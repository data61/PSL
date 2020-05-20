section \<open>Implementation of Prim's Algorithm\<close>
theory Prim_Impl
imports 
  Prim_Abstract
  Undirected_Graph_Impl
  "HOL-Library.While_Combinator"
  "Priority_Search_Trees.PST_RBT"
  "HOL-Data_Structures.RBT_Map"
begin


subsection \<open>Implementation using ADT Interfaces\label{sec:prim_data_structs}\<close>

locale Prim_Impl_Adts = 
  G: adt_wgraph G_\<alpha>w G_\<alpha>g G_invar G_adj G_empty G_add_edge 
+ M: Map M_empty M_update M_delete M_lookup M_invar
(*+ S: Set S_empty S_insert S_delete S_isin S_\<alpha> S_invar*)
+ Q: PrioMap Q_empty Q_update Q_delete Q_invar Q_lookup Q_is_empty Q_getmin
  
  for typG :: "'g itself" and typM :: "'m itself" and typQ :: "'q itself"
  and G_\<alpha>w and G_\<alpha>g :: "'g \<Rightarrow> ('v) ugraph" and G_invar G_adj G_empty G_add_edge
  
  and M_empty M_update M_delete and M_lookup :: "'m \<Rightarrow> 'v \<Rightarrow> 'v option" and M_invar
  
  and Q_empty Q_update Q_delete Q_invar and Q_lookup :: "'q \<Rightarrow> 'v \<Rightarrow> nat option" 
  and Q_is_empty Q_getmin
  
begin

text \<open>Simplifier setup\<close>
lemmas [simp] = G.wgraph_specs
lemmas [simp] = M.map_specs
lemmas [simp] = Q.prio_map_specs

end  

locale Prim_Impl_Defs = Prim_Impl_Adts  
  where typG = typG and typM = typM and typQ = typQ and G_\<alpha>w = G_\<alpha>w and G_\<alpha>g = G_\<alpha>g
  for typG :: "'g itself" and typM :: "'m itself" and typQ :: "'q itself" 
  and G_\<alpha>w and G_\<alpha>g :: "'g \<Rightarrow> ('v::linorder) ugraph" and g :: 'g and r :: 'v
begin
  
subsubsection \<open>Concrete Algorithm\<close>
term M_lookup
definition "foreach_impl_body u \<equiv> (\<lambda>(v,d) (Qi,\<pi>i).
  if v=r then (Qi,\<pi>i)
  else 
    case (Q_lookup Qi v, M_lookup \<pi>i v) of
      (None,None) \<Rightarrow> (Q_update v d Qi, M_update v u \<pi>i)
    | (Some d',_) \<Rightarrow> (if d<d' then (Q_update v d Qi, M_update v u \<pi>i) else (Qi,\<pi>i))
    | (None, Some _) \<Rightarrow> (Qi,\<pi>i)
  )"

definition foreach_impl :: "'q \<Rightarrow> 'm \<Rightarrow> 'v \<Rightarrow> ('v\<times>nat) list \<Rightarrow> 'q \<times> 'm" where
  "foreach_impl Qi \<pi>i u adjs = foldr (foreach_impl_body u) adjs (Qi,\<pi>i)"


definition "outer_loop_impl Qi \<pi>i \<equiv> while (\<lambda>(Qi,\<pi>i). \<not>Q_is_empty Qi) (\<lambda>(Qi,\<pi>i). 
  let
    (u,_) = Q_getmin Qi;
    adjs = G_adj g u;
    (Qi,\<pi>i) = foreach_impl Qi \<pi>i u adjs;
    Qi = Q_delete u Qi
  in (Qi,\<pi>i)) (Qi,\<pi>i)"

definition "prim_impl = (let
  Qi = Q_update r 0 Q_empty;
  \<pi>i = M_empty;
  (Qi,\<pi>i) = outer_loop_impl Qi \<pi>i
  in \<pi>i)
"

text \<open>The whole algorithm as one function\<close>
lemma prim_impl_alt: "prim_impl = (let 
  \<comment> \<open>Initialization\<close>
  (Q,\<pi>) = (Q_update r 0 Q_empty, M_empty);
  \<comment> \<open>Main loop: Iterate until PQ is empty\<close>
  (Q, \<pi>) = 
  while (\<lambda>(Q, \<pi>). \<not> Q_is_empty Q) (\<lambda>(Q, \<pi>). let 
    (u, _) = Q_getmin Q;
    \<comment> \<open>Inner loop: Update for adjacent nodes\<close>
    (Q, \<pi>) = 
    foldr ((\<lambda>(v, d) (Q, \<pi>). let
        qv = Q_lookup Q v;
        \<pi>v = M_lookup \<pi> v
      in
        if v\<noteq>r \<and> (qv\<noteq>None \<or> \<pi>v=None) \<and> enat d < enat_of_option qv 
        then (Q_update v d Q, M_update v u \<pi>) 
        else (Q, \<pi>))
    ) (G_adj g u) (Q, \<pi>); 
    Q = Q_delete u Q
    in (Q, \<pi>)) (Q, \<pi>)
  in \<pi>
)"
proof -

  have 1: "foreach_impl_body u = (\<lambda>(v,d) (Qi,\<pi>i). let
        qiv = (Q_lookup Qi v);
        \<pi>iv = M_lookup \<pi>i v
      in
        if v\<noteq>r \<and> (qiv\<noteq>None \<or> \<pi>iv=None) \<and> enat d < enat_of_option qiv 
        then (Q_update v d Qi, M_update v u \<pi>i) 
        else (Qi, \<pi>i))" for u
    unfolding foreach_impl_body_def
    apply (intro ext)
    by (auto split: option.split)
    
  show ?thesis
    unfolding prim_impl_def outer_loop_impl_def foreach_impl_def 1
    by (simp)
qed  
  

subsubsection \<open>Abstraction of Result\<close>

text \<open>Invariant for the result, and its interpretation as (minimum spanning) tree:
  \<^item> The map \<open>\<pi>i\<close> and set \<open>Vi\<close> satisfy their implementation invariants
  \<^item> The \<open>\<pi>i\<close> encodes irreflexive edges consistent with the nodes determined 
    by \<open>Vi\<close>. Note that the edges in \<open>\<pi>i\<close> will not be symmetric, thus we take 
    their symmetric closure \<open>E\<union>E\<inverse>\<close>.
    
\<close>
  
definition "invar_MST \<pi>i \<equiv> M_invar \<pi>i"

definition "\<alpha>_MST \<pi>i \<equiv> graph {r} {(u,v) | u v. M_lookup \<pi>i u = Some v}"

end


subsection \<open>Refinement of State\<close>

locale Prim_Impl = Prim_Impl_Defs 
  where typG = typG and typM = typM and typQ = typQ and G_\<alpha>w = G_\<alpha>w and G_\<alpha>g = G_\<alpha>g
  for typG :: "'g itself" and typM :: "'m itself" and typQ :: "'q itself" 
  and G_\<alpha>w and G_\<alpha>g :: "'g \<Rightarrow> ('v::linorder) ugraph" 
  +
  assumes G_invar[simp]: "G_invar g"
begin
               
sublocale Prim2 "G_\<alpha>w g" "G_\<alpha>g g" r .

subsubsection \<open>Abstraction of \<open>Q\<close>\<close>
text \<open>The priority map implements a function of type @{typ \<open>'v\<Rightarrow>enat\<close>}, 
  mapping @{const None} to @{term \<infinity>}.
\<close>

definition "Q_\<alpha> Qi \<equiv> enat_of_option o Q_lookup Qi :: 'v \<Rightarrow> enat"

lemma Q_\<alpha>_empty: "Q_\<alpha> Q_empty = (\<lambda>_. \<infinity>)"
  unfolding Q_\<alpha>_def by (auto)

lemma Q_\<alpha>_update: "Q_invar Q \<Longrightarrow> Q_\<alpha> (Q_update u d Q) = (Q_\<alpha> Q)(u := enat d)"
  unfolding Q_\<alpha>_def by (auto)

lemma Q_\<alpha>_is_empty: "Q_invar Q \<Longrightarrow> Q_lookup Q = Map.empty \<longleftrightarrow> Q_\<alpha> Q = (\<lambda>_. \<infinity>)"
  unfolding Q_\<alpha>_def by (auto simp: fun_eq_iff)

lemma Q_\<alpha>_delete: "Q_invar Q \<Longrightarrow> Q_\<alpha> (Q_delete u Q) = (Q_\<alpha> Q)(u:=\<infinity>)"
  unfolding Q_\<alpha>_def by (auto simp: fun_eq_iff)

lemma Q_\<alpha>_min:
  assumes MIN: "Q_getmin Qi = (u, d)"
  assumes I: "Q_invar Qi"
  assumes NE: "\<not> Q_is_empty Qi"
  shows "Q_\<alpha> Qi u = enat d" (is ?G1) and
        "\<forall>v. enat d \<le> Q_\<alpha> Qi v" (is ?G2)
proof -
  from Q.map_getmin[OF MIN] 
    have "Q_lookup Qi u = Some d" "(\<forall>x\<in>ran (Q_lookup Qi). d \<le> x)"
    using NE I by auto
  thus "?G1" "?G2"
    unfolding Q_\<alpha>_def apply simp_all
    by (metis enat_of_option.elims enat_ord_simps(1) enat_ord_simps(3) ranI)
qed


lemmas Q_\<alpha>_specs = Q_\<alpha>_empty Q_\<alpha>_update Q_\<alpha>_is_empty Q_\<alpha>_delete


subsubsection \<open>Concrete Invariant\<close>

text \<open>The implementation invariants of the concrete state's components,
  and the abstract invariant of the state's abstraction\<close>
definition "prim_invar_impl Qi \<pi>i \<equiv> 
    Q_invar Qi \<and> M_invar \<pi>i \<and> prim_invar2 (Q_\<alpha> Qi) (M_lookup \<pi>i)"


end


subsection \<open>Refinement of Algorithm\<close>

context Prim_Impl
begin

lemma foreach_impl_correct:
  fixes Qi Vi \<pi>i defines "Q \<equiv> Q_\<alpha> Qi" and "\<pi> \<equiv> M_lookup \<pi>i"
  assumes A: "foreach_impl Qi \<pi>i u (G_adj g u) = (Qi',\<pi>i')" 
  assumes I: "prim_invar_impl Qi \<pi>i"
  shows "Q_invar Qi'" and "M_invar \<pi>i'" 
    and "Q_\<alpha> Qi' = Qinter Q \<pi> u" and "M_lookup \<pi>i' = \<pi>' Q \<pi> u"
proof -
  from I have [simp]: "Q_invar Qi" "M_invar \<pi>i" 
    unfolding prim_invar_impl_def Q_def \<pi>_def by auto

  {
    fix Qi \<pi>i d v and adjs :: "('v \<times> nat) list"
    assume "Q_invar Qi" "M_invar \<pi>i" "(v, d) \<in> set adjs"
    then have 
      "(case foreach_impl_body u (v, d) (Qi, \<pi>i) of 
         (Qi, \<pi>i) \<Rightarrow> Q_invar Qi \<and> M_invar \<pi>i) 
              \<and> map_prod Q_\<alpha> M_lookup (foreach_impl_body u (v, d) (Qi, \<pi>i)) 
                = foreach_body u (v, d) (Q_\<alpha> Qi, M_lookup \<pi>i)"
      unfolding foreach_impl_body_def foreach_body_def  
      unfolding Q_\<alpha>_def
      by (auto simp: fun_eq_iff split: option.split)

  } note aux=this

  from foldr_refine[
    where I="\<lambda>(Qi,\<pi>i). Q_invar Qi \<and> M_invar \<pi>i" and \<alpha>="map_prod Q_\<alpha> M_lookup",
    of "(Qi,\<pi>i)" "(G_adj g u)" "foreach_impl_body u" "foreach_body u"
    ]
  and A aux[where ?adjs3="(G_adj g u)"] 
    have "Q_invar Qi'" "M_invar \<pi>i'" 
      and 1: "foreach u (G_adj g u) (Q_\<alpha> Qi, M_lookup \<pi>i) 
              = (Q_\<alpha> Qi', M_lookup \<pi>i')"
    unfolding foreach_impl_def foreach_def 
    unfolding Q_def \<pi>_def
    by (auto split: prod.splits) 
  then show "Q_invar Qi'" "M_invar \<pi>i'" by auto

  from 1 foreach_refine[where adjs="G_adj g u" and u=u] show 
    "Q_\<alpha> Qi' = Qinter Q \<pi> u" and "M_lookup \<pi>i' = \<pi>' Q \<pi> u"
    by (auto simp: Q_def \<pi>_def)
    
qed

(*<*)
lemma foreach_impl_correct_presentation:
  fixes Qi Vi \<pi>i defines "Q \<equiv> Q_\<alpha> Qi" and "\<pi> \<equiv> M_lookup \<pi>i"
  assumes A: "foreach_impl Qi \<pi>i u (G_adj g u) = (Qi',\<pi>i')" 
  assumes I: "prim_invar_impl Qi \<pi>i"
  shows "Q_invar Qi' \<and> M_invar \<pi>i' 
        \<and> Q_\<alpha> Qi' = Qinter Q \<pi> u \<and> M_lookup \<pi>i' = \<pi>' Q \<pi> u"
  using foreach_impl_correct assms by blast
(*>*)  

definition "T_measure_impl \<equiv> \<lambda>(Qi,\<pi>i). T_measure2 (Q_\<alpha> Qi) (M_lookup \<pi>i)"

lemma prim_invar_impl_init: "prim_invar_impl (Q_update r 0 Q_empty) M_empty"
  using invar2_init 
  by (auto simp: prim_invar_impl_def Q_\<alpha>_specs initQ_def init\<pi>_def zero_enat_def)
  
lemma maintain_prim_invar_impl:  
  assumes 
      I: "prim_invar_impl Qi \<pi>i" and
      NE: "\<not> Q_is_empty Qi" and
      MIN: "Q_getmin Qi = (u, d)" and
      FOREACH: "foreach_impl Qi \<pi>i u (G_adj g u) = (Qi', \<pi>i')"
  shows "prim_invar_impl (Q_delete u Qi') \<pi>i'" (is ?G1)
     and "T_measure_impl (Q_delete u Qi', \<pi>i') < T_measure_impl (Qi,\<pi>i)" (is "?G2")
proof -
  note II[simp] = I[unfolded prim_invar_impl_def]
  note FI[simp] = foreach_impl_correct[OF FOREACH I]
  note MIN' = Q_\<alpha>_min[OF MIN _ NE, simplified]

  show ?G1 
    unfolding prim_invar_impl_def
    using Q_\<alpha>_delete maintain_invar2[OF _ MIN'] 
    by (simp add: Q'_def)

  show ?G2
    unfolding prim_invar_impl_def T_measure_impl_def
    using Q_\<alpha>_delete maintain_invar2[OF _ MIN'] 
    apply (simp add: Q'_def Q_\<alpha>_def)
    by (metis FI(3) II Q'_def Q_\<alpha>_def 
        \<open>\<And>\<pi>. prim_invar2 (Q_\<alpha> Qi) \<pi> 
            \<Longrightarrow> T_measure2 (Q' (Q_\<alpha> Qi) \<pi> u) (\<pi>' (Q_\<alpha> Qi) \<pi> u) 
                < T_measure2 (Q_\<alpha> Qi) \<pi>\<close>)
    
qed      

lemma maintain_prim_invar_impl_presentation:  
  assumes 
      I: "prim_invar_impl Qi \<pi>i" and
      NE: "\<not> Q_is_empty Qi" and
      MIN: "Q_getmin Qi = (u, d)" and
      FOREACH: "foreach_impl Qi \<pi>i u (G_adj g u) = (Qi', \<pi>i')"
  shows "prim_invar_impl (Q_delete u Qi') \<pi>i'
       \<and> T_measure_impl (Q_delete u Qi', \<pi>i') < T_measure_impl (Qi,\<pi>i)"
  using maintain_prim_invar_impl assms by blast

lemma prim_invar_impl_finish:
  "\<lbrakk>Q_is_empty Q; prim_invar_impl Q \<pi>\<rbrakk> 
    \<Longrightarrow> invar_MST \<pi> \<and> is_MST (G_\<alpha>w g) rg (\<alpha>_MST \<pi>)"
  using invar2_finish
  by (auto simp: Q_\<alpha>_specs prim_invar_impl_def invar_MST_def \<alpha>_MST_def Let_def)
  
lemma prim_impl_correct:
  assumes "prim_impl = \<pi>i"
  shows 
    "invar_MST \<pi>i" (is ?G1)
    "is_MST (G_\<alpha>w g) (component_of (G_\<alpha>g g) r) (\<alpha>_MST \<pi>i)" (is ?G2)
proof -
  have "let (Qi, \<pi>i) = outer_loop_impl (Q_update r 0 Q_empty) M_empty in 
    invar_MST \<pi>i \<and> is_MST (G_\<alpha>w g) rg (\<alpha>_MST \<pi>i)"
    unfolding outer_loop_impl_def
    apply (rule while_rule[where 
      P="\<lambda>(Qi,\<pi>i). prim_invar_impl Qi \<pi>i" and r="measure T_measure_impl"])
    apply (all \<open>clarsimp split: prod.splits simp: Q_\<alpha>_specs\<close>)
    apply (simp_all add: prim_invar_impl_init maintain_prim_invar_impl 
                         prim_invar_impl_finish)
    done
  with assms show ?G1 ?G2 
    unfolding rg_def prim_impl_def by (simp_all split: prod.splits)
qed    

(*<*)
lemma prim_impl_correct_presentation:
  "invar_MST prim_impl 
  \<and> is_MST (G_\<alpha>w g) (component_of (G_\<alpha>g g) r) (\<alpha>_MST prim_impl)"
  using prim_impl_correct by blast
(*>*)  
    
end


subsection \<open>Instantiation with Actual Data Structures\label{sec:prim_inst_ds}\<close>

global_interpretation 
  G: wgraph_by_map RBT_Set.empty RBT_Map.update RBT_Map.delete 
        Lookup2.lookup RBT_Map.M.invar
  defines G_empty = G.empty
      and G_add_edge = G.add_edge
      and G_add_edge1 = G.add_edge1
      and G_adj = G.adj
      and G_from_list = G.from_list
      and G_valid_wgraph_repr = G.valid_wgraph_repr
  by unfold_locales

(* FIXME: Something is strange with generated constants. *)
lemma G_from_list_unfold:  "G_from_list = G.from_list"
  by (simp add: G_add_edge_def G_empty_def G_from_list_def)
  
(* FIXME: The interpretation does not generate a code theorem at all!? *)
lemma [code]: "G_from_list l = foldr (\<lambda>(e, d). G_add_edge e d) l G_empty"
  by (simp add: G.from_list_def G_from_list_unfold)
  
  
global_interpretation Prim_Impl_Adts _ _ _
  G.\<alpha>w G.\<alpha>g G.invar G.adj G.empty G.add_edge
  
  RBT_Set.empty RBT_Map.update RBT_Map.delete Lookup2.lookup RBT_Map.M.invar
  
  PST_RBT.empty PST_RBT.update PST_RBT.delete PST_RBT.PM.invar 
  Lookup2.lookup PST_RBT.rbt_is_empty pst_getmin
  ..

global_interpretation P: Prim_Impl_Defs G.invar G.adj G.empty G.add_edge
  RBT_Set.empty RBT_Map.update RBT_Map.delete Lookup2.lookup RBT_Map.M.invar
  
  PST_RBT.empty PST_RBT.update PST_RBT.delete PST_RBT.PM.invar 
  Lookup2.lookup PST_RBT.rbt_is_empty pst_getmin
  
  _ _ _ G.\<alpha>w G.\<alpha>g g r  
  for g and r::"'a::linorder"
  defines prim_impl = P.prim_impl
      and outer_loop_impl = P.outer_loop_impl
      and foreach_impl = P.foreach_impl
      and foreach_impl_body = P.foreach_impl_body
  by unfold_locales 


lemmas [code] = P.prim_impl_alt  
  
  
context
  fixes g
  assumes [simp]: "G.invar g"  
begin  
  
interpretation AUX: Prim_Impl
  G.invar G.adj G.empty G.add_edge
  
  RBT_Set.empty RBT_Map.update RBT_Map.delete Lookup2.lookup RBT_Map.M.invar
  
  PST_RBT.empty PST_RBT.update PST_RBT.delete PST_RBT.PM.invar 
  Lookup2.lookup PST_RBT.rbt_is_empty pst_getmin
  
  g r _ _ _ G.\<alpha>w G.\<alpha>g for r::"'a::linorder"
  by unfold_locales simp_all
  
lemmas prim_impl_correct = AUX.prim_impl_correct[folded prim_impl_def] 
  
end  

subsubsection \<open>Adding a Graph-From-List Parser\<close>
  
definition "prim_list_impl l r 
  \<equiv> if G_valid_wgraph_repr l then Some (prim_impl (G_from_list l) r) else None"

  
subsection \<open>Main Correctness Theorem\<close>
  
text \<open>
  The @{const prim_list_impl} algorithm returns @{const None}, if the input was 
  invalid. Otherwise it returns @{term \<open>Some (\<pi>i,Vi)\<close>}, which satisfy the 
  map/set invariants and encode a minimum spanning tree of the component of the
  graph that contains \<open>r\<close>.
  
  Notes:
    \<^item> If \<open>r\<close> is n ot a node of the graph, \<open>component_of\<close> will return the graph
      with the only node \<open>r\<close>. (@{thm [source] component_of_not_node})
\<close>
  
theorem prim_list_impl_correct:
  shows "case prim_list_impl l r of 
    None \<Rightarrow> \<not>G.valid_wgraph_repr l \<comment> \<open>Invalid input\<close>
  | Some \<pi>i \<Rightarrow> 
        G.valid_wgraph_repr l \<and> (let Gi = G.from_list l in G.invar Gi \<comment> \<open>Valid input\<close>
        \<and> P.invar_MST \<pi>i \<comment> \<open>Output satisfies invariants\<close>
        \<and> is_MST (G.\<alpha>w Gi) (component_of (G.\<alpha>g Gi) r) (P.\<alpha>_MST r \<pi>i)) \<comment> \<open>and represents MST\<close>"
  unfolding prim_list_impl_def G_from_list_unfold
  using prim_impl_correct[of "G.from_list l" r] G.from_list_correct[of l]
  by (auto simp: Let_def)

theorem prim_list_impl_correct_presentation:
  shows "case prim_list_impl l r of 
    None \<Rightarrow> \<not>G.valid_wgraph_repr l \<comment> \<open>Invalid input\<close>
  | Some \<pi>i \<Rightarrow> let 
      g=G.\<alpha>g (G.from_list l); 
      w=G.\<alpha>w (G.from_list l); 
      rg=component_of g r;
      t=P.\<alpha>_MST r \<pi>i
    in 
        G.valid_wgraph_repr l \<comment> \<open>Valid input\<close> 
      \<and> P.invar_MST \<pi>i \<comment> \<open>Output satisfies invariants\<close>
      \<and> is_MST w rg t \<comment> \<open>and represents MST\<close>"
  using prim_list_impl_correct[of l r] unfolding Let_def 
  by (auto split: option.splits)
  
      
subsection \<open>Code Generation and Test\label{sec:prim_exec}\<close>

definition prim_list_impl_int :: "_ \<Rightarrow> int \<Rightarrow> _" 
  where "prim_list_impl_int \<equiv> prim_list_impl"


export_code prim_list_impl prim_list_impl_int checking SML


experiment begin

                                  
abbreviation "a \<equiv> 1"
abbreviation "b \<equiv> 2"
abbreviation "c \<equiv> 3"
abbreviation "d \<equiv> 4"
abbreviation "e \<equiv> 5"
abbreviation "f \<equiv> 6"
abbreviation "g \<equiv> 7"
abbreviation "h \<equiv> 8"
abbreviation "i \<equiv> 9"


value "(prim_list_impl_int [
  ((a,b),4),
  ((a,h),8),
  ((b,h),11),
  ((b,c),8),
  ((h,i),7),
  ((h,g),1),
  ((c,i),2),
  ((g,i),6),
  ((c,d),7),
  ((c,f),4),
  ((g,f),2),
  ((d,f),14),
  ((d,e),9),
  ((e,f),10)
] 1)"

end




end
