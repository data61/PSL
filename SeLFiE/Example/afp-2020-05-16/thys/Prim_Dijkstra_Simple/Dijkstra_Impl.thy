section \<open>Implementation of Dijkstra's Algorithm\<close>
theory Dijkstra_Impl
imports 
  Dijkstra_Abstract
  "Directed_Graph_Impl"
  "HOL-Library.While_Combinator"
  "Priority_Search_Trees.PST_RBT"
  "HOL-Data_Structures.RBT_Map"
begin

subsection \<open>Implementation using ADT Interfaces\<close>

locale Dijkstra_Impl_Adts = 
  G: adt_finite_wgraph G_invar G_succ G_empty G_add G_\<alpha>
+ M: Map M_empty M_update M_delete M_lookup M_invar
+ Q: PrioMap Q_empty Q_update Q_delete Q_invar Q_lookup Q_is_empty Q_getmin
  
  for G_\<alpha> :: "'g \<Rightarrow> ('v) wgraph" and G_invar G_succ G_empty G_add
  
  and M_empty M_update M_delete and M_lookup :: "'m \<Rightarrow> 'v \<Rightarrow> nat option" 
  and M_invar
  
  and Q_empty Q_update Q_delete Q_invar and Q_lookup :: "'q \<Rightarrow> 'v \<Rightarrow> nat option" 
  and Q_is_empty Q_getmin
begin

text \<open>Simplifier setup\<close>
lemmas [simp] = G.wgraph_specs
lemmas [simp] = M.map_specs
lemmas [simp] = Q.prio_map_specs

end  
  

context PrioMap begin

lemma map_getminE:
  assumes "getmin m = (k,p)" "invar m" "lookup m \<noteq> Map.empty" 
  obtains "lookup m k = Some p" "\<forall>k' p'. lookup m k' = Some p' \<longrightarrow> p\<le>p'"  
  using map_getmin[OF assms]
  by (auto simp: ran_def)
    
end

locale Dijkstra_Impl_Defs = Dijkstra_Impl_Adts where G_\<alpha> = G_\<alpha>
  + Dijkstra \<open>G_\<alpha> g\<close> s
  for G_\<alpha> :: "'g \<Rightarrow> ('v::linorder) wgraph" and g s 


locale Dijkstra_Impl = Dijkstra_Impl_Defs where G_\<alpha> = G_\<alpha>  
  for G_\<alpha> :: "'g \<Rightarrow> ('v::linorder) wgraph" 
  +
  assumes G_invar[simp]: "G_invar g"
begin  

lemma finite_all_dnodes[simp, intro!]: "finite all_dnodes"
proof -  
  have "all_dnodes \<subseteq> Set.insert s (snd ` edges)"
    by (fastforce simp: all_dnodes_def edges_def image_iff)
  also have "finite \<dots>" by (auto simp: G.finite)
  finally (finite_subset) show ?thesis .
qed

lemma finite_unfinished_dnodes[simp, intro!]: "finite (unfinished_dnodes S)"
  using finite_subset[OF unfinished_nodes_subset] by auto
  

lemma (in -) fold_refine:
  assumes "I s"
  assumes "\<And>s x. I s \<Longrightarrow> x\<in>set l \<Longrightarrow> I (f x s) \<and> \<alpha> (f x s) = f' x (\<alpha> s)"
  shows "I (fold f l s) \<and> \<alpha> (fold f l s) = fold f' l (\<alpha> s)"
  using assms
  by (induction l arbitrary: s) auto

definition (in Dijkstra_Impl_Defs) "Q_relax_outgoing u du V Q = fold (\<lambda>(d,v) Q.
  case Q_lookup Q v of 
    None \<Rightarrow> if M_lookup V v \<noteq> None then Q else Q_update v (du+d) Q
  | Some d' \<Rightarrow> Q_update v (min (du+d) d') Q) ((G_succ g u)) Q"
  
lemma Q_relax_outgoing[simp]:
  assumes [simp]: "Q_invar Q"
  shows "Q_invar (Q_relax_outgoing u du V Q) 
       \<and> Q_lookup (Q_relax_outgoing u du V Q) 
          = relax_outgoing' u du (M_lookup V) (Q_lookup Q)"
  apply (subst relax_outgoing''_refine[symmetric, where l="G_succ g u"])
  apply simp
  unfolding Q_relax_outgoing_def relax_outgoing''_def
  apply (rule fold_refine[where I=Q_invar and \<alpha>=Q_lookup])
  by (auto split: option.split)
  
definition (in Dijkstra_Impl_Defs) "D_invar_impl Q V \<equiv> 
  Q_invar Q \<and> M_invar V \<and> D_invar' (Q_lookup Q) (M_lookup V)"

definition (in Dijkstra_Impl_Defs)
  "Q_initQ \<equiv> Q_update s 0 Q_empty"
          
lemma Q_init_Q[simp]:
  shows "Q_invar (Q_initQ)" "Q_lookup (Q_initQ) = initQ"
  by (auto simp: Q_initQ_def initQ_def)
  
definition (in Dijkstra_Impl_Defs)
  "M_initV \<equiv> M_empty"
  
lemma M_initS[simp]: "M_invar M_initV" "M_lookup M_initV = initV" 
  unfolding M_initV_def initV_def by auto

term Q_getmin

definition (in Dijkstra_Impl_Defs) 
  "dijkstra_loop \<equiv> while (\<lambda>(Q,V). \<not> Q_is_empty Q) (\<lambda>(Q,V). 
    let
      (u,du) = Q_getmin Q;
      Q = Q_relax_outgoing u du V Q;
      Q = Q_delete u Q;
      V = M_update u du V
    in
      (Q,V)
  ) (Q_initQ,M_initV)"

definition (in Dijkstra_Impl_Defs) "dijkstra \<equiv> snd dijkstra_loop"

lemma transfer_preconditions:
  assumes "coupling Q V D S"
  shows "Q u = Some du \<longleftrightarrow> D u = enat du \<and> u\<notin>S"
  using assms
  by (auto simp: coupling_def)


lemma dijkstra_loop_invar_and_empty:
  shows "case dijkstra_loop of (Q,V) \<Rightarrow> D_invar_impl Q V \<and> Q_is_empty Q"
  unfolding dijkstra_loop_def
  apply (rule while_rule[where 
        P="case_prod D_invar_impl" 
    and r="inv_image finite_psubset (unfinished_dnodes' o M_lookup o snd)"])
  apply (all \<open>(clarsimp split: prod.splits)?\<close>)
  subgoal
    apply (simp add: D_invar_impl_def)
    apply (simp add: D_invar'_def)
    apply (intro exI conjI)
    apply (rule coupling_init)
    using initD_def initS_def invar_init by auto
proof -  
  fix Q V u du
  assume "\<not> Q_is_empty Q" "D_invar_impl Q V" "Q_getmin Q = (u, du)"
  hence "Q_lookup Q \<noteq> Map.empty" "D_invar' (Q_lookup Q) (M_lookup V)"
    and [simp]: "Q_invar Q" "M_invar V"
    and "Q_lookup Q u = Some du" "\<forall>k' p'. Q_lookup Q k' = Some p' \<longrightarrow> du \<le> p'"
    by (auto simp: D_invar_impl_def elim: Q.map_getminE)
    
  then obtain D S where 
    "D_invar D S" 
    and COUPLING: "coupling (Q_lookup Q) (M_lookup V) D S"  
    and ABS_PRE: "D u = enat du" "u\<notin>S" "\<forall>v. v \<notin> S \<longrightarrow> D u \<le> D v"
    by (auto 
          simp: D_invar'_def transfer_preconditions less_eq_enat_def 
          split: enat.splits) 
    
  then interpret Dijkstra_Invar "G_\<alpha> g" s D S by simp
    
  have COUPLING': "coupling 
    ((relax_outgoing' u du (M_lookup V) (Q_lookup Q))(u := None)) 
    (M_lookup V(u \<mapsto> du)) 
    (relax_outgoing u D) 
    (Set.insert u S)"  
    using coupling_step[OF COUPLING \<open>u\<notin>S\<close> \<open>D u = enat du\<close>] by auto
    
  show "D_invar_impl (Q_delete u (Q_relax_outgoing u du V Q)) (M_update u du V)"
    using maintain_D_invar[OF \<open>u\<notin>S\<close>] ABS_PRE
    using COUPLING'
    by (auto simp: D_invar_impl_def D_invar'_def)
  
  show "unfinished_dnodes' (M_lookup (M_update u du V)) 
        \<subset> unfinished_dnodes' (M_lookup V) 
      \<and> finite (unfinished_dnodes' (M_lookup V))"
    using coupling_unfinished[OF COUPLING] coupling_unfinished[OF COUPLING']
    using unfinished_nodes_decr[OF \<open>u\<notin>S\<close>] ABS_PRE
    by simp
qed  
  
lemma dijkstra_correct: 
  "M_invar dijkstra" 
  "M_lookup dijkstra u = Some d \<longleftrightarrow> \<delta> s u = enat d"
  using dijkstra_loop_invar_and_empty
  unfolding dijkstra_def
  apply -
  apply (all \<open>clarsimp simp: D_invar_impl_def\<close>)
  apply (clarsimp simp: D_invar'_def)
  subgoal for Q V D S  
    using Dijkstra_Invar.invar_finish_imp_correct[of "G_\<alpha> g" s D S u]
    apply (clarsimp simp: coupling_def)
    by (auto simp: domIff)
  done

  
end       


subsection \<open>Instantiation of ADTs and Code Generation\<close>

global_interpretation 
  G: wgraph_by_map RBT_Set.empty RBT_Map.update 
                   RBT_Map.delete Lookup2.lookup RBT_Map.M.invar
  defines G_empty = G.empty_graph
      and G_add_edge = G.add_edge
      and G_succ = G.succ
  by unfold_locales

global_interpretation Dijkstra_Impl_Adts
  G.\<alpha> G.invar G.succ G.empty_graph G.add_edge
  
  RBT_Set.empty RBT_Map.update RBT_Map.delete Lookup2.lookup RBT_Map.M.invar
  
  PST_RBT.empty PST_RBT.update PST_RBT.delete PST_RBT.PM.invar 
  Lookup2.lookup PST_RBT.rbt_is_empty pst_getmin
  ..

global_interpretation D: Dijkstra_Impl_Defs  
  G.invar G.succ G.empty_graph G.add_edge
  
  RBT_Set.empty RBT_Map.update RBT_Map.delete Lookup2.lookup RBT_Map.M.invar
  
  PST_RBT.empty PST_RBT.update PST_RBT.delete PST_RBT.PM.invar 
  Lookup2.lookup PST_RBT.rbt_is_empty pst_getmin
  
  G.\<alpha> g s for g and s::"'v::linorder"
  defines dijkstra = D.dijkstra
      and dijkstra_loop = D.dijkstra_loop
      and Q_relax_outgoing = D.Q_relax_outgoing
      and M_initV = D.M_initV
      and Q_initQ = D.Q_initQ
  ..
  
(* TODO: Why is this fix necessary? *)
lemmas [code] =    
  D.dijkstra_def D.dijkstra_loop_def  
  
context
  fixes g
  assumes [simp]: "G.invar g"  
begin  
  
interpretation AUX: Dijkstra_Impl
  G.invar G.succ G.empty_graph G.add_edge
  
  RBT_Set.empty RBT_Map.update RBT_Map.delete Lookup2.lookup RBT_Map.M.invar
  
  PST_RBT.empty PST_RBT.update PST_RBT.delete PST_RBT.PM.invar 
  Lookup2.lookup PST_RBT.rbt_is_empty pst_getmin
  
  g s G.\<alpha> for s
  by unfold_locales simp_all

lemmas dijkstra_correct = AUX.dijkstra_correct[folded dijkstra_def]

end  

subsection \<open>Combination with Graph Parser\<close>  
text \<open>We combine the algorithm with a parser from lists to graphs\<close>

global_interpretation 
  G: wgraph_from_list_algo G.\<alpha> G.invar G.succ G.empty_graph G.add_edge
  defines from_list = G.from_list
  ..
  
  
definition "dijkstra_list l s \<equiv> 
  if valid_graph_rep l then Some (dijkstra (from_list l) s) else None"

theorem dijkstra_list_correct:
  "case dijkstra_list l s of
    None \<Rightarrow> \<not>valid_graph_rep l
  | Some D \<Rightarrow> 
        valid_graph_rep l 
      \<and> M.invar D 
      \<and> (\<forall>u d. lookup D u = Some d \<longleftrightarrow> WGraph.\<delta> (wgraph_of_list l) s u = enat d)"
  unfolding dijkstra_list_def
  by (auto simp: dijkstra_correct G.from_list_correct)

export_code dijkstra_list checking SML OCaml? Scala Haskell?
  
value "dijkstra_list [(1::nat,2,7),(1,3,1),(3,2,2)] 1"
value "dijkstra_list [(1::nat,2,7),(1,3,1),(3,2,2)] 3"


end
