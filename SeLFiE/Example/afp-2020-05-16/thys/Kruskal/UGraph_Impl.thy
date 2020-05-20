section "Kruskal on UGraphs"

theory UGraph_Impl
imports
 Kruskal_Impl UGraph
begin

definition "\<alpha> = (\<lambda>(u,w,v). Upair u v)"

subsection "Interpreting \<open>Kruskl_Impl\<close> with a UGraph"

abbreviation (in uGraph)
  "getEdges_SPEC csuper_E
    \<equiv> (SPEC (\<lambda>L. distinct (map \<alpha> L) \<and> \<alpha> ` set L = E 
                \<and> (\<forall>(a, wv, b)\<in>set L. w (\<alpha> (a, wv, b)) = wv) \<and> set L \<subseteq> csuper_E))"

locale uGraph_impl = uGraph E w for E :: "nat uprod set" and w :: "nat uprod \<Rightarrow> int" +
  fixes getEdges_impl :: "(nat \<times> int \<times> nat) list Heap" and csuper_E :: "(nat \<times> int \<times> nat) set" 
  assumes getEdges_impl:
    "(uncurry0 getEdges_impl, uncurry0 (getEdges_SPEC csuper_E))
       \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a list_assn (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn)"
begin

 

  abbreviation "V \<equiv> \<Union> (set_uprod ` E)"


  lemma max_node_is_Max_V: " E = \<alpha> ` set la \<Longrightarrow>  max_node la = Max (insert 0 V)"
  proof -
    assume E: "E = \<alpha> ` set la"
    have *: "fst ` set la \<union> (snd \<circ> snd) ` set la = (\<Union>x\<in>set la. case x of (x1, x1a, x2a) \<Rightarrow> {x1, x2a})"
      by auto force 
    show ?thesis  
    unfolding E using *
    by (auto simp add: \<alpha>_def  max_node_def prod.case_distrib) 
  qed




sublocale s: Kruskal_Impl E "\<Union>(set_uprod ` E)" set_uprod "\<lambda>u v e. Upair u v = e"
  "subforest" "uconnectedV"  w \<alpha> "PR_CONST (\<lambda>(u,w,v). RETURN (u,v))"
  "PR_CONST (getEdges_SPEC csuper_E)"
 getEdges_impl "csuper_E" " (\<lambda>(u,w,v). return (u,v))" 
  unfolding subforest_def
proof (unfold_locales, goal_cases) 
  show "finite E" by simp
next
  fix E'
  assume "forest E' \<and> E' \<subseteq> E"
  then show "E' \<subseteq> E" by auto
next
  show "forest {} \<and> {} \<subseteq> E" apply (auto simp: decycle_def forest_def)
    using epath.elims(2) by fastforce 
next
  fix X Y
  assume "forest X \<and> X \<subseteq> E" "Y \<subseteq> X" 
  then show "forest Y \<and> Y \<subseteq> E" using forest_mono by auto
next
  case (5 u v)
  then show ?case unfolding uconnected_def apply auto 
    using epath.elims(2) by force 
next
  case (6 E1 E2 u v)
  then have "(u, v) \<in> (uconnected E1)" and uv: "u \<in> V" "v \<in> V"
    by auto
  then obtain p where 1: "epath E1 u p v" unfolding uconnected_def by auto 
  from 6 uv have 2: "\<not>(\<exists>p.  epath E2 u p v)" unfolding uconnected_def by auto
  from 1 2 have "\<exists>a b. (a, b) \<notin> uconnected E2
           \<and> Upair a b \<notin> E2 \<and> Upair a b \<in> E1" by(rule findaugmenting_edge)
  then show ?case by auto
next
  case (7 F e u v)
  note f = \<open>forest F \<and> F \<subseteq> E\<close>
  note notin = \<open>e \<in> E - F\<close> \<open>Upair u v = e\<close>
  from notin ecard2 have unv: "u\<noteq>v" by fastforce
  show "(forest (insert e F) \<and> insert e F \<subseteq> E) = ((u, v) \<notin> uconnectedV F)"
  proof
    assume a: "forest (insert e F) \<and> insert e F \<subseteq> E "
    have "(u, v) \<notin> uconnected F" apply(rule insert_stays_forest_means_not_connected)
      using notin a unv by auto
    then show "((u, v) \<notin> Restr (uconnected F) V)" by auto
  next 
    assume a: "(u, v) \<notin> Restr (uconnected F) V"
    have "forest (insert (Upair u v) F)" apply(rule augment_forest_overedges[where E=E])
      using notin f a unv  by auto 
    moreover have "insert e F \<subseteq> E"
      using notin f by auto
    ultimately show "forest (insert e F) \<and> insert e F \<subseteq> E" using notin by auto
  qed
next      
  fix F
  assume "F\<subseteq>E"
  show "equiv V (uconnectedV F)" by(rule equiv_vert_uconnected)
next                                 
  case (9 F)
  then show ?case  by auto
next
  case (10 x y F)
  then show ?case using insert_uconnectedV_per' by metis
next
  case (11 x)
  then show ?case apply(cases x) by auto
next
  case (12 u v e)
  then show ?case by auto
next
  case (13 u v e)
  then show ?case by auto
next
  case (14 a F e)
  then show ?case using ecard2 by force
next
  case (15 v)
  then show ?case using ecard2 by auto
next
  case 16
  show "V \<subseteq> V" by auto
next
  case 17
  show "finite V" by simp
next
  case (18 a b e T)
  then show ?case 
    apply auto
    subgoal unfolding uconnected_def apply auto apply(rule exI[where x="[e]"]) apply simp
        using ecard2 by force
    subgoal by force
    subgoal by force 
    done
next
  case (19 xi x)
  then show ?case by (auto split: prod.splits simp: \<alpha>_def)
next
  case 20
  show ?case by auto
next
  case 21
  show ?case using getEdges_impl by simp
next
  case (22 l)
  from max_node_is_Max_V[OF 22] show "max_node l = Max (insert 0 V)" .
next
  case (23)
  then show ?case
    apply sepref_to_hoare by sep_auto 
qed
 
lemma spanningForest_eq_basis: "spanningForest = s.basis"
  unfolding spanningForest_def  s.basis_def by auto

lemma minSpanningForest_eq_minbasis: "minSpanningForest = s.minBasis"
  unfolding minSpanningForest_def  s.MSF_def spanningForest_eq_basis by auto

lemma kruskal_correct': 
  "<emp> kruskal getEdges_impl (\<lambda>(u,w,v). return (u,v)) ()
    <\<lambda>r. \<up> (distinct r \<and> set r \<subseteq> csuper_E \<and> s.MSF (set (map \<alpha> r)))>\<^sub>t"
  using s.kruskal_correct_forest   by auto

lemma kruskal_correct:
  "<emp> kruskal getEdges_impl (\<lambda>(u,w,v). return (u,v)) ()
    <\<lambda>r. \<up> (distinct r \<and> set r \<subseteq> csuper_E \<and> minSpanningForest (set (map \<alpha> r)))>\<^sub>t"
  using s.kruskal_correct_forest minSpanningForest_eq_minbasis  by auto

end

subsection "Kruskal on UGraph from list of concrete edges"


definition "uGraph_from_list_\<alpha>_weight L e = (THE w. \<exists>a' b'. Upair a' b' = e \<and> (a', w, b') \<in> set L)"
abbreviation "uGraph_from_list_\<alpha>_edges L \<equiv> \<alpha> ` set L"

locale fromlist = fixes
  L :: "(nat \<times> int \<times> nat) list"
assumes dist: "distinct (map \<alpha> L)" and no_selfloop: "\<forall>u w v. (u,w,v)\<in>set L \<longrightarrow> u\<noteq>v"
begin

lemma not_distinct_map: "a\<in>set l \<Longrightarrow> b\<in>set l \<Longrightarrow> a\<noteq>b \<Longrightarrow> \<alpha> a = \<alpha> b \<Longrightarrow> \<not> distinct (map \<alpha> l)"
   
  by (meson distinct_map_eq)  

lemma ii: "(a, aa, b) \<in> set L \<Longrightarrow> uGraph_from_list_\<alpha>_weight L (Upair a b) = aa"
  unfolding uGraph_from_list_\<alpha>_weight_def
  apply rule
  subgoal by auto
  apply clarify
  subgoal for w a' b'
    apply(auto) 
    subgoal using distinct_map_eq[OF dist, of "(a, aa, b)" "(a, w, b)"]
      unfolding \<alpha>_def by auto
    subgoal using distinct_map_eq[OF dist, of "(a, aa, b)" "(a', w, b')"]
      unfolding \<alpha>_def by fastforce
    done
  done
 
sublocale uGraph_impl "\<alpha> ` set L" "uGraph_from_list_\<alpha>_weight L" "return L" "set L" 
proof (unfold_locales)
  fix e assume *: "e \<in> \<alpha> ` set L"
  from * obtain u w v where "(u,w,v) \<in> set L" "e = \<alpha> (u, w, v)" by auto
  then show "proper_uprod e" using no_selfloop unfolding \<alpha>_def by auto
next
  show "finite (\<alpha> ` set L)" by auto
next
  show "(uncurry0 (return L),uncurry0((SPEC
          (\<lambda>La. distinct (map \<alpha> La) \<and> \<alpha> ` set La = \<alpha> ` set L 
      \<and> (\<forall>(aa, wv, ba)\<in>set La. uGraph_from_list_\<alpha>_weight L (\<alpha> (aa, wv, ba)) = wv)
      \<and> set La \<subseteq> set L))))
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a list_assn (nat_assn \<times>\<^sub>a int_assn \<times>\<^sub>a nat_assn)"
    apply sepref_to_hoare using dist  apply sep_auto
    subgoal using ii unfolding \<alpha>_def by auto
    subgoal by simp
    subgoal by (auto simp: pure_fold list_assn_emp)   
    done
qed
  
lemmas kruskal_correct = kruskal_correct

definition (in -) "kruskal_algo L = kruskal (return L) (\<lambda>(u,w,v). return (u,v)) ()"

end 

subsection \<open>Outside the locale\<close>

definition uGraph_from_list_invar :: "(nat\<times>int\<times>nat) list \<Rightarrow> bool" where
  "uGraph_from_list_invar L = (distinct (map \<alpha> L) \<and> (\<forall>p\<in>set L. case p of (u,w,v) \<Rightarrow>u\<noteq>v))"

lemma uGraph_from_list_invar_conv: "uGraph_from_list_invar L = fromlist L"
  by(auto simp add: uGraph_from_list_invar_def fromlist_def)

lemma uGraph_from_list_invar_subset: 
  "uGraph_from_list_invar L \<Longrightarrow> set L'\<subseteq> set L \<Longrightarrow> distinct L' \<Longrightarrow> uGraph_from_list_invar L'"
  unfolding uGraph_from_list_invar_def by (auto simp: distinct_map inj_on_subset)  


lemma  uGraph_from_list_\<alpha>_inj_on: "uGraph_from_list_invar E \<Longrightarrow> inj_on \<alpha> (set E)"
  by(auto simp: distinct_map uGraph_from_list_invar_def  )

lemma sum_easier: "uGraph_from_list_invar L 
    \<Longrightarrow> set E \<subseteq> set L
    \<Longrightarrow> sum (uGraph_from_list_\<alpha>_weight L) (uGraph_from_list_\<alpha>_edges E) = sum (\<lambda>(u,w,v). w) (set E)"
 proof -
  assume a: "uGraph_from_list_invar L"
  assume b: "set E \<subseteq> set L" 

  have *: "\<And>e. e\<in>set E \<Longrightarrow>
   ((\<lambda>e. THE w. \<exists>a' b'. Upair a' b' = e \<and> (a', w, b') \<in> set L) \<circ> \<alpha>) e
       = (case e of (u, w, v) \<Rightarrow> w)"
    apply simp
    apply(rule the_equality) 
    subgoal using b by(auto simp: \<alpha>_def split: prod.splits)   
    subgoal using a b apply(auto simp: uGraph_from_list_invar_def distinct_map split: prod.splits)  
      using \<alpha>_def 
      by (smt \<alpha>_def inj_onD old.prod.case prod.inject set_mp)  
    done
 
  have inj_on_E: "inj_on \<alpha> (set E)"
    apply(rule inj_on_subset)
    apply(rule uGraph_from_list_\<alpha>_inj_on) by fact+ 

  show ?thesis
    unfolding uGraph_from_list_\<alpha>_weight_def
    apply(subst sum.reindex[OF inj_on_E] ) 
    using * by auto 
qed
 


lemma corr: "uGraph_from_list_invar L \<Longrightarrow>
  <emp> kruskal_algo L
     <\<lambda>F. \<up> (uGraph_from_list_invar F \<and> set F \<subseteq> set L \<and>               
       uGraph.minSpanningForest (uGraph_from_list_\<alpha>_edges L)
         (uGraph_from_list_\<alpha>_weight L) (uGraph_from_list_\<alpha>_edges F))>\<^sub>t"
  apply(sep_auto heap: fromlist.kruskal_correct
          simp: uGraph_from_list_invar_conv kruskal_algo_def  ) 
  using uGraph_from_list_invar_subset uGraph_from_list_invar_conv by simp



lemma "uGraph_from_list_invar L \<Longrightarrow>
  <emp> kruskal_algo L
     <\<lambda>F. \<up> (uGraph_from_list_invar F \<and> set F \<subseteq> set L \<and>
       uGraph.spanningForest (uGraph_from_list_\<alpha>_edges L) (uGraph_from_list_\<alpha>_edges F)
      \<and> (\<forall>F'. uGraph.spanningForest (uGraph_from_list_\<alpha>_edges L) (uGraph_from_list_\<alpha>_edges F')
          \<longrightarrow> set F' \<subseteq> set L \<longrightarrow>  sum (\<lambda>(u,w,v). w) (set F) \<le> sum (\<lambda>(u,w,v). w) (set F')))>\<^sub>t"
proof -
  assume a: "uGraph_from_list_invar L"
  then interpret fromlist L apply unfold_locales by (auto simp: uGraph_from_list_invar_def)
  from a show ?thesis
    by(sep_auto heap: corr simp: minSpanningForest_def sum_easier)
qed


subsection \<open>Kruskal with input check\<close>

definition "kruskal' L = kruskal (return L)  (\<lambda>(u,w,v). return (u,v)) ()"

definition "kruskal_checked L = (if uGraph_from_list_invar L
                             then do { F \<leftarrow> kruskal' L; return (Some F) }
                             else return None)"

 
lemma "<emp> kruskal_checked L <\<lambda>
    Some F \<Rightarrow> \<up> (uGraph_from_list_invar L \<and> set F \<subseteq> set L
       \<and> uGraph.minSpanningForest (uGraph_from_list_\<alpha>_edges L) (uGraph_from_list_\<alpha>_weight L)
           (uGraph_from_list_\<alpha>_edges F))
  | None \<Rightarrow> \<up> (\<not> uGraph_from_list_invar L)>\<^sub>t"
  unfolding kruskal_checked_def
  apply(cases "uGraph_from_list_invar L") apply simp_all
  subgoal proof -
    assume [simp]: "uGraph_from_list_invar L"
    then interpret fromlist L apply unfold_locales by(auto simp: uGraph_from_list_invar_def)
    show ?thesis unfolding kruskal'_def by (sep_auto heap: kruskal_correct)   
  qed
  subgoal by sep_auto
  done 

subsection \<open>Code export\<close>

export_code uGraph_from_list_invar checking SML_imp
export_code kruskal_checked checking SML_imp

ML_val \<open>
  val export_nat = @{code integer_of_nat}
  val import_nat = @{code nat_of_integer}
  val export_int = @{code integer_of_int}
  val import_int = @{code int_of_integer}
  val import_list = map (fn (a,b,c) => (import_nat a, (import_int b, import_nat c)))
  val export_list = map (fn (a,(b,c)) => (export_nat a, export_int b, export_nat c))
  val export_Some_list = (fn SOME l => SOME (export_list l) | NONE => NONE)

  fun kruskal l = @{code kruskal} (fn () => import_list l) (fn (a,(_,c)) => fn () => (a,c)) () ()
                     |> export_list 
  fun kruskal_checked l = @{code kruskal_checked} (import_list l) ()  |> export_Some_list


  val result = kruskal [(1,~9,2),(2,~3,3),(3,~4,1)]
  val result4 = kruskal [(1,~100,4), (3,64,5), (1,13,2), (3,20,2), (2,5,5), (4,80,3), (4,40,5)]

  val result' = kruskal_checked [(1,~9,2),(2,~3,3),(3,~4,1)]
  val result1' = kruskal_checked [(1,~9,2),(2,~3,3),(3,~4,1),(1,5,3)]
  val result2' = kruskal_checked [(1,~9,2),(2,~3,3),(3,~4,1),(3,~4,1)]
  val result3' = kruskal_checked [(1,~9,2),(2,~3,3),(3,~4,1),(1,~4,1)]
  val result4' = kruskal_checked [(1,~100,4), (3,64,5), (1,13,2), (3,20,2),
                                   (2,5,5), (4,80,3), (4,40,5)]
\<close>


end