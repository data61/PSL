theory FiniteListGraph_Impl
imports 
  FiniteListGraph
  (*"../../Collections/ICF/impl/RBTSetImpl" (*red black trees*)*)
    "HOL-Library.RBT_Impl"
    "HOL-Library.RBT"
  "HOL-Library.Product_Lexorder"
  (*maybe import the following only at the end*)
  Efficient_Distinct
  "HOL-Library.Code_Target_Nat"
begin



text \<open>A graph's well-formed-ness can be tested with an executable function.\<close>  
  fun wf_list_graph_impl::"'v list \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> bool" where
    "wf_list_graph_impl V [] = True" |
    "wf_list_graph_impl V ((v1,v2)#Es) = (v1 \<in> set V \<and> v2 \<in> set V \<and> wf_list_graph_impl V Es)"


  lemma wf_list_graph_impl_axioms_locale_props: 
    "wf_list_graph_impl V E \<longleftrightarrow> fst` set E \<subseteq> set V \<and> snd` set E \<subseteq> set V"
  by (induction E) auto


definition rbt_fromlist :: "'a list \<Rightarrow> ('a::linorder, unit) RBT.rbt" where 
  "rbt_fromlist ls \<equiv> RBT.bulkload (map (\<lambda>l. (l, ())) ls)"
definition "rbt_contains a rbt \<equiv> RBT.lookup rbt a \<noteq> None"

lemma rbt_contains: "rbt_contains a (rbt_fromlist V) \<longleftrightarrow> a \<in> set V"
  apply(simp add: rbt_contains_def rbt_fromlist_def)
  apply(induction V)
   by(simp)+

  (*making the \<in> more efficient*)
  fun wf_list_graph_impl_rs::"('v::linorder,unit) RBT.rbt \<Rightarrow> ('v \<times> 'v) list \<Rightarrow> bool" where
    "wf_list_graph_impl_rs V [] = True" |
    "wf_list_graph_impl_rs V ((v1,v2)#Es) = (rbt_contains v1 V \<and> rbt_contains v2 V \<and> wf_list_graph_impl_rs V Es)"

    
 lemma[code]: "wf_list_graph_impl V E = wf_list_graph_impl_rs (rbt_fromlist V) E"
   apply(induction E)
    apply(simp; fail)
   apply(rename_tac e Es)
   apply(case_tac e)
   by(simp add: rbt_contains)

  lemma[code]: "FiniteListGraph.wf_list_graph_axioms G = wf_list_graph_impl (nodesL G) (edgesL G)"
    by(simp add: FiniteListGraph.wf_list_graph_axioms_def wf_list_graph_impl_axioms_locale_props)

  text\<open>The list implementation matches the @{term "wf_graph"} definition\<close>
  theorem wf_list_graph_iff_wf_graph: 
    "wf_graph (list_graph_to_graph G) \<longleftrightarrow> wf_list_graph_axioms G"
  apply(unfold list_graph_to_graph_def wf_graph_def wf_list_graph_axioms_def wf_list_graph_impl_axioms_locale_props)
    by simp
  corollary wf_list_graph_iff_wf_graph_simplified: 
  "wf_graph \<lparr>nodes = set (nodesL G), edges = set (edgesL G)\<rparr> \<longleftrightarrow> wf_list_graph_axioms G"
  apply(simp add: wf_list_graph_iff_wf_graph[unfolded list_graph_to_graph_def, simplified])
  done


 
text \<open>Code examples.\<close>
  definition wf_graph_example where
  "wf_graph_example \<equiv> \<lparr> nodesL = [1::nat,4,6], edgesL = [(1,4), (1,6), (6,4)] \<rparr>"

  value "wf_list_graph wf_graph_example"

  definition wf_graph_impl_example where
  "wf_graph_impl_example \<equiv> wf_list_graph wf_graph_example"


  export_code wf_list_graph empty add_node delete_node add_edge delete_edge checking Scala


end
