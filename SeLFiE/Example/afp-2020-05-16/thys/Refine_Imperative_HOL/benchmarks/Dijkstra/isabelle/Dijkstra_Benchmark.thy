theory Dijkstra_Benchmark
imports "../../../Examples/Sepref_Dijkstra"
  Dijkstra_Shortest_Path.Test
begin

definition nat_cr_graph_imp 
  :: "nat \<Rightarrow> (nat \<times> nat \<times> nat) list \<Rightarrow> nat graph_impl Heap"
  where "nat_cr_graph_imp \<equiv> cr_graph"

concrete_definition nat_dijkstra_imp uses dijkstra_imp_def[where 'W=nat]
prepare_code_thms nat_dijkstra_imp_def

lemma nat_dijkstra_imp_eq: "nat_dijkstra_imp = dijkstra_imp"
  unfolding dijkstra_imp_def[abs_def] nat_dijkstra_imp_def[abs_def]
  by simp


(*definition nat_dijkstra_imp 
  :: "nat \<Rightarrow> nat \<Rightarrow> nat graph_impl \<Rightarrow> ((nat \<times> nat \<times> nat) list \<times> nat) option Heap.array Heap"
  where
  "nat_dijkstra_imp \<equiv> dijkstra_imp"
*)

definition "nat_cr_graph_fun nn es \<equiv> hlg_from_list_nat ([0..<nn], es)"

export_code 
  integer_of_nat nat_of_integer

  ran_graph

  nat_cr_graph_fun nat_dijkstra 

  nat_cr_graph_imp nat_dijkstra_imp 
  in SML_imp module_name Dijkstra
  file \<open>dijkstra_export.sml\<close>


end

