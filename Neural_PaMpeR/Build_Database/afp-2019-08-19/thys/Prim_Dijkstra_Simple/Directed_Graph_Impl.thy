section \<open>Weighted Digraph Implementation by Adjacency Map\<close>
theory Directed_Graph_Impl
imports 
  Directed_Graph_Specs
  "HOL-Data_Structures.Map_Specs"
begin

locale wgraph_by_map = 
  M: Map M_empty M_update M_delete M_lookup M_invar 
  
  for M_empty M_update M_delete 
  and M_lookup :: "'m \<Rightarrow> 'v \<Rightarrow> ((nat\<times>'v) list) option" and M_invar 
begin

definition \<alpha> :: "'m \<Rightarrow> ('v) wgraph" where
  "\<alpha> g \<equiv> \<lambda>(u,v). case M_lookup g u of 
    None \<Rightarrow> \<infinity> 
  | Some l \<Rightarrow> if \<exists>d. (d,v)\<in>set l then enat (SOME d. (d,v)\<in>set l) else \<infinity>"

definition invar :: "'m \<Rightarrow> bool" where "invar g \<equiv> 
    M_invar g 
  \<and> (\<forall>l\<in>ran (M_lookup g). distinct (map snd l)) 
  \<and> finite (WGraph.edges (\<alpha> g))"

definition succ :: "'m \<Rightarrow> 'v \<Rightarrow> (nat \<times> 'v) list" where
  "succ g v = the_default [] (M_lookup g v)"
  
definition empty_graph :: "'m" where "empty_graph = M_empty"

definition add_edge :: "'v\<times>'v \<Rightarrow> nat \<Rightarrow> 'm \<Rightarrow> 'm" where
  "add_edge \<equiv> \<lambda>(u,v) d g. M_update u ((d,v) # the_default [] (M_lookup g u)) g"

sublocale adt_finite_wgraph invar succ empty_graph add_edge \<alpha>
  apply unfold_locales
  subgoal for g u 
    by (cases "M_lookup g u")
       (auto 
          simp: invar_def \<alpha>_def succ_def ran_def
          intro: distinct_map_snd_inj someI
          split: option.splits
        )
  subgoal by (auto 
                simp: invar_def \<alpha>_def empty_graph_def add_edge_def M.map_specs 
                split: option.split)
  subgoal by (auto 
                simp: invar_def \<alpha>_def empty_graph_def add_edge_def M.map_specs 
                split: option.split)
proof -    
  text \<open>Explicit proof to nicely handle finiteness constraint, using already
     proved shape of abstract result\<close>
  fix g e d
  assume A: "invar g" "\<alpha> g e = \<infinity>"
  then show AAE: "\<alpha> (add_edge e d g) = (\<alpha> g)(e := enat d)"
    by (auto 
      simp: invar_def \<alpha>_def add_edge_def M.map_specs
      split: option.splits if_splits prod.splits
    )
  
  from A show "invar (add_edge e d g)"  
    apply (simp add: invar_def AAE)
    by (force
      simp: invar_def \<alpha>_def empty_graph_def add_edge_def M.map_specs ran_def
      split: option.splits if_splits prod.splits)      
qed (simp add: invar_def)     

end  

end
