section \<open>Implementation of Weighted Undirected Graph by Map\<close>
theory Undirected_Graph_Impl
imports 
  "HOL-Data_Structures.Map_Specs"
  Common
  Undirected_Graph_Specs
begin

subsection \<open>Doubleton Set to Pair\<close>
definition "epair e = (if card e = 2 then Some (SOME (u,v). e={u,v}) else None)"

lemma epair_eqD: "epair e = Some (x,y) \<Longrightarrow> (x\<noteq>y \<and> e={x,y})"
  apply (cases "card e = 2")
  unfolding epair_def
  apply simp_all
  apply (clarsimp simp: card_Suc_eq eval_nat_numeral doubleton_eq_iff)
  by (smt case_prodD case_prodI someI)

lemma epair_not_sng[simp]: "epair e \<noteq> Some (x,x)"  
  by (auto dest: epair_eqD)

lemma epair_None[simp]: "epair {a,b} = None \<longleftrightarrow> a=b" 
  unfolding epair_def by (auto simp: card2_eq) 
  
subsection \<open>Generic Implementation\<close>  

text \<open>
  When instantiated with a map ADT, this locale provides a weighted graph ADT.
\<close>
locale wgraph_by_map = 
  M: Map M_empty M_update M_delete M_lookup M_invar 
  
  for M_empty M_update M_delete 
  and M_lookup :: "'m \<Rightarrow> 'v \<Rightarrow> (('v\<times>nat) list) option" 
  and M_invar 
begin

definition "\<alpha>nodes_aux g \<equiv> dom (M_lookup g)"

definition "\<alpha>edges_aux g 
  \<equiv> ({(u,v). \<exists>xs d. M_lookup g u = Some xs \<and> (v,d)\<in>set xs })"


definition "\<alpha>g g \<equiv> graph (\<alpha>nodes_aux g) (\<alpha>edges_aux g)"

definition "\<alpha>w g e \<equiv> case epair e of 
  Some (u,v) \<Rightarrow> (
    case M_lookup g u of 
      None \<Rightarrow> 0 
    | Some xs \<Rightarrow> the_default 0 (map_of xs v)
    )
| None \<Rightarrow> 0"

definition invar :: "'m \<Rightarrow> bool" where
  "invar g \<equiv> 
      M_invar g \<and> finite (dom (M_lookup g))
    \<and> (\<forall>u xs. M_lookup g u = Some xs \<longrightarrow> 
          distinct (map fst xs) 
        \<and> u\<notin>set (map fst xs)
        \<and> (\<forall>(v,d)\<in>set xs. (u,d)\<in>set (the_default [] (M_lookup g v)))
      )"
  

lemma in_the_default_empty_conv[simp]: 
  "x\<in>set (the_default [] m) \<longleftrightarrow> (\<exists>xs. m=Some xs \<and> x\<in>set xs)"
  by (cases m) auto  
  
lemma \<alpha>edges_irrefl: "invar g \<Longrightarrow> irrefl (\<alpha>edges_aux g)" 
  unfolding invar_def irrefl_def \<alpha>edges_aux_def
  by (force)
  
lemma \<alpha>edges_sym: "invar g \<Longrightarrow> sym (\<alpha>edges_aux g)"  
  unfolding invar_def sym_def \<alpha>edges_aux_def
  by force 
      
lemma \<alpha>edges_subset: "invar g \<Longrightarrow> \<alpha>edges_aux g \<subseteq> \<alpha>nodes_aux g \<times> \<alpha>nodes_aux g"
  unfolding invar_def \<alpha>nodes_aux_def \<alpha>edges_aux_def
  by force
                      
lemma \<alpha>nodes_finite[simp, intro!]: "invar g \<Longrightarrow> finite (\<alpha>nodes_aux g)"
  unfolding invar_def \<alpha>nodes_aux_def by simp
  
lemma \<alpha>edges_finite[simp, intro!]: "invar g \<Longrightarrow> finite (\<alpha>edges_aux g)"
  using finite_subset[OF \<alpha>edges_subset] by blast
      
definition adj :: "'m \<Rightarrow> 'v \<Rightarrow> ('v\<times>nat) list" where
  "adj g v = the_default [] (M_lookup g v)"
  
definition empty :: "'m" where "empty = M_empty"

definition add_edge1 :: "'v\<times>'v \<Rightarrow> nat \<Rightarrow> 'm \<Rightarrow> 'm" where
  "add_edge1 \<equiv> \<lambda>(u,v) d g. M_update u ((v,d) # the_default [] (M_lookup g u)) g"

definition add_edge :: "'v\<times>'v \<Rightarrow> nat \<Rightarrow> 'm \<Rightarrow> 'm" where
  "add_edge \<equiv> \<lambda>(u,v) d g. add_edge1 (v,u) d (add_edge1 (u,v) d g)"
  

lemma edges_\<alpha>g_aux: "invar g \<Longrightarrow> edges (\<alpha>g g) = \<alpha>edges_aux g" 
  unfolding \<alpha>g_def using \<alpha>edges_sym \<alpha>edges_irrefl
  by (auto simp: irrefl_def graph_accs)
 
lemma nodes_\<alpha>g_aux: "invar g \<Longrightarrow> nodes (\<alpha>g g) = \<alpha>nodes_aux g"  
  unfolding \<alpha>g_def using \<alpha>edges_subset
  by (force simp: graph_accs)

lemma card_doubleton_eq2[simp]: "card {a,b} = 2 \<longleftrightarrow> a\<noteq>b" by auto  

lemma the_dflt_Z_eq: "the_default 0 m = d \<longleftrightarrow> (m=None \<and> d=0 \<or> m=Some d)"
  by (cases m) auto

lemma adj_correct_aux:
  "invar g \<Longrightarrow> set (adj g u) = {(v, d). (u, v) \<in> edges (\<alpha>g g) \<and> \<alpha>w g {u, v} = d}"  
  apply (simp add: edges_\<alpha>g_aux)
  apply safe
  subgoal unfolding adj_def \<alpha>edges_aux_def by auto
  subgoal for a d 
    unfolding adj_def \<alpha>w_def
    apply (clarsimp split: prod.splits option.splits simp: the_dflt_Z_eq)
    unfolding invar_def
    by (force dest!: epair_eqD simp: doubleton_eq_iff)+
  subgoal for a 
    unfolding adj_def \<alpha>w_def
    using \<alpha>edges_irrefl[of g]
    apply (clarsimp split: prod.splits option.splits)
    apply safe
    subgoal by (auto simp: irrefl_def)
    subgoal 
      apply (clarsimp dest!: epair_eqD simp: doubleton_eq_iff)
      unfolding invar_def \<alpha>edges_aux_def
      by force
    subgoal  
      apply (clarsimp dest!: epair_eqD simp: doubleton_eq_iff)
      unfolding invar_def \<alpha>edges_aux_def
      apply clarsimp
      by (smt case_prod_conv map_of_is_SomeI the_default.simps(2))
    done      
  done      
    
lemma invar_empty_aux: "invar empty"  
  by (simp add: invar_def empty_def M.map_specs)

lemma dist_fst_the_dflt_aux: "distinct (map fst (the_default [] m)) 
  \<longleftrightarrow> (\<forall>xs. m = Some xs \<longrightarrow> distinct (map fst xs))"  
  by (cases m; auto)

lemma invar_add_edge_aux: 
  "\<lbrakk>invar g; (u, v) \<notin> edges (\<alpha>g g); u \<noteq> v\<rbrakk> \<Longrightarrow> invar (add_edge (u, v) d g)"  
  apply (simp add: edges_\<alpha>g_aux)
  unfolding add_edge_def add_edge1_def invar_def \<alpha>edges_aux_def
  by (auto simp:  M.map_specs dist_fst_the_dflt_aux; force)
  
  
    
sublocale adt_wgraph \<alpha>w \<alpha>g invar adj empty add_edge 
  apply unfold_locales
  subgoal by (simp add: adj_correct_aux)
  subgoal by (simp add: invar_empty_aux)
  subgoal
    apply (simp 
        add: graph_eq_iff nodes_\<alpha>g_aux invar_empty_aux edges_\<alpha>g_aux
        add: \<alpha>nodes_aux_def \<alpha>edges_aux_def
        )
    apply (simp add: empty_def M.map_specs)
    done
  subgoal
    unfolding \<alpha>w_def
    by (auto simp: empty_def M.map_specs fun_eq_iff split: option.splits)    
  subgoal by (simp add: invar_add_edge_aux)
  subgoal for g u v d
    apply (simp add: edges_\<alpha>g_aux nodes_\<alpha>g_aux graph_eq_iff invar_add_edge_aux)
    apply (rule conjI)
    subgoal
      unfolding add_edge_def add_edge1_def invar_def \<alpha>nodes_aux_def
      by (auto simp: M.map_specs)
    subgoal
      unfolding add_edge_def add_edge1_def invar_def \<alpha>edges_aux_def
      by (fastforce simp: M.map_specs split!: if_splits)
    done      
  subgoal for g u v d
    apply (simp add: edges_\<alpha>g_aux invar_add_edge_aux)
    unfolding invar_def \<alpha>w_def add_edge_def add_edge1_def
    by (auto 
      dest: epair_eqD 
      simp: fun_eq_iff M.map_specs 
      split!: prod.splits option.splits if_splits)
  done    
          
        
end
  

end
