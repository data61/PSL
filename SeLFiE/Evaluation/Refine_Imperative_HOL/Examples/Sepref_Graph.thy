section \<open>Imperative Graph Representation\<close>
theory Sepref_Graph
imports 
  "../Sepref"
  "../Sepref_ICF_Bindings"
  "../IICF/IICF"
  (*"../../../DFS_Framework/Misc/DFS_Framework_Refine_Aux"*)
begin

text \<open>Graph Interface\<close>
sepref_decl_intf 'a i_graph is "('a\<times>'a) set"

definition op_graph_succ :: "('v\<times>'v) set \<Rightarrow> 'v \<Rightarrow> 'v set" 
  where [simp]: "op_graph_succ E u \<equiv> E``{u}"
sepref_register op_graph_succ :: "'a i_graph \<Rightarrow> 'a \<Rightarrow> 'a set"

thm intf_of_assnI

lemma [pat_rules]: "((``))$E$(insert$u${}) \<equiv> op_graph_succ$E$u" by simp

definition [to_relAPP]: "graph_rel A \<equiv> \<langle>A\<times>\<^sub>rA\<rangle>set_rel"

text \<open>Adjacency List Implementation\<close>
lemma param_op_graph_succ[param]: 
  "\<lbrakk>IS_LEFT_UNIQUE A; IS_RIGHT_UNIQUE A\<rbrakk> \<Longrightarrow> (op_graph_succ, op_graph_succ) \<in> \<langle>A\<rangle>graph_rel \<rightarrow> A \<rightarrow> \<langle>A\<rangle>set_rel"
  unfolding op_graph_succ_def[abs_def] graph_rel_def
  by parametricity

context begin
private definition "graph_\<alpha>1 l \<equiv> { (i,j). i<length l \<and> j\<in>l!i } "

private definition "graph_rel1 \<equiv> br graph_\<alpha>1 (\<lambda>_. True)"

private definition "succ1 l i \<equiv> if i<length l then l!i else {}"

private lemma succ1_refine: "(succ1,op_graph_succ) \<in> graph_rel1 \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>set_rel"
  by (auto simp: graph_rel1_def graph_\<alpha>1_def br_def succ1_def split: if_split_asm intro!: ext)

private definition "assn2 \<equiv> array_assn (pure (\<langle>Id\<rangle>list_set_rel))"

definition "adjg_assn A \<equiv> hr_comp (hr_comp assn2 graph_rel1) (\<langle>the_pure A\<rangle>graph_rel)"

context
  notes [sepref_import_param] = list_set_autoref_empty[folded op_set_empty_def]
  notes [fcomp_norm_unfold] = adjg_assn_def[symmetric]
begin
sepref_definition succ2 is "(uncurry (RETURN oo succ1))" :: "(assn2\<^sup>k*\<^sub>aid_assn\<^sup>k \<rightarrow>\<^sub>a pure (\<langle>Id\<rangle>list_set_rel))"
  unfolding succ1_def[abs_def] assn2_def
  by sepref

lemma adjg_succ_hnr[sepref_fr_rules]: "\<lbrakk>CONSTRAINT (IS_PURE IS_LEFT_UNIQUE) A; CONSTRAINT (IS_PURE IS_RIGHT_UNIQUE) A\<rbrakk> 
  \<Longrightarrow> (uncurry succ2, uncurry (RETURN \<circ>\<circ> op_graph_succ)) \<in> (adjg_assn A)\<^sup>k *\<^sub>a A\<^sup>k \<rightarrow>\<^sub>a pure (\<langle>the_pure A\<rangle>list_set_rel)"
  using succ2.refine[FCOMP succ1_refine, FCOMP param_op_graph_succ, simplified, of A]
  by (simp add: IS_PURE_def list_set_rel_compp)

end

end

lemma [intf_of_assn]: 
  "intf_of_assn A (i::'I itself) \<Longrightarrow> intf_of_assn (adjg_assn A) TYPE('I i_graph)" by simp

definition cr_graph 
  :: "nat \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat list Heap.array Heap"
where
  "cr_graph numV Es \<equiv> do {
    a \<leftarrow> Array.new numV [];
    a \<leftarrow> imp_nfoldli Es (\<lambda>_. return True) (\<lambda>(u,v) a. do {
      l \<leftarrow> Array.nth a u;
      let l = v#l;
      a \<leftarrow> Array.upd u l a;
      return a
    }) a;
    return a
  }"

(* TODO: Show correctness property for cr_graph *)

export_code cr_graph checking SML_imp

end
