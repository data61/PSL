section \<open>Implementation of Flow Networks\<close>
theory Network_Impl
imports 
  "Lib/Refine_Add_Fofu"
  Ford_Fulkerson 
begin

subsection \<open>Type Constraints\<close>  
text \<open>We constrain the types that we use for implementation.\<close>  
  
text \<open>We define capacities to be integer values.\<close>  
type_synonym capacity_impl = int
type_synonym flow_impl = "capacity_impl flow"  
  
text \<open>We define a locale that assumes that the nodes are natural numbers in the 
  range @{term "{0..<N}"}.\<close>  

locale Network_Impl = Network c s t for c :: "capacity_impl graph" and s t +
  fixes N :: nat
  assumes V_ss: "V\<subseteq>{0..<N}"
begin  
  lemma E_ss: "E \<subseteq> {0..<N}\<times>{0..<N}" using E_ss_VxV V_ss by auto
end \<comment> \<open>Network Implementation Locale\<close>

subsection \<open>Basic Operations\<close>
  
context Network_Impl
begin
  subsubsection \<open>Residual Graph\<close>
  text \<open>Get the residual capacity of an edge.\<close>  
  definition cf_get :: "flow_impl \<Rightarrow> edge \<Rightarrow> capacity_impl nres" 
    where "cf_get cf e \<equiv> do {
      assert (e\<in>E \<union> E\<inverse>);
      return (cf e)
    }"  
    
  text \<open>Update the residual capacity of an edge.\<close>    
  definition cf_set :: "flow_impl \<Rightarrow> edge \<Rightarrow> capacity_impl \<Rightarrow> flow_impl nres" 
    where "cf_set cf e x \<equiv> do {
      assert (e\<in>E \<union> E\<inverse>);
      return (cf (e:=x))
    }"  
  
  text \<open>Obtain the initial residual graph.\<close>    
  definition cf_init :: "flow_impl nres" 
    where "cf_init \<equiv> return (op_mtx_new c)"
  
  subsubsection \<open>Adjacency Map\<close>
  text \<open>Obtain the list of adjacent nodes for a specified node.\<close>  
  definition am_get :: "(node \<Rightarrow> node list) \<Rightarrow> node \<Rightarrow> node list nres"    
    where "am_get am u \<equiv> do {
      assert (u\<in>V);
      return (am u)
    }"
      
  text \<open>Test whether a node identifier is actually a node. 
    As not all numbers in the range @{term \<open>{0..<N}\<close>} must identify nodes, 
    this function uses the adjacency map to check whether there are adjacent
    edges. Due to the network constraints, all nodes have adjacent edges.
  \<close>    
  definition am_is_in_V :: "(node \<Rightarrow> node list) \<Rightarrow> node \<Rightarrow> bool nres"
    where "am_is_in_V am u \<equiv> do {
      return (am u \<noteq> [])
    }"
  
  lemma am_is_in_V_correct[THEN order_trans, refine_vcg]: 
    assumes "(am,adjacent_nodes) \<in> nat_rel \<rightarrow> \<langle>nat_rel\<rangle>list_set_rel"
    shows "am_is_in_V am u \<le> (spec x. x \<longleftrightarrow> u\<in>V)"
  proof -
    have "u\<in>V \<longleftrightarrow> adjacent_nodes u \<noteq> {}" 
      unfolding V_def adjacent_nodes_def by auto
    also have "\<dots> \<longleftrightarrow> am u \<noteq> []" 
      using fun_relD[OF assms IdI[of u]] 
      by (auto simp: list_set_rel_def in_br_conv)
    finally show ?thesis unfolding am_is_in_V_def by refine_vcg auto
  qed    
  
end \<comment> \<open>Network Implementation Locale\<close>
  
subsubsection \<open>Registration of Basic Operations to Sepref\<close>  

text \<open>Bundles the setup for registration of abstract operations.\<close>  
bundle Network_Impl_Sepref_Register begin
  text \<open>Automatically rewrite to \<open>i_mtx\<close> interface type\<close>  
  lemmas [map_type_eqs] = 
    map_type_eqI[of "TYPE(capacity_impl flow)" "TYPE(capacity_impl i_mtx)"]
  
end \<comment> \<open>Bundle\<close>
 
  
context Network_Impl
begin

subsubsection \<open>Registration of Abstract Operations\<close>  
  
context
  includes Network_Impl_Sepref_Register
begin

sepref_register N s t
sepref_register c :: "capacity_impl graph"

sepref_register cf_get cf_set cf_init
  
sepref_register am_get am_is_in_V    
  
end \<comment> \<open>Anonymous Context\<close> 

end \<comment> \<open>Network Implementation Locale\<close>
  
subsection \<open>Refinement To Efficient Data Structures\<close>  

subsubsection \<open>Functions from Nodes by Arrays\<close>  
(*
  TODO: Move to own file in IICF
 
  This has more general uses than implementing nodes!
  It can implement functions from any objects represented by an initial
  segment of the natural numbers, a very often recurring pattern.
*)  
text \<open>
  We provide a template for implementing functions from nodes by arrays.
  Outside the node range, the abstract functions have a default value.

  This template is then used for refinement of various data structures.
\<close>  
definition "is_nf N dflt f a 
  \<equiv> \<exists>\<^sub>Al. a\<mapsto>\<^sub>al * \<up>(length l = N \<and> (\<forall>i<N. l!i = f i) \<and> (\<forall>i\<ge>N. f i = dflt))"
  
lemma nf_init_rule: 
  "<emp> Array.new N dflt <is_nf N dflt (\<lambda>_. dflt)>"
  unfolding is_nf_def by sep_auto

lemma nf_copy_rule[sep_heap_rules]: 
  "<is_nf N dflt f a> array_copy a <\<lambda>r. is_nf N dflt f a * is_nf N dflt f r>"
  unfolding is_nf_def by sep_auto
  
lemma nf_lookup_rule[sep_heap_rules]: 
  "v<N \<Longrightarrow> <is_nf N dflt f a> Array.nth a v <\<lambda>r. is_nf N dflt f a *\<up>(r = f v)>"
  unfolding is_nf_def by sep_auto
  
lemma nf_update_rule[sep_heap_rules]: 
  "v<N \<Longrightarrow> <is_nf N dflt f a> Array.upd v x a <is_nf N dflt (f(v:=x))>"  
  unfolding is_nf_def by sep_auto
  
  
  
subsubsection \<open>Automation Setup for Side-Condition Discharging\<close>  
  
context Network_Impl
begin
  

lemma mtx_nonzero_iff[simp]: "mtx_nonzero c = E" 
  unfolding E_def by (auto simp: mtx_nonzero_def)

lemma mtx_nonzeroN: "mtx_nonzero c \<subseteq> {0..<N}\<times>{0..<N}" using E_ss by simp

lemma in_mtx_nonzeroN[simp]: "(u,v) \<in> mtx_nonzero c \<Longrightarrow> u<N \<and> v<N" 
  using mtx_nonzeroN by auto   
    
lemma inV_less_N[simp]: "v\<in>V \<Longrightarrow> v<N" using V_ss by auto

lemma inEIE_lessN[simp]: "e\<in>E \<or> e\<in>E\<inverse> \<Longrightarrow> case e of (u,v) \<Rightarrow> u<N \<and> v<N"    
  using E_ss by auto
lemmas [simp] = nested_case_prod_simp

subsubsection \<open>Network Parameters by Identity\<close>    
abbreviation (in -) cap_assn :: "capacity_impl \<Rightarrow> _" where "cap_assn \<equiv> id_assn"  
abbreviation (in -) "edge_assn \<equiv> nat_assn \<times>\<^sub>a nat_assn"  
abbreviation (in -) (input) "node_assn \<equiv> nat_assn"  

text \<open>Refine number of nodes, and source and sink node by themselves\<close>
lemmas [sepref_import_param] = 
  IdI[of N]
  IdI[of s]
  IdI[of t]

lemma c_hnr[sepref_fr_rules]: 
  "(uncurry0 (return c),uncurry0 (RETURN c))
    \<in>unit_assn\<^sup>k \<rightarrow>\<^sub>a pure (nat_rel \<times>\<^sub>r nat_rel \<rightarrow> Id)"
  by (sepref_to_hoare) sep_auto 
  
  
subsubsection \<open>Residual Graph by Adjacency Matrix\<close>  
  
definition (in -) "cf_assn N \<equiv> asmtx_assn N cap_assn"
abbreviation cf_assn where "cf_assn \<equiv> Network_Impl.cf_assn N"
lemma [intf_of_assn]: "intf_of_assn (cf_assn) TYPE(capacity_impl i_mtx)"
  by simp
    
sepref_thm cf_get_impl is "uncurry (PR_CONST cf_get)" 
  :: "cf_assn\<^sup>k *\<^sub>a edge_assn\<^sup>k \<rightarrow>\<^sub>a cap_assn"  
  unfolding cf_get_def cf_assn_def PR_CONST_def
  by sepref
concrete_definition (in -) cf_get_impl 
  uses Network_Impl.cf_get_impl.refine_raw is "(uncurry ?f,_)\<in>_"
    
sepref_thm cf_set_impl is "uncurry2 (PR_CONST cf_set)" 
  :: "cf_assn\<^sup>d *\<^sub>a edge_assn\<^sup>k *\<^sub>a cap_assn\<^sup>k \<rightarrow>\<^sub>a cf_assn"  
  unfolding cf_set_def cf_assn_def PR_CONST_def by sepref
concrete_definition (in -) cf_set_impl 
  uses Network_Impl.cf_set_impl.refine_raw is "(uncurry2 ?f,_)\<in>_"

sepref_thm cf_init_impl is "uncurry0 (PR_CONST cf_init)" 
  :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a cf_assn" 
  unfolding PR_CONST_def cf_assn_def cf_init_def 
  apply (rewrite amtx_fold_custom_new[of N N])
  by sepref  
concrete_definition (in -) cf_init_impl 
  uses Network_Impl.cf_init_impl.refine_raw is "(uncurry0 ?f,_)\<in>_"
lemmas [sepref_fr_rules] = 
  cf_get_impl.refine[OF Network_Impl_axioms] 
  cf_set_impl.refine[OF Network_Impl_axioms] 
  cf_init_impl.refine[OF Network_Impl_axioms]
  
  
  
subsubsection \<open>Adjacency Map by Array\<close>  
definition (in -) "am_assn N \<equiv> is_nf N ([]::nat list)"    
abbreviation am_assn where "am_assn \<equiv> Network_Impl.am_assn N"

lemma am_get_hnr[sepref_fr_rules]: 
  "(uncurry Array.nth, uncurry (PR_CONST am_get)) 
  \<in> am_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a list_assn id_assn"  
  unfolding am_assn_def am_get_def list_assn_pure_conv
  by sepref_to_hoare (sep_auto simp: refine_pw_simps)

    
definition (in -) "am_is_in_V_impl am u \<equiv> do {
  amu \<leftarrow> Array.nth am u;
  return (\<not>is_Nil amu)
}"    
lemma am_is_in_V_hnr[sepref_fr_rules]: "(uncurry am_is_in_V_impl, uncurry (am_is_in_V)) 
  \<in> [\<lambda>(_,v). v<N]\<^sub>a am_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow> bool_assn"  
  unfolding am_assn_def am_is_in_V_def am_is_in_V_impl_def
  apply sepref_to_hoare 
  apply (sep_auto simp: refine_pw_simps split: list.split)
  done
  
end \<comment> \<open>Network Implementation Locale\<close>
  
subsection \<open>Computing the Flow Value\<close>
text \<open>We define an algorithm to compute the value of a flow from 
  the residual graph
\<close>  
  
locale RGraph_Impl = RGraph c s t cf + Network_Impl c s t N
  for c :: "capacity_impl flow" and s t N cf
  
lemma rgraph_and_network_impl_imp_rgraph_impl:
  assumes "RGraph c s t cf"
  assumes "Network_Impl c s t N"
  shows "RGraph_Impl c s t N cf"  
  using assms by (rule Network_Impl.RGraph_Impl.intro)  
  
  
lemma (in RGraph) val_by_adj_map:  
  assumes AM: "is_adj_map am"
  shows "f.val = (\<Sum>v\<in>set (am s). cf (v,s))"
proof -
  have [simp]: "set (am s) = E``{s}"
    using AM unfolding is_adj_map_def
    by auto
  
  note f.val_by_cf
  also note rg_is_cf
  also have "(\<Sum>(u, v)\<in>outgoing s. cf (v, u)) 
          = ((\<Sum>v\<in>set (am s). cf (v,s)))"  
    by (simp add: sum_outgoing_pointwise)
  finally show ?thesis .    
qed  
  
context Network_Impl 
begin
  
definition "compute_flow_val_aux am cf \<equiv> do {
    succs \<leftarrow> am_get am s;
    sum_impl (\<lambda>v. cf_get cf (v,s)) (set succs)
  }"

lemma (in RGraph_Impl) compute_flow_val_aux_correct:
  assumes "is_adj_map am"
  shows "compute_flow_val_aux am cf \<le> (spec v. v = f.val)"
  unfolding val_by_adj_map[OF assms]
  unfolding compute_flow_val_aux_def cf_get_def am_get_def
  apply (refine_vcg sum_impl_correct)
  apply (vc_solve simp: s_node)
  subgoal using assms unfolding is_adj_map_def by auto  
  done
  
text \<open>For technical reasons (poor foreach-support of Sepref tool), 
  we have to add another refinement step: \<close>  
definition "compute_flow_val am cf \<equiv> (do {
  succs \<leftarrow> am_get am s;
  nfoldli succs (\<lambda>_. True) (\<lambda>x a. do {
     b \<leftarrow> cf_get cf (x, s); 
     return (a + b)
   }) 0
})"  

lemma (in RGraph_Impl) compute_flow_val_correct[THEN order_trans, refine_vcg]:
  assumes "is_adj_map am"
  shows "compute_flow_val am cf \<le> (spec v. v = f.val)"
proof -
  have [refine_dref_RELATES]: "RELATES (\<langle>Id\<rangle>list_set_rel)" 
    by (simp add: RELATES_def)
  show ?thesis
    apply (rule order_trans[OF _ compute_flow_val_aux_correct[OF assms]])
    unfolding compute_flow_val_def compute_flow_val_aux_def sum_impl_def
    apply (rule refine_IdD)
    apply (refine_rcg LFO_refine bind_refine')
    apply refine_dref_type
    apply vc_solve
    using assms
    by (auto 
        simp: list_set_rel_def br_def am_get_def is_adj_map_def 
        simp: refine_pw_simps)
qed    
    
context 
  includes Network_Impl_Sepref_Register
begin  
  sepref_register compute_flow_val
end  
  
sepref_thm compute_flow_val_impl
  is "uncurry (PR_CONST compute_flow_val)" 
    :: "am_assn\<^sup>k *\<^sub>a cf_assn\<^sup>k \<rightarrow>\<^sub>a cap_assn" 
  unfolding compute_flow_val_def PR_CONST_def
  by sepref  
concrete_definition (in -) compute_flow_val_impl 
  uses Network_Impl.compute_flow_val_impl.refine_raw is "(uncurry ?f,_)\<in>_"
lemmas compute_flow_val_impl_hnr[sepref_fr_rules] 
    = compute_flow_val_impl.refine[OF Network_Impl_axioms]
    
end \<comment> \<open>Network Implementation Locale\<close>
    
text \<open>We also export a correctness theorem on the separation logic level\<close>    

lemma compute_flow_val_impl_correct[sep_heap_rules]:
  assumes "RGraph_Impl c s t N cf"
  assumes AM: "Graph.is_adj_map c am"  
  shows "<cf_assn N cf cfi * am_assn N am ami> 
          compute_flow_val_impl s N ami cfi 
        <\<lambda>v. cf_assn N cf cfi * am_assn N am ami 
            * \<up>( v = Flow.val c s (RPreGraph.f c cf) )>\<^sub>t"
proof -
  interpret RGraph_Impl c s t N cf by fact

      
  from hn_refine_ref[OF 
      compute_flow_val_correct[OF AM order_refl] 
      compute_flow_val_impl_hnr[to_hnr, unfolded autoref_tag_defs]]    
  show ?thesis  
    apply (simp add: hn_ctxt_def pure_def hn_refine_def f_def)
    apply (rule cons_post_rule)
    apply assumption  
    apply sep_auto
    done  
qed    
  
subsubsection \<open>Computing the Exact Number of Nodes\<close>  
  
context Network_Impl
begin
  
lemma am_to_adj_nodes_refine:
  assumes AM: "is_adj_map am"  
  shows "(am u, adjacent_nodes u) \<in> \<langle>nat_rel\<rangle>list_set_rel"  
  using AM  
  unfolding adjacent_nodes_def is_adj_map_def  
  by (auto simp: list_set_rel_def in_br_conv)  

  
  
  
definition "init_C am \<equiv> do {
  let cardV=0;
  nfoldli [0..<N] (\<lambda>_. True) (\<lambda>v cardV. do {
    assert (v<N);
    inV \<leftarrow> am_is_in_V am v;
    if inV then do {
      return (cardV + 1)
    } else
      return cardV
  }) cardV
}"    

lemma init_C_correct:
  assumes AM: "is_adj_map am"  
  shows "init_C am \<le> SPEC (\<lambda>C. C = card V)"
  unfolding init_C_def  
  apply (refine_vcg 
      nfoldli_rule[where I="\<lambda>l1 _ C. C = card (V\<inter>set l1)"]
      )  
  apply clarsimp_all  
  using V_ss  
  apply (auto simp: upt_eq_lel_conv Int_absorb2 am_to_adj_nodes_refine[OF AM])  
  done    

context 
  includes Network_Impl_Sepref_Register
begin  
  sepref_register init_C    
end    
  
sepref_thm fifo_init_C_impl is "(PR_CONST init_C)" 
    :: "am_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn" 
  unfolding init_C_def PR_CONST_def
  by sepref
concrete_definition (in -) fifo_init_C_impl 
  uses Network_Impl.fifo_init_C_impl.refine_raw is "(?f,_)\<in>_"
lemmas [sepref_fr_rules] = fifo_init_C_impl.refine[OF Network_Impl_axioms]
  
end \<comment> \<open>Network Implementation Locale\<close>
  
end
