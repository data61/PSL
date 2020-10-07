theory SINVAR_Dependability_norefl_impl
imports SINVAR_Dependability_norefl "../TopoS_Interface_impl"
begin


code_identifier code_module SINVAR_Dependability_norefl_impl => (Scala) SINVAR_Dependability_norefl


subsubsection \<open>SecurityInvariant Dependability norefl List Implementation\<close>


fun sinvar :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> dependability_level) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> (e1,e2) \<in> set (edgesL G). (num_reachable_norefl G e1) \<le> (nP e1))"


value "sinvar 
    \<lparr> nodesL = [1::nat,2,3,4], edgesL = [(1,2), (2,3), (3,4), (8,9),(9,8)] \<rparr>
    (\<lambda>e. 3)"
value "sinvar 
    \<lparr> nodesL = [1::nat,2,3,4,8,9,10], edgesL = [(1,2), (2,3), (3,4), (8,9),(9,8)] \<rparr>
    (\<lambda>e. 2)"



definition Dependability_norefl_offending_list:: "'v list_graph \<Rightarrow> ('v \<Rightarrow> dependability_level) \<Rightarrow> ('v \<times> 'v) list list" where
  "Dependability_norefl_offending_list = Generic_offending_list sinvar"



definition "NetModel_node_props P = (\<lambda> i. (case (node_properties P) i of Some property \<Rightarrow> property | None \<Rightarrow> SINVAR_Dependability_norefl.default_node_properties))"
lemma[code_unfold]: "SecurityInvariant.node_props SINVAR_Dependability_norefl.default_node_properties P = NetModel_node_props P"
apply(simp add: NetModel_node_props_def)
done

definition "Dependability_norefl_eval G P = (wf_list_graph G \<and>
  sinvar G (SecurityInvariant.node_props SINVAR_Dependability_norefl.default_node_properties P))"



lemma sinvar_correct: "wf_list_graph G \<Longrightarrow> SINVAR_Dependability_norefl.sinvar (list_graph_to_graph G) nP = sinvar G nP"
   apply(simp)
   apply(rule all_edges_list_I)
   apply(simp add: fun_eq_iff)
   apply(clarify)
   apply(rename_tac x)
   apply(drule_tac v="x" in  num_reachable_norefl_correct)
   apply presburger
done



interpretation Dependability_norefl_impl:TopoS_List_Impl 
  where default_node_properties=SINVAR_Dependability_norefl.default_node_properties
  and sinvar_spec=SINVAR_Dependability_norefl.sinvar
  and sinvar_impl=sinvar
  and receiver_violation=SINVAR_Dependability_norefl.receiver_violation
  and offending_flows_impl=Dependability_norefl_offending_list
  and node_props_impl=NetModel_node_props
  and eval_impl=Dependability_norefl_eval
 apply(unfold TopoS_List_Impl_def)
 apply(rule conjI)
  apply(rule conjI)
   apply(simp add: TopoS_Dependability_norefl; fail)
  apply(intro allI impI)
  apply(fact sinvar_correct)
 apply(rule conjI)
  apply(unfold Dependability_norefl_offending_list_def)
  apply(intro allI impI)
  apply(rule Generic_offending_list_correct)
   apply(assumption)
  apply(simp only: sinvar_correct)
 apply(rule conjI)
  apply(intro allI)
  apply(simp only: NetModel_node_props_def)
  apply(metis Dependability.node_props.simps Dependability.node_props_eq_node_props_formaldef)
 apply(simp only: Dependability_norefl_eval_def)
 apply(intro allI impI)
 apply(rule TopoS_eval_impl_proofrule[OF TopoS_Dependability_norefl])
 apply(simp only: sinvar_correct)
done


subsubsection \<open>packing\<close>
  definition SINVAR_LIB_Dependability_norefl :: "('v::vertex, SINVAR_Dependability_norefl.dependability_level) TopoS_packed" where
    "SINVAR_LIB_Dependability_norefl \<equiv> 
    \<lparr> nm_name = ''Dependability_norefl'', 
      nm_receiver_violation = SINVAR_Dependability_norefl.receiver_violation,
      nm_default = SINVAR_Dependability_norefl.default_node_properties, 
      nm_sinvar = sinvar,
      nm_offending_flows = Dependability_norefl_offending_list, 
      nm_node_props = NetModel_node_props,
      nm_eval = Dependability_norefl_eval
      \<rparr>"
  interpretation SINVAR_LIB_Dependability_norefl_interpretation: TopoS_modelLibrary SINVAR_LIB_Dependability_norefl
      SINVAR_Dependability_norefl.sinvar
    apply(unfold TopoS_modelLibrary_def SINVAR_LIB_Dependability_norefl_def)
    apply(rule conjI)
     apply(simp)
    apply(simp)
    by(unfold_locales)


hide_fact (open) sinvar_correct
hide_const (open) sinvar NetModel_node_props

end
