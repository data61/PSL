theory SINVAR_CommunicationPartners_impl
imports SINVAR_CommunicationPartners "../TopoS_Interface_impl"
begin

code_identifier code_module SINVAR_CommunicationPartners_impl => (Scala) SINVAR_CommunicationPartners


subsubsection \<open>SecurityInvariant CommunicationPartners List Implementation\<close>


fun sinvar :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> 'v node_config) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> (s,r) \<in> set (edgesL G). s \<noteq> r \<longrightarrow> SINVAR_CommunicationPartners.allowed_flow (nP s) s (nP r) r)"



definition CommunicationPartners_offending_list:: "'v list_graph \<Rightarrow> ('v \<Rightarrow> 'v node_config) \<Rightarrow> ('v \<times> 'v) list list" where
  "CommunicationPartners_offending_list G nP = (if sinvar G nP then
    []
   else 
    [ [e \<leftarrow> edgesL G. case e of (e1,e2) \<Rightarrow> e1 \<noteq> e2 \<and> \<not> allowed_flow (nP e1) e1 (nP e2) e2] ])"


thm SINVAR_CommunicationPartners.CommunicationPartners.node_props.simps
definition "NetModel_node_props (P::('v::vertex, 'v node_config) TopoS_Params) = 
  (\<lambda> i. (case (node_properties P) i of Some property \<Rightarrow> property | None \<Rightarrow> SINVAR_CommunicationPartners.default_node_properties))"
lemma[code_unfold]: "SecurityInvariant.node_props SINVAR_CommunicationPartners.default_node_properties P = NetModel_node_props P"
apply(simp add: NetModel_node_props_def)
done

definition "CommunicationPartners_eval G P = (wf_list_graph G \<and> 
  sinvar G (SecurityInvariant.node_props SINVAR_CommunicationPartners.default_node_properties P))"


interpretation CommunicationPartners_impl:TopoS_List_Impl 
  where default_node_properties=SINVAR_CommunicationPartners.default_node_properties
  and sinvar_spec=SINVAR_CommunicationPartners.sinvar
  and sinvar_impl=sinvar
  and receiver_violation=SINVAR_CommunicationPartners.receiver_violation
  and offending_flows_impl=CommunicationPartners_offending_list
  and node_props_impl=NetModel_node_props
  and eval_impl=CommunicationPartners_eval
 apply(unfold TopoS_List_Impl_def)
 apply(rule conjI)
  apply(simp add: TopoS_SubnetsInGW list_graph_to_graph_def; fail)
 apply(rule conjI)
  apply(simp add: list_graph_to_graph_def CommunicationPartners_offending_set CommunicationPartners_offending_set_def CommunicationPartners_offending_list_def)
 apply(rule conjI)
  apply(simp only: NetModel_node_props_def)
  apply(metis CommunicationPartners.node_props.simps CommunicationPartners.node_props_eq_node_props_formaldef)
 apply(simp only: CommunicationPartners_eval_def)
 apply(simp add: TopoS_eval_impl_proofrule[OF TopoS_SubnetsInGW])
 apply(simp_all add: list_graph_to_graph_def)
done


subsubsection \<open>CommunicationPartners packing\<close>
  definition SINVAR_LIB_CommunicationPartners :: "('v::vertex, 'v SINVAR_CommunicationPartners.node_config) TopoS_packed" where
    "SINVAR_LIB_CommunicationPartners \<equiv> 
    \<lparr> nm_name = ''CommunicationPartners'', 
      nm_receiver_violation = SINVAR_CommunicationPartners.receiver_violation,
      nm_default = SINVAR_CommunicationPartners.default_node_properties, 
      nm_sinvar = sinvar,
      nm_offending_flows = CommunicationPartners_offending_list, 
      nm_node_props = NetModel_node_props,
      nm_eval = CommunicationPartners_eval
      \<rparr>"
  interpretation SINVAR_LIB_CommunicationPartners_interpretation: TopoS_modelLibrary SINVAR_LIB_CommunicationPartners
      SINVAR_CommunicationPartners.sinvar
    apply(unfold TopoS_modelLibrary_def SINVAR_LIB_CommunicationPartners_def)
    apply(rule conjI)
     apply(simp)
    apply(simp)
    by(unfold_locales)



text \<open>Examples\<close>



hide_const (open) NetModel_node_props
hide_const (open) sinvar

end
