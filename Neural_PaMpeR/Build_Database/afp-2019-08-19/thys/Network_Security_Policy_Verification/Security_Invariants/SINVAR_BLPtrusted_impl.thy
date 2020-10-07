theory SINVAR_BLPtrusted_impl
imports SINVAR_BLPtrusted "../TopoS_Interface_impl"
begin

subsubsection \<open>SecurityInvariant List Implementation\<close>

code_identifier code_module SINVAR_BLPtrusted_impl => (Scala) SINVAR_BLPtrusted

fun sinvar :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> SINVAR_BLPtrusted.node_config) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> (e1,e2) \<in> set (edgesL G). (if trusted (nP e2) then True else security_level (nP e1) \<le> security_level (nP e2) ))"


definition BLP_offending_list:: "'v list_graph \<Rightarrow> ('v \<Rightarrow> SINVAR_BLPtrusted.node_config) \<Rightarrow> ('v \<times> 'v) list list" where
  "BLP_offending_list G nP = (if sinvar G nP then
    []
   else 
    [ [e \<leftarrow> edgesL G. case e of (e1,e2) \<Rightarrow> \<not> SINVAR_BLPtrusted.BLP_P (nP e1) (nP e2)] ])"



definition "NetModel_node_props P = (\<lambda> i. (case (node_properties P) i of Some property \<Rightarrow> property | None \<Rightarrow> SINVAR_BLPtrusted.default_node_properties))"
lemma[code_unfold]: "SecurityInvariant.node_props SINVAR_BLPtrusted.default_node_properties P = NetModel_node_props P"
apply(simp add: NetModel_node_props_def)
done

definition "BLP_eval G P = (wf_list_graph G \<and>
  sinvar G (SecurityInvariant.node_props SINVAR_BLPtrusted.default_node_properties P))"


interpretation BLPtrusted_impl:TopoS_List_Impl 
  where default_node_properties=SINVAR_BLPtrusted.default_node_properties
  and sinvar_spec=SINVAR_BLPtrusted.sinvar
  and sinvar_impl=sinvar
  and receiver_violation=SINVAR_BLPtrusted.receiver_violation
  and offending_flows_impl=BLP_offending_list
  and node_props_impl=NetModel_node_props
  and eval_impl=BLP_eval
 apply(unfold TopoS_List_Impl_def)
 apply(rule conjI)
  apply(simp add: TopoS_BLPtrusted list_graph_to_graph_def; fail)
 apply(rule conjI)
  apply(simp add: list_graph_to_graph_def BLP_offending_set BLP_offending_set_def BLP_offending_list_def)
 apply(rule conjI)
  apply(simp only: NetModel_node_props_def)
  apply(metis BLPtrusted.node_props.simps BLPtrusted.node_props_eq_node_props_formaldef)
 apply(simp only: BLP_eval_def)
 apply(intro allI)
 apply(rule TopoS_eval_impl_proofrule[OF TopoS_BLPtrusted])
 apply(simp_all add: list_graph_to_graph_def)
done



subsubsection \<open>BLPtrusted packing\<close>
  definition SINVAR_LIB_BLPtrusted :: "('v::vertex, SINVAR_BLPtrusted.node_config) TopoS_packed" where
    "SINVAR_LIB_BLPtrusted \<equiv> 
    \<lparr> nm_name = ''BLPtrusted'', 
      nm_receiver_violation = SINVAR_BLPtrusted.receiver_violation,
      nm_default = SINVAR_BLPtrusted.default_node_properties, 
      nm_sinvar = sinvar,
      nm_offending_flows = BLP_offending_list, 
      nm_node_props = NetModel_node_props,
      nm_eval = BLP_eval
      \<rparr>"
  interpretation SINVAR_LIB_BLPtrusted_interpretation: TopoS_modelLibrary SINVAR_LIB_BLPtrusted 
      SINVAR_BLPtrusted.sinvar
    apply(unfold TopoS_modelLibrary_def SINVAR_LIB_BLPtrusted_def)
    apply(rule conjI)
     apply(simp)
    apply(simp)
    by(unfold_locales)

subsubsection\<open>Example\<close>
 (*TODO*)


export_code SINVAR_LIB_BLPtrusted checking Scala


hide_const (open) NetModel_node_props BLP_offending_list BLP_eval

hide_const (open) sinvar

end
