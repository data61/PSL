theory SINVAR_SecGwExt_impl
imports SINVAR_SecGwExt "../TopoS_Interface_impl"
begin

code_identifier code_module SINVAR_SecGwExt_impl => (Scala) SINVAR_SecGwExt

subsubsection \<open>SecurityInvariant PolEnforcePointExtended List Implementation\<close>

fun sinvar :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> SINVAR_SecGwExt.secgw_member) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> (e1,e2) \<in> set (edgesL G). e1 \<noteq> e2 \<longrightarrow> SINVAR_SecGwExt.allowed_secgw_flow (nP e1) (nP e2))"

definition PolEnforcePointExtended_offending_list:: "'v list_graph \<Rightarrow> ('v \<Rightarrow> secgw_member) \<Rightarrow> ('v \<times> 'v) list list" where
  "PolEnforcePointExtended_offending_list G nP = (if sinvar G nP then
    []
   else 
    [ [e \<leftarrow> edgesL G. case e of (e1,e2) \<Rightarrow> e1 \<noteq> e2 \<and> \<not> allowed_secgw_flow (nP e1) (nP e2)] ])"



definition "NetModel_node_props P = (\<lambda> i. (case (node_properties P) i of Some property \<Rightarrow> property | None \<Rightarrow> SINVAR_SecGwExt.default_node_properties))"
lemma[code_unfold]: "SecurityInvariant.node_props SINVAR_SecGwExt.default_node_properties P = NetModel_node_props P"
apply(simp add: NetModel_node_props_def)
done

definition "PolEnforcePoint_eval G P = (wf_list_graph G \<and>
  sinvar G (SecurityInvariant.node_props SINVAR_SecGwExt.default_node_properties P))"


interpretation PolEnforcePoint_impl:TopoS_List_Impl 
  where default_node_properties=SINVAR_SecGwExt.default_node_properties
  and sinvar_spec=SINVAR_SecGwExt.sinvar
  and sinvar_impl=sinvar
  and receiver_violation=SINVAR_SecGwExt.receiver_violation
  and offending_flows_impl=PolEnforcePointExtended_offending_list
  and node_props_impl=NetModel_node_props
  and eval_impl=PolEnforcePoint_eval
 apply(unfold TopoS_List_Impl_def)
 apply(rule conjI)
  apply(simp add: TopoS_PolEnforcePointExtended list_graph_to_graph_def)
 apply(rule conjI)
  apply(simp add: list_graph_to_graph_def PolEnforcePointExtended_offending_set PolEnforcePointExtended_offending_set_def PolEnforcePointExtended_offending_list_def)
 apply(rule conjI)
  apply(simp only: NetModel_node_props_def)
  apply(metis PolEnforcePointExtended.node_props.simps PolEnforcePointExtended.node_props_eq_node_props_formaldef)
 apply(simp only: PolEnforcePoint_eval_def)
 apply(simp add: TopoS_eval_impl_proofrule[OF TopoS_PolEnforcePointExtended])
 apply(simp_all add: list_graph_to_graph_def)
done


subsubsection \<open>PolEnforcePoint packing\<close>
  definition SINVAR_LIB_PolEnforcePointExtended :: "('v::vertex, secgw_member) TopoS_packed" where
    "SINVAR_LIB_PolEnforcePointExtended \<equiv> 
    \<lparr> nm_name = ''PolEnforcePointExtended'', 
      nm_receiver_violation = SINVAR_SecGwExt.receiver_violation,
      nm_default = SINVAR_SecGwExt.default_node_properties, 
      nm_sinvar = sinvar,
      nm_offending_flows = PolEnforcePointExtended_offending_list, 
      nm_node_props = NetModel_node_props,
      nm_eval = PolEnforcePoint_eval
      \<rparr>"
  interpretation SINVAR_LIB_PolEnforcePointExtended_interpretation: TopoS_modelLibrary SINVAR_LIB_PolEnforcePointExtended 
      SINVAR_SecGwExt.sinvar
    apply(unfold TopoS_modelLibrary_def SINVAR_LIB_PolEnforcePointExtended_def)
    apply(rule conjI)
     apply(simp)
    apply(simp)
    by(unfold_locales)


text \<open>Examples\<close>
  definition example_net_secgw :: "nat list_graph" where
  "example_net_secgw \<equiv> \<lparr> nodesL = [1::nat,2, 3, 8,9, 11,12], 
    edgesL = [(3,8),(8,3),(2,8),(8,1),(1,9),(9,2),(2,9),(9,1), (1,3), (8,11),(8,12), (11,9), (11,3), (11,12)] \<rparr>"
  value "wf_list_graph example_net_secgw"
  
  definition example_conf_secgw where
  "example_conf_secgw \<equiv> ((\<lambda>e. SINVAR_SecGwExt.default_node_properties)
    (1 := DomainMember, 2:= DomainMember, 3:= AccessibleMember,
     8:= PolEnforcePoint, 9:= PolEnforcePointIN))" 
  
  export_code sinvar checking SML
  definition "test = sinvar \<lparr> nodesL=[1::nat], edgesL=[] \<rparr> (\<lambda>_. SINVAR_SecGwExt.default_node_properties)"
  export_code test checking SML
  value(**) "sinvar \<lparr> nodesL=[1::nat], edgesL=[] \<rparr> (\<lambda>_. SINVAR_SecGwExt.default_node_properties)"

  value(**) "sinvar example_net_secgw example_conf_secgw"
  value(**) "PolEnforcePoint_offending_list example_net_secgw example_conf_secgw"


  definition example_net_secgw_invalid where
  "example_net_secgw_invalid \<equiv> example_net_secgw\<lparr>edgesL := (3,1)#(11,1)#(11,8)#(1,2)#(edgesL example_net_secgw)\<rparr>"

  value(**) "sinvar example_net_secgw_invalid example_conf_secgw"
  value(**) "PolEnforcePoint_offending_list example_net_secgw_invalid example_conf_secgw"


hide_const (open) NetModel_node_props
hide_const (open) sinvar

end
