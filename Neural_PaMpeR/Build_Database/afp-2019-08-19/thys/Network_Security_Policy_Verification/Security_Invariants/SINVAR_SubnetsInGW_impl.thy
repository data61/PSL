theory SINVAR_SubnetsInGW_impl
imports SINVAR_SubnetsInGW "../TopoS_Interface_impl"
begin

code_identifier code_module SINVAR_SubnetsInGW_impl => (Scala) SINVAR_SubnetsInGW

subsubsection \<open>SecurityInvariant SubnetsInGw List Implementation\<close>

fun sinvar :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> subnets) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> (e1,e2) \<in> set (edgesL G). SINVAR_SubnetsInGW.allowed_subnet_flow (nP e1) (nP e2))"


definition SubnetsInGW_offending_list:: "'v list_graph \<Rightarrow> ('v \<Rightarrow> subnets) \<Rightarrow> ('v \<times> 'v) list list" where
  "SubnetsInGW_offending_list G nP = (if sinvar G nP then
    []
   else 
    [ [e \<leftarrow> edgesL G. case e of (e1,e2) \<Rightarrow> \<not> allowed_subnet_flow (nP e1) (nP e2)] ])"



definition "NetModel_node_props P = (\<lambda> i. (case (node_properties P) i of Some property \<Rightarrow> property | None \<Rightarrow> SINVAR_SubnetsInGW.default_node_properties))"
lemma[code_unfold]: "SecurityInvariant.node_props SINVAR_SubnetsInGW.default_node_properties P = NetModel_node_props P"
apply(simp add: NetModel_node_props_def)
done

definition "SubnetsInGW_eval G P = (wf_list_graph G \<and>
  sinvar G (SecurityInvariant.node_props SINVAR_SubnetsInGW.default_node_properties P))"


interpretation SubnetsInGW_impl:TopoS_List_Impl 
  where default_node_properties=SINVAR_SubnetsInGW.default_node_properties
  and sinvar_spec=SINVAR_SubnetsInGW.sinvar
  and sinvar_impl=sinvar
  and receiver_violation=SINVAR_SubnetsInGW.receiver_violation
  and offending_flows_impl=SubnetsInGW_offending_list
  and node_props_impl=NetModel_node_props
  and eval_impl=SubnetsInGW_eval
 apply(unfold TopoS_List_Impl_def)
 apply(rule conjI)
  apply(simp add: TopoS_SubnetsInGW list_graph_to_graph_def)
 apply(rule conjI)
  apply(simp add: list_graph_to_graph_def SubnetsInGW_offending_set SubnetsInGW_offending_set_def SubnetsInGW_offending_list_def)
 apply(rule conjI)
  apply(simp only: NetModel_node_props_def)
  apply(metis SubnetsInGW.node_props.simps SubnetsInGW.node_props_eq_node_props_formaldef)
 apply(simp only: SubnetsInGW_eval_def)
 apply(simp add: TopoS_eval_impl_proofrule[OF TopoS_SubnetsInGW])
 apply(simp_all add: list_graph_to_graph_def)
done



subsubsection \<open>SubnetsInGW packing\<close>
  definition SINVAR_LIB_SubnetsInGW :: "('v::vertex, subnets) TopoS_packed" where
    "SINVAR_LIB_SubnetsInGW \<equiv> 
    \<lparr> nm_name = ''SubnetsInGW'', 
      nm_receiver_violation = SINVAR_SubnetsInGW.receiver_violation,
      nm_default = SINVAR_SubnetsInGW.default_node_properties, 
      nm_sinvar = sinvar,
      nm_offending_flows = SubnetsInGW_offending_list, 
      nm_node_props = NetModel_node_props,
      nm_eval = SubnetsInGW_eval
      \<rparr>"
  interpretation SINVAR_LIB_SubnetsInGW_interpretation: TopoS_modelLibrary SINVAR_LIB_SubnetsInGW
      SINVAR_SubnetsInGW.sinvar
    apply(unfold TopoS_modelLibrary_def SINVAR_LIB_SubnetsInGW_def)
    apply(rule conjI)
     apply(simp)
    apply(simp)
    by(unfold_locales)

text \<open>Examples\<close>

definition example_net_sub :: "nat list_graph" where
"example_net_sub \<equiv> \<lparr> nodesL = [1::nat,2,3,4, 8, 11,12,42], 
  edgesL = [(1,2),(1,3),(1,4),(2,1),(2,3),(2,4),(3,1),(3,2),(3,4),(4,1),(4,2),(4,3), 
  (8,1),(8,2),
  (8,11),
  (11,8), (12,8),
  (11,42), (12,42), (8,42)] \<rparr>"
value "wf_list_graph example_net_sub"

definition example_conf_sub where
"example_conf_sub \<equiv> ((\<lambda>e. SINVAR_SubnetsInGW.default_node_properties)
  (1 := Member, 2:= Member, 3:= Member, 4:=Member,
   8:=InboundGateway))" 

value "sinvar example_net_sub example_conf_sub"


definition example_net_sub_invalid where
"example_net_sub_invalid \<equiv> example_net_sub\<lparr>edgesL := (42,4)#(edgesL example_net_sub)\<rparr>"

value "sinvar example_net_sub_invalid example_conf_sub"
value "SubnetsInGW_offending_list example_net_sub_invalid example_conf_sub"



hide_const (open) NetModel_node_props
hide_const (open) sinvar

end
