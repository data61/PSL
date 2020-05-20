theory SINVAR_Subnets_impl
imports SINVAR_Subnets "../TopoS_Interface_impl"
begin


subsubsection \<open>SecurityInvariant Subnets List Implementation\<close>

code_identifier code_module SINVAR_Subnets_impl => (Scala) SINVAR_Subnets

fun sinvar :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> subnets) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> (e1,e2) \<in> set (edgesL G). allowed_subnet_flow (nP e1) (nP e2))"


definition Subnets_offending_list:: "'v list_graph \<Rightarrow> ('v \<Rightarrow> subnets) \<Rightarrow> ('v \<times> 'v) list list" where
  "Subnets_offending_list G nP = (if sinvar G nP then
    []
   else 
    [ [e \<leftarrow> edgesL G. case e of (e1,e2) \<Rightarrow> \<not> allowed_subnet_flow (nP e1) (nP e2)] ])"



definition "NetModel_node_props P = (\<lambda> i. (case (node_properties P) i of Some property \<Rightarrow> property | None \<Rightarrow> SINVAR_Subnets.default_node_properties))"
lemma[code_unfold]: "SecurityInvariant.node_props SINVAR_Subnets.default_node_properties P = NetModel_node_props P"
apply(simp add: NetModel_node_props_def)
done

definition "Subnets_eval G P = (wf_list_graph G \<and>
  sinvar G (SecurityInvariant.node_props SINVAR_Subnets.default_node_properties P))"


interpretation Subnets_impl:TopoS_List_Impl 
  where default_node_properties=SINVAR_Subnets.default_node_properties
  and sinvar_spec=SINVAR_Subnets.sinvar
  and sinvar_impl=sinvar
  and receiver_violation=SINVAR_Subnets.receiver_violation
  and offending_flows_impl=Subnets_offending_list
  and node_props_impl=NetModel_node_props
  and eval_impl=Subnets_eval
 apply(unfold TopoS_List_Impl_def)
 apply(rule conjI)
  apply(simp add: TopoS_Subnets list_graph_to_graph_def)
 apply(rule conjI)
  apply(simp add: list_graph_to_graph_def Subnets_offending_set Subnets_offending_set_def Subnets_offending_list_def)
 apply(rule conjI)
  apply(simp only: NetModel_node_props_def)
  apply(metis Subnets.node_props.simps Subnets.node_props_eq_node_props_formaldef)
 apply(simp only: Subnets_eval_def)
 apply(simp add: TopoS_eval_impl_proofrule[OF TopoS_Subnets])
 apply(simp_all add: list_graph_to_graph_def)
done


subsubsection \<open>Subnets packing\<close>
  definition SINVAR_LIB_Subnets :: "('v::vertex, SINVAR_Subnets.subnets) TopoS_packed" where
    "SINVAR_LIB_Subnets \<equiv> 
    \<lparr> nm_name = ''Subnets'', 
      nm_receiver_violation = SINVAR_Subnets.receiver_violation,
      nm_default = SINVAR_Subnets.default_node_properties, 
      nm_sinvar = sinvar,
      nm_offending_flows = Subnets_offending_list, 
      nm_node_props = NetModel_node_props,
      nm_eval = Subnets_eval
      \<rparr>"
  interpretation SINVAR_LIB_Subnets_interpretation: TopoS_modelLibrary SINVAR_LIB_Subnets
      SINVAR_Subnets.sinvar
    apply(unfold TopoS_modelLibrary_def SINVAR_LIB_Subnets_def)
    apply(rule conjI)
     apply(simp)
    apply(simp)
    by(unfold_locales)



text \<open>Examples\<close>
  
  definition example_net_sub :: "nat list_graph" where
  "example_net_sub \<equiv> \<lparr> nodesL = [1::nat,2,3,4, 8,9, 11,12, 42], 
    edgesL = [(1,2),(1,3),(1,4),(2,1),(2,3),(2,4),(3,1),(3,2),(3,4),(4,1),(4,2),(4,3), 
    (4,11),(1,11), 
    (8,9),(9,8),
    (8,12),
    (11,12),
    (11,42), (12,42), (3,42)] \<rparr>"
  value "wf_list_graph example_net_sub"
  
  definition example_conf_sub where
  "example_conf_sub \<equiv> ((\<lambda>e. SINVAR_Subnets.default_node_properties)
    (1 := Subnet 1, 2:= Subnet 1, 3:= Subnet 1, 4:=Subnet 1, 
     11:=BorderRouter 1,
     8:=Subnet 2, 9:=Subnet 2, 
     12:=BorderRouter 2,
     42 := Unassigned))" 
  
  value "sinvar example_net_sub example_conf_sub"
  
  
  definition example_net_sub_invalid where
  "example_net_sub_invalid \<equiv> example_net_sub\<lparr>edgesL := (42,4)#(3,8)#(11,8)#(edgesL example_net_sub)\<rparr>"
  
  value "sinvar example_net_sub_invalid example_conf_sub"
  value "Subnets_offending_list example_net_sub_invalid example_conf_sub"
  


  
  value "sinvar 
      \<lparr> nodesL = [1::nat,2,3,4], edgesL = [(1,2), (2,3), (3,4), (8,9),(9,8)] \<rparr>
      (\<lambda>e. SINVAR_Subnets.default_node_properties)"
  value "sinvar 
      \<lparr> nodesL = [1::nat,2,3,4,8,9,11,12], edgesL = [(1,2),(2,3),(3,4), (4,11),(1,11), (8,9),(9,8),(8,12),  (11,12)] \<rparr>
      ((\<lambda>e. SINVAR_Subnets.default_node_properties)(1 := Subnet 1, 2:= Subnet 1, 3:= Subnet 1, 4:=Subnet 1, 11:=BorderRouter 1,
                                    8:=Subnet 2, 9:=Subnet 2, 12:=BorderRouter 2))"
  value "sinvar 
      \<lparr> nodesL = [1::nat,2,3,4,8,9,11,12], edgesL = [(1,2),(2,3),(3,4), (4,11),(1,11), (8,9),(9,8),(8,12),  (11,12)] \<rparr>
      ((\<lambda>e. SINVAR_Subnets.default_node_properties)(1 := Subnet 1, 2:= Subnet 1, 3:= Subnet 1, 4:=Subnet 1, 11:=BorderRouter 1))"
  value "sinvar 
      \<lparr> nodesL = [1::nat,2,3,4,8,9,10], edgesL = [(1,2), (2,3), (3,4), (8,9),(9,8)] \<rparr>
      ((\<lambda>e. SINVAR_Subnets.default_node_properties)(8:=Subnet 8, 9:=Subnet 8))"
  

hide_const (open) NetModel_node_props
hide_const (open) sinvar

end
