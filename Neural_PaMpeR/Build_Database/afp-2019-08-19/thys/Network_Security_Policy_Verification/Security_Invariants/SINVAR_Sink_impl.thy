theory SINVAR_Sink_impl
imports SINVAR_Sink "../TopoS_Interface_impl"
begin

code_identifier code_module SINVAR_Sink_impl => (Scala) SINVAR_Sink


subsubsection \<open>SecurityInvariant Sink (IFS) List Implementation\<close>

fun sinvar :: "'v list_graph \<Rightarrow> ('v \<Rightarrow> node_config) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> (e1,e2) \<in> set (edgesL G). e1 \<noteq> e2 \<longrightarrow> SINVAR_Sink.allowed_sink_flow (nP e1) (nP e2))"


definition Sink_offending_list:: "'v list_graph \<Rightarrow> ('v \<Rightarrow> SINVAR_Sink.node_config) \<Rightarrow> ('v \<times> 'v) list list" where
  "Sink_offending_list G nP = (if sinvar G nP then
    []
   else 
    [ [e \<leftarrow> edgesL G. case e of (e1,e2) \<Rightarrow> e1 \<noteq> e2 \<and> \<not> allowed_sink_flow (nP e1) (nP e2)] ])"



definition "NetModel_node_props P = (\<lambda> i. (case (node_properties P) i of Some property \<Rightarrow> property | None \<Rightarrow> SINVAR_Sink.default_node_properties))"
lemma[code_unfold]: "SecurityInvariant.node_props SINVAR_Sink.default_node_properties P = NetModel_node_props P"
apply(simp add: NetModel_node_props_def)
done

definition "Sink_eval G P = (wf_list_graph G \<and>
  sinvar G (SecurityInvariant.node_props SINVAR_Sink.default_node_properties P))"


interpretation Sink_impl:TopoS_List_Impl 
  where default_node_properties=SINVAR_Sink.default_node_properties
  and sinvar_spec=SINVAR_Sink.sinvar
  and sinvar_impl=sinvar
  and receiver_violation=SINVAR_Sink.receiver_violation
  and offending_flows_impl=Sink_offending_list
  and node_props_impl=NetModel_node_props
  and eval_impl=Sink_eval
 apply(unfold TopoS_List_Impl_def)
 apply(rule conjI)
  apply(simp add: TopoS_Sink list_graph_to_graph_def)
 apply(rule conjI)
  apply(simp add: list_graph_to_graph_def Sink_offending_set Sink_offending_set_def Sink_offending_list_def)
 apply(rule conjI)
  apply(simp only: NetModel_node_props_def)
  apply(metis Sink.node_props.simps Sink.node_props_eq_node_props_formaldef)
 apply(simp only: Sink_eval_def)
 apply(intro allI)
 apply(rule TopoS_eval_impl_proofrule[OF TopoS_Sink])
 apply(simp_all add: list_graph_to_graph_def)
done


subsubsection \<open>Sink packing\<close>
  definition SINVAR_LIB_Sink :: "('v::vertex, node_config) TopoS_packed" where
    "SINVAR_LIB_Sink \<equiv> 
    \<lparr> nm_name = ''Sink'', 
      nm_receiver_violation = SINVAR_Sink.receiver_violation,
      nm_default = SINVAR_Sink.default_node_properties, 
      nm_sinvar = sinvar,
      nm_offending_flows = Sink_offending_list, 
      nm_node_props = NetModel_node_props,
      nm_eval = Sink_eval
      \<rparr>"
  interpretation SINVAR_LIB_Sink_interpretation: TopoS_modelLibrary SINVAR_LIB_Sink
      SINVAR_Sink.sinvar
    apply(unfold TopoS_modelLibrary_def SINVAR_LIB_Sink_def)
    apply(rule conjI)
     apply(simp)
    apply(simp)
    by(unfold_locales)

text \<open>Examples\<close>
  definition example_net_sink :: "nat list_graph" where
  "example_net_sink \<equiv> \<lparr> nodesL = [1::nat,2,3, 8, 11,12], 
    edgesL = [(1,8),(1,2), (2,8),(3,8),(4,8), (2,3),(3,2), (11,8),(12,8), (11,12), (1,12)] \<rparr>"
  value "wf_list_graph example_net_sink"
  
  definition example_conf_sink where
  "example_conf_sink \<equiv> (\<lambda>e. SINVAR_Sink.default_node_properties)(8:= Sink, 2:= SinkPool, 3:= SinkPool, 4:= SinkPool)" 
  
  value "sinvar example_net_sink example_conf_sink"
  value "Sink_offending_list example_net_sink example_conf_sink"


  definition example_net_sink_invalid where
  "example_net_sink_invalid \<equiv> example_net_sink\<lparr>edgesL := (2,1)#(8,11)#(8,2)#(edgesL example_net_sink)\<rparr>"

  value "sinvar example_net_sink_invalid example_conf_sink"
  value "Sink_offending_list example_net_sink_invalid example_conf_sink"


hide_const (open) NetModel_node_props
hide_const (open) sinvar

end
