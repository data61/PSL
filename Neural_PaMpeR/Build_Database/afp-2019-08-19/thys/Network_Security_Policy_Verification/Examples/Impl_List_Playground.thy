theory Impl_List_Playground
imports "../TopoS_Impl"
begin


text\<open>The executbale models and the composition theory. We can build examples here\<close>


definition testGraph :: "string list_graph" where
  "testGraph \<equiv> \<lparr> nodesL = [''Master'', ''Slave1'', ''Slave2'', ''other1'', ''other2''], 
                 edgesL = [(''Master'', ''Slave1'')] \<rparr>"

lemma "wf_list_graph testGraph" by eval

definition req1 ::"(string SecurityInvariant)" where
  "req1 \<equiv> new_configured_list_SecurityInvariant SINVAR_SecGwExt_impl.SINVAR_LIB_PolEnforcePointExtended \<lparr> 
      node_properties = [''Master'' \<mapsto> PolEnforcePoint,
                         ''Slave1'' \<mapsto> DomainMember,
                         ''Slave2'' \<mapsto> DomainMember]
      \<rparr> ''req1''"


definition "req2 \<equiv> new_configured_list_SecurityInvariant SINVAR_NoRefl_impl.SINVAR_LIB_NoRefl \<lparr> 
      node_properties = [''Master'' \<mapsto> Refl,
                         ''other1'' \<mapsto> Refl,
                         ''other2'' \<mapsto> Refl]
      \<rparr> ''req2''"

definition "reqs = [req1, req2]"


definition "max_network = generate_valid_topology reqs 
      \<lparr>nodesL = nodesL testGraph, edgesL = List.product (nodesL testGraph) (nodesL testGraph) \<rparr>"

value "max_network"

ML\<open>
visualize_graph @{context} @{term "reqs"} @{term "max_network"};
\<close>

end
