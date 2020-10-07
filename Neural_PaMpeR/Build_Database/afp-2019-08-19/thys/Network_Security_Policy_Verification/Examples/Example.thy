theory Example
imports "../TopoS_Interface" "../TopoS_Library"
begin

subsection \<open>Network Graph and Security Requirements\<close>

  text\<open>We define the network\<close>
  definition example_net_secgw :: "nat list_graph" where
  "example_net_secgw \<equiv> \<lparr> nodesL = [1::nat,2,3, 8, 11,12], 
    edgesL = [
      (1,8),(8,2),(2,8),(8,1), 
      (8,11),(8,12), 
      (11,12)] \<rparr>"
  value "wf_list_graph example_net_secgw"


  text\<open>We add two security requirements\<close>
  definition NMParams_secgw_1 :: "(nat, secgw_member) TopoS_Params" where
  "NMParams_secgw_1 \<equiv> \<lparr> node_properties = [1 \<mapsto> DomainMember, 
                                     2 \<mapsto> DomainMember, 
                                     3 \<mapsto> DomainMember,
                                     8 \<mapsto> PolEnforcePoint] \<rparr>"


  definition NMParams_blptrusted_1 :: "(nat, SINVAR_BLPtrusted.node_config) TopoS_Params" where
  "NMParams_blptrusted_1 \<equiv> \<lparr> node_properties = [1 \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>, 
                                     2 \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>, 
                                     3 \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
                                     8 \<mapsto> \<lparr> security_level = 0, trusted = True \<rparr>] \<rparr>"

  text\<open>Both security requirements fulfilled?\<close>
  value "PolEnforcePoint_eval example_net_secgw NMParams_secgw_1"
  value "SINVAR_BLPtrusted_impl.BLP_eval example_net_secgw NMParams_blptrusted_1"


text\<open>Add violations!\<close>
  definition example_net_secgw_invalid where
  "example_net_secgw_invalid \<equiv> example_net_secgw\<lparr>edgesL := (1,11)#(11,1)#(11,8)#(1,2)#(edgesL example_net_secgw)\<rparr>"

  text\<open>Security Requirement still fulfilled?\<close>
  value "PolEnforcePoint_eval example_net_secgw_invalid NMParams_secgw_1"
  text\<open>Whom to blame?\<close>
  value "PolEnforcePointExtended_offending_list example_net_secgw_invalid
          (SINVAR_SecGwExt_impl.NetModel_node_props NMParams_secgw_1)"

  text\<open>Security Requirement still fulfilled?\<close>
  value "SINVAR_BLPtrusted_impl.BLP_eval example_net_secgw_invalid NMParams_blptrusted_1"
  text\<open>Whom to blame?\<close>
  value "SINVAR_BLPtrusted_impl.BLP_offending_list example_net_secgw_invalid
      (SINVAR_BLPtrusted_impl.NetModel_node_props NMParams_blptrusted_1)"


end
