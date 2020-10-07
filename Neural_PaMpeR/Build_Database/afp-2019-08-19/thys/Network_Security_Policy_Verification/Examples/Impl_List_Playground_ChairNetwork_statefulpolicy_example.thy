theory Impl_List_Playground_ChairNetwork_statefulpolicy_example
imports "../TopoS_Impl"
begin


text\<open>An example of our chair network [simplified]\<close>

text\<open>Our access control view on the network\<close>
  definition ChairNetwork_empty :: "string list_graph" where
    "ChairNetwork_empty \<equiv> \<lparr> nodesL = [''WebSrv'', ''FilesSrv'', ''Printer'',
                                ''Students'',
                                ''Employees'',
                                ''Internet''],
                      edgesL = [] \<rparr>"
  
  lemma "wf_list_graph ChairNetwork_empty" by eval


subsection\<open>Our security requirements\<close>
  subsubsection\<open>We have a server with confidential data\<close>
    definition ConfidentialChairData::"(string SecurityInvariant)" where
      "ConfidentialChairData \<equiv> new_configured_list_SecurityInvariant SINVAR_BLPtrusted_impl.SINVAR_LIB_BLPtrusted \<lparr> 
          node_properties = [''FilesSrv'' \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
                             ''Employees'' \<mapsto> \<lparr> security_level = 0, trusted = True \<rparr>]
          \<rparr> ''confidential data''"


  subsubsection\<open>accessibly by employees and students\<close>
    definition "PrintingACL \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_CommunicationPartners \<lparr> 
          node_properties = [''Printer'' \<mapsto> Master [''Employees'', ''Students''],
                             ''Employees'' \<mapsto> Care,
                             ''Students'' \<mapsto> Care]
          \<rparr> ''printing acl''"

  subsubsection\<open>Printers are information sinks\<close>
    definition "PrintingSink \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_Sink \<lparr> 
          node_properties = [''Printer'' \<mapsto> Sink]
          \<rparr> ''printing sink''"



  subsubsection\<open>Students and Employees may access each other but are not accessible from the outside\<close>
    definition "InternalSubnet \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_SubnetsInGW \<lparr> 
          node_properties = [''Students'' \<mapsto> Member, ''Employees'' \<mapsto> Member]
          \<rparr> ''internal subnet''"


  subsubsection\<open>The files server is only accessibly by employees\<close>
    definition "FilesSrvACL \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_CommunicationPartners \<lparr> 
          node_properties = [''FilesSrv'' \<mapsto> Master [''Employees''],
                             ''Employees'' \<mapsto> Care]
          \<rparr> ''file srv acl''"


definition "ChairSecurityRequirements = [ConfidentialChairData, PrintingACL, PrintingSink, InternalSubnet, FilesSrvACL]"

lemma "\<forall>m \<in> set ChairSecurityRequirements. implc_sinvar m ChairNetwork_empty" by eval

value "implc_get_offending_flows ChairSecurityRequirements ChairNetwork_empty"
value "generate_valid_topology ChairSecurityRequirements ChairNetwork_empty"

value "List.product (nodesL ChairNetwork_empty) (nodesL ChairNetwork_empty)"

definition "ChairNetwork = generate_valid_topology ChairSecurityRequirements 
      \<lparr>nodesL = nodesL ChairNetwork_empty, edgesL = List.product (nodesL ChairNetwork_empty) (nodesL ChairNetwork_empty) \<rparr>"

value "ChairNetwork"


ML\<open>
visualize_graph @{context} @{term "ChairSecurityRequirements"} @{term "ChairNetwork"};
\<close>


definition "ChairNetwork_stateful_IFS = \<lparr> hostsL = nodesL ChairNetwork, flows_fixL = edgesL ChairNetwork, flows_stateL = filter_IFS_no_violations ChairNetwork ChairSecurityRequirements \<rparr>"
value "edgesL ChairNetwork"
value "filter_IFS_no_violations ChairNetwork ChairSecurityRequirements"
value "ChairNetwork_stateful_IFS"
lemma "set (flows_stateL ChairNetwork_stateful_IFS) \<subseteq> (set (flows_fixL ChairNetwork_stateful_IFS))" by eval (*must always hold*)
value "(set (flows_fixL ChairNetwork_stateful_IFS)) - set (flows_stateL ChairNetwork_stateful_IFS)"
(*only problems: printers!!!*)
value "stateful_list_policy_to_list_graph ChairNetwork_stateful_IFS"
lemma "set (filter_IFS_no_violations ChairNetwork [ConfidentialChairData]) = set (edgesL ChairNetwork)" by eval

definition "ChairNetwork_stateful_ACS = \<lparr> hostsL = nodesL ChairNetwork, flows_fixL = edgesL ChairNetwork, flows_stateL = filter_compliant_stateful_ACS ChairNetwork ChairSecurityRequirements \<rparr>"
value "edgesL ChairNetwork"
value "filter_compliant_stateful_ACS ChairNetwork ChairSecurityRequirements"
value "ChairNetwork_stateful_ACS"
lemma "set (flows_stateL ChairNetwork_stateful_ACS) \<subseteq> (set (flows_fixL ChairNetwork_stateful_ACS))"
  by eval (*must always hold*)
value "(set (flows_fixL ChairNetwork_stateful_ACS)) - set (flows_stateL ChairNetwork_stateful_ACS)"

(*flows that are already allowed in both directions are not marked as stateful*)
value "((set (flows_fixL ChairNetwork_stateful_ACS)) - set (flows_stateL ChairNetwork_stateful_ACS)) - set (backlinks (flows_fixL ChairNetwork_stateful_ACS))"

(*the new backflows*)
value "set (edgesL (stateful_list_policy_to_list_graph ChairNetwork_stateful_ACS)) - (set (edgesL ChairNetwork))"

(*the resulting ACS graph*)
value "stateful_list_policy_to_list_graph ChairNetwork_stateful_ACS"


value "generate_valid_stateful_policy_IFSACS ChairNetwork ChairSecurityRequirements"
value "generate_valid_stateful_policy_IFSACS_2 ChairNetwork ChairSecurityRequirements"
lemma "set (flows_fixL (generate_valid_stateful_policy_IFSACS ChairNetwork ChairSecurityRequirements)) =
       set (flows_fixL (generate_valid_stateful_policy_IFSACS_2 ChairNetwork ChairSecurityRequirements))" by eval
lemma "set (flows_stateL (generate_valid_stateful_policy_IFSACS ChairNetwork ChairSecurityRequirements)) =
       set (flows_stateL (generate_valid_stateful_policy_IFSACS_2 ChairNetwork ChairSecurityRequirements))" by eval


definition "ChairNetwork_stateful = generate_valid_stateful_policy_IFSACS ChairNetwork ChairSecurityRequirements"


ML_val\<open>
visualize_edges @{context} @{term "flows_fixL ChairNetwork_stateful"} 
    [("edge [dir=\"arrow\", style=dashed, color=\"#FF8822\", constraint=false]", @{term "flows_stateL ChairNetwork_stateful"})] ""; 
\<close>

(*these requirements impose no restrictoins on the stateful flows*)
definition "ChairNetwork_stateful_v2 = generate_valid_stateful_policy_IFSACS ChairNetwork
    [ConfidentialChairData, PrintingACL,  InternalSubnet, FilesSrvACL]"
ML_val\<open>
visualize_edges @{context} @{term "flows_fixL ChairNetwork_stateful_v2"} 
    [("edge [dir=\"arrow\", style=dashed, color=\"#FF8822\", constraint=false]",
     @{term "flows_stateL ChairNetwork_stateful_v2"})] ""; 
\<close>

(*The sink requirements imposes the restriction that the printer cannot answer*)
definition "ChairNetwork_stateful_v3 = generate_valid_stateful_policy_IFSACS ChairNetwork [PrintingSink]"
ML_val\<open>
visualize_edges @{context} @{term "flows_fixL ChairNetwork_stateful_v3"}
    [("edge [dir=\"arrow\", style=dashed, color=\"#FF8822\", constraint=false]", @{term "flows_stateL ChairNetwork_stateful_v3"})] ""; 
\<close>

subsection\<open>An example of bad side-effects in access control policies\<close>

  definition ACL_not_with::"(string SecurityInvariant)" where
    "ACL_not_with \<equiv> new_configured_list_SecurityInvariant SINVAR_ACLnotCommunicateWith_impl.SINVAR_LIB_ACLnotCommunicateWith \<lparr> 
        node_properties = [''A'' \<mapsto> {''C''},
                           ''B'' \<mapsto> {},
                           ''C'' \<mapsto> {}]
        \<rparr> ''example: a must not reach C''"

  definition simple_network :: "string list_graph" where
    "simple_network \<equiv> \<lparr> nodesL = [''A'', ''B'', ''C''],
                      edgesL = [(''B'', ''A''), (''B'', ''C'')] \<rparr>"
  
  lemma "wf_list_graph ChairNetwork_empty" by eval
  lemma "\<forall>m \<in> set [ACL_not_with]. implc_sinvar m simple_network" by eval


  lemma "implc_get_offending_flows [ACL_not_with] simple_network = []" by eval
  lemma "implc_get_offending_flows [ACL_not_with] 
    \<lparr> nodesL = [''A'', ''B'', ''C''], edgesL = [(''B'', ''A''), (''B'', ''C''), (''A'', ''B'')] \<rparr> =
      [[(''B'', ''C'')], [(''A'', ''B'')]]" by eval
  lemma "implc_get_offending_flows [ACL_not_with] 
    \<lparr> nodesL = [''A'', ''B'', ''C''], edgesL = [(''B'', ''A''), (''B'', ''C''), (''C'', ''B'')] \<rparr> =
      []" by eval

value "generate_valid_stateful_policy_IFSACS simple_network [ACL_not_with]"
value "generate_valid_stateful_policy_IFSACS_2 simple_network [ACL_not_with]"








subsection\<open>performance test\<close>
(*6 minutes , about 1.8k edges in graph, most of the times, no requirements apply,
  simply added some nodes, edges to the chair network. topology is valid*)
(*value "generate_valid_stateful_policy_IFSACS biggraph ChairSecurityRequirements"*)

end
