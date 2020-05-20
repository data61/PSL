theory Impl_List_Playground_ChairNetwork
imports "../TopoS_Impl"
begin


text\<open>An example of our chair network [simplified]\<close>

text\<open>Our access control view on the network\<close>
  definition ChairNetwork_empty :: "string list_graph" where
    "ChairNetwork_empty \<equiv> \<lparr> nodesL = [''WebSrv'', ''FilesSrv'', ''PrinterBW'',
                                ''PrinterColor'', ''Students'',
                                ''Employees'', ''EReachable'',
                                ''Internet''],
                      edgesL = [] \<rparr>"
  
  lemma "wf_list_graph ChairNetwork_empty" by eval


subsection\<open>Our security requirements\<close>
  subsubsection\<open>We have a server with confidential data\<close>
    definition ConfidentialChairData::"(string SecurityInvariant)" where
      "ConfidentialChairData \<equiv> new_configured_list_SecurityInvariant SINVAR_BLPtrusted_impl.SINVAR_LIB_BLPtrusted \<lparr> 
          node_properties = [''FilesSrv'' \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
                             ''Employees'' \<mapsto> \<lparr> security_level = 0, trusted = True \<rparr>,
                             ''EReachable'' \<mapsto> \<lparr> security_level = 0, trusted = True \<rparr>]
          \<rparr> ''confidential data''"


  (*
  subsubsection{*We have a hierarchical printing policy*}
    definition "PrintingHierarchy_nodes=[''Employees''\<mapsto> DN (''ColorPrinting''--Leaf, 0),
                           ''PrinterColor''\<mapsto> DN (''ColorPrinting''--''Printer''--Leaf, 0),
                           ''Students''\<mapsto> DN (''ColorPrinting''--''BwPrinting''--Leaf, 0),
                           ''PrinterBW''\<mapsto> DN (''ColorPrinting''--''BwPrinting''--''Printer''--Leaf, 0)]"
    definition "PrintingHierarchy_tree=Department ''ColorPrinting'' [
              Department ''Printer'' [], 
              Department ''BwPrinting'' [
                  Department ''Printer'' []]]"
    definition PrintingHierarchy::"string SecurityInvariant" where
      "PrintingHierarchy \<equiv> new_configured_list_SecurityInvariant SINVAR_DomainHierarchyNG_impl.SINVAR_LIB_DomainHierarchyNG \<lparr> 
        node_properties = PrintingHierarchy_nodes
        \<rparr>"  *)
  subsubsection\<open>The color printer is only accessibly by employees, The black.white printer by employees and students\<close>
    definition "PrintingACL \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_CommunicationPartners \<lparr> 
          node_properties = [''PrinterColor'' \<mapsto> Master [''Employees'', ''EReachable''],
                             ''PrinterBW'' \<mapsto> Master [''Employees'', ''EReachable'', ''Students''],
                             ''Employees'' \<mapsto> Care,
                             ''EReachable'' \<mapsto> Care,
                             ''Students'' \<mapsto> Care]
          \<rparr> ''printing ACL''"

  subsubsection\<open>Printers are information sinks\<close>
    definition "PrintingSink \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_Sink \<lparr> 
          node_properties = [''PrinterColor'' \<mapsto> Sink,
                             ''PrinterBW'' \<mapsto> Sink]
          \<rparr> ''printing sink''"



  subsubsection\<open>Students may access each other but are not accessible from the outside\<close>
    definition "StudentSubnet \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_SubnetsInGW \<lparr> 
          node_properties = [''Students'' \<mapsto> Member, ''Employees'' \<mapsto> Member, ''EReachable'' \<mapsto> InboundGateway]
          \<rparr> ''student subnet''"


  subsubsection\<open>The files server is only accessibly by employees\<close>
    definition "FilesSrvACL \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_CommunicationPartners \<lparr> 
          node_properties = [''FilesSrv'' \<mapsto> Master [''Employees'', ''EReachable''],
                             ''Employees'' \<mapsto> Care,
                             ''EReachable'' \<mapsto> Care]
          \<rparr> ''file srv acl''"


  subsubsection\<open>emplyees are reachable from the Internet\<close>
    (*nothing to do here*)

lemma "implc_sinvar ConfidentialChairData ChairNetwork_empty" by eval
lemma "implc_sinvar PrintingACL ChairNetwork_empty" by eval
lemma "implc_sinvar PrintingSink ChairNetwork_empty" by eval
lemma "implc_sinvar StudentSubnet ChairNetwork_empty" by eval
lemma "implc_sinvar FilesSrvACL ChairNetwork_empty" by eval

definition "ChairSecurityRequirements = [ConfidentialChairData, PrintingACL, PrintingSink, StudentSubnet, FilesSrvACL]"

value "implc_get_offending_flows ChairSecurityRequirements ChairNetwork_empty"
value "generate_valid_topology ChairSecurityRequirements ChairNetwork_empty"

value "List.product (nodesL ChairNetwork_empty) (nodesL ChairNetwork_empty)"

definition "ChairNetwork = generate_valid_topology ChairSecurityRequirements 
      \<lparr>nodesL = nodesL ChairNetwork_empty, edgesL = List.product (nodesL ChairNetwork_empty) (nodesL ChairNetwork_empty) \<rparr>"

lemma "all_security_requirements_fulfilled ChairSecurityRequirements ChairNetwork" by eval

value "ChairNetwork"

ML_val\<open>
visualize_graph @{context} @{term "ChairSecurityRequirements"} @{term "ChairNetwork"};
\<close>



end
