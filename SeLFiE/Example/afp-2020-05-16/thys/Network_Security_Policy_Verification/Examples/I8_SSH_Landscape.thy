theory I8_SSH_Landscape
imports "../TopoS_Impl"
begin


(*generated with ITval (spurious)*)
definition I8SSHgraph :: "nat list_graph" where
    "I8SSHgraph \<equiv> \<lparr> nodesL = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    edgesL = [(7, 3), (16, 9), (19, 4), (22, 19), (20, 7), (18, 19), (21, 6), (8, 5), (9, 0), (10, 7), (11, 22), (14, 1), 
      (12, 17), (15, 4), (13, 20), (3, 2), (4, 5), (16, 0), (6, 23), (19, 13), (7, 22), (20, 14), (18, 10), (23, 19), (21, 15), 
        (8, 12), (22, 12), (9, 9), (23, 9), (10, 14), (8, 18), (11, 15), (9, 19), (14, 8), (12, 8), (15, 13), (13, 13), (2, 18), (0, 14), 
        (3, 11), (4, 12), (2, 12), (5, 1), (3, 17), (16, 7), (6, 14), (19, 18), (17, 6), (7, 15), (18, 5), (21, 8), (22, 7), (23, 6), (10, 9), 
        (11, 4), (9, 20), (14, 19), (12, 7), (10, 19), (15, 10), (13, 6), (0, 5), (4, 11), (2, 7), (5, 10), (3, 22), (6, 1), (4, 17), (7, 4), (5, 20), 
        (16, 20), (21, 17), (19, 1), (8, 0), (15, 19), (11, 19), (12, 20), (16, 11), (6, 18), (19, 6), (22, 17), (23, 20), (21, 4), (8, 7), (22, 11), (9, 6), 
        (10, 5), (11, 8), (0, 19), (14, 7), (12, 19), (15, 6), (13, 18), (0, 9), (3, 4), (4, 7), (5, 6), (16, 2), (6, 21), (19, 15), (17, 3), (7, 16), (21, 13), 
        (8, 14), (22, 2), (9, 15), (23, 11), (10, 12), (8, 20), (11, 1), (9, 17), (14, 14), (12, 10), (10, 22), (15, 15), (13, 11), (2, 16), (3, 13), (4, 14), (2, 10), 
        (5, 15), (3, 19), (6, 12), (4, 20), (19, 20), (7, 9), (18, 3), (21, 22), (22, 5), (23, 0), (11, 6), (14, 17), (12, 1), (10, 17), (15, 20), (13, 4), (1, 6), (2, 5), 
        (5, 8), (6, 7), (4, 19), (7, 6), (5, 18), (16, 22), (19, 3), (8, 2), (9, 3), (11, 21), (14, 2), (12, 22), (13, 23), (3, 1), (16, 13), (6, 16), (19, 8), (7, 21), (22, 23), 
        (20, 3), (23, 22), (21, 2), (8, 9), (22, 9), (9, 4), (23, 12), (10, 3), (11, 10), (14, 5), (12, 13), (15, 0), (13, 16), (2, 23), (0, 11), (3, 6), (4, 1), (5, 4), (16, 4), 
        (6, 11), (19, 17), (7, 18), (18, 6), (21, 11), (22, 0), (9, 13), (23, 5), (10, 10), (8, 22), (11, 3), (9, 23), (14, 12), (12, 4), (10, 20), (15, 9), (13, 9), (3, 15), (1, 3), 
        (4, 8), (2, 8), (5, 13), (3, 21), (6, 2), (4, 22), (19, 22), (7, 11), (5, 23), (16, 17), (21, 20), (23, 2), (14, 23), (12, 3), (15, 22), (13, 2), (2, 3), (6, 5), (7, 0), (5, 16), 
        (16, 8), (19, 5), (22, 18), (20, 6), (21, 7), (8, 4), (9, 1), (10, 6), (11, 23), (14, 0), (12, 16), (15, 5), (13, 21), (3, 3), (4, 4), (16, 15), (6, 22), (19, 10), (17, 14), (7, 23), 
        (22, 21), (23, 16), (21, 0), (8, 11), (22, 15), (9, 10), (23, 14), (10, 1), (8, 17), (11, 12), (14, 11), (12, 15), (15, 2), (13, 14), (2, 21), (3, 8), (4, 3), (2, 15), (5, 2), 
        (16, 6), (6, 9), (19, 19), (17, 7), (7, 12), (21, 9), (22, 6), (23, 7), (10, 8), (11, 5), (9, 21), (14, 18), (12, 6), (10, 18), (15, 11), (13, 7), (4, 10), (2, 6), (5, 11), 
        (3, 23), (6, 0), (4, 16), (7, 5), (5, 21), (20, 19), (16, 19), (21, 18), (14, 21), (15, 16), (13, 0), (11, 16), (2, 1), (7, 2), (16, 10), (19, 7), (17, 11), (22, 16), 
        (23, 21), (21, 5), (8, 6), (22, 10), (9, 7), (10, 4), (11, 9), (14, 6), (12, 18), (1, 19), (15, 7), (13, 19), (3, 5), (4, 6), (5, 7), (16, 1), (6, 20), (19, 12), (7, 17), 
        (18, 11), (23, 18), (21, 14), (8, 13), (22, 13), (9, 8), (23, 8), (10, 15), (8, 19), (11, 14), (9, 18), (14, 9), (12, 9), (15, 12), (13, 12), (2, 19), (3, 10), (1, 14), (4, 13), 
        (2, 13), (5, 0), (3, 16), (6, 15), (19, 21), (17, 5), (7, 14), (21, 23), (22, 4), (23, 1), (11, 7), (14, 16), (12, 0), (10, 16), (15, 21), (13, 5), (0, 6), (1, 7), (2, 4), 
        (5, 9), (6, 6), (4, 18), (7, 7), (5, 19), (16, 21), (21, 16), (19, 0), (8, 1), (15, 18), (11, 18), (12, 21), (16, 12), (6, 19), (19, 9), (17, 9), (22, 22), (18, 14), 
        (23, 23), (21, 3), (8, 8), (22, 8), (9, 5), (23, 13), (10, 2), (11, 11), (14, 4), (12, 12), (15, 1), (13, 17), (2, 22), (3, 7), (1, 11), (4, 0), (5, 5), (16, 3), 
        (6, 10), (19, 14), (7, 19), (20, 9), (18, 9), (21, 12), (8, 15), (22, 3), (9, 14), (23, 10), (10, 13), (8, 21), (11, 0), (9, 16), (14, 15), (12, 11), (10, 23), 
        (15, 14), (13, 10), (2, 17), (3, 12), (4, 15), (2, 11), (5, 14), (3, 18), (6, 13), (4, 21), (19, 23), (7, 8), (16, 16), (21, 21), (23, 3), (14, 22), (12, 2), 
        (15, 23), (13, 3), (1, 5), (2, 2), (6, 4), (7, 1), (5, 17), (16, 23), (19, 2), (20, 5), (8, 3), (9, 2), (11, 20), (14, 3), (12, 23), (13, 22), (3, 0), (16, 14), 
        (6, 17), (19, 11), (7, 20), (22, 20), (23, 17), (21, 1), (8, 10), (22, 14), (9, 11), (23, 15), (10, 0), (8, 16), (11, 13), (14, 10), (12, 14), (15, 3), (13, 15), 
        (2, 20), (3, 9), (1, 9), (4, 2), (2, 14), (5, 3), (16, 5), (6, 8), (19, 16), (7, 13), (20, 11), (18, 7), (21, 10), (22, 1), (9, 12), (23, 4), (10, 11), (8, 23), 
        (11, 2), (9, 22), (14, 13), (12, 5), (10, 21), (15, 8), (13, 8), (0, 3), (3, 14), (4, 9), (2, 9), (5, 12), (3, 20), (6, 3), (4, 23), (7, 10), (5, 22), (16, 18), 
        (21, 19), (17, 19), (14, 20), (15, 17), (13, 1), (11, 17), (2, 0)] \<rparr>" 


value "(0, 20) \<in> set (edgesL I8SSHgraph)"
value "[(s,r) \<leftarrow> (edgesL I8SSHgraph). r = 2]"

  lemma "wf_list_graph I8SSHgraph" by eval

definition Confidentiality1::"(nat SecurityInvariant)" where
      "Confidentiality1 \<equiv> new_configured_list_SecurityInvariant SINVAR_BLPtrusted_impl.SINVAR_LIB_BLPtrusted \<lparr> 
          node_properties = [0 \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
         1 \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
         2 \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
         3 \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
         4 \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
         5 \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
         6 \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
         7 \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
         8 \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
         9 \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
         10 \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
         11 \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
         12 \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
         13 \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
         14 \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
         15 \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
         16 \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
         17 \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
         18 \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
         19 \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
         20 \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
         21 \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
         22 \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
         23 \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>]
          \<rparr> ''some confidentiality lables''"

definition "Subnet1 \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_SubnetsInGW \<lparr> 
          node_properties = [0 \<mapsto> Unassigned,
         1 \<mapsto> Unassigned,
         2 \<mapsto> Member,
         3 \<mapsto> InboundGateway,
         4 \<mapsto> Member,
         5 \<mapsto> InboundGateway,
         6 \<mapsto> InboundGateway,
         7 \<mapsto> InboundGateway,
         8 \<mapsto> InboundGateway,
         9 \<mapsto> InboundGateway,
         10 \<mapsto> Member,
         11 \<mapsto> InboundGateway,
         12 \<mapsto> InboundGateway,
         13 \<mapsto> InboundGateway,
         14 \<mapsto> InboundGateway,
         15 \<mapsto> InboundGateway,
         16 \<mapsto> InboundGateway,
         17 \<mapsto> Unassigned,
         18 \<mapsto> Member,
         19 \<mapsto> InboundGateway,
         20 \<mapsto> Unassigned,
         21 \<mapsto> InboundGateway,
         22 \<mapsto> InboundGateway,
         23 \<mapsto> Member]
          \<rparr> ''some subnet things''"


    definition "PrintingSink \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_Sink \<lparr> 
          node_properties = [3 \<mapsto> Sink]
          \<rparr> ''information must not leave printer''"

definition "I8Requirements = [ Confidentiality1, Subnet1 ]"

value "implc_get_offending_flows I8Requirements I8SSHgraph"

value "implc_offending_flows PrintingSink I8SSHgraph"

ML\<open>
visualize_graph @{context} @{term "I8Requirements"} @{term "I8SSHgraph"};
\<close>

lemma "all_security_requirements_fulfilled I8Requirements I8SSHgraph" by eval

lemma "set (filter_IFS_no_violations I8SSHgraph I8Requirements) = set (edgesL I8SSHgraph)" by eval


value "filter_compliant_stateful_ACS I8SSHgraph I8Requirements"

text\<open>noBiFlows is the list of flows where not already a bidirectional flows is allowed.
      That is, the list of flows we might wish to be stateful to enhance connectivity.\<close>
definition "noBiFlows = [e \<leftarrow> edgesL I8SSHgraph. case e of (s,r) \<Rightarrow> \<not> ((s,r) \<in> set (edgesL I8SSHgraph) \<and> (r,s) \<in> set (edgesL I8SSHgraph)) ]"
lemma "set noBiFlows = set (filter_compliant_stateful_ACS I8SSHgraph I8Requirements)" by eval

value "generate_valid_stateful_policy_IFSACS I8SSHgraph I8Requirements"

text\<open>even the order of the list is preserved!!\<close>
lemma "flows_stateL (generate_valid_stateful_policy_IFSACS I8SSHgraph I8Requirements) = noBiFlows" by eval


lemma "set (flows_stateL (generate_valid_stateful_policy_IFSACS I8SSHgraph I8Requirements)) = set noBiFlows" by eval




end
