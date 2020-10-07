theory SINVAR_Examples
imports
  TopoS_Interface
  TopoS_Interface_impl
  TopoS_Library
  TopoS_Composition_Theory
  TopoS_Stateful_Policy
  TopoS_Composition_Theory_impl
  TopoS_Stateful_Policy_Algorithm
  TopoS_Stateful_Policy_impl
  TopoS_Impl
begin


(*Instead of opening a lot of pdfs now, ask whether to open them first.
  If not clicked yes/no, it will wait 3 seconds until it continues.
  Don't change other settings!
  DoNothing must remain DoNothing for batch build.
  Changing this reference will change the behavior of all other theories! Careful with this one ;-)*)
ML\<open>
case !Graphviz.open_viewer of
    OpenImmediately => Graphviz.open_viewer := AskTimeouted 3.0
  | AskTimeouted _ => ()
  | DoNothing => ()
\<close>

definition make_policy :: "('a SecurityInvariant) list \<Rightarrow> 'a list \<Rightarrow> 'a list_graph" where
  "make_policy sinvars V \<equiv> generate_valid_topology sinvars \<lparr>nodesL = V, edgesL = List.product V V \<rparr>"



context begin
  private definition "SINK_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_Sink \<lparr> 
          node_properties = [''Bot1'' \<mapsto> Sink,
                             ''Bot2'' \<mapsto> Sink,
                             ''MissionControl1'' \<mapsto> SinkPool,
                             ''MissionControl2'' \<mapsto> SinkPool
                             ]
          \<rparr> ''bots and control are infromation sink''"
  value[code] "make_policy [SINK_m] [''INET'', ''Supervisor'', ''Bot1'', ''Bot2'', ''MissionControl1'', ''MissionControl2'']"
  ML_val\<open>
  visualize_graph_header @{context} @{term "[SINK_m]"}
    @{term "make_policy [SINK_m] [''INET'', ''Supervisor'', ''Bot1'', ''Bot2'', ''MissionControl1'', ''MissionControl2'']"}
    @{term "[''Bot1'' \<mapsto> Sink,
             ''Bot2'' \<mapsto> Sink,
             ''MissionControl1'' \<mapsto> SinkPool,
             ''MissionControl2'' \<mapsto> SinkPool
             ]"};
\<close>
end






context begin
  private definition "ACL_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_CommunicationPartners \<lparr> 
          node_properties = [''db1'' \<mapsto> Master [''h1'', ''h2''],
                             ''db2'' \<mapsto> Master [''db1''],
                             ''h1'' \<mapsto> Care,
                             ''h2'' \<mapsto> Care
                             ]
          \<rparr> ''ACL for databases''" 
  value[code] "make_policy [ACL_m] [''db1'', ''db2'', ''h1'', ''h2'', ''h3'']"
  ML_val\<open>
  visualize_graph_header @{context} @{term "[ACL_m]"}
    @{term "make_policy [ACL_m] [''db1'', ''db2'', ''h1'', ''h2'', ''h3'']"}
    @{term "[''db1'' \<mapsto> Master [''h1'', ''h2''],
             ''db2'' \<mapsto> Master [''db1''],
             ''h1'' \<mapsto> Care,
             ''h2'' \<mapsto> Care
             ]"};
\<close>
end




definition CommWith_m::"(nat SecurityInvariant)" where
    "CommWith_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_ACLcommunicateWith \<lparr> 
          node_properties = [
                  1 \<mapsto> [2,3],
                  2 \<mapsto> [3]]
          \<rparr> ''One can only talk to 2,3''"


text\<open>Experimental: the config (only one) can be added to the end.\<close>
ML_val\<open>
visualize_graph_header @{context} @{term "[CommWith_m]"}
       @{term "\<lparr> nodesL = [1::nat, 2, 3],
                edgesL = [(1,2), (2,3)]\<rparr>"} @{term "[
                  (1::nat) \<mapsto> [2::nat,3],
                  2 \<mapsto> [3]]"};
\<close>


value[code] "make_policy [CommWith_m] [1,2,3]"
value[code] "implc_offending_flows CommWith_m \<lparr>nodesL = [1,2,3,4], edgesL = List.product [1,2,3,4] [1,2,3,4] \<rparr>"
value[code] "make_policy [CommWith_m] [1,2,3,4]"


ML_val\<open>
visualize_graph @{context} @{term "[ new_configured_list_SecurityInvariant SINVAR_LIB_ACLcommunicateWith \<lparr> 
          node_properties = [
                  1::nat \<mapsto> [1,2,3],
                  2 \<mapsto> [1,2,3,4],
                  3 \<mapsto> [1,2,3,4],
                  4 \<mapsto> [1,2,3,4]]
          \<rparr> ''usefull description here'']"} @{term "\<lparr>nodesL = [1::nat,2,3,4], edgesL = [(1,2), (1,3), (2,3), (3, 4)] \<rparr>"};
\<close>


lemma "implc_offending_flows (new_configured_list_SecurityInvariant SINVAR_LIB_ACLcommunicateWith \<lparr> 
          node_properties = [
                  1::nat \<mapsto> [1,2,3],
                  2 \<mapsto> [1,2,3,4],
                  3 \<mapsto> [1,2,3,4],
                  4 \<mapsto> [1,2,3,4]]
          \<rparr> ''usefull description here'') \<lparr>nodesL = [1::nat,2,3,4], edgesL = [(1,2), (1,3), (2,3), (3, 4)] \<rparr> =
        [[(1, 2), (1, 3)], [(1, 3), (2, 3)], [(3, 4)]]" by eval



context begin
  private definition G_dep :: "nat list_graph" where
    "G_dep \<equiv> \<lparr>nodesL = [1::nat,2,3,4,5,6,7], edgesL = [(1,2), (2,1), (2,3),
                                                       (4,5), (5,6), (6,7)] \<rparr>"
  private lemma "wf_list_graph G_dep" by eval

  private definition "DEP_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_Dependability \<lparr> 
          node_properties = Some \<circ> dependability_fix_nP G_dep (\<lambda>_. 0)
          \<rparr> ''automatically computed dependability invariant''"
  ML_val\<open>
  visualize_graph_header @{context} @{term "[DEP_m]"}
    @{term "G_dep"}
    @{term "Some \<circ> dependability_fix_nP G_dep (\<lambda>_. 0)"};
\<close>

  text\<open>Connecting @{term "(3,4)"}. This causes only one offedning flow at @{term "(3,4)"}.\<close>
  ML_val\<open>
  visualize_graph_header @{context} @{term "[DEP_m]"}
    @{term "G_dep\<lparr>edgesL := (3,4)#edgesL G_dep\<rparr>"}
    @{term "Some \<circ> dependability_fix_nP G_dep (\<lambda>_. 0)"};
\<close>
  text\<open>We try to increase the dependability level at @{term 3}. Suddenly, offending flows everywhere.\<close>
  ML_val\<open>
  visualize_graph_header @{context} @{term "[new_configured_list_SecurityInvariant SINVAR_LIB_Dependability \<lparr> 
          node_properties = Some \<circ> ((dependability_fix_nP G_dep (\<lambda>_. 0))(3 := 2))
          \<rparr> ''changed deps'']"}
    @{term "G_dep\<lparr>edgesL := (3,4)#edgesL G_dep\<rparr>"}
    @{term "Some \<circ> ((dependability_fix_nP G_dep (\<lambda>_. 0))(3 := 2))"};
\<close>
  lemma "implc_offending_flows (new_configured_list_SecurityInvariant SINVAR_LIB_Dependability \<lparr> 
                          node_properties = Some \<circ> ((dependability_fix_nP G_dep (\<lambda>_. 0))(3 := 2))
                          \<rparr> ''changed deps'')
             (G_dep\<lparr>edgesL := (3,4)#edgesL G_dep\<rparr>) = 
           [[(3, 4)], [(1, 2), (2, 1), (5, 6)], [(1, 2), (4, 5)], [(2, 1), (4, 5)], [(2, 3), (4, 5)], [(2, 3), (5, 6)]]"
           by eval

  text\<open>If we recompute the dependability levels for the changed graph, we see that suddenly, 
        The level at @{term 1} and @{term 2} increased, though we only added the edge @{term "(3,4)"}.
        This hints that we connected the graph. If an attacker can now compromise @{term 1}, she 
        may be able to peek much deeper into the network.\<close>
  ML_val\<open>
  visualize_graph_header @{context} @{term "[new_configured_list_SecurityInvariant SINVAR_LIB_Dependability \<lparr> 
          node_properties = Some \<circ> dependability_fix_nP (G_dep\<lparr>edgesL := (3,4)#edgesL G_dep\<rparr>) (\<lambda>_. 0)
          \<rparr> ''changed deps'']"}
    @{term "G_dep\<lparr>edgesL := (3,4)#edgesL G_dep\<rparr>"}
    @{term "Some \<circ> dependability_fix_nP (G_dep\<lparr>edgesL := (3,4)#edgesL G_dep\<rparr>) (\<lambda>_. 0)"};
\<close>

  text\<open>Dependability is reflexive, a host can depend on itself.\<close>
  ML_val\<open>
  visualize_graph_header @{context} @{term "[new_configured_list_SecurityInvariant SINVAR_LIB_Dependability \<lparr> 
          node_properties = Some \<circ> dependability_fix_nP \<lparr>nodesL = [1::nat], edgesL = [(1,1)] \<rparr> (\<lambda>_. 0)
          \<rparr> ''changed deps'']"}
    @{term "\<lparr>nodesL = [1::nat], edgesL = [(1,1)] \<rparr>"}
    @{term "Some \<circ> dependability_fix_nP \<lparr>nodesL = [1::nat], edgesL = [(1,1)] \<rparr> (\<lambda>_. 0)"};
\<close>
  ML_val\<open>
  visualize_graph_header @{context} @{term "[new_configured_list_SecurityInvariant SINVAR_LIB_Dependability_norefl \<lparr> 
          node_properties = (\<lambda>_::nat. Some 0)
          \<rparr> ''changed deps'']"}
    @{term "\<lparr>nodesL = [1::nat], edgesL = [(1,1)] \<rparr>"}
    @{term "(\<lambda>_::nat. Some (0::nat))"};
\<close>

end



context begin
  private definition G_noninter :: "nat list_graph" where
    "G_noninter \<equiv> \<lparr>nodesL = [1::nat,2,3,4], edgesL = [(1,2), (1,3), (2,3), (3, 4)] \<rparr>"
  private lemma "wf_list_graph G_noninter" by eval

  private definition "NonI_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_NonInterference \<lparr> 
          node_properties = [
                  1::nat \<mapsto> Interfering,
                  2 \<mapsto> Unrelated, 
                  3 \<mapsto> Unrelated, 
                  4 \<mapsto> Interfering]
          \<rparr> ''One and Four interfere''"
  ML_val\<open>
  visualize_graph @{context} @{term "[ NonI_m ]"} @{term "G_noninter"};
\<close>

  (*The same as the CommWith example*)
  lemma "implc_offending_flows NonI_m G_noninter = [[(1, 2), (1, 3)], [(1, 3), (2, 3)], [(3, 4)]]"
           by eval


  ML_val\<open>
  visualize_graph @{context} @{term "[ NonI_m ]"} @{term "\<lparr>nodesL = [1::nat,2,3,4], edgesL = [(1,2), (1,3), (2,3), (4, 3)] \<rparr>"};
\<close>

  lemma "implc_offending_flows NonI_m \<lparr>nodesL = [1::nat,2,3,4], edgesL = [(1,2), (1,3), (2,3), (4, 3)] \<rparr> =
    [[(1, 2), (1, 3)], [(1, 3), (2, 3)], [(4, 3)]]"
           by eval

  text\<open>In comparison, @{const SINVAR_LIB_ACLcommunicateWith} is less strict. 
        Changing the direction of the edge @{term "(3,4)"} removes the access from @{term 1} to @{term 4}
        and the invariant holds.\<close>
  lemma "implc_offending_flows (new_configured_list_SecurityInvariant SINVAR_LIB_ACLcommunicateWith \<lparr> 
          node_properties = [
                  1::nat \<mapsto> [1,2,3],
                  2 \<mapsto> [1,2,3,4],
                  3 \<mapsto> [1,2,3,4],
                  4 \<mapsto> [1,2,3,4]]
          \<rparr> ''One must not access Four'') \<lparr>nodesL = [1::nat,2,3,4], edgesL = [(1,2), (1,3), (2,3), (4, 3)] \<rparr> = []" by eval
end



context begin
  private definition "subnets_host_attributes \<equiv> [
                             ''v11'' \<mapsto> Subnet 1,
                             ''v12'' \<mapsto> Subnet 1,
                             ''v13'' \<mapsto> Subnet 1,
                             ''v1b'' \<mapsto> BorderRouter 1,
                             ''v21'' \<mapsto> Subnet 2,
                             ''v22'' \<mapsto> Subnet 2,
                             ''v23'' \<mapsto> Subnet 2,
                             ''v2b'' \<mapsto> BorderRouter 2,
                             ''v3b'' \<mapsto> BorderRouter 3
                             ]"
  private definition "Subnets_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_Subnets \<lparr> 
          node_properties = subnets_host_attributes
          \<rparr> ''Collaborating hosts''"
  private definition "subnet_hosts \<equiv> [''v11'', ''v12'', ''v13'', ''v1b'',
                                      ''v21'', ''v22'', ''v23'', ''v2b'',
                                      ''v3b'', ''vo'']"

  private lemma "dom (subnets_host_attributes) \<subseteq> set (subnet_hosts)"
    by(simp add: subnet_hosts_def subnets_host_attributes_def)
  value[code] "make_policy [Subnets_m] subnet_hosts"
  ML_val\<open>
  visualize_graph_header @{context} @{term "[Subnets_m]"}
    @{term "make_policy [Subnets_m] subnet_hosts"}
    @{term "subnets_host_attributes"};
\<close>


  text\<open>Emulating the same but with accessible members with SubnetsInGW and ACLs\<close>
  private definition "SubnetsInGW_ACL_ms \<equiv> [new_configured_list_SecurityInvariant SINVAR_LIB_SubnetsInGW \<lparr> 
          node_properties = [''v11'' \<mapsto> Member, ''v12'' \<mapsto> Member, ''v13'' \<mapsto> Member, ''v1b'' \<mapsto> InboundGateway]
          \<rparr> ''v1 subnet'',
          new_configured_list_SecurityInvariant SINVAR_LIB_CommunicationPartners \<lparr> 
          node_properties = [''v1b'' \<mapsto> Master [''v11'', ''v12'', ''v13'', ''v2b'', ''v3b''],
                             ''v11'' \<mapsto> Care,
                             ''v12'' \<mapsto> Care,
                             ''v13'' \<mapsto> Care,
                             ''v2b'' \<mapsto> Care,
                             ''v3b'' \<mapsto> Care
                             ]
          \<rparr> ''v1b ACL'',
          new_configured_list_SecurityInvariant SINVAR_LIB_SubnetsInGW \<lparr> 
          node_properties = [''v21'' \<mapsto> Member, ''v22'' \<mapsto> Member, ''v23'' \<mapsto> Member, ''v2b'' \<mapsto> InboundGateway]
          \<rparr> ''v2 subnet'',
          new_configured_list_SecurityInvariant SINVAR_LIB_CommunicationPartners \<lparr> 
          node_properties = [''v2b'' \<mapsto> Master [''v21'', ''v22'', ''v23'', ''v1b'', ''v3b''],
                             ''v21'' \<mapsto> Care,
                             ''v22'' \<mapsto> Care,
                             ''v23'' \<mapsto> Care,
                             ''v1b'' \<mapsto> Care,
                             ''v3b'' \<mapsto> Care
                             ]
          \<rparr> ''v2b ACL'',
          \<^cancel>\<open>new_configured_list_SecurityInvariant SINVAR_LIB_SubnetsInGW \<lparr> 
          node_properties = [''v3b'' \<mapsto> InboundGateway]
          \<rparr> ''v3b'',\<close>
          new_configured_list_SecurityInvariant SINVAR_LIB_CommunicationPartners \<lparr> 
          node_properties = [''v3b'' \<mapsto> Master [''v1b'', ''v2b''],
                             ''v1b'' \<mapsto> Care,
                             ''v2b'' \<mapsto> Care
                             ]
          \<rparr> ''v3b ACL'']"
  value[code] "make_policy SubnetsInGW_ACL_ms subnet_hosts"
  lemma "set (edgesL (make_policy [Subnets_m] subnet_hosts)) \<subseteq> set (edgesL (make_policy SubnetsInGW_ACL_ms subnet_hosts))" by eval
  lemma "[e <- edgesL (make_policy SubnetsInGW_ACL_ms subnet_hosts). e \<notin> set (edgesL (make_policy [Subnets_m] subnet_hosts))] =
   [(''v1b'', ''v11''), (''v1b'', ''v12''), (''v1b'', ''v13''), (''v2b'', ''v21''), (''v2b'', ''v22''), (''v2b'', ''v23'')]" by eval
  ML_val\<open>
  visualize_graph @{context} @{term "SubnetsInGW_ACL_ms"}
    @{term "make_policy SubnetsInGW_ACL_ms subnet_hosts"};
\<close>
end




context begin
  private definition "secgwext_host_attributes \<equiv> [
                             ''hypervisor'' \<mapsto> PolEnforcePoint,
                             ''securevm1'' \<mapsto> DomainMember,
                             ''securevm2'' \<mapsto> DomainMember,
                             ''publicvm1'' \<mapsto> AccessibleMember,
                             ''publicvm2'' \<mapsto> AccessibleMember
                             ]"
  private definition "SecGwExt_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_PolEnforcePointExtended \<lparr> 
          node_properties = secgwext_host_attributes
          \<rparr> ''secure hypervisor mediates accesses between secure VMs''"
  private definition "secgwext_hosts \<equiv> [''hypervisor'', ''securevm1'', ''securevm2'',
                                      ''publicvm1'', ''publicvm2'',
                                      ''INET'']"

  private lemma "dom (secgwext_host_attributes) \<subseteq> set (secgwext_hosts)"
    by(simp add: secgwext_hosts_def secgwext_host_attributes_def)
  value[code] "make_policy [SecGwExt_m] secgwext_hosts"
  ML_val\<open>
  visualize_graph_header @{context} @{term "[SecGwExt_m]"}
    @{term "make_policy [SecGwExt_m] secgwext_hosts"}
    @{term "secgwext_host_attributes"};
\<close>

  ML_val\<open>
  visualize_graph_header @{context} @{term "[SecGwExt_m, new_configured_list_SecurityInvariant SINVAR_LIB_BLPtrusted \<lparr> 
        node_properties = [''hypervisor'' \<mapsto> \<lparr> security_level = 0, trusted = True \<rparr>,
                           ''securevm1'' \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
                           ''securevm2'' \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>
                           ] \<rparr> ''secure vms are confidential'']"}
    @{term "make_policy [SecGwExt_m, new_configured_list_SecurityInvariant SINVAR_LIB_BLPtrusted \<lparr> 
        node_properties = [''hypervisor'' \<mapsto> \<lparr> security_level = 0, trusted = True \<rparr>,
                           ''securevm1'' \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
                           ''securevm2'' \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>
                           ] \<rparr> ''secure vms are confidential''] secgwext_hosts"}
    @{term "secgwext_host_attributes"};
\<close>
end


end
