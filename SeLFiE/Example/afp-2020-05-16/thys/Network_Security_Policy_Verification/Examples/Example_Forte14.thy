theory Example_Forte14
imports "../TopoS_Impl"
begin



definition policy :: "string list_graph" where
    "policy \<equiv> \<lparr> nodesL = [''CC'', ''C1'', ''C2'', ''IFEsrv'', ''IFE1'', ''IFE2'', ''SAT'', ''Wifi'', ''P1'', ''P2'' ],
                edgesL = [(''CC'', ''C1''), (''CC'', ''C2''), (''CC'', ''IFEsrv''), (''C1'', ''CC''), 
                          (''C1'', ''C2''), (''C2'', ''CC''), (''C2'', ''C1''), 
                          (''IFEsrv'', ''IFE1''), (''IFEsrv'', ''IFE2''), (''IFEsrv'', ''SAT''), (''IFEsrv'', ''Wifi''),
                          (''IFE1'', ''IFEsrv''), (''IFE2'', ''IFEsrv''), 
                          (''Wifi'', ''IFEsrv''), (''Wifi'', ''SAT''), (''Wifi'', ''P1''),
                          (''Wifi'', ''P2''), (''P1'', ''Wifi''), (''P1'', ''P2''), (''P2'', ''Wifi''), (''P2'', ''P1'')
                          ] \<rparr>"

lemma "wf_list_graph policy" by eval

(*21 rules*)
lemma "length (edgesL policy) = 21" by eval


definition DomainHierarchy_m::"(string SecurityInvariant)" where
      "DomainHierarchy_m \<equiv> new_configured_list_SecurityInvariant SINVAR_DomainHierarchyNG_impl.SINVAR_LIB_DomainHierarchyNG \<lparr> 
          node_properties = [
            ''CC'' \<mapsto> DN (''aircraft''--''crew''--Leaf, 1),
            ''C1'' \<mapsto> DN (''aircraft''--''crew''--Leaf, 0),
            ''C2'' \<mapsto> DN (''aircraft''--''crew''--Leaf, 0),
            ''IFEsrv'' \<mapsto> DN (''aircraft''--''entertain''--Leaf, 0),
            ''IFE1'' \<mapsto> DN (''aircraft''--''entertain''--Leaf, 0),
            ''IFE2'' \<mapsto> DN (''aircraft''--''entertain''--Leaf, 0),
            ''SAT'' \<mapsto> DN (''aircraft''--''entertain''--''INET''--Leaf, 0),
            ''Wifi'' \<mapsto> DN (''aircraft''--''entertain''--''POD''--Leaf, 1),
            ''P1'' \<mapsto> DN (''aircraft''--''entertain''--''POD''--Leaf, 0),
            ''P2'' \<mapsto> DN (''aircraft''--''entertain''--''POD''--Leaf, 0)
          ]
          \<rparr> ''Device Hierarchy''"
  text\<open>sanity check that the host attributes correspond to the desired hierarchy\<close>
  lemma "DomainHierarchyNG_sanity_check_config
    (map snd [
            (''CC'', DN (''aircraft''--''crew''--Leaf, 1)),
            (''C1'', DN (''aircraft''--''crew''--Leaf, 0)),
            (''C2'', DN (''aircraft''--''crew''--Leaf, 0)),
            (''IFEsrv'', DN (''aircraft''--''entertain''--Leaf, 0)),
            (''IFE1'', DN (''aircraft''--''entertain''--Leaf, 0)),
            (''IFE2'', DN (''aircraft''--''entertain''--Leaf, 0)),
            (''SAT'', DN (''aircraft''--''entertain''--''INET''--Leaf, 0)),
            (''Wifi'', DN (''aircraft''--''entertain''--''POD''--Leaf, 1)),
            (''P1'', DN (''aircraft''--''entertain''--''POD''--Leaf, 0)),
            (''P2'', DN (''aircraft''--''entertain''--''POD''--Leaf, 0))
                            ])
            (
            Department ''aircraft'' [
              Department ''entertain'' [
                Department ''POD'' [], Department ''INET'' []
              ],
              Department ''crew'' []
            ])" by eval

definition PolEnforcePoint_m::"(string SecurityInvariant)" where
  "PolEnforcePoint_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_PolEnforcePointExtended \<lparr> 
          node_properties = [''IFEsrv'' \<mapsto> SINVAR_SecGwExt.PolEnforcePointIN,
                             ''IFE1'' \<mapsto> SINVAR_SecGwExt.DomainMember,
                             ''IFE2'' \<mapsto> SINVAR_SecGwExt.DomainMember]
          \<rparr> ''IFEsrc mediates access of its thin clients''"


(*
0 - unclassified
1 - confidential
2 - secret
3 - topsecret
*)
definition BLP_m::"(string SecurityInvariant)" where
    "BLP_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_BLPtrusted \<lparr> 
          node_properties = [''CC'' \<mapsto> \<lparr> security_level = 2, trusted = False \<rparr>,
                             ''C1'' \<mapsto> \<lparr> security_level = 2, trusted = False \<rparr>,
                             ''C2'' \<mapsto> \<lparr> security_level = 2, trusted = False \<rparr>,
                             ''IFE1'' \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
                             ''IFE2'' \<mapsto> \<lparr> security_level = 1, trusted = False \<rparr>,
                             ''IFEsrv'' \<mapsto> \<lparr> security_level = 0, trusted = True \<rparr>]
          \<rparr> ''Confidential data''"

definition "security_invariants = [ DomainHierarchy_m, PolEnforcePoint_m, BLP_m]"

lemma "all_security_requirements_fulfilled security_invariants policy" by eval

lemma "implc_get_offending_flows security_invariants policy = []" by eval


text\<open>
Visualization with a violation.
\<close>
ML\<open>
visualize_graph @{context} @{term "security_invariants"} @{term "policy\<lparr>edgesL := (''P1'', ''CC'')#edgesL policy\<rparr>"};
\<close>






definition "max_policy = generate_valid_topology security_invariants \<lparr>nodesL = nodesL policy, edgesL = List.product (nodesL policy) (nodesL policy) \<rparr>"


text\<open>calculating the maximum policy\<close>
value "max_policy"


text\<open>
The diff to the maximum policy. It adds reflexive flows and the IFEsrv may send to the PODs.
\<close>
ML_val\<open>
visualize_edges @{context} @{term "edgesL policy"} 
    [("edge [dir=\"arrow\", style=dashed, color=\"#FF8822\", constraint=false]", @{term "[e \<leftarrow> edgesL max_policy. e \<notin> set (edgesL policy)]"})] ""; 
\<close>


text\<open>
Visualizing the maximum policy.
\<close>
ML\<open>
visualize_graph @{context} @{term "security_invariants"} @{term "max_policy"};
\<close>

lemma "all_security_requirements_fulfilled security_invariants policy" by eval
lemma "all_security_requirements_fulfilled security_invariants max_policy" by eval


subsection\<open>A stateful implementation\<close>
definition "stateful_policy = generate_valid_stateful_policy_IFSACS policy security_invariants"
value "stateful_policy"

ML_val\<open>
visualize_edges @{context} @{term "flows_fixL stateful_policy"} 
    [("edge [dir=\"arrow\", style=dashed, color=\"#FF8822\", constraint=false]", @{term "flows_stateL stateful_policy"})] ""; 
\<close>


end
