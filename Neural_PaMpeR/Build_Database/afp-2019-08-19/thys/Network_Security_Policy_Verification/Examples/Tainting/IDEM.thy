section\<open>IDEM\<close>
theory IDEM
imports "../../TopoS_Impl"
begin

ML\<open>
case !Graphviz.open_viewer of
    OpenImmediately => Graphviz.open_viewer := AskTimeouted 3.0
  | AskTimeouted _ => ()
  | DoNothing => ()
\<close>

definition policy :: "string list_graph" where
  "policy \<equiv> \<lparr> nodesL = [''Logger'',
                        ''Sensor_Controller'',
                        ''P4S_in'',
                        ''P4S_filter_A'',
                        ''P4S_filter_B'',
                        ''P4S_filter_C'',
                        ''P4S_aggregator_C'',
                        ''P4S_encrypt_A'',
                        ''P4S_encrypt_B'',
                        ''P4S_encrypt_C'',
                        ''P4S_encrypt_C_low'',
                        ''P4S_out'',
                        ''P4S_DB'',

                        ''Adversary''],
              edgesL = [
              (''Logger'', ''Sensor_Controller''),
              (''Sensor_Controller'', ''P4S_in''),
              (''P4S_in'',       ''P4S_filter_A''),
              (''P4S_in'',       ''P4S_filter_B''),
              (''P4S_in'',       ''P4S_filter_C''),

              (''P4S_filter_A''    , ''P4S_encrypt_A''),
              (''P4S_filter_B''    , ''P4S_encrypt_B''),
              (''P4S_filter_C''    , ''P4S_encrypt_C''),
              (''P4S_filter_C''    , ''P4S_aggregator_C''),
              (''P4S_aggregator_C'', ''P4S_encrypt_C_low''),

              (''P4S_encrypt_A''      , ''P4S_out''),
              (''P4S_encrypt_B''      , ''P4S_out''),
              (''P4S_encrypt_C''      , ''P4S_out''),
              (''P4S_encrypt_C_low''  , ''P4S_out''),

              (''P4S_out'', ''P4S_DB'')
              ] \<rparr>"

lemma "wf_list_graph policy" by eval

context begin
  definition "tainiting_host_attributes \<equiv> [
                           ''Logger'' \<mapsto> TaintsUntaints {''A'',''B'',''C'',''D''} {},
                           ''Sensor_Controller'' \<mapsto> TaintsUntaints {''A'',''B'',''C'',''D''} {},
                           ''P4S_in'' \<mapsto> TaintsUntaints {''A'',''B'',''C'',''D''} {},
                           ''P4S_filter_A'' \<mapsto> TaintsUntaints {''A''} {''B'',''C'',''D''},
                           ''P4S_filter_B'' \<mapsto> TaintsUntaints {''B''} {''A'',''C'',''D''},
                           ''P4S_filter_C'' \<mapsto> TaintsUntaints {''C''} {''A'',''B'',''D''},
                           ''P4S_aggregator_C'' \<mapsto> TaintsUntaints {''C_low''} {''C''},
                           ''P4S_encrypt_A'' \<mapsto> TaintsUntaints {} {''A''},
                           ''P4S_encrypt_B'' \<mapsto> TaintsUntaints {} {''B''},
                           ''P4S_encrypt_C'' \<mapsto> TaintsUntaints {} {''C''},
                           ''P4S_encrypt_C_low'' \<mapsto> TaintsUntaints {}{''C_low''}
                           ]"
  private lemma "dom (tainiting_host_attributes) \<subseteq> set (nodesL policy)"
    by(simp add: tainiting_host_attributes_def policy_def)
  definition "Tainting_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_TaintingTrusted \<lparr>
        node_properties = tainiting_host_attributes \<rparr> ''critical energy data'' "
end

context begin
  private definition "system_EMS \<equiv>
                [(''Logger'',  SystemComponent),
                 (''Sensor_Controller'',  SystemBoundaryOutput)
                 ]"
  private lemma "dom(map_of system_EMS) \<subseteq> set (nodesL policy)"
    by(simp add: system_EMS_def policy_def)
  definition "system_EMS_m \<equiv> new_meta_system_boundary system_EMS ''EMS''"
end

context begin
  private definition "system_P4S \<equiv>
                [(''P4S_in'',  SystemBoundaryInput),
                 (''P4S_filter_A'',  SystemComponent),
                 (''P4S_filter_B'',  SystemComponent),
                 (''P4S_filter_C'',  SystemComponent),
                 (''P4S_aggregator_C'',  SystemComponent),
                 (''P4S_encrypt_A'',  SystemComponent),
                 (''P4S_encrypt_B'',  SystemComponent),
                 (''P4S_encrypt_C'',  SystemComponent),
                 (''P4S_encrypt_C_low'',  SystemComponent),
                 (''P4S_out'',  SystemBoundaryOutput)
                 ]"
  private lemma "dom(map_of system_P4S) \<subseteq> set (nodesL policy)"
    by(simp add: system_P4S_def policy_def)
  definition "system_P4S_m \<equiv> new_meta_system_boundary system_P4S ''P4S''"
end



context begin
  private definition "system_P4Sstorage \<equiv>
                [(''P4S_DB'',  SystemBoundaryInput)
                 ]"
  private lemma "dom(map_of system_P4Sstorage) \<subseteq> set (nodesL policy)"
    by(simp add: system_P4Sstorage_def policy_def)
  definition "system_P4Sstorage_m \<equiv> new_meta_system_boundary system_P4Sstorage ''P4S storage''"
end


definition "invariants \<equiv> [Tainting_m] @ system_EMS_m @ system_P4S_m @system_P4Sstorage_m"

lemma "all_security_requirements_fulfilled invariants policy" by eval
ML\<open>
visualize_graph @{context} @{term "invariants"} @{term "policy"};
\<close>


value[code] "implc_get_offending_flows invariants (policy\<lparr> edgesL := edgesL policy\<rparr>)"
(*ML{*
visualize_graph @{context} @{term "invariants"} @{term "(policy\<lparr> edgesL := edgesL policy\<rparr>)"};
*}*)
ML\<open>
visualize_graph_header @{context} @{term "invariants"} @{term "policy"} @{term tainiting_host_attributes};
\<close>


definition make_policy :: "('a SecurityInvariant) list \<Rightarrow> 'a list \<Rightarrow> 'a list_graph" where
  "make_policy sinvars Vs \<equiv> generate_valid_topology sinvars \<lparr>nodesL = Vs, edgesL = List.product Vs Vs \<rparr>"


value[code] "make_policy invariants (nodesL policy)"

ML_val\<open>
visualize_edges @{context} @{term "edgesL policy"}
    [("edge [dir=\"arrow\", style=dashed, color=\"#FF8822\", constraint=false]",
     @{term "[(e1, e2) \<leftarrow>  List.product  (nodesL policy) (nodesL policy).
     (e1,e2) \<notin> set (edgesL (make_policy invariants (nodesL policy))) \<and> (e2 = ''Adversary'') \<and> (e1 \<noteq> ''Adversary'')]"})] "";
\<close>


end
