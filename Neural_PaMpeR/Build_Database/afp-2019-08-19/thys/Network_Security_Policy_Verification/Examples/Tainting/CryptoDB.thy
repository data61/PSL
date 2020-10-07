section\<open>CryptoDB\<close>
theory CryptoDB
imports "../../TopoS_Impl"
begin

ML\<open>
case !Graphviz.open_viewer of
    OpenImmediately => Graphviz.open_viewer := AskTimeouted 3.0
  | AskTimeouted _ => ()
  | DoNothing => ()
\<close>

definition policy :: "string list_graph" where
  "policy \<equiv> \<lparr> nodesL = [
                        ''A'', ''A_encrypter'', ''A_channel'',
                        ''B'', ''B_encrypter'', ''B_channel'',
                        ''C'', ''C_encrypter'', ''C_channel_in'', ''C_channel_out'', ''C_decrypter'',
                        ''Adversary'',
                        ''CryptoDB''],
              edgesL = [
              (''A'', ''A_encrypter''), (''A_encrypter'', ''A_channel''), (''A_channel'', ''CryptoDB''),
              (''B'', ''B_encrypter''), (''B_encrypter'', ''B_channel''), (''B_channel'', ''CryptoDB''),
              (''C'', ''C_encrypter''), (''C_encrypter'', ''C_channel_out''), (''C_channel_out'', ''CryptoDB''),
              (''CryptoDB'', ''C_channel_in''), (''C_channel_in'', ''C_decrypter''), (''C_decrypter'', ''C'')
              ] \<rparr>"

context begin
  private definition "tainiting_host_attributes \<equiv> [
                           ''A'' \<mapsto> TaintsUntaints {''A''} {},
                           ''A_encrypter'' \<mapsto> TaintsUntaints {} {''A''},
                           ''A_channel'' \<mapsto> TaintsUntaints {} {},
                           ''B'' \<mapsto> TaintsUntaints {''B''} {},
                           ''B_encrypter'' \<mapsto> TaintsUntaints {} {''B''},
                           ''B_channel'' \<mapsto> TaintsUntaints {} {},
                           ''C'' \<mapsto> TaintsUntaints {''C''} {},
                           ''C_encrypter'' \<mapsto> TaintsUntaints {} {''C''},
                           ''C_decrypter'' \<mapsto> TaintsUntaints {''C''} {},
                           ''C_channel_out'' \<mapsto> TaintsUntaints {} {},
                           ''C_channel_in'' \<mapsto> TaintsUntaints {} {},
                           ''Adversary'' \<mapsto> TaintsUntaints {} {}
                           ]"
  private lemma "dom (tainiting_host_attributes) \<subseteq> set (nodesL policy)"
    by(simp add: tainiting_host_attributes_def policy_def)
  definition "Tainting_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_TaintingTrusted \<lparr>
        node_properties = tainiting_host_attributes \<rparr> ''user-data''"
end
lemma "wf_list_graph policy" by eval

ML_val\<open>
visualize_graph @{context} @{term "[]::string SecurityInvariant list"} @{term "policy"};
\<close>


context begin
  private definition "A_host_attributes \<equiv>
                [''A'' \<mapsto> Member,
                 ''A_encrypter'' \<mapsto> Member,
                 ''A_channel'' \<mapsto> Member
                 ]"
  private lemma "dom A_host_attributes \<subseteq> set (nodesL policy)"
    by(simp add: A_host_attributes_def policy_def)
  definition "SystemA_m \<equiv> new_configured_list_SecurityInvariant
                                  SINVAR_LIB_SubnetsInGW
                                    \<lparr> node_properties = A_host_attributes \<rparr> ''sys-A''"
end

context begin
  private definition "B_host_attributes \<equiv>
                [''B'' \<mapsto> Member,
                 ''B_encrypter'' \<mapsto> Member,
                 ''B_channel'' \<mapsto> Member
                 ]"
  private lemma "dom B_host_attributes \<subseteq> set (nodesL policy)"
    by(simp add: B_host_attributes_def policy_def)
  definition "SystemB_m \<equiv> new_configured_list_SecurityInvariant
                                  SINVAR_LIB_SubnetsInGW
                                    \<lparr> node_properties = B_host_attributes \<rparr> ''sys-B''"
end



context begin
  private definition "C_host_attributes \<equiv>
                [(''C_channel_in'', SystemBoundaryInput),
                 (''C_decrypter'', SystemComponent),
                 (''C'', SystemComponent),
                 (''C_encrypter'', SystemComponent),
                 (''C_channel_out'', SystemBoundaryOutput)
                 ]"
  private lemma "dom (map_of C_host_attributes) \<subseteq> set (nodesL policy)"
    by(simp add: C_host_attributes_def policy_def)
  definition "SystemC_m \<equiv> new_meta_system_boundary C_host_attributes ''sys-C''"
end

definition "invariants \<equiv> [Tainting_m, SystemA_m, SystemB_m] @ SystemC_m"

lemma "all_security_requirements_fulfilled invariants policy" by eval
ML\<open>
visualize_graph @{context} @{term "invariants"} @{term "policy"};
\<close>


value[code] "implc_get_offending_flows invariants (policy\<lparr> edgesL := edgesL policy\<rparr>)"
ML\<open>
visualize_graph @{context} @{term "invariants"} @{term "(policy\<lparr> edgesL := edgesL policy\<rparr>)"};
\<close>


definition make_policy :: "('a SecurityInvariant) list \<Rightarrow> 'a list \<Rightarrow> 'a list_graph" where
  "make_policy sinvars Vs \<equiv> generate_valid_topology sinvars \<lparr>nodesL = Vs, edgesL = List.product Vs Vs \<rparr>"


value[code] "make_policy invariants (nodesL policy)"

text\<open>visualizing all flows which may not end at the adversary. I.e. things which are prohibited.\<close>
ML_val\<open>
visualize_edges @{context} @{term "edgesL policy"}
    [("edge [dir=\"arrow\", style=dashed, color=\"#FF8822\", constraint=false]",
     @{term "[(e1, e2) \<leftarrow>  List.product  (nodesL policy) (nodesL policy).
     ((e1,e2) \<notin> set (edgesL policy)) \<and> ((e1,e2) \<notin> set (edgesL (make_policy invariants (nodesL policy)))) \<and> (e2 = ''Adversary'') \<and> (e1 \<noteq> ''Adversary'')]"})] "";
\<close>


ML_val\<open>
visualize_edges @{context} @{term "edgesL policy"}
    [("edge [dir=\"arrow\", style=dashed, color=\"#FF8822\", constraint=false]",
     @{term "[e \<leftarrow> edgesL (make_policy invariants (nodesL policy)).
                e \<notin> set (edgesL policy)]"})] "";
\<close>


end
