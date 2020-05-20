section\<open>Measr Droid\<close>
theory MeasrDroid
imports "../../TopoS_Impl"
begin


ML\<open>
case !Graphviz.open_viewer of
    OpenImmediately => Graphviz.open_viewer := AskTimeouted 3.0
  | AskTimeouted _ => ()
  | DoNothing => ()
\<close>

subsection\<open>Architecture Definition\<close>

definition policy :: "string list_graph" where
  "policy \<equiv> \<lparr> nodesL = [ \<comment> \<open>SmartPhone A:\<close>
                         ''Sensors_A'',
                         ''Encryption_A'',
                         ''Client_A_out'',

                         \<comment> \<open>SmartPhone B:\<close>
                         ''Sensors_B'',
                         ''Encryption_B'',
                         ''Client_B_out'',

                         \<comment> \<open>SmartPhone C:\<close>
                         ''Sensors_C'',
                         ''Encryption_C'',
                         ''Client_C_out'',

                         ''UploadDroid'',

                         \<comment> \<open>CollectDroid:\<close>
                         ''C3PO_in'',
                         ''C3PO_Dec_A'',
                         ''C3PO_Dec_B'',
                         ''C3PO_Dec_C'',
                         ''C3PO_Storage'',

                         ''Adversary''],
              edgesL = [
              (''Sensors_A'',    ''Encryption_A''),
              (''Encryption_A'', ''Client_A_out''),
              (''Client_A_out'', ''UploadDroid''),

              (''Sensors_B'',    ''Encryption_B''),
              (''Encryption_B'', ''Client_B_out''),
              (''Client_B_out'', ''UploadDroid''),

              (''Sensors_C'',    ''Encryption_C''),
              (''Encryption_C'', ''Client_C_out''),
              (''Client_C_out'', ''UploadDroid''),

              \<^cancel>\<open>(''UploadDroid'', ''C3PO_in'')\<close>  \<comment> \<open>C3PO pulls!\<close>
              (''C3PO_in'', ''UploadDroid''),

              (''C3PO_in'', ''C3PO_Dec_A''),
              (''C3PO_in'', ''C3PO_Dec_B''),
              (''C3PO_in'', ''C3PO_Dec_C''),

              (''C3PO_Dec_A'', ''C3PO_Storage''),
              (''C3PO_Dec_B'', ''C3PO_Storage''),
              (''C3PO_Dec_C'', ''C3PO_Storage'')

              ] \<rparr>"

subsection\<open>Specification of Security Requirements\<close>


context begin
  definition "taint_labels \<equiv> [
                           ''Sensors_A'' \<mapsto> TaintsUntaints {''A''} {},
                           ''Sensors_B'' \<mapsto> TaintsUntaints {''B''} {},
                           ''Sensors_C'' \<mapsto> TaintsUntaints {''C''} {},

                           ''Encryption_A'' \<mapsto> TaintsUntaints {} {''A''} ,
                           ''Encryption_B'' \<mapsto> TaintsUntaints {} {''B''} ,
                           ''Encryption_C'' \<mapsto> TaintsUntaints {} {''C''} ,

                           ''C3PO_Dec_A'' \<mapsto> TaintsUntaints {''A''} {},
                           ''C3PO_Dec_B'' \<mapsto> TaintsUntaints {''B''} {},
                           ''C3PO_Dec_C'' \<mapsto> TaintsUntaints {''C''} {} ,

                           ''C3PO_Storage'' \<mapsto> TaintsUntaints {''A'',''B'',''C''} {}

                           ]"
  private lemma "dom (taint_labels) \<subseteq> set (nodesL policy)" by(simp add: taint_labels_def policy_def)
  definition "Tainting_m \<equiv> new_configured_list_SecurityInvariant SINVAR_LIB_TaintingTrusted \<lparr>
        node_properties = taint_labels \<rparr> ''taint labels''"


  text\<open>A convenient way to specify encryption and decryption pairs\<close>
  private definition mk_Enc_Dec_pair
    :: "string set \<Rightarrow> (SINVAR_TaintingTrusted.taints \<times> SINVAR_TaintingTrusted.taints)"
  where
  "mk_Enc_Dec_pair taints_to_be_encrypted \<equiv> (TaintsUntaints {} taints_to_be_encrypted,
                                             TaintsUntaints taints_to_be_encrypted {})"

  lemma "taint_labels = (let (Enc_A, Dec_A) = mk_Enc_Dec_pair {''A''};
                             (Enc_B, Dec_B) = mk_Enc_Dec_pair {''B''};
                             (Enc_C, Dec_C) = mk_Enc_Dec_pair {''C''}
                       in [
                           ''Sensors_A'' \<mapsto> TaintsUntaints {''A''} {},
                           ''Sensors_B'' \<mapsto> TaintsUntaints {''B''} {},
                           ''Sensors_C'' \<mapsto> TaintsUntaints {''C''} {},

                           ''Encryption_A'' \<mapsto> Enc_A,
                           ''Encryption_B'' \<mapsto> Enc_B,
                           ''Encryption_C'' \<mapsto> Enc_C,

                           ''C3PO_Dec_A'' \<mapsto> Dec_A,
                           ''C3PO_Dec_B'' \<mapsto> Dec_B,
                           ''C3PO_Dec_C'' \<mapsto> Dec_C,

                           ''C3PO_Storage'' \<mapsto> TaintsUntaints {''A'',''B'',''C''} {}
                           ])"
    by(simp add: taint_labels_def mk_Enc_Dec_pair_def)
end
lemma "wf_list_graph policy" by eval

ML_val\<open>
visualize_graph @{context} @{term "[]::string SecurityInvariant list"} @{term "policy"};
\<close>


context begin
  private definition "smartphone_system_A \<equiv>
                [(''Client_A_out'' ,  SystemBoundaryOutput),
                 (''Sensors_A'' ,  SystemComponent),
                 (''Encryption_A'' ,  SystemComponent)
                 ]"
  private lemma "dom (map_of smartphone_system_A) \<subseteq> set (nodesL policy)"
    by(simp add: smartphone_system_A_def policy_def)
  definition "SystemA_m \<equiv> new_meta_system_boundary smartphone_system_A ''smartphone A''"
end

context begin
  private definition "smartphone_system_B \<equiv>
                [(''Client_B_out'' ,  SystemBoundaryOutput),
                 (''Sensors_B'' ,  SystemComponent),
                 (''Encryption_B'' ,  SystemComponent)
                 ]"
  private lemma "dom(map_of smartphone_system_B) \<subseteq> set (nodesL policy)"
    by(simp add: smartphone_system_B_def policy_def)
  definition "SystemB_m \<equiv> new_meta_system_boundary smartphone_system_B ''smartphone B''"
end

context begin
  private definition "smartphone_system_C \<equiv>
                [(''Client_C_out'' ,  SystemBoundaryOutput),
                 (''Sensors_C'' ,  SystemComponent),
                 (''Encryption_C'' ,  SystemComponent)
                 ]"
  private lemma "dom(map_of smartphone_system_C) \<subseteq> set (nodesL policy)"
    by(simp add: smartphone_system_C_def policy_def)
  definition "SystemC_m \<equiv> new_meta_system_boundary smartphone_system_C ''smartphone C''"
end

context begin
  private definition "system_C3PO \<equiv>
                [(''C3PO_in'' ,  SystemBoundaryOutput),
                 (''C3PO_Dec_A'' ,  SystemComponent),
                 (''C3PO_Dec_C'' ,  SystemComponent),
                 (''C3PO_Dec_B'' ,  SystemComponent),
                 (''C3PO_Storage'' ,  SystemComponent)
                 ]"
  private lemma "dom(map_of system_C3PO) \<subseteq> set (nodesL policy)"
    by(simp add: system_C3PO_def policy_def)
  definition "SystemC3PO_m \<equiv> new_meta_system_boundary system_C3PO ''C3PO''"
end

context begin
  text\<open>Technically, the following definition does not impose any restrictions.
       Upload Droid must be reachable from anywhere, therefore it is an @{const SystemBoundaryInput}.
       In addition, Upload Droid will maintain stateful connections with other entities.
       Therefore, we want to allow Upload Droid to send out any data, which also makes it an
       @{const SystemBoundaryOutput}.
       \<close>
  private definition "system_UploadDroid \<equiv>
                [(''UploadDroid'',  SystemBoundaryInputOutput)
                 ]"
  private lemma "dom(map_of system_UploadDroid) \<subseteq> set (nodesL policy)"
    by(simp add: system_UploadDroid_def policy_def)
  definition "SystemUploadDroid_m \<equiv> new_meta_system_boundary system_UploadDroid ''UploadDroid''"
end

definition "invariants \<equiv> [Tainting_m] @ SystemA_m @ SystemB_m @ SystemC_m @ SystemC3PO_m @ SystemUploadDroid_m"

lemma "all_security_requirements_fulfilled invariants policy" by eval
ML\<open>
visualize_graph @{context} @{term "invariants"} @{term "policy"};
\<close>


value[code] "implc_get_offending_flows invariants (policy\<lparr> edgesL := edgesL policy\<rparr>)"
(*ML{*
visualize_graph @{context} @{term "invariants"} @{term "(policy\<lparr> edgesL := (''Adversary'', ''C3PO_Storage'')#edgesL policy\<rparr>)"};
*}*)
ML\<open>
visualize_graph_header @{context} @{term "invariants"} @{term "policy"} @{term taint_labels};
\<close>

subsection\<open>Analyzing the Policy\<close>

definition make_policy :: "('a SecurityInvariant) list \<Rightarrow> 'a list \<Rightarrow> 'a list_graph" where
  "make_policy sinvars Vs \<equiv> generate_valid_topology sinvars \<lparr>nodesL = Vs, edgesL = List.product Vs Vs \<rparr>"


value[code] "make_policy invariants (nodesL policy)"

lemma "set (edgesL policy) \<subseteq> set (edgesL (make_policy invariants (nodesL policy)))" by eval

text\<open>
We analyze the specification of our security invariants. The model includes a node @{term "''Adversary''"}
and we will analyze which interaction with an adversary are not prohibited by the requirements. 
Therefore, we generate a policy only from the security invariants and compare it to our manually designed policy.

We find the following flows which are allowed but which we did not consider in our policy 
 \<^item> All reflexive flows, i.e. every component can interact with itself. This is fine.
 \<^item> Within each smartphone, internally, arbitrary communication is possible. We cannot prevent this at a user's smartphone.
 \<^item> Every smartphone could send data to the adversary.
   It is important that this is generally allowed since we don't to put any restrictions on the
   Internet connectivity of a smartphone. 
   For example, this allows the smartphone user to surf facebook, which is not a trusted component in our system.
   The collected data is encrypted once it leaves the smartphone (via MeasrDroid), therefore, sensor data is not leaked.
 \<^item> @{term "''C3PO_in''"} could send data to the adversary. At this point, the data is still encrypted.
   It would be possible to add an additional security invariant to make sure that @{term "''C3PO_in''"}
   only connects to @{term "''UploadDroid''"}.
 \<^item> An adversary could send data to @{term "''UploadDroid''"}.
   Since the system shall be accessible to any smartphone connected to the Internet, without authentication,
   we cannot prevent that a malicious user might send fake data.
 \<^item> The Upload Droid could send data to the adversary.
   This does not undermine the security concept because upload droid only stores encrypted data. 
   In fact, the security assumptions were from the very beginning that @{term "''UploadDroid''"} can get compromised.
 \<^item> C3PO could directly save data in its database without decrypting.
   This is fine and might potentially be used in a future version for backups.
\<close>
lemma "set [e \<leftarrow> edgesL (make_policy invariants (nodesL policy)). e \<notin> set (edgesL policy)] =
 set [(v,v). v \<leftarrow> (nodesL policy)] \<union>
 {(''Encryption_A'', ''Sensors_A''), (''Client_A_out'', ''Sensors_A''), (''Client_A_out'', ''Encryption_A'')} \<union>

 {(''Encryption_B'', ''Sensors_B''), (''Client_B_out'', ''Sensors_B''), (''Client_B_out'', ''Encryption_B'')} \<union>

 {(''Encryption_C'', ''Sensors_C''), (''Client_C_out'', ''Sensors_C''),  (''Client_C_out'', ''Encryption_C'')} \<union>
 
 {(''Client_C_out'', ''Adversary''),
  (''Client_B_out'', ''Adversary''),
  (''Client_A_out'', ''Adversary'')} \<union>

 {(''C3PO_in'', ''Adversary'')} \<union>

 {(''Adversary'', ''UploadDroid'')} \<union>

 {(''UploadDroid'', ''Adversary'')} \<union>

 {(''C3PO_in'', ''C3PO_Storage'')}" by eval

text\<open>visualization\<close>
ML_val\<open>
visualize_edges @{context} @{term "edgesL policy"} 
    [("edge [dir=\"arrow\", style=dashed, color=\"#3399FF\", constraint=false]",
     @{term "[e \<leftarrow> edgesL (make_policy invariants (nodesL policy)). e \<notin> set (edgesL policy)]"})] ""; 
\<close>

text\<open>A visualization which shows all flows to the adversary which must NEVER happen
      (only considering taint labels, i.e. system boundaries are not considered).\<close>
ML_val\<open>
visualize_edges @{context} @{term "edgesL policy"}
    [("edge [dir=\"arrow\", style=dashed, color=\"#FF8822\", constraint=false]",
     @{term "[(e1, e2) \<leftarrow>  List.product  (nodesL policy) (nodesL policy).
     (e1,e2) \<notin> set (edgesL (make_policy [Tainting_m] (nodesL policy))) \<and> (e2 = ''Adversary'') \<and> (e1 \<noteq> ''Adversary'')]"})] "";
\<close>

text\<open>We conclude that the security invariants adequately reflect all aspects of the system we wanted to specify.\<close>






subsection\<open>A stateful implementation\<close>


definition "stateful_policy = generate_valid_stateful_policy_IFSACS policy invariants"
ML_val\<open>
visualize_edges @{context} @{term "flows_fixL stateful_policy"}
    [("edge [dir=\"arrow\", style=dashed, color=\"#FF8822\", constraint=false]", @{term "flows_stateL stateful_policy"})] "";
\<close>


lemma "stateful_policy =
\<lparr>hostsL =
    [''Sensors_A'', ''Encryption_A'', ''Client_A_out'', ''Sensors_B'', ''Encryption_B'', ''Client_B_out'', ''Sensors_C'',
     ''Encryption_C'', ''Client_C_out'', ''UploadDroid'', ''C3PO_in'', ''C3PO_Dec_A'', ''C3PO_Dec_B'', ''C3PO_Dec_C'',
     ''C3PO_Storage'', ''Adversary''],
    flows_fixL =
      [(''Sensors_A'', ''Encryption_A''), (''Encryption_A'', ''Client_A_out''), (''Client_A_out'', ''UploadDroid''),
       (''Sensors_B'', ''Encryption_B''), (''Encryption_B'', ''Client_B_out''), (''Client_B_out'', ''UploadDroid''),
       (''Sensors_C'', ''Encryption_C''), (''Encryption_C'', ''Client_C_out''), (''Client_C_out'', ''UploadDroid''),
       (''C3PO_in'', ''UploadDroid''), (''C3PO_in'', ''C3PO_Dec_A''), (''C3PO_in'', ''C3PO_Dec_B''),
       (''C3PO_in'', ''C3PO_Dec_C''), (''C3PO_Dec_A'', ''C3PO_Storage''), (''C3PO_Dec_B'', ''C3PO_Storage''),
       (''C3PO_Dec_C'', ''C3PO_Storage'')],
    flows_stateL =
      [(''Sensors_A'', ''Encryption_A''), (''Encryption_A'', ''Client_A_out''), (''Client_A_out'', ''UploadDroid''),
       (''Sensors_B'', ''Encryption_B''), (''Encryption_B'', ''Client_B_out''), (''Client_B_out'', ''UploadDroid''),
       (''Sensors_C'', ''Encryption_C''), (''Encryption_C'', ''Client_C_out''), (''Client_C_out'', ''UploadDroid''),
       (''C3PO_in'', ''UploadDroid'')]\<rparr>"
by eval



subsection\<open>A firewall for Collect Droid\<close>
text\<open>The firewall is installed at @{term "''C3PO_in''"}, this we only filter for the rules which affect this component.\<close>
ML_val\<open>

(*header*)
writeln ("# flush all rules"^"\n"^
         "iptables -F"^"\n"^
         "#default policy for FORWARD chain:"^"\n"^
         "iptables -P INPUT DROP"^"\n"^
         "iptables -P OUTPUT DROP"^"\n"^
         "iptables -P FORWARD DROP");


writeln ("# INPUT"^"\n");
iterate_edges_ML @{context}  @{term "[(s,r) \<leftarrow> flows_fixL stateful_policy. r = ''C3PO_in'']"}
  (fn (v1,v2) => writeln ("iptables -A INPUT -i $"^v1^"_iface -s $"^v1^"_ipv4 -o $"^v2^"_iface -d $"^v2^"_ipv4 -j ACCEPT"^" # "^v1^" -> "^v2) )
  (fn _ => () )
  (fn _ => () );
iterate_edges_ML @{context} @{term "[(s,r) \<leftarrow> flows_stateL stateful_policy. s = ''C3PO_in'']"}
  (fn (v1,v2) => writeln ("iptables -I INPUT -m state --state ESTABLISHED -i $"^v2^"_iface -s $"^v2^"_ipv4 -o $"^v1^"_iface -d $"^v1^"_ipv4 -j ACCEPT # "^v2^" -> "^v1^" (answer)") )
  (fn _ => () )
  (fn _ => () );

writeln ("# OUTPUT"^"\n");
iterate_edges_ML @{context}  @{term "[(s,r) \<leftarrow> flows_fixL stateful_policy. s = ''C3PO_in'']"}
  (fn (v1,v2) => writeln ("iptables -A OUTPUT -i $"^v1^"_iface -s $"^v1^"_ipv4 -o $"^v2^"_iface -d $"^v2^"_ipv4 -j ACCEPT"^" # "^v1^" -> "^v2) )
  (fn _ => () )
  (fn _ => () );
iterate_edges_ML @{context} @{term "[(s,r) \<leftarrow> flows_stateL stateful_policy. r = ''C3PO_in'']"}
  (fn (v1,v2) => writeln ("iptables -I OUTPUT -m state --state ESTABLISHED -i $"^v2^"_iface -s $"^v2^"_ipv4 -o $"^v1^"_iface -d $"^v1^"_ipv4 -j ACCEPT # "^v2^" -> "^v1^" (answer)") )
  (fn _ => () )
  (fn _ => () );
\<close>

end
