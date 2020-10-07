theory Impl_List_Playground_statefulpolicycompliance
imports "../TopoS_Impl"
    Impl_List_Playground_ChairNetwork
begin


thm ChairNetwork_def
thm ChairSecurityRequirements_def

definition "ChairNetwork_stateful_IFS =
  \<lparr> hostsL = nodesL ChairNetwork,
    flows_fixL = edgesL ChairNetwork,
    flows_stateL = filter_IFS_no_violations ChairNetwork ChairSecurityRequirements \<rparr>"
value "edgesL ChairNetwork"
value "filter_IFS_no_violations ChairNetwork ChairSecurityRequirements"
value "ChairNetwork_stateful_IFS"
lemma "set (flows_stateL ChairNetwork_stateful_IFS) \<subseteq>
       (set (flows_fixL ChairNetwork_stateful_IFS))" by eval (*must always hold*)
value "(set (flows_fixL ChairNetwork_stateful_IFS)) - set (flows_stateL ChairNetwork_stateful_IFS)"
(*only problems: printers!!!*)
value "stateful_list_policy_to_list_graph ChairNetwork_stateful_IFS"

definition "ChairNetwork_stateful_ACS =
  \<lparr> hostsL = nodesL ChairNetwork,
   flows_fixL = edgesL ChairNetwork,
   flows_stateL = filter_compliant_stateful_ACS ChairNetwork ChairSecurityRequirements \<rparr>"
value "edgesL ChairNetwork"
value "filter_compliant_stateful_ACS ChairNetwork ChairSecurityRequirements"
value "ChairNetwork_stateful_ACS"
lemma "set (flows_stateL ChairNetwork_stateful_ACS) \<subseteq> (set (flows_fixL ChairNetwork_stateful_ACS))"
  by eval (*must always hold*)
value "(set (flows_fixL ChairNetwork_stateful_ACS)) - set (flows_stateL ChairNetwork_stateful_ACS)"

(*TODO: lemma \<dots> = X by eval*)

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
  [("edge [dir=\"arrow\", style=dashed, color=\"#FF8822\", constraint=false]",
   @{term "flows_stateL ChairNetwork_stateful"})] ""; 
\<close>




end
