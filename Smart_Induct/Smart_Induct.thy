(*  Title:      Smart_Induct/Smart_Induct.thy
    Author:     Yutaka Nagashima, CIIRC, CTU, University of Innsbruck
*)
theory Smart_Induct
  imports  "LiFtEr.LiFtEr"
  keywords "smart_induct" :: diag
begin

ML_file "Dynamic_Induct.ML"
ML_file "Multi_Stage_Screening.ML"
ML_file "LiFtEr_Heuristics.ML"
ML_file "Scoring_Using_LiFtEr.ML"

setup\<open> Apply_LiFtEr.update_assert "heuristic_1"  LiFtEr_Heuristics.all_ind_term_are_non_const_wo_syntactic_sugar \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_2"  LiFtEr_Heuristics.all_ind_terms_have_an_occ_as_variable_at_bottom \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_3"  LiFtEr_Heuristics.all_ind_vars_are_arguments_of_a_recursive_function \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_4"  LiFtEr_Heuristics.all_ind_vars_are_arguments_of_a_rec_func_where_pattern_match_is_complete \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_5"  LiFtEr_Heuristics.all_ind_terms_are_arguments_of_a_const_with_a_related_rule_in_order \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_6"  LiFtEr_Heuristics.ind_is_not_arb \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_7"  LiFtEr_Heuristics.at_least_one_recursive_term \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_8"  LiFtEr_Heuristics.at_least_one_on \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_9"  LiFtEr_Heuristics.one_on_is_deepest \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_10" LiFtEr_Heuristics.ons_and_arbs_share_func \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_11" LiFtEr_Heuristics.all_args_of_rule_as_ons \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_12" LiFtEr_Heuristics.arb_share_parent_with_ind \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_13" LiFtEr_Heuristics.no_arb_should_be_at_the_same_loc_as_ind \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_14" LiFtEr_Heuristics.only_one_rule \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_15" LiFtEr_Heuristics.inner_rec_const_rule \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_16" LiFtEr_Heuristics.no_ind_at_nth_arg_if_two_occ_of_recs \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_17" LiFtEr_Heuristics.no_diff_var_at_same_pos_for_diff_occ_of_rec \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_18" LiFtEr_Heuristics.ind_is_not_arb \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_19" LiFtEr_Heuristics.no_arb_should_be_at_the_same_loc_as_ind \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_20" LiFtEr_Heuristics.rule_inversion_on_premise \<close>

setup\<open> Apply_LiFtEr.update_assert "heuristic_21" LiFtEr_Heuristics.rule_inversion_on_a_member_if_inductive_set_in_a_premise \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_22" LiFtEr_Heuristics.rule_inversion_on_a_member_if_inductive_set_in_a_premise \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_23" LiFtEr_Heuristics.rule_inversion_on_a_member_if_inductive_set_in_a_premise \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_24" LiFtEr_Heuristics.rule_inversion_on_a_member_if_inductive_set_in_a_premise \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_27" LiFtEr_Heuristics.rule_inversion_on_a_member_if_inductive_set_in_a_premise \<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_28" LiFtEr_Heuristics.rule_inversion_on_a_member_if_inductive_set_in_a_premise \<close>

setup\<open> Apply_LiFtEr.update_assert "heuristic_25"  LiFtEr_Heuristics.at_least_one_on \<close>
(*
setup\<open> Apply_LiFtEr.update_assert "heuristic_24" LiFtEr_Heuristics.rule_inversion_on_a_member_if_inductive_set_in_a_premise \<close>
*)

ML\<open> val _ = Outer_Syntax.command @{command_keyword smart_induct} "recommend which method to use." (Scan.succeed Scoring_Using_LiFtEr.smart_induct_cmd); \<close>

end