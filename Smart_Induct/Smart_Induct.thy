(*  Title:      Smart_Induct/Smart_Induct.thy
    Author:     Yutaka Nagashima, CIIRC, CTU, University of Innsbruck
*)
theory Smart_Induct
  imports  "PSL.PSL" "LiFtEr.LiFtEr"
  keywords "smart_induct" :: diag
begin

ML_file "Dynamic_Induct.ML"
ML_file "Multi_Stage_Screening.ML"
ML_file "LiFtEr_Heuristics.ML"
ML_file "Scoring_Using_LiFtEr.ML"

setup\<open> Apply_LiFtEr.update_assert "heuristic_1"  (LiFtEr_Heuristics.all_ind_term_are_non_const_wo_syntactic_sugar                           , 1)\<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_2"  (LiFtEr_Heuristics.all_ind_terms_have_an_occ_as_variable_at_bottom                         , 1)\<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_3"  (LiFtEr_Heuristics.all_ind_vars_are_arguments_of_a_recursive_function                      , 1)\<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_4"  (LiFtEr_Heuristics.all_ind_vars_are_arguments_of_a_rec_func_where_pattern_match_is_complete, 1)\<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_5"  (LiFtEr_Heuristics.all_ind_terms_are_arguments_of_a_const_with_a_related_rule_in_order     , 1)\<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_6"  (LiFtEr_Heuristics.ind_is_not_arb                                                          , 2)\<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_7"  (LiFtEr_Heuristics.at_least_one_recursive_term                                             , 1)\<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_8"  (LiFtEr_Heuristics.at_least_one_on                                                         , 2)\<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_9"  (LiFtEr_Heuristics.one_on_is_deepest                                                       , 1)\<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_10" (LiFtEr_Heuristics.ons_and_arbs_share_func                                                 , 1)\<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_11" (LiFtEr_Heuristics.all_args_of_rule_as_ons                                                 , 1)\<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_12" (LiFtEr_Heuristics.arb_share_parent_with_ind                                               , 1)\<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_13" (LiFtEr_Heuristics.no_arb_should_be_at_the_same_loc_as_ind                                 , 2)\<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_14" (LiFtEr_Heuristics.only_one_rule                                                           , 1)\<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_15" (LiFtEr_Heuristics.inner_rec_const_rule                                                    , 1)\<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_16" (LiFtEr_Heuristics.no_ind_at_nth_arg_if_two_occ_of_recs                                    , 1)\<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_17" (LiFtEr_Heuristics.no_diff_var_at_same_pos_for_diff_occ_of_rec                             , 1)\<close>
setup\<open> Apply_LiFtEr.update_assert "heuristic_20" (LiFtEr_Heuristics.rule_inversion_on_premise                                               , 1)\<close>
(*
setup\<open> Apply_LiFtEr.update_assert "heuristic_21" (LiFtEr_Heuristics.rule_inversion_on_a_member_if_inductive_set_in_a_premise                , 6)\<close>
*)
ML\<open> val _ = Outer_Syntax.command @{command_keyword smart_induct} "recommend which method to use." (Scan.succeed Scoring_Using_LiFtEr.smart_induct_cmd); \<close>

end