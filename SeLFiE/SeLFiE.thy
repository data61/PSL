(*  Title:      PSL/SeLFiE/SeLFiE.thy
 *  Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
 *
 * Examples about rev and itrev were originally developed by Tobias Nipkow and Gerwin Klein
 * as Isabelle theory files accompanying their book "Concrete Semantics".
 *
 * The PDF file of the book and the original Isabelle theory files are available
 * at the following website:
 *   http://concrete-semantics.org/index.html
 *
 * MeLoId: Machine Learning Induction for Isabelle/HOL, and
 * LiFtEr: Logical Feature Extractor.
 * SeLFiE: Semantic Logical Feature Extractor.
 *)
theory SeLFiE
  imports "PSL.PSL"
  keywords "assert_SeLFiE_true"          :: diag
  and      "assert_SeLFiE_false"         :: diag
  and      "semantic_induct"             :: diag
  and      "all_induction_heuristic"     :: diag
  and      "all_generalization_heuristic":: diag
begin
ML\<open> structure Old_Pattern = Pattern \<close>
ML\<open>prod_ord; list_ord \<close>
find_theorems name:"wf_induct"

(* pre-processing *)
ML_file "../PSL/Utils.ML"
ML_file "../MeLoId/src/MeLoId_Util.ML"
ML_file "Pattern.ML"
ML_file "Util.ML"

ML_file "Unique_Node.ML"
ML_file "Unique_Node_Test.ML"
ML_file "Path_Table_And_Print_Table.ML"
ML_file "Term_Table.ML"
(* This Term_Table_Test works only in the interactive mode.
ML_file "Term_Table_Test.ML"
*)

ML_file "Dynamic_Induct.ML"

ML_file "Eval_Bool.ML"
ML_file "Eval_Number.ML"
ML_file "Eval_Node.ML"
ML_file "Eval_Unode.ML"
ML_file "Eval_Print.ML"

ML_file "Path_To_Unode.ML"  (*The bifurcation of "inner" and "outer" starts here.*)
ML_file "Print_To_Paths.ML"

ML\<open> structure Print_To_Inner_Paths = from_Path_Table_and_Path_To_Unode_to_Print_To_Paths(Inner_Path_Table): PRINT_TO_PATHS; \<close>
ML\<open> structure Print_To_Outer_Paths = from_Path_Table_and_Path_To_Unode_to_Print_To_Paths(Outer_Path_Table): PRINT_TO_PATHS; \<close>

ML_file "Eval_Path.ML"
ML_file "Eval_Parameter.ML"
ML_file "Eval_Parameter_With_Bool.ML"
ML_file "Quantifier_Domain.ML"
ML_file "Eval_Unary.ML"
ML_file "Eval_Multi_Arity.ML"      
ML_file "Eval_Variable.ML"
ML_file "Eval_Surface.ML"
ML_file "Eval_Syntactic_Sugar.ML"

ML_file "Smart_Construction.ML"
ML_file "Screening.ML"
ML_file "Apply_SeLFiE.ML"
ML_file "SeLFiE_Assertion.ML"
ML\<open> Apply_SeLFiE.activate (); \<close>

setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "heuristic_1"                                                                                                                        ) (SeLFiE_Assertion.heuristic_1                                                                                                                        , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "heuristic_2"                                                                                                                        ) (SeLFiE_Assertion.heuristic_2                                                                                                                        , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "heuristic_3"                                                                                                                        ) (SeLFiE_Assertion.heuristic_3                                                                                                                        , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "heuristic_4"                                                                                                                        ) (SeLFiE_Assertion.heuristic_4                                                                                                                        , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "heuristic_5"                                                                                                                        ) (SeLFiE_Assertion.heuristic_5                                                                                                                        , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "heuristic_6"                                                                                                                        ) (SeLFiE_Assertion.heuristic_6                                                                                                                        , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "heuristic_7"                                                                                                                        ) (SeLFiE_Assertion.heuristic_7                                                                                                                        , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "heuristic_8"                                                                                                                        ) (SeLFiE_Assertion.heuristic_8                                                                                                                        , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "heuristic_9"                                                                                                                        ) (SeLFiE_Assertion.heuristic_9                                                                                                                        , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "heuristic_10"                                                                                                                       ) (SeLFiE_Assertion.heuristic_10                                                                                                                       , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "heuristic_11"                                                                                                                       ) (SeLFiE_Assertion.heuristic_11                                                                                                                       , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "heuristic_12"                                                                                                                       ) (SeLFiE_Assertion.heuristic_12                                                                                                                       , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "heuristic_13"                                                                                                                       ) (SeLFiE_Assertion.heuristic_13                                                                                                                       , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "heuristic_14"                                                                                                                       ) (SeLFiE_Assertion.heuristic_14                                                                                                                       , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "lifter_1"     (*not good enough for smart_induction_2*)                                                                             ) (SeLFiE_Assertion.lifter_1                                                                                                                           , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "lifter_1b"    (*not good enough for smart_induction_2*)                                                                             ) (SeLFiE_Assertion.lifter_1b                                                                                                                          , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "lifter_2"                                                                                                                           ) (SeLFiE_Assertion.lifter_2                                                                                                                           , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Induction_Heuristic,      "lifter2_improved"                                                                                                                   ) (SeLFiE_Assertion.lifter2_improved                                                                                                                   , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "lifter_3"                                                                                                                           ) (SeLFiE_Assertion.lifter_3                                                                                                                           , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Induction_Heuristic,      "lifter_3_improved"                                                                                                                  ) (SeLFiE_Assertion.lifter_3_improved                                                                                                                  , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "lifter_4"     (*not good enough for smart_induction_2 because it is based solely on pattern-matching on the LHS*)                   ) (SeLFiE_Assertion.lifter_4                                                                                                                           , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Induction_Heuristic,      "lifter_5"     (*may be obsolete due to smart_construction, may be harmful for lacking generalization *)                             ) (SeLFiE_Assertion.lifter_5                                                                                                                           , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Generalization_Heuristic, "lifter_6"                                                                                                                           ) (SeLFiE_Assertion.lifter_6                                                                                                                           , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Induction_Heuristic,      "lifter_7"                                                                                                                           ) (SeLFiE_Assertion.lifter_7                                                                                                                           , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Induction_Heuristic,      "lifter_8"                                                                                                                           ) (SeLFiE_Assertion.lifter_8                                                                                                                           , 5) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "lifter_9"                                                                                                                           ) (SeLFiE_Assertion.lifter_9                                                                                                                           , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Induction_Heuristic,      "lifter_9_improved"                                                                                                                  ) (SeLFiE_Assertion.lifter_9_improved                                                                                                                  , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Generalization_Heuristic, "lifter_10"                                                                                                                          ) (SeLFiE_Assertion.lifter_10                                                                                                                          , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Induction_Heuristic,      "lifter_11"    (*may be harmful*)                                                                                                    ) (SeLFiE_Assertion.lifter_11                                                                                                                          , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Generalization_Heuristic, "lifter_12"                                                                                                                          ) (SeLFiE_Assertion.lifter_12                                                                                                                          , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "lifter_13"    (*may be harmful: no arbitrary is at the same relative location as induction in terms of a function. See sorted_wrt_dist_take_drop in Nearest_Neighbors.thy, for example.*)) (SeLFiE_Assertion.lifter_13                                                                     , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "lifter_14"    (*obsolete because of smart construction*)                                                                            ) (SeLFiE_Assertion.lifter_14                                                                                                                          , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Induction_Heuristic,      "lifter_15"    (*TODO: test the heuristic*)                                                                                          ) (SeLFiE_Assertion.lifter_15                                                                                                                          , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Induction_Heuristic,      "lifter_20"    (*rule inversion on a function in a premise*)(*TODO: test*)                                                           ) (SeLFiE_Assertion.lifter_20                                                                                                                          , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "test_dive_in"                                                                                                                       ) (SeLFiE_Assertion.test_dive_in                                                                                                                       , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "print_all_outer_prints"                                                                                                             ) (SeLFiE_Assertion.print_all_outer_prints                                                                                                             , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "print_all_inner_prints"                                                                                                             ) (SeLFiE_Assertion.print_all_inner_prints                                                                                                             , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "print_all_unodes"                                                                                                                   ) (SeLFiE_Assertion.print_all_unodes                                                                                                                   , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "print_outer_path_root"                                                                                                              ) (SeLFiE_Assertion.print_outer_path_root                                                                                                              , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "print_inner_roots"                                                                                                                  ) (SeLFiE_Assertion.print_inner_roots                                                                                                                  , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "print_all_inner_lhss"                                                                                                               ) (SeLFiE_Assertion.print_all_inner_lhss                                                                                                               , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "print_fst_params_of_fun_const"                                                                                                      ) (SeLFiE_Assertion.print_fst_params_of_fun_const                                                                                                      , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "test_is_a_meta_premise"                                                                                                             ) (SeLFiE_Assertion.test_is_a_meta_premise                                                                                                             , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "test_is_a_meta_conclusion"                                                                                                          ) (SeLFiE_Assertion.test_is_a_meta_conclusion                                                                                                          , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "test_is_a_meta_premise_or_below"                                                                                                    ) (SeLFiE_Assertion.test_is_a_meta_premise_or_below                                                                                                    , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "test_is_a_meta_conclusion_or_below"                                                                                                 ) (SeLFiE_Assertion.test_is_a_meta_conclusion_or_below                                                                                                 , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "test_is_more_than"                                                                                                                  ) (SeLFiE_Assertion.test_is_more_than                                                                                                                  , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Induction_Heuristic,      "is_defined_recursively_on_nth"                                                                                                      ) (SeLFiE_Assertion.is_defined_recursively_on_nth_outer                                                                                                , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Generalization_Heuristic, "generalize_arguments_used_in_recursion"                                                                                             ) (SeLFiE_Assertion.generalize_arguments_used_in_recursion                                                                                             , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Generalization_Heuristic, "for_all_arbs_there_should_be_a_change"                                                                                              ) (SeLFiE_Assertion.for_all_arbs_there_should_be_a_change                                                                                              , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "for_all_arbs_there_should_be_a_change_simplified_for_presentation"                                                                  ) (SeLFiE_Assertion.for_all_arbs_there_should_be_a_change_simplified_for_presentation                                                                  , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Generalization_Heuristic, "ind_on_lhs_of_eq_then_arb_on_rhs_of_eq"                                                                                             ) (SeLFiE_Assertion.ind_on_lhs_of_eq_then_arb_on_rhs_of_eq                                                                                             , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Induction_Heuristic,      "if_part_of_lhs_n_part_of_rhs_of_eq_is_induct_then_induct_on_part_of_lhs"                                                            ) (SeLFiE_Assertion.if_part_of_lhs_n_part_of_rhs_of_eq_is_induct_then_induct_on_part_of_lhs                                                            , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "test_Is_If_Then_Else"                                                                                                               ) (SeLFiE_Assertion.test_Is_If_Then_Else                                                                                                               , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "test_Is_Subprint_Of_true"                                                                                                           ) (SeLFiE_Assertion.test_Is_Subprint_Of_true                                                                                                           , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "test_Is_Subprint_Of_false"                                                                                                          ) (SeLFiE_Assertion.test_Is_Subprint_Of_false                                                                                                          , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "test_Is_Case_Distinct_Of_Trm_With_A_Case"                                                                                           ) (SeLFiE_Assertion.test_Is_Case_Distinct_Of_Trm_With_A_Case                                                                                           , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "test_Is_Let_X_Be_Y_In_X"                                                                                                            ) (SeLFiE_Assertion.test_Is_Let_X_Be_Y_In_X                                                                                                            , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Induction_Heuristic,      "outer_induct_on_arg_of_set_member_n_set_outer"                                                                                      ) (SeLFiE_Assertion.outer_induct_on_arg_of_set_member_n_set_outer                                                                                      , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Induction_Heuristic,      "induct_on_arg_of_set_member_n_set_syntax_only"                                                                                      ) (SeLFiE_Assertion.induct_on_arg_of_set_member_n_set_syntax_only                                                                                      , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Induction_Heuristic,      "induct_on_2nd_arg_of_map_outer"                                                                                                     ) (SeLFiE_Assertion.induct_on_2nd_arg_of_map_outer                                                                                                     , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Induction_Heuristic,      "structural_induction_on_an_arg_of_inductive_defined_constant_in_the_concl_of_meta_imp"                                              ) (SeLFiE_Assertion.structural_induction_on_an_arg_of_inductive_defined_constant_in_the_concl_of_meta_imp                                              , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,(*no good*)"structural_induction_on_nt_arg_of_inductively_defined_constant_in_the_concl_of_meta_imp_if_nth_arg_shrinks_in_def_of_constant_outer") (SeLFiE_Assertion.structural_induction_on_nt_arg_of_inductively_defined_constant_in_the_concl_of_meta_imp_if_nth_arg_shrinks_in_def_of_constant_outer, 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "generalize_all_free_var_not_inducted_on" (*bad*)                                                                                    ) (SeLFiE_Assertion.generalize_all_free_var_not_inducted_on                                                                                            , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Induction_Heuristic,      "rule_inversion_using_the_deepest_const"                                                                                             ) (SeLFiE_Assertion.rule_inversion_using_the_deepest_const                                                                                             , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Induction_Heuristic,      "complex_lhs_causes_functional_induction_outer"                                                                                      ) (SeLFiE_Assertion.complex_lhs_causes_functional_induction_outer                                                                                      , 2) \<close>
setup\<open> Apply_SeLFiE.update_assert (Induction_Heuristic,      "is_defined_recursively_on_nth_n_mth_by_two_funs"                                                                                    ) (SeLFiE_Assertion.is_defined_recursively_on_nth_n_mth_by_two_funs                                                                                    , 2) \<close>
setup\<open> Apply_SeLFiE.update_assert (Generalization_Heuristic, "if_rule_induction_then_no_generalization"                                                                                           ) (SeLFiE_Assertion.if_rule_induction_then_no_generalization                                                                                           , 3) \<close>
(*setup\<open> Apply_SeLFiE.update_assert (Induction_Heuristic,      "function_induction_only_if_there_is_a_complex_lhs"                                                                                  ) (SeLFiE_Assertion.function_induction_only_if_there_is_a_complex_lhs                                                                                , 2) \<close>*)
setup\<open> Apply_SeLFiE.update_assert (Induction_Heuristic,      "if_part_of_lhs_n_part_of_rhs_of_eq_is_induct_rule_then_induct_rule_on_part_of_lhs"                                                  ) (SeLFiE_Assertion.if_part_of_lhs_n_part_of_rhs_of_eq_is_induct_rule_then_induct_rule_on_part_of_lhs                                                  , 2) \<close>
setup\<open> Apply_SeLFiE.update_assert (Induction_Heuristic,      "all_ind_should_be_atom"                                                                                                             ) (SeLFiE_Assertion.all_ind_should_be_atom                                                                                                             , 2) \<close>

end