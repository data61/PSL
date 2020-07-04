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
  keywords "assert_SeLFiE_true"      :: diag
  and      "assert_SeLFiE_false"     :: diag
(*
   and     "test_all_LiFtErs"   :: diag
*)
begin

ML\<open>
val d = ~~; ["a","b"];
\<close>
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
ML_file "Apply_SeLFiE.ML"

definition "func x \<equiv> x"
thm func_def
ML\<open>
val meta_eq  = @{term "True \<Longrightarrow> (x \<equiv> y)"}
val hol_eq   = @{term  "True \<Longrightarrow> (x = y)"}
val hol_imp  = @{term  "f (x \<longrightarrow> y)"}
val meta_imp = @{term  "f (x \<Longrightarrow> y)"}
\<close>
ML\<open>
val meta_eq_hol_eq = @{term "(x = y) \<Longrightarrow> (z \<equiv> w)"}
val meta_imp = @{term "1"};
val meta_imply = @{term "True \<Longrightarrow> True"};
val meta_imply = @{term "True \<Longrightarrow> (False \<equiv> x)"};
val meta_imply = @{term "(x \<Longrightarrow> y) \<Longrightarrow> (z \<longrightarrow> w)"};
val func_thm   = @{thm func_def};
val func_term  = Thm.cprop_of func_thm |> Thm.term_of;

val eq = @{term "1 \<equiv> 1"};
val eq2 = Isabelle_Utils.flatten_trm eq |> (fn trms => nth trms 0);
Isabelle_Utils.trm_to_string @{context} eq2
\<close>

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
setup\<open> Apply_SeLFiE.update_assert (Induction_Heuristic,      "lifter_2"                                                                                                                           ) (SeLFiE_Assertion.lifter_2                                                                                                                           , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Induction_Heuristic,      "lifter_3"                                                                                                                           ) (SeLFiE_Assertion.lifter_3                                                                                                                           , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "lifter_4"     (*not good enough for smart_induction_2 because it is based solely on pattern-matching on the LHS*)                   ) (SeLFiE_Assertion.lifter_4                                                                                                                           , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Induction_Heuristic,      "lifter_5"     (*may be obsolete due to smart_construction, may be harmful for lacking generalization *)                             ) (SeLFiE_Assertion.lifter_5                                                                                                                           , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Generalization_Heuristic, "lifter_6"                                                                                                                           ) (SeLFiE_Assertion.lifter_6                                                                                                                           , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Induction_Heuristic,      "lifter_7"                                                                                                                           ) (SeLFiE_Assertion.lifter_7                                                                                                                           , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Induction_Heuristic,      "lifter_8"                                                                                                                           ) (SeLFiE_Assertion.lifter_8                                                                                                                           , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "lifter_9"                                                                                                                           ) (SeLFiE_Assertion.lifter_9                                                                                                                           , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Induction_Heuristic,      "lifter_9_improved"                                                                                                                  ) (SeLFiE_Assertion.lifter_9_improved                                                                                                                  , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Generalization_Heuristic, "lifter_10"                                                                                                                          ) (SeLFiE_Assertion.lifter_10                                                                                                                          , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Induction_Heuristic,      "lifter_11"    (*may be harmful*)                                                                                                    ) (SeLFiE_Assertion.lifter_11                                                                                                                          , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Generalization_Heuristic, "lifter_12"                                                                                                                          ) (SeLFiE_Assertion.lifter_12                                                                                                                          , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Generalization_Heuristic, "lifter_13"    (*may be harmful: no arbitrary is at the same relative location as induction in terms of a function*)                 ) (SeLFiE_Assertion.lifter_13                                                                                                                          , 1) \<close>
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
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "is_defined_recursively_on_nth"                                                                                                      ) (SeLFiE_Assertion.is_defined_recursively_on_nth_outer                                                                                                , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Generalization_Heuristic, "generalize_arguments_used_in_recursion"                                                                                             ) (SeLFiE_Assertion.generalize_arguments_used_in_recursion                                                                                             , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Generalization_Heuristic, "for_all_arbs_there_should_be_a_change"                                                                                              ) (SeLFiE_Assertion.for_all_arbs_there_should_be_a_change                                                                                              , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "for_all_arbs_there_should_be_a_change_simplified_for_presentation"                                                                  ) (SeLFiE_Assertion.for_all_arbs_there_should_be_a_change_simplified_for_presentation                                                                  , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Generalization_Heuristic, "ind_on_lhs_of_eq_then_arb_on_rhs_of_eq"                                                                                             ) (SeLFiE_Assertion.ind_on_lhs_of_eq_then_arb_on_rhs_of_eq                                                                                             , 1) \<close>
setup\<open> Apply_SeLFiE.update_assert (Test_Heuristic,           "if_part_of_lhs_n_part_of_rhs_of_eq_is_induct_then_induct_on_part_of_lhs"                                                            ) (SeLFiE_Assertion.if_part_of_lhs_n_part_of_rhs_of_eq_is_induct_then_induct_on_part_of_lhs                                                            , 1) \<close>
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

lemma "f x \<Longrightarrow> g y \<Longrightarrow> h z"
  assert_SeLFiE_true test_is_a_meta_premise    [on["f x"], arb[],rule[]]
  assert_SeLFiE_true test_is_a_meta_conclusion [on["h z"], arb[],rule[]]
  assert_SeLFiE_true test_is_a_meta_premise_or_below    [on["x"], arb[],rule[]]
  assert_SeLFiE_true test_is_a_meta_conclusion_or_below [on["z"], arb[],rule[]]
  assert_SeLFiE_true test_is_more_than [on["zs"], arb[],rule[]]
  assert_SeLFiE_false test_Is_If_Then_Else [on["zs"], arb[],rule[]]
  assert_SeLFiE_false test_Is_If_Then_Else [on["x"], arb[],rule[]]
  assert_SeLFiE_false test_Is_Case_Distinct_Of_Trm_With_A_Case [on["zs"], arb[],rule[]]
  oops

lemma "if x then True else False"
  assert_SeLFiE_true  test_Is_If_Then_Else [on["x"], arb[],rule[]]
  oops

lemma "case x of [y] \<Rightarrow> y | _ \<Rightarrow> False"
  assert_SeLFiE_true  test_Is_Case_Distinct_Of_Trm_With_A_Case [on["zs"], arb[],rule[]]
  assert_SeLFiE_false test_Is_Let_X_Be_Y_In_X [on["zs"], arb[],rule[]]
  oops

lemma "let (x1, x2) = y in z < x1"
  assert_SeLFiE_true test_Is_Let_X_Be_Y_In_X [on["zs"], arb[],rule[]]
  oops

primrec rev :: "'a list \<Rightarrow> 'a list" where
  "rev []       = []" |
  "rev (x # xs) = rev xs @ [x]"
 print_theorems

 fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev []     ys = ys" |
  "itrev (x#xs) ys = itrev xs (x#ys)"
 print_theorems

lemma "itrev xs ys = rev xs @ ys"
  assert_SeLFiE_true  generalize_arguments_used_in_recursion [on["xs"], arb["ys"],rule[]](*It used to take 1.196s elapsed time*)
  assert_SeLFiE_false generalize_arguments_used_in_recursion [on["xs"], arb["xs"],rule[]](*It used to take 2.467s elapsed time*)
  assert_SeLFiE_false generalize_arguments_used_in_recursion [on["xs"], arb[    ],rule[]](*It used to take 0.864s elapsed time*)
  assert_SeLFiE_true  for_all_arbs_there_should_be_a_change  [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE_false for_all_arbs_there_should_be_a_change  [on["xs"], arb["xs"],rule[]]
  assert_SeLFiE_true  for_all_arbs_there_should_be_a_change_simplified_for_presentation [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE_false for_all_arbs_there_should_be_a_change_simplified_for_presentation [on["xs"], arb["xs"],rule[]]
  assert_SeLFiE_true  for_all_arbs_there_should_be_a_change  [on["xs"], arb[],rule[]](*unfortunate result due to the universal quantifier.*)
  assert_SeLFiE_true  is_defined_recursively_on_nth  [on["xs"], arb["ys"],rule[]](*It used to take 0.703s elapsed time*)
  assert_SeLFiE_false is_defined_recursively_on_nth  [on["ys"], arb[],rule[]](*It used to take 1.647s elapsed time*)
  assert_SeLFiE_true heuristic_1  [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE_true heuristic_2  [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE_true heuristic_3  [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE_true heuristic_4  [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_true heuristic_5  [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE_true heuristic_6  [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE_true heuristic_7  [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE_true heuristic_8  [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE_true heuristic_9  [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE_true heuristic_10 [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE_true heuristic_11 [on["xs"], arb["ys"],rule[]]
  assert_SeLFiE_true heuristic_12 [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_true heuristic_13 [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_true heuristic_14 [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_true test_dive_in  [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_true print_all_outer_prints [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_true print_all_inner_prints [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_true print_all_unodes       [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_true print_outer_path_root  [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_true lifter_4  [on["xs"], arb["ys"], rule[]]
  assert_SeLFiE_true lifter_5  [on["xs","ys"], arb[], rule["itrev.induct"]]
  assert_SeLFiE_true lifter_6  [on["xs"], arb["ys"], rule[]]
  assert_SeLFiE_true lifter_7  [on["xs"], arb["ys"], rule[]]
  assert_SeLFiE_true lifter_8  [on["xs"], arb["ys"], rule[]]
  assert_SeLFiE_true lifter_9  [on["xs"], arb["ys"], rule[]]
  assert_SeLFiE_true lifter_10  [on["xs"], arb["ys"], rule[]]
  assert_SeLFiE_true lifter_11  [on["xs","ys"], arb[], rule["itrev.induct"]]
  assert_SeLFiE_true lifter_12  [on["xs"], arb["ys"], rule["itrev.induct"]]
  assert_SeLFiE_true lifter_15  [on["xs"], arb["ys"], rule["rev.induct"]]
  assert_SeLFiE_true lifter_13  [on["xs"], arb["ys"], rule["itrev.induct"]]
  assert_SeLFiE_true lifter_14  [on["xs"], arb["ys"], rule["itrev.induct"]]
  assert_SeLFiE_true print_fst_params_of_fun_const [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_true print_inner_roots      [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_true print_all_inner_lhss   [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_true lifter_1  [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_true lifter_1b [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_true lifter_2  [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_true lifter_3  [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_true  test_Is_Subprint_Of_true  [on["xs"], arb["ys"],rule["itrev.induct"]]
  assert_SeLFiE_false test_Is_Subprint_Of_false  [on["xs"], arb["ys"],rule["itrev.induct"]]
  apply(induct xs arbitrary: ys) apply auto done

(* auxiliary stuff *)
ML\<open>
@{term "let x = 1 in x"};
(*
  Const ("HOL.Let", "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a")
$ Const ("Groups.one_class.one", "'a")
$ Abs   ("x", "'a", Bound 0): term
*)

@{term "let x = 1 + y in x"};
(*
  Const ("HOL.Let", "'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a")
$(  Const ("Groups.plus_class.plus", "'a \<Rightarrow> 'a \<Rightarrow> 'a")
  $ Const ("Groups.one_class.one", "'a")
  $ Free ("y", "'a")
 )
$ Abs   ("x", "'a", Bound 0)
*)

@{term "\<lambda>x. x + 1"};
@{term "case x of [] => y | _ \<Rightarrow> z"};
(*
  Const ("List.list.case_list", "'a \<Rightarrow> ('b \<Rightarrow> 'b list \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 'a")
$ Free  ("y", "'a")
$ Abs   ("a", "'b", Abs ("list", "'b list", Free ("z", "'a")))
$ Free  ("x", "'b list")
*)

@{term "case x of [] => y | w#ws \<Rightarrow> z"};
(*
  Const ("List.list.case_list", "'a \<Rightarrow> ('b \<Rightarrow> 'b list \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 'a")
$ Free  ("y", "'a")
$ Abs   ("w", "'b", Abs ("ws", "'b list", Free ("z", "'a")))
$ Free  ("x", "'b list"):
*)

@{term "case x of [] => y | w#ws \<Rightarrow> w"};
(*
  Const ("List.list.case_list", "'a \<Rightarrow> ('a \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a")
$ Free  ("y", "'a")
$ Abs   ("w", "'a", Abs ("ws", "'a list", Bound 1))
$ Free  ("x", "'a list")
*)

@{term "case x of True => y | _ \<Rightarrow> z"}
(*
  Const ("Product_Type.bool.case_bool", "'a \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> 'a")
$ Free  ("y", "'a")
$ Free  ("z", "'a")
$ Free  ("x", "bool")
*)

(*
Is_Case = name has a string "case" as its sub-string
  and it it takes n arguments, (n-1)th argument's type name is part of the constant name..;
Is_Maybe_Bound_Of_Case;
*)
\<close>
find_consts name:"case_list"
find_consts name:"Product_Type.bool.case_bool"
find_theorems name:"case" name:"bool"
find_theorems name:"List.list"
thm List.list.case
(*
datatype alpha = A | B | C | D
ML\<open>
@{term "case x of A \<Rightarrow> True | B \<Rightarrow> False"};
(*
   Const ("SeLFiE.alpha.case_alpha", "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> alpha \<Rightarrow> bool")
 $ Const ("HOL.True", "bool")
 $ Const ("HOL.False", "bool")
 $ Const ("HOL.undefined", "bool")
 $ Const ("HOL.undefined", "bool")
 $ Free ("x", "alpha"):
 term


  Const ("LiFtEr.alpha.case_alpha", "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> alpha \<Rightarrow> 'a")
$ Free  ("a", "'a")
$ Free  ("b", "'a")
$ Const ("HOL.undefined", "'a")
$ Const ("HOL.undefined", "'a")
$ Free  ("x", "alpha")
*)
\<close>
*)
ML\<open>
(*
@{term "case x of B \<Rightarrow> False | A \<Rightarrow> True "};
*)
(*
  Const ("SeLFiE.alpha.case_alpha", "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> alpha \<Rightarrow> bool")
$ Const ("HOL.True", "bool")
$ Const ("HOL.False", "bool")
$ Const ("HOL.undefined", "bool")
$ Const ("HOL.undefined", "bool")
$ Free ("x", "alpha")
: term
*)
\<close>
declare[[ML_print_depth=100]]
ML\<open>
@{term "case x of [x] \<Rightarrow> False | [] \<Rightarrow> True | x#xs \<Rightarrow> True"};
(*
  Const ("List.list.case_list", "bool \<Rightarrow> ('a \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool")
$ Const ("HOL.True", "bool")
$ Abs ("x", "'a",
    Abs ("xs",
         "'a list",
           Const ("List.list.case_list", "bool \<Rightarrow> ('a \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool")
         $ Const ("HOL.False", "bool")
         $ Abs ("a", "'a",
             Abs ("list", "'a list",
               Const ("HOL.True", "bool")
             )
           )
         $ Bound 0
    )
  )
$ Free ("x", "'a list")
: term
*)
\<close>

ML\<open>
@{term "case x of [] \<Rightarrow> True | x#xs \<Rightarrow> False"};
(*
  Const ("List.list.case_list", "bool \<Rightarrow> ('a \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool")
$ Const ("HOL.True", "bool")
$ Abs ("x", "'a", Abs ("xs", "'a list", Const ("HOL.False", "bool")))
$ Free ("x", "'a list")
: term
*)
\<close>

ML\<open>
@{term "List.list.case_list"};
Isabelle_Utils.count_numb_of_args_of_fun_typ;

fun count_numb_of_args_of_fun_typ' (fun_typ:typ) (acc:int) = case try dest_funT fun_typ of
  NONE => acc
| SOME (_(*domain_typ*), range_typ) => count_numb_of_args_of_fun_typ' range_typ (acc + 1);

fun count_numb_of_args_of_fun_typ (typ:typ) = count_numb_of_args_of_fun_typ' typ 0;

@{term "List.null"};
dest_Const @{term "List.null"} |> snd |> dest_funT;

@{term "List.nth"};
dest_Const @{term "List.nth"} |> snd |> dest_funT |> snd |> dest_funT;

local

fun get_fist_type (fun_typ:typ) =
    let
      val (first_typ, _) = dest_funT fun_typ;
    in
      first_typ
    end;

fun remove_first_n_minus_one_typs (fun_typ:typ) (0:int) = fun_typ
  | remove_first_n_minus_one_typs (fun_typ:typ) (n:int) =
    let
      val (_, tail_fun_typ) = dest_funT fun_typ;
    in
      remove_first_n_minus_one_typs tail_fun_typ (n - 1)
    end;

in

fun fun_typ_to_typ_of_nth_arg (fun_typ:typ) (n:int) = (get_fist_type oo remove_first_n_minus_one_typs) fun_typ n;

end;

fun_typ_to_typ_of_nth_arg ((snd o dest_Const) @{term "List.list.case_list"}) 1
\<close>

ML\<open>
@{term "case x of x#xs \<Rightarrow> False | [] \<Rightarrow> True"};
(*
  Const ("List.list.case_list", "bool \<Rightarrow> ('a \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool")
$ Const ("HOL.True", "bool")
$ Abs ("x", "'a", Abs ("xs", "'a list", Const ("HOL.False", "bool")))
$ Free ("x", "'a list")
: term
*)
\<close>

ML\<open>
@{term "case [] of x#xs \<Rightarrow> False | [] \<Rightarrow> True"};
(*
  Const ("List.list.case_list", "bool \<Rightarrow> ('a \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool")
$ Const ("HOL.True", "bool")
$ Abs ("x", "'a", Abs ("xs", "'a list", Const ("HOL.False", "bool")))
$ Const ("List.list.Nil", "'a list"): term
*)
\<close>

ML\<open>
@{term "case f x of x#xs \<Rightarrow> False | [] \<Rightarrow> True"};
(*
  Const ("List.list.case_list", "bool \<Rightarrow> ('a \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool")
$ Const ("HOL.True", "bool")
$ Abs ("x", "'a", Abs ("xs", "'a list", Const ("HOL.False", "bool")))
$ (Free ("f", "'b \<Rightarrow> 'a list") $ Free ("x", "'b")): term
*);
\<close>

ML\<open>
@{term "let ((x1,  x2),  x3) = (y1, y2) in (y1, x3)"};
(*
val it =
   Const ("HOL.Let", "'a \<times> 'b \<times> 'c \<Rightarrow> ('a \<times> 'b \<times> 'c \<Rightarrow> 'a \<times> 'c) \<Rightarrow> 'a \<times> 'c")
$ (Const ("Product_Type.Pair", "'a \<Rightarrow> 'b \<times> 'c \<Rightarrow> 'a \<times> 'b \<times> 'c")
  $ Free ("y1", "'a")
  $ Free ("y2", "'b \<times> 'c"))
$ (Const ("Product_Type.prod.case_prod", "('a \<Rightarrow> 'b \<times> 'c \<Rightarrow> 'a \<times> 'c) \<Rightarrow> 'a \<times> 'b \<times> 'c \<Rightarrow> 'a \<times> 'c")
  $ Abs ("x1", "'a",
      Const ("Product_Type.prod.case_prod", "('b \<Rightarrow> 'c \<Rightarrow> 'a \<times> 'c) \<Rightarrow> 'b \<times> 'c \<Rightarrow> 'a \<times> 'c")
     $ Abs ("x2", "'b",
         Abs ("x3", "'c",
           Const ("Product_Type.Pair", "'a \<Rightarrow> 'c \<Rightarrow> 'a \<times> 'c")
          $ Free ("y1", "'a")
          $ Bound 0
         )
       )
    )
  )

: term
Is_Let_X_Be_Y_In_Z.
Again, we have to count the number of Abs.
X_Is_Let_Z_Be_Y_In_Z.
*)
@{term "Product_Type.Pair"};
dest_funT;
\<close>

ML\<open>
@{term "let x = y in z"};
@{term "(x = y)"};
Name.skolem;
Variable.names_of;
Variable.add_fixes;
type asdf = term;


\<close>

schematic_goal "?x = ?x"
  apply(tactic \<open>fn x => (
let
  val fst_subg = try (hd o Thm.prems_of) x: term option;
  val _        = if length (Thm.prems_of x) = 0 then tracing "empty" else tracing "no empty";
  
  val _ = Option.map (tracing o Isabelle_Utils.trm_to_string @{context}) (fst_subg);

  val _ = if Utils.is_some_true (Option.map (exists_subterm (is_Var)) fst_subg)
          then tracing "Yes Var!"
          else tracing "No Var!"
  val _ = if Utils.is_some_true (Option.map (exists_subterm (is_Bound)) fst_subg)
          then tracing "Yes Bound!"
          else tracing "No Bound!"

in
  Seq.single x
end) \<close>)
  oops

end