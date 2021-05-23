(*  Title:      PSL/SeLFiE/src/Interface/SeLFiE_Assertion.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
(*** signature: ASSERTION_TEST ***)
signature ASSERTION_TEST =
sig

val heuristic_1                                                         : Eval_Syntactic_Sugar.assert;
val heuristic_2                                                         : Eval_Syntactic_Sugar.assert;
val heuristic_3                                                         : Eval_Syntactic_Sugar.assert;
val heuristic_4                                                         : Eval_Syntactic_Sugar.assert;
val heuristic_5                                                         : Eval_Syntactic_Sugar.assert;
val heuristic_6                                                         : Eval_Syntactic_Sugar.assert;
val heuristic_7                                                         : Eval_Syntactic_Sugar.assert;
val heuristic_8                                                         : Eval_Syntactic_Sugar.assert;
val heuristic_9                                                         : Eval_Syntactic_Sugar.assert;
val heuristic_10                                                        : Eval_Syntactic_Sugar.assert;
val heuristic_11                                                        : Eval_Syntactic_Sugar.assert;
val heuristic_12                                                        : Eval_Syntactic_Sugar.assert;
val heuristic_13                                                        : Eval_Syntactic_Sugar.assert;
val heuristic_14                                                        : Eval_Syntactic_Sugar.assert;
val lifter_1                                                            : Eval_Syntactic_Sugar.assert;
val lifter_1b                                                           : Eval_Syntactic_Sugar.assert;
val lifter_2                                                            : Eval_Syntactic_Sugar.assert;
val lifter_3                                                            : Eval_Syntactic_Sugar.assert;
val lifter_4                                                            : Eval_Syntactic_Sugar.assert;
val lifter_9                                                            : Eval_Syntactic_Sugar.assert;
val lifter_13                                                           : Eval_Syntactic_Sugar.assert;
val lifter_14                                                           : Eval_Syntactic_Sugar.assert;
val test_dive_in                                                        : Eval_Syntactic_Sugar.assert;
val print_all_outer_prints                                              : Eval_Syntactic_Sugar.assert;
val print_all_inner_prints                                              : Eval_Syntactic_Sugar.assert;
val print_all_unodes                                                    : Eval_Syntactic_Sugar.assert;
val print_outer_path_root                                               : Eval_Syntactic_Sugar.assert;
val print_inner_roots                                                   : Eval_Syntactic_Sugar.assert;
val print_all_inner_lhss                                                : Eval_Syntactic_Sugar.assert;
val print_fst_params_of_fun_const                                       : Eval_Syntactic_Sugar.assert;
val test_is_a_meta_premise                                              : Eval_Syntactic_Sugar.assert;
val test_is_a_meta_conclusion                                           : Eval_Syntactic_Sugar.assert;
val test_is_a_meta_premise_or_below                                     : Eval_Syntactic_Sugar.assert;
val test_is_a_meta_conclusion_or_below                                  : Eval_Syntactic_Sugar.assert;
val test_is_more_than                                                   : Eval_Syntactic_Sugar.assert;
val for_all_arbs_there_should_be_a_change_simplified_for_presentation   : Eval_Syntactic_Sugar.assert;
val test_Is_If_Then_Else                                                : Eval_Syntactic_Sugar.assert;
val test_Is_Subprint_Of_true                                            : Eval_Syntactic_Sugar.assert;
val test_Is_Subprint_Of_false                                           : Eval_Syntactic_Sugar.assert;
val test_Is_Case_Distinct_Of_Trm_With_A_Case                            : Eval_Syntactic_Sugar.assert;
val test_Is_Let_X_Be_Y_In_X                                             : Eval_Syntactic_Sugar.assert;
val (*not good*)structural_induction_on_nt_arg_of_inductively_defined_constant_in_the_concl_of_meta_imp_if_nth_arg_shrinks_in_def_of_constant_outer   : Eval_Syntactic_Sugar.assert;
val (*bad*)generalize_all_free_var_not_inducted_on                      : Eval_Syntactic_Sugar.assert;

end;

(*** structure: Assertion_Test ***)
structure Assertion_Test: ASSERTION_TEST =
struct

open SeLFiE_Util;
open Eval_Syntactic_Sugar;
open Definition_Pattern;

val heuristic_1 =
  Ands
   [Applies (Lambdas (["x","y","z","w"], Variable "y"), [False, True, False, False]),
    True]

val heuristic_2 =
 Not (Some ("x", QRule, True))

val heuristic_3 =
 All ("x", QInd,
  Some ("x", QOuter_Print, True))

val heuristic_4 =
 (Some ("x", QRule, True))

val heuristic_5 =
 (Some ("x", QInd, True))

val heuristic_6 =
 (Some ("x", QArb, True))

val heuristic_7 =
 (All ("x", QOuter_Print,
   Are_Same_Prints (Print "Test_SeLFiE.itrev", Print "Test_SeLFiE.itrev")))

val heuristic_8 =
 Applies (
  Lambdas (["x"], 
           Are_Same_Prints (Variable "x", Print "Test_SeLFiE.itrev")),
  [Print "Test_SeLFiE.itrev"]);

val heuristic_9 =
 (Some ("x", QOuter_Path,
   Unode_Has_Print (Variable "x", Print "ys")));;

val heuristic_10 =
 Not
  (Some ("x", QOuter_Path,
   Unode_Has_Print (Variable "x", Print "yss")));

val heuristic_11 =
 (Some ("x", QOuter_Path,
   Unode_Has_Print (Variable "x", Print "Test_SeLFiE.itrev")));

val heuristic_12 =
  Some ("induct", QInd,
    Are_Same_Prints (Variable "induct", Print "xs"));

val heuristic_13 =
  Not (
    Some ("induct", QArb,
      Are_Same_Prints (Variable "induct", Print "xs")));

val heuristic_14 =
  Some ("var_occ2", QOuter_Path,
  Some ("var_occ1", QOuter_Path,
  Some ("var_occ", QOuter_Path,
    Has_Same_Prnt_As (Variable "var_occ2",  Variable "var_occ")
  )));(*TODO: double-check this heuristic. It does not make much sense, I think. \<rightarrow> Ah. I wrote this just to test the interpreter.*)

val lifter_1 =
All ("induct", QInd,
  Some ("var_occ", QOuter_Path,
    Ands [
      Not (Node_Is_Cnst (Variable "var_occ")),
      Unode_Has_Print (Variable "var_occ", Variable "induct")
    ]
  )
);

val lifter_1b =
All ("induct", QInd,
  Some_Of ("var_occ", Variable "induct",
      Not (Node_Is_Cnst (Variable "var_occ"))));

val lifter_2 =
All ("xs", QInd,
  Some_Of ("xs_occ", Variable "xs",
    Imply (
      Is_Atomic (Variable "xs_occ"),
      Is_At_Deepest_In_A_Location (Variable "xs_occ")
    )
  )
);

val node_defined_recursively =
Lambdas (["func_occ"],
  Ors [
    Node_Is_Defined_With (Variable "func_occ", Command Fun),
    Node_Is_Defined_With (Variable "func_occ", Command Function),
    Node_Is_Defined_With (Variable "func_occ", Command Primrec)
  ]
);

val lifter_3 =
Some ("func_occ", QOuter_Path,
  Ands [
    Applies (node_defined_recursively, [Variable "func_occ"]),
    All ("ind", QInd,
      Some_Of ("ind_occ", Variable "ind",
        Ands [
          Is_An_Argument_Of (Variable "ind_occ", Variable "func_occ")
        ]
      )
    )
  ]
);

val print_outer_path_root =
All ("outpath", QOuter_Path,
  Imply (
    Is_Root_In_A_Location (Variable "outpath"),
    Debug_Print_Unode (Variable "outpath"))
  );

val print_inner_path_root_help =
Lambdas (["outer_print"],
  Some ("inner_path", QInner_Path,
    Ands [
      Is_Root_In_A_Location (Variable "inner_path"),
      Debug_Print_Unode (Variable "inner_path")
    ]
  )
);

local

val help_lifter_4_nth_arg_is_const_or_app =
Lambdas (["number"],
  Some ("root_path", QInner_Path,
    Ands [
      Is_Root_In_A_Location (Variable "root_path"),
      Some ("lfs_path", QInner_Path,
        Ands [
          Is_Nth_Child_Of (Variable "lfs_path", Number 1, Variable "root_path"),
          Some ("nth_param", QInner_Path,
            Ands [
              Node_Takes_Less_Than_N_Arguments (Variable "lfs_path", Variable "number"),
              Is_N_Plus_One_th_Child_Of (Variable "nth_param", Variable "number", Variable "lfs_path"),
              Ors [
                Node_Is_Cnst (Variable "nth_param"),
                Node_Is_App  (Variable "nth_param")
              ]
            ]
          )
        ]
      )
    ]
  )
);

val print_defined_recursively =
Lambdas (["func_trm"],
  Ors [
    Print_Is_Defined_With (Variable "func_trm", Command Fun),
    Print_Is_Defined_With (Variable "func_trm", Command Function),
    Print_Is_Defined_With (Variable "func_trm", Command Primrec)
  ]
);

in

val lifter_4 =
Imply (
  Not (Some ("rule", QRule, True)),
  Some ("func", QOuter_Print,
    Ands [
      Applies (print_defined_recursively, [Variable "func"]),
      Some_Of ("func_occ", Variable "func",
        Ands [
          All ("induct", QInd,
            Some_Of ("ind_occ", Variable "induct",
              All ("number", QOuter_Number,
                Imply (
                  Ands [
                    Node_Takes_Less_Than_N_Arguments (Variable "func_occ", Variable "number"),
                    Is_Nth_Argument_Of (Variable "ind_occ", Variable "number", Variable "func_occ")
                  ],
                  Ands [
                    Debug_Non_Path_Literal (Print "Now we dive in: "),
                    In_All_Definitions (Variable "func_occ", help_lifter_4_nth_arg_is_const_or_app, [Variable "number"])
                  ]
                )
              )
            )
          )
        ]
      )
    ]
  )
);

end

val lifter_9 =
Imply (
  Some ("induct_arg", QInd, True),
  Some ("induct_arg", QInd,
    Some_Of ("induct_arg_occ", Variable "induct_arg",
      Is_At_Deepest_In_A_Location (Variable "induct_arg_occ")
    )
  )
);

(*no arbitrary is at the same relative location as induction in terms of a function*)
val lifter_13 =
Imply (
  Some ("arb", QArb, True),
  All ("arb", QArb,
    Not
      (Some_Of ("arb_occ", Variable "arb",
         Some ("func", QOuter_Print,
           Some_Of ("func_occ1", Variable "func",
             Some ("number", QOuter_Number,
               Ands [
                 Is_Nth_Argument_Of (Variable "arb_occ", Variable "number", Variable "func_occ1"),
                 Some ("ind", QInd,
                   Some_Of ("ind_occ", Variable "ind",
                     Some_Of ("func_occ2", Variable "func",
                       Is_Nth_Argument_Of (Variable "ind_occ", Variable "number", Variable "func_occ2")
                     )
                   )
                 )
               ]
             )
           )
         )
       )
      )
  )
);

(*only one rule*)
val lifter_14 =
Imply (
  Some ("rule", QRule, True),
  All ("rule1", QRule,
    All ("rule2", QRule,
      Are_Same_Prints (Variable "rule1", Variable "rule2")
    )
  )
);

val help_test_dive_in =
 Lambdas (["func"],
  All ("printed", QInner_Print,
   Debug_Non_Path_Literal (Variable "printed")));

val test_dive_in =
All ("func_occ", QOuter_Path,
  Imply (
    Node_Is_Defined_With (Variable "func_occ", Command Fun),
    All ("func", QOuter_Print,
      Imply (
        Unode_Has_Print (Variable "func_occ", Variable "func"),
        In_All_Definitions (Variable "func", help_test_dive_in, [Variable "func"])
      )
    )
  )
);

val print_all_inner_prints_helper =
Lambdas (["outer_print"],
 All ("printed", QInner_Print,
  Debug_Non_Path_Literal (Variable "printed")));

val print_all_inner_prints =
  All ("outer_print", QOuter_Print,
    In_All_Definitions (Variable "outer_print", print_all_inner_prints_helper, [Print "outer_print"]));

val print_all_outer_prints =
All ("printed", QOuter_Print,
  Debug_Non_Path_Literal (Variable "printed"));

val print_all_unodes =
All ("unode", QOuter_Path,
  Debug_Print_Unode (Variable "unode"));

val print_inner_roots =
All ("outer_path", QOuter_Path,
  Some ("outer_print", QOuter_Print,
    Ands [
      Unode_Has_Print (Variable "outer_path", Variable "outer_print"),
      In_All_Definitions (Variable "outer_print", print_inner_path_root_help, [Variable "outer_print"])
    ]
  )
);

local

val help_print_inner_lhs =
Lambdas (["outer_print"],
  Some ("root_path", QInner_Path,
    Ands [
      Is_Root_In_A_Location (Variable "root_path"),
      Some ("lfs_path", QInner_Path,
        Ands [
          Is_Nth_Child_Of (Variable "lfs_path", Number 1, Variable "root_path"),
          Debug_Print_Unode (Variable "lfs_path")
        ]
      )
    ]
  )
);

in

val print_all_inner_lhss =
All ("outer_path", QOuter_Path,
  Some ("outer_print", QOuter_Print,
    Ands [
      Unode_Has_Print (Variable "outer_path", Variable "outer_print"),
      In_All_Definitions (Variable "outer_print", help_print_inner_lhs, [Variable "outer_print"])
    ]
  )
);

end

local

val help_print_n_plus_one_th_param =
Lambdas (["number"],
  Some ("root_path", QInner_Path,
    Ands [
      Is_Root_In_A_Location (Variable "root_path"),
      Some ("lfs_path", QInner_Path,
        Ands [
          Is_Nth_Child_Of (Variable "lfs_path", Number 1, Variable "root_path"),
          Some ("fst_param", QInner_Path,
            Ands [
              Is_N_Plus_One_th_Child_Of (Variable "fst_param", Variable "number", Variable "lfs_path")
            ]
          )
        ]
      )
    ]
  )
);

in

val print_fst_params_of_fun_const =
Some ("outer_path", QOuter_Path,
  Some ("outer_print", QOuter_Print,
    Ands [
      Unode_Has_Print (Variable "outer_path",  Variable "outer_print"),
      Node_Is_Defined_With (Variable "outer_path", Command Fun),
      In_All_Definitions (Variable "outer_print", help_print_n_plus_one_th_param, [Number 0])
      ]));

end;

val test_is_a_meta_premise =
  All ("ind", QInd,
    Some_Of ("ind_occ", Variable "ind",
      Is_A_Meta_Premise (Variable "ind_occ")
    )
  );

val test_is_a_meta_conclusion =
  All ("ind", QInd,
    Some_Of ("ind_occ", Variable "ind",
      Is_A_Meta_Conclusion (Variable "ind_occ")
    )
  );

val test_is_more_than = Is_More_Than (Number 5, Number 4);

local

(*defined_recursively*)
val print_defined_recursively =
Lambdas (["func_trm"],
  Ors [
    Print_Is_Defined_With (Variable "func_trm", Command Fun),
    Print_Is_Defined_With (Variable "func_trm", Command Function),
    Print_Is_Defined_With (Variable "func_trm", Command Primrec)(*,
    Print_Is_Defined_With (Variable "func_trm", Command Inductive)*)
  ]
);

val is_lhs_of_root =(*TODO: we do not need root here.*)
Lambdas (["lhs_path", "root_path"],
  Ands [
    Is_Root_In_A_Location (Variable "root_path"),
    Is_Nth_Child_Of (Variable "lhs_path", Number 1, Variable "root_path")
  ]
);

val mth_arg_of_func_occ_has_different_print =
Lambdas (["mth_arg_of_func_occ_has_arb"(*Inner_Number*), "func"(*Term*)],
  Some ("root_path", QInner_Path,
    Ands [
      Is_Root_In_A_Location (Variable "root_path"),
      Some ("lhs_path", QInner_Path,
        Ands [
          Applies (is_lhs_of_root, [Variable "lhs_path", Variable "root_path"]),
          Some ("mth_param_on_lhs_path", QInner_Path,
            Ands [
              Is_N_Plus_One_th_Child_Of (Variable "mth_param_on_lhs_path", Variable "mth_arg_of_func_occ_has_arb", Variable "lhs_path"),
                Ands [
                  Some ("mth_param_on_rhs_path", QInner_Path,
                    Ands [
                      Not (Has_Same_Prnt_As (Variable "mth_param_on_rhs_path", Variable "mth_param_on_lhs_path")),
                      Some_Of ("func_occ_on_rhs", Variable "func",
                        Ands [
                          Is_Nth_Argument_Of (Variable "mth_param_on_rhs_path", Variable "mth_arg_of_func_occ_has_arb", Variable "func_occ_on_rhs")
                        ]
                      )
                    ]
                  )
                ]
            ]
          )
        ]
      )
    ]
  )
);

in

(*what should not be generalized. Simplified version for easier presentation.*)
val for_all_arbs_there_should_be_a_change_simplified_for_presentation =
All ("arb_trm", QArb,
    Some ("ind_trm", QInd,
      Some_Of ("ind_occ", Variable "ind_trm",
        Some ("func_trm", QOuter_Print,
          Ands [
            Applies (print_defined_recursively, [Variable "func_trm"]),
            Some_Of ("func_trm_occ", Variable "func_trm",
              Ands [
                Some ("func_is_recurse_on_nth", QOuter_Number,
                  Ands [
                    Is_Nth_Argument_Or_Below_Nth_Argument_Of (Variable "ind_occ", Variable "func_is_recurse_on_nth", Variable "func_trm_occ"),(*Does this actually harm us?*)
                    Some_Of ("arb_trm_occ", Variable "arb_trm",
                      Some ("mth_arg_of_func_occ_has_arb", QOuter_Number,
                        Ands [
                          Is_Nth_Argument_Or_Below_Nth_Argument_Of (Variable "arb_trm_occ", Variable "mth_arg_of_func_occ_has_arb", Variable "func_trm_occ"),
                          Not (Are_Same_Number (Variable "func_is_recurse_on_nth", Variable "mth_arg_of_func_occ_has_arb")),
                          In_Some_Definitions (
                            Variable "func_trm",
                            mth_arg_of_func_occ_has_different_print,
                            [Variable "mth_arg_of_func_occ_has_arb", Variable "func_trm"]
                          )
                        ]
                      )
                    )
                  ]
                )
              ]
            )
          ]
        )
      )
    )
);

end

val test_is_a_meta_premise_or_below =
  All ("ind", QInd,
    Some_Of ("ind_occ", Variable "ind",
      Is_A_Meta_Premise_Or_Below (Variable "ind_occ")
    )
  );

val test_is_a_meta_conclusion_or_below =
  All ("ind", QInd,
    Some_Of ("ind_occ", Variable "ind",
      Is_A_Meta_Conclusion_Or_Below (Variable "ind_occ")
    )
  );

val test_Is_If_Then_Else =
Some ("if_then_else", QOuter_Path,
  Some ("if_condition", QOuter_Path,
    Some ("then_clause", QOuter_Path,
      Some ("else_clause", QOuter_Path,
        Is_If_Then_Else (
          Variable "if_then_else",
          Variable "if_condition",
          Variable "then_clause",
          Variable "else_clause")
      )
    )
  )
);

val test_Is_Subprint_Of_true  = Is_Subprint_Of (Print "abc", Print "aabcc");
val test_Is_Subprint_Of_false = Is_Subprint_Of (Print "abc", Print "aacc");

val test_Is_Case_Distinct_Of_Trm_With_A_Case =
Some ("whole_term", QOuter_Path,
  Some ("case_on", QOuter_Path,
    Some ("a_case", QOuter_Path,
        Ands [
          Is_Case_Distinct_Of_Trm_With_A_Case (
            Variable "whole_term",
            Variable "case_on",
            Variable "a_case"),
          Unode_Has_Print (Variable "case_on", Print "x"),
          Some ("in_a_case", QOuter_Path,
            Ands [
              Is_Path_Below (Variable "in_a_case", Variable "a_case"),
              Unode_Has_Print (Variable "in_a_case", Print "y")
            ]
          )
        ]
    )
  )
);

val test_Is_Let_X_Be_Y_In_X =
Some ("whole_term_occ", QOuter_Path,
  Some ("let_sth_be_this_occ", QOuter_Path,
    Some ("bound_and_body_occ", QOuter_Path,
        Ands [
          Is_Let_X_Be_Y_In_X (
            Variable "whole_term_occ",
            Variable "let_sth_be_this_occ",
            Variable "bound_and_body_occ"),
          Unode_Has_Print (Variable "let_sth_be_this_occ", Print "y"),
          Some ("in_bound_and_body_occ", QOuter_Path,
            Ands [
              Is_Path_Below (Variable "in_bound_and_body_occ", Variable "bound_and_body_occ"),
              Unode_Has_Print (Variable "in_bound_and_body_occ", Print "z < x1"),
              Some ("in_bound_and_body_occ2", QOuter_Path,
                Ands [
                  Unode_Has_As_Subprint (Variable "in_bound_and_body_occ2", Print "x2"),
                  Is_Path_Below (Variable "in_bound_and_body_occ2", Variable "bound_and_body_occ")
                ]
              )
            ]
          )
        ]
    )
  )
);

(*This is not good. To be removed? nth_arg_shrinks_from_assm_to_cncl_of_pure_imp_occ_inner*)
val nth_arg_shrinks_from_assm_to_cncl_of_pure_imp_occ_inner =
  Lambdas (["lth_arg_to_inductive_shrinks"(*number*),"inductive_trm"],
    Ands [
      Some ("root", QInner_Path,
        Ands [
          Is_Root_In_A_Location (Variable "root"),
          Some ("pure_imp_occ", QInner_Path,
            Ands [
              Unode_Has_Print (Variable "pure_imp_occ", Print "Pure.imp"),
              Is_Child_Of     (Variable "pure_imp_occ", Variable "root"),
              Some ("pure_imp_occ_has_n_args", QOuter_Number,
                Ands [
                  Some ("nth_arg_of_pure_imp_occ", QInner_Path,
                    Ands [
                      Is_Nth_Argument_Of (Variable "nth_arg_of_pure_imp_occ", Variable "pure_imp_occ_has_n_args", Variable "pure_imp_occ"),
                      All ("pure_imp_occ_has_more_than_m_args", QOuter_Number,
                        Ands [
                          All ("mth_arg_of_pure_imp_occ", QInner_Path,
                            Ands [
                              Imply (
                                Is_Nth_Argument_Of (Variable "mth_arg_of_pure_imp_occ", Variable "pure_imp_occ_has_more_than_m_args", Variable "pure_imp_occ"),
                                Is_Less_Than_Or_Equal (Variable "pure_imp_occ_has_more_than_m_args", Variable "pure_imp_occ_has_n_args")
                              )
                            ]
                          )
                        ]
                      ),
                      Some_Of ("inductive_occ_in_meta_cncl", Variable "inductive_trm",
                        Ands [
                          Is_Child_Of (Variable "inductive_occ_in_meta_cncl", Variable "nth_arg_of_pure_imp_occ"),
                          Some ("lth_arg_occ_to_inductive_occ_in_meta_cncl", QInner_Path,
                            Ands [
                              Is_Nth_Argument_Of (Variable "lth_arg_occ_to_inductive_occ_in_meta_cncl", Variable "lth_arg_to_inductive_shrinks", Variable "inductive_occ_in_meta_cncl"),
                              Some ("k_is_less_than_n", QInner_Number,
                                Ands [
                                  Is_Less_Than (Variable "k_is_less_than_n", Variable "pure_imp_occ_has_n_args"),
                                  Some ("kth_prem_occ_of_pure_imp_occ", QInner_Path,
                                    Ands [
                                      Is_Nth_Argument_Of (Variable "kth_prem_occ_of_pure_imp_occ", Variable "k_is_less_than_n", Variable "pure_imp_occ"),
                                      Some_Of ("inductive_occ_in_kth_prem_occ_of_pure_imp_occ", Variable "inductive_trm",
                                        Ands [
                                          Is_Child_Of (Variable "inductive_occ_in_kth_prem_occ_of_pure_imp_occ", Variable "kth_prem_occ_of_pure_imp_occ"),
                                          Some ("lth_arg_occ_to_inductive_occ_in_kth_prem_occ_of_pure_imp_occ", QInner_Path,
                                            Ands [
                                              Is_Nth_Argument_Of (Variable "lth_arg_occ_to_inductive_occ_in_kth_prem_occ_of_pure_imp_occ",
                                                             Variable "lth_arg_to_inductive_shrinks",
                                                             Variable "inductive_occ_in_kth_prem_occ_of_pure_imp_occ"),
                                              Some ("subtrm_occ_of_inductive_occ_in_kth_prem_occ_of_pure_imp_occ", QInner_Path,
                                                Ands [
                                                  Is_Path_Below (Variable "subtrm_occ_of_inductive_occ_in_kth_prem_occ_of_pure_imp_occ", Variable "lth_arg_occ_to_inductive_occ_in_kth_prem_occ_of_pure_imp_occ"),
                                                  Has_Same_Prnt_As (Variable "subtrm_occ_of_inductive_occ_in_kth_prem_occ_of_pure_imp_occ", Variable "lth_arg_occ_to_inductive_occ_in_meta_cncl")
                                                ]
                                              )
                                            ]
                                          )
                                        ]
                                      )
                                    ]
                                  )
                                ]
                              )
                            ]
                          )
                        ]
                      )
                    ]
                  )
                ]
              )
            ]
          )
        ]
      )
    ]
  );

(*This is not good. To be removed? structural_induction_on_nt_arg_of_inductively_defined_constant_in_the_concl_of_meta_imp_if_nth_arg_shrinks_in_def_of_constant_outer*)
val structural_induction_on_nt_arg_of_inductively_defined_constant_in_the_concl_of_meta_imp_if_nth_arg_shrinks_in_def_of_constant_outer =
  Some ("ind", QInd,
    Ands [
      Not (Some ("rule", QRule, True)),
      Some ("root", QOuter_Path,
        Ands [
          Is_Root_In_A_Location (Variable "root"),
          Some ("pure_imp_occ", QOuter_Path,
            Ands [
              Unode_Has_Print (Variable "pure_imp_occ", Print "Pure.imp"),
              Is_Child_Of     (Variable "pure_imp_occ", Variable "root"),
              Some ("inductive_trm", QOuter_Print,
                Ands [
                  Ors [
                    Print_Is_Defined_With (Variable "inductive_trm", Command Inductive    ),
                    Print_Is_Defined_With (Variable "inductive_trm", Command Inductive_Set)
                  ],
                  Some ("pure_imp_occ_has_n_args", QOuter_Number,
                    Ands [
                      Some ("nth_arg_of_pure_imp_occ", QOuter_Path,
                        Ands [
                          Is_Nth_Argument_Of (Variable "nth_arg_of_pure_imp_occ", Variable "pure_imp_occ_has_n_args", Variable "pure_imp_occ"),
                          All ("pure_imp_occ_has_more_than_m_args", QOuter_Number,
                            Ands [                
                              All ("mth_arg_of_pure_imp_occ", QOuter_Path,
                                Ands [
                                  Imply (
                                    Is_Nth_Argument_Of (Variable "mth_arg_of_pure_imp_occ", Variable "pure_imp_occ_has_more_than_m_args", Variable "pure_imp_occ"),
                                    Is_Less_Than_Or_Equal (Variable "pure_imp_occ_has_more_than_m_args", Variable "pure_imp_occ_has_n_args")
                                  )
                                ]
                              )
                            ]
                          ),
                          Some_Of ("inductively_defined_cnst_occ_in_pure_imp_cncl", Variable "inductive_trm",
                            Ands [
                              Is_Child_Of (Variable "inductively_defined_cnst_occ_in_pure_imp_cncl", Variable "nth_arg_of_pure_imp_occ"),
                              Some_Of ("ind_occ_appears_as_lth_arg_of_inductively_defined_const_in_pure_imp_cncl", Variable "ind",
                                Ands [
                                  Is_An_Argument_Or_Below_Argument_Of (Variable "ind_occ_appears_as_lth_arg_of_inductively_defined_const_in_pure_imp_cncl", Variable "inductively_defined_cnst_occ_in_pure_imp_cncl"),
                                 Some ("ind_occ_is_lth_arg_of_inductively_defined_const_in_pure_imp_cncl", QOuter_Number,
                                    Ands [
                                      Is_Nth_Argument_Or_Below_Nth_Argument_Of (Variable "ind_occ_appears_as_lth_arg_of_inductively_defined_const_in_pure_imp_cncl",
                                                                      Variable "ind_occ_is_lth_arg_of_inductively_defined_const_in_pure_imp_cncl",
                                                                      Variable "inductively_defined_cnst_occ_in_pure_imp_cncl"),
                                      In_Some_Definitions (
                                        Variable "inductive_trm",
                                        nth_arg_shrinks_from_assm_to_cncl_of_pure_imp_occ_inner,
                                        [Variable "ind_occ_is_lth_arg_of_inductively_defined_const_in_pure_imp_cncl", Variable "inductive_trm"]
                                      )
                                    ]
                                  )
                                ]
                              )
                            ]
                          )
                        ]
                      )
                    ]
                  )
                ]
              )
            ]
          )
        ]
      )
    ]
  );

val generalize_all_free_var_not_inducted_on =
All ("free_var_trm", QOuter_Print,
  Imply (
    Ands [
      Print_Is_Free (Variable "free_var_trm"),
      Not (
        Some ("ind_trm", QInd,
          Are_Same_Prints (Variable "free_var_trm", Variable "ind_trm")
        )
      )
    ],
    Some ("arb_trm", QArb,
      Are_Same_Prints (Variable "free_var_trm", Variable "arb_trm")
    )
  )
);

end