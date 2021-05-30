(*  Title:      PSL/SeLFiE/src/Interface/Assertion_Generalization.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
(*** signature: ASSERTION_GENERALIZATION ***)
signature ASSERTION_GENERALIZATION =
sig

val lifter_6                                                     : Eval_Syntactic_Sugar.assert;
val lifter_10                                                    : Eval_Syntactic_Sugar.assert;
val lifter_12                                                    : Eval_Syntactic_Sugar.assert;
val generalize_arguments_used_in_recursion                       : Eval_Syntactic_Sugar.assert;
val for_all_arbs_there_should_be_a_change                        : Eval_Syntactic_Sugar.assert;
val ind_on_lhs_of_eq_then_arb_on_rhs_of_eq                       : Eval_Syntactic_Sugar.assert;
val if_rule_induction_then_no_generalization                     : Eval_Syntactic_Sugar.assert;
val no_arb_has_occ_as_argument_of_all_occ_of_functional_induction: Eval_Syntactic_Sugar.assert;

end

(*** structure: Assertion_Generalization ***)
structure Assertion_Generalization: ASSERTION_GENERALIZATION =
struct

open SeLFiE_Util;
open Eval_Syntactic_Sugar;
open Definition_Pattern;

val lifter_6 =
Imply (
  Some ("ind_term", QInd,
    Print_Is_App (Variable "ind_term")
  ),
  All ("ind_term", QInd,
    Imply (
      Print_Is_App (Variable "ind_term"),
      All ("fvar_in_ind_term", QOuter_Print,
        Imply (
          Ands [
            Print_Is_Free (Variable "fvar_in_ind_term"),
            Is_Subprint_Of (Variable "fvar_in_ind_term", Variable "ind_term"),
              Some_Of ("ind_occ", Variable "ind_term",
                Ands [
                  Some_Of ("fvar_in_ind_occ", Variable "fvar_in_ind_term",
                    Ands [
                      Are_In_Same_Location (Variable "ind_occ", Variable "fvar_in_ind_occ"),
                      Is_Path_Below (Variable "fvar_in_ind_occ", Variable "ind_occ")
                    ]
                  )
                ]
              )
          ],
          Some ("arb_term", QArb,
            Are_Same_Prints (Variable "arb_term", Variable "fvar_in_ind_term")
          )
        )
      )
    )
  )
);
(*
val lifter_6_lambda_over_arb =
Lambdas (["arb_term"],
    Some ("ind_term", QInd,
      Ands [
        Print_Is_App (Variable "ind_term"),
        Some_Of ("arb_occ", Variable "arb_term",
          Ands [
            Some_Of ("ind_occ", Variable "ind_term",
              Ands [
                Are_In_Same_Location (Variable "ind_occ", Variable "arb_occ"),
                Is_Path_Below (Variable "arb_occ", Variable "ind_occ")
              ]
            )
          ]
        )
      ]
    )
  );
*)

local

val condition_for_sharing_function_by_ind_term_and_arb_term =
Not (
  Some ("ind_term", QInd,
    Ands [
      Some_Of ("ind_occ", Variable "ind_term",
        Ands [
          Some ("hol_eq_occ", QOuter_Path,
            Ands [
               Unode_Has_Print (Variable "hol_eq_occ", Print "HOL.eq"),
               Is_An_Argument_Of (Variable "ind_occ", Variable "hol_eq_occ")
            ]
          )
        ]
      )
    ]
  )
);

in

(*all inducts share a function with all arbitrary-s*)
val lifter_10 =
Imply (
  Ands [
    condition_for_sharing_function_by_ind_term_and_arb_term,
    Not (Some ("ind_term", QInd, Print_Is_App (Variable "ind_term")))
  ],
  All ("ind", QInd,
    Imply (
      Not (Print_Is_App (Variable "ind")),
      All ("arb", QArb,
          Some_Of ("ind_occ", Variable "ind",
            Some_Of ("arb_occ", Variable "arb",
              Some ("func_occ", QOuter_Path,
                Ands [
                  Is_An_Argument_Of (Variable "ind_occ", Variable "func_occ"),
                  Is_An_Argument_Of (Variable "arb_occ", Variable "func_occ")
                ]
              )
            )
          )
      )
    )
  )
);

(*arbitrary and induction share a function.*)
val lifter_12 =
Imply (
  Ands [
    Some ("arb", QArb, True),
    condition_for_sharing_function_by_ind_term_and_arb_term
  ],
  Some ("arb", QArb,
    Some_Of ("arb_occ", Variable "arb",
      Some ("ind", QInd,
        Imply (
          Not (Print_Is_App (Variable "ind")),
          Some_Of ("ind_occ", Variable "ind",
            Some ("func_occ", QOuter_Path,
              Ands [
                Is_An_Argument_Of (Variable "arb_occ", Variable "func_occ"),
                Is_An_Argument_Of (Variable "ind_occ", Variable "func_occ")
              ]
            )
          )
        )
      )
    )
  )
);

end

(*utility function: defined_recursively*)
val print_defined_recursively =
Lambdas (["func_trm"],
  Ors [
    Print_Is_Defined_With (Variable "func_trm", Command Fun),
    Print_Is_Defined_With (Variable "func_trm", Command Function),
    Print_Is_Defined_With (Variable "func_trm", Command Primrec)(*,
    Print_Is_Defined_With (Variable "func_trm", Command Inductive)*)
  ]
);

local

val is_lhs_of_root =(*TODO: we do not need root here.*)
Lambdas (["lhs_path", "root_path"],
  Ands [
    Is_Root_In_A_Location (Variable "root_path"),
    Is_Nth_Child_Of (Variable "lhs_path", Number 1, Variable "root_path")
  ]
);

val is_defined_recursively_on_nth =
Lambdas (["func", "number"],
  Ands [
    Some ("root_path", QInner_Path,
      Ands [
        Is_Root_In_A_Location (Variable "root_path"),
        Some ("lhs_path", QInner_Path,
          Ands [
            Applies (is_lhs_of_root, [Variable "lhs_path", Variable "root_path"]),
            Some ("part_of_nth_param_on_lhs", QInner_Path,
              Ands [
                Is_Below_N_Plus_One_th_Child_Of (Variable "part_of_nth_param_on_lhs", Variable "number", Variable "lhs_path"),
                Some_Of ("func_occ_on_rhs", Variable "func",
                  Ands [
                    Not (Is_Nth_Child_Of (Variable "func_occ_on_rhs", Number 0, Variable "lhs_path")),
                    Some ("part_of_nth_param_on_rhs", QInner_Path,
                      Ands [
                        Has_Same_Prnt_As (Variable "part_of_nth_param_on_rhs", Variable "part_of_nth_param_on_lhs"),
                        (*Is_Nth_Argument_Or_Below_Nth_Argument_Of*)Is_Nth_Argument_Of (Variable "part_of_nth_param_on_rhs", Variable "number", Variable "func_occ_on_rhs")
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
          )
        ]
      )
    ]
  )
);

in

(*what should be generalized.*)
val generalize_arguments_used_in_recursion =
Imply (
  Not (Some ("rule", QRule, True)),
  All ("ind", QInd,
    All_Of ("ind_occ", Variable "ind",
      All ("func", QOuter_Print,
        Imply (
          Ands [
            Applies (print_defined_recursively, [Variable "func"])
          ],
          Ands [
            All_Of ("func_occ", Variable "func",
              Ands [
                Imply (
                  Is_An_Argument_Or_Below_Argument_Of (Variable "ind_occ", Variable "func_occ"),
                  All ("recursive_on_nth_param", QOuter_Number,
                    Imply (
                      Ands [
                        Node_Takes_Less_Than_N_Arguments (Variable "func_occ", Variable "recursive_on_nth_param"),
                        In_Some_Definitions (
                          Variable "func",
                          is_defined_recursively_on_nth,
                          [Variable "func", Variable "recursive_on_nth_param"]
                        )
                      ],
                      All ("used_to_update_mth_arg", QOuter_Number,
                        Imply (
                          Ands [
                            Node_Takes_Less_Than_N_Arguments (Variable "func_occ", Variable "used_to_update_mth_arg"),
                            Not (Are_Same_Number (Variable "recursive_on_nth_param", Variable "used_to_update_mth_arg")),
                            In_Some_Definitions (
                              Variable "func",
                              mth_arg_of_func_occ_has_different_print,
                              [Variable "used_to_update_mth_arg", Variable "func"]
                            )
                          ],
                          Ands [
                            Some_Of ("func_occ_4_arb", Variable "func",
                              Ands [
                                Some ("arb", QArb, (*!*)
                                  Ands [
                                    Some_Of ("arb_occ", Variable "arb",
                                      Ands [
                                        Is_Nth_Argument_Or_Below_Nth_Argument_Of (Variable "arb_occ", Variable "used_to_update_mth_arg", Variable "func_occ_4_arb")
                                      ]
                                    )
                                  ]
                                )
                              ]
                            )
                          ]
                        )
                      )
                    )
                  )
                )
              ]
            )
          ]
        )
      )
    )
  )
);

local

val lifter_6_lambda_over_arb =
Lambdas (["arb_term"],
    Some ("ind_term", QInd,
      Ands [
        Print_Is_App (Variable "ind_term"),
        Some_Of ("arb_occ", Variable "arb_term",
          Ands [
            Some_Of ("ind_occ", Variable "ind_term",
              Ands [
                Are_In_Same_Location (Variable "ind_occ", Variable "arb_occ"),
                Is_Path_Below (Variable "arb_occ", Variable "ind_occ")
              ]
            )
          ]
        )
      ]
    )
  );

in

(*what should not be generalized.*)
val for_all_arbs_there_should_be_a_change =
Imply (
  Not (Some ("rule", QRule, True)),
  All ("arb_trm", QArb,
    Ors [
      Applies (lifter_6_lambda_over_arb, [Variable "arb_trm"])(*TODO: No syntactic heuristics indicate "arb_trm" should be generalized.*),
      Some ("ind_trm", QInd,
        Some_Of ("ind_occ", Variable "ind_trm",
          Some ("func_trm", QOuter_Print,
            Ands [
              Applies (print_defined_recursively, [Variable "func_trm"]),
              Some_Of ("func_trm_occ", Variable "func_trm",
                Ands [
                  Some ("func_is_recurse_on_nth", QOuter_Number,
                    Ands [
                      Node_Takes_Less_Than_N_Arguments (Variable "func_trm_occ", Variable "func_is_recurse_on_nth"),                  (*Does this actually harm us?*)
                      Is_Nth_Argument_Or_Below_Nth_Argument_Of (Variable "ind_occ", Variable "func_is_recurse_on_nth", Variable "func_trm_occ"),(*Does this actually harm us?*)
                      Some_Of ("arb_trm_occ", Variable "arb_trm",
                        Some ("mth_arg_of_func_occ_has_arb", QOuter_Number,
                          Ands [
                            Node_Takes_Less_Than_N_Arguments (Variable "func_trm_occ", Variable "mth_arg_of_func_occ_has_arb"),
                            Some_Of ("func_trm_occ2", Variable "func_trm", (*we do not always talk about the same occurrence of the function. See addO_exp\<omega>_inj in Goodstein_Lambda.thy where we have to deal with two different occurrences of add0.*)
                              Ands [
                                Is_Nth_Argument_Or_Below_Nth_Argument_Of (Variable "arb_trm_occ", Variable "mth_arg_of_func_occ_has_arb", Variable "func_trm_occ2"),
                                Imply ( 
                                  Ands [
                                    Is_Same_Path_As (Variable "func_trm_occ", Variable "func_trm_occ2"),
                                    Are_In_Same_Location (Variable "func_trm_occ", Variable "func_trm_occ2")
                                  ],
                                  Not (Are_Same_Number (Variable "func_is_recurse_on_nth", Variable "mth_arg_of_func_occ_has_arb"))(*We should check this because parameter for recursion is always changing in a recursive call. Maybe we can get rid of this check, and let other heuristics check Inds and Arbs are disjoint.*)
                                )
                              ]
                            ),
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
    ]
  )
);

end

end

local

val node_is_variable =
Lambdas (["variable"],
  Ands [
    Not (Node_Is_Cnst   (Variable "variable")),
    Not (Node_Is_Lambda (Variable "variable")),
    Not (Node_Is_App    (Variable "variable"))
  ]
);

in

val ind_on_lhs_of_eq_then_arb_on_rhs_of_eq =
Imply (
  Ands [
    Not (Some ("rule", QRule, True)),
    Some ("hol_eq_occ", QOuter_Path,
      Ands [
        Unode_Has_Print (Variable "hol_eq_occ", Print "HOL.eq"),
        Some ("ind_trm", QInd,
          Some_Of ("ind_occ", Variable "ind_trm",
            Ands [
              Applies (node_is_variable, [Variable "ind_occ"]),
              Is_Nth_Argument_Of (Variable "ind_occ", Number 0, Variable "hol_eq_occ"),
              Some ("arb_occ", QOuter_Path,
                Ands [
                  Applies (node_is_variable, [Variable "arb_occ"]),
                  Not (Unode_Has_Print (Variable "arb_occ", Variable "ind_trm")),
                  Is_Nth_Argument_Of (Variable "arb_occ", Number 1, Variable "hol_eq_occ")
                ]
              )
            ]
          )
        )
      ]
    )
  ],
  Some ("hol_eq_occ", QOuter_Path,
    Ands [
      Unode_Has_Print (Variable "hol_eq_occ", Print "HOL.eq"),
      Some ("ind_trm", QInd,
        Some_Of ("ind_occ", Variable "ind_trm",
          Ands [
            Applies (node_is_variable, [Variable "ind_occ"]),
            Is_Nth_Argument_Of (Variable "ind_occ", Number 0, Variable "hol_eq_occ"),
            Some ("arb_trm", QArb,(*!*)
              Some_Of ("arb_occ", Variable "arb_trm",(*!*)
                Ands [
                  Is_Nth_Argument_Of (Variable "arb_occ", Number 1, Variable "hol_eq_occ")
                ]
              )
            )
          ]
        )
      )
    ]
  )
);

end

val if_rule_induction_then_no_generalization =
Imply (
  Some ("rule", QRule, True),
  Not (Some ("arb", QArb, True))
);

val no_arb_has_occ_as_argument_of_all_occ_of_functional_induction =
Not (
  Some ("arb", QArb,
    Some ("rule", QRule,
      Some ("rec_func", QOuter_Print,
        Ands [
          Is_Rule_Of_Print (Variable "rule", Variable "rec_func"),
          Applies (print_defined_recursively, [Variable "rec_func"]),
          All_Of ("rec_func_occ", Variable "rec_func",
            Some_Of ("arb_occ", Variable "arb",
              Is_An_Argument_Or_Below_Argument_Of (Variable "arb_occ", Variable "rec_func_occ")
            )
          )
        ]
      )
    )
  )
);

(*

(*what should be generalized deep.*)(*Look how this heuristic handles, for example, soundness' in Hybrid_Logic.thy*)
val generalize_arguments_used_in_recursion_deep =
Ors [
  All ("ind", QInd,
    All ("func", QOuter_Print,
      Imply (
        Ands [
          Print_Is_Cnst (Variable "func"),
          Applies (is_defined_recursively_straw, [Variable "func"])
        ],
        Ands [
          All_Of ("func_occ", Variable "func",
            Ands [
              All ("used_to_update_mth_arg", QOuter_Number,
                  Ands [
                    Node_Takes_Less_Than_N_Arguments (Variable "func_occ", Variable "used_to_update_mth_arg"),
                    In_Some_Definitions (
                      Variable "func",
                      mth_arg_of_func_occ_has_different_print_straw,
                      [Variable "used_to_update_mth_arg", Variable "func"]
                    )
                  ]
                Imply
                  Ands [
                    Some_Of ("func_occ2", Variable "func",
                      Ands [
                        Some ("arb", QArb,
                          Imply (
                            Not (Are_Same_Prints (Variable "ind", Variable "arb")),
                            Ands [
                              Some_Of ("arb_occ", Variable "arb",
                                Ands [
                                  Is_Nth_Argument_Or_Below_Nth_Argument_Of
                                   (Variable "arb_occ", Variable "used_to_update_mth_arg", Variable "func_occ2")
                                ]
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
        ]
      )
    )
  )
];

*)

end;