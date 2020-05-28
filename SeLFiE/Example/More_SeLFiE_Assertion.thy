theory More_SeLFiE_Assertion
imports "../SeLFiE"
begin

ML\<open> structure More_SeLFiE_Assertion =
struct

open SeLFiE_Util;
open Eval_Syntactic_Sugar;
open Quantifier_Domain;
open Pattern;

infix Imply;

val is_lhs_of_root =(*TODO: we do not need root here.*)
Lambdas (["lhs_path", "root_path"],
  Ands [
    Is_Root_In_A_Location (Variable "root_path"),
    Is_Nth_Child_Of (Variable "lhs_path", Number 1, Variable "root_path")
  ]
);

val is_rhs_of_root =(*TODO: we do not need root here.*)
Lambdas (["rhs_path", "root_path"],
  Ands [
    Is_Root_In_A_Location (Variable "root_path"),
    Is_Nth_Child_Of (Variable "rhs_path", Number 2, Variable "root_path")
  ]
);

val is_variable =
Lambdas (["variable"],
  Ors [
    Is_Free  (Variable "variable"),
    Is_Var   (Variable "variable"),
    Is_Bound (Variable "variable")
  ]
);

(*defined_recursively*)
val defined_recursively =
Lambdas (["func_occ"],
  Ors [
    Is_Defined_With (Variable "func_occ", Command Fun),
    Is_Defined_With (Variable "func_occ", Command Function),
    Is_Defined_With (Variable "func_occ", Command Primrec),
    Is_Defined_With (Variable "func_occ", Command Inductive)
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
                Some ("rhs_path", QInner_Path,
                  Ands [
                    Applies (is_rhs_of_root, [Variable "rhs_path", Variable "root_path"]),
                    Some_Of ("func_occ_on_rhs", Variable "func",
                      Ands [
                        Is_Path_Below (Variable "func_occ_on_rhs", Variable "rhs_path"),
                        Some ("part_of_nth_param_on_rhs", QInner_Path,
                          Ands [
                            Has_Same_Prnt_As (Variable "part_of_nth_param_on_rhs", Variable "part_of_nth_param_on_lhs"),
                            Is_Nth_Arg_Or_Below_Nth_Arg_Of (Variable "part_of_nth_param_on_rhs", Variable "number", Variable "func_occ_on_rhs")
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

val is_defined_recursively_on_nth_outer =
  Not (Some ("rule", QRule, True))
Imply
  Some ("func", QOuter_Print,
    Some_Of ("func_occ", Variable "func",
      Ands [
        Applies (defined_recursively, [Variable "func_occ"]),
        All ("induct", QInd,
          Some_Of ("ind_occ", Variable "induct",
            Some ("number", QOuter_Number,
              Ands [
                Takes_Less_Than_N_Arguments (Variable "func_occ", Variable "number"),
                Is_Nth_Arg_Of (Variable "ind_occ", Variable "number", Variable "func_occ"),
                In_Some_Definitions (Variable "func", is_defined_recursively_on_nth, [Variable "func", Variable "number"])
              ]
            )
          )
        )
      ]
    )
  );













val mth_arg_of_func_occ_has_different_print =
Lambdas (["mth_arg_of_func_occ_has_arb"(*Inner_Number*), "func"(*Term*)],
  Some ("print_of_mth_argument", QInner_Print,
    Some_Of ("mth_arg_occ_of_func_occ1", Variable "print_of_mth_argument",
      Some_Of ("func_occ1", Variable "func",
        Ands [
          Is_Nth_Arg_Of (Variable "mth_arg_occ_of_func_occ1", Variable "mth_arg_of_func_occ_has_arb", Variable "func_occ1"),
          Some ("mth_arg_occ_of_func_occ2", QInner_Path,
            Ands [
              Not (Unode_Has_Print (Variable "mth_arg_occ_of_func_occ2", Variable "print_of_mth_argument")),
              Some_Of ("func_occ2", Variable "func",
                Ands [
                  Not (Is_Same_Path_As (Variable "func_occ1", Variable "func_occ2")),
                  Is_Nth_Arg_Of (Variable "mth_arg_occ_of_func_occ2", Variable "mth_arg_of_func_occ_has_arb", Variable "func_occ2")
                ]
              )
            ]
          )
        ]
      )
    )
  )
);
(*slow for some reasons
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
              Some ("print_of_mth_param_on_lhs", QInner_Print,
                Ands [
                  Unode_Has_Print (Variable "mth_param_on_lhs_path", Variable "print_of_mth_param_on_lhs"),
                  Some ("mth_param_on_rhs_path", QInner_Path,
                    Ands [
                      Not (Unode_Has_Print (Variable "mth_param_on_rhs_path", Variable "print_of_mth_param_on_lhs")),
                      Some_Of ("func_occ_on_rhs", Variable "func",
                        Ands [
                          Is_Nth_Arg_Of (Variable "mth_param_on_rhs_path", Variable "mth_arg_of_func_occ_has_arb", Variable "func_occ_on_rhs")
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
);
*)
val for_all_arbs_there_should_be_a_change =
All ("arb_trm", QArb,
    True(*TODO: No syntactic heuristics indicate "arb_trm" should be generalized.*)
  Imply
    Some ("ind_trm", QInd,
      Some_Of ("ind_occ", Variable "ind_trm",
        Some ("func_trm", QOuter_Print,
          Some_Of ("func_trm_occ", Variable "func_trm",
            Ands [
              Applies (defined_recursively, [Variable "func_trm_occ"]),
              Some ("func_is_recurse_on_nth", QOuter_Number,
                Ands [
                  Takes_Less_Than_N_Arguments (Variable "func_trm_occ", Variable "func_is_recurse_on_nth"),                       (*Does this actually harm us?*)
                  Is_Nth_Arg_Or_Below_Nth_Arg_Of (Variable "ind_occ", Variable "func_is_recurse_on_nth", Variable "func_trm_occ"),(*Does this actually harm us?*)
                  Some_Of ("arb_trm_occ", Variable "arb_trm",
                    Some ("mth_arg_of_func_occ_has_arb", QOuter_Number,
                      Ands [
                        Takes_Less_Than_N_Arguments (Variable "func_trm_occ", Variable "mth_arg_of_func_occ_has_arb"),
                        Is_Nth_Arg_Or_Below_Nth_Arg_Of (Variable "arb_trm_occ", Variable "mth_arg_of_func_occ_has_arb", Variable "func_trm_occ"),
                        Not (Are_Same_Number (Variable "func_is_recurse_on_nth", Variable "mth_arg_of_func_occ_has_arb")),
                        Debug_Non_Path_Literal (Variable "func_trm"),
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
        )
      )
    )
)

end;
\<close>

setup\<open> Apply_SeLFiE.update_assert "for_all_arbs_there_should_be_a_change" More_SeLFiE_Assertion.for_all_arbs_there_should_be_a_change \<close>

declare[[ML_print_depth=100]]

end