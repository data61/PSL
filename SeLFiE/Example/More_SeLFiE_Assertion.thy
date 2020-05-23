theory More_SeLFiE_Assertion
imports "SeLFiE.SeLFiE"
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


val nth_parameter_is_used_in_mth_argument_in_recursive_call =
Lambdas (["func", "recursive_on_nth", "mth"],
  Ands [
    Some ("root_path", QInner_Path,
      Ands [
        Is_Root_In_A_Location (Variable "root_path"),
        Some ("lhs_path", QInner_Path,
          Ands [
            Applies (is_lhs_of_root, [Variable "lhs_path", Variable "root_path"]),
            Some ("rhs_path", QInner_Path,
              Ands [
                Applies (is_rhs_of_root, [Variable "rhs_path", Variable "root_path"]),
                Some ("part_of_nth_param_on_lhs_that_causes_ind", QInner_Path,
                  Ands [
                    Applies (is_variable, [Variable "part_of_nth_param_on_lhs_that_causes_ind"]),
                    Is_Below_N_Plus_One_th_Child_Of (Variable "part_of_nth_param_on_lhs_that_causes_ind", Variable "recursive_on_nth", Variable "lhs_path"),
                    Some_Of ("func_occ_on_rhs_that_causes_ind", Variable "func",
                      Ands [
                        Is_Path_Below (Variable "func_occ_on_rhs_that_causes_ind", Variable "rhs_path"),
                        Some ("part_of_nth_param_on_rhs_that_causes_ind", QInner_Path,
                          Ands [
                            Has_Same_Prnt_As (Variable "part_of_nth_param_on_rhs_that_causes_ind", Variable "part_of_nth_param_on_lhs_that_causes_ind"),
                            Is_Nth_Arg_Or_Below_Nth_Arg_Of (Variable "part_of_nth_param_on_rhs_that_causes_ind", Variable "recursive_on_nth", Variable "func_occ_on_rhs_that_causes_ind"),
                            Some_Of ("func_occ_on_rhs_that_causes_arb", Variable "func",
                              Ands [
                                Is_Path_Below (Variable "func_occ_on_rhs_that_causes_arb", Variable "rhs_path"),
                                Some ("part_of_nth_param_on_lhs_that_causes_arb", QInner_Path,
                                  Ands [
                                    Applies (is_variable, [Variable "part_of_nth_param_on_lhs_that_causes_arb"]),
                                    Is_N_Plus_One_th_Child_Or_Below_N_Plus_One_th_Child_Of (Variable "part_of_nth_param_on_lhs_that_causes_arb", Variable "recursive_on_nth", Variable "lhs_path"),
                                    Some ("part_of_nth_param_on_rhs_that_causes_arb", QInner_Path,
                                      Ands [
                                        Has_Same_Prnt_As (Variable "part_of_nth_param_on_rhs_that_causes_arb", Variable "part_of_nth_param_on_lhs_that_causes_arb"),
                                        Is_Nth_Arg_Or_Below_Nth_Arg_Of (Variable "part_of_nth_param_on_rhs_that_causes_arb", Variable "mth", Variable "func_occ_on_rhs_that_causes_arb")
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
            Is_Nth_Child_Of (Variable "lhs_path", Number 1, Variable "root_path"),
            Some ("part_of_nth_param_on_lhs", QInner_Path,
              Ands [
                Is_Below_N_Plus_One_th_Child_Of (Variable "part_of_nth_param_on_lhs", Variable "number", Variable "lhs_path"),
                Some ("rhs_path", QInner_Path,
                  Ands [
                    Is_Nth_Child_Of (Variable "rhs_path", Number 2, Variable "root_path"),
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

val generalize_arguments_used_in_recursion =
  Some ("ind", QInd,
    Some_Of ("ind_occ", Variable "ind",
      Some ("func", QOuter_Print,
        Some_Of ("func_occ", Variable "func",
          Ands [
            Applies (defined_recursively, [Variable "func_occ"]),
            Is_An_Arg_Or_Below_Arg_Of (Variable "ind_occ", Variable "func_occ"),
            Some ("recursive_on_nth_param", QOuter_Number,
              Ands [
                Takes_Less_Than_N_Arguments (Variable "func_occ", Variable "recursive_on_nth_param"),
                Some ("used_to_update_mth_arg", QOuter_Number,
                  Ands [
                    Not (Are_Same_Number (Variable "recursive_on_nth_param", Variable "used_to_update_mth_arg")),
                    Takes_Less_Than_N_Arguments (Variable "func_occ", Variable "used_to_update_mth_arg"),
                    In_Some_Definitions (Variable "func",
                                         nth_parameter_is_used_in_mth_argument_in_recursive_call,
                                         [Variable "func", Variable "recursive_on_nth_param", Variable "used_to_update_mth_arg"]
                                         )
                  ]
                )
              ]
            ),
            Debug_Non_Path_Literal (Print "===Assumption is done===")
          ]
        )
      )
    )
  )
Imply
  All ("ind", QInd,(*!*)(*Now we check for all induction terms.*)
    Some_Of ("ind_occ", Variable "ind",
      Some ("func", QOuter_Print,
        Some_Of ("func_occ", Variable "func",
          Ands [
            Applies (defined_recursively, [Variable "func_occ"]),
            Is_An_Arg_Or_Below_Arg_Of (Variable "ind_occ", Variable "func_occ"),
            Some ("recursive_on_nth_param", QOuter_Number,
              Ands [
                Takes_Less_Than_N_Arguments (Variable "func_occ", Variable "recursive_on_nth_param"),
                Some ("used_to_update_mth_arg", QOuter_Number,
                  Ands [
                    Takes_Less_Than_N_Arguments (Variable "func_occ", Variable "used_to_update_mth_arg"),
                    Not (Are_Same_Number (Variable "recursive_on_nth_param", Variable "used_to_update_mth_arg")),
                    Some ("arb", QArb, (*!*)
                      Some_Of ("arb_occ", Variable "arb",
                        Is_Nth_Arg_Or_Below_Nth_Arg_Of (Variable "arb_occ", Variable "used_to_update_mth_arg", Variable "func_occ")
                      )
                    ),
                    In_Some_Definitions (Variable "func",
                                         nth_parameter_is_used_in_mth_argument_in_recursive_call,
                                         [Variable "func", Variable "recursive_on_nth_param", Variable "used_to_update_mth_arg"]
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
;

end;
\<close>

ML\<open>
@{term "let x = True in y"};
@{term "x y z"};
\<close>

end