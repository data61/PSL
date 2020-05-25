(*  Title:      PSL/SeLFiE/src/Interface/SeLFiE_Assertion.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
(*** signature: SELFIE_ASSERTION ***)

(*** structure: SeLFiE_Assertion ***)
structure SeLFiE_Assertion =
struct

open SeLFiE_Util;
open Eval_Syntactic_Sugar;
open Pattern;

val is_meta_equation =
  Lambdas (["meta_eq"], Are_Same_Prints (Variable "meta_eq", Print "(\<equiv>)"));

(*is_function returns true  for "f" when applied to "f x y"
  is_function returns false for "x" when applied to "f x y"
  is_function returns false for "c" when applied to "c"*)
val is_function =
  Lambdas (["func"],
    Some ("func_app", QOuter_Path,
      Ands
        [Is_App (Variable "func_app"),
         Is_Nth_Child_Of (Variable "func", Number 0, Variable "func_app")
         ]));

val is_constant =
  Lambdas (["constant"], Is_Cnst (Variable "constnat"));

val is_on_the_rhs_of_meta_eq =
  Lambdas (["constant"],
    Some ("meta_eq", QOuter_Path,
      Ands
        [Is_Cnst (Variable "meta_eq"),
         Are_Same_Prints (Variable "meta_eq", Print "(\<equiv>)"),
         Ors
           [(*TODO*)
            ]
        ]
    )
  );

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
   Are_Same_Prints (Print "SeLFiE.itrev", Print "SeLFiE.itrev")))

val heuristic_8 =
 Applies (
  Lambdas (["x"], 
           Are_Same_Prints (Variable "x", Print "SeLFiE.itrev")),
  [Print "SeLFiE.itrev"]);

val heuristic_9 =
 (Some ("x", QOuter_Path,
   Unode_Has_Print (Variable "x", Print "ys")));;

val heuristic_10 =
 Not
  (Some ("x", QOuter_Path,
   Unode_Has_Print (Variable "x", Print "yss")));

val heuristic_11 =
 (Some ("x", QOuter_Path,
   Unode_Has_Print (Variable "x", Print "SeLFiE.itrev")));

val heuristic_12 =
  Some ("induct", QInd,
    Are_Same_Prints (Variable "induct", Print "xs"));

val heuristic_13 =
  Not (
    Some ("induct", QArb,
      Are_Same_Prints (Variable "induct", Print "xs")));
infix Imply;
(*
infix And Or  Is_Rule_Of_Print Is_An_Arg_Of Unode_Has_Print Has_Same_Prnt_As Is_Path_Below;
infix Is_Rule_Of_Node;
*)

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
      Not (Is_Cnst (Variable "var_occ")),
      Unode_Has_Print (Variable "var_occ", Variable "induct")
    ]
  )
);

val lifter_1b =
All ("induct", QInd,
  Some_Of ("var_occ", Variable "induct",
      Not (Is_Cnst (Variable "var_occ"))));

val lifter_2 =
All ("xs", QInd,
  Some_Of ("xs_occ", Variable "xs",
      Is_Atomic (Variable "xs_occ")
    Imply
      Is_At_Deepest_In_A_Location (Variable "xs_occ")
  ));

(*defined_recursively*)
fun defined_recursively (func_occ:Eval_Syntactic_Sugar.assert) =
Ors [
  Is_Defined_With (func_occ, Command Fun),
  Is_Defined_With (func_occ, Command Function),
  Is_Defined_With (func_occ, Command Primrec),
  Is_Defined_With (func_occ, Command Inductive)
];

val lifter_3 =
Some ("func_occ", QOuter_Path,
  All ("ind", QInd,
    Some_Of ("ind_occ", Variable "ind",
      Ands [
        Is_An_Arg_Of (Variable "ind_occ", Variable "func_occ"),
        defined_recursively (Variable "func_occ")
      ]
    )
  )
);

val nth_arg_on_lfs_is_const_or_app =
 Lambdas (["nth"], Debug_Non_Path_Literal (Variable "func"));

val help_test_dive_in =
 Lambdas (["func"],
  All ("printed", QInner_Print,
   Debug_Non_Path_Literal (Variable "printed")));

val test_dive_in =
All ("func_occ", QOuter_Path,
    Is_Defined_With (Variable "func_occ", Command Fun)
  Imply
    All ("func", QOuter_Print,
        Unode_Has_Print (Variable "func_occ", Variable "func")
      Imply
        In_All_Definitions (Variable "func", help_test_dive_in, [Variable "func"])
    )
)

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

val print_outer_path_root =
All ("outpath", QOuter_Path,
    Is_Root_In_A_Location (Variable "outpath")
  Imply
    Debug_Print_Unode (Variable "outpath"));

val print_inner_path_root_help =
Lambdas (["outer_print"],
  Some ("inner_path", QInner_Path,
    Ands [
      Is_Root_In_A_Location (Variable "inner_path"),
      Debug_Print_Unode (Variable "inner_path")
    ]
  )
);

val print_inner_roots =
All ("outer_path", QOuter_Path,
  Some ("outer_print", QOuter_Print,
    Ands [
      Unode_Has_Print (Variable "outer_path", Variable "outer_print"),
      In_All_Definitions (Variable "outer_print", print_inner_path_root_help, [Variable "outer_print"])
    ]
  )
);

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

val print_all_inner_lhss =
All ("outer_path", QOuter_Path,
  Some ("outer_print", QOuter_Print,
    Ands [
      Unode_Has_Print (Variable "outer_path", Variable "outer_print"),
      In_All_Definitions (Variable "outer_print", help_print_inner_lhs, [Variable "outer_print"])
    ]
  )
);

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
              Is_N_Plus_One_th_Child_Of (Variable "fst_param", Variable "number", Variable "lfs_path"),
              Debug_Print_Unode (Variable "fst_param")
            ]
          )
        ]
      )
    ]
  )
);

val print_fst_params_of_fun_const =
Some ("outer_path", QOuter_Path,
  Some ("outer_print", QOuter_Print,
    Ands [
      Unode_Has_Print (Variable "outer_path",  Variable "outer_print"),
      Is_Defined_With (Variable "outer_path", Command Fun),
      In_All_Definitions (Variable "outer_print", help_print_n_plus_one_th_param, [Number 0])
      ]));

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
              Takes_Less_Than_N_Arguments (Variable "lfs_path", Variable "number"),
              Is_N_Plus_One_th_Child_Of (Variable "nth_param", Variable "number", Variable "lfs_path"),
              Ors [
                Is_Cnst (Variable "nth_param"),
                Is_App  (Variable "nth_param")
              ]
            ]
          )
        ]
      )
    ]
  )
);

val lifter_4 =
  Not (Some ("rule", QRule, True))
Imply
  Some ("func", QOuter_Print,
    Some_Of ("func_occ", Variable "func",
      Ands [
        defined_recursively (Variable "func_occ"),
        All ("induct", QInd,
          Some_Of ("ind_occ", Variable "induct",
            All ("number", QOuter_Number,
                Ands [
                  Takes_Less_Than_N_Arguments (Variable "func_occ", Variable "number"),
                  Is_Nth_Arg_Of (Variable "ind_occ", Variable "number", Variable "func_occ")
                ]
              Imply
                Ands [
                  Debug_Non_Path_Literal (Print "Now we dive in: "),
                  In_All_Definitions (Variable "func_occ", help_lifter_4_nth_arg_is_const_or_app, [Variable "number"])
                ]
            )
          )
        )
      ]
    )
  );

val lifter_5 =
  Some ("rule", QRule, True)
Imply
  Some ("rule", QRule,
    Some ("func", QOuter_Print,
      Some_Of ("func_occ", Variable "func",
        Ands [
          Is_Rule_Of_Print (Variable "rule", Variable "func"),
          Debug_Non_Path_Literal (Variable "func"),
          Debug_Non_Path_Literal (Variable "rule"),
          All ("ind", QInd,
            Some_Of ("arg_occ", Variable "ind",
              Some ("numb", QOuter_Number,
                Ands [
                  Takes_Less_Than_N_Arguments (Variable "func_occ", Variable "numb"),
                  Is_Nth_Arg_Of (Variable "arg_occ", Variable "numb", Variable "func_occ"),
                  Is_Nth_Induct (Variable "ind", Variable "numb"),
                  Debug_Print_Unode (Variable "arg_occ"),
                  Debug_Non_Path_Literal (Variable "numb"),
                  Debug_Print_Unode (Variable "func_occ")
                ]
              )
            )
          )
        ]
      )
    )
  );

val lifter_6 =
All ("arbitrary", QArb,
  Not
    (Some ("induct", QInd,
      Are_Same_Prints (Variable "arbitrary", Variable "induct")
     )
    )
);

val lifter_7 =
  Some ("func", QOuter_Print,
    Some_Of ("func_occ", Variable "func",
      defined_recursively (Variable "func_occ")
    )
  )
Imply
  Some ("func", QOuter_Print,
    Some_Of ("func_occ", Variable "func",
      Ands [
        defined_recursively (Variable "func_occ"),
        Some ("induct_arg", QInd,
          Some_Of ("induct_arg_occ", Variable "induct_arg",
            Ands [
              Is_An_Arg_Of (Variable "induct_arg_occ",  Variable "func_occ"),
              Debug_Print_Unode (Variable "func_occ"),
              Debug_Print_Unode (Variable "induct_arg_occ")
            ]
          )
        )
      ]
    )
  );

val lifter_8 = Some ("induct", QInd, True);

val lifter_9 =
  Some ("induct_arg", QInd, True)
Imply
  Some ("induct_arg", QInd,
    Some_Of ("induct_arg_occ", Variable "induct_arg",
      Is_At_Deepest_In_A_Location (Variable "induct_arg_occ")
    )
  );

(*induct and arbitrary share a function*)
val lifter_10 =
All ("ind", QInd,
  All ("arb", QArb,
    Some_Of ("ind_occ", Variable "ind",
      Some_Of ("arb_occ", Variable "arb",
        Some ("func_occ", QOuter_Path,
          Ands [
            Is_An_Arg_Of (Variable "ind_occ", Variable "func_occ"),
            Is_An_Arg_Of (Variable "arb_occ", Variable "func_occ")
          ]
        )
      )
    )
  )
);

(*all arguments rule-function are induction variable*)
val lifter_11 =
  Some ("rule", QRule, True)
Imply
  Some ("rule", QRule,
    Some ("func", QOuter_Print,
      Ands [
        Is_Rule_Of_Print (Variable "rule",  Variable "func"),
        Some_Of ("func_occ", Variable "func",
          All ("arg_occ", QOuter_Path,
              Is_An_Arg_Of (Variable "arg_occ", Variable "func_occ")
            Imply
              Some ("ind", QInd,
                Unode_Has_Print (Variable "arg_occ", Variable "ind")
              )
          )
        )
      ]
    )
  );

(*arbitrary and induction share a function.*)
val lifter_12 =
  Some ("arb", QArb, True)
Imply
  Some ("arb", QArb,
    Some_Of ("arb_occ", Variable "arb",
      Some ("ind", QInd,
        Some_Of ("ind_occ", Variable "ind",
          Some ("func_occ", QOuter_Path,
            Ands [
              Is_An_Arg_Of (Variable "arb_occ", Variable "func_occ"),
              Is_An_Arg_Of (Variable "ind_occ", Variable "func_occ")
            ]
          )
        )
      )
    )
  );

(*no arbitrary is at the same relative location as induction in terms of a function*)
val lifter_13 =
  Some ("arb", QArb, True)
Imply
  All ("arb", QArb,
    Not
      (Some_Of ("arb_occ", Variable "arb",
         Some ("func", QOuter_Print,
           Some_Of ("func_occ1", Variable "func",
             Some ("number", QOuter_Number,
               Ands [
                 Is_Nth_Arg_Of (Variable "arb_occ", Variable "number", Variable "func_occ1"),
                 Some ("ind", QInd,
                   Some_Of ("ind_occ", Variable "ind",
                     Some_Of ("func_occ2", Variable "func",
                       Is_Nth_Arg_Of (Variable "ind_occ", Variable "number", Variable "func_occ2")
                     )
                   )
                 )
               ]
             )
           )
         )
       )
      )
  );

(*only one rule*)
val lifter_14 =
  Some ("rule", QRule, True)
Imply
  All ("rule1", QRule,
    All ("rule2", QRule,
      Are_Same_Prints (Variable "rule1", Variable "rule2")
    )
  );

val lifter_15_assumption =
  All ("ind", QInd,
    Some_Of ("ind_occ", Variable "ind",
      Is_Atomic (Variable "ind_occ")
    )
  );

val lifter_15_conclusion =
  Is_Rule_Of_Node (Variable "rule", Variable "func2_occ");

fun lifter_15_shared unique =
  Some ("rule", QRule,
    Some ("func1_occ", QOuter_Path,
      Ands [
        defined_recursively (Variable "func1_occ"),
        Is_Rule_Of_Node (Variable "rule", Variable "func1_occ"),
        Some ("func2_occ", QOuter_Path,
          Ands [
            defined_recursively (Variable "func2_occ"),
            Is_Rule_Of_Node (Variable "rule", Variable "func2_occ"),
            Have_Different_Prnts (Variable "func1_occ", Variable "func2_occ"),
            Some ("arg_of_func1_occ", QOuter_Path,
              Ands [
                Is_An_Arg_Of (Variable "arg_of_func1_occ", Variable "func1_occ"),
                Is_Path_Below (Variable "func2_occ", Variable "arg_of_func1_occ"),
                unique
              ]
            )
          ]
        )
      ]
    )
  )

(*functional induction on inner constant*) (*TODO: test*)
val lifter_15 =
  lifter_15_shared lifter_15_assumption
Imply
  lifter_15_shared lifter_15_conclusion;

(*rule inversion on a function in a premise*)(*TODO: test*)
val lifter_20 =
  Ands [
    Some ("rule", QRule, True),
    Some ("inductive_occ", QOuter_Path,
      Ands [
        Is_Defined_With (Variable "inductive_occ",  Command Inductive),
        Is_A_Meta_Premise_Or_Below (Variable "inductive_occ")
      ]
    )
  ]
Imply
  Some ("rule", QRule,
    Some ("inductive_occ", QOuter_Path,
      Ands [
        Is_Defined_With (Variable "inductive_occ",  Command Inductive),
        Is_A_Meta_Premise_Or_Below (Variable "inductive_occ"),
        Is_Rule_Of_Node (Variable "rule", Variable "induct_occ")
      ]
    )
  );

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
        defined_recursively (Variable "func_occ"),
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

fun is_variable var =
  Ors [
    Is_Free  var,
    Is_Var   var,
    Is_Bound var
  ]

val nth_parameter_is_used_in_mth_argument_in_recursive_call =
Lambdas (["func", "recursive_on_nth", "mth"],
  Ands [
    Some ("root_path", QInner_Path,
      Ands [
        Is_Root_In_A_Location (Variable "root_path"),
        Some ("lhs_path", QInner_Path,
          Ands [
            Is_Nth_Child_Of (Variable "lhs_path", Number 1, Variable "root_path"),
            Some ("rhs_path", QInner_Path,
              Ands [
                Is_Nth_Child_Of (Variable "rhs_path", Number 2, Variable "root_path"),
                Some ("part_of_nth_param_on_lhs_that_causes_ind", QInner_Path,
                  Ands [
                    is_variable (Variable "part_of_nth_param_on_lhs_that_causes_ind"),
                    (*Maybe it is better to use Is_N_Plus_One_th_Child_Or_Below_N_Plus_One_th_Child_Of instead?*)
                    Is_Below_N_Plus_One_th_Child_Of (Variable "part_of_nth_param_on_lhs_that_causes_ind", Variable "recursive_on_nth", Variable "lhs_path"),
                    Debug_Non_Path_Literal (Print "part_of_nth_param_on_lhs is"),
                    Debug_Print_Unode      (Variable "part_of_nth_param_on_lhs_that_causes_ind"),
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
                                    is_variable (Variable "part_of_nth_param_on_lhs_that_causes_arb"),
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

val generalize_arguments_used_in_recursion =
  Some ("ind", QInd,
    Some_Of ("ind_occ", Variable "ind",
      Some ("func", QOuter_Print,
        Some_Of ("func_occ", Variable "func",
          Ands [
            defined_recursively (Variable "func_occ"),
            Is_An_Arg_Or_Below_Arg_Of (Variable "ind_occ", Variable "func_occ"),
            Some ("recursive_on_nth_param", QOuter_Number,
              Ands [
                Takes_Less_Than_N_Arguments (Variable "func_occ", Variable "recursive_on_nth_param"),
                Some ("used_to_update_mth_arg", QOuter_Number,
                  Ands [
                    Not (Are_Same_Number (Variable "recursive_on_nth_param", Variable "used_to_update_mth_arg")),
                    Takes_Less_Than_N_Arguments (Variable "func_occ", Variable "used_to_update_mth_arg"),
                    Debug_Print_Unode (Variable "func_occ"),
                    Debug_Non_Path_Literal (Variable "recursive_on_nth_param"),
                    Debug_Non_Path_Literal (Variable "used_to_update_mth_arg"),
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
            defined_recursively (Variable "func_occ"),
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
                    Debug_Print_Unode (Variable "func_occ"),
                    Debug_Non_Path_Literal (Variable "recursive_on_nth_param"),
                    Debug_Non_Path_Literal (Variable "used_to_update_mth_arg"),
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

end;