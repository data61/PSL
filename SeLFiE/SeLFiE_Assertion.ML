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
        [Node_Is_App (Variable "func_app"),
         Is_Nth_Child_Of (Variable "func", Number 0, Variable "func_app")
         ]));

val is_constant =
  Lambdas (["constant"], Node_Is_Cnst (Variable "constnat"));

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
      Is_Atomic (Variable "xs_occ")
    Imply
      Is_At_Deepest_In_A_Location (Variable "xs_occ")
  ));

(*defined_recursively*)
val print_defined_recursively =
Lambdas (["func_trm"],
  Ors [
    Print_Is_Defined_With (Variable "func_trm", Command Fun),
    Print_Is_Defined_With (Variable "func_trm", Command Function),
    Print_Is_Defined_With (Variable "func_trm", Command Primrec),
    Print_Is_Defined_With (Variable "func_trm", Command Inductive)
  ]
);

val node_defined_recursively =
Lambdas (["func_occ"],
  Ors [
    Node_Is_Defined_With (Variable "func_occ", Command Fun),
    Node_Is_Defined_With (Variable "func_occ", Command Function),
    Node_Is_Defined_With (Variable "func_occ", Command Primrec),
    Node_Is_Defined_With (Variable "func_occ", Command Inductive)
  ]
);

val lifter_3 =
Some ("func_occ", QOuter_Path,
  Ands [
    Applies (node_defined_recursively, [Variable "func_occ"]),
    All ("ind", QInd,
      Some_Of ("ind_occ", Variable "ind",
        Ands [
          Is_An_Arg_Of (Variable "ind_occ", Variable "func_occ")
        ]
      )
    )
  ]
);

val nth_arg_on_lfs_is_const_or_app =
 Lambdas (["nth"], Debug_Non_Path_Literal (Variable "func"));

val help_test_dive_in =
 Lambdas (["func"],
  All ("printed", QInner_Print,
   Debug_Non_Path_Literal (Variable "printed")));

val test_dive_in =
All ("func_occ", QOuter_Path,
    Node_Is_Defined_With (Variable "func_occ", Command Fun)
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
      Node_Is_Defined_With (Variable "outer_path", Command Fun),
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

val lifter_4 =
  Not (Some ("rule", QRule, True))
Imply
  Some ("func", QOuter_Print,
    Ands [
      Applies (print_defined_recursively, [Variable "func"]),
      Some_Of ("func_occ", Variable "func",
        Ands [
          All ("induct", QInd,
            Some_Of ("ind_occ", Variable "induct",
              All ("number", QOuter_Number,
                  Ands [
                    Node_Takes_Less_Than_N_Arguments (Variable "func_occ", Variable "number"),
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
    ]
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
                  Node_Takes_Less_Than_N_Arguments (Variable "func_occ", Variable "numb"),
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
    Applies (print_defined_recursively, [Variable "func"])
  )
Imply
  Some ("func", QOuter_Print,
    Ands [
      Applies (print_defined_recursively, [Variable "func"]),
      Some_Of ("func_occ", Variable "func",
        Ands [
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
    ]
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
        Applies (node_defined_recursively, [Variable "func1_occ"]),
        Is_Rule_Of_Node (Variable "rule", Variable "func1_occ"),
        Some ("func2_occ", QOuter_Path,
          Ands [
            Applies (node_defined_recursively, [Variable "func2_occ"]),
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
        Node_Is_Defined_With (Variable "inductive_occ",  Command Inductive),
        Is_A_Meta_Premise_Or_Below (Variable "inductive_occ")
      ]
    )
  ]
Imply
  Some ("rule", QRule,
    Some ("inductive_occ", QOuter_Path,
      Ands [
        Node_Is_Defined_With (Variable "inductive_occ",  Command Inductive),
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
    Node_Is_Free  (Variable "variable"),
    Node_Is_Var   (Variable "variable"),
    Node_Is_Bound (Variable "variable")
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

val for_all_arbs_there_should_be_a_change =
All ("arb_trm", QArb,
    True(*TODO: No syntactic heuristics indicate "arb_trm" should be generalized.*)
  Imply
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
                    Is_Nth_Arg_Or_Below_Nth_Arg_Of (Variable "ind_occ", Variable "func_is_recurse_on_nth", Variable "func_trm_occ"),(*Does this actually harm us?*)
                    Some_Of ("arb_trm_occ", Variable "arb_trm",
                      Some ("mth_arg_of_func_occ_has_arb", QOuter_Number,
                        Ands [
                          Node_Takes_Less_Than_N_Arguments (Variable "func_trm_occ", Variable "mth_arg_of_func_occ_has_arb"),
                          Some_Of ("func_trm_occ2", Variable "func_trm", (*we do not always talk about the same occurrence of the function. See addO_exp\<omega>_inj in Goodstein_Lambda.thy where we have to deal with two different occurrences of add0.*)
                            Ands [
                            Is_Nth_Arg_Or_Below_Nth_Arg_Of (Variable "arb_trm_occ", Variable "mth_arg_of_func_occ_has_arb", Variable "func_trm_occ2"),
                            ( Is_Same_Path_As (Variable "func_trm_occ", Variable "func_trm_occ2")
                            Imply
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
                        Is_Path_Below   (Variable "func_occ_on_rhs", Variable "rhs_path"),
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
    Ands [
      Applies (print_defined_recursively, [Variable "func"]),
      Some_Of ("func_occ", Variable "func",
        Ands [
          All ("induct", QInd,
            Some_Of ("ind_occ", Variable "induct",
              Some ("number", QOuter_Number,
                Ands [
                  Node_Takes_Less_Than_N_Arguments (Variable "func_occ", Variable "number"),
                  Is_Nth_Arg_Of (Variable "ind_occ", Variable "number", Variable "func_occ"),
                  In_Some_Definitions (Variable "func", is_defined_recursively_on_nth, [Variable "func", Variable "number"])
                ]
              )
            )
          )
        ]
      )
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
                    (*Maybe it is better to use Is_N_Plus_One_th_Child_Or_Below_N_Plus_One_th_Child_Of instead?*)
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

val generalize_arguments_used_in_recursion =
  Some ("ind", QInd,
    Some_Of ("ind_occ", Variable "ind",
      Some ("func", QOuter_Print,
        Ands [
          Applies (print_defined_recursively, [Variable "func"]),
          Some_Of ("func_occ", Variable "func",
            Ands [
              Is_An_Arg_Or_Below_Arg_Of (Variable "ind_occ", Variable "func_occ"),
              Some ("recursive_on_nth_param", QOuter_Number,
                Ands [
                  Node_Takes_Less_Than_N_Arguments (Variable "func_occ", Variable "recursive_on_nth_param"),
                  In_Some_Definitions (
                    Variable "func",
                    is_defined_recursively_on_nth,
                    [Variable "func", Variable "recursive_on_nth_param"]
                  ),
                  Some ("used_to_update_mth_arg", QOuter_Number,
                    Ands [
                      Not (Are_Same_Number (Variable "recursive_on_nth_param", Variable "used_to_update_mth_arg")),
                      Node_Takes_Less_Than_N_Arguments (Variable "func_occ", Variable "used_to_update_mth_arg"),
                      Ors [
                        In_Some_Definitions ((*This conjunction is a loser condition than nth_parameter_is_used_in_mth_argument_in_recursive_call alone.*)
                          Variable "func",
                          mth_arg_of_func_occ_has_different_print,
                          [Variable "used_to_update_mth_arg", Variable "func"]
                        )(*,
                        In_Some_Definitions (
                          Variable "func",
                          nth_parameter_is_used_in_mth_argument_in_recursive_call,
                          [Variable "func", Variable "recursive_on_nth_param", Variable "used_to_update_mth_arg"]
                        )
*)
                      ]
                    ]
                  )
                ]
              ),
              Debug_Non_Path_Literal (Print "===Assumption is done===")
            ]
          )
        ]
      )
    )
  )
Imply
  All ("ind", QInd,(*!*)(*Now we check for all induction terms.*)
    Some_Of ("ind_occ", Variable "ind",
      Some ("func", QOuter_Print,
        Ands [
          Applies (print_defined_recursively, [Variable "func"]),
          Some_Of ("func_occ", Variable "func",
            Ands [
              Is_An_Arg_Or_Below_Arg_Of (Variable "ind_occ", Variable "func_occ"),
              Some ("recursive_on_nth_param", QOuter_Number,
                Ands [
                  Node_Takes_Less_Than_N_Arguments (Variable "func_occ", Variable "recursive_on_nth_param"),
                  In_Some_Definitions (
                    Variable "func",
                    is_defined_recursively_on_nth,
                    [Variable "func", Variable "recursive_on_nth_param"]
                  ),
                  Some ("used_to_update_mth_arg", QOuter_Number,
                    Ands [
                      Node_Takes_Less_Than_N_Arguments (Variable "func_occ", Variable "used_to_update_mth_arg"),
                      Not (Are_Same_Number (Variable "recursive_on_nth_param", Variable "used_to_update_mth_arg")),
                      Some ("arb", QArb, (*!*)
                      (*TODO: Maybe it is better to have All ("arb", QArb, Ors [generalization heuristics based on syntax, this heuristics.])*)
                        Some_Of ("arb_occ", Variable "arb",
                          Is_Nth_Arg_Or_Below_Nth_Arg_Of (Variable "arb_occ", Variable "used_to_update_mth_arg", Variable "func_occ")
                        )
                      ),
                      Ors [
                        In_Some_Definitions ((*This conjunction is a loser condition than nth_parameter_is_used_in_mth_argument_in_recursive_call alone.*)
                          Variable "func",
                          mth_arg_of_func_occ_has_different_print,
                          [Variable "used_to_update_mth_arg", Variable "func"]
                        )(*,
                        In_Some_Definitions (
                          Variable "func",
                          nth_parameter_is_used_in_mth_argument_in_recursive_call,
                          [Variable "func", Variable "recursive_on_nth_param", Variable "used_to_update_mth_arg"]
                        )*)
                      ]
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

val ind_on_lhs_of_eq_then_arb_on_rhs_of_eq =
  Some ("hol_eq_occ", QOuter_Path,
    Ands [
      Unode_Has_Print (Variable "hol_eq_occ", Print "HOL.eq"),
      Some ("ind_trm", QInd,
        Some_Of ("ind_occ", Variable "ind_trm",
          Ands [
            Applies (is_variable, [Variable "ind_occ"]),
            Is_Nth_Arg_Of (Variable "ind_occ", Number 0, Variable "hol_eq_occ"),
            Some ("arb_occ", QOuter_Path,
              Ands [
                Applies (is_variable, [Variable "arb_occ"]),
                Not (Unode_Has_Print (Variable "arb_occ", Variable "ind_trm")),
                Is_Nth_Arg_Of (Variable "arb_occ", Number 1, Variable "hol_eq_occ")
              ]
            )
          ]
        )
      ),
    Debug_Non_Path_Literal (Print "Assumption is done")
    ]
  )
Imply
  Some ("hol_eq_occ", QOuter_Path,
    Ands [
      Unode_Has_Print (Variable "hol_eq_occ", Print "HOL.eq"),
      Some ("ind_trm", QInd,
        Some_Of ("ind_occ", Variable "ind_trm",
          Ands [
            Applies (is_variable, [Variable "ind_occ"]),
            Is_Nth_Arg_Of (Variable "ind_occ", Number 0, Variable "hol_eq_occ"),
            Some ("arb_trm", QArb,(*!*)
              Some_Of ("arb_occ", Variable "arb_trm",(*!*)
                Ands [
                  Is_Nth_Arg_Of (Variable "arb_occ", Number 1, Variable "hol_eq_occ")
                ]
              )
            )
          ]
        )
      )
    ]
  )
;

val if_one_of_lhs_n_rhs_of_eq_is_induct_then_induct_on_lhs =
  Some ("hol_eq_occ", QOuter_Path,
    Ands [
      Unode_Has_Print (Variable "hol_eq_occ", Print "HOL.eq"),
      Some ("ind_trm1", QInd,
        Some_Of ("ind_occ1", Variable "ind_trm1",
          Ors [
            Ands [(*induct only on the LHS of the equation*)
              Is_Nth_Arg_Of (Variable "ind_occ1", Number 0, Variable "hol_eq_occ"),
              Not (
                Some ("ind_trm2", QInd,
                  Some_Of ("ind_occ2", Variable "ind_trm2",
                    Is_Nth_Arg_Of (Variable "ind_occ2", Number 1, Variable "hol_eq_occ")
                  )
                )
              )
            ],
            Ands [(*induct only on the RHS of the equation*)
              Is_Nth_Arg_Of (Variable "ind_occ1", Number 1, Variable "hol_eq_occ"),
              Not (
                Some ("ind_trm2", QInd,
                  Some_Of ("ind_occ2", Variable "ind_trm2",
                    Is_Nth_Arg_Of (Variable "ind_occ2", Number 0, Variable "hol_eq_occ")
                  )
                )
              )
            ]
          ]
        )
      )
    ]
  )
Imply
  Some ("hol_eq_occ", QOuter_Path,
    Ands [
      Unode_Has_Print (Variable "hol_eq_occ", Print "HOL.eq"),
      Some ("ind_trm1", QInd,
        Some_Of ("ind_occ1", Variable "ind_trm1",
          Ors [
            Ands [(*induct only on the LHS of the equation*)
              Is_Nth_Arg_Of (Variable "ind_occ1", Number 0, Variable "hol_eq_occ"),
              Not (
                Some ("ind_trm2", QInd,
                  Some_Of ("ind_occ2", Variable "ind_trm2",
                    Is_Nth_Arg_Of (Variable "ind_occ2", Number 1, Variable "hol_eq_occ")
                  )
                )
              )
            ]
          ]
        )
      )
    ]
  )

val if_part_of_lhs_n_part_of_rhs_of_eq_is_induct_then_induct_on_part_of_lhs =
  Some ("hol_eq_occ", QOuter_Path,
    Ands [
      Unode_Has_Print (Variable "hol_eq_occ", Print "HOL.eq"),
      Some ("ind_trm1", QInd,
        Some_Of ("ind_occ1", Variable "ind_trm1",
          Ors [
            Ands [(*induct only on the LHS of the equation*)
              Is_Nth_Arg_Or_Below_Nth_Arg_Of (Variable "ind_occ1", Number 0, Variable "hol_eq_occ"),
              Not (
                Some ("ind_trm2", QInd,
                  Some_Of ("ind_occ2", Variable "ind_trm2",
                    Is_Nth_Arg_Or_Below_Nth_Arg_Of (Variable "ind_occ2", Number 1, Variable "hol_eq_occ")
                  )
                )
              )
            ],
            Ands [(*induct only on the RHS of the equation*)
              Is_Nth_Arg_Or_Below_Nth_Arg_Of (Variable "ind_occ1", Number 1, Variable "hol_eq_occ"),
              Not (
                Some ("ind_trm2", QInd,
                  Some_Of ("ind_occ2", Variable "ind_trm2",
                    Is_Nth_Arg_Or_Below_Nth_Arg_Of (Variable "ind_occ2", Number 0, Variable "hol_eq_occ")
                  )
                )
              )
            ]
          ]
        )
      )
    ]
  )
Imply
  Some ("hol_eq_occ", QOuter_Path,
    Ands [
      Unode_Has_Print (Variable "hol_eq_occ", Print "HOL.eq"),
      Some ("ind_trm1", QInd,
        Some_Of ("ind_occ1", Variable "ind_trm1",
          Ors [
            Ands [(*induct only on the LHS of the equation*)
              Is_Nth_Arg_Or_Below_Nth_Arg_Of (Variable "ind_occ1", Number 0, Variable "hol_eq_occ"),
              Not (
                Some ("ind_trm2", QInd,
                  Some_Of ("ind_occ2", Variable "ind_trm2",
                    Is_Nth_Arg_Or_Below_Nth_Arg_Of (Variable "ind_occ2", Number 1, Variable "hol_eq_occ")
                  )
                )
              )
            ]
          ]
        )
      )
    ]
  )

end;