(*  Title:      PSL/SeLFiE/src/Interface/SeLFiE_Assertion.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
(*** signature: ASSERTION_INDUCT ***)
signature ASSERTION_INDUCT =
sig

val lifter2_improved                                                                                                                     : Eval_Syntactic_Sugar.assert;
val lifter_3_improved                                                                                                                    : Eval_Syntactic_Sugar.assert;
val lifter_5                                                                                                                             : Eval_Syntactic_Sugar.assert;
val lifter_7                                                                                                                             : Eval_Syntactic_Sugar.assert;
val lifter_8                                                                                                                             : Eval_Syntactic_Sugar.assert;
val lifter_9_improved                                                                                                                    : Eval_Syntactic_Sugar.assert;
val lifter_11                                                                                                                            : Eval_Syntactic_Sugar.assert;
val lifter_15                                                                                                                            : Eval_Syntactic_Sugar.assert;
val lifter_20                                                                                                                            : Eval_Syntactic_Sugar.assert;
val is_defined_recursively_on_nth_outer                                                                                                  : Eval_Syntactic_Sugar.assert;
val is_defined_recursively_on_nth                                                                                                        : Eval_Syntactic_Sugar.assert;
val if_part_of_lhs_n_part_of_rhs_of_eq_is_induct_then_induct_on_part_of_lhs                                                              : Eval_Syntactic_Sugar.assert;
val outer_induct_on_arg_of_set_member_n_set_outer                                                                                        : Eval_Syntactic_Sugar.assert;
val induct_on_arg_of_set_member_n_set_syntax_only                                                                                        : Eval_Syntactic_Sugar.assert;
val induct_on_2nd_arg_of_map_outer                                                                                                       : Eval_Syntactic_Sugar.assert;
val structural_induction_on_an_arg_of_inductive_defined_constant_in_the_concl_of_meta_imp                                                : Eval_Syntactic_Sugar.assert;
val rule_inversion_using_the_deepest_const                                                                                               : Eval_Syntactic_Sugar.assert;
val complex_lhs_causes_functional_induction_outer                                                                                        : Eval_Syntactic_Sugar.assert;
val is_defined_recursively_on_nth_n_mth_by_two_funs                                                                                      : Eval_Syntactic_Sugar.assert;
val if_part_of_lhs_n_part_of_rhs_of_eq_is_induct_rule_then_induct_rule_on_part_of_lhs                                                    : Eval_Syntactic_Sugar.assert;
val all_ind_should_be_atom                                                                                                               : Eval_Syntactic_Sugar.assert;
val if_rule_induct_using_const_defined_with_inductive_set_in_snd_argument_of_membership_then_induct_on_var_in_fst_argument_of_membership : Eval_Syntactic_Sugar.assert;
val if_defined_with_inductive_set_in_meta_premise_then_set_induction                                                                     : Eval_Syntactic_Sugar.assert;
val trancl_induct                                                                                                                        : Eval_Syntactic_Sugar.assert;
val tranclp_induct                                                                                                                       : Eval_Syntactic_Sugar.assert;
val rtrancl_induct                                                                                                                       : Eval_Syntactic_Sugar.assert;
val rtranclp_induct                                                                                                                      : Eval_Syntactic_Sugar.assert;
val trancl_induct2                                                                                                                       : Eval_Syntactic_Sugar.assert;
val tranclp_induct2                                                                                                                      : Eval_Syntactic_Sugar.assert;
val rtrancl_induct2                                                                                                                      : Eval_Syntactic_Sugar.assert;
val rtranclp_induct2                                                                                                                     : Eval_Syntactic_Sugar.assert;
val if_two_occs_of_length_or_size_in_assum_or_chained_fact_then_list_induct2                                                             : Eval_Syntactic_Sugar.assert;
val rule_is_list_induct2'                                                                                                                : Eval_Syntactic_Sugar.assert;
val if_list_all2_then_list_all2_induct                                                                                                   : Eval_Syntactic_Sugar.assert;
val if_list_induct2'_then_two_induct_terms                                                                                               : Eval_Syntactic_Sugar.assert;
val if_not_equal_in_premise_or_chained_then_rev_nonempty_induct                                                                          : Eval_Syntactic_Sugar.assert;
val if_less_eq_in_premise_or_chained_but_not_nonempty_induct_then_inc_induct                                                             : Eval_Syntactic_Sugar.assert;
val if_less_or_less_eq_in_premise_or_chained_but_not_nonempty_induct_then_less_induct                                                    : Eval_Syntactic_Sugar.assert;

end

(*** structure: Assertion_Induct ***)
structure Assertion_Induct: ASSERTION_INDUCT =
struct

open SeLFiE_Util;
open Eval_Syntactic_Sugar;
open Definition_Pattern;

val condition_to_deepest_heuristic =
  Not (
    Some ("set", QOuter_Print,
      Ands [
        Are_Same_Prints (Variable "set", Print "List.list.set"),
        Some ("hol_quantifier", QOuter_Print,
          Ors [
            Are_Same_Prints (Variable "hol_quantifier", Print "HOL.All"),
            Are_Same_Prints (Variable "hol_quantifier", Print "HOL.Ex" ),
            Are_Same_Prints (Variable "hol_quantifier", Print "Set.Ball"),
            Are_Same_Prints (Variable "hol_quantifier", Print "Set.Bex" ),
            Are_Same_Prints (Variable "hol_quantifier", Print "Set.Bex1"),
            Are_Same_Prints (Variable "hol_quantifier", Print "Set.Bleast")
          ]
        )
      ]
    )
  );

val lifter2_improved =
Imply (
  condition_to_deepest_heuristic,
  All ("xs", QInd,
    Some_Of ("xs_occ", Variable "xs",
      Imply (
        Is_Atomic (Variable "xs_occ"),
        Is_At_Deepest_In_A_Location (Variable "xs_occ")
      )
    )
  )
);

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

val node_defined_recursively =
Lambdas (["func_occ"],
  Ors [
    Node_Is_Defined_With (Variable "func_occ", Command Fun),
    Node_Is_Defined_With (Variable "func_occ", Command Function),
    Node_Is_Defined_With (Variable "func_occ", Command Primrec)(*,
    Node_Is_Defined_With (Variable "func_occ", Command Inductive)*)
  ]
);

val print_defined_inductively =
Lambdas (["func_term"],
  Ors [
    Print_Is_Defined_With (Variable "func_term", Command Inductive),
    Print_Is_Defined_With (Variable "func_term", Command Inductive_Set)
  ]
);

val lifter_3_improved =
Imply (
  Not (
    Some ("inductively_defined_term", QOuter_Print,
      Applies (print_defined_inductively, [Variable "inductively_defined_term"])
    )
  ),
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
  )
);

val lifter_5 =
Imply (
  Some ("rule", QRule, True),
  Some ("rule", QRule,
    Some ("func", QOuter_Print,
      Some_Of ("func_occ", Variable "func",
        Ands [
          Is_Rule_Of_Print (Variable "rule", Variable "func"),
          All ("ind", QInd,
            Some_Of ("arg_occ", Variable "ind",
              Some ("numb", QOuter_Number,
                Ands [
                  Node_Takes_More_Than_N_Arguments (Variable "func_occ", Variable "numb"),
                  Is_Nth_Argument_Of (Variable "arg_occ", Variable "numb", Variable "func_occ"),
                  Is_Nth_Induct (Variable "ind", Variable "numb")
                ]
              )
            )
          )
        ]
      )
    )
  )
);


val lifter_7 =
Imply (
  Ands [
    Not (
      Some ("inductively_defined_term", QOuter_Print,
        Applies (print_defined_inductively, [Variable "inductively_defined_term"])
      )
    ),
    Some ("func", QOuter_Print,
      Applies (print_defined_recursively, [Variable "func"])
    )
  ],
  Some ("func", QOuter_Print,
    Ands [
      Applies (print_defined_recursively, [Variable "func"]),
      Some_Of ("func_occ", Variable "func",
        Ands [
          Some ("induct_arg", QInd,
            Some_Of ("induct_arg_occ", Variable "induct_arg",
              Ands [
                Is_An_Argument_Of (Variable "induct_arg_occ",  Variable "func_occ")
              ]
            )
          )
        ]
      )
    ]
  )
);

val lifter_8 = Some ("induct", QInd, True);

val lifter_9_improved =
Imply (
  Ands [
    condition_to_deepest_heuristic,
    Some ("induct_arg", QInd, True),
    All ("induct_arg", QInd,
      Some_Of ("induct_arg_occ", Variable "induct_arg",
        Is_Atomic (Variable "induct_arg_occ")
      )
    )
  ],
  Some ("induct_arg", QInd,
    Some_Of ("induct_arg_occ", Variable "induct_arg",
      Is_At_Deepest_In_A_Location (Variable "induct_arg_occ")
    )
  )
);

(*all arguments rule-function are induction variable*)
val lifter_11 =
Imply (
  Some ("rule", QRule, True),
  Some ("rule", QRule,
    Some ("func", QOuter_Print,
      Ands [
        Is_Rule_Of_Print (Variable "rule",  Variable "func"),
        Some_Of ("func_occ", Variable "func",
          All ("arg_occ", QOuter_Path,
            Imply (
              Ands [
                Are_In_Same_Location (Variable "arg_occ", Variable "func_occ"),
                Is_An_Argument_Of (Variable "arg_occ", Variable "func_occ")
              ],
              Some ("ind", QInd,
                Unode_Has_Print (Variable "arg_occ", Variable "ind")
              )
            )
          )
        )
      ]
    )
  )
);

local

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
                Is_An_Argument_Of (Variable "arg_of_func1_occ", Variable "func1_occ"),
                Is_Path_Below (Variable "func2_occ", Variable "arg_of_func1_occ"),
                unique
              ]
            )
          ]
        )
      ]
    )
  )

in

(*functional induction on inner constant*) (*TODO: test*)
val lifter_15 =
Imply (
  lifter_15_shared lifter_15_assumption,
  lifter_15_shared lifter_15_conclusion
);

end

(*rule inversion on a function in a premise*)(*TODO: test*)
val lifter_20 =
Imply (
  Ands [
    Some ("rule", QRule, True),
    Some ("inductive_occ", QOuter_Path,
      Ands [
        Node_Is_Defined_With (Variable "inductive_occ",  Command Inductive),
        Is_A_Meta_Premise_Or_Below (Variable "inductive_occ")
      ]
    )
  ],
  Some ("rule", QRule,
    Some ("inductive_occ", QOuter_Path,
      Ands [
        Node_Is_Defined_With (Variable "inductive_occ",  Command Inductive),
        Is_A_Meta_Premise_Or_Below (Variable "inductive_occ"),
        Is_Rule_Of_Node (Variable "rule", Variable "inductive_occ")
      ]
    )
  )
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

in

val is_defined_recursively_on_nth_outer =
Imply (
  Ands [
    Not (Some ("rule", QRule, True)),
    Some ("func", QOuter_Print,
      Ands [
        Applies (print_defined_recursively, [Variable "func"]),
        Some_Of ("func_occ", Variable "func",
          Ands [
            Some ("arg_occ", QOuter_Path,
              Some ("number", QOuter_Number,
                Ands [
                  Node_Takes_More_Than_N_Arguments (Variable "func_occ", Variable "number"),
                  Is_Nth_Argument_Of (Variable "arg_occ", Variable "number", Variable "func_occ"),
                  In_Some_Definitions (Variable "func", is_defined_recursively_on_nth, [Variable "func", Variable "number"])
                ]
              )
            )
          ]
        )
      ]
    )
  ],
  Some ("func", QOuter_Print,
    Ands [
      Applies (print_defined_recursively, [Variable "func"]),
      Some_Of ("func_occ", Variable "func",
        Ands [
          All ("induct", QInd,
            Some_Of ("ind_occ", Variable "induct",
              Some ("number", QOuter_Number,
                Ands [
                  Node_Takes_More_Than_N_Arguments (Variable "func_occ", Variable "number"),
                  Is_Nth_Argument_Of (Variable "ind_occ", Variable "number", Variable "func_occ"),
                  In_Some_Definitions (Variable "func", is_defined_recursively_on_nth, [Variable "func", Variable "number"])
                ]
              )
            )
          )
        ]
      )
    ]
  )
);

end


local

val is_lhs_of_root =(*TODO: we do not need root here.*)
Lambdas (["lhs_path", "root_path"],
  Ands [
    Is_Root_In_A_Location (Variable "root_path"),
    Is_Nth_Child_Of (Variable "lhs_path", Number 1, Variable "root_path")
  ]
);

in

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

end;

val is_defined_recursively_on_nth_n_mth_by_two_funs =
Imply (
  Ands [
    Not (Some ("rule", QRule, True)),
    Some ("func1_term", QOuter_Print,
      Ands [
        Applies (print_defined_recursively, [Variable "func1_term"]),
        Some ("func2_occ_is_below_nth_arg_of_func1_occ", QOuter_Number,
          Ands [
            Print_Takes_More_Than_N_Arguments (Variable "func1_term", Variable "func2_occ_is_below_nth_arg_of_func1_occ"),
            In_Some_Definitions (Variable "func1_term", is_defined_recursively_on_nth, [Variable "func1_term", Variable "func2_occ_is_below_nth_arg_of_func1_occ"]),
            Some_Of ("func1_occ", Variable "func1_term",
              Ands [
                Some ("func2_term", QOuter_Print,
                  Ands [
                    Applies (print_defined_recursively, [Variable "func2_term"]),
                    Some ("ind_occ_is_below_nth_arg_of_func2_occ", QOuter_Number,
                      Ands [
                        Print_Takes_More_Than_N_Arguments (Variable "func2_term", Variable "ind_occ_is_below_nth_arg_of_func2_occ"),
                        In_Some_Definitions (Variable "func2_term", is_defined_recursively_on_nth, [Variable "func2_term", Variable "ind_occ_is_below_nth_arg_of_func2_occ"]),
                        Some_Of ("func2_occ", Variable "func2_term",
                          Ands [
                            Is_Nth_Argument_Or_Below_Nth_Argument_Of (Variable "func2_occ", Variable "func2_occ_is_below_nth_arg_of_func1_occ", Variable "func1_occ")
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
  ],
  Some ("func1_term", QOuter_Print,
    Ands [
      Applies (print_defined_recursively, [Variable "func1_term"]),
      Some ("func2_occ_is_below_nth_arg_of_func1_occ", QOuter_Number,
        Ands [
          Print_Takes_More_Than_N_Arguments (Variable "func1_term", Variable "func2_occ_is_below_nth_arg_of_func1_occ"),
          In_Some_Definitions (Variable "func1_term", is_defined_recursively_on_nth, [Variable "func1_term", Variable "func2_occ_is_below_nth_arg_of_func1_occ"]),
          Some_Of ("func1_occ", Variable "func1_term",
            Ands [
              Some ("func2_term", QOuter_Print,
                Ands [
                  Applies (print_defined_recursively, [Variable "func2_term"]),
                  Some ("ind_occ_is_below_nth_arg_of_func2_occ", QOuter_Number,
                    Ands [
                      Print_Takes_More_Than_N_Arguments (Variable "func2_term", Variable "ind_occ_is_below_nth_arg_of_func2_occ"),
                      In_Some_Definitions (Variable "func2_term", is_defined_recursively_on_nth, [Variable "func2_term", Variable "ind_occ_is_below_nth_arg_of_func2_occ"]),
                      Some_Of ("func2_occ", Variable "func2_term",
                        Ands [
                          Is_Nth_Argument_Or_Below_Nth_Argument_Of (Variable "func2_occ", Variable "func2_occ_is_below_nth_arg_of_func1_occ", Variable "func1_occ"),
                          All ("ind_term", QInd,
                            Some_Of ("ind_occ", Variable "ind_term",
                              Is_Nth_Argument_Or_Below_Nth_Argument_Of (Variable "ind_occ", Variable "ind_occ_is_below_nth_arg_of_func2_occ", Variable "func2_occ")
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
        ]
      )
    ]
  )
);

val if_part_of_lhs_n_part_of_rhs_of_eq_is_induct_then_induct_on_part_of_lhs =
Imply (
  Some ("hol_eq_occ1", QOuter_Path,
    Ands [
      Unode_Has_Print (Variable "hol_eq_occ1", Print "HOL.eq"),
      Some ("hol_eq_occ2", QOuter_Path,
        Ands [
          Unode_Has_Print (Variable "hol_eq_occ2", Print "HOL.eq"),
          Some ("ind_trm1", QInd,
            Some_Of ("ind_occ1", Variable "ind_trm1",
              Ors [
                Ands [(*induct only on the LHS of the equation*)
                  Is_Nth_Argument_Or_Below_Nth_Argument_Of (Variable "ind_occ1", Number 0, Variable "hol_eq_occ1"),
                  Not (
                    Some ("ind_trm2", QInd,
                      Some_Of ("ind_occ2", Variable "ind_trm2",
                        Is_Nth_Argument_Or_Below_Nth_Argument_Of (Variable "ind_occ2", Number 1, Variable "hol_eq_occ2")
                      )
                    )
                  )
                ],
                Ands [(*induct only on the RHS of the equation*)
                  Is_Nth_Argument_Or_Below_Nth_Argument_Of (Variable "ind_occ1", Number 1, Variable "hol_eq_occ1"),
                  Not (
                    Some ("ind_trm2", QInd,
                      Some_Of ("ind_occ2", Variable "ind_trm2",
                        Is_Nth_Argument_Or_Below_Nth_Argument_Of (Variable "ind_occ2", Number 0, Variable "hol_eq_occ2")
                      )
                    )
                  )
                ]
              ]
            )
          )
        ]
      )
    ]
  ),
  Some ("hol_eq_occ", QOuter_Path,
    Ands [
      Unode_Has_Print (Variable "hol_eq_occ", Print "HOL.eq"),
      Some ("ind_trm1", QInd,
        Some_Of ("ind_occ1", Variable "ind_trm1",
          Ors [
            Ands [(*induct only on the LHS of the equation*)
              Is_Nth_Argument_Or_Below_Nth_Argument_Of (Variable "ind_occ1", Number 0, Variable "hol_eq_occ"),
              Not (
                Some ("ind_trm2", QInd,
                  Some_Of ("ind_occ2", Variable "ind_trm2",
                    Is_Nth_Argument_Or_Below_Nth_Argument_Of (Variable "ind_occ2", Number 1, Variable "hol_eq_occ")
                  )
                )
              )
            ]
          ]
        )
      )
    ]
  )
);

val induct_on_arg_of_setmember_n_set_inner =
Lambdas (["nth"],
  Some ("root_path", QInner_Path,
    Ands [
      Is_Root_In_A_Location (Variable "root_path"),
      Some ("lhs_path", QInner_Path,
        Ands [
          Is_Nth_Child_Of (Variable "lhs_path", Number 1, Variable "root_path"),
          Some ("nth_param_on_lhs_path", QInner_Path,
            Ands [
              Is_N_Plus_One_th_Child_Or_Below_N_Plus_One_th_Child_Of (Variable "nth_param_on_lhs_path", Variable "nth", Variable "lhs_path"),
              Some ("rhs_path", QInner_Path,
                Ands [
                  Is_Nth_Child_Of (Variable "rhs_path", Number 2, Variable "root_path"),
                  Some ("nth_param_on_rhs_path", QInner_Path,
                    Ands [
                      Is_Path_Below (Variable "nth_param_on_rhs_path", Variable "rhs_path"),
                      Has_Same_Prnt_As (Variable "nth_param_on_lhs_path", Variable "nth_param_on_rhs_path"),
                      Some ("set_member", QInner_Path,
                        Ands [
                          Unode_Has_Print (Variable "set_member", Print "Set.member"),
                          Some ("set", QInner_Path,
                            Ands [
                              Unode_Has_Print (Variable "set", Print "List.list.set"),
                              Is_Nth_Argument_Or_Below_Nth_Argument_Of      (Variable "set", Number 1, Variable "set_member"),
                              Is_An_Argument_Or_Below_Argument_Of (Variable "nth_param_on_rhs_path", Variable "set")
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
);

val has_set_and_set_member_in_definition =
Lambdas (["to_be_ignored"],
  Ands [
    Some ("set",        QInner_Print, Are_Same_Prints (Variable "set",        Print "List.list.set")),
    Some ("set_member", QInner_Print, Are_Same_Prints (Variable "set_member", Print "Set.member"   ))
  ]
);

val outer_induct_on_arg_of_set_member_n_set_outer =
Imply (
  Ands [
    Some ("ind", QInd, True),
    Not (Some ("rule", QRule, True)),
    Some ("func", QOuter_Print,
        Ands [
          Print_Is_Cnst (Variable "func"),
          In_Some_Definitions (
            Variable "func",
            has_set_and_set_member_in_definition,
            [Variable "func"]
          )
        ]
    )
  ],
  Some ("func", QOuter_Print,
    Ands [
      Print_Is_Cnst (Variable "func"),
      In_Some_Definitions (
        Variable "func",
        has_set_and_set_member_in_definition,
        []
      ),
      All ("ind", QInd, (*!*)
        Ands [
          Some_Of ("func_occ", Variable "func",
            Ands [
              Some_Of ("ind_occ", Variable "ind",
                Ands [
                  Is_An_Argument_Or_Below_Argument_Of (Variable "ind_occ", Variable "func_occ"),
                  Some ("ind_occ_is_in_nth_arg_of_func_occ", QOuter_Number,
                    Ands [
                      Print_Takes_More_Than_N_Arguments (Variable "func", Variable "ind_occ_is_in_nth_arg_of_func_occ"),
                      Is_Nth_Argument_Or_Below_Nth_Argument_Of    (Variable "ind_occ", Variable "ind_occ_is_in_nth_arg_of_func_occ", Variable "func_occ"),
                      In_Some_Definitions (
                        Variable "func",
                        induct_on_arg_of_setmember_n_set_inner,
                        [Variable "ind_occ_is_in_nth_arg_of_func_occ"]
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

val induct_on_arg_of_set_member_n_set_syntax_only =
Imply (
  Ands [
    Some ("ind", QInd, True),
    Not (Some ("rule", QRule, True)),
    Some ("set",        QOuter_Print, Are_Same_Prints (Variable "set",        Print "List.list.set")),
    Some ("set_member", QOuter_Print, Are_Same_Prints (Variable "set_member", Print "Set.member"   ))
  ],
  Ands [
    Some ("set_member_occ", QOuter_Path,
      Ands [
        Unode_Has_Print (Variable "set_member_occ", Print "Set.member"),
        Some ("set_occ", QOuter_Path,
          Ands [
            Unode_Has_Print (Variable "set_occ", Print "List.list.set"),
            Is_Nth_Argument_Or_Below_Nth_Argument_Of (Variable "set_occ", Number 1, Variable "set_member_occ"),
            All ("ind", QInd, (*!*)
              Some_Of ("ind_occ", Variable "ind",
                Ands [
                  Is_An_Argument_Or_Below_Argument_Of (Variable "ind_occ", Variable "set_occ")
                ]
              )
            )
          ]
        )
      ]
    )
  ]
);

val induct_on_2nd_arg_of_map_inner =
Lambdas (["nth"],
  Some ("root_path", QInner_Path,
    Ands [
      Is_Root_In_A_Location (Variable "root_path"),
      Some ("lhs_path", QInner_Path,
        Ands [
          Is_Nth_Child_Of (Variable "lhs_path", Number 1, Variable "root_path"),
          Some ("nth_param_on_lhs_path", QInner_Path,
            Ands [
              Is_N_Plus_One_th_Child_Or_Below_N_Plus_One_th_Child_Of (Variable "nth_param_on_lhs_path", Variable "nth", Variable "lhs_path"),
              Some ("rhs_path", QInner_Path,
                Ands [
                  Is_Nth_Child_Of (Variable "rhs_path", Number 2, Variable "root_path"),
                  Some ("nth_param_on_rhs_path", QInner_Path,
                    Ands [
                      Is_Path_Below (Variable "nth_param_on_rhs_path", Variable "rhs_path"),
                      Has_Same_Prnt_As (Variable "nth_param_on_lhs_path", Variable "nth_param_on_rhs_path"),
                      Some ("map", QInner_Path,
                        Ands [
                          Unode_Has_Print (Variable "map", Print "List.list.map"),
                          Is_Nth_Argument_Or_Below_Nth_Argument_Of (Variable "nth_param_on_rhs_path", Number 1, Variable "map")
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

val has_map_in_definition =
Lambdas (["to_be_ignored"],
  Ands [
    Some ("map", QInner_Print,
      Ands [
        Are_Same_Prints (Variable "map", Print "List.list.map")
      ]
    )
  ]
);

val induct_on_2nd_arg_of_map_outer =
Imply (
  Ands [
    Some ("ind", QInd, True),
    Not (Some ("rule", QRule, True)),
    Some ("func", QOuter_Print,
        Ands [
          Print_Is_Cnst (Variable "func"),
          In_Some_Definitions (
            Variable "func",
            has_map_in_definition,
            [Variable "func"]
          )
        ]
    )
  ],
  Some ("func", QOuter_Print,
    Ands [
      Print_Is_Cnst (Variable "func"),
      In_Some_Definitions (
        Variable "func",
        has_map_in_definition,
        [Variable "func"]
      ),
      All ("ind", QInd, (*!*)
        Ands [
          Some_Of ("func_occ", Variable "func",
            Ands [
              Some_Of ("ind_occ", Variable "ind",
                Ands [
                  Is_An_Argument_Or_Below_Argument_Of (Variable "ind_occ", Variable "func_occ"),
                  Some ("ind_occ_is_in_nth_arg_of_func_occ", QOuter_Number,
                    Ands [
                      Print_Takes_More_Than_N_Arguments (Variable "func",    Variable "ind_occ_is_in_nth_arg_of_func_occ"),
                      Is_Nth_Argument_Or_Below_Nth_Argument_Of    (Variable "ind_occ", Variable "ind_occ_is_in_nth_arg_of_func_occ", Variable "func_occ"),
                      In_Some_Definitions (
                        Variable "func",
                        induct_on_2nd_arg_of_map_inner,
                        [Variable "ind_occ_is_in_nth_arg_of_func_occ"]
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

val structural_induction_on_an_arg_of_inductive_defined_constant_in_the_concl_of_meta_imp =
Imply (
  Some ("ind", QInd,
    Ands [
      Not (Some ("rule", QRule, True)),
      Some ("root", QOuter_Path,
        Ands [
          Is_Root_In_A_Location (Variable "root"),
          Some ("pure_imp", QOuter_Path,
            Ands [
              Unode_Has_Print (Variable "pure_imp", Print "Pure.imp"),
              Is_Child_Of     (Variable "pure_imp", Variable "root"),
              Some ("inductive_trm", QOuter_Print,
                Ands [
                  Ors [
                    Print_Is_Defined_With (Variable "inductive_trm", Command Inductive)
                  ],
                  Some ("pure_imp_has_n_args", QOuter_Number,
                    Ands [
                      Some ("nth_arg_of_pure_imp", QOuter_Path,
                        Ands [
                          Is_Nth_Argument_Of (Variable "nth_arg_of_pure_imp", Variable "pure_imp_has_n_args", Variable "pure_imp"),
                          All ("pure_imp_has_more_than_m_args", QOuter_Number,
                            Ands [
                              All ("mth_arg_of_pure_imp", QOuter_Path,
                                Ands [
                                  Imply (
                                    Is_Nth_Argument_Of (Variable "mth_arg_of_pure_imp", Variable "pure_imp_has_more_than_m_args", Variable "pure_imp"),
                                    Is_Less_Than_Or_Equal (Variable "pure_imp_has_more_than_m_args", Variable "pure_imp_has_n_args")
                                  )
                                ]
                              )
                            ]
                          ),
                          Some ("ind_occ_in_meta_cncl", QOuter_Path,
                            Ands [
                              Node_Is_Free (Variable "ind_occ_in_meta_cncl"),
                              Is_Path_Below (Variable "ind_occ_in_meta_cncl", Variable "nth_arg_of_pure_imp"),
                              All ("pure_imp_has_more_than_m_args", QOuter_Number,
                                Ands [
                                  Imply (
                                    Is_Less_Than (Variable "pure_imp_has_more_than_m_args", Variable "pure_imp_has_n_args"),
                                    Not (
                                      Some ("ind_occ_in_assumption", QOuter_Path,
                                        Ands [
                                          Has_Same_Prnt_As (Variable "ind_occ_in_meta_cncl", Variable "ind_occ_in_assumption"),
                                          Is_Nth_Argument_Or_Below_Nth_Argument_Of (Variable "ind_occ_in_assumption", Variable "pure_imp_has_more_than_m_args", Variable "pure_imp")
                                        ]
                                      )
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
                ]
              )
            ]
          )
        ]
      )
    ]
  ),
  All ("ind", QInd,(*!*)
    Ands [
      Not (Some ("rule", QRule, True)),
      Some ("root", QOuter_Path,
        Ands [
          Is_Root_In_A_Location (Variable "root"),
          Some ("pure_imp", QOuter_Path,
            Ands [
              Unode_Has_Print (Variable "pure_imp", Print "Pure.imp"),
              Is_Child_Of     (Variable "pure_imp", Variable "root"),
              Some ("inductive_trm", QOuter_Print,
                Ands [
                  Ors [
                    Print_Is_Defined_With (Variable "inductive_trm", Command Inductive)
                  ],
                  Some ("pure_imp_has_n_args", QOuter_Number,
                    Ands [
                      Some ("nth_arg_of_pure_imp", QOuter_Path,
                        Ands [
                          Is_Nth_Argument_Of (Variable "nth_arg_of_pure_imp", Variable "pure_imp_has_n_args", Variable "pure_imp"),
                          All ("pure_imp_has_more_than_m_args", QOuter_Number,
                            Ands [
                              All ("mth_arg_of_pure_imp", QOuter_Path,
                                Ands [
                                  Imply (
                                    Is_Nth_Argument_Of (Variable "mth_arg_of_pure_imp", Variable "pure_imp_has_more_than_m_args", Variable "pure_imp"),
                                    Is_Less_Than_Or_Equal (Variable "pure_imp_has_more_than_m_args", Variable "pure_imp_has_n_args")
                                  )
                                ]
                              )
                            ]
                          ),
                          Some_Of ("ind_occ_in_meta_cncl", Variable "ind",(*!*)
                            Ands [
                              Node_Is_Free (Variable "ind_occ_in_meta_cncl"),
                              Is_Path_Below (Variable "ind_occ_in_meta_cncl", Variable "nth_arg_of_pure_imp"),
                              All ("pure_imp_has_more_than_m_args", QOuter_Number,
                                Ands [
                                  Imply (
                                    Is_Less_Than (Variable "pure_imp_has_more_than_m_args", Variable "pure_imp_has_n_args"),
                                    Not (
                                      Some_Of ("ind_occ_in_assumption", Variable "ind",(*!*)
                                        Ands [
                                          Has_Same_Prnt_As (Variable "ind_occ_in_meta_cncl", Variable "ind_occ_in_assumption"),
                                          Is_Nth_Argument_Or_Below_Nth_Argument_Of (Variable "ind_occ_in_assumption", Variable "pure_imp_has_more_than_m_args", Variable "pure_imp")
                                        ]
                                      )
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
                ]
              )
            ]
          )
        ]
      )
    ]
  )
);

val rule_inversion_using_the_deepest_const =
Imply (
  Ands [
    condition_to_deepest_heuristic,
    Some ("rule", QRule,
      Some ("rec_occ1", QOuter_Path,
        Ands [
          Node_Is_Cnst (Variable "rec_occ1"),
          Is_Rule_Of_Node (Variable "rule", Variable "rec_occ1"),
          Some ("rec_occ2", QOuter_Path,
            Ands [
              Applies (node_defined_recursively, [Variable "rec_occ2"]),(*TODO: Double-check! This is not really a condition for rule inversion.*)
              Are_In_Same_Location (Variable "rec_occ1", Variable "rec_occ2"),
              Not (Has_Same_Prnt_As (Variable "rec_occ1", Variable "rec_occ2"))
            ]
          )
        ]
      )
    )
  ],
  Ands [
    Some ("rule", QRule,
      Some ("rec_occ1", QOuter_Path,
        Ands [
          Is_Rule_Of_Node (Variable "rule", Variable "rec_occ1"),
          All ("rec_occ2", QOuter_Path,(*!*)
            Imply (
              Ands [
                Applies (node_defined_recursively, [Variable "rec_occ2"]),
                Are_In_Same_Location (Variable "rec_occ1", Variable "rec_occ2"),
                Not (Has_Same_Prnt_As (Variable "rec_occ1", Variable "rec_occ2"))
              ],
              Ands [
                Not (Is_Deeper_Than (Variable "rec_occ2", Variable "rec_occ1"))
              ]
            )
          )
        ]
      )
    )
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

in

val complex_lhs_causes_functional_induction_inner =
Lambdas (["_"],
  Ands [
    Some ("root_occ", QInner_Path,
      Ands [
        Is_Root_In_A_Location (Variable "root_occ"),
        Some ("lhs_occ", QInner_Path,
          Ands [
            Applies (is_lhs_of_root, [Variable "lhs_occ", Variable "root_occ"]),
            Some ("below_lhs_occ", QInner_Path,
              Ands [
                Node_Is_App (Variable "below_lhs_occ"),
                Is_Child_Of (Variable "below_lhs_occ", Variable "lhs_occ"),
                Some ("below_below_lhs_occ", QInner_Path,
                  Ands [
                    Node_Is_App (Variable "below_below_lhs_occ"),
                    Is_Child_Of (Variable "below_below_lhs_occ", Variable "below_lhs_occ")
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

end

val complex_lhs_causes_functional_induction_outer =
Imply (
  Some ("func_term", QOuter_Print,
    Ands [
      Print_Is_Cnst (Variable "func_term"),
      In_Some_Definitions (Variable "func_term", complex_lhs_causes_functional_induction_inner, [Variable "func_term"])
    ]
  ),
  Some ("rule", QRule,
    Ands [
      Some ("func_term", QOuter_Print,
        Ands [
          Print_Is_Cnst (Variable "func_term"),
          Is_Rule_Of_Print (Variable "rule", Variable "func_term"),
          In_Some_Definitions (Variable "func_term", complex_lhs_causes_functional_induction_inner, [Variable "func_term"])
        ]
      )
    ]
  )
);

val if_part_of_lhs_n_part_of_rhs_of_eq_is_induct_rule_then_induct_rule_on_part_of_lhs =
Imply (
  Ands [
    Some ("rule", QRule, True),
    Some ("hol_eq_occ1", QOuter_Path,
      Ands [
        Unode_Has_Print (Variable "hol_eq_occ1", Print "HOL.eq"),
        Some ("hol_eq_occ2", QOuter_Path,
          Ands [
            Unode_Has_Print (Variable "hol_eq_occ2", Print "HOL.eq"),
            Some ("rule", QRule,
              Some ("rec_fun_term", QOuter_Print,
                Ands [
                  Is_Rule_Of_Print (Variable "rule", Variable "rec_fun_term"),
                  Some_Of ("rec_fun1_occ", Variable "rec_fun_term",
                    Ands [
                      Ors [
                        Ands [(*induct only on the LHS of the equation*)
                          Is_Nth_Argument_Or_Below_Nth_Argument_Of (Variable "rec_fun1_occ", Number 0, Variable "hol_eq_occ1")
                        ],
                        Ands [(*induct only on the RHS of the equation*)
                          Is_Nth_Argument_Or_Below_Nth_Argument_Of (Variable "rec_fun1_occ", Number 1, Variable "hol_eq_occ1")
                        ]
                      ]
                    ]
                  )
                ]
              )
            )
          ]
        )
      ]
    )
  ],
  Some ("hol_eq_occ1", QOuter_Path,
    Ands [
      Unode_Has_Print (Variable "hol_eq_occ1", Print "HOL.eq"),
      Some ("hol_eq_occ2", QOuter_Path,
        Ands [
          Unode_Has_Print (Variable "hol_eq_occ2", Print "HOL.eq"),
          Some ("rule", QRule,
            Some ("rec_fun_term", QOuter_Print,
              Ands [
                Is_Rule_Of_Print (Variable "rule", Variable "rec_fun_term"),
                Some_Of ("rec_fun1_occ", Variable "rec_fun_term",
                  Ands [
                    Ors [
                      Ands [(*induct only on the LHS of the equation*)
                        Is_Nth_Argument_Or_Below_Nth_Argument_Of (Variable "rec_fun1_occ", Number 0, Variable "hol_eq_occ1")
                      ]
                    ]
                  ]
                )
              ]
            )
          )
        ]
      )
    ]
  )
);

val all_ind_should_be_atom =
All ("ind_term", QInd,
  Ors [
    Print_Is_Free  (Variable "ind_term"),
    Print_Is_Bound (Variable "ind_term")
  ]
)

val if_rule_induct_using_const_defined_with_inductive_set_in_snd_argument_of_membership_then_induct_on_var_in_fst_argument_of_membership =
Imply (
  Ands [
    Some ("induct_set", QRule,
      True
    )
  ],
  Ands [
    Not (
      Some ("ind_arg", QInd, True)
    )
  ]
);

val if_defined_with_inductive_set_in_meta_premise_then_set_induction =
Imply (
  Some ("node_defined_as_inductive_set", QOuter_Path,
    Ands [
      Node_Is_Defined_With       (Variable "node_defined_as_inductive_set", Command Definition_Pattern.Inductive_Set),
      Is_A_Meta_Premise_Or_Below (Variable "node_defined_as_inductive_set"),
      Not ((*To prevent recommending induction on set for cases like "hbase_funC" in Goodstein_Lambda.thy*)
        Some_Of ("membership", Print "Print Set.member",
          Ands [
            Is_Nth_Argument_Or_Below_Nth_Argument_Of (Variable "node_defined_as_inductive_set", Number 1, Variable "membership"),
            Some ("rec_node_in_first_arg_of_set_membership", QOuter_Path,
              Ands [
                Applies (node_defined_recursively, [Variable "rec_node_in_first_arg_of_set_membership"]),
                Is_Nth_Argument_Or_Below_Nth_Argument_Of (Variable "node_defined_as_inductive_set", Number 0, Variable "membership")
              ]
            )
          ]
        )
      )
    ]
  ),
  Some ("node_defined_as_inductive_set",
    QRule, Is_Set (Variable "node_defined_as_inductive_set")
  )
);

val trancl_induct =
Imply (
  Some ("trancl", QOuter_Path,
    Ands [
      Unode_Has_Print (Variable "trancl", Print "Transitive_Closure.trancl")
    ]
  ),
  Some ("trancl_induct", QRule,
    Ors [
      Are_Same_Prints (Variable "trancl_induct", Print "trancl_induct"),
      Are_Same_Prints (Variable "trancl_induct", Print "trancl_induct2"),
      Are_Same_Prints (Variable "trancl_induct", Print "converse_trancl_induct"),
      Are_Same_Prints (Variable "trancl_induct", Print "converse_trancl_induct2")
    ]
  )
);

val tranclp_induct =
Imply (
  Some ("tranclp", QOuter_Path,
    Ands [
      Unode_Has_Print (Variable "tranclp", Print "Transitive_Closure.tranclp")
    ]
  ),
  Some ("tranclp_induct", QRule,
    Ors [
      Are_Same_Prints (Variable "tranclp_induct", Print "tranclp_induct"),
      Are_Same_Prints (Variable "tranclp_induct", Print "tranclp_induct2"),
      Are_Same_Prints (Variable "tranclp_induct", Print "converse_tranclp_induct"),
      Are_Same_Prints (Variable "tranclp_induct", Print "converse_tranclp_induct2")
    ]
  )
);

val rtrancl_induct =
Imply (
  Some ("rtrancl", QOuter_Path,
    Ands [
      Unode_Has_Print (Variable "rtrancl", Print "Transitive_Closure.rtrancl")
    ]
  ),
  Some ("rtrancl_induct", QRule,
    Ors [
      Are_Same_Prints (Variable "rtrancl_induct", Print "rtrancl_induct"),
      Are_Same_Prints (Variable "rtrancl_induct", Print "rtrancl_induct2"),
      Are_Same_Prints (Variable "rtrancl_induct", Print "converse_rtrancl_induct"),
      Are_Same_Prints (Variable "rtrancl_induct", Print "converse_rtrancl_induct2")
    ]
  )
);

val rtranclp_induct =
Imply (
  Some ("rtranclp", QOuter_Path,
    Ands [
      Unode_Has_Print (Variable "rtranclp", Print "Transitive_Closure.rtranclp")
    ]
  ),
  Some ("rtranclp_induct", QRule,
    Ors [
      Are_Same_Prints (Variable "rtranclp_induct", Print "rtranclp_induct"),
      Are_Same_Prints (Variable "rtranclp_induct", Print "rtranclp_induct2"),
      Are_Same_Prints (Variable "rtranclp_induct", Print "converse_rtranclp_induct"),
      Are_Same_Prints (Variable "rtranclp_induct", Print "converse_rtranclp_induct2")
    ]
  )
);

val trancl_induct2 =
Imply (
  Some ("trancl", QOuter_Path,
    Ands [
      Unode_Has_Print (Variable "trancl", Print "Transitive_Closure.trancl")
    ]
  ),
  Some ("trancl_induct", QRule,
    Ors [
      Are_Same_Prints (Variable "trancl_induct", Print "trancl_induct2"),
      Are_Same_Prints (Variable "trancl_induct", Print "converse_trancl_induct2")
    ]
  )
);

val tranclp_induct2 =
Imply (
  Some ("tranclp", QOuter_Path,
    Ands [
      Unode_Has_Print (Variable "tranclp", Print "Transitive_Closure.tranclp")
    ]
  ),
  Some ("tranclp_induct", QRule,
    Ors [
      Are_Same_Prints (Variable "tranclp_induct", Print "tranclp_induct2"),
      Are_Same_Prints (Variable "tranclp_induct", Print "converse_tranclp_induct2")
    ]
  )
);

val rtrancl_induct2 =
Imply (
  Some ("rtrancl", QOuter_Path,
    Ands [
      Unode_Has_Print (Variable "rtrancl", Print "Transitive_Closure.rtrancl")
    ]
  ),
  Some ("rtrancl_induct", QRule,
    Ors [
      Are_Same_Prints (Variable "rtrancl_induct", Print "rtrancl_induct2"),
      Are_Same_Prints (Variable "rtrancl_induct", Print "converse_rtrancl_induct2")
    ]
  )
);

val rtranclp_induct2 =
Imply (
  Some ("rtranclp", QOuter_Path,
    Ands [
      Unode_Has_Print (Variable "rtranclp", Print "Transitive_Closure.rtranclp")
    ]
  ),
  Some ("rtranclp_induct", QRule,
    Ors [
      Are_Same_Prints (Variable "rtranclp_induct", Print "rtranclp_induct2"),
      Are_Same_Prints (Variable "rtranclp_induct", Print "converse_rtranclp_induct2")
    ]
  )
);

val if_two_occs_of_length_or_size_in_assum_or_chained_fact_then_list_induct2 =
Imply (
  Some ("length_or_size", QOuter_Print,
    Ands [
      Ors [
        Are_Same_Prints (Variable "length_or_size", Print "Nat.size_class.size"),
        Are_Same_Prints (Variable "length_or_size", Print "List.length")
      ],
    Some_Of ("length_or_size_occ1", Variable "length_or_size",
      Ands [
        Ors [
          Is_In_Chained_Fact (Variable "length_or_size_occ1"),
          Is_A_Meta_Premise_Or_Below (Variable "length_or_size_occ1")
        ],
        Some_Of ("length_or_size_occ2", Variable "length_or_size",
          Ands [
            Not (Is_Same_Path_As (Variable "length_or_size_occ1", Variable "length_or_size_occ2")),
            Ors [
              Is_In_Chained_Fact (Variable "length_or_size_occ2"),
              Is_A_Meta_Premise_Or_Below (Variable "length_or_size_occ2")
            ]
          ]
        )
      ]
    )
    ]
  ),
  Some ("list_induct2", QRule,
    Ors [
      Are_Same_Prints (Variable "list_induct2", Print "List.list_induct2")
    ]
  )
);

val rule_is_list_induct2' =
  Some ("rule", QRule,
    Ors [
      Are_Same_Prints (Variable "rule", Print "List.list_induct2'")
    ]
  );

val if_list_all2_then_list_all2_induct =
Imply (
  Some ("list_all2", QOuter_Print,
    Ors [
      Are_Same_Prints (Variable "list_all2", Print "List.list.list_all2")
    ]
  ),
  Some ("list_all2_induct", QRule,
    Ors [
      Are_Same_Prints (Variable "list_all2_induct", Print "List.list_all2_induct")
    ]
  )
);

val if_list_induct2'_then_two_induct_terms =
Imply (
  Some ("rule", QRule,
    Ors [
      Are_Same_Prints (Variable "rule", Print "List.list_induct2'")
    ]
  ),
  Some ("fst_ind_term", QInd,
    Ands [
      Is_Nth_Induct (Variable "fst_ind_term", Number 0),
      Some ("snd_ind_term", QInd,
        Ands [
          Is_Nth_Induct (Variable "snd_ind_term", Number 1),
          Not (
            Some ("3rd_ind_term", QInd,
              Ands [
                Is_Nth_Induct (Variable "3rd_ind_term", Number 2)
              ]
            )
          )
        ]
      )
    ]
  )
);

val if_not_equal_in_premise_or_chained_then_rev_nonempty_induct =
Imply (
  Some ("nil", QOuter_Path,
    Ands [
      Unode_Has_Print (Variable "nil", Print "List.list.Nil"),
      Ors [
        Is_In_Chained_Fact (Variable "nil"),
        Is_A_Meta_Premise_Or_Below (Variable "nil")
      ],
      Some ("eq", QOuter_Path,
        Ands [
          Unode_Has_Print (Variable "eq", Print "HOL.eq"),
          Ors [
            Is_In_Chained_Fact (Variable "eq"),
            Is_A_Meta_Premise_Or_Below (Variable "eq")
          ],
          Is_An_Argument_Of (Variable "nil", Variable "eq"),
          Some ("not", QOuter_Path,
            Ands [
              Unode_Has_Print (Variable "not", Print "HOL.Not"),
              Ors [
                Is_In_Chained_Fact (Variable "not"),
                Is_A_Meta_Premise_Or_Below (Variable "not")
              ],
              Is_An_Argument_Or_Below_Argument_Of (Variable "eq", Variable "not")
            ]
          )
        ]
      )
    ]
  ),
  Some ("nonempty_induct", QRule,
    Ors [
      Are_Same_Prints (Variable "nonempty_induct", Print "List.rev_nonempty_induct"),
      Are_Same_Prints (Variable "nonempty_induct", Print "List.list_nonempty_induct")
    ]
  )
);

(*TODO: we should check for the type Nat.nat to improve the accuracy of this heuristic.*)
val if_less_eq_in_premise_or_chained_but_not_nonempty_induct_then_inc_induct =
Imply (
  Some ("less_eq", QOuter_Path,
    Ands [
      Unode_Has_Print (Variable "less_eq", Print "Orderings.ord_class.less_eq"),
      Ors [
        Is_In_Chained_Fact (Variable "less_eq"),
        Is_A_Meta_Premise_Or_Below (Variable "less_eq")
      ],
      Not ( 
        Some ("nonempty_induct", QRule,
          Ors [
            Are_Same_Prints (Variable "nonempty_induct", Print "List.rev_nonempty_induct"),
            Are_Same_Prints (Variable "nonempty_induct", Print "List.list_nonempty_induct")
          ]
        )
      )
    ]
  ),
  Some ("inc_induct", QRule,
    Are_Same_Prints (Variable "inc_induct", Print "Nat.inc_induct")
  )
)

val if_less_or_less_eq_in_premise_or_chained_but_not_nonempty_induct_then_less_induct =
Imply (
  Some ("less_or_less_eq", QOuter_Path,
    Ands [
      Ors [
        Unode_Has_Print (Variable "less_or_less_eq", Print "Orderings.ord_class.less"),
        Unode_Has_Print (Variable "less_or_less_eq", Print "Orderings.ord_class.less_eq")
      ],
      Ors [
        Is_In_Chained_Fact (Variable "less_or_less_eq"),
        Is_A_Meta_Premise_Or_Below (Variable "less_or_less_eq")
      ],
      Not ( 
        Some ("nonempty_induct", QRule,
          Ors [
            Are_Same_Prints (Variable "nonempty_induct", Print "List.rev_nonempty_induct"),
            Are_Same_Prints (Variable "nonempty_induct", Print "List.list_nonempty_induct")
          ]
        )
      )
    ]
  ),
  Some ("less_induct", QRule,
    Are_Same_Prints (Variable "less_induct", Print "Orderings.wellorder_class..less_induct")
  )
)

end;