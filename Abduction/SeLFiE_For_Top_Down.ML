(*
 * SeLFiE_for_Top_Down.ML
 *
 * Authors:
 *   Yutaka Nagashima, Daniel Goc Sebastian
 *   Huawei Technologies Research & Development (UK) Limited.
 *)
(*** SeLFiE_For_Top_Down ***)
structure SeLFiE_For_Top_Down =
struct

open Eval_Syntactic_Sugar;

val fvars_in_prem_should_appear_in_concl =
  All ("trm_occ_in_prem", SeLFiE_Util.QOuter_Path,
    Imply (
      And (
        Node_Is_Free (Variable "trm_occ_in_prem"),
        Is_A_Meta_Premise_Or_Below (Variable "trm_occ_in_prem")
      ),
      Some ("trm_occ_in_cncl", SeLFiE_Util.QOuter_Path,
        Ands [
          Has_Same_Prnt_As (Variable "trm_occ_in_prem", Variable "trm_occ_in_cncl"),
          Node_Is_Free (Variable "trm_occ_in_cncl"),
          Is_A_Meta_Conclusion_Or_Below (Variable "trm_occ_in_cncl")
        ]
      )
    )
  );

(* Due to the use of simplifier, this might be obsolete.*)
val does_not_have_trivial_equality =
  Not (
    Some ("equality", SeLFiE_Util.QOuter_Path,
      And (
        Unode_Has_Print (Variable "equality", Print "HOL.eq"),
        Some ("lhs", SeLFiE_Util.QOuter_Path,
          And (
            Is_Nth_Argument_Of (Variable "lhs", Number 0, Variable "equality"),
            Some ("rhs", SeLFiE_Util.QOuter_Path,
              And (
                Has_Same_Prnt_As (Variable "lhs", Variable "rhs"),
                Is_Nth_Argument_Of (Variable "rhs", Number 1, Variable "equality")
              )
            )
          )
        )
      )
    )
  );

val has_func_with_three_occs_in_a_row =
  Some ("func", SeLFiE_Util.QOuter_Print,
    Ands [
      Print_Is_Cnst (Variable "func"),
      Not (Is_Subprint_Of (Print "Pure", Variable "func")),
      Not (Is_Subprint_Of (Print "HOL",  Variable "func")),
      Some_Of ("func_occ1", Variable "func",
        Ands [
          Some ("arg_of_func_occ1", SeLFiE_Util.QOuter_Path,
            Ands [
              Node_Is_App (Variable "arg_of_func_occ1"),
              Is_An_Argument_Of (Variable "arg_of_func_occ1", Variable "func_occ1"),
              Some_Of ("func_occ2", Variable "func",
                Ands [
                  Is_Nth_Child_Of (Variable "func_occ2", Number 0, Variable "arg_of_func_occ1"),

                  Some ("arg_of_func_occ2", SeLFiE_Util.QOuter_Path,
                    Ands [
                      Node_Is_App (Variable "arg_of_func_occ2"),
                      Is_An_Argument_Of (Variable "arg_of_func_occ2", Variable "func_occ2"),
                      Some_Of ("func_occ3", Variable "func",
                        Ands [
                          Is_Nth_Child_Of (Variable "func_occ3", Number 0, Variable "arg_of_func_occ2")
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

val var_appears_many_times_but_always_in_the_same_subtrm =
  Some ("subtrm", SeLFiE_Util.QOuter_Print,
    Some ("var", SeLFiE_Util.QOuter_Print,
      Ands [
        Not (Are_Same_Prints (Variable "subtrm", Variable "var")),
        Print_Is_Free (Variable "var"),
        Is_Subprint_Of (Variable "var", Variable "subtrm"),
        All_Of ("var_occ", Variable "var",
          Some_Of ("subtrm_occ1", Variable "subtrm",
            Ands [
              Is_Path_Above (Variable "subtrm_occ1", Variable "var_occ"),
              Some_Of ("subtrm_occ2", Variable "subtrm",
                Not (Is_Same_Path_As (Variable "subtrm_occ1", Variable "subtrm_occ2"))
              )
            ]
          )
        )
      ]
    )
  );

val nested_eq =
  Some ("eq", SeLFiE_Util.QOuter_Print,
    Ands [
      Are_Same_Prints(Variable "eq", Print "HOL.eq"),
      Some_Of ("eq_occ1", Variable "eq",
        Some_Of ("eq_occ2", Variable "eq",
          Some ("subtrm", SeLFiE_Util.QOuter_Path,
            Ands [
              Is_An_Argument_Of (Variable "subtrm", Variable "eq_occ1"),
              Is_Parent_Of      (Variable "subtrm", Variable "eq_occ2")
            ]
          )
        )
      )
    ]
  );

val congruence =(*Probably unsafe. Not recommended to use this.*)
  Some ("eq_occ", SeLFiE_Util.QOuter_Path,
    Ands [
      Unode_Has_Print (Variable "eq_occ", Print "HOL.eq"),
      Some ("lhs_occ", SeLFiE_Util.QOuter_Path,
        Ands [
          Is_Nth_Argument_Of (Variable "lhs_occ", Number 0, Variable "eq_occ"),
          Node_Is_App (Variable "lhs_occ"),
          Some ("rhs_occ", SeLFiE_Util.QOuter_Path,
            Ands [
              Is_Nth_Argument_Of (Variable "rhs_occ", Number 1, Variable "eq_occ"),
              Node_Is_App (Variable "rhs_occ"),
              Some ("func_lhs_occ", SeLFiE_Util.QOuter_Path,
                Ands [
                  Is_Nth_Child_Of (Variable "func_lhs_occ", Number 0, Variable "lhs_occ"),
                  Ors [
                    Not (Node_Takes_Less_Than_N_Arguments (Variable "func_lhs_occ", Number 2))
                  ],
                  Some ("func_rhs_occ", SeLFiE_Util.QOuter_Path,
                    Ands [
                      Is_Nth_Child_Of (Variable "func_rhs_occ", Number 0, Variable "rhs_occ"),
                      Has_Same_Prnt_As (Variable "func_rhs_occ", Variable "func_lhs_occ"),
                      Some ("arg_numb_of_diff_arg", SeLFiE_Util.QOuter_Number,
                        Ands [
                          Node_Takes_Less_Than_N_Arguments (Variable "func_rhs_occ", Variable "arg_numb_of_diff_arg"),
                          All ("arg_numb_of_same_arg", SeLFiE_Util.QOuter_Number,
                            Imply (
                              Ands [
                                Node_Takes_Less_Than_N_Arguments (Variable "func_rhs_occ", Variable "arg_numb_of_same_arg"),
                                Not (Are_Same_Number (Variable "arg_numb_of_diff_arg", Variable "arg_numb_of_same_arg"))
                              ],
                              All ("lhs_arg_occ", SeLFiE_Util.QOuter_Path,
                                Ands [
                                  Imply (
                                    Is_Nth_Argument_Of (Variable "lhs_arg_occ", Variable "arg_numb_of_same_arg", Variable "func_lhs_occ"),
                                    Some ("rhs_arg_occ", SeLFiE_Util.QOuter_Path,
                                      Ands [
                                        Is_Nth_Argument_Of (Variable "rhs_arg_occ", Variable "arg_numb_of_same_arg", Variable "func_rhs_occ"),
                                        Has_Same_Prnt_As (Variable "lhs_arg_occ", Variable "rhs_arg_occ")
                                      ]
                                    )
                                  ),
                                  Imply (
                                    Is_Nth_Argument_Of (Variable "lhs_arg_occ", Variable "arg_numb_of_diff_arg", Variable "func_lhs_occ"),
                                    Some ("rhs_arg_occ", SeLFiE_Util.QOuter_Path,
                                      Ands [
                                        Is_Nth_Argument_Of (Variable "rhs_arg_occ", Variable "arg_numb_of_diff_arg", Variable "func_rhs_occ"),
                                        Have_Different_Prnts (Variable "lhs_arg_occ", Variable "rhs_arg_occ")
                                      ]
                                    )
                                  )
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
  );

fun run_assertion (pst:Proof.state) (cnjctr:term) (assert:Eval_Syntactic_Sugar.assert) =
  let
    val pst_to_prove              = mk_pst_to_prove_from_term pst cnjctr                                                                          : Proof.state;
    val outer_path_to_unode_table = Outer_Path_To_Unode.pst_n_trm_to_path_to_unode_table pst_to_prove cnjctr                                      : Outer_Path_To_Unode.path_to_unode_table;
    val gen_path_table            = Gen_Path.Outer_Path_To_Unode outer_path_to_unode_table                                                        : Gen_Path.gen_path_to_unode_table;
    val empty_argument            = SeLFiE_Util.Induct_Arguments {ons = [], arbs = [], rules = []}                                                : SeLFiE_Util.induct_arguments;
    val outer_domains             = Quantifier_Domain.inout_pst_n_trm_n_induct_args_to_domains Quantifier_Domain.Out gen_path_table empty_argument: Quantifier_Domain.domains;
  in
    eval pst_to_prove outer_path_to_unode_table outer_domains empty_argument assert = True
  end;

end;