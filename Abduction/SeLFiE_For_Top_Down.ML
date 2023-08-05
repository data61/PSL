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