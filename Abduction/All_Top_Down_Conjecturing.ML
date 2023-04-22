(*
 * Top_Down_Conjecturing.ML
 *
 * Authors:
 *   Yutaka Nagashima, Daniel Goc Sebastian
 *   Huawei Technologies Research & Development (UK) Limited.
 *)
structure SeLFiE_for_Top_Down =
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

fun run_assertion (pst:Proof.state)  (assrt:assert) (cnjctr:term) =
  let
    val outer_path_to_unode_table = Outer_Path_To_Unode.pst_n_trm_to_path_to_unode_table pst cnjctr                                               : Outer_Path_To_Unode.path_to_unode_table;
    val gen_path_table            = Gen_Path.Outer_Path_To_Unode outer_path_to_unode_table                                                        : Gen_Path.gen_path_to_unode_table;
    val empty_argument            = SeLFiE_Util.Induct_Arguments {ons = [], arbs = [], rules = []}                                                : SeLFiE_Util.induct_arguments;
    val outer_domains             = Quantifier_Domain.inout_pst_n_trm_n_induct_args_to_domains Quantifier_Domain.Out gen_path_table empty_argument: Quantifier_Domain.domains;
  in
    eval pst outer_path_to_unode_table outer_domains empty_argument assrt = True
  end;

end;

(*** structure All_Top_Down_Conjecturing ***)
structure All_Top_Down_Conjecturing: TOP_DOWN_CONJECTURING =
struct

fun is_composite trm = Isabelle_Utils.is_Abs trm orelse Isabelle_Utils.is_App trm: bool;

(*TODO: code-duplication with SeLFiE/Eval_Print.ML*)
fun read_term_then_check_term (ctxt:Proof.context) (print:string) (checker: term -> bool) =
    try (Syntax.read_term ctxt) print
<$> checker
 |> Utils.is_some_true;

fun has_no_multiple_occ_of_composite_subtrm (ctxt:Proof.context) (trm:term) =
let
  val p2u_table = Inner_Path_To_Unode.pst_n_trm_to_path_to_unode_table (Proof.init ctxt) trm: Inner_Path_To_Unode.path_to_unode_table;
  val p2p_table = Print_To_Inner_Paths.path_to_unode_table_to_print_to_paths_table p2u_table: Print_To_Inner_Paths.print_to_paths_table;
  val prints = Print_To_Inner_Paths.print_to_paths_table_to_prints p2p_table: strings;
  fun print_has_multiple_paths (print:string) =
    let
      val paths = Print_Table.lookup_list p2p_table print;
      val has_multi = not (length paths = 1): bool;
    in
      has_multi
    end;
  val duplicated_prints = filter print_has_multiple_paths prints: strings;
  val duplicated_composites = filter (fn print => read_term_then_check_term ctxt print is_composite) duplicated_prints: strings;
  val has_dupulicates = null duplicated_composites: bool;
in
  has_dupulicates: bool
end;

(* Prod31 for example needs this congruence(?).
fun eq_over_same_func (ctxt:Proof.context) (trm:term) =
  let
    val trm_wo_Trueprop = Isabelle_Utils.remove_Trueprop trm;
    val trm_w_prnt  = Unique_Node.trm_to_trm_w_prnt ctxt trm_wo_Trueprop;
    val utrm_w_prnt = Unique_Node.trm_w_prnt_to_utrm_w_prnt trm_w_prnt;
    val result = case utrm_w_prnt of
        Unique_Node.UA_Prnt (Unique_Node.UC_Prnt ("HOL.eq", _, "HOL.eq"),
          [Unique_Node.UA_Prnt (func1, _, _),
           Unique_Node.UA_Prnt (func2, _, _)], _) => func1 = func2
      | _ => false
  in
    result
  end;
*)

fun top_down_conjectures (ctxt:Proof.context) trm =
  let
    val _ = tracing "[[[[[[[[[[[top_down_conjecture starts]]]]]]]]]]": unit;
    val standardized_trm = standardize_vnames trm
    val results = (
      Remove_Outermost_Assumption.top_down_conjectures ctxt standardized_trm
    (*@ Generalise_By_Renaming.top_down_conjectures ctxt standardized_trm*)
    @ (Generalise_Then_Extend.top_down_conjectures ctxt standardized_trm       |> filter (fn (_, trm) => has_no_multiple_occ_of_composite_subtrm ctxt trm))
    @ Remove_Function.top_down_conjectures ctxt standardized_trm
    @ Abstract_Same_Term.top_down_conjectures ctxt standardized_trm
    @ Replace_Imp_With_Eq.top_down_conjectures ctxt standardized_trm)
      |> map (apsnd (simp_non_prop_term ctxt))
      |> map (apsnd standardize_vnames)
      |> distinct (fn (f, s) => snd f = snd s)
(*
      |> filter_out (fn (_, trm) => eq_over_same_func ctxt trm)
*)
      |> filter_out (fn (_, trm) => SeLFiE_for_Top_Down.run_assertion (Top_Down_Util.mk_pst_to_prove_from_term ctxt trm) SeLFiE_for_Top_Down.has_func_with_three_occs_in_a_row trm)
      |> filter (fn (_, trm) => SeLFiE_for_Top_Down.run_assertion (Top_Down_Util.mk_pst_to_prove_from_term ctxt trm) SeLFiE_for_Top_Down.fvars_in_prem_should_appear_in_concl trm)
      |> filter (fn (_, trm) => SeLFiE_for_Top_Down.run_assertion (Top_Down_Util.mk_pst_to_prove_from_term ctxt trm) SeLFiE_for_Top_Down.does_not_have_trivial_equality trm);
    val _ = map (tracing o Isabelle_Utils.trm_to_string ctxt o snd) results: unit list;
    val _ = tracing "[[[[[[[[[[[top_down_conjecture ends]]]]]]]]]]": unit;
  in
    results
  end;

end;