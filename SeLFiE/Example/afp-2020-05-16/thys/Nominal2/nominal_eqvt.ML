(*  Title:      nominal_eqvt.ML
    Author:     Stefan Berghofer (original code)
    Author:     Christian Urban
    Author:     Tjark Weber

    Automatic proofs for equivariance of inductive predicates.
*)

signature NOMINAL_EQVT =
sig
  val raw_equivariance: Proof.context -> term list -> thm -> thm list -> thm list
  val equivariance_cmd: string -> Proof.context -> local_theory
end

structure Nominal_Eqvt : NOMINAL_EQVT =
struct

open Nominal_Permeq;
open Nominal_ThmDecls;

fun atomize_conv ctxt =
  Raw_Simplifier.rewrite_cterm (true, false, false) (K (K NONE))
    (put_simpset HOL_basic_ss ctxt addsimps @{thms induct_atomize})

fun atomize_intr ctxt = Conv.fconv_rule (Conv.prems_conv ~1 (atomize_conv ctxt))

fun atomize_induct ctxt = Conv.fconv_rule (Conv.prems_conv ~1
  (Conv.params_conv ~1 (K (Conv.prems_conv ~1 (atomize_conv ctxt))) ctxt))


(** equivariance tactics **)

fun eqvt_rel_single_case_tac ctxt pred_names pi intro =
  let
    val cpi = Thm.cterm_of ctxt pi
    val pi_intro_rule = Thm.instantiate' [] [NONE, SOME cpi] @{thm permute_boolI}
    val eqvt_sconfig = eqvt_strict_config addexcls pred_names
  in
    eqvt_tac ctxt eqvt_sconfig THEN'
    SUBPROOF (fn {prems, context as ctxt, ...} =>
      let
        val simps1 =
          put_simpset HOL_basic_ss ctxt addsimps @{thms permute_fun_def permute_self split_paired_all}
        val simps2 =
          put_simpset HOL_basic_ss ctxt addsimps @{thms permute_bool_def permute_minus_cancel(2)}
        val prems' = map (transform_prem2 ctxt pred_names) prems
        val prems'' = map (fn thm => eqvt_rule ctxt eqvt_sconfig (thm RS pi_intro_rule)) prems'
        val prems''' = map (simplify simps2 o simplify simps1) prems''
      in
        HEADGOAL (resolve_tac ctxt [intro] THEN_ALL_NEW
          resolve_tac ctxt (prems' @ prems'' @ prems'''))
      end) ctxt
  end

fun eqvt_rel_tac ctxt pred_names pi induct intros =
  let
    val cases = map (eqvt_rel_single_case_tac ctxt pred_names pi) intros
  in
    EVERY' ((DETERM o resolve_tac ctxt [induct]) :: cases)
  end


(** equivariance procedure **)

fun prepare_goal ctxt pi pred_with_args =
  let
    val (c, xs) = strip_comb pred_with_args
    fun is_nonfixed_Free (Free (s, _)) = not (Variable.is_fixed ctxt s)
      | is_nonfixed_Free _ = false
    fun mk_perm_nonfixed_Free t =
      if is_nonfixed_Free t then mk_perm pi t else t
  in
    HOLogic.mk_imp (pred_with_args,
      list_comb (c, map mk_perm_nonfixed_Free xs))
  end

fun name_of (Const (s, _)) = s

fun raw_equivariance ctxt preds raw_induct intrs =
  let
    (* FIXME: polymorphic predicates should either be rejected or
              specialized to arguments of sort pt *)

    val is_already_eqvt = filter (is_eqvt ctxt) preds
    val _ = if null is_already_eqvt then ()
      else error ("Already equivariant: " ^ commas
        (map (Syntax.string_of_term ctxt) is_already_eqvt))

    val pred_names = map (name_of o head_of) preds
    val raw_induct' = atomize_induct ctxt raw_induct
    val intrs' = map (atomize_intr ctxt) intrs

    val (([raw_concl], [raw_pi]), ctxt') =
      ctxt
      |> Variable.import_terms false [Thm.concl_of raw_induct']
      ||>> Variable.variant_fixes ["p"]
    val pi = Free (raw_pi, @{typ perm})

    val preds_with_args = raw_concl
      |> HOLogic.dest_Trueprop
      |> HOLogic.dest_conj
      |> map (fst o HOLogic.dest_imp)

    val goal = preds_with_args
      |> map (prepare_goal ctxt pi)
      |> foldr1 HOLogic.mk_conj
      |> HOLogic.mk_Trueprop
  in
    Goal.prove ctxt' [] [] goal
      (fn {context, ...} => eqvt_rel_tac context pred_names pi raw_induct' intrs' 1)
      |> Old_Datatype_Aux.split_conj_thm
      |> Proof_Context.export ctxt' ctxt
      |> map (fn th => th RS mp)
      |> map zero_var_indexes
  end


(** stores thm under name.eqvt and adds [eqvt]-attribute **)

fun note_named_thm (name, thm) ctxt =
  let
    val thm_name = Binding.qualified_name
      (Long_Name.qualify (Long_Name.base_name name) "eqvt")
    val attr = Attrib.internal (K eqvt_add)
    val ((_, [thm']), ctxt') = Local_Theory.note ((thm_name, [attr]), [thm]) ctxt
  in
    (thm', ctxt')
  end


(** equivariance command **)

fun equivariance_cmd pred_name ctxt =
  let
    val ({names, ...}, {preds, raw_induct, intrs, ...}) =
      Inductive.the_inductive_global ctxt (long_name ctxt pred_name)
    val thms = raw_equivariance ctxt preds raw_induct intrs
  in
    fold_map note_named_thm (names ~~ thms) ctxt |> snd
  end

val _ =
  Outer_Syntax.local_theory @{command_keyword equivariance}
    "Proves equivariance for inductive predicate involving nominal datatypes."
      (Parse.const >> equivariance_cmd)

end (* structure *)
