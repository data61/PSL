(*  Title:      nominal_dt_alpha.ML
    Author:     Cezary Kaliszyk
    Author:     Christian Urban

  Definitions and proofs for the alpha-relations.
*)

signature NOMINAL_DT_ALPHA =
sig
  val comb_binders: Proof.context -> bmode -> term list -> (term option * int) list -> term

  val define_raw_alpha: raw_dt_info -> bn_info list -> bclause list list list -> term list ->
    Proof.context -> alpha_result * local_theory

  val induct_prove: typ list -> (typ * (term -> term)) list -> thm ->
    (Proof.context -> int -> tactic) -> Proof.context -> thm list

  val alpha_prove: term list -> (term * ((term * term) -> term)) list -> thm ->
    (Proof.context -> int -> tactic) -> Proof.context -> thm list

  val raw_prove_alpha_distincts: Proof.context -> alpha_result -> raw_dt_info -> thm list
  val raw_prove_alpha_eq_iff: Proof.context -> alpha_result -> raw_dt_info -> thm list
  val raw_prove_refl: Proof.context -> alpha_result -> thm -> thm list
  val raw_prove_sym: Proof.context -> alpha_result -> thm list -> thm list
  val raw_prove_trans: Proof.context -> alpha_result -> thm list -> thm list -> thm list
  val raw_prove_equivp: Proof.context -> alpha_result -> thm list -> thm list -> thm list ->
    thm list * thm list
  val raw_prove_bn_imp: Proof.context -> alpha_result -> thm list
  val raw_fv_bn_rsp_aux: Proof.context -> alpha_result -> term list -> term list -> term list ->
    thm list -> thm list
  val raw_size_rsp_aux: Proof.context -> alpha_result -> thm list -> thm list
  val raw_constrs_rsp: Proof.context -> alpha_result -> term list list -> thm list -> thm list list
  val raw_alpha_bn_rsp: alpha_result -> thm list -> thm list -> thm list
  val raw_perm_bn_rsp: Proof.context -> alpha_result -> term list -> thm list -> thm list

  val mk_funs_rsp: Proof.context -> thm -> thm
  val mk_alpha_permute_rsp: Proof.context -> thm -> thm
end

structure Nominal_Dt_Alpha: NOMINAL_DT_ALPHA =
struct

open Nominal_Permeq
open Nominal_Dt_Data

fun lookup xs x = the (AList.lookup (op=) xs x)
fun group xs = AList.group (op=) xs


(** definition of the inductive rules for alpha and alpha_bn **)

(* construct the compound terms for prod_fv and prod_alpha *)
fun mk_prod_fv (t1, t2) =
  let
    val ty1 = fastype_of t1
    val ty2 = fastype_of t2
    val resT = HOLogic.mk_prodT (domain_type ty1, domain_type ty2) --> @{typ "atom set"}
  in
    Const (@{const_name "prod_fv"}, [ty1, ty2] ---> resT) $ t1 $ t2
  end

fun mk_prod_alpha (t1, t2) =
  let
    val ty1 = fastype_of t1
    val ty2 = fastype_of t2
    val prodT = HOLogic.mk_prodT (domain_type ty1, domain_type ty2)
    val resT = [prodT, prodT] ---> @{typ "bool"}
  in
    Const (@{const_name "prod_alpha"}, [ty1, ty2] ---> resT) $ t1 $ t2
  end

(* generates the compound binder terms *)
fun comb_binders lthy bmode args binders =
  let
    fun bind_set lthy args (NONE, i) = setify lthy (nth args i)
      | bind_set _ args (SOME bn, i) = bn $ (nth args i)
    fun bind_lst lthy args (NONE, i) = listify lthy (nth args i)
      | bind_lst _ args (SOME bn, i) = bn $ (nth args i)

    val (combine_fn, bind_fn) =
      case bmode of
        Lst => (mk_append, bind_lst)
      | Set => (mk_union,  bind_set)
      | Res => (mk_union,  bind_set)
  in
    binders
    |> map (bind_fn lthy args)
    |> foldl1 combine_fn
  end

(* produces the term for an alpha with abstraction *)
fun mk_alpha_term bmode fv alpha args args' binders binders' =
  let
    val (alpha_name, binder_ty) =
      case bmode of
        Lst => (@{const_name "alpha_lst"}, @{typ "atom list"})
      | Set => (@{const_name "alpha_set"}, @{typ "atom set"})
      | Res => (@{const_name "alpha_res"}, @{typ "atom set"})
    val ty = fastype_of args
    val pair_ty = HOLogic.mk_prodT (binder_ty, ty)
    val alpha_ty = [ty, ty] ---> @{typ "bool"}
    val fv_ty = ty --> @{typ "atom set"}
    val pair_lhs = HOLogic.mk_prod (binders, args)
    val pair_rhs = HOLogic.mk_prod (binders', args')
  in
    HOLogic.exists_const @{typ perm} $ Abs ("p", @{typ perm},
      Const (alpha_name, [pair_ty, alpha_ty, fv_ty, @{typ "perm"}, pair_ty] ---> @{typ bool})
        $ pair_lhs $ alpha $ fv $ (Bound 0) $ pair_rhs)
  end

(* for non-recursive binders we have to produce alpha_bn premises *)
fun mk_alpha_bn_prem alpha_bn_map args args' bodies binder =
  case binder of
    (NONE, _) => []
  | (SOME bn, i) =>
     if member (op=) bodies i then []
     else [lookup alpha_bn_map bn $ nth args i $ nth args' i]

(* generate the premises for an alpha rule; mk_frees is used
   if no binders are present *)
fun mk_alpha_prems lthy alpha_map alpha_bn_map is_rec (args, args') bclause =
  let
    fun mk_frees i =
      let
        val arg = nth args i
        val arg' = nth args' i
        val ty = fastype_of arg
      in
        if nth is_rec i
        then fst (lookup alpha_map ty) $ arg $ arg'
        else HOLogic.mk_eq (arg, arg')
      end

    fun mk_alpha_fv i =
      let
        val ty = fastype_of (nth args i)
      in
        case AList.lookup (op=) alpha_map ty of
          NONE => (HOLogic.eq_const ty, supp_const ty)
        | SOME (alpha, fv) => (alpha, fv)
      end
  in
    case bclause of
      BC (_, [], bodies) => map (HOLogic.mk_Trueprop o mk_frees) bodies
    | BC (bmode, binders, bodies) =>
        let
          val (alphas, fvs) = split_list (map mk_alpha_fv bodies)
          val comp_fv = foldl1 mk_prod_fv fvs
          val comp_alpha = foldl1 mk_prod_alpha alphas
          val comp_args = foldl1 HOLogic.mk_prod (map (nth args) bodies)
          val comp_args' = foldl1 HOLogic.mk_prod (map (nth args') bodies)
          val comp_binders = comb_binders lthy bmode args binders
          val comp_binders' = comb_binders lthy bmode args' binders
          val alpha_prem =
            mk_alpha_term bmode comp_fv comp_alpha comp_args comp_args' comp_binders comp_binders'
          val alpha_bn_prems = flat (map (mk_alpha_bn_prem alpha_bn_map args args' bodies) binders)
        in
          map HOLogic.mk_Trueprop (alpha_prem::alpha_bn_prems)
        end
  end

(* produces the introduction rule for an alpha rule *)
fun mk_alpha_intros lthy alpha_map alpha_bn_map (constr, ty, arg_tys, is_rec) bclauses =
  let
    val arg_names = Old_Datatype_Prop.make_tnames arg_tys
    val arg_names' = Name.variant_list arg_names arg_names
    val args = map Free (arg_names ~~ arg_tys)
    val args' = map Free (arg_names' ~~ arg_tys)
    val alpha = fst (lookup alpha_map ty)
    val concl = HOLogic.mk_Trueprop (alpha $ list_comb (constr, args) $ list_comb (constr, args'))
    val prems = map (mk_alpha_prems lthy alpha_map alpha_bn_map is_rec (args, args')) bclauses
  in
    Library.foldr Logic.mk_implies (flat prems, concl)
  end

(* produces the premise of an alpha-bn rule; we only need to
   treat the case special where the binding clause is empty;

   - if the body is not included in the bn_info, then we either
     produce an equation or an alpha-premise

   - if the body is included in the bn_info, then we create
     either a recursive call to alpha-bn, or no premise  *)
fun mk_alpha_bn lthy alpha_map alpha_bn_map bn_args is_rec (args, args') bclause =
  let
    fun mk_alpha_bn_prem i =
      let
        val arg = nth args i
        val arg' = nth args' i
        val ty = fastype_of arg
      in
        case AList.lookup (op=) bn_args i of
          NONE => (case (AList.lookup (op=) alpha_map ty) of
                     NONE =>  [HOLogic.mk_eq (arg, arg')]
                   | SOME (alpha, _) => [alpha $ arg $ arg'])
        | SOME (NONE) => []
        | SOME (SOME bn) => [lookup alpha_bn_map bn $ arg $ arg']
      end
  in
    case bclause of
      BC (_, [], bodies) =>
        map HOLogic.mk_Trueprop (flat (map mk_alpha_bn_prem bodies))
    | _ => mk_alpha_prems lthy alpha_map alpha_bn_map is_rec (args, args') bclause
  end

fun mk_alpha_bn_intro lthy bn_trm alpha_map alpha_bn_map (bn_args, (constr, _, arg_tys, is_rec)) bclauses =
  let
    val arg_names = Old_Datatype_Prop.make_tnames arg_tys
    val arg_names' = Name.variant_list arg_names arg_names
    val args = map Free (arg_names ~~ arg_tys)
    val args' = map Free (arg_names' ~~ arg_tys)
    val alpha_bn = lookup alpha_bn_map bn_trm
    val concl = HOLogic.mk_Trueprop (alpha_bn $ list_comb (constr, args) $ list_comb (constr, args'))
    val prems = map (mk_alpha_bn lthy alpha_map alpha_bn_map bn_args is_rec (args, args')) bclauses
  in
    Library.foldr Logic.mk_implies (flat prems, concl)
  end

fun mk_alpha_bn_intros lthy alpha_map alpha_bn_map constrs_info bclausesss (bn_trm, bn_n, bn_argss) =
  let
    val nth_constrs_info = nth constrs_info bn_n
    val nth_bclausess = nth bclausesss bn_n
  in
    map2 (mk_alpha_bn_intro lthy bn_trm alpha_map alpha_bn_map) (bn_argss ~~ nth_constrs_info) nth_bclausess
  end

fun define_raw_alpha raw_dt_info bn_info bclausesss fvs lthy =
  let
    val RawDtInfo {raw_dt_names, raw_tys, raw_cns_info, ...} = raw_dt_info

    val alpha_names = map (prefix "alpha_" o Long_Name.base_name) raw_dt_names
    val alpha_tys = map (fn ty => [ty, ty] ---> @{typ bool}) raw_tys
    val alpha_frees = map Free (alpha_names ~~ alpha_tys)
    val alpha_map = raw_tys ~~ (alpha_frees ~~ fvs)

    val (bns, bn_tys) = split_list (map (fn (bn, i, _) => (bn, i)) bn_info)
    val bn_names = map (fn bn => Long_Name.base_name (fst (dest_Const bn))) bns
    val alpha_bn_names = map (prefix "alpha_") bn_names
    val alpha_bn_arg_tys = map (nth raw_tys) bn_tys
    val alpha_bn_tys = map (fn ty => [ty, ty] ---> @{typ "bool"}) alpha_bn_arg_tys
    val alpha_bn_frees = map Free (alpha_bn_names ~~ alpha_bn_tys)
    val alpha_bn_map = bns ~~ alpha_bn_frees

    val alpha_intros = map2 (map2 (mk_alpha_intros lthy alpha_map alpha_bn_map)) raw_cns_info bclausesss
    val alpha_bn_intros = map (mk_alpha_bn_intros lthy alpha_map alpha_bn_map raw_cns_info bclausesss) bn_info

    val all_alpha_names = map (fn (a, ty) => ((Binding.name a, ty), NoSyn))
      (alpha_names @ alpha_bn_names ~~ alpha_tys @ alpha_bn_tys)
    val all_alpha_intros = map (pair Binding.empty_atts) (flat alpha_intros @ flat alpha_bn_intros)

    val (alpha_info, lthy') = lthy
      |> Local_Theory.subtarget_result Inductive.transform_result
        (Inductive.add_inductive
         {quiet_mode = true, verbose = false, alt_name = Binding.empty,
          coind = false, no_elim = false, no_ind = false, skip_mono = false}
           all_alpha_names [] all_alpha_intros [])

    val phi =
      Proof_Context.export_morphism lthy'
        (Proof_Context.transfer (Proof_Context.theory_of lthy') lthy);

    val alpha_info_global = Inductive.transform_result phi alpha_info;

    val all_alpha_trms = #preds alpha_info_global |> map Type.legacy_freeze (*FIXME*)
    val alpha_raw_induct = #raw_induct alpha_info_global
    val alpha_intros = #intrs alpha_info_global;
    val alpha_cases = #elims alpha_info_global;

    val (alpha_trms, alpha_bn_trms) = chop (length fvs) all_alpha_trms

    val alpha_tys = map (domain_type o fastype_of) alpha_trms
    val alpha_bn_tys = map (domain_type o fastype_of) alpha_bn_trms

    val alpha_names = map (fst o dest_Const) alpha_trms
    val alpha_bn_names = map (fst o dest_Const) alpha_bn_trms
  in
    (AlphaResult
      {alpha_names = alpha_names,
       alpha_trms = alpha_trms,
       alpha_tys = alpha_tys,
       alpha_bn_names = alpha_bn_names,
       alpha_bn_trms = alpha_bn_trms,
       alpha_bn_tys = alpha_bn_tys,
       alpha_intros = alpha_intros,
       alpha_cases = alpha_cases,
       alpha_raw_induct = alpha_raw_induct}, lthy')
  end


(** induction proofs **)


(* proof by structural induction over data types *)

fun induct_prove tys props induct_thm cases_tac ctxt =
  let
    val (arg_names, ctxt') =
      Variable.variant_fixes (replicate (length tys) "x") ctxt

    val args = map2 (curry Free) arg_names tys

    val true_trms = replicate (length tys) (K @{term True})

    fun apply_all x fs = map (fn f => f x) fs

    val goals =
        group (props @ (tys ~~ true_trms))
        |> map snd
        |> map2 apply_all args
        |> map fold_conj
        |> foldr1 HOLogic.mk_conj
        |> HOLogic.mk_Trueprop

    fun tac ctxt =
      HEADGOAL
        (DETERM o (resolve_tac ctxt [induct_thm])
         THEN_ALL_NEW
           (REPEAT_ALL_NEW (FIRST' [resolve_tac ctxt @{thms TrueI conjI}, cases_tac ctxt])))
  in
    Goal.prove ctxt' [] [] goals (fn {context, ...} => tac context)
    |> singleton (Proof_Context.export ctxt' ctxt)
    |> Old_Datatype_Aux.split_conj_thm
    |> map Old_Datatype_Aux.split_conj_thm
    |> flat
    |> filter_out (is_true o Thm.concl_of)
    |> map zero_var_indexes
  end

(* proof by rule induction over the alpha-definitions *)

fun alpha_prove alphas props alpha_induct_thm cases_tac ctxt =
  let
    val arg_tys = map (domain_type o fastype_of) alphas

    val ((arg_names1, arg_names2), ctxt') =
      ctxt
      |> Variable.variant_fixes (replicate (length alphas) "x")
      ||>> Variable.variant_fixes (replicate (length alphas) "y")

    val args1 = map2 (curry Free) arg_names1 arg_tys
    val args2 = map2 (curry Free) arg_names2 arg_tys

    val true_trms = replicate (length alphas) (K @{term True})

    fun apply_all x fs = map (fn f => f x) fs

    val goals_rhs =
        group (props @ (alphas ~~ true_trms))
        |> map snd
        |> map2 apply_all (args1 ~~ args2)
        |> map fold_conj

    fun apply_trm_pair t (ar1, ar2) = t $ ar1 $ ar2
    val goals_lhs = map2 apply_trm_pair alphas (args1 ~~ args2)

    val goals =
      (map2 (curry HOLogic.mk_imp) goals_lhs goals_rhs)
      |> foldr1 HOLogic.mk_conj
      |> HOLogic.mk_Trueprop

    fun tac ctxt =
      HEADGOAL
        (DETERM o (resolve_tac ctxt [alpha_induct_thm])
         THEN_ALL_NEW FIRST' [resolve_tac ctxt @{thms TrueI}, cases_tac ctxt])
  in
    Goal.prove ctxt' [] [] goals (fn {context, ...} => tac context)
    |> singleton (Proof_Context.export ctxt' ctxt)
    |> Old_Datatype_Aux.split_conj_thm
    |> map (fn th => th RS mp)
    |> map Old_Datatype_Aux.split_conj_thm
    |> flat
    |> filter_out (is_true o Thm.concl_of)
    |> map zero_var_indexes
  end



(** produces the distinctness theorems **)


(* transforms the distinctness theorems of the constructors
   into "not-alphas" of the constructors *)
fun mk_distinct_goal ty_trm_assoc neq =
  let
    val (Const (@{const_name "HOL.eq"}, ty_eq) $ lhs $ rhs) =
      HOLogic.dest_not (HOLogic.dest_Trueprop neq)
    val ty_str = fst (dest_Type (domain_type ty_eq))
  in
    Const (lookup ty_trm_assoc ty_str, ty_eq) $ lhs $ rhs
    |> HOLogic.mk_not
    |> HOLogic.mk_Trueprop
  end

fun distinct_tac ctxt cases_thms distinct_thms =
  resolve_tac ctxt [notI] THEN' eresolve_tac ctxt cases_thms
  THEN_ALL_NEW asm_full_simp_tac (put_simpset HOL_ss ctxt addsimps distinct_thms)

fun raw_prove_alpha_distincts ctxt alpha_result raw_dt_info =
  let
    val AlphaResult {alpha_names, alpha_cases, ...} = alpha_result
    val RawDtInfo {raw_dt_names, raw_distinct_thms, ...} = raw_dt_info

    val ty_trm_assoc = raw_dt_names ~~ alpha_names

    fun mk_alpha_distinct raw_distinct_trm =
      let
        val goal = mk_distinct_goal ty_trm_assoc raw_distinct_trm
    in
      Goal.prove ctxt [] [] goal
        (K (distinct_tac ctxt alpha_cases raw_distinct_thms 1))
    end
  in
    map (mk_alpha_distinct o Thm.prop_of) raw_distinct_thms
  end



(** produces the alpha_eq_iff simplification rules **)

(* in case a theorem is of the form (Rel Const Const), it will be
   rewritten to ((Rel Const = Const) = True)
*)
fun mk_simp_rule thm =
  case Thm.prop_of thm of
    @{term "Trueprop"} $ (_ $ Const _ $ Const _) => thm RS @{thm eqTrueI}
  | _ => thm

fun alpha_eq_iff_tac ctxt dist_inj intros elims =
  SOLVED' (asm_full_simp_tac (put_simpset HOL_ss ctxt addsimps intros)) ORELSE'
  (resolve_tac ctxt @{thms iffI} THEN'
    RANGE [eresolve_tac ctxt elims THEN_ALL_NEW asm_full_simp_tac (put_simpset HOL_ss ctxt addsimps dist_inj),
           asm_full_simp_tac (put_simpset HOL_ss ctxt addsimps intros)])

fun mk_alpha_eq_iff_goal thm =
  let
    val prop = Thm.prop_of thm;
    val concl = HOLogic.dest_Trueprop (Logic.strip_imp_concl prop);
    val hyps = map HOLogic.dest_Trueprop (Logic.strip_imp_prems prop);
    fun list_conj l = foldr1 HOLogic.mk_conj l;
  in
    if hyps = [] then HOLogic.mk_Trueprop concl
    else HOLogic.mk_Trueprop (HOLogic.mk_eq (concl, list_conj hyps))
  end;

fun raw_prove_alpha_eq_iff ctxt alpha_result raw_dt_info =
  let
    val AlphaResult {alpha_intros, alpha_cases, ...} = alpha_result
    val RawDtInfo {raw_distinct_thms, raw_inject_thms, ...} = raw_dt_info

    val ((_, thms_imp), ctxt') = Variable.import false alpha_intros ctxt;
    val goals = map mk_alpha_eq_iff_goal thms_imp;
    val tac = alpha_eq_iff_tac ctxt (raw_distinct_thms @ raw_inject_thms) alpha_intros alpha_cases 1;
    val thms = map (fn goal => Goal.prove ctxt' [] [] goal (K tac)) goals;
  in
    Variable.export ctxt' ctxt thms
    |> map mk_simp_rule
  end


(** reflexivity proof for the alphas **)

val exi_zero = @{lemma "P (0::perm) \<Longrightarrow> (\<exists>x. P x)" by auto}

fun cases_tac intros ctxt =
  let
    val prod_simps = @{thms split_conv prod_alpha_def rel_prod_conv}

    val unbound_tac = REPEAT o (eresolve_tac ctxt @{thms conjE}) THEN' assume_tac ctxt

    val bound_tac =
      EVERY' [ resolve_tac ctxt [exi_zero],
               resolve_tac ctxt @{thms alpha_refl},
               asm_full_simp_tac (put_simpset HOL_ss ctxt addsimps prod_simps) ]
  in
    resolve_tac ctxt intros THEN_ALL_NEW
      FIRST' [resolve_tac ctxt @{thms refl}, unbound_tac, bound_tac]
  end

fun raw_prove_refl ctxt alpha_result raw_dt_induct =
  let
    val AlphaResult {alpha_trms, alpha_tys, alpha_bn_trms, alpha_bn_tys, alpha_intros, ...} =
      alpha_result

    val props =
      map (fn (ty, c) => (ty, fn x => c $ x $ x))
        ((alpha_tys ~~ alpha_trms) @ (alpha_bn_tys ~~ alpha_bn_trms))
  in
    induct_prove alpha_tys props raw_dt_induct (cases_tac alpha_intros) ctxt
  end



(** symmetry proof for the alphas **)

val exi_neg = @{lemma "(\<exists>(p::perm). P p) \<Longrightarrow> (\<And>q. P q \<Longrightarrow> Q (- q)) \<Longrightarrow> \<exists>p. Q p"
  by (erule exE, rule_tac x="-p" in exI, auto)}

(* for premises that contain binders *)
fun prem_bound_tac pred_names alpha_eqvt ctxt =
  let
    fun trans_prem_tac pred_names ctxt =
      SUBPROOF (fn {prems, context = ctxt', ...} =>
        let
          val prems' = map (transform_prem1 ctxt' pred_names) prems
        in
          resolve_tac ctxt' prems' 1
        end) ctxt
    val prod_simps = @{thms split_conv permute_prod.simps prod_alpha_def rel_prod_conv alphas}
  in
    EVERY'
      [ eresolve_tac ctxt [exi_neg],
        resolve_tac ctxt @{thms alpha_sym_eqvt},
        asm_full_simp_tac (put_simpset HOL_ss ctxt addsimps prod_simps),
        eqvt_tac ctxt (eqvt_relaxed_config addpres alpha_eqvt) THEN'
        resolve_tac ctxt @{thms refl},
        trans_prem_tac pred_names ctxt]
  end

fun raw_prove_sym ctxt alpha_result alpha_eqvt =
  let
    val AlphaResult {alpha_names, alpha_trms, alpha_bn_names, alpha_bn_trms,
      alpha_intros, alpha_raw_induct, ...} = alpha_result

    val alpha_trms = alpha_trms @ alpha_bn_trms
    val alpha_names = alpha_names @ alpha_bn_names

    val props = map (fn t => fn (x, y) => t $ y $ x) alpha_trms

    fun tac ctxt =
      resolve_tac ctxt alpha_intros THEN_ALL_NEW
      FIRST' [assume_tac ctxt,
        resolve_tac ctxt @{thms sym} THEN' assume_tac ctxt,
        prem_bound_tac alpha_names alpha_eqvt ctxt]
  in
    alpha_prove alpha_trms (alpha_trms ~~ props) alpha_raw_induct tac ctxt
  end


(** transitivity proof for alphas **)

(* applies cases rules and resolves them with the last premise *)
fun ecases_tac cases =
  Subgoal.FOCUS (fn {context = ctxt, prems, ...} =>
    HEADGOAL (resolve_tac ctxt cases THEN' resolve_tac ctxt [List.last prems]))

fun aatac pred_names =
  SUBPROOF (fn {context = ctxt, prems, ...} =>
    HEADGOAL (resolve_tac ctxt (map (transform_prem1 ctxt pred_names) prems)))

(* instantiates exI with the permutation p + q *)
val perm_inst_tac =
  Subgoal.FOCUS (fn {context = ctxt, params, ...} =>
    let
      val (p, q) = apply2 snd (last2 params)
      val pq_inst = foldl1 (uncurry Thm.apply) [@{cterm "plus::perm => perm => perm"}, p, q]
      val exi_inst = Thm.instantiate' [SOME (@{ctyp "perm"})] [NONE, SOME pq_inst] @{thm exI}
    in
      HEADGOAL (resolve_tac ctxt [exi_inst])
    end)

fun non_trivial_cases_tac pred_names intros alpha_eqvt ctxt =
  let
    val prod_simps = @{thms split_conv alphas permute_prod.simps prod_alpha_def rel_prod_conv}
  in
    resolve_tac ctxt intros
    THEN_ALL_NEW (asm_simp_tac (put_simpset HOL_basic_ss ctxt) THEN'
      TRY o EVERY'   (* if binders are present *)
        [ eresolve_tac ctxt @{thms exE},
          eresolve_tac ctxt @{thms exE},
          perm_inst_tac ctxt,
          resolve_tac ctxt @{thms alpha_trans_eqvt},
          assume_tac ctxt,
          aatac pred_names ctxt,
          eqvt_tac ctxt (eqvt_relaxed_config addpres alpha_eqvt) THEN'
          resolve_tac ctxt @{thms refl},
          asm_full_simp_tac (put_simpset HOL_ss ctxt addsimps prod_simps) ])
  end

fun prove_trans_tac alpha_result raw_dt_thms alpha_eqvt ctxt =
  let
    val AlphaResult {alpha_names, alpha_bn_names, alpha_intros, alpha_cases, ...} = alpha_result
    val alpha_names = alpha_names @ alpha_bn_names

    fun all_cases ctxt =
      asm_full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps raw_dt_thms)
      THEN' TRY o non_trivial_cases_tac alpha_names alpha_intros alpha_eqvt ctxt
  in
    EVERY' [ resolve_tac ctxt @{thms allI},
      resolve_tac ctxt @{thms impI},
      ecases_tac alpha_cases ctxt THEN_ALL_NEW all_cases ctxt ]
  end

fun prep_trans_goal alpha_trm (arg1, arg2) =
  let
    val arg_ty = fastype_of arg1
    val mid = alpha_trm $ arg2 $ (Bound 0)
    val rhs = alpha_trm $ arg1 $ (Bound 0)
  in
    HOLogic.all_const arg_ty $ Abs ("z", arg_ty, HOLogic.mk_imp (mid, rhs))
  end

fun raw_prove_trans ctxt alpha_result raw_dt_thms alpha_eqvt =
  let
    val AlphaResult {alpha_names, alpha_trms, alpha_bn_names, alpha_bn_trms,
      alpha_raw_induct, ...} = alpha_result

    val alpha_trms = alpha_trms @ alpha_bn_trms

    val props = map prep_trans_goal alpha_trms
  in
    alpha_prove alpha_trms (alpha_trms ~~ props) alpha_raw_induct
      (prove_trans_tac alpha_result raw_dt_thms alpha_eqvt) ctxt
  end


(** proves the equivp predicate for all alphas **)

val reflp_def' =
  @{lemma "reflp R == \<forall>x. R x x" by (simp add: reflp_def refl_on_def)}

val symp_def' =
  @{lemma "symp R \<equiv> \<forall>x y . R x y --> R y x" by (simp add: symp_def sym_def)}

val transp_def' =
  @{lemma "transp R \<equiv> \<forall>x y. R x y \<longrightarrow> (\<forall>z. R y z \<longrightarrow> R x z)"
    by (rule eq_reflection, auto simp add: trans_def transp_def)}

fun raw_prove_equivp ctxt alpha_result refl symm trans =
  let
    val AlphaResult {alpha_trms, alpha_bn_trms, ...} = alpha_result

    val refl' = map (fold_rule ctxt [reflp_def'] o atomize ctxt) refl
    val symm' = map (fold_rule ctxt [symp_def'] o atomize ctxt) symm
    val trans' = map (fold_rule ctxt [transp_def'] o atomize ctxt) trans

    fun prep_goal t =
      HOLogic.mk_Trueprop (Const (@{const_name "equivp"}, fastype_of t --> @{typ bool}) $ t)
  in
    Goal.prove_common ctxt NONE [] [] (map prep_goal (alpha_trms @ alpha_bn_trms))
    (K (HEADGOAL (Goal.conjunction_tac THEN_ALL_NEW (resolve_tac ctxt @{thms equivpI} THEN'
       RANGE [resolve_tac ctxt refl', resolve_tac ctxt symm', resolve_tac ctxt trans']))))
    |> chop (length alpha_trms)
  end


(* proves that alpha_raw implies alpha_bn *)

fun raw_prove_bn_imp_tac alpha_result ctxt =
  SUBPROOF (fn {prems, context = ctxt', ...} =>
    let
      val AlphaResult {alpha_names, alpha_intros, ...} = alpha_result

      val prems' = flat (map Old_Datatype_Aux.split_conj_thm prems)
      val prems'' = map (transform_prem1 ctxt' alpha_names) prems'
    in
      HEADGOAL
        (REPEAT_ALL_NEW
           (FIRST' [ resolve_tac ctxt' @{thms TrueI},
                     resolve_tac ctxt' @{thms conjI},
                     resolve_tac ctxt' prems',
                     resolve_tac ctxt' prems'',
                     resolve_tac ctxt' alpha_intros ]))
    end) ctxt


fun raw_prove_bn_imp ctxt alpha_result =
  let
    val AlphaResult {alpha_trms, alpha_tys, alpha_bn_trms, alpha_raw_induct, ...} = alpha_result

    val arg_ty = domain_type o fastype_of
    val ty_assoc = alpha_tys ~~ alpha_trms
    val props = map (fn t => (lookup ty_assoc (arg_ty t), fn (x, y) => t $ x $ y)) alpha_bn_trms
  in
    alpha_prove (alpha_trms @ alpha_bn_trms) props alpha_raw_induct
      (raw_prove_bn_imp_tac alpha_result) ctxt
  end


(* respectfulness for fv_raw / bn_raw *)

fun raw_fv_bn_rsp_aux ctxt alpha_result fvs bns fv_bns simps =
  let
    val AlphaResult {alpha_trms, alpha_tys, alpha_bn_trms, alpha_raw_induct, ...} = alpha_result

    val arg_ty = domain_type o fastype_of
    val ty_assoc = alpha_tys ~~ alpha_trms
    fun mk_eq' t x y = HOLogic.mk_eq (t $ x, t $ y)

    val prop1 = map (fn t => (lookup ty_assoc (arg_ty t), fn (x, y) => mk_eq' t x y)) fvs
    val prop2 = map (fn t => (lookup ty_assoc (arg_ty t), fn (x, y) => mk_eq' t x y)) (bns @ fv_bns)
    val prop3 = map2 (fn t1 => fn t2 => (t1, fn (x, y) => mk_eq' t2 x y)) alpha_bn_trms fv_bns

    val simpset =
      put_simpset HOL_ss ctxt addsimps (simps @ @{thms alphas prod_fv.simps set_simps append.simps}
      @ @{thms Un_assoc Un_insert_left Un_empty_right Un_empty_left})
  in
    alpha_prove (alpha_trms @ alpha_bn_trms) (prop1 @ prop2 @ prop3) alpha_raw_induct
      (K (asm_full_simp_tac simpset)) ctxt
  end


(* respectfulness for size *)

fun raw_size_rsp_aux ctxt alpha_result simps =
  let
    val AlphaResult {alpha_trms, alpha_tys, alpha_bn_trms, alpha_bn_tys, alpha_raw_induct, ...} =
      alpha_result

    fun mk_prop ty (x, y) = HOLogic.mk_eq
      (HOLogic.size_const ty $ x, HOLogic.size_const ty $ y)

    val props = (alpha_trms @ alpha_bn_trms) ~~ (map mk_prop (alpha_tys @ alpha_bn_tys))

    val simpset =
      put_simpset HOL_ss ctxt addsimps (simps @ @{thms alphas prod_alpha_def rel_prod_conv
      permute_prod_def prod.case prod.rec})

    val tac = (TRY o REPEAT o eresolve_tac ctxt @{thms exE}) THEN' asm_full_simp_tac simpset
  in
    alpha_prove (alpha_trms @ alpha_bn_trms) props alpha_raw_induct (K tac) ctxt
  end


(* respectfulness for constructors *)

fun raw_constr_rsp_tac ctxt alpha_intros simps =
  let
    val pre_simpset = put_simpset HOL_ss ctxt addsimps @{thms rel_fun_def}
    val post_simpset = put_simpset HOL_ss ctxt addsimps @{thms alphas prod_alpha_def rel_prod_conv
      prod_fv.simps fresh_star_zero permute_zero prod.case} @ simps
  in
    asm_full_simp_tac pre_simpset
    THEN' REPEAT o (resolve_tac ctxt @{thms allI impI})
    THEN' resolve_tac ctxt alpha_intros
    THEN_ALL_NEW (TRY o (resolve_tac ctxt [exi_zero]) THEN' asm_full_simp_tac post_simpset)
  end

fun raw_constrs_rsp ctxt alpha_result constrs simps =
  let
    val AlphaResult {alpha_trms, alpha_tys, alpha_intros, ...} = alpha_result

    fun lookup ty =
      case AList.lookup (op=) (alpha_tys ~~ alpha_trms) ty of
        NONE => HOLogic.eq_const ty
      | SOME alpha => alpha

    fun rel_fun_app (t1, t2) =
      Const (@{const_name "rel_fun"}, dummyT) $ t1 $ t2

    fun prep_goal trm =
      trm
      |> strip_type o fastype_of
      |> (fn (tys, ty) => tys @ [ty])
      |> map lookup
      |> foldr1 rel_fun_app
      |> (fn t => t $ trm $ trm)
      |> Syntax.check_term ctxt
      |> HOLogic.mk_Trueprop
  in
    map (fn constrs =>
    Goal.prove_common ctxt NONE [] [] (map prep_goal constrs)
      (K (HEADGOAL
        (Goal.conjunction_tac THEN_ALL_NEW raw_constr_rsp_tac ctxt alpha_intros simps)))) constrs
  end


(* rsp lemmas for alpha_bn relations *)

val rsp_equivp =
  @{lemma "[|equivp Q; !!x y. R x y ==> Q x y|] ==> (R ===> R ===> (=)) Q Q"
    by (simp only: rel_fun_def equivp_def, metis)}


(* we have to reorder the alpha_bn_imps theorems in order
   to be in order with alpha_bn_trms *)
fun raw_alpha_bn_rsp alpha_result alpha_bn_equivp alpha_bn_imps =
  let
    val AlphaResult {alpha_bn_trms, ...} = alpha_result

    fun mk_map thm =
      thm |> `Thm.prop_of
          |>> List.last  o snd o strip_comb
          |>> HOLogic.dest_Trueprop
          |>> head_of
          |>> fst o dest_Const

    val alpha_bn_imps' =
      map (lookup (map mk_map alpha_bn_imps) o fst o dest_Const) alpha_bn_trms

    fun mk_thm thm1 thm2 =
      (forall_intr_vars thm2) COMP (thm1 RS rsp_equivp)
  in
    map2 mk_thm alpha_bn_equivp alpha_bn_imps'
  end


(* rsp for permute_bn functions *)

val perm_bn_rsp = @{lemma "(\<forall>x y p. R x y \<longrightarrow> R (f p x) (f p y)) \<Longrightarrow> ((=) ===> R ===> R) f f"
 by (simp add: rel_fun_def)}

fun raw_prove_perm_bn_tac alpha_result simps ctxt =
  SUBPROOF (fn {prems, context = ctxt', ...} =>
    let
      val AlphaResult {alpha_names, alpha_bn_names, alpha_intros, ...} = alpha_result
      val prems' = flat (map Old_Datatype_Aux.split_conj_thm prems)
      val prems'' = map (transform_prem1 ctxt' (alpha_names @ alpha_bn_names)) prems'
    in
      HEADGOAL
        (simp_tac (put_simpset HOL_basic_ss ctxt' addsimps (simps @ prems'))
         THEN' TRY o REPEAT_ALL_NEW
           (FIRST' [ resolve_tac ctxt' @{thms TrueI},
                     resolve_tac ctxt' @{thms conjI},
                     resolve_tac ctxt' @{thms refl},
                     resolve_tac ctxt' prems',
                     resolve_tac ctxt' prems'',
                     resolve_tac ctxt' alpha_intros ]))
    end) ctxt

fun raw_perm_bn_rsp ctxt alpha_result perm_bns simps =
  let
    val AlphaResult {alpha_trms, alpha_tys, alpha_bn_trms, alpha_bn_tys, alpha_raw_induct, ...} =
      alpha_result

    val perm_bn_ty = range_type o range_type o fastype_of
    val ty_assoc = (alpha_tys @ alpha_bn_tys) ~~ (alpha_trms @ alpha_bn_trms)

    val ([p], ctxt') = Variable.variant_fixes ["p"] ctxt
    val p = Free (p, @{typ perm})

    fun mk_prop t =
      let
        val alpha_trm = lookup ty_assoc (perm_bn_ty t)
      in
        (alpha_trm, fn (x, y) => alpha_trm $ (t $ p $ x) $ (t $ p $ y))
      end

    val goals = map mk_prop perm_bns
  in
    alpha_prove (alpha_trms @ alpha_bn_trms) goals alpha_raw_induct
      (raw_prove_perm_bn_tac alpha_result simps) ctxt
     |> Proof_Context.export ctxt' ctxt
     |> map (atomize ctxt)
     |> map single
     |> map (curry (op OF) perm_bn_rsp)
  end



(* transformation of the natural rsp-lemmas into standard form *)

val fun_rsp = @{lemma
  "(\<forall>x y. R x y \<longrightarrow> f x = f y) \<Longrightarrow> (R ===> (=)) f f" by (simp add: rel_fun_def)}

fun mk_funs_rsp ctxt thm =
  thm
  |> atomize ctxt
  |> single
  |> curry (op OF) fun_rsp


val permute_rsp = @{lemma
  "(\<forall>x y p. R x y \<longrightarrow> R (permute p x) (permute p y))
     ==> ((=) ===> R ===> R) permute permute"  by (simp add: rel_fun_def)}

fun mk_alpha_permute_rsp ctxt thm =
  thm
  |> atomize ctxt
  |> single
  |> curry (op OF) permute_rsp




end (* structure *)
