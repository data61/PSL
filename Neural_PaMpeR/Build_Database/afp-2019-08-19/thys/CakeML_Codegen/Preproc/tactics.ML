signature TACTICS = sig
  type rs = {rs_def: thm, simps: thm list, restrict: string list option}

  val wellformed_tac: Proof.context -> int -> tactic
  val beta_reduce_tac: Proof.context -> int -> tactic
  val rewrite_step_tac: Proof.context -> rs -> int -> tactic
  val rewrite_beta_tac: Proof.context -> int -> tactic
  val rewrite_single_tac: Proof.context -> rs option -> int -> tactic
  val rewrite_tac: Proof.context -> rs option -> int -> tactic
  val rewrite1_tac: Proof.context -> rs option -> int -> tactic
  val elims_wellformed: thm -> thm list
  val elims_injects: Proof.context -> thm list -> thm -> thm list
  val eval_ext_tac: Proof.context -> int -> tactic
  val eval_app_tac: Proof.context -> int -> tactic
  val eval_assm_tac: Proof.context -> int -> tactic
  val eval_data_tac: Proof.context -> int -> tactic
  val eval_base_tac: Proof.context -> thm list -> int -> tactic
  val eval_tac: Proof.context -> thm list -> int -> tactic
end

structure Tactics : TACTICS = struct

open Dict_Construction_Util

type rs = {rs_def: thm, simps: thm list, restrict: string list option}

fun elims_wellformed thm =
  let
    val thms = cat_options (map (try (fn t => t OF [thm])) @{thms wellformed_unpack})
  in
    if null thms then
      [thm]
    else
      maps elims_wellformed thms
  end

fun gather_wellformed thms =
  let
    fun is_wellformed (@{const Trueprop} $ (@{const wellformed'} $ _ $ _)) = true
      | is_wellformed _ = false
    fun dest_eval thm =
      case Thm.prop_of thm of
        (@{const Trueprop} $ (Const (@{const_name eval'}, _) $ _ $ _ $ _)) =>
          try (curry op OF @{thm eval'_impl_wellformed}) [thm]
      | (@{const Trueprop} $ (Const (@{const_name eval}, _) $ _ $ _ $ _)) =>
          try (curry op OF @{thm eval_impl_wellformed}) [thm]
      | _ =>
          NONE

    val derived_wellformed = cat_options (map dest_eval thms)
    val existing_wellformed = filter (is_wellformed o Thm.prop_of) thms
  in
    maps elims_wellformed (derived_wellformed @ existing_wellformed)
  end

local

val code_tac = Code_Simp.static_tac {consts = [@{const_name wellformed'}], ctxt = @{context}, simpset = NONE}

in

val wellformed_tac = Subgoal.FOCUS (fn {context = ctxt, prems, ...} =>
  let
    val all_wellformed = gather_wellformed prems

    val tac =
      code_tac ctxt THEN_ALL_NEW
        REPEAT_ALL_NEW (resolve_tac ctxt (@{thms conjI TrueI} @ all_wellformed))
  in
    HEADGOAL (SOLVED' (REPEAT_ALL_NEW tac))
  end)

end

val replace_bound_simps =
  map safe_mk_meta_eq @{thms replace_bound_aux replace_bound.simps incr_bounds.simps incr_bounds_zero}

val beta_reduce_tac = Subgoal.FOCUS_PREMS (fn {context = ctxt, prems, ...} =>
  let
    val replace_bound_eqs =
      gather_wellformed prems
      |> map (fn thm => safe_mk_meta_eq (@{thm wellformed_replace_bound_eq} OF [thm]))
    val conv = Raw_Simplifier.rewrite ctxt false (replace_bound_eqs @ replace_bound_simps)
  in
    HEADGOAL (CHANGED o CONVERSION conv)
  end)

fun rewrite_beta_tac ctxt =
  resolve_tac ctxt @{thms r_into_rtranclp} THEN'
    (resolve_tac ctxt @{thms rewrite_beta_alt} CONTINUE_WITH
      [beta_reduce_tac ctxt THEN' resolve_tac ctxt @{thms refl},
       wellformed_tac ctxt])

local

val code_tac =
  Code_Simp.static_tac {consts = [@{const_name rewrite_step_term}, @{const_name HOL.eq}], ctxt = @{context}, simpset = NONE}

in

fun rewrite_step_tac ctxt {rs_def, simps, restrict} = Subgoal.FOCUS_PREMS (fn {context = ctxt, ...} =>
  let
    val restrict = case restrict of
      NONE => I
    | SOME names => filter (member op = names o fst o dest_Const o fst o strip_comb o fst)

    val rules =
      map (Logic.dest_equals o Thm.prop_of) simps
      |> restrict
      |> map (HOLogic.mk_prod o @{apply 2} (HOL_Term.mk_term true))

    val elem = REPEAT_ALL_NEW (resolve_tac ctxt @{thms finsertI1 finsertI2})
    fun try_rule r =
      resolve_tac ctxt [Drule.infer_instantiate ctxt [(("r", 0), Thm.cterm_of ctxt r)] @{thm rewrite.step}] CONTINUE_WITH_FW
        [SELECT_GOAL (Local_Defs.unfold_tac ctxt [rs_def]) THEN' elem,
         code_tac ctxt]
  in
    HEADGOAL (resolve_tac ctxt @{thms r_into_rtranclp} THEN' FIRST' (map (SOLVED' o try_rule) rules))
  end) ctxt

end

fun rewrite_single_tac ctxt opt_rs =
  let
    fun do_rec n st = rewrite_single_tac ctxt opt_rs n st

    val prems_tac = SOLVED' (Method.assm_tac ctxt)
    val step_tac = case opt_rs of
      NONE => K no_tac
    | SOME rs => rewrite_step_tac ctxt rs

    val beta_tac = rewrite_beta_tac ctxt
    val fun_tac = resolve_tac ctxt @{thms rewrite_rt_fun} THEN' SOLVED' do_rec
    val arg_tac = resolve_tac ctxt @{thms rewrite_rt_arg} THEN' SOLVED' do_rec
  in FIRST' [prems_tac, beta_tac, step_tac, fun_tac, arg_tac] end

fun rewrite_tac ctxt opt_rs =
  resolve_tac ctxt @{thms rtranclp_trans} CONTINUE_WITH_FW
    [SOLVED' (rewrite_single_tac ctxt opt_rs),
     (fn n => rewrite_tac ctxt opt_rs n)] ORELSE'
    resolve_tac ctxt @{thms rtranclp.rtrancl_refl}

fun rewrite1_tac ctxt opt_rs =
  resolve_tac ctxt @{thms rtranclp_trans} CONTINUE_WITH_FW
    [SOLVED' (rewrite_single_tac ctxt opt_rs),
     (fn n => rewrite_tac ctxt opt_rs n)]

fun elims_injects ctxt injects thm =
  let
    val thms =
      map (fn i => try (curry op OF @{thm iffD1}) [i, thm]) injects
      |> cat_options
      |> maps (HOLogic.conj_elims ctxt)
  in
    if null thms then
      [thm]
    else
      maps (elims_injects ctxt injects) thms
  end

fun eval_ext_tac ctxt =
  resolve_tac ctxt @{thms eval'_ext_alt} CONTINUE_WITH_FW
    [wellformed_tac ctxt,
     beta_reduce_tac ctxt]

val eval_app_tac =
  fo_rtac @{thm eval'_funD}

val eval_assm_tac = Subgoal.FOCUS_PREMS (fn {context = ctxt, prems, ...} =>
  HEADGOAL (resolve_tac ctxt prems))

fun eval_data_tac ctxt =
  let
    val intros = Named_Theorems.get ctxt @{named_theorems eval_data_intros}
  in
    resolve_tac ctxt intros THEN'
      SOLVED' (wellformed_tac ctxt) THEN'
      SOLVED' (rewrite_tac ctxt NONE)
  end

val eval_base_tac = resolve_tac

fun eval_tac ctxt base_thms =
  REPEAT_ALL_NEW (ANY'
    [eval_data_tac ctxt,
     eval_base_tac ctxt base_thms,
     eval_assm_tac ctxt,
     eval_app_tac ctxt,
     eval_ext_tac ctxt])

end