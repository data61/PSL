(*
 * Copyright (C) 2014 NICTA
 * All rights reserved.
 *)

(* Author: David Cock - David.Cock@nicta.com.au *)

(* This file implements a simple verification condition generator
   (VCG), for probabilistic programs written in pGCL. *)

signature pVCG_sig =
sig
        val pVCG_tac: Proof.context -> int -> tactic;
end;

structure pVCG =
struct

val pvcg_trace = Attrib.setup_config_bool @{binding "trace_pvcg"} (K false)

fun trace ctxt str =
    if Config.get ctxt pvcg_trace then tracing ("pVCG: " ^ str) else {}

fun trace_pre ctxt str T =
    (trace ctxt str ; T)

(* Match soundness goals on non-schematic expectations *)
fun m_sound t =
  case t of
    @{term "Trueprop"} $ (Const ("Expectations.sound",_) $ Var _) => false
  | @{term "Trueprop"} $ (Const ("Expectations.unitary",_) $ Var _) => false
  | @{term "Trueprop"} $ (Const ("Expectations.sound",_) $ _) => true
  | @{term "Trueprop"} $ (Const ("Expectations.unitary",_) $ _) => true
  | _ => false

(* Match well-definedness goals on non-schematic expectations *)
fun m_wd t =
  case t of
    @{term "Trueprop"} $ (Const ("WellDefined.well_def",_) $ Var _) => false
  | @{term "Trueprop"} $ (Const ("WellDefined.well_def",_) $ _) => true
  | _ => false

fun sound_goal_tac ctxt =
  resolve_tac ctxt @{thms sound_intros unitary_intros}
fun maybe_sound_tac ctxt (g,i) =
  if m_sound g
  then trace_pre ctxt ("soundness goal " ^
                   Pretty.string_of (Syntax.pretty_term ctxt g))
                  (sound_goal_tac ctxt i)
  else no_tac
fun sound_tac ctxt = SUBGOAL (maybe_sound_tac ctxt)

fun wd_goal_tac ctxt =
  resolve_tac ctxt (rev (Named_Theorems.get ctxt @{named_theorems wd}))
fun maybe_wd_tac ctxt (g,i) =
  if m_wd g
  then trace_pre ctxt "well-definedness goal" (wd_goal_tac ctxt i)
  else no_tac
fun wd_tac ctxt = SUBGOAL (maybe_wd_tac ctxt)

(* Attempt to solve a side-condition (healthiness or soundness) *)
fun sidegoal_tac ctxt =
  REPEAT_ALL_NEW (CHANGED o (wd_tac ctxt ORELSE'
                  sound_tac ctxt ORELSE'
                  asm_full_simp_tac ctxt))

fun wp_start ctxt =
  (resolve_tac ctxt @{thms wp_weaken_pre} ORELSE' resolve_tac ctxt @{thms wlp_weaken_pre})
  THEN_ALL_NEW ((sidegoal_tac ctxt) ORELSE' (K all_tac))

fun user_wp_rules ctxt = rev (Named_Theorems.get ctxt @{named_theorems pwp})

fun mod_user_wp_rules ctxt =
  map (fn thm => thm RS @{thm wp_strengthen_post[OF _ well_def_wp_healthy]})
                        (user_wp_rules ctxt)

fun user_wlp_rules ctxt = rev (Named_Theorems.get ctxt @{named_theorems pwlp})

fun mod_user_wlp_rules ctxt =
  map (fn thm => thm RS @{thm wlp_strengthen_post[OF _ well_def_wlp_nearly_healthy]})
                        (user_wlp_rules ctxt)

fun core_rules ctxt = rev (Named_Theorems.get ctxt @{named_theorems pwp_core})

(* Prefer raw user rules, then lifted user rules, then core (safe) rules *)
fun wp_step ctxt =
  (trace_pre ctxt "user WP" (resolve_tac ctxt (user_wp_rules ctxt)) ORELSE'
   resolve_tac ctxt (mod_user_wp_rules ctxt) ORELSE'
   resolve_tac ctxt (user_wlp_rules ctxt) ORELSE'
   resolve_tac ctxt (mod_user_wlp_rules ctxt) ORELSE'
   resolve_tac ctxt (core_rules ctxt)) THEN_ALL_NEW
  (sidegoal_tac ctxt ORELSE' K all_tac)

fun pVCG_tac ctxt =
  (trace_pre ctxt "start" (wp_start ctxt) THEN'
   REPEAT_ALL_NEW (wp_step ctxt)) THEN_ALL_NEW
   (TRY o sidegoal_tac ctxt) THEN'
  (fn _ => trace_pre ctxt "finished" all_tac)

end;

structure pVCGInst : pVCG_sig = pVCG;
