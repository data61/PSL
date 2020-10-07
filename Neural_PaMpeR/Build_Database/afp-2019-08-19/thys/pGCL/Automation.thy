(*
 * Copyright (C) 2014 NICTA
 * All rights reserved.
 *)

(* Author: David Cock - David.Cock@nicta.com.au *)

section "Automated Reasoning"

theory Automation imports StructuredReasoning
begin

text \<open>This theory serves as a container for automated reasoning
  tactics for pGCL, implemented in ML.  At present, there is a basic
  verification condition generator (VCG).\<close>

named_theorems wd
  "theorems to automatically establish well-definedness"
named_theorems pwp_core
  "core probabilistic wp rules, for evaluating primitive terms"
named_theorems pwp
  "user-supplied probabilistic wp rules"
named_theorems pwlp
  "user-supplied probabilistic wlp rules"

ML_file \<open>pVCG.ML\<close>

method_setup pvcg =
  \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (pVCG.pVCG_tac ctxt))\<close>
  "Probabilistic weakest preexpectation tactic"

declare wd_intros[wd]

lemmas core_wp_rules =
  wp_Skip        wlp_Skip
  wp_Abort       wlp_Abort
  wp_Apply       wlp_Apply
  wp_Seq         wlp_Seq
  wp_DC_split    wlp_DC_split
  wp_PC_fixed    wlp_PC_fixed
  wp_SetDC       wlp_SetDC
  wp_SetPC_split wlp_SetPC_split

declare core_wp_rules[pwp_core]

end
