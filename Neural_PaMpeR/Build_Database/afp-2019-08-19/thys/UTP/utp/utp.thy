(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: utp.thy                                                              *)
(* Authors: Simon Foster and Frank Zeyda (University of York, UK)             *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)

section \<open> Meta-theory for the Standard Core \<close>

theory utp
imports
  utp_var
  utp_expr
  utp_expr_insts
  utp_expr_funcs
  utp_unrest
  utp_usedby
  utp_subst
  utp_meta_subst
  utp_alphabet
  utp_lift
  utp_pred
  utp_pred_laws
  utp_recursion
  utp_dynlog
  utp_rel
  utp_rel_laws
  utp_sequent
  utp_state_parser
  utp_sym_eval
  utp_tactics
  utp_hoare
  utp_wp
  utp_sp
  utp_theory
  utp_concurrency
  utp_rel_opsem
begin end