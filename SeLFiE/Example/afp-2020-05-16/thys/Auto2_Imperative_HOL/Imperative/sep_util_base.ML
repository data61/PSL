(*
  File: sep_util_base.ML
  Author: Bohua Zhan

  Declares the interface for setting up auto2 for separation logic.
*)

signature SEP_UTIL =
sig
  val assnT: typ
  val emp: term
  val assn_true: term
  val assn_ac_info: ac_info
  val is_true_assn: term -> bool
  val entail_t: term
  val is_entail: term -> bool
  val dest_entail: term -> term * term
  val cdest_entail: cterm -> cterm * cterm
  val is_ex_assn: term -> bool
  val is_pure_assn: term -> bool
  val has_pure_assn: term -> bool
  val strip_pure_assn: term -> term

  val hoare_triple_pat: term
  val heap_eq_pat: term
  val is_hoare_triple: term -> bool
  val dest_hoare_triple: term -> term * term * term

  val is_bind_cmd: term -> bool

  val mult_emp_left: conv
  val mult_emp_right: conv
  val reduce_emp_right: conv
  val entail_triv_th: Proof.context -> term -> thm
  val entail_true_th: Proof.context -> term -> thm
  val apply_to_entail_r: conv -> thm -> thm

  (* Basic theorems *)
  val pre_pure_rule_th: thm
  val pre_pure_rule_th': thm
  val pre_ex_rule_th: thm
  val entails_pure_th: thm
  val entails_pure_th': thm
  val entails_ex_th: thm
  val entails_frame_th': thm
  val entails_frame_th'': thm
  val pure_conj_th: thm
  val entails_ex_post_th: thm
  val entails_pure_post_th: thm
  val pre_rule_th': thm
  val pre_rule_th'': thm
  val bind_rule_th': thm
  val post_rule_th': thm
  val entails_equiv_forward_th: thm
  val entails_equiv_backward_th: thm
  val norm_pre_pure_iff_th: thm
  val norm_pre_pure_iff2_th: thm
  val entails_trans2_th: thm

  (* Extra functions *)
  val pure_ord: term * term -> bool
  val normalize_times_cv: Proof.context -> conv
  val normalize_assn_cv: Proof.context -> conv
  val assn_rewr_terms: term -> term list
end;
