(*
  File: util_base.ML
  Author: Bohua Zhan

  Defines the interface that an object logic has to meet to setup auto2.
*)

signature BASIC_UTIL_BASE =
sig
  val boolT: typ

  val dest_eq: term -> term * term
  val cdest_eq: cterm -> cterm * cterm
  val mk_eq: term * term -> term
  val is_eq_term: term -> bool

  val bFalse: term
  val bTrue: term
  val true_th: thm
end;

signature UTIL_BASE =
sig
  include BASIC_UTIL_BASE

  (* Types *)
  val mk_setT: typ -> typ

  (* Terms *)
  val Trueprop_name: string
  val Not_name: string
  val Conj_name: string
  val Disj_name: string
  val Imp_name: string
  val All_name: string
  val Ex_name: string
  val is_if: term -> bool

  (* Cterms *)
  val cTrueprop: cterm
  val cNot: cterm
  val cConj: cterm
  val cDisj: cterm

  (* Theorems for equality *)
  val to_meta_eq_cv: conv
  val to_obj_eq_cv: conv
  val to_obj_eq_iff: thm -> thm
  val obj_sym_cv: conv

  (* Theorems *)
  val iffD_th: thm
  val nn_create_th: thm
  val nn_cancel_th: thm
  val to_contra_form_th: thm
  val to_contra_form_th': thm
  val atomize_imp_th: thm
  val atomize_all_th: thm
  val conjunct1_th: thm
  val conjunct2_th: thm
  val conjI_th: thm
  val or_intro1_th: thm
  val or_intro2_th: thm
  val iffD1_th: thm
  val iffD2_th: thm
  val inv_back_th: thm
  val sym_th: thm
  val exE_th': thm
  val eq_True_th: thm
  val eq_True_inv_th: thm
  val disj_True1_th: thm
  val disj_True2_th: thm
  val ex_vardef_th: thm
  val imp_conv_disj_th: thm
  val de_Morgan_conj_th: thm
  val de_Morgan_disj_th: thm
  val not_ex_th: thm
  val not_all_th: thm
  val not_imp_th: thm
  val or_cancel1_th: thm
  val or_cancel2_th: thm
  val swap_all_disj_th: thm
  val swap_ex_conj_th: thm
  val all_trivial_th: thm
  val case_split_th: thm

  (* Theorems for proofstep module *)
  val atomize_conjL_th: thm
  val backward_conv_th: thm
  val backward1_conv_th: thm
  val backward2_conv_th: thm
  val resolve_conv_th: thm

  (* Other theorems *)
  val contra_triv_th: thm

  (* AC for conj and disj *)
  val conj_assoc_th: thm
  val conj_commute_th: thm
  val disj_assoc_th: thm
  val disj_commute_th: thm

  (* Member, Ball and Bex *)
  val Mem_name: string
  val Ball_name: string
  val Bex_name: string
  val Bex_def_th: thm
  val Ball_def_th: thm
end
