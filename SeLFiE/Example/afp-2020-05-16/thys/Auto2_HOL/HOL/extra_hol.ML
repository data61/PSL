(*
  File: extra_hol.ML
  Author: Bohua Zhan

  Extra setup for HOL.
*)

signature EXTRA_HOL =
sig
  val add_forward_arg1_prfstep_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_forward_arg1_prfstep: thm -> theory -> theory
  val add_forward_arg_prfstep_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_forward_arg_prfstep: thm -> theory -> theory
  val add_rewrite_arg_rule_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_rewrite_arg_rule: thm -> theory -> theory

  val add_simple_datatype: string -> theory -> theory
  val del_simple_datatype: string -> theory -> theory
end;

structure Extra_HOL : EXTRA_HOL =
struct

fun add_forward_arg1_prfstep_cond th conds thy =
    let
      val concl = th |> concl_of' |> strip_conj |> hd
    in
      thy |> add_forward_prfstep_cond
          th ([K (WithTerm (dest_arg1 concl))] @ conds)
    end

fun add_forward_arg1_prfstep th = add_forward_arg1_prfstep_cond th []

fun add_forward_arg_prfstep_cond th conds thy =
    let
      val concl = th |> concl_of' |> strip_conj |> hd
    in
      thy |> add_forward_prfstep_cond
          th ([K (WithTerm (dest_arg concl))] @ conds)
    end

fun add_forward_arg_prfstep th = add_forward_arg_prfstep_cond th []

fun add_rewrite_arg_rule_cond th conds thy =
    let
      val concl = th |> concl_of' |> strip_conj |> hd
      val _ = assert (is_eq_term concl) "rewrite_arg"
      val (lhs, _) = dest_eq concl
    in
      thy |> add_forward_prfstep_cond
          th ([K (WithTerm (dest_arg lhs))] @ conds)
    end

fun add_rewrite_arg_rule th = add_rewrite_arg_rule_cond th []

fun add_simple_datatype s thy =
    let
      val collapse_th = Global_Theory.get_thm thy (s ^ ".collapse")
      val case_th = Global_Theory.get_thm thy (s ^ ".case")
      val sel_th = Global_Theory.get_thms thy (s ^ ".sel")
      val simp_th = hd (Global_Theory.get_thms thy (s ^ ".simps"))
      val var = collapse_th |> prop_of' |> dest_arg
      val (f, args) = collapse_th |> prop_of' |> dest_arg1 |> Term.strip_comb
      val vars = map (fn (n, T) => Var (("x",n),T))
                     (tag_list 1 (map fastype_of args))
      val rhs = Term.list_comb (f, vars)
      val neq = get_neg (mk_eq (var, rhs))
      val filt = [with_filt (neq_filter neq)]
    in
      thy |> add_rewrite_rule_back_cond collapse_th filt
          |> add_rewrite_rule case_th
          |> fold add_rewrite_rule sel_th
          |> add_forward_prfstep (equiv_forward_th simp_th)
    end

fun del_simple_datatype s thy =
    let
      val collapse_th = Global_Theory.get_thm thy (s ^ ".collapse")
      val case_th = Global_Theory.get_thm thy (s ^ ".case")
      val sel_th = Global_Theory.get_thms thy (s ^ ".sel")
      val simp_th = hd (Global_Theory.get_thms thy (s ^ ".simps"))
    in
      thy |> fold del_prfstep_thm (collapse_th :: case_th :: simp_th :: sel_th)
    end

end  (* structure Extra_HOL *)

open Extra_HOL
