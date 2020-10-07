(*
  File: sep_util.ML
  Author: Bohua Zhan

  Utility functions for separation logic. Implements the interface
  defined in sep_util_base.ML.
*)

structure SepUtil : SEP_UTIL =
struct

val assnT = @{typ assn}
val emp = @{term emp}
val assn_true = @{term true}
val assn_ac_info = Nat_Util.times_ac_on_typ @{theory} assnT

fun is_true_assn t =
    case t of
        Const (@{const_name top_assn}, _) => true
      | _ => false

val entail_t = @{term entails}

fun is_entail t =
    case t of
        Const (@{const_name entails}, _) $ _ $ _ => true
      | _ => false

(* Deconstruct A ==>_A B into (A, B). *)
fun dest_entail t =
    case t of
        Const (@{const_name entails}, _) $ A $ B => (A, B)
      | _ => raise Fail "dest_entail: unexpected t."

fun cdest_entail ct =
    case Thm.term_of ct of
        Const (@{const_name entails}, _) $ _ $ _ =>
        (Thm.dest_arg1 ct, Thm.dest_arg ct)
      | _ => raise Fail "dest_entail: unexpected t."

fun is_ex_assn t =
    case t of
        Const (@{const_name ex_assn}, _) $ _ => true
      | _ => false

(* Whether t is of the form \<up>(b). *)
fun is_pure_assn t =
    case t of
        Const (@{const_name pure_assn}, _) $ _ => true
      | _ => false

(* Given t of form t1 * ... * tn, check whether any of them is of the
   form \<up>(b).
 *)
fun has_pure_assn t =
    exists is_pure_assn (ACUtil.dest_ac assn_ac_info t)

(* Given t of form t1 * ... * tn, remove those ti that are pure
   assertions and return the product of the remaining terms.
 *)
fun strip_pure_assn t =
    if UtilArith.is_times t andalso is_pure_assn (dest_arg t) then
      strip_pure_assn (dest_arg1 t)
    else if is_pure_assn t then emp
    else t

val hoare_triple_pat = @{term_pat "<?P> ?c <?Q>"}
val heap_eq_pat = @{term_pat "(?c1::?'a Heap) = ?c2"}

fun is_hoare_triple t =
    case t of
        Const (@{const_name hoare_triple}, _) $ _ $ _ $ _ => true
      | _ => false

fun dest_hoare_triple t =
    case t of
        Const (@{const_name hoare_triple}, _) $ P $ c $ Q => (P, c, Q)
      | _ => raise Fail "dest_hoare_triple"

fun is_bind_cmd c =
    case c of
        Const (@{const_name bind}, _) $ _ $ _ => true
      | _ => false

(* Convert A to emp * A *)
val mult_emp_left = rewr_obj_eq (obj_sym @{thm mult_1})

(* Convert A to A * emp *)
val mult_emp_right = rewr_obj_eq (obj_sym @{thm mult_1_right})

(* Convert A * emp to A *)
val reduce_emp_right = rewr_obj_eq @{thm mult_1_right}

(* Given A of type assnT, return the theorem A ==> A. *)
fun entail_triv_th ctxt A =
    let
      val thy = Proof_Context.theory_of ctxt
      val inst = Pattern.first_order_match thy (Var (("A", 0), assnT), A) fo_init
    in
      Util.subst_thm ctxt inst @{thm entails_triv}
    end

(* Given A of type assnT, return the theorem A ==> true. *)
fun entail_true_th ctxt A =
    let
      val thy = Proof_Context.theory_of ctxt
      val inst = Pattern.first_order_match thy (Var (("A", 0), assnT), A) fo_init
    in
      Util.subst_thm ctxt inst @{thm entails_true}
    end

(* Given theorem A ==> B and a conversion cv, apply cv to B *)
val apply_to_entail_r = apply_to_thm' o Conv.arg_conv

val pre_pure_rule_th = @{thm pre_pure_rule}
val pre_pure_rule_th' = @{thm pre_pure_rule'}
val pre_ex_rule_th = @{thm pre_ex_rule}
val entails_pure_th = @{thm entails_pure}
val entails_pure_th' = @{thm entails_pure'}
val entails_ex_th = @{thm entails_ex}
val entails_frame_th' = @{thm entails_frame'}
val entails_frame_th'' = @{thm entails_frame''}
val pure_conj_th = @{thm pure_conj}
val entails_ex_post_th = @{thm entails_ex_post}
val entails_pure_post_th = @{thm entails_pure_post}
val pre_rule_th' = @{thm pre_rule'}
val pre_rule_th'' = @{thm pre_rule''}
val bind_rule_th' = @{thm bind_rule'}
val post_rule_th' = @{thm post_rule'}
val entails_equiv_forward_th = @{thm entails_equiv_forward}
val entails_equiv_backward_th = @{thm entails_equiv_backward}
val norm_pre_pure_iff_th = @{thm norm_pre_pure_iff}
val norm_pre_pure_iff2_th = @{thm norm_pre_pure_iff2}
val entails_trans2_th = @{thm entails_trans2}

(* Extra functions *)

fun is_case_prod t =
    case t of
        Const (@{const_name case_prod}, _) $ _ $ _ => true
      | _ => false

fun sort_by t =
    case t of
        Const (@{const_name pure_assn}, _) $ _ => 2
      | Const (@{const_name top_assn}, _) => 1
      | _ => 0

fun pure_ord (t, s) =
    if sort_by t = 0 andalso sort_by s = 0 then
      Term_Ord.term_ord (t, s) = LESS
    else
      sort_by t < sort_by s

fun normalize_times_cv ctxt ct =
    let
      val (A, B) = Util.dest_binop_args (Thm.term_of ct)
    in
      if is_ex_assn A then
        Conv.every_conv [rewr_obj_eq (obj_sym @{thm ex_distrib_star}),
                         Conv.binder_conv (normalize_times_cv o snd) ctxt] ct
      else if is_ex_assn B then
        Conv.every_conv [ACUtil.comm_cv assn_ac_info,
                         normalize_times_cv ctxt] ct
      else
        Conv.every_conv [
          ACUtil.normalize_au assn_ac_info,
          ACUtil.normalize_comm_gen assn_ac_info pure_ord,
          ACUtil.norm_combine assn_ac_info is_true_assn
                              (rewr_obj_eq @{thm top_assn_reduce})] ct
    end

(* Normalization function for assertions. This function pulls all EX_A
   to the front, then apply AC-rules to the inside, putting all pure
   assertions on the right.
 *)
fun normalize_assn_cv ctxt ct =
    let
      val t = Thm.term_of ct
    in
      if is_ex_assn t then
        Conv.binder_conv (normalize_assn_cv o snd) ctxt ct
      else if UtilArith.is_times t then
        Conv.every_conv [Conv.binop_conv (normalize_assn_cv ctxt),
                         normalize_times_cv ctxt] ct
      else if is_pure_assn t andalso is_conj (dest_arg t) then
        Conv.every_conv [rewr_obj_eq @{thm pure_conj},
                         normalize_assn_cv ctxt] ct
      else if is_case_prod t then
        Conv.every_conv [rewr_obj_eq @{thm case_prod_beta},
                         normalize_assn_cv ctxt] ct
      else
        Conv.all_conv ct
    end

(* Rewrite terms for an assertion *)
fun assn_rewr_terms P =
    P |> ACUtil.dest_ac assn_ac_info
      |> filter_out is_pure_assn
      |> maps (snd o Term.strip_comb)
      |> distinct (op aconv)

end  (* structure SepUtil *)
