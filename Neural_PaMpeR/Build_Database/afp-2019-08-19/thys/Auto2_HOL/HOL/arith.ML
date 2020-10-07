(*
  File: arith.ML
  Author: Bohua Zhan

  Arithmetic proof steps.
*)

signature NAT_UTIL =
sig
  val lookup_numc: Type.tyenv * Envir.tenv -> int -> int
  val lookup_numc0: Type.tyenv * Envir.tenv -> int
  val lookup_numc1: Type.tyenv * Envir.tenv -> int
  val lookup_numc2: Type.tyenv * Envir.tenv -> int
  val mk_nat: int -> term
  val mk_int: int -> term
  val nat0: term
  val cnat0: cterm

  val mk_less: term * term -> term
  val mk_le: term * term -> term
  val nat_le_th: int -> int -> thm
  val nat_less_th: int -> int -> thm
  val nat_neq_th: int -> int -> thm
  val nat_fold_reduce: term -> term
  val nat_fold_conv: conv

  val plus_ac_on_typ: theory -> typ -> ac_info
  val times_ac_on_typ: theory -> typ -> ac_info
  val add_arith_ac_data: theory -> theory
  val add_arith_proofsteps: theory -> theory
end;

structure Nat_Util : NAT_UTIL =
struct

fun lookup_numc inst n = UtilArith.dest_numc (lookup_instn inst ("NUMC", n))
fun lookup_numc0 inst = lookup_numc inst 0
fun lookup_numc1 inst = lookup_numc inst 1
fun lookup_numc2 inst = lookup_numc inst 2
fun mk_nat n = HOLogic.mk_number natT n
fun mk_int n = HOLogic.mk_number intT n
val nat0 = mk_nat 0
val cnat0 = @{cterm "0::nat"}

local
  val ctxt = @{context}
in

fun mk_less (m, n) =
    Const (@{const_name less}, natT --> natT --> boolT) $ m $ n

fun mk_le (m, n) =
    Const (@{const_name less_eq}, natT --> natT --> boolT) $ m $ n

(* Obtain the theorem m <= n. *)
fun nat_le_th m n =
    if m > n then raise Fail "nat_le_th: input"
    else UtilArith.prove_by_arith ctxt [] (mk_le (mk_nat m, mk_nat n))

(* Obtain the theorem m < n. *)
fun nat_less_th m n =
    if m >= n then raise Fail "nat_less_th: input"
    else UtilArith.prove_by_arith ctxt [] (mk_less (mk_nat m, mk_nat n))

(* Obtain the theorem m ~= n. *)
fun nat_neq_th m n =
    if m = n orelse m < 0 orelse n < 0 then raise Fail "nat_neq_th: input"
    else UtilArith.prove_by_arith ctxt [] (mk_not (mk_eq (mk_nat m, mk_nat n)))

fun nat_fold_reduce t =
    if fastype_of t <> natT then t else
    let
      val (f, (n1, n2)) = t |> Util.dest_binop |> apsnd (apply2 UtilArith.dest_numc)
    in
      case f of
          Const (@{const_name plus}, _) => mk_nat (n1 + n2)
        | Const (@{const_name minus}, _) => mk_nat (Int.max (0, n1 - n2))
        | Const (@{const_name times}, _) => mk_nat (n1 * n2)
        | _ => t
    end
    handle Fail "dest_binop" => t | Fail "dest_numc" => t

fun nat_fold_conv ct =
    let
      val t = Thm.term_of ct
      val t' = nat_fold_reduce t
    in
      if t aconv t' then Conv.all_conv ct
      else to_meta_eq (UtilArith.prove_by_arith ctxt [] (mk_eq (t, t')))
    end

end  (* local ctxt = @{context}. *)

val plus_ac =
    {cfhead = @{cterm plus}, unit = SOME @{cterm 0},
     assoc_th = @{thm add_ac(1)}, comm_th = @{thm add_ac(2)},
     unitl_th = @{thm add_0}, unitr_th = @{thm add_0_right}}

val times_ac =
    {cfhead = @{cterm times}, unit = SOME @{cterm 1},
     assoc_th = @{thm mult_ac(1)}, comm_th = @{thm mult_ac(2)},
     unitl_th = @{thm mult_1}, unitr_th = @{thm mult_1_right}}

val gcd_ac =
    {cfhead = @{cterm gcd}, unit = SOME @{cterm 0},
     assoc_th = @{thm gcd.assoc}, comm_th = @{thm gcd.commute},
     unitl_th = @{thm gcd_0_left_nat}, unitr_th = @{thm gcd_0_nat}}

val add_arith_ac_data =
    fold ACUtil.add_ac_data [plus_ac, times_ac, gcd_ac]

fun plus_ac_on_typ thy T =
    the (ACUtil.inst_ac_info thy T plus_ac)
    handle Option.Option => raise Fail "plus_ac_on_typ: cannot inst ac_info."

fun times_ac_on_typ thy T =
    the (ACUtil.inst_ac_info thy T times_ac)
    handle Option.Option => raise Fail "times_ac_on_typ: cannot inst ac_info."

val add_arith_proofsteps =
    fold add_prfstep_custom [
      (* Resolve equality facts with constants. *)
      ("compare_consts",
       [WithFact @{term_pat "(?NUMC1::nat) = ?NUMC2"},
        Filter (fn _ => fn (_, inst) =>
                   lookup_numc1 inst <> lookup_numc2 inst)],
       fn ((id, _), ths) => fn _ => fn ctxt =>
          [Update.thm_update (id, UtilArith.contra_by_arith ctxt ths)]),

      ("compare_consts_le",
       [WithFact @{term_pat "(?NUMC1::nat) <= ?NUMC2"},
        Filter (fn _ => fn (_, inst) =>
                   lookup_numc1 inst > lookup_numc2 inst)],
       fn ((id, _), ths) => fn _ => fn ctxt =>
          [Update.thm_update (id, UtilArith.contra_by_arith ctxt ths)]),

      ("compare_consts_less",
       [WithFact @{term_pat "(?NUMC1::nat) < ?NUMC2"},
        Filter (fn _ => fn (_, inst) =>
                   lookup_numc1 inst >= lookup_numc2 inst)],
       fn ((id, _), ths) => fn _ => fn ctxt =>
          [Update.thm_update (id, UtilArith.contra_by_arith ctxt ths)])

    ] #> fold add_prfstep_conv [
      ("eval_plus_consts",
       [WithTerm @{term_pat "(?NUMC1::nat) + ?NUMC2"},
        Filter (fn _ => fn (_, inst) =>
                   lookup_numc1 inst > 0 andalso lookup_numc2 inst > 0)],
       nat_fold_conv),

      ("eval_mult_consts",
       [WithTerm @{term_pat "(?NUMC1::nat) * ?NUMC2"},
        Filter (fn _ => fn (_, inst) =>
                   lookup_numc1 inst <> 1 andalso lookup_numc2 inst <> 1)],
       nat_fold_conv),

      ("eval_minus_consts",
       [WithTerm @{term_pat "(?NUMC1::nat) - ?NUMC2"},
        Filter (fn _ => fn (_, inst) => lookup_numc2 inst >= 1)],
       nat_fold_conv)]

end  (* structure Nat_Util. *)

val mk_nat = Nat_Util.mk_nat
val mk_int = Nat_Util.mk_int
val plus_ac_on_typ = Nat_Util.plus_ac_on_typ
val times_ac_on_typ = Nat_Util.times_ac_on_typ
val _ = Theory.setup Nat_Util.add_arith_ac_data
val _ = Theory.setup Nat_Util.add_arith_proofsteps
