(*
  File: util_arith.ML
  Author: Bohua Zhan

  Utility functions related to arithmetic.
*)

signature UTIL_ARITH =
sig
  (* Types. *)
  val natT: typ
  val intT: typ
  val ratT: typ
  val rat_zero: Rat.rat

  (* Terms. *)
  val is_numc: term -> bool
  val dest_numc: term -> int
  val dest_numc_rat: term -> Rat.rat
  val is_order: term -> bool
  val is_linorder: Proof.context -> term -> bool
  val is_plus: term -> bool
  val is_minus: term -> bool
  val is_times: term -> bool
  val is_divide: term -> bool
  val is_zero: term -> bool
  val is_one: term -> bool

  (* Theorems. *)
  val neg_ineq_cv: conv
  val neg_ineq_back_cv: conv

  (* Arith tactic. *)
  val prove_by_arith: Proof.context -> thm list -> term -> thm
  val contra_by_arith: Proof.context -> thm list -> thm
end;

structure UtilArith : UTIL_ARITH =
struct

val natT = HOLogic.natT
val intT = @{typ int}
val ratT = @{typ rat}
val rat_zero = Rat.of_int 0

(* Test if a term represents a numerical constant. In addition to use
   dest_number from HOLogic, test for inverse, uminus, of_rat, etc.
 *)
fun is_numc t =
    case t of
        Const (@{const_name inverse}, _) $ t' => is_numc t'
      | Const (@{const_name uminus}, _) $ t' => is_numc t'
      | Const (@{const_name of_rat}, _) $ r => is_numc r
      | Const (@{const_name Fract}, _) $ n $ d => is_numc n andalso is_numc d
      | _ => let val _ = HOLogic.dest_number t in true end
             handle TERM ("dest_number", _) => false

(* Deconstruct numerical constant. Discard type. *)
fun dest_numc t = HOLogic.dest_number t |> snd
                  handle TERM ("dest_number", _) => raise Fail "dest_numc"

(* Rational numbers version of dest_numc. *)
fun dest_numc_rat t =
    case t of
        Const (@{const_name inverse}, _) $ t' =>
        let
          val r' = dest_numc_rat t'
        in
          if r' = rat_zero then rat_zero
          else Rat.inv r'
        end
      | Const (@{const_name uminus}, _) $ t' => Rat.neg (dest_numc_rat t')
      | Const (@{const_name of_rat}, _) $ r => dest_numc_rat r
      | Const (@{const_name Fract}, _) $ n $ d =>
        Rat.make (dest_numc n, dest_numc d)
      | _ => Rat.of_int (dest_numc t)

(* Whether the given term is a < b or a <= b. *)
fun is_order t =
    let
      val _ = assert (fastype_of t = boolT) "is_order: wrong type"
    in
      case t of Const (@{const_name less}, _) $ _ $ _ => true
              | Const (@{const_name less_eq}, _) $ _ $ _ => true
              | _ => false
    end

fun is_linorder ctxt t =
    let
      val T = fastype_of (dest_arg t)
      val thy = Proof_Context.theory_of ctxt
    in
      is_order t andalso Sign.of_sort thy (T, ["Orderings.linorder"])
    end

(* Check whether t is in the form a + b. *)
fun is_plus t =
    case t of
        Const (@{const_name plus}, _) $ _ $ _ => true
      | _ => false

(* Check whether t is in the form a - b. *)
fun is_minus t =
    case t of
        Const (@{const_name minus}, _) $ _ $ _ => true
      | _ => false

fun is_times t =
    case t of
        Const (@{const_name times}, _) $ _ $ _ => true
      | _ => false

fun is_divide t =
    case t of
        Const (@{const_name divide}, _) $ _ $ _ => true
      | _ => false

fun is_zero t =
    case t of
        Const (@{const_name zero_class.zero}, _) => true
      | _ => false

fun is_one t =
    case t of
        Const (@{const_name one_class.one}, _) => true
      | _ => false

(* Convert ~ x < y to y <= x, and ~ x <= y to y < x. *)
val neg_ineq_cv =
    (Conv.try_conv o Conv.first_conv)
        (map rewr_obj_eq [@{thm Orderings.linorder_not_less},
                          @{thm Orderings.linorder_not_le}])

(* Convert x < y to ~ y <= x, and x <= y to ~ y < x. *)
val neg_ineq_back_cv =
    (Conv.try_conv o Conv.first_conv)
        (map (rewr_obj_eq o obj_sym) [@{thm Orderings.linorder_not_less},
                                      @{thm Orderings.linorder_not_le}])

val prove_by_arith = UtilLogic.prove_by_tac Arith_Data.arith_tac
val contra_by_arith = UtilLogic.contra_by_tac Arith_Data.arith_tac

end  (* structure UtilArith *)

val natT = UtilArith.natT
val intT = UtilArith.intT
