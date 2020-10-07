(*
  File: consts.ML
  Author: Bohua Zhan

  Dealing with constants.
*)

signature CONSTS =
sig
  val add_const_data: string * (term -> bool) -> theory -> theory
  val detect_const: theory -> term -> string option
  val detect_const_ctxt: Proof.context -> term -> string option
  val is_const: theory -> term -> bool
  val is_const_ctxt: Proof.context -> term -> bool
  val neq_const: theory -> term * term -> bool
  val neq_const_ctxt: Proof.context -> term * term -> bool
end;

structure Consts : CONSTS =
struct

(* Table of detectors for constants, each registered under a
   descriptive name.
 *)
structure Data = Theory_Data (
  type T = (term -> bool) Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge pointer_eq
)

fun add_const_data (str, f) =
    Data.map (Symtab.update_new (str, f))

fun detect_const thy t =
    let
      val data = Symtab.dest (Data.get thy)
    in
      get_first (fn (str, f) => if f t then SOME str else NONE) data
    end

fun detect_const_ctxt ctxt t =
    detect_const (Proof_Context.theory_of ctxt) t

fun is_const thy t =
    is_some (detect_const thy t)

fun is_const_ctxt ctxt t =
    is_const (Proof_Context.theory_of ctxt) t

(* Whether two constants are of the same type and not equal. If either
   input is not a constant, return false.
 *)
fun neq_const thy (t1, t2) =
    let
      val ty1 = the (detect_const thy t1)
      val ty2 = the (detect_const thy t2)
    in
      ty1 = ty2 andalso not (t1 aconv t2)
    end
    handle Option.Option => false

fun neq_const_ctxt ctxt (t1, t2) =
    neq_const (Proof_Context.theory_of ctxt) (t1, t2)

end  (* structure Consts. *)
