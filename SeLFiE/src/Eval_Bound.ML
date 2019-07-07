(*  Title:      PSL/SeLFeE/src/Eval_Bound.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

    This file contains signatures, structures, and functors to support lambda abstraction in SeLFiE.
    The three functions (shift, subst, and eval) in this file are inspired by the functions of the 
    same names found in "ML for the Working Programmer" written by Larry C. Paulson.
*)

signature BOUND =
sig

type connective;
type atom;
type primitive_op;

datatype expr =
  Bound      of int
| Lambda     of expr
| Apply      of expr   * expr
| Connective of connective
| Primitive  of primitive_op * atom list;

val eval_prim: primitive_op -> atom list -> connective;

end;

signature EVAL_BOUND =
sig

type connective;
type atom;
type primitive_op;

datatype expr =
  Bound      of int
| Lambda     of expr
| Apply      of expr   * expr
| Connective of connective
| Primitive  of primitive_op * atom list;

val eval: expr -> expr;

end;

functor add_Eval_to_Bound (Bound:BOUND): EVAL_BOUND =
struct

open Bound;

fun shift 0 _ u                = u
  | shift i d (Bound j)        = if j >= d then Bound (j+i) else Bound j
  | shift i d (Lambda t)       = Lambda (shift i (d+1) t)
  | shift i d (Apply (t, u))   = Apply (shift i d t, shift i d u)
  | shift _ _ (Connective c)   = Connective c
  | shift _ _ (Primitive pair) = Primitive pair;

fun subst i u (Bound j) =
  if      j < i then Bound j (*locally bound*)
  else if j = i then shift i 0 u
  else               Bound (j-1)
  | subst i u (Lambda t)       = Lambda (subst (i+1) u t)
  | subst i u (Apply (t1, t2)) = Apply (subst i u t1, subst i u t2)
  | subst _ _ (Connective c)   = Connective c
  | subst _ _ (Primitive pair) = Primitive pair;

(*TODO: I think there is no point giving a name to lambda-abstracted variable at this stage due to the*)
(*use of de-Bruijn index.*)
fun eval (Bound.Apply (t1, t2)) = (case eval t1 of
      Lambda u => eval (subst 0 (eval t2) u)
    | u1       => Bound.Apply (u1, eval t2))
  | eval (Primitive (prim_op, args)) = eval_prim prim_op args |> Connective
  | eval t = t;

end;