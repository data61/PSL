(*  Title:      PSL/SeLFeE/src/Eval_Bound_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

    This file contains signatures, structures, and functors to support lambda abstraction in SeLFiE.
    The three functions (shift, subst, and eval) in this file are inspired by the functions of the 
    same names found in "ML for the Working Programmer" written by Larry C. Paulson.
*)
structure Eval_Bound: EVAL_BOUND  =
struct

datatype expr =
  Bound      of int
| Lambda     of expr
| Apply      of expr * expr
| Connective of Eval_Connective.assert
| Literal    of Eval_Parameters.parameter
| Assert     of Eval_Parameters.assert * expr list;

fun de_Connective (Connective assert) = assert
  | de_Connective  _                  = error "de_Connective in Eval_Bound failed.";

fun shift 0 _ u               = u
  | shift i d (Bound j)       = if j >= d then Bound (j+i) else Bound j
  | shift i d (Lambda t)      = Lambda (shift i (d+1) t)
  | shift i d (Apply (t, u))  = Apply (shift i d t, shift i d u)
  | shift _ _ (Connective c)  = Connective c
  | shift _ _ (Literal param) = Literal param
  | shift _ _ (Assert pair)   = Assert pair;

fun subst i u (Bound j) =
  if      j < i then Bound j (*locally bound*)
  else if j = i then shift i 0 u
  else               Bound (j-1)
  | subst i u (Lambda t)       = Lambda (subst (i+1) u t)
  | subst i u (Apply (t1, t2)) = Apply (subst i u t1, subst i u t2)
  | subst _ _ (Connective c)   = Connective c
  | subst _ _ (Literal param)  = Literal param
  | subst _ _ (Assert pair)    = Assert pair;

type full_path_to_fpunode_table = Full_Path_To_Fpunode.full_path_to_fpunode_table;

fun eval_prim (Literal param) = param
  | eval_prim  _              = error "eval_prim in Eval_Bound_Struct failed!"

fun eval (table:full_path_to_fpunode_table) (Apply (t1, t2)) = (case eval table t1 of
      Lambda u => eval table (subst 0 (eval table t2) u)
    | u1       => Apply (u1, eval table t2))
  | eval table (Assert (assert, param_exprs)) =
    let
      val params = map eval_prim param_exprs: Eval_Parameters.parameters;
    in
      Eval_Parameters.eval table assert params |> Connective
    end
  | eval _ t = t;


end;