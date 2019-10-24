(*  Title:      PSL/SeLFeE/src/Eval_Bound_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

    This file contains signatures, structures, and functors to support lambda abstraction in SeLFiE.
    The three functions (shift, subst, and eval) in this file are inspired by the functions of the 
    same names found in "ML for the Working Programmer" written by Larry C. Paulson.
*)
structure Eval_Bound: EVAL_BOUND  =
struct

structure EE = Eval_Expression;

datatype expr =
  Bound      of int
| Lambda     of expr
| Apply      of expr * expr
| Literal    of EE.parameter
| Assert     of EE.assert * expr list;

fun shift 0 _ u                     = u
  | shift i d (Bound j)             = if j >= d then Bound (j+i) else Bound j
  | shift i d (Lambda t)            = Lambda (shift i (d+1) t)
  | shift i d (Apply (t, u))        = Apply (shift i d t, shift i d u)
  | shift _ _ (Literal param)       = Literal param
  | shift i d (Assert (ass, exprs)) = Assert (ass, map (shift i d) exprs);

fun subst i u (Bound j) =
      if      j < i then Bound j (*locally bound*)
      else if j = i then shift i 0 u
      else               Bound (j-1)
  | subst i u (Lambda t)            = Lambda (subst (i+1) u t)
  | subst i u (Apply (t1, t2))      = Apply (subst i u t1, subst i u t2)
  | subst _ _ (Literal param)       = Literal param
  | subst i u (Assert (ass, exprs)) = Assert (ass, map (subst i u) exprs);

type full_path_to_fpunode_table = Full_Path_To_Fpunode.full_path_to_fpunode_table;

fun eval_prim (Literal param) = param
  | eval_prim  _              = error "eval_prim in Eval_Bound_Struct failed!"

fun eval (table:full_path_to_fpunode_table) (expr:expr) =
let
  fun eval' (Apply (trm1, trm2)) = (case eval' trm1 of
        Lambda u => eval' (subst 0 (eval' trm2) u)
      | u1       => Apply (u1, eval' trm2))
    | eval' (Assert (assert, param_exprs)) =
      let
        val params = map eval_prim param_exprs: EE.parameters;
      in
        EE.eval table assert params |> Literal
      end
    | eval' t = t
in
  eval' expr
end;

end;