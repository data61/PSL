(*  Title:      PSL/SeLFeE/src/Interpreter/From_Parameter_With_Bool_To_Bound.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

    This file contains signatures, structures, and functors to support lambda abstraction in SeLFiE.
    The three functions (shift, subst, and eval) in this file are inspired by the functions of the 
    same names found in "ML for the Working Programmer" written by Larry C. Paulson.
*)
functor from_Parameter_With_Bool_to_Bound (Eval_Parameter_With_Bool:EVAL_PARAMETER_WITH_BOOL): EVAL_BOUND =
struct

structure EPWB = Eval_Parameter_With_Bool;

type parameter        = EPWB.parameter;
type parameter_assert = EPWB.parameter_assert;

datatype assert =
  Not
| And
| Or
| Nor
| Imply
| Ands
| Ors
| Eval_Parameter of parameter_assert;

fun convert_assert Not   = EPWB.Not
  | convert_assert And   = EPWB.And
  | convert_assert Or    = EPWB.Or
  | convert_assert Nor   = EPWB.Nor
  | convert_assert Imply = EPWB.Imply
  | convert_assert Ands  = EPWB.Ands
  | convert_assert Ors   = EPWB.Ors
  | convert_assert (Eval_Parameter assert) = EPWB.Eval_Parameter assert;

datatype expr =
  Bound      of int
| Lambda     of expr
| Apply      of expr * expr
| Literal    of parameter
| Assert     of assert * expr list;

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

fun eval_prim (Literal param) = param
  | eval_prim  _              = error "eval_prim in Eval_Bound_Struct failed!"

fun eval (trm:term) (pst:Proof.state) (expr:expr) =
let
  fun eval' (Apply (trm1, trm2)) = (case eval' trm1 of
        Lambda u => eval' (subst 0 (eval' trm2) u)
      | u1       => Apply (u1, eval' trm2))
    | eval' (Assert (assert, param_exprs)) =
      let
        val params = map eval_prim param_exprs: EPWB.parameters;
      in
        EPWB.eval trm pst (convert_assert assert) params |> Literal
      end
    | eval' t = t
in
  eval' expr
end;

end;