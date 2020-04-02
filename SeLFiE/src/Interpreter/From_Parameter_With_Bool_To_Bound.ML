(*  Title:      PSL/SeLFeE/src/Interpreter/From_Parameter_With_Bool_To_Bound.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

    This file contains signatures, structures, and functors to support lambda abstraction in SeLFiE.
    The three functions (shift, subst, and eval) in this file are inspired by the functions of the 
    same names found in "ML for the Working Programmer" written by Larry C. Paulson.
*)
functor from_Parameter_With_Bool_to_Bound (Eval_Parameter_With_Bool:EVAL_PARAMETER_WITH_BOOL): EVAL_BOUND =
struct

structure EPWB = Eval_Parameter_With_Bool;
structure SU   = SeLFiE_Util;
structure EP   = Eval_Parameter;

type command = Pattern.command;

datatype expr =
  Bound      of int
| Lambda     of expr
| Apply      of expr * expr
| Literal    of Eval_Parameter.literal
| Assert     of SU.assert * expr list;

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

fun print_expr (Bound i)            = "B.Bound " ^ Int.toString i
  | print_expr (Lambda expr)        = "B.Lambda (" ^ print_expr expr ^ " )"
  | print_expr (Apply (exp1, exp2)) = "B.Apply (" ^ print_expr exp1 ^ ", " ^ print_expr exp2 ^ ")"
  | print_expr (Literal p) = " B.Literal " ^ (case p of
       EP.Outer_Path _ => "Outer_Path"
     | EP.Inner_Path _ => "Inner_Path"
     | EP.Non_Path non_path  => case non_path of
         EP.Bool    b => if b then "True" else "False"
       | EP.Print   _ => "print!"
       | EP.Number  _ => "number!"
       | EP.Command _ => "command!")
  | print_expr (Assert (_, expres)) = "B.Assert " ^ (fold (curry (op ^)) (map print_expr expres) "")

fun param_with_bool_to_bound (Literal param) = param
  | param_with_bool_to_bound  expr           =
    let
      val mssg = print_expr expr;
    in
      error ("eval_prim in Eval_Bound failed with " ^ mssg)
    end;

fun eval (trm:term) (pst:Proof.state) (induct_args:SU.induct_arguments) (expr:expr) =
  let
    fun eval' (Apply (trm1, trm2)) =
         (case eval' trm1 of
          Lambda  u => (tracing "LAMBDA";eval' (subst 0 (eval' trm2) u))
        | Literal l => (tracing "LITERAL";Literal l)
        | Bound   i => (tracing "BOUND";Bound i)
        | u1        => (tracing ("       Apply in Apply" ^
                       (case u1 of _  =>  " with something"));
                       Apply (u1, eval' trm2)))
      | eval' (Assert (assert, param_exprs)) =
          let
            (* Note that param_exprs are always Literal at this point
             * because the evaluation function in From_Bound_To_Quantifier evaluated
             * param_exprs eagerly.*)
(*
            val _ = tracing (print_expr (Assert (assert, param_exprs)));
            val _ = map (tracing o print_expr) param_exprs;             
*)
            val params = map (param_with_bool_to_bound o eval') param_exprs
          in
            EPWB.eval trm pst induct_args assert params |> Literal
          end
      | eval' t = t
  in
    eval' expr
  end;

end;