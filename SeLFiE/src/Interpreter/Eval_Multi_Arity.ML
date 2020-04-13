(*  Title:      PSL/SeLFiE/src/Interpreter/Eval_Multi_Arity.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_MULTI_ARITY =
sig

datatype expr =
  Bound      of int
| Lambdas    of int * expr (*(0, exp) means one lambda abstraction, and (1, exp) means two lambda abstractions.*)
| Applies    of expr * expr list
| Literal    of Eval_Parameter.literal
| Assert     of SeLFiE_Util.assert * expr list
| Dive_In    of expr * expr * expr list(*outer target, inner lambda, outer arguments*)
| Deep_Dive  of expr * expr * expr list(*outer target, inner lambda, outer arguments*)
| All        of SeLFiE_Util.qtyp * expr
| Some       of SeLFiE_Util.qtyp * expr;

val eval: Proof.state -> SeLFiE_Util.induct_arguments -> expr -> expr;

end;

structure Eval_Multi_Arity: EVAL_MULTI_ARITY  =
struct

structure SU = SeLFiE_Util;
structure EB = Eval_Unary;(*TODO*)

datatype expr =
  Bound     of int
| Lambdas   of int * expr (*(0, exp) means one lambda abstraction, and (1, exp) means two lambda abstractions.*)
| Applies   of expr * expr list
| Literal   of Eval_Parameter.literal
| Assert    of SeLFiE_Util.assert * expr list
| Dive_In   of expr * expr * expr list(*outer target, inner lambda, outer arguments*)
| Deep_Dive of expr * expr * expr list(*outer target, inner lambda, outer arguments*)
| All       of SeLFiE_Util.qtyp * expr
| Some      of SeLFiE_Util.qtyp * expr;
(* unary_to_multi *)
fun unary_to_multi (Bound i)              = EB.Bound i
  | unary_to_multi (Lambdas (0, expr))    = EB.Lambda (unary_to_multi expr)
  | unary_to_multi (Lambdas (n, expr))    = if n > 0  then EB.Lambda (unary_to_multi (Lambdas (n - 1, expr)))
                                       else if n = ~1 then unary_to_multi expr (*corresponding to no-lambda abstraction.*)
                                       else error "quantifier_to_multi_arity failed. negative number of lambda abstractions."
  | unary_to_multi (Applies (f, xs))      =
    let
      fun mk_nested_pair  []                  (acc:EB.expr) = acc:EB.expr
        | mk_nested_pair (arg::args:expr list)(acc:EB.expr) = mk_nested_pair args (EB.Apply (acc, unary_to_multi arg)):EB.expr;
    in
      mk_nested_pair xs (unary_to_multi f)
    end
  | unary_to_multi (Dive_In   (t, l, args)) = EB.Dive_In   (unary_to_multi t, unary_to_multi l, unaries_to_multis args)
  | unary_to_multi (Deep_Dive (t, l, args)) = EB.Deep_Dive (unary_to_multi t, unary_to_multi l, unaries_to_multis args)
  | unary_to_multi (Literal l          )    = EB.Literal l
  | unary_to_multi (Assert (ass, exprs))    = EB.Assert (ass,unaries_to_multis exprs)
  | unary_to_multi (All    (qtyp, expr))    = EB.All    (qtyp, unary_to_multi expr)
  | unary_to_multi (Some   (qtyp, expr))    = EB.Some   (qtyp, unary_to_multi expr)
and unaries_to_multis exprs = map unary_to_multi exprs

fun convert_result (EB.Literal l) = Literal l
  | convert_result (EB.Bound   i) = Bound i
  | convert_result (EB.Lambda expr) = Lambdas (0, convert_result expr)
  | convert_result  _ = error "convert_result in Multi_Arity failed. Evaluation is not complete.";

fun print_expr (Bound i) = "Bound " ^ Int.toString i ^ " "
  | print_expr (Lambdas (vnames, expr)) = "Lambdas ( " ^ Int.toString vnames ^ " ,  " ^ print_expr expr ^ " ) "
  | print_expr (Applies (exp1, exp2)) = "Applies " ^ print_expr exp1 ^ " " ^ (fold (curry (op ^)) (map print_expr exp2) "")
  | print_expr (Literal _) = "Literal lit"
  | print_expr (Assert (ass, expres)) = "Assert ( " ^ SeLFiE_Util.print_assert ass ^ "," ^ (fold (curry (op ^)) (map print_expr expres) " ) ")
  | print_expr (Dive_In   _) = "Dive_In ...\n"
  | print_expr (Deep_Dive _) = "Deep_Dive ...\n"
  | print_expr (All  (_, expr)) = "All ( "  ^ "type" ^ ", " ^ print_expr expr ^ " )"
  | print_expr (Some (_, expr)) = "Some ( " ^ "type" ^ ", " ^ print_expr expr ^ " )";

fun eval (pst:Proof.state) (induct_args:SeLFiE_Util.induct_arguments) expr =
  let
(*
    val _ = tracing ("Print from From_Quantifier_To_Multi_Arity: \n" ^ print_expr expr);
*)
    val eq_result = EB.eval pst induct_args (unary_to_multi expr): EB.expr;
    val result    = convert_result eq_result                     : expr;
  in
    result
  end;

end;