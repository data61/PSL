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

val eval: term -> Proof.state -> SeLFiE_Util.induct_arguments -> expr -> expr;

end;

structure Eval_Multi_Arity: EVAL_MULTI_ARITY  =
struct

structure EQ = Eval_Quantifier;
structure SU = SeLFiE_Util;

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

fun quantifier_to_multi_arity (Bound i)              = EQ.Bound i
  | quantifier_to_multi_arity (Lambdas (0, expr))    = EQ.Lambda (quantifier_to_multi_arity expr)
  | quantifier_to_multi_arity (Lambdas (n, expr))    = if n > 0 then EQ.Lambda (quantifier_to_multi_arity (Lambdas (n - 1, expr)))
                                                       else error "quantifier_to_multi_arity failed. negative number of lambda abstractions."
  | quantifier_to_multi_arity (Applies (f, xs))      =
    let
      fun mk_nested_pair  []                  (acc:EQ.expr) = acc:EQ.expr
        | mk_nested_pair (arg::args:expr list)(acc:EQ.expr) = mk_nested_pair args (EQ.Apply (acc, quantifier_to_multi_arity arg)):EQ.expr
    in
      mk_nested_pair xs (quantifier_to_multi_arity f)
    end
  | quantifier_to_multi_arity (Dive_In   (t, l, args)) = EQ.Dive_In   (quantifier_to_multi_arity t, quantifier_to_multi_arity l, quantifiers_to_multi_arities args)
  | quantifier_to_multi_arity (Deep_Dive (t, l, args)) = EQ.Deep_Dive (quantifier_to_multi_arity t, quantifier_to_multi_arity l, quantifiers_to_multi_arities args)
  | quantifier_to_multi_arity (Literal l          )  = EQ.Literal l
  | quantifier_to_multi_arity (Assert (ass, exprs))  = EQ.Assert (ass, map quantifier_to_multi_arity exprs)
  | quantifier_to_multi_arity (All    (qtyp, expr))  = EQ.All    (qtyp, quantifier_to_multi_arity expr)
  | quantifier_to_multi_arity (Some   (qtyp, expr))  = EQ.Some   (qtyp, quantifier_to_multi_arity expr)
and quantifiers_to_multi_arities exprs = map quantifier_to_multi_arity exprs

fun convert_result (EQ.Literal l) = Literal l
  | convert_result (EQ.Bound   i) = Bound i
  | convert_result (EQ.Lambda expr) = Lambdas (0, convert_result expr)
  | convert_result  _ = error "convert_result in Multi_Arity failed. Evaluation is not complete.";

fun print_expr (Bound i) = "Bound " ^ Int.toString i ^ " \n"
  | print_expr (Lambdas (i, expr)) = "Lambdas " ^  Int.toString i ^ " desu " ^ print_expr expr
  | print_expr (Applies (exp1, exp2)) = "Applies " ^ print_expr exp1 ^ "\n" ^ (fold (curry (op ^)) (map print_expr exp2) "")
  | print_expr (Literal _) = "Literal \n"
  | print_expr (Assert (_, expres)) = "Assert \n" ^ (fold (curry (op ^)) (map print_expr expres) "")
  | print_expr (Dive_In   _) = "Dive_In ...\n"
  | print_expr (Deep_Dive _) = "Deep_Dive ...\n"
  | print_expr (All       _) = "Alls \n"
  | print_expr (Some      _) = "Some \n";

fun eval (trm:term) (pst:Proof.state) (induct_args:SeLFiE_Util.induct_arguments) expr =
  let
    val _ = tracing ("Print from From_Quantifier_To_Multi_Arity: " ^ print_expr expr);
    val eq_result = EQ.eval trm pst induct_args (quantifier_to_multi_arity expr): EQ.expr;
    val result    = convert_result eq_result                                    : expr;
  in
    result
  end;

end;