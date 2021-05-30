(*  Title:      PSL/SeLFiE/src/Interpreter/Eval_Multi_Arity.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_MULTI_ARITY =
sig

datatype expr =
  Bound     of int
| Lambdas   of int * expr (*(0, exp) means one lambda abstraction, and (1, exp) means two lambda abstractions.*)
| Applies   of expr * expr list
| Literal   of Eval_Parameter.literal
| Assert    of SeLFiE_Util.assert * expr list
| Dive_In   of expr * expr * expr list * SeLFiE_Util.assert(*outer target, inner lambda, outer arguments, ands_or_ors*)
| Deep_Dive of expr * expr * expr list * SeLFiE_Util.assert(*outer target, inner lambda, outer arguments, ands_or_ors*)
| All       of SeLFiE_Util.qtyp * expr
| Some      of SeLFiE_Util.qtyp * expr;

val eval: Proof.state -> Outer_Path_To_Unode.path_to_unode_table -> Quantifier_Domain.domains -> SeLFiE_Util.induct_arguments -> expr -> expr;

end;

structure Eval_Multi_Arity: EVAL_MULTI_ARITY  =
struct

structure SU = SeLFiE_Util;
structure EU = Eval_Unary;

datatype expr =
  Bound     of int
| Lambdas   of int * expr (*(0, exp) means one lambda abstraction, and (1, exp) means two lambda abstractions.*)
| Applies   of expr * expr list
| Literal   of Eval_Parameter.literal
| Assert    of SeLFiE_Util.assert * expr list
| Dive_In   of expr * expr * expr list * SeLFiE_Util.assert(*outer target, inner lambda, outer arguments, ands_or_ors*)
| Deep_Dive of expr * expr * expr list * SeLFiE_Util.assert(*outer target, inner lambda, outer arguments, ands_or_ors*)
| All       of SeLFiE_Util.qtyp * expr
| Some      of SeLFiE_Util.qtyp * expr;
(* unary_to_multi *)
fun unary_to_multi (Bound i)              = EU.Bound i
  | unary_to_multi (Lambdas (0, expr))    = EU.Lambda (unary_to_multi expr)
  | unary_to_multi (Lambdas (n, expr))    = if n > 0  then EU.Lambda (unary_to_multi (Lambdas (n - 1, expr)))
                                       else if n = ~1 then unary_to_multi expr (*corresponding to no-lambda abstraction.*)
                                       else error "quantifier_to_multi_arity failed. negative number of lambda abstractions."
  | unary_to_multi (Applies (f, xs))      =
    let
      fun mk_nested_pair  []                  (acc:EU.expr) = acc:EU.expr
        | mk_nested_pair (arg::args:expr list)(acc:EU.expr) = mk_nested_pair args (EU.Apply (acc, unary_to_multi arg)):EU.expr;
    in
      mk_nested_pair xs (unary_to_multi f)
    end
  | unary_to_multi (Dive_In   (t, l, args, ands_ors)) = EU.Dive_In   (unary_to_multi t, unary_to_multi l, unaries_to_multis args, ands_ors)
  | unary_to_multi (Deep_Dive (t, l, args, ands_ors)) = EU.Deep_Dive (unary_to_multi t, unary_to_multi l, unaries_to_multis args, ands_ors)
  | unary_to_multi (Literal l          )    = EU.Literal l
  | unary_to_multi (Assert (ass, exprs))    = EU.Assert (ass,unaries_to_multis exprs)
  | unary_to_multi (All    (qtyp, expr))    = EU.All    (qtyp, unary_to_multi expr)
  | unary_to_multi (Some   (qtyp, expr))    = EU.Some   (qtyp, unary_to_multi expr)
and unaries_to_multis exprs = map unary_to_multi exprs

fun convert_result (EU.Literal l) = Literal l
  | convert_result (EU.Bound   i) = Bound i
  | convert_result (EU.Lambda expr) = Lambdas (0, convert_result expr)
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

fun eval (pst:Proof.state) (path_to_unode_table:Outer_Path_To_Unode.path_to_unode_table) (domains:Quantifier_Domain.domains) (induct_args:SeLFiE_Util.induct_arguments) expr =
  let
    val eq_result = EU.eval pst path_to_unode_table domains induct_args (unary_to_multi expr): EU.expr;
    val result    = convert_result eq_result                                                 : expr;
  in
    result
  end;

end;