(*  Title:      PSL/SeLFeE/src/From_Quantifier_To_Multi_Arity.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
functor from_Quantifier_to_Multi_Arity (Eval_Quantifier:EVAL_QUANTIFIER): EVAL_MULTI_ARITY  =
struct

structure EQ = Eval_Quantifier;
structure SU = SeLFiE_Util;

type path    = EQ.path;
type command = Pattern.command;

datatype parameter = Path of path | Non_Path of SeLFiE_Util.non_path_parameter;

fun here_to_there (Path     p ) = EQ.Path p
  | here_to_there (Non_Path np) = EQ.Non_Path np;

fun there_to_here (EQ.Path     p ) = Path p
  | there_to_here (EQ.Non_Path np) = Non_Path np;

datatype expr =
  Bound   of int
| Lambdas of int  * expr (*(0, exp) means one lambda abstraction, and (1, exp) means two lambda abstractions.*)
| Applies of expr * expr list
| Literal of parameter
| Assert  of SeLFiE_Util.assert * expr list
| All     of SeLFiE_Util.qtyp * expr
| Some    of SeLFiE_Util.qtyp * expr;

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
  | quantifier_to_multi_arity (Literal param)        = EQ.Literal (here_to_there param)
  | quantifier_to_multi_arity (Assert (ass, exprs))  = EQ.Assert (ass, map quantifier_to_multi_arity exprs)
  | quantifier_to_multi_arity (All    (qtyp, expr))  = EQ.All  (qtyp, quantifier_to_multi_arity expr)
  | quantifier_to_multi_arity (Some   (qtyp, expr))  = EQ.Some (qtyp, quantifier_to_multi_arity expr)

fun convert_result (EQ.Literal ee_bool) = Literal (there_to_here ee_bool)
  | convert_result (EQ.Bound i) = Bound i
  | convert_result (EQ.Lambda expr) = Lambdas (0, convert_result expr)
  | convert_result  _ =
    error "convert_result in from_Quantifier_to_Multi_Arity failed. Evaluation is not complete.";

fun print_expr (Bound i) = "Bound " ^ Int.toString i ^ " \n"
  | print_expr (Lambdas (i, expr)) = "Lambdas " ^  Int.toString i ^ " desu " ^ print_expr expr
  | print_expr (Applies (exp1, exp2)) = "Applies " ^ print_expr exp1 ^ "\n" ^ (fold (curry (op ^)) (map print_expr exp2) "")
  | print_expr (Literal _) = "Literal \n"
  | print_expr (Assert (_, expres)) = "Assert \n" ^ (fold (curry (op ^)) (map print_expr expres) "")
  | print_expr (All  _) = "Alls \n"
  | print_expr (Some _) = "Some \n";

fun eval (trm:term) (pst:Proof.state) (induct_args:SeLFiE_Util.induct_arguments) expr =
  let
    val eq_result  = EQ.eval trm pst induct_args (quantifier_to_multi_arity expr): EQ.expr;
    val result     = convert_result eq_result: expr;
  in
    result
  end;

end;