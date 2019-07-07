(*  Title:      PSL/SeLFeE/src/Eval_Var.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_VAR =
sig

type connective;
type atom;
type primitive_op;

datatype expr =
  Var        of string
| Lambda     of string * expr
| Apply      of expr   * expr
| Connective of connective
| Primitive  of primitive_op * atom list;

val eval: expr -> expr;

end;

functor from_Eval_Var_to_Eval_Bound (EB: EVAL_BOUND): EVAL_VAR =
struct

type connective   = EB.connective;
type atom         = EB.atom;
type primitive_op = EB.primitive_op;

datatype expr =
  Var        of string
| Lambda     of string * expr
| Apply      of expr   * expr
| Connective of connective
| Primitive  of primitive_op * atom list;

type eb_expr = EB.expr;

type environment = (string * int) list; (*map a variable name to a de-Bruijn index*)

fun lookup (env:environment) name = AList.lookup (op =) env name |> Utils.the' "lookup in Eval_Var failed.": int;
val update                        = AList.update (op =): (string * int) -> environment -> environment;
fun increment (alist:environment) = map (apsnd (curry (op +) 1)) alist: environment;
fun update_with_0 var_name env    = update (var_name, 0) env: environment;
fun increment_then_update_with_0 var_name env = env |> increment |> update_with_0 var_name: environment;

fun var_to_bound env (Var        vname           ) = EB.Bound (lookup env vname)
  | var_to_bound env (Lambda    (name,  sub_expr)) = EB.Lambda (var_to_bound (increment_then_update_with_0 name env) sub_expr)
  | var_to_bound env (Apply     (expr1, expr2   )) = EB.Apply (apply2 (var_to_bound env) (expr1, expr2))
  | var_to_bound _   (Connective c               ) = EB.Connective c
  | var_to_bound _   (Primitive  p               ) = EB.Primitive  p;

fun bound_to_var (EB.Connective c) = Connective c
  | bound_to_var  _                = error "bound_to_var in from_Eval_Var_to_Eval_Bound failed.";

fun eval (expr:expr) = EB.eval (var_to_bound [] expr) |> bound_to_var;

end;