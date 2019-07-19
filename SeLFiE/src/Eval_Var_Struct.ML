(*  Title:      PSL/SeLFeE/src/Eval_Var_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Var =
struct

structure EB = Eval_Bound;

datatype expr =
  Var        of string
| Lambda     of string * expr
| Apply      of expr   * expr
| Connective of Eval_Connective.assert
| Assert     of Eval_Full_Path.assert;

type full_path_to_fpunode_table = Full_Path_To_Fpunode.full_path_to_fpunode_table;

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
  | var_to_bound _   (Assert     assert          ) = EB.Assert assert;

fun bound_to_var (EB.Connective c) = Connective c
  | bound_to_var  _                = error "bound_to_var in from_Eval_Var_to_Eval_Bound failed.";

fun eval (table:full_path_to_fpunode_table) (expr:expr) =
  let
    val eb_result  = EB.eval table (var_to_bound [] expr): Eval_Bound.expr;
    val connective = EB.de_Connective eb_result          : Eval_Connective.assert;
    val result     = Connective connective               : expr;
  in
    result
  end;

end;