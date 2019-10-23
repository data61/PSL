(*  Title:      PSL/SeLFeE/src/Eval_Var_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Var: EVAL_VAR =
struct

structure EB = Eval_Bound;
structure EP = Eval_Parameters;

datatype expr =
  Var        of string
| Lambda     of string * expr
| Apply      of expr   * expr
| Literal    of Eval_Parameters.parameter
| Assert     of Eval_Parameters.assert * expr list;

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
  | var_to_bound _   (Literal    param           ) = EB.Literal param
  | var_to_bound env (Assert    (assert, params) ) = EB.Assert (assert, map (var_to_bound env) params);

fun convert_result (EB.Literal (EP.Connective connect)) = Literal (EP.Connective connect)
  | convert_result  _ =
    error "eval in Eval_Var_Struct failed. Evaluation is not complete.";

fun eval (table:full_path_to_fpunode_table) (expr:expr) =
  let
    val eb_result  = EB.eval table (var_to_bound [] expr): Eval_Bound.expr;
    val result     = convert_result eb_result            : expr;
  in
    result
  end;

end;