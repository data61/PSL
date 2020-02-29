(*  Title:      PSL/SeLFeE/src/From_Bound_To_Variable.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
functor from_Bound_to_Variable (Eval_Bound:EVAL_BOUND): EVAL_VARIABLE  =
struct

structure EB = Eval_Bound;
structure SU = SeLFiE_Util;

type path    = EB.path;
type command = Pattern.command;

datatype parameter = Path of path | Non_Path of SeLFiE_Util.non_path_parameter;

fun here_to_there (Path     p ) = EB.Path p
  | here_to_there (Non_Path np) = EB.Non_Path np;

fun there_to_here (EB.Path     p ) = Path p
  | there_to_here (EB.Non_Path np) = Non_Path np;

datatype expr =
  Variable   of string
| Lambda     of string * expr
| Apply      of expr   * expr
| Literal    of parameter
| Assert     of SU.assert * expr list;

type environment = (string * int) list; (*map a variable name to a de-Bruijn index*)

fun lookup (env:environment) name = AList.lookup (op =) env name 
|> (fn x => (tracing name; x))
|> (fn x => (tracing ("The length of env is " ^ Int.toString (length env)); x))
|> Utils.the' "lookup in Eval_Var failed.": int;
val update                        = AList.update (op =): (string * int) -> environment -> environment;
fun increment (alist:environment) = map (apsnd (curry (op +) 1)) alist: environment;
fun update_with_0 var_name env    = update (var_name, 0) env: environment;
fun update_with_0 var_name env    = (tracing "update_with_0";(var_name, 0)::env);
fun increment_then_update_with_0 var_name env = 
(tracing "increment_then_update_with_0";
env |> increment |> update_with_0 var_name: environment
);

fun var_to_bound env (Variable   vname           ) = 
(tracing "var_to_bound in From_Bound_To_Variable for Variable";
EB.Bound (lookup env vname)
)
  | var_to_bound env (Lambda    (name,  sub_expr)) = 
(tracing "var_to_bound in From_Bound_To_Variable for Lambda";
EB.Lambda (var_to_bound (increment_then_update_with_0 name env) sub_expr)
)
  | var_to_bound env (Apply     (expr1, expr2   )) = 
(tracing "var_to_bound in From_Bound_To_Variable for Apply";
EB.Apply (apply2 (var_to_bound env) (expr1, expr2))
)
  | var_to_bound _   (Literal    param           ) = 
(tracing "var_to_bound in From_Bound_To_Variable for Literal";
EB.Literal (here_to_there param)
)
  | var_to_bound env (Assert    (assert, params) ) = 
(tracing "var_to_bound in From_Bound_To_Variable for Assert";
EB.Assert (assert, map (var_to_bound env) params)
);

fun bound_to_var (EB.Literal bound_bool) = Literal (there_to_here bound_bool)
  | bound_to_var (EB.Bound _) = error "---EB.Bound"
  | bound_to_var (EB.Lambda _) = error "---EBB.Lambda"
  | bound_to_var (EB.Apply _) = error "---EB.Apply"
  | bound_to_var  _ =
    error "convert_result in from_Bound_to_Variable failed. Evaluation is not complete.";

fun eval (trm:term) (pst:Proof.state) (expr:expr) =
  let
    val eb_result  = EB.eval trm pst (var_to_bound [] expr): Eval_Bound.expr;
val _ = tracing "eb_result is "
    val result     = bound_to_var eb_result          : expr;
  in
    result
  end;

end;