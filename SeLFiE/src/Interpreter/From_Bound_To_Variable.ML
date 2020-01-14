(*  Title:      PSL/SeLFeE/src/From_Bound_To_Variable.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
functor from_Bound_to_Variable (Eval_Bound:EVAL_BOUND): EVAL_VARIABLE  =
struct

structure EB = Eval_Bound;
structure SU = SeLFiE_Util;

type path    = EB.path;
type print   = SeLFiE_Util.print;
type number  = Eval_Number.number;
type command = Pattern.command;

datatype parameter =
  Bool    of bool
| Path    of path
| Print   of print
| String  of string
| Number  of number
| Int     of int
| Command of command;

fun here_to_there (Bool b)    = EB.Bool b
  | here_to_there (Path p)    = EB.Path p
  | here_to_there (Print p)   = EB.Print p
  | here_to_there (String s)  = EB.String s
  | here_to_there (Number n)  = EB.Number n
  | here_to_there (Int i)     = EB.Int i
  | here_to_there (Command i) = EB.Command i;

fun there_to_here (EB.Bool b)    = Bool b
  | there_to_here (EB.Path p)    = Path p
  | there_to_here (EB.Print p)   = Print p
  | there_to_here (EB.String s)  = String s
  | there_to_here (EB.Number n)  = Number n
  | there_to_here (EB.Int i)     = Int i
  | there_to_here (EB.Command i) = Command i;

datatype expr =
  Variable   of string
| Lambda     of string * expr
| Apply      of expr   * expr
| Literal    of parameter
| Assert     of SU.assert * expr list;

type environment = (string * int) list; (*map a variable name to a de-Bruijn index*)

fun lookup (env:environment) name = AList.lookup (op =) env name |> Utils.the' "lookup in Eval_Var failed.": int;
val update                        = AList.update (op =): (string * int) -> environment -> environment;
fun increment (alist:environment) = map (apsnd (curry (op +) 1)) alist: environment;
fun update_with_0 var_name env    = update (var_name, 0) env: environment;
fun increment_then_update_with_0 var_name env = env |> increment |> update_with_0 var_name: environment;

fun var_to_bound env (Variable   vname           ) = EB.Bound (lookup env vname)
  | var_to_bound env (Lambda    (name,  sub_expr)) = EB.Lambda (var_to_bound (increment_then_update_with_0 name env) sub_expr)
  | var_to_bound env (Apply     (expr1, expr2   )) = EB.Apply (apply2 (var_to_bound env) (expr1, expr2))
  | var_to_bound _   (Literal    param           ) = EB.Literal (here_to_there param)
  | var_to_bound env (Assert    (assert, params) ) = EB.Assert (assert, map (var_to_bound env) params);

fun convert_result (EB.Literal ee_bool) = Literal (there_to_here ee_bool)
  | convert_result  _ =
    error "eval in Eval_Var_Struct failed. Evaluation is not complete.";

fun eval (trm:term) (pst:Proof.state) (expr:expr) =
  let
    val eb_result  = EB.eval trm pst (var_to_bound [] expr): Eval_Bound.expr;
    val result     = convert_result eb_result          : expr;
  in
    result
  end;

end;