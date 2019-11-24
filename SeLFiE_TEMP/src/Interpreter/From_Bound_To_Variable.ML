(*  Title:      PSL/SeLFeE/src/From_Bound_To_Variable.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
functor from_Bound_to_Variable (Eval_Bound:EVAL_BOUND): EVAL_VARIABLE  =
struct

structure EB = Eval_Bound;

type parameter = EB.parameter;

type parameter_assert = EB.parameter_assert;

datatype assert =
  Not
| And
| Or
| Nor
| Imply
| Ands
| Ors
| Eval_Parameter of parameter_assert;

fun convert_assert Not   = EB.Not
  | convert_assert And   = EB.And
  | convert_assert Or    = EB.Or
  | convert_assert Nor   = EB.Nor
  | convert_assert Imply = EB.Imply
  | convert_assert Ands  = EB.Ands
  | convert_assert Ors   = EB.Ors
  | convert_assert (Eval_Parameter assert) = EB.Eval_Parameter assert;

datatype expr =
  Variable   of string
| Lambda     of string * expr
| Apply      of expr   * expr
| Literal    of parameter
| Assert     of assert * expr list;

type environment = (string * int) list; (*map a variable name to a de-Bruijn index*)

fun lookup (env:environment) name = AList.lookup (op =) env name |> Utils.the' "lookup in Eval_Var failed.": int;
val update                        = AList.update (op =): (string * int) -> environment -> environment;
fun increment (alist:environment) = map (apsnd (curry (op +) 1)) alist: environment;
fun update_with_0 var_name env    = update (var_name, 0) env: environment;
fun increment_then_update_with_0 var_name env = env |> increment |> update_with_0 var_name: environment;

fun var_to_bound env (Variable   vname           ) = EB.Bound (lookup env vname)
  | var_to_bound env (Lambda    (name,  sub_expr)) = EB.Lambda (var_to_bound (increment_then_update_with_0 name env) sub_expr)
  | var_to_bound env (Apply     (expr1, expr2   )) = EB.Apply (apply2 (var_to_bound env) (expr1, expr2))
  | var_to_bound _   (Literal    param           ) = EB.Literal param
  | var_to_bound env (Assert    (assert, params) ) = EB.Assert (convert_assert assert, map (var_to_bound env) params);

fun convert_result (EB.Literal ee_bool) = Literal ee_bool
  | convert_result  _ =
    error "eval in Eval_Var_Struct failed. Evaluation is not complete.";

fun eval (trm:term) (pst:Proof.state) (expr:expr) =
  let
    val eb_result  = EB.eval trm pst (var_to_bound [] expr): Eval_Bound.expr;
(*TODO: for inner assertions we have to pass an environment from the outer assertion.*)
    val result     = convert_result eb_result          : expr;
  in
    result
  end;

end;