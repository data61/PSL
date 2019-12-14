(*  Title:      PSL/SeLFeE/src/From_Bound_To_Variable.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
functor from_Bound_to_Variable (Eval_Bound:EVAL_BOUND): EVAL_VARIABLE  =
struct

structure EB = Eval_Bound;

type path    = EB.path;
type print   = SeLFiE_Util.print;
type number  = Eval_Number.number;
type command = Pattern.command;(*TODO: double-check*)

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

datatype atomic_assert =
(*Eval_Node*)
  Is_Cnst
| Is_Free
| Is_Var
| Is_Bound
| Is_Lambda
| Is_App
(*Eval_Unode*)
| Has_Same_Prnt_As
| Is_In_Trm_Prnt
| Is_Deeper_Than
| Is_Shallower_Than
| Is_Path_Above
| Is_Same_Path_As
(*Eval_Print*)
| Are_Same_Prints
| Is_Printed_As
(*Eval_Path*)
| Unode_Has_Print
(*Eval_Number*)
| Are_Same_Number
| Is_Less_Than
| Is_Int;

fun convert_parameter_assert Is_Cnst          = EB.Is_Cnst
  | convert_parameter_assert Is_Free          = EB.Is_Free
  | convert_parameter_assert Is_Var           = EB.Is_Var
  | convert_parameter_assert Is_Bound         = EB.Is_Bound
  | convert_parameter_assert Is_Lambda        = EB.Is_Lambda
  | convert_parameter_assert Is_App           = EB.Is_App
  | convert_parameter_assert Has_Same_Prnt_As = EB.Has_Same_Prnt_As
  | convert_parameter_assert Is_In_Trm_Prnt   = EB.Is_In_Trm_Prnt
  | convert_parameter_assert Is_Deeper_Than   = EB.Is_Deeper_Than
  | convert_parameter_assert Is_Shallower_Than= EB.Is_Shallower_Than
  | convert_parameter_assert Is_Path_Above    = EB.Is_Path_Above
  | convert_parameter_assert Is_Same_Path_As  = EB.Is_Same_Path_As
  | convert_parameter_assert Are_Same_Prints  = EB.Are_Same_Prints
  | convert_parameter_assert Is_Printed_As    = EB.Is_Printed_As
  | convert_parameter_assert Unode_Has_Print  = EB.Unode_Has_Print
  | convert_parameter_assert Are_Same_Number  = EB.Are_Same_Number
  | convert_parameter_assert Is_Less_Than     = EB.Is_Less_Than
  | convert_parameter_assert Is_Int           = EB.Is_Int;

datatype assert =
  Not
| And
| Or
| Nor
| Imply
| Ands
| Ors
| Atomic of atomic_assert;

fun convert_assert Not   = EB.Not
  | convert_assert And   = EB.And
  | convert_assert Or    = EB.Or
  | convert_assert Nor   = EB.Nor
  | convert_assert Imply = EB.Imply
  | convert_assert Ands  = EB.Ands
  | convert_assert Ors   = EB.Ors
  | convert_assert (Atomic assert) = EB.Atomic (convert_parameter_assert assert);

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
  | var_to_bound _   (Literal    param           ) = EB.Literal (here_to_there param)
  | var_to_bound env (Assert    (assert, params) ) = EB.Assert (convert_assert assert, map (var_to_bound env) params);

fun convert_result (EB.Literal ee_bool) = Literal (there_to_here ee_bool)
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