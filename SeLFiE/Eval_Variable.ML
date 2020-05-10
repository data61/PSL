(*  Title:      PSL/SeLFeE/src/Interpreter/Eval_Variable.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
(*** signature: EVAL_VARIABLE ***)
signature EVAL_VARIABLE =
sig

datatype expr =
  Variable   of string
| Lambdas    of strings * expr (*(0, exp) means one lambda abstraction, and (1, exp) means two lambda abstractions.*)
| Applies    of expr * expr list
| Literal    of Eval_Parameter.literal
| Assert     of SeLFiE_Util.assert * expr list
| Dive_In    of expr * expr * expr list(*outer target, inner lambda, outer arguments*)
| Deep_Dive  of expr * expr * expr list(*outer target, inner lambda, outer arguments*)
| All        of string * SeLFiE_Util.qtyp * expr
| Some       of string * SeLFiE_Util.qtyp * expr;

val eval: Proof.state -> SeLFiE_Util.induct_arguments -> expr -> expr;

end;

(*** structure: Eval_Variable ***)
structure Eval_Variable: EVAL_VARIABLE =
struct

structure EM = Eval_Multi_Arity;

datatype expr =
  Variable   of string
| Lambdas    of strings * expr (*(0, exp) means one lambda abstraction, and (1, exp) means two lambda abstractions.*)
| Applies    of expr * expr list
| Literal    of Eval_Parameter.literal
| Assert     of SeLFiE_Util.assert * expr list
| Dive_In    of expr * expr * expr list(*outer target, inner lambda, outer arguments*)
| Deep_Dive  of expr * expr * expr list(*outer target, inner lambda, outer arguments*)
| All        of string * SeLFiE_Util.qtyp * expr
| Some       of string * SeLFiE_Util.qtyp * expr;

fun print_expr (Variable vname) = "Variable " ^ vname ^ " "
  | print_expr (Lambdas (vnames, expr)) = "Lambdas ( " ^  String.concat vnames ^ " ,  " ^ print_expr expr ^ " ) "
  | print_expr (Applies (exp1, exp2)) = "Applies " ^ print_expr exp1 ^ " " ^ (fold (curry (op ^)) (map print_expr exp2) " ")
  | print_expr (Literal _) = "Literal lit "
  | print_expr (Assert (ass, expres)) = "Assert ( " ^ SeLFiE_Util.print_assert ass ^ "," ^ (fold (curry (op ^)) (map print_expr expres) " ) ")
  | print_expr (Dive_In   _) = "Dive_In ...\n"
  | print_expr (Deep_Dive _) = "Deep_Dive ...\n"
  | print_expr (All  (vname, _, expr)) = "All ( "  ^ vname ^ ", " ^ print_expr expr ^ " ) "
  | print_expr (Some (vname, _, expr)) = "Some ( " ^ vname ^ ", " ^ print_expr expr ^ " ) ";

type name_scope = (string * int) list; (*map a variable name to a de-Bruijn index*)

fun print_env' [] = ""
  | print_env' ((vname, i)::pairs) = (" " ^ vname ^ " " ^ Int.toString i ^ "\n") ^ print_env' pairs;
fun print_env pairs = "Print environment \n" ^ print_env' pairs;

fun lookup (scope:name_scope) name = AList.lookup (op =) scope name |> (Utils.the' ("lookup in Eval_Var failed with " ^ name)): int;
fun update (new_entry: (string * int)) (scope:name_scope) =
    map (apsnd (fn x => x + 1)) scope
 |> AList.update (op =) new_entry: name_scope;
fun update_with_0 var_name scope = update (var_name, 0) scope: name_scope;
fun increment_then_update_with_0_n_times'  []           (scope,                    acc) = (scope, acc)
  | increment_then_update_with_0_n_times' (name::names) (scope,                    acc) =
    increment_then_update_with_0_n_times'  names        (update_with_0 name scope, acc + 1): (name_scope * int);

fun increment_then_update_with_0_n_times names scope = increment_then_update_with_0_n_times' names (scope, ~1): name_scope * int;

fun var_to_mult scope (Variable vname        ) = EM.Bound (lookup scope vname)
  | var_to_mult scope (Lambdas (vnames, expr)) =
    let
      val (new_env, acc) = increment_then_update_with_0_n_times vnames scope: (name_scope * int);
    in
      EM.Lambdas (acc, var_to_mult new_env expr)
    end
  | var_to_mult scope (Applies   (expr, exprs))        = EM.Applies (var_to_mult scope expr, map (var_to_mult scope) exprs)
  | var_to_mult _     (Literal    l)                   = EM.Literal l
  | var_to_mult scope (Assert    (ass, params))        = EM.Assert (ass, map (var_to_mult scope) params)
  | var_to_mult scope (Dive_In   (target, lamb, args)) = EM.Dive_In   (var_to_mult scope target, var_to_mult scope lamb, map (var_to_mult scope) args)
  | var_to_mult scope (Deep_Dive (target, lamb, args)) = EM.Deep_Dive (var_to_mult scope target, var_to_mult scope lamb, map (var_to_mult scope) args)
  | var_to_mult scope (All       (vname, typ, expr))   = EM.All  (typ, var_to_mult (increment_then_update_with_0_n_times [vname] scope |> fst) expr)
  | var_to_mult scope (Some      (vname, typ, expr))   = EM.Some (typ, var_to_mult (increment_then_update_with_0_n_times [vname] scope |> fst) expr);

fun mult_to_var (EM.Literal l) = Literal l
  | mult_to_var _ = error "mult_to_var is defined only for Literal!"

fun eval (pst:Proof.state) (induct_args:SeLFiE_Util.induct_arguments) (expr:expr) =
  let
    val em_expr     = var_to_mult [] expr            : EM.expr;
    val mult_result = EM.eval pst induct_args em_expr: EM.expr;
  in
    mult_to_var mult_result
  end;

end;