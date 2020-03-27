(*  Title:      PSL/SeLFeE/src/Interpreter/Eval_Variable.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
(*** signature: EVAL_VARIABLE ***)
signature EVAL_VARIABLE =
sig

type outer_parameter = Eval_Deep.outer_parameter;
type inner_parameter = Eval_Deep.inner_parameter;

datatype outer_expression =
  Outer_Variable of string
| Outer_Lambdas  of strings * outer_expression (*(0, exp) means one lambda abstraction, and (1, exp) means two lambda abstractions.*)
| Outer_Applies  of outer_expression * outer_expression list
| Outer_Literal  of outer_parameter
| Outer_Assert   of SeLFiE_Util.assert * outer_expression list
| Outer_All      of string * SeLFiE_Util.qtyp * outer_expression
| Outer_Some     of string * SeLFiE_Util.qtyp * outer_expression
| Dive_In        of outer_expression * inner_expression * outer_expression list  
                   (*target, Inner_Lambdas inner_lambda, outer_args*)
and inner_expression =
  Inner_Variable of string
| Inner_Lambdas  of strings * inner_expression (*(0, exp) means one lambda abstraction, and (1, exp) means two lambda abstractions.*)
| Inner_Applies  of inner_expression * inner_expression list
| Inner_Literal  of inner_parameter
| Inner_Assert   of SeLFiE_Util.assert * inner_expression list
| Inner_All      of string * SeLFiE_Util.qtyp * inner_expression
| Inner_Some     of string * SeLFiE_Util.qtyp * inner_expression
| Dive_Deeper    of inner_expression * inner_expression * inner_expression list;

datatype expr = Outer of outer_expression | Inner of inner_expression;

val eval: Proof.state -> SeLFiE_Util.induct_arguments -> expr -> expr;

end;

(*** structure: Eval_Variable ***)
structure Eval_Variable: EVAL_VARIABLE =
struct

structure EOM = Eval_Outer_Multiple;
structure EIM = Eval_Inner_Multiple;
structure SU  = SeLFiE_Util;
structure ED = Eval_Deep;

type outer_path = ED.outer_path;
type inner_path = ED.inner_path;
type command    = Pattern.command;
type qtyp       = SeLFiE_Util.qtyp;

type outer_parameter = ED.outer_parameter;
type inner_parameter = ED.inner_parameter;

type qtyps = SeLFiE_Util.qtyp list;

datatype outer_expression =
  Outer_Variable of string
| Outer_Lambdas  of strings * outer_expression (*(0, exp) means one lambda abstraction, and (1, exp) means two lambda abstractions.*)
| Outer_Applies  of outer_expression * outer_expression list
| Outer_Literal  of outer_parameter
| Outer_Assert   of SeLFiE_Util.assert * outer_expression list
| Outer_All      of string * SeLFiE_Util.qtyp * outer_expression
| Outer_Some     of string * SeLFiE_Util.qtyp * outer_expression
| Dive_In        of outer_expression * inner_expression * outer_expression list  
                   (*target, Inner_Lambdas inner_lambda, outer_args*)
and inner_expression =
  Inner_Variable of string
| Inner_Lambdas  of strings * inner_expression (*(0, exp) means one lambda abstraction, and (1, exp) means two lambda abstractions.*)
| Inner_Applies  of inner_expression * inner_expression list
| Inner_Literal  of inner_parameter
| Inner_Assert   of SeLFiE_Util.assert * inner_expression list
| Inner_All      of string * SeLFiE_Util.qtyp * inner_expression
| Inner_Some     of string * SeLFiE_Util.qtyp * inner_expression
| Dive_Deeper    of inner_expression * inner_expression * inner_expression list;

type name_scope = (string * int) list; (*map a variable name to a de-Bruijn index*)

fun print_env' [] = ""
  | print_env' ((vname, i)::pairs) = (" " ^ vname ^ " " ^ Int.toString i ^ "\n") ^ print_env' pairs;
fun print_env pairs = "Print environment \n" ^ print_env' pairs;
fun lookup (scope:name_scope) name = AList.lookup (op =) scope name |> Utils.the' "lookup in Eval_Var failed.": int;
fun update (new_entry: (string * int)) (scope:name_scope) =
    map (apsnd (fn x => x + 1)) scope
 |> AList.update (op =) new_entry: name_scope;
fun increment (alist:name_scope) = map (apsnd (curry (op +) 1)) alist: name_scope;
fun update_with_0 var_name scope = update (var_name, 0) scope: name_scope;
fun increment_then_update_with_0 var_name scope = scope |> increment |> update_with_0 var_name: name_scope;

fun increment_then_update_with_0_n_times'  []           (scope,                    acc) = (scope, acc)
  | increment_then_update_with_0_n_times' (name::names) (scope,                    acc) =
    increment_then_update_with_0_n_times'  names        (update_with_0 name scope, acc + 1): (name_scope * int);

fun increment_then_update_with_0_n_times names scope = increment_then_update_with_0_n_times' names (scope, ~1): name_scope * int;

fun transfer_outer scope (Outer_Variable vname)         = ED.Outer_Bound (lookup scope vname)
  | transfer_outer scope (Outer_Lambdas (vnames, expr)) =
    let
      val (new_env, acc) = increment_then_update_with_0_n_times vnames scope: (name_scope * int);
    in
      ED.Outer_Lambdas (acc, transfer_outer new_env expr)
    end
  | transfer_outer scope (Outer_Applies (expr, exprs))     = ED.Outer_Applies (transfer_outer scope expr, map (transfer_outer scope) exprs)
  | transfer_outer _   (Outer_Literal  param)            = ED.Outer_Literal param
  | transfer_outer scope (Outer_Assert  (assert, params))  = ED.Outer_Assert (assert, map (transfer_outer scope) params)
  | transfer_outer scope (Outer_All     (name, typ, expr)) = ED.Outer_All    (typ, transfer_outer (increment_then_update_with_0 name scope) expr)
  | transfer_outer scope (Outer_Some    (name, typ, expr)) = ED.Outer_Some   (typ, transfer_outer (increment_then_update_with_0 name scope) expr)
  | transfer_outer scope (Dive_In (target, inner_func, outer_args)) =
    ED.Dive_In (transfer_outer scope target,
                transfer_inner [] inner_func,(*We only pass literals to inner layers.*)
                map (transfer_outer scope) outer_args)
and transfer_inner scope (Inner_Variable vname)         = ED.Inner_Bound (lookup scope vname)
  | transfer_inner scope (Inner_Lambdas (vnames, expr)) =
    let
      val (new_env, acc) = increment_then_update_with_0_n_times vnames scope: (name_scope * int);
    in
      ED.Inner_Lambdas (acc, transfer_inner new_env expr)
    end
  | transfer_inner scope (Inner_Applies (expr, exprs))     = ED.Inner_Applies (transfer_inner scope expr, map (transfer_inner scope) exprs)
  | transfer_inner _   (Inner_Literal  param)            = ED.Inner_Literal param
  | transfer_inner scope (Inner_Assert  (assert, params))  = ED.Inner_Assert (assert, map (transfer_inner scope) params)
  | transfer_inner scope (Inner_All     (name, typ, expr)) = ED.Inner_All    (typ, transfer_inner (increment_then_update_with_0 name scope) expr)
  | transfer_inner scope (Inner_Some    (name, typ, expr)) = ED.Inner_Some   (typ, transfer_inner (increment_then_update_with_0 name scope) expr)
  | transfer_inner scope (Dive_Deeper (target, inner_func, outer_args)) =
    ED.Dive_Deeper (transfer_inner scope target,
                    transfer_inner [] inner_func,(*We only pass literals to inner layers.*)
                    map (transfer_inner scope) outer_args);

datatype expr = Outer of outer_expression | Inner of inner_expression;

fun deep_to_variable (ED.Outer (ED.Outer_Literal l)) = Outer (Outer_Literal l)
  | deep_to_variable (ED.Outer (ED.Outer_Bound   b)) = Outer (Outer_Variable "y"(*FIXME!*))
  | deep_to_variable _ = error "deep_to_variable in Eval_Variable.ML failed";

fun eval (pst:Proof.state) (induct_args:SeLFiE_Util.induct_arguments) (Outer outer_expr) =
  let
    val ed_expr   = transfer_outer [] outer_expr: ED.outer_expression;
    val result_ed = ED.eval pst induct_args (ED.Outer ed_expr);
  in
    deep_to_variable result_ed
  end
  | eval  _ _ _ = error "eval in Eval_Variable.ML failed. eval is defined only for Outer.";

end;