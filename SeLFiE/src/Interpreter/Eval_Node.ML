(*  Title:      PSL/SeLFeE/src/Eval_Node_Core_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** EVAL_NODE ***)
signature EVAL_NODE =
sig

datatype assert =
  Is_Cnst         of UN.node
| Is_Free         of UN.node
| Is_Var          of UN.node
| Is_Bound        of UN.node (*corresponds to Bound in term*)
| Is_Lambda       of UN.node (*lambda abstraction corresponding to Abs in Term*)
| Is_App          of UN.node (*function application corresponding to $ in Term*)
| Is_Defined_With of UN.node * Pattern.command
| Is_Rule_Of_Node of string * UN.node;

val eval': assert -> Proof.context -> bool;
val eval: assert -> Proof.context -> Eval_Bool.assert;

end;

(*** Eval_Node ***)
structure Eval_Node: EVAL_NODE =
struct

datatype assert =
  Is_Cnst         of UN.node
| Is_Free         of UN.node
| Is_Var          of UN.node
| Is_Bound        of UN.node (*corresponds to Bound in term*)
| Is_Lambda       of UN.node (*lambda abstraction corresponding to Abs in Term*)
| Is_App          of UN.node (*function application corresponding to $ in Term*)
| Is_Defined_With of UN.node * Pattern.command
| Is_Rule_Of_Node of string * UN.node;

fun eval' (Is_Cnst   node) _ = UN.is_NC node
  | eval' (Is_Free   node) _ = UN.is_NF node
  | eval' (Is_Var    node) _ = UN.is_NV node
  | eval' (Is_Bound  node) _ = UN.is_NB node
  | eval' (Is_Lambda node) _ = UN.is_NL node
  | eval' (Is_App    node) _ = UN.is_NA node
  | eval' (Is_Defined_With (node, cmd)) _ = UN.is_defined_by node cmd
  | eval' (Is_Rule_Of_Node (rule, UN.NC (cname, _, _))) ctxt = SeLFiE_Util.rule_to_const_name ctxt rule = cname
  | eval' (Is_Rule_Of_Node _) _ = error "Is_Rule_Of_Node in Eval_Node failed.";

fun eval assert ctxt = eval' assert ctxt |> Eval_Bool.bool_to_assert;

end;