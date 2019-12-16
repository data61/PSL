(*  Title:      PSL/SeLFeE/src/Eval_Node_Core_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** EVAL_NODE ***)
signature EVAL_NODE =
sig

datatype assert =
  Is_Cnst   of UN.node
| Is_Free   of UN.node
| Is_Var    of UN.node
| Is_Bound  of UN.node (*corresponds to Bound in term*)
| Is_Lambda of UN.node (*lambda abstraction corresponding to Abs in Term*)
| Is_App    of UN.node (*function application corresponding to $ in Term*)

val eval: assert -> Eval_Bool.assert;

end;

(*** Eval_Node ***)
structure Eval_Node: EVAL_NODE =
struct

datatype assert =
  Is_Cnst   of UN.node
| Is_Free   of UN.node
| Is_Var    of UN.node
| Is_Bound  of UN.node (*corresponds to Bound in term*)
| Is_Lambda of UN.node (*lambda abstraction corresponding to Abs in Term*)
| Is_App    of UN.node (*function application corresponding to $ in Term*)

fun eval' (Is_Cnst   node) = UN.is_NC node
  | eval' (Is_Free   node) = UN.is_NF node
  | eval' (Is_Var    node) = UN.is_NV node
  | eval' (Is_Bound  node) = UN.is_NB node
  | eval' (Is_Lambda node) = UN.is_NL node
  | eval' (Is_App    node) = UN.is_NA node;

fun eval assert = eval' assert |> Eval_Bool.bool_to_assert;

end;