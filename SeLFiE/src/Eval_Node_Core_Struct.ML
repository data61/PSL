(*  Title:      PSL/SeLFeE/src/Eval_Node_Core_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Node_Core: EVAL_NODE_CORE =
struct

type node = Unique_Node.node;

datatype assert_node_core =
  Is_Cnst          of node
| Is_Free          of node
| Is_Var           of node
| Is_Bound         of node (*corresponds to Bound in term*)
| Is_Lambda        of node (*lambda abstraction corresponding to Abs in Term*)
| Is_App           of node (*function application corresponding to $ in Term*)

fun eval_node_core' (Is_Cnst   node) = UN.is_NC node
  | eval_node_core' (Is_Free   node) = UN.is_NF node
  | eval_node_core' (Is_Var    node) = UN.is_NV node
  | eval_node_core' (Is_Bound  node) = UN.is_NB node
  | eval_node_core' (Is_Lambda node) = UN.is_NL node
  | eval_node_core' (Is_App    node) = UN.is_NA node;

fun eval_node_core assert_node_core =
    eval_node_core' assert_node_core
 |> Eval_Connective.bool_to_assert_connective;

end;