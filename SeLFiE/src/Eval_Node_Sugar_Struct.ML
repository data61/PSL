(*  Title:      PSL/SeLFeE/src/Eval_Node_Sugar_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Node_Sugar: EVAL_NODE_SUGAR =
struct

open Eval_Node_Core;
open Eval_Connective;

datatype assert_node_sugar =
  Assert_Node_Core of assert_node_core
| Connective       of assert_connective
| Is_Atom          of node
| Is_Compund       of node;

infix Or;

fun eval_node_sugar (Assert_Node_Core assert_node_core) = eval_node_core assert_node_core
  | eval_node_sugar (Connective assert_connective)      = eval_connective assert_connective
  | eval_node_sugar (Is_Atom assert_node_sugar)         =
    eval_connective (eval_node_core (Is_Cnst  assert_node_sugar)
                  Or eval_node_core (Is_Free  assert_node_sugar)
                  Or eval_node_core (Is_Var   assert_node_sugar)
                  Or eval_node_core (Is_Bound assert_node_sugar))
  | eval_node_sugar (Is_Compund node)                   =
    eval_connective (eval_node_core (Is_Lambda node)
                  Or eval_node_core (Is_App    node));

end;