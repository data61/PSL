(*  Title:      PSL/SeLFeE/src/Eval_Node_Sugar_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_NODE_SUGAR =
sig

type assert_node_core;
type assert_connective;
type node;

datatype assert_node_sugar =
  Assert_Node_Core of assert_node_core
| Connective       of assert_connective
| Is_Atom          of node
| Is_Compund       of node;

val eval_node_sugar: assert_node_sugar -> assert_connective;

end;