(*  Title:      PSL/SeLFeE/src/Eval_Node_Core_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_NODE_CORE =
sig

type node;

datatype assert_node_core =
  Is_Cnst   of node
| Is_Free   of node
| Is_Var    of node
| Is_Bound  of node (*corresponds to Bound in term*)
| Is_Lambda of node (*lambda abstraction corresponding to Abs in Term*)
| Is_App    of node (*function application corresponding to $ in Term*)

val eval_node_core: assert_node_core -> Eval_Connective.assert_connective;

end;