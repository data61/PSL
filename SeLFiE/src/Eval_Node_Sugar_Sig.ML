(*  Title:      PSL/SeLFeE/src/Eval_Node_Sugar_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_NODE_SUGAR =
sig

datatype assert =
  Connective of Eval_Connective.assert
| Is_Atom    of UN.node
| Is_Compund of UN.node;

val eval: assert -> Eval_Connective.assert;

end;