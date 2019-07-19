(*  Title:      PSL/SeLFeE/src/Eval_Node_Core_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_NODE_CORE =
sig

datatype assert =
  Is_Cnst   of UN.node
| Is_Free   of UN.node
| Is_Var    of UN.node
| Is_Bound  of UN.node (*corresponds to Bound in term*)
| Is_Lambda of UN.node (*lambda abstraction corresponding to Abs in Term*)
| Is_App    of UN.node (*function application corresponding to $ in Term*)

val eval: assert -> Eval_Connective.assert;

end;