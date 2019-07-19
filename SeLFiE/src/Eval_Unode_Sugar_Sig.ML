(*  Title:      PSL/SeLFeE/src/Eval_Nnode_Sugar_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_UNODE_SUGAR =
sig

datatype assert =
  Connective        of Eval_Connective.assert
| Is_As_Deep_As     of UN.unode * UN.unode
| Is_Path_Below     of UN.unode * UN.unode;

val eval: assert -> Eval_Connective.assert;

end;