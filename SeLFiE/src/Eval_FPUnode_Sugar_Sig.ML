(*  Title:      PSL/SeLFeE/src/Eval_Fpunode_Sugar_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_FPUNODE_SUGAR =
sig

type fpunode;

datatype assert =
  Connective          of Eval_Connective.assert
| Is_Above            of fpunode * fpunode
| Is_Below            of fpunode * fpunode
| Is_Same_Occ_As      of fpunode * fpunode;

val eval: assert -> Eval_Connective.assert;

end;