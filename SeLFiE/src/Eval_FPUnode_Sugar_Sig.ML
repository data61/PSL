(*  Title:      PSL/SeLFeE/src/Eval_Fpunode_Sugar_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_FPUNODE_SUGAR =
sig

type assert_fpunode_core;
type assert_connective;
type fpunode;

datatype assert_fpunode_sugar =
  Assert_Fpunode_Core of assert_fpunode_core
| Connective          of assert_connective
| Is_Above            of fpunode * fpunode
| Is_Below            of fpunode * fpunode
| Is_Same_Occ_As      of fpunode * fpunode;

val eval_fpunode_sugar: assert_fpunode_sugar -> Eval_Connective.assert_connective;

end;