(*  Title:      PSL/SeLFeE/src/Eval_Nnode_Sugar_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_UNODE_SUGAR =
sig

type assert_unode_core;
type assert_connective;
type unode;

datatype assert_unode_sugar =
  Assert_Unode_Core of assert_unode_core
| Connective        of assert_connective
| Is_As_Deep_As     of unode * unode
| Is_Path_Below     of unode * unode;

val eval_unode_sugar: assert_unode_sugar -> assert_connective;

end;