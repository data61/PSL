(*  Title:      PSL/SeLFeE/src/Eval_FPUnode_Core_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_FPUNODE_CORE =
sig

type fpunode;

datatype assert_fpunode_core =
  Assert_Fpunode_Sugar   of Eval_Unode_Sugar.assert_unode_sugar
| Is_In_Same_Location_As of fpunode * fpunode
| Is_In_Chained          of fpunode
| Is_In_Fst_Subg         of fpunode;

val eval_fpunode_core: assert_fpunode_core -> Eval_Connective.assert_connective;

end;