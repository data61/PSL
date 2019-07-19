(*  Title:      PSL/SeLFeE/src/Eval_FPUnode_Core_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_FPUNODE_CORE =
sig

type fpunode = Full_Path_To_Fpunode.fpunode;

datatype assert =
  Is_In_Same_Location_As of fpunode * fpunode
| Is_In_Chained          of fpunode
| Is_In_Fst_Subg         of fpunode;

val eval: assert -> Eval_Connective.assert;

end;