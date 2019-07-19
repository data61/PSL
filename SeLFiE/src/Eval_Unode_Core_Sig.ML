(*  Title:      PSL/SeLFeE/src/Eval_Unode_Core_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_UNODE_CORE =
sig

datatype assert =
  Has_Same_Prnt_As  of UN.unode * UN.unode
| Is_In_Trm_Prnt    of UN.unode * UN.unode (*sub-tree-1 is within sub-tree-2 string-wise*)
| Is_Deeper_Than    of UN.unode * UN.unode
| Is_Shallower_Than of UN.unode * UN.unode
| Is_Path_Above     of UN.unode * UN.unode
| Is_Same_Path_As   of UN.unode * UN.unode;

val eval: assert -> Eval_Connective.assert;

end;