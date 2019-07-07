(*  Title:      PSL/SeLFeE/src/Eval_Unode_Core_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_UNODE_CORE =
sig

type unode;

datatype assert_unode_core =
  Assert_Node_Sugar of Eval_Node_Sugar.assert_node_sugar
| Has_Same_Prnt_As  of unode * unode
| Is_In_Trm_Prnt    of unode * unode (*sub-tree-1 is within sub-tree-2 string-wise*)
| Is_Deeper_Than    of unode * unode
| Is_Shallower_Than of unode * unode
| Is_Path_Above     of unode * unode
| Is_Same_Path_As   of unode * unode;

val eval_unode_core: assert_unode_core -> Eval_Connective.assert_connective;

end;