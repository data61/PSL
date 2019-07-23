(*  Title:      PSL/SeLFeE/src/Eval_Primitive_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_PRIMITIVE =
sig

type connective = Eval_Connective.assert;
type node       = UN.node;
type unode      = UN.unode;
type fpunode    = Full_Path_To_Fpunode.fpunode;
type print      = LiFtEr_Util.print;

datatype assert =
(*Eval_Connective*)
  True
| False
| Not                    of connective
| And                    of connective * connective
| Or                     of connective * connective
| Nor                    of connective * connective
| Imply                  of connective * connective
| Ands                   of connective list
| Ors                    of connective list
(*Eval_Node_Core*)
| Is_Cnst                of node
| Is_Free                of node
| Is_Var                 of node
| Is_Bound               of node
| Is_Lambda              of node
| Is_App                 of node
(*Eval_Node_Sugar*)
| Is_Atom                of node
| Is_Compund             of node
(*Eval_Unode_Core*)
| Has_Same_Prnt_As       of unode * unode
| Is_In_Trm_Prnt         of unode * unode
| Is_Deeper_Than         of unode * unode
| Is_Shallower_Than      of unode * unode
| Is_Path_Above          of unode * unode
| Is_Same_Path_As        of unode * unode
(*Eval_Unode_Sugar*)
| Is_As_Deep_As          of unode * unode
| Is_Path_Below          of unode * unode
(*Eval_Fpunode_Core*)
| Is_In_Same_Location_As of fpunode * fpunode
| Is_In_Chained          of fpunode
| Is_In_Fst_Subg         of fpunode
(*Eval_Fpunode_Sugar*)
| Is_Above               of fpunode * fpunode
| Is_Below               of fpunode * fpunode
| Is_Same_Occ_As         of fpunode * fpunode
(*Eval_Print_Core*)
| Are_Same_Prints        of print * print
| Is_Printed_As          of print * string
(*Eval_Print_Sugar*)
| Are_Different_Prints   of print   * print
| Fpnode_Has_Print       of fpunode * print;

val eval: assert -> Eval_Connective.assert;

end