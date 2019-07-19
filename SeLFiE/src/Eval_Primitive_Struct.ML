(*  Title:      PSL/SeLFeE/src/Eval_Primitive_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Primitive: EVAL_PRIMITIVE =
struct

structure EC  = Eval_Connective;
structure ENC = Eval_Node_Core;
structure ENS = Eval_Node_Sugar;
structure EUC = Eval_Unode_Core;
structure EUS = Eval_Unode_Sugar;
structure EFC = Eval_Fpunode_Core;
structure EFS = Eval_Fpunode_Sugar;
structure EPC = Eval_Print_Core;
structure EPS = Eval_Print_Sugar;

type connective = Eval_Connective.assert;
type node       = UN.node;
type unode      = UN.unode;
type fpunode    = Full_Path_To_Fpunode.fpunode;
type print      = LiFtEr_Util.print;

(*TODO: primitive should not take arguments.
  val eval: primitive -> atom list -> connective *)
datatype assert =
(*Eval_Connective*)
  True
| False
| Not                    of connective
| And                    of connective * connective
| Or                     of connective * connective
| Nor                    of connective * connective
| Imply                  of connective * connective
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

fun eval True         = EC.True     
  | eval False        = EC.False  
  | eval (Not con)    = EC.eval (EC.Not con)
  | eval (And pair)   = EC.eval (EC.And pair)
  | eval (Or  pair)   = EC.eval (EC.Or  pair)
  | eval (Nor pair)   = EC.eval (EC.Nor pair)
  | eval (Imply pair) = EC.eval (EC.Imply pair)
  (*Eval_Node_Core*)
  | eval (Is_Cnst   node)  = ENC.eval (ENC.Is_Cnst   node)
  | eval (Is_Free   node)  = ENC.eval (ENC.Is_Free   node)
  | eval (Is_Var    node)  = ENC.eval (ENC.Is_Var    node)
  | eval (Is_Bound  node)  = ENC.eval (ENC.Is_Bound  node)
  | eval (Is_Lambda node)  = ENC.eval (ENC.Is_Lambda node)
  | eval (Is_App    node)  = ENC.eval (ENC.Is_App    node)
  (*Eval_Node_Sugar*)
  | eval (Is_Atom    node) = ENS.eval (ENS.Is_Atom node)
  | eval (Is_Compund node) = ENS.eval (ENS.Is_Compund node)
  (*Eval_Unode_Core*)
  | eval (Has_Same_Prnt_As  pair) = EUC.eval (EUC.Has_Same_Prnt_As  pair)
  | eval (Is_In_Trm_Prnt    pair) = EUC.eval (EUC.Is_In_Trm_Prnt    pair)
  | eval (Is_Deeper_Than    pair) = EUC.eval (EUC.Is_Deeper_Than    pair)
  | eval (Is_Shallower_Than pair) = EUC.eval (EUC.Is_Shallower_Than pair)
  | eval (Is_Path_Above     pair) = EUC.eval (EUC.Is_Path_Above     pair)
  | eval (Is_Same_Path_As   pair) = EUC.eval (EUC.Is_Same_Path_As   pair)
  (*Eval_Unode_Sugar*)
  | eval (Is_As_Deep_As pair) = EUS.eval (EUS.Is_As_Deep_As pair)
  | eval (Is_Path_Below pair) = EUS.eval (EUS.Is_Path_Below pair)
  (*Eval_Fpunode_Core*)
  | eval (Is_In_Same_Location_As pair) = EFC.eval (EFC.Is_In_Same_Location_As pair)
  | eval (Is_In_Chained          fpun) = EFC.eval (EFC.Is_In_Chained          fpun)
  | eval (Is_In_Fst_Subg         fpun) = EFC.eval (EFC.Is_In_Fst_Subg         fpun)
  (*Eval_Fpunode_Sugar*)
  | eval (Is_Above       pair) = EFS.eval (EFS.Is_Above pair)
  | eval (Is_Below       pair) = EFS.eval (EFS.Is_Below pair)
  | eval (Is_Same_Occ_As pair) = EFS.eval (EFS.Is_Same_Occ_As pair)
  (*Eval_Print_Core*)
  | eval (Are_Same_Prints pair) = EPC.eval (EPC.Are_Same_Prints pair)
  | eval (Is_Printed_As pair)   = EPC.eval (EPC.Is_Printed_As   pair)
  (*Eval_Print_Sugar*)
  | eval (Are_Different_Prints pair) = EPS.eval (EPS.Are_Different_Prints pair)
  | eval (Fpnode_Has_Print     pair) = EPS.eval (EPS.Fpnode_Has_Print     pair);

end;