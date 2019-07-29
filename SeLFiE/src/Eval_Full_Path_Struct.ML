(*  Title:      PSL/SeLFeE/src/Eval_Full_Path_Struct.thy
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Full_Path: EVAL_FULL_PATH =
struct

type connective = Eval_Connective.assert;
type print      = LiFtEr_Util.print;
type number     = Eval_Number.number;

structure EC  = Eval_Connective;
structure ENC = Eval_Node_Core;
structure ENS = Eval_Node_Sugar;
structure EUC = Eval_Unode_Core;
structure EUS = Eval_Unode_Sugar;
structure EFC = Eval_Fpunode_Core;
structure EFS = Eval_Fpunode_Sugar;
structure EPS = Eval_Print_Sugar;
structure EN  = Eval_Number;

datatype assert =
(*Eval_Node_Core*)
  Is_Cnst                of full_path
| Is_Free                of full_path
| Is_Var                 of full_path
| Is_Bound               of full_path
| Is_Lambda              of full_path
| Is_App                 of full_path
(*Eval_Node_Sugar*)
| Is_Atom                of full_path
| Is_Compund             of full_path
(*Eval_Unode_Core*)
| Has_Same_Prnt_As       of full_path * full_path
| Is_In_Trm_Prnt         of full_path * full_path
| Is_Deeper_Than         of full_path * full_path
| Is_Shallower_Than      of full_path * full_path
| Is_Path_Above          of full_path * full_path
| Is_Same_Path_As        of full_path * full_path
(*Eval_Unode_Sugar*)
| Is_As_Deep_As          of full_path * full_path
| Is_Path_Below          of full_path * full_path
(*Eval_Fpunode_Core*)
| Is_In_Same_Location_As of full_path * full_path
| Is_In_Chained          of full_path
| Is_In_Fst_Subg         of full_path
(*Eval_Fpunode_Sugar*)
| Is_Above               of full_path * full_path
| Is_Below               of full_path * full_path
| Is_Same_Occ_As         of full_path * full_path
(*Eval_Print_Sugar*)
| Fpnode_Has_Print       of full_path * print;

type full_path_to_fpunode_table = Full_Path_To_Fpunode.full_path_to_fpunode_table;

(*use local in end;*)

fun eval (table:full_path_to_fpunode_table) assert =
                                            
let

type fpunode = Full_Path_To_Fpunode.fpunode;

fun full_path_to_fpunode (fp:full_path) =
   Full_Path_Table.lookup table fp 
|> Utils.the' "lookup in full_path_to_node.ML failed";

fun full_path_to_unode (fp:full_path) = full_path_to_fpunode fp
|> Full_Path_To_Fpunode.fpunode_to_unode: UN.unode;

fun full_path_to_node (fp:full_path) = full_path_to_fpunode fp
|> Full_Path_To_Fpunode.fpunode_to_node: UN.node;

(*
fun full_path2_to_node2 (fp1:full_path, fp2:full_path) =
  apply2 full_path_to_node (fp1, fp2): UN.node * UN.node;
*)
fun full_path2_to_unode2 (fp1:full_path, fp2:full_path) =
  apply2 full_path_to_unode (fp1, fp2): UN.unode * UN.unode;

fun full_path2_to_fpunode2 (fp1:full_path, fp2:full_path) =
  apply2 full_path_to_fpunode (fp1, fp2): (fpunode * fpunode);

fun
  (*Eval_Node_Core*)
    eval' (Is_Cnst   fp) = full_path_to_node fp |> ENC.Is_Cnst   |> ENC.eval
  | eval' (Is_Free   fp) = full_path_to_node fp |> ENC.Is_Free   |> ENC.eval
  | eval' (Is_Var    fp) = full_path_to_node fp |> ENC.Is_Var    |> ENC.eval
  | eval' (Is_Bound  fp) = full_path_to_node fp |> ENC.Is_Bound  |> ENC.eval
  | eval' (Is_Lambda fp) = full_path_to_node fp |> ENC.Is_Lambda |> ENC.eval
  | eval' (Is_App    fp) = full_path_to_node fp |> ENC.Is_App    |> ENC.eval
  (*Eval_Node_Sugar*)
  | eval' (Is_Atom    fp) = full_path_to_node fp |> ENS.Is_Atom    |> ENS.eval
  | eval' (Is_Compund fp) = full_path_to_node fp |> ENS.Is_Compund |> ENS.eval
  (*Eval_Unode_Core*)
  | eval' (Has_Same_Prnt_As  pair) = full_path2_to_unode2 pair |> EUC.Has_Same_Prnt_As  |> EUC.eval
  | eval' (Is_In_Trm_Prnt    pair) = full_path2_to_unode2 pair |> EUC.Is_In_Trm_Prnt    |> EUC.eval
  | eval' (Is_Deeper_Than    pair) = full_path2_to_unode2 pair |> EUC.Is_Deeper_Than    |> EUC.eval
  | eval' (Is_Shallower_Than pair) = full_path2_to_unode2 pair |> EUC.Is_Shallower_Than |> EUC.eval
  | eval' (Is_Path_Above     pair) = full_path2_to_unode2 pair |> EUC.Is_Path_Above     |> EUC.eval
  | eval' (Is_Same_Path_As   pair) = full_path2_to_unode2 pair |> EUC.Is_Same_Path_As   |> EUC.eval
  (*Eval_Unode_Sugar*)
  | eval' (Is_As_Deep_As pair) = full_path2_to_unode2 pair |> EUS.Is_As_Deep_As |> EUS.eval
  | eval' (Is_Path_Below pair) = full_path2_to_unode2 pair |> EUS.Is_Path_Below |> EUS.eval
  (*Eval_Fpunode_Core*)
  | eval' (Is_In_Same_Location_As pair) = full_path2_to_fpunode2 pair |> EFC.Is_In_Same_Location_As |> EFC.eval
  | eval' (Is_In_Chained          fpun) = full_path_to_fpunode   fpun |> EFC.Is_In_Chained          |> EFC.eval
  | eval' (Is_In_Fst_Subg         fpun) = full_path_to_fpunode   fpun |> EFC.Is_In_Fst_Subg         |> EFC.eval
  (*Eval_Fpunode_Sugar*)
  | eval' (Is_Above       pair) = full_path2_to_fpunode2 pair |> EFS.Is_Above       |> EFS.eval
  | eval' (Is_Below       pair) = full_path2_to_fpunode2 pair |> EFS.Is_Below       |> EFS.eval
  | eval' (Is_Same_Occ_As pair) = full_path2_to_fpunode2 pair |> EFS.Is_Same_Occ_As |> EFS.eval
  (*Eval_Print_Sugar*)
  | eval' (Fpnode_Has_Print pair) = pair |> apfst full_path_to_fpunode |> EPS.Fpnode_Has_Print |> EPS.eval

in eval' assert end;

end;