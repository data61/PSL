(*  Title:      PSL/SeLFeE/src/Eval_Path_Struct.thy
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Path: EVAL_PATH =
struct

type connective = Eval_Connective.assert;
type print      = LiFtEr_Util.print;
type number     = Eval_Number.number;
type path       = UN.path;

structure EC  = Eval_Connective;
structure ENC = Eval_Node_Core;
structure ENS = Eval_Node_Sugar;
structure EUC = Eval_Unode_Core;
structure EUS = Eval_Unode_Sugar;
structure EPS = Eval_Print_Sugar;
structure EN  = Eval_Number;

datatype assert =
(*Eval_Node_Core*)
  Is_Cnst                of path
| Is_Free                of path
| Is_Var                 of path
| Is_Bound               of path
| Is_Lambda              of path
| Is_App                 of path
(*Eval_Node_Sugar*)
| Is_Atom                of path
| Is_Compund             of path
(*Eval_Unode_Core*)
| Has_Same_Prnt_As       of path * path
| Is_In_Trm_Prnt         of path * path
| Is_Deeper_Than         of path * path
| Is_Shallower_Than      of path * path
| Is_Path_Above          of path * path
| Is_Same_Path_As        of path * path
(*Eval_Unode_Sugar*)
| Is_As_Deep_As          of path * path
| Is_Path_Below          of path * path
(*Eval_Print_Sugar*)
| Unode_Has_Print        of path * print;

type path_to_unode_table = Path_To_Unode.path_to_unode_table;

(*use local in end;*)

fun eval (table:path_to_unode_table) assert =
                                            
let

type unode = UN.unode;

fun path_to_unode (p:path) = Path_Table.lookup table p |> Utils.the' "lookup in path_to_unode failed";

fun path_to_node  (p:path) = path_to_unode p |> #node: UN.node;

fun path2_to_unode2 (p1:path, p2:path) = apply2 path_to_unode (p1, p2): (UN.unode * UN.unode);
(*
fun full_path2_to_unode2 (fp1:full_path, fp2:full_path) =
  apply2 full_path_to_unode (fp1, fp2): UN.unode * UN.unode;

fun full_path2_to_fpunode2 (fp1:full_path, fp2:full_path) =
  apply2 full_path_to_fpunode (fp1, fp2): (fpunode * fpunode);
*)
fun
  (*Eval_Node_Core*)
    eval' (Is_Cnst   p) = path_to_node p |> ENC.Is_Cnst   |> ENC.eval
  | eval' (Is_Free   p) = path_to_node p |> ENC.Is_Free   |> ENC.eval
  | eval' (Is_Var    p) = path_to_node p |> ENC.Is_Var    |> ENC.eval
  | eval' (Is_Bound  p) = path_to_node p |> ENC.Is_Bound  |> ENC.eval
  | eval' (Is_Lambda p) = path_to_node p |> ENC.Is_Lambda |> ENC.eval
  | eval' (Is_App    p) = path_to_node p |> ENC.Is_App    |> ENC.eval
  (*Eval_Node_Sugar*)
  | eval' (Is_Atom    p) = path_to_node p |> ENS.Is_Atom    |> ENS.eval
  | eval' (Is_Compund p) = path_to_node p |> ENS.Is_Compund |> ENS.eval
  (*Eval_Unode_Core*)
  | eval' (Has_Same_Prnt_As  pair) = path2_to_unode2 pair |> EUC.Has_Same_Prnt_As  |> EUC.eval
  | eval' (Is_In_Trm_Prnt    pair) = path2_to_unode2 pair |> EUC.Is_In_Trm_Prnt    |> EUC.eval
  | eval' (Is_Deeper_Than    pair) = path2_to_unode2 pair |> EUC.Is_Deeper_Than    |> EUC.eval
  | eval' (Is_Shallower_Than pair) = path2_to_unode2 pair |> EUC.Is_Shallower_Than |> EUC.eval
  | eval' (Is_Path_Above     pair) = path2_to_unode2 pair |> EUC.Is_Path_Above     |> EUC.eval
  | eval' (Is_Same_Path_As   pair) = path2_to_unode2 pair |> EUC.Is_Same_Path_As   |> EUC.eval
  (*Eval_Unode_Sugar*)
  | eval' (Is_As_Deep_As pair) = path2_to_unode2 pair |> EUS.Is_As_Deep_As |> EUS.eval
  | eval' (Is_Path_Below pair) = path2_to_unode2 pair |> EUS.Is_Path_Below |> EUS.eval
  (*Eval_Print_Sugar*)
  | eval' (Unode_Has_Print pair) = pair |> apfst path_to_unode |> EPS.Unode_Has_Print |> EPS.eval;

in eval' assert end;

end;