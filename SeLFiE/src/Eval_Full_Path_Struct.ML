(*  Title:      PSL/SeLFeE/src/Eval_Full_Path_Struct.thy
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Full_Path: EVAL_FULL_PATH =
struct

type connective = Eval_Connective.assert;
type print      = LiFtEr_Util.print;
structure EC = Eval_Connective;
structure EP = Eval_Primitive;        

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
| Is_Cnst                of full_path
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
(*Eval_Print_Core*)
| Are_Same_Prints        of print * print
| Is_Printed_As          of print * string
(*Eval_Print_Sugar*)
| Are_Different_Prints   of print     * print
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
  (*Eval_Connective*)
    eval'  True        = EC.True
  | eval'  False       = EC.False
  | eval' (Not con)    = EC.eval (EC.Not con)
  | eval' (And pair)   = EC.eval (EC.eval (EC.And pair))
  | eval' (Or  pair)   = EC.eval (EC.Or  pair)
  | eval' (Nor pair)   = EC.eval (EC.Nor pair)
  | eval' (Imply pair) = EC.eval (EC.Imply pair)
  | eval' (Ands cons)  = EC.eval (EC.Ands cons)
  | eval' (Ors  cons)  = EC.eval (EC.Ors  cons)
  (*Eval_Node_Core*)
  | eval' (Is_Cnst   fp) = full_path_to_node fp |> EP.Is_Cnst   |> EP.eval
  | eval' (Is_Free   fp) = full_path_to_node fp |> EP.Is_Free   |> EP.eval
  | eval' (Is_Var    fp) = full_path_to_node fp |> EP.Is_Var    |> EP.eval
  | eval' (Is_Bound  fp) = full_path_to_node fp |> EP.Is_Bound  |> EP.eval
  | eval' (Is_Lambda fp) = full_path_to_node fp |> EP.Is_Lambda |> EP.eval
  | eval' (Is_App    fp) = full_path_to_node fp |> EP.Is_App    |> EP.eval
  (*Eval_Node_Sugar*)
  | eval' (Is_Atom    fp) = full_path_to_node fp |> EP.Is_Atom    |> EP.eval
  | eval' (Is_Compund fp) = full_path_to_node fp |> EP.Is_Compund |> EP.eval
  (*Eval_Unode_Core*)
  | eval' (Has_Same_Prnt_As  pair) = full_path2_to_unode2 pair |> EP.Has_Same_Prnt_As  |> EP.eval
  | eval' (Is_In_Trm_Prnt    pair) = full_path2_to_unode2 pair |> EP.Is_In_Trm_Prnt    |> EP.eval
  | eval' (Is_Deeper_Than    pair) = full_path2_to_unode2 pair |> EP.Is_Deeper_Than    |> EP.eval
  | eval' (Is_Shallower_Than pair) = full_path2_to_unode2 pair |> EP.Is_Shallower_Than |> EP.eval
  | eval' (Is_Path_Above     pair) = full_path2_to_unode2 pair |> EP.Is_Path_Above     |> EP.eval
  | eval' (Is_Same_Path_As   pair) = full_path2_to_unode2 pair |> EP.Is_Same_Path_As   |> EP.eval
  (*Eval_Unode_Sugar*)
  | eval' (Is_As_Deep_As pair) = full_path2_to_unode2 pair |> EP.Is_As_Deep_As |> EP.eval
  | eval' (Is_Path_Below pair) = full_path2_to_unode2 pair |> EP.Is_Path_Below |> EP.eval
  (*Eval_Fpunode_Core*)
  | eval' (Is_In_Same_Location_As pair) = full_path2_to_fpunode2 pair |> EP.Is_In_Same_Location_As |> EP.eval
  | eval' (Is_In_Chained          fpun) = full_path_to_fpunode   fpun |> EP.Is_In_Chained          |> EP.eval
  | eval' (Is_In_Fst_Subg         fpun) = full_path_to_fpunode   fpun |> EP.Is_In_Fst_Subg         |> EP.eval
  (*Eval_Fpunode_Sugar*)
  | eval' (Is_Above       pair) = full_path2_to_fpunode2 pair |> EP.Is_Above       |> EP.eval
  | eval' (Is_Below       pair) = full_path2_to_fpunode2 pair |> EP.Is_Below       |> EP.eval
  | eval' (Is_Same_Occ_As pair) = full_path2_to_fpunode2 pair |> EP.Is_Same_Occ_As |> EP.eval
  (*Eval_Print_Core*)
  | eval' (Are_Same_Prints pair) = EP.eval (EP.Are_Same_Prints pair)
  | eval' (Is_Printed_As pair)   = EP.eval (EP.Is_Printed_As   pair)
  (*Eval_Print_Sugar*)
  | eval' (Are_Different_Prints pair) = EP.eval (EP.Are_Different_Prints pair)
  | eval' (Fpnode_Has_Print     pair) = pair |> apfst full_path_to_fpunode |> EP.Fpnode_Has_Print |> EP.eval

in eval' assert end;

end;