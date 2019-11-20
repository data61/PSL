(*  Title:      PSL/SeLFeE/src/Interpreter/Eval_Path.thy
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** EVAL_INNER_PATH ***)
signature EVAL_PATH =
sig

type connective = Eval_Bool.assert;
type path       = UN.inner_path;
type print      = SeLFiE_Util.print;
type assert;
(*
datatype assert =
(*Eval_Node*)
  Is_Cnst                of path
| Is_Free                of path
| Is_Var                 of path
| Is_Bound               of path
| Is_Lambda              of path
| Is_App                 of path
(*Eval_Unode*)
| Has_Same_Prnt_As       of path * path
| Is_In_Trm_Prnt         of path * path
| Is_Deeper_Than         of path * path
| Is_Shallower_Than      of path * path
| Is_Path_Above          of path * path
| Is_Same_Path_As        of path * path
*)
(*Eval_Print_Sugar*)
(*TODO: | Unode_Has_Print        of path * print;*)

type path_to_unode_table = Inner_Path_To_Inner_Unode.path_to_unode_table;

(*val eval: path_to_unode_table -> assert -> Eval_Bool.assert;*)
val eval: term -> Proof.state -> assert -> Eval_Bool.assert;

end;

(*** Eval_Inner_Path ***)
structure Eval_Inner_Path(*: EVAL_INNER_PATH*) =
struct

type connective = Eval_Bool.assert;
type print      = SeLFiE_Util.print;
type number     = Eval_Number.number;
type path       = UN.inner_path;

structure END = Eval_Node;
structure EU  = Eval_Unode;
structure EIP = Eval_Inner_Print;
structure ENB = Eval_Number;

datatype assert =
(*Eval_Node_Core*)
  Is_Cnst                of path
| Is_Free                of path
| Is_Var                 of path
| Is_Bound               of path
| Is_Lambda              of path
| Is_App                 of path
(*Eval_Unode*)
| Has_Same_Prnt_As       of path * path
| Is_In_Trm_Prnt         of path * path
| Is_Deeper_Than         of path * path
| Is_Shallower_Than      of path * path
| Is_Path_Above          of path * path
| Is_Same_Path_As        of path * path;

type path_to_unode_table = Inner_Path_To_Inner_Unode.path_to_unode_table;
val trm_n_pst_to_path_to_unode_table = undefined: term -> Proof.state -> path_to_unode_table;(*TODO*)

(*use local in end;*)

fun eval (term:term) (pst:Proof.state) assert =
  let
    val table = trm_n_pst_to_path_to_unode_table term pst: path_to_unode_table;
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
      (*Eval_Node*)
        eval' (Is_Cnst   p) = path_to_node p |> END.Is_Cnst   |> END.eval
      | eval' (Is_Free   p) = path_to_node p |> END.Is_Free   |> END.eval
      | eval' (Is_Var    p) = path_to_node p |> END.Is_Var    |> END.eval
      | eval' (Is_Bound  p) = path_to_node p |> END.Is_Bound  |> END.eval
      | eval' (Is_Lambda p) = path_to_node p |> END.Is_Lambda |> END.eval
      | eval' (Is_App    p) = path_to_node p |> END.Is_App    |> END.eval
      (*Eval_Unode*)
      | eval' (Has_Same_Prnt_As  pair) = path2_to_unode2 pair |> EU.Has_Same_Prnt_As  |> EU.eval
      | eval' (Is_In_Trm_Prnt    pair) = path2_to_unode2 pair |> EU.Is_In_Trm_Prnt    |> EU.eval
      | eval' (Is_Deeper_Than    pair) = path2_to_unode2 pair |> EU.Is_Deeper_Than    |> EU.eval
      | eval' (Is_Shallower_Than pair) = path2_to_unode2 pair |> EU.Is_Shallower_Than |> EU.eval
      | eval' (Is_Path_Above     pair) = path2_to_unode2 pair |> EU.Is_Path_Above     |> EU.eval
      | eval' (Is_Same_Path_As   pair) = path2_to_unode2 pair |> EU.Is_Same_Path_As   |> EU.eval
      (*Eval_Print_Sugar*)
    (*TODO:  | eval' (Unode_Has_Print pair) = pair |> apfst path_to_unode |> EPS.Unode_Has_Print |> EPS.eval;*)
  in eval' assert end;

end;