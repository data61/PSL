(*  Title:      PSL/SeLFeE/src/Interpreter/Eval_Path.thy
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** functor make_Eval_Path: PATH_TO_UNODE -> EVAL_PATH ***)
functor make_Eval_Path (Path_To_Unode:PATH_TO_UNODE): EVAL_PATH =
struct

type connective = Eval_Bool.assert;
type print      = SeLFiE_Util.print;
type number     = Eval_Number.number;
type path       = Path_To_Unode.path;

structure END = Eval_Node;
structure EU  = Eval_Unode;
structure EIP = Eval_Print;
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
| Is_Same_Path_As        of path * path
(*only in path*)
| Unode_Has_Print        of path * print;

fun eval (term:term) (pst:Proof.state) assert =
  let
    val table  = Path_To_Unode.pst_n_trm_to_path_to_unode_table pst term: Path_To_Unode.path_to_unode_table;
    type unode = UN.unode;
    fun path_to_unode (p:path) = Path_To_Unode.lookup table p |> Utils.the' "lookup in path_to_unode failed";
    fun path_to_node  (p:path) = path_to_unode p |> #node: UN.node;
    fun path2_to_unode2 (p1:path, p2:path) = apply2 path_to_unode (p1, p2): (UN.unode * UN.unode);
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
      (*only in path*)
      | eval' (Unode_Has_Print pair) =
          let
            val this_print  = snd pair;
            val unode_print = pair |> fst |> path_to_unode |> #print: SeLFiE_Util.print;
          in
            SeLFiE_Util.same_prints this_print unode_print |> Eval_Bool.bool_to_assert
          end
  in eval' assert end;

end;