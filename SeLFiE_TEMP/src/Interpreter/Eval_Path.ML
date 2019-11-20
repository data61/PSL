(*  Title:      PSL/SeLFeE/src/Interpreter/Eval_Path.thy
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** signature EVAL_INNER_PATH ***)
signature EVAL_PATH =
sig

type connective = Eval_Bool.assert;
type path;
type print      = SeLFiE_Util.print;

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

(*Eval_Print_Sugar*)
(*TODO: | Unode_Has_Print        of path * print;*)

(*
type path_to_unode_table = Inner_Path_To_Inner_Unode.path_to_unode_table;
*)
(*val eval: path_to_unode_table -> assert -> Eval_Bool.assert;*)
val eval: term -> Proof.state -> assert -> Eval_Bool.assert;

end;