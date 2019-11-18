(*  Title:      PSL/SeLFeE/src/Eval_Path_Sig.thy
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_INNER_PATH =
sig

type connective = Eval_Connective.assert;
type path       = UN.path;
type print      = LiFtEr_Util.print;

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

val eval: path_to_unode_table -> assert -> Eval_Connective.assert;

end;