(*  Title:      PSL/SeLFeE/src/Interpreter/Eval_Path.thy
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** signature EVAL_INNER_PATH ***)
signature EVAL_PATH =
sig

type connective = Eval_Bool.assert;
type path;

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
(*only in path*)
| Unode_Has_Print        of path * SeLFiE_Util.print
| Is_In_Subgoal          of path
| Is_In_Chained_Fact     of path
| Is_In_Nth_Subgoal      of path * int
| Is_In_Nth_Chained_Fact of path * int;

val eval: term -> Proof.state -> assert -> Eval_Bool.assert;

end;