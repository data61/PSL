(*  Title:      PSL/SeLFeE/src/Interpreter/Eval_Path.thy
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** structure Path_Assert ***)
structure Path_Assert =
struct

datatype 'path assert =
(*Eval_Node*)
  Is_Cnst                of 'path
| Is_Free                of 'path
| Is_Var                 of 'path
| Is_Bound               of 'path
| Is_Lambda              of 'path
| Is_App                 of 'path
(*Eval_Unode*)
| Has_Same_Prnt_As       of 'path * 'path
| Is_In_Trm_Prnt         of 'path * 'path
| Is_Deeper_Than         of 'path * 'path
| Is_Shallower_Than      of 'path * 'path
| Is_Path_Above          of 'path * 'path
| Is_Same_Path_As        of 'path * 'path
| Is_Nth_Child           of 'path * int
| Is_N_Plus_One_th_Child of 'path * int
(*only in path*)
| Unode_Has_Print        of 'path * string
| Is_In_Subgoal          of 'path
| Is_In_Chained_Fact     of 'path
| Is_In_Nth_Subgoal      of 'path * int
| Is_In_Nth_Chained_Fact of 'path * int;

end;

(*** signature EVAL_EACH_PATH ***)
signature EVAL_EACH_PATH =
sig

type path;

val eval: term -> Proof.state -> path Path_Assert.assert -> Eval_Bool.assert;

end;

(*** signature EVAL_PATH ***)
signature EVAL_PATH =
sig

datatype gen_assert =
  Outer_Assert of outer_path    Path_Assert.assert
| Inner_Assert of UN.inner_path Path_Assert.assert;

val eval: term -> Proof.state -> gen_assert -> Eval_Bool.assert;

end;