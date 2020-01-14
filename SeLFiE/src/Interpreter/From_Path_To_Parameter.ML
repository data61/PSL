(*  Title:      PSL/SeLFiE/src/From_Path_To_Parameter.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** functor from_Eval_Path_to_Eval_Parameter:EVAL_PATH -> EVAL_PARAMETER ***)
functor from_Path_to_Parameter (Eval_Path:EVAL_PATH): EVAL_PARAMETER =
struct

type path    = Eval_Path.path;
type command = Pattern.command;

datatype parameter =
  Path      of path
| Print     of string
| String    of string(*redundant?*)
| Number    of int
| Int       of int
| Command   of command;

type parameters = parameter list;

type atomic_assert = SeLFiE_Util.atomic_assert;

structure EPT  = Eval_Path;
structure EPR  = Eval_Print;
structure ENMB = Eval_Number;
structure SU   = SeLFiE_Util;

fun eval trm pst assert parameters =
  let
    fun
      (*Eval_Node*)
        eval' SU.Is_Cnst   [Path p] = EPT.eval trm pst (EPT.Is_Cnst   p)
      | eval' SU.Is_Free   [Path p] = EPT.eval trm pst (EPT.Is_Free   p)
      | eval' SU.Is_Var    [Path p] = EPT.eval trm pst (EPT.Is_Var    p)
      | eval' SU.Is_Bound  [Path p] = EPT.eval trm pst (EPT.Is_Bound  p)
      | eval' SU.Is_Lambda [Path p] = EPT.eval trm pst (EPT.Is_Lambda p)
      | eval' SU.Is_App    [Path p] = EPT.eval trm pst (EPT.Is_App    p)
      (*Eval_Unode*)
      | eval' SU.Has_Same_Prnt_As  [Path p1, Path p2] = EPT.eval trm pst (EPT.Has_Same_Prnt_As  (p1, p2))
      | eval' SU.Is_In_Trm_Prnt    [Path p1, Path p2] = EPT.eval trm pst (EPT.Is_In_Trm_Prnt    (p1, p2))
      | eval' SU.Is_Deeper_Than    [Path p1, Path p2] = EPT.eval trm pst (EPT.Is_Deeper_Than    (p1, p2))
      | eval' SU.Is_Shallower_Than [Path p1, Path p2] = EPT.eval trm pst (EPT.Is_Shallower_Than (p1, p2))
      | eval' SU.Is_Path_Above     [Path p1, Path p2] = EPT.eval trm pst (EPT.Is_Path_Above     (p1, p2))
      | eval' SU.Is_Same_Path_As   [Path p1, Path p2] = EPT.eval trm pst (EPT.Is_Same_Path_As   (p1, p2))
     (*Eval_Print*)
      | eval' SU.Are_Same_Prints [Print p1, Print p2] = EPR.eval (EPR.Are_Same_Prints (p1, p2))
      (*Eval_Number*)
      | eval' SU.Are_Same_Number [Number numb1,  Number numb2] = ENMB.eval (ENMB.Are_Same_Number (numb1, numb2))
      | eval' SU.Is_Less_Than    [Number numb1,  Number numb2] = ENMB.eval (ENMB.Is_Less_Than    (numb1, numb2))
      | eval' _ _ = error "eval' in Eval_Parameters_Struct.ML failed!"
  in
    eval' assert parameters: Eval_Bool.assert
  end;

end;