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
| Number    of int
| Command   of command;

type parameters = parameter list;

type atomic_assert = SeLFiE_Util.atomic_assert;

structure EPT  = Eval_Path;
structure EPR  = Eval_Print;
structure ENMB = Eval_Number;
structure SU   = SeLFiE_Util;
structure EIA  = Eval_Induct_Argument;

fun eval trm pst assert parameters =
  let
    val induct_args = error "TODO: get it from pst":SU.induct_arguments;
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
      | eval' SU.Is_Nth_Child      [Path p, Number n] = EPT.eval trm pst (EPT.Is_Nth_Child      (p,  n ))
      (*Eval_Path*)
      | eval' SU.Unode_Has_Print        [Path p, Print str] = EPT.eval trm pst (EPT.Unode_Has_Print   (p, str))
      | eval' SU.Is_In_Subgoal          [Path p]            = EPT.eval trm pst (EPT.Is_In_Subgoal      p)
      | eval' SU.Is_In_Chained_Fact     [Path p]            = EPT.eval trm pst (EPT.Is_In_Chained_Fact p)
      | eval' SU.Is_In_Nth_Subgoal      [Path p, Number n]  = EPT.eval trm pst (EPT.Is_In_Nth_Subgoal (p, n))
      | eval' SU.Is_In_Nth_Chained_Fact [Path p, Number n]  = EPT.eval trm pst (EPT.Is_In_Nth_Chained_Fact (p, n))
      (*Eval_Print*)
      | eval' SU.Are_Same_Prints [Print p1, Print p2] = EPR.eval (EPR.Are_Same_Prints (p1, p2))
      (*Eval_Number*)
      | eval' SU.Are_Same_Number [Number numb1,  Number numb2] = ENMB.eval (ENMB.Are_Same_Number (numb1, numb2))
      | eval' SU.Is_Less_Than    [Number numb1,  Number numb2] = ENMB.eval (ENMB.Is_Less_Than    (numb1, numb2))
      (*Eval_Induct_Argument*)
      | eval' SU.Is_Nth_Induct    [Print p, Number n] = EIA.eval (EIA.Is_Nth_Induct (p, n))    induct_args
      | eval' SU.Is_Nth_Arbitrary [Print p, Number n] = EIA.eval (EIA.Is_Nth_Arbitrary (p, n)) induct_args
      | eval' SU.Is_Induct        [Print p]           = EIA.eval (EIA.Is_Induct p)             induct_args
      | eval' SU.Is_Arbitrary     [Print p]           = EIA.eval (EIA.Is_Arbitrary p)          induct_args
      | eval' SU.Is_Rule          [Print p]           = EIA.eval (EIA.Is_Rule p)               induct_args
      | eval' _ _ = error "eval' in From_Path_to_Parameter.ML failed!"
  in
    eval' assert parameters: Eval_Bool.assert
  end;

end;