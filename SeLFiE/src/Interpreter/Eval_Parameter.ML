(*  Title:      PSL/SeLFiE/src/Eval_Parameter.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** signature EVAL_PARAMETER ***)
signature EVAL_PARAMETER =
sig

datatype non_path_literal =
  Bool    of bool
| Print   of string
| Number  of int
| Command of Pattern.command;

datatype literal =
  Outer_Path of outer_path
| Inner_Path of UN.inner_path
| Non_Path   of non_path_literal;

type literals = literal list;

val eval: term -> Proof.state -> SeLFiE_Util.induct_arguments -> SeLFiE_Util.atomic_assert -> literals -> Eval_Bool.assert;

end;

(*** structure Eval_Parameter ***)
structure Eval_Parameter: EVAL_PARAMETER =
struct

structure PA   = Path_Assert;
structure EPT  = Eval_Path;
structure EPR  = Eval_Print;
structure ENMB = Eval_Number;
structure SU   = SeLFiE_Util;

datatype non_path_literal =
  Bool    of bool
| Print   of string
| Number  of int
| Command of Pattern.command;

datatype literal =
  Outer_Path of outer_path
| Inner_Path of UN.inner_path
| Non_Path   of non_path_literal;

type literals = literal list;

fun eval trm pst induct_args assert literals =
  let
    val ctxt = Proof.context_of pst;
    fun
      (*Eval_Node (Outer)*)
        eval' SU.Is_Cnst   [Outer_Path p] = EPT.eval trm pst (EPT.Outer_Assert (PA.Is_Cnst   p))
      | eval' SU.Is_Free   [Outer_Path p] = EPT.eval trm pst (EPT.Outer_Assert (PA.Is_Free   p))
      | eval' SU.Is_Var    [Outer_Path p] = EPT.eval trm pst (EPT.Outer_Assert (PA.Is_Var    p))
      | eval' SU.Is_Bound  [Outer_Path p] = EPT.eval trm pst (EPT.Outer_Assert (PA.Is_Bound  p))
      | eval' SU.Is_Lambda [Outer_Path p] = EPT.eval trm pst (EPT.Outer_Assert (PA.Is_Lambda p))
      | eval' SU.Is_App    [Outer_Path p] = EPT.eval trm pst (EPT.Outer_Assert (PA.Is_App    p))
      | eval' SU.Is_Defined_With [Outer_Path p, Non_Path (Command cmd)] = EPT.eval trm pst (EPT.Outer_Assert (PA.Is_Defined_With (p, cmd)))
      (*Eval_Node (Inner)*)
      | eval' SU.Is_Cnst   [Inner_Path p] = EPT.eval trm pst (EPT.Inner_Assert (PA.Is_Cnst   p))
      | eval' SU.Is_Free   [Inner_Path p] = EPT.eval trm pst (EPT.Inner_Assert (PA.Is_Free   p))
      | eval' SU.Is_Var    [Inner_Path p] = EPT.eval trm pst (EPT.Inner_Assert (PA.Is_Var    p))
      | eval' SU.Is_Bound  [Inner_Path p] = EPT.eval trm pst (EPT.Inner_Assert (PA.Is_Bound  p))
      | eval' SU.Is_Lambda [Inner_Path p] = EPT.eval trm pst (EPT.Inner_Assert (PA.Is_Lambda p))
      | eval' SU.Is_App    [Inner_Path p] = EPT.eval trm pst (EPT.Inner_Assert (PA.Is_App    p))
      | eval' SU.Is_Defined_With [Inner_Path p, Non_Path (Command cmd)] = EPT.eval trm pst (EPT.Inner_Assert (PA.Is_Defined_With (p, cmd)))
      (*Eval_Unode (Outer)*)
      | eval' SU.Has_Same_Prnt_As       [Outer_Path p1, Outer_Path p2]       = EPT.eval trm pst (EPT.Outer_Assert (PA.Has_Same_Prnt_As       (p1, p2)))
      | eval' SU.Is_In_Trm_Prnt         [Outer_Path p1, Outer_Path p2]       = EPT.eval trm pst (EPT.Outer_Assert (PA.Is_In_Trm_Prnt         (p1, p2)))
      | eval' SU.Is_Deeper_Than         [Outer_Path p1, Outer_Path p2]       = EPT.eval trm pst (EPT.Outer_Assert (PA.Is_Deeper_Than         (p1, p2)))
      | eval' SU.Is_Shallower_Than      [Outer_Path p1, Outer_Path p2]       = EPT.eval trm pst (EPT.Outer_Assert (PA.Is_Shallower_Than      (p1, p2)))
      | eval' SU.Is_Path_Above          [Outer_Path p1, Outer_Path p2]       = EPT.eval trm pst (EPT.Outer_Assert (PA.Is_Path_Above          (p1, p2)))
      | eval' SU.Is_Same_Path_As        [Outer_Path p1, Outer_Path p2]       = EPT.eval trm pst (EPT.Outer_Assert (PA.Is_Same_Path_As        (p1, p2)))
      | eval' SU.Is_Nth_Child           [Outer_Path p,  Non_Path (Number n)] = EPT.eval trm pst (EPT.Outer_Assert (PA.Is_Nth_Child           (p,  n )))
      | eval' SU.Is_N_Plus_One_th_Child [Outer_Path p,  Non_Path (Number n)] = EPT.eval trm pst (EPT.Outer_Assert (PA.Is_N_Plus_One_th_Child (p,  n )))
      (*Eval_Unode (Inner)*)
      | eval' SU.Has_Same_Prnt_As       [Inner_Path p1, Inner_Path p2]       = EPT.eval trm pst (EPT.Inner_Assert (PA.Has_Same_Prnt_As       (p1, p2)))
      | eval' SU.Is_In_Trm_Prnt         [Inner_Path p1, Inner_Path p2]       = EPT.eval trm pst (EPT.Inner_Assert (PA.Is_In_Trm_Prnt         (p1, p2)))
      | eval' SU.Is_Deeper_Than         [Inner_Path p1, Inner_Path p2]       = EPT.eval trm pst (EPT.Inner_Assert (PA.Is_Deeper_Than         (p1, p2)))
      | eval' SU.Is_Shallower_Than      [Inner_Path p1, Inner_Path p2]       = EPT.eval trm pst (EPT.Inner_Assert (PA.Is_Shallower_Than      (p1, p2)))
      | eval' SU.Is_Path_Above          [Inner_Path p1, Inner_Path p2]       = EPT.eval trm pst (EPT.Inner_Assert (PA.Is_Path_Above          (p1, p2)))
      | eval' SU.Is_Same_Path_As        [Inner_Path p1, Inner_Path p2]       = EPT.eval trm pst (EPT.Inner_Assert (PA.Is_Same_Path_As        (p1, p2)))
      | eval' SU.Is_Nth_Child           [Inner_Path p,  Non_Path (Number n)] = EPT.eval trm pst (EPT.Inner_Assert (PA.Is_Nth_Child           (p,  n )))
      | eval' SU.Is_N_Plus_One_th_Child [Inner_Path p,  Non_Path (Number n)] = EPT.eval trm pst (EPT.Inner_Assert (PA.Is_N_Plus_One_th_Child (p,  n)))
      (*Eval_Path (Outer)*)
      | eval' SU.Unode_Has_Print        [Outer_Path p, Non_Path (Print str)] = EPT.eval trm pst (EPT.Outer_Assert (PA.Unode_Has_Print        (p, str)))
      | eval' SU.Is_In_Subgoal          [Outer_Path p]                       = EPT.eval trm pst (EPT.Outer_Assert (PA.Is_In_Subgoal           p    ))
      | eval' SU.Is_In_Chained_Fact     [Outer_Path p]                       = EPT.eval trm pst (EPT.Outer_Assert (PA.Is_In_Chained_Fact      p    ))
      | eval' SU.Is_In_Nth_Subgoal      [Outer_Path p, Non_Path (Number n)]  = EPT.eval trm pst (EPT.Outer_Assert (PA.Is_In_Nth_Subgoal      (p, n)))
      | eval' SU.Is_In_Nth_Chained_Fact [Outer_Path p, Non_Path (Number n)]  = EPT.eval trm pst (EPT.Outer_Assert (PA.Is_In_Nth_Chained_Fact (p, n)))
      (*Eval_Path (Inner)*)
      | eval' SU.Unode_Has_Print        [Inner_Path p, Non_Path (Print str)] = EPT.eval trm pst (EPT.Inner_Assert (PA.Unode_Has_Print        (p, str)))
      | eval' SU.Is_In_Subgoal          [Inner_Path p]                       = EPT.eval trm pst (EPT.Inner_Assert (PA.Is_In_Subgoal           p    ))
      | eval' SU.Is_In_Chained_Fact     [Inner_Path p]                       = EPT.eval trm pst (EPT.Inner_Assert (PA.Is_In_Chained_Fact      p    ))
      | eval' SU.Is_In_Nth_Subgoal      [Inner_Path p, Non_Path (Number n)]  = EPT.eval trm pst (EPT.Inner_Assert (PA.Is_In_Nth_Subgoal      (p, n)))
      | eval' SU.Is_In_Nth_Chained_Fact [Inner_Path p, Non_Path (Number n)]  = EPT.eval trm pst (EPT.Inner_Assert (PA.Is_In_Nth_Chained_Fact (p, n)))
      (*Eval_Print*)
      | eval' SU.Are_Same_Prints  [Non_Path (Print p1), Non_Path (Print p2)] = EPR.eval (EPR.Are_Same_Prints (p1, p2)) induct_args ctxt
      | eval' SU.Is_Nth_Induct    [Non_Path (Print p),  Non_Path (Number n)] = EPR.eval (EPR.Is_Nth_Induct (p, n))     induct_args ctxt
      | eval' SU.Is_Nth_Arbitrary [Non_Path (Print p),  Non_Path (Number n)] = EPR.eval (EPR.Is_Nth_Arbitrary (p, n))  induct_args ctxt
      | eval' SU.Is_Induct        [Non_Path (Print p)]                       = EPR.eval (EPR.Is_Induct p)              induct_args ctxt
      | eval' SU.Is_Arbitrary     [Non_Path (Print p)]                       = EPR.eval (EPR.Is_Arbitrary p)           induct_args ctxt
      | eval' SU.Is_Rule          [Non_Path (Print p)]                       = EPR.eval (EPR.Is_Rule p)                induct_args ctxt
      | eval' SU.Is_Rule_Of       [Non_Path (Print p1), Non_Path (Print p2)] = EPR.eval (EPR.Is_Rule_Of (p1, p2))      induct_args ctxt
      (*Eval_Number*)
      | eval' SU.Are_Same_Number [Non_Path (Number numb1), Non_Path (Number numb2)] = ENMB.eval (ENMB.Are_Same_Number (numb1, numb2))
      | eval' SU.Is_Less_Than    [Non_Path (Number numb1), Non_Path (Number numb2)] = ENMB.eval (ENMB.Is_Less_Than    (numb1, numb2))
      (*debug*)
      | eval' SU.Debug_Non_Path_Literal [Non_Path (Bool    b)] = (tracing ("Debug Bool "   ^ (if b then "true" else "false"));  Eval_Bool.True)
      | eval' SU.Debug_Non_Path_Literal [Non_Path (Print   p)] = (tracing ("Debug Print "  ^ p                              );  Eval_Bool.True)
      | eval' SU.Debug_Non_Path_Literal [Non_Path (Number  n)] = (tracing ("Debug Number " ^ Int.toString n                 );  Eval_Bool.True)
      | eval' SU.Debug_Non_Path_Literal [Non_Path (Command c)] = (tracing ("Debug Number " ^ Pattern.print_command c        );  Eval_Bool.True)
      | eval' SU.Debug_Print_Unode      [Outer_Path p]         = (EPT.eval trm pst (EPT.Outer_Assert (PA.Debug_Print_Unode p)); Eval_Bool.True)
      | eval' SU.Debug_Print_Unode      [Inner_Path p]         = (EPT.eval trm pst (EPT.Inner_Assert (PA.Debug_Print_Unode p)); Eval_Bool.True)
      | eval' assert _ = error ("- eval' in Eval_Parameter.ML failed at " ^ SU.print_atomic_assert assert);
  in
    eval' assert literals: Eval_Bool.assert
  end;

end;