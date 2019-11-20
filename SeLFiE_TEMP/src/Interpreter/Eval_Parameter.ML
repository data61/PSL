(*  Title:      PSL/SeLFiE/src/Eval_Parameter.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** EVAL_PARAMETER ***)
signature EVAL_PARAMETER =
sig

type path(*    = SeLFiE_Util.inner_path*);
type print   = SeLFiE_Util.print;
type number  = Eval_Number.number;
type command = Pattern.command;

datatype parameter =
  Path      of path
| Print     of print
| String    of string(*redundant?*)
| Number    of number
| Int       of int
| Command   of command;

type parameters = parameter list;

type parameter_assert;

val eval: term -> Proof.state -> parameter_assert -> parameters -> Eval_Bool.assert;

end;

(*** Eval_Inner_Parameter ***)
structure Eval_Inner_Parameter: EVAL_PARAMETER =
struct           

type path    = SeLFiE_Util.inner_path;
type print   = SeLFiE_Util.print;
type number  = Eval_Number.number;
type command = Pattern.command;

datatype parameter =
  Path      of path
| Print     of print
| String    of string(*redundant?*)
| Number    of number
| Int       of int
| Command   of command;

type parameters = parameter list;

datatype parameter_assert =
(*Eval_Node*)
  Is_Cnst
| Is_Free
| Is_Var
| Is_Bound
| Is_Lambda
| Is_App
(*Eval_Unode*)
| Has_Same_Prnt_As
| Is_In_Trm_Prnt
| Is_Deeper_Than
| Is_Shallower_Than
| Is_Path_Above
| Is_Same_Path_As
(*Eval_Print*)
| Are_Same_Prints
| Is_Printed_As
(*Eval_Print_Sugar*)
(*TODO:| Unode_Has_Print*)
(*Eval_Number*)
| Are_Same_Number
| Is_Less_Than
| Is_Int;

structure EIPT = Eval_Inner_Path;
structure EIPR = Eval_Inner_Print;
structure ENMB = Eval_Number;

fun eval trm pst assert parameters =
  let

    fun
      (*Eval_Node*)
        eval' Is_Cnst   [Path p] = EIPT.eval trm pst (EIPT.Is_Cnst   p)
      | eval' Is_Free   [Path p] = EIPT.eval trm pst (EIPT.Is_Free   p)
      | eval' Is_Var    [Path p] = EIPT.eval trm pst (EIPT.Is_Var    p)
      | eval' Is_Bound  [Path p] = EIPT.eval trm pst (EIPT.Is_Bound  p)
      | eval' Is_Lambda [Path p] = EIPT.eval trm pst (EIPT.Is_Lambda p)
      | eval' Is_App    [Path p] = EIPT.eval trm pst (EIPT.Is_App    p)
      (*Eval_Unode*)
      | eval' Has_Same_Prnt_As  [Path p1, Path p2] = EIPT.eval trm pst (EIPT.Has_Same_Prnt_As  (p1, p2))
      | eval' Is_In_Trm_Prnt    [Path p1, Path p2] = EIPT.eval trm pst (EIPT.Is_In_Trm_Prnt    (p1, p2))
      | eval' Is_Deeper_Than    [Path p1, Path p2] = EIPT.eval trm pst (EIPT.Is_Deeper_Than    (p1, p2))
      | eval' Is_Shallower_Than [Path p1, Path p2] = EIPT.eval trm pst (EIPT.Is_Shallower_Than (p1, p2))
      | eval' Is_Path_Above     [Path p1, Path p2] = EIPT.eval trm pst (EIPT.Is_Path_Above     (p1, p2))
      | eval' Is_Same_Path_As   [Path p1, Path p2] = EIPT.eval trm pst (EIPT.Is_Same_Path_As   (p1, p2))
     (*Eval_Print*)
      | eval' Are_Same_Prints [Print p1, Print p2] = EIPR.eval (EIPR.Are_Same_Prints (p1, p2))
      | eval' Is_Printed_As   [Print p,  String s] = EIPR.eval (EIPR.Is_Printed_As   (p, s))
      (*Eval_Number*)
      | eval' Are_Same_Number [Number numb1,  Number numb2] = ENMB.eval (ENMB.Are_Same_Number (numb1, numb2))
      | eval' Is_Less_Than    [Number numb1,  Number numb2] = ENMB.eval (ENMB.Is_Less_Than    (numb1, numb2))
      | eval' Is_Int          [Number numb,   Int    int  ] = ENMB.eval (ENMB.Is_Int          (numb,    int))
      | eval' _ _ = error "eval' in Eval_Parameters_Struct.ML failed!"
  in
    eval' assert parameters: Eval_Bool.assert
  end;

end;

(*** Eval_Outer_Parameter ***) (*TODO: This is still Eval_Inner_Parameter.*)
structure Eval_Outer_Parameter: EVAL_PARAMETER =
struct           

type path    = SeLFiE_Util.inner_path;
type print   = SeLFiE_Util.print;
type number  = Eval_Number.number;
type command = Pattern.command;

datatype parameter =
  Path      of path
| Print     of print
| String    of string(*redundant?*)
| Number    of number
| Int       of int
| Command   of command;

type parameters = parameter list;

datatype parameter_assert =
(*Eval_Node*)
  Is_Cnst
| Is_Free
| Is_Var
| Is_Bound
| Is_Lambda
| Is_App
(*Eval_Unode*)
| Has_Same_Prnt_As
| Is_In_Trm_Prnt
| Is_Deeper_Than
| Is_Shallower_Than
| Is_Path_Above
| Is_Same_Path_As
(*Eval_Print*)
| Are_Same_Prints
| Is_Printed_As
(*Eval_Print_Sugar*)
(*TODO:| Unode_Has_Print*)
(*Eval_Number*)
| Are_Same_Number
| Is_Less_Than
| Is_Int;

structure EIPT = Eval_Inner_Path;
structure EIPR = Eval_Inner_Print;
structure ENMB = Eval_Number;

fun eval trm pst assert parameters =
  let
    fun
      (*Eval_Node*)
        eval' Is_Cnst   [Path p] = EIPT.eval trm pst (EIPT.Is_Cnst   p)
      | eval' Is_Free   [Path p] = EIPT.eval trm pst (EIPT.Is_Free   p)
      | eval' Is_Var    [Path p] = EIPT.eval trm pst (EIPT.Is_Var    p)
      | eval' Is_Bound  [Path p] = EIPT.eval trm pst (EIPT.Is_Bound  p)
      | eval' Is_Lambda [Path p] = EIPT.eval trm pst (EIPT.Is_Lambda p)
      | eval' Is_App    [Path p] = EIPT.eval trm pst (EIPT.Is_App    p)
      (*Eval_Unode*)
      | eval' Has_Same_Prnt_As  [Path p1, Path p2] = EIPT.eval trm pst (EIPT.Has_Same_Prnt_As  (p1, p2))
      | eval' Is_In_Trm_Prnt    [Path p1, Path p2] = EIPT.eval trm pst (EIPT.Is_In_Trm_Prnt    (p1, p2))
      | eval' Is_Deeper_Than    [Path p1, Path p2] = EIPT.eval trm pst (EIPT.Is_Deeper_Than    (p1, p2))
      | eval' Is_Shallower_Than [Path p1, Path p2] = EIPT.eval trm pst (EIPT.Is_Shallower_Than (p1, p2))
      | eval' Is_Path_Above     [Path p1, Path p2] = EIPT.eval trm pst (EIPT.Is_Path_Above     (p1, p2))
      | eval' Is_Same_Path_As   [Path p1, Path p2] = EIPT.eval trm pst (EIPT.Is_Same_Path_As   (p1, p2))
     (*Eval_Print*)
      | eval' Are_Same_Prints [Print p1, Print p2] = EIPR.eval (EIPR.Are_Same_Prints (p1, p2))
      | eval' Is_Printed_As   [Print p,  String s] = EIPR.eval (EIPR.Is_Printed_As   (p, s))
      (*Eval_Number*)
      | eval' Are_Same_Number [Number numb1,  Number numb2] = ENMB.eval (ENMB.Are_Same_Number (numb1, numb2))
      | eval' Is_Less_Than    [Number numb1,  Number numb2] = ENMB.eval (ENMB.Is_Less_Than    (numb1, numb2))
      | eval' Is_Int          [Number numb,   Int    int  ] = ENMB.eval (ENMB.Is_Int          (numb,    int))
      | eval' _ _ = error "eval' in Eval_Parameters_Struct.ML failed!"
  in
    eval' assert parameters: Eval_Bool.assert
  end;

end;