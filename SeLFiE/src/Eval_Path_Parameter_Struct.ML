(*  Title:      PSL/SeLFeE/src/Eval_Path_Parameters_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Path_Parameter: EVAL_PARAMETER =
struct           

type path    = LiFtEr_Util.path;
type print   = LiFtEr_Util.print;
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
(*Eval_Node_Core*)
  Is_Cnst
| Is_Free
| Is_Var
| Is_Bound
| Is_Lambda
| Is_App
(*Eval_Node_Sugar*)
| Is_Atom
| Is_Compund
(*Eval_Unode_Core*)
| Has_Same_Prnt_As
| Is_In_Trm_Prnt
| Is_Deeper_Than
| Is_Shallower_Than
| Is_Path_Above
| Is_Same_Path_As
(*Eval_Unode_Sugar*)
| Is_As_Deep_As
| Is_Path_Below
(*Eval_Print_Core*)
| Are_Same_Prints
| Is_Printed_As
(*Eval_Print_Sugar*)
| Are_Different_Prints
| Unode_Has_Print
(*Eval_Number*)
| Are_Same_Number
| Is_Less_Than
| Is_Int;

type path_to_unode_table = Path_To_Unode.path_to_unode_table;

val trm_n_pst_to_path_to_unode_table = undefined: term -> Proof.state -> path_to_unode_table;(*TODO*)

structure EP  = Eval_Path;
structure EPC = Eval_Print_Core;
structure EPS = Eval_Print_Sugar;
structure EN  = Eval_Number;

fun eval trm pst assert parameters =
  let
    val path_to_unode_table = trm_n_pst_to_path_to_unode_table trm pst;
    fun
      (*Eval_Node_Core*)
        eval' Is_Cnst   [Path p] = EP.eval path_to_unode_table (EP.Is_Cnst   p)
      | eval' Is_Free   [Path p] = EP.eval path_to_unode_table (EP.Is_Free   p)
      | eval' Is_Var    [Path p] = EP.eval path_to_unode_table (EP.Is_Var    p)
      | eval' Is_Bound  [Path p] = EP.eval path_to_unode_table (EP.Is_Bound  p)
      | eval' Is_Lambda [Path p] = EP.eval path_to_unode_table (EP.Is_Lambda p)
      | eval' Is_App    [Path p] = EP.eval path_to_unode_table (EP.Is_App    p)
      (*Eval_Node_Sugar*)
      | eval' Is_Atom    [Path p] = EP.eval path_to_unode_table (EP.Is_Atom    p)
      | eval' Is_Compund [Path p] = EP.eval path_to_unode_table (EP.Is_Compund p)
      (*Eval_Unode_Core*)
      | eval' Has_Same_Prnt_As  [Path p1, Path p2] = EP.eval path_to_unode_table (EP.Has_Same_Prnt_As  (p1, p2))
      | eval' Is_In_Trm_Prnt    [Path p1, Path p2] = EP.eval path_to_unode_table (EP.Is_In_Trm_Prnt    (p1, p2))
      | eval' Is_Deeper_Than    [Path p1, Path p2] = EP.eval path_to_unode_table (EP.Is_Deeper_Than    (p1, p2))
      | eval' Is_Shallower_Than [Path p1, Path p2] = EP.eval path_to_unode_table (EP.Is_Shallower_Than (p1, p2))
      | eval' Is_Path_Above     [Path p1, Path p2] = EP.eval path_to_unode_table (EP.Is_Path_Above     (p1, p2))
      | eval' Is_Same_Path_As   [Path p1, Path p2] = EP.eval path_to_unode_table (EP.Is_Same_Path_As   (p1, p2))
      (*Eval_Unode_Sugar*)
      | eval' Is_As_Deep_As [Path p1, Path p2] = EP.eval path_to_unode_table (EP.Is_As_Deep_As (p1, p2))
      | eval' Is_Path_Below [Path p1, Path p2] = EP.eval path_to_unode_table (EP.Is_Path_Below (p1, p2))
     (*Eval_Print_Core*)
      | eval' Are_Same_Prints [Print p1, Print p2] = EPC.eval (EPC.Are_Same_Prints (p1, p2))
      | eval' Is_Printed_As   [Print p,  String s] = EPC.eval (EPC.Is_Printed_As   (p, s))
      (*Eval_Print_Sugar*)
      | eval' Are_Different_Prints [Print p1, Print p2] = EPS.eval (EPS.Are_Different_Prints (p1, p2))
      | eval' Unode_Has_Print      [Path  p,  Print pr] = EP.eval path_to_unode_table (EP.Unode_Has_Print (p, pr))
      (*Eval_Number*)
      | eval' Are_Same_Number [Number numb1,  Number numb2] = EN.eval (EN.Are_Same_Number (numb1, numb2))
      | eval' Is_Less_Than    [Number numb1,  Number numb2] = EN.eval (EN.Is_Less_Than    (numb1, numb2))
      | eval' Is_Int          [Number numb,   Int    int  ] = EN.eval (EN.Is_Int          (numb,    int))
      | eval' _ _ = error "eval' in Eval_Parameters_Struct.ML failed!"
  in
    eval' assert parameters: Eval_Connective.assert
  end;

end;