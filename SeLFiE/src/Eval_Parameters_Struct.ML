(*  Title:      PSL/SeLFeE/src/Eval_Parameters_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Parameters: EVAL_PARAMETERS =
struct           

structure EC  = Eval_Connective;
structure EPC = Eval_Print_Core;
structure EPS = Eval_Print_Sugar;
structure EFP = Eval_Full_Path;
structure EN  = Eval_Number;
structure EP  = Eval_Primitive;

type connective = Eval_Connective.assert;
type print      = LiFtEr_Util.print;
type number     = Eval_Number.number;

datatype parameter =
  Full_Path of full_path
| Print     of print
| String    of string(*redundant?*)
| Number    of Eval_Number.number
| Int       of int;

type parameters = parameter list;

datatype assert =
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
(*Eval_Fpunode_Core*)
| Is_In_Same_Location_As
| Is_In_Chained
| Is_In_Fst_Subg
(*Eval_Fpunode_Sugar*)
| Is_Above
| Is_Below
| Is_Same_Occ_As
(*Eval_Print_Core*)
| Are_Same_Prints
| Is_Printed_As
(*Eval_Print_Sugar*)
| Are_Different_Prints
| Fpnode_Has_Print
(*Eval_Number*)
| Are_Same_Number
| Is_Less_Than
| Is_Int
(*Others*)
| Is_Nth_Arg_Of;

type full_path_to_fpunode_table = Full_Path_To_Fpunode.full_path_to_fpunode_table;


fun eval fp_to_fpun_table assert parameters =
  let
    fun
      (*Eval_Node_Core*)
        eval' Is_Cnst   [Full_Path fp] = EFP.eval fp_to_fpun_table (EFP.Is_Cnst   fp)
      | eval' Is_Free   [Full_Path fp] = EFP.eval fp_to_fpun_table (EFP.Is_Free   fp)
      | eval' Is_Var    [Full_Path fp] = EFP.eval fp_to_fpun_table (EFP.Is_Var    fp)
      | eval' Is_Bound  [Full_Path fp] = EFP.eval fp_to_fpun_table (EFP.Is_Bound  fp)
      | eval' Is_Lambda [Full_Path fp] = EFP.eval fp_to_fpun_table (EFP.Is_Lambda fp)
      | eval' Is_App    [Full_Path fp] = EFP.eval fp_to_fpun_table (EFP.Is_App    fp)
      (*Eval_Node_Sugar*)
      | eval' Is_Atom    [Full_Path fp] = EFP.eval fp_to_fpun_table (EFP.Is_Atom    fp)
      | eval' Is_Compund [Full_Path fp] = EFP.eval fp_to_fpun_table (EFP.Is_Compund fp)
      (*Eval_Unode_Core*)
      | eval' Has_Same_Prnt_As  [Full_Path fp1, Full_Path fp2] = EFP.eval fp_to_fpun_table (EFP.Has_Same_Prnt_As  (fp1, fp2))
      | eval' Is_In_Trm_Prnt    [Full_Path fp1, Full_Path fp2] = EFP.eval fp_to_fpun_table (EFP.Is_In_Trm_Prnt    (fp1, fp2))
      | eval' Is_Deeper_Than    [Full_Path fp1, Full_Path fp2] = EFP.eval fp_to_fpun_table (EFP.Is_Deeper_Than    (fp1, fp2))
      | eval' Is_Shallower_Than [Full_Path fp1, Full_Path fp2] = EFP.eval fp_to_fpun_table (EFP.Is_Shallower_Than (fp1, fp2))
      | eval' Is_Path_Above     [Full_Path fp1, Full_Path fp2] = EFP.eval fp_to_fpun_table (EFP.Is_Path_Above     (fp1, fp2))
      | eval' Is_Same_Path_As   [Full_Path fp1, Full_Path fp2] = EFP.eval fp_to_fpun_table (EFP.Is_Same_Path_As   (fp1, fp2))
      (*Eval_Unode_Sugar*)
      | eval' Is_As_Deep_As [Full_Path fp1, Full_Path fp2] = EFP.eval fp_to_fpun_table (EFP.Is_As_Deep_As (fp1, fp2))
      | eval' Is_Path_Below [Full_Path fp1, Full_Path fp2] = EFP.eval fp_to_fpun_table (EFP.Is_Path_Below (fp1, fp2))
      (*Eval_Fpunode_Core*)
      | eval' Is_In_Same_Location_As [Full_Path fp1, Full_Path fp2] = EFP.eval fp_to_fpun_table (EFP.Is_In_Same_Location_As (fp1, fp2))
      | eval' Is_In_Chained          [Full_Path fp]                 = EFP.eval fp_to_fpun_table (EFP.Is_In_Chained  fp)
      | eval' Is_In_Fst_Subg         [Full_Path fp]                 = EFP.eval fp_to_fpun_table (EFP.Is_In_Fst_Subg fp)
      (*Eval_Fpunode_Sugar*)
      | eval' Is_Above       [Full_Path fp1, Full_Path fp2] = EFP.eval fp_to_fpun_table (EFP.Is_Above       (fp1, fp2))
      | eval' Is_Below       [Full_Path fp1, Full_Path fp2] = EFP.eval fp_to_fpun_table (EFP.Is_Below       (fp1, fp2))
      | eval' Is_Same_Occ_As [Full_Path fp1, Full_Path fp2] = EFP.eval fp_to_fpun_table (EFP.Is_Same_Occ_As (fp1, fp2))
      (*Eval_Print_Core*)
      | eval' Are_Same_Prints [Print p1, Print p2] = EPC.eval (EPC.Are_Same_Prints (p1, p2))
      | eval' Is_Printed_As   [Print p,  String s] = EPC.eval (EPC.Is_Printed_As   (p, s))
      (*Eval_Print_Sugar*)
      | eval' Are_Different_Prints [Print p1, Print p2]     = EPS.eval (EPS.Are_Different_Prints (p1, p2))
      | eval' Fpnode_Has_Print     [Full_Path fp, Print pr] = EFP.eval fp_to_fpun_table (EFP.Fpnode_Has_Print     (fp, pr))
      (*Eval_Number*)
      | eval' Are_Same_Number [Number numb1,  Number numb2]            = EN.eval (EN.Are_Same_Number (numb1, numb2))
      | eval' Is_Less_Than    [Number numb1,  Number numb2]            = EN.eval (EN.Is_Less_Than    (numb1, numb2))
      | eval' Is_Int          [Number numb,   Int    int  ]            = EN.eval (EN.Is_Int          (numb,    int))
      (*Others*)
      | eval' Is_Nth_Arg_Of   [Full_Path fp1, Number n, Full_Path fp2] = EP.eval fp_to_fpun_table (EP.Is_Nth_Arg_Of (fp1, n, fp2))
      | eval' _ _ = error "eval' in Eval_Parameters_Struct.ML failed!"
  in
    eval' assert parameters: Eval_Connective.assert
  end;

end;