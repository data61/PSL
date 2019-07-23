(*  Title:      PSL/SeLFeE/src/Eval_Parameters_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Parameters: EVAL_PARAMETERS =
struct           

structure EFP = Eval_Full_Path;

type connective = Eval_Connective.assert;
type print      = LiFtEr_Util.print;

datatype parameter = Connective of connective | Full_Path of full_path | Print of print | String of string(*redundant?*);
type     parameters = parameter list;

fun de_Connective (Connective c) = c
  | de_Connective  _             = error "de_Connective in Eval_Parameters_Struct failed."

datatype assert =
(*Eval_Connective*)
  True
| False
| Not
| And
| Or
| Nor
| Imply
| Ands
| Ors
(*Eval_Node_Core*)
| Is_Cnst
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
| Fpnode_Has_Print;

type full_path_to_fpunode_table = Full_Path_To_Fpunode.full_path_to_fpunode_table;

fun
  (*Eval_Connective*)
    unlist True  []                                 = EFP.True
  | unlist False []                                 = EFP.False
  | unlist Not   [Connective assert]                = EFP.Not    assert
  | unlist And   [Connective ass1, Connective ass2] = EFP.And   (ass1, ass2)
  | unlist Or    [Connective ass1, Connective ass2] = EFP.Or    (ass1, ass2)
  | unlist Nor   [Connective ass1, Connective ass2] = EFP.Nor   (ass1, ass2)
  | unlist Imply [Connective ass1, Connective ass2] = EFP.Imply (ass1, ass2)
  | unlist Ands  ands                               = EFP.Ands  (map de_Connective ands)
  | unlist Ors   ors                                = EFP.Ors   (map de_Connective ors )
  (*Eval_Node_Core*)
  | unlist Is_Cnst   [Full_Path fp] = EFP.Is_Cnst   fp
  | unlist Is_Free   [Full_Path fp] = EFP.Is_Free   fp
  | unlist Is_Var    [Full_Path fp] = EFP.Is_Var    fp
  | unlist Is_Bound  [Full_Path fp] = EFP.Is_Bound  fp
  | unlist Is_Lambda [Full_Path fp] = EFP.Is_Lambda fp
  | unlist Is_App    [Full_Path fp] = EFP.Is_App    fp
  (*Eval_Node_Sugar*)
  | unlist Is_Atom    [Full_Path fp] = EFP.Is_Atom    fp
  | unlist Is_Compund [Full_Path fp] = EFP.Is_Compund fp
  (*Eval_Unode_Core*)
  | unlist Has_Same_Prnt_As  [Full_Path fp1, Full_Path fp2] = EFP.Has_Same_Prnt_As  (fp1, fp2)
  | unlist Is_In_Trm_Prnt    [Full_Path fp1, Full_Path fp2] = EFP.Is_In_Trm_Prnt    (fp1, fp2)
  | unlist Is_Deeper_Than    [Full_Path fp1, Full_Path fp2] = EFP.Is_Deeper_Than    (fp1, fp2)
  | unlist Is_Shallower_Than [Full_Path fp1, Full_Path fp2] = EFP.Is_Shallower_Than (fp1, fp2)
  | unlist Is_Path_Above     [Full_Path fp1, Full_Path fp2] = EFP.Is_Path_Above     (fp1, fp2)
  | unlist Is_Same_Path_As   [Full_Path fp1, Full_Path fp2] = EFP.Is_Same_Path_As   (fp1, fp2)
  (*Eval_Unode_Sugar*)
  | unlist Is_As_Deep_As [Full_Path fp1, Full_Path fp2] = EFP.Is_As_Deep_As (fp1, fp2)
  | unlist Is_Path_Below [Full_Path fp1, Full_Path fp2] = EFP.Is_Path_Below (fp1, fp2)
  (*Eval_Fpunode_Core*)
  | unlist Is_In_Same_Location_As [Full_Path fp1, Full_Path fp2] = EFP.Is_In_Same_Location_As (fp1, fp2)
  | unlist Is_In_Chained          [Full_Path fp]                 = EFP.Is_In_Chained  fp
  | unlist Is_In_Fst_Subg         [Full_Path fp]                 = EFP.Is_In_Fst_Subg fp
  (*Eval_Fpunode_Sugar*)
  | unlist Is_Above       [Full_Path fp1, Full_Path fp2] = EFP.Is_Above       (fp1, fp2)
  | unlist Is_Below       [Full_Path fp1, Full_Path fp2] = EFP.Is_Below       (fp1, fp2)
  | unlist Is_Same_Occ_As [Full_Path fp1, Full_Path fp2] = EFP.Is_Same_Occ_As (fp1, fp2)
  (*Eval_Print_Core*)
  | unlist Are_Same_Prints [Print p1, Print p2] = EFP.Are_Same_Prints (p1, p2)
  | unlist Is_Printed_As   [Print p,  String s] = EFP.Is_Printed_As   (p, s)
  (*Eval_Print_Sugar*)
  | unlist Are_Different_Prints [Print p1, Print p2]     = EFP.Are_Different_Prints (p1, p2)
  | unlist Fpnode_Has_Print     [Full_Path fp, Print pr] = EFP.Fpnode_Has_Print     (fp, pr)
  | unlist _ _ = error "unlist in Eval_Parameters_Struct.ML failed!"

fun eval fp_to_fpun_table assert parameters =
  let
    val assert_full_path = unlist assert parameters: EFP.assert;
  in
    EFP.eval fp_to_fpun_table assert_full_path
  end;

end;