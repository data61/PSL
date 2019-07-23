(*  Title:      PSL/SeLFeE/src/Eval_Parameters_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_PARAMETERS =
sig

type connective = Eval_Connective.assert;
type print      = LiFtEr_Util.print;

datatype parameter = Connective of connective | Full_Path of full_path | Print of print | String of string(*redundant?*);
type     parameters = parameter list;

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

val eval: full_path_to_fpunode_table -> assert -> parameters -> Eval_Connective.assert;

end;