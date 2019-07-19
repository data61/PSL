(*  Title:      PSL/SeLFeE/src/Eval_Full_Path_Sig.thy
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_FULL_PATH =
sig

type connective = Eval_Connective.assert;
type print      = LiFtEr_Util.print;

datatype assert =
(*Eval_Connective*)
  True
| False
| Not                    of connective
| And                    of connective * connective
| Or                     of connective * connective
| Nor                    of connective * connective
| Imply                  of connective * connective
(*Eval_Node_Core*)
| Is_Cnst                of full_path
| Is_Free                of full_path
| Is_Var                 of full_path
| Is_Bound               of full_path
| Is_Lambda              of full_path
| Is_App                 of full_path
(*Eval_Node_Sugar*)
| Is_Atom                of full_path
| Is_Compund             of full_path
(*Eval_Unode_Core*)
| Has_Same_Prnt_As       of full_path * full_path
| Is_In_Trm_Prnt         of full_path * full_path
| Is_Deeper_Than         of full_path * full_path
| Is_Shallower_Than      of full_path * full_path
| Is_Path_Above          of full_path * full_path
| Is_Same_Path_As        of full_path * full_path
(*Eval_Unode_Sugar*)
| Is_As_Deep_As          of full_path * full_path
| Is_Path_Below          of full_path * full_path
(*Eval_Fpunode_Core*)
| Is_In_Same_Location_As of full_path * full_path
| Is_In_Chained          of full_path
| Is_In_Fst_Subg         of full_path
(*Eval_Fpunode_Sugar*)
| Is_Above               of full_path * full_path
| Is_Below               of full_path * full_path
| Is_Same_Occ_As         of full_path * full_path
(*Eval_Print_Core*)
| Are_Same_Prints        of print * print
| Is_Printed_As          of print * string
(*Eval_Print_Sugar*)
| Are_Different_Prints   of print     * print
| Fpnode_Has_Print       of full_path * print;

type full_path_to_fpunode_table = Full_Path_To_Fpunode.full_path_to_fpunode_table;

val eval: full_path_to_fpunode_table -> assert -> Eval_Connective.assert;

end;