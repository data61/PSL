(*  Title:      PSL/SeLFeE/src/Eval_Path_Parameter_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_PATH_PARAMETER =
sig

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

val trm_n_pst_to_path_to_unode_table: term -> Proof.state -> path_to_unode_table;

val eval: term -> Proof.state -> assert -> parameters -> Eval_Connective.assert;

end;