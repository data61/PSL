(*  Title:      PSL/SeLFeE/src/Eval_Path_Expression_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

    Eval_Expression has constructs from Eval_Connective.
*)
signature EVAL_PATH_EXPRESSION =
sig

type connective = Eval_Connective.assert;
type path       = LiFtEr_Util.path;
type print      = LiFtEr_Util.print;
type number     = Eval_Number.number;
type command    = Pattern.command;

datatype parameter =
  Bool    of bool
| Path    of path
| Print   of print
| String  of string(*redundant?*)
| Number  of number
| Int     of int
| Command of command;

type parameters = parameter list;

datatype assert =
(*Eval_Connective*)
  Not
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

val eval: term -> Proof.state -> assert -> parameters -> parameter;

end;