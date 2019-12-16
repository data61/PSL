(*  Title:      PSL/SeLFeE/src/Eval_Parameter_With_Bool.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

    Eval_Bool_With_Parameter has constructs from Eval_Bool.
    We have to have the boolean operators this way to implement quantifiers in later steps.
*)
signature EVAL_PARAMETER_WITH_BOOL =
sig

type path;
type print   = SeLFiE_Util.print;
type number  = Eval_Number.number;
type command = Pattern.command;(*TODO: double-check*)

datatype parameter =
  Bool    of bool
| Path    of path
| Print   of print
| String  of string
| Number  of number
| Int     of int
| Command of command;

type parameters = parameter list;

datatype atomic_assert =
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
(*Eval_Path*)
| Unode_Has_Print
(*Eval_Number*)
| Are_Same_Number
| Is_Less_Than
| Is_Int;

(* The data-type constructors for boolean operations have to be declared in this signature.
 * because we need them i`n From_Var_To_Quantifier.*)
datatype assert =
  Not
| And
| Or
| Nor
| Imply
| Ands
| Ors
| Atomic of atomic_assert;

val eval: term -> Proof.state -> assert -> parameters -> parameter;

end;