(*  Title:      PSL/SeLFiE/src/Interpreter/Eval_Sugar.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
(*** signature: EVAL_SUGAR ***)
signature EVAL_SUGAR =
sig

datatype qtyp = QFull_Path | QPrint | QInd | QArb | QRule | QNumber;

type print   = SeLFiE_Util.print;
type number  = Eval_Number.number;

datatype assert =
(*bool*)
  True
| False
| Not      of assert
| And      of assert * assert
| Or       of assert * assert
| Nor      of assert * assert
| Imply    of assert * assert
| Ands     of assert list
| Ors      of assert list
(*Eval_Node*)
| Is_Cnst    of assert
| Is_Free    of assert
| Is_Var     of assert
| Is_Bound   of assert
| Is_Lambda  of assert
| Is_App     of assert
(*Eval_Unode*)
| Has_Same_Prnt_As  of assert * assert
| Is_In_Trm_Prnt    of assert * assert
| Is_Deeper_Than    of assert * assert
| Is_Shallower_Than of assert * assert
| Is_Path_Above     of assert * assert
| Is_Same_Path_As   of assert * assert
(*Eval_Print*)
| Are_Same_Prints   of assert * assert
| Is_Printed_As     of assert * assert
(*Eval_Path*)
| Unode_Has_Print   of assert * assert
(*Eval_Number*)
| Are_Same_Number of assert * assert
| Is_Less_Than    of assert * assert
| Is_Int          of assert * assert
(*Parameter*)
| Print  of print
| Number of number
(*expr*)
| Variable of string
| Lambdas  of strings * assert
| Applies  of assert  * assert list
| Alls     of (string * qtyp) list * assert
| Somes    of (string * qtyp) list * assert;

val eval: Proof.state -> term -> assert -> assert;

end;
