(*  Title:      PSL/SeLFiE/src/Interpreter/From_Multi_To_Sugar.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

*)
(*** functor: from_Multi_Arity_to_Sugar ***)
functor from_Multi_Arity_to_Sugar (Eval_Multi_Arity:EVAL_MULTI_ARITY) =
struct

structure EMA = Eval_Multi_Arity;

(*** Eval_Multi_Arity ***)
(*
(*  Title:      PSL/SeLFiE/src/Interpreter/Eval_Multi_Arity.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_MULTI_ARITY =
sig

type parameter;

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
(*Eval_Path*)
| Unode_Has_Print
(*Eval_Number*)
| Are_Same_Number
| Is_Less_Than
| Is_Int;

(* The data-type constructors for boolean operations have to be declared in this signature.
 * because we need them in From_Var_To_Quantifier.*)
datatype assert =
  Not
| And
| Or
| Nor
| Imply
| Ands
| Ors
| Atomic of parameter_assert;

type qtyp(* = QFull_Path | QPrint | QInd | QArb | QRule | QNumber*)

datatype expr =
  Variable of string
| Lambdas  of strings * expr
| Applies  of expr    * expr list
| Literal  of parameter
| Assert   of assert * expr list
| Alls     of (string * qtyp) list * expr
| Somes    of (string * qtyp) list * expr;

val eval: term -> Proof.state -> expr -> expr;

end;
*)

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
| Literal  of assert
| Alls     of (string * qtyp) list * assert
| Somes    of (string * qtyp) list * assert
| In_All_Def_Of  of (string * assert)
| In_Some_Def_Of of (string * assert)
| Outermost of assert
| Innermost of assert;

fun (*convert (True)  = () (*TODO: I have to get True as a parameter*)
  | convert (False) = () (*TODO: I have to get False as a parameter*)
  |*) 
    convert (Not    assert     ) = EMA.Assert (EMA.Not,   [convert assert])
  | convert (And   (ass1, ass2)) = EMA.Assert (EMA.And,   [convert ass1, convert ass2])
  | convert (Or    (ass1, ass2)) = EMA.Assert (EMA.Or,    [convert ass1, convert ass2])
  | convert (Nor   (ass1, ass2)) = EMA.Assert (EMA.Nor,   [convert ass1, convert ass2])
  | convert (Imply (ass1, ass2)) = EMA.Assert (EMA.Imply, [convert ass1, convert ass2])
  | convert (Ands   asserts    ) = EMA.Assert (EMA.Ands,   map convert asserts)
  | convert (Ors    asserts    ) = EMA.Assert (EMA.Ors,    map convert asserts)
  | convert (Is_Cnst assert    ) = EMA.Assert (EMA.Atomic EMA.Is_Cnst,   [convert assert])
  | convert (Is_Free assert    ) = EMA.Assert (EMA.Atomic EMA.Is_Free,   [convert assert])
  | convert (Is_Var  assert    ) = EMA.Assert (EMA.Atomic EMA.Is_Var,    [convert assert])
  | convert (Is_Bound    assert) = EMA.Assert (EMA.Atomic EMA.Is_Bound,  [convert assert])
  | convert (Is_Lambda   assert) = EMA.Assert (EMA.Atomic EMA.Is_Lambda, [convert assert])
  | convert (Is_App      assert) = EMA.Assert (EMA.Atomic EMA.Is_App,    [convert assert])
  | convert (Has_Same_Prnt_As  (ass1, ass2)) = EMA.Assert (EMA.Atomic EMA.Has_Same_Prnt_As,  map convert [ass1, ass2])
  | convert (Is_In_Trm_Prnt    (ass1, ass2)) = EMA.Assert (EMA.Atomic EMA.Is_In_Trm_Prnt,    map convert [ass1, ass2])
  | convert (Is_Deeper_Than    (ass1, ass2)) = EMA.Assert (EMA.Atomic EMA.Is_Deeper_Than,    map convert [ass1, ass2])
  | convert (Is_Shallower_Than (ass1, ass2)) = EMA.Assert (EMA.Atomic EMA.Is_Shallower_Than, map convert [ass1, ass2])
  | convert (Is_Path_Above     (ass1, ass2)) = EMA.Assert (EMA.Atomic EMA.Is_Path_Above,     map convert [ass1, ass2])
  | convert (Is_Same_Path_As   (ass1, ass2)) = EMA.Assert (EMA.Atomic EMA.Is_Same_Path_As,   map convert [ass1, ass2])
  | convert (Are_Same_Prints   (ass1, ass2)) = EMA.Assert (EMA.Atomic EMA.Are_Same_Prints,   map convert [ass1, ass2])
  | convert (Is_Printed_As     (ass1, ass2)) = EMA.Assert (EMA.Atomic EMA.Is_Printed_As,     map convert [ass1, ass2])
  | convert (Unode_Has_Print   (ass1, ass2)) = EMA.Assert (EMA.Atomic EMA.Unode_Has_Print,   map convert [ass1, ass2])
  | convert (Are_Same_Number   (ass1, ass2)) = EMA.Assert (EMA.Atomic EMA.Are_Same_Number,   map convert [ass1, ass2])
  | convert (Is_Less_Than      (ass1, ass2)) = EMA.Assert (EMA.Atomic EMA.Is_Less_Than,      map convert [ass1, ass2])
  | convert (Is_Int            (ass1, ass2)) = EMA.Assert (EMA.Atomic EMA.Is_Int,            map convert [ass1, ass2])
(*I need a concrete parameter here..*)
  | convert (Print              print      ) = EMA.Literal (EMA.Print print)
(*TODO:
(*Parameter*)
| Print  of print
| Number of number
(*expr*)
| Variable of string
| Lambdas  of strings * assert
| Applies  of assert  * assert list
| Literal  of assert
| Alls     of (string * qtyp) list * assert
| Somes    of (string * qtyp) list * assert
| In_All_Def_Of  of (string * assert)
| In_Some_Def_Of of (string * assert)
| Outermost of assert
| Innermost of assert;
*)
;

end;