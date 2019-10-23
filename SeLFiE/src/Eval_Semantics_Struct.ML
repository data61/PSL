(*  Title:      PSL/SeLFiE/src/Eval_Semantics_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Eval_Semantics:EVAL_SEMANTICS =
struct

type full_path = full_path;
type print     = LiFtEr_Util.print;
type name      = string;

datatype qtyp = QFull_Path | QPrint | QInd | QArb | QRule;

datatype assert =
(*Eval_Connective*)
  True
| False
| Not                    of assert
| And                    of assert * assert
| Or                     of assert * assert
| Nor                    of assert * assert
| Imply                  of assert * assert
| Ands                   of assert list
| Ors                    of assert list
(*Eval_Node_Core*)
| Is_Cnst                of name
| Is_Free                of name
| Is_Var                 of name
| Is_Bound               of name
| Is_Lambda              of name
| Is_App                 of name
(*Eval_Node_Sugar*)
| Is_Atom                of name
| Is_Compund             of name
(*Eval_Unode_Core*)
| Has_Same_Prnt_As       of name * name
| Is_In_Trm_Prnt         of name * name
| Is_Deeper_Than         of name * name
| Is_Shallower_Than      of name * name
| Is_Path_Above          of name * name
| Is_Same_Path_As        of name * name
(*Eval_Unode_Sugar*)
| Is_As_Deep_As          of name * name
| Is_Path_Below          of name * name
(*Eval_Fpunode_Core*)
| Is_In_Same_Location_As of name * name
| Is_In_Chained          of name
| Is_In_Fst_Subg         of name
(*Eval_Fpunode_Sugar*)
| Is_Above               of name * name
| Is_Below               of name * name
| Is_Same_Occ_As         of name * name
(*Eval_Print_Core*)
| Are_Same_Prints        of name * name
| Is_Printed_As          of name * string
(*Eval_Print_Sugar*)
| Are_Different_Prints   of name * name
| Fpnode_Has_Print       of name * name
(*Eval_Number*)
| Are_Same_Number        of name  * name
| Is_Less_Than           of name  * name
| Is_Int                 of name  * int
(*Other*)
| Is_Nth_Arg_Of          of name * name * name
(*Quantifier*)
| All                    of name * qtyp * assert
| Some                   of name * qtyp * assert
(*Modifier*)
| Is_Rule_Of             of name * name
(*Semantic*)
| Holds_In_Any_Clause_Of of assert * name
| Holds_In_One_Clause_Of of assert * name;

fun eval (pst:Proof.state) (assert:assert) = true (*TODO*);

end;