(*  Title:      PSL/SeLFiE/src/Interpreter/From_Deep_To_Surface.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

*)

(*** functor: from_Deep_to_Surface ***)
functor from_Deep_to_Surface (Eval_Deep:EVAL_DEEP)  =
struct

structure ED = Eval_Deep;

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
| Somes    of (string * qtyp) list * assert
| In_All_Definitions  of (assert * assert * assert list)
| In_Some_Definitions of (assert * assert * assert list)
| Outermost           of assert;


structure EOS = Eval_Outer_Sugar;
structure EIS = Eval_Inner_Sugar;

fun go_out_qtyp QFull_Path = EOS.QFull_Path
  | go_out_qtyp QPrint     = EOS.QPrint
  | go_out_qtyp QInd       = EOS.QInd
  | go_out_qtyp QArb       = EOS.QArb
  | go_out_qtyp QRule      = EOS.QRule
  | go_out_qtyp QNumber    = EOS.QNumber

fun converty _ = error ""

fun convert_outermost  True                    = EOS.True
  | convert_outermost  False                   = EOS.False
  | convert_outermost (Not    assert     )     = EOS.Not       (convert_outermost assert)
  | convert_outermost (And    pair)            = EOS.And       (apply2 convert_outermost pair)
  | convert_outermost (Or     pair)            = EOS.Or        (apply2 convert_outermost pair)
  | convert_outermost (Nor    pair)            = EOS.Nor       (apply2 convert_outermost pair)
  | convert_outermost (Imply  pair)            = EOS.Imply     (apply2 convert_outermost pair)
  | convert_outermost (Ands   asserts    )     = EOS.Ands      (map convert_outermost asserts)
  | convert_outermost (Ors    asserts    )     = EOS.Ors       (map convert_outermost asserts)
  | convert_outermost (Is_Cnst assert    )     = EOS.Is_Cnst   (convert_outermost assert)
  | convert_outermost (Is_Free assert    )     = EOS.Is_Free   (convert_outermost assert)
  | convert_outermost (Is_Var  assert    )     = EOS.Is_Var    (convert_outermost assert)
  | convert_outermost (Is_Bound    assert)     = EOS.Is_Bound  (convert_outermost assert)
  | convert_outermost (Is_Lambda   assert)     = EOS.Is_Lambda (convert_outermost assert)
  | convert_outermost (Is_App      assert)     = EOS.Is_App    (convert_outermost assert)
  | convert_outermost (Has_Same_Prnt_As  pair) = EOS.Has_Same_Prnt_As  (apply2 convert_outermost pair) 
  | convert_outermost (Is_In_Trm_Prnt    pair) = EOS.Is_In_Trm_Prnt    (apply2 convert_outermost pair)
  | convert_outermost (Is_Deeper_Than    pair) = EOS.Is_Deeper_Than    (apply2 convert_outermost pair)
  | convert_outermost (Is_Shallower_Than pair) = EOS.Is_Shallower_Than (apply2 convert_outermost pair)
  | convert_outermost (Is_Path_Above     pair) = EOS.Is_Path_Above     (apply2 convert_outermost pair)
  | convert_outermost (Is_Same_Path_As   pair) = EOS.Is_Same_Path_As   (apply2 convert_outermost pair)
  | convert_outermost (Are_Same_Prints   pair) = EOS.Are_Same_Prints   (apply2 convert_outermost pair)
  | convert_outermost (Is_Printed_As     pair) = EOS.Is_Printed_As     (apply2 convert_outermost pair)
  | convert_outermost (Unode_Has_Print   pair) = EOS.Unode_Has_Print   (apply2 convert_outermost pair)
  | convert_outermost (Are_Same_Number   pair) = EOS.Are_Same_Number   (apply2 convert_outermost pair)
  | convert_outermost (Is_Less_Than      pair) = EOS.Is_Less_Than      (apply2 convert_outermost pair)
  | convert_outermost (Is_Int            pair) = EOS.Is_Int            (apply2 convert_outermost pair)
  | convert_outermost (Print     print      )  = EOS.Print    print
  | convert_outermost (Number    number     )  = EOS.Number   number
  | convert_outermost (Variable  string     )  = EOS.Variable string
  | convert_outermost (Lambdas  (strs, expr))  = EOS.Lambdas  (strs, convert_outermost expr)
  | convert_outermost (Applies  (func, args))  = EOS.Applies  (convert_outermost func, map convert_outermost args)
  | convert_outermost (Alls     (pairs, expr)) = EOS.Alls  (map (apsnd go_out_qtyp) pairs, convert_outermost expr)
  | convert_outermost (Somes    (pairs, expr)) = EOS.Somes (map (apsnd go_out_qtyp) pairs, convert_outermost expr)
  | convert_outermost (Outermost _)            = error "convert_outermost in From_Deep_To_Deep_Sugar.ML failed. Nested Outermost is not allowed."

val convert_inner_expr = undefined; (*TODO*)

fun convert_dive_in (In_All_Definitions (outer_assert, inner_expr, outer_asserts)) =
  (convert_outermost outer_assert, convert_inner_expr inner_expr, map convert_outermost outer_asserts);

fun convert' (In_All_Definitions triple) = convert_dive_in (In_All_Definitions triple) |> ED.Dive_In
  | convert' (other)                     = convert_outermost other                     |> ED.Outer            

fun convert (Outermost assert) = convert' assert
  | convert  _ = error "convert in From_Deep_To_Deep_Sugar failed.\nAn assertion should start with Outermost."

val eval = undefined: Proof.state -> term -> assert -> assert;

end;