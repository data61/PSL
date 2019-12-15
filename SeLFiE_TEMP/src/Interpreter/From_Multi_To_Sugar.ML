(*  Title:      PSL/SeLFiE/src/Interpreter/From_Multi_To_Sugar.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

*)
(*** functor: from_Multi_Arity_to_Sugar ***)
functor from_Multi_Arity_to_Sugar (Eval_Multi_Arity:EVAL_MULTI_ARITY) : EVAL_SUGAR =
struct

structure EMA = Eval_Multi_Arity;

datatype qtyp = QFull_Path | QPrint | QInd | QArb | QRule | QNumber;

fun go_away_qtyp QFull_Path = EMA.QFull_Path
  | go_away_qtyp QPrint     = EMA.QPrint
  | go_away_qtyp QInd       = EMA.QInd
  | go_away_qtyp QArb       = EMA.QArb
  | go_away_qtyp QRule      = EMA.QRule
  | go_away_qtyp QNumber    = EMA.QNumber

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

fun convert  True                             = EMA.Literal (EMA.Bool true)
  | convert  False                            = EMA.Literal (EMA.Bool false)
  | convert (Not    assert     )              = EMA.Assert (EMA.Not,   [convert assert])
  | convert (And   (ass1, ass2))              = EMA.Assert (EMA.And,   [convert ass1, convert ass2])
  | convert (Or    (ass1, ass2))              = EMA.Assert (EMA.Or,    [convert ass1, convert ass2])
  | convert (Nor   (ass1, ass2))              = EMA.Assert (EMA.Nor,   [convert ass1, convert ass2])
  | convert (Imply (ass1, ass2))              = EMA.Assert (EMA.Imply, [convert ass1, convert ass2])
  | convert (Ands   asserts    )              = EMA.Assert (EMA.Ands,   map convert asserts)
  | convert (Ors    asserts    )              = EMA.Assert (EMA.Ors,    map convert asserts)
  | convert (Is_Cnst assert    )              = EMA.Assert (EMA.Atomic EMA.Is_Cnst,   [convert assert])
  | convert (Is_Free assert    )              = EMA.Assert (EMA.Atomic EMA.Is_Free,   [convert assert])
  | convert (Is_Var  assert    )              = EMA.Assert (EMA.Atomic EMA.Is_Var,    [convert assert])
  | convert (Is_Bound    assert)              = EMA.Assert (EMA.Atomic EMA.Is_Bound,  [convert assert])
  | convert (Is_Lambda   assert)              = EMA.Assert (EMA.Atomic EMA.Is_Lambda, [convert assert])
  | convert (Is_App      assert)              = EMA.Assert (EMA.Atomic EMA.Is_App,    [convert assert])
  | convert (Has_Same_Prnt_As  (ass1,  ass2)) = EMA.Assert (EMA.Atomic EMA.Has_Same_Prnt_As,  map convert [ass1, ass2])
  | convert (Is_In_Trm_Prnt    (ass1,  ass2)) = EMA.Assert (EMA.Atomic EMA.Is_In_Trm_Prnt,    map convert [ass1, ass2])
  | convert (Is_Deeper_Than    (ass1,  ass2)) = EMA.Assert (EMA.Atomic EMA.Is_Deeper_Than,    map convert [ass1, ass2])
  | convert (Is_Shallower_Than (ass1,  ass2)) = EMA.Assert (EMA.Atomic EMA.Is_Shallower_Than, map convert [ass1, ass2])
  | convert (Is_Path_Above     (ass1,  ass2)) = EMA.Assert (EMA.Atomic EMA.Is_Path_Above,     map convert [ass1, ass2])
  | convert (Is_Same_Path_As   (ass1,  ass2)) = EMA.Assert (EMA.Atomic EMA.Is_Same_Path_As,   map convert [ass1, ass2])
  | convert (Are_Same_Prints   (ass1,  ass2)) = EMA.Assert (EMA.Atomic EMA.Are_Same_Prints,   map convert [ass1, ass2])
  | convert (Is_Printed_As     (ass1,  ass2)) = EMA.Assert (EMA.Atomic EMA.Is_Printed_As,     map convert [ass1, ass2])
  | convert (Unode_Has_Print   (ass1,  ass2)) = EMA.Assert (EMA.Atomic EMA.Unode_Has_Print,   map convert [ass1, ass2])
  | convert (Are_Same_Number   (ass1,  ass2)) = EMA.Assert (EMA.Atomic EMA.Are_Same_Number,   map convert [ass1, ass2])
  | convert (Is_Less_Than      (ass1,  ass2)) = EMA.Assert (EMA.Atomic EMA.Is_Less_Than,      map convert [ass1, ass2])
  | convert (Is_Int            (ass1,  ass2)) = EMA.Assert (EMA.Atomic EMA.Is_Int,            map convert [ass1, ass2])
  | convert (Print     print      )           = EMA.Literal (EMA.Print print)
  | convert (Number    number     )           = EMA.Literal (EMA.Number number)
  | convert (Variable  string     )           = EMA.Variable string
  | convert (Lambdas  (strs, expr))           = EMA.Lambdas (strs, convert expr)
  | convert (Applies  (func, args))           = EMA.Applies (convert func, map convert args)
  | convert (Alls              (pairs, expr)) = EMA.Alls    (map (apsnd go_away_qtyp) pairs, convert expr)
  | convert (Somes             (pairs, expr)) = EMA.Somes   (map (apsnd go_away_qtyp) pairs, convert expr);

fun only_bool (EMA.Literal ema_bool) = (case ema_bool of
      EMA.Bool bool => if bool then True else False
    | _             => error "only_bool in From_Multi_To_Sugar.ML failed. Not Bool.")
  | only_bool _ = error "only_bool in From_Multi_To_Sugar.ML failed. Not even Literal."

fun eval (pst:Proof.state) (term:term) (assert:assert) = EMA.eval term pst (convert assert) |> only_bool;

end;