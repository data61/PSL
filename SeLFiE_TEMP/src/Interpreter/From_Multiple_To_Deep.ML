(*  Title:      PSL/SeLFeE/src/From_Quantifier_To_Multi_Arity.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
functor from_Multiple_to_Deep
 (structure Eval_Outer_Multiple:EVAL_MULTI_ARITY
  and       Eval_Inner_Multiple:EVAL_MULTI_ARITY): EVAL_DEEP =
struct

structure EOM = Eval_Outer_Multiple;
structure EIM = Eval_Inner_Multiple;

type outer_path = EOM.path;
type inner_path = EIM.path;
type print      = SeLFiE_Util.print;
type number     = Eval_Number.number;
type command    = Pattern.command;

datatype outer_parameter =
  Outer_Bool    of bool
| Outer_Path    of outer_path
| Outer_Print   of print
| Outer_String  of string
| Outer_Number  of number
| Outer_Int     of int
| Outer_Command of command;

datatype inner_parameter =
  Inner_Bool    of bool
| Inner_Path    of inner_path
| Inner_Print   of print
| Inner_String  of string
| Inner_Number  of number
| Inner_Int     of int
| Inner_Command of command;

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

datatype assert =
  Not
| And
| Or
| Nor
| Imply
| Ands
| Ors
| Atomic of atomic_assert;

fun go_away_outer_parameter (Outer_Bool    b) = EOM.Bool b
  | go_away_outer_parameter (Outer_Path    p) = EOM.Path p
  | go_away_outer_parameter (Outer_Print   p) = EOM.Print p
  | go_away_outer_parameter (Outer_String  s) = EOM.String s
  | go_away_outer_parameter (Outer_Number  n) = EOM.Number n
  | go_away_outer_parameter (Outer_Int     i) = EOM.Int i
  | go_away_outer_parameter (Outer_Command c) = EOM.Command c;

fun come_back_outer_parameter (EOM.Bool    b) = Outer_Bool    b
  | come_back_outer_parameter (EOM.Path    p) = Outer_Path    p
  | come_back_outer_parameter (EOM.Print   p) = Outer_Print   p
  | come_back_outer_parameter (EOM.String  s) = Outer_String  s
  | come_back_outer_parameter (EOM.Number  n) = Outer_Number  n
  | come_back_outer_parameter (EOM.Int     i) = Outer_Int     i
  | come_back_outer_parameter (EOM.Command c) = Outer_Command c;

fun go_away_inner_parameter (Inner_Bool b)    = EIM.Bool b
  | go_away_inner_parameter (Inner_Path p)    = EIM.Path p
  | go_away_inner_parameter (Inner_Print p)   = EIM.Print p
  | go_away_inner_parameter (Inner_String s)  = EIM.String s
  | go_away_inner_parameter (Inner_Number n)  = EIM.Number n
  | go_away_inner_parameter (Inner_Int i)     = EIM.Int i
  | go_away_inner_parameter (Inner_Command i) = EIM.Command i;

fun come_back_inner_parameter (EIM.Bool    b) = Inner_Bool    b
  | come_back_inner_parameter (EIM.Path    p) = Inner_Path    p
  | come_back_inner_parameter (EIM.Print   p) = Inner_Print   p
  | come_back_inner_parameter (EIM.String  s) = Inner_String  s
  | come_back_inner_parameter (EIM.Number  n) = Inner_Number  n
  | come_back_inner_parameter (EIM.Int     i) = Inner_Int     i
  | come_back_inner_parameter (EIM.Command c) = Inner_Command c;

fun go_away_outer_atomic Is_Cnst           = EOM.Is_Cnst
  | go_away_outer_atomic Is_Free           = EOM.Is_Free
  | go_away_outer_atomic Is_Var            = EOM.Is_Var
  | go_away_outer_atomic Is_Bound          = EOM.Is_Bound
  | go_away_outer_atomic Is_Lambda         = EOM.Is_Lambda
  | go_away_outer_atomic Is_App            = EOM.Is_App
  | go_away_outer_atomic Has_Same_Prnt_As  = EOM.Has_Same_Prnt_As
  | go_away_outer_atomic Is_In_Trm_Prnt    = EOM.Is_In_Trm_Prnt
  | go_away_outer_atomic Is_Deeper_Than    = EOM.Is_Deeper_Than
  | go_away_outer_atomic Is_Shallower_Than = EOM.Is_Shallower_Than
  | go_away_outer_atomic Is_Path_Above     = EOM.Is_Path_Above
  | go_away_outer_atomic Is_Same_Path_As   = EOM.Is_Same_Path_As
  | go_away_outer_atomic Are_Same_Prints   = EOM.Are_Same_Prints
  | go_away_outer_atomic Is_Printed_As     = EOM.Is_Printed_As
  | go_away_outer_atomic Unode_Has_Print   = EOM.Unode_Has_Print
  | go_away_outer_atomic Are_Same_Number   = EOM.Are_Same_Number
  | go_away_outer_atomic Is_Less_Than      = EOM.Is_Less_Than
  | go_away_outer_atomic Is_Int            = EOM.Is_Int;

fun go_away_inner_atomic Is_Cnst           = EIM.Is_Cnst
  | go_away_inner_atomic Is_Free           = EIM.Is_Free
  | go_away_inner_atomic Is_Var            = EIM.Is_Var
  | go_away_inner_atomic Is_Bound          = EIM.Is_Bound
  | go_away_inner_atomic Is_Lambda         = EIM.Is_Lambda
  | go_away_inner_atomic Is_App            = EIM.Is_App
  | go_away_inner_atomic Has_Same_Prnt_As  = EIM.Has_Same_Prnt_As
  | go_away_inner_atomic Is_In_Trm_Prnt    = EIM.Is_In_Trm_Prnt
  | go_away_inner_atomic Is_Deeper_Than    = EIM.Is_Deeper_Than
  | go_away_inner_atomic Is_Shallower_Than = EIM.Is_Shallower_Than
  | go_away_inner_atomic Is_Path_Above     = EIM.Is_Path_Above
  | go_away_inner_atomic Is_Same_Path_As   = EIM.Is_Same_Path_As
  | go_away_inner_atomic Are_Same_Prints   = EIM.Are_Same_Prints
  | go_away_inner_atomic Is_Printed_As     = EIM.Is_Printed_As
  | go_away_inner_atomic Unode_Has_Print   = EIM.Unode_Has_Print
  | go_away_inner_atomic Are_Same_Number   = EIM.Are_Same_Number
  | go_away_inner_atomic Is_Less_Than      = EIM.Is_Less_Than
  | go_away_inner_atomic Is_Int            = EIM.Is_Int;

fun go_away_outer_assert Not                    = EOM.Not
  | go_away_outer_assert And                    = EOM.And
  | go_away_outer_assert Or                     = EOM.Or
  | go_away_outer_assert Nor                    = EOM.Nor
  | go_away_outer_assert Imply                  = EOM.Imply
  | go_away_outer_assert Ands                   = EOM.Ands
  | go_away_outer_assert Ors                    = EOM.Ors
  | go_away_outer_assert (Atomic atomic_assert) = EOM.Atomic (go_away_outer_atomic atomic_assert);

fun go_away_inner_assert Not                    = EIM.Not
  | go_away_inner_assert And                    = EIM.And
  | go_away_inner_assert Or                     = EIM.Or
  | go_away_inner_assert Nor                    = EIM.Nor
  | go_away_inner_assert Imply                  = EIM.Imply
  | go_away_inner_assert Ands                   = EIM.Ands
  | go_away_inner_assert Ors                    = EIM.Ors
  | go_away_inner_assert (Atomic atomic_assert) = EIM.Atomic (go_away_inner_atomic atomic_assert);

datatype qtyp = QFull_Path | QPrint | QInd | QArb | QRule | QNumber;

fun go_away_outer_qtyp QFull_Path = EOM.QFull_Path
  | go_away_outer_qtyp QPrint     = EOM.QPrint
  | go_away_outer_qtyp QInd       = EOM.QInd
  | go_away_outer_qtyp QArb       = EOM.QArb
  | go_away_outer_qtyp QRule      = EOM.QRule
  | go_away_outer_qtyp QNumber    = EOM.QNumber;

fun go_away_inner_qtyp QFull_Path = EIM.QFull_Path
  | go_away_inner_qtyp QPrint     = EIM.QPrint
  | go_away_inner_qtyp QInd       = EIM.QInd
  | go_away_inner_qtyp QArb       = EIM.QArb
  | go_away_inner_qtyp QRule      = EIM.QRule
  | go_away_inner_qtyp QNumber    = EIM.QNumber;

datatype outer_expression =
  Outer_Variable of string
| Outer_Lambdas  of strings * outer_expression
| Outer_Applies  of outer_expression * outer_expression list
| Outer_Literal  of outer_parameter
| Outer_Assert   of assert * outer_expression list
| Outer_Alls     of (string * qtyp) list * outer_expression
| Outer_Somes    of (string * qtyp) list * outer_expression
| Dive_In        of (outer_expression * inner_expression * outer_expression list)
and inner_expression =
  Inner_Variable of string
| Inner_Lambdas  of strings * outer_expression
| Inner_Applies  of outer_expression    * outer_expression list
| Inner_Literal  of inner_parameter
| Inner_Assert   of assert * outer_expression list
| Inner_Alls     of (string * qtyp) list * outer_expression
| Inner_Somes    of (string * qtyp) list * outer_expression
| Dive_Deeper    of (inner_expression * inner_expression * inner_expression list);

fun come_back_outer_expression (EOM.Literal p) = come_back_outer_parameter p |> Outer_Literal
  | come_back_outer_expression _ = error "come_back_outer_expression in From_Multiple_To_Deep.ML failed."

fun come_back_inner_expression (EIM.Literal p) = come_back_inner_parameter p |> Inner_Literal
  | come_back_inner_expression _ = error "come_back_inner_expression in From_Multiple_To_Deep.ML failed."

fun from_outer_parameter_to_inner_parameter (Outer_Bool   b) = Inner_Bool b
  | from_outer_parameter_to_inner_parameter (Outer_Print  p) = Inner_Print p
  | from_outer_parameter_to_inner_parameter (Outer_Number n) = Inner_Number n
  | from_outer_parameter_to_inner_parameter _ = error "from_outer_parameter_to_inner_parameter in From_Multiple_To_Deep.ML failed. Not Bool, Print, or Number."

datatype expr = Outer of outer_expression | Inner of inner_expression;

(* I need two evals
 * - eval_inner: term -> Proof.state -> outer_expression -> outer_expression
 * - eval_outer: term -> Proof.state -> inner_expression -> inner_expression
 * They should be mutually recursive.
 *)
fun eval_outer (trm:term) (pst:Proof.state) (outer_expression:outer_expression) =
  let
    val eval_eom = EOM.eval trm pst;
    fun eval_outer' (Outer_Variable vname             ) = eval_eom (EOM.Variable vname)
      | eval_outer' (Outer_Lambdas (vnames, sub_expr )) = eval_eom (EOM.Lambdas (vnames, eval_outer' sub_expr))
      | eval_outer' (Outer_Applies (func,   args     )) = eval_eom (EOM.Applies (eval_outer' func, map eval_outer' args))
      | eval_outer' (Outer_Literal  parameter         ) = eval_eom (EOM.Literal (go_away_outer_parameter parameter))
      | eval_outer' (Outer_Assert  (assert, sub_exprs)) = eval_eom (EOM.Assert  (go_away_outer_assert assert, map eval_outer' sub_exprs))
      | eval_outer' (Outer_Alls    (pairs,  sub_expr )) = eval_eom (EOM.Alls  (map (apsnd go_away_outer_qtyp) pairs, eval_outer' sub_expr))
      | eval_outer' (Outer_Somes   (pairs,  sub_expr )) = eval_eom (EOM.Somes (map (apsnd go_away_outer_qtyp) pairs, eval_outer' sub_expr))
      | eval_outer' (Dive_In (target, inner_expr, args)) = error "TODO"
  in
    eval_outer' outer_expression |> come_back_outer_expression
  end
and eval_inner (trm:term) (pst:Proof.state) (inner_expression:inner_expression) =
  let
    val eval_eim = EIM.eval trm pst;
    fun eval_inner' _ = error "TODO";
  in
    eval_inner' inner_expression |> come_back_inner_expression
  end;

fun eval _ = undefined;(*TODO*)

end;