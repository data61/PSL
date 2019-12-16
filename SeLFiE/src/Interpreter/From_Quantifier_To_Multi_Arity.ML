(*  Title:      PSL/SeLFeE/src/From_Quantifier_To_Multi_Arity.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
functor from_Quantifier_to_Multi_Arity (Eval_Quantifier:EVAL_QUANTIFIER): EVAL_MULTI_ARITY  =
struct

structure EQ = Eval_Quantifier;

type path    = EQ.path;
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

fun here_to_there (Bool b)    = EQ.Bool b
  | here_to_there (Path p)    = EQ.Path p
  | here_to_there (Print p)   = EQ.Print p
  | here_to_there (String s)  = EQ.String s
  | here_to_there (Number n)  = EQ.Number n
  | here_to_there (Int i)     = EQ.Int i
  | here_to_there (Command i) = EQ.Command i;

fun there_to_here (EQ.Bool b)    = Bool b
  | there_to_here (EQ.Path p)    = Path p
  | there_to_here (EQ.Print p)   = Print p
  | there_to_here (EQ.String s)  = String s
  | there_to_here (EQ.Number n)  = Number n
  | there_to_here (EQ.Int i)     = Int i
  | there_to_here (EQ.Command i) = Command i;

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

fun convert_parameter_assert Is_Cnst          = EQ.Is_Cnst
  | convert_parameter_assert Is_Free          = EQ.Is_Free
  | convert_parameter_assert Is_Var           = EQ.Is_Var
  | convert_parameter_assert Is_Bound         = EQ.Is_Bound
  | convert_parameter_assert Is_Lambda        = EQ.Is_Lambda
  | convert_parameter_assert Is_App           = EQ.Is_App
  | convert_parameter_assert Has_Same_Prnt_As = EQ.Has_Same_Prnt_As
  | convert_parameter_assert Is_In_Trm_Prnt   = EQ.Is_In_Trm_Prnt
  | convert_parameter_assert Is_Deeper_Than   = EQ.Is_Deeper_Than
  | convert_parameter_assert Is_Shallower_Than= EQ.Is_Shallower_Than
  | convert_parameter_assert Is_Path_Above    = EQ.Is_Path_Above
  | convert_parameter_assert Is_Same_Path_As  = EQ.Is_Same_Path_As
  | convert_parameter_assert Are_Same_Prints  = EQ.Are_Same_Prints
  | convert_parameter_assert Is_Printed_As    = EQ.Is_Printed_As
  | convert_parameter_assert Unode_Has_Print  = EQ.Unode_Has_Print
  | convert_parameter_assert Are_Same_Number  = EQ.Are_Same_Number
  | convert_parameter_assert Is_Less_Than     = EQ.Is_Less_Than
  | convert_parameter_assert Is_Int           = EQ.Is_Int;

datatype assert =
  Not
| And
| Or
| Nor
| Imply
| Ands
| Ors
| Atomic of atomic_assert;

fun convert_assert Not   = EQ.Not
  | convert_assert And   = EQ.And
  | convert_assert Or    = EQ.Or
  | convert_assert Nor   = EQ.Nor
  | convert_assert Imply = EQ.Imply
  | convert_assert Ands  = EQ.Ands
  | convert_assert Ors   = EQ.Ors
  | convert_assert (Atomic assert) = EQ.Atomic (convert_parameter_assert assert);

datatype qtyp = QFull_Path | QPrint | QInd | QArb | QRule | QNumber;

fun qtyp_go_away QFull_Path = EQ.QFull_Path
  | qtyp_go_away QPrint     = EQ.QPrint
  | qtyp_go_away QInd       = EQ.QInd
  | qtyp_go_away QArb       = EQ.QArb
  | qtyp_go_away QRule      = EQ.QRule
  | qtyp_go_away QNumber    = EQ.QNumber

datatype expr =
  Variable of string
| Lambdas  of strings * expr
| Applies  of expr    * expr list
| Literal  of parameter
| Assert   of assert * expr list
| Alls     of (string * qtyp) list * expr
| Somes    of (string * qtyp) list * expr;

datatype quant = All | Some;

fun quantifier_to_multi_arity (Variable vname)        = EQ.Variable vname
  | quantifier_to_multi_arity (Lambdas ([], expr))    = quantifier_to_multi_arity expr
  | quantifier_to_multi_arity (Lambdas (v::vs, expr)) = EQ.Lambda (v, quantifier_to_multi_arity (Lambdas (vs, expr)))
  | quantifier_to_multi_arity (Applies (f, xs))       =
    let
      fun mk_nested_pair  []                  (acc:EQ.expr) = acc:EQ.expr
        | mk_nested_pair (arg::args:expr list)(acc:EQ.expr) = mk_nested_pair args (EQ.Apply (acc, quantifier_to_multi_arity arg)):EQ.expr
    in
      mk_nested_pair xs (quantifier_to_multi_arity f)
    end
  | quantifier_to_multi_arity (Literal param)        = EQ.Literal (here_to_there param)
  | quantifier_to_multi_arity (Assert (ass, exprs))  = EQ.Assert (convert_assert ass, map quantifier_to_multi_arity exprs)
  | quantifier_to_multi_arity (Alls   (pairs, expr)) = mk_nested_pair_for_quantifier All  pairs expr
  | quantifier_to_multi_arity (Somes  (pairs, expr)) = mk_nested_pair_for_quantifier Some pairs expr
and mk_nested_pair_for_quantifier qtyp pairs expr =
    let
      val quantifier = if qtyp = All then EQ.All else EQ.Some
      fun mk_nested_pair  []                                       (acc:EQ.expr) = acc:EQ.expr
        | mk_nested_pair ((name, typ)::pairs:(string * qtyp) list) (acc:EQ.expr) =
          mk_nested_pair pairs (quantifier (name, qtyp_go_away typ, acc):EQ.expr)
    in
      mk_nested_pair pairs (quantifier_to_multi_arity expr)
    end;

fun convert_result (EQ.Literal ee_bool) = Literal (there_to_here ee_bool)
  | convert_result  _ =
    error "eval in Eval_Var_Struct failed. Evaluation is not complete.";

fun eval (trm:term) (pst:Proof.state) expr =
  let
    val eq_result  = EQ.eval trm pst (quantifier_to_multi_arity expr);
    val result     = convert_result eq_result                        : expr;
  in
    result
  end;

end;