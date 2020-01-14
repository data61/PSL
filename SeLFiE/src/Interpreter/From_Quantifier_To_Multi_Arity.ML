(*  Title:      PSL/SeLFeE/src/From_Quantifier_To_Multi_Arity.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
functor from_Quantifier_to_Multi_Arity (Eval_Quantifier:EVAL_QUANTIFIER): EVAL_MULTI_ARITY  =
struct

structure EQ = Eval_Quantifier;
structure SU = SeLFiE_Util;

type path    = EQ.path;
type command = Pattern.command;

datatype parameter =
  Bool    of bool
| Path    of path
| Print   of string
| String  of string
| Number  of int
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

datatype expr =
  Variable of string
| Lambdas  of strings * expr
| Applies  of expr    * expr list
| Literal  of parameter
| Assert   of SU.assert * expr list
| Alls     of (string * SU.qtyp) list * expr
| Somes    of (string * SU.qtyp) list * expr;

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
  | quantifier_to_multi_arity (Assert (ass, exprs))  = EQ.Assert (ass, map quantifier_to_multi_arity exprs)
  | quantifier_to_multi_arity (Alls   (pairs, expr)) = mk_nested_pair_for_quantifier All  pairs expr
  | quantifier_to_multi_arity (Somes  (pairs, expr)) = mk_nested_pair_for_quantifier Some pairs expr
and mk_nested_pair_for_quantifier qtyp pairs expr =
    let
      val quantifier = if qtyp = All then EQ.All else EQ.Some
      fun mk_nested_pair  []                                          (acc:EQ.expr) = acc:EQ.expr
        | mk_nested_pair ((name, typ)::pairs:(string * SU.qtyp) list) (acc:EQ.expr) =
          mk_nested_pair pairs (quantifier (name, typ, acc):EQ.expr)
    in
      mk_nested_pair pairs (quantifier_to_multi_arity expr)
    end;

fun convert_result (EQ.Literal ee_bool) = Literal (there_to_here ee_bool)
  | convert_result  _ =
    error "eval in Eval_Var_Struct failed. Evaluation is not complete.";

fun eval (trm:term) (pst:Proof.state) (induct_args:SeLFiE_Util.induct_arguments) expr =
  let
    val eq_result  = EQ.eval trm pst induct_args (quantifier_to_multi_arity expr): EQ.expr;
    val result     = convert_result eq_result                                    : expr;
  in
    result
  end;

end;