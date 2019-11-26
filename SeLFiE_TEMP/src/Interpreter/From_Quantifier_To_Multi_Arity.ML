(*  Title:      PSL/SeLFeE/src/From_Quantifier_To_Multi_Arity.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
functor from_Quantifier_to_Multi_Arity (Eval_Quantifier:EVAL_QUANTIFIER): EVAL_MULTI_ARITY  =
struct

structure EQ = Eval_Quantifier;

type parameter = EQ.parameter;

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
| Eval_Parameter of parameter_assert;

fun convert_assert Not   = EQ.Not
  | convert_assert And   = EQ.And
  | convert_assert Or    = EQ.Or
  | convert_assert Nor   = EQ.Nor
  | convert_assert Imply = EQ.Imply
  | convert_assert Ands  = EQ.Ands
  | convert_assert Ors   = EQ.Ors
  | convert_assert (Eval_Parameter assert) = EQ.Eval_Parameter (convert_parameter_assert assert);

type qtyp = EQ.qtyp;

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
  | quantifier_to_multi_arity (Literal param)        = EQ.Literal param
  | quantifier_to_multi_arity (Assert (ass, exprs))  = EQ.Assert (convert_assert ass, map quantifier_to_multi_arity exprs)
  | quantifier_to_multi_arity (Alls   (pairs, expr)) = mk_nested_pair_for_quantifier All pairs expr
  | quantifier_to_multi_arity (Somes  (pairs, expr)) = mk_nested_pair_for_quantifier Some pairs expr
and mk_nested_pair_for_quantifier qtyp pairs expr =
    let
      val quantifier = if qtyp = All then EQ.All else EQ.Some
      fun mk_nested_pair  []                                       (acc:EQ.expr) = acc:EQ.expr
        | mk_nested_pair ((name, typ)::pairs:(string * qtyp) list) (acc:EQ.expr) =
          mk_nested_pair pairs (quantifier (name, typ, acc):EQ.expr)
    in
      mk_nested_pair pairs (quantifier_to_multi_arity expr)
    end;

fun convert_result (EQ.Literal ee_bool) = Literal ee_bool
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