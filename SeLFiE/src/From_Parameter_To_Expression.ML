(*  Title:      PSL/SeLFeE/src/From_Parameter_To_Expression.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

    This file contains signatures, structures, and functors to support lambda abstraction in SeLFiE.
    The three functions (shift, subst, and eval) in this file are inspired by the functions of the 
    same names found in "ML for the Working Programmer" written by Larry C. Paulson.
*)
functor from_Parameter_to_Expression (Eval_Parameter:EVAL_PARAMETER): EVAL_EXPRESSION  =
struct

structure EP = Eval_Parameter;

type connective = Eval_Connective.assert;
type path       = EP.path;
type print      = LiFtEr_Util.print;
type number     = Eval_Number.number;
type command    = Pattern.command;(*TODO: double-check*)

datatype parameter =
  Bool    of bool
| Path    of path
| Print   of print
| String  of string(*redundant?*)
| Number  of number
| Int     of int
| Command of command;

type parameters = parameter list;

type parameter_assert = Eval_Parameter.parameter_assert;

datatype assert =
  Not
| And
| Or
| Nor
| Imply
| Ands
| Ors
| Eval_Parameter of parameter_assert;

structure EC = Eval_Connective;

fun de_Bool (Bool c) = c
  | de_Bool  _       = error "de_Bool in Eval_Expression_Struct failed.";

val bool_to_connect    = EC.bool_to_assert_connective;
val bools_to_connects  = Utils.map_pair bool_to_connect;
val de_bool_to_connect = bool_to_connect o de_Bool;

fun eval (trm:term) (pst:Proof.state) (assert:assert) (parameters:parameter list) =
  let
    fun convert_param (Bool       _) = error "convert_param in Eval_Expression_Struct failed."
      | convert_param (Path       p) = EP.Path p
      | convert_param (Print      p) = EP.Print p
      | convert_param (String     s) = EP.String s
      | convert_param (Number     n) = EP.Number n
      | convert_param (Int        i) = EP.Int i
      | convert_param (Command    c) = EP.Command c;
    fun
      (*Eval_Connective*)
        eval' Not   [Bool b]           = EC.eval (EC.Not   (bool_to_connect    b      ))
      | eval' And   [Bool b1, Bool b2] = EC.eval (EC.And   (bools_to_connects (b1, b2)))
      | eval' Or    [Bool b1, Bool b2] = EC.eval (EC.Or    (bools_to_connects (b1, b2)))
      | eval' Nor   [Bool b1, Bool b2] = EC.eval (EC.Nor   (bools_to_connects (b1, b2)))
      | eval' Imply [Bool b1, Bool b2] = EC.eval (EC.Imply (bools_to_connects (b1, b2)))
      | eval' Ands  ands               = EC.eval (EC.Ands  (map de_bool_to_connect ands))
      | eval' Ors   ors                = EC.eval (EC.Ors   (map de_bool_to_connect ors ))
      (*Eval_Unode_Core*)
      | eval' (Eval_Parameter para_assert) params = EP.eval trm pst para_assert (map convert_param params)
      | eval' _ _ = error "eval' in From_Parameter_To_Expression.ML failed."
    val ec_result = eval' assert parameters: Eval_Connective.assert;
    val result    = ec_result |> EC.assert_connective_to_bool |> Bool;
  in
    result
  end;

end;