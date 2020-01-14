(*  Title:      PSL/SeLFeE/src/From_Parameter_To_Parameter_With_Bool.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

    This file contains signatures, structures, and functors to support lambda abstraction in SeLFiE.
    The three functions (shift, subst, and eval) in this file are inspired by the functions of the 
    same names found in "ML for the Working Programmer" written by Larry C. Paulson.
*)
functor from_Parameter_to_Parameter_With_Bool (Eval_Parameter:EVAL_PARAMETER): EVAL_PARAMETER_WITH_BOOL  =
struct

structure EP = Eval_Parameter;
structure SU = SeLFiE_Util;

type connective = Eval_Bool.assert;
type path       = EP.path;
type command    = Pattern.command;

datatype parameter =
  Bool    of bool
| Path    of path
| Print   of string
| String  of string(*redundant?*)
| Number  of int
| Int     of int
| Command of command;

type parameters = parameter list;

structure EB = Eval_Bool;

fun de_Bool (Bool c) = c
  | de_Bool  _       = error "de_Bool in Eval_Expression_Struct failed.";

val bool_to_connect    = EB.bool_to_assert;
val bools_to_connects  = Utils.map_pair bool_to_connect;
val de_bool_to_connect = bool_to_connect o de_Bool;

fun eval (trm:term) (pst:Proof.state) (assert:SU.assert) (parameters:parameter list) =
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
        eval' SU.Not   [Bool b]           = EB.eval (EB.Not   (bool_to_connect    b      ))
      | eval' SU.And   [Bool b1, Bool b2] = EB.eval (EB.And   (bools_to_connects (b1, b2)))
      | eval' SU.Or    [Bool b1, Bool b2] = EB.eval (EB.Or    (bools_to_connects (b1, b2)))
      | eval' SU.Nor   [Bool b1, Bool b2] = EB.eval (EB.Nor   (bools_to_connects (b1, b2)))
      | eval' SU.Imply [Bool b1, Bool b2] = EB.eval (EB.Imply (bools_to_connects (b1, b2)))
      | eval' SU.Ands  ands               = EB.eval (EB.Ands  (map de_bool_to_connect ands))
      | eval' SU.Ors   ors                = EB.eval (EB.Ors   (map de_bool_to_connect ors ))
      (*Eval_Unode_Core*)
      | eval' (SU.Atomic atomic_assert) params = EP.eval trm pst atomic_assert (map convert_param params)
      | eval' _ _ = error "eval' in From_Parameter_To_Expression.ML failed."
    val ec_result = eval' assert parameters: Eval_Bool.assert;
    val result    = ec_result |> EB.assert_to_bool |> Bool;
  in
    result
  end;

end;