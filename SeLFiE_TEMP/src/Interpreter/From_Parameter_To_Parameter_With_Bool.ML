(*  Title:      PSL/SeLFeE/src/From_Parameter_To_Parameter_With_Bool.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

    This file contains signatures, structures, and functors to support lambda abstraction in SeLFiE.
    The three functions (shift, subst, and eval) in this file are inspired by the functions of the 
    same names found in "ML for the Working Programmer" written by Larry C. Paulson.
*)
functor from_Parameter_to_Parameter_With_Bool (Eval_Parameter:EVAL_PARAMETER): EVAL_PARAMETER_WITH_BOOL  =
struct

structure EP = Eval_Parameter;

type connective = Eval_Bool.assert;
type path       = EP.path;
type print      = SeLFiE_Util.print;
type number     = Eval_Number.number;
type command    = Pattern.command;

datatype parameter =
  Bool    of bool
| Path    of path
| Print   of print
| String  of string(*redundant?*)
| Number  of number
| Int     of int
| Command of command;

type parameters = parameter list;

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

fun convert_parameter_assert Is_Cnst          = EP.Is_Cnst
  | convert_parameter_assert Is_Free          = EP.Is_Free
  | convert_parameter_assert Is_Var           = EP.Is_Var
  | convert_parameter_assert Is_Bound         = EP.Is_Bound
  | convert_parameter_assert Is_Lambda        = EP.Is_Lambda
  | convert_parameter_assert Is_App           = EP.Is_App
  | convert_parameter_assert Has_Same_Prnt_As = EP.Has_Same_Prnt_As
  | convert_parameter_assert Is_In_Trm_Prnt   = EP.Is_In_Trm_Prnt
  | convert_parameter_assert Is_Deeper_Than   = EP.Is_Deeper_Than
  | convert_parameter_assert Is_Shallower_Than= EP.Is_Shallower_Than
  | convert_parameter_assert Is_Path_Above    = EP.Is_Path_Above
  | convert_parameter_assert Is_Same_Path_As  = EP.Is_Same_Path_As
  | convert_parameter_assert Are_Same_Prints  = EP.Are_Same_Prints
  | convert_parameter_assert Is_Printed_As    = EP.Is_Printed_As
  | convert_parameter_assert Unode_Has_Print  = EP.Unode_Has_Print
  | convert_parameter_assert Are_Same_Number  = EP.Are_Same_Number
  | convert_parameter_assert Is_Less_Than     = EP.Is_Less_Than
  | convert_parameter_assert Is_Int           = EP.Is_Int;

datatype assert =
  Not
| And
| Or
| Nor
| Imply
| Ands
| Ors
| Atomic of atomic_assert;

structure EB = Eval_Bool;

fun de_Bool (Bool c) = c
  | de_Bool  _       = error "de_Bool in Eval_Expression_Struct failed.";

val bool_to_connect    = EB.bool_to_assert;
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
        eval' Not   [Bool b]           = EB.eval (EB.Not   (bool_to_connect    b      ))
      | eval' And   [Bool b1, Bool b2] = EB.eval (EB.And   (bools_to_connects (b1, b2)))
      | eval' Or    [Bool b1, Bool b2] = EB.eval (EB.Or    (bools_to_connects (b1, b2)))
      | eval' Nor   [Bool b1, Bool b2] = EB.eval (EB.Nor   (bools_to_connects (b1, b2)))
      | eval' Imply [Bool b1, Bool b2] = EB.eval (EB.Imply (bools_to_connects (b1, b2)))
      | eval' Ands  ands               = EB.eval (EB.Ands  (map de_bool_to_connect ands))
      | eval' Ors   ors                = EB.eval (EB.Ors   (map de_bool_to_connect ors ))
      (*Eval_Unode_Core*)
      | eval' (Atomic atomic_assert) params = EP.eval trm pst (convert_parameter_assert atomic_assert) (map convert_param params)
      | eval' _ _ = error "eval' in From_Parameter_To_Expression.ML failed."
    val ec_result = eval' assert parameters: Eval_Bool.assert;
    val result    = ec_result |> EB.assert_to_bool |> Bool;
  in
    result
  end;

end;