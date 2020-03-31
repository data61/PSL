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

datatype parameter = Path of path | Non_Path of SeLFiE_Util.non_path_parameter;

type parameters = parameter list;

structure EB = Eval_Bool;

fun de_Bool (Non_Path (SU.Bool c)) = c
  | de_Bool  _                     = error "de_Bool in Eval_Expression_Struct failed.";

val bool_to_connect    = EB.bool_to_assert;
val bools_to_connects  = Utils.map_pair bool_to_connect;
val de_bool_to_connect = bool_to_connect o de_Bool;

fun eval (trm:term) (pst:Proof.state) (induct_args:SeLFiE_Util.induct_arguments) (assert:SU.assert) (parameters:parameter list) =
  let
    fun convert_param (Path                 p ) = EP.Path p
      | convert_param (Non_Path (SU.Bool    _)) = error "convert_param in Eval_Expression_Struct failed."
      | convert_param (Non_Path (SU.Print   p)) = EP.Print p
      | convert_param (Non_Path (SU.Number  n)) = EP.Number n
      | convert_param (Non_Path (SU.Command c)) = EP.Command c;
    fun
      (*Eval_Connective*)
        eval' SU.Not   [Non_Path (SU.Bool b)]                         = EB.eval (EB.Not   (bool_to_connect    b      ))
      | eval' SU.And   [Non_Path (SU.Bool b1), Non_Path (SU.Bool b2)] = EB.eval (EB.And   (bools_to_connects (b1, b2)))
      | eval' SU.Or    [Non_Path (SU.Bool b1), Non_Path (SU.Bool b2)] = EB.eval (EB.Or    (bools_to_connects (b1, b2)))
      | eval' SU.Nor   [Non_Path (SU.Bool b1), Non_Path (SU.Bool b2)] = EB.eval (EB.Nor   (bools_to_connects (b1, b2)))
      | eval' SU.Imply [Non_Path (SU.Bool b1), Non_Path (SU.Bool b2)] = EB.eval (EB.Imply (bools_to_connects (b1, b2)))
      | eval' SU.Ands  ands                                           = EB.eval (EB.Ands  (map de_bool_to_connect ands))
      | eval' SU.Ors   ors                                            = EB.eval (EB.Ors   (map de_bool_to_connect ors ))
      (*Eval_Unode_Core*)
      | eval' (SU.Atomic atomic_assert) params = EP.eval trm pst induct_args atomic_assert (map convert_param params)
      | eval' _ _ = error "eval' in From_Parameter_To_Expression.ML failed."
    val ec_result = eval' assert parameters: Eval_Bool.assert;
    val result    = ec_result |> EB.assert_to_bool |> SU.Bool |> Non_Path;
  in
    result
  end;

end;