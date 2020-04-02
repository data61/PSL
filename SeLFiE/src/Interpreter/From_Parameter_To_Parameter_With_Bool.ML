(*  Title:      PSL/SeLFeE/src/From_Parameter_To_Parameter_With_Bool.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
structure Parameter_With_Bool: EVAL_PARAMETER_WITH_BOOL =
struct

structure EP = Eval_Parameter;
structure SU = SeLFiE_Util;

type connective = Eval_Bool.assert;
type command    = Pattern.command;

structure EB = Eval_Bool;

fun de_Bool (EP.Non_Path (EP.Bool c)) = c
  | de_Bool  _                        = error "de_Bool in from_Parameter_to_Parameter_With_Bool failed.";

val bool_to_connect    = EB.bool_to_assert;
val bools_to_connects  = Utils.map_pair bool_to_connect;
val de_bool_to_connect = bool_to_connect o de_Bool;

fun eval (trm:term) (pst:Proof.state) (induct_args:SU.induct_arguments) (assert:SU.assert) (parameters:EP.literals) =
  let
    fun
      (*Eval_Connective*)
        eval' SU.Not   [EP.Non_Path (EP.Bool b)]                            = EB.eval (EB.Not   (bool_to_connect    b      ))
      | eval' SU.And   [EP.Non_Path (EP.Bool b1), EP.Non_Path (EP.Bool b2)] = EB.eval (EB.And   (bools_to_connects (b1, b2)))
      | eval' SU.Or    [EP.Non_Path (EP.Bool b1), EP.Non_Path (EP.Bool b2)] = EB.eval (EB.Or    (bools_to_connects (b1, b2)))
      | eval' SU.Nor   [EP.Non_Path (EP.Bool b1), EP.Non_Path (EP.Bool b2)] = EB.eval (EB.Nor   (bools_to_connects (b1, b2)))
      | eval' SU.Imply [EP.Non_Path (EP.Bool b1), EP.Non_Path (EP.Bool b2)] = EB.eval (EB.Imply (bools_to_connects (b1, b2)))
      | eval' SU.Ands   ands                                                = EB.eval (EB.Ands  (map de_bool_to_connect ands))
      | eval' SU.Ors    ors                                                 = EB.eval (EB.Ors   (map de_bool_to_connect ors ))
      (*Eval_Unode_Core*)
      | eval' (SU.Atomic atomic_assert) params = EP.eval trm pst induct_args atomic_assert params
      | eval' _ _ = error "eval' in Parameter_With_Bool failed."
    val ec_result = eval' assert parameters: Eval_Bool.assert;
    val result    = ec_result |> EB.assert_to_bool |> EP.Bool |> EP.Non_Path;
  in
    result
  end;

end;