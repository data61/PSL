(*  Title:      PSL/SeLFeE/src/Eval_Parameter_With_Bool.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

    Eval_Bool_With_Parameter has constructs from Eval_Bool.
    We have to have the boolean operators this way to implement quantifiers in later steps.
*)
(*** signature: EVAL_PARAMETER_WITH_BOOL ***)
signature EVAL_PARAMETER_WITH_BOOL =
sig

val eval: Proof.state -> Gen_Path_To_Unode.gen_path_to_unode_table -> SeLFiE_Util.induct_arguments -> SeLFiE_Util.assert -> Eval_Parameter.literal Seq.seq -> Eval_Parameter.literal;

end;

(*** structure: Eval_Parameter_With_Bool ***)
structure Eval_Parameter_With_Bool: EVAL_PARAMETER_WITH_BOOL =
struct

structure EP = Eval_Parameter;
structure SU = SeLFiE_Util;
structure EB = Eval_Bool;

type connective = Eval_Bool.assert;
type command    = Pattern.command;

fun eval (pst:Proof.state) (term_tables:Gen_Path_To_Unode.gen_path_to_unode_table) (induct_args:SU.induct_arguments) (assert:SU.assert) (parameters:EP.literal Seq.seq) =
  let
    fun take_bool (EP.Non_Path (EP.Bool b)) = b
      | take_bool  _                        = error "take_bool";
    val non_path_lit_to_connect = EB.bool_to_assert o take_bool;
    fun
      (*Eval_Connective*)
        eval' SU.Not   lazy_params = EB.eval (EB.Not   (non_path_lit_to_connect (Seq.hd lazy_params)))
      | eval' SU.And   lazy_params = EB.eval (EB.And   (Seq.map non_path_lit_to_connect lazy_params))
      | eval' SU.Or    lazy_params = EB.eval (EB.Or    (Seq.map non_path_lit_to_connect lazy_params))
      | eval' SU.Nor   lazy_params = EB.eval (EB.Nor   (Seq.map non_path_lit_to_connect lazy_params))
      | eval' SU.Imply lazy_params = EB.eval (EB.Imply (Seq.map non_path_lit_to_connect lazy_params))
      | eval' SU.Ands  lazy_params = EB.eval (EB.Ands  (Seq.map non_path_lit_to_connect lazy_params))
      | eval' SU.Ors   lazy_params = EB.eval (EB.Ors   (Seq.map non_path_lit_to_connect lazy_params))
      (*Eval_Unode_Core*)
      | eval' (SU.Atomic atomic_assert) lazy_params = EP.eval pst term_tables induct_args atomic_assert (Seq.list_of lazy_params)
    val ec_result = eval' assert parameters: Eval_Bool.assert;
    val result    = ec_result |> EB.assert_to_bool |> EP.Bool |> EP.Non_Path;
  in
    result
  end;

end;