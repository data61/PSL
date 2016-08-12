(* This file provides a mechanism to generate e-rule tactics dynamically, utilising run-time 
 * information.*)
theory Dynamic_ERule
imports Dynamic_Rule
begin

ML{* structure Erule_Seed : DYNAMIC_TACTIC_GENERATOR_SEED =
struct

open Rule_Seed_Base;

fun get_all_modifiers (state:Proof.state) =
  let
    val {context: Proof.context, goal: thm,...} = Proof.goal state;
    val intros = map Rule (Find_Theorems2.get_elim_rule_names context goal);
  in
    intros : modifiers
  end;

end;
*}

ML{* structure Erule_Tactic_Generator : DYNAMIC_TACTIC_GENERATOR =
  mk_Dynamic_Tactic_Generator (Erule_Seed);
*}

ML{* structure Dynamic_Erule : DYNAMIC_TACTIC =
struct

structure RTG = Erule_Tactic_Generator;

fun get_state_stttacs (state:Proof.state) =
  let
    val rule           = "HOL.erule";
    val all_modifiers  = RTG.get_all_modifiers state : RTG.modifiers;
    (* for erule, I prefer not to create powerset.*)
    val all_modifierss = map single all_modifiers |> Seq.of_list : RTG.modifiers Seq.seq;
    val stttacs        = Seq.map (RTG.meth_name_n_modifiers_to_stttac_on_state rule) all_modifierss;
    type 'a stttac     = 'a Dynamic_Utils.stttac;
  in
    stttacs : Proof.state stttac Seq.seq
  end;

end;
*}

end