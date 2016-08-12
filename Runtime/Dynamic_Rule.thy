(* This file provides a mechanism to generate rule tactics dynamically, utilising run-time 
 * information.*)
theory Dynamic_Rule
imports Dynamic_Tactic_Generation "../Utils/More_Find_Theorems"
begin

ML{* structure Rule_Seed_Base =
struct

datatype modifier = Rule of string;

type modifiers = modifier list;

fun order (mods:modifiers) = mods;

fun get_name (Rule name) = name;

val get_names = map get_name;

fun mods_to_string (mods:modifiers) =
  mods |> order |> (fn rules => get_names rules) |> Dynamic_Utils.get_meth_nm "";

end;
*}

ML{* structure Rule_Seed : DYNAMIC_TACTIC_GENERATOR_SEED =
struct

open Rule_Seed_Base;

fun get_all_modifiers (state:Proof.state) =
  let
    val {context: Proof.context, goal: thm,...} = Proof.goal state;
    val intros = map Rule (Find_Theorems2.get_intro_rule_names context goal);
  in
    intros : modifiers
  end;

end;
*}

ML{* structure Rule_Tactic_Generator : DYNAMIC_TACTIC_GENERATOR =
  mk_Dynamic_Tactic_Generator (Rule_Seed);
*}

ML{* structure Dynamic_Rule : DYNAMIC_TACTIC =
struct

structure RTG = Rule_Tactic_Generator;

fun get_state_stttacs (state:Proof.state) =
  let
    val rule           = "HOL.rule";
    val all_modifiers  = RTG.get_all_modifiers state : RTG.modifiers;
    (* for rule, I prefer not to create powerset.*)
    val all_modifierss = map single all_modifiers |> Seq.of_list : RTG.modifiers Seq.seq;
    val stttacs        = Seq.map (RTG.meth_name_n_modifiers_to_stttac_on_state rule) all_modifierss;
    type 'a stttac     = 'a Dynamic_Utils.stttac;
  in
    stttacs : Proof.state stttac Seq.seq
  end;

end;
*}

end