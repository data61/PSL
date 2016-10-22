(* This file provides a mechanism to generate simplification tactics dynamically, utilising run-time 
 * information.*)
theory Dynamic_Simp
imports Dynamic_Tactic_Generation "../Utils/More_Find_Theorems"
begin            

ML{* structure Simp_Seed : DYNAMIC_TACTIC_GENERATOR_SEED =
struct

datatype modifier = Add of string;

type modifiers = modifier list;

fun get_adds (consts:string list) = map Add consts;

fun order (mods:modifiers) = mods;

fun get_name (Add name) = name;

val get_names = map get_name;

fun mods_to_string (mods:modifiers) = mods |> order
  |> (fn adds => ["add:"] @ get_names adds)
  |> Dynamic_Utils.get_meth_nm "";

fun get_all_modifiers (state:Proof.state) =
  let
    val {context: Proof.context, goal: thm,...} = Proof.goal state;
    val simp_rule_names = Find_Theorems2.get_simp_rule_names context goal;
    val standard_rules  = ["arith", "algebra", "ac_simps", "field_simps", "algebra_simps", "divide_simps"]
    val all_simp_mods   = get_adds (standard_rules @ simp_rule_names);
  in
    all_simp_mods : modifiers
  end;

end;
*}

ML{* structure Simp_Tactic_Generator : DYNAMIC_TACTIC_GENERATOR = 
  mk_Dynamic_Tactic_Generator (Simp_Seed) : DYNAMIC_TACTIC_GENERATOR;
*}

ML{* structure Dynamic_Simp : DYNAMIC_TACTIC =
struct

structure STG = Simp_Tactic_Generator;

fun get_state_stttacs (state:Proof.state) =
  let
    val simp             = "simp ";
    val all_modifiers    = STG.get_all_modifiers state : STG.modifiers;
    (* for clarsimp, I prefer not to create powerset.*)
    val all_modifierss   = map single all_modifiers |> Seq.of_list : STG.modifiers Seq.seq;
    val ssstacs = Seq.map (STG.meth_name_n_modifiers_to_stttac_on_state simp) all_modifierss;
    type 'a stttac = 'a Dynamic_Utils.stttac;
  in 
    ssstacs : Proof.state stttac Seq.seq
  end;

end;
*}

end