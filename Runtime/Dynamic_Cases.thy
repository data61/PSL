(* This file provides a mechanism to generate cases tactics dynamically, utilising run-time
 * information.*)
theory Dynamic_Cases
imports
  Dynamic_Tactic_Generation
  "../Utils/More_Find_Theorems"
begin

ML{* structure Cases_Seed : DYNAMIC_TACTIC_GENERATOR_SEED =
struct

datatype modifier = On of string;

type modifiers = modifier list;

fun get_ons   (fvars:string list) = map On fvars;

fun order (mods:modifiers) = mods;

fun get_name (On name) = name;

val get_names = map get_name;

fun mods_to_string (mods:modifiers) =
    mods |> order |> (fn ons => get_names ons |> Dynamic_Utils.get_meth_nm "");

fun get_all_modifiers (state:Proof.state) =
  let
    val {goal: thm,...} = Proof.goal state;
    val free_var_names   = Isabelle_Utils.get_free_var_names_in_thm goal;
    val all_cases_mods  = get_ons free_var_names;
  in
    all_cases_mods : modifiers
  end;

end;
*}

ML{* structure Cases_Tactic_Generator : DYNAMIC_TACTIC_GENERATOR = 
  mk_Dynamic_Tactic_Generator (Cases_Seed);
*}

ML{* structure Dynamic_Cases : DYNAMIC_TACTIC =
struct

structure CTG = Cases_Tactic_Generator;

fun get_state_stttacs (state:Proof.state) =
  let
    val induct         = "cases";
    val all_modifiers  = CTG.get_all_modifiers state : CTG.modifiers;
    val all_modifierss   = map single all_modifiers |> Seq.of_list : CTG.modifiers Seq.seq;
    val stttacs        = Seq.map (CTG.meth_name_n_modifiers_to_stttac_on_state induct) all_modifierss;
    type 'a stttac = 'a Dynamic_Utils.stttac;
  in 
    stttacs : Proof.state stttac Seq.seq
  end;

end;
*}

end