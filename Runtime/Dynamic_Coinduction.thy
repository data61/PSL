(* This file provides a mechanism to generate induct tactics dynamically, utilising run-time 
 * information.*)
theory Dynamic_Coinduction
imports
  Dynamic_Tactic_Generation
  "../Utils/More_Find_Theorems"
begin

ML{* structure Coinduction_Seed : DYNAMIC_TACTIC_GENERATOR_SEED =
struct

datatype modifier = 
  On        of string
| Arbitrary of string
| Rule      of string;

type modifiers = modifier list;

fun get_ons   (fvars:string list) = map On fvars;
fun get_arbs  (fvars:string list) = map Arbitrary fvars;
fun get_rules (rules:string list) = map Rule rules;

fun order' ordered [] = ordered
 |  order' (ons, arbs, rules) (On        var :: mods) = order' (On var::ons, arbs, rules) mods
 |  order' (ons, arbs, rules) (Arbitrary var :: mods) = order' (ons, Arbitrary var::arbs, rules) mods
 |  order' (ons, arbs, rules) (Rule     rule :: mods) = order' (ons, arbs, Rule rule::rules) mods;

fun order (mods:modifiers) = (*(ons, arbs, rules)*)
  order' ([],[],[]) mods : (modifiers * modifiers * modifiers)

fun get_name (On        name) = name
  | get_name (Arbitrary name) = name
  | get_name (Rule      name) = name;

val get_names = map get_name;

fun mods_to_string (mods:modifiers) =
  let 
    val prefix_if_nonnil = Utils.prefix_if_nonempty;
  in
    mods |> order |> (fn (ons, arbs, rules) =>
    get_names ons
    @ prefix_if_nonnil "arbitrary:" (get_names arbs)
    @ prefix_if_nonnil "rule:"      (get_names rules))
    |> Dynamic_Utils.get_meth_nm ""
  end;

fun get_all_modifiers (state:Proof.state) =
  let
    val {context:Proof.context, goal: thm,...} = Proof.goal state;
    val free_var_names   = Isabelle_Utils.get_free_var_names_in_thm goal;
    val induct_rules     = Find_Theorems2.get_coinduction_rule_names context goal : string list;
    val all_induct_mods  = get_ons free_var_names @ get_arbs free_var_names @ get_rules induct_rules;
  in
    all_induct_mods : modifiers
  end;

end;
*}

ML{* structure Coinduction_Tactic_Generator : DYNAMIC_TACTIC_GENERATOR = 
  mk_Dynamic_Tactic_Generator (Coinduction_Seed);
*}

ML{* structure Dynamic_Coinduction : DYNAMIC_TACTIC =
struct

structure CITG = Coinduction_Tactic_Generator;

fun get_state_stttacs (state:Proof.state) =
  let
    val coinduction    = "coinduction";
    val all_modifiers  = CITG.get_all_modifiers state : CITG.modifiers;
    (* for clarsimp, I prefer not to create powerset.*)
    val all_modifierss = Seq2.powerset (Seq.of_list all_modifiers)
                      |> Seq.map Seq.list_of: CITG.modifiers Seq.seq;
    val stttacs        = Seq.map (CITG.meth_name_n_modifiers_to_stttac_on_state coinduction) all_modifierss;
    type 'a stttac = 'a Dynamic_Utils.stttac;
  in 
    stttacs : Proof.state stttac Seq.seq
  end;

end;
*}

end