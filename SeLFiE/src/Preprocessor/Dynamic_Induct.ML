(*  Title:      PSL/SeLFiE/src/Preprocessor/DInduct_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

Infrastructure to construct various induct methods.
It is similar to Dynamic (Induct) in PSL but tailored for MiLkMaId.
*)
signature DYNAMIC_INDUCT =
sig

datatype modifier = 
  Ind  of string
| Arb  of string
| Rule of string;

type modifiers = modifier list;

val strs_to_rules             : strings -> modifiers;
val order                     : modifiers -> (modifiers * modifiers * modifiers);
val same_mod                  : (modifier  * modifier ) -> bool;
val same_mods                 : (modifiers * modifiers) -> bool;
val filter_inds               : modifiers -> modifiers;
val filter_arbs               : modifiers -> modifiers;
val filter_rules              : modifiers -> modifiers;

end;

structure Dynamic_Induct : DYNAMIC_INDUCT =
struct

datatype modifier =
  Ind  of string
| Arb  of string
| Rule of string;

open Unique_Node;

type modifiers = modifier list;

fun strs_to_rules (strs:strings) = map Rule strs:  modifiers;

fun order (mods:modifiers) =
  let
    fun order' ordered [] = ordered
     |  order' (ons, arbs, rules) (Ind  var  :: mods) = order' (Ind var::ons, arbs,          rules           ) mods
     |  order' (ons, arbs, rules) (Arb  var  :: mods) = order' (ons,          Arb var::arbs, rules           ) mods
     |  order' (ons, arbs, rules) (Rule rule :: mods) = order' (ons,          arbs,          Rule rule::rules) mods;
    val (inds, abs, rules) = order' ([],[],[]) mods : (modifiers * modifiers * modifiers);
  in
    (rev inds, rev abs, rev rules)
  end;

fun same_mod     (Ind  str1, Ind  str2) = str1 = str2
  | same_mod     (Arb  str1, Arb  str2) = str1 = str2
  | same_mod     (Rule str1, Rule str2) = str1 = str2
  | same_mod      _                     = false

fun same_mods (mods1, mods2) =  if length mods1 = length mods2
  then forall same_mod (mods1 ~~ mods2)
  else false;

val filter_inds  = filter (fn modi => case modi of Ind  _ => true | _ => false);
val filter_arbs  = filter (fn modi => case modi of Arb  _ => true | _ => false);
val filter_rules = filter (fn modi => case modi of Rule _ => true | _ => false);

end;