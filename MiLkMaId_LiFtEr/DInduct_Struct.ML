(*  Title:      PSL/MiLkMaId_LiFtEr/DInduct_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

Infrastructure to construct various induct methods.
It is similar to Dynamic (Induct) in PSL but tailored for MiLkMaId.
*)
structure Dynamic_Induct : DYNAMIC_INDUCT =
struct

datatype modifier =
  Ind  of string
| Arb  of string
| Rule of string;

open Unique_Node;

type modifiers = modifier list;

fun unode_w_aux_wo_path_to_on (unode:unode_w_aux) = #print unode |> LiFtEr_Util.dest_print |> Ind: modifier;

fun unode_w_aux_wo_path_to_arb (unode:unode_w_aux) = #print unode |> LiFtEr_Util.dest_print |> Arb: modifier;

fun strs_to_rules (strs:strings) = map Rule strs:  modifiers;

(*TODO: Double-check. This function does not flip the order of each kind of modifiers.*)
fun order (mods:modifiers) =
  let
    fun order' ordered [] = ordered
     |  order' (ons, arbs, rules) (Ind  var  :: mods) = order' (Ind var::ons, arbs,          rules           ) mods
     |  order' (ons, arbs, rules) (Arb  var  :: mods) = order' (ons,          Arb var::arbs, rules           ) mods
     |  order' (ons, arbs, rules) (Rule rule :: mods) = order' (ons,          arbs,          Rule rule::rules) mods;
    val (inds, abs, rules) = order' ([],[],[]) mods : (modifiers * modifiers * modifiers)
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