(* This file provides a mechanism to generate classical tactics dynamically, utilising run-time 
 * information.*)
theory Dynamic_Classical
imports Dynamic_Tactic_Generation "../Utils/More_Find_Theorems" "../Category/ListCC"
begin

ML{* structure Classical_Seed : DYNAMIC_TACTIC_GENERATOR_SEED =
struct
(*datatype safety = Safe | Haz;*)

datatype modifier = 
  Simp  of string
| Split of string
| Dest  of string
| Elim  of string
| Intro of string;

type modifiers = modifier list;

fun order' ordered [] = ordered
 |  order' (simps, splits, dests, elims, intros) (Simp  rule ::params) = order' (Simp rule::simps, splits, dests, elims, intros)  params
 |  order' (simps, splits, dests, elims, intros) (Split rule ::params) = order' (simps, Split rule::splits, dests, elims, intros) params
 |  order' (simps, splits, dests, elims, intros) (Dest  rule ::params) = order' (simps, splits, Dest rule::dests, elims, intros)  params
 |  order' (simps, splits, dests, elims, intros) (Elim  rule ::params) = order' (simps, splits, dests, Elim rule::elims, intros)  params
 |  order' (simps, splits, dests, elims, intros) (Intro rule ::params) = order' (simps, splits, dests, elims, Intro rule::intros) params

fun order (mods:modifiers) = (*(ons, arbs, rules)*)
  order' ([],[],[],[],[]) mods : (modifiers * modifiers * modifiers * modifiers * modifiers)

fun get_name (Simp  name) = name
  | get_name (Split name) = name
  | get_name (Dest  name) = name
  | get_name (Elim  name) = name
  | get_name (Intro name) = name;

val get_names = map get_name;

fun mods_to_string (mods:modifiers) =
  let 
    val prefix_if_nonnil = Utils.prefix_if_nonempty;
  in
    mods |> order |> (fn (simps, splits, dests, elims, intros) =>
      prefix_if_nonnil "simp:"  (get_names simps)
    @ prefix_if_nonnil "split:" (get_names splits)
    @ prefix_if_nonnil "dest:"  (get_names dests)
    @ prefix_if_nonnil "elim:"  (get_names elims)
    @ prefix_if_nonnil "intro:" (get_names intros))
    |> Dynamic_Utils.get_meth_nm ""
  end;

structure FT2 =  Find_Theorems2;

fun get_all_modifiers (state:Proof.state) =
  let
    val {context: Proof.context, goal: thm,...} = Proof.goal state;
    val simps     = map Simp  (FT2.get_simp_rule_names  context goal);
    val splits    = map Split (FT2.get_split_rule_names context goal);
    val elims     = map Elim  (FT2.get_elim_rule_names  context goal);
    val intros    = map Intro (FT2.get_intro_rule_names context goal);
    val dest      = map Dest  (FT2.get_dest_rule_names  context goal);
    val modifiers = simps @ splits @ elims @ intros @ dest;
  in
    modifiers : modifiers
  end;

end;
*}

ML{* structure Classical_Tactic_Generator : DYNAMIC_TACTIC_GENERATOR = 
  mk_Dynamic_Tactic_Generator (Classical_Seed);
*}

ML{* structure Dynamic_Clarsimp : DYNAMIC_TACTIC =
struct
  structure CTG = Classical_Tactic_Generator;

  fun get_state_stttacs (state:Proof.state) =
    let
      val all_modifiers    = CTG.get_all_modifiers state : CTG.modifiers;
      (* for clarsimp, I prefer not to create powerset.*)
      val all_modifierss   = map single all_modifiers |> Seq.of_list : CTG.modifiers Seq.seq;
      val stttacs = Seq.map (CTG.meth_name_n_modifiers_to_stttac_on_state "clarsimp") all_modifierss;
      type 'a stttac = 'a Dynamic_Utils.stttac;
    in 
      stttacs : Proof.state stttac Seq.seq
    end;
end;
*}

ML{* structure Dynamic_Fastforce : DYNAMIC_TACTIC =
struct
  structure CTG = Classical_Tactic_Generator;

  fun get_state_stttacs (state:Proof.state) =
    let
      val all_modifiers    = CTG.get_all_modifiers state : CTG.modifiers;
      val all_modifierss   = map single all_modifiers |> Seq.of_list : CTG.modifiers Seq.seq;
      val stttacs = Seq.map (CTG.meth_name_n_modifiers_to_stttac_on_state "fastforce") all_modifierss;
      type 'a stttac = 'a Dynamic_Utils.stttac;
    in 
      stttacs : Proof.state stttac Seq.seq
    end;
end;
*}

ML{* structure Dynamic_Auto : DYNAMIC_TACTIC =
struct
  structure CTG = Classical_Tactic_Generator;

  fun get_state_stttacs (state:Proof.state) =
    let
      val all_modifiers    = CTG.get_all_modifiers state : CTG.modifiers;
      val all_modifierss   = map single all_modifiers |> Seq.of_list : CTG.modifiers Seq.seq;
      val stttacs = Seq.map (CTG.meth_name_n_modifiers_to_stttac_on_state "auto") all_modifierss;
      type 'a stttac = 'a Dynamic_Utils.stttac;
    in 
      stttacs : Proof.state stttac Seq.seq
    end;
end;
*}

end