(*  Title:      Dynamic_Tactic_Generation.ML
    Author:     Yutaka Nagashima, Data61, CSIRO

This file provides a mechanism to generate several state monad based tactics at runtime.
Boiler-plate programming is avoided by using ML's module system.
*)

(*** DYNAMIC_TACTIC_GENERATOR_SEED: makes inputs to tactic-generator. ***)
(*
  This following provides a mechanism to derive functions that are necessary to generate tactics at 
  run-time in the PSL framework. Essentially, the functor, "mk_Dynamic_Tactic_Generator", abstracts 
  functions that are commonly observed when dynamically generating tactics, thus avoiding
  code-duplication.
*)
signature DYNAMIC_TACTIC_GENERATOR_SEED =
sig
  type modifier;
  type modifiers = modifier list;
  val  get_all_modifiers : Proof.state -> modifiers;
  (*mods_to_string should reorder parameters and remove duplicated modifier declarations.*)
  val  mods_to_string    : modifiers -> string;
end;

(*** DYNAMIC_TACTIC_GENERATOR: makes tactic-generator. ***)
signature DYNAMIC_TACTIC_GENERATOR =
sig
  include DYNAMIC_TACTIC_GENERATOR_SEED;
  val meth_name_n_modifiers_to_nontac_on_state: string -> modifiers -> Proof.state Dynamic_Utils.nontac;
  val meth_name_n_modifiers_to_logtac_on_state: string -> modifiers -> Proof.state Dynamic_Utils.logtac;
  val meth_name_n_modifiers_to_stttac_on_state: string -> modifiers -> Proof.state Dynamic_Utils.stttac;
end;

(*** mk_Dynamic_Tactic_Generator: makes DYNAMIC_TACTIC_GENERATOR from DYNAMIC_TACTIC_GENERATOR_SEED. ***)
functor mk_Dynamic_Tactic_Generator (Seed:DYNAMIC_TACTIC_GENERATOR_SEED) : DYNAMIC_TACTIC_GENERATOR =
struct
  open Seed;
  structure DG = Dynamic_Utils;

  fun general_case (meth_name:string) (mods:modifiers) =
    let
      val attributes_name   = mods_to_string mods: string;
      val method_str_w_attr = meth_name ^ attributes_name;
      val nontac_on_state  = DG.string_to_nontac_on_pstate method_str_w_attr
        |> Isabelle_Utils.TIMEOUT_in 0.3: Proof.state DG.nontac
        handle THM _ => K Seq.empty;
      val trace_node       = DG.Apply {using = [], methN = method_str_w_attr, back = 0};
      val logtac_on_state  = DG.nontac_to_logtac trace_node nontac_on_state : Proof.state DG.logtac;
      val stttac_on_state  = DG.logtac_to_stttac logtac_on_state;
    in
      (nontac_on_state, logtac_on_state, stttac_on_state)
    end;

  val meth_name_n_modifiers_to_nontac_on_state = #1 oo general_case;
  val meth_name_n_modifiers_to_logtac_on_state = #2 oo general_case;
  val meth_name_n_modifiers_to_stttac_on_state = #3 oo general_case;
end;

(*** DYNAMIC_TACTIC: makes a series of state-monad based tactics from proof state. ***)
signature DYNAMIC_TACTIC =
sig
  val get_state_stttacs  : Proof.state -> Proof.state Dynamic_Utils.stttac Seq.seq;
end;

(*** DYNAMIC_TACTIC_GENERATION ***)
signature DYNAMIC_TACTIC_GENERATION =
sig
  type get_stttacs = Proof.state -> Proof.state Dynamic_Utils.stttac Seq.seq;
  val rule        : get_stttacs;
  val erule       : get_stttacs;
  val simp        : get_stttacs;
  val induct      : get_stttacs;
  val induct_tac  : get_stttacs;
  val coinduction : get_stttacs;
  val cases       : get_stttacs;
  val case_tac    : get_stttacs;
  val clarsimp    : get_stttacs;
  val fastforce   : get_stttacs;
  val auto        : get_stttacs;
end;

(*** Dynamic_Tactic_Generation ***)
structure Dynamic_Tactic_Generation =
struct
(** Rule_Seed_Base: Shared by Rule_Seed and Erule_Seed. **)
structure Rule_Seed_Base =
struct

datatype modifier = Rule of string;

type modifiers = modifier list;

fun order (mods:modifiers) = mods;

fun get_name (Rule name) = name;

val get_names = map get_name;

fun mods_to_string (mods:modifiers) =
  mods |> order |> (fn rules => get_names rules) |> Dynamic_Utils.get_meth_nm "";

end;

(** Dynamic_Rule: The tactic generator for the rule method. **)
structure Dynamic_Rule : DYNAMIC_TACTIC =
struct

(* Rule_Seed: The seed to make the tactic-generator for the rule-method. *)
structure Rule_Seed : DYNAMIC_TACTIC_GENERATOR_SEED =
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

(* RTG: Rule Tactic Generator. *)
structure RTG : DYNAMIC_TACTIC_GENERATOR = mk_Dynamic_Tactic_Generator (Rule_Seed);

fun get_state_stttacs (state:Proof.state) =
  let
    val rule           = "HOL.rule";
    val all_modifiers  = RTG.get_all_modifiers state : RTG.modifiers;
    (*For rule, I prefer not to create powerset.*)
    val all_modifierss = map single all_modifiers |> Seq.of_list : RTG.modifiers Seq.seq;
    val stttacs        = Seq.map (RTG.meth_name_n_modifiers_to_stttac_on_state rule) all_modifierss;
    type 'a stttac     = 'a Dynamic_Utils.stttac;
  in
    stttacs : Proof.state stttac Seq.seq
  end;

end;

(** Dynamic_Erule: The tactic generator for the erule method. **)
structure Dynamic_Erule : DYNAMIC_TACTIC =
struct

(* Erule_Seed: The seed to make the tactic generator for the erule method. *)
structure Erule_Seed : DYNAMIC_TACTIC_GENERATOR_SEED =
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

(* ETG: Erule Tactic Generator. *)
structure ETG : DYNAMIC_TACTIC_GENERATOR = mk_Dynamic_Tactic_Generator (Erule_Seed);

fun get_state_stttacs (state:Proof.state) =
  let
    val rule           = "HOL.erule";
    val all_modifiers  = ETG.get_all_modifiers state : ETG.modifiers;
    (*for erule, I prefer not to create powerset.*)
    val all_modifierss = map single all_modifiers |> Seq.of_list : ETG.modifiers Seq.seq;
    val stttacs        = Seq.map (ETG.meth_name_n_modifiers_to_stttac_on_state rule) all_modifierss;
    type 'a stttac     = 'a Dynamic_Utils.stttac;
  in
    stttacs : Proof.state stttac Seq.seq
  end;

end;

(** Dynamic_Simp: The tactic generator for the simp method. **)
structure Dynamic_Simp : DYNAMIC_TACTIC =
struct

(* Simp_Seed: The seed to make the tactic-generator for the simp method. *)
structure Simp_Seed : DYNAMIC_TACTIC_GENERATOR_SEED =
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

(* STG: Simp_Tactic_Generator *)
structure STG : DYNAMIC_TACTIC_GENERATOR =
  mk_Dynamic_Tactic_Generator (Simp_Seed) : DYNAMIC_TACTIC_GENERATOR;

fun get_state_stttacs (state:Proof.state) =
  let
    val simp             = "simp ";
    val all_modifiers    = STG.get_all_modifiers state : STG.modifiers;
    (*For simp, I prefer not to create powerset.*)
    val all_modifierss   = map single all_modifiers |> Seq.of_list : STG.modifiers Seq.seq;
    val ssstacs = Seq.map (STG.meth_name_n_modifiers_to_stttac_on_state simp) all_modifierss;
    type 'a stttac = 'a Dynamic_Utils.stttac;
  in 
    ssstacs : Proof.state stttac Seq.seq
  end;

end;

(** Dynamic_Induct: The tactic generator for the induct method. **)
structure Dynamic_Induct : DYNAMIC_TACTIC =
struct

(* Induct_Seed: The seed to make the tactic-generator for the induct method. *)
structure Induct_Seed : DYNAMIC_TACTIC_GENERATOR_SEED =
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
    val {context: Proof.context, goal: thm,...} = Proof.goal state;
    val free_var_names   = Isabelle_Utils.get_free_var_names_in_1st_subg goal;
    val induct_rules     = Find_Theorems2.get_induct_rule_names context goal : string list;
    val all_induct_mods  = get_ons free_var_names @ get_arbs free_var_names @ get_rules induct_rules;
  in
    all_induct_mods : modifiers
  end;

end;

(* ITG: Induct_Tactic_Generator. *)
structure ITG : DYNAMIC_TACTIC_GENERATOR = mk_Dynamic_Tactic_Generator (Induct_Seed);

fun get_state_stttacs (state:Proof.state) =
  let
    val induct         = "induct";
    val all_modifiers  = ITG.get_all_modifiers state : ITG.modifiers;
    val all_modifierss = Seq2.powerset (Seq.of_list all_modifiers)
                      |> Seq.map Seq.list_of: ITG.modifiers Seq.seq;
    val stttacs        = Seq.map (ITG.meth_name_n_modifiers_to_stttac_on_state induct) all_modifierss;
    type 'a stttac = 'a Dynamic_Utils.stttac;
  in
    stttacs : Proof.state stttac Seq.seq
  end;

end;

(** Dynamic_Induct_Tac: The tactic generator for the induct_tac method. **)
structure Dynamic_Induct_Tac : DYNAMIC_TACTIC =
struct

(* Induct_Tac_Seed: The seed to make the tactic-generator for the induct_tac method. *)
structure Induct_Tac_Seed : DYNAMIC_TACTIC_GENERATOR_SEED =
struct

datatype modifier =
  On        of string
| Rule      of string;

type modifiers = modifier list;

fun get_ons   (fvars:string list) = map On fvars;
fun get_rules (rules:string list) = map Rule rules;

fun order' ordered [] = ordered
 |  order' (ons, rules) (On        var :: mods) = order' (On var::ons, rules) mods
 |  order' (ons, rules) (Rule     rule :: mods) = order' (ons, Rule rule::rules) mods;

fun order (mods:modifiers) = (*(ons, rules)*)
  order' ([],[]) mods : (modifiers * modifiers)

fun get_name (On        name) = name
  | get_name (Rule      name) = name;

val get_names = map get_name;

fun mods_to_string (mods:modifiers) =
  let
    val prefix_if_nonnil = Utils.prefix_if_nonempty;
  in
    mods |> order |> (fn (ons, rules) =>
    get_names ons
    @ prefix_if_nonnil "rule:"      (get_names rules))
    |> Dynamic_Utils.get_meth_nm ""
  end;

fun get_all_modifiers (state:Proof.state) =
  let
    val {context: Proof.context, goal: thm,...} = Proof.goal state;
    val all_var_names   = Isabelle_Utils.get_all_var_names_in_1st_subg goal;
    val induct_rules     = Find_Theorems2.get_induct_rule_names context goal : string list;
    val all_induct_mods  = get_ons all_var_names @ get_rules induct_rules;
  in
    all_induct_mods : modifiers
  end;

end;

(* ITTG: Induct_Tac_Tactic_Generator *)
structure ITTG : DYNAMIC_TACTIC_GENERATOR =
  mk_Dynamic_Tactic_Generator (Induct_Tac_Seed);

fun get_state_stttacs (state:Proof.state) =
  let
    val induct         = "induct_tac";
    val all_modifiers  = ITTG.get_all_modifiers state : ITTG.modifiers;
    val all_modifierss = Seq2.powerset (Seq.of_list all_modifiers)
                      |> Seq.map Seq.list_of: ITTG.modifiers Seq.seq;
    val stttacs        = Seq.map (ITTG.meth_name_n_modifiers_to_stttac_on_state induct) all_modifierss;
    type 'a stttac = 'a Dynamic_Utils.stttac;
  in 
    stttacs : Proof.state stttac Seq.seq
  end;

end;

(** Dynamic_Coinduction: The tactic generator for the coinduction method. **)
structure Dynamic_Coinduction : DYNAMIC_TACTIC =
struct

(* Coinduction_Seed: The seed to make the tactic-generator for the coinduction method. *)
structure Coinduction_Seed : DYNAMIC_TACTIC_GENERATOR_SEED =
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
    val free_var_names   = Isabelle_Utils.get_free_var_names_in_1st_subg goal;
    val induct_rules     = Find_Theorems2.get_coinduction_rule_names context goal : string list;
    val all_induct_mods  = get_ons free_var_names @ get_arbs free_var_names @ get_rules induct_rules;
  in
    all_induct_mods : modifiers
  end;

end;

(* CITG: Coinduction_Tactic_Generator *)
structure CITG : DYNAMIC_TACTIC_GENERATOR = mk_Dynamic_Tactic_Generator (Coinduction_Seed);

fun get_state_stttacs (state:Proof.state) =
  let
    val coinduction    = "coinduction";
    val all_modifiers  = CITG.get_all_modifiers state : CITG.modifiers;
    val all_modifierss = Seq2.powerset (Seq.of_list all_modifiers)
                      |> Seq.map Seq.list_of: CITG.modifiers Seq.seq;
    val stttacs        = Seq.map (CITG.meth_name_n_modifiers_to_stttac_on_state coinduction) all_modifierss;
    type 'a stttac = 'a Dynamic_Utils.stttac;
  in 
    stttacs : Proof.state stttac Seq.seq
  end;

end;

(** Dynamic_Cases: The tactic generator for the cases method. **)
structure Dynamic_Cases : DYNAMIC_TACTIC =
struct

(* Cases_Seed: The seed to make the tactic-generator for the cases method. *)
structure Cases_Seed : DYNAMIC_TACTIC_GENERATOR_SEED =
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
    val free_var_names   = Isabelle_Utils.get_free_var_names_in_1st_subg goal;
    val all_cases_mods  = get_ons free_var_names;
  in
    all_cases_mods : modifiers
  end;

end;

(* CTG: Cases_Tactic_Generator *)
structure CTG : DYNAMIC_TACTIC_GENERATOR = mk_Dynamic_Tactic_Generator (Cases_Seed);

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

(** Dynamic_Case_Tac: The tactic generator for the case_tac method. **)
structure Dynamic_Case_Tac : DYNAMIC_TACTIC =
struct

(* Case_Tac_Seed: The seed to make the tactic-generator for the case_tac method. *)
structure Case_Tac_Seed : DYNAMIC_TACTIC_GENERATOR_SEED =
struct

datatype modifier = On of string;

type modifiers = modifier list;

fun get_ons (all_vars:string list) = map On all_vars;

fun order (mods:modifiers) = mods;

fun get_name (On name) = name;

val get_names = map get_name;

fun mods_to_string (mods:modifiers) =
    mods |> order |> (fn ons => get_names ons |> Dynamic_Utils.get_meth_nm "");

fun get_all_modifiers (state:Proof.state) =
  let
    val {goal: thm,...} = Proof.goal state;
    val all_var_names   = Isabelle_Utils.get_all_var_names_in_1st_subg goal;
    val all_cases_mods  = get_ons all_var_names;
  in
    all_cases_mods : modifiers
  end;

end;

(* CTTG: Case_Tac_Tactic_Generator *)
structure CTTG : DYNAMIC_TACTIC_GENERATOR = mk_Dynamic_Tactic_Generator (Case_Tac_Seed);

fun get_state_stttacs (state:Proof.state) =
  let
    val induct         = "case_tac";
    val all_modifiers  = CTTG.get_all_modifiers state : CTTG.modifiers;
    val all_modifierss = map single all_modifiers |> Seq.of_list : CTTG.modifiers Seq.seq;
    val stttacs        = Seq.map (CTTG.meth_name_n_modifiers_to_stttac_on_state induct) all_modifierss;
    type 'a stttac = 'a Dynamic_Utils.stttac;
  in 
    stttacs : Proof.state stttac Seq.seq
  end;

end;

(** Classical_Seed: The seed to make the tactic-generator for the classical method. **)
structure Classical_Seed : DYNAMIC_TACTIC_GENERATOR_SEED =
struct

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

fun order (mods:modifiers) =
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

local

(** CTG: Classical_Tactic_Generator. **)
structure CTG : DYNAMIC_TACTIC_GENERATOR = mk_Dynamic_Tactic_Generator (Classical_Seed);

in

(** Dynamic_Clarsimp: The tactic generator for the clarsimp method. **)
structure Dynamic_Clarsimp : DYNAMIC_TACTIC =
struct

fun get_state_stttacs (state:Proof.state) =
  let
    val all_modifiers    = CTG.get_all_modifiers state : CTG.modifiers;
    val all_modifierss   = map single all_modifiers |> Seq.of_list : CTG.modifiers Seq.seq;
    val stttacs = Seq.map (CTG.meth_name_n_modifiers_to_stttac_on_state "clarsimp") all_modifierss;
    type 'a stttac = 'a Dynamic_Utils.stttac;
  in 
    stttacs : Proof.state stttac Seq.seq
  end;

end;

(** Dynamic_Fastforce: The tactic generator for the fastforce method. **)
structure Dynamic_Fastforce : DYNAMIC_TACTIC =
struct

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

(** Dynamic_Auto: The tactic generator for the auto method. **)
structure Dynamic_Auto : DYNAMIC_TACTIC =
struct

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

end;

(** Dynamic_Tactic_Generation: body. **)
type get_stttacs = Proof.state -> Proof.state Dynamic_Utils.stttac Seq.seq;
val rule        = Dynamic_Rule.get_state_stttacs;
val erule       = Dynamic_Erule.get_state_stttacs
val simp        = Dynamic_Simp.get_state_stttacs
val induct      = Dynamic_Induct.get_state_stttacs
val induct_tac  = Dynamic_Induct_Tac.get_state_stttacs
val coinduction = Dynamic_Coinduction.get_state_stttacs
val cases       = Dynamic_Cases.get_state_stttacs
val case_tac    = Dynamic_Case_Tac.get_state_stttacs
val clarsimp    = Dynamic_Clarsimp.get_state_stttacs
val fastforce   = Dynamic_Fastforce.get_state_stttacs
val auto        = Dynamic_Auto.get_state_stttacs

end;