(*  Title:      MiLkMaId/src/Smart_Induct.ML
    Author:     Yutaka Nagashima, CIIRC, CTU, University of Innsbruck

*)

(*** DYNAMIC_TACTIC: makes a series of state-monad based tactics from proof state. ***)
signature SMART_TACTIC =
sig
  type one_line = {used       : bool,
                   ass_results: bool list};
  type datum = {within_psls_scope       : bool,
                numb_of_successful_meths: int, (*NB: upper limit is 10000*)
                numb_of_created_methds  : int, (*NB: upper limit is 10000*)
                ass_results             : one_line list
                };
  val psl_mk_right_mods: Method.text_range -> Proof.state -> datum;
end;

(** Smart_Induct: The tactic generator for the induct method. **)
structure Smart_Induct : SMART_TACTIC =
struct
(*We expose the definitions of these types because other modules should be able to use record field selections.*)
type one_line = {used       : bool,
                 ass_results: bool list
                 };
type datum = {within_psls_scope       : bool,
              numb_of_successful_meths: int, (*NB: upper limit is 10000*)
              numb_of_created_methds  : int, (*NB: upper limit is 10000*)
              ass_results             : one_line list
              };

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

val pick_vars = filter     (fn modi => case modi of On _ => true | _ => false);
val dump_vars = filter_out (fn modi => case modi of On _ => true | _ => false);

fun reordered_mods (mods:modifiers) =
  let
    val vars   = pick_vars mods : modifiers;
    val varss  = Nitpick_Util.all_permutations vars : modifiers list;
    val others = dump_vars mods : modifiers;
    val combs  = map (fn vs => vs @ others) varss;
  in
    combs:modifiers list
  end;

end;

(* ITG: Induct_Tactic_Generator. *)
structure ITG : DYNAMIC_TACTIC_GENERATOR = mk_Dynamic_Tactic_Generator (Induct_Seed);

structure IS = Induct_Seed;
structure DU = Dynamic_Utils;
structure IU = Isabelle_Utils;

fun get_all_modifierss (pst:DU.state) : ITG.modifiers list =
    ITG.get_all_modifiers pst
  |> Seq.of_list
  |> Seq2.powerset
  |> Seq.chop 10000 |> fst |> Seq.of_list (*TODO: Double-check. We set an upper limit.*)
  |> Seq.list_of
  |> map Seq.list_of
  |> map IS.reordered_mods
  |> flat: ITG.modifiers list;

fun mk_modifiers_to_str (meth_name:string) (mods: IS.modifiers) : string =
  enclose "(" ")" (meth_name ^ IS.mods_to_string mods);

fun str_to_nontac (meth:string) : DU.state DU.nontac =
  IU.TIMEOUT_in 3.0 (Utils.try_with (K Seq.empty) DU.string_to_nontac_on_pstate meth);

fun state_to_nontacs (meth_name:string) (pst:DU.state): DU.state DU.nontac list = pst
  |> get_all_modifierss
  |> map (mk_modifiers_to_str meth_name)
  |> map (try str_to_nontac)
  |> Utils.somes;

fun get_fst_result (pst:Proof.state) (nontac: DU.state DU.nontac) : DU.state option =
      (try nontac pst: DU.state Seq.seq option)
  >>= (try Seq.hd: DU.state Seq.seq -> Dynamic_Utils.state option);

fun get_fst_results (pst:Proof.state) (nontacs: DU.state DU.nontac list) : DU.state list =
  map (get_fst_result pst) nontacs |> Utils.somes;

fun state_to_fst_thms (meth_name:string) (pst:DU.state) : thm list =
  let
    val nontacs = state_to_nontacs meth_name pst  : DU.state DU.nontac list;
    val states  = get_fst_results pst nontacs     : DU.state list;
    val thms    = map IU.proof_state_to_thm states: thm list;
  in
    thms
  end;

fun psl_mk_right_mods (model_meth: Method.text_range) (pst:Proof.state) =
  let
    val model_result = try (Proof.apply model_meth) pst
      >>= try Seq.filter_results
      >>= try Seq.hd
      >>= try IU.proof_state_to_thm                                                : thm option;
    val meth_name   = IU.get_meth_name (fst model_meth)                            : string;
    val psl_results = state_to_fst_thms meth_name pst                              : thm list;
    fun has_one (NONE  : thm option) = false
     |  has_one (SOME g: thm option) = List.exists (curry Thm.eq_thm g) psl_results: bool;
    val datum = {within_psls_scope        = has_one model_result                   : bool,
                 numb_of_successful_meths = length psl_results                     : int,
                 numb_of_created_methds   = length (state_to_nontacs meth_name pst): int,
                 ass_results              = [(*TODO*)]                             : one_line list
                 }: datum;
  in
    datum
  end;

end;

(** Dynamic_Induct_Tac: The tactic generator for the induct_tac method. **)
structure Dynamic_Induct_Tac : SMART_TACTIC =
struct

type one_line = {used       : bool,
                 ass_results: bool list
                 };
type datum = {within_psls_scope       : bool,
              numb_of_successful_meths: int, (*NB: upper limit is 10000*)
              numb_of_created_methds  : int, (*NB: upper limit is 10000*)
              ass_results             : one_line list
              };

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
    @ prefix_if_nonnil "rule:" (get_names rules))
    |> Dynamic_Utils.get_meth_nm ""
  end;

fun get_all_modifiers (state:Proof.state) =
  let
    val {context: Proof.context, goal: thm,...} = Proof.goal state;
    val all_var_names   = Isabelle_Utils.get_all_var_names_in_1st_subg goal;
    val induct_rules    = Find_Theorems2.get_induct_rule_names context goal : string list;
    val all_induct_mods = get_ons all_var_names @ get_rules induct_rules;
  in
    all_induct_mods : modifiers
  end;

val reordered_mods = single o I;

end;

(* ITTG: Induct_Tac_Tactic_Generator *)
structure ITTG : DYNAMIC_TACTIC_GENERATOR =
  mk_Dynamic_Tactic_Generator (Induct_Tac_Seed);

fun get_state_stttacs (state:Proof.state) =
  let
    val induct         = "induct_tac";
    val all_modifiers  = ITTG.get_all_modifiers state : ITTG.modifiers;
    val all_modifierss = Seq2.powerset (Seq.of_list all_modifiers)
                      |> Seq.chop 10000 |> fst |> Seq.of_list (*TODO: Double-check. We set an upper limit.*)
                      |> Seq.map Seq.list_of
                       : ITTG.modifiers Seq.seq;
    val stttacs        = Seq.map (ITTG.meth_name_n_modifiers_to_stttac_on_state induct) all_modifierss;
    type 'a stttac = 'a Dynamic_Utils.stttac;
  in 
    stttacs
  end;

(*TODO*)
val datum = {within_psls_scope        = true: bool,
             numb_of_successful_meths = 0   : int,
             numb_of_created_methds   = 0   : int,
             ass_results              = []  : one_line list
             }: datum;

fun psl_mk_right_mods _ _ = datum (*TODO*);

end;