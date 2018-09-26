(*  Title:      MiLkMaId/src/Smart_Induct.ML
    Author:     Yutaka Nagashima, CIIRC, CTU, University of Innsbruck

*)

(*** SMART_TACTIC: makes a series of state-monad based tactics from proof state. ***)
signature SMART_TACTIC =
sig
  type one_line = {used       : bool,
                   ass_results: bool list};
  type datum = {within_psls_scope       : bool,
                numb_of_successful_meths: int, (*NB: upper limit is 10000*)
                numb_of_created_methds  : int, (*NB: upper limit is 10000*)
                lines                   : one_line list
                };
  val mk_datapoint: Method.text_range -> Proof.state -> datum;
end;

(*** Smart_Induct: The tactic generator for the induct method. ***)
structure Smart_Induct : SMART_TACTIC =
struct
(*We expose the definitions of these types because other modules should be able to use record field selections.*)
type one_line = {used       : bool,
                 ass_results: bool list
                 };
type datum = {within_psls_scope       : bool,
              numb_of_successful_meths: int, (*NB: upper limit is 10000*)
              numb_of_created_methds  : int, (*NB: upper limit is 10000*)
              lines                   : one_line list
              };

(** Induct_Seed: The seed to make the tactic-generator for the induct method. **)
(* We should not annotate the signature to this structure Induct_Seed
 * because we have to access some functions that are not exposed when defining assertions. *)
structure Induct_Seed (*: DYNAMIC_TACTIC_GENERATOR_SEED*) =
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

(*ITG: Induct_Tactic_Generator.*)
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

fun modifiers_to_str (meth_name:string) (mods: IS.modifiers) : string =
  enclose "(" ")" (meth_name ^ IS.mods_to_string mods);

fun str_to_nontac (meth:string) : DU.state DU.nontac =
  IU.TIMEOUT_in 3.0 (Utils.try_with (K Seq.empty) DU.string_to_nontac_on_pstate meth);

fun state_to_nontacs (meth_name:string) (pst:DU.state): DU.state DU.nontac list = pst
  |> get_all_modifierss
  |> map (modifiers_to_str meth_name)
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

(** More_MiLkMaId_Table **)
structure More_MiLkMaId_Table =
struct

structure MA = MiLkMaId_Table;

(*TODO: some of the following functions should be defined in MiLkMaId_Assertion.*)
fun get_the_level_of_innermost_UApp' ([]:MA.data)              (acc:int) = acc
 |  get_the_level_of_innermost_UApp' ({point,...}::ds:MA.data) (acc:int) =
let
  val {name, utyp, level} = point;
  val new_acc = if utyp = MA.UAp andalso level > acc then level else acc: int;
in
  get_the_level_of_innermost_UApp' ds new_acc: int
end;

fun get_the_level_of_innermost_UApp (data:MA.data) = get_the_level_of_innermost_UApp' data 1;

fun get_points_below_n (threshold:int) (data:MA.data) =
let
  (*"below" in the un-curried syntax tree*)
  fun is_below_n (n:int) ({level,...}:MA.point) = level > n;
  val points = map #point data: MA.point list;
in
  filter (is_below_n threshold) points: MA.point list
end;

fun opt_map_pair f (SOME v1, SOME v2) = SOME (f (v1, v2))
 |  opt_map_pair _ _ = NONE;

fun ass_001 (pst:Proof.state) (mods:ITG.modifiers) =
  let
    (*TODO: re-factor this.*)
    val ctxt = Proof.context_of pst: Proof.context;
    val thm = IU.proof_state_to_thm pst: thm;
    val fst_subg = IU.get_1st_subg thm: term option;
    val uncurrid_fst_subg = Option.map MA.uncurry fst_subg: MA.uterm option;
    val data = Option.map MA.uncurried_trm_to_data uncurrid_fst_subg: MA.data option;
    val data_with_pattern = Option.map (MA.data_to_data_with_pattern ctxt) data: MA.data_with_pattern option;
    val level_of_innermost_UApp = Option.map get_the_level_of_innermost_UApp data;
    val some_innermost_points = opt_map_pair (uncurry get_points_below_n) (level_of_innermost_UApp, data): MA.point list option;
    val innermost_points = these some_innermost_points: MA.point list;
  in
    true
  end;

fun ass_012 (_:Proof.state) (mods:ITG.modifiers) =
  let
    val (ons, arbs, _) = IS.order mods;
    val dups = duplicates (op =) (map IS.get_name (ons @ arbs));
    val has_dup = (not o null) dups;
  in
    has_dup
  end;


fun ass_013 (_:Proof.state) (mods:ITG.modifiers) =
  let
    val (_, _, rules) = IS.order mods;
    val less_than_2_rules = length rules < 2;
  in
    less_than_2_rules
  end;

(*TODO*)
fun mk_ass_results (pre_pst:Proof.state) (mods:ITG.modifiers) = [
(*001*)true,
(*002*)true,
(*003*)true,
(*004*)true,
(*005*)true,
(*006*)true,
(*007*)true,
(*008*)true,
(*009*)true,
(*010*)true,
(*011*)false,
(*012*)ass_012 pre_pst mods,
(*013*)ass_013 pre_pst mods];

fun mk_get_post_thm (meth_name:string) (pre_pst:Proof.state) (mods:ITG.modifiers): thm option =
  let
val _ = (fn modi => modifiers_to_str meth_name modi |> tracing) mods;
    val nontac = try (modifiers_to_str meth_name) mods
             >>= try (str_to_nontac): Proof.state DU.nontac option;
    fun mk_fst_res _   NONE       = NONE
     |  mk_fst_res st (SOME ntac) = try ntac st >>= try Seq.hd;
    val post_thm = mk_fst_res  pre_pst nontac <$> IU.proof_state_to_thm: thm option;
  in
    post_thm: thm option
  end;

fun is_used (meth_name:string) (pre_pst:Proof.state) (model_post:thm) (mods:ITG.modifiers) =
    mk_get_post_thm meth_name pre_pst mods
<$> (curry Thm.eq_thm model_post)
|>  (fn used:bool option => Option.getOpt (used, false)): bool;

fun mk_a_line (meth_name:string) (pre_pst:Proof.state) (model_post:thm) (mods:ITG.modifiers) =
  {used        = is_used meth_name pre_pst model_post mods,
   ass_results = mk_ass_results (pre_pst:Proof.state) (mods:ITG.modifiers)
   }: one_line;

fun mk_lines (meth_name:string) (pre_pst:Proof.state) (modss:ITG.modifiers list) (model_post:thm) =
  map (mk_a_line meth_name pre_pst model_post) modss;

end;

fun mk_datapoint (model_meth: Method.text_range) (pst:Proof.state) =
  let
    val model_result = try (Proof.apply model_meth) pst
      >>= try Seq.filter_results
      >>= try Seq.hd
      >>= try IU.proof_state_to_thm                                                : thm option;
    (*Nobody should apply induction to TrueI*)
    val model_result' = Option.getOpt (model_result, TrueI)                        : thm;
    val meth_name   = IU.get_meth_name (fst model_meth)                            : string;
    val psl_results = state_to_fst_thms meth_name pst                              : thm list;
    fun has_one (NONE  : thm option) = false
     |  has_one (SOME g: thm option) = List.exists (curry Thm.eq_thm g) psl_results: bool;
    val all_modss = get_all_modifierss pst: ITG.modifiers list; (*TODO: Do I need this here? I can construct it within More_MiLkMaId_Assertion*)
    val lines = More_MiLkMaId_Table.mk_lines meth_name pst all_modss model_result';
    val datum = {within_psls_scope        = has_one model_result                   : bool,
                 numb_of_successful_meths = length psl_results                     : int,
                 numb_of_created_methds   = length (state_to_nontacs meth_name pst): int,
                 lines                    = lines                                  : one_line list
                 }: datum;
  in
    datum
  end;

end;

(*** TODO: Dynamic_Induct_Tac: The tactic generator for the induct_tac method. ***)
structure Dynamic_Induct_Tac : SMART_TACTIC =
struct

type one_line = {used       : bool,
                 ass_results: bool list
                 };
type datum = {within_psls_scope       : bool,
              numb_of_successful_meths: int, (*NB: upper limit is 10000*)
              numb_of_created_methds  : int, (*NB: upper limit is 10000*)
              lines                   : one_line list
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
             lines                    = []  : one_line list
             }: datum;

fun mk_datapoint _ _ = datum (*TODO*);

end;