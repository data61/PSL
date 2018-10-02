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

fun get_ons   (fvars:strings) = map On fvars;
fun get_arbs  (fvars:strings) = map Arbitrary fvars;
fun get_rules (rules:strings) = map Rule rules;

fun order' ordered [] = ordered
 |  order' (ons, arbs, rules) (On        var :: mods) = order' (On var::ons, arbs, rules) mods
 |  order' (ons, arbs, rules) (Arbitrary var :: mods) = order' (ons, Arbitrary var::arbs, rules) mods
 |  order' (ons, arbs, rules) (Rule     rule :: mods) = order' (ons, arbs, Rule rule::rules) mods;

fun order (mods:modifiers) = (*(ons, arbs, rules)*)
     order' ([],[],[]) mods
  |> (fn (a, b, c) => (rev a, rev b, rev c)): (modifiers * modifiers * modifiers)

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
    val induct_rules     = Find_Theorems2.get_induct_rule_names context goal : strings;
    val all_induct_mods  = get_ons free_var_names @ get_arbs free_var_names @ get_rules induct_rules;
  in
    all_induct_mods : modifiers
  end;

val pick_vars = filter     (fn modi => case modi of On _ => true | _ => false);
val dump_vars = filter_out (fn modi => case modi of On _ => true | _ => false);

val pick_arbs = filter     (fn modi => case modi of Arbitrary _ => true | _ => false);
val dump_arbs = filter_out (fn modi => case modi of Arbitrary _ => true | _ => false);

val pick_rules = filter     (fn modi => case modi of Rule _ => true | _ => false);
val dump_rules = filter_out (fn modi => case modi of Rule _ => true | _ => false);

fun reordered_mods (mods:modifiers) =
  let
    val vars   = pick_vars mods                    : modifiers;
    val varss  = Nitpick_Util.all_permutations vars: modifiers list;
    val arbs   = pick_arbs mods                    : modifiers;
    val arbss  = Nitpick_Util.all_permutations arbs: modifiers list;
    val rules  = pick_rules mods                   : modifiers;
    val vars_n_arbs = Utils.cart_prod varss arbss  : (modifiers * modifiers) list;
    val combs  = map (fn (vars, arbs) => vars @ arbs @ rules) vars_n_arbs;
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
  |> Seq.map Seq.list_of
  |> Seq.map IS.reordered_mods
  |> Seq.chop 10000 |> fst |> Seq.of_list (*TODO: Double-check. We set an upper limit.*)
  |> Seq.list_of
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
structure MiLkMaId_Assertion =
struct

val omap = Option.map;

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

fun pst_to_innermost_ufun_n_argss (pst:Proof.state) =
      IU.pst_to_fst_subg pst
  <$> MA.trm_to_utrm
  <$> MA.utrm_to_innermost_ufun_n_argss
   |> these: MA.ufun_n_args list;

fun get_var_namess_of_innermost_constants (pst:Proof.state) =
  let
    val innermost_ufun_n_argss = pst_to_innermost_ufun_n_argss pst: MA.ufun_n_args list;
    (*The type of innermost_var_namess is "strings list" because we need one "strings" for each innermost constant.*)
    val innermost_var_namess   = MA.ufun_n_argss_to_var_namess innermost_ufun_n_argss: strings list;
  in
    innermost_var_namess
  end;

fun ass_001 (pst:Proof.state) (mods:ITG.modifiers) =
  let
    val innermost_var_namess = get_var_namess_of_innermost_constants pst;
    val on_names = mods |> IS.pick_vars |> IS.get_names: strings: strings;
    val has_at_least_one_innermost_vname = Utils.a_member (op =) on_names: strings -> bool;
    val result = fold (fn vnames:strings => fn b:bool => b orelse has_at_least_one_innermost_vname vnames) innermost_var_namess false: bool;
  in
    result:bool
  end;

fun ufun_n_arg_to_induct_name (MA.UConst (cname, _)) = SOME (cname^".induct")
  | ufun_n_arg_to_induct_name  _                     = NONE;

fun ass_002 (pst:Proof.state) (mods:ITG.modifiers) =
  let
    val innermost_ufun_n_argss = pst_to_innermost_ufun_n_argss pst: MA.ufun_n_args list;
    val ctxt                   = Proof.context_of pst;
    val ufun_w_induct_rule_n_argss = MA.ufun_n_argss_to_ufun_w_induct_rule_n_argss ctxt innermost_ufun_n_argss;
    val rule_names             = mods |> IS.pick_rules |> IS.get_names: strings: strings;
    val innermost_induct_names = map (ufun_n_arg_to_induct_name o #ufun) ufun_w_induct_rule_n_argss
                               |> Utils.somes: strings;
    val result = Utils.a_member (op =) rule_names innermost_induct_names;
  in
    result:bool
  end;

fun ass_003 (pst:Proof.state) (mods:ITG.modifiers) =
  let
    val innermost_ufun_n_argss     = pst_to_innermost_ufun_n_argss pst: MA.ufun_n_args list;
    val ctxt                       = Proof.context_of pst;
    val ufun_w_induct_rule_n_argss = MA.ufun_n_argss_to_ufun_w_induct_rule_n_argss ctxt innermost_ufun_n_argss;
    val rule_names                 = mods |> IS.pick_rules |> IS.get_names: strings: strings;
    val cnames = map (unsuffix ".induct") rule_names: strings;
    val on_names = mods |> IS.pick_vars |> IS.get_names |> rev(*!*): strings: strings;
    (*get_var_namess_of_innermost_constants is too much*)
    val name_pairs = MA.ufun_n_argss_to_name_pairs ufun_w_induct_rule_n_argss: (string option * strings) list;
    fun for_given_cname_n_given_ufun_n_args (_              :string) (NONE, _)               = false
      | for_given_cname_n_given_ufun_n_args (cname_from_rule:string) (SOME fname, var_names) =
        cname_from_rule = fname andalso on_names = var_names;
    fun for_a_cname_n_all_ufun_n_args (cnames_from_rules:strings) (pairs:(string option * strings) list) =
      Utils.a_member (uncurry for_given_cname_n_given_ufun_n_args) cnames_from_rules pairs;
  in
    for_a_cname_n_all_ufun_n_args cnames name_pairs:bool
  end;

fun mk_post_thm (meth_name:string) (pre_pst:Proof.state) (mods:ITG.modifiers): thm option =
  let
    val nontac = try (modifiers_to_str meth_name) mods
             >>= try (str_to_nontac): Proof.state DU.nontac option;
    fun mk_fst_res _   NONE       = NONE
     |  mk_fst_res st (SOME ntac) = try ntac st >>= try Seq.hd;
    val post_thm = mk_fst_res  pre_pst nontac <$> IU.proof_state_to_thm: thm option;
  in
    post_thm: thm option
  end;

fun mk_post_1st_subg (meth_name:string) (pre_pst:Proof.state) (mods:ITG.modifiers): term option =
  mk_post_thm meth_name pre_pst mods >>= IU.get_1st_subg;

fun ass_006 (pst:Proof.state) (mods:ITG.modifiers) =
  let
    val pre_1st_subg  = IU.pst_to_fst_subg pst            : term option;
    val post_1st_subg = mk_post_1st_subg "induct" pst mods: term option;
    fun map_option_pair f (SOME x, SOME y) = SOME (f (x, y))
      | map_option_pair _  _               = NONE
    val are_same = map_option_pair Term.aconv (pre_1st_subg, post_1st_subg): bool option;
    val result = Option.getOpt (are_same, false): bool;
  in
    result: bool
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

fun ass_014 (pst:Proof.state) (mods:ITG.modifiers) =
  let
    val innermost_var_namess = get_var_namess_of_innermost_constants pst;
    val on_names = mods |> IS.pick_vars |> IS.get_names: strings: strings;
    val all_are_innermost_vname = Utils.members (op =) on_names: strings -> bool;
    val result = fold (fn vnames:strings => fn b:bool => b orelse all_are_innermost_vname vnames) innermost_var_namess false: bool;
  in
    result:bool
  end;

(*TODO*)
fun mk_ass_results (pre_pst:Proof.state) (mods:ITG.modifiers) = [
(*001*)ass_001 pre_pst mods,
(*002*)ass_002 pre_pst mods,
(*003*)ass_003 pre_pst mods,
(*004*)true,
(*005*)true,
(*006*)ass_006 pre_pst mods,
(*007*)true,
(*008*)true,
(*009*)true,
(*010*)true,
(*011*)false,
(*012*)ass_012 pre_pst mods,
(*013*)ass_013 pre_pst mods,
(*014*)ass_014 pre_pst mods];

fun is_used (meth_name:string) (pre_pst:Proof.state) (model_post:thm) (mods:ITG.modifiers) =
    mk_post_thm meth_name pre_pst mods
<$> (curry Thm.eq_thm model_post)
|>  (fn used:bool option => Option.getOpt (used, false)): bool;

fun mk_a_line (meth_name:string) (pre_pst:Proof.state) (model_post:thm) (mods:ITG.modifiers) =
  {used        = is_used meth_name pre_pst model_post mods,
   ass_results = mk_ass_results (pre_pst:Proof.state) (mods:ITG.modifiers)
   }: one_line;

fun mk_lines (meth_name:string) (pre_pst:Proof.state) (modss:ITG.modifiers list) (model_post:thm) =
  map (mk_a_line meth_name pre_pst model_post) modss;

end(*MiLkMaId_Assertion*);

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
    val all_modss = get_all_modifierss pst: ITG.modifiers list;
    (*TODO: Do I need "all_modss" here? I can construct it within More_MiLkMaId_Assertion*)
    val lines = MiLkMaId_Assertion.mk_lines meth_name pst all_modss model_result';

    (*TODO: print_one_line and _ are only for testing. ToBeRemoved*)
    fun print_one_line (line:one_line) =
      let
        val bool_to_int_str = Int.toString o Utils.bool_to_int: bool -> string;
        val used  = #used line |> bool_to_int_str: string;
        val ass_results = map bool_to_int_str (#ass_results line): string list;
      in
        space_implode "" (used::ass_results)
      end;
    val _ = (map print_one_line lines ~~ map IS.mods_to_string all_modss)
      |> map (tracing o String.concatWith " --- " o Utils.pair_to_list);

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

fun get_ons   (fvars:strings) = map On fvars;
fun get_rules (rules:strings) = map Rule rules;

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
    val induct_rules    = Find_Theorems2.get_induct_rule_names context goal : strings;
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