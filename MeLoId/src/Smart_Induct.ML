(*  Title:      MeLoId/src/Smart_Induct.ML
    Author:     Yutaka Nagashima, CIIRC, CTU, University of Innsbruck
*)

(*** SMART_TACTIC: makes a series of state-monad based tactics from proof state. ***)
signature SMART_TACTIC =
sig
  type one_line = {used       : bool,
                   ass_results: bool list,
                   meth_w_args: string};
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
                 ass_results: bool list,
                 meth_w_args: string};
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
  |> Seq.map Seq.of_list
  |> Seq.flat
  |> Seq.chop 10000 |> fst: ITG.modifiers list;(*TODO: Double-check. We set an upper limit.*)

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

(* TODO: in future, this function, gen_pst_to_ufun_n_argss, should be parametrised, so that
 * users can specify if he/she wants to consider the first subgoal or chained facts. *)
fun gen_pst_to_ufun_n_argss (pst:Proof.state) (get_ufun_n_argss: MA.uterm -> MA.ufun_n_argss) =
      IU.pstate_to_1st_subg_n_chained_facts pst
   |> map IU.trm_to_prop_trms
   |> flat
   |> map MA.trm_to_utrm
   |> map get_ufun_n_argss
   |> flat
   : MA.ufun_n_argss;

fun pst_to_ufun_n_argss (pst:Proof.state) = gen_pst_to_ufun_n_argss pst MA.utrm_to_ufun_n_argss
                                          : MA.ufun_n_argss;

fun pst_to_innermost_ufun_n_argss (pst:Proof.state) = gen_pst_to_ufun_n_argss pst MA.utrm_to_innermost_ufun_n_argss
                                                    : MA.ufun_n_argss;

fun get_var_namess_of_innermost_constants (pst:Proof.state) =
  let
    val innermost_ufun_n_argss = pst_to_innermost_ufun_n_argss pst: MA.ufun_n_argss;
    (*The type of innermost_var_namess is "strings list" because we need one "strings" for each innermost constant.*)
    val innermost_var_namess   = MA.ufun_n_argss_to_var_namess innermost_ufun_n_argss: strings list;
  in
    innermost_var_namess
  end;

(* ass_001 *)
fun ass_001 (pst:Proof.state) (mods:ITG.modifiers) =
  let
    val innermost_var_namess             = get_var_namess_of_innermost_constants pst: strings list;
    val on_names                         = mods |> IS.pick_vars |> IS.get_names     : strings: strings;
    val has_at_least_one_innermost_vname = Utils.a_member (op =) on_names           : strings -> bool;
    val result = fold (fn vnames:strings => fn b:bool => b orelse has_at_least_one_innermost_vname vnames) innermost_var_namess false: bool;
  in
    result:bool
  end;

fun ufun_n_arg_to_induct_name (MA.UConst (cname, _)) = SOME (cname^".induct")
  | ufun_n_arg_to_induct_name  _                     = NONE;

(* ass_002 *)
fun ass_002 (pst:Proof.state) (mods:ITG.modifiers) =
  let
    val innermost_ufun_n_argss     = pst_to_innermost_ufun_n_argss pst                                                : MA.ufun_n_args list;
    val ctxt                       = Proof.context_of pst                                                             : Proof.context;
    val ufun_w_induct_rule_n_argss = MA.ufun_n_argss_to_ufun_w_induct_rule_n_argss ctxt innermost_ufun_n_argss        : MA.ufun_n_argss;
    val rule_names                 = mods |> IS.pick_rules |> IS.get_names                                            : strings;
    val innermost_induct_names     = map (ufun_n_arg_to_induct_name o #ufun) ufun_w_induct_rule_n_argss |> Utils.somes: strings;
    val result                     = Utils.a_member (op =) rule_names innermost_induct_names                          : bool;
  in
    result:bool
  end;

fun induct_rule_name_to_const_name (induct_rule_name) : string option =
    try (unsuffix ".induct"   )  induct_rule_name
<|> try (unsuffix ".inducts(1)")  induct_rule_name
<|> try (unsuffix ".inducts(2)")  induct_rule_name
<|> try (unsuffix ".inducts(3)")  induct_rule_name
<|> try (unsuffix ".inducts(4)")  induct_rule_name
<|> try (unsuffix ".inducts(5)")  induct_rule_name
<|> try (unsuffix ".inducts(6)")  induct_rule_name
<|> try (unsuffix ".inducts(7)")  induct_rule_name
<|> try (unsuffix ".inducts(8)")  induct_rule_name
<|> try (unsuffix ".inducts(9)")  induct_rule_name
<|> try (unsuffix ".inducts(10)") induct_rule_name;

fun helper_for_ass_003_019 (pst:Proof.state) (mods:ITG.modifiers) =
  let
    val ufun_n_argss               = pst_to_ufun_n_argss pst                                           : MA.ufun_n_args list;
    val ctxt                       = Proof.context_of pst                                              : Proof.context;
    val ufun_w_induct_rule_n_argss = MA.ufun_n_argss_to_ufun_w_induct_rule_n_argss ctxt ufun_n_argss   : MA.ufun_n_argss;
    val rules                      = mods |> IS.pick_rules                                             : ITG.modifiers;
    val has_at_least_one_rule      = length rules > 0                                                  : bool;
    val rule_names                 = rules |> IS.get_names                                             : strings: strings;
    val rule_cnames                = map induct_rule_name_to_const_name rule_names |> Utils.somes      : strings;
    val on_names                   = mods |> IS.pick_vars |> IS.get_names                              : strings;
    val name_pairs                 = MA.ufun_n_argss_to_cname_n_vnames_pairs ufun_w_induct_rule_n_argss: (string option * strings) list;
    fun for_given_rule_cname_n_given_ufun_n_args_ind_are_subset_in_ord (_              :string) (NONE, _)               = false
      | for_given_rule_cname_n_given_ufun_n_args_ind_are_subset_in_ord (cname_from_rule:string) (SOME fname, var_names) =
        cname_from_rule = fname andalso Utils.order_sensitive_multi_subset equal on_names var_names
    fun for_some_rule_cname_n_all_ufun_n_args (cnames_from_rules:strings) (pairs:(string option * strings) list) =
        Utils.a_member (uncurry for_given_rule_cname_n_given_ufun_n_args_ind_are_subset_in_ord) cnames_from_rules pairs;
    fun for_given_rule_cname_n_given_ufun_n_args (_              :string) (NONE, _)               = false
      | for_given_rule_cname_n_given_ufun_n_args (cname_from_rule:string) (SOME fname, var_names) =
        cname_from_rule = fname andalso subset (op =) (on_names, var_names);
    fun for_all_rule_cname_n_all_ufun_n_args (cnames_from_rules:strings) (pairs:(string option * strings) list) =
        Utils.a_member (uncurry for_given_rule_cname_n_given_ufun_n_args) cnames_from_rules pairs;
    val result = {ass_003 = has_at_least_one_rule andalso for_some_rule_cname_n_all_ufun_n_args rule_cnames name_pairs: bool,
                  ass_019 = has_at_least_one_rule andalso for_all_rule_cname_n_all_ufun_n_args  rule_cnames name_pairs: bool}
  in
    result
  end;

(* ass_003 *)
fun ass_003 (pst:Proof.state) (mods:ITG.modifiers) = helper_for_ass_003_019 pst mods |> #ass_003;

(* ass_005 *)
fun ass_005 (pst:Proof.state) (mods:ITG.modifiers) =
  let
    val ufun_n_argss       = pst_to_ufun_n_argss pst                                   : MA.ufun_n_args list;
    val ctxt               = Proof.context_of pst                                      : Proof.context;
    val on_names           = mods |> IS.pick_vars |> IS.get_names                      : strings;
    val vnames_only_fullss = map (MA.ufun_n_args_to_vnames_only_full ctxt) ufun_n_argss: strings list;
    fun are_all_vnames_of_full (vnames:strings) (fulls:strings) = Utils.members (op =) vnames fulls;
    val result = exists (are_all_vnames_of_full on_names) vnames_only_fullss andalso length on_names > 0;
  in
    result:bool
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

fun map_option_pair f (SOME x, SOME y) = SOME (f (x, y))
  | map_option_pair _  _               = NONE

(* ass_006 *)
fun ass_006 (pst:Proof.state) (mods:ITG.modifiers) =
  let
    val pre_1st_subg  = IU.pst_to_fst_subg pst            : term option;
    val post_1st_subg = mk_post_1st_subg "induct" pst mods: term option;
    val are_same      = map_option_pair Term.aconv (pre_1st_subg, post_1st_subg): bool option;
    val result        = Option.getOpt (are_same, false): bool;
  in
    result: bool
  end;

(* ass_007 *)
fun ass_007 (pst:Proof.state) (mods:ITG.modifiers) =
  let
    val pre_1st_subg           = IU.pst_to_fst_subg pst                                            : term option;
    val post_1st_subg          = mk_post_1st_subg "induct" pst mods                                : term option;
    val numb_arbs              = IS.pick_arbs mods |> length |> SOME                               : int option;
    val numb_pre_1st_subg      = pre_1st_subg  <$> Utils.flip Term.add_consts [] <$> length        : int option;
    val numb_post_1st_subg     = post_1st_subg <$> Utils.flip Term.add_consts [] <$> length        : int option;
    val numb_post_1st_adjusted = map_option_pair (op -) (numb_post_1st_subg, numb_arbs)            : int option;
    val post_has_less_const    = map_option_pair (op >) (numb_pre_1st_subg, numb_post_1st_adjusted): bool option;
    val result                 = Option.getOpt (post_has_less_const, false)                        : bool;
  in
    result: bool
  end;

(* ass_009 *)
fun ass_009 (pst:Proof.state) (mods:ITG.modifiers) =
  let
    val pre_1st_subg            = IU.pst_to_fst_subg pst                                      : term option;
    val rule_names              = IS.pick_rules mods |> map IS.get_name                       : string list;
    val numb_rules              = rule_names |> length                                        : int;
    val rule_cnames             = map induct_rule_name_to_const_name rule_names |> Utils.somes: strings;
    val ucr_1st_subg            = omap MA.trm_to_utrm pre_1st_subg                            : MA.uterm option;
    val data                    = omap MA.utrm_to_data ucr_1st_subg                           : MA.data option;
    val ctxt                    = Proof.context_of pst: Proof.context                         : Proof.context;
    val cname_to_filtered_data' = omap MA.filter_data_with_point_name data                    : (string -> MA.data) option;
    val cname_to_filtered_data  = Utils.opt_app cname_to_filtered_data'                       : string option -> MA.data option;
    val data_w_rule_cnames      = map cname_to_filtered_data (map SOME rule_cnames)
                                |> Utils.somes |> flat                                        : MA.data;
    val levels_of_rule_cnames   = map MA.datum_to_level data_w_rule_cnames                    : int list;
    val max_level_of_rule_cname = fold (curry Int.max) levels_of_rule_cnames 0                : int;

    val cname_to_filtered_out_data' = omap MA.filter_data_wo_point_name data                  : (string -> MA.data) option;
    val cname_to_filtered_out_data  = Utils.opt_app cname_to_filtered_out_data'               : string option -> MA.data option;
    val data_wo_rule_cnamess    = map cname_to_filtered_out_data (map SOME rule_cnames)
                                |> Utils.somes                                                : MA.data list;
    val data_wo_rule_cnames     = fold (inter (op =)) data_wo_rule_cnamess (these data)       : MA.data;
    val has_induct_rule         = fn name:string =>
                                 (try (Proof_Context.get_thm ctxt) (name^".induct"))
                                |> is_some                                                    : bool;
    val other_data_w_induct_name = filter (fn {point,...}:MA.datum =>
                                   #name point |> has_induct_rule) data_wo_rule_cnames        : MA.data;
    val level_of_others         = map MA.datum_to_level other_data_w_induct_name              : int list;
    val max_level_of_others     = fold (curry Int.max) level_of_others 0                      : int;
  in
    numb_rules > 0 andalso max_level_of_rule_cname >= max_level_of_others
  end;

(* ass_012 *)
fun ass_012 (_:Proof.state) (mods:ITG.modifiers) =
  let
    val (ons, arbs, _) = IS.order mods;
    val dups           = duplicates (op =) (map IS.get_name (ons @ arbs));
    val has_dup        = (not o null) dups;
  in
    has_dup
  end;

(* ass_013 *)
fun ass_013 (_:Proof.state) (mods:ITG.modifiers) =
  let
    val (_, _, rules)     = IS.order mods;
    val less_than_2_rules = length rules < 2;
  in
    less_than_2_rules
  end;

(* ass_014 *)
fun ass_014 (pst:Proof.state) (mods:ITG.modifiers) =
  let
    val innermost_var_namess    = get_var_namess_of_innermost_constants pst;
    val on_names                = mods |> IS.pick_vars |> IS.get_names: strings: strings;
    val all_are_innermost_vname = Utils.members (op =) on_names: strings -> bool;
    val result = fold (fn vnames:strings => fn b:bool => b orelse all_are_innermost_vname vnames) innermost_var_namess false: bool;
  in
    result:bool
  end;

(* ass_015 *)
fun ass_015 (pst:Proof.state) (mods:ITG.modifiers) =
  let
    val pre_1st_subg         = IU.pst_to_fst_subg pst                                                              : term option;
    val post_1st_subg        = mk_post_1st_subg "induct" pst mods                                                  : term option;
    val all_dBi_in_pre_used  = omap IU.are_all_de_Bruijn_indices_used pre_1st_subg                                 : bool option;
    val all_dBi_in_post_used = omap IU.are_all_de_Bruijn_indices_used post_1st_subg                                : bool option;
    val some_dBi_not_used    = omap not all_dBi_in_post_used                                                       : bool option;
    val pre_n_post_are_diff  = map_option_pair (uncurry Utils.conjunction) (all_dBi_in_pre_used, some_dBi_not_used): bool option;
    val result               = Option.getOpt (pre_n_post_are_diff, false)                                          : bool;  
  in
    result: bool
  end;

(* ass_016 *)
fun ass_016 (_:Proof.state) (mods:ITG.modifiers) =
  let
    val numb_rule = mods |> IS.pick_rules |> length: int;
    val result    = numb_rule > 0                  : bool;
  in
    result:bool
  end;

fun is_this_datum_w_pttrn_of_vname (vname:string) ({point,...}:MA.datum_with_pattern) =
  let
    val {name, utyp,...} = point;
  in
    name = vname (*FIXME: why does the following cause problems? andalso utyp = MA.UV*)
  end;

(* ass_017 *)(*TODO: FIXME: we should think about chained facts as well.*)
fun ass_017 (pst:Proof.state) (mods:ITG.modifiers) =
  let
    val pre_1st_subg = IU.pst_to_fst_subg pst                       : term option;
    val ucr_1st_subg = omap MA.trm_to_utrm pre_1st_subg             : MA.uterm option;
    val data         = omap MA.utrm_to_data ucr_1st_subg            : MA.data option;
    val ctxt         = Proof.context_of pst: Proof.context          : Proof.context;
    val data_w_pttrn = omap (MA.data_to_data_with_pattern ctxt) data: MA.data_with_pattern option;
    val vnames       = mods |> IS.pick_vars |> IS.get_names         : strings;
    val induct_has_at_least_one_ons = length vnames > 0: bool;
    fun is_Full_or_Other ({pattern,...}:MA.ancestor_with_pattern) =
      pattern = MA.Full orelse pattern = MA.Other;
    fun this_point_is_Full_or_Other_to_all_ancestors ({ancestors,...}:MA.datum_with_pattern) =
      forall is_Full_or_Other ancestors;
    fun one_var_of_vname_is_Full_or_Other_to_all_ancestors' (vname:string) (data_w_pttrn:MA.data_with_pattern) =
      let
        val data_of_vname = filter (is_this_datum_w_pttrn_of_vname vname) data_w_pttrn: MA.data_with_pattern;
        val has_an_instance_that_is_Full_or_Other_to_all_ist_ancestors =
          exists this_point_is_Full_or_Other_to_all_ancestors data_of_vname: bool;
      in
        has_an_instance_that_is_Full_or_Other_to_all_ist_ancestors
      end;
    fun one_var_of_vname_is_Full_or_Other_to_all_ancestors (vname:string) =
      Option.getOpt (omap (one_var_of_vname_is_Full_or_Other_to_all_ancestors' vname) data_w_pttrn, false): bool;
    val all_ons_are_Full_or_Other_to_all_ancestors =
      forall one_var_of_vname_is_Full_or_Other_to_all_ancestors vnames: bool;
  in
    induct_has_at_least_one_ons andalso all_ons_are_Full_or_Other_to_all_ancestors
  end;

(* ass_018 *)
fun ass_018 _ (mods:ITG.modifiers) = length mods = 0;

(* ass_019 *)
fun ass_019 (pst:Proof.state) (mods:ITG.modifiers) = helper_for_ass_003_019 pst mods |> #ass_019;

(* ass_020. checks if the proof state has chained facts *)
fun ass_020 (pstate:Proof.state) _ = IU.pstate_to_usings pstate |> null;

(* ass_021 *)(*TODO: FIXME:*)
fun ass_021 (pst:Proof.state) (mods:ITG.modifiers) =
  let
    val vnames                       = mods |> IS.pick_vars |> IS.get_names: strings;
    val arb_names                    = mods |> IS.pick_arbs |> IS.get_names: strings;
    val induct_has_at_least_one_ons  = length vnames    > 0                : bool;
    val induct_has_at_least_one_arbs = length arb_names > 0                : bool;
    val ctxt                         = Proof.context_of pst: Proof.context: Proof.context;

    fun const_has_vname_in_part_of_nth_arg (data:MA.data_w_pattern_n_kind) (cname:string) (vname:string) (arg_numb:int) = ();

    fun ancestor_w_pttrn_n_kind_is_rcsv_const ({point,...}:MA.ancestor_w_pattern_n_kind) = IU.has_recursive_simp_about_const_name ctxt (#name point): bool;
    fun datum_w_pttrn_n_kind_has_ancestor_of ({ancestors,...}:MA.datum_w_pattern_n_kind) (f:MA.ancestor_w_pattern_n_kind -> bool) = exists f ancestors;

    val fst_subg_n_chained_facts_term = IU.pstate_to_1st_subg_n_chained_facts pst                                                   : terms;
    val data_w_pattern_n_kind         = map (MA.trm_to_data_w_pttrn_n_kind ctxt) fst_subg_n_chained_facts_term |> flat              : MA.data_w_pattern_n_kind;
    fun name_of_point_w_kind_is (cname:string) ({name,...} : MA.point_w_kind) = cname = name                                        : bool;
    fun name_of_data_pattern_n_kind_is ({point,...}: MA.datum_w_pattern_n_kind) (cname:string) = name_of_point_w_kind_is cname point: bool;
    fun datum_is_arb_occ (datum_w_pk:MA.datum_w_pattern_n_kind) = exists (name_of_data_pattern_n_kind_is datum_w_pk) arb_names      ;
    val data_w_pattern_n_kind_of_var_occs = filter datum_is_arb_occ data_w_pattern_n_kind                                           ;

    fun exists_an_occ_of (arb_name:string) = exists (K true(*TODO: for some recursive function*)) data_w_pattern_n_kind_of_var_occs;

    fun ancestor_w_pttrn_n_kind_is_rcsv_const ({point,...}:MA.ancestor_w_pattern_n_kind) = IU.has_recursive_simp_about_const_name ctxt (#name point): bool;
    fun datum_w_pttrn_n_kind_has_ancestor_of ({ancestors,...}:MA.datum_w_pattern_n_kind) (f:MA.ancestor_w_pattern_n_kind -> bool) = exists f ancestors;

    val fst_subg_n_chained_facts_term = IU.pstate_to_1st_subg_n_chained_facts pst                                                   : terms;
    val data_w_pattern_n_kind         = map (MA.trm_to_data_w_pttrn_n_kind ctxt) fst_subg_n_chained_facts_term |> flat              : MA.data_w_pattern_n_kind;
    fun name_of_point_w_kind_is (cname:string) ({name,...} : MA.point_w_kind) = cname = name                                        : bool;
    fun name_of_data_pattern_n_kind_is ({point,...}: MA.datum_w_pattern_n_kind) (cname:string) = name_of_point_w_kind_is cname point: bool;
    fun datum_is_arb_occ (datum_w_pk:MA.datum_w_pattern_n_kind) = exists (name_of_data_pattern_n_kind_is datum_w_pk) arb_names      ;
    val data_w_pattern_n_kind_of_var_occs = filter datum_is_arb_occ data_w_pattern_n_kind                                           ;

    fun exists_on_occ (on_name:string, arb_name:string, cname:string) = true(*TODO*);
    fun exists_an_ind (on_name:string, arb_name:string, cname:string) = exists (K true(*TODO*)) vnames;

    fun exist_occs_of_fun    (arb_name:string, cname:MA.data_w_pattern_n_kind) = Utils.exist_mult (K true (*TODO*)) [(*TODO:recusrive functions*)];
    fun exists_a_fun_of      (arb_name:string, cname:MA.data_w_pattern_n_kind) = exists (K true(*TODO*)) [(*TODO:recusrive functions*)];
    fun exists_an_occ_of_arb (arb_name:string)                                 = exists (K true(*TODO: for some recursive function*)) data_w_pattern_n_kind_of_var_occs;
    val forall_arb = forall exists_an_occ_of_arb arb_names;
  in
    (*TODO*)()
  end;

fun pstate_to_ons_n_vnames_in_nth_args_of_const (trm_to_nth_args_of_const: string -> term -> terms)
  (cname:string) (pstate:Proof.state) (mods:ITG.modifiers) =
  let
    val cnames_in_1st_subg_n_chained_facts = IU.pstate_to_cnames_in_1st_subg_n_chained_facts pstate                                : strings;
    val chained_n_fst_subg                 = IU.pstate_to_1st_subg_n_chained_facts pstate                                          : terms;
    val nth_args_of_set_member             = Utils.map_flat_distinct (trm_to_nth_args_of_const cname) Term.aconv chained_n_fst_subg: terms;
    val vnames_in_snd_args_of_set_member   = Utils.map_flat_distinct IU.get_free_var_names_in_trm (op =) nth_args_of_set_member    : strings;
    val on_names                           = mods |> IS.pick_vars |> IS.get_names                                                  : strings;
    val arb_names                          = mods |> IS.pick_arbs |> IS.get_names                                                  : strings;
  in
    {has_ind_vars   = null on_names                                          : bool,
     has_arb_vars   = null arb_names                                         : bool,
     has_const      = exists (equal cname) cnames_in_1st_subg_n_chained_facts: bool,
     ons            = on_names                                               : strings,
     arbs           = arb_names                                              : strings,
     vnames         = vnames_in_snd_args_of_set_member                       : strings}
  end;

(* helper functions for ass_023, ass_024, and ass_041 *)
fun pstate_to_ons_n_vnames_in_snd_args_of_set_member (pstate:Proof.state) (mods:ITG.modifiers) =
  pstate_to_ons_n_vnames_in_nth_args_of_const IU.trm_to_snd_args_of_const "Set.member" pstate mods;

(* ass_023. checks if the proof context contains local assumption *)
fun ass_023 (pstate:Proof.state) (mods:ITG.modifiers) =
  let
    val {has_ind_vars, has_const, ons, vnames,...} = pstate_to_ons_n_vnames_in_snd_args_of_set_member pstate mods;
  in
    has_ind_vars andalso has_const andalso Utils.members (op =) ons vnames
  end;

(* ass_024. checks if the proof context contains local assumption *)
fun ass_024 (pstate:Proof.state) (mods:ITG.modifiers) =
  let
    val {has_ind_vars, has_const, ons, vnames,...} = pstate_to_ons_n_vnames_in_snd_args_of_set_member pstate mods;
  in
    has_ind_vars andalso has_const andalso Utils.a_member (op =) ons vnames
  end;

(* helper functions for ass_025, ass_026, and ass_027 *)
fun pstate_to_ons_n_vnames_in_fst_args_of_list_set (pstate:Proof.state) (mods:ITG.modifiers) =
  pstate_to_ons_n_vnames_in_nth_args_of_const IU.trm_to_fst_args_of_const "List.list.set" pstate mods;

(* ass_025. checks if the proof context contains local assumption *)
fun ass_025 (pstate:Proof.state) (mods:ITG.modifiers) =
  let
    val {has_ind_vars, has_const, ons, vnames,...} = pstate_to_ons_n_vnames_in_fst_args_of_list_set pstate mods;
  in
    has_ind_vars andalso has_const andalso Utils.a_member (op =) ons vnames
  end;

(* ass_026. *)
fun ass_026 (pstate:Proof.state) (mods:ITG.modifiers) =
  let
    val {has_ind_vars, has_const, ons, vnames,...} = pstate_to_ons_n_vnames_in_fst_args_of_list_set pstate mods;
  in
    has_ind_vars andalso has_const andalso Utils.members (op =) ons vnames
  end;

(* ass_027. *)
fun ass_027 (pstate:Proof.state) (mods:ITG.modifiers) =
  let
    val {has_ind_vars, has_const, ons, vnames,...} = pstate_to_ons_n_vnames_in_fst_args_of_list_set pstate mods;
  in
    has_ind_vars andalso has_const andalso not (Utils.a_member (op =) ons vnames)
  end;

fun ind_var_of_certain_typ (pstate:Proof.state) (mods:ITG.modifiers)
  (trm_to_consts_fvars_vars: term -> {consts: term list, frees: term list, vars: term list}) =
  let
    val on_names                     = mods |> IS.pick_vars |> IS.get_names                                       : strings;
    val has_ons                      = null on_names |> not                                                       : bool;
    val fst_subg_n_chained_facts     = IU.pstate_to_1st_subg_n_chained_facts pstate                               : terms;
    fun trm_to_fvar_names (trm:term) = trm |> trm_to_consts_fvars_vars |> #frees |> map (fst o Term.dest_Free)    : strings;
    val fun_fvar_names               = map trm_to_fvar_names fst_subg_n_chained_facts |> flat |> duplicates (op =): strings;
    val has_a_fvar_of_certain_typ    = (not o null) fun_fvar_names                                                : bool;
    val no_ind_var_is_certain_type   = Utils.a_member (op =) on_names fun_fvar_names |> not                       : bool;
    val some_ind_var_is_certain_type = Utils.a_member (op =) on_names fun_fvar_names                              : bool;
    val all_ind_var_is_certain_type  = Utils.members (op =) on_names fun_fvar_names                               : bool;
  in
    {has_a_fvar_of_certain_typ    = has_a_fvar_of_certain_typ,
     has_ons                      = has_ons,
     no_ind_var_is_certain_type   = no_ind_var_is_certain_type,
     some_ind_var_is_certain_type = some_ind_var_is_certain_type,
     all_ind_var_is_certain_type  = all_ind_var_is_certain_type}
  end;

fun helper_ass_028_ass_030_ass_040 (pstate:Proof.state) (mods:ITG.modifiers)
  (trm_to_consts_fvars_vars: term -> {consts: term list, frees: term list, vars: term list}) =
  let
    val result = ind_var_of_certain_typ pstate mods trm_to_consts_fvars_vars;
  in
     #has_a_fvar_of_certain_typ result andalso #has_ons result andalso #no_ind_var_is_certain_type result
  end;

(* ass_028. *)
fun ass_028 (pstate:Proof.state) (mods:ITG.modifiers) = helper_ass_028_ass_030_ass_040 pstate mods IU.trm_to_funs;

(* helper functions for ass_029 *)
fun pstate_to_ons_n_vnames_in_snd_args_of_list_nth (pstate:Proof.state) (mods:ITG.modifiers) =
  pstate_to_ons_n_vnames_in_nth_args_of_const IU.trm_to_snd_args_of_const "List.nth" pstate mods;

(* ass_029 *)
fun ass_029 (pstate:Proof.state) (mods:ITG.modifiers) =
  let
    val {has_arb_vars, has_const, arbs, vnames,...} = pstate_to_ons_n_vnames_in_snd_args_of_list_nth pstate mods;
  in
    has_arb_vars andalso has_const andalso Utils.a_member (op =) arbs vnames
  end;

(* ass_030. *)
fun ass_030 (pstate:Proof.state) (mods:ITG.modifiers) = helper_ass_028_ass_030_ass_040 pstate mods IU.trm_to_sets_and_lists;

(* pstate_to_on_names_n_vnames_in_chained_facts: helper function for ass_031, ass_032, ass_043. *)
fun pstate_to_on_names_n_vnames_in_chained_facts (pstate:Proof.state) (mods:ITG.modifiers) =
  let
    val chained_facts           = IU.pstate_to_chained_facts_as_terms pstate : terms;
    val vnames_in_chained_facts = IU.get_free_var_names_in_trms chained_facts: strings;
    val on_names                = mods |> IS.pick_vars |> IS.get_names       : strings;
  in
    {on_names                = on_names               : strings,
     vnames_in_chained_facts = vnames_in_chained_facts: strings}
  end;

(* ass_031. *)
fun ass_031 (pstate:Proof.state) (mods:ITG.modifiers) =
  let
    val {on_names, vnames_in_chained_facts} = pstate_to_on_names_n_vnames_in_chained_facts pstate mods;
  in
    not (null on_names) andalso Utils.a_member (op =) on_names vnames_in_chained_facts
  end;

(* ass_032. *)
fun ass_032 (pstate:Proof.state) (mods:ITG.modifiers) =
  let
    val {on_names, vnames_in_chained_facts} = pstate_to_on_names_n_vnames_in_chained_facts pstate mods;
  in
    not (null on_names) andalso Utils.members (op =) on_names vnames_in_chained_facts
  end;

(* pstate_to_on_names_n_vnames_in_prems_in_fst_subg: helper function for ass_033, ass_034, ass_044 to ass_047. *)
fun pstate_to_on_names_n_vnames_in_premises (pstate:Proof.state) (mods:ITG.modifiers) =
  let
    val {fst_subg, chained_facts}        = IU.pstate_to_1st_subg_n_chained_facts_record pstate;
    val prems_in_fst_subg                = omap Logic.strip_imp_prems fst_subg |> these        : terms;
    val prems_in_chained_facts           = map Logic.strip_imp_prems chained_facts |> flat     : terms;
    val on_names                         = mods |> IS.pick_vars |> IS.get_names                : strings;
  in
    {on_names                            = on_names                                            : strings,
     has_ind_vars                        = not (null on_names)                                 : bool,
     has_meta_imp_in_fst_subg            = IU.trms_have_cname "Pure.imp" (the_list fst_subg)   : bool,
     has_meta_imp_in_chained_facts       = IU.trms_have_cname "Pure.imp" chained_facts         : bool,
     vnames_in_premises_in_fst_subg      = IU.get_free_var_names_in_trms prems_in_fst_subg     : strings,
     vnames_in_premises_in_chained_facts = IU.get_free_var_names_in_trms prems_in_chained_facts: strings
     }
  end;

(* ass_033 *)
fun ass_033 (pstate:Proof.state) (mods:ITG.modifiers) =
  let
    val {on_names, has_ind_vars, has_meta_imp_in_fst_subg, vnames_in_premises_in_fst_subg, ...} = pstate_to_on_names_n_vnames_in_premises pstate mods;
  in
    has_meta_imp_in_fst_subg andalso has_ind_vars andalso Utils.a_member (op =) on_names vnames_in_premises_in_fst_subg
  end;

(* ass_034 *)
fun ass_034 (pstate:Proof.state) (mods:ITG.modifiers) =
  let
    val {on_names, has_ind_vars, has_meta_imp_in_fst_subg, vnames_in_premises_in_fst_subg, ...} = pstate_to_on_names_n_vnames_in_premises pstate mods;
  in
    has_meta_imp_in_fst_subg andalso has_ind_vars andalso Utils.members (op =) on_names vnames_in_premises_in_fst_subg
  end;

(* ass_040. *)
fun ass_040 (pstate:Proof.state) (mods:ITG.modifiers) = helper_ass_028_ass_030_ass_040 pstate mods IU.trm_to_nats;

(* ass_041. checks if the proof context contains local assumption *)
fun ass_041 (pstate:Proof.state) (mods:ITG.modifiers) =
  let
    val {has_ind_vars, has_const, ons, vnames,...} = pstate_to_ons_n_vnames_in_snd_args_of_set_member pstate mods;
  in
    has_ind_vars andalso has_const andalso not (Utils.a_member (op =) ons vnames)
  end;

(* ass_042. *)
fun ass_042 (pstate:Proof.state) (mods:ITG.modifiers) =
  let
    val {has_arb_vars, has_const, arbs, vnames,...} = pstate_to_ons_n_vnames_in_snd_args_of_list_nth pstate mods;
  in
    has_arb_vars andalso has_const andalso Utils.a_member (op =) arbs vnames
  end;

(* ass_043. *)
fun ass_043 (pstate:Proof.state) (mods:ITG.modifiers) =
  let
    val {on_names, vnames_in_chained_facts} = pstate_to_on_names_n_vnames_in_chained_facts pstate mods;
  in
    not (null on_names) andalso not (Utils.a_member (op =) on_names vnames_in_chained_facts)
  end;

(* ass_044 *)
fun ass_044 (pstate:Proof.state) (mods:ITG.modifiers) =
  let
    val {on_names, has_ind_vars, has_meta_imp_in_chained_facts, vnames_in_premises_in_chained_facts, ...} = pstate_to_on_names_n_vnames_in_premises pstate mods;
  in
    has_meta_imp_in_chained_facts andalso has_ind_vars andalso not (Utils.a_member (op =) on_names vnames_in_premises_in_chained_facts)
  end;

(* ass_045 *)
fun ass_045 (pstate:Proof.state) (mods:ITG.modifiers) =
  let
    val {on_names, has_ind_vars, has_meta_imp_in_chained_facts, vnames_in_premises_in_chained_facts, ...} = pstate_to_on_names_n_vnames_in_premises pstate mods;
  in
    has_meta_imp_in_chained_facts andalso has_ind_vars andalso not (Utils.a_member (op =) on_names vnames_in_premises_in_chained_facts)
  end;

(* ass_046 *)
fun ass_046 (pstate:Proof.state) (mods:ITG.modifiers) =
  let
    val {on_names, has_ind_vars, has_meta_imp_in_fst_subg, vnames_in_premises_in_fst_subg, ...} = pstate_to_on_names_n_vnames_in_premises pstate mods;
  in
    has_meta_imp_in_fst_subg andalso has_ind_vars andalso not (Utils.a_member (op =) on_names vnames_in_premises_in_fst_subg)
  end;

(* ass_047 *)
fun ass_047 (pstate:Proof.state) (mods:ITG.modifiers) =
  let
    val {on_names, has_ind_vars, has_meta_imp_in_chained_facts, vnames_in_premises_in_chained_facts, ...} = pstate_to_on_names_n_vnames_in_premises pstate mods;
  in
    has_meta_imp_in_chained_facts andalso has_ind_vars andalso Utils.members (op =) on_names vnames_in_premises_in_chained_facts
  end;

fun helper_ass_048_ass_049_ass_050 (pstate:Proof.state) (mods:ITG.modifiers)
  (trm_to_consts_fvars_vars: term -> {consts: term list, frees: term list, vars: term list}) =
  let
    val res = ind_var_of_certain_typ pstate mods trm_to_consts_fvars_vars;
  in
     #has_a_fvar_of_certain_typ res andalso #has_ons res andalso #some_ind_var_is_certain_type res
  end;

(* ass_048 *)
fun ass_048 (pstate:Proof.state) (mods:ITG.modifiers) = helper_ass_048_ass_049_ass_050 pstate mods IU.trm_to_nats;

(* ass_049 *)
fun ass_049 (pstate:Proof.state) (mods:ITG.modifiers) = helper_ass_028_ass_030_ass_040 pstate mods IU.trm_to_funs;

(* ass_050 *)
fun ass_050 (pstate:Proof.state) (mods:ITG.modifiers) = helper_ass_028_ass_030_ass_040 pstate mods IU.trm_to_sets_and_lists;

fun helper_ass_051_ass_052_ass_053 (pstate:Proof.state) (mods:ITG.modifiers)
  (trm_to_consts_fvars_vars: term -> {consts: term list, frees: term list, vars: term list}) =
  let
    val res = ind_var_of_certain_typ pstate mods trm_to_consts_fvars_vars;
  in
     #has_a_fvar_of_certain_typ res andalso #has_ons res andalso #all_ind_var_is_certain_type res
  end;

(* ass_051 *)
fun ass_051 (pstate:Proof.state) (mods:ITG.modifiers) = helper_ass_051_ass_052_ass_053 pstate mods IU.trm_to_nats;

(* ass_052 *)
fun ass_052 (pstate:Proof.state) (mods:ITG.modifiers) = helper_ass_051_ass_052_ass_053 pstate mods IU.trm_to_funs;

(* ass_053 *)
fun ass_053 (pstate:Proof.state) (mods:ITG.modifiers) = helper_ass_051_ass_052_ass_053 pstate mods IU.trm_to_sets_and_lists;

(*TODO*)
fun mk_ass_results (pre_pst:Proof.state) (mods:ITG.modifiers) = [
(*001*)ass_001 pre_pst mods,
(*002*)ass_002 pre_pst mods,
(*003*)ass_003 pre_pst mods,
(*004*)true,
(*005*)ass_005 pre_pst mods,
(*006*)ass_006 pre_pst mods,
(*007*)ass_007 pre_pst mods,
(*008*)true,
(*009*)ass_009 pre_pst mods,
(*010*)true,
(*011*)false,
(*012*)ass_012 pre_pst mods,
(*013*)ass_013 pre_pst mods,
(*014*)ass_014 pre_pst mods,
(*015*)ass_015 pre_pst mods,
(*016*)ass_016 pre_pst mods,
(*017*)ass_017 pre_pst mods,
(*018*)ass_018 pre_pst mods,
(*019*)ass_019 pre_pst mods,
(*020*)ass_020 pre_pst mods,
(*021*)true,
(*022*)true,
(*023*)ass_023 pre_pst mods,
(*024*)ass_024 pre_pst mods,
(*025*)ass_025 pre_pst mods,
(*026*)ass_026 pre_pst mods,
(*027*)ass_027 pre_pst mods,
(*028*)ass_028 pre_pst mods,
(*029*)ass_029 pre_pst mods,
(*030*)true,
(*031*)ass_031 pre_pst mods,
(*032*)ass_032 pre_pst mods,
(*033*)ass_033 pre_pst mods,
(*034*)ass_034 pre_pst mods,
(*035*)true,
(*036*)true,
(*037*)true,
(*038*)true,
(*039*)true,
(*040*)ass_040 pre_pst mods,
(*041*)ass_041 pre_pst mods,
(*042*)ass_042 pre_pst mods,
(*043*)ass_043 pre_pst mods,
(*044*)ass_044 pre_pst mods,
(*045*)ass_045 pre_pst mods,
(*046*)ass_046 pre_pst mods,
(*047*)ass_047 pre_pst mods,
(*048*)ass_048 pre_pst mods,
(*049*)ass_049 pre_pst mods,
(*050*)ass_050 pre_pst mods,
(*051*)ass_051 pre_pst mods,
(*052*)ass_052 pre_pst mods,
(*053*)ass_053 pre_pst mods
];

fun is_used (meth_name:string) (pre_pst:Proof.state) (model_post:thm) (mods:ITG.modifiers) =
    mk_post_thm meth_name pre_pst mods
<$> (curry Thm.eq_thm model_post)
|>  (fn used:bool option => Option.getOpt (used, false)): bool;

fun mk_a_line (meth_name:string) (pre_pst:Proof.state) (model_post:thm) (mods:ITG.modifiers) =
  {used        = is_used meth_name pre_pst model_post mods,
   ass_results = mk_ass_results (pre_pst:Proof.state) (mods:ITG.modifiers),
   meth_w_args = IS.mods_to_string mods
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
        val ass_results = map bool_to_int_str (#ass_results line): strings;
      in
        space_implode "" (used::ass_results)
      end;

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
                 ass_results: bool list,
                 meth_w_args: string};
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