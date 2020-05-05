theory Evaluate_Smart_Induct
  imports "Smart_Induct.Smart_Induct"
  keywords "apply2" :: prf_script
   and     "proof2" :: prf_block
   and     "by2"    :: "qed"
begin

ML\<open> (*enumerate*)
fun enumerate' [] acc = []
  | enumerate' (x::xs) acc = (acc, x) :: enumerate' xs (acc + 1)

fun enumerate xs = enumerate' xs 1;
\<close>

ML\<open>

local

infix 1 <*> <$>;
fun (f <*> m) = Utils.opt_app f m;  
fun (m <$> f) = Option.map f m;

structure LiFtEr_Assertion = Apply_LiFtEr.LiFtEr_Assertion;

type trans_trans = Toplevel.transition -> Toplevel.transition;
open Parser_Combinator;
open LiFtEr_Util;

in

datatype ind_mod_gen = Ion of LiFtEr_Util.induct_on | Iarb of LiFtEr_Util.induct_arb | Irule of LiFtEr_Util.induct_rule;

fun psl_ind_mod_to_lifter_ind_mod (Dynamic_Induct.Induct_Seed.On        str) = LiFtEr_Util.Print str |> LiFtEr_Util.Ind_On  |> Ion
  | psl_ind_mod_to_lifter_ind_mod (Dynamic_Induct.Induct_Seed.Arbitrary str) = LiFtEr_Util.Print str |> LiFtEr_Util.Ind_Arb |> Iarb
  | psl_ind_mod_to_lifter_ind_mod (Dynamic_Induct.Induct_Seed.Rule      str) = LiFtEr_Util.Ind_Rule str |> Irule;

fun psl_ind_mods_to_lifter_ind_mods' (psl_ind_mod::psl_ind_mods) (acc as Ind_Mods {ons, arbs, rules}) = (case psl_ind_mod_to_lifter_ind_mod psl_ind_mod of
      Ion   modi => psl_ind_mods_to_lifter_ind_mods' (psl_ind_mods) (Ind_Mods {ons = ons @ [modi], arbs = arbs,          rules = rules})
    | Iarb  modi => psl_ind_mods_to_lifter_ind_mods' (psl_ind_mods) (Ind_Mods {ons = ons,          arbs = arbs @ [modi], rules = rules})
    | Irule modi => psl_ind_mods_to_lifter_ind_mods' (psl_ind_mods) (Ind_Mods {ons = ons,          arbs = arbs,          rules = rules @ [modi]}))
  | psl_ind_mods_to_lifter_ind_mods' [] acc = acc;

fun psl_ind_mods_to_lifter_ind_mods (psl_ind_mods: Dynamic_Induct.Induct_Seed.modifier list) =
    psl_ind_mods_to_lifter_ind_mods' psl_ind_mods (Ind_Mods {ons = [], arbs = [], rules = []}): LiFtEr_Util.ind_mods;

type triple = {nth_candidate: int, score: int, ind_mods: ind_mods};

fun pst_to_top_10_mods (pst:Proof.state) =
  let
    val psl_modifierss             = Multi_Stage_Screening.pst_to_promising_modss pst               : Dynamic_Induct.Induct_Seed.modifier list list;
    val lifter_modifierss          = map psl_ind_mods_to_lifter_ind_mods psl_modifierss      : LiFtEr_Util.ind_mods list;
    fun ind_mods_to_pair ind_mods  = ((Scoring_Using_LiFtEr.pst_n_ind_mods_to_result_pair pst ind_mods), ind_mods): (int * ind_mods);
    val pairs                      = Par_List.map ind_mods_to_pair lifter_modifierss         : (int * LiFtEr_Util.ind_mods) list;
    val sorted_pairs               = sort (fn (p1, p2) => Int.compare (fst p1, fst p2)) pairs |> rev: (int * LiFtEr_Util.ind_mods) list;
    val best_pairs                 = take 10 sorted_pairs;
    val best_pairs_with_rank       = enumerate best_pairs: (int * (int * ind_mods)) list;
    fun transform xs = map (fn (a, (b, c)) => {nth_candidate = a, score = b, ind_mods = c}) best_pairs_with_rank; 
  in
    transform best_pairs_with_rank: triple list
  end;

val on_construct   = Dynamic_Induct.Induct_Seed.On;
val arb_construct  = Dynamic_Induct.Induct_Seed.Arbitrary;
val rule_construct = Dynamic_Induct.Induct_Seed.Rule;

fun lifter_ind_mods_to_psl_ind_mods (Ind_Mods {ons, arbs, rules}) =
    map (on_construct   o dest_print o dest_induct_on) ons @
    map (arb_construct  o dest_print o dest_induct_arb) arbs @
    map (rule_construct o dest_induct_rule) rules;


val pst_to_model_subgoals = undefined: Proof.state -> thm;

type result = {
  location: (string * string),
  top_nth: int option,
  total_candidates: int,
  after_1_screening: int,
  after_2_screening: int,
  score: int option,
  time : int};

fun result_to_string
 ({location,
   top_nth,
   total_candidates,
   after_1_screening,
   after_2_screening,
   score,
   time}: result) =
let
  fun print_int_option NONE = "-"
    | print_int_option (SOME n) = Int.toString n;
  val list =
    [fst location, snd location,
     print_int_option top_nth,
     Int.toString total_candidates,
     Int.toString after_1_screening,
     Int.toString after_2_screening,
     print_int_option score,
     Int.toString time
     ];
  val one_line = String.concatWith ";" list;
in
   one_line: string
end;

end;

val write_result = undefined: result -> unit;

\<close>

ML\<open> structure Induct_Seed (*: DYNAMIC_TACTIC_GENERATOR_SEED*) =
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
\<close>

ML\<open>
fun ind_mods_to_string (mods:LiFtEr_Util.ind_mods) =
  let
    fun psl_ind_mods_to_str (mods: Dynamic_Induct.Induct_Seed.modifiers) : string =
        enclose "(" ")" ("induct" ^ Dynamic_Induct.Induct_Seed.mods_to_string mods): string;
    val psl_ind_mods = lifter_ind_mods_to_psl_ind_mods mods: Dynamic_Induct.Induct_Seed.modifier list;
    val meth_string = psl_ind_mods_to_str psl_ind_mods 
  in
    meth_string: string
  end;

fun modifiers_to_str (meth_name:string) (mods: Induct_Seed.modifiers) : string =
  enclose "(" ")" (meth_name ^ Induct_Seed.mods_to_string mods);

fun str_to_nontac (meth:string) : Dynamic_Utils.state Dynamic_Utils.nontac =
  Isabelle_Utils.TIMEOUT_in 3.0 (Utils.try_with (K Seq.empty) Dynamic_Utils.string_to_nontac_on_pstate meth);

fun ind_mods_to_nontacs (ind_mods:LiFtEr_Util.ind_mods) = ind_mods
  |> ind_mods_to_string  
  |> try str_to_nontac: Dynamic_Utils.state Dynamic_Utils.nontac option;

fun get_fst_result (pst:Proof.state) (nontac: Dynamic_Utils.state Dynamic_Utils.nontac) : Dynamic_Utils.state option =
      (try nontac pst: Dynamic_Utils.state Seq.seq option)
  >>= (try Seq.hd: Dynamic_Utils.state Seq.seq -> Dynamic_Utils.state option);

fun state_n_lifter_ind_mods_to_fst_thm (pst:Dynamic_Utils.state) (lifter_ind_mods:LiFtEr_Util.ind_mods): thm =
  let
    val meth_str  = ind_mods_to_string lifter_ind_mods: string;
    val nontac    = str_to_nontac meth_str            : Dynamic_Utils.state Dynamic_Utils.nontac;
    val state_opt = get_fst_result pst nontac         : Dynamic_Utils.state option;
    val thm_opt   = Option.map Isabelle_Utils.proof_state_to_thm state_opt: thm option;
    val thm       = Option.getOpt (thm_opt, FalseE)   : thm;
  in
    thm
  end;

fun model_meth_n_pst_to_fst_thm (model_meth:Method.text_range) (pst:Proof.state): thm =
  let
    val model_result_option = try (Proof.apply model_meth) pst
      >>= try Seq.filter_results
      >>= try Seq.hd
      >>= try Isabelle_Utils.proof_state_to_thm: thm option;
    val model_result = Option.getOpt (model_result_option, TrueI): thm;
  in
    model_result
  end;
\<close>

ML\<open> type triple_result = {nth_candidate: int, score: int, ind_mods: LiFtEr_Util.ind_mods, coincide:bool}; \<close>

ML\<open> fun pst_n_model_meth_n_triple_to_triple_result (pst:Dynamic_Utils.state) (model_meth:Method.text_range)
  {nth_candidate, score, ind_mods} =
let
  val smart_induct_result = state_n_lifter_ind_mods_to_fst_thm pst ind_mods: thm;

  val model_result        = model_meth_n_pst_to_fst_thm model_meth pst     : thm;
  val coincide            = Thm.eq_thm (model_result, smart_induct_result) : bool;
in
  {nth_candidate = nth_candidate, score = score, ind_mods = ind_mods, coincide = coincide}
end;
\<close>

ML\<open> fun triple_result_ord (t1:triple_result, t2:triple_result) = Int.compare (#nth_candidate t1, #nth_candidate t2): order; \<close>

ML\<open>
fun pst_to_promising_modss (pst:Proof.state) =
let
  val all_modifiers             = Multi_Stage_Screening.pst_to_modifiers pst;
  val functioning_modifiers     = Multi_Stage_Screening.pst_to_functioning_modifiers pst: Multi_Stage_Screening.ITG.modifiers list;
  val no_sche_introducing_modss = filter (Multi_Stage_Screening.no_sch_in_pre_but_in_post pst) functioning_modifiers: Multi_Stage_Screening.ITG.modifiers list;
in
  {total_candidates  = length all_modifiers            : int,
   after_1_screening = length functioning_modifiers    : int,
   after_2_screening = length no_sche_introducing_modss: int}
end;
\<close>

ML\<open> fun evaluate (pst:Proof.state) (m: Method.text_range) =
let
val _ = tracing "from evaluate";
  val time_before_smart_induct = Time.now();
  val top_10_triples = pst_to_top_10_mods pst: triple list;
val _ = tracing ("The length of top_10_triples is " ^ Int.toString (length top_10_triples));
  val time_after_smart_induct  = Time.now ();
  val duration = Time.toMilliseconds (time_after_smart_induct - time_before_smart_induct);
  val score          = try (#score o hd) top_10_triples: int option; 
  val triple_results = map (pst_n_model_meth_n_triple_to_triple_result pst m) top_10_triples: triple_result list;
val _ = tracing ("The length of triple_results is " ^ Int.toString (length triple_results));
  val sorted_triple_results = sort triple_result_ord triple_results: triple_result list;
val _ = tracing ("The length of sorted_triple_results is " ^ Int.toString (length sorted_triple_results));
  val sorted_coincides      = filter (#coincide) sorted_triple_results: triple_result list;
val _ = tracing ("The length of sorted_coincides is " ^ Int.toString (length sorted_coincides));
  val top_nth = try hd sorted_coincides <$> #nth_candidate: int option;

  fun string_some NONE = "Method_None_SOMETHING_WENT_WRONG"
   |  string_some (SOME x) = x;
  val location =
     (Method.position (SOME m) |> Position.file_of |> string_some,
      Method.position (SOME m) |> Position.line_of |> Option.map Int.toString |> string_some);
  val {total_candidates, after_1_screening, after_2_screening} = pst_to_promising_modss pst;
  val result =
      {location = location,
       top_nth  = top_nth,
       after_1_screening = after_1_screening,
       after_2_screening = after_2_screening,
       total_candidates  = total_candidates,
       score             = score,
       time              = duration
       }: result;

in result_to_string result end;

\<close>

ML\<open>
local

structure SUL = Scoring_Using_LiFtEr;
(*Method.text_range = text * Position.range;*)
fun state_to_unit  (pst:Proof.state) (m) =
  let
    val message = evaluate pst m;
val _ = tracing message;
    val path = Resources.master_directory @{theory} |> File.platform_path : string;
    val path_to_database  = path ^ "/Database" : string;
    val _ = Isabelle_System.bash
            ("echo -n '" ^ message ^"\n" ^
             "' >> " ^ path_to_database);
  in () end

in

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>apply2\<close> "initial goal refinement step (unstructured)"
    (Method.parse >> (fn m => (
       Method.report m;
       Toplevel.proofs (fn pst =>
         (state_to_unit pst m;
          Proof.apply m pst)
       ))));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>proof2\<close> "backward proof step"
    (Scan.option Method.parse >> (fn m =>
      (Option.map Method.report m;
       Toplevel.proof (fn state =>
         let
          val _= Option.map (state_to_unit state) m;
          val state' = state |> Proof.proof m |> Seq.the_result "";
          val _ =
            Output.information
              (Proof_Context.print_cases_proof (Proof.context_of state) (Proof.context_of state'));
        in state' end))))

fun pst_to_unit m = (fn toplevel_state => state_to_unit (Toplevel.proof_of toplevel_state) m): Toplevel.state -> unit;  fun get_name (Method.Source src) = ((Token.name_of_src src)|>fst)

    fun local_terminal_proof (m1, m2) = (Toplevel.proof o 
          (fn m => 
            (fn state:Proof.state => 
              (state_to_unit state m1;
            Proof.local_future_terminal_proof m state)))) (m1, m2);
    fun global_terminal_proof (m1, m2) = 
        (Toplevel.end_proof o 
         K o 
         (fn m => 
             (fn state => (
                state_to_unit state m1;
                Proof.global_future_terminal_proof m state)))) (m1, m2)
    
    fun terminal_proof m = local_terminal_proof m o global_terminal_proof m;
    
    val _ =
      Outer_Syntax.command @{command_keyword by2} "terminal backward proof"
        (Method.parse -- Scan.option Method.parse >> (fn (m1, m2) =>
         (Method.report m1;
          Option.map Method.report m2;
          terminal_proof (m1, m2))));

end;
\<close>

end