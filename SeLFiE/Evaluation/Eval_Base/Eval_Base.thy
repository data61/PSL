theory Eval_Base
  imports Main "SeLFiE.SeLFiE" Main(*to get Nitpick_Util*)
  keywords "apply2" :: prf_script
   and     "proof2" :: prf_block
   and     "by2"    :: "qed"
begin

ML\<open> (*enumerate*)
fun enumerate' [] _ = []
  | enumerate' (x::xs) acc = (acc, x) :: enumerate' xs (acc + 1)

fun enumerate xs = enumerate' xs 1;

fun timeout f = Isabelle_Utils.timeout_apply (seconds 5.0) f;
\<close>

ML\<open>

local

infix 1 <*> <$>;

type trans_trans = Toplevel.transition -> Toplevel.transition;
open Parser_Combinator;

in
(*
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
*)

structure AS = Apply_SeLFiE;
structure SU = SeLFiE_Util;

fun pst_to_top_10_mods (pst:Proof.state) =
  let
    val thm                       = Isabelle_Utils.proof_state_to_thm pst                            : thm;
    val thm_term                  = Thm.prop_of thm                                                  : term;
    val outer_path_to_unode_table = Outer_Path_To_Unode.pst_n_trm_to_path_to_unode_table pst thm_term: Outer_Path_To_Unode.path_to_unode_table;
    val (ind_best_records, ind_max_point) = AS.score_n_induct_argss_n_proof_state_to_best_pairs 0.0 [] [] AS.Induction_Heuristic 5 pst outer_path_to_unode_table;
    fun record_to_pair {score, modifiers,...} = (score, modifiers);
    val best_pairs            = Par_List.map record_to_pair ind_best_records
                              : (real * SU.induct_arguments) list;
    val arb_pairs             = Smart_Construction.proof_state_n_terms_n_induct_argumentss_to_induct_argumentss_w_arbs pst (Isabelle_Utils.pstate_to_1st_subg_n_chained_facts pst) best_pairs
                              :  (real * SU.induct_arguments) list;
    val (arb_best_records, arb_max_point) = AS.score_n_induct_argss_n_proof_state_to_best_pairs ind_max_point arb_pairs best_pairs AS.Generalization_Heuristic 10 pst outer_path_to_unode_table;
    val enumerated_arb_bests  = enumerate arb_best_records
                              :(int * {modifiers: SeLFiE_Util.induct_arguments, score: real}) list
    fun transform (rank, {modifiers, score,...}) = {nth_candidate = rank, score = score, ind_mods = modifiers};
  in
    map transform enumerated_arb_bests
  end;

type result = {
  location: (string * string),
  top_nth: int option,
(*
  after_1_screening: int,
  after_2_screening: int,
  after_3_screening: int,
  after_4_screening: int,
  after_5_screening: int,
*)
  score: real option,
  time : int};

fun result_to_string
 ({location,
   top_nth,
(*
   after_1_screening,
   after_2_screening,
   after_3_screening,
   after_4_screening,
   after_5_screening,
*)
   score,
   time}: result) =
let
  fun print_int_option NONE = "-"
    | print_int_option (SOME n) = Int.toString n;
  fun print_real_option NONE = "-"
    | print_real_option (SOME n) = Real.toString n;
  val list =
    [fst location, snd location,
     print_int_option top_nth,
(*
     Int.toString after_1_screening,
     Int.toString after_2_screening,
     Int.toString after_3_screening,
     Int.toString after_4_screening,
     Int.toString after_5_screening,
*)
     print_real_option score,
     Int.toString time
     ];
  val one_line = String.concatWith "," list;
in
   one_line: string
end;

end;

val write_result = undefined: result -> unit;

\<close>

ML\<open> fun model_meth_n_pst_to_fst_thm (model_meth:Method.text_range) (pst:Proof.state): thm =
  let
    val model_result_option = try (Proof.apply model_meth) pst
      >>= try Seq.filter_results
      >>= try Seq.hd
      >>= try Isabelle_Utils.proof_state_to_thm: thm option;
    val model_result = Option.getOpt (model_result_option, TrueI): thm;
  in
    model_result:thm
  end;
\<close>

ML\<open> type triple_result = {nth_candidate: int, score: real, ind_mods: SeLFiE_Util.induct_arguments, coincide:bool}; \<close>

ML\<open> fun pst_n_model_meth_n_triple_to_triple_result (pst:Proof.state) (model_meth:Method.text_range)
  {nth_candidate, score, ind_mods as SeLFiE_Util.Induct_Arguments {ons, arbs, rules}} =
let
  fun mk_new_ind_mods new_arbs = SeLFiE_Util.Induct_Arguments {ons = ons, arbs = new_arbs, rules = rules}: SeLFiE_Util.induct_arguments;
  val arbss_permutated     = Nitpick_Util.all_permutations arbs                        : strings list;
  val ind_mods_permutateds = map mk_new_ind_mods arbss_permutated                      : SeLFiE_Util.induct_arguments list;
  val result_psts       = map (fn mods => Screening.induction_arguments_to_tactic_on_proof_state_w_timeout mods pst) ind_mods_permutateds; 
  val result_thms       = map (Isabelle_Utils.proof_state_to_thm o Seq.hd) result_psts                     : thm list;
  val model_result      = model_meth_n_pst_to_fst_thm model_meth pst                                       : thm;
  val coincide          = exists (fn selfie_result => Thm.eq_thm (model_result, selfie_result)) result_thms: bool
in
  {nth_candidate = nth_candidate, score = score, ind_mods = ind_mods, coincide = coincide}
end;
\<close>

ML\<open> fun triple_result_ord (t1:triple_result, t2:triple_result) = Int.compare (#nth_candidate t1, #nth_candidate t2): order; \<close>

ML\<open> fun evaluate (pst:Proof.state) (m: Method.text_range) =
let
  val time_before_smart_induct = Time.now();
  val top_10_triples' = try (timeout pst_to_top_10_mods) pst
                     : {ind_mods: SeLFiE_Util.induct_arguments, nth_candidate: int, score: real} list option;
  val top_10_triples = these top_10_triples';
  val time_after_smart_induct  = Time.now ();
  val duration = Time.toMilliseconds (time_after_smart_induct - time_before_smart_induct);
  val score          = try (#score o hd) top_10_triples: real option; 
  val triple_results = map (pst_n_model_meth_n_triple_to_triple_result pst m) top_10_triples: triple_result list;
  val sorted_triple_results = sort triple_result_ord triple_results: triple_result list;
  val sorted_coincides      = filter (#coincide) sorted_triple_results: triple_result list;
  val top_nth = try hd sorted_coincides <$> #nth_candidate: int option;

  fun string_some NONE = "Method_None_SOMETHING_WENT_WRONG"
   |  string_some (SOME x) = x;
  val location =
     (Method.position (SOME m) |> Position.file_of |> string_some,
      Method.position (SOME m) |> Position.line_of |> Option.map Int.toString |> string_some);
  val result =
      {location = location,
       top_nth  = top_nth,
       score             = score,
       time              = duration
       }: result;

in result_to_string result end;

\<close>

ML\<open>
local

(*Method.text_range = text * Position.range;*)
fun state_to_unit  (pst:Proof.state) (m) =
  let
    val message = evaluate pst m;
    val _ = tracing message;
    val path = Resources.master_directory @{theory} |> File.platform_path : string;
    val path_to_database  = path ^ "/Database.txt" : string;
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

fun pst_to_unit m = (fn toplevel_state => state_to_unit (Toplevel.proof_of toplevel_state) m): Toplevel.state -> unit;
fun get_name (Method.Source src) = ((Token.name_of_src src)|>fst)

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
