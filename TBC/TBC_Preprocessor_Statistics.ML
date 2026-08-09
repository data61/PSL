(*  Title:      TBC/TBC_Preprocessor_Statistics.ML
    Author:     Yutaka Nagashima, Huawei Technologies Research & Development (UK) Limited.

Records per-goal statistics about the TBC preprocessing phase run by the "prove"
command (round counts, conjecture counts, timings), writing them as CSV under
PSL_EVAL_TBC_PREPROCESS_STATS_DIR when PSL_EVAL_MODE=1.
*)
signature TBC_PREPROCESSOR_STATISTICS =
sig

type preprocessing_entry =
 {rounds_requested: int,
  direct_goal_attempted: bool,
  direct_goal_proved: bool,
  direct_goal_elapsed_sec: real,
  generated_conjectures: int,
  refuted_by_counterexample: int,
  surviving_conjectures: int,
  parallel_rounds_run: int,
  parallel_candidate_nodes: int,
  proved_template_lemmas: int,
  original_goal_proved_by_tbc: bool,
  original_goal_proved_in_round: int option,
  tbc_preprocessing_elapsed_sec: real};

type statistics;
type synched_statistics = statistics Synchronized.var;

val mk_statistics: unit -> synched_statistics;
val set_preprocessing_entry: synched_statistics -> preprocessing_entry -> unit;
val write_final:
  Proof.state -> synched_statistics ->
   {abduction_invoked: bool,
    abduction_solved: bool,
    abduction_elapsed_sec: real,
    total_elapsed_sec: real} -> unit;

end;

structure TBC_Preprocessor_Statistics: TBC_PREPROCESSOR_STATISTICS =
struct

type preprocessing_entry =
 {rounds_requested: int,
  direct_goal_attempted: bool,
  direct_goal_proved: bool,
  direct_goal_elapsed_sec: real,
  generated_conjectures: int,
  refuted_by_counterexample: int,
  surviving_conjectures: int,
  parallel_rounds_run: int,
  parallel_candidate_nodes: int,
  proved_template_lemmas: int,
  original_goal_proved_by_tbc: bool,
  original_goal_proved_in_round: int option,
  tbc_preprocessing_elapsed_sec: real};

type statistics = preprocessing_entry option;
type synched_statistics = statistics Synchronized.var;

fun mk_statistics () =
  Synchronized.var "TBC_Preprocessor_Statistics.statistics" NONE: synched_statistics;

fun set_preprocessing_entry synched_statistics entry =
  Synchronized.change synched_statistics (fn _ => SOME entry);

fun safe_char c =
  if Char.isAlphaNum c orelse c = #"_" then str c else "_";

fun safe_name s = String.translate safe_char s;

fun theory_name_of_pst pst =
  Proof.context_of pst
  |> Local_Theory.exit_global
  |> Context.theory_name {long = true}
  |> safe_name;

fun stats_dir () = getenv "PSL_EVAL_TBC_PREPROCESS_STATS_DIR";

fun enabled () = getenv "PSL_EVAL_MODE" = "1" andalso stats_dir () <> "";

fun base_path pst =
  Path.append (Path.explode (stats_dir ()))
    (Path.basic ("tbc_seed_" ^ theory_name_of_pst pst ^ ".csv"));

fun int_to_csv i = Int.toString i;
fun real_to_csv r = Real.toString r;
fun bool_to_csv b = if b then "true" else "false";
fun int_opt_to_csv NONE = ""
  | int_opt_to_csv (SOME i) = Int.toString i;

fun append_line_with_header path header line =
  if File.exists path
  then File.append path line
  else File.write path (header ^ line);

val header =
  "rounds_requested,direct_goal_attempted,direct_goal_proved,direct_goal_elapsed_sec,\
  \generated_conjectures,refuted_by_counterexample,surviving_conjectures,\
  \parallel_rounds_run,parallel_candidate_nodes,proved_template_lemmas,\
  \original_goal_proved_by_tbc,original_goal_proved_in_round,tbc_preprocessing_elapsed_sec,\
  \abduction_invoked,abduction_solved,abduction_elapsed_sec,total_elapsed_sec\n";

fun entry_to_csv
    ({rounds_requested, direct_goal_attempted, direct_goal_proved, direct_goal_elapsed_sec,
      generated_conjectures, refuted_by_counterexample, surviving_conjectures,
      parallel_rounds_run, parallel_candidate_nodes, proved_template_lemmas,
      original_goal_proved_by_tbc, original_goal_proved_in_round,
      tbc_preprocessing_elapsed_sec}: preprocessing_entry)
    ({abduction_invoked, abduction_solved, abduction_elapsed_sec, total_elapsed_sec}) =
  String.concatWith ","
    [int_to_csv rounds_requested,
     bool_to_csv direct_goal_attempted,
     bool_to_csv direct_goal_proved,
     real_to_csv direct_goal_elapsed_sec,
     int_to_csv generated_conjectures,
     int_to_csv refuted_by_counterexample,
     int_to_csv surviving_conjectures,
     int_to_csv parallel_rounds_run,
     int_to_csv parallel_candidate_nodes,
     int_to_csv proved_template_lemmas,
     bool_to_csv original_goal_proved_by_tbc,
     int_opt_to_csv original_goal_proved_in_round,
     real_to_csv tbc_preprocessing_elapsed_sec,
     bool_to_csv abduction_invoked,
     bool_to_csv abduction_solved,
     real_to_csv abduction_elapsed_sec,
     real_to_csv total_elapsed_sec] ^ "\n";

fun default_entry () =
 {rounds_requested = 0,
  direct_goal_attempted = false,
  direct_goal_proved = false,
  direct_goal_elapsed_sec = 0.0,
  generated_conjectures = 0,
  refuted_by_counterexample = 0,
  surviving_conjectures = 0,
  parallel_rounds_run = 0,
  parallel_candidate_nodes = 0,
  proved_template_lemmas = 0,
  original_goal_proved_by_tbc = false,
  original_goal_proved_in_round = NONE,
  tbc_preprocessing_elapsed_sec = 0.0}: preprocessing_entry;

fun write_final pst synched_statistics final =
  if enabled ()
  then
    let
      val entry = the_default (default_entry ()) (Synchronized.value synched_statistics);
      val line = entry_to_csv entry final;
    in
      append_line_with_header (base_path pst) header line
    end
  else ();

end;
