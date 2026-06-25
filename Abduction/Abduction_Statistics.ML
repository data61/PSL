(*
 * Abduction_Statistics.ML
 *
 * Structured statistics for AbductionProver evaluation.
 *)

signature ABDUCTION_STATISTICS =
sig

type loop_entry =
 {depth: int,
  reachable_keys: int,
  worth_expanding: int,
  selected_ornodes: int,
  num_processors: int,
  refutation_cache_size: int,
  refutation_cache_hits: int,
  refutation_cache_misses: int,
  refutation_cache_hit_rate: real,
  elapsed_sec: real};

type statistics;
type synched_statistics = statistics Synchronized.var;

val mk_statistics: unit -> synched_statistics;
val record_loop: Proof.state -> synched_statistics -> loop_entry -> unit;

end;

structure Abduction_Statistics: ABDUCTION_STATISTICS =
struct

type loop_entry =
 {depth: int,
  reachable_keys: int,
  worth_expanding: int,
  selected_ornodes: int,
  num_processors: int,
  refutation_cache_size: int,
  refutation_cache_hits: int,
  refutation_cache_misses: int,
  refutation_cache_hit_rate: real,
  elapsed_sec: real};

type statistics = {loop_entries: loop_entry list};
type synched_statistics = statistics Synchronized.var;

fun mk_statistics () =
  Synchronized.var "Abduction_Statistics.statistics" {loop_entries = []}: synched_statistics;

fun safe_char c =
  if Char.isAlphaNum c orelse c = #"_" then str c else "_";

fun safe_name s = String.translate safe_char s;

fun theory_name_of_pst pst =
  Proof.context_of pst
  |> Local_Theory.exit_global
  |> Context.theory_name {long = true}
  |> safe_name;

fun stats_dir () = getenv "PSL_EVAL_ABDUCTION_STATS_DIR";

fun enabled () = getenv "PSL_EVAL_MODE" = "1" andalso stats_dir () <> "";

fun base_path pst suffix =
  Path.append (Path.explode (stats_dir ()))
    (Path.basic ("abduction_" ^ theory_name_of_pst pst ^ suffix));

fun int_to_csv i = Int.toString i;
fun real_to_csv r = Real.toString r;

fun append_line_with_header path header line =
  if File.exists path
  then File.append path line
  else File.write path (header ^ line);

val loop_header =
  "depth,reachable_keys,worth_expanding,selected_ornodes,num_processors,refutation_cache_size,refutation_cache_hits,refutation_cache_misses,refutation_cache_hit_rate,elapsed_sec\n";

fun loop_entry_to_csv
    ({depth, reachable_keys, worth_expanding, selected_ornodes, num_processors,
      refutation_cache_size, refutation_cache_hits, refutation_cache_misses,
      refutation_cache_hit_rate, elapsed_sec}: loop_entry) =
  String.concatWith ","
    [int_to_csv depth,
     int_to_csv reachable_keys,
     int_to_csv worth_expanding,
     int_to_csv selected_ornodes,
     int_to_csv num_processors,
     int_to_csv refutation_cache_size,
     int_to_csv refutation_cache_hits,
     int_to_csv refutation_cache_misses,
     real_to_csv refutation_cache_hit_rate,
     real_to_csv elapsed_sec] ^ "\n";

fun write_loop_entry pst entry =
  if enabled ()
  then append_line_with_header (base_path pst ".loops.csv") loop_header (loop_entry_to_csv entry)
  else ();

fun record_loop pst synched_statistics entry =
  let
    val _ =
      Synchronized.change synched_statistics
        (fn {loop_entries} => {loop_entries = entry :: loop_entries});
    val _ = write_loop_entry pst entry;
  in
    ()
  end;

end;
