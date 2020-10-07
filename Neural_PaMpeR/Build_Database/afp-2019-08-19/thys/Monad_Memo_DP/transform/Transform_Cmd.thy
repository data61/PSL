subsection \<open>Tool Setup\<close>

theory Transform_Cmd
  imports
    "../Pure_Monad"
    "../state_monad/DP_CRelVS"
    "../heap_monad/DP_CRelVH"
  keywords
    "memoize_fun" :: thy_decl
    and "monadifies" :: thy_decl
    and "memoize_correct" :: thy_goal
    and "with_memory" :: quasi_command
    and "default_proof" :: quasi_command
begin

ML_file \<open>../transform/Transform_Misc.ML\<close>
ML_file \<open>../transform/Transform_Const.ML\<close>
ML_file \<open>../transform/Transform_Data.ML\<close>
ML_file \<open>../transform/Transform_Tactic.ML\<close>
ML_file \<open>../transform/Transform_Term.ML\<close>
ML_file \<open>../transform/Transform.ML\<close>
ML_file \<open>../transform/Transform_Parser.ML\<close>

ML \<open>
val _ =
  Outer_Syntax.local_theory @{command_keyword memoize_fun} "whatever"
    (Transform_Parser.dp_fun_part1_parser >> Transform_DP.dp_fun_part1_cmd)

val _ =
  Outer_Syntax.local_theory @{command_keyword monadifies} "whatever"
    (Transform_Parser.dp_fun_part2_parser >> Transform_DP.dp_fun_part2_cmd)
\<close>

ML \<open>
val _ =
  Outer_Syntax.local_theory_to_proof @{command_keyword memoize_correct} "whatever"
    (Scan.succeed Transform_DP.dp_correct_cmd)
\<close>

method_setup memoize_prover = \<open>
Scan.succeed (fn ctxt => (SIMPLE_METHOD' (
  Transform_Data.get_last_cmd_info ctxt
  |> Transform_Tactic.solve_consistentDP_tac ctxt)))
\<close>

method_setup memoize_prover_init = \<open>
Scan.succeed (fn ctxt => (SIMPLE_METHOD' (
  Transform_Data.get_last_cmd_info ctxt
  |> Transform_Tactic.prepare_consistentDP_tac ctxt)))
\<close>

method_setup memoize_prover_case_init = \<open>
Scan.succeed (fn ctxt => (SIMPLE_METHOD' (
  Transform_Data.get_last_cmd_info ctxt
  |> Transform_Tactic.prepare_case_tac ctxt)))
\<close>

method_setup memoize_prover_match_step = \<open>
Scan.succeed (fn ctxt => (SIMPLE_METHOD' (
  Transform_Data.get_last_cmd_info ctxt
  |> Transform_Tactic.step_tac ctxt)))
\<close>

method_setup memoize_unfold_defs  = \<open>
Scan.option (Scan.lift (Args.parens Args.name) -- Args.term) >> (fn tm_opt => fn ctxt => (SIMPLE_METHOD' (
  Transform_Data.get_or_last_cmd_info ctxt tm_opt
  |> Transform_Tactic.dp_unfold_defs_tac ctxt)))
\<close>

method_setup memoize_combinator_init  = \<open>
Scan.option (Scan.lift (Args.parens Args.name) -- Args.term) >> (fn tm_opt => fn ctxt => (SIMPLE_METHOD' (
  Transform_Data.get_or_last_cmd_info ctxt tm_opt
  |> Transform_Tactic.prepare_combinator_tac ctxt)))
\<close>
end (* theory *)
