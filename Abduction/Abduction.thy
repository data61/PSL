(*
 * Abduction.thy
 * Authors:
 *   Yutaka Nagashima, Daniel Goc Sebastian
 *   Huawei Technologies Research & Development (UK) Limited.
 *)
theory Abduction
  imports "TBC.TBC"
  keywords "prove" :: thy_goal_stmt
  and "prove_by_preprocessed_abduction" :: thy_goal_stmt
begin

ML_file \<open>Top_Down_Util.ML\<close>
ML_file \<open>And_Node.ML\<close>
ML_file \<open>Or_Node.ML\<close>
ML_file \<open>Or2And_Edge.ML\<close>
ML_file \<open>Abduction_Node.ML\<close>
ML_file \<open>Update_Abduction_Node.ML\<close>
ML_file \<open>Abduction_Graph.ML\<close>
ML_file \<open>Update_Abduction_Graph.ML\<close>
ML_file \<open>Shared_State.ML\<close>
ML_file \<open>Generalise_By_Renaming.ML\<close>
ML_file \<open>Term_Table_for_Abduction.ML\<close>
ML_file \<open>Generalise_Then_Extend.ML\<close>
ML_file \<open>Abstract_Same_Term.ML\<close>
ML_file \<open>Remove_Function.ML\<close>
ML_file \<open>Remove_Outermost_Assumption.ML\<close>
ML_file \<open>Replace_Imp_With_Eq.ML\<close>
ML_file \<open>SeLFiE_For_Top_Down.ML\<close>
ML_file \<open>All_Top_Down_Conjecturing.ML\<close>
ML_file \<open>Abduction_Statistics.ML\<close>
ML_file \<open>Seed_Of_Or2And_Edge.ML\<close>
ML_file \<open>Proof_By_Abduction.ML\<close>

strategy Extend_Leaf =
  Alts [
    Clarsimp,
    Thens [
      Cut 10 (Smart_Induct),
      Alts [
        User< simp_all>(*TODO: this simplification is sometimes harmful.*),
        Auto
      ]
    ]
  ]

strategy Finish_Goal_After_Assuming_Subgoals_And_Conjectures =
  Thens [
    Repeat (Hammer),
    IsSolved
  ]

strategy Attack_On_Or_Node = 
  POrs [
    Thens [
      Auto,
      IsSolved
    ],
    PThenOne [
      Alts [
        DInduct,
        Smart_Induct
      ],
      Ors [
        Thens [
          User< simp_all>,
          IsSolved
        ],
        Thens [
          Auto,
          IsSolved
        ]
      ]
    ],
    Thens [
      Hammer,
      IsSolved
    ]
  ]

setup\<open> Config.put_global Top_Down_Util.timeout_config (60.0 * 60.0 * 10.0) \<close>
setup\<open> Config.put_global Top_Down_Util.limit_for_first_decrement 40 \<close>
setup\<open> Config.put_global Top_Down_Util.limit_for_other_decrement 40 \<close>

(* UI *)
ML\<open> (*This part (the definitions of long_keyword, long_statement, and short_statement) are from
by Pure/Pure.thy in Isabelle/HOL's source code.*)

local

val long_keyword =
  Parse_Spec.includes >> K "" ||
  Parse_Spec.long_statement_keyword;

val long_statement =
  Scan.optional (Parse_Spec.opt_thm_name ":" --| Scan.ahead long_keyword) Binding.empty_atts --
  Scan.optional Parse_Spec.includes [] -- Parse_Spec.long_statement
    >> (fn ((binding, includes), (elems, concl)) => (true, binding, includes, elems, concl));

val short_statement =
  Parse_Spec.statement -- Parse_Spec.if_statement -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) =>
      (false, Binding.empty_atts, [], [Element.Fixes fixes, Element.Assumes assumes],
        Element.Shows shows));

fun getenv_int name default =
  case Int.fromString (getenv name) of
      SOME n => n
    | NONE => default;

fun theorem command_keyword descr use_tbc_preprocessing =
  Outer_Syntax.local_theory command_keyword ("state " ^ descr)
    (((long_statement || short_statement) >> (fn (_, _, _, elems, concl) =>
       (fn lthy =>
          let
            fun is_not_fix (Element.Fixes _) = false
              | is_not_fix _                 = true
            fun is_supported (elements:Element.context list) = exists is_not_fix elements;
            val _ = if is_supported elems then () else error
                     ("Currently, the \"prover\" keyword does not support the use of following keywords: \n" ^
                      "\"constraints\", \"assumes\", \"defines\", \"notes\", and  \"lazy_notes\".\n" ^
                      "Please present your proof goal as one single term.")
            fun stmt_to_stmt_as_string (Element.Shows [((_, _), [(stmt, strs:strings)])]) = stmt: string
              | stmt_to_stmt_as_string _ = error "stmt_to_concl_name failed in United_Reasoning";
            val start = (fn _ => Timing.start ()) lthy: Timing.start;
            val cncl_as_trm  = Syntax.read_term lthy (stmt_to_stmt_as_string concl)
                            |> Top_Down_Util.standardize_vnames: term;
            val _ = if Term.size_of_term cncl_as_trm < 100 then ()
                    else error "Your problem size seems too large for Abduction Prover.\n Can you rephrase it?";
            val standardized_cncl = Top_Down_Util.standardize_vnames cncl_as_trm;
            val cxtx_wo_verbose_warnings =
                Config.put SMT_Config.verbose false lthy
             |> Config.put Metis_Generate.verbose false
             |> Context_Position.set_visible false: Proof.context;
            val pst0 = Proof.init cxtx_wo_verbose_warnings: Proof.state;
            val tbc_seed_statistics = TBC_Preprocessor_Statistics.mk_statistics ();
            val (pst, preprocessed_nodes) =
              if use_tbc_preprocessing
              then
                let
                  val rounds = getenv_int "PSL_EVAL_TBC_PREPROCESS_ROUNDS" 2;
                  val _ = tracing ("TBC_PREPROCESSOR: running " ^ Int.toString rounds ^ " preprocessing round(s) before AbductionProver.");
                in
                  TBC_Preprocessor.preprocess_term_with_statistics
                    tbc_seed_statistics rounds pst0 standardized_cncl
                end
              else (pst0, []: TBC_Utils.pnodes);
            val prelude_proofs = TBC_Utils.proved_nodes_to_proof_text preprocessed_nodes;
            val tbc_preprocessing_solved_goal =
              use_tbc_preprocessing andalso TBC_Utils.original_goal_is_proved preprocessed_nodes;
            val abduction_invoked = not tbc_preprocessing_solved_goal;
            val (solved, abduction_elapsed_sec) =
              if tbc_preprocessing_solved_goal
              then (Proof_By_Abduction.write_proof_script_in_result_file pst prelude_proofs; (true, 0.0))
              else
                let
                  val abduction_start = Timing.start ();
                  val solved_by_abduction =
                    Proof_By_Abduction.proof_by_abduction_with_prelude
                      prelude_proofs pst abduction_start standardized_cncl;
                  val elapsed_by_abduction = #elapsed (Timing.result abduction_start) |> Time.toReal;
                in
                  (solved_by_abduction, elapsed_by_abduction)
                end;
            val elapsed = #elapsed (Timing.result start): Time.time;
            val elapsed_str = Time.toReal elapsed |> Real.toString: string;
            val _ =
              if use_tbc_preprocessing
              then
                TBC_Preprocessor_Statistics.write_final pst tbc_seed_statistics
                 {abduction_invoked = abduction_invoked,
                  abduction_solved = solved andalso abduction_invoked,
                  abduction_elapsed_sec = abduction_elapsed_sec,
                  total_elapsed_sec = Time.toReal elapsed}
              else ();
            val message = "We spent " ^ elapsed_str ^ " seconds. " ^ (if solved then "And we proved the goal." else "We failed, but tried.");
            val _ = tracing message: unit;
          in
            lthy
          end)
       )
      )
     );

in

val _ = theorem \<^command_keyword>\<open>prove\<close> "prove" false;
val _ = theorem \<^command_keyword>\<open>prove_by_preprocessed_abduction\<close> "prove by preprocessed abduction" true;

end;
\<close>

end