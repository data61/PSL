(*  Title:      TBC/TBC.thy
    Author:     Yutaka Nagashima, Huawei Technologies Research & Development (UK) Limited.
    Author:     Yutaka Nagashima, Institute of Computer Science, the Czech Academy of Sciences

Template-Based Conjecturing (TBC): generates and proves auxiliary lemmas from the
constants occurring in a goal, to help discharge inductive proof obligations.
*)
theory TBC
  imports Main "PSL.PSL"
  keywords "evaluate_tbc" :: thy_goal_stmt
begin

declare[[names_short]]

ML_file \<open>Pretty_Consts.ML\<close>
ML_file \<open>TBC_Utils.ML\<close>
ML_file \<open>Template_Based_Conjecturing.ML\<close>

strategy TBC_Strategy =
POrs [
  Thens [Auto, IsSolved],
  PThenOne [Smart_Induct, Thens [Auto, IsSolved]],
  PThenOne [DInduct, Thens [Auto, IsSolved]],
  Thens [Hammer, IsSolved],
  PThenOne [
    Smart_Induct,
    Ors
      [Thens [
         Repeat (
           POrs [
             Fastforce,
             Hammer,
             Thens [
               Clarsimp,
               IsSolved
             ],
             Thens [
               Subgoal,
               Clarsimp,
               Repeat (
                 Thens [
                   Subgoal,
                   Ors [
                     Thens [Auto, IsSolved],
                     Thens [
                       Smart_Induct,
                       Auto,
                       IsSolved
                     ]
                   ]
                 ]
               ),
               IsSolved
             ]
           ]
         ),
         IsSolved
       ]
    ]
  ]
]

(* Obligations from "instance" and "interpretation"/"sublocale" need a method that opens them
   up before anything else can touch them: OFCLASS(ty, c_class) and a locale predicate are
   opaque to auto, simp and sledgehammer alike. intro_classes and unfold_locales do that, and
   neither appears in the strategies above. Once opened, the resulting subgoals are ordinary
   ones - typically the class axioms or locale assumptions at the instance - so we attack them
   the same way as anything else. Both strategies fall back to attacking the goal directly, so
   a goal misclassified by TBC_Utils.goal_shape costs time rather than the proof. *)
strategy Class_Obligation_Strategy =
  Ors [
    Thens [
      IntroClasses,
      Ors [
        Thens [Auto, IsSolved],
        Thens [User< simp_all>, IsSolved],
        (*Simplifying first can replace the class operations by whatever the
          instantiation defined them to be, leaving a goal about a recursive function, which
          then wants induction rather than more simplification.*)
        Thens [User< simp_all>, Smart_Induct, Auto, IsSolved],
        Thens [User< simp_all>, Smart_Induct, User< simp_all>, IsSolved],
        PThenOne [Smart_Induct, Thens [Auto, IsSolved]],
        Thens [Hammer, IsSolved]
      ]
    ],
    Thens [Auto, IsSolved],
    Thens [Hammer, IsSolved]
  ]

strategy Locale_Obligation_Strategy =
  Ors [
    Thens [
      User< unfold_locales>,
      Ors [
        Thens [Auto, IsSolved],
        Thens [User< simp_all>, IsSolved],
        Thens [Hammer, IsSolved],
        Thens [User< simp_all>, Smart_Induct, Auto, IsSolved],
        PThenOne [Smart_Induct, Thens [Auto, IsSolved]],
        PThenOne [Smart_Induct, Thens [User< simp_all>, IsSolved]]
      ]
    ],
    Thens [Auto, IsSolved],
    Thens [Hammer, IsSolved]
  ]

strategy Quick_Pick = Thens [Quickcheck, Nitpick]

ML\<open> (*This part (the definitions of long_keyword, long_statement, and short_statement) are
from Pure/Pure.thy in Isabelle/HOL's source code.*)

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

structure TBC = Template_Based_Conjecturing;

in

(*Evaluation functions for AbductionProver*)
fun tbc_eval_enabled () =
  getenv "PSL_EVAL_MODE" = "1";

fun clean_markup s =
  XML.content_of (YXML.parse_body s)
  handle ERROR _ => s;

fun tbc_eval_file_name lthy =
  Local_Theory.exit_global lthy
  |> Context.theory_name {long = true}
  |> space_explode "."
  |> String.concatWith "_";

fun write_tbc_eval_proof lthy proof =
  let
    val dir = getenv "PSL_EVAL_PROOF_DIR";
    val file_name = "tbc__" ^ tbc_eval_file_name lthy ^ ".proof";
    val path = Path.append (Path.explode dir) (Path.basic file_name);
  in
    if tbc_eval_enabled () andalso dir <> ""
    then File.write path (clean_markup proof ^ "\n")
    else ()
  end;

fun stmt_to_stmt_as_string_for_tbc_eval (Element.Shows [((_, _), [(stmt, _)])]) = stmt: string
  | stmt_to_stmt_as_string_for_tbc_eval _ =
      error "stmt_to_stmt_as_string_for_tbc_eval failed in evaluate_tbc.";

fun run_full_tbc_for_eval (lthy: local_theory) (concl: (string, string) Element.stmt) =
  let
    val pst = Proof.init lthy;
    val original_goal =
      TBC_Utils.statement_to_conjecture pst concl;

    (* Round 0: first try the original goal directly using TBC_Strategy.
       This corresponds to the zeroth round reported in the TBC paper. *)
    val (_, processed_nodes_after_0th_round) =
      TBC_Utils.conjectures_n_pst_to_pst_n_proof_w_limit
        TBC_Utils.TBC_Strategy 1 0 [original_goal] pst;

    val processed_nodes =
      if TBC_Utils.original_goal_is_proved processed_nodes_after_0th_round
      then processed_nodes_after_0th_round
      else
        let
          (* Same bottom-up conjecture-generation path used by the
             original property-based-conjecturing loop. *)
          val cncl_as_trm =
            Syntax.read_term lthy (stmt_to_stmt_as_string_for_tbc_eval concl);

          val (relevant_consts, relevant_binary_funcs, relevant_unary_funcs) =
            TBC_Utils.get_relevant_constants lthy cncl_as_trm;

          val conjectures_as_tagged_terms =
            map (TBC.ctxt_n_const_to_all_conjecture_term lthy)
                (relevant_unary_funcs @ relevant_binary_funcs)
            |> flat: (TBC.property * term) list;

          val _ =
            tracing ("\nTBC_EVAL: generated "
              ^ Int.toString (length conjectures_as_tagged_terms)
              ^ " template-based conjectures.");

          val conjectures =
            map (TBC.pst_n_property_n_trm_to_pnode pst)
                conjectures_as_tagged_terms: TBC_Utils.pnodes;

          val conjectures_w_counterexample =
            filter (fn pnode => #refuted pnode) conjectures;

          val conjectures_wo_counterexample =
            filter_out (fn pnode => #refuted pnode) conjectures;

          val _ =
            tracing ("TBC_EVAL: "
              ^ Int.toString (length conjectures_w_counterexample)
              ^ " conjectures refuted by Quickcheck/Nitpick.");

          val _ =
            tracing ("TBC_EVAL: "
              ^ Int.toString (length conjectures_wo_counterexample)
              ^ " conjectures survived counterexample filtering.");

          (* Rounds 1 and 2: prove surviving conjectures, register proved ones
             as auxiliary lemmas, and retry the original goal.  This is the
             actual PBC/TBC loop, not merely TBC_Strategy on the original goal. *)
          val (_, processed_pnodes) =
            TBC_Utils.conjectures_n_pst_to_pst_n_proof_w_limit
              TBC_Utils.TBC_Strategy
              3
              1
              (conjectures_wo_counterexample @ [original_goal])
              pst;
        in
          processed_pnodes
        end;
  in
    processed_nodes
  end;

fun evaluate_tbc_command () =
  Outer_Syntax.local_theory @{command_keyword evaluate_tbc}
    "evaluate full template-based conjecturing for benchmarking"
    (((long_statement || short_statement) >>
      (fn (_, _, _, _, concl: (string, string) Element.stmt) =>
        (fn lthy: local_theory =>
          let
            val processed_nodes =
              run_full_tbc_for_eval lthy concl;

            val proof_text =
              TBC_Utils.print_proved_nodes lthy processed_nodes;

            val _ =
              if TBC_Utils.original_goal_is_proved processed_nodes
              then write_tbc_eval_proof lthy proof_text
              else tracing "TBC_EVAL: no proof found.";
          in
            lthy
          end))));

val _ = evaluate_tbc_command ();

end;
\<close>

ML_file \<open>TBC_Preprocessor_Statistics.ML\<close>
ML_file \<open>TBC_Preprocessor.ML\<close>

end