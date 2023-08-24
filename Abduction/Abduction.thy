(*
 * Abduction.thy
 * Authors:
 *   Yutaka Nagashima, Daniel Goc Sebastian
 *   Huawei Technologies Research & Development (UK) Limited.
 *)
theory Abduction
  imports "../TBC/TBC"
  keywords "prove" :: thy_goal_stmt
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
ML_file \<open>Seed_Of_Or2And_Edge.ML\<close>
ML_file \<open>Proof_By_Abduction.ML\<close>

strategy Extend_Leaf =
  Alts [
    Clarsimp,
    Thens [
      Smart_Induct,
      User< simp_all>
    ]
  ]

strategy Finish_Goal_After_Assuming_Subgoals_And_Conjectures =
  Thens [
    Repeat (Hammer),
    IsSolved
  ]

strategy Attack_On_Or_Node = 
  Ors [
    Thens [
      Auto,
      IsSolved
    ],
    Thens [
      Smart_Induct,
      Thens [
        User< simp_all>,
        IsSolved
      ]
    ],
    Thens [
      Hammer,
      IsSolved
    ]
  ]

setup\<open> Config.put_global Top_Down_Util.timeout_config (60.0 * 60.0 * 10.0) \<close>
setup\<open> Config.put_global Top_Down_Util.limit_for_first_decrement 30 \<close>
setup\<open> Config.put_global Top_Down_Util.limit_for_other_decrement 10 \<close>

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
    >> (fn ((binding, includes), (elems, concl)) => (true, binding, includes, elems, concl))
: Token.T list ->
  (bool * Attrib.binding * (xstring * Position.T) list *
   Element.context list * Element.statement)
  *
  Token.T list;

val short_statement =
  Parse_Spec.statement -- Parse_Spec.if_statement -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) =>
      (false, Binding.empty_atts, [], [Element.Fixes fixes, Element.Assumes assumes],
        Element.Shows shows));

fun theorem _ descr =
  Outer_Syntax.local_theory @{command_keyword prove} ("state " ^ descr)
    (((long_statement || short_statement) >> (fn (_, _, _, _(*elems*), concl) =>
       (fn lthy =>
          let
            fun stmt_to_stmt_as_string (Element.Shows [((_, _), [(stmt, _)])]) = stmt: string
              | stmt_to_stmt_as_string _ = error "stmt_to_concl_name failed in United_Reasoning";
            val start = (fn _ => Timing.start ()) lthy: Timing.start;
            val cncl_as_trm  = Syntax.read_term lthy (stmt_to_stmt_as_string concl) |> Top_Down_Util.standardize_vnames: term;
            val standardized_cncl = Top_Down_Util.standardize_vnames cncl_as_trm;
            val cxtx_wo_verbose_warnings =
                Config.put SMT_Config.verbose false lthy
             |> Config.put Metis_Generate.verbose false
             |> Context_Position.set_visible false: Proof.context;
            val pst = Proof.init cxtx_wo_verbose_warnings: Proof.state;
            val proof_by_abduction = Proof_By_Abduction.proof_by_abduction pst start: term -> bool;
            val solved = proof_by_abduction standardized_cncl;
            val elapsed = #elapsed (Timing.result start): Time.time;
            val elapsed_str = Time.toReal elapsed |> Real.toString: string;
            val message = "We spent " ^ elapsed_str ^ " seconds. " ^ (if solved then "And we proved the goal." else "We failed, but tried.");
            val _ = tracing message: unit;
          in
            lthy
          end)
       )
      )
     );

in

val _ = theorem \<^command_keyword>\<open>prove\<close> "prove";

end;
\<close>

ML\<open>
structure df = Syntax
type tsdf = thm
val thm = Top_Down_Util.term_to_thm @{context} (Syntax.read_term @{context} "x = x");
\<close>
find_theorems name: "List"
ML\<open>
structure TDU  = Top_Down_Util;
structure SS   = Shared_State;
structure SOOE = Seed_Of_Or2And_Edge;

val timeout = Isabelle_Utils.timeout_apply (Time.fromSeconds 1);

val d = Basic_Simplifier.asm_full_simplify @{context} thm;
val s = simp_non_prop_term @{context} @{term "True = True"};

fun simp_explicit_conjecture (synched_term2string:SS.synched_term2string_table) (ctxt:Proof.context)
  (simp as (_:string, simp_term:term)) (cnjctr as (_:string, cnjctr_term:term)): SOOE.conjectures =
  let
    val simp_thm = TDU.term_to_thm ctxt simp_term: thm;
    val ctxt_w_simp = Simplifier.add_simp simp_thm ctxt: Proof.context;
    val simplifier = Basic_Simplifier.asm_full_simplify ctxt_w_simp: thm -> thm;
    val simplifier_w_timeout = try (Isabelle_Utils.timeout_apply (Time.fromSeconds 1) simplifier): thm -> thm option;
    val cnjctr_thm = TDU.term_to_thm ctxt simp_term: thm;
    val simp_result = simplifier_w_timeout cnjctr_thm: thm option;
  in
    if   is_none simp_result
    then [cnjctr]
    else
      let
        val simp_result_term = the simp_result |> Thm.full_prop_of: term;
        val simp_result_name = SS.get_lemma_name synched_term2string ctxt simp_result_term: string;
      in
        if simp_result_term = cnjctr_term
        then [simp, (simp_result_name, simp_result_term)]
        else [cnjctr]
      end
  end;

fun simp_explicit_conjectures (synched_term2string:SS.synched_term2string_table) (ctxt:Proof.context)
  (cnjctrs:SOOE.conjectures) (simp:SOOE.conjecture): SOOE.conjectures =
  map (simp_explicit_conjecture synched_term2string ctxt simp) cnjctrs |> flat;




val sdf = Thm.prop_of @{thm List.distinct_adj_Nil};
\<close>
ML\<open>
val saf = @{thm List.distinct_adj_ConsD} |> Thm.full_prop_of |> Isabelle_Utils.trm_to_string @{context} |> tracing;
\<close>
thm List.distinct_adj_Nil

lemma "False \<Longrightarrow> True"
  apply(tactic \<open>fn thm => (
    thm |> Thm.full_prop_of |> Isabelle_Utils.trm_to_string @{context} |> tracing;
    thm |> Thm.prop_of |> Isabelle_Utils.trm_to_string @{context} |> tracing;
    thm |> Thm.concl_of |> Isabelle_Utils.trm_to_string @{context} |> tracing;

    Seq.single thm)\<close>)
  oops

end