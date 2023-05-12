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

(*** Top_Down_Util ***)
ML_file \<open>Top_Down_Util.ML\<close>
ML_file \<open>Top_Down_Util2.ML\<close>
ML_file \<open>Generalise_By_Renaming.ML\<close>
ML_file \<open>Term_Table_for_Abduction.ML\<close>
ML_file \<open>Generalise_Then_Extend.ML\<close>
ML_file \<open>Abstract_Same_Term.ML\<close>
ML_file \<open>Remove_Function.ML\<close>
ML_file \<open>Remove_Outermost_Assumption.ML\<close>
ML_file \<open>Replace_Imp_With_Eq.ML\<close>
ML_file \<open>All_Top_Down_Conjecturing.ML\<close>
ML_file \<open>And_Node.ML\<close>
ML_file \<open>Or_Node.ML\<close>
ML_file \<open>Or2And_Edge.ML\<close>
ML_file \<open>Proof_Graph_Node.ML\<close>
ML_file \<open>Proof_Graph_Node_Util.ML\<close>
ML_file \<open>Proof_Graph.ML\<close>
ML_file \<open>Proof_Graph_Util.ML\<close>
ML_file \<open>Proof_By_Abduction_Util.ML\<close>
ML_file \<open>Proof_By_Abduction.ML\<close>

strategy Extend_Leaf =
  Alts [
    Clarsimp,
    Thens [
      Smart_Induct,
      User< simp_all>
    ]
  ]

strategy finish_goal_after_assuming_subgoals_n_conjectures =
  Thens [
    Repeat (Hammer),
    IsSolved
  ]

strategy Attack_On_Or_Node = 
  Ors [
    Thens [
      Smart_Induct,
      Thens [
        Auto,
        IsSolved
      ]
    ],
    Thens [
      Hammer,
      IsSolved
    ]
  ]

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
            val cncl_as_trm  = Syntax.read_term lthy (stmt_to_stmt_as_string concl) |> Top_Down_Util.standardize_vnames: term;
            val standardized_cncl = Top_Down_Util.standardize_vnames cncl_as_trm;
            val cxtx_wo_verbose_warnings =
                Config.put SMT_Config.verbose false lthy
             |> Config.put Metis_Generate.verbose false
             |> Context_Position.set_visible false: Proof.context;
            val pst = Proof.init cxtx_wo_verbose_warnings: Proof.state;
            val _ = Proof_By_Abduction.top_down_conjecturing pst standardized_cncl;
          in
            lthy
          end)))
     );

in

val _ = theorem \<^command_keyword>\<open>prove\<close> "prove";

end;
\<close>

end