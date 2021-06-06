(*  Title:      PSL/UR/United_Reasoning.thy
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

A part of this file is heavily influenced by Pure/Pure.thy of Isabelle/HOL's source code.
The author of that part is Makarius Wenzel.
*)

theory United_Reasoning
  imports Bottom_Up_Conjecturing Top_Down_Conjecturing
  keywords "prove" :: thy_goal_stmt
begin

ML\<open> signature United_Reasoning =
sig

type round = int;

type proof_script;
type conjecture_typ;
type target_constants;
type record_triple = proof_script * conjecture_typ * target_constants;

val bottom_up_one_iteration: Proof.state -> record_triple * Proof.state;
val bottom_up              : Proof.state -> record_triple * Proof.state;
val top_down               : Proof.state -> record_triple * Proof.state;

end;
\<close>

ML\<open> type conjecture_w_proof = {name: string, proof: string, stmt: string};
\<close>

ML\<open> fun print_conjecture_w_proof ({name: string, proof: string, stmt: string}:conjecture_w_proof) =
  "lemma " ^ name ^ ": " ^ enclose "\"" "\"" stmt ^ "\n" ^ proof: string;
\<close>

ML\<open> fun prove_pst_with_strategy (pst:Proof.state) (strategy:Monadic_Prover.str) = ();

structure MP = Monadic_Prover;

fun psl_strategy_to_monadic_tactic (strategy:MP.str) = fn (proof_state:Proof.state) =>
  let
    val core_tac  = MP.desugar strategy;
    val interpret = MP.interpret;
    fun hard_timeout_in (sec:real) = Timeout.apply (seconds sec);
  in
    hard_timeout_in 60000.0
    (interpret (MP.eval_prim, MP.eval_para, MP.eval_pgt, MP.eval_strategic, MP.m_equal, MP.iddfc, (5,20))
                core_tac) proof_state
  end: Proof.state MP.monad;
\<close>

ML\<open> fun fst_conjecture_n_lthy_to_some_pst_n_proof  (lthy:local_theory) =(*TODO: Double-check. Probably there is a better way to handle this.*)
  let
    val binding    = (Binding.name ("fake_lemma_to_move_to_proof_state"), [])              : Attrib.binding;
    val stmt_elem  = Element.Shows [(binding, [("True", [])])]: (string, string) Element.stmt;
    val pst =
       let
         val pst_to_be_proved = Specification.theorem_cmd true Thm.theoremK NONE (K I) binding [] [] stmt_elem false lthy;
         val stttac_on_pst    = Subtools.sh_output_to_sh_stttac "by auto"
         val resulting_pst    = stttac_on_pst pst_to_be_proved [] |> Seq.hd |> snd: Proof.state;
       in
         resulting_pst
       end;
  in
    pst:Proof.state
  end;
\<close>

ML\<open> fun string_to_stttac (str:string) =
if   str = "done"
then Subtools.is_solved
else Subtools.sh_output_to_sh_stttac str;
\<close>

ML\<open> fun pst_n_conjecture_has_counterexample (pst:Proof.state) (conjecture:{lemma_name:string, lemma_stmt:string}) =
let
    val pst_to_be_proved    = Proof.theorem_cmd NONE (K I) [[(#lemma_stmt conjecture, [])]] (Proof.context_of pst)
    val quickcheck          = PSL_Interface.lookup (Proof.context_of pst) "Quickcheck" |> the: PSL_Interface.strategy;
    val result_seq          = psl_strategy_to_monadic_tactic quickcheck pst_to_be_proved []   : (Dynamic_Utils.log * Proof.state) Seq.seq;
in
  is_none (Seq.pull result_seq)
end;
\<close>

ML\<open> fun pst_n_conjectures_to_conjectures_wo_obvious_counterexample (pst:Proof.state) (conjectures:{lemma_name:string, lemma_stmt:string} list) =
  filter_out (pst_n_conjecture_has_counterexample pst) conjectures: {lemma_name:string, lemma_stmt:string} list;
\<close>

ML\<open> fun pst_to_proofscript_opt(pst:Proof.state) =
  let
    val ur_strategy         = PSL_Interface.lookup (Proof.context_of pst) "ur_strategy" |> the: PSL_Interface.strategy;
    val result_seq          = psl_strategy_to_monadic_tactic ur_strategy pst []               : (Dynamic_Utils.log * Proof.state) Seq.seq;
    val result_opt          = try Seq.hd result_seq <$> fst                                   : (Dynamic_Utils.log) option;
    fun mk_proof_script log = Dynamic_Utils.mk_apply_script log;
  in
    Option.map mk_proof_script result_opt: string option
  end;
\<close>

ML\<open> fun conjecture_n_pst_to_pst_n_proof (conjecture:{lemma_name:string, lemma_stmt:string}) (pst:Proof.state) =
  let
    val _ = tracing ("trying to prove " ^ #lemma_name conjecture)
    val binding          = (Binding.name (#lemma_name conjecture), [])                                         : Attrib.binding;
    val pst_to_be_proved = Proof.theorem_cmd NONE (K I) [[(#lemma_stmt conjecture, [])]] (Proof.context_of pst): Proof.state;
    val script_opt       = pst_to_proofscript_opt pst_to_be_proved                                             : string option;
    val pst_n_log  = case script_opt of
       NONE                 => (pst, NONE)
     | SOME (script:string) => (
       let
         val _ =  #lemma_stmt conjecture |> tracing;
         val _ = tracing script;
         val stmt_elem        = Element.Shows [(binding, [(#lemma_stmt conjecture, [])])]: (string, string) Element.stmt;
         val pst_to_be_proved = Specification.theorem_cmd true Thm.theoremK NONE (K I) binding [] [] stmt_elem false (Proof.context_of pst);
         val proof_scripts    = Utils.init (space_explode "\n" (YXML.content_of script)) |> Utils.init: strings;
         val stttacs_on_pst   = map string_to_stttac proof_scripts: Proof.state Dynamic_Utils.stttac list;
         (*TODO: Monad fix?*)
         (*TODO: register proved conjectures with Local_Theory.note.
                 zip stttacs with lemma names.*)
         fun apply_stttacs_to_pst (pst:Proof.state) []                = (fn _ => Seq.single ([], pst)): Proof.state Monadic_Interpreter_Core.monad
           | apply_stttacs_to_pst (pst:Proof.state) [stttac]          = stttac pst                    : Proof.state Monadic_Interpreter_Core.monad
           | apply_stttacs_to_pst (pst:Proof.state) (stttac::stttacs) = Monadic_Interpreter_Core.bind (stttac pst) (fn new_pst => apply_stttacs_to_pst new_pst stttacs)
         val resulting_pst = apply_stttacs_to_pst pst_to_be_proved stttacs_on_pst [] |> Seq.hd |> snd: Proof.state;
         val binding = (Binding.name (#lemma_name conjecture), []);
         val {context: Proof.context, goal: thm} = Proof.simple_goal resulting_pst: {context: Proof.context, goal: thm};
         val _ = Proof.theorem NONE (fn thms => fn lthy => Local_Theory.note (binding, flat thms) lthy |> snd) []
               : Proof.context -> Proof.state;
         val goal_term = Syntax.read_prop context (#lemma_stmt conjecture): term;
         val vnames = Variable.add_free_names context goal_term [];
         (*TODO: don't use Skip_Proof.cheat_tac to stay on the safer side.*)
         val some_thm = (SOME (Goal.prove context vnames [] goal_term (fn {context, prems} => (Skip_Proof.cheat_tac context 1))))
                        handle ERROR err => (warning (#lemma_name conjecture); warning err; NONE);
         fun get_ctxt_w_new_lemma _ _ = Local_Theory.note (binding, [the some_thm]) context |> snd: local_theory;
         val pst_to_return = Proof.theorem NONE (get_ctxt_w_new_lemma) [[(goal_term, [])]] context
       in
         (pst_to_return, SOME {name = #lemma_name conjecture, stmt = #lemma_stmt conjecture, proof = script})
       end);
  in
    pst_n_log: Proof.state * {name: string, proof: string, stmt: string} option
  end;
\<close>

ML\<open> fun conjectures_n_pst_to_pst_n_proof' [] pst acc = ((pst, []), acc)
  | conjectures_n_pst_to_pst_n_proof' (conjecture::conjectures) pst acc =
    let
      val (new_pst, conjecture_w_prf: conjecture_w_proof option) = conjecture_n_pst_to_pst_n_proof conjecture pst;
    in
      conjectures_n_pst_to_pst_n_proof' conjectures new_pst (acc @ the_list conjecture_w_prf)
     : (Proof.state * conjecture_w_proof list) * conjecture_w_proof list
    end;

(*Fix these overloaded function names*)
fun conjecture_n_pst_to_pst_n_proof conjectures pst = conjectures_n_pst_to_pst_n_proof' conjectures pst [];
\<close>

strategy ur_strategy =
Ors [
  Thens [Auto, IsSolved],                                       
  PThenOne [
    Smart_Induct,
    Ors
      [Thens [Auto, IsSolved],
       Thens [
         Repeat (Ors [Fastforce, Hammer]),
         IsSolved
       ]
    ]
  ]
]

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

local

fun termsA_n_termB_to_AB_pairs' ([]:terms)         (unary:term) acc = acc
  | termsA_n_termB_to_AB_pairs' (binary::binaries) (unary:term) acc =
    termsA_n_termB_to_AB_pairs' binaries unary ((binary, unary)::acc);

fun termsA_n_termB_to_AB_pairs (binaries:terms) (unary:term) =
    termsA_n_termB_to_AB_pairs' binaries unary [];

in

fun termsA_n_termsB_to_AB_pairs (binaries:terms) (unaries:terms) =
    map (termsA_n_termB_to_AB_pairs binaries) unaries |> flat: (term * term) list;

end;

fun theorem spec descr =
  Outer_Syntax.local_theory @{command_keyword prove} ("state " ^ descr)
    (((long_statement || short_statement) >> (fn (_, _, _, _, concl) =>
       (fn lthy =>
          let
            fun stmt_to_stmt_as_string (Element.Shows [((_, _), [(stmt, _)])]) = stmt: string
              | stmt_to_stmt_as_string _ = error "stmt_to_concl_name failed in United_Reasoning";

            val cncl_as_trm    = Syntax.read_term lthy (stmt_to_stmt_as_string concl);
            val consts_in_cncl = Syntax.read_term lthy (stmt_to_stmt_as_string concl)
                 |> (fn trm:term => Term.add_consts trm []) |> map Const;
            val cnames_in_cncl = Term.add_const_names cncl_as_trm []: strings;
            val defining_terms = (flat o map (SeLFiE_Util.ctxt_n_cname_to_definitions lthy)) cnames_in_cncl: terms;
            val relevant_consts_in_definitinos = map (fn trm => Term.add_consts trm []) defining_terms |> flat |> map Const: terms;
            val relevant_consts = (consts_in_cncl @ relevant_consts_in_definitinos) |> distinct (op =): terms;
            val relevant_binary_funcs = filter (takes_n_arguments 2) relevant_consts: terms;
            val relevant_unary_funcs  = filter (takes_n_arguments 1) relevant_consts: terms;
            (*TODO: get constants from types*)

            val pairs_for_distributivity = termsA_n_termsB_to_AB_pairs relevant_binary_funcs relevant_binary_funcs;
            val pairs_for_anti_distr_n_homomorphism_2 = termsA_n_termsB_to_AB_pairs relevant_unary_funcs relevant_binary_funcs;
            val _= tracing ("We have " ^ Int.toString (length relevant_unary_funcs) ^ " relevant_unary_funcs");
            val _= tracing ("We have " ^ Int.toString (length relevant_binary_funcs) ^ " relevant_binary_funcs");
            val _= tracing ("We have " ^ Int.toString (length pairs_for_distributivity) ^ " pairs_for_distributivity");
            val _= tracing ("We have " ^ Int.toString (length pairs_for_anti_distr_n_homomorphism_2) ^ " pairs_for_anti_distr_n_homomorphism_2");
            val associativities                = map (ctxt_n_trm_to_associativity lthy) relevant_binary_funcs                        |> flat;
            val commutativities                = map (ctxt_n_trm_to_commutativity lthy) relevant_binary_funcs                        |> flat;
            val distributivities               = map (ctxt_n_trms_to_distributivity lthy) pairs_for_distributivity                   |> flat;
            val anti_distributivities          = map (ctxt_n_trms_to_anti_distributivity lthy) pairs_for_anti_distr_n_homomorphism_2 |> flat;
            val homomorphism_2                 = map (ctxt_n_trms_to_homomorphism_2 lthy) pairs_for_anti_distr_n_homomorphism_2      |> flat;
            val conjectures                    = associativities @ commutativities @ distributivities @  anti_distributivities @ homomorphism_2;
            val pst                            = fst_conjecture_n_lthy_to_some_pst_n_proof lthy: Proof.state;
            val _= tracing ("We have " ^ Int.toString (length conjectures) ^ " conjectures");
            val conjectures_wo_counter_example = pst_n_conjectures_to_conjectures_wo_obvious_counterexample pst conjectures;
            val _= tracing ("We have " ^ Int.toString (length conjectures_wo_counter_example) ^ " conjectures_wo_counter_example:");
            val _ = map (tracing o (fn conj => " " ^ #lemma_name conj)) conjectures_wo_counter_example;
            fun statement_to_conjecture (Element.Shows [((binding, _), [(stmt:string, [])])]) =
                {lemma_name = Binding.name_of binding: string,
                 lemma_stmt = stmt |> YXML.content_of |> String.explode |> Utils.init |> tl |> String.implode}
              | statement_to_conjecture _ = error "statement_to_conjecture failed.";

            val ((_, _), prfs2) = conjecture_n_pst_to_pst_n_proof (conjectures_wo_counter_example @ [statement_to_conjecture concl]) pst
              : (Proof.state * conjecture_w_proof list) * conjecture_w_proof list;
            val _ = map (tracing o print_conjecture_w_proof) prfs2;
            fun stmt_to_concl_name (Element.Shows [((binding, _), [(_, _)])]) =  Binding.name_of binding: string
              | stmt_to_concl_name _ = error "stmt_to_concl_name failed in United_Reasoning";
            fun cocl_is_proved (pst:Proof.state) =
                try (Proof_Context.get_thms (Proof.context_of pst)) (stmt_to_concl_name concl) |> is_some: bool;
          in
            lthy
          end)))
     );

in

val _ = theorem \<^command_keyword>\<open>prove\<close> "theorem";

end;
\<close>

datatype Nat = Z | S "Nat"

fun t2 :: "Nat => Nat => Nat" where
"t2 (Z) y = y"
| "t2 (S z) y = S (t2 z y)"
(*
lemma t2_succ: "S (t2 n m) = t2 n (S m)"
  by(induct n, auto)

theorem property0 :
  "((t2 x1 (S x1)) = (S (t2 x1 x1)))"
  apply(induction x1, auto)
  apply(simp add:t2_succ)
  done
*)

(*
prove dfd:"((t2 x1 (S x1)) = (S (t2 x1 x1)))"
*)
end