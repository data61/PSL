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

fun pst_to_proofscript_opt(pst:Proof.state) =
  let
    val ur_strategy  = PSL_Interface.lookup (Proof.context_of pst) "ur_strategy" |> the: PSL_Interface.strategy;
    val result_seq   = psl_strategy_to_monadic_tactic ur_strategy pst []               : (Dynamic_Utils.log * Proof.state) Seq.seq;
    val result_opt   = try Seq.hd result_seq <$> fst                                   : (Dynamic_Utils.log) option;
    fun mk_proof_script log = Dynamic_Utils.mk_apply_script log;
  in
    Option.map mk_proof_script result_opt: string option
  end;
\<close>

ML\<open> fun fst_conjecture_n_lthy_to_some_pst_n_proof  (lthy:local_theory) =
  let
    val binding    = (Binding.name ("fake_lemma_to_move_to_proof_state"), [])              : Attrib.binding;
    val stmt_elem  = Element.Shows [(binding, [("True", [])])]: (string, string) Element.stmt;
    val script     = ("by auto"): string;
    val pst_n_log  =
       let
         val pst_to_be_proved = Specification.theorem_cmd true Thm.theoremK NONE (K I) binding [] [] stmt_elem false lthy;
         val stttacs_on_pst   = map Subtools.sh_output_to_sh_stttac ["by auto"] 
         (*TODO: Monad fix?*)
         fun apply_stttacs_to_pst (pst:Proof.state) []                = (fn _ => Seq.single ([], pst)): Proof.state Monadic_Interpreter_Core.monad
           | apply_stttacs_to_pst (pst:Proof.state) [stttac]          = stttac pst                    : Proof.state Monadic_Interpreter_Core.monad
           | apply_stttacs_to_pst (pst:Proof.state) (stttac::stttacs) = Monadic_Interpreter_Core.bind (stttac pst) (fn new_pst => apply_stttacs_to_pst new_pst stttacs)
         val resulting_pst = apply_stttacs_to_pst pst_to_be_proved stttacs_on_pst [] |> Seq.hd |> snd: Proof.state;
       in
         (resulting_pst, {name = "fake_lemma_to_move_to_proof_state", stmt = "True", proof = script})
       end;
  in
    pst_n_log: (Proof.state * {name: string, proof: string, stmt: string})
  end;
\<close>

ML\<open> fun conjecture_n_pst_to_pst_n_proof (conjecture:{lemma_name:string, lemma_stmt:string}) (pst:Proof.state) =
  let
    val binding          = (Binding.name (#lemma_name conjecture), [])              : Attrib.binding;
    val stmt_elem        = Element.Shows [(binding, [(#lemma_stmt conjecture, [])])]: (string, string) Element.stmt;
    val pst_to_be_proved = Proof.theorem_cmd NONE (K I) [[(#lemma_stmt conjecture, [])]] (Proof.context_of pst)
    val script_opt       = pst_to_proofscript_opt pst_to_be_proved                                             : string option;

    fun string_to_stttac (str:string) =
      if   str = "done"
      then Subtools.is_solved
      else Subtools.sh_output_to_sh_stttac str
    val pst_n_log  = case script_opt of
       NONE                 => (pst, NONE)
     | SOME (script:string) => (
       let
         val pst_to_be_proved = Specification.theorem_cmd true Thm.theoremK NONE (K I) binding [] [] stmt_elem false (Proof.context_of pst);
         val proof_scripts    = Utils.init (space_explode "\n" (YXML.content_of script)) |> Utils.init    : strings;
         val stttacs_on_pst   = map string_to_stttac proof_scripts: Proof.state Dynamic_Utils.stttac list;
         (*TODO: Monad fix?*)
         fun apply_stttacs_to_pst (pst:Proof.state) []                = (fn _ => Seq.single ([], pst)): Proof.state Monadic_Interpreter_Core.monad
           | apply_stttacs_to_pst (pst:Proof.state) [stttac]          = stttac pst                    : Proof.state Monadic_Interpreter_Core.monad
           | apply_stttacs_to_pst (pst:Proof.state) (stttac::stttacs) = Monadic_Interpreter_Core.bind (stttac pst) (fn new_pst => apply_stttacs_to_pst new_pst stttacs)
         val resulting_pst = apply_stttacs_to_pst pst_to_be_proved stttacs_on_pst [] |> Seq.hd |> snd: Proof.state;
       in
         (resulting_pst, SOME {name = #lemma_name conjecture, stmt = #lemma_stmt conjecture, proof = script})
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

fun conjecture_n_pst_to_pst_n_proof conjectures pst = conjectures_n_pst_to_pst_n_proof' conjectures pst [];
\<close>

ML\<open> fun conjectures_n_lthy_to_pst_n_proof (conjectures: {lemma_name: string, lemma_stmt: string} list) (lthy:local_theory) =
  let
    val (pst, proof) = fst_conjecture_n_lthy_to_some_pst_n_proof lthy
    val ((pst_final, prf1), prf2) = conjecture_n_pst_to_pst_n_proof conjectures pst
  in
    conjectures_n_pst_to_pst_n_proof' conjectures pst []
  end;
\<close>

strategy ur_strategy =
Ors [
  Thens [Auto, IsSolved],                                       
  Thens [Smart_Induct,
    Ors
      [Thens [Auto, IsSolved],
       Thens [
         Repeat (Ors [Fastforce, Hammer]),
         IsSolved
       ]
    ]
  ]
]

datatype Nat = Z | S "Nat"

fun t2 :: "Nat => Nat => Nat" where
"t2 (Z) y = y"
| "t2 (S z) y = S (t2 z y)"

lemma t2_succ: "S (t2 n m) = t2 n (S m)"
  by(induct n, auto)

theorem property0 :
  "((t2 x1 (S x1)) = (S (t2 x1 x1)))"
  apply(induction x1, auto)
  apply(simp add:t2_succ)
  done

ML\<open>
val conjectures = [
  {lemma_name = "helper",  lemma_stmt = "True"},
  {lemma_name = "helper2", lemma_stmt = "True"}
]
\<close>

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

fun theorem spec descr =
  Outer_Syntax.local_theory @{command_keyword prove} ("state " ^ descr)
    (((long_statement || short_statement) >> (fn (_, _, _, _, concl) =>
       (fn lthy =>
          let
            fun statement_to_conjecture (Element.Shows [((binding, _), [(stmt:string, [])])]) =
                {lemma_name = Binding.name_of binding: string,
                 lemma_stmt = stmt |> YXML.content_of |> String.explode |> Utils.init |> tl |> String.implode}
              | statement_to_conjecture _ = error "statement_to_conjecture failed.";
            val ((_, _), prfs2) = conjectures_n_lthy_to_pst_n_proof (conjectures @ [statement_to_conjecture concl]) lthy
              : (Proof.state * conjecture_w_proof list) * conjecture_w_proof list;
            val _ = map (tracing o print_conjecture_w_proof) prfs2;
          in
            lthy
          end)))
     );

in

val _ = theorem \<^command_keyword>\<open>prove\<close> "theorem";

end;
\<close>

prove dfd:"False \<or> True"

end