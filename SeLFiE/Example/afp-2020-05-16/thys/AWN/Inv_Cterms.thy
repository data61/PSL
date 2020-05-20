(*  Title:       Inv_Cterms.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke
*)

section "A custom tactic for showing invariants via control terms"

theory Inv_Cterms
imports AWN_Labels
begin

text \<open>
  This tactic tries to solve a goal by reducing it to a problem over (local) cterms (using
  one of the cterms\_intros intro rules); expanding those to consider all process names (using
  one of the ctermsl\_cases destruction rules); simplifying each (using the
  cterms\_env simplification rules); splitting them up into separate subgoals; replacing the
  derivative term with a variable; `executing' a transition of each term; and then simplifying.

  The tactic can stop after applying introduction rule (``inv\_cterms (intro\_only)''), or after
  having generated the verification condition subgoals and before having simplified them
  (``inv\_cterms (vcs\_only)''). It takes arguments to add or remove simplification rules
  (``simp add: lemmanames''), to add forward rules on assumptions (to introduce previously
  proved invariants; ``inv add: lemmanames''), or to add elimination rules that solve any
  remaining subgoals (``solve: lemmanames'').

  To configure the tactic for a set of transition rules:
  \begin{enumerate}
  \item add elimination rules: declare seqpTEs [cterms\_seqte]
  \item add rules to replace derivative terms: declare elimders [cterms\_elimders]
  \end{enumerate}

  To configure the tactic for a process environment (\<open>\<Gamma>\<close>):
  \begin{enumerate}
  \item add simp rules: declare \<open>\<Gamma>\<close>.simps [cterms\_env]
  \item add case rules: declare aodv\_proc\_cases [ctermsl\_cases]
  \item add invariant intros
      declare
        seq\_invariant\_ctermsI [OF aodv\_wf aodv\_control\_within aodv\_simple\_labels, cterms\_intros]
        seq\_step\_invariant\_ctermsI [OF aodv\_wf aodv\_control\_within aodv\_simple\_labels, cterms\_intros]
  \end{enumerate}

\<close>

lemma has_ctermsl: "p \<in> ctermsl \<Gamma> \<Longrightarrow> p \<in> ctermsl \<Gamma>" .

named_theorems cterms_elimders "rules for truncating sequential process terms"
named_theorems cterms_seqte "elimination rules for sequential process terms"
named_theorems cterms_env "simplification rules for sequential process environments"
named_theorems ctermsl_cases "destruction rules for case splitting ctermsl"
named_theorems cterms_intros "introduction rules from cterms"
named_theorems cterms_invs "invariants to try to apply at each vc"
named_theorems cterms_final "elimination rules to try on each vc after simplification"

ML \<open>
fun simp_only thms ctxt =
  asm_full_simp_tac
     (ctxt |> Raw_Simplifier.clear_simpset |> fold Simplifier.add_simp thms)

(* shallow_simp is useful for mopping up assumptions before really trying to simplify.
   Perhaps surprisingly, this saves minutes in some of the proofs that use a lot of
   invariants of the form (l = P-:n --> P). *)
fun shallow_simp ctxt =
  let val ctxt' = Config.put simp_depth_limit 2 ctxt in
    TRY o safe_asm_full_simp_tac ctxt'
  end

fun create_vcs ctxt i =
  let val main_simp_thms = rev (Named_Theorems.get ctxt @{named_theorems cterms_env})
      val ctermsl_cases = rev (Named_Theorems.get ctxt @{named_theorems ctermsl_cases})
  in
    dresolve_tac ctxt @{thms has_ctermsl} i
    THEN_ELSE (dmatch_tac ctxt ctermsl_cases i
               THEN
               TRY (REPEAT_ALL_NEW (ematch_tac ctxt [@{thm disjE}]) i)
               THEN
               PARALLEL_ALLGOALS
                 (fn i => simp_only main_simp_thms ctxt i
                  THEN TRY (REPEAT_ALL_NEW (ematch_tac ctxt [@{thm disjE}]) i)), all_tac)
  end

fun try_invs ctxt =
  let val inv_thms = rev (Named_Theorems.get ctxt @{named_theorems cterms_invs})
      fun fapp thm =
        TRY o (EVERY' (forward_tac ctxt [thm] :: replicate (Thm.nprems_of thm - 1) (assume_tac ctxt)))
  in
    EVERY' (map fapp inv_thms)
  end

fun try_final ctxt =
  let val final_thms = rev (Named_Theorems.get ctxt @{named_theorems cterms_final})
      fun eapp thm = EVERY' (eresolve_tac ctxt [thm] :: replicate (Thm.nprems_of thm - 1) (assume_tac ctxt))
  in
    TRY o (FIRST' (map eapp final_thms))
  end

fun each ctxt =
  (EVERY' ((ematch_tac ctxt (rev (Named_Theorems.get ctxt @{named_theorems cterms_elimders})) ::
    replicate 2 (assume_tac ctxt)))
   THEN' simp_only @{thms labels_psimps} ctxt
   THEN' (ematch_tac ctxt (rev (Named_Theorems.get ctxt @{named_theorems cterms_seqte}))
     THEN_ALL_NEW
       (fn j => simp_only [@{thm mem_Collect_eq}] ctxt j
                  THEN REPEAT (eresolve_tac ctxt @{thms exE} j)
                  THEN REPEAT (eresolve_tac ctxt @{thms conjE} j))))
  ORELSE' (SOLVED' (clarsimp_tac ctxt))

fun simp_all ctxt =
  let val ctxt' =
        ctxt |> fold Splitter.add_split [@{thm if_split_asm}]
  in
    PARALLEL_ALLGOALS (shallow_simp ctxt)
    THEN
    TRY (CHANGED_PROP (PARALLEL_ALLGOALS (asm_full_simp_tac ctxt' THEN' try_final ctxt)))
  end

fun intro_and_invs ctxt i =
  let val cterms_intros = rev (Named_Theorems.get ctxt @{named_theorems cterms_intros}) in
    match_tac ctxt cterms_intros i
    THEN PARALLEL_ALLGOALS (try_invs ctxt)
  end

fun process_vcs ctxt _ =
  ALLGOALS (create_vcs ctxt ORELSE' (SOLVED' (clarsimp_tac ctxt)))
  THEN PARALLEL_ALLGOALS (TRY o each ctxt)
\<close>

method_setup inv_cterms = \<open>
  let
    val intro_onlyN = "intro_only"
    val vcs_onlyN = "vcs_only"
    val invN = "inv"
    val solveN = "solve"

    val inv_cterms_options =
      (Args.parens (Args.$$$ intro_onlyN) >>  K intro_and_invs ||
       Args.parens (Args.$$$ vcs_onlyN) >>  K (fn ctxt => intro_and_invs ctxt
                                                          THEN' process_vcs ctxt) ||
       Scan.succeed (fn ctxt => intro_and_invs ctxt
                                THEN' process_vcs ctxt
                                THEN' K (simp_all ctxt)))
  in
    (Scan.lift inv_cterms_options --| Method.sections
      ((Args.$$$ invN -- Args.add -- Args.colon >>
        K (Method.modifier (Named_Theorems.add @{named_theorems cterms_invs}) \<^here>))
       :: (Args.$$$ solveN -- Args.colon >>
        K (Method.modifier (Named_Theorems.add @{named_theorems cterms_final}) \<^here>))
       :: Simplifier.simp_modifiers)
      >> (fn tac => SIMPLE_METHOD' o tac))
  end
\<close> "solve invariants by considering all (interesting) control terms"

declare
  insert_iff [cterms_env]                                                
  Un_insert_right [cterms_env]
  sup_bot_right [cterms_env]
  Product_Type.prod_cases [cterms_env]
  ctermsl.simps [cterms_env]

end
