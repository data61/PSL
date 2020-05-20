(* Authors: Gerwin Klein and Rafal Kolanski, 2012
   Maintainers: Gerwin Klein <kleing at cse.unsw.edu.au>
                Rafal Kolanski <rafal.kolanski at nicta.com.au>
*)

section "Separation Logic Tactics"

theory Sep_Tactics
imports Separation_Algebra
begin

ML_file \<open>sep_tactics.ML\<close>

text \<open>A number of proof methods to assist with reasoning about separation logic.\<close>


section \<open>Selection (move-to-front) tactics\<close>

method_setup sep_select = \<open>
  Scan.lift Parse.int >> (fn n => fn ctxt => SIMPLE_METHOD' (sep_select_tac ctxt n))
\<close> "Select nth separation conjunct in conclusion"

method_setup sep_select_asm = \<open>
  Scan.lift Parse.int >> (fn n => fn ctxt => SIMPLE_METHOD' (sep_select_asm_tac ctxt n))
\<close> "Select nth separation conjunct in assumptions"


section \<open>Substitution\<close>

method_setup "sep_subst" = \<open>
  Scan.lift (Args.mode "asm" -- Scan.optional (Args.parens (Scan.repeat Parse.nat)) [0]) --
    Attrib.thms >> (fn ((asm, occs), thms) => fn ctxt =>
      SIMPLE_METHOD' ((if asm then sep_subst_asm_tac else sep_subst_tac) ctxt occs thms))
\<close>
"single-step substitution after solving one separation logic assumption"


section \<open>Forward Reasoning\<close>

method_setup "sep_drule" = \<open>
  Attrib.thms >> (fn thms => fn ctxt => SIMPLE_METHOD' (sep_dtac ctxt thms))
\<close> "drule after separating conjunction reordering"

method_setup "sep_frule" = \<open>
  Attrib.thms >> (fn thms => fn ctxt => SIMPLE_METHOD' (sep_ftac ctxt thms))
\<close> "frule after separating conjunction reordering"


section \<open>Backward Reasoning\<close>

method_setup "sep_rule" = \<open>
  Attrib.thms >> (fn thms => fn ctxt => SIMPLE_METHOD' (sep_rtac ctxt thms))
\<close> "applies rule after separating conjunction reordering"


section \<open>Cancellation of Common Conjuncts via Elimination Rules\<close>

named_theorems sep_cancel

text \<open>
  The basic \<open>sep_cancel_tac\<close> is minimal. It only eliminates
  erule-derivable conjuncts between an assumption and the conclusion.

  To have a more useful tactic, we augment it with more logic, to proceed as
  follows:
  \begin{itemize}
  \item try discharge the goal first using \<open>tac\<close>
  \item if that fails, invoke \<open>sep_cancel_tac\<close>
  \item if \<open>sep_cancel_tac\<close> succeeds
    \begin{itemize}
    \item try to finish off with tac (but ok if that fails)
    \item try to finish off with @{term sep_true} (but ok if that fails)
    \end{itemize}
  \end{itemize}
\<close>

ML \<open>
  fun sep_cancel_smart_tac ctxt tac =
    let fun TRY' tac = tac ORELSE' (K all_tac)
    in
      tac
      ORELSE' (sep_cancel_tac ctxt tac
               THEN' TRY' tac
               THEN' TRY' (resolve_tac ctxt @{thms TrueI}))
      ORELSE' (eresolve_tac ctxt @{thms sep_conj_sep_emptyE}
               THEN' sep_cancel_tac ctxt tac
               THEN' TRY' tac
               THEN' TRY' (resolve_tac ctxt @{thms TrueI}))
    end;

  fun sep_cancel_smart_tac_rules ctxt etacs =
      sep_cancel_smart_tac ctxt (FIRST' ([assume_tac ctxt] @ etacs));

  val sep_cancel_syntax = Method.sections [
    Args.add -- Args.colon >>
      K (Method.modifier (Named_Theorems.add @{named_theorems sep_cancel}) \<^here>)];
\<close>

method_setup sep_cancel = \<open>
  sep_cancel_syntax >> (fn _ => fn ctxt =>
    let
      val etacs = map (eresolve_tac ctxt o single)
        (rev (Named_Theorems.get ctxt @{named_theorems sep_cancel}));
    in
      SIMPLE_METHOD' (sep_cancel_smart_tac_rules ctxt etacs)
    end)
\<close> "Separating conjunction conjunct cancellation"

text \<open>
  As above, but use blast with a depth limit to figure out where cancellation
  can be done.\<close>

method_setup sep_cancel_blast = \<open>
  sep_cancel_syntax >> (fn _ => fn ctxt =>
    let
      val rules = rev (Named_Theorems.get ctxt @{named_theorems sep_cancel});
      val tac = Blast.depth_tac (ctxt addIs rules) 10;
    in
      SIMPLE_METHOD' (sep_cancel_smart_tac ctxt tac)
    end)
\<close> "Separating conjunction conjunct cancellation using blast"

end
