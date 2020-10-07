section \<open>Proving Relation (In)equalities via Regular Expressions\<close>

theory Regexp_Method
imports Equivalence_Checking Relation_Interpretation
begin

primrec rel_of_regexp :: "('a * 'a) set list \<Rightarrow> nat rexp \<Rightarrow> ('a * 'a) set" where
"rel_of_regexp vs Zero  = {}" |
"rel_of_regexp vs One  = Id" |
"rel_of_regexp vs (Atom i)  = vs ! i" |
"rel_of_regexp vs (Plus r s)  = rel_of_regexp vs r  \<union> rel_of_regexp vs s " |
"rel_of_regexp vs (Times r s)  = rel_of_regexp vs r O rel_of_regexp vs s" |
"rel_of_regexp vs (Star r)  = (rel_of_regexp vs r)^*"

lemma rel_of_regexp_rel: "rel_of_regexp vs r = rel (\<lambda>i. vs ! i) r"
by (induct r) auto

primrec rel_eq where
"rel_eq (r, s) vs = (rel_of_regexp vs r = rel_of_regexp vs s)"

lemma rel_eqI: "check_eqv r s \<Longrightarrow> rel_eq (r, s) vs"
unfolding rel_eq.simps rel_of_regexp_rel
by (rule Relation_Interpretation.soundness)
 (rule Equivalence_Checking.soundness)

lemmas regexp_reify = rel_of_regexp.simps rel_eq.simps
lemmas regexp_unfold = trancl_unfold_left subset_Un_eq

ML \<open>
local

fun check_eqv (ct, b) = Thm.mk_binop @{cterm "Pure.eq :: bool \<Rightarrow> bool \<Rightarrow> prop"}
  ct (if b then @{cterm True} else @{cterm False});

val (_, check_eqv_oracle) = Context.>>> (Context.map_theory_result
  (Thm.add_oracle (@{binding check_eqv}, check_eqv)));

in

val regexp_conv =
  @{computation_conv bool terms: check_eqv datatypes: "nat rexp"}
  (fn _ => fn b => fn ct => check_eqv_oracle (ct, b))

end
\<close>
  
method_setup regexp = \<open>
  Scan.succeed (fn ctxt =>
    SIMPLE_METHOD' (
      (TRY o eresolve_tac ctxt @{thms rev_subsetD})
      THEN' (Subgoal.FOCUS_PARAMS (fn {context = ctxt', ...} =>
        TRY (Local_Defs.unfold_tac ctxt' @{thms regexp_unfold})
        THEN Reification.tac ctxt' @{thms regexp_reify} NONE 1
        THEN resolve_tac ctxt' @{thms rel_eqI} 1
        THEN CONVERSION (HOLogic.Trueprop_conv (regexp_conv ctxt')) 1
        THEN resolve_tac ctxt' [TrueI] 1) ctxt)))
\<close> \<open>decide relation equalities via regular expressions\<close>

hide_const (open) le_rexp nPlus nTimes norm nullable bisimilar is_bisimulation closure
  pre_bisim add_atoms check_eqv rel word_rel rel_eq

text \<open>Example:\<close>

lemma "(r \<union> s^+)^* = (r \<union> s)^*"
  by regexp

end
