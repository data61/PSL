theory "Axioms" 
imports
  "Syntax"
  "Denotational_Semantics"
  "Ids"
begin

section \<open>Axioms and Axiomatic Proof Rules of Differential Game Logic\<close>

subsection \<open>Axioms\<close>

abbreviation pusall:: "fml"
  where "pusall \<equiv> \<langle>Game hgidc\<rangle>TT"

abbreviation nothing:: "trm"
  where "nothing \<equiv> Number 0"

  
named_theorems axiom_defs "Axiom definitions"

definition box_axiom :: "fml"
  where [axiom_defs]:
"box_axiom \<equiv> (Box (Game hgid1) pusall) \<leftrightarrow> Not(Diamond (Game hgid1) (Not(pusall)))"

definition assigneq_axiom :: "fml"
  where [axiom_defs]:
"assigneq_axiom \<equiv> (Diamond (Assign xid1 (Const fid1)) pusall) \<leftrightarrow> Exists xid1 (Equals (Var xid1) (Const fid1) && pusall)"

definition stutterd_axiom :: "fml"
  where [axiom_defs]:
"stutterd_axiom \<equiv> (Diamond (Assign xid1 (Var xid1)) pusall) \<leftrightarrow> pusall"

definition test_axiom :: "fml"
  where [axiom_defs]:
"test_axiom \<equiv> Diamond (Test (Pred pid2 nothing)) (Pred pid1 nothing) \<leftrightarrow> (Pred pid2 nothing && Pred pid1 nothing)"

definition choice_axiom :: "fml"
  where [axiom_defs]:
"choice_axiom \<equiv> Diamond (Choice (Game hgid1) (Game hgid2)) pusall \<leftrightarrow> (Diamond (Game hgid1) pusall || Diamond (Game hgid2) pusall)"

definition compose_axiom :: "fml"
  where [axiom_defs]:
"compose_axiom \<equiv> Diamond (Compose (Game hgid1) (Game hgid2)) pusall \<leftrightarrow> Diamond (Game hgid1) (Diamond (Game hgid2) pusall)"

definition iterate_axiom :: "fml"
  where [axiom_defs]:
"iterate_axiom \<equiv> Diamond (Loop (Game hgid1)) pusall \<leftrightarrow> (pusall || Diamond (Game hgid1) (Diamond (Loop (Game hgid1)) pusall))"

definition dual_axiom :: "fml"
  where [axiom_defs]:
"dual_axiom \<equiv> Diamond (Dual (Game hgid1)) pusall \<leftrightarrow> !(Diamond (Game hgid1) (!pusall))"


subsection \<open>Axiomatic Rules\<close>

named_theorems rule_defs "Rule definitions"

definition mon_rule :: "inference"
  where [rule_defs]:
"mon_rule \<equiv> ([(\<langle>Game hgidc\<rangle>TT) \<rightarrow> (\<langle>Game hgidd\<rangle>TT)], (\<langle>Game hgid1\<rangle>(\<langle>Game hgidc\<rangle>TT)) \<rightarrow> (\<langle>Game hgid1\<rangle>(\<langle>Game hgidd\<rangle>TT)))"

definition FP_rule :: "inference"
  where [rule_defs]:
"FP_rule \<equiv> ([((\<langle>Game hgidc\<rangle>TT) || \<langle>Game hgid1\<rangle>\<langle>Game hgidd\<rangle>TT) \<rightarrow> \<langle>Game hgidd\<rangle>TT], (\<langle>Loop (Game hgid1)\<rangle>\<langle>Game hgidc\<rangle>TT) \<rightarrow> (\<langle>Game hgidd\<rangle>TT))"

definition MP_rule :: "inference"
  where [rule_defs]:
"MP_rule \<equiv> ([Pred pid1 nothing , Pred pid1 nothing \<rightarrow> Pred pid2 nothing], Pred pid2 nothing)"

definition gena_rule :: "inference"
  where [rule_defs]:
"gena_rule \<equiv> ([pusall], Exists xid1 pusall)"


subsection \<open>Soundness / Validity Proofs for Axioms\<close>

text \<open>Because an axiom in a uniform substitution calculus is an individual formula, 
  proving the validity of that formula suffices to prove soundness\<close>

lemma box_valid: "valid box_axiom"
  unfolding box_axiom_def Box_def Or_def by simp

(*lemma assign_equal: "game_sem I (Assign x (Const f)) (fml_sem I \<phi>) = fml_sem I (Exists x (Equals (Var x) (Const f) && \<phi>))"
  by simp*)

lemma assigneq_valid: "valid assigneq_axiom"
  unfolding assigneq_axiom_def by (auto simp add: valid_equiv)
  
(*lemma game_sem_stutter: "game_sem I (Assign x (Var x)) X = X"
  by (auto simp add: repv_self)*)

lemma stutterd_valid: "valid stutterd_axiom"
  unfolding stutterd_axiom_def by (auto simp add: valid_equiv)

lemma test_valid: "valid test_axiom"
  unfolding test_axiom_def Or_def using valid_equiv by fastforce

lemma choice_valid: "valid choice_axiom"
  unfolding choice_axiom_def Or_def by (auto simp add: valid_equiv)

lemma compose_valid: "valid compose_axiom"
  unfolding compose_axiom_def Or_def by (simp add: valid_equiv)

lemma dual_valid: "valid dual_axiom"
unfolding dual_axiom_def using valid_equiv fml_sem_not using fml_sem.simps(6) game_sem.simps(7) by presburger

lemma iterate_valid: "valid iterate_axiom"
(*unfolding iterate_axiom_def using valid_equiv fml_sem.simps(6) game_equiv_subst[OF loop_iterate_equiv]*)
proof-
  have "\<forall>I. fml_sem I (Diamond (Loop (Game hgid1)) pusall) = fml_sem I (pusall || Diamond (Game hgid1) (Diamond (Loop (Game hgid1)) pusall))"
  proof
  fix I
    have "fml_sem I (Diamond (Loop (Game hgid1)) pusall) = game_sem I (Loop (Game hgid1)) (fml_sem I pusall)" by (rule fml_sem.simps(6))
    also have "... = game_sem I (Choice Skip (Compose (Game hgid1) (Loop (Game hgid1)))) (fml_sem I pusall)"
    using game_equiv_subst[where I=I and X=\<open>fml_sem I pusall\<close>, OF loop_iterate_equiv[where \<alpha>=\<open>Game hgid1\<close>]] by blast
    also have "... = fml_sem I (Diamond (Choice Skip (Compose (Game hgid1) (Loop (Game hgid1)))) pusall)" by simp
    also have "... = fml_sem I (Diamond Skip pusall || Diamond (Compose (Game hgid1) (Loop (Game hgid1))) pusall)" by simp
    also have "... = fml_sem I (pusall || Diamond (Compose (Game hgid1) (Loop (Game hgid1))) pusall)" by simp
    also have "... = fml_sem I (pusall || Diamond (Game hgid1) (Diamond (Loop (Game hgid1)) pusall))" by simp
    finally show "fml_sem I (Diamond (Loop (Game hgid1)) pusall) = fml_sem I (pusall || Diamond (Game hgid1) (Diamond (Loop (Game hgid1)) pusall))" .
  qed
  then have "valid ((Diamond (Loop (Game hgid1)) pusall) \<leftrightarrow> (pusall || Diamond (Game hgid1) (Diamond (Loop (Game hgid1)) pusall)))" using valid_equiv by (rule rev_iffD2)
  then show "valid iterate_axiom" unfolding iterate_axiom_def by auto
qed


subsection \<open>Local Soundness Proofs for Axiomatic Rules\<close>

lemma mon_locsound: "locally_sound mon_rule"
  unfolding mon_rule_def locally_sound_def using valid_in_impl monotone by simp

lemma FP_locsound: "locally_sound FP_rule"
  unfolding FP_rule_def locally_sound_def using valid_in_impl game_sem_loop by auto

lemma MP_locsound: "locally_sound MP_rule"
  unfolding MP_rule_def locally_sound_def valid_in_def using fml_sem_implies less_Suc_eq by auto 

lemma gena_locsound: "locally_sound gena_rule"
  unfolding gena_rule_def locally_sound_def valid_in_def using fml_sem_implies less_Suc_eq by auto 

end
