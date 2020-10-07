(*
 * Copyright (C) 2014 NICTA
 * All rights reserved.
 *)

(* Author: David Cock - David.Cock@nicta.com.au *)

section "Structured Reasoning"

theory StructuredReasoning imports Algebra begin

text \<open>By linking the algebraic, the syntactic, and the semantic views
  of computation, we derive a set of rules for decomposing expectation
  entailment proofs, firstly over the syntactic structure of a program,
  and secondly over the refinement relation.  These rules also form the
  basis for automated reasoning.\<close>

subsection \<open>Syntactic Decomposition\<close>

lemma wp_Abort:
  "(\<lambda>s. 0) \<tturnstile> wp Abort Q"
  unfolding wp_eval by(simp)

lemma wlp_Abort:
  "(\<lambda>s. 1) \<tturnstile> wlp Abort Q"
  unfolding wp_eval by(simp)

lemma wp_Skip:
  "P \<tturnstile> wp Skip P"
  unfolding wp_eval by(blast)

lemma wlp_Skip:
  "P \<tturnstile> wlp Skip P"
  unfolding wp_eval by(blast)

lemma wp_Apply:
  "Q o f \<tturnstile> wp (Apply f) Q"
  unfolding wp_eval by(simp)

lemma wlp_Apply:
  "Q o f \<tturnstile> wlp (Apply f) Q"
  unfolding wp_eval by(simp)

lemma wp_Seq:
  assumes ent_a: "P \<tturnstile> wp a Q"
      and ent_b: "Q \<tturnstile> wp b R"
      and wa:   "well_def a"
      and wb:   "well_def b"
      and s_Q:   "sound Q"
      and s_R:   "sound R"
  shows "P \<tturnstile> wp (a ;; b) R"
proof -
  note ha = well_def_wp_healthy[OF wa]
  note hb = well_def_wp_healthy[OF wb]
  note ent_a
  also from ent_b ha hb s_Q s_R have "wp a Q \<tturnstile> wp a (wp b R)"
    by(blast intro:healthy_monoD2)
  finally show ?thesis by(simp add:wp_eval)
qed

lemma wlp_Seq:
  assumes ent_a: "P \<tturnstile> wlp a Q"
      and ent_b: "Q \<tturnstile> wlp b R"
      and wa:   "well_def a"
      and wb:   "well_def b"
      and u_Q:   "unitary Q"
      and u_R:   "unitary R"
  shows "P \<tturnstile> wlp (a ;; b) R"
proof -
  note ha = well_def_wlp_nearly_healthy[OF wa]
  note hb = well_def_wlp_nearly_healthy[OF wb]
  note ent_a
  also from ent_b ha hb u_Q u_R have "wlp a Q \<tturnstile> wlp a (wlp b R)"
    by(blast intro:nearly_healthy_monoD[OF ha])
  finally show ?thesis by(simp add:wp_eval)
qed

lemma wp_PC:
  "(\<lambda>s. P s * wp a Q s + (1 - P s) * wp b Q s) \<tturnstile> wp (a \<^bsub>P\<^esub>\<oplus> b) Q"
  by(simp add:wp_eval)

lemma wlp_PC:
  "(\<lambda>s. P s * wlp a Q s + (1 - P s) * wlp b Q s) \<tturnstile> wlp (a \<^bsub>P\<^esub>\<oplus> b) Q"
  by(simp add:wp_eval)

text \<open>A simpler rule for when the probability does not depend on the state.\<close>
lemma PC_fixed:
  assumes wpa: "P \<tturnstile> a ab R"
      and wpb: "Q \<tturnstile> b ab R"
      and np: "0 \<le> p" and bp: "p \<le> 1"
  shows "(\<lambda>s. p * P s + (1 - p) * Q s) \<tturnstile> (a \<^bsub>(\<lambda>s. p)\<^esub>\<oplus> b) ab R"
  unfolding PC_def
proof(rule le_funI)
  fix s
  from wpa and np have "p * P s \<le> p * a ab R s"
    by(auto intro:mult_left_mono)
  moreover {
    from bp have "0 \<le> 1 - p" by(simp)
    with wpb have "(1 - p) * Q s \<le> (1 - p) * b ab R s"
      by(auto intro:mult_left_mono)
  }
  ultimately show "p * P s + (1 - p) * Q s \<le>
                   p * a ab R s + (1 - p) * b ab R s"
    by(rule add_mono)
qed

lemma wp_PC_fixed:
  "\<lbrakk> P \<tturnstile> wp a R; Q \<tturnstile> wp b R; 0 \<le> p; p \<le> 1 \<rbrakk> \<Longrightarrow>
  (\<lambda>s. p * P s + (1 - p) * Q s) \<tturnstile> wp (a \<^bsub>(\<lambda>s. p)\<^esub>\<oplus> b) R"
  by(simp add:wp_def PC_fixed)

lemma wlp_PC_fixed:
  "\<lbrakk> P \<tturnstile> wlp a R; Q \<tturnstile> wlp b R; 0 \<le> p; p \<le> 1 \<rbrakk> \<Longrightarrow>
  (\<lambda>s. p * P s + (1 - p) * Q s) \<tturnstile> wlp (a \<^bsub>(\<lambda>s. p)\<^esub>\<oplus> b) R"
  by(simp add:wlp_def PC_fixed)

lemma wp_DC:
  "(\<lambda>s. min (wp a Q s) (wp b Q s)) \<tturnstile> wp (a \<Sqinter> b) Q"
  unfolding wp_eval by(simp)

lemma wlp_DC:
  "(\<lambda>s. min (wlp a Q s) (wlp b Q s)) \<tturnstile> wlp (a \<Sqinter> b) Q"
  unfolding wp_eval by(simp)

text \<open>Combining annotations for both branches:\<close>
lemma DC_split:
  fixes a::"'s prog" and b
  assumes wpa: "P \<tturnstile> a ab R"
      and wpb: "Q \<tturnstile> b ab R"
  shows "(\<lambda>s. min (P s) (Q s)) \<tturnstile> (a \<Sqinter> b) ab R"
  unfolding DC_def
proof(rule le_funI)
  fix s
  from wpa wpb
  have "P s \<le> a ab R s" and "Q s \<le> b ab R s" by(auto)
  thus "min (P s) (Q s) \<le> min (a ab R s) (b ab R s)" by(auto)
qed

lemma wp_DC_split:
  "\<lbrakk> P \<tturnstile> wp prog R; Q \<tturnstile> wp prog' R \<rbrakk> \<Longrightarrow>
  (\<lambda>s. min (P s) (Q s)) \<tturnstile> wp (prog \<Sqinter> prog') R"
  by(simp add:wp_def DC_split)

lemma wlp_DC_split:
  "\<lbrakk> P \<tturnstile> wlp prog R; Q \<tturnstile> wlp prog' R \<rbrakk> \<Longrightarrow>
  (\<lambda>s. min (P s) (Q s)) \<tturnstile> wlp (prog \<Sqinter> prog') R"
  by(simp add:wlp_def DC_split)

lemma wp_DC_split_same:
  "\<lbrakk> P \<tturnstile> wp prog Q; P \<tturnstile> wp prog' Q \<rbrakk> \<Longrightarrow> P \<tturnstile> wp (prog \<Sqinter> prog') Q"
  unfolding wp_eval by(blast intro:min.boundedI)

lemma wlp_DC_split_same:
  "\<lbrakk> P \<tturnstile> wlp prog Q; P \<tturnstile> wlp prog' Q \<rbrakk> \<Longrightarrow> P \<tturnstile> wlp (prog \<Sqinter> prog') Q"
  unfolding wp_eval by(blast intro:min.boundedI)

lemma SetPC_split:
  fixes f::"'x \<Rightarrow> 'y prog"
    and p::"'y \<Rightarrow> 'x \<Rightarrow> real"
  assumes rec: "\<And>x s. x \<in> supp (p s) \<Longrightarrow> P x \<tturnstile> f x ab Q"
      and nnp: "\<And>s. nneg (p s)"
  shows "(\<lambda>s. \<Sum>x \<in> supp (p s). p s x * P x s) \<tturnstile> SetPC f p ab Q"
  unfolding SetPC_def
proof(rule le_funI)
  fix s
  from rec have "\<And>x. x \<in> supp (p s) \<Longrightarrow> P x s \<le> f x ab Q s" by(blast)
  moreover from nnp have "\<And>x. 0 \<le> p s x" by(blast)
  ultimately have "\<And>x. x \<in> supp (p s) \<Longrightarrow> p s x * P x s \<le> p s x * f x ab Q s"
    by(blast intro:mult_left_mono)
  thus "(\<Sum>x \<in> supp (p s). p s x * P x s) \<le> (\<Sum>x \<in> supp (p s). p s x * f x ab Q s)"
    by(rule sum_mono)
qed

lemma wp_SetPC_split:
  "\<lbrakk> \<And>x s. x \<in> supp (p s) \<Longrightarrow> P x \<tturnstile> wp (f x) Q; \<And>s. nneg (p s) \<rbrakk> \<Longrightarrow>
   (\<lambda>s. \<Sum>x \<in> supp (p s). p s x * P x s) \<tturnstile> wp (SetPC f p) Q"
  by(simp add:wp_def SetPC_split)

lemma wlp_SetPC_split:
  "\<lbrakk> \<And>x s. x \<in> supp (p s) \<Longrightarrow> P x \<tturnstile> wlp (f x) Q; \<And>s. nneg (p s) \<rbrakk> \<Longrightarrow>
   (\<lambda>s. \<Sum>x \<in> supp (p s). p s x * P x s) \<tturnstile> wlp (SetPC f p) Q"
  by(simp add:wlp_def SetPC_split)

lemma wp_SetDC_split:
  "\<lbrakk> \<And>s x. x \<in> S s \<Longrightarrow> P \<tturnstile> wp (f x) Q; \<And>s. S s \<noteq> {} \<rbrakk> \<Longrightarrow>
   P \<tturnstile> wp (SetDC f S) Q"
  by(rule le_funI, unfold wp_eval, blast intro!:cInf_greatest)

lemma wlp_SetDC_split:
  "\<lbrakk> \<And>s x. x \<in> S s \<Longrightarrow> P \<tturnstile> wlp (f x) Q; \<And>s. S s \<noteq> {} \<rbrakk> \<Longrightarrow>
   P \<tturnstile> wlp (SetDC f S) Q"
  by(rule le_funI, unfold wp_eval, blast intro!:cInf_greatest)

lemma wp_SetDC:
  assumes wp: "\<And>s x. x \<in> S s \<Longrightarrow> P x \<tturnstile> wp (f x) Q"
      and ne: "\<And>s. S s \<noteq> {}"
      and sP: "\<And>x. sound (P x)"
  shows "(\<lambda>s. Inf ((\<lambda>x. P x s) ` S s)) \<tturnstile> wp (SetDC f S) Q"
  using assms by(intro le_funI, simp add:wp_eval, blast intro!:cInf_mono)

lemma wlp_SetDC:
  assumes wp: "\<And>s x. x \<in> S s \<Longrightarrow> P x \<tturnstile> wlp (f x) Q"
      and ne: "\<And>s. S s \<noteq> {}"
      and sP: "\<And>x. sound (P x)"
  shows "(\<lambda>s. Inf ((\<lambda>x. P x s) ` S s)) \<tturnstile> wlp (SetDC f S) Q"
  using assms by(intro le_funI, simp add:wp_eval, blast intro!:cInf_mono)

lemma wp_Embed:
  "P \<tturnstile> t Q \<Longrightarrow> P \<tturnstile> wp (Embed t) Q"
  by(simp add:wp_def Embed_def)

lemma wlp_Embed:
  "P \<tturnstile> t Q \<Longrightarrow> P \<tturnstile> wlp (Embed t) Q"
  by(simp add:wlp_def Embed_def)

lemma wp_Bind:
  "\<lbrakk> \<And>s. P s \<le> wp (a (f s)) Q s \<rbrakk> \<Longrightarrow> P \<tturnstile> wp (Bind f a) Q"
  by(auto simp:wp_def Bind_def)

lemma wlp_Bind:
  "\<lbrakk> \<And>s. P s \<le> wlp (a (f s)) Q s \<rbrakk> \<Longrightarrow> P \<tturnstile> wlp (Bind f a) Q"
  by(auto simp:wlp_def Bind_def)

lemma wp_repeat:
  "\<lbrakk> P \<tturnstile> wp a Q; Q \<tturnstile> wp (repeat n a) R;
     well_def a; sound Q; sound R \<rbrakk> \<Longrightarrow> P \<tturnstile> wp (repeat (Suc n) a) R"
  by(auto intro!:wp_Seq wd_intros)

lemma wlp_repeat:
  "\<lbrakk> P \<tturnstile> wlp a Q; Q \<tturnstile> wlp (repeat n a) R;
     well_def a; unitary Q; unitary R \<rbrakk> \<Longrightarrow> P \<tturnstile> wlp (repeat (Suc n) a) R"
  by(auto intro!:wlp_Seq wd_intros)

text \<open>Note that the loop rules presented in section \autoref{s:loop_rules} are of the same form,
and would belong here, had they not already been stated.\<close>

text \<open>The following rules are specialisations of those for general
  transformers, and are easier for the unifier to match.\<close>
lemmas wp_strengthen_post=
  entails_strengthen_post[where t="wp a" for a]

lemma wlp_strengthen_post:
  "P \<tturnstile> wlp a Q \<Longrightarrow> nearly_healthy (wlp a) \<Longrightarrow> unitary R \<Longrightarrow> Q \<tturnstile> R \<Longrightarrow> unitary Q \<Longrightarrow>
   P \<tturnstile> wlp a R"
  by(blast intro:entails_trans)

lemmas wp_weaken_pre=
  entails_weaken_pre[where t="wp a" for a]
lemmas wlp_weaken_pre=
  entails_weaken_pre[where t="wlp a" for a]

lemmas wp_scale=
  entails_scale[where t="wp a" for a, OF _ well_def_wp_healthy]

subsection \<open>Algebraic Decomposition\<close>

text \<open>Refinement is a powerful tool for decomposition, belied by the simplicity of the rule.
This is an \emph{axiomatic} formulation of refinement (all annotations of the @{term a}
are annotations of @{term b}), rather than an operational version (all traces of @{term b} are
traces of @{term a}.\<close>

lemma wp_refines:
  "\<lbrakk> a \<sqsubseteq> b; P \<tturnstile> wp a Q; sound Q \<rbrakk> \<Longrightarrow> P \<tturnstile> wp b Q"
  by(auto intro:entails_trans)

lemmas wp_drefines = drefinesD

subsection \<open>Hoare triples\<close>

text \<open>The Hoare triple, or validity predicate, is logically equivalent to the weakest-precondition
entailment form. The benefit is that it allows us to define transitivity rules for computational
(also/finally) reasoning.\<close>

definition
  wp_valid :: "('a \<Rightarrow> real) \<Rightarrow> 'a prog \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool" ("\<lbrace>_\<rbrace> _ \<lbrace>_\<rbrace>p")
where
  "wp_valid P prog Q \<equiv> P \<tturnstile> wp prog Q"

lemma wp_validI:
  "P \<tturnstile> wp prog Q \<Longrightarrow> \<lbrace>P\<rbrace> prog \<lbrace>Q\<rbrace>p"
  unfolding wp_valid_def by(assumption)

lemma wp_validD:
  "\<lbrace>P\<rbrace> prog \<lbrace>Q\<rbrace>p \<Longrightarrow> P \<tturnstile> wp prog Q"
  unfolding wp_valid_def by(assumption)

lemma valid_Seq:
  "\<lbrakk> \<lbrace>P\<rbrace> a \<lbrace>Q\<rbrace>p; \<lbrace>Q\<rbrace> b \<lbrace>R\<rbrace>p; well_def a; well_def b; sound Q; sound R \<rbrakk> \<Longrightarrow>
  \<lbrace>P\<rbrace> a ;; b \<lbrace>R\<rbrace>p"
  unfolding wp_valid_def by(rule wp_Seq)

text \<open>We make it available to the computational reasoner:\<close>
declare valid_Seq[trans]

end
