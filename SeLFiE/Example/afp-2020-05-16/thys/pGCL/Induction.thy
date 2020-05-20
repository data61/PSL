(*
 * Copyright (C) 2014 NICTA
 * All rights reserved.
 *)

(* Author: David Cock - David.Cock@nicta.com.au *)

section "Induction"

theory Induction
  imports Expectations Transformers
begin

text_raw \<open>\label{s:induction}\<close>

subsection \<open>The Lattice of Expectations\<close>

text_raw \<open>\label{s:exp_induct}\<close>

text \<open>Defining recursive (or iterative) programs requires us to reason about
fixed points on the semantic objects, in this case expectations.  The
complication here, compared to the standard Knaster-Tarski theorem (for example,
as shown in @{theory HOL.Inductive}), is that we do not have a complete lattice.

Finding a lower bound is easy (it's @{term "\<lambda>_. 0"}), but as we do not insist
on any global bound on expectations (and work directly in HOL's real type, rather
than extending it with a point at infinity), there is no top element.  We solve
the problem by defining the least (greatest) fixed point, restricted to an
internally-bounded set, allowing us to substitute this bound for the top element.
This works as long as the set contains at least one fixed point, which appears
as an extra assumption in all the theorems.

This also works semantically, thanks to the definition of healthiness.  Given a
healthy transformer parameterised by some sound expectation:
@{term "t::('s \<Rightarrow> real) \<Rightarrow> ('s \<Rightarrow> real) \<Rightarrow> 's \<Rightarrow> real"}.  Imagine that we wish to find
the least fixed point of @{term "t P"}.  In practice, @{term t} is generally
doubly healthy, that is @{term "\<forall>P. sound P \<longrightarrow> healthy (t P)"} and
@{term "\<forall>Q. sound Q \<longrightarrow> healthy (\<lambda>P. t P Q)"}.  Thus by feasibility, @{term "t P Q"}
must be bounded by @{term "bound_of P"}.  Thus, as by definition @{term "x \<le> t P x"}
for any fixed point, all must lie in the
set of sound expectations bounded above by @{term "\<lambda>_. bound_of P"}.\<close>

definition Inf_exp :: "'s expect set \<Rightarrow> 's expect"
where "Inf_exp S = (\<lambda>s. Inf {f s |f. f \<in> S})"

lemma Inf_exp_lower:
  "\<lbrakk> P \<in> S; \<forall>P\<in>S. nneg P \<rbrakk> \<Longrightarrow> Inf_exp S \<le> P"
  unfolding Inf_exp_def
  by(intro le_funI cInf_lower bdd_belowI[where m=0], auto)

lemma Inf_exp_greatest:
  "\<lbrakk> S \<noteq> {}; \<forall>P\<in>S. Q \<le> P \<rbrakk> \<Longrightarrow> Q \<le> Inf_exp S"
  unfolding Inf_exp_def by(auto intro!:le_funI[OF cInf_greatest])

definition Sup_exp :: "'s expect set \<Rightarrow> 's expect"
where "Sup_exp S = (if S = {} then \<lambda>s. 0 else (\<lambda>s. Sup {f s |f. f \<in> S}))"

lemma Sup_exp_upper:
  "\<lbrakk> P \<in> S; \<forall>P\<in>S. bounded_by b P \<rbrakk> \<Longrightarrow> P \<le> Sup_exp S"
  unfolding Sup_exp_def
  by(cases "S={}", simp_all, intro le_funI cSup_upper bdd_aboveI[where M=b], auto)

lemma Sup_exp_least:
  "\<lbrakk> \<forall>P\<in>S. P \<le> Q; nneg Q \<rbrakk> \<Longrightarrow> Sup_exp S \<le> Q"
  unfolding Sup_exp_def
  by(cases "S={}", auto intro!:le_funI[OF cSup_least])

lemma Sup_exp_sound:
  assumes sS: "\<And>P. P\<in>S \<Longrightarrow> sound P"
      and bS: "\<And>P. P\<in>S \<Longrightarrow> bounded_by b P"
  shows "sound (Sup_exp S)"
proof(cases "S={}", simp add:Sup_exp_def, blast,
      intro soundI2 bounded_byI2 nnegI2)
  assume neS: "S \<noteq> {}"
  then obtain P where Pin: "P \<in> S" by(auto)
  with sS bS have nP: "nneg P" "bounded_by b P" by(auto)
  hence nb: "0 \<le> b" by(auto)

  from bS nb show "Sup_exp S \<tturnstile> \<lambda>s. b"
    by(auto intro:Sup_exp_least)

  from nP have "\<lambda>s. 0 \<tturnstile> P" by(auto)
  also from Pin bS have "P \<tturnstile> Sup_exp S"
    by(auto intro:Sup_exp_upper)
  finally show "\<lambda>s. 0 \<tturnstile> Sup_exp S" .
qed

definition lfp_exp :: "'s trans \<Rightarrow> 's expect"
where "lfp_exp t = Inf_exp {P. sound P \<and> t P \<le> P}"

lemma lfp_exp_lowerbound:
  "\<lbrakk> t P \<le> P; sound P \<rbrakk> \<Longrightarrow> lfp_exp t \<le> P"
  unfolding lfp_exp_def by(auto intro:Inf_exp_lower)

lemma lfp_exp_greatest:
  "\<lbrakk> \<And>P. \<lbrakk> t P \<le> P; sound P \<rbrakk> \<Longrightarrow> Q \<le> P; sound Q; t R \<tturnstile> R; sound R \<rbrakk> \<Longrightarrow> Q \<le> lfp_exp t"
  unfolding lfp_exp_def by(auto intro:Inf_exp_greatest)

lemma feasible_lfp_exp_sound:
  "feasible t \<Longrightarrow> sound (lfp_exp t)"
  by(intro soundI2 bounded_byI2 nnegI2, auto intro!:lfp_exp_lowerbound lfp_exp_greatest)

lemma lfp_exp_sound:
  assumes fR: "t R \<tturnstile> R" and sR: "sound R"
  shows "sound (lfp_exp t)"
proof(intro soundI2)
  from fR sR have "lfp_exp t \<tturnstile> R"
    by(auto intro:lfp_exp_lowerbound)
  also from sR have "R \<tturnstile> \<lambda>s. bound_of R" by(auto)
  finally show "bounded_by (bound_of R) (lfp_exp t)" by(auto)
  from fR sR show "nneg (lfp_exp t)" by(auto intro:lfp_exp_greatest)
qed

lemma lfp_exp_bound:
  "(\<And>P. unitary P \<Longrightarrow> unitary (t P)) \<Longrightarrow> bounded_by 1 (lfp_exp t)"
  by(auto intro!:lfp_exp_lowerbound)

lemma lfp_exp_unitary:
  "(\<And>P. unitary P \<Longrightarrow> unitary (t P)) \<Longrightarrow> unitary (lfp_exp t)"
proof(intro unitaryI[OF lfp_exp_sound lfp_exp_bound], simp_all)
  assume IH: "\<And>P. unitary P \<Longrightarrow> unitary (t P)"
  have "unitary (\<lambda>s. 1)" by(auto)
  with IH have "unitary (t (\<lambda>s. 1))" by(auto)
  thus "t (\<lambda>s. 1) \<tturnstile> \<lambda>s. 1" by(auto)
  show "sound (\<lambda>s. 1)" by(auto)
qed

lemma lfp_exp_lemma2:
  fixes t::"'s trans"
  assumes st: "\<And>P. sound P \<Longrightarrow> sound (t P)"
      and mt: "mono_trans t"
      and fR: "t R \<tturnstile> R" and sR: "sound R"
  shows "t (lfp_exp t) \<le> lfp_exp t"
proof(rule lfp_exp_greatest[of t, OF _ _ fR sR])
  from fR sR show "sound (t (lfp_exp t))" by(auto intro:lfp_exp_sound st)

  fix P::"'s expect"
  assume fP: "t P \<tturnstile> P" and sP: "sound P"
  hence "lfp_exp t \<tturnstile> P" by(rule lfp_exp_lowerbound)
  with fP sP have "t (lfp_exp t) \<tturnstile> t P" by(auto intro:mono_transD[OF mt] lfp_exp_sound)
  also note fP
  finally show "t (lfp_exp t) \<tturnstile> P" .
qed

lemma lfp_exp_lemma3:
  assumes st: "\<And>P. sound P \<Longrightarrow> sound (t P)"
      and mt: "mono_trans t"
      and fR: "t R \<tturnstile> R" and sR: "sound R"
  shows "lfp_exp t \<le> t (lfp_exp t)"
  by(iprover intro:lfp_exp_lowerbound lfp_exp_sound lfp_exp_lemma2 assms
                   mono_transD[OF mt])

lemma lfp_exp_unfold:
  assumes nt: "\<And>P. sound P \<Longrightarrow> sound (t P)"
      and mt: "mono_trans t"
      and fR: "t R \<tturnstile> R" and sR: "sound R"
  shows "lfp_exp t = t (lfp_exp t)"
  by(iprover intro:antisym lfp_exp_lemma2 lfp_exp_lemma3 assms)

definition gfp_exp :: "'s trans \<Rightarrow> 's expect"
where "gfp_exp t = Sup_exp {P. unitary P \<and> P \<le> t P}"

lemma gfp_exp_upperbound:
  "\<lbrakk> P \<le> t P; unitary P \<rbrakk> \<Longrightarrow> P \<le> gfp_exp t"
  by(auto simp:gfp_exp_def intro:Sup_exp_upper)

lemma gfp_exp_least:
  "\<lbrakk> \<And>P. \<lbrakk> P \<le> t P; unitary P \<rbrakk> \<Longrightarrow> P \<le> Q; unitary Q \<rbrakk> \<Longrightarrow> gfp_exp t \<le> Q"
  unfolding gfp_exp_def by(auto intro:Sup_exp_least)

lemma gfp_exp_bound:
  "(\<And>P. unitary P \<Longrightarrow> unitary (t P)) \<Longrightarrow> bounded_by 1 (gfp_exp t)"
  unfolding gfp_exp_def
  by(rule bounded_byI2[OF Sup_exp_least], auto)

lemma gfp_exp_nneg[iff]:
  "nneg (gfp_exp t)"
proof(intro nnegI2, simp add:gfp_exp_def, cases)
  assume empty: "{P. unitary P \<and> P \<tturnstile> t P} = {}"
  show "\<lambda>s. 0 \<tturnstile> Sup_exp {P. unitary P \<and> P \<tturnstile> t P}"
    by(simp only:empty Sup_exp_def, auto)
next
  assume "{P. unitary P \<and> P \<tturnstile> t P} \<noteq> {}"
  then obtain Q where Qin: "Q \<in> {P. unitary P \<and> P \<tturnstile> t P}" by(auto)
  hence "\<lambda>s. 0 \<tturnstile> Q" by(auto)
  also from Qin have "Q \<tturnstile> Sup_exp {P. unitary P \<and> P \<tturnstile> t P}"
    by(auto intro:Sup_exp_upper)
  finally show "\<lambda>s. 0 \<tturnstile> Sup_exp {P. unitary P \<and> P \<tturnstile> t P}" .
qed

lemma gfp_exp_unitary:
  "(\<And>P. unitary P \<Longrightarrow> unitary (t P)) \<Longrightarrow> unitary (gfp_exp t)"
  by(iprover intro:gfp_exp_nneg gfp_exp_bound unitaryI2)

lemma gfp_exp_lemma2:
  assumes ft: "\<And>P. unitary P \<Longrightarrow> unitary (t P)"
      and mt: "\<And>P Q. \<lbrakk> unitary P; unitary Q; P \<tturnstile> Q \<rbrakk> \<Longrightarrow> t P \<tturnstile> t Q"
  shows "gfp_exp t \<le> t (gfp_exp t)"
proof(rule gfp_exp_least)
  show "unitary (t (gfp_exp t))" by(auto intro:gfp_exp_unitary ft)
  fix P
  assume fp: "P \<le> t P" and uP: "unitary P"
  with ft have "P \<le> gfp_exp t" by(auto intro:gfp_exp_upperbound)
  with uP gfp_exp_unitary ft
  have "t P \<le> t (gfp_exp t)" by(blast intro: mt)
  with fp show "P \<le> t (gfp_exp t)" by(auto)
qed

lemma gfp_exp_lemma3:
  assumes ft: "\<And>P. unitary P \<Longrightarrow> unitary (t P)"
      and mt: "\<And>P Q. \<lbrakk> unitary P; unitary Q; P \<tturnstile> Q \<rbrakk> \<Longrightarrow> t P \<tturnstile> t Q"
  shows "t (gfp_exp t) \<le> gfp_exp t"
  by(iprover intro:gfp_exp_upperbound unitary_sound
                   gfp_exp_unitary gfp_exp_lemma2 assms)

lemma gfp_exp_unfold:
  "(\<And>P. unitary P \<Longrightarrow> unitary (t P)) \<Longrightarrow> (\<And>P Q. \<lbrakk> unitary P; unitary Q; P \<tturnstile> Q \<rbrakk> \<Longrightarrow> t P \<tturnstile> t Q) \<Longrightarrow>
   gfp_exp t = t (gfp_exp t)"
  by(iprover intro:antisym gfp_exp_lemma2 gfp_exp_lemma3)

subsection \<open>The Lattice of Transformers\<close>

text_raw \<open>\label{s:trans_induct}\<close>

text \<open>In addition to fixed points on expectations, we also need
to reason about fixed points on expectation transformers.  The
interpretation of a recursive program in pGCL is as a fixed
point of a function from transformers to transformers.  In contrast
to the case of expectations, \emph{healthy} transformers do form
a complete lattice, where the bottom element is @{term "\<lambda>_. (\<lambda>_. 0)"},
and the top element is the greatest allowed by feasibility:
@{term "\<lambda>P. (\<lambda>_. bound_of P)"}.\<close>

definition Inf_trans :: "'s trans set \<Rightarrow> 's trans"
where "Inf_trans S = (\<lambda>P. Inf_exp {t P |t. t \<in> S})"

lemma Inf_trans_lower:
  "\<lbrakk> t \<in> S; \<forall>u\<in>S. \<forall>P. sound P \<longrightarrow> sound (u P) \<rbrakk> \<Longrightarrow> le_trans (Inf_trans S) t"
  unfolding Inf_trans_def
  by(rule le_transI[OF Inf_exp_lower], blast+)

lemma Inf_trans_greatest:
  "\<lbrakk> S \<noteq> {}; \<forall>t\<in>S. \<forall>P. le_trans u t \<rbrakk> \<Longrightarrow> le_trans u (Inf_trans S)"
  unfolding Inf_trans_def by(auto intro!:le_transI[OF Inf_exp_greatest])

definition Sup_trans :: "'s trans set \<Rightarrow> 's trans"
where "Sup_trans S = (\<lambda>P. Sup_exp {t P |t. t \<in> S})"

lemma Sup_trans_upper:
  "\<lbrakk> t \<in> S; \<forall>u\<in>S. \<forall>P. unitary P \<longrightarrow> unitary (u P) \<rbrakk> \<Longrightarrow> le_utrans t (Sup_trans S)"
  unfolding Sup_trans_def
  by(intro le_utransI[OF Sup_exp_upper], auto intro:unitary_bound)

lemma Sup_trans_upper2:
  "\<lbrakk> t \<in> S; \<forall>u\<in>S. \<forall>P. (nneg P \<and> bounded_by b P) \<longrightarrow> (nneg (u P) \<and> bounded_by b (u P));
     nneg P; bounded_by b P \<rbrakk> \<Longrightarrow> t P \<tturnstile> Sup_trans S P"
  unfolding Sup_trans_def by(blast intro:Sup_exp_upper)

lemma Sup_trans_least:
  "\<lbrakk> \<forall>t\<in>S. le_utrans t u; \<And>P. unitary P \<Longrightarrow> unitary (u P) \<rbrakk> \<Longrightarrow> le_utrans (Sup_trans S) u"
  unfolding Sup_trans_def
  by(auto intro!:sound_nneg[OF unitary_sound] le_utransI[OF Sup_exp_least])

lemma Sup_trans_least2:
  "\<lbrakk> \<forall>t\<in>S. \<forall>P. nneg P \<longrightarrow> bounded_by b P \<longrightarrow> t P \<tturnstile> u P;
     \<forall>u\<in>S. \<forall>P. (nneg P \<and> bounded_by b P) \<longrightarrow> (nneg (u P) \<and> bounded_by b (u P));
     nneg P; bounded_by b P; \<And>P. \<lbrakk> nneg P; bounded_by b P \<rbrakk> \<Longrightarrow> nneg (u P) \<rbrakk> \<Longrightarrow> Sup_trans S P \<tturnstile> u P"
   unfolding Sup_trans_def by(blast intro!:Sup_exp_least)

lemma feasible_Sup_trans:
  fixes S::"'s trans set"
  assumes fS: "\<forall>t\<in>S. feasible t"
  shows "feasible (Sup_trans S)"
proof(cases "S={}", simp add:Sup_trans_def Sup_exp_def, blast, intro feasibleI)
  fix b::real and P::"'s expect"
  assume bP: "bounded_by b P" and nP: "nneg P"
     and neS: "S \<noteq> {}"

  from neS obtain t where tin: "t \<in> S" by(auto)
  with fS have ft: "feasible t" by(auto)
  with bP nP have "\<lambda>s. 0 \<tturnstile> t P" by(auto)
  also {
    from bP nP have "sound P" by(auto)
    with tin fS have "t P \<tturnstile> Sup_trans S P"
      by(auto intro!:Sup_trans_upper2)
  }
  finally show "nneg (Sup_trans S P)" by(auto)

  from fS bP nP
  show "bounded_by b (Sup_trans S P)"
    by(auto intro!:bounded_byI2[OF Sup_trans_least2])
qed

definition lfp_trans :: "('s trans \<Rightarrow> 's trans) \<Rightarrow> 's trans"
where "lfp_trans T = Inf_trans {t. (\<forall>P. sound P \<longrightarrow> sound (t P)) \<and> le_trans (T t) t}"

lemma lfp_trans_lowerbound:
  "\<lbrakk> le_trans (T t) t; \<And>P. sound P \<Longrightarrow> sound (t P) \<rbrakk> \<Longrightarrow> le_trans (lfp_trans T) t"
  unfolding lfp_trans_def
  by(auto intro:Inf_trans_lower)

lemma lfp_trans_greatest:
  "\<lbrakk> \<And>t P. \<lbrakk> le_trans (T t) t; \<And>P. sound P \<Longrightarrow> sound (t P) \<rbrakk> \<Longrightarrow> le_trans u t;
     \<And>P. sound P \<Longrightarrow> sound (v P); le_trans (T v) v \<rbrakk> \<Longrightarrow>
   le_trans u (lfp_trans T)"
  unfolding lfp_trans_def by(rule Inf_trans_greatest, auto)

lemma lfp_trans_sound:
  fixes P Q::"'s expect"
  assumes sP: "sound P"
      and fv: "le_trans (T v) v"
      and sv: "\<And>P. sound P \<Longrightarrow> sound (v P)"
  shows  "sound (lfp_trans T P)"
proof(intro soundI2 bounded_byI2 nnegI2)
  from fv sv have "le_trans (lfp_trans T) v"
    by(iprover intro:lfp_trans_lowerbound)
  with sP have "lfp_trans T P \<tturnstile> v P" by(auto)
  also {
    from sv sP have "sound (v P)" by(iprover)
    hence "v P \<tturnstile> \<lambda>s. bound_of (v P)" by(auto)
  }
  finally show "lfp_trans T P \<tturnstile> \<lambda>s. bound_of (v P)" .

  have "le_trans (\<lambda>P s. 0) (lfp_trans T)"
  proof(intro lfp_trans_greatest)
    fix t::"'s trans"
    assume "\<And>P. sound P \<Longrightarrow> sound (t P)"
    hence "\<And>P. sound P \<Longrightarrow> \<lambda>s. 0 \<tturnstile> t P" by(auto)
    thus "le_trans (\<lambda>P s. 0) t" by(auto)
  next
    fix P::"'s expect"
    assume "sound P" thus "sound (v P)" by(rule sv)
  next
    show "le_trans (T v) v" by(rule fv)
  qed
  with sP show "\<lambda>s. 0 \<tturnstile> lfp_trans T P" by(auto)
qed

lemma lfp_trans_unitary:
  fixes P Q::"'s expect"
  assumes uP: "unitary P"
      and fv: "le_trans (T v) v"
      and sv: "\<And>P. sound P \<Longrightarrow> sound (v P)"
      and fT: "le_trans (T (\<lambda>P s. bound_of P)) (\<lambda>P s. bound_of P)"
  shows  "unitary (lfp_trans T P)"
proof(rule unitaryI)
  from unitary_sound[OF uP] fv sv show "sound (lfp_trans T P)"
    by(rule lfp_trans_sound)

  show "bounded_by 1 (lfp_trans T P)"
  proof(rule bounded_byI2)
    from fT have "le_trans (lfp_trans T) (\<lambda>P s. bound_of P)"
      by(auto intro: lfp_trans_lowerbound)
    with uP have "lfp_trans T P \<tturnstile> \<lambda>s. bound_of P" by(auto)
    also from uP have "... \<tturnstile> \<lambda>s. 1" by(auto)
    finally show "lfp_trans T P \<tturnstile> \<lambda>s. 1" .
  qed
qed

lemma lfp_trans_lemma2:
  fixes v::"'s trans"
  assumes mono: "\<And>t u. \<lbrakk> le_trans t u; \<And>P. sound P \<Longrightarrow> sound (t P);
                         \<And>P. sound P \<Longrightarrow> sound (u P) \<rbrakk> \<Longrightarrow> le_trans (T t) (T u)"
      and nT:   "\<And>t P. \<lbrakk> \<And>Q. sound Q \<Longrightarrow> sound (t Q); sound P \<rbrakk> \<Longrightarrow> sound (T t P)"
      and fv:   "le_trans (T v) v"
      and sv:   "\<And>P. sound P \<Longrightarrow> sound (v P)"
  shows "le_trans (T (lfp_trans T)) (lfp_trans T)"
proof(rule lfp_trans_greatest[where T=T and v=v], simp_all add:assms)
  fix t::"'s trans" and P::"'s expect"
  assume ft: "le_trans (T t) t" and st: "\<And>P. sound P \<Longrightarrow> sound (t P)"
  hence "le_trans (lfp_trans T) t" by(auto intro!:lfp_trans_lowerbound)
  with ft st have "le_trans (T (lfp_trans T)) (T t)"
    by(iprover intro:mono lfp_trans_sound fv sv)
  also note ft
  finally show "le_trans (T (lfp_trans T)) t" .
qed

lemma lfp_trans_lemma3:
  fixes v::"'s trans"
  assumes mono: "\<And>t u. \<lbrakk> le_trans t u; \<And>P. sound P \<Longrightarrow> sound (t P);
                         \<And>P. sound P \<Longrightarrow> sound (u P) \<rbrakk> \<Longrightarrow> le_trans (T t) (T u)"
      and sT:   "\<And>t P. \<lbrakk> \<And>Q. sound Q \<Longrightarrow> sound (t Q); sound P \<rbrakk> \<Longrightarrow> sound (T t P)"
      and fv:   "le_trans (T v) v"
      and sv:   "\<And>P. sound P \<Longrightarrow> sound (v P)"
  shows "le_trans (lfp_trans T) (T (lfp_trans T))"
proof(rule lfp_trans_lowerbound)
  fix P::"'s expect"
  assume sP: "sound P"
  have n1: "\<And>P. sound P \<Longrightarrow> sound (lfp_trans T P)"
    by(iprover intro:lfp_trans_sound fv sv)
  with sP have n2: "sound (lfp_trans T P)"
    by(iprover intro:lfp_trans_sound fv sv sT)
  with n1 sP show n3: "sound (T (lfp_trans T) P)"
    by(iprover intro: sT)
  next
  show "le_trans (T (T (lfp_trans T))) (T (lfp_trans T))"
    by(rule mono[OF lfp_trans_lemma2, OF mono],
            (iprover intro:assms lfp_trans_sound)+)
qed

lemma lfp_trans_unfold:
  fixes P::"'s expect"
  assumes mono: "\<And>t u. \<lbrakk> le_trans t u; \<And>P. sound P \<Longrightarrow> sound (t P);
                         \<And>P. sound P \<Longrightarrow> sound (u P) \<rbrakk> \<Longrightarrow> le_trans (T t) (T u)"
      and sT:   "\<And>t P. \<lbrakk> \<And>Q. sound Q \<Longrightarrow> sound (t Q); sound P \<rbrakk> \<Longrightarrow> sound (T t P)"
      and fv:   "le_trans (T v) v"
      and sv:   "\<And>P. sound P \<Longrightarrow> sound (v P)"
  shows "equiv_trans (lfp_trans T) (T (lfp_trans T))"
  by(rule le_trans_antisym,
     rule lfp_trans_lemma3[OF mono], (iprover intro:assms)+,
     rule lfp_trans_lemma2[OF mono], (iprover intro:assms)+)

definition gfp_trans :: "('s trans \<Rightarrow> 's trans) \<Rightarrow> 's trans"
where "gfp_trans T = Sup_trans {t. (\<forall>P. unitary P \<longrightarrow> unitary (t P)) \<and> le_utrans t (T t)}"

lemma gfp_trans_upperbound:
  "\<lbrakk> le_utrans t (T t); \<And>P. unitary P \<Longrightarrow> unitary (t P) \<rbrakk> \<Longrightarrow> le_utrans t (gfp_trans T)"
  unfolding gfp_trans_def by(auto intro:Sup_trans_upper)

lemma gfp_trans_least:
  "\<lbrakk> \<And>t. \<lbrakk> le_utrans t (T t); \<And>P. unitary P \<Longrightarrow> unitary (t P) \<rbrakk> \<Longrightarrow> le_utrans t u;
     \<And>P. unitary P \<Longrightarrow> unitary (u P) \<rbrakk> \<Longrightarrow>
   le_utrans (gfp_trans T) u"
  unfolding gfp_trans_def by(auto intro:Sup_trans_least)

lemma gfp_trans_unitary:
  fixes P::"'s expect"
  assumes uP: "unitary P"
  shows "unitary (gfp_trans T P)"
proof(intro unitaryI2 nnegI2 bounded_byI2)
  show "gfp_trans T P \<tturnstile> \<lambda>s. 1"
  unfolding gfp_trans_def Sup_trans_def
  proof(rule Sup_exp_least, clarify)
    fix t::"'s trans"
    assume "\<forall>P. unitary P \<longrightarrow> unitary (t P)"
    with uP have "unitary (t P)" by(auto)
    thus "t P \<tturnstile> \<lambda>s. 1" by(auto)
  next
    show "nneg (\<lambda>s. 1::real)" by(auto)
  qed
  let ?S = "{t P |t. t \<in> {t. (\<forall>P. unitary P \<longrightarrow> unitary (t P)) \<and> le_utrans t (T t)}}"
  show "\<lambda>s. 0 \<tturnstile> gfp_trans T P"
  unfolding gfp_trans_def Sup_trans_def
  proof(cases)
    assume empty: "?S = {}"
    show "\<lambda>s. 0 \<tturnstile> Sup_exp ?S"
      by(simp only:empty Sup_exp_def, auto)
  next
    assume "?S \<noteq> {}"
    then obtain Q where Qin: "Q \<in> ?S" by(auto)
    with uP have "unitary Q" by(auto)
    hence "\<lambda>s. 0 \<tturnstile> Q" by(auto)
    also with uP Qin have "Q \<tturnstile> Sup_exp ?S"
    proof(intro Sup_exp_upper, blast, clarify)
      fix t::"'s trans"
      assume "\<forall>Q. unitary Q \<longrightarrow> unitary (t Q)"
      with uP show "bounded_by 1 (t P)" by(auto)
    qed
    finally show "\<lambda>s. 0 \<tturnstile> Sup_exp ?S" .
  qed
qed

lemma gfp_trans_lemma2:
  assumes mono: "\<And>t u. \<lbrakk> le_utrans t u; \<And>P. unitary P \<Longrightarrow> unitary (t P);
                         \<And>P. unitary P \<Longrightarrow> unitary (u P) \<rbrakk> \<Longrightarrow> le_utrans (T t) (T u)"
      and hT:   "\<And>t P. \<lbrakk> \<And>Q. unitary Q \<Longrightarrow> unitary (t Q); unitary P \<rbrakk> \<Longrightarrow> unitary (T t P)"
  shows "le_utrans (gfp_trans T) (T (gfp_trans T))"
proof(rule gfp_trans_least, simp_all add:hT gfp_trans_unitary)
  fix t
  assume fp: "le_utrans t (T t)" and ht: "\<And>P. unitary P \<Longrightarrow> unitary (t P)"

  note fp
  also {
    from fp ht have "le_utrans t (gfp_trans T)"by(rule gfp_trans_upperbound)
    moreover note ht gfp_trans_unitary
    ultimately have "le_utrans (T t) (T (gfp_trans T))" by(rule mono)
  }
  finally show "le_utrans t (T (gfp_trans T))" .
qed

lemma gfp_trans_lemma3:
  assumes mono: "\<And>t u. \<lbrakk> le_utrans t u; \<And>P. unitary P \<Longrightarrow> unitary (t P);
                         \<And>P. unitary P \<Longrightarrow> unitary (u P) \<rbrakk> \<Longrightarrow> le_utrans (T t) (T u)"
      and hT:   "\<And>t P. \<lbrakk> \<And>Q. unitary Q \<Longrightarrow> unitary (t Q); unitary P \<rbrakk> \<Longrightarrow> unitary (T t P)"
  shows "le_utrans (T (gfp_trans T)) (gfp_trans T)"
  by(blast intro!:mono gfp_trans_unitary gfp_trans_upperbound gfp_trans_lemma2 mono hT)

lemma gfp_trans_unfold:
  assumes mono: "\<And>t u. \<lbrakk> le_utrans t u; \<And>P. unitary P \<Longrightarrow> unitary (t P);
                         \<And>P. unitary P \<Longrightarrow> unitary (u P) \<rbrakk> \<Longrightarrow> le_utrans (T t) (T u)"
      and hT:   "\<And>t P. \<lbrakk> \<And>Q. unitary Q \<Longrightarrow> unitary (t Q); unitary P \<rbrakk> \<Longrightarrow> unitary (T t P)"
  shows "equiv_utrans (gfp_trans T) (T (gfp_trans T))"
  using assms by(auto intro!: le_utrans_antisym gfp_trans_lemma2 gfp_trans_lemma3)

subsection \<open>Tail Recursion\<close>

text_raw \<open>\label{s:tail}\<close>

text \<open>The least (greatest) fixed point of a tail-recursive expression on transformers is
equivalent (given appropriate side conditions) to the least (greatest) fixed point on
expectations.\<close>

lemma gfp_pulldown:
  fixes P::"'s expect"
  assumes tailcall:  "\<And>u P. unitary P \<Longrightarrow> T u P = t P (u P)"
      and fT:        "\<And>t P. \<lbrakk> \<And>Q. unitary Q \<Longrightarrow> unitary (t Q); unitary P \<rbrakk> \<Longrightarrow> unitary (T t P)"
      and ft:        "\<And>P Q. unitary P \<Longrightarrow> unitary Q \<Longrightarrow> unitary (t P Q)"
      and mt:        "\<And>P Q R. \<lbrakk> unitary P; unitary Q; unitary R; Q \<tturnstile> R \<rbrakk> \<Longrightarrow> t P Q \<tturnstile> t P R"
      and uP:        "unitary P"
      and monoT:     "\<And>t u. \<lbrakk> le_utrans t u; \<And>P. unitary P \<Longrightarrow> unitary (t P);
                              \<And>P. unitary P \<Longrightarrow> unitary (u P) \<rbrakk> \<Longrightarrow> le_utrans (T t) (T u)"
  shows "gfp_trans T P = gfp_exp (t P)" (is "?X P = ?Y P")
proof(rule antisym)
  show "?X P \<le> ?Y P"
  proof(rule gfp_exp_upperbound)
    from monoT fT uP have "(gfp_trans T) P \<le> (T (gfp_trans T)) P"
      by(auto intro!: le_utransD[OF gfp_trans_lemma2])
    also from uP have "(T (gfp_trans T)) P = t P (gfp_trans T P)" by(rule tailcall)
    finally show "gfp_trans T P \<tturnstile> t P (gfp_trans T P)" .
    from uP gfp_trans_unitary show "unitary (gfp_trans T P)" by(auto)
  qed
  show "?Y P \<le> ?X P"
  proof(rule le_utransD[OF gfp_trans_upperbound], simp_all add:assms)
    show "le_utrans (\<lambda>a. gfp_exp (t a)) (T (\<lambda>a. gfp_exp (t a)))"
    proof(rule le_utransI)
      fix Q::"'s expect" assume uQ: "unitary Q"
      with ft have "\<And>R. unitary R \<Longrightarrow> unitary (t Q R)" by(auto)
      with mt[OF uQ] have "gfp_exp (t Q) = t Q (gfp_exp (t Q))" by(blast intro:gfp_exp_unfold)
      also from uQ have "... = T (\<lambda>a. gfp_exp (t a)) Q" by(rule tailcall[symmetric])
      finally show "gfp_exp (t Q) \<le> T (\<lambda>a. gfp_exp (t a)) Q" by(simp)
    qed
    fix Q::"'s expect" assume "unitary Q"
    with ft have "\<And>R. unitary R \<Longrightarrow> unitary (t Q R)" by(auto)
    thus "unitary (gfp_exp (t Q))" by(rule gfp_exp_unitary)
  qed
qed

lemma lfp_pulldown:
  fixes P::"'s expect" and t::"'s expect \<Rightarrow> 's trans"
    and T::"'s trans \<Rightarrow> 's trans"
  assumes tailcall:  "\<And>u P. sound P \<Longrightarrow> T u P = t P (u P)"
      and st:        "\<And>P Q. sound P \<Longrightarrow> sound Q \<Longrightarrow> sound (t P Q)"
      and mt:        "\<And>P. sound P \<Longrightarrow> mono_trans (t P)"
      and monoT: "\<And>t u. \<lbrakk> le_trans t u; \<And>P. sound P \<Longrightarrow> sound (t P);
                          \<And>P. sound P \<Longrightarrow> sound (u P) \<rbrakk> \<Longrightarrow> le_trans (T t) (T u)"
      and nT:   "\<And>t P. \<lbrakk> \<And>Q. sound Q \<Longrightarrow> sound (t Q); sound P \<rbrakk> \<Longrightarrow> sound (T t P)"
      and fv:   "le_trans (T v) v"
      and sv:   "\<And>P. sound P \<Longrightarrow> sound (v P)"
      and sP:   "sound P"
  shows "lfp_trans T P = lfp_exp (t P)" (is "?X P = ?Y P")
proof(rule antisym)
  show "?Y P \<le> ?X P"
  proof(rule lfp_exp_lowerbound)
    from sP have "t P (lfp_trans T P) = (T (lfp_trans T)) P" by(rule tailcall[symmetric])
    also have "(T (lfp_trans T)) P \<le> (lfp_trans T) P"
      by(rule le_transD[OF lfp_trans_lemma2[OF monoT]], (iprover intro:assms)+)
    finally show "t P (lfp_trans T P) \<le> lfp_trans T P" .
    from sP show "sound (lfp_trans T P)"
      by(iprover intro:lfp_trans_sound assms)
  qed

  have "\<And>P. sound P \<Longrightarrow> t P (v P) = T v P" by(simp add:tailcall)
  also have "\<And>P. sound P \<Longrightarrow> ... P \<tturnstile> v P" by(auto intro:le_transD[OF fv])
  finally have fvP: "\<And>P. sound P \<Longrightarrow> t P (v P) \<tturnstile> v P" .
  have svP: "\<And>P. sound P \<Longrightarrow> sound (v P)" by(rule sv)

  show "?X P \<le> ?Y P"
  proof(rule le_transD[OF lfp_trans_lowerbound, OF _ _ sP])
    show "le_trans (T (\<lambda>a. lfp_exp (t a))) (\<lambda>a. lfp_exp (t a))"
    proof(rule le_transI)
      fix P::"'s expect"
      assume sP: "sound P"

      from sP have "T (\<lambda>a. lfp_exp (t a)) P = t P (lfp_exp (t P))" by(rule tailcall)
      also have "t P (lfp_exp (t P)) = lfp_exp (t P)"
        by(iprover intro: lfp_exp_unfold[symmetric] sP st mt fvP svP)
      finally show "T (\<lambda>a. lfp_exp (t a)) P \<tturnstile> lfp_exp (t P)" by(simp)
    qed
    fix P::"'s expect"
    assume "sound P"
    with fvP svP show "sound (lfp_exp (t P))"
      by(blast intro:lfp_exp_sound)
  qed
qed

definition Inf_utrans :: "'s trans set \<Rightarrow> 's trans"
where "Inf_utrans S = (if S = {} then \<lambda>P s. 1 else Inf_trans S)"

lemma Inf_utrans_lower:
  "\<lbrakk> t \<in> S; \<forall>t\<in>S. \<forall>P. unitary P \<longrightarrow> unitary (t P) \<rbrakk> \<Longrightarrow> le_utrans (Inf_utrans S) t"
  unfolding Inf_utrans_def
  by(cases "S={}",
     auto intro!:le_utransI Inf_exp_lower sound_nneg unitary_sound
          simp:Inf_trans_def)

lemma Inf_utrans_greatest:
  "\<lbrakk> \<And>P. unitary P \<Longrightarrow> unitary (t P); \<forall>u\<in>S. le_utrans t u \<rbrakk> \<Longrightarrow> le_utrans t (Inf_utrans S)"
  unfolding Inf_utrans_def Inf_trans_def
  by(cases "S={}", simp_all, (blast intro!:le_utransI Inf_exp_greatest)+)

end
