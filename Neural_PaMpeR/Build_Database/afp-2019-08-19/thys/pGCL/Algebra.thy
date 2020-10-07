(*
 * Copyright (C) 2014 NICTA
 * All rights reserved.
 *)

(* Author: David Cock - David.Cock@nicta.com.au *)

section "The Algebra of pGCL"

theory Algebra imports WellDefined begin

text_raw \<open>\label{s:Algebra}\<close>

text \<open>Programs in pGCL have a rich algebraic structure, largely mirroring that for GCL. We show
that programs form a lattice under refinement, with @{term "a \<Sqinter> b"} and @{term "a \<Squnion> b"} as the meet
and join operators, respectively. We also take advantage of the algebraic structure to establish a
framwork for the modular decomposition of proofs.\<close>

subsection \<open>Program Refinement\<close>

text_raw \<open>\label{s:progref}\<close>

text \<open>Refinement in pGCL relates to refinement in GCL exactly as probabilistic entailment relates
to implication. It turns out to have a very similar algebra, the rules of which we establish
shortly.\<close>

definition
  refines :: "'s prog \<Rightarrow> 's prog \<Rightarrow> bool" (infix "\<sqsubseteq>" 70)
where
  "prog \<sqsubseteq> prog' \<equiv> \<forall>P. sound P \<longrightarrow> wp prog P \<tturnstile> wp prog' P"

lemma refinesI[intro]:
  "\<lbrakk> \<And>P. sound P \<Longrightarrow> wp prog P \<tturnstile> wp prog' P \<rbrakk> \<Longrightarrow> prog \<sqsubseteq> prog'"
  unfolding refines_def by(simp)

lemma refinesD[dest]:
  "\<lbrakk> prog \<sqsubseteq> prog'; sound P \<rbrakk> \<Longrightarrow> wp prog P \<tturnstile> wp prog' P"
  unfolding refines_def by(simp)

text \<open>The equivalence relation below will turn out to be that induced by refinement. It is also
the application of @{term equiv_trans} to the weakest precondition.\<close>

definition
  pequiv :: "'s prog \<Rightarrow> 's prog \<Rightarrow> bool" (infix "\<simeq>" 70)
where
  "prog \<simeq> prog' \<equiv> \<forall>P. sound P \<longrightarrow> wp prog P = wp prog' P"

lemma pequivI[intro]:
  "\<lbrakk> \<And>P. sound P \<Longrightarrow> wp prog P = wp prog' P \<rbrakk> \<Longrightarrow> prog \<simeq> prog'"
  unfolding pequiv_def by(simp)

lemma pequivD[dest,simp]:
  "\<lbrakk> prog \<simeq> prog'; sound P \<rbrakk> \<Longrightarrow> wp prog P = wp prog' P"
  unfolding pequiv_def by(simp)

lemma pequiv_equiv_trans:
  "a \<simeq> b \<longleftrightarrow> equiv_trans (wp a) (wp b)"
  by(auto)

subsection \<open>Simple Identities\<close>

text \<open>The following identities involve only the primitive operations as defined in
\autoref{s:syntax}, and refinement as defined above.\<close>

subsubsection \<open>Laws following from the basic arithmetic of the operators seperately\<close>

lemma DC_comm[ac_simps]:
  "a \<Sqinter> b = b \<Sqinter> a"
  unfolding DC_def by(simp add:ac_simps)

lemma DC_assoc[ac_simps]:
  "a \<Sqinter> (b \<Sqinter> c) = (a \<Sqinter> b) \<Sqinter> c"
  unfolding DC_def by(simp add:ac_simps)

lemma DC_idem:
  "a \<Sqinter> a = a"
  unfolding DC_def by(simp)

lemma AC_comm[ac_simps]:
  "a \<Squnion> b = b \<Squnion> a"
  unfolding AC_def by(simp add:ac_simps)

lemma AC_assoc[ac_simps]:
  "a \<Squnion> (b \<Squnion> c) = (a \<Squnion> b) \<Squnion> c"
  unfolding AC_def by(simp add:ac_simps)

lemma AC_idem:
  "a \<Squnion> a = a"
  unfolding AC_def by(simp)

lemma PC_quasi_comm:
  "a \<^bsub>p\<^esub>\<oplus> b = b \<^bsub>(\<lambda>s. 1 - p s)\<^esub>\<oplus> a"
  unfolding PC_def by(simp add:algebra_simps)

lemma PC_idem:
  "a \<^bsub>p\<^esub>\<oplus> a = a"
  unfolding PC_def by(simp add:algebra_simps)

lemma Seq_assoc[ac_simps]:
  "A ;; (B ;; C) = A ;; B ;; C"
  by(simp add:Seq_def o_def)

lemma Abort_refines[intro]:
  "well_def a \<Longrightarrow> Abort \<sqsubseteq> a"
  by(rule refinesI, unfold wp_eval, auto dest!:well_def_wp_healthy)

subsubsection \<open>Laws relating demonic choice and refinement\<close>

lemma left_refines_DC:
  "(a \<Sqinter> b) \<sqsubseteq> a"
  by(auto intro!:refinesI simp:wp_eval)

lemma right_refines_DC:
  "(a \<Sqinter> b) \<sqsubseteq> b"
  by(auto intro!:refinesI simp:wp_eval)

lemma DC_refines:
  fixes a::"'s prog" and b and c
  assumes rab: "a \<sqsubseteq> b" and rac: "a \<sqsubseteq> c"
  shows "a \<sqsubseteq> (b \<Sqinter> c)"
proof
  fix P::"'s \<Rightarrow> real" assume sP: "sound P"
  with assms have "wp a P \<tturnstile> wp b P" and "wp a P \<tturnstile> wp c P"
    by(auto dest:refinesD)
  thus "wp a P \<tturnstile> wp (b \<Sqinter> c) P"
    by(auto simp:wp_eval intro:min.boundedI)
qed

lemma DC_mono:
  fixes a::"'s prog"
  assumes rab: "a \<sqsubseteq> b" and rcd: "c \<sqsubseteq> d"
  shows "(a \<Sqinter> c) \<sqsubseteq> (b \<Sqinter> d)"
proof(rule refinesI, unfold wp_eval, rule le_funI)
  fix P::"'s \<Rightarrow> real" and s::'s
  assume sP: "sound P"
  with assms have "wp a P s \<le> wp b P s" and "wp c P s \<le> wp d P s"
    by(auto)
  thus "min (wp a P s) (wp c P s) \<le> min (wp b P s) (wp d P s)"
    by(auto)
qed

subsubsection \<open>Laws relating angelic choice and refinement\<close>

lemma left_refines_AC:
  "a \<sqsubseteq> (a \<Squnion> b)"
  by(auto intro!:refinesI simp:wp_eval)

lemma right_refines_AC:
  "b \<sqsubseteq> (a \<Squnion> b)"
  by(auto intro!:refinesI simp:wp_eval)

lemma AC_refines:
  fixes a::"'s prog" and b and c
  assumes rac: "a \<sqsubseteq> c" and rbc: "b \<sqsubseteq> c"
  shows "(a \<Squnion> b) \<sqsubseteq> c"
proof
  fix P::"'s \<Rightarrow> real" assume sP: "sound P"
  with assms have "\<And>s. wp a P s \<le> wp c P s"
              and "\<And>s. wp b P s \<le> wp c P s"
    by(auto dest:refinesD)
  thus "wp (a \<Squnion> b) P \<tturnstile> wp c P"
    unfolding wp_eval by(auto)
qed

lemma AC_mono:
  fixes a::"'s prog"
  assumes rab: "a \<sqsubseteq> b" and rcd: "c \<sqsubseteq> d"
  shows "(a \<Squnion> c) \<sqsubseteq> (b \<Squnion> d)"
proof(rule refinesI, unfold wp_eval, rule le_funI)
  fix P::"'s \<Rightarrow> real" and s::'s
  assume sP: "sound P"
  with assms have "wp a P s \<le> wp b P s" and "wp c P s \<le> wp d P s"
    by(auto)
  thus "max (wp a P s) (wp c P s) \<le> max (wp b P s) (wp d P s)"
    by(auto)
qed

subsubsection \<open>Laws depending on the arithmetic of @{term "a \<^bsub>p\<^esub>\<oplus> b"} and @{term "a \<Sqinter> b"}
together\<close>

lemma DC_refines_PC:
  assumes unit: "unitary p"
  shows "(a \<Sqinter> b) \<sqsubseteq> (a \<^bsub>p\<^esub>\<oplus> b)"
proof(rule refinesI, unfold wp_eval, rule le_funI)
  fix s and P::"'a \<Rightarrow> real" assume sound: "sound P"
  from unit have nn_p: "0 \<le> p s" by(blast)
  from unit have "p s \<le> 1" by(blast)
  hence nn_np: "0 \<le> 1 - p s" by(simp)
  show "min (wp a P s) (wp b P s) \<le> p s * wp a P s + (1 - p s) * wp b P s"
  proof(cases "wp a P s \<le> wp b P s",
      simp_all add:min.absorb1 min.absorb2)
    case True note le = this
    have "wp a P s = (p s + (1 - p s)) * wp a P s" by(simp)
    also have "... = p s * wp a P s + (1 - p s) * wp a P s"
      by(simp only: distrib_right)
    also {
      from le and nn_np have "(1 - p s) * wp a P s \<le> (1 - p s) * wp b P s"
        by(rule mult_left_mono)
      hence "p s * wp a P s + (1 - p s) * wp a P s \<le>
        p s * wp a P s + (1 - p s) * wp b P s"
        by(rule add_left_mono)
    }
    finally show "wp a P s \<le> p s * wp a P s + (1 - p s) * wp b P s" .
  next
    case False
    then have le: "wp b P s \<le> wp a P s" by(simp)
    have "wp b P s = (p s + (1 - p s)) * wp b P s" by(simp)
    also have "... = p s * wp b P s + (1 - p s) * wp b P s"
      by(simp only:distrib_right)
    also {
      from le and nn_p have "p s * wp b P s \<le> p s * wp a P s"
        by(rule mult_left_mono)
      hence "p s * wp b P s + (1 - p s) * wp b P s \<le>
        p s * wp a P s + (1 - p s) * wp b P s"
        by(rule add_right_mono)
    }
    finally show "wp b P s \<le> p s * wp a P s + (1 - p s) * wp b P s" .
  qed
qed

subsubsection \<open>Laws depending on the arithmetic of @{term "a \<^bsub>p\<^esub>\<oplus> b"} and @{term "a \<Squnion> b"}
together\<close>

lemma PC_refines_AC:
  assumes unit: "unitary p"
  shows "(a \<^bsub>p\<^esub>\<oplus> b) \<sqsubseteq> (a \<Squnion> b)"
proof(rule refinesI, unfold wp_eval, rule le_funI)
  fix s and P::"'a \<Rightarrow> real" assume sound: "sound P"

  from unit have "p s \<le> 1" by(blast)
  hence nn_np: "0 \<le> 1 - p s" by(simp)

  show "p s * wp a P s + (1 - p s) * wp b P s \<le>
        max (wp a P s) (wp b P s)"
  proof(cases "wp a P s \<le> wp b P s")
    case True note leab = this
    with unit nn_np
    have "p s * wp a P s + (1 - p s) * wp b P s \<le>
          p s * wp b P s + (1 - p s) * wp b P s"
      by(auto intro:add_mono mult_left_mono)
    also have "... = wp b P s"
      by(auto simp:field_simps)
    also from leab
    have "... = max (wp a P s) (wp b P s)"
      by(auto)
    finally show ?thesis .
  next
    case False note leba = this
    with unit nn_np
    have "p s * wp a P s + (1 - p s) * wp b P s \<le>
          p s * wp a P s + (1 - p s) * wp a P s"
      by(auto intro:add_mono mult_left_mono)
    also have "... = wp a P s"
      by(auto simp:field_simps)
    also from leba
    have "... = max (wp a P s) (wp b P s)"
      by(auto)
    finally show ?thesis .
  qed
qed

subsubsection \<open>Laws depending on the arithmetic of @{term "a \<Squnion> b"} and @{term "a \<Sqinter> b"} together
\<close>

lemma DC_refines_AC:
  "(a \<Sqinter> b) \<sqsubseteq> (a \<Squnion> b)"
  by(auto intro!:refinesI simp:wp_eval)

subsubsection \<open>Laws Involving Refinement and Equivalence\<close>

lemma pr_trans[trans]:
  fixes A::"'a prog"
  assumes prAB: "A \<sqsubseteq> B"
      and prBC: "B \<sqsubseteq> C"
  shows "A \<sqsubseteq> C"
proof
  fix P::"'a \<Rightarrow> real" assume sP: "sound P"
  with prAB have "wp A P \<tturnstile> wp B P" by(blast)
  also from sP and prBC have "... \<tturnstile> wp C P" by(blast)
  finally show "wp A P \<tturnstile> ..." .
qed

lemma pequiv_refl[intro!,simp]:
  "a \<simeq> a"
  by(auto)

lemma pequiv_comm[ac_simps]:
  "a \<simeq> b \<longleftrightarrow> b \<simeq> a"
  unfolding pequiv_def
  by(rule iffI, safe, simp_all)

lemma pequiv_pr[dest]:
  "a \<simeq> b \<Longrightarrow> a \<sqsubseteq> b"
  by(auto)

lemma pequiv_trans[intro,trans]:
  "\<lbrakk> a \<simeq> b; b \<simeq> c \<rbrakk> \<Longrightarrow> a \<simeq> c"
  unfolding pequiv_def by(auto intro!:order_trans)

lemma pequiv_pr_trans[intro,trans]:
  "\<lbrakk> a \<simeq> b; b \<sqsubseteq> c \<rbrakk> \<Longrightarrow> a \<sqsubseteq> c"
  unfolding pequiv_def refines_def by(simp)

lemma pr_pequiv_trans[intro,trans]:
  "\<lbrakk> a \<sqsubseteq> b; b \<simeq> c \<rbrakk> \<Longrightarrow> a \<sqsubseteq> c"
  unfolding pequiv_def refines_def by(simp)

text \<open>Refinement induces equivalence by antisymmetry:\<close>
lemma pequiv_antisym:
  "\<lbrakk> a \<sqsubseteq> b; b \<sqsubseteq> a \<rbrakk> \<Longrightarrow> a \<simeq> b"
  by(auto intro:antisym)

lemma pequiv_DC:
  "\<lbrakk> a \<simeq> c; b \<simeq> d \<rbrakk> \<Longrightarrow> (a \<Sqinter> b) \<simeq> (c \<Sqinter> d)"
  by(auto intro!:DC_mono pequiv_antisym simp:ac_simps)

lemma pequiv_AC:
  "\<lbrakk> a \<simeq> c; b \<simeq> d \<rbrakk> \<Longrightarrow> (a \<Squnion> b) \<simeq> (c \<Squnion> d)"
  by(auto intro!:AC_mono pequiv_antisym simp:ac_simps)

subsection \<open>Deterministic Programs are Maximal\<close>

text \<open>Any sub-additive refinement of a deterministic program is in fact an equivalence.
Deterministic programs are thus maximal (under the refinement order) among sub-additive programs.
\<close>
lemma refines_determ:
  fixes a::"'s prog"
  assumes da: "determ (wp a)"
      and wa: "well_def a"
      and wb: "well_def b"
      and dr: "a \<sqsubseteq> b"
  shows "a \<simeq> b"
  txt \<open>Proof by contradiction.\<close>
proof(rule pequivI, rule contrapos_pp)
  from wb have "feasible (wp b)" by(auto)
  with wb have sab: "sub_add (wp b)"
    by(auto dest: sublinear_subadd[OF well_def_wp_sublinear])
  fix P::"'s \<Rightarrow> real" assume sP: "sound P"
  txt \<open>Assume that @{term a} and @{term b} are not equivalent:\<close>
  assume ne: "wp a P \<noteq> wp b P"
  txt \<open>Find a point at which they differ.  As @{term "a \<sqsubseteq> b"},
    @{term "wp b P s"} must by strictly greater than @{term "wp a P s"}
    here:\<close>
  hence "\<exists>s. wp a P s < wp b P s"
  proof(rule contrapos_np)
    assume "\<not>(\<exists>s. wp a P s < wp b P s)"
    hence "\<forall>s. wp b P s \<le> wp a P s" by(auto simp:not_less)
    hence "wp b P \<tturnstile> wp a P" by(auto)
    moreover from sP dr have "wp a P \<tturnstile> wp b P" by(auto)
    ultimately show "wp a P = wp b P" by(auto)
  qed
  then obtain s where less: "wp a P s < wp b P s" by(blast)
  txt \<open>Take a carefully constructed expectation:\<close>
  let ?Pc = "\<lambda>s. bound_of P - P s"
  have sPc: "sound ?Pc"
  proof(rule soundI)
    from sP have "\<And>s. 0 \<le> P s" by(auto)
    hence "\<And>s. ?Pc s \<le> bound_of P" by(auto)
    thus "bounded ?Pc" by(blast)
    from sP have "\<And>s. P s \<le> bound_of P" by(auto)
    hence "\<And>s. 0 \<le> ?Pc s" by(auto simp:sign_simps)
    thus "nneg ?Pc" by(auto)
  qed
  txt \<open>We then show that @{term "wp b"} violates feasibility, and
    thus healthiness.\<close>
  from sP have "0 \<le> bound_of P" by(auto)
  with da have "bound_of P = wp a (\<lambda>s. bound_of P) s"
    by(simp add:maximalD determ_maximalD)
  also have "... = wp a (\<lambda>s. ?Pc s + P s) s"
    by(simp)
  also from da sP sPc have "... = wp a ?Pc s + wp a P s"
    by(subst additiveD[OF determ_additiveD], simp_all add:sP sPc)
  also from sPc dr have "... \<le> wp b ?Pc s + wp a P s"
    by(auto)
  also from less have "... < wp b ?Pc s + wp b P s"
    by(auto)
  also from sab sP sPc have "... \<le> wp b (\<lambda>s. ?Pc s + P s) s"
    by(blast)
  finally have "\<not>wp b (\<lambda>s. bound_of P) s \<le> bound_of P"
    by(simp)
  thus "\<not>bounded_by (bound_of P) (wp b (\<lambda>s. bound_of P))"
    by(auto)
next  
  txt \<open>However,\<close>
  fix P::"'s \<Rightarrow> real" assume sP: "sound P"
  hence "nneg (\<lambda>s. bound_of P)" by(auto)
  moreover have "bounded_by (bound_of P) (\<lambda>s. bound_of P)" by(auto)
  ultimately
  show "bounded_by (bound_of P) (wp b (\<lambda>s. bound_of P))"
    using wb by(auto dest!:well_def_wp_healthy)
qed

subsection \<open>The Algebraic Structure of Refinement\<close>

text \<open>Well-defined programs form a half-bounded semilattice under refinement, where @{term Abort}
is bottom, and @{term "a \<Sqinter> b"} is @{term inf}. There is no unique top element, but all
fully-deterministic programs are maximal.

The type that we construct here is not especially useful, but serves as a convenient way to express
this result.\<close>

quotient_type 's program =
  "'s prog" / partial : "\<lambda>a b. a \<simeq> b \<and> well_def a \<and> well_def b"
proof(rule part_equivpI)
  have "Skip \<simeq> Skip" and "well_def Skip" by(auto intro:wd_intros)
  thus "\<exists>x. x \<simeq> x \<and> well_def x \<and> well_def x" by(blast)
  show "symp (\<lambda>a b. a \<simeq> b \<and> well_def a \<and> well_def b)"
  proof(rule sympI, safe)
    fix a::"'a prog" and b
    assume "a \<simeq> b"
    hence "equiv_trans (wp a) (wp b)"
      by(simp add:pequiv_equiv_trans)
    thus "b \<simeq> a" by(simp add:ac_simps pequiv_equiv_trans)
  qed
  show "transp (\<lambda>a b. a \<simeq> b \<and> well_def a \<and> well_def b)"
    by(rule transpI, safe, rule pequiv_trans)
qed

instantiation program :: (type) semilattice_inf begin
lift_definition
  less_eq_program :: "'a program \<Rightarrow> 'a program \<Rightarrow> bool" is refines
proof(safe)
  fix a::"'a prog" and b c d
  assume "a \<simeq> b" hence "b \<simeq> a" by(simp add:ac_simps)
  also assume "a \<sqsubseteq> c"
  also assume "c \<simeq> d"
  finally show "b \<sqsubseteq> d" .
next
  fix a::"'a prog" and b c d
  assume "a \<simeq> b"
  also assume "b \<sqsubseteq> d"
  also assume "c \<simeq> d" hence "d \<simeq> c" by(simp add:ac_simps)
  finally show "a \<sqsubseteq> c" .
qed (* XXX - what's up here? *)

lift_definition
  less_program :: "'a program \<Rightarrow> 'a program \<Rightarrow> bool"
  is "\<lambda>a b. a \<sqsubseteq> b \<and> \<not> b \<sqsubseteq> a"
proof(safe)
  fix a::"'a prog" and b c d
  assume "a \<simeq> b" hence "b \<simeq> a" by(simp add:ac_simps)
  also assume "a \<sqsubseteq> c"
  also assume "c \<simeq> d"
  finally show "b \<sqsubseteq> d" .
next
  fix a::"'a prog" and b c d
  assume "a \<simeq> b"
  also assume "b \<sqsubseteq> d"
  also assume "c \<simeq> d" hence "d \<simeq> c" by(simp add:ac_simps)
  finally show "a \<sqsubseteq> c" .
next
  fix a b and c::"'a prog" and d
  assume "c \<simeq> d"
  also assume "d \<sqsubseteq> b"
  also assume "a \<simeq> b" hence "b \<simeq> a" by(simp add:ac_simps)
  finally have "c \<sqsubseteq> a" .
  moreover assume "\<not> c \<sqsubseteq> a"
  ultimately show False by(auto)
next
  fix a b and c::"'a prog" and d
  assume "c \<simeq> d" hence "d \<simeq> c" by(simp add:ac_simps)
  also assume "c \<sqsubseteq> a"
  also assume "a \<simeq> b"
  finally have "d \<sqsubseteq> b" .
  moreover assume "\<not> d \<sqsubseteq> b"
  ultimately show False by(auto)
qed

lift_definition
  inf_program :: "'a program \<Rightarrow> 'a program \<Rightarrow> 'a program" is DC
proof(safe)
  fix a b c d::"'s prog"
  assume "a \<simeq> b" and "c \<simeq> d"
  thus "(a \<Sqinter> c) \<simeq> (b \<Sqinter> d)" by(rule pequiv_DC)
next
  fix a c::"'s prog"
  assume "well_def a" "well_def c"
  thus "well_def (a \<Sqinter> c)" by(rule wd_intros)
next
  fix a c::"'s prog"
  assume "well_def a" "well_def c"
  thus "well_def (a \<Sqinter> c)" by(rule wd_intros)
qed

instance
proof
  fix x y::"'a program"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by(transfer, simp)
  show "x \<le> x"
    by(transfer, auto)
  show "inf x y \<le> x"
    by(transfer, rule left_refines_DC)
  show "inf x y \<le> y"
    by(transfer, rule right_refines_DC)
  assume "x \<le> y" and "y \<le> x" thus "x = y"
    by(transfer, iprover intro:pequiv_antisym)
next
  fix x y z::"'a program"
  assume "x \<le> y" and "y \<le> z"
  thus "x \<le> z"
    by(transfer, iprover intro:pr_trans)
next
  fix x y z::"'a program"
  assume "x \<le> y" and "x \<le> z"
  thus "x \<le> inf y z"
    by(transfer, iprover intro:DC_refines)
qed
end

instantiation program :: (type) bot begin
lift_definition
  bot_program :: "'a program" is Abort
  by(auto intro:wd_intros)

instance ..
end

lemma eq_det: "\<And>a b::'s prog. \<lbrakk> a \<simeq> b; determ (wp a) \<rbrakk> \<Longrightarrow> determ (wp b)"
proof(intro determI additiveI maximalI)
  fix a b::"'s prog" and P::"'s \<Rightarrow> real"
    and Q::"'s \<Rightarrow> real" and s::"'s"
  assume da: "determ (wp a)"
  assume sP: "sound P" and sQ: "sound Q"
    and eq: "a \<simeq> b"
  hence "wp b (\<lambda>s. P s + Q s) s =
         wp a (\<lambda>s. P s + Q s) s"
    by(simp add:sound_intros)
  also from da sP sQ
  have "... = wp a P s + wp a Q s"
    by(simp add:additiveD determ_additiveD)
  also from eq sP sQ
  have "... = wp b P s + wp b Q s"
    by(simp add:pequivD)
  finally show "wp b (\<lambda>s. P s + Q s) s = wp b P s + wp b Q s" .
next
  fix a b::"'s prog" and c::real
  assume da: "determ (wp a)"
  assume "a \<simeq> b" hence "b \<simeq> a" by(simp add:ac_simps)
  moreover assume nn: "0 \<le> c"
  ultimately have "wp b (\<lambda>_. c) = wp a (\<lambda>_. c)"
    by(simp add:pequivD const_sound)
  also from da nn have "... = (\<lambda>_. c)"
    by(simp add:determ_maximalD maximalD)
  finally show "wp b (\<lambda>_. c) = (\<lambda>_. c)" .
qed

lift_definition
  pdeterm :: "'s program \<Rightarrow> bool"
  is "\<lambda>a. determ (wp a)"
proof(safe)
  fix a b::"'s prog"
  assume "a \<simeq> b" and "determ (wp a)"
  thus "determ (wp b)" by(rule eq_det)
next
  fix a b::"'s prog"
  assume "a \<simeq> b" hence "b \<simeq> a" by(simp add:ac_simps)
  moreover assume "determ (wp b)"
  ultimately show "determ (wp a)" by(rule eq_det)
qed

lemma determ_maximal:
  "\<lbrakk> pdeterm a; a \<le> x \<rbrakk> \<Longrightarrow> a = x"
  by(transfer, auto intro:refines_determ)

subsection \<open>Data Refinement\<close>

text \<open>A projective data refinement construction for pGCL. By projective, we mean that the abstract
state is always a function (@{term \<phi>}) of the concrete state. Refinement may be predicated (@{term
G}) on the state.\<close>

definition
  drefines :: "('b \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'a prog \<Rightarrow> 'b prog \<Rightarrow> bool"
where
  "drefines \<phi> G A B \<equiv> \<forall>P Q. (unitary P \<and> unitary Q \<and> (P \<tturnstile> wp A Q)) \<longrightarrow>
                            (\<guillemotleft>G\<guillemotright> && (P o \<phi>) \<tturnstile> wp B (Q o \<phi>))"

lemma drefinesD[dest]:
  "\<lbrakk> drefines \<phi> G A B; unitary P; unitary Q; P \<tturnstile> wp A Q \<rbrakk> \<Longrightarrow>
   \<guillemotleft>G\<guillemotright> && (P o \<phi>) \<tturnstile> wp B (Q o \<phi>)"
  unfolding drefines_def by(blast)

text \<open>We can alternatively use G as an assumption:\<close>
lemma drefinesD2:
  assumes dr:  "drefines \<phi> G A B"
      and uP:  "unitary P"
      and uQ:  "unitary Q"
      and wpA: "P \<tturnstile> wp A Q"
      and G:   "G s"
  shows "(P o \<phi>) s \<le> wp B (Q o \<phi>) s"
proof -
  from uP have "0 \<le> (P o \<phi>) s" unfolding o_def by(blast)
  with G have "(P o \<phi>) s = (\<guillemotleft>G\<guillemotright> && (P o \<phi>)) s"
    by(simp add:exp_conj_def)
  also from assms have "... \<le> wp B (Q o \<phi>) s" by(blast)
  finally show "(P o \<phi>) s \<le> ..." .
qed

text \<open>This additional form is sometimes useful:\<close>
lemma drefinesD3:
  assumes dr: "drefines \<phi> G a b"
      and G:  "G s"
      and uQ: "unitary Q"
      and wa: "well_def a"
  shows "wp a Q (\<phi> s) \<le> wp b (Q o \<phi>) s"
proof -
  let "?L s'" = "wp a Q s'"
  from uQ wa have sL: "sound ?L" by(blast)
  from uQ wa have bL: "bounded_by 1 ?L" by(blast)

  have "?L \<tturnstile> ?L" by(simp)
  with sL and bL and assms
  show ?thesis
    by(blast intro:drefinesD2[OF dr, where P="?L", simplified])
qed

lemma drefinesI[intro]:
  "\<lbrakk> \<And>P Q. \<lbrakk> unitary P; unitary Q; P \<tturnstile> wp A Q \<rbrakk> \<Longrightarrow>
           \<guillemotleft>G\<guillemotright> && (P o \<phi>) \<tturnstile> wp B (Q o \<phi>) \<rbrakk> \<Longrightarrow>
   drefines \<phi> G A B"
  unfolding drefines_def by(blast)

text \<open>Use G as an assumption, when showing refinement:\<close>
lemma drefinesI2:
  fixes   A::"'a prog"
    and   B::"'b prog"
    and   \<phi>::"'b \<Rightarrow> 'a"
    and   G::"'b \<Rightarrow> bool"
  assumes wB: "well_def B"
      and withAs:
        "\<And>P Q s. \<lbrakk> unitary P; unitary Q;
                 G s; P \<tturnstile> wp A Q \<rbrakk> \<Longrightarrow> (P o \<phi>) s \<le> wp B (Q o \<phi>) s"
  shows "drefines \<phi> G A B"
proof
  fix P and Q
  assume uP:  "unitary P"
     and uQ:  "unitary Q"
     and wpA: "P \<tturnstile> wp A Q"

  hence "\<And>s. G s \<Longrightarrow> (P o \<phi>) s \<le> wp B (Q o \<phi>) s"
    using withAs by(blast)
  moreover
  from uQ have "unitary (Q o \<phi>)"
    unfolding o_def by(blast)
  moreover
  from uP have "unitary (P o \<phi>)"
    unfolding o_def by(blast)
  ultimately
  show "\<guillemotleft>G\<guillemotright> && (P o \<phi>) \<tturnstile> wp B (Q o \<phi>)"
    using wB by(blast intro:entails_pconj_assumption)
qed

lemma dr_strengthen_guard:
  fixes a::"'s prog" and b::"'t prog"
  assumes fg: "\<And>s. F s \<Longrightarrow> G s"
      and drab: "drefines \<phi> G a b"
  shows "drefines \<phi> F a b"
proof(intro drefinesI)
  fix P Q::"'s expect"
  assume uP: "unitary P" and uQ: "unitary Q"
     and wp: "P \<tturnstile> wp a Q"
  from fg have "\<And>s. \<guillemotleft>F\<guillemotright> s \<le> \<guillemotleft>G\<guillemotright> s" by(simp add:embed_bool_def)
  hence "(\<guillemotleft>F\<guillemotright> && (P o \<phi>)) \<tturnstile> (\<guillemotleft>G\<guillemotright> && (P o \<phi>))" by(auto intro:pconj_mono le_funI simp:exp_conj_def)
  also from drab uP uQ wp have "... \<tturnstile> wp b (Q o \<phi>)" by(auto)
  finally show "\<guillemotleft>F\<guillemotright> && (P o \<phi>) \<tturnstile> wp b (Q o \<phi>)" .
qed

text \<open>Probabilistic correspondence, @{term pcorres}, is equality on distribution transformers,
modulo a guard. It is the analogue, for data refinement, of program equivalence for program
refinement.\<close>
definition
  pcorres :: "('b \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'a prog \<Rightarrow> 'b prog \<Rightarrow> bool"
where
  "pcorres \<phi> G A B \<longleftrightarrow>
   (\<forall>Q. unitary Q \<longrightarrow>  \<guillemotleft>G\<guillemotright> && (wp A Q o \<phi>) = \<guillemotleft>G\<guillemotright> && wp B (Q o \<phi>))"

lemma pcorresI:
  "\<lbrakk> \<And>Q. unitary Q \<Longrightarrow> \<guillemotleft>G\<guillemotright> && (wp A Q o \<phi>) = \<guillemotleft>G\<guillemotright> && wp B (Q o \<phi>) \<rbrakk> \<Longrightarrow>
   pcorres \<phi> G A B"
  by(simp add:pcorres_def)

text \<open>Often easier to use, as it allows one to assume the precondition.\<close>
lemma pcorresI2[intro]:
  fixes A::"'a prog" and B::"'b prog"
  assumes withG: "\<And>Q s. \<lbrakk> unitary Q; G s \<rbrakk> \<Longrightarrow> wp A Q (\<phi> s)= wp B (Q o \<phi>) s"
      and wA: "well_def A"
      and wB: "well_def B"
  shows "pcorres \<phi> G A B"
proof(rule pcorresI, rule ext)
  fix Q::"'a \<Rightarrow> real" and s::'b
  assume uQ: "unitary Q"
  hence uQ\<phi>: "unitary (Q o \<phi>)" by(auto)
  show "(\<guillemotleft>G\<guillemotright> && (wp A Q \<circ> \<phi>)) s = (\<guillemotleft>G\<guillemotright> && wp B (Q \<circ> \<phi>)) s"
  proof(cases "G s")
    case True note this
    moreover
    from well_def_wp_healthy[OF wA] uQ have "0 \<le> wp A Q (\<phi> s)" by(blast)
    moreover
    from well_def_wp_healthy[OF wB] uQ\<phi> have "0 \<le> wp B (Q o \<phi>) s" by(blast)
    ultimately show ?thesis
      using uQ by(simp add:exp_conj_def withG)
  next
    case False note this
    moreover
    from well_def_wp_healthy[OF wA] uQ have "wp A Q (\<phi> s) \<le> 1" by(blast)
    moreover
    from well_def_wp_healthy[OF wB] uQ\<phi> have "wp B (Q o \<phi>) s \<le> 1"
      by(blast dest!:healthy_bounded_byD intro:sound_nneg)
    ultimately show ?thesis by(simp add:exp_conj_def)
  qed
qed

lemma pcorresD:
  "\<lbrakk> pcorres \<phi> G A B; unitary Q \<rbrakk> \<Longrightarrow> \<guillemotleft>G\<guillemotright> && (wp A Q o \<phi>) = \<guillemotleft>G\<guillemotright> && wp B (Q o \<phi>)"
  unfolding pcorres_def by(simp)

text \<open>Again, easier to use if the precondition is known to hold.\<close>
lemma pcorresD2:
  assumes pc: "pcorres \<phi> G A B"
      and uQ: "unitary Q"
      and wA: "well_def A" and wB: "well_def B"
      and G: "G s"
  shows "wp A Q (\<phi> s) = wp B (Q o \<phi>) s"
proof -
  from uQ well_def_wp_healthy[OF wA] have "0 \<le> wp A Q (\<phi> s)" by(auto)
  with G have "wp A Q (\<phi> s) = \<guillemotleft>G\<guillemotright> s .& wp A Q (\<phi> s)" by(simp)
  also {
    from pc uQ have "\<guillemotleft>G\<guillemotright> && (wp A Q o \<phi>) = \<guillemotleft>G\<guillemotright> && wp B (Q o \<phi>)"
      by(rule pcorresD)
    hence "\<guillemotleft>G\<guillemotright> s .& wp A Q (\<phi> s) = \<guillemotleft>G\<guillemotright> s .& wp B (Q o \<phi>) s"
      unfolding exp_conj_def o_def by(rule fun_cong)
  }
  also {
    from uQ have "sound Q" by(auto)
    hence "sound (Q o \<phi>)" by(auto intro:sound_intros)
    with well_def_wp_healthy[OF wB] have "0 \<le> wp B (Q o \<phi>) s" by(auto)
    with G have "\<guillemotleft>G\<guillemotright> s .& wp B (Q o \<phi>) s = wp B (Q o \<phi>) s" by(simp)
  }
  finally show ?thesis .
qed

subsection \<open>The Algebra of Data Refinement\<close>

text \<open>Program refinement implies a trivial data refinement:\<close>
lemma refines_drefines:
  fixes a::"'s prog"
  assumes rab: "a \<sqsubseteq> b" and wb: "well_def b"
  shows "drefines (\<lambda>s. s) G a b"
proof(intro drefinesI2 wb, simp add:o_def)
  fix P::"'s \<Rightarrow> real" and Q::"'s \<Rightarrow> real" and s::'s
  assume sQ: "unitary Q"
  assume "P \<tturnstile> wp a Q" hence "P s \<le> wp a Q s" by(auto)
  also from rab sQ have "... \<le> wp b Q s" by(auto)
  finally show "P s \<le> wp b Q s" .
qed

text \<open>Data refinement is transitive:\<close>
lemma dr_trans[trans]:
  fixes A::"'a prog" and B::"'b prog" and C::"'c prog"
  assumes drAB: "drefines \<phi> G A B"
      and drBC: "drefines \<phi>' G' B C"
      and Gimp: "\<And>s. G' s \<Longrightarrow> G (\<phi>' s)"
  shows "drefines (\<phi> o \<phi>') G' A C"
proof(rule drefinesI)
  fix P::"'a \<Rightarrow> real" and Q::"'a \<Rightarrow> real" and s::'a
  assume uP: "unitary P" and uQ: "unitary Q"
     and wpA: "P \<tturnstile> wp A Q"

  have "\<guillemotleft>G'\<guillemotright> && \<guillemotleft>G o \<phi>'\<guillemotright> = \<guillemotleft>G'\<guillemotright>"
  proof(rule ext, unfold exp_conj_def)
    fix x
    show "\<guillemotleft>G'\<guillemotright> x .& \<guillemotleft>G o \<phi>'\<guillemotright> x = \<guillemotleft>G'\<guillemotright> x" (is ?X)
    proof(cases "G' x")
      case False then show ?X by(simp)
    next
      case True
      moreover
      with Gimp have "(G o \<phi>') x" by(simp add:o_def)
      ultimately
      show ?X by(simp)
    qed
  qed

  with uP
  have "\<guillemotleft>G'\<guillemotright> && (P o (\<phi> o \<phi>')) = \<guillemotleft>G'\<guillemotright> && ((\<guillemotleft>G\<guillemotright> && (P o \<phi>)) o \<phi>')"
    by(simp add:exp_conj_assoc o_assoc)

  also {
    from uP uQ wpA and drAB
    have "\<guillemotleft>G\<guillemotright> && (P o \<phi>) \<tturnstile> wp B (Q o \<phi>)"
      by(blast intro:drefinesD)

    with drBC and uP uQ
    have "\<guillemotleft>G'\<guillemotright> && ((\<guillemotleft>G\<guillemotright> && (P o \<phi>)) o \<phi>') \<tturnstile> wp C ((Q o \<phi>) o \<phi>')"
      by(blast intro:unitary_intros drefinesD)
  }

  finally
  show "\<guillemotleft>G'\<guillemotright> && (P o (\<phi> o \<phi>')) \<tturnstile> wp C (Q o (\<phi> o \<phi>'))"
    by(simp add:o_assoc)
qed

text \<open>Data refinement composes with program refinement:\<close>
lemma pr_dr_trans[trans]:
  assumes prAB: "A \<sqsubseteq> B"
      and drBC: "drefines \<phi> G B C"
  shows "drefines \<phi> G A C"
proof(rule drefinesI)
  fix P and Q
  assume uP:  "unitary P"
     and uQ:  "unitary Q"
     and wpA: "P \<tturnstile> wp A Q"

  note wpA
  also from uQ and prAB have "wp A Q \<tturnstile> wp B Q" by(blast)
  finally have "P \<tturnstile> wp B Q" .
  with uP uQ drBC
  show "\<guillemotleft>G\<guillemotright> && (P o \<phi>) \<tturnstile> wp C (Q o \<phi>)" by(blast intro:drefinesD)
qed

lemma dr_pr_trans[trans]:
  assumes drAB: "drefines \<phi> G A B"
  assumes prBC: "B \<sqsubseteq> C"
  shows "drefines \<phi> G A C"
proof(rule drefinesI)
  fix P and Q
  assume uP:  "unitary P"
     and uQ:  "unitary Q"
     and wpA: "P \<tturnstile> wp A Q"

  with drAB have "\<guillemotleft>G\<guillemotright> && (P o \<phi>) \<tturnstile> wp B (Q o \<phi>)" by(blast intro:drefinesD)
  also from uQ prBC have "... \<tturnstile> wp C (Q o \<phi>)" by(blast)
  finally show "\<guillemotleft>G\<guillemotright> && (P o \<phi>) \<tturnstile> ..." .
qed

text \<open>If the projection @{term \<phi>} commutes with the transformer, then data refinement is
reflexive:\<close>
lemma dr_refl:
  assumes wa: "well_def a"
      and comm: "\<And>Q. unitary Q \<Longrightarrow> wp a Q o \<phi> \<tturnstile> wp a (Q o \<phi>)"
  shows "drefines \<phi> G a a"
proof(intro drefinesI2 wa)
  fix P and Q and s
  assume wp: "P \<tturnstile> wp a Q"
  assume uQ: "unitary Q"

  have "(P o \<phi>) s = P (\<phi> s)" by(simp)
  also from wp have "... \<le> wp a Q (\<phi> s)" by(blast)
  also {
    from comm uQ have "wp a Q o \<phi> \<tturnstile> wp a (Q o \<phi>)" by(blast)
    hence "(wp a Q o \<phi>) s \<le> wp a (Q o \<phi>) s" by(blast)
    hence "wp a Q (\<phi> s) \<le> ..." by(simp)
  }
  finally show  "(P o \<phi>) s \<le> wp a (Q o \<phi>) s" .
qed

text \<open>Correspondence implies data refinement\<close>
lemma pcorres_drefine:
  assumes corres: "pcorres \<phi> G A C"
      and wC: "well_def C"
  shows "drefines \<phi> G A C"
proof
  fix P and Q
  assume uP: "unitary P" and uQ: "unitary Q"
     and wpA: "P \<tturnstile> wp A Q"
  from wpA have "P o \<phi> \<tturnstile> wp A Q o \<phi>" by(simp add:o_def le_fun_def)
  hence "\<guillemotleft>G\<guillemotright> && (P o \<phi>) \<tturnstile> \<guillemotleft>G\<guillemotright> && (wp A Q o \<phi>)"
    by(rule exp_conj_mono_right)
  also from corres uQ
  have "... = \<guillemotleft>G\<guillemotright> && (wp C (Q o \<phi>))" by(rule pcorresD)
  also
  have "... \<tturnstile> wp C (Q o \<phi>)"
  proof(rule le_funI)
    fix s
    from uQ have "unitary (Q o \<phi>)" by(rule unitary_intros)
    with well_def_wp_healthy[OF wC] have nn_wpC: "0 \<le> wp C (Q o \<phi>) s" by(blast)
    show "(\<guillemotleft>G\<guillemotright> && wp C (Q o \<phi>)) s \<le> wp C (Q o \<phi>) s"
    proof(cases "G s")
      case True
      with nn_wpC show ?thesis by(simp add:exp_conj_def)
    next
      case False note this
      moreover {
        from uQ have "unitary (Q o \<phi>)" by(simp)
        with well_def_wp_healthy[OF wC] have "wp C (Q o \<phi>) s \<le> 1" by(auto)
      }
      moreover note nn_wpC
      ultimately show ?thesis by(simp add:exp_conj_def)
    qed
  qed
  finally show "\<guillemotleft>G\<guillemotright> && (P o \<phi>) \<tturnstile> wp C (Q o \<phi>)" .
qed

text \<open>Any \emph{data} refinement of a deterministic program is correspondence. This is the
analogous result to that relating program refinement and equivalence.\<close>
lemma drefines_determ:
  fixes a::"'a prog" and b::"'b prog"
  assumes da: "determ (wp a)"
      and wa: "well_def a"
      and wb: "well_def b"
      and dr: "drefines \<phi> G a b"
  shows "pcorres \<phi> G a b"
  txt \<open>The proof follows exactly the same form
    as that for program refinement: Assuming that correspondence
    \emph{doesn't} hold, we show that @{term "wp b"} is not feasible,
    and thus not healthy, contradicting the assumption.\<close>
proof(rule pcorresI, rule contrapos_pp)
  from wb show "feasible (wp b)" by(auto)

  note ha = well_def_wp_healthy[OF wa]
  note hb = well_def_wp_healthy[OF wb]

  from wb have "sublinear (wp b)" by(auto)
  moreover from hb have "feasible (wp b)" by(auto)
  ultimately have sab: "sub_add (wp b)" by(rule sublinear_subadd)

  fix Q::"'a \<Rightarrow> real"
  assume uQ: "unitary Q"
  hence uQ\<phi>: "unitary (Q o \<phi>)" by(auto)
  assume ne: "\<guillemotleft>G\<guillemotright> && (wp a Q o \<phi>) \<noteq> \<guillemotleft>G\<guillemotright> && wp b (Q o \<phi>)"
  hence ne': "wp a Q o \<phi> \<noteq> wp b (Q o \<phi>)" by(auto)

  txt \<open>From refinement, @{term "\<guillemotleft>G\<guillemotright> && (wp a Q o \<phi>)"}
    lies below @{term "\<guillemotleft>G\<guillemotright> && wp b (Q o \<phi>)"}.\<close>
  from ha uQ
  have gle: "\<guillemotleft>G\<guillemotright> && (wp a Q o \<phi>) \<tturnstile> wp b (Q o \<phi>)" by(blast intro!:drefinesD[OF dr])
  have le: "\<guillemotleft>G\<guillemotright> && (wp a Q o \<phi>) \<tturnstile> \<guillemotleft>G\<guillemotright> && wp b (Q o \<phi>)"
    unfolding exp_conj_def
  proof(rule le_funI)
    fix s
    from gle have "\<guillemotleft>G\<guillemotright> s .& (wp a Q o \<phi>) s \<le> wp b (Q o \<phi>) s"
      unfolding exp_conj_def by(auto)
    hence "\<guillemotleft>G\<guillemotright> s .& (\<guillemotleft>G\<guillemotright> s .& (wp a Q o \<phi>) s) \<le> \<guillemotleft>G\<guillemotright> s .& wp b (Q o \<phi>) s"
      by(auto intro:pconj_mono)
    moreover from uQ ha have "wp a Q (\<phi> s) \<le> 1"
      by(auto dest:healthy_bounded_byD)
    moreover from uQ ha have "0 \<le> wp a Q (\<phi> s)"
      by(auto)
    ultimately
    show "\<guillemotleft> G \<guillemotright> s .& (wp a Q \<circ> \<phi>) s \<le> \<guillemotleft> G \<guillemotright> s .& wp b (Q \<circ> \<phi>) s"
      by(simp add:pconj_assoc)
  qed

  txt \<open>If the programs do not correspond, the terms must differ somewhere, and given the previous
  result, the second must be somewhere strictly larger than the first:\<close>
  have nle: "\<exists>s. (\<guillemotleft>G\<guillemotright> && (wp a Q o \<phi>)) s < (\<guillemotleft>G\<guillemotright> && wp b (Q o \<phi>)) s"
  proof(rule contrapos_np[OF ne], rule ext, rule antisym)
    fix s
    from le show "(\<guillemotleft>G\<guillemotright> && (wp a Q o \<phi>)) s \<le> (\<guillemotleft>G\<guillemotright> && wp b (Q o \<phi>)) s"
      by(blast)
  next
    fix s
    assume "\<not> (\<exists>s. (\<guillemotleft>G\<guillemotright> && (wp a Q \<circ> \<phi>)) s < (\<guillemotleft>G\<guillemotright> && wp b (Q \<circ> \<phi>)) s)"
    thus " (\<guillemotleft>G\<guillemotright> && (wp b (Q \<circ> \<phi>))) s \<le> (\<guillemotleft>G\<guillemotright> && (wp a Q \<circ> \<phi>)) s"
      by(simp add:not_less)
  qed
  from this obtain s where less_s:
    "(\<guillemotleft>G\<guillemotright> && (wp a Q \<circ> \<phi>)) s < (\<guillemotleft>G\<guillemotright> && wp b (Q \<circ> \<phi>)) s"
    by(blast)
  txt \<open>The transformers themselves must differ at this point:\<close>
  hence larger: "wp a Q (\<phi> s) < wp b (Q \<circ> \<phi>) s"
  proof(cases "G s")
    case True
    moreover from ha uQ have "0 \<le> wp a Q (\<phi> s)"
      by(blast)
    moreover from hb uQ\<phi> have "0 \<le> wp b (Q o \<phi>) s"
      by(blast)
    moreover note less_s
    ultimately show ?thesis by(simp add:exp_conj_def)
  next
    case False
    moreover from ha uQ have "wp a Q (\<phi> s) \<le> 1"
      by(blast)
    moreover {
      from uQ have "bounded_by 1 (Q o \<phi>)"
        by(blast)
      moreover from unitary_sound[OF uQ]
      have "sound (Q o \<phi>)" by(auto)
      ultimately have "wp b (Q o \<phi>) s \<le> 1"
        using hb by(auto)
    }
    moreover note less_s
    ultimately show ?thesis by(simp add:exp_conj_def)
  qed
  from less_s have "(\<guillemotleft>G\<guillemotright> && (wp a Q \<circ> \<phi>)) s \<noteq> (\<guillemotleft>G\<guillemotright> && wp b (Q \<circ> \<phi>)) s"
    by(force)
  txt \<open>@{term G} must also hold, as otherwise both would be zero.\<close>
  hence G_s: "G s"
  proof(rule contrapos_np)
    assume nG: "\<not> G s"
    moreover from ha uQ have "wp a Q (\<phi> s) \<le> 1"
      by(blast)
    moreover {
      from uQ have "bounded_by 1 (Q o \<phi>)"
        by(blast)
      moreover from unitary_sound[OF uQ]
      have "sound (Q o \<phi>)" by(auto)
      ultimately have "wp b (Q o \<phi>) s \<le> 1"
        using hb by(auto)
    }
    ultimately
    show "(\<guillemotleft>G\<guillemotright> && (wp a Q \<circ> \<phi>)) s = (\<guillemotleft>G\<guillemotright> && wp b (Q \<circ> \<phi>)) s"
      by(simp add:exp_conj_def)
  qed

  txt \<open>Take a carefully constructed expectation:\<close>
  let ?Qc = "\<lambda>s. bound_of Q - Q s"
  have bQc: "bounded_by 1 ?Qc"
  proof(rule bounded_byI)
    fix s
    from uQ have "bound_of Q \<le> 1" and "0 \<le> Q s" by(auto)
    thus "bound_of Q - Q s \<le> 1" by(auto)
  qed
  have sQc: "sound ?Qc"
  proof(rule soundI)
    from bQc show "bounded ?Qc" by(auto)

    show "nneg ?Qc"
    proof(rule nnegI)
      fix s
      from uQ have "Q s \<le> bound_of Q" by(auto)
      thus "0 \<le> bound_of Q - Q s" by(auto)
    qed
  qed

  txt \<open>By the maximality of @{term "wp a"}, @{term "wp b"} must violate feasibility, by mapping
  @{term s} to something strictly greater than @{term "bound_of Q"}.\<close>
  from uQ have "0 \<le> bound_of Q" by(auto)
  with da have "bound_of Q = wp a (\<lambda>s. bound_of Q) (\<phi> s)"
    by(simp add:maximalD determ_maximalD)
  also have "wp a (\<lambda>s. bound_of Q) (\<phi> s) = wp a (\<lambda>s. Q s + ?Qc s) (\<phi> s)"
    by(simp)
  also {
    from da have "additive (wp a)" by(blast)
    with uQ sQc
    have "wp a (\<lambda>s. Q s + ?Qc s) (\<phi> s) =
          wp a Q (\<phi> s) + wp a ?Qc (\<phi> s)" by(subst additiveD, blast+)
  }
  also {
    from ha and sQc and bQc
    have "\<guillemotleft>G\<guillemotright> && (wp a ?Qc o \<phi>) \<tturnstile> wp b (?Qc o \<phi>)"
      by(blast intro!:drefinesD[OF dr])
    hence "(\<guillemotleft>G\<guillemotright> && (wp a ?Qc o \<phi>)) s \<le> wp b (?Qc o \<phi>) s"
      by(blast)
    moreover from sQc and ha
    have "0 \<le> wp a (\<lambda>s. bound_of Q - Q s) (\<phi> s)"
      by(blast)
    ultimately
    have "wp a ?Qc (\<phi> s) \<le> wp b (?Qc o \<phi>) s"
      using G_s by(simp add:exp_conj_def)
    hence "wp a Q (\<phi> s) + wp a ?Qc (\<phi> s) \<le> wp a Q (\<phi> s) + wp b (?Qc o \<phi>) s"
      by(rule add_left_mono)
    also with larger
    have "wp a Q (\<phi> s) + wp b (?Qc o \<phi>) s <
          wp b (Q o \<phi>) s + wp b (?Qc o \<phi>) s"
      by(auto)
    finally
    have "wp a Q (\<phi> s) + wp a ?Qc (\<phi> s) <
          wp b (Q o \<phi>) s + wp b (?Qc o \<phi>) s" .
  }
  also from sab and unitary_sound[OF uQ] and sQc
  have "wp b (Q o \<phi>) s + wp b (?Qc o \<phi>) s \<le>
        wp b (\<lambda>s. (Q o \<phi>) s + (?Qc o \<phi>) s) s"
    by(blast)
  also have "... = wp b (\<lambda>s. bound_of Q) s"
    by(simp)
  finally
  show "\<not> feasible (wp b)"
  proof(rule contrapos_pn)
    assume fb: "feasible (wp b)"
    have "bounded_by (bound_of Q) (\<lambda>s. bound_of Q)" by(blast)
    hence "bounded_by (bound_of Q) (wp b (\<lambda>s. bound_of Q))"
      using uQ by(blast intro:feasible_boundedD[OF fb])
    hence "wp b (\<lambda>s. bound_of Q) s \<le> bound_of Q" by(blast)
    thus "\<not> bound_of Q < wp b (\<lambda>s. bound_of Q) s" by(simp)
  qed
qed

subsection \<open>Structural Rules for Correspondence\<close>

lemma pcorres_Skip:
  "pcorres \<phi> G Skip Skip"
  by(simp add:pcorres_def wp_eval)

text \<open>Correspondence composes over sequential composition.\<close>
lemma pcorres_Seq:
  fixes A::"'b prog" and B::"'c prog"
    and C::"'b prog" and D::"'c prog"
    and \<phi>::"'c \<Rightarrow> 'b"
  assumes pcAB: "pcorres \<phi> G A B"
      and pcCD: "pcorres \<phi> H C D"
      and wA: "well_def A" and wB: "well_def B"
      and wC: "well_def C" and wD: "well_def D"
      and p3p2: "\<And>Q. unitary Q \<Longrightarrow> \<guillemotleft>I\<guillemotright> && wp B Q = wp B (\<guillemotleft>H\<guillemotright> && Q)"
      and p1p3: "\<And>s. G s \<Longrightarrow> I s"
  shows "pcorres \<phi> G (A;;C) (B;;D)"
proof(rule pcorresI)
  fix Q::"'b \<Rightarrow> real"
  assume uQ: "unitary Q"
  with well_def_wp_healthy[OF wC] have uCQ: "unitary (wp C Q)" by(auto)
  from uQ well_def_wp_healthy[OF wD] have uDQ: "unitary (wp D (Q o \<phi>))"
    by(auto dest:unitary_comp)

  have p3p1: "\<And>R S. \<lbrakk> unitary R; unitary S; \<guillemotleft>I\<guillemotright> && R = \<guillemotleft>I\<guillemotright> && S \<rbrakk> \<Longrightarrow>
                    \<guillemotleft>G\<guillemotright> && R = \<guillemotleft>G\<guillemotright> && S"
  proof(rule ext)
    fix R::"'c \<Rightarrow> real" and S::"'c \<Rightarrow> real" and s::'c
    assume a3: "\<guillemotleft>I\<guillemotright> && R = \<guillemotleft>I\<guillemotright> && S"
       and uR: "unitary R" and uS: "unitary S"
    show "(\<guillemotleft>G\<guillemotright> && R) s = (\<guillemotleft>G\<guillemotright> && S) s"
    proof(simp add:exp_conj_def, cases "G s")
      case False note this
      moreover from uR have "R s \<le> 1" by(blast)
      moreover from uS have "S s \<le> 1" by(blast)
      ultimately show "\<guillemotleft>G\<guillemotright> s .& R s = \<guillemotleft>G\<guillemotright> s .& S s"
        by(simp)
    next
      case True note p1 = this
      with p1p3 have "I s" by(blast)
      with fun_cong[OF a3, where x=s] have "1 .& R s = 1 .& S s"
        by(simp add:exp_conj_def)
      with p1 show "\<guillemotleft>G\<guillemotright> s .& R s = \<guillemotleft>G\<guillemotright> s .& S s"
        by(simp)
    qed
  qed

  show "\<guillemotleft>G\<guillemotright> && (wp (A;;C) Q o \<phi>) = \<guillemotleft>G\<guillemotright> && wp (B;;D) (Q o \<phi>)"
  proof(simp add:wp_eval)
    from uCQ pcAB have "\<guillemotleft>G\<guillemotright> && (wp A (wp C Q) \<circ> \<phi>) =
                        \<guillemotleft>G\<guillemotright> && wp B ((wp C Q) \<circ> \<phi>)"
      by(auto dest:pcorresD)
    also have "\<guillemotleft>G\<guillemotright> && wp B ((wp C Q) \<circ> \<phi>) =
               \<guillemotleft>G\<guillemotright> && wp B (wp D (Q \<circ> \<phi>))"
    proof(rule p3p1)
      from uCQ well_def_wp_healthy[OF wB] show "unitary (wp B (wp C Q \<circ> \<phi>))"
        by(auto intro:unitary_comp)
      from uDQ well_def_wp_healthy[OF wB] show "unitary (wp B (wp D (Q \<circ> \<phi>)))"
        by(auto)

      from uQ have "\<guillemotleft> H \<guillemotright> && (wp C Q \<circ> \<phi>) = \<guillemotleft> H \<guillemotright> && wp D (Q \<circ> \<phi>)"
        by(blast intro:pcorresD[OF pcCD])
      thus "\<guillemotleft> I \<guillemotright> && wp B (wp C Q \<circ> \<phi>) = \<guillemotleft> I \<guillemotright> && wp B (wp D (Q \<circ> \<phi>))"
        by(simp add:p3p2 uCQ uDQ)
    qed
    finally show "\<guillemotleft>G\<guillemotright> && (wp A (wp C Q) \<circ> \<phi>) = \<guillemotleft>G\<guillemotright> && wp B (wp D (Q \<circ> \<phi>))" .
  qed
qed

subsection \<open>Structural Rules for Data Refinement\<close>

lemma dr_Skip:
  fixes \<phi>::"'c \<Rightarrow> 'b"
  shows "drefines \<phi> G Skip Skip"
proof(intro drefinesI2 wd_intros)
  fix P::"'b \<Rightarrow> real" and Q::"'b \<Rightarrow> real" and s::'c
  assume "P \<tturnstile> wp Skip Q"
  hence "(P o \<phi>) s \<le> wp Skip Q (\<phi> s)" by(simp, blast)
  thus "(P o \<phi>) s \<le> wp Skip (Q o \<phi>) s" by(simp add:wp_eval)
qed

lemma dr_Abort:
  fixes \<phi>::"'c \<Rightarrow> 'b"
  shows "drefines \<phi> G Abort Abort"
proof(intro drefinesI2 wd_intros)
  fix P::"'b \<Rightarrow> real" and Q::"'b \<Rightarrow> real" and s::'c
  assume "P \<tturnstile> wp Abort Q"
  hence "(P o \<phi>) s \<le> wp Abort Q (\<phi> s)" by(auto)
  thus "(P o \<phi>) s \<le> wp Abort (Q o \<phi>) s" by(simp add:wp_eval)
qed

lemma dr_Apply:
  fixes \<phi>::"'c \<Rightarrow> 'b"
  assumes commutes: "f o \<phi> = \<phi> o g"
  shows "drefines \<phi> G (Apply f) (Apply g)"
proof(intro drefinesI2 wd_intros)
  fix P::"'b \<Rightarrow> real" and Q::"'b \<Rightarrow> real" and s::'c

  assume wp: "P \<tturnstile> wp (Apply f) Q"
  hence "P \<tturnstile> (Q o f)" by(simp add:wp_eval)
  hence "P (\<phi> s) \<le> (Q o f) (\<phi> s)" by(blast)
  also have "... = Q ((f o \<phi>) s)" by(simp)
  also with commutes
  have "... = ((Q o \<phi>) o g) s" by(simp)
  also have "... = wp (Apply g) (Q o \<phi>) s"
    by(simp add:wp_eval)
  finally show "(P o \<phi>) s \<le> wp (Apply g) (Q o \<phi>) s" by(simp)
qed

lemma dr_Seq:
  assumes drAB: "drefines \<phi> P A B"
      and drBC: "drefines \<phi> Q C D"
      and wpB:  "\<guillemotleft>P\<guillemotright> \<tturnstile> wp B \<guillemotleft>Q\<guillemotright>"
      and wB:   "well_def B"
      and wC:   "well_def C"
      and wD:   "well_def D"
  shows "drefines \<phi> P (A;;C) (B;;D)"
proof
  fix R and S
  assume uR: "unitary R" and uS: "unitary S"
     and wpAC: "R \<tturnstile> wp (A;;C) S"

  from uR
  have "\<guillemotleft>P\<guillemotright> && (R o \<phi>) = \<guillemotleft>P\<guillemotright> && (\<guillemotleft>P\<guillemotright> && (R o \<phi>))"
    by(simp add:exp_conj_assoc)

  also {
    from well_def_wp_healthy[OF wC] uR uS
     and wpAC[unfolded eval_wp_Seq o_def]
    have "\<guillemotleft>P\<guillemotright> && (R o \<phi>) \<tturnstile> wp B (wp C S o \<phi>)"
      by(auto intro:drefinesD[OF drAB])
    with wpB well_def_wp_healthy[OF wC] uS
         sublinear_sub_conj[OF well_def_wp_sublinear, OF wB]
    have "\<guillemotleft>P\<guillemotright> && (\<guillemotleft>P\<guillemotright> && (R o \<phi>)) \<tturnstile> wp B (\<guillemotleft>Q\<guillemotright> && (wp C S o \<phi>))"
      by(auto intro!:entails_combine dest!:unitary_sound)
  }

  also {
    from uS well_def_wp_healthy[OF wC]
    have "\<guillemotleft>Q\<guillemotright> && (wp C S o \<phi>) \<tturnstile> wp D (S o \<phi>)"
      by(auto intro!:drefinesD[OF drBC])
    with well_def_wp_healthy[OF wB] well_def_wp_healthy[OF wC]
         well_def_wp_healthy[OF wD] and unitary_sound[OF uS]
    have "wp B (\<guillemotleft>Q\<guillemotright> && (wp C S o \<phi>)) \<tturnstile> wp B (wp D (S o \<phi>))"
      by(blast intro!:mono_transD)
  }

  finally
  show "\<guillemotleft>P\<guillemotright> && (R o \<phi>) \<tturnstile> wp (B;;D) (S o \<phi>)"
    unfolding wp_eval o_def .
qed

lemma dr_repeat:
  fixes \<phi> :: "'a \<Rightarrow> 'b"
  assumes dr_ab: "drefines \<phi> G a b"
      and Gpr:  "\<guillemotleft>G\<guillemotright> \<tturnstile> wp b \<guillemotleft>G\<guillemotright>"
      and wa:    "well_def a"
      and wb:    "well_def b"
  shows "drefines \<phi> G (repeat n a) (repeat n b)" (is "?X n")
proof(induct n)
  show "?X 0" by(simp add:dr_Skip)

  fix n
  assume IH: "?X n"
  thus "?X (Suc n)" by(auto intro!:dr_Seq Gpr assms wd_intros)
qed

end
