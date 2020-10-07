(*
 * Copyright (C) 2014 NICTA
 * All rights reserved.
 *)

(* Author: David Cock - David.Cock@nicta.com.au *)

section \<open>The Loop Rules\<close>

theory Loops imports WellDefined begin

text_raw \<open>\label{s:loop_rules}\<close>

text \<open>Given a well-defined body, we can annotate a loop using an invariant, just as in the
classical setting.\<close>

subsection \<open>Liberal and Strict Invariants.\<close>

text \<open>A probabilistic invariant generalises a boolean one: it \emph{entails} itself, given
the loop guard.\<close>

definition
  wp_inv :: "('s \<Rightarrow> bool) \<Rightarrow> 's prog \<Rightarrow> ('s \<Rightarrow> real) \<Rightarrow> bool"
where
  "wp_inv G body I \<longleftrightarrow> (\<forall>s. \<guillemotleft>G\<guillemotright> s * I s \<le> wp body I s)"

lemma wp_invI:
  "\<And>I. (\<And>s. \<guillemotleft>G\<guillemotright> s * I s \<le> wp body I s) \<Longrightarrow> wp_inv G body I"
  by(simp add:wp_inv_def)

definition
  wlp_inv :: "('s \<Rightarrow> bool) \<Rightarrow> 's prog \<Rightarrow> ('s \<Rightarrow> real) \<Rightarrow> bool"
where
  "wlp_inv G body I \<longleftrightarrow> (\<forall>s. \<guillemotleft>G\<guillemotright> s * I s \<le> wlp body I s)"

lemma wlp_invI:
  "\<And>I. (\<And>s. \<guillemotleft>G\<guillemotright> s * I s \<le> wlp body I s) \<Longrightarrow> wlp_inv G body I"
  by(simp add:wlp_inv_def)

lemma wlp_invD:
  "wlp_inv G body I \<Longrightarrow> \<guillemotleft>G\<guillemotright> s * I s \<le> wlp body I s"
  by(simp add:wlp_inv_def)

text \<open>For standard invariants, the multiplication reduces to conjunction.\<close>
lemma wp_inv_stdD:
  assumes inv: "wp_inv G body \<guillemotleft>I\<guillemotright>"
  and     hb:  "healthy (wp body)"
  shows "\<guillemotleft>G\<guillemotright> && \<guillemotleft>I\<guillemotright> \<tturnstile> wp body \<guillemotleft>I\<guillemotright>"
proof(rule le_funI)
  fix s
  show "(\<guillemotleft>G\<guillemotright> && \<guillemotleft>I\<guillemotright>) s \<le> wp body \<guillemotleft>I\<guillemotright> s"
  proof(cases "G s")
    case False
    with hb show ?thesis
      by(auto simp:exp_conj_def)
  next
    case True
    hence "(\<guillemotleft>G\<guillemotright> && \<guillemotleft>I\<guillemotright>) s = \<guillemotleft>G\<guillemotright> s * \<guillemotleft>I\<guillemotright> s"
      by(simp add:exp_conj_def)
    also from inv have "\<guillemotleft>G\<guillemotright> s * \<guillemotleft>I\<guillemotright> s \<le> wp body \<guillemotleft>I\<guillemotright> s"
      by(simp add:wp_inv_def)
    finally show ?thesis .
  qed
qed

subsection \<open>Partial Correctness\<close>

text \<open>Partial correctness for loops\citep[Lemma 7.2.2, \S7, p.~185]{McIver_M_04}.\<close>
lemma wlp_Loop:
  assumes wd: "well_def body"
      and uI: "unitary I"
      and inv: "wlp_inv G body I"
  shows "I \<le> wlp do G \<longrightarrow> body od (\<lambda>s. \<guillemotleft>\<N> G\<guillemotright> s * I s)"
  (is "I \<le> wlp do G \<longrightarrow> body od ?P")
proof -
  let "?f Q s" = "\<guillemotleft>G\<guillemotright> s * wlp body Q s + \<guillemotleft>\<N> G\<guillemotright> s * ?P s"
  have "I \<tturnstile> gfp_exp ?f"
  proof(rule gfp_exp_upperbound[OF _ uI])
    have "I = (\<lambda>s. (\<guillemotleft>G\<guillemotright> s + \<guillemotleft>\<N> G\<guillemotright> s) * I s)" by(simp add:negate_embed)
    also have "... = (\<lambda>s. \<guillemotleft>G\<guillemotright> s * I s + \<guillemotleft>\<N> G\<guillemotright> s * I s)"
      by(simp add:algebra_simps)
    also have "... = (\<lambda>s. \<guillemotleft>G\<guillemotright> s * (\<guillemotleft>G\<guillemotright> s * I s) + \<guillemotleft>\<N> G\<guillemotright> s * (\<guillemotleft>\<N> G\<guillemotright> s * I s))"
      by(simp add:embed_bool_idem algebra_simps)
    also have "... \<tturnstile> (\<lambda>s. \<guillemotleft>G\<guillemotright> s * wlp body I s + \<guillemotleft>\<N> G\<guillemotright> s * (\<guillemotleft>\<N> G\<guillemotright> s * I s))"
      using inv by(auto dest:wlp_invD intro:add_mono mult_left_mono)
    finally show "I \<tturnstile> (\<lambda>s. \<guillemotleft>G\<guillemotright> s * wlp body I s + \<guillemotleft>\<N> G\<guillemotright> s * (\<guillemotleft>\<N> G\<guillemotright> s * I s))" .
  qed
  also from uI well_def_wlp_nearly_healthy[OF wd] have "... = wlp do G \<longrightarrow> body od ?P"
    by(auto intro!:wlp_Loop1[symmetric] unitary_intros)
  finally show ?thesis .
qed

subsection \<open>Total Correctness\<close>
text_raw \<open>\label{s:loop_total}\<close>

text \<open>The first total correctness lemma for loops which terminate with probability 1\citep[Lemma
7.3.1, \S7, p.~186]{McIver_M_04}.\<close>

lemma wp_Loop:
  assumes wd:   "well_def body"
      and inv:  "wlp_inv G body I"
      and unit: "unitary I"
  shows "I && wp (do G \<longrightarrow> body od) (\<lambda>s. 1) \<tturnstile> wp (do G \<longrightarrow> body od) (\<lambda>s. \<guillemotleft>\<N> G\<guillemotright> s * I s)"
    (is "I && ?T \<tturnstile> wp ?loop ?X")
proof -
  txt \<open>We first appeal to the \emph{liberal} loop rule:\<close>
  from assms have "I && ?T \<tturnstile> wlp ?loop ?X && ?T"
    by(blast intro:exp_conj_mono_left wlp_Loop)

  txt \<open>Next, by sub-conjunctivity:\<close>
  also {
    from wd have sdp_loop: "sub_distrib_pconj (do G \<longrightarrow> body od)"
      by(blast intro:sdp_intros)

    from wd unit have "wlp ?loop ?X && ?T \<tturnstile> wp ?loop (?X && (\<lambda>s. 1))"
      by(blast intro:sub_distrib_pconjD sdp_intros unitary_intros)
  }

  txt \<open>Finally, the conjunction collapses:\<close>
  finally show ?thesis
    by(simp add:exp_conj_1_right sound_intros sound_nneg unit unitary_sound)
qed

subsection \<open>Unfolding\<close>

lemma wp_loop_unfold:
  fixes body :: "'s prog"
  assumes sP: "sound P"
      and h: "healthy (wp body)"
  shows "wp (do G \<longrightarrow> body od) P =
   (\<lambda>s. \<guillemotleft>\<N> G\<guillemotright> s * P s + \<guillemotleft>G\<guillemotright> s * wp body (wp (do G \<longrightarrow> body od) P) s)"
proof (simp only: wp_eval)
  let "?X t" = "wp (body ;; Embed t \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip)"
  have "equiv_trans (lfp_trans ?X)
    (wp (body ;; Embed (lfp_trans ?X) \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip))"
  proof(intro lfp_trans_unfold)
    fix t::"'s trans" and P::"'s expect"
    assume st: "\<And>Q. sound Q \<Longrightarrow> sound (t Q)"
       and sP: "sound P"
    with h show "sound (?X t P)"
      by(rule wp_loop_step_sound)
  next
    fix t u::"'s trans"
    assume "le_trans t u" "(\<And>P. sound P \<Longrightarrow> sound (t P))"
           "(\<And>P. sound P \<Longrightarrow> sound (u P))"
    with h show "le_trans (wp (body ;; Embed t \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip))
                          (wp (body ;; Embed u \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip))"
      by(iprover intro:wp_loop_step_mono)
  next
    let ?v = "\<lambda>P s. bound_of P"
    from h show "le_trans (wp (body ;; Embed ?v \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip)) ?v"
      by(intro le_transI, simp add:wp_eval lfp_loop_fp[unfolded negate_embed])
    fix P::"'s expect"
    assume "sound P" thus "sound (?v P)" by(auto)
  qed
  also have "equiv_trans ...
    (\<lambda>P s. \<guillemotleft>\<N> G\<guillemotright> s * P s + \<guillemotleft>G\<guillemotright> s * wp body (wp (Embed (lfp_trans ?X)) P) s)"
    by(rule equiv_transI, simp add:wp_eval algebra_simps negate_embed)
  finally show "lfp_trans ?X P =
    (\<lambda>s. \<guillemotleft>\<N> G\<guillemotright> s * P s + \<guillemotleft>G\<guillemotright> s * wp body (lfp_trans ?X P) s)"
    using sP unfolding wp_eval by(blast)
qed

lemma wp_loop_nguard:
  "\<lbrakk> healthy (wp body); sound P; \<not> G s \<rbrakk> \<Longrightarrow> wp do G \<longrightarrow> body od P s = P s"
  by(subst wp_loop_unfold, simp_all)

lemma wp_loop_guard:
  "\<lbrakk> healthy (wp body); sound P; G s \<rbrakk> \<Longrightarrow>
   wp do G \<longrightarrow> body od P s = wp (body ;; do G \<longrightarrow> body od) P s"
  by(subst wp_loop_unfold, simp_all add:wp_eval)

end
