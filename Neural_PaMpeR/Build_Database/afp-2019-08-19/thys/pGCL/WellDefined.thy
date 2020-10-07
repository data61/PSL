(*
 * Copyright (C) 2014 NICTA
 * All rights reserved.
 *)

(* Author: David Cock - David.Cock@nicta.com.au *)

section \<open>Well-Defined Programs.\<close>

theory WellDefined imports
  Healthiness
  Sublinearity
  LoopInduction
begin

text \<open>The definition of a well-defined program collects the various notions of healthiness and
well-behavedness that we have so far established: healthiness of the strict and liberal
transformers, continuity and sublinearity of the strict transformers, and two new properties.
These are that the strict transformer always lies below the liberal one (i.e. that it is at least
as \emph{strict}, recalling the standard embedding of a predicate), and that expectation
conjunction is distributed between then in a particular manner, which will be crucial in
establishing the loop rules.\<close>

subsection \<open>Strict Implies Liberal\<close>

text \<open>This establishes the first connection between the strict and
  liberal interpretations (@{term wp} and @{term wlp}).\<close>

definition
  wp_under_wlp :: "'s prog \<Rightarrow> bool"
where
  "wp_under_wlp prog \<equiv> \<forall>P. unitary P \<longrightarrow> wp prog P \<tturnstile> wlp prog P"

lemma wp_under_wlpI[intro]:
  "\<lbrakk> \<And>P. unitary P \<Longrightarrow> wp prog P \<tturnstile> wlp prog P \<rbrakk> \<Longrightarrow> wp_under_wlp prog"
  unfolding wp_under_wlp_def by(simp)

lemma wp_under_wlpD[dest]:
  "\<lbrakk> wp_under_wlp prog; unitary P \<rbrakk> \<Longrightarrow> wp prog P \<tturnstile> wlp prog P"
  unfolding wp_under_wlp_def by(simp)

lemma wp_under_le_trans:
  "wp_under_wlp a \<Longrightarrow> le_utrans (wp a) (wlp a)"
  by(blast)

lemma wp_under_wlp_Abort:
  "wp_under_wlp Abort"
  by(rule wp_under_wlpI, unfold wp_eval, auto)

lemma wp_under_wlp_Skip:
  "wp_under_wlp Skip"
  by(rule wp_under_wlpI, unfold wp_eval, blast)

lemma wp_under_wlp_Apply:
  "wp_under_wlp (Apply f)"
  by(auto simp:wp_eval)

lemma wp_under_wlp_Seq:
  assumes h_wlp_a: "nearly_healthy (wlp a)"
      and h_wp_b:  "healthy (wp b)"
      and h_wlp_b: "nearly_healthy (wlp b)"
      and wp_u_a:  "wp_under_wlp a"
      and wp_u_b:  "wp_under_wlp b"
  shows "wp_under_wlp (a ;; b)"
proof(rule wp_under_wlpI, unfold wp_eval o_def)
  fix P::"'a \<Rightarrow> real" assume uP: "unitary P"
  with h_wp_b have "unitary (wp b P)" by(blast)
  with wp_u_a have "wp a (wp b P) \<tturnstile> wlp a (wp b P)" by(auto)
  also {
    from wp_u_b and uP have "wp b P \<tturnstile> wlp b P" by(blast)
    with h_wlp_a and h_wlp_b and h_wp_b and uP
    have "wlp a (wp b P) \<tturnstile> wlp a (wlp b P)"
      by(blast intro:nearly_healthy_monoD[OF h_wlp_a])
  }
  finally show "wp a (wp b P) \<tturnstile> wlp a (wlp b P)" .
qed

lemma wp_under_wlp_PC:
  assumes h_wp_a:  "healthy (wp a)"
      and h_wlp_a: "nearly_healthy (wlp a)"
      and h_wp_b:  "healthy (wp b)"
      and h_wlp_b: "nearly_healthy (wlp b)"
      and wp_u_a:  "wp_under_wlp a"
      and wp_u_b:  "wp_under_wlp b"
      and uP:      "unitary P"
  shows "wp_under_wlp (a \<^bsub>P\<^esub>\<oplus> b)"
proof(rule wp_under_wlpI, unfold wp_eval, rule le_funI)
  fix Q::"'a \<Rightarrow> real" and s
  assume uQ: "unitary Q"
  from uP have "P s \<le> 1" by(blast)
  hence "0 \<le> 1 - P s" by(simp)
  moreover
  from uQ and wp_u_b have "wp b Q s \<le> wlp b Q s" by(blast)
  ultimately
  have "(1 - P s) * wp b Q s \<le> (1 - P s) * wlp b Q s"
    by(blast intro:mult_left_mono)

  moreover {
    from uQ and wp_u_a have "wp a Q s \<le> wlp a Q s" by(blast)
    with uP have "P s * wp a Q s \<le> P s * wlp a Q s"
      by(blast intro:mult_left_mono)
  }

  ultimately
  show "P s * wp  a Q s + (1 - P s) * wp  b Q s \<le>
        P s * wlp a Q s + (1 - P s) * wlp b Q s"
    by(blast intro: add_mono)
qed

lemma wp_under_wlp_DC:
  assumes wp_u_a:  "wp_under_wlp a"
      and wp_u_b:  "wp_under_wlp b"
  shows "wp_under_wlp (a \<Sqinter> b)"
proof(rule wp_under_wlpI, unfold wp_eval, rule le_funI)
  fix Q::"'a \<Rightarrow> real" and s
  assume uQ: "unitary Q"

  from wp_u_a uQ have "wp a Q s \<le> wlp a Q s" by(blast)
  moreover
  from wp_u_b uQ have "wp b Q s \<le> wlp b Q s" by(blast)
  ultimately
  show "min (wp a Q s) (wp b Q s) \<le> min (wlp a Q s) (wlp b Q s)"
    by(auto)
qed

lemma wp_under_wlp_SetPC:
  assumes wp_u_f:  "\<And>s a. a \<in> supp (P s) \<Longrightarrow> wp_under_wlp (f a)"
      and nP:      "\<And>s a. a \<in> supp (P s) \<Longrightarrow> 0 \<le> P s a"
  shows "wp_under_wlp (SetPC f P)"
proof(rule wp_under_wlpI, unfold wp_eval, rule le_funI)
  fix Q::"'a \<Rightarrow> real" and s
  assume uQ: "unitary Q"

  from wp_u_f uQ nP
  show "(\<Sum>a\<in>supp (P s). P s a * wp (f a) Q s) \<le> (\<Sum>a\<in>supp (P s). P s a * wlp (f a) Q s)"
    by(auto intro!:sum_mono mult_left_mono)
qed

lemma wp_under_wlp_SetDC:
  assumes wp_u_f:  "\<And>s a. a \<in> S s \<Longrightarrow> wp_under_wlp (f a)"
      and hf:      "\<And>s a. a \<in> S s \<Longrightarrow> healthy (wp (f a))"
      and nS:      "\<And>s. S s \<noteq> {}"
  shows "wp_under_wlp (SetDC f S)"
proof(rule wp_under_wlpI, rule le_funI, unfold wp_eval)
  fix Q::"'a \<Rightarrow> real" and s
  assume uQ: "unitary Q"

  show "Inf ((\<lambda>a. wp (f a) Q s) ` S s) \<le> Inf ((\<lambda>a. wlp (f a) Q s) ` S s)"
  proof(rule cInf_mono)
    from nS show "(\<lambda>a. wlp (f a) Q s) ` S s \<noteq> {}" by(blast)

    fix x assume xin: "x \<in> (\<lambda>a. wlp (f a) Q s) ` S s"
    then obtain a where ain: "a \<in> S s" and xrw: "x = wlp (f a) Q s"
      by(blast)
    with wp_u_f uQ
    have "wp (f a) Q s \<le> wlp (f a) Q s" by(blast)
    moreover from ain have "wp (f a) Q s \<in> (\<lambda>a. wp (f a) Q s) ` S s"
      by(blast)
    ultimately show "\<exists>y\<in> (\<lambda>a. wp (f a) Q s) ` S s. y \<le> x"
      by(auto simp:xrw)

  next
    fix y assume yin: "y \<in> (\<lambda>a. wp (f a) Q s) ` S s"
    then obtain a where ain: "a \<in> S s" and yrw: "y = wp (f a) Q s"
      by(blast)
    with hf uQ have "unitary (wp (f a) Q)" by(auto)
    with yrw show "0 \<le> y" by(auto)
  qed
qed

lemma wp_under_wlp_Embed:
  "wp_under_wlp (Embed t)"
  by(rule wp_under_wlpI, unfold wp_eval, blast)

lemma wp_under_wlp_loop:
  fixes body::"'s prog"
  assumes hwp: "healthy (wp body)"
      and hwlp: "nearly_healthy (wlp body)"
      and wp_under: "wp_under_wlp body"
  shows "wp_under_wlp (do G \<longrightarrow> body od)"
proof(rule wp_under_wlpI)
  fix P::"'s expect"
  assume uP: "unitary P" hence sP: "sound P" by(auto)

  let "?X Q s" = "\<guillemotleft>G\<guillemotright> s * wp body Q s + \<guillemotleft>\<N> G\<guillemotright> s * P s"
  let "?Y Q s" = "\<guillemotleft>G\<guillemotright> s * wlp body Q s + \<guillemotleft>\<N> G\<guillemotright> s * P s"

  show "wp (do G \<longrightarrow> body od) P \<tturnstile> wlp (do G \<longrightarrow> body od) P"
  proof(simp add:hwp hwlp sP uP wp_Loop1 wlp_Loop1, rule gfp_exp_upperbound)
    thm lfp_loop_fp
    from hwp sP have "lfp_exp ?X = ?X (lfp_exp ?X)"
      by(rule lfp_wp_loop_unfold)
    hence "lfp_exp ?X \<tturnstile> ?X (lfp_exp ?X)" by(simp)
    also {
      from hwp uP have "wp body (lfp_exp ?X) \<tturnstile> wlp body (lfp_exp ?X)"
        by(auto intro:wp_under_wlpD[OF wp_under] lfp_loop_unitary)
      hence "?X (lfp_exp ?X) \<tturnstile> ?Y (lfp_exp ?X)"
        by(auto intro:add_mono mult_left_mono)
    }
    finally show "lfp_exp ?X \<tturnstile> ?Y (lfp_exp ?X)" .
    from hwp uP show "unitary (lfp_exp ?X)"
      by(auto intro:lfp_loop_unitary)
  qed
qed

lemma wp_under_wlp_repeat:
  "\<lbrakk> healthy (wp a); nearly_healthy (wlp a); wp_under_wlp a \<rbrakk> \<Longrightarrow>
   wp_under_wlp (repeat n a)"
  by(induct n, auto intro!:wp_under_wlp_Skip wp_under_wlp_Seq healthy_intros)

lemma wp_under_wlp_Bind:
  "\<lbrakk> \<And>s. wp_under_wlp (a (f s)) \<rbrakk> \<Longrightarrow> wp_under_wlp (Bind f a)"
  unfolding wp_under_wlp_def by(auto simp:wp_eval)

lemmas wp_under_wlp_intros =
  wp_under_wlp_Abort wp_under_wlp_Skip
  wp_under_wlp_Apply wp_under_wlp_Seq
  wp_under_wlp_PC    wp_under_wlp_DC
  wp_under_wlp_SetPC wp_under_wlp_SetDC
  wp_under_wlp_Embed wp_under_wlp_loop
  wp_under_wlp_repeat wp_under_wlp_Bind

subsection \<open>Sub-Distributivity of Conjunction\<close>

definition
  sub_distrib_pconj :: "'s prog \<Rightarrow> bool"
where
  "sub_distrib_pconj prog \<equiv>
   \<forall>P Q. unitary P \<longrightarrow> unitary Q \<longrightarrow>
         wlp prog P && wp prog Q \<tturnstile> wp prog (P && Q)"

lemma sub_distrib_pconjI[intro]:
  "\<lbrakk>\<And>P Q. \<lbrakk> unitary P; unitary Q \<rbrakk> \<Longrightarrow>  wlp prog P && wp prog Q \<tturnstile> wp prog (P && Q) \<rbrakk> \<Longrightarrow>
    sub_distrib_pconj prog"
  unfolding sub_distrib_pconj_def by(simp)

lemma sub_distrib_pconjD[dest]:
  "\<And>P Q. \<lbrakk> sub_distrib_pconj prog; unitary P; unitary Q \<rbrakk> \<Longrightarrow>
   wlp prog P && wp prog Q \<tturnstile> wp prog (P && Q)"
  unfolding sub_distrib_pconj_def by(simp)

lemma sdp_Abort:
  "sub_distrib_pconj Abort"
  by(rule sub_distrib_pconjI, unfold wp_eval, auto intro:exp_conj_rzero)

lemma sdp_Skip:
  "sub_distrib_pconj Skip"
  by(rule sub_distrib_pconjI, simp add:wp_eval)

lemma sdp_Seq:
  fixes a and b
  assumes sdp_a:   "sub_distrib_pconj a"
      and sdp_b:   "sub_distrib_pconj b"
      and h_wp_a:  "healthy (wp a)"
      and h_wp_b:  "healthy (wp b)"
      and h_wlp_b: "nearly_healthy (wlp b)"
  shows "sub_distrib_pconj (a ;; b)"
proof(rule sub_distrib_pconjI, unfold wp_eval o_def)
  fix P::"'a \<Rightarrow> real" and Q::"'a \<Rightarrow> real"
  assume uP: "unitary P" and uQ: "unitary Q"

  with h_wp_b and h_wlp_b
  have "wlp a (wlp b P) && wp a (wp b Q) \<tturnstile> wp a (wlp b P && wp b Q)"
    by(blast intro!:sub_distrib_pconjD[OF sdp_a])
  also {
    from sdp_b and uP and uQ
    have "wlp b P && wp b Q \<tturnstile> wp b (P && Q)" by(blast)
    with h_wp_a h_wp_b h_wlp_b uP uQ
    have "wp a (wlp b P && wp b Q) \<tturnstile> wp a (wp b (P && Q))"
      by(blast intro!:mono_transD[OF healthy_monoD, OF h_wp_a] unitary_sound
                      unitary_intros sound_intros)
  }
  finally show "wlp a (wlp b P) && wp a (wp b Q) \<tturnstile> wp a (wp b (P && Q))" .
qed

lemma sdp_Apply:
  "sub_distrib_pconj (Apply f)"
  by(rule sub_distrib_pconjI, simp add:wp_eval)

lemma sdp_DC:
  fixes a::"'s prog" and b
  assumes sdp_a:   "sub_distrib_pconj a"
      and sdp_b:   "sub_distrib_pconj b"
      and h_wp_a:  "healthy (wp a)"
      and h_wp_b:  "healthy (wp b)"
      and h_wlp_b: "nearly_healthy (wlp b)"
  shows "sub_distrib_pconj (a \<Sqinter> b)"
proof(rule sub_distrib_pconjI, unfold wp_eval, rule le_funI)
  fix P::"'s \<Rightarrow> real" and Q::"'s \<Rightarrow> real" and s::'s
  assume uP: "unitary P" and uQ: "unitary Q"

  have "((\<lambda>s. min (wlp a P s) (wlp b P s)) &&
         (\<lambda>s. min (wp a Q s) (wp b Q s))) s \<le>
        min (wlp a P s .& wp a Q s) (wlp b P s .& wp b Q s)"
    unfolding exp_conj_def by(rule min_pconj)
  also {
    have "(\<lambda>s. wlp a P s .& wp a Q s) = wlp a P && wp a Q"
      by(simp add:exp_conj_def)
    also from sdp_a uP uQ have "... \<tturnstile> wp a (P && Q)"
      by(blast dest:sub_distrib_pconjD)
    finally have "wlp a P s .& wp a Q s \<le> wp a (P && Q) s"
      by(rule le_funD)
    moreover {
      have "(\<lambda>s. wlp b P s .& wp b Q s) = wlp b P && wp b Q"
        by(simp add:exp_conj_def)
    also from sdp_b uP uQ have "... \<tturnstile> wp b (P && Q)"
      by(blast)
    finally have "wlp b P s .& wp b Q s \<le> wp b (P && Q) s"
      by(rule le_funD)
    }
    ultimately
    have "min (wlp a P s .& wp a Q s) (wlp b P s .& wp b Q s) \<le>
          min (wp a (P && Q) s) (wp b (P && Q) s)" by(auto)
  }
  finally
  show "((\<lambda>s. min (wlp a P s) (wlp b P s)) &&
         (\<lambda>s. min (wp a Q s) (wp b Q s))) s \<le>
        min (wp a (P && Q) s) (wp b (P && Q) s)" .
qed

lemma sdp_PC:
  fixes a::"'s prog" and b
  assumes sdp_a:   "sub_distrib_pconj a"
      and sdp_b:   "sub_distrib_pconj b"
      and h_wp_a:  "healthy (wp a)"
      and h_wp_b:  "healthy (wp b)"
      and h_wlp_b: "nearly_healthy (wlp b)"
      and uP:      "unitary P"
  shows "sub_distrib_pconj (a \<^bsub>P\<^esub>\<oplus> b)"
proof(rule sub_distrib_pconjI, unfold wp_eval, rule le_funI)
  fix Q::"'s \<Rightarrow> real" and R::"'s \<Rightarrow> real" and s::'s
  assume uQ: "unitary Q" and uR: "unitary R"

  have nnA: "0 \<le> P s" and nnB: "P s \<le> 1"
    using uP by(auto simp:sign_simps)
  note nn = nnA nnB

  have "((\<lambda>s. P s * wlp a Q s + (1 - P s) * wlp b Q s) &&
         (\<lambda>s. P s *  wp a R s + (1 - P s) *  wp b R s)) s =
        ((P s * wlp a Q s + (1 - P s) * wlp b Q s) +
         (P s *  wp a R s + (1 - P s) *  wp b R s)) \<ominus> 1"
    by(simp add:exp_conj_def pconj_def)
  also have "... = P s *       (wlp a Q s + wp a R s) +
                   (1 - P s) * (wlp b Q s + wp b R s) \<ominus> 1"
    by(simp add:field_simps)
  also have "... = P s *       (wlp a Q s + wp a R s) +
                   (1 - P s) * (wlp b Q s + wp b R s) \<ominus>
                   (P s + (1 - P s))"
    by(simp)
  also have "... \<le> (P s *       (wlp a Q s + wp a R s) \<ominus> P s) +
                   ((1 - P s) * (wlp b Q s + wp b R s) \<ominus> (1 - P s))"
    by(rule tminus_add_mono)
  also have "... = (P s       * (wlp a Q s + wp a R s \<ominus> 1)) +
                   ((1 - P s) * (wlp b Q s + wp b R s \<ominus> 1))"
    by(simp add:nn tminus_left_distrib)
  also have "... = P s *       ((wlp a Q && wp a R) s) +
                   (1 - P s) * ((wlp b Q && wp b R) s)"
    by(simp add:exp_conj_def pconj_def)
  also {
    from sdp_a sdp_b uQ uR
    have "P s * (wlp a Q && wp a R) s \<le> P s * wp a (Q && R) s"
     and "(1 - P s) * (wlp b Q && wp b R) s \<le> (1 - P s) * wp b (Q && R) s"
       by (simp_all add: entailsD mult_left_mono nn sub_distrib_pconjD)
    hence "P s *       ((wlp a Q && wp a R) s) +
           (1 - P s) * ((wlp b Q && wp b R) s) \<le>
           P s * wp a (Q && R) s + (1 - P s) * wp b (Q && R) s"
      by(auto)
  }
  finally show "((\<lambda>s. P s * wlp a Q s + (1 - P s) * wlp b Q s) &&
                 (\<lambda>s. P s *  wp a R s + (1 - P s) *  wp b R s)) s \<le>
                P s * wp a (Q && R) s + (1 - P s) * wp b (Q && R) s" .
qed

lemma sdp_Embed:
  "\<lbrakk> \<And>P Q. \<lbrakk> unitary P; unitary Q \<rbrakk> \<Longrightarrow> t P && t Q \<tturnstile> t (P && Q) \<rbrakk> \<Longrightarrow>
   sub_distrib_pconj (Embed t)"
  by(auto simp:wp_eval)

lemma sdp_repeat:
  fixes a::"'s prog"
  assumes sdpa: "sub_distrib_pconj a"
      and hwp: "healthy (wp a)" and hwlp: "nearly_healthy (wlp a)"
  shows "sub_distrib_pconj (repeat n a)" (is "?X n")
proof(induct n)
  show "?X 0" by(simp add:sdp_Skip)
  fix n assume IH: "?X n"
  show "?X (Suc n)"
  proof(rule sub_distrib_pconjI, simp add:wp_eval)
    fix P::"'s \<Rightarrow> real" and Q::"'s \<Rightarrow> real"
    assume uP: "unitary P" and uQ: "unitary Q"
    from assms have hwlpa: "nearly_healthy (wlp (repeat n a))"
                and hwpa:  "healthy (wp (repeat n a))"
      by(auto intro:healthy_intros)
    from uP and hwlpa have "unitary (wlp (repeat n a) P)" by(blast)
    moreover from uQ and hwpa have "unitary (wp (repeat n a) Q)" by(blast)
    ultimately
    have "wlp a (wlp (repeat n a) P) && wp a (wp (repeat n a) Q) \<tturnstile>
          wp a (wlp (repeat n a) P && wp (repeat n a) Q)"
      using sdpa by(blast)
    also {
      from hwlp have "nearly_healthy (wlp (repeat n a))" by(rule healthy_intros)
      with uP have "sound (wlp (repeat n a) P)" by(auto)
      moreover from hwp uQ have "sound (wp (repeat n a) Q)"
        by(auto intro:healthy_intros)
      ultimately have "sound (wlp (repeat n a) P && wp (repeat n a) Q)"
        by(rule exp_conj_sound)
      moreover {
        from uP uQ have "sound (P && Q)" by(auto intro:exp_conj_sound)
        with hwp have "sound (wp (repeat n a) (P && Q))"
          by(auto intro:healthy_intros)
      }
      moreover from uP uQ IH
      have "wlp (repeat n a) P && wp (repeat n a) Q \<tturnstile> wp (repeat n a) (P && Q)"
        by(blast)
      ultimately
      have "wp a (wlp (repeat n a) P && wp (repeat n a) Q) \<tturnstile>
            wp a (wp (repeat n a) (P && Q))"
        by(rule mono_transD[OF healthy_monoD, OF hwp])
    }
    finally show "wlp a (wlp (repeat n a) P) && wp a (wp (repeat n a) Q) \<tturnstile>
                  wp a (wp (repeat n a) (P && Q))" .
  qed
qed

lemma sdp_SetPC:
  fixes p::"'a \<Rightarrow> 's prog"
  assumes sdp: "\<And>s a. a \<in> supp (P s) \<Longrightarrow> sub_distrib_pconj (p a)"
      and fin: "\<And>s. finite (supp (P s))"
      and nnp: "\<And>s a. 0 \<le> P s a"
      and sub: "\<And>s. sum (P s) (supp (P s)) \<le> 1"
  shows "sub_distrib_pconj (SetPC p P)"
proof(rule sub_distrib_pconjI, simp add:wp_eval, rule le_funI)
  fix Q::"'s \<Rightarrow> real" and R::"'s \<Rightarrow> real" and s::'s
  assume uQ: "unitary Q" and uR: "unitary R"
  have "((\<lambda>s. \<Sum>a\<in>supp (P s). P s a * wlp (p a) Q s) &&
         (\<lambda>s. \<Sum>a\<in>supp (P s). P s a *  wp (p a) R s)) s =
        (\<Sum>a\<in>supp (P s). P s a * wlp (p a) Q s) + (\<Sum>a\<in>supp (P s). P s a * wp (p a) R s) \<ominus> 1"
    by(simp add:exp_conj_def pconj_def)
  also have "... = (\<Sum>a\<in>supp (P s). P s a * (wlp (p a) Q s + wp (p a) R s)) \<ominus> 1"
    by(simp add: sum.distrib field_simps)
  also from sub
  have "... \<le> (\<Sum>a\<in>supp (P s). P s a * (wlp (p a) Q s + wp (p a) R s)) \<ominus>
              (\<Sum>a\<in>supp (P s). P s a)"
    by(rule tminus_right_antimono)
  also from fin
  have "... \<le> (\<Sum>a\<in>supp (P s). P s a * (wlp (p a) Q s + wp (p a) R s) \<ominus> P s a)"
    by(rule tminus_sum_mono)
  also from nnp
  have "... = (\<Sum>a\<in>supp (P s). P s a * (wlp (p a) Q s + wp (p a) R s \<ominus> 1))"
    by(simp add:tminus_left_distrib)
  also have "... = (\<Sum>a\<in>supp (P s). P s a * (wlp (p a) Q && wp (p a) R) s)"
    by(simp add:pconj_def exp_conj_def)
  also {
    from sdp uQ uR
    have "\<And>a. a \<in> supp (P s) \<Longrightarrow> wlp (p a) Q && wp (p a) R \<tturnstile> wp (p a) (Q && R)"
      by(blast intro:sub_distrib_pconjD)
    with nnp
    have "(\<Sum>a\<in>supp (P s). P s a * (wlp (p a) Q && wp (p a) R) s) \<le>
          (\<Sum>a\<in>supp (P s). P s a * (wp (p a) (Q && R)) s)"
      by(blast intro:sum_mono mult_left_mono)
  }
  finally show "((\<lambda>s. \<Sum>a\<in>supp (P s). P s a * wlp (p a) Q s) &&
                 (\<lambda>s. \<Sum>a\<in>supp (P s). P s a * wp (p a) R s)) s \<le>
                (\<Sum>a\<in>supp (P s). P s a * wp (p a) (Q && R) s)" .
qed

lemma sdp_SetDC:
  fixes p::"'a \<Rightarrow> 's prog"
  assumes sdp: "\<And>s a. a \<in> S s \<Longrightarrow> sub_distrib_pconj (p a)"
      and hwp: "\<And>s a. a \<in> S s \<Longrightarrow> healthy (wp (p a))"
      and hwlp: "\<And>s a. a \<in> S s \<Longrightarrow> nearly_healthy (wlp (p a))"
      and ne:  "\<And>s. S s \<noteq> {}"
  shows "sub_distrib_pconj (SetDC p S)"
proof(rule sub_distrib_pconjI, rule le_funI)
  fix P::"'s \<Rightarrow> real" and Q::"'s \<Rightarrow> real" and s::'s
  assume uP: "unitary P" and uQ: "unitary Q"

  from uP hwlp
  have "\<And>x. x \<in> (\<lambda>a. wlp (p a) P) ` S s \<Longrightarrow> unitary x" by(auto)
  hence "\<And>y. y \<in> (\<lambda>a. wlp (p a) P s) ` S s \<Longrightarrow> 0 \<le> y" by(auto)
  hence "\<And>a. a \<in> S s \<Longrightarrow> wlp (SetDC p S) P s \<le> wlp (p a) P s"
    unfolding wp_eval by(intro cInf_lower bdd_belowI, auto)
  moreover {
    from uQ hwp have "\<And>a. a \<in> S s \<Longrightarrow>  0 \<le> wp (p a) Q s" by(blast)
    hence "\<And>a. a \<in> S s \<Longrightarrow> wp (SetDC p S) Q s \<le> wp (p a) Q s"
    unfolding wp_eval by(intro cInf_lower bdd_belowI, auto)
  }
  ultimately
  have "\<And>a. a \<in> S s \<Longrightarrow> wlp (SetDC p S) P s + wp (SetDC p S) Q s \<ominus> 1 \<le>
                      wlp (p a) P s + wp (p a) Q s \<ominus> 1"
    by(auto intro:tminus_left_mono add_mono)
  also have "\<And>a. wlp (p a) P s + wp (p a) Q s \<ominus> 1 = (wlp (p a) P && wp (p a) Q) s"
    by(simp add:exp_conj_def pconj_def)
  also from sdp uP uQ
  have "\<And>a. a \<in> S s \<Longrightarrow> ... a \<le> wp (p a) (P && Q) s"
    by(blast)
  also have "\<And>a. ... a = wp (p a) (\<lambda>s. P s + Q s \<ominus> 1) s"
    by(simp add:exp_conj_def pconj_def)
  finally
  show "(wlp (SetDC p S) P && wp (SetDC p S) Q) s \<le> wp (SetDC p S) (P && Q) s"
    unfolding exp_conj_def pconj_def wp_eval
    using ne by(blast intro!:cInf_greatest)
qed

lemma sdp_Bind:
  "\<lbrakk> \<And>s. sub_distrib_pconj (p (f s)) \<rbrakk> \<Longrightarrow> sub_distrib_pconj (Bind f p)"
  unfolding sub_distrib_pconj_def wp_eval exp_conj_def pconj_def
  by(blast)

text \<open>For loops, we again appeal to our transfinite induction principle, this time taking
advantage of the simultaneous treatment of both strict and liberal transformers.\<close>
lemma sdp_loop:
  fixes body::"'s prog"
  assumes sdp_body: "sub_distrib_pconj body"
      and hwlp: "nearly_healthy (wlp body)"
      and hwp:  "healthy (wp body)"
  shows "sub_distrib_pconj (do G \<longrightarrow> body od)"
proof(rule sub_distrib_pconjI, rule loop_induct[OF hwp hwlp])
  fix P Q::"'s expect" and S::"('s trans \<times> 's trans) set"
  assume uP: "unitary P" and uQ: "unitary Q"
     and ffst: "\<forall>x\<in>S. feasible (fst x)"
     and usnd: "\<forall>x\<in>S. \<forall>Q. unitary Q \<longrightarrow> unitary (snd x Q)"
     and IH: "\<forall>x\<in>S. snd x P && fst x Q \<tturnstile> fst x (P && Q)"

  show "Inf_utrans (snd ` S) P && Sup_trans (fst ` S) Q \<tturnstile>
                  Sup_trans (fst ` S) (P && Q)"
  proof(cases)
    assume "S = {}"
    thus ?thesis
      by(simp add:Inf_trans_def Sup_trans_def Inf_utrans_def
                  Inf_exp_def Sup_exp_def exp_conj_def)
  next
    assume ne: "S \<noteq> {}"

    let "?f s" = "1 + Sup_trans (fst ` S) (P && Q) s - Inf_utrans (snd ` S) P s"

    from ne obtain t where tin: "t \<in> fst ` S" by(auto)
    from ne obtain u where uin: "u \<in> snd ` S" by(auto)

    from tin ffst uP uQ have utPQ: "unitary (t (P && Q))"
      by(auto intro:exp_conj_unitary)
    hence "\<And>s. 0 \<le> t (P && Q) s" by(auto)
    also {
      from ffst tin have le: "le_utrans t (Sup_trans (fst ` S))"
        by(auto intro:Sup_trans_upper)
      with uP uQ have "\<And>s. t (P && Q) s \<le> Sup_trans (fst ` S) (P && Q) s"
        by(auto intro:exp_conj_unitary)
    }
    finally have nn_rhs: "\<And>s. 0 \<le> Sup_trans (fst ` S) (P && Q) s" .

    have "\<And>R. Inf_utrans (snd ` S) P && R \<tturnstile> Sup_trans (fst ` S) (P && Q) \<Longrightarrow> R \<le> ?f"
    proof(rule contrapos_pp, assumption)
      fix R
      assume "\<not> R \<le> ?f"
      then obtain s where "\<not> R s \<le> ?f s" by(auto)
      hence gt: "?f s < R s" by(simp)

      from nn_rhs have g1: "1 \<le> 1 + Sup_trans (fst ` S) (P && Q) s" by(auto)
      hence "Sup_trans (fst ` S) (P && Q) s = Inf_utrans (snd ` S) P s .& ?f s"
        by(simp add:pconj_def)
      also from g1 have "... = Inf_utrans (snd ` S) P s + ?f s - 1"
        by(simp)
      also from gt have "... < Inf_utrans (snd ` S) P s + R s - 1"
        by(simp)
      also {
        with g1 have "1 \<le> Inf_utrans (snd ` S) P s + R s"
          by(simp)
        hence "Inf_utrans (snd ` S) P s + R s - 1 = Inf_utrans (snd ` S) P s .& R s"
          by(simp add:pconj_def)
      }
      finally
      have "\<not> (Inf_utrans (snd ` S) P && R) s \<le> Sup_trans (fst ` S) (P && Q) s"
        by(simp add:exp_conj_def)
      thus "\<not> Inf_utrans (snd ` S) P && R \<tturnstile> Sup_trans (fst ` S) (P && Q)"
        by(auto)
    qed

    moreover have "\<forall>t\<in>fst ` S. Inf_utrans (snd ` S) P && t Q  \<tturnstile> Sup_trans (fst ` S) (P && Q)"
    proof
      fix t assume tin: "t \<in> fst ` S"
      then obtain x where xin: "x \<in> S" and fx: "t = fst x" by(auto)

      from xin have "snd x \<in> snd ` S" by(auto)
      with uP usnd have "Inf_utrans (snd ` S) P \<tturnstile> snd x P"
        by(auto intro:le_utransD[OF Inf_utrans_lower])
      hence "Inf_utrans (snd ` S) P && fst x Q \<tturnstile> snd x P && fst x Q"
        by(auto intro:entails_frame)
      also from xin IH have "... \<tturnstile> fst x (P && Q)"
        by(auto)
      also from xin ffst exp_conj_unitary[OF uP uQ]
      have "... \<tturnstile> Sup_trans (fst ` S) (P && Q)"
        by(auto intro:le_utransD[OF Sup_trans_upper])
      finally show "Inf_utrans (snd ` S) P && t Q \<tturnstile> Sup_trans (fst ` S) (P && Q)"
        by(simp add:fx)
    qed
    ultimately have bt: "\<forall>t\<in>fst ` S. t Q \<tturnstile> ?f" by(blast)

    have "Sup_trans (fst ` S) Q = Sup_exp {t Q |t. t \<in> fst ` S}"
      by(simp add:Sup_trans_def)
    also have "... \<tturnstile> ?f"
    proof(rule Sup_exp_least)
      from bt show " \<forall>R\<in>{t Q |t. t \<in> fst ` S}. R \<tturnstile> ?f" by(blast)
      from ne obtain t where tin: "t \<in> fst ` S" by(auto)
      with ffst uQ have "unitary (t Q)" by(auto)
      hence "\<lambda>s. 0 \<tturnstile> t Q" by(auto)
      also from tin bt have "... \<tturnstile> ?f" by(auto)
      finally show "nneg (\<lambda>s. 1 + Sup_trans (fst ` S) (P && Q) s -
                          Inf_utrans (snd ` S) P s)"
        by(auto)
    qed
    finally have "Inf_utrans (snd ` S) P && Sup_trans (fst ` S) Q \<tturnstile>
                  Inf_utrans (snd ` S) P && ?f"
      by(auto intro:entails_frame)
    also from nn_rhs have "... \<tturnstile> Sup_trans (fst ` S) (P && Q)"
      by(simp add:exp_conj_def pconj_def)
    finally show ?thesis .
  qed

next
  fix P Q::"'s expect" and t u::"'s trans"
  assume uP: "unitary P" and uQ: "unitary Q"
     and ft: "feasible t"
     and uu: "\<And>Q. unitary Q \<Longrightarrow> unitary (u Q)"
     and IH: "u P && t Q \<tturnstile> t (P && Q)"
  show "wlp (body ;; Embed u \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip) P &&
        wp  (body ;; Embed t \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip) Q \<tturnstile>
        wp  (body ;; Embed t \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip) (P && Q)"
  proof(rule le_funI, simp add:wp_eval exp_conj_def pconj_def)
    fix s::'s
    have "\<guillemotleft> G \<guillemotright> s * wlp body (u P) s + (1 - \<guillemotleft> G \<guillemotright> s) * P s +
          (\<guillemotleft> G \<guillemotright> s * wp body (t Q) s + (1 - \<guillemotleft> G \<guillemotright> s) * Q s) \<ominus> 1 =
          (\<guillemotleft> G \<guillemotright> s * wlp body (u P) s + \<guillemotleft> G \<guillemotright> s * wp body (t Q) s) +
           ((1 - \<guillemotleft> G \<guillemotright> s) * P s + (1 - \<guillemotleft> G \<guillemotright> s) * Q s) \<ominus> (\<guillemotleft>G\<guillemotright> s + (1 - \<guillemotleft>G\<guillemotright> s))"
      by(simp add:ac_simps)
    also have "... \<le>
          (\<guillemotleft> G \<guillemotright> s * wlp body (u P) s + \<guillemotleft> G \<guillemotright> s * wp body (t Q) s \<ominus> \<guillemotleft>G\<guillemotright> s) +
           ((1 - \<guillemotleft> G \<guillemotright> s) * P s + (1 - \<guillemotleft> G \<guillemotright> s) * Q s \<ominus> (1 - \<guillemotleft>G\<guillemotright> s))"
      by(rule tminus_add_mono)
    also have "... =
          \<guillemotleft> G \<guillemotright> s * (wlp body (u P) s + wp body (t Q) s \<ominus> 1) +
           (1 - \<guillemotleft> G \<guillemotright> s) * (P s + Q s \<ominus> 1)"
       by(simp add:tminus_left_distrib distrib_left)
    also {
      from uP uQ ft uu
      have "wlp body (u P) && wp body (t Q) \<tturnstile> wp body (u P && t Q)"
        by(auto intro:sub_distrib_pconjD[OF sdp_body])
      also from IH unitary_sound[OF uP] unitary_sound[OF uQ] ft
                   unitary_sound[OF uu[OF uP]]
      have "\<dots> \<le> wp body (t (P && Q))"
        by(blast intro!:mono_transD[OF healthy_monoD, OF hwp] exp_conj_sound)
      finally have "wlp body (u P) s + wp body (t Q) s \<ominus> 1 \<le>
                    wp body (t (\<lambda>s. P s + Q s \<ominus> 1)) s"
        by(auto simp:exp_conj_def pconj_def)
      hence "\<guillemotleft> G \<guillemotright> s * (wlp body (u P) s + wp body (t Q) s \<ominus> 1) +
             (1 - \<guillemotleft> G \<guillemotright> s) * (P s + Q s \<ominus> 1) \<le>
             \<guillemotleft> G \<guillemotright> s * wp body (t (\<lambda>s. P s + Q s \<ominus> 1)) s +
             (1 - \<guillemotleft> G \<guillemotright> s) * (P s + Q s \<ominus> 1)"
        by(auto intro:add_right_mono mult_left_mono)
    }
    finally
    show "\<guillemotleft> G \<guillemotright> s * wlp body (u P) s + (1 - \<guillemotleft> G \<guillemotright> s) * P s +
          (\<guillemotleft> G \<guillemotright> s * wp body (t Q) s + (1 - \<guillemotleft> G \<guillemotright> s) * Q s) \<ominus> 1 \<le>
          \<guillemotleft> G \<guillemotright> s * wp body (t (\<lambda>s. P s + Q s \<ominus> 1)) s +
          (1 - \<guillemotleft> G \<guillemotright> s) * (P s + Q s \<ominus> 1)" .
  qed
next
  fix P Q::"'s expect" and t t' u u'::"'s trans"
  assume "unitary P" "unitary Q"
         "equiv_trans t t'" "equiv_utrans u u'"
         "u P && t Q \<tturnstile> t (P && Q)"
  thus "u' P && t' Q \<tturnstile> t' (P && Q)"
    by(simp add:equiv_transD unitary_sound equiv_utransD exp_conj_unitary)
qed

lemmas sdp_intros =
  sdp_Abort  sdp_Skip  sdp_Apply
  sdp_Seq    sdp_DC    sdp_PC
  sdp_SetPC  sdp_SetDC sdp_Embed
  sdp_repeat sdp_Bind  sdp_loop

subsection \<open>The Well-Defined Predicate.\<close>

definition
  well_def :: "'s prog \<Rightarrow> bool"
where
  "well_def prog \<equiv> healthy (wp prog) \<and> nearly_healthy (wlp prog)
                 \<and> wp_under_wlp prog \<and> sub_distrib_pconj prog
                 \<and> sublinear (wp prog) \<and> bd_cts (wp prog)"

lemma well_defI[intro]:
  "\<lbrakk> healthy (wp prog); nearly_healthy (wlp prog);
     wp_under_wlp prog; sub_distrib_pconj prog; sublinear (wp prog);
     bd_cts (wp prog) \<rbrakk> \<Longrightarrow>
   well_def prog"
  unfolding well_def_def by(simp)

lemma well_def_wp_healthy[dest]:
  "well_def prog \<Longrightarrow> healthy (wp prog)"
  unfolding well_def_def by(simp)

lemma well_def_wlp_nearly_healthy[dest]:
  "well_def prog \<Longrightarrow> nearly_healthy (wlp prog)"
  unfolding well_def_def by(simp)

lemma well_def_wp_under[dest]:
  "well_def prog \<Longrightarrow> wp_under_wlp prog"
  unfolding well_def_def by(simp)

lemma well_def_sdp[dest]:
  "well_def prog \<Longrightarrow> sub_distrib_pconj prog"
  unfolding well_def_def by(simp)

lemma well_def_wp_sublinear[dest]:
  "well_def prog \<Longrightarrow> sublinear (wp prog)"
  unfolding well_def_def by(simp)

lemma well_def_wp_cts[dest]:
  "well_def prog \<Longrightarrow> bd_cts (wp prog)"
  unfolding well_def_def by(simp)

lemmas wd_dests =
  well_def_wp_healthy well_def_wlp_nearly_healthy
  well_def_wp_under well_def_sdp
  well_def_wp_sublinear well_def_wp_cts

lemma wd_Abort:
  "well_def Abort"
  by(blast intro:healthy_wp_Abort nearly_healthy_wlp_Abort
                 wp_under_wlp_Abort sdp_Abort sublinear_wp_Abort
                 cts_wp_Abort)

lemma wd_Skip:
  "well_def Skip"
  by(blast intro:healthy_wp_Skip nearly_healthy_wlp_Skip
                 wp_under_wlp_Skip sdp_Skip sublinear_wp_Skip
                 cts_wp_Skip)

lemma wd_Apply:
  "well_def (Apply f)"
  by(blast intro:healthy_wp_Apply nearly_healthy_wlp_Apply
                 wp_under_wlp_Apply sdp_Apply sublinear_wp_Apply
                 cts_wp_Apply)

lemma wd_Seq:
  "\<lbrakk> well_def a; well_def b \<rbrakk> \<Longrightarrow> well_def (a ;; b)"
  by(blast intro:healthy_wp_Seq nearly_healthy_wlp_Seq
                 wp_under_wlp_Seq sdp_Seq sublinear_wp_Seq
                 cts_wp_Seq)

lemma wd_PC:
  "\<lbrakk> well_def a; well_def b; unitary P \<rbrakk> \<Longrightarrow> well_def (a \<^bsub>P\<^esub>\<oplus> b)"
  by(blast intro:healthy_wp_PC nearly_healthy_wlp_PC
                 wp_under_wlp_PC sdp_PC sublinear_wp_PC
                 cts_wp_PC)

lemma wd_DC:
  "\<lbrakk> well_def a; well_def b \<rbrakk> \<Longrightarrow> well_def (a \<Sqinter> b)"
  by(blast intro:healthy_wp_DC nearly_healthy_wlp_DC
                 wp_under_wlp_DC sdp_DC sublinear_wp_DC
                 cts_wp_DC)

lemma wd_SetDC:
  "\<lbrakk> \<And>x s. x \<in> S s \<Longrightarrow> well_def (a x); \<And>s. S s \<noteq> {};
     \<And>s. finite (S s) \<rbrakk> \<Longrightarrow> well_def (SetDC a S)"
by (simp add: cts_wp_SetDC ex_in_conv healthy_intros(17) healthy_intros(18) sdp_intros(8) sublinear_intros(8) well_def_def wp_under_wlp_intros(8))


lemma wd_SetPC:
  "\<lbrakk> \<And>x s. x \<in> (supp (p s)) \<Longrightarrow> well_def (a x); \<And>s. unitary (p s); \<And>s. finite (supp (p s));
     \<And>s. sum (p s) (supp (p s)) \<le> 1 \<rbrakk> \<Longrightarrow> well_def (SetPC a p)"
  by(iprover intro!:well_defI healthy_wp_SetPC nearly_healthy_wlp_SetPC
                    wp_under_wlp_SetPC sdp_SetPC sublinear_wp_SetPC cts_wp_SetPC
             dest:wd_dests unitary_sound sound_nneg[OF unitary_sound] nnegD)

lemma wd_Embed:
  fixes t::"'s trans"
  assumes ht: "healthy t" and st: "sublinear t" and ct: "bd_cts t"
  shows "well_def (Embed t)"
proof(intro well_defI)
  from ht show "healthy (wp (Embed t))" "nearly_healthy (wlp (Embed t))"
    by(simp add:wp_def wlp_def Embed_def healthy_nearly_healthy)+
  from st show "sublinear (wp (Embed t))" by(simp add:wp_def Embed_def)
  show "wp_under_wlp (Embed t)" by(simp add:wp_under_wlp_def wp_eval)
  show "sub_distrib_pconj (Embed t)"
    by(rule sub_distrib_pconjI,
       auto intro:le_funI[OF sublinearD[OF st, where a=1 and b=1 and c=1, simplified]]
            simp:exp_conj_def pconj_def wp_def wlp_def Embed_def)
  from ct show "bd_cts (wp (Embed t))"
    by(simp add:wp_def Embed_def)
qed

lemma wd_repeat:
  "well_def a \<Longrightarrow> well_def (repeat n a)"
  by(blast intro:healthy_wp_repeat nearly_healthy_wlp_repeat
                 wp_under_wlp_repeat sdp_repeat sublinear_wp_repeat cts_wp_repeat)

lemma wd_Bind:
  "\<lbrakk> \<And>s. well_def (a (f s)) \<rbrakk> \<Longrightarrow> well_def (Bind f a)"
  by(blast intro:healthy_wp_Bind nearly_healthy_wlp_Bind
                 wp_under_wlp_Bind sdp_Bind sublinear_wp_Bind cts_wp_Bind)

lemma wd_loop:
  "well_def body \<Longrightarrow> well_def (do G \<longrightarrow> body od)"
  by(blast intro:healthy_wp_loop nearly_healthy_wlp_loop
                 wp_under_wlp_loop sdp_loop sublinear_wp_loop cts_wp_loop)

lemmas wd_intros =
  wd_Abort wd_Skip   wd_Apply
  wd_Embed wd_Seq    wd_PC
  wd_DC    wd_SetPC  wd_SetDC
  wd_Bind  wd_repeat wd_loop

end
