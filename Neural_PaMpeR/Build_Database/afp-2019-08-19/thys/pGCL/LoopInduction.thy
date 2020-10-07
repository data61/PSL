(*
 * Copyright (C) 2014 NICTA
 * All rights reserved.
 *)

(* Author: David Cock - David.Cock@nicta.com.au *)

section \<open>Continuity and Induction for Loops\<close>

theory LoopInduction imports Healthiness Continuity begin

text \<open>Showing continuity for loops requires a stronger induction principle than we have used
so far, which in turn relies on the continuity of loops (inductively).  Thus, the proofs are
intertwined, and broken off from the main set of continuity proofs.  This result is also
essential in showing the sublinearity of loops.\<close>

text \<open>A loop step is monotonic.\<close>
lemma wp_loop_step_mono_trans:
  fixes body::"'s prog"
  assumes sP: "sound P"
      and hb: "healthy (wp body)"
  shows "mono_trans (\<lambda>Q s. \<guillemotleft> G \<guillemotright> s * wp body Q s + \<guillemotleft> \<N> G \<guillemotright> s * P s)"
proof(intro mono_transI le_funI, simp)
  fix Q R::"'s expect" and s::'s
  assume sQ: "sound Q" and sR: "sound R" and le: "Q \<tturnstile> R"
  hence "wp body Q \<tturnstile> wp body R"
    by(rule mono_transD[OF healthy_monoD, OF hb])
  thus "\<guillemotleft>G\<guillemotright> s * wp body Q s \<le> \<guillemotleft>G\<guillemotright> s * wp body R s"
    by(auto dest:le_funD intro:mult_left_mono)
qed

text \<open>We can therefore apply the standard fixed-point lemmas to unfold it:\<close>
lemma lfp_wp_loop_unfold:
  fixes body::"'s prog"
  assumes hb: "healthy (wp body)"
      and sP: "sound P"
  shows "lfp_exp (\<lambda>Q s. \<guillemotleft>G\<guillemotright> s * wp body Q s + \<guillemotleft>\<N> G\<guillemotright> s * P s) =
         (\<lambda>s. \<guillemotleft>G\<guillemotright> s * wp body (lfp_exp (\<lambda>Q s. \<guillemotleft>G\<guillemotright> s * wp body Q s + \<guillemotleft>\<N> G\<guillemotright> s * P s)) s +
              \<guillemotleft>\<N> G\<guillemotright> s * P s)"
proof(rule lfp_exp_unfold)
  from assms show "mono_trans (\<lambda>Q s. \<guillemotleft>G\<guillemotright> s * wp body Q s + \<guillemotleft>\<N> G\<guillemotright> s * P s)"
    by(blast intro:wp_loop_step_mono_trans)
  from assms show "\<lambda>s. \<guillemotleft>G\<guillemotright> s * wp body (\<lambda>s. bound_of P) s + \<guillemotleft>\<N> G\<guillemotright> s * P s \<tturnstile> \<lambda>s. bound_of P"
    by(blast intro:lfp_loop_fp)
  from sP show "sound (\<lambda>s. bound_of P)"
    by(auto)
  fix Q::"'s expect"
  assume "sound Q"
  with assms show "sound (\<lambda>s. \<guillemotleft>G\<guillemotright> s * wp body Q s + \<guillemotleft>\<N> G\<guillemotright> s * P s)"
    by(intro wp_loop_step_sound[unfolded wp_eval, simplified, folded negate_embed], auto)
qed

lemma wp_loop_step_unitary:
  fixes body::"'s prog"
  assumes hb: "healthy (wp body)"
      and uP: "unitary P" and uQ: "unitary Q"
  shows "unitary (\<lambda>s. \<guillemotleft>G\<guillemotright> s * wp body Q s + \<guillemotleft>\<N> G\<guillemotright> s * P s)"
proof(intro unitaryI2 nnegI bounded_byI)
  fix s::'s
  from uQ hb have uwQ: "unitary (wp body Q)" by(auto)
  with uP have "0 \<le> wp body Q s" "0 \<le> P s" by(auto)
  thus "0 \<le> \<guillemotleft>G\<guillemotright> s * wp body Q s + \<guillemotleft>\<N> G\<guillemotright> s * P s"
    by(auto intro:add_nonneg_nonneg mult_nonneg_nonneg)

  from uP uwQ have "wp body Q s \<le> 1" "P s \<le> 1" by(auto)
  hence "\<guillemotleft>G\<guillemotright> s * wp body Q s + \<guillemotleft>\<N> G\<guillemotright> s * P s \<le> \<guillemotleft>G\<guillemotright> s * 1 + \<guillemotleft>\<N> G\<guillemotright> s * 1"
    by(blast intro:add_mono mult_left_mono)
  also have "... = 1" by(simp add:negate_embed)
  finally show "\<guillemotleft>G\<guillemotright> s * wp body Q s + \<guillemotleft>\<N> G\<guillemotright> s * P s \<le> 1" .
qed

lemma lfp_loop_unitary:
  fixes body::"'s prog"
  assumes hb: "healthy (wp body)"
      and uP: "unitary P"
  shows "unitary (lfp_exp (\<lambda>Q s. \<guillemotleft>G\<guillemotright> s * wp body Q s + \<guillemotleft>\<N> G\<guillemotright> s * P s))"
  using assms by(blast intro:lfp_exp_unitary wp_loop_step_unitary)

text \<open>From the lattice structure on transformers, we establish a transfinite induction
  principle for loops.  We use this to show a number of properties, particularly
  subdistributivity, for loops.  This proof follows the pattern of lemma lfp\_ordinal\_induct
  in HOL/Inductive.\<close>
lemma loop_induct:
  fixes body::"'s prog"
  assumes hwp:  "healthy (wp body)"
      and hwlp: "nearly_healthy (wlp body)"
      \<comment> \<open>The body must be healthy, both in strict and liberal semantics.\<close>
      and Limit:   "\<And>S. \<lbrakk> \<forall>x\<in>S. P (fst x) (snd x); \<forall>x\<in>S. feasible (fst x);
                          \<forall>x\<in>S. \<forall>Q. unitary Q \<longrightarrow> unitary (snd x Q) \<rbrakk> \<Longrightarrow>
                    P (Sup_trans (fst ` S)) (Inf_utrans (snd ` S))"
      \<comment> \<open>The property holds at limit points.\<close>
      and IH:   "\<And>t u. \<lbrakk> P t u; feasible t; \<And>Q. unitary Q \<Longrightarrow> unitary (u Q)  \<rbrakk> \<Longrightarrow>
                        P (wp  (body ;; Embed t \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip))
                          (wlp (body ;; Embed u \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip))"
      \<comment> \<open>The inductive step.  The property is preserved by a single loop iteration.\<close>
      and P_equiv: "\<And>t t' u u'. \<lbrakk> P t u; equiv_trans t t'; equiv_utrans u u' \<rbrakk> \<Longrightarrow> P t' u'"
      \<comment> \<open>The property must be preserved by equivalence\<close>
  shows "P (wp (do G \<longrightarrow> body od)) (wlp (do G \<longrightarrow> body od))"
  \<comment> \<open>The property can refer to both interpretations simultaneously.  The unifier will happily
  apply the rule to just one or the other, however.\<close>
proof(simp add:wp_eval)
  let "?X t" = "wp (body ;; Embed t \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip)"
  let "?Y t" = "wlp (body ;; Embed t \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip)"

  let ?M = "{x. P (fst x) (snd x) \<and>
                feasible (fst x) \<and>
                (\<forall>Q. unitary Q \<longrightarrow> unitary (snd x Q)) \<and>
                le_trans (fst x) (lfp_trans ?X) \<and>
                le_utrans (gfp_trans ?Y) (snd x)}"

  have fSup: "feasible (Sup_trans (fst ` ?M))"
  proof(intro feasibleI bounded_byI2 nnegI2)
    fix Q::"'s expect" and b::real
    assume nQ: "nneg Q" and bQ: "bounded_by b Q"
    show "Sup_trans (fst ` ?M) Q \<tturnstile> \<lambda>s. b"
      unfolding Sup_trans_def
      using nQ bQ by(auto intro!:Sup_exp_least)
    show "\<lambda>s. 0 \<tturnstile> Sup_trans (fst ` ?M) Q"
    proof(cases)
      assume empty: "?M = {}"
      show ?thesis by(simp add:Sup_trans_def Sup_exp_def empty)
    next
      assume ne: "?M \<noteq> {}"
      then obtain x where xin: "x \<in> ?M" by auto
      hence ffx: "feasible (fst x)" by(simp)
      with nQ bQ have "\<lambda>s. 0 \<tturnstile> fst x Q" by(auto)
      also from xin have "fst x Q \<tturnstile> Sup_trans (fst ` ?M) Q"
          apply(intro Sup_trans_upper2[OF imageI _ nQ bQ], assumption)
          apply(clarsimp, blast intro: sound_nneg[OF feasible_sound] feasible_boundedD)
          done
      finally show "\<lambda>s. 0 \<tturnstile> Sup_trans (fst ` ?M) Q" .
    qed
  qed

  have uInf: "\<And>P. unitary P \<Longrightarrow> unitary (Inf_utrans (snd ` ?M) P)"
  proof(cases "?M = {}")
    fix P
    assume empty: "?M = {}"
    show "?thesis P" by(simp only:empty, simp add:Inf_utrans_def)
  next
    fix P::"'s expect"
    assume uP: "unitary P"
       and ne: "?M \<noteq> {}"
    show "?thesis P"
    proof(intro unitaryI2 nnegI2 bounded_byI2)
      from ne obtain x where xin: "x \<in> ?M" by auto
      hence sxin: "snd x \<in> snd ` ?M" by(simp)
      hence "le_utrans (Inf_utrans (snd ` ?M)) (snd x)"
        by(intro Inf_utrans_lower, auto)
      with uP
      have "Inf_utrans (snd ` ?M) P \<tturnstile> snd x P" by(auto)
      also {
        from xin uP have "unitary (snd x P)" by(simp)
        hence "snd x P \<tturnstile> \<lambda>s. 1" by(auto)
      }
      finally show "Inf_utrans (snd ` ?M) P \<tturnstile> \<lambda>s. 1" .

      have "\<lambda>s. 0 \<tturnstile> Inf_trans (snd ` ?M) P"
        unfolding Inf_trans_def
      proof(rule Inf_exp_greatest)
        from sxin show "{t P |t. t \<in> snd ` ?M} \<noteq> {}" by(auto)
        show "\<forall>P\<in>{t P |t. t \<in> snd ` ?M}. \<lambda>s. 0 \<tturnstile> P"
        proof(clarsimp)
          fix t::"'s trans"
          assume "\<forall>Q. unitary Q \<longrightarrow> unitary (t Q)"
          with uP have "unitary (t P)" by(auto)
          thus "\<lambda>s. 0 \<tturnstile> t P" by(auto)
        qed
      qed
      also {
        from ne have X: "(snd ` ?M = {}) = False" by(simp)
        have "Inf_trans (snd ` ?M) P = Inf_utrans (snd ` ?M) P"
          unfolding Inf_utrans_def by(subst X, simp)
      }
      finally show "\<lambda>s. 0 \<tturnstile> Inf_utrans (snd ` ?M) P" .
    qed
  qed

  have wp_loop_mono: "\<And>t u. \<lbrakk> le_trans t u; \<And>P. sound P \<Longrightarrow> sound (t P);
                               \<And>P. sound P \<Longrightarrow> sound (u P) \<rbrakk> \<Longrightarrow> le_trans (?X t) (?X u)"
  proof(intro le_transI le_funI, simp add:wp_eval)
    fix t u::"'s trans" and P::"'s expect" and s::'s
    assume le: "le_trans t u"
       and st: "\<And>P. sound P \<Longrightarrow> sound (t P)"
       and su: "\<And>P. sound P \<Longrightarrow> sound (u P)"
       and sP: "sound P"
    hence "sound (t P)" "sound (u P)" by(auto)
    with healthy_monoD[OF hwp] le sP have "wp body (t P) \<tturnstile> wp body (u P)" by(auto)
    hence "wp body (t P) s \<le> wp body (u P) s" by(auto)
    thus "\<guillemotleft>G\<guillemotright> s * wp body (t P) s \<le> \<guillemotleft>G\<guillemotright> s * wp body (u P) s" by(auto intro:mult_left_mono)
  qed

  have wlp_loop_mono: "\<And>t u. \<lbrakk> le_utrans t u; \<And>P. unitary P \<Longrightarrow> unitary (t P);
                               \<And>P. unitary P \<Longrightarrow> unitary (u P) \<rbrakk> \<Longrightarrow> le_utrans (?Y t) (?Y u)"
  proof(intro le_utransI le_funI, simp add:wp_eval)
    fix t u::"'s trans" and P::"'s expect" and s::'s
    assume le: "le_utrans t u"
       and ut: "\<And>P. unitary P \<Longrightarrow> unitary (t P)"
       and uu: "\<And>P. unitary P \<Longrightarrow> unitary (u P)"
       and uP: "unitary P"
    hence "unitary (t P)" "unitary (u P)" by(auto)
    with le uP have "wlp body (t P) \<tturnstile> wlp body (u P)"
      by(auto intro:nearly_healthy_monoD[OF hwlp])
    hence "wlp body (t P) s \<le> wlp body (u P) s" by(auto)
    thus "\<guillemotleft>G\<guillemotright> s * wlp body (t P) s \<le> \<guillemotleft>G\<guillemotright> s * wlp body (u P) s"
      by(auto intro:mult_left_mono)
  qed

  from hwp have hX: "\<And>t. healthy t \<Longrightarrow> healthy (?X t)"
    by(auto intro:healthy_intros)

  from hwlp have hY: "\<And>t. nearly_healthy t \<Longrightarrow> nearly_healthy (?Y t)"
    by(auto intro!:healthy_intros)
                
  have PLimit: "P (Sup_trans (fst ` ?M)) (Inf_utrans (snd ` ?M))"
    by(auto intro:Limit)

  have feasible_lfp_loop:
    "feasible (lfp_trans ?X)"
  proof(intro feasibleI bounded_byI2 nnegI2,
        simp_all add:wp_Loop1[simplified wp_eval] soundI2 hwp)
    fix P::"'s expect" and b::real
    assume bP: "bounded_by b P" and nP: "nneg P"
    hence sP: "sound P" by(auto)
    show "lfp_exp (\<lambda>Q s. \<guillemotleft> G \<guillemotright> s * wp body Q s + \<guillemotleft> \<N> G \<guillemotright> s * P s) \<tturnstile> \<lambda>s. b"
    proof(intro lfp_exp_lowerbound le_funI)
      fix s::'s
      from bP nP have nnb: "0 \<le> b" by(auto)
      hence "sound (\<lambda>s. b)" "bounded_by b (\<lambda>s. b)" by(auto)
      with hwp have "bounded_by b (wp body (\<lambda>s. b))" by(auto)
      with bP have "wp body (\<lambda>s. b) s \<le> b" "P s \<le> b" by(auto)
      hence "\<guillemotleft>G\<guillemotright> s * wp body (\<lambda>s. b) s + \<guillemotleft>\<N> G\<guillemotright> s * P s \<le> \<guillemotleft>G\<guillemotright> s * b + \<guillemotleft>\<N> G\<guillemotright> s * b"
        by(auto intro:add_mono mult_left_mono)
      thus "\<guillemotleft>G\<guillemotright> s * wp body (\<lambda>s. b) s + \<guillemotleft>\<N> G\<guillemotright> s * P s \<le> b"
        by(simp add:negate_embed algebra_simps)
      from nnb show "sound (\<lambda>s. b)" by(auto)
    qed
    from hwp sP show "\<lambda>s. 0 \<tturnstile> lfp_exp (\<lambda>Q s. \<guillemotleft> G \<guillemotright> s * wp body Q s + \<guillemotleft> \<N> G \<guillemotright> s * P s)"
      by(blast intro!:lfp_exp_greatest lfp_loop_fp)
  qed

  have unitary_gfp:
    "\<And>P. unitary P \<Longrightarrow> unitary (gfp_trans ?Y P)"
  proof(intro unitaryI2 nnegI2 bounded_byI2,
      simp_all add:wlp_Loop1[simplified wp_eval] hwlp)
    fix P::"'s expect"
    assume uP: "unitary P"
    show "\<lambda>s. 0 \<tturnstile> gfp_exp (\<lambda>Q s. \<guillemotleft> G \<guillemotright> s * wlp body Q s + \<guillemotleft> \<N> G \<guillemotright> s * P s)"
    proof(rule gfp_exp_upperbound[OF le_funI])
      fix s::"'s"
      from hwlp uP have "0 \<le> wlp body (\<lambda>s. 0) s" "0 \<le> P s" by(auto dest!:unitary_sound)
      thus "0 \<le> \<guillemotleft>G\<guillemotright> s * wlp body (\<lambda>s. 0) s + \<guillemotleft>\<N> G\<guillemotright> s * P s"
        by(auto intro:add_nonneg_nonneg mult_nonneg_nonneg)
      show "unitary (\<lambda>s. 0)" by(auto)
    qed
    show "gfp_exp (\<lambda>Q s. \<guillemotleft> G \<guillemotright> s * wlp body Q s + \<guillemotleft> \<N> G \<guillemotright> s * P s) \<tturnstile> \<lambda>s. 1"
      by(auto intro:gfp_exp_least)
  qed

  have fX:
    "\<And>t. feasible t \<Longrightarrow> feasible (?X t)"
  proof(intro feasibleI nnegI bounded_byI, simp_all add:wp_eval)
    fix t::"'s trans" and Q::"'s expect" and b::real and s::'s
    assume ft: "feasible t" and bQ: "bounded_by b Q" and nQ: "nneg Q"
    hence "nneg (t Q)" "bounded_by b (t Q)" by(auto)
    moreover hence stQ: "sound (t Q)" by(auto)
    ultimately have "wp body (t Q) s \<le> b" using hwp by(auto)
    moreover from bQ have "Q s \<le> b" by(auto)
    ultimately have "\<guillemotleft>G\<guillemotright> s * wp body (t Q) s + (1 - \<guillemotleft>G\<guillemotright> s) * Q s \<le>
                     \<guillemotleft>G\<guillemotright> s * b + (1 - \<guillemotleft> G \<guillemotright> s) * b"
      by(auto intro:add_mono mult_left_mono)
    thus "\<guillemotleft>G\<guillemotright> s * wp body (t Q) s + (1 - \<guillemotleft>G\<guillemotright> s) * Q s \<le> b"
      by(simp add:algebra_simps)

    from nQ stQ hwp have "0 \<le> wp body (t Q) s" "0 \<le> Q s" by(auto)
    thus "0 \<le> \<guillemotleft>G\<guillemotright> s * wp body (t Q) s + (1 - \<guillemotleft>G\<guillemotright> s) * Q s"
      by(auto intro:add_nonneg_nonneg mult_nonneg_nonneg)
  qed

  have uY:
    "\<And>t P. (\<And>P. unitary P \<Longrightarrow> unitary (t P)) \<Longrightarrow> unitary P \<Longrightarrow> unitary (?Y t P)"
  proof(intro unitaryI2 nnegI bounded_byI, simp_all add:wp_eval)
    fix t::"'s trans" and P::"'s expect" and s::'s
    assume ut: "\<And>P. unitary P \<Longrightarrow> unitary (t P)"
       and uP: "unitary P"
    hence utP: "unitary (t P)" by(auto)
    with hwlp have ubtP: "unitary (wlp body (t P))" by(auto)
    with uP have "0 \<le> P s" "0 \<le> wlp body (t P) s" by(auto)
    thus "0 \<le> \<guillemotleft>G\<guillemotright> s * wlp body (t P) s + (1-\<guillemotleft>G\<guillemotright> s) * P s"
      by(auto intro:add_nonneg_nonneg mult_nonneg_nonneg)

    from uP ubtP have "P s \<le> 1" "wlp body (t P) s \<le> 1" by(auto)
    hence "\<guillemotleft>G\<guillemotright> s * wlp body (t P) s + (1-\<guillemotleft>G\<guillemotright> s) * P s \<le> \<guillemotleft>G\<guillemotright> s * 1 + (1-\<guillemotleft>G\<guillemotright> s) * 1"
      by(blast intro:add_mono mult_left_mono)
    also have "... = 1" by(simp add:algebra_simps)
    finally show "\<guillemotleft>G\<guillemotright> s * wlp body (t P) s + (1-\<guillemotleft>G\<guillemotright> s) * P s \<le> 1" .
  qed

  have fw_lfp: "le_trans (Sup_trans (fst ` ?M)) (lfp_trans ?X)"
    using feasible_nnegD[OF feasible_lfp_loop]
    by(intro le_transI[OF Sup_trans_least2], blast+)
  hence "le_trans (?X (Sup_trans (fst ` ?M))) (?X (lfp_trans ?X))"
    by(auto intro:wp_loop_mono feasible_sound[OF fSup]
                  feasible_sound[OF feasible_lfp_loop])
  also have "equiv_trans ... (lfp_trans ?X)"
  proof(rule iffD1[OF equiv_trans_comm, OF lfp_trans_unfold], iprover intro:wp_loop_mono)
    fix t::"'s trans" and P::"'s expect"
    assume st: "\<And>Q. sound Q \<Longrightarrow> sound (t Q)"
       and sP: "sound P"
    show "sound (?X t P)"
    proof(intro soundI2 bounded_byI nnegI, simp_all add:wp_eval)
      fix s::'s
      from sP st hwp have "0 \<le> P s" "0 \<le> wp body (t P) s" by(auto)
      thus "0 \<le> \<guillemotleft>G\<guillemotright> s * wp body (t P) s + (1 - \<guillemotleft>G\<guillemotright> s) * P s"
        by(blast intro:add_nonneg_nonneg mult_nonneg_nonneg)
      from sP st have "bounded_by (bound_of (t P)) (t P)" by(auto)
      with sP st hwp have "bounded_by (bound_of (t P)) (wp body (t P))" by(auto)
      hence "wp body (t P) s \<le> bound_of (t P)" by(auto)
      moreover from sP st hwp have "P s \<le> bound_of P" by(auto)
      moreover have "\<guillemotleft>G\<guillemotright> s \<le> 1" "1 - \<guillemotleft>G\<guillemotright> s \<le> 1" by(auto)
      moreover from sP st hwp have "0 \<le> wp body (t P) s" "0 \<le> P s" by(auto)
      moreover have "(0::real) \<le> 1" by(simp)
      ultimately show "\<guillemotleft>G\<guillemotright> s * wp body (t P) s + (1 - \<guillemotleft>G\<guillemotright> s) * P s \<le>
                       1 * bound_of (t P) + 1 * bound_of P"
        by(blast intro:add_mono mult_mono)
      qed
    next
    let "?fp" = "\<lambda>R s. bound_of R"
    show "le_trans (?X ?fp) ?fp" by(auto intro:healthy_intros hwp)
    fix P::"'s expect" assume "sound P"
    thus "sound (?fp P)" by(auto)
  qed
  finally have le_lfp: "le_trans (?X (Sup_trans (fst ` ?M))) (lfp_trans ?X)" .

  have fw_gfp: "le_utrans (gfp_trans ?Y) (Inf_utrans (snd ` ?M))"
    by(auto intro:Inf_utrans_greatest unitary_gfp)

  have "equiv_utrans (gfp_trans ?Y) (?Y (gfp_trans ?Y))"
    by(auto intro!:gfp_trans_unfold wlp_loop_mono uY)
  also from fw_gfp have "le_utrans (?Y (gfp_trans ?Y)) (?Y (Inf_utrans (snd ` ?M)))"
    by(auto intro:wlp_loop_mono uInf unitary_gfp)
  finally have ge_gfp: "le_utrans (gfp_trans ?Y) (?Y (Inf_utrans (snd ` ?M)))" .
  from PLimit fX uY fSup uInf have "P (?X (Sup_trans (fst ` ?M))) (?Y (Inf_utrans (snd ` ?M)))"
    by(iprover intro:IH)
  moreover from fSup have "feasible (?X (Sup_trans (fst ` ?M)))" by(rule fX)
  moreover have "\<And>P. unitary P \<Longrightarrow> unitary (?Y (Inf_utrans (snd ` ?M)) P)"
    by(auto intro:uY uInf)
  moreover note le_lfp ge_gfp
  ultimately have pair_in: "(?X (Sup_trans (fst ` ?M)), ?Y (Inf_utrans (snd ` ?M))) \<in> ?M"
    by(simp)

  have "?X (Sup_trans (fst ` ?M)) \<in> fst ` ?M"
    by(rule imageI[OF pair_in, of fst, simplified])
  hence "le_trans (?X (Sup_trans (fst ` ?M))) (Sup_trans (fst ` ?M))"
  proof(rule le_transI[OF Sup_trans_upper2[where t="?X (Sup_trans (fst ` ?M))"
                                             and S="fst ` ?M"]])
    fix P::"'s expect"
    assume sP: "sound P"
    thus "nneg P" by(auto)
    from sP show "bounded_by (bound_of P) P" by(auto)
    from sP show "\<forall>u\<in>fst ` ?M. \<forall>Q. nneg Q \<and> bounded_by (bound_of P) Q \<longrightarrow>
                                   nneg (u Q) \<and> bounded_by (bound_of P) (u Q)"
      by(auto)
  qed
  hence "le_trans (lfp_trans ?X) (Sup_trans (fst ` ?M))"
    by(auto intro:lfp_trans_lowerbound feasible_sound[OF fSup])
  with fw_lfp have eqt: "equiv_trans (Sup_trans (fst ` ?M)) (lfp_trans ?X)"
    by(rule le_trans_antisym)

  have "?Y (Inf_utrans (snd ` ?M)) \<in> snd ` ?M"
    by(rule imageI[OF pair_in, of snd, simplified])
  hence "le_utrans (Inf_utrans (snd ` ?M)) (?Y (Inf_utrans (snd ` ?M)))"
    by(intro Inf_utrans_lower, auto)
  hence "le_utrans (Inf_utrans (snd ` ?M)) (gfp_trans ?Y)"
    by(blast intro:gfp_trans_upperbound uInf)
  with fw_gfp have equ: "equiv_utrans (Inf_utrans (snd ` ?M)) (gfp_trans ?Y)"
    by(auto intro:le_utrans_antisym)
  from PLimit eqt equ show "P (lfp_trans ?X) (gfp_trans ?Y)" by(rule P_equiv)
qed

subsection \<open>The Limit of Iterates\<close>

text \<open>The iterates of a loop are its sequence of finite unrollings.  We show shortly that this
converges on the least fixed point.  This is enormously useful, as we can appeal to various
properties of the finite iterates (which will follow by finite induction), which we can then
transfer to the limit.\<close>
definition iterates :: "'s prog \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 's trans"
where "iterates body G i = ((\<lambda>x. wp (body ;; Embed x \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip)) ^^ i) (\<lambda>P s. 0)"

lemma iterates_0[simp]:
  "iterates body G 0 = (\<lambda>P s. 0)"
  by(simp add:iterates_def)

lemma iterates_Suc[simp]:
  "iterates body G (Suc i) = wp (body ;; Embed (iterates body G i) \<^bsub>\<guillemotleft>G\<guillemotright>\<^esub>\<oplus> Skip)"
  by(simp add:iterates_def)

text \<open>All iterates are healthy.\<close>
lemma iterates_healthy:
  "healthy (wp body) \<Longrightarrow> healthy (iterates body G i)"
  by(induct i, auto intro:healthy_intros)

text \<open>The iterates are an ascending chain.\<close>
lemma iterates_increasing:
  fixes body::"'s prog"
  assumes hb: "healthy (wp body)"
  shows "le_trans (iterates body G i) (iterates body G (Suc i))"
proof(induct i)
  show "le_trans (iterates body G 0) (iterates body G (Suc 0))"
  proof(simp add:iterates_def, rule le_transI)
    fix P::"'s expect"
    assume "sound P"
    with hb have "sound (wp (body ;; Embed (\<lambda>P s. 0) \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip) P)"
      by(auto intro!:wp_loop_step_sound)
    thus "\<lambda>s. 0 \<tturnstile> wp (body ;; Embed (\<lambda>P s. 0) \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip) P"
      by(auto)
  qed

  fix i
  assume IH: "le_trans (iterates body G i) (iterates body G (Suc i))"
  have "equiv_trans (iterates body G (Suc i))
                    (wp (body ;; Embed (iterates body G i) \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip))"
    by(simp)
  also from iterates_healthy[OF hb]
  have "le_trans ... (wp (body ;; Embed (iterates body G (Suc i)) \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip))"
    by(blast intro:wp_loop_step_mono[OF hb IH])
  also have "equiv_trans ... (iterates body G (Suc (Suc i)))"
    by(simp)
  finally show "le_trans (iterates body G (Suc i)) (iterates body G (Suc (Suc i)))" .
qed

lemma wp_loop_step_bounded:
  fixes t::"'s trans" and Q::"'s expect"
  assumes nQ: "nneg Q"
      and bQ: "bounded_by b Q"
      and ht: "healthy t"
      and hb: "healthy (wp body)"
  shows "bounded_by b (wp (body ;; Embed t \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip) Q)"
proof(rule bounded_byI, simp add:wp_eval)
  fix s::'s
  from nQ bQ have sQ: "sound Q" by(auto)
  with bQ ht have "sound (t Q)" "bounded_by b (t Q)" by(auto)
  with hb have "bounded_by b (wp body (t Q))" by(auto)
  with bQ have "wp body (t Q) s \<le> b" "Q s \<le> b" by(auto)
  hence "\<guillemotleft>G\<guillemotright> s * wp body (t Q) s + (1-\<guillemotleft>G\<guillemotright> s) * Q s \<le>
         \<guillemotleft>G\<guillemotright> s * b + (1-\<guillemotleft>G\<guillemotright> s) * b"
    by(auto intro:add_mono mult_left_mono)
  also have "... = b" by(simp add:algebra_simps)
  finally show "\<guillemotleft>G\<guillemotright> s * wp body (t Q) s + (1-\<guillemotleft>G\<guillemotright> s) * Q s \<le> b" .
qed

text \<open>This is the key result: The loop is equivalent to the supremum of its iterates.  This
proof follows the pattern of lemma continuous\_lfp in HOL/Library/Continuity.\<close>
lemma lfp_iterates:
  fixes body::"'s prog"
  assumes hb: "healthy (wp body)"
      and cb: "bd_cts (wp body)"
  shows "equiv_trans (wp (do G \<longrightarrow> body od)) (Sup_trans (range (iterates body G)))"
        (is "equiv_trans ?X ?Y")
proof(rule le_trans_antisym)
  let ?F = "\<lambda>x. wp (body ;; Embed x \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip)"
  let ?bot = "\<lambda>(P::'s \<Rightarrow> real) s::'s. 0::real"

  have HF: "\<And>i. healthy ((?F ^^ i) ?bot)"
  proof -
    fix i from hb show "(?thesis i)"
      by(induct i, simp_all add:healthy_intros)
  qed

  from iterates_healthy[OF hb]
  have "\<And>i. feasible (iterates body G i)" by(auto)
  hence fSup: "feasible (Sup_trans (range (iterates body G)))"
    by(auto intro:feasible_Sup_trans)

  {
    fix i
    have "le_trans ((?F ^^ i) ?bot) ?X"
    proof(induct i)
      show "le_trans ((?F ^^ 0) ?bot) ?X"
      proof(simp, intro le_transI)
        fix P::"'s expect"
        assume "sound P"
        with hb healthy_wp_loop
        have "sound (wp (\<mu> x. body ;; x \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip) P)"
          by(auto)
        thus "\<lambda>s. 0 \<tturnstile> wp (\<mu> x. body ;; x \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip) P"
          by(auto)
      qed
      fix i
      assume IH: "le_trans ((?F ^^ i) ?bot) ?X"
      have "equiv_trans ((?F ^^ (Suc i)) ?bot) (?F ((?F ^^ i) ?bot))" by(simp)
      also have "le_trans ... (?F ?X)"
      proof(rule wp_loop_step_mono[OF hb IH])
        fix P::"'s expect"
        assume sP: "sound P"
        with hb healthy_wp_loop
        show "sound (wp (\<mu> x. body ;; x \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip) P)"
          by(auto)
        from sP show "sound ((?F ^^ i) ?bot P)"
          by(rule healthy_sound[OF HF])
      qed
      also {
        from hb have X: "le_trans (wp (body ;; Embed (\<lambda>P s. bound_of P) \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip))
                                 (\<lambda>P s. bound_of P)"
          by(intro le_transI, simp add:wp_eval, auto intro: lfp_loop_fp[unfolded negate_embed])
        have "equiv_trans (?F ?X) ?X"
        apply (simp only: wp_eval)
        by(intro iffD1[OF equiv_trans_comm, OF lfp_trans_unfold]
                 wp_loop_step_mono[OF hb] wp_loop_step_sound[OF hb], (blast|rule X)+)
      }
      finally show "le_trans ((?F ^^ (Suc i)) ?bot) ?X" .
    qed
  }
  hence "\<And>i. le_trans (iterates body G i) (wp do G \<longrightarrow> body od)"
    by(simp add:iterates_def)
  thus "le_trans ?Y ?X"
    by(auto intro!:le_transI[OF Sup_trans_least2] sound_nneg
                   healthy_sound[OF iterates_healthy, OF hb]
                   healthy_bounded_byD[OF iterates_healthy, OF hb]
                   healthy_sound[OF healthy_wp_loop] hb)

  show "le_trans ?X ?Y"
  proof(simp only: wp_eval, rule lfp_trans_lowerbound)
    from hb cb have "bd_cts_tr ?F" by(rule cts_wp_loopstep)
    with iterates_increasing[OF hb] iterates_healthy[OF hb]
    have "equiv_trans (?F ?Y) (Sup_trans (range (?F o (iterates body G))))"
      by (auto intro!: healthy_feasibleD bd_cts_trD cong del: image_cong_simp)
    also have "le_trans (Sup_trans (range (?F o (iterates body G)))) ?Y"
    proof(rule le_transI)
      fix P::"'s expect"
      assume sP: "sound P"
      show "(Sup_trans (range (?F o (iterates body G)))) P \<tturnstile> ?Y P"
      proof(rule Sup_trans_least2, clarsimp)
        show "\<forall>u\<in>range ((\<lambda>x. wp (body ;; Embed x \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip)) \<circ> iterates body G).
              \<forall>R. nneg R \<and> bounded_by (bound_of P) R \<longrightarrow>
                  nneg (u R) \<and> bounded_by (bound_of P) (u R)"
        proof(clarsimp, intro conjI)
          fix Q::"'s expect" and i
          assume nQ: "nneg Q" and bQ: "bounded_by (bound_of P) Q"
          hence "sound Q" by(auto)
          moreover from iterates_healthy[OF hb]
          have "\<And>P. sound P \<Longrightarrow> sound (iterates body G i P)" by(auto)
          moreover note hb
          ultimately have "sound (wp (body ;; Embed (iterates body G i) \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip) Q)"
            by(iprover intro:wp_loop_step_sound)
          thus "nneg (wp (body ;; Embed (iterates body G i) \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip) Q)"
            by(auto)
          from nQ bQ iterates_healthy[OF hb] hb
          show "bounded_by (bound_of P) (wp (body ;; Embed (iterates body G i) \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip) Q)"
            by(rule wp_loop_step_bounded)
        qed
        from sP show "nneg P" "bounded_by (bound_of P) P" by(auto)
      next
        fix Q::"'s expect"
        assume nQ: "nneg Q" and bQ: "bounded_by (bound_of P) Q"
        hence "sound Q" by(auto)
        with fSup have "sound (Sup_trans (range (iterates body G)) Q)" by(auto)
        thus "nneg (Sup_trans (range (iterates body G)) Q)" by(auto)

        fix i
        show "wp (body ;; Embed (iterates body G i) \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip) Q \<tturnstile>
              Sup_trans (range (iterates body G)) Q"
        proof(rule Sup_trans_upper2[OF _ _ nQ bQ])
          from iterates_healthy[OF hb]
          show "\<forall>u\<in>range (iterates body G).
                \<forall>R. nneg R \<and> bounded_by (bound_of P) R \<longrightarrow>
                     nneg (u R) \<and> bounded_by (bound_of P) (u R)"
            by(auto)
          have "wp (body ;; Embed (iterates body G i) \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip) = iterates body G (Suc i)"
            by(simp)
          also have "... \<in> range (iterates body G)"
            by(blast)
          finally show "wp (body ;; Embed (iterates body G i) \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip) \<in>
                        range (iterates body G)" .
        qed
      qed
    qed
    finally show "le_trans (?F ?Y) ?Y" .

    fix P::"'s expect"
    assume "sound P"
    with fSup show "sound (?Y P)" by(auto)
  qed
qed

text \<open>Therefore, evaluated at a given point (state), the sequence of iterates gives a sequence
of real values that converges on that of the loop itself.\<close>
corollary loop_iterates:
  fixes body::"'s prog"
  assumes hb: "healthy (wp body)"
      and cb: "bd_cts (wp body)"
      and sP: "sound P"
  shows "(\<lambda>i. iterates body G i P s) \<longlonglongrightarrow> wp (do G \<longrightarrow> body od) P s"
proof -
  let ?X = "{f s |f. f \<in> {t P |t. t \<in> range (iterates body G)}}"
  have closure_Sup: "Sup ?X \<in> closure ?X"
  proof(rule closure_contains_Sup, simp, clarsimp)
    fix i
    from sP have "bounded_by (bound_of P) P" by(auto)
    with iterates_healthy[OF hb] sP have "\<And>j. bounded_by (bound_of P) (iterates body G j P)"
      by(auto)
    thus "iterates body G i P s \<le> bound_of P" by(auto)    
  qed

  have "(\<lambda>i. iterates body G i P s) \<longlonglongrightarrow> Sup {f s |f. f \<in> {t P |t. t \<in> range (iterates body G)}}"
  proof(rule LIMSEQ_I)
    fix r::real assume posr: "0 < r"
    with closure_Sup obtain y where yin: "y \<in> ?X" and ey: "dist y (Sup ?X) < r"
      by(simp only:closure_approachable, blast)
    from yin obtain i where yit: "y = iterates body G i P s" by(auto)
    {
      fix j
      have "i \<le> j \<longrightarrow> le_trans (iterates body G i) (iterates body G j)"
      proof(induct j, simp, clarify)
        fix k
        assume IH: "i \<le> k \<longrightarrow> le_trans (iterates body G i) (iterates body G k)"
           and le: "i \<le> Suc k"
        show "le_trans (iterates body G i) (iterates body G (Suc k))"
        proof(cases "i = Suc k", simp)
          assume "i \<noteq> Suc k"
          with le have "i \<le> k" by(auto)
          with IH have "le_trans (iterates body G i) (iterates body G k)" by(auto)
          also note iterates_increasing[OF hb]
          finally show "le_trans (iterates body G i) (iterates body G (Suc k))" .
        qed
      qed
    }
    with sP have "\<forall>j\<ge>i. iterates body G i P s \<le> iterates body G j P s"
      by(auto)
    moreover {
      from sP have "bounded_by (bound_of P) P" by(auto)
      with iterates_healthy[OF hb] sP have "\<And>j. bounded_by (bound_of P) (iterates body G j P)"
        by(auto)
      hence "\<And>j. iterates body G j P s \<le> bound_of P" by(auto)
      hence "\<And>j. iterates body G j P s \<le> Sup ?X"
        by(intro cSup_upper bdd_aboveI, auto)
    }
    ultimately have "\<And>j. i \<le> j \<Longrightarrow>
                           norm (iterates body G j P s - Sup ?X) \<le>
                           norm (iterates body G i P s - Sup ?X)"
      by(auto)
    also from ey yit have "norm (iterates body G i P s - Sup ?X) < r"
      by(simp add:dist_real_def)
    finally show "\<exists>no. \<forall>n\<ge>no. norm (iterates body G n P s -
                                    Sup {f s |f. f \<in> {t P |t. t \<in> range (iterates body G)}}) < r"
      by(auto)
  qed
  moreover
  from hb cb sP have "wp do G \<longrightarrow> body od P s = Sup_trans (range (iterates body G)) P s"
    by(simp add:equiv_transD[OF lfp_iterates])
  moreover have "... = Sup {f s |f. f \<in> {t P |t. t \<in> range (iterates body G)}}"
    by(simp add:Sup_trans_def Sup_exp_def)
  ultimately show ?thesis by(simp)
qed

text \<open>The iterates themselves are all continuous.\<close>
lemma cts_iterates:
  fixes body::"'s prog"
  assumes hb: "healthy (wp body)"
      and cb: "bd_cts (wp body)"
  shows "bd_cts (iterates body G i)"
proof(induct i, simp_all)
  have "range (\<lambda>(n::nat) (s::'s). 0::real) = {\<lambda>s. 0::real}"
    by(auto)
  thus "bd_cts (\<lambda>P (s::'s). 0)"
    by(intro bd_ctsI, simp add:o_def Sup_exp_def)
next
  fix i
  assume IH: "bd_cts (iterates body G i)"
  thus "bd_cts (wp (body ;; Embed (iterates body G i) \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip))"
    by(blast intro:cts_wp_PC cts_wp_Seq cts_wp_Embed cts_wp_Skip
                   healthy_intros iterates_healthy cb hb)
qed

text \<open>Therefore so is the loop itself.\<close>
lemma cts_wp_loop:
  fixes body::"'s prog"
  assumes hb: "healthy (wp body)"
      and cb: "bd_cts (wp body)"
  shows "bd_cts (wp do G \<longrightarrow> body od)"
proof(rule bd_ctsI)
  fix M::"nat \<Rightarrow> 's expect" and b::real
  assume chain: "\<And>i. M i \<tturnstile> M (Suc i)"
     and sM: "\<And>i. sound (M i)"
     and bM: "\<And>i. bounded_by b (M i)"

  from sM bM iterates_healthy[OF hb]
  have "\<And>j i. bounded_by b (iterates body G i (M j))" by(blast)
  hence iB: "\<And>j i s. iterates body G i (M j) s \<le> b" by(auto)

  from sM bM have sSup: "sound (Sup_exp (range M))"
    by(auto intro:Sup_exp_sound)
  with lfp_iterates[OF hb cb]
  have "wp do G \<longrightarrow> body od (Sup_exp (range M)) =
        Sup_trans (range (iterates body G)) (Sup_exp (range M))"
    by(simp add:equiv_transD)
  also {
    from chain sM bM
    have "\<And>i. iterates body G i (Sup_exp (range M)) = Sup_exp (range (iterates body G i o M))"
      by(blast intro:bd_ctsD cts_iterates[OF hb cb])
    hence "{t (Sup_exp (range M)) |t. t \<in> range (iterates body G)} =
           {Sup_exp (range (t o M)) |t. t \<in> range (iterates body G)}"
      by(auto intro:sym)
    hence "Sup_trans (range (iterates body G)) (Sup_exp (range M)) =
           Sup_exp {Sup_exp (range (t \<circ> M)) |t. t \<in> range (iterates body G)}"
      by(simp add:Sup_trans_def)
  }
  also {
    have "\<And>s. {f s |f. \<exists>t. f = (\<lambda>s. Sup {f s |f. f \<in> range (t \<circ> M)}) \<and>
                           t \<in> range (iterates body G)} =
          range (\<lambda>i. Sup (range (\<lambda>j. iterates body G i (M j) s)))"
      (is "\<And>s. ?X s = ?Y s")
    proof(intro antisym subsetI)
      fix s x
      assume "x \<in> ?X s"
      then obtain t where rwx: "x = Sup {f s |f. f \<in> range (t \<circ> M)}"
                      and "t \<in> range (iterates body G)" by(auto)
      then obtain i where "t = iterates body G i" by(auto)
      with rwx have "x = Sup {f s |f. f \<in> range (\<lambda>j. iterates body G i (M j))}"
        by(simp add:o_def)
      moreover have "{f s |f. f \<in> range (\<lambda>j. iterates body G i (M j))} =
                     range (\<lambda>j. iterates body G i (M j) s)" by(auto)
      ultimately have "x = Sup (range (\<lambda>j. iterates body G i (M j) s))"
        by(simp)
      thus "x \<in> range (\<lambda>i. Sup (range (\<lambda>j. iterates body G i (M j) s)))"
        by(auto)
    next
      fix s x
      assume "x \<in> ?Y s"
      then obtain i where A: "x = Sup (range (\<lambda>j. iterates body G i (M j) s))"
        by(auto)

      have "\<And>s. {f s |f. f \<in> range (\<lambda>j. iterates body G i (M j))} =
            range (\<lambda>j. iterates body G i (M j) s)" by(auto)
      hence B: "(\<lambda>s. Sup (range (\<lambda>j. iterates body G i (M j) s))) =
             (\<lambda>s. Sup {f s |f. f \<in> range (iterates body G i o M)})"
        by(simp add:o_def)

      have C: "iterates body G i \<in> range (iterates body G)" by(auto)

      have "\<exists>f. x = f s \<and>
                (\<exists>t. f = (\<lambda>s. Sup {f s |f. f \<in> range (t \<circ> M)}) \<and>
                     t \<in> range (iterates body G))"
        by(iprover intro:A B C)
      thus "x \<in> ?X s" by(simp)
    qed
    hence "Sup_exp {Sup_exp (range (t \<circ> M)) |t. t \<in> range (iterates body G)} = 
           (\<lambda>s. Sup (range (\<lambda>i. Sup (range (\<lambda>j. iterates body G i (M j) s)))))"
      by(simp add:Sup_exp_def)
  }
  also have "(\<lambda>s. Sup (range (\<lambda>i. Sup (range (\<lambda>j. iterates body G i (M j) s))))) =
             (\<lambda>s. Sup (range (\<lambda>(i,j). iterates body G i (M j) s)))"
    (is "?X = ?Y")
  proof(rule ext, rule antisym)
    fix s::'s
    show "?Y s \<le> ?X s"
    proof(rule cSup_least, blast, clarify)
      fix i j::nat
      from iB have "iterates body G i (M j) s \<le> Sup (range (\<lambda>j. iterates body G i (M j) s))"
        by(intro cSup_upper bdd_aboveI, auto)
      also from iB have "... \<le> Sup (range (\<lambda>i. Sup (range (\<lambda>j. iterates body G i (M j) s))))"
        by(intro cSup_upper cSup_least bdd_aboveI, (blast intro:cSup_least)+)
      finally show "iterates body G i (M j) s \<le>
                    Sup (range (\<lambda>i. Sup (range (\<lambda>j. iterates body G i (M j) s))))" .
    qed
    have "\<And>i j. iterates body G i (M j) s \<le>
                Sup (range (\<lambda>(i, j). iterates body G i (M j) s))"
      by(rule cSup_upper, auto intro:iB)
    thus "?X s \<le> ?Y s"
      by(intro cSup_least, blast, clarify, simp, blast intro:cSup_least)
  qed
  also have "... = (\<lambda>s. Sup (range (\<lambda>j .Sup (range (\<lambda>i. iterates body G i (M j) s)))))"
    (is "?X = ?Y")
  proof(rule ext, rule antisym)
    fix s::'s
    have "\<And>i j. iterates body G i (M j) s \<le>
                Sup (range (\<lambda>(i, j). iterates body G i (M j) s))"
      by(rule cSup_upper, auto intro:iB)
    thus "?Y s \<le> ?X s"
      by(intro cSup_least, blast, clarify, simp, blast intro:cSup_least)
    show "?X s \<le> ?Y s"
    proof(rule cSup_least, blast, clarify)
      fix i j::nat
      from iB have "iterates body G i (M j) s \<le> Sup (range (\<lambda>i. iterates body G i (M j) s))"
        by(intro cSup_upper bdd_aboveI, auto)
      also from iB have "... \<le> Sup (range (\<lambda>j. Sup (range (\<lambda>i. iterates body G i (M j) s))))"
        by(intro cSup_upper cSup_least bdd_aboveI, blast, blast intro:cSup_least)
      finally show "iterates body G i (M j) s \<le>
                    Sup (range (\<lambda>j. Sup (range (\<lambda>i. iterates body G i (M j) s))))" .
    qed
  qed
  also {
    have "\<And>s. range (\<lambda>j. Sup (range (\<lambda>i. iterates body G i (M j) s))) =
               {f s |f. f \<in> range ((\<lambda>P s. Sup {f s |f. \<exists>t. f = t P \<and>
               t \<in> range (iterates body G)}) \<circ> M)}" (is "\<And>s. ?X s = ?Y s")
    proof(intro antisym subsetI)
      fix s x
      assume "x \<in> ?X s"
      then obtain j where rwx: "x = Sup (range (\<lambda>i. iterates body G i (M j) s))" by(auto)
      moreover {
        have "\<And>s. range (\<lambda>i. iterates body G i (M j) s) =
                   {f s |f. \<exists>t. f = t (M j) \<and> t \<in> range (iterates body G)}"
          by(auto)
        hence "(\<lambda>s. Sup (range (\<lambda>i. iterates body G i (M j) s))) \<in>
              range ((\<lambda>P s. Sup {f s |f.
                           \<exists>t. f = t P \<and> t \<in> range (iterates body G)}) \<circ> M)"
          by (simp add: o_def cong del: SUP_cong_simp)
      }
      ultimately show "x \<in> ?Y s" by(auto)
    next
      fix s x
      assume "x \<in> ?Y s"
      then obtain P where rwx: "x = P s"
                      and Pin: "P \<in> range ((\<lambda>P s. Sup {f s |f.
                            \<exists>t. f = t P \<and> t \<in> range (iterates body G)}) \<circ> M)"
        by(auto)
      then obtain j where "P = (\<lambda>s. Sup {f s |f. \<exists>t. f = t (M j) \<and>
                                                 t \<in> range (iterates body G)})"
        by(auto)
      also {
        have "\<And>s. {f s |f. \<exists>t. f = t (M j) \<and> t \<in> range (iterates body G)} =
                  range (\<lambda>i. iterates body G i (M j) s)" by(auto)
        hence "(\<lambda>s. Sup {f s |f. \<exists>t. f = t (M j) \<and> t \<in> range (iterates body G)}) =
               (\<lambda>s. Sup (range (\<lambda>i. iterates body G i (M j) s)))"
          by(simp)
      }
      finally have "x = Sup (range (\<lambda>i. iterates body G i (M j) s))"
        by(simp add:rwx)
      thus "x \<in> ?X s" by(simp)
    qed
    hence "(\<lambda>s. Sup (range (\<lambda>j .Sup (range (\<lambda>i. iterates body G i (M j) s))))) =
          Sup_exp (range (Sup_trans (range (iterates body G)) o M))"
      by (simp add: Sup_exp_def Sup_trans_def cong del: SUP_cong_simp)
  }
  also have "Sup_exp (range (Sup_trans (range (iterates body G)) o M)) =
             Sup_exp (range (wp do G \<longrightarrow> body od o M))"
    by(simp add:o_def equiv_transD[OF lfp_iterates, OF hb cb, OF sM])
  finally show "wp do G \<longrightarrow> body od (Sup_exp (range M)) =
                Sup_exp (range (wp do G \<longrightarrow> body od o M))" .
qed

lemmas cts_intros =
  cts_wp_Abort  cts_wp_Skip
  cts_wp_Seq    cts_wp_PC
  cts_wp_DC     cts_wp_Embed
  cts_wp_Apply  cts_wp_SetDC
  cts_wp_SetPC  cts_wp_Bind
  cts_wp_repeat

end
