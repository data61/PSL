(*
 * Copyright (C) 2014 NICTA
 * All rights reserved.
 *)

(* Authors: David Cock - David.Cock@nicta.com.au, Thomas Sewell - Thomas.Sewell@nicta.com.au *)

section "Loop Termination"
 
theory Termination imports Embedding StructuredReasoning Loops begin

text_raw \<open>\label{s:termination}\<close>

text \<open>Termination for loops can be shown by classical means (using a variant, or a measure
function), or by probabilistic means: We only need that the loop terminates \emph{with probability
one}.\<close>

subsection \<open>Trivial Termination\<close>

text \<open>A maximal transformer (program) doesn't affect termination. This is
  essentially saying that such a program doesn't abort (or diverge).\<close>
lemma maximal_Seq_term:
  fixes r::"'s prog" and s::"'s prog"
  assumes mr: "maximal (wp r)"
      and ws: "well_def s"
      and ts: "(\<lambda>s. 1) \<tturnstile> wp s (\<lambda>s. 1)"
  shows "(\<lambda>s. 1) \<tturnstile> wp (r ;; s) (\<lambda>s. 1)"
proof -
  note hs = well_def_wp_healthy[OF ws]
  have "wp s (\<lambda>s. 1) = (\<lambda>s. 1)"
  proof(rule antisym)
    show "(\<lambda>s. 1) \<tturnstile> wp s (\<lambda>s. 1)" by(rule ts)
    have "bounded_by 1 (wp s (\<lambda>s. 1))"
      by(auto intro!:healthy_bounded_byD[OF hs])
    thus "wp s (\<lambda>s. 1) \<tturnstile> (\<lambda>s. 1)" by(auto intro!:le_funI)
  qed
  with mr show ?thesis
    by(simp add:wp_eval embed_bool_def maximalD)
qed

text \<open>From any state where the guard does not hold, a loop terminates
  in a single step.\<close>
lemma term_onestep:
  assumes wb: "well_def body"
  shows "\<guillemotleft>\<N> G\<guillemotright> \<tturnstile> wp do G \<longrightarrow> body od (\<lambda>s. 1)"
proof(rule le_funI)
  note hb = well_def_wp_healthy[OF wb]
  fix s
  show "\<guillemotleft>\<N> G\<guillemotright> s \<le> wp do G \<longrightarrow> body od (\<lambda>s. 1) s"
  proof(cases "G s", simp_all add:wp_loop_nguard hb)
    from hb have "sound (wp do G \<longrightarrow> body od (\<lambda>s. 1))"
      by(auto intro:healthy_sound[OF healthy_wp_loop])
    thus "0 \<le> wp do G \<longrightarrow> body od (\<lambda>s. 1) s" by(auto)
  qed
qed

subsection \<open>Classical Termination\<close>

text \<open>The first non-trivial termination result is quite standard: If we can provide a
natural-number-valued measure, that decreases on every iteration, and implies termination on
reaching zero, the loop terminates.\<close>

lemma loop_term_nat_measure_noinv:
  fixes m :: "'s \<Rightarrow> nat" and body :: "'s prog"
  assumes wb: "well_def body"
  and guard: "\<And>s. m s = 0 \<longrightarrow> \<not> G s"
  and variant: "\<And>n. \<guillemotleft>\<lambda>s. m s = Suc n\<guillemotright> \<tturnstile> wp body \<guillemotleft>\<lambda>s. m s = n\<guillemotright>"
  shows "\<lambda>s. 1 \<tturnstile> wp do G \<longrightarrow> body od (\<lambda>s. 1)"
proof -
  note hb = well_def_wp_healthy[OF wb]
  have "\<And>n. (\<forall>s. m s = n \<longrightarrow> 1 \<le> wp do G \<longrightarrow> body od (\<lambda>s. 1) s)"
  proof(induct_tac n)
    fix n
    show "\<forall>s. m s = 0 \<longrightarrow> 1 \<le> wp do G \<longrightarrow> body od (\<lambda>s. 1) s"
    proof(clarify)
      fix s
      assume "m s = 0"
      with guard have "\<not> G s" by(blast)
      with hb show "1 \<le> wp do G \<longrightarrow> body od (\<lambda>s. 1) s"
        by(simp add:wp_loop_nguard)
    qed
    assume IH: "\<forall>s. m s = n \<longrightarrow> 1 \<le> wp do G \<longrightarrow> body od (\<lambda>s. 1) s"
    hence IH': "\<forall>s. m s = n \<longrightarrow> 1 \<le> wp do G \<longrightarrow> body od \<guillemotleft>\<lambda>s. True\<guillemotright> s"
      by(simp add:embed_bool_def)
    have "\<forall>s. m s = Suc n \<longrightarrow> 1 \<le> wp do G \<longrightarrow> body od \<guillemotleft>\<lambda>s. True\<guillemotright> s"
    proof(intro fold_premise healthy_intros hb, rule le_funI)
      fix s
      show "\<guillemotleft>\<lambda>s. m s = Suc n\<guillemotright> s \<le> wp do G \<longrightarrow> body od \<guillemotleft>\<lambda>s. True\<guillemotright> s"
      proof(cases "G s")
        case False
        hence "1 = \<guillemotleft>\<N> G\<guillemotright> s" by(auto)
        also from wb have "... \<le> wp do G \<longrightarrow> body od (\<lambda>s. 1) s"
          by(rule le_funD[OF term_onestep])
        finally show ?thesis by(simp add:embed_bool_def)
      next
        case True note G = this
        from IH' have "\<guillemotleft>\<lambda>s. m s = n\<guillemotright> \<tturnstile> wp do G \<longrightarrow> body od \<guillemotleft>\<lambda>s. True\<guillemotright>"
          by(blast intro:use_premise healthy_intros hb)
        with variant wb
        have "\<guillemotleft>\<lambda>s. m s = Suc n\<guillemotright> \<tturnstile> wp (body ;; do G \<longrightarrow> body od) \<guillemotleft>\<lambda>s. True\<guillemotright>"
          by(blast intro:wp_Seq wd_intros)
        hence "\<guillemotleft>\<lambda>s. m s = Suc n\<guillemotright> s \<le> wp (body ;; do G \<longrightarrow> body od) \<guillemotleft>\<lambda>s. True\<guillemotright> s"
          by(auto)
        also from hb G have "... = wp do G \<longrightarrow> body od \<guillemotleft>\<lambda>s. True\<guillemotright> s"
          by(simp add:wp_loop_guard)
        finally show ?thesis .
      qed
    qed
    thus "\<forall>s. m s = Suc n \<longrightarrow> 1 \<le> wp do G \<longrightarrow> body od (\<lambda>s. 1) s"
      by(simp add:embed_bool_def)
  qed
  thus ?thesis by(auto)
qed

text \<open>This version allows progress to depend on an invariant. Termination is then determined by
the invariant's value in the initial state.\<close>
lemma loop_term_nat_measure:
  fixes m :: "'s \<Rightarrow> nat" and body :: "'s prog"
  assumes wb:  "well_def body"
  and guard:   "\<And>s. m s = 0 \<longrightarrow> \<not> G s"
  and variant: "\<And>n. \<guillemotleft>\<lambda>s. m s = Suc n\<guillemotright> && \<guillemotleft>I\<guillemotright> \<tturnstile> wp body \<guillemotleft>\<lambda>s. m s = n\<guillemotright>"
  and inv:     "wp_inv G body \<guillemotleft>I\<guillemotright>"
  shows "\<guillemotleft>I\<guillemotright> \<tturnstile> wp do G \<longrightarrow> body od (\<lambda>s. 1)"
proof -
  note hb = well_def_wp_healthy[OF wb]
  note scb = sublinear_sub_conj[OF well_def_wp_sublinear, OF wb]
  have "\<guillemotleft>I\<guillemotright> \<tturnstile> wp do G \<longrightarrow> body od \<guillemotleft>\<lambda>s. True\<guillemotright>"
  proof(rule use_premise, intro healthy_intros hb)
    fix s
    have "\<And>n. (\<forall>s. m s = n \<and> I s \<longrightarrow> 1 \<le> wp do G \<longrightarrow> body od \<guillemotleft>\<lambda>s. True\<guillemotright> s)"
    proof(induct_tac n)
      fix n
      show "\<forall>s. m s = 0 \<and> I s \<longrightarrow> 1 \<le> wp do G \<longrightarrow> body od \<guillemotleft>\<lambda>s. True\<guillemotright> s"
      proof(clarify)
        fix s
        assume "m s = 0"
        with guard have "\<not> G s" by(blast)
        with hb show "1 \<le> wp do G \<longrightarrow> body od \<guillemotleft>\<lambda>s. True\<guillemotright> s"
          by(simp add:wp_loop_nguard)
      qed
      assume IH: "\<forall>s. m s = n \<and> I s \<longrightarrow> 1 \<le> wp do G \<longrightarrow> body od \<guillemotleft>\<lambda>s. True\<guillemotright> s"
      show "\<forall>s. m s = Suc n \<and> I s \<longrightarrow> 1 \<le> wp do G \<longrightarrow> body od \<guillemotleft>\<lambda>s. True\<guillemotright> s"
      proof(intro fold_premise healthy_intros hb le_funI)
        fix s
        show "\<guillemotleft>\<lambda>s. m s = Suc n \<and> I s\<guillemotright> s \<le> wp do G \<longrightarrow> body od \<guillemotleft>\<lambda>s. True\<guillemotright> s"
        proof(cases "G s")
          case False with hb show ?thesis
            by(simp add:wp_loop_nguard)
        next
          case True note G = this
          have "\<guillemotleft>\<lambda>s. m s = Suc n\<guillemotright> && \<guillemotleft>I\<guillemotright> && \<guillemotleft>G\<guillemotright> =
                \<guillemotleft>\<lambda>s. m s = Suc n\<guillemotright> && (\<guillemotleft>I\<guillemotright> && \<guillemotleft>I\<guillemotright>) && \<guillemotleft>G\<guillemotright>"
            by(simp)
          also have "... = (\<guillemotleft>\<lambda>s. m s = Suc n\<guillemotright> && \<guillemotleft>I\<guillemotright>) && (\<guillemotleft>I\<guillemotright> && \<guillemotleft>G\<guillemotright>)"
            by(simp add:exp_conj_assoc exp_conj_unitary del:exp_conj_idem)
          also have "... = (\<guillemotleft>\<lambda>s. m s = Suc n\<guillemotright> && \<guillemotleft>I\<guillemotright>) && (\<guillemotleft>G\<guillemotright> && \<guillemotleft>I\<guillemotright>)"
            by(simp only:exp_conj_comm)
          also {
            from inv hb have "\<guillemotleft>G\<guillemotright> && \<guillemotleft>I\<guillemotright> \<tturnstile> wp body \<guillemotleft>I\<guillemotright>"
              by(rule wp_inv_stdD)
            with variant
            have "(\<guillemotleft>\<lambda>s. m s = Suc n\<guillemotright> && \<guillemotleft>I\<guillemotright>) && (\<guillemotleft>G\<guillemotright> && \<guillemotleft>I\<guillemotright>) \<tturnstile>
                  wp body \<guillemotleft>\<lambda>s. m s = n\<guillemotright> && wp body \<guillemotleft>I\<guillemotright>"
              by(rule entails_frame)
          }
          also from scb
          have "wp body \<guillemotleft>\<lambda>s. m s = n\<guillemotright> && wp body \<guillemotleft>I\<guillemotright> \<tturnstile>
                wp body (\<guillemotleft>\<lambda>s. m s = n\<guillemotright> && \<guillemotleft>I\<guillemotright>)"
            by(blast)
          finally have "\<guillemotleft>\<lambda>s. m s = Suc n \<guillemotright> && \<guillemotleft> I \<guillemotright> && \<guillemotleft> G \<guillemotright> \<tturnstile>
                        wp body (\<guillemotleft> \<lambda>s. m s = n \<guillemotright> && \<guillemotleft> I \<guillemotright>)" .
          moreover {
            from IH have "\<guillemotleft>\<lambda>s. m s = n \<and> I s\<guillemotright> \<tturnstile> wp do G \<longrightarrow> body od \<guillemotleft>\<lambda>s. True\<guillemotright>"
              by(blast intro:use_premise healthy_intros hb)
            hence "\<guillemotleft>\<lambda>s. m s = n\<guillemotright> && \<guillemotleft>I\<guillemotright> \<tturnstile> wp do G \<longrightarrow> body od \<guillemotleft>\<lambda>s. True\<guillemotright>"
              by(simp add:exp_conj_std_split)
          }
          ultimately
          have "\<guillemotleft>\<lambda>s. m s = Suc n \<guillemotright> && \<guillemotleft> I \<guillemotright> && \<guillemotleft> G \<guillemotright> \<tturnstile>
                wp (body ;; do G \<longrightarrow> body od) \<guillemotleft>\<lambda>s. True\<guillemotright>"
            using wb by(blast intro:wp_Seq wd_intros)
          hence "(\<guillemotleft>\<lambda>s. m s = Suc n \<and> I s\<guillemotright> && \<guillemotleft> G \<guillemotright>) s \<le>
                 wp (body ;; do G \<longrightarrow> body od) \<guillemotleft>\<lambda>s. True\<guillemotright> s"
            by(auto simp:exp_conj_std_split)
          with G have "\<guillemotleft>\<lambda>s. m s = Suc n \<and> I s\<guillemotright> s \<le>
                       wp (body ;; do G \<longrightarrow> body od) \<guillemotleft>\<lambda>s. True\<guillemotright> s"
            by(simp add:exp_conj_def)
          also from hb G have "... = wp do G \<longrightarrow> body od \<guillemotleft>\<lambda>s. True\<guillemotright> s"
            by(simp add:wp_loop_guard)
          finally show ?thesis .
        qed
      qed
    qed
    moreover assume "I s"
    ultimately show "1 \<le> wp do G \<longrightarrow> body od \<guillemotleft>\<lambda>s. True\<guillemotright> s"
      by(auto)
  qed
  thus ?thesis by(simp add:embed_bool_def)
qed

subsection \<open>Probabilistic Termination\<close>

text \<open>Any loop that has a non-zero chance of terminating after each step terminates with
probability 1.\<close>

lemma termination_0_1:
  fixes body :: "'s prog"
  assumes wb: "well_def body"
      \<comment> \<open>The loop terminates in one step with nonzero probability\<close>
      and onestep: "(\<lambda>s. p) \<tturnstile> wp body \<guillemotleft>\<N> G\<guillemotright>"
      and nzp:     "0 < p"
      \<comment> \<open>The body is maximal i.e.~it terminates absolutely.\<close>
      and mb:      "maximal (wp body)"
  shows "\<lambda>s. 1 \<tturnstile> wp do G \<longrightarrow> body od (\<lambda>s. 1)"
proof -
  note hb = well_def_wp_healthy[OF wb]
  note sb = healthy_scalingD[OF hb]
  note sab = sublinear_subadd[OF well_def_wp_sublinear, OF wb, OF healthy_feasibleD, OF hb]

  from hb have hloop: "healthy (wp do G \<longrightarrow> body od)"
    by(rule healthy_intros)
  hence swp: "sound (wp do G \<longrightarrow> body od (\<lambda>s. 1))" by(blast)

  txt \<open>@{term p} is no greater than $1$, by feasibility.\<close>
  from onestep have onestep': "\<And>s. p \<le> wp body \<guillemotleft>\<N> G\<guillemotright> s" by(auto)
  also {
    from hb have "unitary (wp body \<guillemotleft>\<N> G\<guillemotright>)" by(auto)
    hence "\<And>s. wp body \<guillemotleft>\<N> G\<guillemotright> s \<le> 1" by(auto)
  }
  finally have p1: "p \<le> 1" .

  txt \<open>This is the crux of the proof: that given a lower bound below $1$, we can find another,
    higher one.\<close>
  have new_bound: "\<And>k. 0 \<le> k \<Longrightarrow> k \<le> 1 \<Longrightarrow> (\<lambda>s. k) \<tturnstile> wp do G \<longrightarrow> body od (\<lambda>s. 1) \<Longrightarrow>
            (\<lambda>s. p * (1-k) + k) \<tturnstile> wp do G \<longrightarrow> body od (\<lambda>s. 1)"
  proof(rule le_funI)
    fix k s
    assume X: "\<lambda>s. k \<tturnstile> wp do G \<longrightarrow> body od (\<lambda>s. 1)"
       and k0: "0 \<le> k" and k1: "k \<le> 1"

    from k1 have nz1k: "0 \<le> 1 - k" by(auto)
    with p1 have "p * (1-k) + k \<le> 1 * (1-k) + k"
      by(blast intro:mult_right_mono add_mono)
    hence "p * (1 - k) + k \<le> 1"
      by(simp)
    txt \<open>The new bound is @{term "p * (1-k) + k"}.\<close>
    hence "p * (1-k) + k \<le> \<guillemotleft>\<N> G\<guillemotright> s + \<guillemotleft>G\<guillemotright> s * (p * (1-k) + k)"
      by(cases "G s", simp_all)
    txt \<open>By the one-step termination assumption:\<close>
    also from onestep' nz1k
    have "... \<le> \<guillemotleft>\<N> G\<guillemotright> s + \<guillemotleft>G\<guillemotright> s * (wp body \<guillemotleft>\<N> G\<guillemotright> s * (1-k) + k)"
      by (simp add: mult_right_mono ordered_comm_semiring_class.comm_mult_left_mono)
    txt \<open>By scaling:\<close>
    also from nz1k
    have "... =  \<guillemotleft>\<N> G\<guillemotright> s + \<guillemotleft>G\<guillemotright> s * (wp body (\<lambda>s. \<guillemotleft>\<N> G\<guillemotright> s * (1-k)) s + k)"
      by(simp add:right_scalingD[OF sb])
    txt \<open>By the maximality (termination) of the loop body:\<close>
    also from mb k0
    have "... =  \<guillemotleft>\<N> G\<guillemotright> s + \<guillemotleft>G\<guillemotright> s * (wp body (\<lambda>s. \<guillemotleft>\<N> G\<guillemotright> s * (1-k)) s + wp body (\<lambda>s. k) s)"
      by(simp add:maximalD)
    txt \<open>By sub-additivity of the loop body:\<close>
    also from k0 nz1k
    have "... \<le> \<guillemotleft>\<N> G\<guillemotright> s + \<guillemotleft>G\<guillemotright> s * (wp body (\<lambda>s. \<guillemotleft>\<N> G\<guillemotright> s * (1-k) + k) s)"
      by(auto intro!:add_left_mono mult_left_mono sub_addD[OF sab] sound_intros)
    also
    have "... = \<guillemotleft>\<N> G\<guillemotright> s + \<guillemotleft>G\<guillemotright> s * (wp body (\<lambda>s. \<guillemotleft>\<N> G\<guillemotright> s + \<guillemotleft>G\<guillemotright> s * k) s)"
      by(simp add:negate_embed algebra_simps)
    txt \<open>By monotonicity of the loop body, and that @{term k} is a lower bound:\<close>
    also from k0 hloop le_funD[OF X]
    have "... \<le> \<guillemotleft>\<N> G\<guillemotright> s +
      \<guillemotleft>G\<guillemotright> s * (wp body (\<lambda>s. \<guillemotleft>\<N> G\<guillemotright> s + \<guillemotleft>G\<guillemotright> s * wp do G \<longrightarrow> body od (\<lambda>s. 1) s) s)"
      by(iprover intro:add_left_mono mult_left_mono le_funI embed_ge_0
                       le_funD[OF mono_transD, OF healthy_monoD, OF hb]
                       sound_sum standard_sound sound_intros swp)
    txt \<open>Unrolling the loop once and simplifying:\<close>
    also {
      have "\<And>s. \<guillemotleft>\<N> G\<guillemotright> s + \<guillemotleft>G\<guillemotright> s * wp body (wp do G \<longrightarrow> body od (\<lambda>s. 1)) s =
        \<guillemotleft>\<N> G\<guillemotright> s + \<guillemotleft>G\<guillemotright> s * (\<guillemotleft>\<N> G\<guillemotright> s + \<guillemotleft>G\<guillemotright> s * wp body (wp do G \<longrightarrow> body od (\<lambda>s. 1)) s)"
        by(simp only:distrib_left mult.assoc[symmetric] embed_bool_idem embed_bool_cancel)
      also have "\<And>s. ... s = \<guillemotleft>\<N> G\<guillemotright> s + \<guillemotleft>G\<guillemotright> s * wp do G \<longrightarrow> body od (\<lambda>s. 1) s"
        by(simp add:fun_cong[OF wp_loop_unfold[symmetric, where P="\<lambda>s. 1", simplified, OF hb]])
      finally have X: "\<And>s. \<guillemotleft>\<N> G\<guillemotright> s + \<guillemotleft>G\<guillemotright> s * wp body (wp do G \<longrightarrow> body od (\<lambda>s. 1)) s =
        \<guillemotleft>\<N> G\<guillemotright> s + \<guillemotleft>G\<guillemotright> s * wp do G \<longrightarrow> body od (\<lambda>s. 1) s" .
      have "\<guillemotleft>\<N> G\<guillemotright> s + \<guillemotleft>G\<guillemotright> s * (wp body (\<lambda>s. \<guillemotleft>\<N> G\<guillemotright> s + \<guillemotleft>G\<guillemotright> s *
              wp do G \<longrightarrow> body od (\<lambda>s. 1) s) s) =
            \<guillemotleft>\<N> G\<guillemotright> s + \<guillemotleft>G\<guillemotright> s * (wp body (\<lambda>s. \<guillemotleft>\<N> G\<guillemotright> s + \<guillemotleft>G\<guillemotright> s *
              wp body (wp do G \<longrightarrow> body od (\<lambda>s. 1)) s) s)"
        by(simp only:X)
    }
    txt \<open>Lastly, by folding two loop iterations:\<close>
    also
    have "\<guillemotleft>\<N> G\<guillemotright> s + \<guillemotleft>G\<guillemotright> s * (wp body (\<lambda>s. \<guillemotleft>\<N> G\<guillemotright> s + \<guillemotleft>G\<guillemotright> s *
            wp body (wp do G \<longrightarrow> body od (\<lambda>s. 1)) s) s) =
          wp do G \<longrightarrow> body od (\<lambda>s. 1) s"
      by(simp add:wp_loop_unfold[OF _ hb, where P="\<lambda>s. 1", simplified, symmetric]
                  fun_cong[OF wp_loop_unfold[OF _ hb, where P="\<lambda>s. 1", simplified, symmetric]])
    finally show "p * (1-k) + k \<le> wp do G \<longrightarrow> body od (\<lambda>s. 1) s" .
  qed

  txt \<open>If the previous bound lay in $[0,1)$, the new bound is strictly greater.  This is where
    we appeal to the fact that @{term p} is nonzero.\<close>
  from nzp have inc: "\<And>k. 0 \<le> k \<Longrightarrow> k < 1 \<Longrightarrow> k < p * (1 - k) + k"
    by(auto intro:mult_pos_pos)

  txt \<open>The result follows by contradiction.\<close>
  show ?thesis
  proof(rule ccontr)
    txt \<open>If the loop does not terminate everywhere, then there must exist some state
      from which the probability of termination is strictly less than one.\<close>
    assume "\<not> ?thesis"
    hence "\<not> (\<forall>s. 1 \<le> wp do G \<longrightarrow> body od (\<lambda>s. 1) s)" by(auto)
    then obtain s where point: "\<not> 1 \<le> wp do G \<longrightarrow> body od (\<lambda>s. 1) s" by(auto)

    let ?k = "Inf (range (wp do G \<longrightarrow> body od (\<lambda>s. 1)))"

    from hloop
    have Inflb: "\<And>s. ?k \<le> wp do G \<longrightarrow> body od (\<lambda>s. 1) s"
      by(intro cInf_lower bdd_belowI, auto)
    also from point have "wp do G \<longrightarrow> body od (\<lambda>s. 1) s < 1" by(auto)
    txt \<open>Thus the least (infimum) probabilty of termination is strictly less than one.\<close>
    finally have k1: "?k < 1" .
    hence "?k \<le> 1" by(auto)
    moreover from hloop have k0: "0 \<le> ?k"
      by(intro cInf_greatest, auto)
    txt \<open>The infimum is, naturally, a lower bound.\<close>
    moreover from Inflb have "(\<lambda>s. ?k) \<tturnstile> wp do G \<longrightarrow> body od (\<lambda>s. 1)" by(auto)
    ultimately
    txt \<open>We can therefore use the previous result to find a new bound, \ldots\<close>
    have "\<And>s. p * (1 - ?k) + ?k \<le> wp do G \<longrightarrow> body od (\<lambda>s. 1) s"
      by(blast intro:le_funD[OF new_bound])
    txt \<open>\ldots which is lower than the infimum, by minimality, \ldots\<close>
    hence "p * (1 - ?k) + ?k \<le> ?k"
      by(blast intro:cInf_greatest)
    txt \<open>\ldots yet also strictly greater than it.\<close>
    moreover from k0 k1 have "?k < p * (1 - ?k) + ?k" by(rule inc)
    txt \<open>We thus have a contradiction.\<close>
    ultimately show False by(simp)
  qed
qed

end
