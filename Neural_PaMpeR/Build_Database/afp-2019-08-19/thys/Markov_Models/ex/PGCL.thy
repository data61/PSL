(* Author: Johannes Hölzl <hoelzl@in.tum.de> *)

section \<open>Probabilistic Guarded Command Language (pGCL)\<close>

theory PGCL
  imports "../Markov_Decision_Process"
begin

subsection \<open>Syntax\<close>

datatype 's pgcl =
    Skip
  | Abort
  | Assign "'s \<Rightarrow> 's"
  | Seq "'s pgcl" "'s pgcl"
  | Par "'s pgcl" "'s pgcl"
  | If "'s \<Rightarrow> bool" "'s pgcl" "'s pgcl"
  | Prob "bool pmf" "'s pgcl" "'s pgcl"
  | While "'s \<Rightarrow> bool" "'s pgcl"

subsection \<open>Denotational Semantics\<close>

primrec wp :: "'s pgcl \<Rightarrow> ('s \<Rightarrow> ennreal) \<Rightarrow> ('s \<Rightarrow> ennreal)" where
  "wp Skip f          = f"
| "wp Abort f         = (\<lambda>_. 0)"
| "wp (Assign u) f    = f \<circ> u"
| "wp (Seq c\<^sub>1 c\<^sub>2) f    = wp c\<^sub>1 (wp c\<^sub>2 f)"
| "wp (If b c\<^sub>1 c\<^sub>2) f   = (\<lambda>s. if b s then wp c\<^sub>1 f s else wp c\<^sub>2 f s)"
| "wp (Par c\<^sub>1 c\<^sub>2) f    = wp c\<^sub>1 f \<sqinter> wp c\<^sub>2 f"
| "wp (Prob p c\<^sub>1 c\<^sub>2) f = (\<lambda>s. pmf p True * wp c\<^sub>1 f s + pmf p False * wp c\<^sub>2 f s)"
| "wp (While b c) f   = lfp (\<lambda>X s. if b s then wp c X s else f s)"

lemma wp_mono: "mono (wp c)"
  by (induction c)
     (auto simp: mono_def le_fun_def intro: order_trans le_infI1 le_infI2
           intro!: add_mono mult_left_mono lfp_mono[THEN le_funD])

abbreviation det :: "'s pgcl \<Rightarrow> 's \<Rightarrow> ('s pgcl \<times> 's) pmf set" ("\<lless> _, _ \<ggreater>") where
  "det c s \<equiv> {return_pmf (c, s)}"

subsection \<open>Operational Semantics\<close>

fun step :: "('s pgcl \<times> 's) \<Rightarrow> ('s pgcl \<times> 's) pmf set" where
  "step (Skip, s)        = \<lless>Skip, s\<ggreater>"
| "step (Abort, s)       = \<lless>Abort, s\<ggreater>"
| "step (Assign u, s)    = \<lless>Skip, u s\<ggreater>"
| "step (Seq c\<^sub>1 c\<^sub>2, s)    = (map_pmf (\<lambda>(p1', s'). (if p1' = Skip then c\<^sub>2 else Seq p1' c\<^sub>2, s'))) ` step (c\<^sub>1, s)"
| "step (If b c\<^sub>1 c\<^sub>2, s)   = (if b s then \<lless>c\<^sub>1, s\<ggreater> else \<lless>c\<^sub>2, s\<ggreater>)"
| "step (Par c\<^sub>1 c\<^sub>2, s)    = \<lless>c\<^sub>1, s\<ggreater> \<union> \<lless>c\<^sub>2, s\<ggreater>"
| "step (Prob p c\<^sub>1 c\<^sub>2, s) = {map_pmf (\<lambda>b. if b then (c\<^sub>1, s) else (c\<^sub>2, s)) p}"
| "step (While b c, s)   = (if b s then \<lless>Seq c (While b c), s\<ggreater> else \<lless>Skip, s\<ggreater>)"

lemma step_finite: "finite (step x)"
  by (induction x rule: step.induct) simp_all

lemma step_non_empty: "step x \<noteq> {}"
  by (induction x rule: step.induct) simp_all

interpretation step: Markov_Decision_Process step
  proof qed (rule step_non_empty)

definition rF :: "('s \<Rightarrow> ennreal) \<Rightarrow> (('s pgcl \<times> 's) stream \<Rightarrow> ennreal) \<Rightarrow> ('s pgcl \<times> 's) stream \<Rightarrow> ennreal" where
  "rF f F \<omega> = (if fst (shd \<omega>) = Skip then f (snd (shd \<omega>)) else F (stl \<omega>))"

abbreviation r :: "('s \<Rightarrow> ennreal) \<Rightarrow> ('s pgcl \<times> 's) stream \<Rightarrow> ennreal" where
  "r f \<equiv> lfp (rF f)"

lemma continuous_rF: "sup_continuous (rF f)"
  unfolding rF_def[abs_def]
  by (auto simp: sup_continuous_def fun_eq_iff SUP_sup_distrib [symmetric] image_comp
           split: prod.splits pgcl.splits)

lemma mono_rF: "mono (rF f)"
  using continuous_rF by (rule sup_continuous_mono)

lemma r_unfold: "r f \<omega> = (if fst (shd \<omega>) = Skip then f (snd (shd \<omega>)) else r f (stl \<omega>))"
  by (subst lfp_unfold[OF mono_rF]) (simp add: rF_def)

lemma mono_r: "F \<le> G \<Longrightarrow> r F \<omega> \<le> r G \<omega>"
  by (rule le_funD[of _ _ \<omega>], rule lfp_mono)
     (auto intro!: lfp_mono simp: rF_def le_fun_def max.coboundedI2)

lemma measurable_rF:
  assumes F[measurable]: "F \<in> borel_measurable step.St"
  shows "rF f F \<in> borel_measurable step.St"
  unfolding rF_def[abs_def]
  apply measurable
  apply (rule measurable_compose[OF measurable_shd])
  apply measurable []
  apply (rule measurable_compose[OF measurable_stl])
  apply measurable []
  apply (rule predE)
  apply (rule measurable_compose[OF measurable_shd])
  apply measurable
  done

lemma measurable_r[measurable]: "r f \<in> borel_measurable step.St"
  using continuous_rF measurable_rF by (rule borel_measurable_lfp)

lemma mono_r': "mono (\<lambda>F s. \<Sqinter>D\<in>step s. \<integral>\<^sup>+ t. (if fst t = Skip then f (snd t) else F t) \<partial>measure_pmf D)"
  by (auto intro!: monoI le_funI INF_mono[OF bexI] nn_integral_mono simp: le_fun_def)

lemma E_inf_r:
  "step.E_inf s (r f) =
    lfp (\<lambda>F s. \<Sqinter>D\<in>step s. \<integral>\<^sup>+ t. (if fst t = Skip then f (snd t) else F t) \<partial>measure_pmf D) s"
proof -
  have "step.E_inf s (r f) =
    lfp (\<lambda>F s. \<Sqinter>D\<in>step s. \<integral>\<^sup>+ t. (if fst t = Skip then f (snd t) else F t) \<partial>measure_pmf D) s"
    unfolding rF_def[abs_def]
  proof (rule step.E_inf_lfp[THEN fun_cong])
    let ?F = "\<lambda>t x. (if fst t = Skip then f (snd t) else x)"
    show "(\<lambda>(s, x). ?F s x) \<in> borel_measurable (count_space UNIV \<Otimes>\<^sub>M borel)"
      apply (simp add: measurable_split_conv split_beta')
      apply (intro borel_measurable_max borel_measurable_const measurable_If predE
         measurable_compose[OF measurable_snd] measurable_compose[OF measurable_fst])
      apply measurable
      done
    show "\<And>s. sup_continuous (?F s)"
      by (auto simp: sup_continuous_def SUP_sup_distrib[symmetric] split: prod.split pgcl.split)
    show "\<And>F cfg. (\<integral>\<^sup>+\<omega>. ?F (state cfg) (F \<omega>) \<partial>step.T cfg) =
      ?F (state cfg) (nn_integral (step.T cfg) F)"
      by (auto simp: split: pgcl.split prod.split)
  qed (rule step_finite)
  then show ?thesis
    by simp
qed

lemma E_inf_r_unfold:
  "step.E_inf s (r f) = (\<Sqinter>D\<in>step s. \<integral>\<^sup>+ t. (if fst t = Skip then f (snd t) else step.E_inf t (r f)) \<partial>measure_pmf D)"
  unfolding E_inf_r by (simp add: lfp_unfold[OF mono_r'])

lemma E_inf_r_induct[consumes 1, case_names step]:
  assumes "P s y"
  assumes *: "\<And>F s y. P s y \<Longrightarrow>
    (\<And>s y. P s y \<Longrightarrow> F s \<le> y) \<Longrightarrow> (\<And>s. F s \<le> step.E_inf s (r f)) \<Longrightarrow>
    (\<Sqinter>D\<in>step s. \<integral>\<^sup>+ t. (if fst t = Skip then f (snd t) else F t) \<partial>measure_pmf D) \<le> y"
  shows "step.E_inf s (r f) \<le> y"
  using \<open>P s y\<close>
  unfolding E_inf_r
proof (induction arbitrary: s y rule: lfp_ordinal_induct[OF mono_r'[where f=f]])
  case (1 F) with *[of s y F] show ?case
    unfolding le_fun_def E_inf_r[where f=f, symmetric] by simp
qed (auto intro: SUP_least)

lemma E_inf_Skip: "step.E_inf (Skip, s) (r f) = f s"
  by (subst E_inf_r_unfold) simp

lemma E_inf_Seq:
  assumes [simp]: "\<And>x. 0 \<le> f x"
  shows "step.E_inf (Seq a b, s) (r f) = step.E_inf (a, s) (r (\<lambda>s. step.E_inf (b, s) (r f)))"
proof (rule antisym)
  show "step.E_inf (Seq a b, s) (r f) \<le> step.E_inf (a, s) (r (\<lambda>s. step.E_inf (b, s) (r f)))"
  proof (coinduction arbitrary: a s rule: E_inf_r_induct)
    case step then show ?case
      by (rewrite in "_ \<le> \<hole>" E_inf_r_unfold)
         (force intro!: INF_mono[OF bexI] nn_integral_mono intro: le_infI2
                simp: E_inf_Skip image_comp)
  qed
  show "step.E_inf (a, s) (r (\<lambda>s. step.E_inf (b, s) (r f))) \<le> step.E_inf (Seq a b, s) (r f)"
  proof (coinduction arbitrary: a s rule: E_inf_r_induct)
    case step then show ?case
      by (rewrite in "_ \<le> \<hole>" E_inf_r_unfold)
         (force intro!: INF_mono[OF bexI] nn_integral_mono intro: le_infI2
                simp: E_inf_Skip image_comp)
   qed
qed

lemma E_inf_While:
  "step.E_inf (While g c, s) (r f) =
    lfp (\<lambda>F s. if g s then step.E_inf (c, s) (r F) else f s) s"
proof (rule antisym)
  have E_inf_While_step: "step.E_inf (While g c, s) (r f) =
    (if g s then step.E_inf (c, s) (r (\<lambda>s. step.E_inf (While g c, s) (r f))) else f s)" for f s
    by (rewrite E_inf_r_unfold) (simp add: min_absorb1 E_inf_Seq)

  have "mono (\<lambda>F s. if g s then step.E_inf (c, s) (r F) else f s)" (is "mono ?F")
    by (auto intro!: mono_r step.E_inf_mono simp: mono_def le_fun_def max.coboundedI2)
  then show "lfp ?F s \<le> step.E_inf (While g c, s) (r f)"
  proof (induction arbitrary: s rule: lfp_ordinal_induct[consumes 1])
    case mono then show ?case
      by (rewrite E_inf_While_step) (auto intro!: step.E_inf_mono mono_r le_funI)
  qed (auto intro: SUP_least)

  define w where "w F s = (\<Sqinter>D\<in>step s. \<integral>\<^sup>+ t. (if fst t = Skip then if g (snd t) then F (c, snd t) else f (snd t) else F t) \<partial>measure_pmf D)"
    for F s
  have "mono w"
    by (auto simp: w_def mono_def le_fun_def intro!: INF_mono[OF bexI] nn_integral_mono) []

  define d where "d = c"
  define t where "t = Seq d (While g c)"
  then have "(t = While g c \<and> d = c \<and> g s) \<or> t = Seq d (While g c)"
    by auto
  then have "step.E_inf (t, s) (r f) \<le> lfp w (d, s)"
  proof (coinduction arbitrary: t d s rule: E_inf_r_induct)
    case (step F t d s)
    from step(1)
    show ?case
    proof (elim conjE disjE)
      { fix s have "\<not> g s \<Longrightarrow> F (While g c, s) \<le> f s"
          using step(3)[of "(While g c, s)"] by (simp add: E_inf_While_step) }
      note [simp] = this
      assume "t = Seq d (While g c)" then show ?thesis
        by (rewrite lfp_unfold[OF \<open>mono w\<close>])
           (auto simp: max.absorb2 w_def intro!: INF_mono[OF bexI] nn_integral_mono step)
    qed (auto intro!: step)
  qed
  also have "lfp w = lfp (\<lambda>F s. step.E_inf s (r (\<lambda>s. if g s then F (c, s) else f s)))"
    unfolding E_inf_r w_def
    by (rule lfp_lfp[symmetric]) (auto simp: le_fun_def intro!: INF_mono[OF bexI] nn_integral_mono)
  finally have "step.E_inf (While g c, s) (r f) \<le> (if g s then \<dots> (c, s) else f s)"
    unfolding t_def d_def by (rewrite E_inf_r_unfold) simp
  also have "\<dots> = lfp ?F s"
    by (rewrite lfp_rolling[symmetric, of "\<lambda>F s. if g s then F (c, s) else f s"  "\<lambda>F s. step.E_inf s (r F)"])
       (auto simp: mono_def le_fun_def sup_apply[abs_def] if_distrib[of "max 0"] max.coboundedI2 max.absorb2
                intro!: step.E_inf_mono mono_r cong del: if_weak_cong)
  finally show "step.E_inf (While g c, s) (r f) \<le> \<dots>"
    .
qed

subsection \<open>Equate Both Semantics\<close>

lemma E_inf_r_eq_wp: "step.E_inf (c, s) (r f) = wp c f s"
proof (induction c arbitrary: f s)
  case Skip then show ?case
    by (simp add: E_inf_Skip)
next
  case Abort then show ?case
  proof (intro antisym)
    have "lfp (\<lambda>F s. \<Sqinter>D\<in>step s. \<integral>\<^sup>+ t. (if fst t = Skip then f (snd t) else F t) \<partial>measure_pmf D) \<le>
      (\<lambda>s. if \<exists>t. s = (Abort, t) then 0 else \<top>)"
      by (intro lfp_lowerbound) (auto simp: le_fun_def)
    then show "step.E_inf (Abort, s) (r f) \<le> wp Abort f s"
      by (auto simp: E_inf_r le_fun_def split: if_split_asm)
  qed simp
next
  case Assign then show ?case
    by (rewrite E_inf_r_unfold) (simp add: min_absorb1)
next
  case (If b c1 c2) then show ?case
    by (rewrite E_inf_r_unfold) auto
next
  case (Prob p c1 c2) then show ?case
    apply (rewrite E_inf_r_unfold)
    apply auto
    apply (rewrite nn_integral_measure_pmf_support[of "UNIV::bool set"])
    apply (auto simp: UNIV_bool ac_simps)
    done
next
  case (Par c1 c2) then show ?case
    by (rewrite E_inf_r_unfold) (auto intro: inf.commute)
next
  case (Seq c1 c2) then show ?case
    by (simp add: E_inf_Seq)
next
  case (While g c) then show ?case
    apply (simp add: E_inf_While)
    apply (rewrite While)
    apply auto
    done
qed

end
