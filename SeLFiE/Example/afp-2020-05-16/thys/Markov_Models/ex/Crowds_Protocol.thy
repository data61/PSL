(* Author: Johannes Hölzl <hoelzl@in.tum.de> *)

section \<open>Formalization of the Crowds-Protocol\<close>

theory Crowds_Protocol
  imports "../Discrete_Time_Markov_Chain"
begin

lemma cond_prob_nonneg[simp]: "0 \<le> cond_prob M A B"
  by (auto simp: cond_prob_def)

lemma (in MC_syntax) emeasure_suntil_geometric:
  assumes [measurable]: "Measurable.pred S P"
  assumes "s \<in> X" and *[simp]: "0 \<le> p" "0 \<le> r"
  assumes r: "\<And>s. s \<in> X \<Longrightarrow> emeasure (T s) {\<omega>\<in>space (T s). P \<omega>} = ennreal r"
  assumes p: "\<And>s. s \<in> X \<Longrightarrow> emeasure (K s) X = ennreal p" "p < 1"
  assumes "\<And>t. AE \<omega> in T t. \<not> (P \<sqinter> (HLD X \<sqinter> nxt (HLD X suntil P))) \<omega>"
  shows "emeasure (T s) {\<omega>\<in>space (T s). (HLD X suntil P) \<omega>} = r / (1 - p)"
proof (subst emeasure_suntil_disj)
  let ?F = "\<lambda>F s. emeasure (T s) {\<omega> \<in> space (T s). P \<omega>} + \<integral>\<^sup>+ t. F t * indicator X t \<partial>K s"
  let ?f = "\<lambda>x. ennreal r + ennreal p * x"

  have "mono ?F" "mono ?f"
    by (auto intro!: monoI max.mono add_mono nn_integral_mono mult_left_mono mult_right_mono simp: le_fun_def)

  have 1: "lfp ?f \<le> lfp ?F s"
    using \<open>s \<in> X\<close>
  proof (induction arbitrary: s rule: lfp_ordinal_induct[OF \<open>mono ?f\<close>])
    case step: (1 x)
    then have "?f x \<le> ?F (\<lambda>_. x) s"
      by (auto simp: p r[simplified] nn_integral_cmult mult.commute[of _ x]
               intro!: add_mono mult_right_mono)
    also have "?F (\<lambda>_. x) \<le> ?F (lfp ?F)"
      using step
      by (intro le_funI add_mono order_refl nn_integral_mono) (auto simp: split: split_indicator)
    finally show ?case
      by (subst lfp_unfold[OF \<open>mono ?F\<close>]) (auto simp: le_fun_def)
  qed (auto intro!: Sup_least)
  also have 2: "lfp ?F s \<le> r / (1 - p)"
    using \<open>s \<in> X\<close>
  proof (induction arbitrary: s rule: lfp_ordinal_induct[OF \<open>mono ?F\<close>])
    case (1 S)
    with r have "?F S s \<le> ennreal r + (\<integral>\<^sup>+x. ennreal (r / (1 - p)) * indicator X x \<partial>K s)"
      by (intro add_mono nn_integral_mono) (auto split: split_indicator)
    also have "\<dots> \<le> ennreal r + ennreal (r * p / (1 - p))"
      using \<open>s \<in> X\<close> by (simp add: nn_integral_cmult_indicator p ennreal_mult''[symmetric])
    also have "\<dots> = ennreal (r / (1 - p))"
      using \<open>p < 1\<close> by (simp add: field_simps ennreal_plus[symmetric] del: ennreal_plus)
    finally show ?case .
  qed (auto intro!: SUP_least)
  finally obtain x where x: "lfp ?f = ennreal x" and [simp]: "0 \<le> x"
    by (cases "lfp ?f") (auto simp: top_unique)
  from \<open>p < 1\<close> have "\<And>x. x = r + p * x \<Longrightarrow> x = r / (1 - p)"
    by (auto simp: field_simps)
  with lfp_unfold[OF \<open>mono ?f\<close>] \<open>p < 1\<close> have "lfp ?f = r / (1 - p)"
    unfolding x by (auto simp add: ennreal_plus[symmetric] ennreal_mult[symmetric] simp del: ennreal_plus)
  with 1 2 show "lfp ?F s = ennreal (r / (1 - p))"
    by auto
qed fact+

subsection \<open>Definition of the Crowds-Protocol\<close>

datatype 'a state = Start | Init 'a | Mix 'a | End

lemma inj_Mix[simp]: "inj_on Mix A"
  by (auto intro: inj_onI)

lemma inj_Init[simp]: "inj_on Init A"
  by (auto intro: inj_onI)

lemma distinct_state_image[simp]:
  "Start \<notin> Mix ` A" "Init j \<notin> Mix ` A" "End \<notin> Mix ` A" "Mix j \<in> Mix ` A \<longleftrightarrow> j \<in> A"
  "Start \<notin> Init ` A" "Mix j \<notin> Init ` A" "End \<notin> Init ` A" "Init j \<in> Init ` A \<longleftrightarrow> j \<in> A"
  by auto

lemma Init_cut_Mix[simp]:
  "Init ` H \<inter> Mix ` J = {}"
  by auto

abbreviation "Jondo B \<equiv> Init`B \<union> Mix`B"

locale Crowds_Protocol =
  fixes J :: "'a set" and C :: "'a set" and p_f :: real and p_i :: "'a \<Rightarrow> real"
  assumes J_not_empty: "J \<noteq> {}" and finite_J[simp]: "finite J"
  assumes C_smaller: "C \<subset> J" and C_non_empty: "C \<noteq> {}"
  assumes p_f: "0 < p_f" "p_f < 1"
  assumes p_i_nonneg[simp]: "\<And>j. j \<in> J \<Longrightarrow> 0 \<le> p_i j"
  assumes p_i_distr: "(\<Sum>j\<in>J. p_i j) = 1"
  assumes p_i_C: "\<And>j. j \<in> C \<Longrightarrow> p_i j = 0"
begin

abbreviation H :: "'a set" where
  "H \<equiv> J - C"

definition "p_j = 1 / card J"

lemma p_f_nonneg[simp]: "0 \<le> p_f" "p_f \<le> 1"
  using p_f by simp_all

lemma p_j_nonneg[simp]: "0 \<le> p_j"
  by (simp add: p_j_def)

definition "p_H = card H / card J"

lemma p_H_nonneg[simp]: "0 \<le> p_H" "p_H \<le> 1"
  by (auto simp: p_H_def divide_le_eq_1 card_gt_0_iff intro!: card_mono )

definition next_prob :: "'a state \<Rightarrow> 'a state \<Rightarrow> real" where
  "next_prob s t = (case (s, t) of (Start, Init j) \<Rightarrow> if j \<in> H then p_i j else 0
                                 | (Init j, Mix j') \<Rightarrow> if j' \<in> J then p_j else 0
                                 | (Mix j, Mix j') \<Rightarrow> if j' \<in> J then p_f * p_j else 0
                                 | (Mix j, End) \<Rightarrow> 1 - p_f
                                 | (End, End) \<Rightarrow> 1
                                 | _ \<Rightarrow> 0)"

definition "N s = embed_pmf (next_prob s)"

interpretation MC_syntax N .

abbreviation "\<PP> \<equiv> T Start"

abbreviation "E s \<equiv> set_pmf (N s)"

lemma finite_C[simp]: "finite C"
  using C_smaller finite_J by (blast intro: finite_subset)

lemma sum_p_i_C[simp]: "sum p_i C = 0"
  by (auto intro: sum.neutral p_i_C)

lemma sum_p_i_H[simp]: "sum p_i H = 1"
  using C_smaller by (simp add: sum_diff p_i_distr)

lemma possible_jondo:
  obtains j where "j \<in> J" "j \<notin> C" "p_i j \<noteq> 0"
proof (atomize_elim, rule ccontr)
  assume "\<not> (\<exists>j. j \<in> J \<and> j \<notin> C \<and> p_i j \<noteq> 0)"
  with p_i_C have "\<forall>j\<in>J. p_i j = 0"
    by auto
  with p_i_distr show False
    by simp
qed

lemma C_le_J[simp]: "card C < card J"
  using C_smaller
  by (intro psubset_card_mono) auto

lemma p_H: "0 < p_H" "p_H < 1"
  using J_not_empty C_smaller C_non_empty
  by (simp_all add: p_H_def card_Diff_subset card_mono field_simps zero_less_divide_iff card_gt_0_iff)

lemma p_H_p_f_pos: "0 < p_H * p_f"
  using p_f p_H by (simp add: zero_less_mult_iff)

lemma p_H_p_f_less_1: "p_H * p_f < 1"
proof -
  have "p_H * p_f < 1 * 1"
    using p_H p_f by (intro mult_strict_mono) auto
  then show "p_H * p_f < 1" by simp
qed

lemma p_j_pos: "0 < p_j"
  unfolding p_j_def using J_not_empty by auto

lemma H_compl: "1 - p_H = real (card C) / real (card J)"
  using C_non_empty J_not_empty C_smaller
  by (simp add: p_H_def card_Diff_subset card_mono of_nat_diff divide_eq_eq field_simps)

lemma H_compl2: "1 - p_H = card C * p_j"
  unfolding H_compl p_j_def by simp

lemma H_eq2: "card H * p_j = p_H"
  unfolding p_j_def p_H_def by simp

lemma pmf_next_pmf[simp]: "pmf (N s) t = next_prob s t"
  unfolding N_def
proof (rule pmf_embed_pmf)
  show "\<And>x. 0 \<le> next_prob s x"
    using p_j_pos p_f by (auto simp: next_prob_def intro: p_i_nonneg split: state.split)
  show "(\<integral>\<^sup>+ x. ennreal (next_prob s x) \<partial>count_space UNIV) = 1"
    using p_f J_not_empty
    by (subst nn_integral_count_space'[where A="Init`H \<union> Mix`J \<union> {End}"])
       (auto simp: next_prob_def sum.reindex sum.union_disjoint p_i_distr p_j_def
             split: state.split)
qed

lemma next_prob_Start[simp]: "next_prob Start (Init j) = (if j \<in> H then p_i j else 0)"
  by (auto simp: next_prob_def)

lemma next_prob_to_Init[simp]: "j \<in> H \<Longrightarrow> next_prob s (Init j) =
    (case s of Start \<Rightarrow> p_i j | _ \<Rightarrow> 0)"
  by (cases s) (auto simp: next_prob_def)

lemma next_prob_to_Mix[simp]: "j \<in> J \<Longrightarrow> next_prob s (Mix j) =
    (case s of Init j \<Rightarrow> p_j | Mix j \<Rightarrow> p_f * p_j | _ \<Rightarrow> 0)"
  by (cases s) (auto simp: next_prob_def)

lemma next_prob_to_End[simp]: "next_prob s End =
    (case s of Mix j \<Rightarrow> 1 - p_f | End \<Rightarrow> 1 | _ \<Rightarrow> 0)"
  by (cases s) (auto simp: next_prob_def)

lemma next_prob_from_End[simp]: "next_prob End s = 0 \<longleftrightarrow> s \<noteq> End"
  by (cases s) (auto simp: next_prob_def)

lemma next_prob_Mix_MixI: "\<exists>j. s = Mix j \<Longrightarrow> \<exists>j\<in>J. s' = Mix j \<Longrightarrow> next_prob s s' = p_f * p_j"
  by (cases s) auto


lemma E_Start: "E Start = {Init j | j. j \<in> H \<and> p_i j \<noteq> 0 }"
  using p_i_C by (auto simp: set_pmf_iff next_prob_def split: state.splits if_split_asm)

lemma E_Init: "E (Init j) = {Mix j | j. j \<in> J }"
  using p_j_pos C_smaller by (auto simp: set_pmf_iff next_prob_def split: state.splits if_split_asm)

lemma E_Mix: "E (Mix j) = {Mix j | j. j \<in> J } \<union> {End}"
  using p_j_pos p_f by (auto simp: set_pmf_iff next_prob_def split: state.splits if_split_asm)

lemma E_End: "E End = {End}"
  by (auto simp: set_pmf_iff next_prob_def split: state.splits if_split_asm)

lemma enabled_End:
  "enabled End \<omega> \<longleftrightarrow> \<omega> = sconst End"
proof safe
  assume "enabled End \<omega>" then show "\<omega> = sconst End"
  proof (coinduction arbitrary: \<omega>)
    case Eq_stream then show ?case
      by (auto simp: enabled.simps[of _ \<omega>] E_End)
  qed
next
  show "enabled End (sconst End)"
    by coinduction (simp add: E_End)
qed

lemma AE_End: "(AE \<omega> in T End. P \<omega>) \<longleftrightarrow> P (sconst End)"
proof -
  have "(AE \<omega> in T End. P \<omega>) \<longleftrightarrow> (AE \<omega> in T End. P \<omega> \<and> \<omega> = sconst End)"
    using AE_T_enabled[of End] by (simp add: enabled_End)
  also have "\<dots> = (AE \<omega> in T End. P (sconst End) \<and> \<omega> = sconst End)"
    by (simp add: enabled_End del: AE_conj_iff cong: rev_conj_cong)
  also have "\<dots> = (AE \<omega> in T End. P (sconst End))"
    using AE_T_enabled[of End] by (simp add: enabled_End)
  finally show ?thesis
    by simp
qed

lemma emeasure_Init_eq_Mix:
  assumes [measurable]: "Measurable.pred S P"
  assumes AE_End: "AE x in T End. \<not> P (End ## x)"
  shows "emeasure (T (Init j)) {x\<in>space (T (Init j)). P x} =
    emeasure (T (Mix j)) {x\<in>space (T (Mix j)). P x} / p_f"
proof -
  have *: "{Mix j | j. j \<in> J } = Mix ` J"
    by auto
  show ?thesis
    using emeasure_eq_0_AE[OF AE_End] p_f
    apply (subst (1 2) emeasure_Collect_T)
    apply simp
    apply (subst (1 2) nn_integral_measure_pmf_finite)
    apply (auto simp: E_Mix E_Init * sum.reindex sum_distrib_right[symmetric] divide_ennreal
      ennreal_times_divide[symmetric])
    done
qed

text \<open>

What is the probability that the server sees a specific jondo (including the initiator) as sender.

\<close>

definition visit :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a state stream \<Rightarrow> bool" where
  "visit I L = Init`(I \<inter> H) \<cdot> (HLD (Mix`J) suntil (Mix`(L \<inter> J) \<cdot> HLD {End}))"

lemma visit_unique1:
  "visit I1 L1 \<omega> \<Longrightarrow> visit I2 L2 \<omega> \<Longrightarrow> I1 \<inter> I2 \<noteq> {}"
  by (auto simp: visit_def HLD_iff)

lemma visit_unique2:
  assumes "visit I1 L1 \<omega>" "visit I2 L2 \<omega>"
  shows "L1 \<inter> L2 \<noteq> {}"
proof -
  let ?U = "\<lambda>L \<omega>. (HLD (Mix`J) suntil ((Mix`(L\<inter>J)) \<cdot> HLD {End})) \<omega>"
  have "?U L1 (stl \<omega>)" "?U L2 (stl \<omega>)"
    using assms by (auto simp: visit_def)
  then show "L1 \<inter> L2 \<noteq> {}"
  proof (induction "stl \<omega>" arbitrary: \<omega> rule: suntil_induct_strong)
    case base then show ?case
      by (auto simp add: suntil.simps[of _ _ "stl (stl \<omega>)"] suntil.simps[of _ _ "stl \<omega>"] HLD_iff)
  next
    case step
    show ?case
    proof cases
      assume "((Mix`(L2\<inter>J)) \<cdot> HLD {End}) (stl \<omega>)"
      with step.hyps show ?thesis
        by (auto simp: inj_Mix HLD_iff elim: suntil.cases)
    next
      assume "\<not> ((Mix`(L2\<inter>J)) \<cdot> HLD {End}) (stl \<omega>)"
      with step.prems have "?U L2 (stl (stl \<omega>))"
        by (auto elim: suntil.cases)
      then show ?thesis
        by (rule step.hyps(4)[OF refl])
    qed
  qed
qed

lemma visit_imp_in_H: "visit {i} J \<omega> \<Longrightarrow> i \<in> H"
  by (auto simp: visit_def HLD_iff)

lemma emeasure_visit:
  assumes I: "I \<subseteq> H" and L: "L \<subseteq> J"
  shows "emeasure \<PP> {\<omega>\<in>space \<PP>. visit I L \<omega>} = (\<Sum>i\<in>I. p_i i) * (card L * p_j)"
proof -
  let ?J = "HLD (Mix`J)" and ?E = "(Mix`L) \<cdot> HLD {End}"
  let ?\<phi> = "?J aand not ?E"
  let ?P = "\<lambda>x P. emeasure (T x) {\<omega>\<in>space (T x). P \<omega>}"

  have [intro]: "finite L"
    using finite_J \<open>L \<subseteq> J\<close> by (blast intro: finite_subset)
  have [simp, intro]: "finite I"
    using finite_J \<open>I \<subseteq> H\<close> by (blast intro: finite_subset)

  { fix j assume j: "j \<in> H"
    have "?P (Mix j) (?J suntil ?E) = (p_f * p_j * (1 - p_f) * card L) / (1 - p_f)"
    proof (rule emeasure_suntil_geometric)
      fix s assume s: "s \<in> Mix ` J"
      then have "?P s ?E = (\<integral>\<^sup>+x. ennreal (1 - p_f) * indicator (Mix`L) x \<partial>N s)"
        by (auto simp add: emeasure_HLD_nxt emeasure_HLD AE_measure_pmf_iff emeasure_pmf_single
                 split: state.split split_indicator simp del: space_T nxt.simps
                 intro!: nn_integral_cong_AE)
      also have "\<dots> = ennreal (1 - p_f) * emeasure (N s) (Mix`L)"
        using p_f by (intro nn_integral_cmult_indicator) auto
      also have "\<dots> = ennreal ((1 - p_f) * card L * p_j * p_f)"
        using s assms
        by (subst emeasure_measure_pmf_finite)
           (auto simp: sum.reindex subset_eq ennreal_mult mult_ac)
      finally show "?P s ?E = p_f * p_j * (1 - p_f) * card L"
        by simp
    next
      show "\<And>t. AE \<omega> in T  t. \<not> (?E \<sqinter> (?J \<sqinter> nxt (?J suntil ?E))) \<omega>"
        by (intro AE_I2) (auto simp: HLD_iff elim: suntil.cases)
    qed (insert p_f j, auto simp: emeasure_measure_pmf_finite sum.reindex p_j_def)
    then have "?P (Init j) (?J suntil ?E) = (p_f * p_j * (1 - p_f) * card L) / (1 - p_f) / p_f"
      by (subst emeasure_Init_eq_Mix) (simp_all add:  suntil.simps[of _ _ "x ## s" for x s] divide_ennreal p_f)
    then have "?P (Init j) (?J suntil ?E) = p_j * card L"
      using p_f by simp }
  note J_suntil_E = this

  have "?P Start (visit I L) = (\<integral>\<^sup>+x. ?P x (?J suntil ?E) * indicator (Init`I) x \<partial>N Start)"
    unfolding visit_def using I L by (subst emeasure_HLD_nxt) (auto simp: Int_absorb2)
  also have "\<dots> = (\<integral>\<^sup>+x. ennreal (p_j * card L) * indicator (Init`I) x \<partial>N Start)"
    using I J_suntil_E
    by (intro nn_integral_cong ennreal_mult_right_cong)
       (auto split: split_indicator_asm)
  also have "\<dots> = ennreal ((\<Sum>i\<in>I. p_i i) * card L * p_j)"
    using p_j_pos assms
    by (subst nn_integral_cmult_indicator)
       (auto simp: emeasure_measure_pmf_finite sum.reindex subset_eq ennreal_mult[symmetric] sum_nonneg)
  finally show ?thesis by (simp add: ac_simps)
qed

lemma measurable_visit[measurable]: "Measurable.pred S (visit I L)"
  by (simp add: visit_def)

lemma AE_visit: "AE \<omega> in \<PP>. visit H J \<omega>"
proof (rule T.AE_I_eq_1)
  show "emeasure \<PP> {\<omega>\<in>space \<PP>. visit H J \<omega>} = 1"
    using J_not_empty by (subst emeasure_visit ) (simp_all add: p_j_def)
qed simp

subsection \<open>Server gets no information\<close>

lemma server_view1: "j \<in> J \<Longrightarrow> \<P>(\<omega> in \<PP>. visit H {j} \<omega>) = p_j"
  unfolding measure_def by (subst emeasure_visit) simp_all

lemma server_view_indep:
  "L \<subseteq> J \<Longrightarrow> I \<subseteq> H \<Longrightarrow> \<P>(\<omega> in \<PP>. visit I L \<omega>) = \<P>(\<omega> in \<PP>. visit H L \<omega>) * \<P>(\<omega> in \<PP>. visit I J \<omega>)"
  unfolding measure_def
  by (subst (1 2 3) emeasure_visit) (auto simp: p_j_def sum_nonneg subset_eq)

lemma server_view: "\<P>(\<omega> in \<PP>. \<exists>j\<in>H. visit {j} {j} \<omega>) = p_j"
  using finite_J
proof (subst T.prob_sum[where I="H" and P="\<lambda>j. visit {j} {j}"])
  show "(\<Sum>j\<in>H. \<P>(\<omega> in \<PP>. visit {j} {j} \<omega>)) = p_j"
    by (auto simp: measure_def emeasure_visit sum_distrib_right[symmetric] simp del: space_T sets_T)
  show "AE x in \<PP>. (\<forall>n\<in>H. visit {n} {n} x \<longrightarrow> (\<exists>j\<in>H. visit {j} {j} x)) \<and>
                ((\<exists>j\<in>H. visit {j} {j} x) \<longrightarrow> (\<exists>!n. n \<in> H \<and> visit {n} {n} x))"
    by (auto dest: visit_unique1)
qed simp_all

subsection \<open>Probability that collaborators gain information\<close>

definition "hit_C = Init`H \<cdot> ev (HLD (Mix`C))"
definition "before_C B = (HLD (Jondo H)) suntil ((Jondo (B \<inter> H)) \<cdot> HLD (Mix ` C))"

lemma measurable_hit_C[measurable]: "Measurable.pred S hit_C"
  by (simp add: hit_C_def)

lemma measurable_before_C[measurable]: "Measurable.pred S (before_C B)"
  by (simp add: before_C_def)

lemma before_C:
  assumes \<omega>: "enabled Start \<omega>"
  shows "before_C B \<omega> \<longleftrightarrow>
    ((Init`H \<cdot> (HLD (Mix`H) suntil (Mix`(B \<inter> H) \<cdot> HLD (Mix`C)))) or (Init`(B \<inter> H) \<cdot> HLD (Mix`C))) \<omega>"
proof -
  { fix \<omega> s assume "((HLD (Jondo H)) suntil (Jondo (B \<inter> H) \<cdot> HLD (Mix ` C))) \<omega>"
      "enabled s \<omega>" "s \<in> Jondo H"
    then have "(HLD (Mix ` H) suntil (Mix ` (B \<inter> H) \<cdot> (HLD (Mix ` C)))) \<omega>"
    proof (induction arbitrary: s)
      case (base \<omega>) then show ?case
        by (auto simp: HLD_iff enabled.simps[of _ \<omega>] E_Init E_Mix intro!: suntil.intros(1))
    next
      case (step \<omega>) from step.prems step.hyps step.IH[of "shd \<omega>"] show ?case
        by (auto simp: HLD_iff enabled.simps[of _ \<omega>] E_Init E_Mix
                       suntil.simps[of _ _ \<omega>] enabled_End suntil_sconst)
    qed }
  note this[of "stl \<omega>" "shd \<omega>"]
  moreover
  { fix \<omega> s assume "(HLD (Mix ` H) suntil (Mix ` (B \<inter> H) \<cdot> (HLD (Mix ` C)))) \<omega>"
      "enabled s \<omega>" "s \<in> Jondo H"
    then have "((HLD (Jondo H)) suntil ((Jondo (B \<inter> H)) \<cdot> HLD (Mix ` C))) \<omega>"
    proof (induction arbitrary: s)
      case (step \<omega>) from step.prems step.hyps step.IH[of "shd \<omega>"] show ?case
        by (auto simp: HLD_iff enabled.simps[of _ \<omega>] E_Init E_Mix
                       suntil.simps[of _ _ \<omega>] enabled_End suntil_sconst)
    qed (auto intro: suntil.intros simp: HLD_iff) }
  note this[of "stl \<omega>" "shd \<omega>"]
  ultimately show ?thesis
    using assms
    using \<open>enabled Start \<omega>\<close>
    unfolding before_C_def suntil.simps[of _ _ \<omega>] enabled.simps[of _ \<omega>]
    by (auto simp: E_Start HLD_iff)
qed

lemma before_C_unique:
  assumes \<omega>: "before_C I1 \<omega>" "before_C I2 \<omega>" shows "I1 \<inter> I2 \<noteq> {}"
  using \<omega> unfolding before_C_def
proof induction
  case (base \<omega>) then show ?case
    by (auto simp add: suntil.simps[of _ _ \<omega>] suntil.simps[of _ _ "stl \<omega>"] HLD_iff)
next
  case (step \<omega>) then show ?case
    by (auto simp add: suntil.simps[of _ _ \<omega>] suntil.simps[of _ _ "stl \<omega>"] HLD_iff)
qed

lemma hit_C_imp_before_C:
  assumes "enabled Start \<omega>" "hit_C \<omega>" shows "before_C H \<omega>"
proof -
  let ?X = "Init`H \<union> Mix`H"
  { fix \<omega> s assume "ev (HLD (Mix`C)) \<omega>" "s\<in>?X" "enabled s \<omega>"
    then have "((HLD (Jondo H)) suntil (?X \<cdot> HLD (Mix ` C))) (s ## \<omega>)"
    proof (induction arbitrary: s rule: ev_induct_strong)
      case (step \<omega> s) from step.IH[of "shd \<omega>"] step.prems step.hyps show ?case
        by (auto simp: enabled.simps[of _ \<omega>] suntil_Stream E_Init E_Mix HLD_iff
          enabled_End ev_sconst)
    qed (auto simp: suntil_Stream) }
  from this[of "stl \<omega>" "shd \<omega>"] assms show ?thesis
    by (auto simp: before_C_def hit_C_def enabled.simps[of _ \<omega>] E_Start)
qed

lemma before_C_single:
  assumes "before_C I \<omega>" shows "\<exists>i\<in>I \<inter> H. before_C {i} \<omega>"
  using assms unfolding before_C_def by induction (auto simp: HLD_iff intro: suntil.intros)

lemma before_C_imp_in_H: "before_C {i} \<omega> \<Longrightarrow> i \<in> H"
  by (auto dest: before_C_single)

subsection \<open>The probability that the sender hits a collaborator\<close>

lemma Pr_hit_C: "\<P>(\<omega> in \<PP>. hit_C \<omega>) = (1 - p_H) / (1 - p_H * p_f)"
proof -
  let ?P = "\<lambda>x P. emeasure (T x) {\<omega>\<in>space (T x). P \<omega>}"
  let ?M = "HLD (Mix ` C)" and ?I = "Init`H" and ?J = "Mix`H"
  let ?\<phi> = "(HLD ?J) aand not ?M"

  { fix s assume s: "s \<in> Jondo J"
    have "AE \<omega> in T s. ev ?M \<omega> \<longleftrightarrow> (HLD ?J suntil ?M) \<omega>"
      using AE_T_enabled
    proof eventually_elim
      fix \<omega> assume \<omega>: "enabled s \<omega>"
      show "ev ?M \<omega> \<longleftrightarrow> (HLD ?J suntil ?M) \<omega>"
      proof
        assume "ev ?M \<omega>"
        from this \<omega> s show "(HLD ?J suntil ?M) \<omega>"
        proof (induct arbitrary: s rule: ev_induct_strong)
          case (step \<omega>) then show ?case
            by (auto simp: HLD_iff enabled.simps[of _ \<omega>] suntil.simps[of _ _ \<omega>] E_End E_Init E_Mix
                           enabled_End ev_sconst)
        qed (auto simp: HLD_iff E_Init intro: suntil.intros)
      qed (rule ev_suntil)
    qed }
  note ev_eq_suntil = this

  have "?P Start hit_C = (\<integral>\<^sup>+x. ?P x (ev ?M) * indicator ?I x \<partial>N Start)"
    unfolding hit_C_def by (rule emeasure_HLD_nxt) measurable
  also have "\<dots> = (\<integral>\<^sup>+x. ennreal ((1 - p_H) / (1 - p_f * p_H)) * indicator ?I x \<partial>N Start)"
  proof (intro nn_integral_cong ennreal_mult_right_cong refl)
    fix x assume "indicator (Init ` H) x \<noteq> 0"
    then have "x \<in> ?I"
      by (auto split: split_indicator_asm)
    { fix j assume j: "j \<in> H"
      with ev_eq_suntil[of "Mix j"] have "?P (Mix j) (ev ?M) = ?P (Mix j) ((HLD ?J) suntil ?M)"
        by (intro emeasure_eq_AE) auto
      also have "\<dots> = (((1 - p_H) * p_f)) / (1 - p_H * p_f)"
      proof (rule emeasure_suntil_geometric)
        fix s assume s: "s \<in> Mix ` H"
        from s C_smaller show "?P s ?M = ennreal ((1 - p_H) * p_f)"
          by (subst emeasure_HLD)
             (auto simp add: emeasure_measure_pmf_finite sum.reindex subset_eq p_j_def H_compl)
        from s show "emeasure (N s) (Mix`H) = p_H * p_f"
          by (auto simp: emeasure_measure_pmf_finite sum.reindex p_H_def p_j_def)
      qed (insert j, auto simp: HLD_iff p_H_p_f_less_1)
      finally have "?P (Init j) (ev ?M) = (1 - p_H) / (1 - p_H * p_f)"
        using p_f
        by (subst emeasure_Init_eq_Mix)
           (auto simp: ev_Stream AE_End ev_sconst HLD_iff mult_le_one divide_ennreal) }
    then show "?P x (ev ?M) = (1 - p_H) / (1 - p_f * p_H)"
      using \<open>x \<in> ?I\<close> by (auto simp: mult_ac)
  qed
  also have "\<dots> = ennreal ((1 - p_H) / (1 - p_H * p_f))"
    using p_j_pos p_H p_H_p_f_less_1
    by (subst nn_integral_cmult_indicator)
       (auto simp: emeasure_measure_pmf_finite sum.reindex subset_eq mult_ac
             intro!: divide_nonneg_nonneg)
  finally show ?thesis
    by (simp add: measure_def mult_le_one)
qed

lemma before_C_imp_hit_C:
  assumes "enabled Start \<omega>" "before_C B \<omega>"
  shows "hit_C \<omega>"
proof -
  { fix \<omega> j assume "((HLD (Jondo H)) suntil (Jondo (B \<inter> H) \<cdot> HLD (Mix ` C))) \<omega>"
      "j \<in> H" "enabled (Mix j) \<omega>"
    then have "ev (HLD (Mix`C)) \<omega>"
    proof (induction arbitrary: j rule: suntil_induct_strong)
      case (step \<omega>) then show ?case
        by (auto simp: enabled.simps[of _ \<omega>] E_Mix enabled_End ev_sconst suntil_sconst HLD_iff)
    qed auto }
  from this[of "stl (stl \<omega>)"] assms show "hit_C \<omega>"
    by (force simp: before_C_def hit_C_def E_Start HLD_iff E_Init
      enabled.simps[of _ \<omega>] ev.simps[of _ \<omega>] suntil.simps[of _ _ \<omega>]
      enabled.simps[of _ "stl \<omega>"] ev.simps[of _ "stl \<omega>"] suntil.simps[of _ _ "stl \<omega>"])
qed

lemma negE: "\<not> P \<Longrightarrow> P \<Longrightarrow> False"
  by blast

lemma Pr_visit_before_C:
  assumes L: "L \<subseteq> H" and I: "I \<subseteq> H"
  shows "\<P>(\<omega> in \<PP>. visit I J \<omega> \<and> before_C L \<omega> \<bar> hit_C \<omega> ) =
    (\<Sum>i\<in>I. p_i i) * card L * p_j * p_f + (\<Sum>i\<in>I \<inter> L. p_i i) * (1 - p_H * p_f)"
proof -
  let ?M = "Mix`H"
  let ?P = "\<lambda>x P. emeasure (T x) {\<omega>\<in>space (T x). P \<omega>}"
  let ?V = "(visit I J aand before_C L) aand hit_C"
  let ?U = "HLD ?M suntil (Mix`L \<cdot> HLD (Mix`C))"
  let ?L = "HLD (Mix`C)"

  have IJ: "x \<in> I \<Longrightarrow> x \<in> J" for x
    using I by auto

  have [simp, intro]: "finite I" "finite L"
    using L I by (auto dest: finite_subset)

  have "?P Start ?V = ?P Start ((Init`I \<cdot> ?U) or (Init`(I \<inter> L) \<cdot> ?L))"
  proof (rule emeasure_Collect_eq_AE)
    show "AE \<omega> in \<PP>. ?V \<omega> \<longleftrightarrow> ((Init`I \<cdot> ?U) or (Init`(I \<inter> L) \<cdot> ?L)) \<omega>"
      using AE_T_enabled AE_visit
    proof eventually_elim
      case (elim \<omega>)
      then show ?case
        using before_C_imp_hit_C[of \<omega> "L"]  before_C[of \<omega> "L"] I L
        by (auto simp: visit_def HLD_iff Int_absorb2)
    qed
    show "Measurable.pred \<PP> ((Init`I \<cdot> ?U) or (Init`(I \<inter> L) \<cdot> ?L))"
      by measurable
  qed measurable
  also have "\<dots> = ?P Start (Init`I \<cdot> ?U) + ?P Start (Init`(I \<inter> L) \<cdot> ?L)"
    using L I
    apply (subst plus_emeasure)
    apply (auto intro!: arg_cong2[where f=emeasure])
    apply (subst (asm) suntil.simps)
    apply (auto simp add: HLD_iff[abs_def] elim: suntil.cases)
    done
  also have "?P Start (Init`(I \<inter> L) \<cdot> ?L) = (\<Sum>i\<in>I\<inter>L. p_i i * (1 - p_H))"
    using L I C_smaller p_j_pos
    apply (subst emeasure_HLD_nxt emeasure_HLD, simp)+
    apply (subst nn_integral_indicator_finite)
    apply (auto simp: emeasure_measure_pmf_finite sum.reindex next_prob_def sum.If_cases
                      Int_absorb2 H_compl2 ennreal_mult[symmetric] sum_nonneg
                      sum_distrib_left[symmetric] sum_distrib_right[symmetric]
                intro!: sum.cong sum_nonneg)
    apply (subst (asm) ennreal_inj)
    apply (auto intro!: mult_nonneg_nonneg sum_nonneg sum.mono_neutral_left elim!: negE)
    done
  also have "?P Start (Init`I \<cdot> ?U) = (\<Sum>i\<in>I. ?P (Init i) ?U * p_i i)"
    using I
    by (subst emeasure_HLD_nxt, simp)
       (auto simp: nn_integral_indicator_finite sum.reindex emeasure_measure_pmf_finite
             intro!: sum.cong[OF refl])
  also have "\<dots> = (\<Sum>i\<in>I. ennreal (p_f * (1 - p_H) * p_j * card L / (1 - p_H * p_f)) * p_i i)"
  proof (intro sum.cong refl arg_cong2[where f="(*)"])
    fix i assume "i \<in> I"
    with I have i: "i \<in> H"
      by auto
    have "?P (Mix i) ?U = (p_f * p_f * (1 - p_H) * p_j * card L / (1 - p_H * p_f))"
      unfolding before_C_def
    proof (rule emeasure_suntil_geometric[where X="?M"])
      show "Mix i \<in> ?M"
        using i by auto
    next
      fix s assume "s \<in> ?M"
      with p_f p_j_pos L C_smaller[THEN less_imp_le]
      show "?P s (Mix`L \<cdot> (HLD (Mix ` C))) = ennreal (p_f * p_f * (1 - p_H) * p_j * card L)"
        apply (simp add: emeasure_HLD emeasure_HLD_nxt del: nxt.simps space_T)
        apply (subst nn_integral_measure_pmf_support[of "Mix`L"])
        apply (auto simp add: subset_eq emeasure_measure_pmf_finite sum.reindex H_compl p_j_def
          ennreal_mult[symmetric] ennreal_of_nat_eq_real_of_nat)
        done
    next
      fix s assume "s \<in> ?M" then show "emeasure (N s) ?M = ennreal (p_H * p_f)"
        by (auto simp add: emeasure_measure_pmf_finite sum.reindex H_eq2)
    next
      show "AE \<omega> in T t. \<not> ((Mix ` L \<cdot> ?L) \<sqinter> (HLD (Mix ` H) \<sqinter> nxt ?U)) \<omega>" for t
        using L
        apply (simp add: AE_T_iff[of _ t])
        apply (subst AE_T_iff; simp)
        apply (auto simp: HLD_iff suntil_Stream)
        done
    qed (insert L, auto simp: p_H_p_f_less_1 E_Mix)
    then show "?P (Init i) ?U = p_f * (1 - p_H) * p_j * card L / (1 - p_H * p_f)"
      by (subst emeasure_Init_eq_Mix)
         (auto simp: AE_End suntil_Stream divide_ennreal mult_le_one p_f)
  qed
  finally have *: "\<P>(\<omega> in T Start. ?V \<omega>) =
      (p_f * (1 - p_H) * p_j * (card L) / (1 - p_H * p_f)) * (\<Sum>i\<in>I. p_i i) +
      (\<Sum>i\<in>I \<inter> L. p_i i) * (1 - p_H)"
    using sum_nonneg [of "I \<inter> L" p_i]  sum_nonneg [of "I" p_i]
    by (simp add: mult_ac measure_def sum_distrib_right[symmetric] sum_distrib_left[symmetric]
                  sum_divide_distrib[symmetric] IJ ennreal_mult[symmetric] 
                  mult_le_one ennreal_plus[symmetric]
             del: ennreal_plus)
  show ?thesis
    unfolding cond_prob_def Pr_hit_C *
    using *
    using p_f p_H p_j_pos p_H_p_f_less_1 by (simp add: divide_simps) (simp add: field_simps)
qed

lemma Pr_visit_eq_before_C:
  "\<P>(\<omega> in \<PP>. \<exists>j\<in>H. visit {j} J \<omega> \<and> before_C {j} \<omega> \<bar> hit_C \<omega> ) = 1 - (p_H - p_j) * p_f"
proof -
  let ?V = "\<lambda>j. visit {j} J aand before_C {j}" and ?H = "hit_C"
  let ?J = "H"
  have "\<P>(\<omega> in \<PP>. (\<exists>j\<in>?J. ?V j \<omega>) \<and> ?H \<omega>) = (\<Sum>j\<in>?J. \<P>(\<omega> in \<PP>. (?V j aand ?H) \<omega>))"
  proof (rule T.prob_sum)
    show "AE \<omega> in \<PP>. (\<forall>j\<in>?J. (?V j aand ?H) \<omega> \<longrightarrow> ((\<exists>j\<in>?J. ?V j \<omega>) \<and> ?H \<omega>)) \<and>
      (((\<exists>j\<in>?J. ?V j \<omega>) \<and> ?H \<omega>) \<longrightarrow> (\<exists>!j. j\<in>?J \<and> (?V j aand ?H) \<omega>))"
      by (auto intro!: AE_I2 dest: visit_unique1)
  qed auto
  then have "\<P>(\<omega> in \<PP>. (\<exists>j\<in>?J. ?V j \<omega>) \<bar> ?H \<omega>) = (\<Sum>j\<in>?J. \<P>(\<omega> in \<PP>. ?V j \<omega> \<bar> ?H \<omega>))"
    by (simp add: cond_prob_def sum_divide_distrib)
  also have "\<dots> = p_j * p_f + (1 - p_H * p_f)"
    by (simp add: Pr_visit_before_C sum_distrib_right[symmetric] sum.distrib)
  finally show ?thesis
    by (simp add: field_simps)
qed

lemma probably_innocent:
  assumes approx: "1 / (2 * (p_H - p_j)) \<le> p_f" and "p_H \<noteq> p_j"
  shows "\<P>(\<omega> in \<PP>. \<exists>j\<in>H. visit {j} J \<omega> \<and> before_C {j} \<omega> \<bar> hit_C \<omega> ) \<le> 1 / 2"
  unfolding Pr_visit_eq_before_C
proof -
  have [simp]: "\<And>n :: nat. 1 \<le> real n \<longleftrightarrow> 1 \<le> n" by auto
  have "0 \<le> p_j" unfolding p_j_def by auto
  then have "1 * p_j \<le> p_H"
    unfolding H_eq2[symmetric] using C_smaller
    by (intro mult_mono) (auto simp: Suc_le_eq card_Diff_subset not_le)
  with \<open>p_H \<noteq> p_j\<close> have "p_j < p_H" by auto
  with approx show "1 - (p_H - p_j) * p_f \<le> 1 / 2"
    by (auto simp add: field_simps divide_le_eq split: if_split_asm)
qed

lemma Pr_before_C:
  assumes L: "L \<subseteq> H"
  shows "\<P>(\<omega> in \<PP>. before_C L \<omega> \<bar> hit_C \<omega> ) =
    card L * p_j * p_f + (\<Sum>l\<in>L. p_i l) * (1 - p_H * p_f)"
proof -
  have "\<P>(\<omega> in \<PP>. before_C L \<omega> \<bar> hit_C \<omega> ) =
    \<P>(\<omega> in \<PP>. visit H J \<omega> \<and> before_C L \<omega> \<bar> hit_C \<omega> )"
    using AE_visit by (auto intro!: T.cond_prob_eq_AE)
  also have "\<dots> = card L * p_j * p_f + (\<Sum>i\<in>L. p_i i) * (1 - p_H * p_f)"
    using L by (subst Pr_visit_before_C[OF L order_refl]) (auto simp: Int_absorb1)
  finally show ?thesis .
qed

lemma P_visit:
  assumes I: "I \<subseteq> H"
  shows "\<P>(\<omega> in \<PP>. visit I J \<omega> \<bar> hit_C \<omega> ) = (\<Sum>i\<in>I. p_i i)"
proof -
  have "\<P>(\<omega> in \<PP>. visit I J \<omega> \<bar> hit_C \<omega> ) =
    \<P>(\<omega> in \<PP>. visit I J \<omega> \<and> before_C H \<omega> \<bar> hit_C \<omega> )"
  proof (rule T.cond_prob_eq_AE)
    show "AE x in \<PP>. hit_C x \<longrightarrow>
                visit I J x = (visit I J x \<and> before_C H x)"
      using AE_T_enabled by eventually_elim (auto intro: hit_C_imp_before_C)
  qed auto
  also have "\<dots> = sum p_i I"
    using I by (subst Pr_visit_before_C[OF order_refl]) (auto simp: Int_absorb2 field_simps p_H_def p_j_def)
  finally show ?thesis .
qed

subsection \<open>Probability space of hitting a collaborator\<close>

definition "hC = uniform_measure \<PP> {\<omega>\<in>space \<PP>. hit_C \<omega>}"

lemma emeasure_hit_C_not_0: "emeasure \<PP> {\<omega> \<in> space \<PP>. hit_C \<omega>} \<noteq> 0"
  using p_H p_H_p_f_less_1 unfolding Pr_hit_C T.emeasure_eq_measure by auto

lemma measurable_hC[measurable (raw)]:
  "A \<in> sets S \<Longrightarrow> A \<in> sets hC"
  "f \<in> measurable M S \<Longrightarrow> f \<in> measurable M hC"
  "g \<in> measurable S M \<Longrightarrow> g \<in> measurable hC M"
  "A \<inter> space S \<in> sets S \<Longrightarrow> A \<inter> space hC \<in> sets S"
  unfolding hC_def uniform_measure_def
  by simp_all

lemma vimage_Int_space_C[simp]:
  "f -` {x} \<inter> space hC = {\<omega>\<in>space S. f \<omega> = x}"
  by (auto simp: hC_def)

sublocale hC: information_space hC 2
proof -
  interpret hC: prob_space hC
    unfolding hC_def
    using emeasure_hit_C_not_0
    by (intro prob_space_uniform_measure) auto
  show "information_space hC 2"
    by standard simp
qed

abbreviation
  mutual_information_Pow_CP ("\<I>'(_ ; _')") where
  "\<I>(X ; Y) \<equiv> hC.mutual_information 2 (count_space (X`space hC)) (count_space (Y`space hC)) X Y"

lemma simple_functionI:
  assumes "finite (range f)"
  assumes [measurable]: "\<And>x. {\<omega>\<in>space S. f \<omega> = x} \<in> sets S"
  shows "simple_function hC f"
  using assms unfolding simple_function_def hC_def
  by (simp add: vimage_def space_stream_space)

subsection \<open>Estimate the information to the collaborators\<close>

lemma measure_hC[simp]:
  assumes A[measurable]: "A \<in> sets S"
  shows "measure hC A = \<P>(\<omega> in \<PP>. \<omega> \<in> A \<bar> hit_C \<omega> )"
  unfolding hC_def cond_prob_def
  using emeasure_hit_C_not_0 A
  by (subst measure_uniform_measure) (simp_all add: T.emeasure_eq_measure Int_def conj_ac)

subsubsection \<open>Setup random variables for mutual information\<close>

definition "first_J \<omega> = (THE i. visit {i} J \<omega>)"

lemma first_J_eq:
  "visit {i} J \<omega> \<Longrightarrow> first_J \<omega> = i"
  unfolding first_J_def by (intro the_equality) (auto dest: visit_unique1)

lemma AE_first_J:
  "AE \<omega> in \<PP>. visit {i} J \<omega> \<longleftrightarrow> first_J \<omega> = i"
  using AE_visit
proof eventually_elim
  fix \<omega> assume "visit H J \<omega>"
  then obtain j where "visit {j} J \<omega>" "j \<in> H"
    by (auto simp: visit_def HLD_iff)
  then show "visit {i} J \<omega> \<longleftrightarrow> first_J \<omega> = i"
    by (auto dest: visit_unique1 first_J_eq)
qed

lemma measurbale_first_J[measurable]: "first_J \<in> measurable S (count_space UNIV)"
  unfolding first_J_def[abs_def]
  by (intro measurable_THE[where I=H])
     (auto dest: visit_imp_in_H visit_unique1 intro: countable_finite)

definition "last_H \<omega> = (THE i. before_C {i} \<omega>)"

lemma measurbale_last_H[measurable]: "last_H \<in> measurable S (count_space UNIV)"
  unfolding last_H_def[abs_def]
  by (intro measurable_THE[where I=H])
     (auto dest: before_C_single before_C_unique intro: countable_finite)

lemma last_H_eq:
  "before_C {i} \<omega> \<Longrightarrow> last_H \<omega> = i"
  unfolding last_H_def by (intro the_equality) (auto dest: before_C_unique)

lemma last_H:
  assumes "enabled Start \<omega>" "hit_C \<omega>"
  shows "before_C {last_H \<omega>} \<omega>" "last_H \<omega> \<in> H"
  by (metis before_C_single hit_C_imp_before_C last_H_eq Int_iff assms)+

lemma AE_last_H:
  "AE \<omega> in \<PP>. hit_C \<omega> \<longrightarrow> before_C {i} \<omega> \<longleftrightarrow> last_H \<omega> = i"
  using AE_T_enabled
proof eventually_elim
  fix \<omega> assume "enabled Start \<omega>" then show "hit_C \<omega> \<longrightarrow> before_C {i} \<omega> = (last_H \<omega> = i)"
    by (auto dest: last_H last_H_eq)
qed

lemma information_flow:
  defines "h \<equiv> real (card H)"
  assumes init_uniform: "\<And>i. i \<in> H \<Longrightarrow> p_i i = 1 / h"
  shows "\<I>(first_J ; last_H) \<le> (1 - (h - 1) * p_j * p_f) * log 2 h"
proof -
  let ?il = "\<lambda>i l. \<P>(\<omega> in \<PP>. visit {i} J \<omega> \<and> before_C {l} \<omega> \<bar> hit_C \<omega> )"
  let ?i = "\<lambda>i. \<P>(\<omega> in \<PP>. visit {i} J \<omega> \<bar> hit_C \<omega> )"
  let ?l = "\<lambda>l. \<P>(\<omega> in \<PP>. before_C {l} \<omega> \<bar> hit_C \<omega> )"

  from init_uniform have init_H: "\<And>i. i \<in> H \<Longrightarrow> p_i i = p_j / p_H"
    by (simp add: p_j_def p_H_def h_def)

  from h_def have "1/h = p_j/p_H" "h = p_H / p_j" "p_H = h * p_j"
    by (auto simp: p_H_def p_j_def field_simps)
  from C_smaller have h_pos: "0 < h"
    by (auto simp add: card_gt_0_iff h_def)

  let ?s = "(h - 1) * p_j"
  let ?f = "?s * p_f"

  from psubset_card_mono[OF _ C_smaller]
  have "1 \<le> card J - card C"
    by (simp del: C_le_J)
  then have "1 \<le> h"
    using C_smaller
    by (simp add: h_def card_Diff_subset card_mono field_simps del: C_le_J)

  have log_le_0: "?f * log 2 (p_H * p_f) \<le> ?f * log 2 1"
    using p_H_p_f_less_1 p_H_p_f_pos p_j_pos p_f \<open>1 \<le> h\<close>
    by (intro mult_left_mono log_le mult_nonneg_nonneg) auto

  have "(h - 1) * p_j < 1"
    using \<open>1 \<le> h\<close> C_smaller
    by (auto simp: h_def p_j_def divide_less_eq card_Diff_subset card_mono)
  then have 1: "(h - 1) * p_j * p_f < 1 * 1"
    using p_f by (intro mult_strict_mono) auto

  { fix \<omega> have "first_J \<omega> \<in> H \<or> first_J \<omega> = (THE x. False)"
      apply (cases "\<forall>i. \<not> visit {i} J \<omega>")
      apply (simp add: first_J_def)
      apply (auto dest: visit_imp_in_H first_J_eq)
      done }
  then have range_fj: "range first_J \<subseteq> H \<union> {THE x. False}"
    by auto

  have sf_fj: "simple_function hC first_J"
    by (rule simple_functionI) (auto intro: finite_subset[OF range_fj])

  have sd_fj: "simple_distributed hC first_J ?i"
    apply (rule hC.simple_distributedI[OF sf_fj])
    apply (auto intro!: T.cond_prob_eq_AE)
    apply (auto simp: space_stream_space)
    using AE_first_J
    apply eventually_elim
    apply auto
    done

  { fix \<omega> have "last_H \<omega> \<in> H \<or> last_H \<omega> = (THE x. False)"
      apply (cases "\<forall>i. \<not> before_C {i} \<omega>")
      apply (simp add: last_H_def)
      apply (auto dest: before_C_imp_in_H last_H_eq)
      done }
  then have range_lnc: "range last_H \<subseteq> H \<union> {THE x. False}"
    by auto

  have sf_lnc: "simple_function hC last_H"
    by (rule simple_functionI) (auto intro: finite_subset[OF range_lnc])

  have sd_lnc: "simple_distributed hC last_H ?l"
    apply (rule hC.simple_distributedI[OF sf_lnc])
    apply (auto intro!: T.cond_prob_eq_AE)
    apply (auto simp: space_stream_space)
    using AE_last_H
    apply eventually_elim
    apply auto
    done

  have sd_fj_lnc: "simple_distributed hC (\<lambda>\<omega>. (first_J \<omega>, last_H \<omega>)) (\<lambda>(i, l). ?il i l)"
    apply (rule hC.simple_distributedI)
    apply (rule simple_function_Pair[OF sf_fj sf_lnc])
    apply (auto intro!: T.cond_prob_eq_AE)
    apply (auto simp: space_stream_space)
    using AE_last_H AE_first_J
    apply eventually_elim
    apply auto
    done

  define c where "c = (SOME j. j \<in> C)"
  have c: "c \<in> C"
    using C_non_empty unfolding ex_in_conv[symmetric] c_def by (rule someI_ex)

  let ?inner = "\<lambda>i. \<Sum>l\<in>H. ?il i l * log 2 (?il i l / (?i i * ?l l))"
  { fix i assume i: "i \<in> H"
    with h_pos have card_idx: "real_of_nat (card (H - {i})) = p_H / p_j - 1"
      by (auto simp add: p_j_def p_H_def h_def)

    have neq0: "p_j \<noteq> 0" "p_H \<noteq> 0"
      unfolding p_j_def p_H_def
      using C_smaller i by auto

    from i have "?inner i =
      (\<Sum>l\<in>H - {i}. ?il i l * log 2 (?il i l / (?i i * ?l l))) +
      ?il i i * log 2 (?il i i / (?i i * ?l i))"
      by (simp add: sum_diff)
    also have "\<dots> =
      (\<Sum>l\<in>H - {i}. p_j/p_H * p_j * p_f * log 2 (p_j * p_f / (p_j * p_f + p_j/p_H * (1 - p_H * p_f)))) +
      p_j/p_H * (p_j * p_f + (1 - p_H * p_f)) * log 2 ((p_j * p_f + (1 - p_H * p_f)) / (p_j * p_f + p_j/p_H * (1 - p_H * p_f)))"
      using i p_f p_j_pos p_H
      apply (simp add: Pr_visit_before_C P_visit init_H Pr_before_C
                  del: sum_constant)
      apply (simp add: divide_simps distrib_left)
      apply (intro arg_cong2[where f="(*)"] refl arg_cong2[where f=log])
      apply (auto simp: field_simps)
      done
    also have "\<dots> = (?f * log 2 (h * p_j * p_f) + (1 - ?f) * log 2 ((1 - ?f) * h)) / h"
      using neq0 p_f by (simp add: card_idx field_simps \<open>p_H = h * p_j\<close>)
    finally have "?inner i = (?f * log 2 (h * p_j * p_f) + (1 - ?f) * log 2 ((1 - ?f) * h)) / h" . }
  then have "(\<Sum>i\<in>H. ?inner i) = ?f * log 2 (h * p_j * p_f) + (1 - ?f) * log 2 ((1 - ?f) * h)"
    using h_pos by (simp add: h_def[symmetric])
  also have "\<dots> = ?f * log 2 (p_H * p_f) + (1 - ?f) * log 2 ((1 - ?f) * h)"
    by (simp add: \<open>h = p_H / p_j\<close>)
  also have "\<dots> \<le> (1 - ?f) * log 2 ((1 - ?f) * h)"
    using log_le_0 by simp
  also have "\<dots> \<le> (1 - ?f) * log 2 h"
    using h_pos \<open>1 \<le> h\<close> 1 p_j_pos p_f
    by (intro mult_left_mono log_le mult_pos_pos mult_nonneg_nonneg) auto
  finally have "(\<Sum>i\<in>H. ?inner i) \<le> (1 - ?f) * log 2 h" .
  also have "(\<Sum>i\<in>H. ?inner i) =
      (\<Sum>(i, l)\<in>(first_J`space S) \<times> (last_H`space S). ?il i l * log 2 (?il i l / (?i i * ?l l)))"
    unfolding sum.cartesian_product
  proof (safe intro!: sum.mono_neutral_cong_left del: DiffE DiffI)
    show "finite ((first_J ` space S) \<times> (last_H ` space S))"
      using sf_fj sf_lnc by (auto simp add: hC_def dest!: simple_functionD(1))
  next
    fix i assume "i \<in> H"
    then have "visit {i} J (Init i ## Mix i ## sconst End)"
      "before_C {i} (Init i ## Mix c ## sconst End)"
      by (auto simp: before_C_def visit_def suntil_Stream HLD_iff c)
    then show "i \<in> first_J ` space S" "i \<in> last_H ` space S"
      by (auto simp: space_stream_space image_iff eq_commute dest!: first_J_eq last_H_eq)
  next
    fix i l assume "(i, l) \<in> first_J ` space S \<times> last_H ` space S - H \<times> H"
    then have H: "i \<notin> H \<or> l \<notin> H"
      by auto
    have "\<P>(\<omega> in \<PP>. (visit {i} J \<omega> \<and> before_C {l} \<omega>) \<and> hit_C \<omega>) = 0"
      using H by (intro T.prob_eq_0_AE) (auto dest: visit_imp_in_H before_C_imp_in_H)
    then show "?il i l * log 2 (?il i l / (?i i * ?l l)) = 0"
      by (simp add: cond_prob_def)
  qed
  also have "\<dots> = \<I>(first_J ; last_H)"
    unfolding sum.cartesian_product
    apply (subst hC.mutual_information_simple_distributed[OF sd_fj sd_lnc sd_fj_lnc])
    apply (simp add: hC_def)
  proof (safe intro!: sum.mono_neutral_right imageI)
    show "finite ((first_J ` space S) \<times> (last_H ` space S))"
      using sf_fj sf_lnc by (auto simp add: hC_def dest!: simple_functionD(1))
  next
    fix i l assume "(first_J i, last_H l) \<notin> (\<lambda>x. (first_J x, last_H x)) ` space S"
    moreover
    { fix i l assume "i \<in> H" "l \<in> H"
      then have "visit {i} J (Init i ## Mix l ## Mix c ## sconst End)"
        "before_C {l} (Init i ## Mix l ## Mix c ## sconst End)"
        using c C_smaller by (auto simp: before_C_def visit_def HLD_iff suntil_Stream)
      then have "first_J (Init i ## Mix l ## Mix c ## sconst End) = i"
        "last_H (Init i ## Mix l ## Mix c ## sconst End) = l"
        by (auto intro!: first_J_eq last_H_eq) }
    note this[of "first_J i" "last_H l"]
    ultimately have "(first_J i, last_H l) \<notin> H\<times>H"
      by (auto simp: space_stream_space image_iff eq_commute) metis
    then have "\<P>(\<omega> in \<PP>. (visit {first_J i} J \<omega> \<and> before_C {last_H l} \<omega>) \<and> hit_C \<omega>) = 0"
      by (intro T.prob_eq_0_AE) (auto dest: visit_imp_in_H before_C_imp_in_H)
    then show "?il (first_J i) (last_H l) *
      log 2 (?il (first_J i) (last_H l) / (?i (first_J i) * ?l (last_H l))) = 0"
      by (simp add: cond_prob_def)
  qed
  finally show ?thesis by simp
qed

end

end
