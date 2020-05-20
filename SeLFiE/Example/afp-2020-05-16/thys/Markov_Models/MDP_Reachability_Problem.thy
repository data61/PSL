theory MDP_Reachability_Problem
  imports Markov_Decision_Process
begin

inductive_set directed_towards :: "'a set \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a set" for A r where
  start: "\<And>x. x \<in> A \<Longrightarrow> x \<in> directed_towards A r"
| step: "\<And>x y. y \<in> directed_towards A r \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> x \<in> directed_towards A r"

hide_fact (open) start step

lemma directed_towards_mono:
  assumes "s \<in> directed_towards A F" "F \<subseteq> G" shows "s \<in> directed_towards A G"
  using assms by induct (auto intro: directed_towards.intros)

lemma directed_eq_rtrancl: "x \<in> directed_towards A r \<longleftrightarrow> (\<exists>a\<in>A. (x, a) \<in> r\<^sup>*)"
proof
  assume "x \<in> directed_towards A r" then show "\<exists>a\<in>A. (x, a) \<in> r\<^sup>*"
    by induction (auto intro: converse_rtrancl_into_rtrancl)
next
  assume "\<exists>a\<in>A. (x, a) \<in> r\<^sup>*"
  then obtain a where "(x, a) \<in> r\<^sup>*" "a \<in> A" by auto
  then show "x \<in> directed_towards A r"
    by (induction rule: converse_rtrancl_induct)
       (auto intro: directed_towards.start directed_towards.step)
qed

lemma directed_eq_rtrancl_Image: "directed_towards A r = (r\<^sup>*)\<inverse> `` A"
  unfolding set_eq_iff directed_eq_rtrancl Image_iff by simp

locale Reachability_Problem = Finite_Markov_Decision_Process K S for K :: "'s \<Rightarrow> 's pmf set" and S +
  fixes S1 S2 :: "'s set"
  assumes S1: "S1 \<subseteq> S" and S2: "S2 \<subseteq> S" and S1_S2: "S1 \<inter> S2 = {}"
begin

lemma [measurable]:
  "S \<in> sets (count_space UNIV)" "S1 \<in> sets (count_space UNIV)" "S2 \<in> sets (count_space UNIV)"
  by auto

definition
  "v = (\<lambda>cfg\<in>valid_cfg. emeasure (T cfg) {x\<in>space St. (HLD S1 suntil HLD S2) (state cfg ## x)})"

lemma v_eq: "cfg \<in> valid_cfg \<Longrightarrow>
    v cfg = emeasure (T cfg) {x\<in>space St. (HLD S1 suntil HLD S2) (state cfg ## x)}"
  by (auto simp add: v_def)

lemma real_v: "cfg \<in> valid_cfg \<Longrightarrow> enn2real (v cfg) = \<P>(\<omega> in T cfg. (HLD S1 suntil HLD S2) (state cfg ## \<omega>))"
  by (auto simp add: v_def T.emeasure_eq_measure)

lemma v_le_1: "cfg \<in> valid_cfg \<Longrightarrow> v cfg \<le> 1"
  by (auto simp add: v_def T.emeasure_eq_measure)

lemma v_neq_Pinf[simp]: "cfg \<in> valid_cfg \<Longrightarrow> v cfg \<noteq> top"
  by (auto simp add: v_def)

lemma v_1_AE: "cfg \<in> valid_cfg \<Longrightarrow> v cfg = 1 \<longleftrightarrow> (AE \<omega> in T cfg. (HLD S1 suntil HLD S2) (state cfg ## \<omega>))"
  unfolding v_eq T.emeasure_eq_measure ennreal_eq_1 space_T[symmetric, of cfg]
  by (rule T.prob_Collect_eq_1) simp

lemma v_0_AE: "cfg \<in> valid_cfg \<Longrightarrow> v cfg = 0 \<longleftrightarrow> (AE x in T cfg. not (HLD S1 suntil HLD S2) (state cfg ## x))"
  unfolding v_eq T.emeasure_eq_measure space_T[symmetric, of cfg] ennreal_eq_zero_iff[OF measure_nonneg]
  by (rule T.prob_Collect_eq_0) simp

lemma v_S2[simp]: "cfg \<in> valid_cfg \<Longrightarrow> state cfg \<in> S2 \<Longrightarrow> v cfg = 1"
  using S2 by (subst v_1_AE) (auto simp: suntil_Stream)

lemma v_nS12[simp]: "cfg \<in> valid_cfg \<Longrightarrow> state cfg \<notin> S1 \<Longrightarrow> state cfg \<notin> S2 \<Longrightarrow> v cfg = 0"
  by (subst v_0_AE) (auto simp: suntil_Stream)

lemma v_nS[simp]: "cfg \<notin> valid_cfg \<Longrightarrow> v cfg = undefined"
  by (auto simp add: v_def)

lemma v_S1:
  assumes cfg[simp, intro]: "cfg \<in> valid_cfg" and cfg_S1[simp]: "state cfg \<in> S1"
  shows "v cfg = (\<integral>\<^sup>+s. v (cont cfg s) \<partial>action cfg)"
proof -
  have [simp]: "state cfg \<notin> S2"
    using cfg_S1 S1_S2 S1 by blast
  show ?thesis
    by (auto simp: v_eq emeasure_Collect_T[of _ cfg] K_cfg_def map_pmf_rep_eq nn_integral_distr
                   AE_measure_pmf_iff suntil_Stream[of _ _ "state cfg"]
                   valid_cfg_cont
             intro!: nn_integral_cong_AE)
qed

lemma real_v_integrable:
  "integrable (action cfg) (\<lambda>s. enn2real (v (cont cfg s)))"
  by (rule measure_pmf.integrable_const_bound[where B="max 1 (enn2real undefined)"])
     (auto simp add: v_def measure_def[symmetric] le_max_iff_disj)

lemma real_v_integral_eq:
  assumes cfg[simp]: "cfg \<in> valid_cfg"
  shows "enn2real (\<integral>\<^sup>+ s. v (cont cfg s) \<partial>action cfg) = \<integral> s. enn2real (v (cont cfg s)) \<partial>action cfg"
 by (subst integral_eq_nn_integral)
    (auto simp: AE_measure_pmf_iff v_eq T.emeasure_eq_measure valid_cfg_cont
          intro!: arg_cong[where f=enn2real] nn_integral_cong_AE)

lemma v_eq_0_coinduct[consumes 3, case_names valid nS2 cont]:
  assumes *: "P cfg"
  assumes valid: "\<And>cfg. P cfg \<Longrightarrow> cfg \<in> valid_cfg"
  assumes nS2: "\<And>cfg. P cfg \<Longrightarrow> state cfg \<notin> S2"
  assumes cont: "\<And>cfg cfg'. P cfg \<Longrightarrow> state cfg \<in> S1 \<Longrightarrow> cfg' \<in> K_cfg cfg \<Longrightarrow> P cfg' \<or> v cfg' = 0"
  shows "v cfg = 0"
proof -
  from * valid[OF *]
  have "AE x in MC_syntax.T K_cfg cfg. \<not> (HLD S1 suntil HLD S2) (state cfg ## smap state x)"
    unfolding stream.map[symmetric] suntil_smap hld_smap'
  proof (coinduction arbitrary: cfg rule: MC.AE_not_suntil_coinduct_strong)
    case (\<psi> cfg) then show ?case
      by (auto simp del: cfg_onD_state dest: nS2)
  next
    case (\<phi> cfg' cfg)
    then have *: "P cfg" "state cfg \<in> S1" "cfg' \<in> K_cfg cfg" and [simp, intro]: "cfg \<in> valid_cfg"
      by auto
    with cont[OF *] show ?case
      by (subst (asm) v_0_AE)
         (auto simp: suntil_Stream T_def AE_distr_iff suntil_smap hld_smap' cong del: AE_cong)
  qed
  then have "AE \<omega> in T cfg. \<not> (HLD S1 suntil HLD S2) (state cfg ## \<omega>)"
    unfolding T_def by (subst AE_distr_iff) simp_all
  with valid[OF *] show ?thesis
    by (simp add: v_0_AE)
qed


definition "p = (\<lambda>s\<in>S. P_sup s (\<lambda>\<omega>. (HLD S1 suntil HLD S2) (s ## \<omega>)))"

lemma p_eq_SUP_v: "s \<in> S \<Longrightarrow> p s = \<Squnion> (v ` cfg_on s)"
  by (auto simp add: p_def v_def P_sup_def T.emeasure_eq_measure intro: valid_cfgI intro!: SUP_cong cong: SUP_cong_simp)

lemma v_le_p: "cfg \<in> valid_cfg \<Longrightarrow> v cfg \<le> p (state cfg)"
  by (subst p_eq_SUP_v) (auto intro!: SUP_upper dest: valid_cfgD valid_cfg_state_in_S)

lemma p_eq_0_imp: "cfg \<in> valid_cfg \<Longrightarrow> p (state cfg) = 0 \<Longrightarrow> v cfg = 0"
  using v_le_p[of cfg] by (auto intro: antisym)

lemma p_eq_0_iff: "s \<in> S \<Longrightarrow> p s = 0 \<longleftrightarrow> (\<forall>cfg\<in>cfg_on s. v cfg = 0)"
  unfolding p_eq_SUP_v by (subst SUP_eq_iff) auto

lemma p_le_1: "s \<in> S \<Longrightarrow> p s \<le> 1"
  by (auto simp: p_eq_SUP_v intro!: SUP_least v_le_1 intro: valid_cfgI)

lemma p_undefined[simp]: "s \<notin> S \<Longrightarrow> p s = undefined"
  by (simp add: p_def)

lemma p_not_inf[simp]: "s \<in> S \<Longrightarrow> p s \<noteq> top"
  using p_le_1[of s] by (auto simp: top_unique)

lemma p_S1: "s \<in> S1 \<Longrightarrow> p s = (\<Squnion>D\<in>K s. \<integral>\<^sup>+ t. p t \<partial>measure_pmf D)"
  using S1 S1_S2 K_closed[of s] unfolding p_def
  by (simp add: P_sup_iterate[of _ s] subset_eq set_eq_iff suntil_Stream[of _ _ s])
     (auto intro!: SUP_cong nn_integral_cong_AE simp add: AE_measure_pmf_iff)

lemma p_S2[simp]: "s \<in> S2 \<Longrightarrow> p s = 1"
  using S2 by (auto simp: v_S2[OF valid_cfgI] p_eq_SUP_v)

lemma p_nS12: "s \<in> S \<Longrightarrow> s \<notin> S1 \<Longrightarrow> s \<notin> S2 \<Longrightarrow> p s = 0"
  by (auto simp: p_eq_SUP_v v_nS12[OF valid_cfgI])

lemma p_pos:
  assumes "(s, t) \<in> (SIGMA s:S1. \<Union>D\<in>K s. set_pmf D)\<^sup>*" "t \<in> S2" shows "0 < p s"
using assms proof (induction rule: converse_rtrancl_induct)
  case (step s t')
  then obtain D where "s \<in> S1" "D \<in> K s" "t' \<in> D" "0 < p t'"
    by auto
  with S1 set_pmf_closed[of s D] have in_S: "\<And>t. t \<in> D \<Longrightarrow> t \<in> S"
    by auto
  from \<open>t' \<in> D\<close> \<open>0 < p t'\<close> have "0 < pmf D t' * p t'"
    by (auto simp add: ennreal_zero_less_mult_iff pmf_positive)
  also have "\<dots> \<le> (\<integral>\<^sup>+t. p t' * indicator {t'} t\<partial>D)"
    using in_S[OF \<open>t' \<in> D\<close>]
    by (subst nn_integral_cmult_indicator) (auto simp: ac_simps emeasure_pmf_single)
  also have "\<dots> \<le> (\<integral>\<^sup>+t. p t \<partial>D)"
    by (auto intro!: nn_integral_mono_AE split: split_indicator simp: in_S AE_measure_pmf_iff
      simp del: nn_integral_indicator_singleton)
  also have "\<dots> \<le> p s"
    using \<open>s \<in> S1\<close> \<open>D \<in> K s\<close> by (auto intro: SUP_upper simp add: p_S1)
  finally show ?case .
qed simp

definition F_sup :: "('s \<Rightarrow> ennreal) \<Rightarrow> 's \<Rightarrow> ennreal" where
  "F_sup f = (\<lambda>s\<in>S. if s \<in> S2 then 1 else if s \<in> S1 then SUP D\<in>K s. \<integral>\<^sup>+t. f t \<partial>measure_pmf D else 0)"

lemma F_sup_cong: "(\<And>s. s \<in> S \<Longrightarrow> f s = g s) \<Longrightarrow> F_sup f s = F_sup g s"
  using K_closed[of s]
  by (auto simp: F_sup_def AE_measure_pmf_iff subset_eq
              intro!: SUP_cong nn_integral_cong_AE)

lemma continuous_F_sup: "sup_continuous F_sup"
  unfolding sup_continuous_def fun_eq_iff F_sup_def[abs_def]
  by (auto simp:  SUP_apply[abs_def] nn_integral_monotone_convergence_SUP intro: SUP_commute)

lemma mono_F_sup: "mono F_sup"
  by (intro sup_continuous_mono continuous_F_sup)

lemma lfp_F_sup_iterate: "lfp F_sup = (SUP i. (F_sup ^^ i) (\<lambda>x\<in>S. 0))"
proof -
  { have "(SUP i. (F_sup ^^ i) \<bottom>) = (SUP i. (F_sup ^^ i) (\<lambda>x\<in>S. 0))"
    proof (rule SUP_eq)
      fix i show "\<exists>j\<in>UNIV. (F_sup ^^ i) \<bottom> \<le> (F_sup ^^ j) (\<lambda>x\<in>S. 0)"
        by (intro bexI[of _ i] funpow_mono mono_F_sup) auto
      have *: "(\<lambda>x\<in>S. 0) \<le> F_sup \<bottom>"
        using K_wf by (auto simp: F_sup_def le_fun_def)
      show "\<exists>j\<in>UNIV. (F_sup ^^ i) (\<lambda>x\<in>S. 0) \<le> (F_sup ^^ j) \<bottom>"
        by (auto intro!: exI[of _ "Suc i"] funpow_mono mono_F_sup  *
                 simp del: funpow.simps simp add: funpow_Suc_right le_funI)
    qed }
  then show ?thesis
    by (auto simp: sup_continuous_lfp continuous_F_sup)
qed

lemma p_eq_lfp_F_sup: "p = lfp F_sup"
proof -
  { fix s assume "s \<in> S" let ?F = "\<lambda>P. HLD S2 or (HLD S1 aand nxt P)"
    have "P_sup s (\<lambda>\<omega>. (HLD S1 suntil HLD S2) (s ## \<omega>)) = (\<Squnion>i. P_sup s (\<lambda>\<omega>. (?F ^^ i) \<bottom> (s ## \<omega>)))"
    proof (simp add: suntil_def, rule P_sup_lfp)
      show "(##) s \<in> measurable St St"
        by simp
      (* This proof should work automatically *)
      fix P assume P: "Measurable.pred St P"
      show "Measurable.pred St (HLD S2 or (HLD S1 aand (\<lambda>\<omega>. P (stl \<omega>))))"
        by (intro pred_intros_logic measurable_compose[OF _ P] measurable_compose[OF measurable_shd]) auto
    qed (auto simp: sup_continuous_def)
    also have "\<dots> = (SUP i. (F_sup ^^ i) (\<lambda>x\<in>S. 0) s)"
    proof (rule SUP_cong)
      fix i from \<open>s \<in> S\<close> show "P_sup s (\<lambda>\<omega>. (?F ^^ i) \<bottom> (s##\<omega>)) = (F_sup ^^ i) (\<lambda>x\<in>S. 0) s"
      proof (induct i arbitrary: s)
        case (Suc n) show ?case
        proof (subst P_sup_iterate)
          (* This proof should work automatically *)
          show "Measurable.pred St (\<lambda>\<omega>. (?F ^^ Suc n) \<bottom> (s ## \<omega>))"
            apply (intro measurable_compose[OF measurable_Stream[OF measurable_const measurable_ident_sets[OF refl]] measurable_predpow])
            apply simp
            apply (simp add: bot_fun_def[abs_def])
            apply (intro pred_intros_logic measurable_compose[OF measurable_stl]  measurable_compose[OF measurable_shd])
            apply auto
            done
        next
          show "(\<Squnion>D\<in>K s. \<integral>\<^sup>+ t. P_sup t (\<lambda>\<omega>. (?F ^^ Suc n) \<bottom> (s ## t ## \<omega>)) \<partial>measure_pmf D) =
            (F_sup ^^ Suc n) (\<lambda>x\<in>S. 0) s"
            unfolding funpow.simps comp_def
            using S1 S2 \<open>s \<in> S\<close>
            by (subst F_sup_cong[OF Suc(1)[symmetric]])
               (auto simp add: F_sup_def measure_pmf.emeasure_space_1[simplified] K_wf subset_eq)
        qed
      qed simp
    qed simp
    finally have "lfp F_sup s = P_sup s (\<lambda>\<omega>. (HLD S1 suntil HLD S2) (s ## \<omega>))"
      by (simp add: lfp_F_sup_iterate image_comp) }
  moreover have "\<And>s. s \<notin> S \<Longrightarrow> lfp F_sup s = undefined"
    by (subst lfp_unfold[OF mono_F_sup]) (auto simp add: F_sup_def)
  ultimately show ?thesis
    by (auto simp: p_def)
qed

definition "S\<^sub>e = {s\<in>S. p s = 0}"

lemma S\<^sub>e: "S\<^sub>e \<subseteq> S"
  by (auto simp add: S\<^sub>e_def)

lemma v_S\<^sub>e: "cfg \<in> valid_cfg \<Longrightarrow> state cfg \<in> S\<^sub>e \<Longrightarrow> v cfg = 0"
  using p_eq_0_imp[of cfg] by (auto simp: S\<^sub>e_def)

lemma S\<^sub>e_nS2: "S\<^sub>e \<inter> S2 = {}"
  by (auto simp: S\<^sub>e_def)

lemma S\<^sub>e_E1: "s \<in> S\<^sub>e \<inter> S1 \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> t \<in> S\<^sub>e"
  unfolding S\<^sub>e_def using S1
  by (auto simp: p_S1 SUP_eq_iff K_wf nn_integral_0_iff_AE AE_measure_pmf_iff E_def
           intro: set_pmf_closed antisym
           cong: rev_conj_cong)

lemma S\<^sub>e_E2: "s \<in> S1 \<Longrightarrow> (\<And>t. (s, t) \<in> E \<Longrightarrow> t \<in> S\<^sub>e) \<Longrightarrow> s \<in> S\<^sub>e"
  unfolding S\<^sub>e_def using S1 S1_S2
  by (force simp: p_S1 SUP_eq_iff K_wf nn_integral_0_iff_AE AE_measure_pmf_iff E_def
            cong: rev_conj_cong)

lemma S\<^sub>e_E_iff: "s \<in> S1 \<Longrightarrow> s \<in> S\<^sub>e \<longleftrightarrow> (\<forall>t. (s, t) \<in> E \<longrightarrow> t \<in> S\<^sub>e)"
  using S\<^sub>e_E1[of s] S\<^sub>e_E2[of s] by blast

definition "S\<^sub>r = S - (S\<^sub>e \<union> S2)"

lemma S\<^sub>r: "S\<^sub>r \<subseteq> S"
  by (auto simp: S\<^sub>r_def)

lemma S\<^sub>r_S1: "S\<^sub>r \<subseteq> S1"
  by (auto simp: p_nS12 S\<^sub>r_def S\<^sub>e_def)

lemma S\<^sub>r_eq: "S\<^sub>r = S1 - S\<^sub>e"
  using S1_S2 S1 S2 by (auto simp add: S\<^sub>r_def S\<^sub>e_def p_nS12)

lemma v_neq_0_imp: "cfg \<in> valid_cfg \<Longrightarrow> v cfg \<noteq> 0 \<Longrightarrow> state cfg \<in> S\<^sub>r \<union> S2"
  using p_eq_0_imp[of cfg] by (auto simp add: S\<^sub>r_def S\<^sub>e_def valid_cfg_state_in_S)

lemma valid_cfg_action_in_K: "cfg \<in> valid_cfg \<Longrightarrow> action cfg \<in> K (state cfg)"
  by (auto dest!: valid_cfgD)

lemma K_cfg_E: "cfg \<in> valid_cfg \<Longrightarrow> cfg' \<in> K_cfg cfg \<Longrightarrow> (state cfg, state cfg') \<in> E"
  by (auto simp: E_def K_cfg_def valid_cfg_action_in_K)

lemma S\<^sub>r_directed_towards_S2:
  assumes s: "s \<in> S\<^sub>r"
  shows "s \<in> directed_towards S2 {(s, t) | s t. s \<in> S\<^sub>r \<and> (s, t) \<in> E}" (is "s \<in> ?D")
proof -
  { fix cfg assume "s \<notin> ?D" "cfg \<in> cfg_on s"
    with s S\<^sub>r have "state cfg \<in> S\<^sub>r" "state cfg \<notin> ?D" "cfg \<in> valid_cfg"
      by (auto intro: valid_cfgI)
    then have "v cfg = 0"
    proof (coinduction arbitrary: cfg rule: v_eq_0_coinduct)
      case (cont cfg' cfg)
      with v_neq_0_imp[of cfg'] show ?case
        by (auto intro: directed_towards.intros K_cfg_E)
    qed (auto intro: directed_towards.intros) }
  with p_eq_0_iff[of s] s show ?thesis
    unfolding S\<^sub>r_def S\<^sub>e_def by blast
qed

definition "proper ct \<longleftrightarrow> ct \<in> Pi\<^sub>E S K \<and> (\<forall>s\<in>S\<^sub>r. v (simple ct s) > 0)"

lemma S\<^sub>r_nS2: "s \<in> S\<^sub>r \<Longrightarrow> s \<notin> S2"
  by (auto simp: S\<^sub>r_def)

lemma properD1: "proper ct \<Longrightarrow> ct \<in> Pi\<^sub>E S K"
  by (auto simp: proper_def)

lemma proper_eq:
  assumes ct[simp, intro]: "ct \<in> Pi\<^sub>E S K"
  shows "proper ct \<longleftrightarrow> S\<^sub>r \<subseteq> directed_towards S2 (SIGMA s:S\<^sub>r. ct s)"
    (is "_ \<longleftrightarrow> _ \<subseteq> ?D")
proof -
  have *[simp]: "\<And>s. s \<in> S\<^sub>r \<Longrightarrow> s \<in> S" and ct': "ct \<in> Pi S K"
    using ct by (auto simp: S\<^sub>r_def simp del: ct)
  { fix s t have "s \<in> S \<Longrightarrow> t \<in> ct s \<Longrightarrow> t \<in> S"
      using K_closed[of s] ct' by (auto simp add: subset_eq) }
  note ct_closed = this

  let ?C = "simple ct"
  from ct have valid_C[simp]: "\<And>s. s \<in> S \<Longrightarrow> ?C s \<in> valid_cfg"
    by (auto simp add: PiE_def)
  { fix s assume "s \<in> ?D"
    then have "0 < v (?C s)"
    proof induct
      case (step s t)
      then have s: "s \<in> S\<^sub>r" and t: "t \<in> ct s" and [simp]: "s \<in> S"
        by auto
      with S\<^sub>r_S1 ct have "v (?C s) = (\<integral>\<^sup>+t. v (?C t) \<partial>ct s)"
        by (subst v_S1) (auto intro!: nn_integral_cong_AE AE_pmfI)
      also have "\<dots> \<noteq> 0"
        using ct t step
        by (subst nn_integral_0_iff_AE) (auto simp add: AE_measure_pmf_iff zero_less_iff_neq_zero)
      finally show ?case
        using ct by (auto simp add: less_le)
    qed (subst v_S2, insert S2, auto) }
  moreover
  { fix s assume s: "s \<notin> ?D" "s \<in> S\<^sub>r"
    with ct' have C: "?C s \<in> cfg_on s" and [simp]: "s \<in> S"
      by auto
    from s have "v (?C s) = 0"
    proof (coinduction arbitrary: s rule: v_eq_0_coinduct)
      case (cont cfg s)
      with S1 obtain t where "cfg = ?C t" "t \<in> ct s" "s \<in> S"
        by (auto simp: set_K_cfg subset_eq)
      with cont(1,2) v_neq_0_imp[of "?C t"] ct_closed[of s t] show ?case
        by (intro exI[of _ t] disjCI) (auto intro: directed_towards.intros)
    qed (auto simp: S\<^sub>r_nS2) }
  ultimately show ?thesis
    unfolding proper_def using ct by (force simp del: v_nS v_S2 v_nS12 ct)
qed

lemma exists_proper:
  obtains ct where "proper ct"
proof atomize_elim
  define r where "r = rec_nat S2 (\<lambda>_ S'. {s\<in>S\<^sub>r. \<exists>t\<in>S'. (s, t) \<in> E})"
  then have [simp]: "r 0 = S2" "\<And>n. r (Suc n) = {s\<in>S\<^sub>r. \<exists>t\<in>r n. (s, t) \<in> E}"
    by simp_all

  { fix s assume "s \<in> S\<^sub>r"
    then have "s \<in> directed_towards S2 {(s, t) | s t. s \<in> S\<^sub>r \<and> (s, t) \<in> E}"
      by (rule S\<^sub>r_directed_towards_S2)
    from this \<open>s\<in>S\<^sub>r\<close> have "\<exists>n. s \<in> r n"
    proof induction
      case (step s t)
      show ?case
      proof cases
        assume "t \<in> S2" with step.prems step.hyps show ?thesis
          by (intro exI[of _ "Suc 0"]) force
      next
        assume "t \<notin> S2"
        with step obtain n where "t \<in> r n" "t \<in> S\<^sub>r"
          by (auto elim: directed_towards.cases)
        with \<open>t\<in>S\<^sub>r\<close> step.hyps show ?thesis
          by (intro exI[of _ "Suc n"]) force
      qed
    qed (simp add: S\<^sub>r_def) }
  note r = this

  { fix s assume "s \<in> S"
    have "\<exists>D\<in>K s. s \<in> S\<^sub>r \<longrightarrow> (\<exists>t\<in>D. \<exists>n. t \<in> r n \<and> (\<forall>m. s \<in> r m \<longrightarrow> n < m))"
    proof cases
      assume s: "s \<in> S\<^sub>r"
      define n where "n = (LEAST n. s \<in> r n)"
      then have "s \<in> r n" and n: "\<And>i. i < n \<Longrightarrow> s \<notin> r i"
        using r s by (auto intro: LeastI_ex dest: not_less_Least)
      with s have "n \<noteq> 0"
        by (intro notI) (auto simp: S\<^sub>r_def)
      then obtain n' where "n = Suc n'"
        by (cases n) auto
      with \<open>s \<in> r n\<close> obtain t D where "D \<in> K s" "t \<in> D" "t \<in> r n'"
        by (auto simp: E_def)
      with n \<open>n = Suc n'\<close> s show ?thesis
        by (auto intro!: bexI[of _ D] bexI[of _ t] exI[of _ n'] simp: not_less_eq[symmetric])
    qed (insert K_wf \<open>s\<in>S\<close>, auto) }
  then obtain ct where ct: "\<And>s. s \<in> S \<Longrightarrow> ct s \<in> K s"
    "\<And>s. s \<in> S \<Longrightarrow> s \<in> S\<^sub>r \<Longrightarrow> \<exists>t\<in>ct s. \<exists>n. t \<in> r n \<and> (\<forall>m. s \<in> r m \<longrightarrow> n < m)"
    by metis
  then have *: "restrict ct S \<in> Pi\<^sub>E S K"
    by auto

  moreover
  { fix s assume "s \<in> S\<^sub>r"
    then obtain n where "s \<in> r n"
      by (metis r)
    with \<open>s \<in> S\<^sub>r\<close> have "s \<in> directed_towards S2 (SIGMA s : S\<^sub>r. ct s)"
    proof (induction n arbitrary: s rule: less_induct)
      case (less n s)
      moreover with S\<^sub>r have "s \<in> S" by auto
      ultimately obtain t m where "t \<in> ct s" "t \<in> r m" "m < n"
        using ct[of s] by (auto simp: E_def)
      with less.IH[of m t] \<open>s \<in> S\<^sub>r\<close> show ?case
        by (cases m) (auto intro: directed_towards.intros)
    qed }

  ultimately show "\<exists>ct. proper ct"
    using S\<^sub>r S2
    by (auto simp: proper_eq[OF *] subset_eq
             intro!: exI[of _ "restrict ct S"]
             cong: Sigma_cong)
qed

definition "l_desc X ct l s \<longleftrightarrow>
    s \<in> directed_towards S2 (SIGMA s : X. {l s}) \<and>
    v (simple ct s) \<le> v (simple ct (l s)) \<and>
    l s \<in> maximal (\<lambda>s. v (simple ct s)) (ct s)"

lemma exists_l_desc:
  assumes ct: "proper ct"
  shows "\<exists>l\<in>S\<^sub>r \<rightarrow> S\<^sub>r \<union> S2. \<forall>s\<in>S\<^sub>r. l_desc S\<^sub>r ct l s"
proof -
  have ct_closed: "\<And>s t. s \<in> S \<Longrightarrow> t \<in> ct s \<Longrightarrow> t \<in> S"
    using ct K_closed by (auto simp: proper_def PiE_iff)
  have ct_Pi: "ct \<in> Pi S K"
    using ct by (auto simp: proper_def)

  have "finite S\<^sub>r"
    using S_finite by (auto simp: S\<^sub>r_def)
  then show ?thesis
  proof (induct rule: finite_induct_select)
    case (select X)
    then obtain l where l: "l \<in> X \<rightarrow> X \<union> S2" and desc: "\<And>s. s \<in> X \<Longrightarrow> l_desc X ct l s"
      by auto
    obtain x where x: "x \<in> S\<^sub>r - X"
      using \<open>X \<subset> S\<^sub>r\<close> by auto
    then have "x \<in> S"
      by (auto simp: S\<^sub>r_def)

    let ?C = "simple ct"
    let ?v = "\<lambda>s. v (?C s)" and ?E = "\<lambda>s. set_pmf (ct s)"
    let ?M = "\<lambda>s. maximal ?v (?E s)"

    have finite_E[simp]: "\<And>s. s \<in> S \<Longrightarrow> finite (?E s)"
      using K_closed ct by (intro finite_subset[OF _ S_finite]) (auto simp: proper_def subset_eq)

    have valid_C[simp]: "\<And>s. s \<in> S \<Longrightarrow> ?C s \<in> valid_cfg"
      using ct by (auto simp: proper_def intro!: simple_valid_cfg)

    have E_ne[simp]: "\<And>s. ?E s \<noteq> {}"
        by (rule set_pmf_not_empty)

    have "\<exists>s\<in>S\<^sub>r - X. \<exists>t\<in>?M s. t \<in> S2 \<union> X"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have not_M: "\<And>s. s \<in> S\<^sub>r - X \<Longrightarrow> ?M s \<inter> (S2 \<union> X) = {}"
        by auto

      let ?S\<^sub>m = "maximal ?v (S\<^sub>r - X)"

      have "finite (S\<^sub>r - X)" "S\<^sub>r - X \<noteq> {}"
        using \<open>X \<subset> S\<^sub>r\<close> by (auto intro!: finite_subset[OF _ S_finite] simp: S\<^sub>r_def)
      from maximal_ne[OF this] obtain s\<^sub>m where s\<^sub>m: "s\<^sub>m \<in> ?S\<^sub>m"
        by force

      have "\<exists>s\<^sub>0\<in>?S\<^sub>m. \<exists>t\<in>?E s\<^sub>0. t \<notin> ?S\<^sub>m"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then have S\<^sub>m: "\<And>s\<^sub>0 t. s\<^sub>0 \<in> ?S\<^sub>m \<Longrightarrow> t \<in> ?E s\<^sub>0 \<Longrightarrow> t \<in> ?S\<^sub>m" by blast
        from \<open>s\<^sub>m \<in> ?S\<^sub>m\<close> have [simp]: "s\<^sub>m \<in> S" and "s\<^sub>m \<in> S\<^sub>r"
          by (auto simp: S\<^sub>r_def dest: maximalD1)

        from \<open>s\<^sub>m \<in> ?S\<^sub>m\<close> have "v (?C s\<^sub>m) = 0"
        proof (coinduction arbitrary: s\<^sub>m rule: v_eq_0_coinduct)
          case (cont t s\<^sub>m) with S1 show ?case
            by (intro exI[of _ "state t"] disjCI conjI S\<^sub>m[of s\<^sub>m "state t"])
               (auto simp: set_K_cfg)
        qed (auto simp: S\<^sub>r_def ct_Pi dest!: maximalD1)
        with \<open>s\<^sub>m \<in> S\<^sub>r\<close> \<open>proper ct\<close> show False
          by (auto simp: proper_def)
      qed
      then obtain s\<^sub>0 t where "s\<^sub>0 \<in> ?S\<^sub>m" and t: "t \<in> ?E s\<^sub>0" "t \<notin> ?S\<^sub>m"
        by metis
      with S\<^sub>r_S1 have s\<^sub>0: "s\<^sub>0 \<in> S\<^sub>r - X" and [simp]: "s\<^sub>0 \<in> S" and "s\<^sub>0 \<in> S1"
        by (auto simp: S\<^sub>r_def dest: maximalD1)

      from \<open>proper ct\<close> \<open>s\<^sub>0 \<in> S\<close> s\<^sub>0 have "?v s\<^sub>0 \<noteq> 0"
        by (auto simp add: proper_def)
      then have "0 < ?v s\<^sub>0" by (simp add: zero_less_iff_neq_zero)

      { fix t assume "t \<in> S\<^sub>e \<union> S2 \<union> X" "t \<in> ?E s\<^sub>0" and "?v s\<^sub>0 \<le> ?v t"
        moreover have "t \<in> S\<^sub>e \<Longrightarrow> ?v t = 0"
          by (simp add: p_eq_0_imp S\<^sub>e_def ct_Pi)
        ultimately have t: "t \<in> S2 \<union> X" "t \<in> ?E s\<^sub>0"
          using \<open>0 < ?v s\<^sub>0\<close> by (auto simp: S\<^sub>e_def)

        have "maximal ?v (?E s\<^sub>0 \<inter> (S2 \<union> X)) \<noteq> {}"
          using finite_E t by (intro maximal_ne) auto
        moreover
        { fix x y assume x: "x \<in> S2 \<union> X" "x \<in> ?E s\<^sub>0"
            and *: "\<forall>y\<in>?E s\<^sub>0 \<inter> (S2 \<union> X). ?v y \<le> ?v x" and y: "y \<in> ?E s\<^sub>0"
          with S2 \<open>s\<^sub>0 \<in> S\<close>[THEN ct_closed] have [simp]: "x \<in> S" "y \<in> S"
            by auto

          have "?v y \<le> ?v x"
          proof cases
            assume "y \<in> S\<^sub>r - X"
            then have "?v y \<le> ?v s\<^sub>0"
              using \<open>s\<^sub>0 \<in> ?S\<^sub>m\<close> by (auto intro: maximalD2)
            also note \<open>?v s\<^sub>0 \<le> ?v t\<close>
            also have "?v t \<le> ?v x"
              using * t by auto
            finally show ?thesis .
          next
            assume "y \<notin> S\<^sub>r - X" with y * show ?thesis
              by (auto simp: S\<^sub>r_def v_S\<^sub>e[of "?C y"] ct_Pi)
          qed }
        then have "maximal ?v (?E s\<^sub>0 \<inter> (S2 \<union> X)) \<subseteq> maximal ?v (?E s\<^sub>0)"
          by (auto simp: maximal_def)
        moreover note not_M[OF s\<^sub>0]
        ultimately have False
          by (blast dest: maximalD1) }
      then have less_s\<^sub>0: "\<And>t. t \<in> S\<^sub>e \<union> S2 \<union> X \<Longrightarrow> t \<in> ?E s\<^sub>0 \<Longrightarrow> ?v t < ?v s\<^sub>0"
        by (auto simp add: not_le[symmetric])

      let ?K = "ct s\<^sub>0"

      have "?v s\<^sub>0 = (\<integral>\<^sup>+ x. ?v x \<partial>?K)"
        using v_S1[of "?C s\<^sub>0"] \<open>s\<^sub>0 \<in> S1\<close> \<open>s\<^sub>0 \<in> S\<close>
        by (auto simp add: ct_Pi intro!: nn_integral_cong_AE AE_pmfI)
      also have "\<dots> < (\<integral>\<^sup>+x. ?v s\<^sub>0 \<partial>?K)"
      proof (intro nn_integral_less)
        have "(\<integral>\<^sup>+x. ?v x \<partial>?K) \<le> (\<integral>\<^sup>+x. 1 \<partial>?K)"
          using ct ct_closed[of s\<^sub>0]
          by (intro nn_integral_mono_AE)
             (auto intro!: v_le_1 simp: AE_measure_pmf_iff proper_def ct_Pi)
        then show "(\<integral>\<^sup>+x. ?v x \<partial>?K) \<noteq> \<infinity>"
          by (auto simp: top_unique)
        have "?v t < ?v s\<^sub>0"
        proof cases
          assume "t \<in> S\<^sub>e \<union> S2 \<union> X" then show ?thesis
            using less_s\<^sub>0[of t] t by simp
        next
          assume "t \<notin> S\<^sub>e \<union> S2 \<union> X"
          with t(1) ct_closed[of s\<^sub>0 t] have "t \<in> S\<^sub>r - X"
            unfolding S\<^sub>r_def by (auto simp: E_def)
          with t(2) show ?thesis
            using \<open>s\<^sub>0 \<in> ?S\<^sub>m\<close> by (auto simp: maximal_def not_le intro: less_le_trans)
        qed
        then show "\<not> (AE x in ?K. ?v s\<^sub>0 \<le> ?v x)"
          using t by (auto simp: not_le AE_measure_pmf_iff E_def cong del: AE_cong intro!: exI[of _ "t"])

        show "AE x in ?K. ?v x \<le> ?v s\<^sub>0"
        proof (subst AE_measure_pmf_iff, safe)
          fix t assume t: "t \<in> ?E s\<^sub>0"
          show "?v t \<le> ?v s\<^sub>0"
          proof cases
            assume "t \<in> S\<^sub>e \<union> S2 \<union> X" then show ?thesis
              using less_s\<^sub>0[of t] t by simp
          next
            assume "t \<notin> S\<^sub>e \<union> S2 \<union> X" with t \<open>s\<^sub>0 \<in> ?S\<^sub>m\<close> \<open>s\<^sub>0 \<in> S\<close> show ?thesis
              by (elim maximalD2) (auto simp: S\<^sub>r_def intro!: ct_closed[of _ t])
          qed
        qed
      qed (insert ct_closed[of s\<^sub>0], auto simp: AE_measure_pmf_iff)
      also have "\<dots> = ?v s\<^sub>0"
        using \<open>s\<^sub>0 \<in> S\<close> measure_pmf.emeasure_space_1[of "ct s\<^sub>0"] by simp
      finally show False
        by simp
    qed
    then obtain s t where s: "s \<in> S\<^sub>r - X" and t: "t \<in> S2 \<union> X" "t \<in> ?M s"
      by auto
    with S2 \<open>X \<subset> S\<^sub>r\<close> have "s \<notin> S2" and "s \<in> S \<and> s \<notin> S2" and "s \<notin> X"and [simp]: "t \<in> S"
      by (auto simp add: S\<^sub>r_def)
    define l' where "l' = l(s := t)"
    then have l'_s[simp, intro]: "l' s = t"
      by simp

    let ?D = "\<lambda>X l. directed_towards S2 (SIGMA s : X. {l s})"
    { fix s' assume "s' \<in> ?D X l" "s' \<in> X"
      from this(1) have "s' \<in> ?D (insert s X) l'"
        by (rule directed_towards_mono) (auto simp: l'_def \<open>s \<notin> X\<close>) }
    note directed_towards_l' = this

    show ?case
    proof (intro bexI ballI, elim insertE)
      show "s \<in> S\<^sub>r - X" by fact
      show "l' \<in> insert s X \<rightarrow> insert s X \<union> S2"
        using s t l by (auto simp: l'_def)
    next
      fix s' assume s': "s' \<in> X"
      moreover
      from desc[OF s'] have "s' \<in> ?D X l" and *: "?v s' \<le> ?v (l s')" "l s' \<in> ?M s'"
        by (auto simp: l_desc_def)
      moreover have "l' s' = l s'"
        using \<open>s' \<in> X\<close> s by (auto simp add: l'_def)
      ultimately show "l_desc (insert s X) ct l' s'"
        by (auto simp: l_desc_def intro!: directed_towards_l')
    next
      fix s' assume "s' = s"
      show "l_desc (insert s X) ct l' s'"
        unfolding \<open>s' = s\<close> l_desc_def l'_s
      proof (intro conjI)
        show "s \<in> ?D (insert s X) l'"
        proof cases
          assume "t \<notin> S2"
          with t have "t \<in> X" by auto
          with desc have "t \<in> ?D X l"
            by (simp add: l_desc_def)
          then show ?thesis
            by (force intro: directed_towards.step[OF directed_towards_l'] \<open>t \<in> X\<close>)
        qed (force intro: directed_towards.step directed_towards.start)

        from \<open>s \<in> S\<^sub>r - X\<close> S\<^sub>r_S1 have [simp]: "s \<in> S1" "s \<in> S"
          by (auto simp: S\<^sub>r_def)
        show "?v s \<le> ?v t"
          using t(2)[THEN maximalD2] ct
          by (auto simp add: v_S1 AE_measure_pmf_iff proper_def Pi_iff PiE_def
                   intro!: measure_pmf.nn_integral_le_const)
      qed fact
    qed
  qed simp
qed

lemma F_v_memoryless:
  obtains ct where "ct \<in> Pi\<^sub>E S K" "v\<circ>simple ct = F_sup (v\<circ>simple ct)"
proof atomize_elim
  define R where "R = {(ct(s := D), ct) | ct s D.
    ct \<in> Pi\<^sub>E S K \<and> proper ct \<and> s \<in> S\<^sub>r \<and> D \<in> K s \<and> v (simple ct s) < (\<integral>\<^sup>+t. v (simple ct t) \<partial>D) }"

  { fix ct ct' assume ct_ct': "(ct', ct) \<in> R"
    let ?v = "\<lambda>s. v (simple ct s)" and ?v' = "\<lambda>s. v (simple ct' s)"

    from ct_ct' obtain s D where "ct \<in> Pi\<^sub>E S K" "proper ct" and s: "s \<in> S\<^sub>r" and D: "D \<in> K s"
      and not_maximal: "?v s < (\<integral>\<^sup>+t. ?v t \<partial>D)" and ct'_eq: "ct' = ct(s := D)"
      by (auto simp: R_def)
    with S\<^sub>r_S1 have ct: "ct \<in> Pi S K" and "s \<in> S" and "s \<in> S1"
      by (auto simp: S\<^sub>r_def)
    then have valid_ct[simp]: "\<And>s. s \<in> S \<Longrightarrow> simple ct s \<in> cfg_on s"
      by simp

    from ct'_eq have [simp]: "ct' s = D" "\<And>t. t \<noteq> s \<Longrightarrow> ct' t = ct t"
      by simp_all

    from ct_ct' S\<^sub>r have ct'_E: "ct' \<in> Pi\<^sub>E S K"
      by (auto simp: ct'_eq R_def)
    from ct s D have ct': "ct' \<in> Pi S K"
      by (auto simp: ct'_eq)
    then have valid_ct'[simp]: "\<And>s. s \<in> S \<Longrightarrow> simple ct' s \<in> cfg_on s"
      by simp

    from exists_l_desc[OF \<open>proper ct\<close>]
    obtain l where l: "l \<in> S\<^sub>r \<rightarrow> S\<^sub>r \<union> S2" and "\<And>s. s \<in> S\<^sub>r \<Longrightarrow> l_desc S\<^sub>r ct l s"
      by auto
    then have directed_l: "\<And>s. s \<in> S\<^sub>r \<Longrightarrow> s \<in> directed_towards S2 (SIGMA s:S\<^sub>r. {l s})"
      and v_l_mono: "\<And>s. s \<in> S\<^sub>r \<Longrightarrow> ?v s \<le> ?v (l s)"
      and l_in_Ea: "\<And>s. s \<in> S\<^sub>r \<Longrightarrow> l s \<in> ct s"
      by (auto simp: l_desc_def dest!: maximalD1)

    let ?E = "\<lambda>ct. SIGMA s:S\<^sub>r. ct s"
    let ?D = "\<lambda>ct. directed_towards S2 (?E ct)"

    have finite_E[simp]: "\<And>s. s \<in> S \<Longrightarrow> finite (ct' s)"
      using ct' K_closed by (intro rev_finite_subset[OF S_finite]) auto

    have "maximal ?v (ct' s) \<noteq> {}"
      using ct' D \<open>s\<in>S\<close> finite_E[of s] by (intro maximal_ne set_pmf_not_empty) (auto simp del: finite_E)
    then obtain s' where s': "s' \<in> maximal ?v (ct' s)"
      by blast
    with K_closed[OF \<open>s \<in> S\<close>] D have "s' \<in> S"
      by (auto dest!: maximalD1)

    have "s' \<noteq> s"
    proof
      assume [simp]: "s' = s"
      have "?v s < (\<integral>\<^sup>+t. ?v t \<partial>D)"
        by fact
      also have "\<dots> \<le> (\<integral>\<^sup>+t. ?v s \<partial>D)"
        using \<open>s \<in> S\<close> s' D by (intro nn_integral_mono_AE) (auto simp: AE_measure_pmf_iff intro: maximalD2)
      finally show False
        using measure_pmf.emeasure_space_1[of D] by (simp add: \<open>s \<in> S\<close> ct)
    qed

    have "p s' \<noteq> 0"
    proof
      assume "p s' = 0"
      then have "?v s' = 0"
        using v_le_p[of "simple ct s'"] ct \<open>s' \<in> S\<close> by (auto intro!: antisym ct)
      then have "(\<integral>\<^sup>+t. ?v t \<partial>D) = 0"
        using maximalD2[OF s'] by (subst nn_integral_0_iff_AE) (auto simp: \<open>s\<in>S\<close> D AE_measure_pmf_iff)
      then have "?v s < 0"
        using not_maximal by auto
      then show False
        using \<open>s\<in>S\<close> by (simp add: ct)
    qed
    with \<open>s' \<in> S\<close> have "s' \<in> S2 \<union> S\<^sub>r"
      by (auto simp: S\<^sub>r_def S\<^sub>e_def)

    have l_acyclic: "(s', s) \<notin> (SIGMA s:S\<^sub>r. {l s})^+"
    proof
      assume "(s', s) \<in> (SIGMA s:S\<^sub>r. {l s})^+"
      then have "?v s' \<le> ?v s"
        by induct (blast intro: order_trans v_l_mono)+
      also have "\<dots> < (\<integral>\<^sup>+t. ?v t \<partial>D)"
        using not_maximal .
      also have "\<dots> \<le> (\<integral>\<^sup>+t. ?v s' \<partial>D)"
        using s' by (intro nn_integral_mono_AE) (auto simp: \<open>s \<in> S\<close> D AE_measure_pmf_iff intro: maximalD2)
      finally show False
        using measure_pmf.emeasure_space_1[of D] by (simp add:\<open>s' \<in> S\<close> ct)
    qed

    from \<open>s' \<in> S2 \<union> S\<^sub>r\<close> have "s' \<in> ?D ct'"
    proof
      assume "s' \<in> S\<^sub>r"
      then have "l s' \<in> directed_towards S2 (SIGMA s:S\<^sub>r. {l s})"
        using l directed_l[of "l s'"] by (auto intro: directed_towards.start)
      moreover from \<open>s' \<in> S\<^sub>r\<close> have "(s', l s') \<in> (SIGMA s:S\<^sub>r. {l s})^+"
        by auto
      ultimately have "l s' \<in> ?D ct'"
      proof induct
        case (step t t')
        then have t: "t \<noteq> s" "t \<in> S\<^sub>r" "t' = l t"
          using l_acyclic by auto

        from step have "(s', t') \<in> (SIGMA s:S\<^sub>r. {l s})\<^sup>+"
          by (blast intro: trancl_into_trancl)
        from step(2)[OF this] show ?case
          by (rule directed_towards.step) (simp add: l_in_Ea t)
      qed (rule directed_towards.start)
      then show "s' \<in> ?D ct'"
        by (rule directed_towards.step)
           (simp add: l_in_Ea \<open>s' \<in> S\<^sub>r\<close> \<open>s \<in> S\<^sub>r\<close> \<open>s' \<noteq> s\<close>)
    qed (rule directed_towards.start)

    have proper: "proper ct'"
      unfolding proper_eq[OF ct'_E]
    proof
      fix t assume "t \<in> S\<^sub>r"
      from directed_l[OF this] show "t \<in> ?D ct'"
      proof induct
        case (step t t')
        show ?case
        proof cases
          assume "t = s"
          with \<open>s \<in> S\<^sub>r\<close> s'[THEN maximalD1] have "(t, s') \<in> ?E ct'"
            by auto
          with \<open>s' \<in> ?D ct'\<close> show ?thesis
            by (rule directed_towards.step)
        next
          assume "t \<noteq> s"
          with step have "(t, t') \<in> ?E ct'"
            by (auto simp: l_in_Ea)
          with step.hyps(2) show ?thesis
            by (rule directed_towards.step)
        qed
      qed (rule directed_towards.start)
    qed

    have "?v \<le> ?v'"
    proof (intro le_funI leI notI)
      fix t' assume *: "?v' t' < ?v t'"
      then have "t' \<in> S"
        by (metis v_nS simple_valid_cfg_iff ct' ct order.irrefl)

      define \<Delta> where "\<Delta> t = enn2real (?v t) - enn2real (?v' t)" for t
      with * \<open>t' \<in> S\<close> have "0 < \<Delta> t'"
        by (cases "?v t'" "?v' t'" rule: ennreal2_cases) (auto simp add: ct' ct ennreal_less_iff)

      { fix t assume t: "t \<in> maximal \<Delta> S"
        with \<open>t' \<in> S\<close> have "\<Delta> t' \<le> \<Delta> t"
          by (auto intro: maximalD2)
        with \<open>0 < \<Delta> t'\<close> have "0 < \<Delta> t" by simp
        with t have "t \<in> S\<^sub>r"
          by (auto simp add: S\<^sub>r_def v_S\<^sub>e ct ct' \<Delta>_def dest!: maximalD1) }
      note max_is_S\<^sub>r = this

      { fix s assume "s \<in> S"
        with v_le_1[of "simple ct' s"] v_le_1[of "simple ct s"]
        have "\<bar>\<Delta> s\<bar> \<le> 1"
          by (cases "?v s" "?v' s" rule: ennreal2_cases) (auto simp: \<Delta>_def ct ct') }
      note \<Delta>_le_1[simp] = this
      then have ennreal_\<Delta>: "\<And>s. s \<in> S \<Longrightarrow> \<Delta> s = ?v s - ?v' s"
        by (auto simp add: \<Delta>_def v_def T.emeasure_eq_measure ct ct' ennreal_minus)

      from \<open>s \<in> S\<close> S_finite have "maximal \<Delta> S \<noteq> {}"
        by (intro maximal_ne) auto
      then obtain t where "t \<in> maximal \<Delta> S" by auto
      from max_is_S\<^sub>r[OF this] proper have "t \<in> ?D ct'"
        unfolding proper_eq[OF ct'_E] by auto
      from this \<open>t \<in> maximal \<Delta> S\<close> show False
      proof induct
        case (start t)
        then have "t \<in> S\<^sub>r"
          by (intro max_is_S\<^sub>r)
        with \<open>t \<in> S2\<close> show False
          by (auto simp: S\<^sub>r_def)
      next
        case (step t t')
        then have t': "t' \<in> ct' t" and "t \<in> S\<^sub>r" and t: "t \<in> maximal \<Delta> S"
          by (auto intro: max_is_S\<^sub>r simp: comp_def)
        then have "t' \<in> S" "t \<in> S1" "t \<in> S"
          using S\<^sub>r_S1 S1
          by (auto simp: Pi_closed[OF ct'])

        have "\<Delta> t \<le> \<Delta> t'"
        proof (intro leI notI)
          assume less: "\<Delta> t' < \<Delta> t"
          have "(\<integral>s. \<Delta> s \<partial>ct' t) < (\<integral>s. \<Delta> t \<partial>ct' t)"
          proof (intro measure_pmf.integral_less_AE)
            show "emeasure (ct' t) {t'} \<noteq> 0" "{t'} \<in> sets (ct' t)"
              "AE s in ct' t. s\<in>{t'} \<longrightarrow> \<Delta> s \<noteq> \<Delta> t"
              using t' less by (auto simp add: emeasure_pmf_single_eq_zero_iff)
            show "AE s in ct' t. \<Delta> s \<le> \<Delta> t"
              using ct' ct t D
              by (auto simp add: AE_measure_pmf_iff ct \<open>t\<in>S\<close> Pi_iff E_def Pi_closed[OF ct']
                       intro!: maximalD2[of t \<Delta>] intro: Pi_closed[OF ct'] maximalD1)
            show "integrable (ct' t) (\<lambda>_. \<Delta> t)" "integrable (ct' t) \<Delta>"
              using ct ct' \<open>t \<in> S\<close> D
              by (auto intro!: measure_pmf.integrable_const_bound[where B=1] \<Delta>_le_1
                       simp: AE_measure_pmf_iff dest: Pi_closed)
          qed
          also have "\<dots> = \<Delta> t"
            using measure_pmf.prob_space[of "ct' t"] by simp
          also have "\<Delta> t \<le> (\<integral>s. enn2real (?v s) \<partial>ct' t) - (\<integral>s. enn2real (?v' s) \<partial>ct' t)"
          proof -
            have "?v t \<le> (\<integral>\<^sup>+s. ?v s \<partial>ct' t)"
            proof cases
              assume "t = s" with not_maximal show ?thesis by simp
            next
              assume "t \<noteq> s" with S1 \<open>t\<in>S1\<close> \<open>t \<in> S\<close> ct ct' show ?thesis
                by (subst v_S1) (auto intro!: nn_integral_mono_AE AE_pmfI)
            qed
            also have "\<dots> = ennreal (\<integral>s. enn2real (?v s) \<partial>ct' t)"
              using ct ct' \<open>t\<in>S\<close>
              by (intro measure_pmf.ennreal_integral_real[symmetric, where B=1])
                 (auto simp: AE_measure_pmf_iff one_ennreal_def[symmetric]
                       intro!: v_le_1 simple_valid_cfg intro: Pi_closed)
            finally have "enn2real (?v t) \<le> (\<integral>s. enn2real (?v s) \<partial>ct' t)"
              using ct \<open>t\<in>S\<close> by (simp add: v_def T.emeasure_eq_measure)
            moreover
            { have "?v' t = (\<integral>\<^sup>+s. ?v' s \<partial>ct' t)"
                using ct ct' \<open>t \<in> S\<close> \<open>t \<in> S1\<close> S1 by (subst v_S1) (auto intro!: nn_integral_cong_AE AE_pmfI)
              also have "\<dots> = ennreal (\<integral>s. enn2real (?v' s) \<partial>ct' t)"
                using ct' \<open>t\<in>S\<close>
                by (intro measure_pmf.ennreal_integral_real[symmetric, where B=1])
                   (auto simp: AE_measure_pmf_iff one_ennreal_def[symmetric]
                         intro!:  v_le_1 simple_valid_cfg intro: Pi_closed)
              finally have "enn2real (?v' t) = (\<integral>s. enn2real (?v' s) \<partial>ct' t)"
                using ct' \<open>t\<in>S\<close> by (simp add: v_def T.emeasure_eq_measure) }
            ultimately show ?thesis
              using \<open>t \<in> S\<close> by (simp add: \<Delta>_def ennreal_minus_mono)
          qed
          also have "\<dots> = (\<integral>s. \<Delta> s \<partial>ct' t)"
            unfolding \<Delta>_def using Pi_closed[OF ct \<open>t\<in>S\<close>] Pi_closed[OF ct' \<open>t\<in>S\<close>] ct ct'
            by (intro Bochner_Integration.integral_diff[symmetric] measure_pmf.integrable_const_bound[where B=1])
               (auto simp: AE_measure_pmf_iff real_v)
          finally show False
            by simp
        qed
        with t[THEN  maximalD2] \<open>t \<in> S\<close> \<open>t' \<in> S\<close> have "\<Delta> t = \<Delta> t'"
          by (auto intro: antisym)
        with t \<open>t' \<in> S\<close> have "t' \<in> maximal \<Delta> S"
          by (auto simp: maximal_def)
        then show ?case
          by fact
      qed
    qed
    moreover have "?v s < ?v' s"
    proof -
      have "?v s < (\<integral>\<^sup>+t. ?v t \<partial>D)"
        by fact
      also have "\<dots> \<le> (\<integral>\<^sup>+t. ?v' t \<partial>D)"
        using \<open>?v \<le> ?v'\<close> \<open>s\<in>S\<close> D ct ct'
        by (intro nn_integral_mono) (auto simp: le_fun_def)
      also have "\<dots> = ?v' s"
        using \<open>s\<in>S1\<close> S1 ct' \<open>s \<in> S\<close> by (subst (2) v_S1) (auto intro!: nn_integral_cong_AE AE_pmfI)
      finally show ?thesis .
    qed
    ultimately have "?v < ?v'"
      by (auto simp: less_le le_fun_def fun_eq_iff)
    note this proper ct' }
  note v_strict = this(1) and proper = this(2) and sc'_R = this(3)

  have "finite (Pi\<^sub>E S K \<times> Pi\<^sub>E S K)"
    by (intro finite_PiE S_finite K_finite finite_SigmaI)
  then have "finite R"
    by (rule rev_finite_subset) (auto simp add: PiE_iff S\<^sub>r_def R_def intro: extensional_arb)
  moreover
  from v_strict have "acyclic R"
    by (rule acyclicI_order)
  ultimately have "wf R"
    by (rule finite_acyclic_wf)

  from exists_proper obtain ct' where ct': "proper ct'" .
  define ct where "ct = restrict ct' S"
  with ct' have sc_Pi: "ct \<in> Pi S K" and "ct' \<in> Pi S K"
    by (auto simp: proper_def)
  then have ct: "ct \<in> {ct \<in> Pi\<^sub>E S K. proper ct}"
    using ct' directed_towards_mono[where F="SIGMA s:S\<^sub>r. ct' s" and G="SIGMA s:S\<^sub>r. ct s"]
    apply simp
    apply (subst proper_eq)
    by (auto simp: ct_def proper_eq[OF properD1[OF ct']] subset_eq S\<^sub>r_def)

  show "\<exists>ct. ct \<in> Pi\<^sub>E S K \<and> v\<circ>simple ct = F_sup (v\<circ>simple ct)"
  proof (rule wfE_min[OF \<open>wf R\<close> ct])
    fix ct assume ct: "ct \<in> {ct \<in> Pi\<^sub>E S K. proper ct}"
    then have "ct \<in> Pi S K" "proper ct"
      by (auto simp: proper_def)
    assume min: "\<And>ct'. (ct', ct) \<in> R \<Longrightarrow> ct' \<notin> {ct \<in> Pi\<^sub>E S K. proper ct}"
    let ?v = "\<lambda>s. v (simple ct s)"
    { fix s assume "s \<in> S" "s \<in> S1" "s \<notin> S2"
      with ct have "ct s \<in> K s" "?v s \<le> integral\<^sup>N (ct s) ?v"
        by (auto simp: v_S1 PiE_def intro!: nn_integral_mono_AE AE_pmfI)
      moreover
      { have "0 \<le> ?v s"
          using \<open>s\<in>S\<close> ct by (simp add: PiE_def)
        also assume v_less: "?v s < (\<Squnion>D\<in>K s. \<integral>\<^sup>+ s. v (simple ct s) \<partial>measure_pmf D)"
        also have "\<dots> \<le> p s"
          unfolding p_S1[OF \<open>s\<in>S1\<close>] using \<open>s\<in>S\<close> ct v_le_p[OF simple_valid_cfg, OF \<open>ct \<in> Pi S K\<close>]
          by (auto intro!: SUP_mono nn_integral_mono_AE bexI
                   simp: PiE_def AE_measure_pmf_iff set_pmf_closed)
        finally have "s \<in> S\<^sub>r"
          using \<open>s\<in>S\<close> \<open>s\<notin>S2\<close> by (simp add: S\<^sub>r_def S\<^sub>e_def)

        from v_less obtain D where "D \<in> K s" "?v s < integral\<^sup>N D ?v"
          by (auto simp: less_SUP_iff)
        with ct \<open>s\<in>S\<close> \<open>s\<in>S\<^sub>r\<close> have "(ct(s:=D), ct) \<in> R" "ct(s:=D) \<in> Pi\<^sub>E S K"
          unfolding R_def by (auto simp: PiE_def extensional_def)
        from proper[OF this(1)] min[OF this(1)] ct \<open>D \<in> K s\<close> \<open>s\<in>S\<close> this(2)
        have False
          by simp }
      ultimately have "?v s = (\<Squnion>D\<in>K s. \<integral>\<^sup>+ s. ?v s \<partial>measure_pmf D)"
        by (auto intro: antisym SUP_upper2[where i="ct s"] leI)
      also have "\<dots> = (\<Squnion>D\<in>K s. integral\<^sup>N (measure_pmf D) (\<lambda>s\<in>S. ?v s))"
        using \<open>s\<in>S\<close> by (auto intro!: SUP_cong nn_integral_cong v_nS simp: ct simple_valid_cfg_iff \<open>ct \<in> Pi S K\<close>)
      finally have "?v s = (\<Squnion>D\<in>K s. integral\<^sup>N (measure_pmf D) (\<lambda>s\<in>S. ?v s))" . }
    then have "?v = F_sup ?v"
      unfolding F_sup_def using ct
      by (auto intro!: ext v_S2 simple_cfg_on v_nS v_nS12 SUP_cong nn_integral_cong
               simp: PiE_def simple_valid_cfg_iff)
    with ct show ?thesis
      by (auto simp: comp_def)
  qed
qed

lemma p_v_memoryless:
  obtains ct where "ct \<in> Pi\<^sub>E S K" "p = v\<circ>simple ct"
proof -
  obtain ct where ct_PiE: "ct \<in> Pi\<^sub>E S K" and eq: "v\<circ>simple ct = F_sup (v\<circ>simple ct)"
    by (rule F_v_memoryless)
  then have ct: "ct \<in> Pi S K"
    by (simp add: PiE_def)
  have "p = v\<circ>simple ct"
  proof (rule antisym)
    show "p \<le> v\<circ>simple ct"
      unfolding p_eq_lfp_F_sup by (rule lfp_lowerbound) (metis order_refl eq)
    show "v\<circ>simple ct \<le> p"
    proof (rule le_funI)
      fix s show "(v\<circ>simple ct) s \<le> p s"
        using v_le_p[of "simple ct s"]
        by (cases "s \<in> S") (auto simp del: simp add: v_def ct)
    qed
  qed
  with ct_PiE that show thesis by auto
qed

definition "n = (\<lambda>s\<in>S. P_inf s (\<lambda>\<omega>. (HLD S1 suntil HLD S2) (s ## \<omega>)))"

lemma n_eq_INF_v: "s \<in> S \<Longrightarrow> n s = (\<Sqinter>cfg\<in>cfg_on s. v cfg)"
  by (auto simp add: n_def v_def P_inf_def T.emeasure_eq_measure valid_cfgI intro!: INF_cong)

lemma n_le_v: "s \<in> S \<Longrightarrow> cfg \<in> cfg_on s \<Longrightarrow> n s \<le> v cfg"
  by (subst n_eq_INF_v) (blast intro!: INF_lower)+

lemma n_eq_1_imp: "s \<in> S \<Longrightarrow> cfg \<in> cfg_on s \<Longrightarrow> n s = 1 \<Longrightarrow> v cfg = 1"
  using n_le_v[of s cfg] v_le_1[of cfg] by (auto intro: antisym valid_cfgI)

lemma n_eq_1_iff: "s \<in> S \<Longrightarrow> n s = 1 \<longleftrightarrow> (\<forall>cfg\<in>cfg_on s. v cfg = 1)"
  apply rule
  apply (metis n_eq_1_imp)
  apply (auto simp: n_eq_INF_v intro!: INF_eqI)
  done

lemma n_le_1: "s \<in> S \<Longrightarrow> n s \<le> 1"
  by (auto simp: n_eq_INF_v intro!: INF_lower2[OF simple_cfg_on[of arb_act]] v_le_1)

lemma n_undefined[simp]: "s \<notin> S \<Longrightarrow> n s = undefined"
  by (simp add: n_def)

lemma n_eq_0: "s \<in> S \<Longrightarrow> cfg \<in> cfg_on s \<Longrightarrow> v cfg = 0 \<Longrightarrow> n s = 0"
  using n_le_v[of s cfg] by auto

lemma n_not_inf[simp]: "s \<in> S \<Longrightarrow> n s \<noteq> top"
  using n_le_1[of s] by (auto simp: top_unique)

lemma n_S1: "s \<in> S1 \<Longrightarrow> n s = (\<Sqinter>D\<in>K s. \<integral>\<^sup>+ t. n t \<partial>measure_pmf D)"
  using S1 S1_S2 unfolding n_def
  apply auto
  apply (subst P_inf_iterate)
  apply (auto intro!: nn_integral_cong_AE INF_cong intro: set_pmf_closed
              simp: AE_measure_pmf_iff suntil_Stream set_eq_iff)
  done

lemma n_S2[simp]: "s \<in> S2 \<Longrightarrow> n s = 1"
  using S2 by (auto simp add: n_eq_INF_v valid_cfgI)

lemma n_nS12: "s \<in> S \<Longrightarrow> s \<notin> S1 \<Longrightarrow> s \<notin> S2 \<Longrightarrow> n s = 0"
  by (auto simp add: n_eq_INF_v valid_cfgI)

lemma n_pos:
  assumes "P s" "s \<in> S1" "wf R"
  assumes cont: "\<And>s D. P s \<Longrightarrow> s \<in> S1 \<Longrightarrow> D \<in> K s \<Longrightarrow> \<exists>w\<in>D. ((w, s) \<in> R \<and> w \<in> S1 \<and> P w) \<or> 0 < n w"
  shows "0 < n s"
  using \<open>wf R\<close> \<open>P s\<close> \<open>s\<in>S1\<close>
proof (induction s)
  case (less s)
  with S1 have [simp]: "s \<in> S" by auto
  let ?I = "\<lambda>D::'s pmf. \<integral>\<^sup>+t. n t \<partial>D"
  have "0 < Min (?I`K s)"
  proof (safe intro!: Min_gr_iff [THEN iffD2])
    fix D assume [simp]: "D \<in> K s"
    from cont[OF \<open>P s\<close> \<open>s \<in> S1\<close> \<open>D \<in> K s\<close>]
    obtain w where w: "w \<in> D" "0 < n w"
      by (force intro: less.IH)
    have in_S: "\<And>t. t \<in> D \<Longrightarrow> t \<in> S"
      using set_pmf_closed[OF \<open>s \<in> S\<close> \<open>D \<in> K s\<close>] by auto
    from w have "0 < pmf D w * n w"
      by (simp add: pmf_positive ennreal_zero_less_mult_iff)
    also have "\<dots> = (\<integral>\<^sup>+t. n w * indicator {w} t \<partial>D)"
      by (subst nn_integral_cmult_indicator)
         (auto simp: ac_simps emeasure_pmf_single in_S \<open>w \<in> D\<close>)
    also have "\<dots> \<le> (\<integral>\<^sup>+t. n t \<partial>D)"
      by (intro nn_integral_mono_AE) (auto split: split_indicator simp: AE_measure_pmf_iff in_S)
    finally show "0 < (\<integral>\<^sup>+t. n t \<partial>D)" .
  qed (insert K_wf K_finite \<open>s\<in>S\<close>, auto)
  also have "\<dots> = n s"
    unfolding n_S1[OF \<open>s \<in> S1\<close>]
    using K_wf K_finite \<open>s\<in>S\<close> by (intro Min_Inf) auto
  finally show "0 < n s" .
qed

definition F_inf :: "('s \<Rightarrow> ennreal) \<Rightarrow> ('s \<Rightarrow> ennreal)" where
  "F_inf f = (\<lambda>s\<in>S. if s \<in> S2 then 1 else if s \<in> S1 then (\<Sqinter>D\<in>K s. \<integral>\<^sup>+ t. f t \<partial>measure_pmf D) else 0)"

lemma F_inf_n: "F_inf n = n"
  by (simp add: F_inf_def n_nS12 n_S1 fun_eq_iff)

lemma F_inf_nS[simp]: "s \<notin> S \<Longrightarrow> F_inf f s = undefined"
  by (simp add: F_inf_def)

lemma mono_F_inf: "mono F_inf"
  by (auto intro!: INF_superset_mono nn_integral_mono simp: mono_def F_inf_def le_fun_def)

lemma S1_nS2: "s \<in> S1 \<Longrightarrow> s \<notin> S2"
  using S1_S2 by auto

lemma n_eq_lfp_F_inf: "n = lfp F_inf"
proof (intro antisym lfp_lowerbound le_funI)
  fix s let ?I = "\<lambda>D. (\<integral>\<^sup>+t. lfp F_inf t \<partial>measure_pmf D)"
  define ct where "ct s = (SOME D. D \<in> K s \<and> (s \<in> S1 \<longrightarrow> lfp F_inf s = ?I D))" for s
  { fix s assume s: "s \<in> S"
    then have "finite (?I ` K s)"
      by (auto intro: K_finite)
    with s obtain D where "D \<in> K s" "(\<integral>\<^sup>+t. lfp F_inf t \<partial>D) = Min (?I ` K s)"
      by (auto simp: K_wf dest!: Min_in)
    note this(2)
    also have "\<dots> = (INF D \<in> K s. ?I D)"
      using s K_wf by (subst Min_Inf) (auto intro: K_finite)
    also have "s \<in> S1 \<Longrightarrow> \<dots> = lfp F_inf s"
      using s S1_S2 by (subst (3) lfp_unfold[OF mono_F_inf]) (auto simp add: F_inf_def)
    finally have "\<exists>D. D \<in> K s \<and> (s \<in> S1 \<longrightarrow> lfp F_inf s = ?I D)"
      using \<open>D \<in> K s\<close> by auto
    then have "ct s \<in> K s \<and> (s \<in> S1 \<longrightarrow> lfp F_inf s = ?I (ct s))"
      unfolding ct_def by (rule someI_ex)
    then have "ct s \<in> K s" "s \<in> S1 \<Longrightarrow> lfp F_inf s = ?I (ct s)"
      by auto }
  note ct = this
  then have Pi_ct: "ct \<in> Pi S K"
    by auto
  then have valid_ct[simp]: "\<And>s. s \<in> S \<Longrightarrow> simple ct s \<in> valid_cfg"
    by simp
  let ?F = "\<lambda>P. HLD S2 or (HLD S1 aand nxt P)"
  define P where "P s n =
      emeasure (T (simple ct s)) {x\<in>space (T (simple ct s)). (?F ^^ n) (\<lambda>x. False) (s ## x)}"
    for s n
  { assume "s \<in> S"
    with S1 have [simp, measurable]: "s \<in> S" by auto
    then have "n s \<le> v (simple ct s)"
      by (intro n_le_v) (auto intro: simple_cfg_on[OF Pi_ct])
    also have "\<dots> = emeasure (T (simple ct s)) {x\<in>space (T (simple ct s)). lfp ?F (s ## x)}"
      using S1_S2
      by (simp add: v_eq[OF simple_valid_cfg[OF Pi_ct \<open>s\<in>S\<close>]])
         (simp add: suntil_lfp space_T[symmetric, of "simple ct s"] del: space_T)
    also have "\<dots> = (\<Squnion>n. P s n)" unfolding P_def
      apply (rule emeasure_lfp2[where P="\<lambda>M. \<exists>s. M = T (simple ct s)" and M="T (simple ct s)"])
      apply (intro exI[of _ s] refl)
      apply (auto simp: sup_continuous_def) []
      apply auto []
    proof safe
      fix A s assume "\<And>N. \<exists>s. N = T (simple ct s) \<Longrightarrow> Measurable.pred N A"
      then have "\<And>s. Measurable.pred (T (simple ct s)) A"
        by metis
      then have "\<And>s. Measurable.pred St A"
        by simp
      then show "Measurable.pred (T (simple ct s)) (\<lambda>xs. HLD S2 xs \<or> HLD S1 xs \<and> nxt A xs)"
        by simp
    qed
    also have "\<dots> \<le> lfp F_inf s"
    proof (intro SUP_least)
      fix n from \<open>s\<in>S\<close> show "P s n \<le> lfp F_inf s"
      proof (induct n arbitrary: s)
        case 0 with S1 show ?case
          by (subst lfp_unfold[OF mono_F_inf]) (auto simp: P_def)
      next
        case (Suc n)

        show ?case
        proof cases
          assume "s \<in> S1" with S1_S2 S1 have s[simp]: "s \<notin> S2" "s \<in> S" "s \<in> S1" by auto
          have "P s (Suc n) = (\<integral>\<^sup>+t. P t n \<partial>ct s)"
            unfolding P_def space_T
            apply (subst emeasure_Collect_T)
            apply (rule measurable_compose[OF measurable_Stream[OF measurable_const measurable_ident_sets[OF refl]]])
            apply (measurable, assumption)
            apply (auto simp: K_cfg_def map_pmf_rep_eq nn_integral_distr
                        intro!: nn_integral_cong_AE AE_pmfI)
            done
          also have "\<dots> \<le> (\<integral>\<^sup>+t. lfp F_inf t \<partial>ct s)"
            using Pi_closed[OF Pi_ct \<open>s \<in> S\<close>]
            by (auto intro!: nn_integral_mono_AE Suc simp: AE_measure_pmf_iff)
          also have "\<dots> = lfp F_inf s"
            by (intro ct(2)[symmetric]) auto
          finally show ?thesis .
        next
          assume "s \<notin> S1" with S2 \<open>s \<in> S\<close> show ?case
            using T.emeasure_space_1[of "simple ct s"]
            by (subst lfp_unfold[OF mono_F_inf]) (auto simp: F_inf_def P_def)
        qed
      qed
    qed
    finally have "n s \<le> lfp F_inf s" . }
  moreover have "s \<notin> S \<Longrightarrow> n s \<le> lfp F_inf s"
    by (subst lfp_unfold[OF mono_F_inf]) (simp add: n_def F_inf_def)
  ultimately show "n s \<le> lfp F_inf s"
    by blast
qed (simp add: F_inf_n)


lemma real_n: "s \<in> S \<Longrightarrow> ennreal (enn2real (n s)) = n s"
  by (cases "n s") simp_all

lemma real_p: "s \<in> S \<Longrightarrow> ennreal (enn2real (p s)) = p s"
  by (cases "p s") simp_all

lemma p_ub:
  fixes x
  assumes "s \<in> S"
  assumes solution: "\<And>s D. s \<in> S1 \<Longrightarrow> D \<in> K s \<Longrightarrow> (\<Sum>t\<in>S. pmf D t * x t) \<le> x s"
  assumes solution_0: "\<And>s. s \<in> S \<Longrightarrow> p s = 0 \<Longrightarrow> x s = 0"
  assumes solution_S2: "\<And>s. s \<in> S2 \<Longrightarrow> x s = 1"
  shows "enn2real (p s) \<le> x s" (is "?y s \<le> _")
proof -
  let ?p = "\<lambda>s. enn2real (p s)"
  from p_v_memoryless obtain sc where "sc \<in> Pi\<^sub>E S K" and p_eq: "p = v \<circ> simple sc"
    by auto
  then have sch: "\<And>s. s \<in> S \<Longrightarrow> sc s \<in> K s" and sc_Pi: "sc \<in> Pi S K"
    by (auto simp: PiE_iff)

  interpret sc: MC_syntax sc .

  define N where "N = {s\<in>S. p s = 0} \<union> S2"
  { fix s assume "s \<in> S" "s \<notin> N"
    with p_nS12 have "s \<in> S1"
      by (auto simp add: N_def) }
  note N = this

  have N_S: "N \<subseteq> S"
    using S2 by (auto simp: N_def)

  have finite_sc[intro]: "s \<in> S \<Longrightarrow> finite (sc s)" for s
    using \<open>sc \<in> Pi\<^sub>E S K\<close> by (auto simp: PiE_iff intro: set_pmf_finite)


  show ?thesis
  proof cases
    assume "s \<in> S - N"
    then show ?thesis
    proof (rule mono_les)
      show "(\<Union>x\<in>S - N. set_pmf (sc x)) \<subseteq> S - N \<union> N"
        using Pi_closed[OF sc_Pi] by auto
      show "finite ((\<lambda>s. ?p s - x s) ` (S - N \<union> N))"
        using N_S by (intro finite_imageI finite_subset[OF _ S_finite]) auto
    next
      fix s assume "s \<in> N" then show "?p s \<le> x s"
        by (auto simp: N_def solution_S2 solution_0)
    next
      fix s assume s: "s \<in> S - N"
      then show "integrable (sc s) x" "integrable (sc s) ?p"
        by (auto intro!: integrable_measure_pmf_finite set_pmf_finite sch)

      from s have "s \<in> S1" "s \<in> S"
        using p_nS12[of s] by (auto simp: N_def)
      then show "?p s \<le> (\<integral> t. ?p t \<partial>sc s) + 0"
        unfolding p_eq using real_v_integral_eq[of "simple sc s"]
        by (auto simp add: v_S1 sc_Pi intro!: integral_mono_AE integrable_measure_pmf_finite AE_pmfI)
      show "(\<integral> t. x t \<partial>sc s) + 0 \<le> x s"
        using solution[OF \<open>s \<in> S1\<close> sch[OF \<open>s \<in> S\<close>]]
        by (subst integral_measure_pmf[where A=S])
           (auto intro: S_finite Pi_closed[OF sc_Pi] \<open>s \<in> S\<close> simp: ac_simps)

      define X where "X = (SIGMA x:UNIV. sc x)"
      show "\<exists>t\<in>N. (s, t) \<in> X\<^sup>*"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then have *: "\<forall>t\<in>N. (s, t) \<notin> X\<^sup>*"
          by auto
        with \<open>s\<in>S\<close> have "v (simple sc s) = 0"
        proof (coinduction arbitrary: s rule: v_eq_0_coinduct)
          case (valid t) with sch show ?case
            by auto
        next
          case (nS2 s) then show ?case
            by (auto simp: N_def)
        next
          case (cont cfg s)
          then have "(s, state cfg) \<in> X\<^sup>*"
            by (auto simp: X_def set_K_cfg)
          with cont show ?case
            by (auto simp: set_K_cfg intro!: exI intro: Pi_closed[OF sc_Pi])
               (blast intro: rtrancl_trans)
        qed
        then have "p s = 0"
          unfolding p_eq by simp
        with \<open>s\<in>S\<close> have "s\<in>N"
          by (auto simp: N_def)
        with * show False
          by auto
      qed
    qed
  next
    assume "s \<notin> S - N" with \<open>s \<in> S\<close> show "?p s \<le> x s"
      by (auto simp: N_def solution_0 solution_S2)
  qed
qed

lemma n_lb:
  fixes x
  assumes "s \<in> S"
  assumes solution: "\<And>s D. s \<in> S1 \<Longrightarrow> D \<in> K s \<Longrightarrow> x s \<le> (\<Sum>t\<in>S. pmf D t * x t)"
  assumes solution_n0: "\<And>s. s \<in> S \<Longrightarrow> n s = 0 \<Longrightarrow> x s = 0"
  assumes solution_S2: "\<And>s. s \<in> S2 \<Longrightarrow> x s = 1"
  shows "x s \<le> enn2real (n s)" (is "_ \<le> ?y s")
proof -
  let ?I = "\<lambda>D::'s pmf. \<integral>\<^sup>+x. n x \<partial>D"
  { fix s assume "s \<in> S1"
    with S1 S1_S2 have "n s = (\<Sqinter>D\<in>K s. ?I D)"
      by (subst n_eq_lfp_F_inf, subst lfp_unfold[OF mono_F_inf])
         (auto simp add: F_inf_def n_eq_lfp_F_inf)
    moreover have "(\<Sqinter>D\<in>K s. \<integral>\<^sup>+x. n x \<partial>measure_pmf D) = Min (?I`K s)"
      using \<open>s \<in> S1\<close> S1 K_wf
      by (intro cInf_eq_Min finite_imageI K_finite) auto
    moreover have "Min (?I`K s) \<in> ?I`K s"
      using \<open>s \<in> S1\<close> S1 K_wf by (intro Min_in finite_imageI K_finite) auto
    ultimately have "\<exists>D\<in>K s. (\<integral>\<^sup>+x. n x \<partial>D) = n s"
      by auto }
  then have "\<And>s. s \<in> S \<Longrightarrow> \<exists>D\<in>K s. s \<in> S1 \<longrightarrow> (\<integral>\<^sup>+x. n x \<partial>D) = n s"
    using K_wf by auto
  then obtain sc where sch: "\<And>s. s \<in> S \<Longrightarrow> sc s \<in> K s"
    and n_sc: "\<And>s. s \<in> S1 \<Longrightarrow> (\<integral>\<^sup>+x. n x \<partial>sc s) = n s"
    by (metis S1 subsetD)
  then have sc_Pi: "sc \<in> Pi S K"
    by auto

  define N where "N = {s\<in>S. n s = 0} \<union> S2"
  with S2 have N_S: "N \<subseteq> S"
    by auto
  { fix s assume "s \<in> S" "s \<notin> N"
    with n_nS12 have "s \<in> S1"
      by (auto simp add: N_def) }
  note N = this

  let ?n = "\<lambda>s. enn2real (n s)"
  show ?thesis
  proof cases
    assume "s \<in> S - N"
    then show ?thesis
    proof (rule mono_les)
      show "(\<Union>x\<in>S - N. set_pmf (sc x)) \<subseteq> S - N \<union> N"
        using Pi_closed[OF sc_Pi] by auto
      show "finite ((\<lambda>s. x s - ?n s) ` (S - N \<union> N))"
        using N_S by (intro finite_imageI finite_subset[OF _ S_finite]) auto
    next
      fix s assume "s \<in> N" then show "x s \<le> ?n s"
        by (auto simp: N_def solution_S2 solution_n0)
    next
      fix s assume s: "s \<in> S - N"
      then show "integrable (sc s) x" "integrable (sc s) ?n"
        by (auto intro!: integrable_measure_pmf_finite set_pmf_finite sch)

      from s have "s \<in> S1" "s \<in> S"
        using n_nS12[of s] by (auto simp: N_def)
      then have "(\<integral> t. ?n t \<partial>sc s) = ?n s"
        apply (subst n_sc[symmetric, of s])
        apply simp_all
        apply (subst integral_eq_nn_integral)
        apply (auto simp: Pi_closed[OF sc_Pi] AE_measure_pmf_iff
                    intro!: arg_cong[where f=enn2real] nn_integral_cong_AE real_n)
        done
      then show "(\<integral> t. ?n t \<partial>sc s) + 0 \<le> ?n s"
        by simp

      show "x s \<le> (\<integral> t. x t \<partial>sc s) + 0"
        using solution[OF \<open>s \<in> S1\<close> sch[OF \<open>s \<in> S\<close>]]
        by (subst integral_measure_pmf[where A=S])
           (auto intro: S_finite Pi_closed[OF sc_Pi] \<open>s \<in> S\<close> simp: ac_simps)

      define X where "X = (SIGMA x:UNIV. sc x)"
      show "\<exists>t\<in>N. (s, t) \<in> X\<^sup>*"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then have *: "\<forall>t\<in>N. (s, t) \<notin> X\<^sup>*"
          by auto
        with \<open>s\<in>S\<close> have "v (simple sc s) = 0"
        proof (coinduction arbitrary: s rule: v_eq_0_coinduct)
          case (valid t) with sch show ?case
            by auto
        next
          case (nS2 s) then show ?case
            by (auto simp: N_def)
        next
          case (cont cfg s)
          then have "(s, state cfg) \<in> X\<^sup>*"
            by (auto simp: X_def set_K_cfg)
          with cont show ?case
            by (auto simp: set_K_cfg intro!: exI intro: Pi_closed[OF sc_Pi])
               (blast intro: rtrancl_trans)
        qed
        from n_eq_0[OF \<open>s \<in> S\<close> simple_cfg_on this] have "n s = 0"
          by (auto simp: sc_Pi)
        with \<open>s\<in>S\<close> have "s\<in>N"
          by (auto simp: N_def)
        with * show False
          by auto
      qed
    qed
  next
    assume "s \<notin> S - N" with \<open>s \<in> S\<close> show "x s \<le> ?n s"
      by (auto simp: N_def solution_n0 solution_S2)
  qed
qed

end

end
