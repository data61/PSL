theory Poincare_Map
imports
  Flow
begin

abbreviation "plane n c \<equiv> {x. x \<bullet> n = c}"

lemma
  eventually_tendsto_compose_within:
  assumes "eventually P (at l within S)"
  assumes "P l"
  assumes "(f \<longlongrightarrow> l) (at x within T)"
  assumes "eventually (\<lambda>x. f x \<in> S) (at x within T)"
  shows "eventually (\<lambda>x. P (f x)) (at x within T)"
proof -
  from assms(1) assms(2) obtain U where U:
    "open U" "l \<in> U" "\<And>x. x \<in> U \<Longrightarrow> x \<in> S \<Longrightarrow> P x"
    by (force simp: eventually_at_topological)
  from topological_tendstoD[OF assms(3) \<open>open U\<close> \<open>l \<in> U\<close>]
  have "\<forall>\<^sub>F x in at x within T. f x \<in> U" by auto
  then show ?thesis using assms(4)
    by eventually_elim (auto intro!: U)
qed

lemma
  eventually_eventually_withinI:\<comment> \<open>aha...\<close>
  assumes "\<forall>\<^sub>F x in at x within A. P x" "P x"
  shows "\<forall>\<^sub>F a in at x within S. \<forall>\<^sub>F x in at a within A. P x"
  using assms
  unfolding eventually_at_topological
  by force

lemma eventually_not_in_closed:
  assumes "closed P"
  assumes "f t \<notin> P" "t \<in> T"
  assumes "continuous_on T f"
  shows "\<forall>\<^sub>F t in at t within T. f t \<notin> P"
  using assms
  unfolding Compl_iff[symmetric] closed_def continuous_on_topological eventually_at_topological
  by metis

context ll_on_open_it begin

lemma
  existence_ivl_trans':
  assumes "t + s \<in> existence_ivl t0 x0"
    "t \<in> existence_ivl t0 x0"
  shows "t + s \<in> existence_ivl t (flow t0 x0 t)"
  by (meson assms(1) assms(2) general.existence_ivl_reverse general.flow_solves_ode
      general.is_interval_existence_ivl general.maximal_existence_flow(1)
      general.mem_existence_ivl_iv_defined(2) general.mem_existence_ivl_subset
      local.existence_ivl_subset subsetD)

end

context auto_ll_on_open\<comment> \<open>TODO: generalize to continuous systems\<close>
begin

definition returns_to ::"'a set \<Rightarrow> 'a \<Rightarrow> bool"
  where "returns_to P x \<longleftrightarrow> (\<forall>\<^sub>F t in at_right 0. flow0 x t \<notin> P) \<and> (\<exists>t>0. t \<in> existence_ivl0 x \<and> flow0 x t \<in> P)"

definition return_time :: "'a set \<Rightarrow> 'a \<Rightarrow> real"
  where "return_time P x =
    (if returns_to P x then (SOME t.
      t > 0 \<and>
      t \<in> existence_ivl0 x \<and>
      flow0 x t \<in> P \<and>
      (\<forall>s \<in> {0<..<t}. flow0 x s \<notin> P)) else 0)"

lemma returns_toI:
  assumes t: "t > 0" "t \<in> existence_ivl0 x" "flow0 x t \<in> P"
  assumes ev: "\<forall>\<^sub>F t in at_right 0. flow0 x t \<notin> P"
  assumes "closed P"
  shows "returns_to P x"
  using assms
  by (auto simp: returns_to_def)

lemma returns_to_outsideI:
  assumes t: "t \<ge> 0" "t \<in> existence_ivl0 x" "flow0 x t \<in> P"
  assumes ev: "x \<notin> P"
  assumes "closed P"
  shows "returns_to P x"
proof cases
  assume "t > 0"
  moreover
  have "\<forall>\<^sub>F s in at 0 within {0 .. t}. flow0 x s \<notin> P"
    using assms mem_existence_ivl_iv_defined ivl_subset_existence_ivl[OF \<open>t \<in> _\<close>] \<open>0 < t\<close>
    by (auto intro!: eventually_not_in_closed flow_continuous_on continuous_intros
        simp: eventually_conj_iff)
  with order_tendstoD(2)[OF tendsto_ident_at \<open>0 < t\<close>, of "{0<..}"]
  have "\<forall>\<^sub>F t in at_right 0. flow0 x t \<notin> P"
    unfolding eventually_at_filter
    by eventually_elim (use \<open>t > 0\<close> in auto)
  then show ?thesis
    by (auto intro!: returns_toI assms \<open>0 < t\<close>)
qed (use assms in simp)

lemma returns_toE:
  assumes "returns_to P x"
  obtains t0 t1 where
    "0 < t0"
    "t0 \<le> t1"
    "t1 \<in> existence_ivl0 x"
    "flow0 x t1 \<in> P"
    "\<And>t. 0 < t \<Longrightarrow> t < t0 \<Longrightarrow> flow0 x t \<notin> P"
proof -
  obtain t0 t1 where t0: "t0 > 0" "\<And>t. 0 < t \<Longrightarrow> t < t0 \<Longrightarrow> flow0 x t \<notin> P"
    and t1: "t1 > 0" "t1 \<in> existence_ivl0 x" "flow0 x t1 \<in> P"
    using assms
    by (auto simp: returns_to_def eventually_at_right[OF zero_less_one])
  moreover
  have "t0 \<le> t1"
    using t0(2)[of t1] t1 t0(1)
    by force
  ultimately show ?thesis by (blast intro: that)
qed

lemma return_time_some:
  assumes "returns_to P x"
  shows "return_time P x =
    (SOME t. t > 0 \<and> t \<in> existence_ivl0 x \<and> flow0 x t \<in> P \<and> (\<forall>s \<in> {0<..<t}. flow0 x s \<notin> P))"
  using assms by (auto simp: return_time_def)

lemma return_time_ex1:
  assumes "returns_to P x"
  assumes "closed P"
  shows "\<exists>!t. t > 0 \<and> t \<in> existence_ivl0 x \<and> flow0 x t \<in> P \<and> (\<forall>s \<in> {0<..<t}. flow0 x s \<notin> P)"
proof -
  from returns_toE[OF \<open>returns_to P x\<close>]
  obtain t0 t1 where
    t1: "t1 \<ge> t0" "t1 \<in> existence_ivl0 x" "flow0 x t1 \<in> P"
    and t0: "t0 > 0" "\<And>t. 0 < t \<Longrightarrow> t < t0 \<Longrightarrow> flow0 x t \<notin> P"
    by metis
  from flow_continuous_on have cont: "continuous_on {0 .. t1} (flow0 x)"
    by (rule continuous_on_subset) (intro ivl_subset_existence_ivl t1)
  from cont have cont': "continuous_on {t0 .. t1} (flow0 x)"
    by (rule continuous_on_subset) (use \<open>0 < t0\<close> in auto)
  have "compact (flow0 x -` P \<inter> {t0 .. t1})"
    using \<open>closed P\<close> cont'
    by (auto simp: compact_eq_bounded_closed bounded_Int bounded_closed_interval
        intro!: closed_vimage_Int)

  have "flow0 x -` P \<inter> {t0..t1} \<noteq> {}"
    using t1 t0 by auto
  from compact_attains_inf[OF \<open>compact _\<close> this] t0 t1
  obtain rt where rt: "t0 \<le> rt" "rt \<le> t1" "flow0 x rt \<in> P"
    and least: "\<And>t'. flow0 x t' \<in> P \<Longrightarrow> t0 \<le> t' \<Longrightarrow> t' \<le> t1 \<Longrightarrow> rt \<le> t'"
    by auto
  have "0 < rt" "flow0 x rt \<in> P" "rt \<in> existence_ivl0 x"
    and "0 < t' \<Longrightarrow> t' < rt \<Longrightarrow> flow0 x t' \<notin> P" for t'
    using ivl_subset_existence_ivl[OF \<open>t1 \<in> existence_ivl0 x\<close>] t0 t1 rt least[of t']
    by force+
  then show ?thesis
    by (intro ex_ex1I) force+
qed

lemma
  return_time_pos_returns_to:
  "return_time P x > 0 \<Longrightarrow> returns_to P x"
  by (auto simp: return_time_def split: if_splits)

lemma
  assumes ret: "returns_to P x"
  assumes "closed P"
  shows return_time_pos: "return_time P x > 0"
  using someI_ex[OF return_time_ex1[OF assms, THEN ex1_implies_ex]]
  unfolding return_time_some[OF ret, symmetric]
  by auto

lemma returns_to_return_time_pos:
  assumes "closed P"
  shows "returns_to P x \<longleftrightarrow> return_time P x > 0"
  by (auto intro!: return_time_pos assms) (auto simp: return_time_def split: if_splits)

lemma return_time:
  assumes ret: "returns_to P x"
  assumes "closed P"
  shows "return_time P x > 0"
    and return_time_exivl: "return_time P x \<in> existence_ivl0 x"
    and return_time_returns: "flow0 x (return_time P x) \<in> P"
    and return_time_least: "\<And>s. 0 < s \<Longrightarrow> s < return_time P x \<Longrightarrow> flow0 x s \<notin> P"
  using someI_ex[OF return_time_ex1[OF assms, THEN ex1_implies_ex]]
  unfolding return_time_some[OF ret, symmetric]
  by auto

lemma returns_to_earlierI:
  assumes ret: "returns_to P (flow0 x t)" "closed P"
  assumes "t \<ge> 0" "t \<in> existence_ivl0 x"
  assumes ev: "\<forall>\<^sub>F t in at_right 0. flow0 x t \<notin> P"
  shows "returns_to P x"
proof -
  from return_time[OF ret]
  have rt: "0 < return_time P (flow0 x t)" "flow0 (flow0 x t) (return_time P (flow0 x t)) \<in> P"
    and "0 < s \<Longrightarrow> s < return_time P (flow0 x t) \<Longrightarrow> flow0 (flow0 x t) s \<notin> P" for s
    by auto
  let ?t = "t + return_time P  (flow0 x t)"
  show ?thesis
  proof (rule returns_toI[of ?t])
    show "0 < ?t" by (auto intro!: add_nonneg_pos rt \<open>t \<ge> 0\<close>)
    show "?t \<in> existence_ivl0 x"
      by (intro existence_ivl_trans return_time_exivl assms)
    have "flow0 x (t + return_time P (flow0 x t)) = flow0 (flow0 x t) (return_time P (flow0 x t))"
      by (intro flow_trans assms return_time_exivl)
    also have "\<dots> \<in> P"
      by (rule return_time_returns[OF ret])
    finally show "flow0 x (t + return_time P (flow0 x t)) \<in> P" .
    show "closed P" by fact
    show "\<forall>\<^sub>F t in at_right 0. flow0 x t \<notin> P" by fact
  qed
qed

lemma return_time_gt:
  assumes ret: "returns_to P x" "closed P"
  assumes flow_not: "\<And>s. 0 < s \<Longrightarrow> s \<le> t \<Longrightarrow> flow0 x s \<notin> P"
  shows "t < return_time P x"
  using flow_not[of "return_time P x"] return_time_pos[OF ret] return_time_returns[OF ret] by force

lemma return_time_le:
  assumes ret: "returns_to P x" "closed P"
  assumes flow_not: "flow0 x t \<in> P" "t > 0"
  shows "return_time P x \<le> t"
  using return_time_least[OF assms(1,2), of t] flow_not
  by force

lemma returns_to_laterI:
  assumes ret: "returns_to P x" "closed P"
  assumes t: "t > 0" "t \<in> existence_ivl0 x"
  assumes flow_not: "\<And>s. 0 < s \<Longrightarrow> s \<le> t \<Longrightarrow> flow0 x s \<notin> P"
  shows "returns_to P (flow0 x t)"
  apply (rule returns_toI[of "return_time P x - t"])
  subgoal using flow_not by (auto intro!: return_time_gt ret)
  subgoal by (auto intro!: existence_ivl_trans' return_time_exivl ret t)
  subgoal by (subst flow_trans[symmetric])
      (auto intro!: existence_ivl_trans' return_time_exivl ret t return_time_returns)
  subgoal
  proof -
    have "\<forall>\<^sub>F y in nhds 0. y \<in> existence_ivl0 (flow0 x t)"
      apply (rule eventually_nhds_in_open[OF open_existence_ivl[of "flow0 x t"] existence_ivl_zero])
      apply (rule flow_in_domain)
      apply fact
      done
    then have "\<forall>\<^sub>F s in at_right 0. s \<in> existence_ivl0 (flow0 x t)"
      unfolding eventually_at_filter
      by eventually_elim auto
    moreover
    have "\<forall>\<^sub>F s in at_right 0. t + s < return_time P x"
      using return_time_gt[OF ret flow_not, of t]
      by (auto simp: eventually_at_right[OF zero_less_one] intro!: exI[of _ "return_time P x - t"])
    moreover
    have "\<forall>\<^sub>F s in at_right 0. 0 < t + s"
      by (metis (mono_tags) eventually_at_rightI greaterThanLessThan_iff pos_add_strict t(1))
    ultimately show ?thesis
      apply eventually_elim
      apply (subst flow_trans[symmetric])
      using return_time_least[OF ret]
      by (auto intro!: existence_ivl_trans' t)
    qed
  subgoal by fact
  done

lemma never_returns:
  assumes "\<not>returns_to P x"
  assumes "closed P" "t \<ge> 0" "t \<in> existence_ivl0 x"
  assumes ev: "\<forall>\<^sub>F t in at_right 0. flow0 x t \<notin> P"
  shows "\<not>returns_to P (flow0 x t)"
  using returns_to_earlierI[OF _ assms(2-5)] assms(1)
  by blast

lemma return_time_eqI:
  assumes "closed P"
    and t_pos: "t > 0"
    and ex: "t \<in> existence_ivl0 x"
    and ret: "flow0 x t \<in> P"
    and least: "\<And>s. 0 < s \<Longrightarrow> s < t \<Longrightarrow> flow0 x s \<notin> P"
  shows "return_time P x = t"
proof -
  from least t_pos have "\<forall>\<^sub>F t in at_right 0. flow0 x t \<notin> P"
    by (auto simp: eventually_at_right[OF zero_less_one])
  then have "returns_to P x"
    by (auto intro!: returns_toI[of t] assms)
  then show ?thesis
    using least
    by (auto simp: return_time_def t_pos ex ret
        intro!: some1_equality[OF return_time_ex1[OF \<open>returns_to _ _\<close> \<open>closed _\<close>]])
qed

lemma return_time_step:
  assumes "returns_to P (flow0 x t)"
  assumes "closed P"
  assumes flow_not: "\<And>s. 0 < s \<Longrightarrow> s \<le> t \<Longrightarrow> flow0 x s \<notin> P"
  assumes t: "t > 0" "t \<in> existence_ivl0 x"
  shows "return_time P (flow0 x t) = return_time P x - t"
proof -
  from flow_not t have "\<forall>\<^sub>F t in at_right 0. flow0 x t \<notin> P"
    by (auto simp: eventually_at_right[OF zero_less_one])
  from returns_to_earlierI[OF assms(1,2) less_imp_le, OF t this]
  have ret: "returns_to P x" .
  from return_time_gt[OF ret \<open>closed P\<close> flow_not]
  have "t < return_time P x" by simp
  moreover
  have "0 < s \<Longrightarrow> s < return_time P x - t \<Longrightarrow> flow0 (flow0 x t) s = flow0 x (t + s)" for s
    using ivl_subset_existence_ivl[OF return_time_exivl[OF ret \<open>closed _\<close>]] t
    by (subst flow_trans) (auto intro!: existence_ivl_trans')
  ultimately show ?thesis
    using flow_not assms(1) ret return_time_least t(1)
    by (auto intro!: return_time_eqI return_time_returns ret
        simp: flow_trans[symmetric] \<open>closed P\<close> t(2) existence_ivl_trans' return_time_exivl)
qed

definition "poincare_map P x = flow0 x (return_time P x)"

lemma poincare_map_step_flow:
  assumes ret: "returns_to P x" "closed P"
  assumes flow_not: "\<And>s. 0 < s \<Longrightarrow> s \<le> t \<Longrightarrow> flow0 x s \<notin> P"
  assumes t: "t > 0" "t \<in> existence_ivl0 x"
  shows "poincare_map P (flow0 x t) = poincare_map P x"
  unfolding poincare_map_def
  apply (subst flow_trans[symmetric])
  subgoal by fact
  subgoal using flow_not by (auto intro!: return_time_exivl returns_to_laterI t ret)
  subgoal
    using flow_not
    by (subst return_time_step) (auto intro!: return_time_exivl returns_to_laterI t ret)
  done

lemma poincare_map_returns:
  assumes "returns_to P x" "closed P"
  shows "poincare_map P x \<in> P"
  by (auto intro!: return_time_returns assms simp: poincare_map_def)

lemma poincare_map_onto:
  assumes "closed P"
  assumes "0 < t" "t \<in> existence_ivl0 x" "\<forall>\<^sub>F t in at_right 0. flow0 x t \<notin> P"
  assumes "flow0 x t \<in> P"
  shows "poincare_map P x \<in> flow0 x ` {0 <.. t} \<inter> P"
proof (rule IntI)
  have "returns_to P x"
    by (rule returns_toI) (rule assms)+
  then have "return_time P x \<in> {0<..t}"
    by (auto intro!: return_time_pos assms return_time_le)
  then show "poincare_map P x \<in> flow0 x ` {0<..t}"
    by (auto simp: poincare_map_def)
  show "poincare_map P x \<in> P"
    by (auto intro!: poincare_map_returns \<open>returns_to _ _\<close> \<open>closed _\<close>)
qed

end


lemma isCont_blinfunD:
  fixes f'::"'a::metric_space \<Rightarrow> 'b::real_normed_vector \<Rightarrow>\<^sub>L 'c::real_normed_vector"
  assumes "isCont f' a"
  assumes "0 < e"
  shows "\<exists>d>0. \<forall>x. dist a x < d \<longrightarrow> onorm (\<lambda>v. blinfun_apply (f' x) v - blinfun_apply (f' a) v) < e"
  using assms
  unfolding isCont_def
  by (force dest!: tendstoD[OF _ \<open>0 < e\<close>]
      simp: eventually_at dist_commute dist_norm norm_blinfun.rep_eq
        blinfun.bilinear_simps[symmetric])

proposition has_derivative_locally_injective_blinfun:
  fixes f :: "'n::euclidean_space \<Rightarrow> 'm::euclidean_space"
    and f'::"'n \<Rightarrow> 'n \<Rightarrow>\<^sub>L 'm"
    and g'::"'m \<Rightarrow>\<^sub>L 'n"
  assumes "a \<in> s"
      and "open s"
      and g': "g' o\<^sub>L (f' a) = 1\<^sub>L"
      and f': "\<And>x. x \<in> s \<Longrightarrow> (f has_derivative f' x) (at x)"
      and c: "isCont f' a"
    obtains r where "r > 0" "ball a r \<subseteq> s" "inj_on f (ball a r)"
proof -
  have bl: "bounded_linear (blinfun_apply g')"
    by (auto simp: blinfun.bounded_linear_right)
  from g' have g': "blinfun_apply g' \<circ> blinfun_apply (f' a) = id"
    by transfer (simp add: id_def)
  from has_derivative_locally_injective[OF \<open>a \<in> s\<close> \<open>open s\<close> bl g' f' isCont_blinfunD[OF c]]
  obtain r where "0 < r" "ball a r \<subseteq> s" "inj_on f (ball a r)"
    by auto
  then show ?thesis ..
qed

lift_definition embed1_blinfun::"'a::real_normed_vector \<Rightarrow>\<^sub>L ('a*'b::real_normed_vector)" is "\<lambda>x. (x, 0)"
  by standard (auto intro!: exI[where x=1])
lemma blinfun_apply_embed1_blinfun[simp]: "blinfun_apply embed1_blinfun x = (x, 0)"
  by transfer simp

lift_definition embed2_blinfun::"'a::real_normed_vector \<Rightarrow>\<^sub>L ('b::real_normed_vector*'a)" is "\<lambda>x. (0, x)"
  by standard (auto intro!: exI[where x=1])
lemma blinfun_apply_embed2_blinfun[simp]: "blinfun_apply embed2_blinfun x = (0, x)"
  by transfer simp

lemma blinfun_inverseD: "f o\<^sub>L f' = 1\<^sub>L \<Longrightarrow> f (f' x) = x"
  apply transfer
  unfolding o_def
  by meson

lemmas continuous_on_open_vimageI = continuous_on_open_vimage[THEN iffD1, rule_format]
lemmas continuous_on_closed_vimageI = continuous_on_closed_vimage[THEN iffD1, rule_format]

lemma ball_times_subset: "ball a (c/2) \<times> ball b (c/2) \<subseteq> ball (a, b) c"
proof -
  {
    fix a' b'
    have "sqrt ((dist a a')\<^sup>2 + (dist b b')\<^sup>2) \<le> dist a a' + dist b b'"
      by (rule real_le_lsqrt) (auto simp: power2_eq_square algebra_simps)
    also assume "a' \<in> ball a (c / 2)"
    then have "dist a a' < c / 2" by (simp add:)
    also assume "b' \<in> ball b (c / 2)"
    then have "dist b b' < c / 2" by (simp add:)
    finally have "sqrt ((dist a a')\<^sup>2 + (dist b b')\<^sup>2) < c"
      by simp
  } thus ?thesis by (auto simp: dist_prod_def mem_cball)
qed

lemma linear_inverse_blinop_lemma:
  fixes w::"'a::{banach, perfect_space} blinop"
  assumes "norm w < 1"
  shows
    "summable (\<lambda>n. (-1)^n *\<^sub>R w^n)" (is ?C)
    "(\<Sum>n. (-1)^n *\<^sub>R w^n) * (1 + w) = 1" (is ?I1)
    "(1 + w) * (\<Sum>n. (-1)^n *\<^sub>R w^n) = 1" (is ?I2)
    "norm ((\<Sum>n. (-1)^n *\<^sub>R w^n) - 1 + w) \<le> (norm w)\<^sup>2/(1 - norm (w))" (is ?L)
proof -
  have "summable (\<lambda>n. norm w ^ n)"
    apply (rule summable_geometric)
    using assms by auto
  then have "summable (\<lambda>n. norm (w ^ n))"
    by (rule summable_comparison_test'[where N=0]) (auto intro!: norm_power_ineq)
  then show ?C
    by (rule summable_comparison_test'[where N=0]) (auto simp: norm_power )
  {
    fix N
    have 1: "(1 + w) * sum (\<lambda>n. (-1)^n *\<^sub>R w^n) {..<N} = sum (\<lambda>n. (-1)^n *\<^sub>R w^n) {..<N} * (1 + w)"
      by (auto simp: algebra_simps sum_distrib_left sum_distrib_right sum.distrib power_commutes)
    also have "\<dots> = sum (\<lambda>n. (-1)^n *\<^sub>R w^n - (-1)^Suc n *\<^sub>R w^ Suc n) {..<N}"
      by (auto simp: algebra_simps sum_distrib_left sum_distrib_right sum.distrib power_commutes)
    also have "\<dots> = 1 - (-1)^N *\<^sub>R w^N"
      by (subst sum_lessThan_telescope') (auto simp: algebra_simps)
    finally have "(1 + w) * (\<Sum>n<N. (- 1) ^ n *\<^sub>R w ^ n) = 1 - (- 1) ^ N *\<^sub>R w ^ N" .
    note 1 this
  } note nu = this
  show "?I1"
    apply (subst suminf_mult2, fact)
    apply (subst suminf_eq_lim)
    apply (subst sum_distrib_right[symmetric])
    apply (rule limI)
    apply (subst nu(1)[symmetric])
    apply (subst nu(2))
    apply (rule tendsto_eq_intros)
      apply (rule tendsto_intros)
     apply (rule tendsto_norm_zero_cancel)
     apply auto
    apply (rule Lim_transform_bound[where g="\<lambda>i. norm w ^ i"])
     apply (rule eventuallyI)
    apply simp apply (rule norm_power_ineq)
    apply (auto intro!: LIMSEQ_power_zero assms)
    done
  show "?I2"
    apply (subst suminf_mult[symmetric], fact)
    apply (subst suminf_eq_lim)
    apply (subst sum_distrib_left[symmetric])
    apply (rule limI)
    apply (subst nu(2))
    apply (rule tendsto_eq_intros)
      apply (rule tendsto_intros)
     apply (rule tendsto_norm_zero_cancel)
     apply auto
    apply (rule Lim_transform_bound[where g="\<lambda>i. norm w ^ i"])
     apply (rule eventuallyI)
    apply simp apply (rule norm_power_ineq)
    apply (auto intro!: LIMSEQ_power_zero assms)
    done
  have *: "(\<Sum>n. (- 1) ^ n *\<^sub>R w ^ n) - 1 + w = (w\<^sup>2 * (\<Sum>n. (- 1) ^ n *\<^sub>R w ^ n))"
    apply (subst suminf_split_initial_segment[where k=2], fact)
    apply (subst suminf_mult[symmetric], fact)
    by (auto simp: power2_eq_square algebra_simps eval_nat_numeral)
  also have "norm \<dots> \<le> (norm w)\<^sup>2 / (1 - norm w)"
    apply (rule order_trans[OF norm_mult_ineq])
    apply (subst divide_inverse)
    apply (rule mult_mono)
       apply (auto simp: norm_power_ineq inverse_eq_divide assms )
    apply (rule order_trans[OF summable_norm])
     apply auto
     apply fact
    apply (rule order_trans[OF suminf_le])
       apply (rule allI) apply (rule norm_power_ineq)
      apply fact
     apply fact
    by (auto simp: suminf_geometric assms)
  finally show ?L .
qed

lemma linear_inverse_blinfun_lemma:
  fixes w::"'a \<Rightarrow>\<^sub>L 'a::{banach, perfect_space}"
  assumes "norm w < 1"
  obtains I where
    "I o\<^sub>L (1\<^sub>L + w) = 1\<^sub>L" "(1\<^sub>L + w) o\<^sub>L I = 1\<^sub>L"
    "norm (I - 1\<^sub>L + w) \<le> (norm w)\<^sup>2/(1 - norm (w))"
proof -
  define v::"'a blinop" where "v = Blinop w"
  have "norm v = norm w"
    unfolding v_def
    apply transfer
    by (simp add: bounded_linear_Blinfun_apply norm_blinfun.rep_eq)
  with assms have "norm v < 1" by simp
  from linear_inverse_blinop_lemma[OF this]
  have v: "(\<Sum>n. (- 1) ^ n *\<^sub>R v ^ n) * (1 + v) = 1"
    "(1 + v) * (\<Sum>n. (- 1) ^ n *\<^sub>R v ^ n) = 1"
    "norm ((\<Sum>n. (- 1) ^ n *\<^sub>R v ^ n) - 1 + v) \<le> (norm v)\<^sup>2 / (1 - norm v)"
    by auto
  define J::"'a blinop" where "J = (\<Sum>n. (- 1) ^ n *\<^sub>R v ^ n)"
  define I::"'a \<Rightarrow>\<^sub>L 'a" where "I = Blinfun J"
  have "Blinfun (blinop_apply J) - 1\<^sub>L + w = Rep_blinop (J - 1 + Blinop (blinfun_apply w))"
    by transfer' (auto simp: blinfun_apply_inverse)
  then have ne: "norm (Blinfun (blinop_apply J) - 1\<^sub>L + w) =
    norm (J - 1 + Blinop (blinfun_apply w))"
    by (auto simp: norm_blinfun_def norm_blinop_def)
  from v have
    "I o\<^sub>L (1\<^sub>L + w) = 1\<^sub>L" "(1\<^sub>L + w) o\<^sub>L I = 1\<^sub>L"
    "norm (I - 1\<^sub>L + w) \<le> (norm w)\<^sup>2/(1 - norm (w))"
      apply (auto simp: I_def J_def[symmetric])
    unfolding v_def
      apply (auto simp: blinop.bounded_linear_right bounded_linear_Blinfun_apply
        intro!: blinfun_eqI)
    subgoal by transfer
       (auto simp: blinfun_ext blinfun.bilinear_simps bounded_linear_Blinfun_apply)
    subgoal
      by transfer (auto simp: Transfer.Rel_def
          blinfun_ext blinfun.bilinear_simps bounded_linear_Blinfun_apply)
    subgoal
      apply (auto simp: ne)
      apply transfer
      by (auto simp: norm_blinfun_def bounded_linear_Blinfun_apply)
    done
  then show ?thesis ..
qed

definition "invertibles_blinfun = {w. \<exists>wi. w o\<^sub>L wi = 1\<^sub>L \<and> wi o\<^sub>L w = 1\<^sub>L}"

lemma blinfun_inverse_open:\<comment> \<open>8.3.2 in Dieudonne, TODO: add continuity and derivative\<close>
  shows "open (invertibles_blinfun::
      ('a::{banach, perfect_space} \<Rightarrow>\<^sub>L 'b::banach) set)"
proof (rule openI)
  fix u0::"'a \<Rightarrow>\<^sub>L 'b"
  assume "u0 \<in> invertibles_blinfun"
  then obtain u0i where u0i: "u0 o\<^sub>L u0i = 1\<^sub>L" "u0i o\<^sub>L u0 = 1\<^sub>L"
    by (auto simp: invertibles_blinfun_def)
  then have [simp]: "u0i \<noteq> 0"
    apply (auto)
    by (metis one_blinop.abs_eq zero_blinop.abs_eq zero_neq_one)
  let ?e = "inverse (norm u0i)"
  show "\<exists>e>0. ball u0 e \<subseteq> invertibles_blinfun"
    apply (clarsimp intro!: exI[where x = ?e] simp: invertibles_blinfun_def)
    subgoal premises prems for u0s
    proof -
      define s where "s = u0s - u0"
      have u0s: "u0s = u0 + s"
        by (auto simp: s_def)
      have "norm (u0i o\<^sub>L s) < 1"
        using prems by (auto simp: dist_norm u0s
        divide_simps ac_simps intro!: le_less_trans[OF norm_blinfun_compose])
      from linear_inverse_blinfun_lemma[OF this]
      obtain I where I:
        "I o\<^sub>L 1\<^sub>L + (u0i o\<^sub>L s) = 1\<^sub>L"
        "1\<^sub>L + (u0i o\<^sub>L s) o\<^sub>L I = 1\<^sub>L"
        "norm (I - 1\<^sub>L + (u0i o\<^sub>L s)) \<le> (norm (u0i o\<^sub>L s))\<^sup>2 / (1 - norm (u0i o\<^sub>L s))"
        by auto
      have u0s_eq: "u0s = u0 o\<^sub>L (1\<^sub>L + (u0i o\<^sub>L s))"
        using u0i
        by (auto simp: s_def blinfun.bilinear_simps blinfun_ext)
      show ?thesis
        apply (rule exI[where x="I o\<^sub>L u0i"])
        using I u0i
        apply (auto simp: u0s_eq)
        by (auto simp:  algebra_simps blinfun_ext blinfun.bilinear_simps)
    qed
    done
  qed

lemma blinfun_compose_assoc[ac_simps]: "a o\<^sub>L b o\<^sub>L c = a o\<^sub>L (b o\<^sub>L c)"
  by (auto intro!: blinfun_eqI)

text \<open>TODO: move @{thm norm_minus_cancel} to class!\<close>
lemma (in real_normed_vector) norm_minus_cancel [simp]: "norm (- x) = norm x"
proof -
  have scaleR_minus_left: "- a *\<^sub>R x = - (a *\<^sub>R x)" for a x
  proof -
    have "\<forall>x1 x2. (x2::real) + x1 = x1 + x2"
      by auto
    then have f1: "\<forall>r ra a. (ra + r) *\<^sub>R (a::'a) = r *\<^sub>R a + ra *\<^sub>R a"
      using local.scaleR_add_left by presburger
    have f2: "a + a = 2 * a"
      by force
    have f3: "2 * a + - 1 * a = a"
      by auto
    have "- a = - 1 * a"
      by auto
    then show ?thesis
      using f3 f2 f1 by (metis local.add_minus_cancel local.add_right_imp_eq)
  qed
  have "norm (- x) = norm (scaleR (- 1) x)"
    by (simp only: scaleR_minus_left scaleR_one)
  also have "\<dots> = \<bar>- 1\<bar> * norm x"
    by (rule norm_scaleR)
  finally show ?thesis by simp
qed

text \<open>TODO: move @{thm norm_minus_commute} to class!\<close>
lemma (in real_normed_vector) norm_minus_commute: "norm (a - b) = norm (b - a)"
proof -
  have "norm (- (b - a)) = norm (b - a)"
    by (rule norm_minus_cancel)
  then show ?thesis by simp
qed

instance euclidean_space \<subseteq> banach
  by standard

lemma blinfun_apply_Pair_split:
  "blinfun_apply g (a, b) = blinfun_apply g (a, 0) + blinfun_apply g (0, b)"
  unfolding blinfun.bilinear_simps[symmetric] by simp

lemma blinfun_apply_Pair_add2: "blinfun_apply f (0, a + b) = blinfun_apply f (0, a) + blinfun_apply f (0, b)"
  unfolding blinfun.bilinear_simps[symmetric] by simp

lemma blinfun_apply_Pair_add1: "blinfun_apply f (a + b, 0) = blinfun_apply f (a, 0) + blinfun_apply f (b, 0)"
  unfolding blinfun.bilinear_simps[symmetric] by simp

lemma blinfun_apply_Pair_minus2: "blinfun_apply f (0, a - b) = blinfun_apply f (0, a) - blinfun_apply f (0, b)"
  unfolding blinfun.bilinear_simps[symmetric] by simp

lemma blinfun_apply_Pair_minus1: "blinfun_apply f (a - b, 0) = blinfun_apply f (a, 0) - blinfun_apply f (b, 0)"
  unfolding blinfun.bilinear_simps[symmetric] by simp

lemma implicit_function_theorem:
  fixes f::"'a::euclidean_space * 'b::euclidean_space \<Rightarrow> 'c::euclidean_space"\<comment> \<open>TODO: generalize?!\<close>
  assumes [derivative_intros]: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative blinfun_apply (f' x)) (at x)"
  assumes S: "(x, y) \<in> S" "open S"
  assumes "DIM('c) \<le> DIM('b)"
  assumes f'C: "isCont f' (x, y)"
  assumes "f (x, y) = 0"
  assumes T2: "T o\<^sub>L (f' (x, y) o\<^sub>L embed2_blinfun) = 1\<^sub>L"
  assumes T1: "(f' (x, y) o\<^sub>L embed2_blinfun) o\<^sub>L T = 1\<^sub>L"\<comment> \<open>TODO: reduce?!\<close>
  obtains u e r
  where "f (x, u x) = 0" "u x = y"
    "\<And>s. s \<in> cball x e \<Longrightarrow> f (s, u s) = 0"
    "continuous_on (cball x e) u"
    "(\<lambda>t. (t, u t)) ` cball x e \<subseteq> S"
    "e > 0"
    "(u has_derivative - T o\<^sub>L f' (x, y) o\<^sub>L embed1_blinfun) (at x)"

    "r > 0"
    "\<And>U v s. v x = y \<Longrightarrow> (\<And>s. s \<in> U \<Longrightarrow> f (s, v s) = 0) \<Longrightarrow> U \<subseteq> cball x e \<Longrightarrow>
      continuous_on U v \<Longrightarrow> s \<in> U \<Longrightarrow> (s, v s) \<in> ball (x, y) r \<Longrightarrow> u s = v s"
proof -
  define H where "H \<equiv> \<lambda>(x, y). (x, f (x, y))"
  define H' where "H' \<equiv> \<lambda>x. (embed1_blinfun o\<^sub>L fst_blinfun) + (embed2_blinfun o\<^sub>L (f' x))"
  have f'_inv: "f' (x, y) o\<^sub>L embed2_blinfun \<in> invertibles_blinfun"
    using T1 T2 by (auto simp: invertibles_blinfun_def ac_simps intro!: exI[where x=T])
  from openE[OF blinfun_inverse_open this]
  obtain d0 where e0: "0 < d0"
    "ball (f' (x, y) o\<^sub>L embed2_blinfun) d0 \<subseteq> invertibles_blinfun"
    by auto
  have "isCont (\<lambda>s. f' s o\<^sub>L embed2_blinfun) (x, y)"
    by (auto intro!: continuous_intros f'C)
  from this[unfolded isCont_def, THEN tendstoD, OF \<open>0 < d0\<close>]
  have "\<forall>\<^sub>F s in at (x, y). f' s o\<^sub>L embed2_blinfun \<in> invertibles_blinfun"
    apply eventually_elim
    using e0 by (auto simp: subset_iff dist_commute)
  then obtain e0 where "e0 > 0"
      "xa \<noteq> (x, y) \<Longrightarrow> dist xa (x, y) < e0 \<Longrightarrow>
        f' xa o\<^sub>L embed2_blinfun \<in> invertibles_blinfun" for xa
    unfolding eventually_at
    by auto
  then have e0: "e0 > 0"
    "dist xa (x, y) < e0 \<Longrightarrow> f' xa o\<^sub>L embed2_blinfun \<in> invertibles_blinfun" for xa
    apply -
    subgoal by simp
    using f'_inv
    apply (cases "xa = (x, y)")
    by auto

  have H': "x \<in> S \<Longrightarrow> (H has_derivative H' x) (at x)" for x
    unfolding H_def  H'_def
    by (auto intro!: derivative_eq_intros ext simp: blinfun.bilinear_simps)
  have cH': "isCont H' (x, y)"
    unfolding H'_def
    by (auto intro!: continuous_intros assms)
  have linear_H': "\<And>s. s \<in> S \<Longrightarrow> linear (H' s)"
    using H' assms(2) has_derivative_linear by blast
  have *: "blinfun_apply T (blinfun_apply (f' (x, y)) (0, b)) = b" for b
    using blinfun_inverseD[OF T2, of b]
    by simp
  have "inj (f' (x, y) o\<^sub>L embed2_blinfun)"
    by (metis (no_types, lifting) "*" blinfun_apply_blinfun_compose embed2_blinfun.rep_eq injI)
  then have [simp]: "blinfun_apply (f' (x, y)) (0, b) = 0 \<Longrightarrow> b = 0" for b
    apply (subst (asm) linear_injective_0)
    subgoal
      apply (rule bounded_linear.linear)
      apply (rule blinfun.bounded_linear_right)
      done
    subgoal by simp
    done
  have "inj (H' (x, y))"
    apply (subst linear_injective_0)
     apply (rule linear_H')
     apply fact
    apply (auto simp: H'_def blinfun.bilinear_simps zero_prod_def)
    done
  define Hi where "Hi = (embed1_blinfun o\<^sub>L fst_blinfun) + ((embed2_blinfun o\<^sub>L T o\<^sub>L (snd_blinfun - (f' (x, y) o\<^sub>L embed1_blinfun o\<^sub>L fst_blinfun))))"
  have Hi': "(\<lambda>u. snd (blinfun_apply Hi (u, 0))) = - T o\<^sub>L f' (x, y) o\<^sub>L embed1_blinfun"
    by (auto simp: Hi_def blinfun.bilinear_simps)
  have Hi: "Hi o\<^sub>L H' (x, y) = 1\<^sub>L"
    apply (auto simp: H'_def fun_eq_iff blinfun.bilinear_simps Hi_def
        intro!: ext blinfun_eqI)
    apply (subst blinfun_apply_Pair_split)
    by (auto simp: * blinfun.bilinear_simps)
  from has_derivative_locally_injective_blinfun[OF S this H' cH']
  obtain r0 where r0: "0 < r0" "ball (x, y) r0 \<subseteq> S" and inj: "inj_on H (ball (x, y) r0)"
    by auto
  define r where "r = min r0 e0"
  have r: "0 < r" "ball (x, y) r \<subseteq> S" and inj: "inj_on H (ball (x, y) r)"
    and r_inv: "\<And>s. s \<in> ball (x, y) r \<Longrightarrow> f' s o\<^sub>L embed2_blinfun \<in> invertibles_blinfun"
    subgoal using e0 r0 by (auto simp: r_def)
    subgoal using e0 r0 by (auto simp: r_def)
    subgoal using inj apply (rule inj_on_subset)
      using e0 r0 by (auto simp: r_def)
    subgoal for s
      using e0 r0 by (auto simp: r_def dist_commute)
    done
  obtain i::'a where "i \<in> Basis"
    using nonempty_Basis by blast
  define undef where "undef \<equiv> (x, y) + r *\<^sub>R (i, 0)"\<comment> \<open>really??\<close>
  have ud: "\<not> dist (x, y) undef < r"
    using \<open>r > 0\<close> \<open>i \<in> Basis\<close> by (auto simp: undef_def dist_norm)
  define G where "G \<equiv> the_inv_into (ball (x, y) r) H"
  {
    fix u v
    assume [simp]: "(u, v) \<in> H ` ball (x, y) r"
    note [simp] = inj
    have "(u, v) = H (G (u, v))"
      unfolding G_def
      by (subst f_the_inv_into_f[where f=H]) auto
    moreover have "\<dots> = H (G (u, v))"
      by (auto simp: G_def)
    moreover have "\<dots> = (fst (G (u, v)), f (G (u, v)))"
      by (auto simp: H_def split_beta')
    ultimately have "u = fst (G (u, v))" "v = f (G (u, v))" by simp_all
    then have "f (u, snd (G(u, v))) = v" "u = fst (G (u, v))"
      by (metis prod.collapse)+
  } note uvs = this
  note uv = uvs(1)
  moreover
  have "f (x, snd (G (x, 0))) = 0"
    apply (rule uv)
    by (metis (mono_tags, lifting) H_def assms(6) case_prod_beta' centre_in_ball fst_conv image_iff r(1) snd_conv)
  moreover
  have cH: "continuous_on S H"
    apply (rule has_derivative_continuous_on)
    apply (subst at_within_open)
      apply (auto intro!: H' assms)
    done
  have inj2: "inj_on H (ball (x, y) (r / 2))"
    apply (rule inj_on_subset, rule inj)
    using r by auto
  have oH: "open (H ` ball (x, y) (r/2))"
    apply (rule invariance_of_domain_gen)
       apply (auto simp: assms inj)
    apply (rule continuous_on_subset)
      apply fact
    using r
     apply auto
    using inj2 apply simp
    done
  have "(x, f (x, y)) \<in> H ` ball (x, y) (r/2)"
    using \<open>r > 0\<close> by (auto simp: H_def)
  from open_contains_cball[THEN iffD1, OF oH, rule_format, OF this]
  obtain e' where e': "e' > 0" "cball (x, f (x, y)) e' \<subseteq> H ` ball (x, y) (r/2)"
    by auto

  have inv_subset: "the_inv_into (ball (x, y) r) H a = the_inv_into R H a"
    if "a \<in> H ` R" "R \<subseteq> (ball (x, y) r)"
    for a R
    apply (rule the_inv_into_f_eq[OF inj])
     apply (rule f_the_inv_into_f)
      apply (rule inj_on_subset[OF inj])
      apply fact
     apply fact
    apply (rule the_inv_into_into)
      apply (rule inj_on_subset[OF inj])
      apply fact
     apply fact
    apply (rule order_trans)
     apply fact
    using r apply auto
    done
  have GH: "G (H z) = z" if "dist (x, y) z < r" for z
    by (auto simp: G_def the_inv_into_f_f inj that)
  define e where "e = min (e' / 2) e0"
  define r2 where "r2 = r / 2"
  have r2: "r2 > 0" "r2 < r"
    using \<open>r > 0\<close> by (auto simp: r2_def)
  have "e > 0" using e' e0 by (auto simp: e_def)
  from cball_times_subset[of "x" e' "f (x, y)"] e'
  have "cball x e \<times> cball (f (x, y)) e \<subseteq> H ` ball (x, y) (r/2)"
    by (force simp: e_def)
  then have e_r_subset: "z \<in> cball x e \<Longrightarrow> (z, 0) \<in> H ` ball (x, y) (r/2)" for z
    using \<open>0 < e\<close> assms(6)
    by (auto simp: H_def subset_iff)
  have u0: "(u, 0) \<in> H ` ball (x, y) r" if "u \<in> cball x e" for u
    apply (rule rev_subsetD)
     apply (rule e_r_subset)
     apply fact
    unfolding r2_def using r2 by auto
  have G_r: "G (u, 0) \<in> ball (x, y) r" if "u \<in> cball x e" for u
    unfolding G_def
    apply (rule the_inv_into_into)
      apply fact
     apply (auto)
    apply (rule u0, fact)
    done
  note e_r_subset
  ultimately have G2:
    "f (x, snd (G (x, 0))) = 0" "snd (G (x, 0)) = y"
    "\<And>u. u \<in> cball x e \<Longrightarrow> f (u, snd (G (u, 0))) = 0"
    "continuous_on (cball x e) (\<lambda>u. snd (G (u, 0)))"
    "(\<lambda>t. (t, snd (G (t, 0)))) ` cball x e \<subseteq> S"
    "e > 0"
    "((\<lambda>u. snd (G (u, 0))) has_derivative (\<lambda>u. snd (Hi (u, 0)))) (at x)"
       apply (auto simp: G_def split_beta'
        intro!: continuous_intros continuous_on_compose2[OF cH])
    subgoal premises prems
    proof -
      have "the_inv_into (ball (x, y) r) H (x, 0) = (x, y)"
        apply (rule the_inv_into_f_eq)
          apply fact
         by (auto simp: H_def assms \<open>r > 0\<close>)
       then show ?thesis
         by auto
    qed
    using r2(2) r2_def apply fastforce
    apply (subst continuous_on_cong[OF refl])
     apply (rule inv_subset[where R="cball (x, y) r2"])
    subgoal
      using r2
      apply auto
      using r2_def by force
    subgoal using r2 by (force simp:)
    subgoal
      apply (rule continuous_on_compose2[OF continuous_on_inv_into])
      using r(2) r2(2)
        apply (auto simp: r2_def[symmetric]
          intro!: continuous_on_compose2[OF cH] continuous_intros)
       apply (rule inj_on_subset)
        apply (rule inj)
      using r(2) r2(2) apply force
      apply force
      done
    subgoal premises prems for u
    proof -
      from prems have u: "u \<in> cball x e" by auto
      note G_r[OF u]
      also have "ball (x, y) r \<subseteq> S"
        using r by simp
      finally have "(G (u, 0)) \<in> S" .
      then show ?thesis
        unfolding G_def[symmetric]
        using uvs(2)[OF u0, OF u]
        by (metis prod.collapse)
    qed
    subgoal using \<open>e > 0\<close> by simp
    subgoal premises prems
    proof -
      have "(x, y) \<in> cball (x, y) r2"
        using r2
        by auto
      moreover
      have "H (x, y) \<in> interior (H ` cball (x, y) r2)"
        apply (rule interiorI[OF oH])
        using r2 by (auto simp: r2_def)
      moreover
      have "cball (x, y) r2 \<subseteq> S"
        using r r2 by auto
      moreover have "\<And>z. z \<in> cball (x, y) r2 \<Longrightarrow> G (H z) = z"
        using r2 by (auto intro!: GH)
      ultimately have "(G has_derivative Hi) (at (H (x, y)))"
      proof (rule has_derivative_inverse[where g = G and f = H,
              OF compact_cball _ _ continuous_on_subset[OF cH] _ H' _ _])
        show "blinfun_apply Hi \<circ> blinfun_apply (H' (x, y)) = id"
          using Hi by transfer auto
      qed (use S blinfun.bounded_linear_right in auto)
      then have g': "(G has_derivative Hi) (at (x, 0))"
        by (auto simp: H_def assms)
      show ?thesis
        unfolding G_def[symmetric] H_def[symmetric]
        apply (auto intro!: derivative_eq_intros)
         apply (rule has_derivative_compose[where g=G and f="\<lambda>x. (x, 0)"])
         apply (auto intro!: g' derivative_eq_intros)
        done
    qed
    done
  moreover
  note \<open>r > 0\<close>
  moreover
  define u where "u \<equiv> \<lambda>x. snd (G (x, 0))"
  have local_unique: "u s = v s"
    if solves: "(\<And>s. s \<in> U \<Longrightarrow> f (s, v s) = 0)"
    and i: "v x = y"
    and v: "continuous_on U v"
    and s: "s \<in> U"
    and s': "(s, v s) \<in> ball (x, y) r"
    and U: "U \<subseteq> cball x e"
    for U v s
  proof -
    have H_eq: "H (s, v s) = H (s, u s)"
      apply (auto simp: H_def solves[OF s])
      unfolding u_def
      apply (rule G2)
      apply (rule subsetD; fact)
      done
    have "(s, snd (G (s, 0))) = (G (s, 0))"
      using GH H_def s s' solves by fastforce
    also have "\<dots> \<in> ball (x, y) r"
      unfolding G_def
      apply (rule the_inv_into_into)
        apply fact
       apply (rule u0)
       apply (rule subsetD; fact)
      apply (rule order_refl)
      done
    finally have "(s, u s) \<in> ball (x, y) r" unfolding u_def .
    from inj_onD[OF inj H_eq s' this]
    show "u s = v s"
      by auto
  qed
  ultimately show ?thesis
    unfolding u_def Hi' ..
qed

lemma implicit_function_theorem_unique:
  fixes f::"'a::euclidean_space * 'b::euclidean_space \<Rightarrow> 'c::euclidean_space"\<comment> \<open>TODO: generalize?!\<close>
  assumes f'[derivative_intros]: "\<And>x. x \<in> S \<Longrightarrow> (f has_derivative blinfun_apply (f' x)) (at x)"
  assumes S: "(x, y) \<in> S" "open S"
  assumes D: "DIM('c) \<le> DIM('b)"
  assumes f'C: "continuous_on S f'"
  assumes z: "f (x, y) = 0"
  assumes T2: "T o\<^sub>L (f' (x, y) o\<^sub>L embed2_blinfun) = 1\<^sub>L"
  assumes T1: "(f' (x, y) o\<^sub>L embed2_blinfun) o\<^sub>L T = 1\<^sub>L"\<comment> \<open>TODO: reduce?!\<close>
  obtains u e
  where "f (x, u x) = 0" "u x = y"
    "\<And>s. s \<in> cball x e \<Longrightarrow> f (s, u s) = 0"
    "continuous_on (cball x e) u"
    "(\<lambda>t. (t, u t)) ` cball x e \<subseteq> S"
    "e > 0"
    "(u has_derivative (- T o\<^sub>L f' (x, y) o\<^sub>L embed1_blinfun)) (at x)"
    "\<And>s. s \<in> cball x e \<Longrightarrow> f' (s, u s) o\<^sub>L embed2_blinfun \<in> invertibles_blinfun"
    "\<And>U v s. (\<And>s. s \<in> U \<Longrightarrow> f (s, v s) = 0) \<Longrightarrow>
      u x = v x \<Longrightarrow>
      continuous_on U v \<Longrightarrow> s \<in> U \<Longrightarrow> x \<in> U \<Longrightarrow> U \<subseteq> cball x e \<Longrightarrow> connected U \<Longrightarrow> open U \<Longrightarrow> u s = v s"
proof -
  from T1 T2 have f'I: "f' (x, y) o\<^sub>L embed2_blinfun \<in> invertibles_blinfun"
    by (auto simp: invertibles_blinfun_def)
  from assms have f'Cg: "s \<in> S \<Longrightarrow> isCont f' s" for s
    by (auto simp: continuous_on_eq_continuous_at[OF \<open>open S\<close>])
  then have f'C: "isCont f' (x, y)" by (auto simp: S)
  obtain u e1 r
    where u: "f (x, u x) = 0" "u x = y"
      "\<And>s. s \<in> cball x e1 \<Longrightarrow> f (s, u s) = 0"
      "continuous_on (cball x e1) u"
      "(\<lambda>t. (t, u t)) ` cball x e1 \<subseteq> S"
      "e1 > 0"
    "(u has_derivative (- T o\<^sub>L f' (x, y) o\<^sub>L embed1_blinfun)) (at x)"
    and unique_u: "r > 0"
      "(\<And>v s U. v x = y \<Longrightarrow>
        (\<And>s. s \<in> U \<Longrightarrow> f (s, v s) = 0) \<Longrightarrow>
        continuous_on U v \<Longrightarrow> s \<in> U \<Longrightarrow> U \<subseteq> cball x e1 \<Longrightarrow> (s, v s) \<in> ball (x, y) r \<Longrightarrow> u s = v s)"
    by (rule implicit_function_theorem[OF f' S D f'C z T2 T1]; blast)

  from openE[OF blinfun_inverse_open f'I] obtain d where d:
    "0 < d" "ball (f' (x, y) o\<^sub>L embed2_blinfun) d \<subseteq> invertibles_blinfun"
    by auto
  note [continuous_intros] = continuous_at_compose[OF _ f'Cg, unfolded o_def]
  from \<open>continuous_on _ u\<close>
  have "continuous_on (ball x e1) u" by (rule continuous_on_subset) auto
  then have "\<And>s. s \<in> ball x e1 \<Longrightarrow> isCont u s"
    unfolding continuous_on_eq_continuous_at[OF open_ball] by auto
  note [continuous_intros] = continuous_at_compose[OF _ this, unfolded o_def]
  from assms have f'Ce: "isCont (\<lambda>s. f' (s, u s) o\<^sub>L embed2_blinfun) x"
    by (auto simp: u intro!: continuous_intros)
  from f'Ce[unfolded isCont_def, THEN tendstoD, OF \<open>0 < d\<close>] d
  obtain e0 where "e0 > 0" "\<And>s. s \<noteq> x \<Longrightarrow> s \<in> ball x e0 \<Longrightarrow>
      (f' (s, u s) o\<^sub>L embed2_blinfun) \<in> invertibles_blinfun"
    by (auto simp: eventually_at dist_commute subset_iff u)
  then have e0: "s \<in> ball x e0 \<Longrightarrow> (f' (s, u s) o\<^sub>L embed2_blinfun) \<in> invertibles_blinfun" for s
    by (cases "s = x") (auto simp: f'I \<open>0 < d\<close> u)


  define e where "e = min (e0/2) (e1/2)"
  have e: "f (x, u x) = 0"
      "u x = y"
      "\<And>s. s \<in> cball x e \<Longrightarrow> f (s, u s) = 0"
      "continuous_on (cball x e) u"
      "(\<lambda>t. (t, u t)) ` cball x e \<subseteq> S"
      "e > 0"
      "(u has_derivative (- T o\<^sub>L f' (x, y) o\<^sub>L embed1_blinfun)) (at x)"
      "\<And>s. s \<in> cball x e \<Longrightarrow> f' (s, u s) o\<^sub>L embed2_blinfun \<in> invertibles_blinfun"
    using e0 u \<open>e0 > 0\<close> by (auto simp: e_def intro: continuous_on_subset)

  from u(4) have "continuous_on (ball x e1) u"
    apply (rule continuous_on_subset)
    using \<open>e1 > 0\<close>
    by (auto simp: e_def)
  then have "\<And>s. s \<in> cball x e \<Longrightarrow> isCont u s"
    using \<open>e0 > 0\<close> \<open>e1 > 0\<close>
    unfolding continuous_on_eq_continuous_at[OF open_ball] by (auto simp: e_def Ball_def dist_commute)
  note [continuous_intros] = continuous_at_compose[OF _ this, unfolded o_def]

  have "u s = v s"
    if solves: "(\<And>s. s \<in> U \<Longrightarrow> f (s, v s) = 0)"
    and i: "u x = v x"
    and v: "continuous_on U v"
    and s: "s \<in> U" and U: "x \<in> U" "U \<subseteq> cball x e" "connected U" "open U"
    for U v s
  proof -
    define M where "M = {s \<in> U. u s = v s}"
    have "x \<in> M" using i U by (auto simp: M_def)
    moreover
    have "continuous_on U (\<lambda>s. u s - v s)"
      by (auto intro!: continuous_intros v continuous_on_subset[OF e(4) U(2)])
    from continuous_closedin_preimage[OF this closed_singleton[where a=0]]
    have "closedin (top_of_set U) M"
      by (auto simp: M_def vimage_def Collect_conj_eq)
    moreover
    have "\<And>s. s \<in> U  \<Longrightarrow> isCont v s"
      using v
      unfolding continuous_on_eq_continuous_at[OF \<open>open U\<close>] by auto
    note [continuous_intros] = continuous_at_compose[OF _ this, unfolded o_def]
    {
      fix a assume "a \<in> M"
      then have aU: "a \<in> U" and u_v: "u a = v a"
        by (auto simp: M_def)
      then have a_ball: "a \<in> cball x e" and a_dist: "dist x a \<le> e" using U by auto
      then have a_S: "(a, u a) \<in> S"
        using e by auto
      have fa_z: "f (a, u a) = 0"
        using \<open>a \<in> cball x e\<close> by (auto intro!: e)
      from e(8)[OF \<open>a \<in> cball _ _\<close>]
      obtain Ta where Ta: "Ta o\<^sub>L (f' (a, u a) o\<^sub>L embed2_blinfun) = 1\<^sub>L" "f' (a, u a) o\<^sub>L embed2_blinfun o\<^sub>L Ta = 1\<^sub>L"
        by (auto simp: invertibles_blinfun_def ac_simps)
      obtain u' e' r'
        where "r' > 0" "e' > 0"
        and u': "\<And>v s U. v a = u a \<Longrightarrow>
             (\<And>s. s \<in> U \<Longrightarrow> f (s, v s) = 0) \<Longrightarrow>
             continuous_on U v \<Longrightarrow> s \<in> U \<Longrightarrow> U \<subseteq> cball a e' \<Longrightarrow> (s, v s) \<in> ball (a, u a) r' \<Longrightarrow> u' s = v s"
        by (rule implicit_function_theorem[OF f' a_S \<open>open S\<close> D f'Cg[OF a_S] fa_z Ta]; blast)
      from openE[OF \<open>open U\<close> aU] obtain dU where dU: "dU > 0" "\<And>s. s \<in> ball a dU \<Longrightarrow> s \<in> U"
        by (auto simp: dist_commute subset_iff)

      have v_tendsto: "((\<lambda>s. (s, v s)) \<longlongrightarrow> (a, u a)) (at a)"
        unfolding u_v
        by (subst continuous_at[symmetric]) (auto intro!: continuous_intros aU)
      from tendstoD[OF v_tendsto \<open>0 < r'\<close>, unfolded eventually_at]
      obtain dv where "dv > 0" "s \<noteq> a \<Longrightarrow> dist s a < dv \<Longrightarrow> (s, v s) \<in> ball (a, u a) r'" for s
        by (auto simp: dist_commute)
      then have dv: "dist s a < dv \<Longrightarrow> (s, v s) \<in> ball (a, u a) r'" for s
        by (cases "s = a") (auto simp: u_v \<open>0 < r'\<close>)

      have v_tendsto: "((\<lambda>s. (s, u s)) \<longlongrightarrow> (a, u a)) (at a)"
        using a_dist
        by (subst continuous_at[symmetric]) (auto intro!: continuous_intros)
      from tendstoD[OF v_tendsto \<open>0 < r'\<close>, unfolded eventually_at]
      obtain du where "du > 0" "s \<noteq> a \<Longrightarrow> dist s a < du \<Longrightarrow> (s, u s) \<in> ball (a, u a) r'" for s
        by (auto simp: dist_commute)
      then have du: "dist s a < du \<Longrightarrow> (s, u s) \<in> ball (a, u a) r'" for s
        by (cases "s = a") (auto simp: u_v \<open>0 < r'\<close>)
      {
        fix s assume s: "s \<in> ball a (Min {dU, e', dv, du})"
        let ?U = "ball a (Min {dU, e', dv, du})"
        have balls: "ball a (Min {dU, e', dv, du}) \<subseteq> cball a e'" by auto
        have dsadv: "dist s a < dv"
          using s by (auto simp: dist_commute)
        have dsadu: "dist s a < du"
          using s by (auto simp: dist_commute)
        have U_U: "\<And>s. s \<in> ball a (Min {dU, e', dv, du}) \<Longrightarrow> s \<in> U"
          using dU by auto
        have U_e: "\<And>s. s \<in> ball a (Min {dU, e', dv, du}) \<Longrightarrow> s \<in> cball x e"
          using dU U by (auto simp: dist_commute subset_iff)
        have cv: "continuous_on ?U v"
          using v
          apply (rule continuous_on_subset)
          using dU
          by auto
        have cu: "continuous_on ?U u"
          using e(4)
          apply (rule continuous_on_subset)
          using dU U(2)
          by auto
        from u'[where v=v, OF u_v[symmetric] solves[OF U_U] cv s balls dv[OF dsadv]]
          u'[where v=u, OF refl              e(3)[OF U_e]   cu s balls du[OF dsadu]]
        have "v s = u s" by auto
      } then have "\<exists>dv>0. \<forall>s \<in> ball a dv. v s = u s"
        using \<open>0 < dU\<close> \<open>0 < e'\<close> \<open>0 < dv\<close> \<open>0 < du\<close>
        by (auto intro!: exI[where x="(Min {dU, e', dv, du})"])
    } note ex = this
    have "openin (top_of_set U) M"
      unfolding openin_contains_ball
      apply (rule conjI)
      subgoal using U by (auto simp: M_def)
      apply (auto simp:)
      apply (drule ex)
      apply auto
      subgoal for x d
        by (rule exI[where x=d]) (auto simp: M_def)
      done
    ultimately have "M = U"
      using \<open>connected U\<close>
      by (auto simp: connected_clopen)
    with \<open>s \<in> U\<close> show ?thesis by (auto simp: M_def)
  qed
  from e this
  show ?thesis ..
qed

lemma uniform_limit_compose:
  assumes ul: "uniform_limit T f l F"
  assumes uc: "uniformly_continuous_on S s"
  assumes ev: "\<forall>\<^sub>F x in F. f x ` T \<subseteq> S"
  assumes subs: "l ` T \<subseteq> S"
  shows  "uniform_limit T (\<lambda>i x. s (f i x)) (\<lambda>x. s (l x)) F"
proof (rule uniform_limitI)
  fix e::real assume "e > 0"
  from uniformly_continuous_onE[OF uc \<open>e > 0\<close>]
  obtain d where d: "0 < d" "\<And>t t'. t \<in> S \<Longrightarrow> t' \<in> S \<Longrightarrow> dist t' t < d \<Longrightarrow> dist (s t') (s t) < e"
    by auto
  from uniform_limitD[OF ul \<open>0 < d\<close>] have "\<forall>\<^sub>F n in F. \<forall>x\<in>T. dist (f n x) (l x) < d" .
  then show "\<forall>\<^sub>F n in F. \<forall>x\<in>T. dist (s (f n x)) (s (l x)) < e"
    using ev
    by eventually_elim (use d subs in force)
qed

lemma
  uniform_limit_in_open:
  fixes l::"'a::topological_space\<Rightarrow>'b::heine_borel"
  assumes ul: "uniform_limit T f l (at x)"
  assumes cont: "continuous_on T l"
  assumes compact: "compact T" and T_ne: "T \<noteq> {}"
  assumes B: "open B"
  assumes mem: "l ` T \<subseteq> B"
  shows "\<forall>\<^sub>F y in at x. \<forall>t \<in> T. f y t \<in> B"
proof -
  have l_ne: "l ` T \<noteq> {}" using T_ne by auto
  have "compact (l ` T)"
    by (auto intro!: compact_continuous_image cont compact)
  from compact_in_open_separated[OF l_ne this B mem]
  obtain e where "e > 0" "{x. infdist x (l ` T) \<le> e} \<subseteq> B"
    by auto
  from uniform_limitD[OF ul \<open>0 < e\<close>]
  have "\<forall>\<^sub>F n in at x. \<forall>x\<in>T. dist (f n x) (l x) < e" .
  then show ?thesis
  proof eventually_elim
    case (elim y)
    show ?case
    proof safe
      fix t assume "t \<in> T"
      have "infdist (f y t) (l ` T) \<le> dist (f y t) (l t)"
        by (rule infdist_le) (use \<open>t \<in> T\<close> in auto)
      also have "\<dots> < e" using elim \<open>t \<in> T\<close> by auto
      finally have "infdist (f y t) (l ` T) \<le> e" by simp
      then have "(f y t) \<in> {x. infdist x (l ` T) \<le> e}"
        by (auto )
      also note \<open>\<dots> \<subseteq> B\<close>
      finally show "f y t \<in> B" .
    qed
  qed
qed

lemma
  order_uniform_limitD1:
  fixes l::"'a::topological_space\<Rightarrow>real"\<comment> \<open>TODO: generalize?!\<close>
  assumes ul: "uniform_limit T f l (at x)"
  assumes cont: "continuous_on T l"
  assumes compact: "compact T"
  assumes less: "\<And>t. t \<in> T \<Longrightarrow> l t < b"
  shows "\<forall>\<^sub>F y in at x. \<forall>t \<in> T. f y t < b"
proof cases
  assume ne: "T \<noteq> {}"
  from compact_attains_sup[OF compact_continuous_image[OF cont compact], unfolded image_is_empty, OF ne]
  obtain tmax where tmax: "tmax \<in> T" "\<And>s. s \<in> T \<Longrightarrow> l s \<le> l tmax"
    by auto
  have "b - l tmax > 0"
    using ne tmax less by auto
  from uniform_limitD[OF ul this]
  have "\<forall>\<^sub>F n in at x. \<forall>x\<in>T. dist (f n x) (l x) < b - l tmax"
    by auto
  then show ?thesis
    apply eventually_elim
    using tmax
    by (force simp: dist_real_def abs_real_def split: if_splits)
qed auto

lemma
  order_uniform_limitD2:
  fixes l::"'a::topological_space\<Rightarrow>real"\<comment> \<open>TODO: generalize?!\<close>
  assumes ul: "uniform_limit T f l (at x)"
  assumes cont: "continuous_on T l"
  assumes compact: "compact T"
  assumes less: "\<And>t. t \<in> T \<Longrightarrow> l t > b"
  shows "\<forall>\<^sub>F y in at x. \<forall>t \<in> T. f y t > b"
proof -
  have "\<forall>\<^sub>F y in at x. \<forall>t\<in>T. (- f) y t < - b"
    by (rule order_uniform_limitD1[of "- f" T "-l" x "- b"])
      (auto simp: assms fun_Compl_def intro!: uniform_limit_eq_intros continuous_intros)
  then show ?thesis by auto
qed

lemma continuous_on_avoid_cases:
  fixes l::"'b::topological_space \<Rightarrow> 'a::linear_continuum_topology"\<comment> \<open>TODO: generalize!\<close>
  assumes cont: "continuous_on T l" and conn: "connected T"
  assumes avoid: "\<And>t. t \<in> T \<Longrightarrow> l t \<noteq> b"
  obtains "\<And>t. t \<in> T \<Longrightarrow> l t < b" | "\<And>t. t \<in> T \<Longrightarrow> l t > b"
  apply atomize_elim
  using connected_continuous_image[OF cont conn] using avoid
  unfolding connected_iff_interval
  apply (auto simp: image_iff)
  using leI by blast

lemma
  order_uniform_limit_ne:
  fixes l::"'a::topological_space\<Rightarrow>real"\<comment> \<open>TODO: generalize?!\<close>
  assumes ul: "uniform_limit T f l (at x)"
  assumes cont: "continuous_on T l"
  assumes compact: "compact T" and conn: "connected T"
  assumes ne: "\<And>t. t \<in> T \<Longrightarrow> l t \<noteq> b"
  shows "\<forall>\<^sub>F y in at x. \<forall>t \<in> T. f y t \<noteq> b"
proof -
  from continuous_on_avoid_cases[OF cont conn ne]
  consider "(\<And>t. t \<in> T \<Longrightarrow> l t < b)" | "(\<And>t. t \<in> T \<Longrightarrow> l t > b)"
    by blast
  then show ?thesis
  proof cases
    case 1
    from order_uniform_limitD1[OF ul cont compact 1]
    have "\<forall>\<^sub>F y in at x. \<forall>t\<in>T. f y t < b" by simp
    then show ?thesis
      by eventually_elim auto
  next
    case 2
    from order_uniform_limitD2[OF ul cont compact 2]
    have "\<forall>\<^sub>F y in at x. \<forall>t\<in>T. f y t > b" by simp
    then show ?thesis
      by eventually_elim auto
  qed
qed

lemma open_cballE:
  assumes "open S" "x\<in>S"
  obtains e where "e>0" "cball x e \<subseteq> S"
  using assms unfolding open_contains_cball by auto

lemma pos_half_less: fixes x::real shows "x > 0 \<Longrightarrow> x / 2 < x"
  by auto

lemma closed_levelset: "closed {x. s x = (c::'a::t1_space)}" if "continuous_on UNIV s"
proof -
  have "{x. s x = c} = s -` {c}" by auto
  also have "closed \<dots>"
    apply (rule closed_vimage)
     apply (rule closed_singleton)
    apply (rule that)
    done
  finally show ?thesis .
qed

lemma closed_levelset_within: "closed {x \<in> S. s x = (c::'a::t1_space)}" if "continuous_on S s" "closed S"
proof -
  have "{x \<in> S. s x = c} = s -` {c} \<inter> S" by auto
  also have "closed \<dots>"
    apply (rule continuous_on_closed_vimageI)
      apply (rule that)
     apply (rule that)
    apply simp
    done
  finally show ?thesis .
qed

context c1_on_open_euclidean
begin

lemma open_existence_ivlE:
  assumes "t \<in> existence_ivl0 x" "t \<ge> 0"
  obtains e where "e > 0" "cball x e \<times> {0 .. t + e} \<subseteq> Sigma X existence_ivl0"
proof -
  from assms have "(x, t) \<in> Sigma X existence_ivl0"
    by auto
  from open_cballE[OF open_state_space this]
  obtain e0' where e0: "0 < e0'" "cball (x, t) e0' \<subseteq> Sigma X existence_ivl0"
    by auto
  define e0 where "e0 = (e0' / 2)"
  from cball_times_subset[of x e0' t] pos_half_less[OF \<open>0 < e0'\<close>] half_gt_zero[OF \<open>0 < e0'\<close>] e0
  have "cball x e0 \<times> cball t e0 \<subseteq> Sigma X existence_ivl0" "0 < e0" "e0 < e0'"
    unfolding e0_def by auto
  then have "e0 > 0" "cball x e0 \<times> {0..t + e0} \<subseteq> Sigma X existence_ivl0"
    apply (auto simp: subset_iff dest!: spec[where x=t])
    subgoal for a b
      apply (rule in_existence_between_zeroI)
      apply (drule spec[where x=a])
       apply (drule spec[where x="t + e0"])
       apply (auto simp: dist_real_def closed_segment_eq_real_ivl)
      done
    done
  then show ?thesis ..
qed

lemmas [derivative_intros] = flow0_comp_has_derivative

lemma flow_isCont_state_space_comp[continuous_intros]:
  "t x \<in> existence_ivl0 (s x) \<Longrightarrow> isCont s x \<Longrightarrow> isCont t x \<Longrightarrow> isCont (\<lambda>x. flow0 (s x) (t x)) x"
  using continuous_within_compose3[where g="\<lambda>(x, t). flow0 x t"
      and f="\<lambda>x. (s x, t x)" and x = x and s = UNIV]
  flow_isCont_state_space
  by auto

lemma closed_plane[simp]: "closed {x. x \<bullet> i = c}"
  using closed_hyperplane[of i c] by (auto simp: inner_commute)

lemma flow_tendsto_compose[tendsto_intros]:
  assumes "(x \<longlongrightarrow> xs) F" "(t \<longlongrightarrow> ts) F"
  assumes "ts \<in> existence_ivl0 xs"
  shows "((\<lambda>s. flow0 (x s) (t s)) \<longlongrightarrow> flow0 xs ts) F"
proof -
  have ev: "\<forall>\<^sub>F s in F. (x s, t s) \<in> Sigma X existence_ivl0"
    using tendsto_Pair[OF assms(1,2), THEN topological_tendstoD, OF open_state_space]
      assms
    by auto
  show ?thesis
    by (rule continuous_on_tendsto_compose[OF flow_continuous_on_state_space tendsto_Pair, unfolded split_beta' fst_conv snd_conv])
      (use assms ev in auto)
qed

lemma returns_to_implicit_function:
  fixes s::"'a::euclidean_space \<Rightarrow> real"
  assumes rt: "returns_to {x \<in> S. s x = 0} x" (is "returns_to ?P x")
  assumes cS: "closed S"
  assumes Ds: "\<And>x. (s has_derivative blinfun_apply (Ds x)) (at x)"
  assumes DsC: "isCont Ds (poincare_map ?P x)"
  assumes nz: "Ds (poincare_map ?P x) (f (poincare_map ?P x)) \<noteq> 0"
  obtains u e
  where "s (flow0 x (u x)) = 0"
      "u x = return_time ?P x"
      "(\<And>y. y \<in> cball x e \<Longrightarrow> s (flow0 y (u y)) = 0)"
      "continuous_on (cball x e) u"
      "(\<lambda>t. (t, u t)) ` cball x e \<subseteq> Sigma X existence_ivl0"
      "0 < e" "(u has_derivative (- blinfun_scaleR_left
                   (inverse (blinfun_apply (Ds (poincare_map ?P x)) (f (poincare_map ?P x)))) o\<^sub>L
                      (Ds (poincare_map ?P x) o\<^sub>L flowderiv x (return_time ?P x)) o\<^sub>L embed1_blinfun)) (at x)"
proof -
  note [derivative_intros] = has_derivative_compose[OF _ Ds]
  have cont_s: "continuous_on UNIV s" by (rule has_derivative_continuous_on[OF Ds])
  note cls[simp, intro] = closed_levelset[OF cont_s]
  let ?t1 = "return_time ?P x"
  have cls[simp, intro]: "closed {x \<in> S. s x = 0}"
    by (rule closed_levelset_within) (auto intro!: cS continuous_on_subset[OF cont_s])
  then have xt1: "(x, ?t1) \<in> Sigma X existence_ivl0"
    by (auto intro!: return_time_exivl rt)
  have D: "(\<And>x. x \<in> Sigma X existence_ivl0 \<Longrightarrow>
      ((\<lambda>(x, t). s (flow0 x t)) has_derivative
       blinfun_apply (Ds (flow0 (fst x) (snd x)) o\<^sub>L (flowderiv (fst x) (snd x))))
       (at x))"
    by (auto intro!: derivative_eq_intros)
  have C: "isCont (\<lambda>x. Ds (flow0 (fst x) (snd x)) o\<^sub>L flowderiv (fst x) (snd x))
   (x, ?t1)"
    using flowderiv_continuous_on[unfolded continuous_on_eq_continuous_within,
        rule_format, OF xt1]
    using at_within_open[OF xt1 open_state_space]
    by (auto intro!: continuous_intros tendsto_eq_intros return_time_exivl rt
          isCont_tendsto_compose[OF DsC, unfolded poincare_map_def]
        simp: split_beta' isCont_def)
  from return_time_returns[OF rt cls]
  have Z: "(case (x, ?t1) of (x, t) \<Rightarrow> s (flow0 x t)) = 0"
    by (auto simp: )
  have I1: "blinfun_scaleR_left (inverse (Ds (flow0 x (?t1))(f (flow0 x (?t1))))) o\<^sub>L 
    ((Ds (flow0 (fst (x, return_time {x \<in> S. s x = 0} x))
            (snd (x, return_time {x \<in> S. s x = 0} x))) o\<^sub>L
       flowderiv (fst (x, return_time {x \<in> S. s x = 0} x))
        (snd (x, return_time {x \<in> S. s x = 0} x))) o\<^sub>L
      embed2_blinfun)
     = 1\<^sub>L"
    using nz
    by (auto intro!: blinfun_eqI
        simp: rt flowderiv_def blinfun.bilinear_simps inverse_eq_divide poincare_map_def)
  have I2: "((Ds (flow0 (fst (x, return_time {x \<in> S. s x = 0} x))
            (snd (x, return_time {x \<in> S. s x = 0} x))) o\<^sub>L
       flowderiv (fst (x, return_time {x \<in> S. s x = 0} x))
        (snd (x, return_time {x \<in> S. s x = 0} x))) o\<^sub>L
      embed2_blinfun) o\<^sub>L blinfun_scaleR_left (inverse (Ds (flow0 x (?t1))(f (flow0 x (?t1)))))
     = 1\<^sub>L"
    using nz
    by (auto intro!: blinfun_eqI
        simp: rt flowderiv_def blinfun.bilinear_simps inverse_eq_divide poincare_map_def)
  show ?thesis
    apply (rule implicit_function_theorem[where f="\<lambda>(x, t). s (flow0 x t)"
          and S="Sigma X existence_ivl0", OF D xt1 open_state_space order_refl C Z I1 I2])
     apply blast
    unfolding split_beta' fst_conv snd_conv poincare_map_def[symmetric]
    ..
qed

lemma (in auto_ll_on_open) f_tendsto[tendsto_intros]:
  assumes g1: "(g1 \<longlongrightarrow> b1) (at s within S)" and "b1 \<in> X"
  shows "((\<lambda>x. f (g1 x)) \<longlongrightarrow> f b1) (at s within S)"
  apply (rule continuous_on_tendsto_compose[OF continuous tendsto_Pair[OF tendsto_const],
      unfolded split_beta fst_conv snd_conv, OF g1])
  by (auto simp: \<open>b1 \<in> X\<close> intro!: topological_tendstoD[OF g1])

lemma flow_avoids_surface_eventually_at_right_pos:
  assumes "s x > 0 \<or> s x = 0 \<and> blinfun_apply (Ds x) (f x) > 0"
  assumes x: "x \<in> X"
  assumes Ds: "\<And>x. (s has_derivative Ds x) (at x)"
  assumes DsC: "\<And>x. isCont Ds x"
  shows "\<forall>\<^sub>F t in at_right 0. s (flow0 x t) > (0::real)"
proof -
  have cont_s: "continuous_on UNIV s" by (rule has_derivative_continuous_on[OF Ds])
  then have [THEN continuous_on_compose2, continuous_intros]: "continuous_on S s" for S by (rule continuous_on_subset) simp
  note [derivative_intros] = has_derivative_compose[OF _ Ds]
  note [tendsto_intros] = continuous_on_tendsto_compose[OF cont_s]
    isCont_tendsto_compose[OF DsC]
  from assms(1)
  consider "s x > 0" | "s x = 0" "blinfun_apply (Ds x) (f x) > 0"
    by auto
  then show ?thesis
  proof cases
    assume s: "s x > 0"
    then have "((\<lambda>t. s (flow0 x t)) \<longlongrightarrow> s x) (at_right 0)"
      by (auto intro!: tendsto_eq_intros simp: split_beta' x)
    from order_tendstoD(1)[OF this s]
    show ?thesis .
  next
    assume sz: "s x = 0" and pos: "blinfun_apply (Ds x) (f x) > 0"
    from x have "0 \<in> existence_ivl0 x" "open (existence_ivl0 x)" by simp_all
    then have evex: "\<forall>\<^sub>F t in at_right 0. t \<in> existence_ivl0 x"
      using eventually_at_topological by blast
    moreover
    from evex have "\<forall>\<^sub>F xa in at_right 0. flow0 x xa \<in> X"
      by (eventually_elim) (auto intro!: )
    then have "((\<lambda>t. (Ds (flow0 x t)) (f (flow0 x t))) \<longlongrightarrow> blinfun_apply (Ds x) (f x)) (at_right 0)"
      by (auto intro!: tendsto_eq_intros simp: split_beta' x)
    from order_tendstoD(1)[OF this pos]
    have "\<forall>\<^sub>F z in at_right 0. blinfun_apply (Ds (flow0 x z)) (f (flow0 x z)) > 0" .
    then obtain t where t: "t > 0" "\<And>z. 0 < z \<Longrightarrow> z < t \<Longrightarrow> blinfun_apply (Ds (flow0 x z)) (f (flow0 x z)) > 0"
      by (auto simp: eventually_at)
    have "\<forall>\<^sub>F z in at_right 0. z < t" using \<open>t > 0\<close> order_tendstoD(2)[OF tendsto_ident_at \<open>0 < t\<close>] by auto
    moreover have "\<forall>\<^sub>F z in at_right 0. 0 < z" by (simp add: eventually_at_filter)
    ultimately show ?thesis
    proof eventually_elim
      case (elim z)
      from closed_segment_subset_existence_ivl[OF \<open>z \<in> existence_ivl0 x\<close>]
      have csi: "{0..z} \<subseteq> existence_ivl0 x" by (auto simp add: closed_segment_eq_real_ivl)
      then have cont: "continuous_on {0..z} (\<lambda>t. s (flow0 x t))"
        by (auto intro!: continuous_intros)
      have "\<And>u. \<lbrakk>0 < u; u < z\<rbrakk> \<Longrightarrow> ((\<lambda>t. s (flow0 x t)) has_derivative (\<lambda>t. t * blinfun_apply (Ds (flow0 x u)) (f (flow0 x u)))) (at u)"
        using csi
        by (auto intro!: derivative_eq_intros simp: flowderiv_def blinfun.bilinear_simps)
      from mvt[OF \<open>0 < z\<close> cont this]
      obtain w where w: "0 < w" "w < z" and sDs: "s (flow0 x z) = z * blinfun_apply (Ds (flow0 x w)) (f (flow0 x w))"
        using x sz
        by auto
      note sDs
      also have "\<dots> > 0"
        using elim t(2)[of w] w by simp
      finally show ?case .
    qed
  qed
qed

lemma flow_avoids_surface_eventually_at_right_neg:
  assumes "s x < 0 \<or> s x = 0 \<and> blinfun_apply (Ds x) (f x) < 0"
  assumes x: "x \<in> X"
  assumes Ds: "\<And>x. (s has_derivative Ds x) (at x)"
  assumes DsC: "\<And>x. isCont Ds x"
  shows "\<forall>\<^sub>F t in at_right 0. s (flow0 x t) < (0::real)"
  apply (rule flow_avoids_surface_eventually_at_right_pos[of "-s" x "-Ds", simplified])
  using assms
  by (auto intro!: derivative_eq_intros simp: blinfun.bilinear_simps fun_Compl_def)

lemma flow_avoids_surface_eventually_at_right:
  assumes "x \<notin> S \<or> s x \<noteq> 0 \<or> blinfun_apply (Ds x) (f x) \<noteq> 0"
  assumes x: "x \<in> X" and cS: "closed S"
  assumes Ds: "\<And>x. (s has_derivative Ds x) (at x)"
  assumes DsC: "\<And>x. isCont Ds x"
  shows "\<forall>\<^sub>F t in at_right 0. (flow0 x t) \<notin> {x \<in> S. s x = (0::real)}"
proof -
  from assms(1)
  consider
      "s x > 0 \<or> s x = 0 \<and> blinfun_apply (Ds x) (f x) > 0"
    | "s x < 0 \<or> s x = 0 \<and> blinfun_apply (Ds x) (f x) < 0"
    | "x \<notin> S"
    by arith
  then show ?thesis
  proof cases
    case 1
    from flow_avoids_surface_eventually_at_right_pos[of s x Ds, OF 1 x Ds DsC]
    show ?thesis by eventually_elim auto
  next
    case 2
    from flow_avoids_surface_eventually_at_right_neg[of s x Ds, OF 2 x Ds DsC]
    show ?thesis by eventually_elim auto
  next
    case 3
    then have nS: "open (- S)" "x \<in> - S" using cS by auto
    have "\<forall>\<^sub>F t in at_right 0. (flow0 x t) \<in> - S"
      by (rule topological_tendstoD[OF _ nS]) (auto intro!: tendsto_eq_intros simp: x)
    then show ?thesis by eventually_elim auto
  qed
qed

lemma eventually_returns_to:
  fixes s::"'a::euclidean_space \<Rightarrow> real"
  assumes rt: "returns_to {x \<in> S. s x = 0} x" (is "returns_to ?P x")
  assumes cS: "closed S"
  assumes Ds: "\<And>x. (s has_derivative blinfun_apply (Ds x)) (at x)"
  assumes DsC: "\<And>x. isCont Ds x"
  assumes eventually_inside: "\<forall>\<^sub>F x in at (poincare_map ?P x). s x = 0 \<longrightarrow> x \<in> S"
  assumes nz: "Ds (poincare_map ?P x) (f (poincare_map ?P x)) \<noteq> 0"
  assumes nz0: "x \<notin> S \<or> s x \<noteq> 0 \<or> Ds x (f x) \<noteq> 0"
  shows "\<forall>\<^sub>F x in at x. returns_to ?P x"
proof -
  let ?t1 = "return_time ?P x"
  have cont_s: "continuous_on UNIV s" by (rule has_derivative_continuous_on[OF Ds])
  have cont_s': "continuous_on S s" for S by (rule continuous_on_subset[OF cont_s subset_UNIV])
  note s_tendsto[tendsto_intros] = continuous_on_tendsto_compose[OF cont_s, THEN tendsto_eq_rhs]
  note cls[simp, intro] = closed_levelset_within[OF cont_s' cS, of 0]
  note [tendsto_intros] = continuous_on_tendsto_compose[OF cont_s]
    isCont_tendsto_compose[OF DsC]
  obtain u e
    where "s (flow0 x (u x)) = 0"
      "u x = return_time ?P x"
      "(\<And>y. y \<in> cball x e \<Longrightarrow> s (flow0 y (u y)) = 0)"
      "continuous_on (cball x e) u"
      "(\<lambda>t. (t, u t)) ` cball x e \<subseteq> Sigma X existence_ivl0"
      "0 < e"
    by (rule returns_to_implicit_function[OF rt cS Ds DsC nz]; blast)
  then have u:
    "s (flow0 x (u x)) = 0" "u x = ?t1"
    "(\<And>y. y \<in> cball x e \<Longrightarrow> s (flow0 y (u y)) = 0)"
    "continuous_on (cball x e) u"
    "\<And>z. z \<in> cball x e \<Longrightarrow> u z \<in> existence_ivl0 z"
    "e > 0"
    by (force simp: split_beta')+
  have "\<forall>\<^sub>F y in at x. y \<in> ball x e"
    using eventually_at_ball[OF \<open>0 < e\<close>]
    by eventually_elim auto
  then have ev_cball: "\<forall>\<^sub>F y in at x. y \<in> cball x e"
    by eventually_elim (use \<open>e > 0\<close> in auto)
  moreover
  have "continuous_on (ball x e) u"
    using u by (auto simp: continuous_on_subset)
  then have [tendsto_intros]: "(u \<longlongrightarrow> u x) (at x)"
    using \<open>e > 0\<close> at_within_open[of y "ball x e" for y]
    by (auto simp: continuous_on_def)
  then have flow0_u_tendsto: "(\<lambda>x. flow0 x (u x)) \<midarrow>x\<rightarrow> poincare_map ?P x"
    by (auto intro!: tendsto_eq_intros u return_time_exivl rt simp: poincare_map_def)
  have s_imp: "s (poincare_map {x \<in> S. s x = 0} x) = 0 \<longrightarrow> poincare_map {x \<in> S. s x = 0} x \<in> S"
    using poincare_map_returns[OF rt]
    by auto
  from eventually_tendsto_compose_within[OF eventually_inside s_imp flow0_u_tendsto]
  have "\<forall>\<^sub>F x in at x. s (flow0 x (u x)) = 0 \<longrightarrow> flow0 x (u x) \<in> S" by auto
  with ev_cball
  have "\<forall>\<^sub>F x in at x. flow0 x (u x) \<in> S"
    by eventually_elim (auto simp: u)
  moreover
  {
    have "x \<in> X"
      using u(5) u(6) by force
    from ev_cball
    have ev_X: "\<forall>\<^sub>F y in at x. y \<in> X"\<comment> \<open>eigentlich ist das \<open>open X\<close>\<close>
      apply eventually_elim
      apply (rule)
      by (rule u)
    moreover
    {
      {
        assume a: "x \<notin> S" then have "open (-S)" "x \<in> - S" using cS by auto
        from topological_tendstoD[OF tendsto_ident_at this]
        have "(\<forall>\<^sub>F y in at x. y \<notin> S)" by auto
      } moreover {
        assume a: "s x \<noteq> 0"
        have "(\<forall>\<^sub>F y in at x. s y \<noteq> 0)"
          by (rule tendsto_imp_eventually_ne[OF _ a]) (auto intro!: tendsto_eq_intros)
      } moreover {
        assume a: "(Ds x) (f x) \<noteq> 0"
        have "(\<forall>\<^sub>F y in at x. blinfun_apply (Ds y) (f y) \<noteq> 0)"
          by (rule tendsto_imp_eventually_ne[OF _ a]) (auto intro!: tendsto_eq_intros ev_X \<open>x \<in> X\<close>)
      } ultimately have "(\<forall>\<^sub>F y in at x. y \<notin> S) \<or> (\<forall>\<^sub>F y in at x. s y \<noteq> 0) \<or> (\<forall>\<^sub>F y in at x. blinfun_apply (Ds y) (f y) \<noteq> 0)"
        using nz0 by auto
      then have "\<forall>\<^sub>F y in at x. y \<notin> S \<or> s y \<noteq> 0 \<or> blinfun_apply (Ds y) (f y) \<noteq> 0"
        apply -
        apply (erule disjE)
        subgoal by (rule eventually_elim2, assumption, assumption, blast)
        subgoal
          apply (erule disjE)
          subgoal by (rule eventually_elim2, assumption, assumption, blast)
          subgoal by (rule eventually_elim2, assumption, assumption, blast)
          done
        done
    }
    ultimately
    have "\<forall>\<^sub>F y in at x. (y \<notin> S \<or> s y \<noteq> 0 \<or> blinfun_apply (Ds y) (f y) \<noteq> 0) \<and> y \<in> X"
      by eventually_elim auto
  }
  then have "\<forall>\<^sub>F y in at x. \<forall>\<^sub>F t in at_right 0. flow0 y t \<notin> {x \<in> S. s x = 0}"
    apply eventually_elim
    by (rule flow_avoids_surface_eventually_at_right[where Ds=Ds]) (auto intro!: Ds DsC cS)
  moreover
  have at_eq: "(at x within cball x e) = at x"
    apply (rule at_within_interior)
    apply (auto simp: \<open>e > 0\<close>)
    done
  have "u x > 0"
    using u(1) by (auto simp: u rt cont_s' intro!: return_time_pos closed_levelset_within cS)
  then have "\<forall>\<^sub>F y in at x. u y > 0"
    apply (rule order_tendstoD[rotated])
    using u(4)
    apply (auto simp: continuous_on_def)
    apply (drule bspec[where x=x])
    using \<open>e > 0\<close>
    by (auto simp: at_eq)
  ultimately
  show "\<forall>\<^sub>F y in at x. returns_to ?P y"
    apply eventually_elim
    subgoal premises prems for y
      apply (rule returns_toI[where t="u y"])
      subgoal using prems  by auto
      subgoal apply (rule u) apply (rule prems) done
      subgoal using u(3)[of y] prems by auto
      subgoal using prems(3) by eventually_elim auto
      subgoal by simp
      done
    done
qed

lemma
  return_time_isCont_outside:
  fixes s::"'a::euclidean_space \<Rightarrow> real"
  assumes rt: "returns_to {x \<in> S. s x = 0} x" (is "returns_to ?P x")
  assumes cS: "closed S"
  assumes Ds: "\<And>x. (s has_derivative blinfun_apply (Ds x)) (at x)"
  assumes DsC: "\<And>x. isCont Ds x"
  assumes through: "(Ds (poincare_map ?P x)) (f (poincare_map ?P x)) \<noteq> 0"
  assumes eventually_inside: "\<forall>\<^sub>F x in at (poincare_map ?P x). s x = 0 \<longrightarrow> x \<in> S"
  assumes outside: "x \<notin> S \<or> s x \<noteq> 0"
  shows "isCont (return_time ?P) x"
  unfolding isCont_def
proof (rule tendstoI)
  fix e_orig::real assume "e_orig > 0"
  define e where "e = e_orig / 2"
  have "e > 0" using \<open>e_orig > 0\<close> by (simp add: e_def)

  have cont_s: "continuous_on UNIV s" by (rule has_derivative_continuous_on[OF Ds])
  then have s_tendsto: "(s \<longlongrightarrow> s x) (at x)" for x
    by (auto simp: continuous_on_def)
  have cont_s': "continuous_on S s" by (rule continuous_on_subset[OF cont_s subset_UNIV])
  note cls[simp, intro] = closed_levelset_within[OF cont_s' cS(1)]
  have "{x. s x = 0} = s -` {0}" by auto
  have ret_exivl: "return_time ?P x \<in> existence_ivl0 x"
    by (rule return_time_exivl; fact)
  then have [intro, simp]: "x \<in> X" by auto
  have isCont_Ds_f: "isCont (\<lambda>s. Ds s (f s)) (poincare_map ?P x)"
    apply (auto intro!: continuous_intros DsC)
    apply (rule has_derivative_continuous)
    apply (rule derivative_rhs)
    by (auto simp: poincare_map_def intro!: flow_in_domain return_time_exivl assms)

  obtain u eu where u:
      "s (flow0 x (u x)) = 0"
      "u x = return_time ?P x"
      "(\<And>y. y \<in> cball x eu \<Longrightarrow> s (flow0 y (u y)) = 0)"
      "continuous_on (cball x eu) u"
      "(\<lambda>t. (t, u t)) ` cball x eu \<subseteq> Sigma X existence_ivl0"
      "0 < eu"
    by (rule returns_to_implicit_function[OF rt cS(1) Ds DsC through]; blast)
  have u_tendsto: "(u \<longlongrightarrow> u x) (at x)"
    unfolding isCont_def[symmetric]
    apply (rule continuous_on_interior[OF u(4)])
    using \<open>0 < eu\<close> by auto
  have "u x > 0" by (auto simp: u intro!: return_time_pos rt)
  from order_tendstoD(1)[OF u_tendsto this] have "\<forall>\<^sub>F x in at x. 0 < u x" .
  moreover have "\<forall>\<^sub>F y in at x. y \<in> cball x eu"
    using eventually_at_ball[OF \<open>0 < eu\<close>, of x]
    by eventually_elim auto
  moreover
  have "x \<notin> S \<or> s x \<noteq> 0 \<or> blinfun_apply (Ds x) (f x) \<noteq> 0" using outside by auto
  have returns: "\<forall>\<^sub>F y in at x. returns_to ?P y"
    by (rule eventually_returns_to; fact)
  moreover
  have "\<forall>\<^sub>F y in at x. y \<in> ball x eu"
    using eventually_at_ball[OF \<open>0 < eu\<close>]
    by eventually_elim simp
  then have ev_cball: "\<forall>\<^sub>F y in at x. y \<in> cball x eu"
    by eventually_elim (use \<open>e > 0\<close> in auto)
  have "continuous_on (ball x eu) u"
    using u by (auto simp: continuous_on_subset)
  then have [tendsto_intros]: "(u \<longlongrightarrow> u x) (at x)"
    using \<open>eu > 0\<close> at_within_open[of y "ball x eu" for y]
    by (auto simp: continuous_on_def)
  then have flow0_u_tendsto: "(\<lambda>x. flow0 x (u x)) \<midarrow>x\<rightarrow> poincare_map ?P x"
    by (auto intro!: tendsto_eq_intros u return_time_exivl rt simp: poincare_map_def)
  have s_imp: "s (poincare_map {x \<in> S. s x = 0} x) = 0 \<longrightarrow> poincare_map {x \<in> S. s x = 0} x \<in> S"
    using poincare_map_returns[OF rt]
    by auto
  from eventually_tendsto_compose_within[OF eventually_inside s_imp flow0_u_tendsto]
  have "\<forall>\<^sub>F x in at x. s (flow0 x (u x)) = 0 \<longrightarrow> flow0 x (u x) \<in> S" by auto
  with ev_cball
  have "\<forall>\<^sub>F x in at x. flow0 x (u x) \<in> S"
    by eventually_elim (auto simp: u)
  ultimately have u_returns_ge: "\<forall>\<^sub>F y in at x. returns_to ?P y \<and> return_time ?P y \<le> u y"
  proof eventually_elim
    case (elim y)
    then show ?case
      using u elim by (auto intro!: return_time_le[OF _ cls])
  qed
  moreover
  have "\<forall>\<^sub>F y in at x. u y - return_time ?P x < e"
    using tendstoD[OF u_tendsto \<open>0 < e\<close>, unfolded u] u_returns_ge
    by eventually_elim (auto simp: dist_real_def)
  moreover
  note 1 = outside
  define ml where "ml = max (return_time ?P x / 2) (return_time ?P x - e)"
  have [intro, simp, arith]: "0 < ml" "ml < return_time ?P x" "ml \<le> return_time ?P x"
    using return_time_pos[OF rt cls] \<open>0 < e\<close>
    by (auto simp: ml_def)
  have mt_in: "ml \<in> existence_ivl0 x"
    using \<open>0 < e\<close>
    by (auto intro!: mem_existence_ivl_iv_defined in_existence_between_zeroI[OF ret_exivl]
        simp: closed_segment_eq_real_ivl ml_def)
  from open_existence_ivlE[OF mt_in]
  obtain e0 where e0: "e0 > 0" "cball x e0 \<times> {0..ml + e0} \<subseteq> Sigma X existence_ivl0" (is "?D \<subseteq> _")
    by auto
  have uc: "uniformly_continuous_on ((\<lambda>(x, t). flow0 x t) ` ?D) s"
    apply (auto intro!: compact_uniformly_continuous continuous_on_subset[OF cont_s])
    apply (rule compact_continuous_image)
     apply (rule continuous_on_subset)
      apply (rule flow_continuous_on_state_space)
     apply (rule e0)
    apply (rule compact_Times)
     apply (rule compact_cball)
    apply (rule compact_Icc)
    done
  let ?T = "{0..ml}"
  have ul: "uniform_limit ?T flow0 (flow0 x) (at x)"
    using \<open>0 < e\<close>
    by (intro uniform_limit_flow)
      (auto intro!: mem_existence_ivl_iv_defined in_existence_between_zeroI[OF ret_exivl]
        simp: closed_segment_eq_real_ivl )
  have "\<forall>\<^sub>F y in at x. \<forall>t\<in>{0..ml}. flow0 y t \<in> - {x \<in> S. s x = 0}"
    apply (rule uniform_limit_in_open)
    apply (rule ul)
       apply (auto intro!: continuous_intros continuous_on_compose2[OF cont_s] simp:
        split: if_splits)
     apply (meson atLeastAtMost_iff contra_subsetD local.ivl_subset_existence_ivl mt_in)
    subgoal for t
      apply (cases "t = 0")
      subgoal using 1 by (simp)
      subgoal
        using return_time_least[OF rt cls, of t] \<open>ml < return_time {x \<in> S. s x = 0} x\<close>
        by auto
      done
    done
  then have "\<forall>\<^sub>F y in at x. return_time ?P y \<ge> return_time ?P x - e"
    using u_returns_ge
  proof eventually_elim
    case (elim y)
    have "return_time ?P x - e \<le> ml"
      by (auto simp: ml_def)
    also
    have ry: "returns_to ?P y" "return_time ?P y \<le> u y"
      using elim
      by auto
    have "ml < return_time ?P y"
      apply (rule return_time_gt[OF ry(1) cls])
      using elim
      by (auto simp: Ball_def)
    finally show ?case by simp
  qed
  ultimately
  have "\<forall>\<^sub>F y in at x. dist (return_time ?P y) (return_time ?P x) \<le> e"
    by eventually_elim (auto simp: dist_real_def abs_real_def algebra_simps)
  then show "\<forall>\<^sub>F y in at x. dist (return_time ?P y) (return_time ?P x) < e_orig"
    by eventually_elim (use \<open>e_orig > 0\<close> in \<open>auto simp: e_def\<close>)
qed

lemma isCont_poincare_map:
  assumes "isCont (return_time P) x"
    "returns_to P x" "closed P"
  shows "isCont (poincare_map P) x"
  unfolding poincare_map_def
  by (auto intro!: continuous_intros assms return_time_exivl)

lemma poincare_map_tendsto:
  assumes "(return_time P \<longlongrightarrow> return_time P x) (at x within S)"
    "returns_to P x" "closed P"
  shows "(poincare_map P \<longlongrightarrow> poincare_map P x) (at x within S)"
  unfolding poincare_map_def
  by (rule tendsto_eq_intros refl assms return_time_exivl)+

lemma
  return_time_continuous_below:
  fixes s::"'a::euclidean_space \<Rightarrow> real"
  assumes rt: "returns_to {x \<in> S. s x = 0} x" (is "returns_to ?P x")
  assumes Ds: "\<And>x. (s has_derivative blinfun_apply (Ds x)) (at x)"
  assumes cS: "closed S"
  assumes eventually_inside: "\<forall>\<^sub>F x in at (poincare_map ?P x). s x = 0 \<longrightarrow> x \<in> S"
  assumes DsC: "\<And>x. isCont Ds x"
  assumes through: "(Ds (poincare_map ?P x)) (f (poincare_map ?P x)) \<noteq> 0"
  assumes inside: "x \<in> S" "s x = 0" "Ds x (f x) < 0"
  shows "continuous (at x within {x. s x \<le> 0}) (return_time ?P)"
  unfolding continuous_within
proof (rule tendstoI)
  fix e_orig::real assume "e_orig > 0"
  define e where "e = e_orig / 2"
  have "e > 0" using \<open>e_orig > 0\<close> by (simp add: e_def)

  note DsC_tendso[tendsto_intros] = isCont_tendsto_compose[OF DsC]
  have cont_s: "continuous_on UNIV s" by (rule has_derivative_continuous_on[OF Ds])
  then have s_tendsto: "(s \<longlongrightarrow> s x) (at x)" for x
    by (auto simp: continuous_on_def)
  note [continuous_intros] = continuous_on_compose2[OF cont_s _ subset_UNIV]
  note [derivative_intros] = has_derivative_compose[OF _ Ds]
  have cont_s': "continuous_on S s" by (rule continuous_on_subset[OF cont_s subset_UNIV])
  note cls[simp, intro] = closed_levelset_within[OF cont_s' cS(1)]
  have "{x. s x = 0} = s -` {0}" by auto
  have ret_exivl: "return_time ?P x \<in> existence_ivl0 x"
    by (rule return_time_exivl; fact)
  then have [intro, simp]: "x \<in> X" by auto
  have isCont_Ds_f: "isCont (\<lambda>s. Ds s (f s)) (poincare_map ?P x)"
    apply (auto intro!: continuous_intros DsC)
    apply (rule has_derivative_continuous)
    apply (rule derivative_rhs)
    by (auto simp: poincare_map_def intro!: flow_in_domain return_time_exivl assms)

  have "\<forall>\<^sub>F yt in at (x, 0) within UNIV \<times> {0<..}. (Ds (flow0 (fst yt) (snd yt))) (f (flow0 (fst yt) (snd yt))) < 0"
    by (rule order_tendstoD) (auto intro!: tendsto_eq_intros inside)
  moreover
  have "(x, 0) \<in> Sigma X existence_ivl0" by auto
  from topological_tendstoD[OF tendsto_ident_at open_state_space this, of "UNIV \<times> {0<..}"]
  have "\<forall>\<^sub>F yt in at (x, 0) within UNIV \<times> {0<..}. snd yt \<in> existence_ivl0 (fst yt)"
    by eventually_elim auto
  moreover
  from topological_tendstoD[OF tendsto_ident_at open_Times[OF open_dom open_UNIV], of "(x, 0)" "UNIV \<times> {0<..}"]
  have "\<forall>\<^sub>F yt in at (x, 0) within UNIV \<times> {0<..}. fst yt \<in> X"
    by (auto simp: mem_Times_iff)
  ultimately
  have "\<forall>\<^sub>F yt in at (x, 0) within UNIV \<times> {0<..}. (Ds (flow0 (fst yt) (snd yt))) (f (flow0 (fst yt) (snd yt))) < 0 \<and>
    snd yt \<in> existence_ivl0 (fst yt) \<and>
    0 \<in> existence_ivl0 (fst yt)"
    by eventually_elim auto
  then obtain d2 where "0 < d2" and
    d2_neg: "\<And>y t. (y, t) \<in> cball (x, 0) d2 \<Longrightarrow> 0 < t \<Longrightarrow> (Ds (flow0 y t)) (f (flow0 y t)) < 0"
    and d2_ex: "\<And>y t. (y, t) \<in> cball (x, 0) d2 \<Longrightarrow> 0 < t \<Longrightarrow> t \<in> existence_ivl0 y"
    and d2_ex0: "\<And>y t. (y, t::real) \<in> cball (x, 0) d2 \<Longrightarrow> 0 < t \<Longrightarrow> y \<in> X"
    by (auto simp: eventually_at_le dist_commute)
  define d where "d \<equiv> d2 / 2"
  from \<open>0 < d2\<close> have "d > 0" by (simp add: d_def)
  have d_neg: "dist y x< d \<Longrightarrow> 0 < t \<Longrightarrow> t \<le> d \<Longrightarrow> (Ds (flow0 y t)) (f (flow0 y t)) < 0" for y t
    using d2_neg[of y t, OF subsetD[OF cball_times_subset[of x d2 0]]]
    by (auto simp: d_def dist_commute)
  have d_ex: "t \<in> existence_ivl0 y" if "dist y x< d" "0 \<le> t" "t \<le> d" for y t
  proof cases
    assume "t = 0"
    have "sqrt ((dist x y)\<^sup>2 + (d2 / 2)\<^sup>2) \<le> dist x y + d2/2"
      using \<open>0 < d2\<close>
      by (intro sqrt_sum_squares_le_sum) auto
    also have "dist x y \<le> d2 / 2"
      using that by (simp add: d_def dist_commute)
    finally have "sqrt ((dist x y)\<^sup>2 + (d2 / 2)\<^sup>2) \<le> d2" by simp
    with \<open>t = 0\<close> show ?thesis
      using d2_ex[of y t, OF subsetD[OF cball_times_subset[of x d2 0]]] d2_ex0[of y d] \<open>0 < d2\<close>
      by (auto simp: d_def dist_commute dist_prod_def)
  next
    assume "t \<noteq> 0"
    then show ?thesis
      using d2_ex[of y t, OF subsetD[OF cball_times_subset[of x d2 0]]] that
      by (auto simp: d_def dist_commute)
  qed
  have d_mvt: "s (flow0 y t) < s y" if "0 < t" "t \<le> d" "dist y x < d" for y t
  proof -
    have c: "continuous_on {0 .. t} (\<lambda>t. s (flow0 y t))"
      using that
      by (auto intro!: continuous_intros d_ex)
    have d: "\<And>x. \<lbrakk>0 < x; x < t\<rbrakk> \<Longrightarrow> ((\<lambda>t. s (flow0 y t)) has_derivative (\<lambda>t. t * blinfun_apply (Ds (flow0 y x)) (f (flow0 y x)))) (at x)"
      using that
      by (auto intro!: derivative_eq_intros d_ex simp: flowderiv_def blinfun.bilinear_simps)
    from mvt[OF \<open>0 < t\<close> c d]
    obtain xi where xi: "0 < xi" "xi < t" and "s (flow0 y t) - s (flow0 y 0) = t * blinfun_apply (Ds (flow0 y xi)) (f (flow0 y xi))"
      by auto
    note this(3)
    also have "\<dots> < 0"
      using \<open>0 < t\<close>
      apply (rule mult_pos_neg)
      apply (rule d_neg)
      using that xi by auto
    also have "flow0 y 0 = y"
      apply (rule flow_initial_time)
      apply auto
      using \<open>0 < d\<close> d_ex that(3) by fastforce
    finally show ?thesis
      by (auto simp: )
  qed
  obtain u eu where u:
      "s (flow0 x (u x)) = 0"
      "u x = return_time ?P x"
      "(\<And>y. y \<in> cball x eu \<Longrightarrow> s (flow0 y (u y)) = 0)"
      "continuous_on (cball x eu) u"
      "(\<lambda>t. (t, u t)) ` cball x eu \<subseteq> Sigma X existence_ivl0"
      "0 < eu"
    by (rule returns_to_implicit_function[OF rt cS(1) Ds DsC through]; blast)
  have u_tendsto: "(u \<longlongrightarrow> u x) (at x)"
    unfolding isCont_def[symmetric]
    apply (rule continuous_on_interior[OF u(4)])
    using \<open>0 < eu\<close> by auto
  have "u x > 0" by (auto simp: u intro!: return_time_pos rt)
  from order_tendstoD(1)[OF u_tendsto this] have "\<forall>\<^sub>F x in at x. 0 < u x" .
  moreover have "\<forall>\<^sub>F y in at x. y \<in> cball x eu"
    using eventually_at_ball[OF \<open>0 < eu\<close>, of x]
    by eventually_elim auto
  moreover
  have "x \<notin> S \<or> s x \<noteq> 0 \<or> blinfun_apply (Ds x) (f x) \<noteq> 0" using inside by auto
  have returns: "\<forall>\<^sub>F y in at x. returns_to ?P y"
    by (rule eventually_returns_to; fact)
  moreover
  have "\<forall>\<^sub>F y in at x. y \<in> ball x eu"
    using eventually_at_ball[OF \<open>0 < eu\<close>]
    by eventually_elim simp
  then have ev_cball: "\<forall>\<^sub>F y in at x. y \<in> cball x eu"
    by eventually_elim (use \<open>e > 0\<close> in auto)
  have "continuous_on (ball x eu) u"
    using u by (auto simp: continuous_on_subset)
  then have [tendsto_intros]: "(u \<longlongrightarrow> u x) (at x)"
    using \<open>eu > 0\<close> at_within_open[of y "ball x eu" for y]
    by (auto simp: continuous_on_def)
  then have flow0_u_tendsto: "(\<lambda>x. flow0 x (u x)) \<midarrow>x\<rightarrow> poincare_map ?P x"
    by (auto intro!: tendsto_eq_intros u return_time_exivl rt simp: poincare_map_def)
  have s_imp: "s (poincare_map {x \<in> S. s x = 0} x) = 0 \<longrightarrow> poincare_map {x \<in> S. s x = 0} x \<in> S"
    using poincare_map_returns[OF rt]
    by auto
  from eventually_tendsto_compose_within[OF eventually_inside s_imp flow0_u_tendsto]
  have "\<forall>\<^sub>F x in at x. s (flow0 x (u x)) = 0 \<longrightarrow> flow0 x (u x) \<in> S" by auto
  with ev_cball
  have "\<forall>\<^sub>F x in at x. flow0 x (u x) \<in> S"
    by eventually_elim (auto simp: u)
  ultimately have u_returns_ge: "\<forall>\<^sub>F y in at x. returns_to ?P y \<and> return_time ?P y \<le> u y"
  proof eventually_elim
    case (elim y)
    then show ?case
      using u elim by (auto intro!: return_time_le[OF _ cls])
  qed
  moreover
  have "\<forall>\<^sub>F y in at x. u y - return_time ?P x < e"
    using tendstoD[OF u_tendsto \<open>0 < e\<close>, unfolded u] u_returns_ge
    by eventually_elim (auto simp: dist_real_def)
  moreover
  have d_less: "d < return_time ?P x"
    apply (rule return_time_gt)
      apply fact apply fact
    subgoal for t
      using d_mvt[of t x] \<open>s x = 0\<close> \<open>0 < d\<close>
      by auto
    done
  note 1 = inside
  define ml where "ml = Max {return_time ?P x / 2, return_time ?P x - e, d}"
  have [intro, simp, arith]: "0 < ml" "ml < return_time ?P x" "ml \<le> return_time ?P x" "d \<le> ml"
    using return_time_pos[OF rt cls] \<open>0 < e\<close> d_less
    by (auto simp: ml_def)
  have mt_in: "ml \<in> existence_ivl0 x"
    using \<open>0 < e\<close> \<open>0 < d\<close> d_less
    by (auto intro!: mem_existence_ivl_iv_defined in_existence_between_zeroI[OF ret_exivl]
        simp: closed_segment_eq_real_ivl ml_def)
  from open_existence_ivlE[OF mt_in]
  obtain e0 where e0: "e0 > 0" "cball x e0 \<times> {0..ml + e0} \<subseteq> Sigma X existence_ivl0" (is "?D \<subseteq> _")
    by auto
  have uc: "uniformly_continuous_on ((\<lambda>(x, t). flow0 x t) ` ?D) s"
    apply (auto intro!: compact_uniformly_continuous continuous_on_subset[OF cont_s])
    apply (rule compact_continuous_image)
     apply (rule continuous_on_subset)
      apply (rule flow_continuous_on_state_space)
     apply (rule e0)
    apply (rule compact_Times)
     apply (rule compact_cball)
    apply (rule compact_Icc)
    done
  let ?T = "{d..ml}"
  have ul: "uniform_limit ?T flow0 (flow0 x) (at x)"
    using \<open>0 < e\<close> \<open>0 < d\<close> d_less
    by (intro uniform_limit_flow)
      (auto intro!: mem_existence_ivl_iv_defined in_existence_between_zeroI[OF ret_exivl]
        simp: closed_segment_eq_real_ivl )
  {
    have "\<forall>\<^sub>F y in at x within {x. s x \<le> 0}. y \<in> X"
      by (rule topological_tendstoD[OF tendsto_ident_at open_dom \<open>x \<in> X\<close>])
    moreover
    have "\<forall>\<^sub>F y in at x within {x. s x \<le> 0}. s y \<le> 0"
      by (auto simp: eventually_at)
    moreover
    have "\<forall>\<^sub>F y in at x within {x. s x \<le> 0}. Ds y (f y) < 0"
      by (rule order_tendstoD) (auto intro!: tendsto_eq_intros inside)
    moreover
    from tendstoD[OF tendsto_ident_at \<open>0 < d\<close>]
    have "\<forall>\<^sub>F y in at x within {x. s x \<le> 0}. dist y x < d"
      by (auto simp: )
    moreover
    have "d \<in> existence_ivl0 x"
      using d_ex[of x d] \<open>0 < d\<close> by auto
    have dret: "returns_to {x\<in>S. s x = 0} (flow0 x d)"
      apply (rule returns_to_laterI)
          apply fact+
      subgoal for u
        using d_mvt[of u x] \<open>s x = 0\<close>
        by auto
      done
    have "\<forall>\<^sub>F y in at x. \<forall>t\<in>{d..ml}. flow0 y t \<in> - {x \<in> S. s x = 0}"
      apply (rule uniform_limit_in_open)
           apply (rule ul)
          apply (auto intro!: continuous_intros continuous_on_compose2[OF cont_s] simp:
          split: if_splits)
      using \<open>d \<in> existence_ivl0 x\<close> mem_is_interval_1_I mt_in apply blast
      subgoal for t
        using return_time_least[OF rt cls, of t] \<open>ml < return_time {x \<in> S. s x = 0} x\<close> \<open>0 < d\<close>
        by auto
      done
    then have "\<forall>\<^sub>F y in at x within {x. s x \<le> 0}. \<forall>t\<in>{d .. ml}. flow0 y t \<in> - {x \<in> S. s x = 0}"
      by (auto simp add: eventually_at; force)
    ultimately
    have "\<forall>\<^sub>F y in at x within {x. s x \<le> 0}. \<forall>t\<in>{0<..ml}. flow0 y t \<in> - {x \<in> S. s x = 0}"
      apply eventually_elim
      apply auto
      using d_mvt
      by fastforce
    moreover
    have "\<forall>\<^sub>F y in at x. returns_to ?P y"
      by fact
    then have "\<forall>\<^sub>F y in at x within {x. s x \<le> 0}. returns_to ?P y"
      by (auto simp: eventually_at)
    ultimately
    have "\<forall>\<^sub>F y in at x within {x. s x \<le> 0}. return_time ?P y > ml"
      apply eventually_elim
      apply (rule return_time_gt)
      by auto
  }
  then have "\<forall>\<^sub>F y in at x within {x. s x \<le> 0}. return_time ?P y \<ge> return_time ?P x - e"
    by eventually_elim (auto simp: ml_def)
  ultimately
  have "\<forall>\<^sub>F y in at x within {x . s x \<le> 0}. dist (return_time ?P y) (return_time ?P x) \<le> e"
    unfolding eventually_at_filter
    by eventually_elim (auto simp: dist_real_def abs_real_def algebra_simps)
  then show "\<forall>\<^sub>F y in at x within {x. s x \<le> 0}. dist (return_time ?P y) (return_time ?P x) < e_orig"
    by eventually_elim (use \<open>e_orig > 0\<close> in \<open>auto simp: e_def\<close>)
qed

lemma
  return_time_continuous_below_plane:
  fixes s::"'a::euclidean_space \<Rightarrow> real"
  assumes rt: "returns_to {x \<in> R. x \<bullet> n = c} x" (is "returns_to ?P x")
  assumes cR: "closed R"
  assumes through: "f (poincare_map ?P x) \<bullet> n \<noteq> 0"
  assumes R: "x \<in> R"
  assumes inside: "x \<bullet> n = c" "f x \<bullet> n < 0"
  assumes eventually_inside: "\<forall>\<^sub>F x in at (poincare_map ?P x). x \<bullet> n = c \<longrightarrow> x \<in> R"
  shows "continuous (at x within {x. x \<bullet> n \<le> c}) (return_time ?P)"
  apply (rule return_time_continuous_below[of R "\<lambda>x. x \<bullet> n - c", simplified])
  using through rt inside cR R eventually_inside
  by (auto intro!: derivative_eq_intros blinfun_inner_left.rep_eq[symmetric])

lemma
  poincare_map_in_interior_eventually_return_time_equal:
  assumes RP: "R \<subseteq> P"
  assumes cP: "closed P"
  assumes cR: "closed R"
  assumes ret: "returns_to P x"
  assumes evret: "\<forall>\<^sub>F x in at x within S. returns_to P x"
  assumes evR: "\<forall>\<^sub>F x in at x within S. poincare_map P x \<in> R"
  shows "\<forall>\<^sub>F x in at x within S. returns_to R x \<and> return_time P x = return_time R x"
proof -
  from evret evR
  show ?thesis
  proof eventually_elim
    case (elim x)
    from return_time_least[OF elim(1) cP] RP
    have rtl: "\<And>s. 0 < s \<Longrightarrow> s < return_time P x \<Longrightarrow> flow0 x s \<notin> R"
      by auto
    from elim(2) have pR: "poincare_map P x \<in> R"
      by auto
    have "\<forall>\<^sub>F t in at_right 0. 0 < t"
      by (simp add: eventually_at_filter)
    moreover have "\<forall>\<^sub>F t in at_right 0. t < return_time P x"
      using return_time_pos[OF elim(1) cP]
      by (rule order_tendstoD[OF tendsto_ident_at])
    ultimately have evR: "\<forall>\<^sub>F t in at_right 0. flow0 x t \<notin> R"
    proof eventually_elim
      case et: (elim t)
      from return_time_least[OF elim(1) cP et] show ?case using RP by auto
    qed
    have rtp: "0 < return_time P x" by (intro return_time_pos cP elim)
    have rtex: "return_time P x \<in> existence_ivl0 x" by (intro return_time_exivl elim cP)
    have frR: "flow0 x (return_time P x) \<in> R"
      unfolding poincare_map_def[symmetric] by (rule pR)
    have "returns_to R x"
      by (rule returns_toI[where t="return_time P x"]; fact)
    moreover have "return_time R x = return_time P x"
      by (rule return_time_eqI) fact+
    ultimately show ?case by auto
  qed
qed

lemma poincare_map_in_planeI:
  assumes "returns_to (plane n c) x0"
  shows "poincare_map (plane n c) x0 \<bullet> n = c"
  using poincare_map_returns[OF assms]
  by fastforce

lemma less_return_time_imp_exivl:
  "h \<in> existence_ivl0 x'" if "h \<le> return_time P x'" "returns_to P x'" "closed P" "0 \<le> h"
proof -
  from return_time_exivl[OF that(2,3)]
  have "return_time P x' \<in> existence_ivl0 x'" by auto
  from ivl_subset_existence_ivl[OF this] that show ?thesis
    by auto
qed

lemma eventually_returns_to_continuousI:
  assumes "returns_to P x"
  assumes "closed P"
  assumes "continuous (at x within S) (return_time P)"
  shows "\<forall>\<^sub>F x in at x within S. returns_to P x"
proof -
  have "return_time P x > 0"
    using assms by (auto simp: return_time_pos)
  from order_tendstoD(1)[OF assms(3)[unfolded continuous_within] this]
  have "\<forall>\<^sub>F x in at x within S. 0 < return_time P x" .
  then show ?thesis
    by eventually_elim (auto simp: return_time_pos_returns_to)
qed

lemma return_time_implicit_functionE:
  fixes s::"'a::euclidean_space \<Rightarrow> real"
  assumes rt: "returns_to {x \<in> S. s x = 0} x" (is "returns_to ?P _")
  assumes cS: "closed S"
  assumes Ds: "\<And>x. (s has_derivative blinfun_apply (Ds x)) (at x)"
  assumes DsC: "\<And>x. isCont Ds x"
  assumes Ds_through: "(Ds (poincare_map ?P x)) (f (poincare_map ?P x)) \<noteq> 0"
  assumes eventually_inside: "\<forall>\<^sub>F x in at (poincare_map ?P x). s x = 0 \<longrightarrow> x \<in> S"
  assumes outside: "x \<notin> S \<or> s x \<noteq> 0"
  obtains e' where
    "0 < e'"
    "\<And>y. y \<in> ball x e' \<Longrightarrow> returns_to ?P y"
    "\<And>y. y \<in> ball x e' \<Longrightarrow> s (flow0 y (return_time ?P y)) = 0"
    "continuous_on (ball x e') (return_time ?P)"
    "(\<And>y. y \<in> ball x e' \<Longrightarrow> Ds (poincare_map ?P y) o\<^sub>L flowderiv y (return_time ?P y) o\<^sub>L embed2_blinfun \<in> invertibles_blinfun)"
    "(\<And>U v sa.
       (\<And>sa. sa \<in> U \<Longrightarrow> s (flow0 sa (v sa)) = 0) \<Longrightarrow>
       return_time ?P x = v x \<Longrightarrow>
       continuous_on U v \<Longrightarrow> sa \<in> U \<Longrightarrow> x \<in> U \<Longrightarrow> U \<subseteq> ball x e' \<Longrightarrow> connected U \<Longrightarrow> open U \<Longrightarrow> return_time ?P sa = v sa)"
    "(return_time ?P has_derivative
        - blinfun_scaleR_left (inverse ((Ds (poincare_map ?P x)) (f (poincare_map ?P x)))) o\<^sub>L
              (Ds (poincare_map ?P x) o\<^sub>L Dflow x (return_time ?P x)))
            (at x)"
proof -
  have cont_s: "continuous_on UNIV s" by (rule has_derivative_continuous_on[OF Ds])
  then have s_tendsto: "(s \<longlongrightarrow> s x) (at x)" for x
    by (auto simp: continuous_on_def)
  have cls[simp, intro]: "closed {x \<in> S. s x = 0}"
    by (rule closed_levelset_within) (auto intro!: cS continuous_on_subset[OF cont_s])

  have cont_Ds: "continuous_on UNIV Ds"
    using DsC by (auto simp: continuous_on_def isCont_def)
  note [tendsto_intros] = continuous_on_tendsto_compose[OF cont_Ds _ UNIV_I, simplified]
  note [continuous_intros] = continuous_on_compose2[OF cont_Ds _ subset_UNIV]

  have "\<forall>\<^sub>F x in at (poincare_map ?P x). s x = 0 \<longrightarrow> x \<in> S"
    using eventually_inside
    by auto
  then obtain U where "open U" "poincare_map ?P x \<in> U" "\<And>x. x \<in> U \<Longrightarrow> s x = 0 \<Longrightarrow> x \<in> S"
    using poincare_map_returns[OF rt cls]
    by (force simp: eventually_at_topological)
  have s_imp: "s (poincare_map ?P x) = 0 \<longrightarrow> poincare_map ?P x \<in> S"
    using poincare_map_returns[OF rt cls]
    by auto
  have outside_disj: "x \<notin> S \<or> s x \<noteq> 0 \<or> blinfun_apply (Ds x) (f x) \<noteq> 0"
    using outside by auto
  have pm_tendsto: "(poincare_map ?P \<longlongrightarrow> poincare_map ?P x) (at x)"
    apply (rule poincare_map_tendsto)
    unfolding isCont_def[symmetric]
      apply (rule return_time_isCont_outside)
    using assms
    by (auto intro!: cls )
  have evmemS: "\<forall>\<^sub>F x in at x. poincare_map ?P x \<in> S"
    using eventually_returns_to[OF rt cS Ds DsC eventually_inside Ds_through outside_disj]
    apply eventually_elim
    using poincare_map_returns
    by auto
  have "\<forall>\<^sub>F x in at x. \<forall>\<^sub>F x in at (poincare_map ?P x). s x = 0 \<longrightarrow> x \<in> S"
    apply (rule eventually_tendsto_compose_within[OF _ _ pm_tendsto])
      apply (rule eventually_eventually_withinI)
       apply (rule eventually_inside)
      apply (rule s_imp)
     apply (rule eventually_inside)
    apply (rule evmemS)
    done
  moreover
  have "eventually (\<lambda>x. x \<in> - ?P) (at x)"
    apply (rule topological_tendstoD)
    using outside
    by (auto intro!: )
  then have "eventually (\<lambda>x. x \<notin> S \<or> s x \<noteq> 0) (at x)"
    by auto
  moreover
  have "eventually (\<lambda>x. (Ds (poincare_map ?P x)) (f (poincare_map ?P x)) \<noteq> 0) (at x)"
    apply (rule tendsto_imp_eventually_ne)
     apply (rule tendsto_intros)
     apply (rule tendsto_intros)
    unfolding poincare_map_def
      apply (rule tendsto_intros)
        apply (rule tendsto_intros)
       apply (subst isCont_def[symmetric])
       apply (rule return_time_isCont_outside[OF rt cS Ds DsC Ds_through eventually_inside outside])
      apply (rule return_time_exivl[OF rt cls])
      apply (rule tendsto_intros)
        apply (rule tendsto_intros)
        apply (rule tendsto_intros)
       apply (subst isCont_def[symmetric])
       apply (rule return_time_isCont_outside[OF rt cS Ds DsC Ds_through eventually_inside outside])
      apply (rule return_time_exivl[OF rt cls])
     apply (rule flow_in_domain)
     apply (rule return_time_exivl[OF rt cls])
    unfolding poincare_map_def[symmetric]
    apply (rule Ds_through)
    done
  ultimately
  have "eventually (\<lambda>y. returns_to ?P y \<and> (\<forall>\<^sub>F x in at (poincare_map ?P y). s x = 0 \<longrightarrow> x \<in> S) \<and>
    (y \<notin> S \<or> s y \<noteq> 0) \<and> (Ds (poincare_map ?P y)) (f (poincare_map ?P y)) \<noteq> 0) (at x)"
    using eventually_returns_to[OF rt cS Ds DsC eventually_inside Ds_through outside_disj]
    by eventually_elim auto
  then obtain Y' where Y': "open Y'" "x \<in> Y'" "\<And>y. y \<in> Y' \<Longrightarrow> returns_to ?P y"
      "\<And>y. y \<in> Y' \<Longrightarrow> (\<forall>\<^sub>F x in at (poincare_map ?P y). s x = 0 \<longrightarrow> x \<in> S)"
      "\<And>y. y \<in> Y' \<Longrightarrow> y \<notin> S \<or> s y \<noteq> 0"
      "\<And>y. y \<in> Y' \<Longrightarrow> blinfun_apply (Ds (poincare_map ?P y)) (f (poincare_map ?P y)) \<noteq> 0"
    apply (subst (asm) (3) eventually_at_topological)
    using rt outside Ds_through eventually_inside
    by fastforce
  from openE[OF \<open>open Y'\<close> \<open>x \<in> Y'\<close>] obtain eY where eY: "0 < eY" "ball x eY \<subseteq> Y'" by auto
  define Y where "Y = ball x eY"
  then have Y: "open Y" and x: "x \<in> Y"
      and Yr: "\<And>y. y \<in> Y \<Longrightarrow> returns_to ?P y"
      and Y_mem: "\<And>y. y \<in> Y \<Longrightarrow> (\<forall>\<^sub>F x in at (poincare_map ?P y). s x = 0 \<longrightarrow> x \<in> S)"
      and Y_nz: "\<And>y. y \<in> Y \<Longrightarrow> y \<notin> S \<or> s y \<noteq> 0"
      and Y_fnz: "\<And>y. y \<in> Y \<Longrightarrow> Ds (poincare_map ?P y) (f (poincare_map ?P y)) \<noteq> 0"
      and Y_convex: "convex Y"
    using Y' eY
    by (auto simp: subset_iff dist_commute)
  have "isCont (return_time ?P) y" if "y \<in> Y" for y
    using return_time_isCont_outside[OF Yr[OF that] cS Ds DsC Y_fnz Y_mem Y_nz, OF that that that] .
  then have cY: "continuous_on Y (return_time ?P)"
    by (auto simp: continuous_on_def isCont_def Lim_at_imp_Lim_at_within)

  note [derivative_intros] = has_derivative_compose[OF _ Ds]
  let ?t1 = "return_time ?P x"
  have t1_exivl: "?t1 \<in> existence_ivl0 x"
    by (auto intro!: return_time_exivl rt)
  then have [simp]: "x \<in> X" by auto
  have xt1: "(x, ?t1) \<in> Sigma Y existence_ivl0"
    by (auto intro!: return_time_exivl rt x)
  have "Sigma Y existence_ivl0 = Sigma X existence_ivl0 \<inter> fst -` Y" by auto
  also have "open \<dots>"
    by (rule open_Int[OF open_state_space open_vimage_fst[OF \<open>open Y\<close>]])
  finally have "open (Sigma Y existence_ivl0)" .
  have D: "(\<And>x. x \<in> Sigma Y existence_ivl0 \<Longrightarrow>
      ((\<lambda>(x, t). s (flow0 x t)) has_derivative
       blinfun_apply (Ds (flow0 (fst x) (snd x)) o\<^sub>L (flowderiv (fst x) (snd x))))
       (at x))"
    by (auto intro!: derivative_eq_intros)
  have C: "continuous_on (Sigma Y existence_ivl0) (\<lambda>x. Ds (flow0 (fst x) (snd x)) o\<^sub>L flowderiv (fst x) (snd x))"
    by (auto intro!: continuous_intros)
  from return_time_returns[OF rt cls]
  have Z: "(case (x, ?t1) of (x, t) \<Rightarrow> s (flow0 x t)) = 0"
    by (auto simp: x)
  have I1: "blinfun_scaleR_left (inverse (Ds (flow0 x (?t1))(f (flow0 x (?t1))))) o\<^sub>L 
    ((Ds (flow0 (fst (x, return_time ?P x))
            (snd (x, return_time ?P x))) o\<^sub>L
       flowderiv (fst (x, return_time ?P x))
        (snd (x, return_time ?P x))) o\<^sub>L
      embed2_blinfun)
     = 1\<^sub>L"
    using Ds_through
    by (auto intro!: blinfun_eqI
        simp: rt flowderiv_def blinfun.bilinear_simps inverse_eq_divide poincare_map_def)
  have I2: "((Ds (flow0 (fst (x, return_time ?P x))
            (snd (x, return_time ?P x))) o\<^sub>L
       flowderiv (fst (x, return_time ?P x))
        (snd (x, return_time ?P x))) o\<^sub>L
      embed2_blinfun) o\<^sub>L blinfun_scaleR_left (inverse (Ds (flow0 x (?t1))(f (flow0 x (?t1)))))
     = 1\<^sub>L"
    using Ds_through
    by (auto intro!: blinfun_eqI
        simp: rt flowderiv_def blinfun.bilinear_simps inverse_eq_divide poincare_map_def)
  obtain u e where u:
      "s (flow0 x (u x)) = 0"
       "u x = return_time ?P x"
       "(\<And>sa. sa \<in> cball x e \<Longrightarrow> s (flow0 sa (u sa)) = 0)"
       "continuous_on (cball x e) u"
       "(\<lambda>t. (t, u t)) ` cball x e \<subseteq> Sigma Y existence_ivl0"
       "0 < e"
       "(u has_derivative
            blinfun_apply
             (- blinfun_scaleR_left
                 (inverse (blinfun_apply (Ds (poincare_map ?P x)) (f (poincare_map ?P x)))) o\<^sub>L
              (Ds (poincare_map ?P x) o\<^sub>L flowderiv x (return_time ?P x)) o\<^sub>L
              embed1_blinfun))
            (at x)"
       "(\<And>s. s \<in> cball x e \<Longrightarrow>
         Ds (flow0 s (u s)) o\<^sub>L flowderiv s (u s) o\<^sub>L embed2_blinfun \<in> invertibles_blinfun)"
      and unique: "(\<And>U v sa.
               (\<And>sa. sa \<in> U \<Longrightarrow> s (flow0 sa (v sa)) = 0) \<Longrightarrow>
               u x = v x \<Longrightarrow>
               continuous_on U v \<Longrightarrow> sa \<in> U \<Longrightarrow> x \<in> U \<Longrightarrow> U \<subseteq> cball x e \<Longrightarrow> connected U \<Longrightarrow> open U \<Longrightarrow> u sa = v sa)"
    apply (rule implicit_function_theorem_unique[where f="\<lambda>(x, t). s (flow0 x t)"
          and S="Sigma Y existence_ivl0", OF D xt1 \<open>open (Sigma Y _)\<close> order_refl C Z I1 I2])
     apply blast
    unfolding split_beta' fst_conv snd_conv poincare_map_def[symmetric]
    apply (rule)
    by (assumption+, blast)
  have u_rt: "u y = return_time ?P y" if "y \<in> ball x e \<inter> Y" for y
    apply (rule unique[of "ball x e \<inter> Y" "return_time ?P"])
    subgoal for y
      unfolding poincare_map_def[symmetric]
      using poincare_map_returns[OF Yr cls]
      by auto
    subgoal by (auto simp: u)
    subgoal using cY by (rule continuous_on_subset) auto
    subgoal using that by auto
    subgoal using x \<open>0 < e\<close> by auto
    subgoal by auto
    subgoal
      apply (rule convex_connected)
      apply (rule convex_Int)
       apply simp
      apply fact
      done
    subgoal by (auto intro!: open_Int \<open>open Y\<close>)
    done

  have *: "(- blinfun_scaleR_left
                 (inverse (blinfun_apply (Ds (poincare_map ?P x)) (f (poincare_map ?P x)))) o\<^sub>L
              (Ds (poincare_map ?P x) o\<^sub>L flowderiv x (return_time ?P x)) o\<^sub>L
              embed1_blinfun) =
    - blinfun_scaleR_left (inverse (blinfun_apply (Ds (poincare_map ?P x)) (f (poincare_map ?P x)))) o\<^sub>L
              (Ds (poincare_map ?P x) o\<^sub>L Dflow x (return_time ?P x))"
    by (auto intro!: blinfun_eqI simp: flowderiv_def)
  define e' where "e' = min e eY"
  have e'_eq: "ball x e' = ball x e \<inter> Y" by (auto simp: e'_def Y_def)
  have
    "0 < e'"
    "\<And>y. y \<in> ball x e' \<Longrightarrow> returns_to ?P y"
    "\<And>y. y \<in> ball x e' \<Longrightarrow> s (flow0 y (return_time ?P y)) = 0"
    "continuous_on (ball x e') (return_time ?P)"
    "(\<And>y. y \<in> ball x e' \<Longrightarrow> Ds (poincare_map ?P y) o\<^sub>L flowderiv y (return_time ?P y) o\<^sub>L embed2_blinfun \<in> invertibles_blinfun)"
    "(\<And>U v sa.
       (\<And>sa. sa \<in> U \<Longrightarrow> s (flow0 sa (v sa)) = 0) \<Longrightarrow>
       return_time ?P x = v x \<Longrightarrow>
       continuous_on U v \<Longrightarrow> sa \<in> U \<Longrightarrow> x \<in> U \<Longrightarrow> U \<subseteq> ball x e' \<Longrightarrow> connected U \<Longrightarrow> open U \<Longrightarrow> return_time ?P sa = v sa)"
    "(return_time ?P has_derivative blinfun_apply
             (- blinfun_scaleR_left
                 (inverse (blinfun_apply (Ds (poincare_map ?P x)) (f (poincare_map ?P x)))) o\<^sub>L
              (Ds (poincare_map ?P x) o\<^sub>L flowderiv x (return_time ?P x)) o\<^sub>L
              embed1_blinfun))
            (at x)"
    unfolding e'_eq
    subgoal by (auto simp: e'_def \<open>0 < e\<close> \<open>0 < eY\<close>)
    subgoal by (rule Yr) auto
    subgoal for y
      unfolding poincare_map_def[symmetric]
      using poincare_map_returns[OF Yr cls]
      by auto
    subgoal using cY by (rule continuous_on_subset) auto
    subgoal premises prems for y
      unfolding poincare_map_def
      unfolding u_rt[OF prems, symmetric]
      apply (rule u)
      using prems by auto
    subgoal premises prems for U v t
      apply (subst u_rt[symmetric])
      subgoal using prems by force
      apply (rule unique[of U v])
      subgoal by fact
      subgoal by (auto simp: u prems)
      subgoal by fact
      subgoal by fact
      subgoal by fact
      subgoal using prems by auto
      subgoal by fact
      subgoal by fact
      done
    subgoal
    proof -
      have "\<forall>\<^sub>F x' in at x. x' \<in> ball x e'"
        using eventually_at_ball[OF \<open>0 < e'\<close>]
        by eventually_elim simp
      then have "\<forall>\<^sub>F x' in at x. u x' = return_time ?P x'"
        unfolding e'_eq
        by eventually_elim (rule u_rt, auto)
      from u(7) this
      show ?thesis
        by (rule has_derivative_transform_eventually) (auto simp: u)
    qed
    done
  then show ?thesis unfolding * ..
qed

lemma return_time_has_derivative:
  fixes s::"'a::euclidean_space \<Rightarrow> real"
  assumes rt: "returns_to {x \<in> S. s x = 0} x" (is "returns_to ?P _")
  assumes cS: "closed S"
  assumes Ds: "\<And>x. (s has_derivative blinfun_apply (Ds x)) (at x)"
  assumes DsC: "\<And>x. isCont Ds x"
  assumes Ds_through: "(Ds (poincare_map ?P x)) (f (poincare_map ?P x)) \<noteq> 0"
  assumes eventually_inside: "\<forall>\<^sub>F x in at (poincare_map {x \<in> S. s x = 0} x). s x = 0 \<longrightarrow> x \<in> S"
  assumes outside: "x \<notin> S \<or> s x \<noteq> 0"
  shows "(return_time ?P has_derivative
  - blinfun_scaleR_left (inverse ((Ds (poincare_map ?P x)) (f (poincare_map ?P x)))) o\<^sub>L
      (Ds (poincare_map ?P x) o\<^sub>L Dflow x (return_time ?P x)))
            (at x)"
  using return_time_implicit_functionE[OF assms] by blast

lemma return_time_plane_has_derivative_blinfun:
  assumes rt: "returns_to {x \<in> S. x \<bullet> i = c} x" (is "returns_to ?P _")
  assumes cS: "closed S"
  assumes fnz: "f (poincare_map ?P x) \<bullet> i \<noteq> 0"
  assumes eventually_inside: "\<forall>\<^sub>F x in at (poincare_map ?P x). x \<bullet> i = c \<longrightarrow> x \<in> S"
  assumes outside: "x \<notin> S \<or> x \<bullet> i \<noteq> c"
  shows "(return_time ?P has_derivative
    (- blinfun_scaleR_left (inverse ((blinfun_inner_left i) (f (poincare_map ?P x)))) o\<^sub>L
      (blinfun_inner_left i o\<^sub>L Dflow x (return_time ?P x)))) (at x)"
proof -
  have rt: "returns_to {x \<in> S. x \<bullet> i - c = 0} x"
    using rt by auto
  have D: "((\<lambda>x. x \<bullet> i - c) has_derivative blinfun_inner_left i) (at x)" for x
    by (auto intro!: derivative_eq_intros)
  have DC: "(\<And>x. isCont (\<lambda>x. blinfun_inner_left i) x)"
    by (auto intro!: continuous_intros)
  have nz: "blinfun_apply (blinfun_inner_left i) (f (poincare_map {x \<in> S. x \<bullet> i - c = 0} x)) \<noteq> 0"
    using fnz by (auto )
  from cS have cS: "closed S"by auto
  have out: "x \<notin> S \<or> x \<bullet> i - c \<noteq> 0" using outside by simp
  from eventually_inside
  have eventually_inside: "\<forall>\<^sub>F x in at (poincare_map {x \<in> S. x \<bullet> i - c = 0} x). x \<bullet> i - c = 0 \<longrightarrow> x \<in> S"
    by auto
  from return_time_has_derivative[OF rt cS D DC nz eventually_inside out]
  show ?thesis
    by auto
qed

lemma return_time_plane_has_derivative:
  assumes rt: "returns_to {x \<in> S. x \<bullet> i = c} x" (is "returns_to ?P _")
  assumes cS: "closed S"
  assumes fnz: "f (poincare_map ?P x) \<bullet> i \<noteq> 0"
  assumes eventually_inside: "\<forall>\<^sub>F x in at (poincare_map ?P x). x \<bullet> i = c \<longrightarrow> x \<in> S"
  assumes outside: "x \<notin> S \<or> x \<bullet> i \<noteq> c"
  shows "(return_time ?P has_derivative
    (\<lambda>h. - (Dflow x (return_time ?P x)) h \<bullet> i / (f (poincare_map ?P x) \<bullet> i))) (at x)"
  by (rule return_time_plane_has_derivative_blinfun[OF assms, THEN has_derivative_eq_rhs])
    (auto simp: blinfun.bilinear_simps flowderiv_def inverse_eq_divide intro!: ext)

definition "Dpoincare_map i c S x =
  (\<lambda>h. (Dflow x (return_time {x \<in> S. x \<bullet> i = c} x)) h -
      ((Dflow x (return_time {x \<in> S. x \<bullet> i = c} x)) h \<bullet> i /
        (f (poincare_map {x \<in> S. x \<bullet> i = c} x) \<bullet> i)) *\<^sub>R f (poincare_map {x \<in> S. x \<bullet> i = c} x))"

definition "Dpoincare_map' i c S x =
  Dflow x (return_time {x \<in> S. x \<bullet> i - c = 0} x) -
  (blinfun_scaleR_left (f (poincare_map {x \<in> S. x \<bullet> i = c} x)) o\<^sub>L
    (blinfun_scaleR_left (inverse ((f (poincare_map {x \<in> S. x \<bullet> i = c} x) \<bullet> i))) o\<^sub>L
    (blinfun_inner_left i o\<^sub>L Dflow x (return_time {x \<in> S. x \<bullet> i - c = 0} x))))"

theorem poincare_map_plane_has_derivative:
  assumes rt: "returns_to {x \<in> S. x \<bullet> i = c} x" (is "returns_to ?P _")
  assumes cS: "closed S"
  assumes fnz: "f (poincare_map ?P x) \<bullet> i \<noteq> 0"
  assumes eventually_inside: "\<forall>\<^sub>F x in at (poincare_map ?P x). x \<bullet> i = c \<longrightarrow> x \<in> S"
  assumes outside: "x \<notin> S \<or> x \<bullet> i \<noteq> c"
  notes [derivative_intros] = return_time_plane_has_derivative[OF rt cS fnz eventually_inside outside]
  shows "(poincare_map ?P has_derivative Dpoincare_map' i c S x) (at x)"
  unfolding poincare_map_def Dpoincare_map'_def
  using fnz outside
  by (auto intro!: derivative_eq_intros return_time_exivl assms ext closed_levelset_within
      continuous_intros
      simp: flowderiv_eq poincare_map_def blinfun.bilinear_simps inverse_eq_divide algebra_simps)

end

end
