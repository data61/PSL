section \<open>Flow\<close>
theory Flow
imports
  Picard_Lindeloef_Qualitative
  "HOL-Library.Diagonal_Subsequence"
  "../Library/Bounded_Linear_Operator"
  "../Library/Multivariate_Taylor"
  "../Library/Interval_Integral_HK"
begin

text \<open>TODO: extend theorems for dependence on initial time\<close>

subsection \<open>simp rules for integrability (TODO: move)\<close>

lemma blinfun_ext: "x = y \<longleftrightarrow> (\<forall>i. blinfun_apply x i = blinfun_apply y i)"
  by transfer auto

notation id_blinfun ("1\<^sub>L")

lemma blinfun_inverse_left:
  fixes f::"'a::euclidean_space \<Rightarrow>\<^sub>L 'a" and f'
  shows "f o\<^sub>L f' = 1\<^sub>L \<longleftrightarrow> f' o\<^sub>L f = 1\<^sub>L"
  by transfer
    (auto dest!: bounded_linear.linear simp: id_def[symmetric]
      linear_inverse_left)

lemma onorm_zero_blinfun[simp]: "onorm (blinfun_apply 0) = 0"
  by transfer (simp add: onorm_zero)

lemma blinfun_compose_1_left[simp]: "x o\<^sub>L 1\<^sub>L = x"
  and blinfun_compose_1_right[simp]: "1\<^sub>L o\<^sub>L y = y"
  by (auto intro!: blinfun_eqI)


named_theorems integrable_on_simps

lemma integrable_on_refl_ivl[intro, simp]: "g integrable_on {b .. (b::'b::ordered_euclidean_space)}"
  and integrable_on_refl_closed_segment[intro, simp]: "h integrable_on closed_segment a a"
  using integrable_on_refl by auto

lemma integrable_const_ivl_closed_segment[intro, simp]: "(\<lambda>x. c) integrable_on closed_segment a (b::real)"
  by (auto simp: closed_segment_eq_real_ivl)

lemma integrable_ident_ivl[intro, simp]: "(\<lambda>x. x) integrable_on closed_segment a (b::real)"
  and integrable_ident_cbox[intro, simp]: "(\<lambda>x. x) integrable_on cbox a (b::real)"
  by (auto simp: closed_segment_eq_real_ivl ident_integrable_on)

lemma content_closed_segment_real:
  fixes a b::real
  shows "content (closed_segment a b) = abs (b - a)"
  by (auto simp: closed_segment_eq_real_ivl)

lemma integral_const_closed_segment:
  fixes a b::real
  shows "integral (closed_segment a b) (\<lambda>x. c) = abs (b - a) *\<^sub>R c"
  by (auto simp: closed_segment_eq_real_ivl content_closed_segment_real)

lemmas [integrable_on_simps] =
  integrable_on_empty \<comment> \<open>empty\<close>
  integrable_on_refl integrable_on_refl_ivl integrable_on_refl_closed_segment \<comment> \<open>singleton\<close>
  integrable_const integrable_const_ivl integrable_const_ivl_closed_segment \<comment> \<open>constant\<close>
  ident_integrable_on integrable_ident_ivl integrable_ident_cbox \<comment> \<open>identity\<close>

lemma integrable_cmul_real:
  fixes K::real
  shows "f integrable_on X \<Longrightarrow> (\<lambda>x. K * f x) integrable_on X "
  unfolding real_scaleR_def[symmetric]
  by (rule integrable_cmul)

lemmas [integrable_on_simps] =
  integrable_0
  integrable_neg
  integrable_cmul
  integrable_cmul_real
  integrable_on_cmult_iff
  integrable_on_cmult_left
  integrable_on_cmult_right
  integrable_on_cdivide
  integrable_on_cmult_iff
  integrable_on_cmult_left_iff
  integrable_on_cmult_right_iff
  integrable_on_cdivide_iff
  integrable_diff
  integrable_add
  integrable_sum

lemma dist_cancel_add1: "dist (t0 + et) t0 = norm et"
  by (simp add: dist_norm)

lemma double_nonneg_le:
  fixes a::real
  shows "a * 2 \<le> b \<Longrightarrow> a \<ge> 0 \<Longrightarrow> a \<le> b"
  by arith


subsection \<open>Nonautonomous IVP on maximal existence interval\<close>

context ll_on_open_it
begin

context
fixes x0
assumes iv_defined: "t0 \<in> T" "x0 \<in> X"
begin

lemmas closed_segment_iv_subset_domain = closed_segment_subset_domainI[OF iv_defined(1)]

lemma
  local_unique_solutions:
  obtains t u L
  where
    "0 < t" "0 < u"
    "cball t0 t \<subseteq> existence_ivl t0 x0"
    "cball x0 (2 * u) \<subseteq> X"
    "\<And>t'. t' \<in> cball t0 t \<Longrightarrow> L-lipschitz_on (cball x0 (2 * u)) (f t')"
    "\<And>x. x \<in> cball x0 u \<Longrightarrow> (flow t0 x usolves_ode f from t0) (cball t0 t) (cball x u)"
    "\<And>x. x \<in> cball x0 u \<Longrightarrow> cball x u \<subseteq> X"
proof -
  from local_unique_solution[OF iv_defined] obtain et ex B L
    where "0 < et" "0 < ex" "cball t0 et \<subseteq> T" "cball x0 ex \<subseteq> X"
      "unique_on_cylinder t0 (cball t0 et) x0 ex f B L"
    by metis
  then interpret cyl: unique_on_cylinder t0 "cball t0 et" x0 ex "cball x0 ex" f B L
    by auto

  from cyl.solution_solves_ode order_refl \<open>cball x0 ex \<subseteq> X\<close>
  have "(cyl.solution solves_ode f) (cball t0 et) X"
    by (rule solves_ode_on_subset)
  then have "cball t0 et \<subseteq> existence_ivl t0 x0"
    by (rule existence_ivl_maximal_interval) (insert \<open>cball t0 et \<subseteq> T\<close> \<open>0 < et\<close>, auto)

  have "cball t0 et = {t0 - et .. t0 + et}"
    using \<open>et > 0\<close> by (auto simp: dist_real_def)
  then have cylbounds[simp]: "cyl.tmin = t0 - et" "cyl.tmax = t0 + et"
    unfolding cyl.tmin_def cyl.tmax_def
    using \<open>0 < et\<close>
    by auto

  define et' where "et' \<equiv> et / 2"
  define ex' where "ex' \<equiv> ex / 2"

  have "et' > 0" "ex' > 0" using \<open>0 < et\<close> \<open>0 < ex\<close> by (auto simp: et'_def ex'_def)
  moreover
  from \<open>cball t0 et \<subseteq> existence_ivl t0 x0\<close> have "cball t0 et' \<subseteq> existence_ivl t0 x0"
    by (force simp: et'_def dest!: double_nonneg_le)
  moreover
  from this have "cball t0 et' \<subseteq> T" using existence_ivl_subset[of x0] by simp
  have  "cball x0 (2 * ex') \<subseteq> X" "\<And>t'. t' \<in> cball t0 et' \<Longrightarrow> L-lipschitz_on (cball x0 (2 * ex')) (f t')"
    using cyl.lipschitz \<open>0 < et\<close> \<open>cball x0 ex \<subseteq> X\<close>
    by (auto simp: ex'_def et'_def intro!:)
  moreover
  {
    fix x0'::'a
    assume x0': "x0' \<in> cball x0 ex'"
    {
      fix b
      assume d: "dist x0' b \<le> ex'"
      have "dist x0 b \<le> dist x0 x0' + dist x0' b"
        by (rule dist_triangle)
      also have "\<dots> \<le> ex' + ex'"
        using x0' d by simp
      also have "\<dots> \<le> ex" by (simp add: ex'_def)
      finally have "dist x0 b \<le> ex" .
    } note triangle = this
    have subs1: "cball t0 et' \<subseteq> cball t0 et"
      and subs2: "cball x0' ex' \<subseteq> cball x0 ex"
      and subs: "cball t0 et' \<times> cball x0' ex' \<subseteq> cball t0 et \<times> cball x0 ex"
      using \<open>0 < ex\<close> \<open>0 < et\<close> x0'
      by (auto simp: ex'_def et'_def triangle dest!: double_nonneg_le)

    have subset_X: "cball x0' ex' \<subseteq> X"
      using \<open>cball x0 ex \<subseteq> X\<close> subs2 \<open>0 < ex'\<close> by force
    then have "x0' \<in> X" using \<open>0 < ex'\<close> by force
    have x0': "t0 \<in> T" "x0' \<in> X" by fact+
    have half_intros: "a \<le> ex' \<Longrightarrow> a \<le> ex" "a \<le> et' \<Longrightarrow> a \<le> et"
      and halfdiv_intro: "a * 2 \<le> ex / B \<Longrightarrow> a \<le> ex' / B" for a
      using \<open>0 < ex\<close> \<open>0 < et\<close>
      by (auto simp: ex'_def et'_def)

    interpret cyl': solution_in_cylinder t0 "cball t0 et'" x0' ex' f "cball x0' ex'" B
      using \<open>0 < et'\<close> \<open>0 < ex'\<close> \<open>0 < et\<close> cyl.norm_f cyl.continuous subs1 \<open>cball t0 et \<subseteq> T\<close>
      apply unfold_locales
      apply (auto simp: split_beta' dist_cancel_add1 intro!: triangle
        continuous_intros cyl.norm_f order_trans[OF _ cyl.e_bounded] halfdiv_intro)
      by (simp add: ex'_def et'_def dist_commute)

    interpret cyl': unique_on_cylinder t0 "cball t0 et'" x0' ex' "cball x0' ex'" f B L
      using cyl.lipschitz[simplified] subs subs1
      by (unfold_locales)
         (auto simp: triangle intro!: half_intros lipschitz_on_subset[OF _ subs2])
    from cyl'.solution_usolves_ode
    have "(flow t0 x0' usolves_ode f from t0) (cball t0 et') (cball x0' ex')"
      apply (rule usolves_ode_solves_odeI)
      subgoal
        apply (rule cyl'.solves_ode_on_subset_domain[where Y=X])
        subgoal
          apply (rule solves_ode_on_subset[where S="existence_ivl t0 x0'" and Y=X])
          subgoal by (rule flow_solves_ode[OF x0'])
          subgoal
            using subs2 \<open>cball x0 ex \<subseteq> X\<close> \<open>0 < et'\<close> \<open>cball t0 et' \<subseteq> T\<close>
            by (intro existence_ivl_maximal_interval[OF solves_ode_on_subset[OF cyl'.solution_solves_ode]])
              auto
          subgoal by force
          done
        subgoal by (force simp: \<open>x0' \<in> X\<close> iv_defined)
        subgoal using \<open>0 < et'\<close> by force
        subgoal by force
        subgoal by force
        done
      subgoal by (force simp: \<open>x0' \<in> X\<close> iv_defined cyl'.solution_iv)
      done
    note this subset_X
  } ultimately show thesis ..
qed

lemma Picard_iterate_mem_existence_ivlI:
  assumes "t \<in> T"
  assumes "compact C" "x0 \<in> C" "C \<subseteq> X"
  assumes "\<And>y s. s \<in> {t0 -- t} \<Longrightarrow> y t0 = x0 \<Longrightarrow> y \<in> {t0--s} \<rightarrow> C \<Longrightarrow> continuous_on {t0--s} y \<Longrightarrow>
      x0 + ivl_integral t0 s (\<lambda>t. f t (y t)) \<in> C"
  shows "t \<in> existence_ivl t0 x0" "\<And>s. s \<in> {t0 -- t} \<Longrightarrow> flow t0 x0 s \<in> C"
proof -
  have "{t0 -- t} \<subseteq> T"
    by (intro closed_segment_subset_domain iv_defined assms)
  from lipschitz_on_compact[OF compact_segment \<open>{t0 -- t} \<subseteq> T\<close> \<open>compact C\<close> \<open>C \<subseteq> X\<close>]
  obtain L where L: "\<And>s. s \<in> {t0 -- t} \<Longrightarrow> L-lipschitz_on C (f s)" by metis
  interpret uc: unique_on_closed t0 "{t0 -- t}" x0 f C L
    using assms closed_segment_iv_subset_domain
    by unfold_locales
      (auto intro!: L compact_imp_closed \<open>compact C\<close> continuous_on_f continuous_intros
        simp: split_beta)
  have "{t0 -- t} \<subseteq> existence_ivl t0 x0"
    using assms closed_segment_iv_subset_domain
    by (intro maximal_existence_flow[OF solves_ode_on_subset[OF uc.solution_solves_ode]])
      (auto simp: )
  thus "t \<in> existence_ivl t0 x0"
    using assms by auto
  show "flow t0 x0 s \<in> C" if "s \<in> {t0 -- t}" for s
  proof -
    have "flow t0 x0 s = uc.solution s" "uc.solution s \<in> C"
      using solves_odeD[OF uc.solution_solves_ode] that assms
      by (auto simp: closed_segment_iv_subset_domain
        intro!:  maximal_existence_flowI(2)[where K="{t0 -- t}"])
    thus ?thesis by simp
  qed
qed

lemma flow_has_vderiv_on: "(flow t0 x0 has_vderiv_on (\<lambda>t. f t (flow t0 x0 t))) (existence_ivl t0 x0)"
  by (rule solves_ode_vderivD[OF flow_solves_ode[OF iv_defined]])

lemmas flow_has_vderiv_on_compose[derivative_intros] =
  has_vderiv_on_compose2[OF flow_has_vderiv_on, THEN has_vderiv_on_eq_rhs]

end

lemma unique_on_intersection:
  assumes sols: "(x solves_ode f) U X" "(y solves_ode f) V X"
  assumes iv_mem: "t0 \<in> U" "t0 \<in> V" and subs: "U \<subseteq> T" "V \<subseteq> T"
  assumes ivls: "is_interval U" "is_interval V"
  assumes iv: "x t0 = y t0"
  assumes mem: "t \<in> U" "t \<in> V"
  shows "x t = y t"
proof -
  from
    maximal_existence_flow(2)[OF sols(1) refl          ivls(1) iv_mem(1) subs(1) mem(1)]
    maximal_existence_flow(2)[OF sols(2) iv[symmetric] ivls(2) iv_mem(2) subs(2) mem(2)]
  show ?thesis by simp
qed

lemma unique_solution:
  assumes sols: "(x solves_ode f) U X" "(y solves_ode f) U X"
  assumes iv_mem: "t0 \<in> U" and subs: "U \<subseteq> T"
  assumes ivls: "is_interval U"
  assumes iv: "x t0 = y t0"
  assumes mem: "t \<in> U"
  shows "x t = y t"
  by (metis unique_on_intersection assms)

lemma
  assumes s: "s \<in> existence_ivl t0 x0"
  assumes t: "t + s \<in> existence_ivl s (flow t0 x0 s)"
  shows flow_trans: "flow t0 x0 (s + t) = flow s (flow t0 x0 s) (s + t)"
    and existence_ivl_trans: "s + t \<in> existence_ivl t0 x0"
proof -
  note ll_on_open_it_axioms
  moreover
  from ll_on_open_it_axioms
  have iv_defined: "t0 \<in> T" "x0 \<in> X"
    and iv_defined': "s \<in> T" "flow t0 x0 s \<in> X"
    using ll_on_open_it.mem_existence_ivl_iv_defined s t
    by blast+

  have "{t0--s} \<subseteq> existence_ivl t0 x0"
    by (simp add: s segment_subset_existence_ivl iv_defined)

  have "s \<in> existence_ivl s (flow t0 x0 s)"
    by (rule ll_on_open_it.existence_ivl_initial_time; fact)
  have "{s--t + s} \<subseteq> existence_ivl s (flow t0 x0 s)"
    by (rule ll_on_open_it.segment_subset_existence_ivl; fact)

  have unique: "flow t0 x0 u = flow s (flow t0 x0 s) u"
    if "u \<in> {s--t + s}" "u \<in> {t0--s}" for u
    using
      ll_on_open_it_axioms
      ll_on_open_it.flow_solves_ode[OF ll_on_open_it_axioms iv_defined]
      ll_on_open_it.flow_solves_ode[OF ll_on_open_it_axioms iv_defined']
      s
    apply (rule ll_on_open_it.unique_on_intersection)
    using \<open>s \<in> existence_ivl s (flow t0 x0 s)\<close> existence_ivl_subset
      \<open>flow t0 x0 s \<in> X\<close> \<open>s \<in> T\<close> iv_defined s t ll_on_open_it.in_existence_between_zeroI
      that ll_on_open_it_axioms ll_on_open_it.mem_existence_ivl_subset
    by (auto simp: is_interval_existence_ivl)

  let ?un = "{t0 -- s} \<union> {s -- t + s}"
  let ?if = "\<lambda>t. if t \<in> {t0 -- s} then flow t0 x0 t else flow s (flow t0 x0 s) t"
  have "(?if solves_ode (\<lambda>t. if t \<in> {t0 -- s} then f t else f t)) ?un (X \<union> X)"
    apply (rule connection_solves_ode)
    subgoal by (rule solves_ode_on_subset[OF flow_solves_ode[OF iv_defined] \<open>{t0--s} \<subseteq> _\<close> order_refl])
    subgoal
      by (rule solves_ode_on_subset[OF ll_on_open_it.flow_solves_ode[OF ll_on_open_it_axioms iv_defined']
          \<open>{s--t + s} \<subseteq> _\<close> order_refl])
    subgoal by simp
    subgoal by simp
    subgoal by (rule unique) auto
    subgoal by simp
    done
  then have ifsol: "(?if solves_ode f) ?un X"
    by simp
  moreover
  have "?un \<subseteq> existence_ivl t0 x0"
    using existence_ivl_subset[of x0]
      ll_on_open_it.existence_ivl_subset[OF ll_on_open_it_axioms, of s "flow t0 x0 s"]
      \<open>{t0 -- s} \<subseteq> _\<close> \<open>{s--t + s} \<subseteq> _\<close>
    by (intro existence_ivl_maximal_interval[OF ifsol]) (auto intro!: is_real_interval_union)
  then show "s + t \<in> existence_ivl t0 x0"
    by (auto simp: ac_simps)
  have "(flow t0 x0 solves_ode f) ?un X"
    using \<open>{t0--s} \<subseteq> _\<close> \<open>{s -- t + s} \<subseteq> _\<close>
    by (intro solves_ode_on_subset[OF flow_solves_ode \<open>?un \<subseteq> _\<close> order_refl] iv_defined)
  moreover have "s \<in> ?un"
    by simp
  ultimately have "?if (s + t) = flow t0 x0 (s + t)"
    apply (rule ll_on_open_it.unique_solution)
    using existence_ivl_subset[of x0]
      ll_on_open_it.existence_ivl_subset[OF ll_on_open_it_axioms, of s "flow t0 x0 s"]
      \<open>{t0 -- s} \<subseteq> _\<close> \<open>{s--t + s} \<subseteq> _\<close>
    by (auto intro!: is_real_interval_union simp: ac_simps)
  with unique[of "s + t"]
  show "flow t0 x0 (s + t) = flow s (flow t0 x0 s) (s + t)"
    by (auto split: if_splits simp: ac_simps)
qed

lemma
  assumes t: "t \<in> existence_ivl t0 x0"
  shows flows_reverse: "flow t (flow t0 x0 t) t0 = x0"
    and existence_ivl_reverse: "t0 \<in> existence_ivl t (flow t0 x0 t)"
proof -
  have iv_defined: "t0 \<in> T" "x0 \<in> X"
    using mem_existence_ivl_iv_defined t by blast+
  show "t0 \<in> existence_ivl t (flow t0 x0 t)"
    using assms
    by (metis (no_types, hide_lams) closed_segment_commute closed_segment_subset_interval
        ends_in_segment(2) general.csol(2-4)
        general.existence_ivl_maximal_segment general.is_interval_existence_ivl
        is_interval_closed_segment_1 iv_defined ll_on_open_it.equals_flowI
        local.existence_ivl_initial_time local.flow_initial_time local.ll_on_open_it_axioms)
  then have "flow t (flow t0 x0 t) (t + (t0 - t)) = flow t0 x0 (t + (t0 - t))"
    by (intro flow_trans[symmetric]) (auto simp: t iv_defined)
  then show "flow t (flow t0 x0 t) t0 = x0"
    by (simp add: iv_defined)
qed

lemma flow_has_derivative:
  assumes "t \<in> existence_ivl t0 x0"
  shows "(flow t0 x0 has_derivative (\<lambda>i. i *\<^sub>R f t (flow t0 x0 t))) (at t)"
proof -
  have "(flow t0 x0 has_derivative (\<lambda>i. i *\<^sub>R f t (flow t0 x0 t))) (at t within existence_ivl t0 x0)"
    using flow_has_vderiv_on
    by (auto simp: has_vderiv_on_def has_vector_derivative_def assms mem_existence_ivl_iv_defined[OF assms])
  then show ?thesis
    by (simp add: at_within_open[OF assms open_existence_ivl])
qed


lemma flow_has_vector_derivative:
  assumes "t \<in> existence_ivl t0 x0"
  shows "(flow t0 x0 has_vector_derivative f t (flow t0 x0 t)) (at t)"
  using flow_has_derivative[OF assms]
  by (simp add: has_vector_derivative_def)

lemma flow_has_vector_derivative_at_0:
  assumes"t \<in> existence_ivl t0 x0"
  shows "((\<lambda>h. flow t0 x0 (t + h)) has_vector_derivative f t (flow t0 x0 t)) (at 0)"
proof -
  from flow_has_vector_derivative[OF assms]
  have
    "((+) t has_vector_derivative 1) (at 0)"
    "(flow t0 x0 has_vector_derivative f t (flow t0 x0 t)) (at (t + 0))"
    by (auto intro!: derivative_eq_intros)
  from vector_diff_chain_at[OF this]
  show ?thesis by (simp add: o_def)
qed

lemma
  assumes "t \<in> existence_ivl t0 x0"
  shows closed_segment_subset_existence_ivl: "closed_segment t0 t \<subseteq> existence_ivl t0 x0"
    and ivl_subset_existence_ivl: "{t0 .. t} \<subseteq> existence_ivl t0 x0"
    and ivl_subset_existence_ivl': "{t .. t0} \<subseteq> existence_ivl t0 x0"
  using assms in_existence_between_zeroI
  by (auto simp: closed_segment_eq_real_ivl)

lemma flow_fixed_point:
  assumes t: "t \<in> existence_ivl t0 x0"
  shows "flow t0 x0 t = x0 + ivl_integral t0 t (\<lambda>t. f t (flow t0 x0 t))"
proof -
  have "(flow t0 x0 has_vderiv_on (\<lambda>s. f s (flow t0 x0 s))) {t0 -- t}"
    using closed_segment_subset_existence_ivl[OF t]
    by (auto intro!: has_vector_derivative_at_within flow_has_vector_derivative
      simp: has_vderiv_on_def)
  from fundamental_theorem_of_calculus_ivl_integral[OF this]
  have "((\<lambda>t. f t (flow t0 x0 t)) has_ivl_integral flow t0 x0 t - x0) t0 t"
    by (simp add: mem_existence_ivl_iv_defined[OF assms])
  from this[THEN ivl_integral_unique]
  show ?thesis by (simp add: )
qed

lemma flow_continuous: "t \<in> existence_ivl t0 x0 \<Longrightarrow> continuous (at t) (flow t0 x0)"
  by (metis has_derivative_continuous flow_has_derivative)

lemma flow_tendsto: "t \<in> existence_ivl t0 x0 \<Longrightarrow> (ts \<longlongrightarrow> t) F \<Longrightarrow>
    ((\<lambda>s. flow t0 x0 (ts s)) \<longlongrightarrow> flow t0 x0 t) F"
  by (rule isCont_tendsto_compose[OF flow_continuous])

lemma flow_continuous_on: "continuous_on (existence_ivl t0 x0) (flow t0 x0)"
  by (auto intro!: flow_continuous continuous_at_imp_continuous_on)

lemma flow_continuous_on_intro:
  "continuous_on s g \<Longrightarrow>
  (\<And>xa. xa \<in> s \<Longrightarrow> g xa \<in> existence_ivl t0 x0) \<Longrightarrow>
  continuous_on s (\<lambda>xa. flow t0 x0 (g xa))"
  by (auto intro!: continuous_on_compose2[OF flow_continuous_on])

lemma f_flow_continuous:
  assumes "t \<in> existence_ivl t0 x0"
  shows "isCont (\<lambda>t. f t (flow t0 x0 t)) t"
  by (rule continuous_on_interior)
    (insert existence_ivl_subset assms,
      auto intro!: flow_in_domain flow_continuous_on continuous_intros
        simp: interior_open open_existence_ivl)

lemma exponential_initial_condition:
  assumes y0: "t \<in> existence_ivl t0 y0"
  assumes z0: "t \<in> existence_ivl t0 z0"
  assumes "Y \<subseteq> X"
  assumes remain: "\<And>s. s \<in> closed_segment t0 t \<Longrightarrow> flow t0 y0 s \<in> Y"
    "\<And>s. s \<in> closed_segment t0 t \<Longrightarrow> flow t0 z0 s \<in> Y"
  assumes lipschitz: "\<And>s. s \<in> closed_segment t0 t \<Longrightarrow> K-lipschitz_on Y (f s)"
  shows "norm (flow t0 y0 t - flow t0 z0 t) \<le> norm (y0 - z0) * exp ((K + 1) * abs (t - t0))"
proof cases
  assume "y0 = z0"
  thus ?thesis
    by simp
next
  assume ne: "y0 \<noteq> z0"
  define K' where "K' \<equiv> K + 1"
  from lipschitz have "K'-lipschitz_on Y (f s)" if "s \<in> {t0 -- t}" for s
    using that
    by (auto simp: lipschitz_on_def K'_def
      intro!: order_trans[OF _ mult_right_mono[of K "K + 1"]])

  from mem_existence_ivl_iv_defined[OF y0] mem_existence_ivl_iv_defined[OF z0]
  have "t0 \<in> T" and inX: "y0 \<in> X" "z0 \<in> X" by auto

  from remain[of t0] inX \<open>t0 \<in> T \<close> have "y0 \<in> Y" "z0 \<in> Y" by auto

  define v where "v \<equiv> \<lambda>t. norm (flow t0 y0 t - flow t0 z0 t)"
  {
    fix s
    assume s: "s \<in> {t0 -- t}"
    with s
      closed_segment_subset_existence_ivl[OF y0]
      closed_segment_subset_existence_ivl[OF z0]
    have
      y0': "s \<in> existence_ivl t0 y0" and
      z0': "s \<in> existence_ivl t0 z0"
      by (auto simp: closed_segment_eq_real_ivl)
    have integrable:
      "(\<lambda>t. f t (flow t0 y0 t)) integrable_on {t0--s}"
      "(\<lambda>t. f t (flow t0 z0 t)) integrable_on {t0--s}"
      using closed_segment_subset_existence_ivl[OF y0']
        closed_segment_subset_existence_ivl[OF z0']
        \<open>y0 \<in> X\<close> \<open>z0 \<in> X\<close> \<open>t0 \<in> T\<close>
      by (auto intro!: continuous_at_imp_continuous_on f_flow_continuous
        integrable_continuous_closed_segment)
    hence int: "flow t0 y0 s - flow t0 z0 s =
        y0 - z0 + ivl_integral t0 s (\<lambda>t. f t (flow t0 y0 t) - f t (flow t0 z0 t))"
      unfolding v_def
      using flow_fixed_point[OF y0'] flow_fixed_point[OF z0']
        s
      by (auto simp: algebra_simps ivl_integral_diff)
    have "v s \<le> v t0 + K' *  integral {t0 -- s} (\<lambda>t. v t)"
      using closed_segment_subset_existence_ivl[OF y0'] closed_segment_subset_existence_ivl[OF z0'] s
        using closed_segment_closed_segment_subset[OF _ _ s, of _ t0, simplified]
      by (subst integral_mult)
        (auto simp: integral_mult v_def int inX \<open>t0 \<in> T\<close>
          simp del: Henstock_Kurzweil_Integration.integral_mult_right
          intro!: norm_triangle_le ivl_integral_norm_bound_integral
            integrable_continuous_closed_segment continuous_intros
            continuous_at_imp_continuous_on flow_continuous f_flow_continuous
            lipschitz_on_normD[OF \<open>_ \<Longrightarrow> K'-lipschitz_on _ _\<close>] remain)
  } note le = this
  have cont: "continuous_on {t0 -- t} v"
    using closed_segment_subset_existence_ivl[OF y0] closed_segment_subset_existence_ivl[OF z0] inX
    by (auto simp: v_def \<open>t0 \<in> T\<close>
      intro!: continuous_at_imp_continuous_on continuous_intros flow_continuous)
  have nonneg: "\<And>t. v t \<ge> 0"
    by (auto simp: v_def)
  from ne have pos: "v t0 > 0"
    by (auto simp: v_def \<open>t0 \<in> T\<close> inX)
  have lippos: "K' > 0"
  proof -
    have "0 \<le> dist (f t0 y0) (f t0 z0)" by simp
    also from lipschitz_onD[OF lipschitz \<open>y0 \<in> Y\<close> \<open>z0 \<in> Y\<close>, of t0]ne
    have "\<dots> \<le> K * dist y0 z0"
      by simp
    finally have "0 \<le> K"
      by (metis dist_le_zero_iff ne zero_le_mult_iff)
    thus ?thesis by (simp add: K'_def)
  qed
  from le cont nonneg pos \<open>0 < K'\<close>
  have "v t \<le> v t0 * exp (K' * abs (t - t0))"
    by (rule gronwall_general_segment) simp_all
  thus ?thesis
    by (simp add: v_def K'_def \<open>t0 \<in> T\<close> inX)
qed

lemma
  existence_ivl_cballs:
  assumes iv_defined: "t0 \<in> T" "x0 \<in> X"
  obtains t u L
  where
    "\<And>y. y \<in> cball x0 u \<Longrightarrow> cball t0 t \<subseteq> existence_ivl t0 y"
    "\<And>s y. y \<in> cball x0 u \<Longrightarrow> s \<in> cball t0 t \<Longrightarrow> flow t0 y s \<in> cball y u"
    "L-lipschitz_on (cball t0 t\<times>cball x0 u) (\<lambda>(t, x). flow t0 x t)"
    "\<And>y. y \<in> cball x0 u \<Longrightarrow> cball y u \<subseteq> X"
    "0 < t" "0 < u"
proof -
  note iv_defined
  from local_unique_solutions[OF this]
  obtain t u L where tu: "0 < t" "0 < u"
    and subsT: "cball t0 t \<subseteq> existence_ivl t0 x0"
    and subs': "cball x0 (2 * u) \<subseteq> X"
    and lipschitz: "\<And>s. s \<in> cball t0 t \<Longrightarrow> L-lipschitz_on (cball x0 (2*u)) (f s)"
    and usol: "\<And>y. y \<in> cball x0 u \<Longrightarrow> (flow t0 y usolves_ode f from t0) (cball t0 t) (cball y u)"
    and subs: "\<And>y. y \<in> cball x0 u \<Longrightarrow> cball y u \<subseteq> X"
    by metis
  {
    fix y assume y: "y \<in> cball x0 u"
    from subs[OF y] \<open>0 < u\<close> have "y \<in> X" by auto
    note iv' = \<open>t0 \<in> T\<close> \<open>y \<in> X\<close>
    from usol[OF y, THEN usolves_odeD(1)]
    have sol1: "(flow t0 y solves_ode f) (cball t0 t) (cball y u)" .
    from sol1 order_refl subs[OF y]
    have sol: "(flow t0 y solves_ode f) (cball t0 t) X"
      by (rule solves_ode_on_subset)
    note * = maximal_existence_flow[OF sol flow_initial_time
        is_interval_cball_1 _ order_trans[OF subsT existence_ivl_subset],
        unfolded centre_in_cball, OF iv' less_imp_le[OF \<open>0 < t\<close>]]
    have eivl: "cball t0 t \<subseteq> existence_ivl t0 y"
      by (rule *)
    have "flow t0 y s \<in> cball y u" if "s \<in> cball t0 t" for s
      by (rule solves_odeD(2)[OF sol1 that])
    note eivl this
  } note * = this
  note *
  moreover
  have cont_on_f_flow:
    "\<And>x1 S. S \<subseteq> cball t0 t \<Longrightarrow> x1 \<in> cball x0 u \<Longrightarrow> continuous_on S (\<lambda>t. f t (flow t0 x1 t))"
    using subs[of x0] \<open>u > 0\<close> *(1) iv_defined
    by (auto intro!: continuous_at_imp_continuous_on f_flow_continuous)
  have "bounded ((\<lambda>(t, x). f t x) ` (cball t0 t \<times> cball x0 (2 * u)))"
    using subs' subsT existence_ivl_subset[of x0]
    by (auto intro!: compact_imp_bounded compact_continuous_image compact_Times
      continuous_intros simp: split_beta')
  then obtain B where B: "\<And>s y. s \<in> cball t0 t \<Longrightarrow> y \<in> cball x0 (2 * u) \<Longrightarrow> norm (f s y) \<le> B" "B > 0"
    by (auto simp: bounded_pos cball_def)
  have flow_in_cball: "flow t0 x1 s \<in> cball x0 (2 * u)"
    if s: "s \<in> cball t0 t" and x1: "x1 \<in> cball x0 u"
    for s::real and x1
  proof -
    from *(2)[OF x1 s] have "flow t0 x1 s \<in> cball x1 u" .
    also have "\<dots> \<subseteq> cball x0 (2 * u)"
      using x1
      by (auto intro!: dist_triangle_le[OF add_mono, of _ x1 u _ u, simplified]
        simp: dist_commute)
    finally show ?thesis .
  qed
  have "(B + exp ((L + 1) * \<bar>t\<bar>))-lipschitz_on (cball t0 t\<times>cball x0 u) (\<lambda>(t, x). flow t0 x t)"
  proof (rule lipschitz_onI, safe)
    fix t1 t2 :: real and x1 x2
    assume t1: "t1 \<in> cball t0 t" and t2: "t2 \<in> cball t0 t"
      and x1: "x1 \<in> cball x0 u" and x2: "x2 \<in> cball x0 u"
    have t1_ex: "t1 \<in> existence_ivl t0 x1"
      and t2_ex: "t2 \<in> existence_ivl t0 x1" "t2 \<in> existence_ivl t0 x2"
      and "x1 \<in> cball x0 (2*u)" "x2 \<in> cball x0 (2*u)"
      using *(1)[OF x1] *(1)[OF x2] t1 t2 x1 x2 tu by auto
    have "dist (flow t0 x1 t1) (flow t0 x2 t2) \<le>
      dist (flow t0 x1 t1) (flow t0 x1 t2) + dist (flow t0 x1 t2) (flow t0 x2 t2)"
      by (rule dist_triangle)
    also have "dist (flow t0 x1 t2) (flow t0 x2 t2) \<le> dist x1 x2 * exp ((L + 1) * \<bar>t2 - t0\<bar>)"
      unfolding dist_norm
    proof (rule exponential_initial_condition[where Y = "cball x0 (2 * u)"])
      fix s assume "s \<in> closed_segment t0 t2" hence s: "s \<in> cball t0 t"
        using t2
        by (auto simp: dist_real_def closed_segment_eq_real_ivl split: if_split_asm)
      show "flow t0 x1 s \<in> cball x0 (2 * u)"
        by (rule flow_in_cball[OF s x1])
      show "flow t0 x2 s \<in> cball x0 (2 * u)"
        by (rule flow_in_cball[OF s x2])
      show "L-lipschitz_on (cball x0 (2 * u)) (f s)" if "s \<in> closed_segment t0 t2" for s
        using that centre_in_cball convex_contains_segment less_imp_le t2 tu(1)
        by (blast intro!: lipschitz)
    qed (fact)+
    also have "\<dots> \<le> dist x1 x2 * exp ((L + 1) * \<bar>t\<bar>)"
      using \<open>u > 0\<close> t2
      by (auto
        intro!: mult_left_mono add_nonneg_nonneg lipschitz[THEN lipschitz_on_nonneg]
        simp: cball_eq_empty cball_eq_sing' dist_real_def)
    also
    have "x1 \<in> X"
      using x1 subs[of x0] \<open>u > 0\<close>
      by auto
    have *: "\<bar>t0 - t1\<bar> \<le> t \<Longrightarrow> x \<in> {t0--t1} \<Longrightarrow> \<bar>t0 - x\<bar> \<le> t"
      "\<bar>t0 - t2\<bar> \<le> t \<Longrightarrow> x \<in> {t0--t2} \<Longrightarrow> \<bar>t0 - x\<bar> \<le> t"
      "\<bar>t0 - t1\<bar> \<le> t \<Longrightarrow> \<bar>t0 - t2\<bar> \<le> t \<Longrightarrow> x \<in> {t1--t2} \<Longrightarrow> \<bar>t0 - x\<bar> \<le> t"
      for x
      using t1 t2 t1_ex x1 flow_in_cball[OF _ x1]
      by (auto simp: closed_segment_eq_real_ivl split: if_splits)

    have integrable:
      "(\<lambda>t. f t (flow t0 x1 t)) integrable_on {t0--t1}"
      "(\<lambda>t. f t (flow t0 x1 t)) integrable_on {t0--t2}"
      "(\<lambda>t. f t (flow t0 x1 t)) integrable_on {t1--t2}"
      using t1 t2 t1_ex x1 flow_in_cball[OF _ x1]
      by (auto intro!: order_trans[OF integral_bound[where B=B]] cont_on_f_flow B
        integrable_continuous_closed_segment
        intro: *
        simp: dist_real_def integral_minus_sets')

    have *: "\<bar>t0 - t1\<bar> \<le> t \<Longrightarrow> \<bar>t0 - t2\<bar> \<le> t \<Longrightarrow> s \<in> {t1--t2} \<Longrightarrow> \<bar>t0 - s\<bar> \<le> t" for s
      by (auto simp: closed_segment_eq_real_ivl split: if_splits)
    note [simp] = t1_ex t2_ex \<open>x1 \<in> X\<close> integrable
    have "dist (flow t0 x1 t1) (flow t0 x1 t2) \<le> dist t1 t2 * B"
      using t1 t2 x1 flow_in_cball[OF _ x1] \<open>t0 \<in> T\<close>
        ivl_integral_combine[of "\<lambda>t. f t (flow t0 x1 t)" t2 t0 t1]
        ivl_integral_combine[of "\<lambda>t. f t (flow t0 x1 t)" t1 t0 t2]
      by (auto simp: flow_fixed_point dist_norm add.commute closed_segment_commute
          norm_minus_commute ivl_integral_minus_sets' ivl_integral_minus_sets
        intro!: order_trans[OF ivl_integral_bound[where B=B]] cont_on_f_flow B dest: *)
    finally
    have "dist (flow t0 x1 t1) (flow t0 x2 t2) \<le>
        dist t1 t2 * B + dist x1 x2 * exp ((L + 1) * \<bar>t\<bar>)"
      by arith
    also have "\<dots> \<le> dist (t1, x1) (t2, x2) * B + dist (t1, x1) (t2, x2) * exp ((L + 1) * \<bar>t\<bar>)"
      using \<open>B > 0\<close>
      by (auto intro!: add_mono mult_right_mono simp: dist_prod_def)
    finally show "dist (flow t0 x1 t1) (flow t0 x2 t2)
       \<le> (B + exp ((L + 1) * \<bar>t\<bar>)) * dist (t1, x1) (t2, x2)"
      by (simp add: algebra_simps)
  qed (simp add: \<open>0 < B\<close> less_imp_le)
  ultimately
  show thesis using subs tu ..
qed

context
fixes x0
assumes iv_defined: "t0 \<in> T" "x0 \<in> X"
begin

lemma existence_ivl_notempty: "existence_ivl t0 x0 \<noteq> {}"
  using existence_ivl_initial_time iv_defined
  by auto

lemma initial_time_bounds:
  shows "bdd_above (existence_ivl t0 x0) \<Longrightarrow> t0 < Sup (existence_ivl t0 x0)" (is "?a \<Longrightarrow> _")
    and "bdd_below (existence_ivl t0 x0) \<Longrightarrow> Inf (existence_ivl t0 x0) < t0" (is "?b \<Longrightarrow> _")
proof -
  from local_unique_solutions[OF iv_defined]
  obtain te where te: "te > 0" "cball t0 te \<subseteq> existence_ivl t0 x0"
    by metis
  then
  show "t0 < Sup (existence_ivl t0 x0)" if bdd: "bdd_above (existence_ivl t0 x0)"
    using less_cSup_iff[OF existence_ivl_notempty bdd, of t0] iv_defined
    by (auto simp: dist_real_def intro!: bexI[where x="t0 + te"])

  from te show "Inf (existence_ivl t0 x0) < t0" if bdd: "bdd_below (existence_ivl t0 x0)"
    unfolding cInf_less_iff[OF existence_ivl_notempty bdd, of t0]
    by (auto simp: dist_real_def iv_defined intro!: bexI[where x="t0 - te"])
qed

lemma
  flow_leaves_compact_ivl_right:
  assumes bdd: "bdd_above (existence_ivl t0 x0)"
  defines "b \<equiv> Sup (existence_ivl t0 x0)"
  assumes "b \<in> T"
  assumes "compact K"
  assumes "K \<subseteq> X"
  obtains t where "t \<ge> t0" "t \<in> existence_ivl t0 x0" "flow t0 x0 t \<notin> K"
proof (atomize_elim, rule ccontr, auto)
  note iv_defined
  note ne = existence_ivl_notempty
  assume K[rule_format]: "\<forall>t. t \<in> existence_ivl t0 x0 \<longrightarrow> t0 \<le> t \<longrightarrow> flow t0 x0 t \<in> K"
  have b_upper: "t \<le> b" if "t \<in> existence_ivl t0 x0" for t
    unfolding b_def
    by (rule cSup_upper[OF that bdd])

  have less_b_iff: "y < b \<longleftrightarrow> (\<exists>x\<in>existence_ivl t0 x0. y < x)" for y
    unfolding b_def less_cSup_iff[OF ne bdd] ..
  have "t0 \<le> b"
    by (simp add: iv_defined b_upper)
  then have geI: "t \<in> {t0--<b} \<Longrightarrow> t0 \<le> t" for t
    by (auto simp: half_open_segment_real)
  have subset: "{t0 --< b} \<subseteq> existence_ivl t0 x0"
    using \<open>t0 \<le> b\<close> in_existence_between_zeroI
    by (auto simp: half_open_segment_real iv_defined less_b_iff)
  have sol: "(flow t0 x0 solves_ode f) {t0 --< b} K"
    apply (rule solves_odeI)
    apply (rule has_vderiv_on_subset[OF solves_odeD(1)[OF flow_solves_ode] subset])
    using subset iv_defined
    by (auto intro!: K geI)
  have cont: "continuous_on ({t0--b} \<times> K) (\<lambda>(t, x). f t x)"
    using \<open>K \<subseteq> X\<close> closed_segment_subset_domainI[OF iv_defined(1) \<open>b \<in> T\<close>]
    by (auto simp: split_beta intro!: continuous_intros)

  from initial_time_bounds(1)[OF bdd] have "t0 \<noteq> b" by (simp add: b_def)
  from solves_ode_half_open_segment_continuation[OF sol cont \<open>compact K\<close> \<open>t0 \<noteq> b\<close>]
  obtain l where lim: "(flow t0 x0 \<longlongrightarrow> l) (at b within {t0--<b})"
    and limsol: "((\<lambda>t. if t = b then l else flow t0 x0 t) solves_ode f) {t0--b} K" .
  have "b \<in> existence_ivl t0 x0"
    using \<open>t0 \<noteq> b\<close> closed_segment_subset_domainI[OF \<open>t0 \<in> T\<close> \<open>b \<in> T\<close>]
    by (intro existence_ivl_maximal_segment[OF solves_ode_on_subset[OF limsol order_refl \<open>K \<subseteq> X\<close>]])
      (auto simp: iv_defined)

  have "flow t0 x0 b \<in> X"
    by (simp add: \<open>b \<in> existence_ivl t0 x0\<close> flow_in_domain iv_defined)

  from ll_on_open_it.local_unique_solutions[OF ll_on_open_it_axioms \<open>b \<in> T\<close> \<open>flow t0 x0 b \<in> X\<close>]
  obtain e where "e > 0" "cball b e \<subseteq> existence_ivl b (flow t0 x0 b)"
    by metis
  then have "e + b \<in> existence_ivl b (flow t0 x0 b)"
    by (auto simp: dist_real_def)
  from existence_ivl_trans[OF \<open>b \<in> existence_ivl t0 x0\<close> \<open>e + b \<in> existence_ivl _ _\<close>]
  have "b + e \<in> existence_ivl t0 x0" .
  from b_upper[OF this] \<open>e > 0\<close>
  show False
    by simp
qed

lemma
  flow_leaves_compact_ivl_left:
  assumes bdd: "bdd_below (existence_ivl t0 x0)"
  defines "b \<equiv> Inf (existence_ivl t0 x0)"
  assumes "b \<in> T"
  assumes "compact K"
  assumes "K \<subseteq> X"
  obtains t where "t \<le> t0" "t \<in> existence_ivl t0 x0" "flow t0 x0 t \<notin> K"
proof -
  interpret rev: ll_on_open "(preflect t0 ` T)" "(\<lambda>t. - f (preflect t0 t))" X ..
  from antimono_preflect bdd have bdd_rev: "bdd_above (rev.existence_ivl t0 x0)"
    unfolding rev_existence_ivl_eq
    by (rule bdd_above_image_antimono)
  note ne = existence_ivl_notempty
  have "Sup (rev.existence_ivl t0 x0) = preflect t0 b"
    using continuous_at_Inf_antimono[OF antimono_preflect _ ne bdd]
    by (simp add: continuous_preflect b_def rev_existence_ivl_eq)
  then have Sup_mem: "Sup (rev.existence_ivl t0 x0) \<in> preflect t0 ` T"
    using \<open>b \<in> T\<close> by auto

  have rev_iv: "t0 \<in> preflect t0 ` T" "x0 \<in> X" using iv_defined by auto
  from rev.flow_leaves_compact_ivl_right[OF rev_iv bdd_rev Sup_mem \<open>compact K\<close> \<open>K \<subseteq> X\<close>]
  obtain t where "t0 \<le> t" "t \<in> rev.existence_ivl t0 x0" "rev.flow t0 x0 t \<notin> K" .

  then have "preflect t0 t \<le> t0" "preflect t0 t \<in> existence_ivl t0 x0" "flow t0 x0 (preflect t0 t) \<notin> K"
    by (auto simp: rev_existence_ivl_eq rev_flow_eq)
  thus ?thesis ..
qed

lemma
  sup_existence_maximal:
  assumes "\<And>t. t0 \<le> t \<Longrightarrow> t \<in> existence_ivl t0 x0 \<Longrightarrow> flow t0 x0 t \<in> K"
  assumes "compact K" "K \<subseteq> X"
  assumes "bdd_above (existence_ivl t0 x0)"
  shows "Sup (existence_ivl t0 x0) \<notin> T"
  using flow_leaves_compact_ivl_right[of K] assms by force

lemma
  inf_existence_minimal:
  assumes "\<And>t. t \<le> t0 \<Longrightarrow> t \<in> existence_ivl t0 x0 \<Longrightarrow> flow t0 x0 t \<in> K"
  assumes "compact K" "K \<subseteq> X"
  assumes "bdd_below (existence_ivl t0 x0)"
  shows "Inf (existence_ivl t0 x0) \<notin> T"
  using flow_leaves_compact_ivl_left[of K] assms
  by force

end

lemma
  subset_mem_compact_implies_subset_existence_interval:
  assumes ivl: "t0 \<in> T'" "is_interval T'" "T' \<subseteq> T"
  assumes iv_defined: "x0 \<in> X"
  assumes mem_compact: "\<And>t. t \<in> T' \<Longrightarrow> t \<in> existence_ivl t0 x0 \<Longrightarrow> flow t0 x0 t \<in> K"
  assumes K: "compact K" "K \<subseteq> X"
  shows "T' \<subseteq> existence_ivl t0 x0"
proof (rule ccontr)
  assume "\<not> T' \<subseteq> existence_ivl t0 x0"
  then obtain t' where t': "t' \<notin> existence_ivl t0 x0" "t' \<in> T'"
    by auto
  from assms have iv_defined: "t0 \<in> T" "x0 \<in> X" by auto
  show False
  proof (cases rule: not_in_connected_cases[OF connected_existence_ivl t'(1) existence_ivl_notempty[OF iv_defined]])
    assume bdd: "bdd_below (existence_ivl t0 x0)"
    assume t'_lower: "t' \<le> y" if "y \<in> existence_ivl t0 x0" for y
    have i: "Inf (existence_ivl t0 x0) \<in> T'"
      using initial_time_bounds[OF iv_defined] iv_defined
      apply -
      by (rule mem_is_intervalI[of _ t' t0])
        (auto simp: ivl t' bdd intro!: t'_lower cInf_greatest[OF existence_ivl_notempty[OF iv_defined]])
    have *: "t \<in> T'" if "t \<le> t0" "t \<in> existence_ivl t0 x0" for t
      by (rule mem_is_intervalI[OF \<open>is_interval T'\<close> i \<open>t0 \<in> T'\<close>]) (auto intro!: cInf_lower that bdd)
    from inf_existence_minimal[OF iv_defined mem_compact K bdd, OF *]
    show False using i ivl by auto
  next
    assume bdd: "bdd_above (existence_ivl t0 x0)"
    assume t'_upper: "y \<le> t'" if "y \<in> existence_ivl t0 x0" for y
    have s: "Sup (existence_ivl t0 x0) \<in> T'"
      using initial_time_bounds[OF iv_defined]
      apply -
      apply (rule mem_is_intervalI[of _ t0 t'])
      by (auto simp: ivl t' bdd intro!: t'_upper cSup_least[OF existence_ivl_notempty[OF iv_defined]])
    have *: "t \<in> T'" if "t0 \<le> t" "t \<in> existence_ivl t0 x0" for t
      by (rule mem_is_intervalI[OF \<open>is_interval T'\<close> \<open>t0 \<in> T'\<close> s]) (auto intro!: cSup_upper that bdd)
    from sup_existence_maximal[OF iv_defined mem_compact K bdd, OF *]
    show False using s ivl by auto
  qed
qed

lemma
  mem_compact_implies_subset_existence_interval:
  assumes iv_defined: "t0 \<in> T" "x0 \<in> X"
  assumes mem_compact: "\<And>t. t \<in> T \<Longrightarrow> t \<in> existence_ivl t0 x0 \<Longrightarrow> flow t0 x0 t \<in> K"
  assumes K: "compact K" "K \<subseteq> X"
  shows "T \<subseteq> existence_ivl t0 x0"
  by (rule subset_mem_compact_implies_subset_existence_interval; (fact | rule order_refl interval iv_defined))

lemma
  global_right_existence_ivl_explicit:
  assumes "b \<ge> t0"
  assumes b: "b \<in> existence_ivl t0 x0"
  obtains d K where "d > 0" "K > 0"
    "ball x0 d \<subseteq> X"
    "\<And>y. y \<in> ball x0 d \<Longrightarrow> b \<in> existence_ivl t0 y"
    "\<And>t y. y \<in> ball x0 d \<Longrightarrow> t \<in> {t0 .. b} \<Longrightarrow>
      dist (flow t0 x0 t) (flow t0 y t) \<le> dist x0 y * exp (K * abs (t - t0))"
proof -
  note iv_defined = mem_existence_ivl_iv_defined[OF b]
  define seg where "seg \<equiv> (\<lambda>t. flow t0 x0 t) ` (closed_segment t0 b)"
  have [simp]: "x0 \<in> seg"
    by (auto simp: seg_def intro!: image_eqI[where x=t0] simp: closed_segment_eq_real_ivl iv_defined)
  have "seg \<noteq> {}" by (auto simp: seg_def closed_segment_eq_real_ivl)
  moreover
  have "compact seg"
    using iv_defined b
    by (auto simp: seg_def closed_segment_eq_real_ivl
        intro!: compact_continuous_image continuous_at_imp_continuous_on flow_continuous;
      metis (erased, hide_lams) atLeastAtMost_iff closed_segment_eq_real_ivl
        closed_segment_subset_existence_ivl contra_subsetD order.trans)
  moreover note open_domain(2)
  moreover have "seg \<subseteq> X"
    using closed_segment_subset_existence_ivl b
    by (auto simp: seg_def intro!: flow_in_domain iv_defined)
  ultimately
  obtain e where e: "0 < e" "{x. infdist x seg \<le> e} \<subseteq> X"
    thm compact_in_open_separated
    by (rule compact_in_open_separated)
  define A where "A \<equiv> {x. infdist x seg \<le> e}"

  have "A \<subseteq> X" using e by (simp add: A_def)

  have mem_existence_ivlI: "\<And>s. t0 \<le> s \<Longrightarrow> s \<le> b \<Longrightarrow> s \<in> existence_ivl t0 x0"
    by (rule in_existence_between_zeroI[OF b]) (auto simp: closed_segment_eq_real_ivl)

  have "compact A"
    unfolding A_def
    by (rule compact_infdist_le) fact+
  have "compact {t0 .. b}" "{t0 .. b} \<subseteq> T"
    subgoal by simp
    subgoal
      using mem_existence_ivlI mem_existence_ivl_subset[of _ x0] iv_defined b ivl_subset_existence_ivl
      by blast
    done
  from lipschitz_on_compact[OF this \<open>compact A\<close> \<open>A \<subseteq> X\<close>]
  obtain K' where K': "\<And>t. t \<in> {t0 .. b} \<Longrightarrow> K'-lipschitz_on A (f t)"
    by metis
  define K where "K \<equiv> K' + 1"
  have "0 < K" "0 \<le> K"
    using assms lipschitz_on_nonneg[OF K', of t0]
    by (auto simp: K_def)
  have K: "\<And>t. t \<in> {t0 .. b} \<Longrightarrow> K-lipschitz_on A (f t)"
    unfolding K_def
    using \<open>_ \<Longrightarrow> lipschitz_on K' A _\<close>
    by (rule lipschitz_on_mono) auto

  have [simp]: "x0 \<in> A" using \<open>0 < e\<close> by (auto simp: A_def)


  define d where "d \<equiv> min e (e * exp (-K * (b - t0)))"
  hence d: "0 < d" "d \<le> e" "d \<le> e * exp (-K * (b - t0))"
    using e by auto

  have d_times_exp_le: "d * exp (K * (t - t0)) \<le> e" if "t0 \<le> t" "t \<le> b" for t
  proof -
    from that have "d * exp (K * (t - t0)) \<le> d * exp (K * (b - t0))"
      using \<open>0 \<le> K\<close> \<open>0 < d\<close>
      by (auto intro!: mult_left_mono)
    also have "d * exp (K * (b - t0)) \<le> e"
      using d by (auto simp: exp_minus divide_simps)
    finally show ?thesis .
  qed
  have "ball x0 d \<subseteq> X" using d \<open>A \<subseteq> X\<close>
    by (auto simp: A_def dist_commute intro!: infdist_le2[where a=x0])
  note iv_defined
  {
    fix y
    assume y: "y \<in> ball x0 d"
    hence "y \<in> A" using d
      by (auto simp: A_def dist_commute intro!: infdist_le2[where a=x0])
    hence "y \<in> X" using \<open>A \<subseteq> X\<close> by auto
    note y_iv = \<open>t0 \<in> T\<close> \<open>y \<in> X\<close>
    have in_A: "flow t0 y t \<in> A" if t: "t0 \<le> t" "t \<in> existence_ivl t0 y" "t \<le> b" for t
    proof (rule ccontr)
      assume flow_out: "flow t0 y t \<notin> A"
      obtain t' where t':
        "t0 \<le> t'"
        "t' \<le> t"
        "\<And>t. t \<in> {t0 .. t'} \<Longrightarrow> flow t0 x0 t \<in> A"
        "infdist (flow t0 y t') seg \<ge> e"
        "\<And>t. t \<in> {t0 .. t'} \<Longrightarrow> flow t0 y t \<in> A"
      proof -
        let ?out = "((\<lambda>t. infdist (flow t0 y t) seg) -` {e..}) \<inter> {t0..t}"
        have "compact ?out"
          unfolding compact_eq_bounded_closed
        proof safe
          show "bounded ?out" by (auto intro!: bounded_closed_interval)
          have "continuous_on {t0 .. t} ((\<lambda>t. infdist (flow t0 y t) seg))"
            using closed_segment_subset_existence_ivl t iv_defined
            by (force intro!: continuous_at_imp_continuous_on
              continuous_intros flow_continuous
              simp: closed_segment_eq_real_ivl)
          thus "closed ?out"
            by (simp add: continuous_on_closed_vimage)
        qed
        moreover
        have "t \<in> (\<lambda>t. infdist (flow t0 y t) seg) -` {e..} \<inter> {t0..t}"
          using flow_out \<open>t0 \<le> t\<close>
          by (auto simp: A_def)
        hence "?out \<noteq> {}"
          by blast
        ultimately have "\<exists>s\<in>?out. \<forall>t\<in>?out. s \<le> t"
          by (rule compact_attains_inf)
        then obtain t' where t':
          "\<And>s. e \<le> infdist (flow t0 y s) seg \<Longrightarrow> t0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> t' \<le> s"
          "e \<le> infdist (flow t0 y t') seg"
          "t0 \<le> t'" "t' \<le> t"
          by (auto simp: vimage_def Ball_def) metis
        have flow_in: "flow t0 x0 s \<in> A" if s: "s \<in> {t0 .. t'}" for s
        proof -
          from s have "s \<in> closed_segment t0 b"
            using \<open>t \<le> b\<close> t' by (auto simp: closed_segment_eq_real_ivl)
          then show ?thesis
            using s \<open>e > 0\<close> by (auto simp: seg_def A_def)
        qed
        have "flow t0 y t' \<in> A" if "t' = t0"
          using y d iv_defined that
          by (auto simp:  A_def \<open>y \<in> X\<close> infdist_le2[where a=x0] dist_commute)
        moreover
        have "flow t0 y s \<in> A" if s: "s \<in> {t0 ..< t'}" for s
        proof -
          from s have "s \<in> closed_segment t0 b"
            using \<open>t \<le> b\<close> t' by (auto simp: closed_segment_eq_real_ivl)
          from t'(1)[of s]
          have "t' > s \<Longrightarrow> t0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> e > infdist (flow t0 y s) seg"
            by force
          then show ?thesis
            using s t' \<open>e > 0\<close> by (auto simp: seg_def A_def)
        qed
        moreover
        note left_of_in = this
        have "closed A" using \<open>compact A\<close> by (auto simp: compact_eq_bounded_closed)
        have "((\<lambda>s. flow t0 y s) \<longlongrightarrow> flow t0 y t') (at_left t')"
          using closed_segment_subset_existence_ivl[OF t(2)] t' \<open>y \<in> X\<close> iv_defined
          by (intro flow_tendsto) (auto intro!: tendsto_intros simp: closed_segment_eq_real_ivl)
        with \<open>closed A\<close> _ _ have "t' \<noteq> t0 \<Longrightarrow> flow t0 y t' \<in> A"
        proof (rule Lim_in_closed_set)
          assume "t' \<noteq> t0"
          hence "t' > t0" using t' by auto
          hence "eventually (\<lambda>x. x \<ge> t0) (at_left t')"
            by (metis eventually_at_left less_imp_le)
          thus "eventually (\<lambda>x. flow t0 y x \<in> A) (at_left t')"
            unfolding eventually_at_filter
            by eventually_elim (auto intro!: left_of_in)
        qed simp
        ultimately have flow_y_in: "s \<in> {t0 .. t'} \<Longrightarrow> flow t0 y s \<in> A" for s
          by (cases "s = t'"; fastforce)
        have
          "t0 \<le> t'"
          "t' \<le> t"
          "\<And>t. t \<in> {t0 .. t'} \<Longrightarrow> flow t0 x0 t \<in> A"
          "infdist (flow t0 y t') seg \<ge> e"
          "\<And>t. t \<in> {t0 .. t'} \<Longrightarrow> flow t0 y t \<in> A"
          by (auto intro!: flow_in flow_y_in) fact+
        thus ?thesis ..
      qed
      {
        fix s assume s: "s \<in> {t0 .. t'}"
        hence "t0 \<le> s" by simp
        have "s \<le> b"
          using t t' s b
          by auto
        hence sx0: "s \<in> existence_ivl t0 x0"
          by (simp add: \<open>t0 \<le> s\<close> mem_existence_ivlI)
        have sy: "s \<in> existence_ivl t0 y"
          by (meson atLeastAtMost_iff contra_subsetD s t'(1) t'(2) that(2) ivl_subset_existence_ivl)
        have int: "flow t0 y s - flow t0 x0 s =
            y - x0 + (integral {t0 .. s} (\<lambda>t. f t (flow t0 y t)) -
              integral {t0 .. s} (\<lambda>t. f t (flow t0 x0 t)))"
          using iv_defined s
          unfolding flow_fixed_point[OF sx0] flow_fixed_point[OF sy]
          by (simp add: algebra_simps ivl_integral_def)
        have "norm (flow t0 y s - flow t0 x0 s) \<le> norm (y - x0) +
          norm (integral {t0 .. s} (\<lambda>t. f t (flow t0 y t)) -
            integral {t0 .. s} (\<lambda>t. f t (flow t0 x0 t)))"
          unfolding int
          by (rule norm_triangle_ineq)
        also
        have "norm (integral {t0 .. s} (\<lambda>t. f t (flow t0 y t)) -
            integral {t0 .. s} (\<lambda>t. f t (flow t0 x0 t))) =
          norm (integral {t0 .. s} (\<lambda>t. f t (flow t0 y t) - f t (flow t0 x0 t)))"
          using closed_segment_subset_existence_ivl[of s x0] sx0 closed_segment_subset_existence_ivl[of s y] sy
          by (subst Henstock_Kurzweil_Integration.integral_diff)
            (auto intro!: integrable_continuous_real continuous_at_imp_continuous_on
              f_flow_continuous
              simp: closed_segment_eq_real_ivl)
        also have "\<dots> \<le> (integral {t0 .. s} (\<lambda>t. norm (f t (flow t0 y t) - f t (flow t0 x0 t))))"
          using closed_segment_subset_existence_ivl[of s x0] sx0 closed_segment_subset_existence_ivl[of s y] sy
          by (intro integral_norm_bound_integral)
            (auto intro!: integrable_continuous_real continuous_at_imp_continuous_on
            f_flow_continuous continuous_intros
              simp: closed_segment_eq_real_ivl)
      also have "\<dots> \<le> (integral {t0 .. s} (\<lambda>t. K * norm ((flow t0 y t) - (flow t0 x0 t))))"
          using closed_segment_subset_existence_ivl[of s x0] sx0 closed_segment_subset_existence_ivl[of s y] sy
            iv_defined s t'(3,5) \<open>s \<le> b\<close>
          by (auto simp del: Henstock_Kurzweil_Integration.integral_mult_right intro!: integral_le integrable_continuous_real
            continuous_at_imp_continuous_on lipschitz_on_normD[OF K]
            flow_continuous f_flow_continuous continuous_intros
            simp: closed_segment_eq_real_ivl)
        also have "\<dots> = K * integral {t0 .. s} (\<lambda>t. norm (flow t0 y t - flow t0 x0 t))"
          using closed_segment_subset_existence_ivl[of s x0] sx0 closed_segment_subset_existence_ivl[of s y] sy
          by (subst integral_mult)
             (auto intro!: integrable_continuous_real continuous_at_imp_continuous_on
               lipschitz_on_normD[OF K] flow_continuous f_flow_continuous continuous_intros
               simp: closed_segment_eq_real_ivl)
        finally
        have norm: "norm (flow t0 y s - flow t0 x0 s) \<le>
          norm (y - x0) + K * integral {t0 .. s} (\<lambda>t. norm (flow t0 y t - flow t0 x0 t))"
          by arith
        note norm \<open>s \<le> b\<close> sx0 sy
      } note norm_le = this
      from norm_le(2) t' have "t' \<in> closed_segment t0 b"
        by (auto simp: closed_segment_eq_real_ivl)
      hence "infdist (flow t0 y t') seg \<le> dist (flow t0 y t') (flow t0 x0 t')"
        by (auto simp: seg_def infdist_le)
      also have "\<dots> \<le> norm (flow t0 y t' - flow t0 x0 t')"
        by (simp add: dist_norm)
      also have "\<dots> \<le> norm (y - x0) * exp (K * \<bar>t' - t0\<bar>)"
        unfolding K_def
        apply (rule exponential_initial_condition[OF _ _ _ _ _ K'])
        subgoal by (metis atLeastAtMost_iff local.norm_le(4) order_refl t'(1))
        subgoal by (metis atLeastAtMost_iff local.norm_le(3) order_refl t'(1))
        subgoal using e by (simp add: A_def)
        subgoal by (metis closed_segment_eq_real_ivl t'(1,5))
        subgoal by (metis closed_segment_eq_real_ivl t'(1,3))
        subgoal by (simp add: closed_segment_eq_real_ivl local.norm_le(2) t'(1))
        done
      also have "\<dots> < d * exp (K * (t - t0))"
        using y d t' t
        by (intro mult_less_le_imp_less)
           (auto simp: dist_norm[symmetric] dist_commute intro!: mult_mono \<open>0 \<le> K\<close>)
      also have "\<dots> \<le> e"
        by (rule d_times_exp_le; fact)
      finally
      have "infdist (flow t0 y t') seg < e" .
      with \<open>infdist (flow t0 y t') seg \<ge> e\<close> show False
        by (auto simp: frontier_def)
    qed

    have "{t0..b} \<subseteq> existence_ivl t0 y"
    by (rule subset_mem_compact_implies_subset_existence_interval[OF
      _ is_interval_cc \<open>{t0..b} \<subseteq> T\<close> \<open>y \<in> X\<close> in_A \<open>compact A\<close> \<open>A \<subseteq> X\<close>])
      (auto simp: \<open>t0 \<le> b\<close>)
    with \<open>t0 \<le> b\<close> have b_in: "b \<in> existence_ivl t0 y"
      by force
    {
      fix t assume t: "t \<in> {t0 .. b}"
      also have "{t0 .. b} = {t0 -- b}"
        by (auto simp: closed_segment_eq_real_ivl assms)
      also note closed_segment_subset_existence_ivl[OF b_in]
      finally have t_in: "t \<in> existence_ivl t0 y" .

      note t
      also note \<open>{t0 .. b} = {t0 -- b}\<close>
      also note closed_segment_subset_existence_ivl[OF assms(2)]
      finally have t_in': "t \<in> existence_ivl t0 x0" .
      have "norm (flow t0 y t - flow t0 x0 t) \<le> norm (y - x0) * exp (K * \<bar>t - t0\<bar>)"
        unfolding K_def
        using t closed_segment_subset_existence_ivl[OF b_in] \<open>0 < e\<close>
        by (intro in_A exponential_initial_condition[OF t_in t_in' \<open>A \<subseteq> X\<close> _ _ K'])
          (auto simp: closed_segment_eq_real_ivl A_def seg_def)
      hence "dist (flow t0 x0 t) (flow t0 y t) \<le> dist x0 y * exp (K * \<bar>t - t0\<bar>)"
        by (auto simp: dist_norm[symmetric] dist_commute)
    }
    note b_in this
  } from \<open>d > 0\<close> \<open>K > 0\<close> \<open>ball x0 d \<subseteq> X\<close> this show ?thesis ..
qed

lemma
  global_left_existence_ivl_explicit:
  assumes "b \<le> t0"
  assumes b: "b \<in> existence_ivl t0 x0"
  assumes iv_defined: "t0 \<in> T" "x0 \<in> X"
  obtains d K where "d > 0" "K > 0"
    "ball x0 d \<subseteq> X"
    "\<And>y. y \<in> ball x0 d \<Longrightarrow> b \<in> existence_ivl t0 y"
    "\<And>t y. y \<in> ball x0 d \<Longrightarrow> t \<in> {b .. t0} \<Longrightarrow> dist (flow t0 x0 t) (flow t0 y t) \<le> dist x0 y * exp (K * abs (t - t0))"
proof -
  interpret rev: ll_on_open "(preflect t0 ` T)" "(\<lambda>t. - f (preflect t0 t))" X ..
  have t0': "t0 \<in> preflect t0 ` T" "x0 \<in> X"
    by (auto intro!: iv_defined)
  from assms have "preflect t0 b \<ge> t0" "preflect t0 b \<in> rev.existence_ivl t0 x0"
    by (auto simp: rev_existence_ivl_eq)
  from rev.global_right_existence_ivl_explicit[OF this]
  obtain d K where dK: "d > 0" "K > 0"
    "ball x0 d \<subseteq> X"
    "\<And>y. y \<in> ball x0 d \<Longrightarrow> preflect t0 b \<in> rev.existence_ivl t0 y"
    "\<And>t y. y \<in> ball x0 d \<Longrightarrow> t \<in> {t0 .. preflect t0 b} \<Longrightarrow> dist (rev.flow t0 x0 t) (rev.flow t0 y t) \<le> dist x0 y * exp (K * abs (t - t0))"
    by (auto simp: rev_flow_eq \<open>x0 \<in> X\<close>)

  have ex_ivlI: "dist x0 y < d \<Longrightarrow> t \<in> existence_ivl t0 y" if "b \<le> t" "t \<le> t0" for t y
    using that dK(4)[of y] dK(3) iv_defined
    by (auto simp: subset_iff rev_existence_ivl_eq[of ]
      closed_segment_eq_real_ivl iv_defined in_existence_between_zeroI)
  have "b \<in> existence_ivl t0 y" if "dist x0 y < d" for y
    using that dK
    by (subst existence_ivl_eq_rev) (auto simp: iv_defined intro!: image_eqI[where x="preflect t0 b"])
  with dK have "d > 0" "K > 0"
    "ball x0 d \<subseteq> X"
    "\<And>y. y \<in> ball x0 d \<Longrightarrow> b \<in> existence_ivl t0 y"
    "\<And>t y. y \<in> ball x0 d \<Longrightarrow> t \<in> {b .. t0} \<Longrightarrow> dist (flow t0 x0 t) (flow t0 y t) \<le> dist x0 y * exp (K * abs (t - t0))"
    by (auto simp: flow_eq_rev iv_defined ex_ivlI \<open>x0 \<in> X\<close> subset_iff
      intro!: order_trans[OF dK(5)] image_eqI[where x="preflect t0 b"])
  then show ?thesis ..
qed

lemma
  global_existence_ivl_explicit:
  assumes a: "a \<in> existence_ivl t0 x0"
  assumes b: "b \<in> existence_ivl t0 x0"
  assumes le: "a \<le> b"
  obtains d K where "d > 0" "K > 0"
    "ball x0 d \<subseteq> X"
    "\<And>y. y \<in> ball x0 d \<Longrightarrow> a \<in> existence_ivl t0 y"
    "\<And>y. y \<in> ball x0 d \<Longrightarrow> b \<in> existence_ivl t0 y"
    "\<And>t y. y \<in> ball x0 d \<Longrightarrow> t \<in> {a .. b} \<Longrightarrow>
      dist (flow t0 x0 t) (flow t0 y t) \<le> dist x0 y * exp (K * abs (t - t0))"
proof -
  note iv_defined = mem_existence_ivl_iv_defined[OF a]
  define r where "r \<equiv> Max {t0, a, b}"
  define l where "l \<equiv> Min {t0, a, b}"
  have r: "r \<ge> t0" "r \<in> existence_ivl t0 x0"
    using a b by (auto simp: max_def r_def iv_defined)
  obtain dr Kr where right:
    "0 < dr" "0 < Kr" "ball x0 dr \<subseteq> X"
    "\<And>y. y \<in> ball x0 dr \<Longrightarrow> r \<in> existence_ivl t0 y"
    "\<And>y t. y \<in> ball x0 dr \<Longrightarrow> t \<in> {t0..r} \<Longrightarrow> dist (flow t0 x0 t) (flow t0 y t) \<le> dist x0 y * exp (Kr * \<bar>t - t0\<bar>)"
    by (rule global_right_existence_ivl_explicit[OF r]) blast

  have l: "l \<le> t0" "l \<in> existence_ivl t0 x0"
    using a b by (auto simp: min_def l_def iv_defined)
  obtain dl Kl where left:
    "0 < dl" "0 < Kl" "ball x0 dl \<subseteq> X"
    "\<And>y. y \<in> ball x0 dl \<Longrightarrow> l \<in> existence_ivl t0 y"
    "\<And>y t. y \<in> ball x0 dl \<Longrightarrow> t \<in> {l .. t0} \<Longrightarrow> dist (flow t0 x0 t) (flow t0 y t) \<le> dist x0 y * exp (Kl * \<bar>t - t0\<bar>)"
    by (rule global_left_existence_ivl_explicit[OF l iv_defined]) blast

  define d where "d \<equiv> min dr dl"
  define K where "K \<equiv> max Kr Kl"

  note iv_defined
  have "0 < d" "0 < K" "ball x0 d \<subseteq> X"
    using left right by (auto simp: d_def K_def)
  moreover
  {
    fix y assume y: "y \<in> ball x0 d"
    hence "y \<in> X" using \<open>ball x0 d \<subseteq> X\<close> by auto
    from y
      closed_segment_subset_existence_ivl[OF left(4), of y]
      closed_segment_subset_existence_ivl[OF right(4), of y]
    have "a \<in> existence_ivl t0 y" "b \<in> existence_ivl t0 y"
      by (auto simp: d_def l_def r_def min_def max_def closed_segment_eq_real_ivl split: if_split_asm)
  }
  moreover
  {
    fix t y
    assume y: "y \<in> ball x0 d"
      and t: "t \<in> {a .. b}"
    from y have "y \<in> X" using \<open>ball x0 d \<subseteq> X\<close> by auto
    have "dist (flow t0 x0 t) (flow t0 y t) \<le> dist x0 y * exp (K * abs (t - t0))"
    proof cases
      assume "t \<ge> t0"
      hence "dist (flow t0 x0 t) (flow t0 y t) \<le> dist x0 y * exp (Kr * abs (t - t0))"
        using y t
        by (intro right) (auto simp: d_def r_def)
      also have "exp (Kr * abs (t - t0)) \<le> exp (K * abs (t - t0))"
        by (auto simp: mult_left_mono K_def max_def mult_right_mono)
      finally show ?thesis by (simp add: mult_left_mono)
    next
      assume "\<not>t \<ge> t0"
      hence "dist (flow t0 x0 t) (flow t0 y t) \<le> dist x0 y * exp (Kl * abs (t - t0))"
        using y t
        by (intro left) (auto simp: d_def l_def)
      also have "exp (Kl * abs (t - t0)) \<le> exp (K * abs (t - t0))"
        by (auto simp: mult_left_mono K_def max_def mult_right_mono)
      finally show ?thesis by (simp add: mult_left_mono)
    qed
  } ultimately show ?thesis ..
qed

lemma eventually_exponential_separation:
  assumes a: "a \<in> existence_ivl t0 x0"
  assumes b: "b \<in> existence_ivl t0 x0"
  assumes le: "a \<le> b"
  obtains K where "K > 0" "\<forall>\<^sub>F y in at x0. \<forall>t\<in>{a..b}. dist (flow t0 x0 t) (flow t0 y t) \<le> dist x0 y * exp (K * \<bar>t - t0\<bar>)"
proof -
  from global_existence_ivl_explicit[OF assms]
  obtain d K where *: "d > 0" "K > 0"
    "ball x0 d \<subseteq> X"
    "\<And>y. y \<in> ball x0 d \<Longrightarrow> a \<in> existence_ivl t0 y"
    "\<And>y. y \<in> ball x0 d \<Longrightarrow> b \<in> existence_ivl t0 y"
    "\<And>t y. y \<in> ball x0 d \<Longrightarrow> t \<in> {a .. b} \<Longrightarrow>
      dist (flow t0 x0 t) (flow t0 y t) \<le> dist x0 y * exp (K * abs (t - t0))"
    by auto
  note \<open>K > 0\<close>
  moreover
  have "eventually (\<lambda>y. y \<in> ball x0 d) (at x0)"
    using \<open>d > 0\<close>[THEN eventually_at_ball]
    by eventually_elim simp
  hence "eventually (\<lambda>y. \<forall>t\<in>{a..b}. dist (flow t0 x0 t) (flow t0 y t) \<le> dist x0 y * exp (K * \<bar>t - t0\<bar>)) (at x0)"
    by eventually_elim (safe intro!: *)
  ultimately show ?thesis ..
qed

lemma eventually_mem_existence_ivl:
  assumes b: "b \<in> existence_ivl t0 x0"
  shows "\<forall>\<^sub>F x in at x0. b \<in> existence_ivl t0 x"
proof -
  from mem_existence_ivl_iv_defined[OF b] have iv_defined: "t0 \<in> T" "x0 \<in> X" by simp_all
  note eiit = existence_ivl_initial_time[OF iv_defined]
  {
    fix a b
    assume assms: "a \<in> existence_ivl t0 x0" "b \<in> existence_ivl t0 x0" "a \<le> b"
    from global_existence_ivl_explicit[OF assms]
    obtain d K where *: "d > 0" "K > 0"
      "ball x0 d \<subseteq> X"
      "\<And>y. y \<in> ball x0 d \<Longrightarrow> a \<in> existence_ivl t0 y"
      "\<And>y. y \<in> ball x0 d \<Longrightarrow> b \<in> existence_ivl t0 y"
      "\<And>t y. y \<in> ball x0 d \<Longrightarrow> t \<in> {a .. b} \<Longrightarrow>
        dist (flow t0 x0 t) (flow t0 y t) \<le> dist x0 y * exp (K * abs (t - t0))"
      by auto
    have "eventually (\<lambda>y. y \<in> ball x0 d) (at x0)"
      using \<open>d > 0\<close>[THEN eventually_at_ball]
      by eventually_elim simp
    then have "\<forall>\<^sub>F x in at x0. a \<in> existence_ivl t0 x \<and> b \<in> existence_ivl t0 x"
      by (eventually_elim) (auto intro!: *)
  } from this[OF b eiit] this[OF eiit b]
  show ?thesis
    by (cases "t0 \<le> b") (auto simp: eventually_mono)
qed

lemma uniform_limit_flow:
  assumes a: "a \<in> existence_ivl t0 x0"
  assumes b: "b \<in> existence_ivl t0 x0"
  assumes le: "a \<le> b"
  shows "uniform_limit {a .. b} (flow t0) (flow t0 x0) (at x0)"
proof (rule uniform_limitI)
  fix e::real assume "0 < e"
  from eventually_exponential_separation[OF assms] obtain K where "0 < K"
    "\<forall>\<^sub>F y in at x0. \<forall>t\<in>{a..b}. dist (flow t0 x0 t) (flow t0 y t) \<le> dist x0 y * exp (K * \<bar>t - t0\<bar>)"
    by auto
  note this(2)
  moreover
  let ?m = "max (abs (b - t0)) (abs (a - t0))"
  have "eventually (\<lambda>y. \<forall>t\<in>{a..b}. dist x0 y * exp (K * \<bar>t - t0\<bar>) \<le> dist x0 y * exp (K * ?m)) (at x0)"
    using \<open>a \<le> b\<close> \<open>0 < K\<close>
    by (auto intro!: mult_left_mono always_eventually)
  moreover
  have "eventually (\<lambda>y. dist x0 y * exp (K * ?m) < e) (at x0)"
    using \<open>0 < e\<close> by (auto intro!: order_tendstoD tendsto_eq_intros)
  ultimately
  show "eventually (\<lambda>y. \<forall>t\<in>{a..b}. dist (flow t0 y t) (flow t0 x0 t) < e) (at x0)"
    by eventually_elim (force simp: dist_commute)
qed

lemma eventually_at_fst:
  assumes "eventually P (at (fst x))"
  assumes "P (fst x)"
  shows "eventually (\<lambda>h. P (fst h)) (at x)"
  using assms
  unfolding eventually_at_topological
  by (metis open_vimage_fst rangeI range_fst vimageE vimageI)

lemma eventually_at_snd:
  assumes "eventually P (at (snd x))"
  assumes "P (snd x)"
  shows "eventually (\<lambda>h. P (snd h)) (at x)"
  using assms
  unfolding eventually_at_topological
  by (metis open_vimage_snd rangeI range_snd vimageE vimageI)

lemma
  shows open_state_space: "open (Sigma X (existence_ivl t0))"
  and flow_continuous_on_state_space:
    "continuous_on (Sigma X (existence_ivl t0)) (\<lambda>(x, t). flow t0 x t)"
proof (safe intro!: topological_space_class.openI continuous_at_imp_continuous_on)
  fix t x assume "x \<in> X" and t: "t \<in> existence_ivl t0 x"
  have iv_defined: "t0 \<in> T" "x \<in> X"
    using mem_existence_ivl_iv_defined[OF t] by auto
  from \<open>x \<in> X\<close> t open_existence_ivl
  obtain e where e: "e > 0" "cball t e \<subseteq> existence_ivl t0 x"
    by (metis open_contains_cball)
  hence ivl: "t - e \<in> existence_ivl t0 x" "t + e \<in> existence_ivl t0 x" "t - e \<le> t + e"
    by (auto simp: cball_def dist_real_def)
  obtain d K where dK:
    "0 < d" "0 < K" "ball x d \<subseteq> X"
    "\<And>y. y \<in> ball x d \<Longrightarrow> t - e \<in> existence_ivl t0 y"
    "\<And>y. y \<in> ball x d \<Longrightarrow> t + e \<in> existence_ivl t0 y"
    "\<And>y s. y \<in> ball x d \<Longrightarrow> s \<in> {t - e..t + e} \<Longrightarrow>
      dist (flow t0 x s) (flow t0 y s) \<le> dist x y * exp (K * \<bar>s - t0\<bar>)"
    by (rule global_existence_ivl_explicit[OF ivl]) blast
  let ?T = "ball x d \<times> ball t e"
  have "open ?T" by (auto intro!: open_Times)
  moreover have "(x, t) \<in> ?T" by (auto simp: dK \<open>0 < e\<close>)
  moreover have "?T \<subseteq> Sigma X (existence_ivl t0)"
  proof safe
    fix s y assume y: "y \<in> ball x d" and s: "s \<in> ball t e"
    with \<open>ball x d \<subseteq> X\<close> show "y \<in> X" by auto
    have "ball t e \<subseteq> closed_segment t0 (t - e) \<union> closed_segment t0 (t + e)"
      by (auto simp: closed_segment_eq_real_ivl dist_real_def)
    with \<open>y \<in> X\<close> s closed_segment_subset_existence_ivl[OF dK(4)[OF y]]
      closed_segment_subset_existence_ivl[OF dK(5)[OF y]]
    show "s \<in> existence_ivl t0 y"
      by auto
  qed
  ultimately show "\<exists>T. open T \<and> (x, t) \<in> T \<and> T \<subseteq> Sigma X (existence_ivl t0)"
    by blast
  have **: "\<forall>\<^sub>F s in at 0. norm (flow t0 (x + fst s) (t + snd s) - flow t0 x t) < 2 * eps"
    if "eps > 0" for eps :: real
  proof -
    have "\<forall>\<^sub>F s in at 0. norm (flow t0 (x + fst s) (t + snd s) - flow t0 x t) =
      norm (flow t0 (x + fst s) (t + snd s) - flow t0 x (t + snd s) +
        (flow t0 x (t + snd s) - flow t0 x t))"
      by auto
    moreover
    have "\<forall>\<^sub>F s in at 0.
        norm (flow t0 (x + fst s) (t + snd s) - flow t0 x (t + snd s) +
          (flow t0 x (t + snd s) - flow t0 x t)) \<le>
        norm (flow t0 (x + fst s) (t + snd s) - flow t0 x (t + snd s)) +
          norm (flow t0 x (t + snd s) - flow t0 x t)"
      by eventually_elim (rule norm_triangle_ineq)
    moreover
    have "\<forall>\<^sub>F s in at 0. t + snd s \<in> ball t e"
      by (auto simp: dist_real_def intro!: order_tendstoD[OF _ \<open>0 < e\<close>]
        intro!: tendsto_eq_intros)
    moreover from uniform_limit_flow[OF ivl, THEN uniform_limitD, OF \<open>eps > 0\<close>]
    have "\<forall>\<^sub>F (h::(_ )) in at (fst (0::'a*real)).
      \<forall>t\<in>{t - e..t + e}. dist (flow t0 x t) (flow t0 (x + h) t) < eps"
      by (subst (asm) at_to_0)
        (auto simp: eventually_filtermap dist_commute ac_simps)
    hence "\<forall>\<^sub>F (h::(_ * real)) in at 0.
      \<forall>t\<in>{t - e..t + e}. dist (flow t0 x t) (flow t0 (x + fst h) t) < eps"
      by (rule eventually_at_fst) (simp add: \<open>eps > 0\<close>)
    moreover
    have "\<forall>\<^sub>F h in at (snd (0::'a * _)). norm (flow t0 x (t + h) - flow t0 x t) < eps"
      using flow_continuous[OF t, unfolded isCont_def, THEN tendstoD, OF \<open>eps > 0\<close>]
      by (subst (asm) at_to_0)
        (auto simp: eventually_filtermap dist_norm ac_simps)
    hence "\<forall>\<^sub>F h::('a * _) in at 0. norm (flow t0 x (t + snd h) - flow t0 x t) < eps"
      by (rule eventually_at_snd) (simp add: \<open>eps > 0\<close>)
    ultimately
    show ?thesis
    proof eventually_elim
      case (elim s)
      note elim(1)
      also note elim(2)
      also note elim(5)
      also
      from elim(3) have "t + snd s \<in> {t - e..t + e}"
        by (auto simp: dist_real_def algebra_simps)
      from elim(4)[rule_format, OF this]
      have "norm (flow t0 (x + fst s) (t + snd s) - flow t0 x (t + snd s)) < eps"
        by (auto simp: dist_commute dist_norm[symmetric])
      finally
      show ?case by simp
    qed
  qed
  have *: "\<forall>\<^sub>F s in at 0. norm (flow t0 (x + fst s) (t + snd s) - flow t0 x t) < eps"
    if "eps > 0" for eps::real
  proof -
    from that have "eps / 2 > 0" by simp
    from **[OF this] show ?thesis by auto
  qed
  show "isCont (\<lambda>(x, y). flow t0 x y) (x, t)"
    unfolding isCont_iff
    by (rule LIM_zero_cancel)
      (auto simp: split_beta' norm_conv_dist[symmetric] intro!: tendstoI *)
qed

lemmas flow_continuous_on_compose[continuous_intros] =
  continuous_on_compose_Pair[OF flow_continuous_on_state_space]

lemma flow_isCont_state_space: "t \<in> existence_ivl t0 x0 \<Longrightarrow> isCont (\<lambda>(x, t). flow t0 x t) (x0, t)"
  using flow_continuous_on_state_space[of] mem_existence_ivl_iv_defined[of t x0]
  using continuous_on_eq_continuous_at open_state_space by fastforce

lemma
  flow_absolutely_integrable_on[integrable_on_simps]:
  assumes "s \<in> existence_ivl t0 x0"
  shows "(\<lambda>x. norm (flow t0 x0 x)) integrable_on closed_segment t0 s"
  using assms
  by (auto simp: closed_segment_eq_real_ivl intro!: integrable_continuous_real continuous_intros
    flow_continuous_on_intro
    intro: in_existence_between_zeroI)

lemma existence_ivl_eq_domain:
  assumes iv_defined: "t0 \<in> T" "x0 \<in> X"
  assumes bnd: "\<And>tm tM t x. tm \<in> T \<Longrightarrow> tM \<in> T \<Longrightarrow> \<exists>M. \<exists>L. \<forall>t \<in> {tm .. tM}. \<forall>x \<in> X. norm (f t x) \<le> M + L * norm x"
  assumes "is_interval T" "X = UNIV"
  shows "existence_ivl t0 x0 = T"
proof -
  from assms have XI: "x \<in> X" for x by auto
  {
    fix tm tM assume tm: "tm \<in> T" and tM: "tM \<in> T" and tmtM: "tm \<le> t0" "t0 \<le> tM"
    from bnd[OF tm tM] obtain M' L'
    where bnd': "\<And>x t. x \<in> X \<Longrightarrow> tm \<le> t \<Longrightarrow> t \<le> tM \<Longrightarrow> norm (f t x) \<le> M' + L' * norm x"
      by force
    define M where "M \<equiv> norm M' + 1"
    define L where "L \<equiv> norm L' + 1"
    have bnd: "\<And>x t. x \<in> X \<Longrightarrow> tm \<le> t \<Longrightarrow> t \<le> tM \<Longrightarrow> norm (f t x) \<le> M + L * norm x"
      by (auto simp: M_def L_def intro!: bnd'[THEN order_trans] add_mono mult_mono)
    have "M > 0" "L > 0" by (auto simp: L_def M_def)

    let ?r = "(norm x0 + \<bar>tm - tM\<bar> * M + 1) * exp (L * \<bar>tm - tM\<bar>)"
    define K where "K \<equiv> cball (0::'a) ?r"
    have K: "compact K" "K \<subseteq> X"
      by (auto simp: K_def \<open>X = UNIV\<close>)
    {
      fix t assume t: "t \<in> existence_ivl t0 x0"  and le: "tm \<le> t" "t \<le> tM"
      {
        fix s assume sc: "s \<in> closed_segment t0 t"
        then have s: "s \<in> existence_ivl t0 x0" and le: "tm \<le> s" "s \<le> tM" using t le sc
          using closed_segment_subset_existence_ivl
          apply -
          subgoal by force
          subgoal by (metis (full_types) atLeastAtMost_iff closed_segment_eq_real_ivl order_trans tmtM(1))
          subgoal by (metis (full_types) atLeastAtMost_iff closed_segment_eq_real_ivl order_trans tmtM(2))
          done
        from sc have nle: "norm (t0 - s) \<le> norm (t0 - t)" by (auto simp: closed_segment_eq_real_ivl split: if_split_asm)
        from flow_fixed_point[OF s]
        have "norm (flow t0 x0 s) \<le> norm x0 + integral (closed_segment t0 s) (\<lambda>t. M + L * norm (flow t0 x0 t))"
          using tmtM
          using closed_segment_subset_existence_ivl[OF s] le
          by (auto simp:
            intro!: norm_triangle_le norm_triangle_ineq4[THEN order.trans]
              ivl_integral_norm_bound_integral bnd
              integrable_continuous_closed_segment
              integrable_continuous_real
              continuous_intros
              continuous_on_subset[OF flow_continuous_on]
              flow_in_domain
              mem_existence_ivl_subset)
          (auto simp: closed_segment_eq_real_ivl split: if_splits)
        also have "\<dots> = norm x0 + norm (t0 - s) * M + L * integral (closed_segment t0 s) (\<lambda>t. norm (flow t0 x0 t))"
          by (simp add: integral_add integrable_on_simps \<open>s \<in> existence_ivl _ _\<close>
            integral_const_closed_segment abs_minus_commute)
        also have "norm (t0 - s) * M \<le> norm (t0 - t) * M "
          using nle \<open>M > 0\<close> by auto
        also have "\<dots> \<le> \<dots> + 1" by simp
        finally have "norm (flow t0 x0 s) \<le> norm x0 + norm (t0 - t) * M + 1 +
            L * integral (closed_segment t0 s) (\<lambda>t. norm (flow t0 x0 t))" by simp
      }
      then have "norm (flow t0 x0 t) \<le> (norm x0 + norm (t0 - t) * M + 1) * exp (L * \<bar>t - t0\<bar>)"
        using closed_segment_subset_existence_ivl[OF t]
        by (intro gronwall_more_general_segment[where a=t0 and b = t and t = t])
          (auto simp: \<open>0 < L\<close> \<open>0 < M\<close> less_imp_le
            intro!: add_nonneg_pos mult_nonneg_nonneg add_nonneg_nonneg continuous_intros
              flow_continuous_on_intro)
      also have "\<dots> \<le> ?r"
        using le tmtM
        by (auto simp: less_imp_le \<open>0 < M\<close> \<open>0 < L\<close> abs_minus_commute intro!: mult_mono)
      finally
      have "flow t0 x0 t \<in> K" by (simp add: dist_norm K_def)
    } note flow_compact = this

    have "{tm..tM} \<subseteq> existence_ivl t0 x0"
      using tmtM tm \<open>x0 \<in> X\<close> \<open>compact K\<close> \<open>K \<subseteq> X\<close> mem_is_intervalI[OF \<open>is_interval T\<close> \<open>tm \<in> T\<close> \<open>tM \<in> T\<close>]
      by (intro subset_mem_compact_implies_subset_existence_interval[OF _ _ _ _flow_compact])
         (auto simp: tmtM is_interval_cc)
  } note bnds = this

  show "existence_ivl t0 x0 = T"
  proof safe
    fix x assume x: "x \<in> T"
    from bnds[OF x iv_defined(1)] bnds[OF iv_defined(1) x]
    show "x \<in> existence_ivl t0 x0"
      by (cases "x \<le> t0") auto
  qed (insert existence_ivl_subset, fastforce)
qed

lemma flow_unique:
  assumes "t \<in> existence_ivl t0 x0"
  assumes "phi t0 = x0"
  assumes "\<And>t. t \<in> existence_ivl t0 x0 \<Longrightarrow> (phi has_vector_derivative f t (phi t)) (at t)"
  assumes "\<And>t. t \<in> existence_ivl t0 x0 \<Longrightarrow> phi t \<in> X"
  shows "flow t0 x0 t = phi t"
  apply (rule maximal_existence_flow[where K="existence_ivl t0 x0"])
  subgoal by (auto intro!: solves_odeI simp: has_vderiv_on_def assms at_within_open[OF _ open_existence_ivl])
  subgoal by fact
  subgoal by (simp add: )
  subgoal using mem_existence_ivl_iv_defined[OF \<open>t \<in> existence_ivl t0 x0\<close>] by simp
  subgoal by (simp add: existence_ivl_subset)
  subgoal by fact
  done

lemma flow_unique_on:
  assumes "t \<in> existence_ivl t0 x0"
  assumes "phi t0 = x0"
  assumes "(phi has_vderiv_on (\<lambda>t. f t (phi t))) (existence_ivl t0 x0)"
  assumes "\<And>t. t \<in> existence_ivl t0 x0 \<Longrightarrow> phi t \<in> X"
  shows "flow t0 x0 t = phi t"
  using flow_unique[where phi=phi, OF assms(1,2) _ assms(4)] assms(3)
  by (auto simp: has_vderiv_on_open)

end \<comment> \<open>@{thm local_lipschitz}\<close>

locale two_ll_on_open =
  F: ll_on_open T1 F X + G: ll_on_open T2 G X
  for F T1 G T2 X J x0 +
  fixes e::real and K
  assumes t0_in_J: "0 \<in> J"
  assumes J_subset: "J \<subseteq> F.existence_ivl 0 x0"
  assumes J_ivl: "is_interval J"
  assumes F_lipschitz: "\<And>t. t \<in> J \<Longrightarrow> K-lipschitz_on X (F t)"
  assumes K_pos: "0 < K"
  assumes F_G_norm_ineq: "\<And>t x. t \<in> J \<Longrightarrow> x \<in> X \<Longrightarrow> norm (F t x - G t x) < e"
begin

context begin

lemma F_iv_defined: "0 \<in> T1" "x0 \<in> X"
  subgoal using F.existence_ivl_initial_time_iff J_subset t0_in_J by blast
  subgoal using F.mem_existence_ivl_iv_defined(2) J_subset t0_in_J by blast
  done

lemma e_pos: "0 < e"
  using le_less_trans[OF norm_ge_zero F_G_norm_ineq[OF t0_in_J F_iv_defined(2)]]
  by assumption

qualified definition "flow0 t = F.flow 0 x0 t"
qualified definition "Y t = G.flow 0 x0 t"

lemma norm_X_Y_bound:
shows "\<forall>t \<in> J \<inter> G.existence_ivl 0 x0. norm (flow0 t - Y t) \<le> e / K * (exp(K * \<bar>t\<bar>) - 1)"
proof(safe)
  fix t assume "t \<in> J"
  assume tG: "t \<in> G.existence_ivl 0 x0"
  have "0 \<in> J" by (simp add: t0_in_J)

  let ?u="\<lambda>t. norm (flow0 t - Y t)"
  show "norm (flow0 t - Y t) \<le> e / K * (exp (K * \<bar>t\<bar>) - 1)"
  proof(cases "0 \<le> t")
    assume "0 \<le> t"
    hence [simp]: "\<bar>t\<bar> = t" by simp

    have t0_t_in_J: "{0..t} \<subseteq> J"
      using \<open>t \<in> J\<close> \<open>0 \<in> J\<close> J_ivl
      using mem_is_interval_1_I atLeastAtMost_iff subsetI by blast

    note F_G_flow_cont[continuous_intros] =
      continuous_on_subset[OF F.flow_continuous_on]
      continuous_on_subset[OF G.flow_continuous_on]

    have "?u t + e/K \<le> e/K * exp(K * t)"
    proof(rule gronwall[where g="\<lambda>t. ?u t + e/K", OF _ _ _ _ K_pos \<open>0 \<le> t\<close> order.refl])
      fix s assume "0 \<le> s" "s \<le> t"
      hence "{0..s} \<subseteq> J" using t0_t_in_J by auto

      hence t0_s_in_existence:
        "{0..s} \<subseteq> F.existence_ivl 0 x0"
        "{0..s} \<subseteq> G.existence_ivl 0 x0"
        using J_subset tG \<open>0 \<le> s\<close> \<open>s \<le> t\<close> G.ivl_subset_existence_ivl[OF tG]
        by auto

      hence s_in_existence:
        "s \<in> F.existence_ivl 0 x0"
        "s \<in> G.existence_ivl 0 x0"
          using \<open>0 \<le> s\<close> by auto

      note cont_statements[continuous_intros] =
        F_iv_defined (*  G.iv_defined *)
        F.flow_in_domain
        G.flow_in_domain
        F.mem_existence_ivl_subset
        G.mem_existence_ivl_subset

      have [integrable_on_simps]:
        "continuous_on {0..s} (\<lambda>s. F s (F.flow 0 x0 s))"
        "continuous_on {0..s} (\<lambda>s. G s (G.flow 0 x0 s))"
        "continuous_on {0..s} (\<lambda>s. F s (G.flow 0 x0 s))"
        "continuous_on {0..s} (\<lambda>s. G s (F.flow 0 x0 s))"
        using t0_s_in_existence
        by (auto intro!: continuous_intros integrable_continuous_real)

      have "flow0 s - Y s = integral {0..s} (\<lambda>s. F s (flow0 s) - G s (Y s))"
        using \<open>0 \<le> s\<close>
        by (simp add: flow0_def Y_def Henstock_Kurzweil_Integration.integral_diff integrable_on_simps ivl_integral_def
               F.flow_fixed_point[OF s_in_existence(1)]
               G.flow_fixed_point[OF s_in_existence(2)])
      also have "... = integral {0..s} (\<lambda>s. (F s (flow0 s) - F s (Y s)) + (F s (Y s) - G s (Y s)))"
        by simp
      also have "... = integral {0..s} (\<lambda>s. F s (flow0 s) - F s (Y s)) + integral {0..s} (\<lambda>s. F s (Y s) - G s (Y s))"
        by (simp add: Henstock_Kurzweil_Integration.integral_diff Henstock_Kurzweil_Integration.integral_add flow0_def Y_def integrable_on_simps)
      finally have "?u s \<le> norm (integral {0..s} (\<lambda>s. F s (flow0 s) - F s (Y s))) + norm (integral {0..s} (\<lambda>s. F s (Y s) - G s (Y s)))"
        by (simp add: norm_triangle_ineq)
      also have "... \<le> integral {0..s} (\<lambda>s. norm (F s (flow0 s) - F s (Y s))) + integral {0..s} (\<lambda>s. norm (F s (Y s) - G s (Y s)))"
        using t0_s_in_existence
        by (auto simp add: flow0_def Y_def
          intro!: add_mono continuous_intros continuous_on_imp_absolutely_integrable_on)
      also have "... \<le> integral {0..s} (\<lambda>s. K * ?u s) + integral {0..s} (\<lambda>s. e)"
      proof (rule add_mono[OF integral_le integral_le])
        show "norm (F x (flow0 x) - F x (Y x)) \<le> K * norm (flow0 x - Y x)" if "x \<in> {0..s}" for x
          using F_lipschitz[unfolded lipschitz_on_def, THEN conjunct2] that
            cont_statements(1,2,4)
            t0_s_in_existence F_iv_defined (* G.iv_defined *)
          by (metis F_lipschitz flow0_def Y_def \<open>{0..s} \<subseteq> J\<close> lipschitz_on_normD F.flow_in_domain
            G.flow_in_domain subsetCE)
        show "\<And>x. x \<in> {0..s} \<Longrightarrow> norm (F x (Y x) - G x (Y x)) \<le> e"
          using F_G_norm_ineq cont_statements(2,3) t0_s_in_existence
          using Y_def \<open>{0..s} \<subseteq> J\<close> cont_statements(5) subset_iff G.flow_in_domain
          by (metis eucl_less_le_not_le)
      qed (simp_all add: t0_s_in_existence continuous_intros integrable_on_simps flow0_def Y_def)
      also have "... = K * integral {0..s} (\<lambda>s. ?u s + e / K)"
        using K_pos t0_s_in_existence
        by (simp_all add: algebra_simps Henstock_Kurzweil_Integration.integral_add flow0_def Y_def continuous_intros
          continuous_on_imp_absolutely_integrable_on)
      finally show "?u s + e / K \<le> e / K + K * integral {0..s} (\<lambda>s. ?u s + e / K)"
        by simp
    next
      show "continuous_on {0..t} (\<lambda>t. norm (flow0 t - Y t) + e / K)"
        using t0_t_in_J J_subset G.ivl_subset_existence_ivl[OF tG]
        by (auto simp add: flow0_def Y_def intro!: continuous_intros)
    next
      fix s assume "0 \<le> s" "s \<le> t"
      show "0 \<le> norm (flow0 s - Y s) + e / K"
        using e_pos K_pos by simp
    next
      show "0 < e / K" using e_pos K_pos by simp
    qed
    thus ?thesis by (simp add: algebra_simps)
  next
    assume "\<not>0 \<le> t"
    hence "t \<le> 0" by simp
    hence [simp]: "\<bar>t\<bar> = -t" by simp

    have t0_t_in_J: "{t..0} \<subseteq> J"
      using \<open>t \<in> J\<close> \<open>0 \<in> J\<close> J_ivl \<open>\<not> 0 \<le> t\<close> atMostAtLeast_subset_convex is_interval_convex_1
      by auto

    note F_G_flow_cont[continuous_intros] =
      continuous_on_subset[OF F.flow_continuous_on]
      continuous_on_subset[OF G.flow_continuous_on]

    have "?u t + e/K \<le> e/K * exp(- K * t)"
    proof(rule gronwall_left[where g="\<lambda>t. ?u t + e/K", OF _ _ _ _ K_pos order.refl \<open>t \<le> 0\<close>])
      fix s assume "t \<le> s" "s \<le> 0"
      hence "{s..0} \<subseteq> J" using t0_t_in_J by auto

      hence t0_s_in_existence:
        "{s..0} \<subseteq> F.existence_ivl 0 x0"
        "{s..0} \<subseteq> G.existence_ivl 0 x0"
        using J_subset G.ivl_subset_existence_ivl'[OF tG] \<open>s \<le> 0\<close> \<open>t \<le> s\<close>
        by auto

      hence s_in_existence:
        "s \<in> F.existence_ivl 0 x0"
        "s \<in> G.existence_ivl 0 x0"
          using \<open>s \<le> 0\<close> by auto

      note cont_statements[continuous_intros] =
        F_iv_defined
        F.flow_in_domain
        G.flow_in_domain
        F.mem_existence_ivl_subset
        G.mem_existence_ivl_subset
      then have [continuous_intros]:
        "{s..0} \<subseteq> T1"
        "{s..0} \<subseteq> T2"
        "F.flow 0 x0 ` {s..0} \<subseteq> X"
        "G.flow 0 x0 ` {s..0} \<subseteq> X"
        "s \<le> x \<Longrightarrow> x \<le> 0 \<Longrightarrow> x \<in> F.existence_ivl 0 x0"
        "s \<le> x \<Longrightarrow> x \<le> 0 \<Longrightarrow> x \<in> G.existence_ivl 0 x0" for x
        using t0_s_in_existence
        by (auto simp: )
      have "flow0 s - Y s = - integral {s..0} (\<lambda>s. F s (flow0 s) - G s (Y s))"
        using t0_s_in_existence \<open>s \<le> 0\<close>
        by (simp add: flow0_def Y_def ivl_integral_def
               F.flow_fixed_point[OF s_in_existence(1)]
               G.flow_fixed_point[OF s_in_existence(2)]
               continuous_intros integrable_on_simps Henstock_Kurzweil_Integration.integral_diff)
      also have "... = - integral {s..0} (\<lambda>s. (F s (flow0 s) - F s (Y s)) + (F s (Y s) - G s (Y s)))"
        by simp
      also have "... = - (integral {s..0} (\<lambda>s. F s (flow0 s) - F s (Y s)) + integral {s..0} (\<lambda>s. F s (Y s) - G s (Y s)))"
        using t0_s_in_existence
        by (subst Henstock_Kurzweil_Integration.integral_add) (simp_all add: integral_add flow0_def Y_def continuous_intros integrable_on_simps)
      finally have "?u s \<le> norm (integral {s..0} (\<lambda>s. F s (flow0 s) - F s (Y s))) + norm (integral {s..0} (\<lambda>s. F s (Y s) - G s (Y s)))"
        by (metis (no_types, lifting) norm_minus_cancel norm_triangle_ineq)
      also have "... \<le> integral {s..0} (\<lambda>s. norm (F s (flow0 s) - F s (Y s))) + integral {s..0} (\<lambda>s. norm (F s (Y s) - G s (Y s)))"
        using t0_s_in_existence
        by (auto simp add: flow0_def Y_def intro!: continuous_intros continuous_on_imp_absolutely_integrable_on add_mono)
      also have "... \<le> integral {s..0} (\<lambda>s. K * ?u s) + integral {s..0} (\<lambda>s. e)"
      proof (rule add_mono[OF integral_le integral_le])
        show "norm (F x (flow0 x) - F x (Y x)) \<le> K * norm (flow0 x - Y x)" if "x\<in>{s..0}" for x
          using F_lipschitz[unfolded lipschitz_on_def, THEN conjunct2]
            cont_statements(1,2,4) that
            t0_s_in_existence F_iv_defined (* G.iv_defined *)
          by (metis F_lipschitz flow0_def Y_def \<open>{s..0} \<subseteq> J\<close> lipschitz_on_normD F.flow_in_domain
            G.flow_in_domain subsetCE)
        show "\<And>x. x \<in> {s..0} \<Longrightarrow> norm (F x (Y x) - G x (Y x)) \<le> e"
          using F_G_norm_ineq Y_def \<open>{s..0} \<subseteq> J\<close> cont_statements(5) subset_iff t0_s_in_existence(2)
          using Y_def \<open>{s..0} \<subseteq> J\<close> cont_statements(5) subset_iff G.flow_in_domain
          by (metis eucl_less_le_not_le)
      qed (simp_all add: t0_s_in_existence continuous_intros integrable_on_simps flow0_def Y_def)
      also have "... = K * integral {s..0} (\<lambda>s. ?u s + e / K)"
        using K_pos t0_s_in_existence
        by (simp_all add: algebra_simps Henstock_Kurzweil_Integration.integral_add t0_s_in_existence continuous_intros integrable_on_simps flow0_def Y_def)
      finally show "?u s + e / K \<le> e / K + K * integral {s..0} (\<lambda>s. ?u s + e / K)"
        by simp
    next
      show "continuous_on {t..0} (\<lambda>t. norm (flow0 t - Y t) + e / K)"
        using t0_t_in_J J_subset G.ivl_subset_existence_ivl'[OF tG] F_iv_defined
        by (auto simp add: flow0_def Y_def intro!: continuous_intros)
    next
      fix s assume "t \<le> s" "s \<le> 0"
      show "0 \<le> norm (flow0 s - Y s) + e / K"
        using e_pos K_pos by simp
    next
      show "0 < e / K" using e_pos K_pos by simp
    qed
    thus ?thesis by (simp add: algebra_simps)
  qed
qed

end

end

locale auto_ll_on_open =
  fixes f::"'a::{banach, heine_borel} \<Rightarrow> 'a" and X
  assumes auto_local_lipschitz: "local_lipschitz UNIV X (\<lambda>_::real. f)"
  assumes auto_open_domain[intro!, simp]: "open X"
begin

text \<open>autonomous flow and existence interval \<close>

definition "flow0 x0 t = ll_on_open.flow UNIV (\<lambda>_. f) X 0 x0 t"

definition "existence_ivl0 x0 = ll_on_open.existence_ivl UNIV (\<lambda>_. f) X 0 x0"

sublocale ll_on_open_it UNIV "\<lambda>_. f" X 0
  rewrites "flow = (\<lambda>t0 x0 t. flow0 x0 (t - t0))"
       and "existence_ivl = (\<lambda>t0 x0. (+) t0 ` existence_ivl0 x0)"
       and "(+) 0 = (\<lambda>x::real. x)"
       and "s - 0 = s"
       and "(\<lambda>x. x) ` S = S"
       and "s \<in> (+) t ` S \<longleftrightarrow> s - t \<in> (S::real set)"
       and "P (s + t - s) = P (t::real)"\<comment> \<open>TODO: why does just the equation not work?\<close>
       and "P (t + s - s) = P t"\<comment> \<open>TODO: why does just the equation not work?\<close>
proof -
  interpret ll_on_open UNIV "\<lambda>_. f" X
    by unfold_locales (auto intro!: continuous_on_const auto_local_lipschitz)
  show "ll_on_open_it UNIV (\<lambda>_. f) X" ..
  show "(+) 0 = (\<lambda>x::real. x)" "(\<lambda>x. x) ` S = S" "s - 0 = s" "P (t + s - s) = P t" "P (s + t - s) = P (t::real)"
    by auto
  show "flow = (\<lambda>t0 x0 t. flow0 x0 (t - t0))"
    unfolding flow0_def
    apply (rule ext)
    apply (rule ext)
    apply (rule flow_eq_in_existence_ivlI)
    apply (auto intro: flow_shift_autonomous1
       mem_existence_ivl_shift_autonomous1 mem_existence_ivl_shift_autonomous2)
    done
  show "existence_ivl = (\<lambda>t0 x0. (+) t0 ` existence_ivl0 x0)"
    unfolding existence_ivl0_def
    apply (safe intro!: ext)
    subgoal using image_iff mem_existence_ivl_shift_autonomous1 by fastforce
    subgoal premises prems for t0 x0 x s
    proof -
      have f2: "\<forall>x1 x2. (x2::real) - x1 = - 1 * x1 + x2"
        by auto
      have "- 1 * t0 + (t0 + s) = s"
        by auto
      then show ?thesis
        using f2 prems mem_existence_ivl_iv_defined(2) mem_existence_ivl_shift_autonomous2
        by presburger
    qed
    done
  show "(s \<in> (+) t ` S) = (s - t \<in> S)" by force
qed
\<comment> \<open>at this point, there should be no theorems about \<open>existence_ivl\<close>, only \<open>existence_ivl0\<close>.
Moreover, \<open>(+) _ ` _\<close> and \<open>_ + _ - _\<close> etc should have been removed\<close>

lemma existence_ivl_zero: "x0 \<in> X \<Longrightarrow> 0 \<in> existence_ivl0 x0" by simp

lemmas [continuous_intros del] = continuous_on_f
lemmas continuous_on_f_comp[continuous_intros] = continuous_on_f[OF continuous_on_const _ subset_UNIV]

end

locale compact_continuously_diff =
  derivative_on_prod T X f "\<lambda>(t, x). f' x o\<^sub>L snd_blinfun"
    for T X and f::"real \<Rightarrow> 'a::{banach,perfect_space,heine_borel} \<Rightarrow> 'a"
    and f'::"'a \<Rightarrow> ('a, 'a) blinfun" +
  assumes compact_domain: "compact X"
  assumes convex: "convex X"
  assumes nonempty_domains: "T \<noteq> {}" "X \<noteq> {}"
  assumes continuous_derivative: "continuous_on X f'"
begin

lemma ex_onorm_bound:
  "\<exists>B. \<forall>x \<in> X. norm (f' x) \<le> B"
proof -
  from _ compact_domain have "compact (f' ` X)"
    by (intro compact_continuous_image continuous_derivative)
  hence "bounded (f' ` X)" by (rule compact_imp_bounded)
  thus ?thesis
    by (auto simp add: bounded_iff cball_def norm_blinfun.rep_eq)
qed

definition "onorm_bound = (SOME B. \<forall>x \<in> X. norm (f' x) \<le> B)"

lemma onorm_bound: assumes "x \<in> X" shows "norm (f' x) \<le> onorm_bound"
  unfolding onorm_bound_def
  using someI_ex[OF ex_onorm_bound] assms
  by blast

sublocale closed_domain X
  using compact_domain by unfold_locales (rule compact_imp_closed)

sublocale global_lipschitz T X f onorm_bound
proof (unfold_locales, rule lipschitz_onI)
  fix t z y
  assume "t \<in> T" "y \<in> X" "z \<in> X"
  then have "norm (f t y - f t z) \<le> onorm_bound * norm (y - z)"
    using onorm_bound
    by (intro differentiable_bound[where f'=f', OF convex])
       (auto intro!: derivative_eq_intros simp: norm_blinfun.rep_eq)
  thus "dist (f t y) (f t z) \<le> onorm_bound * dist y z"
    by (auto simp: dist_norm norm_Pair)
next
  from nonempty_domains obtain x where x: "x \<in> X" by auto
  show "0 \<le> onorm_bound"
    using dual_order.trans local.onorm_bound norm_ge_zero x by blast
qed

end \<comment> \<open>@{thm compact_domain}\<close>

locale unique_on_compact_continuously_diff = self_mapping +
  compact_interval T +
  compact_continuously_diff T X f
begin

sublocale unique_on_closed t0 T x0 f X onorm_bound
  by unfold_locales (auto intro!: f' has_derivative_continuous_on)

end

locale c1_on_open =
  fixes f::"'a::{banach, perfect_space, heine_borel} \<Rightarrow> 'a" and f' X
  assumes open_dom[simp]: "open X"
  assumes derivative_rhs:
    "\<And>x. x \<in> X \<Longrightarrow> (f has_derivative blinfun_apply (f' x)) (at x)"
  assumes continuous_derivative: "continuous_on X f'"
begin

lemmas continuous_derivative_comp[continuous_intros] =
  continuous_on_compose2[OF continuous_derivative]

lemma derivative_tendsto[tendsto_intros]:
  assumes [tendsto_intros]: "(g \<longlongrightarrow> l) F"
    and "l \<in> X"
  shows "((\<lambda>x. f' (g x)) \<longlongrightarrow> f' l) F"
  using continuous_derivative[simplified continuous_on] assms
  by (auto simp: at_within_open[OF _ open_dom]
    intro!: tendsto_eq_intros
    intro: tendsto_compose)

lemma c1_on_open_rev[intro, simp]: "c1_on_open (-f) (-f') X"
  using derivative_rhs continuous_derivative
  by unfold_locales
    (auto intro!: continuous_intros derivative_eq_intros
    simp: fun_Compl_def blinfun.bilinear_simps)

lemma derivative_rhs_compose[derivative_intros]:
  "((g has_derivative g') (at x within s)) \<Longrightarrow> g x \<in> X \<Longrightarrow>
    ((\<lambda>x. f (g x)) has_derivative
      (\<lambda>xa. blinfun_apply (f' (g x)) (g' xa)))
    (at x within s)"
  by (metis has_derivative_compose[of g g' x s f "f' (g x)"] derivative_rhs)

sublocale auto_ll_on_open
proof (standard, rule local_lipschitzI)
  fix x and t::real
  assume "x \<in> X"
  with open_contains_cball[of "UNIV::real set"] open_UNIV
    open_contains_cball[of X] open_dom
  obtain u v where uv: "cball t u \<subseteq> UNIV" "cball x v \<subseteq> X" "u > 0" "v > 0"
    by blast
  let ?T = "cball t u" and ?X = "cball x v"
  have "bounded ?X" by simp
  have "compact (cball x v)"
    by simp
  interpret compact_continuously_diff ?T ?X "\<lambda>_. f" f'
    using uv
    by unfold_locales
      (auto simp: convex_cball cball_eq_empty split_beta'
        intro!: derivative_eq_intros continuous_on_compose2[OF continuous_derivative]
          continuous_intros)
  have "onorm_bound-lipschitz_on ?X f"
    using lipschitz[of t] uv
    by auto
  thus "\<exists>u>0. \<exists>L. \<forall>t \<in> cball t u \<inter> UNIV. L-lipschitz_on (cball x u \<inter> X) f"
    by (intro exI[where x=v])
      (auto intro!: exI[where x=onorm_bound] \<open>0 < v\<close> simp: Int_absorb2 uv)
qed (auto intro!: continuous_intros)

end \<comment> \<open>@{thm derivative_rhs}\<close>

locale c1_on_open_euclidean = c1_on_open f f' X
  for f::"'a::euclidean_space \<Rightarrow> _" and f' X
begin
lemma c1_on_open_euclidean_anchor: True ..

definition "vareq x0 t = f' (flow0 x0 t)"

interpretation var: ll_on_open "existence_ivl0 x0" "vareq x0" UNIV
  apply standard
  apply (auto intro!: c1_implies_local_lipschitz[where f' = "\<lambda>(t, x). vareq x0 t"] continuous_intros
      derivative_eq_intros
      simp: split_beta' blinfun.bilinear_simps vareq_def)
  using local.mem_existence_ivl_iv_defined(2) apply blast
  using local.existence_ivl_reverse local.mem_existence_ivl_iv_defined(2) apply blast
  using local.mem_existence_ivl_iv_defined(2) apply blast
  using local.existence_ivl_reverse local.mem_existence_ivl_iv_defined(2) apply blast
  done

context begin

lemma continuous_on_A[continuous_intros]:
  assumes "continuous_on S a"
  assumes "continuous_on S b"
  assumes "\<And>s. s \<in> S \<Longrightarrow> a s \<in> X"
  assumes "\<And>s. s \<in> S \<Longrightarrow> b s \<in> existence_ivl0 (a s)"
  shows "continuous_on S (\<lambda>s. vareq (a s) (b s))"
proof -
  have "continuous_on S (\<lambda>x. f' (flow0 (a x) (b x)))"
    by (auto intro!: continuous_intros assms flow_in_domain)
  then show ?thesis
    by (rule continuous_on_eq) (auto simp: assms vareq_def)
qed

lemmas [intro] = mem_existence_ivl_iv_defined

context
  fixes x0::'a
begin

lemma flow0_defined: "xa \<in> existence_ivl0 x0 \<Longrightarrow> flow0 x0 xa \<in> X"
  by (auto simp: flow_in_domain)

lemma continuous_on_flow0: "continuous_on (existence_ivl0 x0) (flow0 x0)"
  by (auto simp: intro!: continuous_intros)

lemmas continuous_on_flow0_comp[continuous_intros] = continuous_on_compose2[OF continuous_on_flow0]

lemma varexivl_eq_exivl:
  assumes "t \<in> existence_ivl0 x0"
  shows "var.existence_ivl x0 t a = existence_ivl0 x0"
proof (rule var.existence_ivl_eq_domain)
  fix s t x
  assume s: "s \<in> existence_ivl0 x0" and t: "t \<in> existence_ivl0 x0"
  then have "{s .. t} \<subseteq> existence_ivl0 x0"
    by (metis atLeastatMost_empty_iff2 empty_subsetI real_Icc_closed_segment var.closed_segment_subset_domain)
  then have "continuous_on {s .. t} (vareq x0)"
    by (auto simp: closed_segment_eq_real_ivl intro!: continuous_intros flow0_defined)
  then have "compact ((vareq x0) ` {s .. t})"
    using compact_Icc
    by (rule compact_continuous_image)
  then obtain B where B: "\<And>u. u \<in> {s .. t} \<Longrightarrow> norm (vareq x0 u) \<le> B"
    by (force dest!: compact_imp_bounded simp: bounded_iff)
  show "\<exists>M L. \<forall>t\<in>{s..t}. \<forall>x\<in>UNIV. norm (blinfun_apply (vareq x0 t) x) \<le> M + L * norm x"
    by (rule exI[where x=0], rule exI[where x=B])
      (auto intro!: order_trans[OF norm_blinfun] mult_right_mono B simp:)
qed (auto intro: assms)

definition "vector_Dflow u0 t \<equiv> var.flow x0 0 u0 t"

qualified abbreviation "Y z t \<equiv> flow0 (x0 + z) t"

text \<open>Linearity of the solution to the variational equation.
  TODO: generalize this and some other things for arbitrary linear ODEs\<close>
lemma vector_Dflow_linear:
assumes "t \<in> existence_ivl0 x0"
shows "vector_Dflow (\<alpha> *\<^sub>R a + \<beta> *\<^sub>R b) t = \<alpha> *\<^sub>R vector_Dflow a t + \<beta> *\<^sub>R vector_Dflow b t"
proof -
  note mem_existence_ivl_iv_defined[OF assms, intro, simp]
  have "((\<lambda>c. \<alpha> *\<^sub>R var.flow x0 0 a c + \<beta> *\<^sub>R var.flow x0 0 b c) solves_ode (\<lambda>x. vareq x0 x)) (existence_ivl0 x0) UNIV"
    by (auto intro!: derivative_intros var.flow_has_vector_derivative solves_odeI
      simp: blinfun.bilinear_simps varexivl_eq_exivl vareq_def[symmetric])
  moreover
  have "\<alpha> *\<^sub>R var.flow x0 0 a 0 + \<beta> *\<^sub>R var.flow x0 0 b 0 = \<alpha> *\<^sub>R a + \<beta> *\<^sub>R b" by simp
  moreover note is_interval_existence_ivl[of x0]
  ultimately show ?thesis
    unfolding vareq_def[symmetric] vector_Dflow_def
    by (rule var.maximal_existence_flow) (auto simp: assms)
qed

lemma linear_vector_Dflow:
assumes "t \<in> existence_ivl0 x0"
shows "linear (\<lambda>z. vector_Dflow z t)"
using vector_Dflow_linear[OF assms, of 1 _ 1] vector_Dflow_linear[OF assms, of _ _ 0]
by (auto intro!: linearI)

lemma bounded_linear_vector_Dflow:
assumes "t \<in> existence_ivl0 x0"
shows "bounded_linear (\<lambda>z. vector_Dflow z t)"
by (simp add: linear_linear linear_vector_Dflow assms)

lemma vector_Dflow_continuous_on_time: "x0 \<in> X \<Longrightarrow> continuous_on (existence_ivl0 x0) (\<lambda>t. vector_Dflow z t)"
  using var.flow_continuous_on[of x0 0 z] varexivl_eq_exivl
  unfolding vector_Dflow_def
  by (auto simp:  )

proposition proposition_17_6_weak:
  \<comment> \<open>from "Differential Equations, Dynamical Systems, and an Introduction to Chaos",
    Hirsch/Smale/Devaney\<close>
assumes "t \<in> existence_ivl0 x0"
shows "(\<lambda>y. (Y (y - x0) t - flow0 x0 t - vector_Dflow (y - x0) t) /\<^sub>R norm (y - x0)) \<midarrow> x0 \<rightarrow> 0"
proof-
  note x0_def = mem_existence_ivl_iv_defined[OF assms]
  have "0 \<in> existence_ivl0 x0"
    by (simp add: x0_def)

  text \<open>Find some \<open>J \<subseteq> existence_ivl0 x0\<close> with \<open>0 \<in> J\<close> and \<open>t \<in> J\<close>.\<close>
  define t0 where "t0 \<equiv> min 0 t"
  define t1 where "t1 \<equiv> max 0 t"
  define J where "J \<equiv> {t0..t1}"

  have "t0 \<le> 0" "0 \<le> t1" "0 \<in> J" "J \<noteq> {}" "t \<in> J" "compact J"
  and J_in_existence: "J \<subseteq> existence_ivl0 x0"
    using ivl_subset_existence_ivl ivl_subset_existence_ivl' x0_def assms
    by (auto simp add: J_def t0_def t1_def min_def max_def)

  {
    fix z S
    assume assms: "x0 + z \<in> X" "S \<subseteq> existence_ivl0 (x0 + z)"
    have "continuous_on S (Y z)"
      using flow_continuous_on assms(1)
      by (intro continuous_on_subset[OF _ assms(2)]) (simp add:)
  }
  note [continuous_intros] = this integrable_continuous_real blinfun.continuous_on

  have U_continuous[continuous_intros]: "\<And>z. continuous_on J (vector_Dflow z)"
    by(rule continuous_on_subset[OF vector_Dflow_continuous_on_time[OF \<open>x0 \<in> X\<close>] J_in_existence])

  from \<open>t \<in> J\<close>
  have "t0 \<le> t"
  and "t \<le> t1"
  and "t0 \<le> t1"
  and "t0 \<in> existence_ivl0 x0"
  and "t \<in> existence_ivl0 x0"
  and "t1 \<in> existence_ivl0 x0"
    using J_def J_in_existence by auto
  from global_existence_ivl_explicit[OF \<open>t0 \<in> existence_ivl0 x0\<close> \<open>t1 \<in> existence_ivl0 x0\<close> \<open>t0 \<le> t1\<close>]
  obtain u K where uK_def:
    "0 < u"
    "0 < K"
    "ball x0 u \<subseteq> X"
    "\<And>y. y \<in> ball x0 u \<Longrightarrow> t0 \<in> existence_ivl0 y"
    "\<And>y. y \<in> ball x0 u \<Longrightarrow> t1 \<in> existence_ivl0 y"
    "\<And>t y. y \<in> ball x0 u \<Longrightarrow> t \<in> J \<Longrightarrow> dist (flow0 x0 t) (Y (y - x0) t) \<le> dist x0 y * exp (K * \<bar>t\<bar>)"
    by (auto simp add: J_def)

  have J_in_existence_ivl: "\<And>y. y \<in> ball x0 u \<Longrightarrow> J \<subseteq> existence_ivl0 y"
    unfolding J_def
    using uK_def
    by (simp add: real_Icc_closed_segment segment_subset_existence_ivl t0_def t1_def)
  have ball_in_X: "\<And>z. z \<in> ball 0 u \<Longrightarrow> x0 + z \<in> X"
    using uK_def(3)
    by (auto simp: dist_norm)

  have flow0_J_props: "flow0 x0 ` J \<noteq> {}" "compact (flow0 x0 ` J)" "flow0 x0` J \<subseteq> X"
    using \<open>t0 \<le> t1\<close>
    using J_def(1) J_in_existence
    by (auto simp add: J_def intro!:
      compact_continuous_image continuous_intros flow_in_domain)

  have [continuous_intros]: "continuous_on J (\<lambda>s. f' (flow0 x0 s))"
    using J_in_existence
    by (auto intro!: continuous_intros flow_in_domain simp:)

  text \<open> Show the thesis via cases \<open>t = 0\<close>, \<open>0 < t\<close> and \<open>t < 0\<close>. \<close>
  show ?thesis
  proof(cases "t = 0")
    assume "t = 0"
    show ?thesis
    unfolding \<open>t = 0\<close> Lim_at
    proof(simp add: dist_norm[of _ 0] del: zero_less_dist_iff, safe, rule exI, rule conjI[OF \<open>0 < u\<close>], safe)
      fix e::real and x assume "0 < e" "0 < dist x x0" "dist x x0 < u"
      hence "x \<in> X"
        using uK_def(3)
        by (auto simp: dist_commute)
      hence "inverse (norm (x - x0)) * norm (Y (x - x0) 0 - flow0 x0 0 - vector_Dflow (x - x0) 0) = 0"
        using x0_def
        by (simp add: vector_Dflow_def)
      thus "inverse (norm (x - x0)) * norm (flow0 x 0 - flow0 x0 0 - vector_Dflow (x - x0) 0) < e"
        using \<open>0 < e\<close> by auto
    qed
  next
    assume "t \<noteq> 0"
    show ?thesis
    proof(unfold Lim_at, safe)
      fix e::real assume "0 < e"
      then obtain e' where "0 < e'" "e' < e"
        using dense by auto

      obtain N
        where N_ge_SupS: "Sup { norm (f' (flow0 x0 s)) |s. s \<in> J } \<le> N" (is "Sup ?S \<le> N")
          and N_gr_0: "0 < N"
        \<comment> \<open>We need N to be an upper bound of @{term ?S}, but also larger than zero.\<close>
        by (meson le_cases less_le_trans linordered_field_no_ub)
      have N_ineq: "\<And>s. s \<in> J \<Longrightarrow> norm (f' (flow0 x0 s)) \<le> N"
        proof-
          fix s assume "s \<in> J"
          have "?S = (norm o f' o flow0 x0) ` J" by auto
          moreover have "continuous_on J (norm o f' o flow0 x0)"
            using J_in_existence
            by (auto intro!: continuous_intros)
          ultimately have  "\<exists>a b. ?S = {a..b} \<and> a \<le> b"
            using continuous_image_closed_interval[OF \<open>t0 \<le> t1\<close>]
            by (simp add: J_def)
          then obtain a b where "?S = {a..b}" and "a \<le> b" by auto
          hence "bdd_above ?S" by simp
          from \<open>s \<in> J\<close>  cSup_upper[OF _ this]
          have "norm (f' (flow0 x0 s)) \<le> Sup ?S"
            by auto
          thus "norm (f' (flow0 x0 s)) \<le> N"
            using N_ge_SupS by simp
        qed

      text \<open> Define a small region around \<open>flow0 ` J\<close>, that is a subset of the domain \<open>X\<close>. \<close>
      from compact_in_open_separated[OF flow0_J_props(1,2) auto_open_domain flow0_J_props(3)]
        obtain e_domain where e_domain_def: "0 < e_domain" "{x. infdist x (flow0 x0 ` J) \<le> e_domain} \<subseteq> X"
        by auto
      define G where "G \<equiv> {x\<in>X. infdist x (flow0 x0 ` J) < e_domain}"
      have G_vimage: "G = ((\<lambda>x. infdist x (flow0 x0 ` J)) -` {..<e_domain}) \<inter> X"
        by (auto simp: G_def)
      have "open G" "G \<subseteq> X"
        unfolding G_vimage
        by (auto intro!: open_Int open_vimage continuous_intros continuous_at_imp_continuous_on)

      text \<open>Define a compact subset H of G. Inside H, we can guarantee
         an upper bound on the Taylor remainder.\<close>
      define e_domain2 where "e_domain2 \<equiv> e_domain / 2"
      have "e_domain2 > 0" "e_domain2 < e_domain" using \<open>e_domain > 0\<close>
        by (simp_all add: e_domain2_def)
      define H where "H \<equiv> {x. infdist x (flow0 x0 ` J) \<le> e_domain2}"
      have H_props: "H \<noteq> {}" "compact H" "H \<subseteq> G"
        proof-
          have "x0 \<in> flow0 x0 ` J"
            unfolding image_iff
            using \<open>0 \<in> J\<close>  x0_def
            by force

          hence "x0 \<in> H"
            using \<open>0 < e_domain2\<close>
            by (simp add: H_def x0_def)
          thus "H \<noteq> {}"
            by auto
        next
          show "compact H"
            unfolding H_def
            using \<open>0 < e_domain2\<close> flow0_J_props
            by (intro compact_infdist_le) simp_all
        next
          show "H \<subseteq> G"
          proof
            fix x assume "x \<in> H"
            then have *: "infdist x (flow0 x0 ` J) < e_domain"
              using \<open>0 < e_domain\<close>
              by (simp add: H_def e_domain2_def)
            then have "x \<in> X"
              using e_domain_def(2)
              by auto
            with * show "x \<in> G"
              unfolding G_def
              by auto
          qed
        qed

      have f'_cont_on_G: "(\<And>x. x \<in> G \<Longrightarrow> isCont f' x)"
        using continuous_on_interior[OF continuous_on_subset[OF continuous_derivative \<open>G \<subseteq> X\<close>]]
        by (simp add: interior_open[OF \<open>open G\<close>])

      define e1 where "e1 \<equiv> e' / (\<bar>t\<bar> * exp (K * \<bar>t\<bar>) * exp (N * \<bar>t\<bar>))"
        \<comment> \<open>@{term e1} is the bounding term for the Taylor remainder.\<close>
      have "0 < \<bar>t\<bar>"
        using \<open>t \<noteq> 0\<close>
        by simp
      hence "0 < e1"
        using \<open>0 < e'\<close>
        by (simp add: e1_def)

      text \<open> Taylor expansion of f on set G. \<close>
      from uniform_explicit_remainder_Taylor_1[where f=f and f'=f',
        OF derivative_rhs[OF subsetD[OF \<open>G \<subseteq> X\<close>]] f'_cont_on_G \<open>open G\<close> H_props \<open>0 < e1\<close>]
      obtain d_Taylor R
      where Taylor_expansion:
        "0 < d_Taylor"
        "\<And>x z. f z = f x + (f' x) (z - x) + R x z"
        "\<And>x y. x \<in> H \<Longrightarrow> y \<in> H \<Longrightarrow> dist x y < d_Taylor \<Longrightarrow> norm (R x y) \<le> e1 * dist x y"
        "continuous_on (G \<times> G) (\<lambda>(a, b). R a b)"
          by auto

      text \<open> Find d, such that solutions are always at least \<open>min (e_domain/2) d_Taylor\<close> apart,
         i.e. always in H. This later gives us the bound on the remainder. \<close>
      have "0 < min (e_domain/2) d_Taylor"
        using \<open>0 < d_Taylor\<close> \<open>0 < e_domain\<close>
        by auto
      from uniform_limit_flow[OF \<open>t0 \<in> existence_ivl0 x0\<close> \<open>t1 \<in> existence_ivl0 x0\<close> \<open>t0 \<le> t1\<close>,
        THEN uniform_limitD, OF this, unfolded eventually_at]
      obtain d_ivl where d_ivl_def:
        "0 < d_ivl"
        "\<And>x. 0 < dist x x0 \<Longrightarrow> dist x x0 < d_ivl \<Longrightarrow>
          (\<forall>t\<in>J. dist (flow0 x0 t) (Y (x - x0) t) < min (e_domain / 2) d_Taylor)"
        by (auto simp: dist_commute J_def)

      define d where "d \<equiv> min u d_ivl"
      have "0 < d" using \<open>0 < u\<close> \<open>0 < d_ivl\<close>
        by (simp add: d_def)
      hence "d \<le> u" "d \<le> d_ivl"
        by (auto simp: d_def)

      text \<open> Therefore, any flow0 starting in \<open>ball x0 d\<close> will be in G. \<close>
      have Y_in_G: "\<And>y. y \<in> ball x0 d \<Longrightarrow> (\<lambda>s. Y (y - x0) s) ` J \<subseteq> G"
        proof
          fix x y assume assms: "y \<in> ball x0 d" "x \<in> (\<lambda>s. Y (y - x0) s) ` J"
          show "x \<in> G"
          proof(cases)
            assume "y = x0"
            from assms(2)
            have "x \<in> flow0 x0 ` J"
              by (simp add: \<open>y = x0\<close>)
            thus "x \<in> G"
              using \<open>0 < e_domain\<close> \<open>flow0 x0 ` J \<subseteq> X\<close>
              by (auto simp: G_def)
          next
            assume "y \<noteq> x0"
            hence "0 < dist y x0"
              by (simp add: dist_norm)
            from d_ivl_def(2)[OF this] \<open>d \<le> d_ivl\<close>  \<open>0 < e_domain\<close> assms(1)
            have dist_flow0_Y: "\<And>t. t \<in> J \<Longrightarrow> dist (flow0 x0 t) (Y (y - x0) t) < e_domain"
              by (auto simp: dist_commute)

            from assms(2)
            obtain t where t_def: "t \<in> J" "x = Y (y - x0) t"
              by auto
            have "x \<in> X"
              unfolding t_def(2)
              using uK_def(3) assms(1) \<open>d \<le> u\<close> subsetD[OF J_in_existence_ivl t_def(1)]
              by (auto simp: intro!: flow_in_domain)

            have "flow0 x0 t \<in> flow0 x0 ` J" using t_def by auto
            from dist_flow0_Y[OF t_def(1)]
            have "dist x (flow0 x0 t) < e_domain"
              by (simp add: t_def(2) dist_commute)
            from le_less_trans[OF infdist_le[OF \<open>flow0 x0 t \<in> flow0 x0 ` J\<close>] this] \<open>x \<in> X\<close>
            show "x \<in> G"
              by (auto simp: G_def)
          qed
        qed
      from this[of x0] \<open>0 < d\<close>
      have X_in_G: "flow0 x0 ` J \<subseteq> G"
        by (simp add: )

      show "\<exists>d>0. \<forall>x. 0 < dist x x0 \<and> dist x x0 < d \<longrightarrow>
                     dist ((Y (x - x0) t - flow0 x0 t - vector_Dflow (x - x0) t) /\<^sub>R norm (x - x0)) 0 < e"
      proof(rule exI, rule conjI[OF \<open>0 < d\<close>], safe, unfold norm_conv_dist[symmetric])
        fix x assume x_x0_dist: "0 < dist x x0" "dist x x0 < d"
        hence x_in_ball': "x \<in> ball x0 d"
          by (simp add: dist_commute)
        hence x_in_ball: "x \<in> ball x0 u"
          using \<open>d \<le> u\<close>
          by simp

        text \<open> First, some prerequisites. \<close>
        from x_in_ball
        have z_in_ball: "x - x0 \<in> ball 0 u"
          using \<open>0 < u\<close>
          by (simp add: dist_norm)
        hence [continuous_intros]: "dist x0 x < u"
          by (auto simp: dist_norm)

        from J_in_existence_ivl[OF x_in_ball]
        have J_in_existence_ivl_x: "J \<subseteq> existence_ivl0 x" .
        from ball_in_X[OF z_in_ball]
        have x_in_X[continuous_intros]: "x \<in> X"
          by simp

        text \<open> On all of \<open>J\<close>, we can find upper bounds for the distance of \<open>flow0\<close> and \<open>Y\<close>. \<close>
        have dist_flow0_Y: "\<And>s. s \<in> J \<Longrightarrow> dist (flow0 x0 s) (Y (x - x0) s) \<le> dist x0 x * exp (K * \<bar>t\<bar>)"
          using t0_def t1_def uK_def(2)
          by (intro order_trans[OF uK_def(6)[OF x_in_ball] mult_left_mono])
             (auto simp add: J_def intro!: mult_mono)
        from d_ivl_def x_x0_dist \<open>d \<le> d_ivl\<close>
        have dist_flow0_Y2: "\<And>t. t \<in> J \<Longrightarrow> dist (flow0 x0 t) (Y (x - x0) t) < min (e_domain2) d_Taylor"
          by (auto simp: e_domain2_def)

        let ?g = "\<lambda>t. norm (Y (x - x0) t - flow0 x0 t - vector_Dflow (x - x0) t)"
        let ?C = "\<bar>t\<bar> * dist x0 x * exp (K * \<bar>t\<bar>) * e1"
        text \<open> Find an upper bound to \<open>?g\<close>, i.e. show that
             \<open>?g s \<le> ?C + N * integral {a..b} ?g\<close>
           for \<open>{a..b} = {0..s}\<close> or \<open>{a..b} = {s..0}\<close> for some \<open>s \<in> J\<close>.
           We can then apply Grönwall's inequality to obtain a true bound for \<open>?g\<close>. \<close>
        have g_bound: "?g s \<le> ?C + N * integral {a..b} ?g"
          if s_def: "s \<in> {a..b}"
          and J'_def: "{a..b} \<subseteq> J"
          and ab_cases: "(a = 0 \<and> b = s) \<or> (a = s \<and> b = 0)"
          for s a b
        proof -
          from that have "s \<in> J" by auto

          have s_in_existence_ivl_x0: "s \<in> existence_ivl0 x0"
            using J_in_existence \<open>s \<in> J\<close> by auto
          have s_in_existence_ivl: "\<And>y. y \<in> ball x0 u \<Longrightarrow> s \<in> existence_ivl0 y"
            using J_in_existence_ivl \<open>s \<in> J\<close> by auto
          have s_in_existence_ivl2: "\<And>z. z \<in> ball 0 u \<Longrightarrow> s \<in> existence_ivl0 (x0 + z)"
            using s_in_existence_ivl
            by (simp add: dist_norm)

          text \<open>Prove continuities beforehand.\<close>
          note continuous_on_0_s[continuous_intros] = continuous_on_subset[OF _ \<open>{a..b} \<subseteq> J\<close>]

          have[continuous_intros]: "continuous_on J (flow0 x0)"
            using J_in_existence
            by (auto intro!: continuous_intros simp:)
          {
            fix z S
            assume assms: "x0 + z \<in> X" "S \<subseteq> existence_ivl0 (x0 + z)"
            have "continuous_on S (\<lambda>s. f (Y z s))"
            proof(rule continuous_on_subset[OF _ assms(2)])
              show "continuous_on (existence_ivl0 (x0 + z)) (\<lambda>s. f (Y z s))"
                using assms
                by (auto intro!: continuous_intros flow_in_domain flow_continuous_on simp:)
            qed
          }
          note [continuous_intros] = this

          have [continuous_intros]: "continuous_on J (\<lambda>s. f (flow0 x0 s))"
            by(rule continuous_on_subset[OF _ J_in_existence])
              (auto intro!: continuous_intros flow_continuous_on flow_in_domain simp: x0_def)

          have [continuous_intros]: "\<And>z. continuous_on J (\<lambda>s. f' (flow0 x0 s) (vector_Dflow z s))"
          proof-
            fix z
            have a1: "continuous_on J (flow0 x0)"
              by (auto intro!: continuous_intros)

            have a2: "(\<lambda>s. (flow0 x0 s, vector_Dflow z s)) ` J \<subseteq> (flow0 x0 ` J) \<times> ((\<lambda>s. vector_Dflow z s) ` J)"
              by auto
            have a3: "continuous_on ((\<lambda>s. (flow0 x0 s, vector_Dflow z s)) ` J) (\<lambda>(x, u). f' x u)"
              using assms flow0_J_props
              by (auto intro!: continuous_intros simp: split_beta')
            from continuous_on_compose[OF continuous_on_Pair[OF a1 U_continuous] a3]
            show "continuous_on J (\<lambda>s. f' (flow0 x0 s) (vector_Dflow z s))"
              by simp
          qed

          have [continuous_intros]: "continuous_on J (\<lambda>s. R (flow0 x0 s) (Y (x - x0) s))"
            using J_in_existence J_in_existence_ivl[OF x_in_ball] X_in_G \<open>{a..b} \<subseteq> J\<close> Y_in_G
              x_x0_dist
            by (auto intro!: continuous_intros continuous_on_compose_Pair[OF Taylor_expansion(4)]
              simp: dist_commute subset_iff)
          hence [continuous_intros]:
            "(\<lambda>s. R (flow0 x0 s) (Y (x - x0) s)) integrable_on J"
            unfolding J_def
            by (rule integrable_continuous_real)

          have i1: "integral {a..b} (\<lambda>s. f (flow0 x s)) - integral {a..b} (\<lambda>s. f (flow0 x0 s)) =
              integral {a..b} (\<lambda>s. f (flow0 x s) - f (flow0 x0 s))"
            using J_in_existence_ivl[OF x_in_ball]
            apply (intro Henstock_Kurzweil_Integration.integral_diff[symmetric])
             by (auto intro!: continuous_intros existence_ivl_reverse)
          have i2:
            "integral {a..b} (\<lambda>s. f (flow0 x s) - f (flow0 x0 s) - (f' (flow0 x0 s)) (vector_Dflow (x - x0) s)) =
              integral {a..b} (\<lambda>s. f (flow0 x s) - f (flow0 x0 s)) -
              integral {a..b} (\<lambda>s. f' (flow0 x0 s) (vector_Dflow (x - x0) s))"
            using J_in_existence_ivl[OF x_in_ball]
            by (intro Henstock_Kurzweil_Integration.integral_diff[OF Henstock_Kurzweil_Integration.integrable_diff])
              (auto intro!: continuous_intros existence_ivl_reverse)
          from ab_cases
          have "?g s = norm (integral {a..b} (\<lambda>s'. f (Y (x - x0) s')) -
            integral {a..b} (\<lambda>s'. f (flow0 x0 s')) -
            integral {a..b} (\<lambda>s'. (f' (flow0 x0 s')) (vector_Dflow (x - x0) s')))"
          proof(safe)
            assume "a = 0" "b = s"
            hence "0 \<le> s" using \<open>s \<in> {a..b}\<close> by simp

            text\<open> Integral equations for flow0, Y and U. \<close>
            have flow0_integral_eq: "flow0 x0 s = x0 + ivl_integral 0 s (\<lambda>s. f (flow0 x0 s))"
              by (rule flow_fixed_point[OF s_in_existence_ivl_x0])
            have Y_integral_eq: "flow0 x s = x0 + (x - x0) + ivl_integral 0 s (\<lambda>s. f (Y (x - x0) s))"
              using flow_fixed_point \<open>0 \<le> s\<close> s_in_existence_ivl2[OF z_in_ball] ball_in_X[OF z_in_ball]
              by (simp add:)
            have U_integral_eq: "vector_Dflow (x - x0) s = (x - x0) + ivl_integral 0 s (\<lambda>s. vareq x0 s (vector_Dflow (x - x0) s))"
              unfolding vector_Dflow_def
              by (rule var.flow_fixed_point)
                (auto simp: \<open>0 \<le> s\<close> x0_def varexivl_eq_exivl s_in_existence_ivl_x0)
            show "?g s = norm (integral {0..s} (\<lambda>s'. f (Y (x - x0) s')) -
                integral {0..s} (\<lambda>s'. f (flow0 x0 s')) -
                integral {0..s} (\<lambda>s'. blinfun_apply (f' (flow0 x0 s')) (vector_Dflow (x - x0) s')))"
              using \<open>0 \<le> s\<close>
              unfolding vareq_def[symmetric]
              by (simp add: flow0_integral_eq Y_integral_eq U_integral_eq ivl_integral_def)
          next
            assume "a = s" "b = 0"
            hence "s \<le> 0" using \<open>s \<in> {a..b}\<close> by simp

            have flow0_integral_eq_left: "flow0 x0 s = x0 + ivl_integral 0 s (\<lambda>s. f (flow0 x0 s))"
              by (rule flow_fixed_point[OF s_in_existence_ivl_x0])
            have Y_integral_eq_left: "Y (x - x0) s = x0 + (x - x0) + ivl_integral 0 s (\<lambda>s. f (Y (x - x0) s))"
              using flow_fixed_point \<open>s \<le> 0\<close> s_in_existence_ivl2[OF z_in_ball] ball_in_X[OF z_in_ball]
              by (simp add: )
            have U_integral_eq_left: "vector_Dflow (x - x0) s = (x - x0) + ivl_integral 0 s (\<lambda>s. vareq x0 s (vector_Dflow (x - x0) s))"
              unfolding vector_Dflow_def
              by (rule var.flow_fixed_point)
                (auto simp: \<open>s \<le> 0\<close> x0_def varexivl_eq_exivl s_in_existence_ivl_x0)

            have "?g s =
              norm (- integral {s..0} (\<lambda>s'. f (Y (x - x0) s')) +
                integral {s..0} (\<lambda>s'. f (flow0 x0 s')) +
                integral {s..0} (\<lambda>s'. vareq x0 s' (vector_Dflow (x - x0) s')))"
              unfolding flow0_integral_eq_left Y_integral_eq_left U_integral_eq_left
              using \<open>s \<le> 0\<close>
              by (simp add: ivl_integral_def)
            also have "... = norm (integral {s..0} (\<lambda>s'. f (Y (x - x0) s')) -
                integral {s..0} (\<lambda>s'. f (flow0 x0 s')) -
                integral {s..0} (\<lambda>s'. vareq x0 s' (vector_Dflow (x - x0) s')))"
              by (subst norm_minus_cancel[symmetric], simp)
            finally show "?g s =
              norm (integral {s..0} (\<lambda>s'. f (Y (x - x0) s')) -
                integral {s..0} (\<lambda>s'. f (flow0 x0 s')) -
                integral {s..0} (\<lambda>s'. blinfun_apply (f' (flow0 x0 s')) (vector_Dflow (x - x0) s')))"
              unfolding vareq_def .
          qed
          also have "... =
            norm (integral {a..b} (\<lambda>s. f (Y (x - x0) s) - f (flow0 x0 s) - (f' (flow0 x0 s)) (vector_Dflow (x - x0) s)))"
            by (simp add: i1 i2)
          also have "... \<le>
            integral {a..b} (\<lambda>s. norm (f (Y (x - x0) s) - f (flow0 x0 s) - f' (flow0 x0 s) (vector_Dflow (x - x0) s)))"
            using x_in_X J_in_existence_ivl_x J_in_existence \<open>{a..b} \<subseteq> J\<close>
            by (auto intro!: continuous_intros continuous_on_imp_absolutely_integrable_on
                existence_ivl_reverse)
          also have "... = integral {a..b}
              (\<lambda>s. norm (f' (flow0 x0 s) (Y (x - x0) s - flow0 x0 s - vector_Dflow (x - x0) s) + R (flow0 x0 s) (Y (x - x0) s)))"
          proof (safe intro!: integral_spike[OF negligible_empty, simplified] arg_cong[where f=norm])
            fix s' assume "s' \<in> {a..b}"
            show "f' (flow0 x0 s') (Y (x - x0) s' - flow0 x0 s' - vector_Dflow (x - x0) s') + R (flow0 x0 s') (Y (x - x0) s') =
              f (Y (x - x0) s') - f (flow0 x0 s') - f' (flow0 x0 s') (vector_Dflow (x - x0) s')"
              by (simp add: blinfun.diff_right Taylor_expansion(2)[of "flow0 x s'" "flow0 x0 s'"])
          qed
          also have "... \<le> integral {a..b}
            (\<lambda>s. norm (f' (flow0 x0 s) (Y (x - x0) s - flow0 x0 s - vector_Dflow (x - x0) s)) +
              norm (R (flow0 x0 s) (Y (x - x0) s)))"
            using J_in_existence_ivl[OF x_in_ball] norm_triangle_ineq
            using \<open>continuous_on J (\<lambda>s. R (flow0 x0 s) (Y (x - x0) s))\<close>
            by (auto intro!: continuous_intros integral_le)
          also have "... =
            integral {a..b} (\<lambda>s. norm (f' (flow0 x0 s) (Y (x - x0) s - flow0 x0 s - vector_Dflow (x - x0) s))) +
            integral {a..b} (\<lambda>s. norm (R (flow0 x0 s) (Y (x - x0) s)))"
            using J_in_existence_ivl[OF x_in_ball]
            using \<open>continuous_on J (\<lambda>s. R (flow0 x0 s) (Y (x - x0) s))\<close>
            by (auto intro!: continuous_intros Henstock_Kurzweil_Integration.integral_add)
          also have "... \<le> N * integral {a..b} ?g + ?C" (is "?l1 + ?r1 \<le> _")
          proof(rule add_mono)
            have "?l1 \<le> integral {a..b} (\<lambda>s. norm (f' (flow0 x0 s)) * norm (Y (x - x0) s - flow0 x0 s - vector_Dflow (x - x0) s))"
              using norm_blinfun J_in_existence_ivl[OF x_in_ball]
              by (auto intro!: continuous_intros integral_le)

            also have "... \<le> integral {a..b} (\<lambda>s. N * norm (Y (x - x0) s - flow0 x0 s - vector_Dflow (x - x0) s))"
              using J_in_existence_ivl[OF x_in_ball] N_ineq[OF \<open>{a..b} \<subseteq> J\<close>[THEN subsetD]]
              by (intro integral_le) (auto intro!: continuous_intros mult_right_mono)
              
            also have "... = N * integral {a..b} (\<lambda>s. norm ((Y (x - x0) s - flow0 x0 s - vector_Dflow (x - x0) s)))"
              unfolding real_scaleR_def[symmetric]
              by(rule integral_cmul)
            finally show "?l1 \<le> N * integral {a..b} ?g" .
          next
            have "?r1 \<le> integral {a..b} (\<lambda>s. e1 * dist (flow0 x0 s) (Y (x - x0) s))"
              using J_in_existence_ivl[OF x_in_ball] \<open>0 < e_domain\<close> dist_flow0_Y2 \<open>0 < e_domain2\<close>
              by (intro integral_le)
                (force
                  intro!: continuous_intros Taylor_expansion(3) order_trans[OF infdist_le]
                   dest!: \<open>{a..b} \<subseteq> J\<close>[THEN subsetD]
                   intro: less_imp_le
                   simp: dist_commute H_def)+
            also have "... \<le> integral {a..b} (\<lambda>s. e1 * (dist x0 x * exp (K * \<bar>t\<bar>)))"
              apply(rule integral_le)
              subgoal using J_in_existence_ivl[OF x_in_ball] by (force intro!: continuous_intros)
              subgoal by force
              subgoal by (force dest!: \<open>{a..b} \<subseteq> J\<close>[THEN subsetD]
                intro!: less_imp_le[OF \<open>0 < e1\<close>] mult_left_mono[OF dist_flow0_Y])
              done
            also have "... \<le> ?C"
              using \<open>s \<in> J\<close> x_x0_dist \<open>0 < e1\<close> \<open>{a..b} \<subseteq> J\<close> \<open>0 < \<bar>t\<bar>\<close> t0_def t1_def
              by (auto simp: integral_const_real J_def(1))
            finally show "?r1 \<le> ?C" .
          qed
          finally show ?thesis
            by simp
        qed
        have g_continuous: "continuous_on J ?g"
          using J_in_existence_ivl[OF x_in_ball] J_in_existence
          using J_def(1) U_continuous
          by (auto simp: J_def intro!: continuous_intros)
        note [continuous_intros] = continuous_on_subset[OF g_continuous]
        have C_gr_zero: "0 < ?C"
          using \<open>0 < \<bar>t\<bar>\<close> \<open>0 < e1\<close> x_x0_dist(1)
          by (simp add: dist_commute)
        have "0 \<le> t \<or> t \<le> 0" by auto
        then have "?g t \<le> ?C * exp (N * \<bar>t\<bar>)"
        proof
          assume "0 \<le> t"
          moreover
          have "continuous_on {0..t} (vector_Dflow (x - x0))"
            using U_continuous
            by (rule continuous_on_subset) (auto simp: J_def t0_def t1_def)
          then have "norm (Y (x - x0) t - flow0 x0 t - vector_Dflow (x - x0) t) \<le>
            \<bar>t\<bar> * dist x0 x * exp (K * \<bar>t\<bar>) * e1 * exp (N * t)"
            using \<open>t \<in> J\<close> J_def \<open>t0 \<le> 0\<close> J_in_existence J_in_existence_ivl_x
            by (intro gronwall[OF g_bound _ _ C_gr_zero \<open>0 < N\<close> \<open>0 \<le> t\<close> order.refl])
               (auto intro!: continuous_intros simp: )
          ultimately show ?thesis by simp
        next
          assume "t \<le> 0"
          moreover
          have "continuous_on {t .. 0} (vector_Dflow (x - x0))"
            using U_continuous
            by (rule continuous_on_subset) (auto simp: J_def t0_def t1_def)
          then have "norm (Y (x - x0) t - flow0 x0 t - vector_Dflow (x - x0) t) \<le>
            \<bar>t\<bar> * dist x0 x * exp (K * \<bar>t\<bar>) * e1 * exp (- N * t)"
            using \<open>t \<in> J\<close> J_def \<open>0 \<le> t1\<close> J_in_existence J_in_existence_ivl_x
            by (intro gronwall_left[OF g_bound _ _ C_gr_zero \<open>0 < N\<close> order.refl \<open>t \<le> 0\<close>])
                (auto intro!: continuous_intros)
          ultimately show ?thesis
            by simp
        qed
        also have "... = dist x x0 * (\<bar>t\<bar> * exp (K * \<bar>t\<bar>) * e1 * exp (N * \<bar>t\<bar>))"
          by (auto simp: dist_commute)
        also have "... < norm (x - x0) * e"
          unfolding e1_def
          using \<open>e' < e\<close> \<open>0 < \<bar>t\<bar>\<close> \<open>0 < e1\<close> x_x0_dist(1)
          by (simp add: dist_norm)
        finally show "norm ((Y (x - x0) t - flow0 x0 t - vector_Dflow (x - x0) t) /\<^sub>R norm (x - x0)) < e"
          by (simp, metis x_x0_dist(1) dist_norm divide_inverse mult.commute pos_divide_less_eq)
      qed
    qed
  qed
qed

lemma local_lipschitz_A:
  "OT \<subseteq> existence_ivl0 x0 \<Longrightarrow> local_lipschitz OT (OS::('a \<Rightarrow>\<^sub>L 'a) set) (\<lambda>t. (o\<^sub>L) (vareq x0 t))"
  by (rule local_lipschitz_subset[OF _ _ subset_UNIV, where T="existence_ivl0 x0"])
     (auto simp: split_beta' vareq_def
      intro!: c1_implies_local_lipschitz[where f'="\<lambda>(t, x). comp3 (f' (flow0 x0 t))"]
        derivative_eq_intros blinfun_eqI ext
        continuous_intros flow_in_domain)

lemma total_derivative_ll_on_open:
  "ll_on_open (existence_ivl0 x0) (\<lambda>t. blinfun_compose (vareq x0 t)) (UNIV::('a \<Rightarrow>\<^sub>L 'a) set)"
  by standard (auto intro!: continuous_intros local_lipschitz_A[OF order_refl])

end

end

sublocale mvar: ll_on_open "existence_ivl0 x0" "\<lambda>t. blinfun_compose (vareq x0 t)" "UNIV::('a \<Rightarrow>\<^sub>L 'a) set" for x0
  by (rule total_derivative_ll_on_open)

lemma mvar_existence_ivl_eq_existence_ivl[simp]:\<comment> \<open>TODO: unify with @{thm varexivl_eq_exivl}\<close>
  assumes "t \<in> existence_ivl0 x0"
  shows "mvar.existence_ivl x0 t = (\<lambda>_. existence_ivl0 x0)"
proof (rule ext, rule mvar.existence_ivl_eq_domain)
  fix s t x
  assume s: "s \<in> existence_ivl0 x0" and t: "t \<in> existence_ivl0 x0"
  then have "{s .. t} \<subseteq> existence_ivl0 x0"
    by (meson atLeastAtMost_iff is_interval_1 is_interval_existence_ivl subsetI)
  then have "continuous_on {s .. t} (vareq x0)"
    by (auto intro!: continuous_intros)
  then have "compact (vareq x0 ` {s .. t})"
    using compact_Icc
    by (rule compact_continuous_image)
  then obtain B where B: "\<And>u. u \<in> {s .. t} \<Longrightarrow> norm (vareq x0 u) \<le> B"
    by (force dest!: compact_imp_bounded simp: bounded_iff)
  show "\<exists>M L. \<forall>t\<in>{s .. t}. \<forall>x\<in>UNIV. norm (vareq x0 t o\<^sub>L x) \<le> M + L * norm x"
    unfolding o_def
    by (rule exI[where x=0], rule exI[where x=B])
      (auto intro!: order_trans[OF norm_blinfun_compose] mult_right_mono B)
qed (auto intro: assms)

lemma
  assumes "t \<in> existence_ivl0 x0"
  shows "continuous_on (UNIV \<times> existence_ivl0 x0) (\<lambda>(x, ta). mvar.flow x0 t x ta)"
proof -
  from mvar.flow_continuous_on_state_space[of x0 t, unfolded mvar_existence_ivl_eq_existence_ivl[OF assms]]
  show "continuous_on (UNIV \<times> existence_ivl0 x0) (\<lambda>(x, ta). mvar.flow x0 t x ta)" .
qed

definition "Dflow x0 = mvar.flow x0 0 id_blinfun"

lemma var_eq_mvar:
  assumes "t0 \<in> existence_ivl0 x0"
  assumes "t \<in> existence_ivl0 x0"
  shows "var.flow x0 t0 i t = mvar.flow x0 t0 id_blinfun t i"
  by (rule var.flow_unique)
     (auto intro!: assms derivative_eq_intros mvar.flow_has_derivative
       simp: varexivl_eq_exivl assms has_vector_derivative_def blinfun.bilinear_simps)

lemma Dflow_zero[simp]: "x \<in> X \<Longrightarrow> Dflow x 0 = 1\<^sub>L"
  unfolding Dflow_def
  by (subst mvar.flow_initial_time) auto


subsection \<open>Differentiability of the flow0\<close>

text \<open> \<open>U t\<close>, i.e. the solution of the variational equation, is the space derivative at the initial
  value \<open>x0\<close>. \<close>
lemma flow_dx_derivative:
assumes "t \<in> existence_ivl0 x0"
shows "((\<lambda>x0. flow0 x0 t) has_derivative (\<lambda>z. vector_Dflow x0 z t)) (at x0)"
  unfolding has_derivative_at2
  using assms
  by (intro iffD1[OF LIM_equal proposition_17_6_weak[OF assms]] conjI[OF bounded_linear_vector_Dflow[OF assms]])
    (simp add: diff_diff_add inverse_eq_divide)

lemma flow_dx_derivative_blinfun:
assumes "t \<in> existence_ivl0 x0"
shows "((\<lambda>x. flow0 x t) has_derivative Blinfun (\<lambda>z. vector_Dflow x0 z t)) (at x0)"
by (rule has_derivative_Blinfun[OF flow_dx_derivative[OF assms]])

definition "flowderiv x0 t = comp12 (Dflow x0 t) (blinfun_scaleR_left (f (flow0 x0 t)))"

lemma flowderiv_eq: "flowderiv x0 t (\<xi>\<^sub>1, \<xi>\<^sub>2) = (Dflow x0 t) \<xi>\<^sub>1 + \<xi>\<^sub>2 *\<^sub>R f (flow0 x0 t)"
  by (auto simp: flowderiv_def)

lemma W_continuous_on: "continuous_on (Sigma X existence_ivl0) (\<lambda>(x0, t). Dflow x0 t)"
  \<comment> \<open>TODO: somewhere here is hidden continuity wrt rhs of ODE, extract it!\<close>
  unfolding continuous_on split_beta'
proof (safe intro!: tendstoI)
  fix e'::real and t x assume x: "x \<in> X" and tx: "t \<in> existence_ivl0 x" and e': "e' > 0"
  let ?S = "Sigma X existence_ivl0"

  have "(x, t) \<in> ?S" using x tx by auto
  from open_prod_elim[OF open_state_space this]
  obtain OX OT where OXOT: "open OX" "open OT" "(x, t) \<in> OX \<times> OT" "OX \<times> OT \<subseteq> ?S"
    by blast
  then obtain dx dt
  where dx: "dx > 0" "cball x dx \<subseteq> OX"
    and dt: "dt > 0" "cball t dt \<subseteq> OT"
    by (force simp: open_contains_cball)

  from OXOT dt dx have "cball t dt \<subseteq> existence_ivl0 x" "cball x dx \<subseteq> X"
    apply (auto simp: subset_iff)
    subgoal for ta
      apply (drule spec[where x=ta])
      apply (drule spec[where x=t])+
      apply auto
      done
    done

  have one_exivl: "mvar.existence_ivl x 0 = (\<lambda>_. existence_ivl0 x)"
    by (rule mvar_existence_ivl_eq_existence_ivl[OF existence_ivl_zero[OF \<open>x \<in> X\<close>]])

  have *: "closed ({t .. 0} \<union> {0 .. t})" "{t .. 0} \<union> {0 .. t} \<noteq> {}"
    by auto
  let ?T = "{t .. 0} \<union> {0 .. t} \<union> cball t dt"
  have "compact ?T"
    by (auto intro!: compact_Un)
  have "?T \<subseteq> existence_ivl0 x"
    by (intro Un_least ivl_subset_existence_ivl' ivl_subset_existence_ivl \<open>x \<in> X\<close>
      \<open>t \<in> existence_ivl0 x\<close> \<open>cball t dt \<subseteq> existence_ivl0 x\<close>)

  have "compact (mvar.flow x 0 id_blinfun ` ?T)"
    using \<open>?T \<subseteq> _\<close> \<open>x \<in> X\<close>
      mvar_existence_ivl_eq_existence_ivl[OF existence_ivl_zero[OF \<open>x \<in> X\<close>]]
    by (auto intro!: \<open>0 < dx\<close> compact_continuous_image \<open>compact ?T\<close>
      continuous_on_subset[OF mvar.flow_continuous_on])

  let ?line = "mvar.flow x 0 id_blinfun ` ?T"
  let ?X = "{x. infdist x ?line \<le> dx}"
  have "compact ?X"
    using \<open>?T \<subseteq> _\<close> \<open>x \<in> X\<close>
      mvar_existence_ivl_eq_existence_ivl[OF existence_ivl_zero[OF \<open>x \<in> X\<close>]]
    by (auto intro!: compact_infdist_le \<open>0 < dx\<close> compact_continuous_image compact_Un
      continuous_on_subset[OF mvar.flow_continuous_on ])

  from mvar.local_lipschitz \<open>?T \<subseteq> _\<close>
  have llc: "local_lipschitz ?T ?X (\<lambda>t. (o\<^sub>L) (vareq x t))"
    by (rule local_lipschitz_subset) auto

  have cont: "\<And>xa. xa \<in> ?X \<Longrightarrow> continuous_on ?T (\<lambda>t. vareq x t o\<^sub>L xa)"
    using \<open>?T \<subseteq> _\<close>
    by (auto intro!: continuous_intros \<open>x \<in> X\<close>)

  from local_lipschitz_compact_implies_lipschitz[OF llc \<open>compact ?X\<close> \<open>compact ?T\<close> cont]
  obtain K' where K': "\<And>ta. ta \<in> ?T \<Longrightarrow> K'-lipschitz_on ?X ((o\<^sub>L) (vareq x ta))"
    by blast
  define K where "K \<equiv> abs K' + 1"
  have "K > 0"
    by (simp add: K_def)
  have K: "\<And>ta. ta \<in> ?T \<Longrightarrow> K-lipschitz_on ?X ((o\<^sub>L) (vareq x ta))"
    by (auto intro!: lipschitz_onI mult_right_mono order_trans[OF lipschitz_onD[OF K']] simp: K_def)

  have ex_ivlI: "\<And>y. y \<in> cball x dx \<Longrightarrow> ?T \<subseteq> existence_ivl0 y"
    using dx dt OXOT
    by (intro Un_least ivl_subset_existence_ivl' ivl_subset_existence_ivl; force)

  have cont: "continuous_on ((?T \<times> ?X) \<times> cball x dx) (\<lambda>((ta, xa), y). (vareq y ta o\<^sub>L xa))"
    using \<open>cball x dx \<subseteq> X\<close> ex_ivlI
    by (force intro!: continuous_intros simp: split_beta' )

  have "mvar.flow x 0 id_blinfun t \<in> mvar.flow x 0 id_blinfun ` ({t..0} \<union> {0..t} \<union> cball t dt)"
    by auto
  then have mem: "(t, mvar.flow x 0 id_blinfun t, x) \<in> ?T \<times> ?X \<times> cball x dx"
    by (auto simp: \<open>0 < dx\<close> less_imp_le)

  define e where "e \<equiv> min e' (dx / 2) / 2"
  have "e > 0" using \<open>e' > 0\<close> by (auto simp: e_def \<open>0 < dx\<close>)
  define d where "d \<equiv> e * K / (exp (K * (abs t + abs dt + 1)) - 1)"
  have "d > 0" by (auto simp: d_def intro!: mult_pos_pos divide_pos_pos \<open>0 < e\<close> \<open>K > 0\<close>)

  have cmpct: "compact ((?T \<times> ?X) \<times> cball x dx)" "compact (?T \<times> ?X)"
    using \<open>compact ?T\<close> \<open>compact ?X\<close>
    by (auto intro!: compact_cball compact_Times)

  have compact_line: "compact ?line"
    using \<open>{t..0} \<union> {0..t} \<union> cball t dt \<subseteq> existence_ivl0 x\<close> one_exivl
    by (force intro!: compact_continuous_image \<open>compact ?T\<close> continuous_on_subset[OF mvar.flow_continuous_on] simp: \<open>x \<in> X\<close>)

  from compact_uniformly_continuous[OF cont cmpct(1), unfolded uniformly_continuous_on_def,
      rule_format, OF \<open>0 < d\<close>]
  obtain d' where d': "d' > 0"
    "\<And>ta xa xa' y. ta \<in> ?T \<Longrightarrow> xa \<in> ?X \<Longrightarrow> xa'\<in>cball x dx \<Longrightarrow> y\<in>cball x dx \<Longrightarrow> dist xa' y < d' \<Longrightarrow>
      dist (vareq xa' ta o\<^sub>L xa) (vareq y ta o\<^sub>L xa) < d"
    by (auto simp: dist_prod_def)
  {
    fix y
    assume dxy: "dist x y < d'"
    assume "y \<in> cball x dx"
    then have "y \<in> X"
      using dx dt OXOT by force+

    have two_exivl: "mvar.existence_ivl y 0 = (\<lambda>_. existence_ivl0 y)"
      by (rule mvar_existence_ivl_eq_existence_ivl[OF existence_ivl_zero[OF \<open>y \<in> X\<close>]])

    let ?X' = "\<Union>x \<in> ?line. ball x dx"
    have "open ?X'" by auto
    have "?X' \<subseteq> ?X"
      by (auto intro!: infdist_le2 simp: dist_commute)

    interpret oneR: ll_on_open "existence_ivl0 x" "(\<lambda>t. (o\<^sub>L) (vareq x t))" ?X'
      by standard (auto intro!: \<open>x \<in> X\<close> continuous_intros local_lipschitz_A[OF order_refl])
    interpret twoR: ll_on_open "existence_ivl0 y" "(\<lambda>t. (o\<^sub>L) (vareq y t))" ?X'
      by standard (auto intro!: \<open>y \<in> X\<close> continuous_intros local_lipschitz_A[OF order_refl])
    interpret both:
      two_ll_on_open "(\<lambda>t. (o\<^sub>L) (vareq x t))" "existence_ivl0 x" "(\<lambda>t. (o\<^sub>L) (vareq y t))" "existence_ivl0 y" ?X' ?T "id_blinfun" d K
    proof unfold_locales
      show "0 < K" by (simp add: \<open>0 < K\<close>)
      show iv_defined: "0 \<in> {t..0} \<union> {0..t} \<union> cball t dt"
        by auto
      show "is_interval ({t..0} \<union> {0..t} \<union> cball t dt)"
        by (auto simp: is_interval_def dist_real_def)
      show "{t..0} \<union> {0..t} \<union> cball t dt \<subseteq> oneR.existence_ivl 0 id_blinfun"
        apply (rule oneR.maximal_existence_flow[where x="mvar.flow x 0 id_blinfun"])
        subgoal
          apply (rule solves_odeI)
          apply (rule has_vderiv_on_subset[OF solves_odeD(1)[OF mvar.flow_solves_ode[of 0 x id_blinfun]]])
          subgoal using \<open>x \<in> X\<close> \<open>?T \<subseteq> _\<close> \<open>0 < dx\<close> by simp
          subgoal by simp
          subgoal by (simp add: \<open>cball t dt \<subseteq> existence_ivl0 x\<close> ivl_subset_existence_ivl ivl_subset_existence_ivl' one_exivl tx)
          subgoal using dx by (auto; force)
          done
        subgoal by (simp add: \<open>x \<in> X\<close>)
        subgoal by fact
        subgoal using iv_defined by blast
        subgoal using \<open>{t..0} \<union> {0..t} \<union> cball t dt \<subseteq> existence_ivl0 x\<close> by blast
        done
      fix s assume s: "s \<in> ?T"
      then show "K-lipschitz_on ?X' ((o\<^sub>L) (vareq x s))"
        by (intro lipschitz_on_subset[OF K \<open>?X' \<subseteq> ?X\<close>]) auto
      fix j assume j: "j \<in> ?X'"
      show "norm ((vareq x s o\<^sub>L j) - (vareq y s o\<^sub>L j)) < d"
        unfolding dist_norm[symmetric]
        apply (rule d')
        subgoal by (rule s)
        subgoal using \<open>?X' \<subseteq> ?X\<close> j ..
        subgoal using \<open>dx > 0\<close> by simp
        subgoal using \<open>y \<in> cball x dx\<close> by simp
        subgoal using dxy by simp
        done
    qed
    have less_e: "norm (Dflow x s - both.Y s) < e"
      if s: "s \<in> ?T \<inter> twoR.existence_ivl 0 id_blinfun" for s
    proof -
      from s have s_less: "\<bar>s\<bar> < \<bar>t\<bar> + \<bar>dt\<bar> + 1"
        by (auto simp: dist_real_def)
      note both.norm_X_Y_bound[rule_format, OF s]
      also have "d / K * (exp (K * \<bar>s\<bar>) - 1) =
          e * ((exp (K * \<bar>s\<bar>) - 1) / (exp (K * (\<bar>t\<bar> + \<bar>dt\<bar> + 1)) - 1))"
        by (simp add: d_def)
      also have "\<dots> < e * 1"
        by (rule mult_strict_left_mono[OF _ \<open>0 < e\<close>])
           (simp add: add_nonneg_pos \<open>0 < K\<close> \<open>0 < e\<close> s_less)
      also have "\<dots> = e" by simp
      also
      from s have s: "s \<in> ?T" by simp
      have "both.flow0 s = Dflow x s"
        unfolding both.flow0_def Dflow_def
        apply (rule oneR.maximal_existence_flow[where K="?T"])
        subgoal
          apply (rule solves_odeI)
          apply (rule has_vderiv_on_subset[OF solves_odeD(1)[OF mvar.flow_solves_ode[of 0 x id_blinfun]]])
          subgoal using \<open>x \<in> X\<close> \<open>0 < dx\<close> by simp
          subgoal by simp
          subgoal by (simp add: \<open>cball t dt \<subseteq> existence_ivl0 x\<close> ivl_subset_existence_ivl ivl_subset_existence_ivl' one_exivl tx)
          subgoal using dx by (auto; force)
          done
        subgoal by (simp add: \<open>x \<in> X\<close>)
        subgoal by (rule both.J_ivl)
        subgoal using both.t0_in_J by blast
        subgoal using \<open>{t..0} \<union> {0..t} \<union> cball t dt \<subseteq> existence_ivl0 x\<close> by blast
        subgoal using s by blast
        done
      finally show ?thesis .
    qed

    have "e < dx" using \<open>dx > 0\<close> by (auto simp: e_def)

    let ?i = "{y. infdist y (mvar.flow x 0 id_blinfun ` ?T) \<le> e}"
    have 1: "?i \<subseteq> (\<Union>x\<in>mvar.flow x 0 id_blinfun ` ?T. ball x dx)"
    proof -
      have cl: "closed ?line" "?line \<noteq> {}" using compact_line
        by (auto simp: compact_imp_closed)
      have "?i \<subseteq> (\<Union>y\<in>mvar.flow x 0 id_blinfun ` ?T. cball y e)"
      proof safe
        fix x
        assume H: "infdist x ?line \<le> e"
        from infdist_attains_inf[OF cl, of x]
        obtain y where "y \<in> ?line" "infdist x ?line = dist x y" by auto
        then show "x \<in> (\<Union>x\<in>?line. cball x e)"
          using H
          by (auto simp: dist_commute)
      qed
      also have "\<dots> \<subseteq> (\<Union>x\<in>?line. ball x dx)"
        using \<open>e < dx\<close>
        by auto
      finally show ?thesis .
    qed
    have 2: "twoR.flow 0 id_blinfun s \<in> ?i"
      if "s \<in> ?T" "s \<in> twoR.existence_ivl 0 id_blinfun" for s
    proof -
      from that have sT: "s \<in> ?T \<inter> twoR.existence_ivl 0 id_blinfun"
        by force
      from less_e[OF this]
      have "dist (twoR.flow 0 id_blinfun s) (mvar.flow x 0 id_blinfun s) \<le> e"
        unfolding Dflow_def both.Y_def dist_commute dist_norm by simp
      then show ?thesis
        using sT by (force intro: infdist_le2)
    qed
    have T_subset: "?T \<subseteq> twoR.existence_ivl 0 id_blinfun"
      apply (rule twoR.subset_mem_compact_implies_subset_existence_interval[
          where K="{x. infdist x ?line \<le> e}"])
      subgoal using \<open>0 < dt\<close> by force
      subgoal by (rule both.J_ivl)
      subgoal using \<open>y \<in> cball x dx\<close> ex_ivlI by blast
      subgoal using both.F_iv_defined(2) by blast
      subgoal by (rule 2)
      subgoal using \<open>dt > 0\<close> by (intro compact_infdist_le) (auto intro!: compact_line \<open>0 < e\<close>)
      subgoal by (rule 1)
      done
    also have "twoR.existence_ivl 0 id_blinfun \<subseteq> existence_ivl0 y"
      by (rule twoR.existence_ivl_subset)
    finally have "?T \<subseteq> existence_ivl0 y" .
    have "norm (Dflow x s - Dflow y s) < e" if s: "s \<in> ?T" for s
    proof -
      from s have "s \<in> ?T \<inter> twoR.existence_ivl 0 id_blinfun" using T_subset by force
      from less_e[OF this] have "norm (Dflow x s - both.Y s) < e" .
      also have "mvar.flow y 0 id_blinfun s = twoR.flow 0 id_blinfun s"
        apply (rule mvar.maximal_existence_flow[where K="?T"])
        subgoal
          apply (rule solves_odeI)
          apply (rule has_vderiv_on_subset[OF solves_odeD(1)[OF twoR.flow_solves_ode[of 0 id_blinfun]]])
          subgoal using \<open>y \<in> X\<close> by simp
          subgoal using both.F_iv_defined(2) by blast
          subgoal using T_subset by blast
          subgoal by simp
          done
        subgoal using \<open>y \<in> X\<close> auto_ll_on_open.existence_ivl_zero auto_ll_on_open_axioms both.F_iv_defined(2) twoR.flow_initial_time by blast
        subgoal by (rule both.J_ivl)
        subgoal using both.t0_in_J by blast
        subgoal using \<open>{t..0} \<union> {0..t} \<union> cball t dt \<subseteq> existence_ivl0 y\<close> by blast
        subgoal using s by blast
        done
      then have "both.Y s = Dflow y s"
        unfolding both.Y_def Dflow_def
        by simp
      finally show ?thesis .
    qed
  } note cont_data = this
  have "\<forall>\<^sub>F (y, s) in at (x, t) within ?S. dist x y < d'"
    unfolding at_within_open[OF \<open>(x, t) \<in> ?S\<close> open_state_space] UNIV_Times_UNIV[symmetric]
    using \<open>d' > 0\<close>
    by (intro eventually_at_Pair_within_TimesI1)
      (auto simp: eventually_at less_imp_le dist_commute)
  moreover
  have "\<forall>\<^sub>F (y, s) in at (x, t) within ?S. y \<in> cball x dx"
    unfolding at_within_open[OF \<open>(x, t) \<in> ?S\<close> open_state_space] UNIV_Times_UNIV[symmetric]
    using \<open>dx > 0\<close>
    by (intro eventually_at_Pair_within_TimesI1)
      (auto simp: eventually_at less_imp_le dist_commute)
  moreover
  have "\<forall>\<^sub>F (y, s) in at (x, t) within ?S. s \<in> ?T"
    unfolding at_within_open[OF \<open>(x, t) \<in> ?S\<close> open_state_space] UNIV_Times_UNIV[symmetric]
    using \<open>dt > 0\<close>
    by (intro eventually_at_Pair_within_TimesI2)
      (auto simp: eventually_at less_imp_le dist_commute)
  moreover
  have "0 \<in> existence_ivl0 x" by (simp add: \<open>x \<in> X\<close>)
  have "\<forall>\<^sub>F y in at t within existence_ivl0 x. dist (mvar.flow x 0 id_blinfun y) (mvar.flow x 0 id_blinfun t) < e"
    using mvar.flow_continuous_on[of x 0 id_blinfun]
    using \<open>0 < e\<close> tx
    by (auto simp add: continuous_on one_exivl dest!: tendstoD)
  then have "\<forall>\<^sub>F (y, s) in at (x, t) within ?S. dist (Dflow x s) (Dflow x t) < e"
    using \<open>0 < e\<close>
    unfolding at_within_open[OF \<open>(x, t) \<in> ?S\<close> open_state_space] UNIV_Times_UNIV[symmetric] Dflow_def
    by (intro eventually_at_Pair_within_TimesI2)
      (auto simp: at_within_open[OF tx open_existence_ivl])
  ultimately
  have "\<forall>\<^sub>F (y, s) in at (x, t) within ?S. dist (Dflow y s) (Dflow x t) < e'"
    apply eventually_elim
  proof (safe del: UnE, goal_cases)
    case (1 y s)
    have "dist (Dflow y s) (Dflow x t) \<le> dist (Dflow y s) (Dflow x s) + dist (Dflow x s) (Dflow x t)"
      by (rule dist_triangle)
    also
    have "dist (Dflow x s) (Dflow x t) < e"
      by (rule 1)
    also have "dist (Dflow y s) (Dflow x s) < e"
      unfolding dist_norm norm_minus_commute
      using 1
      by (intro cont_data)
    also have "e + e \<le> e'" by (simp add: e_def)
    finally show "dist (Dflow y s) (Dflow x t) < e'" by arith
  qed
  then show "\<forall>\<^sub>F ys in at (x, t) within ?S. dist (Dflow (fst ys) (snd ys)) (Dflow (fst (x, t)) (snd (x, t))) < e'"
    by (simp add: split_beta')
qed

lemma W_continuous_on_comp[continuous_intros]:
  assumes h: "continuous_on S h" and g: "continuous_on S g"
  shows "(\<And>s. s \<in> S \<Longrightarrow> h s \<in> X) \<Longrightarrow> (\<And>s. s \<in> S \<Longrightarrow> g s \<in> existence_ivl0 (h s)) \<Longrightarrow>
    continuous_on S (\<lambda>s. Dflow (h s) (g s))"
  using continuous_on_compose[OF continuous_on_Pair[OF h g] continuous_on_subset[OF W_continuous_on]]
  by auto

lemma f_flow_continuous_on: "continuous_on (Sigma X existence_ivl0) (\<lambda>(x0, t). f (flow0 x0 t))"
  using flow_continuous_on_state_space
  by (auto intro!: continuous_on_f flow_in_domain simp: split_beta')

lemma
  flow_has_space_derivative:
  assumes "t \<in> existence_ivl0 x0"
  shows "((\<lambda>x0. flow0 x0 t) has_derivative Dflow x0 t) (at x0)"
  by (rule flow_dx_derivative_blinfun[THEN has_derivative_eq_rhs])
    (simp_all add: var_eq_mvar assms blinfun.blinfun_apply_inverse Dflow_def vector_Dflow_def
      mem_existence_ivl_iv_defined[OF assms])

lemma
  flow_has_flowderiv:
  assumes "t \<in> existence_ivl0 x0"
  shows "((\<lambda>(x0, t). flow0 x0 t) has_derivative flowderiv x0 t) (at (x0, t) within S)"
proof -
  have Sigma: "(x0, t) \<in> Sigma X existence_ivl0"
    using assms by auto
  from open_state_space assms obtain e' where e': "e' > 0" "ball (x0, t) e' \<subseteq> Sigma X existence_ivl0"
    by (force simp: open_contains_ball)
  define e where "e = e' / sqrt 2"
  have "0 < e" using e' by (auto simp: e_def)
  have "ball x0 e \<times> ball t e \<subseteq> ball (x0, t) e'"
    by (auto simp: dist_prod_def real_sqrt_sum_squares_less e_def)
  also note e'(2)
  finally have subs: "ball x0 e \<times> ball t e \<subseteq> Sigma X existence_ivl0" .


  have d1: "((\<lambda>x0. flow0 x0 s) has_derivative blinfun_apply (Dflow y s)) (at y within ball x0 e)"
    if "y \<in> ball x0 e" "s \<in> ball t e" for y s
    using subs that
    by (subst at_within_open; force intro!: flow_has_space_derivative)
  have d2: "(flow0 y has_derivative blinfun_apply (blinfun_scaleR_left (f (flow0 y s)))) (at s within ball t e)"
    if "y \<in> ball x0 e" "s \<in> ball t e" for y s
    using subs that
    unfolding has_vector_derivative_eq_has_derivative_blinfun[symmetric]
    by (subst at_within_open; force intro!: flow_has_vector_derivative)
  have "((\<lambda>(x0, t). flow0 x0 t) has_derivative flowderiv x0 t) (at (x0, t) within ball x0 e \<times> ball t e)"
    using subs
    unfolding UNIV_Times_UNIV[symmetric]
    by (intro has_derivative_partialsI[OF d1 d2, THEN has_derivative_eq_rhs])
       (auto intro!: \<open>0 < e\<close> continuous_intros flow_in_domain
          continuous_on_imp_continuous_within[where s="Sigma X existence_ivl0"]
          assms
        simp: flowderiv_def split_beta' flow0_defined assms mem_ball)
  then have "((\<lambda>(x0, t). flow0 x0 t) has_derivative flowderiv x0 t) (at (x0, t) within Sigma X existence_ivl0)"
    by (auto simp: at_within_open[OF _ open_state_space] at_within_open[OF _ open_Times] assms \<open>0 < e\<close>
        mem_existence_ivl_iv_defined[OF assms])
  then show ?thesis unfolding at_within_open[OF Sigma open_state_space]
    by (rule has_derivative_at_withinI)
qed

lemma flow0_comp_has_derivative:
  assumes h: "h s \<in> existence_ivl0 (g s)"
  assumes [derivative_intros]: "(g has_derivative g') (at s within S)"
  assumes [derivative_intros]: "(h has_derivative h') (at s within S)"
  shows "((\<lambda>x. flow0 (g x) (h x)) has_derivative (\<lambda>x. blinfun_apply (flowderiv (g s) (h s)) (g' x, h' x)))
     (at s within S)"
  by (rule has_derivative_compose[where f="\<lambda>x. (g x, h x)" and s=S,
        OF _ flow_has_flowderiv[OF h], simplified])
    (auto intro!: derivative_eq_intros)

lemma flowderiv_continuous_on: "continuous_on (Sigma X existence_ivl0) (\<lambda>(x0, t). flowderiv x0 t)"
  unfolding flowderiv_def split_beta'
  by (subst blinfun_of_matrix_works[where f="comp12 (Dflow (fst x) (snd x))
            (blinfun_scaleR_left (f (flow0 (fst x) (snd x))))" for x, symmetric])
    (auto intro!: continuous_intros flow_in_domain)

lemma flowderiv_continuous_on_comp[continuous_intros]:
  assumes "continuous_on S x"
  assumes "continuous_on S t"
  assumes "\<And>s. s \<in> S \<Longrightarrow> x s \<in> X" "\<And>s. s \<in> S \<Longrightarrow> t s \<in> existence_ivl0 (x s)"
  shows "continuous_on S (\<lambda>xa. flowderiv (x xa) (t xa))"
  by (rule continuous_on_compose2[OF flowderiv_continuous_on, where f="\<lambda>s. (x s, t s)",
        unfolded split_beta' fst_conv snd_conv])
    (auto intro!: continuous_intros assms)

lemmas [intro] = flow_in_domain

lemma vareq_trans: "t0 \<in> existence_ivl0 x0 \<Longrightarrow> t \<in> existence_ivl0 (flow0 x0 t0) \<Longrightarrow>
  vareq (flow0 x0 t0) t = vareq x0 (t0 + t)"
  by (auto simp: vareq_def flow_trans)

lemma diff_existence_ivl_trans:
  "t0 \<in> existence_ivl0 x0 \<Longrightarrow> t \<in> existence_ivl0 x0 \<Longrightarrow> t - t0 \<in> existence_ivl0 (flow0 x0 t0)" for t
  by (metis (no_types, hide_lams) add.left_neutral diff_add_eq
      local.existence_ivl_reverse local.existence_ivl_trans local.flows_reverse)

lemma has_vderiv_on_blinfun_compose_right[derivative_intros]:
  assumes "(g has_vderiv_on g') T"
  assumes "\<And>x. x \<in> T \<Longrightarrow> gd' x = g' x o\<^sub>L d"
  shows "((\<lambda>x. g x o\<^sub>L d) has_vderiv_on gd') T"
  using assms
  by (auto simp: has_vderiv_on_def has_vector_derivative_def blinfun_ext blinfun.bilinear_simps
      intro!: derivative_eq_intros ext)

lemma has_vderiv_on_blinfun_compose_left[derivative_intros]:
  assumes "(g has_vderiv_on g') T"
  assumes "\<And>x. x \<in> T \<Longrightarrow> gd' x = d o\<^sub>L g' x"
  shows "((\<lambda>x. d o\<^sub>L g x) has_vderiv_on gd') T"
  using assms
  by (auto simp: has_vderiv_on_def has_vector_derivative_def blinfun_ext blinfun.bilinear_simps
      intro!: derivative_eq_intros ext)

lemma mvar_flow_shift:
  assumes "t0 \<in> existence_ivl0 x0" "t1 \<in> existence_ivl0 x0"
  shows "mvar.flow x0 t0 d t1 = Dflow (flow0 x0 t0) (t1 - t0) o\<^sub>L d"
proof -
  have "mvar.flow x0 t0 d t1 = mvar.flow x0 t0 d (t0 + (t1 - t0))"
    by simp
  also have "\<dots> = mvar.flow x0 t0 (mvar.flow x0 t0 d t0) t1"
    by (subst mvar.flow_trans) (auto simp add: assms)
  also have "\<dots> = Dflow (flow0 x0 t0) (t1 - t0) o\<^sub>L d"
    apply (rule mvar.flow_unique_on)
       apply (auto simp add: assms mvar.flow_initial_time_if blinfun_ext Dflow_def
        intro!: derivative_intros derivative_eq_intros)
      apply (auto simp: assms has_vderiv_on_open has_vector_derivative_def
        intro!: derivative_eq_intros blinfun_eqI)
     apply (subst mvar_existence_ivl_eq_existence_ivl)
    by (auto simp add: vareq_trans assms diff_existence_ivl_trans)
  finally show ?thesis .
qed

lemma Dflow_trans:
  assumes "h \<in> existence_ivl0 x0"
  assumes "i \<in> existence_ivl0 (flow0 x0 h)"
  shows "Dflow x0 (h + i) = Dflow (flow0 x0 h) i o\<^sub>L (Dflow x0 h)"
proof -
  have [intro, simp]: "h + i \<in> existence_ivl0 x0" "i + h \<in> existence_ivl0 x0" "x0 \<in> X"
    using assms
    by (auto simp add: add.commute existence_ivl_trans)
  show ?thesis
    unfolding Dflow_def
    apply (subst mvar.flow_trans[where s=h and t=i])
    subgoal by (auto simp: assms)
    subgoal by (auto simp: assms)
    by (subst mvar_flow_shift) (auto simp: assms Dflow_def )
qed

lemma Dflow_trans_apply:
  assumes "h \<in> existence_ivl0 x0"
  assumes "i \<in> existence_ivl0 (flow0 x0 h)"
  shows "Dflow x0 (h + i) d0 = Dflow (flow0 x0 h) i (Dflow x0 h d0)"
proof -
  have [intro, simp]: "h + i \<in> existence_ivl0 x0" "i + h \<in> existence_ivl0 x0" "x0 \<in> X"
    using assms
    by (auto simp add: add.commute existence_ivl_trans)
  show ?thesis
    unfolding Dflow_def
    apply (subst mvar.flow_trans[where s=h and t=i])
    subgoal by (auto simp: assms)
    subgoal by (auto simp: assms)
    by (subst mvar_flow_shift) (auto simp: assms Dflow_def )
qed


end \<comment> \<open>@{thm c1_on_open_euclidean_anchor}\<close>

end
