section \<open>Upper and Lower Solutions\<close>
theory Upper_Lower_Solution
imports Flow
begin

text \<open>Following  Walter~\cite{walter} in section 9\<close>

lemma IVT_min:
  fixes f :: "real \<Rightarrow> 'b :: {linorder_topology,real_normed_vector,ordered_real_vector}"
  \<comment> \<open>generalize?\<close>
  assumes y: "f a \<le> y" "y \<le> f b" "a \<le> b"
  assumes *: "continuous_on {a .. b} f"
  notes [continuous_intros] = *[THEN continuous_on_subset]
  obtains x where "a \<le> x" "x \<le> b" "f x = y" "\<And>x'. a \<le> x' \<Longrightarrow> x' < x \<Longrightarrow> f x' < y"
proof -
  let ?s = "((\<lambda>x. f x - y) -` {0..}) \<inter> {a..b}"
  have "?s \<noteq> {}"
    using assms
    by auto
  have "closed ?s"
    by (rule closed_vimage_Int) (auto intro!: continuous_intros)
  moreover have "bounded ?s"
    by (rule bounded_Int) (simp add: bounded_closed_interval)
  ultimately have "compact ?s"
    using compact_eq_bounded_closed by blast
  from compact_attains_inf[OF this \<open>?s \<noteq> {}\<close>]
  obtain x where x: "a \<le> x" "x \<le> b" "f x \<ge> y"
    and min: "\<And>z. a \<le> z \<Longrightarrow> z \<le> b \<Longrightarrow> f z \<ge> y \<Longrightarrow> x \<le> z"
    by auto
  have "f x \<le> y"
  proof (rule ccontr)
    assume n: "\<not> f x \<le> y"
    then have "\<exists>z\<ge>a. z \<le> x \<and> (\<lambda>x. f x - y) z = 0"
      using x by (intro IVT') (auto intro!: continuous_intros simp: assms)
    then obtain z where z: "a \<le> z" "z \<le> x" "f z = y" by auto
    then have "a \<le> z" "z \<le> b" "f z \<ge> y" using x by auto
    from min [OF this] z n
    show False by auto
  qed
  then have "a \<le> x" "x \<le> b" "f x = y"
    using x
    by (auto )
  moreover have "f x' < y" if "a \<le> x'" "x' < x" for x'
    apply (rule ccontr)
    using min[of x'] that x
    by (auto simp: not_less)
  ultimately show ?thesis ..
qed

lemma filtermap_at_left_shift: "filtermap (\<lambda>x. x - d) (at_left a) = at_left (a - d::real)"
  by (simp add: filter_eq_iff eventually_filtermap eventually_at_filter filtermap_nhds_shift[symmetric])

context
  fixes v v' w w'::"real \<Rightarrow> real" and t0 t1 e::real
  assumes v': "(v has_vderiv_on v') {t0 <.. t1}"
    and w': "(w has_vderiv_on w') {t0 <.. t1}"
  assumes pos_ivl: "t0 < t1"
  assumes e_pos: "e > 0" and e_in: "t0 + e \<le> t1"
  assumes less:  "\<And>t. t0 < t \<Longrightarrow> t < t0 + e \<Longrightarrow> v t < w t"
begin

lemma first_intersection_crossing_derivatives:
  assumes na: "t0 < tg" "tg \<le> t1" "v tg \<ge> w tg"
  notes [continuous_intros] =
    vderiv_on_continuous_on[OF v', THEN continuous_on_subset]
    vderiv_on_continuous_on[OF w', THEN continuous_on_subset]
  obtains x0 where
    "t0 < x0" "x0 \<le> tg"
    "v' x0 \<ge> w' x0"
    "v x0 = w x0"
    "\<And>t. t0 < t \<Longrightarrow> t < x0 \<Longrightarrow> v t < w t"
proof -
  have "(v - w) (min tg (t0 + e / 2)) \<le> 0" "0 \<le> (v - w) tg"
    "min tg (t0 + e / 2) \<le> tg"
    "continuous_on {min tg (t0 + e / 2)..tg} (v - w)"
  using less[of "t0 + e / 2"]
    less[of tg]na \<open>e > 0\<close>
    by (auto simp: min_def intro!: continuous_intros)
  from IVT_min[OF this]
  obtain x0 where x0: "min tg (t0 + e / 2) \<le> x0" "x0 \<le> tg" "v x0 = w x0"
    "\<And>x'. min tg (t0 + e / 2) \<le> x' \<Longrightarrow> x' < x0 \<Longrightarrow> v x' < w x'"
    by auto
  then have x0_in: "t0 < x0" "x0 \<le> t1"
    using \<open>e > 0\<close> na(1,2)
    by (auto)
  note \<open>t0 < x0\<close> \<open>x0 \<le> tg\<close>
  moreover
  {
    from v' x0_in
    have "(v has_derivative (\<lambda>x. x * v' x0)) (at x0 within {t0<..<x0})"
      by (force intro: has_derivative_within_subset simp: has_vector_derivative_def has_vderiv_on_def)
    then have v: "((\<lambda>y. (v y - (v x0 + (y - x0) * v' x0)) / norm (y - x0)) \<longlongrightarrow> 0) (at x0 within {t0<..<x0})"
      unfolding has_derivative_within
      by (simp add: ac_simps)
    from w' x0_in
    have "(w has_derivative (\<lambda>x. x * w' x0)) (at x0 within {t0<..<x0})"
      by (force intro: has_derivative_within_subset simp: has_vector_derivative_def has_vderiv_on_def)
    then have w: "((\<lambda>y. (w y - (w x0 + (y - x0) * w' x0)) / norm (y - x0)) \<longlongrightarrow> 0) (at x0 within {t0<..<x0})"
      unfolding has_derivative_within
      by (simp add: ac_simps)

    have evs: "\<forall>\<^sub>F x in at x0 within {t0<..<x0}. min tg (t0 + e / 2) < x"
      "\<forall>\<^sub>F x in at x0 within {t0<..<x0}. t0 < x \<and> x < x0"
      using less na(1) na(3) x0(3) x0_in(1)
      by (force simp: min_def eventually_at_filter intro!: order_tendstoD[OF tendsto_ident_at])+
    then have "\<forall>\<^sub>F x in at x0 within {t0<..<x0}.
       (v x - (v x0 + (x - x0) * v' x0)) / norm (x - x0) - (w x - (w x0 + (x - x0) * w' x0)) / norm (x - x0) =
       (v x - w x) / norm (x - x0) + (v' x0 - w' x0)"
       apply eventually_elim
       using x0_in x0 less na \<open>t0 < t1\<close> sum_sqs_eq
       by (auto simp: divide_simps algebra_simps min_def intro!: eventuallyI split: if_split_asm)
    from this tendsto_diff[OF v w]
    have 1: "((\<lambda>x. (v x - w x) / norm (x - x0) + (v' x0 - w' x0)) \<longlongrightarrow> 0) (at x0 within {t0<..<x0})"
      by (rule Lim_transform_eventually[THEN tendsto_eq_rhs]) auto
    moreover
    from evs have 2: "\<forall>\<^sub>F x in at x0 within {t0<..<x0}. (v x - w x) / norm (x - x0) + (v' x0 - w' x0) \<le> (v' x0 - w' x0)"
      by eventually_elim (auto simp: divide_simps intro!: less_imp_le x0(4))

    moreover
    have "at x0 within {t0<..<x0} \<noteq> bot"
      by (simp add: \<open>t0 < x0\<close> at_within_eq_bot_iff less_imp_le)

    ultimately
    have "0 \<le> v' x0 - w' x0"
      by (rule tendsto_upperbound)
    then have "v' x0 \<ge> w' x0" by simp
  }
  moreover note \<open>v x0 = w x0\<close>
  moreover
  have "t0 < t \<Longrightarrow> t < x0 \<Longrightarrow> v t < w t" for t
    by (cases "min tg (t0 + e / 2) \<le> t") (auto intro: x0 less)
  ultimately show ?thesis ..
qed

lemma defect_less:
  assumes b: "\<And>t. t0 < t \<Longrightarrow> t \<le> t1 \<Longrightarrow> v' t - f t (v t) < w' t - f t (w t)"
  notes [continuous_intros] =
    vderiv_on_continuous_on[OF v', THEN continuous_on_subset]
    vderiv_on_continuous_on[OF w', THEN continuous_on_subset]
  shows "\<forall>t \<in> {t0 <.. t1}. v t < w t"
proof (rule ccontr)
  assume " \<not> (\<forall>t\<in>{t0 <.. t1}. v t < w t)"
  then obtain tu where "t0 < tu" "tu \<le> t1" "v tu \<ge> w tu" by auto
  from first_intersection_crossing_derivatives[OF this]
  obtain x0 where "t0 < x0" "x0 \<le> tu" "w' x0 \<le> v' x0" "v x0 = w x0" "\<And>t. t0 < t \<Longrightarrow> t < x0 \<Longrightarrow> v t < w t"
    by metis
  with b[of x0] \<open>tu \<le> t1\<close>
  show False
    by simp
qed

end

lemma has_derivatives_less_lemma:
  fixes v v' ::"real \<Rightarrow> real"
  assumes v': "(v has_vderiv_on v') T"
  assumes y': "(y has_vderiv_on y') T"
  assumes lu: "\<And>t. t \<in> T \<Longrightarrow> t > t0 \<Longrightarrow> v' t - f t (v t) < y' t - f t (y t)"
  assumes lower: "v t0 \<le> y t0"
  assumes eq_imp: "v t0 = y t0 \<Longrightarrow> v' t0 < y' t0"
  assumes t: "t0 < t" "t0 \<in> T" "t \<in> T" "is_interval T"
  shows "v t < y t"
proof -
  have subset: "{t0 .. t} \<subseteq> T"
    by (rule atMostAtLeast_subset_convex) (auto simp: assms is_interval_convex)
  obtain d where "0 < d" "t0 < s \<Longrightarrow> s \<le> t \<Longrightarrow> s < t0 + d \<Longrightarrow> v s < y s" for s
  proof cases
    assume "v t0 = y t0"
    from this[THEN eq_imp]
    have *: "0 < y' t0 - v' t0"
      by (simp add: )
    have "((\<lambda>t. y t - v t) has_vderiv_on (\<lambda>t0. y' t0 - v' t0)) {t0 .. t}"
      by (auto intro!: derivative_intros y' v' has_vderiv_on_subset[OF _ subset])
    with \<open>t0 < t\<close>
    have d: "((\<lambda>t. y t - v t) has_real_derivative y' t0 - v' t0) (at t0 within {t0 .. t})"
      by (auto simp: has_vderiv_on_def has_field_derivative_iff_has_vector_derivative)
    from has_real_derivative_pos_inc_right[OF d *] \<open>v t0 = y t0\<close>
    obtain d where "d > 0" and vy: "h > 0 \<Longrightarrow> t0 + h \<le> t \<Longrightarrow> h < d \<Longrightarrow> v (t0 + h) < y (t0 + h)" for h
      by auto
    have vy: "t0 < s \<Longrightarrow> s \<le> t \<Longrightarrow> s < t0 + d \<Longrightarrow> v s < y s" for s
      using vy[of "s - t0"] by simp
    with \<open>d > 0\<close> show ?thesis ..
  next
    assume "v t0 \<noteq> y t0"
    then have "v t0 < y t0" using lower by simp
    moreover
    have "continuous_on {t0 .. t} v" "continuous_on {t0 .. t} y"
      by (auto intro!: vderiv_on_continuous_on assms has_vderiv_on_subset[OF _ subset])
    then have "(v \<longlongrightarrow> v t0) (at t0 within {t0 .. t})" "(y \<longlongrightarrow> y t0) (at t0 within {t0 .. t})"
      by (auto simp: continuous_on)
    ultimately have "\<forall>\<^sub>F x in at t0 within {t0 .. t}. 0 < y x - v x"
      by (intro order_tendstoD) (auto intro!: tendsto_eq_intros)
    then obtain d where "d > 0" "\<And>x. t0 < x \<Longrightarrow> x \<le> t \<Longrightarrow> x < t0 + d \<Longrightarrow> v x < y x"
      by atomize_elim (auto simp: eventually_at algebra_simps dist_real_def)
    then show ?thesis ..
  qed
  with \<open>d > 0\<close> \<open>t0 < t\<close>
  obtain e where "e > 0" "t0 + e \<le> t" "t0 < s \<Longrightarrow> s < t0 + e \<Longrightarrow> v s < y s" for s
    by atomize_elim (auto simp: min_def divide_simps intro!: exI[where x="min (d/2) ((t - t0) / 2)"]
        split: if_split_asm)
  from defect_less[
      OF has_vderiv_on_subset[OF v']
        has_vderiv_on_subset[OF y']
        \<open>t0 < t\<close>
        this lu]
  show "v t < y t" using \<open>t0 < t\<close> subset
    by (auto simp: subset_iff assms)
qed

lemma strict_lower_solution:
  fixes v v' ::"real \<Rightarrow> real"
  assumes sol: "(y solves_ode f) T X"
  assumes v': "(v has_vderiv_on v') T"
  assumes lower: "\<And>t. t \<in> T \<Longrightarrow> t > t0 \<Longrightarrow> v' t < f t (v t)"
  assumes iv: "v t0 \<le> y t0" "v t0 = y t0 \<Longrightarrow> v' t0 < f t0 (y t0)"
  assumes t: "t0 < t" "t0 \<in> T" "t \<in> T" "is_interval T"
  shows "v t < y t"
proof -
  note v'
  moreover
  note solves_odeD(1)[OF sol]
  moreover
  have 3: "v' t - f t (v t) < f t (y t) - f t (y t)" if "t \<in> T" "t > t0" for t
    using lower(1)[OF that]
    by arith
  moreover note iv
  moreover note t
  ultimately
  show "v t < y t"
    by (rule has_derivatives_less_lemma)
qed

lemma strict_upper_solution:
  fixes w w'::"real \<Rightarrow> real"
  assumes sol: "(y solves_ode f) T X"
  assumes w': "(w has_vderiv_on w') T"
    and upper: "\<And>t. t \<in> T \<Longrightarrow> t > t0 \<Longrightarrow> f t (w t) < w' t"
    and iv: "y t0 \<le> w t0" "y t0 = w t0 \<Longrightarrow> f t0 (y t0) < w' t0"
  assumes t: "t0 < t" "t0 \<in> T" "t \<in> T" "is_interval T"
  shows "y t < w t"
proof -
  note solves_odeD(1)[OF sol]
  moreover
  note w'
  moreover
  have "f t (y t) - f t (y t) < w' t - f t (w t)" if "t \<in> T" "t > t0" for t
    using upper(1)[OF that]
    by arith
  moreover note iv
  moreover note t
  ultimately
  show "y t < w t"
    by (rule has_derivatives_less_lemma)
qed

lemma uniform_limit_at_within_subset:
  assumes "uniform_limit S x l (at t within T)"
  assumes "U \<subseteq> T"
  shows "uniform_limit S x l (at t within U)"
  by (metis assms(1) assms(2) eventually_within_Un filterlim_iff subset_Un_eq)

lemma uniform_limit_le:
  fixes f::"'c \<Rightarrow> 'a \<Rightarrow> 'b::{metric_space, linorder_topology}"
  assumes I: "I \<noteq> bot"
  assumes u: "uniform_limit X f g I"
  assumes u': "uniform_limit X f' g' I"
  assumes "\<forall>\<^sub>F i in I. \<forall>x \<in> X. f i x \<le> f' i x"
  assumes "x \<in> X"
  shows "g x \<le> g' x"
proof -
  have "\<forall>\<^sub>F i in I. f i x \<le> f' i x" using assms by (simp add: eventually_mono)
  with I tendsto_uniform_limitI[OF u' \<open>x \<in> X\<close>] tendsto_uniform_limitI[OF u \<open>x \<in> X\<close>]
  show ?thesis by (rule tendsto_le)
qed

lemma uniform_limit_le_const:
  fixes f::"'c \<Rightarrow> 'a \<Rightarrow> 'b::{metric_space, linorder_topology}"
  assumes I: "I \<noteq> bot"
  assumes u: "uniform_limit X f g I"
  assumes "\<forall>\<^sub>F i in I. \<forall>x \<in> X. f i x \<le> h x"
  assumes "x \<in> X"
  shows "g x \<le> h x"
proof -
  have "\<forall>\<^sub>F i in I. f i x \<le> h x" using assms by (simp add: eventually_mono)
  then show ?thesis by (metis tendsto_upperbound I tendsto_uniform_limitI[OF u \<open>x \<in> X\<close>])
qed

lemma uniform_limit_ge_const:
  fixes f::"'c \<Rightarrow> 'a \<Rightarrow> 'b::{metric_space, linorder_topology}"
  assumes I: "I \<noteq> bot"
  assumes u: "uniform_limit X f g I"
  assumes "\<forall>\<^sub>F i in I. \<forall>x \<in> X. h x \<le> f i x"
  assumes "x \<in> X"
  shows "h x \<le> g x"
proof -
  have "\<forall>\<^sub>F i in I. h x \<le> f i x" using assms by (simp add: eventually_mono)
  then show ?thesis by (metis tendsto_lowerbound I tendsto_uniform_limitI[OF u \<open>x \<in> X\<close>])
qed

locale ll_on_open_real = ll_on_open T f X for T f and X::"real set"
begin

lemma lower_solution:
  fixes v v' ::"real \<Rightarrow> real"
  assumes sol: "(y solves_ode f) S X"
  assumes v': "(v has_vderiv_on v') S"
  assumes lower: "\<And>t. t \<in> S \<Longrightarrow> t > t0 \<Longrightarrow> v' t < f t (v t)"
  assumes iv: "v t0 \<le> y t0"
  assumes t: "t0 \<le> t" "t0 \<in> S" "t \<in> S" "is_interval S" "S \<subseteq> T"
  shows "v t \<le> y t"
proof cases
  assume "v t0 = y t0"
  have "{t0 -- t} \<subseteq> S" using t by (simp add: closed_segment_subset is_interval_convex)
  with sol have "(y solves_ode f) {t0 -- t} X" using order_refl by (rule solves_ode_on_subset)
  moreover note refl
  moreover
  have "{t0 -- t} \<subseteq> T" using \<open>{t0 -- t} \<subseteq> S\<close> \<open>S \<subseteq> T\<close> by (rule order_trans)
  ultimately have t_ex: "t \<in> existence_ivl t0 (y t0)"
    by (rule existence_ivl_maximal_segment)

  have t0_ex: "t0 \<in> existence_ivl t0 (y t0)"
    using in_existence_between_zeroI t_ex by blast
  have "t0 \<in> T" using assms(9) t(2) by blast

  from uniform_limit_flow[OF t0_ex t_ex] \<open>t0 \<le> t\<close>
  have "uniform_limit {t0..t} (flow t0) (flow t0 (y t0)) (at (y t0))" by simp
  then have "uniform_limit {t0..t} (flow t0) (flow t0 (y t0)) (at_right (y t0))"
    by (rule uniform_limit_at_within_subset) simp
  moreover
  {
    have "\<forall>\<^sub>F i in at (y t0). t \<in> existence_ivl t0 i"
      by (rule eventually_mem_existence_ivl) fact
    then have "\<forall>\<^sub>F i in at_right (y t0). t \<in> existence_ivl t0 i"
      unfolding eventually_at_filter
      by eventually_elim simp
    moreover have "\<forall>\<^sub>F i in at_right (y t0). i \<in> X"
    proof -
      have f1: "\<And>r ra rb. r \<notin> existence_ivl ra rb \<or> rb \<in> X"
        by (metis existence_ivl_reverse flow_in_domain flows_reverse)
      obtain rr :: "(real \<Rightarrow> bool) \<Rightarrow> (real \<Rightarrow> bool) \<Rightarrow> real" where
        "\<And>p f pa fa. (\<not> eventually p f \<or> eventually pa f \<or> p (rr p pa)) \<and>
          (\<not> eventually p fa \<or> \<not> pa (rr p pa) \<or> eventually pa fa)"
        by (metis (no_types) eventually_mono)
      then show ?thesis
        using f1 calculation by blast
    qed
    moreover have "\<forall>\<^sub>F i in at_right (y t0). y t0 < i"
      by (simp add: eventually_at_filter)
    ultimately have "\<forall>\<^sub>F i in at_right (y t0). \<forall>x\<in>{t0..t}. v x \<le> flow t0 i x"
    proof eventually_elim
      case (elim y')
      show ?case
      proof safe
        fix s assume s: "s \<in> {t0..t}"
        show "v s \<le> flow t0 y' s"
        proof cases
          assume "s = t0" with elim iv show ?thesis
            by (simp add: \<open>t0 \<in> T\<close> \<open>y' \<in> X\<close>)
        next
          assume "s \<noteq> t0" with s have "t0 < s" by simp
          have "{t0 -- s} \<subseteq> S" using \<open>{t0--t} \<subseteq> S\<close> closed_segment_eq_real_ivl s by auto
          from s elim have "{t0..s} \<subseteq> existence_ivl t0 y'"
            using ivl_subset_existence_ivl by blast
          with flow_solves_ode have sol: "(flow t0 y' solves_ode f) {t0 .. s} X"
            by (rule solves_ode_on_subset) (auto intro!: \<open>y' \<in> X\<close> \<open>t0 \<in> T\<close>)
          have "{t0 .. s} \<subseteq> S" using \<open>{t0 -- s} \<subseteq> S\<close> by (simp add: closed_segment_eq_real_ivl split: if_splits)
          with v' have v': "(v has_vderiv_on v') {t0 .. s}"
            by (rule has_vderiv_on_subset)
          from \<open>y t0 < y'\<close> \<open>v t0 = y t0\<close> have less_init: "v t0 < flow t0 y' t0"
            by (simp add: flow_initial_time_if \<open>t0 \<in> T\<close> \<open>y' \<in> X\<close>)
          from strict_lower_solution[OF sol v' lower less_imp_le[OF less_init] _ \<open>t0 < s\<close>]
            \<open>{t0 .. s} \<subseteq> S\<close>
            less_init \<open>t0 < s\<close>
          have "v s < flow t0 y' s" by (simp add: subset_iff is_interval_cc)
          then show ?thesis by simp
        qed
      qed
    qed
  }
  moreover have "t \<in> {t0 .. t}" using \<open>t0 \<le> t\<close> by simp
  ultimately have "v t \<le> flow t0 (y t0) t"
    by (rule uniform_limit_ge_const[OF trivial_limit_at_right_real])
  also have "flow t0 (y t0) t = y t"
    using sol t
    by (intro maximal_existence_flow) auto
  finally show ?thesis .
next
  assume "v t0 \<noteq> y t0" then have less: "v t0 < y t0" using iv by simp
  show ?thesis
    apply (cases "t0 = t")
    subgoal using iv by blast
    subgoal using strict_lower_solution[OF sol v' lower iv] less t by force
    done
qed

lemma upper_solution:
  fixes v v' ::"real \<Rightarrow> real"
  assumes sol: "(y solves_ode f) S X"
  assumes v': "(v has_vderiv_on v') S"
  assumes upper: "\<And>t. t \<in> S \<Longrightarrow> t > t0 \<Longrightarrow> f t (v t) < v' t"
  assumes iv: "y t0 \<le> v t0"
  assumes t: "t0 \<le> t" "t0 \<in> S" "t \<in> S" "is_interval S" "S \<subseteq> T"
  shows "y t \<le> v t"
proof cases
  assume "v t0 = y t0"
  have "{t0 -- t} \<subseteq> S" using t by (simp add: closed_segment_subset is_interval_convex)
  with sol have "(y solves_ode f) {t0 -- t} X" using order_refl by (rule solves_ode_on_subset)
  moreover note refl
  moreover
  have "{t0 -- t} \<subseteq> T" using \<open>{t0 -- t} \<subseteq> S\<close> \<open>S \<subseteq> T\<close> by (rule order_trans)
  ultimately have t_ex: "t \<in> existence_ivl t0 (y t0)"
    by (rule existence_ivl_maximal_segment)

  have t0_ex: "t0 \<in> existence_ivl t0 (y t0)"
    using in_existence_between_zeroI t_ex by blast
  have "t0 \<in> T" using assms(9) t(2) by blast

  from uniform_limit_flow[OF t0_ex t_ex] \<open>t0 \<le> t\<close>
  have "uniform_limit {t0..t} (flow t0) (flow t0 (y t0)) (at (y t0))" by simp
  then have "uniform_limit {t0..t} (flow t0) (flow t0 (y t0)) (at_left (y t0))"
    by (rule uniform_limit_at_within_subset) simp
  moreover
  {
    have "\<forall>\<^sub>F i in at (y t0). t \<in> existence_ivl t0 i"
      by (rule eventually_mem_existence_ivl) fact
    then have "\<forall>\<^sub>F i in at_left (y t0). t \<in> existence_ivl t0 i"
      unfolding eventually_at_filter
      by eventually_elim simp
    moreover have "\<forall>\<^sub>F i in at_left (y t0). i \<in> X"
    proof -
      have f1: "\<And>r ra rb. r \<notin> existence_ivl ra rb \<or> rb \<in> X"
        by (metis existence_ivl_reverse flow_in_domain flows_reverse)
      obtain rr :: "(real \<Rightarrow> bool) \<Rightarrow> (real \<Rightarrow> bool) \<Rightarrow> real" where
        "\<And>p f pa fa. (\<not> eventually p f \<or> eventually pa f \<or> p (rr p pa)) \<and>
          (\<not> eventually p fa \<or> \<not> pa (rr p pa) \<or> eventually pa fa)"
        by (metis (no_types) eventually_mono)
      then show ?thesis
        using f1 calculation by blast
    qed
    moreover have "\<forall>\<^sub>F i in at_left (y t0). i < y t0"
      by (simp add: eventually_at_filter)
    ultimately have "\<forall>\<^sub>F i in at_left (y t0). \<forall>x\<in>{t0..t}. flow t0 i x \<le> v x"
    proof eventually_elim
      case (elim y')
      show ?case
      proof safe
        fix s assume s: "s \<in> {t0..t}"
        show "flow t0 y' s \<le> v s"
        proof cases
          assume "s = t0" with elim iv show ?thesis
            by (simp add: \<open>t0 \<in> T\<close> \<open>y' \<in> X\<close>)
        next
          assume "s \<noteq> t0" with s have "t0 < s" by simp
          have "{t0 -- s} \<subseteq> S" using \<open>{t0--t} \<subseteq> S\<close> closed_segment_eq_real_ivl s by auto
          from s elim have "{t0..s} \<subseteq> existence_ivl t0 y'"
            using ivl_subset_existence_ivl by blast
          with flow_solves_ode have sol: "(flow t0 y' solves_ode f) {t0 .. s} X"
            by (rule solves_ode_on_subset) (auto intro!: \<open>y' \<in> X\<close> \<open>t0 \<in> T\<close>)
          have "{t0 .. s} \<subseteq> S" using \<open>{t0 -- s} \<subseteq> S\<close> by (simp add: closed_segment_eq_real_ivl split: if_splits)
          with v' have v': "(v has_vderiv_on v') {t0 .. s}"
            by (rule has_vderiv_on_subset)
          from \<open>y' < y t0\<close> \<open>v t0 = y t0\<close> have less_init: "flow t0 y' t0 < v t0"
            by (simp add: flow_initial_time_if \<open>t0 \<in> T\<close> \<open>y' \<in> X\<close>)
          from strict_upper_solution[OF sol v' upper less_imp_le[OF less_init] _ \<open>t0 < s\<close>]
            \<open>{t0 .. s} \<subseteq> S\<close>
            less_init \<open>t0 < s\<close>
          have "flow t0 y' s < v s" by (simp add: subset_iff is_interval_cc)
          then show ?thesis by simp
        qed
      qed
    qed
  }
  moreover have "t \<in> {t0 .. t}" using \<open>t0 \<le> t\<close> by simp
  ultimately have "flow t0 (y t0) t \<le> v t"
    by (rule uniform_limit_le_const[OF trivial_limit_at_left_real])
  also have "flow t0 (y t0) t = y t"
    using sol t
    by (intro maximal_existence_flow) auto
  finally show ?thesis .
next
  assume "v t0 \<noteq> y t0" then have less: "y t0 < v t0" using iv by simp
  show ?thesis
    apply (cases "t0 = t")
    subgoal using iv by blast
    subgoal using strict_upper_solution[OF sol v' upper iv] less t by force
    done
qed

end

end
