theory Picard_Lindeloef_Qualitative
imports Initial_Value_Problem
begin

subsection \<open>Picard-Lindeloef On Open Domains\<close>
text\<open>\label{sec:qpl}\<close>

subsubsection \<open>Local Solution with local Lipschitz\<close>
text\<open>\label{sec:qpl-lipschitz}\<close>

lemma cball_eq_closed_segment_real:
  fixes x e::real
  shows "cball x e = (if e \<ge> 0 then {x - e -- x + e} else {})"
  by (auto simp: closed_segment_eq_real_ivl dist_real_def mem_cball)

lemma cube_in_cball:
  fixes x y :: "'a::euclidean_space"
  assumes "r > 0"
  assumes "\<And>i. i\<in> Basis \<Longrightarrow> dist (x \<bullet> i) (y \<bullet> i) \<le> r / sqrt(DIM('a))"
  shows "y \<in> cball x r"
  unfolding mem_cball euclidean_dist_l2[of x y] L2_set_def
proof -
  have "(\<Sum>i\<in>Basis. (dist (x \<bullet> i) (y \<bullet> i))\<^sup>2) \<le> (\<Sum>(i::'a)\<in>Basis. (r / sqrt(DIM('a)))\<^sup>2)"
  proof (intro sum_mono)
    fix i :: 'a
    assume "i \<in> Basis"
    thus "(dist (x \<bullet> i) (y \<bullet> i))\<^sup>2 \<le> (r / sqrt(DIM('a)))\<^sup>2"
      using assms
      by (auto intro: sqrt_le_D)
  qed
  moreover
  have "... \<le> r\<^sup>2"
    using assms by (simp add: power_divide)
  ultimately
  show "sqrt (\<Sum>i\<in>Basis. (dist (x \<bullet> i) (y \<bullet> i))\<^sup>2) \<le> r"
    using assms by (auto intro!: real_le_lsqrt sum_nonneg)
qed

lemma cbox_in_cball':
  fixes x::"'a::euclidean_space"
  assumes "0 < r"
  shows "\<exists>b > 0. b \<le> r \<and> (\<exists>B. B = (\<Sum>i\<in>Basis. b *\<^sub>R i) \<and> (\<forall>y \<in> cbox (x - B) (x + B). y \<in> cball x r))"
proof (rule, safe)
  have "r / sqrt (real DIM('a)) \<le> r / 1"
    using assms  by (auto simp: divide_simps real_of_nat_ge_one_iff)
  thus "r / sqrt (real DIM('a)) \<le> r" by simp
next
  let ?B = "\<Sum>i\<in>Basis. (r / sqrt (real DIM('a))) *\<^sub>R i"
  show "\<exists>B. B = ?B \<and> (\<forall>y \<in> cbox (x - B) (x + B). y \<in> cball x r)"
  proof (rule, safe)
    fix y::'a
    assume "y \<in> cbox (x - ?B) (x + ?B)"
    hence bounds:
      "\<And>i. i \<in> Basis \<Longrightarrow> (x - ?B) \<bullet> i \<le> y \<bullet> i"
      "\<And>i. i \<in> Basis \<Longrightarrow> y \<bullet> i \<le> (x + ?B) \<bullet> i"
      by (auto simp: mem_box)
    show "y \<in> cball x r"
    proof (intro cube_in_cball)
      fix i :: 'a
      assume "i\<in> Basis"
      with bounds
      have bounds_comp:
        "x \<bullet> i - r / sqrt (real DIM('a)) \<le> y \<bullet> i"
        "y \<bullet> i \<le> x \<bullet> i + r / sqrt (real DIM('a))"
        by (auto simp: algebra_simps)
      thus "dist (x \<bullet> i) (y \<bullet> i) \<le> r / sqrt (real DIM('a))"
        unfolding dist_real_def by simp
    qed (auto simp add: assms)
  qed (rule)
qed (auto simp: assms)

lemma Pair1_in_Basis: "i \<in> Basis \<Longrightarrow> (i, 0) \<in> Basis"
 and Pair2_in_Basis: "i \<in> Basis \<Longrightarrow> (0, i) \<in> Basis"
  by (auto simp: Basis_prod_def)

lemma le_real_sqrt_sumsq' [simp]: "y \<le> sqrt (x * x + y * y)"
  by (simp add: power2_eq_square [symmetric])

lemma cball_Pair_split_subset: "cball (a, b) c \<subseteq> cball a c \<times> cball b c"
  by (auto simp: dist_prod_def mem_cball power2_eq_square
      intro: order_trans[OF le_real_sqrt_sumsq] order_trans[OF le_real_sqrt_sumsq'])

lemma cball_times_subset: "cball a (c/2) \<times> cball b (c/2) \<subseteq> cball (a, b) c"
proof -
  {
    fix a' b'
    have "sqrt ((dist a a')\<^sup>2 + (dist b b')\<^sup>2) \<le> dist a a' + dist b b'"
      by (rule real_le_lsqrt) (auto simp: power2_eq_square algebra_simps)
    also assume "a' \<in> cball a (c / 2)"
    then have "dist a a' \<le> c / 2" by (simp add: mem_cball)
    also assume "b' \<in> cball b (c / 2)"
    then have "dist b b' \<le> c / 2" by (simp add: mem_cball)
    finally have "sqrt ((dist a a')\<^sup>2 + (dist b b')\<^sup>2) \<le> c"
      by simp
  } thus ?thesis by (auto simp: dist_prod_def mem_cball)
qed

lemma eventually_bound_pairE:
  assumes "isCont f (t0, x0)"
  obtains B where
    "B \<ge> 1"
    "eventually (\<lambda>e. \<forall>x \<in> cball t0 e \<times> cball x0 e. norm (f x) \<le> B) (at_right 0)"
proof -
  from assms[simplified isCont_def, THEN tendstoD, OF zero_less_one]
  obtain d::real where d: "d > 0"
    "\<And>x. x \<noteq> (t0, x0) \<Longrightarrow> dist x (t0, x0) < d \<Longrightarrow> dist (f x) (f (t0, x0)) < 1"
    by (auto simp: eventually_at)
  have bound: "norm (f (t, x)) \<le> norm (f (t0, x0)) + 1"
    if "t \<in> cball t0 (d/3)" "x \<in> cball x0 (d/3)" for t x
  proof -
    from that have "norm (f (t, x) - f (t0, x0)) < 1"
      using \<open>0 < d\<close>
      unfolding dist_norm[symmetric]
      apply (cases "(t, x) = (t0, x0)", force)
      by (rule d) (auto simp: dist_commute dist_prod_def mem_cball
        intro!: le_less_trans[OF sqrt_sum_squares_le_sum_abs])
    then show ?thesis
      by norm
  qed
  have "norm (f (t0, x0)) + 1 \<ge> 1"
    "eventually (\<lambda>e. \<forall>x \<in> cball t0 e \<times> cball x0 e.
      norm (f x) \<le> norm (f (t0, x0)) + 1) (at_right 0)"
    using d(1) bound
    by (auto simp: eventually_at dist_real_def mem_cball intro!: exI[where x="d/3"])
  thus ?thesis ..
qed

lemma
  eventually_in_cballs:
  assumes "d > 0" "c > 0"
  shows "eventually (\<lambda>e. cball t0 (c * e) \<times> (cball x0 e) \<subseteq> cball (t0, x0) d) (at_right 0)"
  using assms
  by (auto simp: eventually_at dist_real_def field_simps dist_prod_def mem_cball
    intro!: exI[where x="min d (d / c) / 3"]
    order_trans[OF sqrt_sum_squares_le_sum_abs])

lemma cball_eq_sing':
  fixes x :: "'a::{metric_space,perfect_space}"
  shows "cball x e = {y} \<longleftrightarrow> e = 0 \<and> x = y"
  using cball_eq_sing[of x e]
  apply (cases "x = y", force)
  by (metis cball_empty centre_in_cball insert_not_empty not_le singletonD)

locale ll_on_open = interval T for T +
  fixes f::"real \<Rightarrow> 'a::{banach, heine_borel} \<Rightarrow> 'a" and X
  assumes local_lipschitz: "local_lipschitz T X f"
  assumes cont: "\<And>x. x \<in> X \<Longrightarrow> continuous_on T (\<lambda>t. f t x)"
  assumes open_domain[intro!, simp]: "open T" "open X"
begin

text \<open>all flows on closed segments\<close>

definition csols where
  "csols t0 x0 = {(x, t1). {t0--t1} \<subseteq> T \<and> x t0 = x0 \<and> (x solves_ode f) {t0--t1} X}"

text \<open>the maximal existence interval\<close>

definition "existence_ivl t0 x0 = (\<Union>(x, t1)\<in>csols t0 x0 . {t0--t1})"

text \<open>witness flow\<close>

definition "csol t0 x0 = (SOME csol. \<forall>t \<in> existence_ivl t0 x0. (csol t, t) \<in> csols t0 x0)"

text \<open>unique flow\<close>

definition flow where "flow t0 x0 = (\<lambda>t. if t \<in> existence_ivl t0 x0 then csol t0 x0 t t else 0)"

end

locale ll_on_open_it =
  general?:\<comment> \<open>TODO: why is this qualification necessary? It seems only because of @{thm ll_on_open_it_axioms}\<close>
  ll_on_open + fixes t0::real
  \<comment> \<open>if possible, all development should be done with \<open>t0\<close> as explicit parameter for initial time:
    then it can be instantiated with \<open>0\<close> for autonomous ODEs\<close>

context ll_on_open begin

sublocale ll_on_open_it where t0 = t0  for t0 ..

sublocale continuous_rhs T X f
  by unfold_locales (rule continuous_on_TimesI[OF local_lipschitz cont])

end

context ll_on_open_it begin

lemma ll_on_open_rev[intro, simp]: "ll_on_open (preflect t0 ` T) (\<lambda>t. - f (preflect t0 t)) X"
  using local_lipschitz interval
  by unfold_locales
    (auto intro!: continuous_intros cont intro: local_lipschitz_compose1
      simp: fun_Compl_def local_lipschitz_minus local_lipschitz_subset open_neg_translation
        image_image preflect_def)

lemma eventually_lipschitz:
  assumes "t0 \<in> T" "x0 \<in> X" "c > 0"
  obtains L where
    "eventually (\<lambda>u. \<forall>t' \<in> cball t0 (c * u) \<inter> T.
      L-lipschitz_on (cball x0 u \<inter> X) (\<lambda>y. f t' y)) (at_right 0)"
proof -
  from local_lipschitzE[OF local_lipschitz, OF \<open>t0 \<in> T\<close> \<open>x0 \<in> X\<close>]
  obtain u L where
    "u > 0"
    "\<And>t'. t' \<in> cball t0 u \<inter> T \<Longrightarrow> L-lipschitz_on (cball x0 u \<inter> X) (\<lambda>y. f t' y)"
    by auto
  hence "eventually (\<lambda>u. \<forall>t' \<in> cball t0 (c * u) \<inter> T.
      L-lipschitz_on (cball x0 u \<inter> X) (\<lambda>y. f t' y)) (at_right 0)"
    using \<open>u > 0\<close> \<open>c > 0\<close>
    by (auto simp: dist_real_def eventually_at divide_simps algebra_simps
      intro!: exI[where x="min u (u / c)"]
      intro: lipschitz_on_subset[where E="cball x0 u \<inter> X"])
  thus ?thesis ..
qed

lemmas continuous_on_Times_f = continuous
lemmas continuous_on_f = continuous_rhs_comp

lemma
  lipschitz_on_compact:
  assumes "compact K" "K \<subseteq> T"
  assumes "compact Y" "Y \<subseteq> X"
  obtains L where "\<And>t. t \<in> K \<Longrightarrow> L-lipschitz_on Y (f t)"
proof -
  have cont: "\<And>x. x \<in> Y \<Longrightarrow> continuous_on K (\<lambda>t. f t x)"
    using \<open>Y \<subseteq> X\<close> \<open>K \<subseteq> T\<close>
    by (auto intro!: continuous_on_f continuous_intros)
  from local_lipschitz
  have "local_lipschitz K Y f"
    by (rule local_lipschitz_subset[OF _ \<open>K \<subseteq> T\<close> \<open>Y \<subseteq> X\<close>])
  from local_lipschitz_compact_implies_lipschitz[OF this \<open>compact Y\<close> \<open>compact K\<close> cont] that
  show ?thesis by metis
qed

lemma csols_empty_iff: "csols t0 x0 = {} \<longleftrightarrow> t0 \<notin> T \<or> x0 \<notin> X"
proof cases
  assume iv_defined: "t0 \<in> T \<and> x0 \<in> X"
  then have "(\<lambda>_. x0, t0) \<in> csols t0 x0"
    by (auto simp: csols_def intro!: solves_ode_singleton)
  then show ?thesis using \<open>t0 \<in> T \<and> x0 \<in> X\<close> by auto
qed (auto simp: solves_ode_domainD csols_def)

lemma csols_notempty: "t0 \<in> T \<Longrightarrow> x0 \<in> X \<Longrightarrow> csols t0 x0 \<noteq> {}"
  by (simp add: csols_empty_iff)


lemma existence_ivl_empty_iff[simp]: "existence_ivl t0 x0 = {} \<longleftrightarrow> t0 \<notin> T \<or> x0 \<notin> X"
  using csols_empty_iff
  by (auto simp: existence_ivl_def)

lemma existence_ivl_empty1[simp]: "t0 \<notin> T \<Longrightarrow> existence_ivl t0 x0 = {}"
  and existence_ivl_empty2[simp]: "x0 \<notin> X \<Longrightarrow> existence_ivl t0 x0 = {}"
  using csols_empty_iff
  by (auto simp: existence_ivl_def)

lemma flow_undefined:
  shows "t0 \<notin> T \<Longrightarrow> flow t0 x0 = (\<lambda>_. 0)"
    "x0 \<notin> X \<Longrightarrow> flow t0 x0 = (\<lambda>_. 0)"
  using existence_ivl_empty_iff
  by (auto simp: flow_def)

lemma (in ll_on_open) flow_eq_in_existence_ivlI:
  assumes "\<And>u. x0 \<in> X \<Longrightarrow> u \<in> existence_ivl t0 x0 \<longleftrightarrow> g u \<in> existence_ivl s0 x0"
  assumes "\<And>u. x0 \<in> X \<Longrightarrow> u \<in> existence_ivl t0 x0 \<Longrightarrow> flow t0 x0 u = flow s0 x0 (g u)"
  shows "flow t0 x0 = (\<lambda>t. flow s0 x0 (g t))"
  apply (cases "x0 \<in> X")
  subgoal using assms by (auto intro!: ext simp: flow_def)
  subgoal by (simp add: flow_undefined)
  done


subsubsection \<open>Global maximal flow with local Lipschitz\<close>
text\<open>\label{sec:qpl-global-flow}\<close>

lemma local_unique_solution:
  assumes iv_defined: "t0 \<in> T" "x0 \<in> X"
  obtains et ex B L
  where "et > 0" "0 < ex" "cball t0 et \<subseteq> T" "cball x0 ex \<subseteq> X"
    "unique_on_cylinder t0 (cball t0 et) x0 ex f B L"
proof -
  have "\<forall>\<^sub>F e::real in at_right 0. 0 < e"
    by (auto simp: eventually_at_filter)
  moreover

  from open_Times[OF open_domain] have "open (T \<times> X)" .
  from at_within_open[OF _ this] iv_defined
  have "isCont (\<lambda>(t, x). f t x) (t0, x0)"
    using continuous by (auto simp: continuous_on_eq_continuous_within)
  from eventually_bound_pairE[OF this]
  obtain B where B:
    "1 \<le> B" "\<forall>\<^sub>F e in at_right 0. \<forall>t\<in>cball t0 e. \<forall>x\<in>cball x0 e. norm (f t x) \<le> B"
    by (force simp: )
  note B(2)
  moreover

  define t where "t \<equiv> inverse B"
  have te: "\<And>e. e > 0 \<Longrightarrow> t * e > 0"
    using \<open>1 \<le> B\<close> by (auto simp: t_def field_simps)
  have t_pos: "t > 0"
    using \<open>1 \<le> B\<close> by (auto simp: t_def)

  from B(2) obtain dB where "0 < dB" "0 < dB / 2"
    and dB: "\<And>d t x. 0 < d \<Longrightarrow> d < dB \<Longrightarrow> t\<in>cball t0 d \<Longrightarrow> x\<in>cball x0 d \<Longrightarrow>
      norm (f t x) \<le> B"
    by (auto simp: eventually_at dist_real_def Ball_def)

  hence dB': "\<And>t x. (t, x) \<in> cball (t0, x0) (dB / 2) \<Longrightarrow> norm (f t x) \<le> B"
    using cball_Pair_split_subset[of t0 x0 "dB / 2"]
    by (auto simp: eventually_at dist_real_def
      simp del: mem_cball
      intro!: dB[where d="dB/2"])
  from eventually_in_cballs[OF \<open>0 < dB/2\<close> t_pos, of t0 x0]
  have "\<forall>\<^sub>F e in at_right 0. \<forall>t\<in>cball t0 (t * e). \<forall>x\<in>cball x0 e. norm (f t x) \<le> B"
    unfolding eventually_at_filter
    by eventually_elim (auto intro!: dB')
  moreover

  from eventually_lipschitz[OF iv_defined t_pos] obtain L where
    "\<forall>\<^sub>F u in at_right 0. \<forall>t'\<in>cball t0 (t * u) \<inter> T. L-lipschitz_on (cball x0 u \<inter> X) (f t')"
    by auto
  moreover
  have "\<forall>\<^sub>F e in at_right 0. cball t0 (t * e) \<subseteq> T"
    using eventually_open_cball[OF open_domain(1) iv_defined(1)]
    by (subst eventually_filtermap[symmetric, where f="\<lambda>x. t * x"])
      (simp add: filtermap_times_pos_at_right t_pos)
  moreover
  have "eventually (\<lambda>e. cball x0 e \<subseteq> X) (at_right 0)"
    using open_domain(2) iv_defined(2)
    by (rule eventually_open_cball)
  ultimately have "\<forall>\<^sub>F e in at_right 0. 0 < e \<and> cball t0 (t * e) \<subseteq> T \<and> cball x0 e \<subseteq> X \<and>
    unique_on_cylinder t0 (cball t0 (t * e)) x0 e f B L"
  proof eventually_elim
    case (elim e)
    note \<open>0 < e\<close>
    moreover
    note T = \<open>cball t0 (t * e) \<subseteq> T\<close>
    moreover
    note X = \<open>cball x0 e \<subseteq> X\<close>
    moreover
    from elim Int_absorb2[OF \<open>cball x0 e \<subseteq> X\<close>]
    have L: "t' \<in> cball t0 (t * e) \<inter> T \<Longrightarrow> L-lipschitz_on (cball x0 e) (f t')" for t'
      by auto
    from elim have B: "\<And>t' x. t' \<in> cball t0 (t * e) \<Longrightarrow> x \<in> cball x0 e \<Longrightarrow> norm (f t' x) \<le> B"
      by auto


    have "t * e \<le> e / B"
      by (auto simp: t_def cball_def dist_real_def inverse_eq_divide)

    have "{t0 -- t0 + t * e} \<subseteq> cball t0 (t * e)"
      using \<open>t > 0\<close> \<open>e > 0\<close>
      by (auto simp: cball_eq_closed_segment_real closed_segment_eq_real_ivl)
    then have "unique_on_cylinder t0 (cball t0 (t * e)) x0 e f B L"
      using T X \<open>t > 0\<close> \<open>e > 0\<close> \<open>t * e \<le> e / B\<close>
      by unfold_locales
        (auto intro!: continuous_rhs_comp continuous_on_fst continuous_on_snd B L
          continuous_on_id
          simp: split_beta' dist_commute mem_cball)
    ultimately show ?case by auto
  qed
  from eventually_happens[OF this]
  obtain e where "0 < e" "cball t0 (t * e) \<subseteq> T" "cball x0 e \<subseteq> X"
    "unique_on_cylinder t0 (cball t0 (t * e)) x0 e f B L"
    by (metis trivial_limit_at_right_real)
  with mult_pos_pos[OF \<open>0 < t\<close> \<open>0 < e\<close>] show ?thesis ..
qed

lemma mem_existence_ivl_iv_defined:
  assumes "t \<in> existence_ivl t0 x0"
  shows "t0 \<in> T" "x0 \<in> X"
  using assms existence_ivl_empty_iff
  unfolding atomize_conj
  by blast

lemma csol_mem_csols:
  assumes "t \<in> existence_ivl t0 x0"
  shows "(csol t0 x0 t, t) \<in> csols t0 x0"
proof -
  have "\<exists>csol. \<forall>t \<in> existence_ivl t0 x0. (csol t, t) \<in> csols t0 x0"
  proof (safe intro!: bchoice)
    fix t assume "t \<in> existence_ivl t0 x0"
    then obtain csol t1 where csol: "(csol t, t1) \<in> csols t0 x0" "t \<in> {t0 -- t1}"
      by (auto simp: existence_ivl_def)
    then have "{t0--t} \<subseteq> {t0 -- t1}"
      by (auto simp: closed_segment_eq_real_ivl)
    then have "(csol t, t) \<in> csols t0 x0" using csol
      by (auto simp: csols_def intro: solves_ode_on_subset)
    then show "\<exists>y. (y, t) \<in> csols t0 x0" by force
  qed
  then have "\<forall>t \<in> existence_ivl t0 x0. (csol t0 x0 t, t) \<in> csols t0 x0"
    unfolding csol_def
    by (rule someI_ex)
  with assms show "?thesis" by auto
qed

lemma csol:
  assumes "t \<in> existence_ivl t0 x0"
  shows "t \<in> T" "{t0--t} \<subseteq> T" "csol t0 x0 t t0 = x0" "(csol t0 x0 t solves_ode f) {t0--t} X"
  using csol_mem_csols[OF assms]
  by (auto simp: csols_def)

lemma existence_ivl_initial_time_iff[simp]: "t0 \<in> existence_ivl t0 x0 \<longleftrightarrow> t0 \<in> T \<and> x0 \<in> X"
  using csols_empty_iff
  by (auto simp: existence_ivl_def)

lemma existence_ivl_initial_time: "t0 \<in> T \<Longrightarrow> x0 \<in> X \<Longrightarrow> t0 \<in> existence_ivl t0 x0"
  by simp

lemmas mem_existence_ivl_subset = csol(1)

lemma existence_ivl_subset:
  "existence_ivl t0 x0 \<subseteq> T"
  using mem_existence_ivl_subset by blast

lemma is_interval_existence_ivl[intro, simp]: "is_interval (existence_ivl t0 x0)"
  unfolding is_interval_connected_1
  by (auto simp: existence_ivl_def intro!: connected_Union)

lemma connected_existence_ivl[intro, simp]: "connected (existence_ivl t0 x0)"
  using is_interval_connected by blast

lemma in_existence_between_zeroI:
  "t \<in> existence_ivl t0 x0 \<Longrightarrow> s \<in> {t0 -- t} \<Longrightarrow> s \<in> existence_ivl t0 x0"
  by (meson existence_ivl_initial_time interval.closed_segment_subset_domainI interval.intro
    is_interval_existence_ivl mem_existence_ivl_iv_defined(1) mem_existence_ivl_iv_defined(2))

lemma segment_subset_existence_ivl:
  assumes "s \<in> existence_ivl t0 x0" "t \<in> existence_ivl t0 x0"
  shows "{s -- t} \<subseteq> existence_ivl t0 x0"
  using assms is_interval_existence_ivl
  unfolding is_interval_convex_1
  by (rule closed_segment_subset)

lemma flow_initial_time_if: "flow t0 x0 t0 = (if t0 \<in> T \<and> x0 \<in> X then x0 else 0)"
  by (simp add: flow_def csol(3))

lemma flow_initial_time[simp]: "t0 \<in> T \<Longrightarrow> x0 \<in> X \<Longrightarrow> flow t0 x0 t0 = x0"
  by (auto simp: flow_initial_time_if)

lemma open_existence_ivl[intro, simp]: "open (existence_ivl t0 x0)"
proof (rule openI)
  fix t assume t: "t \<in> existence_ivl t0 x0"
  note csol = csol[OF this]
  note mem_existence_ivl_iv_defined[OF t]

  have "flow t0 x0 t \<in> X" using \<open>t \<in> existence_ivl t0 x0\<close>
    using csol(4) solves_ode_domainD
    by (force simp add: flow_def)

  from ll_on_open_it.local_unique_solution[OF ll_on_open_it_axioms \<open>t \<in> T\<close> this]
  obtain et ex B L where lsol:
    "0 < et"
    "0 < ex"
    "cball t et \<subseteq> T"
    "cball (flow t0 x0 t) ex \<subseteq> X"
    "unique_on_cylinder t (cball t et) (flow t0 x0 t) ex f B L"
    by metis
  then interpret unique_on_cylinder t "cball t et" "flow t0 x0 t" ex "cball (flow t0 x0 t) ex" f B L
    by auto
  from solution_usolves_ode have lsol_ode: "(solution solves_ode f) (cball t et) (cball (flow t0 x0 t) ex)"
    by (intro usolves_odeD)
  show "\<exists>e>0. ball t e \<subseteq> existence_ivl t0 x0"
  proof cases
    assume "t = t0"
    show ?thesis
    proof (safe intro!: exI[where x="et"] mult_pos_pos \<open>0 < et\<close> \<open>0 < ex\<close>)
      fix t' assume "t' \<in> ball t et"
      then have subset: "{t0--t'} \<subseteq> ball t et"
        by (intro closed_segment_subset) (auto simp: \<open>0 < et\<close> \<open>0 < ex\<close> \<open>t = t0\<close>)
      also have "\<dots> \<subseteq> cball t et" by simp
      also note \<open>cball t _ \<subseteq> T\<close>
      finally have "{t0--t'} \<subseteq> T" by simp
      moreover have "(solution solves_ode f) {t0--t'} X"
        using lsol_ode
        apply (rule solves_ode_on_subset)
        using subset lsol
        by (auto simp: mem_ball mem_cball)
      ultimately have "(solution, t') \<in> csols t0 x0"
        unfolding csols_def
        using lsol \<open>t' \<in> ball _ _\<close> lsol \<open>t = t0\<close> solution_iv \<open>x0 \<in> X\<close>
        by (auto simp: csols_def)
      then show "t' \<in> existence_ivl t0 x0"
        unfolding existence_ivl_def
        by force
    qed
  next
    assume "t \<noteq> t0"
    let ?m = "min et (dist t0 t / 2)"
    show ?thesis
    proof (safe intro!: exI[where x = ?m])
      let ?t1' = "if t0 \<le> t then t + et else t - et"
      have lsol_ode: "(solution solves_ode f) {t -- ?t1'} (cball (flow t0 x0 t) ex)"
        by (rule solves_ode_on_subset[OF lsol_ode])
          (insert \<open>0 < et\<close> \<open>0 < ex\<close>, auto simp: mem_cball closed_segment_eq_real_ivl dist_real_def)
      let ?if = "\<lambda>ta. if ta \<in> {t0--t} then csol t0 x0 t ta else solution ta"
      let ?iff = "\<lambda>ta. if ta \<in> {t0--t} then f ta else f ta"
      have "(?if solves_ode ?iff) ({t0--t} \<union> {t -- ?t1'}) X"
        apply (rule connection_solves_ode[OF csol(4) lsol_ode, unfolded Un_absorb2[OF \<open>_ \<subseteq> X\<close>]])
        using lsol solution_iv \<open>t \<in> existence_ivl t0 x0\<close>
        by (auto intro!: simp: closed_segment_eq_real_ivl flow_def split: if_split_asm)
      also have "?iff = f" by auto
      also have Un_eq: "{t0--t} \<union> {t -- ?t1'} = {t0 -- ?t1'}"
        using \<open>0 < et\<close> \<open>0 < ex\<close>
        by (auto simp: closed_segment_eq_real_ivl)
      finally have continuation: "(?if solves_ode f) {t0--?t1'} X" .
      have subset_T: "{t0 -- ?t1'} \<subseteq> T"
        unfolding Un_eq[symmetric]
        apply (intro Un_least)
        subgoal using csol by force
        subgoal using _ lsol(3)
          apply (rule order_trans)
          using \<open>0 < et\<close> \<open>0 < ex\<close>
          by (auto simp: closed_segment_eq_real_ivl subset_iff mem_cball dist_real_def)
        done
      fix t' assume "t' \<in> ball t ?m"
      then have scs: "{t0 -- t'} \<subseteq> {t0--?t1'}"
        using \<open>0 < et\<close> \<open>0 < ex\<close>
        by (auto simp: closed_segment_eq_real_ivl dist_real_def abs_real_def mem_ball split: if_split_asm)
      with continuation have "(?if solves_ode f) {t0 -- t'} X"
        by (rule solves_ode_on_subset) simp
      then have "(?if, t') \<in> csols t0 x0"
        using lsol \<open>t' \<in> ball _ _\<close> csol scs subset_T
        by (auto simp: csols_def subset_iff)
      then show "t' \<in> existence_ivl t0 x0"
        unfolding existence_ivl_def
        by force
    qed (insert \<open>t \<noteq> t0\<close> \<open>0 < et\<close> \<open>0 < ex\<close>, simp)
  qed
qed

lemma csols_unique:
  assumes "(x, t1) \<in> csols t0 x0"
  assumes "(y, t2) \<in> csols t0 x0"
  shows "\<forall>t \<in> {t0 -- t1} \<inter> {t0 -- t2}. x t = y t"
proof (rule ccontr)
  let ?S = "{t0 -- t1} \<inter> {t0 -- t2}"
  let ?Z0 = "(\<lambda>t. x t - y t) -` {0} \<inter> ?S"
  let ?Z = "connected_component_set ?Z0 t0"
  from assms have t1: "t1 \<in> existence_ivl t0 x0" and t2: "t2 \<in> existence_ivl t0 x0"
    and x: "(x solves_ode f) {t0 -- t1} X"
    and y: "(y solves_ode f) {t0 -- t2} X"
    and sub1: "{t0--t1} \<subseteq> T"
    and sub2: "{t0--t2} \<subseteq> T"
    and x0: "x t0 = x0"
    and y0: "y t0 = x0"
    by (auto simp: existence_ivl_def csols_def)

  assume "\<not> (\<forall>t\<in>?S. x t = y t)"
  hence "\<exists>t\<in>?S. x t \<noteq> y t" by simp
  then obtain t_ne where t_ne: "t_ne \<in> ?S" "x t_ne \<noteq> y t_ne" ..
  from assms have x: "(x solves_ode f) {t0--t1} X"
    and y:"(y solves_ode f) {t0--t2} X"
    by (auto simp: csols_def)
  have "compact ?S"
    by auto
  have "closed ?Z"
    by (intro closed_connected_component closed_vimage_Int)
      (auto intro!: continuous_intros continuous_on_subset[OF solves_ode_continuous_on[OF x]]
        continuous_on_subset[OF solves_ode_continuous_on[OF y]])
  moreover
  have "t0 \<in> ?Z" using assms
    by (auto simp: csols_def)
  then have "?Z \<noteq> {}"
    by (auto intro!: exI[where x=t0])
  ultimately
  obtain t_max where max: "t_max \<in> ?Z" "y \<in> ?Z \<Longrightarrow> dist t_ne t_max \<le> dist t_ne y" for y
    by (blast intro: distance_attains_inf)
  have max_equal_flows: "x t = y t" if "t \<in> {t0 -- t_max}" for t
    using max(1) that
    by (auto simp: connected_component_def vimage_def subset_iff closed_segment_eq_real_ivl
      split: if_split_asm) (metis connected_iff_interval)+
  then have t_ne_outside: "t_ne \<notin> {t0 -- t_max}" using t_ne by auto

  have "x t_max = y t_max"
    by (rule max_equal_flows) simp
  have "t_max \<in> ?S" "t_max \<in> T"
    using max sub1 sub2
    by (auto simp: connected_component_def)
  with solves_odeD[OF x]
  have "x t_max \<in> X"
    by auto

  from ll_on_open_it.local_unique_solution[OF ll_on_open_it_axioms \<open>t_max \<in> T\<close> \<open>x t_max \<in> X\<close>]
  obtain et ex B L
    where "0 < et" "0 < ex"
      and "cball t_max et \<subseteq> T" "cball (x t_max) ex \<subseteq> X"
      and "unique_on_cylinder t_max (cball t_max et) (x t_max) ex f B L"
    by metis
  then interpret unique_on_cylinder t_max "cball t_max et" "x t_max" ex "cball (x t_max) ex" f B L
    by auto

  from usolves_ode_on_superset_domain[OF solution_usolves_ode solution_iv \<open>cball _ _ \<subseteq> X\<close>]
  have solution_usolves_on_X: "(solution usolves_ode f from t_max) (cball t_max et) X" by simp

  have ge_imps: "t0 \<le> t1" "t0 \<le> t2" "t0 \<le> t_max" "t_max < t_ne" if "t0 \<le> t_ne"
    using that t_ne_outside \<open>0 < et\<close> \<open>0 < ex\<close> max(1) \<open>t_max \<in> ?S\<close> \<open>t_max \<in> T\<close> t_ne x0 y0
    by (auto simp: min_def dist_real_def max_def closed_segment_eq_real_ivl split: if_split_asm)
  have le_imps: "t0 \<ge> t1" "t0 \<ge> t2" "t0 \<ge> t_max" "t_max > t_ne" if "t0 \<ge> t_ne"
    using that t_ne_outside \<open>0 < et\<close> \<open>0 < ex\<close> max(1) \<open>t_max \<in> ?S\<close> \<open>t_max \<in> T\<close> t_ne x0 y0
    by (auto simp: min_def dist_real_def max_def closed_segment_eq_real_ivl split: if_split_asm)

  define tt where "tt \<equiv> if t0 \<le> t_ne then min (t_max + et) t_ne else max (t_max - et) t_ne"
  have "tt \<in> cball t_max et" "tt \<in> {t0 -- t1}" "tt \<in> {t0 -- t2}"
    using ge_imps le_imps \<open>0 < et\<close> t_ne(1)
    by (auto simp: mem_cball closed_segment_eq_real_ivl tt_def dist_real_def abs_real_def min_def max_def not_less)

  have segment_unsplit: "{t0 -- t_max} \<union> {t_max -- tt} = {t0 -- tt}"
    using ge_imps le_imps \<open>0 < et\<close>
    by (auto simp: tt_def closed_segment_eq_real_ivl min_def max_def split: if_split_asm) arith

  have "tt \<in> {t0 -- t1}"
    using ge_imps le_imps \<open>0 < et\<close> t_ne(1)
    by (auto simp: tt_def closed_segment_eq_real_ivl min_def max_def split: if_split_asm)

  have "tt \<in> ?Z"
  proof (safe intro!: connected_componentI[where t = "{t0 -- t_max} \<union> {t_max -- tt}"])
    fix s assume s: "s \<in> {t_max -- tt}"
    have "{t_max--s} \<subseteq> {t_max -- tt}"
      by (rule closed_segment_subset) (auto simp: s)
    also have "\<dots> \<subseteq> cball t_max et"
      using \<open>tt \<in> cball t_max et\<close> \<open>0 < et\<close>
      by (intro closed_segment_subset) auto
    finally have subset: "{t_max--s} \<subseteq> cball t_max et" .
    from s show "s \<in> {t0--t1}" "s \<in> {t0--t2}"
      using ge_imps le_imps t_ne \<open>0 < et\<close>
      by (auto simp: tt_def min_def max_def closed_segment_eq_real_ivl split: if_split_asm)
    have ivl: "t_max \<in> {t_max -- s}" "is_interval {t_max--s}"
      using \<open>tt \<in> cball t_max et\<close> \<open>0 < et\<close> s
      by (simp_all add: is_interval_convex_1)
    {
      note ivl subset
      moreover
      have "{t_max--s} \<subseteq> {t0--t1}"
        using \<open>s \<in> {t0 -- t1}\<close> \<open>t_max \<in> ?S\<close>
        by (simp add: closed_segment_subset)
      from x this order_refl have "(x solves_ode f) {t_max--s} X"
        by (rule solves_ode_on_subset)
      moreover note solution_iv[symmetric]
      ultimately
      have "x s = solution s"
        by (rule usolves_odeD(4)[OF solution_usolves_on_X]) simp
    } moreover {
      note ivl subset
      moreover
      have "{t_max--s} \<subseteq> {t0--t2}"
        using \<open>s \<in> {t0 -- t2}\<close> \<open>t_max \<in> ?S\<close>
        by (simp add: closed_segment_subset)
      from y this order_refl have "(y solves_ode f) {t_max--s} X"
        by (rule solves_ode_on_subset)
      moreover from solution_iv[symmetric] have "y t_max = solution t_max"
        by (simp add: \<open>x t_max = y t_max\<close>)
      ultimately
      have "y s = solution s"
        by (rule usolves_odeD[OF solution_usolves_on_X]) simp
    } ultimately show "s \<in> (\<lambda>t. x t - y t) -` {0}" by simp
  next
    fix s assume s: "s \<in> {t0 -- t_max}"
    then show "s \<in> (\<lambda>t. x t - y t) -` {0}"
      by (auto intro!: max_equal_flows)
    show "s \<in> {t0--t1}" "s \<in> {t0--t2}"
      by (metis Int_iff \<open>t_max \<in> ?S\<close> closed_segment_closed_segment_subset ends_in_segment(1) s)+
  qed (auto simp: segment_unsplit)
  then have "dist t_ne t_max \<le> dist t_ne tt"
    by (rule max)
  moreover have "dist t_ne t_max > dist t_ne tt"
    using le_imps ge_imps \<open>0 < et\<close>
    by (auto simp: tt_def dist_real_def)
  ultimately show False by simp
qed

lemma csol_unique:
  assumes t1: "t1 \<in> existence_ivl t0 x0"
  assumes t2: "t2 \<in> existence_ivl t0 x0"
  assumes t: "t \<in> {t0 -- t1}" "t \<in> {t0 -- t2}"
  shows "csol t0 x0 t1 t = csol t0 x0 t2 t"
  using csols_unique[OF csol_mem_csols[OF t1] csol_mem_csols[OF t2]] t
  by simp

lemma flow_vderiv_on_left:
  "(flow t0 x0 has_vderiv_on (\<lambda>x. f x (flow t0 x0 x))) (existence_ivl t0 x0 \<inter> {..t0})"
  unfolding has_vderiv_on_def
proof safe
  fix t
  assume t: "t \<in> existence_ivl t0 x0" "t \<le> t0"
  with open_existence_ivl
  obtain e where "e > 0" and e: "\<And>s. s \<in> cball t e \<Longrightarrow> s \<in> existence_ivl t0 x0"
    by (force simp: open_contains_cball)
  have csol_eq: "csol t0 x0 (t - e) s = flow t0 x0 s" if "t - e \<le> s" "s \<le> t0" for s
    unfolding flow_def
    using that \<open>0 < e\<close> t e
    by (auto simp: cball_def dist_real_def abs_real_def closed_segment_eq_real_ivl subset_iff
      intro!: csol_unique in_existence_between_zeroI[of "t - e" x0 s]
      split: if_split_asm)
  from e[of "t - e"] \<open>0 < e\<close> have "t - e \<in> existence_ivl t0 x0" by (auto simp: mem_cball)

  let ?l = "existence_ivl t0 x0 \<inter> {..t0}"
  let ?s = "{t0 -- t - e}"

  from csol(4)[OF e[of "t - e"]] \<open>0 < e\<close>
  have 1: "(csol t0 x0 (t - e) solves_ode f) ?s X"
    by (auto simp: mem_cball)
  have "t \<in> {t0 -- t - e}" using t \<open>0 < e\<close> by (auto simp: closed_segment_eq_real_ivl)
  from solves_odeD(1)[OF 1, unfolded has_vderiv_on_def, rule_format, OF this]
  have "(csol t0 x0 (t - e) has_vector_derivative f t (csol t0 x0 (t - e) t)) (at t within ?s)" .
  also have "at t within ?s = (at t within ?l)"
    using t \<open>0 < e\<close>
    by (intro at_within_nhd[where S="{t - e <..< t0 + 1}"])
      (auto simp: closed_segment_eq_real_ivl intro!: in_existence_between_zeroI[OF \<open>t - e \<in> existence_ivl t0 x0\<close>])
  finally
  have "(csol t0 x0 (t - e) has_vector_derivative f t (csol t0 x0 (t - e) t)) (at t within existence_ivl t0 x0 \<inter> {..t0})" .
  also have "csol t0 x0 (t - e) t = flow t0 x0 t"
    using \<open>0 < e\<close> \<open>t \<le> t0\<close> by (auto intro!: csol_eq)
  finally
  show "(flow t0 x0 has_vector_derivative f t (flow t0 x0 t)) (at t within existence_ivl t0 x0 \<inter> {..t0})"
    apply (rule has_vector_derivative_transform_within[where d=e])
    using t \<open>0 < e\<close>
    by (auto intro!: csol_eq simp: dist_real_def)
qed

lemma flow_vderiv_on_right:
  "(flow t0 x0 has_vderiv_on (\<lambda>x. f x (flow t0 x0 x))) (existence_ivl t0 x0 \<inter> {t0..})"
  unfolding has_vderiv_on_def
proof safe
  fix t
  assume t: "t \<in> existence_ivl t0 x0" "t0 \<le> t"
  with open_existence_ivl
  obtain e where "e > 0" and e: "\<And>s. s \<in> cball t e \<Longrightarrow> s \<in> existence_ivl t0 x0"
    by (force simp: open_contains_cball)
  have csol_eq: "csol t0 x0 (t + e) s = flow t0 x0 s" if "s \<le> t + e" "t0 \<le> s" for s
    unfolding flow_def
    using e that \<open>0 < e\<close>
    by (auto simp: cball_def dist_real_def abs_real_def closed_segment_eq_real_ivl subset_iff
      intro!: csol_unique in_existence_between_zeroI[of "t + e" x0 s]
      split: if_split_asm)
  from e[of "t + e"] \<open>0 < e\<close> have "t + e \<in> existence_ivl t0 x0" by (auto simp: mem_cball dist_real_def)

  let ?l = "existence_ivl t0 x0 \<inter> {t0..}"
  let ?s = "{t0 -- t + e}"

  from csol(4)[OF e[of "t + e"]] \<open>0 < e\<close>
  have 1: "(csol t0 x0 (t + e) solves_ode f) ?s X"
    by (auto simp: dist_real_def mem_cball)
  have "t \<in> {t0 -- t + e}" using t \<open>0 < e\<close> by (auto simp: closed_segment_eq_real_ivl)
  from solves_odeD(1)[OF 1, unfolded has_vderiv_on_def, rule_format, OF this]
  have "(csol t0 x0 (t + e) has_vector_derivative f t (csol t0 x0 (t + e) t)) (at t within ?s)" .
  also have "at t within ?s = (at t within ?l)"
    using t \<open>0 < e\<close>
    by (intro at_within_nhd[where S="{t0 - 1 <..< t + e}"])
      (auto simp: closed_segment_eq_real_ivl intro!: in_existence_between_zeroI[OF \<open>t + e \<in> existence_ivl t0 x0\<close>])
  finally
  have "(csol t0 x0 (t + e) has_vector_derivative f t (csol t0 x0 (t + e) t)) (at t within ?l)" .
  also have "csol t0 x0 (t + e) t = flow t0 x0 t"
    using \<open>0 < e\<close> \<open>t0 \<le> t\<close> by (auto intro!: csol_eq)
  finally
  show "(flow t0 x0 has_vector_derivative f t (flow t0 x0 t)) (at t within ?l)"
    apply (rule has_vector_derivative_transform_within[where d=e])
    using t \<open>0 < e\<close>
    by (auto intro!: csol_eq simp: dist_real_def)
qed

lemma flow_usolves_ode:
  assumes iv_defined: "t0 \<in> T" "x0 \<in> X"
  shows "(flow t0 x0 usolves_ode f from t0) (existence_ivl t0 x0) X"
proof (rule usolves_odeI)
  let ?l = "existence_ivl t0 x0 \<inter> {..t0}" and ?r = "existence_ivl t0 x0 \<inter> {t0..}"
  let ?split = "?l \<union> ?r"
  have insert_idem: "insert t0 ?l = ?l" "insert t0 ?r = ?r" using iv_defined
    by auto
  from existence_ivl_initial_time have cl_inter: "closure ?l \<inter> closure ?r = {t0}"
  proof safe
    from iv_defined have "t0 \<in> ?l" by simp also note closure_subset finally show "t0 \<in> closure ?l" .
    from iv_defined have "t0 \<in> ?r" by simp also note closure_subset finally show "t0 \<in> closure ?r" .
    fix x
    assume xl: "x \<in> closure ?l"
    assume "x \<in> closure ?r"
    also have "closure ?r \<subseteq> closure {t0..}"
      by (rule closure_mono) simp
    finally have "t0 \<le> x" by simp
    moreover
    {
      note xl
      also have cl: "closure ?l \<subseteq> closure {..t0}"
        by (rule closure_mono) simp
      finally have "x \<le> t0" by simp
    } ultimately show "x = t0" by simp
  qed
  have "(flow t0 x0 has_vderiv_on (\<lambda>t. f t (flow t0 x0 t))) ?split"
    by (rule has_vderiv_on_union)
      (auto simp: cl_inter insert_idem flow_vderiv_on_right flow_vderiv_on_left)
  also have "?split = existence_ivl t0 x0"
    by auto
  finally have "(flow t0 x0 has_vderiv_on (\<lambda>t. f t (flow t0 x0 t))) (existence_ivl t0 x0)" .
  moreover
  have "flow t0 x0 t \<in> X" if "t \<in> existence_ivl t0 x0" for t
    using solves_odeD(2)[OF csol(4)[OF that]] that
    by (simp add: flow_def)
  ultimately show "(flow t0 x0 solves_ode f) (existence_ivl t0 x0) X"
    by (rule solves_odeI)
  show "t0 \<in> existence_ivl t0 x0" using iv_defined by simp
  show "is_interval (existence_ivl t0 x0)" by (simp add: is_interval_existence_ivl)
  fix z t
  assume z: "{t0 -- t} \<subseteq> existence_ivl t0 x0" "(z solves_ode f) {t0 -- t} X" "z t0 = flow t0 x0 t0"
  then have "t \<in> existence_ivl t0 x0" by auto
  moreover
  from csol[OF this] z have "(z, t) \<in> csols t0 x0" by (auto simp: csols_def)
  moreover have "(csol t0 x0 t, t) \<in> csols t0 x0"
    by (rule csol_mem_csols) fact
  ultimately
  show "z t = flow t0 x0 t"
    unfolding flow_def
    by (auto intro: csols_unique[rule_format])
qed

lemma flow_solves_ode: "t0 \<in> T \<Longrightarrow> x0 \<in> X \<Longrightarrow> (flow t0 x0 solves_ode f) (existence_ivl t0 x0) X"
  by (rule usolves_odeD[OF flow_usolves_ode])

lemma equals_flowI:
  assumes "t0 \<in> T'"
    "is_interval T'"
    "T' \<subseteq> existence_ivl t0 x0"
    "(z solves_ode f) T' X"
    "z t0 = flow t0 x0 t0" "t \<in> T'"
  shows "z t = flow t0 x0 t"
proof -
  from assms have iv_defined: "t0 \<in> T" "x0 \<in> X"
    unfolding atomize_conj
    using assms existence_ivl_subset mem_existence_ivl_iv_defined
    by blast
  show ?thesis
    using assms
    by (rule usolves_odeD[OF flow_usolves_ode[OF iv_defined]])
qed

lemma existence_ivl_maximal_segment:
  assumes "(x solves_ode f) {t0 -- t} X" "x t0 = x0"
  assumes "{t0 -- t} \<subseteq> T"
  shows "t \<in> existence_ivl t0 x0"
  using assms
  by (auto simp: existence_ivl_def csols_def)

lemma existence_ivl_maximal_interval:
  assumes "(x solves_ode f) S X" "x t0 = x0"
  assumes "t0 \<in> S" "is_interval S" "S \<subseteq> T"
  shows "S \<subseteq> existence_ivl t0 x0"
proof
  fix t assume "t \<in> S"
  with assms have subset1: "{t0--t} \<subseteq> S"
    by (intro closed_segment_subset) (auto simp: is_interval_convex_1)
  with \<open>S \<subseteq> T\<close> have subset2: "{t0 -- t} \<subseteq> T" by auto
  have "(x solves_ode f) {t0 -- t} X"
    using assms(1) subset1 order_refl
    by (rule solves_ode_on_subset)
  from this \<open>x t0 = x0\<close> subset2 show "t \<in> existence_ivl t0 x0"
    by (rule existence_ivl_maximal_segment)
qed

lemma maximal_existence_flow:
  assumes sol: "(x solves_ode f) K X" and iv: "x t0 = x0"
  assumes "is_interval K"
  assumes "t0 \<in> K"
  assumes "K \<subseteq> T"
  shows "K \<subseteq> existence_ivl t0 x0" "\<And>t. t \<in> K \<Longrightarrow> flow t0 x0 t = x t"
proof -
  from assms have iv_defined: "t0 \<in> T" "x0 \<in> X"
    unfolding atomize_conj
    using solves_ode_domainD by blast
  show exivl: "K \<subseteq> existence_ivl t0 x0"
    by (rule existence_ivl_maximal_interval; rule assms)
  show "flow t0 x0 t = x t" if "t \<in> K" for t
    apply (rule sym)
    apply (rule equals_flowI[OF \<open>t0 \<in> K\<close> \<open>is_interval K\<close> exivl sol _ that])
    by (simp add: iv iv_defined)
qed

lemma maximal_existence_flowI:
  assumes "(x has_vderiv_on (\<lambda>t. f t (x t))) K"
  assumes "\<And>t. t \<in> K \<Longrightarrow> x t \<in> X"
  assumes "x t0 = x0"
  assumes K: "is_interval K" "t0 \<in> K" "K \<subseteq> T"
  shows "K \<subseteq> existence_ivl t0 x0" "\<And>t. t \<in> K \<Longrightarrow> flow t0 x0 t = x t"
proof -
  from assms(1,2) have sol: "(x solves_ode f) K X" by (rule solves_odeI)
  from maximal_existence_flow[OF sol assms(3) K]
  show "K \<subseteq> existence_ivl t0 x0" "\<And>t. t \<in> K \<Longrightarrow> flow t0 x0 t = x t"
    by auto
qed

lemma flow_in_domain: "t \<in> existence_ivl t0 x0 \<Longrightarrow> flow t0 x0 t \<in> X"
  using flow_solves_ode solves_ode_domainD local.mem_existence_ivl_iv_defined
  by blast

lemma (in ll_on_open)
  assumes "t \<in> existence_ivl s x"
  assumes "x \<in> X"
  assumes auto: "\<And>s t x. x \<in> X \<Longrightarrow> f s x = f t x"
  assumes "T = UNIV"
  shows mem_existence_ivl_shift_autonomous1: "t - s \<in> existence_ivl 0 x"
    and flow_shift_autonomous1: "flow s x t = flow 0 x (t - s)"
proof -
  have na: "s \<in> T" "x \<in> X" and a: "0 \<in> T" "x \<in> X"
    by (auto simp: assms)

  have tI[simp]: "t \<in> T" for t by (simp add: assms)
  let ?T = "((+) (- s) ` existence_ivl s x)"
  have shifted: "is_interval ?T" "0 \<in> ?T"
    by (auto simp: \<open>x \<in> X\<close>)

  have "(\<lambda>t. t - s) = (+) (- s)" by auto
  with shift_autonomous_solution[OF flow_solves_ode[OF na], of s] flow_in_domain
  have sol: "((\<lambda>t. flow s x (t + s)) solves_ode f) ?T X"
    by (auto simp: auto \<open>x \<in> X\<close>)

  have "flow s x (0 + s) = x" using \<open>x \<in> X\<close> flow_initial_time by simp
  from maximal_existence_flow[OF sol this shifted]
  have *: "?T \<subseteq> existence_ivl 0 x"
    and **: "\<And>t. t \<in> ?T \<Longrightarrow> flow 0 x t = flow s x (t + s)"
    by (auto simp: subset_iff)

  have "t - s \<in> ?T"
    using \<open>t \<in> existence_ivl s x\<close>
    by auto
  also note *
  finally show "t - s \<in> existence_ivl 0 x" .

  show "flow s x t = flow 0 x (t - s)"
    using \<open>t \<in> existence_ivl s x\<close>
    by (auto simp: **)
qed

lemma (in ll_on_open)
  assumes "t - s \<in> existence_ivl 0 x"
  assumes "x \<in> X"
  assumes auto: "\<And>s t x. x \<in> X \<Longrightarrow> f s x = f t x"
  assumes "T = UNIV"
  shows mem_existence_ivl_shift_autonomous2: "t \<in> existence_ivl s x"
    and flow_shift_autonomous2: "flow s x t = flow 0 x (t - s)"
proof -
  have na: "s \<in> T" "x \<in> X" and a: "0 \<in> T" "x \<in> X"
    by (auto simp: assms)

  let ?T = "((+) s ` existence_ivl 0 x)"
  have shifted: "is_interval ?T" "s \<in> ?T"
    by (auto simp: a)

  have "(\<lambda>t. t + s) = (+) s"
    by (auto simp: )
  with shift_autonomous_solution[OF flow_solves_ode[OF a], of "-s"]
    flow_in_domain
  have sol: "((\<lambda>t. flow 0 x (t - s)) solves_ode f) ?T X"
    by (auto simp: auto algebra_simps)

  have "flow 0 x (s - s) = x"
    by (auto simp: a)
  from maximal_existence_flow[OF sol this shifted]
  have *: "?T \<subseteq> existence_ivl s x"
    and **: "\<And>t. t \<in> ?T \<Longrightarrow> flow s x t = flow 0 x (t - s)"
    by (auto simp: subset_iff assms)

  have "t \<in> ?T"
    using \<open>t - s \<in> existence_ivl 0 x\<close>
    by force
  also note *
  finally show "t \<in> existence_ivl s x" .

  show "flow s x t = flow 0 x (t - s)"
    using \<open>t - s \<in> existence_ivl _ _\<close>
    by (subst **; force)
qed

lemma
  flow_eq_rev:
  assumes "t \<in> existence_ivl t0 x0"
  shows "preflect t0 t \<in> ll_on_open.existence_ivl (preflect t0 ` T) (\<lambda>t. - f (preflect t0 t)) X t0 x0"
    "flow t0 x0 t = ll_on_open.flow (preflect t0 ` T) (\<lambda>t. - f (preflect t0 t)) X t0 x0 (preflect t0 t)"
proof -
  from mem_existence_ivl_iv_defined[OF assms] have mt0: "t0 \<in> preflect t0 ` existence_ivl t0 x0"
    by (auto simp: preflect_def)
  have subset: "preflect t0 ` existence_ivl t0 x0 \<subseteq> preflect t0 ` T"
    using existence_ivl_subset
    by (rule image_mono)
  from mt0 subset have "t0 \<in> preflect t0 ` T" by auto

  have sol: "((\<lambda>t. flow t0 x0 (preflect t0 t)) solves_ode (\<lambda>t. - f (preflect t0 t))) (preflect t0 ` existence_ivl t0 x0) X"
    using mt0
    by (rule preflect_solution) (auto simp: image_image flow_solves_ode mem_existence_ivl_iv_defined[OF assms])

  have flow0: "flow t0 x0 (preflect t0 t0) = x0" and ivl: "is_interval (preflect t0 ` existence_ivl t0 x0)"
    by (auto simp: preflect_def mem_existence_ivl_iv_defined[OF assms])

  interpret rev: ll_on_open "(preflect t0 ` T)" "(\<lambda>t. - f (preflect t0 t))" X ..
  from rev.maximal_existence_flow[OF sol flow0 ivl mt0 subset]
  show "preflect t0 t \<in> rev.existence_ivl t0 x0" "flow t0 x0 t = rev.flow t0 x0 (preflect t0 t)"
    using assms by (auto simp: preflect_def)
qed

lemma (in ll_on_open)
  shows rev_flow_eq: "t \<in> ll_on_open.existence_ivl (preflect t0 ` T) (\<lambda>t. - f (preflect t0 t)) X t0 x0 \<Longrightarrow>
    ll_on_open.flow (preflect t0 ` T) (\<lambda>t. - f (preflect t0 t)) X t0 x0 t = flow t0 x0 (preflect t0 t)"
  and mem_rev_existence_ivl_eq:
  "t \<in> ll_on_open.existence_ivl (preflect t0 ` T) (\<lambda>t. - f (preflect t0 t)) X t0 x0 \<longleftrightarrow> preflect t0 t \<in> existence_ivl t0 x0"
proof -
  interpret rev: ll_on_open "(preflect t0 ` T)" "(\<lambda>t. - f (preflect t0 t))" X ..
  from rev.flow_eq_rev[of _ t0 x0] flow_eq_rev[of "2 * t0 - t" t0 x0]
  show "t \<in> rev.existence_ivl t0 x0 \<Longrightarrow> rev.flow t0 x0 t = flow t0 x0 (preflect t0 t)"
    "(t \<in> rev.existence_ivl t0 x0) = (preflect t0 t \<in> existence_ivl t0 x0)"
    by (auto simp: preflect_def fun_Compl_def image_image dest: mem_existence_ivl_iv_defined
      rev.mem_existence_ivl_iv_defined)
qed

lemma
  shows rev_existence_ivl_eq: "ll_on_open.existence_ivl (preflect t0 ` T) (\<lambda>t. - f (preflect t0 t)) X t0 x0 = preflect t0 ` existence_ivl t0 x0"
    and existence_ivl_eq_rev: "existence_ivl t0 x0 = preflect t0 ` ll_on_open.existence_ivl (preflect t0 ` T) (\<lambda>t. - f (preflect t0 t)) X t0 x0"
  apply safe
  subgoal by (force simp: mem_rev_existence_ivl_eq)
  subgoal by (force simp: mem_rev_existence_ivl_eq)
  subgoal for x by (force intro!: image_eqI[where x="preflect t0 x"] simp: mem_rev_existence_ivl_eq)
  subgoal by (force simp: mem_rev_existence_ivl_eq)
  done

end

end
