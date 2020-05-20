section \<open>Additions to the ODE Library\<close>
theory ODE_Misc
  imports
    Ordinary_Differential_Equations.ODE_Analysis
    Analysis_Misc
begin

lemma local_lipschitz_compact_bicomposeE:
  assumes ll: "local_lipschitz T X f"
  assumes cf: "\<And>x. x \<in> X \<Longrightarrow> continuous_on I (\<lambda>t. f t x)"
  assumes cI: "compact I"
  assumes "I \<subseteq> T"
  assumes cv: "continuous_on I v"
  assumes cw: "continuous_on I w"
  assumes v: "v ` I \<subseteq> X"
  assumes w: "w ` I \<subseteq> X"
  obtains L where "L > 0" "\<And>x. x \<in> I \<Longrightarrow> dist (f x (v x)) (f x (w x)) \<le> L * dist (v x) (w x)"
proof -
  from v w have "v ` I \<union> w ` I \<subseteq> X" by auto
  with ll \<open>I \<subseteq> T\<close> have llI:"local_lipschitz I (v ` I \<union> w ` I) f"
    by (rule local_lipschitz_subset)
  have cvwI: "compact (v ` I \<union> w ` I)"
    by (auto intro!: compact_continuous_image cv cw cI)    

  from local_lipschitz_compact_implies_lipschitz[OF llI cvwI \<open>compact I\<close> cf]
  obtain L where L: "\<And>t. t \<in> I \<Longrightarrow> L-lipschitz_on (v ` I \<union> w ` I) (f t)"
    using v w
    by blast
  define L' where "L' = max L 1"
  with L have "L' > 0" "\<And>x. x \<in> I \<Longrightarrow> dist (f x (v x)) (f x (w x)) \<le> L' * dist (v x) (w x)"
     apply (auto simp: lipschitz_on_def L'_def)
    by (smt Un_iff image_eqI mult_right_mono zero_le_dist)
  then show ?thesis ..
qed

subsection \<open>Comparison Principle\<close>

lemma comparison_principle_le:
  fixes f::"real \<Rightarrow> real \<Rightarrow> real"
    and \<phi> \<psi>::"real \<Rightarrow> real"
  assumes ll: "local_lipschitz X Y f"
  assumes cf: "\<And>x. x \<in> Y \<Longrightarrow> continuous_on {a..b} (\<lambda>t. f t x)"
  assumes abX: "{a .. b} \<subseteq> X"
  assumes \<phi>': "\<And>x. x \<in> {a .. b} \<Longrightarrow> (\<phi> has_real_derivative \<phi>' x) (at x)"
  assumes \<psi>': "\<And>x. x \<in> {a .. b} \<Longrightarrow> (\<psi> has_real_derivative \<psi>' x) (at x)"
  assumes \<phi>_in: "\<phi> ` {a..b} \<subseteq> Y"
  assumes \<psi>_in: "\<psi> ` {a..b} \<subseteq> Y"
  assumes init: "\<phi> a \<le> \<psi> a"
  assumes defect: "\<And>x. x \<in> {a .. b} \<Longrightarrow> \<phi>' x - f x (\<phi> x) \<le> \<psi>' x - f x (\<psi> x)"
  shows "\<forall>x \<in> {a .. b}. \<phi> x \<le> \<psi> x" (is "?th1")
    (*
    "(\<forall>x \<in> {a .. b}. \<phi> x < \<psi> x) \<or> (\<exists>c\<in>{a..b}. (\<forall>x\<in>{a..c}. \<phi> x \<le> \<psi> x) \<and> (\<forall>x\<in>{c<..b}. \<phi> x < \<psi> x))"
    (is "?th2")
*)
  unfolding atomize_conj
  apply (cases "a \<le> b")
   defer subgoal by simp
proof -
  assume "a \<le> b"
  note \<phi>_cont = has_real_derivative_imp_continuous_on[OF \<phi>']
  note \<psi>_cont = has_real_derivative_imp_continuous_on[OF \<psi>']
  from local_lipschitz_compact_bicomposeE[OF ll cf compact_Icc abX \<phi>_cont \<psi>_cont \<phi>_in \<psi>_in]
  obtain L where L: "L > 0" "\<And>x. x \<in> {a..b} \<Longrightarrow> dist (f x (\<phi> x)) (f x (\<psi> x)) \<le> L * dist (\<phi> x) (\<psi> x)" by blast
  define w where "w x = \<psi> x - \<phi> x" for x

  have w'[derivative_intros]: "\<And>x. x \<in> {a .. b} \<Longrightarrow> (w has_real_derivative \<psi>' x - \<phi>' x) (at x)"
    using \<phi>' \<psi>'
    by (auto simp: has_vderiv_on_def w_def[abs_def] intro!: derivative_eq_intros)
  note w_cont[continuous_intros] = has_real_derivative_imp_continuous_on[OF w', THEN continuous_on_compose2]
  have "w d \<ge> 0" if "d \<in> {a .. b}" for d
  proof (rule ccontr, unfold not_le)
    assume "w d < 0"
    let ?N = "(w -` {..0} \<inter> {a .. d})"
    from \<open>w d < 0\<close> that have "d \<in> ?N" by auto
    then have "?N \<noteq> {}" by auto
    have "closed ?N"
      unfolding compact_eq_bounded_closed
      using that
      by (intro conjI closed_vimage_Int) (auto intro!: continuous_intros)

    let ?N' = "{a0 \<in> {a .. d}. w ` {a0 .. d} \<subseteq> {..0}}"
    from \<open>w d < 0\<close> that have "d \<in> ?N'" by simp
    then have "?N' \<noteq> {}" by auto
    have "compact ?N'"
      unfolding compact_eq_bounded_closed
    proof
      have "?N' \<subseteq> {a .. d}" using that by auto
      then show "bounded ?N'"
        by (rule bounded_subset[rotated]) simp
      have "w u \<le> 0" if "(\<forall>n. x n \<in> ?N')" "x \<longlonglongrightarrow> l" "l \<le> u" "u \<le> d" for x l u
      proof cases
        assume "l = u"
        have "\<forall>n. x n \<in> ?N" using that(1) by force
        from closed_sequentially[OF \<open>closed ?N\<close> this \<open>x \<longlonglongrightarrow> l\<close>]
        show ?thesis by (auto simp: \<open>l = u\<close>)
      next
        assume "l \<noteq> u" with that have "l < u" by auto
        from order_tendstoD(2)[OF \<open>x \<longlonglongrightarrow> l\<close> \<open>l < u\<close>] obtain n where "x n < u"
          by (auto dest: eventually_happens)
        with that show ?thesis using \<open>l < u\<close>
          by (auto dest!: spec[where x=n] simp: image_subset_iff)
      qed
      then show "closed ?N'"
        unfolding closed_sequential_limits
        by (auto simp: Lim_bounded Lim_bounded2)
    qed

    from compact_attains_inf[OF \<open>compact ?N'\<close> \<open>?N' \<noteq> {}\<close>]
    obtain a0 where a0: "a \<le> a0" "a0 \<le> d" "w ` {a0..d} \<subseteq> {..0}"
      and a0_least: "\<And>x. a \<le> x \<Longrightarrow> x \<le> d \<Longrightarrow> w ` {x..d} \<subseteq> {..0} \<Longrightarrow> a0 \<le> x"
      by auto
    have a0d: "{a0 .. d} \<subseteq> {a .. b}" using that a0
      by auto
    have L_w_bound: "L * w x \<le> \<psi>' x - \<phi>' x" if "x \<in> {a0 .. d}" for x
    proof -
      from set_mp[OF a0d that] have "x \<in> {a .. b}" .
      from defect[OF this]
      have "\<phi>' x - \<psi>' x \<le> dist (f x (\<phi> x)) (f x (\<psi> x))"
        by (simp add: dist_real_def)
      also have "\<dots> \<le> L * dist (\<phi> x) (\<psi> x)"
        using \<open>x \<in> {a .. b}\<close>
        by (rule L)
      also have "\<dots> \<le> -L * w x"
        using \<open>0 < L\<close> a0 that
        by (force simp add: dist_real_def abs_real_def w_def algebra_split_simps )
      finally show ?thesis
        by simp
    qed
    have mono: "mono_on (\<lambda>x. w x * exp(-L*x)) {a0..d}"
      apply (rule mono_onI)
      apply (rule DERIV_nonneg_imp_nondecreasing, assumption)
      using a0d
      by (auto intro!: exI[where x="(\<psi>' x - \<phi>' x) * exp (- (L * x)) - exp (- (L * x)) * L * w x" for x]
          derivative_eq_intros L_w_bound simp: )
    then have "w a0 * exp (-L * a0) \<le> w d * exp (-L * d)"
      by (rule mono_onD) (use that a0 in auto)
    also have "\<dots> < 0" using \<open>w d < 0\<close> by (simp add: algebra_split_simps)
    finally have "w a0 * exp (- L * a0) < 0" .
    then have "w a0 < 0" by (simp add: algebra_split_simps)
    have "a0 \<le> a"
    proof (rule ccontr, unfold not_le)
      assume "a < a0"
      have "continuous_on {a.. a0} w"
        by (rule continuous_intros, assumption) (use a0 a0d in auto)
      from continuous_on_Icc_at_leftD[OF this \<open>a < a0\<close>]
      have "(w \<longlongrightarrow> w a0) (at_left a0)" .
      from order_tendstoD(2)[OF this \<open>w a0 < 0\<close>] have "\<forall>\<^sub>F x in at_left a0. w x < 0" .
      moreover have "\<forall>\<^sub>F x in at_left a0. a < x"
        by (rule order_tendstoD) (auto intro!: \<open>a < a0\<close>)
      ultimately have "\<forall>\<^sub>F x in at_left a0. a < x \<and> w x < 0" by eventually_elim auto
      then obtain a1' where "a1'<a0" and a1_neg: "\<And>y. y > a1' \<Longrightarrow> y < a0 \<Longrightarrow> a < y \<and> w y < 0"
        unfolding eventually_at_left_field by auto
      define a1 where "a1 = (a1' + a0)/2"
      have "a1 < a0" using \<open>a1' < a0\<close> by (auto simp: a1_def)
      have "a \<le> a1"
        using \<open>a < a0\<close> a1_neg by (force simp: a1_def)
      moreover have "a1 \<le> d"
        using \<open>a1' < a0\<close> a0(2) by (auto simp: a1_def)
      moreover have "w ` {a1..a0} \<subseteq> {..0}"
        using \<open>w a0 < 0\<close> a1_neg a0(3)
        by (auto simp: a1_def) smt
      moreover have "w ` {a0..d} \<subseteq> {..0}" using a0 by auto
      ultimately
      have "a0 \<le> a1"
        apply (intro a0_least) apply assumption apply assumption
        by (smt atLeastAtMost_iff image_subset_iff)
      with \<open>a1<a0\<close> show False by simp
    qed
    then have "a0 = a" using \<open>a \<le> a0\<close> by simp
    with \<open>w a0 < 0\<close> have "w a < 0" by simp
    with init show False
      by (auto simp: w_def)
  qed
  then show ?thesis
    by (auto simp: w_def)
qed

lemma local_lipschitz_mult:
  shows "local_lipschitz  (UNIV::real set) (UNIV::real set) (*)"
  apply (auto intro!: c1_implies_local_lipschitz[where f'="\<lambda>p. blinfun_mult_left (fst p)"])
   apply (simp add: has_derivative_mult_right mult_commute_abs)
  by (auto intro!: continuous_intros)

lemma comparison_principle_le_linear:
  fixes \<phi> :: "real \<Rightarrow> real"
  assumes "continuous_on {a..b} g"
  assumes "(\<And>t. t \<in> {a..b} \<Longrightarrow> (\<phi> has_real_derivative \<phi>' t) (at t))"
  assumes "\<phi> a \<le> 0"
  assumes "(\<And>t. t \<in> {a..b} \<Longrightarrow> \<phi>' t \<le> g t *\<^sub>R \<phi> t)"
  shows "\<forall>t\<in>{a..b}. \<phi> t \<le> 0"
proof -
  have *: "\<And>x. continuous_on {a..b} (\<lambda>t. g t * x)"
    using assms(1) continuous_on_mult_right by blast
  then have "local_lipschitz (g`{a..b}) UNIV (*)"
    using local_lipschitz_subset[OF local_lipschitz_mult] by blast 
  from local_lipschitz_compose1[OF this assms(1)]
  have "local_lipschitz {a..b} UNIV (\<lambda>t. (*) (g t))" .
  from comparison_principle_le[OF this _ _ assms(2) _ _ _ assms(3), of b "\<lambda>t.0"] * assms(4)
  show ?thesis by auto
qed

subsection \<open>Locally Lipschitz ODEs\<close>

context ll_on_open_it begin

lemma flow_lipschitzE:
  assumes "{a .. b} \<subseteq> existence_ivl t0 x"
  obtains L where "L-lipschitz_on {a .. b} (flow t0 x)"
proof -
  have f': "(flow t0 x has_derivative (\<lambda>i. i *\<^sub>R f t (flow t0 x t))) (at t within {a .. b})" if "t \<in> {a .. b}" for t
    using flow_has_derivative[of t x] assms that
    by (auto simp: has_derivative_at_withinI)

  have "compact ((\<lambda>t. f t (flow t0 x t)) ` {a .. b})"
    using assms
    apply (auto intro!: compact_continuous_image continuous_intros)
    using local.existence_ivl_empty2 apply fastforce
     apply (meson atLeastAtMost_iff general.existence_ivl_subset in_mono)
    by (simp add: general.flow_in_domain subset_iff)
  then obtain C where "t \<in> {a .. b} \<Longrightarrow> norm (f t (flow t0 x t)) \<le> C" for t
    by (fastforce dest!: compact_imp_bounded simp: bounded_iff intro: that)
  then have "t \<in> {a..b} \<Longrightarrow> onorm (\<lambda>i. i *\<^sub>R f t (flow t0 x t)) \<le> max 0 C" for t
    apply (subst onorm_scaleR_left) 
     apply (auto simp: onorm_id max_def)
    by (metis diff_0_right diff_mono diff_self norm_ge_zero)
  from bounded_derivative_imp_lipschitz[OF f' _ this]
  have "(max 0 C)-lipschitz_on {a..b} (flow t0 x)"
    by auto
  then show ?thesis ..
qed

lemma flow_undefined0: "t \<notin> existence_ivl t0 x \<Longrightarrow> flow t0 x t = 0"
  unfolding flow_def by auto

lemma csols_undefined: "x \<notin> X \<Longrightarrow> csols t0 x = {}"
  apply (auto simp: csols_def)
  using general.existence_ivl_empty2 general.existence_ivl_maximal_segment
  apply blast
  done

lemmas existence_ivl_undefined = existence_ivl_empty2

end

subsection \<open>Reverse flow as Sublocale\<close>

lemma range_preflect_0[simp]: "range (preflect 0) = UNIV"
  by (auto simp: preflect_def)
lemma range_uminus[simp]: "range uminus = (UNIV::'a::ab_group_add set)"
  by auto

context auto_ll_on_open begin

sublocale rev: auto_ll_on_open "-f" rewrites "-(-f) = f"
   apply unfold_locales
  using auto_local_lipschitz auto_open_domain
  unfolding fun_Compl_def local_lipschitz_minus
  by auto

lemma existence_ivl_eq_rev0: "existence_ivl0 y = uminus ` rev.existence_ivl0 y" for y
  by (auto simp: existence_ivl_eq_rev rev.existence_ivl0_def preflect_def)

lemma rev_existence_ivl_eq0: "rev.existence_ivl0 y = uminus ` existence_ivl0 y" for y
  using uminus_uminus_image[of "rev.existence_ivl0 y"]
  by (simp add: existence_ivl_eq_rev0)

lemma flow_eq_rev0: "flow0 y t = rev.flow0 y (-t)" for y t
  apply (cases "t \<in> existence_ivl0 y")
  subgoal
    apply (subst flow_eq_rev(2), assumption)
    apply (subst rev.flow0_def)
    by (simp add: preflect_def)
  subgoal
    apply (frule flow_undefined0)
    by (auto simp: existence_ivl_eq_rev0 rev.flow_undefined0)
  done

lemma rev_eq_flow: "rev.flow0 y t = flow0 y (-t)" for y t
  apply (subst flow_eq_rev0)
  using uminus_uminus_image[of "rev.existence_ivl0 y"]
  apply -
  apply (subst (asm) existence_ivl_eq_rev0[symmetric])
  by auto

lemma rev_flow_image_eq: "rev.flow0 x ` S = flow0 x ` (uminus ` S)"
  unfolding rev_eq_flow[abs_def]
  by force

lemma flow_image_eq_rev: "flow0 x ` S = rev.flow0 x ` (uminus ` S)"
  unfolding rev_eq_flow[abs_def]
  by force

end

context c1_on_open begin

sublocale rev: c1_on_open "-f" "-f'" rewrites "-(-f) = f" and "-(-f') = f'"
  by (rule c1_on_open_rev) auto

end

context c1_on_open_euclidean begin

sublocale rev: c1_on_open_euclidean "-f" "-f'" rewrites "-(-f) = f" and "-(-f') = f'"
  by unfold_locales auto

end


subsection \<open>Autonomous LL ODE : Existence Interval and trapping on the interval\<close>

lemma bdd_above_is_intervalI: "bdd_above I"
  if "is_interval I" "a \<le> b" "a \<in> I" "b \<notin> I" for I::"real set"
  by (meson bdd_above_def is_interval_1 le_cases that) 

lemma bdd_below_is_intervalI: "bdd_below I"
  if "is_interval I" "a \<le> b" "a \<notin> I" "b \<in> I" for I::"real set"
  by (meson bdd_below_def is_interval_1 le_cases that) 

context auto_ll_on_open begin

lemma open_existence_ivl0:
  assumes x : "x \<in> X"
  shows "\<exists>a b. a < 0 \<and> 0 < b \<and> {a..b} \<subseteq> existence_ivl0 x"
proof -
  have a1:"0 \<in> existence_ivl0 x"
    by (simp add: x)
  have a2: "open (existence_ivl0 x)"
    by (simp add: x)
  from a1 a2 obtain d where "d > 0" "ball 0 d \<subseteq> existence_ivl0 x"
    using openE by blast
  have "{-d/2..d/2} \<subseteq> ball 0 d"
    using \<open>0 < d\<close> dist_norm mem_ball by auto
  thus ?thesis
    by (smt \<open>0 < d\<close> \<open>ball 0 d \<subseteq> existence_ivl0 x\<close> divide_minus_left half_gt_zero order_trans)
qed

lemma open_existence_ivl':
  assumes x : "x \<in> X"
  obtains a where "a > 0"  "{-a..a} \<subseteq> existence_ivl0 x"
proof -
  from open_existence_ivl0[OF assms(1)]
  obtain a b where ab: "a < 0" "0 < b" "{a..b} \<subseteq> existence_ivl0 x" by auto
  then have "min (-a) b > 0" by linarith
  have "{-min (-a) b .. min(-a) b} \<subseteq> {a..b}" by auto
  thus ?thesis using ab(3) that[OF \<open>min (-a) b > 0\<close>] by blast
qed

lemma open_existence_ivl_on_compact:
  assumes C: "C \<subseteq> X" and "compact C" "C \<noteq> {}"
  obtains a where "a > 0" "\<And>x. x \<in> C \<Longrightarrow> {-a..a} \<subseteq> existence_ivl0 x"
proof -
  from existence_ivl_cballs
  have "\<forall>x\<in>C. \<exists>e>0. \<exists>t>0. \<forall>y\<in>cball x e. cball 0 t\<subseteq>existence_ivl0 y"
    by (metis (full_types) C Int_absorb1 Int_iff UNIV_I)
  then
  obtain d' t' where *:
    "\<forall>x\<in>C. 0 < d' x \<and> t' x > 0 \<and> (\<forall>y\<in>cball x (d' x). cball 0 (t' x) \<subseteq> existence_ivl0 y)"
    by metis
  with compactE_image[OF \<open>compact C\<close>, of C "\<lambda>x. ball x (d' x)"]
  obtain C' where "C' \<subseteq> C" and [simp]: "finite C'" and C_subset: "C \<subseteq> (\<Union>c\<in>C'. ball c (d' c))"
    by force
  from C_subset \<open>C \<noteq> {}\<close> have [simp]: "C' \<noteq> {}" by auto
  define d where "d = Min (d' ` C')"
  define t where "t = Min (t' ` C')"
  have "t > 0" using * \<open>C' \<subseteq> C\<close>
    by (auto simp: t_def)
  moreover have "{-t .. t} \<subseteq> existence_ivl0 x" if "x \<in> C" for x
  proof -
    from C_subset that \<open>C' \<subseteq> C\<close>
    obtain c where c: "c \<in> C'" "x \<in> ball c (d' c)" "c \<in> C" by force
    then have "{-t .. t} \<subseteq> cball 0 (t' c)"
      by (auto simp: abs_real_def t_def minus_le_iff)
    also
    from c have "cball 0 (t' c) \<subseteq> existence_ivl0 x"
      using *[rule_format, OF \<open>c \<in> C\<close>] by auto
    finally show ?thesis .
  qed
  ultimately show ?thesis ..
qed

definition "trapped_forward x K \<longleftrightarrow> (flow0 x ` (existence_ivl0 x \<inter> {0..}) \<subseteq> K)"
  \<comment> \<open>TODO: use this for backwards trapped, invariant, and all assumptions\<close>

definition "trapped_backward x K \<longleftrightarrow> (flow0 x ` (existence_ivl0 x \<inter> {..0}) \<subseteq> K)"

definition "trapped x K \<longleftrightarrow> trapped_forward x K \<and> trapped_backward x K"

lemma trapped_iff_on_existence_ivl0:
  "trapped x K \<longleftrightarrow> (flow0 x ` (existence_ivl0 x) \<subseteq> K)"
  unfolding trapped_def trapped_forward_def trapped_backward_def
  apply (auto)
  by (metis IntI atLeast_iff atMost_iff image_subset_iff less_eq_real_def linorder_not_less)
end

context auto_ll_on_open begin

lemma infinite_rev_existence_ivl0_rewrites:
  "{0..} \<subseteq> rev.existence_ivl0 x \<longleftrightarrow> {..0} \<subseteq> existence_ivl0 x"
  "{..0} \<subseteq> rev.existence_ivl0 x \<longleftrightarrow> {0..} \<subseteq> existence_ivl0 x"
   apply (auto simp add: rev.rev_existence_ivl_eq0 subset_iff)
  using neg_le_0_iff_le apply fastforce
  using neg_0_le_iff_le by fastforce

lemma trapped_backward_iff_rev_trapped_forward:
  "trapped_backward x K  \<longleftrightarrow> rev.trapped_forward x K"
  unfolding trapped_backward_def rev.trapped_forward_def
  by (auto simp add: rev_flow_image_eq existence_ivl_eq_rev0 image_subset_iff)

text \<open>If solution is trapped in a compact set at some time
  on its existence interval then it is trapped forever\<close>
lemma trapped_sol_right:
  \<comment> \<open>TODO: when building on afp-devel (??? outdated):
    \<^url>\<open>https://bitbucket.org/isa-afp/afp-devel/commits/0c3edf9248d5389197f248c723b625c419e4d3eb\<close>\<close>
  assumes "compact K" "K \<subseteq> X"
  assumes "x \<in> X" "trapped_forward x K"
  shows "{0..} \<subseteq> existence_ivl0 x"
proof (rule ccontr)
  assume "\<not> {0..} \<subseteq> existence_ivl0 x"
  from this obtain t where "0 \<le> t" "t \<notin> existence_ivl0 x" by blast
  then have bdd: "bdd_above (existence_ivl0 x)" 
    by (auto intro!: bdd_above_is_intervalI \<open>x \<in> X\<close>)
  from flow_leaves_compact_ivl_right [OF UNIV_I \<open>x \<in> X\<close> bdd UNIV_I assms(1-2)]
  show False by (metis assms(4) trapped_forward_def IntI atLeast_iff image_subset_iff)
qed

lemma trapped_sol_right_gen:
  assumes "compact K" "K \<subseteq> X"
  assumes "t \<in> existence_ivl0 x" "trapped_forward (flow0 x t) K"
  shows "{t..} \<subseteq> existence_ivl0 x"
proof -
  have "x \<in> X"
    using assms(3) local.existence_ivl_empty_iff by fastforce 
  have xtk: "flow0 x t \<in> X"
    by (simp add: assms(3) local.flow_in_domain)
  from trapped_sol_right[OF assms(1-2) xtk assms(4)] have "{0..} \<subseteq> existence_ivl0 (flow0 x t)" .
  thus "{t..} \<subseteq> existence_ivl0 x"
    using existence_ivl_trans[OF assms(3)]
    by (metis add.commute atLeast_iff diff_add_cancel le_add_same_cancel1 subset_iff)
qed

lemma trapped_sol_left:
  \<comment> \<open>TODO: when building on afp-devel:
    \<^url>\<open>https://bitbucket.org/isa-afp/afp-devel/commits/0c3edf9248d5389197f248c723b625c419e4d3eb\<close>\<close>
  assumes "compact K" "K \<subseteq> X"
  assumes "x \<in> X" "trapped_backward x K"
  shows "{..0} \<subseteq> existence_ivl0 x"
proof (rule ccontr)
  assume "\<not> {..0} \<subseteq> existence_ivl0 x"
  from this obtain t where "t \<le> 0" "t \<notin> existence_ivl0 x" by blast
  then have bdd: "bdd_below (existence_ivl0 x)" 
    by (auto intro!: bdd_below_is_intervalI \<open>x \<in> X\<close>)
  from flow_leaves_compact_ivl_left [OF UNIV_I \<open>x \<in> X\<close> bdd UNIV_I assms(1-2)]
  show False
    by (metis IntI assms(4) atMost_iff auto_ll_on_open.trapped_backward_def auto_ll_on_open_axioms image_subset_iff)
qed

lemma trapped_sol_left_gen:
  assumes "compact K" "K \<subseteq> X"
  assumes "t \<in> existence_ivl0 x" "trapped_backward (flow0 x t) K"
  shows "{..t} \<subseteq> existence_ivl0 x"
proof -
  have "x \<in> X"
    using assms(3) local.existence_ivl_empty_iff by fastforce 
  have xtk: "flow0 x t \<in> X"
    by (simp add: assms(3) local.flow_in_domain)
  from trapped_sol_left[OF assms(1-2) xtk assms(4)] have "{..0} \<subseteq> existence_ivl0 (flow0 x t)" .
  thus "{..t} \<subseteq> existence_ivl0 x"
    using existence_ivl_trans[OF assms(3)]
    by (metis add.commute add_le_same_cancel1 atMost_iff diff_add_cancel subset_eq)
qed

lemma trapped_sol:
  assumes "compact K" "K \<subseteq> X"
  assumes "x \<in> X" "trapped x K"
  shows "existence_ivl0 x = UNIV"
  by (metis (mono_tags, lifting) assms existence_ivl_zero image_subset_iff interval local.existence_ivl_initial_time_iff local.existence_ivl_subset local.subset_mem_compact_implies_subset_existence_interval order_refl subset_antisym trapped_iff_on_existence_ivl0)

(* Follows from rectification *)
lemma regular_locally_noteq:\<comment> \<open>TODO: should be true in \<open>ll_on_open_it\<close>\<close>
  assumes "x \<in> X" "f x \<noteq> 0"
  shows "eventually (\<lambda>t. flow0 x t \<noteq> x) (at 0)"
proof -
  have nf:"norm (f x) > 0" by (simp add: assms(2)) 
      (* By continuity of solutions and f probably *)
  obtain a where
    a: "a>0"
    "{-a--a} \<subseteq> existence_ivl0 x"
    "0 \<in> {-a--a}"
    "\<And>t. t \<in> {-a--a} \<Longrightarrow> norm(f (flow0 x t) - f (flow0 x 0)) \<le> norm(f x)/2"
  proof -
    from open_existence_ivl'[OF assms(1)]
    obtain a1 where a1: "a1 > 0" "{-a1..a1} \<subseteq> existence_ivl0 x" .
    have "continuous (at 0) (\<lambda>t. norm(f (flow0 x t) - f (flow0 x 0) ))"
      apply (auto intro!: continuous_intros)
      by (simp add: assms(1) local.f_flow_continuous)
    then obtain a2 where "a2>0"
      "\<forall>t. norm t < a2 \<longrightarrow>
             norm (f (flow0 x t) - f (flow0 x 0)) < norm(f x)/2"
      unfolding continuous_at_real_range
      by (metis abs_norm_cancel cancel_comm_monoid_add_class.diff_cancel diff_zero half_gt_zero nf norm_zero)
    then have 
      t: "\<And>t. t \<in> {-a2<--<a2} \<Longrightarrow> norm(f (flow0 x t) - f (flow0 x 0)) \<le> norm(f x)/2"
      by (smt open_segment_bound(2) open_segment_bound1 real_norm_def)
    define a where "a = min a1 (a2/2)"
    have t1:"a > 0" unfolding a_def using \<open>a1 > 0\<close> \<open>a2 > 0\<close> by auto
    then have t3:"0 \<in>{-a--a}"
      using closed_segment_eq_real_ivl by auto
    have "{-a--a} \<subseteq> {-a1..a1}" unfolding a_def using \<open>a1 > 0\<close> \<open>a2 > 0\<close>
      using ODE_Auxiliarities.closed_segment_eq_real_ivl by auto
    then have t2:"{-a--a} \<subseteq> existence_ivl0 x" using a1 by auto
    have "{-a--a} \<subseteq> {-a2<--<a2}" unfolding a_def using \<open>a1 > 0\<close> \<open>a2 > 0\<close>
      by (smt Diff_iff closed_segment_eq_real_ivl atLeastAtMost_iff empty_iff half_gt_zero insert_iff pos_half_less segment(1) subset_eq)
    then have t4:"\<And>t. t \<in> {-a--a} \<Longrightarrow> norm(f (flow0 x t) - f (flow0 x 0)) \<le> norm(f x)/2" using t by auto
    show ?thesis using t1 t2 t3 t4 that by auto
  qed
  have "\<And>t. t \<in> {-a--a} \<Longrightarrow> (flow0 x has_vector_derivative f (flow0 x t)) (at t within {-a--a})"
    apply (rule has_vector_derivative_at_within)
    using a(2) by (auto intro!:flow_has_vector_derivative)
  from vector_differentiable_bound_linearization[OF this _ a(4)]
  have nb:"\<And>c d. {c--d} \<subseteq> {-a--a} \<Longrightarrow>
   norm (flow0 x d - flow0 x c - (d - c) *\<^sub>R f (flow0 x 0))  \<le> norm (d - c) * (norm (f x) / 2)"
    using a(3) by blast
  have "\<And>t. dist t 0 < a \<Longrightarrow> t \<noteq> 0 \<Longrightarrow> flow0 x t \<noteq> x"
  proof (rule ccontr)
    fix t
    assume "dist t 0 < a" "t \<noteq> 0" "\<not> flow0 x t \<noteq> x"
    then have tx:"flow0 x t = x" by auto
    have "t \<in> {-a--a}"
      using closed_segment_eq_real_ivl \<open>dist t 0 < a\<close> by auto
    have "t > 0 \<or> t < 0" using \<open>t \<noteq> 0\<close> by linarith
    moreover {
      assume "t > 0"
      then have "{0--t} \<subseteq> {-a--a}"
        by (simp add: \<open>t \<in> {-a--a}\<close> a(3) subset_closed_segment) 
      from nb[OF this] have
        "norm (flow0 x t - x - t *\<^sub>R f x) \<le> norm t * (norm (f x) / 2)"
        by (simp add: assms(1))
      then have "norm (t *\<^sub>R f x) \<le> norm t * (norm (f x) / 2)" using tx by auto
      then have False using nf
        using \<open>0 < t\<close> by auto 
    }
    moreover {
      assume "t < 0"
      then have "{t--0} \<subseteq> {-a--a}"
        by (simp add: \<open>t \<in> {-a--a}\<close> a(3) subset_closed_segment) 
      from nb[OF this] have
        "norm (x - flow0 x t + t *\<^sub>R f x) \<le> norm t * (norm (f x) / 2)"
        by (simp add: assms(1))
      then have "norm (t *\<^sub>R f x) \<le> norm t * (norm (f x) / 2)" using tx by auto
      then have False using nf
        using \<open>t < 0\<close> by auto 
    }
    ultimately show False by blast
  qed
  thus ?thesis unfolding eventually_at
    using a(1) by blast
qed

lemma compact_max_time_flow_in_closed:
  assumes "closed M" and t_ex: "t \<in> existence_ivl0 x"
  shows "compact {s \<in> {0..t}. flow0 x ` {0..s} \<subseteq> M}" (is "compact ?C")
  unfolding compact_eq_bounded_closed
proof
  have "bounded {0 .. t}" by auto
  then show "bounded ?C"
    by (rule bounded_subset) auto
  show "closed ?C"
    unfolding closed_def
  proof (rule topological_space_class.openI, clarsimp)
    \<comment> \<open>TODO: there must be a more abstract argument for this, e.g., with
      @{thm continuous_on_closed_vimageI} and then reasoning about the connected component around 0?\<close>
    fix s
    assume notM: "s \<le> t \<longrightarrow> 0 \<le> s \<longrightarrow> \<not> flow0 x ` {0..s} \<subseteq> M"
    consider "0 \<le> s" "s \<le> t" "flow0 x s \<notin> M" | "0 \<le> s" "s \<le> t" "flow0 x s \<in> M" | "s < 0" | "s > t"
      by arith
    then show "\<exists>T. open T \<and> s \<in> T \<and> T \<subseteq> - {s. 0 \<le> s \<and> s \<le> t \<and> flow0 x ` {0..s} \<subseteq> M}"
    proof cases
      assume s: "0 \<le> s" "s \<le> t" and sM: "flow0 x s \<notin> M"
      have "isCont (flow0 x) s"
        using s ivl_subset_existence_ivl[OF t_ex]
        by (auto intro!: flow_continuous)
      from this[unfolded continuous_at_open, rule_format, of "-M"] sM \<open>closed M\<close>
      obtain S where "open S" "s \<in> S" "(\<forall>x'\<in>S. flow0 x x' \<in> - M)"
        by auto
      then show ?thesis
        by (force intro!: exI[where x=S])
    next
      assume s: "0 \<le> s" "s \<le> t" and sM: "flow0 x s \<in> M"
      from this notM obtain s0 where s0: "0 \<le> s0" "s0 < s" "flow0 x s0 \<notin> M"
        by force
      from order_tendstoD(1)[OF tendsto_ident_at \<open>s0 < s\<close>, of UNIV, unfolded eventually_at_topological]
      obtain S where "open S" "s \<in> S" "\<And>x. x \<in> S \<Longrightarrow> x \<noteq> s \<Longrightarrow> s0 < x"
        by auto
      then show ?thesis using s0
        by (auto simp: intro!: exI[where x=S]) (smt atLeastAtMost_iff image_subset_iff)
    qed (force intro: exI[where x="{t<..}"] exI[where x="{..<0}"])+
  qed
qed

lemma flow_in_closed_max_timeE:
  assumes "closed M" "t \<in> existence_ivl0 x" "0 \<le> t" "x \<in> M"
  obtains T where "0 \<le> T" "T \<le> t" "flow0 x ` {0..T} \<subseteq> M"
    "\<And>s'. 0 \<le> s' \<Longrightarrow> s' \<le> t \<Longrightarrow> flow0 x ` {0..s'} \<subseteq> M \<Longrightarrow> s' \<le> T"
proof -
  let ?C = "{s \<in> {0..t}. flow0 x ` {0..s} \<subseteq> M}"
  have "?C \<noteq> {}"
    using assms
    using local.mem_existence_ivl_iv_defined
    by (auto intro!: exI[where x=0])
  from compact_max_time_flow_in_closed[OF assms(1,2)]
  have "compact ?C" .
  from compact_attains_sup[OF this \<open>?C \<noteq> {}\<close>]
  obtain s where s: "0 \<le> s" "s \<le> t" "flow0 x ` {0..s} \<subseteq> M"
    and s_max: "\<And>s'. 0 \<le> s' \<Longrightarrow> s' \<le> t \<Longrightarrow> flow0 x ` {0..s'} \<subseteq> M \<Longrightarrow> s' \<le> s"
    by auto
  then show ?thesis ..
qed

lemma flow_leaves_closed_at_frontierE:
  assumes "closed M" and t_ex: "t \<in> existence_ivl0 x" and "0 \<le> t" "x \<in> M" "flow0 x t \<notin> M"
  obtains s where "0 \<le> s" "s < t" "flow0 x ` {0..s} \<subseteq> M"
    "flow0 x s \<in> frontier M"
    "\<exists>\<^sub>F s' in at_right s. flow0 x s' \<notin> M"
proof -
  from flow_in_closed_max_timeE[OF assms(1-4)] assms(5)
  obtain s where s: "0 \<le> s" "s < t" "flow0 x ` {0..s} \<subseteq> M"
    and s_max: "\<And>s'. 0 \<le> s' \<Longrightarrow> s' \<le> t \<Longrightarrow> flow0 x ` {0..s'} \<subseteq> M \<Longrightarrow> s' \<le> s"
    by (smt atLeastAtMost_iff image_subset_iff)
  note s
  moreover
  have "flow0 x s \<notin> interior M"
  proof
    assume interior: "flow0 x s \<in> interior M"
    have "s \<in> existence_ivl0 x" using ivl_subset_existence_ivl[OF \<open>t \<in> _\<close>] s by auto
    from flow_continuous[OF this, THEN isContD, THEN topological_tendstoD, OF open_interior interior]
    have "\<forall>\<^sub>F s' in at s. flow0 x s' \<in> interior M" by auto
    then have "\<forall>\<^sub>F s' in at_right s. flow0 x s' \<in> interior M"
      by (auto simp: eventually_at_split)
    moreover have "\<forall>\<^sub>F s' in at_right s. s' < t"
      using tendsto_ident_at \<open>s < t\<close>
      by (rule order_tendstoD)
    ultimately have "\<forall>\<^sub>F s' in at_right s. flow0 x s' \<in> M \<and> s' < t"
      by eventually_elim (use interior_subset[of M] in auto)
    then obtain s' where s': "s < s'" "s' < t" "\<And>y. y > s \<Longrightarrow> y \<le> s' \<Longrightarrow> flow0 x y \<in> M"
      by (auto simp: eventually_at_right_field_le)
    have s'_ivl: "flow0 x ` {0..s'} \<subseteq> M"
    proof safe
      fix s'' assume "s'' \<in> {0 .. s'}"
      then show "flow0 x s'' \<in> M"
        using s interior_subset[of M] s'
        by (cases "s'' \<le> s") auto
    qed
    with s_max[of s'] \<open>s' < t\<close> \<open>0 \<le> s\<close> \<open>s < s'\<close> show False by auto
  qed
  then have "flow0 x s \<in> frontier M"
    using s closure_subset[of M]
    by (force simp: frontier_def)
  moreover
  have "compact (flow0 x -` M \<inter> {s..t})" (is "compact ?C")
    unfolding compact_eq_bounded_closed
  proof
    have "bounded {s .. t}" by simp
    then show "bounded ?C"
      by (rule bounded_subset) auto
    show "closed ?C"
      using \<open>closed M\<close> assms mem_existence_ivl_iv_defined(2)[OF t_ex] ivl_subset_existence_ivl[OF t_ex] \<open>0 \<le> s\<close>
      by (intro closed_vimage_Int) (auto intro!: continuous_intros)
  qed
  have "\<exists>\<^sub>F s' in at_right s. flow0 x s' \<notin> M"
    apply (rule ccontr)
    unfolding not_frequently
  proof -
    assume "\<forall>\<^sub>F s' in at_right s. \<not> flow0 x s' \<notin> M"
    moreover have "\<forall>\<^sub>F s' in at_right s. s' < t"
      using tendsto_ident_at \<open>s < t\<close>
      by (rule order_tendstoD)
    ultimately have "\<forall>\<^sub>F s' in at_right s. flow0 x s' \<in> M \<and> s' < t" by eventually_elim auto
    then obtain s' where s': "s < s'"
      "\<And>y. y > s \<Longrightarrow> y < s' \<Longrightarrow> flow0 x y \<in> M"
      "\<And>y. y > s \<Longrightarrow> y < s' \<Longrightarrow> y < t"
      by (auto simp: eventually_at_right_field)
    define s'' where "s'' = (s + s') / 2"
    have "0 \<le> s''" "s'' \<le> t"  "s < s''" "s'' < s'"
      using s s'
      by (auto simp del: divide_le_eq_numeral1 le_divide_eq_numeral1 simp: s''_def) fastforce
    then have "flow0 x ` {0..s''} \<subseteq> M"
      using s s'
      apply (auto simp: )
      subgoal for u
        by (cases "u\<le>s") auto
      done
    from s_max[OF \<open>0 \<le> s''\<close> \<open>s''\<le> t\<close> this] \<open>s'' > s\<close>
    show False by simp
  qed
  ultimately show ?thesis ..
qed


subsection \<open>Connectedness\<close>

lemma fcontX:
  shows "continuous_on X f"
  using auto_local_lipschitz local_lipschitz_continuous_on by blast

lemma fcontx:
  assumes "x \<in> X"
  shows "continuous (at x) f"
proof -
  have "open X" by simp
  from continuous_on_eq_continuous_at[OF this]
  show ?thesis using fcontX assms(1) by blast
qed

lemma continuous_at_imp_cball:
  assumes "continuous (at x) g"
  assumes "g x > (0::real)"
  obtains r where "r > 0" "\<forall>y \<in> cball x r. g y > 0"
proof -
  from assms(1)
  obtain d where "d>0" "g ` (ball x d) \<subseteq> ball (g x) ((g x)/2)"
    by (meson assms(2) continuous_at_ball half_gt_zero)
  then have "\<forall>y \<in> cball x (d/2). g y > 0"
    by (smt assms(2) dist_norm image_subset_iff mem_ball mem_cball pos_half_less real_norm_def)
  thus ?thesis
    using \<open>0 < d\<close> that half_gt_zero by blast
qed

text \<open> \<open>flow0\<close> is \<open>path_connected\<close> \<close>
lemma flow0_path_connected_time:
  assumes "ts \<subseteq> existence_ivl0 x" "path_connected ts"
  shows "path_connected (flow0 x ` ts)"
proof -
  have "continuous_on ts (flow0 x)"
    by (meson assms continuous_on_sequentially flow_continuous_on subsetD)
  from path_connected_continuous_image[OF this assms(2)] 
  show ?thesis .
qed

lemma flow0_path_connected:
  assumes "path_connected D"
    "path_connected ts"
    "\<And>x. x \<in> D \<Longrightarrow> ts \<subseteq> existence_ivl0 x"
  shows "path_connected ( (\<lambda>(x, y). flow0 x y) ` (D \<times> ts))"
proof -
  have "D \<times> ts \<subseteq> Sigma X existence_ivl0"
    using assms(3) subset_iff by fastforce
  then have a1:"continuous_on (D \<times> ts) (\<lambda>(x, y). flow0 x y)"
    using flow_continuous_on_state_space continuous_on_subset by blast 
  have a2 : "path_connected (D \<times> ts)" using path_connected_Times assms by auto
  from path_connected_continuous_image[OF a1 a2]
  show ?thesis .
qed

end

subsection \<open>Return Time and Implicit Function Theorem\<close>

context c1_on_open_euclidean begin

lemma flow_implicit_function:
  \<comment> \<open>TODO: generalization of @{thm returns_to_implicit_function}!\<close>
  fixes s::"'a::euclidean_space \<Rightarrow> real" and S::"'a set"
  assumes t: "t \<in> existence_ivl0 x" and x: "x \<in> X" and st: "s (flow0 x t) = 0"
  assumes Ds: "\<And>x. (s has_derivative blinfun_apply (Ds x)) (at x)"
  assumes DsC: "isCont Ds (flow0 x t)"
  assumes nz: "Ds (flow0 x t) (f (flow0 x t)) \<noteq> 0"
  obtains u e
  where "s (flow0 x (u x)) = 0"
    "u x = t"
    "(\<And>y. y \<in> cball x e \<Longrightarrow> s (flow0 y (u y)) = 0)"
    "continuous_on (cball x e) u"
    "(\<lambda>t. (t, u t)) ` cball x e \<subseteq> Sigma X existence_ivl0"
    "0 < e" "(u has_derivative (- blinfun_scaleR_left
                   (inverse (blinfun_apply (Ds (flow0 x t)) (f (flow0 x t)))) o\<^sub>L
                      (Ds (flow0 x t) o\<^sub>L flowderiv x t) o\<^sub>L embed1_blinfun)) (at x)"
proof -
  note [derivative_intros] = has_derivative_compose[OF _ Ds]
  have cont_s: "continuous_on UNIV s" by (rule has_derivative_continuous_on[OF Ds])
  note cls[simp, intro] = closed_levelset[OF cont_s]
  then have xt1: "(x, t) \<in> Sigma X existence_ivl0"
    by (auto simp: t x)
  have D: "(\<And>x. x \<in> Sigma X existence_ivl0 \<Longrightarrow>
      ((\<lambda>(x, t). s (flow0 x t)) has_derivative
       blinfun_apply (Ds (flow0 (fst x) (snd x)) o\<^sub>L (flowderiv (fst x) (snd x))))
       (at x))"
    by (auto intro!: derivative_eq_intros)
  have C: "isCont (\<lambda>x. Ds (flow0 (fst x) (snd x)) o\<^sub>L flowderiv (fst x) (snd x))
   (x, t)"
    using flowderiv_continuous_on[unfolded continuous_on_eq_continuous_within,
        rule_format, OF xt1]
    using at_within_open[OF xt1 open_state_space]
    by (auto intro!: continuous_intros tendsto_eq_intros x t
        isCont_tendsto_compose[OF DsC, unfolded poincare_map_def]
        simp: split_beta' isCont_def)
  have Z: "(case (x, t) of (x, t) \<Rightarrow> s (flow0 x t)) = 0"
    by (auto simp: st)
  have I1: "blinfun_scaleR_left (inverse (Ds (flow0 x t)(f (flow0 x t)))) o\<^sub>L 
    ((Ds (flow0 (fst (x, t))
            (snd (x, t))) o\<^sub>L
       flowderiv (fst (x, t))
        (snd (x, t))) o\<^sub>L
      embed2_blinfun)
     = 1\<^sub>L"
    using nz
    by (auto intro!: blinfun_eqI
        simp: flowderiv_def blinfun.bilinear_simps inverse_eq_divide poincare_map_def)
  have I2: "((Ds (flow0 (fst (x, t))
            (snd (x, t))) o\<^sub>L
       flowderiv (fst (x, t))
        (snd (x, t))) o\<^sub>L
      embed2_blinfun) o\<^sub>L blinfun_scaleR_left (inverse (Ds (flow0 x t)(f (flow0 x t))))
     = 1\<^sub>L"
    using nz
    by (auto intro!: blinfun_eqI
        simp: flowderiv_def blinfun.bilinear_simps inverse_eq_divide poincare_map_def)
  show ?thesis
    apply (rule implicit_function_theorem[where f="\<lambda>(x, t). s (flow0 x t)"
          and S="Sigma X existence_ivl0", OF D xt1 open_state_space order_refl C Z I1 I2])
     apply blast
    unfolding split_beta' fst_conv snd_conv poincare_map_def[symmetric]
    ..
qed

lemma flow_implicit_function_at:
  fixes s::"'a::euclidean_space \<Rightarrow> real" and S::"'a set"
  assumes x: "x \<in> X" and st: "s x = 0"
  assumes Ds: "\<And>x. (s has_derivative blinfun_apply (Ds x)) (at x)"
  assumes DsC: "isCont Ds x"
  assumes nz: "Ds x (f x) \<noteq> 0"
  assumes pos: "e > 0"
  obtains u d
  where
    "0 < d"
    "u x = 0"
    "\<And>y. y \<in> cball x d \<Longrightarrow> s (flow0 y (u y)) = 0"
    "\<And>y. y \<in> cball x d \<Longrightarrow> \<bar>u y\<bar> < e"
    "\<And>y. y \<in> cball x d \<Longrightarrow> u y \<in> existence_ivl0 y"
    "continuous_on (cball x d) u"
    "(u has_derivative -Ds x /\<^sub>R (Ds x) (f x)) (at x)"
proof -
  have x0: "flow0 x 0 = x" by (simp add: x)
  from flow_implicit_function[OF existence_ivl_zero[OF x] x, unfolded x0, of s, OF st Ds DsC nz]
  obtain u d0 where
    s0: "s (flow0 x (u x)) = 0"
    and u0: "u x = 0"
    and u: "\<And>y. y \<in> cball x d0 \<Longrightarrow> s (flow0 y (u y)) = 0"
    and uc: "continuous_on (cball x d0) u"
    and uex: "(\<lambda>t. (t, u t)) ` cball x d0 \<subseteq> Sigma X existence_ivl0"
    and d0: "0 < d0"
    and u': "(u has_derivative
     blinfun_apply
      (- blinfun_scaleR_left (inverse (blinfun_apply (Ds x) (f x))) o\<^sub>L (Ds x o\<^sub>L flowderiv x 0) o\<^sub>L embed1_blinfun))
     (at x)"
    by blast
  have "at x within cball x d0 = at x" by (rule at_within_interior) (auto simp: \<open>0 < d0\<close>)
  then have "(u \<longlongrightarrow> 0) (at x)"
    using uc d0 by (auto simp: continuous_on_def u0 dest!: bspec[where x=x])
  from tendstoD[OF this \<open>0 < e\<close>] pos u0
  obtain d1 where d1: "0 < d1" "\<And>xa. dist xa x \<le> d1 \<Longrightarrow> \<bar>u xa\<bar> < e"
    unfolding eventually_at_le
    by force
  define d where "d = min d0 d1"
  have "0 < d" by (auto simp: d_def d0 d1)
  moreover note u0
  moreover have "\<And>y. y \<in> cball x d \<Longrightarrow> s (flow0 y (u y)) = 0" by (auto intro!: u simp: d_def)
  moreover have "\<And>y. y \<in> cball x d \<Longrightarrow> \<bar>u y\<bar> < e" using d1 by (auto simp: d_def dist_commute)
  moreover have "\<And>y. y \<in> cball x d \<Longrightarrow> u y \<in> existence_ivl0 y"
    using uex by (force simp: d_def)
  moreover have "continuous_on (cball x d) u"
    using uc by (rule continuous_on_subset) (auto simp: d_def)
  moreover
  have "(u has_derivative -Ds x /\<^sub>R (Ds x) (f x)) (at x)"
    using u'
    by (rule has_derivative_subst) (auto intro!: ext simp: x x0 flowderiv_def blinfun.bilinear_simps)
  ultimately show ?thesis ..
qed

lemma returns_to_implicit_function_gen:
  \<comment> \<open>TODO: generalizes proof of @{thm returns_to_implicit_function}!\<close>
  fixes s::"'a::euclidean_space \<Rightarrow> real"
  assumes rt: "returns_to {x \<in> S. s x = 0} x" (is "returns_to ?P x")
  assumes cS: "closed S"
  assumes Ds: "\<And>x. (s has_derivative blinfun_apply (Ds x)) (at x)"
    "isCont Ds (poincare_map ?P x)"
    "Ds (poincare_map ?P x) (f (poincare_map ?P x)) \<noteq> 0"
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
  note [derivative_intros] = has_derivative_compose[OF _ Ds(1)]
  have cont_s: "continuous_on UNIV s" by (rule has_derivative_continuous_on[OF Ds(1)])
  note cls[simp, intro] = closed_levelset[OF cont_s]
  let ?t1 = "return_time ?P x"
  have cls[simp, intro]: "closed {x \<in> S. s x = 0}"
    by (rule closed_levelset_within) (auto intro!: cS continuous_on_subset[OF cont_s])

  have *: "poincare_map ?P x = flow0 x (return_time {x \<in> S. s x = 0} x)"
    by (simp add: poincare_map_def)
  have "return_time {x \<in> S. s x = 0} x \<in> existence_ivl0 x"
    "x \<in> X"
    "s (poincare_map ?P x) = 0"
    using poincare_map_returns rt
    by (auto intro!: return_time_exivl rt)
  note E = flow_implicit_function[of "return_time ?P x" x s Ds, OF this[unfolded *] Ds[unfolded *],
      folded *]
  show ?thesis
    by (rule E) rule
qed

text \<open>c.f. Perko Section 3.7 Lemma 2 part 1.\<close>

lemma flow_transversal_surface_finite_intersections:
  fixes s::"'a \<Rightarrow> 'b::real_normed_vector"
    and Ds::"'a \<Rightarrow> 'a \<Rightarrow>\<^sub>L 'b"
  assumes "closed S"
  assumes "\<And>x. (s has_derivative (Ds x)) (at x)"
  assumes "\<And>x. x \<in> S \<Longrightarrow> s x = 0 \<Longrightarrow> Ds x (f x) \<noteq> 0"
  assumes "a \<le> b" "{a .. b} \<subseteq> existence_ivl0 x"
  shows "finite {t\<in>{a..b}. flow0 x t \<in> {x \<in> S. s x = 0}}"
    \<comment> \<open>TODO: define notion of (compact/closed)-(continuous/differentiable/C1)-surface?\<close>
proof cases
  note Ds = \<open>\<And>x. (s has_derivative (Ds x)) (at x)\<close>
  note transversal = \<open>\<And>x. x \<in> S \<Longrightarrow> s x = 0 \<Longrightarrow> Ds x (f x) \<noteq> 0\<close>
  assume "a < b"
  show ?thesis
  proof (rule ccontr)
    let ?S = "{x \<in> S. s x = 0}"
    let ?T = "{t\<in>{a..b}. flow0 x t \<in> {x \<in> S. s x = 0}}"
    define \<phi> where "\<phi> = flow0 x"
    have [THEN continuous_on_compose2, continuous_intros]: "continuous_on S s"
      by (auto simp: intro!: has_derivative_continuous_on Ds intro: has_derivative_at_withinI)
    assume "infinite ?T"
    from compact_sequentialE[OF compact_Icc[of a b] this]
    obtain t tl where t: "t n \<in> ?T" "flow0 x (t n) \<in> ?S" "t n \<in> {a .. b}" "t n \<noteq> tl"
      and tl: "t \<longlonglongrightarrow> tl" "tl \<in> {a..b}"
    for n
      by force
    have tl_ex: "tl \<in> existence_ivl0 x" using \<open>{a .. b} \<subseteq> existence_ivl0 x\<close> \<open>tl \<in> {a .. b}\<close> by auto
    have "closed ?S"
      by (auto intro!: closed_levelset_within \<open>closed S\<close> continuous_intros)
    moreover
    have "\<forall>n. flow0 x (t n) \<in> ?S"
      using t by auto
    moreover
    have flow_t: "(\<lambda>n. flow0 x (t n)) \<longlonglongrightarrow> flow0 x tl"
      by (auto intro!: tendsto_eq_intros tl_ex tl)
    ultimately have "flow0 x tl \<in> ?S"
      by (rule closed_sequentially)

    let ?qt = "\<lambda>t. (flow0 x t - flow0 x tl) /\<^sub>R (t - tl)"
    from flow_has_vector_derivative[OF tl_ex, THEN has_vector_derivative_withinD]
    have qt_tendsto: "?qt \<midarrow>tl\<rightarrow> f (flow0 x tl)" .
    let ?q = "\<lambda>n. ?qt (t n)"
    have "filterlim t (at tl) sequentially"
      using tl(1)
      by (rule filterlim_atI) (simp add: t)
    with qt_tendsto have "?q \<longlonglongrightarrow> f (flow0 x tl)"
      by (rule filterlim_compose)
    then have "((\<lambda>n. Ds (flow0 x tl) (?q n))) \<longlonglongrightarrow> Ds (flow0 x tl) (f (flow0 x tl))"
      by (auto intro!: tendsto_intros)
    moreover

    from flow_lipschitzE[OF \<open>{a .. b} \<subseteq> existence_ivl0 x\<close>] obtain L' where L': "L'-lipschitz_on {a..b} (flow0 x)" .
    define L where "L = L' + 1"
    from lipschitz_on_le[OF L', of L] lipschitz_on_nonneg[OF L']
    have L: "L-lipschitz_on {a .. b} (flow0 x)" and "L > 0"
      by (auto simp: L_def)
    from flow_lipschitzE[OF \<open>{a .. b} \<subseteq> existence_ivl0 x\<close>] obtain L' where "L'-lipschitz_on {a..b} (flow0 x)" .
        \<comment> \<open>TODO: is this reasoning (below) with this Lipschitz constant really necessary?\<close>
    have s[simp]: "s (flow0 x (t n)) = 0""s (flow0 x tl) = 0"
      for n
      using t \<open>flow0 x tl \<in> ?S\<close>
      by auto

    from Ds(1)[of "flow0 x tl", unfolded has_derivative_within]
    have "(\<lambda>y. (1 / norm (y - flow0 x tl)) *\<^sub>R (s y - (s (flow0 x tl) + blinfun_apply (Ds (flow0 x tl)) (y - flow0 x tl)))) \<midarrow>flow0 x tl\<rightarrow> 0"
      by auto
    then have "((\<lambda>y. (1 / norm (y - flow0 x tl)) *\<^sub>R (s y - (s (flow0 x tl) + blinfun_apply (Ds (flow0 x tl)) (y - flow0 x tl)))) \<longlongrightarrow> 0)
      (nhds (flow0 x tl))"
      by (rule tendsto_nhds_continuousI) simp

    from filterlim_compose[OF this flow_t]
    have "(\<lambda>xa. (blinfun_apply (Ds (flow0 x tl)) (flow0 x (t xa) - flow0 x tl)) /\<^sub>R norm (flow0 x (t xa) - flow0 x tl))
      \<longlonglongrightarrow> 0"
      using t
      by (auto simp: inverse_eq_divide tendsto_minus_cancel_right)
    from tendsto_mult[OF tendsto_const[of "L"] tendsto_norm[OF this, simplified, simplified divide_inverse_commute[symmetric]]]\<comment> \<open>TODO: uuugly\<close>
    have Ds0: "(\<lambda>xa. norm (blinfun_apply (Ds (flow0 x tl)) (flow0 x (t xa) - flow0 x tl)) / (norm (flow0 x (t xa) - flow0 x tl)/(L))) \<longlonglongrightarrow> 0"
      by (auto simp: ac_simps)

    from _ Ds0 have "((\<lambda>n. Ds (flow0 x tl) (?q n)) \<longlonglongrightarrow> 0)"
      apply (rule Lim_null_comparison)
      apply (rule eventuallyI)
      unfolding norm_scaleR blinfun.scaleR_right abs_inverse divide_inverse_commute[symmetric]
      subgoal for n
        apply (cases "flow0 x (t n) = flow0 x tl")
        subgoal by (simp add: blinfun.bilinear_simps)
        subgoal
          apply (rule divide_left_mono)
          using lipschitz_onD[OF L, of "t n" tl] \<open>0 < L\<close> t(3) tl(2)
          by (auto simp: algebra_split_simps zero_less_divide_iff dist_norm pos_divide_le_eq
              intro!: add_pos_nonneg)
        done
      done
    ultimately have "Ds (flow0 x tl) (f (flow0 x tl)) = 0"
      by (rule LIMSEQ_unique)
    moreover have "Ds (flow0 x tl) (f (flow0 x tl)) \<noteq> 0"
      by (rule transversal) (use \<open>flow0 x tl \<in> ?S\<close> in auto)
    ultimately show False by auto
  qed
qed (use assms in auto)

lemma uniform_limit_flow0_state:\<comment> \<open>TODO: is that something more general?\<close>
  assumes "compact C"
  assumes "C \<subseteq> X"
  shows "uniform_limit C (\<lambda>s x. flow0 x s) (\<lambda>x. flow0 x 0) (at 0)"
proof (cases "C = {}")
  case True then show ?thesis by auto
next
  case False show ?thesis
  proof (rule uniform_limitI)
    fix e::real assume "0 < e"
    {
      fix x assume "x \<in> C"
      with assms have "x \<in> X" by auto
      from existence_ivl_cballs[OF UNIV_I \<open>x \<in> X\<close>]
      obtain t L u where "\<And>y. y \<in> cball x u \<Longrightarrow> cball 0 t \<subseteq> existence_ivl0 y"
        "\<And>s y. y \<in> cball x u \<Longrightarrow> s \<in> cball 0 t \<Longrightarrow> flow0 y s \<in> cball y u"
        "L-lipschitz_on (cball 0 t\<times>cball x u) (\<lambda>(t, x). flow0 x t)"
        "\<And>y. y \<in> cball x u \<Longrightarrow> cball y u \<subseteq> X"
        "0 < t" "0 < u"
        by metis
      then have "\<exists>L. \<exists>u>0. \<exists>t>0. L-lipschitz_on (cball 0 t\<times>cball x u) (\<lambda>(t, x). flow0 x t)" by blast
    } then have "\<forall>x\<in>C. \<exists>L. \<exists>u>0. \<exists>t>0. L-lipschitz_on (cball 0 t\<times>cball x u) (\<lambda>(t, x). flow0 x t)" ..
    then obtain L d' u' where
      L: "\<And>x. x \<in> C \<Longrightarrow> (L x)-lipschitz_on (cball 0 (d' x)\<times>cball x (u' x)) (\<lambda>(t, x). flow0 x t)"
      and d': "\<And>x. x \<in> C \<Longrightarrow> d' x > 0"
      and u': "\<And>x. x \<in> C \<Longrightarrow> u' x > 0"
      by metis
    have "C \<subseteq> (\<Union>c\<in>C. ball c (u' c))" using u' by auto
    from compactE_image[OF \<open>compact C\<close> _ this]
    obtain C' where "C' \<subseteq> C" and [simp]: "finite C'" and C'_cover: "C \<subseteq> (\<Union>c\<in>C'. ball c (u' c))"
      by auto
    from C'_cover obtain c' where c': "x \<in> C \<Longrightarrow> x \<in> ball (c' x) (u' (c' x))" "x \<in> C \<Longrightarrow> c' x \<in> C'" for x
      by (auto simp: subset_iff) metis
    have "\<forall>\<^sub>F s in at 0. \<forall>x\<in>ball c (u' c). dist (flow0 x s) (flow0 x 0) < e" if "c \<in> C'" for c
    proof -
      have cC: "c \<in> C"
        using c' \<open>c \<in> C'\<close> d' \<open>C' \<subseteq> C\<close>
        by auto
      have *: "dist (flow0 x s) (flow0 x 0) \<le> L c * \<bar>s\<bar>"
        if "x\<in>ball c (u' c)"
          "s \<in> cball 0 (d' c)"
        for x s
      proof -
        from L[OF cC, THEN lipschitz_onD, of "(0, x)" "(s, x)"] d'[OF cC] that
        show ?thesis
          by (auto simp: dist_prod_def dist_commute)
      qed
      have "\<forall>\<^sub>F s in at 0. abs s < d' c"
        by (rule order_tendstoD tendsto_intros)+ (use d' cC in auto)
      moreover have "\<forall>\<^sub>F s in at 0. L c * \<bar>s\<bar> < e"
        by (rule order_tendstoD tendsto_intros)+ (use \<open>0 < e\<close> in auto)
      ultimately show ?thesis
        apply eventually_elim
        apply (use * in auto)
        by smt
    qed
    then have "\<forall>\<^sub>F s in at 0. \<forall>c\<in>C'. \<forall>x\<in>ball c (u' c). dist (flow0 x s) (flow0 x 0) < e"
      by (simp add: eventually_ball_finite_distrib)
    then show "\<forall>\<^sub>F s in at 0. \<forall>x\<in>C. dist (flow0 x s) (flow0 x 0) < e"
      apply eventually_elim
      apply (auto simp: )
      subgoal for s x
        apply (drule bspec[where x="c' x"])
         apply (simp add: c'(2))
        apply (drule bspec) prefer 2 apply assumption
        apply auto
        using c'(1) by auto
      done
  qed
qed

end

subsection \<open>Fixpoints\<close>

context auto_ll_on_open begin

lemma fixpoint_sol:
  assumes "x \<in> X" "f x = 0"
  shows "existence_ivl0 x = UNIV" "flow0 x t = x"
proof -
  have sol: "((\<lambda>t::real. x) solves_ode (\<lambda>_. f)) UNIV X"
    apply (rule solves_odeI)
    by(auto simp add: assms intro!: derivative_intros)
  from maximal_existence_flow[OF sol] have
    "UNIV \<subseteq> existence_ivl0 x" "flow0 x t = x" by auto
  thus "existence_ivl0 x = UNIV" "flow0 x t = x" by auto
qed

end

end