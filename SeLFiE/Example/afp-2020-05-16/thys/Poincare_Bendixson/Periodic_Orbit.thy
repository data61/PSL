section \<open>Periodic Orbits\<close>
theory Periodic_Orbit
  imports 
    Ordinary_Differential_Equations.ODE_Analysis
    Analysis_Misc
    ODE_Misc
    Limit_Set
begin

text \<open> Definition of closed and periodic orbits and their associated properties \<close>

context auto_ll_on_open
begin

text \<open>
   TODO: not sure if the "closed orbit" terminology is standard
   Closed orbits have some non-zero recurrence time T where the flow returns to the initial state
   The period of a closed orbit is the infimum of all positive recurrence times
   Periodic orbits are the subset of closed orbits where the period is non-zero
  \<close>

definition "closed_orbit x \<longleftrightarrow>
  (\<exists>T \<in> existence_ivl0 x. T \<noteq> 0 \<and> flow0 x T = x)"

definition "period x =
  Inf {T \<in> existence_ivl0 x. T > 0 \<and> flow0 x T = x}"

definition "periodic_orbit x \<longleftrightarrow>
  closed_orbit x \<and> period x > 0"

lemma recurrence_time_flip_sign:
  assumes "T \<in> existence_ivl0 x" "flow0 x T = x"
  shows "-T \<in> existence_ivl0 x" "flow0 x (-T) = x"
  using assms existence_ivl_reverse apply fastforce
  using assms flows_reverse by fastforce  

lemma closed_orbit_recurrence_times_nonempty:
  assumes "closed_orbit x"
  shows " {T \<in> existence_ivl0 x. T > 0 \<and> flow0 x T = x} \<noteq> {}"
  apply auto
  using assms(1) unfolding closed_orbit_def
  by (smt recurrence_time_flip_sign)

lemma closed_orbit_recurrence_times_bdd_below:
  shows "bdd_below {T \<in> existence_ivl0 x. T > 0 \<and> flow0 x T = x}"
  unfolding bdd_below_def
  by (auto) (meson le_cases not_le)

lemma closed_orbit_period_nonneg:
  assumes "closed_orbit x"
  shows "period x \<ge> 0"
  unfolding period_def
  using assms(1) unfolding closed_orbit_def apply (auto intro!:cInf_greatest)
  by (smt recurrence_time_flip_sign)

lemma closed_orbit_in_domain:
  assumes "closed_orbit x"
  shows "x \<in> X"
  using assms unfolding closed_orbit_def
  using local.mem_existence_ivl_iv_defined(2) by blast

lemma closed_orbit_global_existence:
  assumes "closed_orbit x"
  shows "existence_ivl0 x = UNIV"
proof -
  obtain Tp where "Tp \<noteq> 0" "Tp \<in> existence_ivl0 x" "flow0 x Tp = x" using assms
    unfolding closed_orbit_def by blast
  then obtain T where T: "T > 0" "T \<in> existence_ivl0 x" "flow0 x T = x"
    by (smt recurrence_time_flip_sign)
  have apos: "real n * T \<in> existence_ivl0 x \<and> flow0 x (real n * T) = x" for n
  proof (induction n)
    case 0
    then show ?case using closed_orbit_in_domain assms by auto
  next
    case (Suc n)
    fix n
    assume ih:"real n * T \<in> existence_ivl0 x \<and> flow0 x (real n * T) = x"
    then have "T \<in> existence_ivl0 (flow0 x (real n * T))" using T by metis
    then have l:"real n * T + T \<in> existence_ivl0 x" using ih
      using existence_ivl_trans by blast 
    have "flow0 (flow0 x (real n * T)) T = x" using ih T by metis
    then have r: "flow0 x (real n * T + T) = x"
      by (simp add: T(2) ih local.flow_trans)
    show "real (Suc n) * T \<in> existence_ivl0 x \<and> flow0 x (real (Suc n) * T) = x"
      using l r
      by (simp add: add.commute distrib_left mult.commute)
  qed
  then have aneg: "-real n * T \<in> existence_ivl0 x \<and> flow0 x (-real n * T) = x" for n
    by (simp add: recurrence_time_flip_sign)
  have "\<forall>t. t \<in> existence_ivl0 x"
  proof safe
    fix t
    have "t \<ge> 0 \<or> t \<le> (0::real)" by linarith
    moreover {
      assume "t \<ge> 0"
      obtain k where "real k * T > t"
        using T(1) ex_less_of_nat_mult by blast
      then have "t \<in> existence_ivl0 x" using apos
        by (meson \<open>0 \<le> t\<close> atLeastAtMost_iff less_eq_real_def local.ivl_subset_existence_ivl subset_eq) 
    }
    moreover {
      assume "t \<le> 0"
      obtain k where "- real k * T < t"
        by (metis T(1) add.inverse_inverse ex_less_of_nat_mult mult.commute mult_minus_right neg_less_iff_less)
      then have "t \<in> existence_ivl0 x" using aneg
        by (smt apos atLeastAtMost_iff calculation(2) local.existence_ivl_trans' local.ivl_subset_existence_ivl mult_minus_left subset_eq)
    }
    ultimately show "t \<in> existence_ivl0 x" by blast
  qed
  thus ?thesis by auto
qed

lemma recurrence_time_multiples:
  fixes n::nat
  assumes "T \<in> existence_ivl0 x" "T \<noteq> 0" "flow0 x T = x"
  shows "\<And>t. flow0 x (t+T*n) = flow0 x t"
proof (induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  fix n t
  assume ih : "(\<And>t. flow0 x (t + T * real n) = flow0 x t)"
  have "closed_orbit x" using assms unfolding closed_orbit_def by auto
  from closed_orbit_global_existence[OF this] have ex:"existence_ivl0 x = UNIV" .
  have "flow0 x (t + T * real (Suc n)) = flow0 x (t+T*real n + T)"
    by (simp add: Groups.add_ac(3) add.commute distrib_left)
  also have "... = flow0 (flow0 x (t+ T*real n)) T" using ex
    by (simp add: local.existence_ivl_trans' local.flow_trans)
  also have "... = flow0 (flow0 x t) T" using ih by auto
  also have "... = flow0 (flow0 x T) t" using ex
    by (metis UNIV_I add.commute local.existence_ivl_trans' local.flow_trans)
  finally show "flow0 x (t + T * real (Suc n)) = flow0 x t" using assms(3) by simp
qed

lemma nasty_arithmetic1:
  fixes t T::real
  assumes "T > 0" "t \<ge> 0"
  obtains q r where "t = (q::nat) * T + r" "0 \<le> r" "r < T"
proof -
  define q where "q = floor (t / T)"
  have q:"q \<ge> 0" using assms unfolding q_def by auto
  from floor_divide_lower[OF assms(1), of t]
  have ql: "q * T \<le> t" unfolding q_def .
  from floor_divide_upper[OF assms(1), of t]
  have qu: "t < (q + 1)* T" unfolding q_def by auto
  define r where "r = t - q * T"
  have rl:"0 \<le> r" using ql unfolding r_def by auto
  have ru:"r < T" using qu unfolding r_def  by (simp add: distrib_right)
  show ?thesis using q r_def rl ru
    by (metis le_add_diff_inverse of_int_of_nat_eq plus_int_code(2) ql that zle_iff_zadd)
qed

lemma nasty_arithmetic2:
  fixes t T::real
  assumes "T > 0" "t \<le> 0"
  obtains q r where "t = (q::nat) * (-T) + r" "0 \<le> r" "r < T"
proof -
  have "-t \<ge> 0" using assms(2) by linarith
  from nasty_arithmetic1[OF assms(1) this]
  obtain q r where qr: "-t = (q::nat) * T + r" "0 \<le> r" "r < T" by blast
  then have "t = q * (-T) - r"  by auto
  then have "t = (q+(1::nat)) * (-T) + (T-r)" by (simp add: distrib_right)
  thus ?thesis using qr(2-3)
    by (smt \<open>t = real q * - T - r\<close> that) 
qed

lemma recurrence_time_restricts_compact_flow:
  assumes "T \<in> existence_ivl0 x" "T > 0" "flow0 x T = x"
  shows "flow0 x ` UNIV = flow0 x ` {0..T}"
  apply auto
proof -
  fix t
  have "t \<ge> 0 \<or> t \<le> (0::real)" by linarith
  moreover {
    assume "t \<ge> 0"
    from nasty_arithmetic1[OF assms(2) this]
    obtain q r where qr:"t = (q::nat) * T + r" "0 \<le> r" "r < T" by blast
    have "T \<noteq> 0" using assms(2) by auto
    from recurrence_time_multiples[OF assms(1) this assms(3),of "r" "q"]
    have "flow0 x t = flow0 x r"
      by (simp add: qr(1) add.commute mult.commute)
    then have "flow0 x t \<in> flow0 x ` {0..<T}" using qr by auto
  }
  moreover {
    assume "t \<le> 0"
    from nasty_arithmetic2[OF assms(2) this]
    obtain q r where qr:"t = (q::nat) * (-T) + r" "0 \<le> r" "r < T" by blast
    have "-T \<in> existence_ivl0 x" "-T \<noteq> 0" "flow0 x (-T) = x" using recurrence_time_flip_sign assms by auto
    from recurrence_time_multiples[OF this, of r q]
    have "flow0 x t = flow0 x r"
      by (simp add: mult.commute qr(1))
    then have "flow0 x t \<in> flow0 x ` {0..<T}" using qr by auto
  }
  ultimately show "flow0 x t \<in> flow0 x ` {0..T}"
    by auto
qed

lemma closed_orbitI:
  assumes "t \<noteq> t'" "t \<in> existence_ivl0 y" "t' \<in> existence_ivl0 y"
  assumes "flow0 y t = flow0 y t'"
  shows "closed_orbit y"
  unfolding closed_orbit_def
  by (smt assms local.existence_ivl_reverse local.existence_ivl_trans local.flow_trans local.flows_reverse)

(* TODO: can be considerably generalized *)
lemma flow0_image_UNIV:
  assumes "existence_ivl0 x = UNIV"
  shows "flow0 (flow0 x t) ` S = flow0 x ` (\<lambda>s. s + t) ` S"
  apply auto
   apply (metis UNIV_I add.commute assms image_eqI local.existence_ivl_trans' local.flow_trans)
  by (metis UNIV_I add.commute assms imageI local.existence_ivl_trans' local.flow_trans)

lemma recurrence_time_restricts_compact_flow':
  assumes "t < t'" "t \<in> existence_ivl0 y" "t' \<in> existence_ivl0 y"
  assumes "flow0 y t = flow0 y t'"
  shows "flow0 y ` UNIV = flow0 y ` {t..t'}"
proof -
  have "closed_orbit y"
    using assms(1-4) closed_orbitI inf.strict_order_iff by blast
  from closed_orbit_global_existence[OF this]
  have yex: "existence_ivl0 y = UNIV" .
  have a1:"t'- t \<in> existence_ivl0 (flow0 y t)"
    by (simp add: assms(2-3) local.existence_ivl_trans')
  have a2:"t' -t > 0" using assms(1) by auto
  have a3:"flow0 (flow0 y t) (t' - t) = flow0 y t"
    using a1 assms(2) assms(4) local.flow_trans by fastforce 
  from recurrence_time_restricts_compact_flow[OF a1 a2 a3]
  have eq:"flow0 (flow0 y t) ` UNIV = flow0 (flow0 y t) ` {0.. t'-t}" .
  from flow0_image_UNIV[OF yex, of _ "UNIV"]
  have eql:"flow0 (flow0 y t) ` UNIV = flow0 y ` UNIV"
    by (metis (no_types) add.commute surj_def surj_plus)
  from flow0_image_UNIV[OF yex, of _ "{0..t'-t}"]
  have eqr:"flow0 (flow0 y t) ` {0.. t'-t} = flow0 y ` {t..t'}" by auto
  show ?thesis using eq eql eqr by auto
qed

lemma closed_orbitE':
  assumes "closed_orbit x"
  obtains T where "T > 0" "\<And>t (n::nat). flow0 x (t+T*n) = flow0 x t"
proof -
  obtain Tp where "Tp \<noteq> 0" "Tp \<in> existence_ivl0 x" "flow0 x Tp = x" using assms
    unfolding closed_orbit_def by blast
  then obtain T where T: "T > 0" "T \<in> existence_ivl0 x" "flow0 x T = x"
    by (smt recurrence_time_flip_sign)
  thus ?thesis using  recurrence_time_multiples T that by blast 
qed

lemma closed_orbitE:
  assumes "closed_orbit x"
  obtains T where "T > 0" "\<And>t. flow0 x (t+T) = flow0 x t"
  using closed_orbitE'
  by (metis assms mult.commute reals_Archimedean3)

lemma closed_orbit_flow_compact:
  assumes "closed_orbit x"
  shows "compact(flow0 x ` UNIV)"
proof -
  obtain Tp where "Tp \<noteq> 0" "Tp \<in> existence_ivl0 x" "flow0 x Tp = x" using assms
    unfolding closed_orbit_def by blast
  then obtain T where T: "T \<in> existence_ivl0 x" "T > 0" "flow0 x T = x"
    by (smt recurrence_time_flip_sign)
  from recurrence_time_restricts_compact_flow[OF this]
  have feq: "flow0 x ` UNIV = flow0 x ` {0..T}" .
  have "continuous_on {0..T} (flow0 x)"
    by (meson T(1) continuous_on_sequentially in_mono local.flow_continuous_on local.ivl_subset_existence_ivl) 
  from compact_continuous_image[OF this]
  have "compact (flow0 x ` {0..T})" by auto
  thus ?thesis using feq by auto
qed

lemma fixed_point_imp_closed_orbit_period_zero:
  assumes "x \<in> X"
  assumes "f x = 0"
  shows "closed_orbit x" "period x = 0"
proof -
  from fixpoint_sol[OF assms] have fp:"existence_ivl0 x = UNIV" "\<And>t. flow0 x t = x" by auto
  then have co:"closed_orbit x" unfolding closed_orbit_def by blast
  have a: "\<forall>y>0. \<exists>a\<in>{T \<in> existence_ivl0 x. 0 < T \<and> flow0 x T = x}. a < y"
    apply auto
    using fp
    by (simp add: dense) 
  from cInf_le_iff[OF closed_orbit_recurrence_times_nonempty[OF co]
      closed_orbit_recurrence_times_bdd_below , of 0]
  have "period x \<le> 0" unfolding period_def using a by auto
  from closed_orbit_period_nonneg[OF co] have "period x \<ge> 0" .
  then have "period x = 0" using \<open>period x \<le> 0\<close> by linarith
  thus "closed_orbit x" "period x = 0" using co by auto
qed

lemma closed_orbit_period_zero_fixed_point:
  assumes "closed_orbit x" "period x = 0"
  shows "f x = 0"
proof (rule ccontr)
  assume "f x \<noteq> 0"
  from regular_locally_noteq[OF closed_orbit_in_domain[OF assms(1)] this]
  have "\<forall>\<^sub>F t in at 0. flow0 x t \<noteq> x " .
  then obtain r where "r>0" "\<forall>t. t \<noteq> 0 \<and> dist t 0 < r \<longrightarrow> flow0 x t \<noteq> x" unfolding eventually_at
    by auto
  then have "period x \<ge> r" unfolding period_def
    apply (auto intro!:cInf_greatest)
     apply (meson assms(1) closed_orbit_def linorder_neqE_linordered_idom neg_0_less_iff_less recurrence_time_flip_sign)
    using not_le by force
  thus False using assms(2) \<open>r >0\<close> by linarith
qed

lemma closed_orbit_subset_\<omega>_limit_set:
  assumes "closed_orbit x"
  shows "flow0 x ` UNIV \<subseteq> \<omega>_limit_set x"
  unfolding \<omega>_limit_set_def \<omega>_limit_point_def
proof clarsimp
  fix t
  from closed_orbitE'[OF assms]
  obtain T where T: "0 < T" "\<And>t n. flow0 x (t + T* real n) = flow0 x t" by blast
  define s where "s = (\<lambda>n::nat. t + T * real n)"
  have exist: "{0..} \<subseteq> existence_ivl0 x"
    by (simp add: assms closed_orbit_global_existence)
  have l:"filterlim s at_top sequentially" unfolding s_def
    using T(1)
    by (auto intro!:filterlim_tendsto_add_at_top filterlim_tendsto_pos_mult_at_top
        simp add: filterlim_real_sequentially)
  have "flow0 x \<circ> s = (\<lambda>n. flow0 x t)" unfolding o_def s_def using T(2) by simp
  then have r:"(flow0 x \<circ> s) \<longlonglongrightarrow> flow0 x t" by auto
  show "{0..} \<subseteq> existence_ivl0 x \<and> (\<exists>s. s \<longlonglongrightarrow>\<^bsub>\<^esub> \<infinity> \<and> (flow0 x \<circ> s) \<longlonglongrightarrow> flow0 x t)"
    using exist l r by blast
qed

lemma closed_orbit_\<omega>_limit_set:
  assumes "closed_orbit x"
  shows "flow0 x ` UNIV = \<omega>_limit_set x"
proof -
  have "\<omega>_limit_set x \<subseteq> flow0 x ` UNIV"
    using closed_orbit_global_existence[OF assms]
    by (intro \<omega>_limit_set_in_compact_subset)
      (auto intro!: flow_in_domain
        simp add: assms closed_orbit_in_domain image_subset_iff trapped_forward_def
        closed_orbit_flow_compact)
  thus ?thesis using closed_orbit_subset_\<omega>_limit_set[OF assms] by auto
qed

lemma flow0_inj_on:
  assumes "t \<le> t'"
  assumes "{t..t'} \<subseteq> existence_ivl0 x"
  assumes "\<And>s. t < s \<Longrightarrow> s \<le> t' \<Longrightarrow> flow0 x s \<noteq> flow0 x t"
  shows "inj_on (flow0 x) {t..t'}"
  apply (rule inj_onI)
proof (rule ccontr)
  fix u v
  assume uv: "u \<in> {t..t'}" "v \<in> {t..t'}" "flow0 x u = flow0 x v" "u \<noteq> v"
  have "u < v \<or> v < u" using uv(4) by linarith
  moreover {
    assume "u < v"
    from recurrence_time_restricts_compact_flow'[OF this _ _ uv(3)]
    have "flow0 x ` UNIV = flow0 x ` {u..v}"  using uv(1-2) assms(2) by blast
    then have "flow0 x t \<in> flow0 x ` {u..v}" by auto
    moreover have "u = t \<or> flow0 x t \<notin> flow0 x ` {u..v}" using assms(3)
      by (smt atLeastAtMost_iff image_iff uv(1) uv(2))
    ultimately have False using uv assms(3)
      by force
  }
  moreover {
    assume "v < u"
    from recurrence_time_restricts_compact_flow'[OF this _ _ ]
    have "flow0 x ` UNIV = flow0 x ` {v..u}"
      by (metis assms(2) subset_iff uv(1) uv(2) uv(3))
    then have "flow0 x t \<in> flow0 x ` {v..u}" by auto
    moreover have "v = t \<or> flow0 x t \<notin> flow0 x ` {v..u}" using assms(3)
      by (smt atLeastAtMost_iff image_iff uv(1) uv(2))
    ultimately have False using uv assms(3) by force
  }
  ultimately show False by blast
qed

(* TODO: Probably has a simpler proof *)
lemma finite_\<omega>_limit_set_in_compact_imp_unique_fixed_point:
  assumes "compact K" "K \<subseteq> X"
  assumes "x \<in> X" "trapped_forward x K"
  assumes "finite (\<omega>_limit_set x)"
  obtains y where "\<omega>_limit_set x = {y}" "f y = 0"
proof -
  from connected_finite_iff_sing[OF \<omega>_limit_set_in_compact_connected]
  obtain y where y: "\<omega>_limit_set x = {y}"
    using \<omega>_limit_set_in_compact_nonempty assms by auto
  have "f y = 0"
  proof (rule ccontr)
    assume fy:"f y \<noteq> 0"
    from \<omega>_limit_set_in_compact_existence[OF assms(1-4)]
    have yex: "existence_ivl0 y = UNIV"
      by (simp add: y)
    then have "y \<in> X"
      by (simp add: local.mem_existence_ivl_iv_defined(2))
    from regular_locally_noteq[OF this fy]
    have "\<forall>\<^sub>F t in at 0. flow0 y t \<noteq> y" .
    then obtain r where r: "r>0" "\<forall>t. t \<noteq> 0 \<and> dist t 0 < r \<longrightarrow> flow0 y t \<noteq> flow0 y 0"
      unfolding eventually_at using \<open>y \<in> X\<close>
      by auto
    then have "\<And>s. 0 < s \<Longrightarrow> s \<le> r/2 \<Longrightarrow> flow0 y s \<noteq> flow0 y 0" by simp
    from flow0_inj_on[OF _ _ this, of "r/2"]
    obtain "inj_on(flow0 y) {0..r/2}" using r yex by simp
    then have "infinite (flow0 y`{0..r/2})" by (simp add: finite_image_iff r(1))
    moreover from \<omega>_limit_set_invariant[of x]
    have "flow0 y `{0..r/2} \<subseteq> \<omega>_limit_set x" using y yex
      unfolding invariant_def trapped_iff_on_existence_ivl0 by auto
    ultimately show False using y
      by (metis assms(5) finite.emptyI subset_singleton_iff)
  qed
  thus ?thesis using that y by auto
qed

lemma closed_orbit_periodic:
  assumes "closed_orbit x" "f x \<noteq> 0"
  shows "periodic_orbit x"
  unfolding periodic_orbit_def
  using assms(1) apply auto
proof (rule ccontr)
  assume "closed_orbit x"
  from closed_orbit_period_nonneg[OF assms(1)] have nneg: "period x \<ge> 0" .
  assume "\<not> 0 < period x"
  then have "period x = 0" using nneg by linarith
  from closed_orbit_period_zero_fixed_point[OF assms(1) this]
  have "f x = 0" . 
  thus False using assms(2) by linarith
qed

lemma periodic_orbitI:
  assumes "t \<noteq> t'" "t \<in> existence_ivl0 y" "t' \<in> existence_ivl0 y"
  assumes "flow0 y t = flow0 y t'"
  assumes "f y \<noteq> 0"
  shows "periodic_orbit y"
proof -
  have y:"y \<in> X"
    using assms(3) local.mem_existence_ivl_iv_defined(2) by blast
  from closed_orbitI[OF assms(1-4)] have "closed_orbit y" .
  from closed_orbit_periodic[OF this assms(5)]
  show ?thesis .
qed

lemma periodic_orbit_recurrence_times_closed:
  assumes "periodic_orbit x"
  shows "closed {T \<in> existence_ivl0 x. T > 0 \<and> flow0 x T = x}"
proof -
  have a1:"x \<in> X"
    using assms closed_orbit_in_domain periodic_orbit_def by auto 
  have a2:"f x \<noteq> 0"
    using assms closed_orbit_in_domain fixed_point_imp_closed_orbit_period_zero(2) periodic_orbit_def by auto
  from regular_locally_noteq[OF a1 a2] have
    "\<forall>\<^sub>F t in at 0. flow0 x t \<noteq> x" .
  then obtain r where r:"r>0" "\<forall>t. t \<noteq> 0 \<and> dist t 0 < r \<longrightarrow> flow0 x t \<noteq> x" unfolding eventually_at
    by auto
  show ?thesis
  proof (auto intro!:discrete_imp_closed[OF r(1)])
    fix t1 t2
    assume t12: "t1 > 0" "flow0 x t1 = x" "t2 > 0" "flow0 x t2 = x" "dist t2 t1 < r"
    then have fx: "flow0 x (t1-t2) = x"
      by (smt a1 assms closed_orbit_global_existence existence_ivl_zero general.existence_ivl_initial_time_iff local.flow_trans periodic_orbit_def)
    have "dist (t1-t2) 0 < r" using t12(5)
      by (simp add: dist_norm) 
    thus "t2 = t1" using r fx
      by smt
  qed
qed

lemma periodic_orbit_period:
  assumes "periodic_orbit x"
  shows "period x > 0" "flow0 x (period x) = x"
proof -
  from periodic_orbit_recurrence_times_closed[OF assms(1)]
  have cl: "closed {T \<in> existence_ivl0 x. T > 0 \<and> flow0 x T = x}" .
  have "closed_orbit x" using assms(1) unfolding periodic_orbit_def by auto
  from closed_contains_Inf[OF closed_orbit_recurrence_times_nonempty[OF this]
      closed_orbit_recurrence_times_bdd_below cl]
  have "period x \<in>  {T \<in> existence_ivl0 x. T > 0 \<and> flow0 x T = x}" unfolding period_def .
  thus "period x > 0" "flow0 x (period x) = x" by auto
qed

lemma closed_orbit_flow0:
  assumes "closed_orbit x"
  shows "closed_orbit (flow0 x t)"
proof -
  from closed_orbit_global_existence[OF assms]
  have "existence_ivl0 x = UNIV" .
  from closed_orbitE[OF assms]
  obtain T where "T > 0" "flow0 x (t+T) = flow0 x t"
    by metis
  thus ?thesis unfolding closed_orbit_def
    by (metis UNIV_I \<open>existence_ivl0 x = UNIV\<close> less_irrefl local.existence_ivl_trans' local.flow_trans)
qed

lemma periodic_orbit_imp_flow0_regular:
  assumes "periodic_orbit x"
  shows "f (flow0 x t) \<noteq> 0"
  by (metis UNIV_I assms closed_orbit_flow0 closed_orbit_global_existence closed_orbit_in_domain fixed_point_imp_closed_orbit_period_zero(2) fixpoint_sol(2) less_irrefl local.flows_reverse periodic_orbit_def)

lemma fixed_point_imp_\<omega>_limit_set:
  assumes "x \<in> X" "f x = 0"
  shows "\<omega>_limit_set x = {x}"
proof -
  have "closed_orbit x"
    by (metis assms fixed_point_imp_closed_orbit_period_zero(1))
  from closed_orbit_\<omega>_limit_set[OF this]
  have "flow0 x ` UNIV = \<omega>_limit_set x" .
  thus ?thesis
    by (metis assms(1) assms(2) fixpoint_sol(2) image_empty image_insert image_subset_iff insertI1 rangeI subset_antisym)
qed

end

context auto_ll_on_open begin

lemma closed_orbit_eq_rev: "closed_orbit x = rev.closed_orbit x"
  unfolding closed_orbit_def rev.closed_orbit_def rev_eq_flow rev_existence_ivl_eq0
  by auto

lemma closed_orbit_\<alpha>_limit_set:
  assumes "closed_orbit x"
  shows "flow0 x ` UNIV = \<alpha>_limit_set x"
  using rev.closed_orbit_\<omega>_limit_set assms
  unfolding closed_orbit_eq_rev \<alpha>_limit_set_eq_rev flow_image_eq_rev range_uminus .

lemma fixed_point_imp_\<alpha>_limit_set:
  assumes "x \<in> X" "f x = 0"
  shows "\<alpha>_limit_set x = {x}"
  using rev.fixed_point_imp_\<omega>_limit_set assms
  unfolding \<alpha>_limit_set_eq_rev
  by auto

lemma finite_\<alpha>_limit_set_in_compact_imp_unique_fixed_point:
  assumes "compact K" "K \<subseteq> X"
  assumes "x \<in> X"  "trapped_backward x K"
  assumes "finite (\<alpha>_limit_set x)"
  obtains y where "\<alpha>_limit_set x = {y}" "f y = 0"
proof -
  from rev.finite_\<omega>_limit_set_in_compact_imp_unique_fixed_point[OF
      assms(1-5)[unfolded trapped_backward_iff_rev_trapped_forward \<alpha>_limit_set_eq_rev]]
  show ?thesis using that
    unfolding \<alpha>_limit_set_eq_rev
    by auto
qed
end

end