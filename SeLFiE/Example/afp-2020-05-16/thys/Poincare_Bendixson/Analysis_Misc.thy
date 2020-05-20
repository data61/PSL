section \<open>Additions to HOL-Analysis\<close>
theory Analysis_Misc
  imports 
    Ordinary_Differential_Equations.ODE_Analysis
begin

subsection \<open>Unsorted Lemmas (TODO: sort!)\<close>

lemma uminus_uminus_image: "uminus ` uminus ` S = S"
  for S::"'r::ab_group_add set"
  by (auto simp: image_image)

lemma in_uminus_image_iff[simp]: "x \<in> uminus ` S \<longleftrightarrow> - x \<in> S"
  for S::"'r::ab_group_add set"
  by force

lemma closed_subsegmentI:
  "w + t *\<^sub>R (z - w) \<in> {x--y}"
  if "w \<in> {x -- y}" "z \<in> {x -- y}" and t: "0 \<le> t" "t\<le> 1"
proof -
  from that obtain u v where
    w_def: "w = (1 - u) *\<^sub>R x + u *\<^sub>R y" and u: "0 \<le> u" "u \<le> 1"
    and z_def: "z = (1 - v) *\<^sub>R x + v *\<^sub>R y" and v: "0 \<le> v" "v \<le> 1"
    by (auto simp: in_segment)
  have "w + t *\<^sub>R (z - w) =
    (1 - (u - t * (u - v))) *\<^sub>R x + (u - t * (u - v)) *\<^sub>R y"
    by (simp add: algebra_simps w_def z_def)
  also have "\<dots> \<in> {x -- y}"
    unfolding closed_segment_image_interval
    apply (rule imageI)
    using t u v
    apply auto
     apply (metis (full_types) diff_0_right diff_left_mono linear mult_left_le_one_le mult_nonneg_nonpos order.trans)
    by (smt mult_left_le_one_le mult_nonneg_nonneg vector_space_over_itself.scale_right_diff_distrib)
  finally show ?thesis .
qed

lemma tendsto_minus_cancel_right: "((\<lambda>x. -g x) \<longlongrightarrow> l) F \<longleftrightarrow> (g \<longlongrightarrow> -l) F"
  \<comment> \<open>cf @{thm tendsto_minus_cancel_left}\<close>
  for g::"_ \<Rightarrow> 'b::topological_group_add"
  by (simp add: tendsto_minus_cancel_left)

lemma tendsto_nhds_continuousI: "(f \<longlongrightarrow> l) (nhds x)" if "(f \<longlongrightarrow> l) (at x)" "f x = l"
  \<comment> \<open>TODO: the assumption is continuity of f at x\<close>
proof (rule topological_tendstoI)
  fix S::"'b set" assume "open S" "l \<in> S"
  from topological_tendstoD[OF that(1) this]
  have "\<forall>\<^sub>F x in at x. f x \<in> S" .
  then show "\<forall>\<^sub>F x in nhds x. f x \<in> S"
    unfolding eventually_at_filter
    by eventually_elim (auto simp: that \<open>l \<in> S\<close>)
qed

lemma inj_composeD:
  assumes "inj (\<lambda>x. g (t x))"
  shows "inj t"
  using assms
  by (auto simp: inj_def)

lemma compact_sequentialE:
  fixes S T::"'a::first_countable_topology set"
  assumes "compact S"
  assumes "infinite T"
  assumes "T \<subseteq> S"
  obtains t::"nat \<Rightarrow> 'a" and l::'a
  where "\<And>n. t n \<in> T" "\<And>n. t n \<noteq> l" "t \<longlonglongrightarrow> l" "l \<in> S"
proof -
  from Heine_Borel_imp_Bolzano_Weierstrass[OF assms]
  obtain l where "l \<in> S" "l islimpt T" by metis
  then obtain t where "t n \<in> T" "t n \<noteq> l" "t \<longlonglongrightarrow> l" "l \<in> S" for n unfolding islimpt_sequential
    by auto
  then show ?thesis ..
qed

lemma infinite_countable_subsetE:
  fixes S::"'a set"
  assumes "infinite S"
  obtains g::"nat\<Rightarrow>'a" where "inj g" "range g \<subseteq> S"
  using assms
  by atomize_elim (simp add: infinite_countable_subset)

lemma real_quad_ge: "2 * (an * bn) \<le> an * an + bn * bn" for an bn::real
  by (sos "(((A<0 * R<1) + (R<1 * (R<1 * [an + ~1*bn]^2))))")

lemma inner_quad_ge: "2 * (a \<bullet> b) \<le> a \<bullet> a + b \<bullet> b"
  for a b::"'a::euclidean_space"\<comment> \<open>generalize?\<close>
proof -
  show ?thesis
    by (subst (1 2 3) euclidean_inner)
      (auto simp add: sum.distrib[symmetric] sum_distrib_left intro!: sum_mono real_quad_ge)
qed

lemma inner_quad_gt: "2 * (a \<bullet> b) < a \<bullet> a + b \<bullet> b"
  if "a \<noteq> b"
  for a b::"'a::euclidean_space"\<comment> \<open>generalize?\<close>
proof -
  from that obtain i where "i \<in> Basis" "a \<bullet> i \<noteq> b \<bullet> i"
    by (auto simp: euclidean_eq_iff[where 'a='a])
  then have "2 * (a \<bullet> i * (b \<bullet> i)) < a \<bullet> i * (a \<bullet> i) + b \<bullet> i * (b \<bullet> i)"
    using sum_sqs_eq[of "a\<bullet>i" "b\<bullet>i"]
    by (auto intro!: le_neq_trans real_quad_ge)
  then show ?thesis
    by (subst (1 2 3) euclidean_inner)
      (auto simp add: \<open>i \<in> Basis\<close> sum.distrib[symmetric] sum_distrib_left
        intro!: sum_strict_mono_ex1 real_quad_ge)
qed

lemma closed_segment_line_hyperplanes:
  "{a -- b} = range (\<lambda>u. a + u *\<^sub>R (b - a)) \<inter> {x. a \<bullet> (b - a) \<le> x \<bullet> (b - a) \<and> x \<bullet> (b - a) \<le> b \<bullet> (b - a)}"
  if "a \<noteq> b"
  for a b::"'a::euclidean_space"
proof safe
  fix x assume x: "x \<in> {a--b}"
  then obtain u where u: "0 \<le> u" "u \<le> 1" and x_eq: "x = a + u *\<^sub>R (b - a)"
    by (auto simp add: in_segment algebra_simps)
  show "x \<in> range (\<lambda>u. a + u *\<^sub>R (b - a))" using x_eq by auto
  have "2 * (a \<bullet> b) \<le> a \<bullet> a + b \<bullet> b"
    by (rule inner_quad_ge)
  then have "u * (2 * (a \<bullet> b) - a \<bullet> a - b \<bullet> b) \<le> 0"
    "0 \<le> (1 - u) * (a \<bullet> a + b \<bullet> b - a \<bullet> b * 2)"
    by (simp_all add: mult_le_0_iff u)
  then show " a \<bullet> (b - a) \<le> x \<bullet> (b - a)" "x \<bullet> (b - a) \<le> b \<bullet> (b - a)"
    by (auto simp: x_eq algebra_simps power2_eq_square inner_commute)
next
  fix u assume
    "a \<bullet> (b - a) \<le> (a + u *\<^sub>R (b - a)) \<bullet> (b - a)"
    "(a + u *\<^sub>R (b - a)) \<bullet> (b - a) \<le> b \<bullet> (b - a)"
  then have "0 \<le> u * ((b - a) \<bullet> (b - a))" "0 \<le> (1 - u) * ((b - a) \<bullet> (b - a))"
    by (auto simp: algebra_simps)
  then have "0 \<le> u" "u \<le> 1"
    using inner_ge_zero[of "(b - a)"] that
    by (auto simp add: zero_le_mult_iff)
  then show "a + u *\<^sub>R (b - a) \<in> {a--b}"
    by (auto simp: in_segment algebra_simps)
qed

lemma open_segment_line_hyperplanes:
  "{a <--< b} = range (\<lambda>u. a + u *\<^sub>R (b - a)) \<inter> {x. a \<bullet> (b - a) < x \<bullet> (b - a) \<and> x \<bullet> (b - a) < b \<bullet> (b - a)}"
  if "a \<noteq> b"
  for a b::"'a::euclidean_space"
proof safe
  fix x assume x: "x \<in> {a<--<b}"
  then obtain u where u: "0 < u" "u < 1" and x_eq: "x = a + u *\<^sub>R (b - a)"
    by (auto simp add: in_segment algebra_simps)
  show "x \<in> range (\<lambda>u. a + u *\<^sub>R (b - a))" using x_eq by auto
  have "2 * (a \<bullet> b) < a \<bullet> a + b \<bullet> b" using that
    by (rule inner_quad_gt)
  then have "u * (2 * (a \<bullet> b) - a \<bullet> a - b \<bullet> b) < 0"
    "0 < (1 - u) * (a \<bullet> a + b \<bullet> b - a \<bullet> b * 2)"
    by (simp_all add: mult_less_0_iff u)
  then show " a \<bullet> (b - a) < x \<bullet> (b - a)" "x \<bullet> (b - a) < b \<bullet> (b - a)"
    by (auto simp: x_eq algebra_simps power2_eq_square inner_commute)
next
  fix u assume
    "a \<bullet> (b - a) < (a + u *\<^sub>R (b - a)) \<bullet> (b - a)"
    "(a + u *\<^sub>R (b - a)) \<bullet> (b - a) < b \<bullet> (b - a)"
  then have "0 < u * ((b - a) \<bullet> (b - a))" "0 < (1 - u) * ((b - a) \<bullet> (b - a))"
    by (auto simp: algebra_simps)
  then have "0 < u" "u < 1"
    using inner_ge_zero[of "(b - a)"] that
    by (auto simp add: zero_less_mult_iff)
  then show "a + u *\<^sub>R (b - a) \<in> {a<--<b}"
    by (auto simp: in_segment algebra_simps that)
qed

lemma at_within_interior: "NO_MATCH UNIV S \<Longrightarrow> x \<in> interior S \<Longrightarrow> at x within S = at x"
  by (auto intro: at_within_interior)

lemma tendsto_at_topI:
  "(f \<longlongrightarrow> l) at_top" if "\<And>e. 0 < e \<Longrightarrow> \<exists>x0. \<forall>x\<ge>x0. dist (f x) l < e"
for f::"'a::linorder_topology \<Rightarrow> 'b::metric_space"
  using that
  apply (intro tendstoI)
  unfolding eventually_at_top_linorder
  by auto

lemma tendsto_at_topE:
  fixes f::"'a::linorder_topology \<Rightarrow> 'b::metric_space"
  assumes "(f \<longlongrightarrow> l) at_top"
  assumes "e > 0"
  obtains x0 where "\<And>x. x \<ge> x0 \<Longrightarrow> dist (f x) l < e"
proof -
  from assms(1)[THEN tendstoD, OF assms(2)]
  have "\<forall>\<^sub>F x in at_top. dist (f x) l < e" .
  then show ?thesis
    unfolding eventually_at_top_linorder
    by (auto intro: that)
qed
lemma tendsto_at_top_iff: "(f \<longlongrightarrow> l) at_top \<longleftrightarrow> (\<forall>e>0. \<exists>x0. \<forall>x\<ge>x0. dist (f x) l < e)"
  for f::"'a::linorder_topology \<Rightarrow> 'b::metric_space"
  by (auto intro!: tendsto_at_topI elim!: tendsto_at_topE)

lemma tendsto_at_top_eq_left:
  fixes f g::"'a::linorder_topology \<Rightarrow> 'b::metric_space"
  assumes "(f \<longlongrightarrow> l) at_top"
  assumes "\<And>x. x \<ge> x0 \<Longrightarrow> f x = g x"
  shows "(g \<longlongrightarrow> l) at_top"
  unfolding tendsto_at_top_iff
  by (metis (no_types, hide_lams) assms(1) assms(2) linear order_trans tendsto_at_topE)

lemma lim_divide_n: "(\<lambda>x. e / real x) \<longlonglongrightarrow> 0"
proof -
  have "(\<lambda>x. e * inverse (real x)) \<longlonglongrightarrow> 0"
    by (auto intro: tendsto_eq_intros lim_inverse_n)
  then show ?thesis by (simp add: inverse_eq_divide)
qed

definition at_top_within :: "('a::order) set \<Rightarrow> 'a filter"
  where "at_top_within s = (INF k \<in> s. principal ({k ..} \<inter> s)) "

lemma at_top_within_at_top[simp]:
  shows "at_top_within UNIV = at_top"
  unfolding at_top_within_def at_top_def
  by (auto)

lemma at_top_within_empty[simp]:
  shows "at_top_within {} = top"
  unfolding at_top_within_def
  by (auto)

definition "nhds_set X = (INF S\<in>{S. open S \<and> X \<subseteq> S}. principal S)"

lemma eventually_nhds_set:
  "(\<forall>\<^sub>F x in nhds_set X. P x) \<longleftrightarrow> (\<exists>S. open S \<and> X \<subseteq> S \<and> (\<forall>x\<in>S. P x))"
  unfolding nhds_set_def by (subst eventually_INF_base) (auto simp: eventually_principal)

term "filterlim f (nhds_set (frontier X)) F" \<comment> \<open>f tends to the boundary of X?\<close>


text \<open>somewhat inspired by @{thm islimpt_range_imp_convergent_subsequence} and its dependencies.
The class constraints seem somewhat arbitrary, perhaps this can be generalized in some way.
\<close>
lemma limpt_closed_imp_exploding_subsequence:\<comment>\<open>TODO: improve name?!\<close>
  fixes f::"'a::{heine_borel,real_normed_vector} \<Rightarrow> 'b::{first_countable_topology, t2_space}"
  assumes cont[THEN continuous_on_compose2, continuous_intros]: "continuous_on T f"
  assumes closed: "closed T"
  assumes bound: "\<And>t. t \<in> T \<Longrightarrow> f t \<noteq> l"
  assumes limpt: "l islimpt (f ` T)"
  obtains s where
    "(f \<circ> s) \<longlonglongrightarrow> l"
    "\<And>i. s i \<in> T"
    "\<And>C. compact C \<Longrightarrow> C \<subseteq> T \<Longrightarrow> \<forall>\<^sub>F i in sequentially. s i \<notin> C"
proof -
  from countable_basis_at_decseq[of l]
  obtain A where A: "\<And>i. open (A i)" "\<And>i. l \<in> A i"
    and evA: "\<And>S. open S \<Longrightarrow> l \<in> S \<Longrightarrow> eventually (\<lambda>i. A i \<subseteq> S) sequentially"
    by blast

  from closed_Union_compact_subsets[OF closed]
  obtain C
    where C: "(\<And>n. compact (C n))" "(\<And>n. C n \<subseteq> T)" "(\<And>n. C n \<subseteq> C (Suc n))" "\<Union> (range C) = T"
      and evC: "(\<And>K. compact K \<Longrightarrow> K \<subseteq> T \<Longrightarrow> \<forall>\<^sub>F i in sequentially. K \<subseteq> C i)"
    by (metis eventually_sequentially)

  have AC: "l \<in> A i - f ` C i" "open (A i - f ` C i)" for i
    using C bound
    by (fastforce intro!: open_Diff A compact_imp_closed compact_continuous_image continuous_intros)+

  from islimptE[OF limpt AC] have "\<exists>t\<in>T. f t \<in> A i - f ` C i \<and> f t \<noteq> l" for i by blast  
  then obtain t where t: "\<And>i. t i \<in> T" "\<And>i. f (t i) \<in> A i - f ` C i" "\<And>i. f (t i) \<noteq> l"
    by metis

  have "(f o t) \<longlonglongrightarrow> l"
    using t
    by (auto intro!: topological_tendstoI dest!: evA elim!: eventually_mono)
  moreover
  have "\<And>i. t i \<in> T" by fact
  moreover
  have "\<forall>\<^sub>F i in sequentially. t i \<notin> K" if "compact K" "K \<subseteq> T" for K
    using evC[OF that]
    by eventually_elim (use t in auto)
  ultimately show ?thesis ..
qed  

lemma Inf_islimpt: "bdd_below S \<Longrightarrow> Inf S \<notin> S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> Inf S islimpt S" for S::"real set"
  by (auto simp: islimpt_in_closure intro!: closure_contains_Inf)

context linorder
begin

text \<open>HOL-analysis doesn't seem to have these, maybe they were never needed.
  Some variants are around @{thm Int_atLeastAtMost}, but with old-style naming conventions.
  Change to the "modern" I.. convention there?\<close>

lemma Int_Ico[simp]:
  shows "{a..} \<inter> {b..} = {max a b ..}"
  by (auto)

lemma Int_Ici_Ico[simp]:
  shows "{a..} \<inter> {b..<c} = {max a b ..<c}"
  by auto

lemma Int_Ico_Ici[simp]:
  shows "{a..<c} \<inter> {b..} = {max a b ..<c}"
  by auto

lemma subset_Ico_iff[simp]:
  "{a..<b} \<subseteq> {c..<b} \<longleftrightarrow> b \<le> a \<or> c \<le> a"
  unfolding atLeastLessThan_def
  by auto

lemma Ico_subset_Ioo_iff[simp]:
  "{a..<b} \<subseteq> {c<..<b} \<longleftrightarrow> b \<le> a \<or> c < a"
  unfolding greaterThanLessThan_def atLeastLessThan_def
  by auto

lemma Icc_Un_Ici[simp]:
  shows "{a..b} \<union> {b..} = {min a b..}"
  unfolding atLeastAtMost_def atLeast_def atMost_def min_def
  by auto

end

lemma at_top_within_at_top_unbounded_right:
  fixes a::"'a::linorder"
  shows "at_top_within {a..} = at_top"
  unfolding at_top_within_def at_top_def
  apply (auto intro!: INF_eq)
  by (metis linorder_class.linear linorder_class.max.cobounded1 linorder_class.max.idem ord_class.atLeast_iff)

lemma at_top_within_at_top_unbounded_rightI:
  fixes a::"'a::linorder"
  assumes "{a..} \<subseteq> s"
  shows "at_top_within s = at_top"
  unfolding at_top_within_def at_top_def
  apply (auto intro!: INF_eq)
   apply (meson Ici_subset_Ioi_iff Ioi_le_Ico assms dual_order.refl dual_order.trans leI)
  by (metis assms atLeast_iff atLeast_subset_iff inf.cobounded1 linear subsetD)

lemma at_top_within_at_top_bounded_right:
  fixes a b::"'a::{dense_order,linorder_topology}"
  assumes "a < b"
  shows "at_top_within {a..<b} = at_left b"
  unfolding at_top_within_def at_left_eq[OF assms(1)]
  apply (auto intro!: INF_eq)
   apply (smt atLeastLessThan_iff greaterThanLessThan_iff le_less lessThan_iff max.absorb1 subset_eq)
  by (metis assms atLeastLessThan_iff dense linear max.absorb1 not_less order_trans)

lemma at_top_within_at_top_bounded_right':
  fixes a b::"'a::{dense_order,linorder_topology}"
  assumes "a < b"
  shows "at_top_within {..<b} = at_left b"
  unfolding at_top_within_def at_left_eq[OF assms(1)]
  apply (auto intro!: INF_eq)
   apply (meson atLeast_iff greaterThanLessThan_iff le_less lessThan_iff subset_eq)
  by (metis Ico_subset_Ioo_iff atLeastLessThan_def dense lessThan_iff)

lemma eventually_at_top_within_linorder:
  assumes sn:"s \<noteq> {}"
  shows "eventually P (at_top_within s) \<longleftrightarrow> (\<exists>x0::'a::{linorder_topology} \<in> s. \<forall>x \<ge> x0. x\<in> s \<longrightarrow> P x)"
  unfolding at_top_within_def
  apply (subst eventually_INF_base)
    apply (auto simp:eventually_principal sn)
  by (metis atLeast_subset_iff inf.coboundedI2 inf_commute linear)

lemma tendsto_at_top_withinI:
  fixes f::"'a::linorder_topology \<Rightarrow> 'b::metric_space"
  assumes "s \<noteq> {}"
  assumes "\<And>e. 0 < e \<Longrightarrow> \<exists>x0 \<in> s. \<forall>x \<in> {x0..} \<inter> s. dist (f x) l < e"
  shows  "(f \<longlongrightarrow> l) (at_top_within s)"
  apply(intro tendstoI)
  unfolding at_top_within_def apply (subst eventually_INF_base)
    apply (auto simp:eventually_principal assms)
  by (metis atLeast_subset_iff inf.coboundedI2 inf_commute linear)

lemma tendsto_at_top_withinE:
  fixes f::"'a::linorder_topology \<Rightarrow> 'b::metric_space"
  assumes "s \<noteq> {}"
  assumes "(f \<longlongrightarrow> l) (at_top_within s)"
  assumes "e > 0"
  obtains x0 where "x0 \<in> s" "\<And>x. x \<in> {x0..} \<inter> s \<Longrightarrow> dist (f x) l < e"
proof -
  from assms(2)[THEN tendstoD, OF assms(3)]
  have "\<forall>\<^sub>F x in at_top_within s. dist (f x) l < e" .
  then show ?thesis unfolding eventually_at_top_within_linorder[OF \<open>s \<noteq> {}\<close>] 
    by (auto intro: that)
qed

lemma tendsto_at_top_within_iff:
  fixes f::"'a::linorder_topology \<Rightarrow> 'b::metric_space"
  assumes "s \<noteq> {}"
  shows "(f \<longlongrightarrow> l) (at_top_within s) \<longleftrightarrow> (\<forall>e>0. \<exists>x0 \<in> s. \<forall>x \<in> {x0..} \<inter> s. dist (f x) l < e)"
  by (auto intro!: tendsto_at_top_withinI[OF \<open>s \<noteq> {}\<close>] elim!: tendsto_at_top_withinE[OF \<open>s \<noteq> {}\<close>])

lemma filterlim_at_top_at_top_within_bounded_right:
  fixes a b::"'a::{dense_order,linorder_topology}"
  fixes f::"'a \<Rightarrow> real"
  assumes "a < b"
  shows "filterlim f at_top (at_top_within {..<b}) = (f \<longlongrightarrow> \<infinity>) (at_left b)"
  unfolding filterlim_at_top_dense
    at_top_within_at_top_bounded_right'[OF assms(1)]
    eventually_at_left[OF assms(1)]
    tendsto_PInfty
  by auto

text \<open>Extract a sequence (going to infinity) bounded away from l\<close>

lemma not_tendsto_frequentlyE:
  assumes "\<not>((f \<longlongrightarrow> l) F)"
  obtains S where "open S" "l \<in> S" "\<exists>\<^sub>F x in F. f x \<notin> S"
  using assms
  by (auto simp: tendsto_def not_eventually)

lemma not_tendsto_frequently_metricE:
  assumes "\<not>((f \<longlongrightarrow> l) F)"
  obtains e where "e > 0" "\<exists>\<^sub>F x in F. e \<le> dist (f x) l"
  using assms
  by (auto simp: tendsto_iff not_eventually not_less)

lemma eventually_frequently_conj: "frequently P F \<Longrightarrow> eventually Q F \<Longrightarrow> frequently (\<lambda>x. P x \<and> Q x) F"
  unfolding frequently_def
  apply (erule contrapos_nn)
  subgoal premises prems
    using prems by eventually_elim auto
  done

lemma frequently_at_top:
  "(\<exists>\<^sub>F t in at_top. P t) \<longleftrightarrow> (\<forall>t0. \<exists>t>t0. P t)"
  for P::"'a::{linorder,no_top}\<Rightarrow>bool" 
  by (auto simp: frequently_def eventually_at_top_dense)

lemma frequently_at_topE:
  fixes P::"nat \<Rightarrow> 'a::{linorder,no_top}\<Rightarrow>_"
  assumes freq[rule_format]: "\<forall>n. \<exists>\<^sub>F a in at_top. P n a"
  obtains s::"nat\<Rightarrow>'a"
  where "\<And>i. P i (s i)" "strict_mono s"
proof -
  have "\<exists>f. \<forall>n. P n (f n) \<and> f n < f (Suc n)"
  proof (rule dependent_nat_choice)
    from frequently_ex[OF freq[of 0]] show "\<exists>x. P 0 x" .
    fix x n assume "P n x"
    from freq[unfolded frequently_at_top, rule_format, of x "Suc n"]
    obtain y where "P (Suc n) y" "y > x" by auto
    then show "\<exists>y. P (Suc n) y \<and> x < y"
      by auto
  qed
  then obtain s where "\<And>i. P i (s i)" "strict_mono s"
    unfolding strict_mono_Suc_iff by auto
  then show ?thesis ..
qed

lemma frequently_at_topE':
  fixes P::"nat \<Rightarrow> 'a::{linorder,no_top}\<Rightarrow>_"
  assumes freq[rule_format]: "\<forall>n. \<exists>\<^sub>F a in at_top. P n a"
    and g: "filterlim g at_top sequentially"
  obtains s::"nat\<Rightarrow>'a"
  where "\<And>i. P i (s i)" "strict_mono s" "\<And>n. g n \<le> s n"
proof -
  have "\<forall>n. \<exists>\<^sub>F a in at_top. P n a \<and> g n \<le> a"
    using freq
    by (auto intro!: eventually_frequently_conj)
  from frequently_at_topE[OF this] obtain s where "\<And>i. P i (s i)" "strict_mono s" "\<And>n. g n \<le> s n"
    by metis
  then show ?thesis ..
qed

lemma frequently_at_top_at_topE:
  fixes P::"nat \<Rightarrow> 'a::{linorder,no_top}\<Rightarrow>_" and g::"nat\<Rightarrow>'a"
  assumes "\<forall>n. \<exists>\<^sub>F a in at_top. P n a" "filterlim g at_top sequentially"
  obtains s::"nat\<Rightarrow>'a"
  where "\<And>i. P i (s i)" "filterlim s at_top sequentially"
proof -
  from frequently_at_topE'[OF assms]
  obtain s where s: "(\<And>i. P i (s i))" "strict_mono s" "(\<And>n. g n \<le> s n)" by blast
  have s_at_top: "filterlim s at_top sequentially"
    by (rule filterlim_at_top_mono) (use assms s in auto)
  with s(1) show ?thesis ..
qed

(* Extract a strict monotone and sequence converging to something other than l *)
lemma not_tendsto_convergent_seq:
  fixes f::"real \<Rightarrow> 'a::metric_space"
  assumes X: "compact (X::'a set)"
  assumes im: "\<And>x. x \<ge> 0 \<Longrightarrow> f x \<in> X"
  assumes nl: "\<not> ((f \<longlongrightarrow> (l::'a)) at_top)"
  obtains s k where
    "k \<in> X" "k \<noteq> l" "(f \<circ> s) \<longlonglongrightarrow> k" "strict_mono s" "\<forall>n. s n \<ge> n"
proof -
  from not_tendsto_frequentlyE[OF nl]
  obtain S where "open S" "l \<in> S" "\<exists>\<^sub>F x in at_top. f x \<notin> S" .
  have "\<forall>n. \<exists>\<^sub>F x in at_top. f x \<notin> S \<and> real n \<le> x"
    apply (rule allI)
    apply (rule eventually_frequently_conj)
     apply fact
    by (rule eventually_ge_at_top)
  from frequently_at_topE[OF this]
  obtain s where "\<And>i. f (s i) \<notin> S" and s: "strict_mono s" and s_ge: "(\<And>i. real i \<le> s i)" by metis
  then have "0 \<le> s i" for i using dual_order.trans of_nat_0_le_iff by blast
  then have "\<forall>n. (f \<circ> s) n \<in> X" using im by auto
  from X[unfolded compact_def, THEN spec, THEN mp, OF this]
  obtain k r where k: "k \<in> X" and r: "strict_mono r" and kLim: "(f \<circ> s \<circ> r) \<longlonglongrightarrow> k" by metis
  have "k \<in> X - S"
    by (rule Lim_in_closed_set[of "X - S", OF _ _ _ kLim])
      (auto simp: im \<open>0 \<le> s _\<close>  \<open>\<And>i. f (s i) \<notin> S\<close> intro!: \<open>open S\<close> X intro: compact_imp_closed)

  note k
  moreover have "k \<noteq> l" using \<open>k \<in> X - S\<close> \<open>l \<in> S\<close> by auto
  moreover have "(f \<circ> (s \<circ> r)) \<longlonglongrightarrow> k" using kLim by (simp add: o_assoc)
  moreover have "strict_mono (s \<circ> r)" using s r by (rule strict_mono_o)
  moreover have "\<forall>n. (s \<circ> r) n \<ge> n" using s_ge r
    by (metis comp_apply dual_order.trans of_nat_le_iff seq_suble)
  ultimately show ?thesis ..
qed

lemma harmonic_bound:
  shows "1 / 2 ^(Suc n) < 1 / real (Suc n)"
proof (induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case
    by (smt frac_less2 of_nat_0_less_iff of_nat_less_two_power zero_less_Suc)
qed

lemma INF_bounded_imp_convergent_seq:
  fixes f::"real \<Rightarrow> real"
  assumes cont: "continuous_on {a..} f"
  assumes bound: "\<And>t. t \<ge> a \<Longrightarrow> f t > l"
  assumes inf: "(INF t\<in>{a..}. f t) = l"
  obtains s where
    "(f \<circ> s) \<longlonglongrightarrow> l"
    "\<And>i. s i \<in> {a..}"
    "filterlim s at_top sequentially"
proof -
  have bound': "t \<in> {a..} \<Longrightarrow> f t \<noteq> l" for t using bound[of t] by auto
  have limpt: "l islimpt f ` {a..}"
  proof -
    have "Inf (f ` {a..}) islimpt f ` {a..}"
      by (rule Inf_islimpt) (auto simp: inf intro!: bdd_belowI2[where m=l] dest: bound)
    then show ?thesis by (simp add: inf)
  qed
  from limpt_closed_imp_exploding_subsequence[OF cont closed_atLeast bound' limpt]
  obtain s where s: "(f \<circ> s) \<longlonglongrightarrow> l"
    "\<And>i. s i \<in> {a..}"
    "compact C \<Longrightarrow> C \<subseteq> {a..} \<Longrightarrow> \<forall>\<^sub>F i in sequentially. s i \<notin> C" for C
    by metis
  have "\<forall>\<^sub>F i in sequentially. s i \<ge> n" for n
    using s(3)[of "{a..n}"] s(2)
    by (auto elim!: eventually_mono)
  then have "filterlim s at_top sequentially"
    unfolding filterlim_at_top
    by auto
  from s(1) s(2) this
  show ?thesis ..
qed

(* Generalizes to other combinations of strict_mono and filterlim *)
lemma filterlim_at_top_strict_mono:
  fixes s :: "_ \<Rightarrow> 'a::linorder"
  fixes r :: "nat \<Rightarrow> _"
  assumes "strict_mono s"
  assumes "strict_mono r"
  assumes "filterlim s at_top F"
  shows "filterlim (s \<circ> r) at_top F"
  apply (rule filterlim_at_top_mono[OF assms(3)])
  by (simp add: assms(1) assms(2) seq_suble strict_mono_leD)

lemma LIMSEQ_lb:
  assumes fl: "s \<longlonglongrightarrow> (l::real)"
  assumes u: "l < u"
  shows "\<exists>n0. \<forall>n\<ge>n0. s n < u"
proof -
  from fl have "\<exists>no>0. \<forall>n\<ge>no. dist (s n) l < u-l" unfolding LIMSEQ_iff_nz using u
    by simp
  thus ?thesis using dist_real_def by fastforce
qed

(* Used to sharpen a tendsto with additional information*)
lemma filterlim_at_top_choose_lower:
  assumes "filterlim s at_top sequentially"
  assumes "(f \<circ> s) \<longlonglongrightarrow> l"
  obtains t where
    "filterlim t at_top sequentially"
    "(f \<circ> t) \<longlonglongrightarrow> l"
    "\<forall>n. t n \<ge> (b::real)"
proof -
  obtain k where k: "\<forall>n \<ge> k. s n \<ge> b" using assms(1)
    unfolding filterlim_at_top eventually_sequentially by blast
  define t where "t = (\<lambda>n. s (n+k))"
  then have "\<forall>n. t n \<ge> b" using k by simp
  have "filterlim t at_top sequentially" using assms(1)
    unfolding filterlim_at_top eventually_sequentially t_def
    by (metis (full_types) add.commute trans_le_add2)
  from LIMSEQ_ignore_initial_segment[OF assms(2), of "k"]
  have "(\<lambda>n. (f \<circ> s) (n + k)) \<longlonglongrightarrow> l" .
  then have "(f \<circ> t) \<longlonglongrightarrow> l" unfolding t_def o_def by simp
  show ?thesis
    using \<open>(f \<circ> t) \<longlonglongrightarrow> l\<close> \<open>\<forall>n. b \<le> t n\<close> \<open>filterlim t at_top sequentially\<close> that by blast
qed

lemma frequently_at_top_realE:
  fixes P::"nat \<Rightarrow> real \<Rightarrow> bool"
  assumes "\<forall>n. \<exists>\<^sub>F t in at_top. P n t"
  obtains s::"nat\<Rightarrow>real"
  where "\<And>i. P i (s i)" "filterlim s at_top at_top"
  by (metis assms frequently_at_top_at_topE[OF _ filterlim_real_sequentially])

lemma approachable_sequenceE:
  fixes f::"real \<Rightarrow> 'a::metric_space"
  assumes "\<And>t e. 0 \<le> t \<Longrightarrow> 0 < e \<Longrightarrow> \<exists>tt\<ge>t. dist (f tt) p < e"
  obtains s where "filterlim s at_top sequentially" "(f \<circ> s) \<longlonglongrightarrow> p"
proof -
  have "\<forall>n. \<exists>\<^sub>F i in at_top. dist (f i) p < 1/real (Suc n)"
    unfolding frequently_at_top
    apply (auto )
    subgoal for n m
      using assms[of "max 0 (m+1)" "1/(Suc n)"]
      by force
    done
  from frequently_at_top_realE[OF this]
  obtain s where s: "\<And>i. dist (f (s i)) p < 1 / real (Suc i)" "filterlim s at_top sequentially"
    by metis
  note this(2)
  moreover
  have "(f o s) \<longlonglongrightarrow> p"
  proof (rule tendstoI)
    fix e::real assume "e > 0"
    have "\<forall>\<^sub>F i in sequentially. 1 / real (Suc i) < e"
      apply (rule order_tendstoD[OF _ \<open>0 < e\<close>])
      apply (rule real_tendsto_divide_at_top)
       apply (rule tendsto_intros)
      by (rule filterlim_compose[OF filterlim_real_sequentially filterlim_Suc])
    then show "\<forall>\<^sub>F x in sequentially. dist ((f \<circ> s) x) p < e"
      by eventually_elim (use dual_order.strict_trans s \<open>e > 0\<close> in auto)
  qed
  ultimately show ?thesis ..
qed

lemma mono_inc_bdd_above_has_limit_at_topI:
  fixes f::"real \<Rightarrow> real"
  assumes "mono f"
  assumes "\<And>x. f x \<le> u"
  shows "\<exists>l. (f \<longlongrightarrow> l) at_top"
proof -
  define l where "l = Sup (range (\<lambda>n. f (real n)))"
  have t:"(\<lambda>n. f (real n)) \<longlonglongrightarrow> l" unfolding l_def
    apply (rule LIMSEQ_incseq_SUP)
     apply (meson assms(2) bdd_aboveI2)
    by (meson assms(1) mono_def of_nat_mono)
  from tendsto_at_topI_sequentially_real[OF assms(1) t]
  have "(f \<longlongrightarrow> l) at_top" .
  thus ?thesis by blast  
qed

lemma gen_mono_inc_bdd_above_has_limit_at_topI:
  fixes f::"real \<Rightarrow> real"
  assumes "\<And>x y. x \<ge> b \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
  assumes "\<And>x. x \<ge> b \<Longrightarrow> f x \<le> u"
  shows "\<exists>l. (f \<longlongrightarrow> l) at_top"
proof -
  define ff where "ff = (\<lambda>x. if x \<ge> b then f x else f b)"
  have m1:"mono ff" unfolding ff_def mono_def using assms(1) by simp
  have m2:"\<And>x. ff x \<le> u" unfolding ff_def using assms(2) by simp
  from mono_inc_bdd_above_has_limit_at_topI[OF m1 m2]
  obtain l where "(ff \<longlongrightarrow> l) at_top" by blast
  thus ?thesis
    by (meson \<open>(ff \<longlongrightarrow> l) at_top\<close> ff_def tendsto_at_top_eq_left)
qed

lemma gen_mono_dec_bdd_below_has_limit_at_topI:
  fixes f::"real \<Rightarrow> real"
  assumes "\<And>x y. x \<ge> b \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<ge> f y"
  assumes "\<And>x. x \<ge> b \<Longrightarrow> f x \<ge> u"
  shows "\<exists>l. (f \<longlongrightarrow> l) at_top"
proof -
  define ff where "ff = (\<lambda>x. if x \<ge> b then f x else f b)"
  have m1:"mono (-ff)" unfolding ff_def mono_def using assms(1) by simp
  have m2:"\<And>x. (-ff) x \<le> -u" unfolding ff_def using assms(2) by simp
  from mono_inc_bdd_above_has_limit_at_topI[OF m1 m2]
  obtain l where "(-ff \<longlongrightarrow> l) at_top" by blast
  then have "(ff \<longlongrightarrow> -l) at_top"
    using tendsto_at_top_eq_left tendsto_minus_cancel_left by fastforce  
  thus ?thesis
    by (meson \<open>(ff \<longlongrightarrow> -l) at_top\<close> ff_def tendsto_at_top_eq_left)
qed

lemma infdist_closed:
  shows "closed ({z. infdist z S \<ge> e})"
  by (auto intro!:closed_Collect_le simp add:continuous_on_infdist)

(* TODO: this is a copy of LIMSEQ_norm_0 where the sequence
  is bounded above in norm by a geometric series *)
lemma LIMSEQ_norm_0_pow:
  assumes "k > 0" "b > 1"
  assumes  "\<And>n::nat. norm (s n) \<le> k / b^n"
  shows "s \<longlonglongrightarrow> 0"
proof (rule metric_LIMSEQ_I)
  fix e
  assume "e > (0::real)"
  then have "k / e > 0" using assms(1) by auto
  obtain N where N: "b^(N::nat) > k / e" using assms(2)
    using real_arch_pow by blast
  then have "norm (s n) < e" if "n \<ge> N" for n
  proof -
    have "k / b^n \<le> k / b^N"
      by (smt assms(1) assms(2) frac_le leD power_less_imp_less_exp that zero_less_power)
    also have " ... < e" using N
      by (metis \<open>0 < e\<close> assms(2) less_trans mult.commute pos_divide_less_eq zero_less_one zero_less_power)
    finally show ?thesis
      by (meson assms less_eq_real_def not_le order_trans)
  qed
  then show "\<exists>no. \<forall>n\<ge>no. dist (s n) 0 < e"
    by auto
qed

lemma filterlim_apply_filtermap:
  assumes g: "filterlim g G F"
  shows "filterlim (\<lambda>x. m (g x)) (filtermap m G) F"
  by (metis filterlim_def filterlim_filtermap filtermap_mono g)

lemma eventually_at_right_field_le:
  "eventually P (at_right x) \<longleftrightarrow> (\<exists>b>x. \<forall>y>x. y \<le> b \<longrightarrow> P y)"
  for x :: "'a::{linordered_field, linorder_topology}"
  by (smt dense eventually_at_right_field le_less_trans less_le_not_le order.strict_trans1)

subsection \<open>indexing euclidean space with natural numbers\<close>

definition  nth_eucl :: "'a::executable_euclidean_space \<Rightarrow> nat \<Rightarrow> real" where
  "nth_eucl x i = x \<bullet> (Basis_list ! i)"
  \<comment> \<open>TODO: why is that and some sort of \<open>lambda_eucl\<close> nowhere available?\<close>
definition lambda_eucl :: "(nat \<Rightarrow> real) \<Rightarrow> 'a::executable_euclidean_space" where
  "lambda_eucl (f::nat\<Rightarrow>real) = (\<Sum>i<DIM('a). f i *\<^sub>R Basis_list ! i)"

lemma eucl_eq_iff: "x = y \<longleftrightarrow> (\<forall>i<DIM('a). nth_eucl x i = nth_eucl y i)"
  for x y::"'a::executable_euclidean_space"
  apply (auto simp: nth_eucl_def euclidean_eq_iff[where 'a='a])
  by (metis eucl_of_list_list_of_eucl list_of_eucl_eq_iff)

bundle eucl_notation begin
notation nth_eucl (infixl "$\<^sub>e" 90)
end
bundle no_eucl_notation begin
no_notation nth_eucl (infixl "$\<^sub>e" 90)
end

unbundle eucl_notation

lemma eucl_of_list_eucl_nth:
  "(eucl_of_list xs::'a) $\<^sub>e i = xs ! i"
  if "length xs = DIM('a::executable_euclidean_space)"
    "i < DIM('a)"
  using that
  apply (auto simp: nth_eucl_def)
  by (metis list_of_eucl_eucl_of_list list_of_eucl_nth)

lemma eucl_of_list_inner:
  "(eucl_of_list xs::'a) \<bullet> eucl_of_list ys = (\<Sum>(x,y)\<leftarrow>zip xs ys. x * y)"
  if "length xs = DIM('a::executable_euclidean_space)"
    "length ys = DIM('a::executable_euclidean_space)"
  using that
  by (auto simp: nth_eucl_def eucl_of_list_inner_eq inner_lv_rel_def)

lemma self_eq_eucl_of_list: "x = eucl_of_list (map (\<lambda>i. x $\<^sub>e i) [0..<DIM('a)])"
  for x::"'a::executable_euclidean_space"
  by (auto simp: eucl_eq_iff[where 'a='a] eucl_of_list_eucl_nth)

lemma inner_nth_eucl: "x \<bullet> y = (\<Sum>i<DIM('a). x $\<^sub>e i * y $\<^sub>e i)"
  for x y::"'a::executable_euclidean_space"
  apply (subst self_eq_eucl_of_list[where x=x])
  apply (subst self_eq_eucl_of_list[where x=y])
  apply (subst eucl_of_list_inner)
  by (auto simp: map2_map_map atLeast_upt interv_sum_list_conv_sum_set_nat)

lemma norm_nth_eucl: "norm x = L2_set (\<lambda>i. x $\<^sub>e i) {..<DIM('a)}"
  for x::"'a::executable_euclidean_space"
  unfolding norm_eq_sqrt_inner inner_nth_eucl L2_set_def
  by (auto simp: power2_eq_square)


lemma plus_nth_eucl: "(x + y) $\<^sub>e i = x $\<^sub>e i + y $\<^sub>e i"
  and minus_nth_eucl: "(x - y) $\<^sub>e i = x $\<^sub>e i - y $\<^sub>e i"
  and uminus_nth_eucl: "(-x) $\<^sub>e i = - x $\<^sub>e i"
  and scaleR_nth_eucl: "(c *\<^sub>R x) $\<^sub>e i = c *\<^sub>R (x $\<^sub>e i)"
  by (auto simp: nth_eucl_def algebra_simps)

lemma inf_nth_eucl: "inf x y $\<^sub>e i = min (x $\<^sub>e i) (y $\<^sub>e i)"
  if "i < DIM('a)"
  for x::"'a::executable_euclidean_space"
  by (auto simp: nth_eucl_def algebra_simps inner_Basis_inf_left that inf_min)
lemma sup_nth_eucl: "sup x y $\<^sub>e i = max (x $\<^sub>e i) (y $\<^sub>e i)"
  if "i < DIM('a)"
  for x::"'a::executable_euclidean_space"
  by (auto simp: nth_eucl_def algebra_simps inner_Basis_sup_left that sup_max)

lemma le_iff_le_nth_eucl: "x \<le> y \<longleftrightarrow> (\<forall>i<DIM('a). (x $\<^sub>e i) \<le> (y $\<^sub>e i))"
  for x::"'a::executable_euclidean_space"
  apply (auto simp: nth_eucl_def algebra_simps eucl_le[where 'a='a])
  by (meson eucl_le eucl_le_Basis_list_iff)

lemma eucl_less_iff_less_nth_eucl: "eucl_less x y \<longleftrightarrow> (\<forall>i<DIM('a). (x $\<^sub>e i) < (y $\<^sub>e i))"
  for x::"'a::executable_euclidean_space"
  apply (auto simp: nth_eucl_def algebra_simps eucl_less_def[where 'a='a])
  by (metis Basis_zero eucl_eq_iff inner_not_same_Basis inner_zero_left length_Basis_list
      nth_Basis_list_in_Basis nth_eucl_def)

lemma continuous_on_nth_eucl[continuous_intros]:
  "continuous_on X (\<lambda>x. f x $\<^sub>e i)"
  if "continuous_on X f"
  by (auto simp: nth_eucl_def intro!: continuous_intros that)


subsection \<open>derivatives\<close>

lemma eventually_at_ne[intro, simp]: "\<forall>\<^sub>F x in at x0. x \<noteq> x0"
  by (auto simp: eventually_at_filter)

lemma has_vector_derivative_withinD:
  fixes f::"real \<Rightarrow> 'b::euclidean_space"
  assumes "(f has_vector_derivative f') (at x0 within S)"
  shows "((\<lambda>x. (f x - f x0) /\<^sub>R (x - x0)) \<longlongrightarrow> f') (at x0 within S)"
  apply (rule LIM_zero_cancel)
  apply (rule tendsto_norm_zero_cancel)
  apply (rule Lim_transform_eventually)
proof -
  show "\<forall>\<^sub>F x in at x0 within S. norm ((f x - f x0 - (x - x0) *\<^sub>R f') /\<^sub>R norm (x - x0)) =
    norm ((f x - f x0) /\<^sub>R (x - x0) - f')"
    (is "\<forall>\<^sub>F x in _. ?th x")
    unfolding eventually_at_filter
  proof (safe intro!: eventuallyI)
    fix x assume x: "x \<noteq> x0"
    then have "norm ((f x - f x0) /\<^sub>R (x - x0) - f') = norm (sgn (x - x0) *\<^sub>R ((f x - f x0) /\<^sub>R (x - x0) - f'))"
      by simp
    also have "sgn (x - x0) *\<^sub>R ((f x - f x0) /\<^sub>R (x - x0) - f') = ((f x - f x0) /\<^sub>R norm (x - x0) - (x - x0) *\<^sub>R f' /\<^sub>R norm (x - x0))"
      by (auto simp add: algebra_simps sgn_div_norm divide_simps)
        (metis add.commute add_divide_distrib diff_add_cancel scaleR_add_left)
    also have "\<dots> = (f x - f x0 - (x - x0) *\<^sub>R f') /\<^sub>R norm (x - x0)" by (simp add: algebra_simps)
    finally show "?th x" ..
  qed
  show "((\<lambda>x. norm ((f x - f x0 - (x - x0) *\<^sub>R f') /\<^sub>R norm (x - x0))) \<longlongrightarrow> 0) (at x0 within S)"
    by (rule tendsto_norm_zero)
      (use assms in \<open>auto simp: has_vector_derivative_def has_derivative_at_within\<close>)
qed

text \<open>A \<open>path_connected\<close> set \<open>S\<close> entering both \<open>T\<close> and \<open>-T\<close>
      must cross the frontier of \<open>T\<close> \<close>
lemma path_connected_frontier:
  fixes S :: "'a::real_normed_vector set"
  assumes "path_connected S"
  assumes "S \<inter> T \<noteq> {}"
  assumes "S \<inter> -T \<noteq> {}"
  obtains s where "s \<in> S" "s \<in> frontier T"
proof -
  obtain st where st:"st \<in> S \<inter> T" using assms(2) by blast
  obtain sn where sn:"sn \<in> S \<inter> -T" using assms(3) by blast
  obtain g where g: "path g" "path_image g \<subseteq> S"
    "pathstart g = st" "pathfinish g = sn"
    using assms(1) st sn unfolding path_connected_def by blast
  have a1:"pathstart g \<in> closure T" using st g(3) closure_Un_frontier by fastforce
  have a2:"pathfinish g \<notin> T" using sn g(4) by auto
  from exists_path_subpath_to_frontier[OF g(1) a1 a2]
  obtain h where "path_image h \<subseteq> path_image g" "pathfinish h \<in> frontier T" by metis
  thus ?thesis using g(2)
    by (meson in_mono pathfinish_in_path_image that) 
qed

lemma path_connected_not_frontier_subset:
  fixes S :: "'a::real_normed_vector set"
  assumes "path_connected S"
  assumes "S \<inter> T \<noteq> {}"
  assumes "S \<inter> frontier T = {}"
  shows "S \<subseteq> T"
  using path_connected_frontier assms by auto  

lemma compact_attains_bounds:
  fixes f::"'a::topological_space \<Rightarrow> 'b::linorder_topology"
  assumes compact: "compact S"
  assumes ne: "S \<noteq> {}"
  assumes cont: "continuous_on S f"
  obtains l u where "l \<in> S" "u \<in> S" "\<And>x. x \<in> S \<Longrightarrow> f x \<in> {f l .. f u}"
proof -
  from compact_continuous_image[OF cont compact]
  have compact_image: "compact (f ` S)" .
  have ne_image: "f ` S \<noteq> {}" using ne by simp
  from compact_attains_inf[OF compact_image ne_image]
  obtain l where "l \<in> S" "\<And>x. x \<in> S \<Longrightarrow> f l \<le> f x" by auto
  moreover
  from compact_attains_sup[OF compact_image ne_image]
  obtain u where "u \<in> S" "\<And>x. x \<in> S \<Longrightarrow> f x \<le> f u" by auto
  ultimately
  have "l \<in> S" "u \<in> S" "\<And>x. x \<in> S \<Longrightarrow> f x \<in> {f l .. f u}" by auto
  then show ?thesis ..
qed

lemma uniform_limit_const[uniform_limit_intros]:
  "uniform_limit S (\<lambda>x y. f x) (\<lambda>_. l) F" if "(f \<longlongrightarrow> l) F"
  apply (auto simp: uniform_limit_iff)
  subgoal for e
    using tendstoD[OF that(1), of e]
    by (auto simp: eventually_mono)
  done

subsection \<open>Segments\<close>

text \<open>\<open>closed_segment\<close> throws away the order that our intuition keeps\<close>

definition line::"'a::real_vector \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> 'a"
  ("{_ -- _}\<^bsub>_\<^esub>")
  where "{a -- b}\<^bsub>u\<^esub> = a + u *\<^sub>R (b - a)"

abbreviation "line_image a b U \<equiv>(\<lambda>u. {a -- b}\<^bsub>u\<^esub>) ` U"
notation line_image ("{_ -- _}\<^bsub>`_\<^esub>")

lemma in_closed_segment_iff_line: "x \<in> {a -- b} \<longleftrightarrow> (\<exists>c\<in>{0..1}. x = line a b c)"
  by (auto simp: in_segment line_def algebra_simps)

lemma in_open_segment_iff_line: "x \<in> {a <--< b} \<longleftrightarrow> (\<exists>c\<in>{0<..<1}. a \<noteq> b \<and> x = line a b c)"
  by (auto simp: in_segment line_def algebra_simps)

lemma line_convex_combination1: "(1 - u) *\<^sub>R line a b i + u *\<^sub>R b = line a b (i + u - i * u)"
  by (auto simp: line_def algebra_simps)

lemma line_convex_combination2: "(1 - u) *\<^sub>R a + u *\<^sub>R line a b i = line a b (i*u)"
  by (auto simp: line_def algebra_simps)

lemma line_convex_combination12: "(1 - u) *\<^sub>R line a b i + u *\<^sub>R line a b j = line a b (i + u * (j - i))"
  by (auto simp: line_def algebra_simps)

lemma mult_less_one_less_self: "0 < x \<Longrightarrow> i < 1 \<Longrightarrow> i * x < x" for i x::real
  by auto

lemma plus_times_le_one_lemma: "i + u - i * u \<le> 1" if "i \<le> 1" "u \<le> 1" for i u::real
  by (simp add: diff_le_eq sum_le_prod1 that)

lemma plus_times_less_one_lemma: "i + u - i * u < 1" if "i < 1" "u < 1" for i u::real
proof -
  have "u * (1 - i) < 1 - i"
    using that by force
  then show ?thesis by (simp add: algebra_simps)
qed

lemma line_eq_endpoint_iff[simp]:
  "line a b i = b \<longleftrightarrow> (a = b \<or> i = 1)"
  "a = line a b i \<longleftrightarrow> (a = b \<or> i = 0)"
  by (auto simp: line_def algebra_simps)

lemma line_eq_iff[simp]: "line a b x = line a b y \<longleftrightarrow> (x = y \<or> a = b)"
  by (auto simp: line_def)

lemma line_open_segment_iff:
  "{line a b i<--<b} = line a b ` {i<..<1}"
  if "i < 1" "a \<noteq> b"
  using that
  apply (auto simp: in_segment line_convex_combination1 plus_times_less_one_lemma)
  subgoal for j
    apply (rule exI[where x="(j - i)/(1 - i)"])
    apply (auto simp: divide_simps algebra_simps)
    by (metis add_diff_cancel less_numeral_extra(4) mult_2_right plus_times_less_one_lemma that(1))
  done

lemma open_segment_line_iff:
  "{a<--<line a b i} = line a b ` {0<..<i}"
  if "0 < i" "a \<noteq> b"
  using that
  apply (auto simp: in_segment line_convex_combination2 plus_times_less_one_lemma)
  subgoal for j
    apply (rule exI[where x="j/i"])
    by (auto simp: )
  done

lemma line_closed_segment_iff:
  "{line a b i--b} = line a b ` {i..1}"
  if "i \<le> 1" "a \<noteq> b"
  using that
  apply (auto simp: in_segment line_convex_combination1 mult_le_cancel_right2 plus_times_le_one_lemma)
  subgoal for j
    apply (rule exI[where x="(j - i)/(1 - i)"])
    apply (auto simp: divide_simps algebra_simps)
    by (metis add_diff_cancel less_numeral_extra(4) mult_2_right plus_times_less_one_lemma that(1))
  done

lemma closed_segment_line_iff:
  "{a--line a b i} = line a b ` {0..i}"
  if "0 < i" "a \<noteq> b"
  using that
  apply (auto simp: in_segment line_convex_combination2 plus_times_less_one_lemma)
  subgoal for j
    apply (rule exI[where x="j/i"])
    by (auto simp: )
  done

lemma closed_segment_line_line_iff: "{line a b i1--line a b i2} = line a b ` {i1..i2}" if "i1 \<le> i2"
  using that
  apply (auto simp: in_segment line_convex_combination12 intro!: imageI)
   apply (smt mult_left_le_one_le)
  subgoal for u
    by (rule exI[where x="(u - i1)/(i2-i1)"]) auto
  done

lemma line_line1: "line (line a b c) b x = line a b (c + x - c * x)"
  by (simp add: line_def algebra_simps)

lemma line_line2: "line a (line a b c) x = line a b (c*x)"
  by (simp add: line_def algebra_simps)

lemma line_in_subsegment:
  "i1 < 1 \<Longrightarrow> i2 < 1 \<Longrightarrow> a \<noteq> b \<Longrightarrow> line a b i1 \<in> {line a b i2<--<b} \<longleftrightarrow> i2 < i1"
  by (auto simp: line_open_segment_iff intro!: imageI)

lemma line_in_subsegment2:
  "0 < i2 \<Longrightarrow> 0 < i1 \<Longrightarrow> a \<noteq> b \<Longrightarrow> line a b i1 \<in> {a<--<line a b i2} \<longleftrightarrow> i1 < i2"
  by (auto simp: open_segment_line_iff intro!: imageI)

lemma line_in_open_segment_iff[simp]:
  "line a b i \<in> {a<--<b} \<longleftrightarrow> (a \<noteq> b \<and> 0 < i \<and> i < 1)"
  by (auto simp: in_open_segment_iff_line)

subsection \<open>Open Segments\<close>

lemma open_segment_subsegment:
  assumes "x1 \<in> {x0<--<x3}"
    "x2 \<in> {x1<--<x3}"
  shows "x1 \<in> {x0<--<x2}"
  using assms
proof -\<comment> \<open>TODO: use \<open>line\<close>\<close>
  from assms obtain u v::real where
    ne: "x0 \<noteq> x3" "(1 - u) *\<^sub>R x0 + u *\<^sub>R x3 \<noteq> x3"
    and x1_def: "x1 = (1 - u) *\<^sub>R x0 + u *\<^sub>R x3"
    and x2_def: "x2 = (1 - v) *\<^sub>R ((1 - u) *\<^sub>R x0 + u *\<^sub>R x3) + v *\<^sub>R x3"
    and uv: \<open>0 < u\<close> \<open>0 < v\<close> \<open>u < 1\<close> \<open>v < 1\<close>
    by (auto simp: in_segment)
  let ?d = "(u + v - u * v)"
  have "?d > 0" using uv
    by (auto simp: add_nonneg_pos pos_add_strict)
  with \<open>x0 \<noteq> x3\<close> have "0 \<noteq> ?d *\<^sub>R (x3 - x0)" by simp
  moreover
  define ua where "ua = u / ?d"
  have "ua * (u * v - u - v) - - u = 0"
    by (auto simp: ua_def algebra_simps divide_simps)
      (metis uv add_less_same_cancel1 add_strict_mono mult.right_neutral
        mult_less_cancel_left_pos not_real_square_gt_zero vector_space_over_itself.scale_zero_left)
  then have "(ua * (u * v - u - v) - - u) *\<^sub>R (x3 - x0) = 0"
    by simp
  moreover
  have "0 < ua" "ua < 1"
    using \<open>0 < u\<close> \<open>0 < v\<close> \<open>u < 1\<close> \<open>v < 1\<close>
    by (auto simp: ua_def pos_add_strict intro!: divide_pos_pos)
  ultimately show ?thesis
    unfolding x1_def x2_def
    by (auto intro!: exI[where x=ua] simp: algebra_simps in_segment)
qed


subsection \<open>Syntax\<close>

abbreviation sequentially_at_top::"(nat\<Rightarrow>real)\<Rightarrow>bool"
  ("_ \<longlonglongrightarrow>\<^bsub>\<^esub> \<infinity>") \<comment> \<open>the \<open>\<^bsub>\<^esub>\<close> is to disambiguate syntax...\<close>
  where "s \<longlonglongrightarrow>\<^bsub>\<^esub> \<infinity>  \<equiv> filterlim s at_top sequentially"

abbreviation sequentially_at_bot::"(nat\<Rightarrow>real)\<Rightarrow>bool"
  ("_ \<longlonglongrightarrow>\<^bsub>\<^esub> -\<infinity>")
  where "s \<longlonglongrightarrow>\<^bsub>\<^esub> -\<infinity>  \<equiv> filterlim s at_bot sequentially"


subsection \<open>Paths\<close>

lemma subpath0_linepath:
  shows "subpath 0 u (linepath t t') = linepath t (t + u * (t' - t))"
  unfolding subpath_def linepath_def
  apply (rule ext)
  apply auto
proof -
  fix x :: real
  have f1: "\<And>r ra rb rc. (r::real) + ra * rb - ra * rc = r - ra * (rc - rb)"
    by (simp add: right_diff_distrib')
  have f2: "\<And>r ra. (r::real) - r * ra = r * (1 - ra)"
    by (simp add: right_diff_distrib')
  have f3: "\<And>r ra rb. (r::real) - ra + rb + ra - r = rb"
    by auto
  have f4: "\<And>r. (r::real) + (1 - 1) = r"
    by linarith
  have f5: "\<And>r ra. (r::real) + ra = ra + r"
    by force
  have f6: "\<And>r ra. (r::real) + (1 - (r + 1) + ra) = ra"
    by linarith
  have "t - x * (t - (t + u * (t' - t))) = t' * (u * x) + (t - t * (u * x))"
    by (simp add: right_diff_distrib')
  then show "(1 - u * x) * t + u * x * t' = (1 - x) * t + x * (t + u * (t' - t))"
    using f6 f5 f4 f3 f2 f1 by (metis (no_types) mult.commute)
qed

lemma linepath_image0_right_open_real:
  assumes "t < (t'::real)"
  shows "linepath t t' ` {0..<1} = {t..<t'}"
  unfolding linepath_def
  apply auto
    apply (metis add.commute add_diff_cancel_left' assms diff_diff_eq2 diff_le_eq less_eq_real_def mult.commute mult.right_neutral mult_right_mono right_diff_distrib')
   apply (smt assms comm_semiring_class.distrib mult_diff_mult semiring_normalization_rules(2) zero_le_mult_iff)
proof -
  fix x
  assume "t \<le> x" "x < t'"
  let ?u = "(x-t)/(t'-t)"
  have "?u \<ge> 0"
    using \<open>t \<le> x\<close> assms by auto
  moreover have "?u < 1"
    by (simp add: \<open>x < t'\<close> assms)
  moreover have "x = (1-?u) * t + ?u*t'"
  proof -
    have f1: "\<forall>r ra. (ra::real) * - r = r * - ra"
      by simp
    have "t + (t' + - t) * ((x + - t) / (t' + - t)) = x"
      using assms by force
    then have "t' * ((x + - t) / (t' + - t)) + t * (1 + - ((x + - t) / (t' + - t))) = x"
      using f1 by (metis (no_types) add.left_commute distrib_left mult.commute mult.right_neutral)
    then show ?thesis
      by (simp add: mult.commute)
  qed
  ultimately show "x \<in> (\<lambda>x. (1 - x) * t + x * t') ` {0..<1}"
    using atLeastLessThan_iff by blast 
qed

lemma oriented_subsegment_scale:
  assumes "x1 \<in> {a<--<b}"
  assumes "x2 \<in> {x1<--<b}"
  obtains e where "e > 0" "b-a = e *\<^sub>R (x2-x1)"
proof -
  from assms(1) obtain u where u : "u > 0" "u < 1" "x1 = (1 - u) *\<^sub>R a + u *\<^sub>R b"
    unfolding in_segment by blast
  from assms(2) obtain v where v: "v > 0" "v < 1" "x2 = (1 - v) *\<^sub>R x1 + v *\<^sub>R b"
    unfolding in_segment by blast
  have "x2-x1 = -v *\<^sub>R x1 + v *\<^sub>R b" using v
    by (metis add.commute add_diff_cancel_right diff_minus_eq_add scaleR_collapse scaleR_left.minus)
  also have "... = (-v) *\<^sub>R ((1 - u) *\<^sub>R a + u *\<^sub>R b)  + v *\<^sub>R b" using u by auto
  also have "... = v *\<^sub>R ((1-u)*\<^sub>R b - (1-u)*\<^sub>R a )"
    by (smt add_diff_cancel diff_diff_add diff_minus_eq_add minus_diff_eq scaleR_collapse scale_minus_left scale_right_diff_distrib)
  finally have x2x1:"x2-x1 = (v *(1-u)) *\<^sub>R (b - a)"
    by (metis scaleR_scaleR scale_right_diff_distrib)
  have "v * (1-u) > 0"  using u(2) v(1) by simp
  then have "(x2-x1)/\<^sub>R (v * (1-u)) = (b-a)" unfolding x2x1
    by (smt field_class.field_inverse scaleR_one scaleR_scaleR) 
  thus ?thesis
    using \<open>0 < v * (1 - u)\<close> positive_imp_inverse_positive that by fastforce
qed

end
