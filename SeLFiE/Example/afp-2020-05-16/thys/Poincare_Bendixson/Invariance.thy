section \<open>Invariance\<close>
theory Invariance
  imports ODE_Misc
begin

context auto_ll_on_open begin

definition "invariant M \<longleftrightarrow> (\<forall>x\<in>M. trapped x M)"

definition "positively_invariant M \<longleftrightarrow> (\<forall>x\<in>M. trapped_forward x M)"

definition "negatively_invariant M \<longleftrightarrow> (\<forall>x\<in>M. trapped_backward x M)"

lemma positively_invariant_iff:
  "positively_invariant M \<longleftrightarrow>
  (\<Union>x\<in>M. flow0 x ` (existence_ivl0 x \<inter> {0..})) \<subseteq> M"
  unfolding positively_invariant_def trapped_forward_def
  by auto

lemma negatively_invariant_iff:
  "negatively_invariant M \<longleftrightarrow>
  (\<Union>x\<in>M. flow0 x ` (existence_ivl0 x \<inter> {..0})) \<subseteq> M"
  unfolding negatively_invariant_def trapped_backward_def
  by auto

lemma invariant_iff_pos_and_neg_invariant:
  "invariant M \<longleftrightarrow> positively_invariant M \<and> negatively_invariant M"
  unfolding invariant_def trapped_def positively_invariant_def negatively_invariant_def
  by blast

lemma invariant_iff:
  "invariant M \<longleftrightarrow> (\<Union>x\<in>M. flow0 x ` (existence_ivl0 x)) \<subseteq>  M"
  unfolding invariant_iff_pos_and_neg_invariant positively_invariant_iff negatively_invariant_iff
  by (metis (mono_tags) SUP_le_iff invariant_def invariant_iff_pos_and_neg_invariant negatively_invariant_iff positively_invariant_iff trapped_iff_on_existence_ivl0)

lemma positively_invariant_restrict_dom: "positively_invariant M = positively_invariant (M \<inter> X)"
  unfolding positively_invariant_def trapped_forward_def
  by (auto intro!: flow_in_domain dest: mem_existence_ivl_iv_defined)

lemma negatively_invariant_restrict_dom: "negatively_invariant M = negatively_invariant (M \<inter> X)"
  unfolding negatively_invariant_def trapped_backward_def
  by (auto intro!: flow_in_domain dest: mem_existence_ivl_iv_defined)

lemma invariant_restrict_dom: "invariant M = invariant (M \<inter> X)"
  using invariant_iff_pos_and_neg_invariant
    negatively_invariant_restrict_dom
    positively_invariant_restrict_dom by auto
    (*
lemma positively_invariant_imp_subset:
  "M \<subseteq> X" if "positively_invariant M"
  using positively_invariant_iff that by blast

lemma negatively_invariant_imp_subset:
  "M \<subseteq> X" if "negatively_invariant M"
  using negatively_invariant_iff that by blast

lemma invariant_imp_subset:
  "M \<subseteq> X" if "invariant M"
  using invariant_iff that by blast
*)

end context auto_ll_on_open begin

lemma positively_invariant_eq_rev: "positively_invariant M = rev.negatively_invariant M"
  unfolding positively_invariant_def rev.negatively_invariant_def
  by (simp add: rev.trapped_backward_iff_rev_trapped_forward)

lemma negatively_invariant_eq_rev: "negatively_invariant M = rev.positively_invariant M"
  unfolding negatively_invariant_def rev.positively_invariant_def
  by (simp add: trapped_backward_iff_rev_trapped_forward)

lemma invariant_eq_rev: "invariant M = rev.invariant M"
  unfolding invariant_iff_pos_and_neg_invariant rev.invariant_iff_pos_and_neg_invariant
    positively_invariant_eq_rev negatively_invariant_eq_rev by auto

lemma negatively_invariant_complI: "negatively_invariant (X-M)" if "positively_invariant M"
  unfolding negatively_invariant_def trapped_backward_def
proof clarsimp
  fix x t
  assume x: "x \<in> X" "x \<notin> M" "t \<in> existence_ivl0 x" "t \<le> 0"
  have a1:"flow0 x t \<in> X" using x
    using flow_in_domain by blast
  have a2:"flow0 x t \<notin> M"
  proof (rule ccontr)
    assume "\<not> flow0 x t \<notin> M"
    then have "trapped_forward (flow0 x t) M"
      using positively_invariant_def that by auto
    moreover have "flow0 (flow0 x t) (-t) = x"
      using \<open>t \<in> existence_ivl0 x\<close> flows_reverse by auto
    moreover have "-t \<in> existence_ivl0 (flow0 x t) \<inter> {0..}"
      using existence_ivl_reverse x(3) x(4) by auto
    ultimately have "x \<in> M" unfolding trapped_forward_def
      by (metis image_subset_iff)
    thus False using x(2) by auto
  qed
  show "flow0 x t \<in> X \<and> flow0 x t \<notin> M" using a1 a2 by auto
qed

end context auto_ll_on_open begin

lemma negatively_invariant_complD: "positively_invariant M" if "negatively_invariant (X-M)"
proof -
  have "rev.positively_invariant (X-M)" using that
    by (simp add: negatively_invariant_eq_rev)
  then have "rev.negatively_invariant (X-(X-M))"
    by (simp add: rev.negatively_invariant_complI)
  then have "positively_invariant (X-(X-M))"
    using rev.negatively_invariant_eq_rev by auto
  thus ?thesis using Diff_Diff_Int
    by (metis inf_commute positively_invariant_restrict_dom) 
qed

lemma pos_invariant_iff_compl_neg_invariant: "positively_invariant M \<longleftrightarrow> negatively_invariant (X - M)"
  by (safe intro!: negatively_invariant_complI dest!: negatively_invariant_complD)

lemma neg_invariant_iff_compl_pos_invariant:
  shows "negatively_invariant M \<longleftrightarrow> positively_invariant (X - M)"
  by (simp add: auto_ll_on_open.pos_invariant_iff_compl_neg_invariant negatively_invariant_eq_rev positively_invariant_eq_rev rev.auto_ll_on_open_axioms)

lemma invariant_iff_compl_invariant:
  shows "invariant M \<longleftrightarrow> invariant (X - M)"
  using invariant_iff_pos_and_neg_invariant neg_invariant_iff_compl_pos_invariant pos_invariant_iff_compl_neg_invariant by blast

lemma invariant_iff_pos_invariant_and_compl_pos_invariant:
  shows "invariant M \<longleftrightarrow> positively_invariant M \<and> positively_invariant (X-M)"
  by (simp add: invariant_iff_pos_and_neg_invariant neg_invariant_iff_compl_pos_invariant)

end

subsection \<open>Tools for proving invariance\<close>

context auto_ll_on_open begin

lemma positively_invariant_left_inter:
  assumes "positively_invariant C"
  assumes "\<forall>x \<in> C \<inter> D. trapped_forward x D"
  shows "positively_invariant (C \<inter> D)"
  using assms positively_invariant_def trapped_forward_def by auto

lemma trapped_forward_le:
  fixes V :: "'a \<Rightarrow> real"
  assumes "V x \<le> 0"
  assumes contg: "continuous_on (flow0 x ` (existence_ivl0 x \<inter> {0..})) g"
  assumes "\<And>x. (V has_derivative V' x) (at x)"
  assumes "\<And>s. s \<in> existence_ivl0 x \<inter> {0..} \<Longrightarrow> V' (flow0 x s) (f (flow0 x s)) \<le> g (flow0 x s) * V (flow0 x s)"
  shows "trapped_forward x {x. V x \<le> 0}"
  unfolding trapped_forward_def
proof clarsimp
  fix t
  assume t: "t \<in> existence_ivl0 x" "0 \<le> t"
  then have ex:"{0..t} \<subseteq> existence_ivl0 x"
    by (simp add: local.ivl_subset_existence_ivl)
  have contV: "continuous_on UNIV V"
    using assms(3) has_derivative_continuous_on by blast
  have 1: "continuous_on {0..t} (g \<circ> flow0 x)"
    apply (rule continuous_on_compose)
    using continuous_on_subset ex local.flow_continuous_on apply blast
    by (meson Int_subset_iff atLeastAtMost_iff atLeast_iff contg continuous_on_subset ex image_mono subsetI)
  have 2: "(\<And>s. s \<in> {0..t} \<Longrightarrow>
         (V \<circ> flow0 x has_real_derivative (V' (flow0 x s) \<circ> f \<circ> flow0 x) s) (at s))"
    apply (auto simp add:o_def has_field_derivative_def)
  proof -                              
    fix s
    assume "0 \<le> s" "s \<le> t"
    then have "s \<in> existence_ivl0 x" using ex by auto
    from flow_has_derivative[OF this] have
      "(flow0 x has_derivative (\<lambda>i. i *\<^sub>R f (flow0 x s))) (at s)" .
    from has_derivative_compose[OF this assms(3)]
    have "((\<lambda>t. V (flow0 x t)) has_derivative (\<lambda>t. V' (flow0 x s)  (t *\<^sub>R f (flow0 x s)))) (at s)" .
    moreover have "linear (V' (flow0 x s))"  using assms(3) has_derivative_linear by blast
    ultimately 
    have "((\<lambda>t. V (flow0 x t)) has_derivative (\<lambda>t. t *\<^sub>R V' (flow0 x s) (f (flow0 x s)))) (at s)" 
      unfolding linear_cmul[OF \<open>linear (V' (flow0 x s))\<close>] by blast
    thus "((\<lambda>t. V (flow0 x t)) has_derivative (*) (V' (flow0 x s) (f (flow0 x s)))) (at s)"
      by (auto intro!: derivative_eq_intros simp add: mult_commute_abs)
  qed
  have 3: "(\<And>s. s \<in> {0..t} \<Longrightarrow>
         (V' (flow0 x s)  \<circ> f \<circ> flow0 x) s \<le> (g \<circ> flow0 x) s *\<^sub>R (V \<circ> flow0 x) s)"
    using ex by (auto intro!:assms(4))
  from comparison_principle_le_linear[OF 1 2 _ 3] assms(1)
  have "\<forall>s \<in> {0..t}. (V \<circ> flow0 x) s \<le> 0"
    using local.mem_existence_ivl_iv_defined(2) t(1) by auto
  thus " V (flow0 x t) \<le> 0"
    by (simp add: t(2))
qed

lemma positively_invariant_le_domain:
  fixes V :: "'a \<Rightarrow> real"
  assumes "positively_invariant D"
  assumes contg: "continuous_on D g"
  assumes "\<And>x. (V has_derivative V' x) (at x)" (* TODO: domain can be added here too ? *)
  assumes "\<And>s. s \<in> D \<Longrightarrow> V' s (f s) \<le> g s * V s"
  shows "positively_invariant (D \<inter> {x. V x \<le> 0})"
  apply (auto intro!:positively_invariant_left_inter[OF assms(1)])
proof -
  fix x
  assume "x \<in> D" "V x \<le> 0"
  have "continuous_on (flow0 x ` (existence_ivl0 x \<inter> {0..})) g"
    by (meson \<open>x \<in> D\<close> assms(1) contg continuous_on_subset positively_invariant_def trapped_forward_def)
  from trapped_forward_le[OF \<open>V x \<le> 0\<close> this assms(3)]
  show "trapped_forward x {x. V x \<le> 0}" using assms(4)
    using \<open>x \<in> D\<close> assms(1) positively_invariant_def trapped_forward_def by auto
qed

lemma positively_invariant_barrier_domain:
  fixes V :: "'a \<Rightarrow> real"
  assumes "positively_invariant D"
  assumes "\<And>x. (V has_derivative V' x) (at x)"
  assumes "continuous_on D (\<lambda>x. V' x (f x))"
  assumes "\<And>s. s \<in> D \<Longrightarrow> V s = 0 \<Longrightarrow> V' s (f s) < 0"
  shows "positively_invariant (D \<inter> {x. V x \<le> 0})"
  apply (auto intro!:positively_invariant_left_inter[OF assms(1)])
proof -
  fix x
  assume "x \<in> D" "V x \<le> 0"
  have contV: "continuous_on UNIV V" using assms(2) has_derivative_continuous_on by blast
  then have *: "continuous_on (flow0 x ` (existence_ivl0 x \<inter> {0..})) V"
    using continuous_on_subset by blast
  have sub: "flow0 x ` (existence_ivl0 x \<inter> {0..}) \<subseteq> D"
    using \<open>x \<in> D\<close> assms(1) positively_invariant_def trapped_forward_def by auto
  then have contV': "continuous_on (flow0 x ` (existence_ivl0 x \<inter> {0..})) (\<lambda>x. V' x (f x))"
    by (metis assms(3) continuous_on_subset)
  have nz: "\<And>i t. t \<in> existence_ivl0 x \<Longrightarrow>
       0 \<le> t \<Longrightarrow>  max (-V' (flow0 x t) (f (flow0 x t))) ((V (flow0 x t))\<^sup>2) > 0"
  proof -
    fix i t
    assume "t \<in> existence_ivl0 x" "0 \<le> t"
    then have "flow0 x t \<in> D"
      using \<open>x \<in> D\<close> assms(1) positively_invariant_def trapped_forward_def by auto
    then have "V (flow0 x t) = 0 \<Longrightarrow> - V' (flow0 x t) (f (flow0 x t)) > 0" using assms(4) by simp
    then have "(V (flow0 x t))^2 > 0 \<or> - V' (flow0 x t) (f (flow0 x t)) > 0" by simp
    thus "max (-V' (flow0 x t) (f (flow0 x t))) ((V (flow0 x t))\<^sup>2) > 0" unfolding less_max_iff_disj
      by auto
  qed
  have *: "continuous_on (flow0 x ` (existence_ivl0 x \<inter> {0..})) (\<lambda>x. V' x (f x) * V x / max (- V' x (f x)) ((V x)^2))"
    apply (auto intro!:continuous_intros continuous_on_max simp add: * contV')
    using nz by fastforce
  have "(\<And>t. t \<in> existence_ivl0 x \<inter> {0..} \<Longrightarrow>
        V' (flow0 x t) (f (flow0 x t)) \<le>
        (V' (flow0 x t) (f (flow0 x t)) * V (flow0 x t)
        / max (- V' (flow0 x t) (f (flow0 x t))) ((V (flow0 x t))\<^sup>2)) * V (flow0 x t))"
  proof clarsimp
    fix t
    assume "t \<in> existence_ivl0 x" "0 \<le> t"
    then have p: "max (-V' (flow0 x t) (f (flow0 x t))) ((V (flow0 x t))\<^sup>2) > 0" using nz by auto
    have " V' (flow0 x t) (f (flow0 x t)) * max (- V' (flow0 x t) (f (flow0 x t))) ((V (flow0 x t))\<^sup>2)
      \<le>  V' (flow0 x t) (f (flow0 x t)) * (V (flow0 x t))\<^sup>2"
      by (smt mult_minus_left mult_minus_right power2_eq_square real_mult_le_cancel_iff2)
    then have "V' (flow0 x t) (f (flow0 x t))
      \<le>  V' (flow0 x t) (f (flow0 x t)) * (V (flow0 x t))\<^sup>2
      / max (- V' (flow0 x t) (f (flow0 x t))) ((V (flow0 x t))\<^sup>2)"
      using p pos_le_divide_eq by blast
    thus " V' (flow0 x t) (f (flow0 x t))
         \<le> V' (flow0 x t) (f (flow0 x t)) * (V (flow0 x t)) * V (flow0 x t) /
           max (- V' (flow0 x t) (f (flow0 x t))) ((V (flow0 x t))\<^sup>2)"
      by (simp add: power2_eq_square)
  qed
  from trapped_forward_le[OF \<open>V x \<le> 0\<close> * assms(2) this]
  show "trapped_forward x {x. V x \<le> 0}" by auto
qed

lemma positively_invariant_UNIV:
  shows "positively_invariant UNIV"
  using positively_invariant_iff by blast

lemma positively_invariant_conj:
  assumes "positively_invariant C"
  assumes "positively_invariant D"
  shows "positively_invariant (C \<inter> D)"
  using assms positively_invariant_def
  using positively_invariant_left_inter by auto

lemma positively_invariant_le:
  fixes V :: "'a \<Rightarrow> real"
  assumes contg: "continuous_on UNIV g"
  assumes "\<And>x. (V has_derivative V' x) (at x)"
  assumes "\<And>s. V' s (f s) \<le> g s * V s"
  shows "positively_invariant {x. V x \<le> 0}"
proof -
  from positively_invariant_le_domain[OF positively_invariant_UNIV assms]  
  have "positively_invariant (UNIV \<inter> {x. V x \<le> 0})" .
  thus ?thesis by auto
qed

lemma positively_invariant_barrier:
  fixes V :: "'a \<Rightarrow> real"
  assumes "\<And>x. (V has_derivative V' x) (at x)"
  assumes "continuous_on UNIV (\<lambda>x. V' x (f x))"
  assumes "\<And>s. V s = 0 \<Longrightarrow> V' s (f s) < 0"
  shows "positively_invariant {x. V x \<le> 0}"
proof -
  from positively_invariant_barrier_domain[OF positively_invariant_UNIV assms]  
  have "positively_invariant (UNIV \<inter> {x. V x \<le> 0})" .
  thus ?thesis by auto
qed

end

end