section \<open>Limit Sets\<close>
theory Limit_Set
  imports Invariance
begin

context auto_ll_on_open begin
text \<open>Positive limit point, assuming \<open>{0..} \<subseteq> existence_ivl0 x\<close>\<close>

(* TODO: Perhaps a more intrinsic definition would be better here *)
definition "\<omega>_limit_point x p \<longleftrightarrow>
  {0..} \<subseteq> existence_ivl0 x \<and>
  (\<exists>s. s \<longlonglongrightarrow>\<^bsub>\<^esub> \<infinity> \<and> (flow0 x \<circ> s) \<longlonglongrightarrow> p)"

text \<open> Also called the \<open>\<omega>\<close>-limit set of x \<close>
definition "\<omega>_limit_set x = {p. \<omega>_limit_point x p}"

definition "\<alpha>_limit_point x p \<longleftrightarrow>
  {..0} \<subseteq> existence_ivl0 x \<and>
  (\<exists>s. s \<longlonglongrightarrow>\<^bsub>\<^esub> -\<infinity> \<and> (flow0 x \<circ> s) \<longlonglongrightarrow> p)"

text \<open> Also called the \<open>\<alpha>\<close>-limit set of x \<close>
definition "\<alpha>_limit_set x =
  {p. \<alpha>_limit_point x p}"

end context auto_ll_on_open begin

lemma \<alpha>_limit_point_eq_rev: "\<alpha>_limit_point x p = rev.\<omega>_limit_point x p"
  unfolding \<alpha>_limit_point_def rev.\<omega>_limit_point_def
  apply (auto simp: rev_eq_flow[abs_def] o_def filterlim_uminus_at_bot rev_existence_ivl_eq0 subset_iff
      intro: exI[where x="uminus o s" for s])
  using neg_0_le_iff_le by fastforce

lemma \<alpha>_limit_set_eq_rev: "\<alpha>_limit_set x = rev.\<omega>_limit_set x"
  unfolding \<alpha>_limit_set_def rev.\<omega>_limit_set_def \<alpha>_limit_point_eq_rev ..

lemma \<omega>_limit_pointE:
  assumes "\<omega>_limit_point x p"
  obtains s where
    "filterlim s at_top sequentially"
    "(flow0 x \<circ> s) \<longlonglongrightarrow> p"
    "\<forall>n. b \<le> s n"
  using assms filterlim_at_top_choose_lower \<omega>_limit_point_def by blast

lemma \<omega>_limit_set_eq:
  assumes "{0..} \<subseteq> existence_ivl0 x"
  shows "\<omega>_limit_set x = (INF \<tau> \<in> {0..}. closure (flow0 x ` {\<tau>..}))"
  unfolding \<omega>_limit_set_def
proof safe
  fix p t
  assume pt: "0 \<le> (t::real)" "\<omega>_limit_point x p"
  from \<omega>_limit_pointE[OF pt(2)]
  obtain s where
    "filterlim s at_top sequentially"
    "(flow0 x \<circ> s) \<longlonglongrightarrow> p"
    "\<forall>n. t \<le> s n" by blast
  thus "p \<in> closure (flow0 x ` {t..})" unfolding closure_sequential
    by (metis atLeast_iff comp_apply imageI)
next
  fix p
  assume "p \<in> (\<Inter>\<tau>\<in>{0..}. closure (flow0 x ` {\<tau>..}))"
  then have "\<And>t. t \<ge>0 \<Longrightarrow> p \<in> closure (flow0 x ` {t..})" by blast
  then have "\<And>t e. t \<ge>0 \<Longrightarrow> e > 0 \<Longrightarrow> (\<exists>tt \<ge> t. dist (flow0 x tt) p < e)"
    unfolding closure_approachable
    by fastforce
  from approachable_sequenceE[OF this]
  obtain s where "filterlim s at_top sequentially" "(flow0 x \<circ> s) \<longlonglongrightarrow> p" by auto
  thus "\<omega>_limit_point x p" unfolding \<omega>_limit_point_def using assms by auto
qed

lemma \<omega>_limit_set_empty:
  assumes "\<not> ({0..} \<subseteq> existence_ivl0 x)"
  shows "\<omega>_limit_set x = {}"
  unfolding \<omega>_limit_set_def \<omega>_limit_point_def
  by (simp add: assms)

lemma \<omega>_limit_set_closed: "closed (\<omega>_limit_set x)"
  using \<omega>_limit_set_eq
  by (metis \<omega>_limit_set_empty closed_INT closed_closure closed_empty)

(* TODO: Walter gives a more direct proof *)
lemma \<omega>_limit_set_positively_invariant:
  shows "positively_invariant (\<omega>_limit_set x)"
  unfolding positively_invariant_def trapped_forward_def
proof safe
  fix dummy p t
  assume xa: "p \<in> \<omega>_limit_set x"
    "t \<in> existence_ivl0 p"
    "0 \<le> t"
  have "p \<in> X" using mem_existence_ivl_iv_defined(2) xa(2) by blast
  have exist: "{0..} \<subseteq> existence_ivl0 x" using xa(1)
    unfolding \<omega>_limit_set_def \<omega>_limit_point_def by auto
  from xa(1)
  obtain s where s:
    "filterlim s at_top sequentially"
    "(flow0 x \<circ> s) \<longlonglongrightarrow> p"
    "\<forall>n. 0 \<le> s n"
    unfolding \<omega>_limit_set_def by (auto elim!:\<omega>_limit_pointE)
  define r where "r = (\<lambda>n. t + s n)"
  have rlim: "filterlim r at_top sequentially" unfolding r_def
    by (auto intro: filterlim_tendsto_add_at_top[OF _ s(1)])
  define dom where "dom = image (flow0 x) {0..} \<union> {p} "
  have domin: "\<forall>n. (flow0 x \<circ> s) n \<in> dom" "p \<in> dom" unfolding dom_def o_def
    using exist by(auto simp add: s(3))
  have xt: "\<And>x. x \<in> dom \<Longrightarrow> t \<in> existence_ivl0 x" unfolding dom_def using xa(2)
    apply auto
    apply (rule existence_ivl_trans')
    using exist xa(3) apply auto[1]
    using exist  by auto
  have cont: "continuous_on dom (\<lambda>x. flow0 x t)"
    apply (rule flow_continuous_on_compose)
       apply auto
    using \<open>p \<in> X\<close>  exist local.dom_def local.flow_in_domain apply auto[1]
    using xt .
  then have f1: "((\<lambda>x. flow0 x t) \<circ> (flow0 x \<circ> s)) \<longlonglongrightarrow> flow0 p t" using domin s(2)
    unfolding continuous_on_sequentially
    by blast
  have ff:"\<And>n. (flow0 x \<circ> r) n = ((\<lambda>x. flow0 x t) \<circ> (flow0 x \<circ> s)) n"
    unfolding o_def r_def
  proof -
    fix n
    have s:"s n \<in> existence_ivl0 x"
      using s(3) exist by auto
    then have t:"t \<in> existence_ivl0 (flow0 x (s n))"
      using domin(1) xt by auto
    from flow_trans[OF s t]
    show "flow0 x (t + s n) = flow0 (flow0 x (s n)) t"
      by (simp add: add.commute)
  qed
  have f2: "(flow0 x \<circ> r) \<longlonglongrightarrow> flow0 p t" using f1 unfolding ff .
  show "flow0 p t \<in> \<omega>_limit_set x" using exist f2 rlim
    unfolding \<omega>_limit_set_def \<omega>_limit_point_def
    using flow_in_domain r_def s(3) xa(2) xa(3) by auto
qed

lemma \<omega>_limit_set_invariant:
  shows "invariant (\<omega>_limit_set x)"
  unfolding invariant_iff_pos_invariant_and_compl_pos_invariant
proof safe
  show "positively_invariant (\<omega>_limit_set x)"
    using \<omega>_limit_set_positively_invariant .
next
  show "positively_invariant (X - \<omega>_limit_set x)"
    unfolding positively_invariant_def trapped_forward_def
    apply safe
    using local.flow_in_domain apply blast
  proof -
    fix dummy p t 
    assume xa: "p \<in> X" "p \<notin> \<omega>_limit_set x"
      "t \<in> existence_ivl0 p" "0 \<le> t"
      and f: "flow0 p t \<in> \<omega>_limit_set x"
    have exist: "{0..} \<subseteq> existence_ivl0 x" using f
      unfolding \<omega>_limit_set_def \<omega>_limit_point_def by auto
    from f
    obtain s where s:
      "filterlim s at_top sequentially"
      "(flow0 x \<circ> s) \<longlonglongrightarrow> flow0 p t"
      "\<forall>n. t \<le> s n"
      unfolding \<omega>_limit_set_def by (auto elim!:\<omega>_limit_pointE)
    define r where "r = (\<lambda>n. (-t) + s n)"
    have "(\<lambda>x. -t) \<longlonglongrightarrow> -t" by simp
    from filterlim_tendsto_add_at_top[OF this s(1)]
    have rlim: "filterlim r at_top sequentially" unfolding r_def by simp
    define dom where "dom = image (flow0 x) {t..} \<union> {flow0 p t} "
    have domin: "\<forall>n. (flow0 x \<circ> s) n \<in> dom" "flow0 p t \<in> dom" unfolding dom_def o_def
      using exist by(auto simp add: s(3))
    have xt: "\<And>x. x \<in> dom \<Longrightarrow> -t \<in> existence_ivl0 x" unfolding dom_def using xa(2)
      apply auto
      using local.existence_ivl_reverse xa(3) apply auto[1]
      by (metis exist atLeast_iff diff_conv_add_uminus diff_ge_0_iff_ge linordered_ab_group_add_class.zero_le_double_add_iff_zero_le_single_add local.existence_ivl_trans' order_trans subset_iff xa(4))
    have cont: "continuous_on dom (\<lambda>x. flow0 x (-t))"
      apply (rule flow_continuous_on_compose)
         apply auto
      using local.mem_existence_ivl_iv_defined(2) xt apply blast
      by (simp add: xt)
    then have f1: "((\<lambda>x. flow0 x (-t)) \<circ> (flow0 x \<circ> s)) \<longlonglongrightarrow> flow0 (flow0 p t) (-t)" using domin s(2)
      unfolding continuous_on_sequentially
      by blast
    have ff:"\<And>n. (flow0 x \<circ> r) n = ((\<lambda>x. flow0 x (-t)) \<circ> (flow0 x \<circ> s)) n"
      unfolding o_def r_def
    proof -
      fix n
      have s:"s n \<in> existence_ivl0 x"
        using s(3) exist \<open>0\<le> t\<close> by (meson atLeast_iff order_trans subset_eq)
      then have t:"-t \<in> existence_ivl0 (flow0 x (s n))"
        using domin(1) xt by auto
      from flow_trans[OF s t]
      show "flow0 x (-t + s n) = flow0 (flow0 x (s n)) (-t)"
        by (simp add: add.commute)
    qed
    have "(flow0 x \<circ> r) \<longlonglongrightarrow> flow0 (flow0 p t) (-t)" using f1 unfolding ff .
    then have f2: "(flow0 x \<circ> r) \<longlonglongrightarrow> p" using flows_reverse xa(3) by auto
    then have "p \<in> \<omega>_limit_set x" unfolding \<omega>_limit_set_def \<omega>_limit_point_def
      using rlim exist by auto
    thus False using xa(2) by auto
  qed
qed

end context auto_ll_on_open begin

lemma \<alpha>_limit_set_eq:
  assumes "{..0} \<subseteq> existence_ivl0 x"
  shows "\<alpha>_limit_set x = (INF \<tau> \<in> {..0}. closure (flow0 x ` {..\<tau>}))"
  using rev.\<omega>_limit_set_eq[of x, OF assms[folded infinite_rev_existence_ivl0_rewrites]]
  unfolding \<alpha>_limit_set_eq_rev rev_flow_image_eq image_uminus_atLeast 
  by (smt INT_extend_simps(10) Sup.SUP_cong image_uminus_atMost)

lemma \<alpha>_limit_set_closed:
  shows "closed (\<alpha>_limit_set x)"
  unfolding \<alpha>_limit_set_eq_rev by (rule rev.\<omega>_limit_set_closed)

lemma \<alpha>_limit_set_positively_invariant:
  shows "negatively_invariant (\<alpha>_limit_set x)"
  unfolding negatively_invariant_eq_rev \<alpha>_limit_set_eq_rev
  by (simp add: rev.\<omega>_limit_set_positively_invariant)

lemma \<alpha>_limit_set_invariant:
  shows "invariant (\<alpha>_limit_set x)"
  unfolding invariant_eq_rev \<alpha>_limit_set_eq_rev
  by (simp add: rev.\<omega>_limit_set_invariant)

text \<open> Fundamental properties of the positive limit set \<close>

context
  fixes x K
  assumes K: "compact K" "K \<subseteq> X"
  assumes x: "x \<in> X" "trapped_forward x K"
begin

text \<open>Bunch of facts for what's to come\<close>
private lemma props:
  shows "{0..} \<subseteq> existence_ivl0 x" "seq_compact K"
   apply (rule trapped_sol_right)
  using x K by (auto simp add: compact_imp_seq_compact)

private lemma flowimg:
  shows "flow0 x ` (existence_ivl0 x \<inter> {0..}) = flow0 x ` {0..}"
  using props(1) by auto

lemma \<omega>_limit_set_in_compact_subset:
  shows "\<omega>_limit_set x \<subseteq> K"
  unfolding \<omega>_limit_set_def
proof safe
  fix p s
  assume "\<omega>_limit_point x p"
  from \<omega>_limit_pointE[OF this]
  obtain s where s:
    "filterlim s at_top sequentially"
    "(flow0 x \<circ> s) \<longlonglongrightarrow> p"
    "\<forall>n. 0 \<le> s n" by blast
  then have fin: "\<forall>n. (flow0 x \<circ> s) n \<in> K" using s(3) x K props(1)
    unfolding trapped_forward_def
    by (simp add: subset_eq)
  from seq_compactE[OF props(2) fin]
  show "p \<in> K" using s(2)
    by (metis LIMSEQ_subseq_LIMSEQ LIMSEQ_unique)
qed

lemma \<omega>_limit_set_in_compact_compact:
  shows "compact (\<omega>_limit_set x)"
proof -
  from \<omega>_limit_set_in_compact_subset 
  have "bounded (\<omega>_limit_set x)"
    using bounded_subset compact_imp_bounded
    using K(1) by auto
  thus ?thesis using \<omega>_limit_set_closed
    by (simp add: compact_eq_bounded_closed)
qed

lemma \<omega>_limit_set_in_compact_nonempty:
  shows "\<omega>_limit_set x \<noteq> {}"
proof -
  have fin: "\<forall>n. (flow0 x \<circ> real) n \<in> K" using x K props(1)
    by (simp add: flowimg image_subset_iff trapped_forward_def)
  from seq_compactE[OF props(2) this]
  obtain r l where "l \<in> K" "strict_mono r" "(flow0 x \<circ> real \<circ> r) \<longlonglongrightarrow> l" by blast
  then have "\<omega>_limit_point x l" unfolding \<omega>_limit_point_def using props(1)
    by (smt comp_def filterlim_sequentially_iff_filterlim_real filterlim_subseq tendsto_at_top_eq_left)
  thus ?thesis unfolding \<omega>_limit_set_def by auto
qed

lemma \<omega>_limit_set_in_compact_existence:
  shows "\<And>y. y \<in> \<omega>_limit_set x \<Longrightarrow> existence_ivl0 y = UNIV"
proof -
  fix y
  assume y: "y \<in> \<omega>_limit_set x"
  then have "y \<in> X" using \<omega>_limit_set_in_compact_subset K by blast 
  from \<omega>_limit_set_invariant
  have "\<And>t. t \<in> existence_ivl0 y \<Longrightarrow> flow0 y t \<in> \<omega>_limit_set x"
    unfolding invariant_def trapped_iff_on_existence_ivl0 using y by blast 
  then have t: "\<And>t. t \<in> existence_ivl0 y \<Longrightarrow> flow0 y t \<in> K"
    using \<omega>_limit_set_in_compact_subset by blast
  thus "existence_ivl0 y = UNIV" 
    by (meson \<open>y \<in> X\<close> existence_ivl_zero existence_ivl_initial_time_iff existence_ivl_subset mem_compact_implies_subset_existence_interval subset_antisym K)
qed

lemma \<omega>_limit_set_in_compact_tendsto:
  shows "((\<lambda>t. infdist (flow0 x t) (\<omega>_limit_set x)) \<longlongrightarrow> 0) at_top"
proof (rule ccontr)
  assume "\<not> ((\<lambda>t. infdist (flow0 x t) (\<omega>_limit_set x)) \<longlongrightarrow> 0) at_top"
  from not_tendsto_frequentlyE[OF this]
  obtain S where S: "open S" "0 \<in> S"
    "\<exists>\<^sub>F t in at_top. infdist (flow0 x t) (\<omega>_limit_set x) \<notin> S" .
  then obtain e where "e > 0" "ball 0 e \<subseteq> S" using openE by blast
  then have "\<And>x. x \<ge>0 \<Longrightarrow> x \<notin> S \<Longrightarrow> x \<ge> e" by force
  then have "\<forall>xa. infdist (flow0 x xa) (\<omega>_limit_set x) \<notin> S \<longrightarrow>
        infdist (flow0 x xa) (\<omega>_limit_set x) \<ge> e" using infdist_nonneg by blast  
  from frequently_mono[OF this S(3)]
  have "\<exists>\<^sub>F t in at_top. infdist (flow0 x t) (\<omega>_limit_set x) \<ge> e" by blast
  then have "\<forall>n. \<exists>\<^sub>F t in at_top. infdist (flow0 x t) (\<omega>_limit_set x) \<ge> e \<and> real n \<le> t"
    by (auto intro!: eventually_frequently_conj)
  from frequently_at_topE[OF this]
  obtain s where s: "\<And>i. e \<le> infdist (flow0 x (s i)) (\<omega>_limit_set x)"
    "\<And>i. real i \<le> s i" "strict_mono s" by force
  then have sf: "filterlim s at_top sequentially"
    using filterlim_at_top_mono filterlim_real_sequentially not_eventuallyD by blast 
  have fin: "\<forall>n. (flow0 x \<circ> s) n \<in> K"  using x K props(1) s unfolding flowimg trapped_forward_def
    by (metis atLeast_iff comp_apply image_subset_iff of_nat_0_le_iff order_trans)
  from seq_compactE[OF props(2) this]
  obtain r l where r:"strict_mono r" and l: "l \<in> K" "(flow0 x \<circ> s \<circ> r) \<longlonglongrightarrow> l" by blast
  moreover from filterlim_at_top_strict_mono[OF s(3) r(1) sf]
  have "filterlim (s \<circ> r) at_top sequentially" .
  moreover have "\<omega>_limit_point x l" unfolding \<omega>_limit_point_def using props(1) calculation
    by (metis comp_assoc)
  ultimately have "infdist l (\<omega>_limit_set x) = 0" by (simp add: \<omega>_limit_set_def)
  then have c1:"((\<lambda>y. infdist y (\<omega>_limit_set x)) \<circ> (flow0 x \<circ> s \<circ> r)) \<longlonglongrightarrow> 0"
    by (auto intro!: tendsto_compose_at[OF l(2)] tendsto_eq_intros)
  have c2: "\<And>i. e \<le> infdist (flow0 x ((s \<circ> r) i)) (\<omega>_limit_set x)" using s(1) by simp
  show False using c1 c2 \<open>e > 0\<close> unfolding o_def
    using Lim_bounded2
    by (metis (no_types, lifting) ball_eq_empty centre_in_ball empty_iff)
qed

lemma \<omega>_limit_set_in_compact_connected:
  shows "connected (\<omega>_limit_set x)"
  unfolding connected_closed_set[OF \<omega>_limit_set_closed]
proof clarsimp
  fix Apre Bpre
  assume pre: "closed Apre" "Apre \<union> Bpre = \<omega>_limit_set x" "closed Bpre"
    "Apre \<noteq> {}" "Bpre \<noteq> {}" "Apre \<inter> Bpre = {}"
    (* TODO: this move is very strange *)
  then obtain A B where "Apre \<subseteq> A" "Bpre \<subseteq> B" "open A" "open B" and disj:"A \<inter> B = {}"
    by (meson t4_space)
  then have "\<omega>_limit_set x \<subseteq> A \<union> B"
    "\<omega>_limit_set x \<inter> A \<noteq> {}" "\<omega>_limit_set x \<inter> B \<noteq> {}" using pre by auto
  then obtain p q where
    p: "\<omega>_limit_point x p" "p \<in> A"
    and q: "\<omega>_limit_point x q" "q \<in> B"
    using \<omega>_limit_set_def by auto
  from \<omega>_limit_pointE[OF p(1)]
  obtain ps where ps: "filterlim ps at_top sequentially"
    "(flow0 x \<circ> ps) \<longlonglongrightarrow> p" "\<forall>n. 0 \<le> ps n" by blast
  from \<omega>_limit_pointE[OF q(1)]
  obtain qs where qs: "filterlim qs at_top sequentially"
    "(flow0 x \<circ> qs) \<longlonglongrightarrow> q" "\<forall>n. 0 \<le> qs n" by blast
  have "\<forall>n. \<exists>\<^sub>F t in at_top. flow0 x t \<notin> A \<and> flow0 x t \<notin> B" unfolding frequently_at_top
  proof safe
    fix dummy mpre
    obtain m where "m \<ge> (0::real)" "m > mpre"
      by (meson approximation_preproc_push_neg(1) gt_ex le_cases order_trans) 
    from ps obtain a where a:"a > m" "(flow0 x a) \<in> A"
      using \<open>open A\<close> p unfolding tendsto_def filterlim_at_top eventually_sequentially
      by (metis approximation_preproc_push_neg(1) comp_apply gt_ex le_cases order_trans)
    from qs obtain b where b:"b > a" "(flow0 x b) \<in> B"
      using \<open>open B\<close> q unfolding tendsto_def filterlim_at_top eventually_sequentially
      by (metis approximation_preproc_push_neg(1) comp_apply gt_ex le_cases order_trans)
    have "continuous_on {a..b} (flow0 x)"
      by (metis Icc_subset_Ici_iff \<open>0 \<le> m\<close> \<open>m < a\<close> approximation_preproc_push_neg(2) atMost_iff atMost_subset_iff continuous_on_subset le_cases local.flow_continuous_on props(1) subset_eq)
    from connected_continuous_image[OF this connected_Icc]
    have c:"connected (flow0 x ` {a..b})" .
    have "\<exists>t\<in> {a..b}. flow0 x t \<notin> A \<and> flow0 x t \<notin> B"
    proof (rule ccontr)
      assume "\<not> (\<exists>t\<in>{a..b}. flow0 x t \<notin> A \<and> flow0 x t \<notin> B)"
      then have "flow0 x ` {a..b} \<subseteq> A \<union> B" by blast
      from topological_space_class.connectedD[OF c \<open>open A\<close> \<open>open B\<close> _ this]
      show False using a b disj by force
    qed
    thus "\<exists>n>mpre. flow0 x n \<notin> A \<and> flow0 x n \<notin> B"
      by (smt \<open>mpre < m\<close> a(1) atLeastAtMost_iff)
  qed
  from frequently_at_topE'[OF this filterlim_real_sequentially]
  obtain s where s: "\<forall>i. flow0 x (s i) \<notin> A \<and> flow0 x (s i) \<notin> B"
    "strict_mono s" "\<And>n. real n \<le> s n" by blast
  then have "\<forall>n. (flow0 x \<circ> s) n \<in> K"
    by (smt atLeast_iff comp_apply flowimg image_subset_iff of_nat_0_le_iff trapped_forward_def x(2))
  from seq_compactE[OF props(2) this]
  obtain r l where r: "l \<in> K" "strict_mono r" "(flow0 x \<circ> s \<circ> r) \<longlonglongrightarrow> l" by blast
  have "filterlim s at_top sequentially"
    using s filterlim_at_top_mono filterlim_real_sequentially not_eventuallyD by blast 
  from filterlim_at_top_strict_mono[OF s(2) r(2) this]
  have "filterlim (s \<circ> r) at_top sequentially" .
  then have "\<omega>_limit_point x l" unfolding \<omega>_limit_point_def using props(1) r
    by (metis comp_assoc)
  moreover have "l \<notin> A" using s(1) r(3) \<open>open A\<close> unfolding tendsto_def by auto
  moreover have "l \<notin> B" using s(1) r(3) \<open>open B\<close> unfolding tendsto_def by auto
  ultimately show False using \<open>\<omega>_limit_set x \<subseteq> A \<union> B\<close> unfolding \<omega>_limit_set_def
    by auto
qed

lemma \<omega>_limit_set_in_compact_\<omega>_limit_set_contained:
  shows "\<forall>y \<in> \<omega>_limit_set x. \<omega>_limit_set y \<subseteq> \<omega>_limit_set x"
proof safe
  fix y z
  assume "y \<in> \<omega>_limit_set x" "z \<in> \<omega>_limit_set y"
  then have "\<omega>_limit_point y z" unfolding \<omega>_limit_set_def by auto
  from \<omega>_limit_pointE[OF this]
  obtain s where s: "(flow0 y \<circ> s) \<longlonglongrightarrow> z" .
  have "\<forall>n. (flow0 y \<circ> s) n \<in> \<omega>_limit_set x"
    using \<open>y \<in> \<omega>_limit_set x\<close> invariant_def
      \<omega>_limit_set_in_compact_existence \<omega>_limit_set_invariant trapped_iff_on_existence_ivl0
    by force
  thus "z \<in> \<omega>_limit_set x" using closed_sequential_limits s \<omega>_limit_set_closed
    by blast
qed

lemma \<omega>_limit_set_in_compact_\<alpha>_limit_set_contained:
  assumes zpx: "z \<in> \<omega>_limit_set x"
  shows "\<alpha>_limit_set z \<subseteq> \<omega>_limit_set x"
proof
  fix w assume "w \<in> \<alpha>_limit_set z"
  then obtain s where s: "(flow0 z \<circ> s) \<longlonglongrightarrow> w"
    unfolding \<alpha>_limit_set_def \<alpha>_limit_point_def
    by auto
  from \<omega>_limit_set_invariant have "invariant (\<omega>_limit_set x)" .
  then have "\<forall>n. (flow0 z \<circ> s) n \<in> \<omega>_limit_set x"
    using \<omega>_limit_set_in_compact_existence[OF zpx] zpx
    using invariant_def trapped_iff_on_existence_ivl0 by fastforce
  from closed_sequentially[OF \<omega>_limit_set_closed this s]
  show "w \<in> \<omega>_limit_set x" .
qed

end

text \<open> Fundamental properties of the negative limit set \<close>

end context auto_ll_on_open begin

context
  fixes x K
  assumes x: "x \<in> X" "trapped_backward x K"
  assumes K: "compact K" "K \<subseteq> X"
begin

private lemma xrev: "x \<in> X" "rev.trapped_forward x K"
  using trapped_backward_iff_rev_trapped_forward x(2) 
  by (auto simp: rev_existence_ivl_eq0 rev_eq_flow x(1))

lemma \<alpha>_limit_set_in_compact_subset: "\<alpha>_limit_set x \<subseteq> K"
  and \<alpha>_limit_set_in_compact_compact: "compact (\<alpha>_limit_set x)"
  and \<alpha>_limit_set_in_compact_nonempty: "\<alpha>_limit_set x \<noteq> {}"
  and \<alpha>_limit_set_in_compact_connected: "connected (\<alpha>_limit_set x)"
  and \<alpha>_limit_set_in_compact_\<alpha>_limit_set_contained:
  "\<forall>y \<in> \<alpha>_limit_set x. \<alpha>_limit_set y \<subseteq> \<alpha>_limit_set x"
  and \<alpha>_limit_set_in_compact_tendsto: "((\<lambda>t. infdist (flow0 x t) (\<alpha>_limit_set x)) \<longlongrightarrow> 0) at_bot"
  using rev.\<omega>_limit_set_in_compact_subset[OF K xrev]
  using rev.\<omega>_limit_set_in_compact_compact[OF K xrev]
  using rev.\<omega>_limit_set_in_compact_nonempty[OF K xrev]
  using rev.\<omega>_limit_set_in_compact_connected[OF K xrev]
  using rev.\<omega>_limit_set_in_compact_\<omega>_limit_set_contained[OF K xrev]
  using rev.\<omega>_limit_set_in_compact_tendsto[OF K xrev]
  unfolding invariant_eq_rev \<alpha>_limit_set_eq_rev existence_ivl_eq_rev flow_eq_rev0 filterlim_at_bot_mirror
    minus_minus
  .

lemma \<alpha>_limit_set_in_compact_existence:
  shows "\<And>y. y \<in> \<alpha>_limit_set x \<Longrightarrow> existence_ivl0 y = UNIV"
  using rev.\<omega>_limit_set_in_compact_existence[OF K xrev]
  unfolding \<alpha>_limit_set_eq_rev existence_ivl_eq_rev0
  by auto

end
end

end
