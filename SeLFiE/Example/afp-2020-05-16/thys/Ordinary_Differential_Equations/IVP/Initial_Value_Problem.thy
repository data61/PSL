section\<open>Initial Value Problems\<close>
theory Initial_Value_Problem
  imports
    "../ODE_Auxiliarities"
    "../Library/Interval_Integral_HK"
    "../Library/Gronwall"
begin

lemma clamp_le[simp]: "x \<le> a \<Longrightarrow> clamp a b x = a" for x::"'a::ordered_euclidean_space"
  by (auto simp: clamp_def eucl_le[where 'a='a] intro!: euclidean_eqI[where 'a='a])

lemma clamp_ge[simp]: "a \<le> b \<Longrightarrow> b \<le> x \<Longrightarrow> clamp a b x = b" for x::"'a::ordered_euclidean_space"
  by (force simp: clamp_def eucl_le[where 'a='a] not_le not_less  intro!: euclidean_eqI[where 'a='a])

abbreviation cfuncset :: "'a::topological_space set \<Rightarrow> 'b::metric_space set \<Rightarrow> ('a \<Rightarrow>\<^sub>C 'b) set"
  (infixr "\<rightarrow>\<^sub>C" 60)
  where "A \<rightarrow>\<^sub>C B \<equiv> PiC A (\<lambda>_. B)"

lemma closed_segment_translation_zero: "z \<in> {z + a--z + b} \<longleftrightarrow> 0 \<in> {a -- b}"
  by (metis add.right_neutral closed_segment_translation_eq)

lemma closed_segment_subset_interval: "is_interval T \<Longrightarrow> a \<in> T \<Longrightarrow> b \<in> T \<Longrightarrow> closed_segment a b \<subseteq> T"
  by (rule closed_segment_subset) (auto intro!: closed_segment_subset is_interval_convex)

definition half_open_segment::"'a::real_vector \<Rightarrow> 'a \<Rightarrow> 'a set" ("(1{_--<_})")
  where "half_open_segment a b = {a -- b} - {b}"

lemma half_open_segment_real:
  fixes a b::real
  shows "{a --< b} = (if a \<le> b then {a ..< b} else {b <.. a})"
  by (auto simp: half_open_segment_def closed_segment_eq_real_ivl)

lemma closure_half_open_segment:
  fixes a b::real
  shows "closure {a --< b} = (if a = b then {} else {a -- b})"
  unfolding closed_segment_eq_real_ivl if_distrib half_open_segment_real
  unfolding if_distribR
  by simp

lemma half_open_segment_subset[intro, simp]:
  "{t0--<t1} \<subseteq> {t0 -- t1}"
  "x \<in> {t0--<t1} \<Longrightarrow> x \<in> {t0 -- t1}"
  by (auto simp: half_open_segment_def)

lemma half_open_segment_closed_segmentI:
  "t \<in> {t0 -- t1} \<Longrightarrow> t \<noteq> t1 \<Longrightarrow> t \<in> {t0 --< t1}"
  by (auto simp: half_open_segment_def)

lemma islimpt_half_open_segment:
  fixes t0 t1 s::real
  assumes "t0 \<noteq> t1" "s \<in> {t0--t1}"
  shows "s islimpt {t0--<t1}"
proof -
  have "s islimpt {t0..<t1}" if "t0 \<le> s" "s \<le> t1" for s
  proof -
    have *: "{t0..<t1} - {s} = {t0..<s} \<union> {s<..<t1}"
      using that by auto
    show ?thesis
      using that \<open>t0 \<noteq> t1\<close> *
      by (cases "t0 = s") (auto simp: islimpt_in_closure)
  qed
  moreover have "s islimpt {t1<..t0}" if "t1 \<le> s" "s \<le> t0" for s
  proof -
    have *: "{t1<..t0} - {s} = {t1<..<s} \<union> {s<..t0}"
      using that by auto
    show ?thesis
      using that \<open>t0 \<noteq> t1\<close> *
      by (cases "t0 = s") (auto simp: islimpt_in_closure)
  qed
  ultimately show ?thesis using assms
    by (auto simp: half_open_segment_real closed_segment_eq_real_ivl)
qed

lemma
  mem_half_open_segment_eventually_in_closed_segment:
  fixes t::real
  assumes "t \<in> {t0--<t1'}"
  shows "\<forall>\<^sub>F t1' in at t1' within {t0--<t1'}. t \<in> {t0--t1'}"
  unfolding half_open_segment_real
proof (split if_split, safe)
  assume le: "t0 \<le> t1'"
  with assms have t: "t0 \<le> t" "t < t1'"
    by (auto simp: half_open_segment_real)
  then have "\<forall>\<^sub>F t1' in at t1' within {t0..<t1'}. t0 \<le> t"
    by simp
  moreover
  from tendsto_ident_at \<open>t < t1'\<close>
  have "\<forall>\<^sub>F t1' in at t1' within {t0..<t1'}. t < t1'"
    by (rule order_tendstoD)
  ultimately show "\<forall>\<^sub>F t1' in at t1' within {t0..<t1'}. t \<in> {t0--t1'}"
    by eventually_elim (auto simp add: closed_segment_eq_real_ivl)
next
  assume le: "\<not> t0 \<le> t1'"
  with assms have t: "t \<le> t0" "t1' < t"
    by (auto simp: half_open_segment_real)
  then have "\<forall>\<^sub>F t1' in at t1' within {t1'<..t0}. t \<le> t0"
    by simp
  moreover
  from tendsto_ident_at \<open>t1' < t\<close>
  have "\<forall>\<^sub>F t1' in at t1' within {t1'<..t0}. t1' < t"
    by (rule order_tendstoD)
  ultimately show "\<forall>\<^sub>F t1' in at t1' within {t1'<..t0}. t \<in> {t0--t1'}"
    by eventually_elim (auto simp add: closed_segment_eq_real_ivl)
qed

lemma closed_segment_half_open_segment_subsetI:
  fixes x::real shows "x \<in> {t0--<t1} \<Longrightarrow> {t0--x} \<subseteq> {t0--<t1}"
  by (auto simp: half_open_segment_real closed_segment_eq_real_ivl split: if_split_asm)

lemma dist_component_le:
  fixes x y::"'a::euclidean_space"
  assumes "i \<in> Basis"
  shows "dist (x \<bullet> i) (y \<bullet> i) \<le> dist x y"
  using assms
  by (auto simp: euclidean_dist_l2[of x y] intro: member_le_L2_set)

lemma sum_inner_Basis_one: "i \<in> Basis \<Longrightarrow> (\<Sum>x\<in>Basis. x \<bullet> i) = 1"
  by (subst sum.mono_neutral_right[where S="{i}"])
    (auto simp: inner_not_same_Basis)

lemma cball_in_cbox:
  fixes y::"'a::euclidean_space"
  shows "cball y r \<subseteq> cbox (y - r *\<^sub>R One) (y + r *\<^sub>R One)"
  unfolding scaleR_sum_right interval_cbox cbox_def
proof safe
  fix x i::'a assume "i \<in> Basis" "x \<in> cball y r"
  with dist_component_le[OF \<open>i \<in> Basis\<close>, of y x]
  have "dist (y \<bullet> i) (x \<bullet> i) \<le> r" by (simp add: mem_cball)
  thus "(y - sum ((*\<^sub>R) r) Basis) \<bullet> i \<le> x \<bullet> i"
    "x \<bullet> i \<le> (y + sum ((*\<^sub>R) r) Basis) \<bullet> i"
    by (auto simp add: inner_diff_left inner_add_left inner_sum_left
      sum_distrib_left[symmetric] sum_inner_Basis_one \<open>i\<in>Basis\<close> dist_real_def)
qed

lemma centered_cbox_in_cball:
  shows "cbox (- r *\<^sub>R One) (r *\<^sub>R One::'a::euclidean_space) \<subseteq>
    cball 0 (sqrt(DIM('a)) * r)"
proof
  fix x::'a
  have "norm x \<le> sqrt(DIM('a)) * infnorm x"
  by (rule norm_le_infnorm)
  also
  assume "x \<in> cbox (- r *\<^sub>R One) (r *\<^sub>R One)"
  hence "infnorm x \<le> r"
    by (auto simp: infnorm_def mem_box intro!: cSup_least)
  finally show "x \<in> cball 0 (sqrt(DIM('a)) * r)"
    by (auto simp: dist_norm mult_left_mono mem_cball)
qed


subsection \<open>Solutions of IVPs \label{sec:solutions}\<close>

definition
  solves_ode :: "(real \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> (real \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> bool"
  (infix "(solves'_ode)" 50)
where
  "(y solves_ode f) T X \<longleftrightarrow> (y has_vderiv_on (\<lambda>t. f t (y t))) T \<and> y \<in> T \<rightarrow> X"

lemma solves_odeI:
  assumes solves_ode_vderivD: "(y has_vderiv_on (\<lambda>t. f t (y t))) T"
    and solves_ode_domainD: "\<And>t. t \<in> T \<Longrightarrow> y t \<in> X"
  shows "(y solves_ode f) T X"
  using assms
  by (auto simp: solves_ode_def)

lemma solves_odeD:
  assumes "(y solves_ode f) T X"
  shows solves_ode_vderivD: "(y has_vderiv_on (\<lambda>t. f t (y t))) T"
    and solves_ode_domainD: "\<And>t. t \<in> T \<Longrightarrow> y t \<in> X"
  using assms
  by (auto simp: solves_ode_def)

lemma solves_ode_continuous_on: "(y solves_ode f) T X \<Longrightarrow> continuous_on T y"
  by (auto intro!: vderiv_on_continuous_on simp: solves_ode_def)

lemma solves_ode_congI:
  assumes "(x solves_ode f) T X"
  assumes "\<And>t. t \<in> T \<Longrightarrow> x t = y t"
  assumes "\<And>t. t \<in> T \<Longrightarrow> f t (x t) = g t (x t)"
  assumes "T = S" "X = Y"
  shows "(y solves_ode g) S Y"
  using assms
  by (auto simp: solves_ode_def Pi_iff)

lemma solves_ode_cong[cong]:
  assumes "\<And>t. t \<in> T \<Longrightarrow> x t = y t"
  assumes "\<And>t. t \<in> T \<Longrightarrow> f t (x t) = g t (x t)"
  assumes "T = S" "X = Y"
  shows "(x solves_ode f) T X \<longleftrightarrow> (y solves_ode g) S Y"
  using assms
  by (auto simp: solves_ode_def Pi_iff)

lemma solves_ode_on_subset:
  assumes "(x solves_ode f) S Y"
  assumes "T \<subseteq> S" "Y \<subseteq> X"
  shows "(x solves_ode f) T X"
  using assms
  by (auto simp: solves_ode_def has_vderiv_on_subset)

lemma preflect_solution:
  assumes "t0 \<in> T"
  assumes sol: "((\<lambda>t. x (preflect t0 t)) solves_ode (\<lambda>t x. - f (preflect t0 t) x)) (preflect t0 ` T) X"
  shows "(x solves_ode f) T X"
proof (rule solves_odeI)
  from solves_odeD[OF sol]
  have xm_deriv: "(x o preflect t0 has_vderiv_on (\<lambda>t. - f (preflect t0 t) (x (preflect t0 t)))) (preflect t0 ` T)"
    and xm_mem: "t \<in> preflect t0 ` T \<Longrightarrow> x (preflect t0 t) \<in> X" for t
    by simp_all
  have "(x o preflect t0 o preflect t0 has_vderiv_on (\<lambda>t. f t (x t))) T"
    apply (rule has_vderiv_on_eq_rhs)
    apply (rule has_vderiv_on_compose)
    apply (rule xm_deriv)
    apply (auto simp: preflect_def intro!: derivative_intros)
    done
  then show "(x has_vderiv_on (\<lambda>t. f t (x t))) T"
    by (simp add: preflect_def)
  show "x t \<in> X" if "t \<in> T" for t
    using that xm_mem[of "preflect t0 t"]
    by (auto simp: preflect_def)
qed

lemma solution_preflect:
  assumes "t0 \<in> T"
  assumes sol: "(x solves_ode f) T X"
  shows "((\<lambda>t. x (preflect t0 t)) solves_ode (\<lambda>t x. - f (preflect t0 t) x)) (preflect t0 ` T) X"
  using sol \<open>t0 \<in> T\<close>
  by (simp_all add: preflect_def image_image preflect_solution[of t0])

lemma solution_eq_preflect_solution:
  assumes "t0 \<in> T"
  shows "(x solves_ode f) T X \<longleftrightarrow> ((\<lambda>t. x (preflect t0 t)) solves_ode (\<lambda>t x. - f (preflect t0 t) x)) (preflect t0 ` T) X"
  using solution_preflect[OF \<open>t0 \<in> T\<close>] preflect_solution[OF \<open>t0 \<in> T\<close>]
  by blast

lemma shift_autonomous_solution:
  assumes sol: "(x solves_ode f) T X"
  assumes auto: "\<And>s t. s \<in> T \<Longrightarrow> f s (x s) = f t (x s)"
  shows "((\<lambda>t. x (t + t0)) solves_ode f) ((\<lambda>t. t - t0) ` T) X"
  using solves_odeD[OF sol]
  apply (intro solves_odeI)
  apply (rule has_vderiv_on_compose'[of x, THEN has_vderiv_on_eq_rhs])
  apply (auto simp: image_image intro!: auto derivative_intros)
  done

lemma solves_ode_singleton: "y t0 \<in> X \<Longrightarrow> (y solves_ode f) {t0} X"
  by (auto intro!: solves_odeI has_vderiv_on_singleton)

subsubsection\<open>Connecting solutions\<close>
text\<open>\label{sec:combining-solutions}\<close>

lemma connection_solves_ode:
  assumes x: "(x solves_ode f) T X"
  assumes y: "(y solves_ode g) S Y"
  assumes conn_T: "closure S \<inter> closure T \<subseteq> T"
  assumes conn_S: "closure S \<inter> closure T \<subseteq> S"
  assumes conn_x: "\<And>t. t \<in> closure S \<Longrightarrow> t \<in> closure T \<Longrightarrow> x t = y t"
  assumes conn_f: "\<And>t. t \<in> closure S \<Longrightarrow> t \<in> closure T \<Longrightarrow> f t (y t) = g t (y t)"
  shows "((\<lambda>t. if t \<in> T then x t else y t) solves_ode (\<lambda>t. if t \<in> T then f t else g t)) (T \<union> S) (X \<union> Y)"
proof (rule solves_odeI)
  from solves_odeD(2)[OF x] solves_odeD(2)[OF y]
  show "t \<in> T \<union> S \<Longrightarrow> (if t \<in> T then x t else y t) \<in> X \<union> Y" for t
    by auto
  show "((\<lambda>t. if t \<in> T then x t else y t) has_vderiv_on (\<lambda>t. (if t \<in> T then f t else g t) (if t \<in> T then x t else y t))) (T \<union> S)"
    apply (rule has_vderiv_on_If[OF refl, THEN has_vderiv_on_eq_rhs])
    unfolding Un_absorb2[OF conn_T] Un_absorb2[OF conn_S]
    apply (rule solves_odeD(1)[OF x])
    apply (rule solves_odeD(1)[OF y])
    apply (simp_all add: conn_T conn_S Un_absorb2 conn_x conn_f)
    done
qed

lemma
  solves_ode_subset_range:
  assumes x: "(x solves_ode f) T X"
  assumes s: "x ` T \<subseteq> Y"
  shows "(x solves_ode f) T Y"
  using assms
  by (auto intro!: solves_odeI dest!: solves_odeD)


subsection \<open>unique solution with initial value\<close>

definition
  usolves_ode_from :: "(real \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> (real \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> real \<Rightarrow> real set \<Rightarrow> 'a set \<Rightarrow> bool"
  ("((_) usolves'_ode (_) from (_))" [10, 10, 10] 10)
  \<comment> \<open>TODO: no idea about mixfix and precedences, check this!\<close>
where
  "(y usolves_ode f from t0) T X \<longleftrightarrow> (y solves_ode f) T X \<and> t0 \<in> T \<and> is_interval T \<and>
    (\<forall>z T'. t0 \<in> T' \<and> is_interval T' \<and> T' \<subseteq> T \<and> (z solves_ode f) T' X \<longrightarrow> z t0 = y t0 \<longrightarrow> (\<forall>t \<in> T'. z t = y t))"

text \<open>uniqueness of solution can depend on domain \<open>X\<close>:\<close>

lemma
  "((\<lambda>_. 0::real) usolves_ode (\<lambda>_. sqrt) from 0) {0..} {0}"
    "((\<lambda>t. t\<^sup>2 / 4) solves_ode (\<lambda>_. sqrt)) {0..} {0..}"
    "(\<lambda>t. t\<^sup>2 / 4) 0 = (\<lambda>_. 0::real) 0"
  by (auto intro!: derivative_eq_intros
    simp: has_vderiv_on_def has_vector_derivative_def usolves_ode_from_def solves_ode_def
      is_interval_ci real_sqrt_divide)

text \<open>TODO: show that if solution stays in interior, then domain can be enlarged! (?)\<close>

lemma usolves_odeD:
  assumes "(y usolves_ode f from t0) T X"
  shows "(y solves_ode f) T X"
    and "t0 \<in> T"
    and "is_interval T"
    and "\<And>z T' t. t0 \<in> T' \<Longrightarrow> is_interval T' \<Longrightarrow> T' \<subseteq> T \<Longrightarrow>(z solves_ode f) T' X \<Longrightarrow> z t0 = y t0 \<Longrightarrow> t \<in> T' \<Longrightarrow> z t = y t"
  using assms
  unfolding usolves_ode_from_def
  by blast+

lemma usolves_ode_rawI:
  assumes "(y solves_ode f) T X" "t0 \<in> T" "is_interval T"
  assumes "\<And>z T' t. t0 \<in> T' \<Longrightarrow> is_interval T' \<Longrightarrow> T' \<subseteq> T \<Longrightarrow> (z solves_ode f) T' X \<Longrightarrow> z t0 = y t0 \<Longrightarrow> t \<in> T' \<Longrightarrow> z t = y t"
  shows "(y usolves_ode f from t0) T X"
  using assms
  unfolding usolves_ode_from_def
  by blast

lemma usolves_odeI:
  assumes "(y solves_ode f) T X" "t0 \<in> T" "is_interval T"
  assumes usol: "\<And>z t. {t0 -- t} \<subseteq> T \<Longrightarrow> (z solves_ode f) {t0 -- t} X \<Longrightarrow> z t0 = y t0 \<Longrightarrow> z t = y t"
  shows "(y usolves_ode f from t0) T X"
proof (rule usolves_ode_rawI; fact?)
  fix z T' t
  assume T': "t0 \<in> T'" "is_interval T'" "T' \<subseteq> T"
    and z: "(z solves_ode f) T' X" and iv: "z t0 = y t0" and t: "t \<in> T'"
  have subset_T': "{t0 -- t} \<subseteq> T'"
    by (rule closed_segment_subset_interval; fact)
  with z have sol_cs: "(z solves_ode f) {t0 -- t} X"
    by (rule solves_ode_on_subset[OF _ _ order_refl])
  from subset_T' have subset_T: "{t0 -- t} \<subseteq> T"
    using \<open>T' \<subseteq> T\<close> by simp
  from usol[OF subset_T sol_cs iv]
  show "z t = y t" by simp
qed

lemma is_interval_singleton[intro,simp]: "is_interval {t0}"
  by (auto simp: is_interval_def intro!: euclidean_eqI[where 'a='a])

lemma usolves_ode_singleton: "x t0 \<in> X \<Longrightarrow> (x usolves_ode f from t0) {t0} X"
  by (auto intro!: usolves_odeI solves_ode_singleton)

lemma usolves_ode_congI:
  assumes x: "(x usolves_ode f from t0) T X"
  assumes "\<And>t. t \<in> T \<Longrightarrow> x t = y t"
  assumes "\<And>t y. t \<in> T \<Longrightarrow> y \<in> X \<Longrightarrow> f t y = g t y"\<comment> \<open>TODO: weaken this assumption?!\<close>
  assumes "t0 = s0"
  assumes "T = S"
  assumes "X = Y"
  shows "(y usolves_ode g from s0) S Y"
proof (rule usolves_ode_rawI)
  from assms x have "(y solves_ode f) S Y"
    by (auto simp add: usolves_ode_from_def)
  then show "(y solves_ode g) S Y"
    by (rule solves_ode_congI) (use assms in \<open>auto simp: usolves_ode_from_def dest!: solves_ode_domainD\<close>)
  from assms show "s0 \<in> S" "is_interval S"
    by (auto simp add: usolves_ode_from_def)
next
  fix z T' t
  assume hyps: "s0 \<in> T'" "is_interval T'" "T' \<subseteq> S" "(z solves_ode g) T' Y" "z s0 = y s0" "t \<in> T'"
  from \<open>(z solves_ode g) T' Y\<close>
  have zsol: "(z solves_ode f) T' Y"
    by (rule solves_ode_congI) (use assms hyps in \<open>auto dest!: solves_ode_domainD\<close>)
  have "z t = x t"
    by (rule x[THEN usolves_odeD(4),where T' = T'])
      (use zsol \<open>s0 \<in> T'\<close> \<open>is_interval T'\<close> \<open>T' \<subseteq> S\<close> \<open>T = S\<close> \<open>z s0 = y s0\<close> \<open>t \<in> T'\<close> assms in auto)
  also have "y t = x t" using assms \<open>t \<in> T'\<close> \<open>T' \<subseteq> S\<close> \<open>T = S\<close> by auto
  finally show "z t = y t" by simp
qed


lemma usolves_ode_cong[cong]:
  assumes "\<And>t. t \<in> T \<Longrightarrow> x t = y t"
  assumes "\<And>t y. t \<in> T \<Longrightarrow> y \<in> X \<Longrightarrow> f t y = g t y"\<comment> \<open>TODO: weaken this assumption?!\<close>
  assumes "t0 = s0"
  assumes "T = S"
  assumes "X = Y"
  shows "(x usolves_ode f from t0) T X \<longleftrightarrow> (y usolves_ode g from s0) S Y"
  apply (rule iffI)
  subgoal by (rule usolves_ode_congI[OF _ assms]; assumption)
  subgoal by (metis assms(1) assms(2) assms(3) assms(4) assms(5) usolves_ode_congI)
  done

lemma shift_autonomous_unique_solution:
  assumes usol: "(x usolves_ode f from t0) T X"
  assumes auto: "\<And>s t x. x \<in> X \<Longrightarrow> f s x = f t x"
  shows "((\<lambda>t. x (t + t0 - t1)) usolves_ode f from t1) ((+) (t1 - t0) ` T) X"
proof (rule usolves_ode_rawI)
  from usolves_odeD[OF usol]
  have sol: "(x solves_ode f) T X"
    and "t0 \<in> T"
    and "is_interval T"
    and unique: "t0 \<in> T' \<Longrightarrow> is_interval T' \<Longrightarrow> T' \<subseteq> T \<Longrightarrow> (z solves_ode f) T' X \<Longrightarrow> z t0 = x t0 \<Longrightarrow> t \<in> T' \<Longrightarrow> z t = x t"
    for z T' t
    by blast+
  have "(\<lambda>t. t + t1 - t0) = (+) (t1 - t0)"
    by (auto simp add: algebra_simps)
  with shift_autonomous_solution[OF sol auto, of "t0 - t1"] solves_odeD[OF sol]
  show "((\<lambda>t. x (t + t0 - t1)) solves_ode f) ((+) (t1 - t0) ` T) X"
    by (simp add: algebra_simps)
  from \<open>t0 \<in> T\<close> show "t1 \<in> (+) (t1 - t0) ` T" by auto
  from \<open>is_interval T\<close>
  show "is_interval ((+) (t1 - t0) ` T)"
    by simp
  fix z T' t
  assume z: "(z solves_ode f) T' X"
    and t0': "t1 \<in> T'" "T' \<subseteq> (+) (t1 - t0) ` T"
    and shift: "z t1 = x (t1 + t0 - t1)"
    and t: "t \<in> T'"
    and ivl: "is_interval T'"

  let ?z = "(\<lambda>t. z (t + (t1 - t0)))"

  have "(?z solves_ode f) ((\<lambda>t. t - (t1 - t0)) ` T') X"
    apply (rule shift_autonomous_solution[OF z, of "t1 - t0"])
    using solves_odeD[OF z]
    by (auto intro!: auto)
  with _ _ _ have "?z ((t + (t0 - t1))) = x (t + (t0 - t1))"
    apply (rule unique[where z = ?z ])
    using shift t t0' ivl
    by auto
  then show "z t = x (t + t0 - t1)"
    by (simp add: algebra_simps)
qed

lemma three_intervals_lemma:
  fixes a b c::real
  assumes a: "a \<in> A - B"
    and b: "b \<in> B - A"
    and c: "c \<in> A \<inter> B"
    and iA: "is_interval A" and iB: "is_interval B"
    and aI: "a \<in> I"
    and bI: "b \<in> I"
    and iI: "is_interval I"
  shows "c \<in> I"
  apply (rule mem_is_intervalI[OF iI aI bI])
  using iA iB
  apply (auto simp: is_interval_def)
  apply (metis Diff_iff Int_iff a b c le_cases)
  apply (metis Diff_iff Int_iff a b c le_cases)
  done

lemma connection_usolves_ode:
  assumes x: "(x usolves_ode f from tx) T X"
  assumes y: "\<And>t. t \<in> closure S \<inter> closure T \<Longrightarrow> (y usolves_ode g from t) S X"
  assumes conn_T: "closure S \<inter> closure T \<subseteq> T"
  assumes conn_S: "closure S \<inter> closure T \<subseteq> S"
  assumes conn_t: "t \<in> closure S \<inter> closure T"
  assumes conn_x: "\<And>t. t \<in> closure S \<Longrightarrow> t \<in> closure T \<Longrightarrow> x t = y t"
  assumes conn_f: "\<And>t x. t \<in> closure S \<Longrightarrow> t \<in> closure T \<Longrightarrow> x \<in> X \<Longrightarrow> f t x = g t x"
  shows "((\<lambda>t. if t \<in> T then x t else y t) usolves_ode (\<lambda>t. if t \<in> T then f t else g t) from tx) (T \<union> S) X"
  apply (rule usolves_ode_rawI)
  apply (subst Un_absorb[of X, symmetric])
  apply (rule connection_solves_ode[OF usolves_odeD(1)[OF x] usolves_odeD(1)[OF y[OF conn_t]] conn_T conn_S conn_x conn_f])
  subgoal by assumption
  subgoal by assumption
  subgoal by assumption
  subgoal by assumption
  subgoal using solves_odeD(2)[OF usolves_odeD(1)[OF x]] conn_T by (auto simp add: conn_x[symmetric])
  subgoal using usolves_odeD(2)[OF x] by auto
  subgoal using usolves_odeD(3)[OF x] usolves_odeD(3)[OF y]
    apply (rule is_real_interval_union)
    using conn_T conn_S conn_t by auto
  subgoal premises prems for z TS' s
  proof -
    from \<open>(z solves_ode _) _ _\<close>
    have "(z solves_ode (\<lambda>t. if t \<in> T then f t else g t)) (T \<inter> TS') X"
      by (rule solves_ode_on_subset) auto
    then have z_f: "(z solves_ode f) (T \<inter> TS') X"
      by (subst solves_ode_cong) auto

    from prems(4)
    have "(z solves_ode (\<lambda>t. if t \<in> T then f t else g t)) (S \<inter> TS') X"
      by (rule solves_ode_on_subset) auto
    then have z_g: "(z solves_ode g) (S \<inter> TS') X"
      apply (rule solves_ode_congI)
      subgoal by simp
      subgoal by clarsimp (meson closure_subset conn_f contra_subsetD prems(4) solves_ode_domainD)
      subgoal by simp
      subgoal by simp
      done
    have "tx \<in> T" using assms using usolves_odeD(2)[OF x] by auto

    have "z tx = x tx" using assms prems
      by (simp add: \<open>tx \<in> T\<close>)

    from usolves_odeD(4)[OF x _ _ _ \<open>(z solves_ode f) _ _\<close>, of s] prems
    have "z s = x s" if "s \<in> T" using that \<open>tx \<in> T\<close> \<open>z tx = x tx\<close>
      by (auto simp: is_interval_Int usolves_odeD(3)[OF x] \<open>is_interval TS'\<close>)

    moreover

    {
      assume "s \<notin> T"
      then have "s \<in> S" using prems assms by auto
      {
        assume "tx \<notin> S"
        then have "tx \<in> T - S" using \<open>tx \<in> T\<close> by simp
        moreover have "s \<in> S - T" using \<open>s \<notin> T\<close> \<open>s \<in> S\<close> by blast
        ultimately have "t \<in> TS'"
          apply (rule three_intervals_lemma)
          subgoal using assms by auto
          subgoal using usolves_odeD(3)[OF x] .
          subgoal using usolves_odeD(3)[OF y[OF conn_t]] .
          subgoal using \<open>tx \<in> TS'\<close> .
          subgoal using \<open>s \<in> TS'\<close> .
          subgoal using \<open>is_interval TS'\<close> .
          done
        with assms have t: "t \<in> closure S \<inter> closure T \<inter> TS'" by simp

        then have "t \<in> S" "t \<in> T" "t \<in> TS'" using assms by auto
        have "z t = x t"
          apply (rule usolves_odeD(4)[OF x _ _ _ z_f, of t])
          using \<open>t \<in> TS'\<close> \<open>t \<in> T\<close> prems assms \<open>tx \<in> T\<close> usolves_odeD(3)[OF x]
          by (auto intro!: is_interval_Int)
        with assms have "z t = y t" using t by auto

        from usolves_odeD(4)[OF y[OF conn_t] _ _ _ z_g, of s] prems
        have "z s = y s" using \<open>s \<notin> T\<close> assms \<open>z t = y t\<close> t \<open>t \<in> S\<close>
          \<open>is_interval TS'\<close> usolves_odeD(3)[OF y[OF conn_t]]
          by (auto simp: is_interval_Int)
      } moreover {
        assume "tx \<in> S"
        with prems closure_subset \<open>tx \<in> T\<close>
        have tx: "tx \<in> closure S \<inter> closure T \<inter> TS'" by force

        then have "tx \<in> S" "tx \<in> T" "tx \<in> TS'" using assms by auto
        have "z tx = x tx"
          apply (rule usolves_odeD(4)[OF x _ _ _ z_f, of tx])
          using \<open>tx \<in> TS'\<close> \<open>tx \<in> T\<close> prems assms \<open>tx \<in> T\<close> usolves_odeD(3)[OF x]
          by (auto intro!: is_interval_Int)
        with assms have "z tx = y tx" using tx by auto

        from usolves_odeD(4)[OF y[where t=tx] _ _ _ z_g, of s] prems
        have "z s = y s" using \<open>s \<notin> T\<close> assms \<open>z tx = y tx\<close> tx \<open>tx \<in> S\<close>
          \<open>is_interval TS'\<close> usolves_odeD(3)[OF y]
          by (auto simp: is_interval_Int)
      } ultimately have "z s = y s" by blast
    }
    ultimately
    show "z s = (if s \<in> T then x s else y s)" by simp
  qed
  done

lemma usolves_ode_union_closed:
  assumes x: "(x usolves_ode f from tx) T X"
  assumes y: "\<And>t. t \<in> closure S \<inter> closure T \<Longrightarrow> (x usolves_ode f from t) S X"
  assumes conn_T: "closure S \<inter> closure T \<subseteq> T"
  assumes conn_S: "closure S \<inter> closure T \<subseteq> S"
  assumes conn_t: "t \<in> closure S \<inter> closure T"
  shows "(x usolves_ode f from tx) (T \<union> S) X"
  using connection_usolves_ode[OF assms] by simp

lemma usolves_ode_solves_odeI:
  assumes "(x usolves_ode f from tx) T X"
  assumes "(y solves_ode f) T X" "y tx = x tx"
  shows "(y usolves_ode f from tx) T X"
  using assms(1)
  apply (rule usolves_ode_congI)
  subgoal using assms by (metis set_eq_subset usolves_odeD(2) usolves_odeD(3) usolves_odeD(4))
  by auto

lemma usolves_ode_subset_range:
  assumes x: "(x usolves_ode f from t0) T X"
  assumes r: "x ` T \<subseteq> Y" and "Y \<subseteq> X"
  shows "(x usolves_ode f from t0) T Y"
proof (rule usolves_odeI)
  note usolves_odeD[OF x]
  show "(x solves_ode f) T Y" by (rule solves_ode_subset_range; fact)
  show "t0 \<in> T" "is_interval T" by fact+
  fix z t
  assume s: "{t0 -- t} \<subseteq> T" and z: "(z solves_ode f) {t0 -- t} Y" and z0: "z t0 = x t0"
  then have "t0 \<in> {t0 -- t}" "is_interval {t0 -- t}"
    by auto
  moreover note s
  moreover have "(z solves_ode f) {t0--t} X"
    using solves_odeD[OF z] \<open>Y \<subseteq> X\<close>
    by (intro solves_ode_subset_range[OF z]) force
  moreover note z0
  moreover have "t \<in> {t0 -- t}" by simp
  ultimately show "z t = x t"
    by (rule usolves_odeD[OF x])
qed


subsection \<open>ivp on interval\<close>

context
  fixes t0 t1::real and T
  defines "T \<equiv> closed_segment t0 t1"
begin

lemma is_solution_ext_cont:
  "continuous_on T x \<Longrightarrow> (ext_cont x (min t0 t1) (max t0 t1) solves_ode f) T X = (x solves_ode f) T X"
  by (rule solves_ode_cong) (auto simp add: T_def min_def max_def closed_segment_eq_real_ivl)

lemma solution_fixed_point:
  fixes x:: "real \<Rightarrow> 'a::banach"
  assumes x: "(x solves_ode f) T X" and t: "t \<in> T"
  shows "x t0 + ivl_integral t0 t (\<lambda>t. f t (x t)) = x t"
proof -
  from solves_odeD(1)[OF x, unfolded T_def]
  have "(x has_vderiv_on (\<lambda>t. f t (x t))) (closed_segment t0 t)"
    by (rule has_vderiv_on_subset) (insert \<open>t \<in> T\<close>, auto simp: closed_segment_eq_real_ivl T_def)
  from fundamental_theorem_of_calculus_ivl_integral[OF this]
  have "((\<lambda>t. f t (x t)) has_ivl_integral x t - x t0) t0 t" .
  from this[THEN ivl_integral_unique]
  show ?thesis by simp
qed

lemma solution_fixed_point_left:
  fixes x:: "real \<Rightarrow> 'a::banach"
  assumes x: "(x solves_ode f) T X" and t: "t \<in> T"
  shows "x t1 - ivl_integral t t1 (\<lambda>t. f t (x t)) = x t"
proof -
  from solves_odeD(1)[OF x, unfolded T_def]
  have "(x has_vderiv_on (\<lambda>t. f t (x t))) (closed_segment t t1)"
    by (rule has_vderiv_on_subset) (insert \<open>t \<in> T\<close>, auto simp: closed_segment_eq_real_ivl T_def)
  from fundamental_theorem_of_calculus_ivl_integral[OF this]
  have "((\<lambda>t. f t (x t)) has_ivl_integral x t1 - x t) t t1" .
  from this[THEN ivl_integral_unique]
  show ?thesis by simp
qed

lemma solution_fixed_pointI:
  fixes x:: "real \<Rightarrow> 'a::banach"
  assumes cont_f: "continuous_on (T \<times> X) (\<lambda>(t, x). f t x)"
  assumes cont_x: "continuous_on T x"
  assumes defined: "\<And>t. t \<in> T \<Longrightarrow> x t \<in> X"
  assumes fp: "\<And>t. t \<in> T \<Longrightarrow> x t = x t0 + ivl_integral t0 t (\<lambda>t. f t (x t))"
  shows "(x solves_ode f) T X"
proof (rule solves_odeI)
  note [continuous_intros] = continuous_on_compose_Pair[OF cont_f]
  have "((\<lambda>t. x t0 + ivl_integral t0 t (\<lambda>t. f t (x t))) has_vderiv_on (\<lambda>t. f t (x t))) T"
    using cont_x defined
    by (auto intro!: derivative_eq_intros ivl_integral_has_vector_derivative
      continuous_intros
      simp: has_vderiv_on_def T_def)
  with fp show "(x has_vderiv_on (\<lambda>t. f t (x t))) T" by simp
qed (simp add: defined)

end

lemma solves_ode_half_open_segment_continuation:
  fixes f::"real \<Rightarrow> 'a \<Rightarrow> 'a::banach"
  assumes ode: "(x solves_ode f) {t0 --< t1} X"
  assumes continuous: "continuous_on ({t0 -- t1} \<times> X) (\<lambda>(t, x). f t x)"
  assumes "compact X"
  assumes "t0 \<noteq> t1"
  obtains l where
    "(x \<longlongrightarrow> l) (at t1 within {t0 --< t1})"
    "((\<lambda>t. if t = t1 then l else x t) solves_ode f) {t0 -- t1} X"
proof -
  note [continuous_intros] = continuous_on_compose_Pair[OF continuous]
  have "compact ((\<lambda>(t, x). f t x) ` ({t0 -- t1} \<times> X))"
    by (auto intro!: compact_continuous_image continuous_intros compact_Times \<open>compact X\<close>
      simp: split_beta)
  then obtain B where "B > 0" and B: "\<And>t x. t \<in> {t0 -- t1} \<Longrightarrow> x \<in> X \<Longrightarrow> norm (f t x) \<le> B"
    by (auto dest!: compact_imp_bounded simp: bounded_pos)

  have uc: "uniformly_continuous_on {t0 --< t1} x"
    apply (rule lipschitz_on_uniformly_continuous[where L=B])
    apply (rule bounded_vderiv_on_imp_lipschitz)
    apply (rule solves_odeD[OF ode])
    using solves_odeD(2)[OF ode] \<open>0 < B\<close>
    by (auto simp: closed_segment_eq_real_ivl half_open_segment_real subset_iff
      intro!: B split: if_split_asm)

  have "t1 \<in> closure ({t0 --< t1})"
    using closure_half_open_segment[of t0 t1] \<open>t0 \<noteq> t1\<close>
    by simp
  from uniformly_continuous_on_extension_on_closure[OF uc]
  obtain g where uc_g: "uniformly_continuous_on {t0--t1} g"
    and xg: "(\<And>t. t \<in> {t0 --< t1} \<Longrightarrow> x t = g t)"
    using closure_half_open_segment[of t0 t1] \<open>t0 \<noteq> t1\<close>
    by metis

  from uc_g[THEN uniformly_continuous_imp_continuous, unfolded continuous_on_def]
  have "(g \<longlongrightarrow> g t) (at t within {t0--t1})" if "t\<in>{t0--t1}" for t
    using that by auto
  then have g_tendsto: "(g \<longlongrightarrow> g t) (at t within {t0--<t1})" if "t\<in>{t0--t1}" for t
    using that by (auto intro: tendsto_within_subset half_open_segment_subset)
  then have x_tendsto: "(x \<longlongrightarrow> g t) (at t within {t0--<t1})" if "t\<in>{t0--t1}" for t
    using that
    by (subst Lim_cong_within[OF refl refl refl xg]) auto
  then have "(x \<longlongrightarrow> g t1) (at t1 within {t0 --< t1})"
    by auto
  moreover
  have nbot: "at s within {t0--<t1} \<noteq> bot" if "s \<in> {t0--t1}" for s
    using that \<open>t0 \<noteq> t1\<close>
    by (auto simp: trivial_limit_within islimpt_half_open_segment)
  have g_mem: "s \<in> {t0--t1} \<Longrightarrow> g s \<in> X" for s
    apply (rule Lim_in_closed_set[OF compact_imp_closed[OF \<open>compact X\<close>] _ _ x_tendsto])
    using solves_odeD(2)[OF ode] \<open>t0 \<noteq> t1\<close>
    by (auto intro!: simp: eventually_at_filter nbot)
  have "(g solves_ode f) {t0 -- t1} X"
    apply (rule solution_fixed_pointI[OF continuous])
    subgoal by (auto intro!: uc_g uniformly_continuous_imp_continuous)
    subgoal by (rule g_mem)
    subgoal premises prems for s
    proof -
      {
        fix s
        assume s: "s \<in> {t0--<t1}"
        with prems have subs: "{t0--s} \<subseteq> {t0--<t1}"
          by (auto simp: half_open_segment_real closed_segment_eq_real_ivl)
        with ode have sol: "(x solves_ode f) ({t0--s}) X"
          by (rule solves_ode_on_subset) (rule order_refl)
        from subs have inner_eq: "t \<in> {t0 -- s} \<Longrightarrow> x t = g t" for t
          by (intro xg) auto
        from solution_fixed_point[OF sol, of s]
        have "g t0 + ivl_integral t0 s (\<lambda>t. f t (g t)) - g s = 0"
          using s prems \<open>t0 \<noteq> t1\<close>
          by (auto simp: inner_eq cong: ivl_integral_cong)
      } note fp = this

      from prems have subs: "{t0--s} \<subseteq> {t0--t1}"
        by (auto simp: closed_segment_eq_real_ivl)
      have int: "(\<lambda>t. f t (g t)) integrable_on {t0--t1}"
        using prems subs
        by (auto intro!: integrable_continuous_closed_segment continuous_intros g_mem
          uc_g[THEN uniformly_continuous_imp_continuous, THEN continuous_on_subset])
      note ivl_tendsto[tendsto_intros] =
        indefinite_ivl_integral_continuous(1)[OF int, unfolded continuous_on_def, rule_format]

      from subs half_open_segment_subset
      have "((\<lambda>s. g t0 + ivl_integral t0 s (\<lambda>t. f t (g t)) - g s) \<longlongrightarrow>
        g t0 + ivl_integral t0 s (\<lambda>t. f t (g t)) - g s) (at s within {t0 --< t1})"
        using subs
        by (auto intro!: tendsto_intros ivl_tendsto[THEN tendsto_within_subset]
          g_tendsto[THEN tendsto_within_subset])
      moreover
      have "((\<lambda>s. g t0 + ivl_integral t0 s (\<lambda>t. f t (g t)) - g s) \<longlongrightarrow> 0) (at s within {t0 --< t1})"
        apply (subst Lim_cong_within[OF refl refl refl, where g="\<lambda>_. 0"])
        subgoal by (subst fp) auto
        subgoal by simp
        done
      ultimately have "g t0 + ivl_integral t0 s (\<lambda>t. f t (g t)) - g s = 0"
        using nbot prems tendsto_unique by blast
      then show "g s = g t0 + ivl_integral t0 s (\<lambda>t. f t (g t))" by simp
    qed
    done
  then have "((\<lambda>t. if t = t1 then g t1 else x t) solves_ode f) {t0--t1} X"
    apply (rule solves_ode_congI)
    using xg \<open>t0 \<noteq> t1\<close>
    by (auto simp: half_open_segment_closed_segmentI)
  ultimately show ?thesis ..
qed


subsection \<open>Picard-Lindeloef on set of functions into closed set\<close>
text\<open>\label{sec:plclosed}\<close>

locale continuous_rhs = fixes T X f
  assumes continuous: "continuous_on (T \<times> X) (\<lambda>(t, x). f t x)"
begin

lemma continuous_rhs_comp[continuous_intros]:
  assumes [continuous_intros]: "continuous_on S g"
  assumes [continuous_intros]: "continuous_on S h"
  assumes "g ` S \<subseteq> T"
  assumes "h ` S \<subseteq> X"
  shows "continuous_on S (\<lambda>x. f (g x) (h x))"
  using continuous_on_compose_Pair[OF continuous assms(1,2)] assms(3,4)
  by auto

end

locale global_lipschitz =
  fixes T X f and L::real
  assumes lipschitz: "\<And>t. t \<in> T \<Longrightarrow> L-lipschitz_on X (\<lambda>x. f t x)"

locale closed_domain =
  fixes X assumes closed: "closed X"

locale interval = fixes T::"real set"
  assumes interval: "is_interval T"
begin

lemma closed_segment_subset_domain: "t0 \<in> T \<Longrightarrow> t \<in> T \<Longrightarrow> closed_segment t0 t \<subseteq> T"
  by (simp add: closed_segment_subset_interval interval)

lemma closed_segment_subset_domainI: "t0 \<in> T \<Longrightarrow> t \<in> T \<Longrightarrow> s \<in> closed_segment t0 t \<Longrightarrow> s \<in> T"
  using closed_segment_subset_domain by force

lemma convex[intro, simp]: "convex T"
  and connected[intro, simp]: "connected T"
  by (simp_all add: interval is_interval_connected is_interval_convex )

end

locale nonempty_set = fixes T assumes nonempty_set: "T \<noteq> {}"

locale compact_interval = interval + nonempty_set T +
  assumes compact_time: "compact T"
begin

definition "tmin = Inf T"
definition "tmax = Sup T"

lemma
  shows tmin: "t \<in> T \<Longrightarrow> tmin \<le> t" "tmin \<in> T"
    and tmax: "t \<in> T \<Longrightarrow> t \<le> tmax" "tmax \<in> T"
  using nonempty_set
  by (auto intro!: cInf_lower cSup_upper bounded_imp_bdd_below bounded_imp_bdd_above
    compact_imp_bounded compact_time closed_contains_Inf closed_contains_Sup compact_imp_closed
    simp: tmin_def tmax_def)

lemma tmin_le_tmax[intro, simp]: "tmin \<le> tmax"
  using nonempty_set tmin tmax by auto

lemma T_def: "T = {tmin .. tmax}"
  using closed_segment_subset_interval[OF interval tmin(2) tmax(2)]
  by (auto simp: closed_segment_eq_real_ivl subset_iff intro!: tmin tmax)

lemma mem_T_I[intro, simp]: "tmin \<le> t \<Longrightarrow> t \<le> tmax \<Longrightarrow> t \<in> T"
  using interval mem_is_interval_1_I tmax(2) tmin(2) by blast

end

locale self_mapping = interval T for T +
  fixes t0::real and x0 f X
  assumes iv_defined: "t0 \<in> T" "x0 \<in> X"
  assumes self_mapping:
    "\<And>x t. t \<in> T \<Longrightarrow> x t0 = x0 \<Longrightarrow> x \<in> closed_segment t0 t \<rightarrow> X \<Longrightarrow>
      continuous_on (closed_segment t0 t) x \<Longrightarrow> x t0 + ivl_integral t0 t (\<lambda>t. f t (x t)) \<in> X"
begin

sublocale nonempty_set T using iv_defined by unfold_locales auto

lemma closed_segment_iv_subset_domain: "t \<in> T \<Longrightarrow> closed_segment t0 t \<subseteq> T"
  by (simp add: closed_segment_subset_domain iv_defined)

end

locale unique_on_closed =
  compact_interval T +
  self_mapping T t0 x0 f X +
  continuous_rhs T X f +
  closed_domain X +
  global_lipschitz T X f L for t0::real and T and x0::"'a::banach" and f X L
begin

lemma T_split: "T = {tmin .. t0} \<union> {t0 .. tmax}"
  by (metis T_def atLeastAtMost_iff iv_defined(1) ivl_disj_un_two_touch(4))

lemma L_nonneg: "0 \<le> L"
  by (auto intro!: lipschitz_on_nonneg[OF lipschitz] iv_defined)

text \<open>Picard Iteration\<close>

definition P_inner where "P_inner x t = x0 + ivl_integral t0 t (\<lambda>t. f  t (x t))"

definition P::"(real \<Rightarrow>\<^sub>C 'a) \<Rightarrow> (real \<Rightarrow>\<^sub>C 'a)"
  where "P x = (SOME g::real\<Rightarrow>\<^sub>C 'a.
    (\<forall>t \<in> T. g t = P_inner x t) \<and>
    (\<forall>t\<le>tmin. g t = P_inner x tmin) \<and>
    (\<forall>t\<ge>tmax. g t = P_inner x tmax))"

lemma cont_P_inner_ivl:
  "x \<in> T \<rightarrow>\<^sub>C X \<Longrightarrow> continuous_on {tmin..tmax} (P_inner (apply_bcontfun x))"
  apply (auto simp: real_Icc_closed_segment P_inner_def Pi_iff mem_PiC_iff
      intro!: continuous_intros indefinite_ivl_integral_continuous_subset
      integrable_continuous_closed_segment tmin(1) tmax(1))
  using closed_segment_subset_domainI tmax(2) tmin(2) apply blast
  using closed_segment_subset_domainI tmax(2) tmin(2) apply blast
  using T_def closed_segment_eq_real_ivl iv_defined(1) by auto

lemma P_inner_t0[simp]: "P_inner g t0 = x0"
  by (simp add: P_inner_def)

lemma t0_cs_tmin_tmax: "t0 \<in> {tmin--tmax}" and cs_tmin_tmax_subset: "{tmin--tmax} \<subseteq> T"
  using iv_defined T_def closed_segment_eq_real_ivl
  by auto

lemma
  P_eqs:
  assumes "x \<in> T \<rightarrow>\<^sub>C X"
  shows P_eq_P_inner: "t \<in> T \<Longrightarrow> P x t = P_inner x t"
    and P_le_tmin: "t \<le> tmin \<Longrightarrow> P x t = P_inner x tmin"
    and P_ge_tmax: "t \<ge> tmax \<Longrightarrow> P x t = P_inner x tmax"
  unfolding atomize_conj atomize_imp
proof goal_cases
  case 1
  obtain g where
    "t \<in> {tmin .. tmax} \<Longrightarrow> apply_bcontfun g t = P_inner (apply_bcontfun x) t"
    "apply_bcontfun g t = P_inner (apply_bcontfun x) (clamp tmin tmax t)"
    for t
    by (metis continuous_on_cbox_bcontfunE cont_P_inner_ivl[OF assms(1)] cbox_interval)
  with T_def have "\<exists>g::real\<Rightarrow>\<^sub>C 'a.
    (\<forall>t \<in> T. g t = P_inner x t) \<and>
    (\<forall>t\<le>tmin. g t = P_inner x tmin) \<and>
    (\<forall>t\<ge>tmax. g t = P_inner x tmax)"
    by (auto intro!: exI[where x=g])
  then have "(\<forall>t \<in> T. P x t = P_inner x t) \<and>
    (\<forall>t\<le>tmin. P x t = P_inner x tmin) \<and>
    (\<forall>t\<ge>tmax. P x t = P_inner x tmax)"
    unfolding P_def
    by (rule someI_ex)
  then show ?case using T_def by auto
qed

lemma P_if_eq:
  "x \<in> T \<rightarrow>\<^sub>C X \<Longrightarrow>
    P x t = (if tmin \<le> t \<and> t \<le> tmax then P_inner x t else if t \<ge> tmax then P_inner x tmax else P_inner x tmin)"
  by (auto simp: P_eqs)

lemma dist_P_le:
  assumes y: "y \<in> T \<rightarrow>\<^sub>C X" and z: "z \<in> T \<rightarrow>\<^sub>C X"
  assumes le: "\<And>t. tmin \<le> t \<Longrightarrow> t \<le> tmax \<Longrightarrow> dist (P_inner y t) (P_inner z t) \<le> R"
  assumes "0 \<le> R"
  shows "dist (P y t) (P z t) \<le> R"
  by (cases "t \<le> tmin"; cases "t \<ge> tmax") (auto simp: P_eqs y z not_le intro!: le)

lemma P_def':
  assumes "t \<in> T"
  assumes "fixed_point \<in> T \<rightarrow>\<^sub>C X"
  shows "(P fixed_point) t = x0 + ivl_integral t0 t (\<lambda>x. f x (fixed_point x))"
  by (simp add: P_eq_P_inner assms P_inner_def)

definition "iter_space = PiC T ((\<lambda>_. X)(t0:={x0}))"

lemma iter_spaceI:
  assumes "g \<in> T \<rightarrow>\<^sub>C X" "g t0 = x0"
  shows "g \<in> iter_space"
  using assms
  by (simp add: iter_space_def mem_PiC_iff Pi_iff)

lemma iter_spaceD:
  assumes "g \<in> iter_space"
  shows "g \<in> T \<rightarrow>\<^sub>C X" "apply_bcontfun g t0 = x0"
  using assms iv_defined
  by (auto simp add: iter_space_def mem_PiC_iff split: if_splits)

lemma const_in_iter_space: "const_bcontfun x0 \<in> iter_space"
  by (auto simp: iter_space_def iv_defined mem_PiC_iff)

lemma closed_iter_space: "closed iter_space"
  by (auto simp: iter_space_def intro!: closed_PiC closed)

lemma iter_space_notempty: "iter_space \<noteq> {}"
  using const_in_iter_space by blast

lemma clamp_in_eq[simp]: fixes a x b::real shows "a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> clamp a b x = x"
  by (auto simp: clamp_def)

lemma P_self_mapping:
  assumes in_space: "g \<in> iter_space"
  shows "P g \<in> iter_space"
proof (rule iter_spaceI)
  show x0: "P g t0 = x0"
    by (auto simp: P_def' iv_defined iter_spaceD[OF in_space])
  from iter_spaceD(1)[OF in_space] show "P g \<in> T \<rightarrow>\<^sub>C X"
    unfolding mem_PiC_iff Pi_iff
    apply (auto simp: mem_PiC_iff Pi_iff P_def')
    apply (auto simp: iter_spaceD(2)[OF in_space, symmetric] intro!: self_mapping)
    using closed_segment_subset_domainI iv_defined(1) by blast
qed

lemma continuous_on_T: "continuous_on {tmin .. tmax} g \<Longrightarrow> continuous_on T g"
  using T_def by auto

lemma T_closed_segment_subsetI[intro, simp]: "t \<in> {tmin--tmax} \<Longrightarrow> t \<in> T"
  and T_subsetI[intro, simp]: "tmin \<le> t \<Longrightarrow> t \<le> tmax \<Longrightarrow> t \<in> T"
  by (subst T_def, simp add: closed_segment_eq_real_ivl)+

lemma t0_mem_closed_segment[intro, simp]: "t0 \<in> {tmin--tmax}"
  using T_def iv_defined
  by (simp add: closed_segment_eq_real_ivl)

lemma tmin_le_t0[intro, simp]: "tmin \<le> t0"
  and tmax_ge_t0[intro, simp]: "tmax \<ge> t0"
  using t0_mem_closed_segment
  unfolding closed_segment_eq_real_ivl
  by simp_all

lemma apply_bcontfun_solution_fixed_point:
  assumes ode: "(apply_bcontfun x solves_ode f) T X"
  assumes iv: "x t0 = x0"
  assumes t: "t \<in> T"
  shows "P x t = x t"
proof -
  have "t \<in> {t0 -- t}" by simp
  have ode': "(apply_bcontfun x solves_ode f) {t0--t} X" "t \<in> {t0 -- t}"
    using ode T_def closed_segment_eq_real_ivl t apply auto
    using closed_segment_iv_subset_domain solves_ode_on_subset apply fastforce
    using closed_segment_iv_subset_domain solves_ode_on_subset apply fastforce
    done
  from solves_odeD[OF ode]
  have x: "x \<in> T \<rightarrow>\<^sub>C X" by (auto simp: mem_PiC_iff)
  from solution_fixed_point[OF ode'] iv
  show ?thesis
    unfolding P_def'[OF t x]
    by simp
qed

lemma
  solution_in_iter_space:
  assumes ode: "(apply_bcontfun z solves_ode f) T X"
  assumes iv: "z t0 = x0"
  shows "z \<in> iter_space" (is "?z \<in> _")
proof -
  from T_def ode have ode: "(z solves_ode f) {tmin -- tmax} X"
    by (simp add: closed_segment_eq_real_ivl)
  have "(?z solves_ode f) T X"
    using is_solution_ext_cont[OF solves_ode_continuous_on[OF ode], of f X] ode T_def
    by (auto simp: min_def max_def closed_segment_eq_real_ivl)
  then have "z \<in> T \<rightarrow>\<^sub>C X"
    by (auto simp add: solves_ode_def mem_PiC_iff)
  thus "?z \<in> iter_space"
    by (auto simp: iv intro!: iter_spaceI)
qed

end

locale unique_on_bounded_closed = unique_on_closed +
  assumes lipschitz_bound: "\<And>s t. s \<in> T \<Longrightarrow> t \<in> T \<Longrightarrow> abs (s - t) * L < 1"
begin

lemma lipschitz_bound_maxmin: "(tmax - tmin) * L < 1"
  using lipschitz_bound[of tmax tmin]
  by auto

lemma lipschitz_P:
  shows "((tmax - tmin) * L)-lipschitz_on iter_space P"
proof (rule lipschitz_onI)
  have "t0 \<in> T" by (simp add: iv_defined)
  then show "0 \<le> (tmax - tmin) * L"
    using T_def
    by (auto intro!: mult_nonneg_nonneg lipschitz lipschitz_on_nonneg[OF lipschitz]
      iv_defined)
  fix y z
  assume "y \<in> iter_space" and "z \<in> iter_space"
  hence y_defined: "y \<in> (T \<rightarrow>\<^sub>C X)" and "y t0 = x0"
    and z_defined: "z \<in> (T \<rightarrow>\<^sub>C X)" and "y t0 = x0"
    by (auto dest: iter_spaceD)
  have defined: "s \<in> T" "y s \<in> X" "z s \<in> X" if "s \<in> closed_segment tmin tmax" for s
    using y_defined z_defined that T_def
    by (auto simp: mem_PiC_iff)
  {
    note [intro, simp] = integrable_continuous_closed_segment
    fix t
    assume t_bounds: "tmin \<le> t" "t \<le> tmax"
    then have cs_subs: "closed_segment t0 t \<subseteq> closed_segment tmin tmax"
      by (auto simp: closed_segment_eq_real_ivl)
    then have cs_subs_ext: "\<And>ta. ta \<in> {t0--t} \<Longrightarrow> ta \<in> {tmin--tmax}" by auto

    have "norm (P_inner y t - P_inner z t) =
      norm (ivl_integral t0 t (\<lambda>t. f t (y t) - f t (z t)))"
      by (subst ivl_integral_diff)
        (auto intro!: integrable_continuous_closed_segment continuous_intros defined cs_subs_ext simp: P_inner_def)
    also have "... \<le> abs (ivl_integral t0 t (\<lambda>t. norm (f t (y t) - f t (z t))))"
      by (rule ivl_integral_norm_bound_ivl_integral)
        (auto intro!: ivl_integral_norm_bound_ivl_integral continuous_intros integrable_continuous_closed_segment
          simp: defined cs_subs_ext)
    also have "... \<le> abs (ivl_integral t0 t (\<lambda>t. L * norm (y t - z t)))"
      using lipschitz t_bounds T_def y_defined z_defined cs_subs
      by (intro norm_ivl_integral_le) (auto intro!: continuous_intros integrable_continuous_closed_segment
        simp add: dist_norm lipschitz_on_def mem_PiC_iff Pi_iff)
    also have "... \<le> abs (ivl_integral t0 t (\<lambda>t. L * norm (y - z)))"
      using norm_bounded[of "y - z"]
        L_nonneg
      by (intro norm_ivl_integral_le) (auto intro!: continuous_intros mult_left_mono)
    also have "... = L * abs (t - t0) * norm (y - z)"
      using t_bounds L_nonneg by (simp add: abs_mult)
    also have "... \<le> L * (tmax - tmin) * norm (y - z)"
      using t_bounds zero_le_dist L_nonneg cs_subs tmin_le_t0 tmax_ge_t0
      by (auto intro!: mult_right_mono mult_left_mono simp: closed_segment_eq_real_ivl abs_real_def
        simp del: tmin_le_t0 tmax_ge_t0 split: if_split_asm)
    finally
    have "dist (P_inner y t) (P_inner z t) \<le> (tmax - tmin) * L * dist y z"
      by (simp add: dist_norm ac_simps)
  } note * = this
  show "dist (P y) (P z) \<le> (tmax - tmin) * L * dist y z"
    by (auto intro!: dist_bound dist_P_le * y_defined z_defined mult_nonneg_nonneg L_nonneg)
qed


lemma fixed_point_unique: "\<exists>!x\<in>iter_space. P x = x"
  using lipschitz lipschitz_bound_maxmin lipschitz_P T_def
      complete_UNIV iv_defined
  by (intro banach_fix)
    (auto
      intro: P_self_mapping split_mult_pos_le
      intro!: closed_iter_space iter_space_notempty mult_nonneg_nonneg
      simp: lipschitz_on_def complete_eq_closed)

definition fixed_point where
  "fixed_point = (THE x. x \<in> iter_space \<and> P x = x)"

lemma fixed_point':
  "fixed_point \<in> iter_space \<and> P fixed_point = fixed_point"
  unfolding fixed_point_def using fixed_point_unique
  by (rule theI')

lemma fixed_point:
  "fixed_point \<in> iter_space" "P fixed_point = fixed_point"
  using fixed_point' by simp_all

lemma fixed_point_equality': "x \<in> iter_space \<and> P x = x \<Longrightarrow> fixed_point = x"
  unfolding fixed_point_def using fixed_point_unique
  by (rule the1_equality)

lemma fixed_point_equality: "x \<in> iter_space \<Longrightarrow> P x = x \<Longrightarrow> fixed_point = x"
  using fixed_point_equality'[of x] by auto

lemma fixed_point_iv: "fixed_point t0 = x0"
  and fixed_point_domain: "x \<in> T \<Longrightarrow> fixed_point x \<in> X"
  using fixed_point
  by (force dest: iter_spaceD simp: mem_PiC_iff)+

lemma fixed_point_has_vderiv_on: "(fixed_point has_vderiv_on (\<lambda>t. f t (fixed_point t))) T"
proof -
  have "continuous_on T (\<lambda>x. f x (fixed_point x))"
    using fixed_point_domain
    by (auto intro!: continuous_intros)
  then have "((\<lambda>u. x0 + ivl_integral t0 u (\<lambda>x. f x (fixed_point x))) has_vderiv_on (\<lambda>t. f t (fixed_point t))) T"
    by (auto intro!: derivative_intros ivl_integral_has_vderiv_on_compact_interval interval compact_time)
  then show ?thesis
  proof (rule has_vderiv_eq)
    fix t
    assume t: "t \<in> T"
    have "fixed_point t = P fixed_point t"
      using fixed_point by simp
    also have "\<dots> = x0 + ivl_integral t0 t (\<lambda>x. f x (fixed_point x))"
      using t fixed_point_domain
      by (auto simp: P_def' mem_PiC_iff)
    finally show "x0 + ivl_integral t0 t (\<lambda>x. f x (fixed_point x)) = fixed_point t" by simp
  qed (insert T_def, auto simp: closed_segment_eq_real_ivl)
qed

lemma fixed_point_solution:
  shows "(fixed_point solves_ode f) T X"
  using fixed_point_has_vderiv_on fixed_point_domain
  by (rule solves_odeI)


subsubsection \<open>Unique solution\<close>
text\<open>\label{sec:ivp-ubs}\<close>

lemma solves_ode_equals_fixed_point:
  assumes ode: "(x solves_ode f) T X"
  assumes iv: "x t0 = x0"
  assumes t: "t \<in> T"
  shows "x t = fixed_point t"
proof -
  from solves_ode_continuous_on[OF ode] T_def
  have "continuous_on (cbox tmin tmax) x" by simp
  from continuous_on_cbox_bcontfunE[OF this]
  obtain g where g:
    "t \<in> {tmin .. tmax} \<Longrightarrow> apply_bcontfun g t = x t"
    "apply_bcontfun g t = x (clamp tmin tmax t)"
    for t
    by (metis interval_cbox)
  with ode T_def have ode_g: "(g solves_ode f) T X"
    by (metis (no_types, lifting) solves_ode_cong)
  have "x t = g t"
    using t T_def
    by (intro g[symmetric]) auto
  also
  have "g t0 = x0" "g \<in> T \<rightarrow>\<^sub>C X"
    using iv g solves_odeD(2)[OF ode_g]
    unfolding mem_PiC_iff atLeastAtMost_iff
    by blast+
  then have "g \<in> iter_space"
    by (intro iter_spaceI)
  then have "g = fixed_point"
    apply (rule fixed_point_equality[symmetric])
    apply (rule bcontfun_eqI)
    subgoal for t
      using apply_bcontfun_solution_fixed_point[OF ode_g \<open>g t0 = x0\<close>, of tmin]
        apply_bcontfun_solution_fixed_point[OF ode_g \<open>g t0 = x0\<close>, of tmax]
        apply_bcontfun_solution_fixed_point[OF ode_g \<open>g t0 = x0\<close>, of t]
      using T_def
      by (fastforce simp: P_eqs not_le \<open>g \<in> T \<rightarrow>\<^sub>C X\<close> g)
    done
  finally show ?thesis .
qed

lemma solves_ode_on_closed_segment_equals_fixed_point:
  assumes ode: "(x solves_ode f) {t0 -- t1'} X"
  assumes iv: "x t0 = x0"
  assumes subset: "{t0--t1'} \<subseteq> T"
  assumes t_mem: "t \<in> {t0--t1'}"
  shows "x t = fixed_point t"
proof -
  have subsetI: "t \<in> {t0--t1'} \<Longrightarrow> t \<in> T" for t
    using subset by auto
  interpret s: unique_on_bounded_closed t0 "{t0--t1'}" x0 f X L
    apply - apply unfold_locales
    subgoal by (simp add: closed_segment_eq_real_ivl)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal using iv_defined by simp
    subgoal by (intro self_mapping subsetI)
    subgoal by (rule continuous_on_subset[OF continuous]) (auto simp: subsetI )
    subgoal by (rule lipschitz) (auto simp: subsetI)
    subgoal by (auto intro!: subsetI lipschitz_bound)
    done
  have "x t = s.fixed_point t"
    by (rule s.solves_ode_equals_fixed_point; fact)
  moreover
  have "fixed_point t = s.fixed_point t"
    by (intro s.solves_ode_equals_fixed_point solves_ode_on_subset[OF fixed_point_solution] assms
      fixed_point_iv order_refl subset t_mem)
  ultimately show ?thesis by simp
qed

lemma unique_solution:
  assumes ivp1: "(x solves_ode f) T X" "x t0 = x0"
  assumes ivp2: "(y solves_ode f) T X" "y t0 = x0"
  assumes "t \<in> T"
  shows "x t = y t"
  using solves_ode_equals_fixed_point[OF ivp1 \<open>t \<in> T\<close>]
    solves_ode_equals_fixed_point[OF ivp2 \<open>t \<in> T\<close>]
  by simp

lemma fixed_point_usolves_ode: "(fixed_point usolves_ode f from t0) T X"
  apply (rule usolves_odeI[OF fixed_point_solution])
  subgoal by (simp add: iv_defined(1))
  subgoal by (rule interval)
  subgoal
    using fixed_point_iv solves_ode_on_closed_segment_equals_fixed_point
    by auto
  done

end

lemma closed_segment_Un:
  fixes a b c::real
  assumes "b \<in> closed_segment a c"
  shows "closed_segment a b \<union> closed_segment b c = closed_segment a c"
  using assms
  by (auto simp: closed_segment_eq_real_ivl)

lemma closed_segment_closed_segment_subset:
  fixes s::real and i::nat
  assumes "s \<in> closed_segment a b"
  assumes "a \<in> closed_segment c d" "b \<in> closed_segment c d"
  shows "s \<in> closed_segment c d"
  using assms
  by (auto simp: closed_segment_eq_real_ivl split: if_split_asm)


context unique_on_closed begin

context\<comment> \<open>solution until t1\<close>
  fixes t1::real
  assumes mem_t1: "t1 \<in> T"
begin

lemma subdivide_count_ex: "\<exists>n. L * abs (t1 - t0) / (Suc n) < 1"
  by auto (meson add_strict_increasing less_numeral_extra(1) real_arch_simple)

definition "subdivide_count = (SOME n. L * abs (t1 - t0) / Suc n < 1)"

lemma subdivide_count: "L * abs (t1 - t0) / Suc subdivide_count < 1"
  unfolding subdivide_count_def
  using subdivide_count_ex
  by (rule someI_ex)

lemma subdivide_lipschitz:
  assumes "\<bar>s - t\<bar> \<le> abs (t1 - t0) / Suc subdivide_count"
  shows "\<bar>s - t\<bar> * L < 1"
proof -
  from assms L_nonneg
  have "\<bar>s - t\<bar> * L \<le> abs (t1 - t0) / Suc subdivide_count * L"
    by (rule mult_right_mono)
  also have "\<dots> < 1"
    using subdivide_count
    by (simp add: ac_simps)
  finally show ?thesis .
qed

lemma subdivide_lipschitz_lemma:
  assumes st: "s \<in> {a -- b}" "t \<in> {a -- b}"
  assumes "abs (b - a) \<le> abs (t1 - t0) / Suc subdivide_count"
  shows "\<bar>s - t\<bar> * L < 1"
  apply (rule subdivide_lipschitz)
  apply (rule order_trans[where y="abs (b - a)"])
  using assms
  by (auto simp: closed_segment_eq_real_ivl split: if_splits)

definition "step = (t1 - t0) / Suc subdivide_count"

lemma last_step: "t0 + real (Suc subdivide_count) * step = t1"
  by (auto simp: step_def)

lemma step_in_segment:
  assumes "0 \<le> i" "i \<le> real (Suc subdivide_count)"
  shows "t0 + i * step \<in> closed_segment t0 t1"
  unfolding closed_segment_eq_real_ivl step_def
proof (clarsimp, safe)
  assume "t0 \<le> t1"
  then have "(t1 - t0) * i \<le> (t1 - t0) * (1 + subdivide_count)"
    using assms
    by (auto intro!: mult_left_mono)
  then show "t0 + i * (t1 - t0) / (1 + real subdivide_count) \<le> t1"
    by (simp add: field_simps)
next
  assume "\<not>t0 \<le> t1"
  then have "(1 + subdivide_count) * (t0 - t1) \<ge> i * (t0 - t1)"
    using assms
    by (auto intro!: mult_right_mono)
  then show "t1 \<le> t0 + i * (t1 - t0) / (1 + real subdivide_count)"
    by (simp add: field_simps)
  show "i * (t1 - t0) / (1 + real subdivide_count) \<le> 0"
    using \<open>\<not>t0 \<le> t1\<close>
    by (auto simp: divide_simps mult_le_0_iff assms)
qed (auto intro!: divide_nonneg_nonneg mult_nonneg_nonneg assms)

lemma subset_T1:
  fixes s::real and i::nat
  assumes "s \<in> closed_segment t0 (t0 + i * step)"
  assumes "i \<le> Suc subdivide_count"
  shows "s \<in> {t0 -- t1}"
  using closed_segment_closed_segment_subset assms of_nat_le_iff of_nat_0_le_iff step_in_segment
  by blast

lemma subset_T: "{t0 -- t1} \<subseteq> T" and subset_TI: "s \<in> {t0 -- t1} \<Longrightarrow> s \<in> T"
  using closed_segment_iv_subset_domain mem_t1 by blast+

primrec psolution::"nat \<Rightarrow> real \<Rightarrow> 'a" where
  "psolution 0 t = x0"
| "psolution (Suc i) t = unique_on_bounded_closed.fixed_point
    (t0 + real i * step) {t0 + real i * step -- t0 + real (Suc i) * step}
    (psolution i (t0 + real i * step)) f X t"

definition "psolutions t = psolution (LEAST i. t \<in> closed_segment (t0 + real (i - 1) * step) (t0 + real i * step)) t"

lemma psolutions_usolves_until_step:
  assumes i_le: "i \<le> Suc subdivide_count"
  shows "(psolutions usolves_ode f from t0) (closed_segment t0 (t0 + real i * step)) X"
proof cases
  assume "t0 = t1"
  then have "step = 0"
    unfolding step_def by simp
  then show ?thesis by (simp add: psolutions_def iv_defined usolves_ode_singleton)
next
  assume "t0 \<noteq> t1"
  then have "step \<noteq> 0"
    by (simp add: step_def)
  define S where "S \<equiv> \<lambda>i. closed_segment (t0 + real (i - 1) * step) (t0 + real i * step)"
  have solution_eq: "psolutions \<equiv> \<lambda>t. psolution (LEAST i. t \<in> S i) t"
    by (simp add: psolutions_def[abs_def] S_def)
  show ?thesis
    unfolding solution_eq
    using i_le
  proof (induction i)
    case 0 then show ?case by (simp add: iv_defined usolves_ode_singleton S_def)
  next
    case (Suc i)
    let ?sol = "\<lambda>t. psolution (LEAST i. t \<in> S i) t"
    let ?pi = "t0 + real (i - Suc 0) * step" and ?i = "t0 + real i * step" and ?si = "t0 + (1 + real i) * step"
    from Suc have ui: "(?sol usolves_ode f from t0) (closed_segment t0 (t0 + real i * step)) X"
      by simp

    from usolves_odeD(1)[OF Suc.IH] Suc
    have IH_sol: "(?sol solves_ode f) (closed_segment t0 ?i) X"
      by simp

    have Least_eq_t0[simp]: "(LEAST n. t0 \<in> S n) = 0"
      by (rule Least_equality) (auto simp add: S_def)
    have Least_eq[simp]: "(LEAST n. t0 + real i * step \<in> S n) = i" for i
      apply (rule Least_equality)
      subgoal by (simp add: S_def)
      subgoal
        using \<open>step \<noteq> 0\<close>
        by (cases "step \<ge> 0")
          (auto simp add: S_def closed_segment_eq_real_ivl zero_le_mult_iff split: if_split_asm)
      done

    have "y = t0 + real i * s"
      if "t0 + (1 + real i) * s \<le> t" "t \<le> y" "y \<le> t0 + real i * s" "t0 \<le> y"
      for y i s t
    proof -
      from that have "(1 + real i) * s \<le> real i * s" "0 \<le> real i * s"
        by arith+
      have "s + (t0 + s * real i) \<le> t \<Longrightarrow> t \<le> y \<Longrightarrow> y \<le> t0 + s * real i \<Longrightarrow> t0 \<le> y \<Longrightarrow> y = t0 + s * real i"
        by (metis add_decreasing2 eq_iff le_add_same_cancel2 linear mult_le_0_iff of_nat_0_le_iff order.trans)
      then show ?thesis using that
        by (simp add: algebra_simps)
    qed
    then have segment_inter:
      "xa = t0 + real i * step"
      if
      "t \<in> {t0 + real (Suc i - 1) * step--t0 + real (Suc i) * step}"
      "xa \<in> closed_segment (t0 + real i * step) t" "xa \<in> closed_segment t0 (t0 + real i * step)"
      for xa t
      apply (cases "step > 0"; cases "step = 0")
      using that
      by (auto simp: S_def closed_segment_eq_real_ivl split: if_split_asm)

    have right_cond: "t0 \<le> t" "t \<le> t1" if "t0 + real i * step \<le> t" "t \<le> t0 + (step + real i * step)" for t
    proof -
      from that have "0 \<le> step" by simp
      with last_step have "t0 \<le> t1"
        by (metis le_add_same_cancel1 of_nat_0_le_iff zero_le_mult_iff)
      from that have "t0 \<le> t - real i * step" by simp
      also have "\<dots> \<le> t" using that by (auto intro!: mult_nonneg_nonneg)
      finally show "t0 \<le> t" .
      have "t \<le> t0 + (real (Suc i) * step)" using that by (simp add: algebra_simps)
      also have "\<dots> \<le> t1"
      proof -
        have "real (Suc i) * (t1 - t0) \<le> real (Suc subdivide_count) * (t1 - t0)"
          using Suc.prems \<open>t0 \<le> t1\<close>
          by (auto intro!: mult_mono)
        then show ?thesis by (simp add: divide_simps algebra_simps step_def)
      qed
      finally show "t \<le> t1" .
    qed
    have left_cond: "t1 \<le> t" "t \<le> t0" if "t0 + (step + real i * step) \<le> t" "t \<le> t0 + real i * step" for t
    proof -
      from that have "step \<le> 0" by simp
      with last_step have "t1 \<le> t0"
        by (metis add_le_same_cancel1 mult_nonneg_nonpos of_nat_0_le_iff)
      from that have "t0 \<ge> t - real i * step" by simp
      also have "t - real i * step \<ge> t" using that by (auto intro!: mult_nonneg_nonpos)
      finally (xtrans) show "t \<le> t0" .
      have "t \<ge> t0 + (real (Suc i) * step)" using that by (simp add: algebra_simps)
      also have " t0 + (real (Suc i) * step) \<ge> t1"
      proof -
        have "real (Suc i) * (t0 - t1) \<le> real (Suc subdivide_count) * (t0 - t1)"
          using Suc.prems \<open>t0 \<ge> t1\<close>
          by (auto intro!: mult_mono)
        then show ?thesis by (simp add: divide_simps algebra_simps step_def)
      qed
      finally (xtrans) show "t1 \<le> t" .
    qed

    interpret l: self_mapping "S (Suc i)" ?i "?sol ?i" f X
    proof unfold_locales
      show "?sol ?i \<in> X"
        using solves_odeD(2)[OF usolves_odeD(1)[OF ui], of "?i"]
        by (simp add: S_def)
      fix x t assume t[unfolded S_def]: "t \<in> S (Suc i)"
        and x: "x ?i = ?sol ?i" "x \<in> closed_segment ?i t \<rightarrow> X"
        and cont: "continuous_on (closed_segment ?i t) x"

      let ?if = "\<lambda>t. if t \<in> closed_segment t0 ?i then ?sol t else x t"
      let ?f = "\<lambda>t. f t (?if t)"
      have sol_mem: "?sol s \<in> X" if "s \<in> closed_segment t0 ?i" for s
        by (auto simp: subset_T1 intro!: solves_odeD[OF IH_sol] that)

      from x(1) have "x ?i + ivl_integral ?i t (\<lambda>t. f t (x t)) = ?sol ?i + ivl_integral ?i t (\<lambda>t. f t (x t))"
        by simp
      also have "?sol ?i = ?sol t0 + ivl_integral t0 ?i (\<lambda>t. f t (?sol t))"
        apply (subst solution_fixed_point)
        apply (rule usolves_odeD[OF ui])
        by simp_all
      also have "ivl_integral t0 ?i (\<lambda>t. f t (?sol t)) = ivl_integral t0 ?i ?f"
        by (simp cong: ivl_integral_cong)
      also
      have psolution_eq: "x (t0 + real i * step) = psolution i (t0 + real i * step) \<Longrightarrow>
        ta \<in> {t0 + real i * step--t} \<Longrightarrow>
        ta \<in> {t0--t0 + real i * step} \<Longrightarrow> psolution (LEAST i. ta \<in> S i) ta = x ta" for ta
        by (subst segment_inter[OF t], assumption, assumption)+ simp
      have "ivl_integral ?i t (\<lambda>t. f t (x t)) = ivl_integral ?i t ?f"
        by (rule ivl_integral_cong) (simp_all add: x psolution_eq)
      also
      from t right_cond(1) have cs: "closed_segment t0 t = closed_segment t0 ?i \<union> closed_segment ?i t"
        by (intro closed_segment_Un[symmetric])
          (auto simp: closed_segment_eq_real_ivl algebra_simps mult_le_0_iff split: if_split_asm
            intro!: segment_inter segment_inter[symmetric])
      have cont_if: "continuous_on (closed_segment t0 t) ?if"
        unfolding cs
        using x Suc.prems cont t psolution_eq
        by (auto simp: subset_T1 T_def intro!: continuous_on_cases solves_ode_continuous_on[OF IH_sol])
      have t_mem: "t \<in> closed_segment t0 t1"
        using x Suc.prems t
        apply -
        apply (rule closed_segment_closed_segment_subset, assumption)
        apply (rule step_in_segment, force, force)
        apply (rule step_in_segment, force, force)
        done
      have segment_subset: "ta \<in> {t0 + real i * step--t} \<Longrightarrow> ta \<in> {t0--t1}" for ta
        using x Suc.prems
        apply -
        apply (rule closed_segment_closed_segment_subset, assumption)
        subgoal by (rule step_in_segment; force)
        subgoal by (rule t_mem)
        done
      have cont_f: "continuous_on (closed_segment t0 t) ?f"
        apply (rule continuous_intros)
        apply (rule continuous_intros)
        apply (rule cont_if)
        unfolding cs
        using x Suc.prems
         apply (auto simp: subset_T1 segment_subset intro!: sol_mem subset_TI)
        done
      have "?sol t0 + ivl_integral t0 ?i ?f + ivl_integral ?i t ?f = ?if t0 + ivl_integral t0 t ?f"
        by (auto simp: cs intro!: ivl_integral_combine integrable_continuous_closed_segment
          continuous_on_subset[OF cont_f])
      also have "\<dots> \<in> X"
        apply (rule self_mapping)
        apply (rule subset_TI)
        apply (rule t_mem)
        using x cont_if
        by (auto simp: subset_T1 Pi_iff cs intro!: sol_mem)
      finally
      have "x ?i + ivl_integral ?i t (\<lambda>t. ?f t) \<in> X" .
      also have "ivl_integral ?i t (\<lambda>t. ?f t) = ivl_integral ?i t (\<lambda>t. f t (x t))"
        apply (rule ivl_integral_cong[OF _ refl refl])
        using x
        by (auto simp: segment_inter psolution_eq)
      finally
      show "x ?i + ivl_integral ?i t (\<lambda>t. f t (x t)) \<in> X" .
    qed (auto simp add: S_def closed_segment_eq_real_ivl)
    have "S (Suc i) \<subseteq> T"
      unfolding S_def
      apply (rule subsetI)
      apply (rule subset_TI)
    proof (cases "step = 0")
      case False
      fix x assume x: "x \<in> {t0 + real (Suc i - 1) * step--t0 + real (Suc i) * step}"
      from x have nn: "((x - t0) / step) \<ge> 0"
        using False right_cond(1)[of x] left_cond(2)[of x]
        by (auto simp: closed_segment_eq_real_ivl divide_simps algebra_simps split: if_splits)
      have "t1 < t0 \<Longrightarrow> t1 \<le> x" "t1 > t0 \<Longrightarrow> x \<le> t1"
        using x False right_cond(1,2)[of x] left_cond(1,2)[of x]
        by (auto simp: closed_segment_eq_real_ivl algebra_simps split: if_splits)
      then have le: "(x - t0) / step \<le> 1 + real subdivide_count"
        unfolding step_def
        by (auto simp: divide_simps)
      have "x = t0 + ((x - t0) / step) * step"
        using False
        by auto
      also have "\<dots> \<in> {t0 -- t1}"
        by (rule step_in_segment) (auto simp: nn le)
      finally show "x \<in> {t0 -- t1}" by simp
    qed simp
    have algebra: "(1 + real i) * (t1 - t0) - real i * (t1 - t0) = t1 - t0"
      by (simp only: algebra_simps)
    interpret l: unique_on_bounded_closed ?i "S (Suc i)" "?sol ?i" f X L
      apply unfold_locales
      subgoal by (auto simp: S_def)
      subgoal using \<open>S (Suc i) \<subseteq> T\<close> by (auto intro!: continuous_intros simp: split_beta')
      subgoal using \<open>S (Suc i) \<subseteq> T\<close> by (auto intro!: lipschitz)
      subgoal by (rule subdivide_lipschitz_lemma) (auto simp add: step_def divide_simps algebra S_def)
      done
    note ui
    moreover
    have mem_SI: "t \<in> closed_segment ?i ?si \<Longrightarrow> t \<in> S (if t = ?i then i else Suc i)" for t
      by (auto simp: S_def)
    have min_S: "(if t = t0 + real i * step then i else Suc i) \<le> y"
      if "t \<in> closed_segment (t0 + real i * step) (t0 + (1 + real i) * step)"
        "t \<in> S y"
      for y t
      apply (cases "t = t0 + real i * step")
      subgoal using that \<open>step \<noteq> 0\<close>
        by (auto simp add: S_def closed_segment_eq_real_ivl algebra_simps zero_le_mult_iff split: if_splits )
      subgoal premises ne
      proof (cases)
        assume "step > 0"
        with that have "t0 + real i * step \<le> t" "t \<le> t0 + (1 + real i) * step"
          "t0 + real (y - Suc 0) * step \<le> t" "t \<le> t0 + real y * step"
          by (auto simp: closed_segment_eq_real_ivl S_def)
        then have "real i * step < real y * step" using \<open>step > 0\<close> ne
          by arith
        then show ?thesis using \<open>step > 0\<close> that by (auto simp add: closed_segment_eq_real_ivl S_def)
      next
        assume "\<not> step > 0" with \<open>step \<noteq> 0\<close> have "step < 0" by simp
        with that have "t0 + (1 + real i) * step \<le> t" "t \<le> t0 + real i * step"
          "t0 + real y * step \<le> t" "t \<le> t0 + real (y - Suc 0) * step" using ne
          by (auto simp: closed_segment_eq_real_ivl S_def diff_Suc zero_le_mult_iff split: if_splits nat.splits)
        then have "real y * step < real i * step"
          using \<open>step < 0\<close> ne
          by arith
        then show ?thesis using \<open>step < 0\<close> by (auto simp add: closed_segment_eq_real_ivl S_def)
      qed
      done
    have "(?sol usolves_ode f from ?i) (closed_segment ?i ?si) X"
      apply (subst usolves_ode_cong)
      apply (subst Least_equality)
      apply (rule mem_SI) apply assumption
      apply (rule min_S) apply assumption apply assumption
      apply (rule refl)
      apply (rule refl)
      apply (rule refl)
      apply (rule refl)
      apply (rule refl)
      apply (subst usolves_ode_cong[where y="psolution (Suc i)"])
      using l.fixed_point_iv[unfolded Least_eq]
      apply (simp add: S_def; fail)
      apply (rule refl)
      apply (rule refl)
      apply (rule refl)
      apply (rule refl)
      using l.fixed_point_usolves_ode
      apply -
      apply (simp)
      apply (simp add: S_def)
      done
    moreover have "t \<in> {t0 + real i * step--t0 + (step + real i * step)} \<Longrightarrow>
         t \<in> {t0--t0 + real i * step} \<Longrightarrow> t = t0 + real i * step" for t
      by (subst segment_inter[rotated], assumption, assumption) (auto simp: algebra_simps)
    ultimately
    have "((\<lambda>t. if t \<in> closed_segment t0 ?i then ?sol t else ?sol t)
      usolves_ode
      (\<lambda>t. if t \<in> closed_segment t0 ?i then f t else f t) from t0)
      (closed_segment t0 ?i \<union> closed_segment ?i ?si) X"
      by (intro connection_usolves_ode[where t="?i"]) (auto simp: algebra_simps split: if_split_asm)
    also have "closed_segment t0 ?i \<union> closed_segment ?i ?si = closed_segment t0 ?si"
      apply (rule closed_segment_Un)
      by (cases "step < 0")
        (auto simp: closed_segment_eq_real_ivl zero_le_mult_iff mult_le_0_iff
          intro!: mult_right_mono
          split: if_split_asm)
    finally show ?case by simp
  qed
qed

lemma psolutions_usolves_ode: "(psolutions usolves_ode f from t0) {t0 -- t1} X"
proof -
  let ?T = "closed_segment t0 (t0 + real (Suc subdivide_count) * step)"
  have "(psolutions usolves_ode f from t0) ?T X"
    by (rule psolutions_usolves_until_step) simp
  also have "?T = {t0 -- t1}" unfolding last_step ..
  finally show ?thesis .
qed

end

definition "solution t = (if t \<le> t0 then psolutions tmin t else psolutions tmax t)"

lemma solution_eq_left: "tmin \<le> t \<Longrightarrow> t \<le> t0 \<Longrightarrow> solution t = psolutions tmin t"
  by (simp add: solution_def)

lemma solution_eq_right: "t0 \<le> t \<Longrightarrow> t \<le> tmax \<Longrightarrow> solution t = psolutions tmax t"
  by (simp add: solution_def psolutions_def)

lemma solution_usolves_ode: "(solution usolves_ode f from t0) T X"
proof -
  from psolutions_usolves_ode[OF tmin(2)] tmin_le_t0
  have u1: "(psolutions tmin usolves_ode f from t0) {tmin .. t0} X"
    by (auto simp: closed_segment_eq_real_ivl split: if_splits)
  from psolutions_usolves_ode[OF tmax(2)] tmin_le_t0
  have u2: "(psolutions tmax usolves_ode f from t0) {t0 .. tmax} X"
    by (auto simp: closed_segment_eq_real_ivl split: if_splits)
  have "(solution usolves_ode f from t0) ({tmin .. t0} \<union> {t0 .. tmax}) (X \<union> X)"
    apply (rule usolves_ode_union_closed[where t=t0])
    subgoal by (subst usolves_ode_cong[where y="psolutions tmin"]) (auto simp: solution_eq_left u1)
    subgoal
      using u2
      by (rule usolves_ode_congI) (auto simp: solution_eq_right)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    done
  also have "{tmin .. t0} \<union> {t0 .. tmax} = T"
    by (simp add: T_split[symmetric])
  finally show ?thesis by simp
qed

lemma solution_solves_ode: "(solution solves_ode f) T X"
  by (rule usolves_odeD[OF solution_usolves_ode])

lemma solution_iv[simp]: "solution t0 = x0"
  by (auto simp: solution_def psolutions_def)

end


subsection \<open>Picard-Lindeloef for @{term "X = UNIV"}\<close>
text\<open>\label{sec:pl-us}\<close>

locale unique_on_strip =
  compact_interval T +
  continuous_rhs T UNIV f +
  global_lipschitz T UNIV f L
  for t0 and T and f::"real \<Rightarrow> 'a \<Rightarrow> 'a::banach" and L +
  assumes iv_time: "t0 \<in> T"
begin

sublocale unique_on_closed t0 T x0 f UNIV L for x0
  by (-, unfold_locales) (auto simp: iv_time)

end


subsection \<open>Picard-Lindeloef on cylindric domain\<close>
text\<open>\label{sec:pl-rect}\<close>

locale solution_in_cylinder =
  continuous_rhs T "cball x0 b" f +
  compact_interval T
  for t0 T x0 b and f::"real \<Rightarrow> 'a \<Rightarrow> 'a::banach" +
  fixes X B
  defines "X \<equiv> cball x0 b"
  assumes initial_time_in: "t0 \<in> T"
  assumes norm_f: "\<And>x t. t \<in> T \<Longrightarrow> x \<in> X \<Longrightarrow> norm (f t x) \<le> B"
  assumes b_pos: "b \<ge> 0"
  assumes e_bounded: "\<And>t. t \<in> T \<Longrightarrow> dist t t0 \<le> b / B"
begin

lemmas cylinder = X_def

lemma B_nonneg: "B \<ge> 0"
proof -
  have "0 \<le> norm (f t0 x0)" by simp
  also from b_pos norm_f have "... \<le> B" by (simp add: initial_time_in X_def)
  finally show ?thesis by simp
qed

lemma in_bounds_derivativeI:
  assumes "t \<in> T"
  assumes init: "x t0 = x0"
  assumes cont: "continuous_on (closed_segment t0 t) x"
  assumes solves: "(x has_vderiv_on (\<lambda>s. f s (y s))) (open_segment t0 t)"
  assumes y_bounded: "\<And>\<xi>. \<xi> \<in> closed_segment t0 t \<Longrightarrow> x \<xi> \<in> X \<Longrightarrow> y \<xi> \<in> X"
  shows "x t \<in> cball x0 (B * abs (t - t0))"
proof cases
  assume "b = 0 \<or> B = 0" with assms e_bounded T_def have "t = t0"
    by auto
  thus ?thesis using b_pos init by simp
next
  assume "\<not>(b = 0 \<or> B = 0)"
  hence "b > 0" "B > 0" using B_nonneg b_pos by auto
  show ?thesis
  proof cases
    assume "t0 \<noteq> t"
    then have b_less: "B * abs (t - t0) \<le> b"
      using b_pos e_bounded using \<open>b > 0\<close> \<open>B > 0\<close> \<open>t \<in> T\<close>
      by (auto simp: field_simps initial_time_in dist_real_def abs_real_def closed_segment_eq_real_ivl split: if_split_asm)
    define b where  "b \<equiv> B * abs (t - t0)"
    have "b > 0" using \<open>t0 \<noteq> t\<close> by (auto intro!: mult_pos_pos simp: algebra_simps b_def \<open>B > 0\<close>)
    from cont
    have closed: "closed (closed_segment t0 t \<inter> ((\<lambda>s. norm (x s - x t0)) -` {b..}))"
      by (intro continuous_closed_preimage continuous_intros closed_segment)
    have exceeding: "{s \<in> closed_segment t0 t. norm (x s - x t0) \<in> {b..}} \<subseteq> {t}"
    proof (rule ccontr)
      assume "\<not>{s \<in> closed_segment t0 t. norm (x s - x t0) \<in> {b..}} \<subseteq> {t}"
      hence notempty: "(closed_segment t0 t \<inter> ((\<lambda>s. norm (x s - x t0)) -` {b..})) \<noteq> {}"
        and not_max: "{s \<in> closed_segment t0 t. norm (x s - x t0) \<in> {b..}} \<noteq> {t}"
        by auto
      obtain s where s_bound: "s \<in> closed_segment t0 t"
        and exceeds: "norm (x s - x t0) \<in> {b..}"
        and min: "\<forall>t2\<in>closed_segment t0 t.
          norm (x t2 - x t0) \<in> {b..} \<longrightarrow> dist t0 s \<le> dist t0 t2"
        by (rule distance_attains_inf[OF closed notempty, of t0]) blast
      have "s \<noteq> t0" using exceeds \<open>b > 0\<close> by auto
      have st: "closed_segment t0 t \<supseteq> open_segment t0 s" using s_bound
        by (auto simp: closed_segment_eq_real_ivl open_segment_eq_real_ivl)
      from cont have cont: "continuous_on (closed_segment t0 s) x"
        by (rule continuous_on_subset)
          (insert b_pos closed_segment_subset_domain s_bound, auto simp: closed_segment_eq_real_ivl)
      have bnd_cont: "continuous_on (closed_segment t0 s) ((*) B)"
        and bnd_deriv: "((*) B has_vderiv_on (\<lambda>_. B)) (open_segment t0 s)"
        by (auto intro!: continuous_intros derivative_eq_intros
          simp: has_vector_derivative_def has_vderiv_on_def)
      {
        fix ss assume ss: "ss \<in> open_segment t0 s"
        with st have "ss \<in> closed_segment t0 t" by auto
        have less_b: "norm (x ss - x t0) < b"
        proof (rule ccontr)
          assume "\<not> norm (x ss - x t0) < b"
          hence "norm (x ss - x t0) \<in> {b..}" by auto
          from min[rule_format, OF \<open>ss \<in> closed_segment t0 t\<close> this]
          show False using ss \<open>s \<noteq> t0\<close>
            by (auto simp: dist_real_def open_segment_eq_real_ivl split_ifs)
        qed
        have "norm (f ss (y ss)) \<le> B"
          apply (rule norm_f)
          subgoal using ss st closed_segment_subset_domain[OF initial_time_in \<open>t \<in> T\<close>] by auto
          subgoal using ss st b_less less_b
            by (intro y_bounded)
              (auto simp: X_def dist_norm b_def init norm_minus_commute mem_cball)
          done
      } note bnd = this
      have subs: "open_segment t0 s \<subseteq> open_segment t0 t" using s_bound \<open>s \<noteq> t0\<close>
        by (auto simp: closed_segment_eq_real_ivl open_segment_eq_real_ivl)
      with differentiable_bound_general_open_segment[OF cont bnd_cont has_vderiv_on_subset[OF solves subs]
        bnd_deriv bnd]
      have "norm (x s - x t0) \<le> B * \<bar>s - t0\<bar>"
        by (auto simp: algebra_simps[symmetric] abs_mult B_nonneg)
      also
      have "s \<noteq> t"
        using s_bound exceeds min not_max
        by (auto simp: dist_norm closed_segment_eq_real_ivl split_ifs)
      hence "B * \<bar>s - t0\<bar> < \<bar>t - t0\<bar> * B"
        using s_bound \<open>B > 0\<close>
        by (intro le_neq_trans)
          (auto simp: algebra_simps closed_segment_eq_real_ivl split_ifs
            intro!: mult_left_mono)
      finally have "norm (x s - x t0) < \<bar>t - t0\<bar> * B" .
      moreover
      {
        have "b \<ge> \<bar>t - t0\<bar> * B" by (simp add: b_def algebra_simps)
        also from exceeds have "norm (x s - x t0) \<ge> b" by simp
        finally have "\<bar>t - t0\<bar> * B \<le> norm (x s - x t0)" .
      }
      ultimately show False by simp
    qed note mvt_result = this
    from cont assms
    have cont_diff: "continuous_on (closed_segment t0 t) (\<lambda>xa. x xa - x t0)"
      by (auto intro!: continuous_intros)
    have "norm (x t - x t0) \<le> b"
    proof (rule ccontr)
      assume H: "\<not> norm (x t - x t0) \<le> b"
      hence "b \<in> closed_segment (norm (x t0 - x t0)) (norm (x t - x t0))"
        using assms T_def \<open>0 < b\<close>
        by (auto simp: closed_segment_eq_real_ivl )
      from IVT'_closed_segment_real[OF this continuous_on_norm[OF cont_diff]]
      obtain s where s: "s \<in> closed_segment t0 t" "norm (x s - x t0) = b"
        using \<open>b > 0\<close> by auto
      have "s \<in> {s \<in> closed_segment t0 t. norm (x s - x t0) \<in> {b..}}"
        using s \<open>t \<in> T\<close> by (auto simp: initial_time_in)
      with mvt_result have "s = t" by blast
      hence "s = t" using s \<open>t \<in> T\<close> by (auto simp: initial_time_in)
      with s H show False by simp
    qed
    hence "x t \<in> cball x0 b" using init
      by (auto simp: dist_commute dist_norm[symmetric] mem_cball)
    thus "x t \<in> cball x0 (B * abs (t - t0))" unfolding cylinder b_def .
  qed (simp add: init[symmetric])
qed

lemma in_bounds_derivative_globalI:
  assumes "t \<in> T"
  assumes init: "x t0 = x0"
  assumes cont: "continuous_on (closed_segment t0 t) x"
  assumes solves: "(x has_vderiv_on (\<lambda>s. f s (y s))) (open_segment t0 t)"
  assumes y_bounded: "\<And>\<xi>. \<xi> \<in> closed_segment t0 t \<Longrightarrow> x \<xi> \<in> X \<Longrightarrow> y \<xi> \<in> X"
  shows "x t \<in> X"
proof -
  from in_bounds_derivativeI[OF assms]
  have "x t \<in> cball x0 (B * abs (t - t0))" .
  moreover have "B * abs (t - t0) \<le> b" using e_bounded b_pos B_nonneg \<open>t \<in> T\<close>
    by (cases "B = 0")
      (auto simp: field_simps initial_time_in dist_real_def abs_real_def closed_segment_eq_real_ivl split: if_splits)
  ultimately show ?thesis by (auto simp: cylinder mem_cball)
qed

lemma integral_in_bounds:
  assumes "t \<in> T" "x t0 = x0" "x \<in> {t0 -- t} \<rightarrow> X"
  assumes cont[continuous_intros]: "continuous_on ({t0 -- t}) x"
  shows "x t0 + ivl_integral t0 t (\<lambda>t. f t (x t)) \<in> X" (is "_ + ?ix t \<in> X")
proof cases
  assume "t = t0"
  thus ?thesis by (auto simp: cylinder b_pos assms)
next
  assume "t \<noteq> t0"
  from closed_segment_subset_domain[OF initial_time_in]
  have cont_f:"continuous_on {t0 -- t} (\<lambda>t. f t (x t))"
    using assms
    by (intro continuous_intros)
      (auto intro: cont continuous_on_subset[OF continuous] simp: cylinder split: if_splits)
  from closed_segment_subset_domain[OF initial_time_in \<open>t \<in> T\<close>]
  have subsets: "s \<in> {t0--t} \<Longrightarrow> s \<in> T" "s \<in> open_segment t0 t \<Longrightarrow> s \<in> {t0--t}" for s
    by (auto simp: closed_segment_eq_real_ivl open_segment_eq_real_ivl initial_time_in split: if_split_asm)
  show ?thesis
    unfolding \<open>x t0 = _\<close>
    using assms \<open>t \<noteq> t0\<close>
    by (intro in_bounds_derivative_globalI[where y=x and x="\<lambda>t. x0 + ?ix t"])
      (auto simp: initial_time_in subsets cylinder has_vderiv_on_def
        split: if_split_asm
        intro!: cont_f has_vector_derivative_const integrable_continuous_closed_segment
          has_vector_derivative_within_subset[OF ivl_integral_has_vector_derivative]
          has_vector_derivative_add[THEN has_vector_derivative_eq_rhs]
          continuous_intros indefinite_ivl_integral_continuous)
qed

lemma solves_in_cone:
  assumes "t \<in> T"
  assumes init: "x t0 = x0"
  assumes cont: "continuous_on (closed_segment t0 t) x"
  assumes solves: "(x has_vderiv_on (\<lambda>s. f s (x s))) (open_segment t0 t)"
  shows "x t \<in> cball x0 (B * abs (t - t0))"
  using assms
  by (rule in_bounds_derivativeI)

lemma is_solution_in_cone:
  assumes "t \<in> T"
  assumes sol: "(x solves_ode f) (closed_segment t0 t) Y" and iv: "x t0 = x0"
  shows "x t \<in> cball x0 (B * abs (t - t0))"
  using solves_odeD[OF sol] \<open>t \<in> T\<close>
  by (intro solves_in_cone)
    (auto intro!: assms vderiv_on_continuous_on segment_open_subset_closed
      intro: has_vderiv_on_subset simp: initial_time_in)

lemma cone_subset_domain:
  assumes "t \<in> T"
  shows "cball x0 (B * \<bar>t - t0\<bar>) \<subseteq> X"
  using e_bounded[OF assms] B_nonneg b_pos
  unfolding cylinder
  by (intro subset_cball) (auto simp: dist_real_def divide_simps algebra_simps split: if_splits)

lemma is_solution_in_domain:
  assumes "t \<in> T"
  assumes sol: "(x solves_ode f) (closed_segment t0 t) Y" and iv: "x t0 = x0"
  shows "x t \<in> X"
  using is_solution_in_cone[OF assms] cone_subset_domain[OF \<open>t \<in> T\<close>]
  by (rule rev_subsetD)

lemma solves_ode_on_subset_domain:
  assumes sol: "(x solves_ode f) S Y" and iv: "x t0 = x0"
    and ivl: "t0 \<in> S" "is_interval S" "S \<subseteq> T"
  shows "(x solves_ode f) S X"
proof (rule solves_odeI)
  show "(x has_vderiv_on (\<lambda>t. f t (x t))) S" using solves_odeD(1)[OF sol] .
  show "x s \<in> X" if s: "s \<in> S" for s
  proof -
    from s assms have "s \<in> T"
      by auto
    moreover
    have "{t0--s} \<subseteq> S"
      by (rule closed_segment_subset) (auto simp: s assms is_interval_convex)
    with sol have "(x solves_ode f) {t0--s} Y"
      using order_refl
      by (rule solves_ode_on_subset)
    ultimately
    show ?thesis using iv
      by (rule is_solution_in_domain)
  qed
qed

lemma usolves_ode_on_subset:
  assumes x: "(x usolves_ode f from t0) T X" and iv: "x t0 = x0"
  assumes "t0 \<in> S" "is_interval S" "S \<subseteq> T" "X \<subseteq> Y"
  shows "(x usolves_ode f from t0) S Y"
proof (rule usolves_odeI)
  show "(x solves_ode f) S Y" by (rule solves_ode_on_subset[OF usolves_odeD(1)[OF x]]; fact)
  show "t0 \<in> S" "is_interval S" by fact+
  fix z t assume "{t0 -- t} \<subseteq> S" and z: "(z solves_ode f) {t0--t} Y" "z t0 = x t0"
  then have "z t0 = x0" "t0 \<in> {t0--t}" "is_interval {t0--t}" "{t0--t} \<subseteq> T"
    using iv \<open>S \<subseteq> T\<close> by (auto simp: is_interval_convex_1)
  with z(1) have zX: "(z solves_ode f) {t0 -- t} X"
    by (rule solves_ode_on_subset_domain)
  show "z t = x t"
    apply (rule usolves_odeD(4)[OF x _ _ _ zX])
    using \<open>{t0 -- t} \<subseteq> S\<close> \<open>S \<subseteq> T\<close>
    by (auto simp: is_interval_convex_1 \<open>z t0 = x t0\<close>)
qed

lemma usolves_ode_on_superset_domain:
  assumes "(x usolves_ode f from t0) T X" and iv: "x t0 = x0"
  assumes "X \<subseteq> Y"
  shows "(x usolves_ode f from t0) T Y"
  using assms(1,2) usolves_odeD(2,3)[OF assms(1)] order_refl assms(3)
  by (rule usolves_ode_on_subset)

end

locale unique_on_cylinder =
  solution_in_cylinder t0 T x0 b f X B +
  global_lipschitz T X f L
  for t0 T x0 b X f B L
begin

sublocale unique_on_closed t0 T x0 f X L
  apply unfold_locales
  subgoal by (simp add: initial_time_in)
  subgoal by (simp add: X_def b_pos)
  subgoal by (auto intro!: integral_in_bounds simp: initial_time_in)
  subgoal by (auto intro!: continuous_intros simp: split_beta' X_def)
  subgoal by (simp add: X_def)
  done

end

locale derivative_on_prod =
  fixes T X and f::"real \<Rightarrow> 'a::banach \<Rightarrow> 'a" and f':: "real \<times> 'a \<Rightarrow> (real \<times> 'a) \<Rightarrow> 'a"
  assumes f': "\<And>tx. tx \<in> T \<times> X \<Longrightarrow> ((\<lambda>(t, x). f t x) has_derivative (f' tx)) (at tx within (T \<times> X))"
begin

lemma f'_comp[derivative_intros]:
  "(g has_derivative g') (at s within S) \<Longrightarrow> (h has_derivative h') (at s within S) \<Longrightarrow>
  s \<in> S \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> g x \<in> T) \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> h x \<in> X) \<Longrightarrow>
  ((\<lambda>x. f (g x) (h x)) has_derivative (\<lambda>y. f' (g s, h s) (g' y, h' y))) (at s within S)"
  apply (rule has_derivative_in_compose2[OF f' _ _ has_derivative_Pair, unfolded split_beta' fst_conv snd_conv, of g h S s g' h'])
  apply auto
  done

lemma derivative_on_prod_subset:
  assumes "X' \<subseteq> X"
  shows "derivative_on_prod T X' f f'"
  using assms
  by (unfold_locales) (auto intro!: derivative_eq_intros)

end

end
