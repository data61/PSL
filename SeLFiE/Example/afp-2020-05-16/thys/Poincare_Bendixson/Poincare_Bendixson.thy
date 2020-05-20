section \<open>Poincare Bendixson Theory\<close>
theory Poincare_Bendixson
  imports 
    Ordinary_Differential_Equations.ODE_Analysis
    Analysis_Misc ODE_Misc Periodic_Orbit
begin


subsection \<open>Flow to Path\<close>

context auto_ll_on_open begin

(* The path along the flow starting at time t to time t' *)
definition "flow_to_path x t t' = flow0 x \<circ> linepath t t'"

lemma pathstart_flow_to_path[simp]:
  shows "pathstart (flow_to_path x t t') = flow0 x t"
  unfolding flow_to_path_def
  by (auto simp add: pathstart_compose)

lemma pathfinish_flow_to_path[simp]:
  shows "pathfinish (flow_to_path x t t') = flow0 x t'"
  unfolding flow_to_path_def
  by (auto simp add: pathfinish_compose)

lemma flow_to_path_unfold:
  shows "flow_to_path x t t' s = flow0 x ((1 - s) * t + s * t')"
  unfolding flow_to_path_def o_def linepath_def by auto

lemma subpath0_flow_to_path:
  shows "(subpath 0 u (flow_to_path x t t')) = flow_to_path x t (t + u*(t'-t))"
  unfolding flow_to_path_def subpath_image subpath0_linepath
  by auto

lemma path_image_flow_to_path[simp]:
  assumes "t \<le> t'"
  shows "path_image (flow_to_path x t t') = flow0 x ` {t..t'}"
  unfolding flow_to_path_def path_image_compose path_image_linepath
  using assms real_Icc_closed_segment by auto

lemma flow_to_path_image0_right_open[simp]:
  assumes "t < t'"
  shows "flow_to_path x t t' ` {0..<1} = flow0 x `{t..<t'}"
  unfolding flow_to_path_def image_comp[symmetric] linepath_image0_right_open_real[OF assms]
  by auto

lemma flow_to_path_path:
  assumes "t \<le> t'"
  assumes "{t..t'} \<subseteq> existence_ivl0 x"
  shows "path (flow_to_path x t t')"
proof -
  have "x \<in> X"
    using assms(1) assms(2) subset_empty by fastforce
  have "\<And>xa. 0 \<le> xa \<Longrightarrow> xa \<le> 1 \<Longrightarrow>  (1 - xa) * t + xa * t' \<le> t'"
    by (simp add: assms(1) convex_bound_le)
  moreover have "\<And>xa. 0 \<le> xa \<Longrightarrow> xa \<le> 1 \<Longrightarrow> t \<le> (1 - xa) * t + xa * t'" using assms(1)
    by (metis add.commute add_diff_cancel_left' diff_diff_eq2 diff_le_eq mult.commute mult.right_neutral mult_right_mono right_diff_distrib')
  ultimately have "\<And>xa. 0 \<le> xa \<Longrightarrow> xa \<le> 1 \<Longrightarrow> (1 - xa) * t + xa * t' \<in> existence_ivl0 x"
    using assms(2) by auto
  thus ?thesis unfolding path_def flow_to_path_def linepath_def
    by (auto intro!:continuous_intros simp add :\<open>x \<in> X\<close>)
qed

lemma flow_to_path_arc:
  assumes "t \<le> t'"
  assumes "{t..t'} \<subseteq> existence_ivl0 x"
  assumes "\<forall>s \<in> {t<..<t'}. flow0 x s \<noteq> flow0 x t"
  assumes "flow0 x t \<noteq> flow0 x t'"
  shows "arc (flow_to_path x t t')"
  unfolding arc_def
proof safe
  from flow_to_path_path[OF assms(1-2)]
  show "path (flow_to_path x t t')" .
next
  show "inj_on (flow_to_path x t t') {0..1}"
    unfolding flow_to_path_def
    apply (rule comp_inj_on)
     apply (metis assms(4) inj_on_linepath)
    using assms path_image_linepath[of t t'] apply (auto intro!:flow0_inj_on)
    using flow0_inj_on greaterThanLessThan_iff linepath_image_01 real_Icc_closed_segment by fastforce
qed

end

locale c1_on_open_R2 = c1_on_open_euclidean f f' X for f::"'a::executable_euclidean_space \<Rightarrow> _" and f' and X +
  assumes dim2: "DIM('a) = 2"
begin


subsection \<open>2D Line segments\<close>

text \<open>Line segments are specified by two endpoints
      The closed line segment from x to y is given by the set {x--y}
      and {x<--<y} for the open segment\<close>

text \<open> Rotates a vector clockwise 90 degrees \<close>
definition "rot (v::'a) = (eucl_of_list [nth_eucl v 1, -nth_eucl v 0]::'a)"

lemma exhaust2_nat: "(\<forall>i<(2::nat). P i) \<longleftrightarrow> P 0 \<and> P 1"
  using less_2_cases by auto
lemma sum2_nat: "(\<Sum>i<(2::nat). P i) = P 0 + P 1"
  by (simp add: eval_nat_numeral)

lemmas vec_simps =
  eucl_eq_iff[where 'a='a] dim2 eucl_of_list_eucl_nth exhaust2_nat
  plus_nth_eucl
  minus_nth_eucl
  uminus_nth_eucl
  scaleR_nth_eucl
  inner_nth_eucl
  sum2_nat
  algebra_simps

lemma minus_expand:
  shows "(x::'a)-y = (eucl_of_list [x$\<^sub>e0 - y$\<^sub>e0, x$\<^sub>e1 - y$\<^sub>e1])"
  by (simp add:vec_simps)

lemma dot_ortho[simp]: "x \<bullet> rot x = 0"
  unfolding rot_def minus_expand
  by (simp add: vec_simps)

lemma nrm_dot:
  shows "((x::'a)-y) \<bullet> (rot (x-y)) = 0"
  unfolding rot_def minus_expand
  by (simp add: vec_simps)

lemma nrm_reverse: "a \<bullet> (rot (x-y)) = - a \<bullet> (rot (y-x))" for x y::'a
  unfolding rot_def
  by (simp add:vec_simps)

lemma norm_rot: "norm (rot v) = norm v" for v::'a
  unfolding rot_def
  by (simp add:vec_simps norm_nth_eucl L2_set_def)

lemma rot_rot[simp]:
  shows "rot (rot v) = -v"
  unfolding rot_def
  by (simp add:vec_simps)

lemma rot_scaleR[simp]:
  shows "rot ( u *\<^sub>R v) =  u *\<^sub>R (rot v)"
  unfolding rot_def
  by (simp add:vec_simps)

lemma rot_0[simp]: "rot 0 = 0"
  using rot_scaleR[of 0] by simp

lemma rot_eq_0_iff[simp]: "rot x = 0 \<longleftrightarrow> x = 0"
  apply (auto simp: rot_def)
   apply (metis One_nat_def norm_eq_zero norm_rot norm_zero rot_def)
  using rot_0 rot_def by auto

lemma in_segment_inner_rot:
  "(x - a) \<bullet> rot (b - a) = 0"
  if "x \<in> {a--b}"
proof -
  from that obtain u where x: "x = a + u *\<^sub>R (b - a)" "0 \<le> u" "u \<le> 1"
    by (auto simp: in_segment algebra_simps)
  show ?thesis
    unfolding x
    by (simp add: inner_add_left nrm_dot)
qed

lemma inner_rot_in_segment:
  "x \<in> range (\<lambda>u. a + u *\<^sub>R (b - a))"
  if "(x - a) \<bullet> rot (b - a) = 0" "a \<noteq> b"
proof -
  from that have
    x0: "b $\<^sub>e 0 = a $\<^sub>e 0 \<Longrightarrow> x $\<^sub>e 0 =
      (a $\<^sub>e 0 * b $\<^sub>e Suc 0 - b $\<^sub>e 0 * a $\<^sub>e Suc 0 + (b $\<^sub>e 0 - a $\<^sub>e 0) * x $\<^sub>e Suc 0) /
      (b $\<^sub>e Suc 0 - a $\<^sub>e Suc 0)"
    and x1: "b $\<^sub>e 0 \<noteq> a $\<^sub>e 0 \<Longrightarrow> x $\<^sub>e Suc 0 =
      ((b $\<^sub>e Suc 0 - a $\<^sub>e Suc 0) * x $\<^sub>e 0 - a $\<^sub>e 0 * b $\<^sub>e Suc 0 + b $\<^sub>e 0 * a $\<^sub>e Suc 0) / (b $\<^sub>e 0 - a $\<^sub>e 0)"
    by (auto simp: rot_def vec_simps divide_simps)
  define u where "u = (if b $\<^sub>e 0 - a $\<^sub>e 0 \<noteq> 0
    then ((x $\<^sub>e 0 - a $\<^sub>e 0) / (b $\<^sub>e 0 -  a $\<^sub>e 0))
    else ((x $\<^sub>e 1 - a $\<^sub>e 1) / (b $\<^sub>e 1 -  a $\<^sub>e 1)))
    "
  show ?thesis
    apply (cases "b $\<^sub>e 0 - a $\<^sub>e 0 = 0")
    subgoal
      using that(2)
      apply (auto intro!: image_eqI[where x="((x $\<^sub>e 1 - a $\<^sub>e 1) / (b $\<^sub>e 1 -  a $\<^sub>e 1))"]
          simp: vec_simps x0 divide_simps algebra_simps)
       apply (metis ab_semigroup_mult_class.mult_ac(1) mult.commute sum_sqs_eq)
      by (metis mult.commute mult.left_commute sum_sqs_eq)
    subgoal
      apply (auto intro!: image_eqI[where x="((x $\<^sub>e 0 - a $\<^sub>e 0) / (b $\<^sub>e 0 -  a $\<^sub>e 0))"]
          simp: vec_simps x1 divide_simps algebra_simps)
       apply (metis ab_semigroup_mult_class.mult_ac(1) mult.commute sum_sqs_eq)
      by (metis mult.commute mult.left_commute sum_sqs_eq)
    done
qed

lemma in_open_segment_iff_rot:
  "x \<in> {a<--<b} \<longleftrightarrow> (x - a) \<bullet> rot (b - a) = 0 \<and> x \<bullet> (b - a) \<in> {a\<bullet>(b - a) <..< b \<bullet> (b - a)}"
  if "a \<noteq> b"
  unfolding open_segment_line_hyperplanes[OF that]
  by (auto simp: nrm_dot intro!: inner_rot_in_segment)

lemma in_open_segment_rotD:
  "x \<in> {a<--<b} \<Longrightarrow> (x - a) \<bullet> rot (b - a) = 0 \<and> x \<bullet> (b - a) \<in> {a\<bullet>(b - a) <..< b \<bullet> (b - a)}"
  by (subst in_open_segment_iff_rot[symmetric]) auto

lemma in_closed_segment_iff_rot:
  "x \<in> {a--b} \<longleftrightarrow> (x - a) \<bullet> rot (b - a) = 0 \<and> x \<bullet> (b - a) \<in> {a\<bullet>(b - a) .. b \<bullet> (b - a)}"
  if "a \<noteq> b"
  unfolding closed_segment_line_hyperplanes[OF that] using that
  by (auto simp: nrm_dot intro!: inner_rot_in_segment)

lemma in_segment_inner_rot2:
  "(x - y) \<bullet> rot (a - b) = 0"
  if "x \<in> {a--b}" "y \<in> {a--b}"
proof -
  from that obtain u where x: "x = a + u *\<^sub>R (b - a)" "0 \<le> u" "u \<le> 1"
    by (auto simp: in_segment algebra_simps)
  from that obtain v where y: "y = a + v *\<^sub>R (b - a)" "0 \<le> v" "v \<le> 1"
    by (auto simp: in_segment algebra_simps)
  show ?thesis
    unfolding x y
    apply (auto simp: inner_add_left )
    by (smt add_diff_cancel_left' in_segment_inner_rot inner_diff_left minus_diff_eq nrm_reverse that(1) that(2) x(1) y(1))
qed

lemma closed_segment_surface:
  "a \<noteq> b \<Longrightarrow> {a--b} = { x \<in> {x. x \<bullet> (b - a) \<in> {a\<bullet>(b - a) .. b \<bullet> (b - a)}}. (x - a) \<bullet> rot (b - a) = 0}"
  by (auto simp: in_closed_segment_iff_rot)

lemma rot_diff_commute: "rot (b - a) = -rot(a - b)"
  apply (auto simp: rot_def algebra_simps)
  by (metis One_nat_def minus_diff_eq rot_def rot_rot)


subsection \<open>Bijection Real-Complex for Jordan Curve Theorem\<close>

definition "complex_of (x::'a) = x$\<^sub>e0 + \<i> * x$\<^sub>e1"

definition "real_of (x::complex) = (eucl_of_list [Re x, Im x]::'a)"

lemma complex_of_linear:
  shows "linear complex_of"
  unfolding complex_of_def
  apply (auto intro!:linearI simp add: distrib_left plus_nth_eucl)
  by (simp add: of_real_def scaleR_add_right scaleR_nth_eucl)

lemma complex_of_bounded_linear:
  shows "bounded_linear complex_of"
  unfolding complex_of_def
  apply (auto intro!:bounded_linearI' simp add: distrib_left plus_nth_eucl)
  by (simp add: of_real_def scaleR_add_right scaleR_nth_eucl)

lemma real_of_linear:
  shows "linear real_of"
  unfolding real_of_def
  by (auto intro!:linearI simp add: vec_simps)

lemma real_of_bounded_linear:
  shows "bounded_linear real_of"
  unfolding real_of_def
  by (auto intro!:bounded_linearI' simp add: vec_simps)

lemma complex_of_real_of:
  "(complex_of \<circ> real_of) = id"
  unfolding complex_of_def real_of_def
  using complex_eq by (auto simp add:vec_simps)

lemma real_of_complex_of:
  "(real_of \<circ> complex_of) = id"
  unfolding complex_of_def real_of_def
  using complex_eq by (auto simp add:vec_simps)

lemma complex_of_bij:
  shows "bij (complex_of)"
  using o_bij[OF real_of_complex_of complex_of_real_of] .

lemma real_of_bij:
  shows "bij (real_of)"
  using o_bij[OF complex_of_real_of real_of_complex_of] .

lemma real_of_inj:
  shows "inj (real_of)"
  using real_of_bij
  using bij_betw_imp_inj_on by auto

lemma Jordan_curve_R2:
  fixes c :: "real \<Rightarrow> 'a"
  assumes "simple_path c" "pathfinish c = pathstart c"
  obtains inside outside where
    "inside \<noteq> {}" "open inside" "connected inside"
    "outside \<noteq> {}" "open outside" "connected outside"
    "bounded inside" "\<not> bounded outside"
    "inside \<inter> outside = {}"
    "inside \<union> outside = - path_image c"
    "frontier inside = path_image c"
    "frontier outside = path_image c"
proof -
  from simple_path_linear_image_eq[OF complex_of_linear]
  have a1:"simple_path (complex_of \<circ> c)" using assms(1) complex_of_bij
    using bij_betw_imp_inj_on by blast
  have a2:"pathfinish (complex_of \<circ> c) = pathstart (complex_of \<circ> c)"
    using assms(2) by (simp add:pathstart_compose pathfinish_compose)

  from Jordan_curve[OF a1 a2]
  obtain inside outside where io:
    "inside \<noteq> {}" "open inside" "connected inside"
    "outside \<noteq> {}" "open outside" "connected outside"
    "bounded inside" "\<not> bounded outside" "inside \<inter> outside = {}"
    "inside \<union> outside = - path_image (complex_of \<circ> c)"
    "frontier inside = path_image (complex_of \<circ> c)"
    "frontier outside = path_image (complex_of \<circ> c)" by blast
  let ?rin = "real_of ` inside"
  let ?rout = "real_of ` outside"
  have i: "inside = complex_of ` ?rin" using complex_of_real_of unfolding image_comp
    by auto
  have o: "outside = complex_of ` ?rout" using complex_of_real_of unfolding image_comp
    by auto
  have c: "path_image(complex_of \<circ> c) = complex_of ` (path_image c)"
    by (simp add: path_image_compose)
  have "?rin \<noteq> {}" using io by auto
  moreover from open_bijective_linear_image_eq[OF real_of_linear real_of_bij]
  have "open ?rin" using io by auto
  moreover from connected_linear_image[OF real_of_linear]
  have "connected ?rin" using io by auto
  moreover have "?rout \<noteq> {}" using io by auto
  moreover from open_bijective_linear_image_eq[OF real_of_linear real_of_bij]
  have "open ?rout" using io by auto
  moreover from connected_linear_image[OF real_of_linear]
  have "connected ?rout" using io by auto
  moreover from bounded_linear_image[OF io(7) real_of_bounded_linear]
  have "bounded ?rin" .
  moreover from bounded_linear_image[OF _ complex_of_bounded_linear]
  have "\<not> bounded ?rout" using io(8) o
    by force
  from image_Int[OF real_of_inj]
  have "?rin \<inter> ?rout = {}" using io(9) by auto
  moreover from bij_image_Compl_eq[OF complex_of_bij]
  have "?rin \<union> ?rout = - path_image c" using io(10) unfolding c
    by (metis id_apply image_Un image_comp image_cong image_ident real_of_complex_of)
  moreover from closure_injective_linear_image[OF real_of_linear real_of_inj]
  have "frontier ?rin = path_image c" using io(11)
    unfolding frontier_closures c
    by (metis \<open>\<And>B A. real_of ` (A \<inter> B) = real_of ` A \<inter> real_of ` B\<close> bij_image_Compl_eq c calculation(9) compl_sup double_compl io(10) real_of_bij)
  moreover from closure_injective_linear_image[OF real_of_linear real_of_inj]
  have "frontier ?rout = path_image c" using io(12)
    unfolding frontier_closures c
    by (metis \<open>\<And>B A. real_of ` (A \<inter> B) = real_of ` A \<inter> real_of ` B\<close> bij_image_Compl_eq c calculation(10) frontier_closures io(11) real_of_bij)
  ultimately show ?thesis
    by (meson \<open>\<not> bounded (real_of ` outside)\<close> that)
qed

(* copied *)
corollary Jordan_inside_outside_R2:
  fixes c :: "real \<Rightarrow> 'a"
  assumes "simple_path c" "pathfinish c = pathstart c"
  shows "inside(path_image c) \<noteq> {} \<and>
          open(inside(path_image c)) \<and>
          connected(inside(path_image c)) \<and>
          outside(path_image c) \<noteq> {} \<and>
          open(outside(path_image c)) \<and>
          connected(outside(path_image c)) \<and>
          bounded(inside(path_image c)) \<and>
          \<not> bounded(outside(path_image c)) \<and>
          inside(path_image c) \<inter> outside(path_image c) = {} \<and>
          inside(path_image c) \<union> outside(path_image c) =
          - path_image c \<and>
          frontier(inside(path_image c)) = path_image c \<and>
          frontier(outside(path_image c)) = path_image c"
proof -
  obtain inner outer
    where *: "inner \<noteq> {}" "open inner" "connected inner"
      "outer \<noteq> {}" "open outer" "connected outer"
      "bounded inner" "\<not> bounded outer" "inner \<inter> outer = {}"
      "inner \<union> outer = - path_image c"
      "frontier inner = path_image c"
      "frontier outer = path_image c"
    using Jordan_curve_R2 [OF assms] by blast
  then have inner: "inside(path_image c) = inner"
    by (metis dual_order.antisym inside_subset interior_eq interior_inside_frontier)
  have outer: "outside(path_image c) = outer"
    using \<open>inner \<union> outer = - path_image c\<close> \<open>inside (path_image c) = inner\<close>
      outside_inside \<open>inner \<inter> outer = {}\<close> by auto
  show ?thesis
    using * by (auto simp: inner outer)
qed

lemma jordan_points_inside_outside:
  fixes p :: "real \<Rightarrow> 'a"
  assumes "0 < e"
  assumes jordan: "simple_path p" "pathfinish p = pathstart p"
  assumes x: "x \<in> path_image p"
  obtains y z where "y \<in> inside (path_image p)" "y \<in> ball x e" 
    "z \<in> outside (path_image p)" "z \<in> ball x e"
proof -
  from Jordan_inside_outside_R2[OF jordan]
  have xi: "x \<in> frontier(inside (path_image p))" and
    xo: "x \<in> frontier(outside (path_image p))"
    using x by auto
  obtain y where y:"y \<in> inside (path_image p)" "y \<in> ball x e" using \<open>0 < e\<close> xi
    unfolding frontier_straddle
    by auto
  obtain z where z:"z \<in> outside (path_image p)" "z \<in> ball x e" using \<open>0 < e\<close> xo
    unfolding frontier_straddle
    by auto
  show ?thesis using y z that by blast
qed  

lemma eventually_at_open_segment:
  assumes "x \<in> {a<--<b}"
  shows "\<forall>\<^sub>F y in at x. (y-a) \<bullet> rot(a-b) = 0 \<longrightarrow> y \<in> {a <--< b}"
proof -
  from assms have "a \<noteq> b" by auto
  from assms have x: "(x - a) \<bullet> rot (b - a) = 0" "x \<bullet> (b - a) \<in> {a \<bullet> (b - a)<..<b \<bullet> (b - a)}"
    unfolding in_open_segment_iff_rot[OF \<open>a \<noteq> b\<close>]
    by auto
  then have "\<forall>\<^sub>F y in at x. y \<bullet> (b - a) \<in> {a \<bullet> (b - a)<..<b \<bullet> (b - a)}"
    by (intro topological_tendstoD) (auto intro!: tendsto_intros)
  then show ?thesis
    by eventually_elim (auto simp: in_open_segment_iff_rot[OF \<open>a \<noteq> b\<close>] nrm_reverse[of _ a b] algebra_simps dist_commute)
qed

lemma linepath_ball:
  assumes "x \<in> {a<--<b}"
  obtains e where "e > 0" "ball x e \<inter> {y. (y-a) \<bullet> rot(a-b) = 0} \<subseteq> {a <--< b}"
proof -
  from eventually_at_open_segment[OF assms] assms
  obtain e where "0 < e" "ball x e \<inter> {y. (y - a) \<bullet> rot (a - b) = 0} \<subseteq> {a<--<b}"
    by (force simp: eventually_at in_open_segment_iff_rot dist_commute)
  then show ?thesis ..
qed

lemma linepath_ball_inside_outside:
  fixes p :: "real \<Rightarrow> 'a"
  assumes jordan: "simple_path (p +++ linepath a b)" "pathfinish p = a" "pathstart p = b"
  assumes x: "x \<in> {a<--<b}"
  obtains e where "e > 0" "ball x e \<inter> path_image p = {}"
    "ball x e \<inter> {y. (y-a) \<bullet> rot (a-b) > 0} \<subseteq> inside (path_image (p +++ linepath a b)) \<and>
     ball x e \<inter> {y. (y-a) \<bullet> rot (a-b) < 0} \<subseteq> outside (path_image (p +++ linepath a b))
     \<or> 
     ball x e \<inter> {y. (y-a) \<bullet> rot (a-b) < 0} \<subseteq> inside (path_image (p +++ linepath a b)) \<and>
     ball x e \<inter> {y. (y-a) \<bullet> rot (a-b) > 0} \<subseteq> outside (path_image (p +++ linepath a b))"
proof -
  let ?lp = "p +++ linepath a b"
  have "a \<noteq> b" using x by auto
  have pp:"path p" using jordan path_join pathfinish_linepath simple_path_imp_path
    by fastforce
  have "path_image p \<inter> path_image (linepath a b) \<subseteq> {a,b}"
    using jordan simple_path_join_loop_eq
    by (metis (no_types, lifting) inf_sup_aci(1) insert_commute path_join_path_ends path_linepath simple_path_imp_path simple_path_joinE)
  then have "x \<notin> path_image p" using x unfolding path_image_linepath
    by (metis DiffE Int_iff le_iff_inf open_segment_def)
  then have "\<forall>\<^sub>F y in at x. y \<notin> path_image p"
    by (intro eventually_not_in_closed) (auto simp: closed_path_image \<open>path p\<close>)
  moreover 
  have "\<forall>\<^sub>F y in at x. (y - a) \<bullet> rot (a - b) = 0 \<longrightarrow> y \<in> {a<--<b}"
    by (rule eventually_at_open_segment[OF x])
  ultimately have "\<forall>\<^sub>F y in at x. y \<notin> path_image p \<and> ((y - a) \<bullet> rot (a - b) = 0 \<longrightarrow> y \<in> {a<--<b})"
    by eventually_elim auto
  then obtain e where e: "e > 0" "ball x e \<inter> path_image p = {}"
    "ball x e \<inter> {y. (y - a) \<bullet> rot (a - b) = 0} \<subseteq> {a<--<b}"
    using \<open>x \<notin> path_image p\<close> x in_open_segment_rotD[OF x]
    apply (auto simp: eventually_at subset_iff dist_commute dest!: )
    by (metis Int_iff all_not_in_conv dist_commute mem_ball) 
  have a1: "pathfinish ?lp = pathstart ?lp"
    by (auto simp add: jordan)
  have "x \<in> path_image ?lp"
    using jordan(1) open_closed_segment path_image_join path_join_path_ends simple_path_imp_path x by fastforce
  from jordan_points_inside_outside[OF e(1) jordan(1) a1 this]
  obtain y z where y: "y \<in> inside (path_image ?lp)" "y \<in> ball x e" 
    and z: "z \<in> outside (path_image ?lp)" "z \<in> ball x e" by blast
  have jordancurve:
    "inside (path_image ?lp) \<inter> outside(path_image ?lp) = {}"
    "frontier (inside (path_image ?lp)) = path_image ?lp"
    "frontier (outside (path_image ?lp)) = path_image ?lp"
    using Jordan_inside_outside_R2[OF jordan(1) a1] by auto
  define b1 where "b1 = ball x e \<inter> {y. (y-a) \<bullet> rot (a-b) > 0}"
  define b2 where "b2 = ball x e \<inter> {y. (y-a) \<bullet> rot (a-b) < 0}"
  define b3 where "b3 = ball x e \<inter> {y. (y-a) \<bullet> rot (a-b) = 0}"
  have "path_connected b1" unfolding b1_def
    apply (auto intro!: convex_imp_path_connected convex_Int simp add:inner_diff_left)
    using convex_halfspace_gt[of "a \<bullet> rot (a - b)" "rot(a-b)"] inner_commute
    by (metis (no_types, lifting) Collect_cong)
  have "path_connected b2" unfolding b2_def
    apply (auto intro!: convex_imp_path_connected convex_Int simp add:inner_diff_left)
    using convex_halfspace_lt[of "rot(a-b)" "a \<bullet> rot (a - b)"] inner_commute
    by (metis (no_types, lifting) Collect_cong)
  have "b1 \<inter> path_image(linepath a b) = {}" unfolding path_image_linepath b1_def
    using closed_segment_surface[OF \<open>a \<noteq> b\<close>] in_segment_inner_rot2 by auto 
  then have b1i:"b1 \<inter> path_image ?lp = {}"
    by (metis IntD2 b1_def disjoint_iff_not_equal e(2) inf_sup_aci(1) not_in_path_image_join)
  have "b2 \<inter> path_image(linepath a b) = {}" unfolding path_image_linepath b2_def
    using closed_segment_surface[OF \<open>a \<noteq> b\<close>] in_segment_inner_rot2 by auto 
  then have b2i:"b2 \<inter> path_image ?lp = {}"
    by (metis IntD2 b2_def disjoint_iff_not_equal e(2) inf_sup_aci(1) not_in_path_image_join)
  have bsplit: "ball x e = b1 \<union> b2 \<union> b3"
    unfolding b1_def b2_def b3_def
    by auto
  have "z \<notin> b3"
  proof clarsimp
    assume "z \<in> b3"
    then have "z \<in> {a<--<b}" unfolding b3_def using e by blast
    then have "z \<in> path_image(linepath a b)" by (auto simp add: open_segment_def)
    then have "z \<in> path_image ?lp"
      by (simp add: jordan(2) path_image_join)
    thus False using z
      using inside_Un_outside by fastforce
  qed
  then have z12: "z \<in> b1 \<or> z \<in> b2" using z bsplit by blast
  have "y \<notin> b3"
  proof clarsimp
    assume "y \<in> b3"
    then have "y \<in> {a<--<b}" unfolding b3_def using e by auto
    then have "y \<in> path_image(linepath a b)" by (auto simp add: open_segment_def)
    then have "y \<in> path_image ?lp"
      by (simp add: jordan(2) path_image_join)
    thus False using y
      using inside_Un_outside by fastforce
  qed
  then have "y \<in> b1 \<or> y \<in> b2" using y bsplit by blast
  moreover {
    assume "y \<in> b1"
    then have "b1 \<inter> inside (path_image ?lp) \<noteq> {}" using y by blast
    from path_connected_not_frontier_subset[OF \<open>path_connected b1\<close> this]
    have 1:"b1 \<subseteq> inside (path_image ?lp)" unfolding jordancurve using b1i
      by blast
    then have "z \<in> b2" using jordancurve(1) z(1) z12 by blast
    then have "b2 \<inter> outside (path_image ?lp) \<noteq> {}" using z by blast
    from path_connected_not_frontier_subset[OF \<open>path_connected b2\<close> this]
    have 2:"b2 \<subseteq> outside (path_image ?lp)" unfolding jordancurve using b2i
      by blast
    note conjI[OF 1 2]
  }
  moreover {
    assume "y \<in> b2"
    then have "b2 \<inter> inside (path_image ?lp) \<noteq> {}" using y by blast
    from path_connected_not_frontier_subset[OF \<open>path_connected b2\<close> this]
    have 1:"b2 \<subseteq> inside (path_image ?lp)" unfolding jordancurve using b2i
      by blast
    then have "z \<in> b1" using jordancurve(1) z(1) z12 by blast
    then have "b1 \<inter> outside (path_image ?lp) \<noteq> {}" using z by blast
    from path_connected_not_frontier_subset[OF \<open>path_connected b1\<close> this]
    have 2:"b1 \<subseteq> outside (path_image ?lp)" unfolding jordancurve using b1i
      by blast
    note conjI[OF 1 2]
  } 
  ultimately show ?thesis unfolding b1_def b2_def using that[OF e(1-2)] by auto
qed

subsection \<open>Transversal Segments\<close>\<comment> \<open>TODO: Transversal surface in Euclidean space?!\<close>

definition "transversal_segment a b \<longleftrightarrow>
  a \<noteq> b \<and> {a--b} \<subseteq> X \<and>
  (\<forall>z \<in> {a--b}. f z \<bullet> rot (a-b) \<noteq> 0)"

lemma transversal_segment_reverse:
  assumes "transversal_segment x y"
  shows "transversal_segment y x"
  unfolding transversal_segment_def
  by (metis (no_types, hide_lams) add.left_neutral add_uminus_conv_diff assms closed_segment_commute inner_diff_left inner_zero_left nrm_reverse transversal_segment_def) 

lemma transversal_segment_commute: "transversal_segment x y \<longleftrightarrow> transversal_segment y x"
  using transversal_segment_reverse by blast

lemma transversal_segment_neg:
  assumes "transversal_segment x y"
  assumes w: "w \<in> {x -- y}" and "f w \<bullet> rot (x-y) < 0"
  shows "\<forall>z \<in> {x--y}. f(z) \<bullet> rot (x-y) < 0"
proof (rule ccontr)
  assume " \<not> (\<forall>z\<in>{x--y}. f z \<bullet> rot (x-y) < 0)"
  then obtain z where z: "z \<in> {x--y}" "f z \<bullet> rot (x-y) \<ge> 0" by auto
  define ff where "ff = (\<lambda>s. f (w + s *\<^sub>R (z - w)) \<bullet> rot (x-y))"
  have f0:"ff 0 \<le> 0" unfolding ff_def using assms(3)
    by simp 
  have fu:"ff 1 \<ge> 0"
    by (auto simp: ff_def z)
  from assms(2) obtain u where u: "0 \<le> u" "u \<le> 1" "w = (1 - u) *\<^sub>R x + u *\<^sub>R y"
    unfolding in_segment by blast
  have "{x--y} \<subseteq> X" using assms(1) unfolding transversal_segment_def by blast
  then have "continuous_on {0..1} ff" unfolding ff_def 
    using assms(2)
    by (auto intro!:continuous_intros closed_subsegmentI z elim!: set_mp)
  from IVT'[of ff, OF f0 fu zero_le_one this]
  obtain s where s: "s \<ge> 0" "s \<le> 1" "ff s = 0" by blast
  have "w + s *\<^sub>R (z - w) \<in> {x -- y}"
    by (auto intro!: closed_subsegmentI z s w)
  with \<open>ff s = 0\<close> show False
    using s assms(1) unfolding transversal_segment_def ff_def by blast
qed

lemmas transversal_segment_sign_less = transversal_segment_neg[OF _ ends_in_segment(1)]

lemma transversal_segment_pos:
  assumes "transversal_segment x y"
  assumes w: "w \<in> {x -- y}" "f w \<bullet> rot (x-y) > 0"
  shows "\<forall>z \<in> {x--y}. f(z) \<bullet> rot (x-y) > 0"
  using transversal_segment_neg[OF transversal_segment_reverse[OF assms(1)], of w] w
  by (auto simp: rot_diff_commute[of x y] closed_segment_commute)

lemma transversal_segment_posD:
  assumes "transversal_segment x y"
    and pos: "z \<in> {x -- y}" "f z \<bullet> rot (x - y) > 0"
  shows "x \<noteq> y" "{x--y} \<subseteq> X" "\<And>z. z \<in> {x--y} \<Longrightarrow> f z \<bullet> rot (x-y) > 0"
  using assms(1) transversal_segment_pos[OF assms]
  by (auto simp: transversal_segment_def)

lemma transversal_segment_negD:
  assumes "transversal_segment x y"
    and pos: "z \<in> {x -- y}" "f z \<bullet> rot (x - y) < 0"
  shows "x \<noteq> y" "{x--y} \<subseteq> X" "\<And>z. z \<in> {x--y} \<Longrightarrow> f z \<bullet> rot (x-y) < 0"
  using assms(1) transversal_segment_neg[OF assms]
  by (auto simp: transversal_segment_def)

lemma transversal_segmentE:
  assumes "transversal_segment x y"
  obtains "x \<noteq> y" "{x -- y} \<subseteq> X" "\<And>z. z \<in> {x--y} \<Longrightarrow> f z \<bullet> rot (x - y) > 0"
  |  "x \<noteq> y" "{x -- y} \<subseteq> X" "\<And>z. z \<in> {x--y} \<Longrightarrow> f z \<bullet> rot (y - x) > 0"
proof (cases "f x \<bullet> rot (x - y) < 0")
  case True
  from transversal_segment_negD[OF assms ends_in_segment(1) True]
  have "x \<noteq> y" "{x -- y} \<subseteq> X" "\<And>z. z \<in> {x--y} \<Longrightarrow> f z \<bullet> rot (y - x) > 0"
    by (auto simp: rot_diff_commute[of x y])
  then show ?thesis ..
next
  case False
  then have "f x \<bullet> rot (x - y) > 0" using assms
    by (auto simp: transversal_segment_def algebra_split_simps not_less order.order_iff_strict)
  from transversal_segment_posD[OF assms ends_in_segment(1) this]
  show ?thesis ..
qed

lemma dist_add_vec:
  shows "dist (x + s *\<^sub>R v) x = abs s * norm v"
  by (simp add: dist_cancel_add1)

lemma transversal_segment_exists:
  assumes "x \<in> X" "f x \<noteq> 0"
  obtains a b where "x \<in> {a<--<b}"
    "transversal_segment a b"
proof -
  (* Line through x perpendicular to f x *)
  define l where "l = (\<lambda>s::real. x + (s/norm(f x)) *\<^sub>R rot (f x))"
  have "norm (f x) > 0" using assms(2) using zero_less_norm_iff by blast 
  then have distl: "\<forall>s. dist (l s) x = abs s" unfolding l_def dist_add_vec
    by (auto simp add: norm_rot)
  obtain d where d:"d > 0" "cball x d \<subseteq> X"
    by (meson UNIV_I assms(1) local.local_unique_solution)
  then have lb: "l`{-d..d} \<subseteq> cball x d" using distl by (simp add: abs_le_iff dist_commute image_subset_iff)
  from fcontx[OF assms(1)] have "continuous (at x) f" .
  then have c:"continuous (at 0) ((\<lambda>y. (f y \<bullet> f x)) \<circ> l)" unfolding l_def
    by (auto intro!:continuous_intros simp add: assms(2))
  have "((\<lambda>y. f y \<bullet> f x) \<circ> l) 0 > 0" using assms(2) unfolding l_def o_def by auto
  from continuous_at_imp_cball[OF c this]
  obtain r where r:"r > 0" " \<forall>z\<in>cball 0 r. 0 < ((\<lambda>y. f y \<bullet> f x) \<circ> l) z" by blast
  then have rc:"\<forall>z \<in> l`{-r..r}. 0 < f z \<bullet> f x" using real_norm_def by auto 
  define dr where "dr = min r d"
  have t1:"l (-dr) \<noteq> l dr" unfolding l_def dr_def
    by (smt \<open>0 < d\<close> \<open>0 < norm (f x)\<close> \<open>0 < r\<close> add_left_imp_eq divide_cancel_right norm_rot norm_zero scale_cancel_right)
  have "x = midpoint (l (-dr)) (l dr)" unfolding midpoint_def l_def by auto
  then have xin:"x \<in> {l (-dr)<--<(l dr)}" using t1 by auto
      (* TODO: actually this should be equality, but l is affine ...
     also the existing stuff about -- is a little too specific *)
  have lsub:"{l (-dr)--l dr} \<subseteq> l`{-dr..dr}"
  proof safe
    fix z
    assume "z \<in> {l (- dr)--l dr}"
    then obtain u where u: "0 \<le> u" "u \<le> 1" "z = (1 - u) *\<^sub>R (l (-dr)) + u *\<^sub>R (l dr)"
      unfolding in_segment by blast
    then have "z = x - (1-u) *\<^sub>R (dr/norm(f x)) *\<^sub>R rot (f x) + u *\<^sub>R  (dr/norm(f x)) *\<^sub>R rot (f x) "
      unfolding l_def
      by (simp add: l_def scaleR_add_right scale_right_diff_distrib u(3))
    also have "... = x - (1 - 2 * u) *\<^sub>R (dr/norm(f x)) *\<^sub>R rot (f x)"
      by (auto simp add: algebra_simps divide_simps simp flip: scaleR_add_left)
    also have "... =  x + (((2 * u - 1) * dr)/norm(f x)) *\<^sub>R rot (f x)"
      by (smt add_uminus_conv_diff scaleR_scaleR scale_minus_left times_divide_eq_right)
    finally have zeq: "z = l ((2*u-1)*dr)" unfolding l_def .
    have ub: " 2* u - 1 \<le> 1 \<and> -1 \<le>  2* u - 1 " using u by linarith
    thus "z \<in> l ` {- dr..dr}" using zeq
      by (smt atLeastAtMost_iff d(1) dr_def image_eqI mult.commute mult_left_le mult_minus_left r(1)) 
  qed
  have t2: "{l (- dr)--l dr} \<subseteq> X" using lsub
    by (smt atLeastAtMost_iff d(2) dist_commute distl dr_def image_subset_iff mem_cball order_trans)
  have "l (- dr) - l dr = -2 *\<^sub>R (dr/norm(f x)) *\<^sub>R rot (f x)" unfolding l_def
    by (simp add: algebra_simps flip: scaleR_add_left)
  then have req: "rot (l (- dr) - l dr) = (2 * dr/norm(f x)) *\<^sub>R f x"
    by auto (metis add.inverse_inverse rot_rot rot_scaleR)
  have "l`{-dr..dr} \<subseteq> l ` {-r ..r}"
    by (simp add: dr_def image_mono)
  then have "{l (- dr)--l dr} \<subseteq> l ` {-r .. r}" using lsub by auto
  then have "\<forall>z \<in> {l (- dr)--l dr}. 0 < f z \<bullet> f x" using rc by blast
  moreover have "(dr / norm (f x)) > 0"
    using \<open>0 < norm (f x)\<close> d(1) dr_def r(1) by auto 
  ultimately have t3: "\<forall>z \<in> {l (- dr)--l dr}. f z \<bullet> rot (l (- dr)- l dr) > 0" unfolding req
    by (smt divide_divide_eq_right inner_scaleR_right mult_2 norm_not_less_zero scaleR_2 times_divide_eq_left times_divide_eq_right zero_less_divide_iff)
  have "transversal_segment (l (-dr)) (l dr)" using t1 t2 t3 unfolding transversal_segment_def by auto
  thus ?thesis using xin
    using that by auto 
qed

text \<open>Perko Section 3.7 Lemma 2 part 1.\<close> 
lemma flow_transversal_segment_finite_intersections:
  assumes "transversal_segment a b"
  assumes "t \<le> t'" "{t .. t'} \<subseteq> existence_ivl0 x"
  shows "finite {s\<in>{t..t'}. flow0 x s \<in> {a--b}}"
proof -
  from assms have "a \<noteq> b" by (simp add: transversal_segment_def)
  show ?thesis
    unfolding closed_segment_surface[OF \<open>a \<noteq> b\<close>]
    apply (rule flow_transversal_surface_finite_intersections[where Ds="\<lambda>_. blinfun_inner_left (rot (b - a))"])
    by
      (use assms in \<open>auto intro!: closed_Collect_conj closed_halfspace_component_ge closed_halfspace_component_le
        derivative_eq_intros
        simp: transversal_segment_def nrm_reverse[where x=a] in_closed_segment_iff_rot\<close>)
qed

lemma transversal_bound_posE:
  assumes transversal: "transversal_segment a b"
  assumes direction: "z \<in> {a -- b}" "f z \<bullet> (rot (a - b)) > 0"
  obtains d B where "d > 0" "0 < B"
    "\<And>x y. x \<in> {a -- b} \<Longrightarrow> dist x y \<le> d \<Longrightarrow> f y \<bullet> (rot (a - b)) \<ge> B"
proof -
  let ?a = "(\<lambda>y. (f y) \<bullet> (rot (a - b)))"
  from transversal_segment_posD[OF transversal direction]
  have seg: "a \<noteq> b" "{a--b} \<subseteq> X" "z \<in> {a--b} \<Longrightarrow> 0 < f z \<bullet> rot (a - b)" for z
    by auto
  {
    fix x
    assume "x \<in> {a--b}"
    then have "x \<in> X" "f x \<noteq> 0" "a \<noteq> b" using transversal by (auto simp: transversal_segment_def)
    then have "?a \<midarrow>x\<rightarrow> ?a x"
      by (auto intro!: tendsto_eq_intros)
    moreover have "?a x > 0"
      using seg \<open>x \<in> {a -- b}\<close> \<open>f x \<noteq> 0\<close>
      by (auto simp: simp del: divide_const_simps
          intro!: divide_pos_pos mult_pos_pos)
    ultimately have "\<forall>\<^sub>F x in at x. ?a x > 0"
      by (rule order_tendstoD)
    moreover have "\<forall>\<^sub>F x in at x. x \<in> X"
      by (rule topological_tendstoD[OF tendsto_ident_at open_dom \<open>x \<in> X\<close>])
    moreover have "\<forall>\<^sub>F x in at x. f x \<noteq> 0"
      by (rule tendsto_imp_eventually_ne tendsto_intros \<open>x \<in> X\<close> \<open>f x \<noteq> 0\<close>)+
    ultimately have "\<forall>\<^sub>F x in at x. ?a x>0 \<and> x \<in> X \<and> f x \<noteq> 0" by eventually_elim auto
    then obtain d where d: "0 < d" "\<And>y. y \<in> cball x d \<Longrightarrow> ?a y > 0 \<and> y \<in> X \<and> f y \<noteq> 0"
      using \<open>?a x > 0\<close> \<open>x \<in> X\<close>
      by (force simp: eventually_at_le dist_commute)

    have "continuous_on (cball x d) ?a"
      using d \<open>a \<noteq> b\<close>
      by (auto intro!: continuous_intros)
    from compact_continuous_image[OF this compact_cball]
    have "compact (?a ` cball x d)" .
    from compact_attains_inf[OF this] obtain s where "s \<in> cball x d" "\<forall>x\<in>cball x d. ?a x \<ge> ?a s"
      using \<open>d > 0\<close>
      by auto
    then have "\<exists>d>0. \<exists>b>0. \<forall>x \<in> cball x d. ?a x \<ge> b"
      using d
      by (force simp: intro: exI[where x="?a s"])
  } then obtain dx Bx where dB:
    "\<And>x y. x \<in> {a -- b} \<Longrightarrow> y\<in>cball x (dx x) \<Longrightarrow> ?a y \<ge> Bx x"
    "\<And>x. x \<in> {a -- b} \<Longrightarrow> Bx x > 0"
    "\<And>x. x \<in> {a -- b} \<Longrightarrow> dx x > 0"
    by metis
  define d' where "d' = (\<lambda>x. dx x / 2)"
  have d':
    "\<And>x. x \<in> {a -- b} \<Longrightarrow> \<forall>y\<in>cball x (d' x). ?a y \<ge> Bx x"
    "\<And>x. x \<in> {a -- b} \<Longrightarrow> d' x > 0"
    using dB(1,3) by (force simp: d'_def)+
  have d'B: "\<And>x. x \<in> {a -- b} \<Longrightarrow> \<forall>y\<in>cball x (d' x). ?a y \<ge> Bx x"
    using d' by auto
  have "{a--b} \<subseteq> \<Union>((\<lambda>x. ball x (d' x)) ` {a -- b})"
    using d'(2) by auto
  from compactE_image[OF compact_segment _ this]
  obtain X where X: "X \<subseteq> {a--b}"
    and [simp]: "finite X"
    and cover: "{a--b} \<subseteq> (\<Union>x\<in>X. ball x (d' x))"
    by auto
  have [simp]: "X \<noteq> {}" using X cover by auto
  define d where "d = Min (d' ` X)"
  define B where "B = Min (Bx ` X)"
  have "d > 0"
    using X d'
    by (auto simp: d_def d'_def)
  moreover have "B > 0"
    using X dB
    by (auto simp: B_def simp del: divide_const_simps)
  moreover have "B \<le> ?a y" if "x \<in> {a -- b}" "dist x y \<le> d" for x y
  proof -
    from \<open>x \<in> {a -- b}\<close> obtain xc where xc: "xc \<in> X" "x \<in> ball xc (d' xc)"
      using cover by auto
    have "?a y \<ge> Bx xc"
    proof (rule dB)
      show "xc \<in> {a -- b}" using xc \<open>X \<subseteq> _\<close> by auto
      have "dist xc y \<le> dist xc x + dist x y" by norm
      also have "dist xc x \<le> d' xc" using xc by auto
      also note \<open>dist x y \<le> d\<close>
      also have "d \<le> d' xc"
        using xc
        by (auto simp: d_def)
      also have "d' xc + d' xc = dx xc" by (simp add: d'_def)
      finally show "y \<in> cball xc (dx xc)" by simp
    qed
    also have "B \<le> Bx xc"
      using xc
      unfolding B_def
      by (auto simp: B_def)
    finally (xtrans) show ?thesis .
  qed
  ultimately show ?thesis ..
qed

lemma transversal_bound_negE:
  assumes transversal: "transversal_segment a b"
  assumes direction: "z \<in> {a -- b}" "f z \<bullet> (rot (a - b)) < 0"
  obtains d B where "d > 0" "0 < B"
    "\<And>x y. x \<in> {a -- b} \<Longrightarrow> dist x y \<le> d \<Longrightarrow> f y \<bullet> (rot (b - a)) \<ge> B"
proof -
  from direction have "z \<in> {b -- a}" "f z \<bullet> (rot (b - a)) > 0"
    by (auto simp: closed_segment_commute rot_diff_commute[of b a])
  from transversal_bound_posE[OF transversal_segment_reverse[OF transversal] this]
  obtain d B where "d > 0" "0 < B"
    "\<And>x y. x \<in> {a -- b} \<Longrightarrow> dist x y \<le> d \<Longrightarrow> f y \<bullet> (rot (b - a)) \<ge> B"
    by (auto simp: closed_segment_commute)
  then show ?thesis ..
qed

lemma leaves_transversal_segmentE:
  assumes transversal: "transversal_segment a b"
  obtains T n where "T > 0" "n = a - b \<or> n = b - a"
    "\<And>x. x \<in> {a -- b} \<Longrightarrow> {-T..T} \<subseteq> existence_ivl0 x"
    "\<And>x s. x \<in> {a -- b} \<Longrightarrow> 0 < s \<Longrightarrow> s \<le> T \<Longrightarrow>
    (flow0 x s - x) \<bullet> rot n > 0"
    "\<And>x s. x \<in> {a -- b} \<Longrightarrow> -T \<le> s \<Longrightarrow> s < 0 \<Longrightarrow>
    (flow0 x s - x) \<bullet> rot n < 0"
proof -
  from transversal_segmentE[OF assms(1)] obtain n
    where n: "n = (a - b) \<or> n = (b - a)"
      and seg: "a \<noteq> b" "{a -- b} \<subseteq> X" "\<And>z. z \<in> {a--b} \<Longrightarrow> f z \<bullet> rot n > 0"
    by metis
  from open_existence_ivl_on_compact[OF \<open>{a -- b} \<subseteq> X\<close>]
  obtain t where "0 < t" and t: "x \<in> {a--b} \<Longrightarrow> {- t..t} \<subseteq> existence_ivl0 x" for x
    by auto
  from n obtain d B where B: "0 < d" "0 < B" "(\<And>x y. x \<in> {a--b} \<Longrightarrow> dist x y \<le> d \<Longrightarrow> B \<le> f y \<bullet> rot n)"
  proof
    assume n_def: "n = a - b"
    with seg have pos:  "0 < f a \<bullet> rot (a - b)"
      by auto
    from transversal_bound_posE[OF transversal ends_in_segment(1) pos, folded n_def]
    show ?thesis using that by blast
  next
    assume n_def: "n = b - a"
    with seg have pos:  "0 > f a \<bullet> rot (a - b)"
      by (auto simp: rot_diff_commute[of a b])
    from transversal_bound_negE[OF transversal ends_in_segment(1) this, folded n_def]
    show ?thesis using that by blast
  qed
  define S where "S = \<Union>((\<lambda>x. ball x d) ` {a -- b})"
  have S: "x \<in> S \<Longrightarrow> B \<le> f x \<bullet> rot n" for x
    by (auto simp: S_def intro!: B)
  have "open S" by (auto simp: S_def)
  have "{a -- b} \<subseteq> S"
    by (auto simp: S_def \<open>0 < d\<close>)
  have "\<forall>\<^sub>F (t, x) in at (0, x). flow0 x t \<in> S" if "x \<in> {a -- b}" for x
    unfolding split_beta'
    apply (rule topological_tendstoD tendsto_intros)+
    using set_mp[OF \<open>{a -- b} \<subseteq> X\<close> that] \<open>0 < d\<close> that \<open>open S\<close> \<open>{a -- b} \<subseteq> S\<close>
    by (force simp: )+
  then obtain d' where d':
    "\<And>x. x \<in> {a--b} \<Longrightarrow> d' x > 0"
    "\<And>x y s. x \<in> {a--b} \<Longrightarrow> (s = 0 \<longrightarrow> y \<noteq> x) \<Longrightarrow> dist (s, y) (0, x) < d' x \<Longrightarrow> flow0 y s \<in> S"
    by (auto simp: eventually_at) metis
  define d2 where "d2 x = d' x / 2" for x
  have d2: "\<And>x. x \<in> {a--b} \<Longrightarrow> d2 x > 0" using d' by (auto simp: d2_def)
  have C: "{a--b} \<subseteq> \<Union>((\<lambda>x. ball x (d2 x)) ` {a -- b})"
    using d2 by auto
  from compactE_image[OF compact_segment _ C]
  obtain C' where "C' \<subseteq> {a--b}" and [simp]: "finite C'"
    and C'_cover: "{a--b} \<subseteq> (\<Union>c\<in>C'. ball c (d2 c))" by auto

  define T where "T = Min (insert t (d2 ` C'))"

  have "T > 0"
    using \<open>0 < t\<close> d2 \<open>C' \<subseteq> _\<close> 
    by (auto simp: T_def)
  moreover
  note n
  moreover
  have T_ex: "{-T..T} \<subseteq> existence_ivl0 x" if "x \<in> {a--b}" for x
    by (rule order_trans[OF _ t[OF that]]) (auto simp: T_def)
  moreover
  have B_le: "B \<le> f (flow0 x \<xi>) \<bullet> rot n"
    if "x \<in> {a -- b}"
      and c': "c' \<in> C'" "x \<in> ball c' (d2 c')"
      and "\<xi> \<noteq> 0" and \<xi>_le: "\<bar>\<xi>\<bar> < d2 c'"
    for x c' \<xi>
  proof -
    have "c' \<in> {a -- b}" using c' \<open>C' \<subseteq> _\<close> by auto
    moreover have "\<xi> = 0 \<longrightarrow> x \<noteq> c'" using \<open>\<xi> \<noteq> 0\<close> by simp
    moreover have "dist (\<xi>, x) (0, c') < d' c'"
    proof -
      have "dist (\<xi>, x) (0, c') \<le> dist (\<xi>, x) (\<xi>, c') + dist (\<xi>, c') (0, c')"
        by norm
      also have "dist (\<xi>, x) (\<xi>, c') < d2 c'"
        using c'
        by (simp add: dist_prod_def dist_commute)
      also
      have "T \<le> d2 c'" using c'
        by (auto simp: T_def)
      then have "dist (\<xi>, c') (0, c') < d2 c'"
        using \<xi>_le
        by (simp add: dist_prod_def)
      also have "d2 c' + d2 c' = d' c'" by (simp add: d2_def)
      finally show ?thesis by simp
    qed
    ultimately have "flow0 x \<xi> \<in> S"
      by (rule d')
    then show ?thesis
      by (rule S)
  qed
  let ?g = "(\<lambda>x t. (flow0 x t - x) \<bullet> rot n)"
  have cont: "continuous_on {-T .. T} (?g x)"
    if "x \<in> {a--b}" for x
    using T_ex that
    by (force intro!: continuous_intros)
  have deriv: "-T \<le> s' \<Longrightarrow> s' \<le> T \<Longrightarrow> ((?g x) has_derivative
      (\<lambda>t. t * (f (flow0 x s') \<bullet> rot n))) (at s')"
    if "x \<in> {a--b}" for x s'
    using T_ex that
    by (force intro!: derivative_eq_intros simp: flowderiv_def blinfun.bilinear_simps)

  have "(flow0 x s - x) \<bullet> rot n > 0" if "x \<in> {a -- b}" "0 < s" "s \<le> T" for x s
  proof (rule ccontr, unfold not_less)
    have [simp]: "x \<in> X" using that \<open>{a -- b} \<subseteq> X\<close> by auto
    assume H: "(flow0 x s - x) \<bullet> rot n \<le> 0"
    have cont: "continuous_on {0 .. s} (?g x)"
      using cont by (rule continuous_on_subset) (use that in auto)
    from mvt[OF \<open>0 < s\<close> cont deriv] that
    obtain \<xi> where \<xi>: "0 < \<xi>" "\<xi> < s" "(flow0 x s - x) \<bullet> rot n = s * (f (flow0 x \<xi>) \<bullet> rot n)"
      by (auto intro: continuous_on_subset)
    note \<open>0 < B\<close>
    also
    from C'_cover that obtain c' where c': "c' \<in> C'" "x \<in> ball c' (d2 c')" by auto
    have "B \<le> f (flow0 x \<xi>) \<bullet> rot n"
    proof (rule B_le[OF that(1) c'])
      show "\<xi> \<noteq> 0" using \<open>0 < \<xi>\<close> by simp
      have "T \<le> d2 c'" using c'
        by (auto simp: T_def)
      then show "\<bar>\<xi>\<bar> < d2 c'"
        using \<open>0 < \<xi>\<close> \<open>\<xi> < s\<close> \<open>s \<le> T\<close>
        by (simp add: dist_prod_def)
    qed
    also from \<xi> H have "\<dots> \<le> 0"
      by (auto simp add: algebra_split_simps not_less split: if_splits)
    finally show False by simp
  qed
  moreover
  have "(flow0 x s - x) \<bullet> rot n < 0" if "x \<in> {a -- b}" "-T \<le> s" "s < 0" for x s
  proof (rule ccontr, unfold not_less)
    have [simp]: "x \<in> X" using that \<open>{a -- b} \<subseteq> X\<close> by auto
    assume H: "(flow0 x s - x) \<bullet> rot n \<ge> 0"
    have cont: "continuous_on {s .. 0} (?g x)"
      using cont by (rule continuous_on_subset) (use that in auto)
    from mvt[OF \<open>s < 0\<close> cont deriv] that
    obtain \<xi> where \<xi>: "s < \<xi>" "\<xi> < 0" "(flow0 x s - x) \<bullet> rot n = s * (f (flow0 x \<xi>) \<bullet> rot n)"
      by auto
    note \<open>0 < B\<close>
    also
    from C'_cover that obtain c' where c': "c' \<in> C'" "x \<in> ball c' (d2 c')" by auto
    have "B \<le> (f (flow0 x \<xi>) \<bullet> rot n)"
    proof (rule B_le[OF that(1) c'])
      show "\<xi> \<noteq> 0" using \<open>0 > \<xi>\<close> by simp
      have "T \<le> d2 c'" using c'
        by (auto simp: T_def)
      then show "\<bar>\<xi>\<bar> < d2 c'"
        using \<open>0 > \<xi>\<close> \<open>\<xi> > s\<close> \<open>s \<ge> - T\<close>
        by (simp add: dist_prod_def)
    qed
    also from \<xi> H have "\<dots> \<le> 0"
      by (simp add: algebra_split_simps)
    finally show False by simp
  qed
  ultimately show ?thesis ..
qed


lemma inner_rot_pos_move_base: "(x - a) \<bullet> rot (a - b) > 0"
  if "(x - y) \<bullet> rot (a - b) > 0" "y \<in> {a -- b}"
  by (smt in_segment_inner_rot inner_diff_left inner_minus_right minus_diff_eq rot_rot that)

lemma inner_rot_neg_move_base: "(x - a) \<bullet> rot (a - b) < 0"
  if "(x - y) \<bullet> rot (a - b) < 0" "y \<in> {a -- b}"
  by (smt in_segment_inner_rot inner_diff_left inner_minus_right minus_diff_eq rot_rot that)

lemma inner_pos_move_base: "(x - a) \<bullet> n > 0"
  if "(a - b) \<bullet> n = 0" "(x - y) \<bullet> n > 0" "y \<in> {a -- b}"
proof -
  from that(3) obtain u where y_def: "y = (1 - u) *\<^sub>R a + u *\<^sub>R b" and u: "0 \<le> u" "u \<le> 1"
    by (auto simp: in_segment)
  have "(x - a) \<bullet> n = (x - y) \<bullet> n - u * ((a - b) \<bullet> n)"
    by (simp add: algebra_simps y_def)
  also have "\<dots> = (x - y) \<bullet> n"
    by (simp add: that)
  also note \<open>\<dots> > 0\<close>
  finally show ?thesis .
qed

lemma inner_neg_move_base: "(x - a) \<bullet> n < 0"
  if "(a - b) \<bullet> n = 0" "(x - y) \<bullet> n < 0" "y \<in> {a -- b}"
proof -
  from that(3) obtain u where y_def: "y = (1 - u) *\<^sub>R a + u *\<^sub>R b" and u: "0 \<le> u" "u \<le> 1"
    by (auto simp: in_segment)
  have "(x - a) \<bullet> n = (x - y) \<bullet> n - u * ((a - b) \<bullet> n)"
    by (simp add: algebra_simps y_def)
  also have "\<dots> = (x - y) \<bullet> n"
    by (simp add: that)
  also note \<open>\<dots> < 0\<close>
  finally show ?thesis .
qed

lemma rot_same_dir:
  assumes "x1 \<in> {a<--<b}"
  assumes "x2 \<in> {x1<--<b}"
  shows "(y \<bullet> rot (a-b) > 0) = (y \<bullet> rot(x1-x2) > 0)"  "(y \<bullet> rot (a-b) < 0) = (y \<bullet> rot(x1-x2) < 0)"
  using oriented_subsegment_scale[OF assms]
   apply (smt inner_scaleR_right nrm_reverse rot_scaleR zero_less_mult_iff)
  by (smt \<open>\<And>thesis. (\<And>e. \<lbrakk>0 < e; b - a = e *\<^sub>R (x2 - x1)\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> inner_minus_right inner_scaleR_right rot_diff_commute rot_scaleR zero_less_mult_iff)


subsection \<open>Monotone Step Lemma\<close>

lemma flow0_transversal_segment_monotone_step:
  assumes "transversal_segment a b"
  assumes "t1 \<le> t2" "{t1..t2} \<subseteq> existence_ivl0 x"
  assumes x1: "flow0 x t1 \<in> {a<--<b}"
  assumes x2: "flow0 x t2 \<in> {flow0 x t1<--<b}"
  assumes "\<And>t. t \<in> {t1<..<t2} \<Longrightarrow> flow0 x t \<notin> {a<--<b}"
  assumes "t > t2" "t \<in> existence_ivl0 x"
  shows "flow0 x t \<notin> {a<--<flow0 x t2}"
proof -
  note exist = \<open>{t1..t2} \<subseteq> existence_ivl0 x\<close>
  note t1t2 = \<open>\<And>t. t \<in> {t1<..<t2} \<Longrightarrow> flow0 x t \<notin> {a<--<b}\<close>
    (* Basic properties of the segment *)
  have x1neqx2: "flow0 x t1 \<noteq> flow0 x t2"
    using open_segment_def x2 by force 
  then have t1neqt2: "t1 \<noteq> t2" by auto

  have [simp]: "a \<noteq> b" and \<open>{a -- b} \<subseteq> X\<close> using \<open>transversal_segment a b\<close>
    by (auto simp: transversal_segment_def)

  from x1 obtain i1 where i1: "flow0 x t1 = line a b i1" "0 < i1" "i1 < 1"
    by (auto simp: in_open_segment_iff_line)
  from x2 obtain i2 where i2: "flow0 x t2 = line a b i2" "0 < i1" "i1 < i2"
    by (auto simp: i1 line_open_segment_iff)


  have "{a <--< flow0 x t1} \<subseteq> {a<--<b}"
    by (simp add: open_closed_segment subset_open_segment x1) 
  have t12sub: "{flow0 x t1--flow0 x t2} \<subseteq> {a<--<b}"
    by (metis ends_in_segment(2) open_closed_segment subset_co_segment subset_eq subset_open_segment x1 x2)
  have subr: "{flow0 x t1<--<flow0 x t2} \<subseteq> {flow0 x t1 <--<b}"
    by (simp add: open_closed_segment subset_open_segment x2)
  have "flow0 x t1 \<in> {a <--<flow0 x t2}" using x1 x2
    by (rule open_segment_subsegment)
  then have subl: "{flow0 x t1<--<flow0 x t2} \<subseteq> {a <--< flow0 x t2}" using x1 x2
    by (simp add: open_closed_segment subset_open_segment x2)
  then have subl2: "{flow0 x t1--<flow0 x t2} \<subseteq> {a <--< flow0 x t2}" using x1 x2
    by (smt DiffE DiffI \<open>flow0 x t1 \<in> {a<--<flow0 x t2}\<close> half_open_segment_def insert_iff open_segment_def subset_eq)

  have sub1b: "{flow0 x t1--b} \<subseteq> {a--b}"
    by (simp add: open_closed_segment subset_closed_segment x1)
  have suba2: "{a--flow0 x t2} \<subseteq> {a -- b}"
    using open_closed_segment subset_closed_segment t12sub by blast
  then have suba2o: "{a<--<flow0 x t2} \<subseteq> {a -- b}"
    using open_closed_segment subset_closed_segment t12sub by blast
  have x2_notmem: "flow0 x t2 \<notin> {a--flow0 x t1}"
    using i1 i2
    by (auto simp: closed_segment_line_iff)
  have suba12: "{a--flow0 x t1} \<subseteq> {a--flow0 x t2}"
    by (simp add: \<open>flow0 x t1 \<in> {a<--<flow0 x t2}\<close> open_closed_segment subset_closed_segment)
  then have suba12_open: "{a<--<flow0 x t1} \<subseteq> {a<--<flow0 x t2}"
    using x2_notmem
    by (auto simp: open_segment_def)
  have "flow0 x t2 \<in> {a--b}"
    using suba2 by auto

  have intereq: "\<And>t. t1 \<le> t \<Longrightarrow> t \<le> t2 \<Longrightarrow> flow0 x t \<in> {a<--<b} \<Longrightarrow>  t = t1 \<or> t = t2"
  proof (rule ccontr)
    fix t
    assume t: "t1 \<le> t" "t \<le> t2" "flow0 x t \<in> {a<--<b}" "\<not>(t= t1 \<or> t = t2)"
    then have "t \<in> {t1<..<t2}" by auto
    then have "flow0 x t \<notin> {a<--<b}" using t1t2 by blast
    thus False using t by auto
  qed
  then have intereqt12: "\<And>t. t1 \<le> t \<Longrightarrow> t \<le> t2 \<Longrightarrow> flow0 x t \<in> {flow0 x t1--flow0 x t2} \<Longrightarrow>  t = t1 \<or> t = t2"
    using t12sub by blast

(* The Jordan curve *)
  define J1 where "J1 = flow_to_path x t1 t2"
  define J2 where "J2 = linepath (flow0 x t2) (flow0 x t1)" 
  define J where "J = J1 +++ J2"
    (* Proof that J is a Jordan curve *)
  have "pathfinish J = pathstart J" unfolding J_def J1_def J2_def
    by (auto simp add: pathstart_compose pathfinish_compose)
  have piJ: "path_image J = path_image J1 \<union> path_image J2"
    unfolding J_def J1_def J2_def
    apply (rule path_image_join)
    by auto
  have "flow0 x t1 \<in> flow0 x ` {t1..t2} \<and> flow0 x t2 \<in> flow0 x ` {t1..t2}"
    using atLeastAtMost_iff \<open>t1 \<le> t2\<close> by blast 
  then have piD: "path_image J = path_image J1 \<union> {flow0 x t1 <--<flow0 x t2}"
    unfolding piJ J1_def J2_def path_image_flow_to_path[OF \<open>t1 \<le> t2\<close>]
      path_image_linepath open_segment_def
    by (smt Diff_idemp Diff_insert2 Un_Diff_cancel closed_segment_commute mk_disjoint_insert)
  have "\<forall>s\<in>{t1<..<t2}. flow0 x s \<noteq> flow0 x t1"
    using x1 t1t2 by fastforce
  from flow_to_path_arc[OF \<open>t1 \<le> t2\<close> exist this x1neqx2]
  have "arc J1" using J1_def assms flow_to_path_arc by auto
  then have "simple_path J" unfolding J_def
    using \<open>arc J1\<close> J1_def J2_def assms x1neqx2 t1neqt2 apply (auto intro!:simple_path_join_loop)
    using intereqt12 closed_segment_commute by blast

  from Jordan_inside_outside_R2[OF this \<open>pathfinish J = pathstart J\<close>]
  obtain inner outer where inner_def: "inner = inside (path_image J)"
    and outer_def: "outer = outside (path_image J)"
    and io:
    "inner \<noteq> {}" "open inner" "connected inner"
    "outer \<noteq> {}" "open outer" "connected outer"
    "bounded inner" "\<not> bounded outer" "inner \<inter> outer = {}"
    "inner \<union> outer = - path_image J"
    "frontier inner = path_image J"
    "frontier outer = path_image J" by metis
  from io have io2: "outer \<inter> inner = {}" "outer \<union> inner = - path_image J" by auto

  have swap_side: "\<And>y t. y \<in> side2 \<Longrightarrow>
    0 \<le> t \<Longrightarrow> t \<in> existence_ivl0 y \<Longrightarrow>
    flow0 y t \<in> closure side1 \<Longrightarrow>
    \<exists>T. 0 < T \<and> T \<le> t \<and> (\<forall>s \<in>{0..<T}. flow0 y s \<in> side2) \<and>
        flow0 y T \<in> {flow0 x t1--<flow0 x t2}"
    if "side1 \<inter> side2 = {}"
      "open side2"
      "frontier side1 = path_image J"
      "frontier side2 = path_image J"
      "side1 \<union> side2 = - path_image J"
    for side1 side2
  proof -
    fix y t
    assume yt: "y \<in> side2" "0 \<le> t" "t \<in> existence_ivl0 y"
      "flow0 y t \<in> closure side1"
    define fp where "fp = flow_to_path y 0 t"
    have ex:"{0..t} \<subseteq> existence_ivl0 y"
      using ivl_subset_existence_ivl yt(3) by blast
    then have y0:"flow0 y 0 = y"
      using mem_existence_ivl_iv_defined(2) yt(3) by auto
    then have tpos: "t > 0" using yt(2)  \<open>side1 \<inter> side2 = {}\<close>
      using yt(1) yt(4)
      by (metis closure_iff_nhds_not_empty less_eq_real_def order_refl that(2)) 
    from flow_to_path_path[OF yt(2) ex]
    have a1: "path fp" unfolding fp_def .
    have "y \<in> closure side2" using yt(1)
      by (simp add: assms closure_def)
    then have a2: "pathstart fp \<in> closure side2" unfolding fp_def using y0 by auto
    have a3:"pathfinish fp \<notin> side2" using yt(4) \<open>side1 \<inter> side2 = {}\<close>
      unfolding fp_def apply auto
      using closure_iff_nhds_not_empty that(2) by blast
    from subpath_to_frontier_strong[OF a1 a3]
    obtain u where u:"0 \<le> u" "u \<le> 1"
      "fp u \<notin> interior side2"
      "u = 0 \<or>
      (\<forall>x. 0 \<le> x \<and> x < 1 \<longrightarrow>
        subpath 0 u fp x \<in> interior side2) \<and> fp u \<in> closure side2" by blast
    have p1:"path_image (subpath 0 u fp) =  flow0 y ` {0 ..  u*t}"
      unfolding fp_def subpath0_flow_to_path using path_image_flow_to_path
      by (simp add: u(1) yt(2))
    have p2:"fp u = flow0 y (u*t)" unfolding fp_def flow_to_path_unfold by simp
    have inout:"interior side2 = side2" using \<open>open side2\<close>
      by (simp add: interior_eq)
    then have iemp: "side2 \<inter> path_image J = {}"
      using \<open>frontier side2 = path_image J\<close>
      by (metis frontier_disjoint_eq inf_sup_aci(1) interior_eq)
    have "u \<noteq> 0" using inout u(3) y0 p2 yt(1) by force
    then have c1:"u * t > 0" using tpos u y0  \<open>side1 \<inter> side2 = {}\<close>
      using frontier_disjoint_eq io(5) yt(1) zero_less_mult_iff by fastforce
    have uim:"fp u \<in> path_image J" using u \<open>u \<noteq> 0\<close>
      using \<open>frontier side2 = path_image J\<close>
      by (metis ComplI IntI closure_subset frontier_closures inout subsetD) 
    have c2:"u * t \<le> t"  using u(1-2) tpos by auto
    have"(flow_to_path y 0 (u * t) ` {0..<1} \<subseteq> side2)"
      using \<open>u \<noteq> 0\<close> u inout unfolding fp_def subpath0_flow_to_path by auto
    then have c3:"\<forall>s \<in>{0..<u*t}. flow0 y s \<in> side2" by auto
    have c4: "flow0 y (u*t) \<in> path_image J"
      using uim path_image_join_subset
      by (simp add: p2)
    have "flow0 y (u*t) \<notin> path_image J1 \<or> flow0 y (u*t) = flow0 x t1"
    proof clarsimp
      assume "flow0 y (u*t) \<in> path_image J1"
      then obtain s where s: "t1 \<le> s" "s \<le> t2" "flow0 x s = flow0 y (u*t)"
        using J1_def \<open>t1 \<le> t2\<close> by auto
      have "s = t1"
      proof (rule ccontr)
        assume "s \<noteq> t1"
        then have st1:"s > t1" using s(1) by linarith
        define sc where "sc = min (s-t1) (u*t)"
        have scd: "s-sc \<in> {t1..t2}" unfolding sc_def
          using c1 s(1) s(2) by auto
        then have *:"flow0 x (s-sc) \<in> path_image J1" unfolding J1_def path_image_flow_to_path[OF \<open>t1 \<le> t2\<close>]
          by blast
        have "flow0 x (s-sc) = flow0 (flow0 x s) (-sc)"
          by (smt exist atLeastAtMost_iff existence_ivl_trans' flow_trans s(1) s(2) scd subsetD)
        then have **:"flow0 (flow0 y (u*t)) (-sc)  \<in> path_image J1"
          using s(3) * by auto
        have b:"u*t - sc \<in> {0..<u*t}" unfolding sc_def by (simp add: st1 c1 s(1))
        then have "u*t - sc \<in> existence_ivl0 y"
          using c2 ex by auto 
        then have "flow0 y (u*t - sc) \<in> path_image J1" using **
          by (smt atLeastAtMost_iff diff_existence_ivl_trans ex flow_trans mult_left_le_one_le mult_nonneg_nonneg subset_eq u(1) u(2) yt(2))
        thus False using b c3 iemp piJ by blast
      qed
      thus "flow0 y (u * t) = flow0 x t1" using s by simp
    qed
    thus "\<exists>T>0. T \<le> t \<and> (\<forall>s\<in>{0..<T}. flow0 y s \<in> side2) \<and>
          flow0 y T \<in> {flow0 x t1--<flow0 x t2}"
      using c1 c2 c3 c4 unfolding piD
      by (metis DiffE UnE ends_in_segment(1) half_open_segment_closed_segmentI insertCI open_segment_def x1neqx2)
  qed
  have outside_in: "\<And>y t. y \<in> outer \<Longrightarrow>
    0 \<le> t \<Longrightarrow> t \<in> existence_ivl0 y \<Longrightarrow>
    flow0 y t \<in> closure inner \<Longrightarrow>
    \<exists>T. 0 < T \<and> T \<le> t \<and> (\<forall>s \<in>{0..<T}. flow0 y s \<in> outer) \<and>
          flow0 y T \<in> {flow0 x t1--<flow0 x t2}"
    by (rule swap_side; (rule io | assumption))
  have inside_out: "\<And>y t. y \<in> inner \<Longrightarrow>
    0 \<le> t \<Longrightarrow> t \<in> existence_ivl0 y \<Longrightarrow>
    flow0 y t \<in> closure outer \<Longrightarrow>
    \<exists>T. 0 < T \<and> T \<le> t \<and> (\<forall>s \<in>{0..<T}. flow0 y s \<in> inner) \<and>
          flow0 y T \<in> {flow0 x t1--<flow0 x t2}"
    by (rule swap_side; (rule io2 io | assumption))

  from leaves_transversal_segmentE[OF assms(1)]
  obtain d n where d: "d > (0::real)"
    and n: "n = a - b \<or> n = b - a"
    and d_ex: "\<And>x. x \<in> {a -- b} \<Longrightarrow> {-d..d} \<subseteq> existence_ivl0 x"
    and d_above: "\<And>x s. x \<in> {a -- b} \<Longrightarrow> 0 < s \<Longrightarrow> s \<le> d \<Longrightarrow> (flow0 x s - x) \<bullet> rot n > 0"
    and d_below: "\<And>x s. x \<in> {a -- b} \<Longrightarrow> -d \<le> s \<Longrightarrow> s < 0 \<Longrightarrow> (flow0 x s - x) \<bullet> rot n < 0"
    by blast

  have ortho: "(a - b) \<bullet> rot n = 0"
    using n by (auto simp: algebra_simps)

(* These "rectangles" are either fully inside or fully outside
           |-----------------------|
           |           r1          | (flow d)
    a --- (t1) --- rp --- (t2) --- b
    |          r2           | (flow -d)
    |-----------------------|
   *)
  define r1 where "r1 = (\<lambda>(x, y). flow0 x y)`({flow0 x t1<--<b} \<times> {0<..<d}) "
  have r1a1: "path_connected {flow0 x t1 <--<b}" by simp
  have r1a2: "path_connected {0<..<d}" by simp
  have "{flow0 x t1<--<b} \<subseteq> {a--b}"
    by (simp add: open_closed_segment subset_oc_segment x1)
  then have r1a3: "y \<in> {flow0 x t1<--<b} \<Longrightarrow> {0<..<d} \<subseteq> existence_ivl0 y" for y
    using d_ex[of y]
    by force
  from flow0_path_connected[OF r1a1 r1a2 r1a3]
  have pcr1:"path_connected r1" unfolding r1_def by auto
  have pir1J1: "r1 \<inter> path_image J1 = {}"
    unfolding J1_def path_image_flow_to_path[OF \<open>t1 \<le> t2\<close>]
  proof (rule ccontr)
    assume "r1 \<inter> flow0 x ` {t1..t2} \<noteq> {}"
    then obtain xx tt ss where
      eq: "flow0 xx tt = flow0 x ss"
      and xx: "xx \<in> {flow0 x t1<--<b}"
      and ss: "t1 \<le> ss" "ss \<le> t2"
      and tt: "0 < tt" "tt < d"
      unfolding r1_def
      by force
    have "xx \<in> {a -- b}"
      using sub1b
      apply (rule set_mp)
      using xx by (simp add: open_closed_segment)
    then have [simp]: "xx \<in> X" using \<open>transversal_segment a b\<close> by (auto simp: transversal_segment_def)
    from ss have ss_ex: "ss \<in> existence_ivl0 x" using exist
      by auto
    from d_ex[OF \<open>xx \<in> {a -- b}\<close>] tt
    have tt_ex: "tt \<in> existence_ivl0 xx" by auto
    then have neg_tt_ex: "- tt \<in> existence_ivl0 (flow0 xx tt)"
      by (rule existence_ivl_reverse[simplified])
    from eq have "flow0 (flow0 xx tt) (-tt) = flow0 (flow0 x ss) (-tt)"
      by simp
    then have "xx = flow0 x (ss - tt)"
      apply (subst (asm) flow_trans[symmetric])
        apply (rule tt_ex)
       apply (rule neg_tt_ex)
      apply (subst (asm) flow_trans[symmetric])
        apply (rule ss_ex)
       apply (subst eq[symmetric])
       apply (rule neg_tt_ex)
      by simp
    moreover
    define e where "e = ss - t1"
    consider "e > tt" | "e \<le> tt" by arith
    then show False
    proof cases
      case 1
      have "flow0 (flow0 x ss) (-tt) \<notin> {a<--<b}"
        apply (subst flow_trans[symmetric])
          apply fact
        subgoal using neg_tt_ex eq by simp
        apply (rule t1t2)
        using 1 ss tt
        unfolding e_def
        by auto
      moreover have "flow0 (flow0 x ss) (-tt) \<in> {a<--<b}"
        unfolding eq[symmetric] using tt_ex xx
        apply (subst flow_trans[symmetric])
          apply (auto simp add: neg_tt_ex)
        by (metis (no_types, hide_lams) sub1b subset_eq subset_open_segment)
      ultimately show ?thesis by simp
    next
      case 2
      have les: "0 \<le> tt - e" "tt - e \<le> d"
        using tt ss 2 e_def
        by auto
      have xxtte: "flow0 xx (tt - e) = flow0 x t1"
        apply (simp add: e_def)
        by (smt \<open>0 \<le> tt - e\<close> \<open>{- d..d} \<subseteq> existence_ivl0 xx\<close> atLeastAtMost_iff e_def eq
            local.existence_ivl_reverse local.existence_ivl_trans local.flow_trans ss(1) ss_ex subset_iff tt(2))
      show False
      proof (cases "tt = e")
        case True
        with xxtte have "xx = flow0 x t1"
          by (simp add: )
        with xx show ?thesis
          apply auto
          by (auto simp: open_segment_def)
      next
        case False
        with les have "0 < tt - e" by (simp)
        from d_above[OF \<open>xx \<in> {a -- b}\<close> this \<open>tt - e \<le> d\<close>]
        have "flow0 xx (tt - e) \<notin> {a -- b}"
          apply (simp add: in_closed_segment_iff_rot[OF \<open>a \<noteq> b\<close>]
              not_le )
          by (smt \<open>xx \<in> {a--b}\<close> inner_minus_right inner_rot_neg_move_base inner_rot_pos_move_base n rot_diff_commute)
        with xxtte show ?thesis
          using \<open>flow0 x t1 \<in> {a<--<flow0 x t2}\<close> suba2o by auto
      qed
    qed
  qed
    (* for sufficiently small d, the flow does not return to the line *)
  moreover
  have pir1J2: "r1 \<inter> path_image J2 = {}"
  proof -
    have "r1 \<subseteq> {x. (x - a) \<bullet> rot n > 0}"
      unfolding r1_def
    proof safe
      fix aa ba
      assume "aa \<in> {flow0 x t1<--<b}" "ba \<in> {0<..<d}"
      with sub1b show "0 < (flow0 aa ba - a) \<bullet> rot n"
        using segment_open_subset_closed[of "flow0 x t1" b]
        by (intro inner_pos_move_base[OF ortho d_above]) auto
    qed
    also have "\<dots> \<inter> {a -- b} = {}"
      using in_segment_inner_rot in_segment_inner_rot2 n by auto
    finally show ?thesis
      unfolding J2_def path_image_linepath
      using t12sub open_closed_segment
      by (force simp: closed_segment_commute)
  qed
  ultimately have pir1:"r1 \<inter> (path_image J) = {}" unfolding J_def
    by (metis disjoint_iff_not_equal not_in_path_image_join)

  define r2 where "r2 =(\<lambda>(x, y). flow0 x y)`({a <--< flow0 x t2} \<times> {-d<..<0})"
  have r2a1:"path_connected {a <--< flow0 x t2}" by simp
  have r2a2:"path_connected {-d<..<0}" by simp
  have "{a <--< flow0 x t2} \<subseteq> {a -- b}"
    by (meson ends_in_segment(1) open_closed_segment subset_co_segment subset_oc_segment t12sub)
  then have r2a3: "y \<in> {a <--< flow0 x t2} \<Longrightarrow> {-d<..<0} \<subseteq> existence_ivl0 y" for y
    using d_ex[of y]
    by force
  from flow0_path_connected[OF r2a1 r2a2 r2a3]
  have pcr2:"path_connected r2" unfolding r2_def by auto
  have pir2J2: "r2 \<inter> path_image J1 = {}"
    unfolding J1_def path_image_flow_to_path[OF \<open>t1 \<le> t2\<close>]
  proof (rule ccontr)
    assume "r2 \<inter> flow0 x ` {t1..t2} \<noteq> {}"
    then obtain xx tt ss where
      eq: "flow0 xx tt = flow0 x ss"
      and xx: "xx \<in> {a<--<flow0 x t2}"
      and ss: "t1 \<le> ss" "ss \<le> t2"
      and tt: "-d < tt" "tt < 0"
      unfolding r2_def
      by force
    have "xx \<in> {a -- b}"
      using suba2
      apply (rule set_mp)
      using xx by (simp add: open_closed_segment)
    then have [simp]: "xx \<in> X" using \<open>transversal_segment a b\<close> by (auto simp: transversal_segment_def)
    from ss have ss_ex: "ss \<in> existence_ivl0 x" using exist
      by auto
    from d_ex[OF \<open>xx \<in> {a -- b}\<close>] tt
    have tt_ex: "tt \<in> existence_ivl0 xx" by auto
    then have neg_tt_ex: "- tt \<in> existence_ivl0 (flow0 xx tt)"
      by (rule existence_ivl_reverse[simplified])
    from eq have "flow0 (flow0 xx tt) (-tt) = flow0 (flow0 x ss) (-tt)"
      by simp
    then have "xx = flow0 x (ss - tt)"
      apply (subst (asm) flow_trans[symmetric])
        apply (rule tt_ex)
       apply (rule neg_tt_ex)
      apply (subst (asm) flow_trans[symmetric])
        apply (rule ss_ex)
       apply (subst eq[symmetric])
       apply (rule neg_tt_ex)
      by simp
    moreover
    define e where "e = t2 - ss"
    consider "e > - tt" | "e \<le> -tt" by arith
    then show False
    proof cases
      case 1
      have "flow0 (flow0 x ss) (-tt) \<notin> {a<--<b}"
        apply (subst flow_trans[symmetric])
          apply fact
        subgoal using neg_tt_ex eq by simp
        apply (rule t1t2)
        using 1 ss tt
        unfolding e_def
        by auto
      moreover have "flow0 (flow0 x ss) (-tt) \<in> {a<--<b}"
        unfolding eq[symmetric] using tt_ex xx
        apply (subst flow_trans[symmetric])
          apply (auto simp add: neg_tt_ex)
        by (metis (no_types, hide_lams) suba2 subset_eq subset_open_segment)
      ultimately show ?thesis by simp
    next
      case 2
      have les: "tt + e \<le> 0" "-d \<le> tt + e"
        using tt ss 2 e_def
        by auto
      have xxtte: "flow0 xx (tt + e) = flow0 x t2"
        apply (simp add: e_def)
        by (smt atLeastAtMost_iff calculation eq exist local.existence_ivl_trans' local.flow_trans neg_tt_ex ss_ex subset_iff \<open>t1 \<le> t2\<close>)
      show False
      proof (cases "tt=-e")
        case True
        with xxtte have "xx = flow0 x t2"
          by (simp add: )
        with xx show ?thesis
          apply auto
          by (auto simp: open_segment_def)
      next
        case False
        with les have "tt+e < 0" by simp
        from d_below[OF \<open>xx \<in> {a -- b}\<close>  \<open>-d \<le> tt + e\<close> this]
        have "flow0 xx (tt + e) \<notin> {a -- b}"
          apply (simp add: in_closed_segment_iff_rot[OF \<open>a \<noteq> b\<close>]
              not_le )
          by (smt \<open>xx \<in> {a--b}\<close> inner_minus_right inner_rot_neg_move_base inner_rot_pos_move_base n rot_diff_commute)
        with xxtte show ?thesis
          using \<open>flow0 x t2 \<in> {a--b}\<close> by simp
      qed
    qed
  qed
  moreover
  have pir2J2: "r2 \<inter> path_image J2 = {}"
  proof -
    have "r2 \<subseteq> {x. (x - a) \<bullet> rot n < 0}"
      unfolding r2_def
    proof safe
      fix aa ba
      assume "aa \<in> {a<--<flow0 x t2}" "ba \<in> {-d<..<0}"
      with suba2 show "0 > (flow0 aa ba - a) \<bullet> rot n"
        using segment_open_subset_closed[of a "flow0 x t2"]
        by (intro inner_neg_move_base[OF ortho d_below]) auto
    qed
    also have "\<dots> \<inter> {a -- b} = {}"
      using in_segment_inner_rot in_segment_inner_rot2 n by auto
    finally show ?thesis
      unfolding J2_def path_image_linepath
      using t12sub open_closed_segment
      by (force simp: closed_segment_commute)
  qed
  ultimately have pir2:"r2 \<inter> (path_image J) = {}"
    unfolding J_def
    by (metis disjoint_iff_not_equal not_in_path_image_join)

  define rp where "rp = midpoint (flow0 x t1) (flow0 x t2)"
  have rpi: "rp \<in> {flow0 x t1<--<flow0 x t2}" unfolding rp_def
    by (simp add: x1neqx2)
  have "rp \<in> {a -- b}"
    using rpi suba2o subl by blast
  then have [simp]: "rp \<in> X"
    using \<open>{a--b} \<subseteq> X\<close> by blast

(* The fundamental case distinction *)
  have *: "pathfinish J1 = flow0 x t2"
    "pathstart J1 = flow0 x t1"
    "rp \<in> {flow0 x t2<--<flow0 x t1}"
    using rpi
    by (auto simp: open_segment_commute J1_def)
  have "{y. 0 < (y - flow0 x t2) \<bullet> rot (flow0 x t2 - flow0 x t1)} = {y. 0 < (y - rp) \<bullet> rot (flow0 x t2 - flow0 x t1)}"
    by (smt Collect_cong in_open_segment_rotD inner_diff_left nrm_dot rpi)
  also have "... =  {y. 0 > (y - rp) \<bullet> rot (flow0 x t1 - flow0 x t2)}"
    by (smt Collect_cong inner_minus_left nrm_reverse)
  also have " ... = {y. 0 > (y - rp) \<bullet> rot (a - b) }"
    by (metis rot_same_dir(2) x1 x2)
  finally have side1: "{y. 0 < (y - flow0 x t2) \<bullet> rot (flow0 x t2 - flow0 x t1)} = {y. 0 > (y - rp) \<bullet> rot (a - b) }"
    (is "_ = ?lower1") .
  have "{y. (y - flow0 x t2) \<bullet> rot (flow0 x t2 - flow0 x t1) < 0} = {y. (y - rp) \<bullet> rot (flow0 x t2 - flow0 x t1) < 0}"
    by (smt Collect_cong in_open_segment_rotD inner_diff_left nrm_dot rpi)
  also have "... =  {y. (y - rp) \<bullet> rot (flow0 x t1 - flow0 x t2) > 0}"
    by (smt Collect_cong inner_minus_left nrm_reverse)
  also have " ... = {y. 0 < (y - rp) \<bullet> rot (a - b) }"
    by (metis rot_same_dir(1) x1 x2)
  finally have side2: "{y. (y - flow0 x t2) \<bullet> rot (flow0 x t2 - flow0 x t1) < 0} = {y. 0 < (y - rp) \<bullet> rot (a - b) }"
    (is "_ = ?upper1") .
  from linepath_ball_inside_outside[OF \<open>simple_path J\<close>[unfolded J_def J2_def] *,
      folded J2_def J_def, unfolded side1 side2]
  obtain e where e0: "0 < e"
    "ball rp e \<inter> path_image J1 = {}"
    "ball rp e \<inter> ?lower1 \<subseteq> inner \<and>
        ball rp e \<inter> ?upper1 \<subseteq> outer \<or>
        ball rp e \<inter> ?upper1 \<subseteq> inner \<and>
        ball rp e \<inter> ?lower1 \<subseteq> outer"
    by (auto simp: inner_def outer_def)

  let ?lower = "{y. 0 > (y - rp) \<bullet> rot n }"
  let ?upper = "{y. 0 < (y - rp) \<bullet> rot n }"
  have "?lower1 = {y. 0 < (y - rp) \<bullet> rot n } \<and> ?upper1 = {y. 0 > (y - rp) \<bullet> rot n } \<or>
      ?lower1 = {y. 0 > (y - rp) \<bullet> rot n } \<and> ?upper1 =  {y. 0 < (y - rp) \<bullet> rot n }"
    using n rot_diff_commute[of a b]
    by auto
  from this e0 have e: "0 < e"
    "ball rp e \<inter> path_image J1 = {}"
    "ball rp e \<inter> ?lower \<subseteq> inner \<and>
        ball rp e \<inter> ?upper \<subseteq> outer \<or>
        ball rp e \<inter> ?upper \<subseteq> inner \<and>
        ball rp e \<inter> ?lower \<subseteq> outer"
    by auto

  have "\<forall>\<^sub>F t in at_right 0. t < d"
    by (auto intro!: order_tendstoD \<open>0 < d\<close>)
  then have evr: "\<forall>\<^sub>F t in at_right 0. 0 < (flow0 rp t - rp) \<bullet> rot n"
    unfolding eventually_at_filter
    by eventually_elim (auto intro!: \<open>rp \<in> {a--b}\<close> d_above)
  have "\<forall>\<^sub>F t in at_left 0. t > -d"
    by (auto intro!: order_tendstoD \<open>0 < d\<close>)
  then have evl: "\<forall>\<^sub>F t in at_left 0. 0 > (flow0 rp t - rp) \<bullet> rot n"
    unfolding eventually_at_filter
    by eventually_elim (auto intro!: \<open>rp \<in> {a--b}\<close> d_below)
  have "\<forall>\<^sub>F t in at 0. flow0 rp t \<in> ball rp e"
    unfolding mem_ball
    apply (subst dist_commute)
    apply (rule tendstoD)
    by (auto intro!: tendsto_eq_intros \<open>0 < e\<close>)
  then have evl2: "(\<forall>\<^sub>F t in at_left 0. flow0 rp t \<in> ball rp e)"
    and evr2: "(\<forall>\<^sub>F t in at_right 0. flow0 rp t \<in> ball rp e)"
    unfolding eventually_at_split by auto
  have evl3: "(\<forall>\<^sub>F t in at_left 0. t > -d)"
    and evr3: "(\<forall>\<^sub>F t in at_right 0. t < d)"
    by (auto intro!: order_tendstoD \<open>0 < d\<close>)
  have evl4: "(\<forall>\<^sub>F t in at_left 0. t < 0)"
    and evr4: "(\<forall>\<^sub>F t in at_right 0. t > 0)"
    by (auto simp: eventually_at_filter)
  from evl evl2 evl3 evl4
  have "\<forall>\<^sub>F t in at_left 0. (flow0 rp t - rp) \<bullet> rot n < 0 \<and> flow0 rp t \<in> ball rp e \<and> t > -d \<and> t < 0"
    by eventually_elim auto
  from eventually_happens[OF this]
  obtain dl where dl: "(flow0 rp dl - rp) \<bullet> rot n < 0" "flow0 rp dl \<in> ball rp e" "- d < dl" "dl < 0"
    by auto
  from evr evr2 evr3 evr4
  have "\<forall>\<^sub>F t in at_right 0. (flow0 rp t - rp) \<bullet> rot n > 0 \<and> flow0 rp t \<in> ball rp e \<and> t < d \<and> t > 0"
    by eventually_elim auto
  from eventually_happens[OF this]
  obtain dr where dr: "(flow0 rp dr - rp) \<bullet> rot n > 0" "flow0 rp dr \<in> ball rp e" "d > dr" "dr > 0"
    by auto

  have "rp \<in> {flow0 x t1<--<b}" using rpi subr by auto
  then have rpr1:"flow0 rp (dr) \<in> r1" unfolding r1_def using \<open>d > dr\<close> \<open>dr > 0\<close>
    by auto
  have "rp \<in> {a<--<flow0 x t2}" using rpi subl by auto
  then have rpr2:"flow0 rp (dl) \<in> r2" unfolding r2_def using \<open>-d < dl\<close> \<open>dl < 0\<close>
    by auto

  from e(3) dr dl
  have "flow0 rp (dr) \<in> outer \<and> flow0 rp (dl) \<in> inner \<or> flow0 rp (dr) \<in> inner \<and> flow0 rp (dl) \<in> outer"
    by auto
  moreover {
    assume "flow0 rp dr \<in> outer" "flow0 rp dl \<in> inner"
    then have
      r1o: "r1 \<inter> outer \<noteq> {}" and
      r2i: "r2 \<inter> inner \<noteq> {}" using rpr1 rpr2 by auto
    from path_connected_not_frontier_subset[OF pcr1 r1o]
    have "r1 \<subseteq> outer" using pir1 by (simp add: io(12))
    from path_connected_not_frontier_subset[OF pcr2 r2i]
    have "r2 \<subseteq> inner" using pir2 by (simp add: io(11))
    have "(\<lambda>(x, y). flow0 x y)`({flow0 x t2} \<times> {0<..<d}) \<subseteq> r1" unfolding r1_def
      by (auto intro!:image_mono simp add: x2)
    then have *:"\<And>t. 0 < t \<Longrightarrow> t < d \<Longrightarrow> flow0 (flow0 x t2) t \<in> outer"
      by (smt \<open>r1 \<subseteq> outer\<close> greaterThanLessThan_iff mem_Sigma_iff pair_imageI r1_def subset_eq x2)

    then have t2o: "\<And>t. 0 < t \<Longrightarrow> t < d \<Longrightarrow> flow0 x (t2 + t) \<in> outer"
      using r1a3[OF x2] exist flow_trans
      by (metis (no_types, hide_lams) closed_segment_commute ends_in_segment(1) local.existence_ivl_trans' local.flow_undefined0 real_Icc_closed_segment subset_eq \<open>t1 \<le> t2\<close>)

(* Construct a sequence of times converging to these points in r2 \<subseteq> inner *)
    have inner: "{a <--< flow0 x t2} \<subseteq> closure inner"
    proof (rule subsetI)
      fix y
      assume y: "y \<in> {a <--< flow0 x t2}"
      have [simp]: "y \<in> X"
        using y suba12_open suba2o \<open>{a -- b} \<subseteq> X\<close>
        by auto
      have "(\<forall>n. flow0 y (- d / real (Suc (Suc n))) \<in> inner)"
        using y
        using suba12_open \<open>0 < d\<close> suba2o \<open>{a -- b} \<subseteq> X\<close>
        by (auto intro!: set_mp[OF \<open>r2 \<subseteq> inner\<close>] image_eqI[where x="(y, -d/Suc (Suc n))" for n]
            simp: r2_def divide_simps) 
      moreover
      have d_over_0: "(\<lambda>s. - d / real (Suc (Suc s))) \<longlonglongrightarrow> 0"
        by (rule real_tendsto_divide_at_top)
          (auto intro!: filterlim_tendsto_add_at_top filterlim_real_sequentially)
      have "(\<lambda>n. flow0 y (- d / real (Suc (Suc n)))) \<longlonglongrightarrow> y"
        apply (rule tendsto_eq_intros)
           apply (rule tendsto_intros)
          apply (rule d_over_0)
        by auto
      ultimately show "y \<in> closure inner"
        unfolding closure_sequential
        by (intro exI[where x="\<lambda>n. flow0 y (-d/Suc (Suc n))"]) (rule conjI)
    qed
    then have "{a <--< flow0 x t1} \<subseteq> closure inner"
      using suba12_open by blast
    then have "{flow0 x t1 -- flow0 x t2} \<subseteq> closure inner"
      by (metis (no_types, lifting) closure_closure closure_mono closure_open_segment dual_order.trans inner subl x1neqx2)
    have outer:"\<And>t. t > t2 \<Longrightarrow> t \<in> existence_ivl0 x \<Longrightarrow> flow0 x t \<in> outer"
    proof (rule ccontr)
      fix t
      assume t: "t > t2" "t \<in> existence_ivl0 x" "flow0 x t \<notin> outer"
      have "0 \<le> t- (t2+d)" using t2o t  by smt 
      then have a2:"0 \<le> t - (t2+dr)" using d \<open>0 < dr\<close> \<open>dr < d\<close> by linarith
      have t2d2_ex: "t2 + dr \<in> existence_ivl0 x"
        using \<open>t1 \<le> t2\<close> exist d_ex[of "flow0 x t2"] \<open>flow0 x t2 \<in> {a--b}\<close> \<open>0 < d\<close> \<open>0 < dr\<close> \<open>dr < d\<close> 
        by (intro existence_ivl_trans) auto
      then have a3: "t - (t2 + dr) \<in> existence_ivl0 (flow0 x (t2 + dr))"
        using t(2)
        by (intro diff_existence_ivl_trans) auto
      then have "flow0 (flow0 x (t2 + dr)) (t - (t2 + dr)) = flow0 x t"
        by (subst flow_trans[symmetric]) (auto simp: t2d2_ex)
      moreover have "flow0 x t \<in> closure inner" using t(3) io
        by (metis ComplI Un_iff closure_Un_frontier)
      ultimately have a4: "flow0 (flow0 x (t2 + dr)) (t - (t2 + dr)) \<in> closure inner" by auto
      have a1: "flow0 x (t2+dr) \<in> outer"
        by (simp add: d t2o \<open>0 < dr\<close> \<open>dr < d\<close>)
      from outside_in[OF a1 a2 a3 a4]
      obtain T where T: "T > 0" "T \<le> t - (t2 + dr)"
        "(\<forall>s\<in>{0..<T}. flow0 (flow0 x (t2 + dr)) s \<in> outer)"
        "flow0 (flow0 x (t2 + dr)) T \<in> {flow0 x t1 --< flow0 x t2}" by blast
      define y where "y = flow0 (flow0 x (t2 + dr)) T"
      have "y \<in> {a <--< flow0 x t2}" unfolding y_def using T(4)
        using subl2 by blast 
      then have "(\<lambda>(x, y). flow0 x y)`({y} \<times> {-d<..<0}) \<subseteq> r2" unfolding r2_def
        by (auto intro!:image_mono)
      then have *:"\<And>t. -d < t \<Longrightarrow> t < 0 \<Longrightarrow> flow0 y t \<in> r2"
        by (simp add: pair_imageI subsetD)
      have "max (-T/2) dl < 0" using d T \<open>0 > dl\<close> \<open>dl > -d\<close> by auto
      moreover have "-d < max (-T/2) dl" using d T \<open>0 > dl\<close> \<open>dl > -d\<close> by auto
      ultimately have inner: "flow0 y (max (-T/2) dl) \<in> inner" using * \<open>r2 \<subseteq> inner\<close> by blast 
      have "0\<le>(T+(max (-T/2) dl))" using T(1) by linarith
      moreover have "(T+(max (-T/2) dl)) < T" using T(1) d \<open>0 > dl\<close> \<open>dl > -d\<close> by linarith
      ultimately have outer: " flow0 (flow0 x (t2 + dr)) (T+(max (-T/2) dl)) \<in> outer"
        using T by auto
      have T_ex: "T \<in> existence_ivl0 (flow0 x (t2 + dr))"
        apply (subst flow_trans)
        using exist \<open>t1 \<le> t2\<close>
        using d_ex[of "flow0 x t2"] \<open>flow0 x t2 \<in> {a -- b}\<close> \<open>d > 0\<close> T \<open>0 < dr\<close> \<open>dr < d\<close>
          apply (auto simp: )
        apply (rule set_rev_mp[where A="{0 .. t - (t2 + dr)}"], force)
        apply (rule ivl_subset_existence_ivl)
        apply (rule existence_ivl_trans')
         apply (rule existence_ivl_trans')
        by (auto simp: t)
      have T_ex2: "dr + T \<in> existence_ivl0 (flow0 x t2)"
        by (smt T_ex ends_in_segment(2) exist local.existence_ivl_trans local.existence_ivl_trans' real_Icc_closed_segment subset_eq t2d2_ex \<open>t1 \<le> t2\<close>)
      thus False using T \<open>t1 \<le> t2\<close> exist
        by (smt T_ex diff_existence_ivl_trans disjoint_iff_not_equal inner io(9) local.flow_trans local.flow_undefined0 outer y_def)
    qed
    have "closure inner \<inter> outer = {}"
      by (simp add: inf_sup_aci(1) io(5) io(9) open_Int_closure_eq_empty) 
    then have "flow0 x t \<notin> {a<--<flow0 x t2}"
      using \<open>t > t2\<close> \<open>t \<in> existence_ivl0 x\<close> inner outer by blast
  }
  moreover {
    assume "flow0 rp dr \<in> inner" "flow0 rp dl \<in> outer"
    then have
      r1i: "r1 \<inter> inner \<noteq> {}" and
      r2o: "r2 \<inter> outer \<noteq> {}" using rpr1 rpr2 by auto
    from path_connected_not_frontier_subset[OF pcr1 r1i]
    have "r1 \<subseteq> inner" using pir1 by (simp add: io(11))
    from path_connected_not_frontier_subset[OF pcr2 r2o]
    have "r2 \<subseteq> outer" using pir2 by (simp add: io(12))

    have "(\<lambda>(x, y). flow0 x y)`({flow0 x t2} \<times> {0<..<d}) \<subseteq> r1" unfolding r1_def
      by (auto intro!:image_mono simp add: x2)
    then have
      *:"\<And>t. 0 < t \<Longrightarrow> t < d \<Longrightarrow> flow0 (flow0 x t2) t \<in> inner"
      by (smt \<open>r1 \<subseteq> inner\<close> greaterThanLessThan_iff mem_Sigma_iff pair_imageI r1_def subset_eq x2)

    then have t2o: "\<And>t. 0 < t \<Longrightarrow> t < d \<Longrightarrow> flow0 x (t2 + t) \<in> inner"
      using r1a3[OF x2] exist flow_trans
      by (metis (no_types, hide_lams) closed_segment_commute ends_in_segment(1) local.existence_ivl_trans' local.flow_undefined0 real_Icc_closed_segment subset_eq \<open>t1 \<le> t2\<close>)

(* Construct a sequence of times converging to these points in r2 \<subseteq> outer *)
    have outer: "{a <--< flow0 x t2} \<subseteq> closure outer"
    proof (rule subsetI)
      fix y
      assume y: "y \<in> {a <--< flow0 x t2}"
      have [simp]: "y \<in> X"
        using y suba12_open suba2o \<open>{a -- b} \<subseteq> X\<close>
        by auto
      have "(\<forall>n. flow0 y (- d / real (Suc (Suc n))) \<in> outer)"
        using y
        using suba12_open \<open>0 < d\<close> suba2o \<open>{a -- b} \<subseteq> X\<close>
        by (auto intro!: set_mp[OF \<open>r2 \<subseteq> outer\<close>] image_eqI[where x="(y, -d/Suc (Suc n))" for n]
            simp: r2_def divide_simps) 
      moreover
      have d_over_0: "(\<lambda>s. - d / real (Suc (Suc s))) \<longlonglongrightarrow> 0"
        by (rule real_tendsto_divide_at_top)
          (auto intro!: filterlim_tendsto_add_at_top filterlim_real_sequentially)
      have "(\<lambda>n. flow0 y (- d / real (Suc (Suc n)))) \<longlonglongrightarrow> y"
        apply (rule tendsto_eq_intros)
           apply (rule tendsto_intros)
          apply (rule d_over_0)
        by auto
      ultimately show "y \<in> closure outer"
        unfolding closure_sequential
        by (intro exI[where x="\<lambda>n. flow0 y (-d/Suc (Suc n))"]) (rule conjI)
    qed
    then have "{a <--< flow0 x t1} \<subseteq> closure outer"
      using suba12_open by blast
    then have "{flow0 x t1 -- flow0 x t2} \<subseteq> closure outer"
      by (metis (no_types, lifting) closure_closure closure_mono closure_open_segment dual_order.trans outer subl x1neqx2)

    have inner:"\<And>t. t > t2 \<Longrightarrow> t \<in> existence_ivl0 x \<Longrightarrow> flow0 x t \<in> inner"
    proof (rule ccontr)
      fix t
      assume t: "t > t2" "t \<in> existence_ivl0 x" "flow0 x t \<notin> inner"
      have "0 \<le> t- (t2+d)" using t2o t by smt 
      then have a2:"0 \<le> t - (t2+dr)" using d \<open>0 < dr\<close> \<open>dr < d\<close> by linarith
      have t2d2_ex: "t2 + dr \<in> existence_ivl0 x"
        using \<open>t1 \<le> t2\<close> exist d_ex[of "flow0 x t2"] \<open>flow0 x t2 \<in> {a--b}\<close> \<open>0 < d\<close> \<open>0 < dr\<close> \<open>dr < d\<close> 
        by (intro existence_ivl_trans) auto
      then have a3: "t - (t2 + dr) \<in> existence_ivl0 (flow0 x (t2 + dr))"
        using t(2)
        by (intro diff_existence_ivl_trans) auto
      then have "flow0 (flow0 x (t2 + dr)) (t - (t2 + dr)) = flow0 x t"
        by (subst flow_trans[symmetric]) (auto simp: t2d2_ex)
      moreover have "flow0 x t \<in> closure outer" using t(3) io
        by (metis ComplI Un_iff closure_Un_frontier)
      ultimately have a4: "flow0 (flow0 x (t2 + dr)) (t - (t2 + dr)) \<in> closure outer" by auto
      have a1: "flow0 x (t2+dr) \<in> inner"
        by (simp add: d t2o \<open>0 < dr\<close> \<open>dr < d\<close>)
      from inside_out[OF a1 a2 a3 a4]
      obtain T where T: "T > 0" "T \<le> t - (t2 + dr)"
        "(\<forall>s\<in>{0..<T}. flow0 (flow0 x (t2 + dr)) s \<in> inner)"
        "flow0 (flow0 x (t2 + dr)) T \<in> {flow0 x t1 --< flow0 x t2}" by blast
      define y where "y = flow0 (flow0 x (t2 + dr)) T"
      have "y \<in> {a <--< flow0 x t2}" unfolding y_def using T(4)
        using subl2 by blast 
      then have "(\<lambda>(x, y). flow0 x y)`({y} \<times> {-d<..<0}) \<subseteq> r2" unfolding r2_def
        by (auto intro!:image_mono)
      then have *:"\<And>t. -d < t \<Longrightarrow> t < 0 \<Longrightarrow> flow0 y t \<in> r2"
        by (simp add: pair_imageI subsetD)
      have "max (-T/2) dl < 0" using d T \<open>0 > dl\<close> \<open>dl > -d\<close> by auto
      moreover have "-d < max (-T/2) dl" using d T \<open>0 > dl\<close> \<open>dl > -d\<close> by auto
      ultimately have outer: "flow0 y (max (-T/2) dl) \<in> outer" using * \<open>r2 \<subseteq> outer\<close> by blast 
      have "0\<le>(T+(max (-T/2) dl))" using T(1) by linarith
      moreover have "(T+(max (-T/2) dl)) < T" using T(1) d \<open>0 > dl\<close> \<open>dl > -d\<close> by linarith
      ultimately have inner: " flow0 (flow0 x (t2 + dr)) (T+(max (-T/2) dl)) \<in> inner"
        using T by auto
      have T_ex: "T \<in> existence_ivl0 (flow0 x (t2 + dr))"
        apply (subst flow_trans)
        using exist \<open>t1 \<le> t2\<close>
        using d_ex[of "flow0 x t2"] \<open>flow0 x t2 \<in> {a -- b}\<close> \<open>d > 0\<close> T \<open>0 < dr\<close> \<open>dr < d\<close>
          apply (auto simp: )
        apply (rule set_rev_mp[where A="{0 .. t - (t2 + dr)}"], force)
        apply (rule ivl_subset_existence_ivl)
        apply (rule existence_ivl_trans')
         apply (rule existence_ivl_trans')
        by (auto simp: t)
      have T_ex2: "dr + T \<in> existence_ivl0 (flow0 x t2)"
        by (smt T_ex ends_in_segment(2) exist local.existence_ivl_trans local.existence_ivl_trans' real_Icc_closed_segment subset_eq t2d2_ex \<open>t1 \<le> t2\<close>)
      thus False using T \<open>t1 \<le> t2\<close> exist
        by (smt T_ex diff_existence_ivl_trans disjoint_iff_not_equal inner io(9) local.flow_trans local.flow_undefined0 outer y_def)
    qed
    have "closure outer \<inter> inner = {}"
      by (metis inf_sup_aci(1) io(2) io2(1) open_Int_closure_eq_empty)
    then have "flow0 x t \<notin> {a<--<flow0 x t2}"
      using \<open>t > t2\<close> \<open>t \<in> existence_ivl0 x\<close> inner outer by blast
  }
  ultimately show
    "flow0 x t \<notin> {a<--<flow0 x t2}" by auto
qed

lemma open_segment_trichotomy:
  fixes x y a b::'a
  assumes x:"x \<in> {a<--<b}"
  assumes y:"y \<in> {a<--<b}"
  shows "x = y \<or> y \<in> {x<--<b} \<or> y \<in> {a<--<x}"
proof -
  from Un_open_segment[OF y]
  have "{a<--<y} \<union> {y} \<union> {y<--<b} = {a<--<b}" .
  then have "x \<in> {a<--<y} \<or> x = y \<or> x \<in> {y <--<b}" using x by blast
  moreover {
    assume "x \<in> {a<--<y}"
    then have "y \<in> {x<--<b}" using open_segment_subsegment
      using open_segment_commute y by blast
  }
  moreover {
    assume "x \<in> {y<--<b}"
    from open_segment_subsegment[OF y this]
    have "y \<in> {a<--<x}" .
  }
  ultimately show ?thesis by blast
qed

sublocale rev: c1_on_open_R2 "-f" "-f'" rewrites "-(-f) = f" and "-(-f') = f'"
  by unfold_locales (auto simp: dim2)

lemma rev_transversal_segment: "rev.transversal_segment a b = transversal_segment a b"
  by (auto simp: transversal_segment_def rev.transversal_segment_def)

lemma flow0_transversal_segment_monotone_step_reverse:
  assumes "transversal_segment a b"
  assumes "t1 \<le> t2"
  assumes "{t1..t2} \<subseteq> existence_ivl0 x"
  assumes x1: "flow0 x t1 \<in> {a<--<b}"
  assumes x2: "flow0 x t2 \<in> {a<--<flow0 x t1}"
  assumes "\<And>t. t \<in> {t1<..<t2} \<Longrightarrow> flow0 x t \<notin> {a<--<b}"
  assumes "t < t1" "t \<in> existence_ivl0 x"
  shows "flow0 x t \<notin> {a<--<flow0 x t1}"
proof -
  note exist = \<open>{t1..t2} \<subseteq> existence_ivl0 x\<close>
  note t1t2 = \<open>\<And>t. t \<in> {t1<..<t2} \<Longrightarrow> flow0 x t \<notin> {a<--<b}\<close>
  from \<open>transversal_segment a b\<close> have [simp]: "a \<noteq> b" by (simp add: transversal_segment_def)
  from x1 obtain i1 where i1: "flow0 x t1 = line a b i1" "0 < i1" "i1 < 1"
    by (auto simp: in_open_segment_iff_line)
  from x2 obtain i2 where i2: "flow0 x t2 = line a b i2" "0 < i2" "i2 < i1"
    by (auto simp: i1 open_segment_line_iff)

  have t2_exist[simp]: "t2 \<in> existence_ivl0 x"
    using \<open>t1 \<le> t2\<close> exist by auto
  have t2_mem: "flow0 x t2 \<in> {a<--<b}"
    and x1_mem: "flow0 x t1 \<in> {flow0 x t2<--<b}"
    using i1 i2
    by (auto simp: line_in_subsegment line_line1)

  have transversal': "rev.transversal_segment a b"
    using \<open>transversal_segment a b\<close> unfolding rev_transversal_segment .
  have time': "0 \<le> t2 - t1" using \<open>t1 \<le> t2\<close> by simp
  have [simp, intro]: "flow0 x t2 \<in> X"
    using exist \<open>t1 \<le> t2\<close>
    by auto
  have exivl': "{0..t2 - t1} \<subseteq> rev.existence_ivl0 (flow0 x t2)"
    using exist \<open>t1 \<le> t2\<close>
    by (force simp add: rev_existence_ivl_eq0 intro!: existence_ivl_trans')
  have step': "rev.flow0 (flow0 x t2) (t2-t) \<notin>  {a<--<rev.flow0 (flow0 x t2) (t2 - t1)}"
    apply (rule rev.flow0_transversal_segment_monotone_step[OF transversal' time' exivl'])
    using exist \<open>t1 \<le> t2\<close> x1 x2 t2_mem x1_mem t1t2 \<open>t < t1\<close> \<open>t \<in> existence_ivl0 x\<close>
        apply (auto simp: rev_existence_ivl_eq0 rev_eq_flow existence_ivl_trans' flow_trans[symmetric])
    by (subst (asm) flow_trans[symmetric]) (auto intro!: existence_ivl_trans')
  then show ?thesis
    unfolding rev_eq_flow
    using \<open>t1 \<le> t2\<close> exist \<open>t < t1\<close> \<open>t \<in> existence_ivl0 x\<close>
    by (auto simp: flow_trans[symmetric] existence_ivl_trans')
qed

lemma flow0_transversal_segment_monotone_step_reverse2:
  assumes transversal: "transversal_segment a b"
  assumes time: "t1 \<le> t2"
  assumes exist: "{t1..t2} \<subseteq> existence_ivl0 x"
  assumes t1: "flow0 x t1 \<in> {a<--<b}"
  assumes t2: "flow0 x t2 \<in> {flow0 x t1<--<b}"
  assumes t1t2: "\<And>t. t \<in> {t1<..<t2} \<Longrightarrow> flow0 x t \<notin> {a<--<b}"
  assumes t: "t < t1" "t \<in> existence_ivl0 x"
  shows "flow0 x t \<notin> {flow0 x t1<--<b}"
  using flow0_transversal_segment_monotone_step_reverse[of b a, OF _ time exist, of t]
    assms
  by (auto simp: open_segment_commute transversal_segment_commute)

lemma flow0_transversal_segment_monotone_step2:
  assumes transversal: "transversal_segment a b"
  assumes time: "t1 \<le> t2"
  assumes exist: "{t1..t2} \<subseteq> existence_ivl0 x"
  assumes t1: "flow0 x t1 \<in> {a<--<b}"
  assumes t2: "flow0 x t2 \<in> {a<--<flow0 x t1}"
  assumes t1t2: "\<And>t. t \<in> {t1<..<t2} \<Longrightarrow> flow0 x t \<notin> {a<--<b}"
  shows "\<And>t. t > t2 \<Longrightarrow> t \<in> existence_ivl0 x \<Longrightarrow> flow0 x t \<notin> {flow0 x t2<--<b}"
  using flow0_transversal_segment_monotone_step[of b a, OF _ time exist]
    assms
  by (auto simp: transversal_segment_commute open_segment_commute)

lemma flow0_transversal_segment_monotone:
  assumes "transversal_segment a b"
  assumes "t1 \<le> t2"
  assumes "{t1..t2} \<subseteq> existence_ivl0 x"
  assumes x1: "flow0 x t1 \<in> {a<--<b}"
  assumes x2: "flow0 x t2 \<in> {flow0 x t1<--<b}"
  assumes "t > t2" "t \<in> existence_ivl0 x"
  shows "flow0 x t \<notin> {a<--<flow0 x t2}"
proof -
  note exist = \<open>{t1..t2} \<subseteq> existence_ivl0 x\<close>
  note t = \<open>t > t2\<close> \<open>t \<in> existence_ivl0 x\<close>
  have x1neqx2: "flow0 x t1 \<noteq> flow0 x t2"
    using open_segment_def x2 by force 
  then have t1neqt2: "t1 \<noteq> t2" by auto
  with \<open>t1 \<le> t2\<close> have "t1 < t2" by simp

  from \<open>transversal_segment a b\<close> have [simp]: "a \<noteq> b" by (simp add: transversal_segment_def)
  from x1 obtain i1 where i1: "flow0 x t1 = line a b i1" "0 < i1" "i1 < 1"
    by (auto simp: in_open_segment_iff_line)
  from x2 i1 obtain i2 where i2: "flow0 x t2 = line a b i2" "i1 < i2" "i2 < 1"
    by (auto simp: line_open_segment_iff)
  have t2_in: "flow0 x t2 \<in> {a<--<b}"
    using i1 i2
    by simp

  let ?T = "{s \<in> {t1..t2}. flow0 x s \<in> {a--b}}"
  let ?T' = "{s \<in> {t1..<t2}. flow0 x s \<in> {a<--<b}}"
  from flow_transversal_segment_finite_intersections[OF \<open>transversal_segment a b\<close> \<open>t1 \<le> t2\<close> exist]
  have "finite ?T" .
  then have "finite ?T'" by (rule finite_subset[rotated]) (auto simp: open_closed_segment)
  have "?T' \<noteq> {}"
    by (auto intro!: exI[where x=t1] \<open>t1 < t2\<close> x1)
  note tm_defined = \<open>finite ?T'\<close> \<open>?T' \<noteq> {}\<close>
  define tm where "tm = Max ?T'"
  have "tm \<in> ?T'"
    unfolding tm_def
    using tm_defined by (rule Max_in)
  have tm_in: "flow0 x tm \<in> {a<--<b}"
    using \<open>tm \<in> ?T'\<close>
    by auto
  have tm: "t1 \<le> tm" "tm < t2" "tm \<le> t2"
    using \<open>tm \<in> ?T'\<close> by auto
  have tm_Max: "t \<le> tm" if "t \<in> ?T'" for t
    unfolding tm_def
    using tm_defined(1) that
    by (rule Max_ge)

  have tm_exclude: "flow0 x t \<notin> {a<--<b}" if "t \<in> {tm<..<t2}" for t
    using \<open>tm \<in> ?T'\<close> tm_Max that
    by auto (meson approximation_preproc_push_neg(2) dual_order.strict_trans2 le_cases)
  have "{tm..t2} \<subseteq> existence_ivl0 x"
    using exist tm by auto

  from open_segment_trichotomy[OF tm_in t2_in]
  consider
    "flow0 x t2 \<in> {flow0 x tm<--<b}" |
    "flow0 x t2 \<in> {a<--<flow0 x tm}" |
    "flow0 x tm = flow0 x t2"
    by blast
  then show "flow0 x t \<notin> {a<--<flow0 x t2}"
  proof cases
    case 1
    from flow0_transversal_segment_monotone_step[OF \<open>transversal_segment a b\<close> \<open>tm \<le> t2\<close>
        \<open>{tm..t2} \<subseteq> existence_ivl0 x\<close> tm_in 1 tm_exclude t]
    show ?thesis .
  next
    case 2
    have "t1 \<noteq> tm"
      using 2 x2 i1 i2
      by (auto simp: line_in_subsegment line_in_subsegment2)
    then have "t1 < tm" using \<open>t1 \<le> tm\<close> by simp
    from flow0_transversal_segment_monotone_step_reverse[OF \<open>transversal_segment a b\<close> \<open>tm \<le> t2\<close>
        \<open>{tm..t2} \<subseteq> existence_ivl0 x\<close> tm_in 2 tm_exclude \<open>t1 < tm\<close>] exist \<open>t1 \<le> t2\<close>
    have "flow0 x t1 \<notin> {a<--<flow0 x tm}" by auto
    then have False
      using x1 x2 2 i1 i2
      apply (auto simp: line_in_subsegment line_in_subsegment2)
      by (smt greaterThanLessThan_iff in_open_segment_iff_line line_in_subsegment2 tm_in)
    then show ?thesis by simp
  next
    case 3
    have "t1 \<noteq> tm"
      using 3 x2
      by (auto simp: open_segment_def)
    then have "t1 < tm" using \<open>t1 \<le> tm\<close> by simp
    have "range (flow0 x) = flow0 x ` {tm..t2}"
      apply (rule recurrence_time_restricts_compact_flow'[OF \<open>tm < t2\<close> _ _ 3])
      using exist \<open>t1 \<le> t2\<close> \<open>t1 < tm\<close> \<open>tm < t2\<close>
      by auto
    also have "\<dots> = flow0 x ` (insert t2 {tm<..<t2})"
      using \<open>tm \<le> t2\<close> 3
      apply (auto simp: )
      by (smt greaterThanLessThan_iff image_eqI)
    finally have "flow0 x t1 \<in> flow0 x ` (insert t2 {tm<..<t2})"
      by auto
    then have "flow0 x t1 \<in> flow0 x ` {tm<..<t2}" using x1neqx2
      by auto
    moreover have "\<dots> \<inter> {a<--<b} = {}"
      using tm_exclude
      by auto
    ultimately have False using x1 by auto
    then show ?thesis by blast
  qed
qed

subsection \<open>Straightening\<close>

text \<open> This lemma uses the implicit function theorem \<close>
lemma cross_time_continuous:
  assumes "transversal_segment a b"
  assumes "x \<in> {a<--<b}"
  assumes "e > 0"
  obtains d t where "d > 0" "continuous_on (ball x d) t"
    "\<And>y. y \<in> ball x d \<Longrightarrow> flow0 y (t y) \<in> {a<--<b}"
    "\<And>y. y \<in> ball x d \<Longrightarrow> \<bar>t y\<bar> < e"
    "continuous_on (ball x d) t"
    "t x = 0"
proof -
  have "x \<in> X" using assms segment_open_subset_closed[of a b]
    by (auto simp: transversal_segment_def)
  have "a \<noteq> b" using assms by auto
  define s where "s x = (x - a) \<bullet> rot (b - a)" for x
  have "s x = 0"
    unfolding s_def
    by (subst in_segment_inner_rot) (auto intro!: assms open_closed_segment)
  have Ds: "(s has_derivative blinfun_inner_left (rot (b - a))) (at x)"
    (is "(_ has_derivative blinfun_apply (?Ds x)) _")
    for x
    unfolding s_def
    by (auto intro!: derivative_eq_intros)
  have Dsc: "isCont ?Ds x" by (auto intro!: continuous_intros)
  have nz: "?Ds x (f x) \<noteq> 0"
    using assms  apply auto
    unfolding transversal_segment_def
    by (smt inner_minus_left nrm_reverse open_closed_segment)

  from flow_implicit_function_at[OF \<open>x \<in> X\<close>, of s, OF \<open>s x = 0\<close> Ds Dsc nz \<open>e > 0\<close>]
  obtain t d1 where "0 < d1"
    and t0: "t x = 0"
    and d1: "(\<And>y. y \<in> cball x d1 \<Longrightarrow> s (flow0 y (t y)) = 0)"
    "(\<And>y. y \<in> cball x d1 \<Longrightarrow> \<bar>t y\<bar> < e)"
    "(\<And>y. y \<in> cball x d1 \<Longrightarrow> t y \<in> existence_ivl0 y)"
    and tc: "continuous_on (cball x d1) t"
    and t': "(t has_derivative
        (- blinfun_inner_left (rot (b - a)) /\<^sub>R (blinfun_inner_left (rot (b - a))) (f x)))
      (at x)"
    by metis
  from tc
  have "t \<midarrow>x\<rightarrow> 0"
    using \<open>0 < d1\<close>
    by (auto simp: continuous_on_def at_within_interior t0 dest!: bspec[where x=x])
  then have ftc: "((\<lambda>y. flow0 y (t y)) \<longlongrightarrow> x) (at x)"
    by (auto intro!: tendsto_eq_intros simp: \<open>x \<in> X\<close>)



  define e2 where "e2 = min (dist a x) (dist b x)"
  have "e2 > 0"
    using assms
    by (auto simp: e2_def open_segment_def)

  from tendstoD[OF ftc this] have "\<forall>\<^sub>F y in at x. dist (flow0 y (t y)) x < e2" .
  moreover
  let ?S = "{x. a \<bullet> (b - a) < x \<bullet> (b - a) \<and> x \<bullet> (b - a) < b \<bullet> (b - a)}"
  have "open ?S" "x \<in> ?S"
    using \<open>x \<in> {a<--<b}\<close>
    by (auto simp add: open_segment_line_hyperplanes \<open>a \<noteq> b\<close>
        intro!: open_Collect_conj open_halfspace_component_gt open_halfspace_component_lt)
  from topological_tendstoD[OF ftc this] have "\<forall>\<^sub>F y in at x. flow0 y (t y) \<in> ?S" .
  ultimately
  have "\<forall>\<^sub>F y in at x. flow0 y (t y) \<in> ball x e2 \<inter> ?S" by eventually_elim (auto simp: dist_commute)
  then obtain d2 where "0 < d2" and "\<And>y. x \<noteq> y \<Longrightarrow> dist y x < d2 \<Longrightarrow> flow0 y (t y) \<in> ball x e2 \<inter> ?S"
    by (force simp: eventually_at)
  then have d2: "dist y x < d2 \<Longrightarrow> flow0 y (t y) \<in> ball x e2 \<inter> ?S" for y
    using \<open>0 < e2\<close> \<open>x \<in> X\<close> t0 \<open>x \<in> ?S\<close>
    by (cases "y = x") auto

  define d where "d = min d1 d2"
  have "d > 0" using \<open>0 < d1\<close> \<open>0 < d2\<close> by (simp add: d_def)
  moreover have "continuous_on (ball x d) t"
    by (auto intro!:continuous_on_subset[OF tc] simp add: d_def)
  moreover
  have "ball x e2 \<inter> ?S \<inter> {x. s x = 0} \<subseteq> {a<--<b}"
    by (auto simp add: in_open_segment_iff_rot \<open>a \<noteq> b\<close>) (auto simp: s_def e2_def in_segment)
  then have "\<And>y. y \<in> ball x d \<Longrightarrow> flow0 y (t y) \<in> {a<--<b}"
    apply (rule set_mp)
    using d1 d2 \<open>0 < d2\<close>
    by (auto simp: d_def e2_def dist_commute)
  moreover have "\<And>y. y \<in> ball x d \<Longrightarrow> \<bar>t y\<bar> < e"
    using d1 by (auto simp: d_def)
  moreover have "continuous_on (ball x d) t"
    using tc by (rule continuous_on_subset) (auto simp: d_def)
  moreover have "t x = 0" by (simp add: t0)
  ultimately show ?thesis ..
qed

lemma \<omega>_limit_crossings:
  assumes "transversal_segment a b"
  assumes pos_ex: "{0..} \<subseteq> existence_ivl0 x"
  assumes "\<omega>_limit_point x p"
  assumes "p \<in> {a<--<b}"
  obtains s where 
    "s \<longlonglongrightarrow>\<^bsub>\<^esub> \<infinity>"
    "(flow0 x \<circ> s) \<longlonglongrightarrow> p"
    "\<forall>\<^sub>F n in sequentially. flow0 x (s n) \<in> {a<--<b} \<and> s n \<in> existence_ivl0 x"
proof -
  from assms have "p \<in> X" by (auto simp: transversal_segment_def open_closed_segment)
  from assms(3)
  obtain t where
    "t \<longlonglongrightarrow>\<^bsub>\<^esub> \<infinity>" "(flow0 x \<circ> t) \<longlonglongrightarrow> p"
    by (auto simp: \<omega>_limit_point_def)
  note t = \<open>t \<longlonglongrightarrow>\<^bsub>\<^esub> \<infinity>\<close> \<open>(flow0 x \<circ> t) \<longlonglongrightarrow> p\<close>
  note [tendsto_intros] = t(2)
  from cross_time_continuous[OF assms(1,4) zero_less_one\<comment> \<open>TODO ??\<close>]
  obtain \<tau> \<delta>
    where "0 < \<delta>" "continuous_on (ball p \<delta>) \<tau>" 
      "\<tau> p = 0" "(\<And>y. y \<in> ball p \<delta> \<Longrightarrow> \<bar>\<tau> y\<bar> < 1)"
      "(\<And>y. y \<in> ball p \<delta> \<Longrightarrow> flow0 y (\<tau> y) \<in> {a<--<b})"
    by metis
  note \<tau> =
    \<open>(\<And>y. y \<in> ball p \<delta> \<Longrightarrow> flow0 y (\<tau> y) \<in> {a<--<b})\<close>
    \<open>(\<And>y. y \<in> ball p \<delta> \<Longrightarrow> \<bar>\<tau> y\<bar> < 1)\<close>
    \<open>continuous_on (ball p \<delta>) \<tau>\<close> \<open>\<tau> p = 0\<close>
  define s where "s n = t n + \<tau> (flow0 x (t n))" for n
  have ev_in_ball: "\<forall>\<^sub>F n in at_top. flow0 x (t n) \<in> ball p \<delta>"
    apply (simp add: )
    apply (subst dist_commute)
    apply (rule tendstoD)
     apply (rule t[unfolded o_def])
    apply (rule \<open>0 < \<delta>\<close>)
    done
  have "filterlim s at_top sequentially"
  proof (rule filterlim_at_top_mono)
    show "filterlim (\<lambda>n. -1 + t n) at_top sequentially"
      by (rule filterlim_tendsto_add_at_top) (auto intro!: filterlim_tendsto_add_at_top t)
    from ev_in_ball show "\<forall>\<^sub>F x in sequentially. -1 + t x \<le> s x"
      apply eventually_elim
      using \<tau>
      by (force simp : s_def)
  qed
  moreover
  have \<tau>_cont: "\<tau> \<midarrow>p\<rightarrow> \<tau> p"
    using \<tau>(3) \<open>0 < \<delta>\<close>
    by (auto simp: continuous_on_def at_within_ball dest!: bspec[where x=p])
  note [tendsto_intros] = tendsto_compose_at[OF _ this, simplified]
  have ev1: "\<forall>\<^sub>F n in sequentially. t n > 1"
    using filterlim_at_top_dense t(1) by auto
  then have ev_eq: "\<forall>\<^sub>F n in sequentially. flow0 ((flow0 x o t) n) ((\<tau> o (flow0 x o t)) n) = (flow0 x o s) n"
    using ev_in_ball
    apply (eventually_elim)
    apply (drule \<tau>(2))
    unfolding o_def
    apply (subst flow_trans[symmetric])
    using pos_ex
      apply (auto simp: s_def)
    apply (rule existence_ivl_trans')
    by auto
  then
  have "\<forall>\<^sub>F n in sequentially.
  (flow0 x o s) n = flow0 ((flow0 x o t) n) ((\<tau> o (flow0 x o t)) n)"
    by (simp add: eventually_mono)
  from \<open>(flow0 x \<circ> t) \<longlonglongrightarrow> p\<close> and \<open>\<tau> \<midarrow>p\<rightarrow> \<tau> p\<close>
  have
    "(\<lambda>n. flow0 ((flow0 x \<circ> t) n) ((\<tau> \<circ> (flow0 x \<circ> t)) n))
  \<longlonglongrightarrow>
  flow0 p (\<tau> p)"
    using \<open>\<tau> p = 0\<close> \<tau>_cont \<open>p \<in> X\<close>
    by (intro tendsto_eq_intros) auto
  then have "(flow0 x o s) \<longlonglongrightarrow> flow0 p (\<tau> p)"
    using ev_eq by (rule Lim_transform_eventually)
  then have "(flow0 x o s) \<longlonglongrightarrow> p"
    using \<open>p \<in> X\<close> \<open>\<tau> p = 0\<close>
    by simp
  moreover
  {
    have "\<forall>\<^sub>F n in sequentially. flow0 x (s n) \<in> {a<--<b}"
      using ev_eq ev_in_ball
      apply eventually_elim
      apply (drule sym)
      apply simp
      apply (rule \<tau>) by simp
    moreover have "\<forall>\<^sub>F n in sequentially. s n \<in> existence_ivl0 x"
      using ev_in_ball ev1
      apply (eventually_elim)
      apply (drule \<tau>(2))
      using pos_ex
      by (auto simp: s_def)
    ultimately have "\<forall>\<^sub>F n in sequentially. flow0 x (s n) \<in> {a<--<b} \<and> s n \<in> existence_ivl0 x"
      by eventually_elim auto
  }
  ultimately show ?thesis ..
qed

(* Obvious but frequently used step *)
lemma filterlim_at_top_tendstoE:
  assumes "e > 0"
  assumes "filterlim s at_top sequentially"
  assumes "(flow0 x \<circ> s) \<longlonglongrightarrow> u"
  assumes "\<forall>\<^sub>F n in sequentially. P (s n)"
  obtains m where "m > b" "P m" "dist (flow0 x m) u < e"
proof -
  from assms(2) have "\<forall>\<^sub>F n in sequentially. b < s n"
    by (simp add: filterlim_at_top_dense)
  moreover have "\<forall>\<^sub>F n in sequentially. norm ((flow0 x \<circ> s) n - u) < e"
    using assms(3)[THEN tendstoD, OF assms(1)] by (simp add: dist_norm)
  moreover note assms(4)
  ultimately have "\<forall>\<^sub>F n in sequentially. b < s n \<and> norm ((flow0 x \<circ> s) n - u) < e \<and> P (s n)"
    by eventually_elim auto
  then obtain m where "m > b" "P m" "dist (flow0 x m) u < e"
    by (auto simp add: eventually_sequentially dist_norm)
  then show ?thesis ..
qed

lemma open_segment_separate_left:
  fixes u v x a b::'a
  assumes u:"u \<in> {a <--< b}"
  assumes v:"v \<in> {u <--< b}"
  assumes x: "dist x u < dist u v" "x \<in> {a <--< b}"
  shows "x \<in> {a <--< v}"
proof -
  have "v \<noteq> x"
    by (smt dist_commute x(1)) 
  moreover have "x \<notin> {v<--<b}"
    by (smt dist_commute dist_in_open_segment open_segment_subsegment v x(1))
  moreover have "v \<in> {a<--<b}" using v
    by (metis ends_in_segment(1) segment_open_subset_closed subset_eq subset_segment(4) u)
  ultimately show ?thesis using open_segment_trichotomy[OF _ x(2)]
    by blast
qed

lemma open_segment_separate_right:
  fixes u v x a b::'a
  assumes u:"u \<in> {a <--< b}"
  assumes v:"v \<in> {a <--< u}"
  assumes x: "dist x u < dist u v" "x \<in> {a <--< b}"
  shows "x \<in> {v <--< b}"
proof -
  have "v \<noteq> x"
    by (smt dist_commute x(1))
  moreover have "x \<notin> {a<--<v}"
    by (smt dist_commute dist_in_open_segment open_segment_commute open_segment_subsegment v x(1))
  moreover have "v \<in> {a<--<b}" using v
    by (metis ends_in_segment(1) segment_open_subset_closed subset_eq subset_segment(4) u)
  ultimately show ?thesis using open_segment_trichotomy[OF _ x(2)]
    by blast
qed

lemma no_two_\<omega>_limit_points:
  assumes transversal: "transversal_segment a b"
  assumes ex_pos: "{0..} \<subseteq> existence_ivl0 x"
  assumes u: "\<omega>_limit_point x u" "u \<in> {a<--<b}"
  assumes v: "\<omega>_limit_point x v" "v \<in> {a<--<b}"
  assumes uv: "v \<in> {u<--<b}"
  shows False
proof -
  have unotv: "u \<noteq> v" using uv
    using dist_in_open_segment by blast 
  define duv where "duv = dist u v / 2"
  have duv: "duv > 0" unfolding duv_def using unotv by simp
  from \<omega>_limit_crossings[OF transversal ex_pos u]
  obtain su where su: "filterlim su at_top sequentially"
    "(flow0 x \<circ> su) \<longlonglongrightarrow> u"
    "\<forall>\<^sub>F n in sequentially. flow0 x (su n) \<in> {a<--<b} \<and> su n \<in> existence_ivl0 x" by blast
  from \<omega>_limit_crossings[OF transversal ex_pos v]
  obtain sv where sv: "filterlim sv at_top sequentially"
    "(flow0 x \<circ> sv) \<longlonglongrightarrow> v"
    "\<forall>\<^sub>F n in sequentially. flow0 x (sv n) \<in> {a<--<b} \<and> sv n \<in> existence_ivl0 x" by blast
  from filterlim_at_top_tendstoE[OF duv su]
  obtain su1 where su1:"su1 > 0" "flow0 x su1 \<in> {a<--<b}"
    "su1 \<in> existence_ivl0 x" "dist (flow0 x su1) u < duv" by auto
  from filterlim_at_top_tendstoE[OF duv sv, of su1]
  obtain su2 where su2:"su2 > su1" "flow0 x su2 \<in> {a<--<b}"
    "su2 \<in> existence_ivl0 x" "dist (flow0 x su2) v < duv" by auto
  from filterlim_at_top_tendstoE[OF duv su, of su2]
  obtain su3 where su3:"su3 > su2" "flow0 x su3 \<in> {a<--<b}"
    "su3 \<in> existence_ivl0 x" "dist (flow0 x su3) u < duv" by auto
  have *: "su1 \<le> su2" "{su1..su2} \<subseteq> existence_ivl0 x" using su1 su2
     apply linarith
    by (metis atLeastatMost_empty_iff empty_iff mvar.closed_segment_subset_domain real_Icc_closed_segment su1(3) su2(3) subset_eq)

(* by construction *)
  have d1: "dist (flow0 x su1) v \<ge> (dist u v)/2" using su1(4) duv unfolding duv_def
    by (smt dist_triangle_half_r)
  have "dist (flow0 x su1) u < dist u v" using su1(4) duv unfolding duv_def by linarith
  from open_segment_separate_left[OF u(2) uv this su1(2)]
  have su1l:"flow0 x su1 \<in> {a<--<v}" .
  have "dist (flow0 x su2) v < dist v (flow0 x su1)" using d1
    by (smt dist_commute duv_def su2(4))
  from open_segment_separate_right[OF v(2) su1l this su2(2)]
  have su2l:"flow0 x su2 \<in> {flow0 x su1<--<b}" .
  then have su2ll:"flow0 x su2 \<in> {u<--<b}"
    by (smt dist_commute dist_pos_lt duv_def open_segment_subsegment pos_half_less open_segment_separate_right su2(2) su2(4) u(2) uv v(2) unotv)

  have "dist (flow0 x su2) u \<ge> (dist u v)/2" using su2(4) duv unfolding duv_def
    by (smt dist_triangle_half_r)
  then have "dist (flow0 x su3) u < dist u (flow0 x su2)"
    by (smt dist_commute duv_def su3(4)) 
  from open_segment_separate_left[OF u(2) su2ll this su3(2)]
  have su3l:"flow0 x su3 \<in> {a<--<flow0 x su2}" .

  from flow0_transversal_segment_monotone[OF transversal * su1(2) su2l su3(1) su3(3)]
  have "flow0 x su3 \<notin> {a <--<flow0 x su2}" .
  thus False using su3l by auto
qed


subsection \<open>Unique Intersection\<close>

text \<open>Perko Section 3.7 Remark 2\<close>
lemma unique_transversal_segment_intersection:
  assumes "transversal_segment a b"
  assumes "{0..} \<subseteq> existence_ivl0 x"
  assumes "u \<in> \<omega>_limit_set x \<inter> {a<--<b}"
  shows "\<omega>_limit_set x \<inter> {a<--<b} = {u}"
proof (rule ccontr)
  assume "\<omega>_limit_set x \<inter> {a<--<b} \<noteq> {u}"
  then
  obtain v where uv: "u \<noteq> v"
    and v: "\<omega>_limit_point x v" "v \<in> {a<--<b}" using assms unfolding \<omega>_limit_set_def
    by fastforce
  have u:"\<omega>_limit_point x u" "u \<in> {a<--<b}" using assms unfolding \<omega>_limit_set_def
    by auto
  show False using no_two_\<omega>_limit_points[OF \<open>transversal_segment a b\<close>]
    by (smt dist_commute dist_in_open_segment open_segment_trichotomy u uv v assms)
qed

text \<open>Adapted from Perko Section 3.7 Lemma 4 (+ Chicone )\<close>
lemma periodic_imp_\<omega>_limit_set:
  assumes "compact K" "K \<subseteq> X"
  assumes "x \<in> X" "trapped_forward x K"
  assumes "periodic_orbit y"
    "flow0 y ` UNIV \<subseteq> \<omega>_limit_set x"
  shows "flow0 y `UNIV = \<omega>_limit_set x"
proof (rule ccontr)
  note y = \<open>periodic_orbit y\<close> \<open>flow0 y ` UNIV \<subseteq> \<omega>_limit_set x\<close>
  from trapped_sol_right[OF assms(1-4)] 
  have ex_pos: "{0..} \<subseteq> existence_ivl0 x" by blast
  assume "flow0 y `UNIV \<noteq> \<omega>_limit_set x"
  obtain p where p: "p \<in> \<omega>_limit_set x" "p \<notin> flow0 y ` UNIV"
    using y(2) apply auto
    using \<open>range (flow0 y) \<noteq> \<omega>_limit_set x\<close> by blast
  from \<omega>_limit_set_in_compact_connected[OF assms(1-4)] have
    wcon: "connected (\<omega>_limit_set x)" .
  from \<omega>_limit_set_invariant have
    "invariant (\<omega>_limit_set x)" .
  from \<omega>_limit_set_in_compact_compact[OF assms(1-4)] have
    "compact (\<omega>_limit_set x)" .
  then have sc: "seq_compact (\<omega>_limit_set x)"
    using compact_imp_seq_compact by blast
  have y1:"closed (flow0 y ` UNIV)"
    using closed_orbit_\<omega>_limit_set periodic_orbit_def \<omega>_limit_set_closed y(1) by auto
  have y2: "flow0 y ` UNIV \<noteq> {}" by simp 
  let ?py = "infdist p (range (flow0 y))"
  have "0 < ?py"
    using y1 y2 p(2)
    by (rule infdist_pos_not_in_closed)
  have "\<forall>n::nat. \<exists>z. z \<in> \<omega>_limit_set x - flow0 y ` UNIV \<and>
    infdist z (flow0 y ` UNIV) < ?py/2^n"
  proof (rule ccontr)
    assume " \<not> (\<forall>n. \<exists>z. z \<in> \<omega>_limit_set x - range (flow0 y) \<and>
                infdist z (range (flow0 y))
                < infdist p (range (flow0 y)) / 2 ^ n) "
    then obtain n where n: "(\<forall>z \<in> \<omega>_limit_set x - range (flow0 y).
      infdist z (range (flow0 y)) \<ge> ?py / 2 ^ n)"
      using not_less by blast
    define A where "A = flow0 y ` UNIV"
    define B where "B = {z. infdist z (range (flow0 y)) \<ge> ?py / 2 ^ n}"
    have Ac:"closed A" unfolding A_def using y1 by auto
    have Bc:"closed B" unfolding B_def using infdist_closed by auto
    have "A \<inter> B = {}"
    proof (rule ccontr)
      assume "A \<inter> B \<noteq> {}"
      then obtain q where q: "q \<in> A" "q \<in> B" by blast
      have qz:"infdist q (range(flow0 y)) = 0" using q(1) unfolding A_def
        by simp
      note \<open>0 < ?py\<close>
      moreover have "2 ^ n > (0::real)" by auto
      ultimately have "infdist p (range (flow0 y)) / 2 ^ n > (0::real)"
        by simp
      then have qnz: "infdist q(range (flow0 y)) > 0" using q(2) unfolding B_def
        by auto
      show False using qz qnz by auto
    qed
    then have a1:"A \<inter> B \<inter> \<omega>_limit_set x = {}" by auto
    have "\<omega>_limit_set x - range(flow0 y) \<subseteq> B" using n B_def by blast
    then have a2:"\<omega>_limit_set x \<subseteq> A \<union> B" using A_def by auto
    from connected_closedD[OF wcon a1 a2 Ac Bc]
    have "A \<inter> \<omega>_limit_set x = {} \<or> B \<inter> \<omega>_limit_set x = {}" .
    moreover {
      assume "A \<inter> \<omega>_limit_set x = {}"
      then have False unfolding A_def using y(2) by blast
    }
    moreover {
      assume "B \<inter> \<omega>_limit_set x = {}"
      then have False unfolding B_def using p
        using A_def B_def a2 by blast
    }
    ultimately show False by blast
  qed
  then obtain s where s: "\<forall>n::nat. (s::nat \<Rightarrow> _) n \<in> \<omega>_limit_set x - flow0 y ` UNIV \<and>
                      infdist (s n) (flow0 y ` UNIV) < ?py/2^n"
    by metis
  then have "\<forall>n. s n \<in> \<omega>_limit_set x" by blast
  from seq_compactE[OF sc this]
  obtain l r where lr: "l \<in> \<omega>_limit_set x" "strict_mono r" "(s \<circ> r) \<longlonglongrightarrow> l" by blast
  have "\<And>n. infdist (s n) (range (flow0 y)) \<le> ?py / 2 ^ n" using s
    using less_eq_real_def by blast
  then have "\<And>n. norm(infdist (s n) (range (flow0 y))) \<le> ?py / 2 ^ n"
    by (auto simp add: infdist_nonneg)
  from LIMSEQ_norm_0_pow[OF \<open>0 < ?py\<close> _ this]
  have "((\<lambda>z. infdist z (flow0 y ` UNIV)) \<circ> s) \<longlonglongrightarrow> 0"
    by (auto simp add:o_def)
  from LIMSEQ_subseq_LIMSEQ[OF this lr(2)]
  have "((\<lambda>z. infdist z (flow0 y ` UNIV)) \<circ> (s \<circ> r)) \<longlonglongrightarrow> 0" by (simp add: o_assoc)
  moreover have "((\<lambda>z. infdist z (flow0 y ` UNIV)) \<circ> (s \<circ> r)) \<longlonglongrightarrow> infdist l (flow0 y ` UNIV)"
    by (auto intro!: tendsto_eq_intros tendsto_compose_at[OF lr(3)])
  ultimately have "infdist l (flow0 y `UNIV) = 0" using LIMSEQ_unique by auto
  then have lu: "l \<in> flow0 y ` UNIV" using in_closed_iff_infdist_zero[OF y1 y2] by auto
  then have l1:"l \<in> X"
    using closed_orbit_global_existence periodic_orbit_def y(1) by auto
      (* TODO: factor out as periodic_orbitE *)
  have l2:"f l \<noteq> 0"
    by (smt \<open>l \<in> X\<close> \<open>l \<in> range (flow0 y)\<close> closed_orbit_global_existence fixed_point_imp_closed_orbit_period_zero(2) fixpoint_sol(2) image_iff local.flows_reverse periodic_orbit_def y(1))
  from transversal_segment_exists[OF l1 l2]
  obtain a b where ab: "transversal_segment a b" "l \<in> {a<--<b}" by blast
  then have "l \<in> \<omega>_limit_set x \<inter> {a<--<b}" using lr by auto
  from unique_transversal_segment_intersection[OF ab(1) ex_pos this]
  have luniq: "\<omega>_limit_set x \<inter> {a<--<b} = {l} " .
  from cross_time_continuous[OF ab, of 1]
  obtain d t where dt: "0 < d"
    "(\<And>y. y \<in> ball l d \<Longrightarrow> flow0 y (t y) \<in> {a<--<b})"
    "(\<And>y. y \<in> ball l d \<Longrightarrow> \<bar>t y\<bar> < 1)"
    "continuous_on (ball l d) t" "t l = 0"
    by auto
  obtain n where "(s \<circ> r) n \<in> ball l d" using lr(3) dt(1) unfolding LIMSEQ_iff_nz
    by (metis dist_commute mem_ball order_refl)
  then have "flow0 ((s \<circ> r) n) (t ((s \<circ> r) n )) \<in> {a<--<b}" using dt by auto
  moreover have sr: "(s \<circ> r) n \<in> \<omega>_limit_set x" "(s \<circ> r) n \<notin> flow0 y ` UNIV"
    using s by auto
  moreover have "flow0 ((s \<circ> r) n) (t ((s \<circ> r) n )) \<in> \<omega>_limit_set x"
    using \<open>invariant (\<omega>_limit_set x)\<close> calculation unfolding invariant_def trapped_def
    by (smt \<omega>_limit_set_in_compact_subset \<open>invariant (\<omega>_limit_set x)\<close> assms(1-4) invariant_def order_trans range_eqI subsetD trapped_iff_on_existence_ivl0 trapped_sol)
  ultimately have "flow0 ((s \<circ> r) n) (t ((s \<circ> r) n )) \<in> \<omega>_limit_set x \<inter> {a<--<b}" by auto
  from unique_transversal_segment_intersection[OF ab(1) ex_pos this]
  have "flow0 ((s \<circ> r) n) (t ((s \<circ> r) n )) = l" using luniq by auto
  then have "((s \<circ> r) n) = flow0 l (-(t ((s \<circ> r) n ))) "
    by (smt UNIV_I \<open>(s \<circ> r) n \<in> \<omega>_limit_set x\<close> flows_reverse \<omega>_limit_set_in_compact_existence assms(1-4)) 
  thus False using sr(2) lu
      \<open>flow0 ((s \<circ> r) n) (t ((s \<circ> r) n)) = l\<close> \<open>flow0 ((s \<circ> r) n) (t ((s \<circ> r) n)) \<in> \<omega>_limit_set x\<close>
      closed_orbit_global_existence image_iff local.flow_trans periodic_orbit_def \<omega>_limit_set_in_compact_existence range_eqI assms y(1)
    by smt
qed

end context c1_on_open_R2 begin

lemma \<alpha>_limit_crossings:
  assumes "transversal_segment a b"
  assumes pos_ex: "{..0} \<subseteq> existence_ivl0 x"
  assumes "\<alpha>_limit_point x p"
  assumes "p \<in> {a<--<b}"
  obtains s where
    "s \<longlonglongrightarrow>\<^bsub>\<^esub> -\<infinity>"
    "(flow0 x \<circ> s) \<longlonglongrightarrow> p"
    "\<forall>\<^sub>F n in sequentially.
    flow0 x (s n) \<in> {a<--<b} \<and>
    s n \<in> existence_ivl0 x"
proof -
  from pos_ex have "{0..} \<subseteq> uminus ` existence_ivl0 x" by force
  from rev.\<omega>_limit_crossings[unfolded rev_transversal_segment rev_existence_ivl_eq0 rev_eq_flow
      \<alpha>_limit_point_eq_rev[symmetric], OF assms(1) this assms(3,4)]
  obtain s where "filterlim s at_top sequentially" "((\<lambda>t. flow0 x (- t)) \<circ> s) \<longlonglongrightarrow> p"
    "\<forall>\<^sub>F n in sequentially. flow0 x (- s n) \<in> {a<--<b} \<and> s n \<in> uminus ` existence_ivl0 x" .
  then have "filterlim (-s) at_bot sequentially"
    "(flow0 x \<circ> (-s)) \<longlonglongrightarrow> p"
    "\<forall>\<^sub>F n in sequentially. flow0 x ((-s) n) \<in> {a<--<b} \<and> (-s) n \<in> existence_ivl0 x"
    by (auto simp: fun_Compl_def o_def filterlim_uminus_at_top)
  then show ?thesis ..
qed

text \<open>If a positive limit point has a regular point in its positive limit set then it is periodic\<close>
lemma \<omega>_limit_point_\<omega>_limit_set_regular_imp_periodic:
  assumes "compact K" "K \<subseteq> X"
  assumes "x \<in> X" "trapped_forward x K"
  assumes y: "y \<in> \<omega>_limit_set x" "f y \<noteq> 0"
  assumes z: "z \<in> \<omega>_limit_set y \<union> \<alpha>_limit_set y" "f z \<noteq> 0"
  shows "periodic_orbit y \<and> flow0 y ` UNIV = \<omega>_limit_set x"
proof -
  from trapped_sol_right[OF assms(1-4)] have ex_pos: "{0..} \<subseteq> existence_ivl0 x" by blast
  from \<omega>_limit_set_in_compact_existence[OF assms(1-4) y(1)]
  have yex: "existence_ivl0 y = UNIV" .
  from \<omega>_limit_set_invariant
  have "invariant (\<omega>_limit_set x)" .
  then have yinv: "flow0 y ` UNIV \<subseteq> \<omega>_limit_set x" using yex unfolding invariant_def
    using trapped_iff_on_existence_ivl0 y(1) by blast 

  have zy: "\<omega>_limit_point y z \<or> \<alpha>_limit_point y z"
    using z unfolding \<omega>_limit_set_def \<alpha>_limit_set_def by auto

  from \<omega>_limit_set_in_compact_\<omega>_limit_set_contained[OF assms(1-4)]
    \<omega>_limit_set_in_compact_\<alpha>_limit_set_contained[OF assms(1-4)]
  have zx:"z \<in> \<omega>_limit_set x" using zy y
    using z(1) by blast
  then have "z \<in> X"
    by (metis UNIV_I local.existence_ivl_initial_time_iff \<omega>_limit_set_in_compact_existence assms(1-4))
  from transversal_segment_exists[OF this z(2)]
  obtain a b where ab: "transversal_segment a b" "z \<in> {a<--<b}" by blast

  from zy
  obtain t1 t2 where t1: "flow0 y t1 \<in> {a<--<b}" and t2: "flow0 y t2 \<in> {a<--<b}" and "t1 \<noteq> t2"
  proof
    assume zy: "\<omega>_limit_point y z"
    from \<omega>_limit_crossings[OF ab(1) _ zy ab(2), unfolded yex]
    obtain s where s: "filterlim s at_top sequentially"
      "(flow0 y \<circ> s) \<longlonglongrightarrow> z"
      "\<forall>\<^sub>F n in sequentially. flow0 y (s n) \<in> {a<--<b}"
      by auto
    from eventually_happens[OF this(3)] obtain t1 where t1: "flow0 y t1 \<in> {a<--<b}" by auto
    have "\<forall>\<^sub>F n in sequentially. s n > t1"
      using filterlim_at_top_dense s(1) by auto
    with s(3) have "\<forall>\<^sub>F n in sequentially. flow0 y (s n) \<in> {a<--<b} \<and> s n > t1"
      by eventually_elim simp
    from eventually_happens[OF this] obtain t2 where t2: "flow0 y t2 \<in> {a<--<b}" and "t1 \<noteq> t2"
      by auto
    from t1 this show ?thesis ..
  next
    assume zy: "\<alpha>_limit_point y z"
    from \<alpha>_limit_crossings[OF ab(1) _ zy ab(2), unfolded yex]
    obtain s where s: "filterlim s at_bot sequentially"
      "(flow0 y \<circ> s) \<longlonglongrightarrow> z"
      "\<forall>\<^sub>F n in sequentially. flow0 y (s n) \<in> {a<--<b}"
      by auto
    from eventually_happens[OF this(3)] obtain t1 where t1: "flow0 y t1 \<in> {a<--<b}" by auto
    have "\<forall>\<^sub>F n in sequentially. s n < t1"
      using filterlim_at_bot_dense s(1) by auto
    with s(3) have "\<forall>\<^sub>F n in sequentially. flow0 y (s n) \<in> {a<--<b} \<and> s n < t1"
      by eventually_elim simp
    from eventually_happens[OF this] obtain t2 where t2: "flow0 y t2 \<in> {a<--<b}" and "t1 \<noteq> t2"
      by auto
    from t1 this show ?thesis ..
  qed
  have "flow0 y t1 \<in> \<omega>_limit_set x \<inter> {a<--<b}" using t1 UNIV_I yinv by auto
  moreover have "flow0 y t2 \<in> \<omega>_limit_set x \<inter> {a<--<b}" using t2 UNIV_I yinv by auto
  ultimately have feq:"flow0 y t1 = flow0 y t2"
    using unique_transversal_segment_intersection[OF \<open>transversal_segment a b\<close> ex_pos]
    by blast
  have "t1 \<noteq> t2" "t1 \<in> existence_ivl0 y" "t2 \<in> existence_ivl0 y" using \<open>t1 \<noteq>  t2\<close>
      apply blast
     apply (simp add: yex)
    by (simp add: yex)
  from periodic_orbitI[OF this feq y(2)]
  have 1: "periodic_orbit y" .
  from periodic_imp_\<omega>_limit_set[OF assms(1-4) this yinv]
  have 2: "flow0 y` UNIV = \<omega>_limit_set x" .
  show ?thesis using 1 2 by auto
qed

subsection \<open>Poincare Bendixson Theorems\<close>
text \<open>Perko Section 3.7 Theorem 1\<close>
theorem poincare_bendixson:
  assumes "compact K" "K \<subseteq> X"
  assumes "x \<in> X" "trapped_forward x K"
  assumes "0 \<notin> f ` (\<omega>_limit_set x)"
  obtains y where "periodic_orbit y"
    "flow0 y ` UNIV = \<omega>_limit_set x"
proof -
  note f = \<open>0 \<notin> f ` (\<omega>_limit_set x)\<close>
  from \<omega>_limit_set_in_compact_nonempty[OF assms(1-4)]
  obtain y where y: "y \<in> \<omega>_limit_set x" by fastforce
  from \<omega>_limit_set_in_compact_existence[OF  assms(1-4) y]
  have yex: "existence_ivl0 y = UNIV" .
  from \<omega>_limit_set_invariant
  have "invariant (\<omega>_limit_set x)" .
  then have yinv: "flow0 y ` UNIV \<subseteq> \<omega>_limit_set x" using yex unfolding invariant_def
    using trapped_iff_on_existence_ivl0 y by blast
  from \<omega>_limit_set_in_compact_subset[OF assms(1-4)]
  have "\<omega>_limit_set x \<subseteq> K" .
  then have "flow0 y ` UNIV \<subseteq> K" using yinv by auto
  then have yk:"trapped_forward y K"
    by (simp add: image_subsetI range_subsetD trapped_forward_def)
  have "y \<in> X"
    by (simp add: local.mem_existence_ivl_iv_defined(2) yex)

  from \<omega>_limit_set_in_compact_nonempty[OF assms(1-2) this _]
  obtain z where z: "z \<in> \<omega>_limit_set y" using yk by blast
  from \<omega>_limit_set_in_compact_\<omega>_limit_set_contained[OF assms(1-4)]
  have zx:"z \<in> \<omega>_limit_set x" using \<open>z \<in> \<omega>_limit_set y\<close> y by auto

  have yreg : "f y \<noteq> 0" using f y
    by (metis rev_image_eqI)
  have zreg : "f z \<noteq> 0" using f zx
    by (metis rev_image_eqI) 
  from \<omega>_limit_point_\<omega>_limit_set_regular_imp_periodic[OF assms(1-4) y yreg _ zreg] z
  show ?thesis using that by blast
qed

lemma fixed_point_in_\<omega>_limit_set_imp_\<omega>_limit_set_singleton_fixed_point:
  assumes "compact K" "K \<subseteq> X"
  assumes "x \<in> X" "trapped_forward x K"
  assumes fp: "yfp \<in> \<omega>_limit_set x" "f yfp = 0"
  assumes zpx: "z \<in> \<omega>_limit_set x"
  assumes finite_fp: "finite {y \<in> K. f y = 0}" (is "finite ?S")
  shows "(\<exists>p1 \<in> \<omega>_limit_set x. f p1 = 0 \<and> \<omega>_limit_set z = {p1}) \<and>
    (\<exists>p2 \<in> \<omega>_limit_set x. f p2 = 0 \<and> \<alpha>_limit_set z = {p2})"
proof -
  let ?weq = "{y \<in> \<omega>_limit_set x. f y = 0}"
  from \<omega>_limit_set_in_compact_subset[OF assms(1-4)]
  have wxK: "\<omega>_limit_set x \<subseteq> K" .
  from \<omega>_limit_set_in_compact_\<omega>_limit_set_contained[OF assms(1-4)]
  have zx: "\<omega>_limit_set z \<subseteq> \<omega>_limit_set x" using zpx by auto
  have zX: "z \<in> X" using subset_trans[OF wxK assms(2)]
    by (metis subset_iff zpx)
  from \<omega>_limit_set_in_compact_subset[OF assms(1-4)]
  have "?weq \<subseteq> ?S"
    by (smt Collect_mono_iff Int_iff inf.absorb_iff1)
  then have "finite ?weq" using \<open>finite ?S\<close>
    by (blast intro: rev_finite_subset) 

  consider "f z = 0" | "f z \<noteq> 0" by auto
  then show ?thesis
  proof cases
    assume "f z = 0"
    from fixed_point_imp_\<omega>_limit_set[OF zX this]
      fixed_point_imp_\<alpha>_limit_set[OF zX this]
    show ?thesis
      by (metis (mono_tags) \<open>f z = 0\<close> zpx)
  next
    assume "f z \<noteq> 0"
    have zweq: "\<omega>_limit_set z \<subseteq> ?weq"
      apply clarsimp
    proof (rule ccontr)
      fix k assume k: "k \<in> \<omega>_limit_set z" "\<not> (k \<in> \<omega>_limit_set x \<and> f k = 0)"
      then have "f k \<noteq> 0" using zx k by auto
      from \<omega>_limit_point_\<omega>_limit_set_regular_imp_periodic[OF assms(1-4) zpx \<open>f z \<noteq> 0\<close> _ this] k(1)
      have "periodic_orbit z" "range(flow0 z) = \<omega>_limit_set x" by auto
      then have "0 \<notin> f ` (\<omega>_limit_set x)"
        by (metis image_iff periodic_orbit_imp_flow0_regular)
      thus False using fp
        by (metis (mono_tags, lifting) empty_Collect_eq image_eqI)
    qed
    have zweq0: "\<alpha>_limit_set z \<subseteq> ?weq"
      apply clarsimp
    proof (rule ccontr)
      fix k assume k: "k \<in> \<alpha>_limit_set z" "\<not> (k \<in> \<omega>_limit_set x \<and> f k = 0)"
      then have "f k \<noteq> 0" using zx k
          \<omega>_limit_set_in_compact_\<alpha>_limit_set_contained[OF assms(1-4), of z] zpx
        by auto
      from \<omega>_limit_point_\<omega>_limit_set_regular_imp_periodic[OF assms(1-4) zpx \<open>f z \<noteq> 0\<close> _ this] k(1)
      have "periodic_orbit z" "range(flow0 z) = \<omega>_limit_set x" by auto
      then have "0 \<notin> f ` (\<omega>_limit_set x)"
        by (metis image_iff periodic_orbit_imp_flow0_regular)
      thus False using fp
        by (metis (mono_tags, lifting) empty_Collect_eq image_eqI)
    qed
    from \<omega>_limit_set_in_compact_existence[OF assms(1-4) zpx]
    have zex: "existence_ivl0 z = UNIV" .
    from \<omega>_limit_set_invariant
    have "invariant (\<omega>_limit_set x)" .
    then have zinv: "flow0 z ` UNIV \<subseteq> \<omega>_limit_set x" using zex unfolding invariant_def
      using trapped_iff_on_existence_ivl0 zpx by blast
    then have "flow0 z ` UNIV \<subseteq> K" using wxK by auto
    then have a2: "trapped_forward z K" "trapped_backward z K"
      using trapped_def trapped_iff_on_existence_ivl0 apply fastforce
      using \<open>range (flow0 z) \<subseteq> K\<close> trapped_def trapped_iff_on_existence_ivl0 by blast
    have a3: "finite (\<omega>_limit_set z)"
      by (metis \<open>finite ?weq\<close> finite_subset zweq)
    from finite_\<omega>_limit_set_in_compact_imp_unique_fixed_point[OF assms(1-2) zX a2(1) a3]
    obtain p1 where p1: "\<omega>_limit_set z = {p1}" "f p1 = 0" by blast
    then have "p1 \<in> ?weq" using zweq by blast
    moreover
    have "finite (\<alpha>_limit_set z)"
      by (metis \<open>finite ?weq\<close> finite_subset zweq0)
    from finite_\<alpha>_limit_set_in_compact_imp_unique_fixed_point[OF assms(1-2) zX a2(2) this]
    obtain p2 where p2: "\<alpha>_limit_set z = {p2}" "f p2 = 0" by blast
    then have "p2 \<in> ?weq" using zweq0 by blast
    ultimately show ?thesis
      by (simp add: p1 p2)
  qed
qed

end context c1_on_open_R2 begin

text \<open>Perko Section 3.7 Theorem 2\<close>
theorem poincare_bendixson_general:
  assumes "compact K" "K \<subseteq> X"
  assumes "x \<in> X" "trapped_forward x K"
  assumes "S = {y \<in> K. f y = 0}" "finite S"
  shows
    "(\<exists>y \<in> S. \<omega>_limit_set x = {y}) \<or>
  (\<exists>y. periodic_orbit y \<and>
    flow0 y ` UNIV = \<omega>_limit_set x) \<or>
  (\<exists>P R. \<omega>_limit_set x = P \<union> R \<and>
    P \<subseteq> S \<and> 0 \<notin> f ` R \<and> R \<noteq> {} \<and>
    (\<forall>z \<in> R.
      (\<exists>p1 \<in> P. \<omega>_limit_set z = {p1}) \<and>
      (\<exists>p2 \<in> P. \<alpha>_limit_set z = {p2})))"
proof -
  note S = \<open>S = {y \<in> K. f y = 0}\<close>
  let ?wreg = "{y \<in> \<omega>_limit_set x. f y \<noteq> 0}"
  let ?weq = "{y \<in> \<omega>_limit_set x. f y = 0}"
  have wreqweq: "?wreg \<union> ?weq = \<omega>_limit_set x"
    by (smt Collect_cong Collect_disj_eq mem_Collect_eq \<omega>_limit_set_def)

  from trapped_sol_right[OF assms(1-4)] have ex_pos: "{0..} \<subseteq> existence_ivl0 x" by blast
  from \<omega>_limit_set_in_compact_subset[OF assms(1-4)]
  have wxK: "\<omega>_limit_set x \<subseteq> K" .
  then have "?weq \<subseteq> S" using S
    by (smt Collect_mono_iff Int_iff inf.absorb_iff1)
  then have "finite ?weq" using \<open>finite S\<close>
    by (metis rev_finite_subset) 
  from \<omega>_limit_set_invariant
  have xinv: "invariant (\<omega>_limit_set x)" .

  from \<omega>_limit_set_in_compact_nonempty[OF assms(1-4)] wreqweq
  consider "?wreg = {}" |
    "?weq = {}" |
    "?weq \<noteq> {}" "?wreg \<noteq> {}" by auto
  then show ?thesis
  proof cases
    (* If w has no regular points then it is equal to a single unique fixed point *)
    assume "?wreg = {}"
    then have "finite (\<omega>_limit_set x)"
      by (metis (mono_tags, lifting) \<open>{y \<in> \<omega>_limit_set x. f y = 0} \<subseteq> S\<close> \<open>finite S\<close> rev_finite_subset sup_bot.left_neutral wreqweq)
    from finite_\<omega>_limit_set_in_compact_imp_unique_fixed_point[OF assms(1-4) this]
    obtain y where y: "\<omega>_limit_set x = {y}" "f y = 0" by blast
    then have "y \<in> S"
      by (metis Un_empty_left \<open>?weq \<subseteq> S\<close> \<open>?wreg = {}\<close> insert_subset wreqweq)
    then show ?thesis using y by auto
  next
    (* If w has no fixed points, then the Poincare Bendixson theorem applies *)
    assume "?weq = {}"
    then have " 0 \<notin> f ` \<omega>_limit_set x"
      by (smt empty_Collect_eq imageE)
    from poincare_bendixson[OF assms(1-4) this]
    have "(\<exists>y. periodic_orbit y \<and> flow0 y ` UNIV = \<omega>_limit_set x)"
      by metis
    then show ?thesis by blast
  next
    (* Otherwise, all points in the limit set converge to a finite subset of the fixed points *)
    assume "?weq \<noteq> {}" "?wreg \<noteq> {}"
    then obtain yfp where yfp: "yfp \<in> \<omega>_limit_set x" "f yfp = 0" by auto
    have "0 \<notin> f ` ?wreg" by auto
    have "(\<exists>p1\<in>\<omega>_limit_set x. f p1 = 0 \<and> \<omega>_limit_set z = {p1}) \<and>
      (\<exists>p2\<in>\<omega>_limit_set x. f p2 = 0 \<and> \<alpha>_limit_set z = {p2})"
      if zpx: "z \<in> \<omega>_limit_set x" for z
      using fixed_point_in_\<omega>_limit_set_imp_\<omega>_limit_set_singleton_fixed_point[
          OF assms(1-4) yfp zpx \<open>finite S\<close>[unfolded S]] by auto
    then have "\<omega>_limit_set x = ?weq \<union> ?wreg \<and>
        ?weq \<subseteq> S \<and> 0 \<notin> f ` ?wreg \<and> ?wreg \<noteq> {} \<and>
        (\<forall>z \<in> ?wreg.
         (\<exists>p1 \<in> ?weq. \<omega>_limit_set z = {p1}) \<and>
         (\<exists>p2 \<in> ?weq. \<alpha>_limit_set z = {p2}))"
      using wreqweq \<open>?weq \<subseteq> S\<close> \<open>?wreg \<noteq> {}\<close> \<open>0 \<notin> f ` ?wreg\<close>
      by blast
    then show ?thesis by blast
  qed
qed

corollary poincare_bendixson_applied:
  assumes "compact K" "K \<subseteq> X"
  assumes "K \<noteq> {}" "positively_invariant K"
  assumes "0 \<notin> f ` K"
  obtains y where "periodic_orbit y" "flow0 y ` UNIV \<subseteq> K"
proof -
  from assms(1-4) obtain x where "x \<in> K" "x \<in> X" by auto
  have *: "trapped_forward x K"
    using assms(4) \<open>x \<in> K\<close>
    by (auto simp: positively_invariant_def)
  have subs: "\<omega>_limit_set x \<subseteq> K"
    by (rule \<omega>_limit_set_in_compact_subset[OF assms(1-2) \<open>x \<in> X\<close> *])
  with assms(5) have "0 \<notin> f ` \<omega>_limit_set x" by auto
  from poincare_bendixson[OF assms(1-2) \<open>x \<in> X\<close> * this]
  obtain y where "periodic_orbit y" "range (flow0 y) = \<omega>_limit_set x"
    by force
  then have "periodic_orbit y" "flow0 y ` UNIV \<subseteq> K" using subs by auto
  then show ?thesis ..
qed

(*
  Limit cycles are periodic orbits that is the \<omega> (or \<alpha>)-limit set of some point not in the cycle.
  As with periodic_orbit, limit_cycles are defined for a representative point y
*)
definition "limit_cycle y \<longleftrightarrow>
  periodic_orbit y \<and>
  (\<exists>x. x \<notin> flow0 y ` UNIV \<and>
  (flow0 y ` UNIV = \<omega>_limit_set x \<or> flow0 y ` UNIV = \<alpha>_limit_set x))"

corollary poincare_bendixson_limit_cycle:
  assumes "compact K" "K \<subseteq> X"
  assumes "x \<in> K" "positively_invariant K"
  assumes "0 \<notin> f ` K"
  assumes "rev.flow0 x t \<notin> K"
  obtains y where "limit_cycle y" "flow0 y ` UNIV \<subseteq> K"
proof -
  have "x \<in> X" using assms(2-3) by blast
  have *: "trapped_forward x K"
    using assms(3-4)
    by (auto simp: positively_invariant_def)
  have subs: "\<omega>_limit_set x \<subseteq> K"
    by (rule \<omega>_limit_set_in_compact_subset[OF assms(1-2) \<open>x \<in> X\<close> *])
  with assms(5) have "0 \<notin> f ` \<omega>_limit_set x" by auto
  from poincare_bendixson[OF assms(1-2) \<open>x \<in> X\<close> * this]
  obtain y where y: "periodic_orbit y" "range (flow0 y) = \<omega>_limit_set x"
    by force
  then have c2: "flow0 y ` UNIV \<subseteq> K" using subs by auto
  have exy: "existence_ivl0 y = UNIV"
    using closed_orbit_global_existence periodic_orbit_def y(1) by blast
  have "x \<notin> flow0 y ` UNIV"
  proof clarsimp
    fix tt
    assume "x = flow0 y tt"
    then have "rev.flow0 (flow0 y tt) t \<notin> K" using assms(6) by auto
    moreover have "rev.flow0 (flow0 y tt) t \<in> flow0 y ` UNIV" using exy unfolding rev_eq_flow
      using UNIV_I \<open>x = flow0 y tt\<close> closed_orbit_\<omega>_limit_set closed_orbit_flow0 periodic_orbit_def y by auto
    ultimately show False using c2 by blast
  qed
  then have "limit_cycle y" "flow0 y ` UNIV \<subseteq> K" using y c2 unfolding limit_cycle_def by auto
  then show ?thesis ..
qed

end

end
