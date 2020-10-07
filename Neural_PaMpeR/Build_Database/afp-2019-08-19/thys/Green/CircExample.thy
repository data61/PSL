section \<open>The Circle Example\<close>

theory CircExample
  imports Green SymmetricR2Shapes

begin

locale circle = R2 +
  fixes d::real
  assumes d_gt_0: "0 < d"
begin

definition circle_y where
  "circle_y t = sqrt (1/4 - t * t)"

definition circle_cube where
  "circle_cube = (\<lambda>(x,y). ((x - 1/2) * d, (2 * y - 1) * d * sqrt (1/4 - (x -1/2)*(x -1/2))))"

lemma circle_cube_nice:
  shows "circle_cube = (\<lambda>(x,y). (d * x_coord x, (2 * y - 1) * d * circle_y (x_coord x)))"
  by (auto simp add: circle_cube_def circle_y_def x_coord_def)

definition rot_circle_cube where
  "rot_circle_cube = prod.swap \<circ> (circle_cube) \<circ> prod.swap"

abbreviation "rot_y t1 t2 \<equiv> ((t1-1/2)/(2* circle_y (x_coord (rot_x t1 t2))) +1/2::real)"

definition "x_coord_inv (x::real) = (1/2) + x"

lemma x_coord_inv_1: "x_coord_inv (x_coord (x::real)) = x" 
  by (auto simp add: x_coord_inv_def x_coord_def)

lemma x_coord_inv_2: "x_coord (x_coord_inv (x::real)) = x" 
  by (auto simp add: x_coord_inv_def x_coord_def)

definition "circle_y_inv = circle_y"

abbreviation "rot_x'' (x::real) (y::real) \<equiv> (x_coord_inv ((2 * y - 1) * circle_y (x_coord x)))"

lemma circle_y_bounds:
  assumes "-1/2 \<le> (x::real) \<and> x \<le> 1/2"
  shows "0 \<le> circle_y x" "circle_y x \<le> 1/2"
  unfolding circle_y_def real_sqrt_ge_0_iff
proof -
  show "0 \<le> 1/4 - x * x"
    using assms by (sos "(((A<0 * R<1) + ((A<=0 * (A<=1 * R<1)) * (R<1 * [1]^2))))")
  show "sqrt (1/4 - x * x) \<le> 1/2"
    apply (rule real_le_lsqrt)
    using assms apply(auto simp add: divide_simps algebra_simps)
    by (sos "(((A<0 * R<1) + ((A<=0 * (A<=1 * R<1)) * (R<1 * [1]^2))))")
qed

lemma circle_y_x_coord_bounds:
  assumes "0 \<le> (x::real)" "x \<le> 1"
  shows "0 \<le> circle_y (x_coord x) \<and> circle_y (x_coord x) \<le> 1/2"
  using circle_y_bounds[OF x_coord_bounds[OF assms]] by auto

lemma rot_x_ivl:
  assumes "(0::real) \<le> x" "x \<le> 1"  "0 \<le> y" "y \<le> 1" 
  shows "0 \<le> rot_x'' x y \<and> rot_x'' x y \<le> 1"
proof
  have "\<And>a::real. 0 \<le> a \<and> a \<le> 1/2 \<Longrightarrow> 0 \<le> 1/2 + (2 * y - 1) * a" using assms
    by (sos "(((A<0 * R<1) + (((A<=4 * R<1) * (R<1/2 * [1]^2)) + (((A<=1 * (A<=5 * R<1)) * (R<1 * [1]^2)) + ((A<=0 * (A<=4 * R<1)) * (R<1 * [1]^2))))))")
  then show "0 \<le> rot_x'' x y"
    using assms circle_y_x_coord_bounds by(auto simp add: x_coord_inv_def)
  have "\<And>a::real. 0 \<le> a \<and> a \<le> 1/2 \<Longrightarrow> 1/2 + (2 * y - 1) * a \<le> 1" using assms
    by (sos "(((A<0 * R<1) + (((A<=5 * R<1) * (R<1/2 * [1]^2)) + (((A<=1 * (A<=4 * R<1)) * (R<1 * [1]^2)) + ((A<=0 * (A<=5 * R<1)) * (R<1 * [1]^2))))))")
  then show "rot_x'' x y \<le> 1"
    using assms circle_y_x_coord_bounds by (auto simp add: x_coord_inv_def)
qed

abbreviation "rot_y'' (x::real) (y::real) \<equiv> (x_coord x)/(2* (circle_y (x_coord (rot_x'' x y))))  + 1/2" 

lemma rot_y_ivl:
  assumes "(0::real) \<le> x" "x \<le> 1" "0 \<le> y" "y \<le> 1" 
  shows "0 \<le> rot_y'' x y \<and> rot_y'' x y \<le> 1"
proof
  show "0 \<le> rot_y'' x y"
  proof(cases "(x_coord x) < 0")
    case True
    have i: "\<And>a b::real. a < 0 \<Longrightarrow> 0 \<le> a + b \<Longrightarrow> (0 \<le> a/(2*(b)) + 1/2)"
      by(auto simp add: algebra_simps divide_simps) 
    have *: "(1/2 - x) \<le> sqrt (x * x + (1/4 + (x * (y * 4) + x * (x * (y * (y * 4))))) - (x + (x * (x * (y * 4)) + x * (y * (y * 4)))))"
      apply (rule real_le_rsqrt)
      using assms apply (simp add: algebra_simps power2_eq_square mult_left_le_one_le)
      by (sos "(((A<0 * R<1) + ((A<=0 * (A<=1 * (A<=2 * (A<=3 * R<1)))) * (R<4 * [1]^2))))")
    have rw: "\<bar>x - x * x\<bar> = x - x * x" using assms
      by (sos "(() & (((((A<0 * A<1) * R<1) + ((A<=0 * (A<=1 * (A<1 * R<1))) * (R<1 * [1]^2)))) & ((((A<0 * A<1) * R<1) + ((A<=0 * (A<=1 * (A<1 * R<1))) * (R<1 * [1]^2))))))")
    have "0 \<le> x_coord x + (circle_y (x_coord (rot_x'' x y)))"
      using * apply (auto simp add: x_coord_inv_2)
      by (auto simp add: circle_y_def algebra_simps rw x_coord_def)
    then show ?thesis
      using True i by blast
  next
    case False
    have i: "\<And>a b::real. 0 \<le> a \<Longrightarrow> 0 \<le> b  \<Longrightarrow> (0 \<le> a/(2*b) + 1/2)"
      by(auto simp add: algebra_simps divide_simps)
    have "0 \<le> circle_y (x_coord (x_coord_inv ((2 * y - 1) * circle_y (x_coord x))))"
    proof -
      have rw: "\<bar>x - x * x\<bar> = x - x * x" using assms
        by (sos "(() & (((((A<0 * A<1) * R<1) + ((A<=0 * (A<=1 * (A<1 * R<1))) * (R<1 * [1]^2)))) & ((((A<0 * A<1) * R<1) + ((A<=0 * (A<=1 * (A<1 * R<1))) * (R<1 * [1]^2))))))")
      have "\<And>x. 0 \<le> x \<Longrightarrow> x \<le> 1/2 \<Longrightarrow> -1/2\<le> (2 * y - 1) * x" using assms
        by (sos "(((A<0 * R<1) + (((A<=4 * R<1) * (R<1/2 * [1]^2)) + (((A<=1 * (A<=5 * R<1)) * (R<1 * [1]^2)) + ((A<=0 * (A<=4 * R<1)) * (R<1 * [1]^2))))))")
      then have "- 1/2 \<le> (2 * y - 1) * circle_y (x_coord x)"
        using circle_y_x_coord_bounds assms(1-2) by auto
      moreover
      have "\<And>x. 0 \<le> x \<Longrightarrow> x \<le> 1/2 \<Longrightarrow> (2 * y - 1) * x \<le> 1/2 " using assms
        by (sos "(((A<0 * R<1) + (((A<=5 * R<1) * (R<1/2 * [1]^2)) + (((A<=1 * (A<=4 * R<1)) * (R<1 * [1]^2)) + ((A<=0 * (A<=5 * R<1)) * (R<1 * [1]^2))))))")
      then have "(2 * y - 1) * circle_y (x_coord x) \<le> 1/2"
        using circle_y_x_coord_bounds assms(1-2) by auto
      ultimately show "0 \<le> circle_y (x_coord (x_coord_inv ((2 * y - 1) * circle_y (x_coord x))))"
        by (simp add: circle_y_bounds(1) x_coord_inv_2)
    qed
    then show ?thesis
      using False by auto
  qed
  have i: "\<And>a b::real. a < 0 \<Longrightarrow> 0 \<le> b \<Longrightarrow> (a/(2*(b)) + 1/2) \<le> 1"
    by(auto simp add: algebra_simps divide_simps) 
  show "rot_y'' x y \<le> 1"
  proof(cases "(x_coord x) < 0")
    case True
    have i: "\<And>a b::real. a < 0 \<Longrightarrow> 0 \<le> b \<Longrightarrow> (a/(2*(b)) + 1/2) \<le> 1"
      by(auto simp add: algebra_simps divide_simps) 
    have "\<And>x. 0 \<le> x \<Longrightarrow> x \<le> 1/2 \<Longrightarrow> -1/2\<le> (2 * y - 1) * x" using assms
      by (sos "(((A<0 * R<1) + (((A<=4 * R<1) * (R<1/2 * [1]^2)) + (((A<=1 * (A<=5 * R<1)) * (R<1 * [1]^2)) + ((A<=0 * (A<=4 * R<1)) * (R<1 * [1]^2))))))")
    then have "- 1/2 \<le> (2 * y - 1) * circle_y (x_coord x)"
      using circle_y_x_coord_bounds assms(1-2) by auto
    moreover have "\<And>x. 0 \<le> x \<Longrightarrow> x \<le> 1/2 \<Longrightarrow> (2 * y - 1) * x \<le> 1/2 " using assms
      by (sos "(((A<0 * R<1) + (((A<=5 * R<1) * (R<1/2 * [1]^2)) + (((A<=1 * (A<=4 * R<1)) * (R<1 * [1]^2)) + ((A<=0 * (A<=5 * R<1)) * (R<1 * [1]^2))))))")
    then have "(2 * y - 1) * circle_y (x_coord x) \<le> 1/2"
      using circle_y_x_coord_bounds assms(1-2) by auto
    ultimately have "0 \<le> circle_y (x_coord (x_coord_inv ((2 * y - 1) * circle_y (x_coord x))))"
      by (simp add: circle_y_bounds(1) x_coord_inv_2)
    then show ?thesis
      by (simp add: True i)
  next
    case False
    have i: "\<And>a b::real. 0 \<le> a \<Longrightarrow> a \<le> b  \<Longrightarrow> (a/(2*b) + 1/2) \<le> 1"
      by(auto simp add: algebra_simps divide_simps)
    have "(x - 1/2) * (x - 1/2) \<le> (x * x + (1/4 + (x * (y * 4) + x * (x * (y * (y * 4))))) - (x + (x * (x * (y * 4)) + x * (y * (y * 4)))))"
      using assms False 
      apply(auto simp add: x_coord_def)
      by (sos "(((A<0 * R<1) + (((A<=0 * (A<=1 * (A<=2 * R<1))) * (R<2 * [1]^2)) + ((A<=0 * (A<=1 * (A<=2 * (A<=3 * R<1)))) * (R<2 * [1]^2)))))")
    then have "sqrt ((x - 1/2) * (x - 1/2)) \<le> sqrt (x * x + (1/4 + (x * (y * 4) + x * (x * (y * (y * 4))))) - (x + (x * (x * (y * 4)) + x * (y * (y * 4)))))"
      using real_sqrt_le_mono by blast
    then have *: "(x - 1/2) \<le> sqrt (x * x + (1/4 + (x * (y * 4) + x * (x * (y * (y * 4))))) - (x + (x * (x * (y * 4)) + x * (y * (y * 4)))))"
      using assms False by(auto simp add: x_coord_def)
    have rw: "\<bar>x - x * x\<bar> = x - x * x" using assms
      by (sos "(() & (((((A<0 * A<1) * R<1) + ((A<=0 * (A<=1 * (A<1 * R<1))) * (R<1 * [1]^2)))) & ((((A<0 * A<1) * R<1) + ((A<=0 * (A<=1 * (A<1 * R<1))) * (R<1 * [1]^2))))))")
    have "x_coord x \<le> circle_y (x_coord (x_coord_inv ((2 * y - 1) * circle_y (x_coord x))))"
      using * unfolding x_coord_inv_2
      by (auto simp add: circle_y_def algebra_simps rw x_coord_def)
    then show ?thesis
      using False i by auto
  qed
qed

lemma circle_eq_rot_circle:
  assumes "0 \<le> x" "x \<le> 1" "0 \<le> y" "y \<le> 1" 
  shows "(circle_cube (x, y)) = (rot_circle_cube (rot_y'' x y, rot_x'' x y))"
proof
  have rw:  "\<bar>1/4 - x_coord x * x_coord x\<bar> = 1/4 - x_coord x * x_coord x"
    apply(rule abs_of_nonneg)
    using assms mult_left_le by (auto simp add: x_coord_def divide_simps algebra_simps)
  show "fst (circle_cube (x, y)) = fst (rot_circle_cube (rot_y'' x y, rot_x'' x y))"
    using assms d_gt_0
    apply(simp add: circle_cube_nice rot_circle_cube_def x_coord_inv_2 circle_y_def algebra_simps rw)
    apply(auto simp add: x_coord_def algebra_simps)
    by (sos "(((((A<0 * A<1) * ((A<0 * A<1) * R<1)) + (([~4*d^2] * A=0) + (((A<=1 * (A<=2 * (A<=3 * R<1))) * (R<8 * [d]^2)) + ((A<=1 * (A<=2 * (A<=3 * (A<1 * R<1)))) * (R<8 * [d]^2)))))) & ((((A<0 * A<1) * ((A<0 * A<1) * R<1)) + (([~4*d^2] * A=0) + (((A<=0 * (A<=2 * (A<=3 * R<1))) * (R<8 * [d]^2)) + ((A<=0 * (A<=2 * (A<=3 * (A<1 * R<1)))) * (R<8 * [d]^2)))))))") (*Be patient: it takes a bit of time, still better than creeping its proof manually.*)
  show "snd (circle_cube (x, y)) = snd (rot_circle_cube (rot_y'' x y, rot_x'' x y))"
    using assms
    by(auto simp add: circle_cube_def rot_circle_cube_def x_coord_inv_def circle_y_def x_coord_def)
qed

lemma rot_circle_eq_circle:
  assumes "0 \<le> x" "x \<le> 1" "0 \<le> y" "y \<le> 1" 
  shows "(rot_circle_cube (x, y)) = (circle_cube (rot_x'' y x, rot_y'' y x))"
proof
  show "fst (rot_circle_cube (x, y)) = fst (circle_cube (rot_x'' y x, rot_y'' y x))"
    using assms
    by(auto simp add: circle_cube_def rot_circle_cube_def x_coord_inv_def circle_y_def x_coord_def)
  have rw:  "\<bar>1/4 - x_coord y * x_coord y\<bar> =  1/4 - x_coord y * x_coord y"
    apply(rule abs_of_nonneg)
    using assms mult_left_le by (auto simp add: x_coord_def divide_simps algebra_simps)
  show "snd (rot_circle_cube (x, y)) = snd (circle_cube (rot_x'' y x, rot_y'' y x))"
    using assms d_gt_0
    apply(simp add: circle_cube_nice rot_circle_cube_def x_coord_inv_2 circle_y_def algebra_simps rw)
    apply(auto simp add: x_coord_def algebra_simps)
    by (sos "(((((A<0 * A<1) * ((A<0 * A<1) * R<1)) + (([~4*d^2] * A=0) + (((A<=0 * (A<=1 * (A<=3 * R<1))) * (R<8 * [d]^2)) + ((A<=0 * (A<=1 * (A<=3 * (A<1 * R<1)))) * (R<8 * [d]^2)))))) & ((((A<0 * A<1) * ((A<0 * A<1) * R<1)) + (([~4*d^2] * A=0) + (((A<=0 * (A<=1 * (A<=2 * R<1))) * (R<8 * [d]^2)) + ((A<=0 * (A<=1 * (A<=2 * (A<1 * R<1)))) * (R<8 * [d]^2)))))))") (*Be patient: it takes a bit of time, still better than creeping its proof manually.*)
qed

lemma rot_img_eq:
  assumes "0 < d"
  shows "(cubeImage (circle_cube )) = (cubeImage (rot_circle_cube))"
  apply(auto simp add: cubeImage_def image_def cbox_def real_pair_basis)
  by (meson rot_y_ivl rot_x_ivl assms circle_eq_rot_circle rot_circle_eq_circle)+ 

lemma rot_circle_div_circle:
  assumes "0 < (d::real)"
  shows "gen_division (cubeImage circle_cube) (cubeImage ` {rot_circle_cube})"
  using rot_img_eq[OF assms] by(auto simp add: gen_division_def)

lemma circle_cube_boundary_valid:
  assumes "(k,\<gamma>)\<in>boundary circle_cube"
  shows "valid_path \<gamma>"
proof -
  have f01: "finite{0,1}"
    by simp
  show ?thesis
    using assms
    unfolding boundary_def horizontal_boundary_def vertical_boundary_def circle_cube_def valid_path_def piecewise_C1_differentiable_on_def
    by safe (rule derivative_intros continuous_intros f01 exI ballI conjI refl | force simp add: field_simps)+
qed

lemma rot_circle_cube_boundary_valid:
  assumes "(k,\<gamma>)\<in>boundary rot_circle_cube"
  shows "valid_path \<gamma>"
  using assms swap_valid_boundaries circle_cube_boundary_valid
  by (fastforce simp add: rot_circle_cube_def)

lemma diff_divide_cancel: 
  fixes z::real shows  "z \<noteq> 0  \<Longrightarrow> (a * z - a * (b * z)) / z = (a - a * b)" 
  by (auto simp: field_simps)

lemma circle_cube_is_type_I:
  assumes "0 < d"
  shows "typeI_twoCube circle_cube"
  unfolding typeI_twoCube_def
proof (intro exI conjI ballI)
  have f01: "finite{-d/2,d/2}"
    by simp
  show "-d/2 < d/2"
    using assms by simp
  show "(\<lambda>x. d * sqrt (1/4 - (x/d) * (x/d))) piecewise_C1_differentiable_on {- d/2..d/2}"
    using assms unfolding piecewise_C1_differentiable_on_def   
    apply (intro exI conjI)
      apply (rule ballI refl f01 derivative_intros continuous_intros | simp)+
    apply (auto simp: field_simps)
    by sos
   show "(\<lambda>x. -d * sqrt (1/4 - (x/d) * (x/d))) piecewise_C1_differentiable_on {- d/2..d/2}"
    using assms unfolding piecewise_C1_differentiable_on_def   
    apply (intro exI conjI)
       apply (rule ballI refl f01 derivative_intros continuous_intros | simp)+
    apply (auto simp: field_simps)
    by sos
  show "- d * sqrt (1/4 - x / d * (x / d)) \<le> d * sqrt (1/4 - x / d * (x / d))"
    if "x \<in> {- d/2..d/2}" for x
  proof -
    have *: "x^2 \<le> (d/2)^2"
      using real_sqrt_le_iff that by fastforce
    show ?thesis
      apply (rule mult_right_mono)
      using assms * apply (simp_all add: divide_simps power2_eq_square)
      done
  qed
qed (auto simp add: circle_cube_def divide_simps algebra_simps diff_divide_cancel)

lemma rot_circle_cube_is_type_II:
  shows "typeII_twoCube rot_circle_cube"
  using d_gt_0 swap_typeI_is_typeII circle_cube_is_type_I
  by (auto simp add: rot_circle_cube_def)

definition circle_bot_edge where
  "circle_bot_edge = (1::int, \<lambda>t. (x_coord t * d, - d * circle_y (x_coord t)))"

definition circle_top_edge where
  "circle_top_edge = (- 1::int, \<lambda>t. (x_coord t * d, d * circle_y (x_coord t)))"

definition circle_right_edge where
  "circle_right_edge = (1::int, \<lambda>y. (d/2, 0))"

definition circle_left_edge where
  "circle_left_edge = (- 1::int, \<lambda>y. (- (d/2), 0))"

lemma circle_cube_boundary_explicit:
    "boundary circle_cube = {circle_left_edge,circle_right_edge,circle_bot_edge,circle_top_edge}"
  by (auto simp add: valid_two_cube_def boundary_def horizontal_boundary_def vertical_boundary_def circle_cube_def 
      circle_top_edge_def circle_bot_edge_def circle_cube_nice x_coord_def circle_y_def
      circle_left_edge_def circle_right_edge_def)

definition rot_circle_right_edge where
  "rot_circle_right_edge = (1::int, \<lambda>t. (d * circle_y (x_coord t), x_coord t * d))"

definition rot_circle_left_edge where
  "rot_circle_left_edge = (- 1::int, \<lambda>t. (- d * circle_y (x_coord t), x_coord t * d))"

definition rot_circle_top_edge where
  "rot_circle_top_edge = (- 1::int, \<lambda>y. (0, d/2))"

definition rot_circle_bot_edge where
  "rot_circle_bot_edge = (1::int, \<lambda>y. (0, - (d/2)))"

lemma rot_circle_cube_boundary_explicit:
    "boundary (rot_circle_cube) =
           {rot_circle_top_edge,rot_circle_bot_edge,rot_circle_right_edge,rot_circle_left_edge}"
  by (auto simp add: rot_circle_cube_def valid_two_cube_def boundary_def horizontal_boundary_def vertical_boundary_def circle_cube_def
      rot_circle_right_edge_def rot_circle_left_edge_def x_coord_def circle_y_def rot_circle_top_edge_def rot_circle_bot_edge_def)

lemma rot_circle_cube_vertical_boundary_explicit:
    "vertical_boundary rot_circle_cube = {rot_circle_right_edge,rot_circle_left_edge}"
  by (auto simp add: rot_circle_cube_def valid_two_cube_def vertical_boundary_def circle_cube_def
      rot_circle_right_edge_def rot_circle_left_edge_def x_coord_def circle_y_def)

lemma circ_left_edge_neq_top:
   "(- 1::int, \<lambda>y::real. (- (d/2), 0)) \<noteq> (- 1, \<lambda>x. ((x - 1/2) * d, d * sqrt (1/4 - (x - 1/2) * (x - 1/2))))"
  by (metis (no_types, lifting) add_diff_cancel_right' d_gt_0 mult.commute mult_cancel_left order_less_irrefl prod.inject)

lemma circle_cube_valid_two_cube: "valid_two_cube (circle_cube)"
proof (auto simp add: valid_two_cube_def boundary_def horizontal_boundary_def vertical_boundary_def circle_cube_def)
  have iv: "(- 1::int, \<lambda>y::real. (- (d/2), 0)) \<noteq> (- 1, \<lambda>x. ((x - 1/2) * d, d * sqrt (1/4 - (x - 1/2) * (x - 1/2))))"
    using d_gt_0  apply (auto simp add: algebra_simps)
    by (metis (no_types, hide_lams) add_diff_cancel_right' add_uminus_conv_diff cancel_comm_monoid_add_class.diff_cancel less_eq_real_def linorder_not_le mult.left_neutral prod.simps(1))
  have v: "(1::int, \<lambda>y. (d/2, 0)) \<noteq> (1, \<lambda>x. ((x - 1/2) * d, - (d * sqrt (1/4 - (x - 1/2) * (x - 1/2)))))"
    using d_gt_0  apply (auto simp add: algebra_simps)
    by (metis (no_types, hide_lams) diff_0 equal_neg_zero mult_zero_left nonzero_mult_div_cancel_left order_less_irrefl prod.sel(1) times_divide_eq_right zero_neq_numeral)
  show " card {(- 1::int, \<lambda>y. (- (d/2), 0)), (1, \<lambda>y. (d/2, 0)), (1, \<lambda>x. ((x - 1/2) * d, - (d * sqrt (1/4 - (x - 1/2) * (x - 1/2))))),
                   (- 1, \<lambda>x. ((x - 1/2) * d, d * sqrt (1/4 - (x - 1/2) * (x - 1/2))))} = 4"
    using iv v by auto
qed

lemma rot_circle_cube_valid_two_cube:
  shows "valid_two_cube rot_circle_cube"
  using valid_cube_valid_swap circle_cube_valid_two_cube d_gt_0 rot_circle_cube_def
  by force

definition circle_arc_0 where "circle_arc_0 = (1, \<lambda>t::real. (0,0))"

lemma circle_top_bot_edges_neq' [simp]: 
  shows "circle_top_edge \<noteq> circle_bot_edge"
  by (simp add: circle_top_edge_def circle_bot_edge_def)

lemma rot_circle_top_left_edges_neq [simp]: "rot_circle_top_edge \<noteq> rot_circle_left_edge"
  apply (simp add: rot_circle_left_edge_def rot_circle_top_edge_def x_coord_def)
  by (metis (mono_tags, hide_lams) cancel_comm_monoid_add_class.diff_cancel d_gt_0 divide_eq_0_iff mult_zero_left order_less_irrefl prod.sel(2) zero_neq_numeral)

lemma rot_circle_bot_left_edges_neq [simp]: "rot_circle_bot_edge \<noteq> rot_circle_left_edge"
  by (simp add: rot_circle_left_edge_def rot_circle_bot_edge_def x_coord_def)

lemma rot_circle_top_right_edges_neq [simp]: "rot_circle_top_edge \<noteq> rot_circle_right_edge"
  by (simp add: rot_circle_right_edge_def rot_circle_top_edge_def x_coord_def)

lemma rot_circle_bot_right_edges_neq [simp]: "rot_circle_bot_edge \<noteq> rot_circle_right_edge"
  apply (simp add: rot_circle_right_edge_def rot_circle_bot_edge_def x_coord_def)
  by (metis (mono_tags, hide_lams) cancel_comm_monoid_add_class.diff_cancel d_gt_0 divide_eq_0_iff mult_zero_left neg_0_equal_iff_equal order_less_irrefl prod.sel(2) zero_neq_numeral)

lemma rot_circle_right_top_edges_neq' [simp]: "rot_circle_right_edge \<noteq> rot_circle_left_edge"
  by (simp add: rot_circle_left_edge_def rot_circle_right_edge_def)

lemma rot_circle_left_bot_edges_neq [simp]: "rot_circle_left_edge \<noteq> rot_circle_top_edge"
  apply (simp add: rot_circle_top_edge_def rot_circle_left_edge_def)
  by (metis (no_types, hide_lams) cancel_comm_monoid_add_class.diff_cancel d_gt_0 mult.commute mult_zero_right nonzero_mult_div_cancel_left order_less_irrefl prod.sel(2) times_divide_eq_right x_coord_def zero_neq_numeral)

lemma circle_right_top_edges_neq [simp]: "circle_right_edge \<noteq> circle_top_edge"
proof -
  have "circle_right_edge = (1, (\<lambda>r::real. (d / 2, 0::real)))"
    using circle.circle_right_edge_def circle_axioms by blast
  then show ?thesis
    using circle.circle_top_edge_def circle_axioms by auto
qed

lemma circle_left_bot_edges_neq [simp]: "circle_left_edge \<noteq> circle_bot_edge"
proof -
  have "circle_bot_edge = (1, \<lambda>r. (x_coord r * d, - d * circle_y (x_coord r)))"
    using circle.circle_bot_edge_def circle_axioms by blast
  then show ?thesis
    by (simp add: circle_left_edge_def)
qed

lemma circle_left_top_edges_neq [simp]: "circle_left_edge \<noteq> circle_top_edge"
proof -
  have "\<exists>r. ((r - 1 / 2) * d, d * sqrt (1 / 4 - (r - 1 / 2) * (r - 1 / 2))) \<noteq> (- (d / 2), 0)"
    by (metis circ_left_edge_neq_top)
  then have "(\<exists>r. d * r \<noteq> - (d / 2)) \<or> (\<exists>r ra. (x_coord (x_coord_inv r) * d, d * circle_y (x_coord (x_coord_inv r))) = (x_coord ra * d, d * circle_y (x_coord ra)) \<and> d * circle_y r \<noteq> 0)"
    by (metis mult.commute)
  then have "(\<lambda>r. (x_coord r * d, d * circle_y (x_coord r))) \<noteq> (\<lambda>r. (- (d / 2), 0))"
    by (metis mult.commute prod.simps(1) x_coord_inv_2)
  then show ?thesis
    by (simp add: circle_left_edge_def circle_top_edge_def)
qed

lemma circle_right_bot_edges_neq [simp]: "circle_right_edge \<noteq> circle_bot_edge"
  by (smt Pair_inject circle_bot_edge_def d_gt_0 circle.circle_right_edge_def circle_axioms real_mult_le_cancel_iff1 x_coord_def)

definition circle_polar where
  "circle_polar t = ((d/2)  * cos (2 * pi * t), (d/2) * sin (2 * pi * t))"

lemma circle_polar_smooth: "(circle_polar) C1_differentiable_on {0..1}"
proof -
  have "inj ((*) (2 * pi))"
    by (auto simp: inj_on_def)
  then have *: "\<And>x. finite ({0..1} \<inter> (*) (2 * pi) -` {x})"
    by (simp add: finite_vimageI)
  have "(\<lambda>t. ((d/2)  * cos (2 * pi * t), (d/2) * sin (2 * pi * t))) C1_differentiable_on {0..1}"
    by (rule * derivative_intros)+
  then show ?thesis
    apply (rule eq_smooth_gen)
    by(simp add: circle_polar_def)
qed

abbreviation "custom_arccos \<equiv> (\<lambda>x. (if -1 \<le> x \<and> x \<le> 1 then arccos x else (if x < -1 then -x + pi else 1 -x )))"

lemma cont_custom_arccos: 
  assumes "S \<subseteq> {-1..1}"
  shows "continuous_on S custom_arccos"
proof -
  have "continuous_on ({-1..1} \<union> {}) custom_arccos"
    by (auto intro!: continuous_on_cases continuous_intros)
  with assms show ?thesis
    using continuous_on_subset by auto 
qed

lemma custom_arccos_has_deriv: 
  assumes "- 1 < x" "x < 1"
  shows "DERIV custom_arccos x :> inverse (- sqrt (1 - x\<^sup>2))"
proof -
  have x1: "\<bar>x\<bar>\<^sup>2 < 1\<^sup>2"
    by (simp add: abs_less_iff abs_square_less_1 assms)
  show ?thesis
    apply (rule DERIV_inverse_function [where f=cos and a="-1" and b=1])
         apply (rule x1 derivative_eq_intros | simp add: sin_arccos)+
    using assms x1 cont_custom_arccos [of "{-1<..<1}"] 
         apply (auto simp: continuous_on_eq_continuous_at greaterThanLessThan_subseteq_atLeastAtMost_iff)
    done
qed

declare 
  custom_arccos_has_deriv[THEN DERIV_chain2, derivative_intros]
  custom_arccos_has_deriv[THEN DERIV_chain2, unfolded has_field_derivative_def, derivative_intros]

lemma circle_boundary_reparams:
  shows rot_circ_left_edge_reparam_polar_circ_split:
    "reparam (rec_join [(rot_circle_left_edge)]) (rec_join [(subcube (1/4) (1/2) (1, circle_polar)), (subcube (1/2) (3/4) (1, circle_polar))])"
    (is ?P1)
    and circ_top_edge_reparam_polar_circ_split:
    "reparam (rec_join [(circle_top_edge)]) (rec_join [(subcube 0 (1/4) (1, circle_polar)), (subcube (1/4) (1/2) (1, circle_polar))])"
    (is ?P2)
    and circ_bot_edge_reparam_polar_circ_split:
    "reparam (rec_join [(circle_bot_edge)]) (rec_join [(subcube (1/2) (3/4) (1, circle_polar)), (subcube (3/4) 1 (1, circle_polar))])"
    (is ?P3)
    and rot_circ_right_edge_reparam_polar_circ_split:
    "reparam (rec_join [(rot_circle_right_edge)]) (rec_join [(subcube (3/4) 1 (1, circle_polar)), (subcube 0 (1/4) (1, circle_polar))])"
    (is ?P4)
proof -
  let ?\<phi> = "((*) (1/pi) \<circ> custom_arccos \<circ> (\<lambda>t. 2 * x_coord (1 - t)))" 
  let ?LHS1 = "(\<lambda>x. (- (d * sqrt (1/4 - x_coord (1 - x) * x_coord (1 - x))), x_coord (1 - x) * d))"
  let ?RHS1 = "((\<lambda>x. if x * 2 \<le> 1 then (d * cos (2 * pi * (2 * x/4 + 1/4))/2, d * sin (2 * pi * (2 * x/4 + 1/4))/2)
                        else (d * cos (2 * pi * ((2 * x - 1)/4 + 1/2))/2, d * sin (2 * pi * ((2 * x - 1)/4 + 1/2))/2)) \<circ> ?\<phi>)"
  let ?LHS2 = "\<lambda>x. ((x_coord (1 - x) * d, d * sqrt (1/4 - x_coord (1 - x) * x_coord (1 - x))))"
  let ?RHS2 = "((\<lambda>x. if x * 2 \<le> 1 then (d * cos (2 * x * pi/2)/2, d * sin (2 * x * pi/2)/2) else (d * cos (2 * pi * ((2 * x - 1)/4 + 1/4))/2, d * sin (2 * pi * ((2 * x - 1)/4 + 1/4))/2)) \<circ> ?\<phi>)"
  let ?LHS3 = "\<lambda>x. (x_coord x * d, - (d * sqrt (1/4 - x_coord x * x_coord x)))"
  let ?RHS3 = "(\<lambda>x. if x * 2 \<le> 1 then (d * cos (2 * pi * (2 * x/4 + 1/2))/2, d * sin (2 * pi * (2 * x/4 + 1/2))/2) 
                  else (d * cos (2 * pi * ((2 * x - 1)/4 + 3/4))/2, d * sin (2 * pi * ((2 * x - 1)/4 + 3/4))/2))"
  let ?LHS4 = "\<lambda>x. (d * sqrt (1/4 - x_coord x * x_coord x), x_coord x * d)"
  let ?RHS4 = "(\<lambda>x. if x * 2 \<le> 1 then (d * cos (2 * pi * (2 * x/4 + 3/4))/2, d * sin (2 * pi * (2 * x/4 + 3/4))/2) 
                 else (d * cos ((2 * x - 1) * pi/2)/2, d * sin ((2 * x - 1) * pi/2)/2))"
  have phi_diff: "?\<phi> piecewise_C1_differentiable_on {0..1}"
    unfolding piecewise_C1_differentiable_on_def
  proof
    show "continuous_on {0..1} ?\<phi>"
      unfolding x_coord_def
      by (intro continuous_on_compose cont_custom_arccos continuous_intros) auto
    have "?\<phi> C1_differentiable_on {0..1} - {0,1}"
      unfolding x_coord_def piecewise_C1_differentiable_on_def C1_differentiable_on_def valid_path_def
      by (simp | rule has_vector_derivative_pair_within DERIV_image_chain derivative_eq_intros continuous_intros exI ballI conjI 
          | force simp add: field_simps | sos)+
    then show "\<exists>s. finite s \<and> ?\<phi> C1_differentiable_on {0..1} - s"
      by force
  qed
  have inj: "inj ?\<phi>"
    apply (intro comp_inj_on inj_on_cases inj_on_arccos)
          apply (auto simp add: inj_on_def x_coord_def)
    using pi_ge_zero apply auto[1]
     apply (smt arccos)
    by (smt arccos_lbound)
  then have fin: "\<And>x. \<lbrakk>0 \<le> x; x \<le> 1\<rbrakk> \<Longrightarrow> finite (?\<phi> -` {x})" 
    by (simp add: finite_vimageI)
  have "?\<phi> ` {0..1} = {0..1}"
  proof
    show "?\<phi> ` {0..1} \<subseteq> {0..1}"
      by (auto simp add: x_coord_def divide_simps arccos_lbound arccos_bounded)
    have "arccos (1 - 2 * ((1 - cos (x * pi))/2)) = x * pi" if "0 \<le> x" "x \<le> 1" for x
      using that by (simp add: field_simps arccos_cos)
    then show "{0..1} \<subseteq> ?\<phi> ` {0..1}"
      apply (auto simp: x_coord_def o_def image_def)
      by (rule_tac x="(1 - cos (x * pi))/2" in bexI) auto
  qed
  then have bij_phi: "bij_betw ?\<phi> {0..1} {0..1}"
    unfolding bij_betw_def using inj inj_on_subset by blast 
  have phi01: "?\<phi> -` {0..1} \<subseteq> {0..1}"
    by (auto simp add: subset_iff x_coord_def divide_simps)
  {
    fix x::real assume x: "0 \<le> x" "x \<le> 1"
    then have i: "- 1 \<le> (2 * x - 1)" "(2 * x - 1) \<le> 1"  by auto
    have ii: "cos (pi / 2 + arccos (1 - x * 2)) = -sin (arccos (1 - x * 2))"
      using minus_sin_cos_eq[symmetric, where ?x = "arccos (1 - x * 2)"]
      by (auto simp add: add.commute)
    have "2 * sqrt (x - x * x) = sqrt (4*x - 4*x * x)"
      by (metis mult.assoc real_sqrt_four real_sqrt_mult right_diff_distrib)
    also have "... = sqrt (1  - (2 * x - 1) * (2 * x - 1))"
      by (simp add: algebra_simps)
    finally have iii: "2 * sqrt (x - x * x) = cos (arcsin (2 * x - 1)) \<and> 2 * sqrt (x - x * x) =  sin (arccos (1 - 2 * x))"
      using arccos_minus[OF i]  unfolding minus_diff_eq sin_pi_minus
      by (simp add: cos_arcsin i power2_eq_square sin_arccos)
    then have 1: "?LHS1 x = ?RHS1 x"
      using d_gt_0 i x apply (simp add: x_coord_def field_simps)
      apply (auto simp add: diff_divide_distrib add_divide_distrib right_diff_distrib mult.commute ii)
      using cos_sin_eq[where ?x = "- arccos (1 - x * 2)"]
      by (simp add: cos_sin_eq[where ?x = "- arccos (1 - x * 2)"] right_diff_distrib)
    have 2: "?LHS2 x = ?RHS2 x"
      using x d_gt_0 iii by (auto simp add: x_coord_def diff_divide_distrib algebra_simps)
    have a: "cos (pi / 2 - arccos (x * 2 - 1)) = cos (pi / 2 - arccos (1 - x * 2))"
      by (smt arccos_minus arccos_cos2 arccos_lbound cos_arccos cos_ge_minus_one cos_le_one i(1) i(2) pi_def pi_half)
    have b: "cos (arccos (1 - x * 2) + pi * 3 / 2) = cos ((pi / 2 - arccos (x * 2 - 1)) + 2 * pi)"
      using arccos_minus[OF i]  by(auto simp add: mult.commute add.commute)
    then have c: "... = cos (pi / 2 - arccos (x * 2 - 1))" using cos_periodic by blast
    have "cos (- pi - arccos (1 - x * 2)) = cos (- (pi + arccos (1 - x * 2)))"
      by (auto simp add: minus_add[where b = "pi" and a = "arccos (1 - x * 2)", symmetric])
    moreover have "... = cos ((pi + arccos (1 - x * 2)))"
      using cos_minus by blast
    moreover have "... = cos (2*pi - arccos (x * 2 - 1))"
      using arccos_minus[OF i]  by (auto simp add: mult.commute add.commute)
    moreover have "... = cos (arccos (x * 2 - 1))"
      using cos_2pi_minus by auto
    ultimately have d: "cos (- pi - arccos (1 - x * 2)) = (x * 2 - 1)"
      using cos_arccos[OF i] mult.commute by metis
    have cosm: "\<And>x. cos (x - pi*2) = cos x"
      by (metis cos_periodic eq_diff_eq' mult.commute) 
    have 34: "?LHS3 x = (?RHS3  \<circ> ?\<phi>) x"  "?LHS4 x = (?RHS4 \<circ> ?\<phi>) x"
      using d_gt_0 x a b c iii cos_periodic [of "pi / 2 - arccos (x * 2 - 1)"] 
       apply (auto simp add: x_coord_def algebra_simps diff_divide_distrib power2_eq_square)
       apply (auto simp add: sin_cos_eq cosm)
      using d apply (auto simp add: right_diff_distrib)
      by (smt cos_minus)
    note 1 2 34
  } note * = this
  show ?P1 ?P2 ?P3 ?P4
       apply (auto simp add: subcube_def circle_bot_edge_def circle_top_edge_def circle_polar_def reversepath_def 
               subpath_def joinpaths_def circle_y_def rot_circle_left_edge_def rot_circle_right_edge_def)
    unfolding reparam_def
    by (rule ballI exI conjI impI phi_diff bij_phi phi01 fin * | force simp add: x_coord_def)+
qed


definition circle_cube_boundary_to_polarcircle where
  "circle_cube_boundary_to_polarcircle \<gamma> \<equiv>
     if (\<gamma> = (circle_top_edge)) then
           {subcube 0 (1/4) (1, circle_polar), subcube (1/4) (1/2) (1, circle_polar)}
     else if (\<gamma> = (circle_bot_edge)) then
           {subcube (1/2) (3/4) (1, circle_polar), subcube (3/4) 1 (1, circle_polar)}
     else {}"

definition rot_circle_cube_boundary_to_polarcircle where
  "rot_circle_cube_boundary_to_polarcircle \<gamma> \<equiv>
     if (\<gamma> = (rot_circle_left_edge )) then
           {subcube (1/4)  (1/2) (1, circle_polar), subcube (1/2) (3/4) (1, circle_polar)}
     else if (\<gamma> = (rot_circle_right_edge)) then
           {subcube (3/4) 1 (1, circle_polar), subcube 0 (1/4) (1, circle_polar)}
     else {}"

lemma circle_arcs_neq:
  assumes "0 \<le> k" "k \<le> 1" "0 \<le> n" "n \<le> 1" "n < k" "k + n < 1"
  shows "subcube k m (1, circle_polar) \<noteq> subcube n q (1, circle_polar)"
proof (simp add: subcube_def subpath_def circle_polar_def)
  have "cos (2 * pi * k) \<noteq> cos(2 * pi * n)"
    unfolding cos_eq
  proof safe
    show False if "2 * pi * k = 2 * pi * n + 2 * m * pi" "m \<in> \<int>" for m
    proof -
      have "2 * pi * (k - n ) = 2 * m * pi"
        using distrib_left that by (simp add: left_diff_distrib mult.commute)
      then have a: "m = (k - n)" by auto
      have "\<lfloor>k - n\<rfloor> = 0 "
        using assms by (simp add: floor_eq_iff)
      then have "k - n \<notin> \<int>"
        using assms by (auto simp only: frac_eq_0_iff[symmetric] frac_def)
      then show False using that a by auto
    qed
    show False if "2 * pi * k = - (2 * pi * n) + 2 * m * pi" "m \<in> \<int>" for m
    proof -
      have "2 * pi * (k + n ) = 2 * m * pi"
        using that by (auto simp add: distrib_left)
      then have a: "m = (k + n)" by auto
      have "\<lfloor>k + n\<rfloor> = 0 "
        using assms by (simp add: floor_eq_iff)
      then have "k + n \<notin> \<int>"
        using Ints_def assms by force
      then show False using that a by auto
    qed
  qed
  then have "(\<lambda>x. (d * cos (2 * pi * ((m - k) * x + k))/2, d * sin (2 * pi * ((m - k) * x + k))/2)) 0  \<noteq> (\<lambda>x. (d * cos (2 * pi * ((q - n) * x + n))/2, d * sin (2 * pi * ((q - n) * x + n))/2)) 0"
    using d_gt_0 by auto
  then show "(\<lambda>x. (d * cos (2 * pi * ((m - k) * x + k))/2, d * sin (2 * pi * ((m - k) * x + k))/2)) \<noteq> (\<lambda>x. (d * cos (2 * pi * ((q - n) * x + n))/2, d * sin (2 * pi * ((q - n) * x + n))/2))" 
    by metis
qed

lemma circle_arcs_neq_2:
  assumes "0 \<le> k" "k \<le> 1" "0 \<le> n" "n \<le> 1" "n < k" "0 < n" and kn12: "1/2 < k + n" and "k + n < 3/2"
  shows "subcube k m (1, circle_polar) \<noteq> subcube n q (1, circle_polar)"
proof (simp add: subcube_def subpath_def circle_polar_def)
  have "sin (2 * pi * k) \<noteq> sin(2 * pi * n)"
    unfolding sin_eq
  proof safe
    show False if "m \<in> \<int>" "2 * pi * k = 2 * pi * n + 2 * m * pi" for m
    proof -
      have "2 * pi * (k - n) = 2 * m * pi"
        using that by (simp add: left_diff_distrib mult.commute)                      
      then have a: "m = (k - n)" by auto
      have "\<lfloor>k - n\<rfloor> = 0 "
        using assms by (simp add: floor_eq_iff)
      then have "k - n \<notin>  \<int>"
        using assms by (auto simp only: frac_eq_0_iff[symmetric] frac_def )
      then show False using that a by auto
    qed
    show False if "2 * pi * k = - (2 * pi * n) + (2 * m + 1) * pi" "m \<in> \<int>" for m
    proof -
      have i: "\<And>pi. 0 < pi \<Longrightarrow> 2 * pi * (k + n ) = 2 * m * pi + pi \<Longrightarrow> m = (k + n) - 1/2"
        by (sos "(((((A<0 * A<1) * R<1) + ([1/2] * A=0))) & ((((A<0 * A<1) * R<1) + ([~1/2] * A=0))))")
      have "2 * pi * (k + n) = 2 * m * pi + pi"
        using that by (simp add: algebra_simps)
      then have a: "m = (k + n) - 1/2" using i[OF pi_gt_zero] by fastforce
      have "\<lfloor>k + n - 1/2\<rfloor> = 0 "
        using assms by (auto simp add: floor_eq_iff)
      then have "k + n - 1/2 \<notin> \<int>"
        by (metis Ints_cases add.commute add.left_neutral add_diff_cancel_left' add_diff_eq kn12 floor_of_int of_int_0 order_less_irrefl)
      then show False using that a by auto
    qed
  qed
  then have "(\<lambda>x. (d * cos (2 * pi * ((m - k) * x + k))/2, d * sin (2 * pi * ((m - k) * x + k))/2)) 0  \<noteq> (\<lambda>x. (d * cos (2 * pi * ((q - n) * x + n))/2, d * sin (2 * pi * ((q - n) * x + n))/2)) 0"
    using d_gt_0 by auto
  then show "(\<lambda>x. (d * cos (2 * pi * ((m - k) * x + k))/2, d * sin (2 * pi * ((m - k) * x + k))/2)) \<noteq> (\<lambda>x. (d * cos (2 * pi * ((q - n) * x + n))/2, d * sin (2 * pi * ((q - n) * x + n))/2))" 
    by metis
qed

lemma circle_cube_is_only_horizontal_div_of_rot:
  shows "only_horizontal_division (boundary (circle_cube)) {rot_circle_cube}"
  unfolding only_horizontal_division_def
proof (rule exI [of _ "{}"], simp, intro conjI ballI)
  show "finite (boundary circle_cube)"
    using circle.circle_cube_boundary_explicit circle_axioms by auto
  show "boundary_chain (boundary circle_cube)"
    by (simp add: two_cube_boundary_is_boundary)
  show "\<And>x. x \<in> boundary circle_cube \<Longrightarrow> case x of (k, x) \<Rightarrow> valid_path x"
    using circle_cube_boundary_valid by blast
  let ?\<V> = "(boundary (circle_cube))"
  let ?pi = "{circle_left_edge, circle_right_edge}"
  let ?pj = "{rot_circle_top_edge, rot_circle_bot_edge}"
  let ?f = "circle_cube_boundary_to_polarcircle"
  let ?one_chaini = "boundary (circle_cube) - ?pi"
  have c: "common_reparam_exists ?\<V> (two_chain_vertical_boundary {rot_circle_cube})"
    unfolding common_reparam_exists_def
  proof (intro exI conjI)
    let ?subdiv = "{(subcube 0 (1/4) (1, circle_polar)),
                    (subcube (1/4) (1/2) (1, circle_polar)),
                    (subcube (1/2) (3/4) (1, circle_polar)),
                    (subcube (3/4) 1 (1, circle_polar))}"
    show "(\<forall>(k, \<gamma>)\<in>?subdiv. \<gamma> C1_differentiable_on {0..1})"
      using subpath_smooth[OF circle_polar_smooth] by (auto simp add: subcube_def)
    have 1: "finite ?subdiv" by auto
    show "boundary_chain ?subdiv"
      by (simp add: boundary_chain_def subcube_def)
    show "chain_reparam_chain' (boundary (circle_cube) - ?pi) ?subdiv"
      unfolding chain_reparam_chain'_def
    proof (intro exI conjI impI)
      show "\<Union> (?f ` ?one_chaini) = ?subdiv"
        apply (simp add: circle_cube_boundary_to_polarcircle_def circle_cube_boundary_explicit)
        using circle_top_bot_edges_neq' by metis
        let ?l = "[subcube 0 (1/4) (1, circle_polar), subcube (1/4) (1/2) (1, circle_polar)]"
      have "chain_reparam_weak_path (coeff_cube_to_path (circle_top_edge)) {subcube 0 (1/4) (1, circle_polar), subcube (1/4) (1/2) (1, circle_polar)}"
        unfolding chain_reparam_weak_path_def
      proof (intro exI conjI)
        show "valid_chain_list ?l"
          by (auto simp add: subcube_def circle_top_edge_def  x_coord_def circle_y_def pathfinish_def pathstart_def
              reversepath_def subpath_def joinpaths_def)
        show "reparam (coeff_cube_to_path circle_top_edge) (rec_join ?l)"
          using circ_top_edge_reparam_polar_circ_split by auto
        show "distinct ?l"
            apply simp
            apply (subst neq_commute)
            apply (simp add: circle_arcs_neq)
            done
      qed auto                                                     
      moreover have "chain_reparam_weak_path (coeff_cube_to_path (circle_bot_edge)) {subcube (1/2) (3/4) (1, circle_polar), subcube (3/4) 1 (1, circle_polar)}"
        unfolding chain_reparam_weak_path_def
      proof
        let ?l = "[subcube (1/2) (3/4) (1, circle_polar), subcube (3/4) 1 (1, circle_polar)]"
        have a: "valid_chain_list ?l"
          by (auto simp add: subcube_def circle_top_edge_def  x_coord_def circle_y_def pathfinish_def pathstart_def
              reversepath_def subpath_def joinpaths_def)
        have b: "reparam (rec_join [circle_bot_edge]) (rec_join ?l)"
          using circ_bot_edge_reparam_polar_circ_split by auto
        have c: "subcube (3/4) 1 (1, circle_polar) \<noteq> subcube (1/2) (3/4) (1, circle_polar)"
          apply(rule circle_arcs_neq_2) using d_gt_0(1) by auto
        show "set ?l = {subcube (1/2) (3/4) (1, circle_polar), subcube (3/4) 1 (1, circle_polar)} \<and>
                            distinct ?l \<and> reparam (coeff_cube_to_path (circle_bot_edge)) (rec_join ?l) \<and> valid_chain_list ?l \<and> ?l \<noteq> []" using a b c by auto
      qed
      ultimately
      show "(\<forall>cube\<in>?one_chaini. chain_reparam_weak_path (rec_join [cube]) (?f cube))"
        by (auto simp add:  circle_cube_boundary_to_polarcircle_def UNION_eq circle_cube_boundary_explicit)
      show "(\<forall>p\<in>?one_chaini. \<forall>p'\<in>?one_chaini. p \<noteq> p' \<longrightarrow> ?f p \<inter> ?f p' = {})"
        using circle_arcs_neq circle_arcs_neq_2 
        apply (auto simp add: circle_cube_boundary_to_polarcircle_def UNION_eq circle_cube_boundary_explicit neq_commute d_gt_0)
        using circle_top_bot_edges_neq' d_gt_0 apply auto[1]
          apply (smt atLeastAtMost_iff divide_less_eq_1_pos zero_less_divide_1_iff)
         apply (smt atLeastAtMost_iff divide_less_eq_1_pos zero_less_divide_iff)
        apply (smt atLeastAtMost_iff divide_cancel_left divide_less_eq_1_pos field_sum_of_halves zero_less_divide_1_iff)
        done
      show "(\<forall>x\<in>?one_chaini. finite (?f x))"
        by (auto simp add: circle_cube_boundary_to_polarcircle_def circle_cube_boundary_explicit)
    qed
    show "(\<forall>(k, \<gamma>)\<in>?pi. point_path \<gamma>)"
      using d_gt_0 by (auto simp add: point_path_def circle_left_edge_def circle_right_edge_def)
    let ?f = "rot_circle_cube_boundary_to_polarcircle"
    let ?one_chain2.0 = "two_chain_vertical_boundary {rot_circle_cube} - ?pj"
    show "chain_reparam_chain' (two_chain_vertical_boundary {rot_circle_cube} - ?pj) ?subdiv"
      unfolding chain_reparam_chain'_def
    proof (intro exI conjI)
      have rw: "?one_chain2.0 = {rot_circle_left_edge, rot_circle_right_edge}"
        by(auto simp add: rot_circle_cube_vertical_boundary_explicit two_chain_vertical_boundary_def)
      show "\<Union> (?f ` ?one_chain2.0) = ?subdiv"
        using rot_circle_right_top_edges_neq'
        by (auto simp add: rot_circle_cube_boundary_to_polarcircle_def rw)
      show "(\<forall>cube\<in>?one_chain2.0. chain_reparam_weak_path (rec_join [cube]) (?f cube))"
      proof (clarsimp simp add: rot_circle_cube_boundary_to_polarcircle_def rw, intro conjI)
        let ?l = "[subcube (1/4) (1/2) (1, circle_polar), subcube (1/2) (3/4) (1, circle_polar)]"
        show "chain_reparam_weak_path (coeff_cube_to_path (rot_circle_left_edge)) {subcube (1/4) (1/2) (1, circle_polar), subcube (1/2) (3/4) (1, circle_polar)}"
          unfolding chain_reparam_weak_path_def
        proof (intro exI conjI)
          show "valid_chain_list ?l"
            by (auto simp add: subcube_def pathfinish_def pathstart_def reversepath_def subpath_def joinpaths_def)
          show "reparam (coeff_cube_to_path rot_circle_left_edge) (rec_join ?l)"
            using rot_circ_left_edge_reparam_polar_circ_split by auto
          show "distinct ?l"
            apply simp
            apply (subst neq_commute)
            apply (simp add: circle_arcs_neq)
            done
        qed auto
        show "chain_reparam_weak_path (coeff_cube_to_path (rot_circle_right_edge)) {subcube (3/4) 1 (1, circle_polar), subcube 0 (1/4) (1, circle_polar)}"
          unfolding chain_reparam_weak_path_def
        proof (intro exI conjI)
          let ?l = "[subcube (3/4) 1 (1, circle_polar), subcube 0 (1/4) (1, circle_polar)]"
          show "valid_chain_list ?l"
            by  (auto simp add: circle_polar_def subcube_def pathfinish_def pathstart_def
                reversepath_def subpath_def joinpaths_def)
          show "reparam (coeff_cube_to_path rot_circle_right_edge) (rec_join ?l)"
            using rot_circ_right_edge_reparam_polar_circ_split by auto
          show "distinct ?l" 
            by (simp add: circle_arcs_neq)
        qed auto
      qed
      show "(\<forall>p\<in>?one_chain2.0. \<forall>p'\<in>?one_chain2.0. p \<noteq> p' \<longrightarrow> ?f p \<inter> ?f p' = {})"
        using circle_arcs_neq circle_arcs_neq_2 
        apply (auto simp add: rot_circle_cube_boundary_to_polarcircle_def neq_commute)
         apply (metis add.right_neutral divide_less_eq_1_pos dual_order.order_iff_strict num.distinct(1) one_less_numeral_iff prod.sel(1) prod.sel(2) semiring_norm(68) subcube_def zero_less_divide_1_iff zero_less_numeral)
        apply (smt field_sum_of_halves)
        done
      show "(\<forall>x\<in>?one_chain2.0. finite (?f x))"
        by (auto simp add: rot_circle_cube_boundary_to_polarcircle_def UNION_eq rw)
    qed
    show "(\<forall>(k, \<gamma>)\<in>?pj. point_path \<gamma>)"
      using d_gt_0 by (auto simp add: point_path_def rot_circle_top_edge_def rot_circle_bot_edge_def)
  qed 
  then show "common_sudiv_exists (two_chain_vertical_boundary {rot_circle_cube}) (boundary circle_cube) \<or>
             common_reparam_exists (boundary circle_cube) (two_chain_vertical_boundary {rot_circle_cube})"
    by blast
qed

lemma GreenThm_cirlce:
  assumes "\<forall>twoC\<in>{circle_cube}. analytically_valid (cubeImage twoC) (\<lambda>x. F x \<bullet> i) j"
    "\<forall>twoC\<in>{rot_circle_cube}. analytically_valid (cubeImage twoC) (\<lambda>x. F x \<bullet> j) i"
  shows "integral (cubeImage (circle_cube)) (\<lambda>x. partial_vector_derivative (\<lambda>x. F x \<bullet> j) i x - partial_vector_derivative (\<lambda>x. F x \<bullet> i) j x) =
                     one_chain_line_integral F {i, j} (boundary (circle_cube))"
proof(rule green_typeI_typeII_chain.GreenThm_typeI_typeII_divisible_region_finite_holes[of "(cubeImage (circle_cube))" i j F "{circle_cube}" "{rot_circle_cube}",
                            OF _ _ _ circle_cube_is_only_horizontal_div_of_rot _], auto)
  show "\<And> a b. (a, b) \<in> boundary circle_cube \<Longrightarrow> valid_path b" using circle_cube_boundary_valid by auto
  show "green_typeI_typeII_chain (cubeImage circle_cube) i j F {circle_cube} {rot_circle_cube}"
    using assms
    proof(auto simp add: green_typeI_typeII_chain_def green_typeI_chain_def green_typeII_chain_def green_typeI_chain_axioms_def green_typeII_chain_axioms_def
               intro!: circle_cube_is_type_I rot_circle_cube_is_type_II d_gt_0 R2_axioms)
      show "gen_division (cubeImage circle_cube) {cubeImage circle_cube}" by (simp add: gen_division_def)
      show "gen_division (cubeImage (circle_cube)) ({cubeImage rot_circle_cube})"
        using rot_circle_div_circle d_gt_0 by auto 
      show "valid_two_chain {rot_circle_cube}" "valid_two_chain {circle_cube}"
        apply (auto simp add: valid_two_chain_def)
        using rot_circle_cube_valid_two_cube circle_cube_valid_two_cube assms(1) by auto
    qed
  show "only_vertical_division (boundary (circle_cube)) {circle_cube}"
    using twoChainVertDiv_of_itself[of "{circle_cube}"]
    apply(simp add: two_chain_boundary_def)
    using circle_cube_boundary_valid
    by auto
qed
end
end
