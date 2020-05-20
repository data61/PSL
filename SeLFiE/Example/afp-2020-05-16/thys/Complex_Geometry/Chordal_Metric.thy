(* -------------------------------------------------------------------------- *)
subsection \<open>Chordal Metric\<close>
(* -------------------------------------------------------------------------- *)

text \<open>Riemann sphere can be made a metric space. We are going to introduce distance on Riemann sphere
and to prove that it is a metric space. The distance between two points on the sphere is defined as
the length of the chord that connects them. This metric can be used in formalization of elliptic
geometry.\<close>

theory Chordal_Metric
  imports Homogeneous_Coordinates Riemann_Sphere Oriented_Circlines "HOL-Analysis.Inner_Product" "HOL-Analysis.Euclidean_Space"
begin

(* -------------------------------------------------------------------------- *)
subsubsection \<open>Inner product and norm\<close>
(* -------------------------------------------------------------------------- *)

definition inprod_cvec :: "complex_vec \<Rightarrow> complex_vec \<Rightarrow> complex" where
 [simp]: "inprod_cvec z w =
             (let (z1, z2) = z;
                  (w1, w2) = w
               in vec_cnj (z1, z2) *\<^sub>v\<^sub>v (w1, w2))"
syntax
  "_inprod_cvec" :: "complex_vec \<Rightarrow> complex_vec \<Rightarrow> complex"  ("\<langle>_,_\<rangle>")
translations
  "\<langle>z,w\<rangle>" == "CONST inprod_cvec z w"

lemma real_inprod_cvec [simp]:
  shows "is_real \<langle>z,z\<rangle>"
  by (cases z, simp add: vec_cnj_def)

lemma inprod_cvec_ge_zero [simp]:
  shows "Re \<langle>z,z\<rangle> \<ge> 0"
  by (cases z, simp add: vec_cnj_def)

lemma inprod_cvec_bilinear1 [simp]:
  assumes "z' = k *\<^sub>s\<^sub>v  z"
  shows "\<langle>z',w\<rangle> = cnj k * \<langle>z,w\<rangle>"
  using assms
  by (cases z, cases z', cases w) (simp add: vec_cnj_def field_simps)

lemma inprod_cvec_bilinear2 [simp]:
  assumes "z' = k *\<^sub>s\<^sub>v z"
  shows "\<langle>w, z'\<rangle> = k * \<langle>w, z\<rangle>"
  using assms
  by (cases z, cases z', cases w) (simp add: vec_cnj_def field_simps)

lemma inprod_cvec_g_zero [simp]:
  assumes "z \<noteq> vec_zero"
  shows "Re \<langle>z, z\<rangle> > 0"
proof-
  have "\<forall> a b. a \<noteq> 0 \<or> b \<noteq> 0 \<longrightarrow> 0 < (Re a * Re a + Im a * Im a) + (Re b * Re b + Im b * Im b)"
    by (smt complex_eq_0 not_sum_squares_lt_zero power2_eq_square)
  thus ?thesis
    using assms
    by (cases z, simp add: vec_cnj_def)
qed

definition norm_cvec :: "complex_vec \<Rightarrow> real" where
  [simp]: "norm_cvec z = sqrt (Re \<langle>z,z\<rangle>)"
syntax
  "_norm_cvec" :: "complex_vec \<Rightarrow> complex"  ("\<langle>_\<rangle>")
translations
  "\<langle>z\<rangle>" == "CONST norm_cvec z"

lemma norm_cvec_square:
  shows "\<langle>z\<rangle>\<^sup>2 = Re (\<langle>z,z\<rangle>)"
  by (simp del: inprod_cvec_def)

lemma norm_cvec_gt_0:
  assumes "z \<noteq> vec_zero"
  shows "\<langle>z\<rangle> > 0"
  using assms
  by (simp del: inprod_cvec_def)

lemma norm_cvec_scale:
  assumes "z' = k *\<^sub>s\<^sub>v z"
  shows "\<langle>z'\<rangle>\<^sup>2 = Re (cnj k * k) * \<langle>z\<rangle>\<^sup>2"
  unfolding norm_cvec_square
  using inprod_cvec_bilinear1[OF assms, of z']
  using inprod_cvec_bilinear2[OF assms, of z]
  by (simp del: inprod_cvec_def add: field_simps)

lift_definition inprod_hcoords :: "complex_homo_coords \<Rightarrow> complex_homo_coords \<Rightarrow> complex" is inprod_cvec
  done

lift_definition norm_hcoords :: "complex_homo_coords \<Rightarrow> real" is norm_cvec
  done

(* -------------------------------------------------------------------------- *)
subsubsection \<open>Distance in $\mathbb{C}P^1$ - defined by Fubini-Study metric.\<close>
(* -------------------------------------------------------------------------- *)

text \<open>Formula for the chordal distance between the two points can be given directly based
on the homogenous coordinates of their stereographic projections in the plane. This is
called the Fubini-Study metric.\<close>

definition dist_fs_cvec :: "complex_vec \<Rightarrow> complex_vec \<Rightarrow> real" where [simp]:
  "dist_fs_cvec z1 z2 =
     (let (z1x, z1y) = z1;
          (z2x, z2y) = z2;
          num = (z1x*z2y - z2x*z1y) * (cnj z1x*cnj z2y - cnj z2x*cnj z1y);
          den = (z1x*cnj z1x + z1y*cnj z1y) * (z2x*cnj z2x + z2y*cnj z2y)
       in 2*sqrt(Re num / Re den))"

lemma dist_fs_cvec_iff:
  assumes "z \<noteq> vec_zero" and "w \<noteq> vec_zero"
  shows "dist_fs_cvec z w = 2*sqrt(1 - (cmod \<langle>z,w\<rangle>)\<^sup>2 / (\<langle>z\<rangle>\<^sup>2 * \<langle>w\<rangle>\<^sup>2))"
proof-
  obtain z1 z2 w1 w2 where *: "z = (z1, z2)" "w = (w1, w2)"
    by (cases "z", cases "w") auto
  have 1: "2*sqrt(1 - (cmod \<langle>z,w\<rangle>)\<^sup>2 / (\<langle>z\<rangle>\<^sup>2 * \<langle>w\<rangle>\<^sup>2)) = 2*sqrt((\<langle>z\<rangle>\<^sup>2 * \<langle>w\<rangle>\<^sup>2 - (cmod \<langle>z,w\<rangle>)\<^sup>2) / (\<langle>z\<rangle>\<^sup>2 * \<langle>w\<rangle>\<^sup>2))"
    using norm_cvec_gt_0[of z] norm_cvec_gt_0[of w] assms
    by (simp add: field_simps)

  have 2: "\<langle>z\<rangle>\<^sup>2 * \<langle>w\<rangle>\<^sup>2 = Re ((z1*cnj z1 + z2*cnj z2) * (w1*cnj w1 + w2*cnj w2))"
    using assms *
    by (simp add: vec_cnj_def)

  have 3: "\<langle>z\<rangle>\<^sup>2 * \<langle>w\<rangle>\<^sup>2 - (cmod \<langle>z,w\<rangle>)\<^sup>2 = Re ((z1*w2 - w1*z2) * (cnj z1*cnj w2 - cnj w1*cnj z2))"
    apply (subst cmod_square, (subst norm_cvec_square)+)
    using *
    by (simp add: vec_cnj_def field_simps)

  thus ?thesis
    using 1 2 3
    using *
    unfolding dist_fs_cvec_def Let_def
    by simp
qed

lift_definition dist_fs_hcoords :: "complex_homo_coords \<Rightarrow> complex_homo_coords \<Rightarrow> real" is dist_fs_cvec
  done

lift_definition dist_fs :: "complex_homo \<Rightarrow> complex_homo \<Rightarrow> real" is dist_fs_hcoords
proof transfer
  fix z1 z2 z1' z2' :: complex_vec
  obtain z1x z1y z2x z2y z1'x z1'y z2'x z2'y where
    zz: "z1 = (z1x, z1y)" "z2 = (z2x, z2y)" "z1' = (z1'x, z1'y)" "z2' = (z2'x, z2'y)"
    by (cases "z1", cases "z2", cases "z1'", cases "z2'") blast

  assume 1: "z1 \<noteq> vec_zero" "z2 \<noteq> vec_zero" "z1' \<noteq> vec_zero" "z2' \<noteq> vec_zero" "z1 \<approx>\<^sub>v z1'" "z2 \<approx>\<^sub>v z2'"
  then obtain k1 k2 where
    *: "k1 \<noteq> 0" "z1' = k1 *\<^sub>s\<^sub>v z1" and
    **: "k2 \<noteq> 0" "z2' = k2 *\<^sub>s\<^sub>v z2"
    by auto
  have "(cmod \<langle>z1,z2\<rangle>)\<^sup>2 / (\<langle>z1\<rangle>\<^sup>2 * \<langle>z2\<rangle>\<^sup>2) = (cmod \<langle>z1',z2'\<rangle>)\<^sup>2 / (\<langle>z1'\<rangle>\<^sup>2 * \<langle>z2'\<rangle>\<^sup>2)"
    using \<open>k1 \<noteq> 0\<close> \<open>k2 \<noteq> 0\<close>
    using cmod_square[symmetric, of k1] cmod_square[symmetric, of k2]
    apply (subst norm_cvec_scale[OF *(2)])
    apply (subst norm_cvec_scale[OF **(2)])
    apply (subst inprod_cvec_bilinear1[OF *(2)])
    apply (subst inprod_cvec_bilinear2[OF **(2)])
    by (simp add: power2_eq_square)
  thus "dist_fs_cvec z1 z2 = dist_fs_cvec z1' z2'"
    using 1 dist_fs_cvec_iff
    by simp
qed

lemma dist_fs_finite:
  shows "dist_fs (of_complex z1) (of_complex z2) = 2 * cmod(z1 - z2) / (sqrt (1+(cmod z1)\<^sup>2) * sqrt (1+(cmod z2)\<^sup>2))"
  apply transfer
  apply transfer
  apply (subst cmod_square)+
  apply (simp add: real_sqrt_divide cmod_def power2_eq_square)
  apply (subst real_sqrt_mult[symmetric])
  apply (simp add: field_simps)
  done

lemma dist_fs_infinite1:
  shows "dist_fs (of_complex z1) \<infinity>\<^sub>h = 2 / sqrt (1+(cmod z1)\<^sup>2)"
  by (transfer, transfer) (subst cmod_square, simp add: real_sqrt_divide)

lemma dist_fs_infinite2:
  shows "dist_fs \<infinity>\<^sub>h (of_complex z1) = 2 / sqrt (1+(cmod z1)\<^sup>2)"
  by (transfer, transfer) (subst cmod_square, simp add: real_sqrt_divide)

lemma dist_fs_cvec_zero:
  assumes "z \<noteq> vec_zero" and "w \<noteq> vec_zero"
  shows  "dist_fs_cvec z w = 0 \<longleftrightarrow> (cmod \<langle>z,w\<rangle>)\<^sup>2 = (\<langle>z\<rangle>\<^sup>2 * \<langle>w\<rangle>\<^sup>2)"
  using assms norm_cvec_gt_0[of z]  norm_cvec_gt_0[of w]
  by (subst dist_fs_cvec_iff) auto

lemma dist_fs_zero1 [simp]:
  shows "dist_fs z z = 0"
  by (transfer, transfer)
     (subst dist_fs_cvec_zero, simp, (subst norm_cvec_square)+, subst cmod_square, simp del: inprod_cvec_def)

lemma dist_fs_zero2 [simp]:
  assumes "dist_fs z1 z2 = 0"
  shows "z1 = z2"
  using assms
proof (transfer, transfer)
  fix z w :: complex_vec
  obtain z1 z2 w1 w2 where *: "z = (z1, z2)" "w = (w1, w2)"
    by (cases "z", cases "w", auto)
  let ?x = "(z1*w2 - w1*z2) * (cnj z1*cnj w2 - cnj w1*cnj z2)"
  assume "z \<noteq> vec_zero" "w \<noteq> vec_zero" "dist_fs_cvec z w = 0"
  hence "(cmod \<langle>z,w\<rangle>)\<^sup>2 = \<langle>z\<rangle>\<^sup>2 * \<langle>w\<rangle>\<^sup>2"
    by (subst (asm) dist_fs_cvec_zero, simp_all)
  hence "Re ?x = 0"
    using *
    by (subst (asm) cmod_square) ((subst (asm) norm_cvec_square)+, simp add: vec_cnj_def field_simps)
  hence "?x = 0"
    using complex_mult_cnj_cmod[of "z1*w2 - w1*z2"] zero_complex.simps
    by (subst complex_eq_if_Re_eq[of ?x 0]) (simp add: power2_eq_square, simp, linarith)
  moreover
  have "z1 * w2 - w1 * z2 = 0 \<longleftrightarrow> cnj z1 * cnj w2 - cnj w1 * cnj z2 = 0"
    by (metis complex_cnj_diff complex_cnj_mult complex_cnj_zero_iff)
  ultimately
  show "z \<approx>\<^sub>v w"
    using * \<open>z \<noteq> vec_zero\<close> \<open>w \<noteq> vec_zero\<close>
    using complex_cvec_eq_mix[of z1 z2 w1 w2]
    by auto
qed

lemma dist_fs_sym:
  shows "dist_fs z1 z2 = dist_fs z2 z1"
  by (transfer, transfer) (simp add: split_def field_simps)

(* -------------------------------------------------------------------------- *)
subsubsection \<open>Triangle inequality for Fubini-Study metric\<close>
(* -------------------------------------------------------------------------- *)

lemma dist_fs_triangle_finite:
  shows "cmod(a - b) / (sqrt (1+(cmod a)\<^sup>2) * sqrt (1+(cmod b)\<^sup>2)) \<le> cmod (a - c) / (sqrt (1+(cmod a)\<^sup>2) * sqrt (1+(cmod c)\<^sup>2)) + cmod (c - b) / (sqrt (1+(cmod b)\<^sup>2) * sqrt (1+(cmod c)\<^sup>2))"
proof-
  let ?cc = "1+(cmod c)\<^sup>2" and ?bb = "1+(cmod b)\<^sup>2" and ?aa = "1+(cmod a)\<^sup>2"
  have "sqrt ?cc > 0" "sqrt ?aa > 0" "sqrt ?bb > 0"
    by (smt real_sqrt_gt_zero zero_compare_simps(12))+
  have "(a - b)*(1+cnj c*c) = (a-c)*(1+cnj c*b) + (c-b)*(1 + cnj c*a)"
    by (simp add: field_simps)
  moreover
  have "1 + cnj c * c = 1 + (cmod c)\<^sup>2"
    using complex_norm_square
    by auto
  hence "cmod ((a - b)*(1+cnj c*c)) = cmod(a - b) * (1+(cmod c)\<^sup>2)"
    by (smt norm_mult norm_of_real zero_compare_simps(12))
  ultimately
  have "cmod(a - b) * (1+(cmod c)\<^sup>2) \<le> cmod (a-c) * cmod (1+cnj c*b) + cmod (c-b) * cmod(1 + cnj c*a)"
    using complex_mod_triangle_ineq2[of "(a-c)*(1+cnj c*b)" "(c-b)*(1 + cnj c*a)"]
    by simp
  moreover
  have *: "\<And> a b c d b' d'. \<lbrakk>b \<le> b'; d \<le> d'; a \<ge> (0::real); c \<ge> 0\<rbrakk> \<Longrightarrow> a*b + c*d \<le> a*b' + c*d'"
    by (smt mult_left_mono)
  have "cmod (a-c) * cmod (1+cnj c*b) + cmod (c-b) * cmod(1 + cnj c*a) \<le> cmod (a - c) * (sqrt (1+(cmod c)\<^sup>2) * sqrt (1+(cmod b)\<^sup>2)) + cmod (c - b) * (sqrt (1+(cmod c)\<^sup>2) * sqrt (1+(cmod a)\<^sup>2))"
    using *[OF cmod_1_plus_mult_le[of "cnj c" b] cmod_1_plus_mult_le[of "cnj c" a], of "cmod (a-c)" "cmod (c-b)"]
    by (simp add: field_simps real_sqrt_mult[symmetric])
  ultimately
  have "cmod(a - b) * ?cc \<le> cmod (a - c) * sqrt ?cc * sqrt ?bb + cmod (c - b) * sqrt ?cc * sqrt ?aa"
    by simp
  moreover
  hence "0 \<le> ?cc * sqrt ?aa * sqrt ?bb"
    using mult_right_mono[of 0 "sqrt ?aa"  "sqrt ?bb"]
    using mult_right_mono[of 0 "?cc" "sqrt ?aa * sqrt ?bb"]
    by simp
  moreover
  have "sqrt ?cc / ?cc = 1 / sqrt ?cc"
    using \<open>sqrt ?cc > 0\<close>
    by (simp add: field_simps)
  hence "sqrt ?cc / (?cc * sqrt ?aa) = 1 / (sqrt ?aa * sqrt ?cc)"
    using times_divide_eq_right[of "1/sqrt ?aa" "sqrt ?cc" "?cc"]
    using \<open>sqrt ?aa > 0\<close>
    by simp
  hence "cmod (a - c) * sqrt ?cc / (?cc * sqrt ?aa) = cmod (a - c) / (sqrt ?aa * sqrt ?cc)"
    using times_divide_eq_right[of "cmod (a - c)" "sqrt ?cc" "(?cc * sqrt ?aa)"]
    by simp
  moreover
  have "sqrt ?cc / ?cc = 1 / sqrt ?cc"
    using \<open>sqrt ?cc > 0\<close>
    by (simp add: field_simps)
  hence "sqrt ?cc / (?cc * sqrt ?bb) = 1 / (sqrt ?bb * sqrt ?cc)"
    using times_divide_eq_right[of "1/sqrt ?bb" "sqrt ?cc" "?cc"]
    using \<open>sqrt ?bb > 0\<close>
    by simp
  hence "cmod (c - b) * sqrt ?cc / (?cc * sqrt ?bb) = cmod (c - b) / (sqrt ?bb * sqrt ?cc)"
    using times_divide_eq_right[of "cmod (c - b)" "sqrt ?cc" "?cc * sqrt ?bb"]
    by simp
  ultimately
  show ?thesis
    using divide_right_mono[of "cmod (a - b) * ?cc" "cmod (a - c) * sqrt ?cc * sqrt ?bb + cmod (c - b) * sqrt ?cc * sqrt ?aa" "?cc * sqrt ?aa * sqrt ?bb"] \<open>sqrt ?aa > 0\<close> \<open>sqrt ?bb > 0\<close> \<open>sqrt ?cc > 0\<close>
    by (simp add: add_divide_distrib)
qed

lemma dist_fs_triangle_infinite1: 
  shows "1 / sqrt(1 + (cmod b)\<^sup>2) \<le> 1 / sqrt(1 + (cmod c)\<^sup>2) + cmod (b - c) / (sqrt(1 + (cmod b)\<^sup>2) * sqrt(1 + (cmod c)\<^sup>2))"
proof-
  let ?bb = "sqrt (1 + (cmod b)\<^sup>2)" and ?cc = "sqrt (1 + (cmod c)\<^sup>2)"
  have "?bb > 0" "?cc > 0"
    by (metis add_strict_increasing real_sqrt_gt_0_iff zero_le_power2 zero_less_one)+
  hence *: "?bb * ?cc \<ge> 0"
    by simp
  have **: "(?cc - ?bb) / (?bb * ?cc) = 1 / ?bb - 1 / ?cc"
    using \<open>sqrt (1 + (cmod b)\<^sup>2) > 0\<close>  \<open>sqrt (1 + (cmod c)\<^sup>2) > 0\<close>
    by (simp add: field_simps)
  show "1 / ?bb \<le> 1 / ?cc + cmod (b - c) / (?bb * ?cc)"
    using divide_right_mono[OF cmod_diff_ge[of c b] *]
    by (subst (asm) **) (simp add: field_simps norm_minus_commute)
qed

lemma dist_fs_triangle_infinite2:
  shows "1 / sqrt(1 + (cmod a)\<^sup>2) \<le> cmod (a - c) / (sqrt (1+(cmod a)\<^sup>2) * sqrt (1+(cmod c)\<^sup>2)) + 1 / sqrt(1 + (cmod c)\<^sup>2)"
  using dist_fs_triangle_infinite1[of a c]
  by simp

lemma dist_fs_triangle_infinite3:
  shows "cmod(a - b) / (sqrt (1+(cmod a)\<^sup>2) * sqrt (1+(cmod b)\<^sup>2)) \<le> 1 / sqrt(1 + (cmod a)\<^sup>2) + 1 / sqrt(1 + (cmod b)\<^sup>2)"
proof-
  let ?aa = "sqrt (1 + (cmod a)\<^sup>2)" and ?bb = "sqrt (1 + (cmod b)\<^sup>2)"
  have "?aa > 0" "?bb > 0"
    by (metis add_strict_increasing real_sqrt_gt_0_iff zero_le_power2 zero_less_one)+
  hence *: "?aa * ?bb \<ge> 0"
    by simp
  have **: "(?aa + ?bb) / (?aa * ?bb) = 1 / ?aa + 1 / ?bb"
    using \<open>?aa > 0\<close> \<open>?bb > 0\<close>
    by (simp add: field_simps)
  show "cmod (a - b) / (?aa * ?bb) \<le> 1 / ?aa + 1 / ?bb"
    using divide_right_mono[OF cmod_diff_le[of a b] *]
    by (subst (asm) **) (simp add: field_simps norm_minus_commute)
qed

lemma dist_fs_triangle:
  shows "dist_fs A B \<le> dist_fs A C + dist_fs C B"
proof (cases "A = \<infinity>\<^sub>h")
  case True
  show ?thesis
  proof (cases "B = \<infinity>\<^sub>h")
    case True
    show ?thesis
    proof (cases "C = \<infinity>\<^sub>h")
      case True
      show ?thesis
        using \<open>A = \<infinity>\<^sub>h\<close> \<open>B = \<infinity>\<^sub>h\<close> \<open>C = \<infinity>\<^sub>h\<close>
        by simp
    next
      case False
      then obtain c where "C = of_complex c"
        using inf_or_of_complex[of C]
        by auto
      show ?thesis
        using \<open>A = \<infinity>\<^sub>h\<close> \<open>B = \<infinity>\<^sub>h\<close> \<open>C = of_complex c\<close>
        by (simp add: dist_fs_infinite2 dist_fs_sym)
    qed
  next
    case False
    then obtain b where "B = of_complex b"
      using inf_or_of_complex[of B]
      by auto
    show ?thesis
    proof (cases "C = \<infinity>\<^sub>h")
      case True
      show ?thesis
        using \<open>A = \<infinity>\<^sub>h\<close> \<open>C = \<infinity>\<^sub>h\<close> \<open>B = of_complex b\<close>
        by simp
    next
      case False
      then obtain c where "C = of_complex c"
        using inf_or_of_complex[of C]
        by auto
      show ?thesis
        using \<open>A = \<infinity>\<^sub>h\<close> \<open>B = of_complex b\<close> \<open>C = of_complex c\<close>
        using mult_left_mono[OF dist_fs_triangle_infinite1[of b c], of 2]
        by (simp add: dist_fs_finite dist_fs_infinite1 dist_fs_infinite2 dist_fs_sym)
    qed
  qed
next
  case False
  then obtain a where "A = of_complex a"
    using inf_or_of_complex[of A]
    by auto
  show ?thesis
  proof (cases "B = \<infinity>\<^sub>h")
    case True
    show ?thesis
    proof (cases "C = \<infinity>\<^sub>h")
      case True
      show ?thesis
        using \<open>B = \<infinity>\<^sub>h\<close> \<open>C = \<infinity>\<^sub>h\<close> \<open>A = of_complex a\<close>
        by (simp add: dist_fs_infinite2)
    next
      case False
      then obtain c where "C = of_complex c"
        using inf_or_of_complex[of C]
        by auto
      show ?thesis
        using \<open>B = \<infinity>\<^sub>h\<close> \<open>C = of_complex c\<close> \<open>A = of_complex a\<close>
        using mult_left_mono[OF dist_fs_triangle_infinite2[of a c], of 2]
        by (simp add: dist_fs_finite dist_fs_infinite1 dist_fs_infinite2)
    qed
  next
    case False
    then obtain b where "B = of_complex b"
      using inf_or_of_complex[of B]
      by auto
    show ?thesis
    proof (cases "C = \<infinity>\<^sub>h")
      case True
      thus ?thesis
        using \<open>C = \<infinity>\<^sub>h\<close> \<open>B = of_complex b\<close> \<open>A = of_complex a\<close>
        using mult_left_mono[OF dist_fs_triangle_infinite3[of a b], of 2]
        by (simp add: dist_fs_finite dist_fs_infinite1 dist_fs_infinite2)
    next
      case False
      then obtain c where "C = of_complex c"
        using inf_or_of_complex[of C]
        by auto
      show ?thesis
        using \<open>A = of_complex a\<close> \<open>B = of_complex b\<close> \<open>C = of_complex c\<close>
        using mult_left_mono[OF dist_fs_triangle_finite[of a b c], of 2]
        by (simp add: dist_fs_finite norm_minus_commute dist_fs_sym)
    qed
  qed
qed

(* -------------------------------------------------------------------------- *)
subsubsection \<open>$\mathbb{C}P^1$ with Fubini-Study metric is a metric space\<close>
(* -------------------------------------------------------------------------- *)

text \<open>Using the (already available) fact that $\mathbb{R}^3$ is a metric space (under the distance
function $\lambda\ x\ y.\ @{term norm}(x - y)$), it was not difficult to show that the type @{term
complex_homo} equipped with @{term dist_fs} is a metric space, i.e., an instantiation of the @{term
metric_space} locale.\<close>

instantiation complex_homo :: metric_space
begin
definition "dist_complex_homo = dist_fs"
definition "(uniformity_complex_homo :: (complex_homo \<times> complex_homo) filter) = (INF e\<in>{0<..}. principal {(x, y). dist_class.dist x y < e})"
definition "open_complex_homo (U :: complex_homo set) = (\<forall> x \<in> U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity)"
instance
proof
  fix x y :: complex_homo
  show "(dist_class.dist x y = 0) = (x = y)"
    unfolding dist_complex_homo_def
    using dist_fs_zero1[of x] dist_fs_zero2[of x y]
    by auto
next
  fix x y z :: complex_homo
  show "dist_class.dist x y \<le> dist_class.dist x z + dist_class.dist y z"
    unfolding dist_complex_homo_def
    using dist_fs_triangle[of x y z]
    by (simp add: dist_fs_sym)
qed (simp_all add: open_complex_homo_def uniformity_complex_homo_def)
end

(* -------------------------------------------------------------------------- *)
subsubsection \<open>Chordal distance on the Riemann sphere\<close>
(* -------------------------------------------------------------------------- *)

text \<open>Distance of the two points is given by the length of the chord. We show that it corresponds to
the Fubini-Study metric in the plane.\<close>

definition dist_riemann_sphere_r3 :: "R3 \<Rightarrow> R3 \<Rightarrow> real" where [simp]:
  "dist_riemann_sphere_r3 M1 M2 =
     (let (x1, y1, z1) = M1;
          (x2, y2, z2) = M2
       in norm (x1 - x2, y1 - y2, z1 - z2))"

lemma dist_riemann_sphere_r3_inner:
  assumes "M1 \<in> unit_sphere" and "M2 \<in> unit_sphere"
  shows  "(dist_riemann_sphere_r3 M1 M2)\<^sup>2 = 2 - 2 * inner M1 M2"
  using assms
  apply (cases M1, cases M2)
  apply (auto simp add: norm_prod_def)
  apply (simp add: power2_eq_square field_simps)
  done


lift_definition dist_riemann_sphere' :: "riemann_sphere \<Rightarrow> riemann_sphere \<Rightarrow> real" is dist_riemann_sphere_r3
  done

lemma dist_riemann_sphere_ge_0 [simp]: 
  shows "dist_riemann_sphere' M1 M2 \<ge> 0"
  apply transfer
  using norm_ge_zero
  by (simp add: split_def Let_def)

text \<open>Using stereographic projection we prove the connection between chordal metric on the spehere
and Fubini-Study metric in the plane.\<close>

lemma dist_stereographic_finite:
  assumes "stereographic M1 = of_complex m1"  and "stereographic M2 = of_complex m2"
  shows "dist_riemann_sphere' M1 M2 = 2 * cmod (m1 - m2) / (sqrt (1 + (cmod m1)\<^sup>2) * sqrt (1 + (cmod m2)\<^sup>2))"
  using assms
proof-
  have *: "M1 = inv_stereographic (of_complex m1)"  "M2 = inv_stereographic (of_complex m2)"
    using inv_stereographic_is_inv assms
    by (metis inv_stereographic_stereographic)+
  have "(1 + (cmod m1)\<^sup>2) \<noteq> 0"  "(1 + (cmod m2)\<^sup>2) \<noteq> 0"
    by (smt power2_less_0)+
  have "(1 + (cmod m1)\<^sup>2) > 0"  "(1 + (cmod m2)\<^sup>2) > 0"
    by (smt realpow_square_minus_le)+
  hence "(1 + (cmod m1)\<^sup>2) * (1 + (cmod m2)\<^sup>2) > 0"
    by (metis norm_mult_less norm_zero power2_eq_square zero_power2)
  hence ++: "sqrt ((1 + cmod m1 * cmod m1) * (1 + cmod m2 * cmod m2)) > 0"
    using real_sqrt_gt_0_iff
    by (simp add: power2_eq_square)
  hence **: "(2 * cmod (m1 - m2) / sqrt ((1 + cmod m1 * cmod m1) * (1 + cmod m2 * cmod m2))) \<ge> 0 \<longleftrightarrow> cmod (m1 - m2) \<ge> 0"
    by (metis diff_self divide_nonneg_pos mult_2 norm_ge_zero norm_triangle_ineq4 norm_zero)

  have "(dist_riemann_sphere' M1 M2)\<^sup>2 * (1 + (cmod m1)\<^sup>2) * (1 + (cmod m2)\<^sup>2) = 4 * (cmod (m1 - m2))\<^sup>2"
    using *
  proof (transfer, transfer)
    fix m1 m2 M1 M2
    assume us: "M1 \<in> unit_sphere" "M2 \<in> unit_sphere" and
        *: "M1 = inv_stereographic_cvec_r3 (of_complex_cvec m1)" "M2 = inv_stereographic_cvec_r3 (of_complex_cvec m2)"
    have "(1 + (cmod m1)\<^sup>2) \<noteq> 0"  "(1 + (cmod m2)\<^sup>2) \<noteq> 0"
      by (smt power2_less_0)+
    thus "(dist_riemann_sphere_r3 M1 M2)\<^sup>2 * (1 + (cmod m1)\<^sup>2) * (1 + (cmod m2)\<^sup>2) =
          4 * (cmod (m1 - m2))\<^sup>2"
      apply (subst dist_riemann_sphere_r3_inner[OF us])
      apply (subst *)+
      apply (simp add: dist_riemann_sphere_r3_inner[OF us] complex_mult_cnj_cmod)
      apply (subst left_diff_distrib[of 2])
      apply (subst left_diff_distrib[of "2*(1+(cmod m1)\<^sup>2)"])
      apply (subst distrib_right[of _ _ "(1 + (cmod m1)\<^sup>2)"])
      apply (subst distrib_right[of _ _ "(1 + (cmod m1)\<^sup>2)"])
      apply simp
      apply (subst distrib_right[of _ _ "(1 + (cmod m2)\<^sup>2)"])
      apply (subst distrib_right[of _ _ "(1 + (cmod m2)\<^sup>2)"])
      apply (subst distrib_right[of _ _ "(1 + (cmod m2)\<^sup>2)"])
      apply simp
      apply (subst (asm) cmod_square)+
      apply (subst cmod_square)+
      apply (simp add: field_simps)
      done
  qed
  hence "(dist_riemann_sphere' M1 M2)\<^sup>2 = 4 * (cmod (m1 - m2))\<^sup>2 / ((1 + (cmod m1)\<^sup>2) * (1 + (cmod m2)\<^sup>2))"
    using \<open>(1 + (cmod m1)\<^sup>2) \<noteq> 0\<close>  \<open>(1 + (cmod m2)\<^sup>2) \<noteq> 0\<close>
    using eq_divide_imp[of "(1 + (cmod m1)\<^sup>2) * (1 + (cmod m2)\<^sup>2)" "(dist_riemann_sphere' M1 M2)\<^sup>2" "4 * (cmod (m1 - m2))\<^sup>2"]
    by simp
  thus "dist_riemann_sphere' M1 M2 = 2 * cmod (m1 - m2) / (sqrt (1 + (cmod m1)\<^sup>2) * sqrt (1 + (cmod m2)\<^sup>2))"
    using power2_eq_iff[of "dist_riemann_sphere' M1 M2" "2 * (cmod (m1 - m2)) / sqrt ((1 + (cmod m1)\<^sup>2) * (1 + (cmod m2)\<^sup>2))"]
    using \<open>(1 + (cmod m1)\<^sup>2) * (1 + (cmod m2)\<^sup>2) > 0\<close>  \<open>(1 + (cmod m1)\<^sup>2) > 0\<close> \<open>(1 + (cmod m2)\<^sup>2) > 0\<close>
    apply (auto simp add: power2_eq_square real_sqrt_mult[symmetric])
    using dist_riemann_sphere_ge_0[of M1 M2] **
    using ++ divide_le_0_iff by force
qed


lemma dist_stereographic_infinite:
  assumes "stereographic M1 = \<infinity>\<^sub>h" and "stereographic M2 = of_complex m2"
  shows "dist_riemann_sphere' M1 M2 = 2 / sqrt (1 + (cmod m2)\<^sup>2)"
proof-
  have *: "M1 = inv_stereographic \<infinity>\<^sub>h"  "M2 = inv_stereographic (of_complex m2)"
    using inv_stereographic_is_inv assms
    by (metis inv_stereographic_stereographic)+
  have "(1 + (cmod m2)\<^sup>2) \<noteq> 0"
    by (smt power2_less_0)
  have "(1 + (cmod m2)\<^sup>2) > 0"
    by (smt realpow_square_minus_le)+
  hence "sqrt (1 + cmod m2 * cmod m2) > 0"
    using real_sqrt_gt_0_iff
    by (simp add: power2_eq_square)
  hence **: "2 / sqrt (1 + cmod m2 * cmod m2) > 0"
    by simp

  have "(dist_riemann_sphere' M1 M2)\<^sup>2 * (1 + (cmod m2)\<^sup>2) = 4"
    using *
    apply transfer
    apply transfer
  proof-
    fix M1 M2 m2
    assume us: "M1 \<in> unit_sphere" "M2 \<in> unit_sphere" and
           *: "M1 = inv_stereographic_cvec_r3 \<infinity>\<^sub>v" "M2 = inv_stereographic_cvec_r3 (of_complex_cvec m2)"
    have "(1 + (cmod m2)\<^sup>2) \<noteq> 0"
      by (smt power2_less_0)
    thus "(dist_riemann_sphere_r3 M1 M2)\<^sup>2 * (1 + (cmod m2)\<^sup>2) = 4"
      apply (subst dist_riemann_sphere_r3_inner[OF us])
      apply (subst *)+
      apply (simp add: complex_mult_cnj_cmod)
      apply (subst left_diff_distrib[of 2], simp)
      done
  qed
  hence "(dist_riemann_sphere' M1 M2)\<^sup>2 = 4 / (1 + (cmod m2)\<^sup>2)"
    using \<open>(1 + (cmod m2)\<^sup>2) \<noteq> 0\<close>
    by (simp add: field_simps)
  thus "dist_riemann_sphere' M1 M2 = 2 / sqrt (1 + (cmod m2)\<^sup>2)"
    using power2_eq_iff[of "dist_riemann_sphere' M1 M2" "2 / sqrt (1 + (cmod m2)\<^sup>2)"]
    using \<open>(1 + (cmod m2)\<^sup>2) > 0\<close>
    apply (auto simp add: power2_eq_square real_sqrt_mult[symmetric])
    using dist_riemann_sphere_ge_0[of M1 M2] **
    by simp
qed

lemma dist_rieman_sphere_zero [simp]: 
  shows "dist_riemann_sphere' M M = 0"
  by transfer auto

lemma dist_riemann_sphere_sym: 
  shows "dist_riemann_sphere' M1 M2 = dist_riemann_sphere' M2 M1"
proof transfer
  fix M1 M2 :: R3
  obtain x1 y1 z1 x2 y2 z2 where MM: "(x1, y1, z1) = M1" "(x2, y2, z2) = M2"
    by (cases "M1", cases "M2", auto)
  show "dist_riemann_sphere_r3 M1 M2 = dist_riemann_sphere_r3 M2 M1"
    using norm_minus_cancel[of "(x1 - x2, y1 - y2, z1 - z2)"] MM[symmetric]
    by simp
qed

text \<open>Central theorem that connects the two metrics.\<close>
lemma dist_stereographic:
  shows "dist_riemann_sphere' M1 M2 = dist_fs (stereographic M1) (stereographic M2)"
proof (cases "M1 = North")
  case True
  hence "stereographic M1 = \<infinity>\<^sub>h"
    by (simp add: stereographic_North)
  show ?thesis
  proof (cases "M2 = North")
    case True
    show ?thesis
      using \<open>M1 = North\<close> \<open>M2 = North\<close>
      by auto
  next
    case False
    hence "stereographic M2 \<noteq> \<infinity>\<^sub>h"
      using stereographic_North[of M2]
      by simp
    then obtain m2 where "stereographic M2 = of_complex m2"
      using inf_or_of_complex[of "stereographic M2"]
      by auto
    show ?thesis
      using \<open>stereographic M2 = of_complex m2\<close> \<open>stereographic M1 = \<infinity>\<^sub>h\<close>
      using dist_fs_infinite1 dist_stereographic_infinite
      by (simp add: dist_fs_sym)
  qed
next
  case False
  hence "stereographic M1 \<noteq> \<infinity>\<^sub>h"
    by (simp add: stereographic_North)
  then obtain m1 where "stereographic M1 = of_complex m1"
    using inf_or_of_complex[of "stereographic M1"]
    by auto
  show ?thesis
  proof (cases "M2 = North")
    case True
    hence "stereographic M2 = \<infinity>\<^sub>h"
      by (simp add: stereographic_North)
    show ?thesis
      using \<open>stereographic M1 = of_complex m1\<close> \<open>stereographic M2 = \<infinity>\<^sub>h\<close>
      using dist_fs_infinite2 dist_stereographic_infinite
      by (subst dist_riemann_sphere_sym, simp add: dist_fs_sym)
  next
    case False
    hence "stereographic M2 \<noteq> \<infinity>\<^sub>h"
      by (simp add: stereographic_North)
    then obtain m2 where "stereographic M2 = of_complex m2"
      using inf_or_of_complex[of "stereographic M2"]
      by auto
    show ?thesis
      using \<open>stereographic M1 = of_complex m1\<close> \<open>stereographic M2 = of_complex m2\<close>
      using dist_fs_finite dist_stereographic_finite
      by simp
  qed
qed

text \<open>Other direction\<close>
lemma dist_stereographic':
  shows "dist_fs A B = dist_riemann_sphere' (inv_stereographic A) (inv_stereographic B)"
  by (subst dist_stereographic) (metis stereographic_inv_stereographic)

text \<open>The @{term riemann_sphere} equipped with @{term dist_riemann_sphere'} is a metric space, i.e.,
an instantiation of the @{term metric_space} locale.\<close>

instantiation riemann_sphere :: metric_space
begin
definition "dist_riemann_sphere = dist_riemann_sphere'"
definition "(uniformity_riemann_sphere :: (riemann_sphere \<times> riemann_sphere) filter) = (INF e\<in>{0<..}. principal {(x, y). dist_class.dist x y < e})"
definition "open_riemann_sphere (U :: riemann_sphere set) = (\<forall> x \<in> U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity)"
instance
proof
  fix x y :: riemann_sphere
  show "(dist_class.dist x y = 0) = (x = y)"
    unfolding dist_riemann_sphere_def
  proof transfer
    fix x y :: R3
    obtain x1 y1 z1 x2 y2 z2 where *: "(x1, y1, z1) = x" "(x2, y2, z2) = y"
      by (cases x, cases y, auto)
    assume "x \<in> unit_sphere" "y \<in> unit_sphere"
    thus "(dist_riemann_sphere_r3 x y = 0) = (x = y)"
      using norm_eq_zero[of "(x1 - y2, y1 - y2, z1 - z2)"] using *[symmetric]
      by (simp add: zero_prod_def)
  qed
next
  fix x y z :: riemann_sphere
  show "dist_class.dist x y \<le> dist_class.dist x z + dist_class.dist y z"
    unfolding dist_riemann_sphere_def
  proof transfer
    fix x y z :: R3
    obtain x1 y1 z1 x2 y2 z2 x3 y3 z3 where MM: "(x1, y1, z1) = x" "(x2, y2, z2) = y" "(x3, y3, z3) = z"
      by (cases "x", cases "y", cases "z", auto)

    assume "x \<in> unit_sphere" "y \<in> unit_sphere" "z \<in> unit_sphere"
    thus "dist_riemann_sphere_r3 x y \<le> dist_riemann_sphere_r3 x z + dist_riemann_sphere_r3 y z"
      using MM[symmetric] norm_minus_cancel[of "(x3 - x2, y3 - y2, z3 - z2)"] norm_triangle_ineq[of "(x1 - x3, y1 - y3, z1 - z3)" "(x3 - x2, y3 - y2, z3 - z2)"]
      by simp
  qed
qed (simp_all add: uniformity_riemann_sphere_def open_riemann_sphere_def)
end

text \<open>The @{term riemann_sphere} metric space is perfect, i.e., it does not have isolated points.\<close>
instantiation riemann_sphere :: perfect_space
begin
instance proof
  fix M :: riemann_sphere
  show "\<not> open {M}"
    unfolding open_dist dist_riemann_sphere_def
    apply (subst dist_riemann_sphere_sym)
  proof transfer
    fix M
    assume "M \<in> unit_sphere"
    obtain x y z where MM: "M = (x, y, z)"
      by (cases "M") auto
    then obtain \<alpha> \<beta> where *: "x = cos \<alpha> * cos \<beta>" "y = cos \<alpha> * sin \<beta>" "z = sin \<alpha>" "-pi / 2 \<le> \<alpha> \<and> \<alpha> \<le> pi / 2"
      using \<open>M \<in> unit_sphere\<close>
      using ex_sphere_params[of x y z]
      by auto
    have "\<And> e. e > 0 \<Longrightarrow> (\<exists>y. y \<in> unit_sphere \<and> dist_riemann_sphere_r3 M y < e \<and> y \<noteq> M)"
    proof-
      fix e :: real
      assume "e > 0"
      then obtain \<alpha>' where "1 - (e*e/2) < cos (\<alpha> - \<alpha>')" "\<alpha> \<noteq> \<alpha>'" "-pi/2 \<le> \<alpha>'" "\<alpha>' \<le> pi/2"
        using ex_cos_gt[of \<alpha> "1 - (e*e/2)"] \<open>- pi / 2 \<le> \<alpha> \<and> \<alpha> \<le> pi / 2\<close>
        by auto
      hence "sin \<alpha> \<noteq> sin \<alpha>'"
        using \<open>-pi / 2 \<le> \<alpha> \<and> \<alpha> \<le> pi / 2\<close> sin_inj[of \<alpha> \<alpha>']
        by auto

      have "2 - 2 * cos (\<alpha> - \<alpha>') < e*e"
        using mult_strict_right_mono[OF \<open>1 - (e*e/2) < cos (\<alpha> - \<alpha>')\<close>, of 2]
        by (simp add: field_simps)
      have "2 - 2 * cos (\<alpha> - \<alpha>') \<ge> 0"
        using cos_le_one[of "\<alpha> - \<alpha>'"]
        by (simp add: algebra_split_simps)
      let ?M' = "(cos \<alpha>' * cos \<beta>,  cos \<alpha>' * sin \<beta>, sin \<alpha>')"
      have "dist_riemann_sphere_r3 M ?M' = sqrt ((cos \<alpha> - cos \<alpha>')\<^sup>2 + (sin \<alpha> - sin \<alpha>')\<^sup>2)"
        using MM * sphere_params_on_sphere[of _ \<alpha>' \<beta>]
        using sin_cos_squared_add[of \<beta>]
        apply (simp add: dist_riemann_sphere'_def Abs_riemann_sphere_inverse norm_prod_def)
        apply (subst left_diff_distrib[symmetric])+
        apply (subst power_mult_distrib)+
        apply (subst distrib_left[symmetric])
        apply simp
        done
      also have "... = sqrt (2 - 2*cos (\<alpha> - \<alpha>'))"
        by (simp add: power2_eq_square field_simps cos_diff)
      finally
      have "(dist_riemann_sphere_r3 M ?M')\<^sup>2 = 2 - 2*cos (\<alpha> - \<alpha>')"
        using \<open>2 - 2 * cos (\<alpha> - \<alpha>') \<ge> 0\<close>
        by simp
      hence "(dist_riemann_sphere_r3 M ?M')\<^sup>2 < e\<^sup>2"
        using \<open>2 - 2 * cos (\<alpha> - \<alpha>') < e*e\<close>
        by (simp add: power2_eq_square)
      hence "dist_riemann_sphere_r3 M ?M' < e"
        apply (rule power2_less_imp_less)
        using \<open>e > 0\<close>
        by simp
      moreover
      have "M \<noteq> ?M'"
        using MM  \<open>sin \<alpha> \<noteq> sin \<alpha>'\<close> *
        by simp
      moreover
      have "?M' \<in> unit_sphere"
        using sphere_params_on_sphere by auto
      ultimately
      show "\<exists>y. y \<in> unit_sphere \<and> dist_riemann_sphere_r3 M y < e \<and> y \<noteq> M"
        unfolding dist_riemann_sphere_def
        by (rule_tac x="?M'" in exI, simp)
    qed
    thus "\<not> (\<forall>x\<in>{M}. \<exists>e>0. \<forall>y\<in>{x. x \<in> unit_sphere}. dist_riemann_sphere_r3 x y < e \<longrightarrow> y \<in> {M})"
      by auto
  qed
qed
end

text \<open>The @{term complex_homo} metric space is perfect, i.e., it does not have isolated points.\<close>
instantiation complex_homo :: perfect_space
begin
instance proof
  fix x::complex_homo
  show "\<not> open {x}"
    unfolding open_dist
  proof (auto)
    fix e::real
    assume "e > 0"
    thus "\<exists> y. dist_class.dist y x < e \<and> y \<noteq> x"
      using not_open_singleton[of "inv_stereographic x"]
      unfolding open_dist
      unfolding dist_complex_homo_def dist_riemann_sphere_def
      apply (subst dist_stereographic', auto)
      apply (erule_tac x=e in allE, auto)
      apply (rule_tac x="stereographic y" in exI, auto)
      done
  qed
qed

end

lemma Lim_within:
  shows "(f \<longlongrightarrow> l) (at a within S) \<longleftrightarrow>
    (\<forall>e >0. \<exists>d>0. \<forall>x \<in> S. 0 < dist_class.dist x a \<and> dist_class.dist x a  < d \<longrightarrow> dist_class.dist (f x) l < e)"
  by (auto simp: tendsto_iff eventually_at)

lemma continuous_on_iff:
  shows "continuous_on s f \<longleftrightarrow>
    (\<forall>x\<in>s. \<forall>e>0. \<exists>d>0. \<forall>x'\<in>s. dist_class.dist x' x < d \<longrightarrow> dist_class.dist (f x') (f x) < e)"
  unfolding continuous_on_def Lim_within
  by (metis dist_pos_lt dist_self)

text \<open>Using the chordal metric in the extended plane, and the Euclidean metric on the sphere in
$\mathbb{R}^3$, the stereographic and inverse stereographic projections are proved to be
continuous.\<close>

lemma "continuous_on UNIV stereographic"
unfolding continuous_on_iff
unfolding dist_complex_homo_def dist_riemann_sphere_def
by (subst dist_stereographic', auto)

lemma "continuous_on UNIV inv_stereographic"
unfolding continuous_on_iff
unfolding dist_complex_homo_def dist_riemann_sphere_def
by (subst dist_stereographic, auto)

(* -------------------------------------------------------------------------- *)
subsubsection \<open>Chordal circles\<close>
(* -------------------------------------------------------------------------- *)

text \<open>Real circlines are sets of points that are equidistant from some given point in the chordal
metric. There are exactly two such points (two chordal centers). On the Riemann sphere, these two
points are obtained as intersections of the sphere and a line that goes trough center of the circle,
and its orthogonal to its plane.\<close>

text \<open>The circline for the given chordal center and radius.\<close>
definition chordal_circle_cvec_cmat :: "complex_vec \<Rightarrow> real \<Rightarrow> complex_mat" where
 [simp]: "chordal_circle_cvec_cmat a r =
           (let (a1, a2) = a
             in ((4*a2*cnj a2 - (cor r)\<^sup>2*(a1*cnj a1 + a2*cnj a2)), (-4*a1*cnj a2), (-4*cnj a1*a2), (4*a1*cnj a1 - (cor r)\<^sup>2*(a1*cnj a1 + a2*cnj a2))))"

lemma chordal_circle_cmat_hermitean_nonzero [simp]:
  assumes "a \<noteq> vec_zero"
  shows "chordal_circle_cvec_cmat a r \<in> hermitean_nonzero"
  using assms
  by (cases a) (auto simp add: hermitean_def mat_adj_def mat_cnj_def Let_def)

lift_definition chordal_circle_hcoords_clmat :: "complex_homo_coords \<Rightarrow> real \<Rightarrow> circline_mat" is chordal_circle_cvec_cmat
  using chordal_circle_cmat_hermitean_nonzero
  by (simp del: chordal_circle_cvec_cmat_def)

lift_definition chordal_circle :: "complex_homo \<Rightarrow> real \<Rightarrow> circline" is chordal_circle_hcoords_clmat
proof transfer
  fix a b :: complex_vec and r :: real
  assume *: "a \<noteq> vec_zero" "b \<noteq> vec_zero"
  obtain a1 a2 where aa: "a = (a1, a2)"
    by (cases a, auto)
  obtain b1 b2 where bb: "b = (b1, b2)"
    by (cases b, auto)
  assume "a \<approx>\<^sub>v b"
  then obtain k where "b = (k * a1, k * a2)" "k \<noteq> 0"
    using aa bb
    by auto
  moreover
  have "cor (Re (k * cnj k)) = k * cnj k"
    by (metis complex_In_mult_cnj_zero complex_of_real_Re)
  ultimately
  show "circline_eq_cmat (chordal_circle_cvec_cmat a r) (chordal_circle_cvec_cmat b r)"
    using * aa bb
    by simp (rule_tac x="Re (k*cnj k)" in exI, auto simp add: Let_def field_simps)
qed

lemma sqrt_1_plus_square:
  shows "sqrt (1 + a\<^sup>2) \<noteq> 0"
  by (smt real_sqrt_less_mono real_sqrt_zero realpow_square_minus_le)

lemma
  assumes "dist_fs z a = r"
  shows "z \<in> circline_set (chordal_circle a r)"
proof (cases "a \<noteq> \<infinity>\<^sub>h")
  case True
  then obtain a' where  "a = of_complex a'"
    using inf_or_of_complex
    by auto
  let ?A = "4 - (cor r)\<^sup>2 * (1 + (a'*cnj a'))" and ?B = "-4*a'" and ?C="-4*cnj a'" and ?D = "4*a'*cnj a' -  (cor r)\<^sup>2 * (1 + (a'*cnj a'))"
  have hh: "(?A, ?B, ?C, ?D) \<in> {H. hermitean H \<and> H \<noteq> mat_zero}"
    by (auto simp add: hermitean_def mat_adj_def mat_cnj_def power2_eq_square)
  hence *: "chordal_circle (of_complex a') r = mk_circline ?A ?B ?C ?D"
    by (transfer, transfer, simp, rule_tac x=1 in exI, simp)

  show ?thesis
  proof (cases "z \<noteq> \<infinity>\<^sub>h")
    case True
    then obtain z' where "z = of_complex z'"
      using inf_or_of_complex[of z] inf_or_of_complex[of a]
      by auto
    have "2 * cmod (z' - a') / (sqrt (1 + (cmod z')\<^sup>2) * sqrt (1 + (cmod a')\<^sup>2)) = r"
      using dist_fs_finite[of z' a'] assms \<open>z = of_complex z'\<close> \<open>a = of_complex a'\<close>
      by auto
    hence "4 * (cmod (z' - a'))\<^sup>2 / ((1 + (cmod z')\<^sup>2) * (1 + (cmod a')\<^sup>2)) = r\<^sup>2 "
      by (auto simp add: field_simps)
    moreover
    have "sqrt (1 + (cmod z')\<^sup>2) \<noteq> 0" "sqrt (1 + (cmod a')\<^sup>2) \<noteq> 0"
      using sqrt_1_plus_square
      by simp+
    hence "(1 + (cmod z')\<^sup>2) * (1 + (cmod a')\<^sup>2) \<noteq> 0"
      by simp
    ultimately
    have "4 * (cmod (z' - a'))\<^sup>2  = r\<^sup>2 * ((1 + (cmod z')\<^sup>2) * (1 + (cmod a')\<^sup>2))"
      by (simp add: field_simps)
    hence "4 * Re ((z' - a')*cnj (z' - a')) = r\<^sup>2 * (1 + Re (z'*cnj z')) * (1 + Re (a'*cnj a'))"
      by ((subst cmod_square[symmetric])+, simp)
    hence "4 * (Re(z'*cnj z') - Re(a'*cnj z') - Re(cnj a'*z') + Re(a'*cnj a')) = r\<^sup>2 * (1 + Re (z'*cnj z')) * (1 + Re (a'*cnj a'))"
      by (simp add: field_simps)
    hence "Re (?A * z' * cnj z' + ?B * cnj z' + ?C * z' + ?D) = 0"
      by (simp add: power2_eq_square field_simps)
    hence "?A * z' * cnj z' + ?B * cnj z' + ?C * z' + ?D = 0"
      by (subst complex_eq_if_Re_eq) (auto simp add: power2_eq_square)
    hence "(cnj z' * ?A + ?C) * z' + (cnj z' * ?B + ?D) = 0"
      by algebra
    hence "z \<in> circline_set (mk_circline ?A ?B ?C ?D)"
      using \<open>z = of_complex z'\<close> hh
      unfolding circline_set_def
      by simp (transfer, transfer, simp add: vec_cnj_def)
    thus ?thesis
      using *
      by (subst \<open>a = of_complex a'\<close>) simp
  next
    case False
    hence "2 / sqrt (1 + (cmod a')\<^sup>2) = r"
      using assms \<open>a = of_complex a'\<close>
      using dist_fs_infinite2[of a']
      by simp
    moreover
    have "sqrt (1 + (cmod a')\<^sup>2) \<noteq> 0"
      using sqrt_1_plus_square
      by simp
    ultimately
    have "2 = r * sqrt (1 + (cmod a')\<^sup>2)"
      by (simp add: field_simps)
    hence "4 = (r * sqrt (1 + (cmod a')\<^sup>2))\<^sup>2"
      by simp
    hence "4 = r\<^sup>2 * (1 + (cmod a')\<^sup>2)"
      by (simp add: power_mult_distrib)
    hence "Re (4 - (cor r)\<^sup>2 * (1 + (a' * cnj a'))) = 0"
      by (subst (asm) cmod_square) (simp add: field_simps power2_eq_square)
    hence "4 - (cor r)\<^sup>2 * (1 + (a'*cnj a')) = 0"
      by (subst complex_eq_if_Re_eq) (auto simp add: power2_eq_square)
    hence "circline_A0 (mk_circline ?A ?B ?C ?D)"
      using hh
      by (simp, transfer, transfer, simp)
    hence "z \<in> circline_set (mk_circline ?A ?B ?C ?D)"
      using inf_in_circline_set[of "mk_circline ?A ?B ?C ?D"]
      using \<open>\<not> z \<noteq> \<infinity>\<^sub>h\<close>
      by simp
    thus ?thesis
      using *
      by (subst \<open>a = of_complex a'\<close>) simp
  qed
next
  case False
  let ?A = "-(cor r)\<^sup>2" and ?B = "0" and ?C = "0" and ?D = "4 -(cor r)\<^sup>2"
  have hh: "(?A, ?B, ?C, ?D) \<in> {H. hermitean H \<and> H \<noteq> mat_zero}"
    by (auto simp add: hermitean_def mat_adj_def mat_cnj_def power2_eq_square)
  hence *: "chordal_circle a r = mk_circline ?A ?B ?C ?D"
    using \<open>\<not> a \<noteq> \<infinity>\<^sub>h\<close>
    by simp (transfer, transfer, simp, rule_tac x=1 in exI, simp)

  show ?thesis
  proof (cases "z = \<infinity>\<^sub>h")
    case True
    show ?thesis
      using assms \<open>z = \<infinity>\<^sub>h\<close> \<open>\<not> a \<noteq> \<infinity>\<^sub>h\<close>
      using * hh
      by (simp, subst inf_in_circline_set, transfer, transfer, simp)
  next
    case False
    then obtain z' where "z = of_complex z'"
      using inf_or_of_complex[of z]
      by auto
    have "2 / sqrt (1 + (cmod z')\<^sup>2) = r"
      using assms \<open>z = of_complex z'\<close>\<open>\<not> a \<noteq> \<infinity>\<^sub>h\<close>
      using dist_fs_infinite2[of z']
      by (simp add: dist_fs_sym)
    moreover
    have "sqrt (1 + (cmod z')\<^sup>2) \<noteq> 0"
      using sqrt_1_plus_square
      by simp
    ultimately
    have "2 = r * sqrt (1 + (cmod z')\<^sup>2)"
      by (simp add: field_simps)
    hence "4 = (r * sqrt (1 + (cmod z')\<^sup>2))\<^sup>2"
      by simp
    hence "4 = r\<^sup>2 * (1 + (cmod z')\<^sup>2)"
      by (simp add: power_mult_distrib)
    hence "Re (4 - (cor r)\<^sup>2 * (1 + (z' * cnj z'))) = 0"
      by (subst (asm) cmod_square) (simp add: field_simps power2_eq_square)
    hence "- (cor r)\<^sup>2 * z'*cnj z' + 4 - (cor r)\<^sup>2 = 0"
      by (subst complex_eq_if_Re_eq) (auto simp add: power2_eq_square field_simps)
    hence "z \<in> circline_set (mk_circline ?A ?B ?C ?D)"
      using hh
      unfolding circline_set_def
      by (subst \<open>z = of_complex z'\<close>, simp) (transfer, transfer, auto simp add: vec_cnj_def field_simps)
    thus ?thesis
      using *
      by simp
  qed
qed

lemma
  assumes "z \<in> circline_set (chordal_circle a r)" and "r \<ge> 0"
  shows "dist_fs z a = r"
proof (cases "a = \<infinity>\<^sub>h")
  case False
  then obtain a' where "a = of_complex a'"
    using inf_or_of_complex
    by auto

  let ?A = "4 - (cor r)\<^sup>2 * (1 + (a'*cnj a'))" and ?B = "-4*a'" and ?C="-4*cnj a'" and ?D = "4*a'*cnj a' -  (cor r)\<^sup>2 * (1 + (a'*cnj a'))"
  have hh: "(?A, ?B, ?C, ?D) \<in> {H. hermitean H \<and> H \<noteq> mat_zero}"
    by (auto simp add: hermitean_def mat_adj_def mat_cnj_def power2_eq_square)
  hence *: "chordal_circle (of_complex a') r = mk_circline ?A ?B ?C ?D"
    by (transfer, transfer, simp, rule_tac x=1 in exI, simp)

  show ?thesis
  proof (cases "z = \<infinity>\<^sub>h")
    case False
    then obtain z' where "z = of_complex z'"
      using inf_or_of_complex[of z] inf_or_of_complex[of a]
      by auto
    hence "z \<in> circline_set (mk_circline ?A ?B ?C ?D)"
      using assms \<open>a = of_complex a'\<close> *
      by simp
    hence "(cnj z' * ?A + ?C) * z' + (cnj z' * ?B + ?D) = 0"
      using hh
      unfolding circline_set_def
      by (subst (asm) \<open>z = of_complex z'\<close>, simp) (transfer, transfer, simp add: vec_cnj_def)
    hence "?A * z' * cnj z' + ?B * cnj z' + ?C * z' + ?D = 0"
      by algebra
    hence "Re (?A * z' * cnj z' + ?B * cnj z' +?C * z' +?D) = 0"
      by (simp add: power2_eq_square field_simps)
    hence "4 * Re ((z' - a')*cnj (z' - a')) = r\<^sup>2 * (1 + Re (z'*cnj z')) * (1 + Re (a'*cnj a'))"
      by (simp add: field_simps power2_eq_square)
    hence "4 * (cmod (z' - a'))\<^sup>2  = r\<^sup>2 * ((1 + (cmod z')\<^sup>2) * (1 + (cmod a')\<^sup>2))"
      by (subst cmod_square)+ simp
    moreover
    have "sqrt (1 + (cmod z')\<^sup>2) \<noteq> 0" "sqrt (1 + (cmod a')\<^sup>2) \<noteq> 0"
      using sqrt_1_plus_square
      by simp+
    hence "(1 + (cmod z')\<^sup>2) * (1 + (cmod a')\<^sup>2) \<noteq> 0"
      by simp
    ultimately
    have "4 * (cmod (z' - a'))\<^sup>2 / ((1 + (cmod z')\<^sup>2) * (1 + (cmod a')\<^sup>2)) = r\<^sup>2 "
      by (simp add: field_simps)
    hence "2 * cmod (z' - a') / (sqrt (1 + (cmod z')\<^sup>2) * sqrt (1 + (cmod a')\<^sup>2)) = r"
      using \<open>r \<ge> 0\<close>
      by (subst (asm) real_sqrt_eq_iff[symmetric]) (simp add: real_sqrt_mult real_sqrt_divide)
    thus ?thesis
      using \<open>z = of_complex z'\<close> \<open>a = of_complex a'\<close>
      using dist_fs_finite[of z' a']
      by simp
  next
    case True
    have "z \<in> circline_set (mk_circline ?A ?B ?C ?D)"
      using assms \<open>a = of_complex a'\<close> *
      by simp
    hence "circline_A0 (mk_circline ?A ?B ?C ?D)"
      using inf_in_circline_set[of "mk_circline ?A ?B ?C ?D"]
      using \<open>z = \<infinity>\<^sub>h\<close>
      by simp
    hence "4 - (cor r)\<^sup>2 * (1 + (a'*cnj a')) = 0"
      using hh
      by (transfer, transfer, simp)
    hence "Re (4 - (cor r)\<^sup>2 * (1 + (a' * cnj a'))) = 0"
      by simp
    hence "4 = r\<^sup>2 * (1 + (cmod a')\<^sup>2)"
      by (subst cmod_square) (simp add: power2_eq_square)
    hence "2 = r * sqrt (1 + (cmod a')\<^sup>2)"
      using \<open>r \<ge> 0\<close>
      by (subst (asm) real_sqrt_eq_iff[symmetric]) (simp add: real_sqrt_mult)
    moreover
    have "sqrt (1 + (cmod a')\<^sup>2) \<noteq> 0"
      using sqrt_1_plus_square
      by simp
    ultimately
    have "2 / sqrt (1 + (cmod a')\<^sup>2) = r"
      by (simp add: field_simps)
    thus ?thesis
      using \<open>a = of_complex a'\<close> \<open>z = \<infinity>\<^sub>h\<close>
      using dist_fs_infinite2[of a']
      by simp
  qed
next
  case True
  let ?A = "-(cor r)\<^sup>2" and ?B = "0" and ?C = "0" and ?D = "4 -(cor r)\<^sup>2"
  have hh: "(?A, ?B, ?C, ?D) \<in> {H. hermitean H \<and> H \<noteq> mat_zero}"
    by (auto simp add: hermitean_def mat_adj_def mat_cnj_def power2_eq_square)
  hence *: "chordal_circle a r = mk_circline ?A ?B ?C ?D"
    using \<open>a = \<infinity>\<^sub>h\<close>
    by simp (transfer, transfer, simp, rule_tac x=1 in exI, simp)

  show ?thesis
  proof (cases "z = \<infinity>\<^sub>h")
    case True
    thus ?thesis
      using \<open>a = \<infinity>\<^sub>h\<close> assms * hh
      by simp (subst (asm) inf_in_circline_set, transfer, transfer, simp)
  next
    case False
    then obtain z' where "z = of_complex z'"
      using inf_or_of_complex
      by auto
    hence "z \<in> circline_set (mk_circline ?A ?B ?C ?D)"
      using assms *
      by simp
    hence "- (cor r)\<^sup>2 * z'*cnj z' + 4 - (cor r)\<^sup>2 = 0"
      using hh
      unfolding circline_set_def
      apply (subst (asm) \<open>z = of_complex z'\<close>)
      by (simp, transfer, transfer, simp add: vec_cnj_def, algebra)
    hence "4 - (cor r)\<^sup>2 * (1 + (z'*cnj z')) = 0"
      by (simp add: field_simps)
    hence "Re (4 - (cor r)\<^sup>2 * (1 + (z' * cnj z'))) = 0"
      by simp
    hence "4 = r\<^sup>2 * (1 + (cmod z')\<^sup>2)"
      by (subst cmod_square) (simp add: power2_eq_square)
    hence "2 = r * sqrt (1 + (cmod z')\<^sup>2)"
      using \<open>r \<ge> 0\<close>
      by (subst (asm) real_sqrt_eq_iff[symmetric]) (simp add: real_sqrt_mult)
    moreover
    have "sqrt (1 + (cmod z')\<^sup>2) \<noteq> 0"
      using sqrt_1_plus_square
      by simp
    ultimately
    have "2 / sqrt (1 + (cmod z')\<^sup>2) = r"
      by (simp add: field_simps)
    thus ?thesis
      using \<open>z = of_complex z'\<close> \<open>a = \<infinity>\<^sub>h\<close>
      using dist_fs_infinite2[of z']
      by (simp add: dist_fs_sym)
  qed
qed

text \<open>Two chordal centers and radii for the given circline\<close>
definition chordal_circles_cmat :: "complex_mat \<Rightarrow> (complex \<times> real) \<times> (complex \<times> real)"  where
 [simp]: "chordal_circles_cmat H =
     (let (A, B, C, D) = H;
          dsc = sqrt(Re ((D-A)\<^sup>2 + 4 * (B*cnj B)));
          a1 = (A - D + cor dsc) / (2 * C);
          r1 = sqrt((4 - Re((-4 * a1/B) * A)) / (1 + Re (a1*cnj a1)));
          a2 = (A - D - cor dsc) / (2 * C);
          r2 = sqrt((4 - Re((-4 * a2/B) * A)) / (1 + Re (a2*cnj a2)))
       in ((a1, r1), (a2, r2)))"

lift_definition chordal_circles_clmat :: "circline_mat \<Rightarrow> (complex \<times> real) \<times> (complex \<times> real)" is chordal_circles_cmat
  done

lift_definition chordal_circles :: "ocircline \<Rightarrow> (complex \<times> real) \<times> (complex \<times> real)" is chordal_circles_clmat
proof transfer
  fix H1 H2 :: complex_mat
  obtain A1 B1 C1 D1 where hh1: "(A1, B1, C1, D1) = H1"
    by (cases H1) auto
  obtain A2 B2 C2 D2 where hh2: "(A2, B2, C2, D2) = H2"
    by (cases H2) auto

  assume "ocircline_eq_cmat H1 H2"
  then obtain k where *: "k > 0" "A2 = cor k * A1" "B2 = cor k * B1" "C2 = cor k * C1" "D2 = cor k * D1"
    using hh1[symmetric] hh2[symmetric]
    by auto
  let ?dsc1 = "sqrt (Re ((D1 - A1)\<^sup>2 + 4 * (B1 * cnj B1)))" and ?dsc2 = "sqrt (Re ((D2 - A2)\<^sup>2 + 4 * (B2 * cnj B2)))"
  let ?a11 = "(A1 - D1 + cor ?dsc1) / (2 * C1)" and ?a12 = "(A2 - D2 + cor ?dsc2) / (2 * C2)"
  let ?a21 = "(A1 - D1 - cor ?dsc1) / (2 * C1)" and ?a22 = "(A2 - D2 - cor ?dsc2) / (2 * C2)"
  let ?r11 = "sqrt((4 - Re((-4 * ?a11/B1) * A1)) / (1 + Re (?a11*cnj ?a11)))"
  let ?r12 = "sqrt((4 - Re((-4 * ?a12/B2) * A2)) / (1 + Re (?a12*cnj ?a12)))"
  let ?r21 = "sqrt((4 - Re((-4 * ?a21/B1) * A1)) / (1 + Re (?a21*cnj ?a21)))"
  let ?r22 = "sqrt((4 - Re((-4 * ?a22/B2) * A2)) / (1 + Re (?a22*cnj ?a22)))"

  have "Re ((D2 - A2)\<^sup>2 + 4 * (B2 * cnj B2)) = k\<^sup>2 * Re ((D1 - A1)\<^sup>2 + 4 * (B1 * cnj B1))"
    using *
    by (simp add: power2_eq_square field_simps)
  hence "?dsc2 = k * ?dsc1"
    using \<open>k > 0\<close>
    by (simp add: real_sqrt_mult)
  hence "A2 - D2 + cor ?dsc2 = cor k * (A1 - D1 + cor ?dsc1)" "A2 - D2 - cor ?dsc2 = cor k * (A1 - D1 - cor ?dsc1)" "2*C2 = cor k * (2*C1)"
    using *
    by (auto simp add: field_simps)
  hence "?a12 = ?a11" "?a22 = ?a21"
    using \<open>k > 0\<close>
    by simp_all
  moreover
  have "Re((-4 * ?a12/B2) * A2) = Re((-4 * ?a11/B1) * A1)"
    using *
    by (subst \<open>?a12 = ?a11\<close>) (simp, simp add: field_simps)
  have "?r12 = ?r11"
    by (subst \<open>Re((-4 * ?a12/B2) * A2) = Re((-4 * ?a11/B1) * A1)\<close>, (subst \<open>?a12 = ?a11\<close>)+) simp
  moreover
  have "Re((-4 * ?a22/B2) * A2) = Re((-4 * ?a21/B1) * A1)"
    using *
    by (subst \<open>?a22 = ?a21\<close>) (simp, simp add: field_simps)
  have "?r22 = ?r21"
    by (subst \<open>Re((-4 * ?a22/B2) * A2) = Re((-4 * ?a21/B1) * A1)\<close>, (subst \<open>?a22 = ?a21\<close>)+) simp
  moreover
  have "chordal_circles_cmat H1 = ((?a11, ?r11), (?a21, ?r21))"
    using hh1[symmetric]
    unfolding chordal_circles_cmat_def Let_def
    by (simp del: times_complex.sel)
  moreover
  have "chordal_circles_cmat H2 = ((?a12, ?r12), (?a22, ?r22))"
    using hh2[symmetric]
    unfolding chordal_circles_cmat_def Let_def
    by (simp del: times_complex.sel)
  ultimately
  show "chordal_circles_cmat H1 = chordal_circles_cmat H2"
    by metis
qed

lemma chordal_circle_radius_positive:
  assumes "hermitean (A, B, C, D)" and "Re (mat_det (A, B, C, D)) \<le> 0" and "B \<noteq> 0" and
  "dsc = sqrt(Re ((D-A)\<^sup>2 + 4 * (B*cnj B)))" and 
  "a1 = (A - D + cor dsc) / (2 * C)" and "a2 = (A - D - cor dsc) / (2 * C)"
  shows "Re (A*a1/B) \<ge> -1 \<and> Re (A*a2/B) \<ge> -1"
proof-
  from assms have "is_real A" "is_real D" "C = cnj B"
    using hermitean_elems
    by auto
  have *: "A*a1/B = ((A - D + cor dsc) / (2 * (B * cnj B))) * A"
    using \<open>B \<noteq> 0\<close> \<open>C = cnj B\<close> \<open>a1 = (A - D + cor dsc) / (2 * C)\<close>
    by (simp add: field_simps) algebra
  have **: "A*a2/B = ((A - D - cor dsc) / (2 * (B * cnj B))) * A"
    using \<open>B \<noteq> 0\<close> \<open>C = cnj B\<close> \<open>a2 = (A - D - cor dsc) / (2 * C)\<close>
    by (simp add: field_simps) algebra
  have "dsc \<ge> 0"
  proof-
    have "0 \<le> Re ((D - A)\<^sup>2) + 4 * Re ((cor (cmod B))\<^sup>2)"
      using \<open>is_real A\<close> \<open>is_real D\<close>
      by (subst cor_squared, subst Re_complex_of_real) (simp add: power2_eq_square)
    thus ?thesis
      using \<open>dsc = sqrt(Re ((D-A)\<^sup>2 + 4*(B*cnj B)))\<close>
      by (subst (asm) complex_mult_cnj_cmod) simp
  qed
  hence "Re (A - D - cor dsc) \<le> Re (A - D + cor dsc)"
    by simp
  moreover
  have "Re (2 * (B * cnj B)) > 0"
    using \<open>B \<noteq> 0\<close>
    by (subst complex_mult_cnj_cmod, simp add: power2_eq_square)
  ultimately
  have xxx: "Re (A - D + cor dsc) / Re (2 * (B * cnj B)) \<ge> Re (A - D - cor dsc) / Re (2 * (B * cnj B))" (is "?lhs \<ge> ?rhs")
    by (metis divide_right_mono less_eq_real_def)

  have "Re A * Re D \<le> Re (B*cnj B)"
    using \<open>Re (mat_det (A, B, C, D)) \<le> 0\<close> \<open>C = cnj B\<close> \<open>is_real A\<close> \<open>is_real D\<close>
    by simp


  have "(Re (2 * (B * cnj B)) / Re A) / Re (2 * B * cnj B) = 1 / Re A"
    using \<open>Re (2 * (B * cnj B)) > 0\<close>
    apply (subst divide_divide_eq_left)
    apply (subst mult.assoc)
    apply (subst nonzero_divide_mult_cancel_right)
    by simp_all

  show ?thesis
  proof (cases "Re A > 0")
    case True
    hence "Re (A*a1/B) \<ge> Re (A*a2/B)"
      using * ** \<open>Re (2 * (B * cnj B)) > 0\<close> \<open>B \<noteq> 0\<close> \<open>is_real A\<close> \<open>is_real D\<close> xxx
      using mult_right_mono[of ?rhs ?lhs "Re A"]
      apply simp
      apply (subst Re_divide_real, simp, simp)
      apply (subst Re_divide_real, simp, simp)
      apply (subst Re_mult_real, simp)+
      apply simp
      done
    moreover
    have "Re (A*a2/B) \<ge> -1"
    proof-
      from \<open>Re A * Re D \<le> Re (B*cnj B)\<close>
      have "Re (A\<^sup>2) \<le> Re (B*cnj B) + Re ((A - D)*A)"
        using \<open>Re A > 0\<close> \<open>is_real A\<close> \<open>is_real D\<close>
        by (simp add: power2_eq_square field_simps)
      have "1 \<le> Re (B*cnj B) / Re (A\<^sup>2) + Re (A - D) / Re A"
        using \<open>Re A > 0\<close> \<open>is_real A\<close> \<open>is_real D\<close>
        using divide_right_mono[OF \<open>Re (A\<^sup>2) \<le> Re (B*cnj B) + Re ((A - D)*A)\<close>, of "Re (A\<^sup>2)"]
        by (simp add: power2_eq_square add_divide_distrib)
      have "4 * Re(B*cnj B) \<le> 4 * (Re (B*cnj B))\<^sup>2 / Re (A\<^sup>2)  + 2*Re (A - D) / Re A * 2 * Re(B*cnj B)"
        using mult_right_mono[OF \<open>1 \<le> Re (B*cnj B) / Re (A\<^sup>2) + Re (A - D) / Re A\<close>, of "4 * Re (B*cnj B)"]
        by (simp add: distrib_right) (simp add: power2_eq_square field_simps)
      moreover
      have "A \<noteq> 0"
        using \<open>Re A > 0\<close>
        by auto
      hence "4 * (Re (B*cnj B))\<^sup>2 / Re (A\<^sup>2) = Re (4 * (B*cnj B)\<^sup>2 / A\<^sup>2)"
        using Re_divide_real[of "A\<^sup>2" "4 * (B*cnj B)\<^sup>2"] \<open>Re A > 0\<close> \<open>is_real A\<close>
        by (auto simp add: power2_eq_square)
      moreover
      have "2*Re (A - D) / Re A * 2 * Re(B*cnj B) = Re (2 * (A - D) / A * 2 * B * cnj B)"
        using \<open>is_real A\<close> \<open>is_real D\<close> \<open>A \<noteq> 0\<close>
        using Re_divide_real[of "A" "(4 * A - 4 * D) * B * cnj B"]
        by (simp add: field_simps)
      ultimately
      have "Re ((D - A)\<^sup>2 + 4 * B*cnj B) \<le> Re((A - D)\<^sup>2 + 4 * (B*cnj B)\<^sup>2 / A\<^sup>2  + 2*(A - D) / A * 2 * B*cnj B)"
        by (simp add: field_simps power2_eq_square)
      hence "Re ((D - A)\<^sup>2 + 4 * B*cnj B) \<le> Re(((A - D) +  2 * B*cnj B / A)\<^sup>2)"
        using \<open>A \<noteq> 0\<close>
        by (subst power2_sum) (simp add: power2_eq_square field_simps)
      hence "dsc \<le> sqrt (Re(((A - D) +  2 * B*cnj B / A)\<^sup>2))"
        using \<open>dsc = sqrt(Re ((D-A)\<^sup>2 + 4*(B*cnj B)))\<close>
        by simp
      moreover
      have "Re(((A - D) +  2 * B*cnj B / A)\<^sup>2) = (Re((A - D) +  2 * B*cnj B / A))\<^sup>2"
        using \<open>is_real A\<close> \<open>is_real D\<close> div_reals
        by (simp add: power2_eq_square)
      ultimately
      have "dsc \<le> \<bar>Re (A - D + 2 * B * cnj B / A)\<bar>"
        by simp
      moreover
      have "Re (A - D + 2 * B * cnj B / A) \<ge> 0"
      proof-
        have *: "Re (A\<^sup>2 + B*cnj B) \<ge> 0"
          using \<open>is_real A\<close>
          by (simp add: power2_eq_square)
        also have "Re (A\<^sup>2 + 2*B*cnj B - A*D) \<ge> Re (A\<^sup>2 + B*cnj B)"
          using \<open>Re A * Re D \<le> Re (B*cnj B)\<close>
          using \<open>is_real A\<close> \<open>is_real D\<close>
          by simp
        finally
        have "Re (A\<^sup>2 + 2*B*cnj B - A*D) \<ge> 0"
          by simp
        show ?thesis
          using divide_right_mono[OF \<open>Re (A\<^sup>2 + 2*B*cnj B - A*D) \<ge> 0\<close>, of "Re A"] \<open>Re A > 0\<close> \<open>is_real A\<close> \<open>A \<noteq> 0\<close>
          by (simp add: add_divide_distrib diff_divide_distrib) (subst Re_divide_real, auto simp add: power2_eq_square field_simps)
      qed
      ultimately
      have "dsc \<le> Re (A - D + 2 * B * cnj B / A)"
        by simp
      hence "- Re (2 * (B * cnj B) / A) \<le> Re ((A - D - cor dsc))"
        by (simp add: field_simps)
      hence *: "- (Re (2 * (B * cnj B)) / Re A) \<le> Re (A - D - cor dsc)"
        using \<open>is_real A\<close> \<open>A \<noteq> 0\<close>
        by (subst (asm) Re_divide_real, auto)
      from divide_right_mono[OF this, of "Re (2 * B * cnj B)"]
      have "- 1 / Re A \<le> Re (A - D - cor dsc) / Re (2 * B * cnj B)"
        using \<open>Re A > 0\<close> \<open>B \<noteq> 0\<close> \<open>A \<noteq> 0\<close> \<open>0 < Re (2 * (B * cnj B))\<close>
        using \<open>(Re (2 * (B * cnj B)) / Re A) / Re (2 * B * cnj B) = 1 / Re A\<close>
        by simp
      from mult_right_mono[OF this, of "Re A"]
      show ?thesis
        using \<open>is_real A\<close> \<open>is_real D\<close> \<open>B \<noteq> 0\<close> \<open>Re A > 0\<close> \<open>A \<noteq> 0\<close>
        apply (subst **)
        apply (subst Re_mult_real, simp)
        apply (subst Re_divide_real, simp, simp)
        apply (simp add: field_simps)
        done
    qed
    ultimately
    show ?thesis
      by simp
  next
    case False
    show ?thesis
    proof (cases "Re A < 0")
      case True
      hence "Re (A*a1/B) \<le> Re (A*a2/B)"
        using * ** \<open>Re (2 * (B * cnj B)) > 0\<close> \<open>B \<noteq> 0\<close> \<open>is_real A\<close> \<open>is_real D\<close> xxx
        using mult_right_mono_neg[of ?rhs ?lhs "Re A"]
        apply simp
        apply (subst Re_divide_real, simp, simp)
        apply (subst Re_divide_real, simp, simp)
        apply (subst Re_mult_real, simp)+
        apply simp
        done
      moreover
      have "Re (A*a1/B) \<ge> -1"
      proof-
        from \<open>Re A * Re D \<le> Re (B*cnj B)\<close>
        have "Re (A\<^sup>2) \<le> Re (B*cnj B) - Re ((D - A)*A)"
          using \<open>Re A < 0\<close> \<open>is_real A\<close> \<open>is_real D\<close>
          by (simp add: power2_eq_square field_simps)
        hence "1 \<le> Re (B*cnj B) / Re (A\<^sup>2) - Re (D - A) / Re A"
          using \<open>Re A < 0\<close> \<open>is_real A\<close> \<open>is_real D\<close>
          using divide_right_mono[OF \<open>Re (A\<^sup>2) \<le> Re (B*cnj B) - Re ((D - A)*A)\<close>, of "Re (A\<^sup>2)"]
          by (simp add: power2_eq_square diff_divide_distrib)
        have "4 * Re(B*cnj B) \<le> 4 * (Re (B*cnj B))\<^sup>2 / Re (A\<^sup>2)  - 2*Re (D - A) / Re A * 2 * Re(B*cnj B)"
          using mult_right_mono[OF \<open>1 \<le> Re (B*cnj B) / Re (A\<^sup>2) - Re (D - A) / Re A\<close>, of "4 * Re (B*cnj B)"]
          by (simp add: left_diff_distrib) (simp add: power2_eq_square field_simps)
        moreover
        have "A \<noteq> 0"
          using \<open>Re A < 0\<close>
          by auto
        hence "4 * (Re (B*cnj B))\<^sup>2 / Re (A\<^sup>2) = Re (4 * (B*cnj B)\<^sup>2 / A\<^sup>2)"
          using Re_divide_real[of "A\<^sup>2" "4 * (B*cnj B)\<^sup>2"] \<open>Re A < 0\<close> \<open>is_real A\<close>
          by (auto simp add: power2_eq_square)
        moreover
        have "2*Re (D - A) / Re A * 2 * Re(B*cnj B) = Re (2 * (D - A) / A * 2 * B * cnj B)"
          using \<open>is_real A\<close> \<open>is_real D\<close> \<open>A \<noteq> 0\<close>
          using Re_divide_real[of "A" "(4 * D - 4 * A) * B * cnj B"]
          by (simp add: field_simps)
        ultimately
        have "Re ((D - A)\<^sup>2 + 4 * B*cnj B) \<le> Re((D - A)\<^sup>2 + 4 * (B*cnj B)\<^sup>2 / A\<^sup>2  - 2*(D - A) / A * 2 * B*cnj B)"
          by (simp add: field_simps power2_eq_square)
        hence "Re ((D - A)\<^sup>2 + 4 * B*cnj B) \<le> Re(((D - A) -  2 * B*cnj B / A)\<^sup>2)"
          using \<open>A \<noteq> 0\<close>
          by (subst power2_diff) (simp add: power2_eq_square field_simps)
        hence "dsc \<le> sqrt (Re(((D - A) -  2 * B*cnj B / A)\<^sup>2))"
          using \<open>dsc = sqrt(Re ((D-A)\<^sup>2 + 4*(B*cnj B)))\<close>
          by simp
        moreover
        have "Re(((D - A) -  2 * B*cnj B / A)\<^sup>2) = (Re((D - A) -  2 * B*cnj B / A))\<^sup>2"
          using \<open>is_real A\<close> \<open>is_real D\<close> div_reals
          by (simp add: power2_eq_square)
        ultimately
        have "dsc \<le> \<bar>Re (D - A - 2 * B * cnj B / A)\<bar>"
          by simp
        moreover
        have "Re (D - A - 2 * B * cnj B / A) \<ge> 0"
        proof-
          have "Re (A\<^sup>2 + B*cnj B) \<ge> 0"
            using \<open>is_real A\<close>
            by (simp add: power2_eq_square)
          also have "Re (A\<^sup>2 + 2*B*cnj B - A*D) \<ge> Re (A\<^sup>2 + B*cnj B)"
            using \<open>Re A * Re D \<le> Re (B*cnj B)\<close>
            using \<open>is_real A\<close> \<open>is_real D\<close>
            by simp
          finally have "Re (A\<^sup>2 + 2*B*cnj B - A*D) \<ge> 0"
            by simp
          show ?thesis
            using divide_right_mono_neg[OF \<open>Re (A\<^sup>2 + 2*B*cnj B - A*D) \<ge> 0\<close>, of "Re A"] \<open>Re A < 0\<close> \<open>is_real A\<close> \<open>A \<noteq> 0\<close>
            by (simp add: add_divide_distrib diff_divide_distrib) (subst Re_divide_real, auto simp add: power2_eq_square field_simps)
        qed
        ultimately
        have "dsc \<le> Re (D - A - 2 * B * cnj B / A)"
          by simp
        hence "- Re (2 * (B * cnj B) / A) \<ge> Re ((A - D + cor dsc))"
          by (simp add: field_simps)
        hence "- (Re (2 * (B * cnj B)) / Re A) \<ge> Re (A - D + cor dsc)"
          using \<open>is_real A\<close> \<open>A \<noteq> 0\<close>
          by (subst (asm) Re_divide_real, auto)
        from divide_right_mono[OF this, of "Re (2 * B * cnj B)"]
        have "- 1 / Re A \<ge> Re (A - D + cor dsc) / Re (2 * B * cnj B)"
          using \<open>Re A < 0\<close> \<open>B \<noteq> 0\<close> \<open>A \<noteq> 0\<close> \<open>0 < Re (2 * (B * cnj B))\<close>
          using \<open>(Re (2 * (B * cnj B)) / Re A) / Re (2 * B * cnj B) = 1 / Re A\<close>
          by simp
        from mult_right_mono_neg[OF this, of "Re A"]
        show ?thesis
          using \<open>is_real A\<close> \<open>is_real D\<close> \<open>B \<noteq> 0\<close> \<open>Re A < 0\<close> \<open>A \<noteq> 0\<close>
          apply (subst *)
          apply (subst Re_mult_real, simp)
          apply (subst Re_divide_real, simp, simp)
          apply (simp add: field_simps)
          done
      qed
      ultimately
      show ?thesis
        by simp
    next
      case False
      hence "A = 0"
        using \<open>\<not> Re A > 0\<close> \<open>is_real A\<close>
        using complex_eq_if_Re_eq by auto
      thus ?thesis
        by simp
    qed
  qed
qed


lemma chordal_circle_det_positive:
  fixes x y :: real
  assumes "x * y < 0"
  shows "x / (x - y) > 0"
proof (cases "x > 0")
  case True
  hence "y < 0"
    using \<open>x * y < 0\<close>
    by (smt mult_nonneg_nonneg)
  have "x - y > 0"
    using \<open>x > 0\<close> \<open>y < 0\<close>
    by auto
  thus ?thesis
    using \<open>x > 0\<close>
    by (metis zero_less_divide_iff)
next
  case False
  hence *: "y > 0 \<and> x < 0"
    using \<open>x * y < 0\<close>
    using mult_nonpos_nonpos[of x y]
    by (cases "x=0") force+

  have "x - y < 0"
    using *
    by auto
  thus ?thesis
    using *
    by (metis zero_less_divide_iff)
qed

lemma chordal_circle1:
  assumes "is_real A" and "is_real D" and "Re (A * D) < 0" and "r = sqrt(Re ((4*A)/(A-D)))"
  shows "mk_circline A 0 0 D = chordal_circle \<infinity>\<^sub>h r"
using assms
proof (transfer, transfer)
  fix A D r
  assume *: "is_real A" "is_real D" "Re (A * D) < 0" "r = sqrt (Re ((4*A)/(A-D)))"
  hence "A \<noteq> 0 \<or> D \<noteq> 0"
    by auto
  hence "(A, 0, 0, D) \<in> hermitean_nonzero"
    using eq_cnj_iff_real[of A] eq_cnj_iff_real[of D] *
    unfolding hermitean_def
    by (simp add: mat_adj_def mat_cnj_def)
  moreover
  have "(- (cor r)\<^sup>2, 0, 0, 4 - (cor r)\<^sup>2) \<in> hermitean_nonzero"
    by (simp add: hermitean_def mat_adj_def mat_cnj_def power2_eq_square)
  moreover
  have "A \<noteq> D"
    using \<open>Re (A * D) < 0\<close> \<open>is_real A\<close> \<open>is_real D\<close>
    by auto
  have "Re ((4*A)/(A-D)) \<ge> 0"
  proof-
    have "Re A / Re (A - D) \<ge> 0"
      using \<open>Re (A * D) < 0\<close> \<open>is_real A\<close> \<open>is_real D\<close>
      using chordal_circle_det_positive[of "Re A" "Re D"]
      by simp
    thus ?thesis
      using \<open>is_real A\<close> \<open>is_real D\<close> \<open>A \<noteq> D\<close>
      by (subst Re_divide_real, auto)
  qed
  moreover
  have "- (cor (sqrt (Re (4 * A / (A - D)))))\<^sup>2 = cor (Re (4 / (D - A))) * A"
    using \<open>Re ((4*A)/(A-D)) \<ge> 0\<close> \<open>is_real A\<close> \<open>is_real D\<close> \<open>A \<noteq> D\<close>
    by (subst cor_squared, subst real_sqrt_power[symmetric], simp) (simp add: Re_divide_real Re_mult_real minus_divide_right)
  moreover
  have "4 * (A - D) - 4 * A  = 4 * -D"
    by (simp add: field_simps)
  hence "4 - 4 * A / (A - D) = -4 * D / (A - D)"
    using \<open>A \<noteq> D\<close>
    by (smt ab_semigroup_mult_class.mult_ac(1) diff_divide_eq_iff eq_iff_diff_eq_0 mult_minus1 mult_minus1_right mult_numeral_1_right right_diff_distrib_numeral times_divide_eq_right)
  hence "4 - 4 * A / (A - D) = 4 * D / (D - A)"
    by (metis (hide_lams, no_types) minus_diff_eq minus_divide_left minus_divide_right minus_mult_left)
  hence **: "4 - (cor (sqrt (Re (4 * A / (A - D)))))\<^sup>2 = cor (Re (4 / (D - A))) * D"
    using \<open>Re ((4*A)/(A-D)) \<ge> 0\<close> \<open>is_real A\<close> \<open>is_real D\<close> \<open>A \<noteq> D\<close>
    by (subst cor_squared, subst real_sqrt_power[symmetric], simp)
  ultimately
  show "circline_eq_cmat (mk_circline_cmat A 0 0 D) (chordal_circle_cvec_cmat \<infinity>\<^sub>v r)"
    using * \<open>is_real A\<close> \<open>is_real D\<close> \<open>A \<noteq> D\<close> \<open>r = sqrt(Re ((4*A)/(A-D)))\<close>
    by (simp, rule_tac x="Re(4/(D-A))" in exI, auto, simp_all add: **)
qed

lemma chordal_circle2:
  assumes "is_real A" and "is_real D" and "Re (A * D) < 0" and "r = sqrt(Re ((4*D)/(D-A)))"
  shows "mk_circline A 0 0 D = chordal_circle 0\<^sub>h r"
using assms
proof (transfer, transfer)
  fix A D r
  assume *: "is_real A" "is_real D" "Re (A * D) < 0" "r = sqrt (Re ((4*D)/(D-A)))"
  hence "A \<noteq> 0 \<or> D \<noteq> 0"
    by auto
  hence "(A, 0, 0, D) \<in> {H. hermitean H \<and> H \<noteq> mat_zero}"
    using eq_cnj_iff_real[of A] eq_cnj_iff_real[of D] *
    unfolding hermitean_def
    by (simp add: mat_adj_def mat_cnj_def)
  moreover
  have "(4 - (cor r)\<^sup>2, 0, 0, - (cor r)\<^sup>2) \<in> {H. hermitean H \<and> H \<noteq> mat_zero}"
    by (auto simp add: hermitean_def mat_adj_def mat_cnj_def power2_eq_square)
  moreover
  have "A \<noteq> D"
    using \<open>Re (A * D) < 0\<close> \<open>is_real A\<close> \<open>is_real D\<close>
    by auto
  have "Re((4*D)/(D-A)) \<ge> 0"
  proof-
    have "Re D / Re (D - A) \<ge> 0"
      using \<open>Re (A * D) < 0\<close> \<open>is_real A\<close> \<open>is_real D\<close>
      using chordal_circle_det_positive[of "Re D" "Re A"]
      by (simp add: field_simps)
    thus ?thesis
      using \<open>is_real A\<close> \<open>is_real D\<close> \<open>A \<noteq> D\<close>
      by (subst Re_divide_real, auto)
  qed
  have "4 * (D - A) - 4 * D  = 4 * -A"
    by (simp add: field_simps)
  hence "4 - 4 * D / (D - A) = -4 * A / (D - A)"
    using \<open>A \<noteq> D\<close>
    by (smt ab_semigroup_mult_class.mult_ac(1) diff_divide_eq_iff eq_iff_diff_eq_0 mult_minus1 mult_minus1_right mult_numeral_1_right right_diff_distrib_numeral times_divide_eq_right)
  hence "4 - 4 * D / (D - A) = 4 * A / (A - D)"
    by (metis (hide_lams, no_types) minus_diff_eq minus_divide_left minus_divide_right minus_mult_left)
  hence **: "4 - (cor (sqrt (Re ((4*D)/(D-A)))))\<^sup>2 = cor (Re (4 / (A - D))) * A"
    using \<open>is_real A\<close> \<open>is_real D\<close> \<open>A \<noteq> D\<close> \<open>Re (4 * D / (D - A)) \<ge> 0\<close>
    by (subst cor_squared, subst real_sqrt_power[symmetric], simp)

  moreover
  have "- (cor (sqrt (Re ((4*D)/(D-A)))))\<^sup>2 = cor (Re (4 / (A - D))) * D"
    using \<open>is_real A\<close> \<open>is_real D\<close> \<open>A \<noteq> D\<close> \<open>Re ((4*D)/(D-A)) \<ge> 0\<close>
    by (subst cor_squared, subst real_sqrt_power[symmetric], simp) (simp add: Re_divide_real minus_divide_right)

  ultimately
  show "circline_eq_cmat (mk_circline_cmat A 0 0 D) (chordal_circle_cvec_cmat 0\<^sub>v r)"
    using \<open>is_real A\<close> \<open>is_real D\<close> \<open>A \<noteq> 0 \<or> D \<noteq> 0\<close> \<open>r = sqrt (Re ((4*D)/(D-A)))\<close>
    using *
    by (simp, rule_tac x="Re (4/(A-D))" in exI, auto, simp_all add: **)
qed

lemma chordal_circle':
  assumes "B \<noteq> 0" and "(A, B, C, D) \<in> hermitean_nonzero" and "Re (mat_det (A, B, C, D)) \<le> 0" and
  "C * a\<^sup>2  + (D - A) * a - B = 0" and "r = sqrt((4 - Re((-4 * a/B) * A)) / (1 + Re (a*cnj a)))"
  shows "mk_circline A B C D = chordal_circle (of_complex a) r"
using assms
proof (transfer, transfer)
  fix A B C D a :: complex and r :: real

  let ?k = "(-4) * a / B"

  assume *: "(A, B, C, D) \<in> {H. hermitean H \<and> H \<noteq> mat_zero}" and **: "B \<noteq> 0" "C * a\<^sup>2 + (D - A) * a - B = 0" and rr: "r = sqrt ((4 - Re (?k * A)) / (1 + Re (a * cnj a)))" and det: "Re (mat_det (A, B, C, D)) \<le> 0"

  have "is_real A" "is_real D" "C = cnj B"
    using * hermitean_elems
    by auto

  from ** have a12: "let dsc = sqrt(Re ((D-A)\<^sup>2 + 4 * (B*cnj B)))
                      in a = (A - D + cor dsc) / (2 * C) \<or> a = (A - D - cor dsc) / (2 * C)"
  proof-
    have "Re ((D-A)\<^sup>2 + 4 * (B*cnj B)) \<ge> 0"
      using \<open>is_real A\<close> \<open>is_real D\<close>
      by (subst complex_mult_cnj_cmod) (simp add: power2_eq_square)
    hence "ccsqrt ((D - A)\<^sup>2 - 4 * C * - B) = cor (sqrt (Re ((D - A)\<^sup>2 + 4 * (B * cnj B))))"
      using csqrt_real[of "((D - A)\<^sup>2 + 4 * (B * cnj B))"] \<open>is_real A\<close> \<open>is_real D\<close> \<open>C = cnj B\<close>
      by (auto simp add: power2_eq_square field_simps)
    thus ?thesis
      using complex_quadratic_equation_two_roots[of C a "D - A" "-B"]
      using  \<open>C * a\<^sup>2 + (D - A) * a - B = 0\<close> \<open>B \<noteq> 0\<close> \<open>C = cnj B\<close>
      by (simp add: Let_def)
  qed

  have "is_real ?k"
    using a12 \<open>C = cnj B\<close> \<open>is_real A\<close> \<open>is_real D\<close>
    by (auto simp add: Let_def)
  have "a \<noteq> 0"
    using **
    by auto
  hence "Re ?k \<noteq> 0"
    using \<open>is_real (-4*a / B)\<close> \<open>B \<noteq> 0\<close>
    by (metis complex.expand divide_eq_0_iff divisors_zero zero_complex.simps(1) zero_complex.simps(2) zero_neq_neg_numeral)
  moreover
  have "(-4) * a = cor (Re ?k) * B"
    using complex_of_real_Re[OF \<open>is_real (-4*a/B)\<close>] \<open>B \<noteq> 0\<close>
    by simp
  moreover
  have "is_real (a/B)"
    using \<open>is_real ?k\<close> is_real_mult_real[of "-4" "a / B"]
    by simp
  hence "is_real (B * cnj a)"
    using * \<open>C = cnj B\<close>
    by (metis (no_types, lifting) Im_complex_div_eq_0 complex_cnj_divide eq_cnj_iff_real hermitean_elems(3) mem_Collect_eq mult.commute)
  hence "B * cnj a = cnj B * a"
    using eq_cnj_iff_real[of "B * cnj a"]
    by simp
  hence "-4 * cnj a = cor (Re ?k) * C"
    using \<open>C = cnj B\<close>
    using complex_of_real_Re[OF \<open>is_real ?k\<close>] \<open>B \<noteq> 0\<close>
    by (simp, simp add: field_simps)
  moreover
  have "1 + a * cnj a \<noteq> 0"
    by (subst complex_mult_cnj_cmod) (smt cor_add of_real_0 of_real_1 of_real_eq_iff realpow_square_minus_le)
  have "r\<^sup>2 = (4 - Re (?k * A)) / (1 + Re (a * cnj a))"
  proof-
    have "Re (a / B * A) \<ge> -1"
      using a12 chordal_circle_radius_positive[of A B C D] * \<open>B \<noteq> 0\<close> det
      by (auto simp add: Let_def field_simps)
    from mult_right_mono_neg[OF this, of "-4"]
    have "4 - Re (?k * A) \<ge> 0"
      using Re_mult_real[of "-4" "a / B * A"]
      by (simp add: field_simps)
    moreover
    have "1 + Re (a * cnj a) > 0"
      using \<open>a \<noteq> 0\<close> complex_mult_cnj complex_neq_0
      by auto
    ultimately
    have "(4 - Re (?k * A)) / (1 + Re (a * cnj a)) \<ge> 0"
      by (metis divide_nonneg_pos)
    thus ?thesis
      using rr
      by simp
  qed
  hence "r\<^sup>2 = Re ((4 - ?k * A) / (1 + a * cnj a))"
    using \<open>is_real ?k\<close> \<open>is_real A\<close> \<open>1 + a * cnj a \<noteq> 0\<close>
    by (subst Re_divide_real, auto)
  hence "(cor r)\<^sup>2 =  (4 - ?k * A) / (1 + a * cnj a)"
    using \<open>is_real ?k\<close> \<open>is_real A\<close>
    using mult_reals[of ?k A]
    by (simp add: cor_squared)
  hence "4 - (cor r)\<^sup>2 * (a * cnj a + 1) = cor (Re ?k) * A"
    using complex_of_real_Re[OF \<open>is_real (-4*a/B)\<close>]
    using \<open>1 + a * cnj a \<noteq> 0\<close>
    by (simp add: field_simps)
  moreover

  have "?k = cnj ?k"
    using \<open>is_real ?k\<close>
    using eq_cnj_iff_real[of "-4*a/B"]
    by simp

  have "?k\<^sup>2 = cor ((cmod ?k)\<^sup>2)"
    using  cor_cmod_real[OF \<open>is_real ?k\<close>]
    unfolding power2_eq_square
    by (subst cor_mult) (metis minus_mult_minus)
  hence "?k\<^sup>2 = ?k * cnj ?k"
    using complex_mult_cnj_cmod[of ?k]
    by simp
  hence ***: "a * cnj a = (cor ((Re ?k)\<^sup>2) * B * C) / 16"
    using complex_of_real_Re[OF \<open>is_real (-4*a/B)\<close>] \<open>C = cnj B\<close> \<open>is_real (-4*a/B)\<close> \<open>B \<noteq> 0\<close>
    by simp
  from ** have "cor ((Re ?k)\<^sup>2) * B * C - 4 * cor (Re ?k) * (D-A) - 16 = 0"
    using complex_of_real_Re[OF \<open>is_real ?k\<close>]
    by (simp add: power2_eq_square, simp add: field_simps, algebra)
  hence "?k * (D-A) = 4 * (cor ((Re ?k)\<^sup>2) * B * C / 16 - 1)"
    by (subst (asm) complex_of_real_Re[OF \<open>is_real ?k\<close>]) algebra
  hence "?k * (D-A) = 4 * (a*cnj a - 1)"
    by (subst (asm)  ***[symmetric]) simp

  hence "4 * a * cnj a - (cor r)\<^sup>2 * (a * cnj a + 1) = cor (Re ?k) * D"
    using \<open>4 - (cor r)\<^sup>2 * (a * cnj a + 1) = cor (Re ?k) * A\<close>
    using complex_of_real_Re[OF \<open>is_real (-4*a/B)\<close>]
    by simp algebra
  ultimately
  show "circline_eq_cmat (mk_circline_cmat A B C D) (chordal_circle_cvec_cmat (of_complex_cvec a) r)"
    using * \<open>a \<noteq> 0\<close>
    by (simp, rule_tac x="Re (-4*a / B)" in exI, simp)
qed

end
