(* ---------------------------------------------------------------------------- *)
section \<open>Riemann sphere\<close>
(* ---------------------------------------------------------------------------- *)

text \<open>The extended complex plane $\mathbb{C}P^1$ can be identified with a Riemann (unit) sphere
$\Sigma$ by means of stereographic projection. The sphere is projected from its north pole $N$ to
the $xOy$ plane (identified with $\mathbb{C}$). This projection establishes a bijective map $sp$
between $\Sigma \setminus \{N\}$ and the finite complex plane $\mathbb{C}$. The infinite point is
defined as the image of $N$.\<close>

theory Riemann_Sphere
imports Homogeneous_Coordinates Circlines "HOL-Analysis.Product_Vector"
begin

text \<open>Coordinates in $\mathbb{R}^3$\<close>
type_synonym R3 = "real \<times> real \<times> real"

text \<open>Type of points of $\Sigma$\<close>
abbreviation unit_sphere where
  "unit_sphere \<equiv> {(x::real, y::real, z::real). x*x + y*y + z*z = 1}"

typedef riemann_sphere = "unit_sphere"
  by (rule_tac x="(1, 0, 0)" in exI) simp

setup_lifting type_definition_riemann_sphere

lemma sphere_bounds':
  assumes "x*x + y*y + z*z = (1::real)"
  shows "-1 \<le> x \<and> x \<le> 1"
proof-
  from assms have "x*x \<le> 1"
    by (smt real_minus_mult_self_le)
  hence "x\<^sup>2 \<le> 1\<^sup>2" "(- x)\<^sup>2 \<le> 1\<^sup>2"
    by (auto simp add: power2_eq_square)
  show "-1 \<le> x \<and> x \<le> 1"
  proof (cases "x \<ge> 0")
    case True
    thus ?thesis
      using \<open>x\<^sup>2 \<le> 1\<^sup>2\<close>
      by (smt power2_le_imp_le)      
  next
    case False
    thus ?thesis
      using \<open>(-x)\<^sup>2 \<le> 1\<^sup>2\<close>
      by (smt power2_le_imp_le)      
  qed
qed

lemma sphere_bounds:
  assumes "x*x + y*y + z*z = (1::real)"
  shows "-1 \<le> x \<and> x \<le> 1"  "-1 \<le> y \<and> y \<le> 1"  "-1 \<le> z \<and> z \<le> 1"
  using assms
  using sphere_bounds'[of x y z] sphere_bounds'[of y x z] sphere_bounds'[of z x y]
  by (auto simp add: field_simps)

(* ---------------------------------------------------------------------------- *)
subsection \<open>Parametrization of the unit sphere in polar coordinates\<close>
(* ---------------------------------------------------------------------------- *)

lemma sphere_params_on_sphere:
  fixes \<alpha> \<beta> :: real
  assumes "x = cos \<alpha> * cos \<beta>" and "y = cos \<alpha> * sin \<beta>" "z = sin \<alpha>"
  shows "x*x + y*y + z*z = 1"
proof-
  have "x*x + y*y = (cos \<alpha> * cos \<alpha>) * (cos \<beta> * cos \<beta>) + (cos \<alpha> * cos \<alpha>) * (sin \<beta> * sin \<beta>)"
    using assms
    by simp
  hence "x*x + y*y = cos \<alpha> * cos \<alpha>"
    using sin_cos_squared_add3[of \<beta>]
    by (subst (asm) distrib_left[symmetric]) (simp add: field_simps)
  thus ?thesis
    using assms
    using sin_cos_squared_add3[of \<alpha>]
    by simp
qed

lemma sphere_params:
  fixes x y z :: real
  assumes "x*x + y*y + z*z = 1"
  shows "x = cos (arcsin z) * cos (atan2 y x) \<and> y = cos (arcsin z) * sin (atan2 y x) \<and> z = sin (arcsin z)"
proof (cases "z=1 \<or> z = -1")
  case True
  hence "x = 0 \<and> y = 0"
    using assms
    by auto
  thus ?thesis
    using \<open>z = 1 \<or> z = -1\<close>
    by (auto simp add: cos_arcsin)
next
  case False
  hence "x \<noteq> 0 \<or> y \<noteq> 0"
    using assms
    by (auto simp add: square_eq_1_iff)
  thus ?thesis
    using real_sqrt_unique[of y "1 - z*z"]
    using real_sqrt_unique[of "-y" "1 - z*z"]
    using sphere_bounds[OF assms] assms
    by (auto simp add: cos_arcsin cos_arctan sin_arctan power2_eq_square field_simps real_sqrt_divide atan2_def)
qed

lemma ex_sphere_params:
  assumes "x*x + y*y + z*z = 1"
  shows "\<exists> \<alpha> \<beta>. x = cos \<alpha> * cos \<beta> \<and> y = cos \<alpha> * sin \<beta> \<and> z = sin \<alpha> \<and> -pi / 2 \<le> \<alpha> \<and> \<alpha> \<le> pi / 2 \<and> -pi \<le> \<beta> \<and> \<beta> < pi"
using assms arcsin_bounded[of z] sphere_bounds[of x y z]
by (rule_tac x="arcsin z" in exI, rule_tac x="atan2 y x" in exI) (simp add: sphere_params arcsin_bounded atan2_bounded)

(* ----------------------------------------------------------------- *)
subsection \<open>Stereographic and inverse stereographic projection\<close>
(* ----------------------------------------------------------------- *)

text \<open>Stereographic projection\<close>

definition stereographic_r3_cvec :: "R3 \<Rightarrow> complex_vec" where
[simp]: "stereographic_r3_cvec M = (let (x, y, z) =  M in
     (if (x, y, z) \<noteq> (0, 0, 1) then
           (x + \<i> * y, cor (1 - z))
      else
           (1, 0)
     ))"


lift_definition stereographic_r3_hcoords :: "R3 \<Rightarrow> complex_homo_coords" is stereographic_r3_cvec
  by (auto split: if_split_asm simp add: cor_eq_0)

lift_definition stereographic :: "riemann_sphere \<Rightarrow> complex_homo" is stereographic_r3_hcoords
  done

text \<open>Inverse stereographic projection\<close>

definition inv_stereographic_cvec_r3 :: "complex_vec \<Rightarrow> R3" where [simp]:
  "inv_stereographic_cvec_r3 z = (
     let (z1, z2) = z
       in if z2 = 0 then
              (0, 0, 1)
          else
             let z = z1/z2;
                 X = Re (2*z / (1 + z*cnj z));
                 Y = Im (2*z / (1 + z*cnj z));
                 Z = ((cmod z)\<^sup>2 - 1) / (1 + (cmod z)\<^sup>2)
               in (X, Y, Z))"

lemma Re_stereographic:
  shows "Re (2 * z / (1 + z * cnj z)) = 2 * Re z / (1 + (cmod z)\<^sup>2)"
  using one_plus_square_neq_zero
  by (subst complex_mult_cnj_cmod, subst Re_divide_real) (auto simp add: power2_eq_square)

lemma Im_stereographic: 
  shows "Im (2 * z / (1 + z * cnj z)) = 2 * Im z / (1 + (cmod z)\<^sup>2)"
  using one_plus_square_neq_zero
  by (subst complex_mult_cnj_cmod, subst Im_divide_real) (auto simp add: power2_eq_square)

lemma inv_stereographic_on_sphere:
  assumes "X = Re (2*z / (1 + z*cnj z))" and "Y = Im (2*z / (1 + z*cnj z))" and "Z = ((cmod z)\<^sup>2 - 1) / (1 + (cmod z)\<^sup>2)"
  shows "X*X + Y*Y + Z*Z = 1"
proof-
  have "1 + (cmod z)\<^sup>2 \<noteq> 0"
    by (smt power2_less_0)
  thus ?thesis
    using assms
    by (simp add: Re_stereographic Im_stereographic)
       (cases z, simp add: power2_eq_square real_sqrt_mult[symmetric] add_divide_distrib[symmetric], simp add: complex_norm power2_eq_square field_simps)
qed

lift_definition inv_stereographic_hcoords_r3 :: "complex_homo_coords \<Rightarrow> R3" is inv_stereographic_cvec_r3
  done

lift_definition inv_stereographic :: "complex_homo \<Rightarrow> riemann_sphere" is inv_stereographic_hcoords_r3
proof transfer
  fix v v'
  assume 1: "v \<noteq> vec_zero" "v' \<noteq> vec_zero" "v \<approx>\<^sub>v v'"
  obtain v1 v2 v'1 v'2 where *: "v = (v1, v2)" "v' = (v'1, v'2)"
    by (cases v, cases v', auto)
  obtain x y z where
    **: "inv_stereographic_cvec_r3 v = (x, y, z)"
    by (cases "inv_stereographic_cvec_r3 v", blast)
  have "inv_stereographic_cvec_r3 v \<in> unit_sphere"
  proof (cases "v2 = 0")
    case True
    thus ?thesis
      using *
      by simp
  next
    case False
    thus ?thesis
      using * ** inv_stereographic_on_sphere[of x "v1 / v2" y z]
      by simp
  qed
  moreover
  have "inv_stereographic_cvec_r3 v = inv_stereographic_cvec_r3 v'"
    using 1 * **
    by (auto split: if_split if_split_asm)
  ultimately
  show "inv_stereographic_cvec_r3 v \<in> unit_sphere \<and>
        inv_stereographic_cvec_r3 v = inv_stereographic_cvec_r3 v'"
    by simp
qed

text \<open>North pole\<close>
definition North_R3 :: R3 where
  [simp]: "North_R3 = (0, 0, 1)"
lift_definition North :: "riemann_sphere" is North_R3
  by simp

lemma stereographic_North: 
  shows "stereographic x = \<infinity>\<^sub>h \<longleftrightarrow> x = North"
  by (transfer, transfer, auto split: if_split_asm)

text \<open>Stereographic and inverse stereographic projection are mutually inverse.\<close>

lemma stereographic_inv_stereographic':
  assumes
  z: "z = z1/z2" and "z2 \<noteq> 0" and
  X: "X = Re (2*z / (1 + z*cnj z))" and Y: "Y = Im (2*z / (1 + z*cnj z))" and Z: "Z = ((cmod z)\<^sup>2 - 1) / (1 + (cmod z)\<^sup>2)"
  shows "\<exists> k. k \<noteq> 0 \<and> (X + \<i>*Y, complex_of_real (1 - Z)) = k *\<^sub>s\<^sub>v (z1, z2)"
proof-
  have "1 + (cmod z)\<^sup>2 \<noteq> 0"
    by (metis one_power2 sum_power2_eq_zero_iff zero_neq_one)
  hence "(1 - Z) = 2 / (1 + (cmod z)\<^sup>2)"
    using Z
    by (auto simp add: field_simps)
  hence "cor (1 - Z) = 2 / cor (1 + (cmod z)\<^sup>2)"
    by auto
  moreover
  have "X = 2 * Re(z) / (1 + (cmod z)\<^sup>2)"
    using X
    by (simp add: Re_stereographic)
  have "Y = 2 * Im(z) / (1 + (cmod z)\<^sup>2)"
    using Y
    by (simp add: Im_stereographic)
  have "X + \<i>*Y = 2 * z / cor (1 + (cmod z)\<^sup>2)"
    using \<open>1 + (cmod z)\<^sup>2 \<noteq> 0\<close>
    unfolding Complex_eq[of X Y, symmetric]
    by (subst \<open>X = 2*Re(z) / (1 + (cmod z)\<^sup>2)\<close>, subst \<open>Y = 2*Im(z) / (1 + (cmod z)\<^sup>2)\<close>, simp add: Complex_scale4 Complex_scale1)
  moreover
  have "1 + (cor (cmod (z1 / z2)))\<^sup>2 \<noteq> 0"
    by (rule one_plus_square_neq_zero)
  ultimately
  show ?thesis
    using \<open>z2 \<noteq> 0\<close> \<open>1 + (cmod z)\<^sup>2 \<noteq> 0\<close>
    by (simp, subst z)+
       (rule_tac x="(2 / (1 + (cor (cmod (z1 / z2)))\<^sup>2)) / z2" in exI, auto)
qed

lemma stereographic_inv_stereographic [simp]:
  shows "stereographic (inv_stereographic w) = w"
proof-
  have "w = stereographic (inv_stereographic w)"
  proof (transfer, transfer)
    fix w
    assume "w \<noteq> vec_zero"
    obtain w1 w2 where *: "w = (w1, w2)"
      by (cases w, auto)
    obtain x y z where **: "inv_stereographic_cvec_r3 w = (x, y, z)"
      by (cases "inv_stereographic_cvec_r3 w", blast)
    show "w \<approx>\<^sub>v stereographic_r3_cvec (inv_stereographic_cvec_r3 w)"
      using \<open>w \<noteq> vec_zero\<close> stereographic_inv_stereographic'[of "w1/w2" w1 w2 x y z] * **
      by (auto simp add: split_def Let_def split: if_split_asm)
  qed
  thus ?thesis
    by simp
qed

text \<open>Stereographic projection is bijective function\<close>

lemma bij_stereographic:
  shows "bij stereographic"
  unfolding bij_def inj_on_def surj_def
proof (safe)
  fix a b
  assume "stereographic a = stereographic b"
  thus "a = b"
  proof (transfer, transfer)
    fix a b :: R3
    obtain xa ya za xb yb zb where
      *: "a = (xa, ya, za)" "b = (xb, yb, zb)"
      by (cases a, cases b, auto)
    assume **: "a \<in> unit_sphere" "b \<in> unit_sphere" "stereographic_r3_cvec a \<approx>\<^sub>v stereographic_r3_cvec b"
    show "a = b"
    proof (cases "a = (0, 0, 1) \<or> b = (0, 0, 1)")
      case True
      thus ?thesis
        using * **
        by (simp split: if_split_asm) force+
    next
      case False
      then obtain k where ++: "k \<noteq> 0" "cor xb + \<i> * cor yb = k * (cor xa + \<i> * cor ya)" "1 - cor zb = k * (1 - cor za)"
        using * **
        by (auto split: if_split_asm)

      {
          assume "xb + xa*zb = xa + xb*za"
                 "yb + ya*zb = ya + yb*za"
                 "xa*xa + ya*ya + za*za = 1" "xb*xb + yb*yb + zb*zb = 1"
                 "za \<noteq> 1" "zb \<noteq> 1"
          hence "xa = xb \<and> ya = yb \<and> za = zb"
            by algebra
      } note *** = this

      have "za \<noteq> 1" "zb \<noteq> 1"
        using False * **
        by auto
      have "k = (1 - cor zb) / (1 - cor za)"
        using \<open>1 - cor zb = k * (1 - cor za)\<close> \<open>za \<noteq> 1\<close>
        by simp
      hence "(1 - cor za) * (cor xb + \<i> * cor yb) = (1 - cor zb) * (cor xa + \<i> * cor ya)"
        using \<open>za \<noteq> 1\<close> ++(2)
        by simp
      hence "xb + xa*zb = xa + xb*za"
            "yb + ya*zb = ya + yb*za"
            "xa*xa + ya*ya + za*za = 1" "xb*xb + yb*yb + zb*zb = 1"
        using * ** \<open>za \<noteq> 1\<close>
        apply (simp_all add: field_simps)
        unfolding complex_of_real_def imaginary_unit.ctr
        by (simp_all add: legacy_Complex_simps)
      thus ?thesis
          using * ** *** \<open>za \<noteq> 1\<close> \<open>zb \<noteq> 1\<close>
          by simp
      qed
  qed
next
  fix y
  show "\<exists> x. y = stereographic x"
    by (rule_tac x="inv_stereographic y" in exI, simp)
qed


lemma inv_stereographic_stereographic [simp]: 
  shows "inv_stereographic (stereographic x) = x"
  using stereographic_inv_stereographic[of "stereographic x"]
  using bij_stereographic
  unfolding bij_def inj_on_def
  by simp

lemma inv_stereographic_is_inv:
  shows "inv_stereographic = inv stereographic"
  by (rule inv_equality[symmetric], simp_all)

(* ----------------------------------------------------------------- *)
subsection \<open>Circles on the sphere\<close>
(* ----------------------------------------------------------------- *)

text \<open>Circlines in the plane correspond to circles on the Riemann sphere, and we formally establish
this connection. Every circle in three--dimensional space can be obtained as the intersection of a
sphere and a plane. We establish a one-to-one correspondence between circles on the Riemann sphere
and planes in space. Note that the plane need not intersect the sphere, but we will still say that
it defines a single imaginary circle. However, for one special circline (the one with the identity
representative matrix), there does not exist a plane in $\mathbb{R}^3$ that would correspond to it
--- in order to have this, instead of considering planes in $\mathbb{R}^3$, we must consider three
dimensional projective space and consider the infinite (hyper)plane.\<close>

text \<open>Planes in $R^3$ are given by equations $ax+by+cz=d$. Two four-tuples of coefficients $(a, b, c,
d)$ give the same plane iff they are proportional.\<close>

type_synonym R4 = "real \<times> real \<times> real \<times> real"

fun mult_sv :: "real \<Rightarrow> R4 \<Rightarrow> R4" (infixl "*\<^sub>s\<^sub>v\<^sub>4" 100) where
  "k *\<^sub>s\<^sub>v\<^sub>4 (a, b, c, d) = (k*a, k*b, k*c, k*d)"

abbreviation plane_vectors where
  "plane_vectors \<equiv> {(a::real, b::real, c::real, d::real). a \<noteq> 0 \<or> b \<noteq> 0 \<or> c \<noteq> 0 \<or> d \<noteq> 0}"

typedef plane_vec = "plane_vectors"
  by (rule_tac x="(1, 1, 1, 1)" in exI) simp

setup_lifting type_definition_plane_vec

definition plane_vec_eq_r4 :: "R4 \<Rightarrow> R4 \<Rightarrow> bool" where
  [simp]: "plane_vec_eq_r4 v1 v2 \<longleftrightarrow> (\<exists> k. k \<noteq> 0 \<and> v2 = k *\<^sub>s\<^sub>v\<^sub>4 v1)"

lift_definition plane_vec_eq :: "plane_vec \<Rightarrow> plane_vec \<Rightarrow> bool" is plane_vec_eq_r4
  done

lemma mult_sv_one [simp]:
  shows "1 *\<^sub>s\<^sub>v\<^sub>4 x = x"
  by (cases x) simp

lemma mult_sv_distb [simp]:
  shows "x *\<^sub>s\<^sub>v\<^sub>4 (y *\<^sub>s\<^sub>v\<^sub>4 v) = (x*y) *\<^sub>s\<^sub>v\<^sub>4 v"
  by (cases v) simp

quotient_type plane = plane_vec / plane_vec_eq
proof (rule equivpI)
  show "reflp plane_vec_eq"
    unfolding reflp_def
    by (auto simp add: plane_vec_eq_def) (rule_tac x="1" in exI, simp)
next
  show "symp plane_vec_eq"
    unfolding symp_def
    by (auto simp add: plane_vec_eq_def) (rule_tac x="1/k" in exI, simp)
next
  show "transp plane_vec_eq"
    unfolding transp_def
    by (auto simp add: plane_vec_eq_def) (rule_tac x="ka*k" in exI, simp)
qed

text \<open>Plane coefficients give a linear equation and the point on the Riemann sphere lies on the
circle determined by the plane iff its representation satisfies that linear equation.\<close>

definition on_sphere_circle_r4_r3 :: "R4 \<Rightarrow> R3 \<Rightarrow> bool" where
  [simp]: "on_sphere_circle_r4_r3 \<alpha> A \<longleftrightarrow>
      (let (X, Y, Z) = A;
           (a, b, c, d) = \<alpha>
        in a*X + b*Y + c*Z + d = 0)"

lift_definition on_sphere_circle_vec :: "plane_vec \<Rightarrow> R3 \<Rightarrow> bool" is on_sphere_circle_r4_r3
  done

lift_definition on_sphere_circle :: "plane \<Rightarrow> riemann_sphere \<Rightarrow> bool" is on_sphere_circle_vec
proof (transfer)
  fix pv1 pv2 :: R4 and w :: R3
  obtain a1 b1 c1 d1 a2 b2 c2 d2 x y z where
    *: "pv1 = (a1, b1, c1, d1)" "pv2 = (a2, b2, c2, d2)" "w = (x, y, z)"
    by (cases pv1, cases pv2, cases w, auto)
  assume "pv1 \<in> plane_vectors" "pv2 \<in> plane_vectors" "w \<in> unit_sphere" "plane_vec_eq_r4 pv1 pv2"
  then obtain k where **: "a2 = k*a1" "b2 = k*b1" "c2 = k*c1" "d2 = k*d1" "k \<noteq> 0"
    using *
    by auto
  have "k * a1 * x + k * b1 * y + k * c1 * z + k * d1 = k*(a1*x + b1*y + c1*z + d1)"
    by (simp add: field_simps)
  thus "on_sphere_circle_r4_r3 pv1 w = on_sphere_circle_r4_r3 pv2 w"
    using * **
    by simp
qed

definition sphere_circle_set where
  "sphere_circle_set \<alpha> = {A. on_sphere_circle \<alpha> A}"


(* ----------------------------------------------------------------- *)
subsection \<open>Connections of circlines in the plane and circles on the Riemann sphere\<close>
(* ----------------------------------------------------------------- *)

text \<open>We introduce stereographic and inverse stereographic projection between circles on the Riemann
sphere and circlines in the extended complex plane.\<close>

definition inv_stereographic_circline_cmat_r4 :: "complex_mat \<Rightarrow> R4" where
  [simp]: "inv_stereographic_circline_cmat_r4 H  =
            (let (A, B, C, D) = H
              in (Re (B+C), Re(\<i>*(C-B)), Re(A-D), Re(D+A)))"

lift_definition inv_stereographic_circline_clmat_pv :: "circline_mat \<Rightarrow> plane_vec" is inv_stereographic_circline_cmat_r4
  by (auto simp add: hermitean_def mat_adj_def mat_cnj_def real_imag_0 eq_cnj_iff_real)

lift_definition inv_stereographic_circline :: "circline \<Rightarrow> plane" is inv_stereographic_circline_clmat_pv
  apply transfer
  apply simp
  apply (erule exE)
  apply (rule_tac x="k" in exI)
  apply (case_tac "circline_mat1", case_tac "circline_mat2")
  apply (simp add: field_simps)
  done

definition stereographic_circline_r4_cmat :: "R4 \<Rightarrow> complex_mat" where
[simp]: "stereographic_circline_r4_cmat \<alpha> =
         (let (a, b, c, d) = \<alpha>
           in (cor ((c+d)/2) , ((cor a + \<i> * cor b)/2), ((cor a - \<i> * cor b)/2), cor ((d-c)/2)))"

lift_definition stereographic_circline_pv_clmat :: "plane_vec \<Rightarrow> circline_mat" is stereographic_circline_r4_cmat
  by (auto simp add: hermitean_def mat_adj_def mat_cnj_def)

lift_definition stereographic_circline :: "plane \<Rightarrow> circline" is stereographic_circline_pv_clmat
  apply transfer
  apply transfer
  apply (case_tac plane_vec1, case_tac plane_vec2, simp, erule exE, rule_tac x=k in exI, simp add: field_simps)
  done

text \<open>Stereographic and inverse stereographic projection of circlines are mutually inverse.\<close>

lemma stereographic_circline_inv_stereographic_circline:
  shows "stereographic_circline \<circ> inv_stereographic_circline = id"
proof (rule ext, simp)
  fix H
  show "stereographic_circline (inv_stereographic_circline H) = H"
  proof (transfer, transfer)
    fix H
    assume hh: "hermitean H \<and> H \<noteq> mat_zero"
    obtain A B C D where HH: "H = (A, B, C, D)"
      by (cases "H") auto
    have "is_real A" "is_real D" "C = cnj B"
      using HH hh hermitean_elems[of A B C D]
      by auto
    thus "circline_eq_cmat (stereographic_circline_r4_cmat (inv_stereographic_circline_cmat_r4 H)) H"
      using HH
      apply simp
      apply (rule_tac x=1 in exI, cases B)
      by (smt add_uminus_conv_diff complex_cnj_add complex_cnj_complex_of_real complex_cnj_i complex_cnj_mult complex_cnj_one complex_eq distrib_left_numeral mult.commute mult.left_commute mult.left_neutral mult_cancel_right2 mult_minus_left of_real_1 one_add_one)
  qed
qed

text \<open>Stereographic and inverse stereographic projection of circlines are mutually inverse.\<close>
lemma inv_stereographic_circline_stereographic_circline:
  "inv_stereographic_circline \<circ> stereographic_circline = id"
proof (rule ext, simp)
  fix \<alpha>
  show "inv_stereographic_circline (stereographic_circline \<alpha>) = \<alpha>"
  proof (transfer, transfer)
    fix \<alpha>
    assume aa: "\<alpha> \<in> plane_vectors"
    obtain a b c d where AA: "\<alpha> = (a, b, c, d)"
      by (cases "\<alpha>") auto
    thus "plane_vec_eq_r4 (inv_stereographic_circline_cmat_r4 (stereographic_circline_r4_cmat \<alpha>)) \<alpha>"
      using AA
      by simp (rule_tac x=1 in exI, auto simp add: field_simps complex_of_real_def)
  qed
qed

lemma stereographic_sphere_circle_set'':
  shows "on_sphere_circle (inv_stereographic_circline H) z \<longleftrightarrow>
         on_circline H (stereographic z)"
proof (transfer, transfer)
  fix M :: R3 and H :: complex_mat
  assume hh: "hermitean H \<and> H \<noteq> mat_zero" "M \<in> unit_sphere"
  obtain A B C D where HH: "H = (A, B, C, D)"
    by (cases "H") auto
  have *: "is_real A" "is_real D" "C = cnj B"
    using hh HH hermitean_elems[of A B C D]
    by auto
  obtain x y z where MM: "M = (x, y, z)"
    by (cases "M") auto
  show "on_sphere_circle_r4_r3 (inv_stereographic_circline_cmat_r4 H) M \<longleftrightarrow>
        on_circline_cmat_cvec H (stereographic_r3_cvec M)" (is "?lhs = ?rhs")
  proof
    assume ?lhs
    show ?rhs
    proof (cases "z=1")
      case True
      hence "x = 0" "y = 0"
        using MM hh
        by auto
      thus ?thesis
        using * \<open>?lhs\<close> HH MM \<open>z=1\<close>
        by (cases A, simp add: vec_cnj_def Complex_eq Let_def)
    next
      case False
      hence "Re A*(1+z) + 2*Re B*x + 2*Im B*y + Re D*(1-z) = 0"
        using * \<open>?lhs\<close> HH MM
        by (simp add: Let_def field_simps)
      hence "(Re A*(1+z) + 2*Re B*x + 2*Im B*y + Re D*(1-z))*(1-z) = 0"
        by simp
      hence "Re A*(1+z)*(1-z) + 2*Re B*x*(1-z) + 2*Im B*y*(1-z) + Re D*(1-z)*(1-z) = 0"
        by (simp add: field_simps)
      moreover
      have "x*x+y*y = (1+z)*(1-z)"
        using MM hh
        by (simp add: field_simps)
      ultimately
      have "Re A*(x*x+y*y) + 2*Re B*x*(1-z) + 2*Im B*y*(1-z) + Re D*(1-z)*(1-z) = 0"
        by simp
      hence "(x * Re A + (1 - z) * Re B) * x - (- (y * Re A) + - ((1 - z) * Im B)) * y + (x * Re B + y * Im B + (1 - z) * Re D) * (1 - z) = 0"
        by (simp add: field_simps)
      thus ?thesis
        using \<open>z \<noteq> 1\<close> HH MM * \<open>Re A*(1+z) + 2*Re B*x + 2*Im B*y + Re D*(1-z) = 0\<close>
        apply (simp add: Let_def vec_cnj_def)
        apply (subst complex_eq_iff)
        apply (simp add: field_simps)
        done
    qed
  next
    assume ?rhs
    show ?lhs
    proof (cases "z=1")
      case True
      hence "x = 0" "y = 0"
        using MM hh
        by auto
      thus ?thesis
        using HH MM \<open>?rhs\<close> \<open>z = 1\<close>
        by (simp add: Let_def vec_cnj_def)
    next
      case False
      hence "(x * Re A + (1 - z) * Re B) * x - (- (y * Re A) + - ((1 - z) * Im B)) * y + (x * Re B + y * Im B + (1 - z) * Re D) * (1 - z) = 0"
        using HH MM * \<open>?rhs\<close>
        by (simp add: Let_def vec_cnj_def complex_eq_iff)
      hence "Re A*(x*x+y*y) + 2*Re B*x*(1-z) + 2*Im B*y*(1-z) + Re D*(1-z)*(1-z) = 0"
        by (simp add: field_simps)
      moreover
      have "x*x + y*y = (1+z)*(1-z)"
        using MM hh
        by (simp add: field_simps)
      ultimately
      have "Re A*(1+z)*(1-z) + 2*Re B*x*(1-z) + 2*Im B*y*(1-z) + Re D*(1-z)*(1-z) = 0"
        by simp
      hence "(Re A*(1+z) + 2*Re B*x + 2*Im B*y + Re D*(1-z))*(1-z) = 0"
        by (simp add: field_simps)
      hence "Re A*(1+z) + 2*Re B*x + 2*Im B*y + Re D*(1-z) = 0"
        using \<open>z \<noteq> 1\<close>
        by simp
      thus ?thesis
        using MM HH *
        by (simp add: field_simps)
    qed
  qed
qed

lemma stereographic_sphere_circle_set' [simp]:
  shows "stereographic ` sphere_circle_set (inv_stereographic_circline H) =
         circline_set H"
unfolding sphere_circle_set_def circline_set_def
apply safe
proof-
  fix x
  assume "on_sphere_circle (inv_stereographic_circline H) x"
  thus "on_circline H (stereographic x)"
    using stereographic_sphere_circle_set''
    by simp
next
  fix x
  assume "on_circline H x"
  show "x \<in> stereographic ` {z. on_sphere_circle (inv_stereographic_circline H) z}"
  proof
    show "x = stereographic (inv_stereographic x)"
      by simp
  next
    show "inv_stereographic x \<in> {z. on_sphere_circle (inv_stereographic_circline H) z}"
      using stereographic_sphere_circle_set''[of H "inv_stereographic x"] \<open>on_circline H x\<close>
      by simp
  qed
qed

text \<open>The projection of the set of points on a circle on the Riemann sphere is exactly the set of
points on the circline obtained by the just introduced circle stereographic projection.\<close>
lemma stereographic_sphere_circle_set:
  shows "stereographic ` sphere_circle_set H = circline_set (stereographic_circline H)"
using stereographic_sphere_circle_set'[of "stereographic_circline H"]
using inv_stereographic_circline_stereographic_circline
unfolding comp_def
by (metis id_apply)

text \<open>Stereographic projection of circlines is bijective.\<close>
lemma bij_stereographic_circline:
  shows "bij stereographic_circline"
  using stereographic_circline_inv_stereographic_circline inv_stereographic_circline_stereographic_circline
  using o_bij by blast

text \<open>Inverse stereographic projection is bijective.\<close>
lemma bij_inv_stereographic_circline:
  shows "bij inv_stereographic_circline"
  using stereographic_circline_inv_stereographic_circline inv_stereographic_circline_stereographic_circline
  using o_bij by blast

end
