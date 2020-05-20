(*
    Author:     Wenda Li <wl302@cam.ac.uk / liwenda1990@hotmail.com>
*)

section \<open>Some useful lemmas about transcendental functions\<close>

theory Missing_Transcendental imports
  Missing_Topology
  Missing_Algebraic
begin

subsection \<open>Misc\<close>

lemma Im_Ln_eq_pi_half:
    "z \<noteq> 0 \<Longrightarrow> (Im(Ln z) = pi/2 \<longleftrightarrow> 0 < Im(z) \<and> Re(z) = 0)"
    "z \<noteq> 0 \<Longrightarrow> (Im(Ln z) = -pi/2 \<longleftrightarrow> Im(z) < 0 \<and> Re(z) = 0)"
proof -
  show "z \<noteq> 0 \<Longrightarrow> (Im(Ln z) = pi/2 \<longleftrightarrow> 0 < Im(z) \<and> Re(z) = 0)"
    by (metis Im_Ln_eq_pi Im_Ln_le_pi Im_Ln_pos_lt Re_Ln_pos_le Re_Ln_pos_lt
      abs_of_nonneg less_eq_real_def order_less_irrefl pi_half_gt_zero)
next
  assume "z\<noteq>0"
  have "Im (Ln z) = - pi / 2 \<Longrightarrow> Im z < 0 \<and> Re z = 0"
    by (metis Im_Ln_pos_le Re_Ln_pos_le Re_Ln_pos_lt_imp \<open>z \<noteq> 0\<close> abs_if
     add.inverse_inverse divide_minus_left less_eq_real_def linorder_not_le minus_pi_half_less_zero)
  moreover have "Im (Ln z) = - pi / 2" when "Im z < 0" "Re z = 0"
  proof -
    obtain r::real where "r>0" "z=r * (-\<i>)"
      by (metis \<open>Im z < 0\<close> \<open>Re z = 0\<close> add.commute add.inverse_inverse add.right_neutral
          complex_eq complex_i_mult_minus diff_0 mult.commute mult.left_commute neg_0_less_iff_less
          of_real_0 of_real_diff)
    then have "Im (Ln z) = Im (Ln (r*(-\<i>)))" by auto
    also have "... = Im (Ln (complex_of_real r) + Ln (- \<i>)) "
      apply (subst Ln_times_of_real)
      using \<open>r>0\<close> by auto
    also have "... = - pi/2"
      using \<open>r>0\<close> by simp
    finally show "Im (Ln z) = - pi / 2" .
  qed
  ultimately show "(Im(Ln z) = -pi/2 \<longleftrightarrow> Im(z) < 0 \<and> Re(z) = 0)" by auto
qed

lemma Im_Ln_eq:
  assumes "z\<noteq>0"
  shows "Im (Ln z) = (if Re z\<noteq>0 then
                        if Re z>0 then
                          arctan (Im z/Re z)
                        else if Im z\<ge>0 then
                           arctan (Im z/Re z) + pi
                        else
                           arctan (Im z/Re z) - pi
                      else
                        if Im z>0 then pi/2 else -pi/2)"
proof -
  have eq_arctan_pos:"Im (Ln z) = arctan (Im z/Re z)" when "Re z>0" for z
  proof -
    define wR where "wR=Re (Ln z)"
    define \<theta> where "\<theta> = arctan (Im z/Re z)"
    have "z\<noteq>0" using that by auto
    have "exp (Complex wR \<theta>) = z"
    proof (rule complex_eqI)
      have "Im (exp (Complex wR \<theta>)) =exp wR * sin \<theta> "
        unfolding Im_exp by simp
      also have "... = Im z"
        unfolding wR_def Re_Ln[OF \<open>z\<noteq>0\<close>] \<theta>_def using \<open>z\<noteq>0\<close> \<open>Re z>0\<close>
        by (auto simp add:sin_arctan divide_simps complex_neq_0 cmod_def real_sqrt_divide)
      finally show "Im (exp (Complex wR \<theta>)) = Im z" .
    next
      have "Re (exp (Complex wR \<theta>)) = exp wR * cos \<theta> "
        unfolding Re_exp by simp
      also have "... = Re z"
        unfolding wR_def Re_Ln[OF \<open>z\<noteq>0\<close>] \<theta>_def using \<open>z\<noteq>0\<close> \<open>Re z>0\<close>
        by (auto simp add:cos_arctan divide_simps complex_neq_0 cmod_def real_sqrt_divide)
      finally show "Re (exp (Complex wR \<theta>)) = Re z" .
    qed
    moreover have "-pi<\<theta>" "\<theta>\<le>pi"
      unfolding \<theta>_def
      subgoal by (auto intro:order_class.order.strict_trans[OF _ arctan_lbound])
      subgoal
        apply (rule preorder_class.less_imp_le)
        by (auto intro:order_class.order.strict_trans[OF arctan_ubound])
      done
    ultimately have "Ln z = Complex wR \<theta>" using Ln_unique by auto
    then show ?thesis using that unfolding \<theta>_def by auto
  qed

  have ?thesis when "Re z=0"
    using Im_Ln_eq_pi_half[OF \<open>z\<noteq>0\<close>] that
    apply auto
    using assms complex.expand by auto
  moreover have ?thesis when "Re z>0"
    using eq_arctan_pos[OF that] that by auto
  moreover have ?thesis when "Re z<0" "Im z\<ge>0"
  proof -
    have "Im (Ln (- z)) = arctan (Im (- z) / Re (- z))"
      apply (rule eq_arctan_pos)
      using that by auto
    moreover have "Ln (- z) = Ln z - \<i> * complex_of_real pi"
      apply (subst Ln_minus[OF \<open>z\<noteq>0\<close>])
      using that by auto
    ultimately show ?thesis using that by auto
  qed
  moreover have ?thesis when "Re z<0" "Im z<0"
  proof -
    have "Im (Ln (- z)) = arctan (Im (- z) / Re (- z))"
      apply (rule eq_arctan_pos)
      using that by auto
    moreover have "Ln (- z) = Ln z + \<i> * complex_of_real pi"
      apply (subst Ln_minus[OF \<open>z\<noteq>0\<close>])
      using that by auto
    ultimately show ?thesis using that by auto
  qed
  ultimately show ?thesis by linarith
qed

lemma exp_Arg2pi2pi_multivalue:
  assumes "exp (\<i>* of_real x) = z"
  shows "\<exists>k::int. x = Arg2pi z + 2*k*pi"
proof -
  define k where "k=floor( x/(2*pi))"
  define x' where "x'= x - (2*k*pi)"
  have "x'/(2*pi) \<ge>0"  unfolding x'_def k_def by (simp add: diff_divide_distrib)
  moreover have "x'/(2*pi) < 1"
  proof -
    have "x/(2*pi) - k < 1" unfolding k_def by linarith
    thus ?thesis unfolding k_def x'_def by (auto simp add:field_simps)
  qed
  ultimately have "x'\<ge>0" and "x'<2*pi" by (auto simp add:field_simps)
  moreover have "exp (\<i> * complex_of_real x') = z"
    using assms x'_def by  (auto simp add:field_simps )
  ultimately have "Arg2pi z = x'" using Arg2pi_unique[of 1 x' z,simplified] by auto
  hence " x = Arg2pi z + 2*k*pi" unfolding x'_def by auto
  thus ?thesis by auto
qed

lemma cos_eq_neg_periodic_intro:
  assumes "x - y=2*(of_int k)*pi + pi \<or> x + y = 2*(of_int k)*pi + pi"
  shows "cos x = - cos y" using assms
proof
  assume "x - y = 2 * (of_int k) * pi + pi"
  then have "cos x = cos ((y+ pi) + (of_int k)*(2*pi))"
    by (auto simp add:algebra_simps)
  also have "... = cos (y+pi)"
    using cos.periodic_simps[of "y+pi"]
    by (auto simp add:algebra_simps)
  also have "... = - cos y" by simp
  finally show "cos x = - cos y" by auto
next
  assume "x + y = 2 * real_of_int k * pi + pi "
  then have "cos x = cos ((- y+ pi) + (of_int k)*(2*pi))"
    apply (intro arg_cong[where f=cos])
    by (auto simp add:algebra_simps)
  also have "... = cos (- y +pi)"
    using cos.periodic_simps[of "-y+pi"]
    by (auto simp add:algebra_simps)
  also have "... = - cos y" by simp
  finally show "cos x = - cos y" by auto
qed

lemma cos_eq_periodic_intro:
  assumes "x - y=2*(of_int k)*pi \<or> x + y = 2*(of_int k)*pi"
  shows "cos x = cos y" using assms
proof
  assume "x - y = 2 * (of_int k) * pi "
  then have "cos x = cos (y + (of_int k)*(2*pi))"
    by (auto simp add:algebra_simps)
  also have "... = cos y"
    using cos.periodic_simps[of "y"]
    by (auto simp add:algebra_simps)
  finally show "cos x = cos y" by auto
next
  assume "x + y = 2 * of_int k * pi"
  then have "cos x = cos (- y + (of_int k)*(2*pi))"
    apply (intro arg_cong[where f=cos])
    by (auto simp add:algebra_simps)
  also have "... = cos (- y)"
    using cos.periodic_simps[of "-y"]
    by (auto simp add:algebra_simps)
  also have "... = cos y" by simp
  finally show "cos x = cos y" by auto
qed

lemma sin_tan_half: "sin (2*x) = 2 * tan x / (1 + (tan x)^2)"
  unfolding sin_double tan_def
  apply (cases "cos x=0")
  by (auto simp add:field_simps power2_eq_square)

lemma cos_tan_half: "cos x \<noteq>0 \<Longrightarrow>  cos (2*x) = (1 - (tan x)^2) / (1+ (tan x)^2)"
  unfolding cos_double tan_def by (auto simp add:field_simps )

lemma tan_eq_arctan_Ex:
  shows "tan x = y \<longleftrightarrow> (\<exists>k::int. x = arctan y + k*pi \<or> (x = pi/2 + k*pi \<and> y=0))"
proof
  assume asm:"tan x = y"
  obtain k::int where k:"-pi/2 < x-k*pi" "x-k*pi \<le> pi/2"
  proof -
    define k where "k=ceiling (x/pi - 1/2)"
    have "(x/pi - 1/2)\<le>k" unfolding k_def by auto
    then have "x-k*pi \<le> pi/2" by (auto simp add:field_simps)
    moreover have "k-1 < x/pi - 1/2" unfolding k_def by linarith
    then have "-pi/2 < x-k*pi"  by (auto simp add:field_simps)
    ultimately show ?thesis using that by auto
  qed
  have "x = arctan y + of_int k * pi" when "x \<noteq> pi/2 + k*pi"
  proof -
    have "tan (x - k * pi) = y" using asm tan_periodic_int[of _ "-k"] by auto
    then have "arctan y = x - real_of_int k * pi"
      apply (intro arctan_unique)
      using k that by (auto simp add:field_simps)
    then show ?thesis by auto
  qed
  moreover have "y=0" when "x = pi/2 + k*pi"
    using asm that by auto (simp add: tan_def)
  ultimately show "\<exists>k. x = arctan y + of_int k * pi \<or> (x = pi/2 + k*pi \<and> y=0)"
    using k by auto
next
  assume "\<exists>k::int. x = arctan y +  k * pi \<or> x = pi / 2 + k * pi \<and> y = 0"
  then show "tan x = y"
    by (metis arctan_unique cos_pi_half division_ring_divide_zero tan_def tan_periodic_int tan_total)
qed

lemma arccos_unique:
  assumes "0 \<le> x"
    and "x \<le> pi"
    and "cos x = y"
  shows "arccos y = x"
using arccos_cos assms(1) assms(2) assms(3) by blast

lemma cos_eq_arccos_Ex:
  "cos x = y \<longleftrightarrow> -1\<le>y \<and> y\<le>1 \<and> (\<exists>k::int. x = arccos y + 2*k*pi \<or> x = - arccos y + 2*k*pi)"
proof
  assume asm:"-1\<le>y \<and> y\<le>1 \<and> (\<exists>k::int. x = arccos y + 2*k*pi \<or> x = - arccos y + 2*k*pi)"
  then obtain k::int where "x = arccos y + 2*k*pi \<or> x = - arccos y + 2*k*pi" by auto
  moreover have "cos x = y" when "x = arccos y + 2*k*pi"
  proof -
    have "cos x = cos (arccos y + k*(2*pi))"
      using that by (auto simp add:algebra_simps)
    also have "... = cos (arccos y)"
      using cos.periodic_simps(3)[of "arccos y" k] by auto
    also have "... = y"
      using asm by auto
    finally show ?thesis .
  qed
  moreover have "cos x = y" when "x = -arccos y + 2*k*pi"
  proof -
    have "cos x = cos (- arccos y + k*2*pi)"
      unfolding that by (auto simp add:algebra_simps)
    also have "... = cos (arccos y - k*2*pi)"
      by (metis cos_minus minus_diff_eq uminus_add_conv_diff)
    also have "... = cos (arccos y)"
      using cos.periodic_simps(3)[of "arccos y" "-k"]
      by (auto simp add:algebra_simps)
    also have "... = y"
      using asm by auto
    finally show ?thesis .
  qed
  ultimately show "cos x = y" by auto
next
  assume asm:"cos x =y"
  let ?goal = "(\<exists>k::int. x = arccos y + 2*k*pi \<or> x = - arccos y + 2*k*pi)"
  obtain k::int where k:"-pi < x-k*2*pi" "x-k*2*pi \<le> pi"
  proof -
    define k where "k=ceiling (x/(2*pi) - 1/2)"
    have "(x/(2*pi) - 1/2)\<le>k" unfolding k_def by auto
    then have "x-k*2*pi \<le> pi" by (auto simp add:field_simps)
    moreover have "k-1 < x/(2*pi) - 1/2" unfolding k_def by linarith
    then have "-pi < x-k*2*pi"  by (auto simp add:field_simps)
    ultimately show ?thesis using that by auto
  qed
  have ?goal when "x-k*2*pi\<ge>0"
  proof -
    have "cos (x - k * 2*pi) = y"
      using cos.periodic_simps(3)[of x "-k"] asm by (auto simp add:field_simps)
    then have "arccos y = x - k * 2*pi"
      apply (intro arccos_unique)
      using k that by auto
    then show ?goal by auto
  qed
  moreover have ?goal when "\<not> x-k*2*pi \<ge>0"
  proof -
    have "cos (x - k * 2*pi) = y"
      using cos.periodic_simps(3)[of x "-k"] asm by (auto simp add:field_simps)
    then have "cos (k * 2*pi - x) = y"
      by (metis cos_minus minus_diff_eq)
    then have "arccos y = k * 2*pi - x"
      apply (intro arccos_unique)
      using k that by auto
    then show ?goal by auto
  qed
  ultimately have ?goal by auto
  moreover have "-1\<le>y \<and> y\<le>1" using asm by auto
  ultimately show "-1\<le>y \<and> y\<le>1 \<and> ?goal" by auto
qed

lemma uniform_discrete_tan_eq:
  "uniform_discrete {x::real. tan x = y}"
proof -
  have "x1=x2" when dist:"dist x1 x2<pi/2" and "tan x1=y" "tan x2=y" for x1 x2
  proof -
    obtain k1::int where x1:"x1 = arctan y + k1*pi \<or> (x1 = pi/2 + k1*pi \<and> y=0)"
      using tan_eq_arctan_Ex \<open>tan x1=y\<close> by auto
    obtain k2::int where x2:"x2 = arctan y + k2*pi \<or> (x2 = pi/2 + k2*pi \<and> y=0)"
      using tan_eq_arctan_Ex \<open>tan x2=y\<close> by auto
    let ?xk1="x1 = arctan y + k1*pi" and ?xk1'="x1 = pi/2 + k1*pi \<and> y=0"
    let ?xk2="x2 = arctan y + k2*pi" and ?xk2'="x2 = pi/2 + k2*pi \<and> y=0"
    have ?thesis when "(?xk1 \<and> ?xk2) \<or> (?xk1' \<and> ?xk2')"
    proof -
      have "x1-x2= (k1 - k2) *pi" when ?xk1 ?xk2
        using arg_cong2[where f=minus,OF \<open>?xk1\<close> \<open>?xk2\<close>]
        by (auto simp add:algebra_simps)
      moreover have "x1-x2= (k1 - k2) *pi" when ?xk1' ?xk2'
        using arg_cong2[where f=minus,OF conjunct1[OF \<open>?xk1'\<close>] conjunct1[OF \<open>?xk2'\<close>]]
        by (auto simp add:algebra_simps)
      ultimately have "x1-x2= (k1 - k2) *pi" using that by auto
      then have "\<bar>k1 - k2\<bar> < 1/2"
        using dist[unfolded dist_real_def] by (auto simp add:abs_mult)
      then have "k1=k2" by linarith
      then show ?thesis using that by auto
    qed
    moreover have ?thesis when ?xk1 ?xk2'
    proof -
      have "x1 = k1*pi" "x2 = pi / 2 + k2 * pi" using \<open>?xk2'\<close> \<open>?xk1\<close> by auto
      from arg_cong2[where f=minus,OF this] have "x1 - x2 = (k1 - k2) * pi -pi/2"
        by (auto simp add:algebra_simps)
      then have "\<bar>(k1 - k2) * pi -pi/2\<bar> < pi/2" using dist[unfolded dist_real_def] by auto
      then have "0<k1-k2" "k1-k2<1"
        unfolding abs_less_iff  by (auto simp add: zero_less_mult_iff)
      then have False by simp
      then show ?thesis by auto
    qed
    moreover have ?thesis when ?xk1' ?xk2
    proof -
      have "x1 = pi / 2 + k1*pi" "x2 = k2 * pi" using \<open>?xk2\<close> \<open>?xk1'\<close> by auto
      from arg_cong2[where f=minus,OF this] have "x1 - x2 = (k1 - k2) * pi + pi/2"
        by (auto simp add:algebra_simps)
      then have "\<bar>(k1 - k2) * pi + pi/2\<bar> < pi/2" using dist[unfolded dist_real_def] by auto
      then have "\<bar>(k1 - k2 + 1/2)*pi\<bar> < pi/2" by (auto simp add:algebra_simps)
      then have "\<bar>(k1 - k2 + 1/2)\<bar> < 1/2" by (auto simp add:abs_mult)
      then have "-1<k1-k2 \<and> k1-k2<0"
        unfolding abs_less_iff by linarith
      then have False by auto
      then show ?thesis by auto
    qed
    ultimately show ?thesis using x1 x2 by blast
  qed
  then show ?thesis unfolding uniform_discrete_def
    apply (intro exI[where x="pi/2"])
    by auto
qed

lemma get_norm_value:
  fixes a::"'a::{floor_ceiling}"
  assumes "pp>0"
  obtains k::int and a1 where "a=(of_int k)*pp+a1" "a0\<le>a1" "a1<a0+pp"
proof -
  define k where "k=floor ((a-a0)/pp)"
  define a1 where "a1=a-(of_int k)*pp"
  have "of_int \<lfloor>(a - a0) / pp\<rfloor> * pp \<le> a- a0" 
    using assms by (meson le_divide_eq of_int_floor_le)
  moreover have "a-a0 < of_int (\<lfloor>(a - a0) / pp\<rfloor>+1) * pp" 
    using assms by (meson divide_less_eq floor_correct)
  ultimately show ?thesis 
    apply (intro that[of k a1])
    unfolding k_def a1_def using assms by (auto simp add:algebra_simps)
qed

(*Is it possible to generalise or simplify this messy proof?*)
lemma filtermap_tan_at_right:
  fixes a::real
  assumes "cos a\<noteq>0"
  shows "filtermap tan (at_right a) = at_right (tan a)"
proof -
  obtain k::int and a1 where aa1:"a=k*pi+a1" and "-pi/2\<le>a1" "a1<pi/2"
    using get_norm_value[of pi a "-pi/2"] by auto
  have "-pi/2 < a1" 
  proof (rule ccontr)
    assume "\<not> - pi / 2 < a1"
    then have "a1=- pi / 2" using \<open>-pi/2\<le>a1\<close> by auto
    then have "cos a = 0" unfolding aa1
      by (metis (no_types, hide_lams) add.commute add_0_left cos_pi_half 
              diff_eq_eq mult.left_neutral mult_minus_right mult_zero_left 
              sin_add sin_pi_half sin_zero_iff_int2 times_divide_eq_left uminus_add_conv_diff)
    then show False using assms by auto
  qed
  have "eventually P (at_right (tan a))" 
    when "eventually P (filtermap tan (at_right a))" for P
  proof -
    obtain b1 where "b1>a" and b1_imp:" \<forall>y>a. y < b1 \<longrightarrow> P (tan y)"
      using \<open>eventually P (filtermap tan (at_right a))\<close>
      unfolding eventually_filtermap eventually_at_right 
      by (metis eventually_at_right_field)
    define b2 where "b2=min b1 (k*pi+pi/4+a1/2)"  
    define b3 where "b3=b2 - k*pi"
    have "-pi/2 < b3" "b3<pi/2" 
    proof -
      have "a1<b3"
        using \<open>b1>a\<close> aa1 \<open>a1<pi/2\<close> unfolding b2_def b3_def by (auto simp add:field_simps)
      then show "-pi/2 < b3" using \<open>-pi/2\<le>a1\<close> by auto
      show "b3 < pi/2"
        unfolding b2_def b3_def
        apply (subst min_diff_distrib_left)
        apply (rule min.strict_coboundedI2)
        using \<open>b1>a\<close> aa1 \<open>a1<pi/2\<close> \<open>-pi/2<a1\<close> by auto
    qed
    have "tan b2 > tan a" 
    proof -
      have "tan a = tan a1"
        using aa1 by (simp add: add.commute)
      also have "... < tan b3"
      proof -
        have "a1<b3"
          using \<open>b1>a\<close> aa1 \<open>a1<pi/2\<close> unfolding b2_def b3_def by (auto simp add:field_simps)
        then show ?thesis
          using tan_monotone \<open>-pi/2 < a1\<close> \<open>b3 < pi/2\<close> by simp
      qed
      also have "... = tan b2" unfolding b3_def
        by (metis Groups.mult_ac(2) add_uminus_conv_diff mult_minus_right of_int_minus 
          tan_periodic_int)
      finally show ?thesis .
    qed
    moreover have "P y" when "y>tan a" "y < tan b2" for y
    proof -
      define y1 where "y1=arctan y+ k * pi"
      have "a<y1" 
      proof -
        have "arctan (tan a) < arctan y" using \<open>y>tan a\<close> arctan_monotone by auto
        then have "a1<arctan y"
          using arctan_tan \<open>-pi/2 < a1\<close> \<open>a1<pi/2\<close> unfolding aa1 by (simp add: add.commute)
        then show ?thesis unfolding y1_def aa1 by auto
      qed
      moreover have "y1<b2"
      proof - 
        have "arctan y < arctan (tan b2)"
          using \<open>y < tan b2\<close> arctan_monotone by auto
        moreover have "arctan (tan b2) = b3"
          using arctan_tan[of b3] \<open>-pi/2 < b3\<close> \<open>b3<pi/2\<close> unfolding b3_def 
          by (metis add.inverse_inverse diff_minus_eq_add divide_minus_left mult.commute 
            mult_minus_right of_int_minus tan_periodic_int)
        ultimately have "arctan y < b3" by auto
        then show ?thesis unfolding y1_def b3_def by auto
      qed
      moreover have "\<forall>y>a. y < b2 \<longrightarrow> P (tan y)"
        using b1_imp unfolding b2_def by auto
      moreover have "tan y1=y" unfolding y1_def by (auto simp add:tan_arctan)
      ultimately show ?thesis by auto
    qed
    ultimately show "eventually P (at_right (tan a))" 
      unfolding eventually_at_right by (metis eventually_at_right_field)
  qed
  moreover have "eventually P (filtermap tan (at_right a))" 
    when "eventually P (at_right (tan a))" for P
  proof -
    obtain b1 where "b1>tan a" and b1_imp:"\<forall>y>tan a. y < b1 \<longrightarrow> P y" 
      using \<open>eventually P (at_right (tan a))\<close> unfolding eventually_at_right 
      by (metis eventually_at_right_field)
    define b2 where "b2=arctan b1 + k*pi" 
    have "a1 < arctan b1" 
      by (metis \<open>- pi / 2 < a1\<close> \<open>a1 < pi / 2\<close> \<open>tan a < b1\<close> aa1 add.commute arctan_less_iff 
            arctan_tan divide_minus_left tan_periodic_int)
    then have "b2>a" unfolding aa1 b2_def by auto
    moreover have "P (tan y)" when "y>a" "y < b2" for y
    proof -
      define y1 where "y1 = y - k*pi"
      have "a1 < y1" "y1 < arctan b1" unfolding y1_def
        subgoal using \<open>y>a\<close> unfolding aa1 by auto
        subgoal using b2_def that(2) by linarith
        done
      then have "tan a1 < tan y1" "tan y1< b1"
        subgoal using \<open>a1>-pi/2\<close>
          apply (intro tan_monotone,simp,simp)
          using arctan_ubound less_trans by blast
        subgoal 
          by (metis \<open>- pi / 2 < a1\<close> \<open>a1 < y1\<close> \<open>y1 < arctan b1\<close> arctan_less_iff arctan_tan 
              arctan_ubound divide_minus_left less_trans)
        done
      have "tan y>tan a" 
        by (metis \<open>tan a1 < tan y1\<close> aa1 add.commute add_uminus_conv_diff mult.commute 
            mult_minus_right of_int_minus tan_periodic_int y1_def)
      moreover have "tan y<b1" 
        by (metis \<open>tan y1 < b1\<close> add_uminus_conv_diff mult.commute mult_minus_right 
            of_int_minus tan_periodic_int y1_def)
      ultimately show ?thesis using b1_imp by auto
    qed
    ultimately show ?thesis unfolding eventually_filtermap eventually_at_right 
      by (metis eventually_at_right_field)
  qed
  ultimately show ?thesis unfolding filter_eq_iff by blast
qed

lemma filtermap_tan_at_left:
  fixes a::real
  assumes "cos a\<noteq>0"
  shows "filtermap tan (at_left a) = at_left (tan a)"
proof -
  have "filtermap tan (at_right (- a)) = at_right (tan (- a))" 
    using filtermap_tan_at_right[of "-a"] assms by auto
  then have "filtermap (uminus o tan) (at_left a) = filtermap uminus (at_left (tan a))"
    unfolding at_right_minus filtermap_filtermap comp_def by auto
  then have "filtermap uminus (filtermap (uminus o tan) (at_left a)) 
      = filtermap uminus (filtermap uminus (at_left (tan a)))"
    by auto
  then show ?thesis 
    unfolding filtermap_filtermap comp_def by auto
qed

lemma cos_zero_iff_int2:
  fixes x::real
  shows "cos x = 0 \<longleftrightarrow> (\<exists>n::int. x = n * pi +  pi/2)"
  using sin_zero_iff_int2[of "x-pi/2"] unfolding sin_cos_eq 
  by (auto simp add:algebra_simps)

lemma filtermap_tan_at_right_inf:
  fixes a::real
  assumes "cos a=0"
  shows "filtermap tan (at_right a) = at_bot"
proof -
  obtain k::int where ak:"a=k*pi + pi/2"
    using cos_zero_iff_int2 assms by auto
  have "eventually P at_bot" when "eventually P (filtermap tan (at_right a))" for P 
  proof -
    obtain b1 where "b1>a" and b1_imp:"\<forall>y>a. y < b1 \<longrightarrow> P (tan y)" 
      using \<open>eventually P (filtermap tan (at_right a))\<close> 
      unfolding eventually_filtermap eventually_at_right 
      by (metis eventually_at_right_field)
    define b2 where "b2=min (k*pi+pi) b1"
    have "P y" when "y<tan b2" for y
    proof -
      define y1 where "y1=(k+1)*pi+arctan y"
      have "a < y1" 
        unfolding ak y1_def using arctan_lbound[of y]
        by (auto simp add:field_simps)
      moreover have "y1 < b2" 
      proof -
        define b3 where "b3=b2-(k+1) * pi"
        have "-pi/2 < b3" "b3<pi/2"
          using \<open>b1>a\<close> unfolding b3_def b2_def ak 
          by (auto simp add:field_simps min_mult_distrib_left intro!:min.strict_coboundedI1)
        then have "arctan (tan b3) = b3"
          by (simp add: arctan_tan)
        then have "arctan (tan b2) = b3" 
          unfolding b3_def by (metis diff_eq_eq tan_periodic_int)
        then have "arctan y < b3"
          using arctan_monotone[OF \<open>y<tan b2\<close>] by simp
        then show ?thesis
          unfolding y1_def b3_def by auto
      qed
      then have "y1<b1" unfolding b2_def by auto
      ultimately have " P (tan y1)" using b1_imp[rule_format,of y1,simplified] by auto
      then show ?thesis unfolding y1_def by (metis add.commute arctan tan_periodic_int)
    qed
    then show ?thesis unfolding eventually_at_bot_dense by auto
  qed
  moreover have "eventually P (filtermap tan (at_right a))" when "eventually P at_bot" for P 
  proof -
    obtain b1 where b1_imp:"\<forall>n<b1. P n"
      using \<open>eventually P at_bot\<close> unfolding eventually_at_bot_dense by auto
    define b2 where "b2=arctan b1 + (k+1)*pi"
    have "b2>a" unfolding ak b2_def using arctan_lbound[of b1]
      by (auto simp add:algebra_simps)
    moreover have "P (tan y)" when "a < y" " y < b2 " for y
    proof -
      define y1 where "y1=y-(k+1)*pi"
      have "tan y1 < tan (arctan b1)"
        apply (rule tan_monotone)
        subgoal using \<open>a<y\<close> unfolding y1_def ak by (auto simp add:algebra_simps)
        subgoal using \<open>y < b2\<close> unfolding y1_def b2_def by (auto simp add:algebra_simps)
        subgoal using arctan_ubound by auto
        done
      then have "tan y1<b1" by (simp add: arctan)
      then have "tan y < b1" unfolding y1_def 
        by (metis diff_eq_eq tan_periodic_int)
      then show ?thesis using b1_imp by auto
    qed
    ultimately show "eventually P (filtermap tan (at_right a))"
      unfolding eventually_filtermap eventually_at_right 
      by (metis eventually_at_right_field)
  qed
  ultimately show ?thesis unfolding filter_eq_iff by auto
qed

lemma filtermap_tan_at_left_inf:
  fixes a::real
  assumes "cos a=0"
  shows "filtermap tan (at_left a) = at_top"
proof -
  have "filtermap tan (at_right (- a)) = at_bot"
    using filtermap_tan_at_right_inf[of "-a"] assms by auto
  then have "filtermap (uminus o tan) (at_left a) = at_bot"
    unfolding at_right_minus filtermap_filtermap comp_def by auto
  then have "filtermap uminus (filtermap (uminus o tan) (at_left a)) = filtermap uminus at_bot"
    by auto
  then show ?thesis 
    unfolding filtermap_filtermap comp_def using at_top_mirror[where 'a=real] by auto
qed

subsection \<open>Periodic set\<close>

(*Devised to characterize roots of Trigonometric equations, which are usually uniformly discrete.*)
definition periodic_set:: "real set \<Rightarrow> real \<Rightarrow> bool" where
  "periodic_set S \<delta> \<longleftrightarrow> (\<exists>B. finite B \<and> (\<forall>x\<in>S. \<exists>b\<in>B. \<exists>k::int. x =b + k * \<delta> ))"

lemma periodic_set_multiple:
  assumes "k\<noteq>0"
  shows "periodic_set S \<delta> \<longleftrightarrow> periodic_set S (of_int k*\<delta>)"
proof
  assume asm:"periodic_set S \<delta> "
  then obtain B1 where "finite B1" and B1_def:"\<forall>x\<in>S. \<exists>b\<in>B1. (\<exists>k::int. x = b + k * \<delta>)"
    unfolding periodic_set_def by metis
  define B where "B = B1 \<union> {b+i*\<delta> | b i. b\<in>B1 \<and> i\<in>{0..<\<bar>k\<bar>}}"
  have "\<exists>b\<in>B. \<exists>k'. x = b + real_of_int k' * (real_of_int k * \<delta>)" when "x\<in>S" for x
  proof -
    obtain b1 and k1::int where "b1\<in>B1" and x_\<delta>:"x = b1 + k1 * \<delta>"
      using B1_def[rule_format, OF \<open>x\<in>S\<close>] by auto
    define r d where "r= k1 mod \<bar>k\<bar>" and "d = k1 div \<bar>k\<bar>"
    define b kk where "b=b1+r*\<delta>" and "kk = (if k>0 then d else -d)"
    have "x = b1 + (r+\<bar>k\<bar>*d)*\<delta>" using x_\<delta> unfolding r_def d_def by auto
    then have "x = b + kk*(k*\<delta>)" unfolding b_def kk_def using \<open>k\<noteq>0\<close>
      by (auto simp add:algebra_simps)
    moreover have "b\<in>B"
    proof -
      have "r \<in> {0..<\<bar>k\<bar>}" unfolding r_def by (simp add: \<open>k\<noteq>0\<close>)
      then show ?thesis unfolding b_def B_def using \<open>b1\<in>B1\<close> by blast
    qed
    ultimately show ?thesis by auto
  qed
  moreover have "finite B" unfolding B_def using \<open>finite B1\<close>
    by (simp add: finite_image_set2)
  ultimately show "periodic_set S (real_of_int k * \<delta>)" unfolding periodic_set_def by auto
next
  assume "periodic_set S (real_of_int k * \<delta>)"
  then show "periodic_set S \<delta>" unfolding periodic_set_def
    by (metis mult.commute mult.left_commute of_int_mult)
qed

lemma periodic_set_empty[simp]: "periodic_set {} \<delta>"
  unfolding periodic_set_def by auto

lemma periodic_set_finite:
  assumes "finite S"
  shows "periodic_set S \<delta>"
unfolding periodic_set_def using assms mult.commute by force

lemma periodic_set_subset[elim]:
  assumes "periodic_set S \<delta>" "T \<subseteq> S"
  shows "periodic_set T \<delta>"
using assms unfolding periodic_set_def by (meson subsetCE)

lemma periodic_set_union:
  assumes "periodic_set S \<delta>" "periodic_set T \<delta>"
  shows "periodic_set (S \<union> T) \<delta>"
using assms unfolding periodic_set_def by (metis Un_iff infinite_Un)

lemma periodic_imp_uniform_discrete:
  assumes "periodic_set S \<delta>"
  shows "uniform_discrete S"
proof -
  have ?thesis when "S\<noteq>{}" "\<delta>\<noteq>0"
  proof -
    obtain B g where "finite B" and g_def:"\<forall>x\<in>S. g x\<in>B \<and> (\<exists>k::int. x = g x + k * \<delta>)"
      using assms unfolding periodic_set_def by metis
    define P where "P = ((*) \<delta>) ` Ints"
    define B_diff where "B_diff = {\<bar>x-y\<bar> | x y.  x\<in>B \<and> y\<in>B} - P"
    have "finite B_diff" unfolding B_diff_def using \<open>finite B\<close>
      by (simp add: finite_image_set2)
    define e where "e = (if setdist B_diff P = 0 then \<bar>\<delta>\<bar> else min (setdist B_diff P) (\<bar>\<delta>\<bar>))"
    have "e>0"
      unfolding e_def using setdist_pos_le[unfolded order_class.le_less] \<open>\<delta>\<noteq>0\<close>
      by auto
    moreover have "x=y" when "x\<in>S" "y\<in>S" "dist x y<e" for x y
    proof -
      obtain k1::int where k1:"x = g x + k1 * \<delta>" and "g x\<in>B" using g_def \<open>x\<in>S\<close> by auto
      obtain k2::int where k2:"y = g y + k2 * \<delta>" and "g y\<in>B" using g_def \<open>y\<in>S\<close> by auto
      have ?thesis when "\<bar>g x - g y\<bar> \<in> P"
      proof -
        obtain k::int where k:"g x - g y = k * \<delta>"
        proof -
          obtain k' where "k'\<in>Ints" and *:"\<bar>g x - g y\<bar> = \<delta> * k'"
            using \<open>\<bar>g x - g y\<bar> \<in> P\<close> unfolding P_def image_iff by auto
          then obtain k where **:"k' = of_int k" using Ints_cases by auto
          show ?thesis
            apply (cases "g x - g y \<ge> 0")
            subgoal using that[of k] * ** by simp
            subgoal using that[of "-k"] * ** by (auto simp add:algebra_simps)
            done
        qed
        have "dist x y = \<bar>(g x - g y)+(k1-k2)*\<delta>\<bar>"
          unfolding dist_real_def by (subst k1,subst k2,simp add:algebra_simps)
        also have "... = \<bar>(k+k1-k2)*\<delta>\<bar>"
          by (subst k,simp add:algebra_simps)
        also have "... = \<bar>k+k1-k2\<bar>*\<bar>\<delta>\<bar>" by (simp add: abs_mult)
        finally have *:"dist x y = \<bar>k+k1-k2\<bar>*\<bar>\<delta>\<bar>" .
        then have "\<bar>k+k1-k2\<bar>*\<bar>\<delta>\<bar> < e" using \<open>dist x y<e\<close> by auto
        then have "\<bar>k+k1-k2\<bar>*\<bar>\<delta>\<bar> < \<bar>\<delta>\<bar>"
          apply (elim order_class.dual_order.strict_trans1[rotated])
          unfolding e_def by auto
        then have "\<bar>k+k1-k2\<bar> = 0" unfolding e_def using \<open>\<delta>\<noteq>0\<close> by force
        then have "dist x y=0" using * by auto
        then show ?thesis by auto
      qed
      moreover have ?thesis when "\<bar>g x - g y\<bar> \<notin> P"
      proof -
        have "\<bar>g x - g y\<bar> \<in> B_diff" unfolding B_diff_def using \<open>g x\<in>B\<close> \<open>g y\<in>B\<close> that by auto
        have "e \<le> \<bar>\<bar>g x - g y\<bar> - \<bar>(k1-k2)*\<delta>\<bar>\<bar>"
        proof -
          have "\<bar>g x - g y\<bar> \<in> B_diff" unfolding B_diff_def using \<open>g x\<in>B\<close> \<open>g y\<in>B\<close> that by auto
          moreover have "\<bar>(k1-k2)*\<delta>\<bar> \<in> P" unfolding P_def
            apply (intro rev_image_eqI[of "(if \<delta>\<ge>0 then \<bar>of_int(k1-k2)\<bar> else - \<bar>of_int(k1-k2)\<bar>)"])
            apply (metis Ints_minus Ints_of_int of_int_abs)
            by (auto simp add:abs_mult)
          ultimately have "\<bar>\<bar>g x - g y\<bar> - \<bar>(k1-k2)*\<delta>\<bar>\<bar> \<ge> setdist B_diff P"
            using setdist_le_dist[of _ B_diff  _ P] dist_real_def by auto
          moreover have "setdist B_diff P \<noteq> 0"
          proof -
            have "compact B_diff " using  \<open>finite B_diff\<close> using finite_imp_compact by blast
            moreover have "closed P"
              unfolding P_def using closed_scaling[OF closed_Ints[where 'a=real], of \<delta>] by auto
            moreover have "P \<noteq> {}" using Ints_0 unfolding P_def by blast
            moreover have "B_diff \<inter> P = {}" unfolding B_diff_def by auto
            moreover have "B_diff \<noteq>{}" unfolding B_diff_def using \<open>g x\<in>B\<close> \<open>g y\<in>B\<close> that by auto
            ultimately show ?thesis using setdist_eq_0_compact_closed[of B_diff P] by auto
          qed
          ultimately show ?thesis unfolding e_def by argo
        qed
        also have "... \<le> \<bar>(g x - g y) + (k1-k2)*\<delta>\<bar>"
        proof -
          define t1 where "t1=g x - g y"
          define t2 where "t2 = of_int (k1 - k2) * \<delta>"
          show ?thesis
            apply (fold t1_def t2_def)
            by linarith
        qed
        also have "... = dist x y"
          unfolding dist_real_def
          by (subst (2) k1,subst (2) k2,simp add:algebra_simps)
        finally have "dist x y\<ge>e" .
        then have False using \<open>dist x y<e\<close> by auto
        then show ?thesis by auto
      qed
      ultimately show ?thesis by auto
    qed
    ultimately show ?thesis unfolding uniform_discrete_def by auto
  qed
  moreover have ?thesis when "S={}" using that by auto
  moreover have ?thesis when "\<delta>=0"
  proof -
    obtain B g where "finite B" and g_def:"\<forall>x\<in>S. g x\<in>B \<and> (\<exists>k::int. x = g x + k * \<delta>)"
      using assms unfolding periodic_set_def by metis
    then have "\<forall>x\<in>S. g x\<in>B \<and> (x = g x)" using that by fastforce
    then have "S \<subseteq> g ` B" by auto
    then have "finite S" using \<open>finite B\<close> by (auto elim:finite_subset)
    then show ?thesis using uniform_discrete_finite_iff by blast
  qed
  ultimately show ?thesis by blast
qed

lemma periodic_set_tan_linear:
  assumes "a\<noteq>0" "c\<noteq>0"
  shows "periodic_set (roots (\<lambda>x. a*tan (x/c) + b)) (c*pi)"
proof -
  define B where "B = { c*arctan (- b / a), c*pi/2}"
  have "\<exists>b\<in>B. \<exists>k::int. x = b + k * (c*pi)" when "x\<in>roots (\<lambda>x. a * tan (x/c) + b)" for x
  proof -
    define C1 where "C1 = (\<exists>k::int. x = c*arctan (- b / a) + k * (c*pi))"
    define C2 where "C2 = (\<exists>k::int. x = c*pi / 2 + k  * (c*pi) \<and> - b / a = 0)"
    have "tan (x/c) = - b/a" using that \<open>a\<noteq>0\<close> unfolding roots_within_def
      by (auto simp add:field_simps)
    then have "C1 \<or> C2" unfolding C1_def C2_def using tan_eq_arctan_Ex[of "x/c" "-b/a"]  \<open>c\<noteq>0\<close>
      by (auto simp add:field_simps)
    moreover have ?thesis when C1 using that unfolding C1_def B_def by blast
    moreover have ?thesis when C2 using that unfolding C2_def B_def by blast
    ultimately show ?thesis by auto
  qed
  moreover have "finite B" unfolding B_def by auto
  ultimately show ?thesis unfolding periodic_set_def by auto
qed

lemma periodic_set_cos_linear:
  assumes "a\<noteq>0" "c\<noteq>0"
  shows "periodic_set (roots (\<lambda>x. a*cos (x/c) + b)) (2*c*pi)"
proof -
  define B where "B = { c*arccos (- b / a), - c*arccos (- b / a)}"
  have "\<exists>b\<in>B. \<exists>k::int. x = b + k * (2*c*pi)"
    when "x\<in>roots (\<lambda>x. a * cos (x/c) + b)" for x
  proof -
    define C1 where "C1 = (\<exists>k::int. x = c*arccos (- b / a) + k * (2*c*pi))"
    define C2 where "C2 = (\<exists>k::int. x = - c*arccos (- b / a) + k * (2*c*pi))"
    have "cos (x/c) = - b/a" using that \<open>a\<noteq>0\<close> unfolding roots_within_def
      by (auto simp add:field_simps)
    then have "C1 \<or> C2"
      unfolding cos_eq_arccos_Ex ex_disj_distrib C1_def C2_def using \<open>c\<noteq>0\<close>
      apply (auto simp add:divide_simps)
      by (auto simp add:algebra_simps)
    moreover have ?thesis when C1 using that unfolding C1_def B_def by blast
    moreover have ?thesis when C2 using that unfolding C2_def B_def by blast
    ultimately show ?thesis by auto
  qed
  moreover have "finite B" unfolding B_def by auto
  ultimately show ?thesis unfolding periodic_set_def by auto
qed

lemma periodic_set_tan_poly:
  assumes "p\<noteq>0" "c\<noteq>0"
  shows "periodic_set (roots (\<lambda>x. poly p (tan (x/c)))) (c*pi)"
  using assms
proof (induct rule:poly_root_induct_alt)
  case 0
  then show ?case by simp
next
  case (no_proots p)
  then show ?case unfolding roots_within_def by simp
next
  case (root a p)
  have "roots (\<lambda>x. poly ([:- a, 1:] * p) (tan (x/c))) = roots (\<lambda>x. tan (x/c) - a)
          \<union> roots (\<lambda>x. poly p (tan (x/c)))"
    unfolding roots_within_def by auto
  moreover have "periodic_set (roots (\<lambda>x. tan (x/c) - a)) (c*pi)"
    using periodic_set_tan_linear[OF _ \<open>c\<noteq>0\<close> ,of 1 "-a",simplified] .
  moreover have "periodic_set (roots (\<lambda>x. poly p (tan (x/c)))) (c*pi)" using root by fastforce
  ultimately show ?case using periodic_set_union by simp
qed

lemma periodic_set_sin_cos_linear:
  fixes a b c ::real
  assumes "a\<noteq>0 \<or> b\<noteq>0 \<or> c\<noteq>0"
  shows "periodic_set (roots (\<lambda>x. a * cos x + b * sin x + c)) (4*pi)"
proof -
  define f where "f x= a * cos x + b * sin x + c" for x
  have "roots f = (roots f \<inter> {x. cos (x/2) = 0}) \<union> (roots f \<inter> {x. cos (x/2) \<noteq> 0})"
    by auto
  moreover have "periodic_set (roots f \<inter> {x. cos (x/2) = 0}) (4*pi)"
  proof -
    have "periodic_set ({x. cos (x/2) = 0}) (4*pi)"
      using periodic_set_cos_linear[of 1 2 0,unfolded roots_within_def,simplified] by simp
    then show ?thesis by auto
  qed
  moreover have "periodic_set (roots f \<inter> {x. cos (x/2) \<noteq> 0}) (4*pi)"
  proof -
    define p where "p=[:a+c,2*b,c-a:]"
    have "poly p (tan (x/2)) = 0 \<longleftrightarrow> f x=0" when "cos (x/2) \<noteq>0" for x
    proof -
      define t where "t=tan (x/2)"
      define tt where "tt = 1+t^2"
      have "cos x = (1-t^2) / tt" unfolding tt_def t_def
        using cos_tan_half[OF that,simplified] by simp
      moreover have "sin x = 2*t / tt" unfolding tt_def t_def
        using sin_tan_half[of "x/2",simplified] by simp
      moreover have "tt\<noteq>0" unfolding tt_def
        by (metis power_one sum_power2_eq_zero_iff zero_neq_one)
      ultimately show ?thesis
        unfolding f_def p_def
        apply (fold t_def)
        apply simp
        apply (auto simp add:field_simps)
        by (auto simp add:algebra_simps tt_def power2_eq_square)
    qed
    then have "roots f \<inter> {x. cos (x/2) \<noteq> 0} = roots (\<lambda>x. poly p (tan (x/2))) \<inter> {x. cos (x/2) \<noteq> 0}"
      unfolding roots_within_def by auto
    moreover have "periodic_set (roots (\<lambda>x. poly p (tan (x/2))) \<inter> {x. cos (x/2) \<noteq> 0}) (4*pi)"
    proof -
      have "p\<noteq>0" unfolding p_def using assms by auto
      then have "periodic_set (roots (\<lambda>x. poly p (tan (x/2)))) (4*pi)"
        using periodic_set_tan_poly[of p 2,simplified]
          periodic_set_multiple[of 2 _ "2*pi",simplified]
        by auto
      then show ?thesis by auto
    qed
    ultimately show ?thesis by auto
  qed
  ultimately show "periodic_set (roots f) (4*pi)" using periodic_set_union by metis
qed

end
