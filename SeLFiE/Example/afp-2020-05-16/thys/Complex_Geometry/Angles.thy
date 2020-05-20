(* ---------------------------------------------------------------------------- *)
subsection \<open>Angle between two vectors\<close>
(* ---------------------------------------------------------------------------- *)

text \<open>In this section we introduce different measures of angle between two vectors (represented by complex numbers).\<close>

theory Angles
imports More_Transcendental Canonical_Angle More_Complex
begin

(* ---------------------------------------------------------------------------- *)
subsubsection \<open>Oriented angle\<close>
(* ---------------------------------------------------------------------------- *)

text \<open>Oriented angle between two vectors (it is always in the interval $(-\pi, \pi]$).\<close>
definition ang_vec ("\<angle>") where
  [simp]: "\<angle> z1 z2 \<equiv> \<downharpoonright>arg z2 - arg z1\<downharpoonleft>"

lemma ang_vec_bounded:
  shows "-pi < \<angle> z1 z2 \<and> \<angle> z1 z2 \<le> pi"
  by (simp add: canon_ang(1) canon_ang(2))

lemma ang_vec_sym:
  assumes "\<angle> z1 z2 \<noteq> pi"
  shows "\<angle> z1 z2 = - \<angle> z2 z1"
  using assms
  unfolding ang_vec_def
  using canon_ang_uminus[of "arg z2 - arg z1"]
  by simp

lemma ang_vec_sym_pi:
  assumes "\<angle> z1 z2 = pi"
  shows "\<angle> z1 z2 = \<angle> z2 z1"
  using assms
  unfolding ang_vec_def
  using canon_ang_uminus_pi[of "arg z2 - arg z1"]
  by simp

lemma ang_vec_plus_pi1:
  assumes "\<angle> z1 z2 > 0"
  shows "\<downharpoonright>\<angle> z1 z2 + pi\<downharpoonleft> = \<angle> z1 z2 - pi"
proof (rule canon_ang_eqI)
  show "\<exists> x::int. \<angle> z1 z2 - pi - (\<angle> z1 z2 + pi) = 2 * real_of_int x * pi"
    by (rule_tac x="-1" in exI) auto
next
  show "- pi < \<angle> z1 z2 - pi \<and> \<angle> z1 z2 - pi \<le> pi"
    using assms
    unfolding ang_vec_def
    using canon_ang(1)[of "arg z2 - arg z1"] canon_ang(2)[of "arg z2 - arg z1"]
    by auto
qed

lemma ang_vec_plus_pi2:
  assumes "\<angle> z1 z2 \<le> 0"
  shows "\<downharpoonright>\<angle> z1 z2 + pi\<downharpoonleft> = \<angle> z1 z2 + pi"
proof (rule canon_ang_id)
  show "- pi < \<angle> z1 z2 + pi \<and> \<angle> z1 z2 + pi \<le> pi"
    using assms
    unfolding ang_vec_def
    using canon_ang(1)[of "arg z2 - arg z1"] canon_ang(2)[of "arg z2 - arg z1"]
    by auto
qed

lemma ang_vec_opposite1:
  assumes "z1 \<noteq> 0"
  shows "\<angle> (-z1) z2 = \<downharpoonright>\<angle> z1 z2 - pi\<downharpoonleft>"
proof-
  have "\<angle> (-z1) z2 = \<downharpoonright>arg z2 - (arg z1 + pi)\<downharpoonleft>"
    unfolding ang_vec_def
    using arg_uminus[OF assms] 
    using canon_ang_arg[of z2, symmetric]
    using canon_ang_diff[of "arg z2" "arg z1 + pi", symmetric]
    by simp
  moreover
  have "\<downharpoonright>\<angle> z1 z2 - pi\<downharpoonleft> = \<downharpoonright>arg z2 - arg z1 - pi\<downharpoonleft>"
    using canon_ang_id[of pi, symmetric]
    using canon_ang_diff[of "arg z2 - arg z1" "pi", symmetric]
    by simp_all
  ultimately
  show ?thesis
    by (simp add: field_simps)
qed

lemma ang_vec_opposite2:
  assumes "z2 \<noteq> 0"
  shows "\<angle> z1 (-z2) = \<downharpoonright>\<angle> z1 z2 + pi\<downharpoonleft>"
  unfolding ang_vec_def
  using arg_mult[of "-1" "z2"] assms
  using arg_complex_of_real_negative[of "-1"]
  using canon_ang_diff[of "arg (-1) + arg z2" "arg z1", symmetric]
  using canon_ang_sum[of "arg z2 - arg z1" "pi", symmetric]
  using canon_ang_id[of pi] canon_ang_arg[of z1]
  by (auto simp: algebra_simps)
  

lemma ang_vec_opposite_opposite:
  assumes "z1 \<noteq> 0" and "z2 \<noteq> 0"
  shows "\<angle> (-z1) (-z2) = \<angle> z1 z2"
proof-
  have "\<angle> (-z1) (-z2) = \<downharpoonright>\<downharpoonright>\<angle> z1 z2 + pi\<downharpoonleft> - \<downharpoonright>pi\<downharpoonleft>\<downharpoonleft>"
    using ang_vec_opposite1[OF assms(1)]
    using ang_vec_opposite2[OF assms(2)]
    using canon_ang_id[of pi, symmetric]
    by simp_all
  also have "... = \<downharpoonright>\<angle> z1 z2\<downharpoonleft>"
    by (subst canon_ang_diff[symmetric], simp)
  finally
  show ?thesis
    by (metis ang_vec_def canon_ang(1) canon_ang(2) canon_ang_id)
qed

lemma ang_vec_opposite_opposite':
  assumes "z1 \<noteq> z" and "z2 \<noteq> z"
  shows "\<angle> (z - z1) (z - z2) = \<angle> (z1 - z) (z2 - z)"
using ang_vec_opposite_opposite[of "z - z1" "z - z2"] assms
by (simp add: field_simps del: ang_vec_def)

text \<open>Cosine, scalar product and the law of cosines\<close>

lemma cos_cmod_scalprod:
  shows "cmod z1 * cmod z2 * (cos (\<angle> z1 z2)) = Re (scalprod z1 z2)"
proof (cases "z1 = 0 \<or> z2 = 0")
  case True
  thus ?thesis
    by auto
next
  case False
  thus ?thesis
    by (simp add: cos_diff cos_arg sin_arg field_simps)
qed

lemma cos0_scalprod0:
  assumes "z1 \<noteq> 0" and "z2 \<noteq> 0"
  shows "cos (\<angle> z1 z2) = 0 \<longleftrightarrow> scalprod z1 z2 = 0"
  using assms
  using cnj_mix_real[of z1 z2]
  using cos_cmod_scalprod[of z1 z2]
  by (auto simp add: complex_eq_if_Re_eq)

lemma ortho_scalprod0:
  assumes "z1 \<noteq> 0" and "z2 \<noteq> 0"
  shows "\<angle> z1 z2 = pi/2 \<or> \<angle> z1 z2 = -pi/2 \<longleftrightarrow> scalprod z1 z2 = 0"
  using cos0_scalprod0[OF assms]
  using ang_vec_bounded[of z1 z2]
  using cos_0_iff_canon[of "\<angle> z1 z2"]
  by (metis cos_minus cos_pi_half divide_minus_left)

lemma law_of_cosines:
  shows "(cdist B C)\<^sup>2 = (cdist A C)\<^sup>2 + (cdist A B)\<^sup>2 - 2*(cdist A C)*(cdist A B)*(cos (\<angle> (C-A) (B-A)))"
proof-
  let ?a = "C-B" and ?b = "C-A" and ?c = "B-A"
  have "?a = ?b - ?c"
    by simp
  hence "(cmod ?a)\<^sup>2 = (cmod (?b - ?c))\<^sup>2"
    by metis
  also have "... = Re (scalprod (?b-?c) (?b-?c))"
    by (simp add: cmod_square)
  also have "... = (cmod ?b)\<^sup>2 + (cmod ?c)\<^sup>2 - 2*Re (scalprod ?b ?c)"
    by (simp add: cmod_square field_simps)
  finally
  show ?thesis
    using cos_cmod_scalprod[of ?b ?c]
    by simp
qed

(* ---------------------------------------------------------------------------- *)
subsubsection \<open>Unoriented angle\<close>
(* ---------------------------------------------------------------------------- *)

text \<open>Convex unoriented angle between two vectors (it is always in the interval $[0, pi]$).\<close>
definition ang_vec_c ("\<angle>c") where
  [simp]:"\<angle>c z1 z2 \<equiv> abs (\<angle> z1 z2)"

lemma ang_vec_c_sym:
  shows "\<angle>c z1 z2 = \<angle>c z2 z1"
  unfolding ang_vec_c_def
  using ang_vec_sym_pi[of z1 z2] ang_vec_sym[of z1 z2]
  by (cases "\<angle> z1 z2 = pi") auto

lemma ang_vec_c_bounded: "0 \<le> \<angle>c z1 z2 \<and> \<angle>c z1 z2 \<le> pi"
  using canon_ang(1)[of "arg z2 - arg z1"] canon_ang(2)[of "arg z2 - arg z1"]
  by auto

text \<open>Cosine and scalar product\<close>

lemma cos_c_: "cos (\<angle>c z1 z2) = cos (\<angle> z1 z2)"
  unfolding ang_vec_c_def
  by (smt cos_minus)

lemma ortho_c_scalprod0:
  assumes "z1 \<noteq> 0" and "z2 \<noteq> 0"
  shows "\<angle>c z1 z2 = pi/2 \<longleftrightarrow> scalprod z1 z2 = 0"
proof-
  have "\<angle> z1 z2 = pi / 2 \<or> \<angle> z1 z2 = - pi / 2 \<longleftrightarrow> \<angle>c z1 z2 = pi/2"
    unfolding ang_vec_c_def
    using arctan 
    by force
  thus ?thesis
    using ortho_scalprod0[OF assms]
    by simp
qed

(* ---------------------------------------------------------------------------- *)
subsubsection \<open>Acute angle\<close>
(* ---------------------------------------------------------------------------- *)

text \<open>Acute or right angle (non-obtuse) between two vectors (it is always in the interval $[0, \frac{\pi}{2}$]).
We will use this to measure angle between two circles, since it can always be acute (or right).\<close>

definition acute_ang where
  [simp]: "acute_ang \<alpha> = (if \<alpha> > pi / 2 then pi - \<alpha> else \<alpha>)"

definition ang_vec_a ("\<angle>a") where
  [simp]: "\<angle>a z1 z2 \<equiv> acute_ang (\<angle>c z1 z2)"

lemma ang_vec_a_sym:
  "\<angle>a z1 z2 = \<angle>a z2 z1"
  unfolding ang_vec_a_def
  using ang_vec_c_sym
  by auto

lemma ang_vec_a_opposite2:
  "\<angle>a z1 z2 = \<angle>a z1 (-z2)"
proof(cases "z2  = 0")
  case True
  thus ?thesis
    by (metis minus_zero)
next
  case False
  thus ?thesis
  proof(cases "\<angle> z1 z2 < -pi / 2")
    case True
    hence "\<angle> z1 z2 < 0"
      using pi_not_less_zero
      by linarith
    have "\<angle>a z1 z2 = pi + \<angle> z1 z2"
      using True \<open>\<angle> z1 z2 < 0\<close>
      unfolding ang_vec_a_def ang_vec_c_def ang_vec_a_def abs_real_def
      by auto
    moreover
    have "\<angle>a z1 (-z2) = pi + \<angle> z1 z2"
      unfolding ang_vec_a_def ang_vec_c_def abs_real_def
      using canon_ang(1)[of "arg z2 - arg z1"] canon_ang(2)[of "arg z2 - arg z1"]
      using ang_vec_plus_pi2[of z1 z2] True \<open>\<angle> z1 z2 < 0\<close> \<open>z2 \<noteq> 0\<close>
      using ang_vec_opposite2[of z2 z1]
      by auto
    ultimately
    show ?thesis
      by auto
  next
    case False
    show ?thesis
    proof (cases "\<angle> z1 z2 \<le> 0")
      case True
      have "\<angle>a z1 z2 = - \<angle> z1 z2"
        using \<open>\<not> \<angle> z1 z2 < - pi / 2\<close> True
        unfolding ang_vec_a_def ang_vec_c_def ang_vec_a_def abs_real_def
        by auto
      moreover
      have "\<angle>a z1 (-z2) = - \<angle> z1 z2"
        using \<open>\<not> \<angle> z1 z2 < - pi / 2\<close> True
        unfolding ang_vec_a_def ang_vec_c_def abs_real_def
        using ang_vec_plus_pi2[of z1 z2]
        using canon_ang(1)[of "arg z2 - arg z1"] canon_ang(2)[of "arg z2 - arg z1"]
        using \<open>z2 \<noteq> 0\<close> ang_vec_opposite2[of z2 z1]
        by auto
      ultimately
      show ?thesis
        by simp
    next
      case False
      show ?thesis
      proof (cases "\<angle> z1 z2 < pi / 2")
        case True
        have "\<angle>a z1 z2 = \<angle> z1 z2"
          using \<open>\<not> \<angle> z1 z2 \<le> 0\<close> True
          unfolding ang_vec_a_def ang_vec_c_def ang_vec_a_def abs_real_def
          by auto
        moreover
        have "\<angle>a z1 (-z2) = \<angle> z1 z2"
          using \<open>\<not> \<angle> z1 z2 \<le> 0\<close> True
          unfolding ang_vec_a_def ang_vec_c_def abs_real_def
          using ang_vec_plus_pi1[of z1 z2]
          using canon_ang(1)[of "arg z2 - arg z1"] canon_ang(2)[of "arg z2 - arg z1"]
          using \<open>z2 \<noteq> 0\<close> ang_vec_opposite2[of z2 z1]
          by auto
        ultimately
        show ?thesis
          by simp
      next
        case False
        have "\<angle> z1 z2 > 0"
          using False
          by (metis less_linear less_trans pi_half_gt_zero)
        have "\<angle>a z1 z2 = pi - \<angle> z1 z2"
          using False \<open>\<angle> z1 z2 > 0\<close>
          unfolding ang_vec_a_def ang_vec_c_def ang_vec_a_def abs_real_def
          by auto
        moreover
        have "\<angle>a z1 (-z2) = pi - \<angle> z1 z2"
          unfolding ang_vec_a_def ang_vec_c_def abs_real_def
          using False \<open>\<angle> z1 z2 > 0\<close>
          using ang_vec_plus_pi1[of z1 z2]
          using canon_ang(1)[of "arg z2 - arg z1"] canon_ang(2)[of "arg z2 - arg z1"]
          using \<open>z2 \<noteq> 0\<close> ang_vec_opposite2[of z2 z1]
          by auto
        ultimately
        show ?thesis
          by auto
      qed
    qed
  qed
qed

lemma ang_vec_a_opposite1:
  shows "\<angle>a z1 z2 = \<angle>a (-z1) z2"
  using ang_vec_a_sym[of "-z1" z2] ang_vec_a_opposite2[of z2 z1] ang_vec_a_sym[of z2 z1]
  by auto

lemma ang_vec_a_scale1:
  assumes "k \<noteq> 0"
  shows "\<angle>a (cor k * z1) z2 = \<angle>a z1 z2"
proof (cases "k > 0")
  case True
  thus ?thesis
    unfolding ang_vec_a_def ang_vec_c_def ang_vec_def
    using arg_mult_real_positive[of k z1]
    by auto
next
  case False
  hence "k < 0"
    using assms
    by auto
  thus ?thesis
    using arg_mult_real_negative[of k z1]
    using ang_vec_a_opposite1[of z1 z2]
    unfolding ang_vec_a_def ang_vec_c_def ang_vec_def
    by simp
qed

lemma ang_vec_a_scale2:
  assumes "k \<noteq> 0"
  shows "\<angle>a z1 (cor k * z2) = \<angle>a z1 z2"
  using ang_vec_a_sym[of z1 "complex_of_real k * z2"]
  using ang_vec_a_scale1[OF assms, of z2 z1]
  using ang_vec_a_sym[of z1 z2]
  by auto

lemma ang_vec_a_scale:
  assumes "k1 \<noteq> 0" and "k2 \<noteq> 0"
  shows "\<angle>a (cor k1 * z1) (cor k2 * z2) = \<angle>a z1 z2"
  using ang_vec_a_scale1[OF assms(1)] ang_vec_a_scale2[OF assms(2)]
  by auto

lemma ang_a_cnj_cnj:
  shows "\<angle>a z1 z2 = \<angle>a (cnj z1) (cnj z2)"
unfolding ang_vec_a_def ang_vec_c_def ang_vec_def
proof(cases "arg z1 \<noteq> pi \<and> arg z2 \<noteq> pi")
  case True
  thus "acute_ang \<bar>\<downharpoonright>arg z2 - arg z1\<downharpoonleft>\<bar> = acute_ang \<bar>\<downharpoonright>arg (cnj z2) - arg (cnj z1)\<downharpoonleft>\<bar>"
    using arg_cnj_not_pi[of z1] arg_cnj_not_pi[of z2]
    apply (auto simp del:acute_ang_def)
    proof(cases "\<downharpoonright>arg z2 - arg z1\<downharpoonleft> = pi")
      case True
      thus "acute_ang \<bar>\<downharpoonright>arg z2 - arg z1\<downharpoonleft>\<bar> = acute_ang \<bar>\<downharpoonright>arg z1 - arg z2\<downharpoonleft>\<bar>"
        using  canon_ang_uminus_pi[of "arg z2 - arg z1"]
        by (auto simp add:field_simps)
    next
      case False
      thus "acute_ang \<bar>\<downharpoonright>arg z2 - arg z1\<downharpoonleft>\<bar> = acute_ang \<bar>\<downharpoonright>arg z1 - arg z2\<downharpoonleft>\<bar>"
        using  canon_ang_uminus[of "arg z2 - arg z1"]
        by (auto simp add:field_simps)
    qed
  next
    case False
    thus "acute_ang \<bar>\<downharpoonright>arg z2 - arg z1\<downharpoonleft>\<bar> = acute_ang \<bar>\<downharpoonright>arg (cnj z2) - arg (cnj z1)\<downharpoonleft>\<bar>"
    proof(cases "arg z1 = pi")
      case False
      hence "arg z2 = pi"
        using \<open> \<not> (arg z1 \<noteq> pi \<and> arg z2 \<noteq> pi)\<close>
        by auto
      thus ?thesis
        using False
        using arg_cnj_not_pi[of z1] arg_cnj_pi[of z2]
        apply (auto simp del:acute_ang_def)
      proof(cases "arg z1 > 0")
          case True
          hence "-arg z1 \<le> 0"
            by auto
          thus "acute_ang \<bar>\<downharpoonright>pi - arg z1\<downharpoonleft>\<bar> = acute_ang \<bar>\<downharpoonright>pi + arg z1\<downharpoonleft>\<bar>"
            using True canon_ang_plus_pi1[of "arg z1"]
            using arg_bounded[of z1] canon_ang_plus_pi2[of "-arg z1"]
            by (auto simp add:field_simps)
        next
          case False
          hence "-arg z1 \<ge> 0"
             by simp
          thus "acute_ang \<bar>\<downharpoonright>pi - arg z1\<downharpoonleft>\<bar> = acute_ang \<bar>\<downharpoonright>pi + arg z1\<downharpoonleft>\<bar>"
          proof(cases "arg z1 = 0")
            case True
            thus ?thesis
              by (auto simp del:acute_ang_def)
          next
            case False
            hence "-arg z1 > 0"
              using \<open>-arg z1 \<ge> 0\<close>
              by auto
            thus ?thesis
            using False canon_ang_plus_pi1[of "-arg z1"]
            using arg_bounded[of z1] canon_ang_plus_pi2[of "arg z1"]
            by (auto simp add:field_simps)
        qed
      qed
    next
      case True
      thus ?thesis
        using arg_cnj_pi[of z1]
        apply (auto simp del:acute_ang_def)
      proof(cases "arg z2 = pi")
        case True
        thus "acute_ang \<bar>\<downharpoonright>arg z2 - pi\<downharpoonleft>\<bar> = acute_ang \<bar>\<downharpoonright>arg (cnj z2) - pi\<downharpoonleft>\<bar>"
          using arg_cnj_pi[of z2]
          by auto
      next
        case False
        thus "acute_ang \<bar>\<downharpoonright>arg z2 - pi\<downharpoonleft>\<bar> = acute_ang \<bar>\<downharpoonright>arg (cnj z2) - pi\<downharpoonleft>\<bar>"
          using arg_cnj_not_pi[of z2]
          apply (auto simp del:acute_ang_def)
        proof(cases "arg z2 > 0")
          case True
          hence "-arg z2 \<le> 0"
            by auto
          thus "acute_ang \<bar>\<downharpoonright>arg z2 - pi\<downharpoonleft>\<bar> = acute_ang \<bar>\<downharpoonright>- arg z2 - pi\<downharpoonleft>\<bar>"
            using True canon_ang_minus_pi1[of "arg z2"]
            using arg_bounded[of z2] canon_ang_minus_pi2[of "-arg z2"]
            by (auto simp add: field_simps)
        next
          case False
          hence "-arg z2 \<ge> 0"
             by simp
          thus "acute_ang \<bar>\<downharpoonright>arg z2 - pi\<downharpoonleft>\<bar> = acute_ang \<bar>\<downharpoonright>- arg z2 - pi\<downharpoonleft>\<bar>"
          proof(cases "arg z2 = 0")
            case True
            thus ?thesis
              by (auto simp del:acute_ang_def)
          next
            case False
            hence "-arg z2 > 0"
              using \<open>-arg z2 \<ge> 0\<close>
              by auto
            thus ?thesis
            using False canon_ang_minus_pi1[of "-arg z2"]
            using arg_bounded[of z2] canon_ang_minus_pi2[of "arg z2"]
            by (auto simp add:field_simps)
        qed
      qed
    qed
  qed
qed

text \<open>Cosine and scalar product\<close>

lemma ortho_a_scalprod0:
  assumes "z1 \<noteq> 0" and "z2 \<noteq> 0"
  shows "\<angle>a z1 z2 = pi/2 \<longleftrightarrow> scalprod z1 z2 = 0"
  unfolding ang_vec_a_def
  using assms ortho_c_scalprod0[of z1 z2]
  by auto

declare ang_vec_c_def[simp del]

lemma cos_a_c: "cos (\<angle>a z1 z2) = abs (cos (\<angle>c z1 z2))"
proof-
  have "0 \<le> \<angle>c z1 z2" "\<angle>c z1 z2 \<le> pi"
    using ang_vec_c_bounded[of z1 z2]
    by auto
  show ?thesis
  proof (cases "\<angle>c z1 z2 = pi/2")
    case True
    thus ?thesis
      unfolding ang_vec_a_def acute_ang_def
      by (smt cos_pi_half pi_def pi_half)
  next
    case False
    show ?thesis
    proof (cases "\<angle>c z1 z2 < pi / 2")
      case True
      thus ?thesis
        using `0 \<le> \<angle>c z1 z2`
        using cos_gt_zero_pi[of "\<angle>c z1 z2"]
        unfolding ang_vec_a_def
        by simp
    next
      case False
      hence "\<angle>c z1 z2 > pi/2"
        using `\<angle>c z1 z2 \<noteq> pi/2`
        by simp
      hence "cos (\<angle>c z1 z2) < 0"
        using `\<angle>c z1 z2 \<le> pi`
        using cos_lt_zero_on_pi2_pi[of "\<angle>c z1 z2"] 
        by simp
      thus ?thesis
        using `\<angle>c z1 z2 > pi/2`
        unfolding ang_vec_a_def
        by simp
    qed
  qed
qed

end
