(* -------------------------------------------------------------------------- *)
subsection \<open>Canonical angle\<close> 
(* -------------------------------------------------------------------------- *)

text \<open>Canonize any angle to $(-\pi, \pi]$ (taking account of $2\pi$ periodicity of @{term sin} and
@{term cos}). With this function, for example, multiplicative properties of @{term arg} for complex
numbers can easily be expressed and proved.\<close>

theory Canonical_Angle
imports More_Transcendental
begin


abbreviation canon_ang_P where
 "canon_ang_P \<alpha> \<alpha>' \<equiv> (-pi < \<alpha>' \<and> \<alpha>' \<le> pi) \<and> (\<exists> k::int. \<alpha> - \<alpha>' = 2*k*pi)"

definition canon_ang :: "real \<Rightarrow> real" ("\<downharpoonright>_\<downharpoonleft>") where
  "\<downharpoonright>\<alpha>\<downharpoonleft> = (THE \<alpha>'. canon_ang_P \<alpha> \<alpha>')"

text \<open>There is a canonical angle for every angle.\<close>
lemma canon_ang_ex:
  shows "\<exists> \<alpha>'. canon_ang_P \<alpha> \<alpha>'"
proof-
  have ***: "\<forall> \<alpha>::real. \<exists> \<alpha>'. 0 < \<alpha>' \<and> \<alpha>' \<le> 1 \<and> (\<exists> k::int. \<alpha>' = \<alpha> - k)"
  proof
    fix \<alpha>::real
    show "\<exists>\<alpha>'>0. \<alpha>' \<le> 1 \<and> (\<exists>k::int. \<alpha>' = \<alpha> - k)"
    proof (cases "\<alpha> = floor \<alpha>")
      case True
      thus ?thesis
        by (rule_tac x="\<alpha> - floor \<alpha> + 1" in exI, auto) (rule_tac x="floor \<alpha> - 1" in exI, auto)
    next
      case False
      thus ?thesis
        using real_of_int_floor_ge_diff_one[of "\<alpha>"]
        using of_int_floor_le[of "\<alpha>"]
        by (rule_tac x="\<alpha> - floor \<alpha>" in exI) smt
    qed
  qed

  have **: "\<forall> \<alpha>::real. \<exists> \<alpha>'. 0 < \<alpha>' \<and> \<alpha>' \<le> 2 \<and> (\<exists> k::int. \<alpha> - \<alpha>' = 2*k - 1)"
  proof
    fix \<alpha>::real
    from ***[rule_format, of "(\<alpha> + 1) /2"]
    obtain \<alpha>' and k::int where "0 < \<alpha>'" "\<alpha>' \<le> 1" "\<alpha>' = (\<alpha> + 1)/2 - k"
      by force
    hence "0 < \<alpha>'" "\<alpha>' \<le> 1" "\<alpha>' = \<alpha>/2 - k + 1/2"
      by auto
    thus "\<exists>\<alpha>'>0. \<alpha>' \<le> 2 \<and> (\<exists>k::int. \<alpha> - \<alpha>' = real_of_int (2 * k - 1))"
      by (rule_tac x="2*\<alpha>'" in exI) auto
  qed
  have *: "\<forall> \<alpha>::real. \<exists> \<alpha>'. -1 < \<alpha>' \<and> \<alpha>' \<le> 1 \<and> (\<exists> k::int. \<alpha> - \<alpha>' = 2*k)"
  proof
    fix \<alpha>::real
    from ** obtain \<alpha>' and k :: int where
      "0 < \<alpha>' \<and> \<alpha>' \<le> 2 \<and> \<alpha> - \<alpha>' = 2*k - 1"
      by force
    thus "\<exists>\<alpha>'>-1. \<alpha>' \<le> 1 \<and> (\<exists>k. \<alpha> - \<alpha>' = real_of_int (2 * (k::int)))"
      by (rule_tac x="\<alpha>' - 1" in exI) (auto simp add: field_simps)
  qed
  obtain \<alpha>' k where 1: "\<alpha>' >- 1 \<and> \<alpha>' \<le> 1" and 2: "\<alpha> / pi - \<alpha>' = real_of_int (2 * k)"
    using *[rule_format, of "\<alpha> / pi"]
    by auto
  have "\<alpha>'*pi > -pi \<and> \<alpha>'*pi \<le> pi" 
    using 1
    by (smt mult.commute mult_le_cancel_left1 mult_minus_right pi_gt_zero)
  moreover
  have "\<alpha> - \<alpha>'*pi = 2 * real_of_int k * pi"
    using 2
    by (auto simp add: field_simps)
  ultimately
  show ?thesis
    by auto
qed

text \<open>Canonical angle of any angle is unique.\<close>
lemma canon_ang_unique:
  assumes "canon_ang_P \<alpha> \<alpha>\<^sub>1" and "canon_ang_P \<alpha> \<alpha>\<^sub>2"
  shows "\<alpha>\<^sub>1 = \<alpha>\<^sub>2"
proof-
  obtain k1::int where "\<alpha> - \<alpha>\<^sub>1 = 2*k1*pi"
    using assms(1)
    by auto
  obtain k2::int where "\<alpha> - \<alpha>\<^sub>2 = 2*k2*pi"
    using assms(2)
    by auto
  hence *: "-\<alpha>\<^sub>1 + \<alpha>\<^sub>2 = 2*(k1 - k2)*pi"
    using \<open>\<alpha> - \<alpha>\<^sub>1 = 2*k1*pi\<close>
    by (simp add:field_simps)
  moreover
  have "-\<alpha>\<^sub>1 + \<alpha>\<^sub>2 < 2 * pi" "-\<alpha>\<^sub>1 + \<alpha>\<^sub>2 > -2*pi"
    using assms
    by auto
  ultimately
  have "-\<alpha>\<^sub>1 + \<alpha>\<^sub>2 = 0"
    using mult_less_cancel_right[of "-2" pi "real_of_int(2 * (k1 - k2))"]
    by auto
  thus ?thesis
    by auto
qed

text \<open>Canonical angle is always in $(-\pi, \pi]$ and differs from the starting angle by $2k\pi$.\<close>
lemma canon_ang:
  shows "-pi < \<downharpoonright>\<alpha>\<downharpoonleft>" and "\<downharpoonright>\<alpha>\<downharpoonleft> \<le> pi" and "\<exists> k::int. \<alpha> - \<downharpoonright>\<alpha>\<downharpoonleft> = 2*k*pi"
proof-
  obtain \<alpha>' where "canon_ang_P \<alpha> \<alpha>'"
    using canon_ang_ex[of \<alpha>]
    by auto
  have "canon_ang_P \<alpha> \<downharpoonright>\<alpha>\<downharpoonleft>"
    unfolding canon_ang_def
  proof (rule theI[where a="\<alpha>'"])
    show "canon_ang_P \<alpha> \<alpha>'"
      by fact
  next
    fix \<alpha>''
    assume "canon_ang_P \<alpha> \<alpha>''"
    thus "\<alpha>'' = \<alpha>'"
      using \<open>canon_ang_P \<alpha> \<alpha>'\<close>
      using canon_ang_unique[of \<alpha>' \<alpha> \<alpha>'']
      by simp
  qed
  thus "-pi < \<downharpoonright>\<alpha>\<downharpoonleft>" "\<downharpoonright>\<alpha>\<downharpoonleft> \<le> pi" "\<exists> k::int. \<alpha> - \<downharpoonright>\<alpha>\<downharpoonleft> = 2*k*pi"
    by auto
qed

text \<open>Angles in $(-\pi, \pi]$ are already canonical.\<close>
lemma canon_ang_id:
  assumes  "-pi < \<alpha> \<and> \<alpha> \<le> pi"
  shows "\<downharpoonright>\<alpha>\<downharpoonleft> = \<alpha>"
  using assms
  using canon_ang_unique[of "canon_ang \<alpha>" \<alpha> \<alpha>] canon_ang[of \<alpha>]
  by auto

text \<open>Angles that differ by $2k\pi$ have equal canonical angles.\<close>
lemma canon_ang_eq:
  assumes "\<exists> k::int. \<alpha>\<^sub>1 - \<alpha>\<^sub>2 = 2*k*pi"
  shows "\<downharpoonright>\<alpha>\<^sub>1\<downharpoonleft> = \<downharpoonright>\<alpha>\<^sub>2\<downharpoonleft>"
proof-
  obtain k'::int where *: "- pi < \<downharpoonright>\<alpha>\<^sub>1\<downharpoonleft>" "\<downharpoonright>\<alpha>\<^sub>1\<downharpoonleft> \<le> pi" "\<alpha>\<^sub>1 - \<downharpoonright>\<alpha>\<^sub>1\<downharpoonleft> = 2 * k' * pi"
    using canon_ang[of \<alpha>\<^sub>1]
    by auto

  obtain k''::int where **: "- pi < \<downharpoonright>\<alpha>\<^sub>2\<downharpoonleft>" "\<downharpoonright>\<alpha>\<^sub>2\<downharpoonleft> \<le> pi" "\<alpha>\<^sub>2 - \<downharpoonright>\<alpha>\<^sub>2\<downharpoonleft> = 2 * k'' * pi"
    using canon_ang[of \<alpha>\<^sub>2]
    by auto

  obtain k::int where ***: "\<alpha>\<^sub>1 - \<alpha>\<^sub>2 = 2*k*pi"
    using assms
    by auto

  have "\<exists>m::int. \<alpha>\<^sub>1 - \<downharpoonright>\<alpha>\<^sub>2\<downharpoonleft> = 2 * m * pi"
    using **(3) ***
    by (rule_tac x="k+k''" in exI) (auto simp add: field_simps)

  thus ?thesis
    using canon_ang_unique[of "\<downharpoonright>\<alpha>\<^sub>1\<downharpoonleft>" \<alpha>\<^sub>1 "\<downharpoonright>\<alpha>\<^sub>2\<downharpoonleft>"] * **
    by auto
qed

text \<open>Introduction and elimination rules\<close>
lemma canon_ang_eqI:
  assumes "\<exists>k::int. \<alpha>' - \<alpha> = 2 * k * pi" and "- pi < \<alpha>' \<and> \<alpha>' \<le> pi"
  shows "\<downharpoonright>\<alpha>\<downharpoonleft> = \<alpha>'"
  using assms
  using canon_ang_eq[of \<alpha>' \<alpha>]
  using canon_ang_id[of \<alpha>']
  by auto

lemma canon_ang_eqE:
  assumes "\<downharpoonright>\<alpha>\<^sub>1\<downharpoonleft> = \<downharpoonright>\<alpha>\<^sub>2\<downharpoonleft>"
  shows "\<exists> (k::int). \<alpha>\<^sub>1 - \<alpha>\<^sub>2 = 2 *k * pi"
proof-
  obtain k1 k2 :: int where
    "\<alpha>\<^sub>1 - \<downharpoonright>\<alpha>\<^sub>1\<downharpoonleft> = 2 * k1 * pi"
    "\<alpha>\<^sub>2 - \<downharpoonright>\<alpha>\<^sub>2\<downharpoonleft> = 2 * k2 * pi"
    using canon_ang[of \<alpha>\<^sub>1] canon_ang[of \<alpha>\<^sub>2]
    by auto
  thus ?thesis
    using assms
    by (rule_tac x="k1 - k2" in exI) (auto simp add: field_simps)
qed

text \<open>Canonical angle of opposite angle\<close>

lemma canon_ang_uminus:
  assumes "\<downharpoonright>\<alpha>\<downharpoonleft> \<noteq> pi"
  shows "\<downharpoonright>-\<alpha>\<downharpoonleft> = -\<downharpoonright>\<alpha>\<downharpoonleft>"
proof (rule canon_ang_eqI)
  show "\<exists>x::int. - \<downharpoonright>\<alpha>\<downharpoonleft> - - \<alpha> = 2 * x * pi"
    using canon_ang(3)[of \<alpha>]
    by (metis minus_diff_eq minus_diff_minus)
next
  show "- pi < - \<downharpoonright>\<alpha>\<downharpoonleft> \<and> - \<downharpoonright>\<alpha>\<downharpoonleft> \<le> pi"
    using canon_ang(1)[of \<alpha>] canon_ang(2)[of \<alpha>] assms
    by auto
qed

lemma canon_ang_uminus_pi:
  assumes "\<downharpoonright>\<alpha>\<downharpoonleft> = pi"
  shows "\<downharpoonright>-\<alpha>\<downharpoonleft> = \<downharpoonright>\<alpha>\<downharpoonleft>"
proof (rule canon_ang_eqI)
  obtain k::int where "\<alpha> - \<downharpoonright>\<alpha>\<downharpoonleft> = 2 * k * pi"
    using canon_ang(3)[of \<alpha>]
    by auto
  thus "\<exists>x::int. \<downharpoonright>\<alpha>\<downharpoonleft> - - \<alpha> = 2 * x * pi"
    using assms
    by (rule_tac x="k+(1::int)" in exI) (auto simp add: field_simps)
next
  show "- pi < \<downharpoonright>\<alpha>\<downharpoonleft> \<and> \<downharpoonright>\<alpha>\<downharpoonleft> \<le> pi"
    using assms
    by auto
qed

text \<open>Canonical angle of difference of two angles\<close>
lemma canon_ang_diff:
  shows "\<downharpoonright>\<alpha> - \<beta>\<downharpoonleft> = \<downharpoonright>\<downharpoonright>\<alpha>\<downharpoonleft> - \<downharpoonright>\<beta>\<downharpoonleft>\<downharpoonleft>"
proof (rule canon_ang_eq)
  show "\<exists>x::int. \<alpha> - \<beta> - (\<downharpoonright>\<alpha>\<downharpoonleft> - \<downharpoonright>\<beta>\<downharpoonleft>) = 2 * x * pi"
  proof-
    obtain k1::int where "\<alpha> - \<downharpoonright>\<alpha>\<downharpoonleft> = 2*k1*pi"
      using canon_ang(3)
      by auto
    moreover
    obtain k2::int where "\<beta> - \<downharpoonright>\<beta>\<downharpoonleft> = 2*k2*pi"
      using canon_ang(3)
      by auto
    ultimately
    show ?thesis
      by (rule_tac x="k1 - k2" in exI) (auto simp add: field_simps)
  qed
qed

text \<open>Canonical angle of sum of two angles\<close>
lemma canon_ang_sum:
  shows "\<downharpoonright>\<alpha> + \<beta>\<downharpoonleft> = \<downharpoonright>\<downharpoonright>\<alpha>\<downharpoonleft> + \<downharpoonright>\<beta>\<downharpoonleft>\<downharpoonleft>"
proof (rule canon_ang_eq)
  show "\<exists>x::int. \<alpha> + \<beta> - (\<downharpoonright>\<alpha>\<downharpoonleft> + \<downharpoonright>\<beta>\<downharpoonleft>) = 2 * x * pi"
  proof-
    obtain k1::int where "\<alpha> - \<downharpoonright>\<alpha>\<downharpoonleft> = 2*k1*pi"
      using canon_ang(3)
      by auto
    moreover
    obtain k2::int where "\<beta> - \<downharpoonright>\<beta>\<downharpoonleft> = 2*k2*pi"
      using canon_ang(3)
      by auto
    ultimately
    show ?thesis
      by (rule_tac x="k1 + k2" in exI) (auto simp add: field_simps)
  qed
qed

text \<open>Canonical angle of angle from $(0, 2\pi]$ shifted by $\pi$\<close>

lemma canon_ang_plus_pi1:
  assumes "0 < \<alpha>" and "\<alpha> \<le> 2*pi"
  shows "\<downharpoonright>\<alpha> + pi\<downharpoonleft> = \<alpha> - pi"
proof (rule canon_ang_eqI)
  show "\<exists> x::int. \<alpha> - pi - (\<alpha> + pi) = 2 * x * pi"
    by (rule_tac x="-1" in exI) auto
next
  show "- pi < \<alpha> - pi \<and> \<alpha> - pi \<le> pi"
    using assms
    by auto
qed

lemma canon_ang_minus_pi1:
  assumes "0 < \<alpha>" and "\<alpha> \<le> 2*pi"
  shows "\<downharpoonright>\<alpha> - pi\<downharpoonleft> = \<alpha> - pi"
proof (rule canon_ang_id)
  show "- pi < \<alpha> - pi \<and> \<alpha> - pi \<le> pi"
    using assms
    by auto
qed

text \<open>Canonical angle of angles from $(-2\pi, 0]$ shifted by $\pi$\<close>

lemma canon_ang_plus_pi2:
  assumes "-2*pi < \<alpha>" and "\<alpha> \<le> 0"
  shows "\<downharpoonright>\<alpha> + pi\<downharpoonleft> = \<alpha> + pi"
proof (rule canon_ang_id)
  show "- pi < \<alpha> + pi \<and> \<alpha> + pi \<le> pi"
    using assms
    by auto
qed

lemma canon_ang_minus_pi2:
  assumes "-2*pi < \<alpha>" and "\<alpha> \<le> 0"
  shows "\<downharpoonright>\<alpha> - pi\<downharpoonleft> = \<alpha> + pi"
proof (rule canon_ang_eqI)
  show "\<exists> x::int. \<alpha> + pi - (\<alpha> - pi) = 2 * x * pi"
    by (rule_tac x="1" in exI) auto
next
  show "- pi < \<alpha> + pi \<and> \<alpha> + pi \<le> pi"
    using assms
    by auto
qed

text \<open>Canonical angle of angle in $(\pi, 3\pi]$.\<close>
lemma canon_ang_pi_3pi: 
  assumes "pi < \<alpha>" and "\<alpha> \<le> 3 * pi"
  shows "\<downharpoonright>\<alpha>\<downharpoonleft> = \<alpha> - 2*pi"
proof-
  have "\<exists>x. - pi = pi * real_of_int x"
    by (rule_tac x="-1" in exI, simp)
  thus ?thesis
    using assms canon_ang_eqI[of "\<alpha> - 2*pi" "\<alpha>"]
    by auto
qed

text \<open>Canonical angle of angle in $(-3\pi, -\pi]$.\<close>
lemma canon_ang_minus_3pi_minus_pi: 
  assumes "-3*pi < \<alpha>" and "\<alpha> \<le> -pi"
  shows "\<downharpoonright>\<alpha>\<downharpoonleft> = \<alpha> + 2*pi"
proof-
  have "\<exists>x. pi = pi * real_of_int x"
    by (rule_tac x="1" in exI, simp)
  thus ?thesis
    using assms canon_ang_eqI[of "\<alpha> + 2*pi" "\<alpha>"]
    by auto
qed

text \<open>Canonical angles for some special angles\<close>

lemma zero_canonical [simp]:
  shows "\<downharpoonright>0\<downharpoonleft> = 0"
  using canon_ang_eqI[of 0 0]
  by simp

lemma pi_canonical [simp]:
  shows "\<downharpoonright>pi\<downharpoonleft> = pi"
  by (simp add: canon_ang_id)

lemma two_pi_canonical [simp]:
  shows "\<downharpoonright>2 * pi\<downharpoonleft> = 0"
  using canon_ang_plus_pi1[of "pi"]
  by simp

text \<open>Canonization preserves sine and cosine\<close>
lemma canon_ang_sin [simp]:
  shows "sin \<downharpoonright>\<alpha>\<downharpoonleft> = sin \<alpha>"
proof-
  obtain x::int where "\<alpha> = \<downharpoonright>\<alpha>\<downharpoonleft> + pi * (x * 2)"
    using canon_ang(3)[of \<alpha>]
    by (auto simp add: field_simps)
  thus ?thesis
    using sin_periodic_int[of "\<downharpoonright>\<alpha>\<downharpoonleft>" x]
    by (simp add: field_simps)
qed

lemma canon_ang_cos [simp]:
  shows "cos \<downharpoonright>\<alpha>\<downharpoonleft> = cos \<alpha>"
proof-
  obtain x::int where "\<alpha> = \<downharpoonright>\<alpha>\<downharpoonleft> + pi * (x * 2)"
    using canon_ang(3)[of \<alpha>]
    by (auto simp add: field_simps)
  thus ?thesis
    using cos_periodic_int[of "\<downharpoonright>\<alpha>\<downharpoonleft>" x]
    by (simp add: field_simps)
qed

end
