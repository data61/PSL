(* ---------------------------------------------------------------------------- *)
subsection \<open>Systems of linear equations\<close>
(* ---------------------------------------------------------------------------- *)
(* TODO: merge with matrices *)

text \<open>In this section some simple properties of systems of linear equations with two or three unknowns are derived.
Existence and uniqueness of solutions of regular and singular homogenous and non-homogenous systems is characterized.\<close>

theory Linear_Systems
imports Main
begin

text \<open>Determinant of 2x2 matrix\<close>
definition det2 :: "('a::field) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  [simp]: "det2 a11 a12 a21 a22 \<equiv> a11*a22 - a12*a21"

text \<open>Regular homogenous system has only trivial solution\<close>
lemma regular_homogenous_system:
  fixes a11 a12 a21 a22 x1 x2 :: "'a::field"
  assumes "det2 a11 a12 a21 a22 \<noteq> 0"
  assumes "a11*x1 + a12*x2 = 0" and
          "a21*x1 + a22*x2 = 0"
  shows "x1 = 0 \<and> x2 = 0"
proof (cases "a11 = 0")
  case True
  with assms(1) have "a12 \<noteq> 0" "a21 \<noteq> 0"
    by auto
  thus ?thesis
    using \<open>a11 = 0\<close> assms(2) assms(3)
    by auto
next
  case False
  hence "x1 = - a12*x2 / a11"
    using assms(2)
    by (metis eq_neg_iff_add_eq_0 mult_minus_left nonzero_mult_div_cancel_left)
  hence "a21 * (- a12 * x2 / a11) + a22 * x2 = 0"
    using assms(3)
    by simp
  hence "a21 * (- a12 * x2) + a22 * x2 * a11 = 0"
    using  \<open>a11 \<noteq> 0\<close>
    by auto
  hence "(a11*a22 - a12*a21)*x2 = 0"
    by (simp add: field_simps)
  thus ?thesis
    using assms(1) assms(2) \<open>a11 \<noteq> 0\<close>
    by auto
qed

text \<open>Regular system has a unique solution\<close>
lemma regular_system:
  fixes a11 a12 a21 a22 b1 b2 :: "'a::field"
  assumes "det2 a11 a12 a21 a22 \<noteq> 0"
  shows "\<exists>! x. a11*(fst x) + a12*(snd x) = b1 \<and>
               a21*(fst x) + a22*(snd x) = b2"
proof
  let ?d = "a11*a22 - a12*a21" and ?d1 = "b1*a22 - b2*a12" and ?d2 = "b2*a11 - b1*a21"
  let ?x = "(?d1 / ?d, ?d2 / ?d)"
  have "a11 * ?d1 + a12 * ?d2 = b1*?d" "a21 * ?d1 + a22 * ?d2 = b2*?d"
    by (auto simp add: field_simps)
  thus "a11 * fst ?x + a12 * snd ?x = b1 \<and> a21 * fst ?x + a22 * snd ?x = b2"
    using assms
    by (metis (hide_lams, no_types) det2_def add_divide_distrib eq_divide_imp fst_eqD snd_eqD times_divide_eq_right)

  fix x'
  assume "a11 * fst x' + a12 * snd x' = b1 \<and> a21 * fst x' + a22 * snd x' = b2"
  with \<open>a11 * fst ?x + a12 * snd ?x = b1 \<and> a21 * fst ?x + a22 * snd ?x = b2\<close>
  have "a11 * (fst x' - fst ?x) + a12 * (snd x' - snd ?x) = 0 \<and> a21 * (fst x' - fst ?x) + a22 * (snd x' - snd ?x) = 0"
    by (auto simp add: field_simps)
  thus "x' = ?x"
    using regular_homogenous_system[OF assms, of "fst x' - fst ?x" "snd x' - snd ?x"]
    by (cases x') auto
qed

text \<open>Singular system does not have a unique solution\<close>
lemma singular_system:
  fixes a11 a12 a21 a22 ::"'a::field"
  assumes "det2 a11 a12 a21 a22 = 0" and "a11 \<noteq> 0 \<or> a12 \<noteq> 0"
  assumes x0: "a11*fst x0 + a12*snd x0 = b1"
              "a21*fst x0 + a22*snd x0 = b2"
  assumes x: "a11*fst x + a12*snd x = b1"
  shows "a21*fst x + a22*snd x = b2"
proof (cases "a11 = 0")
  case True
  with assms have "a21 = 0" "a12 \<noteq> 0"
    by auto
  let ?k = "a22 / a12"
  have "b2 = ?k * b1"
    using x0 \<open>a11 = 0\<close> \<open>a21 = 0\<close> \<open>a12 \<noteq> 0\<close>
    by auto
  thus ?thesis
    using \<open>a11 = 0\<close> \<open>a21 = 0\<close> \<open>a12 \<noteq> 0\<close> x
    by auto
next
  case False
  let ?k = "a21 / a11"
  from x
  have "?k * a11 * fst x + ?k * a12 * snd x = ?k * b1"
    using \<open>a11 \<noteq> 0\<close>
    by (auto simp add: field_simps)
  moreover
  have "a21 = ?k * a11" "a22 = ?k * a12" "b2 = ?k * b1"
    using assms(1) x0 \<open>a11 \<noteq> 0\<close>
    by (auto simp add: field_simps)
  ultimately
  show ?thesis
    by auto
qed

text \<open>All solutions of a homogenous system of 2 equations with 3 unknows are proportional\<close>
lemma linear_system_homogenous_3_2:
  fixes a11 a12 a13 a21 a22 a23 x1 y1 z1 x2 y2 z2 :: "'a::field"
  assumes "f1 = (\<lambda> x y z. a11 * x + a12 * y + a13 * z)"
  assumes "f2 = (\<lambda> x y z. a21 * x + a22 * y + a23 * z)"
  assumes "f1 x1 y1 z1 = 0" and "f2 x1 y1 z1 = 0"
  assumes "f1 x2 y2 z2 = 0" and "f2 x2 y2 z2 = 0"
  assumes "x2 \<noteq> 0 \<or> y2 \<noteq> 0 \<or> z2 \<noteq> 0"
  assumes "det2 a11 a12 a21 a22 \<noteq> 0 \<or> det2 a11 a13 a21 a23 \<noteq> 0 \<or> det2 a12 a13 a22 a23 \<noteq> 0"
  shows "\<exists> k. x1 = k * x2 \<and> y1 = k * y2 \<and> z1 = k * z2"
proof-
  let ?Dz = "det2 a11 a12 a21 a22"
  let ?Dy = "det2 a11 a13 a21 a23"
  let ?Dx = "det2 a12 a13 a22 a23"

  have "a21 * (f1 x1 y1 z1) - a11 * (f2 x1 y1 z1) = 0"
    using assms
    by simp
  hence yz1: "?Dz*y1 + ?Dy*z1 = 0"
    using assms
    by (simp add: field_simps)

  have "a21 * (f1 x2 y2 z2) - a11 * (f2 x2 y2 z2) = 0"
    using assms
    by simp
  hence yz2: "?Dz*y2 + ?Dy*z2 = 0"
    using assms
    by (simp add: field_simps)
                                     
  have "a22 * (f1 x1 y1 z1) - a12 * (f2 x1 y1 z1) = 0"
    using assms
    by simp                          
  hence xz1: "-?Dz*x1 + ?Dx*z1 = 0"
    using assms
    by (simp add: field_simps)

  have "a22 * (f1 x2 y2 z2) - a12 * (f2 x2 y2 z2) = 0"
    using assms
    by simp                          
  hence xz2: "-?Dz*x2 + ?Dx*z2 = 0"
    using assms
    by (simp add: field_simps)

  have "a23 * (f1 x1 y1 z1) - a13 * (f2 x1 y1 z1) = 0"
    using assms
    by simp                          
  hence xy1: "?Dy*x1 + ?Dx*y1 = 0"
    using assms
    by (simp add: field_simps)

  have "a23 * (f1 x2 y2 z2) - a13 * (f2 x2 y2 z2) = 0"
    using assms
    by simp                          
  hence xy2: "?Dy*x2 + ?Dx*y2 = 0"
    using assms
    by (simp add: field_simps)

  show ?thesis
    using `?Dz \<noteq> 0 \<or> ?Dy \<noteq> 0 \<or> ?Dx \<noteq> 0`
  proof safe
    assume "?Dz \<noteq> 0"
    
    hence *:
      "x2 = (?Dx / ?Dz) * z2" "y2 = - (?Dy / ?Dz) * z2"
      "x1 = (?Dx / ?Dz) * z1" "y1 = - (?Dy / ?Dz) * z1"
      using xy2 xz2 xy1 xz1 yz1 yz2
      by (simp_all add: field_simps)     

    hence "z2 \<noteq> 0"
      using `x2 \<noteq> 0 \<or> y2 \<noteq> 0 \<or> z2 \<noteq> 0`
      by auto

    thus ?thesis
      using * `?Dz \<noteq> 0`
      by (rule_tac x="z1/z2" in exI) auto
  next
    assume "?Dy \<noteq> 0"
    hence *:
      "x2 = - (?Dx / ?Dy) * y2" "z2 = - (?Dz / ?Dy) * y2"
      "x1 = - (?Dx / ?Dy) * y1" "z1 = - (?Dz / ?Dy) * y1"
      using xy2 xz2 xy1 xz1 yz1 yz2
      by (simp_all add: field_simps)     

    hence "y2 \<noteq> 0"
      using `x2 \<noteq> 0 \<or> y2 \<noteq> 0 \<or> z2 \<noteq> 0`
      by auto

    thus ?thesis
      using * `?Dy \<noteq> 0`
      by (rule_tac x="y1/y2" in exI) auto
  next
    assume "?Dx \<noteq> 0"
    hence *:
      "y2 = - (?Dy / ?Dx) * x2" "z2 = (?Dz / ?Dx) * x2"
      "y1 = - (?Dy / ?Dx) * x1" "z1 = (?Dz / ?Dx) * x1"
      using xy2 xz2 xy1 xz1 yz1 yz2
      by (simp_all add: field_simps)     

    hence "x2 \<noteq> 0"
      using `x2 \<noteq> 0 \<or> y2 \<noteq> 0 \<or> z2 \<noteq> 0`
      by auto

    thus ?thesis
      using * `?Dx \<noteq> 0`
      by (rule_tac x="x1/x2" in exI) auto
  qed
qed

end
