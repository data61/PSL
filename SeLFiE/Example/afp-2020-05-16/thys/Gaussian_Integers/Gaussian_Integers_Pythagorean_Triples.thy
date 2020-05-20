(*
  File:     Gaussian_Integers_Pythagorean_Triples.thy
  Author:   Manuel Eberl, TU München

  Application of Gaussian integers to deriving Euclid's formula for primitive Pythagorean triples
*)
subsection \<open>Primitive Pythagorean triples\<close>
theory Gaussian_Integers_Pythagorean_Triples
  imports Gaussian_Integers
begin

text \<open>
  In this section, we derive Euclid's formula for primitive Pythagorean triples using
  Gaussian integers, following Stillwell~\cite{stillwell}.
\<close>
definition prim_pyth_triple :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "prim_pyth_triple x y z \<longleftrightarrow> x > 0 \<and> y > 0 \<and> coprime x y \<and> x\<^sup>2 + y\<^sup>2 = z\<^sup>2"

lemma prim_pyth_triple_commute: "prim_pyth_triple x y z \<longleftrightarrow> prim_pyth_triple y x z"
  by (simp add: prim_pyth_triple_def coprime_commute add_ac conj_ac)

lemma prim_pyth_triple_aux:
  fixes u v :: nat
  assumes "v \<le> u"
  shows "(2 * u * v) ^ 2 + (u ^ 2 - v ^ 2) ^ 2 = (u ^ 2 + v ^ 2) ^ 2"
proof -
  have "int ((2 * u * v) ^ 2 + (u ^ 2 - v ^ 2) ^ 2) =
        (2 * int u * int v) ^ 2 + (int u ^ 2 - int v ^ 2) ^ 2"
    using assms by (simp add: of_nat_diff)
  also have "\<dots> = (int u ^ 2 + int v ^ 2) ^ 2"
    by (simp add: power2_eq_square algebra_simps)
  also have "\<dots> = int ((u ^ 2 + v ^ 2) ^ 2)"
    by simp
  finally show ?thesis
    by (simp only: of_nat_eq_iff)
qed

lemma prim_pyth_tripleI1:
  assumes "0 < v" "v < u" "coprime u v" "\<not>(odd u \<and> odd v)"
  shows   "prim_pyth_triple (2 * u * v) (u\<^sup>2 - v\<^sup>2) (u\<^sup>2 + v\<^sup>2)"
proof -
  have "v ^ 2 < u ^ 2"
    using assms by (intro power_strict_mono) auto
  hence "\<not>u ^ 2 < v ^ 2" by linarith

  from assms have "coprime (int u) (int v ^ 2)"
    by auto
  hence "coprime (int u) (int u * int u + (-(int v ^ 2)))"
    unfolding coprime_iff_gcd_eq_1 by (subst gcd_add_mult) auto
  also have "int u * int u + (-(int v ^ 2)) = int (u ^ 2 - v ^ 2)"
    using \<open>v < u\<close> by (simp add: of_nat_diff flip: power2_eq_square)
  finally have coprime1: "coprime u (u ^ 2 - v ^ 2)"
    by auto

  from assms have "coprime (int v) (int u ^ 2)"
    by (auto simp: coprime_commute)
  hence "coprime (int v) ((-int v) * int v + int u ^ 2)"
    unfolding coprime_iff_gcd_eq_1 by (subst gcd_add_mult) auto
  also have "(-int v) * int v + int u ^ 2 = int (u ^ 2 - v ^ 2)"
    using \<open>v < u\<close> by (simp add: of_nat_diff flip: power2_eq_square)
  finally have coprime2: "coprime v (u ^ 2 - v ^ 2)"
    by auto

  have "(2 * u * v) ^ 2 + (u ^ 2 - v ^ 2) ^ 2 = (u ^ 2 + v ^ 2) ^ 2"
    using \<open>v < u\<close> by (intro prim_pyth_triple_aux) auto
  moreover have "coprime (2 * u * v) (u ^ 2 - v ^ 2)"
    using assms \<open>\<not>u ^ 2 < v ^ 2\<close> coprime1 coprime2 by auto
  ultimately show ?thesis using assms \<open>v ^ 2 < u ^ 2\<close>
    by (simp add: prim_pyth_triple_def)
qed

lemma prim_pyth_tripleI2:
  assumes "0 < v" "v < u" "coprime u v" "\<not>(odd u \<and> odd v)"
  shows   "prim_pyth_triple (u\<^sup>2 - v\<^sup>2) (2 * u * v) (u\<^sup>2 + v\<^sup>2)"
  using prim_pyth_tripleI1[OF assms] by (simp add: prim_pyth_triple_commute)

lemma primitive_pythagorean_tripleE_int:
  assumes "z ^ 2 = x ^ 2 + y ^ 2"
  assumes "coprime x y"
  obtains u v :: int
    where "coprime u v" and "\<not>(odd u \<and> odd v)"
      and "x = 2 * u * v \<and> y = u\<^sup>2 - v\<^sup>2  \<or>  x = u\<^sup>2 - v\<^sup>2 \<and> y = 2 * u * v"
proof -
  have "\<not>(even x \<and> even y)"
    using not_coprimeI[of 2 x y] \<open>coprime x y\<close> by auto
  moreover have "\<not>(odd x \<and> odd y)"
  proof safe
    assume "odd x" "odd y"
    hence "[x ^ 2 + y ^ 2 = 1 + 1] (mod 4)"
      by (intro cong_add odd_square_cong_4_int)
    hence "[z ^ 2 = 2] (mod 4)"
      by (simp add: assms)
    moreover have "[z ^ 2 = 0] (mod 4) \<or> [z ^ 2 = 1] (mod 4)"
      using even_square_cong_4_int[of z] odd_square_cong_4_int[of z]
      by (cases "even z") auto
    ultimately show False
      by (auto simp: cong_def)
  qed
  ultimately have "even y \<longleftrightarrow> odd x"
    by blast

  have "even z \<longleftrightarrow> even (z ^ 2)"
    by auto
  also have "even (z ^ 2) \<longleftrightarrow> even (x ^ 2 + y ^ 2)"
    by (subst assms(1)) auto
  finally have "odd z"
    by (cases "even x") (auto simp: \<open>even y \<longleftrightarrow> \<not>even x\<close>)

  define t where "t = of_int x + \<i>\<^sub>\<int> * of_int y"
  from assms have t_mult_cnj: "t * gauss_cnj t = of_int z ^ 2"
    by (simp add: t_def power2_eq_square algebra_simps flip: of_int_mult of_int_add)

  have "gauss_int_norm t = z ^ 2"
    by (simp add: gauss_int_norm_def t_def assms)
  with \<open>coprime x y\<close> and \<open>odd z\<close> have "coprime t (gauss_cnj t)"
    by (intro coprime_self_gauss_cnj)
       (auto simp: t_def gauss_int_norm_def assms(1) [symmetric] even_nat_iff)
  moreover have "is_square (t * gauss_cnj t)"
    by (subst t_mult_cnj) auto
  hence "is_nth_power_upto_unit 2 (t * gauss_cnj t)"
    by (auto intro: is_nth_power_upto_unit_base)
  ultimately have "is_nth_power_upto_unit 2 t"
    by (rule is_nth_power_upto_unit_mult_coprimeD1)
  then obtain a b where ab: "is_unit a" "a * t = b ^ 2"
    by (auto simp: is_nth_power_upto_unit_def is_nth_power_def)
  from ab(1) have "a \<in> {1, -1, \<i>\<^sub>\<int>, -\<i>\<^sub>\<int>}"
    by (auto simp: is_unit_gauss_int_iff)
  then obtain u v :: int where "ReZ t = 2 * u * v \<and> ImZ t = u ^ 2 - v ^ 2 \<or> 
                                ImZ t = 2 * u * v \<and> ReZ t = u ^ 2 - v ^ 2"
  proof safe
    assume [simp]: "a = 1"
    have "ReZ t = ReZ b ^ 2 - ImZ b ^ 2" "ImZ t = 2 * ReZ b * ImZ b" using ab(2)
      by (auto simp: gauss_int_eq_iff power2_eq_square)
    thus ?thesis using that by blast
  next
    assume [simp]: "a = -1"
    have "ReZ t = ImZ b ^ 2 - (-ReZ b) ^ 2" "ImZ t = 2 * ImZ b * (-ReZ b)" using ab(2)
      by (auto simp: gauss_int_eq_iff power2_eq_square algebra_simps)
    thus ?thesis using that by blast
  next
    assume [simp]: "a = \<i>\<^sub>\<int>"
    hence "ImZ t = ImZ b ^ 2 - ReZ b ^ 2" "ReZ t = 2 * ImZ b * ReZ b" using ab(2)
      by (auto simp: gauss_int_eq_iff power2_eq_square algebra_simps)
    thus ?thesis using that by blast
  next
    assume [simp]: "a = -\<i>\<^sub>\<int>"
    hence "ImZ t = (-ReZ b) ^ 2 - ImZ b ^ 2" "ReZ t = 2 * (-ReZ b) * ImZ b" using ab(2)
      by (auto simp: gauss_int_eq_iff power2_eq_square algebra_simps)
    thus ?thesis using that by blast
  qed
  also have "ReZ t = x"
    by (simp add: t_def)
  also have "ImZ t = y"
    by (simp add: t_def)
  finally have xy: "x = 2 * u * v \<and> y = u\<^sup>2 - v\<^sup>2 \<or> x = u\<^sup>2 - v\<^sup>2 \<and> y = 2 * u * v"
    by blast

  have not_both_odd: "\<not>(odd u \<and> odd v)"
  proof safe
    assume "odd u" "odd v"
    hence "even x" "even y"
      using xy by auto
    with \<open>coprime x y\<close> show False
      by auto
  qed

  have "coprime u v"
  proof (rule coprimeI)
    fix d assume "d dvd u" "d dvd v"
    hence "d dvd (u\<^sup>2 - v\<^sup>2)" "d dvd 2 * u * v"
      by (auto simp: power2_eq_square)
    with xy have "d dvd x" "d dvd y"
      by auto
    with \<open>coprime x y\<close> show "is_unit d"
      using not_coprimeI by blast
  qed
  with xy not_both_odd show ?thesis
    using that[of u v] by blast
qed

lemma prim_pyth_tripleE:
  assumes "prim_pyth_triple x y z"
  obtains u v :: nat
  where "0 < v" and "v < u" and "coprime u v" and "\<not>(odd u \<and> odd v)" and "z = u\<^sup>2 + v\<^sup>2"
    and "x = 2 * u * v \<and> y = u\<^sup>2 - v\<^sup>2  \<or>  x = u\<^sup>2 - v\<^sup>2 \<and> y = 2 * u * v"
proof -
  have *: "(int z) ^ 2 = (int x) ^ 2 + (int y) ^ 2" "coprime (int x) (int y)"
    using assms by (auto simp flip: of_nat_power of_nat_add simp: prim_pyth_triple_def)
  obtain u v
    where uv: "coprime u v" "\<not>(odd u \<and> odd v)"
              "int x = 2 * u * v \<and> int y = u\<^sup>2 - v\<^sup>2  \<or>  int x = u\<^sup>2 - v\<^sup>2 \<and> int y = 2 * u * v"
    using primitive_pythagorean_tripleE_int[OF *] by metis
  define u' v' where "u' = nat \<bar>u\<bar>" and "v' = nat \<bar>v\<bar>"

  have **: "a = 2 * u' * v'" if "int a = 2 * u * v" for a
  proof -
    from that have "nat \<bar>int a\<bar> = nat \<bar>2 * u * v\<bar>"
      by (simp only: )
    thus "a = 2 * u' * v'"
      by (simp add: u'_def v'_def abs_mult nat_mult_distrib)
  qed
  have ***: "a = u' ^ 2 - v' ^ 2" "v' \<le> u'" if "int a = u ^ 2 - v ^ 2" for a
  proof -
    have "v ^ 2 \<le> v ^ 2 + int a"
      by simp
    also have "\<dots> = u ^ 2"
      using that by simp
    finally have "\<bar>v\<bar> \<le> \<bar>u\<bar>"
      using abs_le_square_iff by blast
    thus "v' \<le> u'"
      by (simp add: v'_def u'_def)

    from that have "u ^ 2 = v ^ 2 + int a"
      by simp
    hence "nat \<bar>u ^ 2\<bar> = nat \<bar>v ^ 2 + int a\<bar>"
      by (simp only: )
    also have "nat \<bar>u ^ 2\<bar> = u' ^ 2"
      by (simp add: u'_def flip: nat_power_eq)
    also have "nat \<bar>v ^ 2 + int a\<bar> = v' ^ 2 + a"
      by (simp add: nat_add_distrib v'_def flip: nat_power_eq)
    finally show "a = u' ^ 2 - v' ^ 2"
      by simp
  qed

  have eq: "x = 2 * u' * v' \<and> y = u'\<^sup>2 - v'\<^sup>2  \<or>  x = u'\<^sup>2 - v'\<^sup>2 \<and> y = 2 * u' * v'" and "v' \<le> u'"
    using uv(3) **[of x] **[of y] ***[of x] ***[of y] by blast+
  moreover have "coprime u' v'"
    using \<open>coprime u v\<close>
    by (auto simp: u'_def v'_def)
  moreover have "\<not>(odd u' \<and> odd v')"
    using uv(2) by (auto simp: u'_def v'_def)
  moreover have "v' \<noteq> u'" "v' > 0"
    using \<open>coprime u' v'\<close> eq assms by (auto simp: prim_pyth_triple_def)
  moreover from this have "v' < u'"
    using \<open>v' \<le> u'\<close> by auto
  moreover have "z = u'\<^sup>2 + v'\<^sup>2"
  proof -
    from assms have "z ^ 2 = x ^ 2 + y ^ 2"
      by (simp add: prim_pyth_triple_def)
    also have "\<dots> = (2 * u' * v') ^ 2 + (u' ^ 2 - v' ^ 2) ^ 2"
      using eq by (auto simp: add_ac)
    also have "\<dots> = (u' ^ 2 + v' ^ 2) ^ 2"
      by (intro prim_pyth_triple_aux) fact
    finally show ?thesis by simp
  qed
  ultimately show ?thesis using that[of v' u'] by metis
qed

theorem prim_pyth_triple_iff:
  "prim_pyth_triple x y z \<longleftrightarrow>
     (\<exists>u v. 0 < v \<and> v < u \<and> coprime u v \<and> \<not>(odd u \<and> odd v) \<and>
            (x = 2 * u * v \<and> y = u\<^sup>2 - v\<^sup>2  \<or>  x = u\<^sup>2 - v\<^sup>2 \<and> y = 2 * u * v) \<and> z = u\<^sup>2 + v\<^sup>2)"
  (is "_ \<longleftrightarrow> ?rhs")
proof
  assume "prim_pyth_triple x y z"
  from prim_pyth_tripleE[OF this] show ?rhs by metis
next
  assume ?rhs
  then obtain u v where uv: "0 < v" "v < u" "coprime u v" "\<not>(odd u \<and> odd v)" "z = u\<^sup>2 + v\<^sup>2" and
                        eq: "x = 2 * u * v \<and> y = u\<^sup>2 - v\<^sup>2  \<or>  x = u\<^sup>2 - v\<^sup>2 \<and> y = 2 * u * v"
    by metis
  thus "prim_pyth_triple x y z"
    using uv prim_pyth_tripleI1[OF uv(1-4)] prim_pyth_tripleI2[OF uv(1-4)] uv(5) eq by auto
qed

end