(*
  File:     Pell.thy
  Author:   Manuel Eberl, TU München

  Basic facts about the solutions of Pell's equation
*)
section \<open>Pell's equation\<close>
theory Pell
imports
  Complex_Main
  "HOL-Computational_Algebra.Computational_Algebra"
begin

text \<open>
  Pell's equation has the general form $x^2 = 1 + D y^2$ where \<open>D \<in> \<nat>\<close> is a parameter
  and \<open>x\<close>, \<open>y\<close> are \<open>\<int>\<close>-valued variables. As we will see, that case where \<open>D\<close> is a
  perfect square is trivial and therefore uninteresting; we will therefore assume that \<open>D\<close> is
  not a perfect square for the most part.

  Furthermore, it is obvious that the solutions to Pell's equation are symmetric around the
  origin in the sense that \<open>(x, y)\<close> is a solution iff \<open>(\<plusminus>x, \<plusminus>y)\<close> is a solution. We will
  therefore mostly look at solutions \<open>(x, y)\<close> where both \<open>x\<close> and \<open>y\<close> are non-negative, since
  the remaining solutions are a trivial consequence of these.

  Information on the material treated in this formalisation can be found in many textbooks and
   lecture notes, e.\,g.\ \cite{jacobson2008solving, auckland_pell}.
\<close>

subsection \<open>Preliminary facts\<close>

lemma gcd_int_nonpos_iff [simp]: "gcd x (y :: int) \<le> 0 \<longleftrightarrow> x = 0 \<and> y = 0"
proof
  assume "gcd x y \<le> 0"
  with gcd_ge_0_int[of x y] have "gcd x y = 0" by linarith
  thus "x = 0 \<and> y = 0" by auto
qed auto

lemma minus_in_Ints_iff [simp]:
  "-x \<in> \<int> \<longleftrightarrow> x \<in> \<int>"
  using Ints_minus[of x] Ints_minus[of "-x"] by auto

text \<open>
  A (positive) square root of a natural number is either a natural number or irrational.
\<close>
lemma nonneg_sqrt_nat_or_irrat:
  assumes "x ^ 2 = real a" and "x \<ge> 0"
  shows   "x \<in> \<nat> \<or> x \<notin> \<rat>"
proof safe
  assume "x \<notin> \<nat>" and "x \<in> \<rat>"
  from Rats_abs_nat_div_natE[OF this(2)]
    obtain p q :: nat where q_nz [simp]: "q \<noteq> 0" and "abs x = p / q" and coprime: "coprime p q" .
  with \<open>x \<ge> 0\<close> have x: "x = p / q"
      by simp
  with assms have "real (q ^ 2) * real a = real (p ^ 2)"
    by (simp add: field_simps)
  also have "real (q ^ 2) * real a = real (q ^ 2 * a)"
    by simp
  finally have "p ^ 2 = q ^ 2 * a"
    by (subst (asm) of_nat_eq_iff) auto
  hence "q ^ 2 dvd p ^ 2"
    by simp
  hence "q dvd p"
    by simp
  with coprime have "q = 1"
    by auto
  with x and \<open>x \<notin> \<nat>\<close> show False
    by simp
qed

text \<open>
  A square root of a natural number is either an integer or irrational.
\<close>
corollary sqrt_nat_or_irrat:
  assumes "x ^ 2 = real a"
  shows   "x \<in> \<int> \<or> x \<notin> \<rat>"
proof (cases "x \<ge> 0")
  case True
  with nonneg_sqrt_nat_or_irrat[OF assms this]
    show ?thesis by (auto simp: Nats_altdef2)
next
  case False
  from assms have "(-x) ^ 2 = real a"
    by simp
  moreover from False have "-x \<ge> 0"
    by simp
  ultimately have "-x \<in> \<nat> \<or> -x \<notin> \<rat>"
    by (rule nonneg_sqrt_nat_or_irrat)
  thus ?thesis
    by (auto simp: Nats_altdef2)
qed

corollary sqrt_nat_or_irrat':
  "sqrt (real a) \<in> \<nat> \<or> sqrt (real a) \<notin> \<rat>"
  using nonneg_sqrt_nat_or_irrat[of "sqrt a" a] by auto

text \<open>
  The square root of a natural number \<open>n\<close> is again a natural number iff \<open>n is a perfect square.\<close>
\<close>
corollary sqrt_nat_iff_is_square:
  "sqrt (real n) \<in> \<nat> \<longleftrightarrow> is_square n"
proof
  assume "sqrt (real n) \<in> \<nat>"
  then obtain k where "sqrt (real n) = real k" by (auto elim!: Nats_cases)
  hence "sqrt (real n) ^ 2 = real (k ^ 2)" by (simp only: of_nat_power)
  also have "sqrt (real n) ^ 2 = real n" by simp
  finally have "n = k ^ 2" by (simp only: of_nat_eq_iff)
  thus "is_square n" by blast
qed (auto elim!: is_nth_powerE)

corollary irrat_sqrt_nonsquare: "\<not>is_square n \<Longrightarrow> sqrt (real n) \<notin> \<rat>"
  using sqrt_nat_or_irrat'[of n] by (auto simp: sqrt_nat_iff_is_square)


subsection \<open>The case of a perfect square\<close>

text \<open>
  As we have noted, the case where \<open>D\<close> is a perfect square is trivial: In fact, we will
  show that the only solutions in this case are the trivial solutions \<open>(x, y) = (\<plusminus>1, 0)\<close> if
  \<open>D\<close> is a non-zero perfect square, or \<open>(\<plusminus>1, y)\<close> for arbitrary \<open>y \<in> \<int>\<close> if \<open>D = 0\<close>.
\<close>
context
  fixes D :: nat
  assumes square_D: "is_square D"
begin

lemma pell_square_solution_nat_aux:
  fixes x y :: nat
  assumes "D > 0" and "x ^ 2 = 1 + D * y ^ 2"
  shows "(x, y) = (1, 0)"
proof -
  from assms have x_nz: "x > 0" by (auto intro!: Nat.gr0I)
  from square_D obtain d where [simp]: "D = d\<^sup>2"
    by (auto elim: is_nth_powerE)
  have "int x ^ 2 = int (x ^ 2)" by simp
  also note assms(2)
  also have "int (1 + D * y ^ 2) = 1 + int D * int y ^ 2" by simp
  finally have "(int x + int d * int y) * (int x - int d * int y) = 1"
    by (simp add: algebra_simps power2_eq_square)
  hence *: "int x + int d * int y = 1 \<and> int x - int d * int y = 1"
    using x_nz by (subst (asm) pos_zmult_eq_1_iff) (auto intro: add_pos_nonneg)
  from * have [simp]: "x = 1" by simp
  moreover from * and assms(1) have "y = 0" by auto
  ultimately show ?thesis by simp
qed

lemma pell_square_solution_int_aux:
  fixes x y :: int
  assumes "D > 0" and "x ^ 2 = 1 + D * y ^ 2"
  shows "x \<in> {-1, 1} \<and> y = 0"
proof -
  define x' y' where "x' = nat \<bar>x\<bar>" and "y' = nat \<bar>y\<bar>"
  have x: "x = sgn x * x'" and y: "y = sgn y * y'"
    by (auto simp: sgn_if x'_def y'_def)
  have zero_iff: "x = 0 \<longleftrightarrow> x' = 0" "y = 0 \<longleftrightarrow> y' = 0"
    by (auto simp: x'_def y'_def)
  note assms(2)
  also have "x ^ 2 = int (x' ^ 2)"
    by (subst x) (auto simp: sgn_if zero_iff)
  also have "1 + D * y ^ 2 = int (1 + D * y' ^ 2)"
    by (subst y) (auto simp: sgn_if zero_iff)
  also note of_nat_eq_iff
  finally have "x'\<^sup>2 = 1 + D * y'\<^sup>2" .
  from \<open>D > 0\<close> and this have "(x', y') = (1, 0)"
    by (rule pell_square_solution_nat_aux)
  thus ?thesis by (auto simp: x'_def y'_def)
qed

lemma pell_square_solution_nat_iff:
  fixes x y :: nat
  shows "x ^ 2 = 1 + D * y ^ 2  \<longleftrightarrow>  x = 1 \<and> (D = 0 \<or> y = 0)"
  using pell_square_solution_nat_aux[of x y] by (cases "D = 0") auto

lemma pell_square_solution_int_iff:
  fixes x y :: int
  shows "x ^ 2 = 1 + D * y ^ 2  \<longleftrightarrow>  x \<in> {-1, 1} \<and> (D = 0 \<or> y = 0)"
  using pell_square_solution_int_aux[of x y] by (cases "D = 0") (auto simp: power2_eq_1_iff)

end


subsection \<open>Existence of a non-trivial solution\<close>

text \<open>
  Let us now turn to the case where \<open>D\<close> is not a perfect square.

  We first show that Pell's equation always has at least one non-trivial solution (apart
  from the trivial solution \<open>(1, 0)\<close>). For this, we first need a lemma about the existence
  of rational approximations of real numbers.

  The following lemma states that for any positive integer \<open>s\<close> and real number \<open>x\<close>, we can find a
  rational approximation \<open>t / u\<close> to \<open>x\<close> with an error of most \<open>1 / (u * s)\<close> where the denominator
  \<open>u\<close> is at most \<open>s\<close>.
\<close>
lemma pell_approximation_lemma:
  fixes s :: nat and x :: real
  assumes s: "s > 0"
  shows "\<exists>u::nat. \<exists>t::int. u > 0 \<and> coprime u t \<and> 1 / s \<in> {\<bar>t - u * x\<bar><..1 / u}"
proof -
  define f where "f = (\<lambda>u. \<lceil>u * x\<rceil>)"
  define g :: "nat \<Rightarrow> int" where "g = (\<lambda>u. \<lfloor>frac (u * x) * s\<rfloor>)"
  {
    fix u :: nat assume u: "u \<le> s"
    hence "frac (u * x) * real s < 1 * real s"
      using s by (intro mult_strict_right_mono) (auto simp: frac_lt_1)
    hence "g u < int s" by (auto simp: floor_less_iff g_def)
  }
  hence "g ` {..s} \<subseteq> {0..<s}"
    by (auto simp: g_def floor_less_iff)
  hence "card (g ` {..s}) \<le> card {0..<int s}"
    by (intro card_mono) auto
  also have "\<dots> < card {..s}" by simp
  finally have "\<not>inj_on g {..s}" by (rule pigeonhole)
  then obtain a b where ab: "a \<le> s" "b \<le> s" "a \<noteq> b" "g a = g b"
    by (auto simp: inj_on_def)
  define u1 and u2 where "u1 = max a b" and "u2 = min a b"
  have u12: "u1 \<le> s" "u2 \<le> s" "u2 < u1" "g u1 = g u2"
    using ab by (auto simp: u1_def u2_def)

  define u t where "u = u1 - u2" and "t = \<lfloor>u1 * x\<rfloor> - \<lfloor>u2 * x\<rfloor>"
  have u: "u > 0" "\<bar>u\<bar> \<le> s"
    using u12 by (simp_all add: u_def)

  from \<open>g u1 = g u2\<close> have "\<bar>frac (u2 * x) * s - frac (u1 * x) * s\<bar> < 1"
    unfolding g_def by linarith
  also have "\<bar>frac (u2 * x) * s - frac (u1 * x) * s\<bar> =
               \<bar>real s\<bar> * \<bar>frac (u2 * x) - frac (u1 * x)\<bar>"
    by (subst abs_mult [symmetric]) (simp add: algebra_simps)
  finally have "\<bar>t - u * x\<bar> * s < 1" using \<open>u1 > u2\<close>
    by (simp add: g_def u_def t_def frac_def algebra_simps of_nat_diff)
  with \<open>s > 0\<close> have less: "\<bar>t - u * x\<bar> < 1 / s" by (simp add: divide_simps)

  define d where "d = gcd (nat \<bar>t\<bar>) u"
  define t' :: int and u' :: nat where "t'= t div d" and "u' = u div d"
  from u have "d \<noteq> 0"
    by (intro notI) (auto simp: d_def)
  have "int (gcd (nat \<bar>t\<bar>) u) = gcd \<bar>t\<bar> (int u)"
    by simp
  hence t'_u': "t = t' * d" "u = u' * d"
    by (auto simp: t'_def u'_def d_def nat_dvd_iff)

  from \<open>d \<noteq> 0\<close> have "\<bar>t' - u' * x\<bar> * 1 \<le> \<bar>t' - u' * x\<bar> * \<bar>real d\<bar>"
    by (intro mult_left_mono) auto
  also have "\<dots> = \<bar>t - u * x\<bar>" by (subst abs_mult [symmetric]) (simp add: algebra_simps t'_u')
  also note less
  finally have "\<bar>t' - u' * x\<bar> < 1 / s" by simp
  moreover {
    from \<open>s > 0\<close> and u have "1 / s \<le> 1 / u"
      by (simp add: divide_simps u_def)
    also have "\<dots> = 1 / u' / d" by (simp add: t'_u' divide_simps)
    also have "\<dots> \<le> 1 / u' / 1" using \<open>d \<noteq> 0\<close> by (intro divide_left_mono) auto
    finally have "1 / s \<le> 1 / u'" by simp
  }
  ultimately have "1 / s \<in> {\<bar>t' - u' * x\<bar><..1 / u'}" by auto
  moreover from \<open>u > 0\<close> have "u' > 0" by (auto simp: t'_u')
  moreover {
    have "gcd u t = gcd t' u' * int d"
      by (simp add: t'_u' gcd_mult_right gcd.commute)
    also have "int d = gcd u t"
      by (simp add: d_def gcd.commute)
    finally have "gcd u' t' = 1" using u by (simp add: gcd.commute)
  }
  ultimately show ?thesis by blast
qed

text \<open>
  As a simple corollary of this, we can show that for irrational \<open>x\<close>, there is an infinite
  number of rational approximations \<open>t / u\<close> to \<open>x\<close> whose error is less that \<open>1 / u\<^sup>2\<close>.
\<close>
corollary pell_approximation_corollary:
  fixes x :: real
  assumes "x \<notin> \<rat>"
  shows "infinite {(t :: int, u :: nat). u > 0 \<and> coprime u t \<and> \<bar>t - u * x\<bar> < 1 / u}"
    (is "infinite ?A")
proof
  assume fin: "finite ?A"
  let ?f = "\<lambda>(t :: int, u :: nat). \<bar>t - u * x\<bar>"
  from fin have fin': "finite (insert 1 (?f ` ?A))" by blast
  have "Min (insert 1 (?f ` ?A)) > 0"
  proof (subst Min_gr_iff)
    have "a \<noteq> b * x" if "b > 0" for a :: int and b :: nat
    proof
      assume "a = b * x"
      with \<open>b > 0\<close> have "x = a / b" by (simp add: field_simps)
      with \<open>x \<notin> \<rat>\<close> and \<open>b > 0\<close> show False by (auto simp: Rats_eq_int_div_nat)
    qed
    thus "\<forall>x\<in>insert 1 (?f ` ?A). x > 0" by auto
  qed (insert fin', simp_all)
  also note real_arch_inverse
  finally obtain M :: nat where M: "M \<noteq> 0" "inverse M < Min (insert 1 (?f ` ?A))"
    by blast
  hence "M > 0" by simp

  from pell_approximation_lemma[OF this, of x] obtain u :: nat and t :: int
    where ut: "u > 0" "coprime u t" "1 / real M \<in> {?f (t, u)<..1 / u}" by auto
  from ut have "?f (t, u) < 1 / real M" by simp
  also from M have "\<dots>  < Min (insert 1 (?f ` ?A))"
    by (simp add: divide_simps)
  also from ut have "Min (insert 1 (?f ` ?A)) \<le> ?f (t, u)"
    by (intro Min.coboundedI fin') auto
  finally show False by simp
qed


locale pell =
  fixes D :: nat
  assumes nonsquare_D: "\<not>is_square D"
begin

lemma D_gt_1: "D > 1"
proof -
  from nonsquare_D have "D \<noteq> 0" "D \<noteq> 1" by (auto intro!: Nat.gr0I)
  thus ?thesis by simp
qed

lemma D_pos: "D > 0"
  using nonsquare_D by (intro Nat.gr0I) auto

text \<open>
  With the above corollary, we can show the existence of a non-trivial solution. We restrict our
  attention to solutions \<open>(x, y)\<close> where both \<open>x\<close> and \<open>y\<close> are non-negative.
\<close>
theorem pell_solution_exists: "\<exists>(x::nat) (y::nat). y \<noteq> 0 \<and> x\<^sup>2 = 1 + D * y\<^sup>2"
proof -
  define S where "S = {(t :: int, u :: nat). u > 0 \<and> coprime u t \<and> \<bar>t - u * sqrt D\<bar> < 1 / u}"
  let ?f = "\<lambda>(t :: int, u :: nat). t\<^sup>2 - u\<^sup>2 * D"
  define M where "M = \<lfloor>1 + 2 * sqrt D\<rfloor>"
  have infinite: "\<not>finite S" unfolding S_def
    by (intro pell_approximation_corollary irrat_sqrt_nonsquare nonsquare_D)

  have subset: "?f ` S \<subseteq> {-M..M}"
  proof safe
    fix u :: nat and t :: int
    assume tu: "(t, u) \<in> S"
    from tu have [simp]: "u > 0" by (auto simp: S_def)
    have "\<bar>t + u * sqrt D\<bar> = \<bar>t - u * sqrt D + 2 * u * sqrt D\<bar>" by simp
    also have "\<dots> \<le> \<bar>t - u * sqrt D\<bar> + \<bar>2 * u * sqrt D\<bar>"
      by (rule abs_triangle_ineq)
    also have "\<bar>2 * u * sqrt D\<bar> = 2 * u * sqrt D" by simp
    also have "\<bar>t - u * sqrt D\<bar> \<le> 1 / u"
      using tu by (simp add: S_def)
    finally have le: "\<bar>t + u * sqrt D\<bar> \<le> 1 / u + 2 * u * sqrt D" by simp

    have "\<bar>t\<^sup>2 - u\<^sup>2 * D\<bar> = \<bar>t - u * sqrt D\<bar> * \<bar>t + u * sqrt D\<bar>"
      by (subst abs_mult [symmetric]) (simp add: algebra_simps power2_eq_square)
    also have "\<dots> \<le> 1 / u * (1 / u + 2 * u * sqrt D)"
      using tu by (intro mult_mono le) (auto simp: S_def)
    also have "\<dots> = 1 / real u ^ 2 + 2 * sqrt D"
      by (simp add: algebra_simps power2_eq_square)
    also from \<open>u > 0\<close> have "real u \<ge> 1" by linarith
    hence "1 / real u ^ 2 \<le> 1 / 1 ^ 2"
      by (intro divide_left_mono power_mono) auto
    finally have "\<bar>t\<^sup>2 - u\<^sup>2 * D\<bar> \<le> 1 + 2 * sqrt D" by simp
    hence "t\<^sup>2 - u\<^sup>2 * D \<ge> -M" "t\<^sup>2 - u\<^sup>2 * D \<le> M" unfolding M_def by linarith+
    thus "t\<^sup>2 - u\<^sup>2 * D \<in> {-M..M}" by simp
  qed
  hence fin: "finite (?f ` S)" by (rule finite_subset) auto

  from pigeonhole_infinite[OF infinite fin]
    obtain z where z: "z \<in> S" "infinite {z' \<in> S. ?f z' = ?f z}" by blast
  define k where "k = ?f z"
  with subset and z have k: "k \<in> {-M..M}" "infinite {z\<in>S. ?f z = k}"
    by (auto simp: k_def)

  have k_nz: "k \<noteq> 0"
  proof
    assume [simp]: "k = 0"
    note k(2)
    also have "?f z \<noteq> 0" if "z \<in> S" for z
    proof
      assume *: "?f z = 0"
      obtain t u where [simp]: "z = (t, u)" by (cases z)
      from * have "t ^ 2 = int u ^ 2 * int D" by simp
      hence "int u ^ 2 dvd t ^ 2" by simp
      hence "int u dvd t" by simp
      then obtain k where [simp]: "t = int u * k" by (auto elim!: dvdE)
      from * and \<open>z \<in> S\<close> have "k ^ 2 = int D"
        by (auto simp: power_mult_distrib S_def)
      also have "k ^ 2 = int (nat \<bar>k\<bar> ^ 2)" by simp
      finally have "D = nat \<bar>k\<bar> ^ 2" by (simp only: of_nat_eq_iff)
      hence "is_square D" by auto
      with nonsquare_D show False by contradiction
    qed
    hence "{z\<in>S. ?f z = k} = {}" by auto
    finally show False by simp
  qed

  let ?h = "\<lambda>(t :: int, u :: nat). (t mod (abs k), u mod (abs k))"
  have "?h ` {z\<in>S. ?f z = k} \<subseteq> {0..<abs k} \<times> {0..< abs k}"
    using k_nz by (auto simp: case_prod_unfold)
  hence "finite (?h ` {z\<in>S. ?f z = k})" by (rule finite_subset) auto
  from pigeonhole_infinite[OF k(2) this] obtain z'
    where z': "z' \<in> S" "?f z' = k" "infinite {z''\<in>{z\<in>S. ?f z = k}. ?h z'' = ?h z'}"
    by blast
  define l1 and l2 where "l1 = fst (?h z')" and "l2 = snd (?h z')"
  define S' where "S' = {(t,u) \<in> S. ?f (t,u) = k \<and> t mod abs k = l1 \<and> u mod abs k = l2}"
  note z'(3)
  also have "{z''\<in>{z\<in>S. ?f z = k}. ?h z'' = ?h z'} = S'"
    by (auto simp: l1_def l2_def case_prod_unfold S'_def)
  finally have infinite: "infinite S'" .

  from z'(1) and k_nz have l12: "l1 \<in> {0..<abs k}" "l2 \<in> {0..<abs k}"
    by (auto simp: l1_def l2_def case_prod_unfold)

  from infinite_arbitrarily_large[OF infinite]
  obtain X where X: "finite X" "card X = 2" "X \<subseteq> S'" by blast
  from finite_distinct_list[OF this(1)] obtain xs where xs: "set xs = X" "distinct xs"
    by blast
  with X have "length xs = 2" using distinct_card[of xs] by simp
  then obtain z1 z2 where [simp]: "xs = [z1, z2]"
    by (auto simp: length_Suc_conv eval_nat_numeral)
  from X xs have S': "z1 \<in> S'" "z2 \<in> S'" and neq: "z1 \<noteq> z2" by auto
  define t1 u1 t2 u2 where "t1 = fst z1" and "u1 = snd z1" and "t2 = fst z2" and "u2 = snd z2"
  have [simp]: "z1 = (t1, u1)" "z2 = (t2, u2)"
    by (simp_all add: t1_def u1_def t2_def u2_def)

  from S' have * [simp]: "t1 mod abs k = l1" "t2 mod abs k = l1" "u1 mod abs k = l2" "u2 mod abs k = l2"
    by (simp_all add: S'_def)
  define x where "x = (t1 * t2 - D * u1 * u2) div k"
  define y where "y = (t1 * u2 - t2 * u1) div k"

  from S' have "(t1\<^sup>2 - u1\<^sup>2 * D) = k" "(t2\<^sup>2 - u2\<^sup>2 * D) = k"
    by (auto simp: S'_def)
  hence "(t1\<^sup>2 - u1\<^sup>2 * D) * (t2\<^sup>2 - u2\<^sup>2 * D) = k ^ 2"
    unfolding power2_eq_square by simp
  also have "(t1\<^sup>2 - u1\<^sup>2 * D) * (t2\<^sup>2 - u2\<^sup>2 * D) =
               (t1 * t2 - D * u1 * u2) ^ 2 - D * (t1 * u2 - t2 * u1) ^ 2"
    by (simp add: power2_eq_square algebra_simps)
  finally have eq: "(t1 * t2 - D * u1 * u2)\<^sup>2 - D * (t1 * u2 - t2 * u1)\<^sup>2 = k\<^sup>2" .

  have "(t1 * u2 - t2 * u1) mod abs k = (l1 * l2 - l1 * l2) mod abs k"
    using l12 by (intro mod_diff_cong mod_mult_cong) (auto simp: mod_pos_pos_trivial)
  hence dvd1: "k dvd t1 * u2 - t2 * u1" by (simp add: mod_eq_0_iff_dvd)

  have "k\<^sup>2 dvd k\<^sup>2 + D * (t1 * u2 - t2 * u1)\<^sup>2"
    using dvd1 by (intro dvd_add) auto
  also from eq have "\<dots> = (t1 * t2 - D * u1 * u2)\<^sup>2"
    by (simp add: algebra_simps)
  finally have dvd2: "k dvd t1 * t2 - D * u1 * u2"
    by simp

  note eq
  also from dvd2 have "t1 * t2 - D * u1 * u2 = k * x"
    by (simp add: x_def)
  also from dvd1 have "t1 * u2 - t2 * u1 = k * y"
    by (simp add: y_def)
  also have "(k * x)\<^sup>2 - D * (k * y)\<^sup>2 = k\<^sup>2 * (x\<^sup>2 - D * y\<^sup>2)"
    by (simp add: power_mult_distrib algebra_simps)
  finally have eq': "x\<^sup>2 - D * y\<^sup>2 = 1"
    using k_nz by simp
  hence "x\<^sup>2 = 1 + D * y\<^sup>2" by simp
  also have "x\<^sup>2 = int (nat \<bar>x\<bar> ^ 2)" by simp
  also have "1 + D * y\<^sup>2 = int (1 + D * nat \<bar>y\<bar> ^ 2)" by simp
  also note of_nat_eq_iff
  finally have eq'': "(nat \<bar>x\<bar>)\<^sup>2 = 1 + D * (nat \<bar>y\<bar>)\<^sup>2" .

  have "t1 * u2 \<noteq> t2 * u1"
  proof
    assume *: "t1 * u2 = t2 * u1"
    hence "\<bar>t1\<bar> * \<bar>u2\<bar> = \<bar>t2\<bar> * \<bar>u1\<bar>" by (simp only: abs_mult [symmetric])
    moreover from S' have "coprime u1 t1" "coprime u2 t2"
      by (auto simp: S'_def S_def)
    ultimately have eq: "\<bar>t1\<bar> = \<bar>t2\<bar> \<and> u1 = u2"
      by (subst (asm) coprime_crossproduct_int) (auto simp: S'_def S_def gcd.commute coprime_commute)
    moreover from S' have "u1 \<noteq> 0" "u2 \<noteq> 0" by (auto simp: S'_def S_def)
    ultimately have "t1 = t2" using * by auto
    with eq and neq show False by auto
  qed
  with dvd1 have "y \<noteq> 0"
    by (auto simp add: y_def dvd_div_eq_0_iff)
  hence "nat \<bar>y\<bar> \<noteq> 0" by auto
  with eq'' show "\<exists>x y. y \<noteq> 0 \<and> x\<^sup>2 = 1 + D * y\<^sup>2" by blast
qed


subsection \<open>Definition of solutions\<close>

text \<open>
  We define some abbreviations for the concepts of a solution and a non-trivial solution.
\<close>
definition solution :: "('a \<times> 'a :: comm_semiring_1) \<Rightarrow> bool" where
  "solution = (\<lambda>(a, b). a\<^sup>2 = 1 + of_nat D * b\<^sup>2)"

definition nontriv_solution :: "('a \<times> 'a :: comm_semiring_1) \<Rightarrow> bool" where
  "nontriv_solution = (\<lambda>(a, b). (a, b) \<noteq> (1, 0) \<and> a\<^sup>2 = 1 + of_nat D * b\<^sup>2)"

lemma nontriv_solution_altdef: "nontriv_solution z \<longleftrightarrow> solution z \<and> z \<noteq> (1, 0)"
  by (auto simp: solution_def nontriv_solution_def)

lemma solution_trivial_nat [simp, intro]: "solution (Suc 0, 0)"
  by (simp add: solution_def)

lemma solution_trivial [simp, intro]: "solution (1, 0)"
  by (simp add: solution_def)

lemma solution_uminus_left [simp]: "solution (-x, y :: 'a :: comm_ring_1) \<longleftrightarrow> solution (x, y)"
  by (simp add: solution_def)

lemma solution_uminus_right [simp]: "solution (x, -y :: 'a :: comm_ring_1) \<longleftrightarrow> solution (x, y)"
  by (simp add: solution_def)

lemma solution_0_snd_nat_iff [simp]: "solution (a :: nat, 0) \<longleftrightarrow> a = 1"
  by (auto simp: solution_def)

lemma solution_0_snd_iff [simp]: "solution (a :: 'a :: idom, 0) \<longleftrightarrow> a \<in> {1, -1}"
  by (auto simp: solution_def power2_eq_1_iff)

lemma no_solution_0_fst_nat [simp]: "\<not>solution (0, b :: nat)"
  by (auto simp: solution_def)

lemma no_solution_0_fst_int [simp]: "\<not>solution (0, b :: int)"
proof -
  have "1 + int D * b\<^sup>2 > 0" by (intro add_pos_nonneg) auto
  thus ?thesis by (auto simp add: solution_def)
qed

lemma solution_of_nat_of_nat [simp]:
  "solution (of_nat a, of_nat b :: 'a :: {comm_ring_1, ring_char_0}) \<longleftrightarrow> solution (a, b)"
  by (simp only: solution_def prod.case of_nat_power [symmetric]
                 of_nat_1 [symmetric, where ?'a = 'a] of_nat_add [symmetric]
                 of_nat_mult [symmetric] of_nat_eq_iff of_nat_id)

lemma solution_of_nat_of_nat' [simp]:
  "solution (case z of (a, b) \<Rightarrow> (of_nat a, of_nat b :: 'a :: {comm_ring_1, ring_char_0})) \<longleftrightarrow>
     solution z"
  by (auto simp: case_prod_unfold)

lemma solution_nat_abs_nat_abs [simp]:
  "solution (nat \<bar>x\<bar>, nat \<bar>y\<bar>) \<longleftrightarrow> solution (x, y)"
proof -
  define x' and y' where "x' = nat \<bar>x\<bar>" and "y' = nat \<bar>y\<bar>"
  have x: "x = sgn x * x'" and y: "y = sgn y * y'"
    by (auto simp: x'_def y'_def sgn_if)
  have [simp]: "x = 0 \<longleftrightarrow> x' = 0" "y = 0 \<longleftrightarrow> y' = 0"
    by (auto simp: x'_def y'_def)
  show "solution (x', y') \<longleftrightarrow> solution (x, y)"
    by (subst x, subst y) (auto simp: sgn_if)
qed

lemma nontriv_solution_of_nat_of_nat [simp]:
  "nontriv_solution (of_nat a, of_nat b :: 'a :: {comm_ring_1, ring_char_0}) \<longleftrightarrow> nontriv_solution (a, b)"
  by (auto simp: nontriv_solution_altdef)

lemma nontriv_solution_of_nat_of_nat' [simp]:
  "nontriv_solution (case z of (a, b) \<Rightarrow> (of_nat a, of_nat b :: 'a :: {comm_ring_1, ring_char_0})) \<longleftrightarrow>
     nontriv_solution z"
  by (auto simp: case_prod_unfold)

lemma nontriv_solution_imp_solution [dest]: "nontriv_solution z \<Longrightarrow> solution z"
  by (auto simp: nontriv_solution_altdef)


subsection \<open>The Pell valuation function\<close>

text \<open>
  Solutions \<open>(x,y)\<close> have an interesting correspondence to the ring $\mathbb{Z}[\sqrt{D}]$ via
  the map $(x,y) \mapsto x + y \sqrt{D}$. We call this map the \<^emph>\<open>Pell valuation function\<close>.
  It is obvious that this map is injective, since $\sqrt{D}$ is irrational.
\<close>
definition pell_valuation :: "int \<times> int \<Rightarrow> real" where
  "pell_valuation = (\<lambda>(a,b). a + b * sqrt D)"

lemma pell_valuation_nonneg [simp]: "fst z \<ge> 0 \<Longrightarrow> snd z \<ge> 0 \<Longrightarrow> pell_valuation z \<ge> 0"
  by (auto simp: pell_valuation_def case_prod_unfold)

lemma pell_valuation_uminus_uminus [simp]: "pell_valuation (-x, -y) = -pell_valuation (x, y)"
  by (simp add: pell_valuation_def)

lemma pell_valuation_eq_iff [simp]:
  "pell_valuation z1 = pell_valuation z2 \<longleftrightarrow> z1 = z2"
proof
  assume *: "pell_valuation z1 = pell_valuation z2"
  obtain a b where [simp]: "z1 = (a, b)" by (cases z1)
  obtain u v where [simp]: "z2 = (u, v)" by (cases z2)
  have "b = v"
  proof (rule ccontr)
    assume "b \<noteq> v"
    with * have "sqrt D = (u - a) / (b - v)"
      by (simp add: field_simps pell_valuation_def)
    also have "\<dots> \<in> \<rat>" by auto
    finally show False using irrat_sqrt_nonsquare nonsquare_D by blast
  qed
  moreover from this and * have "a = u"
    by (simp add: pell_valuation_def)
  ultimately show "z1 = z2" by simp
qed auto


subsection \<open>Linear ordering of solutions\<close>

text \<open>
  Next, we show that solutions are linearly ordered w.\,r.\,t.\ the pointwise order on products.
  This means thatfor two different solutions \<open>(a, b)\<close> and \<open>(x, y)\<close>, we always either have
  \<open>a < x\<close> and \<open>b < y\<close> or \<open>a > x\<close> and \<open>b > y\<close>.
\<close>

lemma solutions_linorder:
  fixes a b x y :: nat
  assumes "solution (a, b)" "solution (x, y)"
  shows   "a \<le> x \<and> b \<le> y \<or> a \<ge> x \<and> b \<ge> y"
proof -
  have "b \<le> y" if "a \<le> x" "solution (a, b)" "solution (x, y)" for a b x y :: nat
  proof -
    from that have "a ^ 2 \<le> x ^ 2" by (intro power_mono) auto
    with that and D_gt_1 have "b\<^sup>2 \<le> y\<^sup>2"
      by (simp add: solution_def)
    thus "b \<le> y"
      by (simp add: power2_nat_le_eq_le)
  qed
  from this[of a x b y] and this[of x a y b] and assms show ?thesis
    by (cases "a \<le> x") auto
qed

lemma solutions_linorder_strict:
  fixes a b x y :: nat
  assumes "solution (a, b)" "solution (x, y)"
  shows   "(a, b) = (x, y) \<or> a < x \<and> b < y \<or> a > x \<and> b > y"
proof -
  have "b = y" if "a = x"
    using that assms and D_gt_1 by (simp add: solution_def)
  moreover have "a = x" if "b = y"
  proof -
    from that and assms have "a\<^sup>2 = Suc (D * y\<^sup>2)"
      by (simp add: solution_def)
    also from that and assms have "\<dots> = x\<^sup>2"
      by (simp add: solution_def)
    finally show "a = x" by simp
  qed
  ultimately have [simp]: "a = x \<longleftrightarrow> b = y" ..
  show ?thesis using solutions_linorder[OF assms]
    by (cases a x rule: linorder_cases; cases b y rule: linorder_cases) simp_all
qed

lemma solutions_le_iff_pell_valuation_le:
  fixes a b x y :: nat
  assumes "solution (a, b)" "solution (x, y)"
  shows   "a \<le> x \<and> b \<le> y \<longleftrightarrow> pell_valuation (a, b) \<le> pell_valuation (x, y)"
proof
  assume "a \<le> x \<and> b \<le> y"
  thus "pell_valuation (a, b) \<le> pell_valuation (x, y)"
    unfolding pell_valuation_def prod.case using D_gt_1
    by (intro add_mono mult_right_mono) auto
next
  assume *: "pell_valuation (a, b) \<le> pell_valuation (x, y)"
  from assms have "a \<le> x \<and> b \<le> y \<or> x \<le> a \<and> y \<le> b"
    by (rule solutions_linorder)
  thus "a \<le> x \<and> b \<le> y"
  proof
    assume "x \<le> a \<and> y \<le> b"
    hence "pell_valuation (a, b) \<ge> pell_valuation (x, y)"
      unfolding pell_valuation_def prod.case using D_gt_1
      by (intro add_mono mult_right_mono) auto
    with * have "pell_valuation (a, b) = pell_valuation (x, y)" by linarith
    hence "(a, b) = (x, y)" by simp
    thus "a \<le> x \<and> b \<le> y" by simp
  qed auto
qed

lemma solutions_less_iff_pell_valuation_less:
  fixes a b x y :: nat
  assumes "solution (a, b)" "solution (x, y)"
  shows   "a < x \<and> b < y \<longleftrightarrow> pell_valuation (a, b) < pell_valuation (x, y)"
proof
  assume "a < x \<and> b < y"
  thus "pell_valuation (a, b) < pell_valuation (x, y)"
    unfolding pell_valuation_def prod.case using D_gt_1
    by (intro add_strict_mono mult_strict_right_mono) auto
next
  assume *: "pell_valuation (a, b) < pell_valuation (x, y)"
  from assms have "(a, b) = (x, y) \<or> a < x \<and> b < y \<or> x < a \<and> y < b"
    by (rule solutions_linorder_strict)
  thus "a < x \<and> b < y"
  proof (elim disjE)
    assume "x < a \<and> y < b"
    hence "pell_valuation (a, b) > pell_valuation (x, y)"
      unfolding pell_valuation_def prod.case using D_gt_1
      by (intro add_strict_mono mult_strict_right_mono) auto
    with * have False by linarith
    thus ?thesis ..
  qed (insert *, auto)
qed


subsection \<open>The fundamental solution\<close>

text \<open>
  The \<^emph>\<open>fundamental solution\<close> is the non-trivial solution \<open>(x, y)\<close> with non-negative \<open>x\<close> and \<open>y\<close>
  for which the Pell valuation $x + y\sqrt{D}$ is minimal, or, equivalently, for which \<open>x\<close> and \<open>y\<close>
  are minimal.
\<close>
definition fund_sol :: "nat \<times> nat" where
  "fund_sol = (THE z::nat\<times>nat. is_arg_min (pell_valuation :: nat \<times> nat \<Rightarrow> real) nontriv_solution z)"

text \<open>
  The well-definedness of this follows from the injectivity of the Pell valuation and the fact
  that smaller Pell valuation of a solution is smaller than that of another iff the components
  are both smaller.
\<close>
theorem fund_sol_is_arg_min:
  "is_arg_min (pell_valuation :: nat \<times> nat \<Rightarrow> real) nontriv_solution fund_sol"
  unfolding fund_sol_def
proof (rule theI')
  show "\<exists>!z::nat\<times>nat. is_arg_min (pell_valuation :: nat \<times> nat \<Rightarrow> real) nontriv_solution z"
  proof (rule ex_ex1I)
    fix z1 z2 :: "nat \<times> nat"
    assume "is_arg_min (pell_valuation :: nat \<times> nat \<Rightarrow> real) nontriv_solution z1"
           "is_arg_min (pell_valuation :: nat \<times> nat \<Rightarrow> real) nontriv_solution z2"
    hence "pell_valuation z1 = pell_valuation z2"
      by (cases z1, cases z2, intro antisym) (auto simp: is_arg_min_def not_less)
    thus "z1 = z2" by (auto split: prod.splits)
  next
    define y where "y = (LEAST y. y > 0 \<and> is_square (1 + D * y\<^sup>2))"
    have "\<exists>y>0. is_square (1 + D * y\<^sup>2)"
      using pell_solution_exists by (auto simp: eq_commute[of _ "Suc _"])
    hence y: "y > 0 \<and> is_square (1 + D * y\<^sup>2)"
      unfolding y_def by (rule LeastI_ex)
    have y_le: "y \<le> y'" if "y' > 0" "is_square (1 + D * y'\<^sup>2)" for y'
      unfolding y_def using that by (intro Least_le) auto
    from y obtain x where x: "x\<^sup>2 = 1 + D * y\<^sup>2"
      by (auto elim: is_nth_powerE)
    with y have "nontriv_solution (x, y)"
      by (auto simp: nontriv_solution_def)

    have "is_arg_min (pell_valuation :: nat \<times> nat \<Rightarrow> real) nontriv_solution (x, y)"
      unfolding is_arg_min_linorder
    proof safe
      fix a b :: nat
      assume *: "nontriv_solution (a, b)"
      hence "b > 0" and "Suc (D * b\<^sup>2) = a\<^sup>2"
        by (auto simp: nontriv_solution_def intro!: Nat.gr0I)
      hence "is_square (1 + D * b\<^sup>2)"
        by (auto simp: nontriv_solution_def)
      from \<open>b > 0\<close> and this have "y \<le> b" by (rule y_le)
      with \<open>nontriv_solution (x, y)\<close> and * have "x \<le> a"
        using solutions_linorder_strict[of x y a b] by (auto simp: nontriv_solution_altdef)
      with \<open>y \<le> b\<close> show "pell_valuation (int x, int y) \<le> pell_valuation (int a, int b)"
        unfolding pell_valuation_def prod.case by (intro add_mono mult_right_mono) auto
    qed fact+
    thus "\<exists>z. is_arg_min (pell_valuation :: nat \<times> nat \<Rightarrow> real) nontriv_solution z" ..
  qed
qed

corollary
      fund_sol_is_nontriv_solution: "nontriv_solution fund_sol"
  and fund_sol_minimal:
        "nontriv_solution (a, b) \<Longrightarrow> pell_valuation fund_sol \<le> pell_valuation (int a, int b)"
  and fund_sol_minimal':
        "nontriv_solution (z :: nat \<times> nat) \<Longrightarrow> pell_valuation fund_sol \<le> pell_valuation z"
  using fund_sol_is_arg_min by (auto simp: is_arg_min_linorder case_prod_unfold)

lemma fund_sol_minimal'':
  assumes "nontriv_solution z"
  shows   "fst fund_sol \<le> fst z" "snd fund_sol \<le> snd z"
proof -
  have "pell_valuation (fst fund_sol, snd fund_sol) \<le> pell_valuation (fst z, snd z)"
    using fund_sol_minimal'[OF assms] by (simp add: case_prod_unfold)
  hence "fst fund_sol \<le> fst z \<and> snd fund_sol \<le> snd z"
    using assms fund_sol_is_nontriv_solution
    by (subst solutions_le_iff_pell_valuation_le) (auto simp: case_prod_unfold)
  thus "fst fund_sol \<le> fst z" "snd fund_sol \<le> snd z" by blast+
qed


subsection \<open>Group structure on solutions\<close>

text \<open>
  As was mentioned already, the Pell valuation function provides an injective map from
  solutions of Pell's equation into the ring $\mathbb{Z}[\sqrt{D}]$. We shall see now that
  the solutions are actually a subgroup of the multiplicative group of $\mathbb{Z}[\sqrt{D}]$ via
  the valuation function as a homomorphism:

    \<^item> The trivial solution \<open>(1, 0)\<close> has valuation \<open>1\<close>, which is the neutral element of
      $\mathbb{Z}[\sqrt{D}]^*$

    \<^item> Multiplication of two solutions $a + b \sqrt D$ and
      $x + y \sqrt D$ leads to $\bar x + \bar y\sqrt D$
      with $\bar x = xa + ybD$ and $\bar y = xb + ya$, which is again a solution.

    \<^item> The conjugate \<open>(x, -y)\<close> of a solution \<open>(x, y)\<close> is an inverse element to this
      multiplication operation, since $(x + y \sqrt D) (x - y \sqrt D) = 1$.
\<close>
definition pell_mul :: "('a :: comm_semiring_1 \<times> 'a) \<Rightarrow> ('a \<times> 'a) \<Rightarrow> ('a \<times> 'a)" where
  "pell_mul = (\<lambda>(a,b) (x,y). (x * a + y * b * of_nat D, x * b + y * a))"

definition pell_cnj :: "('a :: comm_ring_1 \<times> 'a) \<Rightarrow> 'a \<times> 'a" where
  "pell_cnj = (\<lambda>(a,b). (a, -b))"

lemma pell_cnj_snd_0 [simp]: "snd z = 0 \<Longrightarrow> pell_cnj z = z"
  by (cases z) (simp_all add: pell_cnj_def)

lemma pell_mul_commutes: "pell_mul z1 z2 = pell_mul z2 z1"
  by (auto simp: pell_mul_def algebra_simps case_prod_unfold)

lemma pell_mul_assoc: "pell_mul z1 (pell_mul z2 z3) = pell_mul (pell_mul z1 z2) z3"
  by (auto simp: pell_mul_def algebra_simps case_prod_unfold)

lemma pell_mul_trivial_left [simp]: "pell_mul (1, 0) z = z"
  by (auto simp: pell_mul_def algebra_simps case_prod_unfold)

lemma pell_mul_trivial_right [simp]: "pell_mul z (1, 0) = z"
  by (auto simp: pell_mul_def algebra_simps case_prod_unfold)

lemma pell_mul_trivial_left_nat [simp]: "pell_mul (Suc 0, 0) z = z"
  by (auto simp: pell_mul_def algebra_simps case_prod_unfold)

lemma pell_mul_trivial_right_nat [simp]: "pell_mul z (Suc 0, 0) = z"
  by (auto simp: pell_mul_def algebra_simps case_prod_unfold)

definition pell_power :: "('a :: comm_semiring_1 \<times> 'a) \<Rightarrow> nat \<Rightarrow> ('a \<times> 'a)" where
  "pell_power z n = ((\<lambda>z'. pell_mul z' z) ^^ n) (1, 0)"

lemma pell_power_0 [simp]: "pell_power z 0 = (1, 0)"
  by (simp add: pell_power_def)

lemma pell_power_one [simp]: "pell_power (1, 0) n = (1, 0)"
  by (induction n) (auto simp: pell_power_def)

lemma pell_power_one_right [simp]: "pell_power z 1 = z"
  by (simp add: pell_power_def)

lemma pell_power_Suc: "pell_power z (Suc n) = pell_mul z (pell_power z n)"
  by (simp add: pell_power_def pell_mul_commutes)

lemma pell_power_add: "pell_power z (m + n) = pell_mul (pell_power z m) (pell_power z n)"
  by (induction m arbitrary: z )
     (simp_all add: funpow_add o_def pell_power_Suc pell_mul_assoc)

lemma pell_valuation_mult [simp]:
  "pell_valuation (pell_mul z1 z2) = pell_valuation z1 * pell_valuation z2"
  by (simp add: pell_valuation_def pell_mul_def case_prod_unfold algebra_simps)

lemma pell_valuation_mult_nat [simp]:
  "pell_valuation (case pell_mul z1 z2 of (a, b) \<Rightarrow> (int a, int b)) =
     pell_valuation z1 * pell_valuation z2"
  by (simp add: pell_valuation_def pell_mul_def case_prod_unfold algebra_simps)

lemma pell_valuation_trivial [simp]: "pell_valuation (1, 0) = 1"
  by (simp add: pell_valuation_def)

lemma pell_valuation_trivial_nat [simp]: "pell_valuation (Suc 0, 0) = 1"
  by (simp add: pell_valuation_def)

lemma pell_valuation_cnj: "pell_valuation (pell_cnj z) = fst z - snd z * sqrt D"
  by (simp add: pell_valuation_def pell_cnj_def case_prod_unfold)

lemma pell_valuation_snd_0 [simp]: "pell_valuation (a, 0) = of_int a"
  by (simp add: pell_valuation_def)

lemma pell_valuation_0_iff [simp]: "pell_valuation z = 0 \<longleftrightarrow> z = (0, 0)"
proof
  assume *: "pell_valuation z = 0"
  have "snd z = 0"
  proof (rule ccontr)
    assume "snd z \<noteq> 0"
    with * have "sqrt D = -fst z / snd z"
      by (simp add: pell_valuation_def case_prod_unfold field_simps)
    also have "\<dots> \<in> \<rat>" by auto
    finally show False using nonsquare_D irrat_sqrt_nonsquare by blast
  qed
  with * have "fst z = 0" by (simp add: pell_valuation_def case_prod_unfold)
  with \<open>snd z = 0\<close> show "z = (0, 0)" by (cases z) auto
qed (auto simp: pell_valuation_def)

lemma pell_valuation_solution_pos_nat:
  fixes z :: "nat \<times> nat"
  assumes "solution z"
  shows   "pell_valuation z > 0"
proof -
  from assms have "z \<noteq> (0, 0)" by (intro notI) auto
  hence "pell_valuation z \<noteq> 0" by (auto split: prod.splits)
  moreover have "pell_valuation z \<ge> 0" by (intro pell_valuation_nonneg) (auto split: prod.splits)
  ultimately show ?thesis by linarith
qed

lemma
  assumes "solution z"
  shows   pell_mul_cnj_right: "pell_mul z (pell_cnj z) = (1, 0)"
    and   pell_mul_cnj_left: "pell_mul (pell_cnj z) z = (1, 0)"
  using assms by (auto simp: pell_mul_def pell_cnj_def solution_def power2_eq_square)

lemma pell_valuation_cnj_solution:
  fixes z :: "nat \<times> nat"
  assumes "solution z"
  shows   "pell_valuation (pell_cnj z) = 1 / pell_valuation z"
proof -
  have "pell_valuation (pell_cnj z) * pell_valuation z = pell_valuation (pell_mul (pell_cnj z) z)"
    by simp
  also from assms have "pell_mul (pell_cnj z) z = (1, 0)"
    by (subst pell_mul_cnj_left) (auto simp: case_prod_unfold)
  finally show ?thesis using pell_valuation_solution_pos_nat[OF assms]
    by (auto simp: divide_simps)
qed

lemma pell_valuation_power [simp]: "pell_valuation (pell_power z n) = pell_valuation z ^ n"
  by (induction n) (simp_all add: pell_power_Suc)

lemma pell_valuation_power_nat [simp]:
  "pell_valuation (case pell_power z n of (a, b) \<Rightarrow> (int a, int b)) = pell_valuation z ^ n"
  by (induction n) (simp_all add: pell_power_Suc)

lemma pell_valuation_fund_sol_ge_2: "pell_valuation fund_sol \<ge> 2"
proof -
  obtain x y where [simp]: "fund_sol = (x, y)" by (cases fund_sol)
  from fund_sol_is_nontriv_solution have eq: "x\<^sup>2 = 1 + D * y\<^sup>2"
    by (auto simp: nontriv_solution_def)

  consider "y > 0" | "y = 0" "x \<noteq> 1"
    using fund_sol_is_nontriv_solution by (force simp: nontriv_solution_def)
  thus ?thesis
  proof cases
    assume "y > 0"
    hence "1 + 1 * 1 \<le> 1 + D * y\<^sup>2"
      using D_pos by (intro add_mono mult_mono) auto
    also from eq have "\<dots> = x\<^sup>2" ..
    finally have "x\<^sup>2 > 1\<^sup>2" by simp
    hence "x > 1" by (rule power2_less_imp_less) auto
    with \<open>y > 0\<close> have "x + y * sqrt D \<ge> 2 + 1 * 1"
      using D_pos by (intro add_mono mult_mono) auto
    thus ?thesis by (simp add: pell_valuation_def)
  next
    assume [simp]: "y = 0" and "x \<noteq> 1"
    with eq have "x \<noteq> 0" by (intro notI) auto
    with \<open>x \<noteq> 1\<close> have "x \<ge> 2" by simp
    thus ?thesis by (auto simp: pell_valuation_def)
  qed
qed


lemma solution_pell_mul [intro]:
  assumes "solution z1" "solution z2"
  shows   "solution (pell_mul z1 z2)"
proof -
  obtain a b where [simp]: "z1 = (a, b)" by (cases z1)
  obtain c d where [simp]: "z2 = (c, d)" by (cases z2)
  from assms show ?thesis
    by (simp add: solution_def pell_mul_def case_prod_unfold power2_eq_square algebra_simps)
qed

lemma solution_pell_cnj [intro]:
  assumes "solution z"
  shows   "solution (pell_cnj z)"
  using assms by (auto simp: solution_def pell_cnj_def)

lemma solution_pell_power [simp, intro]: "solution z \<Longrightarrow> solution (pell_power z n)"
  by (induction n) (auto simp: pell_power_Suc)

lemma pell_mul_eq_trivial_nat_iff:
  "pell_mul z1 z2 = (Suc 0, 0) \<longleftrightarrow> z1 = (Suc 0, 0) \<and> z2 = (Suc 0, 0)"
  using D_gt_1 by (cases z1; cases z2) (auto simp: pell_mul_def)

lemma nontriv_solution_pell_nat_mul1:
  "solution (z1 :: nat \<times> nat) \<Longrightarrow> nontriv_solution z2 \<Longrightarrow> nontriv_solution (pell_mul z1 z2)"
  by (auto simp: nontriv_solution_altdef pell_mul_eq_trivial_nat_iff)

lemma nontriv_solution_pell_nat_mul2:
  "nontriv_solution (z1 :: nat \<times> nat) \<Longrightarrow> solution z2 \<Longrightarrow> nontriv_solution (pell_mul z1 z2)"
  by (auto simp: nontriv_solution_altdef pell_mul_eq_trivial_nat_iff)

lemma nontriv_solution_power_nat [intro]:
  assumes "nontriv_solution (z :: nat \<times> nat)" "n > 0"
  shows   "nontriv_solution (pell_power z n)"
proof -
  have "nontriv_solution (pell_power z n) \<or> n = 0"
    by (induction n)
       (insert assms(1), auto intro: nontriv_solution_pell_nat_mul1 simp: pell_power_Suc)
  with assms(2) show ?thesis by auto
qed


subsection \<open>The different regions of the valuation function\<close>

text \<open>
  Next, we shall explore what happens to the valuation function for solutions \<open>(x, y)\<close> for
  different signs of \<open>x\<close> and \<open>y\<close>:

    \<^item> If \<open>x > 0\<close> and \<open>y > 0\<close>, we have  $x + y \sqrt D > 1$.

    \<^item> If \<open>x > 0\<close> and \<open>y < 0\<close>, we have $0 < x + y \sqrt D < 1$.

    \<^item> If \<open>x < 0\<close> and \<open>y > 0\<close>, we have $-1 < x + y \sqrt D < 0$.

    \<^item> If \<open>x < 0\<close> and \<open>y < 0\<close>, we have $x + y \sqrt D < -1$.

  In particular, this means that we can deduce the sign of \<open>x\<close> and \<open>y\<close> if we know in
  which of these four regions the valuation lies.
\<close>
lemma
  assumes "x > 0" "y > 0" "solution (x, y)"
  shows   pell_valuation_pos_pos: "pell_valuation (x, y) > 1"
    and   pell_valuation_pos_neg_aux: "pell_valuation (x, -y) \<in> {0<..<1}"
proof -
  from D_gt_1 assms have "x + y * sqrt D \<ge> 1 + 1 * 1"
    by (intro add_mono mult_mono) auto
  hence gt_1: "x + y * sqrt D > 1" by simp
  thus "pell_valuation (x, y) > 1" by (simp add: pell_valuation_def)

  from assms have "1 = x^2 - D * y^2" by (simp add: solution_def)
  also have "of_int \<dots> = (x - y * sqrt D) * (x + y * sqrt D)"
    by (simp add: field_simps power2_eq_square)
  finally have eq: "(x - y * sqrt D) = 1 / (x + y * sqrt D)"
    using gt_1 by (simp add: field_simps)

  note eq
  also from gt_1 have "1 / (x + y * sqrt D) < 1 / 1"
    by (intro divide_strict_left_mono) auto
  finally have "x - y * sqrt D < 1" by simp

  note eq
  also from gt_1 have "1 / (x + y * sqrt D) > 0"
    by (intro divide_pos_pos) auto
  finally have "x - y * sqrt D > 0" .
  with \<open>x - y * sqrt D < 1\<close> show "pell_valuation (x, -y) \<in> {0<..<1}"
    by (simp add: pell_valuation_def)
qed

lemma pell_valuation_pos_neg:
  assumes "x > 0" "y < 0" "solution (x, y)"
  shows   "pell_valuation (x, y) \<in> {0<..<1}"
  using pell_valuation_pos_neg_aux[of x "-y"] assms by simp

lemma pell_valuation_neg_neg:
  assumes "x < 0" "y < 0" "solution (x, y)"
  shows   "pell_valuation (x, y) < -1"
  using pell_valuation_pos_pos[of "-x" "-y"] assms by simp

lemma pell_valuation_neg_pos:
  assumes "x < 0" "y > 0" "solution (x, y)"
  shows   "pell_valuation (x, y) \<in> {-1<..<0}"
  using pell_valuation_pos_neg[of "-x" "-y"] assms by simp

lemma pell_valuation_solution_gt1D:
  assumes "solution z" "pell_valuation z > 1"
  shows   "fst z > 0 \<and> snd z > 0"
  using pell_valuation_pos_pos[of "fst z" "snd z"] pell_valuation_pos_neg[of "fst z" "snd z"]
        pell_valuation_neg_pos[of "fst z" "snd z"] pell_valuation_neg_neg[of "fst z" "snd z"]
        assms
  by (cases "fst z" "0 :: int" rule: linorder_cases;
      cases "snd z" "0 :: int" rule: linorder_cases;
      cases z) auto


subsection \<open>Generating property of the fundamental solution\<close>

text \<open>
  We now show that the fundamental solution generates the set of the (non-negative) solutions
  in the sense that each solution is a power of the fundamental solution. Combined with the
  symmetry property that \<open>(x,y)\<close> is a solution iff \<open>(\<plusminus>x, \<plusminus>y)\<close> is a solution, this gives us
  a complete characterisation of all solutions of Pell's equation.
\<close>
definition nth_solution :: "nat \<Rightarrow> nat \<times> nat" where
  "nth_solution n = pell_power fund_sol n"

lemma pell_valuation_nth_solution [simp]:
  "pell_valuation (nth_solution n) = pell_valuation fund_sol ^ n"
  by (simp add: nth_solution_def)

theorem nth_solution_inj: "inj nth_solution"
proof
  fix m n :: nat
  assume "nth_solution m = nth_solution n"
  hence "pell_valuation (nth_solution m) = pell_valuation (nth_solution n)"
    by (simp only: )
  also have "pell_valuation (nth_solution m) = pell_valuation fund_sol ^ m"
    by simp
  also have "pell_valuation (nth_solution n) = pell_valuation fund_sol ^ n"
    by simp
  finally show "m = n"
    using pell_valuation_fund_sol_ge_2 by (subst (asm) power_inject_exp) auto
qed

theorem nth_solution_sound [intro]: "solution (nth_solution n)"
  using fund_sol_is_nontriv_solution by (auto simp: nth_solution_def)

theorem nth_solution_sound' [intro]: "n > 0 \<Longrightarrow> nontriv_solution (nth_solution n)"
  using fund_sol_is_nontriv_solution by (auto simp: nth_solution_def)

theorem nth_solution_complete:
  fixes z :: "nat \<times> nat"
  assumes "solution z"
  shows   "z \<in> range nth_solution"
proof (cases "z = (1, 0)")
  case True
  hence "z = nth_solution 0" by (simp add: nth_solution_def)
  thus ?thesis by auto
next
  case False
  with assms have "nontriv_solution z" by (auto simp: nontriv_solution_altdef)
  show ?thesis
  proof (rule ccontr)
    assume "\<not>?thesis"
    hence *: "pell_power fund_sol n \<noteq> z" for n unfolding nth_solution_def by blast

    define u where "u = pell_valuation fund_sol"
    define v where "v = pell_valuation z"
    define n where "n = nat \<lfloor>log u v\<rfloor>"
    have u_ge_2: "u \<ge> 2" using pell_valuation_fund_sol_ge_2 by (auto simp: u_def)
    have v_pos: "v > 0" unfolding v_def using assms
      by (intro pell_valuation_solution_pos_nat) auto
    have u_le_v: "u \<le> v" unfolding u_def v_def by (rule fund_sol_minimal') fact

    have u_power_neq_v: "u ^ k \<noteq> v" for k
    proof
      assume "u ^ k = v"
      also have "u ^ k = pell_valuation (pell_power fund_sol k)"
        by (simp add: u_def)
      also have "\<dots> = v \<longleftrightarrow> pell_power fund_sol k = z"
        unfolding v_def by (subst pell_valuation_eq_iff) (auto split: prod.splits)
      finally show False using * by blast
    qed

    from u_le_v v_pos u_ge_2 have log_ge_1: "log u v \<ge> 1"
      by (subst one_le_log_cancel_iff) auto

    define z' where "z' = pell_mul z (pell_power (pell_cnj fund_sol) n)"
    define x and y where "x = nat \<bar>fst z'\<bar>" and "y = nat \<bar>snd z'\<bar>"
    have "solution z'" using assms fund_sol_is_nontriv_solution unfolding z'_def
      by (intro solution_pell_mul solution_pell_power solution_pell_cnj) (auto simp: case_prod_unfold)

    have "u ^ n < v"
    proof -
      from u_ge_2 have "u ^ n = u powr real n" by (subst powr_realpow) auto
      also have "\<dots> \<le> u powr log u v" using u_ge_2 log_ge_1
        by (intro powr_mono) (auto simp: n_def)
      also have "\<dots> = v"
        using u_ge_2 v_pos by (subst powr_log_cancel) auto
      finally have "u ^ n \<le> v" .
      with u_power_neq_v[of n] show ?thesis by linarith
    qed
    moreover have "v < u ^ Suc n"
    proof -
      have "v = u powr log u v"
        using u_ge_2 v_pos by (subst powr_log_cancel) auto
      also have "log u v \<le> 1 + real_of_int \<lfloor>log u v\<rfloor>" by linarith
      hence "u powr log u v \<le> u powr real (Suc n)" using u_ge_2 log_ge_1
        by (intro powr_mono) (auto simp: n_def)
      also have "\<dots> = u ^ Suc n" using u_ge_2 by (subst powr_realpow) auto
      finally have "u ^ Suc n \<ge> v" .
      with u_power_neq_v[of "Suc n"] show ?thesis by linarith
    qed
    ultimately have "v / u ^ n \<in> {1<..<u}"
      using u_ge_2 by (simp add: field_simps)
    also have "v / u ^ n = pell_valuation z'"
      using fund_sol_is_nontriv_solution
      by (auto simp add: z'_def u_def v_def pell_valuation_cnj_solution field_simps)
    finally have val: "pell_valuation z' \<in> {1<..<u}" .

    from val and \<open>solution z'\<close> have "nontriv_solution z'"
      by (auto simp: nontriv_solution_altdef)
    from \<open>solution z'\<close> and val have "fst z' > 0 \<and> snd z' > 0"
      by (intro pell_valuation_solution_gt1D) auto

    hence [simp]: "z' = (int x, int y)"
      by (auto simp: x_def y_def)

    from \<open>nontriv_solution z'\<close> have "pell_valuation (int x, int y) \<ge> u"
      unfolding u_def by (intro fund_sol_minimal) auto
    with val show False by simp
  qed
qed

corollary solution_iff_nth_solution:
  fixes z :: "nat \<times> nat"
  shows "solution z \<longleftrightarrow> z \<in> range nth_solution"
  using nth_solution_sound nth_solution_complete by blast

corollary solution_iff_nth_solution':
  fixes z :: "int \<times> int"
  shows "solution (a, b) \<longleftrightarrow> (nat \<bar>a\<bar>, nat \<bar>b\<bar>) \<in> range nth_solution"
proof -
  have "solution (a, b) \<longleftrightarrow> solution (nat \<bar>a\<bar>, nat \<bar>b\<bar>)"
    by simp
  also have "\<dots> \<longleftrightarrow> (nat \<bar>a\<bar>, nat \<bar>b\<bar>) \<in> range nth_solution"
    by (rule solution_iff_nth_solution)
  finally show ?thesis .
qed

corollary infinite_solutions: "infinite {z :: nat \<times> nat. solution z}"
proof -
  have "infinite (range nth_solution)"
    by (intro range_inj_infinite nth_solution_inj)
  also have "range nth_solution = {z :: nat \<times> nat. solution z}"
    by (auto simp: solution_iff_nth_solution)
  finally show ?thesis .
qed

corollary infinite_solutions': "infinite {z :: int \<times> int. solution z}"
proof
  assume "finite {z :: int \<times> int. solution z}"
  hence "finite (map_prod (nat \<circ> abs) (nat \<circ> abs) ` {z :: int \<times> int. solution z})"
    by (rule finite_imageI)
  also have "(map_prod (nat \<circ> abs) (nat \<circ> abs) ` {z :: int \<times> int. solution z}) =
               {z :: nat \<times> nat. solution z}"
    by (auto simp: map_prod_def image_iff intro!: exI[of _ "int x" for x])
  finally show False using infinite_solutions by contradiction
qed


lemma strict_mono_pell_valuation_nth_solution: "strict_mono (pell_valuation \<circ> nth_solution)"
  using pell_valuation_fund_sol_ge_2
  by (auto simp: strict_mono_def intro!: power_strict_increasing)

lemma strict_mono_nth_solution:
  "strict_mono (fst \<circ> nth_solution)" "strict_mono (snd \<circ> nth_solution)"
proof -
  let ?g = nth_solution
  have "fst (?g m) < fst (?g n) \<and> snd (?g m) < snd (?g n)" if "m < n" for m n
    using pell_valuation_fund_sol_ge_2 that
    by (subst solutions_less_iff_pell_valuation_less) auto
  thus "strict_mono (fst \<circ> nth_solution)" "strict_mono (snd \<circ> nth_solution)"
    by (auto simp: strict_mono_def)
qed

end


subsection \<open>The case of an ``almost square'' parameter\<close>

text \<open>
  If \<open>D\<close> is equal to \<open>a\<^sup>2 - 1\<close> for some \<open>a > 1\<close>, we have a particularly simple case
  where the fundamental solution is simply \<open>(1, a)\<close>.
\<close>

context
  fixes a :: nat
  assumes a: "a > 1"
begin

lemma pell_square_minus1: "pell (a\<^sup>2 - Suc 0)"
proof
  show "\<not>is_square (a\<^sup>2 - Suc 0)"
  proof
    assume "is_square (a\<^sup>2 - Suc 0)"
    then obtain k where "k\<^sup>2 = a\<^sup>2 - 1" by (auto elim: is_nth_powerE)
    with a have "a\<^sup>2 = Suc (k\<^sup>2)" by simp
    hence "a = 1" using pell_square_solution_nat_iff[of "1" a k] by simp
    with a show False by simp
  qed
qed

interpretation pell "a\<^sup>2 - Suc 0"
  by (rule pell_square_minus1)

lemma fund_sol_square_minus1: "fund_sol = (a, 1)"
proof -
  from a have sol: "nontriv_solution (a, 1)"
    by (simp add: nontriv_solution_def)
  from sol have "snd fund_sol \<le> 1"
    using fund_sol_minimal''[of "(a, 1)"] by auto
  with solutions_linorder_strict[of a 1 "fst fund_sol" "snd fund_sol"]
       fund_sol_is_nontriv_solution sol
  show "fund_sol = (a, 1)"
    by (cases fund_sol) (auto simp: nontriv_solution_altdef)
qed

end


subsection \<open>Alternative presentation of the main results\<close>

theorem pell_solutions:
 fixes D :: nat
 assumes "\<nexists>k. D = k\<^sup>2"
 obtains x\<^sub>0 y\<^sub>0 :: nat
 where   "\<forall>(x::int) (y::int).
            x\<^sup>2 - D * y\<^sup>2 = 1 \<longleftrightarrow>
            (\<exists>n::nat. nat \<bar>x\<bar> + sqrt D * nat \<bar>y\<bar> = (x\<^sub>0 + sqrt D * y\<^sub>0) ^ n)"
proof -
  from assms interpret pell
    by unfold_locales (auto simp: is_nth_power_def)
  show ?thesis
  proof (rule that[of "fst fund_sol" "snd fund_sol"], intro allI, goal_cases)
    case (1 x y)
    have "(x\<^sup>2 - int D * y\<^sup>2 = 1) \<longleftrightarrow> solution (x, y)"
      by (auto simp: solution_def)
    also have "\<dots> \<longleftrightarrow> (\<exists>n. (nat \<bar>x\<bar>, nat \<bar>y\<bar>) = nth_solution n)"
      by (subst solution_iff_nth_solution') blast
    also have "(\<lambda>n. (nat \<bar>x\<bar>, nat \<bar>y\<bar>) = nth_solution n) =
                 (\<lambda>n. pell_valuation (nat \<bar>x\<bar>, nat \<bar>y\<bar>) = pell_valuation (nth_solution n))"
      by (subst pell_valuation_eq_iff) (auto simp add: case_prod_unfold prod_eq_iff fun_eq_iff)
    also have "\<dots> = (\<lambda>n. nat \<bar>x\<bar> + sqrt D * nat \<bar>y\<bar> = (fst fund_sol + sqrt D * snd fund_sol) ^ n)"
      by (subst pell_valuation_nth_solution)
         (simp add: pell_valuation_def case_prod_unfold mult_ac)
    finally show ?case .
  qed
qed

corollary pell_solutions_infinite:
 fixes D :: nat
 assumes "\<nexists>k. D = k\<^sup>2"
 shows   "infinite {(x :: int, y :: int). x\<^sup>2 - D * y\<^sup>2 = 1}"
proof -
  from assms interpret pell
    by unfold_locales (auto simp: is_nth_power_def)
  have "{(x :: int, y :: int). x\<^sup>2 - D * y\<^sup>2 = 1} = {z. solution z}"
    by (auto simp: solution_def)
  also have "infinite \<dots>" by (rule infinite_solutions')
  finally show ?thesis .
qed

end