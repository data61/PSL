(*  
    Author:      René Thiemann 
                 Akihisa Yamada
                 Jose Divason
    License:     BSD
*)
section \<open>Missing Unsorted\<close>

text \<open>This theory contains several lemmas which might be of interest to the Isabelle distribution.
  For instance, we prove that $b^n \cdot n^k$ is bounded by a constant whenever $0 < b < 1$.\<close>

theory Missing_Unsorted
imports
  HOL.Complex "HOL-Computational_Algebra.Factorial_Ring"
begin

lemma bernoulli_inequality: assumes x: "-1 \<le> (x :: 'a :: linordered_field)"
  shows "1 + of_nat n * x \<le> (1 + x) ^ n"
proof (induct n)
  case (Suc n)
  have "1 + of_nat (Suc n) * x = 1 + x + of_nat n * x" by (simp add: field_simps)
  also have "\<dots> \<le> \<dots> + of_nat n * x ^ 2" by simp
  also have "\<dots> = (1 + of_nat n * x) * (1 + x)" by (simp add: field_simps power2_eq_square)
  also have "\<dots> \<le> (1 + x) ^ n * (1 + x)"
    by (rule mult_right_mono[OF Suc], insert x, auto)
  also have "\<dots> = (1 + x) ^ (Suc n)" by simp
  finally show ?case .
qed simp

context
  fixes b :: "'a :: archimedean_field"
  assumes b: "0 < b" "b < 1"
begin
private lemma pow_one: "b ^ x \<le> 1" using power_Suc_less_one[OF b, of "x - 1"] by (cases x, auto)

private lemma pow_zero: "0 < b ^ x" using b(1) by simp

lemma exp_tends_to_zero: assumes c: "c > 0"
  shows "\<exists> x. b ^ x \<le> c" 
proof (rule ccontr)
  assume not: "\<not> ?thesis"
  define bb where "bb = inverse b"
  define cc where "cc = inverse c"
  from b have bb: "bb > 1" unfolding bb_def by (rule one_less_inverse)  
  from c have cc: "cc > 0" unfolding cc_def by simp
  define bbb where "bbb = bb - 1"
  have id: "bb = 1 + bbb" and bbb: "bbb > 0" and bm1: "bbb \<ge> -1" unfolding bbb_def using bb by auto
  have "\<exists> n. cc / bbb < of_nat n" by (rule reals_Archimedean2)
  then obtain n where lt: "cc / bbb < of_nat n" by auto
  from not have "\<not> b ^ n \<le> c" by auto
  hence bnc: "b ^ n > c" by simp
  have "bb ^ n = inverse (b ^ n)" unfolding bb_def by (rule power_inverse)
  also have "\<dots> < cc" unfolding cc_def
    by (rule less_imp_inverse_less[OF bnc c])
  also have "\<dots> < bbb * of_nat n" using lt bbb by (metis mult.commute pos_divide_less_eq)
  also have "\<dots> \<le> bb ^ n"
    using bernoulli_inequality[OF bm1, folded id, of n] by (simp add: ac_simps)
  finally show False by simp
qed

lemma linear_exp_bound: "\<exists> p. \<forall> x. b ^ x * of_nat x \<le> p"
proof -
  from b have "1 - b > 0" by simp
  from exp_tends_to_zero[OF this]
  obtain x0 where x0: "b ^ x0 \<le> 1 - b" ..
  {
    fix x
    assume "x \<ge> x0"
    hence "\<exists> y. x = x0 + y" by arith
    then obtain y where x: "x = x0 + y" by auto
    have "b ^ x = b ^ x0 * b ^ y" unfolding x by (simp add: power_add)
    also have "\<dots> \<le> b ^ x0" using pow_one[of y] pow_zero[of x0] by auto
    also have "\<dots> \<le> 1 - b" by (rule x0)
    finally have "b ^ x \<le> 1 - b" .
  } note x0 = this
  define bs where "bs = insert 1 { b ^ Suc x * of_nat (Suc x) | x . x \<le> x0}"
  have bs: "finite bs" unfolding bs_def by auto
  define p where "p = Max bs"
  have bs: "\<And> b. b \<in> bs \<Longrightarrow> b \<le> p" unfolding p_def using bs by simp
  hence p1: "p \<ge> 1" unfolding bs_def by auto
  show ?thesis
  proof (rule exI[of _ p], intro allI)
    fix x
    show "b ^ x * of_nat x \<le> p"
    proof (induct x)
      case (Suc x)
      show ?case
      proof (cases "x \<le> x0")
        case True
        show ?thesis 
          by (rule bs, unfold bs_def, insert True, auto)
      next
        case False
        let ?x = "of_nat x :: 'a"
        have "b ^ (Suc x) * of_nat (Suc x) = b * (b ^ x * ?x) + b ^ Suc x" by (simp add: field_simps)
        also have "\<dots> \<le> b * p + b ^ Suc x"
          by (rule add_right_mono[OF mult_left_mono[OF Suc]], insert b, auto)
        also have "\<dots> = p - ((1 - b) * p - b ^ (Suc x))" by (simp add: field_simps)
        also have "\<dots> \<le> p - 0"
        proof -
          have "b ^ Suc x \<le> 1 - b" using x0[of "Suc x"] False by auto
          also have "\<dots> \<le> (1 - b) * p" using b p1 by auto
          finally show ?thesis
            by (intro diff_left_mono, simp)
        qed
        finally show ?thesis by simp
      qed
    qed (insert p1, auto)
  qed
qed

lemma poly_exp_bound: "\<exists> p. \<forall> x. b ^ x * of_nat x ^ deg \<le> p" 
proof -
  show ?thesis
  proof (induct deg)
    case 0
    show ?case
      by (rule exI[of _ 1], intro allI, insert pow_one, auto)
  next
    case (Suc deg)
    then obtain q where IH: "\<And> x. b ^ x * (of_nat x) ^ deg \<le> q" by auto
    define p where "p = max 0 q"
    from IH have IH: "\<And> x. b ^ x * (of_nat x) ^ deg \<le> p" unfolding p_def using le_max_iff_disj by blast
    have p: "p \<ge> 0" unfolding p_def by simp
    show ?case
    proof (cases "deg = 0")
      case True
      thus ?thesis using linear_exp_bound by simp
    next
      case False note deg = this
      define p' where "p' = p*p * 2 ^ Suc deg * inverse b"
      let ?f = "\<lambda> x. b ^ x * (of_nat x) ^ Suc deg"
      define f where "f = ?f"
      {
        fix x
        let ?x = "of_nat x :: 'a"
        have "f (2 * x) \<le> (2 ^ Suc deg) * (p * p)"
        proof (cases "x = 0")
          case False
          hence x1: "?x \<ge> 1" by (cases x, auto)
          from x1 have x: "?x ^ (deg - 1) \<ge> 1" by simp
          from x1 have xx: "?x ^ Suc deg \<ge> 1" by (rule one_le_power)
          define c where "c = b ^ x * b ^ x * (2 ^ Suc deg)"
          have c: "c > 0" unfolding c_def using b by auto
          have "f (2 * x) = ?f (2 * x)" unfolding f_def by simp
          also have "b ^ (2 * x) = (b ^ x) * (b ^ x)" by (simp add: power2_eq_square power_even_eq)
          also have "of_nat (2 * x) = 2 * ?x" by simp
          also have "(2 * ?x) ^ Suc deg = 2 ^ Suc deg * ?x ^ Suc deg" by simp
          finally have "f (2 * x) = c * ?x ^ Suc deg" unfolding c_def by (simp add: ac_simps)
          also have "\<dots> \<le> c * ?x ^ Suc deg * ?x ^ (deg - 1)"
          proof -
            have "c * ?x ^ Suc deg > 0" using c xx by simp
            thus ?thesis unfolding mult_le_cancel_left1 using x by simp
          qed
          also have "\<dots> = c * ?x ^ (Suc deg + (deg - 1))" by (simp add: power_add)
          also have "Suc deg + (deg - 1) = deg + deg" using deg by simp
          also have "?x ^ (deg + deg) = (?x ^ deg) * (?x ^ deg)" by (simp add: power_add)
          also have "c * \<dots> = (2 ^ Suc deg) * ((b ^ x * ?x ^ deg) * (b ^ x * ?x ^ deg))" 
            unfolding c_def by (simp add: ac_simps)  
          also have "\<dots> \<le> (2 ^ Suc deg) * (p * p)"
            by (rule mult_left_mono[OF mult_mono[OF IH IH p]], insert pow_zero[of x], auto)
          finally show "f (2 * x) \<le> (2 ^ Suc deg) * (p * p)" .
        qed (auto simp: f_def)
        hence "?f (2 * x) \<le> (2 ^ Suc deg) * (p * p)" unfolding f_def .
      } note even = this
      show ?thesis
      proof (rule exI[of _ p'], intro allI)
        fix y
        show "?f y \<le> p'"
        proof (cases "even y")
          case True
          define x where "x = y div 2"
          have "y = 2 * x" unfolding x_def using True by simp
          from even[of x, folded this] have "?f y \<le> 2 ^ Suc deg * (p * p)" .
          also have "\<dots> \<le> \<dots> * inverse b"
            unfolding mult_le_cancel_left1 using b p by (simp add:sign_simps one_le_inverse)
          also have "\<dots> = p'" unfolding p'_def by (simp add: ac_simps)
          finally show "?f y \<le> p'" .
        next
          case False
          define x where "x = y div 2"
          have "y = 2 * x + 1" unfolding x_def using False by simp
          hence "?f y = ?f (2 * x + 1)" by simp
          also have "\<dots> \<le> b ^ (2 * x + 1) * of_nat (2 * x + 2) ^ Suc deg"
            by (rule mult_left_mono[OF power_mono], insert b, auto) 
          also have "b ^ (2 * x + 1) = b ^ (2 * x + 2) * inverse b" using b by auto
          also have "b ^ (2 * x + 2) * inverse b * of_nat (2 * x + 2) ^ Suc deg = 
            inverse b * ?f (2 * (x + 1))" by (simp add: ac_simps)
          also have "\<dots> \<le> inverse b * ((2 ^ Suc deg) * (p * p))"
            by (rule mult_left_mono[OF even], insert b, auto)
          also have "\<dots> = p'" unfolding p'_def by (simp add: ac_simps)
          finally show "?f y \<le> p'" .
        qed
      qed
    qed
  qed
qed
end

lemma prod_list_replicate[simp]: "prod_list (replicate n a) = a ^ n"
  by (induct n, auto)

lemma prod_list_power: fixes xs :: "'a :: comm_monoid_mult list"
  shows "prod_list xs ^ n = (\<Prod>x\<leftarrow>xs. x ^ n)"
  by (induct xs, auto simp: power_mult_distrib)

lemma set_upt_Suc: "{0 ..< Suc i} = insert i {0 ..< i}"
  by (fact atLeast0_lessThan_Suc)

lemma prod_pow[simp]: "(\<Prod>i = 0..<n. p) = (p :: 'a :: comm_monoid_mult) ^ n"
  by (induct n, auto simp: set_upt_Suc)


(* GCD and LCM part *)

lemma dvd_abs_mult_left_int [simp]:
  "\<bar>a\<bar> * y dvd x \<longleftrightarrow> a * y dvd x" for x y a :: int
  using abs_dvd_iff [of "a * y"] abs_dvd_iff [of "\<bar>a\<bar> * y"]
  by (simp add: abs_mult)
  
lemma gcd_abs_mult_right_int [simp]:
  "gcd x (\<bar>a\<bar> * y) = gcd x (a * y)" for x y a :: int
  using gcd_abs2_int [of _ "a * y"] gcd_abs2_int [of _ "\<bar>a\<bar> * y"]
  by (simp add: abs_mult)

lemma lcm_abs_mult_right_int [simp]:
  "lcm x (\<bar>a\<bar> * y) = lcm x (a * y)" for x y a :: int
  using lcm_abs2_int [of _ "a * y"] lcm_abs2_int [of _ "\<bar>a\<bar> * y"]
  by (simp add: abs_mult)

lemma gcd_abs_mult_left_int [simp]:
  "gcd x (a * \<bar>y\<bar>) = gcd x (a * y)" for x y a :: int
  using gcd_abs2_int [of _ "a * \<bar>y\<bar>"] gcd_abs2_int [of _ "a * y"]
  by (simp add: abs_mult)

lemma lcm_abs_mult_left_int [simp]:
  "lcm x (a * \<bar>y\<bar>) = lcm x (a * y)" for x y a :: int
  using lcm_abs2_int [of _ "a * \<bar>y\<bar>"] lcm_abs2_int [of _ "a * y"]
  by (simp add: abs_mult)


abbreviation (input) list_gcd :: "'a :: semiring_gcd list \<Rightarrow> 'a" where
  "list_gcd \<equiv> gcd_list"

abbreviation (input) list_lcm :: "'a :: semiring_gcd list \<Rightarrow> 'a" where
  "list_lcm \<equiv> lcm_list"


lemma list_gcd_simps: "list_gcd [] = 0" "list_gcd (x # xs) = gcd x (list_gcd xs)"
  by simp_all

lemma list_gcd: "x \<in> set xs \<Longrightarrow> list_gcd xs dvd x"
  by (fact Gcd_fin_dvd)

lemma list_gcd_greatest: "(\<And> x. x \<in> set xs \<Longrightarrow> y dvd x) \<Longrightarrow> y dvd (list_gcd xs)"
  by (fact gcd_list_greatest)

lemma list_gcd_mult_int [simp]: 
  fixes xs :: "int list"
  shows "list_gcd (map (times a) xs) = \<bar>a\<bar> * list_gcd xs"
  by (simp add: Gcd_mult)

lemma list_lcm_simps: "list_lcm [] = 1" "list_lcm (x # xs) = lcm x (list_lcm xs)"
  by simp_all

lemma list_lcm: "x \<in> set xs \<Longrightarrow> x dvd list_lcm xs" 
  by (fact dvd_Lcm_fin)

lemma list_lcm_least: "(\<And> x. x \<in> set xs \<Longrightarrow> x dvd y) \<Longrightarrow> list_lcm xs dvd y"
  by (fact lcm_list_least)

lemma lcm_mult_distrib_nat: "(k :: nat) * lcm m n = lcm (k * m) (k * n)"
  by (simp add: lcm_mult_left)

lemma lcm_mult_distrib_int: "abs (k::int) * lcm m n = lcm (k * m) (k * n)"
  by (simp add: lcm_mult_left)

lemma list_lcm_mult_int [simp]:
  fixes xs :: "int list"
  shows "list_lcm (map (times a) xs) = (if xs = [] then 1 else \<bar>a\<bar> * list_lcm xs)"
  by (simp add: Lcm_mult)

lemma list_lcm_pos:
  "list_lcm xs \<ge> (0 :: int)"
  "0 \<notin> set xs \<Longrightarrow> list_lcm xs \<noteq> 0"
  "0 \<notin> set xs \<Longrightarrow> list_lcm xs > 0" 
proof -
  have "0 \<le> \<bar>Lcm (set xs)\<bar>"
    by (simp only: abs_ge_zero)
  then have "0 \<le> Lcm (set xs)"
    by simp
  then show "list_lcm xs \<ge> 0"
    by simp
  assume "0 \<notin> set xs"
  then show "list_lcm xs \<noteq> 0"
    by (simp add: Lcm_0_iff)
  with \<open>list_lcm xs \<ge> 0\<close> show "list_lcm xs > 0"
    by (simp add: le_less)
qed

lemma quotient_of_nonzero: "snd (quotient_of r) > 0" "snd (quotient_of r) \<noteq> 0"
  using quotient_of_denom_pos' [of r] by simp_all

lemma quotient_of_int_div: assumes q: "quotient_of (of_int x / of_int y) = (a, b)"
  and y: "y \<noteq> 0" 
  shows "\<exists> z. z \<noteq> 0 \<and> x = a * z \<and> y = b * z"
proof -
  let ?r = "rat_of_int"
  define z where "z = gcd x y"
  define x' where "x' = x div z"
  define y' where "y' = y div z"
  have id: "x = z * x'" "y = z * y'" unfolding x'_def y'_def z_def by auto
  from y have y': "y' \<noteq> 0" unfolding id by auto
  have z: "z \<noteq> 0" unfolding z_def using y by auto
  have cop: "coprime x' y'" unfolding x'_def y'_def z_def 
    using div_gcd_coprime y by blast
  have "?r x / ?r y = ?r x' / ?r y'" unfolding id using z y y' by (auto simp: field_simps) 
  from assms[unfolded this] have quot: "quotient_of (?r x' / ?r y') = (a, b)" by auto
  from quotient_of_coprime[OF quot] have cop': "coprime a b" .
  hence cop: "coprime b a"
    by (simp add: ac_simps)
  from quotient_of_denom_pos[OF quot] have b: "b > 0" "b \<noteq> 0" by auto
  from quotient_of_div[OF quot] quotient_of_denom_pos[OF quot] y'
  have "?r x' * ?r b = ?r a * ?r y'" by (auto simp: field_simps)
  hence id': "x' * b = a * y'" unfolding of_int_mult[symmetric] by linarith
  from id'[symmetric] have "b dvd y' * a" unfolding mult.commute[of y'] by auto
  with cop y' have "b dvd y'"
    by (simp add: coprime_dvd_mult_left_iff) 
  then obtain z' where ybz: "y' = b * z'" unfolding dvd_def by auto
  from id[unfolded y' this] have y: "y = b * (z * z')" by auto
  with \<open>y \<noteq> 0\<close> have zz: "z * z' \<noteq> 0" by auto
  from quotient_of_div[OF q] \<open>y \<noteq> 0\<close> \<open>b \<noteq> 0\<close> 
  have "?r x * ?r b = ?r y * ?r a" by (auto simp: field_simps)
  hence id': "x * b = y * a" unfolding of_int_mult[symmetric] by linarith
  from this[unfolded y] b have x: "x = a * (z * z')" by auto
  show ?thesis unfolding x y using zz by blast
qed

fun max_list_non_empty :: "('a :: linorder) list \<Rightarrow> 'a" where
  "max_list_non_empty [x] = x"
| "max_list_non_empty (x # xs) = max x (max_list_non_empty xs)"

lemma max_list_non_empty: "x \<in> set xs \<Longrightarrow> x \<le> max_list_non_empty xs"
proof (induct xs)
  case (Cons y ys) note oCons = this
  show ?case 
  proof (cases ys)
    case (Cons z zs)
    hence id: "max_list_non_empty (y # ys) = max y (max_list_non_empty ys)" by simp
    from oCons show ?thesis unfolding id by (auto simp: max.coboundedI2)
  qed (insert oCons, auto)
qed simp

lemma cnj_reals[simp]: "(cnj c \<in> \<real>) = (c \<in> \<real>)"
  using Reals_cnj_iff by fastforce

lemma sgn_real_mono: "x \<le> y \<Longrightarrow> sgn x \<le> sgn (y :: real)"
  unfolding sgn_real_def
  by (auto split: if_splits)

lemma sgn_minus_rat: "sgn (- (x :: rat)) = - sgn x"
  by (fact Rings.sgn_minus)

lemma real_of_rat_sgn: "sgn (of_rat x) = real_of_rat (sgn x)"
  unfolding sgn_real_def sgn_rat_def by auto

lemma inverse_le_iff_sgn: assumes sgn: "sgn x = sgn y"
  shows "(inverse (x :: real) \<le> inverse y) = (y \<le> x)"
proof (cases "x = 0")
  case True
  with sgn have "sgn y = 0" by simp
  hence "y = 0" unfolding sgn_real_def by (cases "y = 0"; cases "y < 0"; auto)
  thus ?thesis using True by simp
next
  case False note x = this
  show ?thesis
  proof (cases "x < 0")
    case True
    with x sgn have "sgn y = -1" by simp
    hence "y < 0" unfolding sgn_real_def by (cases "y = 0"; cases "y < 0", auto)
    show ?thesis
      by (rule inverse_le_iff_le_neg[OF True \<open>y < 0\<close>])
  next
    case False
    with x have x: "x > 0" by auto
    with sgn have "sgn y = 1" by auto
    hence "y > 0" unfolding sgn_real_def by (cases "y = 0"; cases "y < 0", auto)
    show ?thesis
      by (rule inverse_le_iff_le[OF x \<open>y > 0\<close>])
  qed
qed

lemma inverse_le_sgn: assumes sgn: "sgn x = sgn y" and xy: "x \<le> (y :: real)"
  shows "inverse y \<le> inverse x"
  using xy inverse_le_iff_sgn[OF sgn] by auto

lemma set_list_update: "set (xs [i := k]) = 
  (if i < length xs then insert k (set (take i xs) \<union> set (drop (Suc i) xs)) else set xs)"
proof (induct xs arbitrary: i)
  case (Cons x xs i) 
  thus ?case
    by (cases i, auto)
qed simp

lemma prod_list_dvd: assumes "(x :: 'a :: comm_monoid_mult) \<in> set xs"
  shows "x dvd prod_list xs"
proof -
  from assms[unfolded in_set_conv_decomp] obtain ys zs where xs: "xs = ys @ x # zs" by auto
  show ?thesis unfolding xs dvd_def by (intro exI[of _ "prod_list (ys @ zs)"], simp add: ac_simps)
qed

lemma dvd_prod: 
fixes A::"'b set" 
assumes "\<exists>b\<in>A. a dvd f b" "finite A"
shows "a dvd prod f A" 
using assms(2,1)
proof (induct A)
  case (insert x A)
  thus ?case 
    using comm_monoid_mult_class.dvd_mult dvd_mult2 insert_iff prod.insert by auto
qed auto

context
  fixes xs :: "'a :: comm_monoid_mult list"
begin
lemma prod_list_filter: "prod_list (filter f xs) * prod_list (filter (\<lambda> x. \<not> f x) xs) = prod_list xs"
  by (induct xs, auto simp: ac_simps)

lemma prod_list_partition: assumes "partition f xs = (ys, zs)"
  shows "prod_list xs = prod_list ys * prod_list zs"
  using assms by (subst prod_list_filter[symmetric, of f], auto simp: o_def)
end

lemma dvd_imp_mult_div_cancel_left[simp]:
  assumes "(a :: 'a :: semidom_divide) dvd b"
  shows "a * (b div a) = b"
proof(cases "b = 0")
  case True then show ?thesis by auto
next
  case False
  with dvdE[OF assms] obtain c where *: "b = a * c" by auto
  also with False have "a \<noteq> 0" by auto
  then have "a * c div a = c" by auto
  also note *[symmetric]
  finally show ?thesis.
qed

lemma (in semidom) prod_list_zero_iff[simp]: 
  "prod_list xs = 0 \<longleftrightarrow> 0 \<in> set xs" by (induction xs, auto)


context comm_monoid_mult begin

lemma unit_prod [intro]:
  shows "a dvd 1 \<Longrightarrow> b dvd 1 \<Longrightarrow> (a * b) dvd 1"
  by (subst mult_1_left [of 1, symmetric]) (rule mult_dvd_mono)

lemma is_unit_mult_iff[simp]:
  shows "(a * b) dvd 1 \<longleftrightarrow> a dvd 1 \<and> b dvd 1"
  by (auto dest: dvd_mult_left dvd_mult_right)

end

context comm_semiring_1
begin
lemma irreducibleE[elim]:
  assumes "irreducible p"
      and "p \<noteq> 0 \<Longrightarrow> \<not> p dvd 1 \<Longrightarrow> (\<And>a b. p = a * b \<Longrightarrow> a dvd 1 \<or> b dvd 1) \<Longrightarrow> thesis"
  shows thesis using assms by (auto simp: irreducible_def)

lemma not_irreducibleE:
  assumes "\<not> irreducible x"
      and "x = 0 \<Longrightarrow> thesis"
      and "x dvd 1 \<Longrightarrow> thesis"
      and "\<And>a b. x = a * b \<Longrightarrow> \<not> a dvd 1 \<Longrightarrow> \<not> b dvd 1 \<Longrightarrow> thesis"
  shows thesis using assms unfolding irreducible_def by auto

lemma prime_elem_dvd_prod_list:
  assumes p: "prime_elem p" and pA: "p dvd prod_list A" shows "\<exists>a \<in> set A. p dvd a"
proof(insert pA, induct A)
  case Nil
  with p show ?case by (simp add: prime_elem_not_unit)
next
  case (Cons a A)
  then show ?case by (auto simp: prime_elem_dvd_mult_iff[OF p])
qed

lemma prime_elem_dvd_prod_mset:
  assumes p: "prime_elem p" and pA: "p dvd prod_mset A" shows "\<exists>a \<in># A. p dvd a"
proof(insert pA, induct A)
  case empty
  with p show ?case by (simp add: prime_elem_not_unit)
next
  case (add a A)
  then show ?case by (auto simp: prime_elem_dvd_mult_iff[OF p])
qed

lemma mult_unit_dvd_iff[simp]:
  assumes "b dvd 1"
  shows "a * b dvd c \<longleftrightarrow> a dvd c"
proof
  assume "a * b dvd c"
  with assms show "a dvd c" using dvd_mult_left[of a b c] by simp
next
  assume "a dvd c"
  with assms mult_dvd_mono show "a * b dvd c" by fastforce
qed

lemma mult_unit_dvd_iff'[simp]: "a dvd 1 \<Longrightarrow> (a * b) dvd c \<longleftrightarrow> b dvd c"
  using mult_unit_dvd_iff [of a b c] by (simp add: ac_simps)

lemma irreducibleD':
  assumes "irreducible a" "b dvd a"
  shows   "a dvd b \<or> b dvd 1"
proof -
  from assms obtain c where c: "a = b * c" by (elim dvdE)
  from irreducibleD[OF assms(1) this] have "b dvd 1 \<or> c dvd 1" .
  thus ?thesis by (auto simp: c)
qed

end



context idom
begin

text \<open>
  Following lemmas are adapted and generalized so that they don't use "algebraic" classes.
\<close>

lemma dvd_times_left_cancel_iff [simp]:
  assumes "a \<noteq> 0"
  shows "a * b dvd a * c \<longleftrightarrow> b dvd c"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain d where "a * c = a * b * d" ..
  with assms have "c = b * d" by (auto simp add: ac_simps)
  then show ?rhs ..
next
  assume ?rhs
  then obtain d where "c = b * d" ..
  then have "a * c = a * b * d" by (simp add: ac_simps)
  then show ?lhs ..
qed

lemma dvd_times_right_cancel_iff [simp]:
  assumes "a \<noteq> 0"
  shows "b * a dvd c * a \<longleftrightarrow> b dvd c"
  using dvd_times_left_cancel_iff [of a b c] assms by (simp add: ac_simps)


lemma irreducibleI':
  assumes "a \<noteq> 0" "\<not> a dvd 1" "\<And>b. b dvd a \<Longrightarrow> a dvd b \<or> b dvd 1"
  shows   "irreducible a"
proof (rule irreducibleI)
  fix b c assume a_eq: "a = b * c"
  hence "a dvd b \<or> b dvd 1" by (intro assms) simp_all
  thus "b dvd 1 \<or> c dvd 1"
  proof
    assume "a dvd b"
    hence "b * c dvd b * 1" by (simp add: a_eq)
    moreover from \<open>a \<noteq> 0\<close> a_eq have "b \<noteq> 0" by auto
    ultimately show ?thesis using dvd_times_left_cancel_iff by fastforce
  qed blast
qed (simp_all add: assms(1,2))

lemma irreducible_altdef:
  shows "irreducible x \<longleftrightarrow> x \<noteq> 0 \<and> \<not> x dvd 1 \<and> (\<forall>b. b dvd x \<longrightarrow> x dvd b \<or> b dvd 1)"
  using irreducibleI'[of x] irreducibleD'[of x] irreducible_not_unit[of x] by auto

lemma dvd_mult_unit_iff:
  assumes b: "b dvd 1"
  shows "a dvd c * b \<longleftrightarrow> a dvd c"
proof-
  from b obtain b' where 1: "b * b' = 1" by (elim dvdE, auto)
  then have b0: "b \<noteq> 0" by auto
  from 1 have "a = (a * b') * b" by (simp add: ac_simps)
  also have "\<dots> dvd c * b \<longleftrightarrow> a * b' dvd c" using b0 by auto
  finally show ?thesis by (auto intro: dvd_mult_left)
qed

lemma dvd_mult_unit_iff': "b dvd 1 \<Longrightarrow> a dvd b * c \<longleftrightarrow> a dvd c"
  using dvd_mult_unit_iff [of b a c] by (simp add: ac_simps)

lemma irreducible_mult_unit_left:
  shows "a dvd 1 \<Longrightarrow> irreducible (a * p) \<longleftrightarrow> irreducible p"
  by (auto simp: irreducible_altdef mult.commute[of a] dvd_mult_unit_iff)

lemma irreducible_mult_unit_right:
  shows "a dvd 1 \<Longrightarrow> irreducible (p * a) \<longleftrightarrow> irreducible p"
  by (auto simp: irreducible_altdef mult.commute[of a] dvd_mult_unit_iff)

lemma prime_elem_imp_irreducible:
  assumes "prime_elem p"
  shows   "irreducible p"
proof (rule irreducibleI)
  fix a b
  assume p_eq: "p = a * b"
  with assms have nz: "a \<noteq> 0" "b \<noteq> 0" by auto
  from p_eq have "p dvd a * b" by simp
  with \<open>prime_elem p\<close> have "p dvd a \<or> p dvd b" by (rule prime_elem_dvd_multD)
  with \<open>p = a * b\<close> have "a * b dvd 1 * b \<or> a * b dvd a * 1" by auto
  thus "a dvd 1 \<or> b dvd 1"
    by (simp only: dvd_times_left_cancel_iff[OF nz(1)] dvd_times_right_cancel_iff[OF nz(2)])
qed (insert assms, simp_all add: prime_elem_def)

lemma unit_imp_dvd [dest]: "b dvd 1 \<Longrightarrow> b dvd a"
  by (rule dvd_trans [of _ 1]) simp_all

lemma unit_mult_left_cancel: "a dvd 1 \<Longrightarrow> a * b = a * c \<longleftrightarrow> b = c"
  using mult_cancel_left [of a b c] by auto

lemma unit_mult_right_cancel: "a dvd 1 \<Longrightarrow> b * a = c * a \<longleftrightarrow> b = c"
  using unit_mult_left_cancel [of a b c] by (auto simp add: ac_simps)

text \<open>New parts from here\<close>

lemma irreducible_multD:
  assumes l: "irreducible (a*b)"
  shows "a dvd 1 \<and> irreducible b \<or> b dvd 1 \<and> irreducible a"
proof-
  from l have "a dvd 1 \<or> b dvd 1" using irreducibleD by auto
  then show ?thesis
  proof(elim disjE)
    assume a: "a dvd 1"
    with l have "irreducible b"
      unfolding irreducible_def
      by (metis is_unit_mult_iff mult.left_commute mult_not_zero)
    with a show ?thesis by auto
  next
    assume a: "b dvd 1"
    with l have "irreducible a"
      unfolding irreducible_def
      by (meson is_unit_mult_iff mult_not_zero semiring_normalization_rules(16))
    with a show ?thesis by auto
  qed
qed

end

lemma (in field) irreducible_field[simp]:
  "irreducible x \<longleftrightarrow> False" by (auto simp: dvd_field_iff irreducible_def)

lemma (in idom) irreducible_mult:
  shows "irreducible (a*b) \<longleftrightarrow> a dvd 1 \<and> irreducible b \<or> b dvd 1 \<and> irreducible a"
  by (auto dest: irreducible_multD simp: irreducible_mult_unit_left irreducible_mult_unit_right)


end
