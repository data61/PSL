(* author: Thiemann *)

section \<open>Roots of Unity\<close>

theory Roots_Unity
imports
  Polynomial_Factorization.Order_Polynomial
  "HOL-Computational_Algebra.Fundamental_Theorem_Algebra"
  Polynomial_Interpolation.Ring_Hom_Poly
begin

lemma cis_mult_cmod_id: "cis (arg x) * of_real (cmod x) = x"
  using rcis_cmod_arg[unfolded rcis_def] by (simp add: ac_simps)

lemma rcis_mult_cis[simp]: "rcis n a * cis b = rcis n (a + b)" unfolding cis_rcis_eq rcis_mult by simp
lemma rcis_div_cis[simp]: "rcis n a / cis b = rcis n (a - b)" unfolding cis_rcis_eq rcis_divide by simp

lemma cis_plus_2pi[simp]: "cis (x + 2 * pi) = cis x" by (auto simp: complex_eq_iff)
lemma cis_plus_2pi_neq_1: assumes x: "0 < x" "x < 2 * pi"
  shows "cis x \<noteq> 1"
proof -
  from x have "cos x \<noteq> 1" by (smt cos_2pi_minus cos_monotone_0_pi cos_zero)
  thus ?thesis by (auto simp: complex_eq_iff)
qed

lemma cis_times_2pi[simp]: "cis (of_nat n * 2 * pi) = 1"
proof (induct n)
  case (Suc n)
  have "of_nat (Suc n) * 2 * pi = of_nat n * 2 * pi + 2 * pi" by (simp add: distrib_right)
  also have "cis \<dots> = 1" unfolding cis_plus_2pi Suc ..
  finally show ?case .
qed simp

declare cis_pi[simp]

lemma cis_pi_2[simp]: "cis (pi / 2) = \<i>"
  by (auto simp: complex_eq_iff)

lemma cis_add_pi[simp]: "cis (pi + x) = - cis x"
  by (auto simp: complex_eq_iff)

lemma cis_3_pi_2[simp]: "cis (pi * 3 / 2) = - \<i>"
proof -
  have "cis (pi * 3 / 2) = cis (pi + pi / 2)"
    by (rule arg_cong[of _ _ cis], simp)
  also have "\<dots> = - \<i>" unfolding cis_add_pi by simp
  finally show ?thesis .
qed

lemma rcis_plus_2pi[simp]: "rcis y (x + 2 * pi) = rcis y x" unfolding rcis_def by simp
lemma rcis_times_2pi[simp]: "rcis r (of_nat n * 2 * pi) = of_real r"
  unfolding rcis_def cis_times_2pi by simp

lemma arg_rcis_cis: assumes n: "n > 0" shows "arg (rcis n x) = arg (cis x)"
  using arg_bounded arg_unique cis_arg complex_mod_rcis n rcis_def sgn_eq by auto

lemma arg_eqD: assumes "arg (cis x) = arg (cis y)" "-pi < x" "x \<le> pi" "-pi < y" "y \<le> pi"
  shows "x = y"
  using assms(1) unfolding arg_unique[OF sgn_cis assms(2-3)] arg_unique[OF sgn_cis assms(4-5)] .

lemma rcis_inj_on: assumes r: "r \<noteq> 0" shows "inj_on (rcis r) {0 ..< 2 * pi}"
proof (rule inj_onI, goal_cases)
  case (1 x y)
  from arg_cong[OF 1(3), of "\<lambda> x. x / r"] have "cis x = cis y" using r by (simp add: rcis_def)
  from arg_cong[OF this, of "\<lambda> x. inverse x"] have "cis (-x) = cis (-y)" by simp
  from arg_cong[OF this, of uminus] have *: "cis (-x + pi) = cis (-y + pi)"
    by (auto simp: complex_eq_iff)
  have "- x + pi = - y + pi"
    by (rule arg_eqD[OF arg_cong[OF *, of arg]], insert 1(1-2), auto)
  thus ?case by simp
qed

lemma cis_inj_on: "inj_on cis {0 ..< 2 * pi}"
  using rcis_inj_on[of 1] unfolding rcis_def by auto

definition root_unity :: "nat \<Rightarrow> 'a :: comm_ring_1 poly" where
  "root_unity n = monom 1 n - 1"

lemma poly_root_unity: "poly (root_unity n) x = 0 \<longleftrightarrow> x^n = 1"
  unfolding root_unity_def by (simp add: poly_monom)

lemma degree_root_unity[simp]: "degree (root_unity n) = n" (is "degree ?p = _")
proof -
  have p: "?p = monom 1 n + (-1)" unfolding root_unity_def by auto
  show ?thesis
  proof (cases n)
    case 0
    thus ?thesis unfolding p by simp
  next
    case (Suc m)
    show ?thesis unfolding p unfolding Suc
      by (subst degree_add_eq_left, auto simp: degree_monom_eq)
  qed
qed

lemma zero_root_unit[simp]: "root_unity n = 0 \<longleftrightarrow> n = 0" (is "?p = 0 \<longleftrightarrow> _")
proof (cases "n = 0")
  case True
  thus ?thesis unfolding root_unity_def by simp
next
  case False
  from degree_root_unity[of n] False
  have "degree ?p \<noteq> 0" by auto
  hence "?p \<noteq> 0" by fastforce
  thus ?thesis using False by auto
qed

definition prod_root_unity :: "nat list \<Rightarrow> 'a :: idom poly" where
  "prod_root_unity ns = prod_list (map root_unity ns)"

lemma poly_prod_root_unity: "poly (prod_root_unity ns) x = 0 \<longleftrightarrow> (\<exists>k\<in>set ns. x ^ k = 1)"
  unfolding prod_root_unity_def
  by (simp add: poly_prod_list prod_list_zero_iff o_def image_def poly_root_unity)

lemma degree_prod_root_unity[simp]: "0 \<notin> set ns \<Longrightarrow> degree (prod_root_unity ns) = sum_list ns"
  unfolding prod_root_unity_def
  by (subst degree_prod_list_eq, auto simp: o_def)

lemma zero_prod_root_unit[simp]: "prod_root_unity ns = 0 \<longleftrightarrow> 0 \<in> set ns"
  unfolding prod_root_unity_def prod_list_zero_iff by auto

lemma roots_of_unity: assumes n: "n \<noteq> 0"
  shows "(\<lambda> i. (cis (of_nat i * 2 * pi / n))) ` {0 ..< n} = { x :: complex. x ^ n = 1}" (is "?prod = ?Roots")
     "{x. poly (root_unity n) x = 0} = { x :: complex. x ^ n = 1}"
     "card { x :: complex. x ^ n = 1} = n"
proof (atomize(full), goal_cases)
  case 1
  let ?one = "1 :: complex"
  let ?p = "monom ?one n - 1"
  have degM: "degree (monom ?one n) = n" by (rule degree_monom_eq, simp)
  have "degree ?p = degree (monom ?one n + (-1))" by simp
  also have "\<dots> = degree (monom ?one n)"
    by (rule degree_add_eq_left, insert n, simp add: degM)
  finally have degp: "degree ?p = n" unfolding degM .
  with n have p: "?p \<noteq> 0" by auto
  have roots: "?Roots = {x. poly ?p x = 0}"
    unfolding poly_diff poly_monom by simp
  also have "finite \<dots>" by (rule poly_roots_finite[OF p])
  finally have fin: "finite ?Roots" .
  have sub: "?prod \<subseteq> ?Roots"
  proof
    fix x
    assume "x \<in> ?prod"
    then obtain i where x: "x = cis (real i * 2 * pi / n)" by auto
    have "x ^ n = cis (real i * 2 * pi)" unfolding x DeMoivre using n by simp
    also have "\<dots> = 1" by simp
    finally show "x \<in> ?Roots" by auto
  qed
  have Rn: "card ?Roots \<le> n" unfolding roots
    by (rule poly_roots_degree[of ?p, unfolded degp, OF p])
  have "\<dots> = card {0 ..< n}" by simp
  also have "\<dots> = card ?prod"
  proof (rule card_image[symmetric], rule inj_onI, goal_cases)
    case (1 x y)
    {
      fix m
      assume "m < n"
      hence "real m < real n" by simp
      from mult_strict_right_mono[OF this, of "2 * pi / real n"] n
      have "real m * 2 * pi / real n < real n * 2 * pi / real n" by simp
      hence "real m * 2 * pi / real n < 2 * pi" using n by simp
    } note [simp] = this
    have 0: "(1 :: real) \<noteq> 0" using n by auto
    have "real x * 2 * pi / real n = real y * 2 * pi / real n"
      by (rule inj_onD[OF rcis_inj_on 1(3)[unfolded cis_rcis_eq]], insert 1(1-2), auto)
    with n show "x = y" by auto
  qed
  finally have cn:  "card ?prod = n" ..
  with Rn have "card ?prod \<ge> card ?Roots" by auto
  with card_mono[OF fin sub] have card: "card ?prod = card ?Roots" by auto
  have "?prod = ?Roots"
    by (rule card_subset_eq[OF fin sub card])
  from this roots[symmetric] cn[unfolded this]
  show ?case unfolding root_unity_def by blast
qed

lemma poly_roots_dvd: fixes p :: "'a :: field poly"
  assumes "p \<noteq> 0" and "degree p = n"
  and "card {x. poly p x = 0} \<ge> n" and "{x. poly p x = 0} \<subseteq> {x. poly q x = 0}"
shows "p dvd q"
proof -
  from poly_roots_degree[OF assms(1)] assms(2-3) have "card {x. poly p x = 0} = n" by auto
  from assms(1-2) this assms(4)
  show ?thesis
  proof (induct n arbitrary: p q)
    case (0 p q)
    from is_unit_iff_degree[OF 0(1)] 0(2) show ?case by blast
  next
    case (Suc n p q)
    let ?P = "{x. poly p x = 0}"
    let ?Q = "{x. poly q x = 0}"
    from Suc(4-5) card_gt_0_iff[of ?P] obtain x where
      x: "poly p x = 0" "poly q x = 0" and fin: "finite ?P" by auto
    define r where "r = [:-x, 1:]"
    from x[unfolded poly_eq_0_iff_dvd r_def[symmetric]] obtain p' q' where
      p: "p = r * p'" and q: "q = r * q'" unfolding dvd_def by auto
    from Suc(2) have "degree p = degree r + degree p'" unfolding p
      by (subst degree_mult_eq, auto)
    with Suc(3) have deg: "degree p' = n" unfolding r_def by auto
    from Suc(2) p have p'0: "p' \<noteq> 0" by auto
    let ?P' = "{x. poly p' x = 0}"
    let ?Q' = "{x. poly q' x = 0}"
    have P: "?P = insert x ?P'" unfolding p poly_mult unfolding r_def by auto
    have Q: "?Q = insert x ?Q'" unfolding q poly_mult unfolding r_def by auto
    {
      assume "x \<in> ?P'"
      hence "?P = ?P'" unfolding P by auto
      from arg_cong[OF this, of card, unfolded Suc(4)] deg have False
        using poly_roots_degree[OF p'0] by auto
    } note xp' = this
    hence xP': "x \<notin> ?P'" by auto
    have "card ?P = Suc (card ?P')" unfolding P
      by (rule card_insert_disjoint[OF _ xP'], insert fin[unfolded P], auto)
    with Suc(4) have card: "card ?P' = n" by auto
    from Suc(5)[unfolded P Q] xP' have "?P' \<subseteq> ?Q'" by auto
    from Suc(1)[OF p'0 deg card this]
    have IH: "p' dvd q'" .
    show ?case unfolding p q using IH by simp
  qed
qed

lemma root_unity_decomp: assumes n: "n \<noteq> 0"
  shows "root_unity n =
    prod_list (map (\<lambda> i. [:-cis (of_nat i * 2 * pi / n), 1:]) [0 ..< n])" (is "?u = ?p")
proof -
  have deg: "degree ?u = n" by simp
  note main = roots_of_unity[OF n]
  have dvd: "?u dvd ?p"
  proof (rule poly_roots_dvd[OF _ deg])
    show "n \<le> card {x. poly ?u x = 0}" using main by auto
    show "?u \<noteq> 0" using n by auto
    show "{x. poly ?u x = 0} \<subseteq> {x. poly ?p x = 0}"
      unfolding main(2) main(1)[symmetric] poly_prod_list prod_list_zero_iff by auto
  qed
  have deg': "degree ?p = n"
    by (subst degree_prod_list_eq, auto simp: o_def sum_list_triv)
  have mon: "monic ?u" using deg unfolding root_unity_def using n by auto
  have mon': "monic ?p" by (rule monic_prod_list, auto)
  from dvd[unfolded dvd_def] obtain f where puf: "?p = ?u * f" by auto
  have "degree ?p = degree ?u + degree f" using mon' n unfolding puf
    by (subst degree_mult_eq, auto)
  with deg deg' have "degree f = 0" by auto
  from degree0_coeffs[OF this] obtain a where f: "f = [:a:]" by blast
  from arg_cong[OF puf, of lead_coeff] mon mon'
  have "a = 1" unfolding puf f by (cases "a = 0", auto)
  with f have f: "f = 1" by auto
  with puf show ?thesis by auto
qed

lemma order_monic_linear: "order x [:y,1:] = (if y + x = 0 then 1 else 0)"
proof (cases "y + x = 0")
  case True
  hence "poly [:y,1:] x = 0" by simp
  from this[unfolded order_root] have "order x [:y,1:] \<noteq> 0" by auto
  moreover from order_degree[of "[:y,1:]" x] have "order x [:y,1:] \<le> 1" by auto
  ultimately show ?thesis unfolding True by auto
next
  case False
  hence "poly [:y,1:] x \<noteq> 0" by auto
  from order_0I[OF this] False show ?thesis by auto
qed

lemma order_root_unity: fixes x :: complex assumes n: "n \<noteq> 0"
  shows "order x (root_unity n) = (if x^n = 1 then 1 else 0)"
  (is "order _ ?u = _")
proof (cases "x^n = 1")
  case False
  with roots_of_unity(2)[OF n] have "poly ?u x \<noteq> 0" by auto
  from False order_0I[OF this] show ?thesis by auto
next
  case True
  let ?phi = "\<lambda> i :: nat. i * 2 * pi / n"
  from True roots_of_unity(1)[OF n] obtain i where i: "i < n"
    and x: "x = cis (?phi i)" by force
  from i have n_split: "[0 ..< n] = [0 ..< i] @ i # [Suc i ..< n]"
    by (metis le_Suc_ex less_imp_le_nat not_le_imp_less not_less0 upt_add_eq_append upt_conv_Cons)
  {
    fix j
    assume j: "j < n \<or> j < i" and eq: "cis (?phi i) = cis (?phi j)"
    from inj_onD[OF cis_inj_on eq] i j n have "i = j" by (auto simp: field_simps)
  } note inj = this
  have "order x ?u = 1" unfolding root_unity_decomp[OF n]
    unfolding x n_split using inj
    by (subst order_prod_list, force, fastforce simp: order_monic_linear)
  with True show ?thesis by auto
qed

lemma order_prod_root_unity: assumes 0: "0 \<notin> set ks"
  shows "order (x :: complex) (prod_root_unity ks) = length (filter (\<lambda> k. x^k = 1) ks)"
proof -
  have "order x (prod_root_unity ks) = (\<Sum>k\<leftarrow>ks. order x (root_unity k))"
    unfolding prod_root_unity_def
    by (subst order_prod_list, insert 0, auto simp: o_def)
  also have "\<dots> = (\<Sum>k\<leftarrow>ks. (if x^k = 1 then 1 else 0))"
    by (rule arg_cong, rule map_cong, insert 0, force, intro order_root_unity, metis)
  also have "\<dots> = length (filter (\<lambda> k. x^k = 1) ks)"
    by (subst sum_list_map_filter'[symmetric], simp add: sum_list_triv)
  finally show ?thesis .
qed

lemma root_unity_witness: fixes xs :: "complex list"
  assumes "prod_list (map (\<lambda> x. [:-x,1:]) xs) = monom 1 n - 1"
  shows "x^n = 1 \<longleftrightarrow> x \<in> set xs"
proof -
  from assms have n0: "n \<noteq> 0" by (cases "n = 0", auto simp: prod_list_zero_iff)
  have "x \<in> set xs \<longleftrightarrow> poly (prod_list (map (\<lambda> x. [:-x,1:]) xs)) x = 0"
    unfolding poly_prod_list prod_list_zero_iff by auto
  also have "\<dots> \<longleftrightarrow> x^n = 1" using roots_of_unity(2)[OF n0] unfolding assms root_unity_def by auto
  finally show ?thesis by auto
qed

lemma root_unity_explicit: fixes x :: complex
  shows
    "(x ^ 1 = 1) \<longleftrightarrow> x = 1"
    "(x ^ 2 = 1) \<longleftrightarrow> (x \<in> {1, -1})"
    "(x ^ 3 = 1) \<longleftrightarrow> (x \<in> {1, Complex (-1/2) (sqrt 3 / 2), Complex (-1/2) (- sqrt 3 / 2)})"
    "(x ^ 4 = 1) \<longleftrightarrow> (x \<in> {1, -1, \<i>, - \<i>})"
proof -
  show "(x ^ 1 = 1) \<longleftrightarrow> x = 1"
    by (subst root_unity_witness[of "[1]"], code_simp, auto)
  show "(x ^ 2 = 1) \<longleftrightarrow> (x \<in> {1, -1})"
    by (subst root_unity_witness[of "[1,-1]"], code_simp, auto)
  show "(x ^ 4 = 1) \<longleftrightarrow> (x \<in> {1, -1, \<i>, - \<i>})"
    by (subst root_unity_witness[of "[1,-1, \<i>, - \<i>]"], code_simp, auto)
  have 3: "3 = Suc (Suc (Suc 0))" "1 = [:1:]" by auto
  show "(x ^ 3 = 1) \<longleftrightarrow> (x \<in> {1, Complex (-1/2) (sqrt 3 / 2), Complex (-1/2) (- sqrt 3 / 2)})"
    by (subst root_unity_witness[of
      "[1, Complex (-1/2) (sqrt 3 / 2), Complex (-1/2) (- sqrt 3 / 2)]"],
      auto simp: 3 monom_altdef complex_mult complex_eq_iff)
qed

definition primitive_root_unity :: "nat \<Rightarrow> 'a :: power \<Rightarrow> bool" where
  "primitive_root_unity k x = (k \<noteq> 0 \<and> x^k = 1 \<and> (\<forall> k' < k. k' \<noteq> 0 \<longrightarrow> x^k' \<noteq> 1))"

lemma primitive_root_unityD: assumes "primitive_root_unity k x"
  shows "k \<noteq> 0" "x^k = 1" "k' \<noteq> 0 \<Longrightarrow> x^k' = 1 \<Longrightarrow> k \<le> k'"
proof -
  note * = assms[unfolded primitive_root_unity_def]
  from * have **: "k' < k \<Longrightarrow> k' \<noteq> 0 \<Longrightarrow> x ^ k' \<noteq> 1" by auto
  show "k \<noteq> 0" "x^k = 1" using * by auto
  show "k' \<noteq> 0 \<Longrightarrow> x^k' = 1 \<Longrightarrow> k \<le> k'" using ** by force
qed

lemma primitive_root_unity_exists: assumes "k \<noteq> 0" "x ^ k = 1"
  shows "\<exists> k'. k' \<le> k \<and> primitive_root_unity k' x"
proof -
  let ?P = "\<lambda> k. x ^ k = 1 \<and> k \<noteq> 0"
  define k' where "k' = (LEAST k. ?P k)"
  from assms have Pk: "\<exists> k. ?P k" by auto
  from LeastI_ex[OF Pk, folded k'_def]
  have "k' \<noteq> 0" "x ^ k' = 1" by auto
  with not_less_Least[of _ ?P, folded k'_def]
  have "primitive_root_unity k' x" unfolding primitive_root_unity_def by auto
  with primitive_root_unityD(3)[OF this assms]
  show ?thesis by auto
qed

lemma primitive_root_unity_dvd: fixes x :: "complex"
  assumes k: "primitive_root_unity k x"
  shows "x ^ n = 1 \<longleftrightarrow> k dvd n"
proof
  assume "k dvd n" then obtain j where n: "n = k * j" unfolding dvd_def by auto
  have "x ^ n = (x ^ k) ^ j" unfolding n power_mult by simp
  also have "\<dots> = 1" unfolding primitive_root_unityD[OF k] by simp
  finally show "x ^ n = 1" .
next
  assume n: "x ^ n = 1"
  note k = primitive_root_unityD[OF k]
  show "k dvd n"
  proof (cases "n = 0")
    case n0: False
    from k(3)[OF n0] n have nk: "n \<ge> k" by force
    from roots_of_unity[OF k(1)] k(2) obtain i :: nat where xk: "x = cis (i * 2 * pi / k)"
      and ik: "i < k" by force
    from roots_of_unity[OF n0] n obtain j :: nat where xn: "x = cis (j * 2 * pi / n)"
      and jn: "j < n" by force
    have cop: "coprime i k"
    proof (rule gcd_eq_1_imp_coprime)
      from k(1) have "gcd i k \<noteq> 0" by auto
      from gcd_coprime_exists[OF this] this obtain i' k' g where
        *: "i = i' * g" "k = k' * g" "g \<noteq> 0" and g: "g = gcd i k" by blast
      from *(2) k(1) have k': "k' \<noteq> 0" by auto
      have "x = cis (i * 2 * pi / k)" by fact
      also have "i * 2 * pi / k = i' * 2 * pi / k'" unfolding * using *(3) by auto
      finally have "x ^ k' = 1" by (simp add: DeMoivre k')
      with k(3)[OF k'] have "k' \<ge> k" by linarith
      moreover with * k(1) have "g = 1" by auto
      then show "gcd i k = 1" by (simp add: g)
    qed
    from inj_onD[OF cis_inj_on xk[unfolded xn]] n0 k(1) ik jn
    have "j * real k = i * real n" by (auto simp: field_simps)
    hence "real (j * k) = real (i * n)" by simp
    hence eq: "j * k = i * n" by linarith
    with cop show "k dvd n"
      by (metis coprime_commute coprime_dvd_mult_right_iff dvd_triv_right)
  qed auto
qed

lemma primitive_root_unity_simple_computation:
  "primitive_root_unity k x  = (if k = 0 then False else
     x ^ k = 1 \<and> (\<forall> i \<in> {1 ..< k}. x ^ i \<noteq> 1))"
  unfolding primitive_root_unity_def by auto

lemma primitive_root_unity_explicit: fixes x :: complex
  shows "primitive_root_unity 1 x \<longleftrightarrow> x = 1"
    "primitive_root_unity 2 x \<longleftrightarrow> x = -1"
    "primitive_root_unity 3 x \<longleftrightarrow> (x \<in> {Complex (-1/2) (sqrt 3 / 2), Complex (-1/2) (- sqrt 3 / 2)})"
    "primitive_root_unity 4 x \<longleftrightarrow> (x \<in> {\<i>, - \<i>})"
proof (atomize(full), goal_cases)
  case 1
  {
    fix P :: "nat \<Rightarrow> bool"
    have *: "{1 ..< 2 :: nat} = {1}" "{1 ..< 3 :: nat} = {1,2}" "{1 ..< 4 :: nat} = {1,2,3}"
      by code_simp+
    have "(\<forall>i\<in> {1 ..< 2}. P i) = P 1" "(\<forall>i\<in> {1 ..< 3}. P i) \<longleftrightarrow> P 1 \<and> P 2"
      "(\<forall>i\<in> {1 ..< 4}. P i) \<longleftrightarrow> P 1 \<and> P 2 \<and> P 3"
      unfolding * by auto
  } note * = this
  show ?case unfolding primitive_root_unity_simple_computation root_unity_explicit *
    by (auto simp: complex_eq_iff)
qed

function decompose_prod_root_unity_main ::
  "'a :: field poly \<Rightarrow> nat \<Rightarrow> nat list \<times> 'a poly" where
  "decompose_prod_root_unity_main p k = (
    if k = 0 then ([], p) else
   let q = root_unity k in if q dvd p then if p = 0 then ([],0) else
     map_prod (Cons k) id (decompose_prod_root_unity_main (p div q) k) else
     decompose_prod_root_unity_main p (k - 1))"
  by pat_completeness auto

termination by (relation "measure (\<lambda> (p,k). degree p + k)", auto simp: degree_div_less)

declare decompose_prod_root_unity_main.simps[simp del]

lemma decompose_prod_root_unity_main: fixes p :: "complex poly"
  assumes p: "p = prod_root_unity ks * f"
  and d: "decompose_prod_root_unity_main p k = (ks',g)"
  and f: "\<And> x. cmod x = 1 \<Longrightarrow> poly f x \<noteq> 0"
  and k: "\<And> k'. k' > k \<Longrightarrow> \<not> root_unity k' dvd p"
shows "p = prod_root_unity ks' * f \<and> f = g \<and> set ks = set ks'"
  using d p k
proof (induct p k arbitrary: ks ks' rule: decompose_prod_root_unity_main.induct)
  case (1 p k ks ks')
  note p = 1(4)
  note k = 1(5)
  from k[of "Suc k"] have p0: "p \<noteq> 0" by auto
  hence "p = 0 \<longleftrightarrow> False" by auto
  note d = 1(3)[unfolded decompose_prod_root_unity_main.simps[of p k] this if_False Let_def]
  from p0[unfolded p] have ks0: "0 \<notin> set ks" by simp
  from f[of 1] have f0: "f \<noteq> 0" by auto
  note IH = 1(1)[OF _ refl _ p0] 1(2)[OF _ refl]
  show ?case
  proof (cases "k = 0")
    case True
    with p k[unfolded this, of "hd ks"] p0 have "ks = []"
      by (cases ks, auto simp: prod_root_unity_def)
    with d p True show ?thesis by (auto simp: prod_root_unity_def)
  next
    case k0: False
    note IH = IH[OF k0]
    from k0 have "k = 0 \<longleftrightarrow> False" by auto
    note d = d[unfolded this if_False]
    let ?u = "root_unity k :: complex poly"
    show ?thesis
    proof (cases "?u dvd p")
      case True
      note IH = IH(1)[OF True]
      let ?call = "decompose_prod_root_unity_main (p div ?u) k"
      from True d obtain Ks where rec: "?call = (Ks,g)" and ks': "ks' = (k # Ks)"
        by (cases ?call, auto)
      from True have "?u dvd p \<longleftrightarrow> True" by simp
      note d = d[unfolded this if_True rec]
      let ?x = "cis (2 * pi / k)"
      have rt: "poly ?u ?x = 0" unfolding poly_root_unity using cis_times_2pi[of 1]
        by (simp add: DeMoivre)
      with True have "poly p ?x = 0" unfolding dvd_def by auto
      from this[unfolded p] f[of ?x] rt have "poly (prod_root_unity ks) ?x = 0"
        unfolding poly_root_unity by auto
      from this[unfolded poly_prod_root_unity] ks0 obtain k' where k': "k' \<in> set ks"
        and rt: "?x ^ k' = 1" and k'0: "k' \<noteq> 0" by auto
      let ?u' = "root_unity k' :: complex poly"
      from k' rt k'0 have rtk': "poly ?u' ?x = 0" unfolding poly_root_unity by auto
      {
        let ?phi = " k' * (2 * pi / k)"
        assume "k' < k"
        hence "0 < ?phi" "?phi < 2 * pi" using k0 k'0 by (auto simp: field_simps)
        from cis_plus_2pi_neq_1[OF this] rtk'
        have False unfolding poly_root_unity DeMoivre ..
      }
      hence kk': "k \<le> k'" by presburger
      {
        assume "k' > k"
        from k[OF this, unfolded p]
        have "\<not> ?u' dvd prod_root_unity ks" using dvd_mult2 by auto
        with k' have False unfolding prod_root_unity_def
          using prod_list_dvd[of ?u' "map root_unity ks"] by auto
      }
      with kk' have kk': "k' = k" by presburger
      with k' have "k \<in> set ks" by auto
      from split_list[OF this] obtain ks1 ks2 where ks: "ks = ks1 @ k # ks2" by auto
      hence "p div ?u = (?u * (prod_root_unity (ks1 @ ks2) * f)) div ?u"
        by (simp add: ac_simps p prod_root_unity_def)
      also have "\<dots> = prod_root_unity (ks1 @ ks2) * f"
        by (rule nonzero_mult_div_cancel_left, insert k0, auto)
      finally have id: "p div ?u = prod_root_unity (ks1 @ ks2) * f" .
      from d have ks': "ks' = k # Ks" by auto
      have "k < k' \<Longrightarrow> \<not> root_unity k' dvd p div ?u" for k'
        using k[of k'] True by (metis dvd_div_mult_self dvd_mult2)
      from IH[OF rec id this]
      have id: "p div root_unity k = prod_root_unity Ks * f" and
        *: "f = g \<and> set (ks1 @ ks2) = set Ks" by auto
      from arg_cong[OF id, of "\<lambda> x. x * ?u"] True
      have "p = prod_root_unity Ks * f * root_unity k" by auto
      thus ?thesis using * unfolding ks ks' by (auto simp: prod_root_unity_def)
    next
      case False
      from d False have "decompose_prod_root_unity_main p (k - 1) = (ks',g)" by auto
      note IH = IH(2)[OF False this p]
      have k: "k - 1 < k' \<Longrightarrow> \<not> root_unity k' dvd p" for k' using False k[of k'] k0
        by (cases "k' = k", auto)
      show ?thesis by (rule IH, insert False k, auto)
    qed
  qed
qed

definition "decompose_prod_root_unity p = decompose_prod_root_unity_main p (degree p)"

lemma decompose_prod_root_unity: fixes p :: "complex poly"
  assumes p: "p = prod_root_unity ks * f"
  and d: "decompose_prod_root_unity p = (ks',g)"
  and f: "\<And> x. cmod x = 1 \<Longrightarrow> poly f x \<noteq> 0"
  and p0: "p \<noteq> 0"
shows "p = prod_root_unity ks' * f \<and> f = g \<and> set ks = set ks'"
proof (rule decompose_prod_root_unity_main[OF p d[unfolded decompose_prod_root_unity_def] f])
  fix k
  assume deg: "degree p < k"
  hence "degree p < degree (root_unity k)" by simp
  with p0 show "\<not> root_unity k dvd p"
    by (simp add: poly_divides_conv0)
qed

lemma (in comm_ring_hom) hom_root_unity: "map_poly hom (root_unity n) = root_unity n"
proof -
  interpret p: map_poly_comm_ring_hom hom ..
  show ?thesis unfolding root_unity_def
    by (simp add: hom_distribs)
qed

lemma (in idom_hom) hom_prod_root_unity: "map_poly hom (prod_root_unity n) = prod_root_unity n"
proof -
  interpret p: map_poly_comm_ring_hom hom ..
  show ?thesis unfolding prod_root_unity_def p.hom_prod_list map_map o_def hom_root_unity ..
qed

lemma (in field_hom) hom_decompose_prod_root_unity_main:
  "decompose_prod_root_unity_main (map_poly hom p) k = map_prod id (map_poly hom)
    (decompose_prod_root_unity_main p k)"
proof (induct p k rule: decompose_prod_root_unity_main.induct)
  case (1 p k)
  let ?h = "map_poly hom"
  let ?p = "?h p"
  let ?u = "root_unity k :: 'a poly"
  let ?u' = "root_unity k :: 'b poly"
  interpret p: map_poly_inj_idom_divide_hom hom ..
  have u': "?u' = ?h ?u" unfolding hom_root_unity ..
  note simp = decompose_prod_root_unity_main.simps
  let ?rec1 = "decompose_prod_root_unity_main (p div ?u) k"
  have 0: "?p = 0 \<longleftrightarrow> p = 0" by simp
  show ?case
    unfolding simp[of ?p k] simp[of p k] if_distrib[of "map_prod id ?h"] Let_def u'
    unfolding 0 p.hom_div[symmetric] p.hom_dvd_iff
    by (rule if_cong[OF refl], force, rule if_cong[OF refl if_cong[OF refl]], force,
     (subst 1(1), auto, cases ?rec1, auto)[1],
     (subst 1(2), auto))
qed

lemma (in field_hom) hom_decompose_prod_root_unity:
  "decompose_prod_root_unity (map_poly hom p) = map_prod id (map_poly hom)
    (decompose_prod_root_unity p)"
  unfolding decompose_prod_root_unity_def
  by (subst hom_decompose_prod_root_unity_main, simp)


end
