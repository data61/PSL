(*  
    Author:      René Thiemann 
                 Akihisa Yamada
                 Jose Divason
    License:     BSD
*)
section \<open>Missing Polynomial\<close>

text \<open>The theory contains some basic results on polynomials which have not been detected in
  the distribution, especially on linear factors and degrees.\<close>

theory Missing_Polynomial
imports 
  "HOL-Computational_Algebra.Polynomial_Factorial"
  Missing_Unsorted
begin

subsection \<open>Basic Properties\<close>

lemma degree_0_id: assumes "degree p = 0"
  shows "[: coeff p 0 :] = p" 
proof -
  have "\<And> x. 0 \<noteq> Suc x" by auto 
  thus ?thesis using assms
  by (metis coeff_pCons_0 degree_pCons_eq_if pCons_cases)
qed

lemma degree0_coeffs: "degree p = 0 \<Longrightarrow>
  \<exists> a. p = [: a :]"
  by (metis degree_pCons_eq_if old.nat.distinct(2) pCons_cases)

lemma degree1_coeffs: "degree p = 1 \<Longrightarrow>
  \<exists> a b. p = [: b, a :] \<and> a \<noteq> 0" 
  by (metis One_nat_def degree_pCons_eq_if nat.inject old.nat.distinct(2) pCons_0_0 pCons_cases)

lemma degree2_coeffs: "degree p = 2 \<Longrightarrow>
  \<exists> a b c. p = [: c, b, a :] \<and> a \<noteq> 0"
  by (metis Suc_1 Suc_neq_Zero degree1_coeffs degree_pCons_eq_if nat.inject pCons_cases)

lemma poly_zero:
  fixes p :: "'a :: comm_ring_1 poly"
  assumes x: "poly p x = 0" shows "p = 0 \<longleftrightarrow> degree p = 0"
proof
  assume degp: "degree p = 0"
  hence "poly p x = coeff p (degree p)" by(subst degree_0_id[OF degp,symmetric], simp)
  hence "coeff p (degree p) = 0" using x by auto
  thus "p = 0" by auto
qed auto

lemma coeff_monom_Suc: "coeff (monom a (Suc d) * p) (Suc i) = coeff (monom a d * p) i"
  by (simp add: monom_Suc)

lemma coeff_sum_monom:
  assumes n: "n \<le> d"
  shows "coeff (\<Sum>i\<le>d. monom (f i) i) n = f n" (is "?l = _")
proof -
  have "?l = (\<Sum>i\<le>d. coeff (monom (f i) i) n)" (is "_ = sum ?cmf _")
    using coeff_sum.
  also have "{..d} = insert n ({..d}-{n})" using n by auto
    hence "sum ?cmf {..d} = sum ?cmf ..." by auto
  also have "... = sum ?cmf ({..d}-{n}) + ?cmf n" by (subst sum.insert,auto)
  also have "sum ?cmf ({..d}-{n}) = 0" by (subst sum.neutral, auto)
  finally show ?thesis by simp
qed

lemma linear_poly_root: "(a :: 'a :: comm_ring_1) \<in> set as \<Longrightarrow> poly (\<Prod> a \<leftarrow> as. [: - a, 1:]) a = 0"
proof (induct as)
  case (Cons b as)
  show ?case
  proof (cases "a = b")
    case False
    with Cons have "a \<in> set as" by auto
    from Cons(1)[OF this] show ?thesis by simp
  qed simp
qed simp

lemma degree_lcoeff_sum: assumes deg: "degree (f q) = n"
  and fin: "finite S" and q: "q \<in> S" and degle: "\<And> p . p \<in> S - {q} \<Longrightarrow> degree (f p) < n"
  and cong: "coeff (f q) n = c"
  shows "degree (sum f S) = n \<and> coeff (sum f S) n = c"
proof (cases "S = {q}")
  case True
  thus ?thesis using deg cong by simp
next
  case False
  with q obtain p where "p \<in> S - {q}" by auto
  from degle[OF this] have n: "n > 0" by auto
  have "degree (sum f S) = degree (f q + sum f (S - {q}))"
    unfolding sum.remove[OF fin q] ..
  also have "\<dots> = degree (f q)"
  proof (rule degree_add_eq_left)
    have "degree (sum f (S - {q})) \<le> n - 1"
    proof (rule degree_sum_le)
      fix p
      show "p \<in> S - {q} \<Longrightarrow> degree (f p) \<le> n - 1"
        using degle[of p] by auto
    qed (insert fin, auto)
    also have "\<dots> < n" using n by simp
    finally show "degree (sum f (S - {q})) < degree (f q)" unfolding deg .
  qed
  finally show ?thesis unfolding deg[symmetric] cong[symmetric]
  proof (rule conjI)
    have id: "(\<Sum>x\<in>S - {q}. coeff (f x) (degree (f q))) = 0"
      by (rule sum.neutral, rule ballI, rule coeff_eq_0[OF degle[folded deg]])
    show "coeff (sum f S) (degree (f q)) = coeff (f q) (degree (f q))"
      unfolding coeff_sum
      by (subst sum.remove[OF _ q], unfold id, insert fin, auto)
  qed
qed

lemma degree_sum_list_le: "(\<And> p . p \<in> set ps \<Longrightarrow> degree p \<le> n)
  \<Longrightarrow> degree (sum_list ps) \<le> n"
proof (induct ps)
  case (Cons p ps)
  hence "degree (sum_list ps) \<le> n" "degree p \<le> n" by auto
  thus ?case unfolding sum_list.Cons by (metis degree_add_le)
qed simp

lemma degree_prod_list_le: "degree (prod_list ps) \<le> sum_list (map degree ps)"
proof (induct ps)
  case (Cons p ps)
  show ?case unfolding prod_list.Cons
    by (rule order.trans[OF degree_mult_le], insert Cons, auto)
qed simp

lemma smult_sum: "smult (\<Sum>i \<in> S. f i) p = (\<Sum>i \<in> S. smult (f i) p)"
  by (induct S rule: infinite_finite_induct, auto simp: smult_add_left)


lemma range_coeff: "range (coeff p) = insert 0 (set (coeffs p))" 
  by (metis nth_default_coeffs_eq range_nth_default)

lemma smult_power: "(smult a p) ^ n = smult (a ^ n) (p ^ n)"
  by (induct n, auto simp: field_simps)

lemma poly_sum_list: "poly (sum_list ps) x = sum_list (map (\<lambda> p. poly p x) ps)"
  by (induct ps, auto)

lemma poly_prod_list: "poly (prod_list ps) x = prod_list (map (\<lambda> p. poly p x) ps)"
  by (induct ps, auto)

lemma sum_list_neutral: "(\<And> x. x \<in> set xs \<Longrightarrow> x = 0) \<Longrightarrow> sum_list xs = 0"
  by (induct xs, auto)

lemma prod_list_neutral: "(\<And> x. x \<in> set xs \<Longrightarrow> x = 1) \<Longrightarrow> prod_list xs = 1"
  by (induct xs, auto)

lemma (in comm_monoid_mult) prod_list_map_remove1:
  "x \<in> set xs \<Longrightarrow> prod_list (map f xs) = f x * prod_list (map f (remove1 x xs))"
  by (induct xs) (auto simp add: ac_simps)

lemma poly_as_sum:
  fixes p :: "'a::comm_semiring_1 poly"
  shows "poly p x = (\<Sum>i\<le>degree p. x ^ i * coeff p i)"
  unfolding poly_altdef by (simp add: ac_simps)

lemma poly_prod_0: "finite ps \<Longrightarrow> poly (prod f ps) x = (0 :: 'a :: field) \<longleftrightarrow> (\<exists> p \<in> ps. poly (f p) x = 0)"
  by (induct ps rule: finite_induct, auto)

lemma coeff_monom_mult:
  shows "coeff (monom a d * p) i =
    (if d \<le> i then a * coeff p (i-d) else 0)" (is "?l = ?r")
proof (cases "d \<le> i")
  case False thus ?thesis unfolding coeff_mult by simp
  next case True
    let ?f = "\<lambda>j. coeff (monom a d) j * coeff p (i - j)"
    have "\<And>j. j \<in> {0..i} - {d} \<Longrightarrow> ?f j = 0" by auto
    hence "0 = (\<Sum>j \<in> {0..i} - {d}. ?f j)" by auto
    also have "... + ?f d = (\<Sum>j \<in> insert d ({0..i} - {d}). ?f j)"
      by(subst sum.insert, auto)
    also have "... = (\<Sum>j \<in> {0..i}. ?f j)" by (subst insert_Diff, insert True, auto)
    also have "... = (\<Sum>j\<le>i. ?f j)" by (rule sum.cong, auto)
    also have "... = ?l" unfolding coeff_mult ..
    finally show ?thesis using True by auto
qed

lemma poly_eqI2:
  assumes "degree p = degree q" and "\<And>i. i \<le> degree p \<Longrightarrow> coeff p i = coeff q i"
  shows "p = q"
  apply(rule poly_eqI) by (metis assms le_degree)

text \<open>A nice extension rule for polynomials.\<close>
lemma poly_ext[intro]:
  fixes p q :: "'a :: {ring_char_0, idom} poly"
  assumes "\<And>x. poly p x = poly q x" shows "p = q"
  unfolding poly_eq_poly_eq_iff[symmetric]
  using assms by (rule ext)

text \<open>Copied from non-negative variants.\<close>
lemma coeff_linear_power_neg[simp]:
  fixes a :: "'a::comm_ring_1"
  shows "coeff ([:a, -1:] ^ n) n = (-1)^n"
apply (induct n, simp_all)
apply (subst coeff_eq_0)
apply (auto intro: le_less_trans degree_power_le)
done

lemma degree_linear_power_neg[simp]:
  fixes a :: "'a::{idom,comm_ring_1}"
  shows "degree ([:a, -1:] ^ n) = n"
apply (rule order_antisym)
apply (rule ord_le_eq_trans [OF degree_power_le], simp)
apply (rule le_degree)
unfolding coeff_linear_power_neg
apply (auto)
done


subsection \<open>Polynomial Composition\<close>

lemmas [simp] = pcompose_pCons

lemma pcompose_eq_0: fixes q :: "'a :: idom poly"
  assumes q: "degree q \<noteq> 0"
  shows "p \<circ>\<^sub>p q = 0 \<longleftrightarrow> p = 0"
proof (induct p)
  case 0
  show ?case by auto
next
  case (pCons a p)
  have id: "(pCons a p) \<circ>\<^sub>p q = [:a:] + q * (p \<circ>\<^sub>p q)" by simp
  show ?case 
  proof (cases "p = 0")
    case True
    show ?thesis unfolding id unfolding True by simp
  next
    case False
    with pCons(2) have "p \<circ>\<^sub>p q \<noteq> 0" by auto
    from degree_mult_eq[OF _ this, of q] q have "degree (q * (p \<circ>\<^sub>p q)) \<noteq> 0" by force
    hence deg: "degree ([:a:] + q * (p \<circ>\<^sub>p q)) \<noteq> 0"
      by (subst degree_add_eq_right, auto)
    show ?thesis unfolding id using False deg by auto
  qed
qed

declare degree_pcompose[simp]

subsection \<open>Monic Polynomials\<close>

abbreviation monic where "monic p \<equiv> coeff p (degree p) = 1"

lemma unit_factor_field [simp]: 
  "unit_factor (x :: 'a :: {field,normalization_semidom}) = x"
  by (cases "is_unit x") (auto simp: is_unit_unit_factor dvd_field_iff)

lemma poly_gcd_monic: 
  fixes p :: "'a :: {field,factorial_ring_gcd} poly"
  assumes "p \<noteq> 0 \<or> q \<noteq> 0"
  shows   "monic (gcd p q)"
proof -
  from assms have "1 = unit_factor (gcd p q)" by (auto simp: unit_factor_gcd)
  also have "\<dots> = [:lead_coeff (gcd p q):]" unfolding unit_factor_poly_def
    by (simp add: monom_0)
  finally show ?thesis
    by (metis coeff_pCons_0 degree_1 lead_coeff_1)
qed

lemma normalize_monic: "monic p \<Longrightarrow> normalize p = p"
  by (simp add: normalize_poly_eq_map_poly is_unit_unit_factor)

lemma lcoeff_monic_mult: assumes monic: "monic (p :: 'a :: comm_semiring_1 poly)"
  shows "coeff (p * q) (degree p + degree q) = coeff q (degree q)"
proof -
  let ?pqi = "\<lambda> i. coeff p i * coeff q (degree p + degree q - i)" 
  have "coeff (p * q) (degree p + degree q) = 
    (\<Sum>i\<le>degree p + degree q. ?pqi i)"
    unfolding coeff_mult by simp
  also have "\<dots> = ?pqi (degree p) + (sum ?pqi ({.. degree p + degree q} - {degree p}))"
    by (subst sum.remove[of _ "degree p"], auto)
  also have "?pqi (degree p) = coeff q (degree q)" unfolding monic by simp
  also have "(sum ?pqi ({.. degree p + degree q} - {degree p})) = 0"
  proof (rule sum.neutral, intro ballI)
    fix d
    assume d: "d \<in> {.. degree p + degree q} - {degree p}"
    show "?pqi d = 0"
    proof (cases "d < degree p")
      case True
      hence "degree p + degree q - d > degree q" by auto
      hence "coeff q (degree p + degree q - d) = 0" by (rule coeff_eq_0)
      thus ?thesis by simp
    next
      case False
      with d have "d > degree p" by auto
      hence "coeff p d = 0" by (rule coeff_eq_0)
      thus ?thesis by simp
    qed
  qed
  finally show ?thesis by simp
qed

lemma degree_monic_mult: assumes monic: "monic (p :: 'a :: comm_semiring_1 poly)"
  and q: "q \<noteq> 0"
  shows "degree (p * q) = degree p + degree q"
proof -
  have "degree p + degree q \<ge> degree (p * q)" by (rule degree_mult_le)
  also have "degree p + degree q \<le> degree (p * q)"
  proof -
    from q have cq: "coeff q (degree q) \<noteq> 0" by auto
    hence "coeff (p * q) (degree p + degree q) \<noteq> 0" unfolding lcoeff_monic_mult[OF monic] .
    thus "degree (p * q) \<ge> degree p + degree q" by (rule le_degree)
  qed
  finally show ?thesis .
qed

lemma degree_prod_sum_monic: assumes
  S: "finite S"
  and nzd: "0 \<notin> (degree o f) ` S"
  and monic: "(\<And> a . a \<in> S \<Longrightarrow> monic (f a))"
  shows "degree (prod f S) = (sum (degree o f) S) \<and> coeff (prod f S) (sum (degree o f) S) = 1"
proof -
  from S nzd monic 
  have "degree (prod f S) = sum (degree \<circ> f) S 
  \<and> (S \<noteq> {} \<longrightarrow> degree (prod f S) \<noteq> 0 \<and> prod f S \<noteq> 0) \<and> coeff (prod f S) (sum (degree o f) S) = 1"
  proof (induct S rule: finite_induct)
    case (insert a S)
    have IH1: "degree (prod f S) = sum (degree o f) S"
      using insert by auto
    have IH2: "coeff (prod f S) (degree (prod f S)) = 1"
      using insert by auto
    have id: "degree (prod f (insert a S)) = sum (degree \<circ> f) (insert a S)
      \<and> coeff (prod f (insert a S)) (sum (degree o f) (insert a S)) = 1"
    proof (cases "S = {}")
      case False
      with insert have nz: "prod f S \<noteq> 0" by auto
      from insert have monic: "coeff (f a) (degree (f a)) = 1" by auto
      have id: "(degree \<circ> f) a = degree (f a)" by simp
      show ?thesis unfolding prod.insert[OF insert(1-2)] sum.insert[OF insert(1-2)] id
        unfolding degree_monic_mult[OF monic nz] 
        unfolding IH1[symmetric]
        unfolding lcoeff_monic_mult[OF monic] IH2 by simp
    qed (insert insert, auto)
    show ?case using id unfolding sum.insert[OF insert(1-2)] using insert by auto
  qed simp
  thus ?thesis by auto
qed 

lemma degree_prod_monic: 
  assumes "\<And> i. i < n \<Longrightarrow> degree (f i :: 'a :: comm_semiring_1 poly) = 1"
    and "\<And> i. i < n \<Longrightarrow> coeff (f i) 1 = 1"
  shows "degree (prod f {0 ..< n}) = n \<and> coeff (prod f {0 ..< n}) n = 1"
proof -
  from degree_prod_sum_monic[of "{0 ..< n}" f] show ?thesis using assms by force
qed

lemma degree_prod_sum_lt_n: assumes "\<And> i. i < n \<Longrightarrow> degree (f i :: 'a :: comm_semiring_1 poly) \<le> 1"
  and i: "i < n" and fi: "degree (f i) = 0"
  shows "degree (prod f {0 ..< n}) < n"
proof -
  have "degree (prod f {0 ..< n}) \<le> sum (degree o f) {0 ..< n}"
    by (rule degree_prod_sum_le, auto)
  also have "sum (degree o f) {0 ..< n} = (degree o f) i + sum (degree o f) ({0 ..< n} - {i})"
    by (rule sum.remove, insert i, auto)
  also have "(degree o f) i = 0" using fi by simp
  also have "sum (degree o f) ({0 ..< n} - {i}) \<le> sum (\<lambda> _. 1) ({0 ..< n} - {i})"
    by (rule sum_mono, insert assms, auto)
  also have "\<dots> = n - 1" using i by simp
  also have "\<dots> < n" using i by simp
  finally show ?thesis by simp
qed

lemma degree_linear_factors: "degree (\<Prod> a \<leftarrow> as. [: f a, 1:]) = length as"
proof (induct as)
  case (Cons b as) note IH = this
  have id: "(\<Prod>a\<leftarrow>b # as. [:f a, 1:]) = [:f b,1 :] * (\<Prod>a\<leftarrow>as. [:f a, 1:])" by simp
  show ?case unfolding id
    by (subst degree_monic_mult, insert IH, auto)
qed simp

lemma monic_mult:
  fixes p q :: "'a :: idom poly"
  assumes "monic p" "monic q"
  shows "monic (p * q)"
proof -
  from assms have nz: "p \<noteq> 0" "q \<noteq> 0" by auto
  show ?thesis unfolding degree_mult_eq[OF nz] coeff_mult_degree_sum
    using assms by simp
qed

lemma monic_factor:
  fixes p q :: "'a :: idom poly"
  assumes "monic (p * q)" "monic p"
  shows "monic q"
proof -
  from assms have nz: "p \<noteq> 0" "q \<noteq> 0" by auto
  from assms[unfolded degree_mult_eq[OF nz] coeff_mult_degree_sum \<open>monic p\<close>]
  show ?thesis by simp
qed

lemma monic_prod:
  fixes f :: "'a \<Rightarrow> 'b :: idom poly"
  assumes "\<And> a. a \<in> as \<Longrightarrow> monic (f a)"
  shows "monic (prod f as)" using assms
proof (induct as rule: infinite_finite_induct)
  case (insert a as)
  hence id: "prod f (insert a as) = f a * prod f as" 
    and *: "monic (f a)" "monic (prod f as)" by auto
  show ?case unfolding id by (rule monic_mult[OF *])
qed auto

lemma monic_prod_list:
  fixes as :: "'a :: idom poly list"
  assumes "\<And> a. a \<in> set as \<Longrightarrow> monic a"
  shows "monic (prod_list as)" using assms
  by (induct as, auto intro: monic_mult)

lemma monic_power:
  assumes "monic (p :: 'a :: idom poly)"
  shows "monic (p ^ n)"
  by (induct n, insert assms, auto intro: monic_mult)

lemma monic_prod_list_pow: "monic (\<Prod>(x::'a::idom, i)\<leftarrow>xis. [:- x, 1:] ^ Suc i)"
proof (rule monic_prod_list, goal_cases)
  case (1 a)
  then obtain x i where a: "a = [:-x, 1:]^Suc i" by force
  show "monic a" unfolding a
    by (rule monic_power, auto)
qed

lemma monic_degree_0: "monic p \<Longrightarrow> (degree p = 0) = (p = 1)"
  using le_degree poly_eq_iff by force

subsection \<open>Roots\<close>

text \<open>The following proof structure is completely similar to the one
  of @{thm poly_roots_finite}.\<close>

lemma poly_roots_degree:
  fixes p :: "'a::idom poly"
  shows "p \<noteq> 0 \<Longrightarrow> card {x. poly p x = 0} \<le> degree p"
proof (induct n \<equiv> "degree p" arbitrary: p)
  case (0 p)
  then obtain a where "a \<noteq> 0" and "p = [:a:]"
    by (cases p, simp split: if_splits)
  then show ?case by simp
next
  case (Suc n p)
  show ?case
  proof (cases "\<exists>x. poly p x = 0")
    case True
    then obtain a where a: "poly p a = 0" ..
    then have "[:-a, 1:] dvd p" by (simp only: poly_eq_0_iff_dvd)
    then obtain k where k: "p = [:-a, 1:] * k" ..
    with \<open>p \<noteq> 0\<close> have "k \<noteq> 0" by auto
    with k have "degree p = Suc (degree k)"
      by (simp add: degree_mult_eq del: mult_pCons_left)
    with \<open>Suc n = degree p\<close> have "n = degree k" by simp
    from Suc.hyps(1)[OF this \<open>k \<noteq> 0\<close>]
    have le: "card {x. poly k x = 0} \<le> degree k" .
    have "card {x. poly p x = 0} = card {x. poly ([:-a, 1:] * k) x = 0}" unfolding k ..
    also have "{x. poly ([:-a, 1:] * k) x = 0} = insert a {x. poly k x = 0}"
      by auto
    also have "card \<dots> \<le> Suc (card {x. poly k x = 0})" 
      unfolding card_insert_if[OF poly_roots_finite[OF \<open>k \<noteq> 0\<close>]] by simp
    also have "\<dots> \<le> Suc (degree k)" using le by auto
    finally show ?thesis using \<open>degree p = Suc (degree k)\<close> by simp
  qed simp
qed

lemma poly_root_factor: "(poly ([: r, 1:] * q) (k :: 'a :: idom) = 0) = (k = -r \<or> poly q k = 0)" (is ?one)
  "(poly (q * [: r, 1:]) k = 0) = (k = -r \<or> poly q k = 0)" (is ?two)
  "(poly [: r, 1 :] k = 0) = (k = -r)" (is ?three)
proof -
  have [simp]: "r + k = 0 \<Longrightarrow> k = - r" by (simp add: minus_unique)
  show ?one unfolding poly_mult by auto
  show ?two unfolding poly_mult by auto
  show ?three by auto
qed

lemma poly_root_constant: "c \<noteq> 0 \<Longrightarrow> (poly (p * [:c:]) (k :: 'a :: idom) = 0) = (poly p k = 0)"
  unfolding poly_mult by auto


lemma poly_linear_exp_linear_factors_rev: 
  "([:b,1:])^(length (filter ((=) b) as)) dvd (\<Prod> (a :: 'a :: comm_ring_1) \<leftarrow> as. [: a, 1:])"
proof (induct as)
  case (Cons a as)
  let ?ls = "length (filter ((=) b) (a # as))"
  let ?l = "length (filter ((=) b) as)"
  have prod: "(\<Prod> a \<leftarrow> Cons a as. [: a, 1:]) = [: a, 1 :] * (\<Prod> a \<leftarrow> as. [: a, 1:])" by simp
  show ?case
  proof (cases "a = b")
    case False
    hence len: "?ls = ?l" by simp
    show ?thesis unfolding prod len using Cons by (rule dvd_mult)
  next
    case True
    hence len: "[: b, 1 :] ^ ?ls = [: a, 1 :] * [: b, 1 :] ^ ?l" by simp
    show ?thesis unfolding prod len using Cons using dvd_refl mult_dvd_mono by blast
  qed
qed simp

lemma order_max: assumes dvd: "[: -a, 1 :] ^ k dvd p" and p: "p \<noteq> 0"
  shows "k \<le> order a p"
proof (rule ccontr)
  assume "\<not> ?thesis"
  hence "\<exists> j. k = Suc (order a p + j)" by arith
  then obtain j where k: "k = Suc (order a p + j)" by auto
  have "[: -a, 1 :] ^ Suc (order a p) dvd p"
    by (rule power_le_dvd[OF dvd[unfolded k]], simp)
  with order_2[OF p, of a] show False by blast
qed


subsection \<open>Divisibility\<close>

context
  assumes "SORT_CONSTRAINT('a :: idom)"
begin
lemma poly_linear_linear_factor: assumes 
  dvd: "[:b,1:] dvd (\<Prod> (a :: 'a) \<leftarrow> as. [: a, 1:])"
  shows "b \<in> set as"
proof -
  let ?p = "\<lambda> as. (\<Prod> a \<leftarrow> as. [: a, 1:])"
  let ?b = "[:b,1:]"
  from assms[unfolded dvd_def] obtain p where id: "?p as = ?b * p" ..
  from arg_cong[OF id, of "\<lambda> p. poly p (-b)"]
  have "poly (?p as) (-b) = 0" by simp
  thus ?thesis
  proof (induct as)
    case (Cons a as)
    have "?p (a # as) = [:a,1:] * ?p as" by simp
    from Cons(2)[unfolded this] have "poly (?p as) (-b) = 0 \<or> (a - b) = 0" by simp
    with Cons(1) show ?case by auto
  qed simp
qed

lemma poly_linear_exp_linear_factors: 
  assumes dvd: "([:b,1:])^n dvd (\<Prod> (a :: 'a) \<leftarrow> as. [: a, 1:])"
  shows "length (filter ((=) b) as) \<ge> n"
proof -
  let ?p = "\<lambda> as. (\<Prod> a \<leftarrow> as. [: a, 1:])"
  let ?b = "[:b,1:]"
  from dvd show ?thesis
  proof (induct n arbitrary: as)
    case (Suc n as)
    have bs: "?b ^ Suc n = ?b * ?b ^ n" by simp
    from poly_linear_linear_factor[OF dvd_mult_left[OF Suc(2)[unfolded bs]], 
      unfolded in_set_conv_decomp]
    obtain as1 as2 where as: "as = as1 @ b # as2" by auto
    have "?p as = [:b,1:] * ?p (as1 @ as2)" unfolding as
    proof (induct as1)
      case (Cons a as1)
      have "?p (a # as1 @ b # as2) = [:a,1:] * ?p (as1 @ b # as2)" by simp
      also have "?p (as1 @ b # as2) = [:b,1:] * ?p (as1 @ as2)" unfolding Cons by simp
      also have "[:a,1:] * \<dots> = [:b,1:] * ([:a,1:] * ?p (as1 @ as2))" 
        by (metis (no_types, lifting) mult.left_commute)
      finally show ?case by simp
    qed simp
    from Suc(2)[unfolded bs this dvd_mult_cancel_left]
    have "?b ^ n dvd ?p (as1 @ as2)" by simp
    from Suc(1)[OF this] show ?case unfolding as by simp
  qed simp    
qed
end

lemma const_poly_dvd: "([:a:] dvd [:b:]) = (a dvd b)"
proof
  assume "a dvd b"
  then obtain c where "b = a * c" unfolding dvd_def by auto
  hence "[:b:] = [:a:] * [: c:]" by (auto simp: ac_simps)
  thus "[:a:] dvd [:b:]" unfolding dvd_def by blast
next
  assume "[:a:] dvd [:b:]"
  then obtain pc where "[:b:] =  [:a:] * pc" unfolding dvd_def by blast
  from arg_cong[OF this, of "\<lambda> p. coeff p 0", unfolded coeff_mult]
  have "b = a * coeff pc 0" by auto
  thus "a dvd b" unfolding dvd_def by blast
qed

lemma const_poly_dvd_1 [simp]:
  "[:a:] dvd 1 \<longleftrightarrow> a dvd 1"
  by (metis const_poly_dvd one_poly_eq_simps(2))

lemma poly_dvd_1:
  fixes p :: "'a :: {comm_semiring_1,semiring_no_zero_divisors} poly"
  shows "p dvd 1 \<longleftrightarrow> degree p = 0 \<and> coeff p 0 dvd 1"
proof (cases "degree p = 0")
  case False
  with divides_degree[of p 1] show ?thesis by auto
next
  case True
  from degree0_coeffs[OF this] obtain a where p: "p = [:a:]" by auto
  show ?thesis unfolding p by auto
qed

text \<open>Degree based version of irreducibility.\<close>

definition irreducible\<^sub>d :: "'a :: comm_semiring_1 poly \<Rightarrow> bool" where
  "irreducible\<^sub>d p = (degree p > 0 \<and> (\<forall> q r. degree q < degree p \<longrightarrow> degree r < degree p \<longrightarrow> p \<noteq> q * r))"

lemma irreducible\<^sub>dI [intro]:
  assumes 1: "degree p > 0"
    and 2: "\<And>q r. degree q > 0 \<Longrightarrow> degree q < degree p \<Longrightarrow> degree r > 0 \<Longrightarrow> degree r < degree p \<Longrightarrow> p = q * r \<Longrightarrow> False"
  shows "irreducible\<^sub>d p"
proof (unfold irreducible\<^sub>d_def, intro conjI allI impI notI 1)
  fix q r
  assume "degree q < degree p" and "degree r < degree p" and "p = q * r"
  with degree_mult_le[of q r]
  show False by (intro 2, auto)
qed

lemma irreducible\<^sub>dI2:
  fixes p :: "'a::{comm_semiring_1,semiring_no_zero_divisors} poly"
  assumes deg: "degree p > 0" and ndvd: "\<And> q. degree q > 0 \<Longrightarrow> degree q \<le> degree p div 2 \<Longrightarrow> \<not> q dvd p"
  shows "irreducible\<^sub>d p"
proof (rule ccontr)
  assume "\<not> ?thesis"
  from this[unfolded irreducible\<^sub>d_def] deg obtain q r where dq: "degree q < degree p" and dr: "degree r < degree p"
    and p: "p = q * r" by auto
  from deg have p0: "p \<noteq> 0" by auto
  with p have "q \<noteq> 0" "r \<noteq> 0" by auto
  from degree_mult_eq[OF this] p have dp: "degree p = degree q + degree r" by simp
  show False
  proof (cases "degree q \<le> degree p div 2")
    case True
    from ndvd[OF _ True] dq dr dp p show False by auto
  next
    case False
    with dp have dr: "degree r \<le> degree p div 2" by auto
    from p have dvd: "r dvd p" by auto
    from ndvd[OF _ dr] dvd dp dq show False by auto
  qed
qed

lemma reducible\<^sub>dI:
  assumes "degree p > 0 \<Longrightarrow> \<exists>q r. degree q < degree p \<and> degree r < degree p \<and> p = q * r"
  shows "\<not> irreducible\<^sub>d p"
  using assms by (auto simp: irreducible\<^sub>d_def)

lemma irreducible\<^sub>dE [elim]:
  assumes "irreducible\<^sub>d p"
    and "degree p > 0 \<Longrightarrow> (\<And>q r. degree q < degree p \<Longrightarrow> degree r < degree p \<Longrightarrow> p \<noteq> q * r) \<Longrightarrow> thesis"
  shows thesis
  using assms by (auto simp: irreducible\<^sub>d_def)

lemma reducible\<^sub>dE [elim]:
  assumes red: "\<not> irreducible\<^sub>d p"
    and 1: "degree p = 0 \<Longrightarrow> thesis"
    and 2: "\<And>q r. degree q > 0 \<Longrightarrow> degree q < degree p \<Longrightarrow> degree r > 0 \<Longrightarrow> degree r < degree p \<Longrightarrow> p = q * r \<Longrightarrow> thesis"
  shows thesis
  using red[unfolded irreducible\<^sub>d_def de_Morgan_conj not_not not_all not_imp]
proof (elim disjE exE conjE)
  show "\<not>degree p > 0 \<Longrightarrow> thesis" using 1 by auto
next
  fix q r
  assume "degree q < degree p" and "degree r < degree p" and "p = q * r"
  with degree_mult_le[of q r]
  show thesis by (intro 2, auto)
qed

lemma irreducible\<^sub>dD:
  assumes "irreducible\<^sub>d p"
  shows "degree p > 0" "\<And>q r. degree q < degree p \<Longrightarrow> degree r < degree p \<Longrightarrow> p \<noteq> q * r"
  using assms unfolding irreducible\<^sub>d_def by auto

theorem irreducible\<^sub>d_factorization_exists:
  assumes "degree p > 0"
  shows "\<exists>fs. fs \<noteq> [] \<and> (\<forall>f \<in> set fs. irreducible\<^sub>d f \<and> degree f \<le> degree p) \<and> p = prod_list fs"
    and "\<not>irreducible\<^sub>d p \<Longrightarrow> \<exists>fs. length fs > 1 \<and> (\<forall>f \<in> set fs. irreducible\<^sub>d f \<and> degree f < degree p) \<and> p = prod_list fs"
proof (atomize(full), insert assms, induct "degree p" arbitrary:p rule: less_induct)
  case less
  then have deg_f: "degree p > 0" by auto
  show ?case
  proof (cases "irreducible\<^sub>d p")
    case True
    then have "set [p] \<subseteq> Collect irreducible\<^sub>d" "p = prod_list [p]" by auto
    with True show ?thesis by (auto intro: exI[of _ "[p]"])
  next
    case False
    with deg_f obtain g h
    where deg_g: "degree g < degree p" "degree g > 0"
      and deg_h: "degree h < degree p" "degree h > 0"
      and f_gh: "p = g * h" by auto
    from less.hyps[OF deg_g] less.hyps[OF deg_h]
    obtain gs hs
    where emp: "length gs > 0" "length hs > 0"
      and "\<forall>f \<in> set gs. irreducible\<^sub>d f \<and> degree f \<le> degree g" "g = prod_list gs"
      and "\<forall>f \<in> set hs. irreducible\<^sub>d f \<and> degree f \<le> degree h" "h = prod_list hs" by auto
    with f_gh deg_g deg_h
    have len: "length (gs@hs) > 1"
     and mem: "\<forall>f \<in> set (gs@hs). irreducible\<^sub>d f \<and> degree f < degree p"
     and p: "p = prod_list (gs@hs)" by (auto simp del: length_greater_0_conv)
    with False show ?thesis by (auto intro!: exI[of _ "gs@hs"] simp: less_imp_le)
  qed
qed

lemma irreducible\<^sub>d_factor:
  fixes p :: "'a::{comm_semiring_1,semiring_no_zero_divisors} poly"
  assumes "degree p > 0"
  shows "\<exists> q r. irreducible\<^sub>d q \<and> p = q * r \<and> degree r < degree p" using assms
proof (induct "degree p" arbitrary: p rule: less_induct)
  case (less p)
  show ?case
  proof (cases "irreducible\<^sub>d p")
    case False
    with less(2) obtain q r
    where q: "degree q < degree p" "degree q > 0"
      and r: "degree r < degree p" "degree r > 0"
      and p: "p = q * r"
      by auto
    from less(1)[OF q] obtain s t where IH: "irreducible\<^sub>d s" "q = s * t" by auto
    from p have p: "p = s * (t * r)" unfolding IH by (simp add: ac_simps)
    from less(2) have "p \<noteq> 0" by auto
    hence "degree p = degree s + (degree (t * r))" unfolding p 
      by (subst degree_mult_eq, insert p, auto)
    with irreducible\<^sub>dD[OF IH(1)] have "degree p > degree (t * r)" by auto
    with p IH show ?thesis by auto
  next
    case True
    show ?thesis
      by (rule exI[of _ p], rule exI[of _ 1], insert True less(2), auto)
  qed
qed

context mult_zero begin (* least class with times and zero *)

definition zero_divisor where "zero_divisor a \<equiv> \<exists>b. b \<noteq> 0 \<and> a * b = 0"

lemma zero_divisorI[intro]:
  assumes "b \<noteq> 0" and "a * b = 0" shows "zero_divisor a"
  using assms by (auto simp: zero_divisor_def)

lemma zero_divisorE[elim]:
  assumes "zero_divisor a"
    and "\<And>b. b \<noteq> 0 \<Longrightarrow> a * b = 0 \<Longrightarrow> thesis"
  shows thesis
  using assms by (auto simp: zero_divisor_def)

end

lemma zero_divisor_0[simp]:
  "zero_divisor (0::'a::{mult_zero,zero_neq_one})" (* No need for one! *)
  by (auto intro!: zero_divisorI[of 1])

lemma not_zero_divisor_1:
  "\<not> zero_divisor (1 :: 'a :: {monoid_mult,mult_zero})" (* No need for associativity! *)
  by auto

lemma zero_divisor_iff_eq_0[simp]:
  fixes a :: "'a :: {semiring_no_zero_divisors, zero_neq_one}"
  shows "zero_divisor a \<longleftrightarrow> a = 0" by auto

lemma mult_eq_0_not_zero_divisor_left[simp]:
  fixes a b :: "'a :: mult_zero"
  assumes "\<not> zero_divisor a"
  shows "a * b = 0 \<longleftrightarrow> b = 0"
  using assms unfolding zero_divisor_def by force

lemma mult_eq_0_not_zero_divisor_right[simp]:
  fixes a b :: "'a :: {ab_semigroup_mult,mult_zero}" (* No need for associativity! *)
  assumes "\<not> zero_divisor b"
  shows "a * b = 0 \<longleftrightarrow> a = 0"
  using assms unfolding zero_divisor_def by (force simp: ac_simps)

lemma degree_smult_not_zero_divisor_left[simp]:
  assumes "\<not> zero_divisor c"
  shows "degree (smult c p) = degree p"
proof(cases "p = 0")
  case False
  then have "coeff (smult c p) (degree p) \<noteq> 0" using assms by auto
  from le_degree[OF this] degree_smult_le[of c p]
  show ?thesis by auto
qed auto

lemma degree_smult_not_zero_divisor_right[simp]:
  assumes "\<not> zero_divisor (lead_coeff p)"
  shows "degree (smult c p) = (if c = 0 then 0 else degree p)"
proof(cases "c = 0")
  case False
  then have "coeff (smult c p) (degree p) \<noteq> 0" using assms by auto
  from le_degree[OF this] degree_smult_le[of c p]
  show ?thesis by auto
qed auto


lemma irreducible\<^sub>d_smult_not_zero_divisor_left:
  assumes c0: "\<not> zero_divisor c"
  assumes L: "irreducible\<^sub>d (smult c p)"
  shows "irreducible\<^sub>d p"
proof (intro irreducible\<^sub>dI)
  from L have "degree (smult c p) > 0" by auto
  also note degree_smult_le
  finally show "degree p > 0" by auto
  fix q r
  assume deg_q: "degree q < degree p"
    and deg_r: "degree r < degree p"
    and p_qr: "p = q * r"
  then have 1: "smult c p = smult c q * r" by auto
  note degree_smult_le[of c q]
  also note deg_q
  finally have 2: "degree (smult c q) < degree (smult c p)" using c0 by auto
  from deg_r have 3: "degree r < \<dots>" using c0 by auto
  from irreducible\<^sub>dD(2)[OF L 2 3] 1 show False by auto
qed

lemmas irreducible\<^sub>d_smultI =
  irreducible\<^sub>d_smult_not_zero_divisor_left
  [where 'a = "'a :: {comm_semiring_1,semiring_no_zero_divisors}", simplified]

lemma irreducible\<^sub>d_smult_not_zero_divisor_right:
  assumes p0: "\<not> zero_divisor (lead_coeff p)" and L: "irreducible\<^sub>d (smult c p)"
  shows "irreducible\<^sub>d p"
proof-
  from L have "c \<noteq> 0" by auto
  with p0 have [simp]: "degree (smult c p) = degree p" by simp
  show "irreducible\<^sub>d p"
  proof (intro iffI irreducible\<^sub>dI conjI)
    from L show "degree p > 0" by auto
    fix q r
    assume deg_q: "degree q < degree p"
      and deg_r: "degree r < degree p"
      and p_qr: "p = q * r"
    then have 1: "smult c p = smult c q * r" by auto
    note degree_smult_le[of c q]
    also note deg_q
    finally have 2: "degree (smult c q) < degree (smult c p)" by simp
    from deg_r have 3: "degree r < \<dots>" by simp
    from irreducible\<^sub>dD(2)[OF L 2 3] 1 show False by auto
  qed
qed

lemma zero_divisor_mult_left:
  fixes a b :: "'a :: {ab_semigroup_mult, mult_zero}"
  assumes "zero_divisor a"
  shows "zero_divisor (a * b)"
proof-
  from assms obtain c where c0: "c \<noteq> 0" and [simp]: "a * c = 0" by auto
  have "a * b * c = a * c * b" by (simp only: ac_simps)
  with c0 show ?thesis by auto
qed

lemma zero_divisor_mult_right:
  fixes a b :: "'a :: {semigroup_mult, mult_zero}"
  assumes "zero_divisor b"
  shows "zero_divisor (a * b)"
proof-
  from assms obtain c where c0: "c \<noteq> 0" and [simp]: "b * c = 0" by auto
  have "a * b * c = a * (b * c)" by (simp only: ac_simps)
  with c0 show ?thesis by auto
qed

lemma not_zero_divisor_mult:
  fixes a b :: "'a :: {ab_semigroup_mult, mult_zero}"
  assumes "\<not> zero_divisor (a * b)"
  shows "\<not> zero_divisor a" and "\<not> zero_divisor b"
  using assms by (auto dest: zero_divisor_mult_right zero_divisor_mult_left)

lemma zero_divisor_smult_left:
  assumes "zero_divisor a"
  shows "zero_divisor (smult a f)"
proof-
  from assms obtain b where b0: "b \<noteq> 0" and "a * b = 0" by auto
  then have "smult a f * [:b:] = 0" by (simp add: ac_simps)
  with b0 show ?thesis by (auto intro!: zero_divisorI[of "[:b:]"])
qed

lemma unit_not_zero_divisor:
  fixes a :: "'a :: {comm_monoid_mult, mult_zero}"
  assumes "a dvd 1"
  shows "\<not>zero_divisor a"
proof
  from assms obtain b where ab: "1 = a * b" by (elim dvdE)
  assume "zero_divisor a"
  then have "zero_divisor (1::'a)" by (unfold ab, intro zero_divisor_mult_left)
  then show False by auto
qed


lemma linear_irreducible\<^sub>d: assumes "degree p = 1"
  shows "irreducible\<^sub>d p"
  by (rule irreducible\<^sub>dI, insert assms, auto)

lemma irreducible\<^sub>d_dvd_smult:
  fixes p :: "'a::{comm_semiring_1,semiring_no_zero_divisors} poly"
  assumes "degree p > 0" "irreducible\<^sub>d q" "p dvd q"
  shows "\<exists> c. c \<noteq> 0 \<and> q = smult c p"
proof -
  from assms obtain r where q: "q = p * r" by (elim dvdE, auto)
  from degree_mult_eq[of p r] assms(1) q
  have "\<not> degree p < degree q" and nz: "p \<noteq> 0" "q \<noteq> 0"
    apply (metis assms(2) degree_mult_eq_0 gr_implies_not_zero irreducible\<^sub>dD(2) less_add_same_cancel2)
    using assms by auto
  hence deg: "degree p \<ge> degree q" by auto
  from \<open>p dvd q\<close> obtain k where q: "q = k * p" unfolding dvd_def by (auto simp: ac_simps)
  with nz have "k \<noteq> 0" by auto
  from deg[unfolded q degree_mult_eq[OF \<open>k \<noteq> 0\<close> \<open>p \<noteq> 0\<close> ]] have "degree k = 0" 
    unfolding q by auto 
  then obtain c where k: "k = [: c :]" by (metis degree_0_id)
  with \<open>k \<noteq> 0\<close> have "c \<noteq> 0" by auto
  have "q = smult c p" unfolding q k by simp
  with \<open>c \<noteq> 0\<close> show ?thesis by auto
qed

subsection \<open>Map over Polynomial Coefficients\<close>
lemma map_poly_simps:
  shows "map_poly f (pCons c p) =
    (if c = 0 \<and> p = 0 then 0 else pCons (f c) (map_poly f p))"
proof (cases "c = 0")
  case True note c0 = this show ?thesis
    proof (cases "p = 0")
      case True thus ?thesis using c0 unfolding map_poly_def by simp
      next case False thus ?thesis
        unfolding map_poly_def by auto
    qed
  next case False thus ?thesis
    unfolding map_poly_def by auto
qed

lemma map_poly_pCons[simp]:
  assumes "c \<noteq> 0 \<or> p \<noteq> 0"
  shows "map_poly f (pCons c p) = pCons (f c) (map_poly f p)"
  unfolding map_poly_simps using assms by auto

lemma map_poly_map_poly:
  assumes f0: "f 0 = 0"
  shows "map_poly f (map_poly g p) = map_poly (f \<circ> g) p"
proof (induct p)
  case (pCons a p) show ?case
  proof(cases "g a \<noteq> 0 \<or> map_poly g p \<noteq> 0")
    case True show ?thesis
      unfolding map_poly_pCons[OF pCons(1)]
      unfolding map_poly_pCons[OF True]
      unfolding pCons(2)
      by simp
  next
    case False then show ?thesis
      unfolding map_poly_pCons[OF pCons(1)]
      unfolding pCons(2)[symmetric]
      by (simp add: f0)
  qed
qed simp

lemma map_poly_zero:
  assumes f: "\<forall>c. f c = 0 \<longrightarrow> c = 0"
  shows [simp]: "map_poly f p = 0 \<longleftrightarrow> p = 0"
  by (induct p; auto simp: map_poly_simps f)

lemma map_poly_add:
  assumes h0: "h 0 = 0"
      and h_add: "\<forall>p q. h (p + q) = h p + h q"
  shows "map_poly h (p + q) = map_poly h p + map_poly h q"
proof (induct p arbitrary: q)
  case (pCons a p) note pIH = this
    show ?case
    proof(induct "q")
      case (pCons b q) note qIH = this
        show ?case
          unfolding map_poly_pCons[OF qIH(1)]
          unfolding map_poly_pCons[OF pIH(1)]
          unfolding add_pCons
          unfolding pIH(2)[symmetric]
          unfolding h_add[rule_format,symmetric]
          unfolding map_poly_simps using h0 by auto
    qed auto
qed auto

subsection \<open>Morphismic properties of @{term "pCons 0"}\<close>

lemma monom_pCons_0_monom:
  "monom (pCons 0 (monom a n)) d = map_poly (pCons 0) (monom (monom a n) d)"
  apply (induct d)
  unfolding monom_0 unfolding map_poly_simps apply simp
  unfolding monom_Suc map_poly_simps by auto

lemma pCons_0_add: "pCons 0 (p + q) = pCons 0 p + pCons 0 q" by auto

lemma sum_pCons_0_commute:
  "sum (\<lambda>i. pCons 0 (f i)) S = pCons 0 (sum f S)"
  by(induct S rule: infinite_finite_induct;simp)

lemma pCons_0_as_mult:
  fixes p:: "'a :: comm_semiring_1 poly"
  shows "pCons 0 p = [:0,1:] * p" by auto



subsection \<open>Misc\<close>

fun expand_powers :: "(nat \<times> 'a)list \<Rightarrow> 'a list" where
  "expand_powers [] = []"
| "expand_powers ((Suc n, a) # ps) = a # expand_powers ((n,a) # ps)"
| "expand_powers ((0,a) # ps) = expand_powers ps"

lemma expand_powers: fixes f :: "'a \<Rightarrow> 'b :: comm_ring_1"
  shows "(\<Prod> (n,a) \<leftarrow> n_as. f a ^ n) = (\<Prod> a \<leftarrow> expand_powers n_as. f a)"
  by (rule sym, induct n_as rule: expand_powers.induct, auto)

lemma poly_smult_zero_iff: fixes x :: "'a :: idom" 
  shows "(poly (smult a p) x = 0) = (a = 0 \<or> poly p x = 0)"
  by simp

lemma poly_prod_list_zero_iff: fixes x :: "'a :: idom" 
  shows "(poly (prod_list ps) x = 0) = (\<exists> p \<in> set ps. poly p x = 0)"
  by (induct ps, auto)

lemma poly_mult_zero_iff: fixes x :: "'a :: idom" 
  shows "(poly (p * q) x = 0) = (poly p x = 0 \<or> poly q x = 0)"
  by simp

lemma poly_power_zero_iff: fixes x :: "'a :: idom" 
  shows "(poly (p^n) x = 0) = (n \<noteq> 0 \<and> poly p x = 0)"
  by (cases n, auto)


lemma sum_monom_0_iff: assumes fin: "finite S"
  and g: "\<And> i j. g i = g j \<Longrightarrow> i = j"
  shows "sum (\<lambda> i. monom (f i) (g i)) S = 0 \<longleftrightarrow> (\<forall> i \<in> S. f i = 0)" (is "?l = ?r")
proof -
  {
    assume "\<not> ?r"
    then obtain i where i: "i \<in> S" and fi: "f i \<noteq> 0" by auto
    let ?g = "\<lambda> i. monom (f i) (g i)"
    have "coeff (sum ?g S) (g i) = f i + sum (\<lambda> j. coeff (?g j) (g i)) (S - {i})"
      by (unfold sum.remove[OF fin i], simp add: coeff_sum)
    also have "sum (\<lambda> j. coeff (?g j) (g i)) (S - {i}) = 0"
      by (rule sum.neutral, insert g, auto)
    finally have "coeff (sum ?g S) (g i) \<noteq> 0" using fi by auto
    hence "\<not> ?l" by auto
  }
  thus ?thesis by auto
qed

lemma degree_prod_list_eq: assumes "\<And> p. p \<in> set ps \<Longrightarrow> (p :: 'a :: idom poly) \<noteq> 0"
  shows "degree (prod_list ps) = sum_list (map degree ps)" using assms
proof (induct ps)
  case (Cons p ps)
  show ?case unfolding prod_list.Cons
    by (subst degree_mult_eq, insert Cons, auto simp: prod_list_zero_iff)
qed simp

lemma degree_power_eq: assumes p: "p \<noteq> 0"
  shows "degree (p ^ n) = degree (p :: 'a :: idom poly) * n"
proof (induct n)
  case (Suc n)
  from p have pn: "p ^ n \<noteq> 0" by auto
  show ?case using degree_mult_eq[OF p pn] Suc by auto
qed simp

lemma coeff_Poly: "coeff (Poly xs) i = (nth_default 0 xs i)"
  unfolding nth_default_coeffs_eq[of "Poly xs", symmetric] coeffs_Poly by simp

lemma rsquarefree_def': "rsquarefree p = (p \<noteq> 0 \<and> (\<forall>a. order a p \<le> 1))"
proof -
  have "\<And> a. order a p \<le> 1 \<longleftrightarrow> order a p = 0 \<or> order a p = 1" by linarith
  thus ?thesis unfolding rsquarefree_def by auto
qed

lemma order_prod_list: "(\<And> p. p \<in> set ps \<Longrightarrow> p \<noteq> 0) \<Longrightarrow> order x (prod_list ps) = sum_list (map (order x) ps)"
  by (induct ps, auto, subst order_mult, auto simp: prod_list_zero_iff)

lemma irreducible\<^sub>d_dvd_eq:
  fixes a b :: "'a::{comm_semiring_1,semiring_no_zero_divisors} poly"
  assumes "irreducible\<^sub>d a" and "irreducible\<^sub>d b"
    and "a dvd b"
    and "monic a" and "monic b" 
  shows "a = b"
  using assms
  by (metis (no_types, lifting) coeff_smult degree_smult_eq irreducible\<^sub>dD(1) irreducible\<^sub>d_dvd_smult 
    mult.right_neutral smult_1_left)

lemma monic_gcd_dvd:
  assumes fg: "f dvd g" and mon: "monic f" and gcd: "gcd g h \<in> {1, g}"
  shows "gcd f h \<in> {1, f}"
proof (cases "coprime g h")
  case True
  with dvd_refl have "coprime f h"
    using fg by (blast intro: coprime_divisors)
  then show ?thesis
    by simp
next
  case False
  with gcd have gcd: "gcd g h = g"
    by (simp add: coprime_iff_gcd_eq_1)
  with fg have "f dvd gcd g h"
    by simp
  then have "f dvd h"
    by simp
  then have "gcd f h = normalize f"
    by (simp add: gcd_proj1_iff)
  also have "normalize f = f"
    using mon by (rule normalize_monic)
  finally show ?thesis
    by simp
qed

lemma monom_power: "(monom a b)^n = monom (a^n) (b*n)" 
  by (induct n, auto simp add: mult_monom)

lemma poly_const_pow: "[:a:]^b = [:a^b:]"
  by (metis Groups.mult_ac(2) monom_0 monom_power mult_zero_right)

lemma degree_pderiv_le: "degree (pderiv f) \<le> degree f - 1" 
proof (rule ccontr)
  assume "\<not> ?thesis"
  hence ge: "degree (pderiv f) \<ge> Suc (degree f - 1)" by auto
  hence "pderiv f \<noteq> 0" by auto
  hence "coeff (pderiv f) (degree (pderiv f)) \<noteq> 0" by auto
  from this[unfolded coeff_pderiv]
  have "coeff f (Suc (degree (pderiv f))) \<noteq> 0" by auto
  moreover have "Suc (degree (pderiv f)) > degree f" using ge by auto
  ultimately show False by (simp add: coeff_eq_0)
qed

lemma map_div_is_smult_inverse: "map_poly (\<lambda>x. x / (a :: 'a :: field)) p = smult (inverse a) p" 
  unfolding smult_conv_map_poly
  by (simp add: divide_inverse_commute)

lemma normalize_poly_old_def:
  "normalize (f :: 'a :: {normalization_semidom,field} poly) = smult (inverse (unit_factor (lead_coeff f))) f"
  by (simp add: normalize_poly_eq_map_poly map_div_is_smult_inverse)

(* was in Euclidean_Algorithm in Number_Theory before, but has been removed *)
lemma poly_dvd_antisym:
  fixes p q :: "'b::idom poly"
  assumes coeff: "coeff p (degree p) = coeff q (degree q)"
  assumes dvd1: "p dvd q" and dvd2: "q dvd p" shows "p = q"
proof (cases "p = 0")
  case True with coeff show "p = q" by simp
next
  case False with coeff have "q \<noteq> 0" by auto
  have degree: "degree p = degree q"
    using \<open>p dvd q\<close> \<open>q dvd p\<close> \<open>p \<noteq> 0\<close> \<open>q \<noteq> 0\<close>
    by (intro order_antisym dvd_imp_degree_le)

  from \<open>p dvd q\<close> obtain a where a: "q = p * a" ..
  with \<open>q \<noteq> 0\<close> have "a \<noteq> 0" by auto
  with degree a \<open>p \<noteq> 0\<close> have "degree a = 0"
    by (simp add: degree_mult_eq)
  with coeff a show "p = q"
    by (cases a, auto split: if_splits)
qed

lemma coeff_f_0_code[code_unfold]: "coeff f 0 = (case coeffs f of [] \<Rightarrow> 0 | x # _ \<Rightarrow> x)" 
  by (cases f, auto simp: cCons_def)

lemma poly_compare_0_code[code_unfold]: "(f = 0) = (case coeffs f of [] \<Rightarrow> True | _ \<Rightarrow> False)" 
  using coeffs_eq_Nil list.disc_eq_case(1) by blast

text \<open>Getting more efficient code for abbreviation @{term lead_coeff}"\<close>

definition leading_coeff
  where [code_abbrev, simp]: "leading_coeff = lead_coeff" 

lemma leading_coeff_code [code]:
  "leading_coeff f = (let xs = coeffs f in if xs = [] then 0 else last xs)"
  by (simp add: last_coeffs_eq_coeff_degree)

lemma nth_coeffs_coeff: "i < length (coeffs f) \<Longrightarrow> coeffs f ! i = coeff f i"
  by (metis nth_default_coeffs_eq nth_default_def)

lemma degree_prod_eq_sum_degree:
fixes A :: "'a set"
and f :: "'a \<Rightarrow> 'b::field poly"
assumes f0: "\<forall>i\<in>A. f i \<noteq> 0"
shows "degree (\<Prod>i\<in>A. (f i)) = (\<Sum>i\<in>A. degree (f i))"
using f0
proof (induct A rule: infinite_finite_induct)
  case (insert x A)
  have "(\<Sum>i\<in>insert x A. degree (f i)) = degree (f x) + (\<Sum>i\<in>A. degree (f i))"
    by (simp add: insert.hyps(1) insert.hyps(2))
  also have "... = degree (f x) + degree (\<Prod>i\<in>A. (f i))"
    by (simp add: insert.hyps insert.prems)
  also have "... = degree (f x * (\<Prod>i\<in>A. (f i)))"
  proof (rule degree_mult_eq[symmetric])
    show "f x \<noteq> 0" using insert.prems by auto
    show "prod f A \<noteq> 0" by (simp add: insert.hyps(1) insert.prems)
  qed
  also have "... = degree (\<Prod>i\<in>insert x A. (f i))"
    by (simp add: insert.hyps)
  finally show ?case ..
qed auto

definition monom_mult :: "nat \<Rightarrow> 'a :: comm_semiring_1 poly \<Rightarrow> 'a poly"
  where "monom_mult n f = monom 1 n * f" 

lemma monom_mult_unfold [code_unfold]:
  "monom 1 n * f = monom_mult n f"
  "f * monom 1 n = monom_mult n f" 
  by (auto simp: monom_mult_def ac_simps)

lemma monom_mult_code [code abstract]:
  "coeffs (monom_mult n f) = (let xs = coeffs f in
    if xs = [] then xs else replicate n 0 @ xs)" 
  by (rule coeffs_eqI)
    (auto simp add: Let_def monom_mult_def coeff_monom_mult nth_default_append nth_default_coeffs_eq)

lemma coeff_pcompose_monom: fixes f :: "'a :: comm_ring_1 poly" 
  assumes n: "j < n" 
  shows "coeff (f \<circ>\<^sub>p monom 1 n) (n * i + j) = (if j = 0 then coeff f i else 0)"     
proof (induct f arbitrary: i)
  case (pCons a f i)
  note d = pcompose_pCons coeff_add coeff_monom_mult coeff_pCons
  show ?case 
  proof (cases i)
    case 0
    show ?thesis unfolding d 0 using n by (cases j, auto)
  next
    case (Suc ii)
    have id: "n * Suc ii + j - n = n * ii + j" using n by (simp add: diff_mult_distrib2)
    have id1: "(n \<le> n * Suc ii + j) = True" by auto
    have id2: "(case n * Suc ii + j of 0 \<Rightarrow> a | Suc x \<Rightarrow> coeff 0 x) = 0" using n
      by (cases "n * Suc ii + j", auto)
    show ?thesis unfolding d Suc id id1 id2 pCons(2) if_True by auto
  qed
qed auto

lemma coeff_pcompose_x_pow_n: fixes f :: "'a :: comm_ring_1 poly" 
  assumes n: "n \<noteq> 0" 
  shows "coeff (f \<circ>\<^sub>p monom 1 n) (n * i) = coeff f i"     
  using coeff_pcompose_monom[of 0 n f i] n by auto
        
lemma dvd_dvd_smult: "a dvd b \<Longrightarrow> f dvd g \<Longrightarrow> smult a f dvd smult b g"
  unfolding dvd_def by (metis mult_smult_left mult_smult_right smult_smult)

definition sdiv_poly :: "'a :: idom_divide poly \<Rightarrow> 'a \<Rightarrow> 'a poly" where
  "sdiv_poly p a = (map_poly (\<lambda> c. c div a) p)"  

lemma smult_map_poly: "smult a = map_poly ((*) a)"
  by (rule ext, rule poly_eqI, subst coeff_map_poly, auto)
  
lemma smult_exact_sdiv_poly: assumes "\<And> c. c \<in> set (coeffs p) \<Longrightarrow> a dvd c"
  shows "smult a (sdiv_poly p a) = p" 
  unfolding smult_map_poly sdiv_poly_def
  by (subst map_poly_map_poly,simp,rule map_poly_idI, insert assms, auto)

lemma coeff_sdiv_poly: "coeff (sdiv_poly f a) n = coeff f n div a" 
  unfolding sdiv_poly_def by (rule coeff_map_poly, auto)    

lemma poly_pinfty_ge:
  fixes p :: "real poly"
  assumes "lead_coeff p > 0" "degree p \<noteq> 0" 
  shows "\<exists>n. \<forall> x \<ge> n. poly p x \<ge> b"
proof -
  let ?p = "p - [:b - lead_coeff p :]" 
  have id: "lead_coeff ?p = lead_coeff p" using assms(2)
    by (cases p, auto)
  with assms(1) have "lead_coeff ?p > 0" by auto
  from poly_pinfty_gt_lc[OF this, unfolded id] obtain n
    where "\<And> x. x \<ge> n \<Longrightarrow> 0 \<le> poly p x - b" by auto
  thus ?thesis by auto
qed

lemma pderiv_sum: "pderiv (sum f I) = sum (\<lambda> i. (pderiv (f i))) I" 
  by (induct I rule: infinite_finite_induct, auto simp: pderiv_add)

lemma smult_sum2: "smult m (\<Sum>i \<in> S. f i) = (\<Sum>i \<in> S. smult m (f i))"
  by (induct S rule: infinite_finite_induct, auto simp add: smult_add_right)

lemma degree_mult_not_eq:
  "degree (f * g) \<noteq> degree f + degree g \<Longrightarrow> lead_coeff f * lead_coeff g = 0"
  by (rule ccontr, auto simp: coeff_mult_degree_sum degree_mult_le le_antisym le_degree)

lemma irreducible\<^sub>d_multD:
  fixes a b :: "'a :: {comm_semiring_1,semiring_no_zero_divisors} poly"
  assumes l: "irreducible\<^sub>d (a*b)"
  shows "degree a = 0 \<and> a \<noteq> 0 \<and> irreducible\<^sub>d b \<or> degree b = 0 \<and> b \<noteq> 0 \<and> irreducible\<^sub>d a"
proof-
  from l have a0: "a \<noteq> 0" and b0: "b \<noteq> 0" by auto
  note [simp] = degree_mult_eq[OF this]
  from l have "degree a = 0 \<or> degree b = 0" apply (unfold irreducible\<^sub>d_def) by force
  then show ?thesis
  proof(elim disjE)
    assume a: "degree a = 0"
    with l a0 have "irreducible\<^sub>d b"
      unfolding irreducible\<^sub>d_def
      by (smt add.left_neutral degree_mult_not_eq leading_coeff_0_iff sign_simps(4) mult_eq_0_iff)
    with a a0 show ?thesis by auto
  next
    assume b: "degree b = 0"
    with l b0 have "irreducible\<^sub>d a"
      unfolding irreducible\<^sub>d_def
      by (smt add_cancel_left_right degree_mult_eq degree_mult_eq_0 neq0_conv semiring_normalization_rules(16))
    with b b0 show ?thesis by auto
  qed
qed

lemma irreducible_connect_field[simp]:
  fixes f :: "'a :: field poly"
  shows "irreducible\<^sub>d f = irreducible f" (is "?l = ?r")
proof
  show "?r \<Longrightarrow> ?l"
    apply (intro irreducible\<^sub>dI, force simp:is_unit_iff_degree)
    by (auto dest!: irreducible_multD simp: poly_dvd_1)
next
  assume l: ?l
  show ?r
  proof (rule irreducibleI)
    from l show "f \<noteq> 0" "\<not> is_unit f" by (auto simp: poly_dvd_1)
    fix a b assume "f = a * b"
    from l[unfolded this]
    show "a dvd 1 \<or> b dvd 1" by (auto dest!: irreducible\<^sub>d_multD simp:is_unit_iff_degree)
  qed
qed

lemma is_unit_field_poly[simp]:
  fixes p :: "'a::field poly"
  shows "is_unit p \<longleftrightarrow> p \<noteq> 0 \<and> degree p = 0"
  by (cases "p=0", auto simp: is_unit_iff_degree)

lemma irreducible_smult_field[simp]:
  fixes c :: "'a :: field"
  shows "irreducible (smult c p) \<longleftrightarrow> c \<noteq> 0 \<and> irreducible p" (is "?L \<longleftrightarrow> ?R")
proof (intro iffI conjI irreducible\<^sub>d_smult_not_zero_divisor_left[of c p, simplified])
  assume "irreducible (smult c p)"
  then show "c \<noteq> 0" by auto
next
  assume ?R
  then have c0: "c \<noteq> 0" and irr: "irreducible p" by auto
  show ?L
  proof (fold irreducible_connect_field, intro irreducible\<^sub>dI, unfold degree_smult_eq if_not_P[OF c0])
    show "degree p > 0" using irr by auto
    fix q r
    from c0 have "p = smult (1/c) (smult c p)" by simp
    also assume "smult c p = q * r"
    finally have [simp]: "p = smult (1/c) \<dots>".
    assume main: "degree q < degree p" "degree r < degree p"
    have "\<not>irreducible\<^sub>d p" by (rule reducible\<^sub>dI, rule exI[of _ "smult (1/c) q"], rule exI[of _ r], insert irr c0 main, simp)
    with irr show False by auto
  qed
qed auto

lemma irreducible_monic_factor: fixes p :: "'a :: field poly" 
  assumes "degree p > 0" 
  shows "\<exists> q r. irreducible q \<and> p = q * r \<and> monic q"
proof -
  from irreducible\<^sub>d_factorization_exists[OF assms]
  obtain fs where "fs \<noteq> []" and "set fs \<subseteq> Collect irreducible" and "p = prod_list fs" by auto
  then have q: "irreducible (hd fs)" and p: "p = hd fs * prod_list (tl fs)" by (atomize(full), cases fs, auto)
  define c where "c = coeff (hd fs) (degree (hd fs))"
  from q have c: "c \<noteq> 0" unfolding c_def irreducible\<^sub>d_def by auto
  show ?thesis
    by (rule exI[of _ "smult (1/c) (hd fs)"], rule exI[of _ "smult c (prod_list (tl fs))"], unfold p,
    insert q c, auto simp: c_def)
qed

lemma monic_irreducible_factorization: fixes p :: "'a :: field poly" 
  shows "monic p \<Longrightarrow> 
  \<exists> as f. finite as \<and> p = prod (\<lambda> a. a ^ Suc (f a)) as \<and> as \<subseteq> {q. irreducible q \<and> monic q}"
proof (induct "degree p" arbitrary: p rule: less_induct)
  case (less p)
  show ?case
  proof (cases "degree p > 0")
    case False
    with less(2) have "p = 1" by (simp add: coeff_eq_0 poly_eq_iff)
    thus ?thesis by (intro exI[of _ "{}"], auto)
  next
    case True
    from irreducible\<^sub>d_factor[OF this] obtain q r where p: "p = q * r"
      and q: "irreducible q" and deg: "degree r < degree p" by auto
    hence q0: "q \<noteq> 0" by auto
    define c where "c = coeff q (degree q)"
    let ?q = "smult (1/c) q"
    let ?r = "smult c r"
    from q0 have c: "c \<noteq> 0" "1 / c \<noteq> 0" unfolding c_def by auto
    hence p: "p = ?q * ?r" unfolding p by auto
    have deg: "degree ?r < degree p" using c deg by auto
    let ?Q = "{q. irreducible q \<and> monic (q :: 'a poly)}"
    have mon: "monic ?q" unfolding c_def using q0 by auto
    from monic_factor[OF \<open>monic p\<close>[unfolded p] this] have "monic ?r" .
    from less(1)[OF deg this] obtain f as
      where as: "finite as" "?r = (\<Prod> a \<in>as. a ^ Suc (f a))"
        "as \<subseteq> ?Q" by blast
    from q c have irred: "irreducible ?q" by simp
    show ?thesis
    proof (cases "?q \<in> as")
      case False
      let ?as = "insert ?q as"
      let ?f = "\<lambda> a. if a = ?q then 0 else f a"
      have "p = ?q * (\<Prod> a \<in>as. a ^ Suc (f a))" unfolding p as by simp
      also have "(\<Prod> a \<in>as. a ^ Suc (f a)) = (\<Prod> a \<in>as. a ^ Suc (?f a))"
        by (rule prod.cong, insert False, auto)
      also have "?q * \<dots> = (\<Prod> a \<in> ?as. a ^ Suc (?f a))"
        by (subst prod.insert, insert as False, auto)
      finally have p: "p = (\<Prod> a \<in> ?as. a ^ Suc (?f a))" .
      from as(1) have fin: "finite ?as" by auto
      from as mon irred have Q: "?as \<subseteq> ?Q" by auto
      from fin p Q show ?thesis 
        by(intro exI[of _ ?as] exI[of _ ?f], auto)
    next
      case True
      let ?f = "\<lambda> a. if a = ?q then Suc (f a) else f a"
      have "p = ?q * (\<Prod> a \<in>as. a ^ Suc (f a))" unfolding p as by simp
      also have "(\<Prod> a \<in>as. a ^ Suc (f a)) = ?q ^ Suc (f ?q) * (\<Prod> a \<in>(as - {?q}). a ^ Suc (f a))"
        by (subst prod.remove[OF _ True], insert as, auto)
      also have "(\<Prod> a \<in>(as - {?q}). a ^ Suc (f a)) = (\<Prod> a \<in>(as - {?q}). a ^ Suc (?f a))"
        by (rule prod.cong, auto)
      also have "?q * (?q ^ Suc (f ?q) * \<dots> ) = ?q ^ Suc (?f ?q) * \<dots>"
        by (simp add: ac_simps)
      also have "\<dots> = (\<Prod> a \<in> as. a ^ Suc (?f a))"
        by (subst prod.remove[OF _ True], insert as, auto)
      finally have "p = (\<Prod> a \<in> as. a ^ Suc (?f a))" .
      with as show ?thesis 
        by (intro exI[of _ as] exI[of _ ?f], auto)
    qed
  qed
qed

lemma monic_irreducible_gcd: 
  "monic (f::'a::{field,euclidean_ring_gcd} poly) \<Longrightarrow> irreducible f \<Longrightarrow> gcd f u \<in> {1,f}"
  by (metis gcd_dvd1 irreducible_altdef insertCI is_unit_gcd_iff poly_dvd_antisym poly_gcd_monic)
end
