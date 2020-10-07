(*
   File:      Pi_Transcendental_Polynomial_Library
   Author:    Manuel Eberl, TU München

   Various facts about univariate polynomials and some other things that probably belong in 
   the distribution.
*)
section \<open>Preliminary facts\<close>
theory Pi_Transcendental_Polynomial_Library
  imports "HOL-Computational_Algebra.Computational_Algebra"
begin

(* TODO: Move all this *)
lemma Ints_sum: "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> \<int>) \<Longrightarrow> sum f A \<in> \<int>"
  by (induction A rule: infinite_finite_induct) auto

lemma Ints_prod: "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> \<int>) \<Longrightarrow> prod f A \<in> \<int>"
  by (induction A rule: infinite_finite_induct) auto

lemma sum_in_Rats [intro]: "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> \<rat>) \<Longrightarrow> sum f A \<in> \<rat>"
  by (induction A rule: infinite_finite_induct) auto

lemma prod_in_Rats [intro]: "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> \<rat>) \<Longrightarrow> prod f A \<in> \<rat>"
  by (induction A rule: infinite_finite_induct) auto

lemma poly_cnj: "cnj (poly p z) = poly (map_poly cnj p) (cnj z)"
  by (simp add: poly_altdef degree_map_poly coeff_map_poly)

lemma poly_cnj_real:
  assumes "\<And>n. poly.coeff p n \<in> \<real>"
  shows   "cnj (poly p z) = poly p (cnj z)"
proof -
  from assms have "map_poly cnj p = p"
    by (intro poly_eqI) (auto simp: coeff_map_poly Reals_cnj_iff)
  with poly_cnj[of p z] show ?thesis by simp
qed

lemma real_poly_cnj_root_iff:
  assumes "\<And>n. poly.coeff p n \<in> \<real>"
  shows   "poly p (cnj z) = 0 \<longleftrightarrow> poly p z = 0"
proof -
  have "poly p (cnj z) = cnj (poly p z)"
    by (simp add: poly_cnj_real assms)
  also have "\<dots> = 0 \<longleftrightarrow> poly p z = 0" by simp
  finally show ?thesis .
qed

lemma coeff_pcompose_linear:
  fixes p :: "'a :: comm_semiring_1 poly"
  shows "coeff (pcompose p [:0, c:]) i = c ^ i * coeff p i"
  by (induction p arbitrary: i) (auto simp: pcompose_pCons coeff_pCons mult_ac split: nat.splits)

lemma coeff_pCons': "poly.coeff (pCons c p) n = (if n = 0 then c else poly.coeff p (n - 1))"
  by transfer'(auto split: nat.splits)

lemma prod_smult: "(\<Prod>x\<in>A. Polynomial.smult (c x) (p x)) = Polynomial.smult (prod c A) (prod p A)"
  by (induction A rule: infinite_finite_induct) (auto simp: mult_ac)

lemma degree_higher_pderiv: "Polynomial.degree ((pderiv ^^ n) p) = Polynomial.degree p - n"
  for p :: "'a::{comm_semiring_1,semiring_no_zero_divisors,semiring_char_0} poly"
  by (induction n) (auto simp: degree_pderiv)
  
lemma sum_to_poly: "(\<Sum>x\<in>A. [:f x:]) = [:\<Sum>x\<in>A. f x:]"
  by (induction A rule: infinite_finite_induct) auto

lemma diff_to_poly: "[:c:] - [:d:] = [:c - d:]"
  by (simp add: poly_eq_iff mult_ac)

lemma mult_to_poly: "[:c:] * [:d:] = [:c * d:]"
  by (simp add: poly_eq_iff mult_ac)

lemma prod_to_poly: "(\<Prod>x\<in>A. [:f x:]) = [:\<Prod>x\<in>A. f x:]"
  by (induction A rule: infinite_finite_induct) (auto simp: mult_to_poly mult_ac)

lemma coeff_mult_0: "poly.coeff (p * q) 0 = poly.coeff p 0 * poly.coeff q 0"
  by (simp add: coeff_mult)

lemma card_poly_roots_bound:
  fixes p :: "'a::{comm_ring_1,ring_no_zero_divisors} poly"
  assumes "p \<noteq> 0"
  shows   "card {x. poly p x = 0} \<le> degree p"
using assms
proof (induction "degree p" arbitrary: p rule: less_induct)
  case (less p)
  show ?case
  proof (cases "\<exists>x. poly p x = 0")
    case False
    hence "{x. poly p x = 0} = {}" by blast
    thus ?thesis by simp
  next
    case True
    then obtain x where x: "poly p x = 0" by blast
    hence "[:-x, 1:] dvd p" by (subst (asm) poly_eq_0_iff_dvd)
    then obtain q where q: "p = [:-x, 1:] * q" by (auto simp: dvd_def)
    with \<open>p \<noteq> 0\<close> have [simp]: "q \<noteq> 0" by auto
    have deg: "degree p = Suc (degree q)"
      by (subst q, subst degree_mult_eq) auto
    have "card {x. poly p x = 0} \<le> card (insert x {x. poly q x = 0})"
      by (intro card_mono) (auto intro: poly_roots_finite simp: q)
    also have "\<dots> \<le> Suc (card {x. poly q x = 0})"
      by (rule card_insert_le_m1) auto
    also from deg have  "card {x. poly q x = 0} \<le> degree q"
      using \<open>p \<noteq> 0\<close> and q by (intro less) auto
    also have "Suc \<dots> = degree p" by (simp add: deg)
    finally show ?thesis by - simp_all
  qed
qed

lemma poly_eqI_degree:
  fixes p q :: "'a :: {comm_ring_1, ring_no_zero_divisors} poly"
  assumes "\<And>x. x \<in> A \<Longrightarrow> poly p x = poly q x"
  assumes "card A > degree p" "card A > degree q"
  shows   "p = q"
proof (rule ccontr)
  assume neq: "p \<noteq> q"
  have "degree (p - q) \<le> max (degree p) (degree q)"
    by (rule degree_diff_le_max)
  also from assms have "\<dots> < card A" by linarith
  also have "\<dots> \<le> card {x. poly (p - q) x = 0}"
    using neq and assms by (intro card_mono poly_roots_finite) auto
  finally have "degree (p - q) < card {x. poly (p - q) x = 0}" .
  moreover have "degree (p - q) \<ge> card {x. poly (p - q) x = 0}"
    using neq by (intro card_poly_roots_bound) auto
  ultimately show False by linarith
qed  

lemma poly_root_order_induct [case_names 0 no_roots root]:
  fixes p :: "'a :: idom poly"
  assumes "P 0" "\<And>p. (\<And>x. poly p x \<noteq> 0) \<Longrightarrow> P p" 
          "\<And>p x n. n > 0 \<Longrightarrow> poly p x \<noteq> 0 \<Longrightarrow> P p \<Longrightarrow> P ([:-x, 1:] ^ n * p)"
  shows   "P p"
proof (induction "degree p" arbitrary: p rule: less_induct)
  case (less p)
  consider "p = 0" | "p \<noteq> 0" "\<exists>x. poly p x = 0" | "\<And>x. poly p x \<noteq> 0" by blast
  thus ?case
  proof cases
    case 3
    with assms(2)[of p] show ?thesis by simp
  next
    case 2
    then obtain x where x: "poly p x = 0" by auto
    have "[:-x, 1:] ^ order x p dvd p" by (intro order_1)
    then obtain q where q: "p = [:-x, 1:] ^ order x p * q" by (auto simp: dvd_def)
    with 2 have [simp]: "q \<noteq> 0" by auto
    have order_pos: "order x p > 0"
      using \<open>p \<noteq> 0\<close> and x by (auto simp: order_root)
    have "order x p = order x p + order x q"
      by (subst q, subst order_mult) (auto simp: order_power_n_n)
    hence [simp]: "order x q = 0" by simp
    have deg: "degree p = order x p + degree q"
      by (subst q, subst degree_mult_eq) (auto simp: degree_power_eq)
    with order_pos have "degree q < degree p" by simp
    hence "P q" by (rule less)
    with order_pos have "P ([:-x, 1:] ^ order x p * q)"
      by (intro assms(3)) (auto simp: order_root)
    with q show ?thesis by simp
  qed (simp_all add: assms(1))
qed

lemma complex_poly_decompose:
  "smult (lead_coeff p) (\<Prod>z|poly p z = 0. [:-z, 1:] ^ order z p) = (p :: complex poly)"
proof (induction p rule: poly_root_order_induct)
  case (no_roots p)
  show ?case
  proof (cases "degree p = 0")
    case False
    hence "\<not>constant (poly p)" by (subst constant_degree)
    with fundamental_theorem_of_algebra and no_roots show ?thesis by blast
  qed (auto elim!: degree_eq_zeroE)
next
  case (root p x n)
  from root have *: "{z. poly ([:- x, 1:] ^ n * p) z = 0} = insert x {z. poly p z = 0}"
    by auto
  have "smult (lead_coeff ([:-x, 1:] ^ n * p)) 
           (\<Prod>z|poly ([:-x,1:] ^ n * p) z = 0. [:-z, 1:] ^ order z ([:- x, 1:] ^ n * p)) = 
        [:- x, 1:] ^ order x ([:- x, 1:] ^ n * p) * 
          smult (lead_coeff p) (\<Prod>z\<in>{z. poly p z = 0}. [:- z, 1:] ^ order z ([:- x, 1:] ^ n * p))"
    by (subst *, subst prod.insert) 
       (insert root, auto intro: poly_roots_finite simp: mult_ac lead_coeff_mult lead_coeff_power)
  also have "order x ([:- x, 1:] ^ n * p) = n"
    using root by (subst order_mult) (auto simp: order_power_n_n order_0I)
  also have "(\<Prod>z\<in>{z. poly p z = 0}. [:- z, 1:] ^ order z ([:- x, 1:] ^ n * p)) =
               (\<Prod>z\<in>{z. poly p z = 0}. [:- z, 1:] ^ order z p)"
  proof (intro prod.cong refl, goal_cases)
    case (1 y)
    with root have "order y ([:-x,1:] ^ n) = 0" by (intro order_0I) auto 
    thus ?case using root by (subst order_mult) auto
  qed
  also note root.IH
  finally show ?case .
qed simp_all

lemma order_pos_iff: "p \<noteq> 0 \<Longrightarrow> order a p > 0 \<longleftrightarrow> poly p a = 0"
  using order_root[of p a] by auto

lift_definition poly_roots_mset :: "('a :: idom) poly \<Rightarrow> 'a multiset" is
  "\<lambda>p x. if p = 0 then 0 else Polynomial.order x p"
proof -
  fix p :: "'a poly"
  show "(\<lambda>x. if p = 0 then 0 else order x p) \<in> multiset"
    by (cases "p = 0")
       (auto simp: multiset_def order_pos_iff intro: finite_subset[OF _ poly_roots_finite[of p]])
qed

lemma poly_roots_mset_0 [simp]: "poly_roots_mset 0 = {#}"
  by transfer' auto

lemma count_poly_roots_mset [simp]:
  "p \<noteq> 0 \<Longrightarrow> count (poly_roots_mset p) a = order a p"
  by transfer' auto

lemma set_count_poly_roots_mset [simp]:
   "p \<noteq> 0 \<Longrightarrow> set_mset (poly_roots_mset p) = {x. poly p x = 0}"
  by (auto simp: set_mset_def order_pos_iff)


lemma image_prod_mset_multiplicity:
  "prod_mset (image_mset f M) = prod (\<lambda>x. f x ^ count M x) (set_mset M)"
proof (induction M)
  case (add x M)
  show ?case
  proof (cases "x \<in> set_mset M")
    case True
    have "(\<Prod>y\<in>set_mset (add_mset x M). f y ^ count (add_mset x M) y) = 
            (\<Prod>y\<in>set_mset M. (if y = x then f x else 1) * f y ^ count M y)"
      using True add by (intro prod.cong) auto
    also have "\<dots> = f x * (\<Prod>y\<in>set_mset M. f y ^ count M y)"
      using True by (subst prod.distrib) auto
    also note add.IH [symmetric]
    finally show ?thesis using True by simp
  next
    case False
    hence "(\<Prod>y\<in>set_mset (add_mset x M). f y ^ count (add_mset x M) y) =
              f x * (\<Prod>y\<in>set_mset M. f y ^ count (add_mset x M) y)"
      by (auto simp: not_in_iff)
    also have "(\<Prod>y\<in>set_mset M. f y ^ count (add_mset x M) y) = 
                 (\<Prod>y\<in>set_mset M. f y ^ count M y)"
      using False by (intro prod.cong) auto
    also note add.IH [symmetric]
    finally show ?thesis by simp
  qed
qed auto


lemma complex_poly_decompose_multiset:
  "smult (lead_coeff p) (\<Prod>x\<in>#poly_roots_mset p. [:-x, 1:]) = (p :: complex poly)"
proof (cases "p = 0")
  case False
  hence "(\<Prod>x\<in>#poly_roots_mset p. [:-x, 1:]) = (\<Prod>x | poly p x = 0. [:-x, 1:] ^ order x p)"
    by (subst image_prod_mset_multiplicity) simp_all
  also have "smult (lead_coeff p) \<dots> = p"
    by (rule complex_poly_decompose)
  finally show ?thesis .
qed auto

lemma (in monoid_add) prod_list_prod_nth:
  "prod_list xs = (\<Prod>i=0..<length xs. xs ! i)"
proof -
  have "xs = map (\<lambda>i. xs ! i) [0..<length xs]"
    by (simp add: map_nth)
  also have "prod_list \<dots> = (\<Prod>i=0..<length xs. xs ! i)"
    by (subst prod.distinct_set_conv_list [symmetric]) auto
  finally show ?thesis .
qed

lemma prod_zero_iff': "finite A \<Longrightarrow> prod f A = 0 \<longleftrightarrow> (\<exists>x\<in>A. f x = 0)"
  for f :: "'a \<Rightarrow> 'b :: {comm_semiring_1, semiring_no_zero_divisors}"
  by (induction A rule: infinite_finite_induct) auto

lemma degree_prod_eq: "(\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> 0) \<Longrightarrow> degree (prod f A) = (\<Sum>x\<in>A. degree (f x))"
  for f :: "'a \<Rightarrow> 'b::{comm_semiring_1, semiring_no_zero_divisors} poly"
  by (induction A rule: infinite_finite_induct) (auto simp: degree_mult_eq prod_zero_iff')

lemma lead_coeff_prod: "(\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> 0) \<Longrightarrow> lead_coeff (prod f A) = (\<Prod>x\<in>A. lead_coeff (f x))"
  for f :: "'a \<Rightarrow> 'b :: {comm_semiring_1, semiring_no_zero_divisors} poly"
  by (induction A rule: infinite_finite_induct) (auto simp: lead_coeff_mult prod_zero_iff')

lemma complex_poly_decompose':
  obtains root where "smult (lead_coeff p) (\<Prod>i<degree p. [:-root i, 1:]) = (p :: complex poly)"
proof -
  obtain roots where roots: "mset roots = poly_roots_mset p"
    using ex_mset by blast

  have "p = smult (lead_coeff p) (\<Prod>x\<in>#poly_roots_mset p. [:-x, 1:])"
    by (rule complex_poly_decompose_multiset [symmetric])
  also have "(\<Prod>x\<in>#poly_roots_mset p. [:-x, 1:]) = (\<Prod>x\<leftarrow>roots. [:-x, 1:])"
    by (subst prod_mset_prod_list [symmetric]) (simp add: roots)
  also have "\<dots> = (\<Prod>i<length roots. [:-roots ! i, 1:])"
    by (subst prod_list_prod_nth) (auto simp: atLeast0LessThan)
  finally have eq: "p = smult (lead_coeff p) (\<Prod>i<length roots. [:-roots ! i, 1:])" .
  also have [simp]: "degree p = length roots"
    using roots by (subst eq) (auto simp: degree_prod_eq)
  finally show ?thesis by (intro that[of "\<lambda>i. roots ! i"]) auto
qed
  
lemma rsquarefree_root_order:
  assumes "rsquarefree p" "poly p z = 0" "p \<noteq> 0"
  shows   "order z p = 1"
proof -
  from assms have "order z p \<in> {0, 1}" by (auto simp: rsquarefree_def)
  moreover from assms have "order z p > 0" by (auto simp: order_root)
  ultimately show "order z p = 1" by auto
qed

lemma complex_poly_decompose_rsquarefree:
  assumes "rsquarefree p"
  shows   "smult (lead_coeff p) (\<Prod>z|poly p z = 0. [:-z, 1:]) = (p :: complex poly)"
proof (cases "p = 0")
  case False
  have "(\<Prod>z|poly p z = 0. [:-z, 1:]) = (\<Prod>z|poly p z = 0. [:-z, 1:] ^ order z p)"
    using assms False by (intro prod.cong) (auto simp: rsquarefree_root_order)
  also have "smult (lead_coeff p) \<dots> = p"
    by (rule complex_poly_decompose)
  finally show ?thesis .
qed auto  


lemma pcompose_conjugates_integer:
  assumes "\<And>i. poly.coeff p i \<in> \<int>"
  shows   "poly.coeff (pcompose p [:0, \<i>:] * pcompose p [:0, -\<i>:]) i \<in> \<int>"
proof -
  let ?c = "\<lambda>i. poly.coeff p i :: complex"
  have "poly.coeff (pcompose p [:0, \<i>:] * pcompose p [:0, -\<i>:]) i =
          \<i> ^ i * (\<Sum>k\<le>i. (-1) ^ (i - k) * ?c k * ?c (i - k))"
    unfolding coeff_mult sum_distrib_left
    by (intro sum.cong) (auto simp: coeff_mult coeff_pcompose_linear power_minus' 
                                    power_diff field_simps intro!: Ints_sum)
  also have "(\<Sum>k\<le>i. (-1) ^ (i - k) * ?c k * ?c (i - k)) =
          (\<Sum>k\<le>i. (-1) ^ k * ?c k * ?c (i - k))" (is "?S1 = ?S2")
    by (intro sum.reindex_bij_witness[of _ "\<lambda>k. i - k" "\<lambda>k. i - k"]) (auto simp: mult_ac)
  hence "?S1 = (?S1 + ?S2) / 2" by simp
  also have "\<dots> = (\<Sum>k\<le>i. ((-1) ^ k + (-1) ^ (i - k)) / 2 * ?c k * ?c (i - k))"
    by (simp add: ring_distribs sum.distrib sum_divide_distrib [symmetric])
  also have "\<dots> = (\<Sum>k\<le>i. (1 + (-1) ^ i) / 2 * (-1) ^ k * ?c k * ?c (i - k))"
    by (intro sum.cong) (auto simp: power_add power_diff field_simps)
  also have "\<i> ^ i * \<dots> \<in> \<int>"
  proof (cases "even i")
    case True
    thus ?thesis
      by (intro Ints_mult Ints_sum assms) (auto elim!: evenE simp: power_mult)
  next
    case False
    hence "1 + (-1) ^ i = (0 :: complex)" by (auto elim!: oddE simp: power_mult)
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma algebraic_times_i:
  assumes "algebraic x"
  shows   "algebraic (\<i> * x)" "algebraic (-\<i> * x)"
proof -
  from assms obtain p where p: "poly p x = 0" "\<forall>i. coeff p i \<in> \<int>" "p \<noteq> 0"
    by (auto elim!: algebraicE)
  define p' where "p' = pcompose p [:0, \<i>:] * pcompose p [:0, -\<i>:]"
  have p': "poly p' (\<i> * x) = 0" "poly p' (-\<i> * x) = 0" "p' \<noteq> 0"
    by (auto simp: p'_def poly_pcompose algebra_simps p dest: pcompose_eq_0)
  moreover have "\<forall>i. poly.coeff p' i \<in> \<int>"
    using p unfolding p'_def by (intro allI pcompose_conjugates_integer) auto
  ultimately show "algebraic (\<i> * x)" "algebraic (-\<i> * x)" by (intro algebraicI[of p']; simp)+
qed

lemma algebraic_times_i_iff: "algebraic (\<i> * x) \<longleftrightarrow> algebraic x"
  using algebraic_times_i[of x] algebraic_times_i[of "\<i> * x"] by auto

lemma ratpolyE:
  assumes "\<forall>i. poly.coeff p i \<in> \<rat>"
  obtains q where "p = map_poly of_rat q"
proof -
  have "\<forall>i\<in>{..Polynomial.degree p}. \<exists>x. poly.coeff p i = of_rat x"
    using assms by (auto simp: Rats_def)
  from bchoice[OF this] obtain f
    where f: "\<And>i. i \<le> Polynomial.degree p \<Longrightarrow> poly.coeff p i = of_rat (f i)" by blast
  define q where "q = Poly (map f [0..<Suc (Polynomial.degree p)])"
  have "p = map_poly of_rat q"
    by (intro poly_eqI) 
       (auto simp: coeff_map_poly q_def nth_default_def f coeff_eq_0 simp del: upt_Suc)
  with that show ?thesis by blast
qed

end