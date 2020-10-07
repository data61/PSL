(*
  File:    Linear_Recurrences_Misc.thy
  Author:  Manuel Eberl, TU München
*)
section \<open>Miscellaneous material required for linear recurrences\<close>
theory Linear_Recurrences_Misc
imports 
  Complex_Main
  "HOL-Computational_Algebra.Computational_Algebra"
  "HOL-Computational_Algebra.Polynomial_Factorial"
begin

fun zip_with where
  "zip_with f (x#xs) (y#ys) = f x y # zip_with f xs ys"
| "zip_with f _ _ = []"

lemma length_zip_with [simp]: "length (zip_with f xs ys) = min (length xs) (length ys)"
  by (induction f xs ys rule: zip_with.induct) simp_all

lemma zip_with_altdef: "zip_with f xs ys = map (\<lambda>(x,y). f x y) (zip xs ys)"
  by (induction f xs ys rule: zip_with.induct) simp_all
  
lemma zip_with_nth [simp]:
  "n < length xs \<Longrightarrow> n < length ys \<Longrightarrow> zip_with f xs ys ! n = f (xs!n) (ys!n)"
  by (simp add: zip_with_altdef)

lemma take_zip_with: "take n (zip_with f xs ys) = zip_with f (take n xs) (take n ys)"
proof (induction f xs ys arbitrary: n rule: zip_with.induct)
  case (1 f x xs y ys n)
  thus ?case by (cases n) simp_all
qed simp_all

lemma drop_zip_with: "drop n (zip_with f xs ys) = zip_with f (drop n xs) (drop n ys)"
proof (induction f xs ys arbitrary: n rule: zip_with.induct)
  case (1 f x xs y ys n)
  thus ?case by (cases n) simp_all
qed simp_all

lemma map_zip_with: "map f (zip_with g xs ys) = zip_with (\<lambda>x y. f (g x y)) xs ys"
  by (induction g xs ys rule: zip_with.induct) simp_all

lemma zip_with_map: "zip_with f (map g xs) (map h ys) = zip_with (\<lambda>x y. f (g x) (h y)) xs ys"
  by (induction "\<lambda>x y. f (g x) (h y)" xs ys rule: zip_with.induct) simp_all

lemma zip_with_map_left: "zip_with f (map g xs) ys = zip_with (\<lambda>x y. f (g x) y) xs ys"
  using zip_with_map[of f g xs "\<lambda>x. x" ys] by simp

lemma zip_with_map_right: "zip_with f xs (map g ys) = zip_with (\<lambda>x y. f x (g y)) xs ys"
  using zip_with_map[of f "\<lambda>x. x" xs g ys] by simp

lemma zip_with_swap: "zip_with (\<lambda>x y. f y x) xs ys = zip_with f ys xs"
  by (induction f ys xs rule: zip_with.induct) simp_all

lemma set_zip_with: "set (zip_with f xs ys) = (\<lambda>(x,y). f x y) ` set (zip xs ys)"
  by (induction f xs ys rule: zip_with.induct) simp_all

lemma zip_with_Pair: "zip_with Pair (xs :: 'a list) (ys :: 'b list) = zip xs ys"
  by (induction "Pair :: 'a \<Rightarrow> 'b \<Rightarrow> _" xs ys rule: zip_with.induct) simp_all

lemma zip_with_altdef': 
    "zip_with f xs ys = [f (xs!i) (ys!i). i \<leftarrow> [0..<min (length xs) (length ys)]]"
  by (induction f xs ys rule: zip_with.induct) (simp_all add: map_upt_Suc del: upt_Suc)

lemma zip_altdef: "zip xs ys = [(xs!i, ys!i). i \<leftarrow> [0..<min (length xs) (length ys)]]"
  by (simp add: zip_with_Pair [symmetric] zip_with_altdef')



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


lemma normalize_field: 
  "normalize (x :: 'a :: {normalization_semidom,field}) = (if x = 0 then 0 else 1)"
  by (auto simp: normalize_1_iff dvd_field_iff)

lemma unit_factor_field [simp]:
  "unit_factor (x :: 'a :: {normalization_semidom,field}) = x"
  using unit_factor_mult_normalize[of x] normalize_field[of x]
  by (simp split: if_splits)

lemma coprime_linear_poly: 
  fixes c :: "'a :: {field,factorial_ring_gcd}"
  assumes "c \<noteq> c'"
  shows   "coprime [:c,1:] [:c',1:]"
proof -
  have "gcd [:c,1:] [:c',1:] = gcd ([:c,1:] - [:c',1:]) [:c',1:]"
    by (rule gcd_diff1 [symmetric])
  also have "[:c,1:] - [:c',1:] = [:c-c':]" by simp
  also from assms have "gcd \<dots> [:c',1:] = normalize [:c-c':]"
    by (intro gcd_proj1_if_dvd) (auto simp: const_poly_dvd_iff dvd_field_iff)
  also from assms have "\<dots> = 1" by (simp add: normalize_poly_def)
  finally show "coprime [:c,1:] [:c',1:]"
    by (simp add: gcd_eq_1_imp_coprime)
qed

lemma coprime_linear_poly': 
  fixes c :: "'a :: {field,factorial_ring_gcd,normalization_euclidean_semiring}"
  assumes "c \<noteq> c'" "c \<noteq> 0" "c' \<noteq> 0"
  shows   "coprime [:1,c:] [:1,c':]"
proof -
  have "gcd [:1,c:] [:1,c':] = gcd ([:1,c:] mod [:1,c':]) [:1,c':]"
    by simp
  also have "eucl_rel_poly [:1, c:] [:1, c':] ([:c/c':], [:1-c/c':])"
    using assms by (auto simp add: eucl_rel_poly_iff one_pCons)
  hence "[:1,c:] mod [:1,c':] = [:1 - c / c':]"
    by (rule mod_poly_eq)
  also from assms have "gcd \<dots> [:1,c':] = normalize ([:1 - c / c':])"
    by (intro gcd_proj1_if_dvd) (auto simp: const_poly_dvd_iff dvd_field_iff)
  also from assms have "\<dots> = 1" by (auto simp: normalize_poly_def)
  finally show ?thesis
    by (rule gcd_eq_1_imp_coprime)
qed

end
