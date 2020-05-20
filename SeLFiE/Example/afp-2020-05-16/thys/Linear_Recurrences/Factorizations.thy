(*
  File:    Factorizations.thy
  Author:  Manuel Eberl, TU München
*)
section \<open>Factorizations of polynomials\<close>
theory Factorizations
imports
  Complex_Main
  Linear_Recurrences_Misc
  "HOL-Computational_Algebra.Computational_Algebra"
  "HOL-Computational_Algebra.Polynomial_Factorial"
begin

text \<open>
  We view a factorisation of a polynomial as a pair consisting of the leading coefficient
  and a list of roots with multiplicities. This gives us a factorization into factors of
  the form $(X - c) ^ {n+1}$.
\<close>
definition interp_factorization where
  "interp_factorization = (\<lambda>(a,cs). Polynomial.smult a (\<Prod>(c,n)\<leftarrow>cs. [:-c,1:] ^ Suc n))"

text \<open>
  An alternative way to factorise is as a pair of the leading coefficient and
  factors of the form $(1 - cX) ^ {n+1}$.
\<close>
definition interp_alt_factorization where
  "interp_alt_factorization = (\<lambda>(a,cs). Polynomial.smult a (\<Prod>(c,n)\<leftarrow>cs. [:1,-c:] ^ Suc n))"

definition is_factorization_of where
  "is_factorization_of fctrs p =
     (interp_factorization fctrs = p \<and> distinct (map fst (snd fctrs)))"

definition is_alt_factorization_of where
  "is_alt_factorization_of fctrs p =
     (interp_alt_factorization fctrs = p \<and> 0 \<notin> set (map fst (snd fctrs)) \<and>
     distinct (map fst (snd fctrs)))"

text \<open>
  Regular and alternative factorisations are related by reflecting the polynomial.
\<close>
lemma interp_factorization_reflect:
  assumes "(0::'a::idom) \<notin> fst ` set (snd fctrs)"
  shows   "reflect_poly (interp_factorization fctrs) = interp_alt_factorization fctrs"
proof -
  have "reflect_poly (interp_factorization fctrs) =
          Polynomial.smult (fst fctrs) (\<Prod>x\<leftarrow>snd fctrs. reflect_poly [:- fst x, 1:] ^ Suc (snd x))"
    by (simp add: interp_factorization_def interp_alt_factorization_def case_prod_unfold
             reflect_poly_smult reflect_poly_prod_list reflect_poly_power o_def del: power_Suc)
  also have "map (\<lambda>x. reflect_poly [:- fst x, 1:] ^ Suc (snd x)) (snd fctrs) =
               map (\<lambda>x. [:1, - fst x:] ^ Suc (snd x)) (snd fctrs)"
    using assms by (intro list.map_cong0, subst reflect_poly_pCons) auto
  also have "Polynomial.smult (fst fctrs) (prod_list \<dots>) = interp_alt_factorization fctrs"
    by (simp add: interp_alt_factorization_def case_prod_unfold)
  finally show ?thesis .
qed

lemma interp_alt_factorization_reflect:
  assumes "(0::'a::idom) \<notin> fst ` set (snd fctrs)"
  shows   "reflect_poly (interp_alt_factorization fctrs) = interp_factorization fctrs"
proof -
  have "reflect_poly (interp_alt_factorization fctrs) =
          Polynomial.smult (fst fctrs) (\<Prod>x\<leftarrow>snd fctrs. reflect_poly [:1, - fst x:] ^ Suc (snd x))"
    by (simp add: interp_factorization_def interp_alt_factorization_def case_prod_unfold
             reflect_poly_smult reflect_poly_prod_list reflect_poly_power o_def del: power_Suc)
  also have "map (\<lambda>x. reflect_poly [:1, - fst x:] ^ Suc (snd x)) (snd fctrs) =
               map (\<lambda>x. [:- fst x, 1:] ^ Suc (snd x)) (snd fctrs)"
  proof (intro list.map_cong0, clarsimp simp del: power_Suc, goal_cases)
    fix c n assume "(c, n) \<in> set (snd fctrs)"
    with assms have "c \<noteq> 0" by force
    thus "reflect_poly [:1, -c:] ^ Suc n = [:-c, 1:] ^ Suc n"
      by (simp add: reflect_poly_pCons del: power_Suc)
  qed
  also have "Polynomial.smult (fst fctrs) (prod_list \<dots>) = interp_factorization fctrs"
    by (simp add: interp_factorization_def case_prod_unfold)
  finally show ?thesis .
qed


lemma coeff_0_interp_factorization:
  "coeff (interp_factorization fctrs) 0 = (0 :: 'a :: idom) \<longleftrightarrow>
     fst fctrs = 0 \<or> 0 \<in> fst ` set (snd fctrs)"
  by (force simp: interp_factorization_def case_prod_unfold coeff_0_prod_list o_def
                  coeff_0_power prod_list_zero_iff simp del: power_Suc)

lemma reflect_factorization:
  assumes "coeff p 0 \<noteq> (0::'a::idom)"
  assumes "is_factorization_of fctrs p"
  shows   "is_alt_factorization_of fctrs (reflect_poly p)"
  using assms by (force simp: interp_factorization_reflect is_factorization_of_def
                    is_alt_factorization_of_def coeff_0_interp_factorization)

lemma reflect_factorization':
  assumes "coeff p 0 \<noteq> (0::'a::idom)"
  assumes "is_alt_factorization_of fctrs p"
  shows   "is_factorization_of fctrs (reflect_poly p)"
  using assms by (force simp: interp_alt_factorization_reflect is_factorization_of_def
                    is_alt_factorization_of_def coeff_0_interp_factorization)

lemma zero_in_factorization_iff:
  assumes "is_factorization_of fctrs p"
  shows   "coeff p 0 = 0 \<longleftrightarrow> p = 0 \<or> (0::'a::idom) \<in> fst ` set (snd fctrs)"
proof (cases "p = 0")
  assume "p \<noteq> 0"
  with assms have [simp]: "fst fctrs \<noteq> 0"
    by (auto simp: is_factorization_of_def interp_factorization_def case_prod_unfold)
  from assms have "p = interp_factorization fctrs" by (simp add: is_factorization_of_def)
  also have "coeff \<dots> 0 = 0 \<longleftrightarrow> 0 \<in> fst ` set (snd fctrs)"
    by (force simp add: interp_factorization_def case_prod_unfold coeff_0_prod_list
                        prod_list_zero_iff o_def coeff_0_power)
  finally show ?thesis using \<open>p \<noteq> 0\<close> by blast
next
  assume p: "p = 0"
  with assms have "interp_factorization fctrs = 0" by (simp add: is_factorization_of_def)
  also have "interp_factorization fctrs = 0 \<longleftrightarrow>
                 fst fctrs = 0 \<or> (\<Prod>(c,n)\<leftarrow>snd fctrs. [:-c,1:]^Suc n) = 0"
    by (simp add: interp_factorization_def case_prod_unfold)
  also have "(\<Prod>(c,n)\<leftarrow>snd fctrs. [:-c,1:]^Suc n) = 0 \<longleftrightarrow> False"
    by (auto simp: prod_list_zero_iff simp del: power_Suc)
  finally show ?thesis by (simp add: \<open>p = 0\<close>)
qed

lemma poly_prod_list [simp]: "poly (prod_list ps) x = prod_list (map (\<lambda>p. poly p x) ps)"
  by (induction ps) auto

lemma is_factorization_of_roots:
  fixes a :: "'a :: idom"
  assumes "is_factorization_of (a, fctrs) p" "p \<noteq> 0"
  shows   "set (map fst fctrs) = {x. poly p x = 0}"
  using assms
  by (force simp: is_factorization_of_def interp_factorization_def o_def
        case_prod_unfold prod_list_zero_iff simp del: power_Suc)

lemma (in monoid_mult) prod_list_prod_nth: "prod_list xs = (\<Prod>i<length xs. xs ! i)"
  by (induction xs) (auto simp: prod.lessThan_Suc_shift simp del: prod.lessThan_Suc)

lemma order_prod:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> 0"
  assumes "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<noteq> y \<Longrightarrow> coprime (f x) (f y)"
  shows   "order c (prod f A) = (\<Sum>x\<in>A. order c (f x))"
  using assms
proof (induction A rule: infinite_finite_induct)
  case (insert x A)
  from insert.hyps have "order c (prod f (insert x A)) = order c (f x * prod f A)"
    by simp
  also have "\<dots> = order c (f x) + order c (prod f A)"
    using insert.prems and insert.hyps by (intro order_mult) auto
  also have "order c (prod f A) = (\<Sum>x\<in>A. order c (f x))"
    using insert.prems and insert.hyps by (intro insert.IH) auto
  finally show ?case using insert.hyps by simp
qed auto

lemma is_factorization_of_order:
  fixes p :: "'a :: field_gcd poly"
  assumes "p \<noteq> 0"
  assumes "is_factorization_of (a, fctrs) p"
  assumes "(c, n) \<in> set fctrs"
  shows   "order c p = Suc n"
proof -
  from assms have distinct: "distinct (map fst (fctrs))"
    by (simp add: is_factorization_of_def)
  from assms have [simp]: "a \<noteq> 0"
    by (auto simp: is_factorization_of_def interp_factorization_def)
  from assms(2) have "p = interp_factorization (a, fctrs)"
    unfolding is_factorization_of_def by simp
  also have "order c \<dots> = order c (\<Prod>(c,n)\<leftarrow>fctrs. [:-c, 1:] ^ Suc n)"
    unfolding interp_factorization_def by (simp add: order_smult)
  also have "(\<Prod>(c,n)\<leftarrow>fctrs. [:-c, 1:] ^ Suc n) =
               (\<Prod>i\<in>{..<length fctrs}. [:-fst (fctrs ! i), 1:] ^ Suc (snd (fctrs ! i)))"
    by (simp add: prod_list_prod_nth case_prod_unfold)
  also have "order c \<dots> =
               (\<Sum>x<length fctrs. order c ([:- fst (fctrs ! x), 1:] ^ Suc (snd (fctrs ! x))))"
  proof (rule order_prod)
    fix i
    assume "i \<in> {..<length fctrs}"
    then show "[:- fst (fctrs ! i), 1:] ^ Suc (snd (fctrs ! i)) \<noteq> 0"
      by (simp only: power_eq_0_iff) simp
  next
    fix i j :: nat
    assume "i \<noteq> j" "i \<in> {..<length fctrs}" "j \<in> {..<length fctrs}"
    then have "fst (fctrs ! i) \<noteq> fst (fctrs ! j)"
      using nth_eq_iff_index_eq [OF distinct, of i j] by simp
    then show "coprime ([:- fst (fctrs ! i), 1:] ^ Suc (snd (fctrs ! i)))
      ([:- fst (fctrs ! j), 1:] ^ Suc (snd (fctrs ! j)))"
      by (simp only: coprime_power_left_iff coprime_power_right_iff)
        (auto simp add: coprime_linear_poly)
  qed
  also have "\<dots> = (\<Sum>(c',n')\<leftarrow>fctrs. order c ([:-c', 1:] ^ Suc n'))"
    by (simp add: sum_list_sum_nth case_prod_unfold atLeast0LessThan)
  also have "\<dots> = (\<Sum>(c',n')\<leftarrow>fctrs. if c = c' then Suc n' else 0)"
    by (intro arg_cong[OF map_cong]) (auto simp add: order_power_n_n order_0I simp del: power_Suc)
  also have "\<dots> = (\<Sum>x\<leftarrow>fctrs. if x = (c, n) then Suc (snd x) else 0)"
    using distinct assms by (intro arg_cong[OF map_cong]) (force simp: distinct_map inj_on_def)+
  also from distinct have "\<dots> = (\<Sum>x\<in>set fctrs. if x = (c, n) then Suc (snd x) else 0)"
    by (intro sum_list_distinct_conv_sum_set) (simp_all add: distinct_map)
  also from assms have "\<dots> = Suc n" by simp
  finally show ?thesis .
qed


text \<open>
  For complex polynomials, a factorisation in the above sense always exists.
\<close>
lemma complex_factorization_exists:
  "\<exists>fctrs. is_factorization_of fctrs (p :: complex poly)"
proof (cases "p = 0")
  case True
  thus ?thesis
    by (intro exI[of _ "(0, [])"]) (auto simp: is_factorization_of_def interp_factorization_def)
next
  case False
  hence "\<exists>xs. set xs = {x. poly p x = 0} \<and> distinct xs"
    by (intro finite_distinct_list poly_roots_finite)
  then obtain xs where [simp]: "set xs = {x. poly p x = 0}" "distinct xs" by blast
  have "interp_factorization (lead_coeff p, map (\<lambda>x. (x, order x p - 1)) xs) =
          smult (lead_coeff p) (\<Prod>x\<leftarrow>xs. [:- x, 1:] ^ Suc (order x p - 1))"
    by (simp add: interp_factorization_def o_def)
  also have "(\<Prod>x\<leftarrow>xs. [:- x, 1:] ^ Suc (order x p - 1)) =
               (\<Prod>x|poly p x = 0. [:- x, 1:] ^ Suc (order x p - 1))"
    by (subst prod.distinct_set_conv_list [symmetric]) simp_all
  also have "\<dots> = (\<Prod>x|poly p x = 0. [:- x, 1:] ^ order x p)"
  proof (intro prod.cong refl, goal_cases)
    case (1 x)
    with False have "order x p \<noteq> 0" by (subst (asm) order_root) auto
    hence *: "Suc (order x p - 1) = order x p" by simp
    show ?case by (simp only: *)
  qed
  also have "smult (lead_coeff p) \<dots> = p"
    by (rule complex_poly_decompose)
  finally have "is_factorization_of (lead_coeff p, map (\<lambda>x. (x, order x p - 1)) xs) p"
    by (auto simp: is_factorization_of_def o_def)
  thus ?thesis ..
qed

text \<open>
  By reflecting the polynomial, this means that for complex polynomials with non-zero
  constant coefficient, the alternative factorisation also exists.
\<close>
corollary complex_alt_factorization_exists:
  assumes "coeff p 0 \<noteq> 0"
  shows   "\<exists>fctrs. is_alt_factorization_of fctrs (p :: complex poly)"
proof -
  from assms have "coeff (reflect_poly p) 0 \<noteq> 0"
    by auto
  moreover from complex_factorization_exists [of "reflect_poly p"]
  obtain fctrs where "is_factorization_of fctrs (reflect_poly p)" ..
  ultimately have "is_alt_factorization_of fctrs (reflect_poly (reflect_poly p))"
    by (rule reflect_factorization)
  also from assms have "reflect_poly (reflect_poly p) = p"
    by simp
  finally show ?thesis ..
qed

end