section \<open>Polynomial coefficients with integer index\<close>
  
text \<open>We provide a function to access the coefficients of a polynomial
  via an integer index. Then index-shifting becomes more convenient,
  e.g., compare in the lemmas for accessing the coeffiencent of a product
  with a monomial there is no special case for integer coefficients, whereas
  for natural number coefficients there is a case-distinction.\<close>
  
theory Coeff_Int
imports 
  Polynomial_Interpolation.Missing_Polynomial 
  Jordan_Normal_Form.Missing_Permutations
begin
  
definition coeff_int :: "'a :: zero poly \<Rightarrow> int \<Rightarrow> 'a" where
  "coeff_int p i = (if i < 0 then 0 else coeff p (nat i))"

lemma coeff_int_eq_0: "i < 0 \<or> i > int (degree p) \<Longrightarrow> coeff_int p i = 0"
  unfolding coeff_int_def
  by (cases "i < 0", auto intro: coeff_eq_0)

lemma coeff_int_smult[simp]: "coeff_int (smult c p) i = c * coeff_int p i"
  unfolding coeff_int_def by simp

lemma coeff_int_signof_mult: "coeff_int (signof x * f) i = signof x * (coeff_int f i)"
  unfolding signof_def by (auto simp: coeff_int_def)

lemma coeff_int_sum: "coeff_int (sum p A) i = (\<Sum>x\<in>A. coeff_int (p x) i)"
  using coeff_sum[of p A "nat i"] unfolding coeff_int_def
  by (cases "i < 0", auto)

lemma coeff_int_0[simp]: "coeff_int f 0 = coeff f 0" unfolding coeff_int_def by simp

lemma coeff_int_monom_mult: "coeff_int (monom a d * f) i = (a * coeff_int f (i - d))"
proof (cases "i < 0")
  case True
  thus ?thesis unfolding coeff_int_def by simp
next
  case False
  hence "i \<ge> 0" by auto
  then obtain j where i: "i = int j" by (rule nonneg_eq_int)
  show ?thesis
  proof (cases "i \<ge> d")
    case True
    with i have "nat (int j - int d) = j - d" by auto
    with coeff_monom_mult[of a] show ?thesis unfolding coeff_int_def i
      by simp
  next
    case False
    thus ?thesis unfolding i by (simp add: coeff_int_def coeff_monom_mult)
  qed
qed

lemma coeff_prod_const: assumes "finite xs" and "y \<notin> xs"
  and "\<And> x. x \<in> xs \<Longrightarrow> degree (f x) = 0"
shows "coeff (prod f (insert y xs)) i = prod (\<lambda> x. coeff (f x) 0) xs * coeff (f y) i"
  using assms
proof (induct xs rule: finite_induct)
  case (insert x xs)
  from insert(2,4) have id: "insert y (insert x xs) - {x} = insert y xs" by auto
  have "prod f (insert y (insert x xs)) = f x * prod f (insert y xs)"
    by (subst prod.remove[of _ x], insert insert(1,2) id, auto)
  hence "coeff (prod f (insert y (insert x xs))) i = coeff (f x * prod f (insert y xs)) i" by simp
  also have "\<dots> = coeff (f x) 0 * (coeff (prod f (insert y xs)) i)"
  proof -
    from insert(5)[of x] degree0_coeffs[of "f x"] obtain c where fx: "f x = [: c :]" by auto
    show ?thesis unfolding fx by auto
  qed
  also have "(coeff (prod f (insert y xs)) i) = (\<Prod>x\<in>xs. coeff (f x) 0) * coeff (f y) i" using insert by auto
  also have "coeff (f x) 0 * \<dots> = prod (\<lambda> x. coeff (f x) 0) (insert x xs) * coeff (f y) i"
    by (subst prod.insert_remove, insert insert(1,2,4), auto simp: ac_simps)
  finally show ?case .
qed simp

lemma coeff_int_prod_const: assumes "finite xs" and "y \<notin> xs"
  and "\<And> x. x \<in> xs \<Longrightarrow> degree (f x) = 0"
shows "coeff_int (prod f (insert y xs)) i = prod (\<lambda> x. coeff_int (f x) 0) xs * coeff_int (f y) i"
  using coeff_prod_const[OF assms] unfolding coeff_int_def by (cases "i < 0", auto)

lemma coeff_int[simp]: "coeff_int p n = coeff p n"  unfolding coeff_int_def by auto

lemma coeff_int_minus[simp]:
  "coeff_int (a - b) i = coeff_int a i - coeff_int b i"
  by (auto simp: coeff_int_def)

lemma coeff_int_pCons_0[simp]: "coeff_int (pCons 0 b) i = coeff_int b (i - 1)"
  by (auto simp: Nitpick.case_nat_unfold coeff_int_def coeff_pCons nat_diff_distrib')
    
end
