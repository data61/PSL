(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
subsection \<open>Resultant\<close>

text \<open>This theory contains 
  facts about resultants which are required for addition and multiplication
  of algebraic numbers.

  The results are taken from the textbook \cite[pages 227ff and 235ff]{AlgNumbers}.
\<close> 

theory Resultant
imports
  Polynomial_Factorization.Rational_Factorization
  Subresultants.Subresultant_Gcd 
  Berlekamp_Zassenhaus.Unique_Factorization_Poly
  Bivariate_Polynomials
begin

subsubsection \<open>Sylvester matrices and vector representation of polynomials\<close>

definition vec_of_poly_rev_shifted where
  "vec_of_poly_rev_shifted p n j \<equiv>
   vec n (\<lambda>i. if i \<le> j \<and> j \<le> degree p + i then coeff p (degree p + i - j) else 0)"

lemma vec_of_poly_rev_shifted_dim[simp]: "dim_vec (vec_of_poly_rev_shifted p n j) = n"
  unfolding vec_of_poly_rev_shifted_def by auto

lemma col_sylvester:
  fixes p q
  defines "m \<equiv> degree p" and "n \<equiv> degree q"
  assumes j: "j < m+n"
  shows "col (sylvester_mat p q) j =
    vec_of_poly_rev_shifted p n j @\<^sub>v vec_of_poly_rev_shifted q m j" (is "?l = ?r")
proof
  note [simp] = m_def[symmetric] n_def[symmetric]
  show "dim_vec ?l = dim_vec ?r" by simp
  fix i assume "i < dim_vec ?r" hence i: "i < m+n" by auto
  show "?l $ i = ?r $ i"
    unfolding vec_of_poly_rev_shifted_def
    apply (subst index_col) using i apply simp using j apply simp
    apply (subst sylvester_index_mat) using i apply simp using j apply simp
    apply (cases "i < n") apply force using i by simp
qed

lemma inj_on_diff_nat2: "inj_on (\<lambda>i. (n::nat) - i) {..n}" by (rule inj_onI, auto)

lemma image_diff_atMost: "(\<lambda>i. (n::nat) - i) ` {..n} = {..n}" (is "?l = ?r")
  unfolding set_eq_iff
proof (intro allI iffI)
  fix x assume x: "x \<in> ?r"
    thus "x \<in> ?l" unfolding image_def mem_Collect_eq
    by(intro bexI[of _ "n-x"],auto)
qed auto

lemma sylvester_sum_mat_upper:
  fixes p q :: "'a :: comm_semiring_1 poly"
  defines "m \<equiv> degree p" and "n \<equiv> degree q"
  assumes i: "i < n"
  shows "(\<Sum>j<m+n. monom (sylvester_mat p q $$ (i,j)) (m + n - Suc j)) =
    monom 1 (n - Suc i) * p" (is "sum ?f _ = ?r")
proof -
  have n1: "n \<ge> 1" using i by auto
  define ni1 where "ni1 = n-Suc i"
  hence ni1: "n-i = Suc ni1" using i by auto
  define l where "l = m+n-1"
  hence l: "Suc l = m+n" using n1 by auto
  let ?g = "\<lambda>j. monom (coeff (monom 1 (n-Suc i) * p) j) j"
  let ?p = "\<lambda>j. l-j"
  have "sum ?f {..<m+n} = sum ?f {..l}"
    unfolding l[symmetric] unfolding lessThan_Suc_atMost..
  also {
    fix j assume j: "j\<le>l"
    have "?f j = ((\<lambda>j. monom (coeff (monom 1 (n-i) * p) (Suc j)) j) \<circ> ?p) j"
      apply(subst sylvester_index_mat2)
      using i j unfolding l_def m_def[symmetric] n_def[symmetric]
      by (auto simp add: Suc_diff_Suc)
    also have "... = (?g \<circ> ?p) j"
      unfolding ni1
      unfolding coeff_monom_Suc
      unfolding ni1_def
      using i by auto
    finally have "?f j = (?g \<circ> ?p) j".
  }
  hence "(\<Sum>j\<le>l. ?f j) = (\<Sum>j\<le>l. (?g\<circ>?p) j)" using l by auto
  also have "... = (\<Sum>j\<le>l. ?g j)"
    unfolding l_def
    using sum.reindex[OF inj_on_diff_nat2,symmetric,unfolded image_diff_atMost].
  also have "degree ?r \<le> l"
      using degree_mult_le[of "monom 1 (n-Suc i)" p]
      unfolding l_def m_def
      unfolding degree_monom_eq[OF one_neq_zero] using i by auto
    from poly_as_sum_of_monoms'[OF this]
    have "(\<Sum>j\<le>l. ?g j) = ?r".
  finally show ?thesis.
qed

lemma sylvester_sum_mat_lower:
  fixes p q :: "'a :: comm_semiring_1 poly"
  defines "m \<equiv> degree p" and "n \<equiv> degree q"
  assumes ni: "n \<le> i" and imn: "i < m+n"
  shows "(\<Sum>j<m+n. monom (sylvester_mat p q $$ (i,j)) (m + n - Suc j)) =
    monom 1 (m + n - Suc i) * q" (is "sum ?f _ = ?r")
proof -
  define l where "l = m+n-1"
  hence l: "Suc l = m+n" using imn by auto
  define mni1 where "mni1 = m + n - Suc i"
  hence mni1: "m+n-i = Suc mni1" using imn by auto
  let ?g = "\<lambda>j. monom (coeff (monom 1 (m + n - Suc i) * q) j) j"
  let ?p = "\<lambda>j. l-j"
  have "sum ?f {..<m+n} = sum ?f {..l}"
    unfolding l[symmetric] unfolding lessThan_Suc_atMost..
  also {
    fix j assume j: "j\<le>l"
    have "?f j = ((\<lambda>j. monom (coeff (monom 1 (m+n-i) * q) (Suc j)) j) \<circ> ?p) j"
      apply(subst sylvester_index_mat2)
      using ni imn j unfolding l_def m_def[symmetric] n_def[symmetric]
      by (auto simp add: Suc_diff_Suc)
    also have "... = (?g \<circ> ?p) j"
      unfolding mni1
      unfolding coeff_monom_Suc
      unfolding mni1_def..
    finally have "?f j = ...".
  }
  hence "(\<Sum>j\<le>l. ?f j) = (\<Sum>j\<le>l. (?g\<circ>?p) j)" by auto
  also have "... = (\<Sum>j\<le>l. ?g j)"
    using sum.reindex[OF inj_on_diff_nat2,symmetric,unfolded image_diff_atMost].
  also have "degree ?r \<le> l"
      using degree_mult_le[of "monom 1 (m+n-1-i)" q]
      unfolding l_def n_def[symmetric]
      unfolding degree_monom_eq[OF one_neq_zero] using ni imn by auto
    from poly_as_sum_of_monoms'[OF this]
    have "(\<Sum>j\<le>l. ?g j) = ?r".
  finally show ?thesis.
qed

definition "vec_of_poly p \<equiv> let m = degree p in vec (Suc m) (\<lambda>i. coeff p (m-i))"

definition "poly_of_vec v \<equiv> let d = dim_vec v in \<Sum>i<d. monom (v $ (d - Suc i)) i"

lemma poly_of_vec_of_poly[simp]:
  fixes p :: "'a :: comm_monoid_add poly"
  shows "poly_of_vec (vec_of_poly p) = p"
  unfolding poly_of_vec_def vec_of_poly_def Let_def
  unfolding dim_vec
  unfolding lessThan_Suc_atMost
  using poly_as_sum_of_monoms[of p] by auto

lemma poly_of_vec_0[simp]: "poly_of_vec (0\<^sub>v n) = 0" unfolding poly_of_vec_def Let_def by auto

lemma poly_of_vec_0_iff[simp]:
  fixes v  :: "'a :: comm_monoid_add vec"
  shows "poly_of_vec v = 0 \<longleftrightarrow> v = 0\<^sub>v (dim_vec v)" (is "?v = _ \<longleftrightarrow> _ = ?z")
proof
  assume "?v = 0"
  hence "\<forall>i\<in>{..<dim_vec v}. v $ (dim_vec v - Suc i) = 0"
    unfolding poly_of_vec_def Let_def
    by (subst sum_monom_0_iff[symmetric],auto)
  hence a: "\<And>i. i < dim_vec v \<Longrightarrow> v $ (dim_vec v - Suc i) = 0" by auto
  { fix i assume "i < dim_vec v"
    hence "v $ i = 0" using a[of "dim_vec v - Suc i"] by auto
  }
  thus "v = ?z" by auto
  next assume r: "v = ?z"
  show "?v = 0" apply (subst r) by auto
qed

(* TODO: move, copied from no longer existing Cayley-Hamilton/Polynomial_extension *)
lemma degree_sum_smaller:
  assumes "n > 0" "finite A"
  shows "(\<And> x. x \<in>A \<Longrightarrow> degree (f x) < n) \<Longrightarrow> degree (\<Sum>x\<in>A. f x) < n"
  using \<open>finite A\<close>
  by(induct rule: finite_induct)
    (simp_all add: degree_add_less assms)

lemma degree_poly_of_vec_less:
  fixes v :: "'a :: comm_monoid_add vec"
  assumes dim: "dim_vec v > 0"
  shows "degree (poly_of_vec v) < dim_vec v"
  unfolding poly_of_vec_def Let_def
  apply(rule degree_sum_smaller)
    using dim apply force
    apply force
  unfolding lessThan_iff
  by (metis degree_0 degree_monom_eq dim monom_eq_0_iff)

lemma coeff_poly_of_vec:
  "coeff (poly_of_vec v) i = (if i < dim_vec v then v $ (dim_vec v - Suc i) else 0)"
  (is "?l = ?r")
proof -
  have "?l = (\<Sum>x<dim_vec v. if x = i then v $ (dim_vec v - Suc x) else 0)" (is "_ = ?m")
    unfolding poly_of_vec_def Let_def coeff_sum coeff_monom ..
  also have "\<dots> = ?r"
  proof (cases "i < dim_vec v")
    case False
    show ?thesis
      by (subst sum.neutral, insert False, auto)
  next
    case True
    show ?thesis
      by (subst sum.remove[of _ i], force, force simp: True, subst sum.neutral, insert True, auto)
  qed
  finally show ?thesis .
qed

lemma vec_of_poly_rev_shifted_scalar_prod:
  fixes p v
  defines "q \<equiv> poly_of_vec v"
  assumes m[simp]: "degree p = m" and n: "dim_vec v = n"
  assumes j: "j < m+n"
  shows "vec_of_poly_rev_shifted p n (n+m-Suc j) \<bullet> v = coeff (p * q) j" (is "?l = ?r")
proof -
  have id1: "\<And> i. m + i - (n + m - Suc j) = i + Suc j - n"
    using j by auto
  let ?g = "\<lambda> i. if i \<le> n + m - Suc j \<and> n - Suc j \<le> i then coeff p (i + Suc j - n) *  v $ i else 0"
  have "?thesis = ((\<Sum>i = 0..<n. ?g i) =          
        (\<Sum>i\<le>j. coeff p i * (if j - i < n then v $ (n - Suc (j - i)) else 0)))" (is "_ = (?l = ?r)")
    unfolding vec_of_poly_rev_shifted_def coeff_mult m scalar_prod_def n q_def
      coeff_poly_of_vec 
    by (subst sum.cong, insert id1, auto)
  also have "..." 
  proof -
    have "?r = (\<Sum>i\<le>j. (if j - i < n then coeff p i * v $ (n - Suc (j - i)) else 0))" (is "_ = sum ?f _")
      by (rule sum.cong, auto)
    also have "sum ?f {..j} = sum ?f ({i. i \<le> j \<and> j - i < n} \<union> {i. i \<le> j \<and> \<not> j - i < n})" 
      (is "_ = sum _ (?R1 \<union> ?R2)")
      by (rule sum.cong, auto)
    also have "\<dots> = sum ?f ?R1 + sum ?f ?R2"
      by (subst sum.union_disjoint, auto)
    also have "sum ?f ?R2 = 0"
      by (rule sum.neutral, auto)
    also have "sum ?f ?R1 + 0 = sum (\<lambda> i. coeff p i * v $ (i + n - Suc j)) ?R1"
      (is "_ = sum ?F _")
      by (subst sum.cong, auto simp: ac_simps)
    also have "\<dots> = sum ?F ((?R1 \<inter> {..m}) \<union> (?R1 - {..m}))"
      (is "_ = sum _ (?R \<union> ?R')")
      by (rule sum.cong, auto)
    also have "\<dots> = sum ?F ?R + sum ?F ?R'"
      by (subst sum.union_disjoint, auto)
    also have "sum ?F ?R' = 0"
    proof -
      { 
        fix x
        assume "x > m" 
        from coeff_eq_0[OF this[folded m]]
        have "?F x = 0" by simp
      }
      thus ?thesis
        by (subst sum.neutral, auto)
    qed
    finally have r: "?r = sum ?F ?R" by simp

    have "?l = sum ?g ({i. i < n \<and> i \<le> n + m - Suc j \<and> n - Suc j \<le> i} 
      \<union> {i. i < n \<and> \<not> (i \<le> n + m - Suc j \<and> n - Suc j \<le> i)})" 
      (is "_ = sum _ (?L1 \<union> ?L2)")
      by (rule sum.cong, auto)
    also have "\<dots> = sum ?g ?L1 + sum ?g ?L2"
      by (subst sum.union_disjoint, auto)
    also have "sum ?g ?L2 = 0"
      by (rule sum.neutral, auto)
    also have "sum ?g ?L1 + 0 = sum (\<lambda> i. coeff p (i + Suc j - n) * v $ i) ?L1"
      (is "_ = sum ?G _")
      by (subst sum.cong, auto)
    also have "\<dots> = sum ?G (?L1 \<inter> {i. i + Suc j - n \<le> m} \<union> (?L1 - {i. i + Suc j - n \<le> m}))"
      (is "_ = sum _ (?L \<union> ?L')")
      by (subst sum.cong, auto)
    also have "\<dots> = sum ?G ?L + sum ?G ?L'"      
      by (subst sum.union_disjoint, auto)
    also have "sum ?G ?L' = 0"
    proof -
      {
        fix x
        assume "x + Suc j - n > m" 
        from coeff_eq_0[OF this[folded m]]
        have "?G x = 0" by simp
      }
      thus ?thesis
        by (subst sum.neutral, auto)
    qed
    finally have l: "?l = sum ?G ?L" by simp

    let ?bij = "\<lambda> i. i + n - Suc j"
    {
      fix x
      assume x: "j < m + n" "Suc (x + j) - n \<le> m" "x < n" "n - Suc j \<le> x" 
      define y where "y = x + Suc j - n"
      from x have "x + Suc j \<ge> n" by auto
      with x have xy: "x = ?bij y" unfolding y_def by auto
      from x have y: "y \<in> ?R" unfolding y_def by auto
      have "x \<in> ?bij ` ?R" unfolding xy using y by blast
    } note tedious = this
    show ?thesis unfolding l r
      by (rule sum.reindex_cong[of ?bij], insert j, auto simp: inj_on_def tedious)
  qed
  finally show ?thesis by simp
qed

lemma sylvester_vec_poly:
  fixes p q :: "'a :: comm_semiring_0 poly"
  defines "m \<equiv> degree p"
      and "n \<equiv> degree q"
  assumes v: "v \<in> carrier_vec (m+n)"
  shows "poly_of_vec (transpose_mat (sylvester_mat p q) *\<^sub>v v) =
    poly_of_vec (vec_first v n) * p + poly_of_vec (vec_last v m) * q" (is "?l = ?r")
proof (rule poly_eqI)
  fix i
  note mn[simp] = m_def[symmetric] n_def[symmetric]
  let ?Tv = "transpose_mat (sylvester_mat p q) *\<^sub>v v"
  have dim: "dim_vec (vec_first v n) = n" "dim_vec (vec_last v m) = m" "dim_vec ?Tv = n + m" 
    using v by auto
  have if_distrib: "\<And> x y z. (if x then y else (0 :: 'a)) * z = (if x then y * z else 0)" 
    by auto
  show "coeff ?l i = coeff ?r i"
  proof (cases "i < m+n")
    case False
      hence i_mn: "i \<ge> m+n"
        and i_n: "\<And>x. x \<le> i \<and> x < n \<longleftrightarrow> x < n"
        and i_m: "\<And>x. x \<le> i \<and> x < m \<longleftrightarrow> x < m" by auto
      have "coeff ?r i =
            (\<Sum> x < n. vec_first v n $ (n - Suc x) * coeff p (i - x)) +
            (\<Sum> x < m. vec_last v m $ (m - Suc x) * coeff q (i - x))"
        (is "_ = sum ?f _ + sum ?g _")
        unfolding coeff_add coeff_mult Let_def 
        unfolding coeff_poly_of_vec dim if_distrib
        unfolding atMost_def
        apply(subst sum.inter_filter[symmetric],simp)
        apply(subst sum.inter_filter[symmetric],simp)
        unfolding mem_Collect_eq
        unfolding i_n i_m
        unfolding lessThan_def by simp
      also { fix x assume x: "x < n"
        have "coeff p (i-x) = 0"
          apply(rule coeff_eq_0) using i_mn x unfolding m_def by auto
        hence "?f x = 0" by auto
      } hence "sum ?f {..<n} = 0" by auto
      also { fix x assume x: "x < m"
        have "coeff q (i-x) = 0"
          apply(rule coeff_eq_0) using i_mn x unfolding n_def by auto
        hence "?g x = 0" by auto
      } hence "sum ?g {..<m} = 0" by auto
      finally have "coeff ?r i = 0" by auto
      also from False have "0 = coeff ?l i"
        unfolding coeff_poly_of_vec dim sum.distrib[symmetric] by auto
      finally show ?thesis by auto
    next case True
      hence "coeff ?l i = (transpose_mat (sylvester_mat p q) *\<^sub>v v) $ (n + m - Suc i)"
        unfolding coeff_poly_of_vec dim sum.distrib[symmetric] by auto
      also have "... = coeff (p * poly_of_vec (vec_first v n) + q * poly_of_vec (vec_last v m)) i"
        apply(subst index_mult_mat_vec) using True apply simp
        apply(subst row_transpose) using True apply simp
        apply(subst col_sylvester)
        unfolding mn using True apply simp
        apply(subst vec_first_last_append[of v n m,symmetric]) using v apply(simp add: add.commute)
        apply(subst scalar_prod_append)
        apply (rule carrier_vecI,simp)+
        apply (subst vec_of_poly_rev_shifted_scalar_prod,simp,simp) using True apply simp
        apply (subst add.commute[of n m])
        apply (subst vec_of_poly_rev_shifted_scalar_prod,simp,simp) using True apply simp
        by simp
      also have "... =
        (\<Sum>x\<le>i. (if x < n then vec_first v n $ (n - Suc x) else 0) * coeff p (i - x)) +
        (\<Sum>x\<le>i. (if x < m then vec_last v m $ (m - Suc x) else 0) * coeff q (i - x))"
        unfolding coeff_poly_of_vec[of "vec_first v n",unfolded dim_vec_first,symmetric]
        unfolding coeff_poly_of_vec[of "vec_last v m",unfolded dim_vec_last,symmetric]
        unfolding coeff_mult[symmetric] by (simp add: mult.commute)
      also have "... = coeff ?r i"
        unfolding coeff_add coeff_mult Let_def
        unfolding coeff_poly_of_vec dim..
      finally show ?thesis.
  qed
qed
  
subsubsection \<open>Homomorphism and Resultant\<close>

text \<open>Here we prove Lemma~7.3.1 of the textbook.\<close>

lemma(in comm_ring_hom) resultant_sub_map_poly:
  fixes p q :: "'a poly"
  shows "hom (resultant_sub m n p q) = resultant_sub m n (map_poly hom p) (map_poly hom q)"
    (is "?l = ?r'")
proof -
  let ?mh = "map_poly hom"
  have "?l = det (sylvester_mat_sub m n (?mh p) (?mh q))"
    unfolding resultant_sub_def
    apply(subst sylvester_mat_sub_map[symmetric]) by auto
  thus ?thesis unfolding resultant_sub_def.
qed

(*
lemma (in comm_ring_hom) resultant_map_poly:
  fixes p q :: "'a poly"
    defines "p' \<equiv> map_poly hom p"
    defines "q' \<equiv> map_poly hom q"
    defines "m \<equiv> degree p"
    defines "n \<equiv> degree q"
    defines "m' \<equiv> degree p'"
    defines "n' \<equiv> degree q'"
    defines "r \<equiv> resultant p q"
    defines "r' \<equiv> resultant p' q'"
  shows "m' = m \<Longrightarrow> n' = n \<Longrightarrow> hom r = r'"
    and "m' = m \<Longrightarrow> hom r = hom (coeff p m')^(n-n') * r'"
    and "m' \<noteq> m \<Longrightarrow> n' = n \<Longrightarrow>
      hom r = (if even n then 1 else (-1)^(m-m')) * hom (coeff q n)^(m-m') * r'"
      (is "_ \<Longrightarrow> _ \<Longrightarrow> ?goal")
    and "m' \<noteq> m \<Longrightarrow> n' \<noteq> n \<Longrightarrow> hom r = 0"
proof -
  have m'm: "m' \<le> m" unfolding m_def m'_def p'_def using degree_map_poly_le by auto
  have n'n: "n' \<le> n" unfolding n_def n'_def q'_def using degree_map_poly_le by auto

  have coeffp'[simp]: "\<And>i. coeff p' i = hom (coeff p i)" unfolding p'_def by auto
  have coeffq'[simp]: "\<And>i. coeff q' i = hom (coeff q i)" unfolding q'_def by auto

  let ?f = "\<lambda>i. (if even n then 1 else (-1)^i) * hom (coeff q n)^i"

  have "hom r = resultant_sub m n p' q'"
    unfolding r_def resultant_sub
    unfolding m_def n_def p'_def q'_def
    by(rule resultant_sub_map_poly)
  also have "... = ?f (m-m') * resultant_sub m' n p' q'"
    using resultant_sub_trim_upper[of p' "m-m'" n q',folded m'_def] m'm
    by (auto simp: power_minus[symmetric])
  also have "... = ?f (m-m') * hom (coeff p m')^(n-n') * r'"
    using resultant_sub_trim_lower[of m' q' "n-n'" p'] n'n
    unfolding r'_def resultant_sub m'_def n'_def by auto
  finally have main: "hom r = ?f (m-m') * hom (coeff p m')^(n-n') * r'" by auto

  { assume "m' = m"
    thus "hom r = hom (coeff p m')^(n-n') * r'" using main by auto
    thus "n' = n \<Longrightarrow> hom r = r'" by auto
  }
  assume "m' \<noteq> m"
  hence m'm: "m' < m" using m'm by auto
  thus "n' = n \<Longrightarrow> ?goal" using main by simp
  assume "n' \<noteq> n"
  hence "n' < n" using n'n by auto
  hence "hom (coeff q n) = 0"
    unfolding coeffq'[symmetric] unfolding n'_def by(rule coeff_eq_0)
  hence "hom (coeff q n) ^ (m-m') = 0" using m'm by (simp add: power_0_left)
  from main[unfolded this]
  show "hom r = 0" using power_0_Suc by auto
qed
*)
  
subsubsection\<open>Resultant as Polynomial Expression\<close>
context begin
text \<open>This context provides notions for proving Lemma 7.2.1 of the textbook.\<close>

private fun mk_poly_sub where
  "mk_poly_sub A l 0 = A"
| "mk_poly_sub A l (Suc j) = mat_addcol (monom 1 (Suc j)) l (l-Suc j) (mk_poly_sub A l j)"

definition  "mk_poly A = mk_poly_sub (map_mat coeff_lift A) (dim_col A - 1) (dim_col A - 1)"

private lemma mk_poly_sub_dim[simp]:
  "dim_row (mk_poly_sub A l j) = dim_row A"
  "dim_col (mk_poly_sub A l j) = dim_col A"
  by (induct j,auto)

private lemma mk_poly_sub_carrier:
  assumes "A \<in> carrier_mat nr nc" shows "mk_poly_sub A l j \<in> carrier_mat nr nc"
  apply (rule carrier_matI) using assms by auto

private lemma mk_poly_dim[simp]:
  "dim_col (mk_poly A) = dim_col A"
  "dim_row (mk_poly A) = dim_row A"
  unfolding mk_poly_def by auto

private lemma mk_poly_sub_others[simp]:
  assumes "l \<noteq> j'" and "i < dim_row A" and "j' < dim_col A"
  shows "mk_poly_sub A l j $$ (i,j') = A $$ (i,j')"
  using assms by (induct j; simp)

private lemma mk_poly_others[simp]:
  assumes i: "i < dim_row A" and j: "j < dim_col A - 1"
  shows "mk_poly A $$ (i,j) = [: A $$ (i,j) :]"
  unfolding mk_poly_def
  apply(subst mk_poly_sub_others)
  using i j by auto

private lemma mk_poly_delete[simp]:
  assumes i: "i < dim_row A"
  shows "mat_delete (mk_poly A) i (dim_col A - 1) = map_mat coeff_lift (mat_delete A i (dim_col A - 1))"
  apply(rule eq_matI) unfolding mat_delete_def by auto

private lemma col_mk_poly_sub[simp]:
  assumes "l \<noteq> j'" and "j' < dim_col A"
  shows "col (mk_poly_sub A l j) j' = col A j'"
  by(rule eq_vecI; insert assms; simp)

private lemma det_mk_poly_sub:
  assumes A: "(A :: 'a :: comm_ring_1 poly mat) \<in> carrier_mat n n" and i: "i < n"
  shows "det (mk_poly_sub A (n-1) i) = det A"
  using i
proof (induct i)
  case (Suc i)
    show ?case unfolding mk_poly_sub.simps
    apply(subst det_addcol[of _ n])
      using Suc apply simp
      using Suc apply simp
      apply (rule mk_poly_sub_carrier[OF A])
      using Suc by auto
qed simp

private lemma det_mk_poly:
  fixes A :: "'a :: comm_ring_1 mat"
  shows "det (mk_poly A) = [: det A :]"
proof (cases "dim_row A = dim_col A")
  case True
    define n where "n = dim_col A"
    have "map_mat coeff_lift A \<in> carrier_mat (dim_row A) (dim_col A)" by simp
    hence sq: "map_mat coeff_lift A \<in> carrier_mat (dim_col A) (dim_col A)" unfolding True.
    show ?thesis
    proof(cases "dim_col A = 0")
      case True thus ?thesis unfolding det_def by simp
      next case False thus ?thesis
      unfolding mk_poly_def
      by (subst det_mk_poly_sub[OF sq]; simp)
    qed
  next case False
    hence f2: "dim_row A = dim_col A \<longleftrightarrow> False" by simp
    hence f3: "dim_row (mk_poly A) = dim_col (mk_poly A) \<longleftrightarrow> False"
      unfolding mk_poly_dim by auto
    show ?thesis unfolding det_def unfolding f2 f3 if_False by simp
qed

private fun mk_poly2_row where
  "mk_poly2_row A d j pv 0 = pv"
| "mk_poly2_row A d j pv (Suc n) =
   mk_poly2_row A d j pv n |\<^sub>v n \<mapsto> pv $ n + monom (A$$(n,j)) d"

private fun mk_poly2_col where
  "mk_poly2_col A pv 0 = pv"
| "mk_poly2_col A pv (Suc m) =
   mk_poly2_row A m (dim_col A - Suc m) (mk_poly2_col A pv m) (dim_row A)"

private definition "mk_poly2 A \<equiv> mk_poly2_col A (0\<^sub>v (dim_row A)) (dim_col A)"

private lemma mk_poly2_row_dim[simp]: "dim_vec (mk_poly2_row A d j pv i) = dim_vec pv"
  by(induct i arbitrary: pv, auto)

private lemma mk_poly2_col_dim[simp]: "dim_vec (mk_poly2_col A pv j) = dim_vec pv"
  by (induct j arbitrary: pv, auto)

private lemma mk_poly2_row:
  assumes n: "n \<le> dim_vec pv"
  shows "mk_poly2_row A d j pv n $ i =
    (if i < n then pv $ i + monom (A $$ (i,j)) d else pv $ i)"
  using n
proof (induct n arbitrary: pv)
  case (Suc n) thus ?case
    unfolding mk_poly2_row.simps by (cases rule: linorder_cases[of "i" "n"],auto)
qed simp

private lemma mk_poly2_row_col:
  assumes dim[simp]: "dim_vec pv = n" "dim_row A = n" and j: "j < dim_col A"
  shows "mk_poly2_row A d j pv n = pv + map_vec (\<lambda>a. monom a d) (col A j)"
  apply rule using mk_poly2_row[of _ pv] j by auto

private lemma mk_poly2_col:
  fixes pv :: "'a :: comm_semiring_1 poly vec" and A :: "'a mat"
  assumes i: "i < dim_row A" and dim: "dim_row A = dim_vec pv"
  shows "mk_poly2_col A pv j $ i = pv $ i + (\<Sum>j'<j. monom (A $$ (i, dim_col A - Suc j')) j')"
  using dim
proof (induct j arbitrary: pv)
  case (Suc j) show ?case
    unfolding mk_poly2_col.simps
    apply (subst mk_poly2_row)
      using Suc apply simp
    unfolding Suc(1)[OF Suc(2)]
    using i by (simp add: add.assoc)
qed simp

private lemma mk_poly2_pre:
  fixes A :: "'a :: comm_semiring_1 mat"
  assumes i: "i < dim_row A"
  shows "mk_poly2 A $ i = (\<Sum>j'<dim_col A. monom (A $$ (i, dim_col A - Suc j')) j')"
  unfolding mk_poly2_def
  apply(subst mk_poly2_col) using i by auto

private lemma mk_poly2:
  fixes A :: "'a :: comm_semiring_1 mat"
  assumes i: "i < dim_row A"
      and c: "dim_col A > 0"
  shows "mk_poly2 A $ i = (\<Sum>j'<dim_col A. monom (A $$ (i,j')) (dim_col A - Suc  j'))"
    (is "?l = sum ?f ?S")
proof -
  define l where "l = dim_col A - 1"
  have dim: "dim_col A = Suc l" unfolding l_def using i c by auto
  let ?g = "\<lambda>j. l - j"
  have "?l = sum (?f \<circ> ?g) ?S" unfolding l_def mk_poly2_pre[OF i] by auto
  also have "... = sum ?f ?S"
    unfolding dim
    unfolding lessThan_Suc_atMost
    using sum.reindex[OF inj_on_diff_nat2,symmetric,unfolded image_diff_atMost].
  finally show ?thesis.
qed

private lemma mk_poly2_sylvester_upper:
  fixes p q :: "'a :: comm_semiring_1 poly"
  assumes i: "i < degree q"
  shows "mk_poly2 (sylvester_mat p q) $ i = monom 1 (degree q - Suc i) * p"
  apply (subst mk_poly2)
    using i apply simp using i apply simp
  apply (subst sylvester_sum_mat_upper[OF i,symmetric])
  apply (rule sum.cong)
    unfolding sylvester_mat_dim lessThan_Suc_atMost apply simp
  by auto

private lemma mk_poly2_sylvester_lower:
  fixes p q :: "'a :: comm_semiring_1 poly"
  assumes mi: "i \<ge> degree q" and imn: "i < degree p + degree q"
  shows "mk_poly2 (sylvester_mat p q) $ i = monom 1 (degree p + degree q - Suc i) * q"
  apply (subst mk_poly2)
    using imn apply simp using mi imn apply simp
  unfolding sylvester_mat_dim
  using sylvester_sum_mat_lower[OF mi imn]
  apply (subst sylvester_sum_mat_lower) using mi imn by auto

private lemma foo:
  fixes v :: "'a :: comm_semiring_1 vec"
  shows "monom 1 d \<cdot>\<^sub>v map_vec coeff_lift v = map_vec (\<lambda>a. monom a d) v"
  apply (rule eq_vecI)
  unfolding index_map_vec index_col
  by (auto simp add: Polynomial.smult_monom)

private lemma mk_poly_sub_corresp:
  assumes dimA[simp]: "dim_col A = Suc l" and dimpv[simp]: "dim_vec pv = dim_row A"
      and j: "j < dim_col A"
  shows "pv + col (mk_poly_sub (map_mat coeff_lift A) l j) l =
    mk_poly2_col A pv (Suc j)"
proof(insert j, induct j)
  have le: "dim_row A \<le> dim_vec pv" using dimpv by simp
  have l: "l < dim_col A" using dimA by simp
  { case 0 show ?case
      apply (rule eq_vecI)
      using mk_poly2_row[OF le]
      by (auto simp add: monom_0)
  }
  { case (Suc j)
      hence j: "j < dim_col A" by simp
      show ?case
        unfolding mk_poly_sub.simps
        apply(subst col_addcol)
          apply simp
          apply simp
        apply(subst(2) comm_add_vec)
          apply(rule carrier_vecI, simp)
          apply(rule carrier_vecI, simp)
        apply(subst assoc_add_vec[symmetric])
          apply(rule carrier_vecI, rule refl)
          apply(rule carrier_vecI, simp)
          apply(rule carrier_vecI, simp)
        unfolding Suc(1)[OF j]
        apply(subst(2) mk_poly2_col.simps)
        apply(subst mk_poly2_row_col)
          apply simp
          apply simp
          using Suc apply simp
        apply(subst col_mk_poly_sub)
          using Suc apply simp
          using Suc apply simp
        apply(subst col_map_mat)
          using dimA apply simp
        unfolding foo dimA by simp
  }
qed

private lemma col_mk_poly_mk_poly2:
  fixes A :: "'a :: comm_semiring_1 mat"
  assumes dim: "dim_col A > 0"
  shows "col (mk_poly A) (dim_col A - 1) = mk_poly2 A"
proof -
  define l where "l = dim_col A - 1"
  have dim: "dim_col A = Suc l" unfolding l_def using dim by auto
  show ?thesis
    unfolding mk_poly_def mk_poly2_def dim
    apply(subst mk_poly_sub_corresp[symmetric])
      apply(rule dim)
      apply simp
      using dim apply simp
    apply(subst left_zero_vec)
      apply(rule carrier_vecI) using dim apply simp
    apply simp
    done
qed

private lemma mk_poly_mk_poly2:
  fixes A :: "'a :: comm_semiring_1 mat"
  assumes dim: "dim_col A > 0" and i: "i < dim_row A"
  shows "mk_poly A $$ (i,dim_col A - 1) = mk_poly2 A $ i"
proof -
  have "mk_poly A $$ (i,dim_col A - 1) = col (mk_poly A) (dim_col A - 1) $ i"
    apply (subst index_col(1)) using dim i by auto
  also note col_mk_poly_mk_poly2[OF dim] 
  finally show ?thesis.
qed

lemma mk_poly_sylvester_upper:
  fixes p q :: "'a :: comm_ring_1 poly"
  defines "m \<equiv> degree p" and "n \<equiv> degree q"
  assumes i: "i < n"
  shows "mk_poly (sylvester_mat p q) $$ (i, m + n - 1) = monom 1 (n - Suc i) * p" (is "?l = ?r")
proof -
  let ?S = "sylvester_mat p q"
  have c: "m+n = dim_col ?S" and r: "m+n = dim_row ?S" unfolding m_def n_def by auto
  hence "dim_col ?S > 0" "i < dim_row ?S" using i by auto
  from mk_poly_mk_poly2[OF this]
  have "?l = mk_poly2 (sylvester_mat p q) $ i" unfolding m_def n_def by auto
  also have "... = ?r"
    apply(subst mk_poly2_sylvester_upper)
      using i unfolding n_def m_def by auto
  finally show ?thesis.
qed

lemma mk_poly_sylvester_lower:
  fixes p q :: "'a :: comm_ring_1 poly"
  defines "m \<equiv> degree p" and "n \<equiv> degree q"
  assumes ni: "n \<le> i" and imn: "i < m+n"
  shows "mk_poly (sylvester_mat p q) $$ (i, m + n - 1) = monom 1 (m + n - Suc i) * q" (is "?l = ?r")
proof -
  let ?S = "sylvester_mat p q"
  have c: "m+n = dim_col ?S" and r: "m+n = dim_row ?S" unfolding m_def n_def by auto
  hence "dim_col ?S > 0" "i < dim_row ?S" using imn by auto
  from mk_poly_mk_poly2[OF this]
  have "?l = mk_poly2 (sylvester_mat p q) $ i" unfolding m_def n_def by auto
  also have "... = ?r"
    apply(subst mk_poly2_sylvester_lower)
      using ni imn unfolding n_def m_def by auto
  finally show ?thesis.
qed

text \<open>The next lemma corresponds to Lemma 7.2.1.\<close>
lemma resultant_as_poly:
  fixes p q :: "'a :: comm_ring_1 poly"
  assumes degp: "degree p > 0" and degq: "degree q > 0"
  shows "\<exists>p' q'. degree p' < degree q \<and> degree q' < degree p \<and>
         [: resultant p q :] = p' * p + q' * q"
proof (intro exI conjI)
  define m where "m = degree p"
  define n where "n = degree q"
  define d where "d = dim_row (mk_poly (sylvester_mat p q))"
  define c where "c = (\<lambda>i. coeff_lift (cofactor (sylvester_mat p q) i (m+n-1)))"
  define p' where "p' = (\<Sum>i<n. monom 1 (n - Suc i) * c i)"
  define q' where "q' = (\<Sum>i<m. monom 1 (m - Suc i) * c (n+i))"

  have degc: "\<And>i. degree (c i) = 0" unfolding c_def by auto

  have dmn: "d = m+n" and mnd: "m + n = d" unfolding d_def m_def n_def by auto
  have "[: resultant p q :] =
    (\<Sum>i<d. mk_poly (sylvester_mat p q) $$ (i,m+n-1) *
        cofactor (mk_poly (sylvester_mat p q)) i (m+n-1))"
    unfolding resultant_def
    unfolding det_mk_poly[symmetric]
    unfolding m_def n_def d_def
    apply(rule laplace_expansion_column[of _ _ "degree p + degree q - 1"])
    apply(rule carrier_matI) using degp by auto
  also { fix i assume i: "i<d"
    have d2: "d = dim_row (sylvester_mat p q)" unfolding d_def by auto
    have "cofactor (mk_poly (sylvester_mat p q)) i (m+n-1) =
      (- 1) ^ (i + (m+n-1)) * det (mat_delete (mk_poly (sylvester_mat p q)) i (m+n-1))"
      using cofactor_def.
    also have "... =
      (- 1) ^ (i+m+n-1) * coeff_lift (det (mat_delete (sylvester_mat p q) i (m+n-1)))"
      using mk_poly_delete[OF i[unfolded d2]] degp degq
      unfolding m_def n_def by (auto simp add: add.assoc)
    also have "i+m+n-1 = i+(m+n-1)" using i[folded mnd] by auto
    finally have "cofactor (mk_poly (sylvester_mat p q)) i (m+n-1) = c i"
      unfolding c_def cofactor_def hom_distribs by simp
  }
  hence "... = (\<Sum>i<d. mk_poly (sylvester_mat p q) $$ (i, m+n-1) * c i)"
    (is "_ = sum ?f _") by auto
  also have "... = sum ?f ({..<n} \<union> {n ..<d})" unfolding dmn apply(subst ivl_disj_un(8)) by auto
  also have "... = sum ?f {..<n} + sum ?f {n..<d}" apply(subst sum.union_disjoint) by auto
  also { fix i assume i: "i < n"
    have "?f i = monom 1 (n - Suc i) * c i * p"
      unfolding m_def n_def
      apply(subst mk_poly_sylvester_upper)
      using i unfolding n_def by auto
  }
  hence "sum ?f {..<n} = p' * p" unfolding p'_def sum_distrib_right by auto 
  also { fix i assume i: "i \<in> {n..<d}"
    have "?f i = monom 1 (m + n - Suc i) * c i * q"
      unfolding m_def n_def
      apply(subst mk_poly_sylvester_lower)
      using i unfolding dmn n_def m_def by auto
  }
  hence "sum ?f {n..<d} = (\<Sum>i=n..<d. monom 1 (m + n - Suc i) * c i) * q"
    (is "_ = sum ?h _ * _") unfolding sum_distrib_right by auto
  also have "{n..<d} = (\<lambda>i. i+n) ` {0..<m}"
    by (simp add: dmn)
  also have "sum ?h ... = sum (?h \<circ> (\<lambda>i. i+n)) {0..<m}"
    apply(subst sum.reindex[symmetric])
    apply (rule inj_onI) by auto
  also have "... = q'" unfolding q'_def apply(rule sum.cong) by (auto simp add: add.commute)
  finally show main: "[:resultant p q:] = p' * p + q' * q".
  show "degree p' < n"
    unfolding p'_def
    apply(rule degree_sum_smaller)
    using degq[folded n_def] apply force+
  proof -
    fix i assume i: "i \<in> {..<n}"
    show "degree (monom 1 (n - Suc i) * c i) < n"
      apply (rule order.strict_trans1)
      apply (rule degree_mult_le)
      unfolding add.right_neutral degc
      apply (rule order.strict_trans1)
      apply (rule degree_monom_le) using i by auto
  qed
  show "degree q' < m"
    unfolding q'_def
    apply (rule degree_sum_smaller)
    using degp[folded m_def] apply force+
  proof -
    fix i assume i: "i \<in> {..<m}"
    show "degree (monom 1 (m-Suc i) * c (n+i)) < m"
    apply (rule order.strict_trans1)
    apply (rule degree_mult_le)
    unfolding add.right_neutral degc
    apply (rule order.strict_trans1)
    apply (rule degree_monom_le) using i by auto
  qed
qed

end

subsubsection \<open>Resultant as Nonzero Polynomial Expression\<close>

lemma resultant_zero:
  fixes p q :: "'a :: comm_ring_1 poly"
  assumes deg: "degree p > 0 \<or> degree q > 0"
      and xp: "poly p x = 0" and xq: "poly q x = 0"
  shows "resultant p q = 0"
proof -
  { assume degp: "degree p > 0" and degq: "degree q > 0"
    obtain p' q' where "[: resultant p q :] = p' * p + q' * q"
      using resultant_as_poly[OF degp degq] by force
    hence "resultant p q = poly (p' * p + q' * q) x"
      using mpoly_base_conv(2)[of "resultant p q"] by auto
    also have "... = poly p x * poly p' x + poly q x * poly q' x"
      unfolding poly2_def by simp
    finally have ?thesis using xp xq by simp
  } moreover
  { assume degp: "degree p = 0"
    have p: "p = [:0:]" using xp degree_0_id[OF degp,symmetric] by (metis mpoly_base_conv(2))
    have ?thesis unfolding p using degp deg by simp
  } moreover
  { assume degq: "degree q = 0"
    have q: "q = [:0:]" using xq degree_0_id[OF degq,symmetric] by (metis mpoly_base_conv(2))
    have ?thesis unfolding q using degq deg by simp
  }
  ultimately show ?thesis by auto
qed

lemma poly_resultant_zero:
  fixes p q :: "'a :: comm_ring_1 poly poly"
  assumes deg: "degree p > 0 \<or> degree q > 0"
  assumes p0: "poly2 p x y = 0" and q0: "poly2 q x y = 0"
  shows "poly (resultant p q) x = 0"
proof -
  { assume "degree p > 0" "degree q > 0"
    from resultant_as_poly[OF this]
    obtain p' q' where "[: resultant p q :] = p' * p + q' * q" by force
    hence "resultant p q = poly (p' * p + q' * q) [:y:]"
      using mpoly_base_conv(2)[of "resultant p q"] by auto
    also have "poly ... x = poly2 p x y * poly2 p' x y + poly2 q x y * poly2 q' x y"
      unfolding poly2_def by simp
    finally have ?thesis unfolding p0 q0 by simp
  } moreover {
    assume degp: "degree p = 0"
    hence p: "p = [: coeff p 0 :]" by(subst degree_0_id[OF degp,symmetric],simp)
    hence "resultant p q = coeff p 0 ^ degree q" using resultant_const(1) by metis
    also have "poly ... x = poly (coeff p 0) x ^ degree q" by auto
    also have "... = poly2 p x y ^ degree q" unfolding poly2_def by(subst p, auto)
    finally have ?thesis unfolding p0 using deg degp zero_power by auto
  } moreover {
    assume degq: "degree q = 0"
    hence q: "q = [: coeff q 0 :]" by(subst degree_0_id[OF degq,symmetric],simp)
    hence "resultant p q = coeff q 0 ^ degree p" using resultant_const(2) by metis
    also have "poly ... x = poly (coeff q 0) x ^ degree p" by auto
    also have "... = poly2 q x y ^ degree p" unfolding poly2_def by(subst q, auto)
    finally have ?thesis unfolding q0 using deg degq zero_power by auto
  }
  ultimately show ?thesis by auto
qed

lemma resultant_as_nonzero_poly_weak:
  fixes p q :: "'a :: idom poly"
  assumes degp: "degree p > 0" and degq: "degree q > 0"
      and r0: "resultant p q \<noteq> 0"
  shows "\<exists>p' q'. degree p' < degree q \<and> degree q' < degree p \<and>
         [: resultant p q :] = p' * p + q' * q \<and> p' \<noteq> 0 \<and> q' \<noteq> 0"
proof -
  obtain p' q'
    where deg: "degree p' < degree q" "degree q' < degree p"
      and main: "[: resultant p q :] = p' * p + q' * q"
      using resultant_as_poly[OF degp degq] by auto
  have p0: "p \<noteq> 0" using degp by auto
  have q0: "q \<noteq> 0" using degq by auto
  show ?thesis
  proof (intro exI conjI notI)
    assume "p' = 0"
    hence "[: resultant p q :] = q' * q" using main by auto
    also hence d0: "0 = degree (q' * q)" by (metis degree_pCons_0)
      { assume "q' \<noteq> 0"
        hence "degree (q' * q) = degree q' + degree q"
          apply(rule degree_mult_eq) using q0 by auto
        hence False using d0 degq by auto
      } hence "q' = 0" by auto
    finally show False using r0 by auto
  next
    assume "q' = 0"
    hence "[: resultant p q :] = p' * p" using main by auto
    also
      hence d0: "0 = degree (p' * p)" by (metis degree_pCons_0)
      { assume "p' \<noteq> 0"
        hence "degree (p' * p) = degree p' + degree p"
          apply(rule degree_mult_eq) using p0 by auto
        hence False using d0 degp by auto
      } hence "p' = 0" by auto
    finally show False using r0 by auto
  qed fact+
qed

text \<open> Next lemma corresponds to Lemma 7.2.2 of the textbook \<close>

lemma resultant_as_nonzero_poly:
  fixes p q :: "'a :: idom poly"
  defines "m \<equiv> degree p" and "n \<equiv> degree q"
  assumes degp: "m > 0" and degq: "n > 0"
  shows "\<exists>p' q'. degree p' < n \<and> degree q' < m \<and>
         [: resultant p q :] = p' * p + q' * q \<and> p' \<noteq> 0 \<and> q' \<noteq> 0"
proof (cases "resultant p q = 0")
  case False
  thus ?thesis
    using resultant_as_nonzero_poly_weak degp degq
    unfolding m_def n_def by auto
next case True
  define S where "S = transpose_mat (sylvester_mat p q)"
  have S: "S \<in> carrier_mat (m+n) (m+n)" unfolding S_def m_def n_def by auto
  have "det S = 0" using True
    unfolding resultant_def S_def apply (subst det_transpose) by auto
  then obtain v
    where v: "v \<in> carrier_vec (m+n)" and v0: "v \<noteq> 0\<^sub>v (m+n)" and "S *\<^sub>v v = 0\<^sub>v (m+n)"
    using det_0_iff_vec_prod_zero[OF S] by auto
  hence "poly_of_vec (S *\<^sub>v v) = 0" by auto
  hence main: "poly_of_vec (vec_first v n) * p + poly_of_vec (vec_last v m) * q = 0"
    (is "?p * _ + ?q * _ = _")
    using sylvester_vec_poly[OF v[unfolded m_def n_def], folded m_def n_def S_def]
    by auto
  have split: "vec_first v n @\<^sub>v vec_last v m = v"
    using vec_first_last_append[simplified add.commute] v by auto
  show ?thesis
  proof(intro exI conjI)
    show "[: resultant p q :] = ?p * p + ?q * q" unfolding True using main by auto
    show "?p \<noteq> 0"
    proof
      assume p'0: "?p = 0"
      hence "?q * q = 0" using main by auto
      hence "?q = 0" using degq n_def by auto
      hence "vec_last v m = 0\<^sub>v m" unfolding poly_of_vec_0_iff by auto
      also have "vec_first v n @\<^sub>v ... = 0\<^sub>v (m+n)" using p'0 unfolding poly_of_vec_0_iff by auto
      finally have "v = 0\<^sub>v (m+n)" using split by auto
      thus False using v0 by auto
    qed
    show "?q \<noteq> 0"
    proof
      assume q'0: "?q = 0"
      hence "?p * p = 0" using main by auto
      hence "?p = 0" using degp m_def by auto
      hence "vec_first v n = 0\<^sub>v n" unfolding poly_of_vec_0_iff by auto
      also have "... @\<^sub>v vec_last v m = 0\<^sub>v (m+n)" using q'0 unfolding poly_of_vec_0_iff by auto
      finally have "v = 0\<^sub>v (m+n)" using split by auto
      thus False using v0 by auto
    qed
    show "degree ?p < n" using degree_poly_of_vec_less[of "vec_first v n"] using degq by auto
    show "degree ?q < m" using degree_poly_of_vec_less[of "vec_last v m"] using degp by auto
  qed
qed

text\<open>Corresponds to Lemma 7.2.3 of the textbook\<close>

lemma resultant_zero_imp_common_factor:
  fixes p q :: "'a :: ufd poly"
  assumes deg: "degree p > 0 \<or> degree q > 0" and r0: "resultant p q = 0"
  shows "\<not> coprime p q"
  unfolding neq0_conv[symmetric]
proof -
  { assume degp: "degree p > 0" and degq: "degree q > 0"
    assume cop: "coprime p q"
    obtain p' q' where "p' * p + q' * q = 0"
      and p': "degree p' < degree q" and q': "degree q' < degree p"
      and p'0: "p' \<noteq> 0" and q'0: "q' \<noteq> 0"
      using resultant_as_nonzero_poly[OF degp degq] r0 by auto
    hence "p' * p = - q' * q" by (simp add: eq_neg_iff_add_eq_0)
    
    from some_gcd.coprime_mult_cross_dvd[OF cop this]
    have "p dvd q'" by auto
    from dvd_imp_degree_le[OF this q'0]
    have "degree p \<le> degree q'" by auto
    hence False using q' by auto
  }
  moreover
  { assume degp: "degree p = 0"
    then obtain x where "p = [:x:]" by (elim degree_eq_zeroE)
    moreover hence "resultant p q = x ^ degree q" using resultant_const by auto
      hence "x = 0" using r0 by auto
    ultimately have "p = 0" by auto
    hence ?thesis unfolding not_coprime_iff_common_factor
      by (metis deg degp dvd_0_right dvd_refl less_numeral_extra(3) poly_dvd_1)
  }
  moreover
  { assume degq: "degree q = 0"
    then obtain x where "q = [:x:]" by (elim degree_eq_zeroE)
    moreover hence "resultant p q = x ^ degree p" using resultant_const by auto
      hence "x = 0" using r0 by auto
    ultimately have "q = 0" by auto
    hence ?thesis unfolding not_coprime_iff_common_factor
      by (metis deg degq dvd_0_right dvd_refl less_numeral_extra(3) poly_dvd_1)
  }
  ultimately show ?thesis by auto
qed

lemma resultant_non_zero_imp_coprime:
  assumes nz: "resultant (f :: 'a :: field poly) g \<noteq> 0" 
  and nz': "f \<noteq> 0 \<or> g \<noteq> 0" 
shows "coprime f g" 
proof (cases "degree f = 0 \<or> degree g = 0")
  case False
  define r where "r = [:resultant f g:]" 
  from nz have r: "r \<noteq> 0" unfolding r_def by auto
  from False have "degree f > 0" "degree g > 0" by auto
  from resultant_as_nonzero_poly_weak[OF this nz]
  obtain p q where "degree p < degree g" "degree q < degree f" 
    and id: "r = p * f + q * g"
    and "p \<noteq> 0" "q \<noteq> 0" unfolding r_def by auto
  define h where "h = some_gcd f g"
  have "h dvd f" "h dvd g" unfolding h_def by auto
  then obtain j k where f: "f = h * j" and g: "g = h * k" unfolding dvd_def by auto
  from id[unfolded f g] have id: "h * (p * j + q * k) = r" by (auto simp: field_simps)
  from arg_cong[OF id, of degree] have "degree (h * (p * j + q * k)) = 0" 
    unfolding r_def by auto
  also have "degree (h * (p * j + q * k)) = degree h + degree (p * j + q * k)" 
    by (subst degree_mult_eq, insert id r, auto)
  finally have h: "degree h = 0" "h \<noteq> 0" using r id by auto
  thus ?thesis unfolding h_def using is_unit_iff_degree some_gcd.gcd_dvd_1 by blast
next
  case True
  {
    fix f g :: "'a poly"
    assume deg_g: "degree g = 0" and res: "resultant f g \<noteq> 0" and nz: "f \<noteq> 0 \<or> g \<noteq> 0"
    have "coprime f g"
    proof (cases "g = 0")
      case False
      then show ?thesis using divides_degree[of _ g, unfolded deg_g]
        by (simp add: is_unit_right_imp_coprime) 
    next
      case g: True
      then have "g = [:0:]" by auto
      from res[unfolded this resultant_const] have "degree f = 0" by auto
      with nz show ?thesis unfolding g by auto
    qed
  } note main = this
  from True
  show ?thesis
  proof
    assume f: "degree f = 0" 
    from nz[unfolded resultant_swap[of f g]] have "resultant g f \<noteq> 0" by (auto split: if_splits)
    from main[OF f this] nz' show ?thesis by (auto simp: ac_simps)
  next
    assume "degree g = 0" 
    from main[OF this nz nz'] show ?thesis .
  qed
qed

end
