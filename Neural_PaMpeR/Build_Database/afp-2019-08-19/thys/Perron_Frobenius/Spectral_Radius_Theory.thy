section \<open>Combining Spectral Radius Theory with Perron Frobenius theorem\<close>

theory Spectral_Radius_Theory
imports 
  Polynomial_Factorization.Square_Free_Factorization
  Jordan_Normal_Form.Spectral_Radius
  Jordan_Normal_Form.Char_Poly
  Perron_Frobenius
  "HOL-Computational_Algebra.Field_as_Ring"
begin
abbreviation spectral_radius where "spectral_radius \<equiv> Spectral_Radius.spectral_radius"
hide_const (open) Module.smult

text \<open>Via JNFs it has been proven that the growth of $A^k$ is polynomially bounded,
  if all complex eigenvalues have a norm at most 1, i.e., the spectral radius must be
  at most 1. Moreover, the degree of the polynomial growth can be 
  bounded by the order of those roots which have norm 1, cf. @{thm spectral_radius_poly_bound}.\<close>

text \<open>Perron Frobenius theorem tells us that for a real valued non negative matrix,
  the largest eigenvalue is a real non-negative one. Hence, we only have to check, that all real 
  eigenvalues are at most one.\<close> 

text \<open>We combine both theorems in the following. To be more precise,
  the set-based complexity results from JNFs with the type-based
  Perron Frobenius theorem in HMA are connected to obtain 
  a set based complexity criterion for real-valued
  non-negative matrices, where one only investigated the real valued eigenvalues for
  checking the eigenvalue-at-most-1 condition.  
  Here, in the precondition of the roots of the polynomial, the type-system ensures
  that we only have to look at real-valued eigenvalues, and can ignore the 
  complex-valued ones.

  The linkage between set-and type-based is performed via HMA-connect.\<close>

lemma perron_frobenius_spectral_radius_complex: fixes A :: "complex mat"
  assumes A: "A \<in> carrier_mat n n"
  and real_nonneg: "real_nonneg_mat A"
  and ev_le_1: "\<And> x. poly (char_poly (map_mat Re A)) x = 0 \<Longrightarrow> x \<le> 1"
  and ev_order: "\<And> x. norm x = 1 \<Longrightarrow> order x (char_poly A) \<le> d"
  shows "\<exists>c1 c2. \<forall>k. norm_bound (A ^\<^sub>m k) (c1 + c2 * real k ^ (d - 1))"
proof (cases "n = 0")
  case False
  hence n: "n > 0" "n \<noteq> 0" by auto
  define sr where "sr = spectral_radius A"
  note sr = spectral_radius_mem_max[OF A n(1), folded sr_def]
  show ?thesis
  proof (rule spectral_radius_poly_bound[OF A], unfold sr_def[symmetric])
    let ?cr = "complex_of_real"
    text \<open>here is the transition from type-based perron-frobenius to set-based\<close>
    from perron_frobenius[untransferred, cancel_card_constraint, OF A real_nonneg n(2)]
      obtain v where v: "v \<in> carrier_vec n" and ev: "eigenvector A v (?cr sr)" and 
      rnn: "real_nonneg_vec v" unfolding sr_def by auto
    define B where "B = map_mat Re A"
    let ?A = "map_mat ?cr B"
    have AB: "A = ?A" unfolding B_def 
      by (rule eq_matI, insert real_nonneg[unfolded real_nonneg_mat_def elements_mat_def], auto)
    define w where "w = map_vec Re v"
    let ?v = "map_vec ?cr w"
    have vw: "v = ?v" unfolding w_def
      by (rule eq_vecI, insert rnn[unfolded real_nonneg_vec_def vec_elements_def], auto)
    have B: "B \<in> carrier_mat n n" unfolding B_def using A by auto
    from AB vw ev have ev: "eigenvector ?A ?v (?cr sr)" by simp
    have "eigenvector B w sr"
      by (rule of_real_hom.eigenvector_hom_rev[OF B ev])
    hence "eigenvalue B sr" unfolding eigenvalue_def by blast
    from ev_le_1[folded B_def, OF this[unfolded eigenvalue_root_char_poly[OF B]]]
    show "sr \<le> 1" .
  next
    fix ev
    assume "cmod ev = 1"
    thus "order ev (char_poly A) \<le> d" by (rule ev_order)
  qed
next
  case True
  with A show ?thesis
    by (intro exI[of _ 0], auto simp: norm_bound_def)
qed

text \<open>The following lemma is the same as @{thm perron_frobenius_spectral_radius_complex}, 
  except that now the type @{typ real} is used instead of @{typ complex}.\<close>

lemma perron_frobenius_spectral_radius: fixes A :: "real mat"
  assumes A: "A \<in> carrier_mat n n"
  and nonneg: "nonneg_mat A"
  and ev_le_1: "\<forall> x. poly (char_poly A) x = 0 \<longrightarrow> x \<le> 1"
  and ev_order: "\<forall> x :: complex. norm x = 1 \<longrightarrow> order x (map_poly of_real (char_poly A)) \<le> d"
  shows "\<exists>c1 c2. \<forall>k a. a \<in> elements_mat (A ^\<^sub>m k) \<longrightarrow> abs a \<le> (c1 + c2 * real k ^ (d - 1))"
proof -
  let ?cr = "complex_of_real"
  let ?B = "map_mat ?cr A"
  have B: "?B \<in> carrier_mat n n" using A by auto
  have rnn: "real_nonneg_mat ?B" using nonneg unfolding real_nonneg_mat_def nonneg_mat_def
    by (auto simp: elements_mat_def)
  have id: "map_mat Re ?B = A"
    by (rule eq_matI, auto)
  have "\<exists>c1 c2. \<forall>k. norm_bound (?B ^\<^sub>m k) (c1 + c2 * real k ^ (d - 1))"
    by (rule perron_frobenius_spectral_radius_complex[OF B rnn], unfold id, 
    insert ev_le_1 ev_order, auto simp: of_real_hom.char_poly_hom[OF A])
  then obtain c1 c2 where nb: "\<And> k. norm_bound (?B ^\<^sub>m k) (c1 + c2 * real k ^ (d - 1))" by auto
  show ?thesis
  proof (rule exI[of _ c1], rule exI[of _ c2], intro allI impI)
    fix k a
    assume "a \<in> elements_mat (A ^\<^sub>m k)"
    with pow_carrier_mat[OF A] obtain i j where a: "a = (A ^\<^sub>m k) $$ (i,j)" and ij: "i < n" "j < n"
      unfolding elements_mat by force
    from ij nb[of k] A have "norm ((?B ^\<^sub>m k) $$ (i,j)) \<le> c1 + c2 * real k ^ (d - 1)"
      unfolding norm_bound_def by auto
    also have "(?B ^\<^sub>m k) $$ (i,j) = ?cr a"
      unfolding of_real_hom.mat_hom_pow[OF A, symmetric] a using ij A by auto
    also have "norm (?cr a) = abs a" by auto
    finally show "abs a \<le> (c1 + c2 * real k ^ (d - 1))" .
  qed
qed

text \<open>We can also convert the set-based lemma @{thm perron_frobenius_spectral_radius}
  to a type-based version.\<close>

lemma perron_frobenius_spectral_type_based: 
  assumes "non_neg_mat (A :: real ^ 'n ^ 'n)"
  and "\<forall> x. poly (charpoly A) x = 0 \<longrightarrow> x \<le> 1"
  and "\<forall> x :: complex. norm x = 1 \<longrightarrow> order x (map_poly of_real (charpoly A)) \<le> d"
  shows "\<exists>c1 c2. \<forall>k a. a \<in> elements_mat_h (matpow A k) \<longrightarrow> abs a \<le> (c1 + c2 * real k ^ (d - 1))"
  using assms perron_frobenius_spectral_radius
  by (transfer, blast)

text \<open>And of course, we can also transfer the type-based lemma back to a set-based setting, 
  only that -- without further case-analysis -- 
  we get the additional assumption @{term "(n :: nat) \<noteq> 0"}.\<close>

lemma assumes "A \<in> carrier_mat n n"
  and "nonneg_mat A"
  and "\<forall> x. poly (char_poly A) x = 0 \<longrightarrow> x \<le> 1"
  and "\<forall> x :: complex. norm x = 1 \<longrightarrow> order x (map_poly of_real (char_poly A)) \<le> d"
  and "n \<noteq> 0"
  shows "\<exists>c1 c2. \<forall>k a. a \<in> elements_mat (A ^\<^sub>m k) \<longrightarrow> abs a \<le> (c1 + c2 * real k ^ (d - 1))"
  using perron_frobenius_spectral_type_based[untransferred, cancel_card_constraint, OF assms] .
   

text \<open>Note that the precondition eigenvalue-at-most-1 can easily be formulated as a cardinality
  constraints which can be decided by Sturm's theorem. 
  And in order to obtain a bound on the order, one can 
  perform a square-free-factorization (via Yun's factorization algorithm) 
  of the characteristic polynomial into
  $f_1^1 \cdot \ldots f_d^d$ where each $f_i$ has precisely the roots of order $i$.\<close>

context 
  fixes A :: "real mat" and c :: real and fis and n :: nat
  assumes A: "A \<in> carrier_mat n n"
  and nonneg: "nonneg_mat A"
  and yun: "yun_factorization gcd (char_poly A) = (c,fis)"
  and ev_le_1: "card {x. poly (char_poly A) x = 0 \<and> x > 1} = 0"
begin

text \<open>Note that @{const yun_factorization} has an offset by 1, 
  so the pair @{term "(f\<^sub>i,i) \<in> set fis"} encodes @{term "f\<^sub>i^(Suc i)"}.\<close>
lemma perron_frobenius_spectral_radius_yun: 
  assumes bnd: "\<And> f\<^sub>i i. (f\<^sub>i,i) \<in> set fis 
    \<Longrightarrow> (\<exists> x :: complex. poly (map_poly of_real f\<^sub>i) x = 0 \<and> norm x = 1) 
    \<Longrightarrow> Suc i \<le> d"
  shows "\<exists>c1 c2. \<forall>k a. a \<in> elements_mat (A ^\<^sub>m k) \<longrightarrow> abs a \<le> (c1 + c2 * real k ^ (d - 1))"
proof (rule perron_frobenius_spectral_radius[OF A nonneg]; intro allI impI)
  let ?cr = complex_of_real
  let ?cp = "map_poly ?cr (char_poly A)"
  fix x :: complex
  assume x: "norm x = 1"
  have A0: "char_poly A \<noteq> 0" using degree_monic_char_poly[OF A] by auto
  interpret field_hom_0' ?cr by (standard, auto)
  from A0 have cp0: "?cp \<noteq> 0" by auto
  obtain ox where ox: "order x ?cp = ox" by blast
  note sff = square_free_factorization_order_root[OF yun_factorization(1)[OF 
    yun_factorization_hom[of "char_poly A", unfolded yun map_prod_def split]] cp0, of x ox, unfolded ox]
  show "order x ?cp \<le> d" unfolding ox
  proof (cases ox)
    case (Suc oo)
    with sff obtain fi where mem: "(fi,oo) \<in> set fis" and rt: "poly (map_poly ?cr fi) x = 0" by auto
    from bnd[OF mem exI[of _ x], OF conjI[OF rt x]]
    show "ox \<le> d" unfolding Suc .
  qed auto
next
  let ?L = "{x. poly (char_poly A) x = 0 \<and> x > 1}"
  fix x :: real
  assume rt: "poly (char_poly A) x = 0"
  have "finite ?L"
    by (rule finite_subset[OF _ poly_roots_finite[of "char_poly A"]],
      insert degree_monic_char_poly[OF A], auto)
  with ev_le_1 have "?L = {}" by simp
  with rt show "x \<le> 1" by auto
qed

text \<open>Note that the only remaining problem in applying 
  @{thm perron_frobenius_spectral_radius_yun} is to check the
  condition @{term "\<exists> x :: complex. poly (map_poly of_real f\<^sub>i) x = 0 \<and> norm x = 1"}.
  Here, there are at least three possibilities.
  First, one can just ignore this precondition and weaken the statement.
  Second, one can apply Sturm's theorem to determine whether all roots are real.
  This can be done by comparing the number of distinct real roots with the degree of @{term f\<^sub>i},
    since @{term f\<^sub>i} is square-free. If all roots are real, then one can decide the criterion
    by checking the only two possible real roots with norm equal to 1, namely 1 and -1.
    If on the other hand there are complex roots, then we loose precision at this point.
  Third, one uses a factorization algorithm (e.g., via complex algebraic numbers) to
  precisely determine the complex roots and decide the condition.

  The second approach is illustrated in the following theorem. Note that all preconditions --
  including the ones from the context --
  can easily be checked with the help of Sturm's method.
  This method is used as a fast approximative technique in CeTA \cite{CeTA}. Only if the desired degree
  cannot be ensured by this method, the more costly complex algebraic number based 
  factorization is applied.\<close>

lemma perron_frobenius_spectral_radius_yun_real_roots: 
  assumes bnd: "\<And> f\<^sub>i i. (f\<^sub>i,i) \<in> set fis 
    \<Longrightarrow> card { x. poly f\<^sub>i x = 0} \<noteq> degree f\<^sub>i \<or> poly f\<^sub>i 1 = 0 \<or> poly f\<^sub>i (-1) = 0 
    \<Longrightarrow> Suc i \<le> d"
  shows "\<exists>c1 c2. \<forall>k a. a \<in> elements_mat (A ^\<^sub>m k) \<longrightarrow> abs a \<le> (c1 + c2 * real k ^ (d - 1))"
proof (rule perron_frobenius_spectral_radius_yun)
  fix fi i
  let ?cr = complex_of_real
  let ?cp = "map_poly ?cr"
  assume fi: "(fi, i) \<in> set fis"
    and "\<exists> x. poly (map_poly ?cr fi) x = 0 \<and> norm x = 1"
  then obtain x where rt: "poly (?cp fi) x = 0" and x: "norm x = 1" by auto
  show "Suc i \<le> d"
  proof (rule bnd[OF fi])
    consider (c) "x \<notin> \<real>" | (1) "x = 1" | (m1) "x = -1" | (r) "x \<in> \<real>" "x \<notin> {1, -1}"
      by (cases "x \<in> \<real>"; auto)
    thus "card {x. poly fi x = 0} \<noteq> degree fi \<or> poly fi 1 = 0 \<or> poly fi (- 1) = 0"
    proof (cases)
      case 1
      from rt have "poly fi 1 = 0" 
        unfolding 1 by simp
      thus ?thesis by simp
    next
      case m1
      have id: "-1 = ?cr (-1)" by simp
      from rt have "poly fi (-1) = 0"
        unfolding m1 id of_real_hom.hom_zero[where 'a=complex,symmetric] of_real_hom.poly_map_poly by simp
      thus ?thesis by simp
    next
      case r
      then obtain y where xy: "x = of_real y" unfolding Reals_def by auto
      from r(2)[unfolded xy] have y: "y \<notin> {1,-1}" by auto
      from x[unfolded xy] have "abs y = 1" by auto
      with y have False by auto
      thus ?thesis ..
    next
      case c
      from yun_factorization(2)[OF yun] fi have "monic fi" by auto
      hence fi: "?cp fi \<noteq> 0" by auto
      hence fin: "finite {x. poly (?cp fi) x = 0}" by (rule poly_roots_finite)
      have "?cr ` {x. poly (?cp fi) (?cr x) = 0} \<subset> {x. poly (?cp fi) x = 0}" (is "?l \<subset> ?r")
      proof (rule, force)
        have "x \<in> ?r" using rt by auto
        moreover have "x \<notin> ?l" using c unfolding Reals_def by auto
        ultimately show "?l \<noteq> ?r" by blast
      qed
      from psubset_card_mono[OF fin this] have "card ?l < card ?r" .
      also have "\<dots> \<le> degree (?cp fi)" by (rule poly_roots_degree[OF fi])
      also have "\<dots> = degree fi" by simp
      also have "?l = ?cr ` {x. poly fi x = 0}" by auto
      also have "card \<dots> = card {x. poly fi x = 0}"
        by (rule card_image, auto simp: inj_on_def)
      finally have "card {x. poly fi x = 0} \<noteq> degree fi" by simp
      thus ?thesis by auto
    qed
  qed
qed 

end

thm perron_frobenius_spectral_radius_yun_real_roots
end
