(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Characteristic Polynomial\<close>

text \<open>We define eigenvalues, eigenvectors, and the characteristic polynomial. We further prove
  that the eigenvalues are exactly the roots of the characteristic polynomial.
  Finally, we apply the fundamental theorem of algebra to show that the characteristic polynomial
  of a complex matrix can always be represented as product of linear factors $x - a$.\<close>
 
theory Char_Poly
imports 
  Polynomial_Factorization.Fundamental_Theorem_Algebra_Factorized
  Polynomial_Interpolation.Missing_Polynomial
  Polynomial_Interpolation.Ring_Hom_Poly
  Determinant
  Complex_Main
begin

definition eigenvector :: "'a :: comm_ring_1 mat \<Rightarrow> 'a vec \<Rightarrow> 'a \<Rightarrow> bool" where
  "eigenvector A v k = (v \<in> carrier_vec (dim_row A) \<and> v \<noteq> 0\<^sub>v (dim_row A) \<and> A *\<^sub>v v = k \<cdot>\<^sub>v v)"
  
lemma eigenvector_pow: assumes A: "A \<in> carrier_mat n n"
  and ev: "eigenvector A v (k :: 'a :: comm_ring_1)"
  shows "A ^\<^sub>m i *\<^sub>v v = k^i \<cdot>\<^sub>v v" 
proof -
  let ?G = "monoid_vec TYPE ('a) n"
  from A have dim: "dim_row A = n" by auto
  from ev[unfolded eigenvector_def dim]
  have v: "v \<in> carrier_vec n" and Av: "A *\<^sub>v v = k \<cdot>\<^sub>v v" by auto
  interpret v: comm_group ?G by (rule comm_group_vec)
  show ?thesis
  proof (induct i)
    case 0
    show ?case using v dim by simp
  next
    case (Suc i)
    define P where "P = A ^\<^sub>m i"
    have P: "P \<in> carrier_mat n n" using A unfolding P_def by simp
    have "A ^\<^sub>m Suc i = P * A" unfolding P_def by simp
    also have "\<dots> *\<^sub>v v = P *\<^sub>v (A *\<^sub>v v)" using P A v by simp
    also have "A *\<^sub>v v = k \<cdot>\<^sub>v v" by (rule Av)
    also have "P *\<^sub>v (k \<cdot>\<^sub>v v) = k \<cdot>\<^sub>v (P *\<^sub>v v)" 
      by (rule eq_vecI, insert v P, auto)
    also have "(P *\<^sub>v v) = (k ^ i) \<cdot>\<^sub>v v" unfolding P_def by (rule Suc)
    also have "k \<cdot>\<^sub>v ((k ^ i) \<cdot>\<^sub>v v) = (k * k ^ i) \<cdot>\<^sub>v v"
      by (rule eq_vecI, insert v, auto)
    also have "k * k ^ i = k ^ (Suc i)" by auto
    finally show ?case .
  qed
qed
    


definition eigenvalue :: "'a :: comm_ring_1 mat \<Rightarrow> 'a \<Rightarrow> bool" where
  "eigenvalue A k = (\<exists> v. eigenvector A v k)"


definition char_matrix :: "'a :: field mat \<Rightarrow> 'a \<Rightarrow> 'a mat" where
  "char_matrix A e = A + ((-e) \<cdot>\<^sub>m (1\<^sub>m (dim_row A)))"

lemma char_matrix_closed[simp]: "A \<in> carrier_mat n n \<Longrightarrow> char_matrix A e \<in> carrier_mat n n"
  unfolding char_matrix_def by auto

lemma eigenvector_char_matrix: assumes A: "(A :: 'a :: field mat) \<in> carrier_mat n n" 
  shows "eigenvector A v e = (v \<in> carrier_vec n \<and> v \<noteq> 0\<^sub>v n \<and> char_matrix A e *\<^sub>v v = 0\<^sub>v n)"
proof -
  from A have dim: "dim_row A = n" "dim_col A = n" by auto
  {
    assume v: "v \<in> carrier_vec n"
    hence dimv: "dim_vec v = n" by auto
    have "(A *\<^sub>v v = e \<cdot>\<^sub>v v) = (A *\<^sub>v v + (-e) \<cdot>\<^sub>v v = 0\<^sub>v n)" (is "?id1 = ?id2")
    proof
      assume ?id1
      from arg_cong[OF this, of "\<lambda> w. w + (-e) \<cdot>\<^sub>v v"]
      show ?id2 using A v by auto
    next
      assume ?id2
      have "A *\<^sub>v v + - e \<cdot>\<^sub>v v + e \<cdot>\<^sub>v v = A *\<^sub>v v" using A v by auto
      from arg_cong[OF \<open>?id2\<close>, of "\<lambda> w. w + e \<cdot>\<^sub>v v", unfolded this]
      show ?id1 using A v by simp
    qed
    also have "(A *\<^sub>v v + (-e) \<cdot>\<^sub>v v) = char_matrix A e *\<^sub>v v" unfolding char_matrix_def
      by (rule eq_vecI, insert v A dim, auto simp: add_scalar_prod_distrib[of _ n])
    finally have "(A *\<^sub>v v = e \<cdot>\<^sub>v v) = (char_matrix A e *\<^sub>v v = 0\<^sub>v n)" .
  }
  thus ?thesis unfolding eigenvector_def dim by blast
qed

lemma eigenvalue_char_matrix: assumes A: "(A :: 'a :: field mat) \<in> carrier_mat n n" 
  shows "eigenvalue A e = (\<exists> v. v \<in> carrier_vec n \<and> v \<noteq> 0\<^sub>v n \<and> char_matrix A e *\<^sub>v v = 0\<^sub>v n)"
  unfolding eigenvalue_def eigenvector_char_matrix[OF A] .. 

definition find_eigenvector :: "'a::field mat \<Rightarrow> 'a \<Rightarrow> 'a vec" where
  "find_eigenvector A e = 
    find_base_vector (fst (gauss_jordan (char_matrix A e) (0\<^sub>m (dim_row A) 0)))"

lemma find_eigenvector: assumes A: "A \<in> carrier_mat n n"
  and ev: "eigenvalue A e"
  shows "eigenvector A (find_eigenvector A e) e"
proof -
  define B where "B = char_matrix A e"
  from ev[unfolded eigenvalue_char_matrix[OF A]]  obtain v where
    v: "v \<in> carrier_vec n" "v \<noteq> 0\<^sub>v n" and Bv: "B *\<^sub>v v = 0\<^sub>v n" unfolding B_def by auto
  have B: "B \<in> carrier_mat n n" using A unfolding B_def by simp
  let ?z = "0\<^sub>m (dim_row A) 0"
  obtain C D where gauss: "gauss_jordan B ?z = (C,D)" by force
  define w where "w = find_base_vector C"
  have res: "find_eigenvector A e = w" unfolding w_def find_eigenvector_def Let_def gauss B_def[symmetric]
    by simp
  have "?z \<in> carrier_mat n 0" using A by auto
  note gauss_0 = gauss_jordan[OF B this gauss] 
  hence C: "C \<in> carrier_mat n n" by auto
  from gauss_0(1)[OF v(1)] Bv have Cv: "C *\<^sub>v v = 0\<^sub>v n" by auto
  {
    assume C: "C = 1\<^sub>m n"
    have False using id Cv v unfolding C by auto
  }
  hence C1: "C \<noteq> 1\<^sub>m n" by auto
  from find_base_vector_not_1[OF gauss_jordan_row_echelon[OF B gauss] C C1]
  have w: "w \<in> carrier_vec n" "w \<noteq> 0\<^sub>v n" and id: "C *\<^sub>v w = 0\<^sub>v n" unfolding w_def by auto
  from gauss_0(1)[OF w(1)] id have Bw: "B *\<^sub>v w = 0\<^sub>v n" by simp
  from w Bw have "eigenvector A w e" 
    unfolding eigenvector_char_matrix[OF A] B_def by auto
  thus ?thesis unfolding res .
qed

lemma eigenvalue_imp_nonzero_dim: assumes "A \<in> carrier_mat n n"
  and "eigenvalue A ev"
  shows "n > 0"
proof (cases n)
  case 0
  from assms obtain v where "eigenvector A v ev" unfolding eigenvalue_def by auto
  from this[unfolded eigenvector_def] assms 0 
  have "v \<in> carrier_vec 0" "v \<noteq> 0\<^sub>v 0" by auto
  hence False by auto
  thus ?thesis by auto
qed simp
  
lemma eigenvalue_det: assumes A: "(A :: 'a :: field mat) \<in> carrier_mat n n" shows
  "eigenvalue A e = (det (char_matrix A e) = 0)"
proof -
  from A have cA: "char_matrix A e \<in> carrier_mat n n" by auto
  show ?thesis
    unfolding eigenvalue_char_matrix[OF A]
    unfolding id det_0_negate[OF cA] det_0_iff_vec_prod_zero[OF cA]
      eigenvalue_def by auto
qed

definition char_poly_matrix :: "'a :: comm_ring_1 mat \<Rightarrow> 'a poly mat" where
  "char_poly_matrix A = (([:0,1:] \<cdot>\<^sub>m 1\<^sub>m (dim_row A)) + map_mat (\<lambda> a. [: - a :]) A)"    

lemma char_poly_matrix_closed[simp]: "A \<in> carrier_mat n n \<Longrightarrow> char_poly_matrix A \<in> carrier_mat n n"
  unfolding char_poly_matrix_def by auto    

definition char_poly :: "'a :: comm_ring_1 mat \<Rightarrow> 'a poly" where
  "char_poly A = (det (char_poly_matrix A))"    

lemmas char_poly_defs = char_poly_def char_poly_matrix_def

lemma (in comm_ring_hom) char_poly_matrix_hom: assumes A: "A \<in> carrier_mat n n"
  shows "char_poly_matrix (mat\<^sub>h A) = map_mat (map_poly hom) (char_poly_matrix A)"
  unfolding char_poly_defs
  by (rule eq_matI, insert A, auto simp: smult_mat_def hom_distribs)

lemma (in comm_ring_hom) char_poly_hom: assumes A: "A \<in> carrier_mat n n"
  shows "char_poly (map_mat hom A) = map_poly hom (char_poly A)"
proof -
  interpret map_poly_hom: map_poly_comm_ring_hom hom..
  show ?thesis
    unfolding char_poly_def map_poly_hom.hom_det[symmetric] char_poly_matrix_hom[OF A] ..
qed

context inj_comm_ring_hom
begin

lemma eigenvector_hom: assumes A: "A \<in> carrier_mat n n"
  and ev: "eigenvector A v ev"
  shows "eigenvector (mat\<^sub>h A) (vec\<^sub>h v) (hom ev)"
proof -
  let ?A = "mat\<^sub>h A" 
  let ?v = "vec\<^sub>h v"
  let ?ev = "hom ev"
  from ev[unfolded eigenvector_def] A
  have v: "v \<in> carrier_vec n" "v \<noteq> 0\<^sub>v n" "A *\<^sub>v v = ev \<cdot>\<^sub>v v" by auto
  from v(1) have v1: "?v \<in> carrier_vec n" by simp
  from v(1-2) obtain i where "i < n" and "v $ i \<noteq> 0" by force
  with v(1) have "?v $ i \<noteq> 0" by auto
  hence v2: "?v \<noteq> 0\<^sub>v n" using \<open>i < n\<close> v(1) by force
  from arg_cong[OF v(3), of "vec\<^sub>h", unfolded mult_mat_vec_hom[OF A v(1)] vec_hom_smult]
  have v3: "?A *\<^sub>v ?v = ?ev \<cdot>\<^sub>v ?v" .
  from v1 v2 v3
  show ?thesis unfolding eigenvector_def using A by auto
qed

lemma eigenvalue_hom: assumes A: "A \<in> carrier_mat n n"
  and ev: "eigenvalue A ev"
  shows "eigenvalue (mat\<^sub>h A) (hom ev)"
  using eigenvector_hom[OF A, of _ ev] ev
  unfolding eigenvalue_def by auto

lemma eigenvector_hom_rev: assumes A: "A \<in> carrier_mat n n"
  and ev: "eigenvector (mat\<^sub>h A) (vec\<^sub>h v) (hom ev)"
  shows "eigenvector A v ev"
proof -
  let ?A = "mat\<^sub>h A" 
  let ?v = "vec\<^sub>h v"
  let ?ev = "hom ev"
  from ev[unfolded eigenvector_def] A
  have v: "v \<in> carrier_vec n" "?v \<noteq> 0\<^sub>v n" "?A *\<^sub>v ?v = ?ev \<cdot>\<^sub>v ?v" by auto
  from v(1-2) obtain i where "i < n" and "v $ i \<noteq> 0" by force
  with v(1) have "v $ i \<noteq> 0" by auto
  hence v2: "v \<noteq> 0\<^sub>v n" using \<open>i < n\<close> v(1) by force
  from vec_hom_inj[OF v(3)[folded mult_mat_vec_hom[OF A v(1)] vec_hom_smult]]
  have v3: "A *\<^sub>v v = ev \<cdot>\<^sub>v v" .
  from v(1) v2 v3
  show ?thesis unfolding eigenvector_def using A by auto
qed

end


lemma poly_det_cong: assumes A: "A \<in> carrier_mat n n"
  and B: "B \<in> carrier_mat n n"
  and poly: "\<And> i j. i < n \<Longrightarrow> j < n \<Longrightarrow> poly (B $$ (i,j)) k = A $$ (i,j)"
  shows "poly (det B) k = det A" 
proof -
  show ?thesis
  unfolding det_def'[OF A] det_def'[OF B] poly_sum poly_mult poly_prod
  proof (rule sum.cong[OF refl])
    fix x
    assume x: "x \<in> {p. p permutes {0..<n}}"
    let ?l = "\<Prod>ka = 0..<n. poly (B $$ (ka, x ka)) k"
    let ?r = "\<Prod>i = 0..<n. A $$ (i, x i)"
    have id: "?l = ?r"
      by (rule prod.cong[OF refl poly], insert x, auto)
    show "poly (signof x) k * ?l = signof x * ?r" unfolding id signof_def by auto
  qed
qed

lemma char_poly_matrix: assumes A: "(A :: 'a :: field mat) \<in> carrier_mat n n"
  shows "poly (char_poly A) k = det (- (char_matrix A k))"  unfolding char_poly_def
  by (rule poly_det_cong[of _ n], insert A, auto simp: char_poly_matrix_def char_matrix_def)

lemma eigenvalue_root_char_poly: assumes A: "(A :: 'a :: field mat) \<in> carrier_mat n n"
  shows "eigenvalue A k \<longleftrightarrow> poly (char_poly A) k = 0" 
  unfolding eigenvalue_det[OF A] char_poly_matrix[OF A] 
  by (subst det_0_negate[of _ n], insert A, auto)

context
  fixes A :: "'a :: comm_ring_1 mat" and n :: nat
  assumes A: "A \<in> carrier_mat n n"
  and ut: "upper_triangular A"
begin
lemma char_poly_matrix_upper_triangular: "upper_triangular (char_poly_matrix A)"
  using A ut unfolding upper_triangular_def char_poly_matrix_def by auto 

lemma char_poly_upper_triangular: 
  "char_poly A = (\<Prod> a \<leftarrow> diag_mat A. [:- a, 1:])"
proof -
  from A have cA: "char_poly_matrix A \<in> carrier_mat n n" by simp
  show ?thesis
    unfolding char_poly_def det_upper_triangular [OF char_poly_matrix_upper_triangular cA]
    by (rule arg_cong[where f = prod_list], unfold list_eq_iff_nth_eq, insert cA A, auto simp: diag_mat_def
      char_poly_matrix_def)
qed
end

lemma map_poly_mult: assumes A: "A \<in> carrier_mat nr n"
  and B: "B \<in> carrier_mat n nc"
  shows 
    "map_mat (\<lambda> a. [: a :]) (A * B) = map_mat (\<lambda> a. [: a :]) A * map_mat (\<lambda> a. [: a :]) B" (is "?id")
    "map_mat (\<lambda> a. [: a :] * p) (A * B) = map_mat (\<lambda> a. [: a :] * p) A * map_mat (\<lambda> a. [: a :]) B" (is "?left")
    "map_mat (\<lambda> a. [: a :] * p) (A * B) = map_mat (\<lambda> a. [: a :]) A * map_mat (\<lambda> a. [: a :] * p) B" (is "?right")
proof -
  from A B have dim: "dim_row A = nr" "dim_col A = n" "dim_row B = n" "dim_col B = nc" by auto
  {
    fix i j
    have "i < nr \<Longrightarrow> j < nc \<Longrightarrow> 
      row (map_mat (\<lambda>a. [:a:]) A) i \<bullet> col (map_mat (\<lambda>a. [:a:]) B) j = [:(row A i \<bullet> col B j):]"
      unfolding scalar_prod_def
      by (auto simp: dim ac_simps, induct n, auto)  
  } note id = this 
  {
    fix i j
    have "i < nr \<Longrightarrow> j < nc \<Longrightarrow> 
      [:(row A i \<bullet> col B j):] * p = row (map_mat (\<lambda> a. [: a :] * p) A) i \<bullet> col (map_mat (\<lambda>a. [:a:]) B) j"
      unfolding scalar_prod_def
      by (auto simp: dim ac_simps smult_sum) 
  } note left = this 
  {
    fix i j
    have "i < nr \<Longrightarrow> j < nc \<Longrightarrow> 
      [:(row A i \<bullet> col B j):] * p = row (map_mat (\<lambda> a. [: a :]) A) i \<bullet> col (map_mat (\<lambda>a. [:a:] * p) B) j"
      unfolding scalar_prod_def
      by (auto simp: dim ac_simps smult_sum) 
  } note right = this 
  show ?id
    by (rule eq_matI, insert id, auto simp: dim)
  show ?left
    by (rule eq_matI, insert left, auto simp: dim)
  show ?right
    by (rule eq_matI, insert right, auto simp: dim)
qed

lemma char_poly_similar: assumes "similar_mat A (B :: 'a :: comm_ring_1 mat)"
  shows "char_poly A = char_poly B"
proof -
  from similar_matD[OF assms] obtain n P Q where
  carr: "{A, B, P, Q} \<subseteq> carrier_mat n n" (is "_ \<subseteq> ?C")
  and PQ: "P * Q = 1\<^sub>m n" 
  and AB: "A = P * B * Q" by auto
  hence A: "A \<in> ?C" and B: "B \<in> ?C" and P: "P \<in> ?C" and Q: "Q \<in> ?C" by auto
  let ?m = "\<lambda> a. [: -a :]"
  let ?P = "map_mat (\<lambda> a. [: a :]) P"
  let ?Q = "map_mat (\<lambda> a. [: a :]) Q"
  let ?B = "map_mat ?m B"
  let ?I = "map_mat (\<lambda> a. [: a :]) (1\<^sub>m n)"
  let ?XI = "[:0, 1:] \<cdot>\<^sub>m 1\<^sub>m n"
  from A B have dim: "dim_row A = n" "dim_row B = n" by auto
  have cong: "\<And> x y z. x = y \<Longrightarrow> x * z = y * z" by auto
  have id: "?m = (\<lambda> a :: 'a. [: a :] * [: -1 :])" by (intro ext, auto)
  have "char_poly A = det (?XI + map_mat (\<lambda>a. [:- a:]) (P * B * Q))" unfolding 
    char_poly_defs dim 
    by (simp add: AB)
  also have "?XI = ?P * ?XI * ?Q" (is "_ = ?left")
  proof -
    have "?P * ?XI = [:0, 1:] \<cdot>\<^sub>m (?P * 1\<^sub>m n)" 
      by (rule mult_smult_distrib[of _ n n _ n], insert P, auto)
    also have "?P * 1\<^sub>m n = ?P" using P by simp
    also have "([: 0, 1:] \<cdot>\<^sub>m ?P) * ?Q = [: 0, 1:] \<cdot>\<^sub>m (?P * ?Q)"
      by (rule mult_smult_assoc_mat, insert P Q, auto)
    also have "?P * ?Q = ?I" unfolding PQ[symmetric]
      by (rule map_poly_mult[symmetric, OF P Q])
    also have "[: 0, 1:] \<cdot>\<^sub>m ?I = ?XI"
      by rule auto
    finally show ?thesis ..
  qed
  also have "map_mat ?m (P * B * Q) = ?P * ?B * ?Q" (is "_ = ?right")
    unfolding id
    by (subst map_poly_mult[OF mult_carrier_mat[OF P B] Q],
      subst map_poly_mult(3)[OF P B], simp)
  also have "?left + ?right = (?P * ?XI + ?P * ?B) * ?Q"
    by (rule add_mult_distrib_mat[symmetric, of _ n n], insert B P Q, auto)
  also have "?P * ?XI + ?P * ?B = ?P * (?XI + ?B)"
    by (rule mult_add_distrib_mat[symmetric, of _ n n], insert B P Q, auto)
  also have "det (?P * (?XI + ?B) * ?Q) = det ?P * det (?XI + ?B) * det ?Q"
    by (rule trans[OF det_mult[of _ n] cong[OF det_mult]], insert P Q B, auto)
  also have "\<dots> = (det ?P * det ?Q) * det (?XI + ?B)" by (simp add: ac_simps)
  also have "det (?XI + ?B) = char_poly B" unfolding char_poly_defs dim by simp
  also have "det ?P * det ?Q = det (?P * ?Q)"
    by (rule det_mult[symmetric], insert P Q, auto)
  also have "?P * ?Q = ?I" unfolding PQ[symmetric]
    by (rule map_poly_mult[symmetric, OF P Q])
  also have "det \<dots> = prod_list (diag_mat ?I)"
    by (rule det_upper_triangular[of _ n], auto)
  also have "\<dots> = 1" unfolding prod_list_diag_prod
    by (rule prod.neutral) simp
  finally show ?thesis by simp
qed

lemma degree_signof_mult[simp]: "degree (signof p * q) = degree q"
  by (cases "sign p = 1", auto simp: signof_def)

lemma degree_monic_char_poly: assumes A: "A \<in> carrier_mat n n"
  shows "degree (char_poly A) = n \<and> coeff (char_poly A) n = 1"
proof -
  from A have A': "[:0, 1:] \<cdot>\<^sub>m 1\<^sub>m (dim_row A) + map_mat (\<lambda>a. [:- a:]) A \<in> carrier_mat n n" by auto
  from A have dA: "dim_row A = n" by simp
  show ?thesis
    unfolding char_poly_defs det_def'[OF A']
  proof (rule degree_lcoeff_sum[of _ id], auto simp: finite_permutations permutes_id dA)
    have both: "degree (\<Prod>i = 0..<n. ([:0, 1:] \<cdot>\<^sub>m 1\<^sub>m n + map_mat (\<lambda>a. [:- a:]) A) $$ (i, i)) = n \<and>
      coeff (\<Prod>i = 0..<n. ([:0, 1:] \<cdot>\<^sub>m 1\<^sub>m n + map_mat (\<lambda>a. [:- a:]) A) $$ (i, i)) n = 1"
      by (rule degree_prod_monic, insert A, auto)
    from both show "degree (\<Prod>i = 0..<n. ([:0, 1:] \<cdot>\<^sub>m 1\<^sub>m n + map_mat (\<lambda>a. [:- a:]) A) $$ (i, i)) = n" ..
    from both show "coeff (\<Prod>i = 0..<n. ([:0, 1:] \<cdot>\<^sub>m 1\<^sub>m n + map_mat (\<lambda>a. [:- a:]) A) $$ (i, i)) n = 1" ..
  next
    fix p
    assume p: "p permutes {0..<n}"
      and "p \<noteq> id"
    then obtain i where i: "i < n" and pi: "p i \<noteq> i"
      by (metis atLeastLessThan_iff order_refl permutes_natset_le)
    show "degree (\<Prod>i = 0..<n. ([:0, 1:] \<cdot>\<^sub>m 1\<^sub>m n + map_mat (\<lambda>a. [:- a:]) A) $$ (i, p i)) < n"
      by (rule degree_prod_sum_lt_n[OF _ i], insert p i pi A, auto)
  qed
qed

lemma char_poly_factorized: fixes A :: "complex mat"
  assumes A: "A \<in> carrier_mat n n"
  shows "\<exists> as. char_poly A = (\<Prod> a \<leftarrow> as. [:- a, 1:]) \<and> length as = n"
proof -
  let ?p = "char_poly A"
  from fundamental_theorem_algebra_factorized[of ?p] obtain as
  where "Polynomial.smult (coeff ?p (degree ?p)) (\<Prod>a\<leftarrow>as. [:- a, 1:]) = ?p" by blast
  also have "coeff ?p (degree ?p) = 1" using degree_monic_char_poly[OF A] by simp
  finally have cA: "?p = (\<Prod>a\<leftarrow>as. [:- a, 1:])" by simp
  from degree_monic_char_poly[OF A] have "degree ?p = n" ..
  with degree_linear_factors[of uminus as, folded cA] have "length as = n" by auto
  with cA show ?thesis by blast
qed

lemma char_poly_four_block_zeros_col: assumes A1: "A1 \<in> carrier_mat 1 1"
  and A2: "A2 \<in> carrier_mat 1 n" and A3: "A3 \<in> carrier_mat n n"
  shows "char_poly (four_block_mat A1 A2 (0\<^sub>m n 1) A3) = char_poly A1 * char_poly A3" 
    (is "char_poly ?A = ?cp1 * ?cp3")
proof -
  let ?cm = "\<lambda> A. [:0, 1:] \<cdot>\<^sub>m 1\<^sub>m (dim_row A) +
         map_mat (\<lambda>a. [:- a:]) A"
  let ?B2 = "map_mat (\<lambda>a. [:- a:]) A2"
  have "char_poly ?A = det (?cm ?A)"
    unfolding char_poly_defs using A1 A3 by simp
  also have "?cm ?A = four_block_mat (?cm A1) ?B2 (0\<^sub>m n 1) (?cm A3)"
    by (rule eq_matI, insert A1 A2 A3, auto simp: one_poly_def)
  also have "det \<dots> = det (?cm A1) * det (?cm A3)"
    by (rule det_four_block_mat_lower_left_zero_col[OF _ _ refl], insert A1 A2 A3, auto)
  also have "\<dots> = ?cp1 * ?cp3" unfolding char_poly_defs ..
  finally show ?thesis .
qed

lemma char_poly_transpose_mat[simp]: assumes A: "A \<in> carrier_mat n n"
  shows "char_poly (transpose_mat A) = char_poly A"
proof -
  let ?A = "[:0, 1:] \<cdot>\<^sub>m 1\<^sub>m (dim_row A) + map_mat (\<lambda>a. [:- a:]) A"
  have A': "?A \<in> carrier_mat n n" using A by auto
  show ?thesis unfolding char_poly_defs
    by (subst det_transpose[symmetric, OF A'], rule arg_cong[of _ _ det],
    insert A, auto)
qed

lemma pderiv_char_poly: fixes A :: "'a :: idom mat" 
  assumes A: "A \<in> carrier_mat n n" 
  shows "pderiv (char_poly A) = (\<Sum>i < n. char_poly (mat_delete A i i))"
proof -
  let ?det = Determinant.det
  let ?m = "map_mat (\<lambda>a. [:- a:])" 
  let ?lam = "[:0, 1:] \<cdot>\<^sub>m 1\<^sub>m n :: 'a poly mat" 
  from A have id: "dim_row A = n" by auto  

  define mA where "mA = ?m A"
  define lam where "lam = ?lam" 
  let ?sum = "lam + mA" 
  define Sum where "Sum = ?sum" 
  have mA: "mA \<in> carrier_mat n n" and 
    lam: "lam \<in> carrier_mat n n" and
    Sum: "Sum \<in> carrier_mat n n" 
    using A unfolding mA_def Sum_def lam_def by auto
  let ?P = "{p. p permutes {0..<n}}" 
  let ?e = "\<lambda> p. (\<Prod>i = 0..<n. Sum $$ (i, p i))" 
  let ?f = "\<lambda> p a. signof p * (\<Prod>i\<in>{0..<n} - {a}. Sum $$ (i, p i)) * pderiv (Sum $$ (a, p a))" 
  let ?g = "\<lambda> p a. signof p * (\<Prod>i\<in>{0..<n} - {a}. Sum $$ (i, p i))" 
  define f where "f = ?f" 
  define g where "g = ?g" 
  {
    fix p
    assume p: "p permutes {0 ..< n}" 
    have "pderiv (signof p :: 'a poly) = 0" unfolding signof_def by (simp add: pderiv_minus) 
    hence "pderiv (signof p * ?e p) = signof p * pderiv (\<Prod>i = 0..<n. Sum $$ (i, p i))" 
      unfolding pderiv_mult by auto
    also have "signof p * pderiv (\<Prod>i = 0..<n. Sum $$ (i, p i)) = 
       (\<Sum>a = 0..<n. f p a)" 
      unfolding pderiv_prod sum_distrib_left f_def by (simp add: ac_simps)
    also note calculation
  } note to_f = this
  {
    fix a
    assume a: "a < n" 
    have Psplit: "?P = {p. p permutes {0..<n} \<and> p a = a} \<union> (?P - {p. p a = a})" (is "_ = ?Pa \<union> ?Pz") by auto 
    {
      fix p
      assume p: "p permutes {0 ..< n}" "p a \<noteq> a"
      hence "pderiv (Sum $$ (a, p a)) = 0" unfolding Sum_def lam_def mA_def using a p A by auto
      hence "f p a = 0" unfolding f_def by auto
    } note 0 = this
    {
      fix p
      assume p: "p permutes {0 ..< n}" "p a = a"
      hence "pderiv (Sum $$ (a, p a)) = 1" unfolding Sum_def lam_def mA_def using a p A
        by (auto simp: pderiv_pCons)
      hence "f p a = g p a" unfolding f_def g_def by auto
    } note fg = this
    let ?n = "n - 1" 
    from a have n: "Suc ?n = n" by simp
    let ?B = "[:0, 1:] \<cdot>\<^sub>m 1\<^sub>m ?n + ?m (mat_delete A a a)" 
    have B: "?B \<in> carrier_mat ?n ?n" using A by auto
    have "sum (\<lambda> p. f p a) ?P = sum (\<lambda> p. f p a) ?Pa + sum (\<lambda> p. f p a) ?Pz" 
      by (subst sum.union_disjoint[symmetric], auto simp: finite_permutations Psplit[symmetric])
    also have "\<dots> = sum (\<lambda> p. f p a) ?Pa" 
      by (subst (2) sum.neutral, insert 0, auto)
    also have "\<dots> = sum (\<lambda> p. g p a) ?Pa" 
      by (rule sum.cong, auto simp: fg)
    also have "\<dots> = ?det ?B"
      unfolding det_def'[OF B] 
      unfolding permutation_fix[of a ?n a, unfolded n, OF a a]
      unfolding sum.reindex[OF permutation_insert_inj_on[of a ?n a, unfolded n, OF a a]] o_def
    proof (rule sum.cong[OF refl])
      fix p
      let ?Q = "{p. p permutes {0..<?n}}" 
      assume "p \<in> ?Q"      
      hence p: "p permutes {0 ..< ?n}" by auto
      let ?p = "permutation_insert a a p"
      let ?i = "insert_index a" 
      have sign: "signof ?p = signof p" 
        unfolding signof_permutation_insert[OF p, unfolded n, OF a a] by simp
      show "g (permutation_insert a a p) a = signof p * (\<Prod>i = 0..<?n. ?B $$ (i, p i))" 
        unfolding g_def sign
      proof (rule arg_cong[of _ _ "(*) (signof p)"])
        have "(\<Prod>i\<in>{0..<n} - {a}. Sum $$ (i, ?p i)) = 
           prod (($$) Sum) ((\<lambda>x. (x, ?p x)) ` ({0..<n} - {a}))"
          unfolding prod.reindex[OF inj_on_convol_ident, of _ ?p] o_def ..
        also have "\<dots> = (\<Prod> ii \<in> {(i', ?p i') |i'. i' \<in> {0..<n} - {a}}. Sum $$ ii)" 
          by (rule prod.cong, auto)
        also have "\<dots> = prod (($$) Sum) ((\<lambda> i. (?i i, ?i (p i))) ` {0 ..< ?n})" 
          unfolding Determinant.foo[of a ?n a, unfolded n, OF a a p]
          by (rule arg_cong[of _ _ "prod _"], auto) 
        also have "\<dots> = prod (\<lambda> i. Sum $$ (?i i, ?i (p i))) {0 ..< ?n}"
        proof (subst prod.reindex, unfold o_def)
          show "inj_on (\<lambda>i. (?i i, ?i (p i))) {0..<?n}" using insert_index_inj_on[of a]
            by (auto simp: inj_on_def)
        qed simp
        also have "\<dots> = (\<Prod>i = 0..<?n. ?B $$ (i, p i))" 
        proof (rule prod.cong[OF refl], rename_tac i)
          fix j
          assume "j \<in> {0 ..< ?n}"
          hence j: "j < ?n" by auto
          with p have pj: "p j < ?n" by auto
          from j pj have jj: "?i j < n" "?i (p j) < n" by (auto simp: insert_index_def)
          let ?jj = "(?i j, ?i (p j))" 
          note index_adj = mat_delete_index[of _ ?n, unfolded n, OF _ a a j pj]
          have "Sum $$ ?jj = lam $$ ?jj + mA $$ ?jj" unfolding Sum_def using jj A lam mA by auto
          also have "\<dots> = ?B $$ (j, p j)" 
            unfolding index_adj[OF mA] index_adj[OF lam] using j pj A
            by (simp add: mA_def lam_def mat_delete_def)
          finally show "Sum $$ ?jj = ?B $$ (j, p j)" .
        qed
        finally 
        show "(\<Prod>i\<in>{0..<n} - {a}. Sum $$ (i, ?p i)) = (\<Prod>i = 0..<?n. ?B $$ (i, p i))" .
      qed
    qed
    also have "\<dots> = char_poly (mat_delete A a a)" unfolding char_poly_def char_poly_matrix_def
      using A by simp
    also note calculation
  } note to_char_poly = this
  have "pderiv (char_poly A) = pderiv (?det Sum)" 
    unfolding char_poly_def char_poly_matrix_def id lam_def mA_def Sum_def by auto
  also have "\<dots> = sum (\<lambda> p. pderiv (signof p * ?e p)) ?P" unfolding det_def'[OF Sum]
    pderiv_sum by (rule sum.cong, auto)
  also have "\<dots> = sum (\<lambda> p. (\<Sum>a = 0..<n. f p a)) ?P" 
    by (rule sum.cong[OF refl], subst to_f, auto)
  also have "\<dots> = (\<Sum>a = 0..<n. sum (\<lambda> p. f p a) ?P)" 
    by (rule sum.swap) 
  also have "\<dots> = (\<Sum>a <n. char_poly (mat_delete A a a))" 
    by (rule sum.cong, auto simp: to_char_poly)
  finally show ?thesis .
qed    

lemma char_poly_0_column: fixes A :: "'a :: idom mat" 
  assumes 0: "\<And> j. j < n \<Longrightarrow> A $$ (j,i) = 0" 
  and A: "A \<in> carrier_mat n n" 
  and i: "i < n"
shows "char_poly A = monom 1 1 * char_poly (mat_delete A i i)" 
proof -
  let ?n = "n - 1" 
  let ?A = "mat_delete A i i" 
  let ?sum = "[:0, 1:] \<cdot>\<^sub>m 1\<^sub>m n + map_mat (\<lambda>a. [:- a:]) A" 
  define Sum where "Sum = ?sum" 
  let ?f = "\<lambda> j. Sum $$ (j, i) * cofactor Sum j i" 
  have Sum: "Sum \<in> carrier_mat n n" using A unfolding Sum_def by auto
  from A have id: "dim_row A = n" by auto  
  have "char_poly A = (\<Sum>j<n. ?f j)" 
    unfolding char_poly_def[of A] char_poly_matrix_def 
    using laplace_expansion_column[OF Sum i] unfolding Sum_def using A by simp
  also have "\<dots> = ?f i + sum ?f ({..<n} - {i})" 
    by (rule sum.remove[of _ i], insert i, auto)
  also have "\<dots> = ?f i" 
  proof (subst sum.neutral, intro ballI)
    fix j
    assume "j \<in> {..<n} - {i}" 
    hence j: "j < n" and ji: "j \<noteq> i" by auto
    show "?f j = 0" unfolding Sum_def using ji j i A 0[OF j] by simp
  qed simp
  also have "?f i = [:0, 1:] * (cofactor Sum i i)" 
    unfolding Sum_def using i A 0[OF i] by simp
  also have "cofactor Sum i i = det (mat_delete Sum i i)" 
    unfolding cofactor_def by simp
  also have "\<dots> = char_poly ?A" 
    unfolding char_poly_def char_poly_matrix_def Sum_def
  proof (rule arg_cong[of _ _ det])
    show "mat_delete ?sum i i = [:0, 1:] \<cdot>\<^sub>m 1\<^sub>m (dim_row ?A) + map_mat (\<lambda>a. [:- a:]) ?A"
      using i A by (auto simp: mat_delete_def)
  qed
  also have "[:0, 1:] = (monom 1 1 :: 'a poly)" by (rule x_as_monom)
  finally show ?thesis .
qed

definition mat_erase :: "'a :: zero mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat" where
  "mat_erase A i j = Matrix.mat (dim_row A) (dim_col A) 
     (\<lambda> (i',j'). if i' = i \<or> j' = j then 0 else A $$ (i',j'))"  

lemma mat_erase_carrier[simp]: "(mat_erase A i j) \<in> carrier_mat nr nc \<longleftrightarrow> A \<in> carrier_mat nr nc" 
  unfolding mat_erase_def carrier_mat_def by simp

lemma pderiv_char_poly_mat_erase: fixes A :: "'a :: idom mat" 
  assumes A: "A \<in> carrier_mat n n" 
  shows "monom 1 1 * pderiv (char_poly A) = (\<Sum>i < n. char_poly (mat_erase A i i))"
proof -
  show ?thesis unfolding pderiv_char_poly[OF A] sum_distrib_left
  proof (rule sum.cong[OF refl])
    fix i
    assume "i \<in> {..<n}" 
    hence i: "i < n" by simp
    have mA: "mat_erase A i i \<in> carrier_mat n n" using A by simp
    show "monom 1 1 * char_poly (mat_delete A i i) = char_poly (mat_erase A i i)"
      by (subst char_poly_0_column[OF _ mA i], (insert i A, force simp: mat_erase_def),
      rule arg_cong[of _ _ "\<lambda> x. f * char_poly x" for f],
      auto simp: mat_delete_def mat_erase_def)
  qed
qed
    
end
