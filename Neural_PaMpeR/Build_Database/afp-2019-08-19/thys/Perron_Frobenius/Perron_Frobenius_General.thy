(* Author: Thiemann *)
subsection \<open>Handling Non-Irreducible Matrices as Well\<close>

theory Perron_Frobenius_General
  imports Perron_Frobenius_Irreducible
begin


text \<open>We will need to take sub-matrices and permutations of matrices where the former can best be done
  via JNF-matrices. So, we first need the Perron-Frobenius theorem in the JNF-world. 
  So, we first define irreducibility of a JNF-matrix.\<close>

definition graph_of_mat where
  "graph_of_mat A = (let n = dim_row A; U = {..<n} in
     { ij. A $$ ij \<noteq> 0} \<inter> U \<times> U)" 

definition irreducible_mat where
  "irreducible_mat A = (let n = dim_row A in 
    (\<forall> i j. i < n \<longrightarrow> j < n \<longrightarrow> (i,j) \<in> (graph_of_mat A)^+))" 

definition "nonneg_irreducible_mat A = (nonneg_mat A \<and> irreducible_mat A)"

text \<open>Next, we have to install transfer rules\<close>

context 
  includes lifting_syntax
begin
lemma HMA_irreducible[transfer_rule]: "((HMA_M :: _ \<Rightarrow> _ ^ 'n ^ 'n \<Rightarrow> _) ===> (=)) 
  irreducible_mat fixed_mat.irreducible" 
proof (intro rel_funI, goal_cases)
  case (1 a A)
  interpret fixed_mat A .
  let ?t = "Bij_Nat.to_nat :: 'n \<Rightarrow> nat" 
  let ?f = "Bij_Nat.from_nat :: nat \<Rightarrow> 'n" 
  from 1[unfolded HMA_M_def]
  have a: "a = from_hma\<^sub>m A" (is "_ = ?A") by auto
  let ?n = "CARD('n)" 
  have dim: "dim_row a = ?n" unfolding a by simp
  have id: "{..<?n} = {0..<?n}" by auto
  have Aij: "A $ i $ j = ?A $$ (?t i, ?t j)" for i j
    by (metis (no_types, lifting) to_hma\<^sub>m_def to_hma_from_hma\<^sub>m vec_lambda_beta)
  have graph: "graph_of_mat a = 
    {(?t i,?t j) | i j. A $ i $ j \<noteq> 0}" (is "?G = _") unfolding graph_of_mat_def dim Let_def id range_to_nat[symmetric] 
    unfolding a Aij by auto
  have "irreducible_mat a = (\<forall>i j. i \<in> range ?t \<longrightarrow> j \<in> range ?t \<longrightarrow> (i,j) \<in> ?G^+)" 
    unfolding irreducible_mat_def dim Let_def range_to_nat by auto
  also have "\<dots> = (\<forall> i j. (?t i, ?t j) \<in> ?G^+)" by auto
  also note part1 = calculation
  have G: "?G = map_prod ?t ?t ` G" unfolding graph G_def by auto
  have part2: "(?t i, ?t j) \<in> ?G^+ \<longleftrightarrow> (i,j) \<in> G^+" for i j 
    unfolding G by (rule inj_trancl_image, simp add: inj_on_def)
  show ?case unfolding part1 part2 irreducible_def by auto
qed

lemma HMA_nonneg_irreducible_mat[transfer_rule]: "(HMA_M ===> (=)) nonneg_irreducible_mat perron_frobenius" 
  unfolding perron_frobenius_def pf_nonneg_mat_def perron_frobenius_axioms_def 
    nonneg_irreducible_mat_def
  by transfer_prover
end

text \<open>The main statements of Perron-Frobenius can now be transferred to JNF-matrices\<close>

lemma perron_frobenius_irreducible: fixes A :: "real Matrix.mat" and cA :: "complex Matrix.mat" 
  assumes A: "A \<in> carrier_mat n n" and n: "n \<noteq> 0" and nonneg: "nonneg_mat A" 
    and irr: "irreducible_mat A" 
    and cA: "cA = map_mat of_real A"
    and sr: "sr = Spectral_Radius.spectral_radius cA" 
  shows 
    "eigenvalue A sr"
    "order sr (char_poly A) = 1"
    "0 < sr"
    "eigenvalue cA \<alpha> \<Longrightarrow> cmod \<alpha> \<le> sr"
    "eigenvalue cA \<alpha> \<Longrightarrow> cmod \<alpha> = sr \<Longrightarrow> order \<alpha> (char_poly cA) = 1" 
    "\<exists> k f. k \<noteq> 0 \<and> k \<le> n \<and> char_poly A = (monom 1 k - [:sr ^ k:]) * f \<and>
        (\<forall>x. poly (map_poly complex_of_real f) x = 0 \<longrightarrow> cmod x < sr)" 
proof (atomize (full), goal_cases)
  case 1
  from nonneg irr have irr: "nonneg_irreducible_mat A" unfolding nonneg_irreducible_mat_def by auto
  note main = perron_frobenius.pf_main_connect[untransferred, cancel_card_constraint, OF A irr, 
    folded sr cA] 
  from main(5,6,7)[OF refl refl n]
  have "\<exists> k f. k \<noteq> 0 \<and> k \<le> n \<and> char_poly A = (monom 1 k - [:sr ^ k:]) * f \<and>
        (\<forall>x. poly (map_poly complex_of_real f) x = 0 \<longrightarrow> cmod x < sr)" by blast
  with main(1,3,8)[OF n] main(2)[OF _ n] main(4)[OF _ _ n] show ?case by auto
qed

text \<open>We now need permutations on matrices to show that a matrix if a matrix is not irreducible,
  then it can be turned into a four-block-matrix by a permutation, where the lower left block is 0.\<close>

definition permutation_mat :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> 'a :: semiring_1 mat" where
  "permutation_mat n p = Matrix.mat n n (\<lambda> (i,j). (if i = p j then 1 else 0))" 

no_notation m_inv ("inv\<index> _" [81] 80)

lemma permutation_mat_dim[simp]: "permutation_mat n p \<in> carrier_mat n n" 
  "dim_row (permutation_mat n p) = n"
  "dim_col (permutation_mat n p) = n"
  unfolding permutation_mat_def by auto

lemma permutation_mat_row[simp]: "p permutes {..<n} \<Longrightarrow> i < n \<Longrightarrow>
  Matrix.row (permutation_mat n p) i = unit_vec n (inv p i)"
  unfolding permutation_mat_def unit_vec_def by (intro eq_vecI, auto simp: permutes_inverses)

lemma permutation_mat_col[simp]: "p permutes {..<n} \<Longrightarrow> i < n \<Longrightarrow>
  Matrix.col (permutation_mat n p) i = unit_vec n (p i)"
  unfolding permutation_mat_def unit_vec_def by (intro eq_vecI, auto simp: permutes_inverses)

lemma permutation_mat_left: assumes A: "A \<in> carrier_mat n nc" and p: "p permutes {..<n}" 
  shows "permutation_mat n p * A = Matrix.mat n nc (\<lambda> (i,j). A $$ (inv p i, j))"
proof -
  {
    fix i j
    assume ij: "i < n" "j < nc" 
    from p ij(1) have i: "inv p i < n" by (simp add: permutes_def)
    have "(permutation_mat n p * A) $$ (i,j) = scalar_prod (unit_vec n (inv p i)) (col A j)" 
      by (subst index_mult_mat, insert ij A p, auto)
    also have "\<dots> = A $$ (inv p i, j)"
      by (subst scalar_prod_left_unit, insert A ij i, auto) 
    also note calculation
  }
  thus ?thesis using A
    by (intro eq_matI, auto)
qed

lemma permutation_mat_right: assumes A: "A \<in> carrier_mat nr n" and p: "p permutes {..<n}" 
  shows "A * permutation_mat n p = Matrix.mat nr n (\<lambda> (i,j). A $$ (i, p j))"
proof -
  {
    fix i j
    assume ij: "i < nr" "j < n" 
    from p ij(2) have j: "p j < n" by (simp add: permutes_def)
    have "(A * permutation_mat n p) $$ (i,j) = scalar_prod (Matrix.row A i) (unit_vec n (p j))" 
      by (subst index_mult_mat, insert ij A p, auto)
    also have "\<dots> = A $$ (i, p j)"
      by (subst scalar_prod_right_unit, insert A ij j, auto) 
    also note calculation
  }
  thus ?thesis using A
    by (intro eq_matI, auto)
qed

lemma permutes_lt: "p permutes {..<n} \<Longrightarrow> i < n \<Longrightarrow> p i < n"
  by (meson lessThan_iff permutes_in_image)

lemma permutes_iff: "p permutes {..<n} \<Longrightarrow> i < n \<Longrightarrow> j < n \<Longrightarrow> p i = p j \<longleftrightarrow> i = j" 
  by (metis permutes_inverses(2))

lemma permutation_mat_id_1: assumes p: "p permutes {..<n}" 
  shows "permutation_mat n p * permutation_mat n (inv p) = 1\<^sub>m n" 
  by (subst permutation_mat_left[OF _ p, of _ n], force, unfold permutation_mat_def, rule eq_matI, 
   auto simp: permutes_lt[OF permutes_inv[OF p]] permutes_iff[OF permutes_inv[OF p]])

lemma permutation_mat_id_2: assumes p: "p permutes {..<n}" 
  shows "permutation_mat n (inv p) * permutation_mat n p = 1\<^sub>m n" 
  by (subst permutation_mat_right[OF _ p, of _ n], force, unfold permutation_mat_def, rule eq_matI, 
   insert p, auto simp: permutes_lt[OF p] permutes_inverses)

lemma permutation_mat_both: assumes A: "A \<in> carrier_mat n n" and p: "p permutes {..<n}" 
  shows "permutation_mat n p * Matrix.mat n n (\<lambda> (i,j). A $$ (p i, p j)) * permutation_mat n (inv p) = A" 
  unfolding permutation_mat_left[OF mat_carrier p]
    by (subst permutation_mat_right[OF _ permutes_inv[OF p], of _ n], force, insert A p, 
        auto intro!: eq_matI simp: permutes_inverses permutes_lt[OF permutes_inv[OF p]])

lemma permutation_similar_mat: assumes A: "A \<in> carrier_mat n n" and p: "p permutes {..<n}"
  shows "similar_mat A (Matrix.mat n n (\<lambda> (i,j). A $$ (p i, p j)))" 
  by (rule similar_matI[OF _ permutation_mat_id_1[OF p] permutation_mat_id_2[OF p] 
  permutation_mat_both[symmetric, OF A p]], insert A, auto)

lemma det_four_block_mat_lower_left_zero: fixes A1 :: "'a :: idom mat" 
  assumes A1: "A1 \<in> carrier_mat n n"
  and A2: "A2 \<in> carrier_mat n m" and A30: "A3 = 0\<^sub>m m n"
  and A4: "A4 \<in> carrier_mat m m"  
shows "Determinant.det (four_block_mat A1 A2 A3 A4) = Determinant.det A1 * Determinant.det A4" 
proof -
  let ?det = Determinant.det
  let ?t = "transpose_mat" 
  let ?A = "four_block_mat A1 A2 A3 A4" 
  let ?k = "n + m" 
  have A3: "A3 \<in> carrier_mat m n" unfolding A30 by auto
  have A: "?A \<in> carrier_mat ?k ?k" 
    by (rule four_block_carrier_mat[OF A1 A4])
  have "?det ?A = ?det (?t ?A)" 
    by (rule sym, rule Determinant.det_transpose[OF A])
  also have "?t ?A = four_block_mat (?t A1) (?t A3) (?t A2) (?t A4)" 
    by (rule transpose_four_block_mat[OF A1 A2 A3 A4])
  also have "?det \<dots> = ?det (?t A1) * ?det (?t A4)" 
    by (rule det_four_block_mat_upper_right_zero[of _ n _ m], insert A1 A2 A30 A4, auto)
  also have "?det (?t A1) = ?det A1" 
    by (rule Determinant.det_transpose[OF A1])
  also have "?det (?t A4) = ?det A4" 
    by (rule Determinant.det_transpose[OF A4])
  finally show ?thesis .
qed

lemma char_poly_matrix_four_block_mat: assumes 
      A1: "A1 \<in> carrier_mat n n"
  and A2: "A2 \<in> carrier_mat n m" 
  and A3: "A3 \<in> carrier_mat m n"
  and A4: "A4 \<in> carrier_mat m m"
shows "char_poly_matrix (four_block_mat A1 A2 A3 A4) = 
  four_block_mat (char_poly_matrix A1) (map_mat (\<lambda> x. [:-x:]) A2) 
    (map_mat (\<lambda> x. [:-x:]) A3) (char_poly_matrix A4)" 
proof -
  from A1 A4 
  have dim[simp]: "dim_row A1 = n" "dim_col A1 = n" 
      "dim_row A4 = m" "dim_col A4 = m" by auto
  show ?thesis
    unfolding char_poly_matrix_def four_block_mat_def Let_def dim
    by (rule eq_matI, insert A2 A3, auto)
qed

lemma char_poly_four_block_mat_lower_left_zero: fixes A :: "'a :: idom mat"
  assumes A: "A = four_block_mat B C (0\<^sub>m m n) D"
  and B: "B \<in> carrier_mat n n"
  and C: "C \<in> carrier_mat n m"
  and D: "D \<in> carrier_mat m m"
shows "char_poly A = char_poly B * char_poly D"
  unfolding A char_poly_def
  by (subst char_poly_matrix_four_block_mat[OF B C _ D], force, 
     rule det_four_block_mat_lower_left_zero[of _ n _ m], insert B C D, auto)

lemma elements_mat_permutes: assumes p: "p permutes {..< n}" 
  and A: "A \<in> carrier_mat n n" 
  and B: "B = Matrix.mat n n (\<lambda> (i,j). A $$ (p i, p j))" 
shows "elements_mat A = elements_mat B" 
proof -
  from A B have [simp]: "dim_row A = n" "dim_col A = n" "dim_row B = n" "dim_col B = n" by auto
  {
    fix i j
    assume ij: "i < n" "j < n" 
    let ?p = "inv p" 
    from permutes_lt[OF p] ij have *: "p i < n" "p j < n" by auto
    from permutes_lt[OF permutes_inv[OF p]] ij have **: "?p i < n" "?p j < n" by auto
    have "\<exists> i' j'. B $$ (i,j) = A $$ (i',j') \<and> i' < n \<and> j' < n" 
       "\<exists> i' j'. A $$ (i,j) = B $$ (i',j') \<and> i' < n \<and> j' < n"
      by (rule exI[of _ "p i"], rule exI[of _ "p j"], insert ij *, simp add: B,
      rule exI[of _ "?p i"], rule exI[of _ "?p j"], insert ** p, simp add: B permutes_inverses)
  }
  thus ?thesis unfolding elements_mat by auto
qed

lemma elements_mat_four_block_mat_supseteq: 
  assumes A1: "A1 \<in> carrier_mat n n"
  and A2: "A2 \<in> carrier_mat n m" 
  and A3: "A3 \<in> carrier_mat m n"
  and A4: "A4 \<in> carrier_mat m m"
shows "elements_mat (four_block_mat A1 A2 A3 A4) \<supseteq> 
  (elements_mat A1 \<union> elements_mat A2 \<union> elements_mat A3 \<union> elements_mat A4)" 
proof 
  let ?A = "four_block_mat A1 A2 A3 A4" 
  have A: "?A \<in> carrier_mat (n + m) (n + m)" using A1 A2 A3 A4 by simp
  from A1 A4 
  have dim[simp]: "dim_row A1 = n" "dim_col A1 = n" 
      "dim_row A4 = m" "dim_col A4 = m" by auto
  fix x
  assume x: "x \<in> elements_mat A1 \<union> elements_mat A2 \<union> elements_mat A3 \<union> elements_mat A4" 
  {
    assume "x \<in> elements_mat A1" 
    from this[unfolded elements_mat] A1 obtain i j where x: "x = A1 $$ (i,j)" and 
      ij: "i < n" "j < n" by auto
    have "x = ?A $$ (i,j)" using ij unfolding x four_block_mat_def Let_def by simp
    from elements_matI[OF A _ _ this] ij have "x \<in> elements_mat ?A" by auto
  } 
  moreover
  {
    assume "x \<in> elements_mat A2" 
    from this[unfolded elements_mat] A2 obtain i j where x: "x = A2 $$ (i,j)" and 
      ij: "i < n" "j < m" by auto
    have "x = ?A $$ (i,j + n)" using ij unfolding x four_block_mat_def Let_def by simp
    from elements_matI[OF A _ _ this] ij have "x \<in> elements_mat ?A" by auto
  }
  moreover
  {
    assume "x \<in> elements_mat A3" 
    from this[unfolded elements_mat] A3 obtain i j where x: "x = A3 $$ (i,j)" and 
      ij: "i < m" "j < n" by auto
    have "x = ?A $$ (i+n,j)" using ij unfolding x four_block_mat_def Let_def by simp
    from elements_matI[OF A _ _ this] ij have "x \<in> elements_mat ?A" by auto
  }
  moreover
  {
    assume "x \<in> elements_mat A4" 
    from this[unfolded elements_mat] A4 obtain i j where x: "x = A4 $$ (i,j)" and 
      ij: "i < m" "j < m" by auto
    have "x = ?A $$ (i+n,j + n)" using ij unfolding x four_block_mat_def Let_def by simp
    from elements_matI[OF A _ _ this] ij have "x \<in> elements_mat ?A" by auto
  }
  ultimately show "x \<in> elements_mat ?A" using x by blast
qed
      

lemma non_irreducible_mat_split: 
  fixes A :: "'a :: idom mat" 
  assumes A: "A \<in> carrier_mat n n" 
  and not: "\<not> irreducible_mat A" 
  and n: "n > 1" 
shows "\<exists> n1 n2 B B1 B2 B4. similar_mat A B \<and> elements_mat A = elements_mat B \<and>
       B = four_block_mat B1 B2 (0\<^sub>m n2 n1) B4 \<and>  
       B1 \<in> carrier_mat n1 n1 \<and> B2 \<in> carrier_mat n1 n2 \<and> B4 \<in> carrier_mat n2 n2 \<and>
       0 < n1 \<and> n1 < n \<and> 0 < n2 \<and> n2 < n \<and> n1 + n2 = n"
proof -
  from A have [simp]: "dim_row A = n" by auto
  let ?G = "graph_of_mat A" 
  let ?reachp = "\<lambda> i j. (i,j) \<in> ?G^+" 
  let ?reach = "\<lambda> i j. (i,j) \<in> ?G^*" 
  have "\<exists> i j. i < n \<and> j < n \<and> \<not> ?reach i j" 
  proof (rule ccontr)
    assume "\<not> ?thesis"
    hence reach: "\<And> i j. i < n \<Longrightarrow> j < n \<Longrightarrow> ?reach i j" by auto
    from not[unfolded irreducible_mat_def Let_def]
    obtain i j where i: "i < n" and j: "j < n" and nreach: "\<not> ?reachp i j" by auto
    from reach[OF i j] nreach have ij: "i = j" by (simp add: rtrancl_eq_or_trancl)
    from n j obtain k where k: "k < n" and diff: "j \<noteq> k" by auto
    from reach[OF j k] diff reach[OF k j]
    have "?reachp j j" by (simp add: rtrancl_eq_or_trancl)
    with nreach ij show False by auto
  qed
  then obtain i j where i: "i < n" and j: "j < n" and nreach: "\<not> ?reach i j" by auto
  define I where "I = {k. k < n \<and> ?reach i k}" 
  have iI: "i \<in> I" unfolding I_def using nreach i by auto
  have jI: "j \<notin> I" unfolding I_def using nreach j by auto
  define f where "f = (\<lambda> i. if i \<in> I then 1 else 0 :: nat)" 
  let ?xs = "[0 ..< n]" 
  from mset_eq_permutation[OF mset_sort, of ?xs f] obtain p where p: "p permutes {..< n}" 
    and perm: "permute_list p ?xs = sort_key f ?xs" by auto
  from p have lt[simp]: "i < n \<Longrightarrow> p i < n" for i by (rule permutes_lt)
  let ?p = "inv p" 
  have ip: "?p permutes {..< n}" using permutes_inv[OF p] .
  from ip have ilt[simp]: "i < n \<Longrightarrow> ?p i < n" for i by (rule permutes_lt)
  let ?B = "Matrix.mat n n (\<lambda> (i,j). A $$ (p i, p j))" 
  define B where "B = ?B" 
  from permutation_similar_mat[OF A p] have sim: "similar_mat A B" unfolding B_def .
  let ?ys = "permute_list p ?xs" 
  define ys where "ys = ?ys" 
  have len_ys: "length ys = n" unfolding ys_def by simp
  let ?k = "length (filter (\<lambda> i. f i = 0) ys)" 
  define k where "k = ?k"
  have kn: "k \<le> n" unfolding k_def using len_ys 
    using length_filter_le[of _ ys] by auto
  have ys_p: "i < n \<Longrightarrow> ys ! i = p i" for i unfolding ys_def permute_list_def by simp
  have ys: "ys = map (\<lambda> i. ys ! i) [0 ..< n]" unfolding len_ys[symmetric]
    by (simp add: map_nth) 
  also have "\<dots> = map p [0 ..< n]" 
    by (rule map_cong, insert ys_p, auto)
  also have "[0 ..< n] = [0 ..< k] @ [k ..< n]" using kn
    using le_Suc_ex upt_add_eq_append by blast
  finally have ys: "ys = map p [0 ..< k] @ map p [k ..< n]" by simp    
  {
    fix i
    assume i: "i < n"
    let ?g = "(\<lambda> i. f i = 0)" 
    let ?f = "filter ?g" 
    from i have pi: "p i < n" using p by simp
    have "k = length (?f ys)" by fact    
    also have "?f ys = ?f (map p [0 ..< k]) @ ?f (map p [k ..< n])" unfolding ys by simp
    also note k = calculation
    finally have True by blast
    from perm[symmetric, folded ys_def]
    have "sorted (map f ys)" using sorted_sort_key by metis
    from this[unfolded ys map_append sorted_append set_map]
    have sorted: "\<And> x y. x < k \<Longrightarrow> y \<in> {k..<n} \<Longrightarrow> f (p x) \<le> f (p y)" by auto
    have 0: "\<forall> i < k. f (p i) = 0" 
    proof (rule ccontr)
      assume "\<not> ?thesis" 
      then obtain i where i: "i < k" and zero: "f (p i) \<noteq> 0" by auto
      hence "f (p i) = 1" unfolding f_def by (auto split: if_splits)
      from sorted[OF i, unfolded this] have 1: "j \<in> {k..<n} \<Longrightarrow> f (p j) \<ge> 1" for j by auto
      have le: "j \<in> {k ..< n} \<Longrightarrow> f (p j) = 1" for j using 1[of j] unfolding f_def 
        by (auto split: if_splits)
      also have "?f (map p [k ..< n]) = []" using le by auto
      from k[unfolded this] have "length (?f (map p [0..<k])) = k" by simp 
      from length_filter_less[of "p i" "map p [0 ..< k]" ?g, unfolded this] i zero
      show False by auto
    qed
    hence "?f (map p [0..<k]) = map p [0..<k]" by auto
    from arg_cong[OF k[unfolded this, simplified], of set]
    have 1: "\<And> i. i \<in> {k ..< n} \<Longrightarrow> f (p i) \<noteq> 0" by auto
    have 1: "i < n \<Longrightarrow> \<not> i < k \<Longrightarrow> f (p i) \<noteq> 0" for i using 1[of i] by auto
    have 0: "i < n \<Longrightarrow> (f (p i) = 0) = (i < k)" for i using 1[of i] 0[rule_format, of i] by blast
    have main: "(f i = 0) = (?p i < k)" using 0[of "?p i"] i p 
      by (auto simp: permutes_inverses)
    have "i \<in> I \<longleftrightarrow> f i \<noteq> 0" unfolding f_def by simp
    also have "(f i = 0) \<longleftrightarrow> ?p i < k" using main by auto
    finally have "i \<in> I \<longleftrightarrow> ?p i \<ge> k" by auto
  } note main = this
  from main[OF j] jI
  have k0: "k \<noteq> 0" by auto
  from iI main[OF i] have "?p i \<ge> k" by auto
  with ilt[OF i] have kn: "k < n" by auto
  {
    fix i j 
    assume i: "i < n" and ik: "k \<le> i" and jk: "j < k"
    with kn have j: "j < n" by auto
    have jI: "p j \<notin> I" 
      by (subst main, insert jk j p, auto simp: permutes_inverses)
    have iI: "p i \<in> I" 
      by (subst main, insert i ik p, auto simp: permutes_inverses)
    from i j have "B $$ (i,j) = A $$ (p i, p j)" unfolding B_def by auto
    also have "\<dots> = 0" 
    proof (rule ccontr)
      assume "A $$ (p i, p j) \<noteq> 0" 
      hence "(p i, p j) \<in> ?G" unfolding graph_of_mat_def Let_def using i j p by auto
      with iI j have "p j \<in> I" unfolding I_def by auto
      with jI show False by simp
    qed
    finally have "B $$ (i,j) = 0" .
  } note zero = this
  have dimB[simp]: "dim_row B = n" "dim_col B = n" unfolding B_def by auto
  have dim: "dim_row B = k + (n - k)" "dim_col B = k + (n - k)" using kn by auto
  obtain B1 B2 B3 B4 where spl: "split_block B k k = (B1,B2,B3,B4)" (is "?tmp = _") by (cases ?tmp, auto)  
  from split_block[OF this dim] have
    Bs: "B1 \<in> carrier_mat k k" "B2 \<in> carrier_mat k (n - k)"
      "B3 \<in> carrier_mat (n - k) k" "B4 \<in> carrier_mat (n - k) (n - k)"
    and B: "B = four_block_mat B1 B2 B3 B4" by auto
  have B3: "B3 = 0\<^sub>m (n - k) k" unfolding arg_cong[OF spl[symmetric], of "\<lambda> (_,_,B,_). B", unfolded split]
    unfolding split_block_def Let_def split
    by (rule eq_matI, auto simp: kn zero)
  from elements_mat_permutes[OF p A B_def] 
  have elem: "elements_mat A = elements_mat B" .
  show ?thesis
    by (intro exI conjI, rule sim, rule elem, rule B[unfolded B3], insert Bs k0 kn, auto)
qed

lemma non_irreducible_nonneg_mat_split: 
  fixes A :: "'a :: linordered_idom mat" 
  assumes A: "A \<in> carrier_mat n n" 
  and nonneg: "nonneg_mat A" 
  and not: "\<not> irreducible_mat A" 
  and n: "n > 1" 
shows "\<exists> n1 n2 A1 A2. char_poly A = char_poly A1 * char_poly A2 
    \<and> nonneg_mat A1 \<and> nonneg_mat A2
    \<and> A1 \<in> carrier_mat n1 n1 \<and> A2 \<in> carrier_mat n2 n2
    \<and> 0 < n1 \<and> n1 < n \<and> 0 < n2 \<and> n2 < n \<and> n1 + n2 = n"
proof -
  from non_irreducible_mat_split[OF A not n]
  obtain n1 n2 B B1 B2 B4
    where sim: "similar_mat A B" and elem: "elements_mat A = elements_mat B" 
     and B: "B = four_block_mat B1 B2 (0\<^sub>m n2 n1) B4"
     and Bs: "B1 \<in> carrier_mat n1 n1" "B2 \<in> carrier_mat n1 n2" "B4 \<in> carrier_mat n2 n2" 
     and n: "0 < n1" "n1 < n" "0 < n2" "n2 < n" "n1 + n2 = n" by auto
  from char_poly_similar[OF sim] 
  have AB: "char_poly A = char_poly B" .
  from nonneg have nonneg: "nonneg_mat B" unfolding nonneg_mat_def elem by auto
  have cB: "char_poly B = char_poly B1 * char_poly B4"  
    by (rule char_poly_four_block_mat_lower_left_zero[OF B Bs])
  from nonneg have B1_B4: "nonneg_mat B1" "nonneg_mat B4" unfolding B nonneg_mat_def
    using elements_mat_four_block_mat_supseteq[OF Bs(1-2) _ Bs(3), of "0\<^sub>m n2 n1"] by auto
  show ?thesis
    by (intro exI conjI, rule AB[unfolded cB], rule B1_B4, rule B1_B4, 
        rule Bs, rule Bs, insert n, auto)
qed

text \<open>The main generalized theorem. The characteristic polynomial of a non-negative
  real matrix can be represented as a product of roots of unitys (scaled by the 
  the spectral radius sr) and a polynomial where all roots are smaller than the
  spectral radius.\<close>

theorem perron_frobenius_nonneg: fixes A :: "real Matrix.mat" 
  assumes A: "A \<in> carrier_mat n n" and pos: "nonneg_mat A" and n: "n \<noteq> 0" 
  shows "\<exists> sr ks f. 
    sr \<ge> 0 \<and> 
    0 \<notin> set ks \<and> ks \<noteq> [] \<and>
    char_poly A = prod_list (map (\<lambda> k. monom 1 k - [:sr ^ k:]) ks) * f \<and>
    (\<forall> x. poly (map_poly complex_of_real f) x = 0 \<longrightarrow> cmod x < sr)" 
proof -
  define p where "p = (\<lambda> sr k. monom 1 k - [: (sr :: real) ^ k:])" 
  let ?small = "\<lambda> f sr. (\<forall> x. poly (map_poly complex_of_real f) x = 0 \<longrightarrow> cmod x < sr)" 
  let ?wit = "\<lambda> A sr ks f. sr \<ge> 0 \<and> 0 \<notin> set ks \<and> ks \<noteq> [] \<and>
    char_poly A = prod_list (map (p sr) ks) * f \<and> ?small f sr" 
  let ?c = "complex_of_real" 
  interpret c: field_hom ?c ..
  interpret p: map_poly_inj_idom_divide_hom ?c ..
  have map_p: "map_poly ?c (p sr k) = (monom 1 k - [:?c sr^k:])" for sr k
    unfolding p_def by (simp add:  hom_distribs)
  { 
    fix k x sr
    assume 0: "poly (map_poly ?c (p sr k)) x = 0" and k: "k \<noteq> 0" and sr: "sr \<ge> 0" 
    note 0 also note map_p    
    finally have "x^k = (?c sr)^k" by (simp add: poly_monom) 
    from arg_cong[OF this, of "\<lambda> c. root k (cmod c)", unfolded norm_power] k
    have "cmod x = cmod (?c sr)" using real_root_pos2 by auto
    also have "\<dots> = sr" using sr by auto
    finally have "cmod x = sr" .
  } note p_conv = this  
  have "\<exists> sr ks f. ?wit A sr ks f" using A pos n
  proof (induct n arbitrary: A rule: less_induct)
    case (less n A)
    note pos = less(3)
    note A = less(2)
    note IH = less(1)
    note n = less(4)
    from n 
    consider (1) "n = 1"
      | (irr) "irreducible_mat A" 
      | (red) "\<not> irreducible_mat A" "n > 1" 
      by force
    thus "\<exists> sr ks f. ?wit A sr ks f" 
    proof cases
      case irr
      from perron_frobenius_irreducible(3,6)[OF A n pos irr refl refl]
      obtain sr k f where 
        *: "sr > 0" "k \<noteq> 0" "char_poly A = p sr k * f" "?small f sr" unfolding p_def
        by auto
      hence "?wit A sr [k] f" by auto
      thus ?thesis by blast
    next
      case red
      from non_irreducible_nonneg_mat_split[OF A pos red] obtain n1 n2 A1 A2
        where char:  "char_poly A = char_poly A1 * char_poly A2" 
          and pos: "nonneg_mat A1" "nonneg_mat A2" 
          and A: "A1 \<in> carrier_mat n1 n1" "A2 \<in> carrier_mat n2 n2" 
          and n: "n1 < n" "n2 < n" 
          and n0: "n1 \<noteq> 0" "n2 \<noteq> 0" by auto
      from IH[OF n(1) A(1) pos(1) n0(1)] obtain sr1 ks1 f1 where 1: "?wit A1 sr1 ks1 f1" by blast
      from IH[OF n(2) A(2) pos(2) n0(2)] obtain sr2 ks2 f2 where 2: "?wit A2 sr2 ks2 f2" by blast
      have "\<exists> A1 A2 sr1 ks1 f1 sr2 ks2 f2. ?wit A1 sr1 ks1 f1 \<and> ?wit A2 sr2 ks2 f2 \<and> 
         sr1 \<ge> sr2 \<and> char_poly A = char_poly A1 * char_poly A2" 
      proof (cases "sr1 \<ge> sr2")
        case True
        show ?thesis unfolding char
          by (intro exI, rule conjI[OF 1 conjI[OF 2]], insert True, auto)
      next
        case False
        show ?thesis unfolding char
          by (intro exI, rule conjI[OF 2 conjI[OF 1]], insert False, auto)
      qed
      then obtain A1 A2 sr1 ks1 f1 sr2 ks2 f2 where 
        1: "?wit A1 sr1 ks1 f1" and 2: "?wit A2 sr2 ks2 f2" and 
        sr: "sr1 \<ge> sr2" and char: "char_poly A = char_poly A1 * char_poly A2" by blast
      show ?thesis
      proof (cases "sr1 = sr2")
        case True
        have "?wit A sr2 (ks1 @ ks2) (f1 * f2)" unfolding char
          by (insert 1 2 True, auto simp: True p.hom_mult)
        thus ?thesis by blast
      next
        case False
        with sr have sr1: "sr1 > sr2" by auto         
        have lt: "poly (map_poly ?c (p sr2 k)) x = 0 \<Longrightarrow> k \<in> set ks2 \<Longrightarrow> cmod x < sr1" for k x
          using sr1 p_conv[of sr2 k x] 2 by auto
        have "?wit A sr1 ks1 (f1 * f2 * prod_list (map (p sr2) ks2))" unfolding char
          by (insert 1 2 sr1 lt, auto simp: p.hom_mult p.hom_prod_list 
          poly_prod_list prod_list_zero_iff)
        thus ?thesis by blast
      qed
    next
      case 1
      define a where "a = A $$ (0,0)"
      have A: "A = Matrix.mat 1 1 (\<lambda> x. a)" 
        by (rule eq_matI, unfold a_def, insert A 1(1), auto)
      have char: "char_poly A = [: - a, 1 :]" unfolding A  
        by (auto simp: Determinant.det_def char_poly_def char_poly_matrix_def)
      from pos A have a: "a \<ge> 0" unfolding nonneg_mat_def elements_mat by auto
      have "?wit A a [1] 1" unfolding char using a by (auto simp: p_def monom_Suc)
      thus ?thesis by blast
    qed
  qed
  then obtain sr ks f where wit: "?wit A sr ks f" by blast
  thus ?thesis using wit unfolding p_def by auto
qed

text \<open>And back to HMA world via transfer.\<close>

theorem perron_frobenius_non_neg: fixes A :: "real ^ 'n ^ 'n"
  assumes pos: "non_neg_mat A" 
  shows "\<exists> sr ks f. 
    sr \<ge> 0 \<and> 
    0 \<notin> set ks \<and> ks \<noteq> [] \<and>
    charpoly A = prod_list (map (\<lambda> k. monom 1 k - [:sr ^ k:]) ks) * f \<and>
    (\<forall> x. poly (map_poly complex_of_real f) x = 0 \<longrightarrow> cmod x < sr)" 
  using pos
proof (transfer, goal_cases)
  case (1 A)
  from perron_frobenius_nonneg[OF 1]
  show ?case by auto
qed

text \<open>We now specialize the theorem for complexity analysis where
  we are mainly interested in the case where the spectral radius is as most 1.
  Note that this can be checked by tested that there are no real roots of the
  characteristic polynomial which exceed 1.

  Moreover, here the existential quantifier over the factorization is replaced
  by @{const decompose_prod_root_unity}, an algorithm which computes this factorization 
  in an efficient way.\<close>

lemma perron_frobenius_for_complexity: fixes A :: "real ^ 'n ^ 'n" and f :: "real poly" 
  defines "cA \<equiv> map_matrix complex_of_real A" 
  defines "cf \<equiv> map_poly complex_of_real f" 
  assumes pos: "non_neg_mat A" 
   and sr: "\<And> x. poly (charpoly A) x = 0 \<Longrightarrow> x \<le> 1"
   and decomp: "decompose_prod_root_unity (charpoly A) = (ks, f)" 
  shows "0 \<notin> set ks" 
   "charpoly A = prod_root_unity ks * f"
   "charpoly cA = prod_root_unity ks * cf"
   "\<And> x. poly (charpoly cA) x = 0 \<Longrightarrow> cmod x \<le> 1" 
   "\<And> x. poly cf x = 0 \<Longrightarrow> cmod x < 1" 
   "\<And> x. cmod x = 1 \<Longrightarrow> order x (charpoly cA) = length [k\<leftarrow>ks . x ^ k = 1]" 
   "\<And> x. cmod x = 1 \<Longrightarrow> poly (charpoly cA) x = 0 \<Longrightarrow> \<exists> k \<in> set ks. x^k = 1" 
  unfolding cf_def cA_def
proof (atomize(full), goal_cases)
  case 1
  let ?c = "complex_of_real" 
  let ?cp = "map_poly ?c" 
  let ?A = "map_matrix ?c A" 
  let ?wit = "\<lambda> ks f. 0 \<notin> set ks \<and> 
    charpoly A = prod_root_unity ks * f \<and>
    charpoly ?A = prod_root_unity ks * map_poly of_real f \<and>
    (\<forall> x. poly (charpoly ?A) x = 0 \<longrightarrow> cmod x \<le> 1) \<and>
    (\<forall> x. poly (?cp f) x = 0 \<longrightarrow> cmod x < 1)" 
  interpret field_hom ?c ..
  interpret p: map_poly_inj_idom_divide_hom ?c ..
  {
    from perron_frobenius_non_neg[OF pos] obtain sr ks f 
      where *: "sr \<ge> 0" "0 \<notin> set ks" "ks \<noteq> []" 
       and cp: "charpoly A = prod_list (map (\<lambda> k. monom 1 k - [:sr ^ k:]) ks) * f" 
       and small: "\<And> x. poly (?cp f) x = 0 \<Longrightarrow> cmod x < sr" by blast

    from arg_cong[OF cp, of "map_poly ?c"]
    have cpc: "charpoly ?A = prod_list (map (\<lambda> k. monom 1 k - [:?c sr ^ k:]) ks) * map_poly ?c f" 
      by (simp add: charpoly_of_real hom_distribs p.prod_list_map_hom[symmetric] o_def)  
    have sr_le_1: "sr \<le> 1" 
      by (rule sr, unfold cp, insert *, cases ks, auto simp: poly_monom)
    {
      fix x
      note [simp] = prod_list_zero_iff o_def poly_monom
      assume "poly (charpoly ?A) x = 0" 
      from this[unfolded cpc poly_mult poly_prod_list] small[of x]
      consider (lt) "cmod x < sr" | (mem) k where "k \<in> set ks" "x ^ k = (?c sr) ^ k" by force
      hence "cmod x \<le> sr" 
      proof (cases)
        case (mem k)
        with * have k: "k \<noteq> 0" by metis
        with arg_cong[OF mem(2), of "\<lambda> x. root k (cmod x)", unfolded norm_power] 
          real_root_pos2[of k] *(1)
        have "cmod x = sr" by auto
        thus ?thesis by auto
      qed simp
    } note root = this
    have "\<exists> ks f. ?wit ks f" 
    proof (cases "sr = 1")
      case False    
      with sr_le_1 have *: "cmod x \<le> sr \<Longrightarrow> cmod x < 1" "cmod x \<le> sr \<Longrightarrow> cmod x \<le> 1" for x by auto
      show ?thesis
        by (rule exI[of _ Nil], rule exI[of _ "charpoly A"], insert * root,
        auto simp: prod_root_unity_def charpoly_of_real)
    next
      case sr: True
      from * cp cpc small root
      show ?thesis unfolding sr root_unity_def prod_root_unity_def by (auto simp: pCons_one)
    qed
  }
  then obtain Ks F where wit: "?wit Ks F" by auto
  have cA0: "charpoly ?A \<noteq> 0" using degree_monic_charpoly[of ?A] by auto
  from wit have id: "charpoly ?A = prod_root_unity Ks * ?cp F" by auto
  from of_real_hom.hom_decompose_prod_root_unity[of "charpoly A", unfolded decomp]
  have decompc: "decompose_prod_root_unity (charpoly ?A) = (ks, ?cp f)" 
    by (auto simp: charpoly_of_real)
  from wit have small: "cmod x = 1 \<Longrightarrow> poly (?cp F) x \<noteq> 0" for x by auto
  from decompose_prod_root_unity[OF id decompc this cA0]
  have id: "charpoly ?A = prod_root_unity ks * ?cp F" "F = f" "set Ks = set ks" by auto
  have "?cp (charpoly A) = ?cp (prod_root_unity ks * f)" unfolding id 
    unfolding charpoly_of_real[symmetric] id p.hom_mult of_real_hom.hom_prod_root_unity ..
  hence idr: "charpoly A = prod_root_unity ks * f" by auto
  have wit: "?wit ks f" and idc: "charpoly ?A = prod_root_unity ks * ?cp f" 
    using wit unfolding id idr by auto
  {
    fix x
    assume "cmod x = 1"
    from small[OF this, unfolded id] have "poly (?cp f) x \<noteq> 0" by auto
    from order_0I[OF this] this have ord: "order x (?cp f) = 0" and cf0: "?cp f \<noteq> 0" by auto
    have "order x (charpoly ?A) = order x (prod_root_unity ks)" unfolding idc
      by (subst order_mult, insert cf0 wit ord, auto)
    also have "\<dots> = length [k\<leftarrow>ks . x ^ k = 1]" 
      by (subst order_prod_root_unity, insert wit, auto)
    finally have ord: "order x (charpoly ?A) = length [k\<leftarrow>ks . x ^ k = 1]" .
    {
      assume "poly (charpoly ?A) x = 0" 
      with cA0 have "order x (charpoly ?A) \<noteq> 0" unfolding order_root by auto
      from this[unfolded ord] have "\<exists> k \<in> set ks. x ^ k = 1" 
        by (cases "[k\<leftarrow>ks . x ^ k = 1]", force+)
    } 
    note this ord
  }
  with wit show ?case by blast
qed

text \<open>and convert to JNF-world\<close>
lemmas perron_frobenius_for_complexity_jnf = 
  perron_frobenius_for_complexity[unfolded atomize_imp atomize_all, 
    untransferred, cancel_card_constraint, rule_format]

end
