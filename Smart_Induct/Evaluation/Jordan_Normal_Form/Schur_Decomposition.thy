(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Schur Decomposition\<close>

text \<open>We implement Schur decomposition as an algorithm which, given a square matrix $A$
  and a list eigenvalues, computes $B$, $P$, and $Q$ such that 
  $A = PBQ$, $B$ is upper-triangular and $PQ = 1$. The algorithm works is generic in
  the kind of field and can be applied on the rationals, the reals, and the complex numbers.
  The algorithm relies on the method of Gram-Schmidt to create an orthogonal basis,
  and on the Gauss-Jordan algorithm to find eigenvectors to a given eigenvalue.
  
 The algorithm is a key ingredient to show that every matrix with a linear factorizable 
 characteristic polynomial has a Jordan normal form. 

  A further consequence of the algorithm is that the characteristic polynomial of 
  a block diagonal matrix is the product of the characteristic polynomials of the blocks.\<close>

theory Schur_Decomposition
imports 
  Polynomial_Interpolation.Missing_Polynomial
  Gram_Schmidt 
  Char_Poly
begin

definition vec_inv :: "'a::conjugatable_field vec \<Rightarrow> 'a vec"
  where "vec_inv v = 1 / (v \<bullet>c v) \<cdot>\<^sub>v conjugate v"

lemma vec_inv_closed[simp]: "v \<in> carrier_vec n \<Longrightarrow> vec_inv v \<in> carrier_vec n"
  unfolding vec_inv_def by auto

lemma vec_inv_dim[simp]: "dim_vec (vec_inv v) = dim_vec v"
  unfolding vec_inv_def by auto

lemma vec_inv[simp]:
  assumes v: "v : carrier_vec n"
      and v0: "(v::'a::conjugatable_ordered_field vec) \<noteq> 0\<^sub>v n"
  shows "vec_inv v \<bullet> v = 1"
proof -
  { assume "v \<bullet>c v = 0"
    hence "v = 0\<^sub>v n" using conjugate_square_eq_0_vec[OF v] by auto
    hence False using v0 by auto
  }
  moreover have "conjugate v \<bullet> v = v \<bullet>c v"
    apply (rule comm_scalar_prod) using v by auto
  ultimately show ?thesis
    unfolding vec_inv_def
    apply (subst smult_scalar_prod_distrib)
    using assms by auto
qed

lemma corthogonal_inv:
  assumes orth: "corthogonal (vs ::'a::conjugatable_field vec list)"
      and V: "set vs \<subseteq> carrier_vec n"
  shows "inverts_mat (mat_of_rows n (map vec_inv vs)) (mat_of_cols n vs)"
    (is "inverts_mat ?W ?V")
proof -
  define l where "l = length vs"
  have rW[simp]: "dim_row ?W = l" using l_def by auto
  have cV[simp]:"dim_col ?V = l" using l_def by auto
  have dim: "\<And>i. i < length vs \<Longrightarrow> vs!i \<in> carrier_vec n" using V by auto
  show ?thesis
    unfolding inverts_mat_def
    apply rule
    unfolding mat_of_rows_carrier length_map l_def[symmetric]
    unfolding index_one_mat
  proof -
    show "dim_row (?W * ?V) = l" "dim_col (?W * ?V) = l"
      unfolding times_mat_def rW cV by auto
    fix i j assume i:"i<l" and j: "j<l"
    hence i2: "i<length vs"
      and i3: "i<length (map vec_inv vs)"
      and j2: "j<length vs" using l_def by auto
    hence id2: "vs ! i \<in> carrier_vec n"
      and id3: "map vec_inv vs ! i \<in> carrier_vec n"
      and id4: "conjugate (vs ! i) \<in> carrier_vec n"
      and jd2: "vs ! j \<in> carrier_vec n" using dim by auto
    show "(?W * ?V) $$ (i,j) = (if i = j then 1 else 0)"
      unfolding times_mat_def rW cV
      unfolding index_mat[OF i j] split
      unfolding mat_of_rows_row[OF i3 id3]
      unfolding col_mat_of_cols[OF j2 jd2]
      unfolding nth_map[OF i2]
      unfolding vec_inv_def
      unfolding smult_scalar_prod_distrib[OF id4 jd2]
      unfolding comm_scalar_prod[OF id4 jd2]
      using corthogonalD[OF orth j2 i2] by auto
  qed
qed

definition corthogonal_inv :: "'a::conjugatable_field mat \<Rightarrow> 'a mat"
  where "corthogonal_inv A = mat_of_rows (dim_row A) (map vec_inv (cols A))"

definition mat_adjoint :: "'a :: conjugatable_field mat \<Rightarrow> 'a mat"
  where "mat_adjoint A \<equiv> mat_of_rows (dim_row A) (map conjugate (cols A))"

definition corthogonal_mat :: "'a::conjugatable_field mat \<Rightarrow> bool"
  where "corthogonal_mat A \<equiv>
    let B = mat_adjoint A * A in
    diagonal_mat B \<and> (\<forall>i<dim_col A. B $$ (i,i) \<noteq> 0)"

lemma corthogonal_matD[elim]:
  assumes orth: "corthogonal_mat A"
      and i: "i < dim_col A"
      and j: "j < dim_col A"
  shows "(col A i \<bullet>c col A j = 0) = (i \<noteq> j)"
proof
  have ci: "col A i : carrier_vec (dim_row A)"
   and cj: "col A j : carrier_vec (dim_row A)" by auto
  note [simp] = conjugate_conjugate_sprod[OF ci cj]

  let ?B = "mat_adjoint A * A"
  have diag: "diagonal_mat ?B" and zero: "\<And>i. i<dim_col A \<Longrightarrow> ?B $$ (i,i) \<noteq> 0"
    using orth unfolding corthogonal_mat_def Let_def by auto
  { assume "i = j"
    hence "conjugate (col A i) \<bullet> col A j \<noteq> 0"
      using zero[OF i] unfolding mat_adjoint_def using i by simp
    hence "conjugate (conjugate (col A i) \<bullet> col A j) \<noteq> 0"
      unfolding conjugate_zero_iff.
    hence "col A i \<bullet>c col A j \<noteq> 0" by simp
  }
  thus "col A i \<bullet>c col A j = 0 \<Longrightarrow> i \<noteq> j" by auto
  { assume "i \<noteq> j"
    hence "conjugate (col A i) \<bullet> col A j = 0"
      using diag
      unfolding diagonal_mat_def
      unfolding mat_adjoint_def using i j by simp
    hence "conjugate (conjugate (col A i) \<bullet> col A j) = 0" by simp
    thus "col A i \<bullet>c col A j = 0" by simp
  }
qed

lemma corthogonal_matI[intro]:
  assumes "(\<And>i j. i < dim_col A \<Longrightarrow> j < dim_col A \<Longrightarrow> (col A i \<bullet>c col A j = 0) = (i \<noteq> j))"
  shows "corthogonal_mat A"
proof -
  { fix i j assume i: "i < dim_col A" and j: "j < dim_col A" and ij: "i \<noteq> j"
    have "conjugate (col A i) \<bullet> col A j = 0"
      by (metis assms col_dim i j ij conjugate_vec_sprod_comm)
  }
  moreover
  { fix i assume "i < dim_col A"
    hence "conjugate (col A i) \<bullet> col A i \<noteq> 0"
      by (metis assms comm_scalar_prod carrier_vec_conjugate carrier_vecI)
  }
  ultimately show ?thesis
  unfolding corthogonal_mat_def Let_def
  unfolding diagonal_mat_def
  unfolding mat_adjoint_def by auto
qed

lemma corthogonal_inv_result:
  assumes o: "corthogonal_mat (A::'a::conjugatable_field mat)"
  shows "inverts_mat (corthogonal_inv A) A"
proof -
  have oc: "corthogonal (cols A)"
    apply (intro corthogonalI) using corthogonal_matD[OF o] by auto
  show ?thesis unfolding corthogonal_inv_def
    using corthogonal_inv[OF oc cols_dim] by auto
qed

text "extends a vector to a basis"

definition basis_completion :: "'a::ring_1 vec \<Rightarrow> 'a vec list" where
  "basis_completion v \<equiv> let 
     n = dim_vec v;
     drop_index = hd ([ i . i <- [0..<n], v $ i \<noteq> 0]);
     vs = [unit_vec n i. i <- [0..<n], i \<noteq> drop_index] 
   in v # vs"

lemma (in vec_space) basis_completion: fixes v :: "'a :: field vec"
  assumes v: "v \<in> carrier_vec n"
      and v0: "v \<noteq> 0\<^sub>v n"
  shows 
    "basis (set (basis_completion v))"
    "set (basis_completion v) \<subseteq> carrier_vec n"
    "span (set (basis_completion v)) = carrier_vec n" 
    "distinct (basis_completion v)"
    "\<not> lin_dep (set (basis_completion v))"
    "length (basis_completion v) = n"
    "hd (basis_completion v) = v"
proof -
  let ?b = "basis_completion v"
  note d = basis_completion_def Let_def
  from v have dim: "dim_vec v = n" by auto
  let ?is = "[ i . i <- [0..<n], v $ i \<noteq> 0]"
  {
    assume empty: "set ?is = {}"
    have "v = 0\<^sub>v n"
      by (rule eq_vecI, insert empty v, auto)
  }
  with v0 obtain k ids where id: "?is = k # ids" and mem: "k \<in> set ?is" by (cases ?is, auto)
  from mem have vk: "v $ k \<noteq> 0" and k: "k < n" by auto
  {
    fix i 
    assume i: "\<not> i < k"
    have id: "k # [Suc k..<n] = [k ..< n]" using k by (simp add: upt_conv_Cons)
    from i have "i < n \<Longrightarrow> (k # [Suc k..<n]) ! (i - k) = i" 
      unfolding id
      by (subst nth_upt, auto)
  }
  hence split: "[0 ..< n] = [0 ..< k] @ k # [Suc k ..< n]"
    by (intro nth_equalityI, insert k, auto simp: nth_append) 
  {
    fix as
    assume "k \<notin> set as"
    hence "[unit_vec n i. i <- as, i \<noteq> k] = [unit_vec n i. i <- as]"
      by (induct as, auto)
  } note conv = this
  have b_all: "?b = v # [unit_vec n i. i <- [0..<n], i \<noteq> k]"
    unfolding d dim id by simp 
  also have "[unit_vec n i. i <- [0..<n], i \<noteq> k] = [unit_vec n i. i <- [0..<k]] @ [unit_vec n i. i <- [Suc k..<n]]"
    unfolding split by (auto simp: conv)
  finally have b: "?b = v # [unit_vec n i. i <- [0..<k]] @ [unit_vec n i. i <- [Suc k..<n]]" by simp
  show carr: "set ?b \<subseteq> carrier_vec n" (is "?S \<subseteq> _")
    unfolding b using assms by auto
  show "hd ?b = v" unfolding b by auto
  show len: "length (basis_completion v) = n" unfolding b using k
    by auto
  define I where "I = (\<lambda> i. if i < k then i else Suc i)"
  have I: "\<And> i. I i \<noteq> k" "\<And> i. Suc i < n \<Longrightarrow> I i < n" unfolding I_def by auto
  {
    fix i
    assume i: "i < n"
    have "?b ! i = (if i = 0 then v else unit_vec n (I (i - 1)))"
      unfolding b I_def using i
      by (auto split: if_splits simp: nth_append)
  } note bi = this
  show dist: "distinct ?b" unfolding distinct_conv_nth len
  proof (intro allI impI)
    fix i j
    assume i: "i < n" and j: "j < n" and ij: "i \<noteq> j"
    show "?b ! i \<noteq> ?b ! j"
    proof 
      assume id1: "?b ! i = ?b ! j" 
      hence id2: "\<And> l. ?b ! i $ l = ?b ! j $ l" by auto
      have "i = j" 
      proof (cases "i = 0")
        case True
        hence biv: "?b ! i = v" unfolding b by simp
        from True ij have bj: "?b ! j = unit_vec n (I (j - 1))" "Suc (j - 1) = j" unfolding bi[OF j] by auto
        with id2[of k, unfolded biv bj] vk I[of "j - 1"] k j
        have False by simp
        thus ?thesis ..
      next
        case False note i0 = this
        hence bi': "?b ! i = unit_vec n (I (i - 1))" "Suc (i - 1) = i" unfolding bi[OF i] by auto
        show ?thesis
        proof (cases "j = 0")
          case True
          hence bj: "?b ! j = v" unfolding b by simp
          from id2[of k, unfolded bi' bj] vk I[of "i - 1"] k i bi'
          have False by simp
          thus ?thesis by simp
        next
          case False note j0 = this
          hence bj: "?b ! j = unit_vec n (I (j - 1))" "Suc (j - 1) = j" unfolding bi[OF j] by auto
          have "1 = ?b ! i $ I (i - 1)" unfolding bi' using I[of "i - 1"] i i0 by auto
          also have "\<dots> = unit_vec n (I (j - 1)) $ I (i - 1)" unfolding id1 bj by simp
          also have "\<dots> = (if I (i - 1) = I (j - 1) then 1 else 0)"
            using I[of "i - 1"] I[of "j - 1"] i0 j0 i j by auto
          finally have "I (i - 1) = I (j - 1)" by (auto split: if_splits)
          with i0 j0 show "i = j" unfolding I_def by (auto split: if_splits)
        qed
      qed   
      thus False using ij by simp
    qed
  qed
  have "span (set ?b) \<subseteq> carrier_vec n" using carr by auto
  moreover
  {
    fix w :: "'a vec"
    assume w: "w \<in> carrier_vec n"
    define lookup where "lookup = (v,k) # [(unit_vec n i, i). i <- [0..<n], i \<noteq> k]"
    define a where "a = (\<lambda> vi. case map_of lookup vi of Some i \<Rightarrow> if i = k then w $ k / v $ k else
       w $ i - w $ k / v $ k * v $ i)" 
    have "map fst lookup = ?b" unfolding b_all lookup_def 
      by (auto simp: map_concat o_def if_distrib, unfold list.simps fst_def prod.simps, simp)
    with dist have dist: "distinct (map fst lookup)" by simp
    let ?w = "lincomb a (set ?b)"
    have "?w \<in> carrier_vec n" using carr by auto
    with w have dim: "dim_vec w = n" "dim_vec ?w = n" by auto
    have "w = ?w" 
    proof (rule eq_vecI; unfold dim)
      fix i
      assume i: "i < n"
      show "w $ i = ?w $ i" unfolding lincomb_def 
      proof (subst finsum_index[OF i _ carr]) 
        show "(\<lambda>v. a v \<cdot>\<^sub>v v) \<in> set ?b \<rightarrow> carrier_vec n" using carr by auto
        {
          fix x :: "'a vec" and j
          assume "x = unit_vec n j" "j \<noteq> k" "j < n"
          hence "(x,j) \<in> set lookup" unfolding lookup_def by auto
          from map_of_is_SomeI[OF dist this]
          have "a x = w $ j - w $ k / v $ k * v $ j" unfolding a_def using \<open>j \<noteq> k\<close> by auto
        } note a = this          
        have "(\<Sum>x\<in>set ?b. (a x \<cdot>\<^sub>v x) $ i) = (a v \<cdot>\<^sub>v v) $ i + (\<Sum>x\<in>(set ?b) - {v}. (a x \<cdot>\<^sub>v x) $ i)"
          by (rule sum.remove[OF finite_set], auto simp: b)
        also have "a v = w $ k / v $ k" unfolding a_def lookup_def by auto
        also have "(\<dots> \<cdot>\<^sub>v v) $ i = w $ k / v $ k * v $ i" using i v by auto
        finally have "(\<Sum>x\<in>set ?b. (a x \<cdot>\<^sub>v x) $ i) = w $ k / v $ k * v $ i + (\<Sum>x\<in>(set ?b) - {v}. (a x \<cdot>\<^sub>v x) $ i)" .
        also have "\<dots> = w $ i"
        proof (cases "i = k")
          case True
          hence "w $ k / v $ k * v $ i = w $ k" using vk by auto
          moreover have "(\<Sum>x\<in>(set ?b) - {v}. (a x \<cdot>\<^sub>v x) $ i) = 0" unfolding True
          proof (rule sum.neutral, intro ballI)
            fix x
            assume "x \<in> set ?b - {v}"
            then obtain j where x: "x = unit_vec n j" "j \<noteq> k" "j < n" using k unfolding b by auto
            show "(a x \<cdot>\<^sub>v x) $ k = 0" unfolding a[OF x] unfolding x using x k by auto
          qed
          ultimately show ?thesis unfolding True by simp
        next
          case False
          let ?ui = "unit_vec n i :: 'a vec"
          {
            assume "?ui = v"
            from arg_cong[OF this, of "\<lambda> v. v $ k"] vk i k False have False by auto
          }
          hence diff: "?ui \<noteq> v" by auto
          from a[OF refl False] have ai: "(a ?ui \<cdot>\<^sub>v ?ui) $ i = w $ i - w $ k / v $ k * v $ i" 
            using i by auto          
          have "?ui \<in> set ?b" unfolding b_all using False k i by auto
          with diff have mem: "unit_vec n i \<in> set ?b - {v}" by auto
          have "w $ k / v $ k * v $ i + (\<Sum>x\<in>(set ?b) - {v}. (a x \<cdot>\<^sub>v x) $ i)
            = w $ i + (\<Sum>x\<in>(set ?b) - {v,?ui}. (a x \<cdot>\<^sub>v x) $ i)"
            by (subst sum.remove[OF _ mem], auto simp: ai intro!: sum.cong)
          also have "(\<Sum>x\<in>(set ?b) - {v,?ui}. (a x \<cdot>\<^sub>v x) $ i) = 0"
            by (rule sum.neutral, unfold b_all, insert i k, auto)
          finally show ?thesis by simp
        qed
        finally show "w $ i = (\<Sum>x\<in>set ?b. (a x \<cdot>\<^sub>v x) $ i)" by simp
      qed
    qed auto
    hence "w \<in> span (set ?b)" unfolding span_def by auto
  }
  ultimately show span: "span (set ?b) = carrier_vec n" by blast
  show "basis (set ?b)"
  proof (rule dim_gen_is_basis[OF finite_set carr span])
    have "card (set ?b) = dim" using dist len distinct_card unfolding dim_is_n by blast
    thus "card (set ?b) \<le> dim" by simp
  qed
  thus "\<not> lin_dep (set ?b)" unfolding basis_def by auto
qed

lemma orthogonal_mat_of_cols:
  assumes W: "set ws \<subseteq> carrier_vec n"
    and orth: "corthogonal ws"
    and len: "length ws = n"
  shows "corthogonal_mat (mat_of_cols n ws)" (is "corthogonal_mat ?W")
proof
    fix i j assume i: "i < dim_col ?W" and j: "j < dim_col ?W"
    hence [simp]: "ws ! i : carrier_vec n" "ws ! j : carrier_vec n"
      using W len by auto
    have "i < length ws" and "j < length ws" using i j using len W by auto
    thus "col ?W i \<bullet>c col ?W j = 0 \<longleftrightarrow> i \<noteq> j"
      using orth
      unfolding corthogonal_def
      by simp
qed

lemma corthogonal_col_ev_0: fixes A :: "'a :: conjugatable_ordered_field mat"
  assumes A: "A \<in> carrier_mat n n"
  and v: "v \<in> carrier_vec n"
  and v0: "v \<noteq> 0\<^sub>v n"
  and eigen[simp]: "A *\<^sub>v v = e \<cdot>\<^sub>v v"
  and n: "n \<noteq> 0"
  and hdws: "hd ws = v"
  and ws: "set ws \<subseteq> carrier_vec n" "corthogonal ws" "length ws = n"
  defines "W == mat_of_cols n ws"
  defines "W' == corthogonal_inv W"
  defines "A' == W' * A * W"
  shows "col A' 0 = vec n (\<lambda> i. if i = 0 then e else 0)"
proof -
  let ?f = "(\<lambda> i. if i = 0 then e else 0)"
  from ws have W: "W \<in> carrier_mat n n" unfolding W_def by auto
  from W have W': "W' \<in> carrier_mat n n" unfolding W'_def 
    corthogonal_inv_def mat_of_rows_def by auto
  from A W W' have A': "A' \<in> carrier_mat n n" unfolding A'_def by auto
  show "col A' 0 = vec n ?f"
  proof (rule,unfold dim_vec)
    show dim: "dim_vec (col A' 0) = n" using A' by simp
    have row0: "vec_inv v \<bullet> (A *\<^sub>v v) = e"
      using scalar_prod_smult_distrib[OF vec_inv_closed[OF v] v]
      using vec_inv[OF v v0] by auto
    fix i assume i: "i < n"
    hence i2: "i < length ws" using ws by auto
    let ?wsi = "ws ! i"
    have z: "0 < dim_col A'" using A' n by auto
    hence z2: "0 < length ws" using A' ws by auto
    have wsi[simp]: "ws!i : carrier_vec n" using ws i by auto
    hence ws0[simp]: "ws!0 = v" using hd_conv_nth[symmetric] hdws z2 by auto
    have "col A' 0 $ i = A' $$ (i, 0)" using A' i by auto
    also have "... = (W' * (A * W)) $$ (i, 0)" unfolding A'_def using W' A W by auto
    also have "... = row W' i \<bullet> col (A * W) 0"
      apply (subst index_mult_mat) using W W' A i by auto
    also have "row W' i = vec_inv ?wsi"
      unfolding W'_def W_def unfolding corthogonal_inv_def using i ws by auto
    also have "col (A * W) 0 = A *\<^sub>v col W 0" using A W z A' by auto
    also have "col W 0 = v" unfolding W_def using z2 ws0 n col_mat_of_cols v by blast
    also have "A *\<^sub>v v = e \<cdot>\<^sub>v v" using eigen.
    also have "vec_inv ?wsi \<bullet> (e \<cdot>\<^sub>v v) = e * (vec_inv ?wsi \<bullet> v)"
      using scalar_prod_smult_distrib[OF vec_inv_closed[OF wsi] v].
    also have "... = ?f i"
    proof(cases "i = 0")
      case True thus ?thesis using vec_inv[OF v v0] by simp
    next 
      case False
      hence z: "0 < length ws" using i ws by auto
      note cwsi = carrier_vec_conjugate[OF wsi]
      have "vec_inv ?wsi \<bullet> v = 1 / (?wsi \<bullet>c ?wsi) * (conjugate ?wsi \<bullet> v)"
        unfolding vec_inv_def unfolding smult_scalar_prod_distrib[OF cwsi v].. 
      also have "conjugate ?wsi \<bullet> v = v \<bullet>c ?wsi"
        using comm_scalar_prod[OF cwsi v].
      also have "... = 0"
        using corthogonalD[OF ws(2) z i2] False unfolding ws0 by auto
      finally show ?thesis using False by auto
    qed
    also have "... = vec n ?f $ i" using i by simp
    finally show "col A' 0 $ i = vec n ?f $ i" .
  qed
qed


text "Schur decomposition"
fun schur_decomposition :: "'a::conjugatable_field mat \<Rightarrow> 'a list \<Rightarrow> 'a mat \<times> 'a mat \<times> 'a mat" where 
  "schur_decomposition A [] = (A, 1\<^sub>m (dim_row A), 1\<^sub>m (dim_row A))"
| "schur_decomposition A (e # es) = (let
       n = dim_row A;
       n1 = n - 1;
       v = find_eigenvector A e;
       ws = gram_schmidt n (basis_completion v);
       W = mat_of_cols n ws;
       W' = corthogonal_inv W;
       A' = W' * A * W;
       (A1,A2,A0,A3) = split_block A' 1 1;
       (B,P,Q) = schur_decomposition A3 es;
       z_row = (0\<^sub>m 1 n1);
       z_col = (0\<^sub>m n1 1);
       one_1 = 1\<^sub>m 1
     in (four_block_mat A1 (A2 * P) A0 B, 
     W * four_block_mat one_1 z_row z_col P, 
     four_block_mat one_1 z_row z_col Q * W'))"


theorem schur_decomposition:
  assumes A: "(A::'a::conjugatable_ordered_field mat) \<in> carrier_mat n n"
      and c: "char_poly A = (\<Prod> (e :: 'a) \<leftarrow> es. [:- e, 1:])"
      and B: "schur_decomposition A es = (B,P,Q)"
  shows "similar_mat_wit A B P Q \<and> upper_triangular B \<and> diag_mat B = es"
  using assms
proof (induct es arbitrary: n A B P Q)
  case Nil
  with degree_monic_char_poly[of A n]
  show ?case by (auto intro: similar_mat_wit_refl simp: diag_mat_def)
next
  case (Cons e es n A C P Q)
  let ?n1 = "n - 1"
  from Cons have A: "A \<in> carrier_mat n n" and dim: "dim_row A = n" by auto
  let ?cp = "char_poly A"
  from Cons(3)
  have cp: "?cp = [: -e, 1 :] * (\<Prod>e \<leftarrow> es. [:- e, 1:])" by auto
  have mon: "monic (\<Prod>e\<leftarrow> es. [:- e, 1:])" by (rule monic_prod_list, auto)
  have deg: "degree ?cp = Suc (degree (\<Prod>e\<leftarrow> es. [:- e, 1:]))" unfolding cp
    by (subst degree_mult_eq, insert mon, auto)
  with degree_monic_char_poly[OF A] have n: "n \<noteq> 0" by auto
  define v where "v = find_eigenvector A e"
  define b where "b = basis_completion v"
  define ws where "ws = gram_schmidt n b"
  define W where "W = mat_of_cols n ws"
  define W' where "W' = corthogonal_inv W"
  define A' where "A' = W' * A * W"
  obtain A1 A2 A0 A3 where splitA': "split_block A' 1 1 = (A1,A2,A0,A3)"
    by (cases "split_block A' 1 1", auto)
  obtain B P' Q' where schur: "schur_decomposition A3 es = (B,P',Q')" 
    by (cases "schur_decomposition A3 es", auto)
  let ?P' = "four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 ?n1) (0\<^sub>m ?n1 1) P'"
  let ?Q' = "four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 ?n1) (0\<^sub>m ?n1 1) Q'"
  have C: "C = four_block_mat A1 (A2 * P') A0 B" and P: "P = W * ?P'" and Q: "Q = ?Q' * W'"
    using Cons(4) unfolding schur_decomposition.simps
    Let_def list.sel dim
    v_def[symmetric] b_def[symmetric] ws_def[symmetric] W'_def[symmetric] W_def[symmetric]
    A'_def[symmetric] split splitA' schur by auto
  have e: "eigenvalue A e" 
    unfolding eigenvalue_root_char_poly[OF A] cp by simp
  from find_eigenvector[OF A e] have ev: "eigenvector A v e" unfolding v_def .
  from this[unfolded eigenvector_def]
  have v[simp]: "v \<in> carrier_vec n" and v0: "v \<noteq> 0\<^sub>v n" using A by auto
  interpret cof_vec_space n "TYPE('a)" .
  from basis_completion[OF v v0, folded b_def]
  have span_b: "span (set b) = carrier_vec n" and dist_b: "distinct b" 
    and indep: "\<not> lin_dep (set b)" and b: "set b \<subseteq> carrier_vec n" and hdb: "hd b = v" 
    and len_b: "length b = n" by auto
  from hdb len_b n obtain vs where bv: "b = v # vs" by (cases b, auto)
  from gram_schmidt_result[OF b dist_b indep refl, folded ws_def]
  have ws: "set ws \<subseteq> carrier_vec n" "corthogonal ws" "length ws = n" 
    by (auto simp: len_b)
  from gram_schmidt_hd[OF v, of vs, folded bv] have hdws: "hd ws = v" unfolding ws_def .
  have orth_W: "corthogonal_mat W" using orthogonal_mat_of_cols ws unfolding W_def.
  have W: "W \<in> carrier_mat n n"
    using ws unfolding W_def using mat_of_cols_carrier(1)[of n ws] by auto
  have W': "W' \<in> carrier_mat n n" unfolding W'_def corthogonal_inv_def using W 
    by (auto simp: mat_of_rows_def)  
  from corthogonal_inv_result[OF orth_W] 
  have W'W: "inverts_mat W' W" unfolding W'_def .
  hence WW': "inverts_mat W W'" using mat_mult_left_right_inverse[OF W' W] W' W
    unfolding inverts_mat_def by auto
  have A': "A' \<in> carrier_mat n n" using W W' A unfolding A'_def by auto
  have A'A_wit: "similar_mat_wit A' A W' W"
    by (rule similar_mat_witI[of _ _ n], insert W W' A A' W'W WW', auto simp: A'_def
    inverts_mat_def)
  hence A'A: "similar_mat A' A" unfolding similar_mat_def by blast
  from similar_mat_wit_sym[OF A'A_wit] have simAA': "similar_mat_wit A A' W W'" by auto
  have eigen[simp]: "A *\<^sub>v v = e \<cdot>\<^sub>v v" and v0: "v \<noteq> 0\<^sub>v n"
    using v_def find_eigenvector[OF A e] A
    unfolding eigenvector_def by auto
  let ?f = "(\<lambda> i. if i = 0 then e else 0)"
  have col0: "col A' 0 = vec n ?f"
    unfolding A'_def W'_def W_def
    using corthogonal_col_ev_0[OF A v v0 eigen n hdws ws].
  from A' n have "dim_row A' = 1 + ?n1" "dim_col A' = 1 + ?n1" by auto
  from split_block[OF splitA' this] have A2: "A2 \<in> carrier_mat 1 ?n1"
    and A3: "A3 \<in> carrier_mat ?n1 ?n1" 
    and A'block: "A' = four_block_mat A1 A2 A0 A3" by auto
  have A1id: "A1 = mat 1 1 (\<lambda> _. e)"
    using splitA'[unfolded split_block_def Let_def] arg_cong[OF col0, of "\<lambda> v. v $ 0"] A' n
    by (auto simp: col_def)
  have A1: "A1 \<in> carrier_mat 1 1" unfolding A1id by auto
  {
    fix i
    assume "i < ?n1"
    with arg_cong[OF col0, of "\<lambda> v. v $ Suc i"] A'
    have "A' $$ (Suc i, 0) = 0" by auto
  } note A'0 = this
  have A0id: "A0 = 0\<^sub>m ?n1 1"
    using splitA'[unfolded split_block_def Let_def] A'0 A' by auto
  have A0: "A0 \<in> carrier_mat ?n1 1" unfolding A0id by auto
  from cp char_poly_similar[OF A'A]
  have cp: "char_poly A' = [: -e,1 :] * (\<Prod> e \<leftarrow> es. [:- e, 1:])" by simp
  also have "char_poly A' = char_poly A1 * char_poly A3" 
    unfolding A'block A0id
    by (rule char_poly_four_block_zeros_col[OF A1 A2 A3])
  also have "char_poly A1 = [: -e,1 :]"
    by (simp add: A1id char_poly_defs det_def signof_def sign_def)
  finally have cp: "char_poly A3 = (\<Prod> e \<leftarrow> es. [:- e, 1:])"
    by (metis mult_cancel_left pCons_eq_0_iff zero_neq_one)
  from Cons(1)[OF A3 cp schur]
  have simIH: "similar_mat_wit A3 B P' Q'" and ut: "upper_triangular B" and diag: "diag_mat B = es" by auto
  from similar_mat_witD2[OF A3 simIH] 
  have B: "B \<in> carrier_mat ?n1 ?n1" and P': "P' \<in> carrier_mat ?n1 ?n1" and Q': "Q' \<in> carrier_mat ?n1 ?n1" 
    and PQ': "P' * Q' = 1\<^sub>m ?n1" by auto
  have A0_eq: "A0 = P' * A0 * 1\<^sub>m 1" unfolding A0id using P' by auto
  have simA'C: "similar_mat_wit A' C ?P' ?Q'" unfolding A'block C
    by (rule similar_mat_wit_four_block[OF similar_mat_wit_refl[OF A1] simIH _ A0_eq A1 A3 A0],
    insert PQ' A2 P' Q', auto)
  have ut1: "upper_triangular A1" unfolding A1id by auto
  have ut: "upper_triangular C" unfolding C A0id
    by (intro upper_triangular_four_block[OF _ B ut1 ut], auto simp: A1id)
  from A1id have diagA1: "diag_mat A1 = [e]" unfolding diag_mat_def by auto
  from diag_four_block_mat[OF A1 B] have diag: "diag_mat C = e # es" unfolding diag diagA1 C by simp
  from ut similar_mat_wit_trans[OF simAA' simA'C, folded P Q] diag
  show ?case by blast
qed

definition schur_upper_triangular :: "'a::conjugatable_field mat \<Rightarrow> 'a list \<Rightarrow> 'a mat" where 
  "schur_upper_triangular A es = (case schur_decomposition A es of (B,_,_) \<Rightarrow> B)"


lemma schur_upper_triangular:
  assumes A: "(A :: 'a :: conjugatable_ordered_field mat) \<in> carrier_mat n n"
  and linear: "char_poly A = (\<Prod> a \<leftarrow> es. [:- a, 1:])"
  defines B: "B \<equiv> schur_upper_triangular A es"
  shows "B \<in> carrier_mat n n" "upper_triangular B" "similar_mat A B" 
proof -
  let ?B = "schur_upper_triangular A es"
  obtain C P Q where schur: "schur_decomposition A es = (C,P,Q)" 
    by (cases "schur_decomposition A es", auto)
  hence B: "B = C" using A unfolding schur_upper_triangular_def B by auto
  from schur_decomposition[OF A linear schur]
  have sim: "similar_mat_wit A B P Q" and B: "upper_triangular B" unfolding B by auto
  from sim show "similar_mat A B" unfolding similar_mat_def by auto
  from similar_mat_witD2[OF A sim] show "B \<in> carrier_mat n n" by auto
  show "upper_triangular B" by fact
qed

lemma schur_decomposition_exists: assumes A: "A \<in> carrier_mat n n"
  and linear: "char_poly A = (\<Prod> (a :: 'a :: conjugatable_ordered_field) \<leftarrow> es. [:- a, 1:])"
  shows "\<exists> B \<in> carrier_mat n n. upper_triangular B \<and> similar_mat A B" 
  using schur_upper_triangular[OF A linear] by blast

lemma char_poly_0_block: fixes A :: "'a :: conjugatable_ordered_field mat"
  assumes A: "A = four_block_mat B C (0\<^sub>m m n) D"
  and linearB: "\<exists> es. char_poly B = (\<Prod> a \<leftarrow> es. [:- a, 1:])"
  and linearD: "\<exists> es. char_poly D = (\<Prod> a \<leftarrow> es. [:- a, 1:])"
  and B: "B \<in> carrier_mat n n"
  and C: "C \<in> carrier_mat n m"
  and D: "D \<in> carrier_mat m m"
  shows "char_poly A = char_poly B * char_poly D"
proof -
  from linearB obtain bs where cB: "char_poly B = (\<Prod>a\<leftarrow>bs. [:- a, 1:])" by auto
  from linearD obtain ds where cD: "char_poly D = (\<Prod>a\<leftarrow>ds. [:- a, 1:])" by auto
  from schur_decomposition_exists[OF B cB] 
  obtain B' PB QB where sB: "schur_decomposition B bs = (B',PB,QB)" 
    by (cases "schur_decomposition B bs", auto)
  obtain D' PD QD where sD: "schur_decomposition D ds = (D',PD,QD)" 
    by (cases "schur_decomposition D ds", auto)
  from schur_decomposition[OF B cB sB] similar_mat_witD2[OF B, of B'] have 
    simB: "similar_mat B B'" and utB: "upper_triangular B'" and diagB: "diag_mat B' = bs"
    and B': "B' \<in> carrier_mat n n"
    by (auto simp: similar_mat_def)
  from schur_decomposition[OF D cD sD] similar_mat_witD2[OF D, of D'] have 
    simD: "similar_mat D D'" and utD: "upper_triangular D'" and diagD: "diag_mat D' = ds"
    and D': "D' \<in> carrier_mat m m"
    by (auto simp: similar_mat_def)
  let ?z = "0\<^sub>m m n"
  from similar_mat_four_block_0_ex[OF simB simD C B D, folded A]
    obtain B0 where B0: "B0 \<in> carrier_mat n m" and sim: "similar_mat A (four_block_mat B' B0 ?z D')" 
    by auto
  let ?block = "four_block_mat B' B0 ?z D'"
  let ?cp = char_poly
  let ?prod = "QB * C * PD"
  let ?diag = "\<lambda> A. (\<Prod>a\<leftarrow>diag_mat A. [:- a, 1:])"
  from char_poly_similar[OF sim] have "?cp A = ?cp ?block" by simp
  also have "\<dots> = ?diag ?block"
    by (rule char_poly_upper_triangular[OF four_block_carrier_mat[OF B' D'] upper_triangular_four_block[OF B' D' utB utD]])      
  also have "\<dots> = ?diag B' * ?diag D'" unfolding diag_four_block_mat[OF B' D']
    by auto
  also have "?diag B' = ?cp B'"
    by (subst char_poly_upper_triangular[OF B' utB], simp)
  also have "\<dots> = ?cp B"
    by (rule char_poly_similar[OF similar_mat_sym[OF simB]])
  also have "?diag D' = ?cp D'"
    by (subst char_poly_upper_triangular[OF D' utD], simp)
  also have "\<dots> = ?cp D"
    by (rule char_poly_similar[OF similar_mat_sym[OF simD]])
  finally show ?thesis .
qed


lemma char_poly_0_block': fixes A :: "'a :: conjugatable_ordered_field mat"
  assumes A: "A = four_block_mat B (0\<^sub>m n m) C D"
  and linearB: "\<exists> es. char_poly B = (\<Prod> a \<leftarrow> es. [:- a, 1:])"
  and linearD: "\<exists> es. char_poly D = (\<Prod> a \<leftarrow> es. [:- a, 1:])"
  and B: "B \<in> carrier_mat n n"
  and C: "C \<in> carrier_mat m n"
  and D: "D \<in> carrier_mat m m"
  shows "char_poly A = char_poly B * char_poly D"
proof -
  let ?A = "four_block_mat B (0\<^sub>m n m) C D"
  let ?B = "transpose_mat B"
  let ?D = "transpose_mat D"
  have AC: "?A \<in> carrier_mat (n + m) (n + m)" using B D by auto
  from arg_cong[OF transpose_four_block_mat[OF B zero_carrier_mat C D], of char_poly,
    unfolded char_poly_transpose_mat[OF AC], folded A]
  have "char_poly A =
    char_poly (four_block_mat ?B (transpose_mat C) (0\<^sub>m m n) ?D)" by auto
  also have "\<dots> = char_poly ?B * char_poly ?D"
    by (rule char_poly_0_block[OF refl], insert B C D linearB linearD, auto)
  also have "\<dots> = char_poly B * char_poly D" using B D
    by simp
  finally show ?thesis .
qed

end
