section \<open>Missing Lemmas on Vectors and Matrices\<close>

text \<open>We provide some results on vector spaces which should be merged into Jordan-Normal-Form/Matrix.\<close>
theory Missing_Matrix
  imports Jordan_Normal_Form.Matrix
begin

lemma orthogonalD': assumes "orthogonal vs"
  and "v \<in> set vs" and "w \<in> set vs"
shows "(v \<bullet> w = 0) = (v \<noteq> w)"
proof -
  from assms(2) obtain i where v: "v = vs ! i" and i: "i < length vs" by (auto simp: set_conv_nth)
  from assms(3) obtain j where w: "w = vs ! j" and j: "j < length vs" by (auto simp: set_conv_nth)
  from orthogonalD[OF assms(1) i j, folded v w] orthogonalD[OF assms(1) i i, folded v v]
  show ?thesis using v w by auto
qed

lemma zero_mat_mult_vector[simp]: "x \<in> carrier_vec nc \<Longrightarrow> 0\<^sub>m nr nc *\<^sub>v x = 0\<^sub>v nr"
  by (intro eq_vecI, auto)

lemma add_diff_cancel_right_vec:
  "a \<in> carrier_vec n \<Longrightarrow> (b :: 'a :: cancel_ab_semigroup_add vec) \<in> carrier_vec n \<Longrightarrow>
    (a + b) - b = a"
  by (intro eq_vecI, auto)

lemma elements_four_block_mat_id:
  assumes c: "A \<in> carrier_mat nr1 nc1" "B \<in> carrier_mat nr1 nc2"
    "C \<in> carrier_mat nr2 nc1" "D \<in> carrier_mat nr2 nc2"
  shows
    "elements_mat (four_block_mat A B C D) =
   elements_mat A \<union> elements_mat B \<union> elements_mat C \<union> elements_mat D"
    (is "elements_mat ?four = ?X")
proof
  show "elements_mat ?four \<subseteq> ?X"
    by (rule elements_four_block_mat[OF c])
  have 4: "?four \<in> carrier_mat (nr1 + nr2) (nc1 + nc2)" using c by auto
  {
    fix x
    assume "x \<in> ?X"
    then consider (A) "x \<in> elements_mat A"
      | (B) "x \<in> elements_mat B"
      | (C) "x \<in> elements_mat C"
      | (D) "x \<in> elements_mat D" by auto
    hence "x \<in> elements_mat ?four"
    proof (cases)
      case A
      from elements_matD[OF this] obtain i j
        where *: "i < nr1" "j < nc1" and x: "x = A $$ (i,j)"
        using c by auto
      from elements_matI[OF 4, of i j x] * c
      show ?thesis unfolding x by auto
    next
      case B
      from elements_matD[OF this] obtain i j
        where *: "i < nr1" "j < nc2" and x: "x = B $$ (i,j)"
        using c by auto
      from elements_matI[OF 4, of i "nc1 + j" x] * c
      show ?thesis unfolding x by auto
    next
      case C
      from elements_matD[OF this] obtain i j
        where *: "i < nr2" "j < nc1" and x: "x = C $$ (i,j)"
        using c by auto
      from elements_matI[OF 4, of "nr1 + i" j x] * c
      show ?thesis unfolding x by auto
    next
      case D
      from elements_matD[OF this] obtain i j
        where *: "i < nr2" "j < nc2" and x: "x = D $$ (i,j)"
        using c by auto
      from elements_matI[OF 4, of "nr1 + i" "nc1 + j" x] * c
      show ?thesis unfolding x by auto
    qed
  }
  thus "elements_mat ?four \<supseteq> ?X" by blast
qed


lemma elements_mat_append_rows: "A \<in> carrier_mat nr n \<Longrightarrow> B \<in> carrier_mat nr2 n \<Longrightarrow>
  elements_mat (A @\<^sub>r B) = elements_mat A \<union> elements_mat B"
  unfolding append_rows_def
  by (subst elements_four_block_mat_id, auto)

lemma elements_mat_uminus[simp]: "elements_mat (-A) = uminus ` elements_mat A"
  unfolding elements_mat_def by auto

lemma vec_set_uminus[simp]: "vec_set (-A) = uminus ` vec_set A"
  unfolding vec_set_def by auto

definition append_cols :: "'a :: zero mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat"  (infixr "@\<^sub>c" 65) where
  "A @\<^sub>c B = (A\<^sup>T @\<^sub>r B\<^sup>T)\<^sup>T"

lemma carrier_append_cols[simp, intro]:
  "A \<in> carrier_mat nr nc1 \<Longrightarrow>
   B \<in> carrier_mat nr nc2 \<Longrightarrow> (A @\<^sub>c B) \<in> carrier_mat nr (nc1 + nc2)"
  unfolding append_cols_def by auto

lemma elements_mat_transpose_mat[simp]: "elements_mat (A\<^sup>T) = elements_mat A"
  unfolding elements_mat_def by auto

lemma elements_mat_append_cols: "A \<in> carrier_mat n nc \<Longrightarrow> B \<in> carrier_mat n nc1
  \<Longrightarrow> elements_mat (A @\<^sub>c B) = elements_mat A \<union> elements_mat B"
  unfolding append_cols_def elements_mat_transpose_mat
  by (subst elements_mat_append_rows, auto)

lemma vec_first_index:
  assumes v: "dim_vec v \<ge> n"
    and i: "i < n"
  shows "(vec_first v n) $ i = v $ i"
  unfolding vec_first_def using assms by simp

lemma vec_last_index:
  assumes v: "v \<in> carrier_vec (n + m)"
    and i: "i < m"
  shows "(vec_last v m) $ i = v $ (n + i)"
  unfolding vec_last_def using assms by simp

lemma vec_first_add:
  assumes "dim_vec x \<ge> n"
    and "dim_vec y \<ge> n"
  shows"vec_first (x + y) n = vec_first x n + vec_first y n"
  unfolding vec_first_def using assms by auto

lemma vec_first_zero[simp]: "m \<le> n \<Longrightarrow> vec_first (0\<^sub>v n) m = 0\<^sub>v m"
  unfolding vec_first_def by auto

lemma vec_first_smult:
  "\<lbrakk> m \<le> n; x \<in> carrier_vec n \<rbrakk> \<Longrightarrow> vec_first (c \<cdot>\<^sub>v x) m = c \<cdot>\<^sub>v vec_first x m"
  unfolding vec_first_def by auto

lemma elements_mat_mat_of_row[simp]: "elements_mat (mat_of_row v) = vec_set v"
  by (auto simp: mat_of_row_def elements_mat_def vec_set_def)

lemma vec_set_append_vec[simp]: "vec_set (v @\<^sub>v w) = vec_set v \<union> vec_set w"
  by (metis list_of_vec_append set_append set_list_of_vec)

lemma vec_set_vNil[simp]: "set\<^sub>v vNil = {}" using set_list_of_vec by force

lemma diff_smult_distrib_vec: "((x :: 'a::ring) - y) \<cdot>\<^sub>v v = x \<cdot>\<^sub>v v - y \<cdot>\<^sub>v v"
  unfolding smult_vec_def minus_vec_def
  by (rule eq_vecI, auto simp: left_diff_distrib)

lemma add_diff_eq_vec: fixes y :: "'a :: group_add vec"
  shows "y \<in> carrier_vec n \<Longrightarrow> x \<in> carrier_vec n \<Longrightarrow> z \<in> carrier_vec n \<Longrightarrow> y + (x - z) = y + x - z"
  by (intro eq_vecI, auto simp: add_diff_eq)

definition "mat_of_col v = (mat_of_row v)\<^sup>T"

lemma elements_mat_mat_of_col[simp]: "elements_mat (mat_of_col v) = vec_set v"
  unfolding mat_of_col_def by auto

lemma mat_of_col_dim[simp]: "dim_row (mat_of_col v) = dim_vec v"
  "dim_col (mat_of_col v) = 1"
  "mat_of_col v \<in> carrier_mat (dim_vec v) 1"
  unfolding mat_of_col_def by auto

lemma col_mat_of_col[simp]: "col (mat_of_col v) 0 = v"
  unfolding mat_of_col_def by auto


lemma mult_mat_of_col: "A \<in> carrier_mat nr nc \<Longrightarrow> v \<in> carrier_vec nc \<Longrightarrow>
                        A * mat_of_col v = mat_of_col (A *\<^sub>v v)"
  by (intro mat_col_eqI, auto)

lemma mat_mult_append_cols: fixes A :: "'a :: comm_semiring_0 mat"
  assumes A: "A \<in> carrier_mat nr nc1"
    and B: "B \<in> carrier_mat nr nc2"
    and v1: "v1 \<in> carrier_vec nc1"
    and v2: "v2 \<in> carrier_vec nc2"
  shows "(A @\<^sub>c B) *\<^sub>v (v1 @\<^sub>v v2) = A *\<^sub>v v1 + B *\<^sub>v v2"
proof -
  have "(A @\<^sub>c B) *\<^sub>v (v1 @\<^sub>v v2) = (A @\<^sub>c B) *\<^sub>v col (mat_of_col (v1 @\<^sub>v v2)) 0" by auto
  also have "\<dots> = col ((A @\<^sub>c B) * mat_of_col (v1 @\<^sub>v v2)) 0" by auto
  also have "(A @\<^sub>c B) * mat_of_col (v1 @\<^sub>v v2) = ((A @\<^sub>c B) * mat_of_col (v1 @\<^sub>v v2))\<^sup>T\<^sup>T"
    by auto
  also have "((A @\<^sub>c B) * mat_of_col (v1 @\<^sub>v v2))\<^sup>T =
             (mat_of_row (v1 @\<^sub>v v2))\<^sup>T\<^sup>T * (A\<^sup>T @\<^sub>r B\<^sup>T)\<^sup>T\<^sup>T"
    unfolding append_cols_def mat_of_col_def
  proof (rule transpose_mult, force, unfold transpose_carrier_mat, rule mat_of_row_carrier)
    have "A\<^sup>T \<in> carrier_mat nc1 nr" using A by auto
    moreover have "B\<^sup>T \<in> carrier_mat nc2 nr" using B by auto
    ultimately have "A\<^sup>T @\<^sub>r B\<^sup>T \<in> carrier_mat (nc1 + nc2) nr" by auto
    hence "dim_row (A\<^sup>T @\<^sub>r B\<^sup>T) = nc1 + nc2" by auto
    thus "v1 @\<^sub>v v2 \<in> carrier_vec (dim_row (A\<^sup>T @\<^sub>r B\<^sup>T))" using v1 v2 by auto
  qed
  also have "\<dots> = (mat_of_row (v1 @\<^sub>v v2)) * (A\<^sup>T @\<^sub>r B\<^sup>T)" by auto
  also have "\<dots> = mat_of_row v1 * A\<^sup>T + mat_of_row v2 * B\<^sup>T"
    using mat_of_row_mult_append_rows[OF v1 v2] A B by auto
  also have "\<dots>\<^sup>T = (mat_of_row v1 * A\<^sup>T)\<^sup>T + (mat_of_row v2 * B\<^sup>T)\<^sup>T"
    using transpose_add A B by auto
  also have "(mat_of_row v1 * A\<^sup>T)\<^sup>T = A\<^sup>T\<^sup>T * ((mat_of_row v1)\<^sup>T)"
    using transpose_mult A v1 transpose_carrier_mat mat_of_row_carrier(1)
    by metis
  also have "(mat_of_row v2 * B\<^sup>T)\<^sup>T = B\<^sup>T\<^sup>T * ((mat_of_row v2)\<^sup>T)"
    using transpose_mult B v2 transpose_carrier_mat mat_of_row_carrier(1)
    by metis
  also have "A\<^sup>T\<^sup>T * ((mat_of_row v1)\<^sup>T) + B\<^sup>T\<^sup>T * ((mat_of_row v2)\<^sup>T) =
             A * mat_of_col v1 + B * mat_of_col v2"
    unfolding mat_of_col_def by auto
  also have "col \<dots> 0 = col (A * mat_of_col v1) 0 + col (B * mat_of_col v2) 0"
    using assms by auto
  also have "\<dots> = col (mat_of_col (A *\<^sub>v v1)) 0 + col (mat_of_col (B *\<^sub>v v2)) 0"
    using mult_mat_of_col assms by auto
  also have "\<dots> = A *\<^sub>v v1 + B *\<^sub>v v2" by auto
  finally show ?thesis by auto
qed

lemma vec_first_append:
  assumes "v \<in> carrier_vec n"
  shows "vec_first (v @\<^sub>v w) n = v"
proof -
  have "v @\<^sub>v w = vec_first (v @\<^sub>v w) n @\<^sub>v vec_last (v @\<^sub>v w) (dim_vec w)"
    using vec_first_last_append assms by simp
  thus ?thesis using append_vec_eq[OF assms] by simp
qed

lemma vec_le_iff_diff_le_0: fixes a :: "'a :: ordered_ab_group_add vec"
  shows "(a \<le> b) = (a - b \<le> 0\<^sub>v (dim_vec a))"
  unfolding less_eq_vec_def by auto

definition "mat_row_first A n \<equiv> mat n (dim_col A) (\<lambda> (i, j). A $$ (i, j))"

definition "mat_row_last A n \<equiv> mat n (dim_col A) (\<lambda> (i, j). A $$ (dim_row A - n + i, j))"

lemma mat_row_first_carrier[simp]: "mat_row_first A n \<in> carrier_mat n (dim_col A)"
  unfolding mat_row_first_def by simp

lemma mat_row_first_dim[simp]:
  "dim_row (mat_row_first A n) = n"
  "dim_col (mat_row_first A n) = dim_col A"
  unfolding mat_row_first_def by simp_all

lemma mat_row_last_carrier[simp]: "mat_row_last A n \<in> carrier_mat n (dim_col A)"
  unfolding mat_row_last_def by simp

lemma mat_row_last_dim[simp]:
  "dim_row (mat_row_last A n) = n"
  "dim_col (mat_row_last A n) = dim_col A"
  unfolding mat_row_last_def by simp_all

lemma mat_row_first_nth[simp]: "i < n \<Longrightarrow> row (mat_row_first A n) i = row A i"
  unfolding mat_row_first_def row_def by fastforce

lemma append_rows_nth:
  assumes "A \<in> carrier_mat nr1 nc"
    and "B \<in> carrier_mat nr2 nc"
  shows "i < nr1 \<Longrightarrow> row (A @\<^sub>r B) i = row A i"
    and "\<lbrakk> i \<ge> nr1; i < nr1 + nr2 \<rbrakk> \<Longrightarrow> row (A @\<^sub>r B) i = row B (i - nr1)"
  unfolding append_rows_def using row_four_block_mat assms by auto

lemma mat_of_row_last_nth[simp]:
  "i < n \<Longrightarrow> row (mat_row_last A n) i = row A (dim_row A - n + i)"
  unfolding mat_row_last_def row_def by auto

lemma mat_row_first_last_append:
  assumes "dim_row A = m + n"
  shows "(mat_row_first A m) @\<^sub>r (mat_row_last A n) = A"
proof (rule eq_rowI)
  show "dim_row (mat_row_first A m @\<^sub>r mat_row_last A n) = dim_row A"
    unfolding append_rows_def using assms by fastforce
  show "dim_col (mat_row_first A m @\<^sub>r mat_row_last A n) = dim_col A"
    unfolding append_rows_def by fastforce
  fix i
  assume i: "i < dim_row A"
  show "row (mat_row_first A m @\<^sub>r mat_row_last A n) i = row A i"
  proof cases
    assume i: "i < m"
    thus ?thesis using append_rows_nth(1)[OF mat_row_first_carrier[of A m]
          mat_row_last_carrier[of A n] i] by simp
  next
    assume i': "\<not> i < m"
    thus ?thesis using append_rows_nth(2)[OF mat_row_first_carrier[of A m]
          mat_row_last_carrier[of A n]] i assms by simp
  qed
qed

definition "mat_col_first A n \<equiv> (mat_row_first A\<^sup>T n)\<^sup>T"

definition "mat_col_last A n \<equiv> (mat_row_last A\<^sup>T n)\<^sup>T"

lemma mat_col_first_carrier[simp]: "mat_col_first A n \<in> carrier_mat (dim_row A) n"
  unfolding mat_col_first_def by fastforce

lemma mat_col_first_dim[simp]:
  "dim_row (mat_col_first A n) = dim_row A"
  "dim_col (mat_col_first A n) = n"
  unfolding mat_col_first_def by simp_all

lemma mat_col_last_carrier[simp]: "mat_col_last A n \<in> carrier_mat (dim_row A) n"
  unfolding mat_col_last_def by fastforce

lemma mat_col_last_dim[simp]:
  "dim_row (mat_col_last A n) = dim_row A"
  "dim_col (mat_col_last A n) = n"
  unfolding mat_col_last_def by simp_all

lemma mat_col_first_nth[simp]:
  "\<lbrakk> i < n; i < dim_col A \<rbrakk> \<Longrightarrow> col (mat_col_first A n) i = col A i"
  unfolding mat_col_first_def by force

lemma append_cols_nth:
  assumes "A \<in> carrier_mat nr nc1"
    and "B \<in> carrier_mat nr nc2"
  shows "i < nc1 \<Longrightarrow> col (A @\<^sub>c B) i = col A i"
    and "\<lbrakk> i \<ge> nc1; i < nc1 + nc2 \<rbrakk> \<Longrightarrow> col (A @\<^sub>c B) i = col B (i - nc1)"
  unfolding append_cols_def append_rows_def using row_four_block_mat assms
  by auto

lemma mat_of_col_last_nth[simp]:
  "\<lbrakk> i < n; i < dim_col A \<rbrakk> \<Longrightarrow> col (mat_col_last A n) i = col A (dim_col A - n + i)"
  unfolding mat_col_last_def by auto

lemma mat_col_first_last_append:
  assumes "dim_col A = m + n"
  shows "(mat_col_first A m) @\<^sub>c (mat_col_last A n) = A"
  unfolding append_cols_def mat_col_first_def mat_col_last_def
  using mat_row_first_last_append[of "A\<^sup>T"] assms by simp

lemma mat_of_row_dim_row_1: "(dim_row A = 1) = (A = mat_of_row (row A 0))"
proof
  show "dim_row A = 1 \<Longrightarrow> A = mat_of_row (row A 0)" by force
  show "A = mat_of_row (row A 0) \<Longrightarrow> dim_row A = 1" using mat_of_row_dim(1) by metis
qed

lemma mat_of_col_dim_col_1: "(dim_col A = 1) = (A = mat_of_col (col A 0))"
proof
  show "dim_col A = 1 \<Longrightarrow> A = mat_of_col (col A 0)"
    unfolding mat_of_col_def by auto
  show "A = mat_of_col (col A 0) \<Longrightarrow> dim_col A = 1" by (metis mat_of_col_dim(2))
qed

definition vec_of_scal :: "'a \<Rightarrow> 'a vec" where "vec_of_scal x \<equiv> vec 1 (\<lambda> i. x)"

lemma vec_of_scal_dim[simp]:
  "dim_vec (vec_of_scal x) = 1"
  "vec_of_scal x \<in> carrier_vec 1"
  unfolding vec_of_scal_def by auto

lemma index_vec_of_scal[simp]: "(vec_of_scal x) $ 0 = x"
  unfolding vec_of_scal_def by auto

lemma row_mat_of_col[simp]: "i < dim_vec v \<Longrightarrow> row (mat_of_col v) i = vec_of_scal (v $ i)"
  unfolding mat_of_col_def by auto

lemma vec_of_scal_dim_1: "(v \<in> carrier_vec 1) = (v = vec_of_scal (v $ 0))"
  by(standard, auto simp del: One_nat_def, metis vec_of_scal_dim(2))

lemma mult_mat_of_row_vec_of_scal: fixes x :: "'a :: comm_ring_1"
  shows "mat_of_col v *\<^sub>v vec_of_scal x = x \<cdot>\<^sub>v v"
  by (auto simp add: scalar_prod_def)

lemma smult_pos_vec[simp]: fixes l :: "'a :: linordered_ring_strict"
  assumes l: "l > 0"
  shows "(l \<cdot>\<^sub>v v \<le> 0\<^sub>v n) = (v \<le> 0\<^sub>v n)"
proof (cases "dim_vec v = n")
  case True
  have "i < n \<Longrightarrow> ((l \<cdot>\<^sub>v v) $ i \<le> 0) \<longleftrightarrow> v $ i \<le> 0" for i using True
      mult_le_cancel_left_pos[OF l, of _ 0] by simp
  thus ?thesis using True unfolding less_eq_vec_def by auto
qed (auto simp: less_eq_vec_def)

lemma finite_elements_mat[simp]: "finite (elements_mat A)"
  unfolding elements_mat_def by (rule finite_set)

lemma finite_vec_set[simp]: "finite (vec_set A)"
  unfolding vec_set_def by auto

lemma lesseq_vecI: assumes "v \<in> carrier_vec n" "w \<in> carrier_vec n"
  "\<And> i. i < n \<Longrightarrow> v $ i \<le> w $ i"
shows "v \<le> w"
  using assms unfolding less_eq_vec_def by auto

lemma lesseq_vecD: assumes "w \<in> carrier_vec n"
  and "v \<le> w"
  and "i < n"
shows "v $ i \<le> w $ i"
  using assms unfolding less_eq_vec_def by auto

lemma vec_add_mono: fixes a :: "'a :: ordered_ab_semigroup_add vec"
  assumes dim: "dim_vec b = dim_vec d"
    and ab: "a \<le> b"
    and cd: "c \<le> d"
  shows "a + c \<le> b + d"
proof -
  have "\<And> i. i < dim_vec d \<Longrightarrow> (a + c) $ i \<le> (b + d) $ i"
  proof -
    fix i
    assume id: "i < dim_vec d"
    have ic: "i < dim_vec c" using id cd unfolding less_eq_vec_def by auto
    have ib: "i < dim_vec b" using id dim by auto
    have ia: "i < dim_vec a" using ib ab unfolding less_eq_vec_def by auto
    have "a $ i \<le> b $ i" using ab ia ib unfolding less_eq_vec_def by auto
    moreover have "c $ i \<le> d $ i" using cd ic id unfolding less_eq_vec_def by auto
    ultimately have abcdi: "a $ i + c $ i \<le> b $ i + d $ i" using add_mono by auto
    have "(a + c) $ i = a $ i + c $ i" using index_add_vec(1) ic by auto
    also have "\<dots> \<le> b $ i + d $ i" using abcdi by auto
    also have "b $ i + d $ i = (b + d) $ i" using index_add_vec(1) id by auto
    finally show "(a + c) $ i \<le> (b + d) $ i" by auto
  qed
  then show "a + c \<le> b + d" unfolding less_eq_vec_def
    using dim index_add_vec(2) cd less_eq_vec_def by auto
qed

lemma smult_nneg_npos_vec: fixes l :: "'a :: ordered_semiring_0"
  assumes l: "l \<ge> 0"
    and v: "v \<le> 0\<^sub>v n"
  shows "l \<cdot>\<^sub>v v \<le> 0\<^sub>v n"
proof -
  {
    fix i
    assume i: "i < n"
    then have vi: "v $ i \<le> 0" using v unfolding less_eq_vec_def by simp
    then have "(l \<cdot>\<^sub>v v) $ i = l * v $ i" using v i unfolding less_eq_vec_def by auto
    also have "l * v $ i \<le> 0" by (rule mult_nonneg_nonpos[OF l vi])
    finally have "(l \<cdot>\<^sub>v v) $ i \<le> 0" by auto
  }
  then show ?thesis using v unfolding less_eq_vec_def by auto
qed

lemma smult_vec_nonneg_eq: fixes c :: "'a :: field" 
  shows "c \<noteq> 0 \<Longrightarrow> (c \<cdot>\<^sub>v x = c \<cdot>\<^sub>v y) = (x = y)"
proof -
  have "c \<noteq> 0 \<Longrightarrow> c \<cdot>\<^sub>v x = c \<cdot>\<^sub>v y \<Longrightarrow> x = y" 
    by (metis smult_smult_assoc[of "1 / c" "c"] nonzero_divide_eq_eq one_smult_vec)
  thus "c \<noteq> 0 \<Longrightarrow> ?thesis" by auto
qed

lemma distinct_smult_nonneg: fixes c :: "'a :: field"
  assumes c: "c \<noteq> 0"
  shows "distinct lC \<Longrightarrow> distinct (map ((\<cdot>\<^sub>v) c) lC)"
proof (induction lC)
  case (Cons v lC)
  from Cons.prems have "v \<notin> set lC" by fastforce
  hence "c \<cdot>\<^sub>v v \<notin> set (map ((\<cdot>\<^sub>v) c) lC)" using smult_vec_nonneg_eq[OF c] by fastforce
  moreover have "map ((\<cdot>\<^sub>v) c) (v # lC) = c \<cdot>\<^sub>v v # map ((\<cdot>\<^sub>v) c) lC" by simp
  ultimately show ?case using Cons.IH Cons.prems by simp
qed auto

lemma exists_vec_append: "(\<exists> x \<in> carrier_vec (n + m). P x) \<longleftrightarrow> (\<exists> x1 \<in> carrier_vec n. \<exists> x2 \<in> carrier_vec m. P (x1 @\<^sub>v x2))" 
proof
  assume "\<exists>x \<in> carrier_vec (n + m). P x"
  from this obtain x where xcarr: "x \<in> carrier_vec (n+m)" and Px: "P x" by auto
  have "x = vec n (\<lambda> i. x $ i) @\<^sub>v vec m (\<lambda> i. x $ (n + i))" 
    by (rule eq_vecI, insert xcarr, auto)
  hence "P x = P (vec n (\<lambda> i. x $ i) @\<^sub>v vec m (\<lambda> i. x $ (n + i)))" by simp
  also have 1: "\<dots>" using xcarr Px calculation by blast
  finally show "\<exists>x1\<in>carrier_vec n. \<exists>x2\<in>carrier_vec m. P (x1 @\<^sub>v x2)" using 1 vec_carrier by blast
next
  assume "(\<exists> x1 \<in> carrier_vec n. \<exists> x2 \<in> carrier_vec m. P (x1 @\<^sub>v x2))"
  from this obtain x1 x2 where x1: "x1 \<in> carrier_vec n" 
    and x2: "x2 \<in> carrier_vec m" and P12: "P (x1 @\<^sub>v x2)" by auto
  define x where "x = x1 @\<^sub>v x2"
  have xcarr: "x \<in> carrier_vec (n+m)" using x1 x2 by (simp add: x_def)
  have "P x" using P12 xcarr using x_def by blast
  then show "(\<exists> x \<in> carrier_vec (n + m). P x)" using xcarr by auto
qed

end