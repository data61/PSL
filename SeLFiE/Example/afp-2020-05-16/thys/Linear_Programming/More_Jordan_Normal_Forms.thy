theory More_Jordan_Normal_Forms
  imports
    Jordan_Normal_Form.Matrix_Impl
begin

lemma set_comprehension_list_comprehension:
  "set [f i . i <- [x..<a]] = {f i |i. i \<in> {x..<a}}"
  by (simp) (fastforce)

lemma in_second_append_list: "i\<ge> length a \<Longrightarrow> i < length (a@b) \<Longrightarrow> (a@b)!i \<in> set b"
  by (metis diff_add_inverse diff_less_mono in_set_conv_nth leD length_append nth_append)

section \<open> General Theorems used later, that could be moved \<close>

lemma split_four_block_dual_fst_lst:
  assumes "split_block (four_block_mat A B C D) (dim_row A) (dim_col A) = (U, X, Y, V)"
  shows "U = A" "V = D"
proof -
  define nr where nr: "nr = dim_row (four_block_mat A B C D)"
  define nc where nc: "nc = dim_col (four_block_mat A B C D)"
  define nr2 where nr2: "nr2 = nr - dim_row A"
  define nc2 where nc2: "nc2 = nc - dim_col A"
  define A1 where A1: "A1 = mat (dim_row A) (dim_col A) (($$) (four_block_mat A B C D))"
  define A2 where A2: "A2 = mat (dim_row A) nc2 (\<lambda>(i, j). (four_block_mat A B C D) $$ (i, j + dim_col A))"
  define A3 where A3: "A3 = mat nr2 (dim_col A) (\<lambda>(i, j). (four_block_mat A B C D) $$ (i + dim_row A, j))"
  define A4 where A4: "A4 = mat nr2 nc2 (\<lambda>(i, j). (four_block_mat A B C D) $$ (i + dim_row A, j + dim_col A))"
  have g: "split_block (four_block_mat A B C D) (dim_row A) (dim_col A) = (A1, A2, A3, A4)" 
    using split_block_def[of "(four_block_mat A B C D)" "(dim_row A)" "(dim_col A)"]
    by (metis A1 A2 A3 A4 nc nc2 nr nr2)
  have D: "D = A4"
    using A4 by (auto) (standard, (simp add:  nr nr2 nc nc2)+)
  have "A = A1"
    using A1 by auto
  then have "split_block (four_block_mat A B C D) (dim_row A) (dim_col A) = (A, A2, A3, D)"
    using D g by blast
  also show "U = A" 
    using assms calculation by auto
  ultimately show "V = D"
    using assms by auto
qed

lemma append_split_vec_distrib_scalar_prod:
  assumes "dim_vec (u @\<^sub>v w) = dim_vec x" 
  shows "(u @\<^sub>v w) \<bullet> x = u \<bullet> (vec_first x (dim_vec u)) + w \<bullet> (vec_last x (dim_vec w))"
proof -
  have "(u @\<^sub>v w) \<bullet> (vec_first x (dim_vec u) @\<^sub>v vec_last x (dim_vec w)) = 
              u \<bullet> vec_first x (dim_vec u) + w \<bullet> vec_last x (dim_vec w)"
    by (meson carrier_vec_dim_vec scalar_prod_append vec_first_carrier vec_last_carrier)
  then show ?thesis
    by (metis assms carrier_vec_dim_vec index_append_vec(2) vec_first_last_append)
qed

lemma append_dot_product_split:
  assumes "dim_vec (u @\<^sub>v w) = dim_vec x" 
  shows "(u @\<^sub>v w) \<bullet> x = (\<Sum>i\<in>{0..< dim_vec u}. u$i * x$i) + (\<Sum>i\<in>{0..< dim_vec w}. w$i * x$(i + dim_vec u))"
proof -
  define ix where "ix = vec_first x (dim_vec u)"
  define lx where lx: "lx = vec_last x (dim_vec w)"
  have *: "(u @\<^sub>v w) \<bullet> x = u \<bullet> ix + w \<bullet> lx"
    using append_split_vec_distrib_scalar_prod ix_def lx assms by blast
  have "(u @\<^sub>v w) \<bullet> x = (\<Sum> i \<in> {0 ..< dim_vec x}. (u @\<^sub>v w) $ i * x $ i)" 
    using scalar_prod_def[of "(u @\<^sub>v w)" x] by simp
  also have "... = (\<Sum> i \<in> {0 ..< dim_vec u}. (u @\<^sub>v w) $ i * x $ i) + 
                   (\<Sum> i \<in> {dim_vec u ..< dim_vec (u @\<^sub>v w)}. (u @\<^sub>v w) $ i * x $ i)"
    using assms sum.atLeastLessThan_concat[of "0" "dim_vec u" "dim_vec (u @\<^sub>v w)" 
        "(\<lambda>i. (u @\<^sub>v w) $ i * x $ i)", OF le0[of "dim_vec u"]] 
      le_add1[of  "dim_vec u" "dim_vec w"] index_append_vec(2)[of u w] by simp
  also have *: "... =(\<Sum>i\<in>{0..<dim_vec u}. u$i * x$i) + w \<bullet> lx" 
    using * calculation by (auto simp: ix_def scalar_prod_def vec_first_def)
  have "w \<bullet> lx = (\<Sum>i\<in>{0..< dim_vec w}. w$i * x$(i + dim_vec u))" unfolding lx vec_last_def 
    unfolding scalar_prod_def using add_diff_cancel_right' index_append_vec(2)[of u w] by (auto)
      (metis \<open>dim_vec (u @\<^sub>v w) = dim_vec u + dim_vec w\<close> add.commute add_diff_cancel_right' assms)
  then show ?thesis
    using * calculation by auto
qed

lemma assoc_scalar_prod_mult_mat_vec:
  fixes A :: "'a::comm_semiring_1 mat"
  assumes "y \<in> carrier_vec n"
  assumes "x \<in> carrier_vec m"
  assumes "A \<in> carrier_mat n m"
  shows "(A *\<^sub>v x) \<bullet> y = (A\<^sup>T *\<^sub>v y) \<bullet> x"
proof -
  have "(A *\<^sub>v x) \<bullet> y = (\<Sum> i \<in> {0 ..< n}. (A *\<^sub>v x) $ i * y $ i)"
    unfolding scalar_prod_def using assms(1) carrier_vecD by blast
  also have "... = (\<Sum> i \<in> {0 ..< n}. (vec (dim_row A) (\<lambda> i. row A i \<bullet> x)) $ i * y $ i)"
    unfolding mult_mat_vec_def by blast
  also have "... = (\<Sum> i \<in> {0 ..< n}. (\<lambda> i. row A i \<bullet> x)  i * y $ i)"
    using assms(3) by auto
  also have "... = (\<Sum> i \<in> {0 ..< n}. (\<Sum> j \<in> {0 ..< m}. (row A i) $ j * x $ j) * y $ i)"
    unfolding scalar_prod_def using assms(2) carrier_vecD by blast
  also have "... = (\<Sum> j \<in> {0 ..< n}. (\<Sum> i \<in> {0 ..< m}. (row A j) $ i * x $ i * y $ j))"
    by (simp add: sum_distrib_right)
  also have "... = (\<Sum> j \<in> {0 ..< n}. (\<Sum> i \<in> {0 ..< m}.  A $$ (j,i) * x $ i * y $ j))"
    unfolding row_def using assms(3) by auto
  also have "... = (\<Sum> j \<in> {0 ..< n}. (\<Sum> i \<in> {0 ..< m}.  A $$ (j,i) * y $ j * x $ i))"
    by (meson semiring_normalization_rules(16) sum.cong)
  also have "... = (\<Sum> j \<in> {0 ..< n}. (\<Sum> i \<in> {0 ..< m}. (col A i) $ j * y $ j * x $ i))"
    using assms(3) by auto
  also have "... = (\<Sum> i \<in> {0 ..< m}. (\<Sum> j \<in> {0 ..< n}. (col A i) $ j * y $ j * x $ i))"
    using Groups_Big.comm_monoid_add_class.sum.swap[of 
        "(\<lambda>i j. (col A i) $ j * y $ j * x $ i)" "{0..<n}" "{0 ..< m}", symmetric]
    by simp
  also have "... = (\<Sum> i \<in> {0 ..< m}. (\<Sum> j \<in> {0 ..< n}. (col A i) $ j * y $ j) * x $ i)"
    by (simp add: sum_distrib_right)
  also have "... = (\<Sum> i \<in> {0 ..< m}. (\<lambda> i. col A i \<bullet> y) i * x $ i)"
    unfolding scalar_prod_def using assms(1) carrier_vecD by blast
  also have "... = (\<Sum> i \<in> {0 ..< m}. (\<lambda> i. row A\<^sup>T i \<bullet> y) i * x $ i)"
    using assms(3) by auto
  also have "... = (\<Sum> i \<in> {0 ..< m}. (vec (dim_row A\<^sup>T) (\<lambda> i. row A\<^sup>T i \<bullet> y)) $ i * x $ i)"
    using assms by auto
  also have "... = (\<Sum> i \<in> {0 ..< m}. (A\<^sup>T *\<^sub>v y) $ i * x $ i)"
    using assms by auto
  also have "... = (A\<^sup>T *\<^sub>v y) \<bullet> x"
    using scalar_prod_def[of "(A\<^sup>T *\<^sub>v y)" x,symmetric] using assms(2) carrier_vecD by blast
  finally show ?thesis .
qed


section \<open> Vectors \<close>

abbreviation singletonV ("[_]\<^sub>v" ) where "singletonV e \<equiv> (vec 1 (\<lambda>i. e))"

lemma elem_in_singleton [simp]: "[a]\<^sub>v $ 0 = a"
  by simp

lemma elem_in_singleton_append [simp]: "(x @\<^sub>v [a]\<^sub>v) $ dim_vec x = a"
  by simp

lemma vector_cases_append:
  fixes x :: "'a vec"
  shows "x = vNil \<or> (\<exists>v a. x = v @\<^sub>v [a]\<^sub>v)"
proof -
  have "x \<noteq> vNil \<Longrightarrow> (\<exists>v a. x = v @\<^sub>v [a]\<^sub>v)"
  proof (rule ccontr)
    assume a1: "x \<noteq> vNil"
    assume na: "\<not> (\<exists>v a. x = v @\<^sub>v [a]\<^sub>v)"
    have "dim_vec x \<ge> 1"
      using a1 eq_vecI by auto
    define v where v: "v = vec (dim_vec x - 1) (\<lambda>i. x $ i)"
    have v': "\<forall>i < dim_vec v. v $ i = x $ i" 
      using v by auto
    define a where a: "a = x $ (dim_vec x - 1)"
    have a': "[a]\<^sub>v $ 0 = a" by simp
    have ff1: "1 + dim_vec v = dim_vec x"
      by (metis (no_types) \<open>1 \<le> dim_vec x\<close> add_diff_cancel_left' dim_vec le_Suc_ex v)
    have "\<forall>i < dim_vec x. x$i = (v @\<^sub>v [a]\<^sub>v)$i" 
    proof (standard,standard)
      fix i :: nat
      assume as: "i < dim_vec x"
      have "x $ dim_vec v = a"
        by (simp add: a v)
      then have "x $ i = (v @\<^sub>v [a]\<^sub>v) $ i"
        using ff1 as by (metis (no_types) One_nat_def a' add.left_neutral 
            add_Suc_right add_diff_cancel_left' add_diff_cancel_right' 
            dim_vec index_append_vec(1) less_Suc_eq v')
      then show "x$i = (v @\<^sub>v [a]\<^sub>v)$i"
        by blast
    qed
    then have "x = v @\<^sub>v [a]\<^sub>v"
      using a a' v v'
      by (metis dim_vec eq_vecI ff1 index_append_vec(2) semiring_normalization_rules(24))
    then show False using na by auto
  qed
  then show ?thesis
    by blast
qed

lemma vec_rev_induct [case_names vNil append, induct type: vec]:
  assumes "P vNil" and "\<And>a v. P v \<Longrightarrow> P (v @\<^sub>v [a]\<^sub>v)"
  shows "P v"
proof (induction "dim_vec v" arbitrary: v)
  case 0
  then have "v = vNil"
    by auto
  then show ?case
    using assms(1) by auto
next
  case (Suc l)
  obtain xs x where xs_x: "v = xs @\<^sub>v [x]\<^sub>v"
    using vector_cases_append[of v] Suc.hyps(2) dim_vec by (auto)
  have "l = dim_vec xs"
    using Suc.hyps(2) xs_x by auto
  then have "P xs"
    using Suc.hyps(1)[of xs] by auto
  then have "P (xs @\<^sub>v [x]\<^sub>v)" 
    using assms(2)[of xs x] by auto
  then show ?case
    by (simp add: xs_x)
qed

lemma singleton_append_dotP:
  assumes "dim_vec z = dim_vec y + 1"
  shows "(y @\<^sub>v [x]\<^sub>v) \<bullet> z = (\<Sum>i\<in>{0..<dim_vec y}. y $ i * z $ i) + x * z $ dim_vec y"
proof -
  have "(y @\<^sub>v [x]\<^sub>v) \<bullet> z = (\<Sum>i\<in>{0..<dim_vec z}. (y @\<^sub>v [x]\<^sub>v) $ i * z $ i)"
    unfolding scalar_prod_def by blast
  also have "... = (\<Sum>i\<in>{0..<dim_vec z-1}. (y @\<^sub>v [x]\<^sub>v) $ i * z $ i) + 
                   (y @\<^sub>v [x]\<^sub>v)$(dim_vec z-1) * z$(dim_vec z-1)"
    by (simp add: assms)
  also have "... = (\<Sum>i\<in>{0..<dim_vec y}. (y @\<^sub>v [x]\<^sub>v) $ i * z $ i) + 
                   (y @\<^sub>v [x]\<^sub>v)$(dim_vec y)* z$(dim_vec y)"
    using assms by auto
  also have "... = (\<Sum>i\<in>{0..<dim_vec y}. y $ i * z $ i) + 
                   x * z$(dim_vec y)"
    by simp
  finally show ?thesis .
qed

lemma map_vec_append: "map_vec f (a @\<^sub>v b) = map_vec f a @\<^sub>v map_vec f b"
  by (induction a arbitrary: b) (auto)

lemma map_mat_map_vec:
  assumes "i < dim_row P"
  shows "row (map_mat f P) i = map_vec f (row P i)"
  using assms by auto

lemma append_rows_access1 [simp]:
  assumes "i < dim_row A"
  assumes "dim_col A = dim_col B"
  shows "row (A @\<^sub>r B) i = row A i"
proof 
  show "dim_vec (Matrix.row (A @\<^sub>r B) i) = dim_vec (Matrix.row A i)"
    by (simp add: append_rows_def)
  fix ia
  assume "ia < dim_vec (row A i)" 
  have "row (A @\<^sub>r B) i = (row A i @\<^sub>v row (0\<^sub>m (dim_row A) 0) i)"
    unfolding append_rows_def using 
      carrier_mat_triv[of A] row_four_block_mat(1)[of A "dim_row A" 
        _ "0\<^sub>m (dim_row A) 0" 0 B "dim_row B" "0\<^sub>m (dim_row B) 0" i, OF _ _ _ _ assms(1)]
    by (metis assms(2) carrier_mat_triv zero_carrier_mat)
  also have "... = row A i @\<^sub>v vNil"
    by (simp add: assms(1))
  also have "... = row A i"
    by auto
  finally show "row (A @\<^sub>r B) i $ ia = row A i $ ia"
    by auto
qed

lemma append_rows_access2 [simp]:
  assumes "i \<ge> dim_row A"
  assumes "i < dim_row A + dim_row B"
  assumes "dim_col A = dim_col B"
  shows "row (A @\<^sub>r B) i = row B (i - dim_row A)"
proof 
  show "dim_vec (row (A @\<^sub>r B) i) = dim_vec (row B (i - dim_row A))"
    by (simp add: append_rows_def assms(3))
  fix ia
  assume "ia < dim_vec (row B (i - dim_row A))" 
  have "row (A @\<^sub>r B) i = (row B (i - dim_row A) @\<^sub>v row (0\<^sub>m (dim_row B) 0) (i - dim_row A))"
    unfolding append_rows_def using carrier_mat_triv[of A] row_four_block_mat(2)[of A "dim_row A" 
        _ "0\<^sub>m (dim_row A) 0" 0 B "dim_row B" "0\<^sub>m (dim_row B) 0" i, OF _ _ _ _ _ assms(2)]
    by (metis assms(1) assms(3) carrier_mat_triv le_antisym less_imp_le_nat nat_less_le zero_carrier_mat)
  also have "... = row B (i - dim_row A) @\<^sub>v vNil"
    by fastforce
  also have "... = row B (i - dim_row A)"
    by auto
  finally show "row (A @\<^sub>r B) i $ ia = row B (i - dim_row A) $ ia"
    by auto
qed

lemma append_singleton_access [simp]: "(Matrix.vec n f @\<^sub>v [r]\<^sub>v) $ n = r"
  by simp

text \<open> Move to right place \<close>

fun mat_append_col where
  "mat_append_col A b = mat_of_cols (dim_row A) (cols A @ [b])"

fun mat_append_row where
  "mat_append_row A c = mat_of_rows (dim_col A) (rows A @ [c])"


lemma mat_append_col_dims:
  shows "mat_append_col A b \<in> carrier_mat (dim_row A) (dim_col A + 1)"
  by auto

lemma mat_append_row_dims:
  shows "mat_append_row A c \<in> carrier_mat (dim_row A + 1) (dim_col A)"
  by auto

lemma mat_append_col_col:
  assumes "dim_row A = dim_vec b" 
  shows "col (mat_append_col A b) (dim_col A) = b" 
proof (standard)
  let ?nA = "(mat_of_cols (dim_row A) (cols A @ [b]))"
  show "dim_vec (col (mat_append_col A b) (dim_col A)) = dim_vec b"
    by (simp add: assms)
  fix i
  assume "i < dim_vec b"
  have "col (mat_append_col A b) (dim_col A) $ i = vec_index (vec (dim_row ?nA) (\<lambda> i. ?nA $$ (i, (dim_col A)))) i"
    by (simp add: col_def)
  also have "... = vec_index (vec (dim_row A) (\<lambda> i. ?nA $$ (i, (dim_col A)))) i" 
    by auto
  also have "... = vec_index ((cols A @ [b]) ! dim_col A) i"
    by (simp add: \<open>i < dim_vec b\<close> assms mat_of_cols_index)
  also have "... = vec_index b i"
    by (metis cols_length nth_append_length)
  finally show "col (mat_append_col A b) (dim_col A) $ i = b $ i" .
qed

lemma mat_append_col_vec_index:
  assumes "i < dim_row A"
    and "dim_row A = dim_vec b"
  shows "(row (mat_append_col A b) i) $ (dim_col A) = b $ i"
  using mat_append_col_col 
  by (metis (no_types, lifting) One_nat_def add_Suc_right assms(1) assms(2) carrier_matD(2) 
      col_def dim_row_mat(1) index_row(1) index_vec lessI mat_append_col.simps 
      mat_append_col_dims mat_of_cols_def semiring_norm(51))

lemma mat_append_row_row:
  assumes "dim_col A = dim_vec c" 
  shows "row (mat_append_row A c) (dim_row A) = c"
proof
  let ?nA = "(mat_of_rows (dim_col A) (Matrix.rows A @ [c]))"
  show "dim_vec (Matrix.row (mat_append_row A c) (dim_row A)) = dim_vec c"
    using assms by simp
  fix i assume "i < dim_vec c"
  from mat_append_row.simps[of A c] 
  have "row (mat_append_row A c) (dim_row A) $ i = vec_index (row ?nA (dim_row A)) i"
    by auto
  also have "... = vec_index (vec (dim_col ?nA) (\<lambda> j. ?nA $$ (dim_row A,j))) i"
    by (simp add: Matrix.row_def)
  also have "... =  vec_index ((rows A @ [c]) ! dim_row A) i"
    by (metis (mono_tags, lifting) \<open>mat_append_row A c = mat_of_rows (dim_col A) (Matrix.rows A @ [c])\<close> 
        add_Suc_right append_Nil2 assms calculation carrier_matD(1) col_transpose cols_transpose 
        index_transpose_mat(2) index_transpose_mat(3) length_append length_rows lessI list.size(3) 
        mat_append_col.elims mat_append_col_col mat_append_row_dims nth_append_length 
        transpose_mat_of_rows One_nat_def)
  also have "... = vec_index c i"
    by (metis length_rows nth_append_length)
  finally show "Matrix.row (mat_append_row A c) (dim_row A) $ i = c $ i" .
qed

lemma mat_append_row_in_mat:
  assumes "i < dim_row A"
  shows "row (mat_append_row A r) i = row A i"
  by (auto) (metis assms le_imp_less_Suc length_append_singleton 
      length_rows mat_of_rows_row nat_less_le nth_append nth_rows row_carrier)

lemma mat_append_row_vec_index:
  assumes "i < dim_col A"
    and "dim_col A = dim_vec b"
  shows "vec_index (col (mat_append_row A b) i) (dim_row A) = vec_index b i"
  by (metis One_nat_def add.right_neutral add_Suc_right assms(1) assms(2) carrier_matD(1) 
      carrier_matD(2) index_col index_row(1) lessI mat_append_row_dims mat_append_row_row)

lemma mat_append_col_access_in_mat:
  assumes "dim_row A = dim_vec b"
   and "i < dim_row A"
    and "j < dim_col A"
  shows "(row (mat_append_col A b) i) $ j = (row A i) $ j"
  using Matrix.row_transpose[of j A, OF assms(3)]
    Matrix.transpose_transpose[of "(mat_append_col A b)"] assms carrier_matD(1) 
    carrier_matD(2) cols_length cols_transpose index_col index_row(1)[of i "mat_append_col A b" j] index_transpose_mat(2)
    mat_append_col.simps mat_append_col_dims
    mat_of_cols_carrier(3) mat_of_rows_row
    nth_append nth_rows row_carrier trans_less_add1 transpose_mat_of_cols
    mat_of_cols_index
  by (smt cols_nth index_row(1))


lemma constructing_append_col_row: 
  assumes "i < dim_row A"
    and "dim_row A = dim_vec b"
  shows "row (mat_append_col A b) i = row A i @\<^sub>v [vec_index b i]\<^sub>v"
proof
  show 1: "dim_vec (Matrix.row (mat_append_col A b) i) = dim_vec (Matrix.row A i @\<^sub>v [b $ i]\<^sub>v)"
    by simp
  fix ia
  assume a: "ia < dim_vec (Matrix.row A i @\<^sub>v [b $ i]\<^sub>v)"
  consider "ia = dim_col A" | "ia < dim_col A"     
     using a less_SucE by auto
  then show "row (mat_append_col A b) i $ ia = (Matrix.row A i @\<^sub>v [b $ i]\<^sub>v) $ ia "
  proof (cases)
    case 1
    then show ?thesis 
      using mat_append_col_vec_index[of i A b, OF assms] by auto
  next
    case 2
    have "row (mat_append_col A b) i $ ia = (mat_append_col A b) $$ (i, ia)"
      using a assms(1) by auto
    then show ?thesis using mat_append_col_access_in_mat[of A b i ia, OF assms(2) assms(1) 2]
      using "2" by auto
  qed
qed

definition one_element_vec where "one_element_vec n e = vec n (\<lambda>i. e)"

lemma one_element_vec_carrier: "one_element_vec n e \<in> carrier_vec n"
  unfolding one_element_vec_def by auto

lemma one_element_vec_dim [simp]: "dim_vec (one_element_vec n (r::rat)) = n"
  by (simp add: one_element_vec_def)

lemma one_element_vec_access [simp]: "\<And>i. i < n \<Longrightarrow> vec_index (one_element_vec n e) i = e"
  unfolding one_element_vec_def by (auto)


fun single_nz_val where "single_nz_val n i v = vec n (\<lambda>j. (if i = j then v else 0))"

lemma single_nz_val_carrier: "single_nz_val n i v \<in> carrier_vec n"
   by auto

lemma single_nz_val_access1 [simp]: "i < n \<Longrightarrow> single_nz_val n i v $ i = v"
   by auto

lemma single_nz_val_access2 [simp]: "i < n \<Longrightarrow> j < n \<Longrightarrow> i \<noteq> j\<Longrightarrow> single_nz_val n i v $ j = 0"
   by (auto)

lemma "i < n \<Longrightarrow> (v \<cdot>\<^sub>v unit_vec n i) $ i = (v::'a::{monoid_mult,times,zero_neq_one})"
  by(auto)

lemma single_nz_val_unit_vec: 
  fixes v::"'a::{monoid_mult,times,zero_neq_one,mult_zero}"
  shows "v \<cdot>\<^sub>v (unit_vec n i) = single_nz_val n i v" 
proof 
  show *: "dim_vec (v \<cdot>\<^sub>v unit_vec n i) = dim_vec (single_nz_val n i v)"
    by (simp)
  fix ia
  assume "ia < dim_vec (single_nz_val n i v)"
  then show "(v \<cdot>\<^sub>v unit_vec n i) $ ia = single_nz_val n i v $ ia"
    using * by (simp add: unit_vec_def)
qed

lemma single_nz_valI [intro]:
  fixes v i val
  assumes "\<And>j. j < dim_vec v \<Longrightarrow> j \<noteq> i \<Longrightarrow> v$j = 0"
  assumes "v$i = val"
  shows "v = single_nz_val (dim_vec v) i val"
  using assms(1) assms(2) by auto

lemma single_nz_val_dotP:
  assumes "i < n"
  assumes "dim_vec x = n"
  shows "single_nz_val n i v \<bullet> x = v * x $ i"
proof -
  let ?y = "single_nz_val n i v"
  have "single_nz_val n i v \<bullet> x = (\<Sum>i\<in>{0 ..< dim_vec x}. ?y $ i * x $ i)"
    unfolding scalar_prod_def by auto
  also have "... = (\<Sum>i\<in>{0 ..< dim_vec x}-{i}. ?y $ i * x $ i) + ?y $ i * x $ i"
    by (metis (no_types, lifting) add.commute assms(1) assms(2) atLeast0LessThan 
        finite_atLeastLessThan lessThan_iff sum.remove)
  also have "... = (\<Sum>i\<in>{0 ..< dim_vec x}-{i}. ?y $ i * x $ i) + v * x $ i"
    by (simp add: assms(1))
  also have "... = v * x $ i"
  proof -
    have "\<And>j. j \<in> {0 ..< dim_vec x}-{i} \<Longrightarrow> ?y $ j * x $ j = 0"
      by (simp add: assms(2))
    then have "(\<Sum>i\<in>{0 ..< dim_vec x}-{i}. ?y $ i * x $ i) = 0" by auto
    then show ?thesis by auto
  qed
  finally show ?thesis .
qed

lemma single_nz_zero_singleton: "single_nz_val 1 0 v = [v]\<^sub>v"
  by (auto)

lemma append_one_elem_zero_dotP:
  assumes "dim_vec u = m" 
    and "dim_vec x = n"
  shows "(one_element_vec n e @\<^sub>v (0\<^sub>v m)) \<bullet> (x @\<^sub>v u) = (\<Sum>i\<in>{0 ..< dim_vec x}. e * x $ i)"
proof -
  let ?OEV = "one_element_vec n e"
  have "dim_vec (?OEV @\<^sub>v (0\<^sub>v m)) = dim_vec (x @\<^sub>v u)"
    by (simp add: assms(1) assms(2) one_element_vec_carrier)
  have "(one_element_vec n e @\<^sub>v 0\<^sub>v m) \<bullet> (x @\<^sub>v u) = one_element_vec n e \<bullet> x + 0\<^sub>v m \<bullet> u"
    using scalar_prod_append[of ?OEV _ "0\<^sub>v m" _ x u] assms
    by (meson carrier_vec_dim_vec one_element_vec_carrier zero_carrier_vec)
  also have "... = (\<Sum>i\<in>{0..<dim_vec x}. ?OEV $ i * x $ i) + (\<Sum>i\<in>{0..<dim_vec u}. (0\<^sub>v m)$i * u$i)"
    unfolding scalar_prod_def by blast
  also have "... = (\<Sum>i\<in>{0..<dim_vec x}. ?OEV $ i * x $ i)"
    using assms(1) by auto
  also have "... = (\<Sum>i\<in>{0..<dim_vec x}. e * x $ i)"
    using assms(2) by auto
  finally show ?thesis .
qed

lemma one_element_vec_dotP:
  assumes "dim_vec x = n"
  shows "(one_element_vec n e) \<bullet> x = (\<Sum>i\<in>{0 ..< dim_vec x}. e * x $ i)"
  by (metis (no_types, lifting) assms one_element_vec_access scalar_prod_def sum.ivl_cong)


lemma singleton_dotP [simp]: "dim_vec x = 1 \<Longrightarrow> [v]\<^sub>v \<bullet> x = v * x$0"
  by (metis dim_vec index_vec less_one single_nz_valI single_nz_val_dotP)

lemma singletons_dotP [simp]: "[v]\<^sub>v \<bullet> [w]\<^sub>v = v * w"
  by (metis dim_vec index_vec less_one singleton_dotP)

lemma singleton_appends_dotP [simp]: "dim_vec x = dim_vec y \<Longrightarrow> (x @\<^sub>v [v]\<^sub>v) \<bullet> (y @\<^sub>v [w]\<^sub>v) = x \<bullet> y + v * w"
  using scalar_prod_append[of x "dim_vec x" "[v]\<^sub>v" 1 y "[w]\<^sub>v"]
  by (metis carrier_dim_vec singletons_dotP vec_carrier)


end