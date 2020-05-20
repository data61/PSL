(*  
    Title:      Gauss_Jordan_IArrays.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Gauss Jordan algorithm over nested IArrays\<close>

theory Gauss_Jordan_IArrays
imports
  Matrix_To_IArray
  Gauss_Jordan
begin

subsection\<open>Definitions and functions to compute the Gauss-Jordan algorithm over matrices represented as nested iarrays\<close>

definition "least_non_zero_position_of_vector_from_index A i = the (List.find (\<lambda>x. A !! x \<noteq> 0) [i..<IArray.length A])"
definition "least_non_zero_position_of_vector A = least_non_zero_position_of_vector_from_index A 0"

definition vector_all_zero_from_index :: "(nat \<times> 'a::{zero} iarray) => bool"
  where "vector_all_zero_from_index A' = (let i=fst A'; A=(snd A') in IArray.all (\<lambda>x. A!!x = 0) (IArray [i..<(IArray.length A)]))"

definition Gauss_Jordan_in_ij_iarrays :: "'a::{field} iarray iarray => nat => nat => 'a iarray iarray "
  where "Gauss_Jordan_in_ij_iarrays A i j = (let n = least_non_zero_position_of_vector_from_index (column_iarray j A) i;
  interchange_A = interchange_rows_iarray A i n; 
  A' = mult_row_iarray interchange_A i (1/interchange_A!!i!!j) 
  in IArray.of_fun (\<lambda>s. if s = i then A' !! s else row_add_iarray A' s i (- interchange_A !! s !! j) !! s) (nrows_iarray A))"

definition Gauss_Jordan_column_k_iarrays :: "(nat \<times> 'a::{field} iarray iarray) => nat => (nat \<times> 'a iarray iarray)"
  where "Gauss_Jordan_column_k_iarrays A' k=(let A=(snd A'); i=(fst A') in 
  if ((vector_all_zero_from_index (i, (column_iarray k A)))) \<or> i = (nrows_iarray A) then (i,A) else (Suc i, (Gauss_Jordan_in_ij_iarrays A i k)))"

definition Gauss_Jordan_upt_k_iarrays :: "'a::{field} iarray iarray => nat => 'a::{field} iarray iarray"
  where "Gauss_Jordan_upt_k_iarrays A k = snd (foldl Gauss_Jordan_column_k_iarrays (0,A) [0..<Suc k])"

definition Gauss_Jordan_iarrays :: "'a::{field} iarray iarray => 'a::{field} iarray iarray"
  where "Gauss_Jordan_iarrays A = Gauss_Jordan_upt_k_iarrays A (ncols_iarray A - 1)"


subsection\<open>Proving the equivalence between Gauss-Jordan algorithm over nested iarrays and over nested vecs (abstract matrices).\<close>

lemma vector_all_zero_from_index_eq:
fixes A::"'a::{zero}^'n::{mod_type}"
shows "(\<forall>m\<ge>i. A $ m = 0) = (vector_all_zero_from_index (to_nat i, vec_to_iarray A))"
proof (auto simp add: vector_all_zero_from_index_def Let_def Option.is_none_def find_None_iff)
  fix x
  assume zero: "\<forall>m\<ge>i. A $ m = 0"
    and x_length: "x<length (IArray.list_of (vec_to_iarray A))" and i_le_x: "to_nat i \<le> x"
  have x_le_card: "x < CARD('n)"  using x_length unfolding vec_to_iarray_def by auto
  have i_le_from_nat_x: "i \<le> from_nat x"  using from_nat_mono'[OF i_le_x x_le_card] unfolding from_nat_to_nat_id .
  hence Axk: "A $ (from_nat x) = 0" using zero by simp
  have "vec_to_iarray A !! x = vec_to_iarray A !! to_nat (from_nat x::'n)" unfolding to_nat_from_nat_id[OF x_le_card] ..
  also have "... = A $ (from_nat x)" unfolding vec_to_iarray_nth' ..
  also have "... = 0" unfolding Axk ..
  finally show" IArray.list_of (vec_to_iarray A) ! x = 0"
    unfolding IArray.sub_def .
next
  fix m::'n
  assume zero_assm: "\<forall>x\<in>{mod_type_class.to_nat i..<length (IArray.list_of (vec_to_iarray A))}. IArray.list_of (vec_to_iarray A) ! x = 0"
   and i_le_m: "i \<le> m"
  have zero: "\<forall>x<length (IArray.list_of (vec_to_iarray A)). mod_type_class.to_nat i \<le> x \<longrightarrow> IArray.list_of (vec_to_iarray A) ! x = 0"
    using zero_assm by auto
  have to_nat_i_le_m:"to_nat i \<le> to_nat m" using to_nat_mono'[OF i_le_m] .
  have m_le_length: "to_nat m < IArray.length (vec_to_iarray A)" unfolding vec_to_iarray_def using to_nat_less_card by auto
  have "A $ m = vec_to_iarray A !! (to_nat m)" unfolding vec_to_iarray_nth' ..
  also have "... = 0" using zero to_nat_i_le_m m_le_length unfolding nrows_iarray_def by (metis IArray.sub_def IArray.length_def)
  finally show "A $ m = 0" .
qed

lemma matrix_vector_all_zero_from_index:
  fixes A::"'a::{zero}^'columns::{mod_type}^'rows::{mod_type}"
  shows "(\<forall>m\<ge>i. A $ m $ k = 0) = (vector_all_zero_from_index (to_nat i, vec_to_iarray (column k A)))"
  unfolding vector_all_zero_from_index_eq[symmetric] column_def by simp


lemma vec_to_iarray_least_non_zero_position_of_vector_from_index:
fixes A::"'a::{zero}^'n::{mod_type}"
assumes not_all_zero: "\<not> (vector_all_zero_from_index (to_nat i,  vec_to_iarray A))"
shows "least_non_zero_position_of_vector_from_index (vec_to_iarray A) (to_nat i) = to_nat (LEAST n. A $ n \<noteq> 0 \<and> i \<le> n)"
proof -
  have "\<exists>a. List.find (\<lambda>x. vec_to_iarray A !! x \<noteq> 0) [to_nat i..<IArray.length (vec_to_iarray A)] = Some a"
    proof (rule ccontr, simp, unfold IArray.sub_def[symmetric] IArray.length_def[symmetric])
      assume "List.find (\<lambda>x. (vec_to_iarray A) !! x \<noteq> 0) [to_nat i..<IArray.length (vec_to_iarray A)] = None"
      hence "\<not> (\<exists>x. x \<in> set [mod_type_class.to_nat i..<IArray.length (vec_to_iarray A)] \<and> vec_to_iarray A !! x \<noteq> 0)" 
        unfolding find_None_iff .
      thus False using not_all_zero unfolding vector_all_zero_from_index_eq[symmetric]
      by (simp del: IArray.length_def IArray.sub_def, unfold length_vec_to_iarray, metis to_nat_less_card to_nat_mono' vec_to_iarray_nth')
     qed
  from this obtain a where a: "List.find (\<lambda>x. vec_to_iarray A !! x \<noteq> 0) [to_nat i..<IArray.length (vec_to_iarray A)] = Some a"
    by blast
  from this obtain ia where 
    ia_less_length: "ia<length [to_nat i..<IArray.length (vec_to_iarray A)]" and
    not_eq_zero: "vec_to_iarray A !! ([to_nat i..<IArray.length (vec_to_iarray A)] ! ia) \<noteq> 0" and
    a_eq: "a = [to_nat i..<IArray.length (vec_to_iarray A)] ! ia"
    and least: "(\<forall>ja<ia. \<not> vec_to_iarray A !! ([to_nat i..<IArray.length (vec_to_iarray A)] ! ja) \<noteq> 0)" 
    unfolding find_Some_iff by blast  
  have not_eq_zero': "vec_to_iarray A !! a \<noteq> 0" using not_eq_zero unfolding a_eq .
  have i_less_a: "to_nat i \<le> a" using  ia_less_length length_upt nth_upt a_eq by auto
  have a_less_card: "a<CARD('n)" using a_eq ia_less_length unfolding vec_to_iarray_def by auto
  have "(LEAST n. A $ n \<noteq> 0 \<and> i \<le> n) = from_nat a"
  proof (rule Least_equality, rule conjI)
    show "A $ from_nat a \<noteq> 0"  unfolding vec_to_iarray_nth'[symmetric] using not_eq_zero' unfolding to_nat_from_nat_id[OF a_less_card] .
    show "i \<le> from_nat a" using a_less_card from_nat_mono' from_nat_to_nat_id i_less_a by fastforce
    fix x assume "A $ x  \<noteq> 0 \<and> i \<le> x" hence Axj: "A $ x \<noteq> 0" and i_le_x: "i \<le> x" by fast+   
    show "from_nat a \<le> x"
    proof (rule ccontr)
      assume "\<not> from_nat a \<le> x" hence x_less_from_nat_a: "x < from_nat a" by simp
      define ja where "ja = (to_nat x) - (to_nat i)"
      have to_nat_x_less_card: "to_nat x < CARD ('n)" using bij_to_nat[where ?'a='n] unfolding bij_betw_def by fastforce
      hence ja_less_length: "ja < IArray.length (vec_to_iarray A)" unfolding ja_def vec_to_iarray_def by auto
      have "[to_nat i..<IArray.length (vec_to_iarray A)] ! ja = to_nat i + ja" 
      by (rule nth_upt, unfold vec_to_iarray_def,auto, metis add_diff_inverse diff_add_zero ja_def not_less_iff_gr_or_eq to_nat_less_card)
      also have i_plus_ja: "... = to_nat x" unfolding ja_def by (simp add: i_le_x to_nat_mono')
      finally have list_rw: "[to_nat i..<IArray.length (vec_to_iarray A)] ! ja = to_nat x" .
      moreover have "ja<ia"
      proof -
        have "a = to_nat i + ia" unfolding a_eq 
          by (rule nth_upt, metis ia_less_length length_upt less_diff_conv add.commute)
        thus ?thesis by (metis i_plus_ja add_less_cancel_right add.commute to_nat_le x_less_from_nat_a)
      qed
      ultimately have "vec_to_iarray A !! (to_nat x) = 0" using least by auto
      hence "A $ x = 0" unfolding vec_to_iarray_nth' .  
      thus False using Axj by contradiction
    qed
  qed
  hence "a = to_nat (LEAST n. A $ n \<noteq> 0 \<and> i \<le> n)" using to_nat_from_nat_id[OF a_less_card] by simp
  thus ?thesis unfolding least_non_zero_position_of_vector_from_index_def unfolding a by simp
qed


corollary vec_to_iarray_least_non_zero_position_of_vector_from_index':
fixes A::"'a::{zero}^'cols::{mod_type}^'rows::{mod_type}"
assumes not_all_zero: "\<not> (vector_all_zero_from_index (to_nat i, vec_to_iarray (column j A)))"
shows "least_non_zero_position_of_vector_from_index (vec_to_iarray (column j A)) (to_nat i) = to_nat (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)"
unfolding vec_to_iarray_least_non_zero_position_of_vector_from_index[OF not_all_zero]
unfolding column_def by fastforce

corollary vec_to_iarray_least_non_zero_position_of_vector_from_index'':
fixes A::"'a::{zero}^'cols::{mod_type}^'rows::{mod_type}"
assumes not_all_zero: "\<not> (vector_all_zero_from_index (to_nat j, vec_to_iarray (row i A)))"
shows "least_non_zero_position_of_vector_from_index (vec_to_iarray (row i A)) (to_nat j) = to_nat (LEAST n. A $ i $ n \<noteq> 0 \<and> j \<le> n)"
unfolding vec_to_iarray_least_non_zero_position_of_vector_from_index[OF not_all_zero]
unfolding row_def by fastforce


lemma matrix_to_iarray_Gauss_Jordan_in_ij[code_unfold]:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}"
  assumes not_all_zero: "\<not> (vector_all_zero_from_index (to_nat i, vec_to_iarray (column j A)))"
  shows "matrix_to_iarray (Gauss_Jordan_in_ij A i j) = Gauss_Jordan_in_ij_iarrays (matrix_to_iarray A) (to_nat i) (to_nat j)"
proof (unfold Gauss_Jordan_in_ij_def Gauss_Jordan_in_ij_iarrays_def Let_def, rule matrix_to_iarray_eq_of_fun, auto simp del: IArray.sub_def IArray.length_def)
  show "vec_to_iarray (mult_row (interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)) i (1 / A $ (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ j) $ i) =
    mult_row_iarray
     (interchange_rows_iarray (matrix_to_iarray A) (to_nat i)
       (least_non_zero_position_of_vector_from_index (column_iarray (to_nat j) (matrix_to_iarray A)) (to_nat i)))
     (to_nat i) (1 / interchange_rows_iarray (matrix_to_iarray A) (to_nat i)
           (least_non_zero_position_of_vector_from_index (column_iarray (to_nat j) (matrix_to_iarray A)) (to_nat i)) !! to_nat i !! to_nat j) !! to_nat i" 
    unfolding vec_to_iarray_column[symmetric]
    unfolding vec_to_iarray_least_non_zero_position_of_vector_from_index'[OF not_all_zero]
    unfolding matrix_to_iarray_interchange_rows[symmetric]
    unfolding matrix_to_iarray_mult_row[symmetric] 
    unfolding matrix_to_iarray_nth
    unfolding interchange_rows_i
    unfolding vec_matrix ..
next
  fix ia
  show "vec_to_iarray
          (row_add (mult_row (interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)) i (1 / A $ (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ j)) ia i
            (- interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ ia $ j) $ ia) =
         row_add_iarray
          (mult_row_iarray
            (interchange_rows_iarray (matrix_to_iarray A) (to_nat i)
              (least_non_zero_position_of_vector_from_index (column_iarray (to_nat j) (matrix_to_iarray A)) (to_nat i)))
            (to_nat i)
            (1 / interchange_rows_iarray (matrix_to_iarray A) (to_nat i)
                  (least_non_zero_position_of_vector_from_index (column_iarray (to_nat j) (matrix_to_iarray A)) (to_nat i)) !!
                 to_nat i !! to_nat j))
          (to_nat ia) (to_nat i)
          (- interchange_rows_iarray (matrix_to_iarray A) (to_nat i)
              (least_non_zero_position_of_vector_from_index (column_iarray (to_nat j) (matrix_to_iarray A)) (to_nat i)) !!
             to_nat ia !! to_nat j) !! to_nat ia"
    unfolding vec_to_iarray_column[symmetric]
    unfolding vec_to_iarray_least_non_zero_position_of_vector_from_index'[OF not_all_zero]
    unfolding matrix_to_iarray_interchange_rows[symmetric]
    unfolding matrix_to_iarray_mult_row[symmetric]
    unfolding matrix_to_iarray_nth
    unfolding interchange_rows_i
    unfolding matrix_to_iarray_row_add[symmetric]
    unfolding vec_matrix ..
next
  show "nrows_iarray (matrix_to_iarray A) =
    IArray.length (matrix_to_iarray
    (\<chi> s. if s = i then mult_row (interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)) i (1 / interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ i $ j) $ s
    else row_add (mult_row (interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)) i (1 / interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ i $ j)) s i
    (- interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ s $ j) $ s))" 
    unfolding length_eq_card_rows nrows_eq_card_rows ..
qed



lemma matrix_to_iarray_Gauss_Jordan_column_k_1:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}"
  assumes k: "k<ncols A"
  and i: "i\<le>nrows A"
  shows "(fst (Gauss_Jordan_column_k (i, A) k)) = fst (Gauss_Jordan_column_k_iarrays (i, matrix_to_iarray A) k)"
proof (cases "i<nrows A")
  case True
  show ?thesis
    unfolding Gauss_Jordan_column_k_def Let_def Gauss_Jordan_column_k_iarrays_def fst_conv snd_conv
    unfolding vec_to_iarray_column[of "from_nat k" A, unfolded to_nat_from_nat_id[OF k[unfolded ncols_def]], symmetric]
    using matrix_vector_all_zero_from_index[symmetric, of "from_nat i::'rows" "from_nat k::'columns"]
    unfolding to_nat_from_nat_id[OF True[unfolded nrows_def]] to_nat_from_nat_id[OF k[unfolded ncols_def]]
    using matrix_to_iarray_Gauss_Jordan_in_ij    
    unfolding matrix_to_iarray_nrows snd_conv by auto
next
  case False
  have "vector_all_zero_from_index (nrows A, column_iarray k (matrix_to_iarray A))" unfolding vector_all_zero_from_index_def unfolding Let_def  snd_conv fst_conv
  unfolding nrows_def column_iarray_def
  unfolding length_eq_card_rows by (simp add: is_none_code(1))
  thus ?thesis
    using i False
    unfolding Gauss_Jordan_column_k_iarrays_def Gauss_Jordan_column_k_def Let_def by auto
qed

lemma matrix_to_iarray_Gauss_Jordan_column_k_2:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}"
  assumes k: "k<ncols A"
  and i: "i\<le>nrows A"
  shows "matrix_to_iarray (snd (Gauss_Jordan_column_k (i, A) k)) = snd (Gauss_Jordan_column_k_iarrays (i, matrix_to_iarray A) k)"
proof (cases "i<nrows A")
  case True show ?thesis
    unfolding Gauss_Jordan_column_k_def Let_def Gauss_Jordan_column_k_iarrays_def fst_conv snd_conv
    unfolding vec_to_iarray_column[of "from_nat k" A, unfolded to_nat_from_nat_id[OF k[unfolded ncols_def]], symmetric]
    unfolding matrix_vector_all_zero_from_index[symmetric, of "from_nat i::'rows" "from_nat k::'columns", symmetric]
    using matrix_to_iarray_Gauss_Jordan_in_ij[of "from_nat i::'rows" "from_nat k::'columns"]    
    unfolding to_nat_from_nat_id[OF True[unfolded nrows_def]] to_nat_from_nat_id[OF k[unfolded ncols_def]]
    unfolding matrix_to_iarray_nrows by auto
next
  case False show ?thesis
    using assms False unfolding Gauss_Jordan_column_k_def Let_def Gauss_Jordan_column_k_iarrays_def
    by (auto simp add: matrix_to_iarray_nrows)  
qed


text\<open>Due to the assumptions presented in @{thm "matrix_to_iarray_Gauss_Jordan_column_k_2"}, the following lemma must have three shows.
The proof style is similar to @{thm "rref_and_index_Gauss_Jordan_upt_k"}.\<close>

lemma foldl_Gauss_Jordan_column_k_eq:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}"
  assumes k: "k<ncols A"
  shows matrix_to_iarray_Gauss_Jordan_upt_k[code_unfold]: "matrix_to_iarray (Gauss_Jordan_upt_k A k) = Gauss_Jordan_upt_k_iarrays (matrix_to_iarray A) k"
  and fst_foldl_Gauss_Jordan_column_k_eq: "fst (foldl Gauss_Jordan_column_k_iarrays (0, matrix_to_iarray A) [0..<Suc k]) = fst (foldl Gauss_Jordan_column_k (0, A) [0..<Suc k])"
  and fst_foldl_Gauss_Jordan_column_k_less: "fst (foldl Gauss_Jordan_column_k (0, A) [0..<Suc k]) \<le> nrows A"
  using assms
proof (induct k)
  show "matrix_to_iarray (Gauss_Jordan_upt_k A 0) = Gauss_Jordan_upt_k_iarrays (matrix_to_iarray A) 0"
    unfolding Gauss_Jordan_upt_k_def Gauss_Jordan_upt_k_iarrays_def  by (auto, metis k le0 less_nat_zero_code matrix_to_iarray_Gauss_Jordan_column_k_2 neq0_conv) 
  show "fst (foldl Gauss_Jordan_column_k_iarrays (0, matrix_to_iarray A) [0..<Suc 0]) = fst (foldl Gauss_Jordan_column_k (0, A) [0..<Suc 0])"
    unfolding Gauss_Jordan_upt_k_def Gauss_Jordan_upt_k_iarrays_def by (auto, metis gr_implies_not0 k le0 matrix_to_iarray_Gauss_Jordan_column_k_1 neq0_conv) 
  show "fst (foldl Gauss_Jordan_column_k (0, A) [0..<Suc 0]) \<le> nrows A" unfolding Gauss_Jordan_upt_k_def by (simp add: Gauss_Jordan_column_k_def Let_def size1 nrows_def)
next
  fix k
  assume "(k < ncols A \<Longrightarrow> matrix_to_iarray (Gauss_Jordan_upt_k A k) = Gauss_Jordan_upt_k_iarrays (matrix_to_iarray A) k)" and
    "(k < ncols A \<Longrightarrow> fst (foldl Gauss_Jordan_column_k_iarrays (0, matrix_to_iarray A) [0..<Suc k]) = fst (foldl Gauss_Jordan_column_k (0, A) [0..<Suc k]))"
    and "(k < ncols A \<Longrightarrow> fst (foldl Gauss_Jordan_column_k (0, A) [0..<Suc k]) \<le> nrows A)"
    and Suc_k_less_card: "Suc k < ncols A"
  hence hyp1: "matrix_to_iarray (Gauss_Jordan_upt_k A k) = Gauss_Jordan_upt_k_iarrays (matrix_to_iarray A) k"
    and hyp2: "fst (foldl Gauss_Jordan_column_k_iarrays (0, matrix_to_iarray A) [0..<Suc k]) = fst (foldl Gauss_Jordan_column_k (0, A) [0..<Suc k])"
    and hyp3: "fst (foldl Gauss_Jordan_column_k (0, A) [0..<Suc k]) \<le> nrows A"
    by auto
  hence hyp1_unfolded: "matrix_to_iarray (snd (foldl Gauss_Jordan_column_k (0, A) [0..<Suc k])) = snd (foldl Gauss_Jordan_column_k_iarrays (0, matrix_to_iarray A) [0..<Suc k])" 
    using hyp1 unfolding Gauss_Jordan_upt_k_def Gauss_Jordan_upt_k_iarrays_def by simp
  have upt_rw: "[0..<Suc (Suc k)] = [0..<Suc k] @ [(Suc k)]" by auto
  have fold_rw: "(foldl Gauss_Jordan_column_k_iarrays (0, matrix_to_iarray A) [0..<Suc k]) 
    = (fst (foldl Gauss_Jordan_column_k_iarrays (0, matrix_to_iarray A) [0..<Suc k]), snd (foldl Gauss_Jordan_column_k_iarrays (0, matrix_to_iarray A) [0..<Suc k]))"
    by simp
  have fold_rw': "(foldl Gauss_Jordan_column_k (0, A) [0..<(Suc k)]) 
    = (fst (foldl Gauss_Jordan_column_k (0, A) [0..<(Suc k)]), snd (foldl Gauss_Jordan_column_k (0, A) [0..<(Suc k)]))" by simp
  show "fst (foldl Gauss_Jordan_column_k_iarrays (0, matrix_to_iarray A) [0..<Suc (Suc k)]) = fst (foldl Gauss_Jordan_column_k (0, A) [0..<Suc (Suc k)])"
    unfolding upt_rw foldl_append unfolding List.foldl.simps apply (subst fold_rw) apply (subst fold_rw') unfolding hyp2 unfolding hyp1_unfolded[symmetric]
  proof (rule matrix_to_iarray_Gauss_Jordan_column_k_1[symmetric, of "Suc k" "(snd (foldl Gauss_Jordan_column_k (0, A) [0..<Suc k]))"])
    show "Suc k < ncols (snd (foldl Gauss_Jordan_column_k (0, A) [0..<Suc k]))"  using Suc_k_less_card unfolding ncols_def .
    show " fst (foldl Gauss_Jordan_column_k (0, A) [0..<Suc k]) \<le> nrows (snd (foldl Gauss_Jordan_column_k (0, A) [0..<Suc k]))" using hyp3 unfolding nrows_def .
  qed
  show "matrix_to_iarray (Gauss_Jordan_upt_k A (Suc k)) = Gauss_Jordan_upt_k_iarrays (matrix_to_iarray A) (Suc k)"
    unfolding Gauss_Jordan_upt_k_def Gauss_Jordan_upt_k_iarrays_def  upt_rw foldl_append  List.foldl.simps
    apply (subst fold_rw) apply (subst fold_rw') unfolding hyp2 hyp1_unfolded[symmetric]
  proof (rule matrix_to_iarray_Gauss_Jordan_column_k_2, unfold ncols_def nrows_def)
    show "Suc k < CARD('columns)" using Suc_k_less_card unfolding ncols_def .
    show "fst (foldl Gauss_Jordan_column_k (0, A) [0..<Suc k]) \<le> CARD('rows)" using hyp3 unfolding nrows_def .
  qed
  show "fst (foldl Gauss_Jordan_column_k (0, A) [0..<Suc (Suc k)]) \<le> nrows A"
    using [[unfold_abs_def = false]]
    unfolding upt_rw foldl_append unfolding List.foldl.simps apply (subst fold_rw')
    unfolding Gauss_Jordan_column_k_def Let_def
    using hyp3 le_antisym not_less_eq_eq unfolding nrows_def by fastforce
qed



lemma matrix_to_iarray_Gauss_Jordan[code_unfold]:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}"
  shows "matrix_to_iarray (Gauss_Jordan A) = Gauss_Jordan_iarrays (matrix_to_iarray A)"
  unfolding Gauss_Jordan_iarrays_def ncols_iarray_def unfolding length_eq_card_columns
  by (auto simp add: Gauss_Jordan_def matrix_to_iarray_Gauss_Jordan_upt_k ncols_def)



subsection\<open>Implementation over IArrays of the computation of the @{term "rank"} of a matrix\<close>

definition rank_iarray :: "'a::{field} iarray iarray => nat"
  where "rank_iarray A = (let A' = (Gauss_Jordan_iarrays A); nrows = (IArray.length A') in card {i. i<nrows \<and> \<not> is_zero_iarray (A' !! i)})"

subsubsection\<open>Proving the equivalence between @{term "rank"} and @{term "rank_iarray"}.\<close>

text\<open>First of all, some code equations are removed to allow the execution of Gauss-Jordan algorithm using iarrays\<close>
lemmas card'_code(2)[code del]
lemmas rank_Gauss_Jordan_code[code del]


lemma rank_eq_card_iarrays:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}"
  shows "rank A = card {vec_to_iarray (row i (Gauss_Jordan A)) |i. \<not> is_zero_iarray (vec_to_iarray (row i (Gauss_Jordan A)))}"
proof (unfold rank_Gauss_Jordan_eq Let_def, rule bij_betw_same_card[of "vec_to_iarray"], auto simp add: bij_betw_def)
  show "inj_on vec_to_iarray {row i (Gauss_Jordan A) |i. row i (Gauss_Jordan A) \<noteq> 0}" using inj_vec_to_iarray unfolding inj_on_def by blast
  fix i assume r: "row i (Gauss_Jordan A) \<noteq> 0"
  show "\<exists>ia. vec_to_iarray (row i (Gauss_Jordan A)) = vec_to_iarray (row ia (Gauss_Jordan A)) \<and> \<not> is_zero_iarray (vec_to_iarray (row ia (Gauss_Jordan A)))"
  proof (rule exI[of _ i], simp)
    show "\<not> is_zero_iarray (vec_to_iarray (row i (Gauss_Jordan A)))" using r unfolding is_zero_iarray_eq_iff .
  qed
next
  fix i
  assume not_zero_iarray: "\<not> is_zero_iarray (vec_to_iarray (row i (Gauss_Jordan A)))"
  show "vec_to_iarray (row i (Gauss_Jordan A)) \<in> vec_to_iarray ` {row i (Gauss_Jordan A) |i. row i (Gauss_Jordan A) \<noteq> 0}"
    by (rule imageI, auto simp add: not_zero_iarray  is_zero_iarray_eq_iff)
qed


lemma rank_eq_card_iarrays':
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}"
  shows "rank A = (let A' = (Gauss_Jordan_iarrays (matrix_to_iarray A)) in card {row_iarray (to_nat i) A' |i::'rows. \<not> is_zero_iarray (A' !! (to_nat i))})"
  unfolding Let_def unfolding rank_eq_card_iarrays vec_to_iarray_row'  matrix_to_iarray_Gauss_Jordan row_iarray_def ..

lemma rank_eq_card_iarrays_code:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}"
  shows "rank A = (let A' = (Gauss_Jordan_iarrays (matrix_to_iarray A)) in card {i::'rows. \<not> is_zero_iarray (A' !! (to_nat i))})" 
proof (unfold rank_eq_card_iarrays' Let_def, rule bij_betw_same_card[symmetric, of "\<lambda>i. row_iarray (to_nat i) (Gauss_Jordan_iarrays (matrix_to_iarray A))"],
    unfold bij_betw_def inj_on_def, auto, unfold IArray.sub_def[symmetric]) 
  fix x y::'rows
  assume x: "\<not> is_zero_iarray (Gauss_Jordan_iarrays (matrix_to_iarray A) !! to_nat x)"
    and y: "\<not> is_zero_iarray (Gauss_Jordan_iarrays (matrix_to_iarray A) !! to_nat y)"
    and eq: "row_iarray (to_nat x) (Gauss_Jordan_iarrays (matrix_to_iarray A)) = row_iarray (to_nat y) (Gauss_Jordan_iarrays (matrix_to_iarray A))"
  have eq': "(Gauss_Jordan A) $ x = (Gauss_Jordan A) $ y" by (metis eq matrix_to_iarray_Gauss_Jordan row_iarray_def vec_matrix vec_to_iarray_morph)
  hence not_zero_x: "\<not> is_zero_row x (Gauss_Jordan A)" and not_zero_y: "\<not> is_zero_row y (Gauss_Jordan A)"
    by (metis  is_zero_iarray_eq_iff is_zero_row_def' matrix_to_iarray_Gauss_Jordan vec_eq_iff vec_matrix x zero_index)+
  hence x_in: "row x (Gauss_Jordan A) \<in> {row i (Gauss_Jordan A) |i::'rows. row i (Gauss_Jordan A) \<noteq> 0}"
    and y_in: "row y (Gauss_Jordan A) \<in> {row i (Gauss_Jordan A) |i::'rows. row i (Gauss_Jordan A) \<noteq> 0}"
    by (metis (lifting, mono_tags) is_zero_iarray_eq_iff matrix_to_iarray_Gauss_Jordan mem_Collect_eq vec_to_iarray_row' x y)+
  show "x = y" using inj_index_independent_rows[OF _ x_in eq'] rref_Gauss_Jordan by fast
qed

subsubsection\<open>Code equations for computing the rank over nested iarrays and the dimensions of the elementary subspaces\<close>

lemma rank_iarrays_code[code]:
  "rank_iarray A = length (filter (\<lambda>x. \<not> is_zero_iarray x) (IArray.list_of (Gauss_Jordan_iarrays A)))"
proof -
  obtain xs where A_eq_xs: "(Gauss_Jordan_iarrays A) = IArray xs" by (metis iarray.exhaust)
  have "rank_iarray A = card {i. i<(IArray.length (Gauss_Jordan_iarrays A)) \<and> \<not> is_zero_iarray ((Gauss_Jordan_iarrays A) !! i)}" unfolding rank_iarray_def Let_def ..
  also have "... = length (filter (\<lambda>x. \<not> is_zero_iarray x) (IArray.list_of (Gauss_Jordan_iarrays A)))"
    unfolding A_eq_xs using length_filter_conv_card[symmetric] by force
  finally show ?thesis .
qed

lemma matrix_to_iarray_rank[code_unfold]:
  shows "rank A = rank_iarray (matrix_to_iarray A)"
  unfolding rank_eq_card_iarrays_code rank_iarray_def Let_def
  apply (rule bij_betw_same_card[of "to_nat"])
  unfolding bij_betw_def
  apply auto
  unfolding IArray.length_def[symmetric] IArray.sub_def[symmetric] apply (metis inj_onI to_nat_eq)
  unfolding  matrix_to_iarray_Gauss_Jordan[symmetric] length_eq_card_rows
  using bij_to_nat[where ?'a='c] unfolding bij_betw_def by auto

lemma dim_null_space_iarray[code_unfold]:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}"
  shows "vec.dim (null_space A) = ncols_iarray (matrix_to_iarray A) - rank_iarray (matrix_to_iarray A)"
  unfolding dim_null_space ncols_eq_card_columns matrix_to_iarray_rank dimension_vector by simp

lemma dim_col_space_iarray[code_unfold]:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}"
  shows "vec.dim (col_space A) = rank_iarray (matrix_to_iarray A)"
  unfolding rank_eq_dim_col_space[of A, symmetric]  matrix_to_iarray_rank ..

lemma dim_row_space_iarray[code_unfold]:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}"
  shows "vec.dim (row_space A) = rank_iarray (matrix_to_iarray A)" 
  unfolding row_rank_def[symmetric] rank_def[symmetric] matrix_to_iarray_rank ..

lemma dim_left_null_space_space_iarray[code_unfold]:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}"
  shows "vec.dim (left_null_space A) = nrows_iarray (matrix_to_iarray A) - rank_iarray (matrix_to_iarray A)"
  unfolding dim_left_null_space nrows_eq_card_rows matrix_to_iarray_rank dimension_vector by auto

end
