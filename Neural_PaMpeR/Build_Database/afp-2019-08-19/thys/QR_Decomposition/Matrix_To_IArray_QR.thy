(*  
    Title:      Matrix_To_IArray_QR.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Matrices as nested IArrays\<close>

theory Matrix_To_IArray_QR
imports 
  Rank_Nullity_Theorem.Mod_Type
  Gauss_Jordan.Elementary_Operations
  IArray_Addenda_QR
begin

text\<open>The file is similar to the \<open>Matrix_To_IArray.thy\<close> one, presented in the Gauss-Jordan
algorithm. But now, some proofs have changed slightly because of the new instantiations presented
in the file \<open>IArray_Addenda_QR.thy\<close>.\<close>

subsection\<open>Isomorphism between matrices implemented by vecs and matrices implemented by iarrays\<close>

subsubsection\<open>Isomorphism between vec and iarray\<close>

definition vec_to_iarray :: "'a^'n::{mod_type} \<Rightarrow> 'a iarray"
  where "vec_to_iarray A = IArray.of_fun (\<lambda>i. A $ (from_nat i)) (CARD('n))"

definition iarray_to_vec :: "'a iarray \<Rightarrow> 'a^'n::{mod_type}"
  where "iarray_to_vec A = (\<chi> i. A !! (to_nat i))"

  (*
  definition iarray_to_vec_option :: "'a iarray \<Rightarrow> ('a^'n::{mod_type}) option"
  where "iarray_to_vec_option A = (if (IArray.length A) = CARD('n)
  then Some (\<chi> i::'n. A!!(to_nat i)) 
  else None)"
  *)

lemma vec_to_iarray_nth:
  fixes A::"'a^'n::{finite, mod_type}"
  assumes i: "i<CARD('n)"
  shows "(vec_to_iarray A) !! i = A $ (from_nat i)"
  unfolding vec_to_iarray_def using of_fun_nth[OF i] .

lemma vec_to_iarray_nth':
  fixes A::"'a^'n::{mod_type}"
  shows "(vec_to_iarray A) !! (to_nat i) = A $ i"
proof -
  have to_nat_less_card: "to_nat i<CARD('n)"
    using bij_to_nat[where ?'a='n] unfolding bij_betw_def by fastforce
  show ?thesis
    unfolding vec_to_iarray_def unfolding of_fun_nth[OF to_nat_less_card] from_nat_to_nat_id ..
qed

lemma iarray_to_vec_nth:
  shows "(iarray_to_vec A) $ i = A !! (to_nat i)"
  unfolding iarray_to_vec_def by simp

lemma vec_to_iarray_morph:
  fixes A::"'a^'n::{mod_type}"
  shows "(A = B) = (vec_to_iarray A = vec_to_iarray B)"
  by (metis vec_eq_iff vec_to_iarray_nth')

lemma inj_vec_to_iarray:
  shows "inj vec_to_iarray"
  using vec_to_iarray_morph unfolding inj_on_def by blast


lemma iarray_to_vec_vec_to_iarray:
  fixes A::"'a^'n::{mod_type}"
  shows "iarray_to_vec (vec_to_iarray A)=A"
proof (unfold vec_to_iarray_def iarray_to_vec_def, vector, auto)
  fix i::'n
  have "to_nat i<CARD('n)" using bij_to_nat[where ?'a='n] unfolding bij_betw_def by auto
  thus "map (\<lambda>i. A $ from_nat i) [0..<CARD('n)] ! to_nat i = A $ i" by simp
qed

lemma vec_to_iarray_iarray_to_vec:
  assumes length_eq: "IArray.length A = CARD('n::{mod_type})"
  shows "vec_to_iarray (iarray_to_vec A::'a^'n::{mod_type}) = A"
proof (unfold vec_to_iarray_def iarray_to_vec_def, vector, auto)
  obtain xs where xs: "A = IArray xs" by (metis iarray.exhaust)
  show "IArray (map (\<lambda>i. IArray.list_of A ! to_nat (from_nat i::'n)) [0..<CARD('n)]) = A"
  proof(unfold xs iarray.inject list_eq_iff_nth_eq, auto)
    show "CARD('n) = length xs" using length_eq unfolding xs by simp
    fix i assume i: "i < CARD('n)"
    show "xs ! to_nat (from_nat i::'n) = xs ! i" unfolding to_nat_from_nat_id[OF i] ..
  qed
qed

lemma length_vec_to_iarray:
  fixes xa::"'a^'n::{mod_type}"
  shows "IArray.length (vec_to_iarray xa) = CARD('n)"
  unfolding vec_to_iarray_def by simp

subsubsection\<open>Isomorphism between matrix and nested iarrays\<close>

definition matrix_to_iarray :: "'a^'n::{mod_type}^'m::{mod_type} => 'a iarray iarray"
  where "matrix_to_iarray A = IArray (map (vec_to_iarray \<circ> (($) A) \<circ> (from_nat::nat=>'m)) [0..<CARD('m)])"

definition iarray_to_matrix :: "'a iarray iarray \<Rightarrow> 'a^'n::{mod_type}^'m::{mod_type}"
  where "iarray_to_matrix A = (\<chi> i j. A !! (to_nat i) !! (to_nat j))"

lemma matrix_to_iarray_morph:
  fixes A::"'a^'n::{mod_type}^'m::{mod_type}"
  shows "(A = B) = (matrix_to_iarray A = matrix_to_iarray B)"
  unfolding matrix_to_iarray_def apply simp
  unfolding forall_from_nat_rw[of "\<lambda>x. vec_to_iarray (A $ x) = vec_to_iarray (B $ x)"]
  by (metis from_nat_to_nat_id vec_eq_iff vec_to_iarray_morph)

lemma matrix_to_iarray_eq_of_fun:
  fixes A::"'a^'columns::{mod_type}^'rows::{mod_type}"
  assumes vec_eq_f: "\<forall>i. vec_to_iarray (A $ i) = f (to_nat i)"
  and n_eq_length: "n=IArray.length (matrix_to_iarray A)"
  shows "matrix_to_iarray A = IArray.of_fun f n"
proof (unfold IArray.of_fun_def matrix_to_iarray_def iarray.inject list_eq_iff_nth_eq, auto)
  show *: "CARD('rows) = n" using n_eq_length unfolding matrix_to_iarray_def by auto
  fix i assume i: "i < CARD('rows)"
  hence i_less_n: "i<n" using * i by simp
  show "vec_to_iarray (A $ from_nat i) = map f [0..<n] ! i"
    using vec_eq_f  using i_less_n
    by (simp, unfold to_nat_from_nat_id[OF i], simp)
qed

lemma map_vec_to_iarray_rw[simp]: 
  fixes A::"'a^'columns::{mod_type}^'rows::{mod_type}"
  shows "map (\<lambda>x. vec_to_iarray (A $ from_nat x)) [0..<CARD('rows)] ! to_nat i = vec_to_iarray (A $ i)"
proof -
  have i_less_card: "to_nat i < CARD('rows)"
    using bij_to_nat[where ?'a='rows] unfolding bij_betw_def by fastforce
  hence "map (\<lambda>x. vec_to_iarray (A $ from_nat x)) [0..<CARD('rows)] ! to_nat i 
    = vec_to_iarray (A $ from_nat (to_nat i))" by simp
  also have "... =  vec_to_iarray (A $ i)" unfolding from_nat_to_nat_id ..
  finally show ?thesis .
qed


lemma matrix_to_iarray_nth:
  "matrix_to_iarray A !! to_nat i !! to_nat j = A $ i $ j" 
  unfolding matrix_to_iarray_def o_def using vec_to_iarray_nth' by auto

lemma vec_matrix: "vec_to_iarray (A$i) = (matrix_to_iarray A) !! (to_nat i)"
  unfolding matrix_to_iarray_def o_def by fastforce

lemma iarray_to_matrix_matrix_to_iarray:
  fixes A::"'a^'columns::{mod_type}^'rows::{mod_type}"
  shows "iarray_to_matrix (matrix_to_iarray A) = A"
  unfolding matrix_to_iarray_def iarray_to_matrix_def o_def  
  by (vector, auto, metis IArray.sub_def vec_to_iarray_nth')


subsection\<open>Definition of operations over matrices implemented by iarrays\<close>

definition mult_iarray :: "'a::{times} iarray => 'a => 'a iarray"
  where "mult_iarray A q = IArray.of_fun (\<lambda>n. q * A!!n) (IArray.length A)"

definition row_iarray :: "nat => 'a iarray iarray => 'a iarray"
  where "row_iarray k A = A !! k"

definition column_iarray :: "nat => 'a iarray iarray  => 'a iarray"
  where "column_iarray k A = IArray.of_fun (\<lambda>m. A !! m !! k) (IArray.length A)"

definition nrows_iarray :: "'a iarray iarray => nat"
  where "nrows_iarray A = IArray.length A"

definition ncols_iarray :: "'a iarray iarray => nat"
  where "ncols_iarray A = IArray.length (A!!0)"

definition "rows_iarray A = {row_iarray i A | i. i \<in> {..<nrows_iarray A}}"
definition "columns_iarray A = {column_iarray i A | i. i \<in> {..<ncols_iarray A}}"

definition tabulate2 :: "nat => nat => (nat => nat => 'a) => 'a iarray iarray"
  where "tabulate2 m n f = IArray.of_fun (\<lambda>i. IArray.of_fun (f i) n) m"

definition transpose_iarray :: "'a iarray iarray => 'a iarray iarray"
  where "transpose_iarray A =  tabulate2 (ncols_iarray A) (nrows_iarray A) (\<lambda>a b. A!!b!!a)"

definition matrix_matrix_mult_iarray :: "'a::{times, comm_monoid_add} iarray iarray => 'a iarray iarray => 'a iarray iarray"  (infixl "**i" 70)
  where "A **i B = tabulate2 (nrows_iarray A) (ncols_iarray B) (\<lambda>i j. sum (\<lambda>k. ((A!!i)!!k) * ((B!!k)!!j)) {0..<ncols_iarray A})"

definition matrix_vector_mult_iarray :: "'a::{semiring_1} iarray iarray => 'a iarray => 'a iarray" (infixl "*iv" 70)
  where "A *iv x = IArray.of_fun (\<lambda>i. sum (\<lambda>j. ((A!!i)!!j) * (x!!j)) {0..<IArray.length x}) (nrows_iarray A)"

definition vector_matrix_mult_iarray :: "'a::{semiring_1} iarray => 'a iarray iarray => 'a iarray" (infixl "v*i" 70)
  where "x v*i A = IArray.of_fun (\<lambda>j. sum (\<lambda>i. ((A!!i)!!j) * (x!!i)) {0..<IArray.length x}) (ncols_iarray A)"

definition mat_iarray :: "'a::{zero} => nat => 'a iarray iarray"
  where "mat_iarray k n = tabulate2 n n (\<lambda> i j. if i = j then k else 0)"

definition is_zero_iarray :: "'a::{zero} iarray \<Rightarrow> bool"
  where "is_zero_iarray A = IArray_Addenda_QR.all (\<lambda>i. A !! i = 0) (IArray[0..<IArray.length A])"

subsubsection\<open>Properties of previous definitions\<close>
lemma is_zero_iarray_eq_iff:
  fixes A::"'a::{zero}^'n::{mod_type}"
  shows "(A = 0) = (is_zero_iarray (vec_to_iarray A))"
proof (auto)
  show "is_zero_iarray (vec_to_iarray 0)" by (simp add: vec_to_iarray_def is_zero_iarray_def Option.is_none_def find_None_iff)
  show "is_zero_iarray (vec_to_iarray A) \<Longrightarrow> A = 0"
  proof (simp add: vec_to_iarray_def is_zero_iarray_def Option.is_none_def find_None_iff vec_eq_iff, clarify)
    fix i::'n
    assume "\<forall>i\<in>{0..<CARD('n)}. A $ mod_type_class.from_nat i = 0"
    hence eq_zero: "\<forall>x<CARD('n). A $ from_nat x = 0" by force
    have "to_nat i<CARD('n)" using bij_to_nat[where ?'a='n] unfolding bij_betw_def by fastforce
    hence "A $ (from_nat (to_nat i)) = 0" using eq_zero by blast   
    thus "A $ i = 0" unfolding from_nat_to_nat_id .
  qed
qed

lemma mult_iarray_works:
  assumes "a<IArray.length A" shows "mult_iarray A q !! a = q * A!!a"
  unfolding mult_iarray_def
  unfolding IArray.of_fun_def unfolding sub_def
  using assms by simp

lemma length_eq_card_rows:
  fixes A::"'a^'columns::{mod_type}^'rows::{mod_type}"
  shows "IArray.length (matrix_to_iarray A) = CARD('rows)"
  unfolding matrix_to_iarray_def by auto

lemma nrows_eq_card_rows:
  fixes A::"'a^'columns::{mod_type}^'rows::{mod_type}"
  shows "nrows_iarray (matrix_to_iarray A) = CARD('rows)"
  unfolding nrows_iarray_def length_eq_card_rows ..

lemma length_eq_card_columns:
  fixes A::"'a^'columns::{mod_type}^'rows::{mod_type}"
  shows "IArray.length (matrix_to_iarray A !! 0) = CARD ('columns)"
  unfolding matrix_to_iarray_def o_def vec_to_iarray_def by simp

lemma ncols_eq_card_columns:
  fixes A::"'a^'columns::{mod_type}^'rows::{mod_type}"
  shows "ncols_iarray (matrix_to_iarray A) = CARD('columns)"
  unfolding ncols_iarray_def length_eq_card_columns ..

lemma matrix_to_iarray_nrows:
  fixes A::"'a^'columns::{mod_type}^'rows::{mod_type}"
  shows "nrows A = nrows_iarray (matrix_to_iarray A)"
  unfolding nrows_def nrows_eq_card_rows ..

lemma matrix_to_iarray_ncols:
  fixes A::"'a^'columns::{mod_type}^'rows::{mod_type}"
  shows "ncols A = ncols_iarray (matrix_to_iarray A)"
  unfolding ncols_def ncols_eq_card_columns ..

lemma vec_to_iarray_row[code_unfold]: "vec_to_iarray (row i A) = row_iarray (to_nat i) (matrix_to_iarray A)"
  unfolding row_def row_iarray_def vec_to_iarray_def
  by (auto, metis IArray.sub_def IArray.of_fun_def vec_matrix vec_to_iarray_def)

lemma vec_to_iarray_row': "vec_to_iarray (row i A) = (matrix_to_iarray A) !! (to_nat i)"
  unfolding row_def vec_to_iarray_def
  by (auto, metis IArray.sub_def IArray.of_fun_def vec_matrix vec_to_iarray_def)

lemma vec_to_iarray_column[code_unfold]: "vec_to_iarray (column i A) = column_iarray (to_nat i) (matrix_to_iarray A)"
  unfolding column_def vec_to_iarray_def column_iarray_def length_eq_card_rows
  by (auto, metis IArray.sub_def from_nat_not_eq vec_matrix vec_to_iarray_nth')

lemma vec_to_iarray_column':
  assumes k: "k<ncols A"
  shows "(vec_to_iarray (column (from_nat k) A)) = (column_iarray k (matrix_to_iarray A))"
  unfolding vec_to_iarray_column unfolding to_nat_from_nat_id[OF k[unfolded ncols_def]] ..

lemma column_iarray_nth:
  assumes i: "i<nrows_iarray A"
  shows "column_iarray j A !! i = A !! i !! j"
proof -
  have "column_iarray j A !! i = map (\<lambda>m. A !! m !! j) [0..<IArray.length A] ! i"
    unfolding column_iarray_def by auto
  also have "... = (\<lambda>m. A !! m !! j) ([0..<IArray.length A] ! i)" using i nth_map unfolding nrows_iarray_def by auto
  also have "... = (\<lambda>m. A !! m !! j) (i)" using nth_upt[of 0 i "IArray.length A"] i unfolding nrows_iarray_def by simp
  finally show ?thesis .
qed

lemma vec_to_iarray_rows: "vec_to_iarray` (rows A) = rows_iarray (matrix_to_iarray A)"
  unfolding rows_def unfolding rows_iarray_def
  apply (auto simp add: vec_to_iarray_row to_nat_less_card nrows_eq_card_rows)
  by (unfold image_def, auto, metis from_nat_not_eq vec_to_iarray_row)

lemma vec_to_iarray_columns: "vec_to_iarray` (columns A) = columns_iarray (matrix_to_iarray A)"
  unfolding columns_def unfolding columns_iarray_def
  apply(auto simp add: ncols_eq_card_columns to_nat_less_card vec_to_iarray_column)
  by (unfold image_def, auto, metis from_nat_not_eq vec_to_iarray_column)


subsection\<open>Definition of elementary operations\<close>

definition interchange_rows_iarray :: "'a iarray iarray => nat => nat => 'a iarray iarray"
  where "interchange_rows_iarray A a b = IArray.of_fun (\<lambda>n. if n=a then A!!b else if n=b then A!!a else A!!n) (IArray.length A)"

definition mult_row_iarray :: "'a::{times} iarray iarray => nat => 'a => 'a iarray iarray"
  where "mult_row_iarray A a q = IArray.of_fun (\<lambda>n. if n=a then mult_iarray (A!!a) q else A!!n) (IArray.length A)"

definition row_add_iarray :: "'a::{plus, times,zero} iarray iarray => nat => nat => 'a => 'a iarray iarray"
  where "row_add_iarray A a b q = IArray.of_fun (\<lambda>n. if n=a then A!!a + mult_iarray (A!!b) q else A!!n) (IArray.length A)"

definition interchange_columns_iarray :: "'a iarray iarray => nat => nat => 'a iarray iarray"
  where "interchange_columns_iarray A a b =  tabulate2 (nrows_iarray A) (ncols_iarray A) (\<lambda>i j. if j = a then A !! i !! b else if j = b then A !! i !! a else A !! i !! j)"

definition mult_column_iarray :: "'a::{times} iarray iarray => nat => 'a => 'a iarray iarray"
  where "mult_column_iarray A n q = tabulate2 (nrows_iarray A) (ncols_iarray A) (\<lambda>i j. if j = n then A !! i !! j * q else A !! i !! j)"

definition column_add_iarray :: "'a::{plus, times} iarray iarray => nat => nat => 'a => 'a iarray iarray"
  where "column_add_iarray A n m q = tabulate2 (nrows_iarray A) (ncols_iarray A) (\<lambda>i j. if j = n then A !! i !! n + A !! i !! m * q else A !! i !! j)"

subsubsection\<open>Code generator\<close>

lemma vec_to_iarray_plus[code_unfold]: "vec_to_iarray (a + b) =  (vec_to_iarray a) + (vec_to_iarray b)"
  unfolding vec_to_iarray_def
  unfolding plus_iarray_def Let_def by auto

lemma matrix_to_iarray_plus[code_unfold]: "matrix_to_iarray (A + B) = (matrix_to_iarray A) + (matrix_to_iarray B)"
  unfolding matrix_to_iarray_def o_def
  by (simp add: plus_iarray_def Let_def vec_to_iarray_plus)

lemma matrix_to_iarray_mat[code_unfold]:
  "matrix_to_iarray (mat k ::'a::{zero}^'n::{mod_type}^'n::{mod_type}) = mat_iarray k CARD('n::{mod_type})"
  unfolding matrix_to_iarray_def o_def vec_to_iarray_def mat_def mat_iarray_def tabulate2_def
  using from_nat_eq_imp_eq by fastforce 

lemma matrix_to_iarray_transpose[code_unfold]:
  shows "matrix_to_iarray (transpose A) = transpose_iarray (matrix_to_iarray A)"
  unfolding matrix_to_iarray_def transpose_def transpose_iarray_def 
    o_def tabulate2_def nrows_iarray_def ncols_iarray_def vec_to_iarray_def
  by auto

lemma matrix_to_iarray_matrix_matrix_mult[code_unfold]:
  fixes A::"'a::{semiring_1}^'m::{mod_type}^'n::{mod_type}" and B::"'a^'b::{mod_type}^'m::{mod_type}"
  shows "matrix_to_iarray (A ** B) = (matrix_to_iarray A) **i (matrix_to_iarray B)"
  unfolding matrix_to_iarray_def matrix_matrix_mult_iarray_def matrix_matrix_mult_def 
  unfolding o_def tabulate2_def nrows_iarray_def ncols_iarray_def vec_to_iarray_def
  using sum.reindex_cong[of "from_nat::nat=>'m"] using bij_from_nat unfolding bij_betw_def by fastforce


lemma vec_to_iarray_matrix_matrix_mult[code_unfold]:
  fixes A::"'a::{semiring_1}^'m::{mod_type}^'n::{mod_type}" and x::"'a^'m::{mod_type}"
  shows "vec_to_iarray (A *v x) = (matrix_to_iarray A) *iv (vec_to_iarray x)"
  unfolding matrix_vector_mult_iarray_def matrix_vector_mult_def 
  unfolding o_def tabulate2_def nrows_iarray_def ncols_iarray_def matrix_to_iarray_def vec_to_iarray_def
  using sum.reindex_cong[of "from_nat::nat=>'m"] using bij_from_nat unfolding bij_betw_def by fastforce


lemma vec_to_iarray_vector_matrix_mult[code_unfold]:
  fixes A::"'a::{semiring_1}^'m::{mod_type}^'n::{mod_type}" and x::"'a^'n::{mod_type}"
  shows "vec_to_iarray (x v* A) = (vec_to_iarray x) v*i (matrix_to_iarray A)"
  unfolding vector_matrix_mult_def vector_matrix_mult_iarray_def 
  unfolding o_def tabulate2_def nrows_iarray_def ncols_iarray_def matrix_to_iarray_def vec_to_iarray_def
proof (auto)
  fix xa
  show "(\<Sum>i\<in>UNIV. A $ i $ from_nat xa * x $ i) = (\<Sum>i = 0..<CARD('n). A $ from_nat i $ from_nat xa * x $ from_nat i)"
    apply (rule sum.reindex_cong[of "from_nat::nat=>'n"]) using bij_from_nat[where ?'a='n] unfolding bij_betw_def by fast+
qed


lemma matrix_to_iarray_interchange_rows[code_unfold]:
  fixes A::"'a::{semiring_1}^'columns::{mod_type}^'rows::{mod_type}"
  shows "matrix_to_iarray (interchange_rows A i j) = interchange_rows_iarray (matrix_to_iarray A) (to_nat i) (to_nat j)"  
proof (unfold matrix_to_iarray_def interchange_rows_iarray_def o_def map_vec_to_iarray_rw, auto)
  fix x assume x_less_card: "x < CARD('rows)"
    and x_not_j: "x \<noteq> to_nat j" and x_not_i: "x \<noteq> to_nat i"
  show "vec_to_iarray (interchange_rows A i j $ from_nat x) = vec_to_iarray (A $ from_nat x)"
    by (metis interchange_rows_preserves to_nat_from_nat_id x_less_card x_not_i x_not_j)
qed


lemma matrix_to_iarray_mult_row[code_unfold]:
  fixes A::"'a::{semiring_1}^'columns::{mod_type}^'rows::{mod_type}"
  shows "matrix_to_iarray (mult_row A i q) = mult_row_iarray (matrix_to_iarray A) (to_nat i) q"
  unfolding matrix_to_iarray_def mult_row_iarray_def o_def
  unfolding mult_iarray_def vec_to_iarray_def mult_row_def apply auto
proof -
  fix i x
  assume i_contr:"i \<noteq> to_nat (from_nat i::'rows)" and "x < CARD('columns)"
    and "i<CARD('rows)"
  hence "i = to_nat (from_nat i::'rows)" using to_nat_from_nat_id by fastforce
  thus "q * A $ from_nat i $ from_nat x = A $ from_nat i $ from_nat x"
    using i_contr by contradiction
qed

lemma matrix_to_iarray_row_add[code_unfold]:
  fixes A::"'a::{semiring_1}^'columns::{mod_type}^'rows::{mod_type}"
  shows "matrix_to_iarray (row_add A i j q) = row_add_iarray (matrix_to_iarray A) (to_nat i) (to_nat j) q"
proof (unfold matrix_to_iarray_def row_add_iarray_def o_def, auto)
  show "vec_to_iarray (row_add A i j q $ i) = vec_to_iarray (A $ i) + mult_iarray (vec_to_iarray (A $ j)) q"
    unfolding mult_iarray_def vec_to_iarray_def unfolding plus_iarray_def Let_def row_add_def by auto 
  fix ia assume ia_not_i: "ia \<noteq> to_nat i" and ia_card: "ia < CARD('rows) "
  have from_nat_ia_not_i: "from_nat ia \<noteq> i"
  proof (rule ccontr)
    assume "\<not> from_nat ia \<noteq> i" hence "from_nat ia = i" by simp
    hence "to_nat (from_nat ia::'rows) = to_nat i" by simp
    hence "ia=to_nat i" using to_nat_from_nat_id ia_card by fastforce
    thus False  using ia_not_i by contradiction
  qed
  show "vec_to_iarray (row_add A i j q $ from_nat ia) = vec_to_iarray (A $ from_nat ia)"
    using ia_not_i
    unfolding vec_to_iarray_morph[symmetric] unfolding row_add_def using from_nat_ia_not_i by vector
qed

lemma matrix_to_iarray_interchange_columns[code_unfold]:
  fixes A::"'a::{semiring_1}^'columns::{mod_type}^'rows::{mod_type}"
  shows "matrix_to_iarray (interchange_columns A i j) = interchange_columns_iarray (matrix_to_iarray A) (to_nat i) (to_nat j)"
  unfolding interchange_columns_def interchange_columns_iarray_def o_def tabulate2_def
  unfolding nrows_eq_card_rows ncols_eq_card_columns 
  unfolding  matrix_to_iarray_def o_def vec_to_iarray_def 
  by (auto simp add: to_nat_from_nat_id to_nat_less_card[of i] to_nat_less_card[of j])


lemma matrix_to_iarray_mult_columns[code_unfold]:
  fixes A::"'a::{semiring_1}^'columns::{mod_type}^'rows::{mod_type}"
  shows "matrix_to_iarray (mult_column A i q) = mult_column_iarray (matrix_to_iarray A) (to_nat i) q"
  unfolding mult_column_def mult_column_iarray_def o_def tabulate2_def
  unfolding nrows_eq_card_rows ncols_eq_card_columns 
  unfolding  matrix_to_iarray_def o_def vec_to_iarray_def
  by (auto simp add: to_nat_from_nat_id)

lemma matrix_to_iarray_column_add[code_unfold]:
  fixes A::"'a::{semiring_1}^'columns::{mod_type}^'rows::{mod_type}"
  shows "matrix_to_iarray (column_add A i j q) = column_add_iarray (matrix_to_iarray A) (to_nat i) (to_nat j) q"
  unfolding column_add_def column_add_iarray_def o_def tabulate2_def
  unfolding nrows_eq_card_rows ncols_eq_card_columns 
  unfolding  matrix_to_iarray_def o_def vec_to_iarray_def
  by (auto simp add: to_nat_from_nat_id to_nat_less_card[of i] to_nat_less_card[of j])


end
