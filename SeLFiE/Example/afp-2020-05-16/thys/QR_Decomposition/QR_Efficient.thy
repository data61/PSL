(*  
  Title:      QR_Efficient.thy
  Author:     Jose Divasón <jose.divasonm at unirioja.es>
  Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Improvements to get better performance of the algorithm\<close>

theory QR_Efficient
imports QR_Decomposition_IArrays
begin

subsection\<open>Improvements for computing the Gram Schmidt algorithm and QR decomposition using vecs\<close>

text\<open>Essentialy, we try to avoid removing duplicates in each iteration. 
  They will not affect the @{const sum_list} since the duplicates will be the vector zero.\<close>

subsubsection\<open>New definitions\<close>

definition "Gram_Schmidt_column_k_efficient A k 
  = (\<chi> a b. (if b = from_nat k 
  then column b A - sum_list (map (\<lambda>x. ((column b A \<bullet> x) / (x \<bullet> x)) *\<^sub>R x) 
  ((map (\<lambda>n. column (from_nat n) A) [0..<to_nat b]))) else column b A) $ a)"

subsubsection\<open>General properties about @{const sum_list}\<close>

lemma sum_list_remdups:
  assumes "!!i j. i<length xs \<and> j<length xs \<and> i \<noteq> j 
  \<and> xs ! i = xs ! j \<longrightarrow> xs ! i = 0 \<and> xs ! j = 0"
  shows "sum_list (remdups xs) = sum_list xs"
  using assms
proof (induct xs)
  case Nil
  thus ?case by auto
next
  case (Cons a xs)
  show ?case 
  proof (cases "a \<in> set (xs)")
    case False 
    have "sum_list (remdups (a # xs)) = sum_list (a # (remdups xs))" by (simp add: False)
    also have "... = a + sum_list (remdups xs)" by auto
    also have "... = a + sum_list xs" using Cons.hyps Cons.prems False
      by fastforce      
    also have "... = sum_list (a # xs)" by simp
    finally show ?thesis .
  next
    case True
    have a: "a=0" using Cons.hyps Cons.prems True
      by (metis Suc_less_eq add.right_neutral add_Suc_right add_gr_0 
        in_set_conv_nth lessI list.size(4) nat.simps(3) nth_Cons_0 nth_Cons_Suc)       
    have "sum_list (remdups (a # xs)) = sum_list (remdups xs)" using True by auto
    also have "... = sum_list xs" using Cons.hyps Cons.prems True
      by fastforce
    also have "... = a + sum_list xs" using a by simp
    also have "... = sum_list (a # xs)" by simp
    finally show ?thesis .
  qed
qed


lemma sum_list_remdups_2:
  fixes f:: "'a::{zero, monoid_add}\<Rightarrow>'a"
  assumes "!!i j. i<length xs \<and> j<length xs \<and> i \<noteq> j \<and> (xs ! i) = (xs ! j) 
    \<longrightarrow> f (xs ! i) = 0 \<and> f (xs ! j) = 0"
  shows "sum_list (map f (remdups xs)) = sum_list (map f xs)"
  using assms
proof (induct xs)
  case Nil
  show ?case by auto
next
  case (Cons a xs)
  show ?case
  proof (cases "a \<in> set xs")
    case False 
    hence "sum_list (map f (remdups (a # xs))) =  sum_list (map f (a # (remdups xs)))"
      by simp
    also have "... = sum_list (f a # (map f (remdups xs)))" by auto
    also have "... = f a + sum_list (map f (remdups xs))" by auto
    also have "... = f a + sum_list (map f xs)" using Cons.prems Cons.hyps
      using id_apply by fastforce
    also have "... =  sum_list (map f (a # xs))" by auto
    finally show ?thesis .
  next
    case True
    have fa_0: "f a = 0" using Cons.hyps Cons.prems True
      by (metis Suc_less_eq add.right_neutral add_Suc_right add_gr_0 
        in_set_conv_nth lessI list.size(4) nth_Cons_0 nth_Cons_Suc)
    have "sum_list (map f (remdups (a # xs))) =  sum_list (map f (remdups xs))"
      using True by simp
    also have "... = sum_list (map f xs)" using Cons.prems Cons.hyps
      using id_apply by fastforce
    also have "... = f a + sum_list (map f xs)" using fa_0 by simp
    also have "... = sum_list (map f (a # xs))" by auto
    finally show ?thesis .
  qed
qed

subsubsection\<open>Proving a code equation to improve the performance\<close>

lemma set_map_column:
  "set (map (\<lambda>n. column (from_nat n) G) [0..<to_nat b]) =  {column i G|i. i<b}"
proof (auto) 
  fix n assume "n < to_nat b" 
  hence "from_nat n < b" using from_nat_mono to_nat_less_card by fastforce
  thus "\<exists>i. column (from_nat n) G = column i G\<and> i < b" by auto
next
  fix i assume "i < b" hence ib: "to_nat i < to_nat b" by (simp add: to_nat_le)
  show "column i G \<in> (\<lambda>n. column (from_nat n) G) ` {0..<to_nat b}"
    unfolding image_def
    by (auto, rule bexI[of _ "to_nat i"], auto simp add: ib)
qed

lemma column_Gram_Schmidt_column_k_repeated_0:
  fixes A::"'a::{real_inner}^'n::{mod_type}^'m::{mod_type}"
  assumes i_not_k: "i\<noteq>k" and ik: "i<k"
  and c_eq: "column k (Gram_Schmidt_column_k A (to_nat k)) 
  = column i (Gram_Schmidt_column_k A (to_nat k))"
  and o: "pairwise orthogonal {column i A|i. i<k}"
  shows "column k (Gram_Schmidt_column_k A (to_nat k)) = 0" 
  and "column i (Gram_Schmidt_column_k A (to_nat k)) = 0"
proof -
  have "column k (Gram_Schmidt_column_k A (to_nat k)) 
    = column k A - (\<Sum>x\<in>{column i A |i. i < k}. (x \<bullet> column k A / (x \<bullet> x)) *\<^sub>R x)"
    by (rule column_Gram_Schmidt_column_k)
  also have "... = column k A - proj_onto (column k A) {column i A |i. i < k}"
    unfolding proj_onto_def proj_def[abs_def]
    by (metis (no_types, lifting) inner_commute)
  finally have col_k_rw: "column k (Gram_Schmidt_column_k A (to_nat k)) 
    = column k A - proj_onto (column k A) {column i A |i. i < k}" .
  have "orthogonal (column k (Gram_Schmidt_column_k A (to_nat k))) 
    (column i (Gram_Schmidt_column_k A (to_nat k)))"
    unfolding col_k_rw
  proof (rule orthogonal_proj_set[OF _ _ o])
    have "column i (Gram_Schmidt_column_k A (to_nat k)) = column i A"
      using column_Gram_Schmidt_column_k'[OF i_not_k] .
    also have "...  \<in> {column i A |i. i < k}" using assms(2) by blast
    finally show "column i (Gram_Schmidt_column_k A (to_nat k)) \<in> {column i A |i. i < k}" .
    show "finite {column i A |i. i < k}" by auto
  qed
  thus "column k (Gram_Schmidt_column_k A (to_nat k)) = 0"
    and "column i (Gram_Schmidt_column_k A (to_nat k)) = 0"
    unfolding orthogonal_def c_eq inner_eq_zero_iff by auto
qed



lemma column_Gram_Schmidt_upt_k_repeated_0':
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  assumes i_not_k: "i\<noteq>j" and ij: "i<j" and j: "j\<le>from_nat k"
  and c_eq: "column j (Gram_Schmidt_upt_k A k) 
  = column i (Gram_Schmidt_upt_k A k)"
  and k: "k<ncols A"
  shows "column j (Gram_Schmidt_upt_k A k) = 0" 
  using j c_eq k
proof (induct k)
  case 0
  thus ?case 
    using ij least_mod_type 
    unfolding from_nat_0
    by (metis (no_types) dual_order.strict_trans1 ij least_mod_type not_less)
next
  case (Suc k)
  have k: "k<ncols A" using Suc.prems unfolding ncols_def by auto
  have i_not_k: "i\<noteq>from_nat (Suc k)" using ij Suc.prems by auto
  have col_i_rw: "column i (Gram_Schmidt_upt_k A (Suc k)) = column i (Gram_Schmidt_upt_k A k)" 
    by (simp add: i_not_k Gram_Schmidt_column_k_def Gram_Schmidt_upt_k_suc column_def)
  have tn_fn_suc: "to_nat (from_nat (Suc k)::'n) = Suc k"
    using to_nat_from_nat_id Suc.prems
    unfolding ncols_def by blast
  show ?case
  proof (cases "j=from_nat (Suc k)")
    case False    
    have jk: "j \<le> from_nat k" 
      by (metis False One_nat_def Suc.prems(1) add.right_neutral add_Suc_right
        from_nat_suc le_Suc less_le linorder_not_le)
    have col_j_rw: "column j (Gram_Schmidt_upt_k A (Suc k)) = column j (Gram_Schmidt_upt_k A k)" 
      by (simp add: False Gram_Schmidt_column_k_def Gram_Schmidt_upt_k_suc column_def)
    have col_j_eq_col_i_k: "column j (Gram_Schmidt_upt_k A k) = column i (Gram_Schmidt_upt_k A k)"
      using Suc.prems unfolding col_j_rw col_i_rw by simp
    show ?thesis using Suc.hyps col_j_eq_col_i_k k jk unfolding col_j_rw by blast
  next
    case True
    show ?thesis unfolding True unfolding Gram_Schmidt_upt_k_suc 
    proof (rule column_Gram_Schmidt_column_k_repeated_0(1)
        [of i "from_nat (Suc k)" "Gram_Schmidt_upt_k A k", unfolded tn_fn_suc])
      have set_rw: "{column i (Gram_Schmidt_upt_k A k) |i. i < from_nat (Suc k)} 
        = {column i (Gram_Schmidt_upt_k A k) |i. to_nat i \<le> k}"
        by (metis (mono_tags, hide_lams) less_Suc_eq_le less_le not_less tn_fn_suc to_nat_mono)      
      show "i \<noteq> from_nat (Suc k)" using i_not_k .
      show "i < from_nat (Suc k)" using True ij by blast
      show "column (from_nat (Suc k)) (Gram_Schmidt_column_k (Gram_Schmidt_upt_k A k) (Suc k)) =
        column i (Gram_Schmidt_column_k (Gram_Schmidt_upt_k A k) (Suc k))"
        using Suc.prems True by (simp add: Gram_Schmidt_upt_k_suc) 
      show "pairwise orthogonal {column i (Gram_Schmidt_upt_k A k) |i. i < from_nat (Suc k)}"
        unfolding set_rw by (rule orthogonal_Gram_Schmidt_upt_k[OF k])
    qed
  qed
qed




lemma column_Gram_Schmidt_upt_k_repeated_0:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  assumes i_not_k: "i\<noteq>j" and ij: "i<j" and j: "j\<le>k"
  and c_eq: "column j (Gram_Schmidt_upt_k A (to_nat k)) 
  = column i (Gram_Schmidt_upt_k A (to_nat k))"
  shows "column j (Gram_Schmidt_upt_k A (to_nat k)) = 0" 
  using assms column_Gram_Schmidt_upt_k_repeated_0' to_nat_less_card ncols_def 
  by (metis c_eq column_Gram_Schmidt_upt_k_repeated_0' 
     from_nat_to_nat_id i_not_k ij j ncols_def to_nat_less_card)


corollary column_Gram_Schmidt_upt_k_repeated:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  assumes i_not_k: "i\<noteq>j" and ij: "i\<le>k" and "j\<le>k"
  and c_eq: "column j (Gram_Schmidt_upt_k A (to_nat k)) 
    = column i (Gram_Schmidt_upt_k A (to_nat k))"
  shows "column j (Gram_Schmidt_upt_k A (to_nat k)) = 0" 
  and "column i (Gram_Schmidt_upt_k A (to_nat k)) = 0"
proof -
  show "column j (Gram_Schmidt_upt_k A (to_nat k)) = 0" 
  proof (cases "i<j")
    case True
    thus ?thesis using assms column_Gram_Schmidt_upt_k_repeated_0 by metis
  next
    case False hence ji: "j<i" using i_not_k by auto
    thus ?thesis using assms column_Gram_Schmidt_upt_k_repeated_0 by metis
  qed
  show "column i (Gram_Schmidt_upt_k A (to_nat k)) = 0"
  proof (cases "i<j")
    case True
    thus ?thesis using assms column_Gram_Schmidt_upt_k_repeated_0 by metis
  next
    case False hence ji: "j<i" using i_not_k by auto
    thus ?thesis using assms column_Gram_Schmidt_upt_k_repeated_0 by metis
  qed
qed


lemma column_Gram_Schmidt_column_k_eq_efficient:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  assumes "Gram_Schmidt_upt_k A k = foldl Gram_Schmidt_column_k_efficient A [0..<Suc k]"
  and suc_k: "Suc k < ncols A"
  shows "column b (Gram_Schmidt_column_k (Gram_Schmidt_upt_k A k) (Suc k))
  = column b (Gram_Schmidt_column_k_efficient (Gram_Schmidt_upt_k A k) (Suc k))"
proof (cases "b = from_nat (Suc k)")
  case False thus ?thesis 
    unfolding Gram_Schmidt_column_k_efficient_def Gram_Schmidt_column_k_def column_def by auto
next
  case True
  have tn_fn_suc: "to_nat (from_nat (Suc k)::'n) = Suc k" 
    using suc_k to_nat_from_nat_id unfolding ncols_def by auto
  define G where"G = Gram_Schmidt_upt_k A k"
  let ?f="(\<lambda>x. (column b G \<bullet> x / (x \<bullet> x)) *\<^sub>R x)"
  let ?g="(\<lambda>n. column (from_nat n) G) "
  have proj_eq: "proj_onto (column b G) {column i G |i. i < b} 
    = sum_list (map ?f (map ?g [0..<to_nat b]))"
  proof -
    have "proj_onto (column b G) {column i G |i. i < b} = sum ?f {column i G |i. i < b}" 
      unfolding proj_onto_def proj_def[abs_def] by simp
    also have "... = sum ?f (set (map ?g [0..<to_nat b]))"
      by (rule sum.cong, auto simp add: set_map_column[symmetric])    
    also have "... = sum_list (map ?f (remdups (map ?g [0..<to_nat b])))" unfolding sum_code ..
    also have "... = sum_list ((map ?f ((map ?g [0..<to_nat b]))))" 
    proof (rule sum_list_remdups_2, auto)
      fix i j assume i: "i < to_nat b"
        and j: "j < to_nat b" and ij: "i \<noteq> j"
        and col_eq: "column (from_nat i) G = column (from_nat j) G"
        and col_0: "column (from_nat j) G \<noteq> 0"
      have k: "to_nat (from_nat k::'n) = k" 
        by (metis Suc_lessD ncols_def suc_k to_nat_from_nat_id)
      have "column (from_nat j) G = 0" 
      proof (unfold G_def, rule column_Gram_Schmidt_upt_k_repeated(1)
          [of "(from_nat i)::'n" "from_nat j" "from_nat k" A, unfolded k])
        have "from_nat i < (from_nat (Suc k)::'n)"
          using from_nat_mono[of i "Suc k"] suc_k i 
          unfolding True tn_fn_suc ncols_def by simp
        thus "from_nat i \<le> (from_nat k::'n)" 
          by (metis Suc_lessD True from_nat_mono' i less_Suc_eq_le ncols_def suc_k tn_fn_suc)
        have "from_nat j < (from_nat (Suc k)::'n)"
          using from_nat_mono[of j "Suc k"] suc_k j
          unfolding True tn_fn_suc ncols_def by simp
        thus "from_nat j \<le> (from_nat k::'n)"
          by (metis Suc_lessD True from_nat_mono' j less_Suc_eq_le ncols_def suc_k tn_fn_suc)
        show "from_nat i \<noteq> (from_nat j::'n)" using ij i j True suc_k 
          by (metis (no_types, lifting) dual_order.strict_trans from_nat_eq_imp_eq ncols_def tn_fn_suc)
        show "column (from_nat j) (Gram_Schmidt_upt_k A k) 
          = column (from_nat i) (Gram_Schmidt_upt_k A k)" using G_def col_eq by auto
      qed
      thus "column b G \<bullet> column (from_nat j) G = 0" using col_0 by contradiction
    qed
    finally show ?thesis .
  qed
  have "column b (Gram_Schmidt_column_k G (Suc k)) 
    = column b G - proj_onto (column b G) {column i G |i. i < b}"
    unfolding True
    unfolding Gram_Schmidt_column_k_def G_def column_def by vector
  also have "... = column b G 
    - (\<Sum>x\<leftarrow>map (\<lambda>n. column (from_nat n) G) [0..<to_nat b]. (column b G \<bullet> x / (x \<bullet> x)) *\<^sub>R x)"
    unfolding proj_eq ..
  also have "... = column b (Gram_Schmidt_column_k_efficient G (Suc k))" 
    unfolding True Gram_Schmidt_column_k_efficient_def G_def column_def by vector
  finally show ?thesis unfolding G_def .
qed


lemma Gram_Schmidt_upt_k_efficient_induction:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  assumes "Gram_Schmidt_upt_k A k = foldl Gram_Schmidt_column_k_efficient A [0..<Suc k]"
  and suc_k: "Suc k < ncols A"
  shows "Gram_Schmidt_column_k (Gram_Schmidt_upt_k A k) (Suc k) 
  = Gram_Schmidt_column_k_efficient (Gram_Schmidt_upt_k A k) (Suc k)"
  using column_Gram_Schmidt_column_k_eq_efficient[OF assms]
  unfolding column_def vec_eq_iff by vector


lemma Gram_Schmidt_upt_k_efficient:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}" 
  assumes k: "k<ncols A"
  shows "Gram_Schmidt_upt_k A k = foldl Gram_Schmidt_column_k_efficient A [0..<Suc k]"
  using k
proof (induct k)
  case 0
  have " {column i A |i. i < 0} = {}" using least_mod_type using leD by auto
  thus ?case 
    by (simp, auto simp add: Gram_Schmidt_column_k_efficient_def 
      Gram_Schmidt_upt_k_def Gram_Schmidt_column_k_def 
      proj_onto_def proj_def vec_eq_iff from_nat_0 to_nat_0)
next
  case (Suc k)
  have "Gram_Schmidt_upt_k A (Suc k) = Gram_Schmidt_column_k (Gram_Schmidt_upt_k A k) (Suc k)"
    by (rule Gram_Schmidt_upt_k_suc)
  also have "... = Gram_Schmidt_column_k_efficient (Gram_Schmidt_upt_k A k) (Suc k)"
  proof (rule Gram_Schmidt_upt_k_efficient_induction)
    show "Gram_Schmidt_upt_k A k = foldl Gram_Schmidt_column_k_efficient A [0..<Suc k]"
      using Suc.hyps Suc.prems by auto
    show "Suc k < ncols A" using Suc.prems by auto
  qed
  also have "... = Gram_Schmidt_column_k_efficient
    (foldl Gram_Schmidt_column_k_efficient A [0..<Suc k]) (Suc k)"
    using Suc.hyps Suc.prems by auto
  also have "... = (foldl Gram_Schmidt_column_k_efficient A [0..<Suc (Suc k)])" by auto
  finally show ?case .
qed

text\<open>This equation is now more efficient than the original definition of the algoritm, since it is not
  removing duplicates in each iteration, which is more expensive in time than adding zeros (if there appear 
  duplicates while applying the algorithm, they are zeros and then the @{const sum_list} is the same in each step).\<close>

lemma Gram_Schmidt_matrix_efficient[code_unfold]:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}" 
  shows "Gram_Schmidt_matrix A = foldl Gram_Schmidt_column_k_efficient A [0..<ncols A]"
proof -
  have n: "(ncols A - 1) < ncols A" unfolding ncols_def by auto
  have "Gram_Schmidt_matrix A = Gram_Schmidt_upt_k A (ncols A - 1)"
    unfolding Gram_Schmidt_matrix_def ..
  also have "... = foldl Gram_Schmidt_column_k_efficient A [0..<ncols A]" 
    using Gram_Schmidt_upt_k_efficient[OF n] unfolding ncols_def by auto
  finally show ?thesis .
qed


subsection\<open>Improvements for computing the Gram Schmidt algorithm and QR decomposition 
  using immutable arrays\<close>

subsubsection\<open>New definitions\<close>

definition "Gram_Schmidt_column_k_iarrays_efficient A k = 
  tabulate2 (nrows_iarray A) (ncols_iarray A) (\<lambda>a b. let column_b_A = column_iarray b A in 
  (if b = k then (column_b_A - sum_list (map (\<lambda>x. ((column_b_A \<bullet>i x) / (x \<bullet>i x)) *\<^sub>R x) 
  ((List.map (\<lambda>n. column_iarray n A) [0..<b]))))
  else column_b_A) !! a)"


definition "Gram_Schmidt_matrix_iarrays_efficient A 
  = foldl Gram_Schmidt_column_k_iarrays_efficient A [0..<ncols_iarray A]"

definition "QR_decomposition_iarrays_efficient A = 
  (let Q = divide_by_norm_iarray (Gram_Schmidt_matrix_iarrays_efficient A) 
  in (Q, transpose_iarray Q **i A))"

subsubsection\<open>General properties\<close>

lemma tabulate2_nth:
  assumes i: "i<nr" and j: "j<nc"
  shows "(tabulate2 nr nc f) !! i !! j = f i j"
  unfolding tabulate2_def using i j nth_map by auto

lemma vec_to_iarray_minus[code_unfold]: 
  "vec_to_iarray (a - b) =  (vec_to_iarray a) - (vec_to_iarray b)"
  unfolding vec_to_iarray_def
  unfolding minus_iarray_def Let_def by auto

lemma vec_to_iarray_minus_nth:
  assumes A: "i<IArray.length (vec_to_iarray A)" 
  and B: "i<IArray.length (vec_to_iarray B)"
  shows "(vec_to_iarray A - vec_to_iarray B) !! i 
  = vec_to_iarray A !! i - vec_to_iarray B !! i"
proof -
  have i: "i<CARD('b)" using A unfolding vec_to_iarray_def by auto
  have i2: "i<CARD('c)" using B unfolding vec_to_iarray_def by auto
  have i_length: "i < length [0..<max CARD('b) CARD('c)]" using i i2 by auto
  have i_nth: "[0..<max CARD('b) CARD('c)] ! i = i" using i_length by auto
  let ?f="(\<lambda>a. map (\<lambda>a. if a < CARD('b) then IArray 
    (map (\<lambda>i. A $ from_nat i) [0..<CARD('b)]) !! a else 0) [0..<max CARD('b) CARD('c)] !
    a - map (\<lambda>a. if a < CARD('c) then 
    IArray (map (\<lambda>i. B $ from_nat i) [0..<CARD('c)]) !! a else 0) [0..<max CARD('b) CARD('c)] ! a)"
  have "(vec_to_iarray A - vec_to_iarray B) = (IArray (map (\<lambda>i. A $ from_nat i) [0..<CARD('b)]) 
    - IArray (map (\<lambda>i. B $ from_nat i) [0..<CARD('c)]))"
    unfolding vec_to_iarray_def by auto
  also have "... = IArray (map ?f [0..<max CARD('b) CARD('c)])" 
    unfolding minus_iarray_def Let_def by simp
  also have "... !! i =  A $ from_nat i - B $ from_nat i"
    using i_length using nth_map i i2 by auto
  also have "... = vec_to_iarray A !! i - vec_to_iarray B !! i"
   by (metis i i2 vec_to_iarray_nth)
  finally show ?thesis .
qed


lemma sum_list_map_vec_to_iarray:
  assumes "xs \<noteq> []" (*If I remove this assumption, I have to prove 
  vec_to_iarray 0 = IArray [] which is false.*)
  shows "sum_list (map (vec_to_iarray \<circ> f) xs) = vec_to_iarray (sum_list (map f xs))"
  using assms
proof (induct xs)
  case Nil
  thus ?case unfolding o_def by auto
next
  case (Cons a xs)
  show ?case
  proof (cases "xs=[]")
    case True
    have l_rw: "sum_list (map (vec_to_iarray \<circ> f) xs) = IArray[]" 
      unfolding True by (simp add: zero_iarray_def)
    have "sum_list (map (vec_to_iarray \<circ> f) (a # xs)) 
      = sum_list ((vec_to_iarray \<circ> f) a # map (vec_to_iarray \<circ> f) xs)"
      by simp
    also have "... = (vec_to_iarray \<circ> f) a + sum_list (map (vec_to_iarray \<circ> f) xs)" by simp
    also have "... = vec_to_iarray (f a) + IArray[]" unfolding l_rw by auto
    also have "... = vec_to_iarray (f a) + vec_to_iarray (0::('b,'c) vec)" 
      unfolding plus_iarray_def Let_def vec_to_iarray_def by auto
    also have "... = vec_to_iarray (sum_list (map (f) (a # xs)))" 
      unfolding True unfolding plus_iarray_def Let_def vec_to_iarray_def by auto
    finally show ?thesis .
  next
    case False
    have "sum_list (map (vec_to_iarray \<circ> f) (a # xs)) 
      = sum_list ((vec_to_iarray \<circ> f) a # map (vec_to_iarray \<circ> f) xs)"
      by simp
    also have "... = (vec_to_iarray \<circ> f) a + sum_list (map (vec_to_iarray \<circ> f) xs)" by simp
    also have "... = (vec_to_iarray \<circ> f) a + vec_to_iarray (sum_list (map f xs))"
      using Cons.prems Cons.hyps False by presburger
    also have "... = vec_to_iarray (f a) + vec_to_iarray (sum_list (map f xs))" by auto
    also have "... = vec_to_iarray (f a + (sum_list (map f xs)))"
      by (simp add: vec_to_iarray_plus)
    also have "... = vec_to_iarray (sum_list (map (f) (a # xs)))" by simp
    finally show ?thesis .
  qed
qed

subsubsection\<open>Proving the equivalence\<close>

lemma matrix_to_iarray_Gram_Schmidt_column_k_efficient:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}" 
  assumes k: "k<ncols A"
  shows "matrix_to_iarray (Gram_Schmidt_column_k_efficient A k) 
  = Gram_Schmidt_column_k_iarrays_efficient (matrix_to_iarray A) k"
proof (unfold iarray_exhaust2 list_eq_iff_nth_eq, rule conjI, auto, 
    unfold IArray.sub_def[symmetric] IArray.length_def[symmetric])
  show "IArray.length (matrix_to_iarray (Gram_Schmidt_column_k_efficient A k)) 
    = IArray.length (Gram_Schmidt_column_k_iarrays_efficient (matrix_to_iarray A) k)"
    unfolding matrix_to_iarray_def Gram_Schmidt_column_k_iarrays_efficient_def tabulate2_def 
    unfolding nrows_iarray_def by auto
  fix i 
  show "i < IArray.length (matrix_to_iarray (Gram_Schmidt_column_k_efficient A k)) \<Longrightarrow>
    IArray.length (matrix_to_iarray (Gram_Schmidt_column_k_efficient A k) !! i) =
    IArray.length (Gram_Schmidt_column_k_iarrays_efficient (matrix_to_iarray A) k !! i)"
    by (simp add: matrix_to_iarray_def Gram_Schmidt_column_k_iarrays_efficient_def 
      Gram_Schmidt_column_k_efficient_def tabulate2_def ncols_iarray_def 
      nrows_iarray_def vec_to_iarray_def)
  fix i ia 
  assume i:"i < IArray.length (matrix_to_iarray (Gram_Schmidt_column_k_efficient A k))"
    and ia: "ia < IArray.length (matrix_to_iarray (Gram_Schmidt_column_k_efficient A k) !! i)"
  show "matrix_to_iarray (Gram_Schmidt_column_k_efficient A k) !! i !! ia 
    = Gram_Schmidt_column_k_iarrays_efficient (matrix_to_iarray A) k !! i !! ia"
  proof -
    let ?f="(\<lambda>a b. let column_b_A = column_iarray b (matrix_to_iarray A)
      in (if b = k then column_b_A 
      - (\<Sum>x\<leftarrow>map (\<lambda>n. column_iarray n (matrix_to_iarray A)) [0..<b]. 
      (column_b_A \<bullet>i x / (x \<bullet>i x)) *\<^sub>R x) else column_b_A) !! a)"
    have i2: "i<nrows A" using i unfolding nrows_def matrix_to_iarray_def by auto
    have ia2: "ia<ncols A" 
    using ia unfolding ncols_def matrix_to_iarray_def o_def vec_to_iarray_def
      by (metis i2 ia length_vec_to_iarray nrows_def to_nat_from_nat_id vec_matrix) 
    have "Gram_Schmidt_column_k_iarrays_efficient (matrix_to_iarray A) k !! i !! ia = ?f i ia"
      unfolding Gram_Schmidt_column_k_iarrays_efficient_def
    proof (rule tabulate2_nth)
      show "i < nrows_iarray (matrix_to_iarray A)" 
        using i2 unfolding matrix_to_iarray_nrows .
      show "ia < ncols_iarray (matrix_to_iarray A)"
        using ia2 unfolding matrix_to_iarray_ncols .
    qed
    also have "... = (Gram_Schmidt_column_k_efficient A k) $ (from_nat i) $ (from_nat ia)"
      unfolding Gram_Schmidt_column_k_efficient_def Let_def
    proof (auto)
      assume ia_neq_k: "ia \<noteq> k" and f_eq: "(from_nat ia::'n) = from_nat k "
      have "ia = k" using f_eq by (metis assms from_nat_eq_imp_eq ia2 ncols_def)
      thus "IArray.list_of (column_iarray ia (matrix_to_iarray A)) ! i =
        column (from_nat k) A $ from_nat i -
        sum_list (map ((\<lambda>x. (column (from_nat k) A \<bullet> x / (x \<bullet> x)) *\<^sub>R x) 
        \<circ> (\<lambda>n. column (from_nat n) A)) [0..<to_nat (from_nat k)]) $ from_nat i"
        using ia_neq_k by contradiction
    next
      assume "ia \<noteq> k"
      thus "IArray.list_of (column_iarray ia (matrix_to_iarray A)) ! i 
        = column (from_nat ia) A $ from_nat i"
        by (metis IArray.sub_def i ia2 length_eq_card_rows to_nat_from_nat_id 
          vec_to_iarray_column' vec_to_iarray_nth')
    next
      assume "ia = k"
      let ?f="\<lambda>x. ((column (from_nat k) A) \<bullet> (column (from_nat x) A) /
        ((column (from_nat x) A) \<bullet> (column (from_nat x) A))) *\<^sub>R (column (from_nat x) A)"
      let ?l="sum_list (map ?f [0..<k])"
      show "IArray.list_of
        (column_iarray k (matrix_to_iarray A) -
        sum_list (map ((\<lambda>x. (column_iarray k (matrix_to_iarray A) \<bullet>i x / (x \<bullet>i x)) *\<^sub>R x) 
        \<circ> (\<lambda>n. column_iarray n (matrix_to_iarray A))) [0..<k])) ! i =
        column (from_nat k) A $ from_nat i - 
        sum_list (map ((\<lambda>x. (column (from_nat k) A \<bullet> x / (x \<bullet> x)) *\<^sub>R x) 
        \<circ> (\<lambda>n. column (from_nat n) A)) [0..<to_nat (from_nat k::'n)]) $ from_nat i"    
      proof (cases "k=0")
        case True
        show ?thesis
          unfolding vec_to_iarray_column'[OF k, symmetric]
          unfolding True from_nat_0 to_nat_0 
          by (auto, metis IArray.sub_def i2 minus_zero_iarray nrows_def vec_to_iarray_nth)    
      next
        case False        
        have tn_fn_k: "to_nat (from_nat k::'n) = k" 
          by (metis assms from_nat_to_nat ncols_def)
        have column_rw: "column_iarray k (matrix_to_iarray A) 
          = vec_to_iarray (column (from_nat k) A)"
          by (rule vec_to_iarray_column'[symmetric, OF k])
        have sum_list_rw: "(\<Sum>x\<leftarrow>[0..<k]. (column_iarray k (matrix_to_iarray A) 
        \<bullet>i column_iarray x (matrix_to_iarray A) / (column_iarray x (matrix_to_iarray A) 
        \<bullet>i column_iarray x (matrix_to_iarray A))) *\<^sub>R column_iarray x (matrix_to_iarray A)) 
        = vec_to_iarray ?l"
        proof -
          have "(\<Sum>x\<leftarrow>[0..<k]. (column_iarray k (matrix_to_iarray A) 
          \<bullet>i column_iarray x (matrix_to_iarray A) / (column_iarray x (matrix_to_iarray A) 
          \<bullet>i column_iarray x (matrix_to_iarray A))) *\<^sub>R column_iarray x (matrix_to_iarray A)) 
          = sum_list (map (vec_to_iarray \<circ> ?f) [0..<k])"            
          proof (unfold interv_sum_list_conv_sum_set_nat, rule sum.cong, auto)
            fix x assume "x<k"
            hence x: "x<ncols A" using k by auto
            show "(column_iarray k (matrix_to_iarray A) \<bullet>i column_iarray x (matrix_to_iarray A) /
              (column_iarray x (matrix_to_iarray A) \<bullet>i column_iarray x (matrix_to_iarray A))) *\<^sub>R
              column_iarray x (matrix_to_iarray A) =
              vec_to_iarray ((column (from_nat k) A \<bullet> column (from_nat x) A /
              (column (from_nat x) A \<bullet> column (from_nat x) A)) *\<^sub>R column (from_nat x) A)"
              unfolding vec_to_iarray_scaleR vec_to_iarray_inner
              unfolding column_rw unfolding vec_to_iarray_column'[OF x, symmetric] ..
          qed
          also have "... = vec_to_iarray (sum_list (map ?f [0..<k]))" 
            by (rule sum_list_map_vec_to_iarray, auto simp add: False)
          finally show ?thesis .   
        qed

        have "IArray.list_of
          (column_iarray k (matrix_to_iarray A) -
          sum_list (map ((\<lambda>x. (column_iarray k (matrix_to_iarray A) \<bullet>i x / (x \<bullet>i x)) *\<^sub>R x) 
          \<circ> (\<lambda>n. column_iarray n (matrix_to_iarray A))) [0..<k])) ! i = 
          (column_iarray k (matrix_to_iarray A) -
          (\<Sum>x\<leftarrow>[0..<k]. (column_iarray k (matrix_to_iarray A) \<bullet>i column_iarray x (matrix_to_iarray A) /
          (column_iarray x (matrix_to_iarray A) \<bullet>i column_iarray x (matrix_to_iarray A))) *\<^sub>R
          column_iarray x (matrix_to_iarray A))) !! i"
          unfolding vec_to_iarray_inner tn_fn_k o_def
          unfolding IArray.sub_def[symmetric] ..
        also have "... = (vec_to_iarray (column (from_nat k) A) - vec_to_iarray ?l) !! i"
          unfolding sum_list_rw unfolding column_rw  ..
        also have "... = ((vec_to_iarray (column (from_nat k) A)) !! i) - (vec_to_iarray ?l !! i)"
        proof (rule vec_to_iarray_minus_nth)
          show " i < IArray.length (vec_to_iarray (column (from_nat k) A))" 
            by (metis i2 length_vec_to_iarray nrows_def)
          show "i < IArray.length (vec_to_iarray ?l)" 
            by (metis (no_types, lifting) i2 length_vec_to_iarray nrows_def)
        qed
        also have "... = column (from_nat k) A $ from_nat i - ?l $ from_nat i"
          unfolding column_rw
          by (metis (no_types, lifting) i2 nrows_def vec_to_iarray_nth) 
        also have "... = column (from_nat k) A $ from_nat i -
          sum_list (map ((\<lambda>x. (column (from_nat k) A \<bullet> x / (x \<bullet> x)) *\<^sub>R x) 
          \<circ> (\<lambda>n. column (from_nat n) A)) [0..<to_nat (from_nat k::'n)]) $ from_nat i"
          unfolding o_def tn_fn_k ..
        finally show "IArray.list_of
          (column_iarray k (matrix_to_iarray A) -
          sum_list (map ((\<lambda>x. (column_iarray k (matrix_to_iarray A) \<bullet>i x / (x \<bullet>i x)) *\<^sub>R x) 
          \<circ> (\<lambda>n. column_iarray n (matrix_to_iarray A))) [0..<k])) ! i =
          column (from_nat k) A $ from_nat i -
          sum_list (map ((\<lambda>x. (column (from_nat k) A \<bullet> x / (x \<bullet> x)) *\<^sub>R x) 
          \<circ> (\<lambda>n. column (from_nat n) A)) [0..<to_nat (from_nat k::'n)]) $ from_nat i" .
      qed 
    qed
    also have "... = matrix_to_iarray (Gram_Schmidt_column_k_efficient A k) !! i !! ia"
      using matrix_to_iarray_nth[of "(Gram_Schmidt_column_k_efficient A k)" "from_nat i" "from_nat ia"] 
      using ia2 i2
      unfolding to_nat_from_nat_id[OF i2[unfolded nrows_def]] 
      unfolding to_nat_from_nat_id[OF ia2[unfolded ncols_def]] by simp
    finally show ?thesis ..
  qed
qed



lemma matrix_to_iarray_Gram_Schmidt_upt_k_efficient:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}" 
  assumes k: "k<ncols A"
  shows "matrix_to_iarray (Gram_Schmidt_upt_k A k) 
  = foldl Gram_Schmidt_column_k_iarrays_efficient (matrix_to_iarray A) [0..<Suc k]"
  using assms
proof (induct k)
  case 0
  have zero_le: "0<ncols A" unfolding ncols_def by simp
  thus ?case  unfolding Gram_Schmidt_upt_k_efficient[OF zero_le] unfolding Gram_Schmidt_upt_k_efficient
    by (simp add: matrix_to_iarray_Gram_Schmidt_column_k_efficient[OF "0.prems"])
next
  case (Suc k)
  let ?G="foldl Gram_Schmidt_column_k_iarrays_efficient (matrix_to_iarray A)"
  have k: "k<ncols (Gram_Schmidt_upt_k A k)" using Suc.prems unfolding ncols_def by simp
  have k2: "Suc k < ncols (Gram_Schmidt_upt_k A k)" using Suc.prems unfolding ncols_def .
  have list_rw: "[0..<Suc (Suc k)] = [0..<Suc k] @ [(Suc k)]" by simp
  have hyp: "matrix_to_iarray (Gram_Schmidt_upt_k A k) = ?G [0..<Suc k]"
    by (metis Suc.hyps Suc.prems Suc_lessD)
  show "matrix_to_iarray (Gram_Schmidt_upt_k A (Suc k)) = ?G [0..<Suc (Suc k)]"
    unfolding Gram_Schmidt_upt_k_def 
    unfolding list_rw
    unfolding foldl_append
    unfolding foldl.simps
    unfolding Gram_Schmidt_upt_k_def[symmetric]
    unfolding hyp[symmetric]
    using matrix_to_iarray_Gram_Schmidt_column_k_efficient
    by (metis (no_types) Gram_Schmidt_upt_k_efficient Gram_Schmidt_upt_k_efficient_induction 
      Suc.prems k matrix_to_iarray_Gram_Schmidt_column_k_efficient ncols_def)
qed


lemma matrix_to_iarray_Gram_Schmidt_matrix_efficient[code_unfold]:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}" 
  shows "matrix_to_iarray (Gram_Schmidt_matrix A) 
  = Gram_Schmidt_matrix_iarrays_efficient (matrix_to_iarray A)"
proof -
  have n: "ncols A - 1 < ncols A" unfolding ncols_def by auto
  thus ?thesis
    unfolding Gram_Schmidt_matrix_iarrays_efficient_def Gram_Schmidt_matrix_def 
    using matrix_to_iarray_Gram_Schmidt_upt_k_efficient[OF n]
    unfolding matrix_to_iarray_ncols by auto
qed

lemma QR_decomposition_iarrays_efficient[code]: 
  "QR_decomposition_iarrays (matrix_to_iarray A) 
  = QR_decomposition_iarrays_efficient (matrix_to_iarray A)"
  unfolding QR_decomposition_iarrays_def QR_decomposition_iarrays_efficient_def Let_def
  unfolding matrix_to_iarray_Gram_Schmidt_matrix_efficient[symmetric]
  unfolding matrix_to_iarray_Gram_Schmidt_matrix ..

subsection\<open>Other code equations that improve the performance\<close>

lemma inner_iarray_code[code]:
  "inner_iarray A B = sum_list (map (\<lambda>n. A !! n * B !! n) [0..<IArray.length A])"
proof -
  have set_Eq: "{0..<IArray.length A} = set ([0..<IArray.length A])" using atLeastLessThan_upt by blast
  have "inner_iarray A B = sum (\<lambda>n. A !! n * B !! n) {0..<IArray.length A}" 
    unfolding inner_iarray_def ..
  also have "... = sum (\<lambda>n. A !! n * B !! n) (set [0..<IArray.length A])"
    unfolding set_Eq ..
  also have "... = sum_list (map (\<lambda>n. A !! n * B !! n) [0..<IArray.length A])"
    unfolding sum_set_upt_conv_sum_list_nat ..
  finally show ?thesis .
qed


definition "Gram_Schmidt_column_k_iarrays_efficient2 A k = 
  tabulate2 (nrows_iarray A) (ncols_iarray A) 
  (let col_k = column_iarray k A;
       col = (col_k - sum_list (map (\<lambda>x. ((col_k \<bullet>i x) / (x \<bullet>i x)) *\<^sub>R x) 
              ((List.map (\<lambda>n. column_iarray n A) [0..<k]))))
  in (\<lambda>a b. (if b = k then col else column_iarray b A) !! a))"

lemma Gram_Schmidt_column_k_iarrays_efficient_eq[code]: "Gram_Schmidt_column_k_iarrays_efficient A k 
  = Gram_Schmidt_column_k_iarrays_efficient2 A k"
  unfolding Gram_Schmidt_column_k_iarrays_efficient_def
  unfolding Gram_Schmidt_column_k_iarrays_efficient2_def
  unfolding Let_def tabulate2_def
  by simp

end
