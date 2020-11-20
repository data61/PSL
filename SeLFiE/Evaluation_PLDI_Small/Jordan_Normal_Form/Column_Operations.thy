(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Elementary Column Operations\<close>

text \<open>We define elementary column operations and also combine them with elementary
  row operations. These combined operations are the basis to perform operations which
  preserve similarity of matrices. They are applied later on to convert upper triangular
  matrices into Jordan normal form.\<close>

theory Column_Operations
imports
  Gauss_Jordan_Elimination
begin

definition mat_multcol :: "nat \<Rightarrow> 'a :: semiring_1 \<Rightarrow> 'a mat \<Rightarrow> 'a mat" ("multcol") where
  "multcol k a A = mat (dim_row A) (dim_col A) 
     (\<lambda> (i,j). if k = j then a * A $$ (i,j) else A $$ (i,j))"

definition mat_swapcols :: "nat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" ("swapcols")where
  "swapcols k l A = mat (dim_row A) (dim_col A) 
    (\<lambda> (i,j). if k = j then A $$ (i,l) else if l = j then A $$ (i,k) else A $$ (i,j))"

definition mat_addcol_vec :: "nat \<Rightarrow> 'a :: plus vec \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where
  "mat_addcol_vec k v A = mat (dim_row A) (dim_col A) 
    (\<lambda> (i,j). if k = j then v $ i + A $$ (i,j) else A $$ (i,j))"

definition mat_addcol :: "'a :: semiring_1 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" ("addcol") where
  "addcol a k l A = mat (dim_row A) (dim_col A) 
    (\<lambda> (i,j). if k = j then a * A $$ (i,l) + A $$ (i,j) else A $$ (i,j))"

lemma index_mat_multcol[simp]: 
  "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> multcol k a A $$ (i,j) = (if k = j then a * A $$ (i,j) else A $$ (i,j))"
  "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> multcol j a A $$ (i,j) = a * A $$ (i,j)"
  "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> k \<noteq> j \<Longrightarrow> multcol k a A $$ (i,j) = A $$ (i,j)"
  "dim_row (multcol k a A) = dim_row A" "dim_col (multcol k a A) = dim_col A"
  unfolding mat_multcol_def by auto

lemma index_mat_swapcols[simp]: 
  "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> swapcols k l A $$ (i,j) = (if k = j then A $$ (i,l) else 
    if l = j then A $$ (i,k) else A $$ (i,j))"
  "dim_row (swapcols k l A) = dim_row A" "dim_col (swapcols k l A) = dim_col A"
  unfolding mat_swapcols_def by auto

lemma index_mat_addcol[simp]: 
  "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> addcol a k l A $$ (i,j) = (if k = j then 
    a * A $$ (i,l) + A $$ (i,j) else A $$ (i,j))"
  "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> addcol a j l A $$ (i,j) = a * A $$(i,l) + A$$(i,j)"
  "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> k \<noteq> j \<Longrightarrow> addcol a k l A $$ (i,j) = A $$(i,j)"
  "dim_row (addcol a k l A) = dim_row A" "dim_col (addcol a k l A) = dim_col A"
  unfolding mat_addcol_def by auto

text \<open>Each column-operation can be seen as a multiplication of 
  an elementary matrix from the right\<close>

lemma col_addrow: 
  "l \<noteq> i \<Longrightarrow> i < n \<Longrightarrow> col (addrow_mat n a k l) i = unit_vec n i"
  "k < n \<Longrightarrow> l < n \<Longrightarrow> col (addrow_mat n a k l) l = a \<cdot>\<^sub>v unit_vec n k + unit_vec n l" 
  by (rule eq_vecI, auto)

lemma col_addcol[simp]:
  "k < dim_col A \<Longrightarrow> l < dim_col A \<Longrightarrow> col (addcol a k l A) k = a \<cdot>\<^sub>v col A l + col A k"
  by (rule eq_vecI;simp)

lemma addcol_mat: assumes A: "A \<in> carrier_mat nr n" 
  and k: "k < n"
  shows "addcol (a :: 'a :: comm_semiring_1) l k A = A * addrow_mat n a k l"
  by (rule eq_matI, insert A k, auto simp: col_addrow
  scalar_prod_add_distrib[of _ n] scalar_prod_smult_distrib[of _ n])

lemma col_multrow:  "k \<noteq> i \<Longrightarrow> i < n \<Longrightarrow> col (multrow_mat n k a) i = unit_vec n i"
  "k < n \<Longrightarrow> col (multrow_mat n k a) k = a \<cdot>\<^sub>v unit_vec n k"
  by (rule eq_vecI, auto)

lemma multcol_mat: assumes A: "(A :: 'a :: comm_ring_1 mat) \<in> carrier_mat nr n"
  shows "multcol k a A = A * multrow_mat n k a"
  by (rule eq_matI, insert A, auto simp: col_multrow smult_scalar_prod_distrib[of _ n])

lemma col_swaprows: 
  "l < n \<Longrightarrow> col (swaprows_mat n l l) l = unit_vec n l"
  "i \<noteq> k \<Longrightarrow> i \<noteq> l \<Longrightarrow> i < n \<Longrightarrow> col (swaprows_mat n k l) i = unit_vec n i"
  "k < n \<Longrightarrow> l < n \<Longrightarrow> col (swaprows_mat n k l) l = unit_vec n k"
  "k < n \<Longrightarrow> l < n \<Longrightarrow> col (swaprows_mat n k l) k = unit_vec n l"
  by (rule eq_vecI, auto)

lemma swapcols_mat: assumes A: "A \<in> carrier_mat nr n" and k: "k < n" "l < n"
  shows "swapcols k l A = A * swaprows_mat n k l"
  by (rule eq_matI, insert A k, auto simp: col_swaprows)

text \<open>Combining row and column-operations yields similarity transformations.\<close>

definition add_col_sub_row :: "'a :: ring_1 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat"  where
  "add_col_sub_row a k l A = addrow (- a) k l (addcol a l k A)"

definition mult_col_div_row :: "'a :: field \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where
  "mult_col_div_row a k A = multrow k (inverse a) (multcol k a A)"

definition swap_cols_rows :: "nat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where
  "swap_cols_rows k l A = swaprows k l (swapcols k l A)"


lemma add_col_sub_row_carrier[simp]: 
  "dim_row (add_col_sub_row a k l A) = dim_row A"
  "dim_col (add_col_sub_row a k l A) = dim_col A"
  "A \<in> carrier_mat n n \<Longrightarrow> add_col_sub_row a k l A \<in> carrier_mat n n"
  unfolding add_col_sub_row_def carrier_mat_def by auto

lemma add_col_sub_index_row[simp]: 
  "i < dim_row A \<Longrightarrow> i < dim_col A \<Longrightarrow> j < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> l < dim_row A 
    \<Longrightarrow> add_col_sub_row a k l A $$ (i,j) = (if 
      i = k \<and> j = l then A $$ (i, j) + a * A $$ (i, i) - a * a * A $$ (j, i) - a * A $$ (j, j) else if
      i = k \<and> j \<noteq> l then A $$ (i, j) - a * A $$ (l, j) else if
      i \<noteq> k \<and> j = l then A $$ (i, j) + a * A $$ (i, k) else A $$ (i,j))"
  unfolding add_col_sub_row_def by (auto simp: field_simps)

lemma mult_col_div_index_row[simp]: 
  "i < dim_row A \<Longrightarrow> i < dim_col A \<Longrightarrow> j < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> a \<noteq> 0
    \<Longrightarrow> mult_col_div_row a k A $$ (i,j) = (if 
      i = k \<and> j \<noteq> i then inverse a * A $$ (i, j) else if
      j = k \<and> j \<noteq> i then a * A $$ (i, j) else A $$ (i,j))"
  unfolding mult_col_div_row_def by auto

lemma mult_col_div_row_carrier[simp]: 
  "dim_row (mult_col_div_row a k A) = dim_row A"
  "dim_col (mult_col_div_row a k A) = dim_col A"
  "A \<in> carrier_mat n n \<Longrightarrow> mult_col_div_row a k A \<in> carrier_mat n n"
  unfolding mult_col_div_row_def carrier_mat_def by auto

lemma swap_cols_rows_carrier[simp]: 
  "dim_row (swap_cols_rows k l A) = dim_row A"
  "dim_col (swap_cols_rows k l A) = dim_col A"
  "A \<in> carrier_mat n n \<Longrightarrow> swap_cols_rows k l A \<in> carrier_mat n n"
  unfolding swap_cols_rows_def carrier_mat_def by auto

lemma swap_cols_rows_index[simp]: 
  "i < dim_row A \<Longrightarrow> i < dim_col A \<Longrightarrow> j < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> a < dim_row A \<Longrightarrow> b < dim_row A 
    \<Longrightarrow> swap_cols_rows a b A $$ (i,j) = A $$ (if i = a then b else if i = b then a else i,
     if j = a then b else if j = b then a else j)"
  unfolding swap_cols_rows_def 
  by auto 

lemma add_col_sub_row_similar: assumes A: "A \<in> carrier_mat n n" and kl: "k < n" "l < n" "k \<noteq> l"
  shows "similar_mat (add_col_sub_row a k l A) (A :: 'a :: comm_ring_1 mat)"
proof (rule similar_matI)
  let ?P = "addrow_mat n (-a) k l"
  let ?Q = "addrow_mat n a k l"
  let ?B = "add_col_sub_row a k l A"
  show carr: "{?B, A, ?P, ?Q} \<subseteq> carrier_mat n n" using A by auto
  show "?Q * ?P = 1\<^sub>m n" by (rule addrow_mat_inv[OF kl])
  show "?P * ?Q = 1\<^sub>m n" using addrow_mat_inv[OF kl, of "-a"] by simp
  have col: "addcol a l k A = A * ?Q"
    by (rule addcol_mat[OF A kl(1)])
  have "?B = ?P * (A * ?Q)" unfolding add_col_sub_row_def col
    by (rule addrow_mat[OF _ kl(2), of _ n], insert A, simp)
  thus "?B = ?P * A * ?Q" using carr by (simp add: assoc_mult_mat[of _ n n _ n _ n])
qed

lemma mult_col_div_row_similar: assumes A: "A \<in> carrier_mat n n" and ak: "k < n" "a \<noteq> 0"
  shows "similar_mat (mult_col_div_row a k A) A"
proof (rule similar_matI)
  let ?P = "multrow_mat n k (inverse a)"
  let ?Q = "multrow_mat n k a"
  let ?B = "mult_col_div_row a k A"
  show carr: "{?B, A, ?P, ?Q} \<subseteq> carrier_mat n n" using A by auto
  show "?Q * ?P = 1\<^sub>m n" by (rule multrow_mat_inv[OF ak])
  show "?P * ?Q = 1\<^sub>m n" using multrow_mat_inv[OF ak(1), of "inverse a"] ak(2) by simp
  have col: "multcol k a A = A * ?Q"
    by (rule multcol_mat[OF A])
  have "?B = ?P * (A * ?Q)" unfolding mult_col_div_row_def col
    by (rule multrow_mat[of _ n n], insert A, simp)
  thus "?B = ?P * A * ?Q" using carr by (simp add: assoc_mult_mat[of _ n n _ n _ n])
qed

lemma swap_cols_rows_similar: assumes A: "A \<in> carrier_mat n n" and kl: "k < n" "l < n"
  shows "similar_mat (swap_cols_rows k l A) A"
proof (rule similar_matI)
  let ?P = "swaprows_mat n k l"
  let ?B = "swap_cols_rows k l A"
  show carr: "{?B, A, ?P, ?P} \<subseteq> carrier_mat n n" using A by auto
  show "?P * ?P = 1\<^sub>m n" by (rule swaprows_mat_inv[OF kl])
  show "?P * ?P = 1\<^sub>m n" by fact
  have col: "swapcols k l A = A * ?P"
    by (rule swapcols_mat[OF A kl])
  have "?B = ?P * (A * ?P)" unfolding swap_cols_rows_def col
    by (rule swaprows_mat[of _ n n ], insert A kl, auto)
  thus "?B = ?P * A * ?P" using carr by (simp add: assoc_mult_mat[of _ n n _ n _ n])
qed

(* THIS LINE SEPARATES AFP-ENTRY FROM NEWER DEVELOPMENTS *)

lemma swapcols_carrier[simp]: "(swapcols l k A \<in> carrier_mat n m) = (A \<in> carrier_mat n m)"
  unfolding mat_swapcols_def carrier_mat_def by auto

fun swap_row_to_front :: "'a mat \<Rightarrow> nat \<Rightarrow> 'a mat" where
  "swap_row_to_front A 0 = A"
| "swap_row_to_front A (Suc I) = swap_row_to_front (swaprows I (Suc I) A) I"

fun swap_col_to_front :: "'a mat \<Rightarrow> nat \<Rightarrow> 'a mat" where
  "swap_col_to_front A 0 = A"
| "swap_col_to_front A (Suc I) = swap_col_to_front (swapcols I (Suc I) A) I"

lemma swap_row_to_front_result: "A \<in> carrier_mat n m \<Longrightarrow> I < n \<Longrightarrow> swap_row_to_front A I = 
  mat n m (\<lambda> (i,j). if i = 0 then A $$ (I,j)
  else if i \<le> I then A $$ (i - 1, j) else A $$ (i,j))"
proof (induct I arbitrary: A)
  case 0
  thus ?case
    by (intro eq_matI, auto)
next
  case (Suc I A)
  from Suc(3) have I: "I < n" by auto
  let ?I = "Suc I"
  let ?A = "swaprows I ?I A"
  have AA: "?A \<in> carrier_mat n m" using Suc(2) by simp
  have "swap_row_to_front A (Suc I) = swap_row_to_front ?A I" by simp
  also have "\<dots> = mat n m
   (\<lambda>(i, j). if i = 0 then ?A $$ (I, j)
       else if i \<le> I then ?A $$ (i - 1, j) else ?A $$ (i, j))" 
     using Suc(1)[OF AA I] by simp
  also have "\<dots> = mat n m
   (\<lambda>(i, j). if i = 0 then A $$ (?I, j)
       else if i \<le> ?I then A $$ (i - 1, j) else A $$ (i, j))" 
    by (rule eq_matI, insert I Suc(2), auto)
  finally show ?case .
qed


lemma swap_col_to_front_result: "A \<in> carrier_mat n m \<Longrightarrow> J < m \<Longrightarrow> swap_col_to_front A J = 
  mat n m (\<lambda> (i,j). if j = 0 then A $$ (i,J)
  else if j \<le> J then A $$ (i, j-1) else A $$ (i,j))"
proof (induct J arbitrary: A)
  case 0
  thus ?case
    by (intro eq_matI, auto)
next
  case (Suc J A)
  from Suc(3) have J: "J < m" by auto
  let ?J = "Suc J"
  let ?A = "swapcols J ?J A"
  have AA: "?A \<in> carrier_mat n m" using Suc(2) by simp
  have "swap_col_to_front A (Suc J) = swap_col_to_front ?A J" by simp
  also have "\<dots> = mat n m
   (\<lambda>(i, j). if j = 0 then ?A $$ (i, J)
          else if j \<le> J then ?A $$ (i, j - 1) else ?A $$ (i, j))" 
     using Suc(1)[OF AA J] by simp
  also have "\<dots> = mat n m
   (\<lambda>(i, j). if j = 0 then A $$ (i, ?J)
          else if j \<le> ?J then A $$ (i, j - 1) else A $$ (i, j))" 
    by (rule eq_matI, insert J Suc(2), auto)
  finally show ?case .
qed

lemma swapcols_is_transp_swap_rows: assumes A: "A \<in> carrier_mat n m" "k < m" "l < m"
  shows "swapcols k l A = transpose_mat (swaprows k l (transpose_mat A))"
  using assms by (intro eq_matI, auto)



end
