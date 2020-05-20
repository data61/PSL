(* Author: Alexander Maletzky *)

section \<open>Macaulay Matrices\<close>

theory Macaulay_Matrix
  imports More_MPoly_Type_Class Jordan_Normal_Form.Gauss_Jordan_Elimination
begin

text \<open>We build upon vectors and matrices represented by dimension and characteristic function, because
  later on we need to quantify the dimensions of certain matrices existentially. This is not possible
  (at least not easily possible) with a type-based approach, as in HOL-Multivariate Analysis.\<close>

subsection \<open>More about Vectors\<close>

lemma vec_of_list_alt: "vec_of_list xs = vec (length xs) (nth xs)"
  by (transfer, rule refl)

lemma vec_cong:
  assumes "n = m" and "\<And>i. i < m \<Longrightarrow> f i = g i"
  shows "vec n f = vec m g"
  using assms by auto

lemma scalar_prod_comm:
  assumes "dim_vec v = dim_vec w"
  shows "v \<bullet> w = w \<bullet> (v::'a::comm_semiring_0 vec)"
  by (simp add: scalar_prod_def assms, rule sum.cong, rule refl, simp only: ac_simps)

lemma vec_scalar_mult_fun: "vec n (\<lambda>x. c * f x) = c \<cdot>\<^sub>v vec n f"
  by (simp add: smult_vec_def, rule vec_cong, rule refl, simp)

definition mult_vec_mat :: "'a vec \<Rightarrow> 'a :: semiring_0 mat \<Rightarrow> 'a vec" (infixl "\<^sub>v*" 70)
  where "v \<^sub>v* A \<equiv> vec (dim_col A) (\<lambda>j. v \<bullet> col A j)"

definition resize_vec :: "nat \<Rightarrow> 'a vec \<Rightarrow> 'a vec"
  where "resize_vec n v = vec n (vec_index v)"

lemma dim_resize_vec[simp]: "dim_vec (resize_vec n v) = n"
  by (simp add: resize_vec_def)

lemma resize_vec_carrier: "resize_vec n v \<in> carrier_vec n"
  by (simp add: carrier_dim_vec)

lemma resize_vec_dim[simp]: "resize_vec (dim_vec v) v = v"
  by (simp add: resize_vec_def eq_vecI)

lemma resize_vec_index:
  assumes "i < n"
  shows "resize_vec n v $ i = v $ i"
  using assms by (simp add: resize_vec_def)

lemma mult_mat_vec_resize:
  "v \<^sub>v* A = (resize_vec (dim_row A) v) \<^sub>v* A"
  by (simp add: mult_vec_mat_def scalar_prod_def, rule arg_cong2[of _ _ _ _ vec], rule, rule,
      rule sum.cong, rule, simp add: resize_vec_index)

lemma assoc_mult_vec_mat:
  assumes "v \<in> carrier_vec n1" and "A \<in> carrier_mat n1 n2" and "B \<in> carrier_mat n2 n3"
  shows "v \<^sub>v* (A * B) = (v \<^sub>v* A) \<^sub>v* B"
  using assms by (intro eq_vecI, auto simp add: mult_vec_mat_def mult_mat_vec_def assoc_scalar_prod)

lemma mult_vec_mat_transpose:
  assumes "dim_vec v = dim_row A"
  shows "v \<^sub>v* A = (transpose_mat A) *\<^sub>v (v::'a::comm_semiring_0 vec)"
proof (simp add: mult_vec_mat_def mult_mat_vec_def, rule vec_cong, rule refl, simp)
  fix j
  show "v \<bullet> col A j = col A j \<bullet> v" by (rule scalar_prod_comm, simp add: assms)
qed

subsection \<open>More about Matrices\<close>

definition nzrows :: "'a::zero mat \<Rightarrow> 'a vec list"
  where "nzrows A = filter (\<lambda>r. r \<noteq> 0\<^sub>v (dim_col A)) (rows A)"

definition row_space :: "'a mat \<Rightarrow> 'a::semiring_0 vec set"
  where "row_space A = (\<lambda>v. mult_vec_mat v A) ` (carrier_vec (dim_row A))"

definition row_echelon :: "'a mat \<Rightarrow> 'a::field mat"
  where "row_echelon A = fst (gauss_jordan A (1\<^sub>m (dim_row A)))"

subsubsection \<open>@{const nzrows}\<close>

lemma length_nzrows: "length (nzrows A) \<le> dim_row A"
  by (simp add: nzrows_def length_rows[symmetric] del: length_rows)

lemma set_nzrows: "set (nzrows A) = set (rows A) - {0\<^sub>v (dim_col A)}"
  by (auto simp add: nzrows_def)

lemma nzrows_nth_not_zero:
  assumes "i < length (nzrows A)"
  shows "nzrows A ! i \<noteq> 0\<^sub>v (dim_col A)"
  using assms unfolding nzrows_def using nth_mem by force

subsubsection \<open>@{const row_space}\<close>

lemma row_spaceI:
  assumes "x = v \<^sub>v* A"
  shows "x \<in> row_space A"
  unfolding row_space_def assms by (rule, fact mult_mat_vec_resize, fact resize_vec_carrier)

lemma row_spaceE:
  assumes "x \<in> row_space A"
  obtains v where "v \<in> carrier_vec (dim_row A)" and "x = v \<^sub>v* A"
  using assms unfolding row_space_def by auto

lemma row_space_alt: "row_space A = range (\<lambda>v. mult_vec_mat v A)"
proof
  show "row_space A \<subseteq> range (\<lambda>v. v \<^sub>v* A)" unfolding row_space_def by auto
next
  show "range (\<lambda>v. v \<^sub>v* A) \<subseteq> row_space A"
  proof
    fix x
    assume "x \<in> range (\<lambda>v. v \<^sub>v* A)"
    then obtain v where "x = v \<^sub>v* A" ..
    thus "x \<in> row_space A" by (rule row_spaceI)
  qed
qed

lemma row_space_mult:
  assumes "A \<in> carrier_mat nr nc" and "B \<in> carrier_mat nr nr"
  shows "row_space (B * A) \<subseteq> row_space A"
proof
  from assms(2) assms(1) have "B * A \<in> carrier_mat nr nc" by (rule mult_carrier_mat)
  hence "nr = dim_row (B * A)" by blast
  fix x
  assume "x \<in> row_space (B * A)"
  then obtain v where "v \<in> carrier_vec nr" and x: "x = v \<^sub>v* (B * A)"
    unfolding \<open>nr = dim_row (B * A)\<close> by (rule row_spaceE)
  from this(1) assms(2) assms(1) have "x = (v \<^sub>v* B) \<^sub>v* A" unfolding x by (rule assoc_mult_vec_mat)
  thus "x \<in> row_space A" by (rule row_spaceI)
qed

lemma row_space_mult_unit:
  assumes "P \<in> Units (ring_mat TYPE('a::semiring_1) (dim_row A) b)"
  shows "row_space (P * A) = row_space A"
proof -
  have A: "A \<in> carrier_mat (dim_row A) (dim_col A)" by simp
  from assms have P: "P \<in> carrier (ring_mat TYPE('a) (dim_row A) b)" and
    *: "\<exists>Q\<in>(carrier (ring_mat TYPE('a) (dim_row A) b)).
            Q \<otimes>\<^bsub>ring_mat TYPE('a) (dim_row A) b\<^esub> P = \<one>\<^bsub>ring_mat TYPE('a) (dim_row A) b\<^esub>"
    unfolding Units_def by auto
  from P have P_in: "P \<in> carrier_mat (dim_row A) (dim_row A)" by (simp add: ring_mat_def)
  from * obtain Q where "Q \<in> carrier (ring_mat TYPE('a) (dim_row A) b)"
    and "Q \<otimes>\<^bsub>ring_mat TYPE('a) (dim_row A) b\<^esub> P = \<one>\<^bsub>ring_mat TYPE('a) (dim_row A) b\<^esub>" ..
  hence Q_in: "Q \<in> carrier_mat (dim_row A) (dim_row A)" and QP: "Q * P = 1\<^sub>m (dim_row A)"
    by (simp_all add: ring_mat_def)
  show ?thesis
  proof
    from A P_in show "row_space (P * A) \<subseteq> row_space A" by (rule row_space_mult)
  next
    from A P_in Q_in have "Q * (P * A) = (Q * P) * A" by (simp only: assoc_mult_mat)
    also from A have "... = A" by (simp add: QP)
    finally have eq: "row_space A = row_space (Q * (P * A))" by simp
    show "row_space A \<subseteq> row_space (P * A)" unfolding eq by (rule row_space_mult, rule mult_carrier_mat, fact+)
  qed
qed

subsubsection \<open>@{const row_echelon}\<close>

lemma row_eq_zero_iff_pivot_fun:
  assumes "pivot_fun A f (dim_col A)" and "i < dim_row (A::'a::zero_neq_one mat)"
  shows "(row A i = 0\<^sub>v (dim_col A)) \<longleftrightarrow> (f i = dim_col A)"
proof -
  have *: "dim_row A = dim_row A" ..
  show ?thesis
  proof
    assume a: "row A i = 0\<^sub>v (dim_col A)"
    show "f i = dim_col A"
    proof (rule ccontr)
      assume "f i \<noteq> dim_col A"
      with pivot_funD(1)[OF * assms] have **: "f i < dim_col A" by simp
      with * assms have "A $$ (i, f i) = 1" by (rule pivot_funD)
      with ** assms(2) have "row A i $ (f i) = 1" by simp
      hence "(1::'a) = (0\<^sub>v (dim_col A)) $ (f i)" by (simp only: a)
      also have "... = (0::'a)" using ** by simp
      finally show False by simp
    qed
  next
    assume a: "f i = dim_col A"
    show "row A i = 0\<^sub>v (dim_col A)"
    proof (rule, simp_all add: assms(2))
      fix j
      assume "j < dim_col A"
      hence "j < f i" by (simp only: a)
      with * assms show "A $$ (i, j) = 0" by (rule pivot_funD)
    qed
  qed
qed

lemma row_not_zero_iff_pivot_fun:
  assumes "pivot_fun A f (dim_col A)" and "i < dim_row (A::'a::zero_neq_one mat)"
  shows "(row A i \<noteq> 0\<^sub>v (dim_col A)) \<longleftrightarrow> (f i < dim_col A)"
proof (simp only: row_eq_zero_iff_pivot_fun[OF assms])
  have "f i \<le> dim_col A" by (rule pivot_funD[where ?f = f], rule refl, fact+)
  thus "(f i \<noteq> dim_col A) = (f i < dim_col A)" by auto
qed

lemma pivot_fun_stabilizes:
  assumes "pivot_fun A f nc" and "i1 \<le> i2" and "i2 < dim_row A" and "nc \<le> f i1"
  shows "f i2 = nc"
proof -
  from assms(2) have "i2 = i1 + (i2 - i1)" by simp
  then obtain k where "i2 = i1 + k" ..
  from assms(3) assms(4) show ?thesis unfolding \<open>i2 = i1 + k\<close>
  proof (induct k arbitrary: i1)
    case 0
    from this(1) have "i1 < dim_row A" by simp
    from _ assms(1) this have "f i1 \<le> nc" by (rule pivot_funD, intro refl)
    with \<open>nc \<le> f i1\<close> show ?case by simp
  next
    case (Suc k)
    from Suc(2) have "Suc (i1 + k) < dim_row A" by simp
    hence "Suc i1 + k < dim_row A" by simp
    hence "Suc i1 < dim_row A" by simp
    hence "i1 < dim_row A" by simp
    have "nc \<le> f (Suc i1)"
    proof -
      have "f i1 < f (Suc i1) \<or> f (Suc i1) = nc" by (rule pivot_funD, rule refl, fact+)
      with Suc(3) show ?thesis by auto
    qed
    with \<open>Suc i1 + k < dim_row A\<close> have "f (Suc i1 + k) = nc" by (rule Suc(1))
    thus ?case by simp
  qed
qed

lemma pivot_fun_mono_strict:
  assumes "pivot_fun A f nc" and "i1 < i2" and "i2 < dim_row A" and "f i1 < nc"
  shows "f i1 < f i2"
proof -
  from assms(2) have "i2 - i1 \<noteq> 0" and "i2 = i1 + (i2 - i1)" by simp_all
  then obtain k where "k \<noteq> 0" and "i2 = i1 + k" ..
  from this(1) assms(3) assms(4) show ?thesis unfolding \<open>i2 = i1 + k\<close>
  proof (induct k arbitrary: i1)
    case 0
    thus ?case by simp
  next
    case (Suc k)
    from Suc(3) have "Suc (i1 + k) < dim_row A" by simp
    hence "Suc i1 + k < dim_row A" by simp
    hence "Suc i1 < dim_row A" by simp
    hence "i1 < dim_row A" by simp
    have *: "f i1 < f (Suc i1)"
    proof -
      have "f i1 < f (Suc i1) \<or> f (Suc i1) = nc" by (rule pivot_funD, rule refl, fact+)
      with Suc(4) show ?thesis by auto
    qed
    show ?case
    proof (simp, cases "k = 0")
      case True
      show "f i1 < f (Suc (i1 + k))" by (simp add: True *)
    next
      case False
      have "f (Suc i1) \<le> f (Suc i1 + k)"
      proof (cases "f (Suc i1) < nc")
        case True
        from False \<open>Suc i1 + k < dim_row A\<close> True have "f (Suc i1) < f (Suc i1 + k)" by (rule Suc(1))
        thus ?thesis by simp
      next
        case False
        hence "nc \<le> f (Suc i1)" by simp
        from assms(1) _ \<open>Suc i1 + k < dim_row A\<close> this have "f (Suc i1 + k) = nc"
          by (rule pivot_fun_stabilizes[where ?f=f], simp)
        moreover have "f (Suc i1) = nc" by (rule pivot_fun_stabilizes[where ?f=f], fact, rule le_refl, fact+)
        ultimately show ?thesis by simp
      qed
      also have "... = f (i1 + Suc k)" by simp
      finally have "f (Suc i1) \<le> f (i1 + Suc k)" .
      with * show "f i1 < f (Suc (i1 + k))" by simp
    qed
  qed
qed

lemma pivot_fun_mono:
  assumes "pivot_fun A f nc" and "i1 \<le> i2" and "i2 < dim_row A"
  shows "f i1 \<le> f i2"
proof -
  from assms(2) have "i1 < i2 \<or> i1 = i2" by auto
  thus ?thesis
  proof
    assume "i1 < i2"
    show ?thesis
    proof (cases "f i1 < nc")
      case True
      from assms(1) \<open>i1 < i2\<close> assms(3) this have "f i1 < f i2" by (rule pivot_fun_mono_strict)
      thus ?thesis by simp
    next
      case False
      hence "nc \<le> f i1" by simp
      from assms(1) _ _ this have "f i1 = nc"
      proof (rule pivot_fun_stabilizes[where ?f=f], simp)
        from assms(2) assms(3) show "i1 < dim_row A" by (rule le_less_trans)
      qed
      moreover have "f i2 = nc" by (rule pivot_fun_stabilizes[where ?f=f], fact+)
      ultimately show ?thesis by simp
    qed
  next
    assume "i1 = i2"
    thus ?thesis by simp
  qed
qed

lemma row_echelon_carrier:
  assumes "A \<in> carrier_mat nr nc"
  shows "row_echelon A \<in> carrier_mat nr nc"
proof -
  from assms have "dim_row A = nr" by simp
  let ?B = "1\<^sub>m (dim_row A)"
  note assms
  moreover have "?B \<in> carrier_mat nr nr" by (simp add: \<open>dim_row A = nr\<close>)
  moreover from surj_pair obtain A' B' where *: "gauss_jordan A ?B = (A', B')" by metis
  ultimately have "A' \<in> carrier_mat nr nc" by (rule gauss_jordan_carrier)
  thus ?thesis by (simp add: row_echelon_def *)
qed

lemma dim_row_echelon[simp]:
  shows "dim_row (row_echelon A) = dim_row A" and "dim_col (row_echelon A) = dim_col A"
proof -
  have "A \<in> carrier_mat (dim_row A) (dim_col A)" by simp
  hence "row_echelon A \<in> carrier_mat (dim_row A) (dim_col A)" by (rule row_echelon_carrier)
  thus "dim_row (row_echelon A) = dim_row A" and "dim_col (row_echelon A) = dim_col A" by simp_all
qed

lemma row_echelon_transform:
  obtains P where "P \<in> Units (ring_mat TYPE('a::field) (dim_row A) b)" and "row_echelon A = P * A"
proof -
  let ?B = "1\<^sub>m (dim_row A)"
  have "A \<in> carrier_mat (dim_row A) (dim_col A)" by simp
  moreover have "?B \<in> carrier_mat (dim_row A) (dim_row A)" by simp
  moreover from surj_pair obtain A' B' where *: "gauss_jordan A ?B = (A', B')" by metis
  ultimately have "\<exists>P\<in>Units (ring_mat TYPE('a) (dim_row A) b). A' = P * A \<and> B' = P * ?B"
    by (rule gauss_jordan_transform)
  then obtain P where "P \<in> Units (ring_mat TYPE('a) (dim_row A) b)" and **: "A' = P * A \<and> B' = P * ?B" ..
  from this(1) show ?thesis
  proof
    from ** have "A' = P * A" ..
    thus "row_echelon A = P * A" by (simp add: row_echelon_def *)
  qed
qed

lemma row_space_row_echelon[simp]: "row_space (row_echelon A) = row_space A"
proof -
  obtain P where *: "P \<in> Units (ring_mat TYPE('a::field) (dim_row A) Nil)" and **: "row_echelon A = P * A"
    by (rule row_echelon_transform)
  from * have "row_space (P * A) = row_space A" by (rule row_space_mult_unit)
  thus ?thesis by (simp only: **)
qed

lemma row_echelon_pivot_fun:
  obtains f where "pivot_fun (row_echelon A) f (dim_col (row_echelon A))"
proof -
  let ?B = "1\<^sub>m (dim_row A)"
  have "A \<in> carrier_mat (dim_row A) (dim_col A)" by simp
  moreover from surj_pair obtain A' B' where *: "gauss_jordan A ?B = (A', B')" by metis
  ultimately have "row_echelon_form A'" by (rule gauss_jordan_row_echelon)
  then obtain f where "pivot_fun A' f (dim_col A')" unfolding row_echelon_form_def ..
  hence "pivot_fun (row_echelon A) f (dim_col (row_echelon A))" by (simp add: row_echelon_def *)
  thus ?thesis ..
qed

lemma distinct_nzrows_row_echelon: "distinct (nzrows (row_echelon A))"
  unfolding nzrows_def
proof (rule distinct_filterI, simp del: dim_row_echelon)
  let ?B = "row_echelon A"
  fix i j::nat
  assume "i < j" and "j < dim_row ?B"
  hence "i \<noteq> j" and "i < dim_row ?B" by simp_all
  assume ri: "row ?B i \<noteq> 0\<^sub>v (dim_col ?B)" and rj: "row ?B j \<noteq> 0\<^sub>v (dim_col ?B)"
  obtain f where pf: "pivot_fun ?B f (dim_col ?B)" by (fact row_echelon_pivot_fun)
  from rj have "f j < dim_col ?B" by (simp only: row_not_zero_iff_pivot_fun[OF pf \<open>j < dim_row ?B\<close>])
  from _ pf \<open>j < dim_row ?B\<close> this \<open>i < dim_row ?B\<close> \<open>i \<noteq> j\<close> have *: "?B $$ (i, f j) = 0"
    by (rule pivot_funD(5), intro refl)
  show "row ?B i \<noteq> row ?B j"
  proof
    assume "row ?B i = row ?B j"
    hence "row ?B i $ (f j) = row ?B j $ (f j)" by simp
    with \<open>i < dim_row ?B\<close> \<open>j < dim_row ?B\<close> \<open>f j < dim_col ?B\<close> have "?B $$ (i, f j) = ?B $$ (j, f j)" by simp
    also from _ pf \<open>j < dim_row ?B\<close> \<open>f j < dim_col ?B\<close> have "... = 1" by (rule pivot_funD, intro refl)
    finally show False by (simp add: *)
  qed
qed

subsection \<open>Converting Between Polynomials and Macaulay Matrices\<close>

definition poly_to_row :: "'a list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> 'b vec" where
  "poly_to_row ts p = vec_of_list (map (lookup p) ts)"

definition polys_to_mat :: "'a list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::zero) list \<Rightarrow> 'b mat" where
  "polys_to_mat ts ps = mat_of_rows (length ts) (map (poly_to_row ts) ps)"

definition list_to_fun :: "'a list \<Rightarrow> ('b::zero) list \<Rightarrow> 'a \<Rightarrow> 'b" where
  "list_to_fun ts cs t = (case map_of (zip ts cs) t of Some c \<Rightarrow> c | None \<Rightarrow> 0)"

definition list_to_poly :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::zero)" where
  "list_to_poly ts cs = Abs_poly_mapping (list_to_fun ts cs)"

definition row_to_poly :: "'a list \<Rightarrow> 'b vec \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::zero)" where
  "row_to_poly ts r = list_to_poly ts (list_of_vec r)"

definition mat_to_polys :: "'a list \<Rightarrow> 'b mat \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::zero) list" where
  "mat_to_polys ts A = map (row_to_poly ts) (rows A)"

lemma dim_poly_to_row: "dim_vec (poly_to_row ts p) = length ts"
  by (simp add: poly_to_row_def)

lemma poly_to_row_index:
  assumes "i < length ts"
  shows "poly_to_row ts p $ i = lookup p (ts ! i)"
  by (simp add: poly_to_row_def vec_of_list_index assms)

context term_powerprod
begin

lemma poly_to_row_scalar_mult:
  assumes "keys p \<subseteq> set ts"
  shows "row_to_poly ts (c \<cdot>\<^sub>v (poly_to_row ts p)) = c \<cdot> p"
proof -
  have eq: "(vec (length ts) (\<lambda>i. c * poly_to_row ts p $ i)) =
        (vec (length ts) (\<lambda>i. c * lookup p (ts ! i)))"
    by (rule vec_cong, rule, simp only: poly_to_row_index)
  have *: "list_to_fun ts (list_of_vec (c \<cdot>\<^sub>v (poly_to_row ts p))) = (\<lambda>t. c * lookup p t)"
  proof (rule, simp add: list_to_fun_def smult_vec_def dim_poly_to_row eq,
        simp add: map_upt[of "\<lambda>x. c * lookup p x"] map_of_zip_map, rule)
    fix t
    assume "t \<notin> set ts"
    with assms(1) have "t \<notin> keys p" by auto
    thus "c * lookup p t = 0" by (simp add: in_keys_iff)
  qed
  have **: "lookup (Abs_poly_mapping (list_to_fun ts (list_of_vec (c \<cdot>\<^sub>v (poly_to_row ts p))))) =
            (\<lambda>t. c * lookup p t)"
  proof (simp only: *, rule Abs_poly_mapping_inverse, simp, rule finite_subset, rule, simp)
    fix t
    assume "c * lookup p t \<noteq> 0"
    hence "lookup p t \<noteq> 0" using mult_not_zero by blast 
    thus "t \<in> keys p" by (simp add: in_keys_iff)
  qed (fact finite_keys)
  show ?thesis unfolding row_to_poly_def
    by (rule poly_mapping_eqI) (simp only: list_to_poly_def ** lookup_map_scale)
qed

lemma poly_to_row_to_poly:
  assumes "keys p \<subseteq> set ts"
  shows "row_to_poly ts (poly_to_row ts p) = (p::'t \<Rightarrow>\<^sub>0 'b::semiring_1)"
proof -
  have "1 \<cdot>\<^sub>v (poly_to_row ts p) = poly_to_row ts p" by simp
  thus ?thesis using poly_to_row_scalar_mult[OF assms, of 1] by simp
qed

lemma lookup_list_to_poly: "lookup (list_to_poly ts cs) = list_to_fun ts cs"
  unfolding list_to_poly_def
proof (rule Abs_poly_mapping_inverse, rule, rule finite_subset)
  show "{x. list_to_fun ts cs x \<noteq> 0} \<subseteq> set ts"
  proof (rule, simp)
    fix t
    assume "list_to_fun ts cs t \<noteq> 0"
    then obtain c where "map_of (zip ts cs) t = Some c" unfolding list_to_fun_def by fastforce
    thus "t \<in> set ts" by (meson in_set_zipE map_of_SomeD)
  qed
qed simp

lemma list_to_fun_Nil [simp]: "list_to_fun [] cs = 0"
  by (simp only: zero_fun_def, rule, simp add: list_to_fun_def)

lemma list_to_poly_Nil [simp]: "list_to_poly [] cs = 0"
  by (rule poly_mapping_eqI, simp add: lookup_list_to_poly)

lemma row_to_poly_Nil [simp]: "row_to_poly [] r = 0"
  by (simp only: row_to_poly_def, fact list_to_poly_Nil)

lemma lookup_row_to_poly:
  assumes "distinct ts" and "dim_vec r = length ts" and "i < length ts"
  shows "lookup (row_to_poly ts r) (ts ! i) = r $ i"
proof (simp only: row_to_poly_def lookup_list_to_poly)
  from assms(2) assms(3) have "i < dim_vec r" by simp
  have "map_of (zip ts (list_of_vec r)) (ts ! i) = Some ((list_of_vec r) ! i)"
    by (rule map_of_zip_nth, simp_all only: length_list_of_vec assms(2), fact, fact)
  also have "... = Some (r $ i)" by (simp only: list_of_vec_index)
  finally show "list_to_fun ts (list_of_vec r) (ts ! i) = r $ i" by (simp add: list_to_fun_def)
qed

lemma keys_row_to_poly: "keys (row_to_poly ts r) \<subseteq> set ts"
proof
  fix t
  assume "t \<in> keys (row_to_poly ts r)"
  hence "lookup (row_to_poly ts r) t \<noteq> 0" by (simp add: in_keys_iff)
  thus "t \<in> set ts"
  proof (simp add: row_to_poly_def lookup_list_to_poly list_to_fun_def del: lookup_not_eq_zero_eq_in_keys
              split: option.splits)
    fix c
    assume "map_of (zip ts (list_of_vec r)) t = Some c"
    thus "t \<in> set ts" by (meson in_set_zipE map_of_SomeD)
  qed
qed

lemma lookup_row_to_poly_not_zeroE:
  assumes "lookup (row_to_poly ts r) t \<noteq> 0"
  obtains i where "i < length ts" and "t = ts ! i"
proof -
  from assms have "t \<in> keys (row_to_poly ts r)" by (simp add: in_keys_iff)
  have "t \<in> set ts" by (rule, fact, fact keys_row_to_poly)
  then obtain i where "i < length ts" and "t = ts ! i" by (metis in_set_conv_nth)
  thus ?thesis ..
qed

lemma row_to_poly_zero [simp]: "row_to_poly ts (0\<^sub>v (length ts)) = (0::'t \<Rightarrow>\<^sub>0 'b::zero)"
proof -
  have eq: "map (\<lambda>_. 0::'b) [0..<length ts] = map (\<lambda>_. 0) ts" by (simp add: map_replicate_const)
  show ?thesis
    by (simp add: row_to_poly_def zero_vec_def, rule poly_mapping_eqI,
      simp add: lookup_list_to_poly list_to_fun_def eq map_of_zip_map)
qed

lemma row_to_poly_zeroD:
  assumes "distinct ts" and "dim_vec r = length ts" and "row_to_poly ts r = 0"
  shows "r = 0\<^sub>v (length ts)"
proof (rule, simp_all add: assms(2))
  fix i
  assume "i < length ts"
  from assms(3) have "0 = lookup (row_to_poly ts r) (ts ! i)" by simp
  also from assms(1) assms(2) \<open>i < length ts\<close> have "... = r $ i" by (rule lookup_row_to_poly)
  finally show "r $ i = 0" by simp
qed

lemma row_to_poly_inj:
  assumes "distinct ts" and "dim_vec r1 = length ts" and "dim_vec r2 = length ts"
    and "row_to_poly ts r1 = row_to_poly ts r2"
  shows "r1 = r2"
proof (rule, simp_all add: assms(2) assms(3))
  fix i
  assume "i < length ts"
  have "r1 $ i = lookup (row_to_poly ts r1) (ts ! i)"
    by (simp only: lookup_row_to_poly[OF assms(1) assms(2) \<open>i < length ts\<close>])
  also from assms(4) have "... = lookup (row_to_poly ts r2) (ts ! i)" by simp
  also from assms(1) assms(3) \<open>i < length ts\<close> have "... = r2 $ i" by (rule lookup_row_to_poly)
  finally show "r1 $ i = r2 $ i" .
qed

lemma row_to_poly_vec_plus:
  assumes "distinct ts" and "length ts = n"
  shows "row_to_poly ts (vec n (f1 + f2)) = row_to_poly ts (vec n f1) + row_to_poly ts (vec n f2)"
proof (rule poly_mapping_eqI)
  fix t
  show "lookup (row_to_poly ts (vec n (f1 + f2))) t =
         lookup (row_to_poly ts (vec n f1) + row_to_poly ts (vec n f2)) t"
    (is "lookup ?l t = lookup (?r1 + ?r2) t")
  proof (cases "t \<in> set ts")
    case True
    then obtain j where j: "j < length ts" and t: "t = ts ! j" by (metis in_set_conv_nth)
    have d1: "dim_vec (vec n f1) = length ts" and d2: "dim_vec (vec n f2) = length ts"
      and da: "dim_vec (vec n (f1 + f2)) = length ts" by (simp_all add: assms(2))
    from j have j': "j < n" by (simp only: assms(2))
    show ?thesis
      by (simp only: t lookup_add lookup_row_to_poly[OF assms(1) d1 j]
              lookup_row_to_poly[OF assms(1) d2 j] lookup_row_to_poly[OF assms(1) da j] index_vec[OF j'],
             simp only: plus_fun_def)
  next
    case False
    with keys_row_to_poly[of ts "vec n (f1 + f2)"] keys_row_to_poly[of ts "vec n f1"]
      keys_row_to_poly[of ts "vec n f2"] have "t \<notin> keys ?l" and "t \<notin> keys ?r1" and "t \<notin> keys ?r2"
      by auto
    from this(2) this(3) have "t \<notin> keys (?r1 + ?r2)"
      by (meson Poly_Mapping.keys_add UnE in_mono) 
    with \<open>t \<notin> keys ?l\<close> show ?thesis by (simp add: in_keys_iff)
  qed
qed

lemma row_to_poly_vec_sum:
  assumes "distinct ts" and "length ts = n"
  shows "row_to_poly ts (vec n (\<lambda>j. \<Sum>i\<in>I. f i j)) = ((\<Sum>i\<in>I. row_to_poly ts (vec n (f i)))::'t \<Rightarrow>\<^sub>0 'b::comm_monoid_add)"
proof (cases "finite I")
  case True
  thus ?thesis
  proof (induct I)
    case empty
    thus ?case by (simp add: zero_vec_def[symmetric] assms(2)[symmetric])
  next
    case (insert x I)
    have "row_to_poly ts (vec n (\<lambda>j. \<Sum>i\<in>insert x I. f i j)) = row_to_poly ts (vec n (\<lambda>j. f x j + (\<Sum>i\<in>I. f i j)))"
      by (simp add: insert(1) insert(2))
    also have "... = row_to_poly ts (vec n (f x + (\<lambda>j. (\<Sum>i\<in>I. f i j))))" by (simp only: plus_fun_def)
    also from assms have "... = row_to_poly ts (vec n (f x)) + row_to_poly ts (vec n (\<lambda>j. (\<Sum>i\<in>I. f i j)))"
      by (rule row_to_poly_vec_plus)
    also have "... = row_to_poly ts (vec n (f x)) + (\<Sum>i\<in>I. row_to_poly ts (vec n (f i)))"
      by (simp only: insert(3))
    also have "... = (\<Sum>i\<in>insert x I. row_to_poly ts (vec n (f i)))"
      by (simp add: insert(1) insert(2))
    finally show ?case .
  qed
next
  case False
  thus ?thesis by (simp add: zero_vec_def[symmetric] assms(2)[symmetric])
qed

lemma row_to_poly_smult:
  assumes "distinct ts" and "dim_vec r = length ts"
  shows "row_to_poly ts (c \<cdot>\<^sub>v r) = c \<cdot> (row_to_poly ts r)"
proof (rule poly_mapping_eqI, simp only: lookup_map_scale)
  fix t
  show "lookup (row_to_poly ts (c \<cdot>\<^sub>v r)) t = c * lookup (row_to_poly ts r) t" (is "lookup ?l t = c * lookup ?r t")
  proof (cases "t \<in> set ts")
    case True
    then obtain j where j: "j < length ts" and t: "t = ts ! j" by (metis in_set_conv_nth)
    from assms(2) have dm: "dim_vec (c \<cdot>\<^sub>v r) = length ts" by simp
    from j have j': "j < dim_vec r" by (simp only: assms(2))
    show ?thesis
      by (simp add: t lookup_row_to_poly[OF assms j] lookup_row_to_poly[OF assms(1) dm j] index_smult_vec(1)[OF j'])
  next
    case False
    with keys_row_to_poly[of ts "c \<cdot>\<^sub>v r"] keys_row_to_poly[of ts r] have
      "t \<notin> keys ?l" and "t \<notin> keys ?r" by auto
    thus ?thesis by (simp add: in_keys_iff)
  qed
qed

lemma poly_to_row_Nil [simp]: "poly_to_row [] p = vec 0 f"
proof -
  have "dim_vec (poly_to_row [] p) = 0" by (simp add: dim_poly_to_row)
  thus ?thesis by auto
qed

lemma polys_to_mat_Nil [simp]: "polys_to_mat ts [] = mat 0 (length ts) f"
  by (simp add: polys_to_mat_def mat_eq_iff)

lemma dim_row_polys_to_mat[simp]: "dim_row (polys_to_mat ts ps) = length ps"
  by (simp add: polys_to_mat_def)

lemma dim_col_polys_to_mat[simp]: "dim_col (polys_to_mat ts ps) = length ts"
  by (simp add: polys_to_mat_def)

lemma polys_to_mat_index:
  assumes "i < length ps" and "j < length ts"
  shows "(polys_to_mat ts ps) $$ (i, j) = lookup (ps ! i) (ts ! j)"
  by (simp add: polys_to_mat_def index_mat(1)[OF assms] mat_of_rows_def nth_map[OF assms(1)],
      rule poly_to_row_index, fact)

lemma row_polys_to_mat:
  assumes "i < length ps"
  shows "row (polys_to_mat ts ps) i = poly_to_row ts (ps ! i)"
proof -
  have "row (polys_to_mat ts ps) i = (map (poly_to_row ts) ps) ! i" unfolding polys_to_mat_def
  proof (rule mat_of_rows_row)
    from assms show "i < length (map (poly_to_row ts) ps)" by simp
  next
    show "map (poly_to_row ts) ps ! i \<in> carrier_vec (length ts)" unfolding nth_map[OF assms]
      by (rule carrier_vecI, fact dim_poly_to_row)
  qed
  also from assms have "... = poly_to_row ts (ps ! i)" by (rule nth_map)
  finally show ?thesis .
qed

lemma col_polys_to_mat:
  assumes "j < length ts"
  shows "col (polys_to_mat ts ps) j = vec_of_list (map (\<lambda>p. lookup p (ts ! j)) ps)"
  by (simp add: vec_of_list_alt col_def, rule vec_cong, rule refl, simp add: polys_to_mat_index assms)

lemma length_mat_to_polys[simp]: "length (mat_to_polys ts A) = dim_row A"
  by (simp add: mat_to_polys_def mat_to_list_def)

lemma mat_to_polys_nth:
  assumes "i < dim_row A"
  shows "(mat_to_polys ts A) ! i = row_to_poly ts (row A i)"
proof -
  from assms have "i < length (rows A)" by (simp only: length_rows)
  thus ?thesis by (simp add: mat_to_polys_def)
qed

lemma Keys_mat_to_polys: "Keys (set (mat_to_polys ts A)) \<subseteq> set ts"
proof
  fix t
  assume "t \<in> Keys (set (mat_to_polys ts A))"
  then obtain p where "p \<in> set (mat_to_polys ts A)" and t: "t \<in> keys p" by (rule in_KeysE)
  from this(1) obtain i where "i < length (mat_to_polys ts A)" and p: "p = (mat_to_polys ts A) ! i"
    by (metis in_set_conv_nth)
  from this(1) have "i < dim_row A" by simp
  with p have "p = row_to_poly ts (row A i)" by (simp only: mat_to_polys_nth)
  with t have "t \<in> keys (row_to_poly ts (row A i))" by simp
  also have "... \<subseteq> set ts" by (fact keys_row_to_poly)
  finally show "t \<in> set ts" .
qed

lemma polys_to_mat_to_polys:
  assumes "Keys (set ps) \<subseteq> set ts"
  shows "mat_to_polys ts (polys_to_mat ts ps) = (ps::('t \<Rightarrow>\<^sub>0 'b::semiring_1) list)"
  unfolding mat_to_polys_def mat_to_list_def
proof (rule nth_equalityI, simp_all)
  fix i
  assume "i < length ps"
  have *: "keys (ps ! i) \<subseteq> set ts"
    using \<open>i < length ps\<close> assms keys_subset_Keys nth_mem by blast
  show "row_to_poly ts (row (polys_to_mat ts ps) i) = ps ! i"
    by (simp only: row_polys_to_mat[OF \<open>i < length ps\<close>] poly_to_row_to_poly[OF *])
qed

lemma mat_to_polys_to_mat:
  assumes "distinct ts" and "length ts = dim_col A"
  shows "(polys_to_mat ts (mat_to_polys ts A)) = A"
proof
  fix i j
  assume i: "i < dim_row A" and j: "j < dim_col A"
  hence i': "i < length (mat_to_polys ts A)" and j': "j < length ts" by (simp, simp only: assms(2))
  have r: "dim_vec (row A i) = length ts" by (simp add: assms(2))
  show "polys_to_mat ts (mat_to_polys ts A) $$ (i, j) = A $$ (i, j)"
    by (simp only: polys_to_mat_index[OF i' j'] mat_to_polys_nth[OF \<open>i < dim_row A\<close>]
        lookup_row_to_poly[OF assms(1) r j'] index_row(1)[OF i j])
qed (simp_all add: assms)

subsection \<open>Properties of Macaulay Matrices\<close>

lemma row_to_poly_vec_times:
  assumes "distinct ts" and "length ts = dim_col A"
  shows "row_to_poly ts (v \<^sub>v* A) = ((\<Sum>i=0..<dim_row A. (v $ i) \<cdot> (row_to_poly ts (row A i)))::'t \<Rightarrow>\<^sub>0 'b::comm_semiring_0)"
proof (simp add: mult_vec_mat_def scalar_prod_def row_to_poly_vec_sum[OF assms], rule sum.cong, rule)
  fix i
  assume "i \<in> {0..<dim_row A}"
  hence "i < dim_row A" by simp
  have "dim_vec (row A i) = length ts" by (simp add: assms(2))
  have *: "vec (dim_col A) (\<lambda>j. col A j $ i) = vec (dim_col A) (\<lambda>j. A $$ (i, j))"
    by (rule vec_cong, rule refl, simp add: \<open>i < dim_row A\<close>)
  have "vec (dim_col A) (\<lambda>j. v $ i * col A j $ i) = v $ i \<cdot>\<^sub>v vec (dim_col A) (\<lambda>j. col A j $ i)"
    by (simp only: vec_scalar_mult_fun)
  also have "... = v $ i \<cdot>\<^sub>v (row A i)" by (simp only: * row_def[symmetric])
  finally show "row_to_poly ts (vec (dim_col A) (\<lambda>j. v $ i * col A j $ i)) =
                  (v $ i) \<cdot> (row_to_poly ts (row A i))"
    by (simp add: row_to_poly_smult[OF assms(1) \<open>dim_vec (row A i) = length ts\<close>])
qed

lemma vec_times_polys_to_mat:
  assumes "Keys (set ps) \<subseteq> set ts" and "v \<in> carrier_vec (length ps)"
  shows "row_to_poly ts (v \<^sub>v* (polys_to_mat ts ps)) = (\<Sum>(c, p)\<leftarrow>zip (list_of_vec v) ps. c \<cdot> p)"
    (is "?l = ?r")
proof -
  from assms have *: "dim_vec v = length ps" by (simp only: carrier_dim_vec)
  have eq: "map (\<lambda>i. v \<bullet> col (polys_to_mat ts ps) i) [0..<length ts] =
            map (\<lambda>s. v \<bullet> (vec_of_list (map (\<lambda>p. lookup p s) ps))) ts"
  proof (rule nth_equalityI, simp_all)
    fix i
    assume "i < length ts"
    hence "col (polys_to_mat ts ps) i = vec_of_list (map (\<lambda>p. lookup p (ts ! i)) ps)"
      by (rule col_polys_to_mat)
    thus "v \<bullet> col (polys_to_mat ts ps) i = v \<bullet> map_vec (\<lambda>p. lookup p (ts ! i)) (vec_of_list ps)"
      by simp
  qed
  show ?thesis
  proof (rule poly_mapping_eqI, simp add: mult_vec_mat_def row_to_poly_def lookup_list_to_poly
      eq list_to_fun_def map_of_zip_map lookup_sum_list o_def, intro conjI impI)
    fix t
    assume "t \<in> set ts"
    have "v \<bullet> vec_of_list (map (\<lambda>p. lookup p t) ps) =
          (\<Sum>(c, p)\<leftarrow>zip (list_of_vec v) ps. lookup (c \<cdot> p) t)"
    proof (simp add: scalar_prod_def vec_of_list_index)
      have "(\<Sum>i = 0..<length ps. v $ i * lookup (ps ! i) t) =
            (\<Sum>i = 0..<length ps. (list_of_vec v) ! i * lookup (ps ! i) t)"
        by (rule sum.cong, rule refl, simp add: *)
      also have "... = (\<Sum>(c, p)\<leftarrow>zip (list_of_vec v) ps. c * lookup p t)"
        by (simp only: sum_set_upt_eq_sum_list, rule sum_list_upt_zip, simp only: length_list_of_vec *)
      finally show "(\<Sum>i = 0..<length ps. v $ i * lookup (ps ! i) t) =
                    (\<Sum>(c, p)\<leftarrow>zip (list_of_vec v) ps. c * lookup p t)" .
    qed
    thus "v \<bullet> map_vec (\<lambda>p. lookup p t) (vec_of_list ps) =
          (\<Sum>x\<leftarrow>zip (list_of_vec v) ps. lookup (case x of (c, x) \<Rightarrow> c \<cdot> x) t)"
      by (metis (mono_tags, lifting) case_prod_conv cond_case_prod_eta vec_of_list_map)
  next
    fix t
    assume "t \<notin> set ts"
    with assms(1) have "t \<notin> Keys (set ps)" by auto
    have "(\<Sum>(c, p)\<leftarrow>zip (list_of_vec v) ps. lookup (c \<cdot> p) t) = 0"
    proof (rule sum_list_zeroI, rule, simp)
      fix x
      assume "x \<in> (\<lambda>(c, p). c * lookup p t) ` set (zip (list_of_vec v) ps)"
      then obtain c p where cp: "(c, p) \<in> set (zip (list_of_vec v) ps)"
        and x: "x = c * lookup p t" by auto
      from cp have "p \<in> set ps" by (rule set_zip_rightD)
      with \<open>t \<notin> Keys (set ps)\<close> have "t \<notin> keys p" by (auto intro: in_KeysI)
      thus "x = 0" by (simp add: x in_keys_iff)
    qed
    thus "(\<Sum>x\<leftarrow>zip (list_of_vec v) ps. lookup (case x of (c, x) \<Rightarrow> c \<cdot> x) t) = 0"
      by (metis (mono_tags, lifting) case_prod_conv cond_case_prod_eta)
  qed
qed

lemma row_space_subset_phull:
  assumes "Keys (set ps) \<subseteq> set ts"
  shows "row_to_poly ts ` row_space (polys_to_mat ts ps) \<subseteq> phull (set ps)"
    (is "?r \<subseteq> ?h")
proof
  fix q
  assume "q \<in> ?r"
  then obtain x where x1: "x \<in> row_space (polys_to_mat ts ps)"
    and q1: "q = row_to_poly ts x" ..
  from x1 obtain v where v: "v \<in> carrier_vec (dim_row (polys_to_mat ts ps))" and x: "x = v \<^sub>v* polys_to_mat ts ps"
    by (rule row_spaceE)
  from v have "v \<in> carrier_vec (length ps)" by (simp only: dim_row_polys_to_mat)
  thm vec_times_polys_to_mat
  with x q1 have q: "q = (\<Sum>(c, p)\<leftarrow>zip (list_of_vec v) ps. c \<cdot> p)"
    by (simp add: vec_times_polys_to_mat[OF assms])
  show "q \<in> ?h" unfolding q by (rule phull.span_listI)
qed

lemma phull_subset_row_space:
  assumes "Keys (set ps) \<subseteq> set ts"
  shows "phull (set ps) \<subseteq> row_to_poly ts ` row_space (polys_to_mat ts ps)"
    (is "?h \<subseteq> ?r")
proof
  fix q
  assume "q \<in> ?h"
  then obtain cs where l: "length cs = length ps" and q: "q = (\<Sum>(c, p)\<leftarrow>zip cs ps. c \<cdot> p)"
    by (rule phull.span_listE)
  let ?v = "vec_of_list cs"
  from l have *: "?v \<in> carrier_vec (length ps)" by (simp only: carrier_dim_vec dim_vec_of_list)
  let ?q = "?v \<^sub>v* polys_to_mat ts ps"
  show "q \<in> ?r"
  proof
    show "q = row_to_poly ts ?q"
      by (simp add: vec_times_polys_to_mat[OF assms *] q list_vec)
  next
    show "?q \<in> row_space (polys_to_mat ts ps)" by (rule row_spaceI, rule)
  qed
qed

lemma row_space_eq_phull:
  assumes "Keys (set ps) \<subseteq> set ts"
  shows "row_to_poly ts ` row_space (polys_to_mat ts ps) = phull (set ps)"
  by (rule, rule row_space_subset_phull, fact, rule phull_subset_row_space, fact)

lemma row_space_row_echelon_eq_phull:
  assumes "Keys (set ps) \<subseteq> set ts"
  shows "row_to_poly ts ` row_space (row_echelon (polys_to_mat ts ps)) = phull (set ps)"
  by (simp add: row_space_eq_phull[OF assms])

lemma phull_row_echelon:
  assumes "Keys (set ps) \<subseteq> set ts" and "distinct ts"
  shows "phull (set (mat_to_polys ts (row_echelon (polys_to_mat ts ps)))) = phull (set ps)"
proof -
  have len_ts: "length ts = dim_col (row_echelon (polys_to_mat ts ps))" by simp
  have *: "Keys (set (mat_to_polys ts (row_echelon (polys_to_mat ts ps)))) \<subseteq> set ts"
    by (fact Keys_mat_to_polys)
  show ?thesis
    by (simp only: row_space_eq_phull[OF *, symmetric] mat_to_polys_to_mat[OF assms(2) len_ts],
        rule row_space_row_echelon_eq_phull, fact)
qed

lemma pmdl_row_echelon:
  assumes "Keys (set ps) \<subseteq> set ts" and "distinct ts"
  shows "pmdl (set (mat_to_polys ts (row_echelon (polys_to_mat ts ps)))) = pmdl (set ps)"
    (is "?l = ?r")
proof
  show "?l \<subseteq> ?r"
    by (rule pmdl.span_subset_spanI, rule subset_trans, rule phull.span_superset,
      simp only: phull_row_echelon[OF assms] phull_subset_module)
next
  show "?r \<subseteq> ?l"
    by (rule pmdl.span_subset_spanI, rule subset_trans, rule phull.span_superset,
        simp only: phull_row_echelon[OF assms, symmetric] phull_subset_module)
qed

end (* term_powerprod *)

context ordered_term
begin

lemma lt_row_to_poly_pivot_fun:
  assumes "card S = dim_col (A::'b::semiring_1 mat)" and "pivot_fun A f (dim_col A)"
    and "i < dim_row A" and "f i < dim_col A"
  shows "lt ((mat_to_polys (pps_to_list S) A) ! i) = (pps_to_list S) ! (f i)"
proof -
  let ?ts = "pps_to_list S"
  have len_ts: "length ?ts = dim_col A" by (simp add: length_pps_to_list assms(1))
  show ?thesis
  proof (simp add: mat_to_polys_nth[OF assms(3)], rule lt_eqI)
    have "lookup (row_to_poly ?ts (row A i)) (?ts ! f i) = (row A i) $ (f i)"
      by (rule lookup_row_to_poly, fact distinct_pps_to_list, simp_all add: len_ts assms(4))
    also have "... = A $$ (i, f i)" using assms(3) assms(4) by simp
    also have "... = 1" by (rule pivot_funD, rule refl, fact+)
    finally show "lookup (row_to_poly ?ts (row A i)) (?ts ! f i) \<noteq> 0" by simp
  next
    fix u
    assume a: "lookup (row_to_poly ?ts (row A i)) u \<noteq> 0"
    then obtain j where j: "j < length ?ts" and u: "u = ?ts ! j"
      by (rule lookup_row_to_poly_not_zeroE)
    from j have "j < card S" and "j < dim_col A" by (simp only: length_pps_to_list, simp only: len_ts)
    from a have "0 \<noteq> lookup (row_to_poly ?ts (row A i)) (?ts ! j)" by (simp add: u)
    also have "lookup (row_to_poly ?ts (row A i)) (?ts ! j) = (row A i) $ j"
      by (rule lookup_row_to_poly, fact distinct_pps_to_list, simp add: len_ts, fact)
    finally have "A $$ (i, j) \<noteq> 0" using assms(3) \<open>j < dim_col A\<close> by simp
    from _ \<open>j < card S\<close> show "u \<preceq>\<^sub>t ?ts ! f i" unfolding u
    proof (rule pps_to_list_nth_leI)
      show "f i \<le> j"
      proof (rule ccontr)
        assume "\<not> f i \<le> j"
        hence "j < f i" by simp
        have "A $$ (i, j) = 0" by (rule pivot_funD, rule refl, fact+)
        with \<open>A $$ (i, j) \<noteq> 0\<close> show False ..
      qed
    qed
  qed
qed

lemma lc_row_to_poly_pivot_fun:
  assumes "card S = dim_col (A::'b::semiring_1 mat)" and "pivot_fun A f (dim_col A)"
    and "i < dim_row A" and "f i < dim_col A"
  shows "lc ((mat_to_polys (pps_to_list S) A) ! i) = 1"
proof -
  let ?ts = "pps_to_list S"
  have len_ts: "length ?ts = dim_col A" by (simp only: length_pps_to_list assms(1))
  have "lookup (row_to_poly ?ts (row A i)) (?ts ! f i) = (row A i) $ (f i)"
    by (rule lookup_row_to_poly, fact distinct_pps_to_list, simp_all add: len_ts assms(4))
  also have "... = A $$ (i, f i)" using assms(3) assms(4) by simp
  finally have eq: "lookup (row_to_poly ?ts (row A i)) (?ts ! f i) = A $$ (i, f i)" .
  show ?thesis
    by (simp only: lc_def lt_row_to_poly_pivot_fun[OF assms], simp only: mat_to_polys_nth[OF assms(3)] eq,
        rule pivot_funD, rule refl, fact+)
qed

lemma lt_row_to_poly_pivot_fun_less:
  assumes "card S = dim_col (A::'b::semiring_1 mat)" and "pivot_fun A f (dim_col A)"
    and "i1 < i2" and "i2 < dim_row A" and "f i1 < dim_col A" and "f i2 < dim_col A"
  shows "(pps_to_list S) ! (f i2) \<prec>\<^sub>t (pps_to_list S) ! (f i1)"
proof -
  let ?ts = "pps_to_list S"
  have len_ts: "length ?ts = dim_col A" by (simp add: length_pps_to_list assms(1))
  from assms(3) assms(4) have "i1 < dim_row A" by simp
  show ?thesis
    by (rule pps_to_list_nth_lessI, rule pivot_fun_mono_strict[where ?f=f], fact, fact, fact, fact,
        simp only: assms(1) assms(6))
qed

lemma lt_row_to_poly_pivot_fun_eqD:
  assumes "card S = dim_col (A::'b::semiring_1 mat)" and "pivot_fun A f (dim_col A)"
    and "i1 < dim_row A" and "i2 < dim_row A" and "f i1 < dim_col A" and "f i2 < dim_col A"
    and "(pps_to_list S) ! (f i1) = (pps_to_list S) ! (f i2)"
  shows "i1 = i2"
proof (rule linorder_cases)
  assume "i1 < i2"
  from assms(1) assms(2) this assms(4) assms(5) assms(6) have
    "(pps_to_list S) ! (f i2) \<prec>\<^sub>t (pps_to_list S) ! (f i1)" by (rule lt_row_to_poly_pivot_fun_less)
  with assms(7) show ?thesis by auto
next
  assume "i2 < i1"
  from assms(1) assms(2) this assms(3) assms(6) assms(5) have
    "(pps_to_list S) ! (f i1) \<prec>\<^sub>t (pps_to_list S) ! (f i2)" by (rule lt_row_to_poly_pivot_fun_less)
  with assms(7) show ?thesis by auto
qed

lemma lt_row_to_poly_pivot_in_keysD:
  assumes "card S = dim_col (A::'b::semiring_1 mat)" and "pivot_fun A f (dim_col A)"
    and "i1 < dim_row A" and "i2 < dim_row A" and "f i1 < dim_col A"
    and "(pps_to_list S) ! (f i1) \<in> keys ((mat_to_polys (pps_to_list S) A) ! i2)"
  shows "i1 = i2"
proof (rule ccontr)
  assume "i1 \<noteq> i2"
  hence "i2 \<noteq> i1" by simp
  let ?ts = "pps_to_list S"
  have len_ts: "length ?ts = dim_col A" by (simp only: length_pps_to_list assms(1))
  from assms(6) have "0 \<noteq> lookup (row_to_poly ?ts (row A i2)) (?ts ! (f i1))"
    by (auto simp: mat_to_polys_nth[OF assms(4)])
  also have "lookup (row_to_poly ?ts (row A i2)) (?ts ! (f i1)) = (row A i2) $ (f i1)"
    by (rule lookup_row_to_poly, fact distinct_pps_to_list, simp_all add: len_ts assms(5))
  finally have "A $$ (i2, f i1) \<noteq> 0" using assms(4) assms(5) by simp
  moreover have "A $$ (i2, f i1) = 0" by (rule pivot_funD(5), rule refl, fact+)
  ultimately show False ..
qed

lemma lt_row_space_pivot_fun:
  assumes "card S = dim_col (A::'b::{comm_semiring_0,semiring_1_no_zero_divisors} mat)"
    and "pivot_fun A f (dim_col A)" and "p \<in> row_to_poly (pps_to_list S) ` row_space A" and "p \<noteq> 0"
  shows "lt p \<in> lt_set (set (mat_to_polys (pps_to_list S) A))"
proof -
  let ?ts = "pps_to_list S"
  let ?I = "{0..<dim_row A}"
  have len_ts: "length ?ts = dim_col A" by (simp add: length_pps_to_list assms(1))
  from assms(3) obtain x where "x \<in> row_space A" and p: "p = row_to_poly ?ts x" ..
  from this(1) obtain v where "v \<in> carrier_vec (dim_row A)" and x: "x = v \<^sub>v* A" by (rule row_spaceE)
  
  have p': "p = (\<Sum>i\<in>?I. (v $ i) \<cdot> (row_to_poly ?ts (row A i)))"
    unfolding p x by (rule row_to_poly_vec_times, fact distinct_pps_to_list, fact len_ts)

  have "lt (\<Sum>i = 0..<dim_row A. (v $ i) \<cdot> (row_to_poly ?ts (row A i)))
          \<in> lt_set ((\<lambda>i. (v $ i) \<cdot> (row_to_poly ?ts (row A i))) ` {0..<dim_row A})"
  proof (rule lt_sum_distinct_in_lt_set, rule, simp add: p'[symmetric] \<open>p \<noteq> 0\<close>)
    fix i1 i2
    let ?p1 = "(v $ i1) \<cdot> (row_to_poly ?ts (row A i1))"
    let ?p2 = "(v $ i2) \<cdot> (row_to_poly ?ts (row A i2))"
    assume "i1 \<in> ?I" and "i2 \<in> ?I"
    hence "i1 < dim_row A" and "i2 < dim_row A" by simp_all

    assume "?p1 \<noteq> 0"
    hence "v $ i1 \<noteq> 0" and "row_to_poly ?ts (row A i1) \<noteq> 0" by auto
    hence "row A i1 \<noteq> 0\<^sub>v (length ?ts)" by auto
    hence "f i1 < dim_col A"
      by (simp add: len_ts row_not_zero_iff_pivot_fun[OF assms(2) \<open>i1 < dim_row A\<close>])
    have "lt ?p1 = lt (row_to_poly ?ts (row A i1))" by (rule lt_map_scale, fact)
    also have "... = lt ((mat_to_polys ?ts A) ! i1)" by (simp only: mat_to_polys_nth[OF \<open>i1 < dim_row A\<close>])
    also have "... = ?ts ! (f i1)" by (rule lt_row_to_poly_pivot_fun, fact+)
    finally have lt1: "lt ?p1 = ?ts ! (f i1)" .

    assume "?p2 \<noteq> 0"
    hence "v $ i2 \<noteq> 0" and "row_to_poly ?ts (row A i2) \<noteq> 0" by auto
    hence "row A i2 \<noteq> 0\<^sub>v (length ?ts)" by auto
    hence "f i2 < dim_col A"
      by (simp add: len_ts row_not_zero_iff_pivot_fun[OF assms(2) \<open>i2 < dim_row A\<close>])
    have "lt ?p2 = lt (row_to_poly ?ts (row A i2))" by (rule lt_map_scale, fact)
    also have "... = lt ((mat_to_polys ?ts A) ! i2)" by (simp only: mat_to_polys_nth[OF \<open>i2 < dim_row A\<close>])
    also have "... = ?ts ! (f i2)" by (rule lt_row_to_poly_pivot_fun, fact+)
    finally have lt2: "lt ?p2 = ?ts ! (f i2)" .

    assume "lt ?p1 = lt ?p2"
    with assms(1) assms(2) \<open>i1 < dim_row A\<close> \<open>i2 < dim_row A\<close> \<open>f i1 < dim_col A\<close> \<open>f i2 < dim_col A\<close>
    show "i1 = i2" unfolding lt1 lt2 by (rule lt_row_to_poly_pivot_fun_eqD)
  qed
  also have "... \<subseteq> lt_set ((\<lambda>i. row_to_poly ?ts (row A i)) ` {0..<dim_row A})"
  proof
    fix s
    assume "s \<in> lt_set ((\<lambda>i. (v $ i) \<cdot> (row_to_poly ?ts (row A i))) ` {0..<dim_row A})"
    then obtain f
      where "f \<in> (\<lambda>i. (v $ i) \<cdot> (row_to_poly ?ts (row A i))) ` {0..<dim_row A}"
        and "f \<noteq> 0" and "lt f = s" by (rule lt_setE)
    from this(1) obtain i where "i \<in> {0..<dim_row A}"
      and f: "f = (v $ i) \<cdot> (row_to_poly ?ts (row A i))" ..
    from this(2) \<open>f \<noteq> 0\<close> have "v $ i \<noteq> 0" and **: "row_to_poly ?ts (row A i) \<noteq> 0" by auto
    from \<open>lt f = s\<close> have "s = lt ((v $ i) \<cdot> (row_to_poly ?ts (row A i)))" by (simp only: f)
    also from \<open>v $ i \<noteq> 0\<close> have "... = lt (row_to_poly ?ts (row A i))" by (rule lt_map_scale)
    finally have s: "s = lt (row_to_poly ?ts (row A i))" .
    show "s \<in> lt_set ((\<lambda>i. row_to_poly ?ts (row A i)) ` {0..<dim_row A})"
      unfolding s by (rule lt_setI, rule, rule refl, fact+)
  qed
  also have "... = lt_set ((\<lambda>r. row_to_poly ?ts r) ` (row A ` {0..<dim_row A}))"
    by (simp only: image_comp o_def)
  also have "... = lt_set (set (map (\<lambda>r. row_to_poly ?ts r) (map (row A) [0..<dim_row A])))"
    by (metis image_set set_upt)
  also have "... = lt_set (set (mat_to_polys ?ts A))" by (simp only: mat_to_polys_def rows_def)
  finally show ?thesis unfolding p' .
qed

subsection \<open>Functions \<open>Macaulay_mat\<close> and \<open>Macaulay_list\<close>\<close>

definition Macaulay_mat :: "('t \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> 'b::field mat"
  where "Macaulay_mat ps = polys_to_mat (Keys_to_list ps) ps"

definition Macaulay_list :: "('t \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::field) list"
  where "Macaulay_list ps =
               filter (\<lambda>p. p \<noteq> 0) (mat_to_polys (Keys_to_list ps) (row_echelon (Macaulay_mat ps)))"

lemma dim_Macaulay_mat[simp]:
  "dim_row (Macaulay_mat ps) = length ps"
  "dim_col (Macaulay_mat ps) = card (Keys (set ps))"
  by (simp_all add: Macaulay_mat_def length_Keys_to_list)

lemma Macaulay_list_Nil [simp]: "Macaulay_list [] = ([]::('t \<Rightarrow>\<^sub>0 'b::field) list)" (is "?l = _")
proof -
  have "length ?l \<le> length (mat_to_polys (Keys_to_list ([]::('t \<Rightarrow>\<^sub>0 'b) list))
                    (row_echelon (Macaulay_mat ([]::('t \<Rightarrow>\<^sub>0 'b) list))))"
    unfolding Macaulay_list_def by (fact length_filter_le)
  also have "... = 0" by simp
  finally show ?thesis by simp
qed

lemma set_Macaulay_list:
  "set (Macaulay_list ps) =
      set (mat_to_polys (Keys_to_list ps) (row_echelon (Macaulay_mat ps))) - {0}"
  by (auto simp add: Macaulay_list_def)

lemma Keys_Macaulay_list: "Keys (set (Macaulay_list ps)) \<subseteq> Keys (set ps)"
proof -
  have "Keys (set (Macaulay_list ps)) \<subseteq> set (Keys_to_list ps)"
    by (simp only: set_Macaulay_list Keys_minus_zero, fact Keys_mat_to_polys)
  also have "... = Keys (set ps)" by (fact set_Keys_to_list)
  finally show ?thesis .
qed

lemma in_Macaulay_listE:
  assumes "p \<in> set (Macaulay_list ps)"
    and "pivot_fun (row_echelon (Macaulay_mat ps)) f (dim_col (row_echelon (Macaulay_mat ps)))"
  obtains i where "i < dim_row (row_echelon (Macaulay_mat ps))"
    and "p = (mat_to_polys (Keys_to_list ps) (row_echelon (Macaulay_mat ps))) ! i"
    and "f i < dim_col (row_echelon (Macaulay_mat ps))"
proof -
  let ?ts = "Keys_to_list ps"
  let ?A = "Macaulay_mat ps"
  let ?E = "row_echelon ?A"

  from assms(1) have "p \<in> set (mat_to_polys ?ts ?E) - {0}" by (simp add: set_Macaulay_list)
  hence "p \<in> set (mat_to_polys ?ts ?E)" and "p \<noteq> 0" by auto
  from this(1) obtain i where "i < length (mat_to_polys ?ts ?E)" and p: "p = (mat_to_polys ?ts ?E) ! i"
    by (metis in_set_conv_nth)
  from this(1) have "i < dim_row ?E" and "i < dim_row ?A" by simp_all

  from this(1) p show ?thesis
  proof
    from \<open>p \<noteq> 0\<close> have "0 \<noteq> (mat_to_polys ?ts ?E) ! i" by (simp only: p)
    also have "(mat_to_polys ?ts ?E) ! i = row_to_poly ?ts (row ?E i)"
      by (simp only: Macaulay_list_def mat_to_polys_nth[OF \<open>i < dim_row ?E\<close>])
    finally have *: "row_to_poly ?ts (row ?E i) \<noteq> 0" by simp
    have "row ?E i \<noteq> 0\<^sub>v (length ?ts)"
    proof
      assume "row ?E i = 0\<^sub>v (length ?ts)"
      with * show False by simp
    qed
    hence "row ?E i \<noteq> 0\<^sub>v (dim_col ?E)" by (simp add: length_Keys_to_list)
    thus "f i < dim_col ?E"
      by (simp only: row_not_zero_iff_pivot_fun[OF assms(2) \<open>i < dim_row ?E\<close>])
  qed
qed

lemma phull_Macaulay_list: "phull (set (Macaulay_list ps)) = phull (set ps)"
proof -
  have *: "Keys (set ps) \<subseteq> set (Keys_to_list ps)"
    by (simp add: set_Keys_to_list)
  have "phull (set (Macaulay_list ps)) =
          phull (set (mat_to_polys (Keys_to_list ps) (row_echelon (Macaulay_mat ps))))"
    by (simp only: set_Macaulay_list phull.span_Diff_zero)
  also have "... = phull (set ps)"
    by (simp only: Macaulay_mat_def phull_row_echelon[OF * distinct_Keys_to_list])
  finally show ?thesis .
qed

lemma pmdl_Macaulay_list: "pmdl (set (Macaulay_list ps)) = pmdl (set ps)"
proof -
  have *: "Keys (set ps) \<subseteq> set (Keys_to_list ps)"
    by (simp add: set_Keys_to_list)
  have "pmdl (set (Macaulay_list ps)) =
          pmdl (set (mat_to_polys (Keys_to_list ps) (row_echelon (Macaulay_mat ps))))"
    by (simp only: set_Macaulay_list pmdl.span_Diff_zero)
  also have "... = pmdl (set ps)"
    by (simp only: Macaulay_mat_def pmdl_row_echelon[OF * distinct_Keys_to_list])
  finally show ?thesis .
qed

lemma Macaulay_list_is_monic_set: "is_monic_set (set (Macaulay_list ps))"
proof (rule is_monic_setI)
  let ?ts = "Keys_to_list ps"
  let ?E = "row_echelon (Macaulay_mat ps)"

  fix p
  assume "p \<in> set (Macaulay_list ps)"
  obtain h where "pivot_fun ?E h (dim_col ?E)" by (rule row_echelon_pivot_fun)
  with \<open>p \<in> set (Macaulay_list ps)\<close> obtain i where "i < dim_row ?E"
    and p: "p = (mat_to_polys ?ts ?E) ! i" and "h i < dim_col ?E"
    by (rule in_Macaulay_listE)
  
  show "lc p = 1" unfolding p Keys_to_list_eq_pps_to_list
    by (rule lc_row_to_poly_pivot_fun, simp, fact+)
qed

lemma Macaulay_list_not_zero: "0 \<notin> set (Macaulay_list ps)"
  by (simp add: Macaulay_list_def)

lemma Macaulay_list_distinct_lt:
  assumes "x \<in> set (Macaulay_list ps)" and "y \<in> set (Macaulay_list ps)"
    and "x \<noteq> y"
  shows "lt x \<noteq> lt y"
proof
  let ?S = "Keys (set ps)"
  let ?ts = "Keys_to_list ps"
  let ?E = "row_echelon (Macaulay_mat ps)"

  assume "lt x = lt y"
  obtain h where pf: "pivot_fun ?E h (dim_col ?E)" by (rule row_echelon_pivot_fun)
  with assms(1) obtain i1 where "i1 < dim_row ?E"
    and x: "x = (mat_to_polys ?ts ?E) ! i1" and "h i1 < dim_col ?E"
    by (rule in_Macaulay_listE)
  from assms(2) pf obtain i2 where "i2 < dim_row ?E"
    and y: "y = (mat_to_polys ?ts ?E) ! i2" and "h i2 < dim_col ?E"
    by (rule in_Macaulay_listE)

  have "lt x = ?ts ! (h i1)"
    by (simp only: x Keys_to_list_eq_pps_to_list, rule lt_row_to_poly_pivot_fun, simp, fact+)
  moreover have "lt y = ?ts ! (h i2)"
    by (simp only: y Keys_to_list_eq_pps_to_list, rule lt_row_to_poly_pivot_fun, simp, fact+)
  ultimately have "?ts ! (h i1) = ?ts ! (h i2)" by (simp only: \<open>lt x = lt y\<close>)
  hence "pps_to_list (Keys (set ps)) ! h i1 = pps_to_list (Keys (set ps)) ! h i2"
    by (simp only: Keys_to_list_eq_pps_to_list)

  have "i1 = i2"
  proof (rule lt_row_to_poly_pivot_fun_eqD)
    show "card ?S = dim_col ?E" by simp
  qed fact+
  hence "x = y" by (simp only: x y)
  with \<open>x \<noteq> y\<close> show False ..
qed

lemma Macaulay_list_lt:
  assumes "p \<in> phull (set ps)" and "p \<noteq> 0"
  obtains g where "g \<in> set (Macaulay_list ps)" and "g \<noteq> 0" and "lt p = lt g"
proof -
  let ?S = "Keys (set ps)"
  let ?ts = "Keys_to_list ps"
  let ?E = "row_echelon (Macaulay_mat ps)"
  let ?gs = "mat_to_polys ?ts ?E"
  have "finite ?S" by (rule finite_Keys, rule)
  have "?S \<subseteq> set ?ts" by (simp only: set_Keys_to_list)
  
  from assms(1) \<open>?S \<subseteq> set ?ts\<close> have "p \<in> row_to_poly ?ts ` row_space ?E"
    by (simp only: Macaulay_mat_def row_space_row_echelon_eq_phull[symmetric])
  hence "p \<in> row_to_poly (pps_to_list ?S) ` row_space ?E"
    by (simp only: Keys_to_list_eq_pps_to_list)

  obtain f where "pivot_fun ?E f (dim_col ?E)" by (rule row_echelon_pivot_fun)

  have "lt p \<in> lt_set (set ?gs)" unfolding Keys_to_list_eq_pps_to_list
    by (rule lt_row_space_pivot_fun, simp, fact+)
  then obtain g where "g \<in> set ?gs" and "g \<noteq> 0" and "lt g = lt p" by (rule lt_setE)
  
  show ?thesis
  proof
    from \<open>g \<in> set ?gs\<close> \<open>g \<noteq> 0\<close> show "g \<in> set (Macaulay_list ps)" by (simp add: set_Macaulay_list)
  next
    from \<open>lt g = lt p\<close> show "lt p = lt g" by simp
  qed fact
qed

end (* ordered_term *)

end (* theory *)
