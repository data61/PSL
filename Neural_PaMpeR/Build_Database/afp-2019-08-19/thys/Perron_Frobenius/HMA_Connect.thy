(*
  Authors: J. Divasón, R. Thiemann, A. Yamada, O. Kunčar
*)

subsection \<open>Transfer rules to convert theorems from JNF to HMA and vice-versa.\<close>

theory HMA_Connect
imports 
  Jordan_Normal_Form.Spectral_Radius 
  "HOL-Analysis.Determinants"
  "HOL-Analysis.Cartesian_Euclidean_Space"
  Bij_Nat
  Cancel_Card_Constraint
  "HOL-Eisbach.Eisbach" 
begin

text \<open>Prefer certain constants and lemmas without prefix.\<close>

hide_const (open) Matrix.mat
hide_const (open) Matrix.row
hide_const (open) Determinant.det

lemmas mat_def = Finite_Cartesian_Product.mat_def
lemmas det_def = Determinants.det_def
lemmas row_def = Finite_Cartesian_Product.row_def

notation vec_index (infixl "$v" 90)
notation vec_nth (infixl "$h" 90)


text \<open>Forget that @{typ "'a mat"}, @{typ "'a Matrix.vec"}, and @{typ "'a poly"} 
  have been defined via lifting\<close>


(* TODO: add to end of matrix theory, stores lifting + transfer setup *)
lifting_forget vec.lifting
lifting_forget mat.lifting

lifting_forget poly.lifting

text \<open>Some notions which we did not find in the HMA-world.\<close>
definition eigen_vector :: "'a::comm_ring_1 ^ 'n ^ 'n \<Rightarrow> 'a ^ 'n \<Rightarrow> 'a \<Rightarrow> bool" where
  "eigen_vector A v ev = (v \<noteq> 0 \<and> A *v v = ev *s v)"

definition eigen_value :: "'a :: comm_ring_1 ^ 'n ^ 'n \<Rightarrow> 'a \<Rightarrow> bool" where
  "eigen_value A k = (\<exists> v. eigen_vector A v k)"

definition similar_matrix_wit 
  :: "'a :: semiring_1 ^ 'n ^ 'n \<Rightarrow> 'a ^ 'n ^ 'n \<Rightarrow> 'a ^ 'n ^ 'n \<Rightarrow> 'a ^ 'n ^ 'n \<Rightarrow> bool" where
  "similar_matrix_wit A B P Q = (P ** Q = mat 1 \<and> Q ** P = mat 1 \<and> A = P ** B ** Q)"

definition similar_matrix 
  :: "'a :: semiring_1 ^ 'n ^ 'n \<Rightarrow> 'a ^ 'n ^ 'n \<Rightarrow> bool" where
  "similar_matrix A B = (\<exists> P Q. similar_matrix_wit A B P Q)"

definition spectral_radius :: "complex ^ 'n ^ 'n \<Rightarrow> real" where
  "spectral_radius A = Max { norm ev | v ev. eigen_vector A v ev}"

definition Spectrum :: "'a :: field ^ 'n ^ 'n \<Rightarrow> 'a set" where
  "Spectrum A = Collect (eigen_value A)" 

definition vec_elements_h :: "'a ^ 'n \<Rightarrow> 'a set" where
  "vec_elements_h v = range (vec_nth v)"

lemma vec_elements_h_def': "vec_elements_h v = {v $h i | i. True}"
  unfolding vec_elements_h_def by auto

definition elements_mat_h :: "'a ^ 'nc ^ 'nr \<Rightarrow> 'a set" where
  "elements_mat_h A = range (\<lambda> (i,j). A $h i $h j)"

lemma elements_mat_h_def': "elements_mat_h A = {A $h i $h j | i j. True}"
  unfolding elements_mat_h_def by auto

definition map_vector :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a ^'n \<Rightarrow> 'b ^'n" where 
  "map_vector f v \<equiv> \<chi> i. f (v $h i)"

definition map_matrix :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a ^ 'n ^ 'm \<Rightarrow> 'b ^ 'n ^ 'm" where 
  "map_matrix f A \<equiv> \<chi> i. map_vector f (A $h i)"

definition normbound :: "'a :: real_normed_field ^ 'nc ^ 'nr \<Rightarrow> real \<Rightarrow> bool" where
  "normbound A b \<equiv> \<forall> x \<in> elements_mat_h A. norm x \<le> b"

lemma spectral_radius_ev_def: "spectral_radius A = Max (norm ` (Collect (eigen_value A)))"
  unfolding spectral_radius_def eigen_value_def[abs_def]
  by (rule arg_cong[where f = Max], auto) 

lemma elements_mat: "elements_mat A = {A $$ (i,j) | i j. i < dim_row A \<and> j < dim_col A}"
  unfolding elements_mat_def by force

definition vec_elements :: "'a Matrix.vec \<Rightarrow> 'a set"
  where "vec_elements v = set [v $ i. i <- [0 ..< dim_vec v]]"

lemma vec_elements: "vec_elements v = { v $ i | i. i < dim_vec v}"
  unfolding vec_elements_def by auto


(* TODO: restore a bundle, for e.g., for matrix_impl *)
context includes vec.lifting 
begin
end

definition from_hma\<^sub>v :: "'a ^ 'n  \<Rightarrow> 'a Matrix.vec" where
  "from_hma\<^sub>v v = Matrix.vec CARD('n) (\<lambda> i. v $h from_nat i)"

definition from_hma\<^sub>m :: "'a ^ 'nc ^ 'nr \<Rightarrow> 'a Matrix.mat" where
  "from_hma\<^sub>m a = Matrix.mat CARD('nr) CARD('nc) (\<lambda> (i,j). a $h from_nat i $h from_nat j)"

definition to_hma\<^sub>v :: "'a Matrix.vec \<Rightarrow> 'a ^ 'n" where
  "to_hma\<^sub>v v = (\<chi> i. v $v to_nat i)"

definition to_hma\<^sub>m :: "'a Matrix.mat \<Rightarrow> 'a ^ 'nc  ^ 'nr " where
  "to_hma\<^sub>m a = (\<chi> i j. a $$ (to_nat i, to_nat j))"

declare vec_lambda_eta[simp]

lemma to_hma_from_hma\<^sub>v[simp]: "to_hma\<^sub>v (from_hma\<^sub>v v) = v"
  by (auto simp: to_hma\<^sub>v_def from_hma\<^sub>v_def to_nat_less_card)

lemma to_hma_from_hma\<^sub>m[simp]: "to_hma\<^sub>m (from_hma\<^sub>m v) = v"
  by (auto simp: to_hma\<^sub>m_def from_hma\<^sub>m_def to_nat_less_card)

lemma from_hma_to_hma\<^sub>v[simp]:
  "v \<in> carrier_vec (CARD('n)) \<Longrightarrow> from_hma\<^sub>v (to_hma\<^sub>v v :: 'a ^ 'n) = v"
  by (auto simp: to_hma\<^sub>v_def from_hma\<^sub>v_def to_nat_from_nat_id)

lemma from_hma_to_hma\<^sub>m[simp]:
  "A \<in> carrier_mat (CARD('nr)) (CARD('nc)) \<Longrightarrow> from_hma\<^sub>m (to_hma\<^sub>m A :: 'a ^ 'nc  ^ 'nr) = A"
  by (auto simp: to_hma\<^sub>m_def from_hma\<^sub>m_def to_nat_from_nat_id)

lemma from_hma\<^sub>v_inj[simp]: "from_hma\<^sub>v x = from_hma\<^sub>v y \<longleftrightarrow> x = y"
  by (intro iffI, insert to_hma_from_hma\<^sub>v[of x], auto)

lemma from_hma\<^sub>m_inj[simp]: "from_hma\<^sub>m x = from_hma\<^sub>m y \<longleftrightarrow> x = y"
  by(intro iffI, insert to_hma_from_hma\<^sub>m[of x], auto)

definition HMA_V :: "'a Matrix.vec \<Rightarrow> 'a ^ 'n  \<Rightarrow> bool" where 
  "HMA_V = (\<lambda> v w. v = from_hma\<^sub>v w)"

definition HMA_M :: "'a Matrix.mat \<Rightarrow> 'a ^ 'nc  ^ 'nr  \<Rightarrow> bool" where 
  "HMA_M = (\<lambda> a b. a = from_hma\<^sub>m b)"

definition HMA_I :: "nat \<Rightarrow> 'n :: finite \<Rightarrow> bool" where
  "HMA_I = (\<lambda> i a. i = to_nat a)"

context includes lifting_syntax
begin

lemma Domainp_HMA_V [transfer_domain_rule]: 
  "Domainp (HMA_V :: 'a Matrix.vec \<Rightarrow> 'a ^ 'n \<Rightarrow> bool) = (\<lambda> v. v \<in> carrier_vec (CARD('n )))"
  by(intro ext iffI, insert from_hma_to_hma\<^sub>v[symmetric], auto simp: from_hma\<^sub>v_def HMA_V_def)

lemma Domainp_HMA_M [transfer_domain_rule]: 
  "Domainp (HMA_M :: 'a Matrix.mat \<Rightarrow> 'a ^ 'nc  ^ 'nr  \<Rightarrow> bool) 
  = (\<lambda> A. A \<in> carrier_mat CARD('nr) CARD('nc))"
  by (intro ext iffI, insert from_hma_to_hma\<^sub>m[symmetric], auto simp: from_hma\<^sub>m_def HMA_M_def)

lemma Domainp_HMA_I [transfer_domain_rule]: 
  "Domainp (HMA_I :: nat \<Rightarrow> 'n :: finite \<Rightarrow> bool) = (\<lambda> i. i < CARD('n))" (is "?l = ?r")
proof (intro ext)
  fix i :: nat
  show "?l i = ?r i"
    unfolding HMA_I_def Domainp_iff
    by (auto intro: exI[of _ "from_nat i"] simp: to_nat_from_nat_id to_nat_less_card)
qed

lemma bi_unique_HMA_V [transfer_rule]: "bi_unique HMA_V" "left_unique HMA_V" "right_unique HMA_V"
  unfolding HMA_V_def bi_unique_def left_unique_def right_unique_def by auto

lemma bi_unique_HMA_M [transfer_rule]: "bi_unique HMA_M" "left_unique HMA_M" "right_unique HMA_M"
  unfolding HMA_M_def bi_unique_def left_unique_def right_unique_def by auto

lemma bi_unique_HMA_I [transfer_rule]: "bi_unique HMA_I" "left_unique HMA_I" "right_unique HMA_I"
  unfolding HMA_I_def bi_unique_def left_unique_def right_unique_def by auto

lemma right_total_HMA_V [transfer_rule]: "right_total HMA_V"
  unfolding HMA_V_def right_total_def by simp

lemma right_total_HMA_M [transfer_rule]: "right_total HMA_M"
  unfolding HMA_M_def right_total_def by simp

lemma right_total_HMA_I [transfer_rule]: "right_total HMA_I"
  unfolding HMA_I_def right_total_def by simp

lemma HMA_V_index [transfer_rule]: "(HMA_V ===> HMA_I ===> (=)) ($v) ($h)"
  unfolding rel_fun_def HMA_V_def HMA_I_def from_hma\<^sub>v_def
  by (auto simp: to_nat_less_card)

text \<open>We introduce the index function to have pointwise access to 
  HMA-matrices by a constant. Otherwise, the transfer rule 
  with @{term "\<lambda> A i j. A $h i $h j"} instead of index is not applicable.\<close>

definition "index_hma A i j \<equiv> A $h i $h j"

lemma HMA_M_index [transfer_rule]:
  "(HMA_M ===> HMA_I ===> HMA_I ===> (=)) (\<lambda> A i j. A $$ (i,j)) index_hma"
  by (intro rel_funI, simp add: index_hma_def to_nat_less_card HMA_M_def HMA_I_def from_hma\<^sub>m_def)  

lemma HMA_V_0 [transfer_rule]: "HMA_V (0\<^sub>v CARD('n)) (0 :: 'a :: zero ^ 'n)"
  unfolding HMA_V_def from_hma\<^sub>v_def by auto

lemma HMA_M_0 [transfer_rule]: 
  "HMA_M (0\<^sub>m CARD('nr) CARD('nc)) (0 :: 'a :: zero ^ 'nc  ^ 'nr )"
  unfolding HMA_M_def from_hma\<^sub>m_def by auto

lemma HMA_M_1[transfer_rule]:
  "HMA_M (1\<^sub>m (CARD('n))) (mat 1 :: 'a::{zero,one}^'n^'n)"
  unfolding HMA_M_def
  by (auto simp add: mat_def from_hma\<^sub>m_def from_nat_inj)

lemma from_hma\<^sub>v_add: "from_hma\<^sub>v v + from_hma\<^sub>v w = from_hma\<^sub>v (v + w)"
  unfolding from_hma\<^sub>v_def by auto

lemma HMA_V_add [transfer_rule]: "(HMA_V ===> HMA_V ===> HMA_V) (+) (+) "
  unfolding rel_fun_def HMA_V_def
  by (auto simp: from_hma\<^sub>v_add)

lemma from_hma\<^sub>v_diff: "from_hma\<^sub>v v - from_hma\<^sub>v w = from_hma\<^sub>v (v - w)"
  unfolding from_hma\<^sub>v_def by auto

lemma HMA_V_diff [transfer_rule]: "(HMA_V ===> HMA_V ===> HMA_V) (-) (-)"
  unfolding rel_fun_def HMA_V_def
  by (auto simp: from_hma\<^sub>v_diff)

lemma from_hma\<^sub>m_add: "from_hma\<^sub>m a + from_hma\<^sub>m b = from_hma\<^sub>m (a + b)"
  unfolding from_hma\<^sub>m_def by auto

lemma HMA_M_add [transfer_rule]: "(HMA_M ===> HMA_M ===> HMA_M) (+) (+) "
  unfolding rel_fun_def HMA_M_def
  by (auto simp: from_hma\<^sub>m_add)

lemma from_hma\<^sub>m_diff: "from_hma\<^sub>m a - from_hma\<^sub>m b = from_hma\<^sub>m (a - b)"
  unfolding from_hma\<^sub>m_def by auto

lemma HMA_M_diff [transfer_rule]: "(HMA_M ===> HMA_M ===> HMA_M) (-) (-) "
  unfolding rel_fun_def HMA_M_def
  by (auto simp: from_hma\<^sub>m_diff)

lemma scalar_product: fixes v :: "'a :: semiring_1 ^ 'n "
  shows "scalar_prod (from_hma\<^sub>v v) (from_hma\<^sub>v w) = scalar_product v w"
  unfolding scalar_product_def scalar_prod_def from_hma\<^sub>v_def dim_vec
  by (simp add: sum.reindex[OF inj_to_nat, unfolded range_to_nat])

lemma [simp]:
  "from_hma\<^sub>m (y :: 'a ^ 'nc  ^ 'nr) \<in> carrier_mat (CARD('nr)) (CARD('nc))"
  "dim_row (from_hma\<^sub>m (y :: 'a ^ 'nc  ^ 'nr )) = CARD('nr)"
  "dim_col (from_hma\<^sub>m (y :: 'a ^ 'nc  ^ 'nr )) = CARD('nc)"
  unfolding from_hma\<^sub>m_def by simp_all

lemma [simp]:
  "from_hma\<^sub>v (y :: 'a ^ 'n) \<in> carrier_vec (CARD('n))"
  "dim_vec (from_hma\<^sub>v (y :: 'a ^ 'n)) = CARD('n)"
  unfolding from_hma\<^sub>v_def by simp_all

declare rel_funI [intro!]

lemma HMA_scalar_prod [transfer_rule]:
  "(HMA_V ===> HMA_V ===> (=)) scalar_prod scalar_product"
  by (auto simp: HMA_V_def scalar_product)

lemma HMA_row [transfer_rule]: "(HMA_I ===> HMA_M ===> HMA_V) (\<lambda> i a. Matrix.row a i) row"
  unfolding HMA_M_def HMA_I_def HMA_V_def
  by (auto simp: from_hma\<^sub>m_def from_hma\<^sub>v_def to_nat_less_card row_def)

lemma HMA_col [transfer_rule]: "(HMA_I ===> HMA_M ===> HMA_V) (\<lambda> i a. col a i) column"
  unfolding HMA_M_def HMA_I_def HMA_V_def
  by (auto simp: from_hma\<^sub>m_def from_hma\<^sub>v_def to_nat_less_card column_def)

definition mk_mat :: "('i \<Rightarrow> 'j \<Rightarrow> 'c) \<Rightarrow> 'c^'j^'i" where
  "mk_mat f = (\<chi> i j. f i j)"

definition mk_vec :: "('i \<Rightarrow> 'c) \<Rightarrow> 'c^'i" where
  "mk_vec f = (\<chi> i. f i)"

lemma HMA_M_mk_mat[transfer_rule]: "((HMA_I ===> HMA_I ===> (=)) ===> HMA_M) 
  (\<lambda> f. Matrix.mat (CARD('nr)) (CARD('nc)) (\<lambda> (i,j). f i j)) 
  (mk_mat :: (('nr \<Rightarrow> 'nc \<Rightarrow> 'a) \<Rightarrow> 'a^'nc^'nr))"
proof-
  {
    fix x y i j
    assume id: "\<forall> (ya :: 'nr) (yb :: 'nc). (x (to_nat ya) (to_nat yb) :: 'a) = y ya yb"
       and i: "i < CARD('nr)" and j: "j < CARD('nc)"
    from to_nat_from_nat_id[OF i] to_nat_from_nat_id[OF j] id[rule_format, of "from_nat i" "from_nat j"]
    have "x i j = y (from_nat i) (from_nat j)" by auto
  }
  thus ?thesis
    unfolding rel_fun_def mk_mat_def HMA_M_def HMA_I_def from_hma\<^sub>m_def by auto
qed

lemma HMA_M_mk_vec[transfer_rule]: "((HMA_I ===> (=)) ===> HMA_V) 
  (\<lambda> f. Matrix.vec (CARD('n)) (\<lambda> i. f i)) 
  (mk_vec :: (('n \<Rightarrow> 'a) \<Rightarrow> 'a^'n))"
proof-
  {
    fix x y i
    assume id: "\<forall> (ya :: 'n). (x (to_nat ya) :: 'a) = y ya"
       and i: "i < CARD('n)" 
    from to_nat_from_nat_id[OF i] id[rule_format, of "from_nat i"]
    have "x i = y (from_nat i)" by auto
  }
  thus ?thesis
    unfolding rel_fun_def mk_vec_def HMA_V_def HMA_I_def from_hma\<^sub>v_def by auto
qed


lemma mat_mult_scalar: "A ** B = mk_mat (\<lambda> i j. scalar_product (row i A) (column j B))"
  unfolding vec_eq_iff matrix_matrix_mult_def scalar_product_def mk_mat_def
  by (auto simp: row_def column_def)

lemma mult_mat_vec_scalar: "A *v v = mk_vec (\<lambda> i. scalar_product (row i A) v)"
  unfolding vec_eq_iff matrix_vector_mult_def scalar_product_def mk_mat_def mk_vec_def
  by (auto simp: row_def column_def)

lemma dim_row_transfer_rule: 
  "HMA_M A (A' :: 'a ^ 'nc ^ 'nr) \<Longrightarrow> (=) (dim_row A) (CARD('nr))"
  unfolding HMA_M_def by auto

lemma dim_col_transfer_rule: 
  "HMA_M A (A' :: 'a ^ 'nc ^ 'nr) \<Longrightarrow> (=) (dim_col A) (CARD('nc))"
  unfolding HMA_M_def by auto

lemma HMA_M_mult [transfer_rule]: "(HMA_M ===> HMA_M ===> HMA_M) ((*)) ((**))"
proof -
  {
    fix A B :: "'a :: semiring_1 mat" and A' :: "'a ^ 'n  ^ 'nr" and B' :: "'a ^ 'nc ^ 'n"
    assume 1[transfer_rule]: "HMA_M A A'" "HMA_M B B'"
    note [transfer_rule] = dim_row_transfer_rule[OF 1(1)] dim_col_transfer_rule[OF 1(2)]
    have "HMA_M (A * B) (A' ** B')"
      unfolding times_mat_def mat_mult_scalar
      by (transfer_prover_start, transfer_step+, transfer, auto)
  }
  thus ?thesis by blast
qed
      

lemma HMA_V_smult [transfer_rule]: "((=) ===> HMA_V ===> HMA_V) (\<cdot>\<^sub>v) ((*s))"
  unfolding smult_vec_def 
  unfolding rel_fun_def HMA_V_def from_hma\<^sub>v_def
  by auto

lemma HMA_M_mult_vec [transfer_rule]: "(HMA_M ===> HMA_V ===> HMA_V) ((*\<^sub>v)) ((*v))"
proof -
  {
    fix A :: "'a :: semiring_1 mat" and v :: "'a Matrix.vec"
      and A' :: "'a ^ 'nc  ^ 'nr" and v' :: "'a ^ 'nc"
    assume 1[transfer_rule]: "HMA_M A A'" "HMA_V v v'"
    note [transfer_rule] = dim_row_transfer_rule
    have "HMA_V (A *\<^sub>v v) (A' *v v')"
      unfolding mult_mat_vec_def mult_mat_vec_scalar
      by (transfer_prover_start, transfer_step+, transfer, auto)
  }
  thus ?thesis by blast  
qed

lemma HMA_det [transfer_rule]: "(HMA_M ===> (=)) Determinant.det 
  (det :: 'a :: comm_ring_1 ^ 'n ^ 'n \<Rightarrow> 'a)"
proof -
  {
    fix a :: "'a ^ 'n ^ 'n"
    let ?tn = "to_nat :: 'n :: finite \<Rightarrow> nat"
    let ?fn = "from_nat :: nat \<Rightarrow> 'n"
    let ?zn = "{0..< CARD('n)}"
    let ?U = "UNIV :: 'n set"
    let ?p1 = "{p. p permutes ?zn}"
    let ?p2 = "{p. p permutes ?U}"  
    let ?f= "\<lambda> p i. if i \<in> ?U then ?fn (p (?tn i)) else i"
    let ?g = "\<lambda> p i. ?fn (p (?tn i))"
    have fg: "\<And> a b c. (if a \<in> ?U then b else c) = b" by auto
    have "?p2 = ?f ` ?p1" 
      by (rule permutes_bij', auto simp: to_nat_less_card to_nat_from_nat_id)
    hence id: "?p2 = ?g ` ?p1" by simp
    have inj_g: "inj_on ?g ?p1"
      unfolding inj_on_def
    proof (intro ballI impI ext, auto)
      fix p q i
      assume p: "p permutes ?zn" and q: "q permutes ?zn"
        and id: "(\<lambda> i. ?fn (p (?tn i))) = (\<lambda> i. ?fn (q (?tn i)))"
      {
        fix i
        from permutes_in_image[OF p] have pi: "p (?tn i) < CARD('n)" by (simp add: to_nat_less_card)
        from permutes_in_image[OF q] have qi: "q (?tn i) < CARD('n)" by (simp add: to_nat_less_card)
        from fun_cong[OF id] have "?fn (p (?tn i))  = from_nat (q (?tn i))" .
        from arg_cong[OF this, of ?tn] have "p (?tn i) = q (?tn i)"
          by (simp add: to_nat_from_nat_id pi qi)
      } note id = this             
      show "p i = q i"
      proof (cases "i < CARD('n)")
        case True
        hence "?tn (?fn i) = i" by (simp add: to_nat_from_nat_id)
        from id[of "?fn i", unfolded this] show ?thesis .
      next
        case False
        thus ?thesis using p q unfolding permutes_def by simp
      qed
    qed
    have mult_cong: "\<And> a b c d. a = b \<Longrightarrow> c = d \<Longrightarrow> a * c = b * d" by simp
    have "sum (\<lambda> p. 
      signof p * (\<Prod>i\<in>?zn. a $h ?fn i $h ?fn (p i))) ?p1
      = sum (\<lambda> p. of_int (sign p) * (\<Prod>i\<in>UNIV. a $h i $h p i)) ?p2"
      unfolding id sum.reindex[OF inj_g]
    proof (rule sum.cong[OF refl], unfold mem_Collect_eq o_def, rule mult_cong)
      fix p
      assume p: "p permutes ?zn"
      let ?q = "\<lambda> i. ?fn (p (?tn i))"
      from id p have q: "?q permutes ?U" by auto
      from p have pp: "permutation p" unfolding permutation_permutes by auto
      let ?ft = "\<lambda> p i. ?fn (p (?tn i))"
      have fin: "finite ?zn" by simp
      have "sign p = sign ?q \<and> p permutes ?zn"
      proof (induct rule: permutes_induct[OF fin _ _ p])    
        case 1 
        show ?case by (auto simp: sign_id[unfolded id_def] permutes_id[unfolded id_def])
      next
        case (2 a b p)
        let ?sab = "Fun.swap a b id"
        let ?sfab = "Fun.swap (?fn a) (?fn b) id"
        have p_sab: "permutation ?sab" by (rule permutation_swap_id)
        have p_sfab: "permutation ?sfab" by (rule permutation_swap_id)
        from 2(3) have IH1: "p permutes ?zn" and IH2: "sign p = sign (?ft p)" by auto
        have sab_perm: "?sab permutes ?zn" using 2(1-2) by (rule permutes_swap_id)
        from permutes_compose[OF IH1 this] have perm1: "?sab o p permutes ?zn" .
        from IH1 have p_p1: "p \<in> ?p1" by simp
        hence "?ft p \<in> ?ft ` ?p1" by (rule imageI)
        from this[folded id] have "?ft p permutes ?U" by simp
        hence p_ftp: "permutation (?ft p)" unfolding permutation_permutes by auto
        {
          fix a b
          assume a: "a \<in> ?zn" and b: "b \<in> ?zn"
          hence "(?fn a = ?fn b) = (a = b)" using 2(1-2)
            by (auto simp: from_nat_inj)
        } note inj = this
        from inj[OF 2(1-2)] have id2: "sign ?sfab = sign ?sab" unfolding sign_swap_id by simp
        have id: "?ft (Fun.swap a b id \<circ> p) = Fun.swap (?fn a) (?fn b) id \<circ> ?ft p"
        proof
          fix c 
          show "?ft (Fun.swap a b id \<circ> p) c = (Fun.swap (?fn a) (?fn b) id \<circ> ?ft p) c"
          proof (cases "p (?tn c) = a \<or> p (?tn c) = b")
            case True
            thus ?thesis by (cases, auto simp add: o_def swap_def)
          next
            case False
            hence neq: "p (?tn c) \<noteq> a" "p (?tn c) \<noteq> b" by auto
            have pc: "p (?tn c) \<in> ?zn" unfolding permutes_in_image[OF IH1] 
              by (simp add: to_nat_less_card)
            from neq[folded inj[OF pc 2(1)] inj[OF pc 2(2)]]
            have "?fn (p (?tn c)) \<noteq> ?fn a" "?fn (p (?tn c)) \<noteq> ?fn b" .
            with neq show ?thesis by (auto simp: o_def swap_def)
          qed
        qed
        show ?case unfolding IH2 id sign_compose[OF p_sab 2(5)] sign_compose[OF p_sfab p_ftp] id2 
          by (rule conjI[OF refl perm1])
      qed
      thus "signof p = of_int (sign ?q)" unfolding signof_def sign_def by auto
      show "(\<Prod>i = 0..<CARD('n). a $h ?fn i $h ?fn (p i)) =
           (\<Prod>i\<in>UNIV. a $h i $h ?q i)" unfolding 
           range_to_nat[symmetric] prod.reindex[OF inj_to_nat]
        by (rule prod.cong[OF refl], unfold o_def, simp)
    qed   
  }
  thus ?thesis unfolding HMA_M_def 
    by (auto simp: from_hma\<^sub>m_def Determinant.det_def det_def)
qed

lemma HMA_mat[transfer_rule]: "((=) ===> HMA_M) (\<lambda> k. k \<cdot>\<^sub>m 1\<^sub>m CARD('n)) 
  (Finite_Cartesian_Product.mat :: 'a::semiring_1 \<Rightarrow> 'a^'n^'n)"
  unfolding Finite_Cartesian_Product.mat_def[abs_def] rel_fun_def HMA_M_def
  by (auto simp: from_hma\<^sub>m_def from_nat_inj)


lemma HMA_mat_minus[transfer_rule]: "(HMA_M ===> HMA_M ===> HMA_M) 
  (\<lambda> A B. A + map_mat uminus B) ((-) :: 'a :: group_add ^'nc^'nr \<Rightarrow> 'a^'nc^'nr \<Rightarrow> 'a^'nc^'nr)"
  unfolding rel_fun_def HMA_M_def from_hma\<^sub>m_def by auto

definition mat2matofpoly where "mat2matofpoly A = (\<chi> i j. [: A $ i $ j :])"

definition charpoly where charpoly_def: "charpoly A = det (mat (monom 1 (Suc 0)) - mat2matofpoly A)"

definition erase_mat :: "'a :: zero ^ 'nc ^ 'nr \<Rightarrow> 'nr \<Rightarrow> 'nc \<Rightarrow> 'a ^ 'nc ^ 'nr" 
  where "erase_mat A i j = (\<chi> i'. \<chi>  j'. if i' = i \<or> j' = j then 0 else A $ i' $ j')" 

definition sum_UNIV_type :: "('n :: finite \<Rightarrow> 'a :: comm_monoid_add) \<Rightarrow> 'n itself \<Rightarrow> 'a" where
  "sum_UNIV_type f _ = sum f UNIV" 

definition sum_UNIV_set :: "(nat \<Rightarrow> 'a :: comm_monoid_add) \<Rightarrow> nat \<Rightarrow> 'a" where
  "sum_UNIV_set f n = sum f {..<n}" 

definition HMA_T :: "nat \<Rightarrow> 'n :: finite itself \<Rightarrow> bool" where
  "HMA_T n _ = (n = CARD('n))" 

lemma HMA_mat2matofpoly[transfer_rule]: "(HMA_M ===> HMA_M) (\<lambda>x. map_mat (\<lambda>a. [:a:]) x) mat2matofpoly"
  unfolding rel_fun_def HMA_M_def from_hma\<^sub>m_def mat2matofpoly_def by auto

lemma HMA_char_poly [transfer_rule]: 
  "((HMA_M :: ('a:: comm_ring_1 mat \<Rightarrow> 'a^'n^'n \<Rightarrow> bool)) ===> (=)) char_poly charpoly"
proof -
  {
    fix A :: "'a mat" and A' :: "'a^'n^'n"
    assume [transfer_rule]: "HMA_M A A'"
    hence [simp]: "dim_row A = CARD('n)" by (simp add: HMA_M_def)
    have [simp]: "monom 1 (Suc 0) = [:0, 1 :: 'a :]"
      by (simp add: monom_Suc)
    have [simp]: "map_mat uminus (map_mat (\<lambda>a. [:a:]) A) = map_mat (\<lambda>a. [:-a:]) A"
      by (rule eq_matI, auto)
    have "char_poly A = charpoly A'"
      unfolding char_poly_def[abs_def] char_poly_matrix_def charpoly_def[abs_def]
      by (transfer, simp)
  }
  thus ?thesis by blast
qed
 

lemma HMA_eigen_vector [transfer_rule]: "(HMA_M ===> HMA_V ===> (=)) eigenvector eigen_vector"
proof -
  { 
    fix A :: "'a mat" and v :: "'a Matrix.vec" 
    and A' :: "'a ^ 'n ^ 'n" and v' :: "'a ^ 'n" and k :: 'a
    assume 1[transfer_rule]: "HMA_M A A'" and 2[transfer_rule]: "HMA_V v v'"
    hence [simp]: "dim_row A = CARD('n)" "dim_vec v = CARD('n)" by (auto simp add: HMA_V_def HMA_M_def)
    have [simp]: "v \<in> carrier_vec CARD('n)" using 2 unfolding HMA_V_def by simp
    have "eigenvector A v = eigen_vector A' v'" 
      unfolding eigenvector_def[abs_def] eigen_vector_def[abs_def] 
      by (transfer, simp)
  }
  thus ?thesis by blast
qed


lemma HMA_eigen_value [transfer_rule]: "(HMA_M ===> (=) ===> (=)) eigenvalue eigen_value"
proof -
  {
    fix A :: "'a mat" and A' :: "'a ^ 'n  ^ 'n" and k
    assume 1[transfer_rule]: "HMA_M A A'"
    hence [simp]: "dim_row A = CARD('n)" by (simp add: HMA_M_def)
    note [transfer_rule] = dim_row_transfer_rule[OF 1(1)]    
    have "(eigenvalue A k) = (eigen_value A' k)"
      unfolding eigenvalue_def[abs_def] eigen_value_def[abs_def] 
      by (transfer, auto simp add: eigenvector_def)
  }
  thus ?thesis by blast
qed


lemma HMA_spectral_radius [transfer_rule]: 
  "(HMA_M ===> (=)) Spectral_Radius.spectral_radius spectral_radius"
  unfolding Spectral_Radius.spectral_radius_def[abs_def] spectrum_def 
    spectral_radius_ev_def[abs_def]
  by transfer_prover

lemma HMA_elements_mat[transfer_rule]: "((HMA_M :: ('a mat \<Rightarrow> 'a ^ 'nc ^ 'nr \<Rightarrow> bool))  ===> (=)) 
  elements_mat elements_mat_h"
proof -
  {
    fix y :: "'a ^ 'nc ^ 'nr" and i j :: nat
    assume i: "i < CARD('nr)" and j: "j < CARD('nc)"
    hence "from_hma\<^sub>m y $$ (i, j) \<in> range (\<lambda>(i, ya). y $h i $h ya)"      
      using to_nat_from_nat_id[OF i] to_nat_from_nat_id[OF j] by (auto simp: from_hma\<^sub>m_def)
  }
  moreover
  {
    fix y :: "'a ^ 'nc ^ 'nr" and a b
    have "\<exists>i j. y $h a $h b = from_hma\<^sub>m y $$ (i, j) \<and> i < CARD('nr) \<and> j < CARD('nc)"
      unfolding from_hma\<^sub>m_def
      by (rule exI[of _ "Bij_Nat.to_nat a"], rule exI[of _ "Bij_Nat.to_nat b"], auto
        simp: to_nat_less_card)
  }
  ultimately show ?thesis
    unfolding elements_mat[abs_def] elements_mat_h_def[abs_def] HMA_M_def
    by auto
qed  

lemma HMA_vec_elements[transfer_rule]: "((HMA_V :: ('a Matrix.vec \<Rightarrow> 'a ^ 'n \<Rightarrow> bool))  ===> (=)) 
  vec_elements vec_elements_h"
proof -
  {
    fix y :: "'a ^ 'n" and i :: nat
    assume i: "i < CARD('n)" 
    hence "from_hma\<^sub>v y $ i \<in> range (vec_nth y)"      
      using to_nat_from_nat_id[OF i] by (auto simp: from_hma\<^sub>v_def)
  }
  moreover
  {
    fix y :: "'a ^ 'n" and a
    have "\<exists>i. y $h a = from_hma\<^sub>v y $ i \<and> i < CARD('n)"
      unfolding from_hma\<^sub>v_def
      by (rule exI[of _ "Bij_Nat.to_nat a"], auto simp: to_nat_less_card)
  }
  ultimately show ?thesis
    unfolding vec_elements[abs_def] vec_elements_h_def[abs_def] rel_fun_def HMA_V_def
    by auto
qed  
  
lemma norm_bound_elements_mat: "norm_bound A b = (\<forall> x \<in> elements_mat A. norm x \<le> b)"
  unfolding norm_bound_def elements_mat by auto

lemma HMA_normbound [transfer_rule]: 
  "((HMA_M :: 'a :: real_normed_field mat \<Rightarrow> 'a ^ 'nc ^ 'nr \<Rightarrow> bool) ===> (=) ===> (=))
  norm_bound normbound"
  unfolding normbound_def[abs_def] norm_bound_elements_mat[abs_def]
  by (transfer_prover)

lemma HMA_map_matrix [transfer_rule]: 
  "((=) ===> HMA_M ===> HMA_M) map_mat map_matrix"
  unfolding map_vector_def map_matrix_def[abs_def] map_mat_def[abs_def] HMA_M_def from_hma\<^sub>m_def
  by auto

lemma HMA_transpose_matrix [transfer_rule]: 
  "(HMA_M ===> HMA_M) transpose_mat transpose"
  unfolding transpose_mat_def transpose_def HMA_M_def from_hma\<^sub>m_def by auto

lemma HMA_map_vector [transfer_rule]: 
  "((=) ===> HMA_V ===> HMA_V) map_vec map_vector"
  unfolding map_vector_def[abs_def] map_vec_def[abs_def] HMA_V_def from_hma\<^sub>v_def
  by auto

lemma HMA_similar_mat_wit [transfer_rule]: 
  "((HMA_M :: _ \<Rightarrow> 'a :: comm_ring_1 ^ 'n ^ 'n \<Rightarrow> _) ===> HMA_M ===> HMA_M ===> HMA_M ===> (=)) 
  similar_mat_wit similar_matrix_wit"
proof (intro rel_funI, goal_cases)
  case (1 a A b B c C d D)  
  note [transfer_rule] = this
  hence id: "dim_row a = CARD('n)" by (auto simp: HMA_M_def)
  have *: "(c * d = 1\<^sub>m (dim_row a) \<and> d * c = 1\<^sub>m (dim_row a) \<and> a = c * b * d) =
    (C ** D = mat 1 \<and> D ** C = mat 1 \<and> A = C ** B ** D)" unfolding id
    by (transfer, simp)
  show ?case unfolding similar_mat_wit_def Let_def similar_matrix_wit_def *
    using 1 by (auto simp: HMA_M_def)
qed

lemma HMA_similar_mat [transfer_rule]: 
  "((HMA_M :: _ \<Rightarrow> 'a :: comm_ring_1 ^ 'n ^ 'n \<Rightarrow> _) ===> HMA_M ===> (=)) 
  similar_mat similar_matrix"
proof (intro rel_funI, goal_cases)
  case (1 a A b B)
  note [transfer_rule] = this
  hence id: "dim_row a = CARD('n)" by (auto simp: HMA_M_def)
  {
    fix c d
    assume "similar_mat_wit a b c d" 
    hence "{c,d} \<subseteq> carrier_mat CARD('n) CARD('n)" unfolding similar_mat_wit_def id Let_def by auto
  } note * = this
  show ?case unfolding similar_mat_def similar_matrix_def
    by (transfer, insert *, blast)
qed

lemma HMA_spectrum[transfer_rule]: "(HMA_M ===> (=)) spectrum Spectrum"
  unfolding spectrum_def[abs_def] Spectrum_def[abs_def]
  by transfer_prover

lemma HMA_M_erase_mat[transfer_rule]: "(HMA_M ===> HMA_I ===> HMA_I ===> HMA_M) mat_erase erase_mat" 
  unfolding mat_erase_def[abs_def] erase_mat_def[abs_def]
  by (auto simp: HMA_M_def HMA_I_def from_hma\<^sub>m_def to_nat_from_nat_id intro!: eq_matI)

lemma HMA_M_sum_UNIV[transfer_rule]: 
  "((HMA_I ===> (=)) ===> HMA_T ===> (=)) sum_UNIV_set sum_UNIV_type"
  unfolding rel_fun_def 
proof (clarify, rename_tac f fT n nT)
  fix f and fT :: "'b \<Rightarrow> 'a" and n and nT :: "'b itself" 
  assume f: "\<forall>x y. HMA_I x y \<longrightarrow> f x = fT y"
    and n: "HMA_T n nT" 
  let ?f = "from_nat :: nat \<Rightarrow> 'b" 
  let ?t = "to_nat :: 'b \<Rightarrow> nat" 
  from n[unfolded HMA_T_def] have n: "n = CARD('b)" .
  from to_nat_from_nat_id[where 'a = 'b, folded n]
  have tf: "i < n \<Longrightarrow> ?t (?f i) = i" for i by auto
  have "sum_UNIV_set f n = sum f (?t ` ?f ` {..<n})" 
    unfolding sum_UNIV_set_def
    by (rule arg_cong[of _ _ "sum f"], insert tf, force)
  also have "\<dots> = sum (f \<circ> ?t) (?f ` {..<n})" 
    by (rule sum.reindex, insert tf n, auto simp: inj_on_def)
  also have "?f ` {..<n} = UNIV" 
    using range_to_nat[where 'a = 'b, folded n] by force
  also have "sum (f \<circ> ?t) UNIV = sum fT UNIV" 
  proof (rule sum.cong[OF refl])
    fix i :: 'b
    show "(f \<circ> ?t) i = fT i" unfolding o_def 
      by (rule f[rule_format], auto simp: HMA_I_def)
  qed
  also have "\<dots> = sum_UNIV_type fT nT" 
    unfolding sum_UNIV_type_def ..
  finally show "sum_UNIV_set f n = sum_UNIV_type fT nT" .
qed
end

text \<open>Setup a method to easily convert theorems from JNF into HMA.\<close>

method transfer_hma uses rule = (
  (fold index_hma_def)?, (* prepare matrix access for transfer *)
  transfer,
  rule rule, 
  (unfold carrier_vec_def carrier_mat_def)?, 
  auto)

text \<open>Now it becomes easy to transfer results which are not yet proven in HMA, such as:\<close>

lemma matrix_add_vect_distrib: "(A + B) *v v = A *v v + B *v v"
  by (transfer_hma rule: add_mult_distrib_mat_vec)

lemma matrix_vector_right_distrib: "M *v (v + w) = M *v v + M *v w"
  by (transfer_hma rule: mult_add_distrib_mat_vec)

lemma matrix_vector_right_distrib_diff: "(M :: 'a :: ring_1 ^ 'nr ^ 'nc) *v (v - w) = M *v v - M *v w"
  by (transfer_hma rule: mult_minus_distrib_mat_vec)

lemma eigen_value_root_charpoly: 
  "eigen_value A k \<longleftrightarrow> poly (charpoly (A :: 'a :: field ^ 'n ^ 'n)) k = 0"
  by (transfer_hma rule: eigenvalue_root_char_poly)

lemma finite_spectrum: fixes A :: "'a :: field ^ 'n ^ 'n"
  shows "finite (Collect (eigen_value A))" 
  by (transfer_hma rule: card_finite_spectrum(1)[unfolded spectrum_def])

lemma non_empty_spectrum: fixes A :: "complex ^ 'n ^ 'n"
  shows "Collect (eigen_value A) \<noteq> {}"
  by (transfer_hma rule: spectrum_non_empty[unfolded spectrum_def])

lemma charpoly_transpose: "charpoly (transpose A :: 'a :: field ^ 'n ^ 'n) = charpoly A"
  by (transfer_hma rule: char_poly_transpose_mat)

lemma eigen_value_transpose: "eigen_value (transpose A :: 'a :: field ^ 'n ^ 'n) v = eigen_value A v" 
  unfolding eigen_value_root_charpoly charpoly_transpose by simp

lemma matrix_diff_vect_distrib: "(A - B) *v v = A *v v - B *v (v :: 'a :: ring_1 ^ 'n)"
  by (transfer_hma rule: minus_mult_distrib_mat_vec)

lemma similar_matrix_charpoly: "similar_matrix A B \<Longrightarrow> charpoly A = charpoly B" 
  by (transfer_hma rule: char_poly_similar)

lemma pderiv_char_poly_erase_mat: fixes A :: "'a :: idom ^ 'n ^ 'n" 
  shows "monom 1 1 * pderiv (charpoly A) = sum (\<lambda> i. charpoly (erase_mat A i i)) UNIV" 
proof -
  let ?A = "from_hma\<^sub>m A" 
  let ?n = "CARD('n)" 
  have tA[transfer_rule]: "HMA_M ?A A" unfolding HMA_M_def by simp
  have tN[transfer_rule]: "HMA_T ?n TYPE('n)" unfolding HMA_T_def by simp
  have A: "?A \<in> carrier_mat ?n ?n" unfolding from_hma\<^sub>m_def by auto
  have id: "sum (\<lambda> i. charpoly (erase_mat A i i)) UNIV = 
    sum_UNIV_type (\<lambda> i. charpoly (erase_mat A i i)) TYPE('n)"
    unfolding sum_UNIV_type_def ..
  show ?thesis unfolding id
    by (transfer, insert pderiv_char_poly_mat_erase[OF A], simp add: sum_UNIV_set_def)
qed

lemma degree_monic_charpoly: fixes A :: "'a :: comm_ring_1 ^ 'n ^ 'n" 
  shows "degree (charpoly A) = CARD('n) \<and> monic (charpoly A)" 
proof (transfer, goal_cases)
  case 1
  from degree_monic_char_poly[OF 1] show ?case by auto
qed



end
