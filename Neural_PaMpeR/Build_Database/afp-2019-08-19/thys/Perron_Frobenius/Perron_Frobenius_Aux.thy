(* Author: Thiemann *)
section \<open>Perron-Frobenius Theorem\<close>

subsection \<open>Auxiliary Notions\<close>

text \<open>We define notions like non-negative real-valued matrix, both
  in JNF and in HMA. These notions will be linked via HMA-connect.\<close>

theory Perron_Frobenius_Aux
imports HMA_Connect
begin

definition real_nonneg_mat :: "complex mat \<Rightarrow> bool" where
  "real_nonneg_mat A \<equiv> \<forall> a \<in> elements_mat A. a \<in> \<real> \<and> Re a \<ge> 0"

definition real_nonneg_vec :: "complex Matrix.vec \<Rightarrow> bool" where
  "real_nonneg_vec v \<equiv> \<forall> a \<in> vec_elements v. a \<in> \<real> \<and> Re a \<ge> 0"

definition real_non_neg_vec :: "complex ^ 'n \<Rightarrow> bool" where
  "real_non_neg_vec v \<equiv> (\<forall> a \<in> vec_elements_h v. a \<in> \<real> \<and> Re a \<ge> 0)" 

definition real_non_neg_mat :: "complex ^ 'nr ^ 'nc \<Rightarrow> bool" where
  "real_non_neg_mat A \<equiv> (\<forall> a \<in> elements_mat_h A. a \<in> \<real> \<and> Re a \<ge> 0)" 

lemma real_non_neg_matD: assumes "real_non_neg_mat A"
  shows "A $h i $h j \<in> \<real>" "Re (A $h i $h j) \<ge> 0" 
  using assms unfolding real_non_neg_mat_def elements_mat_h_def by auto

definition nonneg_mat :: "'a :: linordered_idom mat \<Rightarrow> bool" where
  "nonneg_mat A \<equiv> \<forall> a \<in> elements_mat A. a \<ge> 0"

definition non_neg_mat :: "'a :: linordered_idom ^ 'nr ^ 'nc \<Rightarrow> bool" where
  "non_neg_mat A \<equiv> (\<forall> a \<in> elements_mat_h A. a \<ge> 0)" 


context includes lifting_syntax
begin

lemma HMA_real_non_neg_mat [transfer_rule]:
  "((HMA_M :: complex mat \<Rightarrow> complex ^ 'nc ^ 'nr \<Rightarrow> bool) ===> (=)) 
  real_nonneg_mat real_non_neg_mat"
  unfolding real_nonneg_mat_def[abs_def] real_non_neg_mat_def[abs_def]
  by transfer_prover

lemma HMA_real_non_neg_vec [transfer_rule]:
  "((HMA_V :: complex Matrix.vec \<Rightarrow> complex ^ 'n \<Rightarrow> bool) ===> (=)) 
  real_nonneg_vec real_non_neg_vec"
  unfolding real_nonneg_vec_def[abs_def] real_non_neg_vec_def[abs_def]
  by transfer_prover

lemma HMA_non_neg_mat [transfer_rule]:
  "((HMA_M :: 'a :: linordered_idom mat \<Rightarrow> 'a ^ 'nc ^ 'nr \<Rightarrow> bool) ===> (=)) 
  nonneg_mat non_neg_mat"
  unfolding nonneg_mat_def[abs_def] non_neg_mat_def[abs_def]
  by transfer_prover

end

primrec matpow :: "'a::semiring_1^'n^'n \<Rightarrow> nat \<Rightarrow> 'a^'n^'n" where
  matpow_0:   "matpow A 0 = mat 1" |
  matpow_Suc: "matpow A (Suc n) = (matpow A n) ** A"

context includes lifting_syntax
begin  
lemma HMA_pow_mat[transfer_rule]:
  "((HMA_M ::'a::{semiring_1} mat \<Rightarrow> 'a^'n^'n \<Rightarrow> bool) ===> (=) ===> HMA_M) pow_mat matpow"
proof -
  {
    fix A :: "'a mat" and A' :: "'a^'n^'n" and n :: nat
    assume [transfer_rule]: "HMA_M A A'"
    hence [simp]: "dim_row A = CARD('n)" unfolding HMA_M_def by simp
    have "HMA_M (pow_mat A n) (matpow A' n)"
    proof (induct n)
      case (Suc n)
      note [transfer_rule] = this
      show ?case by (simp, transfer_prover)
    qed (simp, transfer_prover)
  }
  thus ?thesis by blast
qed
end

lemma trancl_image: 
  "(i,j) \<in> R\<^sup>+ \<Longrightarrow> (f i, f j) \<in> (map_prod f f ` R)\<^sup>+" 
proof (induct rule: trancl_induct)
  case (step j k)
  from step(2) have "(f j, f k) \<in> map_prod f f ` R" by auto
  from step(3) this show ?case by auto
qed auto

lemma inj_trancl_image: assumes inj: "inj f" 
  shows "(f i, f j) \<in> (map_prod f f ` R)\<^sup>+ = ((i,j) \<in> R\<^sup>+)" (is "?l = ?r")
proof
  assume ?r from trancl_image[OF this] show ?l .
next
  assume ?l from trancl_image[OF this, of "the_inv f"]
  show ?r unfolding image_image prod.map_comp o_def the_inv_f_f[OF inj] by auto
qed  

lemma matrix_add_rdistrib: "((B + C) ** A) = (B ** A) + (C ** A)"
  by (vector matrix_matrix_mult_def sum.distrib[symmetric] field_simps)

lemma norm_smult: "norm ((a :: real) *s x) = abs a * norm x" 
  unfolding norm_vec_def 
  by (metis norm_scaleR norm_vec_def scalar_mult_eq_scaleR)

lemma nonneg_mat_mult: 
  "nonneg_mat A \<Longrightarrow> nonneg_mat B \<Longrightarrow> A \<in> carrier_mat nr n
  \<Longrightarrow> B \<in> carrier_mat n nc \<Longrightarrow> nonneg_mat (A * B)" 
  unfolding nonneg_mat_def
  by (auto simp: elements_mat_def scalar_prod_def intro!: sum_nonneg)

lemma nonneg_mat_power: assumes "A \<in> carrier_mat n n" "nonneg_mat A" 
  shows "nonneg_mat (A ^\<^sub>m k)"
proof (induct k)
  case 0
  thus ?case by (auto simp: nonneg_mat_def)
next
  case (Suc k)
  from nonneg_mat_mult[OF this assms(2) _ assms(1), of n] assms(1)
  show ?case by auto
qed

lemma nonneg_matD: assumes "nonneg_mat A"
  and "i < dim_row A" and "j < dim_col A"
shows "A $$ (i,j) \<ge> 0"
  using assms unfolding nonneg_mat_def elements_mat by auto

lemma (in comm_ring_hom) similar_mat_wit_hom: assumes
  "similar_mat_wit A B C D"
shows "similar_mat_wit (mat\<^sub>h A) (mat\<^sub>h B) (mat\<^sub>h C) (mat\<^sub>h D)"
proof -
  obtain n where n: "n = dim_row A" by auto
  note * = similar_mat_witD[OF n assms]
  from * have [simp]: "dim_row C = n" by auto
  note C = *(6) note D = *(7)
  note id = mat_hom_mult[OF C D] mat_hom_mult[OF D C]
  note ** = *(1-3)[THEN arg_cong[of _ _ "mat\<^sub>h"], unfolded id]
  note mult = mult_carrier_mat[of _ n n]
  note hom_mult = mat_hom_mult[of _ n n _ n]
  show ?thesis unfolding similar_mat_wit_def Let_def unfolding **(3) using **(1,2)
    by (auto simp: n[symmetric] hom_mult simp: *(4-) mult)
qed

lemma (in comm_ring_hom) similar_mat_hom:
  "similar_mat A B \<Longrightarrow> similar_mat (mat\<^sub>h A) (mat\<^sub>h B)"
  using similar_mat_wit_hom[of A B C D for C D]
  by (smt similar_mat_def)

lemma det_dim_1: assumes A: "A \<in> carrier_mat n n"
  and n: "n = 1"
shows "Determinant.det A = A $$ (0,0)"
  by (subst laplace_expansion_column[OF A[unfolded n], of 0], insert A n,
    auto simp: cofactor_def mat_delete_def)

lemma det_dim_2: assumes A: "A \<in> carrier_mat n n"
  and n: "n = 2"
shows "Determinant.det A = A $$ (0,0) * A $$ (1,1) - A $$ (0,1) * A $$ (1,0)"
proof -
  have set: "(\<Sum>i<(2 :: nat). f i) = f 0 + f 1" for f
    by (subst sum.cong[of _ "{0,1}" f f], auto)
  show ?thesis
    apply (subst laplace_expansion_column[OF A[unfolded n], of 0], insert A n,
      auto simp: cofactor_def mat_delete_def set)
    apply (subst (1 2) det_dim_1, auto)
    done
qed


lemma jordan_nf_root_char_poly: fixes A :: "'a :: {semiring_no_zero_divisors, idom} mat"
  assumes "jordan_nf A n_as" 
  and "(m, lam) \<in> set n_as" 
shows "poly (char_poly A) lam = 0" 
proof -
  from assms have m0: "m \<noteq> 0" unfolding jordan_nf_def by force
  from split_list[OF assms(2)] obtain as bs where nas: "n_as = as @ (m, lam) # bs" by auto
  show ?thesis using m0
    unfolding jordan_nf_char_poly[OF assms(1)] nas poly_prod_list prod_list_zero_iff by (auto simp: o_def)
qed

lemma inverse_power_tendsto_zero:
  "(\<lambda>x. inverse ((of_nat x :: 'a :: real_normed_div_algebra) ^ Suc d)) \<longlonglongrightarrow> 0"
proof (rule filterlim_compose[OF tendsto_inverse_0], 
  intro filterlim_at_infinity[THEN iffD2, of 0] allI impI, goal_cases) 
  case (2 r)
  let ?r = "nat (ceiling r) + 1" 
  show ?case
  proof (intro eventually_sequentiallyI[of ?r], unfold norm_power norm_of_nat)
    fix x
    assume r: "?r \<le> x" 
    hence x1: "real x \<ge> 1" by auto 
    have "r \<le> real ?r" by linarith
    also have "\<dots> \<le> x" using r by auto
    also have "\<dots> \<le> real x ^ Suc d" using x1 by simp
    finally show "r \<le> real x ^ Suc d" .
  qed 
qed simp

lemma inverse_of_nat_tendsto_zero:
  "(\<lambda>x. inverse (of_nat x :: 'a :: real_normed_div_algebra)) \<longlonglongrightarrow> 0"
  using inverse_power_tendsto_zero[of 0] by auto

lemma poly_times_exp_tendsto_zero: assumes b: "norm (b :: 'a :: real_normed_field) < 1" 
  shows "(\<lambda> x. of_nat x ^ k * b ^ x) \<longlonglongrightarrow> 0" 
proof (cases "b = 0")
  case False
  define nla where "nla = norm b" 
  define s where "s = sqrt nla" 
  from b False have nla: "0 < nla" "nla < 1" unfolding nla_def by auto
  hence s: "0 < s" "s < 1" unfolding s_def by auto
  { 
    fix x
    have "s^x * s^x = sqrt (nla ^ (2 * x))"
      unfolding s_def power_add[symmetric] 
      unfolding real_sqrt_power[symmetric] 
      by (rule arg_cong[of _ _ "\<lambda> x. sqrt (nla ^ x)"], simp)
    also have "\<dots> = nla^x" unfolding power_mult real_sqrt_power
      using nla by simp
    finally have "nla^x = s^x * s^x" by simp
  } note nla_s = this
  show "(\<lambda>x. of_nat x ^ k * b ^ x) \<longlonglongrightarrow> 0"        
  proof (rule tendsto_norm_zero_cancel, unfold norm_mult norm_power norm_of_nat nla_def[symmetric] nla_s
       mult.assoc[symmetric])  
    from poly_exp_constant_bound[OF s, of 1 k] obtain p where 
      p: "real x ^ k * s^x \<le> p" for x by (auto simp: ac_simps)              
    have "norm (real x ^ k * s ^ x) = real x ^ k * s^x" for x using s by auto
    with p have p: "norm (real x ^ k * s ^ x) \<le> p" for x by auto
    from s have s: "norm s < 1" by auto
    show "(\<lambda>x. real x ^ k * s ^ x * s ^ x) \<longlonglongrightarrow> 0" 
      by (rule lim_null_mult_left_bounded[OF _ LIMSEQ_power_zero[OF s], of _ p], insert p, auto)
  qed 
next
  case True
  show ?thesis unfolding True
    by (subst tendsto_cong[of _ "\<lambda> x. 0"], rule eventually_sequentiallyI[of 1], auto)
qed


lemma (in linorder_topology) tendsto_Min: assumes I: "I \<noteq> {}" and fin: "finite I"
  shows "(\<And>i. i \<in> I \<Longrightarrow> (f i \<longlongrightarrow> a i) F) \<Longrightarrow> ((\<lambda>x. Min ((\<lambda> i. f i x) ` I)) \<longlongrightarrow> 
    (Min (a ` I) :: 'a)) F" 
  using fin I
proof (induct rule: finite_induct)
  case (insert i I)
  hence i: "(f i \<longlongrightarrow> a i) F" by auto
  show ?case
  proof (cases "I = {}")
    case True
    show ?thesis unfolding True using i by auto
  next
    case False
    have *: "Min (a ` insert i I) = min (a i) (Min (a ` I))" using False insert(1) by auto
    have **: "(\<lambda>x. Min ((\<lambda>i. f i x) ` insert i I)) = (\<lambda>x. min (f i x) (Min ((\<lambda>i. f i x) ` I)))" 
      using False insert(1) by auto
    have IH: "((\<lambda>x. Min ((\<lambda>i. f i x) ` I)) \<longlongrightarrow> Min (a ` I)) F" 
      using insert(3)[OF insert(4) False] by auto
    show ?thesis unfolding * **
      by (auto intro!: tendsto_min i IH)
  qed
qed simp

lemma tendsto_mat_mult [tendsto_intros]: 
  "(f \<longlongrightarrow> a) F \<Longrightarrow> (g \<longlongrightarrow> b) F \<Longrightarrow> ((\<lambda>x. f x ** g x) \<longlongrightarrow> a ** b) F" 
  for f :: "'a \<Rightarrow> 'b :: {semiring_1, real_normed_algebra} ^ 'n1 ^ 'n2" 
  unfolding matrix_matrix_mult_def[abs_def] by (auto intro!: tendsto_intros)

lemma tendsto_matpower [tendsto_intros]: "(f \<longlongrightarrow> a) F \<Longrightarrow> ((\<lambda>x. matpow (f x) n) \<longlongrightarrow> matpow a n) F"
  for f :: "'a \<Rightarrow> 'b :: {semiring_1, real_normed_algebra} ^ 'n ^ 'n"
  by (induct n, simp_all add: tendsto_mat_mult)

lemma continuous_matpow: "continuous_on R (\<lambda> A :: 'a :: {semiring_1, real_normed_algebra_1} ^ 'n ^ 'n. matpow A n)"
  unfolding continuous_on_def by (auto intro!: tendsto_intros)

lemma vector_smult_distrib: "(A *v ((a :: 'a :: comm_ring_1) *s x)) = a *s ((A *v x))" 
  unfolding matrix_vector_mult_def vector_scalar_mult_def
  by (simp add: ac_simps sum_distrib_left)  

instance real :: ordered_semiring_strict
  by (intro_classes, auto)

lemma poly_tendsto_pinfty:  fixes p :: "real poly"
  assumes "lead_coeff p > 0" "degree p \<noteq> 0" 
  shows "poly p \<longlonglongrightarrow> \<infinity>" 
  unfolding Lim_PInfty
proof 
  fix b
  show "\<exists>N. \<forall>n\<ge>N. ereal b \<le> ereal (poly p (real n))" 
    unfolding ereal_less_eq using poly_pinfty_ge[OF assms, of b]
    by (meson of_nat_le_iff order_trans real_arch_simple)
qed

lemma div_lt_nat: "(j :: nat) < x * y \<Longrightarrow> j div x < y" 
  by (simp add: less_mult_imp_div_less mult.commute)


definition diagvector :: "('n \<Rightarrow> 'a :: semiring_0) \<Rightarrow> 'a ^ 'n ^ 'n" where
  "diagvector x = (\<chi> i. \<chi> j. if i = j then x i else 0)" 

lemma diagvector_mult_vector[simp]: "diagvector x *v y = (\<chi> i. x i * y $ i)" 
  unfolding diagvector_def matrix_vector_mult_def vec_eq_iff vec_lambda_beta
proof (rule, goal_cases)
  case (1 i)
  show ?case by (subst sum.remove[of _ i], auto)
qed

lemma diagvector_mult_left: "diagvector x ** A = (\<chi> i j. x i * A $ i $ j)" (is "?A = ?B") 
  unfolding vec_eq_iff
proof (intro allI)
  fix i j
  show "?A $h i $h j = ?B $h i $h j" 
    unfolding map_vector_def diagvector_def matrix_matrix_mult_def vec_lambda_beta
    by (subst sum.remove[of _ i], auto)
qed

lemma diagvector_mult_right: "A ** diagvector x = (\<chi> i j. A $ i $ j * x j)" (is "?A = ?B") 
  unfolding vec_eq_iff
proof (intro allI)
  fix i j
  show "?A $h i $h j = ?B $h i $h j" 
    unfolding map_vector_def diagvector_def matrix_matrix_mult_def vec_lambda_beta
    by (subst sum.remove[of _ j], auto)
qed

lemma diagvector_mult[simp]: "diagvector x ** diagvector y = diagvector (\<lambda> i. x i * y i)" 
  unfolding diagvector_mult_left unfolding diagvector_def by (auto simp: vec_eq_iff)

lemma diagvector_const[simp]: "diagvector (\<lambda> x. k) = mat k" 
  unfolding diagvector_def mat_def by auto

lemma diagvector_eq_mat: "diagvector x = mat a \<longleftrightarrow> x = (\<lambda> x. a)" 
  unfolding diagvector_def mat_def by (auto simp: vec_eq_iff)

lemma cmod_eq_Re: assumes "cmod x = Re x"
  shows "of_real (Re x) = x" 
proof (cases "Im x = 0")
  case False
  hence "(cmod x)^2 \<noteq> (Re x)^2" unfolding norm_complex_def by simp
  from this[unfolded assms] show ?thesis by auto
qed (cases x, auto simp: norm_complex_def complex_of_real_def)

hide_fact (open) Matrix.vec_eq_iff

no_notation
  vec_index (infixl "$" 100)

lemma spectral_radius_ev:
  "\<exists> ev v. eigen_vector A v ev \<and> norm ev = spectral_radius A"
proof -
  from non_empty_spectrum[of A] finite_spectrum[of A] have
    "spectral_radius A \<in> norm ` (Collect (eigen_value A))"
    unfolding spectral_radius_ev_def by auto
  thus ?thesis unfolding eigen_value_def[abs_def] by auto
qed

lemma spectral_radius_max: assumes "eigen_value A v"
  shows "norm v \<le> spectral_radius A"
proof -
  from assms have "norm v \<in> norm ` (Collect (eigen_value A))" by auto
  from Max_ge[OF _ this, folded spectral_radius_ev_def]
    finite_spectrum[of A] show ?thesis by auto
qed

text \<open>For Perron-Frobenius it is useful to use the linear norm, and
  not the Euclidean norm.\<close>

definition norm1 :: "'a :: real_normed_field ^ 'n \<Rightarrow> real" where
  "norm1 v = (\<Sum>i\<in>UNIV. norm (v $ i))"

lemma norm1_ge_0: "norm1 v \<ge> 0" unfolding norm1_def
  by (rule sum_nonneg, auto)

lemma norm1_0[simp]: "norm1 0 = 0" unfolding norm1_def by auto

lemma norm1_nonzero: assumes "v \<noteq> 0"
  shows "norm1 v > 0"
proof -
  from \<open>v \<noteq> 0\<close> obtain i where vi: "v $ i \<noteq> 0" unfolding vec_eq_iff
    using Finite_Cartesian_Product.vec_eq_iff zero_index by force
  have "sum (\<lambda> i. norm (v $ i)) (UNIV - {i}) \<ge> 0"
    by (rule sum_nonneg, auto)
  moreover have "norm (v $ i) > 0" using vi by auto
  ultimately
  have "0 < norm (v $ i) + sum (\<lambda> i. norm (v $ i)) (UNIV - {i})" by arith
  also have "\<dots> = norm1 v" unfolding norm1_def
    by (simp add: sum.remove)
  finally show "norm1 v > 0" .
qed

lemma norm1_0_iff[simp]: "(norm1 v = 0) = (v = 0)"
  using norm1_0 norm1_nonzero by (cases "v = 0", force+)

lemma norm1_scaleR[simp]: "norm1 (r *\<^sub>R v) = abs r * norm1 v" unfolding norm1_def sum_distrib_left
  by (rule sum.cong, auto)

lemma abs_norm1[simp]: "abs (norm1 v) = norm1 v" using norm1_ge_0[of v] by arith

lemma normalize_eigen_vector: assumes "eigen_vector (A :: 'a :: real_normed_field ^ 'n ^ 'n) v ev"
  shows "eigen_vector A ((1 / norm1 v) *\<^sub>R v) ev" "norm1 ((1 / norm1 v) *\<^sub>R v) = 1"
proof -
  let ?v = "(1 / norm1 v) *\<^sub>R v"
  from assms[unfolded eigen_vector_def]
  have nz: "v \<noteq> 0" and id: "A *v v = ev *s v" by auto
  from nz have norm1: "norm1 v \<noteq> 0" by auto
  thus "norm1 ?v = 1" by simp
  from norm1 nz have nz: "?v \<noteq> 0" by auto
  have "A *v ?v = (1 / norm1 v) *\<^sub>R (A *v v)"
    by (auto simp: vec_eq_iff matrix_vector_mult_def real_vector.scale_sum_right)
  also have "A *v v = ev *s v" unfolding id ..
  also have "(1 / norm1 v) *\<^sub>R (ev *s v) = ev *s ?v"
    by (auto simp: vec_eq_iff)
  finally show "eigen_vector A ?v ev" using nz unfolding eigen_vector_def by auto
qed


lemma norm1_cont[simp]: "isCont norm1 v" unfolding norm1_def[abs_def] by auto

lemma norm1_ge_norm: "norm1 v \<ge> norm v" unfolding norm1_def norm_vec_def
  by (rule L2_set_le_sum, auto)

text \<open>The following continuity lemmas have been proven with hints from Fabian Immler.\<close>

lemma tendsto_matrix_vector_mult[tendsto_intros]:
  "((*v) (A :: 'a :: real_normed_algebra_1 ^ 'n ^ 'k) \<longlongrightarrow> A *v v) (at v within S)"
  unfolding matrix_vector_mult_def[abs_def]
  by (auto intro!: tendsto_intros)

lemma tendsto_matrix_matrix_mult[tendsto_intros]:
  "((**) (A :: 'a :: real_normed_algebra_1 ^ 'n ^ 'k) \<longlongrightarrow> A ** B) (at B within S)"
  unfolding matrix_matrix_mult_def[abs_def]
  by (auto intro!: tendsto_intros)

lemma matrix_vect_scaleR: "(A :: 'a :: real_normed_algebra_1 ^ 'n ^ 'k) *v (a *\<^sub>R v) = a *\<^sub>R (A *v v)"
  unfolding vec_eq_iff
  by (auto simp: matrix_vector_mult_def scaleR_vec_def scaleR_sum_right
  intro!: sum.cong)

lemma (in inj_semiring_hom) map_vector_0: "(map_vector hom v = 0) = (v = 0)"
  unfolding vec_eq_iff map_vector_def by auto

lemma (in inj_semiring_hom) map_vector_inj: "(map_vector hom v = map_vector hom w) = (v = w)"
  unfolding vec_eq_iff map_vector_def by auto

lemma (in semiring_hom) matrix_vector_mult_hom:
  "(map_matrix hom A) *v (map_vector hom v) = map_vector hom (A *v v)"
  by (transfer fixing: hom, auto simp: mult_mat_vec_hom)

lemma (in semiring_hom) vector_smult_hom:
  "hom x *s (map_vector hom v) = map_vector hom (x *s v)"
  by (transfer fixing: hom, auto simp: vec_hom_smult)

lemma (in inj_comm_ring_hom) eigen_vector_hom: 
  "eigen_vector (map_matrix hom A) (map_vector hom v) (hom x) = eigen_vector A v x"
  unfolding eigen_vector_def matrix_vector_mult_hom vector_smult_hom map_vector_0 map_vector_inj 
  by auto

end
