(* ---------------------------------------------------------------------------- *)
subsection \<open>Vectors and Matrices in $\mathbb{C}^2$\<close>
(* ---------------------------------------------------------------------------- *)

text \<open>Representing vectors and matrices of arbitrary dimensions pose a challenge in formal theorem
proving \cite{harrison05}, but we only need to consider finite dimension spaces $\mathbb{C}^2$ and
$\mathbb{R}^3$.\<close>

theory Matrices
imports More_Complex Linear_Systems Quadratic
begin

(* ---------------------------------------------------------------------------- *)
subsubsection \<open>Vectors in $\mathbb{C}^2$\<close>
(* ---------------------------------------------------------------------------- *)

text \<open>Type of complex vector\<close>

type_synonym complex_vec = "complex \<times> complex"

definition vec_zero :: "complex_vec" where
  [simp]: "vec_zero = (0, 0)"

text \<open>Vector scalar multiplication\<close>

fun mult_sv :: "complex \<Rightarrow> complex_vec \<Rightarrow> complex_vec" (infixl "*\<^sub>s\<^sub>v" 100) where
  "k *\<^sub>s\<^sub>v (x, y) = (k*x, k*y)"

lemma fst_mult_sv [simp]: 
  shows "fst (k *\<^sub>s\<^sub>v v) = k * fst v"
  by (cases v) simp

lemma snd_mult_sv [simp]:
  shows "snd (k *\<^sub>s\<^sub>v v) = k * snd v"
  by (cases v) simp

lemma mult_sv_mult_sv [simp]: 
  shows "k1 *\<^sub>s\<^sub>v (k2 *\<^sub>s\<^sub>v v) = (k1*k2) *\<^sub>s\<^sub>v v"
  by (cases v) simp

lemma one_mult_sv [simp]:
  shows "1 *\<^sub>s\<^sub>v v =  v"
  by (cases v) simp

lemma mult_sv_ex_id1 [simp]:
  shows "\<exists> k::complex. k \<noteq> 0 \<and> k *\<^sub>s\<^sub>v v = v"
  by (rule_tac x=1 in exI, simp)

lemma mult_sv_ex_id2 [simp]:
  shows "\<exists> k::complex. k \<noteq> 0 \<and> v = k *\<^sub>s\<^sub>v v"
  by (rule_tac x=1 in exI, simp)

text \<open>Scalar product of two vectors\<close>

fun mult_vv :: "complex \<times> complex \<Rightarrow> complex \<times> complex \<Rightarrow> complex" (infixl "*\<^sub>v\<^sub>v" 100) where
 "(x, y) *\<^sub>v\<^sub>v (a, b) = x*a + y*b"

lemma mult_vv_commute:
  shows "v1 *\<^sub>v\<^sub>v v2 = v2 *\<^sub>v\<^sub>v v1"
  by (cases v1, cases v2) auto

lemma mult_vv_scale_sv1:
  shows "(k *\<^sub>s\<^sub>v v1) *\<^sub>v\<^sub>v v2 = k * (v1 *\<^sub>v\<^sub>v v2)"
  by (cases v1, cases v2) (auto simp add: field_simps)

lemma mult_vv_scale_sv2:
  shows "v1 *\<^sub>v\<^sub>v (k *\<^sub>s\<^sub>v v2) = k * (v1 *\<^sub>v\<^sub>v v2)"
  by (cases v1, cases v2) (auto simp add: field_simps)

text \<open>Conjugate vector\<close>

fun vec_map where
 "vec_map f (x, y) = (f x, f y)"

definition vec_cnj where
  "vec_cnj = vec_map cnj"

lemma vec_cnj_vec_cnj [simp]:
  shows "vec_cnj (vec_cnj v) = v"
  by (cases v) (simp add: vec_cnj_def)

lemma cnj_mult_vv:
  shows "cnj (v1 *\<^sub>v\<^sub>v v2) = (vec_cnj v1) *\<^sub>v\<^sub>v (vec_cnj v2)"
  by (cases v1, cases v2) (simp add: vec_cnj_def)

lemma vec_cnj_sv [simp]:
  shows "vec_cnj (k *\<^sub>s\<^sub>v A) = cnj k *\<^sub>s\<^sub>v vec_cnj A"
  by (cases A) (auto simp add: vec_cnj_def)

lemma scalsquare_vv_zero:
  shows "(vec_cnj v) *\<^sub>v\<^sub>v v = 0 \<longleftrightarrow> v = vec_zero"
  apply (cases v)
  apply (auto simp add: vec_cnj_def field_simps complex_mult_cnj_cmod power2_eq_square)
   apply (simp only: cor_add[symmetric] cor_mult[symmetric] of_real_eq_0_iff, simp)+
  done

(* ---------------------------------------------------------------------------- *)
subsubsection \<open>Matrices in $\mathbb{C}^2$\<close>
(* ---------------------------------------------------------------------------- *)

text \<open>Type of complex matrices\<close>

type_synonym complex_mat = "complex \<times> complex \<times> complex \<times> complex"

text \<open>Matrix scalar multiplication\<close>

fun mult_sm :: "complex \<Rightarrow> complex_mat \<Rightarrow> complex_mat" (infixl "*\<^sub>s\<^sub>m" 100) where
  "k *\<^sub>s\<^sub>m (a, b, c, d) = (k*a, k*b, k*c, k*d)"

lemma mult_sm_distribution [simp]:
  shows "k1 *\<^sub>s\<^sub>m (k2 *\<^sub>s\<^sub>m A) = (k1*k2) *\<^sub>s\<^sub>m A"
  by (cases A) auto

lemma mult_sm_neutral [simp]:
  shows "1 *\<^sub>s\<^sub>m A = A"
  by (cases A) auto

lemma mult_sm_inv_l:
  assumes "k \<noteq> 0" and "k *\<^sub>s\<^sub>m A = B"
  shows "A = (1/k) *\<^sub>s\<^sub>m B"
  using assms
  by auto

lemma mult_sm_ex_id1 [simp]:
  shows "\<exists> k::complex. k \<noteq> 0 \<and> k *\<^sub>s\<^sub>m M = M"
  by (rule_tac x=1 in exI, simp)

lemma mult_sm_ex_id2 [simp]:
  shows "\<exists> k::complex. k \<noteq> 0 \<and> M = k *\<^sub>s\<^sub>m M"
  by (rule_tac x=1 in exI, simp)

text \<open>Matrix addition and subtraction\<close>

definition mat_zero :: "complex_mat" where [simp]: "mat_zero = (0, 0, 0, 0)"

fun mat_plus :: "complex_mat \<Rightarrow> complex_mat \<Rightarrow> complex_mat" (infixl "+\<^sub>m\<^sub>m" 100) where
  "mat_plus (a1, b1, c1, d1) (a2, b2, c2, d2) = (a1+a2, b1+b2, c1+c2, d1+d2)"

fun mat_minus :: "complex_mat \<Rightarrow> complex_mat \<Rightarrow> complex_mat" (infixl "-\<^sub>m\<^sub>m" 100) where
  "mat_minus (a1, b1, c1, d1) (a2, b2, c2, d2) = (a1-a2, b1-b2, c1-c2, d1-d2)"

fun mat_uminus :: "complex_mat \<Rightarrow> complex_mat" where
  "mat_uminus (a, b, c, d) = (-a, -b, -c, -d)"

lemma nonzero_mult_real:
  assumes "A \<noteq> mat_zero" and "k \<noteq> 0"
  shows "k *\<^sub>s\<^sub>m A \<noteq> mat_zero"
  using assms
  by (cases A) simp

text \<open>Matrix multiplication.\<close>

fun mult_mm :: "complex_mat \<Rightarrow> complex_mat \<Rightarrow> complex_mat" (infixl "*\<^sub>m\<^sub>m" 100) where
  "(a1, b1, c1, d1) *\<^sub>m\<^sub>m (a2, b2, c2, d2) =
   (a1*a2 + b1*c2, a1*b2 + b1*d2, c1*a2+d1*c2, c1*b2+d1*d2)"

lemma mult_mm_assoc:
  shows "A *\<^sub>m\<^sub>m (B *\<^sub>m\<^sub>m C) = (A *\<^sub>m\<^sub>m B) *\<^sub>m\<^sub>m C"
  by (cases A, cases B, cases C) (auto simp add: field_simps)

lemma mult_assoc_5:
  shows "A *\<^sub>m\<^sub>m (B *\<^sub>m\<^sub>m C *\<^sub>m\<^sub>m D) *\<^sub>m\<^sub>m E = (A *\<^sub>m\<^sub>m B) *\<^sub>m\<^sub>m C *\<^sub>m\<^sub>m (D *\<^sub>m\<^sub>m E)"
  by (simp only: mult_mm_assoc)

lemma mat_zero_r [simp]:
  shows "A *\<^sub>m\<^sub>m mat_zero = mat_zero"
  by (cases A) simp

lemma mat_zero_l [simp]:
  shows "mat_zero *\<^sub>m\<^sub>m A = mat_zero"
  by (cases A) simp

definition eye :: "complex_mat" where
  [simp]: "eye = (1, 0, 0, 1)"

lemma mat_eye_l:
  shows "eye *\<^sub>m\<^sub>m A = A"
  by (cases A) auto

lemma mat_eye_r:
  shows "A *\<^sub>m\<^sub>m eye = A"
  by (cases A) auto

lemma mult_mm_sm [simp]:
  shows "A *\<^sub>m\<^sub>m (k *\<^sub>s\<^sub>m B) = k *\<^sub>s\<^sub>m (A *\<^sub>m\<^sub>m B)"
  by (cases A, cases B) (simp add: field_simps)

lemma mult_sm_mm [simp]:
  shows "(k *\<^sub>s\<^sub>m A) *\<^sub>m\<^sub>m B = k *\<^sub>s\<^sub>m (A *\<^sub>m\<^sub>m B)"
  by (cases A, cases B) (simp add: field_simps)

lemma mult_sm_eye_mm [simp]:
  shows "k *\<^sub>s\<^sub>m eye *\<^sub>m\<^sub>m A = k *\<^sub>s\<^sub>m A"
  by (cases A) simp

text \<open>Matrix determinant\<close>

fun mat_det where "mat_det (a, b, c, d) = a*d - b*c"

lemma mat_det_mult [simp]:
  shows "mat_det (A *\<^sub>m\<^sub>m B) = mat_det A * mat_det B"
  by (cases A, cases B) (auto simp add: field_simps)

lemma mat_det_mult_sm [simp]:
  shows "mat_det (k *\<^sub>s\<^sub>m A) = (k*k) * mat_det A"
  by (cases A) (auto simp add: field_simps)

text \<open>Matrix inverse\<close>

fun mat_inv :: "complex_mat \<Rightarrow> complex_mat" where
  "mat_inv (a, b, c, d) = (1/(a*d - b*c)) *\<^sub>s\<^sub>m (d, -b, -c, a)"

lemma mat_inv_r:
  assumes "mat_det A \<noteq> 0"
  shows "A *\<^sub>m\<^sub>m (mat_inv A) = eye"
  using assms
proof (cases A, auto simp add: field_simps)
  fix a b c d :: complex
  assume "a * (a * (d * d)) + b * (b * (c * c)) = a * (b * (c * (d * 2)))"
  hence "(a*d - b*c)*(a*d - b*c) = 0"
    by (auto simp add: field_simps)
  hence *: "a*d - b*c = 0"
    by auto
  assume "a*d \<noteq> b*c"
  with * show False
    by auto
qed

lemma mat_inv_l:
  assumes "mat_det A \<noteq> 0"
  shows "(mat_inv A) *\<^sub>m\<^sub>m A  = eye"
  using assms
proof (cases A, auto simp add: field_simps)
  fix a b c d :: complex
  assume "a * (a * (d * d)) + b * (b * (c * c)) = a * (b * (c * (d * 2)))"
  hence "(a*d - b*c)*(a*d - b*c) = 0"
    by (auto simp add: field_simps)
  hence *: "a*d - b*c = 0"
    by auto
  assume "a*d \<noteq> b*c"
  with * show False
    by auto
qed

lemma mat_det_inv:
  assumes "mat_det A \<noteq> 0"
  shows "mat_det (mat_inv A) = 1 / mat_det A"
proof-
  have "mat_det eye = mat_det A * mat_det (mat_inv A)"
    using mat_inv_l[OF assms, symmetric]
    by simp
  thus ?thesis
    using assms
    by (simp add: field_simps)
qed

lemma mult_mm_inv_l:
  assumes "mat_det A \<noteq> 0" and "A *\<^sub>m\<^sub>m B = C"
  shows "B = mat_inv A *\<^sub>m\<^sub>m C"
  using assms mat_eye_l[of B]
  by (auto simp add: mult_mm_assoc mat_inv_l)

lemma mult_mm_inv_r:
  assumes "mat_det B \<noteq> 0" and "A *\<^sub>m\<^sub>m B = C"
  shows "A = C *\<^sub>m\<^sub>m mat_inv B"
  using assms mat_eye_r[of A]
  by (auto simp add: mult_mm_assoc[symmetric] mat_inv_r)

lemma mult_mm_non_zero_l:
  assumes "mat_det A \<noteq> 0" and "B \<noteq> mat_zero"
  shows "A *\<^sub>m\<^sub>m B \<noteq> mat_zero"
  using assms mat_zero_r
  using mult_mm_inv_l[OF assms(1), of B mat_zero]
  by auto

lemma mat_inv_mult_mm:
  assumes "mat_det A \<noteq> 0" and "mat_det B \<noteq> 0"
  shows "mat_inv (A *\<^sub>m\<^sub>m B) = mat_inv B *\<^sub>m\<^sub>m mat_inv A"
  using assms
proof-
  have "(A *\<^sub>m\<^sub>m B) *\<^sub>m\<^sub>m (mat_inv B *\<^sub>m\<^sub>m mat_inv A) = eye"
    using assms
    by (metis mat_inv_r mult_mm_assoc mult_mm_inv_r)
  thus ?thesis
    using mult_mm_inv_l[of "A *\<^sub>m\<^sub>m B" "mat_inv B *\<^sub>m\<^sub>m mat_inv A" eye] assms mat_eye_r
    by simp
qed

lemma mult_mm_cancel_l:
  assumes "mat_det M \<noteq> 0"  "M *\<^sub>m\<^sub>m A = M *\<^sub>m\<^sub>m B"
  shows "A = B"
  using assms
  by (metis mult_mm_inv_l)

lemma mult_mm_cancel_r:
  assumes "mat_det M \<noteq> 0"  "A *\<^sub>m\<^sub>m M = B *\<^sub>m\<^sub>m M"
  shows "A = B"
  using assms
  by (metis mult_mm_inv_r)

lemma mult_mm_non_zero_r:
  assumes "A \<noteq> mat_zero" and "mat_det B \<noteq> 0"
  shows "A *\<^sub>m\<^sub>m B \<noteq> mat_zero"
  using assms mat_zero_l
  using mult_mm_inv_r[OF assms(2), of A mat_zero]
  by auto

lemma mat_inv_mult_sm:
  assumes "k \<noteq> 0"
  shows "mat_inv (k *\<^sub>s\<^sub>m A) = (1 / k) *\<^sub>s\<^sub>m mat_inv A"
proof-
  obtain a b c d where "A = (a, b, c, d)"
    by (cases A) auto
  thus ?thesis
    using assms
    by auto (subst mult.assoc[of k a "k*d"], subst mult.assoc[of k b "k*c"], subst right_diff_distrib[of k "a*(k*d)" "b*(k*c)", symmetric], simp, simp add: field_simps)+
qed

lemma mat_inv_inv [simp]:
  assumes "mat_det M \<noteq> 0"
  shows "mat_inv (mat_inv M) = M"
proof-
  have "mat_inv M *\<^sub>m\<^sub>m M = eye"
    using mat_inv_l[OF assms]
    by simp
  thus ?thesis
    using assms mat_det_inv[of M]
    using mult_mm_inv_l[of "mat_inv M" M eye] mat_eye_r
    by (auto simp del: eye_def)
qed

text \<open>Matrix transpose\<close>

fun mat_transpose where
  "mat_transpose (a, b, c, d) = (a, c, b, d)"

lemma mat_t_mat_t [simp]:
  shows "mat_transpose (mat_transpose A) = A"
  by (cases A) auto

lemma mat_t_mult_sm [simp]:
  shows "mat_transpose (k *\<^sub>s\<^sub>m A) = k *\<^sub>s\<^sub>m (mat_transpose A)"
  by (cases A) simp

lemma mat_t_mult_mm [simp]:
  shows "mat_transpose (A *\<^sub>m\<^sub>m B) = mat_transpose B *\<^sub>m\<^sub>m mat_transpose A"
  by (cases A, cases B) auto

lemma mat_inv_transpose:
  shows "mat_transpose (mat_inv M) = mat_inv (mat_transpose M)"
  by (cases M) auto

lemma mat_det_transpose [simp]:
  fixes M :: "complex_mat"
  shows "mat_det (mat_transpose M) = mat_det M"
  by (cases M) auto

text \<open>Diagonal matrices definition\<close>

fun mat_diagonal where
 "mat_diagonal (A, B, C, D) = (B = 0 \<and> C = 0)"

text \<open>Matrix conjugate\<close>

fun mat_map where
 "mat_map f (a, b, c, d) = (f a, f b, f c, f d)"

definition mat_cnj where
  "mat_cnj = mat_map cnj"

lemma mat_cnj_cnj [simp]:
  shows "mat_cnj (mat_cnj A) = A"
  unfolding mat_cnj_def
  by (cases A) auto

lemma mat_cnj_sm [simp]:
  shows "mat_cnj (k *\<^sub>s\<^sub>m A) = cnj k *\<^sub>s\<^sub>m (mat_cnj A)"
  by (cases A) (simp add: mat_cnj_def)

lemma mat_det_cnj [simp]: 
  shows "mat_det (mat_cnj A) = cnj (mat_det A)"
  by (cases A) (simp add: mat_cnj_def)

lemma nonzero_mat_cnj:
  shows "mat_cnj A = mat_zero \<longleftrightarrow> A = mat_zero"
  by (cases A) (auto simp add: mat_cnj_def)

lemma mat_inv_cnj:
  shows "mat_cnj (mat_inv M) = mat_inv (mat_cnj M)"
  unfolding mat_cnj_def
  by (cases M) auto

text \<open>Matrix adjoint - the conjugate traspose matrix ($A^* = \overline{A^t}$)\<close>

definition mat_adj where
  "mat_adj A = mat_cnj (mat_transpose A)"

lemma mat_adj_mult_mm [simp]:
  shows "mat_adj (A *\<^sub>m\<^sub>m B) = mat_adj B *\<^sub>m\<^sub>m mat_adj A"
  by (cases A, cases B) (auto simp add: mat_adj_def mat_cnj_def)

lemma mat_adj_mult_sm [simp]:
  shows "mat_adj (k *\<^sub>s\<^sub>m A) = cnj k *\<^sub>s\<^sub>m mat_adj A"
  by (cases A) (auto simp add: mat_adj_def mat_cnj_def)

lemma mat_det_adj: 
  shows "mat_det (mat_adj A) = cnj (mat_det A)"
  by (cases A) (auto simp add: mat_adj_def mat_cnj_def)

lemma mat_adj_inv:
  assumes "mat_det M \<noteq> 0"
  shows "mat_adj (mat_inv M) = mat_inv (mat_adj M)"
  by (cases M) (auto simp add: mat_adj_def mat_cnj_def)

lemma mat_transpose_mat_cnj:
  shows "mat_transpose (mat_cnj A) = mat_adj A"
  by (cases A)  (auto simp add: mat_adj_def mat_cnj_def)

lemma mat_adj_adj [simp]:
  shows "mat_adj (mat_adj A) = A"
  unfolding mat_adj_def
  by (subst mat_transpose_mat_cnj) (simp add: mat_adj_def)

lemma mat_adj_eye [simp]:
  shows "mat_adj eye = eye"
  by (auto simp add: mat_adj_def mat_cnj_def)

text \<open>Matrix trace\<close>

fun mat_trace where
  "mat_trace (a, b, c, d) = a + d"

text \<open>Multiplication of matrix and a vector\<close>

fun mult_mv :: "complex_mat \<Rightarrow> complex_vec \<Rightarrow> complex_vec" (infixl "*\<^sub>m\<^sub>v" 100)  where
  "(a, b, c, d) *\<^sub>m\<^sub>v (x, y) = (x*a + y*b, x*c + y*d)"

fun mult_vm :: "complex_vec \<Rightarrow> complex_mat \<Rightarrow> complex_vec" (infixl "*\<^sub>v\<^sub>m" 100) where
  "(x, y) *\<^sub>v\<^sub>m (a, b, c, d)  = (x*a + y*c, x*b + y*d)"

lemma eye_mv_l [simp]:
  shows "eye *\<^sub>m\<^sub>v v = v"
  by (cases v) simp

lemma mult_mv_mv [simp]: 
  shows "B *\<^sub>m\<^sub>v (A *\<^sub>m\<^sub>v v) = (B *\<^sub>m\<^sub>m A) *\<^sub>m\<^sub>v v"
  by (cases v, cases A, cases B) (auto simp add: field_simps)

lemma mult_vm_vm [simp]:
  shows "(v *\<^sub>v\<^sub>m A) *\<^sub>v\<^sub>m B = v *\<^sub>v\<^sub>m (A *\<^sub>m\<^sub>m B)"
  by (cases v, cases A, cases B) (auto simp add: field_simps)

lemma mult_mv_inv:
  assumes "x =  A *\<^sub>m\<^sub>v y" and "mat_det A \<noteq> 0"
  shows "y = (mat_inv A) *\<^sub>m\<^sub>v x"
  using assms
  by (cases y) (simp add: mat_inv_l)

lemma mult_vm_inv:
  assumes "x =  y *\<^sub>v\<^sub>m A" and "mat_det A \<noteq> 0"
  shows "y = x *\<^sub>v\<^sub>m (mat_inv A) "
  using assms
  by (cases y) (simp add: mat_inv_r)

lemma mult_mv_cancel_l:
  assumes "mat_det A \<noteq> 0" and "A *\<^sub>m\<^sub>v v = A *\<^sub>m\<^sub>v v'"
  shows "v = v'"
  using assms
  using mult_mv_inv
  by blast

lemma mult_vm_cancel_r:
  assumes "mat_det A \<noteq> 0" and "v *\<^sub>v\<^sub>m A = v' *\<^sub>v\<^sub>m A"
  shows "v = v'"
  using assms
  using mult_vm_inv
  by blast

lemma vec_zero_l [simp]:
  shows "A *\<^sub>m\<^sub>v vec_zero = vec_zero"
  by (cases A) simp

lemma vec_zero_r [simp]:
  shows "vec_zero *\<^sub>v\<^sub>m A = vec_zero"
  by (cases A) simp

lemma mult_mv_nonzero:
  assumes "v \<noteq> vec_zero" and "mat_det A \<noteq> 0"
  shows "A *\<^sub>m\<^sub>v v \<noteq> vec_zero"
  apply (rule ccontr)
  using assms mult_mv_inv[of vec_zero A v] mat_inv_l vec_zero_l
  by auto

lemma mult_vm_nonzero:
  assumes "v \<noteq> vec_zero" and "mat_det A \<noteq> 0"
  shows "v *\<^sub>v\<^sub>m A \<noteq> vec_zero"
  apply (rule ccontr)
  using assms mult_vm_inv[of vec_zero v A] mat_inv_r vec_zero_r
  by auto

lemma mult_sv_mv:
  shows "k *\<^sub>s\<^sub>v (A *\<^sub>m\<^sub>v v) = (A *\<^sub>m\<^sub>v (k *\<^sub>s\<^sub>v v))"
  by (cases A, cases v) (simp add: field_simps)

lemma mult_mv_mult_vm: 
  shows "A *\<^sub>m\<^sub>v x = x *\<^sub>v\<^sub>m (mat_transpose A)"
  by (cases A, cases x) auto

lemma mult_mv_vv:
  shows "A *\<^sub>m\<^sub>v v1 *\<^sub>v\<^sub>v v2 = v1 *\<^sub>v\<^sub>v (mat_transpose A *\<^sub>m\<^sub>v v2)"
  by (cases v1, cases v2, cases A) (auto simp add: field_simps)

lemma mult_vv_mv:
  shows "x *\<^sub>v\<^sub>v (A *\<^sub>m\<^sub>v y)  = (x *\<^sub>v\<^sub>m A) *\<^sub>v\<^sub>v y"
  by (cases x, cases y, cases A) (auto simp add: field_simps)

lemma vec_cnj_mult_mv:
  shows "vec_cnj (A *\<^sub>m\<^sub>v x) =  (mat_cnj A) *\<^sub>m\<^sub>v (vec_cnj x)"
  by (cases A, cases x) (auto simp add: vec_cnj_def mat_cnj_def)

lemma vec_cnj_mult_vm:
  shows "vec_cnj (v *\<^sub>v\<^sub>m A) = vec_cnj v *\<^sub>v\<^sub>m mat_cnj A"
  unfolding vec_cnj_def mat_cnj_def
  by (cases A, cases v, auto)

(* ---------------------------------------------------------------------------- *)
subsubsection \<open>Eigenvalues and eigenvectors\<close>
(* ---------------------------------------------------------------------------- *)

definition eigenpair where
  [simp]: "eigenpair k v H \<longleftrightarrow> v \<noteq> vec_zero \<and> H *\<^sub>m\<^sub>v v = k *\<^sub>s\<^sub>v v"

definition eigenval where
  [simp]: "eigenval k H \<longleftrightarrow> (\<exists> v. v \<noteq> vec_zero \<and> H *\<^sub>m\<^sub>v v = k *\<^sub>s\<^sub>v v)"

lemma eigen_equation:
  shows "eigenval k H \<longleftrightarrow> k\<^sup>2 - mat_trace H * k + mat_det H = 0" (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  obtain A B C D where HH: "H = (A, B, C, D)"
    by (cases H) auto
  show ?thesis
  proof
    assume ?lhs
    then obtain v where "v \<noteq> vec_zero" "H *\<^sub>m\<^sub>v v = k *\<^sub>s\<^sub>v v"
      unfolding eigenval_def
      by blast
    obtain v1 v2 where vv: "v = (v1, v2)"
      by (cases v) auto
    from \<open>H *\<^sub>m\<^sub>v v = k *\<^sub>s\<^sub>v v\<close> have "(H -\<^sub>m\<^sub>m (k *\<^sub>s\<^sub>m eye)) *\<^sub>m\<^sub>v v = vec_zero"
      using HH vv
      by (auto simp add: field_simps)
    hence "mat_det (H -\<^sub>m\<^sub>m (k *\<^sub>s\<^sub>m eye)) = 0"
      using \<open>v \<noteq> vec_zero\<close> vv HH
      using regular_homogenous_system[of "A - k" B C "D - k" v1 v2]
      unfolding det2_def
      by (auto simp add: field_simps)
    thus ?rhs
      using HH
      by (auto simp add: power2_eq_square field_simps)
  next
    assume ?rhs
    hence *: "mat_det (H -\<^sub>m\<^sub>m (k *\<^sub>s\<^sub>m eye)) = 0"
      using HH
      by (auto simp add: field_simps power2_eq_square)
    show ?lhs
    proof (cases "H -\<^sub>m\<^sub>m (k *\<^sub>s\<^sub>m eye) = mat_zero")
      case True
      thus ?thesis
        using HH
        by (auto) (rule_tac x=1 in exI, simp)
    next
      case False
      hence "(A - k \<noteq> 0 \<or> B \<noteq> 0) \<or> (D - k \<noteq> 0 \<or> C \<noteq> 0)"
        using HH
        by auto
      thus ?thesis
      proof
        assume "A - k \<noteq> 0 \<or> B \<noteq> 0"
        hence "C * B + (D - k) * (k - A) = 0"
          using * singular_system[of "A-k" "D-k" B C "(0, 0)" 0 0  "(B, k-A)"] HH
          by (auto simp add: field_simps)
        hence  "(B, k-A) \<noteq> vec_zero" "(H -\<^sub>m\<^sub>m (k *\<^sub>s\<^sub>m eye)) *\<^sub>m\<^sub>v (B, k-A) = vec_zero"
          using HH \<open>A - k \<noteq> 0 \<or> B \<noteq> 0\<close>
          by (auto simp add: field_simps)
        then obtain v where "v \<noteq> vec_zero \<and> (H -\<^sub>m\<^sub>m (k *\<^sub>s\<^sub>m eye)) *\<^sub>m\<^sub>v v = vec_zero"
          by blast
        thus ?thesis
          using HH
          unfolding eigenval_def
          by (rule_tac x="v" in exI) (case_tac v, simp add: field_simps)
      next
        assume "D - k \<noteq> 0 \<or> C \<noteq> 0"
        hence "C * B + (D - k) * (k - A) = 0"
          using * singular_system[of "D-k" "A-k" C B "(0, 0)" 0 0  "(C, k-D)"] HH
          by (auto simp add: field_simps)
        hence  "(k-D, C) \<noteq> vec_zero" "(H -\<^sub>m\<^sub>m (k *\<^sub>s\<^sub>m eye)) *\<^sub>m\<^sub>v (k-D, C) = vec_zero"
          using HH \<open>D - k \<noteq> 0 \<or> C \<noteq> 0\<close>
          by (auto simp add: field_simps)
        then obtain v where "v \<noteq> vec_zero \<and> (H -\<^sub>m\<^sub>m (k *\<^sub>s\<^sub>m eye)) *\<^sub>m\<^sub>v v = vec_zero"
          by blast
        thus ?thesis
          using HH
          unfolding eigenval_def
          by (rule_tac x="v" in exI) (case_tac v, simp add: field_simps)
      qed
    qed
  qed
qed

(* ---------------------------------------------------------------------------- *)
subsubsection \<open>Bilinear and Quadratic forms, Congruence, and Similarity\<close>
(* ---------------------------------------------------------------------------- *)

text \<open>Bilinear forms\<close>

definition bilinear_form where
  [simp]: "bilinear_form v1 v2 H = (vec_cnj v1) *\<^sub>v\<^sub>m H *\<^sub>v\<^sub>v v2"

lemma bilinear_form_scale_m:
  shows "bilinear_form v1 v2 (k *\<^sub>s\<^sub>m H) = k * bilinear_form v1 v2 H"
  by (cases v1, cases v2, cases H) (simp add: vec_cnj_def field_simps)

lemma bilinear_form_scale_v1:
  shows "bilinear_form (k *\<^sub>s\<^sub>v v1) v2 H = cnj k * bilinear_form v1 v2 H"
  by (cases v1, cases v2, cases H) (simp add: vec_cnj_def field_simps)

lemma bilinear_form_scale_v2:
  shows "bilinear_form  v1 (k *\<^sub>s\<^sub>v v2) H = k * bilinear_form v1 v2 H"
  by (cases v1, cases v2, cases H) (simp add: vec_cnj_def field_simps)

text \<open>Quadratic forms\<close>

definition quad_form where
  [simp]: "quad_form v H = (vec_cnj v) *\<^sub>v\<^sub>m H *\<^sub>v\<^sub>v v"

lemma quad_form_bilinear_form: 
  shows "quad_form v H = bilinear_form v v H"
  by simp

lemma quad_form_scale_v:
  shows "quad_form (k *\<^sub>s\<^sub>v v) H = cor ((cmod k)\<^sup>2) * quad_form v H"
  using bilinear_form_scale_v1 bilinear_form_scale_v2
  by (simp add: complex_mult_cnj_cmod field_simps)

lemma quad_form_scale_m:
  shows "quad_form v (k *\<^sub>s\<^sub>m H) = k * quad_form v H"
  using bilinear_form_scale_m
  by simp

lemma cnj_quad_form [simp]:
  shows "cnj (quad_form z H) = quad_form z (mat_adj H)"
  by (cases H, cases z) (auto simp add: mat_adj_def mat_cnj_def vec_cnj_def field_simps)

text \<open>Matrix congruence\<close>

text \<open>Two matrices are congruent iff they represent the same quadratic form with respect to different
bases (for example if one circline can be transformed to another by a Möbius trasformation).\<close>

definition congruence where
  [simp]: "congruence M H \<equiv> mat_adj M *\<^sub>m\<^sub>m H *\<^sub>m\<^sub>m M"

lemma congruence_nonzero:
  assumes "H \<noteq> mat_zero" and "mat_det M \<noteq> 0"
  shows "congruence M H \<noteq> mat_zero"
  using assms
  unfolding congruence_def
  by (subst mult_mm_non_zero_r, subst mult_mm_non_zero_l) (auto simp add: mat_det_adj)

lemma congruence_congruence:
  shows "congruence M1 (congruence M2 H) = congruence (M2 *\<^sub>m\<^sub>m M1) H"
  unfolding congruence_def
  apply (subst mult_mm_assoc)
  apply (subst mult_mm_assoc)
  apply (subst mat_adj_mult_mm)
  apply (subst mult_mm_assoc)
  by simp

lemma congruence_eye [simp]: 
  shows "congruence eye H = H"
  by (cases H) (simp add: mat_adj_def mat_cnj_def)

lemma congruence_congruence_inv [simp]:
  assumes "mat_det M \<noteq> 0"
  shows "congruence M (congruence (mat_inv M) H) = H"
  using assms congruence_congruence[of M "mat_inv M" H]
  using mat_inv_l[of M] mat_eye_l mat_eye_r
  unfolding congruence_def
  by (simp del: eye_def)

lemma congruence_inv:
  assumes "mat_det M \<noteq> 0" and "congruence M H = H'"
  shows "congruence (mat_inv M) H' = H"
  using assms
  using \<open>mat_det M \<noteq> 0\<close> mult_mm_inv_l[of "mat_adj M" "H *\<^sub>m\<^sub>m M" "H'"]
  using mult_mm_inv_r[of M "H" "mat_inv (mat_adj M) *\<^sub>m\<^sub>m H'"]
  by (simp add: mat_det_adj mult_mm_assoc mat_adj_inv)

lemma congruence_scale_m [simp]:
  shows "congruence M (k *\<^sub>s\<^sub>m H) = k *\<^sub>s\<^sub>m (congruence M H)"
  by (cases M, cases H) (auto simp add: mat_adj_def mat_cnj_def field_simps)

lemma inj_congruence:
  assumes "mat_det M \<noteq> 0" and "congruence M H = congruence M H'"
  shows "H = H'"
proof-
  have "H *\<^sub>m\<^sub>m M = H' *\<^sub>m\<^sub>m M "
    using assms
    using mult_mm_cancel_l[of "mat_adj M" "H *\<^sub>m\<^sub>m M" "H' *\<^sub>m\<^sub>m M"]
    by (simp add: mat_det_adj mult_mm_assoc)
  thus ?thesis
    using assms
    using mult_mm_cancel_r[of "M" "H" "H'"]
    by simp
qed

lemma mat_det_congruence [simp]:
  "mat_det (congruence M H) = (cor ((cmod (mat_det M))\<^sup>2)) * mat_det H"
  using complex_mult_cnj_cmod[of "mat_det M"]
  by (auto simp add: mat_det_adj field_simps)

lemma det_sgn_congruence [simp]:
  assumes "mat_det M \<noteq> 0"
  shows "sgn (mat_det (congruence M H)) = sgn (mat_det H)"
  using assms
  by (subst mat_det_congruence, auto simp add: sgn_mult power2_eq_square) (simp add: sgn_of_real)

lemma Re_det_sgn_congruence [simp]:
  assumes "mat_det M \<noteq> 0"
  shows "sgn (Re (mat_det (congruence M H))) = sgn (Re (mat_det H))"
proof-
  have *: "Re (mat_det (congruence M H)) = (cmod (mat_det M))\<^sup>2 * Re (mat_det H)"
    by (subst mat_det_congruence, subst Re_mult_real, rule Im_complex_of_real) (subst Re_complex_of_real, simp)
  show ?thesis
    using assms
    by (subst *) (auto simp add: sgn_mult)
qed

text \<open>Transforming a matrix $H$ by a regular matrix $M$ preserves its bilinear and quadratic forms.\<close>

lemma bilinear_form_congruence [simp]:
  assumes "mat_det M \<noteq> 0"
  shows "bilinear_form (M *\<^sub>m\<^sub>v v1) (M *\<^sub>m\<^sub>v v2) (congruence (mat_inv M) H) =
         bilinear_form v1 v2 H"
proof-
  have "mat_det (mat_adj M) \<noteq> 0"
    using assms
    by (simp add: mat_det_adj)
  show ?thesis
    unfolding bilinear_form_def congruence_def
    apply (subst mult_mv_mult_vm)
    apply (subst vec_cnj_mult_vm)
    apply (subst mat_adj_def[symmetric])
    apply (subst mult_vm_vm)
    apply (subst mult_vv_mv)
    apply (subst mult_vm_vm)
    apply (subst mat_adj_inv[OF \<open>mat_det M \<noteq> 0\<close>])
    apply (subst mult_assoc_5)
    apply (subst mat_inv_r[OF \<open>mat_det (mat_adj M) \<noteq> 0\<close>])
    apply (subst mat_inv_l[OF \<open>mat_det M \<noteq> 0\<close>])
    apply (subst mat_eye_l, subst mat_eye_r)
    by simp
qed

lemma quad_form_congruence [simp]:
  assumes "mat_det M \<noteq> 0"
  shows "quad_form (M *\<^sub>m\<^sub>v z) (congruence (mat_inv M) H) = quad_form z H"
  using bilinear_form_congruence[OF assms]
  by simp


text \<open>Similar matrices\<close>

text \<open>Two matrices are similar iff they represent the same linear operator with respect to (possibly)
different bases (e.g., if they represent the same Möbius transformation after changing the
coordinate system)\<close>

definition similarity where
  "similarity A M = mat_inv A *\<^sub>m\<^sub>m M *\<^sub>m\<^sub>m A"

lemma mat_det_similarity [simp]:
  assumes "mat_det A \<noteq> 0"
  shows "mat_det (similarity A M) = mat_det M"
  using assms
  unfolding similarity_def
  by (simp add: mat_det_inv)

lemma mat_trace_similarity [simp]:
  assumes "mat_det A \<noteq> 0"
  shows "mat_trace (similarity A M) = mat_trace M"
proof-
  obtain a b c d where AA: "A = (a, b, c, d)"
    by (cases A) auto
  obtain mA mB mC mD where MM: "M = (mA, mB, mC, mD)"
    by (cases M) auto
  have "mA * (a * d) / (a * d - b * c) + mD * (a * d) / (a * d - b * c) =
        mA + mD + mA * (b * c) / (a * d - b * c) + mD * (b * c) / (a * d - b * c)"
    using assms AA
    by (simp add: field_simps)
  thus ?thesis
    using AA MM
    by (simp add: field_simps similarity_def)
qed

lemma similarity_eye [simp]:
  shows "similarity eye M = M"
  unfolding similarity_def
  using mat_eye_l mat_eye_r
  by auto


lemma similarity_eye' [simp]:
  shows "similarity (1, 0, 0, 1) M = M"
  unfolding eye_def[symmetric]
  by (simp del: eye_def)

lemma similarity_comp [simp]:
  assumes "mat_det A1 \<noteq> 0" and "mat_det A2 \<noteq> 0"
  shows "similarity A1 (similarity A2 M) = similarity (A2*\<^sub>m\<^sub>mA1) M"
  using assms
  unfolding similarity_def
  by (simp add: mult_mm_assoc mat_inv_mult_mm)

lemma similarity_inv:
  assumes "similarity A M1 = M2" and "mat_det A \<noteq> 0"
  shows "similarity (mat_inv A) M2 = M1"
  using assms
  unfolding similarity_def
  by (metis mat_det_mult mult_mm_assoc mult_mm_inv_l mult_mm_inv_r mult_zero_left)

end
