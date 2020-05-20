(* -------------------------------------------------------------------------- *)
subsection \<open>Hermitean matrices\<close>
(* -------------------------------------------------------------------------- *)

text \<open>Hermitean matrices over $\mathbb{C}$ generalize symmetric matrices over $\mathbb{R}$. Quadratic
forms with Hermitean matrices represent circles and lines in the extended complex plane (when
applied to homogenous coordinates).\<close>

theory Hermitean_Matrices
imports Unitary_Matrices
begin

definition hermitean :: "complex_mat \<Rightarrow> bool" where
 "hermitean A \<longleftrightarrow> mat_adj A = A"

lemma hermitean_transpose:
  shows "hermitean A \<longleftrightarrow> mat_transpose A = mat_cnj A"
  unfolding hermitean_def
  by (cases A) (auto simp add: mat_adj_def mat_cnj_def)

text \<open>Characterization of 2x2 Hermitean matrices elements. 
All 2x2 Hermitean matrices are of the form 
$$
\left(
\begin{array}{cc}
A & B\\
\overline{B} & D
\end{array}
\right),
$$
for real $A$ and $D$ and complex $B$.
\<close>

lemma hermitean_mk_circline [simp]: 
  shows "hermitean (cor A, B, cnj B, cor D)"
  unfolding hermitean_def mat_adj_def mat_cnj_def
  by simp

lemma hermitean_mk_circline' [simp]:
  assumes "is_real A" and "is_real D"
  shows "hermitean (A, B, cnj B, D)"
  using assms eq_cnj_iff_real
  unfolding hermitean_def mat_adj_def mat_cnj_def
  by force

lemma hermitean_elems:
  assumes "hermitean (A, B, C, D)"
  shows "is_real A" and "is_real D" and "B = cnj C" and "cnj B = C"
  using assms eq_cnj_iff_real[of A] eq_cnj_iff_real[of D]
  by (auto simp add: hermitean_def mat_adj_def mat_cnj_def)

text \<open>Operations that preserve the Hermitean property\<close>

lemma hermitean_mat_cnj: 
  shows "hermitean H \<longleftrightarrow> hermitean (mat_cnj H)"
  by (cases H) (auto simp add:  hermitean_def mat_adj_def mat_cnj_def)

lemma hermitean_mult_real:
  assumes "hermitean H"
  shows "hermitean ((cor k) *\<^sub>s\<^sub>m H)"
  using assms
  unfolding hermitean_def
  by simp

lemma hermitean_congruence:
  assumes "hermitean H"
  shows "hermitean (congruence M H)"
  using assms
  unfolding hermitean_def
  by (auto simp add: mult_mm_assoc)

text \<open>Identity matrix is Hermitean\<close>

lemma hermitean_eye [simp]:
  shows "hermitean eye"
  by (auto simp add:  hermitean_def mat_adj_def mat_cnj_def)

lemma hermitean_eye' [simp]: 
  shows "hermitean (1, 0, 0, 1)"
  by (auto simp add:  hermitean_def mat_adj_def mat_cnj_def)

text \<open>Unit circle matrix is Hermitean\<close>

lemma hermitean_unit_circle [simp]:
  shows "hermitean (1, 0, 0, -1)"
  by (auto simp add:  hermitean_def mat_adj_def mat_cnj_def)

text \<open>Hermitean matrices have real determinant\<close>
lemma mat_det_hermitean_real:
  assumes "hermitean A"
  shows "is_real (mat_det A)"
  using assms
  unfolding hermitean_def
  by (metis eq_cnj_iff_real mat_det_adj)

text \<open>Zero matrix is the only Hermitean matrix with both determinant and trace equal
to zero\<close>
lemma hermitean_det_zero_trace_zero:
  assumes "mat_det A = 0" and "mat_trace A = (0::complex)" and "hermitean A"
  shows "A = mat_zero"
using assms
proof-
  {
    fix a d c
    assume "a * d = cnj c * c" "a + d = 0" "cnj a = a"
    from \<open>a + d = 0\<close> have "d = -a"
      by (metis add_eq_0_iff)
    hence "- (cor (Re a))\<^sup>2  = (cor (cmod c))\<^sup>2"
      using \<open>cnj a = a\<close> eq_cnj_iff_real[of a]
      using \<open>a*d = cnj c * c\<close>
      using complex_mult_cnj_cmod[of "cnj c"]
      by (simp add: power2_eq_square)
    hence "- (Re a)\<^sup>2 \<ge> 0"
      using zero_le_power2[of "cmod c"]
      by (metis Re_complex_of_real cor_squared of_real_minus)
    hence "a = 0"
      using zero_le_power2[of "Re a"]
      using \<open>cnj a = a\<close>  eq_cnj_iff_real[of a]
      by (simp add: complex_eq_if_Re_eq)
  } note * = this
  obtain a b c d where "A = (a, b, c, d)"
    by (cases A) auto
  thus ?thesis
    using *[of a d c]  *[of d a c]
    using assms \<open>A = (a, b, c, d)\<close>
    by (auto simp add: hermitean_def mat_adj_def mat_cnj_def)
qed

(* ---------------------------------------------------------------------------- *)
subsubsection \<open>Bilinear and quadratic forms with Hermitean matrices\<close>
(* ---------------------------------------------------------------------------- *)

text \<open>A Hermitean matrix $(A, B, \overline{B}, D)$, for real $A$ and $D$, gives rise to bilinear form
$A\cdot \overline{v_{11}} \cdot v_{21}+\overline{B} \cdot \overline{v_{12}} \cdot v_{21} +
B \cdot \overline{v_{11}} \cdot v_{22}+D\cdot \overline{v_{12}}\cdot v_{22}$ (acting on vectors $(v_{11}, v_{12})$ and
$(v_{21}, v_{22})$) and to the quadratic form $A \cdot \overline{v_1} \cdot v_1+\overline{B}\cdot \overline{v_2}\cdot v_1 +
B\cdot \overline{v_1}\cdot v_2 + D\cdot \overline{v_2} \cdot v_2$ (acting on the vector $(v_1, v_2)$).\<close>

lemma bilinear_form_hermitean_commute:
  assumes "hermitean H"
  shows "bilinear_form v1 v2 H = cnj (bilinear_form v2 v1 H)"
proof-
  have "v2 *\<^sub>v\<^sub>m mat_cnj H *\<^sub>v\<^sub>v vec_cnj v1 = vec_cnj v1 *\<^sub>v\<^sub>v (mat_adj H *\<^sub>m\<^sub>v v2)"
    by (subst mult_vv_commute, subst mult_mv_mult_vm, simp add: mat_adj_def mat_transpose_mat_cnj)
  also
  have "\<dots> = bilinear_form v1 v2 H"
    using assms
    by (simp add: mult_vv_mv hermitean_def)
  finally
  show ?thesis
    by (simp add: cnj_mult_vv vec_cnj_mult_vm)
qed

lemma quad_form_hermitean_real:
  assumes "hermitean H"
  shows "is_real (quad_form z H)"
  using assms
  by (subst eq_cnj_iff_real[symmetric])  (simp del: quad_form_def add: hermitean_def)

lemma quad_form_vec_cnj_mat_cnj:
  assumes "hermitean H"
  shows "quad_form (vec_cnj z) (mat_cnj H) = quad_form z H"
  using assms
  using cnj_mult_vv cnj_quad_form hermitean_def vec_cnj_mult_vm by auto

(* ---------------------------------------------------------------------------- *)
subsubsection \<open>Eigenvalues, eigenvectors and diagonalization of Hermitean matrices\<close>
(* ---------------------------------------------------------------------------- *)

text \<open>Hermitean matrices have real eigenvalues\<close>
lemma hermitean_eigenval_real:
  assumes "hermitean H" and "eigenval k H"
  shows "is_real k"
proof-
  from assms obtain v where "v \<noteq> vec_zero" "H *\<^sub>m\<^sub>v v = k *\<^sub>s\<^sub>v v"
    unfolding eigenval_def
    by blast
  have "k * (v *\<^sub>v\<^sub>v vec_cnj v) = (k *\<^sub>s\<^sub>v v) *\<^sub>v\<^sub>v (vec_cnj v)"
    by (simp add: mult_vv_scale_sv1)
  also have "... = (H *\<^sub>m\<^sub>v v) *\<^sub>v\<^sub>v (vec_cnj v)"
    using \<open>H *\<^sub>m\<^sub>v v = k *\<^sub>s\<^sub>v v\<close>
    by simp
  also have "... =  v *\<^sub>v\<^sub>v (mat_transpose H *\<^sub>m\<^sub>v (vec_cnj v))"
    by (simp add: mult_mv_vv)
  also have "... = v *\<^sub>v\<^sub>v (vec_cnj (mat_cnj (mat_transpose H) *\<^sub>m\<^sub>v v))"
    by (simp add: vec_cnj_mult_mv)
  also have "... = v *\<^sub>v\<^sub>v (vec_cnj (H *\<^sub>m\<^sub>v v))"
    using \<open>hermitean H\<close>
    by (simp add: hermitean_def mat_adj_def)
  also have "... = v *\<^sub>v\<^sub>v (vec_cnj (k *\<^sub>s\<^sub>v v))"
    using \<open>H *\<^sub>m\<^sub>v v = k *\<^sub>s\<^sub>v v\<close>
    by simp
  finally have "k * (v *\<^sub>v\<^sub>v vec_cnj v) = cnj k * (v *\<^sub>v\<^sub>v vec_cnj v)"
    by (simp add: mult_vv_scale_sv2)
  hence "k = cnj k"
    using \<open>v \<noteq> vec_zero\<close>
    using scalsquare_vv_zero[of v]
    by (simp add: mult_vv_commute)
  thus ?thesis
    by (metis eq_cnj_iff_real)
qed

text \<open>Non-diagonal Hermitean matrices have distinct eigenvalues\<close>
lemma hermitean_distinct_eigenvals:
  assumes "hermitean H"
  shows "(\<exists> k\<^sub>1 k\<^sub>2. k\<^sub>1 \<noteq> k\<^sub>2 \<and> eigenval k\<^sub>1 H \<and> eigenval k\<^sub>2 H) \<or> mat_diagonal H"
proof-
  obtain A B C D where HH: "H = (A, B, C, D)"
    by (cases H) auto
  show ?thesis
  proof (cases "B = 0")
    case True
    thus ?thesis
      using \<open>hermitean H\<close> hermitean_elems[of A B C D] HH
      by auto
  next
    case False
    have "(mat_trace H)\<^sup>2 \<noteq> 4 * mat_det H"
    proof (rule ccontr)
      have "C = cnj B" "is_real A" "is_real D"
        using hermitean_elems HH \<open>hermitean H\<close>
        by auto
      assume "\<not> ?thesis"
      hence "(A + D)\<^sup>2 = 4*(A*D - B*C)"
        using HH
        by auto
      hence "(A - D)\<^sup>2 = - 4*B*cnj B"
        using \<open>C = cnj B\<close>
        by (auto simp add: power2_eq_square field_simps)
      hence "(A - D)\<^sup>2 / cor ((cmod B)\<^sup>2) = -4"
        using \<open>B \<noteq> 0\<close> complex_mult_cnj_cmod[of B]
        by (auto simp add: field_simps)
      hence "(Re A - Re D)\<^sup>2 / (cmod B)\<^sup>2 = -4"
        using \<open>is_real A\<close> \<open>is_real D\<close> \<open>B \<noteq> 0\<close>
        using Re_divide_real[of "cor ((cmod B)\<^sup>2)" "(A - D)\<^sup>2"]
        by (auto simp add: power2_eq_square)
      thus False
        by (metis abs_neg_numeral abs_power2 neg_numeral_neq_numeral power_divide)
    qed
    show ?thesis
      apply (rule disjI1)
      apply (subst eigen_equation)+
      using complex_quadratic_equation_monic_distinct_roots[of "-mat_trace H" "mat_det H"] \<open>(mat_trace H)\<^sup>2 \<noteq> 4 * mat_det H\<close>
      by auto
  qed
qed

text \<open>Eigenvectors corresponding to different eigenvalues of Hermitean matrices are
orthogonal\<close>
lemma hermitean_ortho_eigenvecs:
  assumes "hermitean H"
  assumes "eigenpair k1 v1 H" and "eigenpair k2 v2 H" and "k1 \<noteq> k2"
  shows "vec_cnj v2 *\<^sub>v\<^sub>v v1 = 0" and "vec_cnj v1 *\<^sub>v\<^sub>v v2 = 0"
proof-
  from assms
  have "v1 \<noteq> vec_zero" "H *\<^sub>m\<^sub>v v1 = k1 *\<^sub>s\<^sub>v v1"
       "v2 \<noteq> vec_zero" "H *\<^sub>m\<^sub>v v2 = k2 *\<^sub>s\<^sub>v v2"
    unfolding eigenpair_def
    by auto
  have real_k: "is_real k1" "is_real k2"
    using assms
    using hermitean_eigenval_real[of H k1]
    using hermitean_eigenval_real[of H k2]
    unfolding eigenpair_def eigenval_def
    by blast+

  have "vec_cnj (H *\<^sub>m\<^sub>v v2) = vec_cnj (k2 *\<^sub>s\<^sub>v v2)"
    using \<open>H *\<^sub>m\<^sub>v v2 = k2 *\<^sub>s\<^sub>v v2\<close>
    by auto
  hence "vec_cnj v2 *\<^sub>v\<^sub>m H  = k2 *\<^sub>s\<^sub>v vec_cnj v2"
    using \<open>hermitean H\<close> real_k eq_cnj_iff_real[of k1] eq_cnj_iff_real[of k2]
    unfolding hermitean_def
    by (cases H, cases v2) (auto simp add: mat_adj_def mat_cnj_def vec_cnj_def)
  have "k2 * (vec_cnj v2 *\<^sub>v\<^sub>v v1) = k1 * (vec_cnj v2 *\<^sub>v\<^sub>v v1)"
    using \<open>H *\<^sub>m\<^sub>v v1 = k1 *\<^sub>s\<^sub>v v1\<close>
    using \<open>vec_cnj v2 *\<^sub>v\<^sub>m H  = k2 *\<^sub>s\<^sub>v vec_cnj v2\<close>
    by (cases v1, cases v2, cases H)
       (metis mult_vv_mv mult_vv_scale_sv1 mult_vv_scale_sv2)
  thus "vec_cnj v2 *\<^sub>v\<^sub>v v1 = 0"
    using \<open>k1 \<noteq> k2\<close>
    by simp
  hence "cnj (vec_cnj v2 *\<^sub>v\<^sub>v v1) = 0"
    by simp
  thus "vec_cnj v1 *\<^sub>v\<^sub>v v2 = 0"
    by (simp add: cnj_mult_vv mult_vv_commute)
qed

text \<open>Hermitean matrices are diagonizable by unitary matrices. Diagonal entries are
real and the sign of the determinant is preserved.\<close>
lemma hermitean_diagonizable:
  assumes "hermitean H"
  shows "\<exists> k1 k2 M. mat_det M \<noteq> 0 \<and> unitary M \<and> congruence M H = (k1, 0, 0, k2) \<and>
                    is_real k1 \<and> is_real k2 \<and> sgn (Re k1 * Re k2) = sgn (Re (mat_det H))"
proof-
  from assms
  have "(\<exists>k\<^sub>1 k\<^sub>2. k\<^sub>1 \<noteq> k\<^sub>2 \<and> eigenval k\<^sub>1 H \<and> eigenval k\<^sub>2 H) \<or> mat_diagonal H"
    using hermitean_distinct_eigenvals[of H]
    by simp
  thus ?thesis
  proof
    assume "\<exists>k\<^sub>1 k\<^sub>2. k\<^sub>1 \<noteq> k\<^sub>2 \<and> eigenval k\<^sub>1 H \<and> eigenval k\<^sub>2 H"
    then  obtain k1 k2 where  "k1 \<noteq> k2" "eigenval k1 H" "eigenval k2 H"
      using hermitean_distinct_eigenvals
      by blast
    then obtain v1 v2 where "eigenpair k1 v1 H" "eigenpair k2 v2 H"
      "v1 \<noteq> vec_zero" "v2 \<noteq> vec_zero"
      unfolding eigenval_def eigenpair_def
      by blast
    hence *: "vec_cnj v2 *\<^sub>v\<^sub>v v1 = 0" "vec_cnj v1 *\<^sub>v\<^sub>v v2 = 0"
      using \<open>k1 \<noteq> k2\<close> hermitean_ortho_eigenvecs \<open>hermitean H\<close>
      by auto
    obtain v11 v12 v21 v22 where vv: "v1 = (v11, v12)" "v2 = (v21, v22)"
      by  (cases v1, cases v2) auto
    let ?nv1' = "vec_cnj v1 *\<^sub>v\<^sub>v v1" and ?nv2' = "vec_cnj v2 *\<^sub>v\<^sub>v v2"
    let ?nv1 = "cor (sqrt (Re ?nv1'))"
    let ?nv2 = "cor (sqrt (Re ?nv2'))"
    have "?nv1' \<noteq> 0"  "?nv2' \<noteq> 0"
      using \<open>v1 \<noteq> vec_zero\<close> \<open>v2 \<noteq> vec_zero\<close> vv
      by (simp add: scalsquare_vv_zero)+
    moreover
    have "is_real ?nv1'" "is_real ?nv2'"
      using vv
      by (auto simp add: vec_cnj_def)
    ultimately
    have "?nv1 \<noteq> 0"  "?nv2 \<noteq> 0"
      using complex_eq_if_Re_eq
      by auto
    have "Re (?nv1') \<ge> 0"  "Re (?nv2') \<ge> 0"
      using vv
      by (auto simp add: vec_cnj_def)
    obtain nv1 nv2 where "nv1 = ?nv1" "nv1 \<noteq> 0"  "nv2 = ?nv2" "nv2 \<noteq> 0"
      using \<open>?nv1 \<noteq> 0\<close>  \<open>?nv2 \<noteq> 0\<close>
      by auto
    let ?M = "(1/nv1 * v11, 1/nv2 * v21, 1/nv1 * v12, 1/nv2 * v22)"

    have "is_real k1" "is_real k2"
      using  \<open>eigenval k1 H\<close> \<open>eigenval k2 H\<close> \<open>hermitean H\<close>
      by (auto simp add: hermitean_eigenval_real)
    moreover
    have "mat_det ?M \<noteq> 0"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      hence "v11 * v22 = v12 * v21"
        using \<open>nv1 \<noteq> 0\<close> \<open>nv2 \<noteq> 0\<close>
        by (auto simp add: field_simps)
      hence "\<exists> k. k \<noteq> 0 \<and> v2 = k *\<^sub>s\<^sub>v v1"
        using vv \<open>v1 \<noteq> vec_zero\<close> \<open>v2 \<noteq> vec_zero\<close>
        apply auto
        apply (rule_tac x="v21/v11" in exI, force simp add: field_simps)
        apply (rule_tac x="v21/v11" in exI, force simp add: field_simps)
        apply (rule_tac x="v22/v12" in exI, force simp add: field_simps)
        apply (rule_tac x="v22/v12" in exI, force simp add: field_simps)
        done
      thus False
        using * \<open>vec_cnj v1 *\<^sub>v\<^sub>v v2 = 0\<close> \<open>vec_cnj v2 *\<^sub>v\<^sub>v v2 \<noteq> 0\<close> vv \<open>?nv1' \<noteq> 0\<close>
        by (metis mult_vv_scale_sv2 mult_zero_right)
    qed
    moreover
    have "unitary ?M"
    proof-
      have **: "cnj nv1 * nv1 = ?nv1'"  "cnj nv2 * nv2 = ?nv2'"
        using \<open>nv1 = ?nv1\<close> \<open>nv1 \<noteq> 0\<close>  \<open>nv2 = ?nv2\<close> \<open>nv2 \<noteq> 0\<close> \<open>is_real ?nv1'\<close> \<open>is_real ?nv2'\<close>
        using \<open>Re (?nv1') \<ge> 0\<close>  \<open>Re (?nv2') \<ge> 0\<close>
        by auto
      have ***: "cnj nv1 * nv2 \<noteq> 0"  "cnj nv2 * nv1 \<noteq> 0"
        using vv \<open>nv1 = ?nv1\<close> \<open>nv1 \<noteq> 0\<close>  \<open>nv2 = ?nv2\<close> \<open>nv2 \<noteq> 0\<close> \<open>is_real ?nv1'\<close> \<open>is_real ?nv2'\<close>
        by auto           

      show ?thesis
        unfolding unitary_def
        using vv ** \<open>?nv1' \<noteq> 0\<close> \<open>?nv2' \<noteq> 0\<close> * ***
        unfolding mat_adj_def mat_cnj_def vec_cnj_def
        by simp (metis (no_types, lifting) add_divide_distrib divide_eq_0_iff divide_eq_1_iff)
    qed
    moreover
    have "congruence ?M H = (k1, 0, 0, k2)"
    proof-
      have "mat_inv ?M *\<^sub>m\<^sub>m H *\<^sub>m\<^sub>m ?M = (k1, 0, 0, k2)"
      proof-
        have *: "H *\<^sub>m\<^sub>m ?M = ?M *\<^sub>m\<^sub>m (k1, 0, 0, k2)"
          using \<open>eigenpair k1 v1 H\<close> \<open>eigenpair k2 v2 H\<close> vv \<open>?nv1 \<noteq> 0\<close> \<open>?nv2 \<noteq> 0\<close>
          unfolding eigenpair_def vec_cnj_def
          by (cases H) (smt mult_mm.simps vec_map.simps add.right_neutral add_cancel_left_left distrib_left fst_mult_sv mult.commute mult.left_commute mult_mv.simps mult_zero_right prod.sel(1) prod.sel(2) snd_mult_sv)
        show ?thesis
          using mult_mm_inv_l[of ?M "(k1, 0, 0, k2)" "H *\<^sub>m\<^sub>m ?M", OF \<open>mat_det ?M \<noteq> 0\<close> *[symmetric], symmetric]
          by (simp add: mult_mm_assoc)
      qed
      moreover
      have "mat_inv ?M = mat_adj ?M"
        using \<open>mat_det ?M \<noteq> 0\<close> \<open>unitary ?M\<close> mult_mm_inv_r[of ?M "mat_adj ?M" eye]
        by (simp add: unitary_def)
      ultimately
      show ?thesis
        by simp
    qed
    moreover
    have "sgn (Re k1 * Re k2) = sgn (Re (mat_det H))"
      using \<open>congruence ?M H = (k1, 0, 0, k2)\<close> \<open>is_real k1\<close> \<open>is_real k2\<close>
      using Re_det_sgn_congruence[of ?M H] \<open>mat_det ?M \<noteq> 0\<close> \<open>hermitean H\<close>
      by simp
    ultimately
    show ?thesis
      by (rule_tac x="k1" in exI, rule_tac x="k2" in exI, rule_tac x="?M" in exI) simp
  next
    assume "mat_diagonal H"
    then obtain A D where "H = (A, 0, 0, D)"
      by (cases H) auto
    moreover
    hence "is_real A" "is_real D"
      using \<open>hermitean H\<close> hermitean_elems[of A 0 0 D]
      by auto
    ultimately
    show ?thesis
      by (rule_tac x="A" in exI, rule_tac x="D" in exI, rule_tac x="eye" in exI) (simp add: unitary_def mat_adj_def mat_cnj_def)
  qed
qed

end
