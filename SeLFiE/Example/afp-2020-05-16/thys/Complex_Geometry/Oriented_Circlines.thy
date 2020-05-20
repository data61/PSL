(* -------------------------------------------------------------------------- *)
section \<open>Oriented circlines\<close>
(* -------------------------------------------------------------------------- *)
theory Oriented_Circlines
imports Circlines
begin

(* ----------------------------------------------------------------- *)
subsection \<open>Oriented circlines definition\<close>
(* ----------------------------------------------------------------- *)

text \<open>In this section we describe how the orientation is introduced for the circlines. Similarly as
the set of circline points, the set of disc points is introduced using the quadratic form induced by
the circline matrix --- the set of points of the circline disc is the set of points such that
satisfy that $A\cdot z\cdot \overline{z} + B\cdot \overline{z} + C\cdot z + D < 0$, where
$(A, B, C, D)$ is a circline matrix representative Hermitean matrix. As the
set of disc points must be invariant to the choice of representative, it is clear that oriented
circlines matrices are equivalent only if they are proportional by a positive real factor (recall
that unoriented circline allowed arbitrary non-zero real factors).\<close>

definition ocircline_eq_cmat :: "complex_mat \<Rightarrow> complex_mat \<Rightarrow> bool" where
  [simp]: "ocircline_eq_cmat A B \<longleftrightarrow>(\<exists> k::real. k > 0 \<and> B = cor k *\<^sub>s\<^sub>m A)"
lift_definition ocircline_eq_clmat :: "circline_mat \<Rightarrow> circline_mat \<Rightarrow> bool" is ocircline_eq_cmat
  done

lemma ocircline_eq_cmat_id [simp]:
  shows "ocircline_eq_cmat H H"
  by (simp, rule_tac x=1 in exI, simp)

quotient_type ocircline = circline_mat / ocircline_eq_clmat
proof (rule equivpI)
  show "reflp ocircline_eq_clmat"
    unfolding reflp_def
    by transfer (auto, rule_tac x="1" in exI, simp)
next
  show "symp ocircline_eq_clmat"
    unfolding symp_def
    by transfer (simp only: ocircline_eq_cmat_def, safe, rule_tac x="1/k" in exI, simp)
next
  show "transp ocircline_eq_clmat"
    unfolding transp_def
    by transfer (simp only: ocircline_eq_cmat_def, safe, rule_tac x="k*ka" in exI, simp)
qed

(* ----------------------------------------------------------------- *)
subsection \<open>Points on oriented circlines\<close>
(* ----------------------------------------------------------------- *)

text \<open>Boundary of the circline.\<close>

lift_definition on_ocircline :: "ocircline \<Rightarrow> complex_homo \<Rightarrow> bool" is on_circline_clmat_hcoords
  by transfer (simp del: quad_form_def, (erule exE)+, simp add: quad_form_scale_m quad_form_scale_v del: quad_form_def)

definition ocircline_set :: "ocircline \<Rightarrow> complex_homo set" where
  "ocircline_set H = {z. on_ocircline H z}"

lemma ocircline_set_I [simp]:
  assumes "on_ocircline H z"
  shows "z \<in> ocircline_set H"
  using assms
  unfolding ocircline_set_def
  by simp

(* ----------------------------------------------------------------- *)
subsection \<open>Disc and disc complement - in and out points\<close>
(* ----------------------------------------------------------------- *)

text \<open>Interior and the exterior of an oriented circline.\<close>

definition in_ocircline_cmat_cvec :: "complex_mat \<Rightarrow> complex_vec \<Rightarrow> bool" where
  [simp]: "in_ocircline_cmat_cvec H z \<longleftrightarrow> Re (quad_form z H) < 0"
lift_definition in_ocircline_clmat_hcoords :: "circline_mat \<Rightarrow> complex_homo_coords \<Rightarrow> bool" is in_ocircline_cmat_cvec
  done
lift_definition in_ocircline :: "ocircline \<Rightarrow> complex_homo \<Rightarrow> bool" is in_ocircline_clmat_hcoords
proof transfer
  fix H H' z z'
  assume hh: "hermitean H \<and> H \<noteq> mat_zero" and "hermitean H' \<and> H' \<noteq> mat_zero" and
             "z \<noteq> vec_zero" and "z' \<noteq> vec_zero"
  assume "ocircline_eq_cmat H H'" and "z \<approx>\<^sub>v z'"
  then obtain k k' where
    *: "0 < k" "H' = cor k *\<^sub>s\<^sub>m H" "k' \<noteq> 0" "z' = k' *\<^sub>s\<^sub>v  z"
    by auto
  hence "quad_form z' H' = cor k * cor ((cmod k')\<^sup>2) * quad_form z H"
    by (simp add: quad_form_scale_v quad_form_scale_m del: vec_cnj_sv quad_form_def)
  hence "Re (quad_form z' H') = k * (cmod k')\<^sup>2 * Re (quad_form z H)"
    using hh quad_form_hermitean_real[of H]
    by (simp add: power2_eq_square)
  thus "in_ocircline_cmat_cvec H z = in_ocircline_cmat_cvec H' z'"
    using \<open>k > 0\<close> \<open>k' \<noteq> 0\<close>
    using mult_less_0_iff
    by fastforce
qed

definition disc :: "ocircline \<Rightarrow> complex_homo set" where
  "disc H = {z. in_ocircline H z}"

lemma disc_I [simp]:
  assumes "in_ocircline H z"
  shows "z \<in> disc H"
  using assms
  unfolding disc_def
  by simp

definition out_ocircline_cmat_cvec :: "complex_mat \<Rightarrow> complex_vec \<Rightarrow> bool" where
  [simp]: "out_ocircline_cmat_cvec H z \<longleftrightarrow> Re (quad_form z H) > 0"
lift_definition out_ocircline_clmat_hcoords :: "circline_mat \<Rightarrow> complex_homo_coords \<Rightarrow> bool" is out_ocircline_cmat_cvec
  done
lift_definition out_ocircline :: "ocircline \<Rightarrow> complex_homo \<Rightarrow> bool" is out_ocircline_clmat_hcoords
proof transfer
  fix H H' z z'
  assume hh: "hermitean H \<and> H \<noteq> mat_zero" "hermitean H' \<and> H' \<noteq> mat_zero"
             "z \<noteq> vec_zero" "z' \<noteq> vec_zero"
  assume "ocircline_eq_cmat H H'" "z \<approx>\<^sub>v z'"
  then obtain k k' where
    *: "0 < k" "H' = cor k *\<^sub>s\<^sub>m H" "k' \<noteq> 0" "z' = k' *\<^sub>s\<^sub>v  z"
    by auto
  hence "quad_form z' H' = cor k * cor ((cmod k')\<^sup>2) * quad_form z H"
    by (simp add: quad_form_scale_v quad_form_scale_m del: vec_cnj_sv quad_form_def)
  hence "Re (quad_form z' H') = k * (cmod k')\<^sup>2 * Re (quad_form z H)"
    using hh quad_form_hermitean_real[of H]
    by (simp add: power2_eq_square)
  thus "out_ocircline_cmat_cvec H z = out_ocircline_cmat_cvec H' z'"
    using \<open>k > 0\<close> \<open>k' \<noteq> 0\<close>
    using zero_less_mult_pos
    by fastforce
qed

definition disc_compl :: "ocircline \<Rightarrow> complex_homo set" where
  "disc_compl H = {z. out_ocircline H z}"

text \<open>These three sets are mutually disjoint and they fill up the entire plane.\<close>

lemma disc_compl_I [simp]:
  assumes "out_ocircline H z"
  shows "z \<in> disc_compl H"
  using assms
  unfolding disc_compl_def
  by simp

lemma in_on_out:
  shows "in_ocircline H z \<or> on_ocircline H z \<or> out_ocircline H z"
  apply (transfer, transfer)
  using quad_form_hermitean_real
  using complex_eq_if_Re_eq
  by auto

lemma in_on_out_univ:
  shows "disc H \<union> disc_compl H \<union> ocircline_set H = UNIV"
  unfolding disc_def disc_compl_def ocircline_set_def
  using in_on_out[of H]
  by auto

lemma disc_inter_disc_compl [simp]:
  shows "disc H \<inter> disc_compl H = {}"
  unfolding disc_def disc_compl_def
  by auto (transfer, transfer, simp)

lemma disc_inter_ocircline_set [simp]:
  shows "disc H \<inter> ocircline_set H = {}"
  unfolding disc_def ocircline_set_def
  by auto (transfer, transfer, simp)

lemma disc_compl_inter_ocircline_set [simp]:
  shows "disc_compl H \<inter> ocircline_set H = {}"
  unfolding disc_compl_def ocircline_set_def
  by auto (transfer, transfer, simp)

(* ----------------------------------------------------------------- *)
subsection \<open>Opposite orientation\<close>
(* ----------------------------------------------------------------- *)

text \<open>Finding opposite circline is idempotent, and opposite circlines share the same set of points,
but exchange disc and its complement.\<close>

definition opposite_ocircline_cmat :: "complex_mat \<Rightarrow> complex_mat" where
  [simp]: "opposite_ocircline_cmat H = (-1) *\<^sub>s\<^sub>m H"
lift_definition opposite_ocircline_clmat :: "circline_mat \<Rightarrow> circline_mat" is opposite_ocircline_cmat
  by (auto simp add: hermitean_def mat_adj_def mat_cnj_def)
lift_definition opposite_ocircline :: "ocircline \<Rightarrow> ocircline" is opposite_ocircline_clmat
  by transfer auto

lemma opposite_ocircline_involution [simp]:
  shows "opposite_ocircline (opposite_ocircline H) = H"
  by (transfer, transfer) (auto, rule_tac x="1" in exI, simp)

lemma on_circline_opposite_ocircline_cmat [simp]:
  assumes "hermitean H \<and> H \<noteq> mat_zero" and "z \<noteq> vec_zero"
  shows "on_circline_cmat_cvec (opposite_ocircline_cmat H) z = on_circline_cmat_cvec H z"
  using assms
  by (simp add: quad_form_scale_m del: quad_form_def)

lemma on_circline_opposite_ocircline [simp]:
  shows "on_ocircline (opposite_ocircline H) z \<longleftrightarrow> on_ocircline H z"
  using on_circline_opposite_ocircline_cmat
  by (transfer, transfer, simp)

lemma ocircline_set_opposite_ocircline [simp]:
  shows "ocircline_set (opposite_ocircline H) = ocircline_set H"
  unfolding ocircline_set_def
  by auto

lemma disc_compl_opposite_ocircline [simp]:
  shows "disc_compl (opposite_ocircline H) = disc H"
  unfolding disc_def disc_compl_def
  apply auto
   apply (transfer, transfer)
   apply (auto simp add: quad_form_scale_m simp del: quad_form_def)
  apply (transfer ,transfer)
  apply (auto simp add: quad_form_scale_m simp del: quad_form_def)
  done

lemma disc_opposite_ocircline [simp]:
  shows "disc (opposite_ocircline H) = disc_compl H"
  using disc_compl_opposite_ocircline[of "opposite_ocircline H"]
  by simp

(* ----------------------------------------------------------------- *)
subsection \<open>Positive orientation. Conversion between unoriented and oriented circlines\<close>
(* ----------------------------------------------------------------- *)

text \<open>Given an oriented circline, one can trivially obtain its unoriented counterpart, and these two
share the same set of points.\<close>

lift_definition of_ocircline :: "ocircline \<Rightarrow> circline" is "id::circline_mat \<Rightarrow> circline_mat"
  by transfer (simp, erule exE, force)

lemma of_ocircline_opposite_ocircline [simp]:
  shows "of_ocircline (opposite_ocircline H) = of_ocircline H"
  by (transfer, transfer) (simp, erule exE, rule_tac x="-1" in exI, simp)

lemma on_ocircline_of_circline [simp]:
  shows "on_circline (of_ocircline H) z \<longleftrightarrow> on_ocircline H z"
  by (transfer, transfer, simp)

lemma circline_set_of_ocircline [simp]:
  shows "circline_set (of_ocircline H) = ocircline_set H"
  unfolding ocircline_set_def circline_set_def
  by (safe) (transfer, simp)+

lemma inj_of_ocircline:
  assumes "of_ocircline H = of_ocircline H'"
  shows "H = H' \<or> H = opposite_ocircline H'"
  using assms
  by (transfer, transfer) (simp, metis linorder_neqE_linordered_idom minus_of_real_eq_of_real_iff mult_minus1 mult_sm_distribution neg_0_equal_iff_equal neg_less_0_iff_less)

lemma inj_ocircline_set:
  assumes "ocircline_set H = ocircline_set H'" and "ocircline_set H \<noteq> {}"
  shows "H = H' \<or> H = opposite_ocircline H'"
proof-
  from assms 
  have "circline_set (of_ocircline H) = circline_set (of_ocircline H')"
       "circline_set (of_ocircline H') \<noteq> {}"
    by auto
  hence "of_ocircline H = of_ocircline H'"
    by (simp add: inj_circline_set)
  thus ?thesis
    by (rule inj_of_ocircline)
qed

text \<open>Positive orientation.\<close>

text \<open>Given a representative Hermitean matrix of a circline, it represents exactly one of the two
possible oriented circlines. The choice of what should be called a positive orientation is
arbitrary. We follow Schwerdtfeger \cite{schwerdtfeger}, use the leading coefficient $A$ as the
first criterion, and say that circline matrices with $A > 0$ are called positively oriented, and
with $A < 0$ negatively oriented. However, Schwerdtfeger did not discuss the possible case of $A =
0$ (the case of lines), so we had to extend his definition to achieve a total characterization.\<close>

definition pos_oriented_cmat :: "complex_mat \<Rightarrow> bool" where
  [simp]: "pos_oriented_cmat H \<longleftrightarrow>
           (let (A, B, C, D) = H
              in (Re A > 0 \<or> (Re A = 0 \<and> ((B \<noteq> 0 \<and> arg B > 0) \<or> (B = 0 \<and> Re D > 0)))))"
lift_definition pos_oriented_clmat :: "circline_mat \<Rightarrow> bool" is pos_oriented_cmat
  done

lift_definition pos_oriented :: "ocircline \<Rightarrow> bool" is pos_oriented_clmat
  by transfer
     (case_tac circline_mat1, case_tac circline_mat2, simp, erule exE, simp, 
      metis mult_pos_pos zero_less_mult_pos)

lemma pos_oriented:
  shows "pos_oriented H \<or> pos_oriented (opposite_ocircline H)"
proof (transfer, transfer)
  fix H
  assume hh: "hermitean H \<and> H \<noteq> mat_zero"
  obtain A B C D where HH: "H = (A, B, C, D)"
    by (cases H) auto
  moreover
  hence "Re A = 0 \<and> Re D = 0 \<longrightarrow> B \<noteq> 0"
    using hh hermitean_elems[of A B C D]
    by (cases A, cases D) (auto simp add: Complex_eq)
  moreover
  have "B \<noteq> 0 \<and> \<not> 0 < arg B \<longrightarrow> 0 < arg (- B)"
    using canon_ang_plus_pi2[of "arg B"] arg_bounded[of B]
    by (auto simp add: arg_uminus)
  ultimately
  show "pos_oriented_cmat H \<or> pos_oriented_cmat (opposite_ocircline_cmat H)"
    by auto
qed

lemma pos_oriented_opposite_ocircline_cmat [simp]:
  assumes "hermitean H \<and> H \<noteq> mat_zero"
  shows  "pos_oriented_cmat (opposite_ocircline_cmat H) \<longleftrightarrow> \<not> pos_oriented_cmat H"
proof-
  obtain A B C D where HH: "H = (A, B, C, D)"
    by (cases H) auto
  moreover
  hence "Re A = 0 \<and> Re D = 0 \<longrightarrow> B \<noteq> 0"
    using assms hermitean_elems[of A B C D]
    by (cases A, cases D) (auto simp add: Complex_eq)
  moreover
  have "B \<noteq> 0 \<and> \<not> 0 < arg B \<longrightarrow> 0 < arg (- B)"
    using canon_ang_plus_pi2[of "arg B"] arg_bounded[of B]
    by (auto simp add: arg_uminus)
  moreover
  have "B \<noteq> 0 \<and> 0 < arg B \<longrightarrow> \<not> 0 < arg (- B)"
    using canon_ang_plus_pi1[of "arg B"] arg_bounded[of B]
    by (auto simp add: arg_uminus)
  ultimately
  show "pos_oriented_cmat (opposite_ocircline_cmat H) = (\<not> pos_oriented_cmat H)"
    by simp (metis not_less_iff_gr_or_eq)
qed

lemma pos_oriented_opposite_ocircline [simp]:
  shows "pos_oriented (opposite_ocircline H) \<longleftrightarrow> \<not> pos_oriented H"
  using pos_oriented_opposite_ocircline_cmat
  by (transfer, transfer, simp)

lemma pos_oriented_circle_inf:
  assumes "\<infinity>\<^sub>h \<notin> ocircline_set H"
  shows "pos_oriented H \<longleftrightarrow> \<infinity>\<^sub>h \<notin> disc H"
  using assms
  unfolding ocircline_set_def disc_def
  apply simp
proof (transfer, transfer)
  fix H
  assume hh: "hermitean H \<and> H \<noteq> mat_zero"
  obtain A B C D where HH: "H = (A, B, C, D)"
    by (cases H) auto
  hence "is_real A"
    using hh hermitean_elems
    by auto
  assume "\<not> on_circline_cmat_cvec H \<infinity>\<^sub>v"
  thus "pos_oriented_cmat H = (\<not> in_ocircline_cmat_cvec H  \<infinity>\<^sub>v)"
    using HH \<open>is_real A\<close>
    by (cases A) (auto simp add: vec_cnj_def Complex_eq)
qed

lemma pos_oriented_euclidean_circle:
  assumes "is_circle (of_ocircline H)"
          "(a, r) = euclidean_circle (of_ocircline H)"
          "circline_type (of_ocircline H) < 0"
  shows "pos_oriented H \<longleftrightarrow> of_complex a \<in> disc H"
  using assms
  unfolding disc_def
  apply simp
proof (transfer, transfer)
  fix H a r
  assume hh: "hermitean H \<and> H \<noteq> mat_zero"
  obtain A B C D where HH: "H = (A, B, C, D)"
    by (cases H) auto
  hence "is_real A" "is_real D" "C = cnj B"
    using hh hermitean_elems
    by auto

  assume *: "\<not> circline_A0_cmat (id H)" "(a, r) = euclidean_circle_cmat (id H)" "circline_type_cmat (id H) < 0"
  hence "A \<noteq> 0" "Re A \<noteq> 0"
    using HH \<open>is_real A\<close>
    by (case_tac[!] A) (auto simp add: Complex_eq)

  have "Re (A*D - B*C) < 0"
    using \<open>circline_type_cmat (id H) < 0\<close> HH
    by simp

  have **: "(A * (D * cnj A) - B * (C * cnj A)) / (A * cnj A) = (A*D - B*C) / A"
    using \<open>A \<noteq> 0\<close>
    by (simp add: field_simps)
  hence ***: "0 < Re A \<longleftrightarrow> Re ((A * (D * cnj A) - B * (C * cnj A)) / (A * cnj A)) < 0"
    using \<open>is_real A\<close> \<open>A \<noteq> 0\<close> \<open>Re (A*D - B*C) < 0\<close>
    by (simp add: Re_divide_real divide_less_0_iff)

  have "Re D - Re (cnj B * B / cnj A) < Re ((C - cnj B * A / cnj A) * B / A)" if "Re A > 0"
    using HH * \<open>is_real A\<close> that
    by simp (smt "**" "***" cnj.simps(1) cnj.simps(2) complex_eq diff_divide_distrib left_diff_distrib'
               minus_complex.simps(1) mult.commute nonzero_mult_div_cancel_right)?
  moreover have "Re A > 0" if "Re D - Re (cnj B * B / cnj A) < Re ((C - cnj B * A / cnj A) * B / A)"
    using HH * \<open>is_real A\<close> that
    by simp (smt "**" "***" cnj.simps(1) cnj.simps(2) complex_eq diff_divide_distrib left_diff_distrib'
               minus_complex.simps(1) mult.commute nonzero_mult_div_cancel_right)?
  ultimately show "pos_oriented_cmat H = in_ocircline_cmat_cvec H (of_complex_cvec a)"
    using HH \<open>Re A \<noteq> 0\<close> * \<open>is_real A\<close> by (auto simp add: vec_cnj_def)
qed

text \<open>Introduce positive orientation\<close>

definition of_circline_cmat :: "complex_mat \<Rightarrow> complex_mat" where
 [simp]: "of_circline_cmat H = (if pos_oriented_cmat H then H else opposite_ocircline_cmat H)"

lift_definition of_circline_clmat :: "circline_mat \<Rightarrow> circline_mat" is of_circline_cmat
  by (auto simp add: hermitean_def mat_adj_def mat_cnj_def)

lemma of_circline_clmat_def':
  shows "of_circline_clmat H = (if pos_oriented_clmat H then H else opposite_ocircline_clmat H)"
  by transfer simp

lemma pos_oriented_cmat_mult_positive':
  assumes
    "hermitean H1 \<and> H1 \<noteq> mat_zero" and
    "hermitean H2 \<and> H2 \<noteq> mat_zero" and
    "\<exists>k. k > 0 \<and> H2 = cor k *\<^sub>s\<^sub>m H1" and
    "pos_oriented_cmat H1"
  shows "pos_oriented_cmat H2"
proof-
  obtain A1 B1 C1 D1 A2 B2 C2 D2
    where HH: "H1 = (A1, B1, C1, D1)" "H2 = (A2, B2, C2, D2)"
    by (cases H1, cases H2)
  thus ?thesis
    using assms
    by fastforce
qed

lemma pos_oriented_cmat_mult_positive:
  assumes
    "hermitean H1 \<and> H1 \<noteq> mat_zero" and
    "hermitean H2 \<and> H2 \<noteq> mat_zero" and
    "\<exists>k. k > 0 \<and> H2 = cor k *\<^sub>s\<^sub>m H1"
  shows 
    "pos_oriented_cmat H1 \<longleftrightarrow> pos_oriented_cmat H2"
proof-
  from assms(3) obtain k where "k > 0 \<and> H2 = cor k *\<^sub>s\<^sub>m H1"
    by auto
  hence "\<exists>k. k > 0 \<and> H1 = cor k *\<^sub>s\<^sub>m H2"
    by (rule_tac x="1/k" in exI, auto)
  thus ?thesis
    using assms pos_oriented_cmat_mult_positive'
    by blast
qed


lemma pos_oriented_cmat_mult_negative:
  assumes
    "hermitean H1 \<and> H1 \<noteq> mat_zero" and
    "hermitean H2 \<and> H2 \<noteq> mat_zero" and
    "\<exists>k. k < 0 \<and> H2 = cor k *\<^sub>s\<^sub>m H1"
  shows
    "pos_oriented_cmat H1 \<longleftrightarrow> \<not> pos_oriented_cmat H2"
  using assms
proof-
  obtain A B C D A1 B1 C1 D1
    where *: "H1 = (A, B, C, D)" "H2 = (A1, B1, C1, D1)"
    by (cases H1, cases H2) auto
  hence **: "is_real A" "is_real D" "is_real A1" "is_real D1" "B = 0 \<longleftrightarrow> C = 0" "B1 = 0 \<longleftrightarrow> C1 = 0"
    using assms hermitean_elems[of A B C D] hermitean_elems[of A1 B1 C1 D1]
    by auto
  show ?thesis
  proof (rule iffI)
    assume H1: "pos_oriented_cmat H1"
    show "\<not> pos_oriented_cmat H2"
    proof (cases "Re A > 0")
      case True
      thus ?thesis
        using assms * ** mult_neg_pos
        by fastforce
    next
      case False
      show ?thesis
      proof (cases "B = 0")
        case True
        thus ?thesis
          using assms * ** H1 `\<not> Re A > 0` mult_neg_pos
          by fastforce
      next
        case False
        thus ?thesis
          using arg_uminus_opposite_sign[of B] arg_mult_real_negative
          using assms * ** H1 `\<not> Re A > 0` mult_neg_pos
          by fastforce
      qed
    qed
  next
    assume H2: "\<not> pos_oriented_cmat H2"
    show "pos_oriented_cmat H1"
    proof (cases "Re A > 0")
      case True
      thus ?thesis
        using * ** mult_neg_pos
        by fastforce
    next
      case False
      show ?thesis
      proof (cases "B = 0")
        case True
        thus ?thesis 
          using assms * ** H2 `\<not> Re A > 0`
          by simp (smt arg_0_iff arg_complex_of_real_negative arg_complex_of_real_positive arg_mult_eq complex_of_real_Re mult.right_neutral mult_eq_0_iff of_real_0 of_real_1 zero_complex.simps(1))
      next
        case False
        thus ?thesis
          using assms `\<not> Re A > 0` H2 * **
          using arg_uminus_opposite_sign[of B]
          by (cases "Re A = 0", auto simp add: mult_neg_neg)
      qed
    qed
  qed
qed
   
lift_definition of_circline :: "circline \<Rightarrow> ocircline" is of_circline_clmat
proof transfer
  fix H1 H2
  assume hh:
    "hermitean H1 \<and> H1 \<noteq> mat_zero"
    "hermitean H2 \<and> H2 \<noteq> mat_zero"
  assume "circline_eq_cmat H1 H2"
  then obtain k where *: "k \<noteq> 0 \<and> H2 = cor k *\<^sub>s\<^sub>m H1"
    by auto
  show "ocircline_eq_cmat (of_circline_cmat H1) (of_circline_cmat H2)"
  proof (cases "k > 0")
    case True
    hence "pos_oriented_cmat H1 = pos_oriented_cmat H2"
      using * pos_oriented_cmat_mult_positive[OF hh]
      by blast
    thus ?thesis
      using hh * \<open>k > 0\<close>
      apply (simp del: pos_oriented_cmat_def)
      apply (rule conjI)
       apply (rule impI)
       apply (simp, rule_tac x=k in exI, simp)
      apply (rule impI)
      apply (simp, rule_tac x=k in exI, simp)
      done
  next
    case False
    hence "k < 0"
      using *
      by simp
    hence "pos_oriented_cmat H1 \<longleftrightarrow> \<not> (pos_oriented_cmat H2)"
      using * pos_oriented_cmat_mult_negative[OF hh]
      by blast
    thus ?thesis
      using hh * \<open>k < 0\<close>
      apply (simp del: pos_oriented_cmat_def)
      apply (rule conjI)
       apply (rule impI)
       apply (simp, rule_tac x="-k" in exI, simp)
      apply (rule impI)
      apply (simp, rule_tac x="-k" in exI, simp)
      done
  qed
qed

lemma pos_oriented_of_circline [simp]:
  shows "pos_oriented (of_circline H)"
  using pos_oriented_opposite_ocircline_cmat
  by (transfer, transfer, simp)

lemma of_ocircline_of_circline [simp]:
  shows "of_ocircline (of_circline H) = H"
  apply (transfer, auto simp add: of_circline_clmat_def')
  apply (transfer, simp, rule_tac x="-1" in exI, simp)
  done

lemma of_circline_of_ocircline_pos_oriented [simp]:
  assumes "pos_oriented H"
  shows "of_circline (of_ocircline H) = H"
  using assms
  by (transfer, transfer, simp, rule_tac x=1 in exI, simp)

lemma inj_of_circline:
  assumes "of_circline H = of_circline H'"
  shows "H = H'"
  using assms
proof (transfer, transfer)
  fix H H'
  assume "ocircline_eq_cmat (of_circline_cmat H) (of_circline_cmat H')"
  then obtain k where "k > 0" "of_circline_cmat H' = cor k *\<^sub>s\<^sub>m of_circline_cmat H"
    by auto
  thus "circline_eq_cmat H H'"
    using mult_sm_inv_l[of "-1" "H'" "cor k *\<^sub>s\<^sub>m H"]
    using mult_sm_inv_l[of "-1" "H'" "(- (cor k)) *\<^sub>s\<^sub>m H"]
    apply (simp split: if_split_asm)
    apply (rule_tac x="k" in exI, simp)
    apply (rule_tac x="-k" in exI, simp)
    apply (rule_tac x="-k" in exI, simp)
    apply (rule_tac x="k" in exI, simp)
    done
qed

lemma of_circline_of_ocircline:
  shows "of_circline (of_ocircline H') = H' \<or> 
         of_circline (of_ocircline H') = opposite_ocircline H'"
proof (cases "pos_oriented H'")
  case True
  thus ?thesis
    by auto
next
  case False
  hence "pos_oriented (opposite_ocircline H')"
    using pos_oriented
    by auto
  thus ?thesis
    using of_ocircline_opposite_ocircline[of H']
    using of_circline_of_ocircline_pos_oriented [of "opposite_ocircline H'"]
    by auto
qed

(* -------------------------------------------------------------------------- *)
subsubsection \<open>Set of points on oriented and unoriented circlines\<close>
(* -------------------------------------------------------------------------- *)

lemma ocircline_set_of_circline [simp]:
  shows "ocircline_set (of_circline H) = circline_set H"
  unfolding ocircline_set_def circline_set_def
proof (safe)
  fix z
  assume "on_ocircline (of_circline H) z"
  thus "on_circline H z"
    by (transfer, transfer, simp del: on_circline_cmat_cvec_def opposite_ocircline_cmat_def split: if_split_asm)
next
  fix z
  assume "on_circline H z"
  thus "on_ocircline (of_circline H) z"
    by (transfer, transfer, simp del: on_circline_cmat_cvec_def opposite_ocircline_cmat_def split: if_split_asm)
qed

(* ----------------------------------------------------------------- *)
subsection \<open>Some special oriented circlines and discs\<close>
(* ----------------------------------------------------------------- *)

lift_definition mk_ocircline :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> ocircline" is mk_circline_clmat
  done

text \<open>oriented unit circle and unit disc\<close>

lift_definition ounit_circle :: "ocircline" is unit_circle_clmat
  done

lemma pos_oriented_ounit_circle [simp]: 
  shows "pos_oriented ounit_circle"
  by (transfer, transfer, simp)

lemma of_ocircline_ounit_circle [simp]:
  shows "of_ocircline ounit_circle = unit_circle"
  by (transfer, transfer, simp)

lemma of_circline_unit_circle [simp]:
  shows "of_circline (unit_circle) = ounit_circle"
  by (transfer, transfer, simp)

lemma ocircline_set_ounit_circle [simp]:
  shows "ocircline_set ounit_circle = circline_set unit_circle"
  apply (subst of_circline_unit_circle[symmetric])
  apply (subst ocircline_set_of_circline)
  apply simp
  done

definition unit_disc :: "complex_homo set" where
  "unit_disc = disc ounit_circle"

definition unit_disc_compl :: "complex_homo set" where
  "unit_disc_compl = disc_compl ounit_circle"

definition unit_circle_set :: "complex_homo set" where
  "unit_circle_set = circline_set unit_circle"

lemma zero_in_unit_disc [simp]:
  shows "0\<^sub>h \<in> unit_disc"
  unfolding unit_disc_def disc_def
  by (simp, transfer, transfer) (simp add: Let_def vec_cnj_def)

lemma one_notin_unit_dic [simp]: 
  shows "1\<^sub>h \<notin> unit_disc"
  unfolding unit_disc_def disc_def
  by (simp, transfer, transfer) (simp add: Let_def vec_cnj_def)

lemma inf_notin_unit_disc [simp]:
  shows "\<infinity>\<^sub>h \<notin> unit_disc"
  unfolding unit_disc_def disc_def
  by (simp, transfer, transfer) (simp add: Let_def vec_cnj_def)

lemma unit_disc_iff_cmod_lt_1 [simp]:
  shows "of_complex c \<in> unit_disc \<longleftrightarrow> cmod c < 1"
  unfolding unit_disc_def disc_def
  by (simp, transfer, transfer, simp add: vec_cnj_def cmod_def power2_eq_square)

lemma unit_disc_cmod_square_lt_1 [simp]:
  assumes "z \<in> unit_disc"
  shows "(cmod (to_complex z))\<^sup>2 < 1"
  using assms inf_or_of_complex[of z]
  by (auto simp add: abs_square_less_1)

lemma unit_disc_to_complex_inj:
  assumes "u \<in> unit_disc" and "v \<in> unit_disc"
  assumes "to_complex u = to_complex v"
  shows "u = v"
  using assms
  using inf_or_of_complex[of u] inf_or_of_complex[of v]
  by auto

lemma inversion_unit_disc [simp]: 
  shows "inversion ` unit_disc = unit_disc_compl"
  unfolding unit_disc_def unit_disc_compl_def disc_def disc_compl_def
proof safe
  fix x
  assume "in_ocircline ounit_circle x"
  thus "out_ocircline ounit_circle (inversion x)"
    unfolding inversion_def
    by (transfer, transfer, auto simp add: vec_cnj_def)
next
  fix x
  assume *: "out_ocircline ounit_circle x"
  show "x \<in> inversion ` Collect (in_ocircline ounit_circle)"
  proof (rule image_eqI)
    show "x = inversion (inversion x)"
      by auto
  next
    show "inversion x \<in> Collect (in_ocircline ounit_circle)"
      using *
      unfolding inversion_def
      by (simp, transfer, transfer, auto simp add: vec_cnj_def)
  qed
qed

lemma inversion_unit_disc_compl [simp]: 
  shows "inversion ` unit_disc_compl = unit_disc"
proof-
  have "inversion ` (inversion ` unit_disc) = unit_disc"
    by (auto simp del: inversion_unit_disc simp add: image_iff)
  thus ?thesis
    by simp
qed

lemma inversion_noteq_unit_disc:
  assumes "u \<in> unit_disc" and "v \<in> unit_disc"
  shows "inversion u \<noteq> v"
proof-
  from assms
  have "inversion u \<in> unit_disc_compl"
    by (metis image_eqI inversion_unit_disc)
  thus ?thesis
    using assms
    unfolding unit_disc_def unit_disc_compl_def
    using disc_inter_disc_compl
    by fastforce
qed

lemma in_ocircline_ounit_circle_conjugate [simp]:
  assumes "in_ocircline ounit_circle z"
  shows "in_ocircline ounit_circle (conjugate z)"
  using assms
  by (transfer, transfer, auto simp add: vec_cnj_def)

lemma conjugate_unit_disc [simp]:
  shows "conjugate ` unit_disc = unit_disc"                
  unfolding unit_disc_def disc_def
  apply (auto simp add: image_iff)
  apply (rule_tac x="conjugate x" in exI, simp)
  done

lemma conjugate_in_unit_disc [simp]:
  assumes "z \<in> unit_disc"
  shows "conjugate z \<in> unit_disc"
  using conjugate_unit_disc
  using assms
  by blast

lemma out_ocircline_ounit_circle_conjugate [simp]:
  assumes "out_ocircline ounit_circle z"
  shows "out_ocircline ounit_circle (conjugate z)"
  using assms
  by (transfer, transfer, auto simp add: vec_cnj_def)

lemma conjugate_unit_disc_compl [simp]:
  shows "conjugate ` unit_disc_compl = unit_disc_compl"                
  unfolding unit_disc_compl_def disc_compl_def
  apply (auto simp add: image_iff)
  apply (rule_tac x="conjugate x" in exI, simp)
  done

lemma conjugate_in_unit_disc_compl [simp]:
  assumes "z \<in> unit_disc_compl"
  shows "conjugate z \<in> unit_disc_compl"
  using conjugate_unit_disc_compl
  using assms
  by blast

(* -------------------------------------------------------------------------- *)
subsubsection \<open>Oriented x axis and lower half plane\<close>
(* -------------------------------------------------------------------------- *)

lift_definition o_x_axis :: "ocircline" is x_axis_clmat
done

lemma o_x_axis_pos_oriented [simp]:
  shows "pos_oriented o_x_axis"
  by (transfer, transfer, simp)

lemma of_ocircline_o_x_axis [simp]: 
  shows "of_ocircline o_x_axis = x_axis"
  by (transfer, transfer, simp)

lemma of_circline_x_axis [simp]:
  shows "of_circline x_axis = o_x_axis"
  using of_circline_of_ocircline_pos_oriented[of o_x_axis]
  using o_x_axis_pos_oriented
  by simp

lemma ocircline_set_circline_set_x_axis [simp]: 
  shows "ocircline_set o_x_axis = circline_set x_axis"
  by (subst of_circline_x_axis[symmetric], subst ocircline_set_of_circline, simp)

lemma ii_in_disc_o_x_axis [simp]: 
  shows "ii\<^sub>h \<notin> disc o_x_axis"
  unfolding disc_def
  by simp (transfer, transfer, simp add: Let_def vec_cnj_def)

lemma ii_notin_disc_o_x_axis [simp]:
  shows "ii\<^sub>h \<in> disc_compl o_x_axis"
  unfolding disc_compl_def
  by simp (transfer, transfer, simp add: Let_def vec_cnj_def)

lemma of_complex_in_o_x_axis_disc [simp]:
  shows "of_complex z \<in> disc o_x_axis \<longleftrightarrow> Im z < 0"
  unfolding disc_def
  by auto (transfer, transfer, simp add: vec_cnj_def)+

lemma inf_notin_disc_o_x_axis [simp]:
  shows "\<infinity>\<^sub>h \<notin> disc o_x_axis"
  unfolding disc_def
  by simp (transfer, transfer, simp add: vec_cnj_def)

lemma disc_o_x_axis:
  shows "disc o_x_axis = of_complex ` {z. Im z < 0}"
proof-
  {
    fix z
    assume "z \<in> disc o_x_axis"
    hence "\<exists> x. Im x < 0 \<and> z = of_complex x"
      using inf_or_of_complex[of z]
      by auto
  }
  thus ?thesis
    by (auto simp add: image_iff)
qed

(* -------------------------------------------------------------------------- *)
subsubsection \<open>Oriented single point circline\<close>
(* -------------------------------------------------------------------------- *)

lift_definition  o_circline_point_0 :: "ocircline" is circline_point_0_clmat
done

lemma of_ocircline_o_circline_point_0 [simp]: 
  shows "of_ocircline o_circline_point_0 = circline_point_0"
  by (transfer, transfer, simp)

(* ----------------------------------------------------------------- *)
subsection \<open>Möbius action on oriented circlines and discs\<close>
(* ----------------------------------------------------------------- *)

text \<open>Möbius action on an oriented circline is the same as on to an unoriented circline.\<close>

lift_definition moebius_ocircline :: "moebius \<Rightarrow> ocircline \<Rightarrow> ocircline" is moebius_circline_mmat_clmat
  apply (transfer, transfer)
  apply simp
  apply ((erule exE)+, (erule conjE)+)
  apply (simp add: mat_inv_mult_sm)
  apply (rule_tac x="ka / Re (k * cnj k)" in exI, auto simp add: complex_mult_cnj_cmod power2_eq_square)
  done

text \<open>Möbius action on (unoriented) circlines could have been defined using the action on oriented
circlines, but not the other way around.\<close>

lemma moebius_circline_ocircline:
  shows "moebius_circline M H = of_ocircline (moebius_ocircline M (of_circline H))"
  apply (transfer, simp add: of_circline_clmat_def', safe)
  apply (transfer, simp, rule_tac x="-1" in exI, simp)
  done

lemma moebius_ocircline_circline:
  shows "moebius_ocircline M H = of_circline (moebius_circline M (of_ocircline H)) \<or>
         moebius_ocircline M H = opposite_ocircline (of_circline (moebius_circline M (of_ocircline H)))"
  apply (transfer, simp add: of_circline_clmat_def', safe)
  apply (transfer, simp, rule_tac x="1" in exI, simp)
  apply (transfer, simp, erule_tac x="1" in allE, simp)
  done

text \<open>Möbius action on oriented circlines have many nice properties as it was the case with
Möbius action on (unoriented) circlines. These transformations are injective and form group under
composition.\<close>

lemma inj_moebius_ocircline [simp]:
  shows "inj (moebius_ocircline M)"
  unfolding inj_on_def
proof (safe)
  fix H H'
  assume "moebius_ocircline M H = moebius_ocircline M H'"
  thus "H = H'"
  proof (transfer, transfer)
    fix M H H' :: complex_mat
    assume "mat_det M \<noteq> 0"
    let ?iM = "mat_inv M"
    assume "ocircline_eq_cmat (moebius_circline_cmat_cmat M H) (moebius_circline_cmat_cmat M H')"
    then obtain k where "congruence ?iM H' = congruence ?iM (cor k *\<^sub>s\<^sub>m H)" "k > 0"
      by (auto simp del: congruence_def)
    thus "ocircline_eq_cmat H H'"
      using \<open>mat_det M \<noteq> 0\<close> inj_congruence[of ?iM H' "cor k *\<^sub>s\<^sub>m H"] mat_det_inv[of M]
      by auto
  qed
qed

lemma moebius_ocircline_id_moebius [simp]:
  shows "moebius_ocircline id_moebius H = H"
  by (transfer, transfer) (force simp add: mat_adj_def mat_cnj_def)

lemma moebius_ocircline_comp [simp]:
  shows "moebius_ocircline (moebius_comp M1 M2) H = moebius_ocircline M1 (moebius_ocircline M2 H)"
  by (transfer, transfer, simp, rule_tac x=1 in exI, simp add: mat_inv_mult_mm mult_mm_assoc)

lemma moebius_ocircline_comp_inv_left [simp]:
  shows "moebius_ocircline (moebius_inv M) (moebius_ocircline M H) = H"
  by (subst moebius_ocircline_comp[symmetric]) simp

lemma moebius_ocircline_comp_inv_right [simp]:
  shows "moebius_ocircline M (moebius_ocircline (moebius_inv M) H) = H"
  by (subst moebius_ocircline_comp[symmetric]) simp

lemma moebius_ocircline_opposite_ocircline [simp]:
  shows "moebius_ocircline M (opposite_ocircline H) = opposite_ocircline (moebius_ocircline M H)"
  by (transfer, transfer, simp, rule_tac x=1 in exI, simp)

text \<open>Möbius action on oriented circlines preserve the set of points of the circline.\<close>

lemma ocircline_set_moebius_ocircline [simp]:
  shows "ocircline_set (moebius_ocircline M H) = moebius_pt M ` ocircline_set H" (is "?lhs = ?rhs")
proof-
  have "?rhs = circline_set (moebius_circline M (of_ocircline H))"
    by simp
  thus ?thesis
    using moebius_ocircline_circline[of M H]
    by auto
qed

lemma ocircline_set_fix_iff_ocircline_fix:
  assumes "ocircline_set H' \<noteq> {}"
  shows "ocircline_set (moebius_ocircline M H) = ocircline_set H' \<longleftrightarrow>
         moebius_ocircline M H = H' \<or> moebius_ocircline M H = opposite_ocircline H'"
  using assms
  using inj_ocircline_set[of "moebius_ocircline M H" H']
  by (auto simp del: ocircline_set_moebius_ocircline)

lemma disc_moebius_ocircline [simp]:
  shows "disc (moebius_ocircline M H) = moebius_pt M ` (disc H)"
proof (safe)
  fix z
  assume "z \<in> disc H"
  thus "moebius_pt M z \<in> disc (moebius_ocircline M H)"
    unfolding disc_def
  proof (safe)
    assume "in_ocircline H z"
    thus "in_ocircline (moebius_ocircline M H) (moebius_pt M z)"
    proof (transfer, transfer)
      fix H M :: complex_mat and z :: complex_vec
      assume "mat_det M \<noteq> 0"
      assume "in_ocircline_cmat_cvec H z"
      thus "in_ocircline_cmat_cvec (moebius_circline_cmat_cmat M H) (moebius_pt_cmat_cvec M z)"
        using \<open>mat_det M \<noteq> 0\<close> quad_form_congruence[of M z]
        by simp
    qed
  qed
next
  fix z
  assume "z \<in> disc (moebius_ocircline M H)"
  thus "z \<in> moebius_pt M ` disc H"
    unfolding disc_def
  proof(safe)
    assume "in_ocircline (moebius_ocircline M H) z"
    show "z \<in> moebius_pt M ` Collect (in_ocircline H)"
    proof
      show "z = moebius_pt M (moebius_pt (moebius_inv M) z)"
        by simp
    next
      show "moebius_pt (moebius_inv M) z \<in> Collect (in_ocircline H)"
        using \<open>in_ocircline (moebius_ocircline M H) z\<close>
      proof (safe, transfer, transfer)
        fix M H :: complex_mat and z :: complex_vec
        assume "mat_det M \<noteq> 0"
        hence "congruence (mat_inv (mat_inv M)) (congruence (mat_inv M) H) = H"
          by (simp del: congruence_def)
        hence "quad_form z (congruence (mat_inv M) H) = quad_form (mat_inv M *\<^sub>m\<^sub>v z) H"
          using quad_form_congruence[of "mat_inv M" "z" "congruence (mat_inv M) H"]
          using \<open>mat_det M \<noteq> 0\<close> mat_det_inv[of "M"]
          by simp
        moreover
        assume "in_ocircline_cmat_cvec (moebius_circline_cmat_cmat M H) z"
        ultimately
        show "in_ocircline_cmat_cvec H (moebius_pt_cmat_cvec (moebius_inv_cmat M) z)"
          by simp
      qed
    qed
  qed
qed

lemma disc_compl_moebius_ocircline [simp]:
  shows "disc_compl (moebius_ocircline M H) = moebius_pt M ` (disc_compl H)"
proof (safe)
  fix z
  assume "z \<in> disc_compl H"
  thus "moebius_pt M z \<in> disc_compl (moebius_ocircline M H)"
    unfolding disc_compl_def
  proof (safe)
    assume "out_ocircline H z"
    thus "out_ocircline (moebius_ocircline M H) (moebius_pt M z)"
    proof (transfer, transfer)
      fix H M :: complex_mat and z :: complex_vec
      assume "mat_det M \<noteq> 0"
      assume "out_ocircline_cmat_cvec H z"
      thus "out_ocircline_cmat_cvec (moebius_circline_cmat_cmat M H) (moebius_pt_cmat_cvec M z)"
        using \<open>mat_det M \<noteq> 0\<close> quad_form_congruence[of M z]
        by simp
    qed
  qed
next
  fix z
  assume "z \<in> disc_compl (moebius_ocircline M H)"
  thus "z \<in> moebius_pt M ` disc_compl H"
    unfolding disc_compl_def
  proof(safe)
    assume "out_ocircline (moebius_ocircline M H) z"
    show "z \<in> moebius_pt M ` Collect (out_ocircline H)"
    proof
      show "z = moebius_pt M (moebius_pt (moebius_inv M) z)"
        by simp
    next
      show "moebius_pt (moebius_inv M) z \<in> Collect (out_ocircline H)"
        using \<open>out_ocircline (moebius_ocircline M H) z\<close>
      proof (safe, transfer, transfer)
        fix M H :: complex_mat and z :: complex_vec
        assume "mat_det M \<noteq> 0"
        hence "congruence (mat_inv (mat_inv M)) (congruence (mat_inv M) H) = H"
          by (simp del: congruence_def)
        hence "quad_form z (congruence (mat_inv M) H) = quad_form (mat_inv M *\<^sub>m\<^sub>v z) H"
          using quad_form_congruence[of "mat_inv M" "z" "congruence (mat_inv M) H"]
          using \<open>mat_det M \<noteq> 0\<close> mat_det_inv[of "M"]
          by simp
        moreover
        assume "out_ocircline_cmat_cvec (moebius_circline_cmat_cmat M H) z"
        ultimately
        show "out_ocircline_cmat_cvec H (moebius_pt_cmat_cvec (moebius_inv_cmat M) z)"
          by simp
      qed
    qed
  qed
qed

(* ----------------------------------------------------------------- *)
subsection \<open>Orientation after Möbius transformations\<close>
(* ----------------------------------------------------------------- *)

text \<open>All Euclidean similarities preserve circline orientation.\<close>

lemma moebius_similarity_oriented_lines_to_oriented_lines:
  assumes "a \<noteq> 0"
  shows "\<infinity>\<^sub>h \<in> ocircline_set H \<longleftrightarrow> \<infinity>\<^sub>h \<in> ocircline_set (moebius_ocircline (moebius_similarity a b) H)"
  using moebius_similarity_lines_to_lines[OF \<open>a \<noteq> 0\<close>, of b "of_ocircline H"]
  by simp

lemma moebius_similarity_preserve_orientation':
  assumes "a \<noteq> 0" and "\<infinity>\<^sub>h \<notin> ocircline_set H" and "pos_oriented H"
  shows "pos_oriented (moebius_ocircline (moebius_similarity a b) H)"
proof-
  let ?M = "moebius_similarity a b"
  let ?H = "moebius_ocircline ?M H"
  have "\<infinity>\<^sub>h \<notin> ocircline_set ?H"
    using \<open>\<infinity>\<^sub>h \<notin> ocircline_set H\<close> moebius_similarity_oriented_lines_to_oriented_lines[OF \<open>a \<noteq> 0\<close>]
    by simp

  have "\<infinity>\<^sub>h \<in> disc_compl H"
    using \<open>\<infinity>\<^sub>h \<notin> ocircline_set H\<close> \<open>pos_oriented H\<close> pos_oriented_circle_inf[of H] in_on_out
    unfolding disc_def disc_compl_def ocircline_set_def
    by auto
  hence "\<infinity>\<^sub>h \<in> disc_compl ?H"
    using moebius_similarity_inf[OF \<open>a \<noteq> 0\<close>, of b]
    by force
  thus "pos_oriented ?H"
    using pos_oriented_circle_inf[of ?H] disc_inter_disc_compl[of ?H] \<open>\<infinity>\<^sub>h \<notin> ocircline_set ?H\<close>
    by auto
qed

lemma moebius_similarity_preserve_orientation:
  assumes "a \<noteq> 0" and "\<infinity>\<^sub>h \<notin> ocircline_set H"
  shows "pos_oriented H \<longleftrightarrow> pos_oriented(moebius_ocircline (moebius_similarity a b) H)"
proof-
  let ?M = "moebius_similarity a b"
  let ?H = "moebius_ocircline ?M H"
  have "\<infinity>\<^sub>h \<notin> ocircline_set ?H"
    using \<open>\<infinity>\<^sub>h \<notin> ocircline_set H\<close> moebius_similarity_oriented_lines_to_oriented_lines[OF \<open>a \<noteq> 0\<close>]
    by simp

  have *: "H = moebius_ocircline (- moebius_similarity a b) ?H"
    by simp
  show ?thesis
    using \<open>a \<noteq> 0\<close>
    using moebius_similarity_preserve_orientation' [OF \<open>a \<noteq> 0\<close> \<open>\<infinity>\<^sub>h \<notin> ocircline_set H\<close>]
    using moebius_similarity_preserve_orientation'[OF _   \<open>\<infinity>\<^sub>h \<notin> ocircline_set ?H\<close>, of "1/a" "-b/a"]
    using moebius_similarity_inv[of a b, OF \<open>a \<noteq> 0\<close>]  *
    by auto
qed

lemma reciprocal_preserve_orientation:
  assumes "0\<^sub>h \<in> disc_compl H"
  shows "pos_oriented (moebius_ocircline moebius_reciprocal H)"
proof-
  have "\<infinity>\<^sub>h \<in> disc_compl (moebius_ocircline moebius_reciprocal H)"
    using assms
    by force
  thus "pos_oriented (moebius_ocircline moebius_reciprocal H)"
    using pos_oriented_circle_inf[of "moebius_ocircline moebius_reciprocal H"]
    using disc_inter_disc_compl[of "moebius_ocircline moebius_reciprocal H"]
    using disc_compl_inter_ocircline_set[of "moebius_ocircline moebius_reciprocal H"]
    by auto
qed


lemma reciprocal_not_preserve_orientation:
  assumes "0\<^sub>h \<in> disc H"
  shows "\<not> pos_oriented (moebius_ocircline moebius_reciprocal H)"
proof-
  let ?H = "moebius_ocircline moebius_reciprocal H"
  have "\<infinity>\<^sub>h \<in> disc ?H"
    using assms
    by force
  thus "\<not> pos_oriented ?H"
    using pos_oriented_circle_inf[of ?H] disc_inter_ocircline_set[of ?H]
    by auto
qed

text \<open>Orientation of the image of a given oriented circline $H$ under a given Möbius transformation
$M$ depends on whether the pole of $M$ (the point that $M$ maps to $\infty_{hc}$) lies in the disc
or in the disc complement of $H$ (if it is on the set of $H$, then it maps onto a line and we do not
discuss the orientation).\<close>

lemma pole_in_disc:
  assumes "M = mk_moebius a b c d" and "c \<noteq> 0" and "a*d - b*c \<noteq> 0"
  assumes "is_pole M z" "z \<in> disc H"
  shows "\<not> pos_oriented (moebius_ocircline M H)"
proof-
  let ?t1 = "moebius_translation (a / c)"
  let ?rd = "moebius_rotation_dilatation ((b * c - a * d) / (c * c))"
  let ?r =  "moebius_reciprocal"
  let ?t2 = "moebius_translation (d / c)"

  have "0\<^sub>h = moebius_pt (moebius_translation (d/c)) z"
    using pole_mk_moebius[of a b c d z] assms
    by simp

  have "z \<notin> ocircline_set H"
    using \<open>z \<in> disc H\<close> disc_inter_ocircline_set[of H]
    by blast      
                                              
  hence "0\<^sub>h \<notin> ocircline_set (moebius_ocircline ?t2 H)"
    using \<open>0\<^sub>h = moebius_pt ?t2 z\<close>
    using moebius_pt_neq_I[of z _ ?t2]
    by force

  hence *: "\<infinity>\<^sub>h \<notin> ocircline_set (moebius_ocircline (?r + ?t2) H)"
    using \<open>0\<^sub>h = moebius_pt (moebius_translation (d / c)) z\<close>
    by (metis circline_set_moebius_circline circline_set_moebius_circline_iff circline_set_of_ocircline moebius_pt_comp moebius_reciprocal ocircline_set_moebius_ocircline plus_moebius_def reciprocal_zero)

    
  hence **: "\<infinity>\<^sub>h \<notin> ocircline_set (moebius_ocircline (?rd + ?r + ?t2) H)"
    using \<open>a*d - b*c \<noteq> 0\<close> \<open>c \<noteq> 0\<close>
    unfolding moebius_rotation_dilatation_def
    using moebius_similarity_oriented_lines_to_oriented_lines[of _ "moebius_ocircline (?r + ?t2) H"]
    by (metis divide_eq_0_iff divisors_zero moebius_ocircline_comp plus_moebius_def right_minus_eq)

  have "\<not> pos_oriented (moebius_ocircline (?r + ?t2) H)"
    using pole_mk_moebius[of a b c d z] assms
    using reciprocal_not_preserve_orientation
    by force
  hence "\<not> pos_oriented (moebius_ocircline (?rd + ?r + ?t2) H)"
    using *
    using \<open>a*d - b*c \<noteq> 0\<close> \<open>c \<noteq> 0\<close>
    using moebius_similarity_preserve_orientation[of _ "moebius_ocircline (?r + ?t2) H"]
    unfolding moebius_rotation_dilatation_def
    by simp    
  hence "\<not> pos_oriented (moebius_ocircline (?t1 + ?rd + ?r + ?t2) H)"
    using **
    using moebius_similarity_preserve_orientation[of _ "moebius_ocircline (?rd + ?r + ?t2) H"]
    unfolding moebius_translation_def
    by simp

  thus ?thesis
    using assms
    by simp (subst moebius_decomposition, simp_all)
qed

lemma pole_in_disc_compl:
  assumes "M = mk_moebius a b c d" and "c \<noteq> 0" and "a*d - b*c \<noteq> 0"
  assumes "is_pole M z" and "z \<in> disc_compl H"
  shows "pos_oriented (moebius_ocircline M H)"
proof-
  let ?t1 = "moebius_translation (a / c)"
  let ?rd = "moebius_rotation_dilatation ((b * c - a * d) / (c * c))"
  let ?r = "moebius_reciprocal"
  let ?t2 = "moebius_translation (d / c)"

  have "0\<^sub>h = moebius_pt (moebius_translation (d/c)) z"
    using pole_mk_moebius[of a b c d z] assms
    by simp

  have "z \<notin> ocircline_set H"
    using \<open>z \<in> disc_compl H\<close> disc_compl_inter_ocircline_set[of H]
    by blast
  hence "0\<^sub>h \<notin> ocircline_set (moebius_ocircline ?t2 H)"
    using \<open>0\<^sub>h = moebius_pt ?t2 z\<close>
    using moebius_pt_neq_I[of z _ ?t2]
    by force
  hence *: "\<infinity>\<^sub>h \<notin> ocircline_set (moebius_ocircline (?r + ?t2) H)"
    using \<open>0\<^sub>h = moebius_pt (moebius_translation (d / c)) z\<close> 
    by (metis circline_set_moebius_circline circline_set_moebius_circline_iff circline_set_of_ocircline moebius_pt_comp moebius_reciprocal ocircline_set_moebius_ocircline plus_moebius_def reciprocal_zero)

  hence **: "\<infinity>\<^sub>h \<notin> ocircline_set (moebius_ocircline (?rd + ?r + ?t2) H)"
    using \<open>a*d - b*c \<noteq> 0\<close> \<open>c \<noteq> 0\<close>
    unfolding moebius_rotation_dilatation_def
    using moebius_similarity_oriented_lines_to_oriented_lines[of _ "moebius_ocircline (?r + ?t2) H"]
    by (metis divide_eq_0_iff divisors_zero moebius_ocircline_comp plus_moebius_def right_minus_eq)

  have "pos_oriented (moebius_ocircline (?r + ?t2) H)"
    using pole_mk_moebius[of a b c d z] assms
    using reciprocal_preserve_orientation
    by force
  hence "pos_oriented (moebius_ocircline (?rd + ?r + ?t2) H)"
    using *
    using \<open>a*d - b*c \<noteq> 0\<close> \<open>c \<noteq> 0\<close>
    using moebius_similarity_preserve_orientation[of _ "moebius_ocircline (?r + ?t2) H"]
    unfolding moebius_rotation_dilatation_def
    by simp
  hence "pos_oriented (moebius_ocircline (?t1 + ?rd + ?r + ?t2) H)"
    using **
    using moebius_similarity_preserve_orientation[of _ "moebius_ocircline (?rd + ?r + ?t2) H"]
    unfolding moebius_translation_def
    by simp

  thus ?thesis
    using assms
    by simp (subst moebius_decomposition, simp_all)
qed

(* ----------------------------------------------------------------- *)
subsection \<open>Oriented circlines uniqueness\<close>
(* ----------------------------------------------------------------- *)

lemma ocircline_01inf:
  assumes "0\<^sub>h \<in> ocircline_set H \<and> 1\<^sub>h \<in> ocircline_set H \<and> \<infinity>\<^sub>h \<in> ocircline_set H"
  shows "H = o_x_axis \<or> H = opposite_ocircline o_x_axis"
proof-
  have "0\<^sub>h \<in> circline_set (of_ocircline H) \<and> 1\<^sub>h \<in> circline_set (of_ocircline H) \<and> \<infinity>\<^sub>h \<in> circline_set (of_ocircline H)"
    using assms
    by simp
  hence "of_ocircline H = x_axis"
    using unique_circline_01inf'
    by auto
  thus "H = o_x_axis \<or> H = opposite_ocircline o_x_axis"
    by (metis inj_of_ocircline of_ocircline_o_x_axis)
qed

lemma unique_ocircline_01inf:
  shows "\<exists>! H. 0\<^sub>h \<in> ocircline_set H \<and> 1\<^sub>h \<in> ocircline_set H \<and> \<infinity>\<^sub>h \<in> ocircline_set H \<and> ii\<^sub>h \<notin> disc H"
proof
  show "0\<^sub>h \<in> ocircline_set o_x_axis \<and> 1\<^sub>h \<in> ocircline_set o_x_axis \<and> \<infinity>\<^sub>h \<in> ocircline_set o_x_axis \<and> ii\<^sub>h \<notin> disc o_x_axis"
    by simp
next
  fix H
  assume "0\<^sub>h \<in> ocircline_set H \<and> 1\<^sub>h \<in> ocircline_set H \<and> \<infinity>\<^sub>h \<in> ocircline_set H \<and> ii\<^sub>h \<notin> disc H"
  hence "0\<^sub>h \<in> ocircline_set H \<and> 1\<^sub>h \<in> ocircline_set H \<and> \<infinity>\<^sub>h \<in> ocircline_set H" "ii\<^sub>h \<notin> disc H"
    by auto
  hence "H = o_x_axis \<or> H = opposite_ocircline o_x_axis"
    using ocircline_01inf
    by simp
  thus "H = o_x_axis"           
    using \<open>ii\<^sub>h \<notin> disc H\<close>
    by auto
qed

lemma unique_ocircline_set:
  assumes "A \<noteq> B" and "A \<noteq> C" and "B \<noteq> C"
  shows "\<exists>! H. pos_oriented H \<and> (A \<in> ocircline_set H \<and> B \<in> ocircline_set H \<and> C \<in> ocircline_set H)"
proof-
  obtain M where *: "moebius_pt M A = 0\<^sub>h"  "moebius_pt M B = 1\<^sub>h" "moebius_pt M C = \<infinity>\<^sub>h"
    using ex_moebius_01inf[OF assms]
    by auto
  let ?iM = "moebius_pt (moebius_inv M)"
  have **: "?iM 0\<^sub>h = A"  "?iM 1\<^sub>h = B"  "?iM \<infinity>\<^sub>h = C"
    using *
    by (auto simp add: moebius_pt_invert)
  let ?H = "moebius_ocircline (moebius_inv M) o_x_axis"
  have 1: "A \<in> ocircline_set ?H" "B \<in> ocircline_set ?H" "C \<in> ocircline_set ?H"
    using **
    by auto
  have 2: "\<And> H'. A \<in> ocircline_set H' \<and> B \<in> ocircline_set H' \<and> C \<in> ocircline_set H' \<Longrightarrow> H' = ?H \<or> H' = opposite_ocircline ?H"
  proof-
    fix H'
    let ?H' = "ocircline_set H'" and ?H'' = "ocircline_set (moebius_ocircline M H')"
    assume "A \<in> ocircline_set H' \<and> B \<in> ocircline_set H' \<and> C \<in> ocircline_set H'"
    hence "moebius_pt M A \<in> ?H''" "moebius_pt M B \<in> ?H''" "moebius_pt M C \<in> ?H''"
      by auto
    hence "0\<^sub>h \<in> ?H''" "1\<^sub>h \<in> ?H''"  "\<infinity>\<^sub>h \<in> ?H''"
      using *
      by auto
    hence "moebius_ocircline M H' = o_x_axis \<or> moebius_ocircline M H' = opposite_ocircline o_x_axis"
      using ocircline_01inf
      by auto
    hence "o_x_axis = moebius_ocircline M H' \<or>  o_x_axis = opposite_ocircline (moebius_ocircline M H')"
      by auto
    thus "H' = ?H \<or> H' = opposite_ocircline ?H"
    proof
      assume *: "o_x_axis = moebius_ocircline M H'"
      show "H' = moebius_ocircline (moebius_inv M) o_x_axis \<or> H' = opposite_ocircline (moebius_ocircline (moebius_inv M) o_x_axis)"
        by (rule disjI1) (subst *, simp)
    next
      assume *: "o_x_axis = opposite_ocircline (moebius_ocircline M H')"
      show "H' = moebius_ocircline (moebius_inv M) o_x_axis \<or> H' = opposite_ocircline (moebius_ocircline (moebius_inv M) o_x_axis)"
        by (rule disjI2) (subst *, simp)
    qed
  qed

  show ?thesis (is "\<exists>! x. ?P x")
  proof (cases "pos_oriented ?H")
    case True
    show ?thesis
    proof
      show "?P ?H"
        using 1 True
        by auto
    next
      fix H
      assume "?P H"
      thus "H = ?H"
        using 1 2[of H] True
        by auto
    qed
  next
    case False
    let ?OH = "opposite_ocircline ?H"
    show ?thesis
    proof
      show "?P ?OH"
        using 1 False
        by auto
    next
      fix H
      assume "?P H"
      thus "H = ?OH"
        using False 2[of H]
        by auto
    qed
  qed
qed

lemma ocircline_set_0h:
  assumes "ocircline_set H = {0\<^sub>h}"
  shows "H = o_circline_point_0 \<or> H = opposite_ocircline (o_circline_point_0)"
proof-
  have "of_ocircline H = circline_point_0"
    using assms
    using unique_circline_type_zero_0' card_eq1_circline_type_zero[of "of_ocircline H"]
    by auto
  thus ?thesis
    by (metis inj_of_ocircline of_ocircline_o_circline_point_0)
qed


end
