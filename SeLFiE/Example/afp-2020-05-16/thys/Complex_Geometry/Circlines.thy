(* ---------------------------------------------------------------------------- *)
section \<open>Circlines\<close>
(* ---------------------------------------------------------------------------- *)
theory Circlines
  imports More_Set Moebius Hermitean_Matrices Elementary_Complex_Geometry
begin

(* ----------------------------------------------------------------- *)
subsection \<open>Definition of circlines\<close>
(* ----------------------------------------------------------------- *)

text \<open>In our formalization we follow the approach described by Schwerdtfeger
\cite{schwerdtfeger} and represent circlines by Hermitean, non-zero
$2\times 2$ matrices. In the original formulation, a matrix
$\left(\begin{array}{cc}A & B\\C & D\end{array}\right)$ corresponds to
the equation $A\cdot z\cdot \overline{z} + B\cdot \overline{z} + C\cdot z + D = 0$,
where $C = \overline{B}$ and $A$ and $D$ are real (as the matrix is
Hermitean).\<close>

abbreviation hermitean_nonzero where
  "hermitean_nonzero \<equiv> {H. hermitean H \<and> H \<noteq> mat_zero}"

typedef circline_mat = hermitean_nonzero
by (rule_tac x="eye" in exI) (auto simp add: hermitean_def mat_adj_def mat_cnj_def)

setup_lifting type_definition_circline_mat


definition circline_eq_cmat :: "complex_mat \<Rightarrow> complex_mat \<Rightarrow> bool" where
 [simp]: "circline_eq_cmat A B \<longleftrightarrow> (\<exists> k::real. k \<noteq> 0 \<and> B = cor k *\<^sub>s\<^sub>m A)"

lemma symp_circline_eq_cmat: "symp circline_eq_cmat"
  unfolding symp_def
proof ((rule allI)+, rule impI)
  fix x y
  assume "circline_eq_cmat x y"
  then obtain k where "k \<noteq> 0 \<and> y = cor k *\<^sub>s\<^sub>m x"
    by auto
  hence  "1 / k \<noteq> 0 \<and> x = cor (1 / k) *\<^sub>s\<^sub>m y"
    by auto
  thus "circline_eq_cmat y x"
    unfolding circline_eq_cmat_def
    by blast
qed

text\<open>Hermitean non-zero matrices are equivalent only to such matrices\<close>
lemma circline_eq_cmat_hermitean_nonzero:
  assumes "hermitean H \<and> H \<noteq> mat_zero" "circline_eq_cmat H H'"
  shows "hermitean H' \<and> H' \<noteq> mat_zero"
  using assms
  by (metis circline_eq_cmat_def hermitean_mult_real nonzero_mult_real of_real_eq_0_iff)


lift_definition circline_eq_clmat :: "circline_mat \<Rightarrow> circline_mat \<Rightarrow> bool" is circline_eq_cmat
  done

lemma circline_eq_clmat_refl [simp]: "circline_eq_clmat H H"
  by transfer (simp, rule_tac x="1" in exI, simp)

quotient_type circline = circline_mat / circline_eq_clmat
proof (rule equivpI)
  show "reflp circline_eq_clmat"
    unfolding reflp_def
    by transfer (auto, rule_tac x="1" in exI, simp)
next
  show "symp circline_eq_clmat"
    unfolding symp_def
    by transfer (auto, (rule_tac x="1/k" in exI, simp)+)
next
  show "transp circline_eq_clmat"
    unfolding transp_def
    by transfer (simp, safe, (rule_tac x="ka*k" in exI, simp)+)
qed

text \<open>Circline with specified matrix\<close>

text \<open>An auxiliary constructor @{term mk_circline} returns a circline (an
equivalence class) for given four complex numbers $A$, $B$, $C$ and
$D$ (provided that they form a Hermitean, non-zero matrix).\<close>

definition mk_circline_cmat :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex_mat" where
[simp]: "mk_circline_cmat A B C D =
          (let M = (A, B, C, D)
            in if M \<in> hermitean_nonzero then
                  M
               else
                  eye)"

lift_definition mk_circline_clmat :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> circline_mat" is mk_circline_cmat
  by (auto simp add: Let_def hermitean_def mat_adj_def mat_cnj_def)

lift_definition mk_circline :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> circline" is mk_circline_clmat
  done

lemma ex_mk_circline:
  shows "\<exists> A B C D. H = mk_circline A B C D \<and> hermitean (A, B, C, D) \<and> (A, B, C, D) \<noteq> mat_zero"
proof (transfer, transfer)
  fix H
  assume *: "hermitean H \<and> H \<noteq> mat_zero"
  obtain A B C D where "H = (A, B, C, D)"
    by (cases " H", auto)
  hence "circline_eq_cmat H (mk_circline_cmat A B C D) \<and> hermitean (A, B, C, D) \<and> (A, B, C, D) \<noteq> mat_zero"
    using *
    by auto
  thus "\<exists> A B C D. circline_eq_cmat H (mk_circline_cmat A B C D) \<and> hermitean (A, B, C, D) \<and> (A, B, C, D) \<noteq> mat_zero"
    by blast
qed

(* ----------------------------------------------------------------- *)
subsection \<open>Circline type\<close>
(* ----------------------------------------------------------------- *)

definition circline_type_cmat :: "complex_mat \<Rightarrow> real" where
  [simp]: "circline_type_cmat H = sgn (Re (mat_det H))"

lift_definition circline_type_clmat :: "circline_mat \<Rightarrow> real" is circline_type_cmat
  done

lift_definition circline_type :: "circline \<Rightarrow> real" is circline_type_clmat
  by transfer (simp, erule exE, simp add: sgn_mult)

lemma circline_type: "circline_type H = -1 \<or> circline_type H = 0 \<or> circline_type H = 1"
  by (transfer, transfer, simp add: sgn_if)

lemma circline_type_mk_circline [simp]:
  assumes "(A, B, C, D) \<in> hermitean_nonzero"
  shows  "circline_type (mk_circline A B C D) = sgn (Re (A*D - B*C))"
  using assms
  by (transfer, transfer, simp)

(* ----------------------------------------------------------------- *)
subsection \<open>Points on the circline\<close>
(* ----------------------------------------------------------------- *)

text \<open>Each circline determines a corresponding set of points. Again, a description given in
homogeneous coordinates is a bit better than the original description defined only for ordinary
complex numbers. The point with homogeneous coordinates $(z_1, z_2)$ will belong to the set of
circline points iff $A \cdot z_1\cdot \overline{z_1} + B\cdot \overline{z_1} \cdot z_2 + C\cdot z_1 \cdot\overline{z_2} +
D\cdot z_2 \cdot \overline{z_2} = 0$. Note that this is a quadratic form determined by a vector of
homogeneous coordinates and the Hermitean matrix.\<close>

definition on_circline_cmat_cvec :: "complex_mat \<Rightarrow> complex_vec \<Rightarrow> bool" where
  [simp]: "on_circline_cmat_cvec H z \<longleftrightarrow> quad_form z H = 0"

lift_definition on_circline_clmat_hcoords :: "circline_mat \<Rightarrow> complex_homo_coords \<Rightarrow> bool" is on_circline_cmat_cvec
  done

lift_definition on_circline :: "circline \<Rightarrow> complex_homo \<Rightarrow> bool" is on_circline_clmat_hcoords
  by transfer (simp del: quad_form_def, (erule exE)+, simp del: quad_form_def add: quad_form_scale_m quad_form_scale_v)

definition circline_set :: "circline \<Rightarrow> complex_homo set" where
  "circline_set H = {z. on_circline H z}"

lemma circline_set_I [simp]:
  assumes "on_circline H z"
  shows "z \<in> circline_set H"
  using assms
  unfolding circline_set_def
  by auto

abbreviation circline_equation where
  "circline_equation A B C D z1 z2 \<equiv> A*z1*cnj z1 + B*z2*cnj z1 + C*cnj z2*z1 + D*z2*cnj z2 = 0"

lemma on_circline_cmat_cvec_circline_equation:
  "on_circline_cmat_cvec (A, B, C, D) (z1, z2) \<longleftrightarrow> circline_equation A B C D z1 z2"
  by (simp add: vec_cnj_def field_simps)

lemma circline_equation:
  assumes "H = mk_circline A B C D" and "(A, B, C, D) \<in> hermitean_nonzero"
  shows "of_complex z \<in> circline_set H \<longleftrightarrow> circline_equation A B C D z 1"
  using assms
  unfolding circline_set_def
  by simp (transfer, transfer, simp add: vec_cnj_def field_simps)

text \<open>Circlines trough 0 and inf.\<close>
text \<open>The circline represents a line when $A=0$ or a circle, otherwise.\<close>

definition circline_A0_cmat :: "complex_mat \<Rightarrow> bool" where
  [simp]: "circline_A0_cmat H \<longleftrightarrow> (let (A, B, C, D) = H in A = 0)"
lift_definition circline_A0_clmat :: "circline_mat \<Rightarrow> bool" is circline_A0_cmat
  done
lift_definition circline_A0 :: "circline \<Rightarrow> bool" is circline_A0_clmat
  by transfer auto

abbreviation is_line where
  "is_line H \<equiv> circline_A0 H"

abbreviation is_circle where
  "is_circle H \<equiv> \<not> circline_A0 H"

definition circline_D0_cmat :: "complex_mat \<Rightarrow> bool" where
  [simp]: "circline_D0_cmat H \<longleftrightarrow> (let (A, B, C, D) = H in D = 0)"
lift_definition circline_D0_clmat :: "circline_mat \<Rightarrow> bool" is circline_D0_cmat
  done
lift_definition circline_D0 :: "circline \<Rightarrow> bool" is circline_D0_clmat
  by transfer auto

lemma inf_on_circline: "on_circline H \<infinity>\<^sub>h \<longleftrightarrow> circline_A0 H"
  by (transfer, transfer, auto simp add: vec_cnj_def)

lemma
  inf_in_circline_set: "\<infinity>\<^sub>h \<in> circline_set H \<longleftrightarrow> is_line H"
  using inf_on_circline
  unfolding circline_set_def
  by simp

lemma zero_on_circline: "on_circline H 0\<^sub>h \<longleftrightarrow> circline_D0 H"
  by (transfer, transfer, auto simp add: vec_cnj_def)

lemma
  zero_in_circline_set: "0\<^sub>h \<in> circline_set H \<longleftrightarrow> circline_D0 H"
  using zero_on_circline
  unfolding circline_set_def
  by simp

(* ----------------------------------------------------------------- *)
subsection \<open>Connection with circles and lines in the classic complex plane\<close>
(* ----------------------------------------------------------------- *)

text \<open>Every Euclidean circle and Euclidean line can be represented by a
circline.\<close>

lemma classic_circline:
  assumes "H = mk_circline A B C D" and "hermitean (A, B, C, D) \<and> (A, B, C, D) \<noteq> mat_zero"
  shows "circline_set H - {\<infinity>\<^sub>h} = of_complex ` circline (Re A) B (Re D)"
using assms
unfolding circline_set_def
proof (safe)
  fix z
  assume "hermitean (A, B, C, D)" "(A, B, C, D) \<noteq> mat_zero" "z \<in> circline (Re A) B (Re D)"
    thus "on_circline (mk_circline A B C D) (of_complex z)"
      using hermitean_elems[of A B C D]
      by (transfer, transfer) (auto simp add: circline_def vec_cnj_def field_simps)
next
  fix z
  assume "of_complex z = \<infinity>\<^sub>h"
  thus False
    by simp
next
  fix z
  assume "hermitean (A, B, C, D)" "(A, B, C, D) \<noteq> mat_zero" "on_circline (mk_circline A B C D) z" "z \<notin> of_complex ` circline (Re A) B (Re D)"
  moreover
  have "z \<noteq> \<infinity>\<^sub>h \<longrightarrow> z \<in> of_complex ` circline (Re A) B (Re D)"
  proof
    assume "z \<noteq> \<infinity>\<^sub>h"
    show "z \<in> of_complex ` circline (Re A) B (Re D)"
    proof
      show "z = of_complex (to_complex z)"
        using \<open>z \<noteq> \<infinity>\<^sub>h\<close>
        by simp
    next
      show "to_complex z \<in> circline (Re A) B (Re D)"
        using \<open>on_circline (mk_circline A B C D) z\<close> \<open>z \<noteq> \<infinity>\<^sub>h\<close>
        using \<open>hermitean (A, B, C, D)\<close> \<open>(A, B, C, D) \<noteq> mat_zero\<close>
      proof (transfer, transfer)
        fix A B C D and z :: complex_vec
        obtain z1 z2 where zz: "z = (z1, z2)"
          by (cases z, auto)
        assume *: "z \<noteq> vec_zero"  "\<not> z \<approx>\<^sub>v \<infinity>\<^sub>v"
                  "on_circline_cmat_cvec (mk_circline_cmat A B C D) z"
                  "hermitean (A, B, C, D)" "(A, B, C, D) \<noteq> mat_zero"
        have "z2 \<noteq> 0"
          using \<open>z \<noteq> vec_zero\<close> \<open>\<not> z \<approx>\<^sub>v \<infinity>\<^sub>v\<close>
          using inf_cvec_z2_zero_iff zz
          by blast
        thus "to_complex_cvec z \<in> circline (Re A) B (Re D)"
          using * zz
          using hermitean_elems[of A B C D]
          by (simp add: vec_cnj_def circline_def field_simps)
      qed
    qed
  qed
  ultimately
  show "z = \<infinity>\<^sub>h"
    by simp
qed

text \<open>The matrix of the circline representing circle determined with center and radius.\<close>
definition mk_circle_cmat :: "complex \<Rightarrow> real \<Rightarrow> complex_mat" where
  [simp]: "mk_circle_cmat a r = (1, -a, -cnj a, a*cnj a - cor r*cor r)"

lift_definition mk_circle_clmat :: "complex \<Rightarrow> real \<Rightarrow> circline_mat" is mk_circle_cmat
  by (simp add: hermitean_def mat_adj_def mat_cnj_def)

lift_definition mk_circle :: "complex \<Rightarrow> real \<Rightarrow> circline" is mk_circle_clmat
  done

lemma is_circle_mk_circle: "is_circle (mk_circle a r)"
  by (transfer, transfer, simp)

lemma circline_set_mk_circle [simp]:
  assumes "r \<ge> 0"
  shows "circline_set (mk_circle a r) = of_complex ` circle a r"
proof-
  let ?A = "1" and ?B = "-a" and ?C = "-cnj a" and ?D = "a*cnj a - cor r*cor r"
  have *: "(?A, ?B, ?C, ?D) \<in> {H. hermitean H \<and> H \<noteq> mat_zero}"
    by (simp add: hermitean_def mat_adj_def mat_cnj_def)
  have "mk_circle a r = mk_circline ?A ?B ?C ?D"
    using *
    by (transfer, transfer, simp)
  hence "circline_set (mk_circle a r) - {\<infinity>\<^sub>h} = of_complex ` circline ?A ?B (Re ?D)"
    using classic_circline[of "mk_circle a r" ?A ?B ?C ?D] *
    by simp
  moreover
  have "circline ?A ?B (Re ?D) = circle a r"
    by (rule circline_circle[of ?A "Re ?D" "?B" "circline ?A ?B (Re ?D)" "a" "r*r" r], simp_all add: cmod_square \<open>r \<ge> 0\<close>)
  moreover
  have "\<infinity>\<^sub>h \<notin> circline_set (mk_circle a r)"
    using inf_in_circline_set[of "mk_circle a r"] is_circle_mk_circle[of a r]
    by auto
  ultimately
  show ?thesis
    unfolding circle_def
    by simp
qed

text \<open>The matrix of the circline representing line determined with two (not equal) complex points.\<close>
definition mk_line_cmat :: "complex \<Rightarrow> complex \<Rightarrow> complex_mat" where
  [simp]: "mk_line_cmat z1 z2 =
    (if z1 \<noteq> z2 then
          let B = \<i> * (z2 - z1) in (0, B, cnj B, -cnj_mix B z1)
    else
          eye)"

lift_definition mk_line_clmat :: "complex \<Rightarrow> complex \<Rightarrow> circline_mat" is mk_line_cmat
  by (auto simp add: Let_def hermitean_def mat_adj_def mat_cnj_def  split: if_split_asm)

lift_definition mk_line :: "complex \<Rightarrow> complex \<Rightarrow> circline" is mk_line_clmat
  done

lemma circline_set_mk_line [simp]:
  assumes "z1 \<noteq> z2"
  shows "circline_set (mk_line z1 z2) - {\<infinity>\<^sub>h} = of_complex ` line z1 z2"
proof-
  let ?A = "0" and ?B = "\<i>*(z2 - z1)"
  let ?C = "cnj ?B" and ?D = "-cnj_mix ?B z1"
  have *: "(?A, ?B, ?C, ?D) \<in> {H. hermitean H \<and> H \<noteq> mat_zero}"
    using assms
    by (simp add: hermitean_def mat_adj_def mat_cnj_def)
  have "mk_line z1 z2 = mk_circline ?A ?B ?C ?D"
    using * assms
    by (transfer, transfer, auto simp add: Let_def)
  hence "circline_set (mk_line z1 z2) - {\<infinity>\<^sub>h} = of_complex ` circline ?A ?B (Re ?D)"
    using classic_circline[of "mk_line z1 z2" ?A ?B ?C ?D] *
    by simp
  moreover
  have "circline ?A ?B (Re ?D) = line z1 z2"
    using \<open>z1 \<noteq> z2\<close>
    using circline_line'
    by simp
  ultimately
  show ?thesis
    by simp
qed

text \<open>The set of points determined by a circline is always 
either an Euclidean circle or an Euclidean line. \<close>

text \<open>Euclidean circle is determined by its center and radius.\<close>
type_synonym euclidean_circle = "complex \<times> real"

definition euclidean_circle_cmat :: "complex_mat \<Rightarrow> euclidean_circle" where
  [simp]: "euclidean_circle_cmat H = (let (A, B, C, D) = H in (-B/A, sqrt(Re ((B*C - A*D)/(A*A)))))"

lift_definition euclidean_circle_clmat :: "circline_mat \<Rightarrow> euclidean_circle" is euclidean_circle_cmat
  done

lift_definition euclidean_circle :: "circline \<Rightarrow> euclidean_circle" is euclidean_circle_clmat
proof transfer
  fix H1 H2
  assume hh: "hermitean H1 \<and> H1 \<noteq> mat_zero" "hermitean H2 \<and> H2 \<noteq> mat_zero"
  obtain A1 B1 C1 D1 where HH1: "H1 = (A1, B1, C1, D1)"
    by (cases "H1") auto
  obtain A2 B2 C2 D2 where HH2: "H2 = (A2, B2, C2, D2)"
    by (cases "H2") auto
  assume "circline_eq_cmat H1 H2"
  then obtain k where "k \<noteq> 0" and *: "A2 = cor k * A1" "B2 = cor k * B1" "C2 = cor k * C1" "D2 = cor k * D1"
    using HH1 HH2
    by auto
  have "(cor k * B1 * (cor k * C1) - cor k * A1 * (cor k * D1)) = (cor k)\<^sup>2 * (B1*C1 - A1*D1)"
    "(cor k * A1 * (cor k * A1)) = (cor k)\<^sup>2 * (A1*A1)"
    by (auto simp add: field_simps power2_eq_square)
  hence "(cor k * B1 * (cor k * C1) - cor k * A1 * (cor k * D1)) /
         (cor k * A1 * (cor k * A1)) = (B1*C1 - A1*D1) / (A1*A1)"
    using \<open>k \<noteq> 0\<close>
    by (simp add: power2_eq_square)
  thus "euclidean_circle_cmat H1 = euclidean_circle_cmat H2"
    using HH1 HH2 * hh
    by auto
qed

lemma classic_circle:
  assumes "is_circle H" and "(a, r) = euclidean_circle H" and "circline_type H \<le> 0"
  shows "circline_set H = of_complex ` circle a r"
proof-
  obtain A B C D where *: "H = mk_circline A B C D" "hermitean (A, B, C, D)" "(A, B, C, D) \<noteq> mat_zero"
    using ex_mk_circline[of H]
    by auto
  have "is_real A" "is_real D" "C = cnj B"
    using * hermitean_elems
    by auto
  have "Re (A*D - B*C) \<le> 0"
    using \<open>circline_type H \<le> 0\<close> *
    by simp

  hence **: "Re A * Re D \<le> (cmod B)\<^sup>2"
    using \<open>is_real A\<close> \<open>is_real D\<close> \<open>C = cnj B\<close>
    by (simp add: cmod_square)

  have "A \<noteq> 0"
    using \<open>is_circle H\<close> * \<open>is_real A\<close>
    by simp (transfer, transfer, simp)

  hence "Re A \<noteq> 0"
    using \<open>is_real A\<close>
    by (metis complex_surj zero_complex.code)

  have ***: "\<infinity>\<^sub>h \<notin> circline_set H"
    using * inf_in_circline_set[of H] \<open>is_circle H\<close>
    by simp

  let ?a = "-B/A"
  let ?r2 = "((cmod B)\<^sup>2 - Re A * Re D) / (Re A)\<^sup>2"
  let ?r = "sqrt ?r2"

  have "?a = a \<and> ?r = r"
    using \<open>(a, r) = euclidean_circle H\<close>
    using * \<open>is_real A\<close> \<open>is_real D\<close> \<open>C = cnj B\<close> \<open>A \<noteq> 0\<close>
    apply simp
    apply transfer
    apply transfer
    apply simp
    apply (subst Re_divide_real)
    apply (simp_all add: cmod_square, simp add: power2_eq_square)
    done

  show ?thesis
    using * ** *** \<open>Re A \<noteq> 0\<close> \<open>is_real A\<close> \<open>C = cnj B\<close> \<open>?a = a \<and> ?r = r\<close>
    using classic_circline[of H A B C D] assms circline_circle[of "Re A" "Re D" B "circline (Re A) B (Re D)" ?a ?r2 ?r]
    by (simp add: circle_def)
qed

text \<open>Euclidean line is represented by two points.\<close>
type_synonym euclidean_line = "complex \<times> complex"

definition euclidean_line_cmat :: "complex_mat \<Rightarrow> euclidean_line" where
 [simp]: "euclidean_line_cmat H =
         (let (A, B, C, D) = H;
              z1 = -(D*B)/(2*B*C);
              z2 = z1 + \<i> * sgn (if arg B > 0 then -B else B)
           in (z1, z2))"

lift_definition euclidean_line_clmat :: "circline_mat \<Rightarrow> euclidean_line" is euclidean_line_cmat
  done

lift_definition euclidean_line :: "circline \<Rightarrow> complex \<times> complex" is euclidean_line_clmat
proof transfer
  fix H1 H2
  assume hh: "hermitean H1 \<and> H1 \<noteq> mat_zero" "hermitean H2 \<and> H2 \<noteq> mat_zero"
  obtain A1 B1 C1 D1 where HH1: "H1 = (A1, B1, C1, D1)"
    by (cases "H1") auto
  obtain A2 B2 C2 D2 where HH2: "H2 = (A2, B2, C2, D2)"
    by (cases "H2") auto
  assume "circline_eq_cmat H1 H2"
  then obtain k where "k \<noteq> 0" and *: "A2 = cor k * A1" "B2 = cor k * B1" "C2 = cor k * C1" "D2 = cor k * D1"
    using HH1 HH2
    by auto
  have 1: "B1 \<noteq> 0 \<and> 0 < arg B1 \<longrightarrow> \<not> 0 < arg (- B1)"
    using canon_ang_plus_pi1[of "arg B1"] arg_bounded[of B1]
    by (auto simp add: arg_uminus)
  have 2: "B1 \<noteq> 0 \<and> \<not> 0 < arg B1 \<longrightarrow> 0 < arg (- B1)"
    using canon_ang_plus_pi2[of "arg B1"] arg_bounded[of B1]
    by (auto simp add: arg_uminus)

  show "euclidean_line_cmat H1 = euclidean_line_cmat H2"
    using HH1 HH2 * \<open>k \<noteq> 0\<close>
    by (cases "k > 0") (auto simp add: Let_def, simp_all add: sgn_eq 1 2)
qed

lemma classic_line:
  assumes "is_line H" and "circline_type H < 0" and "(z1, z2) = euclidean_line H"
  shows "circline_set H - {\<infinity>\<^sub>h} = of_complex ` line z1 z2"
proof-
  obtain A B C D where *: "H = mk_circline A B C D" "hermitean (A, B, C, D)" "(A, B, C, D) \<noteq> mat_zero"
    using ex_mk_circline[of H]
    by auto
  have "is_real A" "is_real D" "C = cnj B"
    using * hermitean_elems
    by auto
  have "Re A = 0"
    using \<open>is_line H\<close> * \<open>is_real A\<close> \<open>is_real D\<close> \<open>C = cnj B\<close>
    by simp (transfer, transfer, simp)
  have "B \<noteq> 0"
    using \<open>Re A = 0\<close>  \<open>is_real A\<close> \<open>is_real D\<close> \<open>C = cnj B\<close> * \<open>circline_type H < 0\<close>
    using circline_type_mk_circline[of A B C D]
    by auto

  let ?z1 = "- cor (Re D) * B / (2 * B * cnj B)"
  let ?z2 = "?z1 + \<i> * sgn (if 0 < arg B then - B else B)"
  have "z1 = ?z1 \<and> z2 = ?z2"
    using \<open>(z1, z2) = euclidean_line H\<close> * \<open>is_real A\<close> \<open>is_real D\<close> \<open>C = cnj B\<close>
    by simp (transfer, transfer, simp add: Let_def)
  thus ?thesis
    using *
    using classic_circline[of H A B C D] circline_line[of "Re A" B "circline (Re A) B (Re D)" "Re D" ?z1 ?z2] \<open>Re A = 0\<close> \<open>B \<noteq> 0\<close>
    by simp
qed


(* ----------------------------------------------------------------- *)
subsection \<open>Some special circlines\<close>
(* ----------------------------------------------------------------- *)

(* ---------------------------------------------------------------------------- *)
subsubsection \<open>Unit circle\<close>
(* ---------------------------------------------------------------------------- *)

definition unit_circle_cmat :: complex_mat where
  [simp]: "unit_circle_cmat =  (1, 0, 0, -1)"
lift_definition unit_circle_clmat :: circline_mat is unit_circle_cmat
  by (simp add: hermitean_def mat_adj_def mat_cnj_def)
lift_definition unit_circle :: circline is unit_circle_clmat
  done

lemma on_circline_cmat_cvec_unit:
  shows "on_circline_cmat_cvec unit_circle_cmat (z1, z2) \<longleftrightarrow> 
         z1 * cnj z1 = z2 * cnj z2"
  by (simp add: vec_cnj_def field_simps)

lemma
  one_on_unit_circle [simp]: "on_circline unit_circle 1\<^sub>h"  and
  ii_on_unit_circle [simp]: "on_circline unit_circle ii\<^sub>h" and
  not_zero_on_unit_circle [simp]: "\<not> on_circline unit_circle 0\<^sub>h"
  by (transfer, transfer, simp add: vec_cnj_def)+

lemma  
  one_in_unit_circle_set [simp]: "1\<^sub>h \<in> circline_set unit_circle" and
  ii_in_unit_circle_set [simp]: "ii\<^sub>h \<in> circline_set unit_circle" and
  zero_in_unit_circle_set [simp]: "0\<^sub>h \<notin> circline_set unit_circle"
  unfolding circline_set_def
  by simp_all

lemma is_circle_unit_circle [simp]:
  shows "is_circle unit_circle"
  by (transfer, transfer, simp)

lemma not_inf_on_unit_circle' [simp]:
  shows "\<not> on_circline unit_circle \<infinity>\<^sub>h"
  using is_circle_unit_circle inf_on_circline
  by blast

lemma not_inf_on_unit_circle'' [simp]:
  shows "\<infinity>\<^sub>h \<notin> circline_set unit_circle"
  by (simp add: inf_in_circline_set)

lemma euclidean_circle_unit_circle [simp]:
  shows "euclidean_circle unit_circle = (0, 1)"
  by (transfer, transfer, simp)

lemma circline_type_unit_circle [simp]:
  shows "circline_type unit_circle = -1"
  by (transfer, transfer, simp)

lemma on_circline_unit_circle [simp]:
  shows "on_circline unit_circle (of_complex z) \<longleftrightarrow> cmod z = 1"
  by (transfer, transfer, simp add: vec_cnj_def mult.commute)

lemma circline_set_unit_circle [simp]:
  shows "circline_set unit_circle = of_complex ` {z. cmod z = 1}"
proof-
  show ?thesis
  proof safe
    fix x
    assume "x \<in> circline_set unit_circle"
    then obtain x' where "x = of_complex x'"
      using inf_or_of_complex[of x]
      by auto
    thus "x \<in> of_complex ` {z. cmod z = 1}"
      using \<open>x \<in> circline_set unit_circle\<close>
      unfolding circline_set_def              
      by auto
  next
    fix x
    assume "cmod x = 1"
    thus "of_complex x \<in> circline_set unit_circle"
      unfolding circline_set_def
      by auto
  qed
qed

lemma circline_set_unit_circle_I [simp]:
  assumes "cmod z = 1"
  shows "of_complex z \<in> circline_set unit_circle"
  using assms
  unfolding circline_set_unit_circle
  by simp

lemma inversion_unit_circle [simp]:
  assumes "on_circline unit_circle x"
  shows "inversion x = x"
proof-
  obtain x' where "x = of_complex x'" "x' \<noteq> 0"
    using inf_or_of_complex[of x]
    using assms
    by force
  moreover
  hence "x' * cnj x' = 1"
    using assms
    using circline_set_unit_circle
    unfolding circline_set_def
    by auto
  hence "1 / cnj x' = x'"
    using \<open>x' \<noteq> 0\<close>
    by (simp add: field_simps)
  ultimately
  show ?thesis
    using assms
    unfolding inversion_def
    by simp
qed

lemma inversion_id_iff_on_unit_circle: 
  shows "inversion a = a \<longleftrightarrow> on_circline unit_circle a"
  using inversion_id_iff[of a] inf_or_of_complex[of a]
  by auto

lemma on_unit_circle_conjugate [simp]:
  shows "on_circline unit_circle (conjugate z) \<longleftrightarrow> on_circline unit_circle z"
  by (transfer, transfer, auto simp add: vec_cnj_def field_simps)

lemma conjugate_unit_circle_set [simp]:
  shows "conjugate ` (circline_set unit_circle) = circline_set unit_circle"
  unfolding circline_set_def
  by (auto simp add: image_iff, rule_tac x="conjugate x" in exI, simp)

(* ---------------------------------------------------------------------------- *)
subsubsection \<open>x-axis\<close>
(* ---------------------------------------------------------------------------- *)

definition x_axis_cmat :: complex_mat where
  [simp]: "x_axis_cmat =  (0, \<i>, -\<i>, 0)"
lift_definition x_axis_clmat :: circline_mat is x_axis_cmat
  by (simp add: hermitean_def mat_adj_def mat_cnj_def)
lift_definition x_axis :: circline is x_axis_clmat
  done

lemma special_points_on_x_axis' [simp]:
  shows "on_circline x_axis 0\<^sub>h" and "on_circline x_axis 1\<^sub>h" and "on_circline x_axis \<infinity>\<^sub>h"
  by (transfer, transfer, simp add: vec_cnj_def)+

lemma special_points_on_x_axis'' [simp]:
  shows "0\<^sub>h \<in> circline_set x_axis" and "1\<^sub>h \<in> circline_set x_axis" and "\<infinity>\<^sub>h \<in> circline_set x_axis"
  unfolding circline_set_def
  by auto

lemma is_line_x_axis [simp]:
  shows "is_line x_axis"
  by (transfer, transfer, simp)

lemma circline_type_x_axis [simp]:
  shows "circline_type x_axis = -1"
  by (transfer, transfer, simp)

lemma on_circline_x_axis:
  shows "on_circline x_axis z \<longleftrightarrow> (\<exists> c. is_real c \<and> z = of_complex c) \<or> z = \<infinity>\<^sub>h"
proof safe
  fix z c
  assume "is_real c"
  thus "on_circline x_axis (of_complex c)"
  proof (transfer, transfer)
    fix c
    assume "is_real c"
    thus "on_circline_cmat_cvec x_axis_cmat (of_complex_cvec c)"
      using eq_cnj_iff_real[of c]
      by (simp add: vec_cnj_def)
  qed
next
  fix z
  assume "on_circline x_axis z" "z \<noteq> \<infinity>\<^sub>h"
  thus "\<exists>c. is_real c \<and> z = of_complex c"
  proof (transfer, transfer, safe)
    fix a b
    assume "(a, b) \<noteq> vec_zero"
      "on_circline_cmat_cvec x_axis_cmat (a, b)"
      "\<not> (a, b) \<approx>\<^sub>v \<infinity>\<^sub>v"
    hence "b \<noteq> 0" "cnj a * b = cnj b * a" using inf_cvec_z2_zero_iff
      by (auto simp add: vec_cnj_def)
    thus "\<exists>c. is_real c \<and> (a, b) \<approx>\<^sub>v of_complex_cvec c"
      apply (rule_tac x="a/b" in exI)
      apply (auto simp add: is_real_div field_simps)
      apply (rule_tac x="1/b" in exI, simp)
      done
  qed
next
  show "on_circline x_axis \<infinity>\<^sub>h"
    by auto
qed

lemma on_circline_x_axis_I [simp]:
  assumes "is_real z"
  shows "on_circline x_axis (of_complex z)"
  using assms
  unfolding on_circline_x_axis
  by auto

lemma circline_set_x_axis:
  shows "circline_set x_axis = of_complex ` {x. is_real x} \<union> {\<infinity>\<^sub>h}"
  using on_circline_x_axis
  unfolding circline_set_def
  by auto

lemma circline_set_x_axis_I:
  assumes "is_real z"
  shows "of_complex z \<in> circline_set x_axis"
  using assms
  unfolding circline_set_x_axis
  by auto

lemma circline_equation_x_axis:
  shows "of_complex z \<in> circline_set x_axis \<longleftrightarrow> z = cnj z"
  unfolding circline_set_x_axis
proof auto
  fix x
  assume "of_complex z = of_complex x" "is_real x"
  hence "z = x"
    using of_complex_inj[of z x]
    by simp
  thus "z = cnj z"
    using eq_cnj_iff_real[of z] \<open>is_real x\<close>
    by auto
next
  assume "z = cnj z"
  thus "of_complex z \<in> of_complex ` {x. is_real x} "
    using eq_cnj_iff_real[of z]
    by auto
qed

text \<open>Positive and negative part of x-axis\<close>

definition positive_x_axis where
  "positive_x_axis = {z. z \<in> circline_set x_axis \<and> z \<noteq> \<infinity>\<^sub>h \<and> Re (to_complex z) > 0}"

definition negative_x_axis where
  "negative_x_axis = {z. z \<in> circline_set x_axis \<and> z \<noteq> \<infinity>\<^sub>h \<and> Re (to_complex z) < 0}"

lemma circline_set_positive_x_axis_I [simp]:
  assumes "is_real z" and "Re z > 0"
  shows "of_complex z \<in> positive_x_axis"
  using assms
  unfolding positive_x_axis_def
  by simp

lemma circline_set_negative_x_axis_I [simp]:
  assumes "is_real z" and "Re z < 0"
  shows "of_complex z \<in> negative_x_axis"
  using assms
  unfolding negative_x_axis_def
  by simp

(* ---------------------------------------------------------------------------- *)
subsubsection \<open>y-axis\<close>
(* ---------------------------------------------------------------------------- *)

definition y_axis_cmat :: complex_mat where
  [simp]: "y_axis_cmat = (0, 1, 1, 0)"
lift_definition y_axis_clmat :: circline_mat is y_axis_cmat
  by (simp add: hermitean_def mat_adj_def mat_cnj_def)
lift_definition y_axis :: circline is y_axis_clmat
  done

lemma special_points_on_y_axis' [simp]:
  shows "on_circline y_axis 0\<^sub>h" and "on_circline y_axis ii\<^sub>h" and "on_circline y_axis \<infinity>\<^sub>h"
  by (transfer, transfer, simp add: vec_cnj_def)+

lemma special_points_on_y_axis'' [simp]:
  shows "0\<^sub>h \<in> circline_set y_axis" and "ii\<^sub>h \<in> circline_set y_axis" and "\<infinity>\<^sub>h \<in> circline_set y_axis"
  unfolding circline_set_def
  by auto

lemma on_circline_y_axis: 
  shows "on_circline y_axis z \<longleftrightarrow> (\<exists> c. is_imag c \<and> z = of_complex c) \<or> z = \<infinity>\<^sub>h"
proof safe
  fix z c
  assume "is_imag c"
  thus "on_circline y_axis (of_complex c)"                                 
  proof (transfer, transfer)
    fix c                                                       
    assume "is_imag c"
    thus "on_circline_cmat_cvec y_axis_cmat (of_complex_cvec c)"
      using eq_minus_cnj_iff_imag[of c]
      by (simp add: vec_cnj_def)
  qed
next
  fix z
  assume "on_circline y_axis z" "z \<noteq> \<infinity>\<^sub>h"
  thus "\<exists>c. is_imag c \<and> z = of_complex c"
  proof (transfer, transfer, safe)
    fix a b
    assume "(a, b) \<noteq> vec_zero"
      "on_circline_cmat_cvec y_axis_cmat (a, b)"
      "\<not> (a, b) \<approx>\<^sub>v \<infinity>\<^sub>v"
    hence "b \<noteq> 0" "cnj a * b + cnj b * a = 0"
      using inf_cvec_z2_zero_iff
      by (blast, smt add.left_neutral add_cancel_right_right mult.commute mult.left_neutral mult_not_zero on_circline_cmat_cvec_circline_equation y_axis_cmat_def)
    thus "\<exists>c. is_imag c \<and> (a, b) \<approx>\<^sub>v of_complex_cvec c"
      using eq_minus_cnj_iff_imag[of "a / b"]
      apply (rule_tac x="a/b" in exI)
      apply (auto simp add: field_simps)
      apply (rule_tac x="1/b" in exI, simp)
      using add_eq_0_iff apply blast
      apply (rule_tac x="1/b" in exI, simp)
      done
  qed
next
  show "on_circline y_axis \<infinity>\<^sub>h"
    by simp
qed

lemma on_circline_y_axis_I [simp]:
  assumes "is_imag z"
  shows "on_circline y_axis (of_complex z)"
  using assms
  unfolding on_circline_y_axis
  by auto

lemma circline_set_y_axis:
  shows "circline_set y_axis = of_complex ` {x. is_imag x} \<union> {\<infinity>\<^sub>h}"
  using on_circline_y_axis
  unfolding circline_set_def
  by auto

lemma circline_set_y_axis_I:
  assumes "is_imag z"
  shows "of_complex z \<in> circline_set y_axis"
  using assms
  unfolding circline_set_y_axis
  by auto

text \<open>Positive and negative part of y-axis\<close>

definition positive_y_axis where
  "positive_y_axis = {z. z \<in> circline_set y_axis \<and> z \<noteq> \<infinity>\<^sub>h \<and> Im (to_complex z) > 0}"

definition negative_y_axis where
  "negative_y_axis = {z. z \<in> circline_set y_axis \<and> z \<noteq> \<infinity>\<^sub>h \<and> Im (to_complex z) < 0}"

lemma circline_set_positive_y_axis_I [simp]:
  assumes "is_imag z" and "Im z > 0"
  shows "of_complex z \<in> positive_y_axis"
  using assms
  unfolding positive_y_axis_def
  by simp

lemma circline_set_negative_y_axis_I [simp]:
  assumes "is_imag z" and "Im z < 0"
  shows "of_complex z \<in> negative_y_axis"
  using assms
  unfolding negative_y_axis_def
  by simp

(* ---------------------------------------------------------------------------- *)
subsubsection \<open>Point zero as a circline\<close>
(* ---------------------------------------------------------------------------- *)

definition circline_point_0_cmat :: complex_mat where
  [simp]: "circline_point_0_cmat =  (1, 0, 0, 0)"
lift_definition circline_point_0_clmat :: circline_mat is circline_point_0_cmat
  by (simp add: hermitean_def mat_adj_def mat_cnj_def)
lift_definition circline_point_0 :: circline is circline_point_0_clmat
  done

lemma circline_type_circline_point_0 [simp]:
  shows "circline_type circline_point_0 = 0"
  by (transfer, transfer, simp)

lemma zero_in_circline_point_0 [simp]:
  shows "0\<^sub>h \<in> circline_set circline_point_0"
  unfolding circline_set_def
  by auto (transfer, transfer, simp add: vec_cnj_def)+

(* ---------------------------------------------------------------------------- *)
subsubsection \<open>Imaginary unit circle\<close>
(* ---------------------------------------------------------------------------- *)

definition imag_unit_circle_cmat :: complex_mat where
  [simp]: "imag_unit_circle_cmat =  (1, 0, 0, 1)"
lift_definition imag_unit_circle_clmat :: circline_mat is imag_unit_circle_cmat
  by (simp add: hermitean_def mat_adj_def mat_cnj_def)
lift_definition imag_unit_circle :: circline is imag_unit_circle_clmat
  done

lemma circline_type_imag_unit_circle [simp]:
  shows "circline_type imag_unit_circle = 1"
  by (transfer, transfer, simp)

(* ----------------------------------------------------------------- *)
subsection \<open>Intersection of circlines\<close>
(* ----------------------------------------------------------------- *)

definition circline_intersection :: "circline \<Rightarrow> circline \<Rightarrow> complex_homo set" where
  "circline_intersection H1 H2 = {z. on_circline H1 z \<and> on_circline H2 z}"

lemma circline_equation_cancel_z2:
  assumes "circline_equation A B C D z1 z2 " and "z2 \<noteq> 0"
  shows "circline_equation A B C D (z1/z2) 1"
  using assms
  by (simp add: field_simps)

lemma circline_equation_quadratic_equation:
  assumes "circline_equation A B (cnj B) D z 1" and 
          "Re z = x" and "Im z = y" and "Re B = bx" and "Im B = by"
  shows "A*x\<^sup>2 + A*y\<^sup>2 + 2*bx*x + 2*by*y + D = 0"
  using assms
proof-
  have "z = x + \<i>*y" "B = bx + \<i>*by"
    using assms complex_eq
    by auto
  thus ?thesis
    using assms
    by (simp add: field_simps power2_eq_square)
qed

lemma circline_intersection_symetry:
  shows "circline_intersection H1 H2 = circline_intersection H2 H1"
  unfolding circline_intersection_def
  by auto

(* ----------------------------------------------------------------- *)
subsection \<open>Möbius action on circlines\<close>
(* ----------------------------------------------------------------- *)

definition moebius_circline_cmat_cmat :: "complex_mat \<Rightarrow> complex_mat \<Rightarrow> complex_mat" where
  [simp]: "moebius_circline_cmat_cmat M H = congruence (mat_inv M) H"

lift_definition moebius_circline_mmat_clmat :: "moebius_mat \<Rightarrow> circline_mat \<Rightarrow> circline_mat" is moebius_circline_cmat_cmat
  using mat_det_inv congruence_nonzero hermitean_congruence
  by simp

lift_definition moebius_circline :: "moebius \<Rightarrow> circline \<Rightarrow> circline" is moebius_circline_mmat_clmat
proof transfer
  fix M M' H H'
  assume "moebius_cmat_eq M M'" "circline_eq_cmat H H'"
  thus "circline_eq_cmat (moebius_circline_cmat_cmat M H) (moebius_circline_cmat_cmat M' H')"
    by (auto simp add: mat_inv_mult_sm) (rule_tac x="ka / Re (k * cnj k)" in exI, auto simp add: complex_mult_cnj_cmod power2_eq_square)
qed

lemma moebius_preserve_circline_type [simp]:                                
  shows "circline_type (moebius_circline M H) = circline_type H"
proof (transfer, transfer)
  fix M H :: complex_mat
  assume "mat_det M \<noteq> 0" "hermitean H \<and> H \<noteq> mat_zero"
  thus "circline_type_cmat (moebius_circline_cmat_cmat M H) = circline_type_cmat H"
    using Re_det_sgn_congruence[of "mat_inv M" "H"] mat_det_inv[of "M"]
    by (simp del: congruence_def)
qed

text \<open>The central lemma in this section connects the action of Möbius transformations on points and
on circlines.\<close>

lemma moebius_circline:
  shows "{z. on_circline (moebius_circline M H) z} =
         moebius_pt M ` {z. on_circline H z}"
proof safe
  fix z
  assume "on_circline H z"
  thus "on_circline (moebius_circline M H) (moebius_pt M z)"
  proof (transfer, transfer)
    fix z :: complex_vec and M H :: complex_mat
    assume hh: "hermitean H \<and> H \<noteq> mat_zero" "z \<noteq> vec_zero" "mat_det M \<noteq> 0"
    let ?z = "M *\<^sub>m\<^sub>v z"
    let ?H = "mat_adj (mat_inv M) *\<^sub>m\<^sub>m H *\<^sub>m\<^sub>m (mat_inv M)"
    assume *: "on_circline_cmat_cvec H z"
    hence "quad_form z H = 0"
      by simp
    hence "quad_form ?z ?H = 0"
      using quad_form_congruence[of M z H] hh
      by simp
    thus "on_circline_cmat_cvec (moebius_circline_cmat_cmat M H) (moebius_pt_cmat_cvec M z)"
      by simp
  qed
next
  fix z
  assume "on_circline (moebius_circline M H) z"
  hence "\<exists> z'. z = moebius_pt M z' \<and> on_circline H z'"
  proof (transfer, transfer)
    fix z :: complex_vec and M H :: complex_mat
    assume hh: "hermitean H \<and> H \<noteq> mat_zero" "z \<noteq> vec_zero" "mat_det M \<noteq> 0"
    let ?iM = "mat_inv M"
    let ?z' = "?iM *\<^sub>m\<^sub>v z"
    assume *: "on_circline_cmat_cvec (moebius_circline_cmat_cmat M H) z"
    have "?z' \<noteq> vec_zero"
      using hh
      using mat_det_inv mult_mv_nonzero
      by auto
    moreover
    have "z \<approx>\<^sub>v moebius_pt_cmat_cvec M ?z'"
      using hh eye_mv_l mat_inv_r
      by simp
    moreover
    have "M *\<^sub>m\<^sub>v (?iM *\<^sub>m\<^sub>v z) = z"
      using hh eye_mv_l mat_inv_r
      by auto
    hence "on_circline_cmat_cvec H ?z'"
      using hh *
      using quad_form_congruence[of M "?iM *\<^sub>m\<^sub>v z" H, symmetric]
      unfolding moebius_circline_cmat_cmat_def
      unfolding on_circline_cmat_cvec_def
      by simp
    ultimately
    show "\<exists>z'\<in>{v. v \<noteq> vec_zero}. z \<approx>\<^sub>v moebius_pt_cmat_cvec M z' \<and> on_circline_cmat_cvec H z'"
      by blast
  qed
  thus "z \<in> moebius_pt M ` {z. on_circline H z}"
    by auto
qed

lemma on_circline_moebius_circline_I [simp]:
  assumes "on_circline H z"
  shows "on_circline (moebius_circline M H) (moebius_pt M z)"
  using assms moebius_circline
  by fastforce

lemma circline_set_moebius_circline [simp]:
  shows "circline_set (moebius_circline M H) = moebius_pt M ` circline_set H"
  using moebius_circline[of M H]
  unfolding circline_set_def
  by auto

lemma circline_set_moebius_circline_I [simp]:
  assumes "z \<in> circline_set H"
  shows "moebius_pt M z \<in> circline_set (moebius_circline M H)"
  using assms
  by simp

lemma circline_set_moebius_circline_E:
  assumes "moebius_pt M z \<in> circline_set (moebius_circline M H)"
  shows "z \<in> circline_set H"
  using assms
  using moebius_pt_eq_I[of M z]
  by auto

lemma circline_set_moebius_circline_iff [simp]:
  shows "moebius_pt M z \<in> circline_set (moebius_circline M H) \<longleftrightarrow> 
         z \<in> circline_set H"
  using moebius_pt_eq_I[of M z]
  by auto

lemma inj_moebius_circline:
  shows "inj (moebius_circline M)"
unfolding inj_on_def
proof (safe)
  fix H H'
  assume "moebius_circline M H = moebius_circline M H'"
  thus "H = H'"
  proof (transfer, transfer)
    fix M H H' :: complex_mat
    assume hh: "mat_det M \<noteq> 0"
    let ?iM = "mat_inv M"
    assume "circline_eq_cmat (moebius_circline_cmat_cmat M H) (moebius_circline_cmat_cmat M H')"
    then obtain k where "congruence ?iM H' = congruence ?iM (cor k *\<^sub>s\<^sub>m H)" "k \<noteq> 0"
      by auto
    thus "circline_eq_cmat H H'"
      using hh inj_congruence[of ?iM H' "cor k *\<^sub>s\<^sub>m H"] mat_det_inv[of M]
      by auto
  qed
qed

lemma moebius_circline_eq_I:
  assumes "moebius_circline M H1 = moebius_circline M H2"
  shows "H1 = H2"
  using assms inj_moebius_circline[of M]
  unfolding inj_on_def
  by blast

lemma moebius_circline_neq_I [simp]:
  assumes "H1 \<noteq> H2"
  shows "moebius_circline M H1 \<noteq> moebius_circline M H2"
  using assms inj_moebius_circline[of M]
  unfolding inj_on_def
  by blast

(* ---------------------------------------------------------------------------- *)
subsubsection \<open>Group properties of Möbius action on ciclines\<close>
(* ---------------------------------------------------------------------------- *)

text \<open>Möbius actions on circlines have similar properties as Möbius actions on points.\<close>

lemma moebius_circline_id [simp]:
  shows "moebius_circline id_moebius H = H"
  by (transfer, transfer) (simp add: mat_adj_def mat_cnj_def, rule_tac x=1 in exI, auto)

lemma moebius_circline_comp [simp]:
  shows "moebius_circline (moebius_comp M1 M2) H = moebius_circline M1 (moebius_circline M2 H)"
  by (transfer, transfer) (simp add: mat_inv_mult_mm, rule_tac x=1 in exI, simp add: mult_mm_assoc)

lemma moebius_circline_comp_inv_left [simp]:
  shows "moebius_circline (moebius_inv M) (moebius_circline M H) = H"
  by (subst moebius_circline_comp[symmetric], simp)

lemma moebius_circline_comp_inv_right [simp]:
  shows "moebius_circline M (moebius_circline (moebius_inv M) H) = H"
  by (subst moebius_circline_comp[symmetric], simp)

(* ----------------------------------------------------------------- *)
subsection \<open>Action of Euclidean similarities on circlines\<close>
(* ----------------------------------------------------------------- *)

lemma moebius_similarity_lines_to_lines [simp]:
  assumes "a \<noteq> 0"
  shows "\<infinity>\<^sub>h \<in> circline_set (moebius_circline (moebius_similarity a b) H) \<longleftrightarrow> 
         \<infinity>\<^sub>h \<in> circline_set H"
  using assms       
  by (metis circline_set_moebius_circline_iff moebius_similarity_inf)

lemma moebius_similarity_lines_to_lines':
  assumes "a \<noteq> 0"
  shows "on_circline (moebius_circline (moebius_similarity a b) H) \<infinity>\<^sub>h \<longleftrightarrow>
         \<infinity>\<^sub>h \<in> circline_set H"
  using moebius_similarity_lines_to_lines assms
  unfolding circline_set_def
  by simp

(* ----------------------------------------------------------------- *)
subsection \<open>Conjugation, recpiprocation and inversion of circlines\<close>
(* ----------------------------------------------------------------- *)

text \<open>Conjugation of circlines\<close>
definition conjugate_circline_cmat :: "complex_mat \<Rightarrow> complex_mat" where
 [simp]: "conjugate_circline_cmat = mat_cnj"
lift_definition conjugate_circline_clmat :: "circline_mat \<Rightarrow> circline_mat" is conjugate_circline_cmat
  by (auto simp add: hermitean_def mat_adj_def mat_cnj_def)
lift_definition conjugate_circline :: "circline \<Rightarrow> circline" is conjugate_circline_clmat
  by transfer (metis circline_eq_cmat_def conjugate_circline_cmat_def hermitean_transpose mat_t_mult_sm)

lemma conjugate_circline_set':
  shows "conjugate ` circline_set H \<subseteq> circline_set (conjugate_circline H)"
proof (safe)
  fix z
  assume "z \<in> circline_set H"
  thus "conjugate z \<in> circline_set (conjugate_circline H)"
    unfolding circline_set_def
    apply simp
    apply (transfer, transfer)
    unfolding on_circline_cmat_cvec_def conjugate_cvec_def conjugate_circline_cmat_def
    apply (subst quad_form_vec_cnj_mat_cnj, simp_all)
    done
qed

lemma conjugate_conjugate_circline [simp]:
  shows "conjugate_circline (conjugate_circline H) = H"
  by (transfer, transfer, force)

lemma circline_set_conjugate_circline [simp]:
  shows "circline_set (conjugate_circline H) = conjugate ` circline_set H" (is "?lhs = ?rhs")
proof (safe)
  fix z
  assume "z \<in> ?lhs"
  show "z \<in> ?rhs"
  proof
    show "z = conjugate (conjugate z)"
      by simp
  next
    show "conjugate z \<in> circline_set H"
      using \<open>z \<in> circline_set (conjugate_circline H)\<close>
      using conjugate_circline_set'[of "conjugate_circline H"]
      by auto
  qed
next
  fix z
  assume "z \<in> circline_set H"
  thus "conjugate z \<in> circline_set (conjugate_circline H)"
    using conjugate_circline_set'[of H]
    by auto
qed

lemma on_circline_conjugate_circline [simp]: 
  shows "on_circline (conjugate_circline H) z \<longleftrightarrow> on_circline H (conjugate z)"
  using circline_set_conjugate_circline[of H]
  unfolding circline_set_def
  by force

text \<open>Inversion of circlines\<close>

definition circline_inversion_cmat :: "complex_mat \<Rightarrow> complex_mat" where
  [simp]:  "circline_inversion_cmat H = (let (A, B, C, D) = H in (D, B, C, A))"
lift_definition circline_inversion_clmat :: "circline_mat \<Rightarrow> circline_mat" is circline_inversion_cmat
  by (auto simp add: hermitean_def mat_adj_def mat_cnj_def)
lift_definition circline_inversion :: "circline \<Rightarrow> circline" is circline_inversion_clmat
  by transfer auto

lemma on_circline_circline_inversion [simp]:
  shows "on_circline (circline_inversion H) z \<longleftrightarrow> on_circline H (reciprocal (conjugate z))"
  by (transfer, transfer, auto simp add: vec_cnj_def field_simps)

lemma circline_set_circline_inversion [simp]:
  shows "circline_set (circline_inversion H) = inversion ` circline_set H"
  unfolding circline_set_def inversion_def
  by (force simp add: comp_def image_iff)

text \<open>Reciprocal of circlines\<close>

definition circline_reciprocal :: "circline \<Rightarrow> circline" where
  "circline_reciprocal = conjugate_circline \<circ> circline_inversion"

lemma circline_set_circline_reciprocal:
  shows "circline_set (circline_reciprocal H) = reciprocal ` circline_set H"
  unfolding circline_reciprocal_def comp_def
  by (auto simp add: inversion_def image_iff)

text \<open>Rotation of circlines\<close>

lemma rotation_pi_2_y_axis [simp]:
  shows "moebius_circline (moebius_rotation (pi/2)) y_axis = x_axis"
  unfolding moebius_rotation_def moebius_similarity_def
  by (transfer, transfer, simp add: mat_adj_def mat_cnj_def)

lemma rotation_minus_pi_2_y_axis [simp]:
  shows "moebius_circline (moebius_rotation (-pi/2)) y_axis = x_axis"
  unfolding moebius_rotation_def moebius_similarity_def
  by (transfer, transfer, simp add: mat_adj_def mat_cnj_def, rule_tac x="-1" in exI, simp)

lemma rotation_minus_pi_2_x_axis [simp]:
  shows "moebius_circline (moebius_rotation (-pi/2)) x_axis = y_axis"
  unfolding moebius_rotation_def moebius_similarity_def
  by (transfer, transfer, simp add: mat_adj_def mat_cnj_def)

lemma rotation_pi_2_x_axis [simp]:
  shows "moebius_circline (moebius_rotation (pi/2)) x_axis = y_axis"
  unfolding moebius_rotation_def moebius_similarity_def
  by (transfer, transfer, simp add: mat_adj_def mat_cnj_def, rule_tac x="-1" in exI, simp)

lemma rotation_minus_pi_2_positive_y_axis [simp]:
  shows "(moebius_pt (moebius_rotation (-pi/2))) ` positive_y_axis = positive_x_axis"
proof safe
  fix y
  assume y: "y \<in> positive_y_axis"
  have *: "Re (a * \<i> / b) < 0 \<longleftrightarrow> Im (a / b) > 0" for a b
    by (subst times_divide_eq_left [symmetric], subst mult.commute, subst Re_i_times) auto
  from y * show "moebius_pt (moebius_rotation (-pi/2)) y \<in> positive_x_axis"
    unfolding positive_y_axis_def positive_x_axis_def circline_set_def
    unfolding moebius_rotation_def moebius_similarity_def
    apply simp
    apply transfer
    apply transfer
    apply (auto simp add: vec_cnj_def field_simps add_eq_0_iff)
    done
next
  fix x
  assume x: "x \<in> positive_x_axis"
  let ?y = "moebius_pt (moebius_rotation (pi/2)) x"
  have *: "Im (a * \<i> / b) > 0 \<longleftrightarrow> Re (a / b) > 0" for a b
    by (subst times_divide_eq_left [symmetric], subst mult.commute, subst Im_i_times) auto
  hence "?y \<in> positive_y_axis"
    using \<open>x \<in> positive_x_axis\<close>
    unfolding positive_x_axis_def positive_y_axis_def
    unfolding moebius_rotation_def moebius_similarity_def
    unfolding circline_set_def
    apply simp
    apply transfer
    apply transfer
    apply (auto simp add: vec_cnj_def field_simps add_eq_0_iff)
    done
  thus "x \<in> moebius_pt (moebius_rotation (-pi/2)) ` positive_y_axis"
    by (auto simp add: image_iff) (rule_tac x="?y" in bexI, simp_all)
qed

(* ----------------------------------------------------------------- *)
subsection \<open>Circline uniqueness\<close>
(* ----------------------------------------------------------------- *)

(* ----------------------------------------------------------------- *)
subsubsection \<open>Zero type circline uniqueness\<close>
(* ----------------------------------------------------------------- *)

lemma unique_circline_type_zero_0':
  shows "(circline_type circline_point_0 = 0 \<and> 0\<^sub>h \<in> circline_set circline_point_0) \<and>
         (\<forall> H. circline_type H = 0 \<and> 0\<^sub>h \<in> circline_set H \<longrightarrow> H = circline_point_0)"
unfolding circline_set_def
proof (safe)
  show "circline_type circline_point_0 = 0"
    by (transfer, transfer, simp)
next
  show "on_circline circline_point_0 0\<^sub>h"
    using circline_set_def zero_in_circline_point_0
    by auto
next
  fix H
  assume "circline_type H = 0" "on_circline H 0\<^sub>h"
  thus "H = circline_point_0"
  proof (transfer, transfer)
    fix H :: complex_mat
    assume hh: "hermitean H \<and> H \<noteq> mat_zero"
    obtain A B C D where HH: "H = (A, B, C, D)"
      by (cases "H") auto
    hence *: "C = cnj B" "is_real A"
      using hh hermitean_elems[of A B C D]
      by auto
    assume "circline_type_cmat H = 0" "on_circline_cmat_cvec H 0\<^sub>v"
    thus "circline_eq_cmat H circline_point_0_cmat"
      using HH hh *
      by (simp add: Let_def vec_cnj_def sgn_minus sgn_mult sgn_zero_iff)
         (rule_tac x="1/Re A" in exI, cases A, cases B, simp add: Complex_eq sgn_zero_iff)
  qed
qed

lemma unique_circline_type_zero_0:
  shows "\<exists>! H. circline_type H = 0 \<and> 0\<^sub>h \<in> circline_set H"
  using unique_circline_type_zero_0'
  by blast

lemma unique_circline_type_zero:
  shows "\<exists>! H. circline_type H = 0 \<and> z \<in> circline_set H"
proof-
  obtain M where ++: "moebius_pt M z = 0\<^sub>h"
    using ex_moebius_1[of z]
    by auto
  have +++: "z = moebius_pt (moebius_inv M) 0\<^sub>h"
    by (subst ++[symmetric]) simp
  then obtain H0 where *: "circline_type H0 = 0 \<and> 0\<^sub>h \<in> circline_set H0" and
    **: "\<forall> H'. circline_type H' = 0 \<and> 0\<^sub>h \<in> circline_set H' \<longrightarrow> H' = H0"
    using unique_circline_type_zero_0
    by auto
  let ?H' = "moebius_circline (moebius_inv M) H0"
  show ?thesis
    unfolding Ex1_def
    using * +++
  proof (rule_tac x="?H'" in exI, simp, safe)
    fix H'
    assume "circline_type H' = 0" "moebius_pt (moebius_inv M) 0\<^sub>h \<in> circline_set H'"
    hence "0\<^sub>h \<in> circline_set (moebius_circline M H')"
      using ++ +++
      by force
    hence "moebius_circline M H' = H0"
      using **[rule_format, of "moebius_circline M H'"]
      using \<open>circline_type H' = 0\<close>
      by simp
    thus "H' = moebius_circline (moebius_inv M) H0"
      by auto
  qed
qed

(* ----------------------------------------------------------------- *)
subsubsection \<open>Negative type circline uniqueness\<close>
(* ----------------------------------------------------------------- *)

lemma unique_circline_01inf':
  shows "0\<^sub>h \<in> circline_set x_axis \<and> 1\<^sub>h \<in> circline_set x_axis \<and> \<infinity>\<^sub>h \<in> circline_set x_axis \<and>
        (\<forall> H. 0\<^sub>h \<in> circline_set H \<and> 1\<^sub>h \<in> circline_set H \<and> \<infinity>\<^sub>h \<in> circline_set H  \<longrightarrow> H = x_axis)"
proof safe
  fix H
  assume "0\<^sub>h \<in> circline_set H"  "1\<^sub>h \<in> circline_set H" "\<infinity>\<^sub>h \<in> circline_set H"
  thus "H = x_axis"
    unfolding circline_set_def
    apply simp
  proof (transfer, transfer)
    fix H
    assume hh: "hermitean H \<and> H \<noteq> mat_zero"
    obtain A B C D where HH: "H = (A, B, C, D)"
      by (cases H) auto
    have *: "C = cnj B" "A = 0 \<and> D = 0 \<longrightarrow> B \<noteq> 0"
      using hermitean_elems[of A B C D] hh HH
      by auto
    obtain Bx By where "B = Complex Bx By"
      by (cases B) auto
    assume "on_circline_cmat_cvec H 0\<^sub>v" "on_circline_cmat_cvec H 1\<^sub>v" "on_circline_cmat_cvec H \<infinity>\<^sub>v"
    thus "circline_eq_cmat H x_axis_cmat"
      using * HH \<open>C = cnj B\<close> \<open>B = Complex Bx By\<close>
      by (simp add: Let_def vec_cnj_def Complex_eq) (rule_tac x="1/By" in exI, auto)
  qed
qed simp_all

lemma unique_circline_set:
  assumes "A \<noteq> B" and "A \<noteq> C" and "B \<noteq> C"
  shows "\<exists>! H. A \<in> circline_set H \<and> B \<in> circline_set H \<and> C \<in> circline_set H"
proof-
  let ?P = "\<lambda> A B C. A \<noteq> B \<and> A \<noteq> C \<and> B \<noteq> C \<longrightarrow> (\<exists>! H. A \<in> circline_set H \<and> B \<in> circline_set H \<and> C \<in> circline_set H)"
  have "?P A B C"
  proof (rule wlog_moebius_01inf[of ?P])
    fix M a b c
    let ?M = "moebius_pt M"
    assume "?P a b c"
    show "?P (?M a) (?M b) (?M c)"
    proof
      assume "?M a \<noteq> ?M b \<and> ?M a \<noteq> ?M c \<and> ?M b \<noteq> ?M c"
      hence "a \<noteq> b" "b \<noteq> c" "a \<noteq> c"
        by auto
      hence "\<exists>!H. a \<in> circline_set H \<and> b \<in> circline_set H \<and> c \<in> circline_set H"
        using \<open>?P a b c\<close>
        by simp
      then obtain H where
        *: "a \<in> circline_set H \<and> b \<in> circline_set H \<and> c \<in> circline_set H" and
        **: "\<forall>H'. a \<in> circline_set H' \<and> b \<in> circline_set H' \<and> c \<in> circline_set H' \<longrightarrow> H' = H"
        unfolding Ex1_def
        by auto
      let ?H' = "moebius_circline M H"
      show "\<exists>! H. ?M a \<in> circline_set H \<and> moebius_pt M b \<in> circline_set H \<and> moebius_pt M c \<in> circline_set H"
        unfolding Ex1_def
      proof (rule_tac x="?H'" in exI, rule)
        show "?M a \<in> circline_set ?H' \<and> ?M b \<in> circline_set ?H' \<and> ?M c \<in> circline_set ?H'"
          using * 
          by auto
      next
        show "\<forall>H'. ?M a \<in> circline_set H' \<and> ?M b \<in> circline_set H' \<and> ?M c \<in> circline_set H' \<longrightarrow> H' = ?H'"
        proof (safe)
          fix H'
          let ?iH' = "moebius_circline (moebius_inv M) H'"
          assume "?M a \<in> circline_set H'" "?M b \<in> circline_set H'" "?M c \<in> circline_set H'"
          hence "a \<in> circline_set ?iH' \<and> b \<in> circline_set ?iH' \<and> c \<in> circline_set ?iH'"
            by simp
          hence "H = ?iH'"
            using **
            by blast
          thus "H' = moebius_circline M H"
            by simp
        qed
      qed
    qed
  next
    show "?P 0\<^sub>h 1\<^sub>h \<infinity>\<^sub>h"
      using unique_circline_01inf'
      unfolding Ex1_def
      by (safe, rule_tac x="x_axis" in exI) auto
  qed fact+
  thus ?thesis
    using assms
    by simp
qed

lemma zero_one_inf_x_axis [simp]:
  assumes "0\<^sub>h \<in> circline_set H" and "1\<^sub>h \<in> circline_set H" and "\<infinity>\<^sub>h \<in> circline_set H"
  shows "H = x_axis"
  using assms unique_circline_set[of "0\<^sub>h" "1\<^sub>h" "\<infinity>\<^sub>h"]
  by auto

(* ----------------------------------------------------------------- *)
subsection \<open>Circline set cardinality\<close>
(* ----------------------------------------------------------------- *)

(* ----------------------------------------------------------------- *)
subsubsection \<open>Diagonal circlines\<close>
(* ----------------------------------------------------------------- *)

definition is_diag_circline_cmat :: "complex_mat \<Rightarrow> bool" where
 [simp]: "is_diag_circline_cmat H = (let (A, B, C, D) = H in B = 0 \<and> C = 0)"
lift_definition is_diag_circline_clmat :: "circline_mat \<Rightarrow> bool" is is_diag_circline_cmat
  done
lift_definition circline_diag :: "circline \<Rightarrow> bool" is is_diag_circline_clmat
  by transfer auto

lemma circline_diagonalize:
  shows "\<exists> M H'. moebius_circline M H = H' \<and> circline_diag H'"
proof (transfer, transfer)
  fix H
  assume hh: "hermitean H \<and> H \<noteq> mat_zero"
  obtain A B C D where HH: "H = (A, B, C, D)"
    by (cases "H") auto
  hence HH_elems: "is_real A" "is_real D" "C = cnj B"
    using hermitean_elems[of A B C D] hh
    by auto
  obtain M k1 k2 where *: "mat_det M \<noteq> 0" "unitary M" "congruence M H = (k1, 0, 0, k2)" "is_real k1" "is_real k2"
    using hermitean_diagonizable[of H] hh
    by auto
  have "k1 \<noteq> 0 \<or> k2 \<noteq> 0"
    using \<open>congruence M H = (k1, 0, 0, k2)\<close> hh congruence_nonzero[of H M] \<open>mat_det M \<noteq> 0\<close>
    by auto
  let ?M' = "mat_inv M"
  let ?H' = "(k1, 0, 0, k2)"
  have "circline_eq_cmat (moebius_circline_cmat_cmat ?M' H) ?H' \<and> is_diag_circline_cmat ?H'"
    using *
    by force
  moreover
  have "?H' \<in> hermitean_nonzero"
    using * \<open>k1 \<noteq> 0 \<or> k2 \<noteq> 0\<close> eq_cnj_iff_real[of k1] eq_cnj_iff_real[of k2]
    by (auto simp add: hermitean_def mat_adj_def mat_cnj_def)
  moreover
  have "mat_det ?M' \<noteq> 0"
    using * mat_det_inv[of M]
    by auto
  ultimately
  show "\<exists>M\<in>{M. mat_det M \<noteq> 0}.
            \<exists>H'\<in>hermitean_nonzero.
               circline_eq_cmat (moebius_circline_cmat_cmat M H) H' \<and> is_diag_circline_cmat H'"
    by blast
qed

lemma wlog_circline_diag:
  assumes "\<And> H. circline_diag H \<Longrightarrow> P H"
          "\<And> M H. P H \<Longrightarrow> P (moebius_circline M H)"
  shows "P H"
proof-
  obtain M H' where "moebius_circline M H = H'" "circline_diag H'"
    using circline_diagonalize[of H]
    by auto
  hence "P (moebius_circline M H)"
    using assms(1)
    by simp
  thus ?thesis
    using assms(2)[of "moebius_circline M H" "moebius_inv M"]
    by simp
qed

(* ----------------------------------------------------------------- *)
subsubsection \<open>Zero type circline set cardinality\<close>
(* ----------------------------------------------------------------- *)

lemma circline_type_zero_card_eq1_0:
  assumes "circline_type H = 0" and "0\<^sub>h \<in> circline_set H"
  shows "circline_set H = {0\<^sub>h}"
using assms
unfolding circline_set_def
proof(safe)
  fix z
  assume "on_circline H z" "circline_type H = 0" "on_circline H 0\<^sub>h"
  hence "H = circline_point_0"
    using unique_circline_type_zero_0'
    unfolding circline_set_def
    by simp
  thus "z = 0\<^sub>h"
    using \<open>on_circline H z\<close>
    by (transfer, transfer) (case_tac z, case_tac H, force simp add: vec_cnj_def)
qed


lemma circline_type_zero_card_eq1:
  assumes "circline_type H = 0"
  shows "\<exists> z. circline_set H = {z}"
proof-
  have "\<exists> z. on_circline H z"
    using assms
  proof (transfer, transfer)
    fix H
    assume hh: "hermitean H \<and> H \<noteq> mat_zero"
    obtain A B C D where HH: "H = (A, B, C, D)"
      by (cases H) auto
    hence "C = cnj B" "is_real A" "is_real D"
      using hh hermitean_elems[of A B C D]
      by auto
    assume "circline_type_cmat H = 0"
    hence "mat_det H = 0"
      by (simp add: complex_eq_if_Re_eq hh mat_det_hermitean_real sgn_eq_0_iff)
    hence "A*D = B*C"
      using HH
      by simp
    show "Bex {v. v \<noteq> vec_zero} (on_circline_cmat_cvec H)"
    proof (cases "A \<noteq> 0 \<or> B \<noteq> 0")
      case True
      thus ?thesis
        using HH \<open>A*D = B*C\<close>
        by (rule_tac x="(-B, A)" in bexI) (auto simp add: Let_def vec_cnj_def field_simps)
    next
      case False
      thus ?thesis
        using HH \<open>C = cnj B\<close>
        by (rule_tac x="(1, 0)" in bexI) (simp_all add: Let_def vec_cnj_def)
    qed
  qed
  then obtain z where "on_circline H z"
    by auto
  obtain M where "moebius_pt M z = 0\<^sub>h"
    using ex_moebius_1[of z]
    by auto
  hence "0\<^sub>h \<in> circline_set (moebius_circline M H)"
    using on_circline_moebius_circline_I[OF \<open>on_circline H z\<close>, of M]
    unfolding circline_set_def
    by simp
  hence "circline_set (moebius_circline M H) = {0\<^sub>h}"
    using circline_type_zero_card_eq1_0[of "moebius_circline M H"] \<open>circline_type H = 0\<close>
    by auto
  hence "circline_set H = {z}"
    using \<open>moebius_pt M z = 0\<^sub>h\<close>
    using bij_moebius_pt[of M] bij_image_singleton[of "moebius_pt M" "circline_set H" _ z]
    by simp
  thus ?thesis
    by auto
qed

(* ----------------------------------------------------------------- *)
subsubsection \<open>Negative type circline set cardinality\<close>
(* ----------------------------------------------------------------- *)

lemma quad_form_diagonal_iff:
  assumes "k1 \<noteq> 0" and "is_real k1" and "is_real k2" and "Re k1 * Re k2 < 0"
  shows "quad_form (z1, 1) (k1, 0, 0, k2) = 0 \<longleftrightarrow> (\<exists> \<phi>. z1 = rcis (sqrt (Re (-k2 /k1))) \<phi>)"
proof-
  have "Re (-k2/k1) \<ge> 0"
    using \<open>Re k1 * Re k2 < 0\<close> \<open>is_real k1\<close> \<open>is_real k2\<close> \<open>k1 \<noteq> 0\<close>
    using Re_divide_real[of k1 "-k2"]
    by (smt divide_less_0_iff mult_nonneg_nonneg mult_nonpos_nonpos uminus_complex.simps(1))

  have "quad_form (z1, 1) (k1, 0, 0, k2) = 0 \<longleftrightarrow> (cor (cmod z1))\<^sup>2 = -k2 / k1"
    using assms add_eq_0_iff[of k2 "k1*(cor (cmod z1))\<^sup>2"]
    using eq_divide_imp[of k1 "(cor (cmod z1))\<^sup>2" "-k2"]
    by (auto simp add: vec_cnj_def field_simps complex_mult_cnj_cmod)
  also have "... \<longleftrightarrow> (cmod z1)\<^sup>2 = Re (-k2 /k1)"
    using assms
    apply (subst complex_eq_if_Re_eq)
    using Re_complex_of_real[of "(cmod z1)\<^sup>2"] div_reals
    by auto
  also have "... \<longleftrightarrow> cmod z1 = sqrt (Re (-k2 /k1))"
    by (metis norm_ge_zero real_sqrt_ge_0_iff real_sqrt_pow2 real_sqrt_power)
  also have "... \<longleftrightarrow> (\<exists> \<phi>. z1 = rcis (sqrt (Re (-k2 /k1))) \<phi>)"
    using rcis_cmod_arg[of z1, symmetric] assms abs_of_nonneg[of "sqrt (Re (-k2/k1))"]
    using \<open>Re (-k2/k1) \<ge> 0\<close>
    by auto
  finally show ?thesis
    .
qed

lemma circline_type_neg_card_gt3_diag:
  assumes "circline_type H < 0" and "circline_diag H"
  shows "\<exists> A B C. A \<noteq> B \<and> A \<noteq> C \<and> B \<noteq> C \<and> {A, B, C} \<subseteq> circline_set H"
  using assms
  unfolding circline_set_def
  apply (simp del: HOL.ex_simps)
proof (transfer, transfer)
  fix H
  assume hh: "hermitean H \<and> H \<noteq> mat_zero"
  obtain A B C D where HH: "H = (A, B, C, D)"
    by (cases H) auto
  hence HH_elems: "is_real A" "is_real D" "C = cnj B"
    using hermitean_elems[of A B C D] hh
    by auto
  assume "circline_type_cmat H < 0" "is_diag_circline_cmat H"
  hence "B = 0" "C = 0" "Re A * Re D < 0" "A \<noteq> 0"
    using HH \<open>is_real A\<close> \<open>is_real D\<close>
    by auto

  let ?x = "sqrt (Re (- D / A))"
  let ?A = "(rcis ?x 0, 1)"
  let ?B = "(rcis ?x (pi/2), 1)"
  let ?C = "(rcis ?x pi, 1)"
  from quad_form_diagonal_iff[OF \<open>A \<noteq> 0\<close> \<open>is_real A\<close> \<open>is_real D\<close> \<open>Re A * Re D < 0\<close>]
  have "quad_form ?A (A, 0, 0, D) = 0"  "quad_form ?B (A, 0, 0, D) = 0"  "quad_form ?C (A, 0, 0, D) = 0"
    by (auto simp del: rcis_zero_arg)
  hence "on_circline_cmat_cvec H ?A \<and> on_circline_cmat_cvec H ?B \<and> on_circline_cmat_cvec H ?C"
    using HH \<open>B = 0\<close> \<open>C = 0\<close>
    by simp
  moreover                                    
  have "Re (D / A) < 0"
    using \<open>Re A * Re D < 0\<close> \<open>A \<noteq> 0\<close> \<open>is_real A\<close> \<open>is_real D\<close>
    using Re_divide_real[of A D]
    by (metis Re_complex_div_lt_0 Re_mult_real div_reals eq_cnj_iff_real is_real_div)
  hence "\<not> ?A \<approx>\<^sub>v ?B \<and> \<not> ?A \<approx>\<^sub>v ?C \<and> \<not> ?B \<approx>\<^sub>v ?C"
    unfolding rcis_def
    by (auto simp add: cis_def complex.corec)
  moreover
  have "?A \<noteq> vec_zero" "?B \<noteq> vec_zero" "?C \<noteq> vec_zero"
    by auto
  ultimately
  show "\<exists>A\<in>{v. v \<noteq> vec_zero}. \<exists>B\<in>{v. v \<noteq> vec_zero}. \<exists>C\<in>{v. v \<noteq> vec_zero}.
            \<not> A \<approx>\<^sub>v B \<and> \<not> A \<approx>\<^sub>v C \<and> \<not> B \<approx>\<^sub>v C \<and>
            on_circline_cmat_cvec H A \<and> on_circline_cmat_cvec H B \<and> on_circline_cmat_cvec H C"
    by blast
qed

lemma circline_type_neg_card_gt3:
  assumes "circline_type H < 0"
  shows "\<exists> A B C. A \<noteq> B \<and> A \<noteq> C \<and> B \<noteq> C \<and> {A, B, C} \<subseteq> circline_set H"
proof-
  obtain M H' where "moebius_circline M H = H'" "circline_diag H'"
    using circline_diagonalize[of H] assms
    by auto
  moreover
  hence "circline_type H' < 0"
    using assms moebius_preserve_circline_type
    by auto
  ultimately
  obtain A B C where "A \<noteq> B" "A \<noteq> C" "B \<noteq> C" "{A, B, C} \<subseteq> circline_set H'"
    using circline_type_neg_card_gt3_diag[of H']
    by auto
  let ?iM = "moebius_inv M"
  have "moebius_circline ?iM H' = H"
    using \<open>moebius_circline M H = H'\<close>[symmetric]
    by simp
  let ?A = "moebius_pt ?iM A" and ?B= "moebius_pt ?iM B" and ?C = "moebius_pt ?iM C"
  have "?A \<in> circline_set H"  "?B \<in> circline_set H"  "?C \<in> circline_set H"
    using \<open>moebius_circline ?iM H' = H\<close>[symmetric] \<open>{A, B, C} \<subseteq> circline_set H'\<close>
    by simp_all
  moreover
  have "?A \<noteq> ?B" "?A \<noteq> ?C" "?B \<noteq> ?C"
    using \<open>A \<noteq> B\<close> \<open>A \<noteq> C\<close> \<open>B \<noteq> C\<close>
    by auto
  ultimately
  show ?thesis
    by auto
qed

(* ----------------------------------------------------------------- *)
subsubsection \<open>Positive type circline set cardinality\<close>
(* ----------------------------------------------------------------- *)

lemma circline_type_pos_card_eq0_diag:
  assumes "circline_diag H" and "circline_type H > 0"
  shows "circline_set H = {}"
using assms
unfolding circline_set_def
apply simp
proof (transfer, transfer)
  fix H
  assume hh: "hermitean H \<and> H \<noteq> mat_zero"
  obtain A B C D where HH: "H = (A, B, C, D)"
    by (cases H) auto
  hence HH_elems: "is_real A" "is_real D" "C = cnj B"
    using hermitean_elems[of A B C D] hh
    by auto
  assume "is_diag_circline_cmat H" "0 < circline_type_cmat H"
  hence "B = 0" "C = 0" "Re A * Re D > 0" "A \<noteq> 0"
    using HH \<open>is_real A\<close> \<open>is_real D\<close>
    by auto
  show "\<forall>x\<in>{v. v \<noteq> vec_zero}. \<not> on_circline_cmat_cvec H x"
  proof
    fix x
    assume "x \<in> {v. v \<noteq> vec_zero}"
    obtain x1 x2 where xx: "x = (x1, x2)"
      by (cases x, auto)
    have "(Re A > 0 \<and> Re D > 0) \<or> (Re A < 0 \<and> Re D < 0)"
      using \<open>Re A * Re D > 0\<close>
      by (metis linorder_neqE_linordered_idom mult_eq_0_iff zero_less_mult_pos zero_less_mult_pos2)
    moreover
    have "(Re (x1 * cnj x1) \<ge> 0 \<and> Re (x2 * cnj x2) > 0) \<or> (Re (x1 * cnj x1) > 0 \<and> Re (x2 * cnj x2) \<ge> 0)"
      using \<open>x \<in> {v. v \<noteq> vec_zero}\<close> xx
      apply auto
      apply (simp add: complex_neq_0 power2_eq_square)+
      done
    ultimately
    have "Re A * Re (x1 * cnj x1) + Re D * Re (x2 * cnj x2) \<noteq> 0"
      by (smt mult_neg_pos mult_nonneg_nonneg mult_nonpos_nonneg mult_pos_pos)
    hence "A * (x1 * cnj x1) + D * (x2 * cnj x2) \<noteq> 0"
      using \<open>is_real A\<close> \<open>is_real D\<close>
      by (metis Re_mult_real plus_complex.simps(1) zero_complex.simps(1))
    thus "\<not> on_circline_cmat_cvec H x"
      using HH \<open>B = 0\<close> \<open>C = 0\<close> xx
      by (simp add: vec_cnj_def field_simps)
  qed
qed

lemma circline_type_pos_card_eq0:
  assumes "circline_type H > 0"
  shows "circline_set H = {}"
proof-
  obtain M H' where "moebius_circline M H = H'" "circline_diag H'"
    using circline_diagonalize[of H] assms
    by auto
  moreover
  hence "circline_type H' > 0"
    using assms moebius_preserve_circline_type
    by auto
  ultimately
  have "circline_set H' = {}"
    using circline_type_pos_card_eq0_diag[of H']
    by auto
  let ?iM = "moebius_inv M"
  have "moebius_circline ?iM H' = H"
    using \<open>moebius_circline M H = H'\<close>[symmetric]
    by simp
  thus ?thesis
    using \<open>circline_set H' = {}\<close>
    by auto
qed

(* ----------------------------------------------------------------- *)
subsubsection \<open>Cardinality determines type\<close>
(* ----------------------------------------------------------------- *)

lemma card_eq1_circline_type_zero:
  assumes "\<exists> z. circline_set H = {z}"
  shows "circline_type H = 0"
proof (cases "circline_type H < 0")
  case True
  thus ?thesis
    using circline_type_neg_card_gt3[of H] assms
    by auto
next
  case False
  show ?thesis
  proof (cases "circline_type H > 0")
    case True
    thus ?thesis
      using circline_type_pos_card_eq0[of H] assms
      by auto
  next
    case False
    thus ?thesis
      using \<open>\<not> (circline_type H) < 0\<close>
      by simp
  qed
qed

(* ----------------------------------------------------------------- *)
subsubsection \<open>Circline set is injective\<close>
(* ----------------------------------------------------------------- *)

lemma inj_circline_set:
  assumes "circline_set H = circline_set H'" and "circline_set H \<noteq> {}"
  shows "H = H'"
proof (cases "circline_type H < 0")
  case True
  then obtain A B C where "A \<noteq> B" "A \<noteq> C" "B \<noteq> C" "{A, B, C} \<subseteq> circline_set H"
    using circline_type_neg_card_gt3[of H]
    by auto
  hence "\<exists>!H. A \<in> circline_set H \<and> B \<in> circline_set H \<and> C \<in> circline_set H"
    using unique_circline_set[of A B C]
    by simp
  thus ?thesis
    using \<open>circline_set H = circline_set H'\<close> \<open>{A, B, C} \<subseteq> circline_set H\<close>
    by auto
next
  case False
  show ?thesis
  proof (cases "circline_type H = 0")
    case True
    moreover
    then obtain A where "{A} = circline_set H"
      using circline_type_zero_card_eq1[of H]
      by auto
    moreover
    hence "circline_type H' = 0"
      using \<open>circline_set H = circline_set H'\<close> card_eq1_circline_type_zero[of H']
      by auto
    ultimately
    show ?thesis
      using unique_circline_type_zero[of A] \<open>circline_set H = circline_set H'\<close>
      by auto
  next
    case False
    hence "circline_type H > 0"
      using \<open>\<not> (circline_type H < 0)\<close>
      by auto
    thus ?thesis
      using \<open>circline_set H \<noteq> {}\<close>  circline_type_pos_card_eq0[of H]
      by auto
  qed
qed

(* ----------------------------------------------------------------- *)
subsection \<open>Circline points - cross ratio real\<close>
(* ----------------------------------------------------------------- *)

lemma four_points_on_circline_iff_cross_ratio_real:
  assumes "distinct [z, u, v, w]"
  shows "is_real (to_complex (cross_ratio z u v w)) \<longleftrightarrow> 
         (\<exists> H. {z, u, v, w} \<subseteq> circline_set H)"
proof-
  have "\<forall> z. distinct [z, u, v, w] \<longrightarrow> is_real (to_complex (cross_ratio z u v w)) \<longleftrightarrow> (\<exists> H. {z, u, v, w} \<subseteq> circline_set H)"
       (is "?P u v w")
  proof (rule wlog_moebius_01inf[of ?P u v w])
    fix M a b c
    assume aa: "?P a b c"
    let ?Ma = "moebius_pt M a" and ?Mb = "moebius_pt M b" and ?Mc = "moebius_pt M c"
    show "?P ?Ma ?Mb ?Mc"
    proof (rule allI, rule impI)
      fix z
      obtain d where *: "z = moebius_pt M d"
        using bij_moebius_pt[of M]
        unfolding bij_def
        by auto
      let ?Md = "moebius_pt M d"
      assume "distinct [z, moebius_pt M a, moebius_pt M b, moebius_pt M c]"
      hence "distinct [a, b, c, d]"
        using *
        by auto
      moreover
      have "(\<exists> H. {d, a, b, c} \<subseteq> circline_set H) \<longleftrightarrow> (\<exists> H. {z, ?Ma, ?Mb, ?Mc} \<subseteq> circline_set H)"
        using *
        apply auto
        apply (rule_tac x="moebius_circline M H" in exI, simp)
        apply (rule_tac x="moebius_circline (moebius_inv M) H" in exI, simp)
        done
      ultimately
      show "is_real (to_complex (cross_ratio z ?Ma ?Mb ?Mc)) = (\<exists>H. {z, ?Ma, ?Mb, ?Mc} \<subseteq> circline_set H)"
        using aa[rule_format, of d] *
        by auto
    qed
  next
    show "?P 0\<^sub>h 1\<^sub>h \<infinity>\<^sub>h"
    proof safe
      fix z
      assume "distinct [z, 0\<^sub>h, 1\<^sub>h, \<infinity>\<^sub>h]"
      hence "z \<noteq> \<infinity>\<^sub>h"
        by auto
      assume "is_real (to_complex (cross_ratio z 0\<^sub>h 1\<^sub>h \<infinity>\<^sub>h))"
      hence "is_real (to_complex z)"
        by simp
      hence "z \<in> circline_set x_axis"
        using of_complex_to_complex[symmetric, OF \<open>z \<noteq> \<infinity>\<^sub>h\<close>]
        using circline_set_x_axis
        by auto
      thus "\<exists>H. {z, 0\<^sub>h, 1\<^sub>h, \<infinity>\<^sub>h} \<subseteq> circline_set H"
        by (rule_tac x=x_axis in exI, auto)
    next
      fix z H
      assume *: "distinct [z, 0\<^sub>h, 1\<^sub>h, \<infinity>\<^sub>h]" "{z, 0\<^sub>h, 1\<^sub>h, \<infinity>\<^sub>h} \<subseteq> circline_set H"
      hence "H = x_axis"
        by auto
      hence "z \<in> circline_set x_axis"
        using *
        by auto
      hence "is_real (to_complex z)"
        using * circline_set_x_axis
        by auto
      thus "is_real (to_complex (cross_ratio z 0\<^sub>h 1\<^sub>h \<infinity>\<^sub>h))"
        by simp
    qed
  next
    show "u \<noteq> v" "v \<noteq> w" "u \<noteq> w"
      using assms
      by auto
  qed
  thus ?thesis
    using assms
    by auto
qed

(* ----------------------------------------------------------------- *)
subsection \<open>Symmetric points wrt. circline\<close>
(* ----------------------------------------------------------------- *)

text \<open>In the extended complex plane there are no substantial differences between circles and lines,
so we will consider only one kind of relation and call two points \emph{circline symmetric} if they
are mapped to one another using either reflection or inversion over arbitrary line or circle. Points
are symmetric iff the bilinear form of their representation vectors and matrix is zero.\<close>

definition circline_symmetric_cvec_cmat :: "complex_vec \<Rightarrow> complex_vec \<Rightarrow> complex_mat \<Rightarrow> bool" where
  [simp]: "circline_symmetric_cvec_cmat z1 z2 H \<longleftrightarrow> bilinear_form z1 z2 H = 0"
lift_definition circline_symmetric_hcoords_clmat :: "complex_homo_coords \<Rightarrow> complex_homo_coords \<Rightarrow> circline_mat \<Rightarrow> bool" is circline_symmetric_cvec_cmat
  done
lift_definition circline_symmetric :: "complex_homo \<Rightarrow> complex_homo \<Rightarrow> circline \<Rightarrow> bool" is circline_symmetric_hcoords_clmat
  apply transfer
  apply (simp del: bilinear_form_def)
  apply (erule exE)+
  apply (simp add: bilinear_form_scale_m bilinear_form_scale_v1 bilinear_form_scale_v2 del: vec_cnj_sv quad_form_def bilinear_form_def)
  done

lemma symmetry_principle [simp]:
  assumes "circline_symmetric z1 z2 H"
  shows "circline_symmetric (moebius_pt M z1) (moebius_pt M z2) (moebius_circline M H)"
  using assms
  by (transfer, transfer, simp del: bilinear_form_def congruence_def)

text \<open>Symmetry wrt. @{term "unit_circle"}\<close>
lemma circline_symmetric_0inf_disc [simp]:
  shows "circline_symmetric 0\<^sub>h \<infinity>\<^sub>h unit_circle"
  by (transfer, transfer, simp add: vec_cnj_def)

lemma circline_symmetric_inv_homo_disc [simp]:
  shows "circline_symmetric a (inversion a) unit_circle"
  unfolding inversion_def
  by (transfer, transfer) (case_tac a, auto simp add: vec_cnj_def)

lemma circline_symmetric_inv_homo_disc':
  assumes "circline_symmetric a a' unit_circle"
  shows "a' = inversion a"
  unfolding inversion_def
  using assms
proof (transfer, transfer)
  fix a a'
  assume vz: "a \<noteq> vec_zero" "a' \<noteq> vec_zero"
  obtain a1 a2 where aa: "a = (a1, a2)"
    by (cases a, auto)
  obtain a1' a2' where aa': "a' = (a1', a2')"
    by (cases a', auto)
  assume *: "circline_symmetric_cvec_cmat a a' unit_circle_cmat"
  show "a' \<approx>\<^sub>v (conjugate_cvec \<circ> reciprocal_cvec) a"
  proof (cases "a1' = 0")
    case True
    thus ?thesis
      using aa aa' vz *
      by (auto simp add: vec_cnj_def field_simps)
  next
    case False
    show ?thesis
    proof (cases "a2 = 0")
      case True
      thus ?thesis
        using \<open>a1' \<noteq> 0\<close>
        using aa aa' * vz
        by (simp add:  vec_cnj_def field_simps)
    next
      case False
      thus ?thesis
        using \<open>a1' \<noteq> 0\<close> aa aa' *
        by (simp add: vec_cnj_def field_simps) (rule_tac x="cnj a2 / a1'" in exI, simp add: field_simps)
    qed
  qed
qed

lemma ex_moebius_circline_x_axis:
  assumes "circline_type H < 0"
  shows "\<exists> M. moebius_circline M H = x_axis"
proof-
  obtain A B C where *: "A \<noteq> B" "A \<noteq> C" "B \<noteq> C" "on_circline H A" "on_circline H B" "on_circline H C"
    using circline_type_neg_card_gt3[OF assms]
    unfolding circline_set_def
    by auto
  then obtain M where "moebius_pt M A = 0\<^sub>h" "moebius_pt M B = 1\<^sub>h" "moebius_pt M C = \<infinity>\<^sub>h"
    using ex_moebius_01inf by blast
  hence "moebius_circline M H = x_axis"
    using *
    by (metis circline_set_I circline_set_moebius_circline rev_image_eqI unique_circline_01inf')
  thus ?thesis
    by blast
qed

lemma wlog_circline_x_axis:
  assumes "circline_type H < 0"
  assumes "\<And> M H. P H \<Longrightarrow> P (moebius_circline M H)"
  assumes "P x_axis"
  shows "P H"
proof-
  obtain M where "moebius_circline M H = x_axis"
    using ex_moebius_circline_x_axis[OF assms(1)]
    by blast
  then obtain M' where "moebius_circline M' x_axis = H"
    by (metis moebius_circline_comp_inv_left)
  thus ?thesis
    using assms(2)[of x_axis M'] assms(3)
    by simp
qed

lemma circline_intersection_at_most_2_points:
  assumes "H1 \<noteq> H2"
  shows "finite (circline_intersection H1 H2) \<and> card (circline_intersection H1 H2) \<le> 2"
proof (rule ccontr)
  assume "\<not> ?thesis"
  hence "infinite (circline_intersection H1 H2) \<or> card (circline_intersection H1 H2) > 2"
    by auto
  hence "\<exists> A B C. A \<noteq> B \<and> B \<noteq> C \<and> A \<noteq> C \<and> {A, B, C} \<subseteq> circline_intersection H1 H2"
  proof
    assume "card (circline_intersection H1 H2) > 2"
    thus ?thesis
      using card_geq_3_iff_contains_3_elems[of "circline_intersection H1 H2"]
      by auto
  next
    assume "infinite (circline_intersection H1 H2)"
    thus ?thesis
      using infinite_contains_3_elems
      by blast
  qed
  then obtain A B C where "A \<noteq> B" "B \<noteq> C" "A \<noteq> C" "{A, B, C} \<subseteq> circline_intersection H1 H2"
    by blast
  hence "H2 = H1"
    using circline_intersection_def mem_Collect_eq unique_circline_set by fastforce
  thus False
    using assms
    by simp
qed
              
end
