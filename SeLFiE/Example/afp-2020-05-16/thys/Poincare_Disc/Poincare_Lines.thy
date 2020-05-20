(* ------------------------------------------------------------------ *)
section \<open>H-lines in the Poincar\'e model\<close>
(* ------------------------------------------------------------------ *)

theory Poincare_Lines
  imports Complex_Geometry.Unit_Circle_Preserving_Moebius Complex_Geometry.Circlines_Angle
begin


(* ------------------------------------------------------------------ *)
subsection \<open>Definition and basic properties of h-lines\<close>
(* ------------------------------------------------------------------ *)

text \<open>H-lines in the Poincar\'e model are either line segments passing trough the origin or
segments (within the unit disc) of circles that are perpendicular to the unit circle. Algebraically
these are circlines that are represented by Hermitean matrices of
the form
$$H = \left(
 \begin{array}{cc}
 A & B\\
 \overline{B} & A
 \end{array}
\right),$$
for $A \in \mathbb{R}$, and $B \in \mathbb{C}$, and $|B|^2 > A^2$,
where the circline equation is the usual one: $z^*Hz = 0$, for homogenous coordinates $z$.\<close>

definition is_poincare_line_cmat :: "complex_mat \<Rightarrow> bool" where
  [simp]: "is_poincare_line_cmat H \<longleftrightarrow>
             (let (A, B, C, D) = H
               in hermitean (A, B, C, D) \<and> A = D \<and> (cmod B)\<^sup>2 > (cmod A)\<^sup>2)"

lift_definition is_poincare_line_clmat :: "circline_mat \<Rightarrow> bool" is is_poincare_line_cmat
  done

text \<open>We introduce the predicate that checks if a given complex matrix is a matrix of a h-line in
the Poincar\'e model, and then by means of the lifting package lift it to the type of non-zero
Hermitean matrices, and then to circlines (that are equivalence classes of such matrices).\<close>

lift_definition is_poincare_line :: "circline \<Rightarrow> bool" is is_poincare_line_clmat
proof (transfer, transfer)
  fix H1 H2 :: complex_mat
  assume hh: "hermitean H1 \<and> H1 \<noteq> mat_zero" "hermitean H2 \<and> H2 \<noteq> mat_zero"
  assume "circline_eq_cmat H1 H2"
  thus "is_poincare_line_cmat H1 \<longleftrightarrow> is_poincare_line_cmat H2"
    using hh
    by (cases H1, cases H2) (auto simp add: power_mult_distrib)
qed

lemma is_poincare_line_mk_circline:
  assumes "(A, B, C, D) \<in> hermitean_nonzero"
  shows "is_poincare_line (mk_circline A B C D) \<longleftrightarrow> (cmod B)\<^sup>2 > (cmod A)\<^sup>2 \<and> A = D"
  using assms
  by (transfer, transfer, auto simp add: Let_def)


text\<open>Abstract characterisation of @{term is_poincare_line} predicate: H-lines in the Poincar\'e
model are real circlines (circlines with the negative determinant) perpendicular to the unit
circle.\<close>

lemma is_poincare_line_iff:
  shows "is_poincare_line H \<longleftrightarrow> circline_type H = -1 \<and> perpendicular H unit_circle"
  unfolding perpendicular_def
proof (simp, transfer, transfer)
  fix H
  assume hh: "hermitean H \<and> H \<noteq> mat_zero"
  obtain A B C D where *: "H = (A, B, C, D)"
    by (cases H, auto)
  have **: "is_real A" "is_real D" "C = cnj B"
    using hh * hermitean_elems
    by auto
  hence "(Re A = Re D \<and> cmod A * cmod A < cmod B * cmod B) =
         (Re A * Re D < Re B * Re B + Im B * Im B \<and> (Re D = Re A \<or> Re A * Re D = Re B * Re B + Im B * Im B))"
    using *
    by (smt cmod_power2 power2_eq_square zero_power2)+
  thus "is_poincare_line_cmat H \<longleftrightarrow>
         circline_type_cmat H = - 1 \<and> cos_angle_cmat (of_circline_cmat H) unit_circle_cmat = 0"
    using * **
    by (auto simp add: sgn_1_neg complex_eq_if_Re_eq cmod_square power2_eq_square simp del: pos_oriented_cmat_def)
qed

text\<open>The @{term x_axis} is an h-line.\<close>
lemma is_poincare_line_x_axis [simp]:
  shows "is_poincare_line x_axis"
  by (transfer, transfer) (auto simp add: hermitean_def mat_adj_def mat_cnj_def)

text\<open>The @{term unit_circle} is not an h-line.\<close>
lemma not_is_poincare_line_unit_circle [simp]:
  shows "\<not> is_poincare_line unit_circle"
  by (transfer, transfer, simp)

(* ------------------------------------------------------------------ *)
subsubsection \<open>Collinear points\<close>
(* ------------------------------------------------------------------ *)

text\<open>Points are collinear if they all belong to an h-line. \<close>
definition poincare_collinear :: "complex_homo set \<Rightarrow> bool" where
  "poincare_collinear S \<longleftrightarrow> (\<exists> p. is_poincare_line p \<and> S \<subseteq> circline_set p)"

(* ------------------------------------------------------------------ *)
subsubsection \<open>H-lines and inversion\<close>
(* ------------------------------------------------------------------ *)

text\<open>Every h-line in the Poincar\'e model contains the inverse (wrt.~the unit circle) of each of its
points (note that at most one of them belongs to the unit disc).\<close>
lemma is_poincare_line_inverse_point:
  assumes "is_poincare_line H" "u \<in> circline_set H"
  shows "inversion u \<in> circline_set H"
  using assms
  unfolding is_poincare_line_iff circline_set_def perpendicular_def inversion_def
  apply simp
proof (transfer, transfer)
  fix u H
  assume hh: "hermitean H \<and> H \<noteq> mat_zero" "u \<noteq> vec_zero" and
         aa: "circline_type_cmat H = - 1 \<and> cos_angle_cmat (of_circline_cmat H) unit_circle_cmat = 0" "on_circline_cmat_cvec H u"
  obtain A B C D u1 u2 where *: "H = (A, B, C, D)" "u = (u1, u2)"
    by (cases H, cases u, auto)
  have "is_real A" "is_real D" "C = cnj B"
    using * hh hermitean_elems
    by auto
  moreover
  have "A = D"
    using aa(1) * \<open>is_real A\<close> \<open>is_real D\<close>
    by (auto simp del: pos_oriented_cmat_def simp add: complex.expand split: if_split_asm)
  thus "on_circline_cmat_cvec H (conjugate_cvec (reciprocal_cvec u))"
    using aa(2) *
    by (simp add: vec_cnj_def field_simps)
qed

text\<open>Every h-line in the Poincar\'e model and is invariant under unit circle inversion.\<close>

lemma circline_inversion_poincare_line:
  assumes "is_poincare_line H"
  shows "circline_inversion H = H"
proof-
  obtain u v w where *: "u \<noteq> v" "v \<noteq> w" "u \<noteq> w" "{u, v, w} \<subseteq> circline_set H"
    using assms is_poincare_line_iff[of H]
    using circline_type_neg_card_gt3[of H]
    by auto
  hence "{inversion u, inversion v, inversion w} \<subseteq> circline_set (circline_inversion H)"
        "{inversion u, inversion v, inversion w} \<subseteq> circline_set H"
    using is_poincare_line_inverse_point[OF assms]
    by auto
  thus ?thesis
    using * unique_circline_set[of "inversion u" "inversion v" "inversion w"]
    by (metis insert_subset inversion_involution)
qed

(* ------------------------------------------------------------------ *)
subsubsection \<open>Classification of h-lines into Euclidean segments and circles\<close>
(* ------------------------------------------------------------------ *)

text\<open>If an h-line contains zero, than it also contains infinity (the inverse point of zero) and is by
definition an Euclidean line.\<close>
lemma is_poincare_line_trough_zero_trough_infty [simp]:
  assumes "is_poincare_line l" and "0\<^sub>h \<in> circline_set l"
  shows "\<infinity>\<^sub>h \<in> circline_set l"
  using is_poincare_line_inverse_point[OF assms]
  by simp

lemma is_poincare_line_trough_zero_is_line:
  assumes "is_poincare_line l" and "0\<^sub>h \<in> circline_set l"
  shows "is_line l"
  using assms
  using inf_in_circline_set is_poincare_line_trough_zero_trough_infty
  by blast

text\<open>If an h-line does not contain zero, than it also does not contain infinity (the inverse point of
zero) and is by definition an Euclidean circle.\<close>
lemma is_poincare_line_not_trough_zero_not_trough_infty [simp]:
  assumes "is_poincare_line l"
  assumes "0\<^sub>h \<notin> circline_set l"
  shows "\<infinity>\<^sub>h \<notin> circline_set l"
  using assms
  using is_poincare_line_inverse_point[OF assms(1), of "\<infinity>\<^sub>h"]
  by auto

lemma is_poincare_line_not_trough_zero_is_circle:
  assumes "is_poincare_line l" "0\<^sub>h \<notin> circline_set l"
  shows "is_circle l"
  using assms
  using inf_in_circline_set is_poincare_line_not_trough_zero_not_trough_infty
  by auto

(* ------------------------------------------------------------------ *)
subsubsection\<open>Points on h-line\<close>
(* ------------------------------------------------------------------ *)

text\<open>Each h-line in the Poincar\'e model contains at least two different points within the unit
disc.\<close>

text\<open>First we prove an auxiliary lemma.\<close>
lemma ex_is_poincare_line_points':
  assumes i12: "i1 \<in> circline_set H \<inter> unit_circle_set"
               "i2 \<in> circline_set H \<inter> unit_circle_set"
               "i1 \<noteq> i2"
  assumes a: "a \<in> circline_set H" "a \<notin> unit_circle_set"
  shows "\<exists> b. b \<noteq> i1 \<and> b \<noteq> i2 \<and> b \<noteq> a \<and> b \<noteq> inversion a \<and> b \<in> circline_set H"
proof-
  have "inversion a \<notin> unit_circle_set"
    using \<open>a \<notin> unit_circle_set\<close> 
    unfolding unit_circle_set_def circline_set_def
    by (metis inversion_id_iff_on_unit_circle inversion_involution mem_Collect_eq)

  have "a \<noteq> inversion a"
    using \<open>a \<notin> unit_circle_set\<close> inversion_id_iff_on_unit_circle[of a]
    unfolding unit_circle_set_def circline_set_def
    by auto

  have "a \<noteq> i1" "a \<noteq> i2" "inversion a \<noteq> i1" "inversion a \<noteq> i2"
    using assms \<open>inversion a \<notin> unit_circle_set\<close>
    by auto

  then obtain b where cr2: "cross_ratio b i1 a i2 = of_complex 2"
    using \<open>i1 \<noteq> i2\<close>
    using ex_cross_ratio[of i1 a i2]
    by blast

  have distinct_b: "b \<noteq> i1" "b \<noteq> i2" "b \<noteq> a"
    using \<open>i1 \<noteq> i2\<close> \<open>a \<noteq> i1\<close> \<open>a \<noteq> i2\<close>
    using ex1_cross_ratio[of i1 a i2]
    using cross_ratio_0[of i1 a i2] cross_ratio_1[of i1 a i2] cross_ratio_inf[of i1 i2 a]
    using cr2
    by auto

  hence "b \<in> circline_set H" 
    using assms four_points_on_circline_iff_cross_ratio_real[of b i1 a i2] cr2
    using unique_circline_set[of i1 i2 a]
    by auto

  moreover

  have "b \<noteq> inversion a"
  proof (rule ccontr)
    assume *: "\<not> ?thesis"
    have "inversion i1 = i1" "inversion i2 = i2"
      using i12
      unfolding unit_circle_set_def
      by auto
    hence "cross_ratio (inversion a) i1 a i2 = cross_ratio a i1 (inversion a) i2"
      using * cross_ratio_inversion[of i1 a i2 b] \<open>a \<noteq> i1\<close> \<open>a \<noteq> i2\<close> \<open>i1 \<noteq> i2\<close> \<open>b \<noteq> i1\<close>
      using four_points_on_circline_iff_cross_ratio_real[of b i1 a i2]
      using i12 distinct_b conjugate_id_iff[of "cross_ratio b i1 a i2"]
      using i12 a \<open>b \<in> circline_set H\<close>            
      by auto
    hence "cross_ratio (inversion a) i1 a i2 \<noteq> of_complex 2"
      using cross_ratio_commute_13[of "inversion a" i1 a i2]
      using reciprocal_id_iff
      using of_complex_inj
      by force
    thus False
      using * cr2
      by simp
  qed

  ultimately
  show ?thesis
    using assms \<open>b \<noteq> i1\<close> \<open>b \<noteq> i2\<close> \<open>b \<noteq> a\<close>
    by auto
qed

text\<open>Now we can prove the statement.\<close>
lemma ex_is_poincare_line_points:
  assumes "is_poincare_line H"
  shows "\<exists> u v. u \<in> unit_disc \<and> v \<in> unit_disc \<and> u \<noteq> v \<and> {u, v} \<subseteq> circline_set H"
proof-
  obtain u v w where *: "u \<noteq> v" "v \<noteq> w" "u \<noteq> w" "{u, v, w} \<subseteq> circline_set H"
    using assms is_poincare_line_iff[of H]
    using circline_type_neg_card_gt3[of H]
    by auto

  have "\<not> {u, v, w} \<subseteq> unit_circle_set"
    using unique_circline_set[of u v w] *
    by (metis assms insert_subset not_is_poincare_line_unit_circle unit_circle_set_def)

  hence "H \<noteq> unit_circle"
    unfolding unit_circle_set_def
    using *
    by auto

  show ?thesis
  proof (cases "(u \<in> unit_disc \<and> v \<in> unit_disc) \<or>
                (u \<in> unit_disc \<and> w \<in> unit_disc) \<or>
                (v \<in> unit_disc \<and> w \<in> unit_disc)")
    case True
    thus ?thesis
      using *
      by auto
  next
    case False

    have "\<exists> a b. a \<noteq> b \<and> a \<noteq> inversion b \<and> a \<in> circline_set H \<and> b \<in> circline_set H \<and> a \<notin> unit_circle_set \<and> b \<notin> unit_circle_set"
    proof (cases "(u \<in> unit_circle_set \<and> v \<in> unit_circle_set) \<or>
                  (u \<in> unit_circle_set \<and> w \<in> unit_circle_set) \<or>
                  (v \<in> unit_circle_set \<and> w \<in> unit_circle_set)")
      case True
      then obtain i1 i2 a where *:
        "i1 \<in> unit_circle_set \<inter> circline_set H" "i2 \<in> unit_circle_set \<inter> circline_set H" 
        "a \<in> circline_set H" "a \<notin> unit_circle_set"
        "i1 \<noteq> i2" "i1 \<noteq> a" "i2 \<noteq> a"
        using * \<open>\<not> {u, v, w} \<subseteq> unit_circle_set\<close>
        by auto
      then obtain b where "b \<in> circline_set H" "b \<noteq> i1" "b \<noteq> i2" "b \<noteq> a" "b \<noteq> inversion a"
        using ex_is_poincare_line_points'[of i1 H i2 a]
        by blast

      hence "b \<notin> unit_circle_set"
        using * \<open>H \<noteq> unit_circle\<close> unique_circline_set[of i1 i2 b]
        unfolding unit_circle_set_def
        by auto
        
      thus ?thesis
        using * \<open>b \<in> circline_set H\<close> \<open>b \<noteq> a\<close> \<open>b \<noteq> inversion a\<close>
        by auto
    next
      case False  
      then obtain f g h where
        *: "f \<noteq> g" "f \<in> circline_set H" "f \<notin> unit_circle_set"  
                    "g \<in> circline_set H" "g \<notin> unit_circle_set"
                    "h \<in> circline_set H" "h \<noteq> f" "h \<noteq> g"
        using *
        by auto
      show ?thesis
      proof (cases "f = inversion g")   
        case False
        thus ?thesis
          using *
          by auto
      next
        case True
        show ?thesis
        proof (cases "h \<in> unit_circle_set")
          case False
          thus ?thesis
            using * \<open>f = inversion g\<close>
            by auto
        next
          case True
          obtain m where cr2: "cross_ratio m h f g = of_complex 2"
            using ex_cross_ratio[of h f g] * \<open>f \<noteq> g\<close> \<open>h \<noteq> f\<close> \<open>h \<noteq> g\<close>
            by auto
          hence "m \<noteq> h" "m \<noteq> f" "m \<noteq> g"
            using \<open>h \<noteq> f\<close> \<open>h \<noteq> g\<close> \<open>f \<noteq> g\<close>
            using ex1_cross_ratio[of h f g]
            using cross_ratio_0[of h f g] cross_ratio_1[of h f g] cross_ratio_inf[of h g f]
            using cr2
            by auto
          hence "m \<in> circline_set H" 
            using four_points_on_circline_iff_cross_ratio_real[of m h f g] cr2
            using \<open>h \<noteq> f\<close> \<open>h \<noteq> g\<close> \<open>f \<noteq> g\<close> *
            using unique_circline_set[of h f g]
            by auto

          show ?thesis
          proof (cases "m \<in> unit_circle_set")
            case False
            thus ?thesis
              using \<open>m \<noteq> f\<close> \<open>m \<noteq> g\<close> \<open>f = inversion g\<close> * \<open>m \<in> circline_set H\<close>
              by auto
          next
            case True
            then obtain n where "n \<noteq> h" "n \<noteq> m" "n \<noteq> f" "n \<noteq> inversion f" "n \<in> circline_set H"
              using ex_is_poincare_line_points'[of h H m f] * \<open>m \<in> circline_set H\<close> \<open>h \<in> unit_circle_set\<close> \<open>m \<noteq> h\<close>
              by auto
            hence "n \<notin> unit_circle_set"
              using * \<open>H \<noteq> unit_circle\<close> unique_circline_set[of m n h] 
              using \<open>m \<noteq> h\<close> \<open>m \<in> unit_circle_set\<close> \<open>h \<in> unit_circle_set\<close> \<open>m \<in> circline_set H\<close>
              unfolding unit_circle_set_def
              by auto
        
            thus ?thesis
              using * \<open>n \<in> circline_set H\<close> \<open>n \<noteq> f\<close> \<open>n \<noteq> inversion f\<close>
              by auto
          qed
        qed
      qed
    qed
    then obtain a b where ab: "a \<noteq> b" "a \<noteq> inversion b" "a \<in> circline_set H" "b \<in> circline_set H" "a \<notin> unit_circle_set" "b \<notin> unit_circle_set"
      by blast
    have "\<forall> x. x \<in> circline_set H \<and> x \<notin> unit_circle_set \<longrightarrow> (\<exists> x'. x' \<in> circline_set H \<inter> unit_disc \<and> (x' = x \<or> x' = inversion x))"
    proof safe
      fix x
      assume x: "x \<in> circline_set H" "x \<notin> unit_circle_set" 
      show "\<exists> x'. x' \<in> circline_set H \<inter> unit_disc \<and> (x' = x \<or> x' = inversion x)"
      proof (cases "x \<in> unit_disc")
        case True
        thus ?thesis
          using x
          by auto
      next
        case False
        hence "x \<in> unit_disc_compl"
          using x  in_on_out_univ[of "ounit_circle"]
          unfolding unit_circle_set_def unit_disc_def unit_disc_compl_def
          by auto
        hence "inversion x \<in> unit_disc"
          using inversion_unit_disc_compl
          by blast
        thus ?thesis
          using is_poincare_line_inverse_point[OF assms, of x] x
          by auto
      qed
    qed
    then obtain a' b' where 
      *: "a' \<in> circline_set H" "a' \<in> unit_disc" "b' \<in> circline_set H" "b' \<in> unit_disc" and
      **: "a' = a \<or> a' = inversion a" "b' = b \<or> b' = inversion b" 
      using ab
      by blast
    have "a' \<noteq> b'"
      using \<open>a \<noteq> b\<close> \<open>a \<noteq> inversion b\<close> ** *
      by (metis inversion_involution)
    thus ?thesis
      using *
      by auto
  qed
qed

(* ------------------------------------------------------------------ *)
subsubsection \<open>H-line uniqueness\<close>
(* ------------------------------------------------------------------ *)

text\<open>There is no more than one h-line that contains two different h-points (in the disc).\<close>
lemma unique_is_poincare_line:
  assumes in_disc: "u \<in> unit_disc" "v \<in> unit_disc" "u \<noteq> v"
  assumes pl: "is_poincare_line l1" "is_poincare_line l2"
  assumes on_l: "{u, v} \<subseteq> circline_set l1 \<inter> circline_set l2"
  shows "l1 = l2"
proof-
  have "u \<noteq> inversion u" "v \<noteq> inversion u"
    using in_disc
    using inversion_noteq_unit_disc[of u v]
    using inversion_noteq_unit_disc[of u u]
    by auto
  thus ?thesis
    using on_l
    using unique_circline_set[of u "inversion u" "v"] \<open>u \<noteq> v\<close>
    using is_poincare_line_inverse_point[of l1 u]
    using is_poincare_line_inverse_point[of l2 u]
    using pl
    by auto                                                                            
qed

text\<open>For the rest of our formalization it is often useful to consider points on h-lines that are not
within the unit disc. Many lemmas in the rest of this section will have such generalizations.\<close>

text\<open>There is no more than one h-line that contains two different and not mutually inverse points
(not necessary in the unit disc).\<close>
lemma unique_is_poincare_line_general:
  assumes different: "u \<noteq> v" "u \<noteq> inversion v"
  assumes pl: "is_poincare_line l1" "is_poincare_line l2"
  assumes on_l: "{u, v} \<subseteq> circline_set l1 \<inter> circline_set l2"
  shows  "l1 = l2"
proof (cases "u \<noteq> inversion u")
  case True
  thus ?thesis
    using unique_circline_set[of u "inversion u" "v"]
    using assms
    using is_poincare_line_inverse_point by force
next
  case False
  show ?thesis
  proof (cases "v \<noteq> inversion v")
    case True
    thus ?thesis
      using unique_circline_set[of u "inversion v" "v"]
      using assms
      using is_poincare_line_inverse_point by force
  next
    case False

    have "on_circline unit_circle u" "on_circline unit_circle v"
      using `\<not> u \<noteq> inversion u` `\<not> v \<noteq> inversion v`
      using inversion_id_iff_on_unit_circle
      by fastforce+
    thus ?thesis
      using pl on_l `u \<noteq> v`
      unfolding circline_set_def
      apply simp
    proof (transfer, transfer, safe)
      fix u1 u2 v1 v2 A1 B1 C1 D1 A2 B2 C2 D2 :: complex
      let ?u = "(u1, u2)" and ?v = "(v1, v2)" and  ?H1 = "(A1, B1, C1, D1)" and ?H2 = "(A2, B2, C2, D2)"
      assume *: "?u \<noteq> vec_zero" "?v \<noteq> vec_zero"
        "on_circline_cmat_cvec unit_circle_cmat ?u" "on_circline_cmat_cvec unit_circle_cmat ?v" 
        "is_poincare_line_cmat ?H1" "is_poincare_line_cmat ?H2"
        "hermitean ?H1" "?H1 \<noteq> mat_zero" "hermitean ?H2" "?H2 \<noteq> mat_zero"
        "on_circline_cmat_cvec ?H1 ?u" "on_circline_cmat_cvec ?H1 ?v"
        "on_circline_cmat_cvec ?H2 ?u" "on_circline_cmat_cvec ?H2 ?v"
        "\<not> (u1, u2) \<approx>\<^sub>v (v1, v2)"
      have **: "A1 = D1" "A2 = D2" "C1 = cnj B1" "C2 = cnj B2" "is_real A1" "is_real A2"
        using `is_poincare_line_cmat ?H1` `is_poincare_line_cmat ?H2`
        using `hermitean ?H1` `?H1 \<noteq> mat_zero` `hermitean ?H2` `?H2 \<noteq> mat_zero`
        using hermitean_elems
        by auto

      have uv: "u1 \<noteq> 0" "u2 \<noteq> 0" "v1 \<noteq> 0" "v2 \<noteq> 0"
        using *(1-4)
        by (auto simp add: vec_cnj_def)

      have u: "cor ((Re (u1/u2))\<^sup>2) + cor ((Im (u1/u2))\<^sup>2) = 1"
        using `on_circline_cmat_cvec unit_circle_cmat ?u` uv
        apply (subst cor_add[symmetric])
        apply (subst complex_mult_cnj[symmetric])
        apply (simp add: vec_cnj_def mult.commute)
        done

      have v: "cor ((Re (v1/v2))\<^sup>2) + cor ((Im (v1/v2))\<^sup>2) = 1"
        using `on_circline_cmat_cvec unit_circle_cmat ?v` uv
        apply (subst cor_add[symmetric])
        apply (subst complex_mult_cnj[symmetric])
        apply (simp add: vec_cnj_def mult.commute)
        done

      have 
        "A1 * (cor ((Re (u1/u2))\<^sup>2) + cor ((Im (u1/u2))\<^sup>2) + 1) + cor (Re B1) * cor(2 * Re (u1/u2)) + cor (Im B1) * cor(2 * Im (u1/u2)) = 0"
        "A2 * (cor ((Re (u1/u2))\<^sup>2) + cor ((Im (u1/u2))\<^sup>2) + 1) + cor (Re B2) * cor(2 * Re (u1/u2)) + cor (Im B2) * cor(2 * Im (u1/u2)) = 0"
        "A1 * (cor ((Re (v1/v2))\<^sup>2) + cor ((Im (v1/v2))\<^sup>2) + 1) + cor (Re B1) * cor(2 * Re (v1/v2)) + cor (Im B1) * cor(2 * Im (v1/v2)) = 0"
        "A2 * (cor ((Re (v1/v2))\<^sup>2) + cor ((Im (v1/v2))\<^sup>2) + 1) + cor (Re B2) * cor(2 * Re (v1/v2)) + cor (Im B2) * cor(2 * Im (v1/v2)) = 0"
        using circline_equation_quadratic_equation[of A1 "u1/u2" B1 D1 "Re (u1/u2)" "Im (u1 / u2)" "Re B1" "Im B1"]
        using circline_equation_quadratic_equation[of A2 "u1/u2" B2 D2 "Re (u1/u2)" "Im (u1 / u2)" "Re B2" "Im B2"]
        using circline_equation_quadratic_equation[of A1 "v1/v2" B1 D1 "Re (v1/v2)" "Im (v1 / v2)" "Re B1" "Im B1"]
        using circline_equation_quadratic_equation[of A2 "v1/v2" B2 D2 "Re (v1/v2)" "Im (v1 / v2)" "Re B2" "Im B2"]
        using `on_circline_cmat_cvec ?H1 ?u` `on_circline_cmat_cvec ?H2 ?u` 
        using `on_circline_cmat_cvec ?H1 ?v` `on_circline_cmat_cvec ?H2 ?v` 
        using ** uv
        by (simp_all add: vec_cnj_def field_simps)

      hence
        "A1 + cor (Re B1) * cor(Re (u1/u2)) + cor (Im B1) * cor(Im (u1/u2)) = 0"
        "A1 + cor (Re B1) * cor(Re (v1/v2)) + cor (Im B1) * cor(Im (v1/v2)) = 0"
        "A2 + cor (Re B2) * cor(Re (u1/u2)) + cor (Im B2) * cor(Im (u1/u2)) = 0"
        "A2 + cor (Re B2) * cor(Re (v1/v2)) + cor (Im B2) * cor(Im (v1/v2)) = 0"
        using u v
        by simp_all algebra+

      hence 
        "cor (Re A1 + Re B1 * Re (u1/u2) + Im B1 * Im (u1/u2)) = 0"
        "cor (Re A2 + Re B2 * Re (u1/u2) + Im B2 * Im (u1/u2)) = 0"
        "cor (Re A1 + Re B1 * Re (v1/v2) + Im B1 * Im (v1/v2)) = 0"
        "cor (Re A2 + Re B2 * Re (v1/v2) + Im B2 * Im (v1/v2)) = 0"
        using `is_real A1` `is_real A2`
        by simp_all

      hence 
        "Re A1 + Re B1 * Re (u1/u2) + Im B1 * Im (u1/u2) = 0"
        "Re A1 + Re B1 * Re (v1/v2) + Im B1 * Im (v1/v2) = 0"
        "Re A2 + Re B2 * Re (u1/u2) + Im B2 * Im (u1/u2) = 0"
        "Re A2 + Re B2 * Re (v1/v2) + Im B2 * Im (v1/v2) = 0"
        using of_real_eq_0_iff 
        by blast+

      moreover

      have "Re(u1/u2) \<noteq> Re(v1/v2) \<or> Im(u1/u2) \<noteq> Im(v1/v2)"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        hence "u1/u2 = v1/v2"
          using complex_eqI by blast
        thus False
          using uv `\<not> (u1, u2) \<approx>\<^sub>v (v1, v2)`
          using "*"(1) "*"(2) complex_cvec_eq_mix[OF *(1) *(2)]
          by (auto simp add: field_simps)
      qed

      moreover

      have "Re A1 \<noteq> 0 \<or> Re B1 \<noteq> 0 \<or> Im B1 \<noteq> 0"
        using `?H1 \<noteq> mat_zero` **
        by (metis complex_cnj_zero complex_of_real_Re mat_zero_def of_real_0)

      ultimately

      obtain k where
        k: "Re A2 = k * Re A1" "Re B2 = k * Re B1" "Im B2 = k * Im B1"
        using linear_system_homogenous_3_2[of "\<lambda>x y z. 1 * x + Re (u1 / u2) * y + Im (u1 / u2) * z" 1 "Re (u1/u2)" "Im (u1/u2)" 
                                              "\<lambda>x y z. 1 * x + Re (v1 / v2) * y + Im (v1 / v2) * z" 1 "Re (v1/v2)" "Im (v1/v2)"
                                              "Re A2" "Re B2" "Im B2" "Re A1" "Re B1" "Im B1"]
        by (auto simp add: field_simps)

      have "Re A2 \<noteq> 0 \<or> Re B2 \<noteq> 0 \<or> Im B2 \<noteq> 0"
        using `?H2 \<noteq> mat_zero` **
        by (metis complex_cnj_zero complex_of_real_Re mat_zero_def of_real_0)
      hence "k \<noteq> 0"
        using k
        by auto

      show "circline_eq_cmat ?H1 ?H2"
        using ** k `k \<noteq> 0`
        by (auto simp add: vec_cnj_def) (rule_tac x="k" in exI, auto simp add: complex.expand)
    qed
  qed
qed

text \<open>The only h-line that goes trough zero and a non-zero point on the x-axis is the x-axis.\<close>
lemma is_poincare_line_0_real_is_x_axis:
  assumes "is_poincare_line l" "0\<^sub>h \<in> circline_set l"
    "x \<in> circline_set l \<inter> circline_set x_axis" "x \<noteq> 0\<^sub>h" "x \<noteq> \<infinity>\<^sub>h"
  shows "l = x_axis"
  using assms
  using is_poincare_line_trough_zero_trough_infty[OF assms(1-2)]
  using unique_circline_set[of x "0\<^sub>h" "\<infinity>\<^sub>h"]
  by auto

text \<open>The only h-line that goes trough zero and a non-zero point on the y-axis is the y-axis.\<close>
lemma is_poincare_line_0_imag_is_y_axis:
  assumes "is_poincare_line l" "0\<^sub>h \<in> circline_set l"
    "y \<in> circline_set l \<inter> circline_set y_axis" "y \<noteq> 0\<^sub>h" "y \<noteq> \<infinity>\<^sub>h"
  shows "l = y_axis"
  using assms
  using is_poincare_line_trough_zero_trough_infty[OF assms(1-2)]
  using unique_circline_set[of y "0\<^sub>h" "\<infinity>\<^sub>h"]
  by auto

(* ------------------------------------------------------------------ *)
subsubsection\<open>H-isometries preserve h-lines\<close>
(* ------------------------------------------------------------------ *)

text\<open>\emph{H-isometries} are defined as homographies (actions of Möbius transformations) and
antihomographies (compositions of actions of Möbius transformations with conjugation) that fix the
unit disc (map it onto itself). They also map h-lines onto h-lines\<close>

text\<open>We prove a bit more general lemma that states that all Möbius transformations that fix the
unit circle (not necessary the unit disc) map h-lines onto h-lines\<close>
lemma unit_circle_fix_preserve_is_poincare_line [simp]:
  assumes "unit_circle_fix M" "is_poincare_line H"
  shows "is_poincare_line (moebius_circline M H)"
  using assms
  unfolding is_poincare_line_iff
proof (safe)
  let ?H' = "moebius_ocircline M (of_circline H)"
  let ?U' = "moebius_ocircline M ounit_circle"
  assume ++: "unit_circle_fix M" "perpendicular H unit_circle"
  have ounit: "ounit_circle = moebius_ocircline M ounit_circle \<or>
               ounit_circle = moebius_ocircline M (opposite_ocircline ounit_circle)"
    using ++(1) unit_circle_fix_iff[of M]
    by (simp add: inj_of_ocircline moebius_circline_ocircline)

  show "perpendicular (moebius_circline M H) unit_circle"
  proof (cases "pos_oriented ?H'")
    case True
    hence *: "of_circline (of_ocircline ?H') = ?H'"
      using of_circline_of_ocircline_pos_oriented
      by blast
    from ounit show ?thesis
    proof
      assume **: "ounit_circle = moebius_ocircline M ounit_circle"
      show ?thesis
        using ++ 
        unfolding perpendicular_def
        by (simp, subst moebius_circline_ocircline, subst *, subst **) simp
    next
      assume **: "ounit_circle = moebius_ocircline M (opposite_ocircline ounit_circle)"
      show ?thesis
        using ++
        unfolding perpendicular_def
        by (simp, subst moebius_circline_ocircline, subst *, subst **) simp
    qed
  next
    case False
    hence *: "of_circline (of_ocircline ?H') = opposite_ocircline ?H'"
      by (metis of_circline_of_ocircline pos_oriented_of_circline)
    from ounit show ?thesis
    proof
      assume **: "ounit_circle = moebius_ocircline M ounit_circle"
      show ?thesis
        using ++
        unfolding perpendicular_def
        by (simp, subst moebius_circline_ocircline, subst *, subst **) simp
    next
      assume **: "ounit_circle = moebius_ocircline M (opposite_ocircline ounit_circle)"
      show ?thesis
        using ++
        unfolding perpendicular_def
        by (simp, subst moebius_circline_ocircline, subst *, subst **) simp
    qed
  qed
qed simp

lemma unit_circle_fix_preserve_is_poincare_line_iff [simp]:
  assumes "unit_circle_fix M"
  shows "is_poincare_line (moebius_circline M H) \<longleftrightarrow> is_poincare_line H"
  using assms
  using unit_circle_fix_preserve_is_poincare_line[of M H]
  using unit_circle_fix_preserve_is_poincare_line[of "moebius_inv M" "moebius_circline M H"]
  by (auto simp del: unit_circle_fix_preserve_is_poincare_line)

text\<open>Since h-lines are preserved by transformations that fix the unit circle, so is collinearity.\<close>
lemma unit_disc_fix_preserve_poincare_collinear [simp]:
  assumes "unit_circle_fix M" "poincare_collinear A"
  shows "poincare_collinear (moebius_pt M ` A)"
  using assms
  unfolding poincare_collinear_def                                                    
  by (auto, rule_tac x="moebius_circline M p" in exI, auto)

lemma unit_disc_fix_preserve_poincare_collinear_iff [simp]:
  assumes "unit_circle_fix M"
  shows "poincare_collinear (moebius_pt M ` A) \<longleftrightarrow> poincare_collinear A"
  using assms
  using unit_disc_fix_preserve_poincare_collinear[of M A]
  using unit_disc_fix_preserve_poincare_collinear[of "moebius_inv M" "moebius_pt M ` A"]
  by (auto simp del: unit_disc_fix_preserve_poincare_collinear)

lemma unit_disc_fix_preserve_poincare_collinear3 [simp]:
  assumes "unit_disc_fix M"
  shows "poincare_collinear {moebius_pt M u, moebius_pt M v, moebius_pt M w} \<longleftrightarrow>
         poincare_collinear {u, v, w}"
  using assms unit_disc_fix_preserve_poincare_collinear_iff[of M "{u, v, w}"]
  by simp

text\<open>Conjugation is also an h-isometry and it preserves h-lines.\<close>
lemma is_poincare_line_conjugate_circline [simp]:
  assumes "is_poincare_line H"
  shows "is_poincare_line (conjugate_circline H)"
  using assms
  by (transfer, transfer, auto simp add: mat_cnj_def hermitean_def mat_adj_def)

lemma is_poincare_line_conjugate_circline_iff [simp]:
  shows "is_poincare_line (conjugate_circline H) \<longleftrightarrow> is_poincare_line H"
  using is_poincare_line_conjugate_circline[of "conjugate_circline H"]
  by auto

text\<open>Since h-lines are preserved by conjugation, so is collinearity.\<close>
lemma conjugate_preserve_poincare_collinear [simp]:
  assumes "poincare_collinear A"
  shows "poincare_collinear (conjugate ` A)"
  using assms
  unfolding poincare_collinear_def
  by auto (rule_tac x="conjugate_circline p" in exI, auto)

lemma conjugate_conjugate [simp]: "conjugate ` conjugate ` A = A"
  by (auto simp add: image_iff)

lemma conjugate_preserve_poincare_collinear_iff [simp]:
  shows "poincare_collinear (conjugate ` A) \<longleftrightarrow> poincare_collinear A"
  using conjugate_preserve_poincare_collinear[of "A"]
  using conjugate_preserve_poincare_collinear[of "conjugate ` A"]
  by (auto simp del: conjugate_preserve_poincare_collinear)

(* ------------------------------------------------------------------ *)
subsubsection\<open>Mapping h-lines to x-axis\<close>
(* ------------------------------------------------------------------ *)

text\<open>Each h-line in the Poincar\'e model can be mapped onto the x-axis (by a unit-disc preserving
Möbius transformation).\<close>
lemma ex_unit_disc_fix_is_poincare_line_to_x_axis:
  assumes "is_poincare_line l"
  shows  "\<exists> M. unit_disc_fix M \<and> moebius_circline M l = x_axis"
proof-
  from assms obtain u v where "u \<noteq> v" "u \<in> unit_disc" "v \<in> unit_disc" and "{u, v} \<subseteq> circline_set l"
    using ex_is_poincare_line_points
    by blast
  then obtain M where *: "unit_disc_fix M" "moebius_pt M u = 0\<^sub>h" "moebius_pt M v \<in> positive_x_axis"
    using ex_unit_disc_fix_to_zero_positive_x_axis[of u v]
    by auto
  moreover
  hence "{0\<^sub>h, moebius_pt M v} \<subseteq> circline_set x_axis"
    unfolding positive_x_axis_def
    by auto
  moreover
  have "moebius_pt M v \<noteq> 0\<^sub>h"
    using \<open>u \<noteq> v\<close> *
    by (metis moebius_pt_neq_I)
  moreover
  have "moebius_pt M v \<noteq> \<infinity>\<^sub>h"
    using \<open>unit_disc_fix M\<close> \<open>v \<in> unit_disc\<close>
    using unit_disc_fix_discI
    by fastforce
  ultimately
  show ?thesis
    using \<open>is_poincare_line l\<close> \<open>{u, v} \<subseteq> circline_set l\<close> \<open>unit_disc_fix M\<close>
    using is_poincare_line_0_real_is_x_axis[of "moebius_circline M l" "moebius_pt M v"]
    by (rule_tac x="M" in exI, force) 
qed

text \<open>When proving facts about h-lines, without loss of generality it can be assumed that h-line is
the x-axis (if the property being proved is invariant under Möbius transformations that fix the
unit disc).\<close>

lemma wlog_line_x_axis:
  assumes is_line: "is_poincare_line H"
  assumes x_axis: "P x_axis"
  assumes preserves: "\<And> M. \<lbrakk>unit_disc_fix M; P (moebius_circline M H)\<rbrakk> \<Longrightarrow> P H"
  shows "P H"
  using assms
  using ex_unit_disc_fix_is_poincare_line_to_x_axis[of H]
  by auto

(* ------------------------------------------------------------------ *)
subsection\<open>Construction of the h-line between the two given points\<close>
(* ------------------------------------------------------------------ *)

text\<open>Next we show how to construct the (unique) h-line between the two given points in the Poincar\'e model\<close>

text\<open>
Geometrically, h-line can be constructed by finding the inverse point of one of the two points and 
by constructing the circle (or line) trough it and the two given points.

Algebraically, for two given points $u$ and $v$ in $\mathbb{C}$, the h-line matrix coefficients can
be $A = i\cdot(u\overline{v}-v\overline{u})$ and $B = i\cdot(v(|u|^2+1) - u(|v|^2+1))$.

We need to extend this to homogenous coordinates. There are several degenerate cases.

 - If $\{z, w\} = \{0_h, \infty_h\}$ then there is no unique h-line (any line trough zero is an h-line).

 - If z and w are mutually inverse, then the construction fails (both geometric and algebraic).

 - If z and w are different points on the unit circle, then the standard construction fails (only geometric).

 - None of this problematic cases occur when z and w are inside the unit disc.

We express the construction algebraically, and construct the Hermitean circline matrix for the two
points given in homogenous coordinates. It works correctly in all cases except when the two points
are the same or are mutually inverse.
\<close>


definition mk_poincare_line_cmat :: "real \<Rightarrow> complex \<Rightarrow> complex_mat" where
  [simp]: "mk_poincare_line_cmat A B = (cor A, B, cnj B, cor A)"

lemma mk_poincare_line_cmat_zero_iff:
  "mk_poincare_line_cmat A B = mat_zero \<longleftrightarrow> A = 0 \<and> B = 0"
  by auto

lemma mk_poincare_line_cmat_hermitean
  [simp]:  "hermitean (mk_poincare_line_cmat A B)"
  by simp

lemma mk_poincare_line_cmat_scale:
  "cor k *\<^sub>s\<^sub>m mk_poincare_line_cmat A B = mk_poincare_line_cmat (k * A) (k * B)"
  by simp

definition poincare_line_cvec_cmat :: "complex_vec \<Rightarrow> complex_vec \<Rightarrow> complex_mat" where
  [simp]: "poincare_line_cvec_cmat z w =
            (let (z1, z2) = z;
                 (w1, w2) = w;
                 nom = w1*cnj w2*(z1*cnj z1 + z2*cnj z2) - z1*cnj z2*(w1*cnj w1 + w2*cnj w2);
                 den = z1*cnj z2*cnj w1*w2 - w1*cnj w2*cnj z1*z2
              in if den \<noteq> 0 then
                    mk_poincare_line_cmat (Re(\<i>*den)) (\<i>*nom)
                 else if z1*cnj z2 \<noteq> 0 then
                    mk_poincare_line_cmat 0 (\<i>*z1*cnj z2)
                 else if w1*cnj w2 \<noteq> 0 then
                    mk_poincare_line_cmat 0 (\<i>*w1*cnj w2)
                 else
                    mk_poincare_line_cmat 0 \<i>)"

lemma poincare_line_cvec_cmat_AeqD:
  assumes "poincare_line_cvec_cmat z w = (A, B, C, D)"
  shows "A = D"
  using assms
  by (cases z, cases w) (auto split: if_split_asm)

lemma poincare_line_cvec_cmat_hermitean [simp]: 
  shows "hermitean (poincare_line_cvec_cmat z w)"
  by (cases z, cases w) (auto split: if_split_asm simp del: mk_poincare_line_cmat_def)

lemma poincare_line_cvec_cmat_nonzero [simp]:
  assumes "z \<noteq> vec_zero" "w \<noteq> vec_zero"
  shows  "poincare_line_cvec_cmat z w \<noteq> mat_zero"
proof-

  obtain z1 z2 w1 w2 where *: "z = (z1, z2)" "w = (w1, w2)"
    by (cases z, cases w, auto)

  let ?den = "z1*cnj z2*cnj w1*w2 - w1*cnj w2*cnj z1*z2"
  show ?thesis
  proof (cases "?den \<noteq> 0")
    case True
    have "is_real (\<i> * ?den)"
      using eq_cnj_iff_real[of "\<i> *?den"]
      by (simp add: field_simps)
    hence "Re (\<i> * ?den) \<noteq> 0"
      using \<open>?den \<noteq> 0\<close>
      by (metis complex_i_not_zero complex_surj mult_eq_0_iff zero_complex.code)
    thus ?thesis
      using * \<open>?den \<noteq> 0\<close>
      by (simp del: mk_poincare_line_cmat_def mat_zero_def add: mk_poincare_line_cmat_zero_iff)
  next
    case False
    thus ?thesis
      using *
      by (simp del: mk_poincare_line_cmat_def mat_zero_def add: mk_poincare_line_cmat_zero_iff)
  qed
qed

lift_definition poincare_line_hcoords_clmat :: "complex_homo_coords \<Rightarrow> complex_homo_coords \<Rightarrow> circline_mat" is poincare_line_cvec_cmat
  using poincare_line_cvec_cmat_hermitean poincare_line_cvec_cmat_nonzero
  by simp

lift_definition poincare_line :: "complex_homo \<Rightarrow> complex_homo \<Rightarrow> circline" is poincare_line_hcoords_clmat
proof transfer
  fix za zb wa wb
  assume "za \<noteq> vec_zero" "zb \<noteq> vec_zero" "wa \<noteq> vec_zero" "wb \<noteq> vec_zero"
  assume "za \<approx>\<^sub>v zb" "wa \<approx>\<^sub>v wb"
  obtain za1 za2 zb1 zb2 wa1 wa2 wb1 wb2 where
  *: "(za1, za2) = za" "(zb1, zb2) = zb"
     "(wa1, wa2) = wa" "(wb1, wb2) = wb"
    by (cases za, cases zb, cases wa, cases wb, auto)
  obtain kz kw where
    **: "kz \<noteq> 0" "kw \<noteq> 0" "zb1 = kz * za1" "zb2 = kz * za2" "wb1 = kw * wa1" "wb2 = kw * wa2"
    using \<open>za \<approx>\<^sub>v zb\<close> \<open>wa \<approx>\<^sub>v wb\<close> *[symmetric]
    by auto

  let ?nom = "\<lambda> z1 z2 w1 w2. w1*cnj w2*(z1*cnj z1 + z2*cnj z2) - z1*cnj z2*(w1*cnj w1 + w2*cnj w2)"
  let ?den = "\<lambda> z1 z2 w1 w2. z1*cnj z2*cnj w1*w2 - w1*cnj w2*cnj z1*z2"

  show "circline_eq_cmat (poincare_line_cvec_cmat za wa)
                         (poincare_line_cvec_cmat zb wb)"
  proof-
    have "\<exists>k. k \<noteq> 0 \<and>
            poincare_line_cvec_cmat (zb1, zb2) (wb1, wb2) = cor k *\<^sub>s\<^sub>m poincare_line_cvec_cmat (za1, za2) (wa1, wa2)"
    proof (cases "?den za1 za2 wa1 wa2 \<noteq> 0")
      case True
      hence "?den zb1 zb2 wb1 wb2 \<noteq> 0"
        using **
        by (simp add: field_simps)

      let ?k = "kz * cnj kz * kw * cnj kw"

      have "?k \<noteq> 0"
        using **
        by simp

      have "is_real ?k"
        using eq_cnj_iff_real[of ?k]
        by auto

      have "cor (Re ?k) = ?k"
        using \<open>is_real ?k\<close>
        using complex_of_real_Re
        by blast

      have "Re ?k \<noteq> 0"
        using \<open>?k \<noteq> 0\<close> \<open>cor (Re ?k) = ?k\<close>
        by (metis of_real_0)

      have arg1: "Re (\<i> * ?den zb1 zb2 wb1 wb2) = Re ?k * Re (\<i> * ?den za1 za2 wa1 wa2)"
        apply (subst **)+
        apply (subst Re_mult_real[symmetric, OF \<open>is_real ?k\<close>])
        apply (rule arg_cong[where f=Re])
        apply (simp add: field_simps)
        done
      have arg2: "\<i> * ?nom zb1 zb2 wb1 wb2 = ?k * \<i> * ?nom za1 za2 wa1 wa2"
        using **
        by (simp add: field_simps)
      have "mk_poincare_line_cmat (Re (\<i>*?den zb1 zb2 wb1 wb2)) (\<i>*?nom zb1 zb2 wb1 wb2) =
            cor (Re ?k) *\<^sub>s\<^sub>m mk_poincare_line_cmat (Re (\<i>*?den za1 za2 wa1 wa2)) (\<i>*?nom za1 za2 wa1 wa2)"
        using \<open>cor (Re ?k) = ?k\<close> \<open>is_real ?k\<close>
        apply (subst mk_poincare_line_cmat_scale)
        apply (subst arg1, subst arg2)
        apply (subst \<open>cor (Re ?k) = ?k\<close>)+
        apply simp
        done
       thus ?thesis
        using \<open>?den za1 za2 wa1 wa2 \<noteq> 0\<close> \<open>?den zb1 zb2 wb1 wb2 \<noteq> 0\<close>
        using \<open>Re ?k \<noteq> 0\<close> \<open>cor (Re ?k) = ?k\<close>
        by (rule_tac x="Re ?k" in exI, simp)
    next
      case False
      hence "?den zb1 zb2 wb1 wb2 = 0"
        using **
        by (simp add: field_simps)
      show ?thesis
      proof (cases "za1*cnj za2 \<noteq> 0")
        case True
        hence "zb1*cnj zb2 \<noteq> 0"
          using **
          by (simp add: field_simps)

        let ?k = "kz * cnj kz"

        have "?k \<noteq> 0" "is_real ?k"
          using **
          using eq_cnj_iff_real[of ?k]
          by auto
        thus ?thesis
          using \<open>za1 * cnj za2 \<noteq> 0\<close> \<open>zb1 * cnj zb2 \<noteq> 0\<close>
          using \<open>\<not> (?den za1 za2 wa1 wa2 \<noteq> 0)\<close> \<open>?den zb1 zb2 wb1 wb2 = 0\<close> **
          by (rule_tac x="Re (kz * cnj kz)" in exI, auto simp add: complex.expand)
      next
        case False
        hence "zb1 * cnj zb2 = 0"
          using **
          by (simp add: field_simps)
        show ?thesis
        proof (cases "wa1 * cnj wa2 \<noteq> 0")
          case True
          hence "wb1*cnj wb2 \<noteq> 0"
            using **
            by (simp add: field_simps)

          let ?k = "kw * cnj kw"

          have "?k \<noteq> 0" "is_real ?k"
            using **
            using eq_cnj_iff_real[of ?k]
            by auto

          thus ?thesis
            using \<open>\<not> (za1 * cnj za2 \<noteq> 0)\<close> 
            using \<open>wa1 * cnj wa2 \<noteq> 0\<close> \<open>wb1 * cnj wb2 \<noteq> 0\<close>
            using \<open>\<not> (?den za1 za2 wa1 wa2 \<noteq> 0)\<close> \<open>?den zb1 zb2 wb1 wb2 = 0\<close> **
            by (rule_tac x="Re (kw * cnj kw)" in exI) 
               (auto simp add: complex.expand)
        next
          case False
          hence "wb1 * cnj wb2 = 0"
            using **
            by (simp add: field_simps)
          thus ?thesis
            using \<open>\<not> (za1 * cnj za2 \<noteq> 0)\<close> \<open>zb1 * cnj zb2 = 0\<close>
            using \<open>\<not> (wa1 * cnj wa2 \<noteq> 0)\<close> \<open>wb1 * cnj wb2 = 0\<close>
            using \<open>\<not> (?den za1 za2 wa1 wa2 \<noteq> 0)\<close> \<open>?den zb1 zb2 wb1 wb2 = 0\<close> **
            by simp
        qed
      qed
    qed
    thus ?thesis
      using *[symmetric]
      by simp
  qed
qed

subsubsection \<open>Correctness of the construction\<close>

text\<open>For finite points, our definition matches the classic algebraic definition for points in
$\mathbb{C}$ (given in ordinary, not homogenous coordinates).\<close>
lemma poincare_line_non_homogenous:
  assumes "u \<noteq> \<infinity>\<^sub>h" "v \<noteq> \<infinity>\<^sub>h" "u \<noteq> v" "u \<noteq> inversion v"
  shows "let u' = to_complex u;  v' = to_complex v;
             A = \<i> * (u' * cnj v' - v' * cnj u');
             B = \<i> * (v' * ((cmod u')\<^sup>2 + 1) - u' * ((cmod v')\<^sup>2 + 1))
          in poincare_line u v = mk_circline A B (cnj B) A"
  using assms
  unfolding unit_disc_def disc_def inversion_def
  apply (simp add: Let_def)
proof (transfer, transfer, safe)
  fix u1 u2 v1 v2
  assume uv: "(u1, u2) \<noteq> vec_zero" "(v1, v2) \<noteq> vec_zero" 
             "\<not> (u1, u2) \<approx>\<^sub>v \<infinity>\<^sub>v" "\<not> (v1, v2) \<approx>\<^sub>v \<infinity>\<^sub>v"            
             "\<not> (u1, u2) \<approx>\<^sub>v (v1, v2)" "\<not> (u1, u2) \<approx>\<^sub>v conjugate_cvec (reciprocal_cvec (v1, v2))"
  let ?u = "to_complex_cvec (u1, u2)" and ?v = "to_complex_cvec (v1, v2)"
  let ?A = "\<i> * (?u * cnj ?v - ?v * cnj ?u)"
  let ?B = "\<i> * (?v * ((cor (cmod ?u))\<^sup>2 + 1) - ?u * ((cor (cmod ?v))\<^sup>2 + 1))"
  let ?C = "- (\<i> * (cnj ?v * ((cor (cmod ?u))\<^sup>2 + 1) - cnj ?u * ((cor (cmod ?v))\<^sup>2 + 1)))"
  let ?D = ?A
  let ?H = "(?A, ?B, ?C, ?D)"


  let ?den = "u1 * cnj u2 * cnj v1 * v2 - v1 * cnj v2 * cnj u1 * u2"

  have "u2 \<noteq> 0" "v2 \<noteq> 0"
    using uv                                                    
    using inf_cvec_z2_zero_iff 
    by blast+

  have "\<not> (u1, u2) \<approx>\<^sub>v (cnj v2, cnj v1)"
    using uv(6)
    by (simp add: vec_cnj_def)
  moreover
  have "(cnj v2, cnj v1) \<noteq> vec_zero"
    using uv(2)
    by auto
  ultimately
  have *: "u1 * cnj v1 \<noteq> u2 * cnj v2" "u1 * v2 \<noteq> u2 * v1" 
    using uv(5) uv(1) uv(2) `u2 \<noteq> 0` `v2 \<noteq> 0`
    using complex_cvec_eq_mix 
    by blast+

  show "circline_eq_cmat (poincare_line_cvec_cmat (u1, u2) (v1, v2))
                         (mk_circline_cmat ?A ?B ?C ?D)"
  proof (cases "?den \<noteq> 0")
    case True

    let ?nom = "v1 * cnj v2 * (u1 * cnj u1 + u2 * cnj u2) - u1 * cnj u2 * (v1 * cnj v1 + v2 * cnj v2)"
    let ?H' = "mk_poincare_line_cmat (Re (\<i> * ?den)) (\<i> * ?nom)"

    have "circline_eq_cmat ?H ?H'"
    proof-
      let ?k = "(u2 * cnj v2) * (v2 * cnj u2)"
      have "is_real ?k"
        using eq_cnj_iff_real 
        by fastforce
      hence "cor (Re ?k) = ?k"
        using complex_of_real_Re 
        by blast

      have "Re (\<i> * ?den) = Re ?k * ?A"
      proof-
        have "?A = cnj ?A"
          by (simp add: field_simps)
        hence "is_real ?A"
          using eq_cnj_iff_real 
          by fastforce
        moreover
        have "\<i> * ?den =  cnj (\<i> * ?den)"
          by (simp add: field_simps)
        hence "is_real (\<i> * ?den)"
          using eq_cnj_iff_real 
          by fastforce
        hence "cor (Re (\<i> * ?den)) = \<i> * ?den"
          using complex_of_real_Re
          by blast
        ultimately
        show ?thesis
          using `cor (Re ?k) = ?k`
          by (simp add: field_simps)
      qed
      
      moreover
      have "\<i> * ?nom = Re ?k  * ?B"
        using `cor (Re ?k) = ?k` `u2 \<noteq>  0` `v2 \<noteq> 0` complex_mult_cnj_cmod[symmetric]
        by (auto simp add: field_simps)
      
      moreover
      have "?k \<noteq> 0"
        using `u2 \<noteq> 0` `v2 \<noteq> 0`
        by simp
      hence "Re ?k \<noteq> 0"
        using `is_real ?k`
        by (metis \<open>cor (Re ?k) = ?k\<close> of_real_0)

      ultimately
      show ?thesis
        by simp (rule_tac x="Re ?k" in exI, simp add: mult.commute)
    qed

    moreover

    have "poincare_line_cvec_cmat (u1, u2) (v1, v2) = ?H'"
      using `?den \<noteq> 0`
      unfolding poincare_line_cvec_cmat_def
      by (simp add: Let_def)

    moreover

    hence "hermitean ?H' \<and> ?H' \<noteq> mat_zero"
      by (metis mk_poincare_line_cmat_hermitean poincare_line_cvec_cmat_nonzero uv(1) uv(2))

    hence "hermitean ?H \<and> ?H \<noteq> mat_zero"
      using `circline_eq_cmat ?H ?H'`
      using circline_eq_cmat_hermitean_nonzero[of ?H' ?H] symp_circline_eq_cmat
      unfolding symp_def
      by metis

    hence "mk_circline_cmat ?A ?B ?C ?D = ?H"
      by simp

    ultimately

    have "circline_eq_cmat (mk_circline_cmat ?A ?B ?C ?D)
                           (poincare_line_cvec_cmat (u1, u2) (v1, v2))"
      by simp
    thus ?thesis
      using symp_circline_eq_cmat
      unfolding symp_def
      by blast
  next
    case False

    let ?d = "v1 * (u1 * cnj u1 / (u2 * cnj u2) + 1) / v2 - u1 * (v1 * cnj v1 / (v2 * cnj v2) + 1) / u2"
    let ?cd = "cnj v1 * (u1 * cnj u1 / (u2 * cnj u2) + 1) / cnj v2 - cnj u1 * (v1 * cnj v1 / (v2 * cnj v2) + 1) / cnj u2"

    have "cnj ?d = ?cd"
      by (simp add: mult.commute)

    let ?d1 = "(v1 / v2) * (cnj u1 / cnj u2) - 1"
    let ?d2 = "u1 / u2 - v1 / v2"

    have **: "?d = ?d1 * ?d2"
      using `\<not> ?den \<noteq> 0` `u2 \<noteq> 0` `v2 \<noteq> 0` 
      by(simp add: field_simps)

    hence "?d \<noteq> 0"
      using `\<not> ?den \<noteq> 0` `u2 \<noteq> 0` `v2 \<noteq> 0` *
      by auto (simp add: field_simps)+

    have "is_real ?d1"
    proof-
      have "cnj ?d1 = ?d1"
        using `\<not> ?den \<noteq> 0` `u2 \<noteq> 0` `v2 \<noteq> 0` *
        by (simp add: field_simps)
      thus ?thesis
        using eq_cnj_iff_real
        by blast
    qed

    show ?thesis
    proof (cases "u1 * cnj u2 \<noteq> 0")
      case True
      let ?nom = "u1 * cnj u2"
      let ?H' = "mk_poincare_line_cmat 0 (\<i> * ?nom)"

      have "circline_eq_cmat ?H ?H'"
      proof-

        let ?k = "(u1 * cnj u2) / ?d"

        have "is_real ?k"
        proof-
          have "is_real ((u1 * cnj u2) / ?d2)"
          proof-
            let ?rhs = "(u2 * cnj u2) / (1 - (v1*u2)/(u1*v2))"

            have 1: "(u1 * cnj u2) / ?d2 = ?rhs"
              using `\<not> ?den \<noteq> 0` `u2 \<noteq> 0` `v2 \<noteq> 0` * `u1 * cnj u2 \<noteq> 0`
              by (simp add: field_simps)
            moreover
            have "cnj ?rhs = ?rhs"
            proof-
              have "cnj (1 - v1 * u2 / (u1 * v2)) = 1 - v1 * u2 / (u1 * v2)"
                using `\<not> ?den \<noteq> 0` `u2 \<noteq> 0` `v2 \<noteq> 0` * `u1 * cnj u2 \<noteq> 0`
                by (simp add: field_simps)
              moreover
              have "cnj (u2 * cnj u2) = u2 * cnj u2"
                by simp
              ultimately
              show ?thesis
                by simp
            qed

            ultimately 

            show ?thesis
              using eq_cnj_iff_real
              by fastforce
          qed

          thus ?thesis
            using ** `is_real ?d1`
            by (metis complex_cnj_divide divide_divide_eq_left' eq_cnj_iff_real)
        qed

        have "?k \<noteq> 0"
          using `?d \<noteq> 0` `u1 * cnj u2 \<noteq> 0`
          by simp

        have "cnj ?k = ?k"
          using `is_real ?k`
          using eq_cnj_iff_real by blast

        have "Re ?k \<noteq> 0"
          using `?k \<noteq> 0` `is_real ?k` 
          by (metis complex.expand zero_complex.simps(1) zero_complex.simps(2))

        have "u1 * cnj u2 = ?k * ?d"
          using `?d \<noteq> 0`
          by simp

        moreover

        hence "cnj u1 * u2 = cnj ?k * cnj ?d"
          by (metis complex_cnj_cnj complex_cnj_mult)
        hence "cnj u1 * u2 = ?k * ?cd"
          using `cnj ?k = ?k` `cnj ?d = ?cd`
          by metis

        ultimately

        show ?thesis
          using `~ ?den \<noteq> 0` `u1 * cnj u2 \<noteq> 0` `u2 \<noteq> 0` `v2 \<noteq> 0` `Re ?k \<noteq> 0` `is_real ?k` `?d \<noteq> 0`
          using complex_mult_cnj_cmod[symmetric, of u1]
          using complex_mult_cnj_cmod[symmetric, of v1]
          using complex_mult_cnj_cmod[symmetric, of u2]
          using complex_mult_cnj_cmod[symmetric, of v2]
          apply (auto simp add: power_divide)
          apply (rule_tac x="Re ?k" in exI)
          apply simp
          apply (simp add: field_simps)
          done
      qed

      moreover

      have "poincare_line_cvec_cmat (u1, u2) (v1, v2) = ?H'"
        using `\<not> ?den \<noteq> 0` `u1 * cnj u2 \<noteq> 0`
        unfolding poincare_line_cvec_cmat_def
        by (simp add: Let_def)

      moreover

      hence "hermitean ?H' \<and> ?H' \<noteq> mat_zero"
        by (metis mk_poincare_line_cmat_hermitean poincare_line_cvec_cmat_nonzero uv(1) uv(2))

      hence "hermitean ?H \<and> ?H \<noteq> mat_zero"
        using `circline_eq_cmat ?H ?H'`
        using circline_eq_cmat_hermitean_nonzero[of ?H' ?H] symp_circline_eq_cmat
        unfolding symp_def
        by metis

      hence "mk_circline_cmat ?A ?B ?C ?D = ?H"
        by simp

      ultimately

      have "circline_eq_cmat (mk_circline_cmat ?A ?B ?C ?D)
                             (poincare_line_cvec_cmat (u1, u2) (v1, v2))"
        by simp
      thus ?thesis
        using symp_circline_eq_cmat
        unfolding symp_def
        by blast
    next
      case  False
      show ?thesis
      proof (cases "v1 * cnj v2 \<noteq> 0")
        case True
        let ?nom = "v1 * cnj v2"
        let ?H' = "mk_poincare_line_cmat 0 (\<i> * ?nom)"

        have "circline_eq_cmat ?H ?H'"
        proof-
          let ?k = "(v1 * cnj v2) / ?d"

          have "is_real ?k"
          proof-
          have "is_real ((v1 * cnj v2) / ?d2)"
          proof-
            let ?rhs = "(v2 * cnj v2) / ((u1*v2)/(u2*v1) - 1)"

            have 1: "(v1 * cnj v2) / ?d2 = ?rhs"
              using `\<not> ?den \<noteq> 0` `u2 \<noteq> 0` `v2 \<noteq> 0` * `v1 * cnj v2 \<noteq> 0`
              by (simp add: field_simps)
            moreover
            have "cnj ?rhs = ?rhs"
            proof-
              have "cnj (u1 * v2 / (u2 * v1) - 1) = u1 * v2 / (u2 * v1) - 1"
                using `\<not> ?den \<noteq> 0` `u2 \<noteq> 0` `v2 \<noteq> 0` * `v1 * cnj v2 \<noteq> 0`
                by (simp add: field_simps)
              moreover                            
              have "cnj (v2 * cnj v2) = v2 * cnj v2"
                by simp
              ultimately
              show ?thesis
                by simp
            qed

            ultimately 

            show ?thesis
              using eq_cnj_iff_real
              by fastforce
          qed

          thus ?thesis
            using ** `is_real ?d1`
            by (metis complex_cnj_divide divide_divide_eq_left' eq_cnj_iff_real)
        qed

        have "?k \<noteq> 0"
          using `?d \<noteq> 0` `v1 * cnj v2 \<noteq> 0`
          by simp

        have "cnj ?k = ?k"
          using `is_real ?k`
          using eq_cnj_iff_real by blast

        have "Re ?k \<noteq> 0"
          using `?k \<noteq> 0` `is_real ?k` 
          by (metis complex.expand zero_complex.simps(1) zero_complex.simps(2))

        have "v1 * cnj v2 = ?k * ?d"
          using `?d \<noteq> 0`
          by simp

        moreover

        hence "cnj v1 * v2 = cnj ?k * cnj ?d"
          by (metis complex_cnj_cnj complex_cnj_mult)
        hence "cnj v1 * v2 = ?k * ?cd"
          using `cnj ?k = ?k` `cnj ?d = ?cd`
          by metis

        ultimately

        show ?thesis
          using `~ ?den \<noteq> 0` `v1 * cnj v2 \<noteq> 0` `u2 \<noteq> 0` `v2 \<noteq> 0` `Re ?k \<noteq> 0` `is_real ?k` `?d \<noteq> 0`
          using complex_mult_cnj_cmod[symmetric, of u1]
          using complex_mult_cnj_cmod[symmetric, of v1]
          using complex_mult_cnj_cmod[symmetric, of u2]
          using complex_mult_cnj_cmod[symmetric, of v2]
          apply (auto simp add: power_divide)
          apply (rule_tac x="Re ?k" in exI)
          apply simp
          apply (simp add: field_simps)
          done
        qed

        moreover

        have "poincare_line_cvec_cmat (u1, u2) (v1, v2) = ?H'"
          using `\<not> ?den \<noteq> 0` `\<not> u1 * cnj u2 \<noteq> 0` `v1 * cnj v2 \<noteq> 0`
          unfolding poincare_line_cvec_cmat_def
          by (simp add: Let_def)

        moreover

        hence "hermitean ?H' \<and> ?H' \<noteq> mat_zero"
          by (metis mk_poincare_line_cmat_hermitean poincare_line_cvec_cmat_nonzero uv(1) uv(2))

        hence "hermitean ?H \<and> ?H \<noteq> mat_zero"
          using `circline_eq_cmat ?H ?H'`
          using circline_eq_cmat_hermitean_nonzero[of ?H' ?H] symp_circline_eq_cmat
          unfolding symp_def
          by metis

        hence "mk_circline_cmat ?A ?B ?C ?D = ?H"
          by simp

        ultimately

        have "circline_eq_cmat (mk_circline_cmat ?A ?B ?C ?D)
                               (poincare_line_cvec_cmat (u1, u2) (v1, v2))"
          by simp
        thus ?thesis
          using symp_circline_eq_cmat
          unfolding symp_def
          by blast
      next
        case False
        hence False
          using `\<not> ?den \<noteq> 0` `\<not> u1 * cnj u2 \<noteq> 0` uv
          by (simp add: \<open>u2 \<noteq> 0\<close> \<open>v2 \<noteq> 0\<close>)
        thus ?thesis
          by simp
      qed
    qed
  qed                    
qed

text\<open>Our construction (in homogenous coordinates) always yields an h-line that contain two starting
points (this also holds for all degenerate cases except when points are the same).\<close>
lemma poincare_line [simp]:
  assumes "z \<noteq> w"
  shows "on_circline (poincare_line z w) z"
        "on_circline (poincare_line z w) w"
proof-
  have "on_circline (poincare_line z w) z \<and> on_circline (poincare_line z w) w"
    using assms
  proof (transfer, transfer)
    fix z w
    assume vz: "z \<noteq> vec_zero" "w \<noteq> vec_zero"
    obtain z1 z2 w1 w2 where
    zw: "(z1, z2) = z" "(w1, w2) = w"
      by (cases z, cases w, auto)

    let ?den = "z1*cnj z2*cnj w1*w2 - w1*cnj w2*cnj z1*z2"
    have *: "cor (Re (\<i> * ?den)) = \<i> * ?den"
    proof-
      have "cnj ?den = -?den"
        by auto
      hence "is_imag ?den"
        using eq_minus_cnj_iff_imag[of ?den]
        by simp
      thus ?thesis
        using complex_of_real_Re[of "\<i> * ?den"]
        by simp
    qed
    show "on_circline_cmat_cvec (poincare_line_cvec_cmat z w) z \<and>
          on_circline_cmat_cvec (poincare_line_cvec_cmat z w) w"
      unfolding poincare_line_cvec_cmat_def mk_poincare_line_cmat_def
      apply (subst zw[symmetric])+
      unfolding Let_def prod.case
      apply (subst *)+
      by (auto simp add: vec_cnj_def field_simps)
  qed
  thus "on_circline (poincare_line z w) z" "on_circline (poincare_line z w) w"
    by auto
qed

lemma poincare_line_circline_set [simp]:
  assumes "z \<noteq> w"
  shows "z \<in> circline_set (poincare_line z w)"
        "w \<in> circline_set (poincare_line z w)"
  using assms
  by (auto simp add: circline_set_def)

text\<open>When the points are different, the constructed line matrix always has a negative determinant\<close>
lemma poincare_line_type:
  assumes "z \<noteq> w"
  shows "circline_type (poincare_line z w) = -1"
proof-
  have "\<exists> a b. a \<noteq> b \<and> {a, b} \<subseteq> circline_set (poincare_line z w)"
    using poincare_line[of z w] assms
    unfolding circline_set_def
    by (rule_tac x=z in exI, rule_tac x=w in exI, simp)
  thus ?thesis
    using circline_type[of "poincare_line z w"]
    using circline_type_pos_card_eq0[of "poincare_line z w"]
    using circline_type_zero_card_eq1[of "poincare_line z w"]
    by auto
qed

text\<open>The constructed line is an h-line in the Poincar\'e model (in all cases when the two points are
different)\<close>
lemma is_poincare_line_poincare_line [simp]:
  assumes "z \<noteq> w"
  shows "is_poincare_line (poincare_line z w)"
  using poincare_line_type[of z w, OF assms]
proof (transfer, transfer)
  fix z w
  assume vz: "z \<noteq> vec_zero" "w \<noteq> vec_zero"
  obtain A B C D where *: "poincare_line_cvec_cmat z w = (A, B, C, D)"
    by (cases "poincare_line_cvec_cmat z w") auto
  assume "circline_type_cmat (poincare_line_cvec_cmat z w) = - 1"
  thus "is_poincare_line_cmat (poincare_line_cvec_cmat z w)"
    using vz *
    using poincare_line_cvec_cmat_hermitean[of z w]
    using poincare_line_cvec_cmat_nonzero[of z w]
    using poincare_line_cvec_cmat_AeqD[of z w A B C D]
    using hermitean_elems[of A B C D]
    using cmod_power2[of D] cmod_power2[of C]
    unfolding is_poincare_line_cmat_def
    by (simp del: poincare_line_cvec_cmat_def add: sgn_1_neg power2_eq_square)
qed

text \<open>When the points are different, the constructed h-line between two points also contains their inverses\<close>
lemma poincare_line_inversion:
  assumes "z \<noteq> w"
  shows "on_circline (poincare_line z w) (inversion z)"
        "on_circline (poincare_line z w) (inversion w)"
  using assms
  using is_poincare_line_poincare_line[OF \<open>z \<noteq> w\<close>]
  using is_poincare_line_inverse_point
  unfolding circline_set_def
  by auto

text \<open>When the points are different, the onstructed h-line between two points contains the inverse of its every point\<close>
lemma poincare_line_inversion_full:
  assumes "u \<noteq> v"
  assumes "on_circline (poincare_line u v) x"
  shows "on_circline (poincare_line u v) (inversion x)"
  using is_poincare_line_inverse_point[of "poincare_line u v" x]
  using is_poincare_line_poincare_line[OF `u \<noteq> v`] assms
  unfolding circline_set_def
  by simp

subsubsection \<open>Existence of h-lines\<close>

text\<open>There is an h-line trough every point in the Poincar\'e model\<close>
lemma ex_poincare_line_one_point:
  shows "\<exists> l. is_poincare_line l \<and> z \<in> circline_set l"
proof (cases "z = 0\<^sub>h")
  case True
  thus ?thesis
    by (rule_tac x="x_axis" in exI) simp
next
  case False
  thus ?thesis
    by (rule_tac x="poincare_line 0\<^sub>h z" in exI) auto
qed

lemma poincare_collinear_singleton [simp]:
  assumes "u \<in> unit_disc"
  shows "poincare_collinear {u}"
  using assms
  using ex_poincare_line_one_point[of u]
  by (auto simp add: poincare_collinear_def)

text\<open>There is an h-line trough every two points in the Poincar\'e model\<close>
lemma ex_poincare_line_two_points:
  assumes "z \<noteq> w"
  shows "\<exists> l. is_poincare_line l \<and> z \<in> circline_set l \<and> w \<in> circline_set l"
  using assms
  by (rule_tac x="poincare_line z w" in exI, simp)

lemma poincare_collinear_doubleton [simp]:
  assumes "u \<in> unit_disc" "v \<in> unit_disc"
  shows "poincare_collinear {u, v}"
  using assms
  using ex_poincare_line_one_point[of u]
  using ex_poincare_line_two_points[of u v]
  by (cases "u = v") (simp_all add: poincare_collinear_def)


subsubsection \<open>Uniqueness of h-lines\<close>

text \<open>The only h-line between two points is the one obtained by the line-construction.\<close> 
text \<open>First we show this only for two different points inside the disc.\<close>
lemma unique_poincare_line:
  assumes in_disc: "u \<noteq> v" "u \<in> unit_disc" "v \<in> unit_disc"
  assumes on_l: "u \<in> circline_set l" "v \<in> circline_set l" "is_poincare_line l"
  shows "l = poincare_line u v"
  using assms
  using unique_is_poincare_line[of u v l "poincare_line u v"]
  unfolding circline_set_def
  by auto

text\<open>The assumption that the points are inside the disc can be relaxed.\<close>
lemma unique_poincare_line_general:
  assumes in_disc: "u \<noteq> v" "u \<noteq> inversion v"
  assumes on_l: "u \<in> circline_set l" "v \<in> circline_set l" "is_poincare_line l"
  shows "l = poincare_line u v"
  using assms
  using unique_is_poincare_line_general[of u v l "poincare_line u v"]
  unfolding circline_set_def
  by auto

text\<open>The explicit line construction enables us to prove that there exists a unique h-line through any
given two h-points (uniqueness part was already shown earlier).\<close>
text \<open>First we show this only for two different points inside the disc.\<close>
lemma ex1_poincare_line:
  assumes "u \<noteq> v" "u \<in> unit_disc" "v \<in> unit_disc"
  shows "\<exists>! l. is_poincare_line l \<and> u \<in> circline_set l \<and> v \<in> circline_set l"
proof (rule ex1I)
  let ?l = "poincare_line u v"
  show "is_poincare_line ?l \<and> u \<in> circline_set ?l \<and> v \<in> circline_set ?l"
    using assms
    unfolding circline_set_def
    by auto
next
  fix l
  assume "is_poincare_line l \<and> u \<in> circline_set l \<and> v \<in> circline_set l"
  thus "l = poincare_line u v"
    using unique_poincare_line assms
    by auto
qed

text \<open>The assumption that the points are in the disc can be relaxed.\<close>
lemma ex1_poincare_line_general:
  assumes "u \<noteq> v" "u \<noteq> inversion v"
  shows "\<exists>! l. is_poincare_line l \<and> u \<in> circline_set l \<and> v \<in> circline_set l"
proof (rule ex1I)
  let ?l = "poincare_line u v"
  show "is_poincare_line ?l \<and> u \<in> circline_set ?l \<and> v \<in> circline_set ?l"
    using assms
    unfolding circline_set_def
    by auto
next
  fix l
  assume "is_poincare_line l \<and> u \<in> circline_set l \<and> v \<in> circline_set l"
  thus "l = poincare_line u v"
    using unique_poincare_line_general assms
    by auto
qed

subsubsection \<open>Some consequences of line uniqueness\<close>

text\<open>H-line $uv$ is the same as the h-line $vu$.\<close>
lemma poincare_line_sym:
  assumes "u \<in> unit_disc" "v \<in> unit_disc" "u \<noteq> v"
  shows "poincare_line u v = poincare_line v u"
  using assms
  using unique_poincare_line[of u v "poincare_line v u"]
  by simp

lemma poincare_line_sym_general:
  assumes "u \<noteq> v" "u \<noteq> inversion v"
  shows "poincare_line u v = poincare_line v u"
  using assms
  using unique_poincare_line_general[of u v "poincare_line v u"]
  by simp

text\<open>Each h-line is the h-line constructed out of its two arbitrary different points.\<close>
lemma ex_poincare_line_points:
  assumes "is_poincare_line H"
  shows "\<exists> u v. u \<in> unit_disc \<and> v \<in> unit_disc \<and> u \<noteq> v \<and> H = poincare_line u v"
  using assms
  using ex_is_poincare_line_points
  using unique_poincare_line[where l=H]
  by fastforce

text\<open>If an h-line contains two different points on x-axis/y-axis then it is the x-axis/y-axis.\<close>
lemma poincare_line_0_real_is_x_axis:
  assumes "x \<in> circline_set x_axis" "x \<noteq> 0\<^sub>h" "x \<noteq> \<infinity>\<^sub>h"
  shows "poincare_line 0\<^sub>h x = x_axis"
  using assms
  using is_poincare_line_0_real_is_x_axis[of "poincare_line 0\<^sub>h x" x]
  by auto

lemma poincare_line_0_imag_is_y_axis:
  assumes "y \<in> circline_set y_axis" "y \<noteq> 0\<^sub>h" "y \<noteq> \<infinity>\<^sub>h"
  shows "poincare_line 0\<^sub>h y = y_axis"
  using assms
  using is_poincare_line_0_imag_is_y_axis[of "poincare_line 0\<^sub>h y" y]
  by auto

lemma poincare_line_x_axis:
  assumes "x \<in> unit_disc" "y \<in> unit_disc" "x \<in> circline_set x_axis" "y \<in> circline_set x_axis" "x \<noteq> y"
  shows "poincare_line x y = x_axis"
  using assms
  using unique_poincare_line
  by auto

lemma poincare_line_minus_one_one [simp]: 
  shows "poincare_line (of_complex (-1)) (of_complex 1) = x_axis"
proof-
  have "0\<^sub>h \<in> circline_set (poincare_line (of_complex (-1)) (of_complex 1))"
    unfolding circline_set_def
    by simp (transfer, transfer,  simp add: vec_cnj_def)
  hence "poincare_line 0\<^sub>h (of_complex 1) = poincare_line (of_complex (-1)) (of_complex 1)"
    by (metis is_poincare_line_poincare_line is_poincare_line_trough_zero_trough_infty not_zero_on_unit_circle of_complex_inj of_complex_one one_neq_neg_one one_on_unit_circle poincare_line_0_real_is_x_axis poincare_line_circline_set(2) reciprocal_involution reciprocal_one reciprocal_zero unique_circline_01inf')
  thus ?thesis
    using poincare_line_0_real_is_x_axis[of "of_complex 1"]
    by auto
qed

subsubsection \<open>Transformations of constructed lines\<close>

text\<open>Unit dics preserving Möbius transformations preserve the h-line construction\<close>
lemma unit_disc_fix_preserve_poincare_line [simp]:
  assumes "unit_disc_fix M" "u \<in> unit_disc" "v \<in> unit_disc" "u \<noteq> v"
  shows "poincare_line (moebius_pt M u) (moebius_pt M v) = moebius_circline M (poincare_line u v)"
proof (rule unique_poincare_line[symmetric])
  show "moebius_pt M u \<noteq> moebius_pt M v"
    using \<open>u \<noteq> v\<close> 
    by auto
next
  show "moebius_pt M u \<in> circline_set (moebius_circline M (poincare_line u v))"
       "moebius_pt M v \<in> circline_set (moebius_circline M (poincare_line u v))"
    unfolding circline_set_def
    using moebius_circline[of M "poincare_line u v"] \<open>u \<noteq> v\<close>
    by auto
next
  from assms(1) have "unit_circle_fix M"
    by simp
  thus "is_poincare_line (moebius_circline M (poincare_line u v))"
    using unit_circle_fix_preserve_is_poincare_line assms
    by auto
next
  show "moebius_pt M u \<in> unit_disc" "moebius_pt M v \<in> unit_disc"
    using assms(2-3) unit_disc_fix_iff[OF assms(1)]
    by auto
qed

text\<open>Conjugate preserve the h-line construction\<close>
lemma conjugate_preserve_poincare_line [simp]:
  assumes "u \<in> unit_disc" "v \<in> unit_disc" "u \<noteq> v"
  shows "poincare_line (conjugate u) (conjugate v) = conjugate_circline (poincare_line u v)"
proof-
  have "conjugate u \<noteq> conjugate v"
    using \<open>u \<noteq> v\<close>
    by (auto simp add: conjugate_inj)
  moreover
  have "conjugate u \<in> unit_disc" "conjugate v \<in> unit_disc"
    using assms
    by auto
  moreover
  have "conjugate u \<in> circline_set (conjugate_circline (poincare_line u v))"
       "conjugate v \<in> circline_set (conjugate_circline (poincare_line u v))"
    using \<open>u \<noteq> v\<close>
    by simp_all
  moreover
  have "is_poincare_line (conjugate_circline (poincare_line u v))"
    using is_poincare_line_poincare_line[OF \<open>u \<noteq> v\<close>]
    by simp
  ultimately
  show ?thesis
    using unique_poincare_line[of "conjugate u" "conjugate v" "conjugate_circline (poincare_line u v)"]
    by simp
qed

subsubsection \<open>Collinear points and h-lines\<close>

lemma poincare_collinear3_poincare_line_general:
  assumes "poincare_collinear {a, a1, a2}" "a1 \<noteq> a2" "a1 \<noteq> inversion a2"
  shows "a \<in> circline_set (poincare_line a1 a2)"
  using assms
  using poincare_collinear_def unique_poincare_line_general
  by auto

lemma poincare_line_poincare_collinear3_general:
  assumes "a \<in> circline_set (poincare_line a1 a2)" "a1 \<noteq> a2"
  shows "poincare_collinear {a, a1, a2}"
  using assms
  unfolding poincare_collinear_def
  by (rule_tac x="poincare_line a1 a2" in exI, simp)
  

lemma poincare_collinear3_poincare_lines_equal_general:
  assumes "poincare_collinear {a, a1, a2}" "a \<noteq> a1" "a \<noteq> a2" "a \<noteq> inversion a1" "a \<noteq> inversion a2"
  shows "poincare_line a a1 = poincare_line a a2"
  using assms
  using unique_poincare_line_general[of a a2 "poincare_line a a1"]
  by (simp add: insert_commute poincare_collinear3_poincare_line_general)

subsubsection \<open>Points collinear with @{term "0\<^sub>h"}\<close>

lemma poincare_collinear_zero_iff:
  assumes "of_complex y' \<in> unit_disc" and "of_complex z' \<in> unit_disc" and
          "y' \<noteq> z'" and "y' \<noteq> 0" and "z' \<noteq> 0"
  shows "poincare_collinear {0\<^sub>h, of_complex y', of_complex z'} \<longleftrightarrow>
         y'*cnj z' = cnj y'*z'" (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  have "of_complex y' \<noteq> of_complex z'"
    using assms
    using of_complex_inj
    by blast
  show ?thesis
  proof
    assume ?lhs
    hence "0\<^sub>h \<in> circline_set (poincare_line (of_complex y') (of_complex z'))"
      using unique_poincare_line[of "of_complex y'" "of_complex z'"]
      using assms \<open>of_complex y' \<noteq> of_complex z'\<close>
      unfolding poincare_collinear_def
      by auto
    moreover
    let ?mix = "y' * cnj z' - cnj y' * z'"
    have "is_real (\<i> * ?mix)"
      using eq_cnj_iff_real[of ?mix]
      by auto
    hence "y' * cnj z' = cnj y' * z' \<longleftrightarrow> Re (\<i> * ?mix) = 0"
      using complex.expand[of "\<i> * ?mix" 0]
      by (metis complex_i_not_zero eq_iff_diff_eq_0 mult_eq_0_iff zero_complex.simps(1) zero_complex.simps(2))
    ultimately
    show ?rhs
      using \<open>y' \<noteq> z'\<close> \<open>y' \<noteq> 0\<close> \<open>z' \<noteq> 0\<close>
      unfolding circline_set_def
      by simp (transfer, transfer, auto simp add: vec_cnj_def split: if_split_asm, metis Re_complex_of_real Re_mult_real Im_complex_of_real)
  next
    assume ?rhs
    thus ?lhs
      using assms \<open>of_complex y' \<noteq> of_complex z'\<close>
      unfolding poincare_collinear_def
      unfolding circline_set_def
      apply (rule_tac x="poincare_line (of_complex y') (of_complex z')" in exI)
      apply auto
      apply (transfer, transfer, simp add: vec_cnj_def)
      done
  qed
qed

lemma poincare_collinear_zero_polar_form:
  assumes "poincare_collinear {0\<^sub>h, of_complex x, of_complex y}" and
          "x \<noteq> 0" and "y \<noteq> 0" and "of_complex x \<in> unit_disc" and "of_complex y \<in> unit_disc"
  shows "\<exists> \<phi> rx ry. x = cor rx * cis \<phi> \<and> y = cor ry * cis \<phi> \<and> rx \<noteq> 0 \<and> ry \<noteq> 0"
proof-
  from \<open>x \<noteq> 0\<close> \<open>y \<noteq> 0\<close> obtain \<phi> \<phi>' rx ry where
    polar: "x = cor rx * cis \<phi>" "y = cor ry * cis \<phi>'" and  "\<phi> = arg x" "\<phi>' = arg y"
    by (metis cmod_cis)
  hence "rx \<noteq> 0" "ry \<noteq> 0"
    using \<open>x \<noteq> 0\<close> \<open>y \<noteq> 0\<close>
    by auto
  have "of_complex y \<in> circline_set (poincare_line 0\<^sub>h (of_complex x))"
    using assms
    using unique_poincare_line[of "0\<^sub>h" "of_complex x"]
    unfolding poincare_collinear_def
    unfolding circline_set_def
    using of_complex_zero_iff
    by fastforce
  hence "cnj x * y = x * cnj y"
    using \<open>x \<noteq> 0\<close> \<open>y \<noteq> 0\<close>
    unfolding circline_set_def
    by simp (transfer, transfer, simp add: vec_cnj_def field_simps)
  hence "cis(\<phi>' - \<phi>) = cis(\<phi> - \<phi>')"
    using polar \<open>rx \<noteq> 0\<close> \<open>ry \<noteq> 0\<close>
    by (simp add: cis_mult)
  hence "sin (\<phi>' - \<phi>) = 0"
    using cis_diff_cis_opposite[of "\<phi>' - \<phi>"]
    by simp
  then obtain k :: int where "\<phi>' - \<phi> = k * pi"
    using sin_zero_iff_int2[of "\<phi>' - \<phi>"]
    by auto
  hence *: "\<phi>' = \<phi> + k * pi"
    by simp
  show ?thesis
  proof (cases "even k")
    case True
    then obtain k' where "k = 2*k'"
      using evenE by blast
    hence "cis \<phi> = cis \<phi>'"
      using * cos_periodic_int sin_periodic_int
      by (simp add: cis.ctr field_simps)
    thus ?thesis
      using polar \<open>rx \<noteq> 0\<close> \<open>ry \<noteq> 0\<close>
      by (rule_tac x=\<phi> in exI, rule_tac x=rx in exI, rule_tac x=ry in exI) simp
  next
    case False
    then obtain k' where "k = 2*k' + 1"
      using oddE by blast
    hence "cis \<phi> = - cis \<phi>'"
      using * cos_periodic_int sin_periodic_int
      by (simp add: cis.ctr complex_minus field_simps)
    thus ?thesis
      using polar \<open>rx \<noteq> 0\<close> \<open>ry \<noteq> 0\<close>
      by (rule_tac x=\<phi> in exI, rule_tac x=rx in exI, rule_tac x="-ry" in exI) simp
  qed
qed

end
