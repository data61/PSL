(* -------------------------------------------------------------------------- *)
section \<open>Möbius transformations\<close>
(* -------------------------------------------------------------------------- *)

text \<open>Möbius transformations (also called homographic, linear fractional, or bilinear
transformations) are the fundamental transformations of the extended complex plane. Here they are
introduced algebraically. Each transformation is represented by a regular (non-singular,
non-degenerate) $2\times 2$ matrix that acts linearly on homogeneous coordinates. As proportional
homogeneous coordinates represent same points of $\mathbb{\overline{C}}$, proportional matrices will
represent the same Möbius transformation.\<close>

theory Moebius
imports Homogeneous_Coordinates
begin

(* -------------------------------------------------------------------------- *)
subsection \<open>Definition of Möbius transformations\<close>
(* -------------------------------------------------------------------------- *)

typedef moebius_mat = "{M::complex_mat. mat_det M \<noteq> 0}"
  by (rule_tac x="eye" in exI, simp)

setup_lifting type_definition_moebius_mat

definition moebius_cmat_eq :: "complex_mat \<Rightarrow> complex_mat \<Rightarrow> bool" where                     
  [simp]: "moebius_cmat_eq A B \<longleftrightarrow>  (\<exists> k::complex. k \<noteq> 0 \<and> B = k *\<^sub>s\<^sub>m A)"

lift_definition moebius_mat_eq :: "moebius_mat \<Rightarrow> moebius_mat \<Rightarrow> bool" is moebius_cmat_eq
  done

lemma moebius_mat_eq_refl [simp]: 
  shows "moebius_mat_eq x x"
  by transfer simp

quotient_type moebius = moebius_mat / moebius_mat_eq
proof (rule equivpI)
  show "reflp moebius_mat_eq"
    unfolding reflp_def
    by transfer auto
next
  show "symp moebius_mat_eq"
    unfolding symp_def
    by transfer (auto simp add: symp_def, rule_tac x="1/k" in exI, simp)
next
  show "transp moebius_mat_eq"
    unfolding transp_def
    by transfer (auto simp add: transp_def, rule_tac x="ka*k" in exI, simp)
qed

definition mk_moebius_cmat :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex_mat" where
 [simp]: "mk_moebius_cmat a b c d =
           (let M = (a, b, c, d)
             in if mat_det M \<noteq> 0 then
                M
             else
                eye)"

lift_definition mk_moebius_mat :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> moebius_mat" is mk_moebius_cmat
  by simp

lift_definition mk_moebius :: "complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> complex \<Rightarrow> moebius" is mk_moebius_mat
  done

lemma ex_mk_moebius:
  shows "\<exists> a b c d. M = mk_moebius a b c d \<and> mat_det (a, b, c, d) \<noteq> 0"
proof (transfer, transfer)
  fix M :: complex_mat
  assume "mat_det M \<noteq> 0"
  obtain a b c d where "M = (a, b, c, d)"
    by (cases M, auto)
  hence "moebius_cmat_eq M (mk_moebius_cmat a b c d) \<and> mat_det (a, b, c, d) \<noteq> 0"
    using \<open>mat_det M \<noteq> 0\<close>
    by auto (rule_tac x=1 in exI, simp)
  thus "\<exists>a b c d. moebius_cmat_eq M (mk_moebius_cmat a b c d) \<and> mat_det (a, b, c, d) \<noteq> 0"
    by blast
qed

(* -------------------------------------------------------------------------- *)
subsection \<open>Action on points\<close>
(* -------------------------------------------------------------------------- *)

text \<open>Möbius transformations are given as the action of Möbius group on the points of the
extended complex plane (in homogeneous coordinates).\<close>

definition moebius_pt_cmat_cvec :: "complex_mat \<Rightarrow> complex_vec \<Rightarrow> complex_vec" where
   [simp]: "moebius_pt_cmat_cvec M z = M *\<^sub>m\<^sub>v z"

lift_definition moebius_pt_mmat_hcoords :: "moebius_mat \<Rightarrow> complex_homo_coords \<Rightarrow> complex_homo_coords" is moebius_pt_cmat_cvec
  by auto algebra+

lift_definition moebius_pt :: "moebius \<Rightarrow> complex_homo \<Rightarrow> complex_homo" is moebius_pt_mmat_hcoords
proof transfer
  fix M M' x x'
  assume "moebius_cmat_eq M M'" "x \<approx>\<^sub>v x'"
  thus "moebius_pt_cmat_cvec M x \<approx>\<^sub>v moebius_pt_cmat_cvec M' x'"
    by (cases "M", cases "x", auto simp add: field_simps) (rule_tac x="k*ka" in exI, simp)
qed

lemma bij_moebius_pt [simp]:
  shows "bij (moebius_pt M)"
  unfolding bij_def inj_on_def surj_def
proof safe
  fix x y
  assume "moebius_pt M x = moebius_pt M y"
  thus "x = y"
  proof (transfer, transfer)
    fix M x y
    assume "mat_det M \<noteq> 0" "moebius_pt_cmat_cvec M x \<approx>\<^sub>v moebius_pt_cmat_cvec M y"
    thus "x \<approx>\<^sub>v y"
      using mult_sv_mv[of _ M x] mult_mv_inv[of _ M]
      unfolding moebius_pt_cmat_cvec_def
      by (metis complex_cvec_eq_def)
  qed
next
  fix y
  show "\<exists>x. y = moebius_pt M x"
  proof (transfer, transfer)
    fix y :: complex_vec and M :: complex_mat
    assume *: "y \<noteq> vec_zero" "mat_det M \<noteq> 0"
    let ?iM = "mat_inv M"
    let ?x = "?iM *\<^sub>m\<^sub>v y"
    have "?x \<noteq> vec_zero"
      using *
      by (metis mat_det_mult mat_eye_r mat_inv_r mult_cancel_right1 mult_mv_nonzero)
    moreover
    have "y \<approx>\<^sub>v moebius_pt_cmat_cvec M ?x"
      by (simp del: eye_def add: mat_inv_r[OF \<open>mat_det M \<noteq> 0\<close>])
    ultimately
    show "\<exists>x\<in>{v. v \<noteq> vec_zero}. y \<approx>\<^sub>v moebius_pt_cmat_cvec M x"
      by (rule_tac x="?x" in bexI, simp_all)
  qed
qed

lemma moebius_pt_eq_I:                                          
  assumes "moebius_pt M z1 = moebius_pt M z2"
  shows "z1 = z2"
  using assms
  using bij_moebius_pt[of M]
  unfolding bij_def inj_on_def
  by blast

lemma moebius_pt_neq_I [simp]:
  assumes "z1 \<noteq> z2"
  shows "moebius_pt M z1 \<noteq> moebius_pt M z2"
  using assms
  by (auto simp add: moebius_pt_eq_I)

definition is_moebius :: "(complex_homo \<Rightarrow> complex_homo) \<Rightarrow> bool" where
  "is_moebius f \<longleftrightarrow> (\<exists> M. f = moebius_pt M)"

text \<open>In the classic literature Möbius transformations are often expressed in the form
$\frac{az+b}{cz+d}$. The following lemma shows that when restricted to finite points, the action
of Möbius transformations is bilinear.\<close>

lemma moebius_pt_bilinear:
  assumes "mat_det (a, b, c, d) \<noteq> 0"
  shows "moebius_pt (mk_moebius a b c d) z =
            (if z \<noteq> \<infinity>\<^sub>h then
                 ((of_complex a) *\<^sub>h z +\<^sub>h (of_complex b)) :\<^sub>h
                 ((of_complex c) *\<^sub>h z +\<^sub>h (of_complex d))
             else
                 (of_complex a) :\<^sub>h
                 (of_complex c))"
  unfolding divide_def
  using assms
proof (transfer, transfer)
  fix a b c d :: complex and z :: complex_vec
  obtain z1 z2 where zz: "z = (z1, z2)"
    by (cases z, auto)
  assume *: "mat_det (a, b, c, d) \<noteq> 0" "z \<noteq> vec_zero"
  let ?oc = "of_complex_cvec"
  show "moebius_pt_cmat_cvec (mk_moebius_cmat a b c d) z \<approx>\<^sub>v
       (if \<not> z \<approx>\<^sub>v \<infinity>\<^sub>v
        then (?oc a *\<^sub>v z +\<^sub>v ?oc b) *\<^sub>v
             reciprocal_cvec (?oc c *\<^sub>v z +\<^sub>v ?oc d)
        else ?oc a *\<^sub>v
             reciprocal_cvec (?oc c))"
  proof (cases "z \<approx>\<^sub>v \<infinity>\<^sub>v")
    case True
    thus ?thesis
      using zz *
      by auto
  next
    case False
    hence "z2 \<noteq> 0"
      using zz inf_cvec_z2_zero_iff \<open>z \<noteq> vec_zero\<close>
      by auto
    thus ?thesis
      using zz * False
      using regular_homogenous_system[of a b c d z1 z2]
      by auto
  qed
qed

(* -------------------------------------------------------------------------- *)
subsection \<open>Möbius group\<close>
(* -------------------------------------------------------------------------- *)

text \<open>Möbius elements form a group under composition. This group is called the \emph{projective
general linear group} and denoted by $PGL(2, \mathbb{C})$ (the group $SGL(2, \mathbb{C})$ containing elements
with the determinant $1$ can also be considered).\<close>

text \<open>Identity Möbius transformation is represented by the identity matrix.\<close>

definition id_moebius_cmat :: "complex_mat" where
  [simp]: "id_moebius_cmat = eye"

lift_definition id_moebius_mmat :: "moebius_mat" is id_moebius_cmat
  by simp

lift_definition id_moebius :: "moebius" is id_moebius_mmat
  done

lemma moebius_pt_moebius_id [simp]:
  shows "moebius_pt id_moebius = id"
  unfolding id_def
  apply (rule ext, transfer, transfer)
  using eye_mv_l
  by simp

lemma mk_moeibus_id [simp]:
  shows "mk_moebius a 0 0 a = id_moebius"
  by (transfer, transfer, simp)

text \<open>The inverse Möbius transformation is obtained by taking the inverse representative matrix.\<close>

definition moebius_inv_cmat :: "complex_mat \<Rightarrow> complex_mat" where
  [simp]: "moebius_inv_cmat M = mat_inv M"

lift_definition moebius_inv_mmat :: "moebius_mat \<Rightarrow> moebius_mat" is moebius_inv_cmat
  by (simp add: mat_det_inv)

lift_definition moebius_inv :: "moebius \<Rightarrow> moebius" is "moebius_inv_mmat"
proof (transfer)
  fix x y
  assume "moebius_cmat_eq x y"
  thus "moebius_cmat_eq (moebius_inv_cmat x) (moebius_inv_cmat y)"
    by (auto simp add: mat_inv_mult_sm) (rule_tac x="1/k" in exI, simp)
qed

lemma moebius_inv:
  shows "moebius_pt (moebius_inv M) = inv (moebius_pt M)"
proof (rule inv_equality[symmetric])
  fix x
  show "moebius_pt (moebius_inv M) (moebius_pt M x) = x"
  proof (transfer, transfer)
    fix M::complex_mat and x::complex_vec
    assume "mat_det M \<noteq> 0" "x \<noteq> vec_zero"
    show "moebius_pt_cmat_cvec (moebius_inv_cmat M) (moebius_pt_cmat_cvec M x) \<approx>\<^sub>v x"
      using eye_mv_l
      by (simp add: mat_inv_l[OF \<open>mat_det M \<noteq> 0\<close>])
  qed
next
  fix y
  show "moebius_pt M (moebius_pt (moebius_inv M) y) = y"
  proof (transfer, transfer)
    fix M::complex_mat and y::complex_vec
    assume "mat_det M \<noteq> 0" "y \<noteq> vec_zero"
    show "moebius_pt_cmat_cvec M (moebius_pt_cmat_cvec (moebius_inv_cmat M) y) \<approx>\<^sub>v y"
      using eye_mv_l
      by (simp add: mat_inv_r[OF \<open>mat_det M \<noteq> 0\<close>])
  qed
qed

lemma is_moebius_inv [simp]:
  assumes "is_moebius m"
  shows "is_moebius (inv m)"
  using assms
  using moebius_inv
  unfolding is_moebius_def
  by metis

lemma moebius_inv_mk_moebus [simp]:
  assumes "mat_det (a, b, c, d) \<noteq> 0"
  shows "moebius_inv (mk_moebius a b c d) =
         mk_moebius (d/(a*d-b*c)) (-b/(a*d-b*c)) (-c/(a*d-b*c)) (a/(a*d-b*c))"
  using assms
  by (transfer, transfer) (auto, rule_tac x=1 in exI, simp_all add: field_simps)

text \<open>Composition of Möbius elements is obtained by multiplying their representing matrices.\<close>

definition moebius_comp_cmat :: "complex_mat \<Rightarrow> complex_mat \<Rightarrow> complex_mat" where
  [simp]: "moebius_comp_cmat M1 M2 = M1 *\<^sub>m\<^sub>m M2"

lift_definition moebius_comp_mmat :: "moebius_mat \<Rightarrow> moebius_mat \<Rightarrow> moebius_mat" is moebius_comp_cmat
  by simp

lift_definition moebius_comp :: "moebius \<Rightarrow> moebius \<Rightarrow> moebius" is moebius_comp_mmat
  by transfer (simp, (erule exE)+, rule_tac x="k*ka" in exI, simp add: field_simps)

lemma moebius_comp: 
  shows "moebius_pt (moebius_comp M1 M2) = moebius_pt M1 \<circ> moebius_pt M2"
  unfolding comp_def
  by (rule ext, transfer, transfer, simp)

lemma moebius_pt_comp [simp]:
  shows "moebius_pt (moebius_comp M1 M2) z = moebius_pt M1 (moebius_pt M2 z)"
  by (auto simp add: moebius_comp)

lemma is_moebius_comp [simp]:
  assumes "is_moebius m1" and "is_moebius m2"
  shows "is_moebius (m1 \<circ> m2)"
  using assms
  unfolding is_moebius_def
  using moebius_comp
  by metis

lemma moebius_comp_mk_moebius [simp]:
  assumes "mat_det (a, b, c, d) \<noteq> 0" and "mat_det (a', b', c', d') \<noteq> 0"
  shows "moebius_comp (mk_moebius a b c d) (mk_moebius a' b' c' d') =
           mk_moebius (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d')"
  using mat_det_mult[of "(a, b, c, d)" "(a', b', c', d')"]
  using assms
  by (transfer, transfer) (auto, rule_tac x=1 in exI, simp)

instantiation moebius :: group_add
begin
definition plus_moebius :: "moebius \<Rightarrow> moebius \<Rightarrow> moebius" where
  [simp]: "plus_moebius = moebius_comp"

definition uminus_moebius :: "moebius \<Rightarrow> moebius" where
  [simp]: "uminus_moebius = moebius_inv"

definition zero_moebius :: "moebius" where
  [simp]: "zero_moebius = id_moebius"

definition minus_moebius :: "moebius \<Rightarrow> moebius \<Rightarrow> moebius" where
  [simp]: "minus_moebius A B = A + (-B)"

instance proof
  fix a b c :: moebius
  show "a + b + c = a + (b + c)"
    unfolding plus_moebius_def
  proof (transfer, transfer)
    fix a b c :: complex_mat
    assume "mat_det a \<noteq> 0" "mat_det b \<noteq> 0" "mat_det c \<noteq> 0"
    show "moebius_cmat_eq (moebius_comp_cmat (moebius_comp_cmat a b) c) (moebius_comp_cmat a (moebius_comp_cmat b c))"
      by simp (rule_tac x="1" in exI, simp add: mult_mm_assoc)
  qed
next
  fix a :: moebius
  show "a + 0 = a"
    unfolding plus_moebius_def zero_moebius_def
  proof (transfer, transfer)
    fix A :: complex_mat
    assume "mat_det A \<noteq> 0"
    thus "moebius_cmat_eq (moebius_comp_cmat A id_moebius_cmat) A"
      using mat_eye_r
      by simp
  qed
next
  fix a :: moebius
  show "0 + a = a"
    unfolding plus_moebius_def zero_moebius_def
  proof (transfer, transfer)
    fix A :: complex_mat
    assume "mat_det A \<noteq> 0"
    thus "moebius_cmat_eq (moebius_comp_cmat id_moebius_cmat A) A"
      using mat_eye_l
      by simp
  qed
next
  fix a :: moebius
  show "- a + a = 0"
    unfolding plus_moebius_def uminus_moebius_def zero_moebius_def
  proof (transfer, transfer)
    fix a :: complex_mat
    assume "mat_det a \<noteq> 0"
    thus "moebius_cmat_eq (moebius_comp_cmat (moebius_inv_cmat a) a) id_moebius_cmat"
      by (simp add: mat_inv_l)
  qed
next
  fix a b :: moebius
  show "a + - b = a - b"
    unfolding minus_moebius_def
    by simp
qed
end

text \<open>Composition with inverse\<close>

lemma moebius_comp_inv_left [simp]: 
  shows "moebius_comp (moebius_inv M) M = id_moebius"
  by (metis left_minus plus_moebius_def uminus_moebius_def zero_moebius_def)

lemma moebius_comp_inv_right [simp]:
  shows "moebius_comp M (moebius_inv M) = id_moebius"
  by (metis right_minus plus_moebius_def uminus_moebius_def zero_moebius_def)

lemma moebius_pt_comp_inv_left [simp]:
  shows "moebius_pt (moebius_inv M) (moebius_pt M z) = z"
  by (subst moebius_pt_comp[symmetric], simp)

lemma moebius_pt_comp_inv_right [simp]: 
  shows "moebius_pt M (moebius_pt (moebius_inv M) z) = z"
  by (subst moebius_pt_comp[symmetric], simp)

lemma moebius_pt_comp_inv_image_left [simp]:
  shows "moebius_pt (moebius_inv M) ` moebius_pt M ` A = A"
  by force

lemma moebius_pt_comp_inv_image_right [simp]:
  shows "moebius_pt M ` moebius_pt (moebius_inv M) ` A = A"
  by force

lemma moebius_pt_invert:
  assumes "moebius_pt M z1 = z2"
  shows "moebius_pt (moebius_inv M) z2 = z1"
  using assms[symmetric]
  by simp

lemma moebius_pt_moebius_inv_in_set [simp]:
  assumes "moebius_pt M z \<in> A"
  shows "z \<in> moebius_pt (moebius_inv M) ` A"
  using assms
  using image_iff
  by fastforce

(* -------------------------------------------------------------------------- *)
subsection \<open>Special kinds of Möbius transformations\<close>
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
subsubsection \<open>Reciprocal (1/z) as a Möbius transformation\<close>
(* -------------------------------------------------------------------------- *)

definition moebius_reciprocal :: "moebius" where
  "moebius_reciprocal = mk_moebius 0 1 1 0"

lemma moebius_reciprocal [simp]:
  shows "moebius_pt moebius_reciprocal = reciprocal"
  unfolding moebius_reciprocal_def
  by (rule ext, transfer, transfer) (force simp add: split_def)

lemma moebius_reciprocal_inv [simp]:
  shows "moebius_inv moebius_reciprocal = moebius_reciprocal"
  unfolding moebius_reciprocal_def
  by (transfer, transfer) simp

(* -------------------------------------------------------------------------- *)
subsubsection \<open>Euclidean similarities as a Möbius transform\<close>
(* -------------------------------------------------------------------------- *)

text\<open>Euclidean similarities include Euclidean isometries (translations and rotations) and 
dilatations.\<close>

definition moebius_similarity :: "complex \<Rightarrow> complex \<Rightarrow> moebius" where
  "moebius_similarity a b = mk_moebius a b 0 1"

lemma moebius_pt_moebius_similarity [simp]:
  assumes "a \<noteq> 0"
  shows "moebius_pt (moebius_similarity a b) z = (of_complex a) *\<^sub>h z +\<^sub>h (of_complex b)"
  unfolding moebius_similarity_def
  using assms
  using mult_inf_right[of "of_complex a"]
  by (subst moebius_pt_bilinear, auto)

text \<open>Their action is a linear transformation of $\mathbb{C}.$\<close>
lemma moebius_pt_moebius_similarity':
  assumes "a \<noteq> 0"
  shows "moebius_pt (moebius_similarity a b) = (\<lambda> z. (of_complex a) *\<^sub>h z +\<^sub>h (of_complex b))"
  using moebius_pt_moebius_similarity[OF assms, symmetric]
  by simp

lemma is_moebius_similarity':
  assumes "a \<noteq> 0\<^sub>h" and "a \<noteq> \<infinity>\<^sub>h" and "b \<noteq> \<infinity>\<^sub>h"
  shows "(\<lambda> z. a *\<^sub>h z +\<^sub>h b) = moebius_pt (moebius_similarity (to_complex a) (to_complex b))"
proof-
  obtain ka kb where *: "a = of_complex ka"  "ka \<noteq> 0" "b = of_complex kb"
    using assms
    using inf_or_of_complex[of a]  inf_or_of_complex[of b]
    by auto
  thus ?thesis
    unfolding is_moebius_def
    using moebius_pt_moebius_similarity'[of ka kb]
    by simp
qed

lemma is_moebius_similarity:
  assumes "a \<noteq> 0\<^sub>h" and "a \<noteq> \<infinity>\<^sub>h" and "b \<noteq> \<infinity>\<^sub>h"
  shows "is_moebius (\<lambda> z. a *\<^sub>h z +\<^sub>h b)"
  using is_moebius_similarity'[OF assms]
  unfolding is_moebius_def
  by auto

text \<open>Euclidean similarities form a group.\<close>

lemma moebius_similarity_id [simp]:
  shows "moebius_similarity 1 0 = id_moebius"
  unfolding moebius_similarity_def
  by simp

lemma moebius_similarity_inv [simp]:
  assumes "a \<noteq> 0"
  shows "moebius_inv (moebius_similarity a b) = moebius_similarity (1/a) (-b/a)"
  using assms
  unfolding moebius_similarity_def
  by simp

lemma moebius_similarity_uminus [simp]:
  assumes "a \<noteq> 0"
  shows "- moebius_similarity a b = moebius_similarity (1/a) (-b/a)"
  using assms
  by simp

lemma moebius_similarity_comp [simp]:
  assumes "a \<noteq> 0" and "c \<noteq> 0"
  shows "moebius_comp (moebius_similarity a b) (moebius_similarity c d) = moebius_similarity (a*c) (a*d+b)"
  using assms
  unfolding moebius_similarity_def
  by simp

lemma moebius_similarity_plus [simp]:
  assumes "a \<noteq> 0" and "c \<noteq> 0"
  shows "moebius_similarity a b + moebius_similarity c d = moebius_similarity (a*c) (a*d+b)"
  using assms
  by simp

text \<open>Euclidean similarities are the only Möbius group elements such that their action leaves the
$\infty_{h}$ fixed.\<close>
lemma moebius_similarity_inf [simp]:
  assumes "a \<noteq> 0"
  shows "moebius_pt (moebius_similarity a b) \<infinity>\<^sub>h = \<infinity>\<^sub>h"
  using assms
  unfolding moebius_similarity_def
  by (transfer, transfer, simp)

lemma moebius_similarity_only_inf_to_inf:
  assumes "a \<noteq> 0"  "moebius_pt (moebius_similarity a b) z = \<infinity>\<^sub>h"
  shows "z = \<infinity>\<^sub>h"
  using assms
  using inf_or_of_complex[of z]
  by auto

lemma moebius_similarity_inf_iff [simp]:
  assumes "a \<noteq> 0"
  shows "moebius_pt (moebius_similarity a b) z = \<infinity>\<^sub>h \<longleftrightarrow> z = \<infinity>\<^sub>h"
  using assms
  using moebius_similarity_only_inf_to_inf[of a b z]
  by auto

lemma inf_fixed_only_moebius_similarity:
  assumes "moebius_pt M \<infinity>\<^sub>h = \<infinity>\<^sub>h"
  shows "\<exists> a b. a \<noteq> 0 \<and> M = moebius_similarity a b"
  using assms
  unfolding moebius_similarity_def
proof (transfer, transfer)
  fix M :: complex_mat
  obtain a b c d where MM: "M = (a, b, c, d)"
    by (cases M, auto)
  assume "mat_det M \<noteq> 0" "moebius_pt_cmat_cvec M \<infinity>\<^sub>v \<approx>\<^sub>v \<infinity>\<^sub>v"
  hence *: "c = 0" "a \<noteq> 0 \<and> d \<noteq> 0"
    using MM
    by auto
  show "\<exists>a b. a \<noteq> 0 \<and> moebius_cmat_eq M (mk_moebius_cmat a b 0 1)"
  proof (rule_tac x="a/d" in exI, rule_tac x="b/d" in exI)
    show "a/d \<noteq> 0 \<and> moebius_cmat_eq M (mk_moebius_cmat (a / d) (b / d) 0 1)"
      using MM *
      by simp (rule_tac x="1/d" in exI, simp)
  qed
qed

text \<open>Euclidean similarities include translations, rotations, and dilatations.\<close>

(* -------------------------------------------------------------------------- *)
subsubsection \<open>Translation\<close>
(* -------------------------------------------------------------------------- *)

definition moebius_translation where
  "moebius_translation v = moebius_similarity 1 v"

lemma moebius_translation_comp [simp]:
  shows "moebius_comp (moebius_translation v1) (moebius_translation v2) = moebius_translation (v1 + v2)"
  unfolding moebius_translation_def
  by (simp add: field_simps)

lemma moebius_translation_plus [simp]:
  shows "(moebius_translation v1) + (moebius_translation v2) = moebius_translation (v1 + v2)"
  by simp

lemma moebius_translation_zero [simp]:
  shows "moebius_translation 0 = id_moebius"
  unfolding moebius_translation_def moebius_similarity_id
  by simp

lemma moebius_translation_inv [simp]:
  shows "moebius_inv (moebius_translation v1) = moebius_translation (-v1)"
  using moebius_translation_comp[of v1 "-v1"] moebius_translation_zero
  using minus_unique[of "moebius_translation v1" "moebius_translation (-v1)"]
  by simp

lemma moebius_translation_uminus [simp]:
  shows "- (moebius_translation v1) = moebius_translation (-v1)"
  by simp

lemma moebius_translation_inv_translation [simp]:
  shows "moebius_pt (moebius_translation v) (moebius_pt (moebius_translation (-v)) z) = z"
  using moebius_translation_inv[symmetric, of v]
  by (simp del: moebius_translation_inv)

lemma moebius_inv_translation_translation [simp]:
  shows "moebius_pt (moebius_translation (-v)) (moebius_pt (moebius_translation v) z) = z"
  using moebius_translation_inv[symmetric, of v]
  by (simp del: moebius_translation_inv)

lemma moebius_pt_moebius_translation [simp]:
  shows "moebius_pt (moebius_translation v) (of_complex z) = of_complex (z + v)"
  unfolding moebius_translation_def
  by (simp add: field_simps)

lemma moebius_pt_moebius_translation_inf [simp]:
  shows "moebius_pt (moebius_translation v) \<infinity>\<^sub>h = \<infinity>\<^sub>h"
  unfolding moebius_translation_def
  by simp

(* -------------------------------------------------------------------------- *)
subsubsection \<open>Rotation\<close>
(* -------------------------------------------------------------------------- *)

definition moebius_rotation where
  "moebius_rotation \<phi> = moebius_similarity (cis \<phi>) 0"

lemma moebius_rotation_comp [simp]:
  shows "moebius_comp (moebius_rotation \<phi>1) (moebius_rotation \<phi>2) = moebius_rotation (\<phi>1 + \<phi>2)"
  unfolding moebius_rotation_def
  using moebius_similarity_comp[of "cis \<phi>1" "cis \<phi>2" 0 0]
  by (simp add: cis_mult)

lemma moebius_rotation_plus [simp]:
  shows "(moebius_rotation \<phi>1) + (moebius_rotation \<phi>2) = moebius_rotation (\<phi>1 + \<phi>2)"
  by simp

lemma moebius_rotation_zero [simp]:
  shows "moebius_rotation 0 = id_moebius"
  unfolding moebius_rotation_def
  using moebius_similarity_id
  by simp

lemma moebius_rotation_inv [simp]:
  shows "moebius_inv (moebius_rotation \<phi>) = moebius_rotation (- \<phi>)"
  using moebius_rotation_comp[of \<phi> "-\<phi>"] moebius_rotation_zero
  using minus_unique[of "moebius_rotation \<phi>" "moebius_rotation (-\<phi>)"]
  by simp

lemma moebius_rotation_uminus [simp]:
  shows "- (moebius_rotation \<phi>) = moebius_rotation (- \<phi>)"
  by simp
                                                                                          
lemma moebius_rotation_inv_rotation [simp]:
  shows "moebius_pt (moebius_rotation \<phi>) (moebius_pt (moebius_rotation (-\<phi>)) z) = z"
  using moebius_rotation_inv[symmetric, of \<phi>]
  by (simp del: moebius_rotation_inv)

lemma moebius_inv_rotation_rotation [simp]:
  shows "moebius_pt (moebius_rotation (-\<phi>)) (moebius_pt (moebius_rotation \<phi>) z) = z"
  using moebius_rotation_inv[symmetric, of \<phi>]
  by (simp del: moebius_rotation_inv)

lemma moebius_pt_moebius_rotation [simp]:
  shows "moebius_pt (moebius_rotation \<phi>) (of_complex z) = of_complex (cis \<phi> * z)"
  unfolding moebius_rotation_def
  by simp

lemma moebius_pt_moebius_rotation_inf [simp]:
  shows "moebius_pt (moebius_rotation v) \<infinity>\<^sub>h = \<infinity>\<^sub>h"
  unfolding moebius_rotation_def
  by simp

lemma moebius_pt_rotation_inf_iff [simp]:
  shows "moebius_pt (moebius_rotation v) x = \<infinity>\<^sub>h \<longleftrightarrow> x = \<infinity>\<^sub>h"
  unfolding moebius_rotation_def
  using cis_neq_zero moebius_similarity_only_inf_to_inf
  by (simp del: moebius_pt_moebius_similarity)

lemma moebius_pt_moebius_rotation_zero [simp]:
  shows "moebius_pt (moebius_rotation \<phi>) 0\<^sub>h = 0\<^sub>h"
  unfolding moebius_rotation_def 
  by simp

lemma moebius_pt_moebius_rotation_zero_iff [simp]:
  shows "moebius_pt (moebius_rotation \<phi>) x = 0\<^sub>h \<longleftrightarrow> x = 0\<^sub>h"
  using moebius_pt_invert[of "moebius_rotation \<phi>" x "0\<^sub>h"]
  by auto

lemma moebius_rotation_preserve_cmod [simp]:
  assumes "u \<noteq> \<infinity>\<^sub>h"
  shows "cmod (to_complex (moebius_pt (moebius_rotation \<phi>) u)) = cmod (to_complex u)"
  using assms
  using inf_or_of_complex[of u]
  by auto

(* -------------------------------------------------------------------------- *)
subsubsection \<open>Dilatation\<close>
(* -------------------------------------------------------------------------- *)

definition moebius_dilatation where
  "moebius_dilatation a = moebius_similarity (cor a) 0"

lemma moebius_dilatation_comp [simp]:
  assumes "a1 > 0" and "a2 > 0"
  shows "moebius_comp (moebius_dilatation a1) (moebius_dilatation a2) = moebius_dilatation (a1 * a2)"
  using assms                                  
  unfolding moebius_dilatation_def
  by simp

lemma moebius_dilatation_plus [simp]:
  assumes "a1 > 0" and "a2 > 0"
  shows "(moebius_dilatation a1) + (moebius_dilatation a2) = moebius_dilatation (a1 * a2)"
  using assms
  by simp

lemma moebius_dilatation_zero [simp]:
  shows "moebius_dilatation 1 = id_moebius"
  unfolding moebius_dilatation_def
  using moebius_similarity_id
  by simp

lemma moebius_dilatation_inverse [simp]:
  assumes "a > 0"
  shows "moebius_inv (moebius_dilatation a) = moebius_dilatation (1/a)"
  using assms
  unfolding moebius_dilatation_def
  by simp

lemma moebius_dilatation_uminus [simp]:
  assumes "a > 0"
  shows "- (moebius_dilatation a) = moebius_dilatation (1/a)"
  using assms
  by simp

lemma moebius_pt_dilatation [simp]:
  assumes "a \<noteq> 0"
  shows "moebius_pt (moebius_dilatation a) (of_complex z) = of_complex (cor a * z)"
  using assms
  unfolding moebius_dilatation_def
  by simp

(* -------------------------------------------------------------------------- *)
subsubsection \<open>Rotation-dilatation\<close>
(* -------------------------------------------------------------------------- *)

definition moebius_rotation_dilatation where
  "moebius_rotation_dilatation a = moebius_similarity a 0"

lemma moebius_rotation_dilatation:                                     
  assumes "a \<noteq> 0"
  shows "moebius_rotation_dilatation a = moebius_rotation (arg a) + moebius_dilatation (cmod a)"
  using assms
  unfolding moebius_rotation_dilatation_def moebius_rotation_def moebius_dilatation_def
  by simp

(* -------------------------------------------------------------------------- *)
subsubsection \<open>Conjugate Möbius\<close>
(* -------------------------------------------------------------------------- *)

text \<open>Conjugation is not a Möbius transformation, and conjugate Möbius transformations (obtained
by conjugating each matrix element) do not represent conjugation function (although they are
somewhat related).\<close>

lift_definition conjugate_moebius_mmat :: "moebius_mat \<Rightarrow> moebius_mat" is mat_cnj
  by auto
lift_definition conjugate_moebius :: "moebius \<Rightarrow> moebius" is conjugate_moebius_mmat
  by transfer (auto simp add: mat_cnj_def)

lemma conjugate_moebius:
  shows "conjugate \<circ> moebius_pt M = moebius_pt (conjugate_moebius M) \<circ> conjugate"
  apply (rule ext, simp)
  apply (transfer, transfer)
  using vec_cnj_mult_mv by auto


(* -------------------------------------------------------------------------- *)
subsection \<open>Decomposition of M\"obius transformations\<close>
(* -------------------------------------------------------------------------- *)

text \<open>Every Euclidean similarity can be decomposed using translations, rotations, and dilatations.\<close>
lemma similarity_decomposition:
  assumes "a \<noteq> 0"
  shows "moebius_similarity a b = (moebius_translation b) + (moebius_rotation (arg a)) + (moebius_dilatation (cmod a))"
proof-
  have "moebius_similarity a b = (moebius_translation b) + (moebius_rotation_dilatation a)"
    using assms
    unfolding moebius_rotation_dilatation_def moebius_translation_def moebius_similarity_def
    by auto
  thus ?thesis
    using moebius_rotation_dilatation [OF assms]
    by (auto simp add: add.assoc simp del: plus_moebius_def)
qed

text \<open>A very important fact is that every Möbius transformation can be
composed of Euclidean similarities and a reciprocation.\<close>
lemma moebius_decomposition:
  assumes "c \<noteq> 0" and "a*d - b*c \<noteq> 0"
  shows "mk_moebius a b c d =
             moebius_translation (a/c) +
             moebius_rotation_dilatation ((b*c - a*d)/(c*c)) +
             moebius_reciprocal +
             moebius_translation (d/c)"
  using assms
  unfolding moebius_rotation_dilatation_def moebius_translation_def moebius_similarity_def plus_moebius_def moebius_reciprocal_def
  by (simp add: field_simps) (transfer, transfer, auto simp add: field_simps, rule_tac x="1/c" in exI, simp)

lemma moebius_decomposition_similarity:
  assumes "a \<noteq> 0"
  shows "mk_moebius a b 0 d = moebius_similarity (a/d) (b/d)"
  using assms
  unfolding moebius_similarity_def
  by (transfer, transfer, auto, rule_tac x="1/d" in exI, simp)

text \<open>Decomposition is used in many proofs. Namely, to show that every Möbius transformation has
some property, it suffices to show that reciprocation and all Euclidean similarities have that
property, and that the property is preserved under compositions.\<close>
lemma wlog_moebius_decomposition:
  assumes
    trans: "\<And> v. P (moebius_translation v)" and
    rot: "\<And> \<alpha>. P (moebius_rotation \<alpha>)" and
    dil: "\<And> k. P (moebius_dilatation k)" and
    recip: "P (moebius_reciprocal)" and
    comp: "\<And> M1 M2. \<lbrakk>P M1; P M2\<rbrakk> \<Longrightarrow> P (M1 + M2)"
  shows "P M"
proof-
    obtain a b c d where "M = mk_moebius a b c d" "mat_det (a, b, c, d) \<noteq> 0"
      using ex_mk_moebius[of M]
      by auto
    show ?thesis
    proof (cases "c = 0")
      case False
      show ?thesis
        using moebius_decomposition[of c a d b] \<open>mat_det (a, b, c, d) \<noteq> 0\<close> \<open>c \<noteq> 0\<close> \<open>M = mk_moebius a b c d\<close>
        using moebius_rotation_dilatation[of "(b*c - a*d) / (c*c)"]
        using trans[of "a/c"] rot[of "arg ((b*c - a*d) / (c*c))"] dil[of "cmod ((b*c - a*d) / (c*c))"] recip
        using comp
        by (simp add: trans)
    next
      case True
      hence "M = moebius_similarity (a/d) (b/d)"
        using \<open>M = mk_moebius a b c d\<close> \<open>mat_det (a, b, c, d) \<noteq> 0\<close>
        using moebius_decomposition_similarity
        by auto
      thus ?thesis
        using \<open>c = 0\<close> \<open>mat_det (a, b, c, d) \<noteq> 0\<close>
        using similarity_decomposition[of "a/d" "b/d"]
        using trans[of "b/d"] rot[of "arg (a/d)"] dil[of "cmod (a/d)"] comp
        by simp
    qed
qed

(* -------------------------------------------------------------------------- *)
subsection \<open>Cross ratio and Möbius existence\<close>
(* -------------------------------------------------------------------------- *)

text \<open>For any fixed three points $z1$, $z2$ and $z3$, @{term "cross_ratio z z1 z2 z3"} can be seen as
a function of a single variable $z$.\<close>


lemma is_moebius_cross_ratio:
  assumes "z1 \<noteq> z2" and  "z2 \<noteq> z3" and "z1 \<noteq> z3"
  shows "is_moebius (\<lambda> z. cross_ratio z z1 z2 z3)"
proof-
  have "\<exists> M. \<forall> z. cross_ratio z z1 z2 z3 = moebius_pt M z"
    using assms
  proof (transfer, transfer)
    fix z1 z2 z3
    assume vz: "z1 \<noteq> vec_zero" "z2 \<noteq> vec_zero" "z3 \<noteq> vec_zero"
    obtain z1' z1'' where zz1: "z1 = (z1', z1'')"
      by (cases z1, auto)
    obtain z2' z2'' where zz2: "z2 = (z2', z2'')"
      by (cases z2, auto)
    obtain z3' z3'' where zz3: "z3 = (z3', z3'')"
      by (cases z3, auto)

    let ?m23 = "z2'*z3''-z3'*z2''"
    let ?m21 = "z2'*z1''-z1'*z2''"
    let ?m13 = "z1'*z3''-z3'*z1''"
    let ?M = "(z1''*?m23, -z1'*?m23, z3''*?m21, -z3'*?m21)"
    assume "\<not> z1 \<approx>\<^sub>v z2" "\<not> z2 \<approx>\<^sub>v z3" "\<not> z1 \<approx>\<^sub>v z3"
    hence *: "?m23 \<noteq> 0" "?m21 \<noteq> 0" "?m13 \<noteq> 0"
      using vz zz1 zz2 zz3
      using complex_cvec_eq_mix[of z1' z1'' z2' z2'']
      using complex_cvec_eq_mix[of z1' z1'' z3' z3'']
      using complex_cvec_eq_mix[of z2' z2'' z3' z3'']
      by (auto simp del: complex_cvec_eq_def simp add: field_simps)

    have "mat_det ?M = ?m21*?m23*?m13"
      by (simp add: field_simps)
    hence "mat_det ?M \<noteq> 0"
      using *
      by simp
    moreover
    have "\<forall>z\<in>{v. v \<noteq> vec_zero}. cross_ratio_cvec z z1 z2 z3 \<approx>\<^sub>v moebius_pt_cmat_cvec ?M z"
    proof
      fix z
      assume "z \<in> {v. v \<noteq> vec_zero}"
      hence "z \<noteq> vec_zero"
        by simp
      obtain z' z'' where zz: "z = (z', z'')"
        by (cases z, auto)

      let ?m01 = "z'*z1''-z1'*z''"
      let ?m03 = "z'*z3''-z3'*z''"

      have "?m01 \<noteq> 0 \<or> ?m03 \<noteq> 0"
      proof (cases "z'' = 0 \<or> z1'' = 0 \<or> z3'' = 0")
        case True
        thus ?thesis
          using * \<open>z \<noteq> vec_zero\<close>  zz
          by auto
      next
        case False
        hence 1: "z'' \<noteq> 0 \<and> z1'' \<noteq> 0 \<and> z3'' \<noteq> 0"
          by simp
        show ?thesis
        proof (rule ccontr)
          assume "\<not> ?thesis"
          hence "z' * z1'' - z1' * z'' = 0" "z' * z3'' - z3' * z'' = 0"
            by auto
          hence "z1'/z1'' = z3'/z3''"
            using 1 zz \<open>z \<noteq> vec_zero\<close>
            by (metis frac_eq_eq right_minus_eq)
          thus False
            using * 1
            using frac_eq_eq
            by auto
        qed
      qed
      note * = * this
      show "cross_ratio_cvec z z1 z2 z3 \<approx>\<^sub>v moebius_pt_cmat_cvec ?M z"
        using * zz zz1 zz2 zz3 mult_mv_nonzero[of "z" ?M] \<open>mat_det ?M \<noteq> 0\<close>
        by simp (rule_tac x="1" in exI, simp add: field_simps)
    qed
    ultimately
    show "\<exists>M\<in>{M. mat_det M \<noteq> 0}.
              \<forall>z\<in>{v. v \<noteq> vec_zero}. cross_ratio_cvec z z1 z2 z3 \<approx>\<^sub>v moebius_pt_cmat_cvec M z"
      by blast
  qed
  thus ?thesis
    by (auto simp add: is_moebius_def)
qed

text \<open>Using properties of the cross-ratio, it is shown that there is a Möbius transformation
mapping any three different points to $0_{hc}$, $1_{hc}$ and $\infty_{hc}$, respectively.\<close>
lemma ex_moebius_01inf:
  assumes "z1 \<noteq> z2" and "z1 \<noteq> z3" and "z2 \<noteq> z3"
  shows "\<exists> M. ((moebius_pt M z1 = 0\<^sub>h) \<and> (moebius_pt M z2 = 1\<^sub>h) \<and> (moebius_pt M z3 = \<infinity>\<^sub>h))"
  using assms
  using is_moebius_cross_ratio[OF \<open>z1 \<noteq> z2\<close> \<open>z2 \<noteq> z3\<close> \<open>z1 \<noteq> z3\<close>]
  using cross_ratio_0[OF \<open>z1 \<noteq> z2\<close> \<open>z1 \<noteq> z3\<close>] cross_ratio_1[OF \<open>z1 \<noteq> z2\<close> \<open>z2 \<noteq> z3\<close>] cross_ratio_inf[OF \<open>z1 \<noteq> z3\<close> \<open>z2 \<noteq> z3\<close>]
  by (metis is_moebius_def)

text \<open>There is a Möbius transformation mapping any three different points to any three different
points.\<close>
lemma ex_moebius:
  assumes "z1 \<noteq> z2" and "z1 \<noteq> z3" and "z2 \<noteq> z3" 
          "w1 \<noteq> w2" and "w1 \<noteq> w3" and "w2 \<noteq> w3"
  shows "\<exists> M. ((moebius_pt M z1 = w1) \<and> (moebius_pt M z2 = w2) \<and> (moebius_pt M z3 = w3))"
proof-
  obtain M1 where *: "moebius_pt M1 z1 = 0\<^sub>h \<and> moebius_pt M1 z2 = 1\<^sub>h \<and> moebius_pt M1 z3 = \<infinity>\<^sub>h"
    using ex_moebius_01inf[OF assms(1-3)]
    by auto
  obtain M2 where **: "moebius_pt M2 w1 = 0\<^sub>h \<and> moebius_pt M2 w2 = 1\<^sub>h \<and> moebius_pt M2 w3 = \<infinity>\<^sub>h"
    using ex_moebius_01inf[OF assms(4-6)]
    by auto
  let ?M = "moebius_comp (moebius_inv M2) M1"
  show ?thesis
    using * **
    by (rule_tac x="?M" in exI, auto simp add: moebius_pt_invert)
qed

lemma ex_moebius_1:
  shows "\<exists> M. moebius_pt M z1 = w1"
proof-
  obtain z2 z3 where "z1 \<noteq> z2" "z1 \<noteq> z3" "z2 \<noteq> z3"
    using ex_3_different_points[of z1]
    by auto
  moreover
  obtain w2 w3 where "w1 \<noteq> w2" "w1 \<noteq> w3" "w2 \<noteq> w3"
    using ex_3_different_points[of w1]
    by auto
  ultimately
  show ?thesis
    using ex_moebius[of z1 z2 z3 w1 w2 w3]
    by auto
qed

text \<open>The next lemma turns out to have very important applications in further proof development, as
it enables so called ,,without-loss-of-generality (wlog)'' reasoning \cite{wlog}. Namely, if the
property is preserved under Möbius transformations, then instead of three arbitrary different
points one can consider only the case of points $0_{hc}$, $1_{hc}$, and $\infty_{hc}$.\<close>
lemma wlog_moebius_01inf:
  fixes M::moebius
  assumes "P 0\<^sub>h 1\<^sub>h \<infinity>\<^sub>h" and "z1 \<noteq> z2" and "z2 \<noteq> z3" and "z1 \<noteq> z3"
   "\<And> M a b c. P a b c \<Longrightarrow> P (moebius_pt M a) (moebius_pt M b) (moebius_pt M c)"
  shows "P z1 z2 z3"
proof-
  from assms obtain M where *:
    "moebius_pt M z1 = 0\<^sub>h"  "moebius_pt M z2 = 1\<^sub>h"   "moebius_pt M z3 = \<infinity>\<^sub>h"
    using ex_moebius_01inf[of z1 z2 z3]
    by auto
  have **: "moebius_pt (moebius_inv M) 0\<^sub>h = z1"  "moebius_pt (moebius_inv M) 1\<^sub>h = z2" "moebius_pt (moebius_inv M) \<infinity>\<^sub>h = z3"
    by (subst *[symmetric], simp)+
  thus ?thesis
    using assms
    by auto
qed

(* -------------------------------------------------------------------------- *)
subsection \<open>Fixed points and Möbius transformation uniqueness\<close>
(* -------------------------------------------------------------------------- *)

lemma three_fixed_points_01inf:
  assumes "moebius_pt M 0\<^sub>h = 0\<^sub>h" and "moebius_pt M 1\<^sub>h = 1\<^sub>h" and "moebius_pt M \<infinity>\<^sub>h = \<infinity>\<^sub>h"
  shows "M = id_moebius"
  using assms
  by (transfer, transfer, auto)

lemma three_fixed_points:
  assumes "z1 \<noteq> z2" and "z1 \<noteq> z3" and "z2 \<noteq> z3"
  assumes "moebius_pt M z1 = z1" and "moebius_pt M z2 = z2" and "moebius_pt M z3 = z3"
  shows "M = id_moebius"
proof-
  from assms obtain M' where *: "moebius_pt M' z1 = 0\<^sub>h"  "moebius_pt M' z2 = 1\<^sub>h"   "moebius_pt M' z3 = \<infinity>\<^sub>h"
    using ex_moebius_01inf[of z1 z2 z3]
    by auto
  have **: "moebius_pt (moebius_inv M') 0\<^sub>h = z1"  "moebius_pt (moebius_inv M') 1\<^sub>h = z2" "moebius_pt (moebius_inv M') \<infinity>\<^sub>h = z3"
    by (subst *[symmetric], simp)+

  have "M' + M + (-M') = 0"
    unfolding zero_moebius_def
    apply (rule three_fixed_points_01inf)
    using * ** assms
    by (simp add: moebius_comp[symmetric])+
  thus ?thesis
    by (metis eq_neg_iff_add_eq_0 minus_add_cancel zero_moebius_def)
qed

lemma unique_moebius_three_points:
  assumes "z1 \<noteq> z2" and "z1 \<noteq> z3" and "z2 \<noteq> z3"
  assumes "moebius_pt M1 z1 = w1" and "moebius_pt M1 z2 = w2" and "moebius_pt M1 z3 = w3"
          "moebius_pt M2 z1 = w1" and "moebius_pt M2 z2 = w2" and "moebius_pt M2 z3 = w3"
  shows "M1 = M2"
proof-
  let ?M = "moebius_comp (moebius_inv M2) M1"
  have "moebius_pt ?M z1 = z1"
    using \<open>moebius_pt M1 z1 = w1\<close> \<open>moebius_pt M2 z1 = w1\<close>
    by (auto simp add: moebius_pt_invert)
  moreover
  have "moebius_pt ?M z2 = z2"
    using \<open>moebius_pt M1 z2 = w2\<close> \<open>moebius_pt M2 z2 = w2\<close>
    by (auto simp add: moebius_pt_invert)
  moreover
  have "moebius_pt ?M z3 = z3"
    using \<open>moebius_pt M1 z3 = w3\<close> \<open>moebius_pt M2 z3 = w3\<close>
    by (auto simp add: moebius_pt_invert)
  ultimately
  have "?M = id_moebius"
    using assms three_fixed_points
    by auto
  thus ?thesis
    by (metis add_minus_cancel left_minus plus_moebius_def uminus_moebius_def zero_moebius_def)
qed

text \<open>There is a unique Möbius transformation mapping three different points to other three
different points.\<close>

lemma ex_unique_moebius_three_points:
  assumes "z1 \<noteq> z2" and "z1 \<noteq> z3" and "z2 \<noteq> z3" 
          "w1 \<noteq> w2" and "w1 \<noteq> w3" and "w2 \<noteq> w3"
  shows "\<exists>! M. ((moebius_pt M z1 = w1) \<and> (moebius_pt M z2 = w2) \<and> (moebius_pt M z3 = w3))"
proof-
  obtain M where *: "moebius_pt M z1 = w1 \<and> moebius_pt M z2 = w2 \<and> moebius_pt M z3 = w3"
    using ex_moebius[OF assms]
    by auto
  show ?thesis
    unfolding Ex1_def
  proof (rule_tac x="M" in exI, rule)
    show "\<forall>y. moebius_pt y z1 = w1 \<and> moebius_pt y z2 = w2 \<and> moebius_pt y z3 = w3 \<longrightarrow> y = M"
      using *
      using unique_moebius_three_points[OF assms(1-3)]
      by simp
  qed (simp add: *)
qed

lemma ex_unique_moebius_three_points_fun:
  assumes "z1 \<noteq> z2" and "z1 \<noteq> z3" and "z2 \<noteq> z3" 
          "w1 \<noteq> w2" and "w1 \<noteq> w3" and "w2 \<noteq> w3"
  shows "\<exists>! f. is_moebius f \<and> (f z1 = w1) \<and> (f z2 = w2) \<and> (f z3 = w3)"
proof-
  obtain M where "moebius_pt M z1 = w1" "moebius_pt M z2 = w2" "moebius_pt M z3 = w3"
    using ex_unique_moebius_three_points[OF assms]
    by auto
  thus ?thesis
    using ex_unique_moebius_three_points[OF assms]
    unfolding Ex1_def
    by (rule_tac x="moebius_pt M" in exI) (auto simp add: is_moebius_def)
qed

text \<open>Different Möbius transformations produce different actions.\<close>
lemma unique_moebius_pt:
  assumes "moebius_pt M1 = moebius_pt M2"
  shows "M1 = M2"
  using assms unique_moebius_three_points[of "0\<^sub>h" "1\<^sub>h" "\<infinity>\<^sub>h"]
  by auto

lemma is_cross_ratio_01inf:
  assumes "z1 \<noteq> z2" and "z1 \<noteq> z3" and "z2 \<noteq> z3" and "is_moebius f"
  assumes "f z1 = 0\<^sub>h" and "f z2 = 1\<^sub>h" and "f z3 = \<infinity>\<^sub>h"
  shows "f = (\<lambda> z. cross_ratio z z1 z2 z3)"
  using assms
  using cross_ratio_0[OF \<open>z1 \<noteq> z2\<close> \<open>z1 \<noteq> z3\<close>] cross_ratio_1[OF \<open>z1 \<noteq> z2\<close> \<open>z2 \<noteq> z3\<close>] cross_ratio_inf[OF \<open>z1 \<noteq> z3\<close> \<open>z2 \<noteq> z3\<close>]
  using is_moebius_cross_ratio[OF \<open>z1 \<noteq> z2\<close> \<open>z2 \<noteq> z3\<close> \<open>z1 \<noteq> z3\<close>]
  using ex_unique_moebius_three_points_fun[OF \<open>z1 \<noteq> z2\<close> \<open>z1 \<noteq> z3\<close> \<open>z2 \<noteq> z3\<close>, of "0\<^sub>h" "1\<^sub>h" "\<infinity>\<^sub>h"]
  by auto

text \<open>Möbius transformations preserve cross-ratio.\<close>
lemma moebius_preserve_cross_ratio [simp]:
  assumes "z1 \<noteq> z2" and "z1 \<noteq> z3" and "z2 \<noteq> z3"
  shows "cross_ratio (moebius_pt M z) (moebius_pt M z1) (moebius_pt M z2) (moebius_pt M z3) =
         cross_ratio z z1 z2 z3"
proof-
  let ?f = "\<lambda> z. cross_ratio z z1 z2 z3"
  let ?M = "moebius_pt M"
  let ?iM = "inv ?M"
  have "(?f \<circ> ?iM) (?M z1) = 0\<^sub>h"
    using bij_moebius_pt[of M] cross_ratio_0[OF \<open>z1 \<noteq> z2\<close> \<open>z1 \<noteq> z3\<close>]
    by (simp add: bij_def)
  moreover
  have "(?f \<circ> ?iM) (?M z2) = 1\<^sub>h"
    using bij_moebius_pt[of M]  cross_ratio_1[OF \<open>z1 \<noteq> z2\<close> \<open>z2 \<noteq> z3\<close>]
    by (simp add: bij_def)
  moreover
  have "(?f \<circ> ?iM) (?M z3) = \<infinity>\<^sub>h"
    using bij_moebius_pt[of M] cross_ratio_inf[OF \<open>z1 \<noteq> z3\<close> \<open>z2 \<noteq> z3\<close>]
    by (simp add: bij_def)
  moreover
  have "is_moebius (?f \<circ> ?iM)"
    by (rule is_moebius_comp, rule is_moebius_cross_ratio[OF \<open>z1 \<noteq> z2\<close> \<open>z2 \<noteq> z3\<close> \<open>z1 \<noteq> z3\<close>], rule is_moebius_inv, auto simp add: is_moebius_def)
  moreover
  have "?M z1 \<noteq> ?M z2" "?M z1 \<noteq> ?M z3"  "?M z2 \<noteq> ?M z3"
    using assms
    by simp_all
  ultimately
  have "?f \<circ> ?iM = (\<lambda> z. cross_ratio z (?M z1) (?M z2) (?M z3))"
    using assms
    using is_cross_ratio_01inf[of "?M z1" "?M z2" "?M z3" "?f \<circ> ?iM"]
    by simp
  moreover
  have "(?f \<circ> ?iM) (?M z) = cross_ratio z z1 z2 z3"
    using bij_moebius_pt[of M]
    by (simp add: bij_def)                             
  moreover
  have "(\<lambda> z. cross_ratio z (?M z1) (?M z2) (?M z3)) (?M z) = cross_ratio (?M z) (?M z1) (?M z2) (?M z3)"
    by simp
  ultimately
  show ?thesis
    by simp
qed

lemma conjugate_cross_ratio [simp]:                                  
  assumes "z1 \<noteq> z2" and "z1 \<noteq> z3" and "z2 \<noteq> z3"
  shows "cross_ratio (conjugate z) (conjugate z1) (conjugate z2) (conjugate z3) =
         conjugate (cross_ratio z z1 z2 z3)"
proof-
  let ?f = "\<lambda> z. cross_ratio z z1 z2 z3"
  let ?M = "conjugate"
  let ?iM = "conjugate"
  have "(conjugate \<circ> ?f \<circ> ?iM) (?M z1) = 0\<^sub>h"
    using cross_ratio_0[OF \<open>z1 \<noteq> z2\<close> \<open>z1 \<noteq> z3\<close>]
    by simp
  moreover
  have "(conjugate \<circ> ?f \<circ> ?iM) (?M z2) = 1\<^sub>h"
    using cross_ratio_1[OF \<open>z1 \<noteq> z2\<close> \<open>z2 \<noteq> z3\<close>]
    by simp
  moreover
  have "(conjugate \<circ> ?f \<circ> ?iM) (?M z3) = \<infinity>\<^sub>h"
    using cross_ratio_inf[OF \<open>z1 \<noteq> z3\<close> \<open>z2 \<noteq> z3\<close>]
    by simp
  moreover
  have "is_moebius (conjugate \<circ> ?f \<circ> ?iM)"
  proof-
    obtain M where "?f = moebius_pt M"
      using is_moebius_cross_ratio[OF \<open>z1 \<noteq> z2\<close> \<open>z2 \<noteq> z3\<close> \<open>z1 \<noteq> z3\<close>]
      by (auto simp add: is_moebius_def)
    thus ?thesis
      using conjugate_moebius[of M]
      by (auto simp add: comp_assoc is_moebius_def)
  qed
  moreover
  have "?M z1 \<noteq> ?M z2" "?M z1 \<noteq> ?M z3"  "?M z2 \<noteq> ?M z3"
    using assms
    by (auto simp add: conjugate_inj)
  ultimately
  have "conjugate \<circ> ?f \<circ> ?iM = (\<lambda> z. cross_ratio z (?M z1) (?M z2) (?M z3))"
    using assms
    using is_cross_ratio_01inf[of "?M z1" "?M z2" "?M z3" "conjugate \<circ> ?f \<circ> ?iM"]
    by simp
  moreover
  have "(conjugate \<circ> ?f \<circ> ?iM) (?M z) = conjugate (cross_ratio z z1 z2 z3)"
    by simp
  moreover
  have "(\<lambda> z. cross_ratio z (?M z1) (?M z2) (?M z3)) (?M z) = cross_ratio (?M z) (?M z1) (?M z2) (?M z3)"
    by simp
  ultimately
  show ?thesis
    by simp
qed

lemma cross_ratio_reciprocal [simp]:
  assumes "u \<noteq> v" and "v \<noteq> w" and "u \<noteq> w"
  shows "cross_ratio (reciprocal z) (reciprocal u) (reciprocal v) (reciprocal w) = 
         cross_ratio z u v w"
  using assms
  by (subst moebius_reciprocal[symmetric])+ (simp del: moebius_reciprocal)                           

lemma cross_ratio_inversion [simp]:
  assumes "u \<noteq> v" and "v \<noteq> w" and "u \<noteq> w"
  shows "cross_ratio (inversion z) (inversion u) (inversion v) (inversion w) = 
         conjugate (cross_ratio z u v w)"
proof-                                               
  have "reciprocal u \<noteq> reciprocal v" "reciprocal u \<noteq> reciprocal w" "reciprocal v \<noteq> reciprocal w"
    using assms
    by ((subst moebius_reciprocal[symmetric])+, simp del: moebius_reciprocal)+
  thus ?thesis
    using assms
    unfolding inversion_def
    by simp
qed


lemma fixed_points_0inf':
  assumes "moebius_pt M 0\<^sub>h = 0\<^sub>h" and "moebius_pt M \<infinity>\<^sub>h = \<infinity>\<^sub>h"
  shows "\<exists> k::complex_homo. (k \<noteq> 0\<^sub>h \<and> k \<noteq> \<infinity>\<^sub>h) \<and> (\<forall> z. moebius_pt M z = k *\<^sub>h z)"
using assms
proof (transfer, transfer)
  fix M :: complex_mat
  assume "mat_det M \<noteq> 0"
  obtain a b c d where MM: "M = (a, b, c, d)"
    by (cases M) auto
  assume "moebius_pt_cmat_cvec M 0\<^sub>v \<approx>\<^sub>v 0\<^sub>v" "moebius_pt_cmat_cvec M \<infinity>\<^sub>v \<approx>\<^sub>v \<infinity>\<^sub>v"
  hence *: "b = 0" "c = 0" "a \<noteq> 0 \<and> d \<noteq> 0"
    using MM
    by auto
  let ?z = "(a, d)"
  have "?z \<noteq> vec_zero"
    using *
    by simp
  moreover
  have "\<not> ?z \<approx>\<^sub>v 0\<^sub>v \<and> \<not> ?z \<approx>\<^sub>v \<infinity>\<^sub>v"
    using *
    by simp
  moreover
  have "\<forall>z\<in>{v. v \<noteq> vec_zero}. moebius_pt_cmat_cvec M z \<approx>\<^sub>v ?z *\<^sub>v z"
    using MM \<open>mat_det M \<noteq> 0\<close> *
    by force
  ultimately
  show "\<exists>k\<in>{v. v \<noteq> vec_zero}.
                   (\<not> k \<approx>\<^sub>v 0\<^sub>v \<and> \<not> k \<approx>\<^sub>v \<infinity>\<^sub>v) \<and>
                   (\<forall>z\<in>{v. v \<noteq> vec_zero}. moebius_pt_cmat_cvec M z \<approx>\<^sub>v k *\<^sub>v z)"
    by blast
qed

lemma fixed_points_0inf:
  assumes "moebius_pt M 0\<^sub>h = 0\<^sub>h" and "moebius_pt M \<infinity>\<^sub>h = \<infinity>\<^sub>h"
  shows "\<exists> k::complex_homo. (k \<noteq> 0\<^sub>h \<and> k \<noteq> \<infinity>\<^sub>h) \<and> moebius_pt M = (\<lambda> z. k *\<^sub>h z)"
  using fixed_points_0inf'[OF assms]
  by auto

lemma ex_cross_ratio:
  assumes "u \<noteq> v" and "u \<noteq> w" and "v \<noteq> w"
  shows "\<exists> z. cross_ratio z u v w = c"
proof-
  obtain M where "(\<lambda> z. cross_ratio z u v w) = moebius_pt M"    
    using assms is_moebius_cross_ratio[of u v w]
    unfolding is_moebius_def
    by auto
  hence *: "\<forall> z. cross_ratio z u v w = moebius_pt M z"
    by metis
  let ?z = "moebius_pt (-M) c"
  have "cross_ratio ?z u v w = c"
    using *
    by auto
  thus ?thesis
    by auto
qed

lemma unique_cross_ratio:
  assumes "u \<noteq> v" and "v \<noteq> w" and "u \<noteq> w"
  assumes "cross_ratio z u v w = cross_ratio z' u v w"
  shows "z = z'"
proof-
  obtain M where "(\<lambda> z. cross_ratio z u v w) = moebius_pt M"
    using is_moebius_cross_ratio[OF assms(1-3)]
    unfolding is_moebius_def
    by auto
  hence "moebius_pt M z = moebius_pt M z'"
    using assms(4)
    by metis
  thus ?thesis
    using moebius_pt_eq_I
    by metis
qed

lemma ex1_cross_ratio:
  assumes "u \<noteq> v" and "u \<noteq> w" and "v \<noteq> w"
  shows "\<exists>! z. cross_ratio z u v w = c"
  using assms ex_cross_ratio[OF assms, of c] unique_cross_ratio[of u v w]
  by blast

(* -------------------------------------------------------------------------- *)
subsection \<open>Pole\<close>
(* -------------------------------------------------------------------------- *)

definition is_pole :: "moebius \<Rightarrow> complex_homo \<Rightarrow> bool" where
  "is_pole M z \<longleftrightarrow> moebius_pt M z = \<infinity>\<^sub>h"

lemma ex1_pole:
  shows "\<exists>! z. is_pole M z"
  using bij_moebius_pt[of M]
  unfolding is_pole_def bij_def inj_on_def surj_def
  unfolding Ex1_def
  by (metis UNIV_I)

definition pole :: "moebius \<Rightarrow> complex_homo" where
  "pole M = (THE z. is_pole M z)"

lemma pole_mk_moebius:
  assumes "is_pole (mk_moebius a b c d) z" and "c \<noteq> 0" and "a*d - b*c \<noteq> 0"
  shows "z = of_complex (-d/c)"
proof-
  let ?t1 = "moebius_translation (a / c)"
  let ?rd = "moebius_rotation_dilatation ((b * c - a * d) / (c * c))"
  let ?r = "moebius_reciprocal"                                                 
  let ?t2 = "moebius_translation (d / c)"
  have "moebius_pt (?rd + ?r + ?t2) z = \<infinity>\<^sub>h"
    using assms
    unfolding is_pole_def
    apply (subst (asm) moebius_decomposition)
    apply (auto simp add: moebius_comp[symmetric] moebius_translation_def)
    apply (subst moebius_similarity_only_inf_to_inf[of 1 "a/c"], auto)
    done
  hence "moebius_pt (?r + ?t2) z = \<infinity>\<^sub>h"
    using \<open>a*d - b*c \<noteq> 0\<close> \<open>c \<noteq> 0\<close>
    unfolding moebius_rotation_dilatation_def
    by (simp del: moebius_pt_moebius_similarity)
  hence "moebius_pt ?t2 z = 0\<^sub>h"
    by simp
  thus ?thesis
    using moebius_pt_invert[of ?t2 z "0\<^sub>h"]
    by simp ((subst (asm) of_complex_zero[symmetric])+, simp del: of_complex_zero)
qed

lemma pole_similarity:
  assumes "is_pole (moebius_similarity a b) z" and "a \<noteq> 0"
  shows "z = \<infinity>\<^sub>h"
  using assms
  unfolding is_pole_def
  using moebius_similarity_only_inf_to_inf[of a b z]
  by simp

(* -------------------------------------------------------------------------- *)
subsection \<open>Homographies and antihomographies\<close>
(* -------------------------------------------------------------------------- *)

text \<open>Inversion is not a Möbius transformation (it is a canonical example of so called
anti-Möbius transformations, or antihomographies). All antihomographies are compositions of
homographies and conjugation. The fundamental theorem of projective geometry (that we shall not
prove) states that all automorphisms (bijective functions that preserve the cross-ratio) of
$\mathbb{C}P^1$ are either homographies or antihomographies.\<close>

definition is_homography :: "(complex_homo \<Rightarrow> complex_homo) \<Rightarrow> bool" where
 "is_homography f \<longleftrightarrow> is_moebius f"

definition is_antihomography :: "(complex_homo \<Rightarrow> complex_homo) \<Rightarrow> bool" where
 "is_antihomography f \<longleftrightarrow> (\<exists> f'. is_moebius f' \<and> f = f' \<circ> conjugate)"

text \<open>Conjugation is not a Möbius transformation, but is antihomograhpy.\<close>
lemma not_moebius_conjugate: 
  shows "\<not> is_moebius conjugate"
proof
  assume "is_moebius conjugate"
  then obtain M where *: "moebius_pt M = conjugate"
    unfolding is_moebius_def
    by metis
  hence "moebius_pt M 0\<^sub>h = 0\<^sub>h" "moebius_pt M 1\<^sub>h = 1\<^sub>h" "moebius_pt M \<infinity>\<^sub>h = \<infinity>\<^sub>h"
    by auto
  hence "M = id_moebius"
    using three_fixed_points_01inf
    by auto
  hence "conjugate = id"
    using *
    by simp
  moreover
  have "conjugate ii\<^sub>h \<noteq> ii\<^sub>h"
    using of_complex_inj[of "\<i>" "-\<i>"]
    by (subst of_complex_ii[symmetric])+ (auto simp del: of_complex_ii)
  ultimately
  show False
    by simp
qed

lemma conjugation_is_antihomography[simp]:
  shows "is_antihomography conjugate"
  unfolding is_antihomography_def
  by (rule_tac x="id" in exI, metis fun.map_id0 id_apply is_moebius_def moebius_pt_moebius_id)

lemma inversion_is_antihomography [simp]: 
  shows "is_antihomography inversion"
  using moebius_reciprocal
  unfolding inversion_sym is_antihomography_def is_moebius_def
  by metis

text \<open>Functions cannot simultaneously be homographies and antihomographies - the disjunction is exclusive.\<close>
lemma homography_antihomography_exclusive:
  assumes "is_antihomography f"
  shows "\<not> is_homography f"
proof
  assume "is_homography f"
  then obtain M where "f = moebius_pt M"
    unfolding is_homography_def is_moebius_def
    by auto
  then obtain M' where "moebius_pt M = moebius_pt M' \<circ> conjugate"
    using assms
    unfolding is_antihomography_def is_moebius_def
    by auto
  hence "conjugate = moebius_pt (-M') \<circ> moebius_pt M"
    by auto
  hence "conjugate = moebius_pt (-M' + M)"
    by (simp add: moebius_comp)
  thus False
    using not_moebius_conjugate
    unfolding is_moebius_def
    by metis
qed


(* -------------------------------------------------------------------------- *)
subsection \<open>Classification of Möbius transformations\<close>
(* -------------------------------------------------------------------------- *)

text \<open>Möbius transformations can be classified to parabolic, elliptic and loxodromic. We do not
develop this part of the theory in depth.\<close>

lemma similarity_scale_1:
  assumes "k \<noteq> 0"
  shows "similarity (k *\<^sub>s\<^sub>m I) M = similarity I M"
  using assms
  unfolding similarity_def
  using mat_inv_mult_sm[of k I]
  by simp

lemma similarity_scale_2:
  shows "similarity I (k *\<^sub>s\<^sub>m M) = k *\<^sub>s\<^sub>m (similarity I M)"
  unfolding similarity_def
  by auto

lemma mat_trace_mult_sm [simp]:
  shows "mat_trace (k *\<^sub>s\<^sub>m M) = k * mat_trace M"
  by (cases M) (simp add: field_simps)

definition moebius_mb_cmat :: "complex_mat \<Rightarrow> complex_mat \<Rightarrow> complex_mat" where
  [simp]: "moebius_mb_cmat I M = similarity I M"

lift_definition moebius_mb_mmat :: "moebius_mat \<Rightarrow> moebius_mat \<Rightarrow> moebius_mat" is moebius_mb_cmat
  by (simp add: similarity_def mat_det_inv)

lift_definition moebius_mb :: "moebius \<Rightarrow> moebius \<Rightarrow> moebius" is moebius_mb_mmat
proof transfer
  fix M M' I I'
  assume "moebius_cmat_eq M M'" "moebius_cmat_eq I I'"
  thus "moebius_cmat_eq (moebius_mb_cmat I M) (moebius_mb_cmat I' M')"
    by (auto simp add: similarity_scale_1 similarity_scale_2)
qed

definition similarity_invar_cmat :: "complex_mat \<Rightarrow> complex" where
  [simp]: "similarity_invar_cmat M = (mat_trace M)\<^sup>2 / mat_det M - 4"

lift_definition similarity_invar_mmat :: "moebius_mat \<Rightarrow> complex" is similarity_invar_cmat
  done

lift_definition similarity_invar :: "moebius \<Rightarrow> complex" is similarity_invar_mmat
  by transfer (auto simp add: power2_eq_square field_simps)

lemma similarity_invar_moeibus_mb:
  shows "similarity_invar (moebius_mb I M) = similarity_invar M"
  by (transfer, transfer, simp)

definition similar :: "moebius \<Rightarrow> moebius \<Rightarrow> bool" where
  "similar M1 M2 \<longleftrightarrow> (\<exists> I. moebius_mb I M1 = M2)"

lemma similar_refl [simp]:
  shows "similar M M"
  unfolding similar_def
  by (rule_tac x="id_moebius" in exI) (transfer, transfer, simp)

lemma similar_sym:
  assumes "similar M1 M2"
  shows "similar M2 M1"
proof-
  from assms obtain I where "M2 = moebius_mb I M1"
    unfolding similar_def
    by auto
  hence "M1 = moebius_mb (moebius_inv I) M2"
  proof (transfer, transfer)
    fix M2 I M1
    assume "moebius_cmat_eq M2 (moebius_mb_cmat I M1)" "mat_det I \<noteq> 0"
    then obtain k where "k \<noteq> 0" "similarity I M1 = k *\<^sub>s\<^sub>m M2"
      by auto
    thus "moebius_cmat_eq M1 (moebius_mb_cmat (moebius_inv_cmat I) M2)"
      using similarity_inv[of I M1 "k *\<^sub>s\<^sub>m M2", OF _ \<open>mat_det I \<noteq> 0\<close>]
      by (auto simp add: similarity_scale_2) (rule_tac x="1/k" in exI, simp)
  qed
  thus ?thesis
    unfolding similar_def
    by auto
qed

lemma similar_trans:
  assumes "similar M1 M2" and "similar M2 M3"
  shows "similar M1 M3"
proof-
  obtain I1 I2 where "moebius_mb I1 M1 = M2" "moebius_mb I2 M2 = M3"
    using assms
    by (auto simp add: similar_def)
  thus ?thesis
    unfolding similar_def
  proof (rule_tac x="moebius_comp I1 I2" in exI, transfer, transfer)
    fix I1 I2 M1 M2 M3
    assume "moebius_cmat_eq (moebius_mb_cmat I1 M1) M2"
           "moebius_cmat_eq (moebius_mb_cmat I2 M2) M3"
           "mat_det I1 \<noteq> 0" "mat_det I2 \<noteq> 0"
    thus "moebius_cmat_eq (moebius_mb_cmat (moebius_comp_cmat I1 I2) M1) M3"
      by (auto simp add: similarity_scale_2) (rule_tac x="ka*k" in exI, simp)
  qed
qed

end
