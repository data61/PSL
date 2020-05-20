(* ---------------------------------------------------------------------------- *)
section \<open>Homogeneous coordinates in extended complex plane\<close>
(* ---------------------------------------------------------------------------- *)

text \<open>Extended complex plane $\mathbb{\overline{C}}$ is complex plane with an additional element 
(treated as the infinite point). The extended complex plane $\mathbb{\overline{C}}$ is identified 
with a complex projective line (the one-dimensional projective space over the complex field, sometimes denoted by $\mathbb{C}P^1$).
Each point of $\mathbb{\overline{C}}$ is represented by a pair of complex homogeneous coordinates (not
both equal to zero), and two pairs of homogeneous coordinates represent the same
point in $\mathbb{\overline{C}}$ iff they are proportional by a non-zero complex factor.\<close>

theory Homogeneous_Coordinates
imports More_Complex Matrices
begin

(* ---------------------------------------------------------------------------- *)
subsection \<open>Definition of homogeneous coordinates\<close>
(* ---------------------------------------------------------------------------- *)

text \<open>Two complex vectors are equivalent iff they are proportional.\<close>

definition complex_cvec_eq :: "complex_vec \<Rightarrow> complex_vec \<Rightarrow> bool" (infix "\<approx>\<^sub>v" 50)  where
  [simp]: "z1 \<approx>\<^sub>v z2 \<longleftrightarrow> (\<exists> k. k \<noteq> (0::complex) \<and> z2 = k *\<^sub>s\<^sub>v z1)"

lemma complex_cvec_eq_mix:
  assumes "(z1, z2) \<noteq> vec_zero" and "(w1, w2) \<noteq> vec_zero"
  shows "(z1, z2) \<approx>\<^sub>v (w1, w2) \<longleftrightarrow> z1*w2 = z2*w1"
proof safe
  assume "(z1, z2) \<approx>\<^sub>v (w1, w2)"
  thus "z1 * w2 = z2 * w1"
    by auto
next
  assume *: "z1 * w2 = z2 * w1"
  show "(z1, z2) \<approx>\<^sub>v (w1, w2)"
  proof (cases "z2 = 0")
    case True
    thus ?thesis
      using * assms
      by auto
  next
    case False
    hence "w1 = (w2/z2)*z1 \<and> w2 = (w2/z2)*z2" "w2/z2 \<noteq> 0"
      using * assms
      by (auto simp add: field_simps)
    thus "(z1, z2) \<approx>\<^sub>v (w1, w2)"
      by (metis complex_cvec_eq_def mult_sv.simps)
  qed
qed

lemma complex_eq_cvec_reflp [simp]:
  shows "reflp (\<approx>\<^sub>v)"
  unfolding reflp_def complex_cvec_eq_def
  by safe (rule_tac x="1" in exI, simp)

lemma complex_eq_cvec_symp [simp]:
  shows "symp (\<approx>\<^sub>v)"
  unfolding symp_def complex_cvec_eq_def
  by safe (rule_tac x="1/k" in exI, simp)

lemma complex_eq_cvec_transp [simp]:
  shows "transp (\<approx>\<^sub>v)"
  unfolding transp_def complex_cvec_eq_def
  by safe (rule_tac x="k*ka" in exI, simp)

lemma complex_eq_cvec_equivp [simp]:
  shows "equivp (\<approx>\<^sub>v)"
  by (auto intro: equivpI)

text \<open>Non-zero pairs of complex numbers (also treated as non-zero complex vectors)\<close>

typedef complex_homo_coords = "{v::complex_vec. v \<noteq> vec_zero}"
  by (rule_tac x="(1, 0)" in exI, simp)

setup_lifting type_definition_complex_homo_coords

lift_definition complex_homo_coords_eq :: "complex_homo_coords \<Rightarrow> complex_homo_coords \<Rightarrow> bool" (infix "\<approx>" 50) is complex_cvec_eq
  done

lemma complex_homo_coords_eq_reflp [simp]:
  shows "reflp (\<approx>)"
  using complex_eq_cvec_reflp
  unfolding reflp_def
  by transfer blast

lemma complex_homo_coords_eq_symp [simp]:
  shows "symp (\<approx>)"
  using complex_eq_cvec_symp
  unfolding symp_def
  by transfer blast

lemma complex_homo_coords_eq_transp [simp]: 
  shows "transp (\<approx>)"
  using complex_eq_cvec_transp
  unfolding transp_def
  by transfer blast

lemma complex_homo_coords_eq_equivp:
  shows "equivp (\<approx>)"
  by (auto intro: equivpI)

lemma complex_homo_coords_eq_refl [simp]:
  shows "z \<approx> z"
  using complex_homo_coords_eq_reflp
  unfolding reflp_def refl_on_def
  by blast

lemma complex_homo_coords_eq_sym:
  assumes "z1 \<approx> z2"
  shows "z2 \<approx> z1"
  using assms complex_homo_coords_eq_symp
  unfolding symp_def
  by blast

lemma complex_homo_coords_eq_trans:
  assumes "z1 \<approx> z2" and "z2 \<approx> z3"
  shows "z1 \<approx> z3"
  using assms complex_homo_coords_eq_transp
  unfolding transp_def
  by blast

text \<open>Quotient type of homogeneous coordinates\<close>
quotient_type
  complex_homo = complex_homo_coords / "complex_homo_coords_eq"
  by (rule complex_homo_coords_eq_equivp)


(* ---------------------------------------------------------------------------- *)
subsection \<open>Some characteristic points in $\mathbb{C}P^1$\<close>
(* ---------------------------------------------------------------------------- *)

text \<open>Infinite point\<close>
definition inf_cvec :: "complex_vec" ("\<infinity>\<^sub>v") where
  [simp]: "inf_cvec = (1, 0)"
lift_definition inf_hcoords :: "complex_homo_coords"  ("\<infinity>\<^sub>h\<^sub>c") is inf_cvec
  by simp
lift_definition inf :: "complex_homo"  ("\<infinity>\<^sub>h")  is inf_hcoords
done

lemma inf_cvec_z2_zero_iff:
  assumes "(z1, z2) \<noteq> vec_zero"
  shows "(z1, z2) \<approx>\<^sub>v \<infinity>\<^sub>v \<longleftrightarrow> z2 = 0"
  using assms
  by auto

text \<open>Zero\<close>
definition zero_cvec :: "complex_vec" ("0\<^sub>v") where
  [simp]: "zero_cvec = (0, 1)"
lift_definition zero_hcoords :: "complex_homo_coords" ("0\<^sub>h\<^sub>c") is zero_cvec
  by simp
lift_definition zero :: "complex_homo" ("0\<^sub>h") is zero_hcoords
  done

lemma zero_cvec_z1_zero_iff:
  assumes "(z1, z2) \<noteq> vec_zero"
  shows "(z1, z2) \<approx>\<^sub>v 0\<^sub>v \<longleftrightarrow> z1 = 0"
  using assms
  by auto

text \<open>One\<close>
definition one_cvec :: "complex_vec" ("1\<^sub>v")where
  [simp]: "one_cvec = (1, 1)"
lift_definition one_hcoords :: "complex_homo_coords" ("1\<^sub>h\<^sub>c") is one_cvec
  by simp
lift_definition one :: "complex_homo" ("1\<^sub>h") is one_hcoords
  done

lemma zero_one_infty_not_equal [simp]:
  shows "1\<^sub>h \<noteq> \<infinity>\<^sub>h" and "0\<^sub>h \<noteq> \<infinity>\<^sub>h" and "0\<^sub>h \<noteq> 1\<^sub>h" and "1\<^sub>h \<noteq> 0\<^sub>h" and "\<infinity>\<^sub>h \<noteq> 0\<^sub>h" and "\<infinity>\<^sub>h \<noteq> 1\<^sub>h"
  by (transfer, transfer, simp)+

text \<open>Imaginary unit\<close>
definition ii_cvec :: "complex_vec" ("ii\<^sub>v") where
  [simp]: "ii_cvec = (\<i>, 1)"
lift_definition ii_hcoords :: "complex_homo_coords" ("ii\<^sub>h\<^sub>c") is ii_cvec
  by simp
lift_definition ii :: "complex_homo" ("ii\<^sub>h") is ii_hcoords
  done

lemma ex_3_different_points:
  fixes z::complex_homo
  shows "\<exists> z1 z2. z \<noteq> z1 \<and> z1 \<noteq> z2 \<and> z \<noteq> z2"
proof (cases "z \<noteq> 0\<^sub>h \<and> z \<noteq> 1\<^sub>h")
  case True
  thus ?thesis
    by (rule_tac x="0\<^sub>h" in exI, rule_tac x="1\<^sub>h" in exI, auto)
next
  case False
  hence "z = 0\<^sub>h \<or> z = 1\<^sub>h"
    by simp
  thus ?thesis
  proof
    assume "z = 0\<^sub>h"
    thus ?thesis
      by (rule_tac x="\<infinity>\<^sub>h" in exI, rule_tac x="1\<^sub>h" in exI, auto)
  next
    assume "z = 1\<^sub>h"
    thus ?thesis
      by (rule_tac x="\<infinity>\<^sub>h" in exI, rule_tac x="0\<^sub>h" in exI, auto)
  qed
qed

(* ---------------------------------------------------------------------------- *)
subsection \<open>Connection to ordinary complex plane $\mathbb{C}$\<close>
(* ---------------------------------------------------------------------------- *)

text \<open>Conversion from complex\<close>

definition of_complex_cvec :: "complex \<Rightarrow> complex_vec" where
  [simp]: "of_complex_cvec z = (z, 1)"
lift_definition of_complex_hcoords :: "complex \<Rightarrow> complex_homo_coords" is of_complex_cvec
  by simp
lift_definition of_complex :: "complex \<Rightarrow> complex_homo" is of_complex_hcoords
  done

lemma of_complex_inj:
  assumes "of_complex x = of_complex y"
  shows "x = y"
  using assms
  by (transfer, transfer, simp)

lemma of_complex_image_inj:
  assumes "of_complex ` A = of_complex ` B"
  shows "A = B"
  using assms
  using of_complex_inj
  by auto

lemma of_complex_not_inf [simp]:
  shows "of_complex x \<noteq> \<infinity>\<^sub>h"
  by (transfer, transfer, simp)

lemma inf_not_of_complex [simp]:
  shows "\<infinity>\<^sub>h \<noteq> of_complex x"
  by (transfer, transfer, simp)

lemma inf_or_of_complex:
  shows "z = \<infinity>\<^sub>h \<or> (\<exists> x. z = of_complex x)"
proof (transfer, transfer)
  fix z :: complex_vec
  obtain z1 z2 where *: "z = (z1, z2)"
    by (cases z) auto
  assume "z \<noteq> vec_zero"
  thus "z \<approx>\<^sub>v \<infinity>\<^sub>v \<or> (\<exists>x. z \<approx>\<^sub>v of_complex_cvec x)"
    using *
    by (cases "z2 = 0", auto)
qed

lemma of_complex_zero [simp]:
  shows "of_complex 0 = 0\<^sub>h"
  by (transfer, transfer, simp)

lemma of_complex_one [simp]:
  shows "of_complex 1 = 1\<^sub>h"
  by (transfer, transfer, simp)

lemma of_complex_ii [simp]:
  shows "of_complex \<i> = ii\<^sub>h"
  by (transfer, transfer, simp)

lemma of_complex_zero_iff [simp]:
  shows "of_complex x = 0\<^sub>h \<longleftrightarrow> x = 0"
  by (subst of_complex_zero[symmetric]) (auto simp add: of_complex_inj)

lemma of_complex_one_iff [simp]:
  shows "of_complex x = 1\<^sub>h \<longleftrightarrow> x = 1"
  by (subst of_complex_one[symmetric]) (auto simp add: of_complex_inj)

lemma of_complex_ii_iff [simp]:
  shows "of_complex x = ii\<^sub>h \<longleftrightarrow> x = \<i>"
  by (subst of_complex_ii[symmetric]) (auto simp add: of_complex_inj)

text \<open>Conversion to complex\<close>

definition to_complex_cvec :: "complex_vec \<Rightarrow> complex" where
  [simp]: "to_complex_cvec z = (let (z1, z2) = z in z1/z2)"
lift_definition to_complex_homo_coords :: "complex_homo_coords \<Rightarrow> complex" is to_complex_cvec
  done
lift_definition to_complex :: "complex_homo \<Rightarrow> complex" is to_complex_homo_coords
proof-
  fix z w
  assume "z \<approx> w"
  thus "to_complex_homo_coords z = to_complex_homo_coords w"
    by transfer auto
qed

lemma to_complex_of_complex [simp]:
  shows "to_complex (of_complex z) = z"
  by (transfer, transfer, simp)

lemma of_complex_to_complex [simp]:
  assumes "z \<noteq> \<infinity>\<^sub>h"
  shows "(of_complex (to_complex z)) = z"
  using assms
proof (transfer, transfer)
  fix z :: complex_vec
  obtain z1 z2 where *: "z = (z1, z2)"
    by (cases z, auto)
  assume "z \<noteq> vec_zero" "\<not> z \<approx>\<^sub>v \<infinity>\<^sub>v"
  hence "z2 \<noteq> 0"
    using *
    by (simp, erule_tac x="1/z1" in allE, auto)
  thus "(of_complex_cvec (to_complex_cvec z)) \<approx>\<^sub>v z"
    using *
    by simp
qed

lemma to_complex_zero_zero [simp]:
  shows "to_complex 0\<^sub>h = 0"
  by (metis of_complex_zero to_complex_of_complex)

lemma to_complex_one_one [simp]:
  shows "to_complex 1\<^sub>h = 1"
  by (metis of_complex_one to_complex_of_complex)

lemma to_complex_img_one [simp]:
  shows "to_complex ii\<^sub>h = \<i>"
  by (metis of_complex_ii to_complex_of_complex)

(* ---------------------------------------------------------------------------- *)
subsection \<open>Arithmetic operations\<close>
(* ---------------------------------------------------------------------------- *)

text \<open>Due to the requirement of HOL that all functions are total, we could not define the function
only for the well-defined cases, and in the lifting proofs we must also handle the ill-defined
cases. For example, $\infty_h +_h \infty_h$ is ill-defined, but we must define it, so we define it
arbitrarily to be $\infty_h$.\<close>

(* ---------------------------------------------------------------------------- *)
subsubsection \<open>Addition\<close>
(* ---------------------------------------------------------------------------- *)

text \<open>$\infty_h\ +_h\ \infty_h$ is ill-defined. Since functions must be total, for formal reasons we
define it arbitrarily to be $\infty_h$.\<close>

definition add_cvec :: "complex_vec \<Rightarrow> complex_vec \<Rightarrow> complex_vec" (infixl "+\<^sub>v" 60) where
  [simp]: "add_cvec z w = (let (z1, z2) = z; (w1, w2) = w
                                in if z2 \<noteq> 0 \<or> w2 \<noteq> 0 then
                                      (z1*w2 + w1*z2, z2*w2)
                                   else
                                      (1, 0))"
lift_definition add_hcoords :: "complex_homo_coords \<Rightarrow> complex_homo_coords \<Rightarrow> complex_homo_coords" (infixl "+\<^sub>h\<^sub>c" 60) is add_cvec
  by (auto split: if_split_asm)

lift_definition add :: "complex_homo \<Rightarrow> complex_homo \<Rightarrow> complex_homo" (infixl "+\<^sub>h" 60) is add_hcoords
proof transfer
  fix z w z' w' :: complex_vec
  obtain z1 z2 w1 w2 z'1 z'2 w'1 w'2 where
    *: "z = (z1, z2)" "w = (w1, w2)" "z' = (z'1, z'2)" "w' = (w'1, w'2)"
    by (cases z, auto, cases w, auto, cases z', auto, cases w', auto)
  assume **:
         "z \<noteq> vec_zero" "w \<noteq> vec_zero" "z \<approx>\<^sub>v z'"
         "z' \<noteq> vec_zero" "w' \<noteq> vec_zero" "w \<approx>\<^sub>v w'"
  show "z +\<^sub>v w \<approx>\<^sub>v z' +\<^sub>v w'"
  proof (cases "z2 \<noteq> 0 \<or> w2 \<noteq> 0")
    case True
    hence "z'2 \<noteq> 0 \<or> w'2 \<noteq> 0"
      using * **
      by auto
    show ?thesis
      using \<open>z2 \<noteq> 0 \<or> w2 \<noteq> 0\<close> \<open>z'2 \<noteq> 0 \<or> w'2 \<noteq> 0\<close>
      using * **
      by simp ((erule exE)+, rule_tac x="k*ka" in exI, simp add: field_simps)
  next
    case False
    hence "z'2 = 0 \<or> w'2 = 0"
      using * **
      by auto
    show ?thesis
      using \<open>\<not> (z2 \<noteq> 0 \<or> w2 \<noteq> 0)\<close> \<open>z'2 = 0 \<or> w'2 = 0\<close>
      using * **
      by auto
  qed
qed

lemma add_commute:
  shows "z +\<^sub>h w = w +\<^sub>h z"
  apply (transfer, transfer)
  unfolding complex_cvec_eq_def
  by (rule_tac x="1" in exI, auto split: if_split_asm)

lemma add_zero_right [simp]:
  shows "z +\<^sub>h 0\<^sub>h = z"
  by (transfer, transfer, force)

lemma add_zero_left [simp]:
  shows "0\<^sub>h +\<^sub>h z = z"
  by (subst add_commute) simp

lemma of_complex_add_of_complex [simp]:
  shows "(of_complex x) +\<^sub>h (of_complex y) = of_complex (x + y)"
  by (transfer, transfer, simp)

lemma of_complex_add_inf [simp]:
  shows "(of_complex x) +\<^sub>h \<infinity>\<^sub>h = \<infinity>\<^sub>h"
  by (transfer, transfer, simp)

lemma inf_add_of_complex [simp]:
  shows "\<infinity>\<^sub>h +\<^sub>h (of_complex x) = \<infinity>\<^sub>h"
  by (subst add_commute) simp

lemma inf_add_right:
  assumes "z \<noteq> \<infinity>\<^sub>h"
  shows "z +\<^sub>h \<infinity>\<^sub>h = \<infinity>\<^sub>h"
  using assms
  using inf_or_of_complex[of z]
  by auto

lemma inf_add_left:
  assumes "z \<noteq> \<infinity>\<^sub>h"
  shows "\<infinity>\<^sub>h +\<^sub>h z = \<infinity>\<^sub>h"
  using assms
  by (subst add_commute) (rule inf_add_right, simp)

text \<open>This is ill-defined, but holds by our definition\<close>
lemma inf_add_inf:
  shows "\<infinity>\<^sub>h +\<^sub>h \<infinity>\<^sub>h = \<infinity>\<^sub>h"
  by (transfer, transfer, simp)

(* ---------------------------------------------------------------------------- *)
subsubsection \<open>Unary minus\<close>
(* ---------------------------------------------------------------------------- *)

definition uminus_cvec :: "complex_vec \<Rightarrow> complex_vec" ("~\<^sub>v") where
  [simp]: "~\<^sub>v z = (let (z1, z2) = z in (-z1, z2))"
lift_definition uminus_hcoords :: "complex_homo_coords \<Rightarrow> complex_homo_coords" ("~\<^sub>h\<^sub>c") is uminus_cvec
  by auto
lift_definition uminus :: "complex_homo \<Rightarrow> complex_homo" ("~\<^sub>h") is uminus_hcoords
  by transfer auto

lemma uminus_of_complex [simp]:
  shows "~\<^sub>h (of_complex z) = of_complex (-z)"
  by (transfer, transfer, simp)

lemma uminus_zero [simp]:
  shows "~\<^sub>h 0\<^sub>h = 0\<^sub>h"
  by (transfer, transfer, simp)

lemma uminus_inf [simp]:
  shows "~\<^sub>h \<infinity>\<^sub>h = \<infinity>\<^sub>h"
  apply (transfer, transfer)
  unfolding complex_cvec_eq_def
  by (rule_tac x="-1" in exI, simp)

lemma uminus_inf_iff:
  shows "~\<^sub>h z = \<infinity>\<^sub>h \<longleftrightarrow> z = \<infinity>\<^sub>h"
  apply (transfer, transfer)
  by auto (rule_tac x="-1/a" in exI, auto)

lemma uminus_id_iff:
  shows "~\<^sub>h z = z \<longleftrightarrow> z = 0\<^sub>h \<or> z = \<infinity>\<^sub>h"
  apply (transfer, transfer)
  apply auto
   apply (erule_tac x="1/a" in allE, simp)
  apply (rule_tac x="-1" in exI, simp)
  done


(* ---------------------------------------------------------------------------- *)
subsubsection \<open>Subtraction\<close>
(* ---------------------------------------------------------------------------- *)

text \<open>Operation $\infty_h\ -_h\ \infty_h$ is ill-defined, but we define it arbitrarily to $0_h$. It breaks the connection between
   subtraction with addition and unary minus, but seems more intuitive.\<close>

definition sub :: "complex_homo \<Rightarrow> complex_homo \<Rightarrow> complex_homo" (infixl "-\<^sub>h" 60) where
  "z -\<^sub>h w = (if z = \<infinity>\<^sub>h \<and> w = \<infinity>\<^sub>h then 0\<^sub>h else z +\<^sub>h (~\<^sub>h w))"

lemma of_complex_sub_of_complex [simp]:
  shows "(of_complex x) -\<^sub>h (of_complex y) = of_complex (x - y)"
  unfolding sub_def
  by simp

lemma zero_sub_right[simp]:
  shows "z -\<^sub>h 0\<^sub>h = z"
  unfolding sub_def
  by simp

lemma zero_sub_left[simp]:
  shows "0\<^sub>h -\<^sub>h of_complex x = of_complex (-x)"
  by (subst of_complex_zero[symmetric], simp del: of_complex_zero)

lemma zero_sub_one[simp]:
  shows "0\<^sub>h -\<^sub>h 1\<^sub>h = of_complex (-1)"
  by (metis of_complex_one zero_sub_left)

lemma of_complex_sub_one [simp]:
  shows "of_complex x -\<^sub>h 1\<^sub>h = of_complex (x - 1)"
  by (metis of_complex_one of_complex_sub_of_complex)

lemma sub_eq_zero [simp]:
  assumes "z \<noteq> \<infinity>\<^sub>h"
  shows "z -\<^sub>h z = 0\<^sub>h"
  using assms
  using inf_or_of_complex[of z]
  by auto

lemma sub_eq_zero_iff:
  assumes "z \<noteq> \<infinity>\<^sub>h \<or> w \<noteq> \<infinity>\<^sub>h"
  shows "z -\<^sub>h w = 0\<^sub>h \<longleftrightarrow> z = w"
proof
  assume "z -\<^sub>h w = 0\<^sub>h"
  thus "z = w"
    using assms
    unfolding sub_def
  proof (transfer, transfer)
    fix z w :: complex_vec
    obtain z1 z2 w1 w2 where *: "z = (z1, z2)" "w = (w1, w2)"
      by (cases z, auto, cases w, auto)
    assume "z \<noteq> vec_zero" "w \<noteq> vec_zero" "\<not> z \<approx>\<^sub>v \<infinity>\<^sub>v \<or> \<not> w \<approx>\<^sub>v \<infinity>\<^sub>v" and
           **: "(if z \<approx>\<^sub>v \<infinity>\<^sub>v \<and> w \<approx>\<^sub>v \<infinity>\<^sub>v then 0\<^sub>v else z +\<^sub>v ~\<^sub>v w) \<approx>\<^sub>v 0\<^sub>v"
    have "z2 \<noteq> 0 \<or> w2 \<noteq> 0"
      using * \<open>\<not> z \<approx>\<^sub>v \<infinity>\<^sub>v \<or> \<not> w \<approx>\<^sub>v \<infinity>\<^sub>v\<close> \<open>z \<noteq> vec_zero\<close> \<open>w \<noteq> vec_zero\<close>
      apply auto
       apply (erule_tac x="1/z1" in allE, simp)
      apply (erule_tac x="1/w1" in allE, simp)
      done

    thus "z \<approx>\<^sub>v w"
      using * **
      by simp (rule_tac x="w2/z2" in exI, auto simp add: field_simps)
  qed
next
  assume "z = w"
  thus "z -\<^sub>h w = 0\<^sub>h"
    using sub_eq_zero[of z] assms
    by auto
qed

lemma inf_sub_left [simp]:
  assumes "z \<noteq> \<infinity>\<^sub>h"
  shows "\<infinity>\<^sub>h -\<^sub>h z = \<infinity>\<^sub>h"
  using assms
  using uminus_inf_iff
  using inf_or_of_complex
  unfolding sub_def
  by force

lemma inf_sub_right [simp]:
  assumes "z \<noteq> \<infinity>\<^sub>h"
  shows "z -\<^sub>h \<infinity>\<^sub>h = \<infinity>\<^sub>h"
  using assms
  using inf_or_of_complex
  unfolding sub_def
  by force

text \<open>This is ill-defined, but holds by our definition\<close>
lemma inf_sub_inf:
  shows "\<infinity>\<^sub>h -\<^sub>h \<infinity>\<^sub>h = 0\<^sub>h"
  unfolding sub_def
  by simp

lemma sub_noteq_inf:
  assumes "z \<noteq> \<infinity>\<^sub>h" and "w \<noteq> \<infinity>\<^sub>h"
  shows "z -\<^sub>h w \<noteq> \<infinity>\<^sub>h"
  using assms
  using inf_or_of_complex[of z]
  using inf_or_of_complex[of w]
  using inf_or_of_complex[of "z -\<^sub>h w"]
  using of_complex_sub_of_complex
  by auto

lemma sub_eq_inf:
  assumes "z -\<^sub>h w = \<infinity>\<^sub>h"
  shows "z = \<infinity>\<^sub>h \<or> w = \<infinity>\<^sub>h"
  using assms sub_noteq_inf
  by blast

(* ---------------------------------------------------------------------------- *)
subsubsection \<open>Multiplication\<close>
(* ---------------------------------------------------------------------------- *)

text \<open>Operations $0_h \cdot_h \infty_h$ and $\infty_h \cdot_h 0_h$ are ill defined. Since all
functions must be total, for formal reasons we define it arbitrarily to be $1_h$.\<close>

definition mult_cvec :: "complex_vec \<Rightarrow> complex_vec \<Rightarrow> complex_vec" (infixl "*\<^sub>v" 70) where
 [simp]: "z *\<^sub>v w = (let (z1, z2) = z; (w1, w2) = w
                     in if (z1 = 0 \<and> w2 = 0) \<or> (w1 = 0 \<and> z2 = 0) then
                          (1, 1)
                        else
                          (z1*w1, z2*w2))"
lift_definition mult_hcoords :: "complex_homo_coords \<Rightarrow> complex_homo_coords \<Rightarrow> complex_homo_coords" (infixl "*\<^sub>h\<^sub>c" 70) is mult_cvec
  by (auto split: if_split_asm)

lift_definition mult :: "complex_homo \<Rightarrow> complex_homo \<Rightarrow> complex_homo" (infixl "*\<^sub>h" 70) is mult_hcoords
proof transfer
  fix z w z' w' :: complex_vec
  obtain z1 z2 w1 w2 z'1 z'2 w'1 w'2 where
    *: "z = (z1, z2)" "w = (w1, w2)" "z' = (z'1, z'2)" "w' = (w'1, w'2)"
    by (cases z, auto, cases w, auto, cases z', auto, cases w', auto)
  assume **:
         "z \<noteq> vec_zero" "w \<noteq> vec_zero" "z \<approx>\<^sub>v z'"
         "z' \<noteq> vec_zero" "w' \<noteq> vec_zero" "w \<approx>\<^sub>v w'"
  show "z *\<^sub>v w \<approx>\<^sub>v z' *\<^sub>v w'"
  proof (cases "(z1 = 0 \<and> w2 = 0) \<or> (w1 = 0 \<and> z2 = 0)")
    case True
    hence "(z'1 = 0 \<and> w'2 = 0) \<or> (w'1 = 0 \<and> z'2 = 0)"
      using * **
      by auto
    show ?thesis
      using \<open>(z1 = 0 \<and> w2 = 0) \<or> (w1 = 0 \<and> z2 = 0)\<close> \<open>(z'1 = 0 \<and> w'2 = 0) \<or> (w'1 = 0 \<and> z'2 = 0)\<close>
      using * **
      by simp
  next
    case False
    hence "\<not>((z'1 = 0 \<and> w'2 = 0) \<or> (w'1 = 0 \<and> z'2 = 0))"
      using * **
      by auto
    hence ***: "z *\<^sub>v w = (z1*w1, z2*w2)" "z' *\<^sub>v w' = (z'1*w'1, z'2*w'2)"
      using \<open>\<not>((z1 = 0 \<and> w2 = 0) \<or> (w1 = 0 \<and> z2 = 0))\<close> \<open>\<not>((z'1 = 0 \<and> w'2 = 0) \<or> (w'1 = 0 \<and> z'2 = 0))\<close>
      using *
      by auto
    show ?thesis
      apply (subst ***)+
      using * **
      by simp ((erule exE)+, rule_tac x="k*ka" in exI, simp)
  qed
qed

lemma of_complex_mult_of_complex [simp]:
  shows "(of_complex z1) *\<^sub>h (of_complex z2) = of_complex (z1 * z2)"
  by (transfer, transfer, simp)

lemma mult_commute:
  shows "z1 *\<^sub>h z2 = z2 *\<^sub>h z1"
  apply (transfer, transfer)
  unfolding complex_cvec_eq_def
  by (rule_tac x="1" in exI, auto split: if_split_asm)

lemma mult_zero_left [simp]:
  assumes "z \<noteq> \<infinity>\<^sub>h"
  shows "0\<^sub>h *\<^sub>h z = 0\<^sub>h"
  using assms
proof (transfer, transfer)
  fix z :: complex_vec
  obtain z1 z2 where *: "z = (z1, z2)"
    by (cases z, auto)
  assume "z \<noteq> vec_zero" "\<not> (z \<approx>\<^sub>v \<infinity>\<^sub>v)"
  hence "z2 \<noteq> 0"
    using *
    by force
  thus "0\<^sub>v *\<^sub>v z \<approx>\<^sub>v 0\<^sub>v"
    using *
    by simp
qed

lemma mult_zero_right [simp]:
  assumes "z \<noteq> \<infinity>\<^sub>h"
  shows "z *\<^sub>h 0\<^sub>h = 0\<^sub>h"
  using mult_zero_left[OF assms]
  by (simp add: mult_commute)

lemma mult_inf_right [simp]:
  assumes "z \<noteq> 0\<^sub>h"
  shows "z *\<^sub>h \<infinity>\<^sub>h = \<infinity>\<^sub>h"
using assms
proof (transfer, transfer)
  fix z :: complex_vec
  obtain z1 z2 where *: "z = (z1, z2)"
    by (cases z, auto)
  assume "z \<noteq> vec_zero" "\<not> (z \<approx>\<^sub>v 0\<^sub>v)"
  hence "z1 \<noteq> 0"
    using *
    by force
  thus "z *\<^sub>v \<infinity>\<^sub>v \<approx>\<^sub>v \<infinity>\<^sub>v"
    using *
    by simp
qed

lemma mult_inf_left [simp]:
  assumes "z \<noteq> 0\<^sub>h"
  shows "\<infinity>\<^sub>h *\<^sub>h z = \<infinity>\<^sub>h"
  using mult_inf_right[OF assms]
  by (simp add: mult_commute)

lemma mult_one_left [simp]:
  shows "1\<^sub>h *\<^sub>h z = z"
  by (transfer, transfer, force)

lemma mult_one_right [simp]:
  shows "z *\<^sub>h 1\<^sub>h = z"
  using mult_one_left[of z]
  by (simp add: mult_commute)

text \<open>This is ill-defined, but holds by our definition\<close>
lemma inf_mult_zero:
  shows "\<infinity>\<^sub>h *\<^sub>h 0\<^sub>h = 1\<^sub>h"
  by (transfer, transfer, simp)
lemma zero_mult_inf: 
  shows "0\<^sub>h *\<^sub>h \<infinity>\<^sub>h = 1\<^sub>h"
  by (transfer, transfer, simp)

lemma mult_eq_inf:
  assumes "z *\<^sub>h w = \<infinity>\<^sub>h"
  shows "z = \<infinity>\<^sub>h \<or> w = \<infinity>\<^sub>h"
  using assms
  using inf_or_of_complex[of z]
  using inf_or_of_complex[of w]
  using inf_or_of_complex[of "z *\<^sub>h w"]
  using of_complex_mult_of_complex
  by auto

lemma mult_noteq_inf:
  assumes "z \<noteq> \<infinity>\<^sub>h" and "w \<noteq> \<infinity>\<^sub>h"
  shows "z *\<^sub>h w \<noteq> \<infinity>\<^sub>h"
  using assms mult_eq_inf
  by blast

subsubsection \<open>Reciprocal\<close>
definition reciprocal_cvec :: "complex_vec \<Rightarrow> complex_vec" where
  [simp]: "reciprocal_cvec z = (let (z1, z2) = z in (z2, z1))"
lift_definition reciprocal_hcoords :: "complex_homo_coords \<Rightarrow> complex_homo_coords" is reciprocal_cvec
  by auto

lift_definition reciprocal :: "complex_homo \<Rightarrow> complex_homo" is reciprocal_hcoords
  by transfer auto

lemma reciprocal_involution [simp]: "reciprocal (reciprocal z) = z"
  by (transfer, transfer, auto)

lemma reciprocal_zero [simp]: "reciprocal 0\<^sub>h = \<infinity>\<^sub>h"
  by (transfer, transfer, simp)

lemma reciprocal_inf [simp]: "reciprocal \<infinity>\<^sub>h = 0\<^sub>h"
  by (transfer, transfer, simp)

lemma reciprocal_one [simp]: "reciprocal 1\<^sub>h = 1\<^sub>h"
  by (transfer, transfer, simp)

lemma reciprocal_inf_iff [iff]: "reciprocal z = \<infinity>\<^sub>h \<longleftrightarrow> z = 0\<^sub>h"
  by (transfer, transfer, auto)

lemma reciprocal_zero_iff [iff]: "reciprocal z = 0\<^sub>h \<longleftrightarrow> z = \<infinity>\<^sub>h"
  by (transfer, transfer, auto)

lemma reciprocal_of_complex [simp]:
  assumes "z \<noteq> 0"
  shows "reciprocal (of_complex z) = of_complex (1 / z)"
  using assms
  by (transfer, transfer, simp)

lemma reciprocal_real:
  assumes "is_real (to_complex z)" and "z \<noteq> 0\<^sub>h" and "z \<noteq> \<infinity>\<^sub>h"
  shows "Re (to_complex (reciprocal z)) = 1 / Re (to_complex z)"
proof-
  obtain c where "z = of_complex c" "c \<noteq> 0" "is_real c"
    using assms inf_or_of_complex[of z]
    by auto
  thus ?thesis
    by (simp add: Re_divide_real)
qed

lemma reciprocal_id_iff: 
  shows "reciprocal z = z \<longleftrightarrow> z = of_complex 1 \<or> z = of_complex (-1)"
proof (cases "z = 0\<^sub>h")
  case True
  thus ?thesis
    by (metis inf_not_of_complex of_complex_zero_iff reciprocal_inf_iff zero_neq_neg_one zero_neq_one)
next
  case False
  thus ?thesis
    using inf_or_of_complex[of z]
    by (smt complex_sqrt_1 of_complex_zero_iff reciprocal_inf_iff reciprocal_of_complex to_complex_of_complex)
qed


(* ---------------------------------------------------------------------------- *)
subsubsection \<open>Division\<close>
(* ---------------------------------------------------------------------------- *)

text \<open>Operations $0_h :_h 0_h$ and $\infty_h :_h \infty_h$ are ill-defined. For formal reasons they
are defined to be $1_h$ (by the definition of multiplication).\<close>

definition divide :: "complex_homo \<Rightarrow> complex_homo \<Rightarrow> complex_homo" (infixl ":\<^sub>h" 70) where
  "x :\<^sub>h y = x *\<^sub>h (reciprocal y)"

lemma divide_zero_right [simp]:
  assumes "z \<noteq> 0\<^sub>h"
  shows "z :\<^sub>h 0\<^sub>h = \<infinity>\<^sub>h"
  using assms
  unfolding divide_def
  by simp

lemma divide_zero_left [simp]:
  assumes "z \<noteq> 0\<^sub>h"
  shows "0\<^sub>h :\<^sub>h z = 0\<^sub>h"
  using assms
  unfolding divide_def
  by simp

lemma divide_inf_right [simp]:
  assumes "z \<noteq> \<infinity>\<^sub>h"
  shows "z :\<^sub>h \<infinity>\<^sub>h = 0\<^sub>h"
  using assms
  unfolding divide_def
  by simp

lemma divide_inf_left [simp]:
  assumes "z \<noteq> \<infinity>\<^sub>h"
  shows "\<infinity>\<^sub>h :\<^sub>h z = \<infinity>\<^sub>h"
  using assms reciprocal_zero_iff[of z] mult_inf_left
  unfolding divide_def
  by simp

lemma divide_eq_inf:
  assumes "z :\<^sub>h w = \<infinity>\<^sub>h"
  shows "z = \<infinity>\<^sub>h \<or> w = 0\<^sub>h"
  using assms
  using reciprocal_inf_iff[of w] mult_eq_inf
  unfolding divide_def
  by auto

lemma inf_divide_zero [simp]:
  shows "\<infinity>\<^sub>h :\<^sub>h 0\<^sub>h = \<infinity>\<^sub>h"
  unfolding divide_def
  by (transfer, simp)

lemma zero_divide_inf [simp]:
  shows "0\<^sub>h :\<^sub>h \<infinity>\<^sub>h =  0\<^sub>h"
  unfolding divide_def
  by (transfer, simp)

lemma divide_one_right [simp]:
  shows "z :\<^sub>h 1\<^sub>h = z"
  unfolding divide_def
  by simp

lemma of_complex_divide_of_complex [simp]:
  assumes "z2 \<noteq> 0"
  shows "(of_complex z1) :\<^sub>h (of_complex z2) = of_complex (z1 / z2)"
using assms
  unfolding divide_def
  apply transfer
  apply transfer
  by (simp, rule_tac x="1/z2" in exI, simp)

lemma one_div_of_complex [simp]:
  assumes "x \<noteq> 0"
  shows "1\<^sub>h :\<^sub>h of_complex x = of_complex (1 / x)"
  using assms
  unfolding divide_def
  by simp

text \<open> This is ill-defined, but holds by our definition\<close>
lemma inf_divide_inf: 
  shows "\<infinity>\<^sub>h :\<^sub>h \<infinity>\<^sub>h = 1\<^sub>h"
  unfolding divide_def
  by (simp add: inf_mult_zero)

text \<open> This is ill-defined, but holds by our definition\<close>
lemma zero_divide_zero:
  shows "0\<^sub>h :\<^sub>h 0\<^sub>h = 1\<^sub>h"
  unfolding divide_def
  by (simp add: zero_mult_inf)

(* ---------------------------------------------------------------------------- *)
subsubsection \<open>Conjugate\<close>
(* ---------------------------------------------------------------------------- *)

definition conjugate_cvec :: "complex_vec \<Rightarrow> complex_vec" where
  [simp]: "conjugate_cvec z = vec_cnj z"
lift_definition conjugate_hcoords :: "complex_homo_coords \<Rightarrow> complex_homo_coords" is conjugate_cvec
  by (auto simp add: vec_cnj_def)
lift_definition conjugate :: "complex_homo \<Rightarrow> complex_homo" is conjugate_hcoords
  by transfer (auto simp add: vec_cnj_def)

lemma conjugate_involution [simp]:
  shows "conjugate (conjugate z) = z"
  by (transfer, transfer, auto)

lemma conjugate_conjugate_comp [simp]:
  shows "conjugate \<circ> conjugate = id"
  by (rule ext, simp)

lemma inv_conjugate [simp]:
  shows "inv conjugate = conjugate"
  using inv_unique_comp[of conjugate conjugate]
  by simp

lemma conjugate_of_complex [simp]:
  shows "conjugate (of_complex z) = of_complex (cnj z)"
  by (transfer, transfer, simp add: vec_cnj_def)

lemma conjugate_inf [simp]:
  shows "conjugate \<infinity>\<^sub>h = \<infinity>\<^sub>h"
  by (transfer, transfer, simp add: vec_cnj_def)

lemma conjugate_zero [simp]:
  shows "conjugate 0\<^sub>h = 0\<^sub>h"
  by (transfer, transfer, simp add: vec_cnj_def)

lemma conjugate_one [simp]:
  shows "conjugate 1\<^sub>h = 1\<^sub>h"
  by (transfer, transfer, simp add: vec_cnj_def)

lemma conjugate_inj:
  assumes "conjugate x = conjugate y"
  shows "x = y"
  using assms
  using conjugate_involution[of x] conjugate_involution[of y]
  by metis

lemma bij_conjugate [simp]:
  shows "bij conjugate"
  unfolding bij_def inj_on_def
proof auto
  fix x y
  assume "conjugate x = conjugate y"
  thus "x = y"
   by (simp add: conjugate_inj)
next
  fix x
  show "x \<in> range conjugate"
    by (metis conjugate_involution range_eqI)
qed

lemma conjugate_id_iff: 
  shows "conjugate a = a \<longleftrightarrow> is_real (to_complex a) \<or> a = \<infinity>\<^sub>h"
  using inf_or_of_complex[of a]
  by (metis conjugate_inf conjugate_of_complex eq_cnj_iff_real to_complex_of_complex)

subsubsection \<open>Inversion\<close>

text \<open>Geometric inversion wrt. the unit circle\<close>

definition inversion where
  "inversion = conjugate \<circ> reciprocal"

lemma inversion_sym:
  shows "inversion = reciprocal \<circ> conjugate"
  unfolding inversion_def
  apply (rule ext, simp)
  apply transfer
  apply transfer
  apply (auto simp add: vec_cnj_def)
  using one_neq_zero
  by blast+

lemma inversion_involution [simp]:
  shows "inversion (inversion z) = z"
proof-
  have *: "conjugate \<circ> reciprocal = reciprocal \<circ> conjugate"
    using inversion_sym
    by (simp add: inversion_def)
  show ?thesis
    unfolding inversion_def
    by (subst *) simp
qed

lemma inversion_inversion_id [simp]:
  shows "inversion \<circ> inversion = id"
  by (rule ext, simp)

lemma inversion_zero [simp]:
  shows "inversion 0\<^sub>h = \<infinity>\<^sub>h"
  by (simp add: inversion_def)

lemma inversion_infty [simp]:
  shows "inversion \<infinity>\<^sub>h = 0\<^sub>h"
  by (simp add: inversion_def)

lemma inversion_of_complex [simp]:
  assumes "z \<noteq> 0"
  shows "inversion (of_complex z) = of_complex (1 / cnj z)"
  using assms
  by (simp add: inversion_def)

lemma is_real_inversion:
  assumes "is_real x" and "x \<noteq> 0"
  shows "is_real (to_complex (inversion (of_complex x)))"
  using assms eq_cnj_iff_real[of x]
  by simp

lemma inversion_id_iff: 
  shows "a = inversion a \<longleftrightarrow> a \<noteq> \<infinity>\<^sub>h \<and> (to_complex a) * cnj (to_complex a) = 1" (is "?lhs = ?rhs")
proof
  assume "a = inversion a"
  thus ?rhs
    unfolding inversion_def
    using inf_or_of_complex[of a]
    by (metis (full_types) comp_apply complex_cnj_cancel_iff complex_cnj_zero inversion_def inversion_infty inversion_of_complex inversion_sym nonzero_eq_divide_eq of_complex_zero reciprocal_zero to_complex_of_complex zero_one_infty_not_equal(5))
next
  assume ?rhs
  thus ?lhs
    using inf_or_of_complex[of a]
    by (metis inversion_of_complex mult_not_zero nonzero_mult_div_cancel_right one_neq_zero to_complex_of_complex)
qed

(* ---------------------------------------------------------------------------- *)
subsection \<open>Ratio and cross-ratio\<close>
(* ---------------------------------------------------------------------------- *)

(* ---------------------------------------------------------------------------- *)
subsubsection \<open>Ratio\<close>
(* ---------------------------------------------------------------------------- *)

text \<open>Ratio of points $z$, $v$ and $w$ is usually defined as
$\frac{z-v}{z-w}$. Our definition introduces it in homogeneous
coordinates. It is well-defined if $z_1 \neq z_2 \vee z_1 \neq z_3$ and $z_1 \neq \infty_h$ and 
$z_2 \neq \infty_h \vee z_3 \neq \infty_h$\<close>

definition ratio :: "complex_homo \<Rightarrow> complex_homo \<Rightarrow> complex_homo \<Rightarrow> complex_homo" where
  "ratio za zb zc = (za -\<^sub>h zb) :\<^sub>h (za -\<^sub>h zc)"

text \<open>This is ill-defined, but holds by our definition\<close>
lemma
  assumes "zb \<noteq> \<infinity>\<^sub>h" and "zc \<noteq> \<infinity>\<^sub>h"
  shows "ratio \<infinity>\<^sub>h zb zc = 1\<^sub>h"
  using assms
  using inf_sub_left[OF assms(1)]
  using inf_sub_left[OF assms(2)]
  unfolding ratio_def
  by (simp add: inf_divide_inf)

lemma
  assumes "za \<noteq> \<infinity>\<^sub>h" and "zc \<noteq> \<infinity>\<^sub>h"
  shows "ratio za \<infinity>\<^sub>h zc = \<infinity>\<^sub>h"
  using assms
  unfolding ratio_def
  using inf_sub_right[OF assms(1)]
  using sub_noteq_inf[OF assms]
  using divide_inf_left
  by simp

lemma
  assumes "za \<noteq> \<infinity>\<^sub>h" and "zb \<noteq> \<infinity>\<^sub>h"
  shows "ratio za zb \<infinity>\<^sub>h = 0\<^sub>h"
  unfolding ratio_def
  using sub_noteq_inf[OF assms]
  using inf_sub_right[OF assms(1)]
  using divide_inf_right
  by simp

lemma
  assumes "z1 \<noteq> z2" and "z1 \<noteq> \<infinity>\<^sub>h"
  shows "ratio z1 z2 z1 = \<infinity>\<^sub>h"
  using assms
  unfolding ratio_def
  using divide_zero_right[of "z1 -\<^sub>h z2"]
  using sub_eq_zero_iff[of z1 z2]
  by simp

(* ---------------------------------------------------------------------------- *)
subsubsection \<open>Cross-ratio\<close>
(* ---------------------------------------------------------------------------- *)

text \<open>The cross-ratio is defined over 4 points $(z, u, v, w)$, usually as
$\frac{(z-u)(v-w)}{(z-w)(v-u)}$. We define it using homogeneous coordinates. Cross ratio is
ill-defined when $z = u \vee v = w$ and $z = w$ and $v = u$ i.e. when 3 points are equal. Since
function must be total, in that case we define it arbitrarily to 1.\<close>

definition cross_ratio_cvec :: "complex_vec \<Rightarrow> complex_vec \<Rightarrow> complex_vec \<Rightarrow> complex_vec \<Rightarrow> complex_vec" where
  [simp]: "cross_ratio_cvec z u v w =
     (let (z', z'') = z;
          (u', u'') = u;
          (v', v'') = v;
          (w', w'') = w;
          n1 = z'*u'' - u'*z'';
          n2 = v'*w'' - w'*v'';
          d1 = z'*w'' - w'*z'';
          d2 = v'*u'' - u'*v''
       in
         if n1 * n2 \<noteq> 0 \<or> d1 * d2 \<noteq> 0 then
              (n1 * n2, d1 * d2)
         else
              (1, 1))"

lift_definition cross_ratio_hcoords :: "complex_homo_coords \<Rightarrow> complex_homo_coords \<Rightarrow> complex_homo_coords \<Rightarrow> complex_homo_coords \<Rightarrow> complex_homo_coords" is cross_ratio_cvec
  by (auto split: if_split_asm)

lift_definition cross_ratio :: "complex_homo \<Rightarrow> complex_homo \<Rightarrow> complex_homo \<Rightarrow> complex_homo \<Rightarrow> complex_homo" is cross_ratio_hcoords
proof transfer
  fix z u v w z' u' v' w' :: complex_vec
  obtain z1 z2 u1 u2 v1 v2 w1 w2 z'1 z'2 u'1 u'2 v'1 v'2 w'1 w'2
    where *: "z = (z1, z2)" "u = (u1, u2)" "v = (v1, v2)" "w = (w1, w2)"
             "z' = (z'1, z'2)" "u' = (u'1, u'2)" "v' = (v'1, v'2)" "w' = (w'1, w'2)"
    by (cases z, auto, cases u, auto, cases v, auto, cases w, auto,
        cases z', auto, cases u', auto, cases v', auto, cases w', auto)
  let ?n1 = "z1*u2 - u1*z2"
  let ?n2 = "v1*w2 - w1*v2"
  let ?d1 = "z1*w2 - w1*z2"
  let ?d2 = "v1*u2 - u1*v2"
  let ?n1' = "z'1*u'2 - u'1*z'2"
  let ?n2' = "v'1*w'2 - w'1*v'2"
  let ?d1' = "z'1*w'2 - w'1*z'2"
  let ?d2' = "v'1*u'2 - u'1*v'2"

  assume **:
         "z \<noteq> vec_zero" "u \<noteq> vec_zero" "v \<noteq> vec_zero" "w \<noteq> vec_zero"
         "z' \<noteq> vec_zero" "u' \<noteq> vec_zero" "v' \<noteq> vec_zero" "w' \<noteq> vec_zero"
         "z \<approx>\<^sub>v z'" "v \<approx>\<^sub>v v'" "u \<approx>\<^sub>v u'" "w \<approx>\<^sub>v w'"
  show "cross_ratio_cvec z u v w \<approx>\<^sub>v cross_ratio_cvec z' u' v' w'"
  proof (cases "?n1*?n2 \<noteq> 0 \<or> ?d1*?d2 \<noteq> 0")
    case True
    hence "?n1'*?n2' \<noteq> 0 \<or> ?d1'*?d2' \<noteq> 0"
      using * **
      by simp ((erule exE)+, simp)
    show ?thesis
      using \<open>?n1*?n2 \<noteq> 0 \<or> ?d1*?d2 \<noteq> 0\<close>
      using \<open>?n1'*?n2' \<noteq> 0 \<or> ?d1'*?d2' \<noteq> 0\<close>
      using * **
      by simp ((erule exE)+, rule_tac x="k*ka*kb*kc" in exI, simp add: field_simps)
  next
    case False
    hence "\<not> (?n1'*?n2' \<noteq> 0 \<or> ?d1'*?d2' \<noteq> 0)"
      using * **
      by simp ((erule exE)+, simp)
    show ?thesis
      using \<open>\<not> (?n1*?n2 \<noteq> 0 \<or> ?d1*?d2 \<noteq> 0)\<close>
      using \<open>\<not> (?n1'*?n2' \<noteq> 0 \<or> ?d1'*?d2' \<noteq> 0)\<close>
      using * **
      by simp blast
  qed
qed

lemma cross_ratio_01inf_id [simp]:
  shows "cross_ratio z 0\<^sub>h 1\<^sub>h \<infinity>\<^sub>h = z"
proof (transfer, transfer)
  fix z :: complex_vec
  obtain z1 z2 where *: "z = (z1, z2)"
    by (cases z, auto)
  assume "z \<noteq> vec_zero"
  thus "cross_ratio_cvec z 0\<^sub>v 1\<^sub>v \<infinity>\<^sub>v \<approx>\<^sub>v z"
    using *
    by simp (rule_tac x="-1" in exI, simp)
qed

lemma cross_ratio_0:
  assumes "u \<noteq> v" and "u \<noteq> w"
  shows "cross_ratio u u v w = 0\<^sub>h"
  using assms
proof (transfer, transfer)
  fix u v w  :: complex_vec
  obtain u1 u2 v1 v2 w1 w2
    where *: "u = (u1, u2)" "v = (v1, v2)" "w = (w1, w2)"
    by (cases u, auto, cases v, auto, cases w, auto)
  assume "u \<noteq> vec_zero" "v \<noteq> vec_zero" "w \<noteq> vec_zero" "\<not> u \<approx>\<^sub>v v" "\<not> u \<approx>\<^sub>v w"
  thus "cross_ratio_cvec u u v w \<approx>\<^sub>v 0\<^sub>v"
    using * complex_cvec_eq_mix[of u1 u2 v1 v2] complex_cvec_eq_mix[of u1 u2 w1 w2]
    by (force simp add: mult.commute)
qed

lemma cross_ratio_1:
  assumes "u \<noteq> v" and "v \<noteq> w"
  shows "cross_ratio v u v w = 1\<^sub>h"
  using assms
proof (transfer, transfer)
  fix u v w  :: complex_vec
  obtain u1 u2 v1 v2 w1 w2
    where *: "u = (u1, u2)" "v = (v1, v2)" "w = (w1, w2)"
    by (cases u, auto, cases v, auto, cases w, auto)
  let ?n1 = "v1*u2 - u1*v2"
  let ?n2 = "v1*w2 - w1*v2"
  assume "u \<noteq> vec_zero" "v \<noteq> vec_zero" "w \<noteq> vec_zero" "\<not> u \<approx>\<^sub>v v" "\<not> v \<approx>\<^sub>v w"
  hence "?n1 \<noteq> 0 \<and> ?n2 \<noteq> 0"
    using * complex_cvec_eq_mix[of u1 u2 v1 v2] complex_cvec_eq_mix[of v1 v2 w1 w2]
    by (auto simp add: field_simps)
  thus "cross_ratio_cvec v u v w \<approx>\<^sub>v 1\<^sub>v"
    using *
    by simp (rule_tac x="1 / (?n1 * ?n2)" in exI, simp)
qed

lemma cross_ratio_inf:
  assumes "u \<noteq> w" and "v \<noteq> w"
  shows "cross_ratio w u v w = \<infinity>\<^sub>h"
  using assms
proof (transfer, transfer)
  fix u v w  :: complex_vec
  obtain u1 u2 v1 v2 w1 w2
    where *: "u = (u1, u2)" "v = (v1, v2)" "w = (w1, w2)"
    by (cases u, auto, cases v, auto, cases w, auto)
  let ?n1 = "w1*u2 - u1*w2"
  let ?n2 = "v1*w2 - w1*v2"
  assume "u \<noteq> vec_zero" "v \<noteq> vec_zero" "w \<noteq> vec_zero" "\<not> u \<approx>\<^sub>v w" "\<not> v \<approx>\<^sub>v w"
  hence "?n1 \<noteq> 0 \<and> ?n2 \<noteq> 0"
    using * complex_cvec_eq_mix[of u1 u2 w1 w2] complex_cvec_eq_mix[of v1 v2 w1 w2]
    by (auto simp add: field_simps)
  thus "cross_ratio_cvec w u v w \<approx>\<^sub>v \<infinity>\<^sub>v"
    using *
    by simp
qed

lemma cross_ratio_0inf:
  assumes "y \<noteq> 0"
  shows "cross_ratio (of_complex x) 0\<^sub>h (of_complex y) \<infinity>\<^sub>h = (of_complex (x / y))"
  using assms
  by (transfer, transfer) (simp, rule_tac x="-1/y" in exI, simp)

lemma cross_ratio_commute_13:
  shows "cross_ratio z u v w = reciprocal (cross_ratio v u z w)"
  by (transfer, transfer, case_tac z, case_tac u, case_tac v, case_tac w, simp)

lemma cross_ratio_commute_24:
  shows "cross_ratio z u v w = reciprocal (cross_ratio z w v u)"
  by (transfer, transfer, case_tac z, case_tac u, case_tac v, case_tac w, simp)

lemma cross_ratio_not_inf:
  assumes "z \<noteq> w" and "u \<noteq> v"
  shows "cross_ratio z u v w \<noteq> \<infinity>\<^sub>h"
  using assms
proof (transfer, transfer)
  fix z u v w
  assume nz: "z \<noteq> vec_zero" "u \<noteq> vec_zero" "v \<noteq> vec_zero" "w \<noteq> vec_zero"
  obtain z1 z2 u1 u2 v1 v2 w1 w2 where *: "z = (z1, z2)" "u = (u1, u2)" "v = (v1, v2)" "w = (w1, w2)"
    by (cases z, cases u, cases v, cases w, auto)
  obtain x1 x2 where **: "cross_ratio_cvec z u v w = (x1, x2)"
    by (cases "cross_ratio_cvec z u v w", auto)
  assume "\<not> z \<approx>\<^sub>v w" "\<not> u \<approx>\<^sub>v v"
  hence "z1*w2 \<noteq> z2*w1" "u1*v2 \<noteq> u2*v1"
    using * nz complex_cvec_eq_mix
    by blast+
  hence "x2 \<noteq> 0"
    using * **
    by (auto split: if_split_asm) (simp add: field_simps)
  thus "\<not> cross_ratio_cvec z u v w \<approx>\<^sub>v \<infinity>\<^sub>v"
    using inf_cvec_z2_zero_iff * **
    by simp
qed

lemma cross_ratio_not_zero:
  assumes "z \<noteq> u" and "v \<noteq> w"
  shows "cross_ratio z u v w \<noteq> 0\<^sub>h"
  using assms
proof (transfer, transfer)
  fix z u v w
  assume nz: "z \<noteq> vec_zero" "u \<noteq> vec_zero" "v \<noteq> vec_zero" "w \<noteq> vec_zero"
  obtain z1 z2 u1 u2 v1 v2 w1 w2 where *: "z = (z1, z2)" "u = (u1, u2)" "v = (v1, v2)" "w = (w1, w2)"
    by (cases z, cases u, cases v, cases w, auto)
  obtain x1 x2 where **: "cross_ratio_cvec z u v w = (x1, x2)"
    by (cases "cross_ratio_cvec z u v w", auto)
  assume "\<not> z \<approx>\<^sub>v u" "\<not> v \<approx>\<^sub>v w"
  hence "z1*u2 \<noteq> z2*u1" "v1*w2 \<noteq> v2*w1"
    using * nz complex_cvec_eq_mix
    by blast+
  hence "x1 \<noteq> 0"
    using * **
    by (auto split: if_split_asm)
  thus "\<not> cross_ratio_cvec z u v w \<approx>\<^sub>v 0\<^sub>v"
    using zero_cvec_z1_zero_iff * **
    by simp
qed

lemma cross_ratio_real:
  assumes "is_real z" and "is_real u" and "is_real v" and "is_real w" 
  assumes "z \<noteq> u \<and> v \<noteq> w \<or> z \<noteq> w \<and> u \<noteq> v"
  shows "is_real (to_complex (cross_ratio (of_complex z) (of_complex u) (of_complex v) (of_complex w)))"
  using assms
  by (transfer, transfer, auto)

lemma cross_ratio:
  assumes "(z \<noteq> u \<and> v \<noteq> w) \<or> (z \<noteq> w \<and> u \<noteq> v)" and
          "z \<noteq> \<infinity>\<^sub>h" and  "u \<noteq> \<infinity>\<^sub>h" and "v \<noteq> \<infinity>\<^sub>h" and "w \<noteq> \<infinity>\<^sub>h"
  shows "cross_ratio z u v w = ((z -\<^sub>h u) *\<^sub>h (v -\<^sub>h w)) :\<^sub>h ((z -\<^sub>h w) *\<^sub>h (v -\<^sub>h u))"
  unfolding sub_def divide_def
  using assms
  apply transfer
  apply simp
  apply transfer
proof-
  fix z u v w :: complex_vec
  obtain z1 z2 u1 u2 v1 v2 w1 w2
    where *: "z = (z1, z2)" "u = (u1, u2)" "v = (v1, v2)" "w = (w1, w2)"
    by (cases z, auto, cases u, auto, cases v, auto, cases w, auto)

  let ?n1 = "z1*u2 - u1*z2"
  let ?n2 = "v1*w2 - w1*v2"
  let ?d1 = "z1*w2 - w1*z2"
  let ?d2 = "v1*u2 - u1*v2"
  assume **: "z \<noteq> vec_zero" "u \<noteq> vec_zero" "v \<noteq> vec_zero" "w \<noteq> vec_zero"
         "\<not> z \<approx>\<^sub>v u \<and> \<not> v \<approx>\<^sub>v w \<or> \<not> z \<approx>\<^sub>v w \<and> \<not> u \<approx>\<^sub>v v"
         "\<not> z \<approx>\<^sub>v \<infinity>\<^sub>v" "\<not> u \<approx>\<^sub>v \<infinity>\<^sub>v" "\<not> v \<approx>\<^sub>v \<infinity>\<^sub>v" "\<not> w \<approx>\<^sub>v \<infinity>\<^sub>v"

  hence ***: "?n1 * ?n2 \<noteq> 0 \<or> ?d1 * ?d2 \<noteq> 0"
    using *
    using complex_cvec_eq_mix[of z1 z2 u1 u2] complex_cvec_eq_mix[of v1 v2 w1 w2]
    using complex_cvec_eq_mix[of z1 z2 w1 w2] complex_cvec_eq_mix[of u1 u2 v1 v2]
    by (metis eq_iff_diff_eq_0 mult.commute mult_eq_0_iff)

  have ****: "z2 \<noteq> 0" "w2 \<noteq> 0" "u2 \<noteq> 0" "v2 \<noteq> 0"
    using * **(1-4) **(6-9)
    using inf_cvec_z2_zero_iff[of z1 z2]
    using inf_cvec_z2_zero_iff[of u1 u2]
    using inf_cvec_z2_zero_iff[of v1 v2]
    using inf_cvec_z2_zero_iff[of w1 w2]
    by blast+

  have "cross_ratio_cvec z u v w = (?n1*?n2, ?d1*?d2)"
    using * ***
    by simp
  moreover
  let ?k = "z2*u2*v2*w2"
  have "(z +\<^sub>v ~\<^sub>v u) *\<^sub>v (v +\<^sub>v ~\<^sub>v w) *\<^sub>v reciprocal_cvec ((z +\<^sub>v ~\<^sub>v w) *\<^sub>v (v +\<^sub>v ~\<^sub>v u)) = (?k * ?n1 * ?n2, ?k * ?d1 * ?d2)"
    using * *** ****
    by auto
  ultimately
  show "cross_ratio_cvec z u v w \<approx>\<^sub>v
           (z +\<^sub>v ~\<^sub>v u) *\<^sub>v (v +\<^sub>v ~\<^sub>v w) *\<^sub>v reciprocal_cvec ((z +\<^sub>v ~\<^sub>v w) *\<^sub>v (v +\<^sub>v ~\<^sub>v u))"
    using ****
    unfolding complex_cvec_eq_def
    by (rule_tac x="?k" in exI) simp
qed

end

(*
(* Although it seems useful, we did not use this. *)

text \<open>Transfer extended complex plane to complex plane\<close>

definition HC :: "complex_homo \<Rightarrow> complex \<Rightarrow> bool"
  where "HC = (\<lambda> h c. h = of_complex c)"

lemma Domainp_HC [transfer_domain_rule]: "Domainp HC = (\<lambda> x. x \<noteq> \<infinity>\<^sub>h)"
  unfolding HC_def Domainp_iff[abs_def]
  apply (rule ext)
  using inf_or_of_complex
  by auto

lemma bi_unique_HC [transfer_rule]: "bi_unique HC"
  using of_complex_inj
  unfolding HC_def bi_unique_def
  by auto

lemma right_total_HC [transfer_rule]: "right_total HC"
  unfolding HC_def right_total_def
  by auto

lemma HC_0 [transfer_rule]: "HC 0\<^sub>h 0"
  unfolding HC_def
  by simp

lemma HC_1 [transfer_rule]: "HC 1\<^sub>h 1"
  unfolding HC_def
  by simp

context includes lifting_syntax
begin
lemma HC_add [transfer_rule]: "(HC ===> HC ===> HC) (op +\<^sub>h) (op +)"
  unfolding rel_fun_def HC_def
  by auto

lemma HC_mult [transfer_rule]: "(HC ===> HC ===> HC) (op *\<^sub>h) ( op * )"
  unfolding rel_fun_def HC_def
  by auto

lemma HC_All [transfer_rule]:
  "((HC ===> op =) ===> op =) (Ball {z. z \<noteq> \<infinity>\<^sub>h}) All"
  using inf_or_of_complex
  unfolding rel_fun_def HC_def
  by auto

lemma HC_transfer_forall [transfer_rule]:
  "((HC ===> op =) ===> op =) (transfer_bforall (\<lambda>x. x \<noteq> \<infinity>\<^sub>h)) transfer_forall"
  using inf_or_of_complex
  unfolding transfer_forall_def transfer_bforall_def
  unfolding rel_fun_def HC_def
  by auto
end
*)
