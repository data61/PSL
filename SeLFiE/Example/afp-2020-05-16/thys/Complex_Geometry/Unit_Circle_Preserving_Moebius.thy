(* ---------------------------------------------------------------------------- *)
section \<open>Unit circle preserving Möbius transformations\<close>
(* ---------------------------------------------------------------------------- *)

text \<open>In this section we shall examine Möbius transformations that map the unit circle onto itself.
We shall say that they fix or preserve the unit circle (although, they do not need to fix each of
its points).\<close>

theory Unit_Circle_Preserving_Moebius
imports Unitary11_Matrices Moebius Oriented_Circlines
begin

(* ---------------------------------------------------------------------------- *)
subsection \<open>Möbius transformations that fix the unit circle\<close>
(* ---------------------------------------------------------------------------- *)

text \<open>We define Möbius transformations that preserve unit circle as transformations represented by
generalized unitary matrices with the $1-1$ signature (elements of the gruop $GU_{1,1}(2,
\mathbb{C})$, defined earlier in the theory Unitary11Matrices).\<close>

lift_definition unit_circle_fix_mmat :: "moebius_mat \<Rightarrow> bool" is unitary11_gen
  done

lift_definition unit_circle_fix :: "moebius \<Rightarrow> bool" is unit_circle_fix_mmat
  apply transfer
  apply (auto simp del: mult_sm.simps)
  apply (simp del: mult_sm.simps add: unitary11_gen_mult_sm)
  apply (simp del: mult_sm.simps add: unitary11_gen_div_sm)
  done

text \<open>Our algebraic characterisation (by matrices) is geometrically correct.\<close>

lemma unit_circle_fix_iff:
  shows "unit_circle_fix M \<longleftrightarrow> 
         moebius_circline M unit_circle = unit_circle" (is "?rhs = ?lhs")
proof
  assume ?lhs
  thus ?rhs
  proof (transfer, transfer)
    fix M :: complex_mat
    assume "mat_det M \<noteq> 0"
    assume "circline_eq_cmat (moebius_circline_cmat_cmat M unit_circle_cmat) unit_circle_cmat"
    then obtain k where "k \<noteq> 0" "(1, 0, 0, -1) = cor k *\<^sub>s\<^sub>m congruence (mat_inv M) (1, 0, 0, -1)"
      by auto
    hence "(1/cor k, 0, 0, -1/cor k) = congruence (mat_inv M) (1, 0, 0, -1)"
      using mult_sm_inv_l[of "cor k" "congruence (mat_inv M) (1, 0, 0, -1)" ]
      by simp
    hence "congruence M (1/cor k, 0, 0, -1/cor k) = (1, 0, 0, -1)"
      using \<open>mat_det M \<noteq> 0\<close> mat_det_inv[of M]
      using congruence_inv[of "mat_inv M" "(1, 0, 0, -1)" "(1/cor k, 0, 0, -1/cor k)"]
      by simp
    hence "congruence M (1, 0, 0, -1) = cor k *\<^sub>s\<^sub>m (1, 0, 0, -1)"
      using congruence_scale_m[of "M" "1/cor k" "(1, 0, 0, -1)"]
      using mult_sm_inv_l[of "1/ cor k" "congruence M (1, 0, 0, -1)"  "(1, 0, 0, -1)"] \<open>k \<noteq> 0\<close>
      by simp
    thus "unitary11_gen M"
      using \<open>k \<noteq> 0\<close>
      unfolding unitary11_gen_def
      by simp
  qed
next
  assume ?rhs
  thus ?lhs
  proof (transfer, transfer)
    fix M :: complex_mat
    assume "mat_det M \<noteq> 0"
    assume "unitary11_gen M"
    hence "unitary11_gen (mat_inv M)"
      using \<open>mat_det M \<noteq> 0\<close>
      using unitary11_gen_mat_inv
      by simp
    thus " circline_eq_cmat (moebius_circline_cmat_cmat M unit_circle_cmat) unit_circle_cmat"
      unfolding unitary11_gen_real
      by auto (rule_tac x="1/k" in exI, simp)
  qed
qed

lemma circline_set_fix_iff_circline_fix:
  assumes "circline_set H' \<noteq> {}"
  shows "circline_set (moebius_circline M H) = circline_set H' \<longleftrightarrow> 
         moebius_circline M H = H'"
  using assms
  by auto (rule inj_circline_set, auto)

lemma unit_circle_fix_iff_unit_circle_set:
  shows "unit_circle_fix M \<longleftrightarrow> moebius_pt M ` unit_circle_set = unit_circle_set"
proof-
  have "circline_set unit_circle \<noteq> {}"
    using one_in_unit_circle_set
    by auto
  thus ?thesis
    using unit_circle_fix_iff[of M] circline_set_fix_iff_circline_fix[of unit_circle M unit_circle]
    by (simp add: unit_circle_set_def)
qed


text \<open>Unit circle preserving Möbius transformations form a group. \<close>

lemma unit_circle_fix_id_moebius [simp]:
  shows "unit_circle_fix id_moebius"
  by (transfer, transfer, simp add: unitary11_gen_def mat_adj_def mat_cnj_def)

lemma unit_circle_fix_moebius_add [simp]:
  assumes "unit_circle_fix M1" and "unit_circle_fix M2"
  shows "unit_circle_fix (M1 + M2)"
  using assms
  unfolding unit_circle_fix_iff
  by auto

lemma unit_circle_fix_moebius_comp [simp]:
  assumes "unit_circle_fix M1" and "unit_circle_fix M2"
  shows "unit_circle_fix (moebius_comp M1 M2)"
  using unit_circle_fix_moebius_add[OF assms]
  by simp

lemma unit_circle_fix_moebius_uminus [simp]:
  assumes "unit_circle_fix M"
  shows "unit_circle_fix (-M)"
  using assms
  unfolding unit_circle_fix_iff
  by (metis moebius_circline_comp_inv_left uminus_moebius_def)

lemma unit_circle_fix_moebius_inv [simp]:
  assumes "unit_circle_fix M"
  shows "unit_circle_fix (moebius_inv M)"
  using unit_circle_fix_moebius_uminus[OF assms]
  by simp

text \<open>Unit circle fixing transforms preserve inverse points.\<close>

lemma unit_circle_fix_moebius_pt_inversion [simp]:
  assumes "unit_circle_fix M"
  shows "moebius_pt M (inversion z) = inversion (moebius_pt M z)"
  using assms
  using symmetry_principle[of z "inversion z" unit_circle M]
  using unit_circle_fix_iff[of M, symmetric]
  using circline_symmetric_inv_homo_disc[of z]
  using circline_symmetric_inv_homo_disc'[of "moebius_pt M z" "moebius_pt M (inversion z)"]
  by metis

(* -------------------------------------------------------------------------- *)
subsection \<open>Möbius transformations that fix the imaginary unit circle\<close>
(* -------------------------------------------------------------------------- *)

text \<open>Only for completeness we show that Möbius transformations that preserve the imaginary unit
circle are exactly those characterised by generalized unitary matrices (with the (2, 0) signature).\<close>
lemma imag_unit_circle_fixed_iff_unitary_gen:
  assumes "mat_det (A, B, C, D) \<noteq> 0"
  shows "moebius_circline (mk_moebius A B C D) imag_unit_circle = imag_unit_circle \<longleftrightarrow>
         unitary_gen (A, B, C, D)" (is "?lhs = ?rhs")
proof
  assume ?lhs
  thus ?rhs
    using assms
  proof (transfer, transfer)
    fix A B C D :: complex
    let ?M = "(A, B, C, D)" and ?E = "(1, 0, 0, 1)"
    assume "circline_eq_cmat (moebius_circline_cmat_cmat (mk_moebius_cmat A B C D) imag_unit_circle_cmat) imag_unit_circle_cmat"
           "mat_det ?M \<noteq> 0"
    then obtain k where "k \<noteq> 0" "?E = cor k *\<^sub>s\<^sub>m congruence (mat_inv ?M) ?E"
      by auto
    hence "unitary_gen (mat_inv ?M)"
      using mult_sm_inv_l[of "cor k" "congruence (mat_inv ?M) ?E" "?E"]
      unfolding unitary_gen_def
      by (metis congruence_def divide_eq_0_iff eye_def mat_eye_r of_real_eq_0_iff one_neq_zero)
    thus "unitary_gen ?M"
      using unitary_gen_inv[of "mat_inv ?M"] \<open>mat_det ?M \<noteq> 0\<close>
      by (simp del: mat_inv.simps)
  qed
next
  assume ?rhs
  thus ?lhs
    using assms
  proof (transfer, transfer)
    fix A B C D :: complex
    let ?M = "(A, B, C, D)" and ?E = "(1, 0, 0, 1)"
    assume "unitary_gen ?M" "mat_det ?M \<noteq> 0"
    hence "unitary_gen (mat_inv ?M)"
      using unitary_gen_inv[of ?M]
      by simp
    then obtain k where "k \<noteq> 0" "mat_adj (mat_inv ?M) *\<^sub>m\<^sub>m (mat_inv ?M) = cor k *\<^sub>s\<^sub>m eye"
      using unitary_gen_real[of "mat_inv ?M"] mat_det_inv[of ?M]
      by auto
    hence *: "?E = (1 / cor k) *\<^sub>s\<^sub>m (mat_adj (mat_inv ?M) *\<^sub>m\<^sub>m (mat_inv ?M))"
      using mult_sm_inv_l[of "cor k" eye "mat_adj (mat_inv ?M) *\<^sub>m\<^sub>m (mat_inv ?M)"]
      by simp
    have "\<exists>k. k \<noteq> 0 \<and>
            (1, 0, 0, 1) = cor k *\<^sub>s\<^sub>m (mat_adj (mat_inv (A, B, C, D)) *\<^sub>m\<^sub>m (1, 0, 0, 1) *\<^sub>m\<^sub>m mat_inv (A, B, C, D))"
      using \<open>mat_det ?M \<noteq> 0\<close> \<open>k \<noteq> 0\<close> 
      by (metis "*" Im_complex_of_real Re_complex_of_real \<open>mat_adj (mat_inv ?M) *\<^sub>m\<^sub>m mat_inv ?M = cor k *\<^sub>s\<^sub>m eye\<close> complex_of_real_Re eye_def mat_eye_l mult_mm_assoc mult_mm_sm mult_sm_eye_mm of_real_1 of_real_divide of_real_eq_1_iff zero_eq_1_divide_iff)
    thus "circline_eq_cmat (moebius_circline_cmat_cmat (mk_moebius_cmat A B C D) imag_unit_circle_cmat) imag_unit_circle_cmat"
      using \<open>mat_det ?M \<noteq> 0\<close> \<open>k \<noteq> 0\<close> 
      by (simp del: mat_inv.simps)
  qed
qed

(* -------------------------------------------------------------------------- *)
subsection \<open>Möbius transformations that fix the oriented unit circle and the unit disc\<close>
(* -------------------------------------------------------------------------- *)

text \<open>Möbius transformations that fix the unit circle either map the unit disc onto itself or
exchange it with its exterior. The transformations that fix the unit disc can be recognized from
their matrices -- they have the form as before, but additionally it must hold that $|a|^2 > |b|^2$.\<close>
  
definition unit_disc_fix_cmat :: "complex_mat \<Rightarrow> bool" where
 [simp]: "unit_disc_fix_cmat M \<longleftrightarrow>
          (let (A, B, C, D) = M
            in unitary11_gen (A, B, C, D) \<and> (B = 0 \<or> Re ((A*D)/(B*C)) > 1))"

lift_definition unit_disc_fix_mmat :: "moebius_mat \<Rightarrow> bool" is unit_disc_fix_cmat
  done

lift_definition unit_disc_fix :: "moebius \<Rightarrow> bool" is unit_disc_fix_mmat
proof transfer
  fix M M' :: complex_mat
  assume det: "mat_det M \<noteq> 0" "mat_det M' \<noteq> 0"
  assume "moebius_cmat_eq M M'"
  then obtain k where *: "k \<noteq> 0" "M' = k *\<^sub>s\<^sub>m M"
    by auto
  hence **: "unitary11_gen M \<longleftrightarrow> unitary11_gen M'"
    using unitary11_gen_mult_sm[of k M] unitary11_gen_div_sm[of k M]
    by auto
  obtain A B C D where MM: "(A, B, C, D) = M"
    by (cases M) auto
  obtain A' B' C' D' where MM': "(A', B', C', D') = M'"
    by (cases M') auto

  show "unit_disc_fix_cmat M = unit_disc_fix_cmat M'"
    using * ** MM MM'
    by auto
qed

text \<open>Transformations that fix the unit disc also fix the unit circle.\<close>
lemma unit_disc_fix_unit_circle_fix [simp]:
  assumes "unit_disc_fix M"
  shows "unit_circle_fix M"
  using assms
  by (transfer, transfer, auto)

text \<open>Transformations that preserve the unit disc preserve the orientation of the unit circle.\<close>
lemma unit_disc_fix_iff_ounit_circle:
  shows "unit_disc_fix M \<longleftrightarrow> 
         moebius_ocircline M ounit_circle = ounit_circle" (is "?rhs \<longleftrightarrow> ?lhs")
proof
  assume *: ?lhs
  have "moebius_circline M unit_circle = unit_circle"
    apply (subst moebius_circline_ocircline[of M unit_circle])
    apply (subst of_circline_unit_circle)
    apply (subst *)
    by simp

  hence "unit_circle_fix M"
    by (simp add: unit_circle_fix_iff)
  thus ?rhs
    using *
  proof (transfer, transfer)
    fix M :: complex_mat
    assume "mat_det M \<noteq> 0"
    let ?H = "(1, 0, 0, -1)"
    obtain A B C D where MM: "(A, B, C, D) = M"
      by (cases M) auto
    assume "unitary11_gen M" "ocircline_eq_cmat (moebius_circline_cmat_cmat M unit_circle_cmat) unit_circle_cmat"
    then obtain k where "0 < k" "?H = cor k *\<^sub>s\<^sub>m congruence (mat_inv M) ?H"
      by auto
    hence "congruence M ?H = cor k *\<^sub>s\<^sub>m ?H"
      using congruence_inv[of "mat_inv M" "?H" "(1/cor k) *\<^sub>s\<^sub>m ?H"] \<open>mat_det M \<noteq> 0\<close>
      using mult_sm_inv_l[of "cor k" "congruence (mat_inv M) ?H" "?H"]
      using mult_sm_inv_l[of "1/cor k" "congruence M ?H"]
      using congruence_scale_m[of M "1/cor k" "?H"]
      by (auto simp add: mat_det_inv)
    then obtain a b k' where "k' \<noteq> 0" "M = k' *\<^sub>s\<^sub>m (a, b, cnj b, cnj a)" "sgn (Re (mat_det (a, b, cnj b, cnj a))) = 1"
      using unitary11_sgn_det_orientation'[of M k] \<open>k > 0\<close>
      by auto
    moreover
    have "mat_det (a, b, cnj b, cnj a) \<noteq> 0"
      using \<open>sgn (Re (mat_det (a, b, cnj b, cnj a))) = 1\<close>
      by (smt sgn_0 zero_complex.simps(1))
    ultimately
    show "unit_disc_fix_cmat M"
      using unitary11_sgn_det[of k' a b M A B C D]
      using MM[symmetric] \<open>k > 0\<close> \<open>unitary11_gen M\<close>
      by (simp add: sgn_1_pos split: if_split_asm)
  qed
next
  assume ?rhs
  thus ?lhs
  proof (transfer, transfer)
    fix M :: complex_mat
    assume "mat_det M \<noteq> 0"

    obtain A B C D where MM: "(A, B, C, D) = M"
      by (cases M) auto
    assume "unit_disc_fix_cmat M"
    hence "unitary11_gen M" "B = 0 \<or> 1 < Re (A * D / (B * C))"
      using MM[symmetric]
      by auto
    have "sgn (if B = 0 then 1 else sgn (Re (A * D / (B * C)) - 1)) = 1"
      using \<open>B = 0 \<or> 1 < Re (A * D / (B * C))\<close>
      by auto
    then obtain k' where "k' > 0" "congruence M (1, 0, 0, -1) = cor k' *\<^sub>s\<^sub>m (1, 0, 0, -1)"
      using unitary11_orientation[OF \<open>unitary11_gen M\<close> MM[symmetric]]
      by (auto simp add: sgn_1_pos)
    thus "ocircline_eq_cmat (moebius_circline_cmat_cmat M unit_circle_cmat) unit_circle_cmat"
      using congruence_inv[of M "(1, 0, 0, -1)" "cor k' *\<^sub>s\<^sub>m (1, 0, 0, -1)"] \<open>mat_det M \<noteq> 0\<close>
      using congruence_scale_m[of "mat_inv M" "cor k'" "(1, 0, 0, -1)"]
      by auto
  qed
qed


text \<open>Our algebraic characterisation (by matrices) is geometrically correct.\<close>

lemma unit_disc_fix_iff [simp]:
  assumes "unit_disc_fix M"
  shows "moebius_pt M ` unit_disc = unit_disc"
  using assms
  using unit_disc_fix_iff_ounit_circle[of M]
  unfolding unit_disc_def
  by (subst disc_moebius_ocircline[symmetric], simp)

lemma unit_disc_fix_discI [simp]:
  assumes "unit_disc_fix M" and "u \<in> unit_disc"
  shows "moebius_pt M u \<in> unit_disc"
  using unit_disc_fix_iff assms
  by blast

text \<open>Unit disc preserving transformations form a group.\<close>

lemma unit_disc_fix_id_moebius [simp]:
  shows "unit_disc_fix id_moebius"
  by (transfer, transfer, simp add: unitary11_gen_def mat_adj_def mat_cnj_def)

lemma unit_disc_fix_moebius_add [simp]:
  assumes "unit_disc_fix M1" and "unit_disc_fix M2"
  shows "unit_disc_fix (M1 + M2)"
  using assms
  unfolding unit_disc_fix_iff_ounit_circle
  by auto

lemma unit_disc_fix_moebius_comp [simp]:
  assumes "unit_disc_fix M1" and "unit_disc_fix M2"
  shows "unit_disc_fix (moebius_comp M1 M2)"
  using unit_disc_fix_moebius_add[OF assms]
  by simp

lemma unit_disc_fix_moebius_uminus [simp]:
  assumes "unit_disc_fix M"
  shows "unit_disc_fix (-M)"
  using assms
  unfolding unit_disc_fix_iff_ounit_circle
  by (metis moebius_ocircline_comp_inv_left uminus_moebius_def)

lemma unit_disc_fix_moebius_inv [simp]:
  assumes "unit_disc_fix M"
  shows "unit_disc_fix (moebius_inv M)"
  using unit_disc_fix_moebius_uminus[OF assms]
  by simp

(* -------------------------------------------------------------------------- *)
subsection \<open>Rotations are unit disc preserving transformations\<close>
(* -------------------------------------------------------------------------- *)

lemma unit_disc_fix_rotation [simp]:
  shows "unit_disc_fix (moebius_rotation \<phi>)"      
  unfolding moebius_rotation_def moebius_similarity_def
  by (transfer, transfer, simp add: unitary11_gen_def mat_adj_def mat_cnj_def cis_mult)

lemma moebius_rotation_unit_circle_fix [simp]:
  shows "moebius_pt (moebius_rotation \<phi>) u \<in> unit_circle_set \<longleftrightarrow> u \<in> unit_circle_set"
  using moebius_pt_moebius_inv_in_set unit_circle_fix_iff_unit_circle_set
  by fastforce

lemma ex_rotation_mapping_u_to_positive_x_axis:
  assumes "u \<noteq> 0\<^sub>h" and "u \<noteq> \<infinity>\<^sub>h"
  shows "\<exists> \<phi>. moebius_pt (moebius_rotation \<phi>) u \<in> positive_x_axis"
proof-
  from assms obtain c where *: "u = of_complex c"
    using inf_or_of_complex
    by blast
  have "is_real (cis (- arg c) * c)" "Re (cis (-arg c) * c) > 0"
    using "*" assms is_real_rot_to_x_axis positive_rot_to_x_axis of_complex_zero_iff
    by blast+
  thus ?thesis
    using *
    by (rule_tac x="-arg c" in exI) (simp add: positive_x_axis_def circline_set_x_axis)
qed

lemma ex_rotation_mapping_u_to_positive_y_axis:
  assumes "u \<noteq> 0\<^sub>h" and "u \<noteq> \<infinity>\<^sub>h"
  shows "\<exists> \<phi>. moebius_pt (moebius_rotation \<phi>) u \<in> positive_y_axis"
proof-
  from assms obtain c where *: "u = of_complex c"
    using inf_or_of_complex
    by blast
  have "is_imag (cis (pi/2 - arg c) * c)" "Im (cis (pi/2 - arg c) * c) > 0"
    using "*" assms is_real_rot_to_x_axis positive_rot_to_x_axis of_complex_zero_iff
    by - (simp, simp, simp add: field_simps)
  thus ?thesis
    using *
    by (rule_tac x="pi/2-arg c" in exI) (simp add: positive_y_axis_def circline_set_y_axis)
qed

lemma wlog_rotation_to_positive_x_axis:
  assumes in_disc: "u \<in> unit_disc" and not_zero: "u \<noteq> 0\<^sub>h"
  assumes preserving: "\<And>\<phi> u. \<lbrakk>u \<in> unit_disc; u \<noteq> 0\<^sub>h; P (moebius_pt (moebius_rotation \<phi>) u)\<rbrakk> \<Longrightarrow> P u"
  assumes x_axis: "\<And>x. \<lbrakk>is_real x; 0 < Re x; Re x < 1\<rbrakk> \<Longrightarrow> P (of_complex x)"
  shows "P u"
proof-
  from in_disc obtain \<phi> where *:
    "moebius_pt (moebius_rotation \<phi>) u \<in> positive_x_axis"
    using ex_rotation_mapping_u_to_positive_x_axis[of u]
    using inf_notin_unit_disc not_zero
    by blast
  let ?Mu = "moebius_pt (moebius_rotation \<phi>) u"
  have "P ?Mu"
  proof-
    let ?x = "to_complex ?Mu"
    have "?Mu \<in> unit_disc" "?Mu \<noteq> 0\<^sub>h" "?Mu \<noteq> \<infinity>\<^sub>h"
      using \<open>u \<in> unit_disc\<close> \<open>u \<noteq> 0\<^sub>h\<close>
      by auto
    hence "is_real (to_complex ?Mu)"  "0 < Re ?x" "Re ?x < 1"
      using *
      unfolding positive_x_axis_def circline_set_x_axis
      by (auto simp add: cmod_eq_Re)
    thus ?thesis
      using x_axis[of ?x] \<open>?Mu \<noteq> \<infinity>\<^sub>h\<close>
      by simp
  qed
  thus ?thesis
    using preserving[OF in_disc] not_zero
    by simp
qed

lemma wlog_rotation_to_positive_x_axis':
  assumes not_zero: "u \<noteq> 0\<^sub>h" and not_inf: "u \<noteq> \<infinity>\<^sub>h"
  assumes preserving: "\<And>\<phi> u. \<lbrakk>u \<noteq> 0\<^sub>h; u \<noteq> \<infinity>\<^sub>h; P (moebius_pt (moebius_rotation \<phi>) u)\<rbrakk> \<Longrightarrow> P u"
  assumes x_axis: "\<And>x. \<lbrakk>is_real x; 0 < Re x\<rbrakk> \<Longrightarrow> P (of_complex x)"
  shows "P u"
proof-
  from not_zero and not_inf obtain \<phi> where *:
    "moebius_pt (moebius_rotation \<phi>) u \<in> positive_x_axis"
    using ex_rotation_mapping_u_to_positive_x_axis[of u]
    using inf_notin_unit_disc
    by blast
  let ?Mu = "moebius_pt (moebius_rotation \<phi>) u"
  have "P ?Mu"
  proof-
    let ?x = "to_complex ?Mu"
    have "?Mu \<noteq> 0\<^sub>h" "?Mu \<noteq> \<infinity>\<^sub>h"
      using \<open>u \<noteq> \<infinity>\<^sub>h\<close> \<open>u \<noteq> 0\<^sub>h\<close>
      by auto
    hence "is_real (to_complex ?Mu)"  "0 < Re ?x"
      using *
      unfolding positive_x_axis_def circline_set_x_axis
      by (auto simp add: cmod_eq_Re)
    thus ?thesis
      using x_axis[of ?x] \<open>?Mu \<noteq> \<infinity>\<^sub>h\<close>
      by simp
  qed
  thus ?thesis
    using preserving[OF not_zero not_inf]
    by simp
qed

lemma wlog_rotation_to_positive_y_axis:
  assumes in_disc: "u \<in> unit_disc" and not_zero: "u \<noteq> 0\<^sub>h"
  assumes preserving: "\<And>\<phi> u. \<lbrakk>u \<in> unit_disc; u \<noteq> 0\<^sub>h; P (moebius_pt (moebius_rotation \<phi>) u)\<rbrakk> \<Longrightarrow> P u"
  assumes y_axis: "\<And>x. \<lbrakk>is_imag x; 0 < Im x; Im x < 1\<rbrakk> \<Longrightarrow> P (of_complex x)"
  shows "P u"
proof-
  from in_disc and not_zero obtain \<phi> where *:
    "moebius_pt (moebius_rotation \<phi>) u \<in> positive_y_axis"
    using ex_rotation_mapping_u_to_positive_y_axis[of u]
    using inf_notin_unit_disc
    by blast
  let ?Mu = "moebius_pt (moebius_rotation \<phi>) u"
  have "P ?Mu"
  proof-
    let ?y = "to_complex ?Mu"
    have "?Mu \<in> unit_disc" "?Mu \<noteq> 0\<^sub>h" "?Mu \<noteq> \<infinity>\<^sub>h"
      using \<open>u \<in> unit_disc\<close> \<open>u \<noteq> 0\<^sub>h\<close>
      by auto
    hence "is_imag (to_complex ?Mu)"  "0 < Im ?y" "Im ?y < 1"
      using *
      unfolding positive_y_axis_def circline_set_y_axis
      by (auto simp add: cmod_eq_Im)
    thus ?thesis
      using y_axis[of ?y] \<open>?Mu \<noteq> \<infinity>\<^sub>h\<close>
      by simp
  qed
  thus ?thesis
    using preserving[OF in_disc not_zero]
    by simp
qed

(* ---------------------------------------------------------------------------- *)
subsection \<open>Blaschke factors are unit disc preserving transformations\<close>
(* ---------------------------------------------------------------------------- *)

text \<open>For a given point $a$, Blaschke factor transformations are of the form $k \cdot
\left(\begin{array}{cc}1 & -a\\ -\overline{a} & 1\end{array}\right)$. It is a disc preserving
Möbius transformation that maps the point $a$ to zero (by the symmetry principle, it must map the
inverse point of $a$ to infinity).\<close>

definition blaschke_cmat :: "complex \<Rightarrow> complex_mat" where
 [simp]: "blaschke_cmat a = (if cmod a \<noteq> 1 then (1, -a, -cnj a, 1) else eye)"
lift_definition blaschke_mmat :: "complex \<Rightarrow> moebius_mat" is blaschke_cmat
  by simp
lift_definition blaschke :: "complex \<Rightarrow> moebius" is blaschke_mmat
  done

lemma blaschke_0_id [simp]: "blaschke 0 = id_moebius"
  by (transfer, transfer, simp)

lemma blaschke_a_to_zero [simp]:
  assumes "cmod a \<noteq> 1"
  shows "moebius_pt (blaschke a) (of_complex a) = 0\<^sub>h"
  using assms
  by (transfer, transfer, simp)

lemma blaschke_inv_a_inf [simp]:
  assumes "cmod a \<noteq> 1"
  shows "moebius_pt (blaschke a) (inversion (of_complex a)) = \<infinity>\<^sub>h"
  using assms
  unfolding inversion_def
  by (transfer, transfer) (simp add: vec_cnj_def, rule_tac x="1/(1 - a*cnj a)" in exI, simp)

lemma blaschke_inf [simp]:
  assumes "cmod a < 1" and "a \<noteq> 0"
  shows "moebius_pt (blaschke a) \<infinity>\<^sub>h = of_complex (- 1 / cnj a)"
  using assms
  by (transfer, transfer, simp add: complex_mod_sqrt_Re_mult_cnj)

lemma blaschke_0_minus_a [simp]:
  assumes "cmod a \<noteq> 1"
  shows "moebius_pt (blaschke a) 0\<^sub>h = ~\<^sub>h (of_complex a)"
  using assms
  by (transfer, transfer, simp)
                                                
lemma blaschke_unit_circle_fix [simp]:
  assumes "cmod a \<noteq> 1"
  shows "unit_circle_fix (blaschke a)"
  using assms
  by (transfer, transfer) (simp add: unitary11_gen_def mat_adj_def mat_cnj_def)

lemma blaschke_unit_disc_fix [simp]:
  assumes "cmod a < 1"
  shows "unit_disc_fix (blaschke a)"
  using assms
proof (transfer, transfer)
  fix a
  assume *: "cmod a < 1"
  show "unit_disc_fix_cmat (blaschke_cmat a)"
  proof (cases "a = 0")
    case True
    thus ?thesis
      by (simp add: unitary11_gen_def mat_adj_def mat_cnj_def)
  next
    case False
    hence "Re (a * cnj a) < 1"
      using *
      by (metis complex_mod_sqrt_Re_mult_cnj real_sqrt_lt_1_iff)
    hence "1 / Re (a * cnj a) > 1"
      using False
      by (smt complex_div_gt_0 less_divide_eq_1_pos one_complex.simps(1) right_inverse_eq)
    hence "Re (1 / (a * cnj a)) > 1"
      by (simp add: complex_is_Real_iff)
    thus ?thesis
      by (simp add: unitary11_gen_def mat_adj_def mat_cnj_def)
  qed
qed

lemma blaschke_unit_circle_fix':
  assumes "cmod a \<noteq> 1"
  shows "moebius_circline (blaschke a) unit_circle = unit_circle"
  using assms
  using blaschke_unit_circle_fix unit_circle_fix_iff
  by simp

lemma blaschke_ounit_circle_fix':
  assumes "cmod a < 1"
  shows "moebius_ocircline (blaschke a) ounit_circle = ounit_circle"
proof-
  have "Re (a * cnj a) < 1"
    using assms
    by (metis complex_mod_sqrt_Re_mult_cnj real_sqrt_lt_1_iff)
  thus ?thesis
    using assms
    using blaschke_unit_disc_fix unit_disc_fix_iff_ounit_circle
    by simp
qed

lemma moebius_pt_blaschke [simp]:
  assumes "cmod a \<noteq> 1" and "z \<noteq> 1 / cnj a"
  shows "moebius_pt (blaschke a) (of_complex z) = of_complex ((z - a) / (1 - cnj a * z))"
  using assms
proof (cases "a = 0")
  case True
  thus ?thesis
    by auto
next
  case False
  thus ?thesis
    using assms
    apply (transfer, transfer)
    apply (simp add: complex_mod_sqrt_Re_mult_cnj)
    apply (rule_tac x="1 / (1 - cnj a * z)" in exI)
    apply (simp add: field_simps)
    done
qed

(* -------------------------------------------------------------------------- *)
subsubsection \<open>Blaschke factors for a real point $a$\<close>
(* -------------------------------------------------------------------------- *)

text \<open>If the point $a$ is real, the Blaschke factor preserve x-axis and the upper and the lower
halfplane.\<close>

lemma blaschke_real_preserve_x_axis [simp]:
  assumes "is_real a" and "cmod a < 1"
  shows "moebius_pt (blaschke a) z \<in> circline_set x_axis \<longleftrightarrow> z \<in> circline_set x_axis"
proof (cases "a = 0")
  case True
  thus ?thesis
    by simp
next
  case False
  have "cmod a \<noteq> 1"
    using assms
    by linarith
  let ?a = "of_complex a"
  let ?i = "inversion ?a"
  let ?M = "moebius_pt (blaschke a)"
  have *: "?M ?a = 0\<^sub>h" "?M ?i = \<infinity>\<^sub>h" "?M 0\<^sub>h = of_complex (-a)"
    using \<open>cmod a \<noteq> 1\<close> blaschke_a_to_zero[of a] blaschke_inv_a_inf[of a] blaschke_0_minus_a[of a]
    by auto
  let ?Mx = "moebius_circline (blaschke a) x_axis"
  have "?a \<in> circline_set x_axis" "?i \<in> circline_set x_axis" "0\<^sub>h \<in> circline_set x_axis"
    using \<open>is_real a\<close> \<open>a \<noteq> 0\<close> eq_cnj_iff_real[of a]
    by auto
  hence "0\<^sub>h \<in> circline_set ?Mx" "\<infinity>\<^sub>h \<in> circline_set ?Mx" "of_complex (-a) \<in> circline_set ?Mx"
    using *
    apply -                          
    apply (force simp add: image_iff)+
    apply (simp add: image_iff, rule_tac x="0\<^sub>h" in bexI, simp_all)   
    done
  moreover
  have "0\<^sub>h \<in> circline_set x_axis" "\<infinity>\<^sub>h \<in> circline_set x_axis" "of_complex (-a) \<in> circline_set x_axis"
    using \<open>is_real a\<close> 
    by auto
  moreover
  have "of_complex (-a) \<noteq> 0\<^sub>h"
    using \<open>a \<noteq> 0\<close>
    by simp
  hence "0\<^sub>h \<noteq> of_complex (-a)"
    by metis
  hence "\<exists>!H. 0\<^sub>h \<in> circline_set H \<and> \<infinity>\<^sub>h \<in> circline_set H \<and> of_complex (- a) \<in> circline_set H"
    using unique_circline_set[of "0\<^sub>h" "\<infinity>\<^sub>h" "of_complex (-a)"] \<open>a \<noteq> 0\<close>
    by simp
  ultimately
  have "moebius_circline (blaschke a) x_axis = x_axis"
    by auto
  thus ?thesis
    by (metis circline_set_moebius_circline_iff)
qed

lemma blaschke_real_preserve_sgn_Im [simp]:
  assumes "is_real a" and "cmod a < 1" and "z \<noteq> \<infinity>\<^sub>h" and "z \<noteq> inversion (of_complex a)"
  shows "sgn (Im (to_complex (moebius_pt (blaschke a) z))) = sgn (Im (to_complex z))"
proof (cases "a = 0")
  case True
  thus ?thesis
    by simp
next
  case False
  obtain z' where z': "z = of_complex z'"
    using inf_or_of_complex[of z] \<open>z \<noteq> \<infinity>\<^sub>h\<close>
    by auto
  have "z' \<noteq> 1 / cnj a"
    using assms z' \<open>a \<noteq> 0\<close>
    by (auto simp add: of_complex_inj)
  moreover
  have "a * cnj a \<noteq> 1"
    using \<open>cmod a < 1\<close>
    by auto (simp add: complex_mod_sqrt_Re_mult_cnj)
  moreover
  have "sgn (Im ((z' - a) / (1 - a * z'))) = sgn (Im z')"
  proof-
    have "a * z' \<noteq> 1"
      using \<open>is_real a\<close> \<open>z' \<noteq> 1 / cnj a\<close> \<open>a \<noteq> 0\<close> eq_cnj_iff_real[of a]
      by (simp add: field_simps)
    moreover                             
    have "Re (1 - a\<^sup>2) > 0"
      using \<open>is_real a\<close> \<open>cmod a < 1\<close>
      by (smt Re_power2 minus_complex.simps(1) norm_complex_def one_complex.simps(1) power2_less_0 real_sqrt_lt_1_iff)
    moreover
    have "Im ((z' - a) / (1 - a * z')) = Re (((1 - a\<^sup>2) * Im z') / (cmod (1 - a*z'))\<^sup>2)"
    proof-
      have "1 - a * cnj z' \<noteq> 0"
        using \<open>z' \<noteq> 1 / cnj a\<close>
        by (metis Im_complex_div_eq_0  complex_cnj_zero_iff diff_eq_diff_eq diff_numeral_special(9) eq_divide_imp is_real_div mult_not_zero one_complex.simps(2) zero_neq_one)
      hence "Im ((z' - a) / (1 - a * z')) = Im (((z' - a) * (1 - a * cnj z')) / ((1 - a * z') * cnj (1 - a * z')))"
        using \<open>is_real a\<close> eq_cnj_iff_real[of a]
        by simp
      also have "... = Im ((z' - a - a * z' * cnj z' + a\<^sup>2 * cnj z') / (cmod (1 - a*z'))\<^sup>2)"
        unfolding complex_mult_cnj_cmod
        by (simp add: power2_eq_square field_simps)
      finally show ?thesis
        using \<open>is_real a\<close>
        by (simp add: field_simps) 
    qed
    moreover
    have "0 < (1 - (Re a)\<^sup>2) * Im z' / (cmod (1 - a * z'))\<^sup>2 \<Longrightarrow> Im z' > 0"
      using `is_real a` `0 < Re (1 - a\<^sup>2)` 
      by (smt Re_power_real divide_le_0_iff minus_complex.simps(1) not_sum_power2_lt_zero one_complex.simps(1) zero_less_mult_pos)
    ultimately
    show ?thesis
      unfolding sgn_real_def
      using \<open>cmod a < 1\<close> \<open>a * z' \<noteq> 1\<close> \<open>is_real a\<close>
      by (auto simp add: cmod_eq_Re)
  qed
  ultimately
  show ?thesis
    using assms z' moebius_pt_blaschke[of a z'] \<open>is_real a\<close> eq_cnj_iff_real[of a]                  
    by simp
qed

lemma blaschke_real_preserve_sgn_arg [simp]:
  assumes "is_real a" and "cmod a < 1" and "z \<notin> circline_set x_axis"
  shows "sgn (arg (to_complex (moebius_pt (blaschke a) z))) = sgn (arg (to_complex z))"
proof-
  have "z \<noteq> \<infinity>\<^sub>h"
    using assms
    using special_points_on_x_axis''(3) by blast
  moreover
  have "z \<noteq> inversion (of_complex a)"
    using assms
    by (metis calculation circline_equation_x_axis circline_set_x_axis_I conjugate_of_complex inversion_of_complex inversion_sym is_real_inversion o_apply of_complex_zero reciprocal_zero to_complex_of_complex)
  ultimately
  show ?thesis
    using blaschke_real_preserve_sgn_Im[OF assms(1) assms(2), of z]
    by (smt arg_Im_sgn assms(3) circline_set_x_axis_I norm_sgn of_complex_to_complex)
qed

(* -------------------------------------------------------------------------- *)
subsubsection \<open>Inverse Blaschke transform\<close>
(* -------------------------------------------------------------------------- *)

definition inv_blaschke_cmat :: "complex \<Rightarrow> complex_mat" where
 [simp]: "inv_blaschke_cmat a = (if cmod a \<noteq> 1 then (1, a, cnj a, 1) else eye)"
lift_definition inv_blaschke_mmat :: "complex \<Rightarrow> moebius_mat" is inv_blaschke_cmat
  by simp
lift_definition inv_blaschke :: "complex \<Rightarrow> moebius" is inv_blaschke_mmat
  done

lemma inv_blaschke_neg [simp]: "inv_blaschke a = blaschke (-a)"
  by (transfer, transfer) simp

lemma inv_blaschke:
  assumes "cmod a \<noteq> 1"
  shows "blaschke a + inv_blaschke a = 0"
  apply simp
  apply (transfer, transfer)
  by auto (rule_tac x="1/(1 - a*cnj a)" in exI, simp)

lemma ex_unit_disc_fix_mapping_u_to_zero:
  assumes "u \<in> unit_disc"
  shows "\<exists> M. unit_disc_fix M \<and> moebius_pt M u = 0\<^sub>h"
proof-
  from assms obtain c where *: "u = of_complex c"
    by (metis inf_notin_unit_disc inf_or_of_complex)
  hence "cmod c < 1"
    using assms unit_disc_iff_cmod_lt_1
    by simp
  thus ?thesis
    using *
    by (rule_tac x="blaschke c" in exI)
       (smt blaschke_a_to_zero blaschke_ounit_circle_fix' unit_disc_fix_iff_ounit_circle)
qed

lemma wlog_zero:
  assumes in_disc: "u \<in> unit_disc"
  assumes preserving: "\<And> a u. \<lbrakk>u \<in> unit_disc; cmod a < 1; P (moebius_pt (blaschke a) u)\<rbrakk> \<Longrightarrow> P u"
  assumes zero: "P 0\<^sub>h"
  shows "P u"
proof-
  have *: "moebius_pt (blaschke (to_complex u)) u = 0\<^sub>h"
    by (smt blaschke_a_to_zero in_disc inf_notin_unit_disc of_complex_to_complex unit_disc_iff_cmod_lt_1)
  thus ?thesis
    using preserving[of u "to_complex u"] in_disc zero
    using inf_or_of_complex[of u]
    by auto
qed

lemma wlog_real_zero:
  assumes in_disc: "u \<in> unit_disc" and real: "is_real (to_complex u)"
  assumes preserving: "\<And> a u. \<lbrakk>u \<in> unit_disc; is_real a; cmod a < 1; P (moebius_pt (blaschke a) u)\<rbrakk> \<Longrightarrow> P u"
  assumes zero: "P 0\<^sub>h"
  shows "P u"
proof-
  have *: "moebius_pt (blaschke (to_complex u)) u = 0\<^sub>h"
    by (smt blaschke_a_to_zero in_disc inf_notin_unit_disc of_complex_to_complex unit_disc_iff_cmod_lt_1)
  thus ?thesis
    using preserving[of u "to_complex u"] in_disc zero real
    using inf_or_of_complex[of u]
    by auto
qed

lemma unit_disc_fix_transitive:
  assumes in_disc: "u \<in> unit_disc" and "u' \<in> unit_disc"
  shows "\<exists> M. unit_disc_fix M \<and> moebius_pt M u = u'"
proof-
  have "\<forall> u \<in> unit_disc. \<exists> M. unit_disc_fix M \<and> moebius_pt M u = u'" (is "?P u'")
  proof (rule wlog_zero)
    show "u' \<in> unit_disc" by fact
  next
    show "?P 0\<^sub>h"
      by (simp add: ex_unit_disc_fix_mapping_u_to_zero)
  next
    fix a u
    assume "cmod a < 1" and *: "?P (moebius_pt (blaschke a) u)"
    show "?P u"
    proof
      fix u'
      assume "u' \<in> unit_disc"
      then obtain M' where "unit_disc_fix M'" "moebius_pt M' u' = moebius_pt (blaschke a) u"
        using *
        by auto
      thus "\<exists>M. unit_disc_fix M \<and> moebius_pt M u' = u"
        using \<open>cmod a < 1\<close> blaschke_unit_disc_fix[of a]
        using unit_disc_fix_moebius_comp[of "- blaschke a" "M'"]
        using unit_disc_fix_moebius_inv[of "blaschke a"]
        by (rule_tac x="(- (blaschke a)) + M'" in exI, simp)
    qed
  qed
  thus ?thesis
    using assms
    by auto
qed

(* -------------------------------------------------------------------------- *)
subsection \<open>Decomposition of unit disc preserving Möbius transforms\<close>
(* -------------------------------------------------------------------------- *)

text \<open>Each transformation preserving unit disc can be decomposed to a rotation around the origin and
a Blaschke factors that maps a point within the unit disc to zero.\<close>

lemma unit_disc_fix_decompose_blaschke_rotation:
  assumes "unit_disc_fix M"
  shows "\<exists> k \<phi>. cmod k < 1 \<and> M = moebius_rotation \<phi> + blaschke k"
  using assms
  unfolding moebius_rotation_def moebius_similarity_def
proof (simp, transfer, transfer)
  fix M
  assume *: "mat_det M \<noteq> 0" "unit_disc_fix_cmat M"
  then obtain k a b :: complex where
    **: "k \<noteq> 0" "mat_det (a, b, cnj b, cnj a) \<noteq> 0" "M = k *\<^sub>s\<^sub>m (a, b, cnj b, cnj a)"
    using unitary11_gen_iff[of M]
    by auto
  have "a \<noteq> 0"
    using * **
    by auto
  then obtain a' k' \<phi>
    where ***: "k' \<noteq> 0 \<and> a' * cnj a' \<noteq> 1 \<and> M = k' *\<^sub>s\<^sub>m (cis \<phi>, 0, 0, 1) *\<^sub>m\<^sub>m (1, - a', - cnj a', 1)"
    using ** unitary11_gen_cis_blaschke[of k M a b]
    by auto
  have "a' = 0 \<or> 1 < 1 / (cmod a')\<^sup>2"
    using * *** complex_mult_cnj_cmod[of a']
    by simp
  hence "cmod a' < 1"
    by (smt less_divide_eq_1_pos norm_zero one_less_power one_power2 pos2)
  thus "\<exists>k. cmod k < 1 \<and>
            (\<exists>\<phi>. moebius_cmat_eq M (moebius_comp_cmat (mk_moebius_cmat (cis \<phi>) 0 0 1) (blaschke_cmat k)))"
    using ***
    apply (rule_tac x=a' in exI)
    apply simp
    apply (rule_tac x=\<phi> in exI)
    apply simp
    apply (rule_tac x="1/k'" in exI)
    by auto
qed

lemma wlog_unit_disc_fix:
  assumes "unit_disc_fix M"
  assumes b: "\<And> k. cmod k < 1 \<Longrightarrow> P (blaschke k)"
  assumes r: "\<And> \<phi>. P (moebius_rotation \<phi>)"
  assumes comp: "\<And>M1 M2. \<lbrakk>unit_disc_fix M1; P M1; unit_disc_fix M2; P M2\<rbrakk> \<Longrightarrow> P (M1 + M2)"
  shows "P M"
  using assms
  using unit_disc_fix_decompose_blaschke_rotation[OF assms(1)]
  using blaschke_unit_disc_fix
  by auto

lemma ex_unit_disc_fix_to_zero_positive_x_axis:
  assumes "u \<in> unit_disc" and "v \<in> unit_disc" and "u \<noteq> v"
  shows "\<exists> M. unit_disc_fix M \<and>
              moebius_pt M u = 0\<^sub>h \<and> moebius_pt M v \<in> positive_x_axis"
proof-
  from assms obtain B where
    *: "unit_disc_fix B" "moebius_pt B u = 0\<^sub>h"
    using ex_unit_disc_fix_mapping_u_to_zero
    by blast

  let ?v = "moebius_pt B v"
  have "?v \<in> unit_disc"
    using \<open>v \<in> unit_disc\<close> *
    by auto
  hence "?v \<noteq> \<infinity>\<^sub>h"
    using inf_notin_unit_disc by auto
  have "?v \<noteq> 0\<^sub>h"
    using \<open>u \<noteq> v\<close> *
    by (metis moebius_pt_invert)

  obtain R where
    "unit_disc_fix R"
    "moebius_pt R 0\<^sub>h = 0\<^sub>h" "moebius_pt R ?v \<in> positive_x_axis"
    using ex_rotation_mapping_u_to_positive_x_axis[of ?v] \<open>?v \<noteq> 0\<^sub>h\<close> \<open>?v \<noteq> \<infinity>\<^sub>h\<close>
    using moebius_pt_rotation_inf_iff moebius_pt_moebius_rotation_zero unit_disc_fix_rotation
    by blast
  thus ?thesis
    using * moebius_comp[of R B, symmetric]
    using unit_disc_fix_moebius_comp
    by (rule_tac x="R + B" in exI) (simp add: comp_def)
qed

lemma wlog_x_axis:
  assumes in_disc: "u \<in> unit_disc" "v \<in> unit_disc"
  assumes preserved: "\<And> M u v. \<lbrakk>unit_disc_fix M; u \<in> unit_disc; v \<in> unit_disc; P (moebius_pt M u) (moebius_pt M v)\<rbrakk> \<Longrightarrow> P u v"
  assumes axis: "\<And> x. \<lbrakk>is_real x; 0 \<le> Re x;  Re x < 1\<rbrakk> \<Longrightarrow> P 0\<^sub>h (of_complex x)"
  shows "P u v"
proof (cases "u = v")
  case True
  have "P u u" (is "?Q u")
  proof (rule wlog_zero[where P="?Q"])
    show "u \<in> unit_disc"
      by fact
  next
    show "?Q 0\<^sub>h"
      using axis[of 0]
      by simp
  next
    fix a u
    assume "u \<in> unit_disc" "cmod a < 1" "?Q (moebius_pt (blaschke a) u)"
    thus "?Q u"
      using preserved[of "blaschke a" u u]
      using blaschke_unit_disc_fix[of a]
      by simp
  qed
  thus ?thesis
    using True
    by simp
next
  case False
  from in_disc obtain M where
    *: "unit_disc_fix M" "moebius_pt M u = 0\<^sub>h" "moebius_pt M v \<in> positive_x_axis"
    using ex_unit_disc_fix_to_zero_positive_x_axis False
    by auto
  then obtain x where **: "moebius_pt M v = of_complex x" "is_real x"
    unfolding positive_x_axis_def circline_set_x_axis
    by auto
  moreover
  have "of_complex x \<in> unit_disc"
    using \<open>unit_disc_fix M\<close> \<open>v \<in> unit_disc\<close> **
    using unit_disc_fix_discI
    by fastforce
  hence "0 < Re x" "Re x < 1"
    using \<open>moebius_pt M v \<in> positive_x_axis\<close> **
    by (auto simp add: positive_x_axis_def cmod_eq_Re)
  ultimately
  have "P 0\<^sub>h (of_complex x)"
    using \<open>is_real x\<close> axis
    by auto
  thus ?thesis
    using preserved[OF *(1) assms(1-2)] *(2) **(1)
    by simp
qed

lemma wlog_positive_x_axis:
  assumes in_disc: "u \<in> unit_disc" "v \<in> unit_disc" "u \<noteq> v"
  assumes preserved: "\<And> M u v. \<lbrakk>unit_disc_fix M; u \<in> unit_disc; v \<in> unit_disc; u \<noteq> v; P (moebius_pt M u) (moebius_pt M v)\<rbrakk> \<Longrightarrow> P u v"
  assumes axis: "\<And> x. \<lbrakk>is_real x; 0 < Re x;  Re x < 1\<rbrakk> \<Longrightarrow> P 0\<^sub>h (of_complex x)"
  shows "P u v"
proof-
  have "u \<noteq> v \<longrightarrow> P u v" (is "?Q u v")
  proof (rule wlog_x_axis)
    show "u \<in> unit_disc" "v \<in> unit_disc"
      by fact+
  next
    fix M u v
    assume "unit_disc_fix M" "u \<in> unit_disc" "v \<in> unit_disc"
           "?Q (moebius_pt M u) (moebius_pt M v)"
    thus "?Q u v"
      using preserved[of M u v]
      using moebius_pt_invert
      by blast
  next
    fix x
    assume "is_real x" "0 \<le> Re x" "Re x < 1"
    thus "?Q 0\<^sub>h (of_complex x)"
      using axis[of x] of_complex_zero_iff[of x] complex.expand[of x 0]
      by fastforce
  qed
  thus ?thesis
    using \<open>u \<noteq> v\<close>
    by simp
qed

(* -------------------------------------------------------------------------- *)
subsection \<open>All functions that fix the unit disc\<close>
(* -------------------------------------------------------------------------- *)

text \<open>It can be proved that continuous functions that fix the unit disc are either actions of
Möbius transformations that fix the unit disc (homographies), or are compositions of actions of
Möbius transformations that fix the unit disc and the conjugation (antihomographies). We postulate
this as a definition, but it this characterisation could also be formally shown (we do not need this
for our further applications).\<close>

definition unit_disc_fix_f where
  "unit_disc_fix_f f \<longleftrightarrow> 
   (\<exists> M. unit_disc_fix M \<and> (f = moebius_pt M \<or> f = moebius_pt M \<circ> conjugate))"

text \<open>Unit disc fixing functions really fix unit disc.\<close>
lemma unit_disc_fix_f_unit_disc:
  assumes "unit_disc_fix_f M"
  shows "M ` unit_disc = unit_disc"
  using assms
  unfolding unit_disc_fix_f_def
  using image_comp
  by force

text \<open>Actions of unit disc fixing Möbius transformations (unit disc fixing homographies) are unit
disc fixing functions.\<close>
lemma unit_disc_fix_f_moebius_pt [simp]:
  assumes "unit_disc_fix M"
  shows "unit_disc_fix_f (moebius_pt M)"
  using assms
  unfolding unit_disc_fix_f_def
  by auto

text \<open>Compositions of unit disc fixing Möbius transformations and conjugation (unit disc fixing
antihomographies) are unit disc fixing functions.\<close>
lemma unit_disc_fix_conjugate_moebius [simp]:
  assumes "unit_disc_fix M"
  shows "unit_disc_fix (conjugate_moebius M)"
proof-
  have "\<And>a aa ab b. \<lbrakk>1 < Re (a * b / (aa * ab)); \<not> 1 < Re (cnj a * cnj b / (cnj aa * cnj ab))\<rbrakk> \<Longrightarrow> aa = 0"
    by (metis cnj.simps(1) complex_cnj_divide complex_cnj_mult)
  thus ?thesis
    using assms
    by (transfer, transfer)
       (auto simp add: mat_cnj_def unitary11_gen_def mat_adj_def field_simps)
qed

lemma unit_disc_fix_conjugate_comp_moebius [simp]:
  assumes "unit_disc_fix M"
  shows "unit_disc_fix_f (conjugate \<circ> moebius_pt M)"
  using assms
  apply (subst conjugate_moebius)
  apply (simp add: unit_disc_fix_f_def)
  apply (rule_tac x="conjugate_moebius M" in exI, simp)
  done


text \<open>Uniti disc fixing functions form a group under function composition.\<close>

lemma unit_disc_fix_f_comp [simp]:
  assumes "unit_disc_fix_f f1" and "unit_disc_fix_f f2"
  shows "unit_disc_fix_f (f1 \<circ> f2)"
  using assms
  apply (subst (asm) unit_disc_fix_f_def)
  apply (subst (asm) unit_disc_fix_f_def)
proof safe
  fix M M'
  assume "unit_disc_fix M" "unit_disc_fix M'"
  thus "unit_disc_fix_f (moebius_pt M \<circ> moebius_pt M')"
    unfolding unit_disc_fix_f_def
    by (rule_tac x="M + M'" in exI) auto
next
  fix M M'
  assume "unit_disc_fix M" "unit_disc_fix M'"
  thus "unit_disc_fix_f (moebius_pt M \<circ> (moebius_pt M' \<circ> conjugate))"
    unfolding unit_disc_fix_f_def
    by (subst comp_assoc[symmetric])+
       (rule_tac x="M + M'" in exI, auto)
next
  fix M M'
  assume "unit_disc_fix M" "unit_disc_fix M'"
  thus "unit_disc_fix_f ((moebius_pt M \<circ> conjugate) \<circ> moebius_pt M')"
    unfolding unit_disc_fix_f_def
    by (subst comp_assoc, subst conjugate_moebius, subst comp_assoc[symmetric])+
       (rule_tac x="M + conjugate_moebius M'" in exI, auto)
next
  fix M M'
  assume "unit_disc_fix M" "unit_disc_fix M'"
  thus "unit_disc_fix_f ((moebius_pt M \<circ> conjugate) \<circ> (moebius_pt M' \<circ> conjugate))"
    apply (subst comp_assoc[symmetric], subst comp_assoc)
    apply (subst conjugate_moebius, subst comp_assoc, subst comp_assoc)
    apply (simp add: unit_disc_fix_f_def)
    apply (rule_tac x="M + conjugate_moebius M'" in exI, auto)
    done
qed

lemma unit_disc_fix_f_inv:
  assumes "unit_disc_fix_f M"
  shows "unit_disc_fix_f (inv M)"
  using assms
  apply (subst (asm) unit_disc_fix_f_def)
proof safe
  fix M
  assume "unit_disc_fix M"
  have "inv (moebius_pt M) = moebius_pt (-M)"
    by (rule ext) (simp add: moebius_inv)
  thus "unit_disc_fix_f (inv (moebius_pt M))"
    using \<open>unit_disc_fix M\<close>
    unfolding unit_disc_fix_f_def
    by (rule_tac x="-M" in exI, simp)
next
  fix M
  assume "unit_disc_fix M"
  have "inv (moebius_pt M \<circ> conjugate) = conjugate \<circ> inv (moebius_pt M)"
    by (subst o_inv_distrib, simp_all)
  also have "... = conjugate \<circ> (moebius_pt (-M))"
    using moebius_inv
    by auto
  also have "... = moebius_pt (conjugate_moebius (-M)) \<circ> conjugate"
    by (simp add: conjugate_moebius)
  finally
  show "unit_disc_fix_f (inv (moebius_pt M \<circ> conjugate))"
    using \<open>unit_disc_fix M\<close>
    unfolding unit_disc_fix_f_def
    by (rule_tac x="conjugate_moebius (-M)" in exI, simp)
qed

(* -------------------------------------------------------------------------- *)
subsubsection \<open>Action of unit disc fixing functions on circlines\<close>
(* -------------------------------------------------------------------------- *)

definition unit_disc_fix_f_circline where
  "unit_disc_fix_f_circline f H = 
      (if \<exists> M. unit_disc_fix M \<and> f = moebius_pt M then
          moebius_circline (THE M. unit_disc_fix M \<and> f = moebius_pt M) H
       else if \<exists> M. unit_disc_fix M \<and> f = moebius_pt M \<circ> conjugate then
          (moebius_circline (THE M. unit_disc_fix M \<and> f = moebius_pt M \<circ> conjugate) \<circ> conjugate_circline) H
       else
          H)"


lemma unique_moebius_pt_conjugate:
  assumes "moebius_pt M1 \<circ> conjugate = moebius_pt M2 \<circ> conjugate"
  shows "M1 = M2"
proof-               
  from assms have "moebius_pt M1 = moebius_pt M2"
    using conjugate_conjugate_comp rewriteL_comp_comp2 by fastforce
  thus ?thesis
    using unique_moebius_pt
    by auto
qed

lemma unit_disc_fix_f_circline_direct:
  assumes "unit_disc_fix M" and "f = moebius_pt M"
  shows "unit_disc_fix_f_circline f H = moebius_circline M H"
proof-
  have "M = (THE M. unit_disc_fix M \<and> f = moebius_pt M)"
    using assms
    using theI_unique[of "\<lambda> M. unit_disc_fix M \<and> f = moebius_pt M" M]
    using unique_moebius_pt[of M]
    by auto
  thus ?thesis
    using assms
    unfolding unit_disc_fix_f_circline_def
    by auto
qed

lemma unit_disc_fix_f_circline_indirect:
  assumes "unit_disc_fix M" and "f = moebius_pt M \<circ> conjugate"
  shows "unit_disc_fix_f_circline f H = ((moebius_circline M) \<circ> conjugate_circline) H"
proof-
  have "\<not> (\<exists> M. unit_disc_fix M \<and> f = moebius_pt M)"
    using assms homography_antihomography_exclusive[of f]
    unfolding is_homography_def is_antihomography_def is_moebius_def
    by auto
  moreover
  have "M = (THE M. unit_disc_fix M \<and> f = moebius_pt M \<circ> conjugate)"
    using assms
    using theI_unique[of "\<lambda> M. unit_disc_fix M \<and> f = moebius_pt M \<circ> conjugate" M]
    using unique_moebius_pt_conjugate[of M] 
    by auto
  ultimately
  show ?thesis
    using assms
    unfolding unit_disc_fix_f_circline_def
    by metis
qed

text \<open>Disc automorphisms - it would be nice to show that there are no disc automorphisms other than
unit disc fixing homographies and antihomographies, but this part of the theory is not yet
developed.\<close>

definition is_disc_aut where "is_disc_aut f \<longleftrightarrow> bij_betw f unit_disc unit_disc"

end