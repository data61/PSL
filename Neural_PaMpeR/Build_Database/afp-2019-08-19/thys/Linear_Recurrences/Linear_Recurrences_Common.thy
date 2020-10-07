(*
  File:    Linear_Recurrence_Common.thy
  Author:  Manuel Eberl, TU München
*)
section \<open>Material common to homogenous and inhomogenous linear recurrences\<close>
theory Linear_Recurrences_Common
imports
  Complex_Main 
  "HOL-Computational_Algebra.Computational_Algebra"
begin

definition lr_fps_denominator where
  "lr_fps_denominator cs = Poly (rev cs)"

lemma lr_fps_denominator_code [code abstract]:
  "coeffs (lr_fps_denominator cs) = rev (dropWhile ((=) 0) cs)"
  by (simp add: lr_fps_denominator_def)
 
definition lr_fps_denominator' where
  "lr_fps_denominator' cs = Poly cs"

lemma lr_fps_denominator'_code [code abstract]:
  "coeffs (lr_fps_denominator' cs) = strip_while ((=) 0) cs"
  by (simp add: lr_fps_denominator'_def)

lemma lr_fps_denominator_nz: "last cs \<noteq> 0 \<Longrightarrow> cs \<noteq> [] \<Longrightarrow> lr_fps_denominator cs \<noteq> 0"
  unfolding lr_fps_denominator_def
  by (subst coeffs_eq_iff) (auto simp: poly_eq_iff intro!: bexI[of _ "last cs"])

lemma lr_fps_denominator'_nz: "last cs \<noteq> 0 \<Longrightarrow> cs \<noteq> [] \<Longrightarrow> lr_fps_denominator' cs \<noteq> 0"
  unfolding lr_fps_denominator'_def
  by (subst coeffs_eq_iff) (auto simp: poly_eq_iff intro!: bexI[of _ "last cs"])  

end
