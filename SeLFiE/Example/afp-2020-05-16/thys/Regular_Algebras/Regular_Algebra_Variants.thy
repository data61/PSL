(* Title:      Regular Algebras
   Author:     Simon Foster, Georg Struth
   Maintainer: Simon Foster <s.foster at york.ac.uk>
               Georg Struth <g.struth at sheffield.ac.uk>               
*)

section \<open>Variants of Regular Algebra\<close>

theory Regular_Algebra_Variants
  imports Regular_Algebras Pratts_Counterexamples
begin

text \<open>Replacing Kozen's induction axioms by Boffa's leads to incompleteness.\<close>

lemma (in star_dioid) 
  assumes "\<And>x. 1 + x \<cdot> x\<^sup>\<star> =  x\<^sup>\<star>"
  and "\<And>x. 1 + x\<^sup>\<star> \<cdot> x =  x\<^sup>\<star>"
  and "\<And>x. x \<cdot> x = x \<Longrightarrow> x\<^sup>\<star> = 1 + x"
  shows "\<And>x y. (x + y)\<^sup>\<star> = x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
(*  nitpick [expect=genuine] --"5-element counterexample"*)
oops

lemma (in star_dioid) 
  assumes "\<And>x. 1 + x \<cdot> x\<^sup>\<star> =  x\<^sup>\<star>"
  and "\<And>x. 1 + x\<^sup>\<star> \<cdot> x =  x\<^sup>\<star>"
  and "\<And>x. x \<cdot> x = x \<Longrightarrow> x\<^sup>\<star> = 1 + x"
  shows "\<And>x y. x \<le> y \<longrightarrow> x\<^sup>\<star> \<le> y\<^sup>\<star>"
(*  nitpick [expect=genuine] --"5-element counterexample"*)
oops 

lemma (in star_dioid) 
  assumes "\<And>x. 1 + x \<cdot> x\<^sup>\<star> =  x\<^sup>\<star>"
  and "\<And>x. 1 + x\<^sup>\<star> \<cdot> x =  x\<^sup>\<star>"
  and "\<And>x y. 1 + x \<le> y \<and> y \<cdot> y \<le> y \<longrightarrow> x\<^sup>\<star> \<le> y"
  shows "\<And>x. 1 + x \<le> x\<^sup>\<star>"
  by (metis add_iso_r assms(1) mult_oner subdistl)

lemma (in star_dioid) 
  assumes "\<And>x. 1 + x \<cdot> x\<^sup>\<star> =  x\<^sup>\<star>"
  and "\<And>x. 1 + x\<^sup>\<star> \<cdot> x =  x\<^sup>\<star>"
  and "\<And>x y. 1 + x \<le> y \<and> y \<cdot> y \<le> y \<longrightarrow> x\<^sup>\<star> \<le> y"
  shows "\<And>x. x\<^sup>\<star> = (1 + x)\<^sup>\<star>"
oops \<comment> \<open>need to reconsider this\<close>

lemma (in star_dioid) 
  assumes "\<And>x. 1 + x \<cdot> x\<^sup>\<star> =  x\<^sup>\<star>"
  and "\<And>x. 1 + x\<^sup>\<star> \<cdot> x =  x\<^sup>\<star>"
  and "\<And>x y. 1 + x + y \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<le> y"
  shows "\<And>x. x\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
oops

lemma (in star_dioid) 
  assumes "\<And>x. 1 + x \<cdot> x\<^sup>\<star> =  x\<^sup>\<star>"
  and "\<And>x. 1 + x\<^sup>\<star> \<cdot> x =  x\<^sup>\<star>"
  and "\<And>x y z. x \<cdot> y = y \<cdot> z \<Longrightarrow> x\<^sup>\<star> \<cdot> y = y \<cdot> z\<^sup>\<star>"
  shows "1\<^sup>\<star> = 1"
(*  nitpick -- "3-element counterexample"*)
oops

lemma (in star_dioid) 
  assumes "\<And>x. 1 + x \<cdot> x\<^sup>\<star> =  x\<^sup>\<star>"
  and "\<And>x. 1 + x\<^sup>\<star> \<cdot> x =  x\<^sup>\<star>"
  and "\<And>x y z. x \<cdot> y \<le> y \<cdot> z \<Longrightarrow> x\<^sup>\<star> \<cdot> y \<le> y \<cdot> z\<^sup>\<star>"
  and "\<And>x y z. y \<cdot> x \<le> z \<cdot> y \<Longrightarrow> y \<cdot> x\<^sup>\<star> \<le> z\<^sup>\<star> \<cdot> y"
  shows "1\<^sup>\<star> = 1"
(*  nitpick [expect=genuine] -- "3-element counterexample"*)
oops

lemma (in star_dioid) 
  assumes "\<And>x. 1 + x \<cdot> x\<^sup>\<star> =  x\<^sup>\<star>"
  and "\<And>x. 1 + x\<^sup>\<star> \<cdot> x =  x\<^sup>\<star>"
  and "\<And>x y. x = y \<cdot> x \<Longrightarrow> x = y\<^sup>\<star> \<cdot> x"
  and "\<And>x y. x = x \<cdot> y \<Longrightarrow> x = x \<cdot> y\<^sup>\<star>"
  shows "\<And>x y. y \<cdot> x \<le> y \<Longrightarrow> y \<cdot> x\<^sup>\<star> \<le> y"
oops

class C3l_var = conway_dioid +
  assumes C3l_var: "z + x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y"

class C3r_var = conway_dioid +
  assumes C3r_var: "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"

class C3_var = C3l_var + C3r_var

sublocale C3l_var \<subseteq> C3l_algebra
  apply unfold_locales
  by (simp add: local.C3l_var)

sublocale C3l_algebra \<subseteq> C3l_var
  by (unfold_locales, metis star_inductl_var)

sublocale C3_var \<subseteq> C3_algebra
  apply unfold_locales
  by (simp add: local.C3r_var)

sublocale C3_algebra \<subseteq> C3_var
  by (unfold_locales, metis star_inductr_var)

class Brtc_algebra = star_dioid +
  assumes rtc1: "1 + x\<^sup>\<star> \<cdot> x\<^sup>\<star> + x \<le> x\<^sup>\<star>"
  and rtc2: "1 + x + y \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<le> y"

sublocale B2_algebra \<subseteq> Brtc_algebra
proof 
  fix x y
  show "1 + x\<^sup>\<star> \<cdot> x\<^sup>\<star> + x \<le> x\<^sup>\<star>"
    by (simp add: local.star_ext)
  show "1 + x + y \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<le> y"
    by (metis B23 local.join.le_sup_iff eq_iff mult_1_right subdistl)
qed

sublocale Brtc_algebra \<subseteq> B2_algebra
proof 
  fix x y
  show "1 + x \<le> x\<^sup>\<star>"
    by (metis rtc1 join.le_sup_iff)
  show "x\<^sup>\<star> \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
  proof (rule antisym)
    show "x\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
      by (metis rtc1 join.le_sup_iff)
    show "x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> x\<^sup>\<star>"
      by (metis rtc1 add.commute join.le_sup_iff less_eq_def mult_isor mult_onel)
  qed
  show "\<lbrakk> 1 + x \<le> y; y \<cdot> y = y \<rbrakk> \<Longrightarrow> x\<^sup>\<star> \<le> y"
    by (metis rtc2 eq_refl less_eq_def)
qed

class wB1_algebra = conway_dioid +
  assumes wR: "x \<cdot> x \<le> x \<Longrightarrow> x\<^sup>\<star> = 1 + x"

sublocale wB1_algebra \<subseteq> B1_algebra
  by (unfold_locales, metis order_refl wR)

lemma (in B1_algebra) one_plus_star:  "x\<^sup>\<star> = (1 + x)\<^sup>\<star>"
  by (metis C11_var R add_idem' mult_onel mult_oner)

sublocale B1_algebra \<subseteq> wB1_algebra
proof unfold_locales
  fix x :: 'a
  assume "x \<cdot> x \<le> x"
  hence "x \<cdot> (1 + x) = x"
    by (simp add: local.distrib_left local.join.sup_absorb1)
  hence "(1 + x) \<cdot> (1 + x) = 1 + x"
    using add.left_commute distrib_right' by simp
  thus "x\<^sup>\<star> = 1 + x"
    by (metis R add_assoc' add_idem' one_plus_star)
qed

end
