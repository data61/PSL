(* Title:      Action Algebra
   Author:     Alasdair Armstrong, Georg Struth, Tjark Weber
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

section \<open>Action Algebras\<close>

theory Action_Algebra
imports "../Residuated_Lattices/Residuated_Lattices" Kleene_Algebra.Kleene_Algebra
begin

text \<open>Action algebras have been defined and discussed in œ
Pratt's paper on \emph{Action Logic and Pure
Induction}~\cite{pratt90action}. They are expansions of Kleene
algebras by operations of left and right residuation. They are
interesting, first because most models of Kleene algebras, e.g.
relations, traces, paths and languages, possess the residuated
structure, and second because, in this setting, the Kleene star can be
defined equationally.

Action algebras can be based on residuated
semilattices. Many important properties of action
algebras already arise at this level.\<close>

text \<open>We can define an action algebra as a residuated join
semilattice that is also a dioid. Following Pratt, we also add a star
operation that is axiomatised as a reflexive transitive closure
operation.
\<close>

class action_algebra = residuated_sup_lgroupoid + dioid_one_zero + star_op +
  assumes star_rtc1: "1 + x\<^sup>\<star> \<cdot> x\<^sup>\<star> + x \<le> x\<^sup>\<star>"
  and star_rtc2: "1 + y \<cdot> y + x \<le> y \<Longrightarrow> x\<^sup>\<star> \<le> y"
begin

lemma plus_sup: "(+) = (\<squnion>)"
  by (rule ext)+ (simp add: local.join.sup_unique)

text \<open>We first prove a reflexivity property for residuals.\<close>

lemma residual_r_refl: "1 \<le> x \<rightarrow> x"
  by (simp add: local.resrI)

lemma residual_l_refl: "1 \<le> x \<leftarrow> x"
  by (simp add: local.reslI)

text \<open>We now derive pure induction laws for residuals.\<close>


lemma residual_l_pure_induction: "(x \<leftarrow> x)\<^sup>\<star> \<le> x \<leftarrow> x"
proof -
  have "1 + (x \<leftarrow> x) \<cdot> (x \<leftarrow> x) + (x \<leftarrow> x) \<le> (x \<leftarrow> x)"
    using local.resl_antitoner local.resl_galois mult_assoc by auto
  thus ?thesis
    by (fact star_rtc2)
qed

lemma residual_r_pure_induction: "(x \<rightarrow> x)\<^sup>\<star> \<le> x \<rightarrow> x"
proof -
  have "1 + (x \<rightarrow> x) \<cdot> (x \<rightarrow> x) + (x \<rightarrow> x) \<le> (x \<rightarrow> x)"
    using local.resr_antitonel local.resr_galois mult_assoc apply clarsimp
    by (metis local.mult_oner residual_r_refl)
  thus ?thesis
    by (fact star_rtc2)
qed

text \<open>Next we show that every action algebra is a Kleene
algebra. First, we derive the star unfold law and the star induction
laws in action algebra. Then we prove a subclass statement.\<close>

lemma star_unfoldl: "1 + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
proof -
  have "x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (meson local.dual_order.trans local.join.le_sup_iff local.mult_isor local.star_rtc1)
  thus ?thesis
    using local.star_rtc1 by auto
qed

lemma star_mon [intro]: "x \<le> y \<Longrightarrow> x\<^sup>\<star> \<le> y\<^sup>\<star>"
proof -
  assume "x \<le> y"
  hence "x \<le> y\<^sup>\<star>"
    by (meson local.dual_order.trans local.join.le_supE local.star_rtc1)
  hence "1 + x + y\<^sup>\<star> \<cdot> y\<^sup>\<star> \<le> y\<^sup>\<star>"
    using local.star_rtc1 by auto
  thus "x\<^sup>\<star> \<le> y\<^sup>\<star>"
    by (simp add: local.star_rtc2)
qed

lemma star_subdist': "x\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
  by force

lemma star_inductl: "z + x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y"
proof -
  assume hyp: "z + x \<cdot> y \<le> y"
  hence "x \<le> y \<leftarrow> y"
    by (simp add: local.resl_galois)
  hence "x\<^sup>\<star> \<le> (y \<leftarrow> y)\<^sup>\<star>"
    by (fact star_mon)
  hence "x\<^sup>\<star> \<le> y \<leftarrow> y"
    using local.order_trans residual_l_pure_induction by blast
  hence "x\<^sup>\<star> \<cdot> y \<le> y"
    by (simp add: local.resl_galois)
  thus "x\<^sup>\<star> \<cdot> z \<le> y"
    by (meson hyp local.dual_order.trans local.join.le_supE local.mult_isol)
qed

lemma star_inductr: "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"
proof -
  assume hyp: "z + y \<cdot> x \<le> y"
  hence "x \<le> y \<rightarrow> y"
    by (simp add: resr_galois)
  hence "x\<^sup>\<star> \<le> (y \<rightarrow> y)\<^sup>\<star>"
    by (fact star_mon)
  hence "x\<^sup>\<star> \<le> y \<rightarrow> y"
    by (metis order_trans residual_r_pure_induction)
  hence "y \<cdot> x\<^sup>\<star> \<le> y"
    by (simp add: local.resr_galois)
  thus "z \<cdot> x\<^sup>\<star> \<le> y"
    by (meson hyp local.join.le_supE local.order_trans local.resl_galois)
qed

subclass kleene_algebra
proof
  fix x y z
  show "1 + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    using local.star_unfoldl by blast
  show "z + x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y"
    by (simp add: local.star_inductl)    
  show "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"
    by (simp add: star_inductr)
qed
    
end (* action_algebra *)


subsection \<open>Equational Action Algebras\<close>

text \<open>The induction axioms of Kleene algebras are universal Horn
formulas. This is unavoidable, because due to a well known result of
Redko, there is no finite equational axiomatisation for the equational
theory of regular expressions.

Action algebras, in contrast, admit a finite equational
axiomatization, as Pratt has shown. We now formalise this
result. Consequently, the equational action algebra axioms, which
imply those based on Galois connections, which in turn imply those of
Kleene algebras, are complete with respect to the equational theory of
regular expressions. However, this completeness result does not
account for residuation.\<close>

class equational_action_algebra = residuated_sup_lgroupoid + dioid_one_zero + star_op +
  assumes star_ax: "1 + x\<^sup>\<star> \<cdot> x\<^sup>\<star> + x \<le> x\<^sup>\<star>"
  and star_subdist: "x\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
  and right_pure_induction: "(x \<rightarrow> x)\<^sup>\<star> \<le> x \<rightarrow> x"
begin

text \<open>We now show that the equational axioms of action algebra
satisfy those based on the Galois connections. Since we can use our
correspondence between the two variants of residuated semilattice, it
remains to derive the second reflexive transitive closure axiom for
the star, essentially copying Pratt's proof step by step. We then
prove a subclass statement.\<close>

lemma star_rtc_2: "1 + y \<cdot> y + x \<le> y \<Longrightarrow> x\<^sup>\<star> \<le> y"
proof -
  assume "1 + y \<cdot> y + x \<le> y"
  hence "1 \<le> y" and "x \<le> y" and "y \<cdot> y \<le> y"
    by auto
  hence "y \<le> y \<rightarrow> y" and "x \<le> y \<rightarrow> y"
    using local.order_trans by blast+
  hence "x\<^sup>\<star> \<le> (y \<rightarrow> y)\<^sup>\<star>"
    by (metis local.join.sup.absorb2 local.star_subdist)
  hence "x\<^sup>\<star> \<le> y \<rightarrow> y"
    by (metis order_trans right_pure_induction)
  hence "y \<cdot> x\<^sup>\<star> \<le> y"
    by (simp add: local.resr_galois)
  thus "x\<^sup>\<star> \<le> y"
    by (metis \<open>1 \<le> y\<close> local.dual_order.trans local.mult_onel local.resl_galois)
qed

subclass action_algebra
  by (unfold_locales, metis star_ax, metis star_rtc_2)

end (* equational_action_algebra *)

text \<open>
Conversely, every action algebra satisfies the equational axioms of
equational action algebras.

Because the subclass relation must be acyclic in Isabelle, we can only
establish this for the corresponding locales. Again this proof is
based on the residuated semilattice result.
\<close>

sublocale action_algebra \<subseteq> equational_action_algebra
  by (unfold_locales, metis star_rtc1, metis star_subdist, metis residual_r_pure_induction)

subsection \<open>Another Variant\<close>

text \<open>Finally we show that Pratt and Kozen's star axioms generate
precisely the same theory.\<close>

class action_algebra_var = residuated_sup_lgroupoid + dioid_one_zero + star_op +
  assumes star_unfold': "1 + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
  and star_inductl': "z + x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y"
  and star_inductr': "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x\<^sup>\<star>  \<le> y"
begin

subclass kleene_algebra
  by (unfold_locales, metis star_unfold', metis star_inductl', metis star_inductr')

subclass action_algebra
  by (unfold_locales, metis add.commute less_eq_def order_refl star_ext star_plus_one star_trans_eq, metis add.assoc add.commute star_rtc_least)

end

sublocale action_algebra \<subseteq> action_algebra_var
  by (unfold_locales, metis star_unfoldl, metis star_inductl, metis star_inductr)

end
