(* Title:      Relation Algebra
   Author:     Alasdair Armstrong, Simon Foster, Georg Struth, Tjark Weber
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

section \<open>(More) Boolean Algebra\<close>

theory More_Boolean_Algebra
  imports Main
begin

subsection \<open>Laws of Boolean Algebra\<close>

text \<open>The following laws of Boolean algebra support relational proofs. We
might add laws for the binary minus since that would make certain theorems look
more nicely. These are currently not so well supported.\<close>

context boolean_algebra
begin

no_notation
  times (infixl "\<cdot>" 70)
  and plus (infixl "+" 65)
  and Groups.zero_class.zero ("0")
  and Groups.one_class.one ("1")

notation
  inf (infixl "\<cdot>" 70)
  and sup (infixl "+" 65)
  and bot ("0")
  and top ("1")

lemma meet_assoc: "x \<cdot> (y \<cdot> z) = (x \<cdot> y) \<cdot> z"
by (metis inf_assoc)

lemma aux4 [simp]: "x \<cdot> y + x \<cdot> -y = x"
by (metis inf_sup_distrib1 inf_top_right sup_compl_top)

lemma aux4_comm [simp]: "x \<cdot> -y + x \<cdot> y = x"
by (metis aux4 sup.commute)

lemma aux6 [simp]: "(x + y) \<cdot> -x = y \<cdot> -x"
by (metis inf_compl_bot inf_sup_distrib2 sup_bot_left)

lemma aux6_var [simp]: "(-x + y) \<cdot> x = x \<cdot> y"
by (metis compl_inf_bot inf_commute inf_sup_distrib2 sup_bot_left)

lemma aux9 [simp]: "x + -x \<cdot> y = x + y"
by (metis aux4 aux6 inf.commute inf_sup_absorb)

lemma join_iso: "x \<le> y \<Longrightarrow> x + z \<le> y + z"
by (metis eq_refl sup_mono)

lemma join_isol: "x \<le> y \<Longrightarrow> z + x \<le> z + y"
by (metis join_iso sup.commute)

lemma join_double_iso: "x \<le> y \<Longrightarrow> w + x + z \<le> w + y + z"
by (metis le_iff_inf sup_inf_distrib1 sup_inf_distrib2)

lemma comp_anti: "x \<le> y \<longleftrightarrow> -y \<le> -x"
by (metis compl_le_swap2 double_compl)

lemma meet_iso: "x \<le> y \<Longrightarrow> x \<cdot> z \<le> y \<cdot> z"
by (metis eq_refl inf_mono)

lemma meet_isor: "x \<le> y \<Longrightarrow> z \<cdot> x \<le> z \<cdot> y"
by (metis inf.commute meet_iso)

lemma meet_double_iso: "x \<le> y \<Longrightarrow> w \<cdot> x \<cdot> z \<le> w \<cdot> y \<cdot> z"
by (metis meet_iso meet_isor)

lemma de_morgan_3 [simp]: "-(-x \<cdot> -y) = x + y"
by (metis compl_sup double_compl)

lemma subdist_2_var: "x + y \<cdot> z \<le> x + y"
by (metis eq_refl inf_le1 sup_mono)

lemma dist_alt: "\<lbrakk>x + z = y + z; x \<cdot> z = y \<cdot> z\<rbrakk> \<Longrightarrow> x = y"
by (metis aux4 aux6 sup.commute)

text \<open>Finally we prove the Galois connections for complementation.\<close>

lemma galois_aux: "x \<cdot> y = 0 \<longleftrightarrow> x \<le> -y"
by (metis aux6 compl_sup double_compl inf.commute le_iff_inf sup_bot_right sup_compl_top)

lemma galois_aux2: "x \<cdot> -y = 0 \<longleftrightarrow> x \<le> y"
by (metis double_compl galois_aux)

lemma galois_1: "x \<cdot> -y \<le> z \<longleftrightarrow> x \<le> y + z"
apply (rule iffI)
 apply (metis inf_le2 join_iso le_iff_sup le_supE join_isol aux4)
apply (metis meet_iso aux6 le_infE)
done

lemma galois_2: "x \<le> y + -z \<longleftrightarrow> x \<cdot> z \<le> y"
apply (rule iffI)
 apply (metis compl_sup double_compl galois_1 inf.commute)
apply (metis inf.commute order_trans subdist_2_var aux4 join_iso)
done

lemma galois_aux3: "x + y = 1 \<longleftrightarrow> -x \<le> y"
by (metis galois_1 inf_top_left top_unique)

lemma galois_aux4: "-x + y = 1 \<longleftrightarrow> x \<le> y"
by (metis double_compl galois_aux3)

subsection \<open>Boolean Algebras with Operators\<close>

text \<open>We follow J\'onsson and Tarski to define pairs of conjugate functions
on Boolean algebras. We also consider material from Maddux's article. This
gives rise to a Galois connection and the notion of Boolean algebras with
operators.

We do not explicitly define families of functions over Boolean algebras as a
type class.

This development should certainly be expanded do deal with complete Boolean
algebras one the one hand and other lattices on the other hand.

Boolean algebras with operators and their variants can be applied in various
ways. The prime example are relation algebras. The modular laws, for instance,
can be derived by instantiation. Other applications are antidomain semirings
where modal operators satisfy conjugations and Galois connections, and algebras
of predicate transformers.\<close>

text\<open>We define conjugation as a predicate which holds if a pair of functions
are conjugates.\<close>

definition is_conjugation :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "is_conjugation f g \<equiv> (\<forall>x y . f x \<cdot> y = 0 \<longleftrightarrow> x \<cdot> g y = 0)"

text \<open>We now prove the standard lemmas. First we show that conjugation is
symmetric and that conjugates are uniqely defined.\<close>

lemma is_conjugation_sym: "is_conjugation f g \<longleftrightarrow> is_conjugation g f"
by (metis inf.commute is_conjugation_def)

lemma is_conjugation_unique: "\<lbrakk>is_conjugation f g; is_conjugation f h\<rbrakk> \<Longrightarrow> g = h"
by (metis galois_aux inf.commute double_compl eq_iff ext is_conjugation_def)

text \<open>Next we show that conjugates give rise to adjoints in a Galois
connection.\<close>

lemma conj_galois_1:
  assumes "is_conjugation f g"
  shows "f x \<le> y \<longleftrightarrow> x \<le> -g (-y)"
by (metis assms is_conjugation_def double_compl galois_aux)

lemma conj_galois_2:
  assumes "is_conjugation f g"
  shows "g x \<le> y \<longleftrightarrow> x \<le> -f (-y)"
by (metis assms is_conjugation_sym conj_galois_1)

text \<open>Now we prove some of the standard properties of adjoints and
conjugates. In fact, conjugate functions even distribute over all existing
suprema. We display the next proof in detail because it is elegant.\<close>

lemma f_pre_additive:
  assumes "is_conjugation f g"
  shows "f (x + y) \<le> z \<longleftrightarrow> f x + f y \<le> z"
proof -
  have "f (x + y) \<le> z \<longleftrightarrow> x + y \<le> -g (-z)"
    by (metis assms conj_galois_1)
  also have "... \<longleftrightarrow> x \<le> -g (-z) \<and> y \<le> -g (-z)"
    by (metis le_sup_iff)
  also have "... \<longleftrightarrow> f x \<le> z \<and> f y \<le> z"
    by (metis assms conj_galois_1)
  thus ?thesis
    by (metis le_sup_iff calculation)
qed

lemma f_additive:
  assumes "is_conjugation f g"
  shows "f (sup x y) = sup (f x) (f y)"
by (metis assms eq_iff f_pre_additive)

lemma g_pre_additive:
  assumes "is_conjugation f g"
  shows "g (sup x y) \<le> z \<longleftrightarrow> sup (g x) (g y) \<le> z"
by (metis assms is_conjugation_sym f_pre_additive)

lemma g_additive:
  assumes "is_conjugation f g"
  shows "g (sup x y) = sup (g x) (g y)"
by (metis assms is_conjugation_sym f_additive)

text \<open>Additivity of adjoints obviously implies their isotonicity.\<close>

lemma f_iso:
  assumes "is_conjugation f g"
  shows "x \<le> y \<longrightarrow> f x \<le> f y"
by (metis assms f_additive le_iff_sup)

lemma g_iso:
  assumes "is_conjugation f g"
  shows "x \<le> y \<longrightarrow> g x \<le> g y"
by (metis assms is_conjugation_sym f_iso)

lemma f_subdist:
  assumes "is_conjugation f g"
  shows "f (x \<cdot> y) \<le> f x"
by (metis assms f_iso inf_le1)

lemma g_subdist:
  assumes "is_conjugation f g"
  shows "g (x \<cdot> y) \<le> g x"
by (metis assms g_iso inf_le1)

text \<open>Next we prove cancellation and strictness laws.\<close>

lemma cancellation_1:
  assumes "is_conjugation f g"
  shows "f (-g x) \<le> -x"
by (metis assms conj_galois_1 double_compl eq_refl)

lemma cancellation_2:
  assumes "is_conjugation f g"
  shows "g (-f x) \<le> -x"
by (metis assms is_conjugation_sym cancellation_1)

lemma f_strict:
  assumes "is_conjugation f g"
  shows "f 0 = 0"
by (metis assms inf.idem inf_bot_left is_conjugation_def)

lemma g_strict:
  assumes "is_conjugation f g"
  shows "g 0 = 0"
by (metis assms is_conjugation_sym f_strict)

text \<open>The following variants of modular laws have more concrete counterparts
in relation algebra.\<close>

lemma modular_1_aux:
  assumes "is_conjugation f g"
  shows "f (x \<cdot> -g y) \<cdot> y = 0"
by (metis assms galois_aux inf_le2 is_conjugation_def)

lemma modular_2_aux:
  assumes "is_conjugation f g"
  shows "g (x \<cdot> -f y) \<cdot> y = 0"
by (metis assms is_conjugation_sym modular_1_aux)

lemma modular_1:
  assumes "is_conjugation f g"
  shows "f x \<cdot> y = f (x \<cdot> g y) \<cdot> y"
proof -
  have "f x \<cdot> y = f (x \<cdot> g y + x \<cdot> -g y) \<cdot> y"
    by (metis aux4)
  hence "f x \<cdot> y = (f (x \<cdot> g y) + f (x \<cdot> -g y)) \<cdot> y"
    by (metis assms f_additive)
  hence "f x \<cdot> y = f (x \<cdot> g y) \<cdot> y + f (x \<cdot> -g y) \<cdot> y"
    by (metis inf.commute inf_sup_distrib1)
  thus ?thesis
    by (metis assms modular_1_aux sup_bot_right)
qed

lemma modular_2:
  assumes "is_conjugation f g"
  shows "g x \<cdot> y = g (x \<cdot> f y) \<cdot> y"
by (metis assms is_conjugation_sym modular_1)

lemma conjugate_eq_aux:
  "is_conjugation f g \<Longrightarrow> f (x \<cdot> -g y) \<le> f x \<cdot> -y"
  by (metis f_subdist galois_aux le_inf_iff modular_1_aux)

lemma conjugate_eq:
  "is_conjugation f g \<longleftrightarrow> (\<forall>x y. f (x \<cdot> -g y) \<le> f x \<cdot> -y \<and> g (y \<cdot> -f x) \<le> g y \<cdot> -x)"
    (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l thus ?r
    by (metis is_conjugation_sym conjugate_eq_aux)
next
  assume r: ?r
  have "\<forall>x y. f x \<cdot> y = 0 \<longrightarrow> x \<cdot> g y = 0"
    by (metis aux4 inf.left_commute inf_absorb1 inf_compl_bot inf_left_idem sup_bot_left r)
  hence "\<forall>x y. x \<cdot> g y = 0 \<longleftrightarrow> f x \<cdot> y = 0"
    by (metis aux4 inf.commute inf.left_commute inf_absorb1 inf_compl_bot sup_commute sup_inf_absorb r)
  thus "is_conjugation f g"
    by (metis is_conjugation_def)
qed

lemma conjugation_prop1: "is_conjugation f g \<Longrightarrow> f y \<cdot> z \<le> f (y \<cdot> g z)"
by (metis le_infE modular_1 order_refl)

lemma conjugation_prop2: "is_conjugation f g \<Longrightarrow> g z \<cdot> y \<le> g (z \<cdot> f y)"
by (metis is_conjugation_sym conjugation_prop1)

end (* boolean_algebra *)

end

