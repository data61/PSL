(* Title:      Relation Algebra
   Author:     Alasdair Armstrong, Simon Foster, Georg Struth, Tjark Weber
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

section \<open>Relation Algebra\<close>

theory Relation_Algebra
  imports More_Boolean_Algebra Kleene_Algebra.Kleene_Algebra
begin

text \<open>We follow Tarski's original article and Maddux's book, in particular we
use their notation. In contrast to Schmidt and Str\"ohlein we do not assume
that the Boolean algebra is complete and we do not consider the Tarski rule in
this development.

A main reason for using complete Boolean algebras seems to be that the
Knaster-Tarski fixpoint theorem becomes available for defining notions of
iteration. In fact, several chapters of Schmidt and Str\"ohlein's book deal
with iteration.

We capture iteration in an alternative way by linking relation algebras with
Kleene algebras (cf.~\emph{relation-algebra-rtc}).\<close>

class relation_algebra = boolean_algebra +
  fixes composition :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl ";" 75)
    and converse :: "'a \<Rightarrow> 'a" ("(_\<^sup>\<smile>)" [1000] 999)
    and unit :: "'a" ("1'")
  assumes comp_assoc: "(x ; y) ; z = x ; (y ; z)"
    and comp_unitr [simp]: "x ; 1' = x"
    and comp_distr: "(x + y) ; z = x ; z + y ; z"
    and conv_invol [simp]: "(x\<^sup>\<smile>)\<^sup>\<smile> = x"
    and conv_add [simp]: "(x + y)\<^sup>\<smile> = x\<^sup>\<smile> + y\<^sup>\<smile>"
    and conv_contrav [simp]: "(x ; y)\<^sup>\<smile> = y\<^sup>\<smile> ; x\<^sup>\<smile>"
    and comp_res: "x\<^sup>\<smile> ; -(x ; y) \<le> -y"

text \<open>We first show that every relation algebra is a dioid. We do not yet
treat the zero (the minimal element of the boolean reduct) since the proof of
the annihilation laws is rather tricky to automate. Following Maddux we derive
them from properties of Boolean algebras with operators.\<close>

sublocale relation_algebra \<subseteq> dioid_one "(+)" "(;)" "(\<le>) " "(<)" "1'"
proof
  fix x y z :: 'a
  show "x ; y ; z = x ; (y ; z)"
    by (fact comp_assoc)
  show "x + y + z = x + (y + z)"
    by (metis sup.commute sup.left_commute)
  show "x + y = y + x"
    by (fact sup.commute)
  show "(x + y) ; z = x ; z + y ; z"
    by (fact comp_distr)
  show "x + x = x"
    by (fact sup.idem)
  show "x ; (y + z) = x ; y + x ; z"
    by (metis conv_invol conv_add conv_contrav comp_distr)
  show "x ; 1' = x"
    by (fact comp_unitr)
  show "1' ; x = x"
    by (metis comp_unitr conv_contrav conv_invol)
  show "x \<le> y \<longleftrightarrow> x + y = y"
    by (metis sup.commute sup_absorb1 sup_ge1)
  show "x < y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y"
    by (fact less_le)
qed

context relation_algebra
begin

text \<open>First we prove some basic facts about joins and meets.\<close>

lemma meet_interchange: "(w \<cdot> x) ; (y \<cdot> z) \<le> w ; y \<cdot> x ; z"
by (metis inf_le1 inf_le2 le_infI mult_isol_var)

lemma join_interchange: "w ; x + y ; z \<le> (w + y) ; (x + z)"
using local.mult_isol_var local.sup.bounded_iff local.sup.cobounded2 local.sup_ge1 by presburger

text \<open>We now prove some simple facts about conversion.\<close>

lemma conv_iso: "x \<le> y \<longleftrightarrow> x\<^sup>\<smile> \<le> y\<^sup>\<smile>"
by (metis conv_add conv_invol le_iff_sup)

lemma conv_zero [simp]: "0\<^sup>\<smile> = 0"
by (metis conv_add conv_invol sup_bot_right sup_eq_bot_iff)

lemma conv_one [simp]: "1\<^sup>\<smile> = 1"
by (metis conv_add conv_invol sup_top_left sup_top_right)

lemma conv_compl_aux: "(-x)\<^sup>\<smile> = (-x)\<^sup>\<smile> + (-x\<^sup>\<smile>)"
by (metis aux9 conv_add conv_one double_compl galois_aux4 inf.commute less_eq_def sup.commute sup_top_left)

lemma conv_compl: "(-x)\<^sup>\<smile> = -(x\<^sup>\<smile>)"
by (metis add_commute conv_add conv_compl_aux conv_invol)

lemma comp_res_aux [simp]: "x\<^sup>\<smile> ; -(x ; y) \<cdot> y = 0"
by (metis comp_res galois_aux)

lemma conv_e [simp]: "1'\<^sup>\<smile> = 1'"
by (metis comp_unitr conv_contrav conv_invol)

lemma conv_times [simp]: "(x \<cdot> y)\<^sup>\<smile> = x\<^sup>\<smile> \<cdot> y\<^sup>\<smile>"
by (metis compl_inf double_compl conv_add conv_compl)

text \<open>The next lemmas show that conversion is self-conjugate in the sense of
Boolean algebra with operators.\<close>

lemma conv_self_conjugate: "x\<^sup>\<smile> \<cdot> y = 0 \<longleftrightarrow> x \<cdot> y\<^sup>\<smile> = 0"
by (metis conv_invol conv_times conv_zero)

lemma conv_self_conjugate_var: "is_conjugation converse converse"
by (metis conv_self_conjugate is_conjugation_def)

text \<open>The following lemmas link the relative product and meet.\<close>

lemma one_idem_mult [simp]: "1 ; 1 = 1"
by (metis compl_eq_compl_iff galois_aux2 inf.commute inf_top_right mult_1_left mult_isor top_greatest)

lemma mult_subdistl: "x ; (y \<cdot> z) \<le> x ; y"
by (metis inf_le1 mult_isol)

lemma mult_subdistr: "(x \<cdot> y) ; z \<le> x ; z"
by (metis inf_le1 mult_isor)

lemma mult_subdistr_var: "(x \<cdot> y) ; z \<le> x ; z \<cdot> y ; z"
by (metis inf.commute le_inf_iff mult_subdistr)

text \<open>The following lemmas deal with variants of the Peirce law, the
Schr\"oder laws and the Dedekind law. Some of them are obtained from Boolean
algebras with operators by instantiation, using conjugation properties.
However, Isabelle does not always pick up this relationship.\<close>

lemma peirce_1: "x ; y \<cdot> z\<^sup>\<smile> = 0 \<Longrightarrow> y ; z \<cdot> x\<^sup>\<smile> = 0"
by (metis compl_le_swap1 conv_contrav conv_self_conjugate galois_aux comp_res conv_invol galois_aux mult_isol order_trans)

lemma peirce: "x ; y \<cdot> z\<^sup>\<smile> = 0 \<longleftrightarrow> y ; z \<cdot> x\<^sup>\<smile> = 0"
by (metis peirce_1)

lemma schroeder_1: "x ; y \<cdot> z = 0 \<longleftrightarrow> y \<cdot> x\<^sup>\<smile> ; z = 0"
by (metis conv_invol peirce conv_contrav conv_invol conv_self_conjugate inf.commute)

lemma schroeder_2: "y ; x \<cdot> z = 0 \<longleftrightarrow> y \<cdot> z ; x\<^sup>\<smile> = 0"
by (metis conv_invol peirce schroeder_1)

text \<open>The following two conjugation properties between multiplication with
elements and their converses are used for deriving modular laws of relation
algebra from those of Boolean algebras with operators.\<close>

lemma schroeder_1_var: "is_conjugation (composition x) (composition (x\<^sup>\<smile>))"
by (metis schroeder_1 is_conjugation_def)

lemma schroeder_2_var: "is_conjugation (\<lambda>x. x ; y) (\<lambda>x. x ; y\<^sup>\<smile>)"
by (unfold is_conjugation_def, metis schroeder_2)

text \<open>The following Galois connections define residuals. They link relation
algebras with action algebras. This could be further explored and formalised.
\<close>

lemma conv_galois_1: "x ; y \<le> z \<longleftrightarrow> y \<le> -(x\<^sup>\<smile> ; -z)"
by (metis galois_aux galois_aux2 schroeder_1)

lemma conv_galois_2: "y ; x \<le> z \<longleftrightarrow> y \<le> -(-z ; x\<^sup>\<smile>)"
by (metis galois_aux galois_aux2 schroeder_2)

text \<open>Variants of the modular law for relation algebras can now be
instantiated from Boolean algebras with operators.\<close>

lemma modular_1_aux': "x ; (y \<cdot> -(x\<^sup>\<smile> ; z)) \<cdot> z = 0"
by (metis schroeder_1_var modular_1_aux)

lemma modular_2_aux': "(y \<cdot> -(z ; x\<^sup>\<smile>)) ; x \<cdot> z = 0"
by (metis modular_1_aux schroeder_2_var)

lemma modular_1': "x ; y \<cdot> z = x ; (y \<cdot> x\<^sup>\<smile> ; z) \<cdot> z"
by (metis schroeder_1_var modular_1)

lemma modular_2': "y ; x \<cdot> z = (y \<cdot> z ; x\<^sup>\<smile>) ; x \<cdot> z"
proof -
  have "y ; x \<cdot> z = (y \<cdot> z ; x\<^sup>\<smile>) ; x \<cdot> z + (y \<cdot> -(z ; x\<^sup>\<smile>)) ; x \<cdot> z"
    by (metis aux4 distrib_right inf.commute inf_sup_distrib1)
  thus ?thesis
    by (metis sup_bot_right modular_2_aux')
qed

lemma modular_1_var: "x ; y \<cdot> z \<le> x ; (y \<cdot> x\<^sup>\<smile> ; z)"
by (metis inf.commute inf_le2 modular_1')

lemma modular_2_var: "x ; y \<cdot> z \<le> (x \<cdot> z ; y\<^sup>\<smile>) ; y"
by (metis inf.commute inf_le2 modular_2')

lemma modular_var_2: "x ; y \<le> x ; (y \<cdot> x\<^sup>\<smile> ; 1)"
by (metis inf_top_right modular_1_var)

lemma modular_var_3: "x ; y \<le> (x \<cdot> 1 ; y\<^sup>\<smile>) ; y"
by (metis inf_top_right modular_2_var)

text \<open>The modular laws are used to prove the Dedekind rule.\<close>

lemma dedekind: "x ; y \<cdot> z \<le> (x \<cdot> z ; y\<^sup>\<smile>) ; (y \<cdot> x\<^sup>\<smile> ; z)"
proof -
  have "x ; y \<cdot> z \<le> (x \<cdot> z ; y\<^sup>\<smile>) ; (y \<cdot> ((x \<cdot> z ; y\<^sup>\<smile>)\<^sup>\<smile> ; z))"
    by (metis modular_2' modular_1_var)
  also have "\<dots> \<le> (x \<cdot> z ; y\<^sup>\<smile>) ; (y \<cdot> x\<^sup>\<smile> ; z)"
    by (metis conv_iso inf_le1 inf_mono mult_isol mult_isor order_refl)
  thus ?thesis
    by (metis calculation order_trans)
qed

lemma dedekind_var_1: "x ; y \<le> (x \<cdot> 1 ; y\<^sup>\<smile>) ; (y \<cdot> x\<^sup>\<smile> ; 1)"
by (metis dedekind inf.commute inf_top_left)

end (* relation_algebra *)

text \<open>The Schr\"oder laws allow us, finally, to prove the annihilation laws
for zero. We formalise this by proving that relation algebras form dioids with
zero.\<close>

sublocale relation_algebra < dioid_one_zero "(+)" "(;)" "1'" 0 "(\<le>)" "(<)"
proof
  fix x :: 'a
  show "0 + x = x"
    by (fact sup_bot_left)
  show "0 ; x = 0"
    by (metis f_strict schroeder_2_var)
  show "x ; 0 = 0"
    by (metis f_strict schroeder_1_var)
qed

context relation_algebra
begin

text \<open>Next we prove miscellaneous properties which we found in the books of
Maddux and Schmidt and Str\"ohlein. Most of them do not carry any meaningful
names.\<close>

lemma ra_1: "(x \<cdot> y ; 1) ; z = x ; z \<cdot> y ; 1"
proof (rule antisym)
  show "x ; z \<cdot> y ; 1 \<le> (x \<cdot> y ; 1) ; z"
    by (metis modular_2_var comp_assoc order_trans eq_refl inf_mono inf_top_left mult_isor mult_subdistl)
  show "(x \<cdot> y ; 1) ; z \<le> x ; z \<cdot> y ; 1"
    by (metis inf.commute inf_greatest inf_top_left mult.assoc mult_subdistl mult_subdistr order_trans)
qed

lemma ra_2: "x ; (z \<cdot> y ; 1) = (x \<cdot> (y ; 1)\<^sup>\<smile>) ; z"
proof (rule antisym)
  have "(x \<cdot> 1 ; (z \<cdot> y ; 1)\<^sup>\<smile>) ; z \<le> (x \<cdot> (y ; 1)\<^sup>\<smile>) ; z"
    by (metis conv_contrav conv_invol conv_one conv_times inf.idem inf.left_commute le_iff_inf meet_assoc mult_isor ra_1)
  thus "x ; (z \<cdot> y ; 1) \<le> (x \<cdot> (y ; 1)\<^sup>\<smile>) ; z"
    by (metis modular_var_3 mult_subdistl order_trans)
next
  have "x ; (z \<cdot> ((x \<cdot> (y ; 1)\<^sup>\<smile>)\<^sup>\<smile> ; 1)) \<le> x ; (z \<cdot> y ; 1)"
    by (metis conv_invol conv_times eq_refl inf_le2 inf_mono mult.assoc mult_isol mult_isor one_idem_mult)
  thus "x ; (z \<cdot> y ; 1) \<ge> (x \<cdot> (y ; 1)\<^sup>\<smile>) ; z"
    by (metis modular_var_2 mult_subdistr order_trans)
qed

lemma one_conv: "1' \<cdot> x ; 1 = 1' \<cdot> x ; x\<^sup>\<smile>"
by (metis inf.commute inf_top_left modular_1' mult.right_neutral)

lemma maddux_12: "-(y ; x) ; x\<^sup>\<smile> \<le> -y"
by (metis galois_aux inf.commute inf_compl_bot schroeder_2)

lemma maddux_141: "x ; y \<cdot> z = 0 \<longleftrightarrow> x\<^sup>\<smile> ; z \<cdot> y = 0"
by (metis inf.commute schroeder_1)

lemma maddux_142: "x\<^sup>\<smile> ; z \<cdot> y = 0 \<longleftrightarrow> z ; y\<^sup>\<smile> \<cdot> x = 0"
by (metis inf.commute schroeder_1 schroeder_2)

lemmas maddux_16 = modular_1_var

lemmas maddux_17 = modular_2_var

lemma maddux_20: "x \<le> x ; 1"
by (metis inf_top_left mult.right_neutral mult_subdistl)

lemma maddux_21: "x \<le> 1 ; x"
by (metis mult_isor mult_onel top_greatest)

lemma maddux_23: "x ; y \<cdot> -(x ; z) = x ; (y \<cdot> -z) \<cdot> -(x ; z)"
apply (rule antisym)
apply (metis local.aux6 local.aux6_var local.aux9 local.compl_inf_bot local.compl_sup_top local.compl_unique local.distrib_left local.galois_2 local.sup_ge2)
using local.meet_iso local.mult_subdistl by blast

lemma maddux_24: "-(x ; y) + x ; z = -(x ; (y \<cdot> -z)) + x ; z"
by (metis de_morgan_3 double_compl maddux_23)

lemma one_compl: "-(x ; 1) ; 1 = -(x ; 1)"
by (metis antisym conv_one maddux_12 mult.assoc one_idem_mult maddux_20)

lemma ss_p18: "x ; 1 = 0 \<longleftrightarrow> x = 0"
by (metis annil le_bot maddux_20)

end (* relation_algebra *)

text \<open>This finishes our development of the basic laws of relation algebras.
The next sections are devoted to special elements such as vectors, test or
subidentities, and, in particular, functions.\<close>

end

