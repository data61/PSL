(* Title:      Kleene Algebra
   Author:     Alasdair Armstrong, Georg Struth, Tjark Weber
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

section \<open>Kleene Algebras\<close>

theory Kleene_Algebra
imports Conway
begin

subsection \<open>Left Near Kleene Algebras\<close>

text \<open>Extending the hierarchy developed in @{theory Kleene_Algebra.Dioid} we now
add an operation of Kleene star, finite iteration, or reflexive
transitive closure to variants of Dioids. Since a multiplicative unit
is needed for defining the star we only consider variants with~$1$;
$0$ can be added separately. We consider the left star induction axiom
and the right star induction axiom independently since in some
applications, e.g., Salomaa's axioms, probabilistic Kleene algebras,
or completeness proofs with respect to the equational theoy of regular
expressions and regular languages, the right star induction axiom is
not needed or not valid.

We start with near dioids, then consider pre-dioids and finally
dioids. It turns out that many of the known laws of Kleene algebras
hold already in these more general settings. In fact, all our
equational theorems have been proved within left Kleene algebras, as
expected.

Although most of the proofs in this file could be fully automated by
Sledgehammer and Metis, we display step-wise proofs as they would
appear in a text book. First, this file may then be useful as a
reference manual on Kleene algebra. Second, it is better protected
against changes in the underlying theories and supports easy
translation of proofs into other settings.\<close>

class left_near_kleene_algebra = near_dioid_one + star_op +
  assumes star_unfoldl: "1 + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
  and star_inductl: "z + x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y"

begin

text \<open>First we prove two immediate consequences of the unfold
axiom. The first one states that starred elements are reflexive.\<close>

lemma star_ref [simp]: "1 \<le> x\<^sup>\<star>"
  using star_unfoldl by auto
 
text \<open>Reflexivity of starred elements implies, by definition of the
order, that~$1$ is an additive unit for starred elements.\<close>

lemma star_plus_one [simp]: "1 + x\<^sup>\<star> = x\<^sup>\<star>"
  using less_eq_def star_ref by blast

lemma star_1l [simp]: "x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
  using star_unfoldl by auto

lemma "x\<^sup>\<star> \<cdot> x \<le> x\<^sup>\<star>"
(*nitpick [expect=genuine]*)
  oops

lemma "x \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
(*nitpick [expect=genuine]*)
  oops

text \<open>Next we show that starred elements are transitive.\<close>

lemma star_trans_eq [simp]: "x\<^sup>\<star> \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
proof (rule antisym) \<comment> \<open>this splits an equation into two inequalities\<close>
  have "x\<^sup>\<star> + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by auto
  thus "x\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (simp add: star_inductl)
  next show "x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> x\<^sup>\<star>"
    using mult_isor star_ref by fastforce
qed

lemma star_trans: "x\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
  by simp
  
text \<open>We now derive variants of the star induction axiom.\<close>

lemma star_inductl_var: "x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> y \<le> y"
proof -
  assume "x \<cdot> y \<le> y"
  hence "y + x \<cdot> y \<le> y"
    by simp
  thus "x\<^sup>\<star> \<cdot> y \<le> y"
    by (simp add: star_inductl)
qed

lemma star_inductl_var_equiv [simp]: "x\<^sup>\<star> \<cdot> y \<le> y \<longleftrightarrow> x \<cdot> y \<le> y"
proof
  assume "x \<cdot> y \<le> y"
  thus "x\<^sup>\<star> \<cdot> y \<le> y"
    by (simp add: star_inductl_var)
next
  assume "x\<^sup>\<star> \<cdot> y \<le> y"
  hence  "x\<^sup>\<star> \<cdot> y = y"
    by (metis eq_iff mult_1_left mult_isor star_ref)
  moreover hence "x \<cdot> y = x \<cdot> x\<^sup>\<star> \<cdot> y"
    by (simp add: mult.assoc)
  moreover have "... \<le> x\<^sup>\<star> \<cdot> y"
    by (metis mult_isor star_1l)
  ultimately show "x \<cdot> y \<le> y" 
    by auto
qed

lemma star_inductl_var_eq:  "x \<cdot> y = y \<Longrightarrow> x\<^sup>\<star> \<cdot> y \<le> y"
  by (metis eq_iff star_inductl_var)

lemma star_inductl_var_eq2: "y = x \<cdot> y \<Longrightarrow> y = x\<^sup>\<star> \<cdot> y"
proof -
  assume hyp: "y = x \<cdot> y"
  hence "y \<le> x\<^sup>\<star> \<cdot> y"
    using mult_isor star_ref by fastforce
  thus "y = x\<^sup>\<star> \<cdot> y"
    using hyp eq_iff by auto
qed

lemma "y = x \<cdot> y \<longleftrightarrow> y = x\<^sup>\<star> \<cdot> y"
(*nitpick [expect=genuine]*)
  oops

lemma "x\<^sup>\<star> \<cdot> z \<le> y \<Longrightarrow> z + x \<cdot> y \<le> y"
(*nitpick [expect=genuine]*)
  oops

lemma star_inductl_one: "1 + x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<le> y"
  using star_inductl by force

lemma star_inductl_star: "x \<cdot> y\<^sup>\<star> \<le> y\<^sup>\<star> \<Longrightarrow> x\<^sup>\<star> \<le> y\<^sup>\<star>"
  by (simp add: star_inductl_one)

lemma star_inductl_eq:  "z + x \<cdot> y = y \<Longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y"
  by (simp add: star_inductl)

text \<open>We now prove two facts related to~$1$.\<close>

lemma star_subid: "x \<le> 1 \<Longrightarrow> x\<^sup>\<star> = 1"
proof -
  assume "x \<le> 1"
  hence "1 + x \<cdot> 1 \<le> 1"
    by simp
  hence "x\<^sup>\<star> \<le> 1"
    by (metis mult_oner star_inductl)
  thus "x\<^sup>\<star> = 1"
    by (simp add: order.antisym)
qed

lemma star_one [simp]: "1\<^sup>\<star> = 1"
  by (simp add: star_subid)

text \<open>We now prove a subdistributivity property for the star (which
is equivalent to isotonicity of star).\<close>

lemma star_subdist:  "x\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
proof -
  have "x \<cdot> (x + y)\<^sup>\<star> \<le> (x + y) \<cdot> (x + y)\<^sup>\<star>"
    by simp
  also have "...  \<le> (x + y)\<^sup>\<star>"
    by (metis star_1l)
  thus ?thesis
    using calculation order_trans star_inductl_star by blast
qed

lemma star_subdist_var:  "x\<^sup>\<star> + y\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
  using join.sup_commute star_subdist by force

lemma star_iso [intro]: "x \<le> y \<Longrightarrow> x\<^sup>\<star> \<le> y\<^sup>\<star>"
  by (metis less_eq_def star_subdist)

text \<open>We now prove some more simple properties.\<close>

lemma star_invol [simp]: "(x\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star>"
proof (rule antisym)
  have "x\<^sup>\<star> \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
    by (fact star_trans_eq)
  thus "(x\<^sup>\<star>)\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (simp add: star_inductl_star)
  have"(x\<^sup>\<star>)\<^sup>\<star> \<cdot> (x\<^sup>\<star>)\<^sup>\<star> \<le> (x\<^sup>\<star>)\<^sup>\<star>"
    by (fact star_trans)
  hence "x \<cdot> (x\<^sup>\<star>)\<^sup>\<star> \<le> (x\<^sup>\<star>)\<^sup>\<star>"
    by (meson star_inductl_var_equiv)
  thus "x\<^sup>\<star> \<le> (x\<^sup>\<star>)\<^sup>\<star>"
    by (simp add: star_inductl_star)
qed

lemma star2 [simp]: "(1 + x)\<^sup>\<star> = x\<^sup>\<star>"
proof (rule antisym)
  show "x\<^sup>\<star> \<le> (1 + x)\<^sup>\<star>"
    by auto
  have "x\<^sup>\<star> + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by simp
  thus "(1 + x)\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (simp add: star_inductl_star)
qed

lemma "1 + x\<^sup>\<star> \<cdot> x \<le> x\<^sup>\<star>"
(*nitpick [expect=genuine]*)
  oops

lemma "x \<le> x\<^sup>\<star>"
(*nitpick [expect=genuine]*)
  oops

lemma "x\<^sup>\<star> \<cdot> x \<le> x\<^sup>\<star>"
(*nitpick [expect=genuine]*)
  oops

lemma "1 + x \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
(*nitpick [expect=genuine]*)
  oops

lemma "x \<cdot> z \<le> z \<cdot> y \<Longrightarrow> x\<^sup>\<star> \<cdot> z \<le> z \<cdot> y\<^sup>\<star>"
(*nitpick [expect=genuine]*)
  oops

text \<open>The following facts express inductive conditions that are used
to show that @{term "(x + y)\<^sup>\<star>"} is the greatest term that can be built
from~@{term x} and~@{term y}.\<close>

lemma prod_star_closure: "x \<le> z\<^sup>\<star> \<Longrightarrow> y \<le> z\<^sup>\<star> \<Longrightarrow> x \<cdot> y \<le> z\<^sup>\<star>"
proof -
  assume assm: "x \<le> z\<^sup>\<star>" "y \<le> z\<^sup>\<star>"
  hence "y + z\<^sup>\<star> \<cdot> z\<^sup>\<star> \<le> z\<^sup>\<star>"
    by simp
  hence "z\<^sup>\<star> \<cdot> y \<le> z\<^sup>\<star>"
    by (simp add: star_inductl)
  also have "x \<cdot> y \<le> z\<^sup>\<star> \<cdot> y"
    by (simp add: assm mult_isor)
  thus "x \<cdot> y \<le> z\<^sup>\<star>"
    using calculation order.trans by blast
qed

lemma star_star_closure: "x\<^sup>\<star> \<le> z\<^sup>\<star> \<Longrightarrow> (x\<^sup>\<star>)\<^sup>\<star> \<le> z\<^sup>\<star>"
  by (metis star_invol)

lemma star_closed_unfold: "x\<^sup>\<star> = x \<Longrightarrow> x = 1 + x \<cdot> x"
  by (metis star_plus_one star_trans_eq)

lemma "x\<^sup>\<star> = x \<longleftrightarrow> x = 1 + x \<cdot> x"
(*nitpick [expect=genuine]*)
  oops

end (* left_near_kleene_algebra *)


subsection \<open>Left Pre-Kleene Algebras\<close>

class left_pre_kleene_algebra = left_near_kleene_algebra + pre_dioid_one

begin

text \<open>We first prove that the star operation is extensive.\<close>

lemma star_ext [simp]: "x \<le> x\<^sup>\<star>"
proof -
  have "x \<le> x \<cdot> x\<^sup>\<star>"
    by (metis mult_oner mult_isol star_ref)
  thus ?thesis
    by (metis order_trans star_1l)
qed

text \<open>We now prove a right star unfold law.\<close>

lemma star_1r [simp]: "x\<^sup>\<star> \<cdot> x \<le> x\<^sup>\<star>"
proof -
  have "x + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by simp
  thus ?thesis
    by (fact star_inductl)
qed

lemma star_unfoldr: "1 + x\<^sup>\<star> \<cdot> x \<le> x\<^sup>\<star>"
  by simp

lemma "1 + x\<^sup>\<star> \<cdot> x = x\<^sup>\<star>"
(*nitpick [expect=genuine]*)
  oops

text \<open>Next we prove a simulation law for the star.  It is
instrumental in proving further properties.\<close>

lemma star_sim1: "x \<cdot> z \<le> z \<cdot> y \<Longrightarrow> x\<^sup>\<star> \<cdot> z \<le> z \<cdot> y\<^sup>\<star>"
proof -
  assume "x \<cdot> z \<le> z \<cdot> y"
  hence "x \<cdot> z \<cdot> y\<^sup>\<star> \<le> z \<cdot> y \<cdot> y\<^sup>\<star>"
    by (simp add: mult_isor)
  also have "...  \<le> z \<cdot> y\<^sup>\<star>"
    by (simp add: mult_isol mult_assoc)
  finally have "x \<cdot> z \<cdot> y\<^sup>\<star> \<le> z \<cdot> y\<^sup>\<star>"
    by simp
  hence "z + x \<cdot> z \<cdot> y\<^sup>\<star> \<le> z \<cdot> y\<^sup>\<star>"
    by (metis join.sup_least mult_isol mult_oner star_ref)
  thus "x\<^sup>\<star> \<cdot> z \<le> z \<cdot> y\<^sup>\<star>"
    by (simp add: star_inductl mult_assoc)
qed

text \<open>The next lemma is used in omega algebras to prove, for
instance, Bachmair and Dershowitz's separation of termination
theorem~\cite{bachmair86commutation}. The property at the left-hand
side of the equivalence is known as \emph{quasicommutation}.\<close>

lemma quasicomm_var: "y \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star> \<longleftrightarrow> y\<^sup>\<star> \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star>"
proof
  assume "y \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star>"
  thus "y\<^sup>\<star> \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star>"
    using star_sim1 by force
next
  assume "y\<^sup>\<star> \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star>"
  thus "y \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star>"
    by (meson mult_isor order_trans star_ext)
qed

lemma star_slide1: "(x \<cdot> y)\<^sup>\<star> \<cdot> x \<le> x \<cdot> (y \<cdot> x)\<^sup>\<star>"
  by (simp add: mult_assoc star_sim1)

lemma "(x \<cdot> y)\<^sup>\<star> \<cdot> x = x \<cdot> (y \<cdot> x)\<^sup>\<star>"
(*nitpick [expect=genuine]*)
  oops

lemma star_slide_var1: "x\<^sup>\<star> \<cdot> x \<le> x \<cdot> x\<^sup>\<star>" 
  by (simp add: star_sim1)

text \<open>We now show that the (left) star unfold axiom can be strengthened to an equality.\<close>

lemma star_unfoldl_eq [simp]: "1 + x \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
proof (rule antisym)
  show "1 + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (fact star_unfoldl)
  have "1 + x \<cdot> (1 + x \<cdot> x\<^sup>\<star>) \<le> 1 + x \<cdot> x\<^sup>\<star>"
    by (meson join.sup_mono eq_refl mult_isol star_unfoldl)
  thus "x\<^sup>\<star> \<le> 1 + x \<cdot> x\<^sup>\<star>"
    by (simp add: star_inductl_one)
qed

lemma "1 + x\<^sup>\<star> \<cdot> x = x\<^sup>\<star>"
(*nitpick [expect=genuine]*)
  oops

text \<open>Next we relate the star and the reflexive transitive closure
operation.\<close>

lemma star_rtc1_eq [simp]: "1 + x + x\<^sup>\<star> \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
  by (simp add: join.sup.absorb2)

lemma star_rtc1: "1 + x + x\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
  by simp

lemma star_rtc2: "1 + x \<cdot> x \<le> x \<longleftrightarrow> x = x\<^sup>\<star>"
proof
  assume "1 + x \<cdot> x \<le> x"
  thus "x = x\<^sup>\<star>"
    by (simp add: local.eq_iff local.star_inductl_one)
next
  assume "x = x\<^sup>\<star>"
  thus "1 + x \<cdot> x \<le> x"
    using local.star_closed_unfold by auto
qed

lemma star_rtc3: "1 + x \<cdot> x = x \<longleftrightarrow> x = x\<^sup>\<star>"
  by (metis order_refl star_plus_one star_rtc2 star_trans_eq)

lemma star_rtc_least: "1 + x + y \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<le> y"
proof -
  assume "1 + x + y \<cdot> y \<le> y"
  hence "1 + x \<cdot> y \<le> y"
    by (metis join.le_sup_iff mult_isol_var star_trans_eq star_rtc2)
  thus "x\<^sup>\<star> \<le> y"
    by (simp add: star_inductl_one)
qed

lemma star_rtc_least_eq: "1 + x + y \<cdot> y = y \<Longrightarrow> x\<^sup>\<star> \<le> y"
  by (simp add: star_rtc_least)

lemma "1 + x + y \<cdot> y \<le> y \<longleftrightarrow> x\<^sup>\<star> \<le> y"
(*nitpick [expect=genuine]*)
  oops

text \<open>The next lemmas are again related to closure conditions\<close>

lemma star_subdist_var_1: "x \<le> (x + y)\<^sup>\<star>"
  by (meson join.sup.boundedE star_ext)

lemma star_subdist_var_2: "x \<cdot> y \<le> (x + y)\<^sup>\<star>"
  by (meson join.sup.boundedE prod_star_closure star_ext)

lemma star_subdist_var_3: "x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
  by (simp add: prod_star_closure star_iso)

text \<open>We now prove variants of sum-elimination laws under a star.
These are also known a denesting laws or as sum-star laws.\<close>

lemma star_denest [simp]: "(x + y)\<^sup>\<star> = (x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star>"
proof (rule antisym)
  have "x + y \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by (metis join.sup.bounded_iff mult_1_right mult_isol_var mult_onel star_ref star_ext)
  thus "(x + y)\<^sup>\<star> \<le> (x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star>"
    by (fact star_iso)
  have "x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
    by (fact star_subdist_var_3)
  thus "(x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
    by (simp add: prod_star_closure star_inductl_star)
qed

lemma star_sum_var [simp]: "(x\<^sup>\<star> + y\<^sup>\<star>)\<^sup>\<star> = (x + y)\<^sup>\<star>"
  by simp

lemma star_denest_var [simp]: "x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> = (x + y)\<^sup>\<star>"
proof (rule antisym)
  have "1 \<le> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    by (metis mult_isol_var mult_oner star_ref)
  moreover have "x \<cdot> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    by (simp add: mult_isor)
  moreover have "y \<cdot> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    by (metis mult_isol_var mult_onel star_1l star_ref)
  ultimately have "1 + (x + y) \<cdot> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    by auto
  thus "(x + y)\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    by (metis mult.assoc mult_oner star_inductl)
  have "(y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> (y\<^sup>\<star> \<cdot> x\<^sup>\<star>)\<^sup>\<star>"
    by (simp add: mult_isol_var star_iso)
  hence "(y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
    by (metis add.commute star_denest)
  moreover have "x\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
    by (fact star_subdist)
  ultimately show "x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
    using prod_star_closure by blast
qed

lemma star_denest_var_2 [simp]: "x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> = (x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star>"
  by simp

lemma star_denest_var_3 [simp]: "x\<^sup>\<star> \<cdot> (y\<^sup>\<star> \<cdot> x\<^sup>\<star>)\<^sup>\<star> = (x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star>"
  by simp

lemma star_denest_var_4 [ac_simps]: "(y\<^sup>\<star> \<cdot> x\<^sup>\<star>)\<^sup>\<star> = (x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star>"
  by (metis add_comm star_denest)

lemma star_denest_var_5 [ac_simps]: "x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> = y\<^sup>\<star> \<cdot> (x \<cdot> y\<^sup>\<star>)\<^sup>\<star>"
  by (simp add: star_denest_var_4)

lemma "x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<star> = (x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<star>"
(*nitpick [expect=genuine]*)
  oops


lemma star_denest_var_6 [simp]: "x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<cdot> (x + y)\<^sup>\<star> = (x + y)\<^sup>\<star>"
  using mult_assoc by simp

lemma star_denest_var_7 [simp]: "(x + y)\<^sup>\<star> \<cdot> x\<^sup>\<star> \<cdot> y\<^sup>\<star> = (x + y)\<^sup>\<star>"
proof (rule antisym)
  have "(x + y)\<^sup>\<star> \<cdot> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<le> (x + y)\<^sup>\<star> \<cdot> (x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star>"
    by (simp add: mult_assoc)
  thus "(x + y)\<^sup>\<star> \<cdot> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
    by simp
  have "1 \<le> (x + y)\<^sup>\<star> \<cdot> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by (metis dual_order.trans mult_1_left mult_isor star_ref)
  moreover have "(x + y) \<cdot> (x + y)\<^sup>\<star> \<cdot> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<le> (x + y)\<^sup>\<star> \<cdot> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    using mult_isor star_1l by presburger
  ultimately have "1 + (x + y) \<cdot> (x + y)\<^sup>\<star> \<cdot> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<le> (x + y)\<^sup>\<star> \<cdot> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by simp
  thus "(x + y)\<^sup>\<star> \<le> (x + y)\<^sup>\<star> \<cdot> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by (metis mult.assoc star_inductl_one)
qed

lemma star_denest_var_8 [simp]: "x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<cdot> (x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star> = (x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star>"
  by (simp add: mult_assoc)

lemma star_denest_var_9 [simp]: "(x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star> \<cdot> x\<^sup>\<star> \<cdot> y\<^sup>\<star> = (x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star>"
  using star_denest_var_7 by simp

text \<open>The following statements are well known from term
rewriting. They are all variants of the Church-Rosser theorem in
Kleene algebra~\cite{struth06churchrosser}. But first we prove a law
relating two confluence properties.\<close>

lemma confluence_var [iff]: "y \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<longleftrightarrow> y\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
proof
  assume "y \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
  thus "y\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    using star_sim1 by fastforce
next
  assume "y\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
  thus "y \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by (meson mult_isor order_trans star_ext)
qed

lemma church_rosser [intro]: "y\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<Longrightarrow> (x + y)\<^sup>\<star> = x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
proof (rule antisym)
  assume "y\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
  hence "x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<cdot> (x\<^sup>\<star> \<cdot> y\<^sup>\<star>) \<le> x\<^sup>\<star> \<cdot> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by (metis mult_isol mult_isor mult.assoc)
  hence "x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<cdot> (x\<^sup>\<star> \<cdot> y\<^sup>\<star>) \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by (simp add: mult_assoc)
  moreover have "1 \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by (metis dual_order.trans mult_1_right mult_isol star_ref)
  ultimately have "1 + x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<cdot> (x\<^sup>\<star> \<cdot> y\<^sup>\<star>) \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by simp
  hence "(x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by (simp add: star_inductl_one)
  thus "(x + y)\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by simp
  thus "x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<le> (x + y)\<^sup>\<star>"
    by simp 
qed

lemma church_rosser_var: "y \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<Longrightarrow> (x + y)\<^sup>\<star> = x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
  by fastforce

lemma church_rosser_to_confluence: "(x + y)\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<Longrightarrow> y\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
  by (metis add_comm eq_iff star_subdist_var_3)

lemma church_rosser_equiv: "y\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<longleftrightarrow> (x + y)\<^sup>\<star> = x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
  using church_rosser_to_confluence eq_iff by blast

lemma confluence_to_local_confluence: "y\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<Longrightarrow> y \<cdot> x \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
  by (meson mult_isol_var order_trans star_ext)


lemma "y \<cdot> x \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<Longrightarrow> y\<^sup>\<star> \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
(*nitpick [expect=genuine]*)
  oops

lemma "y \<cdot> x \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<Longrightarrow> (x + y)\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
  (* nitpick [expect=genuine] *) oops

text \<open>
More variations could easily be proved. The last counterexample shows
that Newman's lemma needs a wellfoundedness assumption. This is well
known.
\<close>


text \<open>The next lemmas relate the reflexive transitive closure and
the transitive closure.\<close>

lemma sup_id_star1: "1 \<le> x \<Longrightarrow> x \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
proof -
  assume "1 \<le> x"
  hence " x\<^sup>\<star> \<le> x \<cdot> x\<^sup>\<star>"
    using mult_isor by fastforce
  thus "x \<cdot> x\<^sup>\<star> = x\<^sup>\<star>"
    by (simp add: eq_iff)
qed

lemma sup_id_star2: "1 \<le> x \<Longrightarrow> x\<^sup>\<star> \<cdot> x = x\<^sup>\<star>"
  by (metis order.antisym mult_isol mult_oner star_1r)

lemma "1 + x\<^sup>\<star> \<cdot> x = x\<^sup>\<star>"
(*nitpick [expect=genuine]*)
  oops

lemma "(x \<cdot> y)\<^sup>\<star> \<cdot> x = x \<cdot> (y \<cdot> x)\<^sup>\<star>"
(*nitpick [expect=genuine]*)
  oops

lemma "x \<cdot> x = x \<Longrightarrow> x\<^sup>\<star> = 1 + x"
(* nitpick [expect=genuine] *) 
  oops

end (* left_pre_kleene_algebra *)


subsection \<open>Left Kleene Algebras\<close>

class left_kleene_algebra = left_pre_kleene_algebra + dioid_one

begin

text \<open>In left Kleene algebras the non-fact @{prop "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"}
is a good challenge for counterexample generators. A model of left
Kleene algebras in which the right star induction law does not hold
has been given by Kozen~\cite{kozen90kleene}.\<close>

text \<open>We now show that the right unfold law becomes an equality.\<close>

lemma star_unfoldr_eq [simp]: "1 + x\<^sup>\<star> \<cdot> x = x\<^sup>\<star>"
proof (rule antisym)
  show "1 + x\<^sup>\<star> \<cdot> x \<le> x\<^sup>\<star>"
    by (fact star_unfoldr)
  have "1 + x \<cdot> (1 + x\<^sup>\<star> \<cdot> x) = 1 + (1 + x \<cdot> x\<^sup>\<star>) \<cdot> x"
    using distrib_left distrib_right mult_1_left mult_1_right mult_assoc by presburger
  also have "... = 1 + x\<^sup>\<star> \<cdot> x"
    by simp
  finally show "x\<^sup>\<star> \<le> 1 + x\<^sup>\<star> \<cdot> x"
    by (simp add: star_inductl_one)
qed

text \<open>The following more complex unfold law has been used as an
axiom, called prodstar, by Conway~\cite{conway71regular}.\<close>

lemma star_prod_unfold [simp]: "1 + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y = (x \<cdot> y)\<^sup>\<star>"
proof (rule antisym)
  have "(x \<cdot> y)\<^sup>\<star> = 1 + (x \<cdot> y)\<^sup>\<star> \<cdot> x \<cdot> y"
    by (simp add: mult_assoc)
  thus "(x \<cdot> y)\<^sup>\<star> \<le> 1 + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y"
    by (metis join.sup_mono mult_isor order_refl star_slide1)
  have "1 + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y \<le> 1 + x \<cdot> y \<cdot>  (x \<cdot> y)\<^sup>\<star>"
    by (metis join.sup_mono eq_refl mult.assoc mult_isol star_slide1)
  thus "1 + x \<cdot> (y \<cdot> x)\<^sup>\<star> \<cdot> y \<le> (x \<cdot> y)\<^sup>\<star>"
    by simp
qed

text \<open>The slide laws, which have previously been inequalities, now
become equations.\<close>

lemma star_slide [ac_simps]: "(x \<cdot> y)\<^sup>\<star> \<cdot> x = x \<cdot> (y \<cdot> x)\<^sup>\<star>"
proof -
  have "x \<cdot> (y \<cdot> x)\<^sup>\<star> = x \<cdot> (1 + y \<cdot> (x \<cdot> y)\<^sup>\<star> \<cdot> x)"
    by simp
  also have "... = (1 + x \<cdot> y \<cdot> (x \<cdot> y)\<^sup>\<star>) \<cdot> x"
    by (simp add: distrib_left mult_assoc)
  finally show ?thesis
    by simp
qed

lemma star_slide_var [ac_simps]: "x\<^sup>\<star> \<cdot> x = x \<cdot> x\<^sup>\<star>"
  by (metis mult_onel mult_oner star_slide)

lemma star_sum_unfold_var [simp]: "1 + x\<^sup>\<star> \<cdot> (x + y)\<^sup>\<star> \<cdot> y\<^sup>\<star> = (x + y)\<^sup>\<star>"
  by (metis star_denest star_denest_var_3 star_denest_var_4 star_plus_one star_slide)

text \<open>The following law shows how starred sums can be unfolded.\<close>

lemma star_sum_unfold [simp]: "x\<^sup>\<star> + x\<^sup>\<star> \<cdot> y \<cdot> (x + y)\<^sup>\<star> = (x + y)\<^sup>\<star>"
proof -
  have "(x + y)\<^sup>\<star> = x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star> )\<^sup>\<star>"
    by simp
  also have "... = x\<^sup>\<star> \<cdot> (1 + y \<cdot> x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star> )\<^sup>\<star>)"
    by simp
  also have "... = x\<^sup>\<star> \<cdot> (1 + y \<cdot> (x + y)\<^sup>\<star>)"
    by (simp add: mult.assoc)
  finally show ?thesis
    by (simp add: distrib_left mult_assoc)
qed

text \<open>The following property appears in process algebra.\<close>

lemma troeger: "(x + y)\<^sup>\<star> \<cdot> z = x\<^sup>\<star> \<cdot> (y \<cdot> (x + y)\<^sup>\<star> \<cdot> z + z)"
proof -
  have "(x + y)\<^sup>\<star> \<cdot> z = x\<^sup>\<star> \<cdot> z + x\<^sup>\<star> \<cdot> y \<cdot> (x + y)\<^sup>\<star> \<cdot> z"
    by (metis (full_types) distrib_right star_sum_unfold)
  thus ?thesis
    by (simp add: add_commute distrib_left mult_assoc)
qed

text \<open>The following properties are related to a property from
propositional dynamic logic which has been attributed to Albert
Meyer~\cite{harelkozentiuryn00dynamic}. Here we prove it as a theorem
of Kleene algebra.\<close>

lemma star_square: "(x \<cdot> x)\<^sup>\<star> \<le> x\<^sup>\<star>"
proof -
  have "x \<cdot> x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (simp add: prod_star_closure)
  thus ?thesis
    by (simp add: star_inductl_star)  
qed

lemma meyer_1 [simp]: "(1 + x) \<cdot> (x \<cdot> x)\<^sup>\<star> = x\<^sup>\<star>"
proof (rule antisym)
  have "x \<cdot>  (1 + x) \<cdot> (x \<cdot> x)\<^sup>\<star> = x \<cdot> (x \<cdot> x)\<^sup>\<star> + x \<cdot> x \<cdot> (x \<cdot> x)\<^sup>\<star>"
    by (simp add: distrib_left)
  also have "... \<le> x \<cdot> (x \<cdot> x)\<^sup>\<star> + (x \<cdot> x)\<^sup>\<star>"
    using join.sup_mono star_1l by blast
  finally have "x \<cdot>  (1 + x) \<cdot> (x \<cdot> x)\<^sup>\<star> \<le> (1 + x) \<cdot> (x \<cdot> x)\<^sup>\<star>"
    by (simp add: join.sup_commute)
  moreover have "1 \<le> (1 + x) \<cdot> (x \<cdot> x)\<^sup>\<star>"
    using join.sup.coboundedI1 by auto
  ultimately have "1 + x \<cdot> (1 + x) \<cdot> (x \<cdot> x)\<^sup>\<star> \<le> (1 + x) \<cdot> (x \<cdot> x)\<^sup>\<star>"
    by auto
  thus "x\<^sup>\<star> \<le> (1 + x) \<cdot> (x \<cdot> x)\<^sup>\<star>"
    by (simp add: star_inductl_one mult_assoc)
  show "(1 + x) \<cdot> (x \<cdot> x)\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (simp add: prod_star_closure star_square)
qed

text \<open>The following lemma says that transitive elements are equal to
their transitive closure.\<close>

lemma tc: "x \<cdot> x \<le> x \<Longrightarrow> x\<^sup>\<star> \<cdot> x = x"
proof -
  assume "x \<cdot> x \<le> x"
  hence "x + x \<cdot> x \<le> x"
    by simp
  hence "x\<^sup>\<star> \<cdot> x \<le> x"
    by (fact star_inductl)
  thus  "x\<^sup>\<star> \<cdot> x = x"
    by (metis mult_isol mult_oner star_ref star_slide_var eq_iff)
qed

lemma tc_eq: "x \<cdot> x = x \<Longrightarrow> x\<^sup>\<star> \<cdot> x = x"
  by (auto intro: tc)


text \<open>The next fact has been used by Boffa~\cite{boffa90remarque} to
axiomatise the equational theory of regular expressions.\<close>

lemma boffa_var: "x \<cdot> x \<le> x \<Longrightarrow> x\<^sup>\<star> = 1 + x"
proof -
  assume "x \<cdot> x \<le> x"
  moreover have "x\<^sup>\<star> = 1 + x\<^sup>\<star> \<cdot> x"
    by simp
  ultimately show "x\<^sup>\<star> = 1 + x"
    by (simp add: tc)
qed

lemma boffa: "x \<cdot> x = x \<Longrightarrow> x\<^sup>\<star> = 1 + x"
  by (auto intro: boffa_var)

(*
text {*
For the following two lemmas, Isabelle could neither find a
counterexample nor a proof automatically.
*}

lemma "z \<cdot> x \<le> y \<cdot> z \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y\<^sup>\<star> \<cdot> z"
  -- "unfortunately, no counterexample found"
oops

lemma star_sim3: "z \<cdot> x = y \<cdot> z \<Longrightarrow> z \<cdot> x\<^sup>\<star> = y\<^sup>\<star> \<cdot> z"
  -- "we conjecture that this is not provable"
oops
*)

end (* left_kleene_algebra *)


subsection \<open>Left Kleene Algebras with Zero\<close>

text \<open>
There are applications where only a left zero is assumed, for instance
in the context of total correctness and for demonic refinement
algebras~\cite{vonwright04refinement}.
\<close>

class left_kleene_algebra_zerol = left_kleene_algebra + dioid_one_zerol
begin

sublocale conway: near_conway_base_zerol star
  by standard (simp_all add: local.star_slide)

lemma star_zero [simp]: "0\<^sup>\<star> = 1"
  by (rule local.conway.zero_dagger)

text \<open>
In principle,~$1$ could therefore be defined from~$0$ in this setting.
\<close>

end (* left_kleene_algebra_zerol *)


class left_kleene_algebra_zero = left_kleene_algebra_zerol + dioid_one_zero


subsection \<open>Pre-Kleene Algebras\<close>

text \<open>Pre-Kleene algebras are essentially probabilistic Kleene
algebras~\cite{mciverweber05pka}.  They have a weaker right star
unfold axiom. We are still looking for theorems that could be proved
in this setting.\<close>

class pre_kleene_algebra = left_pre_kleene_algebra +
  assumes weak_star_unfoldr: "z + y \<cdot> (x + 1) \<le> y \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"

subsection \<open>Kleene Algebras\<close>

class kleene_algebra_zerol = left_kleene_algebra_zerol + 
  assumes star_inductr: "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"

begin

lemma star_sim2: "z \<cdot> x \<le> y \<cdot> z \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y\<^sup>\<star> \<cdot> z"
proof -
  assume "z \<cdot> x \<le> y \<cdot> z"
  hence "y\<^sup>\<star> \<cdot> z \<cdot> x \<le> y\<^sup>\<star> \<cdot> y \<cdot> z"
    using mult_isol mult_assoc by auto
  also have "... \<le> y\<^sup>\<star> \<cdot> z"
    by (simp add: mult_isor)
  finally have "y\<^sup>\<star> \<cdot> z \<cdot> x \<le> y\<^sup>\<star> \<cdot> z"
    by simp
  moreover have "z \<le> y\<^sup>\<star> \<cdot> z"
    using mult_isor star_ref by fastforce
  ultimately have "z + y\<^sup>\<star> \<cdot> z \<cdot> x \<le> y\<^sup>\<star> \<cdot> z"
    by simp
  thus "z \<cdot> x\<^sup>\<star> \<le> y\<^sup>\<star> \<cdot> z"
    by (simp add: star_inductr)
qed

sublocale conway: pre_conway star
  by standard (simp add: star_sim2)

lemma star_inductr_var: "y \<cdot> x \<le> y \<Longrightarrow> y \<cdot> x\<^sup>\<star> \<le> y"
  by (simp add: star_inductr)

lemma star_inductr_var_equiv: "y \<cdot> x \<le> y \<longleftrightarrow> y \<cdot> x\<^sup>\<star> \<le> y"
  by (meson order_trans mult_isol star_ext star_inductr_var)

lemma star_sim3: "z \<cdot> x = y \<cdot> z \<Longrightarrow> z \<cdot> x\<^sup>\<star> = y\<^sup>\<star> \<cdot> z"
  by (simp add: eq_iff star_sim1 star_sim2)

lemma star_sim4: "x \<cdot> y \<le>  y \<cdot> x \<Longrightarrow> x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<le> y\<^sup>\<star> \<cdot> x\<^sup>\<star>"
  by (auto intro: star_sim1 star_sim2)

lemma star_inductr_eq: "z + y \<cdot> x = y \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"
  by (auto intro: star_inductr)

lemma star_inductr_var_eq: "y \<cdot> x = y \<Longrightarrow> y \<cdot> x\<^sup>\<star> \<le> y"
  by (auto intro: star_inductr_var)

lemma star_inductr_var_eq2: "y \<cdot> x = y \<Longrightarrow> y \<cdot> x\<^sup>\<star> = y"
  by (metis mult_onel star_one star_sim3)

lemma bubble_sort: "y \<cdot> x \<le> x \<cdot> y \<Longrightarrow> (x + y)\<^sup>\<star> = x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
  by (fastforce intro: star_sim4)

lemma independence1: "x \<cdot> y = 0 \<Longrightarrow> x\<^sup>\<star> \<cdot> y = y"
proof -
  assume "x \<cdot> y = 0"
  moreover have "x\<^sup>\<star> \<cdot> y = y + x\<^sup>\<star> \<cdot> x \<cdot> y"
    by (metis distrib_right mult_onel star_unfoldr_eq)
  ultimately show "x\<^sup>\<star> \<cdot> y = y"
    by (metis add_0_left add.commute join.sup_ge1 eq_iff star_inductl_eq)
qed

lemma independence2: "x \<cdot> y = 0 \<Longrightarrow> x \<cdot> y\<^sup>\<star> = x"
  by (metis annil mult_onel star_sim3 star_zero)

lemma lazycomm_var: "y \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star> + y \<longleftrightarrow> y \<cdot> x\<^sup>\<star> \<le> x \<cdot> (x + y)\<^sup>\<star> + y"
proof
  let ?t = "x \<cdot> (x + y)\<^sup>\<star>"
  assume hyp: "y \<cdot> x \<le> ?t + y"
  have "(?t + y) \<cdot> x = ?t \<cdot> x + y \<cdot> x"
    by (fact distrib_right)
  also have "... \<le> ?t \<cdot> x + ?t + y"
    using hyp join.sup.coboundedI2 join.sup_assoc by auto
  also have "... \<le> ?t + y"
    using eq_refl join.sup_least join.sup_mono mult_isol prod_star_closure star_subdist_var_1 mult_assoc by presburger
  finally have "y + (?t + y) \<cdot> x \<le> ?t + y"
    by simp
  thus "y \<cdot> x\<^sup>\<star> \<le> x \<cdot> (x + y)\<^sup>\<star> + y"
    by (fact star_inductr)
next
  assume "y \<cdot> x\<^sup>\<star> \<le> x \<cdot> (x + y)\<^sup>\<star> + y"
  thus "y \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star> + y"
    using dual_order.trans mult_isol star_ext by blast
qed

lemma arden_var: "(\<forall>y v. y \<le> x \<cdot> y + v \<longrightarrow> y \<le> x\<^sup>\<star> \<cdot> v) \<Longrightarrow> z = x \<cdot> z + w \<Longrightarrow> z = x\<^sup>\<star> \<cdot> w"
  by (auto simp: add_comm eq_iff star_inductl_eq)

lemma "(\<forall>x y. y \<le> x \<cdot> y \<longrightarrow> y = 0) \<Longrightarrow> y \<le> x \<cdot> y + z \<Longrightarrow> y \<le> x\<^sup>\<star> \<cdot> z"
  by (metis eq_refl mult_onel)

end

text \<open>Finally, here come the Kleene algebras \`a~la
Kozen~\cite{kozen94complete}. We only prove quasi-identities in this
section. Since left Kleene algebras are complete with respect to the
equational theory of regular expressions and regular languages, all
identities hold already without the right star induction axiom.\<close>

class kleene_algebra = left_kleene_algebra_zero +
  assumes star_inductr': "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"
begin

subclass kleene_algebra_zerol 
  by standard (simp add: star_inductr')

sublocale conway_zerol: conway star ..

text \<open>
The next lemma shows that opposites of Kleene algebras (i.e., Kleene
algebras with the order of multiplication swapped) are again Kleene
algebras.
\<close>

lemma dual_kleene_algebra:
  "class.kleene_algebra (+) (\<odot>) 1 0 (\<le>) (<) star"
proof
  fix x y z :: 'a
  show "(x \<odot> y) \<odot> z = x \<odot> (y \<odot> z)"
    by (metis mult.assoc opp_mult_def)
  show "(x + y) \<odot> z = x \<odot> z + y \<odot> z"
    by (metis opp_mult_def distrib_left)
  show "1 \<odot> x = x"
    by (metis mult_oner opp_mult_def)
  show "x \<odot> 1 = x"
    by (metis mult_onel opp_mult_def)
  show "0 + x = x"
    by (fact add_zerol)
  show "0 \<odot> x = 0"
    by (metis annir opp_mult_def)
   show "x \<odot> 0 = 0"
    by (metis annil opp_mult_def)
  show "x + x = x"
    by (fact add_idem)
  show "x \<odot> (y + z) = x \<odot> y + x \<odot> z"
    by (metis distrib_right opp_mult_def)
  show "z \<odot> x \<le> z \<odot> (x + y)"
    by (metis mult_isor opp_mult_def order_prop)
  show "1 + x \<odot> x\<^sup>\<star> \<le> x\<^sup>\<star>"
    by (metis opp_mult_def order_refl star_slide_var star_unfoldl_eq)
  show "z + x \<odot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<odot> z \<le> y"
    by (metis opp_mult_def star_inductr)
  show "z + y \<odot> x \<le> y \<Longrightarrow> z \<odot> x\<^sup>\<star> \<le> y"
    by (metis opp_mult_def star_inductl)
qed

end (* kleene_algebra *)

text \<open>We finish with some properties on (multiplicatively)
commutative Kleene algebras. A chapter in Conway's
book~\cite{conway71regular} is devoted to this topic.\<close>

class commutative_kleene_algebra = kleene_algebra +
  assumes mult_comm [ac_simps]: "x \<cdot> y = y \<cdot> x"

begin

lemma conway_c3 [simp]: "(x + y)\<^sup>\<star> = x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
  using church_rosser mult_comm by auto

lemma conway_c4: "(x\<^sup>\<star> \<cdot> y)\<^sup>\<star> = 1 + x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<cdot> y"
  by (metis conway_c3 star_denest_var star_prod_unfold)

lemma cka_1: "(x \<cdot> y)\<^sup>\<star> \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
  by (metis conway_c3 star_invol star_iso star_subdist_var_2)

lemma cka_2 [simp]: "x\<^sup>\<star> \<cdot> (x\<^sup>\<star> \<cdot> y)\<^sup>\<star> = x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
  by (metis conway_c3 mult_comm star_denest_var)

lemma conway_c4_var [simp]: "(x\<^sup>\<star> \<cdot> y\<^sup>\<star>)\<^sup>\<star> = x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
  by (metis conway_c3 star_invol)

lemma conway_c2_var: "(x \<cdot> y)\<^sup>\<star> \<cdot> x \<cdot> y \<cdot> y\<^sup>\<star> \<le> (x \<cdot> y)\<^sup>\<star> \<cdot> y\<^sup>\<star>"
  by (metis mult_isor star_1r mult_assoc)

lemma conway_c2 [simp]: "(x \<cdot> y)\<^sup>\<star> \<cdot> (x\<^sup>\<star> + y\<^sup>\<star>) = x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
proof (rule antisym)
  show "(x \<cdot> y)\<^sup>\<star> \<cdot> (x\<^sup>\<star> + y\<^sup>\<star>) \<le> x\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    by (metis cka_1 conway_c3 prod_star_closure star_ext star_sum_var)
  have "x \<cdot> (x \<cdot> y)\<^sup>\<star> \<cdot> (x\<^sup>\<star> + y\<^sup>\<star>) = x \<cdot> (x \<cdot> y)\<^sup>\<star> \<cdot> (x\<^sup>\<star> + 1 + y \<cdot> y\<^sup>\<star>)"
    by (simp add: add_assoc)
  also have "... = x \<cdot> (x \<cdot> y)\<^sup>\<star> \<cdot> (x\<^sup>\<star> + y \<cdot> y\<^sup>\<star>)"
    by (simp add: add_commute)
  also have "... = (x \<cdot> y)\<^sup>\<star> \<cdot> (x \<cdot> x\<^sup>\<star>) + (x \<cdot> y)\<^sup>\<star> \<cdot> x \<cdot> y \<cdot> y\<^sup>\<star>"
    using distrib_left mult_comm mult_assoc by force
  also have "... \<le> (x \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<star> + (x \<cdot> y)\<^sup>\<star> \<cdot> x \<cdot> y \<cdot> y\<^sup>\<star>"
    using add_iso mult_isol by force
  also have "... \<le> (x \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<star> + (x \<cdot> y)\<^sup>\<star> \<cdot> y\<^sup>\<star>"
    using conway_c2_var join.sup_mono by blast
  also have "... = (x \<cdot> y)\<^sup>\<star> \<cdot> (x\<^sup>\<star> + y\<^sup>\<star>)"
    by (simp add: distrib_left)
  finally have "x \<cdot> (x \<cdot> y)\<^sup>\<star> \<cdot> (x\<^sup>\<star> + y\<^sup>\<star>) \<le> (x \<cdot> y)\<^sup>\<star> \<cdot> (x\<^sup>\<star> + y\<^sup>\<star>)" .
  moreover have "y\<^sup>\<star> \<le> (x \<cdot> y)\<^sup>\<star> \<cdot> (x\<^sup>\<star> + y\<^sup>\<star>)"
    by (metis dual_order.trans join.sup_ge2 mult_1_left mult_isor star_ref)
  ultimately have "y\<^sup>\<star> + x \<cdot> (x \<cdot> y)\<^sup>\<star> \<cdot> (x\<^sup>\<star> + y\<^sup>\<star>) \<le> (x \<cdot> y)\<^sup>\<star> \<cdot> (x\<^sup>\<star> + y\<^sup>\<star>)"
    by simp
  thus "x\<^sup>\<star> \<cdot> y\<^sup>\<star> \<le> (x \<cdot> y)\<^sup>\<star> \<cdot> (x\<^sup>\<star> + y\<^sup>\<star>)"
    by (simp add: mult.assoc star_inductl)
qed

end (* commutative_kleene_algebra *)

end
