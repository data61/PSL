(* Title:      Omega Algebra
   Author:     Alasdair Armstrong, Georg Struth, Tjark Weber
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

section \<open>Omega Algebras\<close>

theory Omega_Algebra
imports Kleene_Algebra
begin

text \<open>
\emph{Omega algebras}~\cite{cohen00omega} extend Kleene algebras by an
$\omega$-operation that axiomatizes infinite iteration (just like the
Kleene star axiomatizes finite iteration).
\<close>


subsection \<open>Left Omega Algebras\<close>

text \<open>
In this section we consider \emph{left omega algebras}, i.e., omega
algebras based on left Kleene algebras. Surprisingly, we are still
looking for statements mentioning~$\omega$ that are true in omega
algebras, but do not already hold in left omega algebras.
\<close>

class left_omega_algebra = left_kleene_algebra_zero + omega_op +
  assumes omega_unfold: "x\<^sup>\<omega> \<le> x \<cdot> x\<^sup>\<omega>"
  and omega_coinduct: "y \<le> z + x \<cdot> y \<Longrightarrow> y \<le> x\<^sup>\<omega> + x\<^sup>\<star> \<cdot> z"
begin

text \<open>First we prove some variants of the coinduction axiom.\<close>

lemma omega_coinduct_var1: "y \<le> 1 + x \<cdot> y \<Longrightarrow> y \<le> x\<^sup>\<omega> + x\<^sup>\<star>"
  using local.omega_coinduct by fastforce

lemma  omega_coinduct_var2: "y \<le> x \<cdot> y \<Longrightarrow> y \<le> x\<^sup>\<omega>"
  by (metis add.commute add_zero_l annir omega_coinduct)

lemma omega_coinduct_eq: "y = z + x \<cdot> y \<Longrightarrow> y \<le> x\<^sup>\<omega> + x\<^sup>\<star> \<cdot> z"
  by (simp add: local.omega_coinduct)

lemma omega_coinduct_eq_var1: "y = 1 + x \<cdot> y \<Longrightarrow> y \<le> x\<^sup>\<omega> + x\<^sup>\<star>"
  by (simp add: omega_coinduct_var1)

lemma  omega_coinduct_eq_var2: "y = x \<cdot> y \<Longrightarrow> y \<le> x\<^sup>\<omega>"
  by (simp add: omega_coinduct_var2)

lemma "y = x \<cdot> y + z \<Longrightarrow> y = x\<^sup>\<star> \<cdot> z + x\<^sup>\<omega>"
  (* nitpick [expect=genuine] -- "2-element counterexample" *)
oops

lemma "y = 1 + x \<cdot> y \<Longrightarrow> y = x\<^sup>\<omega> + x\<^sup>\<star>"
  (* nitpick [expect=genuine] -- "3-element counterexample" *)
oops

lemma "y = x \<cdot> y \<Longrightarrow> y = x\<^sup>\<omega>"
  (* nitpick [expect=genuine] -- "2-element counterexample" *)
oops

text \<open>Next we strengthen the unfold law to an equation.\<close>

lemma omega_unfold_eq [simp]: "x \<cdot> x\<^sup>\<omega> = x\<^sup>\<omega>"
proof (rule antisym)
  have "x \<cdot> x\<^sup>\<omega> \<le> x \<cdot> x \<cdot> x\<^sup>\<omega>"
    by (simp add: local.mult_isol local.omega_unfold mult_assoc)
  thus "x \<cdot> x\<^sup>\<omega> \<le> x\<^sup>\<omega>"
    by (simp add: mult_assoc omega_coinduct_var2)
  show  "x\<^sup>\<omega> \<le> x \<cdot> x\<^sup>\<omega>"
    by (fact omega_unfold)
qed

lemma omega_unfold_var: "z + x \<cdot> x\<^sup>\<omega> \<le> x\<^sup>\<omega> + x\<^sup>\<star> \<cdot> z"
  by (simp add: local.omega_coinduct)

lemma "z + x \<cdot> x\<^sup>\<omega> = x\<^sup>\<omega> + x\<^sup>\<star> \<cdot> z"
  (* nitpick [expect=genuine] -- "4-element counterexample" *)
oops

text \<open>We now prove subdistributivity and isotonicity of omega.\<close>

lemma omega_subdist: "x\<^sup>\<omega> \<le> (x + y)\<^sup>\<omega>"
proof -
  have "x\<^sup>\<omega> \<le> (x + y) \<cdot> x\<^sup>\<omega>"
    by simp
  thus ?thesis
    by (rule omega_coinduct_var2)
qed

lemma omega_iso: "x \<le> y \<Longrightarrow> x\<^sup>\<omega> \<le> y\<^sup>\<omega>"
  by (metis less_eq_def omega_subdist)

lemma omega_subdist_var: "x\<^sup>\<omega> + y\<^sup>\<omega> \<le> (x + y)\<^sup>\<omega>"
  by (simp add: omega_iso)

lemma zero_omega [simp]: "0\<^sup>\<omega> = 0"
  by (metis annil omega_unfold_eq)

text \<open>The next lemma is another variant of omega unfold\<close>

lemma star_omega_1 [simp]: "x\<^sup>\<star> \<cdot> x\<^sup>\<omega> = x\<^sup>\<omega>"
proof (rule antisym)
  have "x \<cdot> x\<^sup>\<omega> \<le> x\<^sup>\<omega>"
    by simp
  thus "x\<^sup>\<star> \<cdot> x\<^sup>\<omega> \<le> x\<^sup>\<omega>"
    by simp
  show "x\<^sup>\<omega> \<le> x\<^sup>\<star> \<cdot> x\<^sup>\<omega>"
    using local.star_inductl_var_eq2 by auto
qed

text \<open>The next lemma says that~@{term "1\<^sup>\<omega>"} is the maximal element
of omega algebra. We therefore baptise it~$\top$.\<close>

lemma max_element: "x \<le> 1\<^sup>\<omega>"
  by (simp add: omega_coinduct_eq_var2)

definition top ("\<top>")
  where "\<top> = 1\<^sup>\<omega>"

lemma star_omega_3 [simp]: "(x\<^sup>\<star>)\<^sup>\<omega> = \<top>"
proof -
  have "1 \<le> x\<^sup>\<star>"
    by (fact star_ref)
  hence "\<top> \<le> (x\<^sup>\<star>)\<^sup>\<omega>"
    by (simp add: omega_iso top_def)
  thus ?thesis
    by (simp add: local.order.antisym max_element top_def)
qed

text \<open>The following lemma is strange since it is counterintuitive
that one should be able to append something after an infinite
iteration.\<close>

lemma omega_1: "x\<^sup>\<omega> \<cdot> y \<le> x\<^sup>\<omega>"
proof -
  have "x\<^sup>\<omega> \<cdot> y \<le> x \<cdot> x\<^sup>\<omega> \<cdot> y"
    by simp
  thus ?thesis
    by (metis mult.assoc omega_coinduct_var2)
qed

lemma "x\<^sup>\<omega> \<cdot> y = x\<^sup>\<omega>"
  (*nitpick [expect=genuine] -- "2-element counterexample"*)
oops

lemma omega_sup_id: "1 \<le> y \<Longrightarrow> x\<^sup>\<omega> \<cdot> y = x\<^sup>\<omega>"
  using local.eq_iff local.mult_isol omega_1 by fastforce

lemma omega_top [simp]: "x\<^sup>\<omega> \<cdot> \<top> = x\<^sup>\<omega>"
  by (simp add: max_element omega_sup_id top_def)

lemma supid_omega: "1 \<le> x \<Longrightarrow> x\<^sup>\<omega> = \<top>"
  by (simp add: local.order.antisym max_element omega_iso top_def)

lemma "x\<^sup>\<omega> = \<top> \<Longrightarrow> 1 \<le> x"
  (* nitpick [expect=genuine] -- "4-element counterexample" *)
oops

text \<open>Next we prove a simulation law for the omega operation\<close>

lemma omega_simulation: "z \<cdot> x \<le> y \<cdot> z \<Longrightarrow> z \<cdot> x\<^sup>\<omega> \<le> y\<^sup>\<omega>"
proof -
  assume hyp: "z \<cdot> x \<le> y \<cdot> z"
  have "z \<cdot> x\<^sup>\<omega> = z \<cdot> x \<cdot> x\<^sup>\<omega>"
    by (simp add: mult_assoc)
  also have "... \<le> y \<cdot> z \<cdot> x\<^sup>\<omega>"
    by (simp add: hyp local.mult_isor)
  finally show "z \<cdot> x\<^sup>\<omega> \<le> y\<^sup>\<omega>"
    by (simp add: mult_assoc omega_coinduct_var2)
qed

lemma "z \<cdot> x \<le> y \<cdot> z \<Longrightarrow> z \<cdot> x\<^sup>\<omega> \<le> y\<^sup>\<omega> \<cdot> z"
  (* nitpick [expect=genuine] -- "4-element counterexample" *)
oops

lemma "y \<cdot> z  \<le> z \<cdot> x \<Longrightarrow> y\<^sup>\<omega> \<le> z \<cdot> x\<^sup>\<omega>"
  (* nitpick [expect=genuine] -- "2-element counterexample" *)
oops

lemma "y \<cdot> z  \<le> z \<cdot> x \<Longrightarrow> y\<^sup>\<omega> \<cdot> z \<le> x\<^sup>\<omega>"
  (* nitpick [expect=genuine] -- "4-element counterexample" *)
oops

text \<open>Next we prove transitivity of omega elements.\<close>

lemma omega_omega: "(x\<^sup>\<omega>)\<^sup>\<omega> \<le> x\<^sup>\<omega>"
  by (metis omega_1 omega_unfold_eq)

(*
lemma "x\<^sup>\<omega> \<cdot> x\<^sup>\<omega> = x\<^sup>\<omega>"
nitpick -- "no proof, no counterexample"

lemma "(x\<^sup>\<omega>)\<^sup>\<omega> = x\<^sup>\<omega>"
nitpick -- "no proof, no counterexample"
*)

text \<open>The next lemmas are axioms of Wagner's complete axiomatisation
for omega-regular languages~\cite{Wagner77omega}, but in a slightly
different setting.\<close>

lemma wagner_1 [simp]: "(x \<cdot> x\<^sup>\<star>)\<^sup>\<omega> = x\<^sup>\<omega>"
proof (rule antisym)
  have "(x \<cdot> x\<^sup>\<star>)\<^sup>\<omega> = x \<cdot> x\<^sup>\<star> \<cdot> x \<cdot> x\<^sup>\<star> \<cdot> (x \<cdot> x\<^sup>\<star>)\<^sup>\<omega>"
    by (metis mult.assoc omega_unfold_eq)
  also have "... = x \<cdot> x \<cdot> x\<^sup>\<star> \<cdot> x\<^sup>\<star> \<cdot> (x \<cdot> x\<^sup>\<star>)\<^sup>\<omega>"
    by (simp add: local.star_slide_var mult_assoc)
  also have "... = x \<cdot> x \<cdot> x\<^sup>\<star> \<cdot> (x \<cdot> x\<^sup>\<star>)\<^sup>\<omega>"
    by (simp add: mult_assoc)
  also have "... = x \<cdot> (x \<cdot> x\<^sup>\<star>)\<^sup>\<omega>"
    by (simp add: mult_assoc)
  thus "(x \<cdot> x\<^sup>\<star>)\<^sup>\<omega> \<le> x\<^sup>\<omega>"
    using calculation omega_coinduct_eq_var2 by auto
   show "x\<^sup>\<omega> \<le> (x \<cdot> x\<^sup>\<star>)\<^sup>\<omega>"
    by (simp add: mult_assoc omega_coinduct_eq_var2)
qed

lemma wagner_2_var: "x \<cdot> (y \<cdot> x)\<^sup>\<omega> \<le> (x \<cdot> y)\<^sup>\<omega>"
proof -
  have "x \<cdot> y \<cdot> x \<le> x \<cdot> y \<cdot> x"
    by auto
  thus "x \<cdot> (y \<cdot> x)\<^sup>\<omega> \<le> (x \<cdot> y)\<^sup>\<omega>"
    by (simp add: mult_assoc omega_simulation)
qed

lemma wagner_2 [simp]: "x \<cdot> (y \<cdot> x)\<^sup>\<omega> = (x \<cdot> y)\<^sup>\<omega>"
proof (rule antisym)
  show "x \<cdot> (y \<cdot> x)\<^sup>\<omega> \<le> (x \<cdot> y)\<^sup>\<omega>"
    by (rule wagner_2_var)
  have "(x \<cdot> y)\<^sup>\<omega> = x \<cdot> y \<cdot> (x \<cdot> y)\<^sup>\<omega>"
    by simp
  thus "(x \<cdot> y)\<^sup>\<omega> \<le> x \<cdot> (y \<cdot> x)\<^sup>\<omega>"
    by (metis mult.assoc mult_isol wagner_2_var)
qed

text \<open>
This identity is called~(A8) in Wagner's paper.
\<close>

lemma wagner_3:
assumes "x \<cdot> (x + y)\<^sup>\<omega> + z = (x + y)\<^sup>\<omega>"
shows "(x + y)\<^sup>\<omega> = x\<^sup>\<omega> + x\<^sup>\<star> \<cdot> z"
proof (rule antisym)
  show  "(x + y)\<^sup>\<omega> \<le> x\<^sup>\<omega> + x\<^sup>\<star> \<cdot> z"
    using assms local.join.sup_commute omega_coinduct_eq by auto
  have "x\<^sup>\<star> \<cdot> z \<le> (x + y)\<^sup>\<omega>"
    using assms local.join.sup_commute local.star_inductl_eq by auto
  thus "x\<^sup>\<omega> + x\<^sup>\<star> \<cdot> z \<le> (x + y)\<^sup>\<omega>"
    by (simp add: omega_subdist)
qed

text \<open>
This identity is called~(R4) in Wagner's paper.
\<close>

lemma wagner_1_var [simp]: "(x\<^sup>\<star> \<cdot> x)\<^sup>\<omega> = x\<^sup>\<omega>"
  by (simp add: local.star_slide_var)

lemma star_omega_4 [simp]: "(x\<^sup>\<omega>)\<^sup>\<star> = 1 + x\<^sup>\<omega>"
proof (rule antisym)
  have "(x\<^sup>\<omega>)\<^sup>\<star> = 1 + x\<^sup>\<omega> \<cdot> (x\<^sup>\<omega>)\<^sup>\<star>"
    by simp
  also have "... \<le> 1 + x\<^sup>\<omega> \<cdot> \<top>"
    by (simp add: omega_sup_id)
  finally show "(x\<^sup>\<omega>)\<^sup>\<star> \<le> 1 + x\<^sup>\<omega>"
    by simp
  show "1 + x\<^sup>\<omega> \<le> (x\<^sup>\<omega>)\<^sup>\<star>"
    by simp
qed

lemma star_omega_5 [simp]: "x\<^sup>\<omega> \<cdot> (x\<^sup>\<omega>)\<^sup>\<star> = x\<^sup>\<omega>"
proof (rule antisym)
  show "x\<^sup>\<omega> \<cdot> (x\<^sup>\<omega>)\<^sup>\<star> \<le> x\<^sup>\<omega>"
    by (rule omega_1)
  show "x\<^sup>\<omega> \<le> x\<^sup>\<omega> \<cdot> (x\<^sup>\<omega>)\<^sup>\<star>"
    by (simp add: omega_sup_id)
qed

text \<open>The next law shows how omegas below a sum can be unfolded.\<close>

lemma omega_sum_unfold: "x\<^sup>\<omega> + x\<^sup>\<star> \<cdot> y \<cdot> (x + y)\<^sup>\<omega> = (x + y)\<^sup>\<omega>"
proof -
  have "(x + y)\<^sup>\<omega> = x \<cdot> (x + y)\<^sup>\<omega> + y \<cdot> (x+y)\<^sup>\<omega>"
    by (metis distrib_right omega_unfold_eq)
  thus ?thesis
    by (metis mult.assoc wagner_3)
qed

text \<open>
The next two lemmas apply induction and coinduction to this law.
\<close>

lemma omega_sum_unfold_coind: "(x + y)\<^sup>\<omega> \<le> (x\<^sup>\<star> \<cdot> y)\<^sup>\<omega> + (x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<omega>"
  by (simp add: omega_coinduct_eq omega_sum_unfold)

lemma omega_sum_unfold_ind: "(x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<omega> \<le> (x + y)\<^sup>\<omega>"
  by (simp add: local.star_inductl_eq omega_sum_unfold)

lemma wagner_1_gen: "(x \<cdot> y\<^sup>\<star>)\<^sup>\<omega> \<le> (x + y)\<^sup>\<omega>"
proof -
  have "(x \<cdot> y\<^sup>\<star>)\<^sup>\<omega> \<le> ((x + y) \<cdot> (x + y)\<^sup>\<star>)\<^sup>\<omega>"
    using local.join.le_sup_iff local.join.sup.cobounded1 local.mult_isol_var local.star_subdist_var omega_iso by presburger
  thus ?thesis
    by (metis wagner_1)
qed

lemma wagner_1_var_gen: "(x\<^sup>\<star> \<cdot> y)\<^sup>\<omega> \<le> (x + y)\<^sup>\<omega>"
proof -
  have "(x\<^sup>\<star> \<cdot> y)\<^sup>\<omega> = x\<^sup>\<star> \<cdot> (y \<cdot> x\<^sup>\<star>)\<^sup>\<omega>"
    by simp
  also have "... \<le> x\<^sup>\<star> \<cdot> (x + y)\<^sup>\<omega>"
    by (metis add.commute mult_isol wagner_1_gen)
  also have "... \<le> (x + y)\<^sup>\<star> \<cdot> (x + y)\<^sup>\<omega>"
    using local.mult_isor local.star_subdist by auto
  thus ?thesis
    by (metis calculation order_trans star_omega_1)
qed

text \<open>The next lemma is a variant of the denest law for the star at
the level of omega.\<close>

lemma omega_denest [simp]: "(x + y)\<^sup>\<omega> = (x\<^sup>\<star> \<cdot> y)\<^sup>\<omega> + (x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<omega>"
proof (rule antisym)
  show "(x + y)\<^sup>\<omega> \<le> (x\<^sup>\<star> \<cdot> y)\<^sup>\<omega> + (x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<omega>"
    by (rule omega_sum_unfold_coind)
  have "(x\<^sup>\<star> \<cdot> y)\<^sup>\<omega> \<le>  (x + y)\<^sup>\<omega>"
    by (rule wagner_1_var_gen)
  hence "(x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<omega> \<le> (x + y)\<^sup>\<omega>"
    by (simp add: omega_sum_unfold_ind)
  thus "(x\<^sup>\<star> \<cdot> y)\<^sup>\<omega> + (x\<^sup>\<star> \<cdot> y)\<^sup>\<star> \<cdot> x\<^sup>\<omega> \<le> (x + y)\<^sup>\<omega>"
    by (simp add: wagner_1_var_gen)
qed

text \<open>The next lemma yields a separation theorem for infinite
iteration in the presence of a quasicommutation property. A
nondeterministic loop over~@{term x} and~@{term y} can be refined into
separate infinite loops over~@{term x} and~@{term y}.\<close>

lemma omega_sum_refine:
  assumes "y \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star>"
  shows "(x + y)\<^sup>\<omega> = x\<^sup>\<omega> + x\<^sup>\<star> \<cdot> y\<^sup>\<omega>"
proof (rule antisym)
  have a: "y\<^sup>\<star> \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star>"
    using assms local.quasicomm_var by blast
  have "(x + y)\<^sup>\<omega> = y\<^sup>\<omega> + y\<^sup>\<star> \<cdot> x \<cdot> (x + y)\<^sup>\<omega>"
    by (metis add.commute omega_sum_unfold)
  also have "... \<le> y\<^sup>\<omega> + x \<cdot> (x + y)\<^sup>\<star> \<cdot> (x + y)\<^sup>\<omega>"
    using a local.join.sup_mono local.mult_isol_var by blast
  also have "... \<le> x \<cdot> (x + y)\<^sup>\<omega> + y\<^sup>\<omega>"
    using local.eq_refl local.join.sup_commute mult_assoc star_omega_1 by presburger
  finally show "(x + y)\<^sup>\<omega> \<le> x\<^sup>\<omega> + x\<^sup>\<star> \<cdot> y\<^sup>\<omega>"
    by (metis add_commute local.omega_coinduct)
  have "x\<^sup>\<omega> + x\<^sup>\<star> \<cdot> y\<^sup>\<omega> \<le> (x + y)\<^sup>\<omega> + (x + y)\<^sup>\<star> \<cdot> (x + y)\<^sup>\<omega>"
    using local.join.sup.cobounded2 local.join.sup.mono local.mult_isol_var local.star_subdist omega_iso omega_subdist by presburger
  thus "x\<^sup>\<omega> + x\<^sup>\<star> \<cdot> y\<^sup>\<omega> \<le> (x + y)\<^sup>\<omega>"
    by (metis local.join.sup_idem star_omega_1)
qed

text \<open>The following theorem by Bachmair and
Dershowitz~\cite{bachmair86commutation} is a corollary.\<close>

lemma bachmair_dershowitz:
  assumes "y \<cdot> x \<le> x \<cdot> (x + y)\<^sup>\<star>"
  shows "(x + y)\<^sup>\<omega> = 0 \<longleftrightarrow> x\<^sup>\<omega> + y\<^sup>\<omega> = 0"
  by (metis add_commute assms local.annir local.join.le_bot local.no_trivial_inverse omega_subdist omega_sum_refine)

text \<open>
The next lemmas consider an abstract variant of the empty word
property from language theory and match it with the absence of
infinite iteration~\cite{struth12regeq}.
\<close>

definition (in dioid_one_zero) ewp
where "ewp x \<equiv> \<not>(\<forall>y. y \<le> x \<cdot> y \<longrightarrow> y = 0)"

lemma ewp_super_id1: "0 \<noteq> 1 \<Longrightarrow> 1 \<le> x \<Longrightarrow> ewp x"
  by (metis ewp_def mult_oner)

lemma "0 \<noteq> 1 \<Longrightarrow> 1 \<le> x \<longleftrightarrow> ewp x"
  (* nitpick [expect=genuine] -- "3-element counterexample" *)
oops

text \<open>The next facts relate the absence of the empty word property
with the absence of infinite iteration.\<close>

lemma ewp_neg_and_omega: "\<not> ewp x \<longleftrightarrow> x\<^sup>\<omega> = 0"
proof
  assume "\<not> ewp x"
  hence "\<forall> y. y \<le> x \<cdot> y \<longrightarrow> y = 0"
    by (meson ewp_def)
  thus "x\<^sup>\<omega> = 0"
    by simp
next
  assume "x\<^sup>\<omega> = 0"
  hence "\<forall> y. y \<le> x \<cdot> y \<longrightarrow> y = 0"
    using local.join.le_bot local.omega_coinduct_var2 by blast
  thus "\<not> ewp x"
    by (meson ewp_def)
qed

lemma ewp_alt1: "(\<forall>z. x\<^sup>\<omega> \<le> x\<^sup>\<star> \<cdot> z) \<longleftrightarrow> (\<forall>y z. y \<le> x \<cdot> y + z \<longrightarrow> y \<le> x\<^sup>\<star> \<cdot> z)"
  by (metis add_comm less_eq_def omega_coinduct omega_unfold_eq order_prop)

lemma ewp_alt: "x\<^sup>\<omega> = 0 \<longleftrightarrow> (\<forall>y z. y \<le> x \<cdot> y + z \<longrightarrow> y \<le> x\<^sup>\<star> \<cdot> z)"
  by (metis annir antisym ewp_alt1 join.bot_least)

text \<open>So we have obtained a condition for Arden's lemma in omega
algebra.\<close>

lemma omega_super_id1: "0 \<noteq> 1 \<Longrightarrow> 1 \<le> x \<Longrightarrow> x\<^sup>\<omega> \<noteq> 0"
  using ewp_neg_and_omega ewp_super_id1 by blast

lemma omega_super_id2: "0 \<noteq> 1 \<Longrightarrow> x\<^sup>\<omega> = 0 \<Longrightarrow> \<not>(1 \<le> x)"
  using omega_super_id1 by blast

text \<open>The next lemmas are abstract versions of Arden's lemma from
language theory.\<close>

lemma ardens_lemma_var:
  assumes "x\<^sup>\<omega> = 0" 
  and "z + x \<cdot> y = y"
  shows "x\<^sup>\<star> \<cdot> z = y"
proof -
  have "y \<le> x\<^sup>\<omega> + x\<^sup>\<star> \<cdot> z"
    by (simp add: assms(2) local.omega_coinduct_eq)
  hence "y \<le> x\<^sup>\<star> \<cdot> z"
    by (simp add: assms(1))
  thus "x\<^sup>\<star> \<cdot> z = y"
    by (simp add: assms(2) local.eq_iff local.star_inductl_eq)
qed

lemma ardens_lemma: "\<not> ewp x \<Longrightarrow> z + x \<cdot> y = y \<Longrightarrow> x\<^sup>\<star> \<cdot> z = y"
  by (simp add: ardens_lemma_var ewp_neg_and_omega)

lemma ardens_lemma_equiv:
  assumes "\<not> ewp x"
  shows "z + x \<cdot> y = y \<longleftrightarrow> x\<^sup>\<star> \<cdot> z = y"
  by (metis ardens_lemma_var assms ewp_neg_and_omega local.conway.dagger_unfoldl_distr mult_assoc)

lemma ardens_lemma_var_equiv: "x\<^sup>\<omega> = 0 \<Longrightarrow> (z + x \<cdot> y = y \<longleftrightarrow> x\<^sup>\<star> \<cdot> z = y)"
  by (simp add: ardens_lemma_equiv ewp_neg_and_omega)

lemma arden_conv1: "(\<forall>y z. z + x \<cdot> y = y \<longrightarrow> x\<^sup>\<star> \<cdot> z = y) \<Longrightarrow> \<not> ewp x"
  by (metis add_zero_l annir ewp_neg_and_omega omega_unfold_eq)

lemma arden_conv2: "(\<forall>y z. z + x \<cdot> y = y \<longrightarrow> x\<^sup>\<star> \<cdot> z = y) \<Longrightarrow> x\<^sup>\<omega> = 0"
  using arden_conv1 ewp_neg_and_omega by blast

lemma arden_var3: "(\<forall>y z. z + x \<cdot> y = y \<longrightarrow> x\<^sup>\<star> \<cdot> z = y) \<longleftrightarrow> x\<^sup>\<omega> = 0"
  using arden_conv2 ardens_lemma_var by blast

end

subsection \<open>Omega Algebras\<close>

class omega_algebra = kleene_algebra + left_omega_algebra

end
