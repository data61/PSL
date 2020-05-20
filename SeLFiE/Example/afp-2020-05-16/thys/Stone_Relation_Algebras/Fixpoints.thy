(* Title:      Fixpoints
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Fixpoints\<close>

text \<open>
This theory develops a fixpoint calculus based on partial orders.
Besides fixpoints we consider least prefixpoints and greatest postfixpoints of functions on a partial order.
We do not assume that the underlying structure is complete or that all functions are continuous or isotone.
Assumptions about the existence of fixpoints and necessary properties of the involved functions will be stated explicitly in each theorem.
This way, the results can be instantiated by various structures, such as complete lattices and Kleene algebras, which impose different kinds of restriction.
See, for example, \cite{AartsBackhouseBoitenDoornbosGasterenGeldropHoogendijkVoermansWoude1995,DaveyPriestley2002} for fixpoint calculi in complete lattices.
Our fixpoint calculus contains similar rules, in particular:
\begin{itemize}
\item unfold rule,
\item fixpoint operators preserve isotonicity,
\item square rule,
\item rolling rule,
\item various fusion rules,
\item exchange rule and
\item diagonal rule.
\end{itemize}
All of our rules are based on existence rather than completeness of the underlying structure.
We have applied results from this theory in \cite{Guttmann2012c} and subsequent papers for unifying and reasoning about the semantics of recursion in various relational and matrix-based computation models.
\<close>

theory Fixpoints

imports Stone_Algebras.Lattice_Basics

begin

text \<open>
The whole calculus is based on partial orders only.
\<close>

context order
begin

text \<open>
We first define when an element $x$ is a least/greatest (pre/post)fixpoint of a given function $f$.
\<close>

definition is_fixpoint               :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> bool" where "is_fixpoint              f x \<equiv> f x = x"
definition is_prefixpoint            :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> bool" where "is_prefixpoint           f x \<equiv> f x \<le> x"
definition is_postfixpoint           :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> bool" where "is_postfixpoint          f x \<equiv> f x \<ge> x"
definition is_least_fixpoint         :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> bool" where "is_least_fixpoint        f x \<equiv> f x = x \<and> (\<forall>y . f y = y \<longrightarrow> x \<le> y)"
definition is_greatest_fixpoint      :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> bool" where "is_greatest_fixpoint     f x \<equiv> f x = x \<and> (\<forall>y . f y = y \<longrightarrow> x \<ge> y)"
definition is_least_prefixpoint      :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> bool" where "is_least_prefixpoint     f x \<equiv> f x \<le> x \<and> (\<forall>y . f y \<le> y \<longrightarrow> x \<le> y)"
definition is_greatest_postfixpoint  :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> bool" where "is_greatest_postfixpoint f x \<equiv> f x \<ge> x \<and> (\<forall>y . f y \<ge> y \<longrightarrow> x \<ge> y)"

text \<open>
Next follows the existence of the corresponding fixpoints for a given function $f$.
\<close>

definition has_fixpoint              :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where "has_fixpoint              f \<equiv> \<exists>x . is_fixpoint f x"
definition has_prefixpoint           :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where "has_prefixpoint           f \<equiv> \<exists>x . is_prefixpoint f x"
definition has_postfixpoint          :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where "has_postfixpoint          f \<equiv> \<exists>x . is_postfixpoint f x"
definition has_least_fixpoint        :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where "has_least_fixpoint        f \<equiv> \<exists>x . is_least_fixpoint f x"
definition has_greatest_fixpoint     :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where "has_greatest_fixpoint     f \<equiv> \<exists>x . is_greatest_fixpoint f x"
definition has_least_prefixpoint     :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where "has_least_prefixpoint     f \<equiv> \<exists>x . is_least_prefixpoint f x"
definition has_greatest_postfixpoint :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where "has_greatest_postfixpoint f \<equiv> \<exists>x . is_greatest_postfixpoint f x"

text \<open>
The actual least/greatest (pre/post)fixpoints of a given function $f$ are extracted by the following operators.
\<close>

definition the_least_fixpoint        :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<mu> _"  [201] 200) where "\<mu>  f = (THE x . is_least_fixpoint f x)"
definition the_greatest_fixpoint     :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<nu> _"  [201] 200) where "\<nu>  f = (THE x . is_greatest_fixpoint f x)"
definition the_least_prefixpoint     :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a" ("p\<mu> _" [201] 200) where "p\<mu> f = (THE x . is_least_prefixpoint f x)"
definition the_greatest_postfixpoint :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a" ("p\<nu> _" [201] 200) where "p\<nu> f = (THE x . is_greatest_postfixpoint f x)"

text \<open>
We start with basic consequences of the above definitions.
\<close>

lemma least_fixpoint_unique:
  "has_least_fixpoint f \<Longrightarrow> \<exists>!x . is_least_fixpoint f x"
  using has_least_fixpoint_def is_least_fixpoint_def antisym by auto

lemma greatest_fixpoint_unique:
  "has_greatest_fixpoint f \<Longrightarrow> \<exists>!x . is_greatest_fixpoint f x"
  using has_greatest_fixpoint_def is_greatest_fixpoint_def antisym by auto

lemma least_prefixpoint_unique:
  "has_least_prefixpoint f \<Longrightarrow> \<exists>!x . is_least_prefixpoint f x"
  using has_least_prefixpoint_def is_least_prefixpoint_def antisym by auto

lemma greatest_postfixpoint_unique:
  "has_greatest_postfixpoint f \<Longrightarrow> \<exists>!x . is_greatest_postfixpoint f x"
  using has_greatest_postfixpoint_def is_greatest_postfixpoint_def antisym by auto

lemma least_fixpoint:
  "has_least_fixpoint f \<Longrightarrow> is_least_fixpoint f (\<mu> f)"
  by (simp add: least_fixpoint_unique theI' the_least_fixpoint_def)

lemma greatest_fixpoint:
  "has_greatest_fixpoint f \<Longrightarrow> is_greatest_fixpoint f (\<nu> f)"
  by (simp add: greatest_fixpoint_unique theI' the_greatest_fixpoint_def)

lemma least_prefixpoint:
  "has_least_prefixpoint f \<Longrightarrow> is_least_prefixpoint f (p\<mu> f)"
  by (simp add: least_prefixpoint_unique theI' the_least_prefixpoint_def)

lemma greatest_postfixpoint:
  "has_greatest_postfixpoint f \<Longrightarrow> is_greatest_postfixpoint f (p\<nu> f)"
  by (simp add: greatest_postfixpoint_unique theI' the_greatest_postfixpoint_def)

lemma least_fixpoint_same:
  "is_least_fixpoint f x \<Longrightarrow> x = \<mu> f"
  by (simp add: is_least_fixpoint_def antisym the_equality the_least_fixpoint_def)

lemma greatest_fixpoint_same:
  "is_greatest_fixpoint f x \<Longrightarrow> x = \<nu> f"
  using greatest_fixpoint greatest_fixpoint_unique has_greatest_fixpoint_def by auto

lemma least_prefixpoint_same:
  "is_least_prefixpoint f x \<Longrightarrow> x = p\<mu> f"
  using has_least_prefixpoint_def least_prefixpoint least_prefixpoint_unique by blast

lemma greatest_postfixpoint_same:
  "is_greatest_postfixpoint f x \<Longrightarrow> x = p\<nu> f"
  using greatest_postfixpoint greatest_postfixpoint_unique has_greatest_postfixpoint_def by auto

lemma least_fixpoint_char:
  "is_least_fixpoint f x \<longleftrightarrow> has_least_fixpoint f \<and> x = \<mu> f"
  using has_least_fixpoint_def least_fixpoint_same by auto

lemma least_prefixpoint_char:
  "is_least_prefixpoint f x \<longleftrightarrow> has_least_prefixpoint f \<and> x = p\<mu> f"
  using has_least_prefixpoint_def least_prefixpoint_same by auto

lemma greatest_fixpoint_char:
  "is_greatest_fixpoint f x \<longleftrightarrow> has_greatest_fixpoint f \<and> x = \<nu> f"
  using greatest_fixpoint_same has_greatest_fixpoint_def by auto

lemma greatest_postfixpoint_char:
  "is_greatest_postfixpoint f x \<longleftrightarrow> has_greatest_postfixpoint f \<and> x = p\<nu> f"
  using greatest_postfixpoint_same has_greatest_postfixpoint_def by auto

text \<open>
Next come the unfold rules for least/greatest (pre/post)fixpoints.
\<close>

lemma mu_unfold:
  "has_least_fixpoint f \<Longrightarrow> f (\<mu> f) = \<mu> f"
  using is_least_fixpoint_def least_fixpoint by auto

lemma pmu_unfold:
  "has_least_prefixpoint f \<Longrightarrow> f (p\<mu> f) \<le> p\<mu> f"
  using is_least_prefixpoint_def least_prefixpoint by blast

lemma nu_unfold:
  "has_greatest_fixpoint f \<Longrightarrow> \<nu> f = f (\<nu> f)"
  by (metis is_greatest_fixpoint_def greatest_fixpoint)

lemma pnu_unfold:
  "has_greatest_postfixpoint f \<Longrightarrow> p\<nu> f \<le> f (p\<nu> f)"
  using greatest_postfixpoint is_greatest_postfixpoint_def by auto

text \<open>
Pre-/postfixpoints of isotone functions are fixpoints.
\<close>

lemma least_prefixpoint_fixpoint:
  "has_least_prefixpoint f \<Longrightarrow> isotone f \<Longrightarrow> is_least_fixpoint f (p\<mu> f)"
  using is_least_fixpoint_def is_least_prefixpoint_def least_prefixpoint antisym isotone_def by auto

lemma pmu_mu:
  "has_least_prefixpoint f \<Longrightarrow> isotone f \<Longrightarrow> p\<mu> f = \<mu> f"
  by (simp add: least_fixpoint_same least_prefixpoint_fixpoint)

lemma greatest_postfixpoint_fixpoint:
  "has_greatest_postfixpoint f \<Longrightarrow> isotone f \<Longrightarrow> is_greatest_fixpoint f (p\<nu> f)"
  using greatest_postfixpoint is_greatest_fixpoint_def is_greatest_postfixpoint_def antisym isotone_def by auto

lemma pnu_nu:
  "has_greatest_postfixpoint f \<Longrightarrow> isotone f \<Longrightarrow> p\<nu> f = \<nu> f"
  by (simp add: greatest_fixpoint_same greatest_postfixpoint_fixpoint)

text \<open>
The fixpoint operators preserve isotonicity.
\<close>

lemma pmu_isotone:
  "has_least_prefixpoint f \<Longrightarrow> has_least_prefixpoint g \<Longrightarrow> f \<le>\<le> g \<Longrightarrow> p\<mu> f \<le> p\<mu> g"
  by (metis is_least_prefixpoint_def least_prefixpoint order_trans lifted_less_eq_def)

lemma mu_isotone:
  "has_least_prefixpoint f \<Longrightarrow> has_least_prefixpoint g \<Longrightarrow> isotone f \<Longrightarrow> isotone g \<Longrightarrow> f \<le>\<le> g \<Longrightarrow> \<mu> f \<le> \<mu> g"
  using pmu_isotone pmu_mu by fastforce

lemma pnu_isotone:
  "has_greatest_postfixpoint f \<Longrightarrow> has_greatest_postfixpoint g \<Longrightarrow> f \<le>\<le> g \<Longrightarrow> p\<nu> f \<le> p\<nu> g"
  by (metis greatest_postfixpoint is_greatest_postfixpoint_def order_trans lifted_less_eq_def)

lemma nu_isotone:
  "has_greatest_postfixpoint f \<Longrightarrow> has_greatest_postfixpoint g \<Longrightarrow> isotone f \<Longrightarrow> isotone g \<Longrightarrow> f \<le>\<le> g \<Longrightarrow> \<nu> f \<le> \<nu> g"
  using pnu_isotone pnu_nu by fastforce

text \<open>
The square rule for fixpoints of a function applied twice.
\<close>

lemma mu_square:
  "isotone f \<Longrightarrow> has_least_fixpoint f \<Longrightarrow> has_least_fixpoint (f \<circ> f) \<Longrightarrow> \<mu> f = \<mu> (f \<circ> f)"
  by (metis (no_types, hide_lams) antisym is_least_fixpoint_def isotone_def least_fixpoint_char least_fixpoint_unique o_apply)

lemma nu_square:
  "isotone f \<Longrightarrow> has_greatest_fixpoint f \<Longrightarrow> has_greatest_fixpoint (f \<circ> f) \<Longrightarrow> \<nu> f = \<nu> (f \<circ> f)"
  by (metis (no_types, hide_lams) antisym is_greatest_fixpoint_def isotone_def greatest_fixpoint_char greatest_fixpoint_unique o_apply)

text \<open>
The rolling rule for fixpoints of the composition of two functions.
\<close>

lemma mu_roll:
  assumes "isotone g"
      and "has_least_fixpoint (f \<circ> g)"
      and "has_least_fixpoint (g \<circ> f)"
    shows "\<mu> (g \<circ> f) = g (\<mu> (f \<circ> g))"
proof (rule antisym)
  show "\<mu> (g \<circ> f) \<le> g (\<mu> (f \<circ> g))"
    by (metis assms(2-3) comp_apply is_least_fixpoint_def least_fixpoint)
next
  have "is_least_fixpoint (g \<circ> f) (\<mu> (g \<circ> f))"
    by (simp add: assms(3) least_fixpoint)
  thus "g (\<mu> (f \<circ> g)) \<le> \<mu> (g \<circ> f)"
    by (metis (no_types) assms(1-2) comp_def is_least_fixpoint_def least_fixpoint isotone_def)
qed

lemma nu_roll:
  assumes "isotone g"
      and "has_greatest_fixpoint (f \<circ> g)"
      and "has_greatest_fixpoint (g \<circ> f)"
    shows "\<nu> (g \<circ> f) = g (\<nu> (f \<circ> g))"
proof (rule antisym)
  have 1: "is_greatest_fixpoint (f \<circ> g) (\<nu> (f \<circ> g))"
    by (simp add: assms(2) greatest_fixpoint)
  have "is_greatest_fixpoint (g \<circ> f) (\<nu> (g \<circ> f))"
    by (simp add: assms(3) greatest_fixpoint)
  thus "\<nu> (g \<circ> f) \<le> g (\<nu> (f \<circ> g))"
    using 1 by (metis (no_types) assms(1) comp_def is_greatest_fixpoint_def isotone_def)
next
  show "g (\<nu> (f \<circ> g)) \<le> \<nu> (g \<circ> f)"
    by (metis assms(2-3) comp_apply greatest_fixpoint is_greatest_fixpoint_def)
qed

text \<open>
Least (pre)fixpoints are below greatest (post)fixpoints.
\<close>

lemma mu_below_nu:
  "has_least_fixpoint f \<Longrightarrow> has_greatest_fixpoint f \<Longrightarrow> \<mu> f \<le> \<nu> f"
  using greatest_fixpoint is_greatest_fixpoint_def mu_unfold by auto

lemma pmu_below_pnu_fix:
  "has_fixpoint f \<Longrightarrow> has_least_prefixpoint f \<Longrightarrow> has_greatest_postfixpoint f \<Longrightarrow> p\<mu> f \<le> p\<nu> f"
  by (metis greatest_postfixpoint has_fixpoint_def is_fixpoint_def is_greatest_postfixpoint_def is_least_prefixpoint_def least_prefixpoint order_refl order_trans)

lemma pmu_below_pnu_iso:
  "isotone f \<Longrightarrow> has_least_prefixpoint f \<Longrightarrow> has_greatest_postfixpoint f \<Longrightarrow> p\<mu> f \<le> p\<nu> f"
  using greatest_postfixpoint_fixpoint is_greatest_fixpoint_def is_least_fixpoint_def least_prefixpoint_fixpoint by auto

text \<open>
Several variants of the fusion rule for fixpoints follow.
\<close>

lemma mu_fusion_1:
  assumes "galois l u"
      and "isotone h"
      and "has_least_prefixpoint g"
      and "has_least_fixpoint h"
      and "l (g (u (\<mu> h))) \<le> h (l (u (\<mu> h)))"
    shows "l (p\<mu> g) \<le> \<mu> h"
proof -
  have "l (g (u (\<mu> h))) \<le> \<mu> h"
    by (metis assms(1,2,4,5) galois_char isotone_def order_lesseq_imp mu_unfold)
  thus "l (p\<mu> g) \<le> \<mu> h"
  using assms(1,3) is_least_prefixpoint_def least_prefixpoint galois_def by auto
qed

lemma mu_fusion_2:
  "galois l u \<Longrightarrow> isotone h \<Longrightarrow> has_least_prefixpoint g \<Longrightarrow> has_least_fixpoint h \<Longrightarrow> l \<circ> g \<le>\<le> h \<circ> l \<Longrightarrow> l (p\<mu> g) \<le> \<mu> h"
  by (simp add: mu_fusion_1 lifted_less_eq_def)

lemma mu_fusion_equal_1:
  "galois l u \<Longrightarrow> isotone g \<Longrightarrow> isotone h \<Longrightarrow> has_least_prefixpoint g \<Longrightarrow> has_least_fixpoint h \<Longrightarrow> l (g (u (\<mu> h))) \<le> h(l(u(\<mu> h))) \<Longrightarrow> l (g (p\<mu> g)) = h (l (p\<mu> g)) \<Longrightarrow> \<mu> h = l (p\<mu> g) \<and> \<mu> h = l (\<mu> g)"
  by (metis antisym least_fixpoint least_prefixpoint_fixpoint is_least_fixpoint_def mu_fusion_1 pmu_mu)

lemma mu_fusion_equal_2:
  "galois l u \<Longrightarrow> isotone h \<Longrightarrow> has_least_prefixpoint g \<Longrightarrow> has_least_prefixpoint h \<Longrightarrow> l (g (u (\<mu> h))) \<le> h (l (u (\<mu> h))) \<and> l (g (p\<mu> g)) = h (l (p\<mu> g)) \<longrightarrow> p\<mu> h = l (p\<mu> g) \<and> \<mu> h = l (p\<mu> g)"
  by (metis is_least_prefixpoint_def least_fixpoint_char least_prefixpoint least_prefixpoint_fixpoint antisym galois_char isotone_def mu_fusion_1)

lemma mu_fusion_equal_3:
  assumes "galois l u"
      and "isotone g"
      and "isotone h"
      and "has_least_prefixpoint g"
      and "has_least_fixpoint h"
      and "l \<circ> g = h \<circ> l"
    shows "\<mu> h = l (p\<mu> g)"
      and "\<mu> h = l (\<mu> g)"
proof -
  have "\<forall>x . l (g x) = h (l x)"
    using assms(6) comp_eq_elim by blast
  thus "\<mu> h = l (p\<mu> g)"
    using assms(1-5) mu_fusion_equal_1 by auto
  thus "\<mu> h = l (\<mu> g)"
    by (simp add: assms(2,4) pmu_mu)
qed

lemma mu_fusion_equal_4:
  assumes "galois l u"
      and "isotone h"
      and "has_least_prefixpoint g"
      and "has_least_prefixpoint h"
      and "l \<circ> g = h \<circ> l"
    shows "p\<mu> h = l (p\<mu> g)"
      and "\<mu> h = l (p\<mu> g)"
proof -
  have "\<forall>x . l (g x) = h (l x)"
    using assms(5) comp_eq_elim by blast
  thus "p\<mu> h = l (p\<mu> g)"
    using assms(1-4) mu_fusion_equal_2 by auto
  thus "\<mu> h = l (p\<mu> g)"
    by (simp add: assms(2,4) pmu_mu)
qed

lemma nu_fusion_1:
  assumes "galois l u"
      and "isotone h"
      and "has_greatest_postfixpoint g"
      and "has_greatest_fixpoint h"
      and "h (u (l (\<nu> h))) \<le> u (g (l (\<nu> h)))"
    shows "\<nu> h \<le> u (p\<nu> g)"
proof -
  have "\<nu> h \<le> u (g (l (\<nu> h)))"
    by (metis assms(1,2,4,5) order_trans galois_char isotone_def nu_unfold)
  thus "\<nu> h \<le> u (p\<nu> g)"
    by (metis assms(1,3) greatest_postfixpoint is_greatest_postfixpoint_def ord.galois_def)
qed

lemma nu_fusion_2:
  "galois l u \<Longrightarrow> isotone h \<Longrightarrow> has_greatest_postfixpoint g \<Longrightarrow> has_greatest_fixpoint h \<Longrightarrow> h \<circ> u \<le>\<le> u \<circ> g \<Longrightarrow> \<nu> h \<le> u (p\<nu> g)"
  by (simp add: nu_fusion_1 lifted_less_eq_def)

lemma nu_fusion_equal_1:
  "galois l u \<Longrightarrow> isotone g \<Longrightarrow> isotone h \<Longrightarrow> has_greatest_postfixpoint g \<Longrightarrow> has_greatest_fixpoint h \<Longrightarrow> h (u (l (\<nu> h))) \<le> u (g (l (\<nu> h))) \<Longrightarrow> h (u (p\<nu> g)) = u (g (p\<nu> g)) \<Longrightarrow> \<nu> h = u (p\<nu> g) \<and> \<nu> h = u (\<nu> g)"
  by (metis greatest_fixpoint_char greatest_postfixpoint_fixpoint is_greatest_fixpoint_def antisym nu_fusion_1)

lemma nu_fusion_equal_2:
  "galois l u \<Longrightarrow> isotone h \<Longrightarrow> has_greatest_postfixpoint g \<Longrightarrow> has_greatest_postfixpoint h \<Longrightarrow> h (u (l (\<nu> h))) \<le> u (g (l (\<nu> h))) \<and> h (u (p\<nu> g)) = u (g (p\<nu> g)) \<Longrightarrow> p\<nu> h = u (p\<nu> g) \<and> \<nu> h = u (p\<nu> g)"
  by (metis greatest_fixpoint_char greatest_postfixpoint greatest_postfixpoint_fixpoint is_greatest_postfixpoint_def antisym galois_char nu_fusion_1 isotone_def)

lemma nu_fusion_equal_3:
  assumes "galois l u"
      and "isotone g"
      and "isotone h"
      and "has_greatest_postfixpoint g"
      and "has_greatest_fixpoint h"
      and "h \<circ> u = u \<circ> g"
    shows "\<nu> h = u (p\<nu> g)"
      and "\<nu> h = u (\<nu> g)"
proof -
  have "\<forall>x . u (g x) = h (u x)"
    using assms(6) comp_eq_dest by fastforce
  thus "\<nu> h = u (p\<nu> g)"
    using assms(1-5) nu_fusion_equal_1 by auto
  thus "\<nu> h = u (\<nu> g)"
    by (simp add: assms(2-4) pnu_nu)
qed

lemma nu_fusion_equal_4:
  assumes "galois l u"
      and "isotone h"
      and "has_greatest_postfixpoint g"
      and "has_greatest_postfixpoint h"
      and "h \<circ> u = u \<circ> g"
    shows "p\<nu> h = u (p\<nu> g)"
      and "\<nu> h = u (p\<nu> g)"
proof -
  have "\<forall>x . u (g x) = h (u x)"
    using assms(5) comp_eq_dest by fastforce
  thus "p\<nu> h = u (p\<nu> g)"
    using assms(1-4) nu_fusion_equal_2 by auto
  thus "\<nu> h = u (p\<nu> g)"
    by (simp add: assms(2,4) pnu_nu)
qed

text \<open>
Next come the exchange rules for replacing the first/second function in a composition.
\<close>

lemma mu_exchange_1:
  assumes "galois l u"
      and "isotone g"
      and "isotone h"
      and "has_least_prefixpoint (l \<circ> h)"
      and "has_least_prefixpoint (h \<circ> g)"
      and "has_least_fixpoint (g \<circ> h)"
      and "l \<circ> h \<circ> g \<le>\<le> g \<circ> h \<circ> l"
    shows "\<mu> (l \<circ> h) \<le> \<mu> (g \<circ> h)"
proof -
  have 1: "l \<circ> (h \<circ> g) \<le>\<le> (g \<circ> h) \<circ> l"
    by (simp add: assms(7) rewriteL_comp_comp)
  have "(l \<circ> h) (\<mu> (g \<circ> h)) = l (\<mu> (h \<circ> g))"
    by (metis assms(2,3,5,6) comp_apply least_fixpoint_char least_prefixpoint_fixpoint isotone_def mu_roll)
  also have "... \<le> \<mu> (g \<circ> h)"
    using 1 by (metis assms(1-3,5,6) comp_apply least_fixpoint_char least_prefixpoint_fixpoint isotone_def mu_fusion_2)
  finally have "p\<mu> (l \<circ> h) \<le> \<mu> (g \<circ> h)"
    using assms(4) is_least_prefixpoint_def least_prefixpoint by blast
  thus "\<mu> (l \<circ> h) \<le> \<mu> (g \<circ> h)"
    by (metis assms(1,3,4) galois_char isotone_def least_fixpoint_char least_prefixpoint_fixpoint o_apply)
qed

lemma mu_exchange_2:
  assumes "galois l u"
      and "isotone g"
      and "isotone h"
      and "has_least_prefixpoint (l \<circ> h)"
      and "has_least_prefixpoint (h \<circ> l)"
      and "has_least_prefixpoint (h \<circ> g)"
      and "has_least_fixpoint (g \<circ> h)"
      and "has_least_fixpoint (h \<circ> g)"
      and "l \<circ> h \<circ> g \<le>\<le> g \<circ> h \<circ> l"
    shows "\<mu> (h \<circ> l) \<le> \<mu> (h \<circ> g)"
proof -
  have "\<mu> (h \<circ> l) = h (\<mu> (l \<circ> h))"
    by (metis (no_types, lifting) assms(1,3-5) galois_char isotone_def least_fixpoint_char least_prefixpoint_fixpoint mu_roll o_apply)
  also have "... \<le> h (\<mu> (g \<circ> h))"
    using assms(1-4,6,7,9) isotone_def mu_exchange_1 by blast
  also have "... = \<mu> (h \<circ> g)"
    by (simp add: assms(3,7,8) mu_roll)
  finally show ?thesis
    .
qed

lemma mu_exchange_equal:
  assumes "galois l u"
      and "galois k t"
      and "isotone h"
      and "has_least_prefixpoint (l \<circ> h)"
      and "has_least_prefixpoint (h \<circ> l)"
      and "has_least_prefixpoint (k \<circ> h)"
      and "has_least_prefixpoint (h \<circ> k)"
      and "l \<circ> h \<circ> k = k \<circ> h \<circ> l"
    shows "\<mu> (l \<circ> h) = \<mu> (k \<circ> h)"
      and "\<mu> (h \<circ> l) = \<mu> (h \<circ> k)"
proof -
  have 1: "has_least_fixpoint (k \<circ> h)"
    using assms(2,3,6) least_fixpoint_char least_prefixpoint_fixpoint galois_char isotone_def by auto
  have 2: "has_least_fixpoint (h \<circ> k)"
    using assms(2,3,7) least_fixpoint_char least_prefixpoint_fixpoint galois_char isotone_def by auto
  have 3: "has_least_fixpoint (l \<circ> h)"
    using assms(1,3,4) least_fixpoint_char least_prefixpoint_fixpoint galois_char isotone_def by auto
  have 4: "has_least_fixpoint (h \<circ> l)"
    using assms(1,3,5) least_fixpoint_char least_prefixpoint_fixpoint galois_char isotone_def by auto
  show "\<mu> (h \<circ> l) = \<mu> (h \<circ> k)"
    using 1 2 3 4 assms antisym galois_char lifted_reflexive mu_exchange_2 by auto
  show "\<mu> (l \<circ> h) = \<mu> (k \<circ> h)"
    using 1 2 3 4 assms antisym galois_char lifted_reflexive mu_exchange_1 by auto
qed

lemma nu_exchange_1:
  assumes "galois l u"
      and "isotone g"
      and "isotone h"
      and "has_greatest_postfixpoint (u \<circ> h)"
      and "has_greatest_postfixpoint (h \<circ> g)"
      and "has_greatest_fixpoint (g \<circ> h)"
      and "g \<circ> h \<circ> u \<le>\<le> u \<circ> h \<circ> g"
    shows "\<nu> (g \<circ> h) \<le> \<nu> (u \<circ> h)"
proof -
  have "(g \<circ> h) \<circ> u \<le>\<le> u \<circ> (h \<circ> g)"
    by (simp add: assms(7) o_assoc)
  hence "\<nu> (g \<circ> h) \<le> u (\<nu> (h \<circ> g))"
    by (metis assms(1-3,5,6) greatest_fixpoint_char greatest_postfixpoint_fixpoint isotone_def nu_fusion_2 o_apply)
  also have "... = (u \<circ> h) (\<nu> (g \<circ> h))"
    by (metis assms(2,3,5,6) greatest_fixpoint_char greatest_postfixpoint_fixpoint isotone_def nu_roll o_apply)
  finally have "\<nu> (g \<circ> h) \<le> p\<nu> (u \<circ> h)"
    using assms(4) greatest_postfixpoint is_greatest_postfixpoint_def by blast
  thus "\<nu> (g \<circ> h) \<le> \<nu> (u \<circ> h)"
    using assms(1,3,4) galois_char greatest_fixpoint_char greatest_postfixpoint_fixpoint isotone_def by auto
qed

lemma nu_exchange_2:
  assumes "galois l u"
      and "isotone g"
      and "isotone h"
      and "has_greatest_postfixpoint (u \<circ> h)"
      and "has_greatest_postfixpoint (h \<circ> u)"
      and "has_greatest_postfixpoint (h \<circ> g)"
      and "has_greatest_fixpoint (g \<circ> h)"
      and "has_greatest_fixpoint (h \<circ> g)"
      and "g \<circ> h \<circ> u \<le>\<le> u \<circ> h \<circ> g"
    shows "\<nu> (h \<circ> g) \<le> \<nu> (h \<circ> u)"
proof -
  have "\<nu> (h \<circ> g) = h (\<nu> (g \<circ> h))"
    by (simp add: assms(3,7,8) nu_roll)
  also have "... \<le> h (\<nu> (u \<circ> h))"
    using assms(1-4,6,7,9) isotone_def nu_exchange_1 by blast
  also have "... = \<nu> (h \<circ> u)"
    by (metis (no_types, lifting) assms(1,3-5) galois_char greatest_fixpoint_char greatest_postfixpoint_fixpoint isotone_def nu_roll o_apply)
  finally show "\<nu> (h \<circ> g) \<le> \<nu> (h \<circ> u)"
    .
qed

lemma nu_exchange_equal:
  assumes "galois l u"
      and "galois k t"
      and "isotone h"
      and "has_greatest_postfixpoint (u \<circ> h)"
      and "has_greatest_postfixpoint (h \<circ> u)"
      and "has_greatest_postfixpoint (t \<circ> h)"
      and "has_greatest_postfixpoint (h \<circ> t)"
      and "u \<circ> h \<circ> t = t \<circ> h \<circ> u"
    shows "\<nu> (u \<circ> h) = \<nu> (t \<circ> h)"
      and "\<nu> (h \<circ> u) = \<nu> (h \<circ> t)"
proof -
  have 1: "has_greatest_fixpoint (u \<circ> h)"
    using assms(1,3,4) greatest_fixpoint_char greatest_postfixpoint_fixpoint galois_char isotone_def by auto
  have 2: "has_greatest_fixpoint (h \<circ> u)"
    using assms(1,3,5) greatest_fixpoint_char greatest_postfixpoint_fixpoint galois_char isotone_def by auto
  have 3: "has_greatest_fixpoint (t \<circ> h)"
    using assms(2,3,6) greatest_fixpoint_char greatest_postfixpoint_fixpoint galois_char isotone_def by auto
  have 4: "has_greatest_fixpoint (h \<circ> t)"
    using assms(2,3,7) greatest_fixpoint_char greatest_postfixpoint_fixpoint galois_char isotone_def by auto
  show "\<nu> (u \<circ> h) = \<nu> (t \<circ> h)"
    using 1 2 3 4 assms antisym galois_char lifted_reflexive nu_exchange_1 by auto
  show "\<nu> (h \<circ> u) = \<nu> (h \<circ> t)"
    using 1 2 3 4 assms antisym galois_char lifted_reflexive nu_exchange_2 by auto
qed

text \<open>
The following results generalise parts of \cite[Exercise 8.27]{DaveyPriestley2002} from continuous functions on complete partial orders to the present setting.
\<close>

lemma mu_commute_fixpoint_1:
  "isotone f \<Longrightarrow> has_least_fixpoint (f \<circ> g) \<Longrightarrow> f \<circ> g = g \<circ> f \<Longrightarrow> is_fixpoint f (\<mu> (f \<circ> g))"
  by (metis is_fixpoint_def mu_roll)

lemma mu_commute_fixpoint_2:
  "isotone g \<Longrightarrow> has_least_fixpoint (f \<circ> g) \<Longrightarrow> f \<circ> g = g \<circ> f \<Longrightarrow> is_fixpoint g (\<mu> (f \<circ> g))"
  by (simp add: mu_commute_fixpoint_1)

lemma mu_commute_least_fixpoint:
  "isotone f \<Longrightarrow> isotone g \<Longrightarrow> has_least_fixpoint f \<Longrightarrow> has_least_fixpoint g \<Longrightarrow> has_least_fixpoint (f \<circ> g) \<Longrightarrow> f \<circ> g = g \<circ> f \<Longrightarrow> \<mu> (f \<circ> g) = \<mu> f \<Longrightarrow> \<mu> g \<le> \<mu> f"
  by (metis is_least_fixpoint_def least_fixpoint mu_roll)

text \<open>
The converse of the preceding result is claimed for continuous $f$, $g$ on a complete partial order; it is unknown whether it holds without these additional assumptions.
\<close>

lemma nu_commute_fixpoint_1:
  "isotone f \<Longrightarrow> has_greatest_fixpoint (f \<circ> g) \<Longrightarrow> f \<circ> g = g \<circ> f \<Longrightarrow> is_fixpoint f (\<nu>(f \<circ> g))"
  by (metis is_fixpoint_def nu_roll)

lemma nu_commute_fixpoint_2:
  "isotone g \<Longrightarrow> has_greatest_fixpoint (f \<circ> g) \<Longrightarrow> f \<circ> g = g \<circ> f \<Longrightarrow> is_fixpoint g (\<nu>(f \<circ> g))"
  by (simp add: nu_commute_fixpoint_1)

lemma nu_commute_greatest_fixpoint:
  "isotone f \<Longrightarrow> isotone g \<Longrightarrow> has_greatest_fixpoint f \<Longrightarrow> has_greatest_fixpoint g \<Longrightarrow> has_greatest_fixpoint (f \<circ> g) \<Longrightarrow> f \<circ> g = g \<circ> f \<Longrightarrow> \<nu> (f \<circ> g) = \<nu> f \<Longrightarrow> \<nu> f \<le> \<nu> g"
  by (metis greatest_fixpoint is_greatest_fixpoint_def nu_roll)

text \<open>
Finally, we show a number of versions of the diagonal rule for functions with two arguments.
\<close>

lemma mu_diagonal_1:
  assumes "isotone (\<lambda>x . \<mu> (\<lambda>y . f x y))"
      and "\<forall>x . has_least_fixpoint (\<lambda>y . f x y)"
      and "has_least_prefixpoint (\<lambda>x . \<mu> (\<lambda>y . f x y))"
    shows "\<mu> (\<lambda>x . f x x) = \<mu> (\<lambda>x . \<mu> (\<lambda>y . f x y))"
proof -
  let ?g = "\<lambda>x . \<mu> (\<lambda>y . f x y)"
  have 1: "is_least_prefixpoint ?g (\<mu> ?g)"
    using assms(1,3) least_prefixpoint pmu_mu by fastforce
  have "f (\<mu> ?g) (\<mu> ?g) = \<mu> ?g"
    by (metis (no_types, lifting) assms is_least_fixpoint_def least_fixpoint_char least_prefixpoint_fixpoint)
  hence "is_least_fixpoint (\<lambda>x . f x x) (\<mu> ?g)"
    using 1 assms(2) is_least_fixpoint_def is_least_prefixpoint_def least_fixpoint by auto
  thus ?thesis
    using least_fixpoint_same by simp
qed

lemma mu_diagonal_2:
  "\<forall>x . isotone (\<lambda>y . f x y) \<and> isotone (\<lambda>y . f y x) \<and> has_least_prefixpoint (\<lambda>y . f x y) \<Longrightarrow> has_least_prefixpoint (\<lambda>x . \<mu> (\<lambda>y . f x y)) \<Longrightarrow> \<mu> (\<lambda>x . f x x) = \<mu> (\<lambda>x . \<mu> (\<lambda>y . f x y))"
  apply (rule mu_diagonal_1)
  using isotone_def lifted_less_eq_def mu_isotone apply simp
  using has_least_fixpoint_def least_prefixpoint_fixpoint apply blast
  by simp

lemma nu_diagonal_1:
  assumes "isotone (\<lambda>x . \<nu> (\<lambda>y . f x y))"
      and "\<forall>x . has_greatest_fixpoint (\<lambda>y . f x y)"
      and "has_greatest_postfixpoint (\<lambda>x . \<nu> (\<lambda>y . f x y))"
    shows "\<nu> (\<lambda>x . f x x) = \<nu> (\<lambda>x . \<nu> (\<lambda>y . f x y))"
proof -
  let ?g = "\<lambda>x . \<nu> (\<lambda>y . f x y)"
  have 1: "is_greatest_postfixpoint ?g (\<nu> ?g)"
    using assms(1,3) greatest_postfixpoint pnu_nu by fastforce
  have "f (\<nu> ?g) (\<nu> ?g) = \<nu> ?g"
    by (metis (no_types, lifting) assms is_greatest_fixpoint_def greatest_fixpoint_char greatest_postfixpoint_fixpoint)
  hence "is_greatest_fixpoint (\<lambda>x . f x x) (\<nu> ?g)"
    using 1 assms(2) is_greatest_fixpoint_def is_greatest_postfixpoint_def greatest_fixpoint by auto
  thus ?thesis
    using greatest_fixpoint_same by simp
qed

lemma nu_diagonal_2:
  "\<forall>x . isotone (\<lambda>y . f x y) \<and> isotone (\<lambda>y . f y x) \<and> has_greatest_postfixpoint (\<lambda>y . f x y) \<Longrightarrow> has_greatest_postfixpoint (\<lambda>x . \<nu> (\<lambda>y . f x y)) \<Longrightarrow> \<nu> (\<lambda>x . f x x) = \<nu> (\<lambda>x . \<nu> (\<lambda>y . f x y))"
  apply (rule nu_diagonal_1)
  using isotone_def lifted_less_eq_def nu_isotone apply simp
  using has_greatest_fixpoint_def greatest_postfixpoint_fixpoint apply blast
  by simp

end

end

