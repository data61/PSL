(* Title:      Pseudocomplemented Algebras
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Pseudocomplemented Algebras\<close>

text \<open>
This theory expands lattices with a pseudocomplement operation.
In particular, we consider the following algebraic structures:
\begin{itemize}
\item pseudocomplemented lattices (p-algebras)
\item pseudocomplemented distributive lattices (distributive p-algebras)
\item Stone algebras
\item Heyting semilattices
\item Heyting lattices
\item Heyting algebras
\item Heyting-Stone algebras
\item Brouwer algebras
\item Boolean algebras
\end{itemize}
Most of these structures and many results in this theory are discussed in \cite{BalbesDwinger1974,Birkhoff1967,Blyth2005,Curry1977,Graetzer1971,Maddux1996}.
\<close>

theory P_Algebras

imports Lattice_Basics

begin

subsection \<open>P-Algebras\<close>

text \<open>
In this section we add a pseudocomplement operation to lattices and to distributive lattices.
\<close>

subsubsection \<open>Pseudocomplemented Lattices\<close>

text \<open>
The pseudocomplement of an element \<open>y\<close> is the greatest element whose meet with \<open>y\<close> is the least element of the lattice.
\<close>

class p_algebra = bounded_lattice + uminus +
  assumes pseudo_complement: "x \<sqinter> y = bot \<longleftrightarrow> x \<le> -y"
begin

text \<open>
Regular elements and dense elements are frequently used in pseudocomplemented algebras.
\<close>

abbreviation "regular x \<equiv> x = --x"
abbreviation "dense x \<equiv> -x = bot"
abbreviation "complemented x \<equiv> \<exists>y . x \<sqinter> y = bot \<and> x \<squnion> y = top"
abbreviation "in_p_image x \<equiv> \<exists>y . x = -y"
abbreviation "selection s x \<equiv> s = --s \<sqinter> x"

abbreviation "dense_elements \<equiv> { x . dense x }"
abbreviation "regular_elements \<equiv> { x . in_p_image x }"

lemma p_bot [simp]:
  "-bot = top"
  using inf_top.left_neutral pseudo_complement top_unique by blast

lemma p_top [simp]:
  "-top = bot"
  by (metis eq_refl inf_top.comm_neutral pseudo_complement)

text \<open>
The pseudocomplement satisfies the following half of the requirements of a complement.
\<close>

lemma inf_p [simp]:
  "x \<sqinter> -x = bot"
  using inf.commute pseudo_complement by fastforce

lemma p_inf [simp]:
  "-x \<sqinter> x = bot"
  by (simp add: inf_commute)

lemma pp_inf_p:
  "--x \<sqinter> -x = bot"
  by simp

text \<open>
The double complement is a closure operation.
\<close>

lemma pp_increasing:
  "x \<le> --x"
  using inf_p pseudo_complement by blast

lemma ppp [simp]:
  "---x = -x"
  by (metis antisym inf.commute order_trans pseudo_complement pp_increasing)

lemma pp_idempotent:
  "----x = --x"
  by simp

lemma regular_in_p_image_iff:
  "regular x \<longleftrightarrow> in_p_image x"
  by auto

lemma pseudo_complement_pp:
  "x \<sqinter> y = bot \<longleftrightarrow> --x \<le> -y"
  by (metis inf_commute pseudo_complement ppp)

lemma p_antitone:
  "x \<le> y \<Longrightarrow> -y \<le> -x"
  by (metis inf_commute order_trans pseudo_complement pp_increasing)

lemma p_antitone_sup:
  "-(x \<squnion> y) \<le> -x"
  by (simp add: p_antitone)

lemma p_antitone_inf:
  "-x \<le> -(x \<sqinter> y)"
  by (simp add: p_antitone)

lemma p_antitone_iff:
  "x \<le> -y \<longleftrightarrow> y \<le> -x"
  using order_lesseq_imp p_antitone pp_increasing by blast

lemma pp_isotone:
  "x \<le> y \<Longrightarrow> --x \<le> --y"
  by (simp add: p_antitone)

lemma pp_isotone_sup:
  "--x \<le> --(x \<squnion> y)"
  by (simp add: p_antitone)

lemma pp_isotone_inf:
  "--(x \<sqinter> y) \<le> --x"
  by (simp add: p_antitone)

text \<open>
One of De Morgan's laws holds in pseudocomplemented lattices.
\<close>

lemma p_dist_sup [simp]:
  "-(x \<squnion> y) = -x \<sqinter> -y"
  apply (rule antisym)
  apply (simp add: p_antitone)
  using inf_le1 inf_le2 le_sup_iff p_antitone_iff by blast

lemma p_supdist_inf:
  "-x \<squnion> -y \<le> -(x \<sqinter> y)"
  by (simp add: p_antitone)

lemma pp_dist_pp_sup [simp]:
  "--(--x \<squnion> --y) = --(x \<squnion> y)"
  by simp

lemma p_sup_p [simp]:
  "-(x \<squnion> -x) = bot"
  by simp

lemma pp_sup_p [simp]:
  "--(x \<squnion> -x) = top"
  by simp

lemma dense_pp:
  "dense x \<longleftrightarrow> --x = top"
  by (metis p_bot p_top ppp)

lemma dense_sup_p:
  "dense (x \<squnion> -x)"
  by simp

lemma regular_char:
  "regular x \<longleftrightarrow> (\<exists>y . x = -y)"
  by auto

lemma pp_inf_bot_iff:
  "x \<sqinter> y = bot \<longleftrightarrow> --x \<sqinter> y = bot"
  by (simp add: pseudo_complement_pp)

text \<open>
Weak forms of the shunting property hold.
Most require a pseudocomplemented element on the right-hand side.
\<close>

lemma p_shunting_swap:
  "x \<sqinter> y \<le> -z \<longleftrightarrow> x \<sqinter> z \<le> -y"
  by (metis inf_assoc inf_commute pseudo_complement)

lemma pp_inf_below_iff:
  "x \<sqinter> y \<le> -z \<longleftrightarrow> --x \<sqinter> y \<le> -z"
  by (simp add: inf_commute p_shunting_swap)

lemma p_inf_pp [simp]:
  "-(x \<sqinter> --y) = -(x \<sqinter> y)"
  apply (rule antisym)
  apply (simp add: inf.coboundedI2 p_antitone pp_increasing)
  using inf_commute p_antitone_iff pp_inf_below_iff by auto

lemma p_inf_pp_pp [simp]:
  "-(--x \<sqinter> --y) = -(x \<sqinter> y)"
  by (simp add: inf_commute)

lemma regular_closed_inf:
  "regular x \<Longrightarrow> regular y \<Longrightarrow> regular (x \<sqinter> y)"
  by (metis p_dist_sup ppp)

lemma regular_closed_p:
  "regular (-x)"
  by simp

lemma regular_closed_pp:
  "regular (--x)"
  by simp

lemma regular_closed_bot:
  "regular bot"
  by simp

lemma regular_closed_top:
  "regular top"
  by simp

lemma pp_dist_inf [simp]:
  "--(x \<sqinter> y) = --x \<sqinter> --y"
  by (metis p_dist_sup p_inf_pp_pp ppp)

lemma inf_import_p [simp]:
  "x \<sqinter> -(x \<sqinter> y) = x \<sqinter> -y"
  apply (rule antisym)
  using p_shunting_swap apply fastforce
  using inf.sup_right_isotone p_antitone by auto

text \<open>
Pseudocomplements are unique.
\<close>

lemma p_unique:
  "(\<forall>x . x \<sqinter> y = bot \<longleftrightarrow> x \<le> z) \<Longrightarrow> z = -y"
  using inf.eq_iff pseudo_complement by auto

lemma maddux_3_5:
  "x \<squnion> x = x \<squnion> -(y \<squnion> -y)"
  by simp

lemma shunting_1_pp:
  "x \<le> --y \<longleftrightarrow> x \<sqinter> -y = bot"
  by (simp add: pseudo_complement)

lemma pp_pp_inf_bot_iff:
  "x \<sqinter> y = bot \<longleftrightarrow> --x \<sqinter> --y = bot"
  by (simp add: pseudo_complement_pp)

lemma inf_pp_semi_commute:
  "x \<sqinter> --y \<le> --(x \<sqinter> y)"
  using inf.eq_refl p_antitone_iff p_inf_pp by presburger

lemma inf_pp_commute:
  "--(--x \<sqinter> y) = --x \<sqinter> --y"
  by simp

lemma sup_pp_semi_commute:
  "x \<squnion> --y \<le> --(x \<squnion> y)"
  by (simp add: p_antitone_iff)

lemma regular_sup:
  "regular z \<Longrightarrow> (x \<le> z \<and> y \<le> z \<longleftrightarrow> --(x \<squnion> y) \<le> z)"
  apply (rule iffI)
  apply (metis le_supI pp_isotone)
  using dual_order.trans sup_ge2 pp_increasing pp_isotone_sup by blast

lemma dense_closed_inf:
  "dense x \<Longrightarrow> dense y \<Longrightarrow> dense (x \<sqinter> y)"
  by (simp add: dense_pp)

lemma dense_closed_sup:
  "dense x \<Longrightarrow> dense y \<Longrightarrow> dense (x \<squnion> y)"
  by simp

lemma dense_closed_pp:
  "dense x \<Longrightarrow> dense (--x)"
  by simp

lemma dense_closed_top:
  "dense top"
  by simp

lemma dense_up_closed:
  "dense x \<Longrightarrow> x \<le> y \<Longrightarrow> dense y"
  using dense_pp top_le pp_isotone by auto

lemma regular_dense_top:
  "regular x \<Longrightarrow> dense x \<Longrightarrow> x = top"
  using p_bot by blast

lemma selection_char:
  "selection s x \<longleftrightarrow> (\<exists>y . s = -y \<sqinter> x)"
  by (metis inf_import_p inf_commute regular_closed_p)

lemma selection_closed_inf:
  "selection s x \<Longrightarrow> selection t x \<Longrightarrow> selection (s \<sqinter> t) x"
  by (metis inf_assoc inf_commute inf_idem pp_dist_inf)

lemma selection_closed_pp:
  "regular x \<Longrightarrow> selection s x \<Longrightarrow> selection (--s) x"
  by (metis pp_dist_inf)

lemma selection_closed_bot:
  "selection bot x"
  by simp

lemma selection_closed_id:
  "selection x x"
  using inf.le_iff_sup pp_increasing by auto

text \<open>
Conjugates are usually studied for Boolean algebras, however, some of their properties generalise to pseudocomplemented algebras.
\<close>

lemma conjugate_unique_p:
  assumes "conjugate f g"
      and "conjugate f h"
    shows "uminus \<circ> g = uminus \<circ> h"
proof -
  have "\<forall>x y . x \<sqinter> g y = bot \<longleftrightarrow> x \<sqinter> h y = bot"
    using assms conjugate_def inf.commute by simp
  hence "\<forall>x y . x \<le> -(g y) \<longleftrightarrow> x \<le> -(h y)"
    using inf.commute pseudo_complement by simp
  hence "\<forall>y . -(g y) = -(h y)"
    using eq_iff by blast
  thus ?thesis
    by auto
qed

lemma conjugate_symmetric:
  "conjugate f g \<Longrightarrow> conjugate g f"
  by (simp add: conjugate_def inf_commute)

lemma additive_isotone:
  "additive f \<Longrightarrow> isotone f"
  by (metis additive_def isotone_def le_iff_sup)

lemma dual_additive_antitone:
  assumes "dual_additive f"
    shows "isotone (uminus \<circ> f)"
proof -
  have "\<forall>x y . f (x \<squnion> y) \<le> f x"
    using assms dual_additive_def by simp
  hence "\<forall>x y . x \<le> y \<longrightarrow> f y \<le> f x"
    by (metis sup_absorb2)
  hence "\<forall>x y . x \<le> y \<longrightarrow> -(f x) \<le> -(f y)"
    by (simp add: p_antitone)
  thus ?thesis
    by (simp add: isotone_def)
qed

lemma conjugate_dual_additive:
  assumes "conjugate f g"
    shows "dual_additive (uminus \<circ> f)"
proof -
  have 1: "\<forall>x y z . -z \<le> -(f (x \<squnion> y)) \<longleftrightarrow> -z \<le> -(f x) \<and> -z \<le> -(f y)"
  proof (intro allI)
    fix x y z
    have "(-z \<le> -(f (x \<squnion> y))) = (f (x \<squnion> y) \<sqinter> -z = bot)"
      by (simp add: p_antitone_iff pseudo_complement)
    also have "... = ((x \<squnion> y) \<sqinter> g(-z) = bot)"
      using assms conjugate_def by auto
    also have "... = (x \<squnion> y \<le> -(g(-z)))"
      by (simp add: pseudo_complement)
    also have "... = (x \<le> -(g(-z)) \<and> y \<le> -(g(-z)))"
      by (simp add: le_sup_iff)
    also have "... = (x \<sqinter> g(-z) = bot \<and> y \<sqinter> g(-z) = bot)"
      by (simp add: pseudo_complement)
    also have "... = (f x \<sqinter> -z = bot \<and> f y \<sqinter> -z = bot)"
      using assms conjugate_def by auto
    also have "... = (-z \<le> -(f x) \<and> -z \<le> -(f y))"
      by (simp add: p_antitone_iff pseudo_complement)
    finally show "-z \<le> -(f (x \<squnion> y)) \<longleftrightarrow> -z \<le> -(f x) \<and> -z \<le> -(f y)"
      by simp
  qed
  have "\<forall>x y . -(f (x \<squnion> y)) = -(f x) \<sqinter> -(f y)"
  proof (intro allI)
    fix x y
    have "-(f x) \<sqinter> -(f y) = --(-(f x) \<sqinter> -(f y))"
      by simp
    hence "-(f x) \<sqinter> -(f y) \<le> -(f (x \<squnion> y))"
      using 1 by (metis inf_le1 inf_le2)
    thus "-(f (x \<squnion> y)) = -(f x) \<sqinter> -(f y)"
      using 1 antisym by fastforce
  qed
  thus ?thesis
    using dual_additive_def by simp
qed

lemma conjugate_isotone_pp:
  "conjugate f g \<Longrightarrow> isotone (uminus \<circ> uminus \<circ> f)"
  by (simp add: comp_assoc conjugate_dual_additive dual_additive_antitone)

lemma conjugate_char_1_pp:
  "conjugate f g \<longleftrightarrow> (\<forall>x y . f(x \<sqinter> -(g y)) \<le> --f x \<sqinter> -y \<and> g(y \<sqinter> -(f x)) \<le> --g y \<sqinter> -x)"
proof
  assume 1: "conjugate f g"
  show "\<forall>x y . f(x \<sqinter> -(g y)) \<le> --f x \<sqinter> -y \<and> g(y \<sqinter> -(f x)) \<le> --g y \<sqinter> -x"
  proof (intro allI)
    fix x y
    have 2: "f(x \<sqinter> -(g y)) \<le> -y"
      using 1 by (simp add: conjugate_def pseudo_complement)
    have "f(x \<sqinter> -(g y)) \<le> --f(x \<sqinter> -(g y))"
      by (simp add: pp_increasing)
    also have "... \<le> --f x"
      using 1 conjugate_isotone_pp isotone_def by simp
    finally have 3: "f(x \<sqinter> -(g y)) \<le> --f x \<sqinter> -y"
      using 2 by simp
    have 4: "isotone (uminus \<circ> uminus \<circ> g)"
      using 1 conjugate_isotone_pp conjugate_symmetric by auto
    have 5: "g(y \<sqinter> -(f x)) \<le> -x"
      using 1 by (metis conjugate_def inf.cobounded2 inf_commute pseudo_complement)
    have "g(y \<sqinter> -(f x)) \<le> --g(y \<sqinter> -(f x))"
      by (simp add: pp_increasing)
    also have "... \<le> --g y"
      using 4 isotone_def by auto
    finally have "g(y \<sqinter> -(f x)) \<le> --g y \<sqinter> -x"
      using 5 by simp
    thus "f(x \<sqinter> -(g y)) \<le> --f x \<sqinter> -y \<and> g(y \<sqinter> -(f x)) \<le> --g y \<sqinter> -x"
      using 3 by simp
  qed
next
  assume 6: "\<forall>x y . f(x \<sqinter> -(g y)) \<le> --f x \<sqinter> -y \<and> g(y \<sqinter> -(f x)) \<le> --g y \<sqinter> -x"
  hence 7: "\<forall>x y . f x \<sqinter> y = bot \<longrightarrow> x \<sqinter> g y = bot"
    by (metis inf.le_iff_sup inf.le_sup_iff inf_commute pseudo_complement)
  have "\<forall>x y . x \<sqinter> g y = bot \<longrightarrow> f x \<sqinter> y = bot"
    using 6 by (metis inf.le_iff_sup inf.le_sup_iff inf_commute pseudo_complement)
  thus "conjugate f g"
    using 7 conjugate_def by auto
qed

lemma conjugate_char_1_isotone:
  "conjugate f g \<Longrightarrow> isotone f \<Longrightarrow> isotone g \<Longrightarrow> f(x \<sqinter> -(g y)) \<le> f x \<sqinter> -y \<and> g(y \<sqinter> -(f x)) \<le> g y \<sqinter> -x"
  by (simp add: conjugate_char_1_pp ord.isotone_def)

lemma dense_lattice_char_1:
  "(\<forall>x y . x \<sqinter> y = bot \<longrightarrow> x = bot \<or> y = bot) \<longleftrightarrow> (\<forall>x . x \<noteq> bot \<longrightarrow> dense x)"
  by (metis inf_top.left_neutral p_bot p_inf pp_inf_bot_iff)

lemma dense_lattice_char_2:
  "(\<forall>x y . x \<sqinter> y = bot \<longrightarrow> x = bot \<or> y = bot) \<longleftrightarrow> (\<forall>x . regular x \<longrightarrow> x = bot \<or> x = top)"
  by (metis dense_lattice_char_1 inf_top.left_neutral p_inf regular_closed_p regular_closed_top)

lemma restrict_below_Rep_eq:
  "x \<sqinter> --y \<le> z \<Longrightarrow> x \<sqinter> y = x \<sqinter> z \<sqinter> y"
  by (metis inf.absorb2 inf.commute inf.left_commute pp_increasing)

(*
lemma p_inf_sup_below: "-x \<sqinter> (x \<squnion> y) \<le> y" nitpick [expect=genuine] oops
lemma complement_p: "x \<sqinter> y = bot \<and> x \<squnion> y = top \<longrightarrow> -x = y" nitpick [expect=genuine] oops
lemma complemented_regular: "complemented x \<longrightarrow> regular x" nitpick [expect=genuine] oops
*)

end

text \<open>
The following class gives equational axioms for the pseudocomplement operation.
\<close>

class p_algebra_eq = bounded_lattice + uminus +
  assumes p_bot_eq: "-bot = top"
      and p_top_eq: "-top = bot"
      and inf_import_p_eq: "x \<sqinter> -(x \<sqinter> y) = x \<sqinter> -y"
begin

lemma inf_p_eq:
  "x \<sqinter> -x = bot"
  by (metis inf_bot_right inf_import_p_eq inf_top_right p_top_eq)

subclass p_algebra
  apply unfold_locales
  apply (rule iffI)
  apply (metis inf.orderI inf_import_p_eq inf_top.right_neutral p_bot_eq)
  by (metis (full_types) inf.left_commute inf.orderE inf_bot_right inf_commute inf_p_eq)

end

subsubsection \<open>Pseudocomplemented Distributive Lattices\<close>

text \<open>
We obtain further properties if we assume that the lattice operations are distributive.
\<close>

class pd_algebra = p_algebra + bounded_distrib_lattice
begin

lemma p_inf_sup_below:
  "-x \<sqinter> (x \<squnion> y) \<le> y"
  by (simp add: inf_sup_distrib1)

lemma pp_inf_sup_p [simp]:
  "--x \<sqinter> (x \<squnion> -x) = x"
  using inf.absorb2 inf_sup_distrib1 pp_increasing by auto

lemma complement_p:
  "x \<sqinter> y = bot \<Longrightarrow> x \<squnion> y = top \<Longrightarrow> -x = y"
  by (metis pseudo_complement inf.commute inf_top.left_neutral sup.absorb_iff1 sup.commute sup_bot.right_neutral sup_inf_distrib2 p_inf)

lemma complemented_regular:
  "complemented x \<Longrightarrow> regular x"
  using complement_p inf.commute sup.commute by fastforce

lemma regular_inf_dense:
  "\<exists>y z . regular y \<and> dense z \<and> x = y \<sqinter> z"
  by (metis pp_inf_sup_p dense_sup_p ppp)

lemma maddux_3_12 [simp]:
  "(x \<squnion> -y) \<sqinter> (x \<squnion> y) = x"
  by (metis p_inf sup_bot_right sup_inf_distrib1)

lemma maddux_3_13 [simp]:
  "(x \<squnion> y) \<sqinter> -x = y \<sqinter> -x"
  by (simp add: inf_sup_distrib2)

lemma maddux_3_20:
  "((v \<sqinter> w) \<squnion> (-v \<sqinter> x)) \<sqinter> -((v \<sqinter> y) \<squnion> (-v \<sqinter> z)) = (v \<sqinter> w \<sqinter> -y) \<squnion> (-v \<sqinter> x \<sqinter> -z)"
proof -
  have "v \<sqinter> w \<sqinter> -(v \<sqinter> y) \<sqinter> -(-v \<sqinter> z) = v \<sqinter> w \<sqinter> -(v \<sqinter> y)"
    by (meson inf.cobounded1 inf_absorb1 le_infI1 p_antitone_iff)
  also have "... = v \<sqinter> w \<sqinter> -y"
    using inf.sup_relative_same_increasing inf_import_p inf_le1 by blast
  finally have 1: "v \<sqinter> w \<sqinter> -(v \<sqinter> y) \<sqinter> -(-v \<sqinter> z) = v \<sqinter> w \<sqinter> -y"
    .
  have "-v \<sqinter> x \<sqinter> -(v \<sqinter> y) \<sqinter> -(-v \<sqinter> z) = -v \<sqinter> x \<sqinter> -(-v \<sqinter> z)"
    by (simp add: inf.absorb1 le_infI1 p_antitone_inf)
  also have "... = -v \<sqinter> x \<sqinter> -z"
    by (simp add: inf.assoc inf_left_commute)
  finally have 2: "-v \<sqinter> x \<sqinter> -(v \<sqinter> y) \<sqinter> -(-v \<sqinter> z) = -v \<sqinter> x \<sqinter> -z"
    .
  have "((v \<sqinter> w) \<squnion> (-v \<sqinter> x)) \<sqinter> -((v \<sqinter> y) \<squnion> (-v \<sqinter> z)) = (v \<sqinter> w \<sqinter> -(v \<sqinter> y) \<sqinter> -(-v \<sqinter> z)) \<squnion> (-v \<sqinter> x \<sqinter> -(v \<sqinter> y) \<sqinter> -(-v \<sqinter> z))"
    by (simp add: inf_assoc inf_sup_distrib2)
  also have "... = (v \<sqinter> w \<sqinter> -y) \<squnion> (-v \<sqinter> x \<sqinter> -z)"
    using 1 2 by simp
  finally show ?thesis
    .
qed

lemma order_char_1:
  "x \<le> y \<longleftrightarrow> x \<le> y \<squnion> -x"
  by (metis inf.sup_left_isotone inf_sup_absorb le_supI1 maddux_3_12 sup_commute)

lemma order_char_2:
  "x \<le> y \<longleftrightarrow> x \<squnion> -x \<le> y \<squnion> -x"
  using order_char_1 by auto

(*
lemma pp_dist_sup [simp]: "--(x \<squnion> y) = --x \<squnion> --y" nitpick [expect=genuine] oops
lemma regular_closed_sup: "regular x \<and> regular y \<longrightarrow> regular (x \<squnion> y)" nitpick [expect=genuine] oops
lemma regular_complemented_iff: "regular x \<longleftrightarrow> complemented x" nitpick [expect=genuine] oops
lemma selection_closed_sup: "selection s x \<and> selection t x \<longrightarrow> selection (s \<squnion> t) x" nitpick [expect=genuine] oops
lemma stone [simp]: "-x \<squnion> --x = top" nitpick [expect=genuine] oops
*)

end

subsection \<open>Stone Algebras\<close>

text \<open>
A Stone algebra is a distributive lattice with a pseudocomplement that satisfies the following equation.
We thus obtain the other half of the requirements of a complement at least for the regular elements.
\<close>

class stone_algebra = pd_algebra +
  assumes stone [simp]: "-x \<squnion> --x = top"
begin

text \<open>
As a consequence, we obtain both De Morgan's laws for all elements.
\<close>

lemma p_dist_inf [simp]:
  "-(x \<sqinter> y) = -x \<squnion> -y"
proof (rule p_unique[THEN sym], rule allI, rule iffI)
  fix w
  assume "w \<sqinter> (x \<sqinter> y) = bot"
  hence "w \<sqinter> --x \<sqinter> y = bot"
    using inf_commute inf_left_commute pseudo_complement by auto
  hence 1: "w \<sqinter> --x \<le> -y"
    by (simp add: pseudo_complement)
  have "w = (w \<sqinter> -x) \<squnion> (w \<sqinter> --x)"
    using distrib_imp2 sup_inf_distrib1 by auto
  thus "w \<le> -x \<squnion> -y"
    using 1 by (metis inf_le2 sup.mono)
next
  fix w
  assume "w \<le> -x \<squnion> -y"
  thus "w \<sqinter> (x \<sqinter> y) = bot"
    using order_trans p_supdist_inf pseudo_complement by blast
qed

lemma pp_dist_sup [simp]:
  "--(x \<squnion> y) = --x \<squnion> --y"
  by simp

lemma regular_closed_sup:
  "regular x \<Longrightarrow> regular y \<Longrightarrow> regular (x \<squnion> y)"
  by simp

text \<open>
The regular elements are precisely the ones having a complement.
\<close>

lemma regular_complemented_iff:
  "regular x \<longleftrightarrow> complemented x"
  by (metis inf_p stone complemented_regular)

lemma selection_closed_sup:
  "selection s x \<Longrightarrow> selection t x \<Longrightarrow> selection (s \<squnion> t) x"
  by (simp add: inf_sup_distrib2)

lemma huntington_3_pp [simp]:
  "-(-x \<squnion> -y) \<squnion> -(-x \<squnion> y) = --x"
  by (metis p_dist_inf p_inf sup.commute sup_bot_left sup_inf_distrib1)

lemma maddux_3_3 [simp]:
  "-(x \<squnion> y) \<squnion> -(x \<squnion> -y) = -x"
  by (simp add: sup_commute sup_inf_distrib1)

lemma maddux_3_11_pp:
  "(x \<sqinter> -y) \<squnion> (x \<sqinter> --y) = x"
  by (metis inf_sup_distrib1 inf_top_right stone)

lemma maddux_3_19_pp:
  "(-x \<sqinter> y) \<squnion> (--x \<sqinter> z) = (--x \<squnion> y) \<sqinter> (-x \<squnion> z)"
proof -
  have "(--x \<squnion> y) \<sqinter> (-x \<squnion> z) = (--x \<sqinter> z) \<squnion> (y \<sqinter> -x) \<squnion> (y \<sqinter> z)"
    by (simp add: inf.commute inf_sup_distrib1 sup.assoc)
  also have "... = (--x \<sqinter> z) \<squnion> (y \<sqinter> -x) \<squnion> (y \<sqinter> z \<sqinter> (-x \<squnion> --x))"
    by simp
  also have "... = (--x \<sqinter> z) \<squnion> ((y \<sqinter> -x) \<squnion> (y \<sqinter> -x \<sqinter> z)) \<squnion> (y \<sqinter> z \<sqinter> --x)"
    using inf_sup_distrib1 sup_assoc inf_commute inf_assoc by presburger
  also have "... = (--x \<sqinter> z) \<squnion> (y \<sqinter> -x) \<squnion> (y \<sqinter> z \<sqinter> --x)"
    by simp
  also have "... = ((--x \<sqinter> z) \<squnion> (--x \<sqinter> z \<sqinter> y)) \<squnion> (y \<sqinter> -x)"
    by (simp add: inf_assoc inf_commute sup.left_commute sup_commute)
  also have "... = (--x \<sqinter> z) \<squnion> (y \<sqinter> -x)"
    by simp
  finally show ?thesis
    by (simp add: inf_commute sup_commute)
qed

lemma compl_inter_eq_pp:
  "--x \<sqinter> y = --x \<sqinter> z \<Longrightarrow> -x \<sqinter> y = -x \<sqinter> z \<Longrightarrow> y = z"
  by (metis inf_commute inf_p inf_sup_distrib1 inf_top.right_neutral p_bot p_dist_inf)

lemma maddux_3_21_pp [simp]:
  "--x \<squnion> (-x \<sqinter> y) = --x \<squnion> y"
  by (simp add: sup.commute sup_inf_distrib1)

lemma shunting_2_pp:
  "x \<le> --y \<longleftrightarrow> -x \<squnion> --y = top"
  by (metis inf_top_left p_bot p_dist_inf pseudo_complement)

lemma shunting_p:
  "x \<sqinter> y \<le> -z \<longleftrightarrow> x \<le> -z \<squnion> -y"
  by (metis inf.assoc p_dist_inf p_shunting_swap pseudo_complement)

text \<open>
The following weak shunting property is interesting as it does not require the element \<open>z\<close> on the right-hand side to be regular.
\<close>

lemma shunting_var_p:
  "x \<sqinter> -y \<le> z \<longleftrightarrow> x \<le> z \<squnion> --y"
proof
  assume "x \<sqinter> -y \<le> z"
  hence "z \<squnion> --y = --y \<squnion> (z \<squnion> x \<sqinter> -y)"
    by (simp add: sup.absorb1 sup.commute)
  thus "x \<le> z \<squnion> --y"
    by (metis inf_commute maddux_3_21_pp sup.commute sup.left_commute sup_left_divisibility)
next
  assume "x \<le> z \<squnion> --y"
  thus "x \<sqinter> -y \<le> z"
    by (metis inf.mono maddux_3_12 sup_ge2)
qed

(* Whether conjugate_char_2_pp can be proved in pd_algebra or in p_algebra is unknown. *)
lemma conjugate_char_2_pp:
  "conjugate f g \<longleftrightarrow> f bot = bot \<and> g bot = bot \<and> (\<forall>x y . f x \<sqinter> y \<le> --(f(x \<sqinter> --(g y))) \<and> g y \<sqinter> x \<le> --(g(y \<sqinter> --(f x))))"
proof
  assume 1: "conjugate f g"
  hence 2: "dual_additive (uminus \<circ> g)"
    using conjugate_symmetric conjugate_dual_additive by auto
  show "f bot = bot \<and> g bot = bot \<and> (\<forall>x y . f x \<sqinter> y \<le> --(f(x \<sqinter> --(g y))) \<and> g y \<sqinter> x \<le> --(g(y \<sqinter> --(f x))))"
  proof (intro conjI)
    show "f bot = bot"
      using 1 by (metis conjugate_def inf_idem inf_bot_left)
  next
    show "g bot = bot"
      using 1 by (metis conjugate_def inf_idem inf_bot_right)
  next
    show "\<forall>x y . f x \<sqinter> y \<le> --(f(x \<sqinter> --(g y))) \<and> g y \<sqinter> x \<le> --(g(y \<sqinter> --(f x)))"
    proof (intro allI)
      fix x y
      have 3: "y \<le> -(f(x \<sqinter> -(g y)))"
        using 1 by (simp add: conjugate_def pseudo_complement inf_commute)
      have 4: "x \<le> -(g(y \<sqinter> -(f x)))"
        using 1 conjugate_def inf.commute pseudo_complement by fastforce
      have "y \<sqinter> -(f(x \<sqinter> --(g y))) = y \<sqinter> -(f(x \<sqinter> -(g y))) \<sqinter> -(f(x \<sqinter> --(g y)))"
        using 3 by (simp add: inf.le_iff_sup inf_commute)
      also have "... = y \<sqinter> -(f((x \<sqinter> -(g y)) \<squnion> (x \<sqinter> --(g y))))"
        using 1 conjugate_dual_additive dual_additive_def inf_assoc by auto
      also have "... = y \<sqinter> -(f x)"
        by (simp add: maddux_3_11_pp)
      also have "... \<le> -(f x)"
        by simp
      finally have 5: "f x \<sqinter> y \<le> --(f(x \<sqinter> --(g y)))"
        by (simp add: inf_commute p_shunting_swap)
      have "x \<sqinter> -(g(y \<sqinter> --(f x))) = x \<sqinter> -(g(y \<sqinter> -(f x))) \<sqinter> -(g(y \<sqinter> --(f x)))"
        using 4 by (simp add: inf.le_iff_sup inf_commute)
      also have "... = x \<sqinter> -(g((y \<sqinter> -(f x)) \<squnion> (y \<sqinter> --(f x))))"
        using 2 by (simp add: dual_additive_def inf_assoc)
      also have "... = x \<sqinter> -(g y)"
        by (simp add: maddux_3_11_pp)
      also have "... \<le> -(g y)"
        by simp
      finally have "g y \<sqinter> x \<le> --(g(y \<sqinter> --(f x)))"
        by (simp add: inf_commute p_shunting_swap)
      thus "f x \<sqinter> y \<le> --(f(x \<sqinter> --(g y))) \<and> g y \<sqinter> x \<le> --(g(y \<sqinter> --(f x)))"
        using 5 by simp
    qed
  qed
next
  assume "f bot = bot \<and> g bot = bot \<and> (\<forall>x y . f x \<sqinter> y \<le> --(f(x \<sqinter> --(g y))) \<and> g y \<sqinter> x \<le> --(g(y \<sqinter> --(f x))))"
  thus "conjugate f g"
    by (unfold conjugate_def, metis inf_commute le_bot pp_inf_bot_iff regular_closed_bot)
qed

lemma conjugate_char_2_pp_additive:
  assumes "conjugate f g"
      and "additive f"
      and "additive g"
    shows "f x \<sqinter> y \<le> f(x \<sqinter> --(g y)) \<and> g y \<sqinter> x \<le> g(y \<sqinter> --(f x))"
proof -
  have "f x \<sqinter> y = f ((x \<sqinter> --g y) \<squnion> (x \<sqinter> -g y)) \<sqinter> y"
    by (simp add: sup.commute sup_inf_distrib1)
  also have "... = (f (x \<sqinter> --g y) \<sqinter> y) \<squnion> (f (x \<sqinter> -g y) \<sqinter> y)"
    using assms(2) additive_def inf_sup_distrib2 by auto
  also have "... = f (x \<sqinter> --g y) \<sqinter> y"
    by (metis assms(1) conjugate_def inf_le2 pseudo_complement sup_bot.right_neutral)
  finally have 2: "f x \<sqinter> y \<le> f (x \<sqinter> --g y)"
    by simp
  have "g y \<sqinter> x = g ((y \<sqinter> --f x) \<squnion> (y \<sqinter> -f x)) \<sqinter> x"
    by (simp add: sup.commute sup_inf_distrib1)
  also have "... = (g (y \<sqinter> --f x) \<sqinter> x) \<squnion> (g (y \<sqinter> -f x) \<sqinter> x)"
    using assms(3) additive_def inf_sup_distrib2 by auto
  also have "... = g (y \<sqinter> --f x) \<sqinter> x"
    by (metis assms(1) conjugate_def inf.cobounded2 pseudo_complement sup_bot.right_neutral inf_commute)
  finally have "g y \<sqinter> x \<le> g (y \<sqinter> --f x)"
    by simp
  thus ?thesis
    using 2 by simp
qed

(*
lemma compl_le_swap2_iff: "-x \<le> y \<longleftrightarrow> -y \<le> x" nitpick [expect=genuine] oops
lemma huntington_3: "x = -(-x \<squnion> -y) \<squnion> -(-x \<squnion> y)" nitpick [expect=genuine] oops
lemma maddux_3_1: "x \<squnion> -x = y \<squnion> -y" nitpick [expect=genuine] oops
lemma maddux_3_4: "x \<squnion> (y \<squnion> -y) = z \<squnion> -z" nitpick [expect=genuine] oops
lemma maddux_3_11: "x = (x \<sqinter> y) \<squnion> (x \<sqinter> -y)" nitpick [expect=genuine] oops
lemma maddux_3_19: "(-x \<sqinter> y) \<squnion> (x \<sqinter> z) = (x \<squnion> y) \<sqinter> (-x \<squnion> z)" nitpick [expect=genuine] oops
lemma compl_inter_eq: "x \<sqinter> y = x \<sqinter> z \<and> -x \<sqinter> y = -x \<sqinter> z \<longrightarrow> y = z" nitpick [expect=genuine] oops
lemma maddux_3_21: "x \<squnion> y = x \<squnion> (-x \<sqinter> y)" nitpick [expect=genuine] oops
lemma shunting_1: "x \<le> y \<longleftrightarrow> x \<sqinter> -y = bot" nitpick [expect=genuine] oops
lemma shunting_2: "x \<le> y \<longleftrightarrow> -x \<squnion> y = top" nitpick [expect=genuine] oops
lemma conjugate_unique: "conjugate f g \<and> conjugate f h \<longrightarrow> g = h" nitpick [expect=genuine] oops
lemma conjugate_isotone_pp: "conjugate f g \<longrightarrow> isotone f" nitpick [expect=genuine] oops
lemma conjugate_char_1: "conjugate f g \<longleftrightarrow> (\<forall>x y . f(x \<sqinter> -(g y)) \<le> f x \<sqinter> -y \<and> g(y \<sqinter> -(f x)) \<le> g y \<sqinter> -x)" nitpick [expect=genuine] oops
lemma conjugate_char_2: "conjugate f g \<longleftrightarrow> f bot = bot \<and> g bot = bot \<and> (\<forall>x y . f x \<sqinter> y \<le> f(x \<sqinter> g y) \<and> g y \<sqinter> x \<le> g(y \<sqinter> f x))" nitpick [expect=genuine] oops
lemma shunting: "x \<sqinter> y \<le> z \<longleftrightarrow> x \<le> z \<squnion> -y" nitpick [expect=genuine] oops
lemma shunting_var: "x \<sqinter> -y \<le> z \<longleftrightarrow> x \<le> z \<squnion> y" nitpick [expect=genuine] oops
lemma sup_compl_top: "x \<squnion> -x = top" nitpick [expect=genuine] oops
lemma selection_closed_p: "selection s x \<longrightarrow> selection (-s) x" nitpick [expect=genuine] oops
lemma selection_closed_pp: "selection s x \<longrightarrow> selection (--s) x" nitpick [expect=genuine] oops
*)

end

text \<open>
Every bounded linear order can be expanded to a Stone algebra.
The pseudocomplement takes \<open>bot\<close> to the \<open>top\<close> and every other element to \<open>bot\<close>.
\<close>

class linorder_stone_algebra_expansion = linorder_lattice_expansion + uminus +
  assumes uminus_def [simp]: "-x = (if x = bot then top else bot)"
begin

subclass stone_algebra
  apply unfold_locales
  using bot_unique min_def top_le by auto

text \<open>
The regular elements are the least and greatest elements.
All elements except the least element are dense.
\<close>

lemma regular_bot_top:
  "regular x \<longleftrightarrow> x = bot \<or> x = top"
  by simp

lemma not_bot_dense:
  "x \<noteq> bot \<Longrightarrow> --x = top"
  by simp

end

subsection \<open>Heyting Algebras\<close>

text \<open>
In this section we add a relative pseudocomplement operation to semilattices and to lattices.
\<close>

subsubsection \<open>Heyting Semilattices\<close>

text \<open>
The pseudocomplement of an element \<open>y\<close> relative to an element \<open>z\<close> is the least element whose meet with \<open>y\<close> is below \<open>z\<close>.
This can be stated as a Galois connection.
Specialising \<open>z = bot\<close> gives (non-relative) pseudocomplements.
Many properties can already be shown if the underlying structure is just a semilattice.
\<close>

class implies =
  fixes implies :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<leadsto>" 65)

class heyting_semilattice = semilattice_inf + implies +
  assumes implies_galois: "x \<sqinter> y \<le> z \<longleftrightarrow> x \<le> y \<leadsto> z"
begin

lemma implies_below_eq [simp]:
  "y \<sqinter> (x \<leadsto> y) = y"
  using implies_galois inf.absorb_iff1 inf.cobounded1 by blast

lemma implies_increasing:
  "x \<le> y \<leadsto> x"
  by (simp add: inf.orderI)

lemma implies_galois_swap:
  "x \<le> y \<leadsto> z \<longleftrightarrow> y \<le> x \<leadsto> z"
  by (metis implies_galois inf_commute)

lemma implies_galois_var:
  "x \<sqinter> y \<le> z \<longleftrightarrow> y \<le> x \<leadsto> z"
  by (simp add: implies_galois_swap implies_galois)

lemma implies_galois_increasing:
  "x \<le> y \<leadsto> (x \<sqinter> y)"
  using implies_galois by blast

lemma implies_galois_decreasing:
  "(y \<leadsto> x) \<sqinter> y \<le> x"
  using implies_galois by blast

lemma implies_mp_below:
  "x \<sqinter> (x \<leadsto> y) \<le> y"
  using implies_galois_decreasing inf_commute by auto

lemma implies_isotone:
  "x \<le> y \<Longrightarrow> z \<leadsto> x \<le> z \<leadsto> y"
  using implies_galois order_trans by blast

lemma implies_antitone:
  "x \<le> y \<Longrightarrow> y \<leadsto> z \<le> x \<leadsto> z"
  by (meson implies_galois_swap order_lesseq_imp)

lemma implies_isotone_inf:
  "x \<leadsto> (y \<sqinter> z) \<le> x \<leadsto> y"
  by (simp add: implies_isotone)

lemma implies_antitone_inf:
  "x \<leadsto> z \<le> (x \<sqinter> y) \<leadsto> z"
  by (simp add: implies_antitone)

lemma implies_curry:
  "x \<leadsto> (y \<leadsto> z) = (x \<sqinter> y) \<leadsto> z"
  by (metis implies_galois_decreasing implies_galois inf_assoc antisym)

lemma implies_curry_flip:
  "x \<leadsto> (y \<leadsto> z) = y \<leadsto> (x \<leadsto> z)"
  by (simp add: implies_curry inf_commute)

lemma triple_implies [simp]:
  "((x \<leadsto> y) \<leadsto> y) \<leadsto> y = x \<leadsto> y"
  using implies_antitone implies_galois_swap eq_iff by auto

lemma implies_mp_eq [simp]:
  "x \<sqinter> (x \<leadsto> y) = x \<sqinter> y"
  by (metis implies_below_eq implies_mp_below inf_left_commute inf.absorb2)

lemma implies_dist_implies:
  "x \<leadsto> (y \<leadsto> z) \<le> (x \<leadsto> y) \<leadsto> (x \<leadsto> z)"
  using implies_curry implies_curry_flip by auto

lemma implies_import_inf [simp]:
  "x \<sqinter> ((x \<sqinter> y) \<leadsto> (x \<leadsto> z)) = x \<sqinter> (y \<leadsto> z)"
  by (metis implies_curry implies_mp_eq inf_commute)

lemma implies_dist_inf:
  "x \<leadsto> (y \<sqinter> z) = (x \<leadsto> y) \<sqinter> (x \<leadsto> z)"
proof -
  have "(x \<leadsto> y) \<sqinter> (x \<leadsto> z) \<sqinter> x \<le> y \<sqinter> z"
    by (simp add: implies_galois)
  hence "(x \<leadsto> y) \<sqinter> (x \<leadsto> z) \<le> x \<leadsto> (y \<sqinter> z)"
    using implies_galois by blast
  thus ?thesis
    by (simp add: implies_isotone eq_iff)
qed

lemma implies_itself_top:
  "y \<le> x \<leadsto> x"
  by (simp add: implies_galois_swap implies_increasing)

lemma inf_implies_top:
  "z \<le> (x \<sqinter> y) \<leadsto> x"
  using implies_galois_var le_infI1 by blast

lemma inf_inf_implies [simp]:
  "z \<sqinter> ((x \<sqinter> y) \<leadsto> x) = z"
  by (simp add: inf_implies_top inf_absorb1)

lemma le_implies_top:
  "x \<le> y \<Longrightarrow> z \<le> x \<leadsto> y"
  using implies_antitone implies_itself_top order.trans by blast

lemma le_iff_le_implies:
  "x \<le> y \<longleftrightarrow> x \<le> x \<leadsto> y"
  using implies_galois inf_idem by force

lemma implies_inf_isotone:
  "x \<leadsto> y \<le> (x \<sqinter> z) \<leadsto> (y \<sqinter> z)"
  by (metis implies_curry implies_galois_increasing implies_isotone)

lemma implies_transitive:
  "(x \<leadsto> y) \<sqinter> (y \<leadsto> z) \<le> x \<leadsto> z"
  using implies_dist_implies implies_galois_var implies_increasing order_lesseq_imp by blast

lemma implies_inf_absorb [simp]:
  "x \<leadsto> (x \<sqinter> y) = x \<leadsto> y"
  using implies_dist_inf implies_itself_top inf.absorb_iff2 by auto

lemma implies_implies_absorb [simp]:
  "x \<leadsto> (x \<leadsto> y) = x \<leadsto> y"
  by (simp add: implies_curry)

lemma implies_inf_identity:
  "(x \<leadsto> y) \<sqinter> y = y"
  by (simp add: inf_commute)

lemma implies_itself_same:
  "x \<leadsto> x = y \<leadsto> y"
  by (simp add: le_implies_top eq_iff)

end

text \<open>
The following class gives equational axioms for the relative pseudocomplement operation (inequalities can be written as equations).
\<close>

class heyting_semilattice_eq = semilattice_inf + implies +
  assumes implies_mp_below: "x \<sqinter> (x \<leadsto> y) \<le> y"
      and implies_galois_increasing: "x \<le> y \<leadsto> (x \<sqinter> y)"
      and implies_isotone_inf: "x \<leadsto> (y \<sqinter> z) \<le> x \<leadsto> y"
begin

subclass heyting_semilattice
  apply unfold_locales
  apply (rule iffI)
  apply (metis implies_galois_increasing implies_isotone_inf inf.absorb2 order_lesseq_imp)
  by (metis implies_mp_below inf_commute order_trans inf_mono order_refl)

end

text \<open>
The following class allows us to explicitly give the pseudocomplement of an element relative to itself.
\<close>

class bounded_heyting_semilattice = bounded_semilattice_inf_top + heyting_semilattice
begin

lemma implies_itself [simp]:
  "x \<leadsto> x = top"
  using implies_galois inf_le2 top_le by blast

lemma implies_order:
  "x \<le> y \<longleftrightarrow> x \<leadsto> y = top"
  by (metis implies_galois inf_top.left_neutral top_unique)

lemma inf_implies [simp]:
  "(x \<sqinter> y) \<leadsto> x = top"
  using implies_order inf_le1 by blast

lemma top_implies [simp]:
  "top \<leadsto> x = x"
  by (metis implies_mp_eq inf_top.left_neutral)

end

subsubsection \<open>Heyting Lattices\<close>

text \<open>
We obtain further properties if the underlying structure is a lattice.
In particular, the lattice operations are automatically distributive in this case.
\<close>

class heyting_lattice = lattice + heyting_semilattice
begin

lemma sup_distrib_inf_le:
  "(x \<squnion> y) \<sqinter> (x \<squnion> z) \<le> x \<squnion> (y \<sqinter> z)"
proof -
  have "x \<squnion> z \<le> y \<leadsto> (x \<squnion> (y \<sqinter> z))"
    using implies_galois_var implies_increasing sup.bounded_iff sup.cobounded2 by blast
  hence "x \<squnion> y \<le> (x \<squnion> z) \<leadsto> (x \<squnion> (y \<sqinter> z))"
    using implies_galois_swap implies_increasing le_sup_iff by blast
  thus ?thesis
    by (simp add: implies_galois)
qed

subclass distrib_lattice
  apply unfold_locales
  using distrib_sup_le eq_iff sup_distrib_inf_le by auto

lemma implies_isotone_sup:
  "x \<leadsto> y \<le> x \<leadsto> (y \<squnion> z)"
  by (simp add: implies_isotone)

lemma implies_antitone_sup:
  "(x \<squnion> y) \<leadsto> z \<le> x \<leadsto> z"
  by (simp add: implies_antitone)

lemma implies_sup:
  "x \<leadsto> z \<le> (y \<leadsto> z) \<leadsto> ((x \<squnion> y) \<leadsto> z)"
proof -
  have "(x \<leadsto> z) \<sqinter> (y \<leadsto> z) \<sqinter> y \<le> z"
    by (simp add: implies_galois)
  hence "(x \<leadsto> z) \<sqinter> (y \<leadsto> z) \<sqinter> (x \<squnion> y) \<le> z"
    using implies_galois_swap implies_galois_var by fastforce
  thus ?thesis
    by (simp add: implies_galois)
qed

lemma implies_dist_sup:
  "(x \<squnion> y) \<leadsto> z = (x \<leadsto> z) \<sqinter> (y \<leadsto> z)"
  apply (rule antisym)
  apply (simp add: implies_antitone)
  by (simp add: implies_sup implies_galois)

lemma implies_antitone_isotone:
  "(x \<squnion> y) \<leadsto> (x \<sqinter> y) \<le> x \<leadsto> y"
  by (simp add: implies_antitone_sup implies_dist_inf le_infI2)

lemma implies_antisymmetry:
  "(x \<leadsto> y) \<sqinter> (y \<leadsto> x) = (x \<squnion> y) \<leadsto> (x \<sqinter> y)"
  by (metis implies_dist_sup implies_inf_absorb inf.commute)

lemma sup_inf_implies [simp]:
  "(x \<squnion> y) \<sqinter> (x \<leadsto> y) = y"
  by (simp add: inf_sup_distrib2 sup.absorb2)

lemma implies_subdist_sup:
  "(x \<leadsto> y) \<squnion> (x \<leadsto> z) \<le> x \<leadsto> (y \<squnion> z)"
  by (simp add: implies_isotone)

lemma implies_subdist_inf:
  "(x \<leadsto> z) \<squnion> (y \<leadsto> z) \<le> (x \<sqinter> y) \<leadsto> z"
  by (simp add: implies_antitone)

lemma implies_sup_absorb:
  "(x \<leadsto> y) \<squnion> z \<le> (x \<squnion> z) \<leadsto> (y \<squnion> z)"
  by (metis implies_dist_sup implies_isotone_sup implies_increasing inf_inf_implies le_sup_iff sup_inf_implies)

lemma sup_below_implies_implies:
  "x \<squnion> y \<le> (x \<leadsto> y) \<leadsto> y"
  by (simp add: implies_dist_sup implies_galois_swap implies_increasing)

end

class bounded_heyting_lattice = bounded_lattice + heyting_lattice
begin

subclass bounded_heyting_semilattice ..

lemma implies_bot [simp]:
  "bot \<leadsto> x = top"
  using implies_galois top_unique by fastforce

end

subsubsection \<open>Heyting Algebras\<close>

text \<open>
The pseudocomplement operation can be defined in Heyting algebras, but it is typically not part of their signature.
We add the definition as an axiom so that we can use the class hierarchy, for example, to inherit results from the class \<open>pd_algebra\<close>.
\<close>

class heyting_algebra = bounded_heyting_lattice + uminus +
  assumes uminus_eq: "-x = x \<leadsto> bot"
begin

subclass pd_algebra
  apply unfold_locales
  using bot_unique implies_galois uminus_eq by auto

lemma boolean_implies_below:
  "-x \<squnion> y \<le> x \<leadsto> y"
  by (simp add: implies_increasing implies_isotone uminus_eq)

lemma negation_implies:
  "-(x \<leadsto> y) = --x \<sqinter> -y"
proof (rule antisym)
  show "-(x \<leadsto> y) \<le> --x \<sqinter> -y"
    using boolean_implies_below p_antitone by auto
next
  have "x \<sqinter> -y \<sqinter> (x \<leadsto> y) = bot"
    by (metis implies_mp_eq inf_p inf_bot_left inf_commute inf_left_commute)
  hence "--x \<sqinter> -y \<sqinter> (x \<leadsto> y) = bot"
    using pp_inf_bot_iff inf_assoc by auto
  thus "--x \<sqinter> -y \<le> -(x \<leadsto> y)"
    by (simp add: pseudo_complement)
qed

lemma double_negation_dist_implies:
  "--(x \<leadsto> y) = --x \<leadsto> --y"
  apply (rule antisym)
  apply (metis pp_inf_below_iff implies_galois_decreasing implies_galois negation_implies ppp)
  by (simp add: p_antitone_iff negation_implies)

(*
lemma stone: "-x \<squnion> --x = top" nitpick [expect=genuine] oops
*)

end

text \<open>
The following class gives equational axioms for Heyting algebras.
\<close>

class heyting_algebra_eq = bounded_lattice + implies + uminus +
  assumes implies_mp_eq: "x \<sqinter> (x \<leadsto> y) = x \<sqinter> y"
      and implies_import_inf: "x \<sqinter> ((x \<sqinter> y) \<leadsto> (x \<leadsto> z)) = x \<sqinter> (y \<leadsto> z)"
      and inf_inf_implies: "z \<sqinter> ((x \<sqinter> y) \<leadsto> x) = z"
      and uminus_eq_eq: "-x = x \<leadsto> bot"
begin

subclass heyting_algebra
  apply unfold_locales
  apply (rule iffI)
  apply (metis implies_import_inf inf.sup_left_divisibility inf_inf_implies le_iff_inf)
  apply (metis implies_mp_eq inf.commute inf.le_sup_iff inf.sup_right_isotone)
  by (simp add: uminus_eq_eq)

end

text \<open>
A relative pseudocomplement is not enough to obtain the Stone equation, so we add it in the following class.
\<close>

class heyting_stone_algebra = heyting_algebra +
  assumes heyting_stone: "-x \<squnion> --x = top"
begin

subclass stone_algebra
  by unfold_locales (simp add: heyting_stone)

(*
lemma pre_linear: "(x \<leadsto> y) \<squnion> (y \<leadsto> x) = top" nitpick [expect=genuine] oops
*)

end

subsubsection \<open>Brouwer Algebras\<close>

text \<open>
Brouwer algebras are dual to Heyting algebras.
The dual pseudocomplement of an element \<open>y\<close> relative to an element \<open>x\<close> is the least element whose join with \<open>y\<close> is above \<open>x\<close>.
We can now use the binary operation provided by Boolean algebras in Isabelle/HOL because it is compatible with dual relative pseudocomplements (not relative pseudocomplements).
\<close>

class brouwer_algebra = bounded_lattice + minus + uminus +
  assumes minus_galois: "x \<le> y \<squnion> z \<longleftrightarrow> x - y \<le> z"
      and uminus_eq_minus: "-x = top - x"
begin

sublocale brouwer: heyting_algebra where inf = sup and less_eq = greater_eq and less = greater and sup = inf and bot = top and top = bot and implies = "\<lambda>x y . y - x"
  apply unfold_locales
  apply simp
  apply simp
  apply simp
  apply simp
  apply (metis minus_galois sup_commute)
  by (simp add: uminus_eq_minus)

lemma curry_minus:
  "x - (y \<squnion> z) = (x - y) - z"
  by (simp add: brouwer.implies_curry sup_commute)

lemma minus_subdist_sup:
  "(x - z) \<squnion> (y - z) \<le> (x \<squnion> y) - z"
  by (simp add: brouwer.implies_dist_inf)

lemma inf_sup_minus:
  "(x \<sqinter> y) \<squnion> (x - y) = x"
  by (simp add: inf.absorb1 brouwer.inf_sup_distrib2)

end

subsection \<open>Boolean Algebras\<close>

text \<open>
This section integrates Boolean algebras in the above hierarchy.
In particular, we strengthen several results shown above.
\<close>

context boolean_algebra
begin

text \<open>
Every Boolean algebra is a Stone algebra, a Heyting algebra and a Brouwer algebra.
\<close>

subclass stone_algebra
  apply unfold_locales
  apply (rule iffI)
  apply (metis compl_sup_top inf.orderI inf_bot_right inf_sup_distrib1 inf_top_right sup_inf_absorb)
  using inf.commute inf.sup_right_divisibility apply fastforce
  by simp

sublocale heyting: heyting_algebra where implies = "\<lambda>x y . -x \<squnion> y"
  apply unfold_locales
  apply (rule iffI)
  using shunting_var_p sup_commute apply fastforce
  using shunting_var_p sup_commute apply force
  by simp

subclass brouwer_algebra
  apply unfold_locales
  apply (simp add: diff_eq shunting_var_p sup.commute)
  by (simp add: diff_eq)

lemma huntington_3 [simp]:
  "-(-x \<squnion> -y) \<squnion> -(-x \<squnion> y) = x"
  using huntington_3_pp by auto

lemma maddux_3_1:
  "x \<squnion> -x = y \<squnion> -y"
  by simp

lemma maddux_3_4:
  "x \<squnion> (y \<squnion> -y) = z \<squnion> -z"
  by simp

lemma maddux_3_11 [simp]:
  "(x \<sqinter> y) \<squnion> (x \<sqinter> -y) = x"
  using brouwer.maddux_3_12 sup.commute by auto

lemma maddux_3_19:
  "(-x \<sqinter> y) \<squnion> (x \<sqinter> z) = (x \<squnion> y) \<sqinter> (-x \<squnion> z)"
  using maddux_3_19_pp by auto

lemma compl_inter_eq:
  "x \<sqinter> y = x \<sqinter> z \<Longrightarrow> -x \<sqinter> y = -x \<sqinter> z \<Longrightarrow> y = z"
  by (metis inf_commute maddux_3_11)

lemma maddux_3_21 [simp]:
  "x \<squnion> (-x \<sqinter> y) = x \<squnion> y"
  by (simp add: sup_inf_distrib1)

lemma shunting_1:
  "x \<le> y \<longleftrightarrow> x \<sqinter> -y = bot"
  by (simp add: pseudo_complement)

lemma uminus_involutive:
  "uminus \<circ> uminus = id"
  by auto

lemma uminus_injective:
  "uminus \<circ> f = uminus \<circ> g \<Longrightarrow> f = g"
  by (metis comp_assoc id_o minus_comp_minus)

lemma conjugate_unique:
  "conjugate f g \<Longrightarrow> conjugate f h \<Longrightarrow> g = h"
  using conjugate_unique_p uminus_injective by blast

lemma dual_additive_additive:
  "dual_additive (uminus \<circ> f) \<Longrightarrow> additive f"
  by (metis additive_def compl_eq_compl_iff dual_additive_def p_dist_sup o_def)

lemma conjugate_additive:
  "conjugate f g \<Longrightarrow> additive f"
  by (simp add: conjugate_dual_additive dual_additive_additive)

lemma conjugate_isotone:
  "conjugate f g \<Longrightarrow> isotone f"
  by (simp add: conjugate_additive additive_isotone)

lemma conjugate_char_1:
  "conjugate f g \<longleftrightarrow> (\<forall>x y . f(x \<sqinter> -(g y)) \<le> f x \<sqinter> -y \<and> g(y \<sqinter> -(f x)) \<le> g y \<sqinter> -x)"
  by (simp add: conjugate_char_1_pp)

lemma conjugate_char_2:
  "conjugate f g \<longleftrightarrow> f bot = bot \<and> g bot = bot \<and> (\<forall>x y . f x \<sqinter> y \<le> f(x \<sqinter> g y) \<and> g y \<sqinter> x \<le> g(y \<sqinter> f x))"
  by (simp add: conjugate_char_2_pp)

lemma shunting:
  "x \<sqinter> y \<le> z \<longleftrightarrow> x \<le> z \<squnion> -y"
  by (simp add: heyting.implies_galois sup.commute)

lemma shunting_var:
  "x \<sqinter> -y \<le> z \<longleftrightarrow> x \<le> z \<squnion> y"
  by (simp add: shunting)

end

class non_trivial_stone_algebra = non_trivial_bounded_order + stone_algebra

class non_trivial_boolean_algebra = non_trivial_stone_algebra + boolean_algebra

end

