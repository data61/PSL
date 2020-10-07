(* Title:      Formal Power Series Model of Kleene Algebra
   Author:     Alasdair Armstrong, Georg Struth, Tjark Weber
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

section \<open>Formal Power Series\<close>

theory Formal_Power_Series
imports Finite_Suprema Kleene_Algebra
begin

subsection \<open>The Type of Formal Power Series\<close>

text \<open>Formal powerseries are functions from a free monoid into a
dioid. They have applications in formal language theory, e.g.,
weighted automata. As usual, we represent elements of a free monoid
by lists.

This theory generalises Amine Chaieb's development of formal power
series as functions from natural numbers, which may be found in {\em
HOL/Library/Formal\_Power\_Series.thy}.\<close>

typedef ('a, 'b) fps = "{f::'a list \<Rightarrow> 'b. True}"
  morphisms fps_nth Abs_fps
  by simp

text \<open>It is often convenient to reason about functions, and transfer
results to formal power series.\<close>

setup_lifting type_definition_fps

declare fps_nth_inverse [simp]

notation fps_nth (infixl "$" 75)

lemma expand_fps_eq: "p = q \<longleftrightarrow> (\<forall>n. p $ n = q $ n)"
by (simp add: fps_nth_inject [symmetric] fun_eq_iff)

lemma fps_ext: "(\<And>n. p $ n = q $ n) \<Longrightarrow> p = q"
by (simp add: expand_fps_eq)

lemma fps_nth_Abs_fps [simp]: "Abs_fps f $ n = f n"
by (simp add: Abs_fps_inverse)


subsection \<open>Definition of the Basic Elements~0 and~1 and the Basic
Operations of Addition and Multiplication\<close>

text \<open>The zero formal power series maps all elements of the monoid
(all lists) to zero.\<close>

instantiation fps :: (type,zero) zero
begin
  definition zero_fps where
    "0 = Abs_fps (\<lambda>n. 0)"
  instance ..
end

lemma fps_zero_nth [simp]: "0 $ n = 0"
unfolding zero_fps_def by simp

text \<open>The unit formal power series maps the monoidal unit (the empty
list) to one and all other elements to zero.\<close>

instantiation fps :: (type,"{one,zero}") one
begin
  definition one_fps where
    "1 = Abs_fps (\<lambda>n. if n = [] then 1 else 0)"
  instance ..
end

lemma fps_one_nth_Nil [simp]: "1 $ [] = 1"
unfolding one_fps_def by simp

lemma fps_one_nth_Cons [simp]: "1 $ (x # xs) = 0"
unfolding one_fps_def by simp

text \<open>Addition of formal power series is the usual pointwise
addition of functions.\<close>

instantiation fps :: (type,plus) plus
begin
  definition plus_fps where
    "f + g = Abs_fps (\<lambda>n. f $ n + g $ n)"
  instance ..
end

lemma fps_add_nth [simp]: "(f + g) $ n = f $ n + g $ n"
unfolding plus_fps_def by simp

text \<open>This directly shows that formal power series form a
semilattice with zero.\<close>

lemma fps_add_assoc: "((f::('a,'b::semigroup_add) fps) + g) + h = f + (g + h)"
unfolding plus_fps_def by (simp add: add.assoc)

lemma fps_add_comm [simp]: "(f::('a,'b::ab_semigroup_add) fps) + g = g + f"
unfolding plus_fps_def by (simp add: add.commute)

lemma fps_add_idem [simp]: "(f::('a,'b::join_semilattice) fps) + f = f"
unfolding plus_fps_def by simp

lemma fps_zerol [simp]: "(f::('a,'b::monoid_add) fps) + 0 = f"
unfolding plus_fps_def by simp

lemma fps_zeror [simp]: "0 + (f::('a,'b::monoid_add) fps) = f"
unfolding plus_fps_def by simp

text \<open>The product of formal power series is convolution. The product
of two formal powerseries at a list is obtained by splitting the list
into all possible prefix/suffix pairs, taking the product of the first
series applied to the first coordinate and the second series applied
to the second coordinate of each pair, and then adding the results.\<close>

instantiation fps :: (type,"{comm_monoid_add,times}") times
begin
  definition times_fps where
    "f * g = Abs_fps (\<lambda>n. \<Sum>{f $ y * g $ z |y z. n = y @ z})"
  instance ..
end

text \<open>We call the set of all prefix/suffix splittings of a
list~@{term xs} the \emph{splitset} of~@{term xs}.\<close>

definition splitset where
  "splitset xs \<equiv> {(p, q). xs = p @ q}"

text \<open>Altenatively, splitsets can be defined recursively, which
yields convenient simplification rules in Isabelle.\<close>

fun splitset_fun where
  "splitset_fun []       = {([], [])}"
| "splitset_fun (x # xs) = insert ([], x # xs) (apfst (Cons x) ` splitset_fun xs)"

lemma splitset_consl:
  "splitset (x # xs) = insert ([], x # xs) (apfst (Cons x) ` splitset xs)"
by (auto simp add: image_def splitset_def) (metis append_eq_Cons_conv)+

lemma splitset_eq_splitset_fun: "splitset xs = splitset_fun xs"
apply (induct xs)
 apply (simp add: splitset_def)
apply (simp add: splitset_consl)
done

text \<open>The definition of multiplication is now more precise.\<close>

lemma fps_mult_var:
  "(f * g) $ n = \<Sum>{f $ (fst p) * g $ (snd p) | p. p \<in> splitset n}"
by (simp add: times_fps_def splitset_def)

lemma fps_mult_image:
  "(f * g) $ n = \<Sum>((\<lambda>p. f $ (fst p) * g $ (snd p)) ` splitset n)"
by (simp only: Collect_mem_eq fps_mult_var fun_im)

text \<open>Next we show that splitsets are finite and non-empty.\<close>

lemma splitset_fun_finite [simp]: "finite (splitset_fun xs)"
  by (induct xs, simp_all)

lemma splitset_finite [simp]: "finite (splitset xs)"
  by (simp add: splitset_eq_splitset_fun)

lemma split_append_finite [simp]: "finite {(p, q). xs = p @ q}"
  by (fold splitset_def, fact splitset_finite)

lemma splitset_fun_nonempty [simp]: "splitset_fun xs \<noteq> {}"
  by (cases xs, simp_all)

lemma splitset_nonempty [simp]: "splitset xs \<noteq> {}"
  by (simp add: splitset_eq_splitset_fun)

text \<open>We now proceed with proving algebraic properties of formal
power series.\<close>

lemma fps_annil [simp]:
  "0 * (f::('a::type,'b::{comm_monoid_add,mult_zero}) fps) = 0"
by (rule fps_ext) (simp add: times_fps_def sum.neutral)

lemma fps_annir [simp]:
  "(f::('a::type,'b::{comm_monoid_add,mult_zero}) fps) * 0 = 0"
by (simp add: fps_ext times_fps_def sum.neutral)

lemma fps_distl:
  "(f::('a::type,'b::{join_semilattice_zero,semiring}) fps) * (g + h) = (f * g) + (f * h)"
by (simp add: fps_ext fps_mult_image distrib_left sum_fun_sum)

lemma fps_distr:
  "((f::('a::type,'b::{join_semilattice_zero,semiring}) fps) + g) * h = (f * h) + (g * h)"
by (simp add: fps_ext fps_mult_image distrib_right sum_fun_sum)

text \<open>The multiplicative unit laws are surprisingly tedious. For the
proof of the left unit law we use the recursive definition, which we
could as well have based on splitlists instead of splitsets.

However, a right unit law cannot simply be obtained along the lines of
this proofs. The reason is that an alternative recursive definition
that produces a unit with coordinates flipped would be needed. But
this is difficult to obtain without snoc lists. We therefore prove the
right unit law more directly by using properties of suprema.\<close>

lemma fps_onel [simp]:
  "1 * (f::('a::type,'b::{join_semilattice_zero,monoid_mult,mult_zero}) fps) = f"
proof (rule fps_ext)
  fix n :: "'a list"
  show "(1 * f) $ n = f $ n"
  proof (cases n)
    case Nil thus ?thesis
      by (simp add: times_fps_def)
  next
    case Cons thus ?thesis
      by (simp add: fps_mult_image splitset_eq_splitset_fun image_comp one_fps_def comp_def image_constant_conv)
  qed
qed

lemma fps_oner [simp]:
  "(f::('a::type,'b::{join_semilattice_zero,monoid_mult,mult_zero}) fps) * 1 = f"
proof (rule fps_ext)
  fix n :: "'a list"
  {
    fix z :: 'b
    have "(f * 1) $ n \<le> z \<longleftrightarrow> (\<forall>p \<in> splitset n. f $ (fst p) * 1 $ (snd p) \<le> z)"
      by (simp add: fps_mult_image sum_fun_image_sup)
    also have "... \<longleftrightarrow> (\<forall>a b. n = a @ b \<longrightarrow> f $ a * 1 $ b \<le> z)"
      unfolding splitset_def by simp
    also have "... \<longleftrightarrow> (f $ n * 1 $ [] \<le> z)"
      by (simp add: one_fps_def)
    finally have "(f * 1) $ n \<le> z \<longleftrightarrow> f $ n \<le> z"
      by simp
  }
  thus "(f * 1) $ n = f $ n"
    by (metis eq_iff)
qed

text \<open>Finally we prove associativity of convolution. This requires
splitting lists into three parts and rearranging these parts in two
different ways into splitsets. This rearrangement is captured by the
following technical lemma.\<close>

lemma splitset_rearrange:
  fixes F :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'b::join_semilattice_zero"
  shows "\<Sum>{\<Sum>{F (fst p) (fst q) (snd q) | q. q \<in> splitset (snd p)} | p. p \<in> splitset x} =
         \<Sum>{\<Sum>{F (fst q) (snd q) (snd p) | q. q \<in> splitset (fst p)} | p. p \<in> splitset x}"
    (is "?lhs = ?rhs")
proof -
  {
    fix z :: 'b
    have "?lhs \<le> z \<longleftrightarrow> (\<forall>p q r. x = p @ q @ r \<longrightarrow> F p q r \<le> z)"
      by (simp only: fset_to_im sum_fun_image_sup splitset_finite)
         (auto simp add: splitset_def)
    hence "?lhs \<le> z \<longleftrightarrow> ?rhs \<le> z"
      by (simp only: fset_to_im sum_fun_image_sup splitset_finite)
         (auto simp add: splitset_def)
  }
  thus ?thesis
    by (simp add: eq_iff)
qed

lemma fps_mult_assoc: "(f::('a::type,'b::dioid_one_zero) fps) * (g * h) = (f * g) * h"
proof (rule fps_ext)
  fix n :: "'a list"
  have "(f * (g * h)) $ n = \<Sum>{\<Sum>{f $ (fst p) * g $ (fst q) * h $ (snd q) | q. q \<in> splitset (snd p)} | p. p \<in> splitset n}"
    by (simp add: fps_mult_image sum_sum_distl_fun mult.assoc)
  also have "... = \<Sum>{\<Sum>{f $ (fst q) * g $ (snd q) * h $ (snd p) | q. q \<in> splitset (fst p)} | p. p \<in> splitset n}"
    by (fact splitset_rearrange)
  finally show "(f * (g * h)) $ n = ((f * g) * h) $ n"
    by (simp add: fps_mult_image sum_sum_distr_fun mult.assoc)
qed


subsection \<open>The Dioid Model of Formal Power Series\<close>

text \<open>We can now show that formal power series with suitably
defined operations form a dioid. Many of the underlying properties
already hold in weaker settings, where the target algebra is a
semilattice or semiring. We currently ignore this fact.\<close>

subclass (in dioid_one_zero) mult_zero
proof
  fix x :: 'a
  show "0 * x = 0"
    by (fact annil)
  show "x * 0 = 0"
    by (fact annir)
qed

instantiation fps :: (type,dioid_one_zero) dioid_one_zero
begin

  definition less_eq_fps where
    "(f::('a,'b) fps) \<le> g \<longleftrightarrow> f + g = g"

  definition less_fps where
    "(f::('a,'b) fps) < g \<longleftrightarrow> f \<le> g \<and> f \<noteq> g"

  instance
  proof
    fix f g h :: "('a,'b) fps"
    show "f + g + h = f + (g + h)"
      by (fact fps_add_assoc)
    show "f + g = g + f"
      by (fact fps_add_comm)
    show "f * g * h = f * (g * h)"
      by (metis fps_mult_assoc)
    show "(f + g) * h = f * h + g * h"
      by (fact fps_distr)
    show "1 * f = f"
      by (fact fps_onel)
    show "f * 1 = f"
      by (fact fps_oner)
    show "0 + f = f"
      by (fact fps_zeror)
    show "0 * f = 0"
      by (fact fps_annil)
    show "f * 0 = 0"
      by (fact fps_annir)
    show "f \<le> g \<longleftrightarrow> f + g = g"
      by (fact less_eq_fps_def)
    show "f < g \<longleftrightarrow> f \<le> g \<and> f \<noteq> g"
      by (fact less_fps_def)
    show "f + f = f"
      by (fact fps_add_idem)
    show "f * (g + h) = f \<cdot> g + f \<cdot> h"
      by (fact fps_distl)
  qed

end (* instantiation *)

lemma expand_fps_less_eq: "(f::('a,'b::dioid_one_zero) fps) \<le> g \<longleftrightarrow> (\<forall>n. f $ n \<le> g $ n)"
by (simp add: expand_fps_eq less_eq_def less_eq_fps_def)


subsection \<open>The Kleene Algebra Model of Formal Power Series\<close>

text \<open>There are two approaches to define the Kleene star. The first
one defines the star for a certain kind of (so-called proper) formal
power series into a semiring or dioid. The second one, which is more
interesting in the context of our algebraic hierarchy, shows that
formal power series into a Kleene algebra form a Kleene algebra. We
have only formalised the latter approach.\<close>

lemma Sum_splitlist_nonempty:
  "\<Sum>{f ys zs |ys zs. xs = ys @ zs} = ((f [] xs)::'a::join_semilattice_zero) + \<Sum>{f ys zs |ys zs. xs = ys @ zs \<and> ys \<noteq> []}"
proof -
  have "{f ys zs |ys zs. xs = ys @ zs} = {f ys zs |ys zs. xs = ys @ zs \<and> ys = []} \<union> {f ys zs |ys zs. xs = ys @ zs \<and> ys \<noteq> []}"
    by blast
  thus ?thesis using [[simproc add: finite_Collect]]
    by (simp add: sum.insert)
qed

lemma (in left_kleene_algebra) add_star_eq:
  "x + y \<cdot> y\<^sup>\<star> \<cdot> x = y\<^sup>\<star> \<cdot> x"
by (metis add.commute mult_onel star2 star_one troeger)

declare rev_conj_cong[fundef_cong]
  \<comment> \<open>required for the function package to prove termination of @{term star_fps_rep}\<close>

fun star_fps_rep where
  star_fps_rep_Nil: "star_fps_rep f [] = (f [])\<^sup>\<star>"
| star_fps_rep_Cons: "star_fps_rep f n = (f [])\<^sup>\<star> \<cdot> \<Sum>{f y \<cdot> star_fps_rep f z |y z. n = y @ z \<and> y \<noteq> []}"

instantiation fps :: (type,kleene_algebra) kleene_algebra
begin

  text \<open>We first define the star on functions, where we can use
  Isabelle's package for recursive functions, before lifting the
  definition to the type of formal power series.

  This definition of the star is from an unpublished manuscript by
  Esik and Kuich.\<close>

  lift_definition star_fps :: "('a, 'b) fps \<Rightarrow> ('a, 'b) fps" is star_fps_rep ..

  lemma star_fps_Nil [simp]: "f\<^sup>\<star> $ [] = (f $ [])\<^sup>\<star>"
  by (simp add: star_fps_def)

  lemma star_fps_Cons [simp]: "f\<^sup>\<star> $ (x # xs) = (f $ [])\<^sup>\<star> \<cdot> \<Sum>{f $ y \<cdot> f\<^sup>\<star> $ z |y z. x # xs = y @ z \<and> y \<noteq> []}"
  by (simp add: star_fps_def)

  instance
  proof
    fix f g h :: "('a,'b) fps"  
    have "1 + f \<cdot> f\<^sup>\<star> = f\<^sup>\<star>"
      apply (rule fps_ext)
      apply (case_tac n)
       apply (auto simp add: times_fps_def)
      apply (simp add: add_star_eq mult.assoc[THEN sym] Sum_splitlist_nonempty)
      apply (simp add: add_star_eq join.sup_commute)
    done
    thus "1 + f \<cdot> f\<^sup>\<star> \<le> f\<^sup>\<star>"
      by (metis order_refl)
    have "f \<cdot> g \<le> g \<longrightarrow> f\<^sup>\<star> \<cdot> g \<le> g"
      proof
        assume "f \<cdot> g \<le> g"
        hence 1: "\<And>u v. f $ u \<cdot> g $ v \<le> g $ (u @ v)"
          using [[simproc add: finite_Collect]]
          apply (simp add: expand_fps_less_eq)
          apply (drule_tac x="u @ v" in spec)
          apply (simp add: times_fps_def)
          apply (auto elim!: sum_less_eqE)
        done
        hence 2: "\<And>v. (f $ []) \<^sup>\<star> \<cdot> g $ v \<le> g $ v"
          apply (subgoal_tac "f $ [] \<cdot> g $ v \<le> g $ v")
           apply (metis star_inductl_var)
          apply (metis append_Nil)
        done
        show "f\<^sup>\<star> \<cdot> g \<le> g"
          using [[simproc add: finite_Collect]]
          apply (auto intro!: sum_less_eqI simp add: expand_fps_less_eq times_fps_def)
          apply (induct_tac "y" rule: length_induct)
          apply (case_tac "xs")
           apply (simp add: "2")
          using "2" apply (auto simp add: mult.assoc sum_distr)
          apply (rule_tac y="(f $ [])\<^sup>\<star> \<cdot> g $ (a # list @ z)" in order_trans)
           prefer 2
           apply (rule "2")
          apply (auto intro!: mult_isol[rule_format] sum_less_eqI)
          apply (drule_tac x="za" in spec)
          apply (drule mp)
           apply (metis append_eq_Cons_conv length_append less_not_refl2 add.commute not_less_eq trans_less_add1)
          apply (drule_tac z="f $ y" in mult_isol[rule_format])
          apply (auto elim!: order_trans simp add: mult.assoc)
          apply (metis "1" append_Cons append_assoc)
        done
      qed
    thus "h + f \<cdot> g \<le> g \<Longrightarrow> f\<^sup>\<star> \<cdot> h \<le> g"
      by (metis (no_types, lifting) distrib_left join.sup.bounded_iff less_eq_def)
    have "g \<cdot> f \<le> g \<longrightarrow> g \<cdot> f\<^sup>\<star> \<le> g"
      \<comment> \<open>this property is dual to the previous one; the proof is slightly different\<close>
      proof
        assume "g \<cdot> f \<le> g"
        hence 1: "\<And>u v. g $ u \<cdot> f $ v \<le> g $ (u @ v)"
          using [[simproc add: finite_Collect]]
          apply (simp add: expand_fps_less_eq)
          apply (drule_tac x="u @ v" in spec)
          apply (simp add: times_fps_def)
          apply (auto elim!: sum_less_eqE)
        done
        hence 2: "\<And>u. g $ u \<cdot> (f $ [])\<^sup>\<star> \<le> g $ u"
          apply (subgoal_tac "g $ u \<cdot> f $ [] \<le> g $ u")
           apply (metis star_inductr_var)
          apply (metis append_Nil2)
        done
        show "g \<cdot> f\<^sup>\<star> \<le> g"
          using [[simproc add: finite_Collect]]
          apply (auto intro!: sum_less_eqI simp add: expand_fps_less_eq times_fps_def)
          apply (rule_tac P="\<lambda>y. g $ y \<cdot> f\<^sup>\<star> $ z \<le> g $ (y @ z)" and x="y" in allE)
           prefer 2
           apply assumption
          apply (induct_tac "z" rule: length_induct)
          apply (case_tac "xs")
           apply (simp add: "2")
          apply (auto intro!: sum_less_eqI simp add: sum_distl)
          apply (rule_tac y="g $ x \<cdot> f $ yb \<cdot> f\<^sup>\<star> $ z" in order_trans)
           apply (simp add: "2" mult.assoc[THEN sym] mult_isor)
          apply (rule_tac y="g $ (x @ yb) \<cdot> f\<^sup>\<star> $ z" in order_trans)
           apply (simp add: "1" mult_isor)
          apply (drule_tac x="z" in spec)
          apply (drule mp)
           apply (metis append_eq_Cons_conv length_append less_not_refl2 add.commute not_less_eq trans_less_add1)
          apply (metis append_assoc)
        done
      qed
    thus "h + g \<cdot> f \<le> g \<Longrightarrow> h \<cdot> f\<^sup>\<star> \<le> g"
      by (metis (no_types, lifting) distrib_right' join.sup.bounded_iff order_prop)
  qed

end (* instantiation *)

end
