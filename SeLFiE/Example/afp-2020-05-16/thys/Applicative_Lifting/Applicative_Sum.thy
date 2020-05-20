(* Author: Joshua Schneider, ETH Zurich *)

subsection \<open>Sum types\<close>

theory Applicative_Sum imports
  Applicative
  "HOL-Library.Adhoc_Overloading"
begin

text \<open>
  There are several ways to define an applicative functor based on sum types. First, we can choose
  whether the left or the right type is fixed. Both cases are isomorphic, of course. Next, what
  should happen if two values of the fixed type are combined? The corresponding operator must be
  associative, or the idiom laws don't hold true.

  We focus on the cases where the right type is fixed. We define two concrete functors: One based
  on Haskell's \textsf{Either} datatype, which prefers the value of the left operand, and a generic
  one using the @{class semigroup_add} class. Only the former lifts the \textbf{W} combinator,
  though.
\<close>

fun ap_sum :: "('e \<Rightarrow> 'e \<Rightarrow> 'e) \<Rightarrow> ('a \<Rightarrow> 'b) + 'e \<Rightarrow> 'a + 'e \<Rightarrow> 'b + 'e"
where
    "ap_sum _ (Inl f) (Inl x) = Inl (f x)"
  | "ap_sum _ (Inl _) (Inr e) = Inr e"
  | "ap_sum _ (Inr e) (Inl _) = Inr e"
  | "ap_sum c (Inr e1) (Inr e2) = Inr (c e1 e2)"

abbreviation "ap_either \<equiv> ap_sum (\<lambda>x _. x)"
abbreviation "ap_plus \<equiv> ap_sum (plus :: 'a :: semigroup_add \<Rightarrow> _)"

abbreviation (input) pure_sum where "pure_sum \<equiv> Inl"
adhoc_overloading Applicative.pure pure_sum
adhoc_overloading Applicative.ap ap_either (* ap_plus *)

lemma ap_sum_id: "ap_sum c (Inl id) x = x"
by (cases x) simp_all

lemma ap_sum_ichng: "ap_sum c f (Inl x) = ap_sum c (Inl (\<lambda>f. f x)) f"
by (cases f) simp_all

lemma (in semigroup) ap_sum_comp:
  "ap_sum f (ap_sum f (ap_sum f (Inl (o)) h) g) x = ap_sum f h (ap_sum f g x)"
by(cases h g x rule: sum.exhaust[case_product sum.exhaust, case_product sum.exhaust])
  (simp_all add: local.assoc)

lemma semigroup_const: "semigroup (\<lambda>x y. x)"
by unfold_locales simp

locale either_af =
  fixes B :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
  assumes B_refl: "reflp B"
begin

applicative either (W)
for
  pure: Inl
  ap: ap_either
  rel: "\<lambda>A. rel_sum A B"
proof -
  include applicative_syntax
  { fix f :: "('c \<Rightarrow> 'c \<Rightarrow> 'd) + 'a" and x
    show "pure (\<lambda>f x. f x x) \<diamondop> f \<diamondop> x = f \<diamondop> x \<diamondop> x"
      by (cases f x rule: sum.exhaust[case_product sum.exhaust]) simp_all
  next
    interpret semigroup "\<lambda>x y. x" by(rule semigroup_const)
    fix g :: "('d \<Rightarrow> 'e) + 'a" and f :: "('c \<Rightarrow> 'd) + 'a" and x
    show "pure (\<lambda>g f x. g (f x)) \<diamondop> g \<diamondop> f \<diamondop> x = g \<diamondop> (f \<diamondop> x)"
      by(rule ap_sum_comp[simplified comp_def[abs_def]])
  next
    fix R and f :: "('c \<Rightarrow> 'd) + 'b" and g :: "('c \<Rightarrow> 'e) + 'b" and x
    assume "rel_sum (rel_fun (eq_on UNIV) R) B f g"
    then show "rel_sum R B (f \<diamondop> x) (g \<diamondop> x)"
      by (cases f g x rule: sum.exhaust[case_product sum.exhaust, case_product sum.exhaust])
        (auto intro: B_refl[THEN reflpD] elim: rel_funE)
  }
qed (auto intro: ap_sum_id[simplified id_def] ap_sum_ichng)

end  (* locale *)

interpretation either_af "(=)" by unfold_locales simp

applicative semigroup_sum
for
  pure: Inl
  ap: ap_plus
using
  ap_sum_id[simplified id_def]
  ap_sum_ichng
  add.ap_sum_comp[simplified comp_def[abs_def]]
by auto

no_adhoc_overloading Applicative.pure pure_sum

end
