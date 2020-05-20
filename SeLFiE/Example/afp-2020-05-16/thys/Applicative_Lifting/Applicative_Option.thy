(* Author: Joshua Schneider, ETH Zurich *)

subsection \<open>Option\<close>

theory Applicative_Option imports
  Applicative
  "HOL-Library.Adhoc_Overloading"
begin

fun ap_option :: "('a \<Rightarrow> 'b) option \<Rightarrow> 'a option \<Rightarrow> 'b option"
where
    "ap_option (Some f) (Some x) = Some (f x)"
  | "ap_option _ _ = None"

abbreviation (input) pure_option :: "'a \<Rightarrow> 'a option"
where "pure_option \<equiv> Some"

adhoc_overloading Applicative.pure pure_option
adhoc_overloading Applicative.ap ap_option

lemma some_ap_option: "ap_option (Some f) x = map_option f x"
by (cases x) simp_all

lemma ap_some_option: "ap_option f (Some x) = map_option (\<lambda>g. g x) f"
by (cases f) simp_all

lemma ap_option_transfer[transfer_rule]:
  "rel_fun (rel_option (rel_fun A B)) (rel_fun (rel_option A) (rel_option B)) ap_option ap_option"
by(auto elim!: option.rel_cases simp add: rel_fun_def)

applicative option (C, W)
for
  pure: Some
  ap: ap_option
  rel: rel_option
  set: set_option
proof -
  include applicative_syntax
  { fix x :: "'a option"
    show "pure (\<lambda>x. x) \<diamondop> x = x" by (cases x) simp_all
  next
    fix g :: "('b \<Rightarrow> 'c) option" and f :: "('a \<Rightarrow> 'b) option" and x
    show "pure (\<lambda>g f x. g (f x)) \<diamondop> g \<diamondop> f \<diamondop> x = g \<diamondop> (f \<diamondop> x)"
      by (cases g f x rule: option.exhaust[case_product option.exhaust, case_product option.exhaust]) simp_all
  next
    fix f :: "('b \<Rightarrow> 'a \<Rightarrow> 'c) option" and x y
    show "pure (\<lambda>f x y. f y x) \<diamondop> f \<diamondop> x \<diamondop> y = f \<diamondop> y \<diamondop> x"
      by (cases f x y rule: option.exhaust[case_product option.exhaust, case_product option.exhaust]) simp_all
  next
    fix f :: "('a \<Rightarrow> 'a \<Rightarrow> 'b) option" and x
    show "pure (\<lambda>f x. f x x) \<diamondop> f \<diamondop> x = f \<diamondop> x \<diamondop> x"
      by (cases f x rule: option.exhaust[case_product option.exhaust]) simp_all
  next
    fix R :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
    show "rel_fun R (rel_option R) pure pure" by transfer_prover
  next
    fix R and f :: "('a \<Rightarrow> 'b) option" and g :: "('a \<Rightarrow> 'c) option" and x
    assume [transfer_rule]: "rel_option (rel_fun (eq_on (set_option x)) R) f g"
    have [transfer_rule]: "rel_option (eq_on (set_option x)) x x" by (auto intro: option.rel_refl_strong)
    show "rel_option R (f \<diamondop> x) (g \<diamondop> x)" by transfer_prover
  }
qed (simp add: some_ap_option ap_some_option)

lemma map_option_ap_conv[applicative_unfold]: "map_option f x = ap_option (pure f) x"
by (cases x rule: option.exhaust) simp_all

no_adhoc_overloading Applicative.pure pure_option \<comment> \<open>We do not want to print all occurrences of @{const "Some"} as @{const "pure"}\<close>

end
