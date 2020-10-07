(* Author: Andreas Lochbihler, ETH Zurich *)

subsection \<open>Probability mass functions implemented as lists with duplicates\<close>

theory Applicative_Probability_List imports
  Applicative_List
  Complex_Main
begin

lemma sum_list_concat_map: "sum_list (concat (map f xs)) = sum_list (map (\<lambda>x. sum_list (f x)) xs)"
by(induction xs) simp_all

context includes applicative_syntax begin

lemma set_ap_list [simp]: "set (f \<diamondop> x) = (\<lambda>(f, x). f x) ` (set f \<times> set x)"
by(auto simp add: ap_list_def List.bind_def)

text \<open>We call the implementation type \<open>pfp\<close> because it is the basis for the Haskell library
  Probability by Martin Erwig and Steve Kollmansberger (Probabilistic Functional Programming).\<close>

typedef 'a pfp = "{xs :: ('a \<times> real) list. (\<forall>(_, p) \<in> set xs. p > 0) \<and> sum_list (map snd xs) = 1}"
proof
  show "[(x, 1)] \<in> ?pfp" for x by simp
qed

setup_lifting type_definition_pfp

lift_definition pure_pfp :: "'a \<Rightarrow> 'a pfp" is "\<lambda>x. [(x, 1)]" by simp

lift_definition ap_pfp :: "('a \<Rightarrow> 'b) pfp \<Rightarrow> 'a pfp \<Rightarrow> 'b pfp"
is "\<lambda>fs xs. [\<lambda>(f, p) (x, q). (f x, p * q)] \<diamondop> fs \<diamondop> xs"
proof safe
  fix xs :: "(('a \<Rightarrow> 'b) \<times> real) list" and ys :: "('a \<times> real) list"
  assume xs: "\<forall>(x, y) \<in> set xs. 0 < y" "sum_list (map snd xs) = 1"
    and ys: "\<forall>(x, y) \<in> set ys. 0 < y" "sum_list (map snd ys) = 1"
  let ?ap = "[\<lambda>(f, p) (x, q). (f x, p * q)] \<diamondop> xs \<diamondop> ys"
  show "0 < b" if "(a, b) \<in> set ?ap" for a b using that xs ys
    by(auto intro!: mult_pos_pos)
  show "sum_list (map snd ?ap) = 1" using xs ys
    by(simp add: ap_list_def List.bind_def map_concat o_def split_beta sum_list_concat_map sum_list_const_mult)
qed

adhoc_overloading Applicative.ap ap_pfp

applicative pfp
 for pure: pure_pfp
     ap: ap_pfp
proof -
  show "pure_pfp (\<lambda>x. x) \<diamondop> x = x" for x :: "'a pfp"
    by transfer(simp add: ap_list_def List.bind_def)
  show "pure_pfp f \<diamondop> pure_pfp x = pure_pfp (f x)" for f :: "'a \<Rightarrow> 'b" and x
    by transfer (applicative_lifting; simp)
  show "pure_pfp (\<lambda>g f x. g (f x)) \<diamondop> g \<diamondop> f \<diamondop> x = g \<diamondop> (f \<diamondop> x)"
    for g :: "('b \<Rightarrow> 'c) pfp" and f :: "('a \<Rightarrow> 'b) pfp" and x
    by transfer(applicative_lifting; clarsimp)
  show "f \<diamondop> pure_pfp x = pure_pfp (\<lambda>f. f x) \<diamondop> f" for f :: "('a \<Rightarrow> 'b) pfp" and x
    by transfer(applicative_lifting; clarsimp)
qed

end

end
