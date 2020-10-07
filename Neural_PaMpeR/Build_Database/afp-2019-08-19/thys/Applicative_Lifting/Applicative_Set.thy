(* Author: Joshua Schneider, ETH Zurich *)

subsection \<open>Set with Cartesian product\<close>

theory Applicative_Set imports
  Applicative
  "HOL-Library.Adhoc_Overloading"
begin

definition ap_set :: "('a \<Rightarrow> 'b) set \<Rightarrow> 'a set \<Rightarrow> 'b set"
  where "ap_set F X = {f x | f x. f \<in> F \<and> x \<in> X}"

adhoc_overloading Applicative.ap ap_set

lemma ap_set_transfer[transfer_rule]:
  "rel_fun (rel_set (rel_fun A B)) (rel_fun (rel_set A) (rel_set B)) ap_set ap_set"
unfolding ap_set_def[abs_def] rel_set_def
by (fastforce elim: rel_funE)

applicative set (C)
for
  pure: "\<lambda>x. {x}"
  ap: ap_set
  rel: rel_set
  set: "\<lambda>x. x"
proof -
  fix R :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  show "rel_fun R (rel_set R) (\<lambda>x. {x}) (\<lambda>x. {x})" by (auto intro: rel_setI)
next
  fix R and f :: "('a \<Rightarrow> 'b) set" and g :: "('a \<Rightarrow> 'c) set" and x
  assume [transfer_rule]: "rel_set (rel_fun (eq_on x) R) f g"
  have [transfer_rule]: "rel_set (eq_on x) x x" by (auto intro: rel_setI)
  show "rel_set R (ap_set f x) (ap_set g x)" by transfer_prover
qed (unfold ap_set_def, fast+)

end
