(* Author: Andreas Lochbihler, Digital Asset *)

subsection \<open>Filters\<close>

theory Applicative_Filter imports 
  Complex_Main
  Applicative
  "HOL-Library.Conditional_Parametricity"
begin

definition pure_filter :: "'a \<Rightarrow> 'a filter" where
  "pure_filter x = principal {x}"

definition ap_filter :: "('a \<Rightarrow> 'b) filter \<Rightarrow> 'a filter \<Rightarrow> 'b filter" where
  "ap_filter F X = filtermap (\<lambda>(f, x). f x) (prod_filter F X)"

lemma eq_on_UNIV: "eq_on UNIV = (=)"
  by auto

declare filtermap_parametric[transfer_rule]

parametric_constant pure_filter_parametric[transfer_rule]: pure_filter_def
parametric_constant ap_filter_parametric [transfer_rule]: ap_filter_def

applicative filter (C)
  \<comment> \<open>K is available for not-@{term bot} filters and W isholds not available\<close>
for 
  pure: "pure_filter"
  ap: "ap_filter"
  rel: "rel_filter"
proof -
  show "ap_filter (pure_filter f) (pure_filter x) = pure_filter (f x)" for f :: "'a \<Rightarrow> 'b" and x
    by(simp add: ap_filter_def pure_filter_def principal_prod_principal)
  show "ap_filter (ap_filter (ap_filter (pure_filter (\<lambda>g f x. g (f x))) g) f) x =
    ap_filter g (ap_filter f x)" for f :: "('a \<Rightarrow> 'b) filter" and g :: "('b \<Rightarrow> 'c) filter" and x
    by(simp add: ap_filter_def pure_filter_def filtermap_filtermap prod_filtermap1 prod_filtermap2 apfst_def case_prod_map_prod prod_filter_assoc prod_filter_principal_singleton split_beta)
  show "ap_filter (pure_filter (\<lambda>x. x)) x = x" for x :: "'a filter"
    by(simp add: ap_filter_def pure_filter_def prod_filter_principal_singleton filtermap_filtermap)
  show "ap_filter (ap_filter (ap_filter (pure_filter (\<lambda>f x y. f y x)) f) x) y =
    ap_filter (ap_filter f y) x" for f :: "('b \<Rightarrow> 'a \<Rightarrow> 'c) filter" and x y
    apply(simp add: ap_filter_def pure_filter_def filtermap_filtermap prod_filter_principal_singleton2 prod_filter_principal_singleton prod_filtermap1 prod_filtermap2 prod_filter_assoc split_beta)
    apply(subst (2) prod_filter_commute)
    apply(simp add: filtermap_filtermap prod_filtermap1 prod_filtermap2)
    done
  show "rel_fun R (rel_filter R) pure_filter pure_filter" for R :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
    by(rule pure_filter_parametric)
  show "rel_filter R (ap_filter f x) (ap_filter g x)" if "rel_filter (rel_fun (eq_on UNIV) R) f g" 
    for R and f :: "('a \<Rightarrow> 'b) filter" and g :: "('a \<Rightarrow> 'c) filter" and x
    supply that[unfolded eq_on_UNIV, transfer_rule] by transfer_prover
qed

end