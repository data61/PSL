(*
  File: Interval.thy
  Author: Bohua Zhan
*)

section \<open>Intervals\<close>

theory Interval
  imports "Auto2_HOL.Auto2_Main"
begin

text \<open>Basic definition of intervals.\<close>

subsection \<open>Definition of interval\<close>

datatype 'a interval = Interval (low: 'a) (high: 'a)
setup \<open>add_simple_datatype "interval"\<close>

instantiation interval :: (linorder) linorder begin

definition int_less: "(a < b) = (low a < low b | (low a = low b \<and> high a < high b))"
definition int_less_eq: "(a \<le> b) = (low a < low b | (low a = low b \<and> high a \<le> high b))"

instance proof
  fix x y z :: "'a interval"
  show a: "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    using int_less int_less_eq by force
  show b: "x \<le> x"
    by (simp add: int_less_eq)
  show c: "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (smt int_less_eq dual_order.trans less_trans)
  show d: "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    using int_less_eq a interval.expand int_less by fastforce
  show e: "x \<le> y \<or> y \<le> x"
    by (meson int_less_eq leI not_less_iff_gr_or_eq)
qed end

definition is_interval :: "('a::linorder) interval \<Rightarrow> bool" where [rewrite]:
  "is_interval it \<longleftrightarrow> (low it \<le> high it)"

subsection \<open>Definition of interval with an index\<close>

datatype 'a idx_interval = IdxInterval (int: "'a interval") (idx: nat)
setup \<open>add_simple_datatype "idx_interval"\<close>

instantiation idx_interval :: (linorder) linorder begin

definition iint_less: "(a < b) = (int a < int b | (int a = int b \<and> idx a < idx b))"
definition iint_less_eq: "(a \<le> b) = (int a < int b | (int a = int b \<and> idx a \<le> idx b))"

instance proof
  fix x y z :: "'a idx_interval"
  show a: "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    using iint_less iint_less_eq by force
  show b: "x \<le> x"
    by (simp add: iint_less_eq)
  show c: "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (smt iint_less_eq dual_order.trans less_trans)
  show d: "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    using a idx_interval.expand iint_less iint_less_eq by auto
  show e: "x \<le> y \<or> y \<le> x"
    by (meson iint_less_eq leI not_less_iff_gr_or_eq)
qed end

lemma interval_less_to_le_low [forward]:
  "(a::('a::linorder idx_interval)) < b \<Longrightarrow> low (int a) \<le> low (int b)"
  by (metis eq_iff iint_less int_less less_imp_le)

subsection \<open>Overlapping intervals\<close>

definition is_overlap :: "('a::linorder) interval \<Rightarrow> 'a interval \<Rightarrow> bool" where [rewrite]:
  "is_overlap x y \<longleftrightarrow> (high x \<ge> low y \<and> high y \<ge> low x)"

definition has_overlap :: "('a::linorder) idx_interval set \<Rightarrow> 'a interval \<Rightarrow> bool" where [rewrite]:
  "has_overlap xs y \<longleftrightarrow> (\<exists>x\<in>xs. is_overlap (int x) y)"

end
