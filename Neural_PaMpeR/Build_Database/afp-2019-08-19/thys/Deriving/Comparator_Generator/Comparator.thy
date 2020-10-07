(*  Title:       Deriving class instances for datatypes
    Author:      Christian Sternagel and René Thiemann  <christian.sternagel|rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann 
    License:     LGPL
*)
section \<open>Comparisons\<close>

subsection \<open>Comparators and Linear Orders\<close>

theory Comparator
imports Main
begin

text \<open>Instead of having to define a strict and a weak linear order, @{term "((<), (\<le>))"},
 one can alternative use a comparator to define the linear order, which may deliver 
 three possible outcomes when comparing two values.\<close>

datatype order = Eq | Lt | Gt

type_synonym 'a comparator = "'a \<Rightarrow> 'a \<Rightarrow> order"

text \<open>In the following, we provide the obvious definitions how to switch between 
  linear orders and comparators.\<close>

definition lt_of_comp :: "'a comparator \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "lt_of_comp acomp x y = (case acomp x y of Lt \<Rightarrow> True | _ \<Rightarrow> False)"

definition le_of_comp :: "'a comparator \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "le_of_comp acomp x y = (case acomp x y of Gt \<Rightarrow> False | _ \<Rightarrow> True)"
  
definition comp_of_ords :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a comparator" where
  "comp_of_ords le lt x y = (if lt x y then Lt else if le x y then Eq else Gt)"

lemma comp_of_ords_of_le_lt[simp]: "comp_of_ords (le_of_comp c) (lt_of_comp c) = c"
  by (intro ext, auto simp: comp_of_ords_def le_of_comp_def lt_of_comp_def split: order.split)

lemma lt_of_comp_of_ords: "lt_of_comp (comp_of_ords le lt) = lt"
  by (intro ext, auto simp: comp_of_ords_def le_of_comp_def lt_of_comp_def split: order.split)

lemma le_of_comp_of_ords_gen: "(\<And> x y. lt x y \<Longrightarrow> le x y) \<Longrightarrow> le_of_comp (comp_of_ords le lt) = le"
  by (intro ext, auto simp: comp_of_ords_def le_of_comp_def lt_of_comp_def split: order.split)

lemma le_of_comp_of_ords_linorder: assumes "class.linorder le lt"
  shows "le_of_comp (comp_of_ords le lt) = le"
proof -
  interpret linorder le lt by fact
  show ?thesis by (rule le_of_comp_of_ords_gen) simp
qed

fun invert_order:: "order \<Rightarrow> order" where
  "invert_order Lt = Gt" |
  "invert_order Gt = Lt" |
  "invert_order Eq = Eq"

locale comparator =
  fixes comp :: "'a comparator"
  assumes sym: "invert_order (comp x y) = comp y x"
    and weak_eq: "comp x y = Eq \<Longrightarrow> x = y"
    and trans: "comp x y = Lt \<Longrightarrow> comp y z = Lt \<Longrightarrow> comp x z = Lt"
begin 

lemma eq: "(comp x y = Eq) = (x = y)"
proof
  assume "x = y"
  with sym [of y y] show "comp x y = Eq" by (cases "comp x y") auto
qed (rule weak_eq)

lemma comp_same [simp]:
  "comp x x = Eq"
  by (simp add: eq)

abbreviation "lt \<equiv> lt_of_comp comp"
abbreviation "le \<equiv> le_of_comp comp"

lemma linorder: "class.linorder le lt"
proof
  note [simp] = lt_of_comp_def le_of_comp_def
  fix x y z :: 'a
  show "lt x y = (le x y \<and> \<not> le y x)"
    using sym [of x y] by (cases "comp x y") (simp_all)
  show "le x y \<or> le y x"
    using sym [of x y] by (cases "comp x y") (simp_all)
  show "le x x" using eq [of x x] by (simp)
  show "le x y \<Longrightarrow> le y x \<Longrightarrow> x = y"
    using sym [of x y] by (cases "comp x y") (simp_all add: eq)
  show "le x y \<Longrightarrow> le y z \<Longrightarrow> le x z"
    by (cases "comp x y" "comp y z" rule: order.exhaust [case_product order.exhaust])
       (auto dest: trans simp: eq)
qed

sublocale linorder le lt
  by (rule linorder)

lemma Gt_lt_conv: "comp x y = Gt \<longleftrightarrow> lt y x" 
  unfolding lt_of_comp_def sym[of x y, symmetric] 
  by (cases "comp x y", auto)
lemma Lt_lt_conv: "comp x y = Lt \<longleftrightarrow> lt x y" 
  unfolding lt_of_comp_def by (cases "comp x y", auto)
lemma eq_Eq_conv: "comp x y = Eq \<longleftrightarrow> x = y" 
  by (rule eq)
lemma nGt_le_conv: "comp x y \<noteq> Gt \<longleftrightarrow> le x y" 
  unfolding le_of_comp_def by (cases "comp x y", auto)
lemma nLt_le_conv: "comp x y \<noteq> Lt \<longleftrightarrow> le y x" 
  unfolding le_of_comp_def sym[of x y, symmetric] by (cases "comp x y", auto)
lemma nEq_neq_conv: "comp x y \<noteq> Eq \<longleftrightarrow> x \<noteq> y" 
  using eq_Eq_conv[of x y] by simp

lemmas le_lt_convs =  nLt_le_conv nGt_le_conv Gt_lt_conv Lt_lt_conv eq_Eq_conv nEq_neq_conv

lemma two_comparisons_into_case_order: 
  "(if le x y then (if x = y then P else Q) else R) = (case_order P Q R (comp x y))" 
  "(if le x y then (if y = x then P else Q) else R) = (case_order P Q R (comp x y))" 
  "(if le x y then (if le y x then P else Q) else R) = (case_order P Q R (comp x y))" 
  "(if le x y then (if lt x y then Q else P) else R) = (case_order P Q R (comp x y))" 
  "(if lt x y then Q else (if le x y then P else R)) = (case_order P Q R (comp x y))" 
  "(if lt x y then Q else (if lt y x then R else P)) = (case_order P Q R (comp x y))" 
  "(if lt x y then Q else (if x = y then P else R)) = (case_order P Q R (comp x y))" 
  "(if lt x y then Q else (if y = x then P else R)) = (case_order P Q R (comp x y))" 
  "(if x = y then P else (if lt y x then R else Q)) = (case_order P Q R (comp x y))" 
  "(if x = y then P else (if lt x y then Q else R)) = (case_order P Q R (comp x y))" 
  "(if x = y then P else (if le y x then R else Q)) = (case_order P Q R (comp x y))" 
  "(if x = y then P else (if le x y then Q else R)) = (case_order P Q R (comp x y))"
  by (auto simp: le_lt_convs split: order.splits)

end

lemma comp_of_ords: assumes "class.linorder le lt"
  shows "comparator (comp_of_ords le lt)"
proof -
  interpret linorder le lt by fact
  show ?thesis
    by (unfold_locales, auto simp: comp_of_ords_def split: if_splits)
qed

definition (in linorder) comparator_of :: "'a comparator" where
  "comparator_of x y = (if x < y then Lt else if x = y then Eq else Gt)"

lemma comparator_of: "comparator comparator_of"
  by unfold_locales (auto split: if_splits simp: comparator_of_def)

end
