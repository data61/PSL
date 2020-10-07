(*<*)
theory Interval
  imports "HOL-Library.Extended_Nat" "HOL-Library.Product_Lexorder"
begin
(*>*)

section \<open>Intervals\<close>

typedef \<I> = "{(i :: nat, j :: enat). i \<le> j}"
  by (intro exI[of _ "(0, \<infinity>)"]) auto

setup_lifting type_definition_\<I>

instantiation \<I> :: equal begin
lift_definition equal_\<I> :: "\<I> \<Rightarrow> \<I> \<Rightarrow> bool" is "(=)" .
instance by standard (transfer, auto)
end

instantiation \<I> :: linorder begin
lift_definition less_eq_\<I> :: "\<I> \<Rightarrow> \<I> \<Rightarrow> bool" is "(\<le>)" .
lift_definition less_\<I> :: "\<I> \<Rightarrow> \<I> \<Rightarrow> bool" is "(<)" .
instance by standard (transfer, auto)+
end


lift_definition all :: \<I> is "(0, \<infinity>)" by simp
lift_definition left :: "\<I> \<Rightarrow> nat" is fst .
lift_definition right :: "\<I> \<Rightarrow> enat" is snd .
lift_definition point :: "nat \<Rightarrow> \<I>" is "\<lambda>n. (n, enat n)" by simp
lift_definition init :: "nat \<Rightarrow> \<I>" is "\<lambda>n. (0, enat n)" by auto
abbreviation mem where "mem n I \<equiv> (left I \<le> n \<and> n \<le> right I)"
lift_definition subtract :: "nat \<Rightarrow> \<I> \<Rightarrow> \<I>" is
  "\<lambda>n (i, j). (i - n, j - enat n)" by (auto simp: diff_enat_def split: enat.splits)
lift_definition add :: "nat \<Rightarrow> \<I> \<Rightarrow> \<I>" is
  "\<lambda>n (a, b). (a, b + enat n)" by (auto simp add: add_increasing2)

lemma left_right: "left I \<le> right I"
  by transfer auto

lemma point_simps[simp]:
  "left (point n) = n"
  "right (point n) = n"
  by (transfer; auto)+

lemma init_simps[simp]:
  "left (init n) = 0"
  "right (init n) = n"
  by (transfer; auto)+

lemma subtract_simps[simp]:
  "left (subtract n I) = left I - n"
  "right (subtract n I) = right I - n"
  "subtract 0 I = I"
  "subtract x (point y) = point (y - x)"
  by (transfer; auto)+

definition shifted :: "\<I> \<Rightarrow> \<I> set" where
  "shifted I = (\<lambda>n. subtract n I) ` {0 .. (case right I of \<infinity> \<Rightarrow> left I | enat n \<Rightarrow> n)}"

lemma subtract_too_much: "i > (case right I of \<infinity> \<Rightarrow> left I | enat n \<Rightarrow> n) \<Longrightarrow>
  subtract i I = subtract (case right I of \<infinity> \<Rightarrow> left I | enat n \<Rightarrow> n) I"
  by transfer (auto split: enat.splits)

lemma subtract_shifted: "subtract n I \<in> shifted I"
  by (cases "n \<le> (case right I of \<infinity> \<Rightarrow> left I | enat n \<Rightarrow> n)")
    (auto simp: shifted_def subtract_too_much)

lemma finite_shifted: "finite (shifted I)"
  unfolding shifted_def by auto

definition interval :: "nat \<Rightarrow> enat \<Rightarrow> \<I>" where
  "interval l r = (if l \<le> r then Abs_\<I> (l, r) else undefined)"

lemma [code abstract]: "Rep_\<I> (interval l r) = (if l \<le> r then (l, r) else Rep_\<I> undefined)"
  unfolding interval_def using Abs_\<I>_inverse by simp

(*<*)
end
(*>*)