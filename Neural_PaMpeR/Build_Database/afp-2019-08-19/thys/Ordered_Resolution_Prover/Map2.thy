(*  Title:       Map Function on Two Parallel Lists
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2017
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>Map Function on Two Parallel Lists\<close>

theory Map2
  imports Main
begin

text \<open>
This theory defines a map function that applies a (curried) binary function elementwise to two
parallel lists.

The definition is taken from @{url "https://www.isa-afp.org/browser_info/current/AFP/Jinja/Listn.html"}.
\<close>

abbreviation map2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list" where
  "map2 f xs ys \<equiv> map (case_prod f) (zip xs ys)"

lemma map2_empty_iff[simp]: "map2 f xs ys = [] \<longleftrightarrow> xs = [] \<or> ys = []"
  by (metis Nil_is_map_conv list.exhaust list.simps(3) zip.simps(1) zip_Cons_Cons zip_Nil)

lemma image_map2: "length t = length s \<Longrightarrow> g ` set (map2 f t s) = set (map2 (\<lambda>a b. g (f a b)) t s)"
  by auto

lemma map2_tl: "length t = length s \<Longrightarrow> map2 f (tl t) (tl s) = tl (map2 f t s)"
  by (metis (no_types, lifting) hd_Cons_tl list.sel(3) map2_empty_iff map_tl tl_Nil zip_Cons_Cons)

lemma map_zip_assoc:
  "map f (zip (zip xs ys) zs) = map (\<lambda>(x, y, z). f ((x, y), z)) (zip xs (zip ys zs))"
  by (induct zs arbitrary: xs ys) (auto simp add: zip.simps(2) split: list.splits)

lemma set_map2_ex:
  assumes "length t = length s"
  shows "set (map2 f s t) = {x. \<exists>i < length t. x = f (s ! i) (t ! i)}"
proof (rule; rule)
  fix x
  assume "x \<in> set (map2 f s t)"
  then obtain i where i_p: "i < length (map2 f s t) \<and> x = map2 f s t ! i"
    by (metis in_set_conv_nth)
  from i_p have "i < length t"
    by auto
  moreover from this i_p have "x = f (s ! i) (t ! i)"
    using assms by auto
  ultimately show "x \<in> {x. \<exists>i < length t. x = f (s ! i) (t ! i)}"
    using assms by auto
next
  fix x
  assume "x \<in> {x. \<exists>i < length t. x = f (s ! i) (t ! i)}"
  then obtain i where i_p: "i < length t \<and> x = f (s ! i) (t ! i)"
    by auto
  then have "i < length (map2 f s t)"
    using assms by auto
  moreover from i_p have "x = map2 f s t ! i"
    using assms by auto
  ultimately show "x \<in> set (map2 f s t)"
    by (metis in_set_conv_nth)
qed

end
