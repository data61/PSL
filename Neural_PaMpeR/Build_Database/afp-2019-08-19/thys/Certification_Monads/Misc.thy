(* Title:     Parser_Monad
   Author:    Christian Sternagel
   Author:    René Thiemann
*)

section \<open>More material on parsing\<close>

theory Misc
  imports Main
begin

definition span :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<times> 'a list"
  where [simp]: "span P xs = (takeWhile P xs, dropWhile P xs)"

lemma span_code [code]:
  "span P [] = ([], [])"
  "span P (x # xs) =
    (if P x then let (ys, zs) = span P xs in (x # ys, zs) else ([], x # xs))"
  by simp_all

definition splitter :: "char list \<Rightarrow> string \<Rightarrow> string \<times> string"
where
  [code_unfold]: "splitter cs s = span (\<lambda>c. c \<in> set cs) s"

end
