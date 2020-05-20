(*  Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

section "Deterministic automata"

theory DA
imports AutoProj
begin

type_synonym ('a,'s)da = "'s * ('a \<Rightarrow> 's \<Rightarrow> 's) * ('s \<Rightarrow> bool)"

definition
 foldl2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b" where
"foldl2 f xs a = foldl (\<lambda>a b. f b a) a xs"

definition
 delta :: "('a,'s)da \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> 's" where
"delta A = foldl2 (next A)"

definition
 accepts :: "('a,'s)da \<Rightarrow> 'a list \<Rightarrow> bool" where
"accepts A = (\<lambda>w. fin A (delta A w (start A)))"

lemma [simp]: "foldl2 f [] a = a \<and> foldl2 f (x#xs) a = foldl2 f xs (f x a)"
by(simp add:foldl2_def)

lemma delta_Nil[simp]: "delta A [] s = s"
by(simp add:delta_def)

lemma delta_Cons[simp]: "delta A (a#w) s = delta A w (next A a s)"
by(simp add:delta_def)

lemma delta_append[simp]:
 "\<And>q ys. delta A (xs@ys) q = delta A ys (delta A xs q)"
by(induct xs) simp_all

end
