(*  Title:      Nominal2_Eqvt
    Author:     Brian Huffman,
    Author:     Christian Urban

    Test cases for perm_simp
*)
theory Eqvt
imports Nominal2_Base
begin


declare [[trace_eqvt = false]]
(* declare [[trace_eqvt = true]] *)

lemma
  fixes B::"'a::pt"
  shows "p \<bullet> (B = C)"
apply(perm_simp)
oops

lemma
  fixes B::"bool"
  shows "p \<bullet> (B = C)"
apply(perm_simp)
oops

lemma
  fixes B::"bool"
  shows "p \<bullet> (A \<longrightarrow> B = C)"
apply (perm_simp)
oops

lemma
  shows "p \<bullet> (\<lambda>(x::'a::pt). A \<longrightarrow> (B::'a \<Rightarrow> bool) x = C) = foo"
apply(perm_simp)
oops

lemma
  shows "p \<bullet> (\<lambda>B::bool. A \<longrightarrow> (B = C)) = foo"
apply (perm_simp)
oops

lemma
  shows "p \<bullet> (\<lambda>x y. \<exists>z. x = z \<and> x = y \<longrightarrow> z \<noteq> x) = foo"
apply (perm_simp)
oops

lemma
  shows "p \<bullet> (\<lambda>f x. f (g (f x))) = foo"
apply (perm_simp)
oops

lemma
  fixes p q::"perm"
  and   x::"'a::pt"
  shows "p \<bullet> (q \<bullet> x) = foo"
apply(perm_simp)
oops

lemma
  fixes p q r::"perm"
  and   x::"'a::pt"
  shows "p \<bullet> (q \<bullet> r \<bullet> x) = foo"
apply(perm_simp)
oops

lemma
  fixes p r::"perm"
  shows "p \<bullet> (\<lambda>q::perm. q \<bullet> (r \<bullet> x)) = foo"
apply (perm_simp)
oops

lemma
  fixes C D::"bool"
  shows "B (p \<bullet> (C = D))"
apply(perm_simp)
oops

declare [[trace_eqvt = false]]

text \<open>there is no raw eqvt-rule for The\<close>
lemma "p \<bullet> (THE x. P x) = foo"
apply(perm_strict_simp exclude: The)
apply(perm_simp exclude: The)
oops

lemma
  fixes P :: "(('b \<Rightarrow> bool) \<Rightarrow> ('b::pt)) \<Rightarrow> ('a::pt)"
  shows "p \<bullet> (P The) = foo"
apply(perm_simp exclude: The)
oops

lemma
  fixes  P :: "('a::pt) \<Rightarrow> ('b::pt) \<Rightarrow> bool"
  shows "p \<bullet> (\<lambda>(a, b). P a b) = (\<lambda>(a, b). (p \<bullet> P) a b)"
apply(perm_simp)
oops

thm eqvts
thm eqvts_raw

ML \<open>Nominal_ThmDecls.is_eqvt @{context} @{term "supp"}\<close>


end
