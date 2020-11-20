(*  Title:      Containers/Lexicographic_Order.thy
    Author:     Andreas Lochbihler, KIT *)

theory Lexicographic_Order imports
  List_Fusion
  "HOL-Library.Char_ord"
begin

hide_const (open) List.lexordp

section \<open>List fusion for lexicographic order\<close>

context linorder begin

lemma lexordp_take_index_conv:
  "lexordp xs ys \<longleftrightarrow> 
   (length xs < length ys \<and> take (length xs) ys = xs) \<or>
   (\<exists>i < min (length xs) (length ys). take i xs = take i ys \<and> xs ! i < ys ! i)"
  (is "?lhs = ?rhs")
proof
  assume ?lhs thus ?rhs
    by induct (auto 4 3 del: disjCI intro: disjI2 exI[where x="Suc i" for i])
next
  assume ?rhs (is "?prefix \<or> ?less") thus ?lhs 
  proof
    assume "?prefix"
    hence "ys = xs @ hd (drop (length xs) ys) # tl (drop (length xs) ys)"
      by (metis append_Nil2 append_take_drop_id less_not_refl list.collapse)
    thus ?thesis unfolding lexordp_iff by blast
  next
    assume "?less"
    then obtain i where "i < min (length xs) (length ys)"
      and "take i xs = take i ys" and nth: "xs ! i < ys ! i" by blast
    hence "xs = take i xs @ xs ! i # drop (Suc i) xs" "ys = take i xs @ ys ! i # drop (Suc i) ys"
      by -(subst append_take_drop_id[symmetric, of _ i], simp_all add: Cons_nth_drop_Suc)
    with nth show ?thesis unfolding lexordp_iff by blast
  qed
qed

\<comment> \<open>lexord is extension of partial ordering List.lex\<close> 
lemma lexordp_lex: "(xs, ys) \<in> lex {(xs, ys). xs < ys} \<longleftrightarrow> lexordp xs ys \<and> length xs = length ys"
proof(induct xs arbitrary: ys)
  case Nil thus ?case by clarsimp
next
  case Cons thus ?case by(cases ys)(simp_all, safe, simp)
qed

end

subsection \<open>Setup for list fusion\<close>

context ord begin

definition lexord_fusion :: "('a, 's1) generator \<Rightarrow> ('a, 's2) generator \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> bool"
where [code del]: "lexord_fusion g1 g2 s1 s2 = lexordp (list.unfoldr g1 s1) (list.unfoldr g2 s2)"

definition lexord_eq_fusion :: "('a, 's1) generator \<Rightarrow> ('a, 's2) generator \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> bool"
where [code del]: "lexord_eq_fusion g1 g2 s1 s2 = lexordp_eq (list.unfoldr g1 s1) (list.unfoldr g2 s2)"

lemma lexord_fusion_code:
  "lexord_fusion g1 g2 s1 s2 \<longleftrightarrow>
  (if list.has_next g1 s1 then
     if list.has_next g2 s2 then
       let (x, s1') = list.next g1 s1;
           (y, s2') = list.next g2 s2
       in x < y \<or> \<not> y < x \<and> lexord_fusion g1 g2 s1' s2'
     else False
   else list.has_next g2 s2)"
unfolding lexord_fusion_def
by(subst (1 2) list.unfoldr.simps)(auto split: prod.split_asm)

lemma lexord_eq_fusion_code:
  "lexord_eq_fusion g1 g2 s1 s2 \<longleftrightarrow>
  (list.has_next g1 s1 \<longrightarrow>
   list.has_next g2 s2 \<and>
   (let (x, s1') = list.next g1 s1;
        (y, s2') = list.next g2 s2
    in x < y \<or> \<not> y < x \<and> lexord_eq_fusion g1 g2 s1' s2'))"
unfolding lexord_eq_fusion_def
by(subst (1 2) list.unfoldr.simps)(auto split: prod.split_asm)

end

lemmas [code] =
  lexord_fusion_code ord.lexord_fusion_code
  lexord_eq_fusion_code ord.lexord_eq_fusion_code

lemmas [symmetric, code_unfold] =
  lexord_fusion_def ord.lexord_fusion_def
  lexord_eq_fusion_def ord.lexord_eq_fusion_def

end
