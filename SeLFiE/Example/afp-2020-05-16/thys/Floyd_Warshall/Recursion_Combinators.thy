(* Authors: Lammich, Wimmer *)
theory Recursion_Combinators
  imports Refine_Imperative_HOL.IICF
begin

context
begin

private definition for_comb where
  "for_comb f a0 n = nfoldli [0..<n + 1] (\<lambda> x. True) (\<lambda> k a. (f a k)) a0"

fun for_rec :: "('a \<Rightarrow> nat \<Rightarrow> 'a nres) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a nres" where
  "for_rec f a 0 = f a 0" |
  "for_rec f a (Suc n) = for_rec f a n \<bind> (\<lambda> x. f x (Suc n))"

private lemma for_comb_for_rec: "for_comb f a n = for_rec f a n"
unfolding for_comb_def
proof (induction f a n rule: for_rec.induct)
  case 1 then show ?case by (auto simp: pw_eq_iff refine_pw_simps)
next
  case IH: (2 a n)
  then show ?case by (fastforce simp: nfoldli_append pw_eq_iff refine_pw_simps)
qed

private definition for_rec2' where
  "for_rec2' f a n i j =
    (if i = 0 then RETURN a else for_rec (\<lambda>a i. for_rec (\<lambda> a. f a i) a n) a (i - 1))
    \<bind> (\<lambda> a. for_rec (\<lambda> a. f a i) a j)"

fun for_rec2 :: "('a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a nres) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a nres" where
  "for_rec2 f a n 0 0 = f a 0 0" |
  "for_rec2 f a n (Suc i) 0 = for_rec2 f a n i n \<bind> (\<lambda> a. f a (Suc i) 0)" |
  "for_rec2 f a n i (Suc j) = for_rec2 f a n i j \<bind> (\<lambda> a. f a i (Suc j))"

private lemma for_rec2_for_rec2':
  "for_rec2 f a n i j = for_rec2' f a n i j"
unfolding for_rec2'_def
 apply (induction f a n i j rule: for_rec2.induct)
 apply simp_all
 subgoal for f a n i
  apply (cases i)
 by auto
done

fun for_rec3 :: "('a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a nres) \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a nres"
where
  "for_rec3 f m n 0       0       0        = f m 0 0 0" |
  "for_rec3 f m n (Suc k) 0       0        = for_rec3 f m n k n n \<bind> (\<lambda> a. f a (Suc k) 0 0)" |
  "for_rec3 f m n k       (Suc i) 0        = for_rec3 f m n k i n \<bind> (\<lambda> a. f a k (Suc i) 0)" |
  "for_rec3 f m n k       i       (Suc j)  = for_rec3 f m n k i j \<bind> (\<lambda> a. f a k i (Suc j))"

private definition for_rec3' where
  "for_rec3' f a n k i j =
    (if k = 0 then RETURN a else for_rec (\<lambda>a k. for_rec2' (\<lambda> a. f a k) a n n n) a (k - 1))
    \<bind> (\<lambda> a. for_rec2' (\<lambda> a. f a k) a n i j)"

private lemma for_rec3_for_rec3':
  "for_rec3 f a n k i j = for_rec3' f a n k i j"
unfolding for_rec3'_def
 apply (induction f a n k i j rule: for_rec3.induct)
 apply (simp_all add: for_rec2_for_rec2'[symmetric])
 subgoal for f a n k
  apply (cases k)
 by auto
done

private lemma for_rec2'_for_rec:
  "for_rec2' f a n n n =
    for_rec (\<lambda>a i. for_rec (\<lambda> a. f a i) a n) a n"
unfolding for_rec2'_def by (cases n) auto

private lemma for_rec3'_for_rec:
  "for_rec3' f a n n n n =
    for_rec (\<lambda> a k. for_rec (\<lambda>a i. for_rec (\<lambda> a. f a k i) a n) a n) a n"
unfolding for_rec3'_def for_rec2'_for_rec by (cases n) auto

theorem for_rec_eq:
  "for_rec f a n = nfoldli [0..<n + 1] (\<lambda>x. True) (\<lambda>k a. f a k) a"
using for_comb_for_rec[unfolded for_comb_def, symmetric] .

theorem for_rec2_eq:
  "for_rec2 f a n n n =
     nfoldli [0..<n + 1] (\<lambda>x. True)
           (\<lambda>i. nfoldli [0..<n + 1] (\<lambda>x. True) (\<lambda>j a. f a i j)) a"
using
  for_rec2'_for_rec[
    unfolded for_rec2_for_rec2'[symmetric], unfolded for_comb_for_rec[symmetric] for_comb_def
  ] .

theorem for_rec3_eq:
  "for_rec3 f a n n n n =
    nfoldli [0..<n + 1] (\<lambda>x. True)
     (\<lambda>k. nfoldli [0..<n + 1] (\<lambda>x. True)
           (\<lambda>i. nfoldli [0..<n + 1] (\<lambda>x. True) (\<lambda>j a. f a k i j)))
     a"
using
  for_rec3'_for_rec[
    unfolded for_rec3_for_rec3'[symmetric], unfolded for_comb_for_rec[symmetric] for_comb_def
  ] .

end

lemmas [intf_of_assn] = intf_of_assnI[where R= "is_mtx n" and 'a= "'b i_mtx" for n]

declare param_upt[sepref_import_param]


end
