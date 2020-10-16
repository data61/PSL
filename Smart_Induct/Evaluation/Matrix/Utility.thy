(*  Title:       Executable Matrix Operations on Matrices of Arbitrary Dimensions
    Author:      Christian Sternagel <christian.sternagel@uibk.ac.at>
                 René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann
    License:     LGPL
*)

(*
Copyright 2010 Christian Sternagel, René Thiemann

This file is part of IsaFoR/CeTA.

IsaFoR/CeTA is free software: you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

IsaFoR/CeTA is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along
with IsaFoR/CeTA. If not, see <http://www.gnu.org/licenses/>.
*)

section \<open>Utility Functions and Lemmas\<close>

theory Utility
imports Main
begin

subsection \<open>Miscellaneous\<close>

lemma ballI2[Pure.intro]:
  assumes "\<And>x y. (x, y) \<in> A \<Longrightarrow> P x y"
  shows "\<forall>(x, y)\<in>A. P x y"
  using assms by auto


lemma infinite_imp_elem: "\<not> finite A \<Longrightarrow> \<exists> x. x \<in> A"
  by (cases "A = {}", auto)

lemma infinite_imp_many_elems:
  "infinite A \<Longrightarrow> \<exists> xs. set xs \<subseteq> A \<and> length xs = n \<and> distinct xs"
proof (induct n arbitrary: A)
  case (Suc n)
  from infinite_imp_elem[OF Suc(2)] obtain x where x: "x \<in> A" by auto
  from Suc(2) have "infinite (A - {x})" by auto
  from Suc(1)[OF this] obtain xs where "set xs \<subseteq> A - {x}" and "length xs = n" and "distinct xs" by auto
  with x show ?case by (intro exI[of _ "x # xs"], auto)
qed auto


lemma inf_pigeonhole_principle:
  assumes "\<forall>k::nat. \<exists>i<n::nat. f k i"
  shows "\<exists>i<n. \<forall>k. \<exists>k'\<ge>k. f k' i"
proof -
  have nfin: "~ finite (UNIV :: nat set)" by auto
  have fin: "finite ({i. i < n})" by auto
  from pigeonhole_infinite_rel[OF nfin fin] assms
  obtain i where i: "i < n" and nfin: "\<not> finite {a. f a i}" by auto
  show ?thesis 
  proof (intro exI conjI, rule i, intro allI)
    fix k
    have "finite {a. f a i \<and> a < k}" by auto
    with nfin have "\<not> finite ({a. f a i} - {a. f a i \<and> a < k})" by auto
    from infinite_imp_elem[OF this]
    obtain a where "f a i" and "a \<ge> k" by auto
    thus "\<exists> k' \<ge> k. f k' i" by force
  qed
qed

lemma map_upt_Suc: "map f [0 ..< Suc n] = f 0 # map (\<lambda> i. f (Suc i)) [0 ..< n]"
  by (induct n arbitrary: f, auto)

lemma map_upt_add: "map f [0 ..< n + m] = map f [0 ..< n] @ map (\<lambda> i. f (i + n)) [0 ..< m]"
proof (induct n arbitrary: f)
  case (Suc n f)
  have "map f [0 ..< Suc n + m] = map f [0 ..< Suc (n+m)]" by simp
  also have "\<dots> = f 0 # map (\<lambda> i. f (Suc i)) [0 ..< n + m]" unfolding map_upt_Suc ..
  finally show ?case unfolding Suc map_upt_Suc by simp
qed simp

lemma map_upt_split: assumes i: "i < n"
  shows "map f [0 ..< n] = map f [0 ..< i] @ f i # map (\<lambda> j. f (j + Suc i)) [0 ..< n - Suc i]"
proof -
  from i have "n = i + Suc 0 + (n - Suc i)" by arith
  hence id: "[0 ..< n] = [0 ..< i + Suc 0 + (n - Suc i)]" by simp
  show ?thesis unfolding id
    unfolding map_upt_add by auto
qed

lemma all_Suc_conv:
  "(\<forall>i<Suc n. P i) \<longleftrightarrow> P 0 \<and> (\<forall>i<n. P (Suc i))" (is "?l = ?r")
proof
  assume ?l thus ?r by auto
next
  assume ?r show ?l
  proof (intro allI impI)
    fix i
    assume "i < Suc n"
    with \<open>?r\<close> show "P i" by (cases i, auto)
  qed
qed

lemma ex_Suc_conv:
  "(\<exists>i<Suc n. P i) \<longleftrightarrow> P 0 \<or> (\<exists>i<n. P (Suc i))" (is "?l = ?r")
  using all_Suc_conv[of n "\<lambda>i. \<not> P i"] by blast

fun sorted_list_subset :: "'a :: linorder list \<Rightarrow> 'a list \<Rightarrow> 'a option" where
  "sorted_list_subset (a # as) (b # bs) = 
    (if a = b then sorted_list_subset as (b # bs)
     else if a > b then sorted_list_subset (a # as) bs
     else Some a)"
| "sorted_list_subset [] _ = None"
| "sorted_list_subset (a # _) [] = Some a"
   
lemma sorted_list_subset:
  assumes "sorted as" and "sorted bs"
  shows "(sorted_list_subset as bs = None) = (set as \<subseteq> set bs)"
using assms 
proof (induct rule: sorted_list_subset.induct)
  case (2 bs)
  thus ?case by auto
next
  case (3 a as)
  thus ?case by auto
next
  case (1 a as b bs)
  from 1(3) have sas: "sorted as" and a: "\<And> a'. a' \<in> set as \<Longrightarrow> a \<le> a'" by (auto)
  from 1(4) have sbs: "sorted bs" and b: "\<And> b'. b' \<in> set bs \<Longrightarrow> b \<le> b'" by (auto)
  show ?case
  proof (cases "a = b")
    case True
    from 1(1)[OF this sas 1(4)] True show ?thesis by auto
  next
    case False note oFalse = this
    show ?thesis 
    proof (cases "a > b")
      case True
      with a b have "b \<notin> set as" by force
      with 1(2)[OF False True 1(3) sbs] False True show ?thesis by auto
    next
      case False
      with oFalse have "a < b" by auto
      with a b have "a \<notin> set bs" by force
      with oFalse False show ?thesis by auto
    qed
  qed
qed

lemma zip_nth_conv: "length xs = length ys \<Longrightarrow> zip xs ys = map (\<lambda> i. (xs ! i, ys ! i)) [0 ..< length ys]"
proof (induct xs arbitrary: ys, simp)
  case (Cons x xs)
  then obtain y yys where ys: "ys = y # yys" by (cases ys, auto)
  with Cons have len: "length xs = length yys" by simp
  show ?case unfolding ys 
    by (simp del: upt_Suc add: map_upt_Suc, unfold Cons(1)[OF len], simp) 
qed

lemma nth_map_conv:
  assumes "length xs = length ys"
    and "\<forall>i<length xs. f (xs ! i) = g (ys ! i)"
  shows "map f xs = map g ys"
using assms
proof (induct xs arbitrary: ys)
  case (Cons x xs) thus ?case
  proof (induct ys)
    case (Cons y ys)
    have "\<forall>i<length xs. f (xs ! i) = g (ys ! i)"
    proof (intro allI impI)
      fix i assume "i < length xs" thus "f (xs ! i) = g (ys ! i)" using Cons(4) by force
    qed
    with Cons show ?case by auto
  qed simp
qed simp

lemma sum_list_0: "\<lbrakk>\<And> x. x \<in> set xs \<Longrightarrow> x = 0\<rbrakk> \<Longrightarrow> sum_list xs = 0"
  by (induct xs, auto)

lemma foldr_foldr_concat: "foldr (foldr f) m a = foldr f (concat m) a"
proof (induct m arbitrary: a)
  case Nil show ?case by simp
next
  case (Cons v m a)
  show ?case
    unfolding concat.simps foldr_Cons o_def Cons
    unfolding foldr_append by simp
qed

lemma sum_list_double_concat: 
  fixes f :: "'b \<Rightarrow> 'c \<Rightarrow> 'a :: comm_monoid_add" and g as bs
  shows "sum_list (concat (map (\<lambda> i. map (\<lambda> j. f i j + g i j) as) bs))
      = sum_list (concat (map (\<lambda> i. map (\<lambda> j. f i j) as) bs)) + 
        sum_list (concat (map (\<lambda> i. map (\<lambda> j. g i j) as) bs))"
proof (induct bs)
  case Nil thus ?case by simp
next
  case (Cons b bs)
  have id: "(\<Sum>j\<leftarrow>as. f b j + g b j) = sum_list (map (f b) as) + sum_list (map (g b) as)"
    by (induct as, auto simp: ac_simps)
  show ?case unfolding list.map concat.simps sum_list_append
    unfolding Cons
    unfolding id 
    by (simp add: ac_simps)
qed

fun max_list :: "nat list \<Rightarrow> nat" where
  "max_list [] = 0"
| "max_list (x # xs) = max x (max_list xs)"

lemma max_list: "x \<in> set xs \<Longrightarrow> x \<le> max_list xs"
  by (induct xs) auto
  
lemma max_list_mem: "xs \<noteq> [] \<Longrightarrow> max_list xs \<in> set xs"
proof (induct xs)
  case (Cons x xs)
  show ?case
  proof (cases "x \<ge> max_list xs")
    case True
    thus ?thesis by auto
  next
    case False
    hence max: "max_list xs > x" by auto
    hence nil: "xs \<noteq> []" by (cases xs, auto)
    from max have max: "max x (max_list xs) = max_list xs" by auto
    from Cons(1)[OF nil] max show ?thesis by auto
  qed
qed simp

lemma max_list_set: "max_list xs = (if set xs = {} then 0 else (THE x. x \<in> set xs \<and> (\<forall> y \<in> set xs. y \<le> x)))"
proof (cases "xs = []")
  case True thus ?thesis by simp
next
  case False
  note p = max_list_mem[OF this] max_list[of _ xs] 
  from False have id: "(set xs = {}) = False" by simp
  show ?thesis unfolding id if_False
  proof (rule the_equality[symmetric], intro conjI ballI, rule p, rule p)
    fix x 
    assume "x \<in> set xs \<and> (\<forall> y \<in> set xs. y \<le> x)"
    hence mem: "x \<in> set xs" and le: "\<And> y. y \<in> set xs \<Longrightarrow> y \<le> x" by auto
    from max_list[OF mem] le[OF max_list_mem[OF False]] 
    show "x = max_list xs" by simp
  qed
qed
      
lemma max_list_eq_set: "set xs = set ys \<Longrightarrow> max_list xs = max_list ys"
  unfolding max_list_set by simp

lemma all_less_two: "(\<forall> i < Suc (Suc 0). P i) = (P 0 \<and> P (Suc 0))" (is "?l = ?r")
proof
  assume ?r
  show ?l
  proof(intro allI impI)
    fix i
    assume "i < Suc (Suc 0)"
    hence "i = 0 \<or> i = Suc 0" by auto
    with \<open>?r\<close> show "P i" by auto
  qed
qed auto

text \<open>Induction over a finite set of natural numbers.\<close>
lemma bound_nat_induct[consumes 1]:
  assumes "n \<in> {l..u}" and "P l" and "\<And>n. \<lbrakk>P n; n \<in> {l..<u}\<rbrakk> \<Longrightarrow> P (Suc n)"
  shows "P n"
using assms
proof (induct n)
 case (Suc n) thus ?case by (cases "Suc n = l") auto
qed simp

end
