section\<open>Preliminaries\<close>
theory Preliminaries
imports "HOL-Cardinals.Cardinals"
        "HOL-Library.Countable_Set_Type"
begin


subsection \<open>Miscelanea\<close>

text\<open>A fixed countable universe for interpreting countable models:\<close>

datatype univ = UU nat

lemma infinite_univ[simp]: "infinite (UNIV :: univ set)"
unfolding infinite_iff_card_of_nat card_of_ordLeq[symmetric]
unfolding inj_on_def by auto

lemma countable_univ[simp]: "countable (UNIV :: univ set)"
unfolding countable_card_of_nat apply(rule surj_imp_ordLeq[of _ UU])
by (metis subset_UNIV surj_def univ.exhaust)


text\<open>Picking an element from a nonempty set (Hilbert choice for sets):\<close>

definition "pick X \<equiv> SOME x. x \<in> X"

lemma pick[simp]: "x \<in> X \<Longrightarrow> pick X \<in> X"
unfolding pick_def by (metis someI_ex)

lemma pick_NE[simp]: "X \<noteq> {} \<Longrightarrow> pick X \<in> X" by auto

definition sappend (infix "@@" 60) where
"Al @@ Bl = {al @ bl | al bl. al \<in> Al \<and> bl \<in> Bl}"

lemma sappend_NE[simp]: "A @@ B \<noteq> {} \<longleftrightarrow> A \<noteq> {} \<and> B \<noteq> {}"
unfolding sappend_def by auto

abbreviation fst3 :: "'a * 'b * 'c \<Rightarrow> 'a" where "fst3 abc \<equiv> fst abc"
abbreviation "snd3 abc \<equiv> fst (snd abc)"
abbreviation "trd3 abc \<equiv> snd (snd abc)"

hide_const int

abbreviation "any \<equiv> undefined"

text\<open>Non-emptyness of predicates:\<close>

abbreviation (input) "NE \<phi> \<equiv> \<exists> a. \<phi> a"

lemma NE_NE: "NE NE"
apply(rule exI[of _ "\<lambda> a. True"]) by auto

lemma length_Suc_0:
"length al = Suc 0 \<longleftrightarrow> (\<exists> a. al = [a])"
by (metis (lifting) length_0_conv length_Suc_conv)


subsection\<open>List combinators\<close>

lemmas list_all2_length = list_all2_conv_all_nth
lemmas list_eq_iff = list_eq_iff_nth_eq
lemmas list_all_iff
lemmas list_all_length

definition "singl a = [a]"

lemma length_singl[simp]: "length (singl a) = Suc 0"
unfolding singl_def by simp

lemma hd_singl[simp]: "hd (singl a) = a"
unfolding singl_def by simp

lemma hd_o_singl[simp]: "hd o singl = id"
unfolding comp_def fun_eq_iff by simp

lemma singl_hd[simp]: "length al = Suc 0 \<Longrightarrow> singl (hd al) = al"
unfolding singl_def by (cases al, auto)

lemma singl_inj[simp]: "singl a = singl b \<longleftrightarrow> a = b"
unfolding singl_def by simp

(* The list of a finite set: *)
definition "list A \<equiv> SOME al. distinct al \<and> set al = A"

lemma distinct_set_list:
"finite A \<Longrightarrow> distinct (list A) \<and> set (list A) = A"
unfolding list_def apply(rule someI_ex) using finite_distinct_list by auto

lemmas distinct_list[simp] = distinct_set_list[THEN conjunct1]
lemmas set_list[simp] = distinct_set_list[THEN conjunct2]

lemma set_list_set[simp]: "set (list (set xl)) = set xl" by auto

lemma length_list[simp]: "finite A \<Longrightarrow> length (list A) = card A"
by (metis distinct_card distinct_set_list)

lemma list_all_mp[elim]:
assumes "list_all (\<lambda> a. \<phi> a \<longrightarrow> \<psi> a) al" and "list_all \<phi> al"
shows "list_all \<psi> al"
using assms unfolding list_all_iff by auto

lemma list_all_map:
"list_all \<phi> (map f al) = list_all (\<phi> o f) al"
by (metis (no_types) length_map list_all_length nth_map o_def)

lemma list_Emp[simp]: "list {} = []"
by (metis set_empty2 set_list_set)

lemma distinct_set_eq_Singl[simp]: "distinct al \<Longrightarrow> set al = {a} \<longleftrightarrow> al = [a]"
apply(cases al, simp)
by (metis (lifting) List.set_simps distinct.simps
           distinct_singleton empty_not_insert insert_eq_iff set_empty2)

lemma list_Singl[simp]: "list {b} = [b]"
unfolding list_def apply(rule some_equality) by auto

lemma list_insert:
assumes A: "finite A" and b: "b \<notin> A"
shows
"\<exists> al1 al2.
   A = set (al1 @ al2) \<and> distinct (al1 @ [b] @ al2) \<and>
   list (insert b A) = al1 @ [b] @ al2"
proof-
  have "b \<in> set (list (insert b A))" using A by auto
  then obtain al1 al2 where 0: "list (insert b A) = al1 @ [b] @ al2"
  by (metis append_Cons eq_Nil_appendI split_list_last)
  hence 1: "distinct (al1 @ [b] @ al2)" using A
  by (metis distinct_set_list finite_insert)
  hence "b \<notin> set (al1 @ al2)" by simp
  moreover have "insert b A = insert b (set (al1 @ al2))"
  using 0 set_list[OF finite.insertI[OF A, of b]] by auto
  ultimately have "A = set (al1 @ al2)" using b by auto
  thus ?thesis using 0 1 by auto
qed

lemma list_all_list[simp]:
assumes "finite A" shows "list_all \<phi> (list A) \<longleftrightarrow> (\<forall> a \<in> A. \<phi> a)"
using assms unfolding list_all_iff by simp

lemma list_ex_list[simp]:
"finite A \<Longrightarrow> list_ex \<phi> (list A) = (\<exists>a\<in>A. \<phi> a)"
unfolding list_ex_iff by simp

text\<open>list update:\<close>

fun lupd where
"lupd Nil Nil F = F"
|
"lupd (a # al) (b # bl) F = lupd al bl (F(a := b))"
|
"lupd _ _ F = any"

lemma set_lupd:
assumes "a \<in> set al \<or> F1 a = F2 a"
shows "lupd al bl F1 a = lupd al bl F2 a"
using assms apply(induct arbitrary: F1 F2 rule: list_induct2') by auto

lemma lupd_map:
assumes "length al = length bl" and "a1 \<in> set al \<or> G a1 = F (H a1)"
shows "lupd al (map F bl) G a1 = F (lupd al bl H a1)"
using assms apply (induct arbitrary: F G H rule: list_induct2) by auto

lemma nth_map2[simp]:
assumes "length bl = length al" and "i < length al"
shows "(map2 f al bl) ! i = f (al!i) (bl!i)"
using assms by auto

lemma list_all2_Nil_iff:
assumes "list_all2 R xs ys"
shows "xs = [] \<longleftrightarrow> ys = []"
using assms by (cases xs, cases ys) auto

lemma list_all2_NilL[simp]:
"list_all2 R [] ys \<longleftrightarrow> ys = []"
using list_all2_Nil_iff by auto

lemma list_all2_NilR[simp]:
"list_all2 R xs [] \<longleftrightarrow> xs = []"
using list_all2_Nil_iff by auto

lemma list_all2_ConsL:
assumes "list_all2 R (x # xs') ys"
shows "\<exists> y ys'. ys = y # ys' \<and> R x y \<and> list_all2 R xs' ys'"
using assms by(cases ys) auto

lemma list_all2_elimL[elim, consumes 2, case_names Cons]:
assumes xs: "xs = x # xs'" and h: "list_all2 R xs ys"
and Cons: "\<And> y ys'. \<lbrakk>ys = y # ys'; R x y; list_all2 R xs' ys'\<rbrakk> \<Longrightarrow> phi"
shows phi
using list_all2_ConsL assms by metis

lemma list_all2_elimL2[elim, consumes 1, case_names Cons]:
assumes h: "list_all2 R (x # xs') ys"
and Cons: "\<And> y ys'. \<lbrakk>ys = y # ys'; R x y; list_all2 R xs' ys'\<rbrakk> \<Longrightarrow> phi"
shows phi
using list_all2_ConsL assms by metis

lemma list_all2_ConsR:
assumes "list_all2 R xs (y # ys')"
shows "\<exists> x xs'. xs = x # xs' \<and> R x y \<and> list_all2 R xs' ys'"
using assms by(cases xs) auto

lemma list_all2_elimR[elim, consumes 2, case_names Cons]:
assumes ys: "ys = y # ys'" and h: "list_all2 R xs ys"
and Cons: "\<And> x xs'. \<lbrakk>xs = x # xs'; R x y; list_all2 R xs' ys'\<rbrakk> \<Longrightarrow> phi"
shows phi
using list_all2_ConsR assms by metis

lemma list_all2_elimR2[elim, consumes 1, case_names Cons]:
assumes h: "list_all2 R xs (y # ys')"
and Cons: "\<And> x xs'. \<lbrakk>xs = x # xs'; R x y; list_all2 R xs' ys'\<rbrakk> \<Longrightarrow> phi"
shows phi
using list_all2_ConsR assms by metis

lemma ex_list_all2:
assumes "\<And>x. x \<in> set xs \<Longrightarrow> \<exists>y. f x y"
shows "\<exists> ys. list_all2 f xs ys"
using assms apply(induct xs)
apply fastforce
by (metis set_simps insertCI list_all2_Cons)

lemma list_all2_cong[fundef_cong]:
assumes "xs1 = ys1" and "xs2 = ys2"
and "\<And> i . i < length xs2 \<Longrightarrow> R (xs1!i) (xs2!i) \<longleftrightarrow> R' (ys1!i) (ys2!i)"
shows "list_all2 R xs1 xs2 \<longleftrightarrow> list_all2 R' ys1 ys2"
by (metis assms list_all2_length)

lemma list_all2_o: "list_all2 (P o f) al bl = list_all2 P (map f al) bl"
unfolding list_all2_map1 comp_def ..

lemma set_size_list:
assumes "x \<in> set xs"
shows "f x \<le> size_list f xs"
by (metis assms size_list_estimation' order_eq_refl)

lemma nth_size_list:
assumes "i < length xs"
shows "f (xs!i) \<le> size_list f xs"
by (metis assms nth_mem set_size_list)

lemma list_all2_list_all[simp]:
"list_all2 (\<lambda> x. f) xs ys \<longleftrightarrow>
 length xs = length ys \<and> list_all f ys"
by (metis list_all2_length list_all_length)

lemma list_all2_list_allR[simp]:
"list_all2 (\<lambda> x y. f x) xs ys \<longleftrightarrow>
 length xs = length ys \<and> list_all f xs"
by (metis (lifting) list_all2_length list_all_length)

lemma list_all2_list_all_2[simp]:
"list_all2 f xs xs \<longleftrightarrow> list_all (\<lambda> x. f x x) xs"
by (auto simp add: list_all2_iff list_all_iff zip_same)

lemma list_all2_map_map:
"list_all2 \<phi> (map f Tl) (map g Tl) =
 list_all (\<lambda>T. \<phi> (f T) (g T)) Tl"
unfolding list_all2_map1 list_all2_map2 list_all2_list_all_2 ..

lemma length_map2[simp]:
assumes "length ys = length xs"
shows "length (map2 f xs ys) = length xs"
using assms by auto

lemma listAll2_map2I[intro?]:
assumes "length xs = length ys"
and "\<And> i. i < length xs \<Longrightarrow> R (xs!i) (f (xs!i) (ys!i))"
shows "list_all2 R xs (map2 f xs ys)"
apply(rule list_all2I) using assms unfolding set_zip by auto

(*
lemma listAll2_map2I[intro?]:
assumes "length xs = length ys" and "\<And> x y. R x (f x y)"
shows "list_all2 R xs (map2 f xs ys)"
apply(rule list_all2I) using assms unfolding set_zip map2_def by auto
*)

lemma set_incl_pred:
"A \<le> B \<longleftrightarrow> (\<forall> a. A a \<longrightarrow> B a)"
by (metis predicate1D predicate1I)

lemma set_incl_pred2:
"A \<le> B \<longleftrightarrow> (\<forall> a1 a2. A a1 a2 \<longrightarrow> B a1 a2)"
by (metis predicate2I rev_predicate2D)

lemma set_incl_pred3:
"A \<le> B \<longleftrightarrow> (\<forall> a1 a2 a3. A a1 a2 a3 \<longrightarrow> B a1 a2 a3)" (is "_ \<longleftrightarrow> ?R")
proof-
  have "A \<le> B \<longleftrightarrow> (\<forall> a1. A a1 \<le> B a1)" by (metis le_funD le_funI)
  also have "... \<longleftrightarrow> ?R" apply(rule iff_allI)
  unfolding set_incl_pred2 ..
  finally show ?thesis .
qed

lemma set_incl_pred4:
"A \<le> B \<longleftrightarrow> (\<forall> a1 a2 a3 a4. A a1 a2 a3 a4 \<longrightarrow> B a1 a2 a3 a4)" (is "_ \<longleftrightarrow> ?R")
proof-
  have "A \<le> B \<longleftrightarrow> (\<forall> a1. A a1 \<le> B a1)" by (metis le_funD le_funI)
  also have "... \<longleftrightarrow> ?R" apply(rule iff_allI)
  unfolding set_incl_pred3 ..
  finally show ?thesis .
qed

lemma list_all_mono:
assumes "phi \<le> chi"
shows "list_all phi \<le> list_all chi"
using assms unfolding set_incl_pred list_all_iff by auto

lemma list_all2_mono:
assumes "phi \<le> chi"
shows "list_all2 phi \<le> list_all2 chi"
using assms by (metis (full_types) list_all2_mono set_incl_pred2)


subsection\<open>Variables\<close>

text\<open>The type of variables:\<close>

datatype var = Variable nat

lemma card_of_var: "|UNIV::var set| =o natLeq"
proof-
  have "|UNIV::var set| =o |UNIV::nat set|"
  apply(rule ordIso_symmetric,rule card_of_ordIsoI)
  unfolding bij_betw_def inj_on_def surj_def using var.exhaust by auto
  also have "|UNIV::nat set| =o natLeq" by(rule card_of_nat)
  finally show ?thesis .
qed

lemma infinite_var[simp]: "infinite (UNIV :: var set)"
using card_of_var by (rule ordIso_natLeq_infinite1)

lemma countable_var: "countable (UNIV :: var set)"
proof-
  have 0: "(UNIV :: var set) \<noteq> {}" by simp
  show ?thesis unfolding countable_card_of_nat unfolding card_of_ordLeq2[symmetric, OF 0]
  apply(rule exI[of _ Variable]) unfolding image_def apply auto by (case_tac x, auto)
qed


(* FIXME: Move into Countable_Set *)
lemma countable_infinite:
assumes A: "countable A" and B: "infinite B"
shows "|A| \<le>o |B|"
proof-
  have "|A| \<le>o natLeq" using A unfolding countable_card_le_natLeq .
  also have "natLeq \<le>o |B|" by (metis B infinite_iff_natLeq_ordLeq)
  finally show ?thesis .
qed

(* Partitioning V in two infinite disjoint sets *)
definition "part12_pred V V1_V2 \<equiv>
 V = fst V1_V2 \<union> snd V1_V2 \<and> fst V1_V2 \<inter> snd V1_V2 = {} \<and>
 infinite (fst V1_V2) \<and> infinite (snd V1_V2)"

definition "part12 V \<equiv> SOME V1_V2. part12_pred V V1_V2"
definition "part1 = fst o part12"  definition "part2 = snd o part12"

lemma part12_pred:
assumes "infinite (V::'a set)"  shows "\<exists> V1_V2. part12_pred V V1_V2"
proof-
  obtain f :: "nat \<Rightarrow> 'a" where f: "inj f" and r: "range f \<subseteq> V"
  using assms by (metis infinite_iff_countable_subset)
  let ?u = "\<lambda> k::nat. 2 * k"  let ?v = "\<lambda> k::nat. Suc (2 * k)"
  let ?A = "?u ` UNIV"  let ?B = "?v ` UNIV"
  have 0: "inj ?u \<and> inj ?v" unfolding inj_on_def by auto
  hence 1: "infinite ?A \<and> infinite ?B" using finite_imageD by auto
  let ?V1 = "f ` ?A"  let ?V2 = "V - ?V1"
  have "V = ?V1 \<union> ?V2 \<and> ?V1 \<inter> ?V2 = {}" using r by blast
  moreover have "infinite ?V1" using 1 f
  by (metis finite_imageD subset_inj_on top_greatest)
  moreover
  {have "infinite (f ` ?B)" using 1 f
   by (metis finite_imageD subset_inj_on top_greatest)
   moreover have "f ` ?B \<subseteq> ?V2" using r f by (auto simp: inj_eq) arith
   ultimately have "infinite ?V2" by (metis infinite_super)
  }
  ultimately show ?thesis unfolding part12_pred_def
  by (intro exI[of _ "(?V1,?V2)"]) auto
qed

lemma part12: assumes "infinite V"  shows "part12_pred V (part12 V)"
using part12_pred[OF assms] unfolding part12_def by(rule someI_ex)

lemma part1_Un_part2: "infinite V \<Longrightarrow> part1 V \<union> part2 V = V"
using part12 unfolding part1_def part2_def part12_pred_def by auto

lemma part1_Int_part2: "infinite V \<Longrightarrow> part1 V \<inter> part2 V = {}"
using part12 unfolding part1_def part2_def part12_pred_def by auto

lemma infinite_part1: "infinite V \<Longrightarrow> infinite (part1 V)"
using part12 unfolding part1_def part12_pred_def by auto

lemma part1_su: "infinite V \<Longrightarrow> part1 V \<subseteq> V"
using part1_Un_part2 by auto

lemma infinite_part2: "infinite V \<Longrightarrow> infinite (part2 V)"
using part12 unfolding part2_def part12_pred_def by auto

lemma part2_su: "infinite V \<Longrightarrow> part2 V \<subseteq> V"
using part1_Un_part2 by auto



end
