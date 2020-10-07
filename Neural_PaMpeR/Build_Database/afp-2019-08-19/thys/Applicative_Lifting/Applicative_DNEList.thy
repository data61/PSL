(* Author: Andreas Lochbihler, ETH Zurich *)

section \<open>Distinct, non-empty list\<close>

theory Applicative_DNEList imports
  Applicative_List
  "HOL-Library.Dlist"
begin

lemma bind_eq_Nil_iff [simp]: "List.bind xs f = [] \<longleftrightarrow> (\<forall>x\<in>set xs. f x = [])"
by(simp add: List.bind_def)

lemma zip_eq_Nil_iff [simp]: "zip xs ys = [] \<longleftrightarrow> xs = [] \<or> ys = []"
by(cases xs ys rule: list.exhaust[case_product list.exhaust]) simp_all

lemma remdups_append1: "remdups (remdups xs @ ys) = remdups (xs @ ys)"
by(induction xs) simp_all

lemma remdups_append2: "remdups (xs @ remdups ys) = remdups (xs @ ys)"
by(induction xs) simp_all

lemma remdups_append1_drop: "set xs \<subseteq> set ys \<Longrightarrow> remdups (xs @ ys) = remdups ys"
by(induction xs) auto

lemma remdups_concat_map: "remdups (concat (map remdups xss)) = remdups (concat xss)"
by(induction xss)(simp_all add: remdups_append1, metis remdups_append2)

lemma remdups_concat_remdups: "remdups (concat (remdups xss)) = remdups (concat xss)"
apply(induction xss)
apply(auto simp add: remdups_append1_drop)
 apply(subst remdups_append1_drop; auto)
apply(metis remdups_append2)
done

lemma remdups_replicate: "remdups (replicate n x) = (if n = 0 then [] else [x])"
by(induction n) simp_all


typedef 'a dnelist = "{xs::'a list. distinct xs \<and> xs \<noteq> []}"
  morphisms list_of_dnelist Abs_dnelist
proof
  show "[x] \<in> ?dnelist" for x by simp
qed

setup_lifting type_definition_dnelist

lemma dnelist_subtype_dlist:
  "type_definition (\<lambda>x. Dlist (list_of_dnelist x)) (\<lambda>x. Abs_dnelist (list_of_dlist x)) {xs. xs \<noteq> Dlist.empty}"
apply unfold_locales
subgoal by(transfer; auto simp add: dlist_eq_iff)
subgoal by(simp add: distinct_remdups_id dnelist.list_of_dnelist[simplified] list_of_dnelist_inverse)
subgoal by(simp add: dlist_eq_iff Abs_dnelist_inverse)
done

lift_bnf 'a dnelist via dnelist_subtype_dlist for map: map by(simp_all add: dlist_eq_iff)
hide_const (open) map

context begin
qualified lemma map_def: "Applicative_DNEList.map = map_fun id (map_fun list_of_dnelist Abs_dnelist) (\<lambda>f xs. remdups (list.map f xs))"
unfolding map_def by(simp add: fun_eq_iff distinct_remdups_id list_of_dnelist[simplified])

qualified lemma map_transfer [transfer_rule]:
  "rel_fun (=) (rel_fun (pcr_dnelist (=)) (pcr_dnelist (=))) (\<lambda>f xs. remdups (map f xs)) Applicative_DNEList.map"
by(simp add: map_def rel_fun_def dnelist.pcr_cr_eq cr_dnelist_def list_of_dnelist[simplified] Abs_dnelist_inverse)

qualified lift_definition single :: "'a \<Rightarrow> 'a dnelist" is "\<lambda>x. [x]" by simp
qualified lift_definition insert :: "'a \<Rightarrow> 'a dnelist \<Rightarrow> 'a dnelist" is "\<lambda>x xs. if x \<in> set xs then xs else x # xs" by auto
qualified lift_definition append :: "'a dnelist \<Rightarrow> 'a dnelist \<Rightarrow> 'a dnelist" is "\<lambda>xs ys. remdups (xs @ ys)" by auto
qualified lift_definition bind :: "'a dnelist \<Rightarrow> ('a \<Rightarrow> 'b dnelist) \<Rightarrow> 'b dnelist" is "\<lambda>xs f. remdups (List.bind xs f)" by auto

abbreviation (input) pure_dnelist :: "'a \<Rightarrow> 'a dnelist"
where "pure_dnelist \<equiv> single"

end

lift_definition ap_dnelist :: "('a \<Rightarrow> 'b) dnelist \<Rightarrow> 'a dnelist \<Rightarrow> 'b dnelist"
is "\<lambda>f x. remdups (ap_list f x)"
by(auto simp add: ap_list_def)

adhoc_overloading Applicative.ap ap_dnelist

lemma ap_pure_list [simp]: "ap_list [f] xs = map f xs"
by(simp add: ap_list_def List.bind_def)

context includes applicative_syntax
begin

lemma ap_pure_dlist: "pure_dnelist f \<diamondop> x = Applicative_DNEList.map f x"
by transfer simp

applicative dnelist (K)
for pure: pure_dnelist
    ap: ap_dnelist
proof -
  show "pure_dnelist (\<lambda>x. x) \<diamondop> x = x" for x :: "'a dnelist"
    by transfer simp

  have *: "remdups (remdups (remdups ([\<lambda>g f x. g (f x)] \<diamondop> g) \<diamondop> f) \<diamondop> x) = remdups (g \<diamondop> remdups (f \<diamondop> x))"
    (is "?lhs = ?rhs") for g :: "('b \<Rightarrow> 'c) list" and f :: "('a \<Rightarrow> 'b) list" and x
  proof -
    have "?lhs = remdups (concat (map (\<lambda>f. map f x) (remdups (concat (map (\<lambda>x. map (\<lambda>f y. x (f y)) f) g)))))"
      unfolding ap_list_def List.bind_def
      by(subst (2) remdups_concat_remdups[symmetric])(simp add: o_def remdups_map_remdups remdups_concat_remdups)
    also have "\<dots> =  remdups (concat (map (\<lambda>f. map f x) (concat (map (\<lambda>x. map (\<lambda>f y. x (f y)) f) g))))"
      by(subst (1) remdups_concat_remdups[symmetric])(simp add: remdups_map_remdups remdups_concat_remdups)
    also have "\<dots> = remdups (concat (map remdups (map (\<lambda>g. map g (concat (map (\<lambda>f. map f x) f))) g)))"
      using list.pure_B_conv[of g f x] unfolding remdups_concat_map
      by(simp add: ap_list_def List.bind_def o_def)
    also have "\<dots> = ?rhs" unfolding ap_list_def List.bind_def
      by(subst (2) remdups_concat_map[symmetric])(simp add: o_def remdups_map_remdups)
    finally show ?thesis .
  qed
  show "pure_dnelist (\<lambda>g f x. g (f x)) \<diamondop> g \<diamondop> f \<diamondop> x = g \<diamondop> (f \<diamondop> x)"
    for g :: "('b \<Rightarrow> 'c) dnelist" and f :: "('a \<Rightarrow> 'b) dnelist" and x
    by transfer(rule *)
  show "pure_dnelist f \<diamondop> pure_dnelist x = pure_dnelist (f x)" for f :: "'a \<Rightarrow> 'b" and x
    by transfer simp
  show "f \<diamondop> pure_dnelist x = pure_dnelist (\<lambda>f. f x) \<diamondop> f" for f :: "('a \<Rightarrow> 'b) dnelist" and x
    by transfer(simp add: list.interchange)

  have *: "remdups (remdups ([\<lambda>x y. x] \<diamondop> x) \<diamondop> y) = x" if x: "distinct x" and y: "distinct y" "y \<noteq> []"
    for x :: "'b list" and y :: "'a list"
  proof -
    have "remdups (map (\<lambda>(x :: 'b) (y :: 'a). x) x) = map (\<lambda>(x :: 'b) (y :: 'a). x) x"
      using that by(simp add: distinct_map inj_on_def fun_eq_iff)
    hence "remdups (remdups ([\<lambda>x y. x] \<diamondop> x) \<diamondop> y) = remdups (concat (map (\<lambda>f. map f y) (map (\<lambda>x y. x) x)))"
      by(simp add: ap_list_def List.bind_def del: remdups_id_iff_distinct) 
    also have "\<dots> = x" using that
      by(simp add: o_def map_replicate_const)(subst remdups_concat_map[symmetric], simp add: o_def remdups_replicate)
    finally show ?thesis .
  qed
  show "pure_dnelist (\<lambda>x y. x) \<diamondop> x \<diamondop> y = x" 
    for x :: "'b dnelist" and y :: "'a dnelist"
    by transfer(rule *; simp)
qed

text \<open>@{typ "_ dnelist"} does not have combinator C, so it cannot have W either.\<close>

context begin 
private lift_definition x :: "int dnelist" is "[2,3]" by simp
private lift_definition y :: "int dnelist" is "[5,7]" by simp
private lemma "pure_dnelist (\<lambda>f x y. f y x) \<diamondop> pure_dnelist ((*)) \<diamondop> x \<diamondop> y \<noteq> pure_dnelist ((*)) \<diamondop> y \<diamondop> x"
  by transfer(simp add: ap_list_def fun_eq_iff)
end

end

end
