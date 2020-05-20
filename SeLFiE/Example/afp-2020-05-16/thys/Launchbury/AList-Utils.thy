theory "AList-Utils"
imports Main "HOL-Library.AList"
begin
declare implies_True_equals [simp] False_implies_equals[simp]
text \<open>We want to have \<open>delete\<close> and \<open>update\<close> back in the namespace.\<close>

abbreviation delete where "delete \<equiv> AList.delete"
abbreviation update where "update \<equiv> AList.update"
abbreviation restrictA where "restrictA \<equiv> AList.restrict"
abbreviation clearjunk where "clearjunk \<equiv> AList.clearjunk"

lemmas restrict_eq = AList.restrict_eq
  and delete_eq = AList.delete_eq

lemma restrictA_append: "restrictA S (a@b) = restrictA S a @ restrictA S b"
  unfolding restrict_eq by (rule filter_append)

lemma length_restrictA_le: "length (restrictA S a) \<le> length a"
  by (metis length_filter_le restrict_eq)

subsubsection \<open>The domain of an associative list\<close>

definition domA
  where "domA h = fst ` set h"

lemma domA_append[simp]:"domA (a @ b) = domA a \<union> domA b"
  and [simp]:"domA ((v,e) # h) = insert v (domA h)"
  and [simp]:"domA (p # h) = insert (fst p) (domA h)"
  and [simp]:"domA [] = {}"
  by (auto simp add: domA_def)

lemma domA_from_set:
  "(x, e) \<in> set h \<Longrightarrow> x \<in> domA h"
by (induct h, auto)

lemma finite_domA[simp]:
  "finite (domA \<Gamma>)"
  by (auto simp add: domA_def)

lemma domA_delete[simp]:
  "domA (delete x \<Gamma>) = domA \<Gamma> - {x}"
  by (induct \<Gamma>) auto

lemma domA_restrictA[simp]:
  "domA (restrictA S \<Gamma>) = domA \<Gamma> \<inter> S"
  by (induct \<Gamma>) auto

lemma delete_not_domA[simp]:
  "x \<notin> domA \<Gamma> \<Longrightarrow>  delete x \<Gamma> = \<Gamma>"
  by (induct \<Gamma>) auto

lemma deleted_not_domA: "x \<notin> domA (delete x \<Gamma>)"
  by (induct \<Gamma>) auto

lemma dom_map_of_conv_domA:
  "dom (map_of \<Gamma>) = domA \<Gamma>"
  by (induct \<Gamma>) (auto simp add: dom_if)

lemma domA_map_of_Some_the:
  "x \<in> domA \<Gamma> \<Longrightarrow> map_of \<Gamma> x = Some (the (map_of \<Gamma> x))"
  by (induct \<Gamma>) (auto simp add: dom_if)

lemma domA_clearjunk[simp]: "domA (clearjunk \<Gamma>) = domA \<Gamma>"
  unfolding domA_def using dom_clearjunk.

lemma the_map_option_domA[simp]: "x \<in> domA \<Gamma> \<Longrightarrow> the (map_option f (map_of \<Gamma> x)) = f (the (map_of \<Gamma> x))"
  by (induction \<Gamma>) auto

lemma map_of_domAD: "map_of \<Gamma> x = Some e \<Longrightarrow> x \<in> domA \<Gamma>"
  using dom_map_of_conv_domA by fastforce

lemma restrictA_noop: "domA \<Gamma> \<subseteq> S \<Longrightarrow> restrictA S \<Gamma> = \<Gamma>"
  unfolding restrict_eq by (induction \<Gamma>) auto

lemma restrictA_cong:
  "(\<And>x. x \<in> domA m1 \<Longrightarrow> x \<in> V \<longleftrightarrow> x \<in> V') \<Longrightarrow> m1 = m2 \<Longrightarrow> restrictA V m1 = restrictA V' m2"
  unfolding restrict_eq by (induction m1 arbitrary: m2) auto

subsubsection \<open>Other lemmas about associative lists\<close>

lemma delete_set_none: "(map_of l)(x := None) = map_of (delete x l)"
proof (induct l)
  case Nil thus ?case by simp
  case (Cons l ls)
  from this[symmetric]
  show ?case
  by (cases "fst l = x") auto
qed

lemma list_size_delete[simp]: "size_list size (delete x l) < Suc (size_list size l)"
  by (induct l) auto

lemma delete_append[simp]: "delete x (l1 @ l2) = delete x l1 @ delete x l2"
  unfolding AList.delete_eq by simp

lemma map_of_delete_insert:
  assumes "map_of \<Gamma> x = Some e"
  shows "map_of ((x,e) # delete x \<Gamma>) = map_of \<Gamma>"
  using assms by (induct \<Gamma>) (auto split:prod.split)

lemma map_of_delete_iff[simp]: "map_of (delete x \<Gamma>) xa = Some e \<longleftrightarrow> (map_of \<Gamma> xa = Some e) \<and> xa \<noteq> x"
  by (metis delete_conv fun_upd_same map_of_delete option.distinct(1))

lemma map_add_domA[simp]: 
  "x \<in> domA \<Gamma> \<Longrightarrow> (map_of \<Delta> ++ map_of \<Gamma>) x = map_of \<Gamma> x"
  "x \<notin> domA \<Gamma> \<Longrightarrow> (map_of \<Delta> ++ map_of \<Gamma>) x = map_of \<Delta> x"
    apply (metis dom_map_of_conv_domA map_add_dom_app_simps(1))
    apply (metis dom_map_of_conv_domA map_add_dom_app_simps(3))
    done

lemma set_delete_subset: "set (delete k al) \<subseteq> set al"
  by (auto simp add: delete_eq)

lemma dom_delete_subset: "snd ` set (delete k al) \<subseteq> snd ` set al"
  by (auto simp add: delete_eq)

(*
lemma ran_map_cong[fundef_cong]:
  "\<lbrakk> list_all2 (\<lambda> x y. fst x = fst y \<and> f1 (fst x) (snd x) = f2 (fst y) (snd y)) m1 m2 \<rbrakk>
      \<Longrightarrow> map_ran f1 m1 = map_ran f2 m2"    
  by (induction rule: list_all2_induct) auto
*)
lemma map_ran_cong[fundef_cong]:
  "\<lbrakk> \<And> x . x \<in> set m1 \<Longrightarrow> f1 (fst x) (snd x) = f2 (fst x) (snd x) ; m1 = m2 \<rbrakk>
      \<Longrightarrow> map_ran f1 m1 = map_ran f2 m2"    
  by (induction m1 arbitrary: m2) auto

lemma domA_map_ran[simp]: "domA (map_ran f m) = domA m"
  unfolding domA_def by (rule dom_map_ran)

lemma map_ran_delete:
  "map_ran f (delete x \<Gamma>) = delete x (map_ran f \<Gamma>)"
  by (induction \<Gamma>)  auto

lemma map_ran_restrictA:
  "map_ran f (restrictA V \<Gamma>) = restrictA V (map_ran f \<Gamma>)"
  by (induction \<Gamma>)  auto

lemma map_ran_append:
  "map_ran f (\<Gamma>@\<Delta>) = map_ran f \<Gamma> @ map_ran f \<Delta>"
  by (induction \<Gamma>)  auto

subsubsection \<open>Syntax for map comprehensions\<close>

definition mapCollect :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> 'c set"
  where "mapCollect f m = {f k v | k v . m k = Some v}"

syntax
 "_MapCollect" :: "'c \<Rightarrow> pttrn => pttrn \<Rightarrow> 'a \<rightharpoonup> 'b => 'c set"    ("(1{_ |/_/\<mapsto>/_/\<in>/_/})")
translations
  "{e | k\<mapsto>v \<in> m}" == "CONST mapCollect (\<lambda>k v. e) m"

lemma mapCollect_empty[simp]: "{f k v | k \<mapsto> v \<in> Map.empty} = {}"
  unfolding mapCollect_def by simp

lemma mapCollect_const[simp]:
  "m \<noteq> Map.empty \<Longrightarrow> {e | k\<mapsto>v\<in>m} = {e}"
  unfolding mapCollect_def by auto

lemma mapCollect_cong[fundef_cong]:
  "(\<And> k v. m1 k = Some v \<Longrightarrow> f1 k v = f2 k v) \<Longrightarrow> m1 = m2 \<Longrightarrow> mapCollect f1 m1 = mapCollect f2 m2"
  unfolding mapCollect_def by force

lemma mapCollectE[elim!]:
  assumes "x \<in> {f k v | k \<mapsto> v \<in> m}"
  obtains k v where "m k = Some v" and "x = f k v"
  using assms by (auto simp add: mapCollect_def)

lemma mapCollectI[intro]:
  assumes  "m k = Some v"
  shows "f k v \<in> {f k v | k \<mapsto> v \<in> m}"
  using assms by (auto simp add: mapCollect_def)


lemma ball_mapCollect[simp]:
  "(\<forall> x \<in> {f k v | k \<mapsto> v \<in> m}. P x) \<longleftrightarrow> (\<forall> k v. m k = Some v \<longrightarrow> P (f k v))"
  by (auto simp add: mapCollect_def)

lemma image_mapCollect[simp]: 
  "g ` {f k v | k \<mapsto> v \<in> m} = { g (f k v) | k \<mapsto> v \<in> m}"
  by (auto simp add: mapCollect_def)

lemma mapCollect_map_upd[simp]:
  "mapCollect f (m(k\<mapsto>v)) = insert (f k v) (mapCollect f (m(k := None)))"
unfolding mapCollect_def by auto


definition mapCollectFilter :: "('a \<Rightarrow> 'b \<Rightarrow> (bool \<times> 'c)) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> 'c set"
  where "mapCollectFilter f m = {snd (f k v) | k v . m k = Some v \<and> fst (f k v)}"

syntax
 "_MapCollectFilter" :: "'c \<Rightarrow> pttrn \<Rightarrow> pttrn \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> bool \<Rightarrow> 'c set"    ("(1{_ |/_/\<mapsto>/_/\<in>/_/./ _})")
translations
  "{e | k\<mapsto>v \<in> m . P }" == "CONST mapCollectFilter (\<lambda>k v. (P,e)) m"

lemma mapCollectFilter_const_False[simp]:
  "{e | k\<mapsto>v \<in> m . False } = {}"
  unfolding mapCollect_def mapCollectFilter_def by simp

lemma mapCollectFilter_const_True[simp]:
  "{e | k\<mapsto>v \<in> m . True } = {e | k\<mapsto>v \<in> m}"
  unfolding mapCollect_def mapCollectFilter_def by simp



end
