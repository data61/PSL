section \<open>\isaheader{The type of associative lists}\<close>
theory Assoc_List 
  imports 
  "HOL-Library.AList" 
  "../Iterator/SetIteratorOperations"
begin

subsection \<open>Type \<open>('a, 'b) assoc_list\<close>\<close>

typedef ('k, 'v) assoc_list = "{xs :: ('k \<times> 'v) list. distinct (map fst xs)}"
morphisms impl_of Assoc_List
by(rule exI[where x="[]"]) simp

lemma assoc_list_ext: "impl_of xs = impl_of ys \<Longrightarrow> xs = ys"
by(simp add: impl_of_inject)

lemma expand_assoc_list_eq: "xs = ys \<longleftrightarrow> impl_of xs = impl_of ys"
by(simp add: impl_of_inject)

lemma impl_of_distinct [simp, intro]: "distinct (map fst (impl_of al))"
using impl_of[of al] by simp

lemma impl_of_distinct_full [simp, intro]: "distinct (impl_of al)"
using impl_of_distinct[of al] 
unfolding distinct_map by simp

lemma Assoc_List_impl_of [code abstype]: "Assoc_List (impl_of al) = al"
by(rule impl_of_inverse)

subsection \<open>Primitive operations\<close>

definition empty :: "('k, 'v) assoc_list"
where [code del]: "empty = Assoc_List []"

definition lookup :: "('k, 'v) assoc_list \<Rightarrow> 'k \<Rightarrow> 'v option"
where [code]: "lookup al = map_of (impl_of al)" 

definition update_with :: "'v \<Rightarrow> 'k \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> ('k, 'v) assoc_list \<Rightarrow> ('k, 'v) assoc_list"
where [code del]: "update_with v k f al = Assoc_List (AList.update_with_aux v k f (impl_of al))"

definition delete :: "'k \<Rightarrow> ('k, 'v) assoc_list \<Rightarrow> ('k, 'v) assoc_list"
where [code del]: "delete k al = Assoc_List (AList.delete_aux k (impl_of al))"

definition iteratei :: "('k, 'v) assoc_list \<Rightarrow> ('s\<Rightarrow>bool) \<Rightarrow> ('k \<times> 'v \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 's \<Rightarrow> 's" 
where [code]: "iteratei al c f = foldli (impl_of al) c f"

lemma impl_of_empty [code abstract]: "impl_of empty = []"
by(simp add: empty_def Assoc_List_inverse)

lemma impl_of_update_with [code abstract]:
  "impl_of (update_with v k f al) = AList.update_with_aux v k f (impl_of al)"
by(simp add: update_with_def Assoc_List_inverse)

lemma impl_of_delete [code abstract]:
  "impl_of (delete k al) = AList.delete_aux k (impl_of al)"
by(simp add: delete_def Assoc_List_inverse)

subsection \<open>Abstract operation properties\<close>

lemma lookup_empty [simp]: "lookup empty k = None"
by(simp add: empty_def lookup_def Assoc_List_inverse)

lemma lookup_empty': "lookup empty = Map.empty"
by(rule ext) simp

lemma lookup_update_with [simp]: 
  "lookup (update_with v k f al) = (lookup al)(k \<mapsto> case lookup al k of None \<Rightarrow> f v | Some v \<Rightarrow> f v)"
by(simp add: lookup_def update_with_def Assoc_List_inverse map_of_update_with_aux)

lemma lookup_delete [simp]: "lookup (delete k al) = (lookup al)(k := None)"
by(simp add: lookup_def delete_def Assoc_List_inverse distinct_delete map_of_delete_aux')

lemma finite_dom_lookup [simp, intro!]: "finite (dom (lookup m))"
by(simp add: lookup_def finite_dom_map_of)

lemma iteratei_correct:
  "map_iterator (iteratei m) (lookup m)"
unfolding iteratei_def[abs_def] lookup_def map_to_set_def
by (simp add: set_iterator_foldli_correct)


subsection \<open>Derived operations\<close>

definition update :: "'key \<Rightarrow> 'val \<Rightarrow> ('key, 'val) assoc_list \<Rightarrow> ('key, 'val) assoc_list"
where "update k v = update_with v k (\<lambda>_. v)"

definition set :: "('key, 'val) assoc_list \<Rightarrow> ('key \<times> 'val) set"
where "set al = List.set (impl_of al)"


lemma lookup_update [simp]: "lookup (update k v al) = (lookup al)(k \<mapsto> v)"
by(simp add: update_def split: option.split)

lemma set_empty [simp]: "set empty = {}"
by(simp add: set_def empty_def Assoc_List_inverse)

lemma set_update_with:
  "set (update_with v k f al) = 
  (set al - {k} \<times> UNIV \<union> {(k, f (case lookup al k of None \<Rightarrow> v | Some v \<Rightarrow> v))})"
by(simp add: set_def update_with_def Assoc_List_inverse set_update_with_aux lookup_def)

lemma set_update: "set (update k v al) = (set al - {k} \<times> UNIV \<union> {(k, v)})"
by(simp add: update_def set_update_with)

lemma set_delete: "set (delete k al) = set al - {k} \<times> UNIV"
by(simp add: set_def delete_def Assoc_List_inverse set_delete_aux)

subsection \<open>Type classes\<close>

instantiation assoc_list :: (equal, equal) equal begin

definition "equal_class.equal (al :: ('a, 'b) assoc_list) al' == impl_of al = impl_of al'"

instance
proof
qed (simp add: equal_assoc_list_def impl_of_inject)

end

instantiation assoc_list :: (type, type) size begin

definition "size (al :: ('a, 'b) assoc_list) = length (impl_of al)"

instance ..
end

hide_const (open) impl_of empty lookup update_with set update delete iteratei 

subsection \<open>@{const map_ran}\<close>

text \<open>@{term map_ran} with more general type - lemmas replicated from AList in HOL/Library\<close>

hide_const (open) map_ran

primrec
  map_ran :: "('key \<Rightarrow> 'val \<Rightarrow> 'val') \<Rightarrow> ('key \<times> 'val) list \<Rightarrow> ('key \<times> 'val') list"
where
    "map_ran f [] = []"
  | "map_ran f (p#ps) = (fst p, f (fst p) (snd p)) # map_ran f ps"

lemma map_ran_conv: "map_of (map_ran f al) k = map_option (f k) (map_of al k)"
  by (induct al) auto

lemma dom_map_ran: "fst ` set (map_ran f al) = fst ` set al"
  by (induct al) auto

lemma distinct_map_ran: "distinct (map fst al) \<Longrightarrow> distinct (map fst (map_ran f al))"
  by (induct al) (auto simp add: dom_map_ran)

lemma map_ran_filter: "map_ran f [(a, _)\<leftarrow>ps. fst p \<noteq> a] = [(a, _)\<leftarrow>map_ran f ps. fst p \<noteq> a]"
  by (induct ps) auto

lemma clearjunk_map_ran: "AList.clearjunk (map_ran f al) 
  = map_ran f (AList.clearjunk al)"
  by (induct al rule: clearjunk.induct) (simp_all add: AList.delete_eq map_ran_filter)

text \<open>new lemmas and definitions\<close>

lemma map_ran_cong [fundef_cong]:
  "\<lbrakk> al = al'; \<And>k v. (k, v) \<in> set al \<Longrightarrow> f k v = g k v \<rbrakk> \<Longrightarrow> map_ran f al = map_ran g al'"
by hypsubst_thin (induct al', auto)

lemma size_list_delete: "size_list f (AList.delete a al) \<le> size_list f al"
by(induct al) simp_all

lemma size_list_clearjunk: "size_list f (AList.clearjunk al) \<le> size_list f al"
by(induct al)(auto simp add: clearjunk_delete intro: le_trans[OF size_list_delete])

lemma set_delete_conv: "set (AList.delete a al) = set al - ({a} \<times> UNIV)"
proof(induct al)
  case (Cons kv al)
  thus ?case by(cases kv) auto
qed simp

lemma set_clearjunk_subset: "set (AList.clearjunk al) \<subseteq> set al"
by(induct al)(auto simp add: clearjunk_delete set_delete_conv)

lemma map_ran_conv_map:
  "map_ran f xs = map (\<lambda>(k, v). (k, f k v)) xs"
by(induct xs) auto

lemma card_dom_map_of: "distinct (map fst al) \<Longrightarrow> card (dom (map_of al)) = length al"
by(induct al)(auto simp add: card_insert_if finite_dom_map_of dom_map_of_conv_image_fst)

lemma map_of_map_inj_fst:
  assumes "inj f"
  shows "map_of (map (\<lambda>(k, v). (f k, v)) xs) (f x) = map_of xs x"
by(induct xs)(auto dest: injD[OF \<open>inj f\<close>])

lemma length_map_ran [simp]: "length (map_ran f xs) = length xs"
by(induct xs) simp_all

lemma length_update: 
  "length (AList.update k v xs) 
  = (if k \<in> fst ` set xs then length xs else Suc (length xs))"
by(induct xs) simp_all

lemma length_distinct: 
  "distinct (map fst xs) \<Longrightarrow> length (AList.delete k xs) 
  = (if k \<in> fst ` set xs then length xs - 1 else length xs)"
  by(induct xs)(auto split: if_split_asm simp add: in_set_conv_nth)

lemma finite_Assoc_List_set_image:
  assumes "finite (Assoc_List.set ` A)"
  shows "finite A"
proof -
  have "Assoc_List.set ` A = set ` Assoc_List.impl_of ` A"
    by (auto simp add: Assoc_List.set_def)
  with assms finite_set_image have "finite (Assoc_List.impl_of ` A)" by auto
  with assoc_list_ext show ?thesis by (metis inj_onI finite_imageD)
qed

end
