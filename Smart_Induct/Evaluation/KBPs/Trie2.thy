(* Title: Adaptation of Trie Implementation
   Author: Peter Gammie < peteg42 at gmail dot com >
*)

(*<*)
theory Trie2 imports
  MapOps
  ODList
  Trie.Trie
begin
(*>*)

definition
  trie_update_with :: "'key list \<Rightarrow> 'val \<Rightarrow> ('val \<Rightarrow> 'val) \<Rightarrow> ('key, 'val) trie \<Rightarrow> ('key, 'val) trie"
where
  "trie_update_with ks v f \<equiv> update_with_trie ks (%vo. f(case vo of None \<Rightarrow> v | Some v \<Rightarrow> v))"

lemma [simp]:
  "trie_update_with [] v f (Trie vo ts) =
    Trie (Some (f (case vo of None \<Rightarrow> v | Some v' \<Rightarrow> v'))) ts"
by(simp add: trie_update_with_def)

lemma [simp]:
  "trie_update_with (k#ks) v f (Trie vo ts) =
    Trie vo (AList.update_with_aux empty_trie k (trie_update_with ks v f) ts)"
by(simp add: trie_update_with_def empty_trie_def)

abbreviation
  trie_update_with' :: "'k list \<Rightarrow> ('k, 'v) trie \<Rightarrow> 'v \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> ('k, 'v) trie"
where
  "trie_update_with' \<equiv> (\<lambda>k m v f. trie_update_with k v f m)"

definition
  trie_update :: "'key list \<Rightarrow> 'val \<Rightarrow> ('key, 'val) trie \<Rightarrow> ('key, 'val) trie"
where
  "trie_update k v t = trie_update_with k v (\<lambda>v'. v) t"

text \<open>@{term "trie_lookup"}\<close>

lemma lookup_empty_trie [simp]: "lookup_trie empty_trie ks = None"
by (cases ks) (simp_all)

lemma lookup_trie_update_with:
  "lookup_trie (trie_update_with ks v f t) ks'
 = (if ks = ks' then Some (f (case lookup_trie t ks of None \<Rightarrow> v | Some v' \<Rightarrow> v')) else lookup_trie t ks')"
proof(induct ks "(%vo. f(case vo of None \<Rightarrow> v | Some v \<Rightarrow> v))" t arbitrary: v ks' rule: update_with_trie.induct)
  case (1 v ps vo ks')
  show ?case by (fastforce simp add: neq_Nil_conv dest: not_sym)
next
  case (2 k ks v ps vo ks')
  show ?case by(cases ks')(auto simp add: map_of_update_with_aux "2" empty_trie_def split: option.split)
qed

lemma lookup_trie_update:
  "lookup_trie (trie_update ks v t) ks' = (if ks = ks' then Some v else lookup_trie t ks')"
  unfolding trie_update_def by (auto simp add: lookup_trie_update_with)

text\<open>@{term "MapOps"}\<close>

definition
  trie_MapOps :: "(('k, 'e) trie, 'k list, 'e) MapOps"
where
  "trie_MapOps \<equiv>
     \<lparr> MapOps.empty = empty_trie,
       lookup = lookup_trie,
       update = trie_update \<rparr>"

lemma trie_MapOps[intro, simp]:
  "inj_on \<alpha> { x . \<alpha> x \<in> d } \<Longrightarrow> MapOps \<alpha> d trie_MapOps"
  apply rule
  unfolding trie_MapOps_def
  apply (auto dest: inj_onD simp add: lookup_trie_update)
  done

definition
  "trie_odlist_lookup = (\<lambda>M. lookup_trie M \<circ> toList)"

definition
  "trie_odlist_update = (\<lambda>k v. trie_update (toList k) v)"

definition
  trie_odlist_update_with :: "('k :: linorder) odlist \<Rightarrow> ('k, 'v) trie \<Rightarrow> 'v \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> ('k, 'v) trie"
where
  "trie_odlist_update_with = (\<lambda>k m v f. trie_update_with (toList k) v f m)"

definition
  trie_odlist_MapOps :: "(('k, 'e) trie, ('k ::linorder) odlist, 'e) MapOps"
where
  "trie_odlist_MapOps \<equiv>
     \<lparr> MapOps.empty = empty_trie,
       lookup = trie_odlist_lookup,
       update = trie_odlist_update \<rparr>"

lemma trie_odlist_MapOps[intro, simp]:
  "inj_on \<alpha> { x . \<alpha> x \<in> d } \<Longrightarrow> MapOps \<alpha> d trie_odlist_MapOps"
  apply rule
  unfolding trie_odlist_MapOps_def trie_odlist_lookup_def trie_odlist_update_def
  apply (auto dest: inj_onD simp add: lookup_trie_update)
  done

(*<*)
end
(*>*)
