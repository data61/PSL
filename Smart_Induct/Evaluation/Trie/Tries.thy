(*  Author: Tobias Nipkow  *)

section "Tries (List Version)"

theory Tries
imports Trie
begin

text\<open>This is a specialization of tries where values are lists.\<close>

type_synonym ('k,'v)tries = "('k,'v list)trie"

definition lookup_tries :: "('k,'v)tries \<Rightarrow> 'k list \<Rightarrow> 'v list" where
"lookup_tries t ks = (case lookup_trie t ks of None \<Rightarrow> [] | Some vs \<Rightarrow> vs)"

definition update_with_tries ::
  "'k list \<Rightarrow> ('v list \<Rightarrow> 'v list) \<Rightarrow> ('k, 'v) tries \<Rightarrow> ('k, 'v) tries" where
"update_with_tries ks f =
  update_with_trie ks (\<lambda>vo. case vo of None \<Rightarrow> f [] | Some vs \<Rightarrow> f vs)"

definition insert_tries :: "'k list \<Rightarrow> 'v \<Rightarrow> ('k,'v)tries \<Rightarrow> ('k,'v)tries" where
"insert_tries ks v =
  update_with_trie ks (\<lambda>vo. case vo of None \<Rightarrow> [v] | Some vs \<Rightarrow> v#vs)"

definition inserts_tries :: "('v \<Rightarrow> 'k list) \<Rightarrow> 'v list \<Rightarrow> ('k,'v)tries \<Rightarrow> ('k,'v)tries" where
"inserts_tries key = fold (%v. insert_tries (key v) v)"

definition tries_of_list :: "('v \<Rightarrow> 'k list) \<Rightarrow> 'v list \<Rightarrow> ('k,'v)tries" where
"tries_of_list key vs = inserts_tries key vs (Trie None [])"

definition set_tries :: "('k,'v)tries \<Rightarrow> 'v set" where
"set_tries t = Union {gs. \<exists>a. gs = set(lookup_tries t a)}"

definition all_tries :: "('v \<Rightarrow> bool) \<Rightarrow> ('k,'v)tries \<Rightarrow> bool" where
"all_tries P = all_trie (list_all P)"


subsection \<open>@{const lookup_tries}\<close>

lemma lookup_Nil[simp]:
  "lookup_tries (Trie vo ps) [] = (case vo of None \<Rightarrow> [] | Some vs \<Rightarrow> vs)"
by (simp add: lookup_tries_def)

lemma lookup_Cons[simp]: "lookup_tries (Trie vo ps) (a#as) =
  (case map_of ps a of None \<Rightarrow> [] | Some at \<Rightarrow> lookup_tries at as)"
by (simp add: lookup_tries_def split: option.split)

lemma lookup_empty[simp]: "lookup_tries (Trie None []) as = []"
by(case_tac as, simp_all add: lookup_tries_def)

theorem lookup_update:
 "lookup_tries (update_trie as vs t) bs =
 (if as=bs then vs else lookup_tries t bs)"
by(auto simp add: lookup_tries_def lookup_update)

theorem lookup_update_with:
 "lookup_tries (update_with_tries as f t) bs =
 (if as=bs then f(lookup_tries t as) else lookup_tries t bs)"
by(auto simp add: lookup_tries_def update_with_tries_def lookup_update_with_trie
  split: option.split)


subsection \<open>@{const insert_tries}, @{const inserts_tries}, @{const tries_of_list}\<close>

lemma invar_insert_tries: "invar_trie t \<Longrightarrow> invar_trie(insert_tries as v t)"
by(simp add: insert_tries_def invar_update_with_trie split: option.split)

lemma invar_inserts_tries:
  "invar_trie t \<Longrightarrow> invar_trie (inserts_tries key xs t)"
by(induct xs arbitrary: t)(auto simp: invar_insert_tries inserts_tries_def)

lemma invar_of_list: "invar_trie (tries_of_list key xs)"
by(simp add: tries_of_list_def invar_inserts_tries)

lemma set_lookup_insert_tries: "set (lookup_tries (insert_tries ks a t) ks') =
  (if ks' = ks then Set.insert a (set(lookup_tries t ks')) else set(lookup_tries t ks'))"
by(simp add: lookup_tries_def insert_tries_def lookup_update_with_trie set_eq_iff split: option.split)

lemma in_set_lookup_inserts_tries:
  "(v \<in> set(lookup_tries (inserts_tries key vs t) (key v))) =
   (v \<in> set vs \<union> set(lookup_tries t (key v)))"
by(induct vs arbitrary: t)
  (auto simp add: inserts_tries_def set_lookup_insert_tries)

lemma in_set_lookup_of_list:
  "v \<in> set(lookup_tries (tries_of_list key vs) (key v)) = (v \<in> set vs)"
by(simp add: tries_of_list_def in_set_lookup_inserts_tries)

lemma in_set_lookup_inserts_triesD:
  "v \<in> set(lookup_tries (inserts_tries key vs t) xs) \<Longrightarrow>
  v \<in> set vs \<union> set(lookup_tries t xs)"
apply(induct vs arbitrary: t)
 apply (simp add: inserts_tries_def)
apply (simp add: inserts_tries_def)
apply (fastforce simp add: set_lookup_insert_tries split: if_splits)
done
 
lemma in_set_lookup_of_listD:
  "v \<in> set(lookup_tries (tries_of_list f vs) xs) \<Longrightarrow> v \<in> set vs"
by(auto simp: tries_of_list_def dest: in_set_lookup_inserts_triesD)


subsection \<open>@{const set_tries}\<close>

lemma set_tries_eq_ran: "set_tries t = Union(set ` ran(lookup_trie t))"
apply(auto simp add: set_eq_iff set_tries_def lookup_tries_def ran_def)
 apply metis
by (metis option.inject)

lemma set_tries_empty[simp]: "set_tries (Trie None []) = {}"
by(simp add: set_tries_def)

lemma set_tries_insert[simp]:
  "set_tries (insert_tries a x t) = Set.insert x (set_tries t)"
apply(auto simp: set_tries_def lookup_update set_lookup_insert_tries)
by (metis insert_iff)

lemma set_insert_tries:
  "set_tries (inserts_tries key xs t) =
   set xs Un set_tries t"
by(induct xs arbitrary: t) (auto simp: inserts_tries_def)

lemma set_tries_of_list[simp]:
  "set_tries(tries_of_list key xs) = set xs"
by(simp add: tries_of_list_def set_insert_tries)

lemma in_set_lookup_set_triesD:
  "x\<in>set (lookup_tries t a) \<Longrightarrow> x \<in> set_tries t"
by(auto simp: set_tries_def)

end
