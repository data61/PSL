(*  Title:      Containers/AssocList.thy
    Author:     Andreas Lochbihler, KIT *)

theory AssocList imports
  "HOL-Library.DAList" 
begin

section \<open>Additional operations for associative lists\<close>

subsection \<open>Operations on the raw type\<close>

primrec update_with_aux :: "'val \<Rightarrow> 'key \<Rightarrow> ('val \<Rightarrow> 'val) \<Rightarrow> ('key \<times> 'val) list \<Rightarrow> ('key \<times> 'val) list"
where
  "update_with_aux v k f [] = [(k, f v)]"
| "update_with_aux v k f (p # ps) = (if (fst p = k) then (k, f (snd p)) # ps else p # update_with_aux v k f ps)"

text \<open>
  Do not use @{term "AList.delete"} because this traverses all the list even if it has found the key.
  We do not have to keep going because we use the invariant that keys are distinct.
\<close>
fun delete_aux :: "'key \<Rightarrow> ('key \<times> 'val) list \<Rightarrow> ('key \<times> 'val) list"
where
  "delete_aux k [] = []"
| "delete_aux k ((k', v) # xs) = (if k = k' then xs else (k', v) # delete_aux k xs)"

lemma update_conv_update_with_aux:
  "AList.update k v xs = update_with_aux v k (\<lambda>_. v) xs"
by(induct xs) simp_all

lemma map_of_update_with_aux':
  "map_of (update_with_aux v k f ps) k' = ((map_of ps)(k \<mapsto> (case map_of ps k of None \<Rightarrow> f v | Some v \<Rightarrow> f v))) k'"
by(induct ps) auto

lemma map_of_update_with_aux:
  "map_of (update_with_aux v k f ps) = (map_of ps)(k \<mapsto> (case map_of ps k of None \<Rightarrow> f v | Some v \<Rightarrow> f v))"
by(simp add: fun_eq_iff map_of_update_with_aux')

lemma dom_update_with_aux: "fst ` set (update_with_aux v k f ps) = {k} \<union> fst ` set ps"
  by (induct ps) auto

lemma distinct_update_with_aux [simp]:
  "distinct (map fst (update_with_aux v k f ps)) = distinct (map fst ps)"
by(induct ps)(auto simp add: dom_update_with_aux)

lemma set_update_with_aux:
  "distinct (map fst xs) 
  \<Longrightarrow> set (update_with_aux v k f xs) = (set xs - {k} \<times> UNIV \<union> {(k, f (case map_of xs k of None \<Rightarrow> v | Some v \<Rightarrow> v))})"
by(induct xs)(auto intro: rev_image_eqI)

lemma set_delete_aux: "distinct (map fst xs) \<Longrightarrow> set (delete_aux k xs) = set xs - {k} \<times> UNIV"
apply(induct xs)
apply simp_all
apply clarsimp
apply(fastforce intro: rev_image_eqI)
done

lemma dom_delete_aux: "distinct (map fst ps) \<Longrightarrow> fst ` set (delete_aux k ps) = fst ` set ps - {k}"
by(auto simp add: set_delete_aux)

lemma distinct_delete_aux [simp]:
  "distinct (map fst ps) \<Longrightarrow> distinct (map fst (delete_aux k ps))"
proof(induct ps)
  case Nil thus ?case by simp
next
  case (Cons a ps)
  obtain k' v where a: "a = (k', v)" by(cases a)
  show ?case
  proof(cases "k' = k")
    case True with Cons a show ?thesis by simp
  next
    case False
    with Cons a have "k' \<notin> fst ` set ps" "distinct (map fst ps)" by simp_all
    with False a have "k' \<notin> fst ` set (delete_aux k ps)"
      by(auto dest!: dom_delete_aux[where k=k])
    with Cons a show ?thesis by simp
  qed
qed

lemma map_of_delete_aux':
  "distinct (map fst xs) \<Longrightarrow> map_of (delete_aux k xs) = (map_of xs)(k := None)"
by(induct xs)(fastforce simp add: map_of_eq_None_iff fun_upd_twist)+

lemma map_of_delete_aux:
  "distinct (map fst xs) \<Longrightarrow> map_of (delete_aux k xs) k' = ((map_of xs)(k := None)) k'"
by(simp add: map_of_delete_aux')

lemma delete_aux_eq_Nil_conv: "delete_aux k ts = [] \<longleftrightarrow> ts = [] \<or> (\<exists>v. ts = [(k, v)])"
by(cases ts)(auto split: if_split_asm)

subsection \<open>Operations on the abstract type @{typ "('a, 'b) alist"}\<close>

lift_definition update_with :: "'v \<Rightarrow> 'k \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> ('k, 'v) alist \<Rightarrow> ('k, 'v) alist"
  is "update_with_aux" by simp

lift_definition delete :: "'k \<Rightarrow> ('k, 'v) alist \<Rightarrow> ('k, 'v) alist" is "delete_aux"
by simp

lift_definition keys :: "('k, 'v) alist \<Rightarrow> 'k set" is "set \<circ> map fst" .

lift_definition set :: "('key, 'val) alist \<Rightarrow> ('key \<times> 'val) set"
is "List.set" .

lemma lookup_update_with [simp]: 
  "DAList.lookup (update_with v k f al) = (DAList.lookup al)(k \<mapsto> case DAList.lookup al k of None \<Rightarrow> f v | Some v \<Rightarrow> f v)"
by transfer(simp add: map_of_update_with_aux)

lemma lookup_delete [simp]: "DAList.lookup (delete k al) = (DAList.lookup al)(k := None)"
by transfer(simp add: map_of_delete_aux')

lemma finite_dom_lookup [simp, intro!]: "finite (dom (DAList.lookup m))"
by transfer(simp add: finite_dom_map_of)

lemma update_conv_update_with: "DAList.update k v = update_with v k (\<lambda>_. v)"
by(rule ext)(transfer, simp add: update_conv_update_with_aux)

lemma lookup_update [simp]: "DAList.lookup (DAList.update k v al) = (DAList.lookup al)(k \<mapsto> v)"
by(simp add: update_conv_update_with split: option.split)

lemma dom_lookup_keys: "dom (DAList.lookup al) = keys al"
by transfer(simp add: dom_map_of_conv_image_fst)

lemma keys_empty [simp]: "keys DAList.empty = {}"
by transfer simp

lemma keys_update_with [simp]: "keys (update_with v k f al) = insert k (keys al)"
by(simp add: dom_lookup_keys[symmetric])

lemma keys_update [simp]: "keys (DAList.update k v al) = insert k (keys al)"
by(simp add: update_conv_update_with)

lemma keys_delete [simp]: "keys (delete k al) = keys al - {k}"
by(simp add: dom_lookup_keys[symmetric])

lemma set_empty [simp]: "set DAList.empty = {}"
by transfer simp

lemma set_update_with:
  "set (update_with v k f al) = 
  (set al - {k} \<times> UNIV \<union> {(k, f (case DAList.lookup al k of None \<Rightarrow> v | Some v \<Rightarrow> v))})"
by transfer(simp add: set_update_with_aux)

lemma set_update: "set (DAList.update k v al) = (set al - {k} \<times> UNIV \<union> {(k, v)})"
by(simp add: update_conv_update_with set_update_with)

lemma set_delete: "set (delete k al) = set al - {k} \<times> UNIV"
by transfer(simp add: set_delete_aux)

lemma size_dalist_transfer [transfer_rule]:
  includes lifting_syntax
  shows "(pcr_alist (=) (=) ===> (=)) length size"
unfolding size_alist_def[abs_def]
by transfer_prover

lemma size_eq_card_dom_lookup: "size al = card (dom (DAList.lookup al))"
by transfer (metis comp_apply distinct_card dom_map_of_conv_image_fst image_set length_map)

hide_const (open) update_with keys set delete

end
