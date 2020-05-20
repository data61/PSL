section "Hash-Tables"
theory Hash_Table
imports
  Collections.HashCode
  Collections.Code_Target_ICF
  "../Sep_Main"
begin

subsection \<open>Datatype\<close>

subsubsection \<open>Definition\<close>

datatype ('k, 'v) hashtable = HashTable "('k \<times> 'v) list array" nat

primrec the_array :: "('k, 'v) hashtable \<Rightarrow> ('k \<times> 'v) list array"
  where "the_array (HashTable a _) = a"

primrec the_size :: "('k, 'v) hashtable \<Rightarrow> nat"
  where "the_size (HashTable _ n) = n"


subsubsection \<open>Storable on Heap\<close>

fun hs_encode :: "('k::countable, 'v::countable) hashtable \<Rightarrow> nat"
  where "hs_encode (HashTable a n) = to_nat (n, a)"

instance hashtable :: (countable, countable) countable
proof (rule countable_classI[of "hs_encode"])
  fix x y :: "('a, 'b) hashtable"
  assume "hs_encode x = hs_encode y"
  then show "x = y" by (cases x, cases y) auto
qed

instance hashtable :: (heap, heap) heap ..


subsection \<open>Assertions\<close>

subsubsection \<open>Assertion for Hashtable\<close>

definition ht_table :: "('k::heap \<times> 'v::heap) list list \<Rightarrow> ('k, 'v) hashtable \<Rightarrow> assn"
  where "ht_table l ht = (the_array ht) \<mapsto>\<^sub>a l"

definition ht_size :: "'a list list \<Rightarrow> nat \<Rightarrow> bool"
  where "ht_size l n \<equiv> n = sum_list (map length l)"

definition ht_hash :: "('k::hashable \<times> 'v) list list \<Rightarrow> bool" where
  "ht_hash l \<equiv> \<forall>i<length l. \<forall>x\<in>set (l!i).
    bounded_hashcode_nat (length l) (fst x) = i"

definition ht_distinct :: "('k \<times> 'v) list list \<Rightarrow> bool" where
  "ht_distinct l \<equiv> \<forall>i<length l. distinct (map fst (l!i))"


definition is_hashtable :: "('k::{heap,hashable} \<times> 'v::heap) list list
    \<Rightarrow> ('k, 'v) hashtable \<Rightarrow> assn"
where
  "is_hashtable l ht =
  (the_array ht \<mapsto>\<^sub>a l) *
  \<up>(ht_size l (the_size ht)
    \<and> ht_hash l
    \<and> ht_distinct l
    \<and> 1 < length l)"

lemma is_hashtable_prec: "precise is_hashtable"
  apply (rule preciseI)
  unfolding is_hashtable_def
  apply (auto simp add: preciseD[OF snga_prec])
  done

text \<open>These rules are quite useful for automated methods, to avoid unfolding
  of definitions, that might be used folded in other lemmas,
  like induction hypothesis. However, they show in some sense a possibility for
  modularization improvement, as it should be enough to show an implication
  and know that the \<open>nth\<close> and \<open>len\<close> operations do not change
  the heap.\<close>
lemma ht_array_nth_rule[sep_heap_rules]:
    "i<length l \<Longrightarrow> <is_hashtable l ht>
      Array.nth (the_array ht) i
      <\<lambda>r. is_hashtable l ht * \<up>(r = l!i)>"
  unfolding is_hashtable_def
  by sep_auto

lemma ht_array_length_rule[sep_heap_rules]:
    "<is_hashtable l ht>
      Array.len (the_array ht)
      <\<lambda>r. is_hashtable l ht * \<up>(r = length l)>"
  unfolding is_hashtable_def
  by sep_auto


subsection \<open>New\<close>

subsubsection \<open>Definition\<close>

definition ht_new_sz :: "nat \<Rightarrow> ('k::{heap,hashable}, 'v::heap) hashtable Heap"
where
  "ht_new_sz n \<equiv> do { let l = replicate n [];
  a \<leftarrow> Array.of_list l;
  return (HashTable a 0) }"


definition ht_new :: "('k::{heap,hashable}, 'v::heap) hashtable Heap"
  where "ht_new \<equiv> ht_new_sz (def_hashmap_size TYPE('k))"


subsubsection \<open>Complete Correctness\<close>

lemma ht_hash_replicate[simp, intro!]: "ht_hash (replicate n [])"
  apply (induct n)
  apply (auto simp add: ht_hash_def)
  apply (case_tac i)
  apply auto
  done

lemma ht_distinct_replicate[simp, intro!]: "ht_distinct (replicate n [])"
  apply (induct n)
  apply (auto simp add: ht_distinct_def)
  apply (case_tac i)
  apply auto
  done

lemma ht_size_replicate[simp, intro!]: "ht_size (replicate n []) 0"
  by (simp add: ht_size_def)

 \<comment> \<open>We can't create hash tables with a size of zero\<close>
lemma complete_ht_new_sz: "1 < n \<Longrightarrow> <emp> ht_new_sz n <is_hashtable (replicate n [])>"
  apply (unfold ht_new_sz_def)
  apply (simp del: replicate.simps)
  apply (rule bind_rule)
  apply (rule of_list_rule)
  apply (rule return_cons_rule)
  apply (simp add: is_hashtable_def)
  done

lemma complete_ht_new:
  "<emp>
     ht_new::('k::{heap,hashable}, 'v::heap) hashtable Heap
   <is_hashtable (replicate (def_hashmap_size TYPE('k)) [])>"
  unfolding ht_new_def
  by (simp add: complete_ht_new_sz[OF def_hashmap_size])


subsection \<open>Lookup\<close>

subsubsection \<open>Definition\<close>

fun ls_lookup :: "'k \<Rightarrow> ('k \<times> 'v) list \<Rightarrow> 'v option"
where
  "ls_lookup x [] = None" |
  "ls_lookup x ((k, v) # l) = (if x = k then Some v else ls_lookup x l)"

definition ht_lookup :: "'k \<Rightarrow> ('k::{heap,hashable}, 'v::heap) hashtable \<Rightarrow> 'v option Heap"
where
  "ht_lookup x ht = do {
    m \<leftarrow> Array.len (the_array ht);
    let i = bounded_hashcode_nat m x;
    l \<leftarrow> Array.nth (the_array ht) i;
    return (ls_lookup x l)
  }"


subsubsection \<open>Complete Correctness\<close>

lemma complete_ht_lookup:
  "<is_hashtable l ht> ht_lookup x ht
     <\<lambda>r. is_hashtable l ht *
        \<up>(r = ls_lookup x (l!(bounded_hashcode_nat (length l) x))) >"
  apply (cases ht)
  apply (clarsimp simp: is_hashtable_def)
  apply (simp add: ht_lookup_def)
  apply (rule bind_rule)
  apply (rule length_rule)
  apply (rule norm_pre_pure_rule)
  apply (rule bind_rule)
  apply (rule nth_rule)
  apply (simp add: bounded_hashcode_nat_bounds)
  apply (rule norm_pre_pure_rule)
  apply (rule return_cons_rule)
  apply simp
  done

text \<open>Alternative, more automatic proof\<close>
lemma complete_ht_lookup_alt_proof:
  "<is_hashtable l ht> ht_lookup x ht
    <\<lambda>r. is_hashtable l ht *
      \<up>(r = ls_lookup x (l!(bounded_hashcode_nat (length l) x)))>"
  unfolding is_hashtable_def ht_lookup_def
  apply (cases ht)
  apply (sep_auto simp: bounded_hashcode_nat_bounds)
  done


subsection \<open>Update\<close>

subsubsection \<open>Definition\<close>

fun ls_update :: "'k \<Rightarrow> 'v \<Rightarrow> ('k \<times> 'v) list \<Rightarrow> (('k \<times> 'v) list \<times> bool)"
where
  "ls_update k v [] = ([(k, v)], False)" |
  "ls_update k v ((l, w) # ls) = (
    if k = l then
      ((k, v) # ls, True)
    else
      (let r = ls_update k v ls in ((l, w) # fst r, snd r))
  )"

definition abs_update
  :: "'k::hashable \<Rightarrow> 'v \<Rightarrow> ('k \<times> 'v) list list \<Rightarrow> ('k \<times> 'v) list list"
  where
  "abs_update k v l =
    l[bounded_hashcode_nat (length l) k
      := fst (ls_update k v (l ! bounded_hashcode_nat (length l) k))]"

lemma ls_update_snd_set: "snd (ls_update k v l) \<longleftrightarrow> k \<in> set (map fst l)"
  by (induct l rule: ls_update.induct) simp_all

lemma ls_update_fst_set: "set (fst (ls_update k v l)) \<subseteq> insert (k, v) (set l)"
  apply (induct l rule: ls_update.induct)
  apply simp
  apply (auto simp add: Let_def)
  done

lemma ls_update_fst_map_set: "set (map fst (fst (ls_update k v l))) = insert k (set (map fst l))"
  apply (induct l rule: ls_update.induct)
  apply simp
  apply (auto simp add: Let_def)
  done

lemma ls_update_distinct: "distinct (map fst l) \<Longrightarrow> distinct (map fst (fst (ls_update k v l)))"
proof (induct l rule: ls_update.induct)
  case 1 thus ?case by simp
next
  case (2 k v l w ls) show ?case
  proof (cases "k = l")
    case True
    with 2 show ?thesis by simp
  next
    case False
    with 2 have d: "distinct (map fst (fst (ls_update k v ls)))"
      by simp
    from 2(2) have "l \<notin> set (map fst ls)" by simp
    with False have "l \<notin> set (map fst (fst (ls_update k v ls)))"
      by (simp only: ls_update_fst_map_set) simp
    with d False show ?thesis by (simp add: Let_def)
  qed
qed

lemma ls_update_length: "length (fst (ls_update k v l))
  = (if (k \<in> set (map fst l)) then length l else Suc (length l))"
  by (induct l rule: ls_update.induct) (auto simp add: Let_def)

lemma ls_update_length_snd_True:
  "snd (ls_update k v l) \<Longrightarrow> length (fst (ls_update k v l)) = length l"
  by (simp add: ls_update_length ls_update_snd_set)

lemma ls_update_length_snd_False:
  "\<not> snd (ls_update k v l) \<Longrightarrow> length (fst (ls_update k v l)) = Suc (length l)"
  by (simp add: ls_update_length ls_update_snd_set)


definition ht_upd
  :: "'k \<Rightarrow> 'v
    \<Rightarrow> ('k::{heap,hashable}, 'v::heap) hashtable
    \<Rightarrow> ('k, 'v) hashtable Heap"
  where
  "ht_upd k v ht = do {
      m \<leftarrow> Array.len (the_array ht);
      let i = bounded_hashcode_nat m k;
      l \<leftarrow> Array.nth (the_array ht) i;
      let l = ls_update k v l;
      Array.upd i (fst l) (the_array ht);
      let n = (if (snd l) then the_size ht else Suc (the_size ht));
      return (HashTable (the_array ht) n)
    }"


subsubsection \<open>Complete Correctness\<close>

lemma ht_hash_update:
  assumes "ht_hash ls"
  shows "ht_hash (abs_update k v ls)"
  unfolding ht_hash_def abs_update_def
  apply (intro allI ballI impI)
  apply simp
  subgoal premises prems for i x
  proof (cases "i = bounded_hashcode_nat (length ls) k")
    case True
    note i = True
    show ?thesis
    proof (cases "fst x = k")
      case True
      with i show ?thesis by simp
    next
      case False
      with prems i
      have
        "x \<in> set (fst (ls_update k v
                         (ls ! bounded_hashcode_nat (length ls) k)))"
        by auto
      with
        ls_update_fst_set[
          of k v "ls ! bounded_hashcode_nat (length ls) k"]
        False
      have "x \<in> insert (k, v)
                  (set (ls ! bounded_hashcode_nat (length ls) k))"
        by auto
      with False have "x \<in> set (ls ! bounded_hashcode_nat (length ls) k)"
        by auto
      with i prems assms[unfolded ht_hash_def] show ?thesis by simp
    qed
  next
    case False
    with prems have "x \<in> set (ls ! i)" by simp
    with prems assms[unfolded ht_hash_def] show ?thesis by simp
  qed
  done


lemma ht_distinct_update:
  assumes "ht_distinct l"
  shows "ht_distinct (abs_update k v l)"
  unfolding ht_distinct_def abs_update_def
  apply (intro allI impI)
  apply simp
  subgoal premises prems for i
  proof (cases "i = bounded_hashcode_nat (length l) k")
    case True
    with prems assms[unfolded ht_distinct_def]
    have "distinct (map fst (l ! bounded_hashcode_nat (length l) k))"
      by simp
    from ls_update_distinct[OF this, of k v] True prems
    show ?thesis by simp
  next
    case False
    with prems assms[unfolded ht_distinct_def] show ?thesis by simp
  qed
  done


lemma length_update:
  assumes "1 < length l"
  shows "1 < length (abs_update k v l)"
  using assms
  by (simp add: abs_update_def)

lemma ht_size_update1:
  assumes size: "ht_size l n"
  assumes i: "i < length l"
  assumes snd: "snd (ls_update k v (l ! i))"
  shows "ht_size (l[i := fst (ls_update k v (l!i))]) n"
proof -
  have "(map length (l[i := fst (ls_update k v (l ! i))]))
    = (map length l)[i := length (fst (ls_update k v (l ! i)))]"
    by (simp add: map_update) also
  from sum_list_update[of i "map length l", simplified, OF i,
    of "length (fst (ls_update k v (l ! i)))"]
    ls_update_length_snd_True[OF snd]
  have
    "sum_list ((map length l)[i := length (fst (ls_update k v (l ! i)))])
    = sum_list (map length l)" by simp
  finally show ?thesis using assms by (simp add: ht_size_def assms)
qed

lemma ht_size_update2:
  assumes size: "ht_size l n"
  assumes i: "i < length l"
  assumes snd: "\<not> snd (ls_update k v (l ! i))"
  shows "ht_size (l[i := fst (ls_update k v (l!i))]) (Suc n)"
proof -
  have "(map length (l[i := fst (ls_update k v (l ! i))]))
    = (map length l)[i := length (fst (ls_update k v (l ! i)))]"
    by (simp add: map_update) also
  from sum_list_update[of i "map length l", simplified, OF i,
    of "length (fst (ls_update k v (l ! i)))"]
    ls_update_length_snd_False[OF snd]
  have
    "sum_list ((map length l)[i := length (fst (ls_update k v (l ! i)))])
    = Suc (sum_list (map length l))" by simp
  finally show ?thesis using assms by (simp add: ht_size_def assms)
qed


lemma complete_ht_upd: "<is_hashtable l ht> ht_upd k v ht
  <is_hashtable (abs_update k v l)>"
  unfolding ht_upd_def is_hashtable_def
  apply (rule norm_pre_pure_rule)
  apply (rule bind_rule)
  apply (rule length_rule)
  apply (rule norm_pre_pure_rule)
  apply (simp add: Let_def)
  apply (rule bind_rule)
  apply (rule nth_rule)
  apply (simp add: bounded_hashcode_nat_bounds)
  apply (rule norm_pre_pure_rule)
  apply (rule bind_rule)
  apply (rule upd_rule)
  apply (simp add: bounded_hashcode_nat_bounds)
  apply (rule return_cons_rule)
  apply (auto
    simp add: ht_size_update1 ht_size_update2 bounded_hashcode_nat_bounds
              is_hashtable_def ht_hash_update[unfolded abs_update_def]
              ht_distinct_update[unfolded abs_update_def] abs_update_def)
  done

text \<open>Alternative, more automatic proof\<close>
lemma complete_ht_upd_alt_proof:
  "<is_hashtable l ht> ht_upd k v ht <is_hashtable (abs_update k v l)>"
  unfolding ht_upd_def is_hashtable_def Let_def
  (* TODO: Is this huge simp-step really necessary? *)
  apply (sep_auto
    simp: ht_size_update1 ht_size_update2 bounded_hashcode_nat_bounds
              is_hashtable_def ht_hash_update[unfolded abs_update_def]
              ht_distinct_update[unfolded abs_update_def] abs_update_def)
  done


subsection \<open>Delete\<close>

subsubsection \<open>Definition\<close>

fun ls_delete :: "'k \<Rightarrow> ('k \<times> 'v) list \<Rightarrow> (('k \<times> 'v) list \<times> bool)" where
  "ls_delete k [] = ([], False)" |
  "ls_delete k ((l, w) # ls) = (
    if k = l then
      (ls, True)
    else
      (let r = ls_delete k ls in ((l, w) # fst r, snd r)))"

lemma ls_delete_snd_set: "snd (ls_delete k l) \<longleftrightarrow> k \<in> set (map fst l)"
  by (induct l rule: ls_delete.induct) simp_all

lemma ls_delete_fst_set: "set (fst (ls_delete k l)) \<subseteq> set l"
  apply (induct l rule: ls_delete.induct)
  apply simp
  apply (auto simp add: Let_def)
  done

lemma ls_delete_fst_map_set:
  "distinct (map fst l) \<Longrightarrow>
  set (map fst (fst (ls_delete k l))) = (set (map fst l)) - {k}"
  apply (induct l rule: ls_delete.induct)
  apply simp
  apply (auto simp add: Let_def)
  done

lemma ls_delete_distinct: "distinct (map fst l) \<Longrightarrow> distinct (map fst (fst (ls_delete k l)))"
proof (induct l rule: ls_delete.induct)
  case 1 thus ?case by simp
next
  case (2 k l w ls) show ?case
  proof (cases "k = l")
    case True
    with 2 show ?thesis by simp
  next
    case False
    with 2 have d: "distinct (map fst (fst (ls_delete k ls)))"
      by simp
    from 2 have d2: "distinct (map fst ls)" by simp
    from 2(2) have "l \<notin> set (map fst ls)" by simp
    with False 2 ls_delete_fst_map_set[OF d2, of k]
    have "l \<notin> set (map fst (fst (ls_delete k ls)))"
      by simp
    with d False show ?thesis by (simp add: Let_def)
  qed
qed

lemma ls_delete_length:
  "length (fst (ls_delete k l)) = (
    if (k \<in> set (map fst l)) then
      (length l - 1)
    else
      length l)"
proof (induct l rule: ls_delete.induct)
  case 1
  then show ?case by simp
next
  case (2 k l w ls)
  then show ?case by (cases ls) (auto simp add: Let_def)
qed

lemma ls_delete_length_snd_True:
  "snd (ls_delete k l) \<Longrightarrow> length (fst (ls_delete k l)) = length l - 1"
  by (simp add: ls_delete_length ls_delete_snd_set)

lemma ls_delete_length_snd_False:
  "\<not> snd (ls_delete k l) \<Longrightarrow> length (fst (ls_delete k l)) = length l"
  by (simp add: ls_delete_length ls_delete_snd_set)


definition ht_delete
  :: "'k
    \<Rightarrow> ('k::{heap,hashable}, 'v::heap) hashtable
    \<Rightarrow> ('k, 'v) hashtable Heap"
  where
  "ht_delete k ht = do {
      m \<leftarrow> Array.len (the_array ht);
      let i = bounded_hashcode_nat m k;
      l \<leftarrow> Array.nth (the_array ht) i;
      let l = ls_delete k l;
      Array.upd i (fst l) (the_array ht);
      let n = (if (snd l) then (the_size ht - 1) else the_size ht);
      return (HashTable (the_array ht) n)
    }"


subsubsection \<open>Complete Correctness\<close>

lemma ht_hash_delete:
  assumes "ht_hash ls"
  shows "ht_hash (
    ls[bounded_hashcode_nat (length ls) k
      := fst (ls_delete k
               (ls ! bounded_hashcode_nat (length ls) k)
             )
      ]
  )"
  unfolding ht_hash_def
  apply (intro allI ballI impI)
  apply simp
  subgoal premises prems for i x
  proof (cases "i = bounded_hashcode_nat (length ls) k")
    case i: True
    show ?thesis
    proof (cases "fst x = k")
      case True
      with i show ?thesis by simp
    next
      case False
      with prems i
      have
        "x \<in> set (fst (ls_delete k
                        (ls ! bounded_hashcode_nat (length ls) k)))"
        by auto
      with
        ls_delete_fst_set[
          of k "ls ! bounded_hashcode_nat (length ls) k"]
        False
      have "x \<in> (set (ls ! bounded_hashcode_nat (length ls) k))" by auto
      with i prems assms[unfolded ht_hash_def] show ?thesis by simp
    qed
  next
    case False
    with prems have "x \<in> set (ls ! i)" by simp
    with prems assms[unfolded ht_hash_def] show ?thesis by simp
  qed
  done

lemma ht_distinct_delete:
  assumes "ht_distinct l"
  shows "ht_distinct (
    l[bounded_hashcode_nat (length l) k
      := fst (ls_delete k (l ! bounded_hashcode_nat (length l) k))])"
  unfolding ht_distinct_def
  apply (intro allI impI)
  apply simp
  subgoal premises prems for i
  proof (cases "i = bounded_hashcode_nat (length l) k")
    case True
    with prems assms[unfolded ht_distinct_def]
    have "distinct (map fst (l ! bounded_hashcode_nat (length l) k))"
      by simp
    from ls_delete_distinct[OF this, of k] True prems
    show ?thesis by simp
  next
    case False
    with prems assms[unfolded ht_distinct_def] show ?thesis by simp
  qed
  done

lemma ht_size_delete1:
  assumes size: "ht_size l n"
  assumes i: "i < length l"
  assumes snd: "snd (ls_delete k (l ! i))"
  shows "ht_size (l[i := fst (ls_delete k (l!i))]) (n - 1)"
proof -
  have "(map length (l[i := fst (ls_delete k (l ! i))]))
    = (map length l)[i := length (fst (ls_delete k (l ! i)))]"
    by (simp add: map_update) also
  from sum_list_update[of i "map length l", simplified, OF i,
    of "length (fst (ls_delete k (l ! i)))"]
    ls_delete_length_snd_True[OF snd] snd
  have "sum_list ((map length l)[i := length (fst (ls_delete k (l ! i)))])
    = sum_list (map length l) - 1"
    by (cases "length (l ! i)") (simp_all add: ls_delete_snd_set)
  finally show ?thesis using assms by (simp add: ht_size_def assms)
qed

lemma ht_size_delete2:
  assumes size: "ht_size l n"
  assumes i: "i < length l"
  assumes snd: "\<not> snd (ls_delete k (l ! i))"
  shows "ht_size (l[i := fst (ls_delete k (l!i))]) n"
proof -
  have "(map length (l[i := fst (ls_delete k (l ! i))]))
    = (map length l)[i := length (fst (ls_delete k (l ! i)))]"
    by (simp add: map_update) also
  from sum_list_update[of i "map length l", simplified, OF i,
    of "length (fst (ls_delete k (l ! i)))"]
    ls_delete_length_snd_False[OF snd]
  have "sum_list ((map length l)[i := length (fst (ls_delete k (l ! i)))])
    = sum_list (map length l)" by simp
  finally show ?thesis using assms by (simp add: ht_size_def assms)
qed


lemma complete_ht_delete: "<is_hashtable l ht> ht_delete k ht
  <is_hashtable (l[bounded_hashcode_nat (length l) k
    := fst (ls_delete k (l ! bounded_hashcode_nat (length l) k))])>"
  unfolding ht_delete_def is_hashtable_def
  apply (rule norm_pre_pure_rule)
  apply (rule bind_rule)
  apply (rule length_rule)
  apply (rule norm_pre_pure_rule)
  apply (simp add: Let_def)
  apply (rule bind_rule)
  apply (rule nth_rule)
  apply (simp add: bounded_hashcode_nat_bounds)
  apply (rule norm_pre_pure_rule)
  apply (rule bind_rule)
  apply (rule upd_rule)
  apply (simp add: bounded_hashcode_nat_bounds)
  apply (rule return_cons_rule)
  apply (auto
    simp add: ht_size_delete1 ht_size_delete2 bounded_hashcode_nat_bounds
              is_hashtable_def ht_hash_delete ht_distinct_delete)
  using ht_size_delete1[OF _ bounded_hashcode_nat_bounds[of "length l" k], of "the_size ht"]
  apply simp
  done

text \<open>Alternative, more automatic proof\<close>
lemma "<is_hashtable l ht> ht_delete k ht
  <is_hashtable (l[bounded_hashcode_nat (length l)
    k := fst (ls_delete k (l ! bounded_hashcode_nat (length l) k))])>"
  unfolding ht_delete_def is_hashtable_def Let_def
  using ht_size_delete1[OF _ bounded_hashcode_nat_bounds[of "length l" k],
    of "the_size ht"]
  apply (sep_auto simp:
    ht_size_delete1 ht_size_delete2 bounded_hashcode_nat_bounds
    is_hashtable_def ht_hash_delete ht_distinct_delete)
  done


subsection \<open>Re-Hashing\<close>

subsubsection \<open>Auxiliary Functions\<close>

text \<open>\paragraph{Insert List}\<close>
fun ht_insls
  :: "('k \<times> 'v) list
    \<Rightarrow> ('k::{heap,hashable}, 'v::heap) hashtable
    \<Rightarrow> ('k, 'v::heap) hashtable Heap"
  where
  "ht_insls [] ht = return ht" |
  "ht_insls ((k, v) # l) ht = do { h \<leftarrow> ht_upd k v ht; ht_insls l h }"

text "Abstract version"
fun ls_insls :: "('k::hashable \<times> 'v) list
  \<Rightarrow> ('k \<times> 'v) list list \<Rightarrow> ('k \<times> 'v) list list"
where
  "ls_insls [] l = l" |
  "ls_insls ((k, v) # ls) l =
    ls_insls ls (abs_update k v l)"

lemma ht_hash_ls_insls:
  assumes "ht_hash l"
  shows "ht_hash (ls_insls ls l)"
  using assms
  apply (induct l rule: ls_insls.induct)
  apply simp
  apply (simp add: ht_hash_update)
  done

lemma ht_distinct_ls_insls:
  assumes "ht_distinct l"
  shows "ht_distinct (ls_insls ls l)"
  using assms
  apply (induct l rule: ls_insls.induct)
  apply simp
  apply (simp add: ht_distinct_update)
  done

lemma length_ls_insls:
  assumes "1 < length l"
  shows "1 < length (ls_insls ls l)"
  using assms
proof (induct l rule: ls_insls.induct)
  case 1
  then show ?case by simp
next
  case (2 k v ls l)
  from 2(1)[OF length_update[OF 2(2), of k v]] show ?case
    by simp
qed

lemma complete_ht_insls:
  "<is_hashtable ls ht> ht_insls xs ht <is_hashtable (ls_insls xs ls)>"
proof (induct xs arbitrary: ls ht)
  case Nil
  show ?case by (auto intro: return_cons_rule)
next
  case (Cons x xs)
  show ?case
  proof (cases x)
    case (Pair k v)
    then show ?thesis
      apply simp
      apply (rule bind_rule)
      apply (rule complete_ht_upd)
      apply (simp add: Cons)
      done
  qed
qed

text \<open>\paragraph{Copy}\<close>
fun ht_copy :: "nat \<Rightarrow> ('k::{heap,hashable}, 'v::heap) hashtable
  \<Rightarrow> ('k, 'v) hashtable \<Rightarrow> ('k, 'v) hashtable Heap"
  where
  "ht_copy 0 src dst = return dst" |
  "ht_copy (Suc n) src dst = do {
    l \<leftarrow> Array.nth (the_array src) n;
    ht \<leftarrow> ht_insls l dst;
    ht_copy n src ht
  }"

text "Abstract version"
fun ls_copy :: "nat \<Rightarrow> ('k::hashable \<times> 'v) list list
  \<Rightarrow> ('k \<times> 'v) list list \<Rightarrow> ('k \<times> 'v) list list"
  where
  "ls_copy 0 ss ds = ds" |
  "ls_copy (Suc n) ss ds = ls_copy n ss (ls_insls (ss ! n) ds)"

lemma ht_hash_ls_copy:
  assumes "ht_hash l"
  shows "ht_hash (ls_copy n ss l)"
  using assms
  apply (induct n arbitrary: l)
  apply simp
  apply (simp add: ht_hash_ls_insls)
  done

lemma ht_distinct_ls_copy:
  assumes "ht_distinct l"
  shows "ht_distinct (ls_copy n ss l)"
  using assms
  apply (induct n arbitrary: l)
  apply simp
  apply (simp add: ht_distinct_ls_insls)
  done

lemma length_ls_copy:
  assumes "1 < length l"
  shows "1 < length (ls_copy n ss l)"
  using assms
proof (induct n arbitrary: l)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc(1)[OF length_ls_insls[OF Suc(2)]] show ?case by simp
qed

lemma complete_ht_copy: "n \<le> List.length ss \<Longrightarrow>
  <is_hashtable ss src * is_hashtable ds dst>
  ht_copy n src dst
  <\<lambda>r. is_hashtable ss src * is_hashtable (ls_copy n ss ds) r>"
proof (induct n arbitrary: ds dst)
  case 0
  show ?case by (auto intro!: return_cons_rule)
next
  case (Suc n)
  then have n: "n < length ss" by simp
  then have "n \<le> length ss" by simp
  note IH = Suc(1)[OF this]
  show ?case
    apply simp
    apply (rule bind_rule)
    apply (rule frame_rule)
    apply (subgoal_tac "<is_hashtable ss src>
      Array.nth (the_array src) n
      <\<lambda>r. is_hashtable ss src * \<up>(r = ss ! n)>")
    apply simp
    apply (simp add: is_hashtable_def)
    apply (auto intro!: nth_rule simp add: n)[]
    apply clarsimp
    apply (rule bind_rule)
    apply (rule frame_rule_left)
    apply (rule complete_ht_insls)
    apply (simp add: IH)
    done
qed

text \<open>Alternative, more automatic proof\<close>
lemma complete_ht_copy_alt_proof: "n \<le> List.length ss \<Longrightarrow>
  <is_hashtable ss src * is_hashtable ds dst>
  ht_copy n src dst
  <\<lambda>r. is_hashtable ss src * is_hashtable (ls_copy n ss ds) r>"
proof (induct n arbitrary: ds dst)
  case 0
  show ?case by (sep_auto)
next
  case (Suc n)
  then have N_LESS: "n < length ss" by simp
  then have N_LE: "n \<le> length ss" by simp
  note IH = Suc(1)[OF this]
  show ?case
    by (sep_auto simp: N_LESS N_LE heap: complete_ht_insls IH)
qed

definition ht_rehash
  :: "('k::{heap,hashable}, 'v::heap) hashtable \<Rightarrow> ('k, 'v) hashtable Heap"
  where
  "ht_rehash ht = do {
    n \<leftarrow> Array.len (the_array ht);
    h \<leftarrow> ht_new_sz (2 * n);
    ht_copy n ht h
  }"

text "Operation on Abstraction"
definition ls_rehash :: "('k::hashable \<times> 'v) list list \<Rightarrow> ('k \<times> 'v) list list"
  where "ls_rehash l = ls_copy (List.length l) l (replicate (2 * length l) [])"

lemma ht_hash_ls_rehash: "ht_hash (ls_rehash l)"
  by (simp add: ht_hash_ls_copy ls_rehash_def)

lemma ht_distinct_ls_rehash: "ht_distinct (ls_rehash l)"
  by (simp add: ht_distinct_ls_copy ls_rehash_def)

lemma length_ls_rehash:
  assumes "1 < length l"
  shows "1 < length (ls_rehash l)"
proof -
  from assms have "1 < length (replicate (2 * length l) [])" by simp
  from length_ls_copy[OF this, of "length l" l] show ?thesis
    by (simp add: ls_rehash_def)
qed

lemma ht_imp_len: "is_hashtable l ht \<Longrightarrow>\<^sub>A is_hashtable l ht * \<up>(length l > 0)"
  unfolding is_hashtable_def
  by sep_auto

lemma complete_ht_rehash:
  "<is_hashtable l ht> ht_rehash ht
  <\<lambda>r. is_hashtable l ht * is_hashtable (ls_rehash l) r>"
  apply (rule cons_pre_rule[OF ht_imp_len])
  unfolding ht_rehash_def
  apply (sep_auto heap: complete_ht_new_sz)
  apply (cases l; simp)
  apply (sep_auto heap: complete_ht_copy simp: ls_rehash_def)
  done

definition load_factor :: nat \<comment> \<open>in percent\<close>
  where "load_factor = 75"

definition ht_update
  :: "'k::{heap,hashable} \<Rightarrow> 'v::heap \<Rightarrow> ('k, 'v) hashtable
  \<Rightarrow> ('k, 'v) hashtable Heap"
  where
  "ht_update k v ht = do {
    m \<leftarrow> Array.len (the_array ht);
    ht \<leftarrow> (if m * load_factor \<le> (the_size ht) * 100 then
        ht_rehash ht
      else return ht);
    ht_upd k v ht
  }"


lemma complete_ht_update_normal:
  "\<not> length l * load_factor \<le> (the_size ht)* 100 \<Longrightarrow>
  <is_hashtable l ht>
  ht_update k v ht
  <is_hashtable (abs_update k v l)>"
  unfolding ht_update_def
  apply (sep_auto simp: is_hashtable_def)
  apply (rule cons_pre_rule[where P' = "is_hashtable l ht"])
  apply (simp add: is_hashtable_def)
  apply (simp add: complete_ht_upd)
  done

lemma complete_ht_update_rehash:
  "length l * load_factor \<le> (the_size ht)* 100 \<Longrightarrow>
  <is_hashtable l ht>
  ht_update k v ht
  <\<lambda>r. is_hashtable l ht
    * is_hashtable (abs_update k v (ls_rehash l)) r>"
  unfolding ht_update_def
  by (sep_auto heap: complete_ht_rehash complete_ht_upd)


subsection \<open>Conversion to List\<close>

definition ht_to_list ::
  "('k::heap, 'v::heap) hashtable \<Rightarrow> ('k \<times> 'v) list Heap" where
  "ht_to_list ht = do {
    l \<leftarrow> (Array.freeze (the_array ht));
    return (concat l)
  }"

lemma complete_ht_to_list: "<is_hashtable l ht> ht_to_list ht
  <\<lambda>r. is_hashtable l ht * \<up>(r = concat l)>"
  unfolding ht_to_list_def is_hashtable_def
  by sep_auto

end
