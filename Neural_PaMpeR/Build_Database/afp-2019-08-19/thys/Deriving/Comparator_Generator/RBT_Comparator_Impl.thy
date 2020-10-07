subsection \<open>A Comparator-Interface to Red-Black-Trees\<close>

theory RBT_Comparator_Impl
imports 
  "HOL-Library.RBT_Impl"
  Comparator
begin

text \<open>For all of the main algorithms of red-black trees, we
  provide alternatives which are completely based on comparators,
  and which are provable equivalent. At the time of writing,
  this interface is used in the Container AFP-entry.
  
  It does not rely on the modifications of code-equations as in 
  the previous subsection.\<close>

context 
  fixes c :: "'a comparator"
begin

primrec rbt_comp_lookup :: "('a, 'b) rbt \<Rightarrow> 'a \<rightharpoonup> 'b"
where
  "rbt_comp_lookup RBT_Impl.Empty k = None"
| "rbt_comp_lookup (Branch _ l x y r) k = 
   (case c k x of Lt \<Rightarrow> rbt_comp_lookup l k 
     | Gt \<Rightarrow> rbt_comp_lookup r k 
     | Eq \<Rightarrow> Some y)"

fun
  rbt_comp_ins :: "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"
where
  "rbt_comp_ins f k v RBT_Impl.Empty = Branch RBT_Impl.R RBT_Impl.Empty k v  RBT_Impl.Empty" |
  "rbt_comp_ins f k v (Branch RBT_Impl.B l x y r) = (case c k x of 
      Lt \<Rightarrow> balance (rbt_comp_ins f k v l) x y r
    | Gt \<Rightarrow> balance l x y (rbt_comp_ins f k v r)
    | Eq \<Rightarrow> Branch RBT_Impl.B l x (f k y v) r)" |
  "rbt_comp_ins f k v (Branch RBT_Impl.R l x y r) = (case c k x of 
      Lt \<Rightarrow> Branch RBT_Impl.R (rbt_comp_ins f k v l) x y r
    | Gt \<Rightarrow> Branch RBT_Impl.R l x y (rbt_comp_ins f k v r)
    | Eq \<Rightarrow> Branch RBT_Impl.R l x (f k y v) r)"

definition rbt_comp_insert_with_key :: "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"
where "rbt_comp_insert_with_key f k v t = paint RBT_Impl.B (rbt_comp_ins f k v t)"

definition rbt_comp_insert :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt" where
  "rbt_comp_insert = rbt_comp_insert_with_key (\<lambda>_ _ nv. nv)"

fun
  rbt_comp_del_from_left :: "'a \<Rightarrow> ('a,'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt" and
  rbt_comp_del_from_right :: "'a \<Rightarrow> ('a,'b) rbt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt" and
  rbt_comp_del :: "'a\<Rightarrow> ('a,'b) rbt \<Rightarrow> ('a,'b) rbt"
where
  "rbt_comp_del x RBT_Impl.Empty = RBT_Impl.Empty" |
  "rbt_comp_del x (Branch _ a y s b) = 
   (case c x y of 
        Lt \<Rightarrow> rbt_comp_del_from_left x a y s b 
      | Gt \<Rightarrow> rbt_comp_del_from_right x a y s b
      | Eq \<Rightarrow> combine a b)" |
  "rbt_comp_del_from_left x (Branch RBT_Impl.B lt z v rt) y s b = balance_left (rbt_comp_del x (Branch RBT_Impl.B lt z v rt)) y s b" |
  "rbt_comp_del_from_left x a y s b = Branch RBT_Impl.R (rbt_comp_del x a) y s b" |
  "rbt_comp_del_from_right x a y s (Branch RBT_Impl.B lt z v rt) = balance_right a y s (rbt_comp_del x (Branch RBT_Impl.B lt z v rt))" | 
  "rbt_comp_del_from_right x a y s b = Branch RBT_Impl.R a y s (rbt_comp_del x b)"

definition "rbt_comp_delete k t = paint RBT_Impl.B (rbt_comp_del k t)"

definition "rbt_comp_bulkload xs = foldr (\<lambda>(k, v). rbt_comp_insert k v) xs RBT_Impl.Empty"

primrec
  rbt_comp_map_entry :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt"
where
  "rbt_comp_map_entry k f RBT_Impl.Empty = RBT_Impl.Empty"
| "rbt_comp_map_entry k f (Branch cc lt x v rt) =
    (case c k x of 
        Lt \<Rightarrow> Branch cc (rbt_comp_map_entry k f lt) x v rt
      | Gt \<Rightarrow> Branch cc lt x v (rbt_comp_map_entry k f rt)
      | Eq \<Rightarrow> Branch cc lt x (f v) rt)"

function comp_sunion_with :: "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" 
where
  "comp_sunion_with f ((k, v) # as) ((k', v') # bs) =
   (case c k' k of 
        Lt \<Rightarrow> (k', v') # comp_sunion_with f ((k, v) # as) bs
      | Gt \<Rightarrow> (k, v) # comp_sunion_with f as ((k', v') # bs)
      | Eq \<Rightarrow> (k, f k v v') # comp_sunion_with f as bs)"
| "comp_sunion_with f [] bs = bs"
| "comp_sunion_with f as [] = as"
by pat_completeness auto
termination by lexicographic_order

function comp_sinter_with :: "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list"
where
  "comp_sinter_with f ((k, v) # as) ((k', v') # bs) =
  (case c k' k of 
      Lt \<Rightarrow> comp_sinter_with f ((k, v) # as) bs
    | Gt \<Rightarrow> comp_sinter_with f as ((k', v') # bs)
    | Eq \<Rightarrow> (k, f k v v') # comp_sinter_with f as bs)"
| "comp_sinter_with f [] _ = []"
| "comp_sinter_with f _ [] = []"
by pat_completeness auto
termination by lexicographic_order

definition rbt_comp_union_with_key :: "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt"
where
  "rbt_comp_union_with_key f t1 t2 =
  (case RBT_Impl.compare_height t1 t1 t2 t2
   of compare.EQ \<Rightarrow> rbtreeify (comp_sunion_with f (RBT_Impl.entries t1) (RBT_Impl.entries t2))
    | compare.LT \<Rightarrow> RBT_Impl.fold (rbt_comp_insert_with_key (\<lambda>k v w. f k w v)) t1 t2
    | compare.GT \<Rightarrow> RBT_Impl.fold (rbt_comp_insert_with_key f) t2 t1)"

definition rbt_comp_inter_with_key :: "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt \<Rightarrow> ('a, 'b) rbt"
where
  "rbt_comp_inter_with_key f t1 t2 =
  (case RBT_Impl.compare_height t1 t1 t2 t2 
   of compare.EQ \<Rightarrow> rbtreeify (comp_sinter_with f (RBT_Impl.entries t1) (RBT_Impl.entries t2))
    | compare.LT \<Rightarrow> rbtreeify (List.map_filter (\<lambda>(k, v). map_option (\<lambda>w. (k, f k v w)) (rbt_comp_lookup t2 k)) (RBT_Impl.entries t1))
    | compare.GT \<Rightarrow> rbtreeify (List.map_filter (\<lambda>(k, v). map_option (\<lambda>w. (k, f k w v)) (rbt_comp_lookup t1 k)) (RBT_Impl.entries t2)))"


context
  assumes c: "comparator c"
begin

lemma rbt_comp_lookup: "rbt_comp_lookup = ord.rbt_lookup (lt_of_comp c)" 
proof (intro ext)
  fix k and t :: "('a,'b)rbt"
  show "rbt_comp_lookup t k = ord.rbt_lookup (lt_of_comp c) t k"
    by (induct t, unfold rbt_comp_lookup.simps ord.rbt_lookup.simps
      comparator.two_comparisons_into_case_order[OF c]) 
      (auto split: order.splits)
qed  

lemma rbt_comp_ins: "rbt_comp_ins = ord.rbt_ins (lt_of_comp c)" 
proof (intro ext)
  fix f k v and t :: "('a,'b)rbt"
  show "rbt_comp_ins f k v t = ord.rbt_ins (lt_of_comp c) f k v t"
    by (induct f k v t rule: rbt_comp_ins.induct, unfold rbt_comp_ins.simps ord.rbt_ins.simps
      comparator.two_comparisons_into_case_order[OF c]) 
      (auto split: order.splits)
qed  

lemma rbt_comp_insert_with_key: "rbt_comp_insert_with_key = ord.rbt_insert_with_key (lt_of_comp c)"
  unfolding rbt_comp_insert_with_key_def[abs_def] ord.rbt_insert_with_key_def[abs_def]
  unfolding rbt_comp_ins ..

lemma rbt_comp_insert: "rbt_comp_insert = ord.rbt_insert (lt_of_comp c)"
  unfolding rbt_comp_insert_def[abs_def] ord.rbt_insert_def[abs_def]
  unfolding rbt_comp_insert_with_key ..

lemma rbt_comp_del: "rbt_comp_del = ord.rbt_del (lt_of_comp c)" 
proof - {
  fix k a b and s t :: "('a,'b)rbt"
  have 
    "rbt_comp_del_from_left k t a b s = ord.rbt_del_from_left (lt_of_comp c) k t a b s"
    "rbt_comp_del_from_right k t a b s = ord.rbt_del_from_right (lt_of_comp c) k t a b s"
    "rbt_comp_del k t = ord.rbt_del (lt_of_comp c) k t"
  by (induct k t a b s and k t a b s and k t rule: rbt_comp_del_from_left_rbt_comp_del_from_right_rbt_comp_del.induct,
    unfold 
      rbt_comp_del.simps ord.rbt_del.simps
      rbt_comp_del_from_left.simps ord.rbt_del_from_left.simps
      rbt_comp_del_from_right.simps ord.rbt_del_from_right.simps
      comparator.two_comparisons_into_case_order[OF c],
    auto split: order.split) 
  }
  thus ?thesis by (intro ext)
qed  

lemma rbt_comp_delete: "rbt_comp_delete = ord.rbt_delete (lt_of_comp c)"
  unfolding rbt_comp_delete_def[abs_def] ord.rbt_delete_def[abs_def]
  unfolding rbt_comp_del ..

lemma rbt_comp_bulkload: "rbt_comp_bulkload = ord.rbt_bulkload (lt_of_comp c)"
  unfolding rbt_comp_bulkload_def[abs_def] ord.rbt_bulkload_def[abs_def]
  unfolding rbt_comp_insert ..

lemma rbt_comp_map_entry: "rbt_comp_map_entry = ord.rbt_map_entry (lt_of_comp c)" 
proof (intro ext)
  fix f k and t :: "('a,'b)rbt"
  show "rbt_comp_map_entry f k t = ord.rbt_map_entry (lt_of_comp c) f k t"
    by (induct t, unfold rbt_comp_map_entry.simps ord.rbt_map_entry.simps
      comparator.two_comparisons_into_case_order[OF c]) 
      (auto split: order.splits)
qed  

lemma comp_sunion_with: "comp_sunion_with = ord.sunion_with (lt_of_comp c)"
proof (intro ext)
  fix f and as bs :: "('a \<times> 'b)list"
  show "comp_sunion_with f as bs = ord.sunion_with (lt_of_comp c) f as bs"
    by (induct f as bs rule: comp_sunion_with.induct,
      unfold comp_sunion_with.simps ord.sunion_with.simps
      comparator.two_comparisons_into_case_order[OF c]) 
      (auto split: order.splits)
qed

lemma comp_sinter_with: "comp_sinter_with = ord.sinter_with (lt_of_comp c)"
proof (intro ext)
  fix f and as bs :: "('a \<times> 'b)list"
  show "comp_sinter_with f as bs = ord.sinter_with (lt_of_comp c) f as bs"
    by (induct f as bs rule: comp_sinter_with.induct,
      unfold comp_sinter_with.simps ord.sinter_with.simps
      comparator.two_comparisons_into_case_order[OF c]) 
      (auto split: order.splits)
qed

lemma rbt_comp_union_with_key: "rbt_comp_union_with_key = ord.rbt_union_with_key (lt_of_comp c)"
  unfolding rbt_comp_union_with_key_def[abs_def] ord.rbt_union_with_key_def[abs_def]
  unfolding rbt_comp_insert_with_key comp_sunion_with .. 

lemma rbt_comp_inter_with_key: "rbt_comp_inter_with_key = ord.rbt_inter_with_key (lt_of_comp c)"
  unfolding rbt_comp_inter_with_key_def[abs_def] ord.rbt_inter_with_key_def[abs_def]
  unfolding rbt_comp_insert_with_key comp_sinter_with rbt_comp_lookup .. 

lemmas rbt_comp_simps = 
  rbt_comp_insert
  rbt_comp_lookup
  rbt_comp_delete
  rbt_comp_bulkload
  rbt_comp_map_entry
  rbt_comp_union_with_key
  rbt_comp_inter_with_key
end
end

end
