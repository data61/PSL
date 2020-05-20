(*  Title:      Containers/RBT_Mapping2.thy
    Author:     Andreas Lochbihler, KIT *)

theory RBT_Mapping2
imports
  Collection_Order
  RBT_ext
  Deriving.RBT_Comparator_Impl
begin

section \<open>Mappings implemented by red-black trees\<close>

lemma distinct_map_filterI: "distinct (map f xs) \<Longrightarrow> distinct (map f (filter P xs))"
by(induct xs) auto

lemma map_of_filter_apply:
  "distinct (map fst xs)
  \<Longrightarrow> map_of (filter P xs) k = 
  (case map_of xs k of None \<Rightarrow> None | Some v \<Rightarrow> if P (k, v) then Some v else None)"
by(induct xs)(auto simp add: map_of_eq_None_iff split: option.split)

subsection \<open>Type definition\<close>

typedef (overloaded) ('a, 'b) mapping_rbt
  = "{t :: ('a :: ccompare, 'b) RBT_Impl.rbt. ord.is_rbt cless t \<or> ID CCOMPARE('a) = None}"
  morphisms impl_of Mapping_RBT'
proof
  show "RBT_Impl.Empty \<in> ?mapping_rbt" by(simp add: ord.Empty_is_rbt)
qed

definition Mapping_RBT :: "('a :: ccompare, 'b) rbt \<Rightarrow> ('a, 'b) mapping_rbt"
where
  "Mapping_RBT t = Mapping_RBT'
  (if ord.is_rbt cless t \<or> ID CCOMPARE('a) = None then t
   else RBT_Impl.fold (ord.rbt_insert cless) t rbt.Empty)"

lemma Mapping_RBT_inverse:
  fixes y :: "('a :: ccompare, 'b) rbt"
  assumes "y \<in> {t. ord.is_rbt cless t \<or> ID CCOMPARE('a) = None}"
  shows "impl_of (Mapping_RBT y) = y"
using assms by(auto simp add: Mapping_RBT_def Mapping_RBT'_inverse)

lemma impl_of_inverse: "Mapping_RBT (impl_of t) = t"
by(cases t)(auto simp add: Mapping_RBT'_inverse Mapping_RBT_def)

lemma type_definition_mapping_rbt': 
  "type_definition impl_of Mapping_RBT 
    {t :: ('a, 'b) rbt. ord.is_rbt cless t \<or> ID CCOMPARE('a :: ccompare) = None}"
by unfold_locales(rule mapping_rbt.impl_of impl_of_inverse Mapping_RBT_inverse)+

lemmas Mapping_RBT_cases[cases type: mapping_rbt] = 
  type_definition.Abs_cases[OF type_definition_mapping_rbt'] 
  and Mapping_RBT_induct[induct type: mapping_rbt] =
  type_definition.Abs_induct[OF type_definition_mapping_rbt'] and
  Mapping_RBT_inject = type_definition.Abs_inject[OF type_definition_mapping_rbt']

lemma rbt_eq_iff:
  "t1 = t2 \<longleftrightarrow> impl_of t1 = impl_of t2"
  by (simp add: impl_of_inject)

lemma rbt_eqI:
  "impl_of t1 = impl_of t2 \<Longrightarrow> t1 = t2"
  by (simp add: rbt_eq_iff)

lemma Mapping_RBT_impl_of [simp]:
  "Mapping_RBT (impl_of t) = t"
  by (simp add: impl_of_inverse)

subsection \<open>Operations\<close>

setup_lifting type_definition_mapping_rbt'

context fixes dummy :: "'a :: ccompare" begin

lift_definition lookup :: "('a, 'b) mapping_rbt \<Rightarrow> 'a \<rightharpoonup> 'b" is "rbt_comp_lookup ccomp" .

lift_definition empty :: "('a, 'b) mapping_rbt" is "RBT_Impl.Empty"
by(simp add: ord.Empty_is_rbt)

lift_definition insert :: "'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) mapping_rbt \<Rightarrow> ('a, 'b) mapping_rbt" is
  "rbt_comp_insert ccomp"
by(auto 4 3 intro: linorder.rbt_insert_is_rbt ID_ccompare simp: rbt_comp_insert[OF ID_ccompare'])

lift_definition delete :: "'a \<Rightarrow> ('a, 'b) mapping_rbt \<Rightarrow> ('a, 'b) mapping_rbt" is
  "rbt_comp_delete ccomp"
by(auto 4 3 intro: linorder.rbt_delete_is_rbt ID_ccompare simp: rbt_comp_delete[OF ID_ccompare'])

lift_definition bulkload :: "('a \<times> 'b) list \<Rightarrow> ('a, 'b) mapping_rbt" is
  "rbt_comp_bulkload ccomp"
by(auto 4 3 intro: linorder.rbt_bulkload_is_rbt ID_ccompare simp: rbt_comp_bulkload[OF ID_ccompare'])

lift_definition map_entry :: "'a \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) mapping_rbt \<Rightarrow> ('a, 'b) mapping_rbt" is
  "rbt_comp_map_entry ccomp"
by(auto simp: ord.rbt_map_entry_is_rbt rbt_comp_map_entry[OF ID_ccompare'])

lift_definition map :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a, 'b) mapping_rbt \<Rightarrow> ('a, 'c) mapping_rbt" is "RBT_Impl.map"
by(simp add: ord.map_is_rbt)

lift_definition entries :: "('a, 'b) mapping_rbt \<Rightarrow> ('a \<times> 'b) list" is "RBT_Impl.entries" .

lift_definition keys :: "('a, 'b) mapping_rbt \<Rightarrow> 'a set" is "set \<circ> RBT_Impl.keys" .

lift_definition fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> ('a, 'b) mapping_rbt \<Rightarrow> 'c \<Rightarrow> 'c" is "RBT_Impl.fold" .

lift_definition is_empty :: "('a, 'b) mapping_rbt \<Rightarrow> bool" is "case_rbt True (\<lambda>_ _ _ _ _. False)" .

lift_definition filter :: "('a \<times> 'b \<Rightarrow> bool) \<Rightarrow> ('a, 'b) mapping_rbt \<Rightarrow> ('a, 'b) mapping_rbt" is
  "\<lambda>P t. rbtreeify (List.filter P (RBT_Impl.entries t))"
by(auto intro!: linorder.is_rbt_rbtreeify ID_ccompare linorder.sorted_filter linorder.rbt_sorted_entries ord.is_rbt_rbt_sorted linorder.distinct_entries distinct_map_filterI simp add: filter_map[symmetric])

lift_definition join ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) mapping_rbt \<Rightarrow> ('a, 'b) mapping_rbt \<Rightarrow> ('a, 'b) mapping_rbt"
is "rbt_comp_union_with_key ccomp"
by(auto 4 3 intro: linorder.is_rbt_rbt_unionwk ID_ccompare simp: rbt_comp_union_with_key[OF ID_ccompare'])

lift_definition meet ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) mapping_rbt \<Rightarrow> ('a, 'b) mapping_rbt \<Rightarrow> ('a, 'b) mapping_rbt" 
is "rbt_comp_inter_with_key ccomp"
by(auto 4 3 intro: linorder.rbt_interwk_is_rbt ID_ccompare ord.is_rbt_rbt_sorted simp: rbt_comp_inter_with_key[OF ID_ccompare'])

lift_definition all :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a, 'b) mapping_rbt \<Rightarrow> bool" 
is "RBT_Impl_rbt_all" .

lift_definition ex :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a, 'b) mapping_rbt \<Rightarrow> bool"
is "RBT_Impl_rbt_ex" .

lift_definition product ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e) \<Rightarrow> ('a, 'b) mapping_rbt
  \<Rightarrow> ('c :: ccompare, 'd) mapping_rbt \<Rightarrow> ('a \<times> 'c, 'e) mapping_rbt"
is "rbt_product"
  by (fastforce intro: is_rbt_rbt_product ID_ccompare simp add: lt_of_comp_less_prod ccompare_prod_def ID_Some ID_None split: option.split_asm)

lift_definition diag ::
  "('a, 'b) mapping_rbt \<Rightarrow> ('a \<times> 'a, 'b) mapping_rbt"
is "RBT_Impl_diag"
by(auto simp add: lt_of_comp_less_prod ccompare_prod_def ID_Some ID_None is_rbt_RBT_Impl_diag split: option.split_asm)

lift_definition init :: "('a, 'b) mapping_rbt \<Rightarrow> ('a, 'b, 'c) rbt_generator_state"
is "rbt_init" .

end

subsection \<open>Properties\<close>

lemma unfoldr_rbt_entries_generator:
  "list.unfoldr rbt_entries_generator (init t) = entries t"
  by transfer(simp add: unfoldr_rbt_entries_generator)

lemma lookup_RBT:
  "ord.is_rbt cless t \<Longrightarrow>
  lookup (Mapping_RBT t) = rbt_comp_lookup ccomp t"
by(simp add: lookup_def Mapping_RBT_inverse)

lemma lookup_impl_of:
  "rbt_comp_lookup ccomp (impl_of t) = lookup t"
by(transfer) simp

lemma entries_impl_of:
  "RBT_Impl.entries (impl_of t) = entries t"
by transfer simp

lemma keys_impl_of:
  "set (RBT_Impl.keys (impl_of t)) = keys t"
  by (simp add: keys_def)

lemma lookup_empty [simp]:
  "lookup empty = Map.empty"
by transfer (simp add: fun_eq_iff ord.rbt_lookup.simps)

lemma fold_conv_fold:
  "fold f t = List.fold (case_prod f) (entries t)"
by transfer(simp add: RBT_Impl.fold_def)

lemma is_empty_empty [simp]:
  "is_empty t \<longleftrightarrow> t = empty"
by transfer (simp split: rbt.split)

context assumes ID_ccompare_neq_None: "ID CCOMPARE('a :: ccompare) \<noteq> None"
begin

lemma mapping_linorder: "class.linorder (cless_eq :: 'a \<Rightarrow> 'a \<Rightarrow> bool) cless"
using ID_ccompare_neq_None by(clarsimp)(rule ID_ccompare)

lemma mapping_comparator: "comparator (ccomp :: 'a comparator)"
using ID_ccompare_neq_None by(clarsimp)(rule ID_ccompare')

lemmas rbt_comp[simp] = rbt_comp_simps[OF mapping_comparator]

lemma is_rbt_impl_of [simp, intro]:
  fixes t :: "('a, 'b) mapping_rbt"
  shows "ord.is_rbt cless (impl_of t)"
using ID_ccompare_neq_None impl_of [of t] by auto

lemma lookup_insert [simp]:
  "lookup (insert (k :: 'a) v t) = (lookup t)(k \<mapsto> v)"
by transfer (simp add: ID_ccompare_neq_None 
  linorder.rbt_lookup_rbt_insert[OF mapping_linorder])

lemma lookup_delete [simp]:
  "lookup (delete (k :: 'a) t) = (lookup t)(k := None)"
by transfer(simp add: ID_ccompare_neq_None linorder.rbt_lookup_rbt_delete[OF mapping_linorder] restrict_complement_singleton_eq)

lemma map_of_entries [simp]:
  "map_of (entries (t :: ('a, 'b) mapping_rbt)) = lookup t"
by transfer(simp add: ID_ccompare_neq_None linorder.map_of_entries[OF mapping_linorder] ord.is_rbt_rbt_sorted)

lemma entries_lookup:
  "entries (t1 :: ('a, 'b) mapping_rbt) = entries t2 \<longleftrightarrow> lookup t1 = lookup t2"
by transfer(simp add: ID_ccompare_neq_None linorder.entries_rbt_lookup[OF mapping_linorder] ord.is_rbt_rbt_sorted)

lemma lookup_bulkload [simp]:
  "lookup (bulkload xs) = map_of (xs :: ('a \<times> 'b) list)"
by transfer(simp add: linorder.rbt_lookup_rbt_bulkload[OF mapping_linorder])

lemma lookup_map_entry [simp]:
  "lookup (map_entry (k :: 'a) f t) = (lookup t)(k := map_option f (lookup t k))"
by transfer(simp add: ID_ccompare_neq_None linorder.rbt_lookup_rbt_map_entry[OF mapping_linorder])

lemma lookup_map [simp]:
  "lookup (map f t) (k :: 'a) = map_option (f k) (lookup t k)"
by transfer(simp add: linorder.rbt_lookup_map[OF mapping_linorder])

lemma RBT_lookup_empty [simp]:
  "ord.rbt_lookup cless (t :: ('a, 'b) RBT_Impl.rbt) = Map.empty \<longleftrightarrow> t = RBT_Impl.Empty"
proof -
  interpret linorder "cless_eq :: 'a \<Rightarrow> 'a \<Rightarrow> bool" cless by(rule mapping_linorder)
  show ?thesis by(cases t)(auto simp add: fun_eq_iff)
qed

lemma lookup_empty_empty [simp]:
  "lookup t = Map.empty \<longleftrightarrow> (t :: ('a, 'b) mapping_rbt) = empty"
by transfer simp

lemma finite_dom_lookup [simp]: "finite (dom (lookup (t :: ('a, 'b) mapping_rbt)))"
by transfer(auto simp add: linorder.finite_dom_rbt_lookup[OF mapping_linorder])

lemma card_com_lookup [unfolded length_map, simp]:
  "card (dom (lookup (t :: ('a, 'b) mapping_rbt))) = length (List.map fst (entries t))"
by transfer(auto simp add: linorder.rbt_lookup_keys[OF mapping_linorder] linorder.distinct_entries[OF mapping_linorder] RBT_Impl.keys_def ord.is_rbt_rbt_sorted ID_ccompare_neq_None List.card_set simp del: set_map length_map)

lemma lookup_join:
  "lookup (join f (t1 :: ('a, 'b) mapping_rbt) t2) =
  (\<lambda>k. case lookup t1 k of None \<Rightarrow> lookup t2 k | Some v1 \<Rightarrow> Some (case lookup t2 k of None \<Rightarrow> v1 | Some v2 \<Rightarrow> f k v1 v2))"
by transfer(auto simp add: fun_eq_iff linorder.rbt_lookup_rbt_unionwk[OF mapping_linorder] ord.is_rbt_rbt_sorted ID_ccompare_neq_None split: option.splits)

lemma lookup_meet:
  "lookup (meet f (t1 :: ('a, 'b) mapping_rbt) t2) =
  (\<lambda>k. case lookup t1 k of None \<Rightarrow> None | Some v1 \<Rightarrow> case lookup t2 k of None \<Rightarrow> None | Some v2 \<Rightarrow> Some (f k v1 v2))"
by transfer(auto simp add: fun_eq_iff linorder.rbt_lookup_rbt_interwk[OF mapping_linorder] ord.is_rbt_rbt_sorted ID_ccompare_neq_None split: option.splits)

lemma lookup_filter [simp]:
  "lookup (filter P (t :: ('a, 'b) mapping_rbt)) k = 
  (case lookup t k of None \<Rightarrow> None | Some v \<Rightarrow> if P (k, v) then Some v else None)"
by transfer(simp split: option.split add: ID_ccompare_neq_None linorder.rbt_lookup_rbtreeify[OF mapping_linorder] linorder.sorted_filter[OF mapping_linorder] ord.is_rbt_rbt_sorted linorder.rbt_sorted_entries[OF mapping_linorder] distinct_map_filterI linorder.distinct_entries[OF mapping_linorder] map_of_filter_apply linorder.map_of_entries[OF mapping_linorder])

lemma all_conv_all_lookup:
  "all P t \<longleftrightarrow> (\<forall>(k :: 'a) v. lookup t k = Some v \<longrightarrow> P k v)"
by transfer(auto simp add: ID_ccompare_neq_None linorder.rbt_lookup_keys[OF mapping_linorder] ord.is_rbt_rbt_sorted RBT_Impl.keys_def RBT_Impl_rbt_all_def linorder.map_of_entries[OF mapping_linorder, symmetric] linorder.distinct_entries[OF mapping_linorder] dest: map_of_SomeD intro: map_of_is_SomeI)

lemma ex_conv_ex_lookup:
  "ex P t \<longleftrightarrow> (\<exists>(k :: 'a) v. lookup t k = Some v \<and> P k v)"
by transfer(auto simp add: ID_ccompare_neq_None linorder.rbt_lookup_keys[OF mapping_linorder] ord.is_rbt_rbt_sorted RBT_Impl.keys_def RBT_Impl_rbt_ex_def linorder.map_of_entries[OF mapping_linorder, symmetric] linorder.distinct_entries[OF mapping_linorder] intro: map_of_is_SomeI)

lemma diag_lookup:
  "lookup (diag t) = (\<lambda>(k :: 'a, k'). if k = k' then lookup t k else None)"
using linorder.rbt_lookup_RBT_Impl_diag[where ?'b='b, OF mapping_linorder]
apply transfer
apply (clarsimp simp add: ID_ccompare_neq_None ccompare_prod_def lt_of_comp_less_prod[symmetric] 
  rbt_comp_lookup[OF comparator_prod[OF mapping_comparator mapping_comparator], symmetric]
  ID_Some split: option.split) 
apply (unfold rbt_comp_lookup[OF mapping_comparator], simp)
done

context assumes ID_ccompare_neq_None': "ID CCOMPARE('b :: ccompare) \<noteq> None"
begin

lemma mapping_linorder': "class.linorder (cless_eq :: 'b \<Rightarrow> 'b \<Rightarrow> bool) cless"
using ID_ccompare_neq_None' by(clarsimp)(rule ID_ccompare)

lemma mapping_comparator': "comparator (ccomp :: 'b comparator)"
using ID_ccompare_neq_None' by(clarsimp)(rule ID_ccompare')

lemmas rbt_comp'[simp] = rbt_comp_simps[OF mapping_comparator']

lemma ccomp_comparator_prod:
  "ccomp = (comparator_prod ccomp ccomp :: ('a \<times> 'b)comparator)"
  by(simp add: ccompare_prod_def lt_of_comp_less_prod ID_ccompare_neq_None ID_ccompare_neq_None' ID_Some split: option.splits)

lemma lookup_product: 
  "lookup (product f rbt1 rbt2) (a :: 'a, b :: 'b) = 
  (case lookup rbt1 a of None \<Rightarrow> None
   | Some c \<Rightarrow> map_option (f a c b) (lookup rbt2 b))"
using mapping_linorder mapping_linorder'
apply transfer
apply (unfold ccomp_comparator_prod rbt_comp_lookup[OF comparator_prod[OF mapping_comparator mapping_comparator']]
  rbt_comp rbt_comp' lt_of_comp_less_prod)
apply (simp add: ID_ccompare_neq_None ID_ccompare_neq_None' rbt_lookup_rbt_product)
done
end

end

hide_const (open) impl_of lookup empty insert delete
  entries keys bulkload map_entry map fold join meet filter all ex product diag init

end
