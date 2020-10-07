(*  Title:      Mapping_Exts.thy
    Author:     Denis Lohner, Sebastian Ullrich
*)

subsection "Mapping Extensions"

text \<open>Some lifted definition on mapping and efficient implementations.\<close>

theory Mapping_Exts
imports "HOL-Library.Mapping" FormalSSA_Misc
begin

lift_definition mapping_delete_all :: "('a \<Rightarrow> bool) \<Rightarrow> ('a,'b) mapping \<Rightarrow> ('a,'b) mapping"
  is "\<lambda>P m x. if (P x) then None else m x" .
lift_definition map_keys :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a,'c) mapping \<Rightarrow> ('b,'c) mapping"
  is "\<lambda>f m x. if f -` {x} \<noteq> {} then m (THE k. f -` {x} = {k}) else None" .
lift_definition map_values :: "('a \<Rightarrow> 'b \<Rightarrow> 'c option) \<Rightarrow> ('a,'b) mapping \<Rightarrow> ('a,'c) mapping"
  is "\<lambda>f m x. Option.bind (m x) (f x)" .
lift_definition restrict_mapping :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> ('a, 'b) mapping"
  is "\<lambda>f. restrict_map (Some \<circ> f)" .
lift_definition mapping_add :: "('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping"
  is "(++)" .

definition "mmap = Mapping.map id"

lemma lookup_map_keys: "Mapping.lookup (map_keys f m) x = (if f -` {x} \<noteq> {} then Mapping.lookup m (THE k. f -` {x} = {k}) else None)"
apply transfer ..

lemma Mapping_Mapping_lookup [simp, code_unfold]: "Mapping.Mapping (Mapping.lookup m) = m" by transfer simp
declare Mapping.lookup.abs_eq[simp]

lemma Mapping_eq_lookup: "m = m' \<longleftrightarrow> Mapping.lookup m = Mapping.lookup m'" by transfer simp

lemma map_of_map_if_conv:
  "map_of (map (\<lambda>k. (k, f k)) xs) x = (if (x \<in> set xs) then Some (f x) else None)"
  by (clarsimp simp: map_of_map_restrict)

lemma Mapping_lookup_map: "Mapping.lookup (Mapping.map f g m) a = map_option g (Mapping.lookup m (f a))"
  by transfer simp

lemma Mapping_lookup_map_default: "Mapping.lookup (Mapping.map_default k d f m) k' = (if k = k'
  then (Some \<circ> f) (case Mapping.lookup m k of None \<Rightarrow> d | Some x \<Rightarrow> x)
  else Mapping.lookup m k')"
  unfolding Mapping.map_default_def Mapping.default_def
  by transfer auto

lemma Mapping_lookup_mapping_add: "Mapping.lookup (mapping_add m1 m2) k =
  case_option (Mapping.lookup m1 k) Some (Mapping.lookup m2 k)"
  by transfer (simp add: map_add_def)

lemma Mapping_lookup_map_values: "Mapping.lookup (map_values f m) k =
  Option.bind (Mapping.lookup m k) (f k)"
  by transfer simp

lemma lookup_fold_update [simp]: "Mapping.lookup (fold (\<lambda>n. Mapping.update n (g n)) xs m) x
  = (if (x \<in> set xs) then Some (g x) else Mapping.lookup m x)"
  by transfer (rule fold_update_conv)

lemma mapping_eq_iff: "m1 = m2 \<longleftrightarrow> (\<forall>k. Mapping.lookup m1 k = Mapping.lookup m2 k)"
  by transfer auto

lemma lookup_delete: "Mapping.lookup (Mapping.delete k m) k' = (if k = k' then None else Mapping.lookup m k')"
  by transfer auto

lemma keys_map_values: "Mapping.keys (map_values f m) = Mapping.keys m - {k\<in>Mapping.keys m. f k (the (Mapping.lookup m k)) = None}"
  by transfer (auto simp add: bind_eq_Some_conv)

lemma map_default_eq: "Mapping.map_default k v f m = m \<longleftrightarrow> (\<exists>v. Mapping.lookup m k = Some v \<and> f v = v)"
  apply (clarsimp simp: Mapping.map_default_def Mapping.default_def)
  by transfer' (auto simp: fun_eq_iff split: if_splits)

lemma lookup_update_cases: "Mapping.lookup (Mapping.update k v m) k' = (if k=k' then Some v else Mapping.lookup m k')"
by (cases "k=k'", simp_all add: Mapping.lookup_update Mapping.lookup_update_neq)

end
