(*  Title:      RBT_Mapping_Exts.thy
    Author:     Denis Lohner, Sebastian Ullrich
*)

theory RBT_Mapping_Exts
imports
  Mapping_Exts
  "HOL-Library.RBT_Mapping"
  "HOL-Library.RBT_Set"
begin

lemma restrict_mapping_code [code]:
  "restrict_mapping f (RBT_Set.Set r) = RBT_Mapping.Mapping (RBT.map (\<lambda>a _. f a) r)"
  by transfer (auto simp: RBT_Set.Set_def restrict_map_def)

lemma map_keys_code:
  assumes "inj f"
  shows "map_keys f (RBT_Mapping.Mapping t) = RBT.fold (\<lambda>x v m. Mapping.update (f x) v m) t Mapping.empty"
proof-
  have[simp]: "\<And>x. {y. f y = f x} = {x}"
    using assms by (auto simp: inj_on_def)

  have[simp]: "distinct (map fst (rev (RBT.entries t)))"
  apply (subst rev_map[symmetric])
  apply (subst distinct_rev)
  apply (rule distinct_entries)
  done

  {
    fix k v
    fix xs :: "('a \<times> 'c) list"
    assume asm: "distinct (map fst xs)"
    hence
      "(k, v) \<in> set xs \<Longrightarrow> Some v = foldr (\<lambda>(x, v) m. m(f x \<mapsto> v)) xs Map.empty (f k)"
      "k \<notin> fst ` set xs \<Longrightarrow> None = foldr (\<lambda>(x, v) m. m(f x \<mapsto> v)) xs Map.empty (f k)"
      "\<And>x. x \<notin> f ` UNIV \<Longrightarrow> None = foldr (\<lambda>(x, v) m. m(f x \<mapsto> v)) xs Map.empty x"
      by (induction xs) (auto simp: image_def dest!: injD[OF assms])
  }
  note a = this[unfolded foldr_conv_fold, where xs3="rev _", simplified]

  show ?thesis
  unfolding RBT.fold_fold
  apply (transfer fixing: t f)
  apply (rule ext)
  apply (auto simp: vimage_def)
   apply (rename_tac x)
   apply (case_tac "RBT.lookup t x")
    apply (auto simp: lookup_in_tree[symmetric] intro!: a(2))[1]
   apply (auto dest!: lookup_in_tree[THEN iffD1] intro!: a(1))[1]
  apply (rule a(3); auto)
  done
qed

lemma map_values_code [code]:
  "map_values f (RBT_Mapping.Mapping t) = RBT.fold (\<lambda>x v m. case (f x v) of None \<Rightarrow> m | Some v' \<Rightarrow> Mapping.update x v' m) t Mapping.empty"
proof -
  {fix xs m
    assume "distinct (map fst (xs::('a \<times> 'c) list))"
    hence "fold (\<lambda>p m. case f (fst p) (snd p) of None \<Rightarrow> m | Some v' \<Rightarrow> m(fst p \<mapsto> v')) xs m
       = m ++ (\<lambda>x. Option.bind (map_of xs x) (f x))"
    by (induction xs arbitrary: m) (auto intro: rev_image_eqI split: bind_split option.splits simp: map_add_def fun_eq_iff)
  }
  note bind_map_of_fold = this
  show ?thesis
  unfolding RBT.fold_fold
  apply (transfer fixing: t f)
  apply (simp add: split_def)
  apply (rule bind_map_of_fold [of "RBT.entries t" Map.empty, simplified, symmetric])
  using RBT.distinct_entries distinct_map by auto
qed

lemma [code_unfold]: "set (RBT.keys t) = RBT_Set.Set (RBT.map (\<lambda>_ _. ()) t)"
  by (auto simp: RBT_Set.Set_def RBT.keys_def_alt RBT.lookup_in_tree elim: rev_image_eqI)

lemma mmap_rbt_code [code]: "mmap f (RBT_Mapping.Mapping t) = RBT_Mapping.Mapping (RBT.map (\<lambda>_. f) t)"
  unfolding mmap_def by transfer auto

lemma mapping_add_code [code]: "mapping_add (RBT_Mapping.Mapping t1) (RBT_Mapping.Mapping t2) = RBT_Mapping.Mapping (RBT.union t1 t2)"
  by transfer (simp add: lookup_union)

end
