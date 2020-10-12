(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
section \<open>\isaheader{Additions to RB-Trees}\<close>
theory RBT_add
imports 
  "HOL-Library.RBT_Impl" 
  "../Iterator/Iterator"
begin
text_raw \<open>\label{thy:RBT_add}\<close>

lemma tlt_trans: "\<lbrakk>l |\<guillemotleft> u; u\<le>v\<rbrakk> \<Longrightarrow> l |\<guillemotleft> v"
  by (induct l) auto

lemma trt_trans: "\<lbrakk> u\<le>v; v\<guillemotleft>|r \<rbrakk> \<Longrightarrow> u\<guillemotleft>|r"
  by (induct r) auto

lemmas tlt_trans' = tlt_trans[OF _ less_imp_le]
lemmas trt_trans' = trt_trans[OF less_imp_le]

primrec rm_iterateoi 
  :: "('k,'v) RBT_Impl.rbt \<Rightarrow> ('k \<times> 'v, '\<sigma>) set_iterator"
  where
  "rm_iterateoi RBT_Impl.Empty c f \<sigma> = \<sigma>" |
  "rm_iterateoi (RBT_Impl.Branch col l k v r) c f \<sigma> = (
    if (c \<sigma>) then
      let \<sigma>' = rm_iterateoi l c f \<sigma> in
        if (c \<sigma>') then
          rm_iterateoi r c f (f (k, v) \<sigma>')
        else \<sigma>'
    else 
      \<sigma>
  )"

lemma rm_iterateoi_abort :
  "\<not>(c \<sigma>) \<Longrightarrow> rm_iterateoi t c f \<sigma> = \<sigma>"
by (cases t) auto

lemma rm_iterateoi_alt_def :
  "rm_iterateoi RBT_Impl.Empty = set_iterator_emp"
  "rm_iterateoi (RBT_Impl.Branch col l k v r) = 
   set_iterator_union (rm_iterateoi l)
     (set_iterator_union (set_iterator_sng (k, v)) (rm_iterateoi r))"
by (simp_all add: fun_eq_iff set_iterator_emp_def rm_iterateoi_abort
                  set_iterator_union_def set_iterator_sng_def Let_def)
declare rm_iterateoi.simps[simp del]


primrec rm_reverse_iterateoi 
  :: "('k,'v) RBT_Impl.rbt \<Rightarrow> ('k \<times> 'v, '\<sigma>) set_iterator"
  where
  "rm_reverse_iterateoi RBT_Impl.Empty c f \<sigma> = \<sigma>" |
  "rm_reverse_iterateoi (Branch col l k v r) c f \<sigma> = (
    if (c \<sigma>) then
      let \<sigma>' = rm_reverse_iterateoi r c f \<sigma> in
        if (c \<sigma>') then
          rm_reverse_iterateoi l c f (f (k, v) \<sigma>')
        else \<sigma>'
    else 
      \<sigma>
  )"

lemma rm_reverse_iterateoi_abort :
  "\<not>(c \<sigma>) \<Longrightarrow> rm_reverse_iterateoi t c f \<sigma> = \<sigma>"
by (cases t) auto

lemma rm_reverse_iterateoi_alt_def :
  "rm_reverse_iterateoi RBT_Impl.Empty = set_iterator_emp"
  "rm_reverse_iterateoi (RBT_Impl.Branch col l k v r) = 
   set_iterator_union (rm_reverse_iterateoi r)
     (set_iterator_union (set_iterator_sng (k, v)) (rm_reverse_iterateoi l))"
by (simp_all add: fun_eq_iff set_iterator_emp_def rm_reverse_iterateoi_abort
                  set_iterator_union_def set_iterator_sng_def Let_def)
declare rm_reverse_iterateoi.simps[simp del]

(*
lemma finite_dom_lookup [simp, intro!]: "finite (dom (RBT.lookup t))"
by(simp add: RBT.lookup_def)


instantiation rbt :: ("{equal, linorder}", equal) equal begin

definition "equal_class.equal (r :: ('a, 'b) rbt) r' == RBT.impl_of r = RBT.impl_of r'"

instance
proof
qed (simp add: equal_rbt_def RBT.impl_of_inject)

end
*)

lemma (in linorder) map_to_set_lookup_entries: 
   "rbt_sorted t \<Longrightarrow> map_to_set (rbt_lookup t) = set (RBT_Impl.entries t)"
  using map_of_entries[symmetric,of t]
  by (simp add: distinct_entries map_to_set_map_of)

lemma (in linorder) rm_iterateoi_correct:
  fixes t::"('a, 'v) RBT_Impl.rbt"
  assumes is_sort: "rbt_sorted t"
  defines "it \<equiv> 
  RBT_add.rm_iterateoi::(('a, 'v) RBT_Impl.rbt \<Rightarrow> ('a \<times> 'v, '\<sigma>) set_iterator)"
  shows "map_iterator_linord (it t) (rbt_lookup t)"
  using is_sort
proof (induct t)
  case Empty
  show ?case unfolding it_def 
    by (simp add: rm_iterateoi_alt_def 
      map_iterator_linord_emp_correct rbt_lookup_Empty)
next
  case (Branch c l k v r)
  note is_sort_t = Branch(3)

  from Branch(1) is_sort_t have 
    l_it: "map_iterator_linord (it l) (rbt_lookup l)" by simp
  from Branch(2) is_sort_t have 
    r_it: "map_iterator_linord (it r) (rbt_lookup r)" by simp
  note kv_it = map_iterator_linord_sng_correct[of k v]

  have kv_r_it : "set_iterator_map_linord
     (set_iterator_union (set_iterator_sng (k, v)) (it r))
     (map_to_set [k \<mapsto> v] \<union> map_to_set (rbt_lookup r))"
  proof (rule map_iterator_linord_union_correct [OF kv_it r_it])
    fix kv kv'
    assume pre: "kv \<in> map_to_set [k \<mapsto> v]" "kv' \<in> map_to_set (rbt_lookup r)"
    obtain k' v' where kv'_eq[simp]: "kv' = (k', v')" by (rule prod.exhaust)
 
    from pre is_sort_t show "fst kv < fst kv'" 
      apply (simp add: map_to_set_lookup_entries split: prod.splits)
      apply (metis entry_in_tree_keys rbt_greater_prop)
      done
  qed

  have l_kv_r_it : "set_iterator_map_linord (it (Branch c l k v r))
     (map_to_set (rbt_lookup l) 
      \<union> (map_to_set [k \<mapsto> v] \<union> map_to_set (rbt_lookup r)))"
    unfolding it_def rm_iterateoi_alt_def
    unfolding it_def[symmetric]
  proof (rule map_iterator_linord_union_correct [OF l_it kv_r_it])
    fix kv1 kv2
    assume pre: "kv1 \<in> map_to_set (rbt_lookup l)" 
                "kv2 \<in> map_to_set [k \<mapsto> v] \<union> map_to_set (rbt_lookup r)" 

    obtain k1 v1 where kv1_eq[simp]: "kv1 = (k1, v1)" by (rule prod.exhaust)
    obtain k2 v2 where kv2_eq[simp]: "kv2 = (k2, v2)" by (rule prod.exhaust)

    from pre is_sort_t show "fst kv1 < fst kv2" 
      apply (simp add: map_to_set_lookup_entries split: prod.splits)
      by (metis (lifting) map_of_entries neqE option.simps(3) 
        ord.rbt_lookup_rbt_greater ord.rbt_lookup_rbt_less rbt_greater_trans 
        rbt_less_trans weak_map_of_SomeI)
  qed
  
  from is_sort_t
  have map_eq: "map_to_set (rbt_lookup l) 
    \<union> (map_to_set [k \<mapsto> v] \<union> map_to_set (rbt_lookup r)) =
        map_to_set (rbt_lookup (Branch c l k v r))" 
    by (simp add: set_eq_iff map_to_set_lookup_entries)
  
  from l_kv_r_it[unfolded map_eq]
  show ?case .
qed

lemma (in linorder) rm_reverse_iterateoi_correct:
  fixes t::"('a, 'v) RBT_Impl.rbt"
  assumes is_sort: "rbt_sorted t"
  defines "it \<equiv> RBT_add.rm_reverse_iterateoi
    ::(('a, 'v) RBT_Impl.rbt \<Rightarrow> ('a \<times> 'v, '\<sigma>) set_iterator)"
  shows "map_iterator_rev_linord (it t) (rbt_lookup t)"
  using is_sort
proof (induct t)
  case Empty
  show ?case unfolding it_def 
    by (simp add: rm_reverse_iterateoi_alt_def 
      map_iterator_rev_linord_emp_correct rbt_lookup_Empty)
next
  case (Branch c l k v r)
  note is_sort_t = Branch(3)

  from Branch(1) is_sort_t have 
    l_it: "map_iterator_rev_linord (it l) (rbt_lookup l)" by simp
  from Branch(2) is_sort_t have 
    r_it: "map_iterator_rev_linord (it r) (rbt_lookup r)" by simp
  note kv_it = map_iterator_rev_linord_sng_correct[of k v]

  have kv_l_it : "set_iterator_map_rev_linord
     (set_iterator_union (set_iterator_sng (k, v)) (it l))
     (map_to_set [k \<mapsto> v] \<union> map_to_set (rbt_lookup l))"
  proof (rule map_iterator_rev_linord_union_correct [OF kv_it l_it])
    fix kv kv'
    assume pre: "kv \<in> map_to_set [k \<mapsto> v]" "kv' \<in> map_to_set (rbt_lookup l)"
    obtain k' v' where kv'_eq[simp]: "kv' = (k', v')" by (rule prod.exhaust)
 
    from pre is_sort_t show "fst kv > fst kv'" 
      apply (simp add: map_to_set_lookup_entries split: prod.splits)
      apply (metis entry_in_tree_keys rbt_less_prop)
   done
  qed

  have r_kv_l_it : "set_iterator_map_rev_linord (it (Branch c l k v r))
     (map_to_set (rbt_lookup r) 
      \<union> (map_to_set [k \<mapsto> v] \<union> map_to_set (rbt_lookup l)))"
    unfolding it_def rm_reverse_iterateoi_alt_def
    unfolding it_def[symmetric]
  proof (rule map_iterator_rev_linord_union_correct [OF r_it kv_l_it])
    fix kv1 kv2
    assume pre: "kv1 \<in> map_to_set (rbt_lookup r)" 
                "kv2 \<in> map_to_set [k \<mapsto> v] \<union> map_to_set (rbt_lookup l)" 

    obtain k1 v1 where kv1_eq[simp]: "kv1 = (k1, v1)" by (rule prod.exhaust)
    obtain k2 v2 where kv2_eq[simp]: "kv2 = (k2, v2)" by (rule prod.exhaust)

    from pre is_sort_t show "fst kv1 > fst kv2" 
      apply (simp add: map_to_set_lookup_entries split: prod.splits)
      by (metis (mono_tags) entry_in_tree_keys neq_iff option.simps(3) 
        ord.rbt_greater_prop ord.rbt_lookup_rbt_less rbt_less_trans 
        rbt_lookup_in_tree)
  qed
  
  from is_sort_t
  have map_eq: "map_to_set (rbt_lookup r) 
    \<union> (map_to_set [k \<mapsto> v] \<union> map_to_set (rbt_lookup l)) =
        map_to_set (rbt_lookup (Branch c l k v r))" 
    by (auto simp add: set_eq_iff map_to_set_lookup_entries)

  from r_kv_l_it[unfolded map_eq]
  show ?case .
qed

lemma pi_rm[icf_proper_iteratorI]: 
  "proper_it (RBT_add.rm_iterateoi t) (RBT_add.rm_iterateoi t)"
  by (induct t) (simp_all add: rm_iterateoi_alt_def icf_proper_iteratorI)

lemma pi_rm_rev[icf_proper_iteratorI]: 
  "proper_it (RBT_add.rm_reverse_iterateoi t) (RBT_add.rm_reverse_iterateoi t)"
  by (induct t) (simp_all add: rm_reverse_iterateoi_alt_def 
    icf_proper_iteratorI)

primrec bheight_aux :: "('a,'b) RBT_Impl.rbt \<Rightarrow> nat \<Rightarrow> nat"
where
  "\<And>acc. bheight_aux RBT_Impl.Empty acc = acc"
| "\<And>acc. bheight_aux (RBT_Impl.Branch c lt k v rt) acc = 
     bheight_aux lt (case c of RBT_Impl.B \<Rightarrow> Suc acc | RBT_Impl.R \<Rightarrow> acc)"

lemma bheight_aux_eq: "bheight_aux t a = bheight t + a"
  by (induct t arbitrary: a) (auto split: RBT_Impl.color.split)

definition [code_unfold]: "rbt_bheight t \<equiv> bheight_aux t 0"
lemma "rbt_bheight t = bheight t"
  unfolding rbt_bheight_def by (simp add: bheight_aux_eq)

(*definition "black_height t \<equiv> rbt_bheight (RBT.impl_of t)"*)

end
