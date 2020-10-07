theory Array_Map_Impl
imports 
  "../Sep_Main" Imp_Map_Spec Array_Blit
  "HOL-Library.Code_Target_Numeral"
begin
  subsection "Array Map"

  type_synonym 'v array_map = "'v option array"
  definition "iam_initial_size \<equiv> 8::nat"

  definition "iam_of_list l i \<equiv> if i<length l then l!i else None"

  definition is_iam :: "(nat\<rightharpoonup>'a) \<Rightarrow> ('a::heap) array_map \<Rightarrow> assn" where
    "is_iam m a \<equiv> \<exists>\<^sub>Al. a\<mapsto>\<^sub>al * \<up>(m=iam_of_list l)"

  definition iam_new_sz :: "nat \<Rightarrow> ('v::heap) array_map Heap"
    where "iam_new_sz sz \<equiv> Array.new sz None"

  definition iam_new :: "('v::heap) array_map Heap"
    where "iam_new \<equiv> iam_new_sz iam_initial_size"

  definition iam_lookup 
    :: "nat \<Rightarrow> ('v::heap) array_map \<Rightarrow> 'v option Heap"
    where "iam_lookup k a = do {
      l\<leftarrow>Array.len a;
      if k < l then Array.nth a k else return None
    }"

  lemma [code]: "iam_lookup k a \<equiv> nth_oo None a k"
    unfolding nth_oo_def iam_lookup_def .

  definition iam_delete
    :: "nat \<Rightarrow> ('v::heap) array_map \<Rightarrow> ('v::heap) array_map Heap"
  where "iam_delete k a = do {
      l\<leftarrow>Array.len a;
      if k < l then Array.upd k None a else return a
    }"

  lemma [code]: "iam_delete k a \<equiv> upd_oo (return a) k None a"
    unfolding upd_oo_def iam_delete_def .

  definition iam_update
    :: "nat \<Rightarrow> 'v::heap \<Rightarrow> 'v array_map \<Rightarrow> 'v array_map Heap"
    where "iam_update k v a = do {
      l\<leftarrow>Array.len a;
      a\<leftarrow>if k>=l then do {
          let newsz = max (k+1) (2 * l + 3);
          array_grow a newsz None
        } else return a;

      Array.upd k (Some v) a
    }"

  lemma [code]: "iam_update k v a = upd_oo 
    (do {
      l\<leftarrow>Array.len a;
      let newsz = max (k+1) (2 * l + 3);
      a\<leftarrow>array_grow a newsz None;
      Array.upd k (Some v) a
    })
    k (Some v) a"
  proof -
    have [simp]: 
      "\<And>x t e. do {
        l\<leftarrow>Array.len a;
        if x l then 
          t l 
        else do {
          l'\<leftarrow>Array.len a;
          e l l'
        } 
      }
      =
      do {
        l\<leftarrow>Array.len a;
        if x l then t l else e l l
      }"
      apply (auto 
        simp: bind_def execute_len 
        split: option.split
        intro!: ext
      )
      done
  
    show ?thesis
      unfolding upd_oo_def iam_update_def
      apply simp
      apply (rule cong[OF arg_cong, where f1=bind])
      apply simp
      apply (rule ext)
      apply auto
      done
  qed

  lemma precise_iam: "precise is_iam"
    apply rule
    by (auto simp add: is_iam_def dest: preciseD[OF snga_prec])

  lemma iam_new_abs: "iam_of_list (replicate n None) = Map.empty"
    unfolding iam_of_list_def[abs_def]
    by auto

  lemma iam_new_sz_rule: "<emp> iam_new_sz n < is_iam Map.empty >"
    unfolding iam_new_sz_def is_iam_def[abs_def]
    by (sep_auto simp: iam_new_abs)

  lemma iam_new_rule: "<emp> iam_new < is_iam Map.empty >"
    unfolding iam_new_def by (sep_auto heap: iam_new_sz_rule)

  lemma iam_lookup_abs1: "k<length l \<Longrightarrow> iam_of_list l k = l!k"
    by (simp add: iam_of_list_def)
  lemma iam_lookup_abs2: "\<not>k<length l \<Longrightarrow> iam_of_list l k = None"
    by (simp add: iam_of_list_def)

  lemma iam_lookup_rule: "< is_iam m p > 
    iam_lookup k p 
    <\<lambda>r. is_iam m p * \<up>(r=m k) >"
    unfolding iam_lookup_def is_iam_def
    by (sep_auto simp: iam_lookup_abs1 iam_lookup_abs2)

  lemma iam_delete_abs1: "k<length l 
    \<Longrightarrow> iam_of_list (l[k := None]) = iam_of_list l |` (- {k})"
    unfolding iam_of_list_def[abs_def]
    by (auto intro!: ext simp: restrict_map_def)

  lemma iam_delete_abs2: "\<not>k<length l 
    \<Longrightarrow> iam_of_list l |` (- {k}) = iam_of_list l"
    unfolding iam_of_list_def[abs_def]
    by (auto intro!: ext simp: restrict_map_def)

  lemma iam_delete_rule: "< is_iam m p >
    iam_delete k p
    <\<lambda>r. is_iam (m|`(-{k})) r>"
    unfolding is_iam_def iam_delete_def
    by (sep_auto simp: iam_delete_abs1 iam_delete_abs2)
    

  lemma iam_update_abs1: "iam_of_list (l@replicate n None) = iam_of_list l"
    unfolding iam_of_list_def[abs_def]
    by (auto intro!: ext simp: nth_append)

  lemma iam_update_abs2: "\<not> length l \<le> k 
    \<Longrightarrow> iam_of_list (l[k := Some v]) = iam_of_list l(k \<mapsto> v)"
    unfolding iam_of_list_def[abs_def]
    by auto

  lemma iam_update_rule:
    "< is_iam m p > iam_update k v p <\<lambda>r. is_iam (m(k\<mapsto>v)) r>\<^sub>t"
    unfolding is_iam_def iam_update_def
    by (sep_auto 
      decon: decon_if_split 
      simp: iam_update_abs1 iam_update_abs2)
  
  interpretation iam: imp_map is_iam
    apply unfold_locales
    by (rule precise_iam)
  interpretation iam: imp_map_empty is_iam iam_new
    apply unfold_locales
    by (sep_auto heap: iam_new_rule)
  interpretation iam_sz: imp_map_empty is_iam "iam_new_sz sz"
    apply unfold_locales
    by (sep_auto heap: iam_new_sz_rule)
 
  interpretation iam: imp_map_lookup is_iam iam_lookup
    apply unfold_locales
    by (sep_auto heap: iam_lookup_rule)
  interpretation iam: imp_map_delete is_iam iam_delete
    apply unfold_locales
    by (sep_auto heap: iam_delete_rule)
  interpretation iam: imp_map_update is_iam iam_update
    apply unfold_locales
    by (sep_auto heap: iam_update_rule)

end
