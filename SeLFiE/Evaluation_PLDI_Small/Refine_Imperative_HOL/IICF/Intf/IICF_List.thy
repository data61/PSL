theory IICF_List
imports 
  "../../Sepref"
  "List-Index.List_Index"
begin

lemma param_index[param]: 
  "\<lbrakk>single_valued A; single_valued (A\<inverse>)\<rbrakk> \<Longrightarrow> (index,index) \<in> \<langle>A\<rangle>list_rel \<rightarrow> A \<rightarrow> nat_rel"
  unfolding index_def[abs_def] find_index_def 
  apply (subgoal_tac "(((=), (=)) \<in> A \<rightarrow> A \<rightarrow> bool_rel)")
  apply parametricity
  by (simp add: pres_eq_iff_svb)


(* TODO: Move? *)
subsection \<open>Swap two elements of a list, by index\<close>

definition "swap l i j \<equiv> l[i := l!j, j:=l!i]"
lemma swap_nth[simp]: "\<lbrakk>i < length l; j<length l; k<length l\<rbrakk> \<Longrightarrow>
  swap l i j!k = (
    if k=i then l!j
    else if k=j then l!i
    else l!k
  )"
  unfolding swap_def
  by auto

lemma swap_set[simp]: "\<lbrakk> i < length l; j<length l \<rbrakk> \<Longrightarrow> set (swap l i j) = set l"  
  unfolding swap_def
  by auto

lemma swap_multiset[simp]: "\<lbrakk> i < length l; j<length l \<rbrakk> \<Longrightarrow> mset (swap l i j) = mset l"  
  unfolding swap_def
  by (auto simp: mset_swap)


lemma swap_length[simp]: "length (swap l i j) = length l"  
  unfolding swap_def
  by auto

lemma swap_same[simp]: "swap l i i = l"
  unfolding swap_def by auto

lemma distinct_swap[simp]: 
  "\<lbrakk>i<length l; j<length l\<rbrakk> \<Longrightarrow> distinct (swap l i j) = distinct l"
  unfolding swap_def
  by auto

lemma map_swap: "\<lbrakk>i<length l; j<length l\<rbrakk> 
  \<Longrightarrow> map f (swap l i j) = swap (map f l) i j"
  unfolding swap_def 
  by (auto simp add: map_update)

lemma swap_param[param]: "\<lbrakk> i<length l; j<length l; (l',l)\<in>\<langle>A\<rangle>list_rel; (i',i)\<in>nat_rel; (j',j)\<in>nat_rel\<rbrakk>
  \<Longrightarrow> (swap l' i' j', swap l i j)\<in>\<langle>A\<rangle>list_rel"
  unfolding swap_def
  by parametricity

lemma swap_param_fref: "(uncurry2 swap,uncurry2 swap) \<in> 
  [\<lambda>((l,i),j). i<length l \<and> j<length l]\<^sub>f (\<langle>A\<rangle>list_rel \<times>\<^sub>r nat_rel) \<times>\<^sub>r nat_rel \<rightarrow> \<langle>A\<rangle>list_rel"
  apply rule apply clarsimp
  unfolding swap_def
  apply parametricity
  by simp_all

lemma param_list_null[param]: "(List.null,List.null) \<in> \<langle>A\<rangle>list_rel \<rightarrow> bool_rel"
proof -
  have 1: "List.null = (\<lambda>[] \<Rightarrow> True | _ \<Rightarrow> False)" 
    apply (rule ext) subgoal for l by (cases l) (auto simp: List.null_def)
    done 
  show ?thesis unfolding 1 by parametricity
qed

subsection \<open>Operations\<close>

sepref_decl_op list_empty: "[]" :: "\<langle>A\<rangle>list_rel" .
context notes [simp] = eq_Nil_null begin
  sepref_decl_op list_is_empty: "\<lambda>l. l=[]" :: "\<langle>A\<rangle>list_rel \<rightarrow>\<^sub>f bool_rel" .
end
sepref_decl_op list_replicate: replicate :: "nat_rel \<rightarrow> A \<rightarrow> \<langle>A\<rangle>list_rel" .
definition op_list_copy :: "'a list \<Rightarrow> 'a list" where [simp]:  "op_list_copy l \<equiv> l"
sepref_decl_op (no_def) list_copy: "op_list_copy" :: "\<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel" .
sepref_decl_op list_prepend: "(#)" :: "A \<rightarrow> \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel" .
sepref_decl_op list_append: "\<lambda>xs x. xs@[x]" :: "\<langle>A\<rangle>list_rel \<rightarrow> A \<rightarrow> \<langle>A\<rangle>list_rel" .
sepref_decl_op list_concat: "(@)" :: "\<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel" .
sepref_decl_op list_length: length :: "\<langle>A\<rangle>list_rel \<rightarrow> nat_rel" .
sepref_decl_op list_get: nth :: "[\<lambda>(l,i). i<length l]\<^sub>f \<langle>A\<rangle>list_rel \<times>\<^sub>r nat_rel \<rightarrow> A" .
sepref_decl_op list_set: list_update :: "[\<lambda>((l,i),_). i<length l]\<^sub>f (\<langle>A\<rangle>list_rel \<times>\<^sub>r nat_rel) \<times>\<^sub>r A \<rightarrow> \<langle>A\<rangle>list_rel" .
context notes [simp] = eq_Nil_null begin
  sepref_decl_op list_hd: hd :: "[\<lambda>l. l\<noteq>[]]\<^sub>f \<langle>A\<rangle>list_rel \<rightarrow> A" .
  sepref_decl_op list_tl: tl :: "[\<lambda>l. l\<noteq>[]]\<^sub>f \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel" .
  sepref_decl_op list_last: last :: "[\<lambda>l. l\<noteq>[]]\<^sub>f \<langle>A\<rangle>list_rel \<rightarrow> A" .
  sepref_decl_op list_butlast: butlast :: "[\<lambda>l. l\<noteq>[]]\<^sub>f \<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel" .
end
sepref_decl_op list_contains: "\<lambda>x l. x\<in>set l" :: "A \<rightarrow> \<langle>A\<rangle>list_rel \<rightarrow> bool_rel" 
  where "single_valued A" "single_valued (A\<inverse>)" .
sepref_decl_op list_swap: swap :: "[\<lambda>((l,i),j). i<length l \<and> j<length l]\<^sub>f (\<langle>A\<rangle>list_rel \<times>\<^sub>r nat_rel) \<times>\<^sub>r nat_rel \<rightarrow> \<langle>A\<rangle>list_rel" .
sepref_decl_op list_rotate1: rotate1 :: "\<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel" .
sepref_decl_op list_rev: rev :: "\<langle>A\<rangle>list_rel \<rightarrow> \<langle>A\<rangle>list_rel" .
sepref_decl_op list_index: index :: "\<langle>A\<rangle>list_rel \<rightarrow> A \<rightarrow> nat_rel" 
  where "single_valued A" "single_valued (A\<inverse>)" .

subsection \<open>Patterns\<close>
lemma [def_pat_rules]:
  "[] \<equiv> op_list_empty"
  "(=) $l$[] \<equiv> op_list_is_empty$l"
  "(=) $[]$l \<equiv> op_list_is_empty$l"
  "replicate$n$v \<equiv> op_list_replicate$n$v"
  "Cons$x$xs \<equiv> op_list_prepend$x$xs"
  "(@) $xs$(Cons$x$[]) \<equiv> op_list_append$xs$x"
  "(@) $xs$ys \<equiv> op_list_concat$xs$ys"
  "op_list_concat$xs$(Cons$x$[]) \<equiv> op_list_append$xs$x"
  "length$xs \<equiv> op_list_length$xs"
  "nth$l$i \<equiv> op_list_get$l$i"
  "list_update$l$i$x \<equiv> op_list_set$l$i$x"
  "hd$l \<equiv> op_list_hd$l"
  "hd$l \<equiv> op_list_hd$l"
  "tl$l \<equiv> op_list_tl$l"
  "tl$l \<equiv> op_list_tl$l"
  "last$l \<equiv> op_list_last$l"
  "butlast$l \<equiv> op_list_butlast$l"
  "(\<in>) $x$(set$l) \<equiv> op_list_contains$x$l"
  "swap$l$i$j \<equiv> op_list_swap$l$i$j"
  "rotate1$l \<equiv> op_list_rotate1$l"
  "rev$l \<equiv> op_list_rev$l"
  "index$l$x \<equiv> op_list_index$l$x"
  by (auto intro!: eq_reflection)

text \<open>Standard preconditions are preserved by list-relation. These lemmas are used for
  simplification of preconditions after composition.\<close>
lemma list_rel_pres_neq_nil[fcomp_prenorm_simps]: "(x',x)\<in>\<langle>A\<rangle>list_rel \<Longrightarrow> x'\<noteq>[] \<longleftrightarrow> x\<noteq>[]" by auto
lemma list_rel_pres_length[fcomp_prenorm_simps]: "(x',x)\<in>\<langle>A\<rangle>list_rel \<Longrightarrow> length x' = length x" by (rule list_rel_imp_same_length)

locale list_custom_empty = 
  fixes rel empty and op_custom_empty :: "'a list"
  assumes customize_hnr_aux: "(uncurry0 empty,uncurry0 (RETURN (op_list_empty::'a list))) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a rel"
  assumes op_custom_empty_def: "op_custom_empty = op_list_empty"
begin
  sepref_register op_custom_empty :: "'c list"

  lemma fold_custom_empty:
    "[] = op_custom_empty"
    "op_list_empty = op_custom_empty"
    "mop_list_empty = RETURN op_custom_empty"
    unfolding op_custom_empty_def by simp_all

  lemmas custom_hnr[sepref_fr_rules] = customize_hnr_aux[folded op_custom_empty_def]
end


lemma gen_mop_list_swap: "mop_list_swap l i j = do {
    xi \<leftarrow> mop_list_get l i;
    xj \<leftarrow> mop_list_get l j;
    l \<leftarrow> mop_list_set l i xj;
    l \<leftarrow> mop_list_set l j xi;
    RETURN l
  }"
  unfolding mop_list_swap_def
  by (auto simp: pw_eq_iff refine_pw_simps swap_def)


end
