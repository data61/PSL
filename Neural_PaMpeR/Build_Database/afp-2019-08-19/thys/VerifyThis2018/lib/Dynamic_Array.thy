section \<open>Arrays with Dynamic Resizing\<close>
theory Dynamic_Array
imports "Refine_Imperative_HOL.IICF_List" "Separation_Logic_Imperative_HOL.Array_Blit" "Refine_Imperative_HOL.IICF_Array" "Refine_Imperative_HOL.IICF_Map"
begin

(* TODO: Move to Array_Blit *)
definition "array_grow' a n x \<equiv> do {
  l\<leftarrow>Array.len a;
  a'\<leftarrow>Array.new (l+n) x;
  blit a 0 a' 0 l;
  return a'
}"

lemma array_grow'_rule[sep_heap_rules]:
  shows "
    < a\<mapsto>\<^sub>ala > 
      array_grow' a n x 
    <\<lambda>a'. a'\<mapsto>\<^sub>a (la @ replicate n x)>\<^sub>t"
  unfolding array_grow'_def
  by sep_auto

(* TODO: Move to IICF_List *)
sepref_decl_op list_grow: 
  "\<lambda>xs n x. xs@replicate n x" :: "\<langle>A\<rangle>list_rel \<rightarrow> nat_rel \<rightarrow> A \<rightarrow> \<langle>A\<rangle>list_rel" .


definition "nff_\<alpha> dflt l i \<equiv> if i<length l then l!i else dflt"
definition "is_nff dflt f a \<equiv> \<exists>\<^sub>Al. a \<mapsto>\<^sub>a l * \<up>(f = nff_\<alpha> dflt l)"

definition [code_unfold]: "dyn_array_new_sz dflt n \<equiv> Array.new n dflt"

lemma dyn_array_new_sz_rl[sep_heap_rules]: 
  "<emp> dyn_array_new_sz dflt n <\<lambda>r. is_nff dflt (\<lambda>_. dflt) r>"
  unfolding dyn_array_new_sz_def is_nff_def nff_\<alpha>_def
  by sep_auto

definition "array_get_dyn dflt a i \<equiv> do {
  \<^cancel>\<open>\<open>nth_oo dflt a i\<close>\<close>
  l \<leftarrow> Array.len a;
  if i<l then Array.nth a i else return dflt
  }"

lemma array_get_dyn_rule[sep_heap_rules]: "
  < is_nff dflt f a > 
    array_get_dyn dflt a i 
  < \<lambda>r. is_nff dflt f a * \<up>(r = f i) >"
  unfolding array_get_dyn_def nth_oo_def
  by (sep_auto simp: nff_\<alpha>_def is_nff_def)

definition "array_set_dyn dflt a i v \<equiv> do {
  l \<leftarrow> Array.len a;
  if i<l then 
    Array.upd i v a 
  else do {
    let ns = max (2*l) (i+1);
    a \<leftarrow> array_grow a ns dflt;
    Array.upd i v a
  }
}"

lemma nff_\<alpha>_upd: "\<lbrakk>i < length l\<rbrakk> \<Longrightarrow> nff_\<alpha> dflt (l[i := v]) = (nff_\<alpha> dflt l)(i := v)"
  by (auto simp: nff_\<alpha>_def)

lemma nff_\<alpha>_append_default: "nff_\<alpha> dflt (l@replicate n dflt) = nff_\<alpha> dflt l"
  by (auto simp: nff_\<alpha>_def nth_append intro!: ext)

lemma array_set_dyn_rule[sep_heap_rules]: "
  < is_nff dflt f a >
    array_set_dyn dflt a i v
  <\<lambda>r. is_nff dflt (f(i:=v)) r >\<^sub>t  
  "
  unfolding array_set_dyn_def is_nff_def upd_oo_def
  by (sep_auto simp: nff_\<alpha>_upd nff_\<alpha>_append_default)

end


