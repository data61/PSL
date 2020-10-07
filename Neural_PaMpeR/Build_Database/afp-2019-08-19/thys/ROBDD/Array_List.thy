section\<open>Array List\<close>
text\<open>Most of this has been contributed by Peter Lammich.\<close>
theory Array_List
imports
  Separation_Logic_Imperative_HOL.Array_Blit
begin
  text\<open>
    This implements a datastructure that efficiently supports two operations: appending an element and looking up the nth element. 
  The implementation is straightforward.
\<close>
  text\<open>
    As underlying data structure an array is used.
  Since changing the length of an array requires copying, we double the size whenever the array needs to be expanded.
  We use a counter for the current length to track which elements are used and which are spares.
\<close>
  type_synonym 'a array_list = "'a array \<times> nat"

  definition "is_array_list l \<equiv> \<lambda>(a,n). \<exists>\<^sub>Al'. a \<mapsto>\<^sub>a l' * \<up>(n \<le> length l' \<and> l = take n l' \<and> length l'>0)"

  definition "initial_capacity \<equiv> 16::nat"

  definition "arl_empty \<equiv> do {
    a \<leftarrow> Array.new initial_capacity default;
    return (a,0)
  }"

  lemma [sep_heap_rules]: "< emp > arl_empty <is_array_list []>"
    by (sep_auto simp: arl_empty_def is_array_list_def initial_capacity_def)

  definition "arl_nth \<equiv> \<lambda>(a,n) i. do {
    Array.nth a i
  }"

  lemma [sep_heap_rules]: "i<length l \<Longrightarrow> < is_array_list l a > arl_nth a i <\<lambda>x. is_array_list l a * \<up>(x = l!i) >"  
    by (sep_auto simp: arl_nth_def is_array_list_def split: prod.splits)

  definition "arl_append \<equiv> \<lambda>(a,n) x. do {
    len \<leftarrow> Array.len a;

    if n<len then do {
      a \<leftarrow> Array.upd n x a;
      return (a,n+1)
    } else do {
      let newcap = 2 * len;
      a \<leftarrow> array_grow a newcap default;
      a \<leftarrow> Array.upd n x a;
      return (a,n+1)
    }
  }"

  lemma [sep_heap_rules]: "
    < is_array_list l a > 
      arl_append a x 
    <\<lambda>a. is_array_list (l@[x]) a >\<^sub>t"  
    by (sep_auto 
      simp: arl_append_def is_array_list_def take_update_last neq_Nil_conv
      split: prod.splits nat.split)
    
  lemma is_array_list_prec: "precise is_array_list"
    unfolding is_array_list_def[abs_def]
    apply(rule preciseI)
    apply(simp split: prod.splits)
    using preciseD snga_prec by fastforce
    
  lemma is_array_list_lengthIA: "is_array_list l li \<Longrightarrow>\<^sub>A \<up>(snd li = length l) * true"
    by(sep_auto simp: is_array_list_def split: prod.splits)
    find_consts "assn \<Rightarrow> bool"
  lemma is_array_list_lengthI: "x \<Turnstile> is_array_list l li \<Longrightarrow> snd li = length l"
  using is_array_list_lengthIA by (metis (full_types) ent_pure_post_iff star_aci(2))

end
