theory Array_Set_Impl
imports 
  "../Sep_Main" Imp_Set_Spec Array_Blit
  "HOL-Library.Code_Target_Numeral"
begin
  subsection "Array Set"

  type_synonym array_set = "bool array"
  definition "ias_initial_size \<equiv> 8::nat"

  definition "ias_of_list l \<equiv> {i. i<length l \<and> l!i}"

  definition is_ias :: "(nat set) \<Rightarrow> array_set \<Rightarrow> assn" where
    "is_ias m a \<equiv> \<exists>\<^sub>Al. a\<mapsto>\<^sub>al * \<up>(m=ias_of_list l)"

  definition ias_new_sz :: "nat \<Rightarrow> array_set Heap"
    where "ias_new_sz sz \<equiv> Array.new sz False"

  definition ias_new :: "array_set Heap"
    where "ias_new \<equiv> ias_new_sz ias_initial_size"

  definition ias_memb
    :: "nat \<Rightarrow> array_set \<Rightarrow> bool Heap"
    where "ias_memb k a = do {
      l\<leftarrow>Array.len a;
      if k < l then Array.nth a k else return False
    }"

  lemma [code]: "ias_memb k a \<equiv> nth_oo False a k"
    unfolding ias_memb_def nth_oo_def .

  definition ias_delete
    :: "nat \<Rightarrow> array_set \<Rightarrow> array_set Heap"
  where "ias_delete k a = do {
      l\<leftarrow>Array.len a;
      if k < l then Array.upd k False a else return a
    }"

  lemma [code]: "ias_delete k a \<equiv> upd_oo (return a) k False a"
    unfolding ias_delete_def upd_oo_def .

  definition ias_ins
    :: "nat \<Rightarrow> array_set \<Rightarrow> array_set Heap"
    where "ias_ins k a = do {
      l\<leftarrow>Array.len a;
      a\<leftarrow>if k>=l then do {
          let newsz = max (k+1) (2 * l + 3);
          array_grow a newsz False
        } else return a;

      Array.upd k True a
    }"

  lemma [code]: "ias_ins k a \<equiv> upd_oo (do {
      l\<leftarrow>Array.len a;
      let newsz = max (k+1) (2 * l + 3);
      a\<leftarrow>array_grow a newsz False;
      Array.upd k True a
    })
    k True a"
    unfolding ias_ins_def upd_oo_def
    apply (rule eq_reflection)
    apply (auto simp add: bind_def execute_len execute_return)
    done


  lemma precise_ias: "precise is_ias"
    apply rule
    by (auto simp add: is_ias_def dest: preciseD[OF snga_prec])

  lemma ias_new_abs: "ias_of_list (replicate n False) = {}"
    unfolding ias_of_list_def[abs_def]
    by auto

  lemma ias_new_sz_rule: "<emp> ias_new_sz n < is_ias {} >"
    unfolding ias_new_sz_def is_ias_def[abs_def]
    by (sep_auto simp: ias_new_abs)

  lemma ias_new_rule: "<emp> ias_new < is_ias {} >"
    unfolding ias_new_def by (sep_auto heap: ias_new_sz_rule)

  lemma ias_memb_abs1: "k<length l \<Longrightarrow> k\<in>ias_of_list l \<longleftrightarrow> l!k"
    by (simp add: ias_of_list_def)
  lemma ias_memb_abs2: "\<not>k<length l \<Longrightarrow> k\<notin>ias_of_list l"
    by (simp add: ias_of_list_def)

  lemma ias_memb_rule: "< is_ias m p > 
    ias_memb k p 
    <\<lambda>r. is_ias m p * \<up>(r\<longleftrightarrow>k\<in>m) >"
    unfolding ias_memb_def is_ias_def
    by (sep_auto simp: ias_memb_abs1 ias_memb_abs2)

  lemma ias_delete_abs1: "k<length l 
    \<Longrightarrow> ias_of_list (l[k := False]) = ias_of_list l - {k}"
    unfolding ias_of_list_def[abs_def]
    by (auto simp: nth_list_update)

  lemma ias_delete_abs2: "\<not>k<length l 
    \<Longrightarrow> ias_of_list l - {k} = ias_of_list l"
    unfolding ias_of_list_def[abs_def]
    by (auto)

  lemma ias_delete_rule: "< is_ias m p >
    ias_delete k p
    <\<lambda>r. is_ias (m-{k}) r>"
    unfolding is_ias_def ias_delete_def
    by (sep_auto simp: ias_delete_abs1 ias_delete_abs2)
    
  lemma ias_ins_abs1: "ias_of_list (l@replicate n False) = ias_of_list l"
    unfolding ias_of_list_def[abs_def]
    apply rule
    apply rule
    apply simp
    apply (elim conjE)
    apply (case_tac "x<length l")
    apply (simp_all add: nth_append) [2]
    apply rule
    apply (simp add: nth_append)
    done

  lemma ias_ins_abs2: "\<not> length l \<le> k 
    \<Longrightarrow> ias_of_list (l[k := True]) = insert k (ias_of_list l)"
    unfolding ias_of_list_def[abs_def]
    by (auto simp: nth_list_update)
  
  lemma ias_ins_rule:
    "< is_ias m p > ias_ins k p <\<lambda>r. is_ias (insert k m) r>\<^sub>t"
    unfolding is_ias_def ias_ins_def
    by (sep_auto 
      decon: decon_if_split 
      simp: ias_ins_abs1 ias_ins_abs2)
  
  lemma ias_set_impl: "imp_set is_ias"
    apply unfold_locales
    by (rule precise_ias)
  interpretation ias: imp_set is_ias using ias_set_impl .
  
  lemma ias_empty_impl: "imp_set_empty is_ias ias_new"
    apply unfold_locales
    by (sep_auto heap: ias_new_rule)
  interpretation ias: imp_set_empty is_ias ias_new using ias_empty_impl .

  lemma ias_empty_sz_impl: "imp_set_empty is_ias (ias_new_sz sz)"
    apply unfold_locales
    by (sep_auto heap: ias_new_sz_rule)
  interpretation ias_sz: imp_set_empty is_ias "ias_new_sz sz"
    using ias_empty_sz_impl .

  lemma ias_memb_impl: "imp_set_memb is_ias ias_memb"
    apply unfold_locales
    by (sep_auto heap: ias_memb_rule)
  interpretation ias: imp_set_memb is_ias ias_memb
    using ias_memb_impl .
  
  lemma ias_delete_impl: "imp_set_delete is_ias ias_delete"
    apply unfold_locales
    by (sep_auto heap: ias_delete_rule)
  interpretation ias: imp_set_delete is_ias ias_delete
    using ias_delete_impl .

  (* Self - contained proof, for paper *)  
  context begin
    interpretation ias: imp_set_ins is_ias ias_ins proof
      fix s p a
      show "<is_ias s p> ias_ins a p <is_ias (insert a s)>\<^sub>t"
        unfolding is_ias_def ias_ins_def
        by (sep_auto decon: decon_if_split simp: ias_ins_abs1 ias_ins_abs2)
    qed    

  end

  lemma "imp_set_ins is_ias ias_ins"
    apply unfold_locales
    by (sep_auto heap: ias_ins_rule)
  
  lemma ias_ins_impl: "imp_set_ins is_ias ias_ins"
    apply unfold_locales
    by (sep_auto heap: ias_ins_rule)
  interpretation ias: imp_set_ins is_ias ias_ins
    using ias_ins_impl .

end
