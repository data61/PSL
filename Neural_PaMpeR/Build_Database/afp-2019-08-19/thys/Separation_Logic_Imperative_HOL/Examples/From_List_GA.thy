section \<open>Generic Algorithm to Generate Sets from Lists\<close>
theory From_List_GA
imports Imp_Set_Spec Imp_List_Spec Hash_Set_Impl Array_Set_Impl
begin

term fold

  primrec from_list_ga_aux where
    "from_list_ga_aux ins [] s = return s"
  | "from_list_ga_aux ins (x#l) s 
     = do { s \<leftarrow> ins x s; from_list_ga_aux ins l s }"
 
  lemma from_list_ga_aux_rule:
    assumes "imp_set_ins is_set ins"
    shows 
    "< is_set s p > from_list_ga_aux ins l p <\<lambda>r. is_set (set l \<union> s) r >\<^sub>t"
  proof -
    interpret imp_set_ins is_set ins by fact
    show ?thesis 
    proof (induction l arbitrary: s p)
      case Nil thus ?case by sep_auto
    next
      case (Cons x l)
      show ?case by (sep_auto heap: Cons.IH)
    qed
  qed

  definition "from_list_ga e i l = do { s\<leftarrow>e; from_list_ga_aux i l s}"

  lemma from_list_ga_rule:
    fixes empty
    assumes "imp_set_empty is_set empty"
    assumes I: "imp_set_ins is_set ins"
    shows "<emp> from_list_ga empty ins l <\<lambda>r. is_set (set l) r>\<^sub>t"
  proof -
    interpret imp_set_empty is_set empty by fact
    note [sep_heap_rules] = from_list_ga_aux_rule[OF I]
    show ?thesis unfolding from_list_ga_def by sep_auto
  qed

  definition "hs_from_list \<equiv> from_list_ga hs_new hs_ins"
  lemmas hs_from_list_rule[sep_heap_rules] 
    = from_list_ga_rule[OF hs_new_impl hs_ins_impl, folded hs_from_list_def]

  definition "ias_from_list \<equiv> from_list_ga ias_new ias_ins"
  lemmas ias_from_list_rule[sep_heap_rules] 
    = from_list_ga_rule[OF ias_empty_impl ias_ins_impl, 
        folded ias_from_list_def]

end
