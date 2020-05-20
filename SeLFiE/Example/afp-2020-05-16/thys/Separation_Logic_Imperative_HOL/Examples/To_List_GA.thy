section \<open>Generic Algorithm to Convert Sets to Lists\<close>
theory To_List_GA
imports Imp_Set_Spec Imp_List_Spec Hash_Set_Impl Open_List
begin
  text \<open>This theory demonstrates how to develop a generic to-list 
    algorithm, and gives a sample instantiation for hash sets and open lists.
\<close>

  subsection \<open>Algorithm\<close>
  partial_function (heap) to_list_ga_rec where [code]: 
    "to_list_ga_rec 
      it_has_next it_next 
      l_prepend
      it l 
    =
    do {
      b \<leftarrow> it_has_next it;
      if b then do {
        (x,it) \<leftarrow> it_next it;
        l \<leftarrow> l_prepend x l;
        to_list_ga_rec it_has_next it_next 
          l_prepend it l
      } else
        return l
    }
    "

  lemma to_list_ga_rec_rule:
    assumes "imp_set_iterate is_set is_it it_init it_has_next it_next"
    assumes "imp_list_prepend is_list l_prepend"
    assumes FIN: "finite it"
    shows "
    < is_it s si it iti * is_list l li > 
      to_list_ga_rec it_has_next it_next l_prepend iti li
    < \<lambda>r. \<exists>\<^sub>Al'. is_set s si 
      * is_list l' r
      * \<up>(set l' = set l \<union> it) >\<^sub>t"
  proof -
    interpret imp_set_iterate is_set is_it it_init it_has_next it_next
      + imp_list_prepend is_list l_prepend
      by fact+

    from FIN show ?thesis
    proof (induction arbitrary: l li iti rule: finite_psubset_induct)
      case (psubset it)
      show ?case
        apply (subst to_list_ga_rec.simps)
        apply (sep_auto heap: psubset.IH)
        apply (rule ent_frame_fwd[OF quit_iteration])
        apply frame_inference
        apply solve_entails
        done
    qed
  qed

  definition "to_list_ga 
    it_init it_has_next it_next
    l_empty l_prepend s 
    \<equiv> do {
      it \<leftarrow> it_init s;
      l \<leftarrow> l_empty;
      l \<leftarrow> to_list_ga_rec it_has_next it_next l_prepend it l;
      return l
    }"

  lemma to_list_ga_rule:
    assumes IT: "imp_set_iterate is_set is_it it_init it_has_next it_next"
    assumes EM: "imp_list_empty is_list l_empty"
    assumes PREP: "imp_list_prepend is_list l_prepend"
    assumes FIN: "finite s"
    shows "
    <is_set s si>
    to_list_ga it_init it_has_next it_next
      l_empty l_prepend si
    <\<lambda>r. \<exists>\<^sub>Al. is_set s si * is_list l r * true * \<up>(set l = s)>"
  proof -
    interpret imp_list_empty is_list l_empty +
      imp_set_iterate is_set is_it it_init it_has_next it_next
      by fact+

    note [sep_heap_rules] = to_list_ga_rec_rule[OF IT PREP]
    show ?thesis
      unfolding to_list_ga_def
      by (sep_auto simp: FIN)
  qed

  subsection \<open>Sample Instantiation for hash set and open list\<close>
  definition "hs_to_ol 
    \<equiv> to_list_ga hs_it_init hs_it_has_next hs_it_next
        os_empty os_prepend"
  
  lemmas hs_to_ol_rule[sep_heap_rules] =
    to_list_ga_rule[OF hs_iterate_impl os_empty_impl os_prepend_impl,
    folded hs_to_ol_def] 


  export_code hs_to_ol checking SML_imp

end
