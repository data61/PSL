theory Iterator
imports 
  It_to_It 
  SetIteratorOperations 
  SetIteratorGA 
  Proper_Iterator
  Gen_Iterator
  Idx_Iterator
begin

  text \<open>Folding over a list created by a proper iterator can be replaced
    by a single iteration\<close>
  lemma proper_it_to_list_opt[refine_transfer_post_subst]:
    assumes PR: "proper_it' it it'"
    shows "foldli o it_to_list it \<equiv> it'"
  proof (rule eq_reflection, intro ext)
    fix s c f \<sigma>
    
    obtain l where "it s = foldli l" and "it' s = foldli l"
      by (rule proper_itE[OF PR[THEN proper_it'D[where s=s]]])
    thus "(foldli o it_to_list it) s c f \<sigma> = it' s c f \<sigma>"
      by (simp add: comp_def it_to_list_def)
  qed

  lemma iterator_cnv_to_comp[refine_transfer_post_simp]:
    "foldli (it_to_list it x) = (foldli o it_to_list it) x"
    by auto

  declare idx_iteratei_eq_foldli[autoref_rules]

end
