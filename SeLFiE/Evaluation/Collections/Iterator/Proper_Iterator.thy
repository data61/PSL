section \<open>Proper Iterators\<close>
theory Proper_Iterator
imports 
  SetIteratorOperations 
  Automatic_Refinement.Refine_Lib
begin
  text \<open>
    Proper iterators provide a way to obtain polymorphic iterators even
    inside locale contexts.

    For this purpose, an iterator that converts the set to a list is fixed
    inside the locale, and polymorphic iterators are described by folding
    over the generated list.

    In order to ensure efficiency, it is shown that folding over the generated
    list is equivalent to directly iterating over the set, and this equivalence
    is set up as a code preprocessing rule.
\<close>

  subsection \<open>Proper Iterators\<close>

  text \<open>A proper iterator can be expressed as a fold over a list, where
    the list does only depend on the set. In particular, it does not depend
    on the type of the state. We express this by the following definition, 
    using two iterators with different types:\<close>

  definition proper_it 
    :: "('x,'\<sigma>1) set_iterator \<Rightarrow> ('x,'\<sigma>2) set_iterator \<Rightarrow> bool"
    where "proper_it it it' \<equiv> (\<exists>l. it=foldli l \<and> it'=foldli l)"

  lemma proper_itI[intro?]:
    fixes it :: "('x,'\<sigma>1) set_iterator" 
    and it' :: "('x,'\<sigma>2) set_iterator"
    assumes "it=foldli l \<and> it'=foldli l"
    shows "proper_it it it'"
    using assms unfolding proper_it_def by auto

  lemma proper_itE:
    fixes it :: "('x,'\<sigma>1) set_iterator" 
    and it' :: "('x,'\<sigma>2) set_iterator"
    assumes "proper_it it it'"
    obtains l where "it=foldli l" and "it'=foldli l"
    using assms unfolding proper_it_def by auto

  lemma proper_it_parE:
    fixes it :: "'a \<Rightarrow> ('x,'\<sigma>1) set_iterator" 
    and it' :: "'a \<Rightarrow> ('x,'\<sigma>2) set_iterator"
    assumes "\<forall>x. proper_it (it x) (it' x)"
    obtains f where "it = (\<lambda>x. foldli (f x))" and "it' = (\<lambda>x. foldli (f x))"
    using assms unfolding proper_it_def
    by metis

  definition 
    proper_it'
    where "proper_it' it it' \<equiv> \<forall>s. proper_it (it s) (it' s)"

  lemma proper_it'I:
    "\<lbrakk>\<And>s. proper_it (it s) (it' s)\<rbrakk> \<Longrightarrow> proper_it' it it'"
    unfolding proper_it'_def by blast

  lemma proper_it'D:
    "proper_it' it it' \<Longrightarrow> proper_it (it s) (it' s)"
    unfolding proper_it'_def by blast





  subsubsection \<open>Properness Preservation\<close>
  ML \<open>
    structure Icf_Proper_Iterator = struct

      structure icf_proper_iteratorI = Named_Thms
        ( val name = @{binding icf_proper_iteratorI_raw}
          val description = "ICF (internal): Rules to show properness of iterators" )

      val get = icf_proper_iteratorI.get
  
      fun add_thm thm = icf_proper_iteratorI.add_thm thm
  
      val add = Thm.declaration_attribute add_thm

      fun del_thm thm = icf_proper_iteratorI.del_thm thm

      val del = Thm.declaration_attribute del_thm

      val setup = I
        #> icf_proper_iteratorI.setup
        #> Attrib.setup @{binding icf_proper_iteratorI} 
          (Attrib.add_del add del) 
          ("ICF: Rules to show properness of iterators")
        #> Global_Theory.add_thms_dynamic (@{binding icf_proper_iteratorI}, 
             get o Context.proof_of
            )
        
  
    end
\<close>
  setup \<open>Icf_Proper_Iterator.setup\<close>

  lemma proper_iterator_trigger: 
    "proper_it it it' \<Longrightarrow> proper_it it it'"
    "proper_it' itf itf' \<Longrightarrow> proper_it' itf itf'" .

  declaration \<open>
    Tagged_Solver.declare_solver @{thms proper_iterator_trigger} 
      @{binding proper_iterator} "Proper iterator solver"
      (fn ctxt => REPEAT_ALL_NEW (resolve_tac ctxt (Icf_Proper_Iterator.get ctxt)))
\<close>

  lemma pi_foldli[icf_proper_iteratorI]: 
    "proper_it (foldli l :: ('a,'\<sigma>) set_iterator) (foldli l)"
    unfolding proper_it_def 
    by auto

  lemma pi_foldri[icf_proper_iteratorI]: 
    "proper_it (foldri l :: ('a,'\<sigma>) set_iterator) (foldri l)"
    unfolding proper_it_def foldri_def by auto

  lemma pi'_foldli[icf_proper_iteratorI]: 
    "proper_it' (foldli o tsl) (foldli o tsl)"
    apply (clarsimp simp add: proper_it'_def)
    apply (tagged_solver)
    done

  lemma pi'_foldri[icf_proper_iteratorI]: 
    "proper_it' (foldri o tsl) (foldri o tsl)"
    apply (clarsimp simp add: proper_it'_def)
    apply (tagged_solver)
    done

  text \<open>Iterator combinators preserve properness\<close>
  lemma pi_emp[icf_proper_iteratorI]: 
    "proper_it set_iterator_emp set_iterator_emp"
    unfolding proper_it_def set_iterator_emp_def[abs_def]
    by (auto intro!: ext exI[where x="[]"])

  lemma pi_sng[icf_proper_iteratorI]:
    "proper_it (set_iterator_sng x) (set_iterator_sng x)"
    unfolding proper_it_def set_iterator_sng_def[abs_def]
    by (auto intro!: ext exI[where x="[x]"])

  lemma pi_union[icf_proper_iteratorI]:
    assumes PA: "proper_it it_a it_a'"
    assumes PB: "proper_it it_b it_b'"
    shows "proper_it (set_iterator_union it_a it_b)
      (set_iterator_union it_a' it_b')"
    unfolding set_iterator_union_def
    apply (rule proper_itE[OF PA])
    apply (rule proper_itE[OF PB])
    apply (rule_tac l="l@la" in proper_itI)
    apply simp
    apply (intro conjI ext)
    apply (simp_all add: foldli_append)
    done

  lemma pi_product[icf_proper_iteratorI]:
    fixes it_a :: "('a,'\<sigma>a) set_iterator"
    fixes it_b :: "'a \<Rightarrow> ('b,'\<sigma>a) set_iterator"
    assumes PA: "proper_it it_a it_a'"
    and PB: "\<And>x. proper_it (it_b x) (it_b' x)"
    shows "proper_it (set_iterator_product it_a it_b)
      (set_iterator_product it_a' it_b')"
  proof -
    from PB have PB': "\<forall>x. proper_it (it_b x) (it_b' x)" ..
    show ?thesis
      unfolding proper_it_def
      apply (rule proper_itE[OF PA])
      apply (rule proper_it_parE[OF PB'])
      apply (auto simp add: set_iterator_product_foldli_conv)
      done
  qed

  lemma pi_image_filter[icf_proper_iteratorI]:
    fixes it :: "('x,'\<sigma>1) set_iterator" 
    and it' :: "('x,'\<sigma>2) set_iterator"
    and g :: "'x \<Rightarrow> 'y option"
    assumes P: "proper_it it it'"
    shows "proper_it (set_iterator_image_filter g it) 
      (set_iterator_image_filter g it')"
    unfolding proper_it_def
    apply (rule proper_itE[OF P])
    apply (auto simp: set_iterator_image_filter_foldli_conv)
    done

  lemma pi_filter[icf_proper_iteratorI]:
    assumes P: "proper_it it it'"
    shows "proper_it (set_iterator_filter P it) 
      (set_iterator_filter P it')"
    unfolding proper_it_def
    apply (rule proper_itE[OF P])
    by (auto simp: set_iterator_filter_foldli_conv)

  lemma pi_image[icf_proper_iteratorI]:
    assumes P: "proper_it it it'"
    shows "proper_it (set_iterator_image g it) 
      (set_iterator_image g it')"
    unfolding proper_it_def
    apply (rule proper_itE[OF P])
    by (auto simp: set_iterator_image_foldli_conv)

  lemma pi_dom[icf_proper_iteratorI]:
    assumes P: "proper_it it it'"
    shows "proper_it (map_iterator_dom it) 
      (map_iterator_dom it')"
    unfolding proper_it_def
    apply (rule proper_itE[OF P])
    by (auto simp: map_iterator_dom_foldli_conv)

  lemma set_iterator_product_eq2:
    assumes "\<forall>a\<in>set la. itb a = itb' a"
    shows "set_iterator_product (foldli la) itb
    = set_iterator_product (foldli la) itb'"
  proof (intro ext)
    fix c f \<sigma>
    show "set_iterator_product (foldli la) itb c f \<sigma>
      = set_iterator_product (foldli la) itb' c f \<sigma>"
      using assms
      unfolding set_iterator_product_def
      apply (induct la arbitrary: \<sigma>)
      apply (auto)
      done
  qed


subsubsection \<open>Optimizing Folds\<close>
  text \<open>
    Using an iterator to create a list. The optimizations will
    match the pattern \<open>foldli (it_to_list it s)\<close>
\<close>
  definition "it_to_list it s \<equiv> (it s) (\<lambda>_. True) (\<lambda>x l. l@[x]) []"

  lemma map_it_to_list_genord_correct:
    assumes A: "map_iterator_genord (it s) m (\<lambda>(k,_) (k',_). R k k')"
    shows "map_of (it_to_list it s) = m
      \<and> distinct (map fst (it_to_list it s))
      \<and> sorted_wrt R ((map fst (it_to_list it s)))"
    unfolding it_to_list_def
    apply (rule map_iterator_genord_rule_insert_P[OF A, where I="
      \<lambda>it l. map_of l = m |` it 
        \<and> distinct (map fst l) 
        \<and> sorted_wrt R ((map fst l))
      "])
    apply auto
    apply (auto simp: restrict_map_def) []
    apply (metis Some_eq_map_of_iff restrict_map_eq(2))
    apply (auto simp add: sorted_wrt_append)
    by (metis (lifting) restrict_map_eq(2) weak_map_of_SomeI)

  lemma (in linorder) map_it_to_list_linord_correct:
    assumes A: "map_iterator_linord (it s) m"
    shows "map_of (it_to_list it s) = m
      \<and> distinct (map fst (it_to_list it s))
      \<and> sorted ((map fst (it_to_list it s)))"
    using map_it_to_list_genord_correct[where it=it,
      OF A[unfolded set_iterator_map_linord_def]]
    by (simp add: sorted_sorted_wrt)

  lemma (in linorder) map_it_to_list_rev_linord_correct:
    assumes A: "map_iterator_rev_linord (it s) m"
    shows "map_of (it_to_list it s) = m
      \<and> distinct (map fst (it_to_list it s))
      \<and> sorted (rev (map fst (it_to_list it s)))"
    using map_it_to_list_genord_correct[where it=it,
      OF A[unfolded set_iterator_map_rev_linord_def]]
    by simp

 
end
