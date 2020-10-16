theory It_to_It
imports 
  Proper_Iterator
begin

  lemma proper_it_fold: 
    "proper_it it it' \<Longrightarrow> foldli (it (\<lambda>_. True) (\<lambda>x l. l@[x]) []) = it'"
    unfolding proper_it_def by auto
  lemma proper_it_unfold: 
    "proper_it it it' \<Longrightarrow> it' = foldli (it (\<lambda>_. True) (\<lambda>x l. l@[x]) [])"
    unfolding proper_it_def by auto


  text \<open>The following constant converts an iterator over list-state
    to an iterator over arbitrary state\<close>
  definition it_to_it :: "('x,'x list) set_iterator \<Rightarrow> ('x,'\<sigma>) set_iterator"
    where [code del]: "it_to_it it 
    \<equiv> (foldli (it (\<lambda>_. True) (\<lambda>x l. l@[x]) []))"

  lemma pi_it_to_it[icf_proper_iteratorI]: "proper_it (it_to_it I) (it_to_it I)"
    unfolding it_to_it_def by (rule pi_foldli)
  text \<open>In case of a proper iterator, it is equivalent to direct iteration\<close>
  lemma it_to_it_fold: "proper_it it (it'::('x,'\<sigma>) set_iterator) 
    \<Longrightarrow> it_to_it it = it'"
    unfolding it_to_it_def
    by (simp add: proper_it_fold)

  lemma it_to_it_map_fold:
    assumes P: "proper_it it it'"
    shows "it_to_it (\<lambda>c f. it c (f \<circ> f')) = (\<lambda>c f. it' c (f o f'))"
    apply (rule proper_itE[OF P])
    unfolding it_to_it_def
    apply (intro ext)
    apply (simp add: foldli_foldl map_by_foldl foldli_map)
    done

  lemma it_to_it_fold': "proper_it' it (it'::'s \<Rightarrow> ('x,'\<sigma>) set_iterator) 
    \<Longrightarrow> it_to_it (it s) = (it' s)"
    by (drule proper_it'D) (rule it_to_it_fold)

  lemma it_to_it_map_fold':
    assumes P: "proper_it' it it'"
    shows "it_to_it (\<lambda>c f. it s c (f \<circ> f')) = (\<lambda>c f. it' s c (f o f'))"
    using P[THEN proper_it'D] by (rule it_to_it_map_fold)

  text \<open>This locale wraps up the setup of a proper iterator for use
    with \<open>it_to_it\<close>.\<close>
  locale proper_it_loc =
    fixes it :: "'s \<Rightarrow> ('x,'x list) set_iterator"
    and it' :: "'s \<Rightarrow> ('x,'\<sigma>) set_iterator"
    assumes proper': "proper_it' it it'"
  begin
    lemma proper: "proper_it (it s) (it' s)"
      using proper' by (rule proper_it'D)

    lemmas it_to_it_code_unfold[code_unfold] = it_to_it_fold[OF proper]
  end

  subsubsection \<open>Correctness\<close>
  text \<open>The polymorphic iterator is a valid iterator again.\<close>
  lemma it_to_it_genord_correct: 
    assumes "set_iterator_genord (it::('x,'x list) set_iterator) S R" 
    shows "set_iterator_genord ((it_to_it it)::('x,'\<sigma>) set_iterator) S R"
  proof -
    interpret set_iterator_genord it S R by fact

    show ?thesis
      apply (unfold_locales)
      unfolding it_to_it_def
      using foldli_transform
      by auto
  qed

  lemma it_to_it_linord_correct: 
    assumes "set_iterator_linord (it::('x::linorder,'x list) set_iterator) S" 
    shows "set_iterator_linord ((it_to_it it)::('x,'\<sigma>) set_iterator) S"
    using assms
    unfolding set_iterator_linord_def
    by (rule it_to_it_genord_correct)

  lemma it_to_it_rev_linord_correct: 
    assumes "set_iterator_rev_linord (it::('x::linorder,'x list) set_iterator) S"
    shows "set_iterator_rev_linord ((it_to_it it)::('x,'\<sigma>) set_iterator) S"
    using assms
    unfolding set_iterator_rev_linord_def
    by (rule it_to_it_genord_correct)

  lemma it_to_it_correct: 
    assumes "set_iterator (it::('x,'x list) set_iterator) S" 
    shows "set_iterator ((it_to_it it)::('x,'\<sigma>) set_iterator) S"
    using assms
    unfolding set_iterator_def
    by (rule it_to_it_genord_correct)

  lemma it_to_it_map_genord_correct:
    assumes "map_iterator_genord (it::('u,'v,('u\<times>'v) list) map_iterator) S R" 
    shows "map_iterator_genord ((it_to_it it)::('u,'v,'\<sigma>) map_iterator) S R"
    using assms by (rule it_to_it_genord_correct)

  lemma it_to_it_map_linord_correct:
    assumes "map_iterator_linord (it::('u::linorder,'v,('u\<times>'v) list) map_iterator) S" 
    shows "map_iterator_linord ((it_to_it it)::('u,'v,'\<sigma>) map_iterator) S"
    using assms unfolding set_iterator_map_linord_def by (rule it_to_it_genord_correct)

  lemma it_to_it_map_rev_linord_correct:
    assumes 
      "map_iterator_rev_linord (it::('u::linorder,'v,('u\<times>'v) list) map_iterator) S" 
    shows "map_iterator_rev_linord ((it_to_it it)::('u,'v,'\<sigma>) map_iterator) S"
    using assms unfolding set_iterator_map_rev_linord_def 
    by (rule it_to_it_genord_correct)

  lemma it_to_it_map_correct:
    assumes "map_iterator (it::('u,'v,('u\<times>'v) list) map_iterator) S" 
    shows "map_iterator ((it_to_it it)::('u,'v,'\<sigma>) map_iterator) S"
    using assms by (rule it_to_it_correct)






end
