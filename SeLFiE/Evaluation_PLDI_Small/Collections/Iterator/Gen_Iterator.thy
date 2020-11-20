section \<open>\isaheader{Iterators}\<close>
theory Gen_Iterator
imports Refine_Monadic.Refine_Monadic Proper_Iterator
begin
  text \<open>
    Iterators are realized by to-list functions followed by folding.
    A post-optimization step then replaces these constructions by
    real iterators.\<close>

  lemma param_it_to_list[param]: "(it_to_list,it_to_list) \<in>
    (Rs \<rightarrow> (Ra \<rightarrow> bool_rel) \<rightarrow> 
    (Rb \<rightarrow> \<langle>Rb\<rangle>list_rel \<rightarrow> \<langle>Rb\<rangle>list_rel) \<rightarrow> \<langle>Rc\<rangle>list_rel \<rightarrow> Rd) \<rightarrow> Rs \<rightarrow> Rd"
    unfolding it_to_list_def[abs_def]
    by parametricity


  definition key_rel :: "('k \<Rightarrow> 'k \<Rightarrow> bool) \<Rightarrow> ('k\<times>'v) \<Rightarrow> ('k\<times>'v) \<Rightarrow> bool"
    where "key_rel R a b \<equiv> R (fst a) (fst b)"

  lemma key_rel_UNIV[simp]: "key_rel (\<lambda>_ _. True) = (\<lambda>_ _. True)"
    unfolding key_rel_def[abs_def] by auto

  subsection \<open>Setup for Autoref\<close>
  text \<open>Default pattern rules for \<open>it_to_sorted_list\<close>\<close>
  definition "set_to_sorted_list R S \<equiv> it_to_sorted_list R S"
  lemma set_to_sorted_list_itype[autoref_itype]: 
    "set_to_sorted_list R ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>\<langle>I\<rangle>\<^sub>ii_list\<rangle>\<^sub>ii_nres" 
    by simp

context begin interpretation autoref_syn .
  lemma set_to_sorted_list_pat[autoref_op_pat]: 
    "it_to_sorted_list R S \<equiv> OP (set_to_sorted_list R) S"
    unfolding set_to_sorted_list_def[abs_def] by auto
end

  definition "map_to_sorted_list R M 
    \<equiv> it_to_sorted_list (key_rel R) (map_to_set M)"
  lemma map_to_sorted_list_itype[autoref_itype]:
    "map_to_sorted_list R ::\<^sub>i \<langle>Rk,Rv\<rangle>\<^sub>ii_map \<rightarrow>\<^sub>i \<langle>\<langle>\<langle>Rk,Rv\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_list\<rangle>\<^sub>ii_nres"
    by simp

context begin interpretation autoref_syn .
  lemma map_to_sorted_list_pat[autoref_op_pat]:
    "it_to_sorted_list (key_rel R) (map_to_set M) 
      \<equiv> OP (map_to_sorted_list R) M"
    "it_to_sorted_list (\<lambda>_ _. True) (map_to_set M) 
      \<equiv> OP (map_to_sorted_list (\<lambda>_ _. True)) M"
    unfolding map_to_sorted_list_def[abs_def] by auto
end

  subsection \<open>Set iterators\<close>
  (*definition "is_set_to_sorted_list_deprecated ordR Rk Rs tsl \<equiv> \<forall>s s'.
    (s,s')\<in>\<langle>Rk\<rangle>Rs \<longrightarrow> 
      (RETURN (tsl s),it_to_sorted_list ordR s')\<in>\<langle>\<langle>Rk\<rangle>list_rel\<rangle>nres_rel"
    *)

  definition "is_set_to_sorted_list ordR Rk Rs tsl \<equiv> \<forall>s s'.
    (s,s')\<in>\<langle>Rk\<rangle>Rs 
      \<longrightarrow> ( \<exists>l'. (tsl s,l')\<in>\<langle>Rk\<rangle>list_rel 
            \<and> RETURN l' \<le> it_to_sorted_list ordR s')"

  definition "is_set_to_list \<equiv> is_set_to_sorted_list (\<lambda>_ _. True)"


  lemma is_set_to_sorted_listE:
    assumes "is_set_to_sorted_list ordR Rk Rs tsl"
    assumes "(s,s')\<in>\<langle>Rk\<rangle>Rs"
    obtains l' where "(tsl s,l')\<in>\<langle>Rk\<rangle>list_rel" 
    and "RETURN l' \<le> it_to_sorted_list ordR s'"
    using assms unfolding is_set_to_sorted_list_def by blast

  (* TODO: Move *)
  lemma it_to_sorted_list_weaken: 
    "R\<le>R' \<Longrightarrow> it_to_sorted_list R s \<le> it_to_sorted_list R' s"
    unfolding it_to_sorted_list_def
    by (auto intro!: sorted_wrt_mono_rel[where P=R])

  lemma set_to_list_by_set_to_sorted_list[autoref_ga_rules]:
    assumes "GEN_ALGO_tag (is_set_to_sorted_list ordR Rk Rs tsl)"
    shows "is_set_to_list Rk Rs tsl"
    using assms
    unfolding is_set_to_list_def is_set_to_sorted_list_def autoref_tag_defs
    apply (safe)
    apply (drule spec, drule spec, drule (1) mp)
    apply (elim exE conjE)
    apply (rule exI, rule conjI, assumption)
    apply (rule order_trans, assumption)
    apply (rule it_to_sorted_list_weaken)
    by blast


  definition "det_fold_set R c f \<sigma> result \<equiv> 
    \<forall>l. distinct l \<and> sorted_wrt R l \<longrightarrow> foldli l c f \<sigma> = result (set l)"

  lemma det_fold_setI[intro?]:
    assumes "\<And>l. \<lbrakk>distinct l; sorted_wrt R l\<rbrakk> 
      \<Longrightarrow> foldli l c f \<sigma> = result (set l)"
    shows "det_fold_set R c f \<sigma> result"
    using assms unfolding det_fold_set_def by auto

  text \<open>Template lemma for generic algorithm using set iterator\<close>
  lemma det_fold_sorted_set:
    assumes 1: "det_fold_set ordR c' f' \<sigma>' result"
    assumes 2: "is_set_to_sorted_list ordR Rk Rs tsl"
    assumes SREF[param]: "(s,s')\<in>\<langle>Rk\<rangle>Rs"
    assumes [param]:  "(c,c')\<in>R\<sigma>\<rightarrow>Id"
    assumes [param]: "(f,f')\<in>Rk \<rightarrow> R\<sigma> \<rightarrow> R\<sigma>"
    assumes [param]: "(\<sigma>,\<sigma>')\<in>R\<sigma>"
    shows "(foldli (tsl s) c f \<sigma>, result s') \<in> R\<sigma>"
  proof -
    obtain tsl' where
      [param]: "(tsl s,tsl') \<in> \<langle>Rk\<rangle>list_rel" 
      and IT: "RETURN tsl' \<le> it_to_sorted_list ordR s'"
      using 2 SREF
      by (rule is_set_to_sorted_listE)
    
    have "(foldli (tsl s) c f \<sigma>, foldli tsl' c' f' \<sigma>') \<in> R\<sigma>"
      by parametricity
    also have "foldli tsl' c' f' \<sigma>' = result s'"
      using 1 IT 
      unfolding det_fold_set_def it_to_sorted_list_def
      by simp
    finally show ?thesis .
  qed

  lemma det_fold_set:
    assumes "det_fold_set (\<lambda>_ _. True) c' f' \<sigma>' result"
    assumes "is_set_to_list Rk Rs tsl"
    assumes "(s,s')\<in>\<langle>Rk\<rangle>Rs"
    assumes "(c,c')\<in>R\<sigma>\<rightarrow>Id"
    assumes "(f,f')\<in>Rk \<rightarrow> R\<sigma> \<rightarrow> R\<sigma>"
    assumes "(\<sigma>,\<sigma>')\<in>R\<sigma>"
    shows "(foldli (tsl s) c f \<sigma>, result s') \<in> R\<sigma>"
    using assms
    unfolding  is_set_to_list_def
    by (rule det_fold_sorted_set)

  subsection \<open>Map iterators\<close>

  text \<open>Build relation on keys\<close>
  
  (*definition "is_map_to_sorted_list_deprecated ordR Rk Rv Rm tsl \<equiv> \<forall>m m'.
    (m,m')\<in>\<langle>Rk,Rv\<rangle>Rm \<longrightarrow> 
      (RETURN (tsl m),it_to_sorted_list (key_rel ordR) (map_to_set m'))
      \<in>\<langle>\<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel\<rangle>nres_rel"*)

  definition "is_map_to_sorted_list ordR Rk Rv Rm tsl \<equiv> \<forall>m m'.
    (m,m')\<in>\<langle>Rk,Rv\<rangle>Rm \<longrightarrow> (
      \<exists>l'. (tsl m,l')\<in>\<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel
        \<and> RETURN l' \<le> it_to_sorted_list (key_rel ordR) (map_to_set m'))"

  definition "is_map_to_list Rk Rv Rm tsl 
    \<equiv> is_map_to_sorted_list (\<lambda>_ _. True) Rk Rv Rm tsl"

  lemma is_map_to_sorted_listE:
    assumes "is_map_to_sorted_list ordR Rk Rv Rm tsl"
    assumes "(m,m')\<in>\<langle>Rk,Rv\<rangle>Rm"
    obtains l' where "(tsl m,l')\<in>\<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel" 
    and "RETURN l' \<le> it_to_sorted_list (key_rel ordR) (map_to_set m')"
    using assms unfolding is_map_to_sorted_list_def by blast

  lemma map_to_list_by_map_to_sorted_list[autoref_ga_rules]:
    assumes "GEN_ALGO_tag (is_map_to_sorted_list ordR Rk Rv Rm tsl)"
    shows "is_map_to_list Rk Rv Rm tsl"
    using assms
    unfolding is_map_to_list_def is_map_to_sorted_list_def autoref_tag_defs
    apply (safe)
    apply (drule spec, drule spec, drule (1) mp)
    apply (elim exE conjE)
    apply (rule exI, rule conjI, assumption)
    apply (rule order_trans, assumption)
    apply (rule it_to_sorted_list_weaken)
    unfolding key_rel_def[abs_def]
    by blast

  definition "det_fold_map R c f \<sigma> result \<equiv> 
    \<forall>l. distinct (map fst l) \<and> sorted_wrt (key_rel R) l 
      \<longrightarrow> foldli l c f \<sigma> = result (map_of l)"

  lemma det_fold_mapI[intro?]:
    assumes "\<And>l. \<lbrakk>distinct (map fst l); sorted_wrt (key_rel R) l\<rbrakk> 
      \<Longrightarrow> foldli l c f \<sigma> = result (map_of l)"
    shows "det_fold_map R c f \<sigma> result"
    using assms unfolding det_fold_map_def by auto

  lemma det_fold_map_aux:
    assumes 1: "\<lbrakk>distinct (map fst l); sorted_wrt (key_rel R) l \<rbrakk>
      \<Longrightarrow> foldli l c f \<sigma> = result (map_of l)"
    assumes 2: "RETURN l \<le> it_to_sorted_list (key_rel R) (map_to_set m)"
    shows "foldli l c f \<sigma> = result m"
  proof -
    from 2 have "distinct l" and "set l = map_to_set m" 
      and SORTED: "sorted_wrt (key_rel R) l"
      unfolding it_to_sorted_list_def by simp_all
    hence "\<forall>(k,v)\<in>set l. \<forall>(k',v')\<in>set l. k=k' \<longrightarrow> v=v'"
      apply simp
      unfolding map_to_set_def
      apply auto
      done
    with \<open>distinct l\<close> have DF: "distinct (map fst l)"
      apply (induct l)
      apply simp
      apply force
      done
    with \<open>set l = map_to_set m\<close> have [simp]: "m = map_of l"
      by (metis map_of_map_to_set)
      
    from 1[OF DF SORTED] show ?thesis by simp
  qed
    
  text \<open>Template lemma for generic algorithm using map iterator\<close>
  lemma det_fold_sorted_map:
    assumes 1: "det_fold_map ordR c' f' \<sigma>' result"
    assumes 2: "is_map_to_sorted_list ordR Rk Rv Rm tsl"
    assumes MREF[param]: "(m,m')\<in>\<langle>Rk,Rv\<rangle>Rm"
    assumes [param]:  "(c,c')\<in>R\<sigma>\<rightarrow>Id"
    assumes [param]: "(f,f')\<in>\<langle>Rk,Rv\<rangle>prod_rel \<rightarrow> R\<sigma> \<rightarrow> R\<sigma>"
    assumes [param]: "(\<sigma>,\<sigma>')\<in>R\<sigma>"
    shows "(foldli (tsl m) c f \<sigma>, result m') \<in> R\<sigma>"
  proof -
    obtain tsl' where
      [param]: "(tsl m,tsl') \<in> \<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel" 
      and IT: "RETURN tsl' \<le> it_to_sorted_list (key_rel ordR) (map_to_set m')"
      using 2 MREF by (rule is_map_to_sorted_listE)
    
    have "(foldli (tsl m) c f \<sigma>, foldli tsl' c' f' \<sigma>') \<in> R\<sigma>"
      by parametricity
    also have "foldli tsl' c' f' \<sigma>' = result m'"
      using det_fold_map_aux[of tsl' ordR c' f' \<sigma>' result] 1 IT
      unfolding det_fold_map_def
      by clarsimp
    finally show ?thesis .
  qed

  lemma det_fold_map:
    assumes "det_fold_map (\<lambda>_ _. True) c' f' \<sigma>' result"
    assumes "is_map_to_list Rk Rv Rm tsl"
    assumes "(m,m')\<in>\<langle>Rk,Rv\<rangle>Rm"
    assumes "(c,c')\<in>R\<sigma>\<rightarrow>Id"
    assumes "(f,f')\<in>\<langle>Rk,Rv\<rangle>prod_rel \<rightarrow> R\<sigma> \<rightarrow> R\<sigma>"
    assumes "(\<sigma>,\<sigma>')\<in>R\<sigma>"
    shows "(foldli (tsl m) c f \<sigma>, result m') \<in> R\<sigma>"
    using assms
    unfolding is_map_to_list_def
    by (rule det_fold_sorted_map)

lemma set_to_sorted_list_by_tsl[autoref_rules]:
  assumes "MINOR_PRIO_TAG (- 11)"
  assumes TSL: "SIDE_GEN_ALGO (is_set_to_sorted_list R Rk Rs tsl)"
  shows "(\<lambda>s. RETURN (tsl s), set_to_sorted_list R) 
    \<in> \<langle>Rk\<rangle>Rs \<rightarrow> \<langle>\<langle>Rk\<rangle>list_rel\<rangle>nres_rel"
proof (intro fun_relI nres_relI)
  fix s s'
  assume "(s,s')\<in>\<langle>Rk\<rangle>Rs"
  with TSL obtain l' where 
    R1: "(tsl s, l') \<in> \<langle>Rk\<rangle>list_rel" 
      and R2: "RETURN l' \<le> set_to_sorted_list R s'"
    unfolding is_set_to_sorted_list_def set_to_sorted_list_def autoref_tag_defs
    by blast
  
  have "RETURN (tsl s) \<le> \<Down>(\<langle>Rk\<rangle>list_rel) (RETURN l')"
    by (rule RETURN_refine) fact
  also note R2
  finally show "RETURN (tsl s) \<le> \<Down> (\<langle>Rk\<rangle>list_rel) (set_to_sorted_list R s')" .
qed

lemma set_to_list_by_tsl[autoref_rules]:
  assumes "MINOR_PRIO_TAG (- 10)"
  assumes TSL: "SIDE_GEN_ALGO (is_set_to_list Rk Rs tsl)"
  shows "(\<lambda>s. RETURN (tsl s), set_to_sorted_list (\<lambda>_ _. True)) 
    \<in> \<langle>Rk\<rangle>Rs \<rightarrow> \<langle>\<langle>Rk\<rangle>list_rel\<rangle>nres_rel"
  using assms(2-) unfolding is_set_to_list_def
  by (rule set_to_sorted_list_by_tsl[OF PRIO_TAGI])

lemma map_to_sorted_list_by_tsl[autoref_rules]:
  assumes "MINOR_PRIO_TAG (- 11)"
  assumes TSL: "SIDE_GEN_ALGO (is_map_to_sorted_list R Rk Rv Rs tsl)"
  shows "(\<lambda>s. RETURN (tsl s), map_to_sorted_list R) 
    \<in> \<langle>Rk,Rv\<rangle>Rs \<rightarrow> \<langle>\<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel\<rangle>nres_rel"
proof (intro fun_relI nres_relI)
  fix s s'
  assume "(s,s')\<in>\<langle>Rk,Rv\<rangle>Rs"
  with TSL obtain l' where 
    R1: "(tsl s, l') \<in> \<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel" 
      and R2: "RETURN l' \<le> map_to_sorted_list R s'"
    unfolding is_map_to_sorted_list_def map_to_sorted_list_def autoref_tag_defs
    by blast
  
  have "RETURN (tsl s) \<le> \<Down>(\<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel) (RETURN l')"
    apply (rule RETURN_refine)
    by fact
  also note R2
  finally show 
    "RETURN (tsl s) \<le> \<Down> (\<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel) (map_to_sorted_list R s')" .
qed

lemma map_to_list_by_tsl[autoref_rules]:
  assumes "MINOR_PRIO_TAG (- 10)"
  assumes TSL: "SIDE_GEN_ALGO (is_map_to_list Rk Rv Rs tsl)"
  shows "(\<lambda>s. RETURN (tsl s), map_to_sorted_list (\<lambda>_ _. True)) 
    \<in> \<langle>Rk,Rv\<rangle>Rs \<rightarrow> \<langle>\<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel\<rangle>nres_rel"
  using assms(2-) unfolding is_map_to_list_def
  by (rule map_to_sorted_list_by_tsl[OF PRIO_TAGI])


(*lemma dres_it_FOREACH_it_simp[iterator_simps]: 
  "dres_it_FOREACH (\<lambda>s. dRETURN (i s)) s c f \<sigma> 
    = foldli (i s) (case_dres False False c) (\<lambda>x s. s \<bind> f x) (dRETURN \<sigma>)"
  unfolding dres_it_FOREACH_def
  by simp
*)

text \<open>
  TODO/FIXME: 
    * Integrate mono-prover properly into solver-infrastructure,
        i.e. tag a mono-goal.
    * Tag iterators, such that, for the mono-prover, we can just convert
        a proper iterator back to its foldli-equivalent!
\<close>
lemma proper_it_mono_dres_pair:
  assumes PR: "proper_it' it it'"
  assumes A: "\<And>k v x. f k v x \<le> f' k v x"
  shows "
    it' s (case_dres False False c) (\<lambda>(k,v) s. s \<bind> f k v) \<sigma>
    \<le> it' s (case_dres False False c) (\<lambda>(k,v) s. s \<bind> f' k v) \<sigma>" (is "?a \<le> ?b")
proof -
  from proper_itE[OF PR[THEN proper_it'D]] obtain l where 
    A_FMT: 
      "?a = foldli l (case_dres False False c) (\<lambda>(k,v) s. s \<bind> f k v) \<sigma>" 
        (is "_ = ?a'")
    and B_FMT: 
      "?b = foldli l (case_dres False False c) (\<lambda>(k,v) s. s \<bind> f' k v) \<sigma>" 
        (is "_ = ?b'")
    by metis
  
  from A have A': "\<And>kv x. case_prod f kv x \<le> case_prod f' kv x"
    by auto

  note A_FMT
  also have 
    "?a' = foldli l (case_dres False False c) (\<lambda>kv s. s \<bind> case_prod f kv) \<sigma>"
    apply (fo_rule fun_cong)
    apply (fo_rule arg_cong)
    by auto
  also note foldli_mono_dres[OF A']
  also have 
    "foldli l (case_dres False False c) (\<lambda>kv s. s \<bind> case_prod f' kv) \<sigma> = ?b'"
    apply (fo_rule fun_cong)
    apply (fo_rule arg_cong)
    by auto
  also note B_FMT[symmetric]
  finally show ?thesis .
qed

lemma proper_it_mono_dres_pair_flat:
  assumes PR: "proper_it' it it'"
  assumes A: "\<And>k v x. flat_ge (f k v x) (f' k v x)"
  shows "
    flat_ge (it' s (case_dres False False c) (\<lambda>(k,v) s. s \<bind> f k v) \<sigma>)
      (it' s (case_dres False False c) (\<lambda>(k,v) s. s \<bind> f' k v) \<sigma>)" 
      (is "flat_ge ?a ?b")
proof -
  from proper_itE[OF PR[THEN proper_it'D]] obtain l where 
    A_FMT: 
      "?a = foldli l (case_dres False False c) (\<lambda>(k,v) s. s \<bind> f k v) \<sigma>" 
        (is "_ = ?a'")
    and B_FMT: 
      "?b = foldli l (case_dres False False c) (\<lambda>(k,v) s. s \<bind> f' k v) \<sigma>" 
        (is "_ = ?b'")
    by metis
  
  from A have A': "\<And>kv x. flat_ge (case_prod f kv x) (case_prod f' kv x)"
    by auto

  note A_FMT
  also have 
    "?a' = foldli l (case_dres False False c) (\<lambda>kv s. s \<bind> case_prod f kv) \<sigma>"
    apply (fo_rule fun_cong)
    apply (fo_rule arg_cong)
    by auto
  also note foldli_mono_dres_flat[OF A']
  also have 
    "foldli l (case_dres False False c) (\<lambda>kv s. s \<bind> case_prod f' kv) \<sigma> = ?b'"
    apply (fo_rule fun_cong)
    apply (fo_rule arg_cong)
    by auto
  also note B_FMT[symmetric]
  finally show ?thesis .
qed

    
lemma proper_it_mono_dres:
  assumes PR: "proper_it' it it'"
  assumes A: "\<And>kv x. f kv x \<le> f' kv x"
  shows "
    it' s (case_dres False False c) (\<lambda>kv s. s \<bind> f kv) \<sigma>
    \<le> it' s (case_dres False False c) (\<lambda>kv s. s \<bind> f' kv) \<sigma>"
  apply (rule proper_itE[OF PR[THEN proper_it'D[where s=s]]])
  apply (erule_tac t="it' s" in ssubst)
  apply (rule foldli_mono_dres[OF A])
  done

lemma proper_it_mono_dres_flat:
  assumes PR: "proper_it' it it'"
  assumes A: "\<And>kv x. flat_ge (f kv x) (f' kv x)"
  shows "
    flat_ge (it' s (case_dres False False c) (\<lambda>kv s. s \<bind> f kv) \<sigma>)
      (it' s (case_dres False False c) (\<lambda>kv s. s \<bind> f' kv) \<sigma>)"
  apply (rule proper_itE[OF PR[THEN proper_it'D[where s=s]]])
  apply (erule_tac t="it' s" in ssubst)
  apply (rule foldli_mono_dres_flat[OF A])
  done

lemma pi'_dom[icf_proper_iteratorI]: "proper_it' it it' 
  \<Longrightarrow> proper_it' (map_iterator_dom o it) (map_iterator_dom o it')"
  apply (rule proper_it'I)
  apply (simp add: comp_def)
  apply (rule icf_proper_iteratorI)
  apply (erule proper_it'D)
  done

lemma proper_it_mono_dres_dom:
  assumes PR: "proper_it' it it'"
  assumes A: "\<And>kv x. f kv x \<le> f' kv x"
  shows "
    (map_iterator_dom o it') s (case_dres False False c) (\<lambda>kv s. s \<bind> f kv) \<sigma>
    \<le> 
    (map_iterator_dom o it') s (case_dres False False c) (\<lambda>kv s. s \<bind> f' kv) \<sigma>"
  
  apply (rule proper_it_mono_dres)
  apply (rule icf_proper_iteratorI)
  by fact+

lemma proper_it_mono_dres_dom_flat:
  assumes PR: "proper_it' it it'"
  assumes A: "\<And>kv x. flat_ge (f kv x) (f' kv x)"
  shows "flat_ge 
    ((map_iterator_dom o it') s (case_dres False False c) (\<lambda>kv s. s \<bind> f kv) \<sigma>)
    ((map_iterator_dom o it') s (case_dres False False c) (\<lambda>kv s. s \<bind> f' kv) \<sigma>)"
  apply (rule proper_it_mono_dres_flat)
  apply (rule icf_proper_iteratorI)
  by fact+


(* TODO/FIXME: Hack! Mono-prover should be able to find proper-iterators itself
*)
lemmas proper_it_monos = 
  proper_it_mono_dres_pair proper_it_mono_dres_pair_flat
  proper_it_mono_dres proper_it_mono_dres_flat
  proper_it_mono_dres_dom proper_it_mono_dres_dom_flat

(* TODO: Conceptually, this leads to some kind of bundles: 
  Each bundle has a list of processors, that are invoked for every registered
  theorem. *)


attribute_setup "proper_it" = \<open>
  Scan.succeed (Thm.declaration_attribute (fn thm => fn context => 
    let
      val mono_thms = map_filter (try (curry (RS) thm)) @{thms proper_it_monos}
      (*val mono_thms = map (fn mt => thm RS mt) @{thms proper_it_monos}*)
      val context = context 
        |> Icf_Proper_Iterator.add_thm thm
        |> fold Refine_Mono_Prover.add_mono_thm mono_thms
    in
      context
    end
  ))
\<close>
  "Proper iterator declaration"

end
