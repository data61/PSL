theory ArityTransformSafe
imports ArityTransform ArityConsistent ArityAnalysisSpec ArityEtaExpansionSafe AbstractTransform ConstOn
begin

locale CardinalityArityTransformation = ArityAnalysisLetSafeNoCard
begin
  sublocale AbstractTransformBoundSubst
    "\<lambda> a . inc\<cdot>a"
    "\<lambda> a . pred\<cdot>a"
    "\<lambda> \<Delta> e a . (a, Aheap \<Delta> e\<cdot>a)"
    "fst"
    "snd"
    "\<lambda> _. 0"
    "Aeta_expand"
    "snd"
  apply standard
  apply (simp add: Aheap_subst)
  apply (rule subst_Aeta_expand)
  done

  abbreviation ccTransform where "ccTransform \<equiv> transform"

  lemma supp_transform: "supp (transform a e) \<subseteq> supp e"
    by (induction rule: transform.induct)
       (auto simp add: exp_assn.supp Let_supp dest!: subsetD[OF supp_map_transform] subsetD[OF supp_map_transform_step] )
  interpretation supp_bounded_transform transform
    by standard (auto simp add: fresh_def supp_transform) 

  fun transform_alts :: "Arity list \<Rightarrow> stack \<Rightarrow> stack"
    where 
      "transform_alts _ [] = []"
    | "transform_alts (a#as) (Alts e1 e2 # S) = (Alts (ccTransform a e1) (ccTransform a e2)) # transform_alts as S"
    | "transform_alts as (x # S) = x # transform_alts as S"

  lemma transform_alts_Nil[simp]: "transform_alts [] S = S"
    by (induction  S) auto

  lemma Astack_transform_alts[simp]:
    "Astack (transform_alts as S) = Astack S"
   by (induction rule: transform_alts.induct) auto

  lemma fresh_star_transform_alts[intro]: "a \<sharp>* S \<Longrightarrow> a \<sharp>* transform_alts as S"
   by (induction as S  rule: transform_alts.induct) (auto simp add: fresh_star_Cons)

  fun a_transform :: "astate \<Rightarrow> conf \<Rightarrow> conf"
  where "a_transform (ae, a, as) (\<Gamma>, e, S) =
    (map_transform Aeta_expand ae (map_transform ccTransform ae \<Gamma>), 
     ccTransform a e,
     transform_alts as  S)"

  fun restr_conf :: "var set \<Rightarrow> conf \<Rightarrow> conf"
    where "restr_conf V (\<Gamma>, e, S) = (restrictA V \<Gamma>, e, restr_stack V S)"

  inductive consistent :: "astate \<Rightarrow> conf \<Rightarrow> bool" where
    consistentI[intro!]: 
    "a_consistent (ae, a, as) (\<Gamma>, e, S)
    \<Longrightarrow> (\<And> x. x \<in> thunks \<Gamma> \<Longrightarrow>  ae x = up\<cdot>0)
    \<Longrightarrow> consistent (ae, a, as) (\<Gamma>, e, S)"  
  inductive_cases consistentE[elim!]: "consistent (ae, a, as) (\<Gamma>, e, S)"

  lemma closed_consistent:
    assumes "fv e = ({}::var set)"
    shows "consistent (\<bottom>, 0, []) ([], e, [])"
  by (auto simp add: edom_empty_iff_bot closed_a_consistent[OF assms])

  lemma arity_tranform_safe:
    fixes c c'
    assumes "c \<Rightarrow>\<^sup>* c'" and "\<not> boring_step c'" and "heap_upds_ok_conf c" and "consistent (ae,a,as) c"
    shows "\<exists>ae' a' as'. consistent (ae',a',as') c' \<and> a_transform (ae,a,as) c \<Rightarrow>\<^sup>* a_transform (ae',a',as') c'"
  using assms(1,2) heap_upds_ok_invariant assms(3-)
  proof(induction c c' arbitrary: ae a as rule:step_invariant_induction)
  case (app\<^sub>1 \<Gamma> e x S)
    from app\<^sub>1 have "consistent (ae, inc\<cdot>a, as) (\<Gamma>, e, Arg x # S)"
      by (auto intro: a_consistent_app\<^sub>1)
    moreover
    have "a_transform (ae, a, as) (\<Gamma>, App e x, S) \<Rightarrow> a_transform (ae, inc\<cdot>a, as) (\<Gamma>, e, Arg x # S)"
      by simp rule
    ultimately
    show ?case by (blast del: consistentI consistentE)
  next
  case (app\<^sub>2 \<Gamma> y e x S)
    have "consistent (ae, pred\<cdot>a, as) (\<Gamma>, e[y::=x], S)" using app\<^sub>2
      by (auto 4 3 intro: a_consistent_app\<^sub>2)
    moreover
    have "a_transform (ae, a, as) (\<Gamma>, Lam [y]. e, Arg x # S) \<Rightarrow> a_transform (ae, pred \<cdot> a, as) (\<Gamma>, e[y::=x], S)" by (simp add: subst_transform[symmetric]) rule
    ultimately
    show ?case by (blast  del: consistentI consistentE)
  next
  case (thunk \<Gamma> x e S)
    hence "x \<in> thunks \<Gamma>" by auto
    hence [simp]: "x \<in> domA \<Gamma>" by (rule subsetD[OF thunks_domA])

    from \<open>heap_upds_ok_conf (\<Gamma>, Var x, S)\<close>
    have "x \<notin> upds S"  by (auto dest!: heap_upds_okE)
    
    have "x \<in> edom ae" using thunk by auto
    have "ae x = up\<cdot>0" using thunk \<open>x \<in> thunks \<Gamma>\<close> by (auto)

    have "a_consistent (ae, 0, as) (delete x \<Gamma>, e, Upd x # S)" using thunk \<open>ae x = up\<cdot>0\<close>
      by (auto intro!: a_consistent_thunk_0 simp del: restr_delete)
    hence "consistent (ae, 0, as) (delete x \<Gamma>, e, Upd x # S)" using thunk \<open>ae x = up\<cdot>0\<close> 
      by (auto simp add:  restr_delete_twist)
    moreover
  
    from  \<open>map_of \<Gamma> x = Some e\<close> \<open>ae x = up\<cdot>0\<close>
    have "map_of (map_transform Aeta_expand ae (map_transform ccTransform ae \<Gamma>)) x = Some (transform 0 e)"
      by (simp add: map_of_map_transform)
    with \<open>\<not> isVal e\<close>
    have "a_transform (ae, a, as) (\<Gamma>, Var x, S) \<Rightarrow> a_transform (ae, 0, as) (delete x \<Gamma>, e, Upd x # S)"
      by (auto simp add: map_transform_delete restr_delete_twist intro!: step.intros  simp del: restr_delete)
    ultimately
    show ?case by (blast del: consistentI consistentE)
  next
  case (lamvar \<Gamma> x e S)
    from lamvar(1) have [simp]: "x \<in> domA \<Gamma>" by (metis domI dom_map_of_conv_domA)

    have "up\<cdot>a \<sqsubseteq> (Aexp (Var x)\<cdot>a f|` (domA \<Gamma> \<union> upds S)) x"
      by (simp) (rule Aexp_Var)
    also from lamvar have "Aexp (Var x)\<cdot>a f|` (domA \<Gamma> \<union> upds S) \<sqsubseteq> ae" by (auto simp add: join_below_iff env_restr_join a_consistent.simps)
    finally
    obtain u where "ae x = up\<cdot>u" by (cases "ae x") (auto simp add: edom_def)
    hence "x \<in> edom ae" by (auto simp add: edomIff)

    have "a_consistent (ae, u, as) ((x,e) # delete x \<Gamma>, e, S)" using lamvar \<open>ae x = up\<cdot>u\<close>
      by (auto intro!: a_consistent_lamvar simp del: restr_delete)
    hence "consistent (ae, u, as) ((x, e) # delete x \<Gamma>, e, S)"
      using lamvar by (auto simp add:  thunks_Cons restr_delete_twist elim: below_trans)
    moreover

    from \<open>a_consistent _ _\<close>
    have "Astack (transform_alts as S) \<sqsubseteq> u" by (auto elim: a_consistent_stackD)
  
    {
    from \<open>isVal e\<close>
    have "isVal (transform u e)" by simp
    hence "isVal (Aeta_expand u (transform u e))" by (rule isVal_Aeta_expand)
    moreover
    from  \<open>map_of \<Gamma> x = Some e\<close>  \<open>ae x = up \<cdot> u\<close>  \<open>isVal (transform u e)\<close>
    have "map_of (map_transform Aeta_expand ae (map_transform transform ae \<Gamma>)) x = Some (Aeta_expand u (transform u e))"
      by (simp add: map_of_map_transform)
    ultimately
    have "a_transform (ae, a, as) (\<Gamma>, Var x, S) \<Rightarrow>\<^sup>*
          ((x, Aeta_expand u (transform u e)) # delete x (map_transform Aeta_expand ae (map_transform transform ae \<Gamma>)), Aeta_expand u (transform u e), transform_alts as S)"
       by (auto intro: lambda_var simp del: restr_delete)
    also have "\<dots> = ((map_transform Aeta_expand ae (map_transform transform ae ((x,e) # delete x \<Gamma>))), Aeta_expand u (transform u e), transform_alts as S)"
      using \<open>ae x = up \<cdot> u\<close> \<open>isVal (transform u e)\<close>
      by (simp add: map_transform_Cons map_transform_delete  del: restr_delete)
    also(subst[rotated]) have "\<dots> \<Rightarrow>\<^sup>* a_transform (ae, u, as) ((x, e) # delete x \<Gamma>, e, S)"
      by (simp add: restr_delete_twist) (rule Aeta_expand_safe[OF \<open>Astack _ \<sqsubseteq> u\<close>])
    finally(rtranclp_trans)
    have "a_transform (ae, a, as) (\<Gamma>, Var x, S) \<Rightarrow>\<^sup>* a_transform (ae, u, as) ((x, e) # delete x \<Gamma>, e, S)".
    }
    ultimately show ?case by (blast del: consistentI consistentE)
  next
  case (var\<^sub>2 \<Gamma> x e S)
    from var\<^sub>2
    have "a_consistent (ae, a, as) (\<Gamma>, e, Upd x # S)" by auto
    from a_consistent_UpdD[OF this]
    have "ae x = up\<cdot>0" and "a = 0".

    have "a_consistent (ae, a, as) ((x, e) # \<Gamma>, e, S)"
      using var\<^sub>2 by (auto intro!: a_consistent_var\<^sub>2)
    hence "consistent (ae, 0, as) ((x, e) # \<Gamma>, e, S)"
      using var\<^sub>2 \<open>a = 0\<close>
      by (auto simp add: thunks_Cons elim: below_trans)
    moreover
    have "a_transform (ae, a, as) (\<Gamma>, e, Upd x # S) \<Rightarrow> a_transform (ae, 0, as) ((x, e) # \<Gamma>, e, S)"
      using \<open>ae x = up\<cdot>0\<close> \<open>a = 0\<close> var\<^sub>2
      by (auto intro!: step.intros simp add: map_transform_Cons)
    ultimately show ?case by (blast del: consistentI consistentE)
  next
    case (let\<^sub>1 \<Delta> \<Gamma> e S)
    let ?ae = "Aheap \<Delta> e\<cdot>a"
  
    have "domA \<Delta> \<inter> upds S = {}" using fresh_distinct_fv[OF let\<^sub>1(2)] by (auto dest: subsetD[OF ups_fv_subset])
    hence *: "\<And> x. x \<in> upds S \<Longrightarrow> x \<notin> edom ?ae" by (auto simp add:  dest!: subsetD[OF edom_Aheap])
    have restr_stack_simp2: "restr_stack (edom (?ae \<squnion> ae)) S = restr_stack (edom ae) S"
      by (auto intro: restr_stack_cong dest!: *)

    have "edom ae \<subseteq> domA \<Gamma> \<union> upds S" using let\<^sub>1 by (auto dest!: a_consistent_edom_subsetD)
    from subsetD[OF this] fresh_distinct[OF let\<^sub>1(1)] fresh_distinct_fv[OF let\<^sub>1(2)]
    have "edom ae \<inter> domA \<Delta> = {}" by (auto dest: subsetD[OF ups_fv_subset])

    {
    { fix x e'
      assume "x \<in> thunks \<Gamma>"
      with let\<^sub>1
      have "(?ae \<squnion> ae) x = up\<cdot>0" by auto
    }
    moreover
    { fix x e'
      assume "x \<in> thunks \<Delta>" 
      hence "(?ae \<squnion> ae) x = up\<cdot>0" by (auto simp add: Aheap_heap3)
    }
    moreover
    
    have "a_consistent (ae, a, as) (\<Gamma>, Let \<Delta> e, S)"
      using let\<^sub>1 by auto
    hence "a_consistent (?ae \<squnion> ae, a, as) (\<Delta> @ \<Gamma>, e, S)"
      using let\<^sub>1(1,2) \<open>edom ae \<inter> domA \<Delta> = {}\<close> 
      by (auto intro!:  a_consistent_let simp del: join_comm)
    ultimately
    have "consistent (?ae \<squnion> ae, a, as) (\<Delta> @ \<Gamma>, e, S)"
      by auto
    }
    moreover
    {
      have "\<And> x. x \<in> domA \<Gamma> \<Longrightarrow> x \<notin> edom ?ae"
        using fresh_distinct[OF let\<^sub>1(1)]
        by (auto dest!: subsetD[OF edom_Aheap])
      hence "map_transform Aeta_expand (?ae \<squnion> ae) (map_transform transform (?ae \<squnion> ae) \<Gamma>)
         = map_transform Aeta_expand ae (map_transform transform ae \<Gamma>)"
         by (auto intro!: map_transform_cong restrictA_cong simp add: edomIff)
      moreover
  
      from \<open>edom ae \<subseteq> domA \<Gamma> \<union> upds S\<close>
      have  "\<And> x. x \<in> domA \<Delta> \<Longrightarrow> x \<notin> edom ae"
         using fresh_distinct[OF let\<^sub>1(1)] fresh_distinct_fv[OF let\<^sub>1(2)] 
         by (auto dest!:  subsetD[OF ups_fv_subset])
      hence "map_transform Aeta_expand (?ae \<squnion> ae) (map_transform transform (?ae \<squnion> ae) \<Delta>)
         = map_transform Aeta_expand ?ae (map_transform transform ?ae \<Delta>)"
         by (auto intro!: map_transform_cong restrictA_cong simp add: edomIff)
      ultimately
      
      
      have "a_transform (ae, a, as) (\<Gamma>, Let \<Delta> e, S) \<Rightarrow> a_transform (?ae \<squnion> ae,  a, as) (\<Delta> @ \<Gamma>, e, S)"
        using restr_stack_simp2 let\<^sub>1(1,2)
        apply (auto simp add: map_transform_append restrictA_append  restr_stack_simp2[simplified] map_transform_restrA)
        apply (rule step.let\<^sub>1)
        apply (auto dest: subsetD[OF edom_Aheap])
        done
    }
    ultimately
    show ?case by (blast del: consistentI consistentE)
  next
    case (if\<^sub>1 \<Gamma> scrut e1 e2 S)
    have "consistent (ae, 0, a#as) (\<Gamma>, scrut, Alts e1 e2 # S)"
      using if\<^sub>1  by (auto dest: a_consistent_if\<^sub>1)
    moreover
    have "a_transform (ae,  a, as) (\<Gamma>, scrut ? e1 : e2, S) \<Rightarrow> a_transform (ae, 0, a#as) (\<Gamma>, scrut, Alts e1 e2 # S)"
      by (auto intro: step.intros)
    ultimately
    show ?case by (blast del: consistentI consistentE)
  next
    case (if\<^sub>2 \<Gamma> b e1 e2 S)
    hence "a_consistent (ae, a, as) (\<Gamma>, Bool b, Alts e1 e2 # S)" by auto
    then  obtain a' as' where [simp]: "as = a' # as'" "a = 0"
      by (rule a_consistent_alts_on_stack)

    have "consistent (ae, a', as') (\<Gamma>, if b then e1 else e2, S)" 
      using if\<^sub>2 by (auto dest!: a_consistent_if\<^sub>2)
    moreover
    have "a_transform (ae, a, as) (\<Gamma>, Bool b, Alts e1 e2 # S) \<Rightarrow> a_transform (ae,  a', as') (\<Gamma>, if b then e1 else e2, S)"
      by (auto intro: step.if\<^sub>2[where b = True, simplified] step.if\<^sub>2[where b = False, simplified])
    ultimately
    show ?case by (blast del: consistentI consistentE)
  next
    case refl thus ?case by auto
  next
    case (trans c c' c'')
      from trans(3)[OF trans(5)]
      obtain ae' a' as' where "consistent (ae', a', as') c'" and *: "a_transform (ae, a, as) c \<Rightarrow>\<^sup>* a_transform (ae', a', as') c'" by blast
      from trans(4)[OF this(1)]
      obtain ae'' a'' as'' where "consistent (ae'', a'', as'') c''" and **: "a_transform (ae', a', as') c' \<Rightarrow>\<^sup>* a_transform (ae'', a'', as'') c''" by blast
      from this(1) rtranclp_trans[OF * **]
      show ?case by blast
  qed
end

end
