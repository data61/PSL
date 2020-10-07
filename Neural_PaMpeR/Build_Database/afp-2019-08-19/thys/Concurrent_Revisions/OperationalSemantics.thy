section \<open>Operational Semantics\<close>

text \<open>This theory defines the operational semantics of the concurrent revisions model. It also
  introduces a relaxed formulation of the operational semantics, and proves the main result required
  for establishing their equivalence.\<close>

theory OperationalSemantics
  imports Substitution
begin

context substitution
begin

subsection Definition

inductive revision_step :: "'r \<Rightarrow> ('r,'l,'v) global_state \<Rightarrow> ('r,'l,'v) global_state \<Rightarrow> bool" where
  app: "s r = Some (\<sigma>, \<tau>, \<E>[Apply (VE (Lambda x e)) (VE v)]) \<Longrightarrow> revision_step r s (s(r \<mapsto> (\<sigma>, \<tau>, \<E>[subst (VE v) x e])))"
| ifTrue: "s r = Some (\<sigma>, \<tau>, \<E>[Ite (VE (CV T)) e1 e2]) \<Longrightarrow> revision_step r s (s(r \<mapsto> (\<sigma>, \<tau>, \<E>[e1])))"
| ifFalse: "s r = Some (\<sigma>, \<tau>, \<E>[Ite (VE (CV F)) e1 e2]) \<Longrightarrow> revision_step r s (s(r \<mapsto> (\<sigma>, \<tau>, \<E>[e2])))"
(* store operations *)
| new: "s r = Some (\<sigma>, \<tau>, \<E>[Ref (VE v)]) \<Longrightarrow> l \<notin> LID\<^sub>G s \<Longrightarrow> revision_step r s (s(r \<mapsto> (\<sigma>, \<tau>(l \<mapsto> v), \<E>[VE (Loc l)])))"
| get: "s r = Some (\<sigma>, \<tau>, \<E>[Read (VE (Loc l))]) \<Longrightarrow> l \<in> dom (\<sigma>;;\<tau>) \<Longrightarrow> revision_step r s (s(r \<mapsto> (\<sigma>, \<tau>, \<E>[VE (the ((\<sigma>;;\<tau>) l))])))"
| set: "s r = Some (\<sigma>, \<tau>, \<E>[Assign (VE (Loc l)) (VE v)]) \<Longrightarrow> l \<in> dom (\<sigma>;;\<tau>) \<Longrightarrow> revision_step r s (s(r \<mapsto> (\<sigma>, \<tau>(l \<mapsto> v), \<E>[VE (CV Unit)])))"
(* synchronization operations *)
| fork: "s r = Some (\<sigma>, \<tau>, \<E>[Rfork e]) \<Longrightarrow> r' \<notin> RID\<^sub>G s \<Longrightarrow> revision_step r s (s(r \<mapsto> (\<sigma>, \<tau>, \<E>[VE (Rid r')]), r' \<mapsto> (\<sigma>;;\<tau>, \<epsilon>, e)))"
| join: "s r = Some (\<sigma>, \<tau>, \<E>[Rjoin (VE (Rid r'))]) \<Longrightarrow> s r' = Some (\<sigma>', \<tau>', VE v) \<Longrightarrow> revision_step r s (s(r := Some (\<sigma>, (\<tau>;;\<tau>'), \<E>[VE (CV Unit)]), r' := None))"
| join\<^sub>\<epsilon>: "s r = Some (\<sigma>, \<tau>, \<E>[Rjoin (VE (Rid r'))]) \<Longrightarrow> s r' = None \<Longrightarrow> revision_step r s \<epsilon>"

inductive_cases revision_stepE [elim, consumes 1, case_names app ifTrue ifFalse new get set fork join join\<^sub>\<epsilon>]:
  "revision_step r s s'"

subsection \<open>Introduction lemmas for identifiers\<close>

lemma only_new_introduces_lids [intro, dest]:
  assumes 
    step: "revision_step r s s'" and
    not_new: "\<And>\<sigma> \<tau> \<E> v. s r \<noteq> Some (\<sigma>,\<tau>,\<E>[Ref (VE v)])"
  shows "LID\<^sub>G s' \<subseteq> LID\<^sub>G s"
proof (use step in \<open>cases rule: revision_stepE\<close>)
  case fork
  thus ?thesis by (auto simp add: fun_upd_twist ID_distr_global_conditional)
next
  case (join _ _ _ r' _ _ _)
  hence "r \<noteq> r'" by auto
  thus ?thesis using join by (auto simp add: fun_upd_twist dest!: in_combination_in_component)
qed (auto simp add: not_new fun_upd_twist ID_distr_global_conditional dest: LID\<^sub>SI(2))

lemma only_fork_introduces_rids [intro, dest]:
  assumes 
    step: "revision_step r s s'" and
    not_fork: "\<And>\<sigma> \<tau> \<E> e. s r \<noteq> Some (\<sigma>,\<tau>,\<E>[Rfork e])"
  shows "RID\<^sub>G s' \<subseteq> RID\<^sub>G s"
proof (use step in \<open>cases rule: revision_stepE\<close>)
next
  case get
  then show ?thesis by (auto simp add: ID_distr_global_conditional)
next
  case fork
  then show ?thesis by (simp add: not_fork)
next
  case (join _ _ _r' _ _ _)
  hence "r \<noteq> r'" by auto
  then show ?thesis using join by (auto simp add: fun_upd_twist dest!: in_combination_in_component)
qed (auto simp add: ID_distr_global_conditional)

lemma only_fork_introduces_rids' [dest]:
  assumes 
    step: "revision_step r s s'" and
    not_fork: "\<And>\<sigma> \<tau> \<E> e. s r \<noteq> Some (\<sigma>,\<tau>,\<E>[Rfork e])"
  shows "r' \<notin> RID\<^sub>G s \<Longrightarrow> r' \<notin> RID\<^sub>G s'"
  using assms by blast

lemma only_new_introduces_lids' [dest]:
  assumes 
    step: "revision_step r s s'" and
    not_new: "\<And>\<sigma> \<tau> \<E> v. s r \<noteq> Some (\<sigma>,\<tau>,\<E>[Ref (VE v)])"
  shows "l \<notin> LID\<^sub>G s \<Longrightarrow> l \<notin> LID\<^sub>G s'"
  using assms by blast

subsection \<open>Domain subsumption\<close>

subsubsection Definitions

definition domains_subsume :: "('r,'l,'v) local_state \<Rightarrow> bool" ("\<S>") where
  "\<S> ls = (LID\<^sub>L ls \<subseteq> doms ls)"

definition domains_subsume_globally :: "('r,'l,'v) global_state \<Rightarrow> bool" ("\<S>\<^sub>G") where
  "\<S>\<^sub>G s = (\<forall>r ls. s r = Some ls \<longrightarrow> \<S> ls)"

lemma domains_subsume_globallyI [intro]:
  "(\<And>r \<sigma> \<tau> e. s r = Some (\<sigma>,\<tau>,e) \<Longrightarrow> \<S> (\<sigma>,\<tau>,e)) \<Longrightarrow> domains_subsume_globally s"
  using domains_subsume_globally_def by auto

definition subsumes_accessible :: "'r \<Rightarrow> 'r \<Rightarrow> ('r,'l,'v) global_state \<Rightarrow> bool" ("\<A>") where
  "\<A> r\<^sub>1 r\<^sub>2 s = (r\<^sub>2 \<in> RID\<^sub>L (the (s r\<^sub>1)) \<longrightarrow> (LID\<^sub>S ((the (s r\<^sub>2))\<^sub>\<sigma>) \<subseteq> doms (the (s r\<^sub>1))))"

lemma subsumes_accessibleI [intro]: 
  "(r\<^sub>2 \<in> RID\<^sub>L (the (s r\<^sub>1)) \<Longrightarrow> LID\<^sub>S ((the (s r\<^sub>2))\<^sub>\<sigma>) \<subseteq> doms (the (s r\<^sub>1))) \<Longrightarrow> \<A> r\<^sub>1 r\<^sub>2 s"
  using subsumes_accessible_def by auto

definition subsumes_accessible_globally :: "('r,'l,'v) global_state \<Rightarrow> bool" ("\<A>\<^sub>G") where
  "\<A>\<^sub>G s = (\<forall>r\<^sub>1 r\<^sub>2. r\<^sub>1 \<in> dom s \<longrightarrow> r\<^sub>2 \<in> dom s \<longrightarrow> \<A> r\<^sub>1 r\<^sub>2 s)"

lemma subsumes_accessible_globallyI [intro]:
  "(\<And>r\<^sub>1 \<sigma>\<^sub>1 \<tau>\<^sub>1 e\<^sub>1 r\<^sub>2 \<sigma>\<^sub>2 \<tau>\<^sub>2 e\<^sub>2. s r\<^sub>1 = Some (\<sigma>\<^sub>1,\<tau>\<^sub>1,e\<^sub>1) \<Longrightarrow> s r\<^sub>2 = Some (\<sigma>\<^sub>2,\<tau>\<^sub>2,e\<^sub>2) \<Longrightarrow> \<A> r\<^sub>1 r\<^sub>2 s) \<Longrightarrow> \<A>\<^sub>G s"
  using subsumes_accessible_globally_def by auto

subsubsection \<open>The theorem\<close>

lemma \<S>\<^sub>G_imp_\<A>_refl:
  assumes 
    \<S>\<^sub>G_s: "\<S>\<^sub>G s" and
    r_in_dom: "r \<in> dom s"
  shows "\<A> r r s" 
  using assms by (auto simp add: domains_subsume_def domains_subsume_globally_def subsumes_accessibleI)

lemma step_preserves_\<S>\<^sub>G_and_\<A>\<^sub>G:
  assumes 
    step: "revision_step r s s'" and
    \<S>\<^sub>G_s: "\<S>\<^sub>G s" and
    \<A>\<^sub>G_s: "\<A>\<^sub>G s"
  shows "\<S>\<^sub>G s'" "\<A>\<^sub>G s'"
proof -
  show "\<S>\<^sub>G s'"
  proof (rule domains_subsume_globallyI)
    fix r' \<sigma> \<tau> e
    assume s'_r: "s' r' = Some (\<sigma>,\<tau>,e)"
    show "\<S> (\<sigma>,\<tau>,e)"
    proof (cases "s' r' = s r'")
      case True
      then show ?thesis using \<S>\<^sub>G_s domains_subsume_globally_def s'_r by auto
    next
      case r'_was_updated: False
      show ?thesis
      proof (use step in \<open>cases rule: revision_stepE\<close>)
        case (app \<sigma>' \<tau>' \<E>' _ e' v')
        have "r = r'" by (metis fun_upd_apply app(1) r'_was_updated)
        have "LID\<^sub>L (the (s' r)) \<subseteq> LID\<^sub>S \<sigma>' \<union> LID\<^sub>S \<tau>' \<union> LID\<^sub>C \<E>' \<union> LID\<^sub>E e' \<union> LID\<^sub>V v'" using app(1) by auto
        also have "... = LID\<^sub>L (the (s r))" using app(2) by auto
        also have "... \<subseteq> doms (the (s r))" 
          by (metis \<S>\<^sub>G_s domains_subsume_def domains_subsume_globally_def local.app(2) option.sel)
        also have "... = doms (the (s' r))" using app by simp
        finally have "\<S> (the (s' r))" by (simp add: domains_subsume_def)
        thus ?thesis by (simp add: \<open>r = r'\<close> s'_r)
      next
        case ifTrue
        have "r = r'" by (metis fun_upd_apply ifTrue(1) r'_was_updated)
        have "LID\<^sub>L (the (s' r)) \<subseteq> LID\<^sub>L (the (s r))" using ifTrue by auto
        also have "... \<subseteq> doms (the (s r))"
          by (metis \<S>\<^sub>G_s domains_subsume_def domains_subsume_globally_def ifTrue(2) option.sel)
        also have "... = doms (the (s' r))" by (simp add: ifTrue)
        finally have "\<S> (the (s' r))" by (simp add: domains_subsume_def)
        thus ?thesis by (simp add: \<open>r = r'\<close> s'_r)
      next
        case ifFalse
        have "r = r'" by (metis fun_upd_apply ifFalse(1) r'_was_updated)
        have "LID\<^sub>L (the (s' r)) \<subseteq> LID\<^sub>L (the (s r))" using ifFalse by auto
        also have "... \<subseteq> doms (the (s r))"
          by (metis \<S>\<^sub>G_s domains_subsume_def domains_subsume_globally_def ifFalse(2) option.sel)
        also have "... = doms (the (s' r))" by (simp add: ifFalse)
        finally have "\<S> (the (s' r))" by (simp add: domains_subsume_def)
        thus ?thesis by (simp add: \<open>r = r'\<close> s'_r)
      next
        case (new \<sigma>' \<tau>' \<E>' v' l')
        have "r = r'" by (metis fun_upd_apply new(1) r'_was_updated)
        have "LID\<^sub>L (the (s' r)) = insert l' (LID\<^sub>S \<sigma>' \<union> LID\<^sub>S \<tau>' \<union> LID\<^sub>V v' \<union> LID\<^sub>C \<E>')"
        proof -
          have "l' \<notin> LID\<^sub>S \<tau>'" using new(2-3) by auto
          thus ?thesis using new(1) by auto
        qed
        also have "... = insert l' (LID\<^sub>L (the (s r)))" using new by auto
        also have "... \<subseteq> insert l' (doms (the (s r)))"
          by (metis \<S>\<^sub>G_s domains_subsume_def domains_subsume_globally_def insert_mono new(2) option.sel)
        also have "... = doms (the (s' r))" using new by auto
        finally have "\<S> (the (s' r))" by (simp add: domains_subsume_def)
        thus ?thesis by (simp add: \<open>r = r'\<close> s'_r)
      next
        case get
        have "r = r'" by (metis fun_upd_apply get(1) r'_was_updated)
        have "LID\<^sub>L (the (s' r)) = LID\<^sub>L (the (s r))" using get by auto
        also have "... \<subseteq> doms (the (s r))"
          by (metis \<S>\<^sub>G_s domains_subsume_def domains_subsume_globally_def get(2) option.sel)
        also have "... = doms (the (s' r))" by (simp add: get(1-2))
        finally have "\<S> (the (s' r))" by (simp add: domains_subsume_def)
        thus ?thesis by (simp add: \<open>r = r'\<close> s'_r)
      next
        case set
        have "r = r'" by (metis fun_upd_apply set(1) r'_was_updated)
        have "LID\<^sub>L (the (s' r)) \<subseteq> LID\<^sub>L (the (s r))" using set(1-2) by auto
        also have "... \<subseteq> doms (the (s r))"
          by (metis \<S>\<^sub>G_s domains_subsume_def domains_subsume_globally_def set(2) option.sel)
        also have "... \<subseteq> doms (the (s' r))" using set(1-2) by auto
        finally have "\<S> (the (s' r))" by (simp add: domains_subsume_def)
        thus ?thesis by (simp add: \<open>r = r'\<close> s'_r)
      next
        case (fork \<sigma>' \<tau>' _ _ r'')
        have "r = r' \<or> r'' = r'" using fork r'_was_updated by auto
        then show ?thesis
        proof (rule disjE)
          assume "r = r'"
          have "LID\<^sub>L (the (s' r)) \<subseteq> LID\<^sub>L (the (s r))" using fork(1-2) by auto
          also have "... \<subseteq> doms (the (s r))"
            by (metis \<S>\<^sub>G_s domains_subsume_def domains_subsume_globally_def fork(2) option.sel)
          also have "... = doms (the (s' r))" using fork by auto
          finally have "\<S> (the (s' r))" by (simp add: domains_subsume_def)
          thus ?thesis by (simp add: \<open>r = r'\<close> s'_r)
        next
          assume "r'' = r'"
          have "LID\<^sub>L (the (s' r'')) \<subseteq> LID\<^sub>L (the (s r))" using fork(1-2) by auto
          also have "... \<subseteq> doms (the (s r))"
            by (metis \<S>\<^sub>G_s domains_subsume_def domains_subsume_globally_def fork(2) option.sel)
          also have "... = dom \<sigma>' \<union> dom \<tau>'" using fork by simp
          also have "... = dom (\<sigma>';;\<tau>')"  by (simp add: dom_combination_dom_union)
          also have "... = doms (the (s' r''))" using fork by simp
          finally have "\<S> (the (s' r''))" by (simp add: domains_subsume_def)
          thus ?thesis by (simp add: \<open>r'' = r'\<close> s'_r)
        qed
      next
        case (join \<sigma>' \<tau>' _ r'' \<sigma>'' \<tau>'' _)
        have "r' = r" by (metis fun_upd_def join(1) option.simps(3) r'_was_updated s'_r)
        have "LID\<^sub>L (the (s' r)) \<subseteq> LID\<^sub>L (the (s r)) \<union> LID\<^sub>S \<tau>''" using join by auto
        also have "... \<subseteq> doms (the (s r)) \<union> LID\<^sub>S \<tau>''"
          by (metis Un_mono \<S>\<^sub>G_s domains_subsume_def domains_subsume_globally_def join(2) option.sel subset_refl)
        also have "... \<subseteq> doms (the (s r)) \<union> LID\<^sub>L (the (s r''))" using join(3) by auto
        also have "... \<subseteq> doms (the (s r)) \<union> doms (the (s r''))"
          by (metis (no_types, lifting) Un_absorb \<S>\<^sub>G_s domains_subsume_def domains_subsume_globally_def join(3) option.sel sup.orderI sup_mono)
        also have "... = dom \<sigma>' \<union> dom \<tau>' \<union> dom \<sigma>'' \<union> dom \<tau>''" using join by auto
        also have "... \<subseteq> dom \<sigma>' \<union> dom \<tau>' \<union> LID\<^sub>S \<sigma>'' \<union> dom \<tau>''" by auto
        also have "... \<subseteq> dom \<sigma>' \<union> dom \<tau>' \<union> dom \<sigma>' \<union> dom \<tau>' \<union> dom \<tau>''"
        proof -
          have r_r'': "\<A> r r'' s" using \<A>\<^sub>G_s join(2-3) subsumes_accessible_globally_def by auto
          have r_accesses_r'': "r'' \<in> RID\<^sub>L (the (s r))" using join by auto
          have "LID\<^sub>S \<sigma>'' \<subseteq> dom \<sigma>' \<union> dom \<tau>'" using join subsumes_accessible_def r_r'' r_accesses_r'' by auto
          thus ?thesis by auto
        qed
        also have "... = dom \<sigma>' \<union> dom \<tau>' \<union> dom \<tau>''" by auto
        also have "... = dom \<sigma>' \<union> dom (\<tau>';;\<tau>'')" by (auto simp add: dom_combination_dom_union)
        also have "... = doms (the (s' r))" using join by auto
        finally have "\<S> (the (s' r))" by (simp add: domains_subsume_def)
        thus ?thesis using \<open>r' = r\<close> s'_r by auto
      next
        case join\<^sub>\<epsilon>
        then show ?thesis using s'_r by blast
      qed
    qed
  qed
  show "\<A>\<^sub>G s'"
  proof (rule subsumes_accessible_globallyI)
    fix r\<^sub>1 \<sigma>\<^sub>1 \<tau>\<^sub>1 e\<^sub>1 r\<^sub>2 \<sigma>\<^sub>2 \<tau>\<^sub>2 e\<^sub>2
    assume 
      s'_r\<^sub>1: "s' r\<^sub>1 = Some (\<sigma>\<^sub>1, \<tau>\<^sub>1, e\<^sub>1)" and
      s'_r\<^sub>2: "s' r\<^sub>2 = Some (\<sigma>\<^sub>2, \<tau>\<^sub>2, e\<^sub>2)"
    show "\<A> r\<^sub>1 r\<^sub>2 s'"
    proof (cases "r\<^sub>1 = r\<^sub>2")
      case True
      then show ?thesis using \<S>\<^sub>G_imp_\<A>_refl \<open>\<S>\<^sub>G s'\<close> s'_r\<^sub>1 by blast
    next
      case r\<^sub>1_neq_r\<^sub>2: False
      have r\<^sub>1_nor_r\<^sub>2_updated_implies_thesis: "s' r\<^sub>1 = s r\<^sub>1 \<Longrightarrow> s' r\<^sub>2 = s r\<^sub>2 \<Longrightarrow> ?thesis"
      proof - 
        assume r\<^sub>1_unchanged: "s' r\<^sub>1 = s r\<^sub>1" and r\<^sub>2_unchanged: "s' r\<^sub>2 = s r\<^sub>2"
        have "\<A> r\<^sub>1 r\<^sub>2 s"
          by (metis \<A>\<^sub>G_s domIff option.discI r\<^sub>1_unchanged r\<^sub>2_unchanged s'_r\<^sub>1 s'_r\<^sub>2 subsumes_accessible_globally_def)
        show ?thesis using \<open>\<A> r\<^sub>1 r\<^sub>2 s\<close> r\<^sub>1_unchanged r\<^sub>2_unchanged subsumes_accessible_def by auto
      qed
      have r\<^sub>1_or_r\<^sub>2_updated_implies_thesis: "s' r\<^sub>1 \<noteq> s r\<^sub>1 \<or> s' r\<^sub>2 \<noteq> s r\<^sub>2 \<Longrightarrow> ?thesis"
      proof -
        assume r\<^sub>1_or_r\<^sub>2_updated: "s' r\<^sub>1 \<noteq> s r\<^sub>1 \<or> s' r\<^sub>2 \<noteq> s r\<^sub>2"
        show ?thesis
        proof (use step in \<open>cases rule: revision_stepE\<close>)
          case app
          have "r\<^sub>1 = r \<or> r\<^sub>2 = r" by (metis fun_upd_other app(1) r\<^sub>1_or_r\<^sub>2_updated)
          then show ?thesis
          proof (rule disjE)
            assume r\<^sub>1_eq_r: "r\<^sub>1 = r"
            show "\<A> r\<^sub>1 r\<^sub>2 s'"
            proof (rule subsumes_accessibleI)
              assume r\<^sub>2_in_s'_r\<^sub>1: "r\<^sub>2 \<in> RID\<^sub>L (the (s' r\<^sub>1))"
              have "LID\<^sub>S ((the (s' r\<^sub>2))\<^sub>\<sigma>) \<subseteq> LID\<^sub>S ((the (s r\<^sub>2))\<^sub>\<sigma>)" using app by auto
              also have "... \<subseteq> doms (the (s r\<^sub>1))" 
              proof -
                have r\<^sub>2_in_s_r\<^sub>1: "r\<^sub>2 \<in> RID\<^sub>L (the (s r\<^sub>1))" using app r\<^sub>2_in_s'_r\<^sub>1 r\<^sub>1_eq_r by auto
                have "\<A> r\<^sub>1 r\<^sub>2 s"
                  by (metis \<A>\<^sub>G_s domI fun_upd_other app r\<^sub>1_eq_r s'_r\<^sub>2 subsumes_accessible_globally_def)
                show ?thesis using \<open>\<A> r\<^sub>1 r\<^sub>2 s\<close> r\<^sub>2_in_s_r\<^sub>1 subsumes_accessible_def by blast
              qed
              also have "... \<subseteq> doms (the (s' r\<^sub>1))" using app by auto
              finally show "LID\<^sub>S (the (s' r\<^sub>2)\<^sub>\<sigma>) \<subseteq> doms (the (s' r\<^sub>1))" by simp
            qed
          next
            assume r\<^sub>2_eq_r: "r\<^sub>2 = r"
            show "\<A> r\<^sub>1 r\<^sub>2 s'"
            proof (rule subsumes_accessibleI)
              assume r\<^sub>2_in_s'_r\<^sub>1: "r\<^sub>2 \<in> RID\<^sub>L (the (s' r\<^sub>1))"
              have "LID\<^sub>S (the (s' r\<^sub>2)\<^sub>\<sigma>) = LID\<^sub>S (the (s r\<^sub>2)\<^sub>\<sigma>)" using app by auto
              also have "... \<subseteq> doms (the (s r\<^sub>1))"
              proof -
                have r\<^sub>2_in_s_r\<^sub>1: "r\<^sub>2 \<in> RID\<^sub>L (the (s r\<^sub>1))" using app(1) r\<^sub>1_neq_r\<^sub>2 r\<^sub>2_eq_r r\<^sub>2_in_s'_r\<^sub>1 by auto
                have "\<A> r\<^sub>1 r\<^sub>2 s"
                  by (metis (no_types, lifting) \<A>\<^sub>G_s domIff fun_upd_other app option.discI r\<^sub>2_eq_r s'_r\<^sub>1 subsumes_accessible_globally_def)
                show ?thesis using \<open>\<A> r\<^sub>1 r\<^sub>2 s\<close> r\<^sub>2_in_s_r\<^sub>1 subsumes_accessible_def by blast
              qed
              also have "... \<subseteq> doms (the (s' r\<^sub>1))" by (simp add: app)
              finally show "LID\<^sub>S (the (s' r\<^sub>2)\<^sub>\<sigma>) \<subseteq> doms (the (s' r\<^sub>1))" by simp
            qed
          qed
        next
          case ifTrue
          have "r\<^sub>1 = r \<or> r\<^sub>2 = r" by (metis fun_upd_other ifTrue(1) r\<^sub>1_or_r\<^sub>2_updated)
          then show ?thesis
          proof (rule disjE)
            assume r\<^sub>1_eq_r: "r\<^sub>1 = r"
            show "\<A> r\<^sub>1 r\<^sub>2 s'"
            proof (rule subsumes_accessibleI)
              assume r\<^sub>2_in_s'_r\<^sub>1: "r\<^sub>2 \<in> RID\<^sub>L (the (s' r\<^sub>1))"
              have "LID\<^sub>S ((the (s' r\<^sub>2))\<^sub>\<sigma>) \<subseteq> LID\<^sub>S ((the (s r\<^sub>2))\<^sub>\<sigma>)" using ifTrue by auto
              also have "... \<subseteq> doms (the (s r\<^sub>1))" 
              proof -
                have r\<^sub>2_in_s_r\<^sub>1: "r\<^sub>2 \<in> RID\<^sub>L (the (s r\<^sub>1))" using ifTrue r\<^sub>2_in_s'_r\<^sub>1 r\<^sub>1_eq_r by auto
                have "\<A> r\<^sub>1 r\<^sub>2 s"
                  by (metis \<A>\<^sub>G_s domI fun_upd_other ifTrue r\<^sub>1_eq_r s'_r\<^sub>2 subsumes_accessible_globally_def)
                show ?thesis using \<open>\<A> r\<^sub>1 r\<^sub>2 s\<close> r\<^sub>2_in_s_r\<^sub>1 subsumes_accessible_def by blast
              qed
              also have "... \<subseteq> doms (the (s' r\<^sub>1))" using ifTrue by auto
              finally show "LID\<^sub>S (the (s' r\<^sub>2)\<^sub>\<sigma>) \<subseteq> doms (the (s' r\<^sub>1))" by simp
            qed
          next
            assume r\<^sub>2_eq_r: "r\<^sub>2 = r"
            show "\<A> r\<^sub>1 r\<^sub>2 s'"
            proof (rule subsumes_accessibleI)
              assume r\<^sub>2_in_s'_r\<^sub>1: "r\<^sub>2 \<in> RID\<^sub>L (the (s' r\<^sub>1))"
              have "LID\<^sub>S (the (s' r\<^sub>2)\<^sub>\<sigma>) = LID\<^sub>S (the (s r\<^sub>2)\<^sub>\<sigma>)" using ifTrue by auto
              also have "... \<subseteq> doms (the (s r\<^sub>1))"
              proof -
                have r\<^sub>2_in_s_r\<^sub>1: "r\<^sub>2 \<in> RID\<^sub>L (the (s r\<^sub>1))" using ifTrue(1) r\<^sub>1_neq_r\<^sub>2 r\<^sub>2_eq_r r\<^sub>2_in_s'_r\<^sub>1 by auto
                have "\<A> r\<^sub>1 r\<^sub>2 s"
                  by (metis (no_types, lifting) \<A>\<^sub>G_s domIff fun_upd_other ifTrue option.discI r\<^sub>2_eq_r s'_r\<^sub>1 subsumes_accessible_globally_def)
                show ?thesis using \<open>\<A> r\<^sub>1 r\<^sub>2 s\<close> r\<^sub>2_in_s_r\<^sub>1 subsumes_accessible_def by blast
              qed
              also have "... \<subseteq> doms (the (s' r\<^sub>1))" by (simp add: ifTrue)
              finally show "LID\<^sub>S (the (s' r\<^sub>2)\<^sub>\<sigma>) \<subseteq> doms (the (s' r\<^sub>1))" by simp
            qed
          qed
        next
          case ifFalse
          have "r\<^sub>1 = r \<or> r\<^sub>2 = r" by (metis fun_upd_other ifFalse(1) r\<^sub>1_or_r\<^sub>2_updated)
          then show ?thesis
          proof (rule disjE)
            assume r\<^sub>1_eq_r: "r\<^sub>1 = r"
            show "\<A> r\<^sub>1 r\<^sub>2 s'"
            proof (rule subsumes_accessibleI)
              assume r\<^sub>2_in_s'_r\<^sub>1: "r\<^sub>2 \<in> RID\<^sub>L (the (s' r\<^sub>1))"
              have "LID\<^sub>S ((the (s' r\<^sub>2))\<^sub>\<sigma>) \<subseteq> LID\<^sub>S ((the (s r\<^sub>2))\<^sub>\<sigma>)" using ifFalse by auto
              also have "... \<subseteq> doms (the (s r\<^sub>1))" 
              proof -
                have r\<^sub>2_in_s_r\<^sub>1: "r\<^sub>2 \<in> RID\<^sub>L (the (s r\<^sub>1))" using ifFalse r\<^sub>2_in_s'_r\<^sub>1 r\<^sub>1_eq_r by auto
                have "\<A> r\<^sub>1 r\<^sub>2 s"
                  by (metis \<A>\<^sub>G_s domI fun_upd_other ifFalse r\<^sub>1_eq_r s'_r\<^sub>2 subsumes_accessible_globally_def)
                show ?thesis using \<open>\<A> r\<^sub>1 r\<^sub>2 s\<close> r\<^sub>2_in_s_r\<^sub>1 subsumes_accessible_def by blast
              qed
              also have "... \<subseteq> doms (the (s' r\<^sub>1))" using ifFalse by auto
              finally show "LID\<^sub>S (the (s' r\<^sub>2)\<^sub>\<sigma>) \<subseteq> doms (the (s' r\<^sub>1))" by simp
            qed
          next
            assume r\<^sub>2_eq_r: "r\<^sub>2 = r"
            show "\<A> r\<^sub>1 r\<^sub>2 s'"
            proof (rule subsumes_accessibleI)
              assume r\<^sub>2_in_s'_r\<^sub>1: "r\<^sub>2 \<in> RID\<^sub>L (the (s' r\<^sub>1))"
              have "LID\<^sub>S (the (s' r\<^sub>2)\<^sub>\<sigma>) = LID\<^sub>S (the (s r\<^sub>2)\<^sub>\<sigma>)" using ifFalse by auto
              also have "... \<subseteq> doms (the (s r\<^sub>1))"
              proof -
                have r\<^sub>2_in_s_r\<^sub>1: "r\<^sub>2 \<in> RID\<^sub>L (the (s r\<^sub>1))" using ifFalse(1) r\<^sub>1_neq_r\<^sub>2 r\<^sub>2_eq_r r\<^sub>2_in_s'_r\<^sub>1 by auto
                have "\<A> r\<^sub>1 r\<^sub>2 s"
                  by (metis (no_types, lifting) \<A>\<^sub>G_s domIff fun_upd_other ifFalse option.discI r\<^sub>2_eq_r s'_r\<^sub>1 subsumes_accessible_globally_def)
                show ?thesis using \<open>\<A> r\<^sub>1 r\<^sub>2 s\<close> r\<^sub>2_in_s_r\<^sub>1 subsumes_accessible_def by blast
              qed
              also have "... \<subseteq> doms (the (s' r\<^sub>1))" by (simp add: ifFalse)
              finally show "LID\<^sub>S (the (s' r\<^sub>2)\<^sub>\<sigma>) \<subseteq> doms (the (s' r\<^sub>1))" by simp
            qed
          qed
        next
          case new
          have "r\<^sub>1 = r \<or> r\<^sub>2 = r" by (metis fun_upd_other new(1) r\<^sub>1_or_r\<^sub>2_updated)
          then show ?thesis
          proof (rule disjE)
            assume r\<^sub>1_eq_r: "r\<^sub>1 = r"
            show "\<A> r\<^sub>1 r\<^sub>2 s'"
            proof (rule subsumes_accessibleI)
              assume r\<^sub>2_in_s'_r\<^sub>1: "r\<^sub>2 \<in> RID\<^sub>L (the (s' r\<^sub>1))"
              have "LID\<^sub>S ((the (s' r\<^sub>2))\<^sub>\<sigma>) \<subseteq> LID\<^sub>S ((the (s r\<^sub>2))\<^sub>\<sigma>)" using new by auto
              also have "... \<subseteq> doms (the (s r\<^sub>1))" 
              proof -
                have r\<^sub>2_in_s_r\<^sub>1: "r\<^sub>2 \<in> RID\<^sub>L (the (s r\<^sub>1))" using new r\<^sub>2_in_s'_r\<^sub>1 r\<^sub>1_eq_r by auto
                have "\<A> r\<^sub>1 r\<^sub>2 s"
                  by (metis \<A>\<^sub>G_s domI fun_upd_other new(1-2) r\<^sub>1_eq_r s'_r\<^sub>2 subsumes_accessible_globally_def)
                show ?thesis using \<open>\<A> r\<^sub>1 r\<^sub>2 s\<close> r\<^sub>2_in_s_r\<^sub>1 subsumes_accessible_def by blast
              qed
              also have "... \<subseteq> doms (the (s' r\<^sub>1))" using new by auto
              finally show "LID\<^sub>S (the (s' r\<^sub>2)\<^sub>\<sigma>) \<subseteq> doms (the (s' r\<^sub>1))" by simp
            qed
          next
            assume r\<^sub>2_eq_r: "r\<^sub>2 = r"
            show "\<A> r\<^sub>1 r\<^sub>2 s'"
            proof (rule subsumes_accessibleI)
              assume r\<^sub>2_in_s'_r\<^sub>1: "r\<^sub>2 \<in> RID\<^sub>L (the (s' r\<^sub>1))"
              have "LID\<^sub>S (the (s' r\<^sub>2)\<^sub>\<sigma>) = LID\<^sub>S (the (s r\<^sub>2)\<^sub>\<sigma>)" using new by auto
              also have "... \<subseteq> doms (the (s r\<^sub>1))"
              proof -
                have r\<^sub>2_in_s_r\<^sub>1: "r\<^sub>2 \<in> RID\<^sub>L (the (s r\<^sub>1))" using new(1) r\<^sub>1_neq_r\<^sub>2 r\<^sub>2_eq_r r\<^sub>2_in_s'_r\<^sub>1 by auto
                have "\<A> r\<^sub>1 r\<^sub>2 s"
                  by (metis (no_types, lifting) \<A>\<^sub>G_s domIff fun_upd_other new(1-2) option.discI r\<^sub>2_eq_r s'_r\<^sub>1 subsumes_accessible_globally_def)
                show ?thesis using \<open>\<A> r\<^sub>1 r\<^sub>2 s\<close> r\<^sub>2_in_s_r\<^sub>1 subsumes_accessible_def by blast
              qed
              also have "... \<subseteq> doms (the (s' r\<^sub>1))" by (auto simp add: new)
              finally show "LID\<^sub>S (the (s' r\<^sub>2)\<^sub>\<sigma>) \<subseteq> doms (the (s' r\<^sub>1))" by simp
            qed
          qed
        next
          case get
          have "r\<^sub>1 = r \<or> r\<^sub>2 = r" by (metis fun_upd_other get(1) r\<^sub>1_or_r\<^sub>2_updated)
          then show ?thesis
          proof (rule disjE)
            assume r\<^sub>1_eq_r: "r\<^sub>1 = r"
            show "\<A> r\<^sub>1 r\<^sub>2 s'"
            proof (rule subsumes_accessibleI)
              assume r\<^sub>2_in_s'_r\<^sub>1: "r\<^sub>2 \<in> RID\<^sub>L (the (s' r\<^sub>1))"
              have "LID\<^sub>S ((the (s' r\<^sub>2))\<^sub>\<sigma>) \<subseteq> LID\<^sub>S ((the (s r\<^sub>2))\<^sub>\<sigma>)" using get by auto
              also have "... \<subseteq> doms (the (s r\<^sub>1))" 
              proof -
                have r\<^sub>2_in_s_r\<^sub>1: "r\<^sub>2 \<in> RID\<^sub>L (the (s r\<^sub>1))" using get r\<^sub>2_in_s'_r\<^sub>1 r\<^sub>1_eq_r apply auto
                  by (meson RID\<^sub>SI) (* by (auto 1 3) *)
                have "\<A> r\<^sub>1 r\<^sub>2 s"
                  by (metis \<A>\<^sub>G_s domI fun_upd_other get(1-2) r\<^sub>1_eq_r s'_r\<^sub>2 subsumes_accessible_globally_def)
                show ?thesis using \<open>\<A> r\<^sub>1 r\<^sub>2 s\<close> r\<^sub>2_in_s_r\<^sub>1 subsumes_accessible_def by blast
              qed
              also have "... \<subseteq> doms (the (s' r\<^sub>1))" using get by auto
              finally show "LID\<^sub>S (the (s' r\<^sub>2)\<^sub>\<sigma>) \<subseteq> doms (the (s' r\<^sub>1))" by simp
            qed
          next
            assume r\<^sub>2_eq_r: "r\<^sub>2 = r"
            show "\<A> r\<^sub>1 r\<^sub>2 s'"
            proof (rule subsumes_accessibleI)
              assume r\<^sub>2_in_s'_r\<^sub>1: "r\<^sub>2 \<in> RID\<^sub>L (the (s' r\<^sub>1))"
              have "LID\<^sub>S (the (s' r\<^sub>2)\<^sub>\<sigma>) = LID\<^sub>S (the (s r\<^sub>2)\<^sub>\<sigma>)" using get by auto
              also have "... \<subseteq> doms (the (s r\<^sub>1))"
              proof -
                have r\<^sub>2_in_s_r\<^sub>1: "r\<^sub>2 \<in> RID\<^sub>L (the (s r\<^sub>1))" using get(1) r\<^sub>1_neq_r\<^sub>2 r\<^sub>2_eq_r r\<^sub>2_in_s'_r\<^sub>1 by auto
                have "\<A> r\<^sub>1 r\<^sub>2 s"
                  by (metis (no_types, lifting) \<A>\<^sub>G_s domIff fun_upd_other get(1-2) option.discI r\<^sub>2_eq_r s'_r\<^sub>1 subsumes_accessible_globally_def)
                show ?thesis using \<open>\<A> r\<^sub>1 r\<^sub>2 s\<close> r\<^sub>2_in_s_r\<^sub>1 subsumes_accessible_def by blast
              qed
              also have "... \<subseteq> doms (the (s' r\<^sub>1))" by (simp add: get)
              finally show "LID\<^sub>S (the (s' r\<^sub>2)\<^sub>\<sigma>) \<subseteq> doms (the (s' r\<^sub>1))" by simp
            qed
          qed
        next
          case set
          have "r\<^sub>1 = r \<or> r\<^sub>2 = r" by (metis fun_upd_other set(1) r\<^sub>1_or_r\<^sub>2_updated)
          then show ?thesis
          proof (rule disjE)
            assume r\<^sub>1_eq_r: "r\<^sub>1 = r"
            show "\<A> r\<^sub>1 r\<^sub>2 s'"
            proof (rule subsumes_accessibleI)
              assume r\<^sub>2_in_s'_r\<^sub>1: "r\<^sub>2 \<in> RID\<^sub>L (the (s' r\<^sub>1))"
              have "LID\<^sub>S ((the (s' r\<^sub>2))\<^sub>\<sigma>) \<subseteq> LID\<^sub>S ((the (s r\<^sub>2))\<^sub>\<sigma>)" using set by auto
              also have "... \<subseteq> doms (the (s r\<^sub>1))" 
              proof -
                have r\<^sub>2_in_s_r\<^sub>1: "r\<^sub>2 \<in> RID\<^sub>L (the (s r\<^sub>1))" using set r\<^sub>2_in_s'_r\<^sub>1 r\<^sub>1_eq_r by auto
                have "\<A> r\<^sub>1 r\<^sub>2 s"
                  by (metis \<A>\<^sub>G_s domI fun_upd_other set(1-2) r\<^sub>1_eq_r s'_r\<^sub>2 subsumes_accessible_globally_def)
                show ?thesis using \<open>\<A> r\<^sub>1 r\<^sub>2 s\<close> r\<^sub>2_in_s_r\<^sub>1 subsumes_accessible_def by blast
              qed
              also have "... \<subseteq> doms (the (s' r\<^sub>1))" using set by auto
              finally show "LID\<^sub>S (the (s' r\<^sub>2)\<^sub>\<sigma>) \<subseteq> doms (the (s' r\<^sub>1))" by simp
            qed
          next
            assume r\<^sub>2_eq_r: "r\<^sub>2 = r"
            show "\<A> r\<^sub>1 r\<^sub>2 s'"
            proof (rule subsumes_accessibleI)
              assume r\<^sub>2_in_s'_r\<^sub>1: "r\<^sub>2 \<in> RID\<^sub>L (the (s' r\<^sub>1))"
              have "LID\<^sub>S (the (s' r\<^sub>2)\<^sub>\<sigma>) = LID\<^sub>S (the (s r\<^sub>2)\<^sub>\<sigma>)" using set by auto
              also have "... \<subseteq> doms (the (s r\<^sub>1))"
              proof -
                have r\<^sub>2_in_s_r\<^sub>1: "r\<^sub>2 \<in> RID\<^sub>L (the (s r\<^sub>1))" using set(1) r\<^sub>1_neq_r\<^sub>2 r\<^sub>2_eq_r r\<^sub>2_in_s'_r\<^sub>1 by auto
                have "\<A> r\<^sub>1 r\<^sub>2 s"
                  by (metis (no_types, lifting) \<A>\<^sub>G_s domIff fun_upd_other set(1-2) option.discI r\<^sub>2_eq_r s'_r\<^sub>1 subsumes_accessible_globally_def)
                show ?thesis using \<open>\<A> r\<^sub>1 r\<^sub>2 s\<close> r\<^sub>2_in_s_r\<^sub>1 subsumes_accessible_def by blast
              qed
              also have "... \<subseteq> doms (the (s' r\<^sub>1))" by (auto simp add: set)
              finally show "LID\<^sub>S (the (s' r\<^sub>2)\<^sub>\<sigma>) \<subseteq> doms (the (s' r\<^sub>1))" by simp
            qed
          qed
        next
          case (fork \<sigma> \<tau> \<E> e r')
          have s'_r: "s' r = Some (\<sigma>, \<tau>, \<E> [VE (Rid r')])" using fork by auto
          have s'_r': "s' r' = Some (\<sigma>;;\<tau>, \<epsilon>, e)" 
            by (simp add: local.fork(1))
          have case1: "r\<^sub>1 = r \<Longrightarrow> r\<^sub>2 \<noteq> r \<Longrightarrow> r\<^sub>2 \<noteq> r' \<Longrightarrow> ?thesis"
          proof (rule subsumes_accessibleI)
            assume "r\<^sub>1 = r" "r\<^sub>2 \<noteq> r" "r\<^sub>2 \<noteq> r'"
            assume r\<^sub>2_in_s'_r\<^sub>1: "r\<^sub>2 \<in> RID\<^sub>L (the (s' r\<^sub>1))"
            have "LID\<^sub>S ((the (s' r\<^sub>2))\<^sub>\<sigma>) \<subseteq> LID\<^sub>S ((the (s r\<^sub>2))\<^sub>\<sigma>)" using fork(1-2) by (simp add: \<open>r\<^sub>2 \<noteq> r'\<close>)
            also have "... \<subseteq> doms (the (s r\<^sub>1))" 
            proof -
              have r\<^sub>2_in_s_r\<^sub>1: "r\<^sub>2 \<in> RID\<^sub>L (the (s r\<^sub>1))" using fork \<open>r\<^sub>1 = r\<close> \<open>r\<^sub>2 \<noteq> r'\<close> r\<^sub>2_in_s'_r\<^sub>1 s'_r by auto
              have "\<A> r\<^sub>1 r\<^sub>2 s"
                by (metis (no_types, lifting) \<A>\<^sub>G_s \<open>r\<^sub>1 = r\<close> \<open>r\<^sub>2 \<noteq> r'\<close> domIff fun_upd_other fork(1-2) option.discI s'_r\<^sub>2 subsumes_accessible_globally_def)
              show ?thesis using \<open>\<A> r\<^sub>1 r\<^sub>2 s\<close> r\<^sub>2_in_s_r\<^sub>1 subsumes_accessible_def by blast
            qed
            also have "... \<subseteq> doms (the (s' r\<^sub>1))" by (simp add: \<open>r\<^sub>1 = r\<close> fork(2) s'_r)
            finally show "LID\<^sub>S (the (s' r\<^sub>2)\<^sub>\<sigma>) \<subseteq> doms (the (s' r\<^sub>1))" by simp
          qed
          have case2: "r\<^sub>1 \<noteq> r \<Longrightarrow> r\<^sub>1 \<noteq> r' \<Longrightarrow> r\<^sub>2 = r \<Longrightarrow> ?thesis"
          proof (rule subsumes_accessibleI)
            assume "r\<^sub>1 \<noteq> r" "r\<^sub>1 \<noteq> r'" "r\<^sub>2 = r"
            assume r\<^sub>2_in_s'_r\<^sub>1: "r\<^sub>2 \<in> RID\<^sub>L (the (s' r\<^sub>1))"
            have "LID\<^sub>S ((the (s' r\<^sub>2))\<^sub>\<sigma>) \<subseteq> LID\<^sub>S ((the (s r\<^sub>2))\<^sub>\<sigma>)"
              using \<open>r\<^sub>1 \<noteq> r'\<close> \<open>r\<^sub>1 \<noteq> r\<close> fork r\<^sub>2_in_s'_r\<^sub>1 s'_r\<^sub>1 by auto
            also have "... \<subseteq> doms (the (s r\<^sub>1))" 
            proof -
              have r\<^sub>2_in_s_r\<^sub>1: "r\<^sub>2 \<in> RID\<^sub>L (the (s r\<^sub>1))" using \<open>r\<^sub>1 \<noteq> r'\<close> \<open>r\<^sub>1 \<noteq> r\<close> fork(1) r\<^sub>2_in_s'_r\<^sub>1 by auto
              have "\<A> r\<^sub>1 r\<^sub>2 s"
                by (metis (no_types, lifting) \<A>\<^sub>G_s \<open>r\<^sub>1 \<noteq> r'\<close> \<open>r\<^sub>2 = r\<close> domIff fun_upd_other fork(1-2) option.discI s'_r\<^sub>1 subsumes_accessible_globally_def)
              show ?thesis using \<open>\<A> r\<^sub>1 r\<^sub>2 s\<close> r\<^sub>2_in_s_r\<^sub>1 subsumes_accessible_def by auto
            qed
            also have "... \<subseteq> doms (the (s' r\<^sub>1))" by (simp add: \<open>r\<^sub>1 \<noteq> r'\<close> \<open>r\<^sub>1 \<noteq> r\<close> fork(1))
            finally show "LID\<^sub>S (the (s' r\<^sub>2)\<^sub>\<sigma>) \<subseteq> doms (the (s' r\<^sub>1))" by simp
          qed
          have case3: "r\<^sub>1 = r' \<Longrightarrow> r\<^sub>2 \<noteq> r \<Longrightarrow> r\<^sub>2 \<noteq> r' \<Longrightarrow> ?thesis"
          proof (rule subsumes_accessibleI)
            fix l
            assume "r\<^sub>1 = r'" "r\<^sub>2 \<noteq> r" "r\<^sub>2 \<noteq> r'"
            assume "r\<^sub>2 \<in> RID\<^sub>L (the (s' r\<^sub>1))"
            hence "r\<^sub>2 \<in> RID\<^sub>L (the (s r))" using RID\<^sub>LI(3) \<open>r\<^sub>1 = r'\<close> fork(2) s'_r' by auto
            have "s r\<^sub>2 = s' r\<^sub>2" by (simp add: \<open>r\<^sub>2 \<noteq> r'\<close> \<open>r\<^sub>2 \<noteq> r\<close> fork(1))
            hence "\<A> r r\<^sub>2 s" using \<A>\<^sub>G_s fork(2) s'_r\<^sub>2 subsumes_accessible_globally_def by auto
            hence "LID\<^sub>S (the (s' r\<^sub>2)\<^sub>\<sigma>) \<subseteq> doms (the (s r))"
              by (simp add: \<open>r\<^sub>2 \<in> RID\<^sub>L (the (s r))\<close> \<open>s r\<^sub>2 = s' r\<^sub>2\<close> subsumes_accessible_def)
            also have "... = dom \<sigma> \<union> dom \<tau>" by (simp add: fork(2))
            also have "... = dom (\<sigma>;;\<tau>)" by (simp add: dom_combination_dom_union)
            also have "... = doms (the (s' r'))" by (simp add: s'_r')
            finally show "LID\<^sub>S (the (s' r\<^sub>2)\<^sub>\<sigma>) \<subseteq> doms (the (s' r\<^sub>1))" using \<open>r\<^sub>1 = r'\<close> by blast
          qed
          have case4: "r\<^sub>1 \<noteq> r \<Longrightarrow> r\<^sub>1 \<noteq> r' \<Longrightarrow> r\<^sub>2 = r' \<Longrightarrow> ?thesis"
          proof -
            assume "r\<^sub>1 \<noteq> r" "r\<^sub>1 \<noteq> r'" "r\<^sub>2 = r'"
            have "r\<^sub>2 \<notin> RID\<^sub>L (the (s r\<^sub>1))" using \<open>r\<^sub>1 \<noteq> r'\<close> \<open>r\<^sub>1 \<noteq> r\<close> \<open>r\<^sub>2 = r'\<close> fork(1,3) s'_r\<^sub>1 by auto
            hence "r\<^sub>2 \<notin> RID\<^sub>L (the (s' r\<^sub>1))" by (simp add: \<open>r\<^sub>1 \<noteq> r'\<close> \<open>r\<^sub>1 \<noteq> r\<close> fork(1))
            thus ?thesis by blast
          qed
          have case5: "r\<^sub>1 = r \<Longrightarrow> r\<^sub>2 = r' \<Longrightarrow> ?thesis"
          proof (rule subsumes_accessibleI)
            assume "r\<^sub>1 = r" "r\<^sub>2 = r'"
            have "LID\<^sub>S ((the (s' r\<^sub>2))\<^sub>\<sigma>) = LID\<^sub>S (\<sigma>;;\<tau>)" by (simp add: \<open>r\<^sub>2 = r'\<close> s'_r')
            also have "... \<subseteq> LID\<^sub>S \<sigma> \<union> LID\<^sub>S \<tau>" by auto
            also have "... \<subseteq> LID\<^sub>L (the (s' r\<^sub>1))" by (simp add: \<open>r\<^sub>1 = r\<close> s'_r)
            also have "... \<subseteq> doms (the (s' r\<^sub>1))"
              by (metis \<open>\<S>\<^sub>G s'\<close> \<open>r\<^sub>1 = r\<close> domains_subsume_def domains_subsume_globally_def option.sel s'_r)
            finally show "LID\<^sub>S (the (s' r\<^sub>2)\<^sub>\<sigma>) \<subseteq> doms (the (s' r\<^sub>1))" by simp
          qed
          have case6: "r\<^sub>1 = r' \<Longrightarrow> r\<^sub>2 = r \<Longrightarrow> ?thesis"
          proof (rule subsumes_accessibleI)
            assume "r\<^sub>1 = r'" "r\<^sub>2 = r" "r\<^sub>2 \<in> RID\<^sub>L (the (s' r\<^sub>1))"
            have "LID\<^sub>S (the (s' r\<^sub>2)\<^sub>\<sigma>) \<subseteq> LID\<^sub>L (the (s' r\<^sub>2))" by (simp add: s'_r\<^sub>2 subsetI)
            also have "... \<subseteq> doms (the (s' r\<^sub>2))"
              using \<open>\<S>\<^sub>G s'\<close> domains_subsume_def domains_subsume_globally_def s'_r\<^sub>2 by auto
            also have "... = dom \<sigma> \<union> dom \<tau>" by (simp add: \<open>r\<^sub>2 = r\<close> s'_r)
            also have "... = dom (\<sigma>;;\<tau>)" by (simp add: dom_combination_dom_union)
            finally show " LID\<^sub>S (the (s' r\<^sub>2)\<^sub>\<sigma>) \<subseteq> doms (the (s' r\<^sub>1))"
              using \<open>r\<^sub>1 = r'\<close> s'_r' by auto
          qed
          show ?thesis using case1 case2 case3 case4 case5 case6 fork(1) r\<^sub>1_neq_r\<^sub>2 r\<^sub>1_nor_r\<^sub>2_updated_implies_thesis by fastforce
        next
          case (join \<sigma> \<tau> \<E> r' \<sigma>' \<tau>' v)
          have "r\<^sub>1 = r \<or> r\<^sub>2 = r" by (metis fun_upd_def join(1) option.simps(3) r\<^sub>1_or_r\<^sub>2_updated s'_r\<^sub>1 s'_r\<^sub>2)
          then show ?thesis
          proof (rule disjE)
            assume "r\<^sub>1 = r"
            show "\<A> r\<^sub>1 r\<^sub>2 s'"
            proof (rule subsumes_accessibleI)
              assume r\<^sub>2_in_s'_r\<^sub>1: "r\<^sub>2 \<in> RID\<^sub>L (the (s' r\<^sub>1))"
              show "LID\<^sub>S (the (s' r\<^sub>2)\<^sub>\<sigma>) \<subseteq> doms (the (s' r\<^sub>1))"
              proof (cases "r\<^sub>2 \<in> RID\<^sub>S \<tau>'")
                case r\<^sub>2_in_\<tau>': True
                have "LID\<^sub>S (the (s' r\<^sub>2)\<^sub>\<sigma>) = LID\<^sub>S (the (s r\<^sub>2)\<^sub>\<sigma>)" 
                  by (metis \<open>r\<^sub>1 = r\<close> fun_upd_def join(1) option.distinct(1) r\<^sub>1_neq_r\<^sub>2 s'_r\<^sub>2)
                also have "... \<subseteq> doms (the (s r'))"
                proof -
                  have r\<^sub>2_in_s_r': "r\<^sub>2 \<in> RID\<^sub>L (the (s r'))" by (simp add: join(3) r\<^sub>2_in_\<tau>')
                  have "\<A> r' r\<^sub>2 s"
                    by (metis \<A>\<^sub>G_s \<open>r\<^sub>1 = r\<close> domI fun_upd_def join(1) join(3) r\<^sub>1_neq_r\<^sub>2 s'_r\<^sub>2 subsumes_accessible_globally_def)
                  show ?thesis using \<open>\<A> r' r\<^sub>2 s\<close> r\<^sub>2_in_s_r' subsumes_accessible_def by blast
                qed
                also have "... = dom \<sigma>' \<union> dom \<tau>'" by (simp add: join(3))
                also have "... \<subseteq> LID\<^sub>S \<sigma>' \<union> dom \<tau>'" by auto
                also have "... \<subseteq> dom \<sigma> \<union> dom \<tau> \<union> dom \<tau>'"
                proof -
                  have "r' \<in> RID\<^sub>L (the (s r))" by (simp add: join(2))
                  have "\<A> r r' s" using \<A>\<^sub>G_s join(2-3) subsumes_accessible_globally_def by auto
                  show ?thesis using \<open>\<A> r r' s\<close> join(2-3) subsumes_accessible_def by auto
                qed
                also have "... = dom \<sigma> \<union> dom (\<tau>;;\<tau>')" by (auto simp add: dom_combination_dom_union)
                also have "... = doms (the (s' r\<^sub>1))" using join by (auto simp add: \<open>r\<^sub>1 = r\<close>)
                finally show ?thesis by simp
              next
                case r\<^sub>2_nin_\<tau>': False
                have "LID\<^sub>S (the (s' r\<^sub>2)\<^sub>\<sigma>) = LID\<^sub>S (the (s r\<^sub>2)\<^sub>\<sigma>)" 
                  by (metis \<open>r\<^sub>1 = r\<close> fun_upd_def join(1) option.distinct(1) r\<^sub>1_neq_r\<^sub>2 s'_r\<^sub>2)
                also have "... \<subseteq> doms (the (s r\<^sub>1))"
                proof -
                  have r\<^sub>2_in_s_r\<^sub>1: "r\<^sub>2 \<in> RID\<^sub>L (the (s r))"
                  proof -
                    have "RID\<^sub>L (the (s' r\<^sub>1)) = RID\<^sub>S \<sigma> \<union> RID\<^sub>S (\<tau>;;\<tau>') \<union> RID\<^sub>C \<E>"
                      by (metis (no_types, lifting) ID_distr_completion(1) ID_distr_local(2) \<open>r\<^sub>1 = r\<close> expr.simps(153) fun_upd_apply local.join(1) option.discI option.sel s'_r\<^sub>1 sup_bot.right_neutral val.simps(66))
                    hence "r\<^sub>2 \<in> RID\<^sub>S \<sigma> \<union> RID\<^sub>S \<tau> \<union> RID\<^sub>C \<E>" using r\<^sub>2_in_s'_r\<^sub>1 r\<^sub>2_nin_\<tau>' by auto
                    thus ?thesis by (simp add: join(2))
                  qed
                  have "\<A> r\<^sub>1 r\<^sub>2 s" by (metis (no_types, lifting) \<A>\<^sub>G_s \<open>r\<^sub>1 = r\<close> join(1-2) domIff fun_upd_def option.discI s'_r\<^sub>2 subsumes_accessible_globally_def)
                  show ?thesis using \<open>\<A> r\<^sub>1 r\<^sub>2 s\<close> r\<^sub>2_in_s_r\<^sub>1 subsumes_accessible_def \<open>r\<^sub>1 = r\<close> by blast
                qed
                also have "... = dom \<sigma> \<union> dom \<tau>" by (simp add: \<open>r\<^sub>1 = r\<close> join(2))
                also have "... \<subseteq> dom \<sigma> \<union> dom (\<tau>;;\<tau>')" by (auto simp add: dom_combination_dom_union)
                also have "... = doms (the (s' r\<^sub>1))" using join \<open>r\<^sub>1 = r\<close> by auto
                finally show ?thesis by simp
              qed
            qed
          next
            assume "r\<^sub>2 = r"
            show "\<A> r\<^sub>1 r\<^sub>2 s'"
            proof (rule subsumes_accessibleI)
              assume r\<^sub>2_in_s'_r\<^sub>1: "r\<^sub>2 \<in> RID\<^sub>L (the (s' r\<^sub>1))"
              have "LID\<^sub>S (the (s' r\<^sub>2)\<^sub>\<sigma>) = LID\<^sub>S (the (s r\<^sub>2)\<^sub>\<sigma>)"
                by (metis (no_types, lifting) LID_snapshot.simps fun_upd_apply join(1-2) option.discI option.sel s'_r\<^sub>2)
              also have "... \<subseteq> doms (the (s r\<^sub>1))"
              proof -
                have r\<^sub>2_in_s_r\<^sub>1: "r\<^sub>2 \<in> RID\<^sub>L (the (s r\<^sub>1))"
                  by (metis \<open>r\<^sub>2 = r\<close> fun_upd_apply local.join(1) option.discI r\<^sub>1_neq_r\<^sub>2 r\<^sub>2_in_s'_r\<^sub>1 s'_r\<^sub>1)
                have "\<A> r\<^sub>1 r\<^sub>2 s"
                  by (metis (no_types, lifting) \<A>\<^sub>G_s \<open>r\<^sub>2 = r\<close> domIff fun_upd_apply join(1-2) option.discI s'_r\<^sub>1 subsumes_accessible_globally_def)
                show ?thesis using \<open>\<A> r\<^sub>1 r\<^sub>2 s\<close> r\<^sub>2_in_s_r\<^sub>1 subsumes_accessible_def by blast
              qed
              also have "... \<subseteq> doms (the (s' r\<^sub>1))"
                by (metis \<open>r\<^sub>2 = r\<close> eq_refl fun_upd_def local.join(1) option.distinct(1) r\<^sub>1_neq_r\<^sub>2 s'_r\<^sub>1)
              finally show "LID\<^sub>S (the (s' r\<^sub>2)\<^sub>\<sigma>) \<subseteq> doms (the (s' r\<^sub>1))" by simp
            qed
          qed
        next
          case join\<^sub>\<epsilon>
          thus ?thesis using s'_r\<^sub>1 by blast
        qed
      qed
      show "\<A> r\<^sub>1 r\<^sub>2 s'" using r\<^sub>1_nor_r\<^sub>2_updated_implies_thesis r\<^sub>1_or_r\<^sub>2_updated_implies_thesis by blast
    qed
  qed
qed

subsection \<open>Relaxed definition of the operational semantics\<close>

inductive revision_step_relaxed :: "'r \<Rightarrow> ('r,'l,'v) global_state \<Rightarrow> ('r,'l,'v) global_state \<Rightarrow> bool" where
  app: "s r = Some (\<sigma>, \<tau>, \<E>[Apply (VE (Lambda x e)) (VE v)]) \<Longrightarrow> revision_step_relaxed r s (s(r \<mapsto> (\<sigma>, \<tau>, \<E>[subst (VE v) x e])))"
| ifTrue: "s r = Some (\<sigma>, \<tau>, \<E>[Ite (VE (CV T)) e1 e2]) \<Longrightarrow> revision_step_relaxed r s (s(r \<mapsto> (\<sigma>, \<tau>, \<E>[e1])))"
| ifFalse: "s r = Some (\<sigma>, \<tau>, \<E>[Ite (VE (CV F)) e1 e2]) \<Longrightarrow> revision_step_relaxed r s (s(r \<mapsto> (\<sigma>, \<tau>, \<E>[e2])))"
(* store operations *)
| new: "s r = Some (\<sigma>, \<tau>, \<E>[Ref (VE v)]) \<Longrightarrow> l \<notin> \<Union> { doms ls | ls. ls \<in> ran s } \<Longrightarrow> revision_step_relaxed r s (s(r \<mapsto> (\<sigma>, \<tau>(l \<mapsto> v), \<E>[VE (Loc l)])))"
| get: "s r = Some (\<sigma>, \<tau>, \<E>[Read (VE (Loc l))]) \<Longrightarrow> revision_step_relaxed r s (s(r \<mapsto> (\<sigma>, \<tau>, \<E>[VE (the ((\<sigma>;;\<tau>) l))])))"
| set: "s r = Some (\<sigma>, \<tau>, \<E>[Assign (VE (Loc l)) (VE v)]) \<Longrightarrow> revision_step_relaxed r s (s(r \<mapsto> (\<sigma>, \<tau>(l \<mapsto> v), \<E>[VE (CV Unit)])))"
(* synchronization operations *)
| fork: "s r = Some (\<sigma>, \<tau>, \<E>[Rfork e]) \<Longrightarrow> r' \<notin> RID\<^sub>G s \<Longrightarrow> revision_step_relaxed r s (s(r \<mapsto> (\<sigma>, \<tau>, \<E>[VE (Rid r')]), r' \<mapsto> (\<sigma>;;\<tau>, \<epsilon>, e)))"
| join: "s r = Some (\<sigma>, \<tau>, \<E>[Rjoin (VE (Rid r'))]) \<Longrightarrow> s r' = Some (\<sigma>', \<tau>', VE v) \<Longrightarrow> revision_step_relaxed r s (s(r := Some (\<sigma>, (\<tau>;;\<tau>'), \<E>[VE (CV Unit)]), r' := None))"
| join\<^sub>\<epsilon>: "s r = Some (\<sigma>, \<tau>, \<E>[Rjoin (VE (Rid r'))]) \<Longrightarrow> s r' = None \<Longrightarrow> revision_step_relaxed r s \<epsilon>"

inductive_cases revision_step_relaxedE [elim, consumes 1, case_names app ifTrue ifFalse new get set fork join join\<^sub>\<epsilon>]: 
  "revision_step_relaxed r s s'"

end (* substitution locale *)

end (* theory *)