section Executions

text \<open>This section contains all definitions required for reasoning about executions in the concurrent
  revisions model. It also contains a number of proofs for inductive variants. One of these
  proves the equivalence of the two definitions of the operational semantics. The others are
  required for proving determinacy.\<close>

theory Executions
  imports OperationalSemantics
begin

context substitution
begin

subsection \<open>Generalizing the original transition\<close>

subsubsection Definition

definition steps :: "('r,'l,'v) global_state rel" ("[\<leadsto>]") where
  "steps = { (s,s') | s s'. \<exists>r. revision_step r s s' }"

abbreviation valid_step :: "('r,'l,'v) global_state \<Rightarrow> ('r,'l,'v) global_state \<Rightarrow> bool" (infix "\<leadsto>" 60) where
  "s \<leadsto> s' \<equiv> (s,s') \<in> [\<leadsto>]"

lemma valid_stepI [intro]:
  "revision_step r s s' \<Longrightarrow> s \<leadsto> s'"
  using steps_def by auto

lemma valid_stepE [dest]:
  "s \<leadsto> s' \<Longrightarrow> \<exists>r. revision_step r s s'"
  by (simp add: steps_def)

subsubsection Closures

abbreviation refl_trans_step_rel :: "('r,'l,'v) global_state \<Rightarrow> ('r,'l,'v) global_state \<Rightarrow> bool"(infix "\<leadsto>\<^sup>*" 60) where
  "s \<leadsto>\<^sup>* s' \<equiv> (s,s') \<in> [\<leadsto>]\<^sup>*"

abbreviation refl_step_rel :: "('r,'l,'v) global_state \<Rightarrow> ('r,'l,'v) global_state \<Rightarrow> bool" (infix "\<leadsto>\<^sup>=" 60) where
  "s \<leadsto>\<^sup>= s' \<equiv> (s,s') \<in> [\<leadsto>]\<^sup>="

lemma refl_rewritesI [intro]: "s \<leadsto> s' \<Longrightarrow> s \<leadsto>\<^sup>= s'" by blast

subsection Properties

abbreviation program_expr :: "('r,'l,'v) expr \<Rightarrow> bool" where
  "program_expr e \<equiv> LID\<^sub>E e = {} \<and> RID\<^sub>E e = {}"

abbreviation initializes :: "('r,'l,'v) global_state \<Rightarrow> ('r,'l,'v) expr \<Rightarrow> bool" where
  "initializes s e \<equiv> \<exists>r. s = (\<epsilon>(r \<mapsto>(\<epsilon>,\<epsilon>,e))) \<and> program_expr e"

abbreviation initial_state :: "('r,'l,'v) global_state \<Rightarrow> bool" where
  "initial_state s \<equiv> \<exists>e. initializes s e"

definition execution :: "('r,'l,'v) expr \<Rightarrow> ('r,'l,'v) global_state \<Rightarrow> ('r,'l,'v) global_state \<Rightarrow> bool" where
  "execution e s s' \<equiv> initializes s e \<and> s \<leadsto>\<^sup>* s'"

definition maximal_execution :: "('r,'l,'v) expr \<Rightarrow> ('r,'l,'v) global_state \<Rightarrow> ('r,'l,'v) global_state \<Rightarrow> bool" where
  "maximal_execution e s s' \<equiv> execution e s s' \<and> (\<nexists>s''. s' \<leadsto> s'')"

definition reachable :: "('r,'l,'v) global_state \<Rightarrow> bool" where
  "reachable s \<equiv> \<exists>e s'. execution e s' s"

definition terminates_in :: "('r,'l,'v) expr \<Rightarrow> ('r,'l,'v) global_state \<Rightarrow> bool" (infix "\<down>" 60) where
  "e \<down> s' \<equiv> \<exists>s. maximal_execution e s s'"

subsection Invariants

subsubsection \<open>Inductive invariance\<close>

definition inductive_invariant :: "(('r,'l,'v) global_state \<Rightarrow> bool) \<Rightarrow> bool" where
  "inductive_invariant P \<equiv> (\<forall>s. initial_state s \<longrightarrow> P s) \<and> (\<forall>s s'. s \<leadsto> s' \<longrightarrow> P s \<longrightarrow> P s')"

lemma inductive_invariantI [intro]:
  "(\<And>s. initial_state s \<Longrightarrow> P s) \<Longrightarrow> (\<And>s s'. s \<leadsto> s' \<Longrightarrow> P s \<Longrightarrow> P s') \<Longrightarrow> inductive_invariant P"
  by (auto simp add: inductive_invariant_def)

lemma inductive_invariant_is_execution_invariant: "reachable s \<Longrightarrow> inductive_invariant P \<Longrightarrow> P s"
proof -
  assume reach: "reachable s" and ind_inv: "inductive_invariant P"
  then obtain e initial n where initializes: "initializes initial e" and trace: "(initial,s) \<in> [\<leadsto>]^^n"
    by (metis execution_def reachable_def rtrancl_power)
  thus "P s"
  proof (induct n arbitrary: s)
    case 0
    have "initial = s"   using "0.prems"(2) by auto
    hence "initial_state s" using initializes by blast
    then show ?case using ind_inv inductive_invariant_def by auto
  next
    case (Suc n)
    obtain s' where nfold: "(initial, s') \<in> [\<leadsto>]^^n" and step: "s' \<leadsto> s" using Suc.prems(2) by auto
    have "P s'" using Suc(1) nfold initializes by blast
    then show ?case using ind_inv step inductive_invariant_def by auto
  qed
qed

subsubsection \<open>Subsumption is invariant\<close>

lemma nice_ind_inv_is_inductive_invariant: "inductive_invariant (\<lambda>s. \<S>\<^sub>G s \<and> \<A>\<^sub>G s)"
proof (rule inductive_invariantI)
  fix s
  assume "initial_state s"
  then obtain e r where s: "s = \<epsilon>(r \<mapsto> (\<epsilon>, \<epsilon>, e))" and prog_expr_e: "program_expr e" by blast
  show "\<S>\<^sub>G s \<and> \<A>\<^sub>G s"
  proof (rule conjI)
    show "\<S>\<^sub>G s"
    proof (rule domains_subsume_globallyI)
      fix r' \<sigma>' \<tau>' e'
      assume s_r': "s r' = Some (\<sigma>',\<tau>',e')"
      have "r' = r" using s s_r' prog_expr_e by (meson domI domIff fun_upd_other)
      hence "LID\<^sub>L (\<sigma>',\<tau>',e') = LID\<^sub>L (\<epsilon>, \<epsilon>, e)" using s s_r' by auto
      also have "... = {}" using prog_expr_e by auto
      also have "... = dom \<sigma>' \<union> dom \<tau>'" using \<open>r' = r\<close> s s_r' by auto
      finally show "\<S> (\<sigma>', \<tau>', e')" by (simp add: domains_subsume_def)
    qed
    show "\<A>\<^sub>G s"
    proof (rule subsumes_accessible_globallyI)
      fix r\<^sub>1 \<sigma>\<^sub>1 \<tau>\<^sub>1 e\<^sub>1 r\<^sub>2 \<sigma>\<^sub>2 \<tau>\<^sub>2 e\<^sub>2
      assume s_r1: "s r\<^sub>1 = Some (\<sigma>\<^sub>1, \<tau>\<^sub>1, e\<^sub>1)" and s_r2: "s r\<^sub>2 = Some (\<sigma>\<^sub>2, \<tau>\<^sub>2, e\<^sub>2)"
      have "r\<^sub>2 = r" using s s_r2 prog_expr_e  by (meson domI domIff fun_upd_other)
      hence "\<sigma>\<^sub>2 = \<epsilon>" using s s_r2 by auto
      hence "LID\<^sub>S \<sigma>\<^sub>2 = {}" by auto
      thus "\<A> r\<^sub>1 r\<^sub>2 s" using s_r2 by auto
    qed
  qed
qed (use step_preserves_\<S>\<^sub>G_and_\<A>\<^sub>G in auto)

corollary reachable_imp_\<S>\<^sub>G: "reachable s \<Longrightarrow> \<S>\<^sub>G s"
proof -
  assume reach: "reachable s"
  have "\<S>\<^sub>G s \<and> \<A>\<^sub>G s" by (rule inductive_invariant_is_execution_invariant[OF reach nice_ind_inv_is_inductive_invariant]) 
  thus ?thesis by auto
qed

lemma transition_relations_equivalent: "reachable s \<Longrightarrow> revision_step r s s' = revision_step_relaxed r s s'"
proof -
  assume reach: "reachable s"
  have doms_sub_local: "\<S>\<^sub>G s" by (rule reachable_imp_\<S>\<^sub>G[OF reach])
  show "revision_step r s s' = revision_step_relaxed r s s'"
  proof (rule iffI)
    assume step: "revision_step r s s'"
    show "revision_step_relaxed r s s'"
    proof (use step in \<open>induct rule: revision_stepE\<close>)
      case (new \<sigma> \<tau> \<E> v l)
      have "revision_step_relaxed r s (s(r \<mapsto> (\<sigma>, \<tau>(l \<mapsto> v), \<E> [VE (Loc l)])))"
      proof (rule revision_step_relaxed.new)
        show "l \<notin> \<Union> { doms ls | ls. ls \<in> ran s}"
        proof 
          assume "l \<in> \<Union> { doms ls | ls. ls \<in> ran s}"
          then obtain ls where in_ran: "ls \<in> ran s" and in_doms: "l \<in> doms ls" by blast
          from in_doms have "l \<in> LID\<^sub>L ls" by (cases ls) auto
          have "l \<in> LID\<^sub>G s"
          proof -
            have "ls \<in> {ls. \<exists>r. s r = Some ls}" by (metis (full_types) in_ran ran_def)
            then show ?thesis using \<open>l \<in> LID\<^sub>L ls\<close> by blast
          qed
          thus False using new by auto
        qed
      qed (simp add: new.hyps(2))
      thus ?thesis using new.hyps(1) by blast
    qed (use revision_step_relaxed.intros in simp)+
  next
    assume step: "revision_step_relaxed r s s'"
    show "revision_step r s s'"
    proof (use step in \<open>induct rule: revision_step_relaxedE\<close>)
      case (new \<sigma> \<tau> \<E> v l)
      have "revision_step r s (s(r \<mapsto> (\<sigma>, \<tau>(l \<mapsto> v), \<E> [VE (Loc l)])))"
      proof (rule revision_step.new)
        show "s r = Some (\<sigma>, \<tau>, \<E> [Ref (VE v)])" by (simp add: new.hyps(2))
        show "l \<notin> LID\<^sub>G s"
        proof
          assume "l \<in> LID\<^sub>G s"
          then obtain r' \<sigma>' \<tau>' e' where s_r': "s r' = Some (\<sigma>',\<tau>',e')" and l_in_local: "l \<in> LID\<^sub>L (\<sigma>',\<tau>',e')" by auto
          hence "l \<in> dom \<sigma>' \<union> dom \<tau>'"
            by (metis (no_types, lifting) domains_subsume_def domains_subsume_globally_def doms.simps doms_sub_local rev_subsetD)
          thus False by (meson s_r' new.hyps(3) ranI)
        qed
      qed
      then show ?case using new.hyps(1) by blast
    next
      case (get \<sigma> \<tau> \<E> l)
      have "revision_step r s (s(r \<mapsto> (\<sigma>, \<tau>, \<E> [VE (the ((\<sigma>;;\<tau>) l))])))"
      proof 
       show "s r = Some (\<sigma>, \<tau>, \<E> [Read (VE (Loc l))])" by (simp add: get.hyps(2))
       show "l \<in> dom (\<sigma>;;\<tau>)"
       proof -
         have "l \<in> LID\<^sub>L (\<sigma>, \<tau>, \<E> [Read (VE (Loc l))])"  by simp
         hence "l \<in> dom \<sigma> \<union> dom \<tau>"
           using domains_subsume_def domains_subsume_globally_def doms_sub_local get.hyps(2) by fastforce
         thus "l \<in> dom (\<sigma>;;\<tau>)" by (simp add: dom_combination_dom_union)
       qed
     qed
     then show ?case using get.hyps(1) by auto
    next
      case (set \<sigma> \<tau> \<E> l v)
      have "revision_step r s (s(r \<mapsto> (\<sigma>, \<tau>(l \<mapsto> v), \<E> [VE (CV Unit)])))"
      proof 
       show "s r = Some (\<sigma>, \<tau>, \<E> [Assign (VE (Loc l)) (VE v)])" by (simp add: set.hyps(2))
       show "l \<in> dom (\<sigma>;;\<tau>)"
       proof -
         have "l \<in> LID\<^sub>L (\<sigma>, \<tau>, \<E> [Assign (VE (Loc l)) (VE v)])"  by simp
         hence "l \<in> dom \<sigma> \<union> dom \<tau>"
           using domains_subsume_def domains_subsume_globally_def doms_sub_local set.hyps(2) by fastforce
         thus "l \<in> dom (\<sigma>;;\<tau>)" by (simp add: dom_combination_dom_union)
       qed
     qed
     then show ?case using set.hyps(1) by blast
    qed (simp add: revision_step.intros)+
  qed
qed

subsubsection \<open>Finitude is invariant\<close>

lemma finite_occurrences_val_expr [simp]:
  fixes 
    v :: "('r,'l,'v) val" and
    e :: "('r,'l,'v) expr"
  shows
  "finite (RID\<^sub>V v)"
  "finite (RID\<^sub>E e)"
  "finite (LID\<^sub>V v)"
  "finite (LID\<^sub>E e)"
proof -
  have "(finite (RID\<^sub>V v) \<and> finite (LID\<^sub>V v)) \<and> finite (RID\<^sub>E e) \<and> finite (LID\<^sub>E e)"
    by (induct rule: val_expr.induct) auto
  thus  
    "finite (RID\<^sub>V v)"
    "finite (RID\<^sub>E e)"
    "finite (LID\<^sub>V v)"
    "finite (LID\<^sub>E e)"
    by auto
qed

lemma store_finite_upd [intro]:
  "finite (RID\<^sub>S \<tau>) \<Longrightarrow> finite (RID\<^sub>S (\<tau>(l := None)))" 
  "finite (LID\<^sub>S \<tau>) \<Longrightarrow> finite (LID\<^sub>S (\<tau>(l := None)))"
  apply (meson ID_restricted_store_subset_store(1) finite_subset)
  by (simp add: ID_restricted_store_subset_store(2) rev_finite_subset)

lemma finite_state_imp_restriction_finite [intro]: 
  "finite (RID\<^sub>G s) \<Longrightarrow> finite (RID\<^sub>G (s(r := None)))"
  "finite (LID\<^sub>G s) \<Longrightarrow> finite (LID\<^sub>G (s(r := None)))"
proof -
  assume "finite (RID\<^sub>G s)"
  thus "finite (RID\<^sub>G (s(r := None)))" by (meson infinite_super ID_restricted_global_subset_unrestricted)
next
  assume fin: "finite (LID\<^sub>G s)"
  have "LID\<^sub>G (s(r := None)) \<subseteq> LID\<^sub>G s" by auto
  thus "finite (LID\<^sub>G (s(r := None)))" using fin finite_subset by auto
qed

lemma local_state_of_finite_restricted_global_state_is_finite [intro]: 
  "s r' = Some ls \<Longrightarrow> finite (RID\<^sub>G (s(r := None))) \<Longrightarrow> r \<noteq> r' \<Longrightarrow> finite (RID\<^sub>L ls)"
  "s r' = Some ls \<Longrightarrow> finite (LID\<^sub>G (s(r := None))) \<Longrightarrow> r \<noteq> r' \<Longrightarrow> finite (LID\<^sub>L ls)"
   apply (metis (no_types, lifting) ID_distr_global(1) finite_Un finite_insert fun_upd_triv fun_upd_twist)
  by (metis ID_distr_global(2) finite_Un fun_upd_triv fun_upd_twist)

lemma empty_map_finite [simp]: 
  "finite (RID\<^sub>S \<epsilon>)" 
  "finite (LID\<^sub>S \<epsilon>)" 
  "finite (RID\<^sub>G \<epsilon>)" 
  "finite (LID\<^sub>G \<epsilon>)" 
  by (simp add: RID\<^sub>S_def LID\<^sub>S_def RID\<^sub>G_def LID\<^sub>G_def)+

lemma finite_combination [intro]:
  "finite (RID\<^sub>S \<sigma>) \<Longrightarrow> finite (RID\<^sub>S \<tau>) \<Longrightarrow> finite (RID\<^sub>S (\<sigma>;;\<tau>))"
  "finite (LID\<^sub>S \<sigma>) \<Longrightarrow> finite (LID\<^sub>S \<tau>) \<Longrightarrow> finite (LID\<^sub>S (\<sigma>;;\<tau>))"
  by (meson finite_UnI rev_finite_subset ID_combination_subset_union)+

lemma RID\<^sub>G_finite_invariant:
  assumes
    step: "revision_step r s s'" and
    fin: "finite (RID\<^sub>G s)"
shows
    "finite (RID\<^sub>G s')"
proof (use step in \<open>cases rule: revision_stepE\<close>)
  case (join \<sigma> \<tau> \<E> r' \<sigma>' \<tau>' v)
  hence "r \<noteq> r'" by auto
  then show ?thesis 
    by (metis (mono_tags, lifting) ID_distr_global(1) ID_distr_local(2) fin finite_Un finite_combination(1) finite_insert finite_occurrences_val_expr(2) finite_state_imp_restriction_finite(1) join local_state_of_finite_restricted_global_state_is_finite(1))
qed (use fin in \<open>auto simp add: ID_distr_global_conditional\<close>)

lemma RID\<^sub>L_finite_invariant:
  assumes
    step: "revision_step r s s'" and
    fin: "finite (LID\<^sub>G s)"
shows
    "finite (LID\<^sub>G s')"
proof (use step in \<open>cases rule: revision_stepE\<close>)
  case (join \<sigma> \<tau> \<E> r' \<sigma>' \<tau>' v)
  hence "r \<noteq> r'" by auto
  then show ?thesis 
    using join assms
    by (metis (mono_tags, lifting) ID_distr_global(2) ID_distr_local(1) fin finite_Un finite_combination(2) finite_occurrences_val_expr(4) finite_state_imp_restriction_finite(2) join local_state_of_finite_restricted_global_state_is_finite(2))
qed (use fin in \<open>auto simp add: ID_distr_global_conditional\<close>)
 
lemma reachable_imp_identifiers_finite:
  assumes reach: "reachable s"
  shows 
    "finite (RID\<^sub>G s)"
    "finite (LID\<^sub>G s)"
proof -
  from reach obtain e r where exec: "execution e (\<epsilon>(r \<mapsto> (\<epsilon>,\<epsilon>,e))) s" using reachable_def execution_def by auto
  hence prog_exp: "program_expr e" by (meson execution_def)
  obtain n where n_reachable: "(\<epsilon>(r \<mapsto> (\<epsilon>,\<epsilon>,e)), s) \<in> [\<leadsto>]^^n" using exec by (meson execution_def rtrancl_imp_relpow)
  hence "finite (RID\<^sub>G s) \<and> finite (LID\<^sub>G s)"
  proof (induct n arbitrary: s)
    case 0
    hence s: "s = \<epsilon>(r \<mapsto> (\<epsilon>, \<epsilon>, e))" by auto
    hence rid_dom: "dom s = {r}" by auto
    hence rid_ran: "\<Union> (RID\<^sub>L ` ran s) = {}" using s by (auto simp add: prog_exp)
    have rids: "RID\<^sub>G s = {r}" by (unfold RID\<^sub>G_def, use rid_dom rid_ran in auto)
    have lid_ran: "\<Union> (LID\<^sub>L ` ran s) = {}" using s by (auto simp add: prog_exp)
    hence lids: "LID\<^sub>G s = {}" by (unfold LID\<^sub>G_def, simp)
    thus ?case using rids lids by simp
  next
    case (Suc n)
    then obtain s' where 
      n_steps: "(\<epsilon>(r \<mapsto> (\<epsilon>, \<epsilon>, e)), s') \<in> [\<leadsto>]^^n" and 
      step: "s' \<leadsto> s" 
      by (meson relpow_Suc_E)
    have fin_rid: "finite (RID\<^sub>G s')" using Suc.hyps n_steps by blast
    have fin_lid: "finite (LID\<^sub>G s')" using Suc.hyps n_steps by blast
    thus ?case by (meson RID\<^sub>G_finite_invariant RID\<^sub>L_finite_invariant fin_rid local.step valid_stepE)
  qed
  thus "finite (RID\<^sub>G s)" "finite (LID\<^sub>G s)" by auto
qed

lemma reachable_imp_identifiers_available:
  assumes 
    "reachable (s :: ('r,'l,'v) global_state)"
  shows 
    "infinite (UNIV :: 'r set) \<Longrightarrow> \<exists>r. r \<notin> RID\<^sub>G s"
    "infinite (UNIV :: 'l set) \<Longrightarrow> \<exists>l. l \<notin> LID\<^sub>G s"
  by (simp add: assms ex_new_if_finite reachable_imp_identifiers_finite)+

subsubsection \<open>Reachability is invariant\<close>

lemma initial_state_reachable:
  assumes "program_expr e"
  shows "reachable (\<epsilon>(r \<mapsto> (\<epsilon>,\<epsilon>,e)))"
proof -
  have "initializes (\<epsilon>(r \<mapsto> (\<epsilon>,\<epsilon>,e))) e" using assms by auto
  hence "execution e (\<epsilon>(r \<mapsto> (\<epsilon>,\<epsilon>,e))) (\<epsilon>(r \<mapsto> (\<epsilon>,\<epsilon>,e)))" by (simp add: execution_def)
  thus ?thesis using reachable_def by blast
qed

lemma reachability_closed_under_execution_step:
  assumes
    reach: "reachable s" and
    step: "revision_step r s s'"
  shows "reachable s'"
proof -
  obtain init e where exec: "execution e init s" using reach reachable_def by blast
  hence init_s:"init \<leadsto>\<^sup>* s" by (simp add: execution_def)
  have s_s': "s \<leadsto> s'" using step by blast 
  have "init \<leadsto>\<^sup>* s'" using init_s s_s' by auto
  hence "execution e init s'" using exec by (simp add: execution_def)
  thus ?thesis using reachable_def by auto
qed

lemma reachability_closed_under_execution: "reachable s \<Longrightarrow> s \<leadsto>\<^sup>* s' \<Longrightarrow> reachable s'"
proof -
  assume reach: "reachable s" and "s \<leadsto>\<^sup>* s'"
  then obtain n where "(s, s') \<in> [\<leadsto>]^^n" using rtrancl_imp_relpow by blast
  thus "reachable s'"
  proof (induct n arbitrary: s')
    case 0
    thus ?case using reach by auto
  next 
    case (Suc n)
    obtain s'' where "(s,s'') \<in> [\<leadsto>]^^n" "s'' \<leadsto> s'" using Suc.prems by auto
    have "reachable s''" by (simp add: Suc.hyps \<open>(s, s'') \<in> [\<leadsto>]^^n\<close>)
    then show ?case using \<open>s'' \<leadsto> s'\<close> reachability_closed_under_execution_step by blast
  qed
qed

end (* substitution locale *)

end (* theory *)