section Determinacy

text \<open>This section proves that the concurrent revisions model is determinate modulo renaming-equivalence.\<close>

theory Determinacy
  imports Executions
begin

context substitution
begin

subsection \<open>Rule determinism\<close>

lemma app_deterministic [simp]:
  assumes
    s_r: "s r = Some (\<sigma>, \<tau>, \<E> [Apply (VE (Lambda x e)) (VE v)])"
  shows "(revision_step r s s') = (s' = (s(r \<mapsto> (\<sigma>, \<tau>, \<E> [subst (VE v) x e]))))" (is "?l = ?r")
proof (rule iffI)
  assume ?l
  thus ?r by (cases rule: revision_stepE) (use s_r in auto)
qed (simp add: s_r revision_step.app)

lemma ifTrue_deterministic [simp]:
  assumes
    s_r: "s r = Some (\<sigma>, \<tau>, \<E> [Ite (VE (CV T)) e1 e2])"
  shows "(revision_step r s s') = (s' = (s(r \<mapsto> (\<sigma>, \<tau>, \<E> [e1]))))" (is "?l = ?r")
proof (rule iffI)
  assume ?l
  thus ?r by (cases rule: revision_stepE) (use s_r in auto)
qed (simp add: s_r revision_step.ifTrue)

lemma ifFalse_deterministic [simp]:
  assumes
    s_r: "s r = Some (\<sigma>, \<tau>, \<E> [Ite (VE (CV F)) e1 e2])"
  shows "(revision_step r s s') = (s' = (s(r \<mapsto> (\<sigma>, \<tau>, \<E> [e2]))))" (is "?l = ?r")
proof (rule iffI)
  assume ?l
  thus ?r by (cases rule: revision_stepE) (use s_r in auto)
qed (simp add: s_r revision_step.ifFalse)

lemma new_pseudodeterministic [simp]:
  assumes
    s_r: "s r = Some (\<sigma>, \<tau>, \<E> [Ref (VE v)])"
  shows "(revision_step r s s') = (\<exists>l. l \<notin> LID\<^sub>G s \<and> s' = (s(r \<mapsto> (\<sigma>, \<tau>(l \<mapsto> v), \<E> [VE (Loc l)]))))" (is "?l = ?r")
proof (rule iffI)
  assume ?l
  thus ?r by (cases rule: revision_stepE) (use s_r in auto)
qed (auto simp add: s_r revision_step.new)

lemma get_deterministic [simp]:
  assumes
    s_r: "s r = Some (\<sigma>, \<tau>, \<E> [Read (VE (Loc l))])"
  shows "(revision_step r s s') = (l \<in> dom (\<sigma>;;\<tau>) \<and> s' = (s(r \<mapsto> (\<sigma>, \<tau>, \<E> [VE (the ((\<sigma>;;\<tau>) l))]))))" (is "?l = ?r")
proof (rule iffI)
  assume ?l
  thus ?r by (cases rule: revision_stepE) (use s_r in auto)
qed (use revision_step.get in \<open>auto simp add: s_r\<close>)

lemma set_deterministic [simp]:
  assumes
    s_r: "s r = Some (\<sigma>, \<tau>, \<E> [Assign (VE (Loc l)) (VE v)])"
  shows "(revision_step r s s') = (l \<in> dom (\<sigma>;;\<tau>) \<and> s' = (s(r \<mapsto> (\<sigma>, \<tau>(l \<mapsto> v), \<E> [VE (CV Unit)]))))" (is "?l = ?r")
proof (rule iffI)
  assume ?l
  thus ?r by (cases rule: revision_stepE) (use s_r in auto)
qed (auto simp add: s_r revision_step.set)

lemma fork_pseudodeterministic [simp]:
  assumes
    s_r: "s r = Some (\<sigma>, \<tau>, \<E> [Rfork e])"
  shows "(revision_step r s s') = (\<exists>r'. r' \<notin> RID\<^sub>G (s(r \<mapsto> (\<sigma>, \<tau>, \<E> [Rfork e]))) \<and> s' = (s(r \<mapsto> (\<sigma>, \<tau>, \<E> [VE (Rid r')]), r' \<mapsto> (\<sigma>;;\<tau>, \<epsilon>, e))))" (is "?l = ?r")
proof (rule iffI)
  assume step: ?l
  show ?r
  proof (use step in \<open>cases rule: revision_stepE\<close>)
    case (fork \<sigma> \<tau> \<E> e r')
    show ?thesis by (rule exI[where x=r']) (use fork s_r in auto)
  qed (auto simp add: s_r)
qed (auto simp add: s_r revision_step.fork map_upd_triv)

lemma rjoin_deterministic [simp]:
  assumes
    s_r: "s r = Some (\<sigma>, \<tau>, \<E> [Rjoin (VE (Rid r'))])" and
    s_r': "s r' = Some (\<sigma>', \<tau>', VE v)"
  shows "(revision_step r s s') = (s' = (s(r := Some (\<sigma>, \<tau>;;\<tau>', \<E> [VE (CV Unit)]), r' := None)))" (is "?l = ?r")
proof (rule iffI)
  assume step: ?l
  show ?r by (cases rule: revision_stepE[OF step]) (use s_r s_r' in auto)
qed (meson s_r s_r' revision_step.join)

lemma rjoin\<^sub>\<epsilon>_deterministic [simp]:
  assumes
    s_r: "s r = Some (\<sigma>, \<tau>, \<E> [Rjoin (VE (Rid r'))])" and
    s_r': "s r' = None"
  shows "(revision_step r s s') = (s' = \<epsilon>)" (is "?l = ?r")
proof (rule iffI)
  assume step: ?l
  show ?r by (cases rule: revision_stepE[OF step]) (use s_r s_r' in auto)
qed (simp add: revision_step.join\<^sub>\<epsilon> s_r s_r')

subsection \<open>Strong local confluence\<close>

subsubsection \<open>Local determinism\<close>

lemma local_determinism:
  assumes
    left: "revision_step r s\<^sub>1 s\<^sub>2" and
    right: "revision_step r s\<^sub>1 s\<^sub>2'"
  shows "s\<^sub>2 \<approx> s\<^sub>2'"
proof (use left in \<open>induct rule:revision_stepE\<close>)
  case (new \<sigma> \<tau> \<E> v l)
  from new(2) right obtain l' where 
    side: "l' \<notin> LID\<^sub>G s\<^sub>1" and
    s\<^sub>2': "s\<^sub>2' = s\<^sub>1(r \<mapsto> (\<sigma>, \<tau>(l' \<mapsto> v), \<E>[VE (Loc l')]))"
    by auto
  let "?\<beta>" = "id(l := l', l' := l)"
  have bij_\<beta>: "bij ?\<beta>" by (rule swap_bij)
  have renaming: "\<R>\<^sub>G id ?\<beta> s\<^sub>2 = s\<^sub>2'" 
    by (use new side s\<^sub>2' bij_\<beta> in \<open>auto simp add: ID_distr_global_conditional\<close>)
  show ?case by (rule eq_statesI[OF renaming bij_id bij_\<beta>])
next
  case (fork \<sigma> \<tau> \<E> e r')
  from fork(2) right obtain r'' where 
    side: "r'' \<notin> RID\<^sub>G s\<^sub>1" and
    s\<^sub>2': "s\<^sub>2' = s\<^sub>1(r \<mapsto> (\<sigma>, \<tau>, \<E> [VE (Rid r'')]), r'' \<mapsto> (\<sigma>;;\<tau>, \<epsilon>, e))"
    by (auto simp add: ID_distr_global_conditional)
  let "?\<alpha>" = "id(r' := r'', r'' := r')"
  have bij_\<alpha>: "bij ?\<alpha>" by (rule swap_bij)
  have renaming: "\<R>\<^sub>G ?\<alpha> id s\<^sub>2 = s\<^sub>2'" 
    by (use fork side s\<^sub>2' bij_\<alpha> in \<open>auto simp add: ID_distr_global_conditional\<close>)
  show ?case by (rule eq_statesI[OF renaming bij_\<alpha> bij_id])
qed ((rule eq_statesI[of id id], use assms in auto)[1])+

subsubsection \<open>General principles\<close>

lemma SLC_sym:
  "\<exists>s\<^sub>3' s\<^sub>3. s\<^sub>3' \<approx> s\<^sub>3 \<and> (revision_step r' s\<^sub>2 s\<^sub>3' \<or> s\<^sub>2 = s\<^sub>3') \<and> (revision_step r s\<^sub>2' s\<^sub>3 \<or> s\<^sub>2' = s\<^sub>3) \<Longrightarrow>
   \<exists>s\<^sub>3 s\<^sub>3'. s\<^sub>3 \<approx> s\<^sub>3' \<and> (revision_step r s\<^sub>2' s\<^sub>3 \<or> s\<^sub>2' = s\<^sub>3) \<and> (revision_step r' s\<^sub>2 s\<^sub>3' \<or> s\<^sub>2 = s\<^sub>3')"
  by (metis \<alpha>\<beta>_sym)

lemma SLC_commute: 
  "\<lbrakk> s\<^sub>3 = s\<^sub>3'; revision_step r' s\<^sub>2 s\<^sub>3; revision_step r s\<^sub>2' s\<^sub>3' \<rbrakk> \<Longrightarrow> 
  s\<^sub>3 \<approx> s\<^sub>3' \<and> (revision_step r' s\<^sub>2 s\<^sub>3 \<or> s\<^sub>2 = s\<^sub>3) \<and> (revision_step r s\<^sub>2' s\<^sub>3' \<or> s\<^sub>2' = s\<^sub>3')"
  using \<alpha>\<beta>_refl by auto

subsubsection \<open>Case join-epsilon\<close>

lemma SLC_join\<^sub>\<epsilon>:
  assumes
    s\<^sub>1_r: "s\<^sub>1 r = Some (\<sigma>, \<tau>, \<E>[Rjoin (VE (Rid r''))])" and
    s\<^sub>2: "s\<^sub>2 = \<epsilon>" and
    side: "s\<^sub>1 r'' = None" and
    right: "revision_step r' s\<^sub>1 s\<^sub>2'" and
    neq: "r \<noteq> r'"
  shows
    "\<exists>s\<^sub>3 s\<^sub>3'. s\<^sub>3 \<approx> s\<^sub>3' \<and> (revision_step r' s\<^sub>2 s\<^sub>3 \<or> s\<^sub>2 = s\<^sub>3) \<and> (revision_step r s\<^sub>2' s\<^sub>3' \<or> s\<^sub>2' = s\<^sub>3')"
proof -
  have right_collapsed_case: "s\<^sub>2' = \<epsilon> \<Longrightarrow> ?thesis" 
    by (rule exI[where x=\<epsilon>], rule exI[where x=\<epsilon>], use s\<^sub>2 in auto)
  have left_step_still_available_case: "s\<^sub>2' \<noteq> \<epsilon> \<Longrightarrow> s\<^sub>2' r = s\<^sub>1 r \<Longrightarrow> s\<^sub>2' r'' = None \<Longrightarrow> ?thesis"
    by (rule exI[where x=\<epsilon>], rule exI[where x=\<epsilon>]) (use assms in auto)
  show ?thesis
  proof (use right in \<open>cases rule: revision_stepE\<close>)
    case (join _ _ _ right_joinee)
    have r_unchanged_left: "s\<^sub>2' r = s\<^sub>1 r" using join assms by auto
    have r'_unchanged_right: "s\<^sub>2' r'' = None" using join assms by auto
    have "right_joinee \<noteq> r'" using join(2-3) by auto
    hence s\<^sub>2'_nonempty: "s\<^sub>2' \<noteq> \<epsilon>" using assms join by (auto simp add: fun_upd_twist)
    show ?thesis by (rule left_step_still_available_case[OF s\<^sub>2'_nonempty r_unchanged_left r'_unchanged_right])
  next
    case join\<^sub>\<epsilon>
    show ?thesis by (rule right_collapsed_case, use join\<^sub>\<epsilon>(2-3) right in auto)
  qed ((rule left_step_still_available_case, use side neq s\<^sub>1_r right in auto)[1])+
qed

subsubsection \<open>Case join\<close>

lemma join_and_local_commute:
  assumes
    "s\<^sub>2 = s\<^sub>1(r := Some (\<sigma>, \<tau>;;\<tau>', \<E>[VE (CV Unit)]), r'' := None)"
    "s\<^sub>2' = s\<^sub>1(r' \<mapsto> ls)"
    "r \<noteq> r'"
    "r' \<noteq> r''"
    "revision_step r' s\<^sub>2 (s\<^sub>1(r := Some (\<sigma>, \<tau>;;\<tau>', \<E>[VE (CV Unit)]), r'' := None, r' := Some ls))"
    "s\<^sub>2' r = Some (\<sigma>, \<tau>, \<E> [Rjoin (VE (Rid r''))])"
    "s\<^sub>2' r'' = Some (\<sigma>', \<tau>', VE v)"
  shows
    "\<exists>s\<^sub>3 s\<^sub>3'. s\<^sub>3 \<approx> s\<^sub>3' \<and> (revision_step r' s\<^sub>2 s\<^sub>3 \<or> s\<^sub>2 = s\<^sub>3) \<and> (revision_step r s\<^sub>2' s\<^sub>3' \<or> s\<^sub>2' = s\<^sub>3')"
  apply (rule exI[where x="s\<^sub>1(r := Some (\<sigma>, \<tau>;;\<tau>', \<E>[VE (CV Unit)]), r'' := None, r' := Some ls)"])
  apply (rule exI[where x="s\<^sub>1(r' := Some ls, r := Some (\<sigma>, \<tau>;;\<tau>', \<E>[VE (CV Unit)]), r'' := None)"])
  by (rule SLC_commute, use assms in auto)

lemma SLC_join:
  assumes
    s\<^sub>1_r: "s\<^sub>1 r = Some (\<sigma>, \<tau>, \<E>[Rjoin (VE (Rid r''))])" and
    s\<^sub>2: "s\<^sub>2 = (s\<^sub>1(r := Some (\<sigma>, (\<tau>;;\<tau>'), \<E>[VE (CV Unit)]), r'' := None))" and
    side: "s\<^sub>1 r'' = Some (\<sigma>', \<tau>', VE v)" and 
    right: "revision_step r' s\<^sub>1 s\<^sub>2'" and
    neq: "r \<noteq> r'"
  shows
    "\<exists>s\<^sub>3 s\<^sub>3'. s\<^sub>3 \<approx> s\<^sub>3' \<and> (revision_step r' s\<^sub>2 s\<^sub>3 \<or> s\<^sub>2 = s\<^sub>3) \<and> (revision_step r s\<^sub>2' s\<^sub>3' \<or> s\<^sub>2' = s\<^sub>3')"
proof -
  have left_step: "revision_step r s\<^sub>1 s\<^sub>2" using s\<^sub>1_r s\<^sub>2 side by auto
  have r'_not_joined: "r' \<noteq> r''" using right side by auto
  show ?thesis
  proof (use right in \<open>cases rule: revision_stepE\<close>)
    case (new _ _ _ _ l)
    have l_fresh_left: "l \<notin> LID\<^sub>G s\<^sub>2" by (rule only_new_introduces_lids'[OF left_step]) (use new right s\<^sub>1_r in auto)
    show ?thesis by (rule join_and_local_commute, use assms r'_not_joined new l_fresh_left in auto)
  next
    case (fork _ _ _ _ r''')
    have r'_unchanged_left: "s\<^sub>2 r' = s\<^sub>1 r'" using fork assms by auto
    have r'''_fresh_left: "r''' \<notin> RID\<^sub>G s\<^sub>2" using left_step fork(3) only_fork_introduces_rids' s\<^sub>1_r by auto 
    have r_unchanged_right: "s\<^sub>2' r = s\<^sub>1 r" using fork assms by auto
    have r''_unchanged_right: "s\<^sub>2' r'' = s\<^sub>1 r''" using fork assms by auto
    let "?s\<^sub>3" = "s\<^sub>2(r' := s\<^sub>2' r', r''' := s\<^sub>2' r''')"
    let "?s\<^sub>3'" = "s\<^sub>2'(r := s\<^sub>2 r, r'' := None)"
    show ?thesis 
    proof (rule exI[where x="?s\<^sub>3"],rule exI[where x="?s\<^sub>3'"], rule SLC_commute)
      show "?s\<^sub>3 = ?s\<^sub>3'" using fork(1) fork(3) neq r'_not_joined s\<^sub>1_r s\<^sub>2 by (auto simp add: ID_distr_global_conditional)
      show "revision_step r' s\<^sub>2 ?s\<^sub>3" using fork(1-2) r'_unchanged_left r'''_fresh_left by (auto simp add: ID_distr_global_conditional) 
      show "revision_step r s\<^sub>2' ?s\<^sub>3'" using r''_unchanged_right r_unchanged_right s\<^sub>1_r s\<^sub>2 side by auto
    qed
  next
    case (join _ _ _ r''')
    have r'_unchanged_left: "s\<^sub>2 r' = s\<^sub>1 r'" using join(2) neq r'_not_joined s\<^sub>2 by auto
    have r_unchanged_right: "s\<^sub>2' r = s\<^sub>1 r" using join(1,3) neq s\<^sub>1_r by auto
    show ?thesis
    proof (cases "r'' = r'''")
      case True
      have r'''_none_left: "s\<^sub>2 r''' = None" by (simp add: True s\<^sub>2)
      have r''_none_right: "s\<^sub>2' r'' = None" by (simp add: True join(1))
      show ?thesis
      proof (rule exI[where x=\<epsilon>], rule exI[where x=\<epsilon>], rule SLC_commute)
        show "\<epsilon> = \<epsilon>" by (rule refl)
        show "revision_step r' s\<^sub>2 \<epsilon>" using r'_unchanged_left r'''_none_left join(2) by auto
        show "revision_step r s\<^sub>2' \<epsilon>" using r_unchanged_right r''_none_right s\<^sub>1_r by auto
      qed
    next
      case False
      have r'''_unchanged_left: "s\<^sub>2 r''' = s\<^sub>1 r'''" using False join(1,3) s\<^sub>2 r_unchanged_right by auto
      have r''_unchanged_right': "s\<^sub>2' r'' = s\<^sub>1 r''" using False join(1) r'_not_joined side by auto
      let "?s\<^sub>3" = "s\<^sub>2(r' := s\<^sub>2' r', r''' := None)"
      let "?s\<^sub>3'" = "s\<^sub>2'(r := s\<^sub>2 r, r'' := None)"
      show ?thesis
      proof (rule exI[where x="?s\<^sub>3"], rule exI[where x="?s\<^sub>3'"], rule SLC_commute)
        show "?s\<^sub>3 = ?s\<^sub>3'" using join(1) neq r'_not_joined r_unchanged_right s\<^sub>1_r s\<^sub>2 s\<^sub>1_r by fastforce
        show "revision_step r' s\<^sub>2 ?s\<^sub>3" by (simp add: join r'''_unchanged_left r'_unchanged_left)
        show "revision_step r s\<^sub>2' ?s\<^sub>3'" using r''_unchanged_right' r_unchanged_right s\<^sub>1_r side s\<^sub>2 by auto
      qed
    qed
  next
    case join\<^sub>\<epsilon>
    show ?thesis by (rule SLC_sym, rule SLC_join\<^sub>\<epsilon>, use left_step neq right join\<^sub>\<epsilon> in auto)
  qed ((rule join_and_local_commute, use assms r'_not_joined in auto)[1])+
qed

subsubsection \<open>Case local\<close>

lemma local_steps_commute:
  assumes
    "s\<^sub>2 = s\<^sub>1(r \<mapsto> x)"
    "s\<^sub>2' = s\<^sub>1(r' \<mapsto> y)"
    "revision_step r' (s\<^sub>1(r \<mapsto> x)) (s\<^sub>1(r \<mapsto> x, r' \<mapsto> y))"
    "revision_step r (s\<^sub>1(r' \<mapsto> y)) (s\<^sub>1(r' \<mapsto> y, r \<mapsto> x))"
  shows
    "\<exists>s\<^sub>3 s\<^sub>3'. s\<^sub>3 \<approx> s\<^sub>3' \<and> (revision_step r' s\<^sub>2 s\<^sub>3 \<or> s\<^sub>2 = s\<^sub>3) \<and> (revision_step r s\<^sub>2' s\<^sub>3' \<or> s\<^sub>2' = s\<^sub>3')"
  by (metis (no_types, lifting) assms fun_upd_twist fun_upd_upd local_determinism)

lemma local_and_fork_commute:
  assumes
    "s\<^sub>2 = s\<^sub>1(r \<mapsto> x)"
    "s\<^sub>2' = s\<^sub>1(r' \<mapsto> (\<sigma>, \<tau>, \<E> [VE (Rid r'')]), r'' \<mapsto> (\<sigma>;;\<tau>, \<epsilon>, e))"
    "s\<^sub>2 r' = Some (\<sigma>, \<tau>, \<E>[Rfork e])"
    "r'' \<notin> RID\<^sub>G s\<^sub>2"
    "revision_step r s\<^sub>2' (s\<^sub>1(r' \<mapsto> (\<sigma>, \<tau>, \<E> [VE (Rid r'')]), r'' \<mapsto> (\<sigma>;;\<tau>, \<epsilon>, e), r \<mapsto> x))"
    "r \<noteq> r'"
    "r \<noteq> r''"
  shows
    "\<exists>s\<^sub>3 s\<^sub>3'. (s\<^sub>3 \<approx> s\<^sub>3') \<and> (revision_step r' s\<^sub>2 s\<^sub>3 \<or> s\<^sub>2 = s\<^sub>3) \<and> (revision_step r s\<^sub>2' s\<^sub>3' \<or> s\<^sub>2' = s\<^sub>3')"
  proof(rule exI[where x="s\<^sub>1(r \<mapsto> x, r' \<mapsto> (\<sigma>, \<tau>, \<E> [VE (Rid r'')]), r'' \<mapsto> (\<sigma>;;\<tau>, \<epsilon>, e))"],
        rule exI[where x="s\<^sub>1(r' \<mapsto> (\<sigma>, \<tau>, \<E> [VE (Rid r'')]), r'' \<mapsto> (\<sigma>;;\<tau>, \<epsilon>, e), r \<mapsto> x)"],
        rule SLC_commute)
  show "s\<^sub>1(r \<mapsto> x, r' \<mapsto> (\<sigma>, \<tau>, \<E> [VE (Rid r'')]), r'' \<mapsto> (\<sigma>;;\<tau>, \<epsilon>, e)) = 
    s\<^sub>1(r' \<mapsto> (\<sigma>, \<tau>, \<E> [VE (Rid r'')]), r'' \<mapsto> (\<sigma>;;\<tau>, \<epsilon>, e), r \<mapsto> x)"
    using assms revision_step.fork by auto
  show "revision_step r' s\<^sub>2 (s\<^sub>1(r \<mapsto> x, r' \<mapsto> (\<sigma>, \<tau>, \<E> [VE (Rid r'')]), r'' \<mapsto> (\<sigma>;;\<tau>, \<epsilon>, e)))"
    using assms(1) assms(3) assms(4) revision_step.fork by blast
  show "revision_step r s\<^sub>2' (s\<^sub>1(r' \<mapsto> (\<sigma>, \<tau>, \<E> [VE (Rid r'')]), r'' \<mapsto> (\<sigma>;;\<tau>, \<epsilon>, e), r \<mapsto> x))"
    using assms(5) by blast
qed
 
lemma SLC_app:
  assumes
    s\<^sub>1_r: "s\<^sub>1 r = Some (\<sigma>, \<tau>, \<E>[Apply (VE (Lambda x e)) (VE v)])" and
    s\<^sub>2: "s\<^sub>2 = s\<^sub>1(r \<mapsto> (\<sigma>, \<tau>, \<E>[subst (VE v) x e]))" and
    right: "revision_step r' s\<^sub>1 s\<^sub>2'" and
    neq: "r \<noteq> r'"
  shows
    "\<exists>s\<^sub>3 s\<^sub>3'. s\<^sub>3 \<approx> s\<^sub>3' \<and> (revision_step r' s\<^sub>2 s\<^sub>3 \<or> s\<^sub>2 = s\<^sub>3) \<and> (revision_step r s\<^sub>2' s\<^sub>3' \<or> s\<^sub>2' = s\<^sub>3')"
proof -
  have left_step: "revision_step r s\<^sub>1 s\<^sub>2" using s\<^sub>1_r s\<^sub>2 by auto 
  show ?thesis
  proof (use right in \<open>cases rule: revision_stepE\<close>)
    case new: (new _ _ _ _ l)
    have l_fresh_left: "l \<notin> LID\<^sub>G s\<^sub>2"
      by (rule only_new_introduces_lids'[OF left_step]) (simp add: s\<^sub>1_r new(3))+
    show ?thesis by (rule local_steps_commute) (use new l_fresh_left assms in auto)
  next
    case (fork _ _ _ _ r'')
    have r''_fresh_left: "r'' \<notin> RID\<^sub>G s\<^sub>2"
      by (rule only_fork_introduces_rids'[OF left_step]) (simp add: s\<^sub>1_r fork(3))+
    show ?thesis by (rule local_and_fork_commute[OF s\<^sub>2 fork(1)]) (use fork neq s\<^sub>2 r''_fresh_left s\<^sub>1_r in auto)
  next
    case join
    show ?thesis by (rule SLC_sym, rule SLC_join, use join left_step right neq in auto)
  next
    case join\<^sub>\<epsilon>
    show ?thesis by (rule SLC_sym, rule SLC_join\<^sub>\<epsilon>, use join\<^sub>\<epsilon> left_step right neq in auto)
  qed ((rule local_steps_commute[OF s\<^sub>2], use assms in auto)[1])+
qed

lemma SLC_ifTrue:
  assumes
    s\<^sub>1_r: "s\<^sub>1 r = Some (\<sigma>, \<tau>, \<E>[Ite (VE (CV T)) e1 e2])" and
    s\<^sub>2: "s\<^sub>2 = s\<^sub>1(r \<mapsto> (\<sigma>, \<tau>, \<E>[e1]))" and
    right: "revision_step r' s\<^sub>1 s\<^sub>2'" and
    neq: "r \<noteq> r'"
  shows
    "\<exists>s\<^sub>3 s\<^sub>3'. s\<^sub>3 \<approx> s\<^sub>3' \<and> (revision_step r' s\<^sub>2 s\<^sub>3 \<or> s\<^sub>2 = s\<^sub>3) \<and> (revision_step r s\<^sub>2' s\<^sub>3' \<or> s\<^sub>2' = s\<^sub>3')"
proof -
  have left_step: "revision_step r s\<^sub>1 s\<^sub>2" using s\<^sub>1_r s\<^sub>2 by auto
  show ?thesis
  proof (use right in \<open>cases rule: revision_stepE\<close>)
    case (new _ _ _ _ l)
    have l_fresh_left: "l \<notin> LID\<^sub>G s\<^sub>2"
      by (rule only_new_introduces_lids'[OF left_step]) (simp add: s\<^sub>1_r new(3))+
    show ?thesis by (rule local_steps_commute) (use new l_fresh_left assms in auto)
  next
    case (fork _ _ _ _ r'')
    have r''_fresh_left: "r'' \<notin> RID\<^sub>G s\<^sub>2"
      by (rule only_fork_introduces_rids'[OF left_step]) (simp add: s\<^sub>1_r fork(3))+
    show ?thesis by (rule local_and_fork_commute[OF s\<^sub>2 fork(1)]) (use fork neq s\<^sub>2 r''_fresh_left s\<^sub>1_r in auto)
  next
    case join
    show ?thesis by (rule SLC_sym, rule SLC_join, use join left_step right neq in auto)
  next
    case join\<^sub>\<epsilon>
    show ?thesis by (rule SLC_sym, rule SLC_join\<^sub>\<epsilon>, use join\<^sub>\<epsilon> left_step right neq in auto)
  qed ((rule local_steps_commute[OF s\<^sub>2], use assms in auto)[1])+
qed

lemma SLC_ifFalse:
  assumes
    s\<^sub>1_r: "s\<^sub>1 r = Some (\<sigma>, \<tau>, \<E>[Ite (VE (CV F)) e1 e2])" and
    s\<^sub>2: "s\<^sub>2 = s\<^sub>1(r \<mapsto> (\<sigma>, \<tau>, \<E>[e2]))" and
    right: "revision_step r' s\<^sub>1 s\<^sub>2'" and
    neq: "r \<noteq> r'"
  shows
    "\<exists>s\<^sub>3 s\<^sub>3'. s\<^sub>3 \<approx> s\<^sub>3' \<and> (revision_step r' s\<^sub>2 s\<^sub>3 \<or> s\<^sub>2 = s\<^sub>3) \<and> (revision_step r s\<^sub>2' s\<^sub>3' \<or> s\<^sub>2' = s\<^sub>3')"
proof -
  have left_step: "revision_step r s\<^sub>1 s\<^sub>2" using s\<^sub>1_r s\<^sub>2 by auto
  show ?thesis
  proof (use right in \<open>cases rule: revision_stepE\<close>)
  next
    case (new _ _ _ _ l)
    have l_fresh_left: "l \<notin> LID\<^sub>G s\<^sub>2" 
      by (rule only_new_introduces_lids'[OF left_step]) (simp add: s\<^sub>1_r new(3))+
    show ?thesis by (rule local_steps_commute) (use new l_fresh_left assms in auto)
  next
    case (fork _ _ _ _ r'')
    have r''_fresh_left: "r'' \<notin> RID\<^sub>G s\<^sub>2"
      by (rule only_fork_introduces_rids'[OF left_step]) (simp add: s\<^sub>1_r fork(3))+
    show ?thesis by (rule local_and_fork_commute[OF s\<^sub>2 fork(1)]) (use fork neq s\<^sub>2 r''_fresh_left s\<^sub>1_r in auto)
  next
    case join
    show ?thesis by (rule SLC_sym, rule SLC_join, use join left_step right neq in auto)
  next
    case join\<^sub>\<epsilon>
    show ?thesis by (rule SLC_sym, rule SLC_join\<^sub>\<epsilon>, use join\<^sub>\<epsilon> left_step right neq in auto)
  qed ((rule local_steps_commute[OF s\<^sub>2], use assms in auto)[1])+
qed

lemma SLC_set:
  assumes
    s\<^sub>1_r: "s\<^sub>1 r = Some (\<sigma>, \<tau>, \<E>[Assign (VE (Loc l)) (VE v)])" and
    s\<^sub>2: "s\<^sub>2 = s\<^sub>1(r \<mapsto> (\<sigma>, \<tau>(l \<mapsto> v), \<E>[VE (CV Unit)]))" and
    side: "l \<in> dom (\<sigma>;;\<tau>)" and
    right: "revision_step r' s\<^sub>1 s\<^sub>2'" and
    neq: "r \<noteq> r'"
  shows
    "\<exists>s\<^sub>3 s\<^sub>3'. s\<^sub>3 \<approx> s\<^sub>3' \<and> (revision_step r' s\<^sub>2 s\<^sub>3 \<or> s\<^sub>2 = s\<^sub>3) \<and> (revision_step r s\<^sub>2' s\<^sub>3' \<or> s\<^sub>2' = s\<^sub>3')"
proof -
  have left_step: "revision_step r s\<^sub>1 s\<^sub>2" using s\<^sub>1_r s\<^sub>2 side by auto
  show ?thesis
  proof (use right in \<open>cases rule: revision_stepE\<close>)
    case (new _ _ _ _ l)
    have l_fresh_left: "l \<notin> LID\<^sub>G s\<^sub>2"
      by (rule only_new_introduces_lids'[OF left_step]) (simp add: s\<^sub>1_r new(3))+
    show ?thesis by (rule local_steps_commute) (use new l_fresh_left assms in auto)
  next
    case (fork _ _ _ _ r'')
    have r''_fresh_left: "r'' \<notin> RID\<^sub>G s\<^sub>2"
      by (rule only_fork_introduces_rids'[OF left_step]) (simp add: s\<^sub>1_r fork(3))+
    show ?thesis by (rule local_and_fork_commute[OF s\<^sub>2 fork(1)]) (use fork neq s\<^sub>2 r''_fresh_left s\<^sub>1_r side in auto)
  next
    case join
    show ?thesis by (rule SLC_sym, rule SLC_join, use join left_step neq in auto)
  next
    case join\<^sub>\<epsilon>
    show ?thesis by (rule SLC_sym, rule SLC_join\<^sub>\<epsilon>, use join\<^sub>\<epsilon> left_step neq in auto)
  qed ((rule local_steps_commute[OF s\<^sub>2], use assms in auto)[1])+
qed

lemma SLC_get:
  assumes
    s\<^sub>1_r: "s\<^sub>1 r = Some (\<sigma>, \<tau>, \<E> [Read (VE (Loc l))])" and
    s\<^sub>2: "s\<^sub>2 = s\<^sub>1(r \<mapsto> (\<sigma>, \<tau>, \<E>[VE (the ((\<sigma>;;\<tau>) l))]))" and
    side: "l \<in> dom (\<sigma>;;\<tau>)" and
    right: "revision_step r' s\<^sub>1 s\<^sub>2'" and
    neq: "r \<noteq> r'"
  shows
    "\<exists>s\<^sub>3 s\<^sub>3'. s\<^sub>3 \<approx> s\<^sub>3' \<and> (revision_step r' s\<^sub>2 s\<^sub>3 \<or> s\<^sub>2 = s\<^sub>3) \<and> (revision_step r s\<^sub>2' s\<^sub>3' \<or> s\<^sub>2' = s\<^sub>3')"
proof -
  have left_step: "revision_step r s\<^sub>1 s\<^sub>2" using s\<^sub>1_r s\<^sub>2 side by auto
  show ?thesis
  proof (use right in \<open>cases rule: revision_stepE\<close>)
    case (new _ _ _ _ l)
    have l_fresh_left: "l \<notin> LID\<^sub>G s\<^sub>2"
      by (rule only_new_introduces_lids'[OF left_step]) (simp add: s\<^sub>1_r new(3))+
    show ?thesis by (rule local_steps_commute) (use new l_fresh_left assms in auto)
  next
    case (fork _ _ _ _ r'')
    have r''_fresh_left: "r'' \<notin> RID\<^sub>G s\<^sub>2"
      by (rule only_fork_introduces_rids'[OF left_step]) (simp add: s\<^sub>1_r fork(3))+
    show ?thesis by (rule local_and_fork_commute[OF s\<^sub>2 fork(1)]) (use fork neq s\<^sub>2 r''_fresh_left s\<^sub>1_r side in auto)
  next
    case join
    show ?thesis by (rule SLC_sym, rule SLC_join, use join left_step neq in auto)
  next
    case join\<^sub>\<epsilon>
    show ?thesis by (rule SLC_sym, rule SLC_join\<^sub>\<epsilon>, use join\<^sub>\<epsilon> left_step neq in auto)
  qed ((rule local_steps_commute[OF s\<^sub>2], use assms in auto)[1])+
qed

subsubsection \<open>Case new\<close>

lemma SLC_new:
  assumes
    s\<^sub>1_r: "s\<^sub>1 r = Some (\<sigma>, \<tau>, \<E>[Ref (VE v)])" and
    s\<^sub>2: "s\<^sub>2 = s\<^sub>1(r \<mapsto> (\<sigma>, \<tau>(l \<mapsto> v), \<E> [VE (Loc l)]))" and
    side: "l \<notin> LID\<^sub>G s\<^sub>1" and
    right: "revision_step r' s\<^sub>1 s\<^sub>2'" and
    neq: "r \<noteq> r'" and
    reach: "reachable (s\<^sub>1 :: ('r,'l,'v) global_state)" and
    lid_inf: "infinite (UNIV :: 'l set)"
  shows
    "\<exists>s\<^sub>3 s\<^sub>3'. s\<^sub>3 \<approx> s\<^sub>3' \<and> (revision_step r' s\<^sub>2 s\<^sub>3 \<or> s\<^sub>2 = s\<^sub>3) \<and> (revision_step r s\<^sub>2' s\<^sub>3' \<or> s\<^sub>2' = s\<^sub>3')"
proof -
  have left_step: "revision_step r s\<^sub>1 s\<^sub>2" using s\<^sub>1_r s\<^sub>2 side by auto
  show ?thesis
  proof (use right in \<open>cases rule: revision_stepE\<close>)
    case app
    show ?thesis by (rule SLC_sym, rule SLC_app) (use app assms(1-5) in auto)
  next
    case ifTrue
    show ?thesis by (rule SLC_sym, rule SLC_ifTrue) (use ifTrue assms(1-5) in auto)
  next
    case ifFalse
    show ?thesis by (rule SLC_sym, rule SLC_ifFalse) (use ifFalse assms(1-5) in auto)
  next
    case (new \<sigma>' \<tau>' \<E>' v' l')
    have r'_unchanged_left: "s\<^sub>2 r' = s\<^sub>1 r'" using new(2) neq s\<^sub>2 by auto
    have r_unchanged_right: "s\<^sub>2' r = s\<^sub>1 r" by (simp add: new(1) neq s\<^sub>1_r)
    show ?thesis
    proof (cases "l = l'")
      case True
      obtain l'' where l''_fresh_left: "l'' \<notin> LID\<^sub>G s\<^sub>2"
        by (meson ex_new_if_finite left_step lid_inf reach RID\<^sub>L_finite_invariant reachable_imp_identifiers_finite(2))
      hence l_l'': "l \<noteq> l''" by (auto simp add: s\<^sub>2)
      have l''_fresh_s\<^sub>1: "l'' \<notin> LID\<^sub>G s\<^sub>1" using assms True new l''_fresh_left by (auto simp add: ID_distr_global_conditional)
      hence l''_fresh_right': "l'' \<notin> LID\<^sub>G s\<^sub>2'" using True l_l'' new(1-2) by auto
      let "?\<beta>" = "id(l := l'', l'' := l)" 
      have bij_\<beta>: "bij ?\<beta>" by (simp add: swap_bij)
      let "?s\<^sub>3" = "s\<^sub>2(r' \<mapsto> (\<sigma>', \<tau>'(l'' \<mapsto> v'), \<E>' [VE (Loc l'')]))"
      have left_convergence: "revision_step r' s\<^sub>2 ?s\<^sub>3"
        using l''_fresh_left new(2) r'_unchanged_left by auto
      let "?s\<^sub>3'" = "s\<^sub>2'(r \<mapsto> (\<sigma>, \<tau>(l'' \<mapsto> v), \<E> [VE (Loc l'')]))"
      have right_convergence: "revision_step r s\<^sub>2' ?s\<^sub>3'"
        using l''_fresh_right' new(1) neq s\<^sub>1_r by auto 
      have equiv: "?s\<^sub>3 \<approx> ?s\<^sub>3'"
      proof (rule eq_statesI[of id ?\<beta>])
        show "\<R>\<^sub>G id ?\<beta> ?s\<^sub>3 = ?s\<^sub>3'"
        proof -
          have s\<^sub>1: "\<R>\<^sub>G id ?\<beta> s\<^sub>1 = s\<^sub>1" using l''_fresh_s\<^sub>1 side by auto
          have \<sigma>: "\<R>\<^sub>S id ?\<beta> \<sigma> = \<sigma>" using l''_fresh_s\<^sub>1 s\<^sub>1_r side by auto
          have \<E>: "\<R>\<^sub>C id ?\<beta> \<E> = \<E>"
          proof
            show "l \<notin> LID\<^sub>C \<E>" using s\<^sub>1_r side by auto
            show "l'' \<notin> LID\<^sub>C \<E>" using l''_fresh_left s\<^sub>2 by auto
          qed
          have \<tau>lv: "\<R>\<^sub>S id (id(l := l'', l'' := l)) (\<tau>(l \<mapsto> v)) = (\<tau>(l'' \<mapsto> v))"
          proof -
            have \<tau>: "\<R>\<^sub>S id ?\<beta> \<tau> = \<tau>" using l''_fresh_s\<^sub>1 s\<^sub>1_r side by auto
            have v: "\<R>\<^sub>V id ?\<beta> v = v"
            proof
              show "l \<notin> LID\<^sub>V v" using s\<^sub>1_r side by auto
              show "l'' \<notin> LID\<^sub>V v" using l''_fresh_s\<^sub>1 s\<^sub>1_r by auto
            qed
            show ?thesis by (simp add: \<tau> v bij_\<beta>)
          qed
          have \<sigma>': "\<R>\<^sub>S id ?\<beta> \<sigma>' = \<sigma>'" using l''_fresh_s\<^sub>1 new(2-3) by (auto simp add: True ID_distr_global_conditional)
          have \<E>': "\<R>\<^sub>C id ?\<beta> \<E>' = \<E>'" using l''_fresh_s\<^sub>1 new(2-3) by (auto simp add: True ID_distr_global_conditional)
          have \<tau>l''v: "\<R>\<^sub>S id (id(l := l'', l'' := l)) (\<tau>'(l'' \<mapsto> v')) = (\<tau>'(l \<mapsto> v'))"
          proof -
            have \<tau>': "\<R>\<^sub>S id ?\<beta> \<tau>' = \<tau>'" using new(2-3) l''_fresh_s\<^sub>1 by (auto simp add: True ID_distr_global_conditional)
            have v': "\<R>\<^sub>V id ?\<beta> v' = v'" using new(2-3) l''_fresh_s\<^sub>1 by (auto simp add: True ID_distr_global_conditional)
            show ?thesis by (simp add: \<tau>' v' bij_\<beta>)
          qed
          show ?thesis using True neq s\<^sub>1 \<sigma> \<E> \<tau>lv \<sigma>' \<E>' \<tau>l''v s\<^sub>2 l_l'' new(1) by auto
        qed
      qed (simp add: bij_\<beta>)+
      show ?thesis using left_convergence right_convergence equiv by blast
    next
      case False
      have l_fresh_left: "l \<notin> LID\<^sub>G s\<^sub>2'" 
        by (rule revision_stepE[OF left_step]) (use False side new(1-2) in \<open>auto simp add: s\<^sub>1_r\<close>)
      have l'_fresh_right: "l' \<notin> LID\<^sub>G s\<^sub>2" 
        by (rule revision_stepE[OF right]) (use False new(3) assms(1-3) in \<open>auto simp add: new(2)\<close>)
      show ?thesis by (rule local_steps_commute[OF s\<^sub>2 new(1)]) (use new assms l_fresh_left l'_fresh_right s\<^sub>2 in auto)
    qed
  next
    case get
    show ?thesis by (rule SLC_sym, rule SLC_get) (use get assms(1-5) in auto)
  next
    case set
    show ?thesis by (rule SLC_sym, rule SLC_set) (use set assms(1-5) in auto)
  next
    case (fork _ _ _ _ r'')
    have r''_fresh_left: "r'' \<notin> RID\<^sub>G s\<^sub>2" 
      by (rule only_fork_introduces_rids'[OF left_step]) (simp add: s\<^sub>1_r fork(3))+
    have l_fresh_right: "l \<notin> LID\<^sub>G s\<^sub>2'" 
      by (rule only_new_introduces_lids'[OF right]) (simp add: side fork(2))+
    show ?thesis by (rule local_and_fork_commute[OF s\<^sub>2 fork(1)]) (use fork(1-2) neq s\<^sub>2 l_fresh_right r''_fresh_left s\<^sub>1_r in auto)
  next
    case join
    show ?thesis by (rule SLC_sym, rule SLC_join, use join left_step neq in auto)
  next
    case join\<^sub>\<epsilon>
    show ?thesis by (rule SLC_sym, rule SLC_join\<^sub>\<epsilon>, use join\<^sub>\<epsilon> left_step neq in auto)
  qed
qed

subsubsection \<open>Case fork\<close>

lemma SLC_fork:
  assumes
    s\<^sub>1_r: "s\<^sub>1 r = Some (\<sigma>, \<tau>, \<E> [Rfork e])" and
    s\<^sub>2: "s\<^sub>2 = (s\<^sub>1(r \<mapsto> (\<sigma>, \<tau>, \<E>[VE (Rid left_forkee)]), left_forkee \<mapsto> (\<sigma>;;\<tau>, \<epsilon>, e)))" and
    side: "left_forkee \<notin> RID\<^sub>G s\<^sub>1" and
    right: "revision_step r' s\<^sub>1 s\<^sub>2'" and
    neq: "r \<noteq> r'" and
    reach: "reachable (s\<^sub>1 :: ('r,'l,'v) global_state)" and
    rid_inf: "infinite (UNIV :: 'r set)"
  shows
    "\<exists>s\<^sub>3 s\<^sub>3'. s\<^sub>3 \<approx> s\<^sub>3' \<and> (revision_step r' s\<^sub>2 s\<^sub>3 \<or> s\<^sub>2 = s\<^sub>3) \<and> (revision_step r s\<^sub>2' s\<^sub>3' \<or> s\<^sub>2' = s\<^sub>3')"
proof -
  have left_step: "revision_step r s\<^sub>1 s\<^sub>2" using s\<^sub>1_r s\<^sub>2 side by (auto simp add: ID_distr_global_conditional)
  show ?thesis
  proof (use right in \<open>cases rule: revision_stepE\<close>)
    case app
    show ?thesis by (rule SLC_sym, rule SLC_app) (use assms(1-5) app in \<open>auto simp add: ID_distr_global_conditional\<close>)
  next
    case ifTrue
    show ?thesis by (rule SLC_sym, rule SLC_ifTrue) (use assms(1-5) ifTrue in \<open>auto simp add: ID_distr_global_conditional\<close>)
  next
    case ifFalse
    show ?thesis by (rule SLC_sym, rule SLC_ifFalse) (use assms(1-5) ifFalse in \<open>auto simp add: ID_distr_global_conditional\<close>)
  next
    case (new _ _ _ _ l) (* symmetry is intentionally not exploited: this would require the lid_inf assumption *)
    have l_fresh_left: "l \<notin> LID\<^sub>G s\<^sub>2"
      by (rule only_new_introduces_lids'[OF left_step]) (simp add: s\<^sub>1_r new(3))+
    have r''_fresh_right: "left_forkee \<notin> RID\<^sub>G s\<^sub>2'"
      by (rule only_fork_introduces_rids'[OF right]) (simp add: side new(2))+
    show ?thesis by (rule SLC_sym, rule local_and_fork_commute[OF new(1) s\<^sub>2]) (use new(1-2) neq s\<^sub>1_r r''_fresh_right l_fresh_left s\<^sub>2 in auto)
  next
    case get
    show ?thesis by (rule SLC_sym, rule SLC_get) (use assms(1-5) get in \<open>auto simp add: ID_distr_global_conditional\<close>)
  next
    case set
    show ?thesis by (rule SLC_sym, rule SLC_set) (use assms(1-5) set in \<open>auto simp add: ID_distr_global_conditional\<close>)
  next
    case (fork \<sigma>' \<tau>' \<E>' e' right_forkee)
    have r'_unchanged_left: "s\<^sub>2 r' = s\<^sub>1 r'" using side fork(2) neq s\<^sub>2 by auto
    have r_unchanged_right: "s\<^sub>2' r = s\<^sub>1 r" using fork(1,3) neq s\<^sub>1_r by auto
    have "r \<noteq> left_forkee" using s\<^sub>1_r side by auto
    have "r \<noteq> right_forkee" using fork(3) s\<^sub>1_r by auto
    have "r' \<noteq> left_forkee" using fork(2) side by auto
    have "r' \<noteq> right_forkee" using fork(2) fork(3) by auto
    show ?thesis
    proof (cases "left_forkee = right_forkee")
      case True
      obtain r'' where r''_fresh_left: "r'' \<notin> RID\<^sub>G s\<^sub>2"
        using RID\<^sub>G_finite_invariant ex_new_if_finite left_step reach reachable_imp_identifiers_finite(1) rid_inf by blast
      hence "r'' \<noteq> left_forkee" using assms(2) by auto
      have "r'' \<noteq> r" using r''_fresh_left s\<^sub>2 by auto
      have "r'' \<noteq> r'" using fork(2) r''_fresh_left r'_unchanged_left by auto
      have "r'' \<notin> RID\<^sub>G (s\<^sub>1(r \<mapsto> (\<sigma>, \<tau>, \<E>[VE (Rid left_forkee)])))"
        by (metis (mono_tags, lifting) RID\<^sub>G_def True UnI1 \<open>r \<noteq> right_forkee\<close> domIff fun_upd_other fun_upd_triv in_restricted_global_in_updated_global(1) fork(3) r''_fresh_left s\<^sub>2)
      hence "r'' \<notin> RID\<^sub>G (s\<^sub>1(r := None))" by blast
      have r''_fresh_s\<^sub>1: "r'' \<notin> RID\<^sub>G s\<^sub>1" 
        using \<open>r \<noteq> left_forkee\<close> s\<^sub>2 r''_fresh_left s\<^sub>1_r \<open>r'' \<noteq> r\<close> \<open>r'' \<notin> RID\<^sub>G (s\<^sub>1(r := None))\<close>
        by (auto simp add: ID_distr_global_conditional)
      have r''_fresh_right: "r'' \<notin> RID\<^sub>G s\<^sub>2'"
        using True \<open>r'' \<noteq> left_forkee\<close> \<open>r' \<noteq> right_forkee\<close> \<open>r'' \<noteq> r'\<close> r''_fresh_s\<^sub>1 fork(2) r''_fresh_s\<^sub>1 
        by (auto simp add: fork(1) ID_distr_global_conditional fun_upd_twist)
      let ?\<alpha> = "id(left_forkee := r'', r'' := left_forkee)"
      have bij_\<alpha>: "bij ?\<alpha>" by (simp add: swap_bij)
      let "?s\<^sub>3" = "s\<^sub>2(r' \<mapsto> (\<sigma>', \<tau>', \<E>' [VE (Rid r'')]), r'' \<mapsto> (\<sigma>';;\<tau>', \<epsilon>, e'))"
      have left_convergence: "revision_step r' s\<^sub>2 ?s\<^sub>3"
        using fork(2) r''_fresh_left r'_unchanged_left revision_step.fork by auto
      let "?s\<^sub>3'" = "s\<^sub>2'(r \<mapsto> (\<sigma>, \<tau>, \<E>[VE (Rid r'')]), r'' \<mapsto> (\<sigma>;;\<tau>, \<epsilon>, e))"
      have right_convergence: "revision_step r s\<^sub>2' ?s\<^sub>3'"
        using r''_fresh_right r_unchanged_right revision_step.fork s\<^sub>1_r by auto
      have equiv: "?s\<^sub>3 \<approx> ?s\<^sub>3'"
      proof (rule eq_statesI[of ?\<alpha> id])
        show "\<R>\<^sub>G ?\<alpha> id ?s\<^sub>3 = ?s\<^sub>3'"
        proof -
          have s\<^sub>1: "\<R>\<^sub>G ?\<alpha> id s\<^sub>1 = s\<^sub>1" using r''_fresh_s\<^sub>1 side by auto
          have \<sigma>: "\<R>\<^sub>S ?\<alpha> id \<sigma> = \<sigma>" using r''_fresh_s\<^sub>1 s\<^sub>1_r True fork(3) by auto
          have \<tau>: "\<R>\<^sub>S ?\<alpha> id \<tau> = \<tau>" using r''_fresh_s\<^sub>1 s\<^sub>1_r True fork(3) by auto
          have \<E>: "\<R>\<^sub>C ?\<alpha> id \<E> = \<E>"
          proof
            show "left_forkee \<notin> RID\<^sub>C \<E>" using s\<^sub>1_r side by auto
            show "r'' \<notin> RID\<^sub>C \<E>" using True \<open>r \<noteq> right_forkee\<close> r''_fresh_left s\<^sub>2 by auto
          qed
          have e: "\<R>\<^sub>E ?\<alpha> id e = e"
          proof
            show "left_forkee \<notin> RID\<^sub>E e" using s\<^sub>1_r side by auto
            show "r'' \<notin> RID\<^sub>E e" using True \<open>r \<noteq> right_forkee\<close> r''_fresh_left s\<^sub>2 by auto
          qed
          have \<sigma>': "\<R>\<^sub>S ?\<alpha> id \<sigma>' = \<sigma>'" using fork(2) r''_fresh_s\<^sub>1 side by auto
          have \<tau>': "\<R>\<^sub>S ?\<alpha> id \<tau>' = \<tau>'" using fork(2) r''_fresh_s\<^sub>1 side by auto
          have \<E>': "\<R>\<^sub>C ?\<alpha> id \<E>' = \<E>'"
          proof 
            show "left_forkee \<notin> RID\<^sub>C \<E>'" using fork(2) side by auto
            show "r'' \<notin> RID\<^sub>C \<E>'" using fork(2) r''_fresh_s\<^sub>1 by auto
          qed
          have e': "\<R>\<^sub>E ?\<alpha> id e' = e'"
          proof 
            show "left_forkee \<notin> RID\<^sub>E e'" using fork(2) side by auto
            show "r'' \<notin> RID\<^sub>E e'" using fork(2) r''_fresh_s\<^sub>1 by auto
          qed
          show ?thesis using True fork(1) neq \<sigma> \<tau> \<E> e  \<sigma>' \<tau>' \<E>' e' s\<^sub>1 s\<^sub>2
            bij_\<alpha> \<open>r'' \<noteq> left_forkee\<close> \<open>r' \<noteq> left_forkee\<close> \<open>r \<noteq> left_forkee\<close> \<open>r'' \<noteq> r\<close> \<open>r'' \<noteq> r'\<close> 
            by auto
        qed
      qed (simp add: bij_\<alpha>)+
      show ?thesis using equiv left_convergence right_convergence by blast
    next
      case False
      have right_forkee_fresh_left: "right_forkee \<notin> RID\<^sub>G s\<^sub>2" 
        using False \<open>r \<noteq> left_forkee\<close> \<open>r \<noteq> right_forkee\<close> fork(3) s\<^sub>1_r 
        by (auto simp add: s\<^sub>2 ID_distr_global_conditional, auto)
      have left_forkee_fresh_right: "left_forkee \<notin> RID\<^sub>G s\<^sub>2'" 
        using False \<open>r' \<noteq> right_forkee\<close> \<open>r' \<noteq> left_forkee\<close> side fork(2)
        by (auto simp add: fork(1) ID_distr_global_conditional fun_upd_twist)
      show ?thesis 
      proof(rule exI[where x="s\<^sub>2(r' := s\<^sub>2' r', right_forkee := s\<^sub>2' right_forkee)"],
            rule exI[where x="s\<^sub>2'(r := s\<^sub>2 r, left_forkee := s\<^sub>2 left_forkee)"],
            rule SLC_commute)
        show "s\<^sub>2(r' := s\<^sub>2' r', right_forkee := s\<^sub>2' right_forkee) = s\<^sub>2'(r := s\<^sub>2 r, left_forkee := s\<^sub>2 left_forkee)"
          using False \<open>r \<noteq> right_forkee\<close> \<open>r' \<noteq> left_forkee\<close> \<open>r' \<noteq> right_forkee\<close> fork(1) neq s\<^sub>2 by auto
        show "revision_step r' s\<^sub>2 (s\<^sub>2(r' := s\<^sub>2' r', right_forkee := s\<^sub>2' right_forkee))"
          using fork(1-2) r'_unchanged_left revision_step.fork right_forkee_fresh_left by auto
        show "revision_step r s\<^sub>2' (s\<^sub>2'(r := s\<^sub>2 r, left_forkee := s\<^sub>2 left_forkee))"
          using left_forkee_fresh_right r_unchanged_right revision_step.fork s\<^sub>1_r s\<^sub>2 by auto
      qed
    qed
  next
    case join
    show ?thesis by (rule SLC_sym, rule SLC_join, use join left_step assms(3-5) in auto)
  next
    case join\<^sub>\<epsilon>
    show ?thesis by (rule SLC_sym, rule SLC_join\<^sub>\<epsilon>, use join\<^sub>\<epsilon> left_step assms(3-5) in auto)
  qed
qed

subsubsection \<open>The theorem\<close>

theorem strong_local_confluence:
  assumes 
    l: "revision_step r s\<^sub>1 s\<^sub>2" and
    r: "revision_step r' s\<^sub>1 s\<^sub>2'" and
    reach: "reachable (s\<^sub>1 :: ('r,'l,'v) global_state)" and
    lid_inf: "infinite (UNIV :: 'l set)" and
    rid_inf: "infinite (UNIV :: 'r set)"
  shows
    "\<exists>s\<^sub>3 s\<^sub>3'. s\<^sub>3 \<approx> s\<^sub>3' \<and> (revision_step r' s\<^sub>2 s\<^sub>3 \<or> s\<^sub>2 = s\<^sub>3) \<and> (revision_step r s\<^sub>2' s\<^sub>3' \<or> s\<^sub>2' = s\<^sub>3')"
proof (cases "r = r'")
  case True
  thus ?thesis by (metis l local_determinism r)
next
  case neq: False
  thus ?thesis by (cases rule: revision_stepE[OF l]) (auto simp add: assms SLC_app SLC_ifTrue
    SLC_ifFalse SLC_new SLC_get SLC_set SLC_fork SLC_join SLC_join\<^sub>\<epsilon>)
qed

subsection \<open>Diagram Tiling\<close>

subsubsection \<open>Strong local confluence diagrams\<close>

lemma SLC:
  assumes
    s\<^sub>1s\<^sub>2: "s\<^sub>1 \<leadsto> s\<^sub>2" and
    s\<^sub>1s\<^sub>2': "s\<^sub>1 \<leadsto> s\<^sub>2'" and
    reach: "reachable (s\<^sub>1 :: ('r,'l,'v) global_state)" and
    lid_inf: "infinite (UNIV :: 'l set)" and
    rid_inf: "infinite (UNIV :: 'r set)"
  shows
    "\<exists>s\<^sub>3 s\<^sub>3'. s\<^sub>3 \<approx> s\<^sub>3' \<and> s\<^sub>2 \<leadsto>\<^sup>= s\<^sub>3 \<and> s\<^sub>2' \<leadsto>\<^sup>= s\<^sub>3'"
proof -
  from s\<^sub>1s\<^sub>2 obtain r where l: "revision_step r s\<^sub>1 s\<^sub>2" by auto
  from s\<^sub>1s\<^sub>2' obtain r' where r: "revision_step r' s\<^sub>1 s\<^sub>2'" by auto
  obtain s\<^sub>3 s\<^sub>3' where 
    s\<^sub>3_eq_s\<^sub>3': "s\<^sub>3 \<approx> s\<^sub>3'" and
    l_join: "revision_step r' s\<^sub>2 s\<^sub>3 \<or> s\<^sub>2 = s\<^sub>3" and
    r_join: "revision_step r s\<^sub>2' s\<^sub>3' \<or> s\<^sub>2' = s\<^sub>3'"
    using l r reach lid_inf rid_inf strong_local_confluence by metis
  have s\<^sub>2s\<^sub>3: "s\<^sub>2 \<leadsto>\<^sup>= s\<^sub>3" using l_join steps_def by auto
  have s\<^sub>2's\<^sub>3: "s\<^sub>2' \<leadsto>\<^sup>= s\<^sub>3'" using r_join steps_def by auto
  show ?thesis using s\<^sub>2's\<^sub>3 s\<^sub>2s\<^sub>3 s\<^sub>3_eq_s\<^sub>3' by blast
qed

lemma SLC_top_relaxed:
  assumes
    s\<^sub>1s\<^sub>2: "s\<^sub>1 \<leadsto>\<^sup>= s\<^sub>2" and
    s\<^sub>1s\<^sub>2': "s\<^sub>1 \<leadsto> s\<^sub>2'" and
    reach: "reachable (s\<^sub>1 :: ('r,'l,'v) global_state)" and
    lid_inf: "infinite (UNIV :: 'l set)" and
    rid_inf: "infinite (UNIV :: 'r set)"
  shows
    "\<exists>s\<^sub>3 s\<^sub>3'. s\<^sub>3 \<approx> s\<^sub>3' \<and> s\<^sub>2 \<leadsto>\<^sup>= s\<^sub>3 \<and> s\<^sub>2' \<leadsto>\<^sup>= s\<^sub>3'"
proof -
  have 1: "s\<^sub>1 \<leadsto> s\<^sub>2 \<Longrightarrow> s\<^sub>1 \<leadsto> s\<^sub>2' \<Longrightarrow> ?thesis" using SLC lid_inf reach rid_inf by blast
  have 2: "s\<^sub>1 = s\<^sub>2 \<Longrightarrow> s\<^sub>1 \<leadsto> s\<^sub>2' \<Longrightarrow> ?thesis" 
    by (rule exI[where x="s\<^sub>2'"], rule exI[where x="s\<^sub>2'"]) (auto simp add: \<alpha>\<beta>_refl)
  show ?thesis using assms 1 2 by auto
qed

subsubsection \<open>Mimicking diagrams\<close>

declare bind_eq_None_conv [simp]
declare bind_eq_Some_conv [simp]

lemma in_renamed_in_unlabelled_val: 
  "bij \<alpha> \<Longrightarrow> (\<alpha> r \<in> RID\<^sub>V (\<R>\<^sub>V \<alpha> \<beta> v)) = (r \<in> RID\<^sub>V v)"
  "bij \<beta> \<Longrightarrow> (\<beta> l \<in> LID\<^sub>V (\<R>\<^sub>V \<alpha> \<beta> v)) = (l \<in> LID\<^sub>V v)"
  by (auto simp add: bij_is_inj inj_image_mem_iff val.set_map(1-2))

lemma in_renamed_in_unlabelled_expr:
  "bij \<alpha> \<Longrightarrow> (\<alpha> r \<in> RID\<^sub>E (\<R>\<^sub>E \<alpha> \<beta> v)) = (r \<in> RID\<^sub>E v)"
  "bij \<beta> \<Longrightarrow> (\<beta> l \<in> LID\<^sub>E (\<R>\<^sub>E \<alpha> \<beta> v)) = (l \<in> LID\<^sub>E v)"
  by (auto simp add: bij_is_inj inj_image_mem_iff expr.set_map(1-2))

lemma in_renamed_in_unlabelled_store:
  assumes 
    bij_\<alpha>: "bij \<alpha>" and
    bij_\<beta>: "bij \<beta>"
  shows
    "(\<alpha> r \<in> RID\<^sub>S (\<R>\<^sub>S \<alpha> \<beta> \<sigma>)) = (r \<in> RID\<^sub>S \<sigma>)"
    "(\<beta> l \<in> LID\<^sub>S (\<R>\<^sub>S \<alpha> \<beta> \<sigma>)) = (l \<in> LID\<^sub>S \<sigma>)"
proof -
  show "(\<alpha> r \<in> RID\<^sub>S (\<R>\<^sub>S \<alpha> \<beta> \<sigma>)) = (r \<in> RID\<^sub>S \<sigma>)"
  proof (rule iffI)
    assume "\<alpha> r \<in> RID\<^sub>S (\<R>\<^sub>S \<alpha> \<beta> \<sigma>)"
    thus "r \<in> RID\<^sub>S \<sigma>"
    proof (rule RID\<^sub>SE)
      fix l v
      assume map: "\<R>\<^sub>S \<alpha> \<beta> \<sigma> l = Some v" and \<alpha>r: "\<alpha> r \<in> RID\<^sub>V v" 
      hence "\<sigma> (inv \<beta> l) = Some (\<R>\<^sub>V (inv \<alpha>) (inv \<beta>) v)"
        using bij_\<alpha> bij_\<beta> by (auto simp add: bij_is_inj)
      have "r \<in> RID\<^sub>V (\<R>\<^sub>V (inv \<alpha>) (inv \<beta>) v)"
        using bij_\<alpha> bij_\<beta> \<alpha>r map by (auto simp add: bij_is_inj in_renamed_in_unlabelled_val(1))
      show "r \<in> RID\<^sub>S \<sigma>"
        using \<open>\<sigma> (inv \<beta> l) = Some (\<R>\<^sub>V (inv \<alpha>) (inv \<beta>) v)\<close> \<open>r \<in> RID\<^sub>V (\<R>\<^sub>V (inv \<alpha>) (inv \<beta>) v)\<close> by blast
    qed
  next
    assume "r \<in> RID\<^sub>S \<sigma>"
    thus "\<alpha> r \<in> RID\<^sub>S (\<R>\<^sub>S \<alpha> \<beta> \<sigma>)" 
      by (metis (mono_tags, lifting) RID\<^sub>SE RID\<^sub>SI bij_\<alpha> bij_\<beta> fun_upd_same fun_upd_triv 
      in_renamed_in_unlabelled_val(1) renaming_distr_store)
  qed
  show "(\<beta> l \<in> LID\<^sub>S (\<R>\<^sub>S \<alpha> \<beta> \<sigma>)) = (l \<in> LID\<^sub>S \<sigma>)"
  proof (rule iffI)
    assume "\<beta> l \<in> LID\<^sub>S (\<R>\<^sub>S \<alpha> \<beta> \<sigma>)"
    thus "l \<in> LID\<^sub>S \<sigma>"
    proof (rule LID\<^sub>SE)
      assume "\<beta> l \<in> dom (\<R>\<^sub>S \<alpha> \<beta> \<sigma>)"
      thus "l \<in> LID\<^sub>S \<sigma>" by (auto simp add: LID\<^sub>SI(1) bij_\<beta> bijection.intro bijection.inv_left)
    next
      fix v l'
      assume "\<R>\<^sub>S \<alpha> \<beta> \<sigma> l' = Some v" "\<beta> l \<in> LID\<^sub>V v"
      thus "l \<in> LID\<^sub>S \<sigma>" using bij_\<beta> by (auto simp add: LID\<^sub>SI(2) in_renamed_in_unlabelled_val(2))
    qed
  next
    assume "l \<in> LID\<^sub>S \<sigma>" 
    thus "\<beta> l \<in> LID\<^sub>S (\<R>\<^sub>S \<alpha> \<beta> \<sigma>)"
    proof (rule LID\<^sub>SE)
      assume "l \<in> dom \<sigma>"
      hence "\<exists>\<sigma>' v. \<sigma> = (\<sigma>'(l \<mapsto> v))" by fastforce
      hence "\<beta> l \<in> dom (\<R>\<^sub>S \<alpha> \<beta> \<sigma>)" using bij_\<beta> by auto
      thus "\<beta> l \<in> LID\<^sub>S (\<R>\<^sub>S \<alpha> \<beta> \<sigma>)" by auto
    next
      fix v l'
      assume "\<sigma> l' = Some v" and l_in_v: "l \<in> LID\<^sub>V v"
      hence "\<exists>\<sigma>'. \<sigma> = (\<sigma>'(l' \<mapsto> v))" by force
      thus "\<beta> l \<in> LID\<^sub>S (\<R>\<^sub>S \<alpha> \<beta> \<sigma>)" 
        using l_in_v bij_\<beta> by (auto simp add: LID\<^sub>SI(2) in_renamed_in_unlabelled_val(2))
    qed
  qed
qed

lemma in_renamed_in_unlabelled_local:
  assumes
    bij_\<alpha>: "bij \<alpha>" and
    bij_\<beta>: "bij \<beta>"
  shows
    "(\<alpha> r \<in> RID\<^sub>L (\<R>\<^sub>L \<alpha> \<beta> ls)) = (r \<in> RID\<^sub>L ls)"
    "(\<beta> l \<in> LID\<^sub>L (\<R>\<^sub>L \<alpha> \<beta> ls)) = (l \<in> LID\<^sub>L ls)"
  by (cases ls, simp add: assms in_renamed_in_unlabelled_expr in_renamed_in_unlabelled_store)+

lemma in_renamed_in_unlabelled_global:
  assumes
    bij_\<alpha>: "bij \<alpha>" and
    bij_\<beta>: "bij \<beta>"
  shows
    "(\<alpha> r \<in> RID\<^sub>G (\<R>\<^sub>G \<alpha> \<beta> s)) = (r \<in> RID\<^sub>G s)"
    "(\<beta> l \<in> LID\<^sub>G (\<R>\<^sub>G \<alpha> \<beta> s)) = (l \<in> LID\<^sub>G s)"
proof -
  show "(\<alpha> r \<in> RID\<^sub>G (\<R>\<^sub>G \<alpha> \<beta> s)) = (r \<in> RID\<^sub>G s)"
  proof (rule iffI)
    assume "\<alpha> r \<in> RID\<^sub>G (\<R>\<^sub>G \<alpha> \<beta> s)"
    thus "r \<in> RID\<^sub>G s" 
    proof (rule RID\<^sub>GE)
      assume "\<alpha> r \<in> dom (\<R>\<^sub>G \<alpha> \<beta> s)"
      hence "r \<in> dom s" by (metis bij_\<alpha> domIff fun_upd_same fun_upd_triv renaming_distr_global(2))
      thus "r \<in> RID\<^sub>G s" by auto
    next
      fix r' ls
      assume \<R>sr': "\<R>\<^sub>G \<alpha> \<beta> s r' = Some ls" and \<alpha>r: "\<alpha> r \<in> RID\<^sub>L ls"
      have s_inv_\<alpha>r': "s (inv \<alpha> r') = Some (\<R>\<^sub>L (inv \<alpha>) (inv \<beta>) ls)"
      proof -
        have "inv \<alpha> r' \<in> dom s" using \<R>sr' by auto
        then obtain ls' where s_inv_\<alpha>r: "s (inv \<alpha> r') = Some ls'" by blast
        hence "\<R>\<^sub>G \<alpha> \<beta> s r' = Some (\<R>\<^sub>L \<alpha> \<beta> ls')" by simp
        hence "ls = (\<R>\<^sub>L \<alpha> \<beta> ls')" using \<R>sr' by auto
        thus ?thesis by (metis \<R>\<^sub>L_inv s_inv_\<alpha>r bij_\<alpha> bij_\<beta>)
      qed
      have r_in: "r \<in> RID\<^sub>L (\<R>\<^sub>L (inv \<alpha>) (inv \<beta>) ls)"
        by (metis bij_\<alpha> bij_\<beta> bij_imp_bij_inv bijection.intro bijection.inv_left in_renamed_in_unlabelled_local(1) \<alpha>r)
      show "r \<in> RID\<^sub>G s"
        using r_in s_inv_\<alpha>r' by blast
    qed
  next
    assume "r \<in> RID\<^sub>G s"
    thus "\<alpha> r \<in> RID\<^sub>G (\<R>\<^sub>G \<alpha> \<beta> s)"
    proof (rule RID\<^sub>GE)
      assume "r \<in> dom s"
      hence "\<alpha> r \<in> dom (\<R>\<^sub>G \<alpha> \<beta> s)"
        by (metis (mono_tags, lifting) bij_\<alpha> domD domI fun_upd_same fun_upd_triv renaming_distr_global(1))
      thus "\<alpha> r \<in> RID\<^sub>G (\<R>\<^sub>G \<alpha> \<beta> s)" by auto
    next
      fix r' ls
      assume "s r' = Some ls" "r \<in> RID\<^sub>L ls"
      thus "\<alpha> r \<in> RID\<^sub>G (\<R>\<^sub>G \<alpha> \<beta> s)"
        by (metis ID_distr_global(1) UnI2 bij_\<alpha> bij_\<beta> fun_upd_triv in_renamed_in_unlabelled_local(1) insertI2 renaming_distr_global(1))
    qed
  qed
  show "(\<beta> l \<in> LID\<^sub>G (\<R>\<^sub>G \<alpha> \<beta> s)) = (l \<in> LID\<^sub>G s)"
  proof (rule iffI)
    assume "\<beta> l \<in> LID\<^sub>G (\<R>\<^sub>G \<alpha> \<beta> s)"
    from this obtain r ls where Rs_ls: "\<R>\<^sub>G \<alpha> \<beta> s r = Some ls" and \<beta>l_in_ls: "\<beta> l \<in> LID\<^sub>L ls" by blast
    hence "l \<in> LID\<^sub>L (\<R>\<^sub>L (inv \<alpha>) (inv \<beta>) ls)"
      by (metis bij_\<alpha> bij_\<beta> bij_imp_bij_inv bijection.intro bijection.inv_left in_renamed_in_unlabelled_local(2))
    hence "l \<in> LID\<^sub>G (\<R>\<^sub>G (inv \<alpha>) (inv \<beta>) (\<R>\<^sub>G \<alpha> \<beta> s))"
      by (metis (mono_tags, lifting) LID\<^sub>GI Rs_ls bij_\<alpha> bij_imp_bij_inv fun_upd_idem_iff renaming_distr_global(1))
    thus "l \<in> LID\<^sub>G s" using bij_\<alpha> bij_\<beta> by (metis \<R>\<^sub>G_inv)
  next
    assume "l \<in> LID\<^sub>G s"
    then obtain r s' ls where "s = (s'(r \<mapsto> ls))" "l \<in> LID\<^sub>L ls" by (metis LID\<^sub>GE fun_upd_triv)
    thus "\<beta> l \<in> LID\<^sub>G (\<R>\<^sub>G \<alpha> \<beta> s)" by (simp add: bij_\<alpha> bij_\<beta> in_renamed_in_unlabelled_local(2))
  qed
qed

lemma mimicking:
  assumes
    step: "revision_step r s s'" and
    bij_\<alpha>: "bij \<alpha>" and
    bij_\<beta>: "bij \<beta>"
  shows "revision_step (\<alpha> r) (\<R>\<^sub>G \<alpha> \<beta> s) (\<R>\<^sub>G \<alpha> \<beta> s')"
proof (use step in \<open>cases rule: revision_stepE\<close>)
  case app
  then show ?thesis by (auto simp add: bij_\<alpha> bij_\<beta> bijection.intro bijection.inv_left renaming_distr_subst)
next
  case (new _ _ _ _ l)
  have \<beta>l_fresh: "\<beta> l \<notin> LID\<^sub>G (\<R>\<^sub>G \<alpha> \<beta> s)"
    by (simp add: bij_\<alpha> bij_\<beta> in_renamed_in_unlabelled_global(2) new(3))
  show ?thesis using \<beta>l_fresh new by (auto simp add: bij_\<alpha> bij_\<beta> bijection.intro bijection.inv_left)   
next
  case (fork \<sigma> \<tau> \<E> e r')
  have \<alpha>r'_fresh: "\<alpha> r' \<notin> RID\<^sub>G (\<R>\<^sub>G \<alpha> \<beta> s)"
    by (simp add: bij_\<alpha> bij_\<beta> in_renamed_in_unlabelled_global(1) fork(3))
  have s_r_as_upd: "s = (s(r \<mapsto> (\<sigma>, \<tau>, \<E> [Rfork e])))" using fork(2) by auto
  have src: "\<R>\<^sub>G \<alpha> \<beta> s (\<alpha> r) = Some (\<R>\<^sub>S \<alpha> \<beta> \<sigma>, \<R>\<^sub>S \<alpha> \<beta> \<tau>, (\<R>\<^sub>C \<alpha> \<beta> \<E>) [Rfork (\<R>\<^sub>E \<alpha> \<beta> e)])" 
    by (subst s_r_as_upd, simp add: bij_\<alpha>)
  show ?thesis using \<alpha>r'_fresh src revision_step.fork fork(1) bij_\<alpha> by auto
qed (auto simp add: bij_\<alpha> bij_\<beta> bijection.intro bijection.inv_left)

lemma mimic_single_step:
  assumes
    s\<^sub>1s\<^sub>1': "s\<^sub>1 \<approx> s\<^sub>1'" and
    s\<^sub>1s\<^sub>2: "s\<^sub>1 \<leadsto> s\<^sub>2"
  shows "\<exists>s\<^sub>2'. (s\<^sub>2 \<approx> s\<^sub>2') \<and> s\<^sub>1' \<leadsto> s\<^sub>2'"
proof -
  from s\<^sub>1s\<^sub>1' obtain \<alpha> \<beta> where 
    bij_\<alpha>: "bij \<alpha>" and 
    bij_\<beta>: "bij \<beta>" and
    R: "\<R>\<^sub>G \<alpha> \<beta> s\<^sub>1 = s\<^sub>1'" by blast
  from s\<^sub>1s\<^sub>2 obtain r where step: "revision_step r s\<^sub>1 s\<^sub>2" by auto
  have mirrored_step: "revision_step (\<alpha> r) s\<^sub>1' (\<R>\<^sub>G \<alpha> \<beta> s\<^sub>2)" 
    using R bij_\<alpha> bij_\<beta> step mimicking by auto
  have eq: "s\<^sub>2 \<approx> (\<R>\<^sub>G \<alpha> \<beta> s\<^sub>2)" using bij_\<alpha> bij_\<beta> by blast
  have s\<^sub>1's\<^sub>2': "s\<^sub>1' \<leadsto> (\<R>\<^sub>G \<alpha> \<beta> s\<^sub>2)" using mirrored_step by auto
  from eq s\<^sub>1's\<^sub>2' show ?thesis by blast
qed

lemma mimic_trans:
  assumes
    s\<^sub>1_eq_s\<^sub>1': "s\<^sub>1 \<approx> s\<^sub>1'" and
    s\<^sub>1s\<^sub>2: "s\<^sub>1 \<leadsto>\<^sup>* s\<^sub>2"
  shows "\<exists>s\<^sub>2'. s\<^sub>2 \<approx> s\<^sub>2' \<and> s\<^sub>1' \<leadsto>\<^sup>* s\<^sub>2'"
proof -
  from s\<^sub>1_eq_s\<^sub>1' obtain \<alpha> \<beta> where
    bij_\<alpha>: "bij \<alpha>" and
    bij_\<beta>: "bij \<beta>" and
    R: "\<R>\<^sub>G \<alpha> \<beta> s\<^sub>1 = s\<^sub>1'"
    by blast
  from s\<^sub>1s\<^sub>2 obtain n where "(s\<^sub>1,s\<^sub>2) \<in> [\<leadsto>]^^n" using rtrancl_power by blast
  thus ?thesis
  proof (induct n arbitrary: s\<^sub>2)
    case 0
    thus ?case using s\<^sub>1_eq_s\<^sub>1' by auto
  next
    case (Suc n)
    obtain x where n_steps: "(s\<^sub>1, x) \<in> [\<leadsto>]^^n" and step: "x \<leadsto> s\<^sub>2" using Suc.prems by auto
    obtain x' where x_eq_x': "x \<approx> x'" and s\<^sub>1'x: "s\<^sub>1' \<leadsto>\<^sup>* x'" using Suc.hyps n_steps by blast
    obtain s\<^sub>2' where s\<^sub>2_eq_s\<^sub>2': "s\<^sub>2 \<approx> s\<^sub>2'" and x's\<^sub>2': "x' \<leadsto> s\<^sub>2'" 
      by (meson step mimic_single_step x_eq_x')
    show ?case using s\<^sub>1'x s\<^sub>2_eq_s\<^sub>2' trancl_into_rtrancl x's\<^sub>2' by auto
  qed
qed

subsubsection \<open>Strip diagram\<close>

lemma strip_lemma:
  assumes
    s\<^sub>1s\<^sub>2: "s\<^sub>1 \<leadsto>\<^sup>* s\<^sub>2" and
    s\<^sub>1s\<^sub>2': "s\<^sub>1 \<leadsto>\<^sup>= s\<^sub>2'" and
    reach: "reachable (s\<^sub>1 :: ('r,'l,'v) global_state)" and
    lid_inf: "infinite (UNIV :: 'l set)" and
    rid_inf: "infinite (UNIV :: 'r set)"
  shows "\<exists>s\<^sub>3 s\<^sub>3'. s\<^sub>3 \<approx> s\<^sub>3' \<and> s\<^sub>2 \<leadsto>\<^sup>* s\<^sub>3 \<and> s\<^sub>2' \<leadsto>\<^sup>* s\<^sub>3'"
proof -
  from s\<^sub>1s\<^sub>2 obtain n where "(s\<^sub>1, s\<^sub>2) \<in> [\<leadsto>]^^n" using rtrancl_power by blast
  from reach s\<^sub>1s\<^sub>2' and this show ?thesis
  proof (induct n arbitrary: s\<^sub>1 s\<^sub>2 s\<^sub>2')
    case 0
    hence "s\<^sub>1 = s\<^sub>2" by simp
    hence s\<^sub>2s\<^sub>2': "s\<^sub>2 \<leadsto>\<^sup>* s\<^sub>2'" using "0.prems"(2) by blast
    show ?case by (rule exI[where x=s\<^sub>2'], rule exI[where x=s\<^sub>2']) (use s\<^sub>2s\<^sub>2' in \<open>simp add: \<alpha>\<beta>_refl\<close>)
  next
    case (Suc n)
    obtain a where s\<^sub>1a: "s\<^sub>1 \<leadsto> a" and as\<^sub>2: "(a, s\<^sub>2) \<in> [\<leadsto>]^^n" by (meson Suc.prems(3) relpow_Suc_D2)
    obtain b c where "b \<approx> c" "a \<leadsto>\<^sup>= b" "s\<^sub>2' \<leadsto>\<^sup>= c"
      by (metis (mono_tags, lifting) SLC_top_relaxed Suc.prems(1) Suc.prems(2) \<alpha>\<beta>_sym lid_inf rid_inf s\<^sub>1a)
    obtain d e where "d \<approx> e" "s\<^sub>2 \<leadsto>\<^sup>* d" "b \<leadsto>\<^sup>* e"
      by (meson Suc.hyps Suc.prems(1) \<open>a \<leadsto>\<^sup>= b\<close> as\<^sub>2 reachability_closed_under_execution_step s\<^sub>1a valid_stepE)
    obtain f where "c \<leadsto>\<^sup>* f" "e \<approx> f"
      by (meson  \<open>b \<approx> c\<close> \<open>b \<leadsto>\<^sup>* e\<close> mimic_trans)
    have "d \<approx> f" using \<alpha>\<beta>_trans \<open>d \<approx> e\<close> \<open>e \<approx> f\<close> by auto
    then show ?case by (metis (no_types, lifting) \<open>c \<leadsto>\<^sup>* f\<close> \<open>s\<^sub>2 \<leadsto>\<^sup>* d\<close> \<open>s\<^sub>2' \<leadsto>\<^sup>= c\<close> r_into_rtrancl rtrancl_reflcl rtrancl_trans)
  qed
qed

subsubsection \<open>Confluence diagram\<close>

lemma confluence_modulo_equivalence:
  assumes
    s\<^sub>1s\<^sub>2: "s\<^sub>1 \<leadsto>\<^sup>* s\<^sub>2" and
    s\<^sub>1s\<^sub>2': "s\<^sub>1' \<leadsto>\<^sup>* s\<^sub>2'" and
    equiv: "s\<^sub>1 \<approx> s\<^sub>1'" and
    reach: "reachable (s\<^sub>1 :: ('r,'l,'v) global_state)" and
    lid_inf: "infinite (UNIV :: 'l set)" and
    rid_inf: "infinite (UNIV :: 'r set)"
  shows "\<exists>s\<^sub>3 s\<^sub>3'. s\<^sub>3 \<approx> s\<^sub>3' \<and> s\<^sub>2 \<leadsto>\<^sup>* s\<^sub>3 \<and> s\<^sub>2' \<leadsto>\<^sup>* s\<^sub>3'"
proof -
  obtain n where "(s\<^sub>1, s\<^sub>2) \<in> [\<leadsto>]^^n" using s\<^sub>1s\<^sub>2 rtrancl_power by blast
  from reach equiv s\<^sub>1s\<^sub>2' and this show ?thesis
  proof (induct n arbitrary: s\<^sub>1 s\<^sub>1' s\<^sub>2 s\<^sub>2')
    case base: 0
    hence "s\<^sub>1 = s\<^sub>2" by simp
    obtain s\<^sub>2'' where "s\<^sub>1 \<leadsto>\<^sup>* s\<^sub>2''" "s\<^sub>2' \<approx> s\<^sub>2''"
      using \<alpha>\<beta>_sym base.prems(2,3) mimic_trans by blast
    have "s\<^sub>2 \<leadsto>\<^sup>* s\<^sub>2''" using \<open>s\<^sub>1 = s\<^sub>2\<close> \<open>s\<^sub>1 \<leadsto>\<^sup>* s\<^sub>2''\<close> by blast
    show ?case by (rule exI[where x=s\<^sub>2''], rule exI[where x=s\<^sub>2']) (auto simp add: \<alpha>\<beta>_sym \<open>s\<^sub>2 \<leadsto>\<^sup>* s\<^sub>2''\<close> \<open>s\<^sub>2' \<approx> s\<^sub>2''\<close>)
  next
    case step: (Suc n)
    obtain a where s\<^sub>1a: "(s\<^sub>1, a) \<in> [\<leadsto>]^^n" and as\<^sub>2: "a \<leadsto> s\<^sub>2" using step.prems(4) by auto
    have "reachable a" using reachability_closed_under_execution relpow_imp_rtrancl s\<^sub>1a step.prems(1) by blast
    obtain b c where "a \<leadsto>\<^sup>* b" "s\<^sub>2' \<leadsto>\<^sup>* c" "b \<approx> c"
      using s\<^sub>1a step.hyps step.prems(1-3) by blast
    have "a \<leadsto>\<^sup>* s\<^sub>2" by (simp add: as\<^sub>2 r_into_rtrancl)
    obtain s\<^sub>3 d where "s\<^sub>3 \<approx> d" "s\<^sub>2 \<leadsto>\<^sup>* s\<^sub>3" "b \<leadsto>\<^sup>* d" 
      by (meson \<alpha>\<beta>_sym \<open>a \<leadsto>\<^sup>* b\<close> \<open>reachable a\<close> as\<^sub>2 lid_inf refl_rewritesI rid_inf strip_lemma)
    obtain s\<^sub>3' where "s\<^sub>3 \<approx> s\<^sub>3'" "c \<leadsto>\<^sup>* s\<^sub>3'"
      by (meson \<alpha>\<beta>_trans \<open>b \<approx> c\<close> \<open>b \<leadsto>\<^sup>* d\<close> \<open>s\<^sub>3 \<approx> d\<close> mimic_trans)
    show ?case by (meson \<open>c \<leadsto>\<^sup>* s\<^sub>3'\<close> \<open>s\<^sub>2 \<leadsto>\<^sup>* s\<^sub>3\<close> \<open>s\<^sub>2' \<leadsto>\<^sup>* c\<close> \<open>s\<^sub>3 \<approx> s\<^sub>3'\<close> transD trans_rtrancl)
  qed
qed

subsection \<open>Determinacy\<close>

theorem determinacy:
  assumes 
    prog_expr: "program_expr e" and
    e_terminates_in_s: "e \<down> s" and
    e_terminates_in_s': "e \<down> s'" and
    lid_inf: "infinite (UNIV :: 'l set)" and
    rid_inf: "infinite (UNIV :: 'r set)"
  shows "s \<approx> s'"
proof -
  obtain r where x: "(\<epsilon>(r \<mapsto> (\<epsilon>,\<epsilon>,e))) \<leadsto>\<^sup>* s"
    by (metis e_terminates_in_s execution_def maximal_execution_def terminates_in_def)
  obtain r' where y: "(\<epsilon>(r' \<mapsto> (\<epsilon>,\<epsilon>,e))) \<leadsto>\<^sup>* s'"
    by (metis e_terminates_in_s' execution_def maximal_execution_def terminates_in_def)
  let "?\<alpha>" = "id(r := r', r' := r)"
  have bij_\<alpha>: "bij ?\<alpha>" by (simp add: swap_bij)
  have equiv: "(\<epsilon>(r \<mapsto> (\<epsilon>,\<epsilon>,e))) \<approx> (\<epsilon>(r' \<mapsto> (\<epsilon>,\<epsilon>,e)))" 
  proof (rule eq_statesI[of ?\<alpha> id])
    show "\<R>\<^sub>G ?\<alpha> id (\<epsilon>(r \<mapsto> (\<epsilon>, \<epsilon>, e))) = \<epsilon>(r' \<mapsto> (\<epsilon>, \<epsilon>, e))"
      using bij_\<alpha> prog_expr by auto
  qed (simp add: bij_\<alpha>)+
  have reach: "reachable (\<epsilon>(r \<mapsto> (\<epsilon>,\<epsilon>,e)))" 
    by (simp add: initial_state_reachable prog_expr)
  have "\<exists>a b. (a \<approx> b) \<and> s \<leadsto>\<^sup>* a \<and> s' \<leadsto>\<^sup>* b"
    by (rule confluence_modulo_equivalence[OF x y equiv reach lid_inf rid_inf])
  from this obtain a b where "s \<leadsto>\<^sup>* a" "s' \<leadsto>\<^sup>* b" "a \<approx> b" by blast
  have "s = a" by (meson \<open>s \<leadsto>\<^sup>* a\<close> e_terminates_in_s maximal_execution_def rtranclD terminates_in_def tranclD)
  have "s' = b" by (meson \<open>s' \<leadsto>\<^sup>* b\<close> converse_rtranclE e_terminates_in_s' maximal_execution_def terminates_in_def)
  show ?thesis using \<open>a \<approx> b\<close> \<open>s = a\<close> \<open>s' = b\<close> by auto
qed

end (* substitution locale *)

end