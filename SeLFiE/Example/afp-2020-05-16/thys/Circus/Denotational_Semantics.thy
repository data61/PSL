section \<open>Denotational semantics of Circus actions\<close>

theory Denotational_Semantics 
imports Circus_Actions Var_list
begin

text \<open>In this section, we introduce the definitions of Circus actions denotational semantics.
We provide the proof of well-formedness of every action. We also provide proofs concerning 
the monotonicity of operators over actions.\<close>

subsection \<open>Skip\<close>

definition Skip :: "('\<theta>::ev_eq,'\<sigma>) action" where
"Skip \<equiv> action_of 
                  (R (true \<turnstile> \<lambda>(A, A'). tr A' = tr A \<and> \<not>wait A' \<and> more A = more A'))"

lemma Skip_is_action: 
"(R (true \<turnstile> \<lambda>(A, A'). tr A' = tr A \<and> \<not>wait A' \<and> more A = more A')) \<in> {p. is_CSP_process p}"
apply (simp)
apply (rule rd_is_CSP)
by auto

lemmas Skip_is_CSP = Skip_is_action[simplified]

lemma relation_of_Skip: 
"relation_of Skip = 
                  (R (true \<turnstile> \<lambda>(A, A'). tr A' = tr A \<and> \<not>wait A' \<and> more A = more A'))"
by (simp add: Skip_def action_of_inverse Skip_is_CSP)

definition CSP3::"(('\<theta>::ev_eq,'\<sigma>) alphabet_rp) Healthiness_condition"
where "CSP3 (P)  \<equiv>  relation_of Skip ;; P"

definition CSP4::"(('\<theta>::ev_eq,'\<sigma>) alphabet_rp) Healthiness_condition"
where "CSP4 (P)  \<equiv>  P ;; relation_of Skip"

lemma Skip_is_CSP3: "(relation_of Skip) is CSP3 healthy"
apply (auto simp: relation_of_Skip rp_defs design_defs fun_eq_iff CSP3_def)
apply (split cond_splits, simp_all)+
apply (rule_tac b=b in comp_intro)
apply (split cond_splits, simp_all)+
apply (rule_tac b=b in comp_intro)
apply (split cond_splits, simp_all)+
prefer 3
apply (split cond_splits, simp_all)+
apply (auto simp add: prefix_def)
done

lemma Skip_is_CSP4: "(relation_of Skip) is CSP4 healthy"
apply (auto simp: relation_of_Skip rp_defs design_defs fun_eq_iff CSP4_def)
apply (split cond_splits, simp_all)+
apply (rule_tac b=b in comp_intro)
apply (split cond_splits, simp_all)+
apply (rule_tac b=b in comp_intro)
apply (split cond_splits, simp_all)+
prefer 3
apply (split cond_splits, simp_all)+
apply (auto simp add: prefix_def)
done


lemma Skip_comp_absorb: "(relation_of Skip ;; relation_of Skip) = relation_of Skip"
apply (auto simp: relation_of_Skip fun_eq_iff rp_defs true_def design_defs)
apply (clarsimp split: cond_splits)+
apply (case_tac "ok aa", simp_all)
apply (erule disjE)+
apply (clarsimp simp: prefix_def)
apply (clarsimp simp: prefix_def)
apply (erule disjE)+
apply (clarsimp simp: prefix_def)
apply (clarsimp simp: prefix_def)
apply (erule disjE)+
apply (clarsimp simp: prefix_def)
apply (clarsimp simp: prefix_def)
apply (case_tac "ok aa", simp_all)
apply (clarsimp simp: prefix_def)
apply (clarsimp split: cond_splits)+
apply (rule_tac b=a in comp_intro)
apply (clarsimp split: cond_splits)+
apply (rule_tac b=a in comp_intro)
apply (clarsimp split: cond_splits)+
done


subsection \<open>Stop\<close>

definition Stop :: "('\<theta>::ev_eq,'\<sigma>) action"
where "Stop \<equiv> action_of (R (true \<turnstile> \<lambda>(A, A'). tr A' = tr A \<and> wait A'))"

lemma Stop_is_action:
"(R (true \<turnstile> \<lambda>(A, A'). tr A' = tr A \<and> wait A')) \<in> {p. is_CSP_process p}"
apply (simp)
apply (rule rd_is_CSP)
by auto

lemmas Stop_is_CSP = Stop_is_action[simplified]

lemma relation_of_Stop:
"relation_of Stop = (R (true \<turnstile> \<lambda>(A, A'). tr A' = tr A \<and> wait A'))"
by (simp add: Stop_def action_of_inverse Stop_is_CSP)


lemma Stop_is_CSP3: "(relation_of Stop) is CSP3 healthy"
apply (auto simp: relation_of_Stop relation_of_Skip rp_defs design_defs fun_eq_iff CSP3_def)
apply (rule_tac b=a in comp_intro)
apply (split cond_splits, auto)
apply (split cond_splits)+
apply (simp_all)
apply (case_tac "ok aa", simp_all)
apply (case_tac "tr aa \<le> tr ba", simp_all)
apply (case_tac "ok ba", simp_all)
apply (case_tac "tr ba \<le> tr c", simp_all)
apply (rule disjI1)
apply (simp add: prefix_def)
apply (erule exE)+
apply (rule_tac x="zs@zsa" in exI, simp)
apply (rule disjI1)
apply (simp add: prefix_def)
apply (erule exE | erule conjE)+
apply (rule_tac x="zs@zsa" in exI, simp)
apply (split cond_splits)+
apply (simp_all add: true_def)
apply (erule disjE)
apply (simp add: prefix_def)
apply (erule exE | erule conjE)+
apply (rule_tac x="zs@zsa" in exI, simp)
apply (auto simp add: prefix_def)
done


lemma Stop_is_CSP4: "(relation_of Stop) is CSP4 healthy"
apply (auto simp: relation_of_Stop relation_of_Skip rp_defs design_defs fun_eq_iff CSP4_def)
apply (rule_tac b=b in comp_intro)
apply (split cond_splits, simp_all)+
apply (case_tac "ok aa", simp_all)
apply (case_tac "tr aa \<le> tr ba", simp_all)
apply (case_tac "ok ba", simp_all)
apply (case_tac "tr ba \<le> tr c", simp_all)
apply (rule disjI1)
apply (simp add: prefix_def)
apply (erule exE)+
apply (rule_tac x="zs@zsa" in exI, simp)
apply (rule disjI1)
apply (simp add: prefix_def)
apply (erule exE | erule conjE)+
apply (rule_tac x="zs@zsa" in exI, simp)
apply (split cond_splits)+
apply (simp_all add: true_def)
apply (erule disjE)
apply (simp add: prefix_def)
apply (erule exE | erule conjE)+
apply (rule_tac x="zs@zsa" in exI, simp)
apply (auto simp add: prefix_def)
done

subsection \<open>Chaos\<close>

definition Chaos :: "('\<theta>::ev_eq,'\<sigma>) action"
where "Chaos \<equiv> action_of (R(false \<turnstile> true))"

lemma Chaos_is_action: "(R(false \<turnstile> true)) \<in> {p. is_CSP_process p}"
apply (simp)
apply (rule rd_is_CSP)
by auto

lemmas Chaos_is_CSP = Chaos_is_action[simplified]

lemma relation_of_Chaos: "relation_of Chaos = (R(false \<turnstile> true))"
by (simp add: Chaos_def action_of_inverse Chaos_is_CSP)


subsection \<open>State update actions\<close>

definition Pre ::"'\<sigma> relation  \<Rightarrow> '\<sigma> predicate"
where "Pre sc \<equiv> \<lambda>A. \<exists> A'. sc (A, A')"


definition state_update_before :: "'\<sigma> relation \<Rightarrow> ('\<theta>::ev_eq,'\<sigma>) action \<Rightarrow> ('\<theta>,'\<sigma>) action"
where "state_update_before sc Ac = action_of(R ((\<lambda>(A, A'). (Pre sc) (more A)) \<turnstile> 
                      (\<lambda>(A, A'). sc (more A, more A') & \<not>wait A' & tr A = tr A')) ;; relation_of Ac)"

lemma state_update_before_is_action: 
"(R ((\<lambda>(A, A'). (Pre sc) (more A)) \<turnstile> 
                               (\<lambda>(A, A').sc (more A, more A') & \<not>wait A' & tr A = tr A')) ;; relation_of Ac) \<in> {p. is_CSP_process p}"
apply (simp)
apply (rule seq_CSP)
apply (rule rd_is_CSP1)
apply (auto simp: R_idem2 Healthy_def relation_of_CSP)
done

lemmas state_update_before_is_CSP = state_update_before_is_action[simplified]

lemma relation_of_state_update_before:
"relation_of (state_update_before sc Ac) = (R ((\<lambda>(A, A'). (Pre sc) (more A)) \<turnstile> 
                               (\<lambda>(A, A'). sc (more A, more A') & \<not>wait A' & tr A = tr A')) ;; relation_of Ac)"
by (simp add: state_update_before_def action_of_inverse state_update_before_is_CSP)

lemma mono_state_update_before: "mono (state_update_before sc)"
by (auto simp: mono_def less_eq_action ref_def relation_of_state_update_before design_defs rp_defs fun_eq_iff 
            split: cond_splits dest: relation_of_spec_f_f[simplified] 
                                     relation_of_spec_t_f[simplified])

lemma state_update_before_is_CSP3: "relation_of (state_update_before sc Ac) is CSP3 healthy"
apply (auto simp: relation_of_state_update_before relation_of_Skip rp_defs design_defs fun_eq_iff CSP3_def)
apply (rule_tac b=aa in comp_intro)
apply (split cond_splits, auto)
apply (split cond_splits, simp_all)+
apply (rule_tac b=bb in comp_intro)
apply (split cond_splits, simp_all)+
apply (case_tac "ok aa", simp_all)
apply (case_tac "tr aa \<le> tr ab", simp_all)
apply (case_tac "ok ab", simp_all)
apply (case_tac "tr ab \<le> tr bb", simp_all)
apply (rule disjI1)
apply (simp add: prefix_def)
apply (erule exE)+
apply (rule_tac x="zs@zsa" in exI, simp)
apply (rule_tac b=bb in comp_intro)
apply (split cond_splits, simp_all)+
apply (rule disjI1)
apply (simp add: prefix_def)
apply (erule exE | erule conjE)+
apply (rule_tac x="zs@zsa" in exI, simp)
apply (rule_tac b=bb in comp_intro)
apply (split cond_splits, simp_all)+
apply (simp_all add: true_def)
apply (erule disjE)
apply (simp add: prefix_def)
apply (erule exE | erule conjE)+
apply (rule_tac x="zs@zsa" in exI, simp)
apply (auto simp add: prefix_def)
done


lemma state_update_before_is_CSP4: 
  assumes A : "relation_of Ac is CSP4 healthy"
  shows "relation_of (state_update_before sc Ac) is CSP4 healthy"
apply (auto simp: relation_of_state_update_before relation_of_Skip rp_defs design_defs fun_eq_iff CSP4_def)
apply (rule_tac b=c in comp_intro)
apply (rule_tac b=ba in comp_intro, simp_all)
apply (split cond_splits, simp_all)
apply (rule_tac b=bb in comp_intro, simp_all)
apply (subst A[simplified design_defs rp_defs CSP4_def relation_of_Skip])
apply (auto simp: rp_defs)
done

definition state_update_after :: "'\<sigma> relation \<Rightarrow> ('\<theta>::ev_eq,'\<sigma>) action \<Rightarrow> ('\<theta>,'\<sigma>) action"
where "state_update_after sc Ac = action_of(relation_of Ac ;; R (true \<turnstile> (\<lambda>(A, A'). sc (more A, more A') & \<not>wait A' & tr A = tr A')))"

lemma state_update_after_is_action: 
"(relation_of Ac ;; R (true \<turnstile> (\<lambda>(A, A'). sc (more A, more A') & \<not>wait A' & tr A = tr A'))) \<in> {p. is_CSP_process p}"
apply (simp)
apply (rule seq_CSP)
apply (auto simp: relation_of_CSP[simplified is_CSP_process_def])
apply (rule rd_is_CSP, auto)
done

lemmas state_update_after_is_CSP = state_update_after_is_action[simplified]

lemma relation_of_state_update_after:
"relation_of (state_update_after sc Ac) = (relation_of Ac ;; R (true \<turnstile> (\<lambda>(A, A'). sc (more A, more A') & \<not>wait A' & tr A = tr A')))"
by (simp add: state_update_after_def action_of_inverse state_update_after_is_CSP)

lemma mono_state_update_after: "mono (state_update_after sc)"
by (auto simp: mono_def less_eq_action ref_def relation_of_state_update_after design_defs rp_defs fun_eq_iff 
            split: cond_splits dest: relation_of_spec_f_f[simplified] 
                                     relation_of_spec_t_f[simplified])


lemma state_update_after_is_CSP3: 
  assumes A : "relation_of Ac is CSP3 healthy"
  shows "relation_of (state_update_after sc Ac) is CSP3 healthy"
apply (auto simp: relation_of_state_update_after relation_of_Skip rp_defs design_defs fun_eq_iff CSP3_def)
apply (rule_tac b=aa in comp_intro)
apply (split cond_splits, auto)
apply (rule_tac b=bb in comp_intro, simp_all)
apply (subst A[simplified design_defs rp_defs CSP3_def relation_of_Skip])
apply (auto simp: rp_defs)
done


lemma state_update_after_is_CSP4: "relation_of (state_update_after sc Ac) is CSP4 healthy"
apply (auto simp: relation_of_state_update_after relation_of_Skip rp_defs design_defs fun_eq_iff CSP4_def)
apply (rule_tac b=c in comp_intro)
apply (rule_tac b=ba in comp_intro, simp_all)
apply (split cond_splits, simp_all)+
apply (rule_tac b=bb in comp_intro, simp_all)
apply (split cond_splits, simp_all)+
apply (case_tac "ok bb", simp_all)
apply (case_tac "tr bb \<le> tr c", simp_all)
apply (case_tac "ok ca", simp_all)
apply (case_tac "tr ca \<le> tr c", simp_all)
apply (simp add: prefix_def)
apply (erule exE)+
apply (erule_tac x="zs@zsa" in allE, simp)
apply (rule_tac b=bb in comp_intro, simp_all)
apply (split cond_splits, simp_all add: true_def)+
apply (case_tac "ok ca", simp_all)
apply (case_tac "tr ca \<le> tr c", simp_all)
apply (simp add: prefix_def)
apply (erule exE | erule conjE)+
apply (rule_tac x="zsa@zs" in exI, simp)
apply (rule_tac b=bb in comp_intro, simp_all)
apply (split cond_splits, simp_all)+
apply (case_tac "tr bb \<le> tr c", simp_all)
apply (simp add: prefix_def)
apply (erule exE | erule conjE)+
apply (erule_tac x="zsa@zs" in allE, simp)
apply (auto simp add: prefix_def)
done



subsection \<open>Sequential composition\<close>

definition 
Seq::"('\<theta>::ev_eq,'\<sigma>) action \<Rightarrow> ('\<theta>,'\<sigma>) action \<Rightarrow> ('\<theta>,'\<sigma>) action" (infixl "`;`" 24)
where "P `;` Q \<equiv> action_of (relation_of P ;; relation_of Q)"

lemma Seq_is_action: "(relation_of P ;; relation_of Q) \<in> {p. is_CSP_process p}"
apply (simp)
apply (rule seq_CSP[OF relation_of_CSP[THEN CSP_is_CSP1] relation_of_CSP[THEN CSP_is_R] relation_of_CSP])
done

lemmas Seq_is_CSP = Seq_is_action[simplified]

lemma relation_of_Seq: "relation_of (P `;` Q) = (relation_of P ;; relation_of Q)"
by (simp add: Seq_def action_of_inverse Seq_is_CSP)

lemma mono_Seq: "mono ((`;`) P)"
  by (auto simp: mono_def less_eq_action ref_def relation_of_Seq)


lemma CSP3_imp_left_Skip:
  assumes A: "relation_of P is CSP3 healthy"
  shows "(Skip `;` P) = P"
apply (subst relation_of_inject[symmetric])
apply (simp add: relation_of_Seq A[simplified design_defs CSP3_def, symmetric])
done

lemma CSP4_imp_right_Skip:
  assumes A: "relation_of P is CSP4 healthy"
  shows "(P `;` Skip) = P"
apply (subst relation_of_inject[symmetric])
apply (simp add: relation_of_Seq A[simplified design_defs CSP4_def, symmetric])
done

lemma Seq_assoc: "(A `;` (B `;` C)) = ((A `;` B) `;` C)"
by (auto simp: relation_of_inject[symmetric] fun_eq_iff relation_of_Seq rp_defs design_defs)

lemma Skip_absorb: "(Skip `;` Skip) = Skip"
by (auto simp: Skip_comp_absorb relation_of_inject[symmetric] relation_of_Seq)


subsection \<open>Internal choice\<close>

definition 
Ndet::"('\<theta>::ev_eq,'\<sigma>) action \<Rightarrow> ('\<theta>,'\<sigma>) action \<Rightarrow> ('\<theta>,'\<sigma>) action" (infixl "\<sqinter>" 18) 
where "P \<sqinter> Q \<equiv> action_of ((relation_of P) \<or> (relation_of Q))"

lemma Ndet_is_action: "((relation_of P) \<or> (relation_of Q)) \<in> {p. is_CSP_process p}"
apply (simp)
apply (rule disj_CSP)
apply (simp_all add: relation_of_CSP)
done

lemmas Ndet_is_CSP = Ndet_is_action[simplified]

lemma relation_of_Ndet: "relation_of (P \<sqinter> Q) = ((relation_of P) \<or> (relation_of Q))"
by (simp add: Ndet_def action_of_inverse Ndet_is_CSP)

lemma mono_Ndet: "mono ((\<sqinter>) P)"
by (auto simp: mono_def less_eq_action ref_def relation_of_Ndet)

subsection \<open>External choice\<close>

definition
Det::"('\<theta>::ev_eq,'\<sigma>) action \<Rightarrow> ('\<theta>,'\<sigma>) action \<Rightarrow> ('\<theta>,'\<sigma>) action" (infixl "\<box>" 18)
where "P \<box> Q \<equiv> action_of(R((\<not>((relation_of P)\<^sup>f\<^sub>f) \<and> \<not>((relation_of Q)\<^sup>f\<^sub>f)) \<turnstile>
                                             (((relation_of P)\<^sup>t\<^sub>f \<and> ((relation_of Q)\<^sup>t\<^sub>f))
                                                \<triangleleft> \<lambda>(A, A'). tr A = tr A' \<and> wait A' \<triangleright>
                                              ((relation_of P)\<^sup>t\<^sub>f \<or> ((relation_of Q)\<^sup>t\<^sub>f)))))"

lemma Det_is_action: 
"(R((\<not>((relation_of P)\<^sup>f\<^sub>f) \<and> \<not>((relation_of Q)\<^sup>f\<^sub>f)) \<turnstile>
           (((relation_of P)\<^sup>t\<^sub>f \<and> ((relation_of Q)\<^sup>t\<^sub>f))
              \<triangleleft> \<lambda>(A, A'). tr A = tr A' \<and> wait A' \<triangleright>
            ((relation_of P)\<^sup>t\<^sub>f \<or> ((relation_of Q)\<^sup>t\<^sub>f))))) \<in> {p. is_CSP_process p}"
apply (simp add: spec_def)
apply (rule rd_is_CSP)
apply (auto)
done

lemmas Det_is_CSP = Det_is_action[simplified]

lemma relation_of_Det:
"relation_of (P \<box> Q) = (R((\<not>((relation_of P)\<^sup>f\<^sub>f) \<and> \<not>((relation_of Q)\<^sup>f\<^sub>f)) \<turnstile>
                                          (((relation_of P)\<^sup>t\<^sub>f \<and> ((relation_of Q)\<^sup>t\<^sub>f))
                                             \<triangleleft> \<lambda>(A, A'). tr A = tr A' \<and> wait A' \<triangleright>
                                           ((relation_of P)\<^sup>t\<^sub>f \<or> ((relation_of Q)\<^sup>t\<^sub>f)))))"
apply (unfold Det_def)
apply (rule action_of_inverse)
apply (rule Det_is_action)
done

lemma mono_Det: "mono ((\<box>) P)"
by (auto simp: mono_def less_eq_action ref_def relation_of_Det design_defs rp_defs fun_eq_iff 
            split: cond_splits dest: relation_of_spec_f_f[simplified] 
                                     relation_of_spec_t_f[simplified])


subsection \<open>Reactive design assignment\<close>


definition 
"rd_assign s = action_of (R (true \<turnstile> \<lambda>(A, A'). ref A' = ref A \<and> tr A' = tr A \<and> \<not>wait A' \<and> more A' = s))"


lemma rd_assign_is_action: 
"(R (true \<turnstile> \<lambda>(A, A'). ref A' = ref A \<and> tr A' = tr A \<and> \<not>wait A' \<and> more A' = s)) \<in> {p. is_CSP_process p}"
apply (auto simp:)
apply (rule rd_is_CSP)
by auto

lemmas rd_assign_is_CSP = rd_assign_is_action[simplified]

lemma relation_of_rd_assign: 
"relation_of (rd_assign s) = 
                  (R (true \<turnstile> \<lambda>(A, A'). ref A' = ref A \<and> tr A' = tr A \<and> \<not>wait A' \<and> more A' = s))"
by (simp add: rd_assign_def  action_of_inverse rd_assign_is_CSP)





subsection \<open>Local state external choice\<close>

definition
Loc::"'\<sigma> \<Rightarrow> ('\<theta>::ev_eq,'\<sigma>) action \<Rightarrow> '\<sigma> \<Rightarrow> ('\<theta>,'\<sigma>) action \<Rightarrow> ('\<theta>,'\<sigma>) action" 
                                        ("'(()loc _ \<bullet> _ ') \<boxplus> '(()loc _ \<bullet> _ ')")
where "(loc s1 \<bullet> P) \<boxplus> (loc s2 \<bullet> Q) \<equiv> 
                   ((rd_assign s1)`;`P) \<box> ((rd_assign s2)`;` Q)"



subsection \<open>Schema expression\<close>


definition Schema :: "'\<sigma> relation \<Rightarrow> ('\<theta>::ev_eq,'\<sigma>) action" where
"Schema sc \<equiv> action_of(R ((\<lambda>(A, A'). (Pre sc) (more A)) \<turnstile> 
                           (\<lambda>(A, A'). sc (more A, more A') \<and> \<not>wait A' \<and> tr A = tr A')))"

lemma Schema_is_action: 
"(R ((\<lambda>(A, A'). (Pre sc) (more A)) \<turnstile> 
                 (\<lambda>(A, A'). sc (more A, more A') & \<not>wait A' & tr A = tr A'))) \<in> {p. is_CSP_process p}"
apply (simp)
apply (rule rd_is_CSP)
apply (auto)
done

lemmas Schema_is_CSP = Schema_is_action[simplified]

lemma relation_of_Schema:
"relation_of (Schema sc) = (R ((\<lambda>(A, A'). (Pre sc) (more A)) \<turnstile> 
                          (\<lambda>(A, A'). sc (more A, more A') \<and> \<not>wait A' \<and> tr A = tr A')))"
by (simp add: Schema_def action_of_inverse Schema_is_CSP)

lemma Schema_is_state_update_before: "Schema u = state_update_before u Skip"
apply (subst relation_of_inject[symmetric])
apply (auto simp: relation_of_Schema relation_of_state_update_before relation_of_Skip rp_defs fun_eq_iff
                  design_defs)
apply (split cond_splits, simp_all)
apply (rule comp_intro)
apply (split cond_splits, simp_all)+
apply (rule comp_intro)
apply (split cond_splits, simp_all)+
prefer 3
apply (split cond_splits, simp_all)+
apply (auto simp: prefix_def)
done



subsection \<open>Parallel composition\<close>

type_synonym '\<sigma> local_state = "('\<sigma> \<times> ('\<sigma>  \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>))"

fun MergeSt :: "'\<sigma> local_state \<Rightarrow> '\<sigma> local_state \<Rightarrow> ('\<theta>,'\<sigma>) relation_rp" where 
"MergeSt (s1,s1') (s2,s2') = ((\<lambda>(S, S'). (s1' s1) (more S) = more S');; 
                            (\<lambda>(S::('\<theta>,'\<sigma>) alphabet_rp, S'). (s2' s2) (more S) = more S'))"

definition listCons ::"'\<theta> \<Rightarrow> '\<theta> list list \<Rightarrow> '\<theta> list list" ("_ ## _") where
"a ## l = ((map (Cons a)) l)"

fun ParMergel :: "'\<theta>::ev_eq list \<Rightarrow> '\<theta> list \<Rightarrow> '\<theta> set \<Rightarrow> '\<theta> list list" where
    "ParMergel [] [] cs = [[]]"
  | "ParMergel [] (b#tr2) cs = (if (filter_chan_set b cs) then [[]]
                                          else (b ## (ParMergel [] tr2 cs)))" 
  | "ParMergel (a#tr1) [] cs = (if (filter_chan_set a cs) then [[]]
                                          else (a ## (ParMergel tr1 [] cs)))"
  | "ParMergel (a#tr1) (b#tr2) cs =
           (if (filter_chan_set a cs)
                   then (if (ev_eq a b)
                              then (a ## (ParMergel tr1 tr2 cs)) 
                               else (if (filter_chan_set b cs) 
                                        then [[]] 
                                         else (b ## (ParMergel (a#tr1) tr2 cs))))
                     else (if (filter_chan_set b cs) 
                               then (a ## (ParMergel tr1 (b#tr2) cs)) 
                                 else (a ## (ParMergel tr1 (b#tr2) cs)) 
                                            @ (b ## (ParMergel (a#tr1) tr2 cs))))"

definition ParMerge::"'\<theta>::ev_eq list \<Rightarrow> '\<theta> list \<Rightarrow> '\<theta> set \<Rightarrow> '\<theta> list set" where
"ParMerge tr1 tr2 cs = set (ParMergel tr1 tr2 cs)"

lemma set_Cons1: "tr1 \<in> set l \<Longrightarrow> a # tr1 \<in> (#) a ` set l"
by (auto)

lemma tr_in_set_eq: "(tr1 \<in> (#) b ` set l) = (tr1 \<noteq> [] \<and> hd tr1 = b \<and> tl tr1 \<in> set l)"
by (induct l) auto



definition M_par::"(('\<theta>::ev_eq), '\<sigma>) alpha_rp_scheme \<Rightarrow> ('\<sigma>  \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>)
                            \<Rightarrow> ('\<theta>, '\<sigma>) alpha_rp_scheme \<Rightarrow> ('\<sigma> \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>)
                                \<Rightarrow> ('\<theta> set) \<Rightarrow> ('\<theta>, '\<sigma>) relation_rp" where
"M_par s1 x1 s2 x2 cs = 
((\<lambda>(S, S'). ((diff_tr S' S) \<in> ParMerge (diff_tr s1 S) (diff_tr s2 S) cs &
     ev_eq (tr_filter (tr s1) cs) (tr_filter (tr s2) cs))) \<and>
   ((\<lambda>(S, S'). (wait s1 \<or> wait s2) \<and> 
                             ref S' \<subseteq> ((((ref s1)\<union>(ref s2))\<inter>cs)\<union>(((ref s1)\<inter>(ref s2))-cs)))
   \<triangleleft> wait o snd \<triangleright>
   ((\<lambda>(S, S'). (\<not>wait s1 \<or> \<not>wait s2)) \<and> MergeSt ((more s1), x1) ((more s2), x2))))"

definition  Par::"('\<theta>::ev_eq,'\<sigma>) action \<Rightarrow> 
                    ('\<sigma>  \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>) \<Rightarrow> '\<theta> set \<Rightarrow> ('\<sigma>  \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>) \<Rightarrow> 
                    ('\<theta>,'\<sigma>) action \<Rightarrow> ('\<theta>,'\<sigma>) action" ("_ \<lbrakk> _ | _ | _ \<rbrakk> _") where
"A1 \<lbrakk> ns1 | cs | ns2 \<rbrakk> A2 \<equiv> (action_of (R ((\<lambda> (S, S'). 
 \<not> (\<exists> tr1 tr2. ((relation_of A1)\<^sup>f\<^sub>f ;; (\<lambda> (S, S'). tr1 = (tr S))) (S, S') 
 \<and> (spec False (wait S) (relation_of A2) ;; (\<lambda> (S, _). tr2 = (tr S))) (S, S')
 \<and> ((tr_filter tr1 cs) = (tr_filter tr2 cs))) \<and>
 \<not> (\<exists> tr1 tr2. (spec False (wait S) (relation_of A1);;(\<lambda>(S, _). tr1 = tr S)) (S, S')
 \<and> ((relation_of A2)\<^sup>f\<^sub>f ;; (\<lambda>(S, S'). tr2 = (tr S))) (S, S') 
 \<and> ((tr_filter tr1 cs) = (tr_filter tr2 cs)))) \<turnstile> 
   (\<lambda> (S, S'). (\<exists> s1 s2. ((\<lambda> (A, A'). (relation_of A1)\<^sup>t\<^sub>f (A, s1)
 \<and> ((relation_of A2)\<^sup>t\<^sub>f (A, s2)));; M_par s1 ns1 s2 ns2 cs) (S, S'))))))"

lemma Par_is_action: "(R ((\<lambda> (S, S'). 
 \<not> (\<exists> tr1 tr2. ((relation_of A1)\<^sup>f\<^sub>f ;; (\<lambda> (S, S'). tr1 = (tr S))) (S, S') 
 \<and> (spec False (wait S) (relation_of A2) ;; (\<lambda> (S, S'). tr2 = (tr S))) (S, S')
 \<and> ((tr_filter tr1 cs) = (tr_filter tr2 cs))) \<and>
 \<not> (\<exists> tr1 tr2. (spec False (wait S) (relation_of A1);;(\<lambda>(S, _). tr1 = tr S)) (S, S')
 \<and> ((relation_of A2)\<^sup>f\<^sub>f ;; (\<lambda> (S, S'). tr2 = (tr S))) (S, S') 
 \<and> ((tr_filter tr1 cs) = (tr_filter tr2 cs)))) \<turnstile> 
   (\<lambda> (S, S'). (\<exists> s1 s2. ((\<lambda> (A, A'). (relation_of A1)\<^sup>t\<^sub>f (A, s1)
 \<and> ((relation_of A2)\<^sup>t\<^sub>f (A, s2)));; M_par s1 ns1 s2 ns2 cs) (S, S'))))) \<in> {p. is_CSP_process p}"
apply (simp)
apply (rule rd_is_CSP)
apply (blast)
done

lemmas Par_is_CSP = Par_is_action[simplified]

lemma relation_of_Par:
"relation_of (A1 \<lbrakk> ns1 | cs | ns2 \<rbrakk> A2) = (R ((\<lambda> (S, S'). 
 \<not> (\<exists> tr1 tr2. ((relation_of A1)\<^sup>f\<^sub>f ;; (\<lambda> (S, S'). tr1 = (tr S))) (S, S') 
 \<and> (spec False (wait S) (relation_of A2) ;; (\<lambda> (S, S'). tr2 = (tr S))) (S, S') 
 \<and> ((tr_filter tr1 cs) = (tr_filter tr2 cs))) \<and>
 \<not> (\<exists> tr1 tr2. (spec False (wait S) (relation_of A1);;(\<lambda>(S, _). tr1 = tr S)) (S, S') 
 \<and> ((relation_of A2)\<^sup>f\<^sub>f ;; (\<lambda> (S, S'). tr2 = (tr S))) (S, S') 
 \<and> ((tr_filter tr1 cs) = (tr_filter tr2 cs)))) \<turnstile> 
   (\<lambda> (S, S'). (\<exists> s1 s2. ((\<lambda> (A, A'). (relation_of A1)\<^sup>t\<^sub>f (A, s1)
 \<and> ((relation_of A2)\<^sup>t\<^sub>f (A, s2)));; M_par s1 ns1 s2 ns2 cs) (S, S')))))"
apply (unfold Par_def)
apply (rule action_of_inverse)
apply (rule Par_is_action)
done

lemma mono_Par: "mono (\<lambda>Q. P \<lbrakk> ns1 | cs | ns2 \<rbrakk> Q)"
  apply (auto simp: mono_def less_eq_action ref_def relation_of_Par design_defs fun_eq_iff rp_defs
              split: cond_splits)
  apply (auto simp: rp_defs dest: relation_of_spec_f_f[simplified] relation_of_spec_t_f[simplified])
  apply (erule_tac x="tr ba" in allE, auto)
  apply (erule notE)
  apply (auto dest: relation_of_spec_f_f relation_of_spec_t_f)
done


subsection \<open>Local parallel block\<close>

definition
ParLoc::"'\<sigma> \<Rightarrow> ('\<sigma> \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>) \<Rightarrow> ('\<theta>::ev_eq, '\<sigma>) action \<Rightarrow> '\<theta> set \<Rightarrow> '\<sigma> \<Rightarrow> ('\<sigma> \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>) \<Rightarrow> ('\<theta>,'\<sigma>) action \<Rightarrow> ('\<theta>,'\<sigma>) action"
                                        ("'(()par _ | _ \<bullet> _ ') \<lbrakk> _ \<rbrakk> '(()par _ | _ \<bullet> _ ')")
where 
"(par s1 | ns1 \<bullet> P) \<lbrakk> cs \<rbrakk> (par s2 | ns2 \<bullet> Q) \<equiv> ((rd_assign s1)`;`P) \<lbrakk> ns1 | cs | ns2 \<rbrakk> ((rd_assign s2)`;` Q)"



subsection \<open>Assignment\<close>

definition ASSIGN::"('v, '\<sigma>) var_list \<Rightarrow> ('\<sigma> \<Rightarrow> 'v) \<Rightarrow> ('\<theta>::ev_eq, '\<sigma>) action" where
"ASSIGN x e \<equiv> action_of (R (true \<turnstile> (\<lambda> (S, S'). tr S' = tr S \<and> \<not>wait S' \<and> 
                                 (more S' = (update x (\<lambda>_. (e (more S)))) (more S)))))"

syntax "_assign"::"id \<Rightarrow> ('\<sigma> \<Rightarrow> 'v) \<Rightarrow> ('\<theta>, '\<sigma>) action"  ("_ `:=` _")
translations "y `:=` vv" => "CONST ASSIGN (VAR y) vv"

lemma Assign_is_action: 
"(R (true \<turnstile> (\<lambda> (S, S'). tr S' = tr S \<and> \<not>wait S' \<and> 
                (more S' = (update x (\<lambda>_. (e (more S)))) (more S))))) \<in> {p. is_CSP_process p}"
apply (simp)
apply (rule rd_is_CSP)
apply (blast)
done

lemmas Assign_is_CSP = Assign_is_action[simplified]

lemma relation_of_Assign:
"relation_of (ASSIGN x e) = (R (true \<turnstile> (\<lambda> (S, S'). tr S' = tr S \<and> \<not>wait S' \<and> 
                                   (more S' = (update x (\<lambda>_. (e (more S)))) (more S)))))"
by (simp add: ASSIGN_def action_of_inverse Assign_is_CSP)

lemma Assign_is_state_update_before: "ASSIGN x e = state_update_before (\<lambda> (s, s') . s' = (update x (\<lambda>_. (e s))) s) Skip"
apply (subst relation_of_inject[symmetric])
apply (auto simp: relation_of_Assign relation_of_state_update_before relation_of_Skip rp_defs fun_eq_iff
                  Pre_def update_def design_defs)
apply (split cond_splits, simp_all)+
apply (rule_tac b=b in comp_intro)
apply (split cond_splits, simp_all)+
apply (rule_tac b=b in comp_intro)
apply (split cond_splits, simp_all)+
defer
apply (split cond_splits, simp_all)+
prefer 3
apply (split cond_splits, simp_all)+
apply (auto simp add: prefix_def)
done


subsection \<open>Variable scope\<close>

definition Var::"('v, '\<sigma>) var_list \<Rightarrow>('\<theta>, '\<sigma>) action \<Rightarrow> ('\<theta>::ev_eq,'\<sigma>) action" where
"Var v A \<equiv> action_of(
     (R(true \<turnstile> (\<lambda> (A, A'). \<exists> a. tr A' = tr A \<and> \<not>wait A' \<and> more A' = (increase v a (more A)))));; 
     (relation_of A;;
     (R(true \<turnstile> (\<lambda> (A, A').  tr A' = tr A \<and> \<not>wait A' \<and> more A' = (decrease v (more A)))))))"

syntax "_var"::"idt \<Rightarrow> ('\<theta>, '\<sigma>) action \<Rightarrow> ('\<theta>, '\<sigma>) action" ("var _ \<bullet> _" [1000] 999)
translations "var y \<bullet> Act" => "CONST Var (VAR_LIST y) Act"

lemma Var_is_action:
"((R(true \<turnstile> (\<lambda> (A, A'). \<exists> a. tr A' = tr A \<and> \<not>wait A' \<and> more A' = (increase v a (more A)))));; 
     (relation_of A;;
     (R(true \<turnstile> (\<lambda> (A, A').  tr A' = tr A \<and> \<not>wait A' \<and> more A' = (decrease v (more A))))))) \<in> {p. is_CSP_process p}"
  apply (simp)
  apply (rule seq_CSP)
  prefer 3
  apply (rule seq_CSP)
  apply (auto simp: relation_of_CSP1 relation_of_R)
  apply (rule rd_is_CSP)
  apply (auto simp: csp_defs rp_defs design_defs fun_eq_iff prefix_def increase_def decrease_def
               split: cond_splits)
done

lemmas Var_is_CSP = Var_is_action[simplified]

lemma relation_of_Var:
"relation_of (Var v A) = 
    ((R(true \<turnstile> (\<lambda> (A, A'). \<exists> a. tr A' = tr A \<and> \<not>wait A' \<and> more A' = (increase v a (more A)))));; 
     (relation_of A;;
     (R(true \<turnstile> (\<lambda> (A, A').  tr A' = tr A \<and> \<not>wait A' \<and> more A' = (decrease v (more A)))))))"
apply (simp only: Var_def)
apply (rule action_of_inverse)
apply (rule Var_is_action)
done


lemma mono_Var : "mono (Var x)"
  by (auto simp: mono_def less_eq_action ref_def relation_of_Var)



definition Let::"('v, '\<sigma>) var_list \<Rightarrow>('\<theta>, '\<sigma>) action \<Rightarrow> ('\<theta>::ev_eq,'\<sigma>) action" where
"Let v A \<equiv> action_of((relation_of A;;
     (R(true \<turnstile> (\<lambda> (A, A').  tr A' = tr A \<and> \<not>wait A' \<and> more A' = (decrease v (more A)))))))"

syntax "_let"::"idt \<Rightarrow> ('\<theta>, '\<sigma>) action \<Rightarrow> ('\<theta>, '\<sigma>) action" ("let _ \<bullet> _" [1000] 999)
translations "let y \<bullet> Act" => "CONST Let (VAR_LIST y) Act"

lemma Let_is_action:
"(relation_of A;;
     (R(true \<turnstile> (\<lambda> (A, A').  tr A' = tr A \<and> \<not>wait A' \<and> more A' = (decrease v (more A)))))) \<in> {p. is_CSP_process p}"
  apply (simp)
  apply (rule seq_CSP)
  apply (auto simp: relation_of_CSP1 relation_of_R)
  apply (rule rd_is_CSP)
  apply (auto)
done

lemmas Let_is_CSP = Let_is_action[simplified]

lemma relation_of_Let:
"relation_of (Let v A) = 
    (relation_of A;;
     (R(true \<turnstile> (\<lambda> (A, A').  tr A' = tr A \<and> \<not>wait A' \<and> more A' = (decrease v (more A))))))"
by (simp add: Let_def action_of_inverse Let_is_CSP)

lemma mono_Let : "mono (Let x)"
  by (auto simp: mono_def less_eq_action ref_def relation_of_Let)


lemma Var_is_state_update_before: "Var v A = state_update_before (\<lambda> (s, s'). \<exists> a. s' = increase v a s) (Let v A)"
apply (subst relation_of_inject[symmetric])
apply (auto simp: relation_of_Var relation_of_Let relation_of_state_update_before relation_of_Skip fun_eq_iff)
apply (auto simp: rp_defs fun_eq_iff Pre_def design_defs)
apply (split cond_splits, simp_all)+
apply (rule_tac b=ab in comp_intro)
apply (split cond_splits, simp_all)+
apply (rule_tac b=bb in comp_intro, simp_all)
apply (split cond_splits, simp_all)+
apply (rule_tac b=ab in comp_intro)
apply (split cond_splits, simp_all)+
apply (rule_tac b=bb in comp_intro, simp_all)
apply (split cond_splits, simp_all)+
apply (rule_tac b=ab in comp_intro)
apply (split cond_splits, simp_all)+ defer
apply (rule_tac b=bb in comp_intro, simp_all)
apply (split cond_splits, simp_all)+
apply (rule_tac b=ab in comp_intro)
apply (split cond_splits, simp_all)+ defer
apply (rule_tac b=bb in comp_intro, simp_all)
apply (split cond_splits, simp_all)+
apply (rule_tac b=ab in comp_intro)
apply (split cond_splits, simp_all)+
apply (rule_tac b=bb in comp_intro, simp_all)
apply (split cond_splits, simp_all)+
apply (rule_tac b=ab in comp_intro)
apply (split cond_splits, simp_all)+
apply (rule_tac b=bb in comp_intro, simp_all)
apply (split cond_splits, simp_all)+
apply (rule_tac b=ab in comp_intro)
apply (split cond_splits, simp_all)+
apply (case_tac "\<exists>A' a. A' = increase v a (alpha_rp.more aa)", simp_all add: true_def)
apply (erule_tac x="increase v a (alpha_rp.more aa)" in allE)
apply (erule_tac x="a" in allE, simp)
apply (rule_tac b=bb in comp_intro, simp_all)
apply (split cond_splits, simp_all)+
apply (rule_tac b=ab in comp_intro)
apply (split cond_splits, simp_all)+
apply (case_tac "\<exists>A' a. A' = increase v a (alpha_rp.more aa)", simp_all add: true_def)
apply (erule_tac x="increase v a (alpha_rp.more aa)" in allE)
apply (erule_tac x="a" in allE, simp)
apply (rule_tac b=bb in comp_intro, simp_all)
apply (split cond_splits, simp_all)+
done


lemma Let_is_state_update_after: "Let v A = state_update_after (\<lambda> (s, s'). s' = decrease v s) A"
apply (subst relation_of_inject[symmetric])
apply (auto simp: relation_of_Var relation_of_Let relation_of_state_update_after relation_of_Skip fun_eq_iff)
apply (auto simp: rp_defs fun_eq_iff Pre_def design_defs)
apply (auto split: cond_splits)
done


subsection \<open>Guarded action\<close>

definition Guard::"'\<sigma> predicate \<Rightarrow> ('\<theta>::ev_eq, '\<sigma>) action \<Rightarrow> ('\<theta>, '\<sigma>) action" ("_ `&` _")
where "g `&` P \<equiv> action_of(R (((g o more o fst) \<longrightarrow> \<not> ((relation_of P)\<^sup>f\<^sub>f)) \<turnstile> 
                             (((g o more o fst) \<and> ((relation_of P)\<^sup>t\<^sub>f)) \<or> 
                         ((\<not>(g o more o fst)) \<and> (\<lambda> (A, A'). tr A' = tr A \<and> wait A')))))"

lemma Guard_is_action: 
"(R ( ((g o more o fst) \<longrightarrow> \<not> ((relation_of P)\<^sup>f\<^sub>f)) \<turnstile> 
                (((g o more o fst) \<and> ((relation_of P)\<^sup>t\<^sub>f)) \<or> 
                 ((\<not>(g o more o fst)) \<and> (\<lambda> (A, A'). tr A' = tr A \<and> wait A'))))) \<in> {p. is_CSP_process p}"
  by (auto simp add: spec_def intro: rd_is_CSP)

lemmas Guard_is_CSP = Guard_is_action[simplified]

lemma relation_of_Guard:
"relation_of (g `&` P) = (R (((g o more o fst) \<longrightarrow>  \<not> ((relation_of P)\<^sup>f\<^sub>f)) \<turnstile> 
                             (((g o more o fst) \<and> ((relation_of P)\<^sup>t\<^sub>f)) \<or>
                          ((\<not>(g o more o fst)) \<and> (\<lambda> (A, A'). tr A' = tr A \<and> wait A')))))"
  apply (unfold Guard_def)
  apply (subst action_of_inverse)
  apply (simp_all only: Guard_is_action)
done

lemma mono_Guard : "mono (Guard g)"
  apply (auto simp: mono_def less_eq_action ref_def rp_defs design_defs relation_of_Guard 
                split: cond_splits)
  apply (auto dest: relation_of_spec_f_f relation_of_spec_t_f)
done

lemma false_Guard: "false `&` P = Stop"
apply (subst relation_of_inject[symmetric])
apply (subst relation_of_Stop)
apply (subst relation_of_Guard)
apply (simp add: fun_eq_iff utp_defs csp_defs design_defs rp_defs)
done

lemma false_Guard1: "\<And> a b. g (alpha_rp.more a) = False \<Longrightarrow> 
                                (relation_of (g `&` P)) (a, b) = (relation_of Stop) (a, b)"
apply (subst relation_of_Guard)
apply (subst relation_of_Stop)
apply (auto simp: fun_eq_iff csp_defs design_defs rp_defs split: cond_splits)
done

lemma true_Guard: "true `&` P = P"
apply (subst relation_of_inject[symmetric])
apply (subst relation_of_Guard)
apply (subst CSP_is_rd[OF relation_of_CSP]) back back
apply (simp add: fun_eq_iff utp_defs csp_defs design_defs rp_defs)
done

lemma true_Guard1: "\<And> a b. g (alpha_rp.more a) = True \<Longrightarrow> 
                                     (relation_of (g `&` P)) (a, b) = (relation_of P) (a, b)"
apply (subst relation_of_Guard)
apply (subst CSP_is_rd[OF relation_of_CSP]) back back
apply (auto simp: fun_eq_iff csp_defs design_defs rp_defs split: cond_splits)
done

lemma Guard_is_state_update_before: "g `&` P = state_update_before (\<lambda> (s, s') . g s) P"
apply (subst relation_of_inject[symmetric])
apply (auto simp: relation_of_Guard relation_of_state_update_before relation_of_Skip rp_defs fun_eq_iff
                  Pre_def update_def design_defs)
apply (rule_tac b=a in comp_intro)
apply (split cond_splits, simp_all)+
apply (subst CSP_is_rd)
apply (simp_all add: relation_of_CSP rp_defs design_defs fun_eq_iff)
apply (split cond_splits, simp_all)+
apply (auto)
apply (subst (asm) CSP_is_rd)
apply (simp_all add: relation_of_CSP rp_defs design_defs fun_eq_iff)
apply (split cond_splits, simp_all)+
apply (subst (asm) CSP_is_rd)
apply (simp_all add: relation_of_CSP rp_defs design_defs fun_eq_iff)
apply (split cond_splits, simp_all)+
apply (subst CSP_is_rd)
apply (simp_all add: relation_of_CSP rp_defs design_defs fun_eq_iff)
apply (split cond_splits, simp_all)+
apply (subst CSP_is_rd)
apply (simp_all add: relation_of_CSP rp_defs design_defs fun_eq_iff)
apply (split cond_splits, simp_all)+
apply (auto) defer
apply (split cond_splits, simp_all)+
apply (subst (asm) CSP_is_rd)
apply (simp_all add: relation_of_CSP rp_defs design_defs fun_eq_iff)
apply (split cond_splits, simp_all)+ defer
apply (rule disjI1) defer
apply (case_tac "g (alpha_rp.more aa)", simp_all)
apply (rule)+
apply (simp add: impl_def) defer
oops

subsection \<open>Prefixed action\<close>

definition do where
"do e \<equiv> (\<lambda>(A, A'). tr A = tr A' \<and> (e (more A)) \<notin> (ref A')) \<triangleleft> wait o snd \<triangleright> 
         (\<lambda>(A, A'). tr A' = (tr A @[(e (more A))]))"

definition do_I::"('\<sigma> \<Rightarrow>'\<theta>) \<Rightarrow> '\<theta> set \<Rightarrow> ('\<theta>, '\<sigma>) relation_rp"
where "do_I c S \<equiv>  ((\<lambda>(A, A'). tr A = tr A' & S \<inter> (ref A') = {})
                                \<triangleleft> wait o snd \<triangleright> 
  (\<lambda>(A, A'). hd (tr A' - tr A) \<in> S & (c (more A) = (last (tr A')))))"

(*
definition do_I::"('v \<Rightarrow> '\<theta>) \<Rightarrow> ('v, '\<sigma>) var_list \<Rightarrow> 'v set \<Rightarrow> ('\<theta>, '\<sigma>) relation_rp"
where "do_I c x P \<equiv>  ((\<lambda>(A, A'). tr A = tr A' \<and> (c`P) \<inter> (ref A') = {})
                                \<triangleleft> wait o fst \<triangleright> 
  (\<lambda>(A, A'). hd (tr A' - tr A) \<in> (c`P) \<and> (c (select x (more A)) = (last (tr A')))))"
*)


definition
iPrefix::"('\<sigma> \<Rightarrow>'\<theta>::ev_eq) \<Rightarrow> ('\<sigma> relation) \<Rightarrow> (('\<theta>, '\<sigma>) action \<Rightarrow> ('\<theta>, '\<sigma>) action) \<Rightarrow> ('\<sigma> \<Rightarrow> '\<theta> set) \<Rightarrow> ('\<theta>, '\<sigma>) action \<Rightarrow> ('\<theta>, '\<sigma>) action" where
"iPrefix c i j S P \<equiv> action_of(R(true \<turnstile> (\<lambda> (A, A'). (do_I c (S (more A))) (A, A') & more A' = more A)))`;` P"

definition
oPrefix::"('\<sigma> \<Rightarrow>'\<theta>) \<Rightarrow> ('\<theta>::ev_eq, '\<sigma>) action \<Rightarrow> ('\<theta>, '\<sigma>) action" where
"oPrefix c P \<equiv> action_of(R(true \<turnstile> (do c) \<and> (\<lambda> (A, A'). more A' = more A)))`;` P"

definition Prefix0::"'\<theta> \<Rightarrow> ('\<theta>::ev_eq, '\<sigma>) action \<Rightarrow> ('\<theta>, '\<sigma>) action" where
"Prefix0 c P \<equiv> action_of(R(true \<turnstile> (do (\<lambda> _. c)) \<and> (\<lambda> (A, A'). more A' = more A)))`;` P"

definition 
read::"('v \<Rightarrow> '\<theta>) \<Rightarrow> ('v, '\<sigma>) var_list \<Rightarrow> ('\<theta>::ev_eq, '\<sigma>) action \<Rightarrow> ('\<theta>, '\<sigma>) action"
where  "read c x P  \<equiv> iPrefix (\<lambda> A. c (select x A)) (\<lambda> (s, s'). \<exists> a. s' = increase x a s) (Let x) (\<lambda>_. range c) P"

definition 
read1::"('v \<Rightarrow> '\<theta>) \<Rightarrow> ('v, '\<sigma>) var_list \<Rightarrow> ('\<sigma> \<Rightarrow> 'v set) \<Rightarrow> ('\<theta>::ev_eq, '\<sigma>) action \<Rightarrow> ('\<theta>, '\<sigma>) action"
where  "read1 c x S P  \<equiv> iPrefix (\<lambda> A. c (select x A)) (\<lambda> (s, s'). \<exists> a. a\<in>(S s) & s' = increase x a s) (Let x) (\<lambda>s. c`(S s)) P"

definition 
write1::"('v \<Rightarrow> '\<theta>) \<Rightarrow> ('\<sigma> \<Rightarrow> 'v) \<Rightarrow> ('\<theta>::ev_eq, '\<sigma>) action \<Rightarrow> ('\<theta>, '\<sigma>) action"
where "write1 c a P \<equiv> oPrefix (\<lambda> A. c (a A)) P"

definition 
write0::"'\<theta> \<Rightarrow> ('\<theta>::ev_eq, '\<sigma>) action \<Rightarrow> ('\<theta>, '\<sigma>) action" 
where "write0 c P \<equiv> Prefix0 c P"

syntax
"_read"  ::"[id, pttrn, ('\<theta>, '\<sigma>) action] => ('\<theta>, '\<sigma>) action" ("(_`?`_ /\<rightarrow> _)")
"_readS" ::"[id, pttrn, '\<theta> set,('\<theta>, '\<sigma>) action] => ('\<theta>, '\<sigma>) action" ("(_`?`_`:`_ /\<rightarrow> _)")
"_readSS" ::"[id, pttrn, '\<sigma> => '\<theta> set,('\<theta>, '\<sigma>) action] => ('\<theta>, '\<sigma>) action" ("(_`?`_`\<in>`_ /\<rightarrow> _)")
"_write" ::"[id, '\<sigma>, ('\<theta>, '\<sigma>) action] => ('\<theta>, '\<sigma>) action" ("(_`!`_ /\<rightarrow> _)")
"_writeS"::"['\<theta>, ('\<theta>, '\<sigma>) action] => ('\<theta>, '\<sigma>) action" ("(_ /\<rightarrow> _)")

translations
"_read c p P"    == "CONST read c (VAR_LIST p) P" 
"_readS c p b P" == "CONST read1 c (VAR_LIST p) (\<lambda>_. b) P"
"_readSS c p b P" == "CONST read1 c (VAR_LIST p) b P"
"_write c p P"   == "CONST write1 c p P"
"_writeS a P"    == "CONST write0 a P"

lemma Prefix_is_action:
"(R(true \<turnstile> (do c) \<and> (\<lambda> (A, A'). more A' = more A))) \<in> {p. is_CSP_process p}"
by (auto intro: rd_is_CSP)

lemma Prefix1_is_action:
"(R(true \<turnstile> \<lambda>(A, A'). do_I c (S (alpha_rp.more A)) (A, A') \<and> alpha_rp.more A' = alpha_rp.more A)) \<in> {p. is_CSP_process p}"
by (auto intro: rd_is_CSP)

lemma Prefix0_is_action:
"(R(true \<turnstile> (do c) \<and> (\<lambda> (A, A'). more A' = more A))) \<in> {p. is_CSP_process p}"
by (auto intro: rd_is_CSP)

lemmas Prefix_is_CSP = Prefix_is_action[simplified]

lemmas Prefix1_is_CSP = Prefix1_is_action[simplified]

lemmas Prefix0_is_CSP = Prefix0_is_action[simplified]

lemma relation_of_iPrefix:
"relation_of (iPrefix c i j S P) = 
((R(true \<turnstile> (\<lambda> (A, A'). (do_I c (S (more A))) (A, A') & more A' = more A)));; relation_of P)"
by (simp add: iPrefix_def relation_of_Seq action_of_inverse Prefix1_is_CSP)

lemma relation_of_oPrefix:
"relation_of (oPrefix c P) = 
((R(true \<turnstile> (do c) \<and> (\<lambda> (A, A'). more A' = more A)));; relation_of P)"
by (simp add: oPrefix_def relation_of_Seq action_of_inverse Prefix_is_CSP)


lemma relation_of_Prefix0:
"relation_of (Prefix0 c P) = 
((R(true \<turnstile> (do (\<lambda> _. c)) \<and> (\<lambda> (A, A'). more A' = more A)));; relation_of P)"
by (simp add: Prefix0_def relation_of_Seq action_of_inverse Prefix0_is_CSP)

lemma mono_iPrefix : "mono (iPrefix c i j s)"
by (auto simp: mono_def less_eq_action ref_def relation_of_iPrefix)

lemma mono_oPrefix : "mono (oPrefix c)"
by (auto simp: mono_def less_eq_action ref_def relation_of_oPrefix)

lemma mono_Prefix0 : "mono(Prefix0 c)"
by (auto simp: mono_def less_eq_action ref_def relation_of_Prefix0)

subsection \<open>Hiding\<close>

definition Hide::"('\<theta>::ev_eq, '\<sigma>) action \<Rightarrow> '\<theta> set \<Rightarrow> ('\<theta>, '\<sigma>) action" (infixl "\\" 18) where
"P \\ cs \<equiv> action_of(R(\<lambda>(S, S'). \<exists> s. (diff_tr S' S) = (tr_filter (s - (tr S)) cs) &
             (relation_of P)(S, S'\<lparr>tr := s, ref := (ref S') \<union> cs \<rparr>));; (relation_of Skip))"


definition 
"hid P cs == (R(\<lambda>(S, S'). \<exists> s. (diff_tr S' S) = (tr_filter (s - (tr S)) cs) & (relation_of P)(S, S'\<lparr>tr := s, ref := (ref S') \<union> cs \<rparr>)) ;; (relation_of Skip))"

lemma hid_is_R: "hid P cs is R healthy"
apply (simp add: hid_def)
apply (rule seq_R)
apply (simp add: Healthy_def R_idem2)
apply (rule CSP_is_R)
apply (rule relation_of_CSP)
done

lemma hid_Skip: "hid P cs = (hid P cs ;; relation_of Skip)"
by (simp add: hid_def comp_assoc[symmetric] Skip_comp_absorb)

lemma hid_is_CSP1: "hid P cs is CSP1 healthy"
apply (auto simp: design_defs CSP1_def hid_def rp_defs fun_eq_iff)
apply (rule_tac b="a" in comp_intro)
apply (clarsimp split: cond_splits)
apply (subst CSP_is_rd, auto simp: rp_defs relation_of_CSP design_defs fun_eq_iff split: cond_splits)
apply (auto simp: diff_tr_def relation_of_Skip rp_defs design_defs true_def split: cond_splits)
apply (rule_tac x="[]" in exI, auto)
done

lemma hid_is_CSP2: "hid P cs is CSP2 healthy"
apply (simp add: hid_def)
apply (rule seq_CSP2)
apply (rule CSP_is_CSP2)
apply (rule relation_of_CSP)
done

lemma hid_is_CSP: "is_CSP_process (hid P cs)"
by (auto simp: csp_defs hid_is_CSP1 hid_is_R hid_is_CSP2)

lemma Hide_is_action: 
"(R(\<lambda>(S, S'). \<exists> s. (diff_tr S' S) = (tr_filter (s - (tr S)) cs) &
   (relation_of P)(S, S'\<lparr>tr := s, ref := (ref S') \<union> cs \<rparr>));; (relation_of Skip)) \<in> {p. is_CSP_process p}"
by (simp add: hid_is_CSP[simplified hid_def])

lemmas Hide_is_CSP = Hide_is_action[simplified]

lemma relation_of_Hide:
"relation_of (P \\ cs) = (R(\<lambda>(S, S'). \<exists> s. (diff_tr S' S) = (tr_filter (s - (tr S)) cs)
        & (relation_of P)(S, S'\<lparr>tr :=s, ref := (ref S') \<union> cs \<rparr>));; (relation_of Skip))"
  by (simp add: Hide_def action_of_inverse Hide_is_CSP)

lemma mono_Hide : "mono(\<lambda> P. P \\ cs)"
by (auto simp: mono_def less_eq_action ref_def prefix_def utp_defs relation_of_Hide rp_defs)

subsection \<open>Recursion\<close>

text \<open>To represent the recursion operator "\<open>\<mu>\<close>" over actions, we use the
universal least fix-point operator "@{const lfp}" defined in the HOL library for lattices. 
The operator "@{const lfp}" is inherited from the "Complete Lattice class" under some conditions. 
All theorems defined over this operator can be reused.\<close>

text \<open>In the @{theory Circus.Circus_Actions} theory, we presented the proof that Circus actions 
form a complete lattice. The Knaster-Tarski Theorem (in its simplest formulation) states 
that any monotone function on a complete lattice has a least fixed-point. 
This is a consequence of the basic boundary properties of the complete lattice operations. 
Instantiating the complete lattice class allows one to inherit these properties with the 
definition of the least fixed-point for monotonic functions over Circus actions.
\<close>

syntax "_MU"::"[idt, idt \<Rightarrow> ('\<theta>, '\<sigma>) action] \<Rightarrow> ('\<theta>, '\<sigma>) action"  ("\<mu> _ \<bullet> _")
translations "_MU X P" == "CONST lfp (\<lambda> X. P)"


(*<*)
text\<open>Instead fo the following:\<close>
lemma is_action_REP_Mu:
  shows "is_CSP_process (relation_of (lfp P))"
oops 

text\<open>... we refer to the proof of @{thm Sup_is_action} and its 
analogue who capture the essence of this proof at the level of the
type instantiation.\<close>

text\<open>Monotonicity: STATUS: probably critical.  Does not seem to be necessary for 
parameterless Circus.\<close>
lemma mono_Mu:
  assumes A : "mono P"
  and     B : "\<And> X. mono (P X)"
  shows  "mono (lfp P)"
apply (subst lfp_unfold)
apply (auto simp: A B)
done 

term Nat.Suc
(*>*)
end
