section \<open>Circus actions\<close>

theory Circus_Actions
imports HOLCF CSP_Processes
begin

text \<open>In this section, we introduce definitions for Circus actions with 
some useful theorems and lemmas.\<close>

default_sort type

subsection \<open>Definitions\<close>

text \<open>The Circus actions type is defined as the set of all the CSP healthy reactive processes.\<close>

typedef ('\<theta>::"ev_eq",'\<sigma>)  "action" = "{p::('\<theta>,'\<sigma>) relation_rp. is_CSP_process p}"
    morphisms relation_of action_of
proof -
   have "R (false \<turnstile> true) \<in> {p :: ('\<theta>,'\<sigma>) relation_rp. is_CSP_process p}"
        by (auto intro: rd_is_CSP)
   thus ?thesis by auto
qed

print_theorems

text \<open>The type-definition introduces a new type by stating a set. In our case, 
 it is the set of reactive processes that satisfy the healthiness-conditions
 for CSP-processes, isomorphic to the new type.
 Technically, this construct introduces two constants (morphisms) definitions $relation\_of$
 and $action\_of$ as well as the usual axioms expressing the bijection @{thm relation_of_inverse}
 and @{thm action_of_inverse}.\<close>

lemma relation_of_CSP: "is_CSP_process (relation_of x)"
proof -
have "(relation_of x) :{p. is_CSP_process p}" by (rule relation_of)
then show "is_CSP_process (relation_of x)" ..
qed

lemma relation_of_CSP1: "(relation_of x) is CSP1 healthy"
by (rule CSP_is_CSP1[OF relation_of_CSP])

lemma relation_of_CSP2: "(relation_of x) is CSP2 healthy"
by (rule CSP_is_CSP2[OF relation_of_CSP])

lemma relation_of_R: "(relation_of x) is R healthy"
by (rule CSP_is_R[OF relation_of_CSP])

subsection \<open>Proofs\<close>

text \<open>In the following, Circus actions are proved to be an instance of the $Complete\_Lattice$ class.\<close>

lemma relation_of_spec_f_f: 
"\<forall>a b. (relation_of y \<longrightarrow> relation_of x) (a, b) \<Longrightarrow>
           (relation_of y)\<^sup>f\<^sub>f (a\<lparr>tr := []\<rparr>, b) \<Longrightarrow>
                      (relation_of x)\<^sup>f\<^sub>f (a\<lparr>tr := []\<rparr>, b)"
by (auto simp: spec_def)

lemma relation_of_spec_t_f: 
"\<forall>a b. (relation_of y \<longrightarrow> relation_of x) (a, b) \<Longrightarrow>
           (relation_of y)\<^sup>t\<^sub>f (a\<lparr>tr := []\<rparr>, b) \<Longrightarrow>
                     (relation_of x)\<^sup>t\<^sub>f (a\<lparr>tr := []\<rparr>, b)"
by (auto simp: spec_def)

instantiation "action"::(ev_eq, type) below
begin
definition ref_def : "P \<sqsubseteq> Q \<equiv> [(relation_of Q) \<longrightarrow> (relation_of P)]"
instance ..
end

instance "action" :: (ev_eq, type) po
proof
  fix x y z::"('a, 'b) action"
  {
    show "x \<sqsubseteq> x" by (simp add: ref_def utp_defs)
  next
    assume "x \<sqsubseteq> y" and "y \<sqsubseteq> z" then show " x \<sqsubseteq> z"
      by (simp add: ref_def utp_defs)
  next
    assume A:"x \<sqsubseteq> y" and B:"y \<sqsubseteq> x" then show " x = y"
      by (auto simp add: ref_def relation_of_inject[symmetric] fun_eq_iff)
  }
qed

instantiation "action"  ::  (ev_eq, type) lattice
begin

definition inf_action : "(inf P Q \<equiv> action_of ((relation_of P) \<sqinter> (relation_of Q)))"
definition sup_action : "(sup P Q \<equiv> action_of ((relation_of P) \<squnion> (relation_of Q)))"
definition less_eq_action : "(less_eq (P::('a, 'b) action) Q \<equiv> P \<sqsubseteq> Q)"
definition less_action : "(less (P::('a, 'b) action) Q \<equiv> P \<sqsubseteq> Q \<and> \<not> Q \<sqsubseteq> P)"

instance 
proof
  fix x y z::"('a, 'b) action"
  {
    show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
      by (simp add: less_action less_eq_action)
  next
    show "(x \<le> x)" by (simp add: less_eq_action)
  next
    assume "x \<le> y" and "y \<le> z" 
    then show " x \<le> z"
      by (simp add: less_eq_action ref_def utp_defs)
  next
    assume "x \<le> y" and "y \<le> x"
    then show " x = y"
      by (auto simp add: less_eq_action ref_def relation_of_inject[symmetric] utp_defs)
  next
    show "inf x y \<le> x"
      apply (auto simp add: less_eq_action inf_action ref_def
        csp_defs design_defs rp_defs)
      apply (subst action_of_inverse, simp add: Healthy_def)
      apply (insert relation_of_CSP[where x="x"])
      apply (insert relation_of_CSP[where x="y"])
      apply (simp_all add: CSP_join)
      apply (simp add: utp_defs)
      done
  next
    show "inf x y \<le> y"
      apply (auto simp add: less_eq_action inf_action ref_def csp_defs)
      apply (subst action_of_inverse, simp add: Healthy_def)
      apply (insert relation_of_CSP[where x="x"])
      apply (insert relation_of_CSP[where x="y"])
      apply (simp_all add: CSP_join)
      apply (simp add: utp_defs)
      done
  next
    assume "x \<le> y" and "x \<le> z" 
    then show "x \<le> inf y z"
      apply (auto simp add: less_eq_action inf_action ref_def impl_def csp_defs)
      apply (erule_tac x="a" in allE, erule_tac x="a" in allE)
      apply (erule_tac x="b" in allE)+
      apply (subst (asm) action_of_inverse)
      apply (simp add: Healthy_def)
      apply (insert relation_of_CSP[where x="z"])
      apply (insert relation_of_CSP[where x="y"])
      apply (auto simp add: CSP_join)
      done
  next
    show "x \<le> sup x y"
      apply (auto simp add: less_eq_action sup_action ref_def 
         impl_def csp_defs)
      apply (subst (asm) action_of_inverse)
      apply (simp add: Healthy_def)
      apply (insert relation_of_CSP[where x="x"])
      apply (insert relation_of_CSP[where x="y"])
      apply (auto simp add: CSP_meet)
      done
  next
    show "y \<le> sup x y"
      apply (auto simp add: less_eq_action sup_action ref_def
         impl_def csp_defs)
      apply (subst (asm) action_of_inverse)
      apply (simp add: Healthy_def)
      apply (insert relation_of_CSP[where x="x"])
      apply (insert relation_of_CSP[where x="y"])
      apply (auto simp add: CSP_meet)
      done
  next
    assume "y \<le> x" and "z \<le> x"
    then show "sup y z \<le> x"
      apply (auto simp add: less_eq_action sup_action ref_def  impl_def csp_defs)
      apply (erule_tac x="a" in allE)
      apply (erule_tac x="a" in allE)
      apply (erule_tac x="b" in allE)+
      apply (subst action_of_inverse)
      apply (simp add: Healthy_def)
      apply (insert relation_of_CSP[where x="z"])
      apply (insert relation_of_CSP[where x="y"])
      apply (auto simp add: CSP_meet)
      done
  }
qed

end

lemma bot_is_action: "R (false \<turnstile> true) \<in> {p. is_CSP_process p}"
  by (auto intro: rd_is_CSP)

lemma bot_eq_true: "R (false \<turnstile> true) = R true"
  by (auto simp: fun_eq_iff design_defs rp_defs split: cond_splits)

instantiation "action"  ::  (ev_eq, type) bounded_lattice
begin

definition bot_action : "(bot::('a, 'b) action) \<equiv> action_of (R(false \<turnstile> true))"
definition top_action : "(top::('a, 'b) action) \<equiv> action_of (R(true \<turnstile> false))"

instance
proof
  fix x::"('a, 'b) action"
  {
    show "bot \<le> x"
      unfolding bot_action
      apply (auto simp add: less_action less_eq_action ref_def bot_action)
      apply (subst action_of_inverse) apply (rule bot_is_action)
      apply (subst bot_eq_true)
      apply (subst (asm) CSP_is_rd)
      apply (rule relation_of_CSP)
      apply (auto simp add: csp_defs rp_defs fun_eq_iff split: cond_splits)
      done
  next
    show "x \<le> top"
      apply (auto simp add: less_action less_eq_action ref_def top_action)
      apply (subst (asm) action_of_inverse)
      apply (simp)
      apply (rule rd_is_CSP)
      apply auto
      apply (subst action_of_cases[where x=x], simp_all)
      apply (subst action_of_inverse, simp_all)
      apply (subst CSP_is_rd[where P=y], simp_all)
      apply (auto simp: rp_defs design_defs fun_eq_iff split: cond_splits)
      done
  }
qed

end

lemma relation_of_top: "relation_of top = R(true \<turnstile> false)"
  apply (simp add: top_action)
  apply (subst action_of_inverse)
  apply (simp)
  apply (rule rd_is_CSP)
  apply (auto simp add: utp_defs design_defs rp_defs)
  done

lemma relation_of_bot: "relation_of bot = R true"
  apply (simp add: bot_action)
  apply (subst action_of_inverse)
  apply (simp add: bot_is_action[simplified], rule bot_eq_true)
  done

lemma non_emptyE: assumes "A \<noteq> {}" obtains x where "x : A"
  using assms by (auto simp add: ex_in_conv [symmetric])

lemma CSP1_Inf: 
assumes *:"A \<noteq> {}"
shows "(\<Sqinter> relation_of ` A) is CSP1 healthy"
proof -
  have "(\<Sqinter> relation_of ` A) = CSP1 (\<Sqinter> relation_of ` A)"
  proof
    fix P
    note * then
    show "(P \<in> \<Union>{{p. P p} |P. P \<in> relation_of ` A}) = CSP1 (\<lambda>Aa. Aa \<in> \<Union>{{p. P p} |P. P \<in> relation_of ` A}) P"
    apply (intro iffI) 
    apply (simp_all add: csp_defs)
    apply (rule disj_introC, simp)
    apply (erule disj_elim, simp_all)
    apply (cases P, simp_all)
    apply (erule non_emptyE)
    apply (rule_tac x="Collect (relation_of x)" in exI, simp)
    apply (rule conjI)
    apply (rule_tac x="(relation_of x)" in exI, simp)
    apply (subst CSP_is_rd, simp add: relation_of_CSP)
    apply (auto simp add: csp_defs design_defs rp_defs fun_eq_iff split: cond_splits)
    done
  qed
  then show "(\<Sqinter> relation_of ` A) is CSP1 healthy" by (simp add: design_defs)
qed

lemma CSP2_Inf:
assumes *:"A \<noteq> {}"
shows "(\<Sqinter> relation_of ` A) is CSP2 healthy"
proof -
  have "(\<Sqinter> relation_of ` A) = CSP2 (\<Sqinter> relation_of ` A)"
  proof
    fix P
    note * then
    show "(P \<in> \<Union>{{p. P p} |P. P \<in> relation_of ` A}) = CSP2 (\<lambda>Aa. Aa \<in> \<Union>{{p. P p} |P. P \<in> relation_of ` A}) P"
    apply (intro iffI)
    apply (simp_all add: csp_defs)
    apply (cases P, simp_all)
    apply (erule exE)
    apply (rule_tac b=b in comp_intro, simp_all)
    apply (rule_tac x=x in exI, simp)
    apply (erule comp_elim, simp_all)
    apply (erule exE | erule conjE)+
    apply (simp_all)
    apply (rule_tac x="Collect Pa" in exI, simp)
    apply (rule conjI)
    apply (rule_tac x="Pa" in exI, simp)
    apply (erule Set.imageE, simp add: relation_of)
    apply (subst CSP_is_rd, simp add: relation_of_CSP)
    apply (subst (asm) CSP_is_rd, simp add: relation_of_CSP)
    apply (auto simp add: csp_defs rp_defs prefix_def design_defs fun_eq_iff split: cond_splits)
    apply (subgoal_tac "b\<lparr>tr := zs, ok := False\<rparr> = c\<lparr>tr := zs, ok := False\<rparr>", auto)
    apply (subgoal_tac "b\<lparr>tr := zs, ok := False\<rparr> = c\<lparr>tr := zs, ok := False\<rparr>", auto)
    apply (subgoal_tac "b\<lparr>tr := zs, ok := False\<rparr> = c\<lparr>tr := zs, ok := False\<rparr>", auto)
    apply (subgoal_tac "b\<lparr>tr := zs, ok := False\<rparr> = c\<lparr>tr := zs, ok := False\<rparr>", auto)
    apply (subgoal_tac "b\<lparr>tr := zs, ok := False\<rparr> = c\<lparr>tr := zs, ok := False\<rparr>", auto)
    apply (subgoal_tac "b\<lparr>tr := zs, ok := False\<rparr> = c\<lparr>tr := zs, ok := False\<rparr>", auto)
    apply (subgoal_tac "b\<lparr>tr := zs, ok := True\<rparr> = c\<lparr>tr := zs, ok := True\<rparr>", auto)
    apply (subgoal_tac "b\<lparr>tr := zs, ok := True\<rparr> = c\<lparr>tr := zs, ok := True\<rparr>", auto)
    done
  qed
  then show "(\<Sqinter> relation_of ` A) is CSP2 healthy" by (simp add: design_defs)
qed

lemma R_Inf:
assumes *:"A \<noteq> {}"
shows "(\<Sqinter> relation_of ` A) is R healthy"
proof -
  have "(\<Sqinter> relation_of ` A) = R (\<Sqinter> relation_of ` A)"
  proof
    fix P
    show "(P \<in> \<Union>{{p. P p} |P. P \<in> relation_of ` A}) = R (\<lambda>Aa. Aa \<in> \<Union>{{p. P p} |P. P \<in> relation_of ` A}) P"
    apply (cases P, simp_all)
    apply (rule)
    apply (simp_all add: csp_defs rp_defs split: cond_splits)
    apply (erule exE)
    apply (erule exE | erule conjE)+
    apply (simp_all)
    apply (erule Set.imageE, simp add: relation_of)
    apply (subst (asm) CSP_is_rd, simp add: relation_of_CSP)
    apply (simp add: csp_defs prefix_def design_defs rp_defs fun_eq_iff split: cond_splits)
    apply (rule_tac x="x" in exI, simp)
    apply (rule conjI)
    apply (rule_tac x="relation_of xa" in exI, simp)
    apply (subst CSP_is_rd, simp add: relation_of_CSP)
    apply (simp add: csp_defs prefix_def design_defs rp_defs fun_eq_iff split: cond_splits)
    apply (insert *)
    apply (erule non_emptyE)
    apply (rule_tac x="Collect (relation_of x)" in exI, simp)
    apply (rule conjI)
    apply (rule_tac x="(relation_of x)" in exI, simp)
    apply (subst CSP_is_rd, simp add: relation_of_CSP)
    apply (simp add: csp_defs prefix_def design_defs rp_defs fun_eq_iff split: cond_splits)
    apply (erule exE | erule conjE)+
    apply (simp_all)
    apply (erule Set.imageE, simp add: relation_of)
    apply (rule_tac x="x" in exI, simp)
    apply (rule conjI)
    apply (rule_tac x="(relation_of xa)" in exI, simp)
    apply (subst CSP_is_rd, simp add: relation_of_CSP)
    apply (simp add: csp_defs prefix_def design_defs rp_defs fun_eq_iff split: cond_splits)
    apply (subst (asm) CSP_is_rd, simp add: relation_of_CSP)
    apply (simp add: csp_defs prefix_def design_defs rp_defs fun_eq_iff split: cond_splits)
    done
  qed
  then show "(\<Sqinter> relation_of ` A) is R healthy" by (simp add: design_defs)
qed

lemma CSP_Inf: 
  assumes "A \<noteq> {}"
  shows "is_CSP_process (\<Sqinter> relation_of ` A)"
  unfolding is_CSP_process_def 
  using assms CSP1_Inf CSP2_Inf R_Inf 
  by auto

lemma Inf_is_action: "A \<noteq> {} \<Longrightarrow> \<Sqinter> relation_of ` A \<in> {p. is_CSP_process p}"
  by (auto dest!: CSP_Inf)

lemma CSP1_Sup: "A \<noteq> {} \<Longrightarrow> (\<Squnion> relation_of ` A) is CSP1 healthy"
  apply (auto simp add: design_defs csp_defs fun_eq_iff)
  apply (subst CSP_is_rd, simp add: relation_of_CSP)
  apply (simp add: csp_defs prefix_def design_defs rp_defs split: cond_splits)
done

lemma CSP2_Sup: "A \<noteq> {} \<Longrightarrow> (\<Squnion> relation_of ` A) is CSP2 healthy"
  apply (simp add: design_defs csp_defs fun_eq_iff)
  apply (rule allI)+
  apply (rule)
  apply (rule_tac b=b in comp_intro, simp_all)
  apply (erule comp_elim, simp_all)
  apply (rule allI)
  apply (erule_tac x=x in allE)
  apply (rule impI)
  apply (case_tac "(\<exists>P. x = Collect P & P \<in> relation_of ` A)", simp_all)
  apply (erule exE | erule conjE)+
  apply (simp_all)
  apply (erule Set.imageE, simp add: relation_of)
  apply (subst (asm) CSP_is_rd, simp add: relation_of_CSP, subst CSP_is_rd, simp add: relation_of_CSP)
  apply (auto simp add: csp_defs design_defs rp_defs split: cond_splits)
  apply (subgoal_tac "ba\<lparr>tr := tr c - tr aa, ok := False\<rparr> = c\<lparr>tr := tr c - tr aa, ok := False\<rparr>", simp_all)
  apply (subgoal_tac "ba\<lparr>tr := tr c - tr aa, ok := False\<rparr> = c\<lparr>tr := tr c - tr aa, ok := False\<rparr>", simp_all)
  apply (subgoal_tac "ba\<lparr>tr := tr c - tr aa, ok := False\<rparr> = c\<lparr>tr := tr c - tr aa, ok := False\<rparr>", simp_all)
  apply (subgoal_tac "ba\<lparr>tr := tr c - tr aa, ok := False\<rparr> = c\<lparr>tr := tr c - tr aa, ok := False\<rparr>", simp_all)
  apply (subgoal_tac "ba\<lparr>tr := tr c - tr aa, ok := False\<rparr> = c\<lparr>tr := tr c - tr aa, ok := False\<rparr>", simp_all)
  apply (subgoal_tac "ba\<lparr>tr := tr c - tr aa, ok := False\<rparr> = c\<lparr>tr := tr c - tr aa, ok := False\<rparr>", simp_all)
  apply (subgoal_tac "ba\<lparr>tr := tr c - tr aa, ok := True\<rparr> = c\<lparr>tr := tr c - tr aa, ok := True\<rparr>", simp_all)
  apply (subgoal_tac "ba\<lparr>tr := tr c - tr aa, ok := True\<rparr> = c\<lparr>tr := tr c - tr aa, ok := True\<rparr>", simp_all)
done

lemma R_Sup: "A \<noteq> {} \<Longrightarrow> (\<Squnion> relation_of ` A) is R healthy"
  apply (simp add: rp_defs design_defs csp_defs fun_eq_iff)
  apply (rule allI)+
  apply (rule)
  apply (simp split: cond_splits)
  apply (case_tac "wait a", simp_all)
  apply (erule non_emptyE)
  apply (erule_tac x="Collect (relation_of x)" in allE, simp_all)
  apply (case_tac "relation_of x (a, b)", simp_all)
  apply (subst (asm) CSP_is_rd, simp add: relation_of_CSP)
  apply (simp add: csp_defs design_defs rp_defs split: cond_splits)
  apply (erule_tac x="(relation_of x)" in allE, simp_all)
  apply (rule conjI)
  apply (rule allI)
  apply (erule_tac x=x in allE)
  apply (rule impI)
  apply (case_tac "(\<exists>P. x = Collect P & P \<in> relation_of ` A)", simp_all)
  apply (erule exE | erule conjE)+
  apply (simp_all)
  apply (erule Set.imageE, simp add: relation_of)
  apply (subst (asm) CSP_is_rd, simp add: relation_of_CSP, subst CSP_is_rd, simp add: relation_of_CSP)
  apply (simp add: csp_defs design_defs rp_defs split: cond_splits)
  apply (erule non_emptyE)
  apply (erule_tac x="Collect (relation_of x)" in allE, simp_all)
  apply (case_tac "relation_of x (a, b)", simp_all)
  apply (subst (asm) CSP_is_rd, simp add: relation_of_CSP)
  apply (simp add: csp_defs design_defs rp_defs split: cond_splits)
  apply (erule_tac x="(relation_of x)" in allE, simp_all)
  apply (simp split: cond_splits)
  apply (rule allI)
  apply (rule impI)
  apply (erule exE | erule conjE)+
  apply (simp_all)
  apply (erule Set.imageE, simp add: relation_of)
  apply (subst (asm) CSP_is_rd, simp add: relation_of_CSP, subst CSP_is_rd, simp add: relation_of_CSP)
  apply (simp add: csp_defs design_defs rp_defs split: cond_splits)
  apply (rule allI)
  apply (rule impI)
  apply (erule exE | erule conjE)+
  apply (simp_all)
  apply (erule Set.imageE, simp add: relation_of)
  apply (erule_tac x="x" in allE, simp_all)
  apply (case_tac "relation_of xa (a\<lparr>tr := []\<rparr>, b\<lparr>tr := tr b - tr a\<rparr>)", simp_all)
  apply (subst (asm) CSP_is_rd) back back back
  apply (simp add: relation_of_CSP, subst CSP_is_rd, simp add: relation_of_CSP)
  apply (simp add: csp_defs design_defs rp_defs split: cond_splits)
  apply (erule_tac x="P" in allE, simp_all)
done

lemma CSP_Sup: "A \<noteq> {} \<Longrightarrow> is_CSP_process (\<Squnion> relation_of ` A)"
  unfolding is_CSP_process_def using CSP1_Sup CSP2_Sup R_Sup by auto

lemma Sup_is_action: "A \<noteq> {} \<Longrightarrow> \<Squnion> relation_of ` A \<in> {p. is_CSP_process p}"
  by (auto dest!: CSP_Sup)

lemma relation_of_Sup: 
  "A \<noteq> {} \<Longrightarrow> relation_of (action_of \<Squnion> relation_of ` A) = \<Squnion> relation_of ` A"
  by (auto simp: action_of_inverse dest!: Sup_is_action)

instantiation "action"  ::  (ev_eq, type) complete_lattice
begin

definition Sup_action : 
"(Sup (S:: ('a, 'b) action set) \<equiv> if S={} then bot else action_of \<Squnion> (relation_of ` S))"
definition Inf_action : 
"(Inf (S:: ('a, 'b) action set) \<equiv> if S={} then top else action_of \<Sqinter> (relation_of ` S))"

instance
proof 
  fix A::"('a, 'b) action set" and z::"('a, 'b) action"
  {
    fix x::"('a, 'b) action"
    assume "x \<in> A"
    then show "Inf A \<le> x"
      apply (auto simp add: less_action less_eq_action Inf_action ref_def)
      apply (subst (asm) action_of_inverse)
      apply (auto intro: Inf_is_action[simplified])
      done
  } note rule1 = this
  {
    assume *: "\<And>x. x \<in> A \<Longrightarrow> z \<le> x"
    show "z \<le> Inf A"
    proof (cases "A = {}")
      case True
      then show ?thesis by (simp add: Inf_action)
    next
      case False
      show ?thesis
        using *
        apply (auto simp add: Inf_action)
        using \<open>A \<noteq> {}\<close>
        apply (simp add: less_eq_action Inf_action ref_def)
        apply (subst (asm) action_of_inverse)
        apply (subst (asm) ex_in_conv[symmetric])
        apply (erule exE)
        apply (auto intro: Inf_is_action[simplified])
        done
    qed
  }{
    fix x::"('a, 'b) action" 
    assume "x \<in> A"
    then show "x \<le> (Sup A)"
      apply (auto simp add: less_action less_eq_action Sup_action ref_def)
      apply (subst (asm) action_of_inverse)
      apply (auto intro: Sup_is_action[simplified])
      done
  } note rule2 = this
  {
    assume "\<And>x. x \<in> A \<Longrightarrow> x \<le> z"
    then show "Sup A \<le> z"
      apply (auto simp add: Sup_action)
      apply atomize
      apply (case_tac "A = {}", simp_all)
      apply (insert rule2)
      apply (auto simp add: less_action less_eq_action Sup_action ref_def)
      apply (subst (asm) action_of_inverse)
      apply (auto intro: Sup_is_action[simplified])
      apply (subst (asm) action_of_inverse)
      apply (auto intro: Sup_is_action[simplified])
      done
  } 
  { show "Inf ({}::('a, 'b) action set) = top" by(simp add:Inf_action) }
  { show "Sup ({}::('a, 'b) action set) = bot" by(simp add:Sup_action) }
qed

end

end
