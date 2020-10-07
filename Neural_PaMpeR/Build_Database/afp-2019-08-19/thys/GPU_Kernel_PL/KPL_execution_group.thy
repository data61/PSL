section \<open>Execution rules for groups\<close>

theory KPL_execution_group imports 
  KPL_execution_thread
begin

text \<open>Intra-group race detection\<close>
definition group_race 
  :: "lid set \<Rightarrow> (lid \<rightharpoonup> thread_state) \<Rightarrow> bool"
where "group_race T \<gamma> \<equiv> 
  \<exists>j \<in> T. \<exists>k \<in> T. j \<noteq> k \<and> 
  W (the (\<gamma> j)) \<inter> (R (the (\<gamma> k)) \<union> W (the (\<gamma> k))) \<noteq> {}"

text \<open>The constraints for the @{term "merge"} map\<close>
inductive pre_merge 
  :: "lid set \<Rightarrow> (lid \<rightharpoonup> thread_state) \<Rightarrow> nat \<Rightarrow> word \<Rightarrow> bool"
where 
  "\<lbrakk> j \<in> T ; z \<in> W (the (\<gamma> j)) ; dom \<gamma> = T \<rbrakk> \<Longrightarrow>
  pre_merge T \<gamma> z (sh (the (\<gamma> j)) z)"
| "\<lbrakk> \<forall>j \<in> T. z \<notin> W (the (\<gamma> j)) ; dom \<gamma> = T \<rbrakk> \<Longrightarrow> 
  pre_merge T \<gamma> z (sh (the (\<gamma> 0)) z)"

inductive_cases pre_merge_inv [elim!]: "pre_merge P \<gamma> z z'"

text \<open>The @{term "merge"} map maps each nat to the word that 
   satisfies the above constaints. The \<open>merge_is_unique\<close>
   lemma shows that there exists exactly one such word 
   per nat, provided there are no group races.\<close>
definition merge :: "lid set \<Rightarrow> (lid \<rightharpoonup> thread_state) \<Rightarrow> nat \<Rightarrow> word"
where "merge T \<gamma> \<equiv> \<lambda>z. The (pre_merge T \<gamma> z)"

lemma no_races_imp_no_write_overlap: 
  "\<not> (group_race T \<gamma>) \<Longrightarrow> 
  \<forall>i \<in> T. \<forall>j \<in> T. 
  i \<noteq> j \<longrightarrow> W (the (\<gamma> i)) \<inter> W (the (\<gamma> j)) = {}"
unfolding group_race_def 
by blast

lemma merge_is_unique:
  assumes "dom \<gamma> = T"
  assumes "\<not> (group_race T \<gamma>)"
  shows "\<exists>!z'. pre_merge T \<gamma> z z'"
apply (insert assms)
apply (drule no_races_imp_no_write_overlap)
apply (intro allI ex_ex1I)
apply (metis pre_merge.intros)
apply clarify
proof -
  fix z1 z2
  assume a: "\<forall>i\<in>dom \<gamma>. \<forall>j\<in>dom \<gamma>. i \<noteq> j \<longrightarrow> W (the (\<gamma> i)) \<inter> W (the (\<gamma> j)) = {}"
  assume "pre_merge (dom \<gamma>) \<gamma> z z1" 
  and "pre_merge (dom \<gamma>) \<gamma> z z2"
  thus "z1 = z2"
  apply (elim pre_merge_inv)
  apply (rename_tac j1 j2)
  apply (case_tac "j1 = j2")
  apply auto[1]
  apply simp
  apply (subgoal_tac "W (the (\<gamma> j1)) \<inter> W (the (\<gamma> j2)) = {}")
  apply auto[1]
  apply (auto simp add: a)
  done
qed
 
text \<open>The rules of Figure 5, plus an additional rule for
  equality abstraction (Fig 7a), plus an additional rule for
  adversarial abstraction (Fig 7b)\<close>
inductive step_g
  :: "abs_level \<Rightarrow> gid \<Rightarrow> (gid \<rightharpoonup> lid set) \<Rightarrow> (group_state \<times> pred_stmt) \<Rightarrow> group_state option \<Rightarrow> bool"
where
  G_Race:
  "\<lbrakk> \<forall>j \<in> the (T i). step_t a (the (\<gamma> \<^sub>t\<^sub>s j), (s, p)) (the (\<gamma>' \<^sub>t\<^sub>s j)) ; 
    group_race (the (T i)) ((\<gamma>' :: group_state)\<^sub>t\<^sub>s) \<rbrakk>
  \<Longrightarrow> step_g a i T (\<gamma>, (Basic s, p)) None"
| G_Basic:
  "\<lbrakk> \<forall>j \<in> the (T i). step_t a (the (\<gamma> \<^sub>t\<^sub>s j), (s, p)) (the (\<gamma>' \<^sub>t\<^sub>s j)) ; 
    \<not> (group_race (the (T i)) (\<gamma>' \<^sub>t\<^sub>s)) ;
    R_group \<gamma>' = R_group \<gamma> \<union> (\<Union>j \<in> the (T i). ({j} \<times> R (the (\<gamma>' \<^sub>t\<^sub>s j)))) ;
    W_group \<gamma>' = W_group \<gamma> \<union> (\<Union>j \<in> the (T i). ({j} \<times> W (the (\<gamma>' \<^sub>t\<^sub>s j)))) \<rbrakk>
  \<Longrightarrow> step_g a i T (\<gamma>, (Basic s, p)) (Some \<gamma>')"
| G_No_Op:
  "\<forall>j \<in> the (T i). \<not> (eval_bool p (the (\<gamma> \<^sub>t\<^sub>s j)))
  \<Longrightarrow> step_g a i T (\<gamma>, (Barrier, p)) (Some \<gamma>)"
| G_Divergence:
  "\<lbrakk> j \<noteq> k ; j \<in> the (T i) ; k \<in> the (T i) ;
   eval_bool p (the (\<gamma> \<^sub>t\<^sub>s j)) ; \<not> (eval_bool p (the (\<gamma> \<^sub>t\<^sub>s k))) \<rbrakk>
  \<Longrightarrow> step_g a i T (\<gamma>, (Barrier, p)) None"
| G_Sync:
  "\<lbrakk> \<forall>j \<in> the (T i). eval_bool p (the (\<gamma> \<^sub>t\<^sub>s j)) ;
    \<forall>j \<in> the (T i). the (\<gamma>' \<^sub>t\<^sub>s j) = (the (\<gamma> \<^sub>t\<^sub>s j)) (| 
    sh := merge P (\<gamma> \<^sub>t\<^sub>s), R := {}, W := {} |) \<rbrakk> 
  \<Longrightarrow> step_g No_Abst i T (\<gamma>, (Barrier, p)) (Some \<gamma>')"
| G_Sync_Eq:
  "\<lbrakk> \<forall>j \<in> the (T i). eval_bool p (the (\<gamma> \<^sub>t\<^sub>s j)) ;
    \<forall>j \<in> the (T i). the (\<gamma>' \<^sub>t\<^sub>s j) = (the (\<gamma> \<^sub>t\<^sub>s j)) (| 
    sh := sh', R := {}, W := {} |) \<rbrakk> 
  \<Longrightarrow> step_g Eq_Abst i T (\<gamma>, (Barrier, p)) (Some \<gamma>')"
| G_Sync_Adv:
  "\<lbrakk> \<forall>j \<in> the (T i). eval_bool p (the (\<gamma> \<^sub>t\<^sub>s j)) ;
    \<forall>j \<in> the (T i). \<exists>sh'. the (\<gamma>' \<^sub>t\<^sub>s j) = (the (\<gamma> \<^sub>t\<^sub>s j)) (| 
    sh := sh', R := {}, W := {} |) \<rbrakk> 
  \<Longrightarrow> step_g Adv_Abst i T (\<gamma>, (Barrier, p)) (Some \<gamma>')"

text \<open>Rephrasing \<open>G_No_Op\<close> to make it more usable\<close>
lemma G_No_Op_helper:
  "\<lbrakk> \<forall>j \<in> the (T i). \<not> (eval_bool p (the (\<gamma> \<^sub>t\<^sub>s j))) ; \<gamma> = \<gamma>' \<rbrakk>
  \<Longrightarrow> step_g a i T (\<gamma>, (Barrier, p)) (Some \<gamma>')"
by (simp add: step_g.G_No_Op)


end
