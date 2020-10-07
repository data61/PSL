section \<open>Execution rules for threads\<close>

theory KPL_execution_thread imports 
  KPL_state
begin

text \<open>Evaluate a local expression down to a word\<close>
fun eval_word :: "local_expr \<Rightarrow> thread_state \<Rightarrow> word"
where
  "eval_word (Loc (Var v)) \<tau> = l \<tau> (Inl v)"
(* eval_word (Loc (Name n)) \<tau> = undefined *)
| "eval_word Lid \<tau> = l \<tau> LID"
| "eval_word Gid \<tau> = l \<tau> GID"
| "eval_word eTrue \<tau> = 1"
| "eval_word (e1 \<and>* e2) \<tau> = 
  (eval_word e1 \<tau> * eval_word e2 \<tau>)"
| "eval_word (\<not>* e) \<tau> = (if eval_word e \<tau> = 0 then 1 else 0)"

text \<open>Evaluate a local expression down to a boolean\<close>
fun eval_bool :: "local_expr \<Rightarrow> thread_state \<Rightarrow> bool"
where
  "eval_bool e \<tau> = (eval_word e \<tau> \<noteq> 0)"

text \<open>Abstraction level: none, equality abstraction, or adversarial abstraction\<close>
datatype abs_level = No_Abst | Eq_Abst | Adv_Abst

text \<open>The rules of Figure 4, plus two additional rules 
  for adversarial abstraction (Fig 7b)\<close>
inductive step_t 
  :: "abs_level \<Rightarrow> (thread_state \<times> pred_basic_stmt) \<Rightarrow> thread_state \<Rightarrow> bool"  
where
  T_Disabled: 
  "\<not> (eval_bool p \<tau>) \<Longrightarrow> step_t a (\<tau>, (b, p)) \<tau>"
| T_Assign: 
  "\<lbrakk> eval_bool p \<tau> ; l' = (l \<tau>) (Inl v := eval_word e \<tau>) \<rbrakk> 
  \<Longrightarrow> step_t a (\<tau>, (Assign (Var v) e, p)) (\<tau> (| l := l' |))"
| T_Read: 
  "\<lbrakk> eval_bool p \<tau> ; l' = (l \<tau>) (Inl v := sh \<tau> (eval_word e \<tau>)) ;
  R' = R \<tau> \<union> { eval_word e \<tau> } ; a \<in> {No_Abst, Eq_Abst} \<rbrakk> 
  \<Longrightarrow> step_t a (\<tau>, (Read (Var v) e, p)) (\<tau> (| l := l', R := R' |))"
| T_Write: 
  "\<lbrakk> eval_bool p \<tau> ; 
  sh' = (sh \<tau>) (eval_word e1 \<tau> := eval_word e2 \<tau>) ;
  W' = W \<tau> \<union> { eval_word e1 \<tau> } ; a \<in> {No_Abst, Eq_Abst} \<rbrakk> 
  \<Longrightarrow> step_t a (\<tau>, (Write e1 e2, p)) (\<tau> (| sh := sh', W := W' |))"
| T_Read_Adv:
  "\<lbrakk> eval_bool p \<tau> ; l' = (l \<tau>) (Inl v := asterisk) ;
  R' = R \<tau> \<union> { eval_word e \<tau> } \<rbrakk> 
  \<Longrightarrow> step_t Adv_Abst (\<tau>, (Read (Var v) e, p)) (\<tau> (| l := l', R := R' |))"
| T_Write_Adv:
  "\<lbrakk> eval_bool p \<tau> ; W' = W \<tau> \<union> { eval_word e1 \<tau> } \<rbrakk> 
  \<Longrightarrow> step_t Adv_Abst (\<tau>, (Write e1 e2, p)) (\<tau> (| \<^cancel>\<open>sh := sh',\<close> W := W' |))"

text \<open>Rephrasing \<open>T_Assign\<close> to make it more usable\<close>
lemma T_Assign_helper: 
  "\<lbrakk> eval_bool p \<tau> ; l' = (l \<tau>) (Inl v := eval_word e \<tau>) ; \<tau>' = \<tau> (| l := l' |) \<rbrakk> 
  \<Longrightarrow> step_t a (\<tau>, (Assign (Var v) e, p)) \<tau>'"
by (auto simp add: step_t.T_Assign)

text \<open>Rephrasing \<open>T_Read\<close> to make it more usable\<close>
lemma T_Read_helper: 
  "\<lbrakk> eval_bool p \<tau> ; l' = (l \<tau>) (Inl v := sh \<tau> (eval_word e \<tau>)) ;
  R' = R \<tau> \<union> { eval_word e \<tau> } ; a \<in> {No_Abst, Eq_Abst} ; 
  \<tau>' = \<tau> (| l := l', R := R' |) \<rbrakk> 
  \<Longrightarrow> step_t a (\<tau>, (Read (Var v) e, p)) \<tau>'"
by (auto simp add: step_t.T_Read)

text \<open>Rephrasing \<open>T_Write\<close> to make it more usable\<close>
lemma T_Write_helper:
  "\<lbrakk> eval_bool p \<tau> ; 
  sh' = (sh \<tau>) (eval_word e1 \<tau> := eval_word e2 \<tau>) ;
  W' = W \<tau> \<union> { eval_word e1 \<tau> } ; a \<in> {No_Abst, Eq_Abst} ;
  \<tau>' = \<tau> (| sh := sh', W := W' |) \<rbrakk> 
  \<Longrightarrow> step_t a (\<tau>, (Write e1 e2, p)) \<tau>'"
by (auto simp add: step_t.T_Write)

end
