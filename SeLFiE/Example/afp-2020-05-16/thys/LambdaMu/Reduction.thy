subsection \<open>Reduction relation\<close>

theory Reduction
  imports Substitution
begin

inductive red_term :: "[trm, trm] \<Rightarrow> bool"  (infixl "\<longlonglongrightarrow>" 50) 
      and red_cmd :: "[cmd, cmd] \<Rightarrow> bool"  (infixl "\<^sub>C\<longlonglongrightarrow>" 50)
where
  beta   [intro]: "(\<lambda> T : t)\<degree>r \<longlonglongrightarrow> t[r/0]\<^sup>T" |
  struct [intro]: "(\<mu> (T1\<rightarrow>T2) : c)\<degree>s \<longlonglongrightarrow> \<mu> T2 : (c[0 = 0 (\<diamond> \<^sup>\<bullet> (liftM_trm s 0))]\<^sup>C)" |
  rename [intro]: "\<lbrakk> 0 \<notin> (fmv_trm t 0) \<rbrakk> \<Longrightarrow> (\<mu> T : (<0> t)) \<longlonglongrightarrow> dropM_trm t 0" |
  mueta  [intro]: "<i> (\<mu> T : c) \<^sub>C\<longlonglongrightarrow> (dropM_cmd (c[0 = i \<diamond>]\<^sup>C) i)" |

  lambda [intro]: "\<lbrakk> s \<longlonglongrightarrow> t \<rbrakk> \<Longrightarrow> (\<lambda> T : s) \<longlonglongrightarrow> (\<lambda> T : t)" |
  appL   [intro]: "\<lbrakk> s \<longlonglongrightarrow> u \<rbrakk> \<Longrightarrow> (s\<degree>t) \<longlonglongrightarrow> (u\<degree>t)" |
  appR   [intro]: "\<lbrakk> t \<longlonglongrightarrow> u \<rbrakk> \<Longrightarrow> (s\<degree>t) \<longlonglongrightarrow> (s\<degree>u)" |
  mu     [intro]: "\<lbrakk> c \<^sub>C\<longlonglongrightarrow> d \<rbrakk> \<Longrightarrow> (\<mu> T : c) \<longlonglongrightarrow> (\<mu> T : d)" |
  cmd    [intro]: "\<lbrakk> t \<longlonglongrightarrow> s \<rbrakk> \<Longrightarrow> (<i> t) \<^sub>C\<longlonglongrightarrow> (<i> s)"

inductive_cases redE [elim]:
  "`i \<longlonglongrightarrow> s"
  "(\<lambda> T : t) \<longlonglongrightarrow> s"
  "s\<degree>t \<longlonglongrightarrow> u"
  "(\<mu> T : c) \<longlonglongrightarrow> t"
  "<i> t \<^sub>C\<longlonglongrightarrow> c"

text\<open>Reflexive transitive closure\<close>

inductive beta_rtc_term :: "[trm, trm] \<Rightarrow> bool"  (infixl "\<longlonglongrightarrow>\<^sup>*" 50) where
  refl_term [iff]: "s \<longlonglongrightarrow>\<^sup>* s" |
  step_term: "\<lbrakk>s \<longlonglongrightarrow> t; t \<longlonglongrightarrow>\<^sup>* u\<rbrakk> \<Longrightarrow> s \<longlonglongrightarrow>\<^sup>* u"

lemma step_term2: "\<lbrakk>s \<longlonglongrightarrow>\<^sup>* t; t \<longlonglongrightarrow> u\<rbrakk> \<Longrightarrow> s \<longlonglongrightarrow>\<^sup>* u"
  by (induct rule: beta_rtc_term.induct) (auto intro: step_term)

inductive beta_rtc_command :: "[cmd, cmd] \<Rightarrow> bool"  (infixl "\<^sub>C\<longlonglongrightarrow>\<^sup>*" 50) where
  refl_command [iff]: "c \<^sub>C\<longlonglongrightarrow>\<^sup>* c" |
  step_command: "c \<^sub>C\<longlonglongrightarrow> d \<Longrightarrow> d \<^sub>C\<longlonglongrightarrow>\<^sup>* e \<Longrightarrow> c \<^sub>C\<longlonglongrightarrow>\<^sup>* e"

text\<open>The beta reduction relation is included in the reflexive transitive closure.\<close>
lemma rtc_term_incl [intro]: "s \<longlonglongrightarrow> t \<Longrightarrow> s \<longlonglongrightarrow>\<^sup>* t"
  by (meson beta_rtc_term.simps)

lemma [intro]: "c \<^sub>C\<longlonglongrightarrow> d \<Longrightarrow> c \<^sub>C\<longlonglongrightarrow>\<^sup>* d"
  by(auto intro: step_command)

text\<open>Proof that the reflexive transitive closure as defined above is transitive.\<close>
  
lemma rtc_term_trans [intro]: "s \<longlonglongrightarrow>\<^sup>* t \<Longrightarrow> t \<longlonglongrightarrow>\<^sup>* u \<Longrightarrow> s \<longlonglongrightarrow>\<^sup>* u"
  by(induction rule: beta_rtc_term.induct) (auto simp add: step_term)

lemma rtc_command_trans[intro]: "c \<^sub>C\<longlonglongrightarrow>\<^sup>* d \<Longrightarrow> d \<^sub>C\<longlonglongrightarrow>\<^sup>* e \<Longrightarrow> c \<^sub>C\<longlonglongrightarrow>\<^sup>* e"
  by(induction rule: beta_rtc_command.induct) (auto simp add: step_command)

text\<open>Congruence rules for the reflexive transitive closure.\<close>

lemma rtc_lambda: "s \<longlonglongrightarrow>\<^sup>* t \<Longrightarrow> (\<lambda> T : s) \<longlonglongrightarrow>\<^sup>* (\<lambda> T : t)"
  apply(induction rule: beta_rtc_term.induct)
  by force (meson red_term_red_cmd.lambda step_term)

lemma rtc_appL: "s \<longlonglongrightarrow>\<^sup>* u \<Longrightarrow> (s\<degree>t) \<longlonglongrightarrow>\<^sup>* (u\<degree>t)"
  apply(induction rule: beta_rtc_term.induct)
  by force (meson appL step_term)
    
end
