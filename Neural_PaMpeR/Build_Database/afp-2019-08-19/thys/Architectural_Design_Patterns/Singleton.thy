(*
  Title:      Singleton.thy
  Author:     Diego Marmsoler
*)
section "A Theory of Singletons"
text\<open>
  In the following, we formalize the specification of the singleton pattern as described in~\cite{Marmsoler2018c}.
\<close>
  
theory Singleton
imports DynamicArchitectures.Dynamic_Architecture_Calculus
begin
subsection Singletons
text \<open>
  In the following we formalize a variant of the Singleton pattern.
\<close>
locale singleton = dynamic_component cmp active
    for active :: "'id \<Rightarrow> cnf \<Rightarrow> bool" ("\<parallel>_\<parallel>\<^bsub>_\<^esub>" [0,110]60)
    and cmp :: "'id \<Rightarrow> cnf \<Rightarrow> 'cmp" ("\<sigma>\<^bsub>_\<^esub>(_)" [0,110]60) +
assumes alwaysActive: "\<And>k. \<exists>id. \<parallel>id\<parallel>\<^bsub>k\<^esub>"
    and unique: "\<exists>id. \<forall>k. \<forall>id'. (\<parallel>id'\<parallel>\<^bsub>k\<^esub> \<longrightarrow> id = id')"
begin
subsubsection "Calculus Interpretation"
text \<open>
\noindent
@{thm[source] baIA}: @{thm baIA [no_vars]}
\<close>
text \<open>
\noindent
@{thm[source] baIN1}: @{thm baIN1 [no_vars]}
\<close>
text \<open>
\noindent
@{thm[source] baIN2}: @{thm baIN2 [no_vars]}
\<close>

subsubsection "Architectural Guarantees"

definition "the_singleton \<equiv> THE id. \<forall>k. \<forall>id'. \<parallel>id'\<parallel>\<^bsub>k\<^esub> \<longrightarrow> id' = id"

theorem ts_prop:
  fixes k::cnf
  shows "\<And>id. \<parallel>id\<parallel>\<^bsub>k\<^esub> \<Longrightarrow> id = the_singleton"
    and "\<parallel>the_singleton\<parallel>\<^bsub>k\<^esub>"
proof -
  { fix id
    assume a1: "\<parallel>id\<parallel>\<^bsub>k\<^esub>"
  have "(THE id. \<forall>k. \<forall>id'. \<parallel>id'\<parallel>\<^bsub>k\<^esub> \<longrightarrow> id' = id) = id"
  proof (rule the_equality)
    show "\<forall>k id'. \<parallel>id'\<parallel>\<^bsub>k\<^esub> \<longrightarrow> id' = id"
    proof
      fix k show "\<forall>id'. \<parallel>id'\<parallel>\<^bsub>k\<^esub> \<longrightarrow> id' = id"
      proof
        fix id' show "\<parallel>id'\<parallel>\<^bsub>k\<^esub> \<longrightarrow> id' = id"
        proof
          assume "\<parallel>id'\<parallel>\<^bsub>k\<^esub>"
          from unique have "\<exists>id. \<forall>k. \<forall>id'. (\<parallel>id'\<parallel>\<^bsub>k\<^esub> \<longrightarrow> id = id')" .
          then obtain i'' where "\<forall>k. \<forall>id'. (\<parallel>id'\<parallel>\<^bsub>k\<^esub> \<longrightarrow> i'' = id')" by auto
            with \<open>\<parallel>id'\<parallel>\<^bsub>k\<^esub>\<close> have "id=i''" and "id'=i''" using a1 by auto
          thus "id' = id" by simp
        qed
      qed
    qed
  next
      fix i'' show "\<forall>k id'. \<parallel>id'\<parallel>\<^bsub>k\<^esub> \<longrightarrow> id' = i'' \<Longrightarrow> i'' = id" using a1 by auto
  qed
    hence "\<parallel>id\<parallel>\<^bsub>k\<^esub> \<Longrightarrow> id = the_singleton" by (simp add: the_singleton_def)
  } note g1 = this
  thus "\<And>id. \<parallel>id\<parallel>\<^bsub>k\<^esub> \<Longrightarrow> id = the_singleton" by simp

  from alwaysActive obtain id where "\<parallel>id\<parallel>\<^bsub>k\<^esub>" by blast
  with g1 have "id = the_singleton" by simp
  with \<open>\<parallel>id\<parallel>\<^bsub>k\<^esub>\<close> show "\<parallel>the_singleton\<parallel>\<^bsub>k\<^esub>" by simp
qed
declare ts_prop(2)[simp]
  
lemma lNact_active[simp]:
  fixes cid t n
  shows "\<langle>the_singleton \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> = n"
  using lNact_active ts_prop(2) by auto

lemma lNxt_active[simp]:
  fixes cid t n
  shows "\<langle>the_singleton \<rightarrow> t\<rangle>\<^bsub>n\<^esub> = n"
by (simp add: nxtAct_active)
    
lemma baI[intro]:
  fixes t n a
  assumes "\<phi> (\<sigma>\<^bsub>the_singleton\<^esub>(t n))"
  shows "eval the_singleton t t' n [\<phi>]\<^sub>b" using assms by (simp add: baIANow)
  
lemma baE[elim]:
  fixes t n a
  assumes "eval the_singleton t t' n [\<phi>]\<^sub>b"                      
  shows "\<phi> (\<sigma>\<^bsub>the_singleton\<^esub>(t n))" using assms by (simp add: baEANow)

lemma evtE[elim]:
  fixes t id n a
  assumes "eval the_singleton t t' n (\<diamond>\<^sub>b \<gamma>)"
  shows "\<exists>n'\<ge>n. eval the_singleton t t' n' \<gamma>"
proof -
  have "\<parallel>the_singleton\<parallel>\<^bsub>t n\<^esub>" by simp
  with assms obtain n' where "n'\<ge>\<langle>the_singleton \<rightarrow> t\<rangle>\<^bsub>n\<^esub>" and "(\<exists>i\<ge>n'. \<parallel>the_singleton\<parallel>\<^bsub>t i\<^esub> \<and>
    (\<forall>n''\<ge>\<langle>the_singleton \<Leftarrow> t\<rangle>\<^bsub>n'\<^esub>. n'' \<le> \<langle>the_singleton \<rightarrow> t\<rangle>\<^bsub>n'\<^esub> \<longrightarrow> eval the_singleton t t' n'' \<gamma>)) \<or>
    \<not> (\<exists>i\<ge>n'. \<parallel>the_singleton\<parallel>\<^bsub>t i\<^esub>) \<and> eval the_singleton t t' n' \<gamma>" using evtEA[of n "the_singleton" t] by blast
  moreover have "\<parallel>the_singleton\<parallel>\<^bsub>t n'\<^esub>" by simp
  ultimately have
    "\<forall>n''\<ge>\<langle>the_singleton \<Leftarrow> t\<rangle>\<^bsub>n'\<^esub>. n'' \<le> \<langle>the_singleton \<rightarrow> t\<rangle>\<^bsub>n'\<^esub> \<longrightarrow> eval the_singleton t t' n'' \<gamma>" by auto
  hence "eval the_singleton t t' n' \<gamma>" by simp
  moreover from \<open>n'\<ge>\<langle>the_singleton \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<close> have "n'\<ge>n" by (simp add: nxtAct_active)
  ultimately show ?thesis by auto
qed
  
lemma globE[elim]:
  fixes t id n a
  assumes "eval the_singleton t t' n (\<box>\<^sub>b \<gamma>)"
  shows "\<forall>n'\<ge>n. eval the_singleton t t' n' \<gamma>"
proof
  fix n' show "n \<le> n' \<longrightarrow> eval the_singleton t t' n' \<gamma>"
  proof
    assume "n\<le>n'"
    hence "\<langle>the_singleton \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> n'" by simp
    moreover have "\<parallel>the_singleton\<parallel>\<^bsub>t n\<^esub>" by simp
    ultimately show "eval the_singleton t t' n' \<gamma>"
      using \<open>eval the_singleton t t' n (\<box>\<^sub>b \<gamma>)\<close> globEA by blast
  qed
qed

lemma untilI[intro]:
  fixes t::"nat \<Rightarrow> cnf"
    and t'::"nat \<Rightarrow> 'cmp"
    and n::nat
    and n'::nat
  assumes "n'\<ge>n"
    and "eval the_singleton t t' n' \<gamma>"
    and "\<And>n''. \<lbrakk>n\<le>n''; n''<n'\<rbrakk> \<Longrightarrow> eval the_singleton t t' n'' \<gamma>'"
  shows "eval the_singleton t t' n (\<gamma>' \<UU>\<^sub>b \<gamma>)"
proof -
  have "\<parallel>the_singleton\<parallel>\<^bsub>t n\<^esub>" by simp 
  moreover from \<open>n'\<ge>n\<close> have "\<langle>the_singleton \<Leftarrow> t\<rangle>\<^bsub>n\<^esub> \<le> n'" by simp
  moreover have "\<parallel>the_singleton\<parallel>\<^bsub>t n'\<^esub>" by simp
  moreover have
    "\<exists>n''\<ge>\<langle>the_singleton \<Leftarrow> t\<rangle>\<^bsub>n'\<^esub>. n'' \<le> \<langle>the_singleton \<rightarrow> t\<rangle>\<^bsub>n'\<^esub> \<and> eval the_singleton t t' n'' \<gamma> \<and>
    (\<forall>n'''\<ge>\<langle>the_singleton \<rightarrow> t\<rangle>\<^bsub>n\<^esub>. n''' < \<langle>the_singleton \<Leftarrow> t\<rangle>\<^bsub>n''\<^esub> \<longrightarrow>
      (\<exists>n''''\<ge>\<langle>the_singleton \<Leftarrow> t\<rangle>\<^bsub>n'''\<^esub>. n'''' \<le> \<langle>the_singleton \<rightarrow> t\<rangle>\<^bsub>n'''\<^esub> \<and> eval the_singleton t t' n'''' \<gamma>'))"
  proof -
    have "n'\<ge>\<langle>the_singleton \<Leftarrow> t\<rangle>\<^bsub>n'\<^esub>" by simp
    moreover have "n' \<le> \<langle>the_singleton \<rightarrow> t\<rangle>\<^bsub>n'\<^esub>" by simp
    moreover from assms(3) have "(\<forall>n''\<ge>\<langle>the_singleton \<rightarrow> t\<rangle>\<^bsub>n\<^esub>. n'' < \<langle>the_singleton \<Leftarrow> t\<rangle>\<^bsub>n'\<^esub> \<longrightarrow>
      (\<exists>n'''\<ge>\<langle>the_singleton \<Leftarrow> t\<rangle>\<^bsub>n''\<^esub>. n''' \<le> \<langle>the_singleton \<rightarrow> t\<rangle>\<^bsub>n''\<^esub> \<and> eval the_singleton t t' n''' \<gamma>'))"
      by auto
    ultimately show ?thesis using \<open>eval the_singleton t t' n' \<gamma>\<close> by auto
  qed
  ultimately show ?thesis using untilIA[of n "the_singleton" t n' t' \<gamma> \<gamma>'] by blast
qed

lemma untilE[elim]:
  fixes t id n \<gamma>' \<gamma>
  assumes "eval the_singleton t t' n (\<gamma>' \<UU>\<^sub>b \<gamma>)"
  shows "\<exists>n'\<ge>n. eval the_singleton t t' n' \<gamma> \<and> (\<forall>n''\<ge>n. n'' < n' \<longrightarrow> eval the_singleton t t' n'' \<gamma>')"
proof -
  have "\<parallel>the_singleton\<parallel>\<^bsub>t n\<^esub>" by simp
  with \<open>eval the_singleton t t' n (\<gamma>' \<UU>\<^sub>b \<gamma>)\<close> obtain n' where "n'\<ge>\<langle>the_singleton \<rightarrow> t\<rangle>\<^bsub>n\<^esub>" and
   "(\<exists>i\<ge>n'. \<parallel>the_singleton\<parallel>\<^bsub>t i\<^esub>) \<and>
   (\<forall>n''\<ge>\<langle>the_singleton \<Leftarrow> t\<rangle>\<^bsub>n'\<^esub>. n'' \<le> \<langle>the_singleton \<rightarrow> t\<rangle>\<^bsub>n'\<^esub> \<longrightarrow> eval the_singleton t t' n'' \<gamma>) \<and>
   (\<forall>n''\<ge>\<langle>the_singleton \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>. n'' < \<langle>the_singleton \<Leftarrow> t\<rangle>\<^bsub>n'\<^esub> \<longrightarrow> eval the_singleton t t' n'' \<gamma>') \<or>
   \<not> (\<exists>i\<ge>n'. \<parallel>the_singleton\<parallel>\<^bsub>t i\<^esub>) \<and>
   eval the_singleton t t' n' \<gamma> \<and> (\<forall>n''\<ge>\<langle>the_singleton \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>. n'' < n' \<longrightarrow> eval the_singleton t t' n'' \<gamma>')"
  using untilEA[of n "the_singleton" t t' \<gamma>' \<gamma>] by auto
  moreover have "\<parallel>the_singleton\<parallel>\<^bsub>t n'\<^esub>" by simp
  ultimately have
    "(\<forall>n''\<ge>\<langle>the_singleton \<Leftarrow> t\<rangle>\<^bsub>n'\<^esub>. n'' \<le> \<langle>the_singleton \<rightarrow> t\<rangle>\<^bsub>n'\<^esub> \<longrightarrow> eval the_singleton t t' n'' \<gamma>) \<and>
    (\<forall>n''\<ge>\<langle>the_singleton \<Leftarrow> t\<rangle>\<^bsub>n\<^esub>. n'' < \<langle>the_singleton \<Leftarrow> t\<rangle>\<^bsub>n'\<^esub> \<longrightarrow> eval the_singleton t t' n'' \<gamma>')" by auto
  hence "eval the_singleton t t' n' \<gamma>" and "(\<forall>n''\<ge>n. n'' < n' \<longrightarrow> eval the_singleton t t' n'' \<gamma>')" by auto
  with \<open>eval the_singleton t t' n' \<gamma>\<close> \<open>n'\<ge>\<langle>the_singleton \<rightarrow> t\<rangle>\<^bsub>n\<^esub>\<close> show ?thesis by auto
qed
end

end
