section \<open>Weakest (Liberal) Precondition Calculus\<close>

theory utp_wp
imports utp_hoare
begin

text \<open>A very quick implementation of wlp -- more laws still needed!\<close>

named_theorems wp

method wp_tac = (simp add: wp)

consts
  uwp :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" 

syntax
  "_uwp" :: "logic \<Rightarrow> uexp \<Rightarrow> logic" (infix "wp" 60)

translations
  "_uwp P b" == "CONST uwp P b"

definition wp_upred :: "('\<alpha>, '\<beta>) urel \<Rightarrow> '\<beta> cond \<Rightarrow> '\<alpha> cond" where
"wp_upred Q r = \<lfloor>\<not> (Q ;; (\<not> \<lceil>r\<rceil>\<^sub><)) :: ('\<alpha>, '\<beta>) urel\<rfloor>\<^sub><"

adhoc_overloading
  uwp wp_upred

declare wp_upred_def [urel_defs]

lemma wp_true [wp]: "p wp true = true"
  by (rel_simp)  
  
theorem wp_assigns_r [wp]:
  "\<langle>\<sigma>\<rangle>\<^sub>a wp r = \<sigma> \<dagger> r"
  by rel_auto

theorem wp_skip_r [wp]:
  "II wp r = r"
  by rel_auto

theorem wp_abort [wp]:
  "r \<noteq> true \<Longrightarrow> true wp r = false"
  by rel_auto

theorem wp_conj [wp]:
  "P wp (q \<and> r) = (P wp q \<and> P wp r)"
  by rel_auto

theorem wp_seq_r [wp]: "(P ;; Q) wp r = P wp (Q wp r)"
  by rel_auto

theorem wp_choice [wp]: "(P \<sqinter> Q) wp R = (P wp R \<and> Q wp R)"
  by (rel_auto)

theorem wp_cond [wp]: "(P \<triangleleft> b \<triangleright>\<^sub>r Q) wp r = ((b \<Rightarrow> P wp r) \<and> ((\<not> b) \<Rightarrow> Q wp r))"
  by rel_auto

lemma wp_USUP_pre [wp]: "P wp (\<Squnion>i\<in>{0..n} \<bullet> Q(i)) = (\<Squnion>i\<in>{0..n} \<bullet> P wp Q(i))"
  by (rel_auto)

theorem wp_hoare_link:
  "\<lbrace>p\<rbrace>Q\<lbrace>r\<rbrace>\<^sub>u \<longleftrightarrow> (Q wp r \<sqsubseteq> p)"
  by rel_auto

text \<open>If two programs have the same weakest precondition for any postcondition then the programs
  are the same.\<close>

theorem wp_eq_intro: "\<lbrakk> \<And> r. P wp r = Q wp r \<rbrakk> \<Longrightarrow> P = Q"
  by (rel_auto robust, fastforce+)
end