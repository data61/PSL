chapter\<open>Main Theorems\<close>

theory Hygge_Theory
imports
  Corecursive_Prop

begin
text \<open>
  Using the properties we have shown about the interpretation of configurations 
  and the stepwise unfolding of the denotational semantics, we can now prove 
  several important results about the construction of runs from a specification.
\<close>
section \<open>Initial configuration\<close>

text \<open>
  The denotational semantics of a specification @{term \<open>\<Psi>\<close>} is the interpretation 
  at the first instant of a configuration which has @{term \<open>\<Psi>\<close>} as its present.
  This means that we can start to build a run that satisfies a specification by 
  starting from this configuration.
\<close>
theorem solve_start:
  shows \<open>\<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk> [], 0 \<turnstile> \<Psi> \<triangleright> [] \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
  proof -
    have \<open>\<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> 0\<^esup>\<close>
    by (simp add: TESL_interpretation_stepwise_zero')
    moreover have \<open>\<lbrakk> [], 0 \<turnstile> \<Psi> \<triangleright> [] \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g =
                      \<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> 0\<^esup> \<inter> \<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc 0\<^esup>\<close>
    by simp
    ultimately show ?thesis by auto
  qed

section \<open>Soundness\<close>
text \<open>
  The interpretation of a configuration @{term \<open>\<S>\<^sub>2\<close>} that is a refinement of a
  configuration @{term \<open>\<S>\<^sub>1\<close>} is contained in the interpretation of @{term \<open>\<S>\<^sub>1\<close>}.
  This means that by making successive choices in building the instants of a run,
  we preserve the soundness of the constructed run with regard to the original 
  specification.
\<close>
lemma sound_reduction:
  assumes \<open>(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1)  \<hookrightarrow>  (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2)\<close>
  shows \<open>\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>1\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>1\<^esup>
          \<supseteq>  \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^sub>2\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^sub>2\<^esup>\<close> (is ?P)
proof -
  from assms consider
    (a) \<open>(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1)  \<hookrightarrow>\<^sub>i  (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2)\<close>
  | (b) \<open>(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1)  \<hookrightarrow>\<^sub>e  (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2)\<close>
    using operational_semantics_step.simps by blast
  thus ?thesis
  proof (cases)
    case a
      thus ?thesis by (simp add: operational_semantics_intro.simps)
  next
    case b thus ?thesis
    proof (rule operational_semantics_elim.cases)
      fix  \<Gamma> n K\<^sub>1 \<tau> K\<^sub>2 \<Psi> \<Phi>
      assume \<open>(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi>)\<close>
      and \<open>(\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (\<Gamma>, n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi>))\<close>
      thus ?P using HeronConf_interp_stepwise_sporadicon_cases
                    HeronConf_interpretation.simps by blast
    next
      fix  \<Gamma> n K\<^sub>1 \<tau> K\<^sub>2 \<Psi> \<Phi>
      assume \<open>(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi>)\<close>
      and \<open>(\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Down> n @ \<tau>) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> \<Phi>)\<close>
      thus ?P using HeronConf_interp_stepwise_sporadicon_cases
                    HeronConf_interpretation.simps by blast
    next
      fix \<Gamma> n K\<^sub>1 K\<^sub>2 R \<Psi> \<Phi>
      assume \<open>(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> (time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R) # \<Psi> \<triangleright> \<Phi>)\<close>
      and \<open>(\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (((\<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>2, n)\<rfloor> \<in> R) # \<Gamma>), n
                                      \<turnstile> \<Psi> \<triangleright> ((time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R) # \<Phi>))\<close>
      thus ?P using HeronConf_interp_stepwise_tagrel_cases
                    HeronConf_interpretation.simps by blast
    next
      fix \<Gamma> n K\<^sub>1 K\<^sub>2 \<Psi> \<Phi>
      assume \<open>(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi>)\<close>
      and \<open>(\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>))\<close>
      thus ?P using HeronConf_interp_stepwise_implies_cases
                    HeronConf_interpretation.simps by blast
    next
      fix \<Gamma> n K\<^sub>1 K\<^sub>2 \<Psi> \<Phi>
      assume \<open>(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> ((K\<^sub>1 implies K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)\<close>
      and \<open>(\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Up> n) # \<Gamma>), n
                                   \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>))\<close>
      thus ?P using HeronConf_interp_stepwise_implies_cases
                    HeronConf_interpretation.simps by blast
    next
      fix \<Gamma> n K\<^sub>1 K\<^sub>2 \<Psi> \<Phi>
      assume \<open>(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> ((K\<^sub>1 implies not K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)\<close>
      and \<open>(\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies not K\<^sub>2) # \<Phi>))\<close>
      thus ?P using HeronConf_interp_stepwise_implies_not_cases
                    HeronConf_interpretation.simps by blast
    next
      fix \<Gamma> n K\<^sub>1 K\<^sub>2 \<Psi> \<Phi>
      assume \<open>(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> ((K\<^sub>1 implies not K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)\<close>
      and \<open>(\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> n) # \<Gamma>), n
                                   \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies not K\<^sub>2) # \<Phi>))\<close>
      thus ?P using HeronConf_interp_stepwise_implies_not_cases
                    HeronConf_interpretation.simps by blast
    next
      fix \<Gamma> n K\<^sub>1 \<delta>\<tau> K\<^sub>2 K\<^sub>3 \<Psi> \<Phi>
      assume \<open>(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) =
                (\<Gamma>, n \<turnstile> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi>) \<triangleright> \<Phi>)\<close>
      and \<open>(\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) =
            (((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>))\<close>
      thus ?P using HeronConf_interp_stepwise_timedelayed_cases
                    HeronConf_interpretation.simps by blast
    next
      fix \<Gamma> n K\<^sub>1 \<delta>\<tau> K\<^sub>2 K\<^sub>3 \<Psi> \<Phi>
      assume \<open>(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) =
               (\<Gamma>, n \<turnstile> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi>) \<triangleright> \<Phi>)\<close>
      and \<open>(\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2)
            = (((K\<^sub>1 \<Up> n) # (K\<^sub>2 @ n \<oplus> \<delta>\<tau> \<Rightarrow> K\<^sub>3) # \<Gamma>), n
                \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>))\<close>
      thus ?P using HeronConf_interp_stepwise_timedelayed_cases
                    HeronConf_interpretation.simps by blast
    next
      fix \<Gamma> n K\<^sub>1 K\<^sub>2 \<Psi> \<Phi>
      assume \<open>(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> ((K\<^sub>1 weakly precedes K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)\<close>
      and \<open>(\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (((\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>\<le> K\<^sub>1 n\<rceil> \<in> (\<lambda>(x, y). x \<le> y)) # \<Gamma>), n
                                  \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 weakly precedes K\<^sub>2) # \<Phi>))\<close>
      thus ?P using HeronConf_interp_stepwise_weakly_precedes_cases
                    HeronConf_interpretation.simps by blast
    next
      fix \<Gamma> n K\<^sub>1 K\<^sub>2 \<Psi> \<Phi>
      assume \<open>(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> ((K\<^sub>1 strictly precedes K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)\<close>
      and \<open>(\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (((\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>< K\<^sub>1 n\<rceil> \<in> (\<lambda>(x, y). x \<le> y)) # \<Gamma>), n
                                  \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 strictly precedes K\<^sub>2) # \<Phi>))\<close>
      thus ?P using HeronConf_interp_stepwise_strictly_precedes_cases
                    HeronConf_interpretation.simps by blast
    next
      fix \<Gamma> n K\<^sub>1 K\<^sub>2 \<Psi> \<Phi>
      assume \<open>(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> ((K\<^sub>1 kills K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)\<close>
      and \<open>(\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) = (((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 kills K\<^sub>2) # \<Phi>))\<close>
      thus ?P using HeronConf_interp_stepwise_kills_cases
                    HeronConf_interpretation.simps by blast
    next
      fix \<Gamma> n K\<^sub>1 K\<^sub>2 \<Psi> \<Phi>
      assume \<open>(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1) = (\<Gamma>, n \<turnstile> ((K\<^sub>1 kills K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)\<close>
      and \<open>(\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) =
            (((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> \<ge> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 kills K\<^sub>2) # \<Phi>))\<close>
      thus ?P using HeronConf_interp_stepwise_kills_cases
                    HeronConf_interpretation.simps by blast
    qed
  qed
qed

inductive_cases step_elim:\<open>\<S>\<^sub>1 \<hookrightarrow> \<S>\<^sub>2\<close>

lemma sound_reduction':
  assumes \<open>\<S>\<^sub>1 \<hookrightarrow> \<S>\<^sub>2\<close>
  shows \<open>\<lbrakk> \<S>\<^sub>1 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<supseteq> \<lbrakk> \<S>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
proof -
  have \<open>\<forall>s\<^sub>1 s\<^sub>2. (\<lbrakk> s\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<subseteq> \<lbrakk> s\<^sub>1 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g) \<or> \<not>(s\<^sub>1 \<hookrightarrow> s\<^sub>2)\<close>
    using sound_reduction by fastforce
  thus ?thesis using assms by blast
qed

lemma sound_reduction_generalized:
  assumes \<open>\<S>\<^sub>1 \<hookrightarrow>\<^bsup>k\<^esup> \<S>\<^sub>2\<close>
    shows \<open>\<lbrakk> \<S>\<^sub>1 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<supseteq> \<lbrakk> \<S>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
proof -
  from assms show ?thesis
  proof (induction k arbitrary: \<S>\<^sub>2)
    case 0
      hence *: \<open>\<S>\<^sub>1 \<hookrightarrow>\<^bsup>0\<^esup> \<S>\<^sub>2 \<Longrightarrow> \<S>\<^sub>1 = \<S>\<^sub>2\<close> by auto
      moreover have \<open>\<S>\<^sub>1 = \<S>\<^sub>2\<close> using * "0.prems" by linarith
      ultimately show ?case by auto
  next
    case (Suc k)
      thus ?case
      proof -
        fix k :: nat
        assume ff: \<open>\<S>\<^sub>1 \<hookrightarrow>\<^bsup>Suc k\<^esup> \<S>\<^sub>2\<close>
        assume hi: \<open>\<And>\<S>\<^sub>2. \<S>\<^sub>1 \<hookrightarrow>\<^bsup>k\<^esup> \<S>\<^sub>2 \<Longrightarrow> \<lbrakk> \<S>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<subseteq> \<lbrakk> \<S>\<^sub>1 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
        obtain \<S>\<^sub>n where red_decomp: \<open>(\<S>\<^sub>1 \<hookrightarrow>\<^bsup>k\<^esup> \<S>\<^sub>n) \<and> (\<S>\<^sub>n \<hookrightarrow> \<S>\<^sub>2)\<close> using ff by auto
        hence \<open>\<lbrakk> \<S>\<^sub>1 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<supseteq> \<lbrakk> \<S>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close> using hi by simp
        also have \<open>\<lbrakk> \<S>\<^sub>n \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<supseteq> \<lbrakk> \<S>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close> by (simp add: red_decomp sound_reduction')
        ultimately show \<open>\<lbrakk> \<S>\<^sub>1 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<supseteq> \<lbrakk> \<S>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close> by simp
      qed
  qed
qed

text \<open>
  From the initial configuration, a configuration @{term \<open>\<S>\<close>} obtained after any 
  number @{term \<open>k\<close>} of reduction steps denotes runs from the 
  initial specification @{term \<open>\<Psi>\<close>}.
\<close>
theorem soundness:
  assumes \<open>([], 0 \<turnstile> \<Psi> \<triangleright> []) \<hookrightarrow>\<^bsup>k\<^esup> \<S>\<close>
    shows \<open>\<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<supseteq> \<lbrakk> \<S> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
  using assms sound_reduction_generalized solve_start by blast

section \<open>Completeness\<close>

text \<open>
  We will now show that any run that satisfies a specification can be derived
  from the initial configuration, at any number of steps.

  We start by proving that any run that is denoted by a configuration @{term \<open>\<S>\<close>}
  is necessarily denoted by at least one of the configurations that can be reached
  from @{term \<open>\<S>\<close>}.
\<close>
lemma complete_direct_successors:
  shows \<open>\<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<subseteq> (\<Union>X\<in>\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>). \<lbrakk> X \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g)\<close>
  proof (induct \<Psi>)
    case Nil
    show ?case
      using HeronConf_interp_stepwise_instant_cases operational_semantics_step.simps
            operational_semantics_intro.instant_i
      by fastforce
  next
    case (Cons \<psi> \<Psi>)  thus ?case
      proof (cases \<psi>)
        case (SporadicOn K1 \<tau> K2) thus ?thesis 
          using HeronConf_interp_stepwise_sporadicon_cases
                                      [of \<open>\<Gamma>\<close> \<open>n\<close> \<open>K1\<close> \<open>\<tau>\<close> \<open>K2\<close> \<open>\<Psi>\<close> \<open>\<Phi>\<close>]
                Cnext_solve_sporadicon[of \<open>\<Gamma>\<close> \<open>n\<close> \<open>\<Psi>\<close> \<open>K1\<close> \<open>\<tau>\<close> \<open>K2\<close> \<open>\<Phi>\<close>] by blast
      next
        case (TagRelation K\<^sub>1 K\<^sub>2 R) thus ?thesis
          using HeronConf_interp_stepwise_tagrel_cases
                                  [of \<open>\<Gamma>\<close> \<open>n\<close> \<open>K\<^sub>1\<close> \<open>K\<^sub>2\<close> \<open>R\<close> \<open>\<Psi>\<close> \<open>\<Phi>\<close>]
                Cnext_solve_tagrel[of \<open>K\<^sub>1\<close> \<open>n\<close> \<open>K\<^sub>2\<close> \<open>R\<close> \<open>\<Gamma>\<close> \<open>\<Psi>\<close> \<open>\<Phi>\<close>] by blast
      next
        case (Implies K1 K2) thus ?thesis
          using HeronConf_interp_stepwise_implies_cases
                                   [of \<open>\<Gamma>\<close> \<open>n\<close> \<open>K1\<close> \<open>K2\<close> \<open>\<Psi>\<close> \<open>\<Phi>\<close>]
                Cnext_solve_implies[of \<open>K1\<close> \<open>n\<close> \<open>\<Gamma>\<close> \<open>\<Psi>\<close> \<open>K2\<close> \<open>\<Phi>\<close>] by blast
      next
        case (ImpliesNot K1 K2) thus ?thesis
          using HeronConf_interp_stepwise_implies_not_cases
                                       [of \<open>\<Gamma>\<close> \<open>n\<close> \<open>K1\<close> \<open>K2\<close> \<open>\<Psi>\<close> \<open>\<Phi>\<close>]
                Cnext_solve_implies_not[of \<open>K1\<close> \<open>n\<close> \<open>\<Gamma>\<close> \<open>\<Psi>\<close> \<open>K2\<close> \<open>\<Phi>\<close>] by blast
      next
        case (TimeDelayedBy Kmast \<tau> Kmeas Kslave) thus ?thesis
          using HeronConf_interp_stepwise_timedelayed_cases
                          [of \<open>\<Gamma>\<close> \<open>n\<close> \<open>Kmast\<close> \<open>\<tau>\<close> \<open>Kmeas\<close> \<open>Kslave\<close> \<open>\<Psi>\<close> \<open>\<Phi>\<close>]
                Cnext_solve_timedelayed
                          [of \<open>Kmast\<close> \<open>n\<close> \<open>\<Gamma>\<close> \<open>\<Psi>\<close> \<open>\<tau>\<close> \<open>Kmeas\<close> \<open>Kslave\<close> \<open>\<Phi>\<close>] by blast
      next
        case (WeaklyPrecedes K1 K2) thus ?thesis
          using HeronConf_interp_stepwise_weakly_precedes_cases
                                           [of \<open>\<Gamma>\<close> \<open>n\<close> \<open>K1\<close> \<open>K2\<close> \<open>\<Psi>\<close> \<open>\<Phi>\<close>]
                Cnext_solve_weakly_precedes[of \<open>K2\<close> \<open>n\<close> \<open>K1\<close> \<open>\<Gamma>\<close> \<open>\<Psi>\<close>  \<open>\<Phi>\<close>]
          by blast
      next
        case (StrictlyPrecedes K1 K2)  thus ?thesis
          using HeronConf_interp_stepwise_strictly_precedes_cases
                                             [of \<open>\<Gamma>\<close> \<open>n\<close> \<open>K1\<close> \<open>K2\<close> \<open>\<Psi>\<close> \<open>\<Phi>\<close>]
                Cnext_solve_strictly_precedes[of \<open>K2\<close> \<open>n\<close> \<open>K1\<close> \<open>\<Gamma>\<close> \<open>\<Psi>\<close>  \<open>\<Phi>\<close>]
          by blast
      next
        case (Kills K1 K2) thus ?thesis
          using HeronConf_interp_stepwise_kills_cases[of \<open>\<Gamma>\<close> \<open>n\<close> \<open>K1\<close> \<open>K2\<close> \<open>\<Psi>\<close> \<open>\<Phi>\<close>]
                Cnext_solve_kills[of \<open>K1\<close> \<open>n\<close> \<open>\<Gamma>\<close> \<open>\<Psi>\<close> \<open>K2\<close> \<open>\<Phi>\<close>] by blast
      qed
  qed

lemma complete_direct_successors':
  shows \<open>\<lbrakk> \<S> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<subseteq> (\<Union>X\<in>\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t \<S>. \<lbrakk> X \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g)\<close>
proof -
  from HeronConf_interpretation.cases obtain \<Gamma> n \<Psi> \<Phi>
    where \<open>\<S> = (\<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>)\<close> by blast
  with complete_direct_successors[of \<open>\<Gamma>\<close> \<open>n\<close> \<open>\<Psi>\<close> \<open>\<Phi>\<close>] show ?thesis by simp
qed

text \<open>
  Therefore, if a run belongs to a configuration, it necessarily belongs to a
  configuration derived from it.
\<close>
lemma branch_existence:
  assumes \<open>\<rho> \<in> \<lbrakk> \<S>\<^sub>1 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
  shows \<open>\<exists>\<S>\<^sub>2. (\<S>\<^sub>1 \<hookrightarrow> \<S>\<^sub>2) \<and> (\<rho> \<in> \<lbrakk> \<S>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g)\<close>
proof -
  from assms complete_direct_successors' have \<open>\<rho> \<in> (\<Union>X\<in>\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t \<S>\<^sub>1. \<lbrakk> X \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g)\<close> by blast
  hence \<open>\<exists>s\<in>\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t \<S>\<^sub>1. \<rho> \<in> \<lbrakk> s \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close> by simp
  thus ?thesis by blast
qed

lemma branch_existence':
  assumes \<open>\<rho> \<in> \<lbrakk> \<S>\<^sub>1 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
  shows \<open>\<exists>\<S>\<^sub>2. (\<S>\<^sub>1 \<hookrightarrow>\<^bsup>k\<^esup> \<S>\<^sub>2) \<and> (\<rho> \<in> \<lbrakk> \<S>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g)\<close>
proof (induct k)
  case 0
    thus ?case by (simp add: assms)
next
  case (Suc k)
    thus ?case
      using branch_existence relpowp_Suc_I[of \<open>k\<close> \<open>operational_semantics_step\<close>]
    by blast
qed

text\<open>
  Any run that belongs to the original specification @{term \<open>\<Psi>\<close>} has a corresponding 
  configuration @{term \<open>\<S>\<close>} at any number @{term \<open>k\<close>} of reduction steps
  from the initial configuration. Therefore, any run that satisfies a specification
  can be derived from the initial configuration at any level of reduction.
\<close>
theorem completeness:
  assumes \<open>\<rho> \<in> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
  shows \<open>\<exists>\<S>. (([], 0 \<turnstile> \<Psi> \<triangleright> [])  \<hookrightarrow>\<^bsup>k\<^esup>  \<S>)
           \<and> \<rho> \<in> \<lbrakk> \<S> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
  using assms branch_existence' solve_start by blast

section \<open>Progress\<close>

text \<open>
  Reduction steps do not guarantee that the construction of a run progresses in the
  sequence of instants. We need to show that it is always possible to reach the next 
  instant, and therefore any future instant, through a number of steps.
\<close>
lemma instant_index_increase:
  assumes \<open>\<rho> \<in> \<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
  shows   \<open>\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. ((\<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>)  \<hookrightarrow>\<^bsup>k\<^esup>  (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))
                         \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
proof (insert assms, induct \<Psi> arbitrary: \<Gamma> \<Phi>)
  case (Nil \<Gamma> \<Phi>)
    then show ?case
    proof -
      have \<open>(\<Gamma>, n \<turnstile> [] \<triangleright> \<Phi>) \<hookrightarrow>\<^bsup>1\<^esup> (\<Gamma>, Suc n \<turnstile> \<Phi> \<triangleright> [])\<close>
        using instant_i intro_part by fastforce
      moreover have \<open>\<lbrakk> \<Gamma>, n \<turnstile> [] \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk> \<Gamma>, Suc n \<turnstile> \<Phi> \<triangleright> [] \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
        by auto
      moreover have \<open>\<rho> \<in> \<lbrakk> \<Gamma>, Suc n \<turnstile> \<Phi> \<triangleright> [] \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
        using assms Nil.prems calculation(2) by blast
      ultimately show ?thesis by blast
    qed
next
  case (Cons \<psi> \<Psi>)
    then show ?case
    proof (induct \<psi>)
      case (SporadicOn K\<^sub>1 \<tau> K\<^sub>2)
        have branches: \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                      = \<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                      \<union> \<lbrakk> ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Down> n @ \<tau>) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
          using HeronConf_interp_stepwise_sporadicon_cases by simp
        have br1: \<open>\<rho> \<in> \<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                    \<Longrightarrow> \<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k.
                      ((\<Gamma>, n \<turnstile> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
                          \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))
                      \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
        proof -
          assume h1: \<open>\<rho> \<in> \<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
          hence \<open>\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. ((\<Gamma>, n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi>))
                                      \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))
                                 \<and> (\<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g)\<close>
            using h1 SporadicOn.prems by simp
          from this obtain \<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k where
              fp:\<open>((\<Gamma>, n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi>))
                    \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))
                \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close> by blast
          have
            \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
              \<hookrightarrow> (\<Gamma>, n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi>))\<close>
            by (simp add: elims_part sporadic_on_e1)
          with fp relpowp_Suc_I2 have
            \<open>((\<Gamma>, n \<turnstile> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
              \<hookrightarrow>\<^bsup>Suc k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))\<close> by auto
          thus ?thesis using fp by blast
        qed
        have br2: \<open>\<rho> \<in> \<lbrakk> ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Down> n @ \<tau>) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                  \<Longrightarrow> \<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. ((\<Gamma>, n \<turnstile> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
                                        \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))
                            \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
        proof -
          assume h2: \<open>\<rho> \<in> \<lbrakk> ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Down> n @ \<tau>) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
          hence \<open>\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. ((((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Down> n @ \<tau>) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> \<Phi>)
                                    \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))
                             \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
            using h2 SporadicOn.prems by simp

            from this obtain \<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k
            where fp:\<open>((((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Down> n @ \<tau>) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> \<Phi>)
                            \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))\<close>
              and rc:\<open>\<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close> by blast
            have pc:\<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
              \<hookrightarrow> (((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Down> n @ \<tau>) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> \<Phi>)\<close>
            by (simp add: elims_part sporadic_on_e2)
            hence \<open>(\<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi>)
                    \<hookrightarrow>\<^bsup>Suc k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k)\<close>
                using fp relpowp_Suc_I2 by auto
            with rc show ?thesis by blast
        qed
        from branches SporadicOn.prems(2) have
          \<open>\<rho> \<in> \<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
             \<union> \<lbrakk> ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Down> n @ \<tau>) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
          by simp
        with br1 br2 show ?case by blast
  next
    case (TagRelation K\<^sub>1 K\<^sub>2 R)
      have branches: \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = \<lbrakk> ((\<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n)\<rfloor> \<in> R) # \<Gamma>), n
              \<turnstile> \<Psi> \<triangleright> ((time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
        using HeronConf_interp_stepwise_tagrel_cases by simp
      thus ?case
      proof -
        have \<open>\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k.
            ((((\<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n)\<rfloor> \<in> R) # \<Gamma>), n
                \<turnstile> \<Psi> \<triangleright> ((time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R) # \<Phi>))
              \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k)) \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
          using TagRelation.prems by simp

        from this obtain \<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k
          where fp:\<open>((((\<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n)\<rfloor> \<in> R) # \<Gamma>), n
                        \<turnstile> \<Psi> \<triangleright> ((time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R) # \<Phi>))
                    \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))\<close>
            and rc:\<open>\<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close> by blast
        have pc:\<open>(\<Gamma>, n \<turnstile> ((time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R) # \<Psi>) \<triangleright> \<Phi>)
            \<hookrightarrow> (((\<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r (K\<^sub>2, n)\<rfloor> \<in> R) # \<Gamma>), n
                  \<turnstile> \<Psi> \<triangleright> ((time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R) # \<Phi>))\<close>
          by (simp add: elims_part tagrel_e)
        hence \<open>(\<Gamma>, n \<turnstile> (time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R) # \<Psi> \<triangleright> \<Phi>)
                \<hookrightarrow>\<^bsup>Suc k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k)\<close>
          using fp relpowp_Suc_I2 by auto
        with rc show ?thesis by blast
      qed
  next
    case (Implies K\<^sub>1 K\<^sub>2)
      have branches: \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((K\<^sub>1 implies K\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = \<lbrakk> ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          \<union> \<lbrakk> ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
        using HeronConf_interp_stepwise_implies_cases by simp
      moreover have br1: \<open>\<rho> \<in> \<lbrakk> ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                \<Longrightarrow> \<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. ((\<Gamma>, n \<turnstile> ((K\<^sub>1 implies K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
                                    \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))
                  \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
      proof -
        assume h1: \<open>\<rho> \<in> \<lbrakk> ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
        then have \<open>\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k.
                    ((((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>))
                        \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))
                  \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
          using h1 Implies.prems by simp
        from this obtain \<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k where
          fp:\<open>((((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>))
            \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))\<close>
          and rc:\<open>\<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close> by blast
        have pc:\<open>(\<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi>)
                  \<hookrightarrow> (((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>))\<close>
          by (simp add: elims_part implies_e1)
        hence \<open>(\<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi>) \<hookrightarrow>\<^bsup>Suc k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k)\<close>
          using fp relpowp_Suc_I2 by auto
        with rc show ?thesis by blast
      qed
      moreover have br2: \<open>\<rho> \<in> \<lbrakk> ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Up> n) # \<Gamma>), n
                                \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                            \<Longrightarrow> \<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. ((\<Gamma>, n \<turnstile> ((K\<^sub>1 implies K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
                                              \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))
                                  \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
      proof -
        assume h2: \<open>\<rho> \<in> \<lbrakk> ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Up> n) # \<Gamma>), n
                          \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
        then have \<open>\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. (
                        (((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>))
                          \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k)
                    ) \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
          using h2 Implies.prems by simp
        from this obtain \<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k where
            fp:\<open>(((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>))
                \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k)\<close>
        and rc:\<open>\<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close> by blast
        have \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 implies K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
              \<hookrightarrow> (((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>))\<close>
          by (simp add: elims_part implies_e2)
        hence \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 implies K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>) \<hookrightarrow>\<^bsup>Suc k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k)\<close>
          using fp relpowp_Suc_I2 by auto
        with rc show ?thesis by blast
      qed
      ultimately show ?case using Implies.prems(2) by blast
  next
    case (ImpliesNot K\<^sub>1 K\<^sub>2)
      have branches: \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((K\<^sub>1 implies not K\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = \<lbrakk> ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies not K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          \<union> \<lbrakk> ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies not K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
        using HeronConf_interp_stepwise_implies_not_cases by simp
      moreover have br1: \<open>\<rho> \<in> \<lbrakk> ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n
                            \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies not K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                \<Longrightarrow> \<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. ((\<Gamma>, n \<turnstile> ((K\<^sub>1 implies not K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
                                    \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))
                  \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
      proof -
        assume h1: \<open>\<rho> \<in> \<lbrakk> ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies not K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
        then have \<open>\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k.
                    ((((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies not K\<^sub>2) # \<Phi>))
                      \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))
                  \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
          using h1 ImpliesNot.prems by simp
        from this obtain \<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k where
          fp:\<open>((((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies not K\<^sub>2) # \<Phi>))
                \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))\<close>
          and rc:\<open>\<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close> by blast
        have pc:\<open>(\<Gamma>, n \<turnstile> (K\<^sub>1 implies not K\<^sub>2) # \<Psi> \<triangleright> \<Phi>)
                  \<hookrightarrow> (((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies not K\<^sub>2) # \<Phi>))\<close>
          by (simp add: elims_part implies_not_e1)
        hence \<open>(\<Gamma>, n \<turnstile> (K\<^sub>1 implies not K\<^sub>2) # \<Psi> \<triangleright> \<Phi>) \<hookrightarrow>\<^bsup>Suc k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k)\<close>
          using fp relpowp_Suc_I2 by auto
        with rc show ?thesis by blast
      qed
      moreover have br2: \<open>\<rho> \<in> \<lbrakk> ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> n) # \<Gamma>), n
                            \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies not K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                            \<Longrightarrow> \<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. ((\<Gamma>, n \<turnstile> ((K\<^sub>1 implies not K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
                                              \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))
                                  \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
      proof -
        assume h2: \<open>\<rho> \<in> \<lbrakk> ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> n) # \<Gamma>), n
                          \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies not K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
        then have \<open>\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. (
                     (((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> n) # \<Gamma>), n
                       \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies not K\<^sub>2) # \<Phi>)) \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k)
                    ) \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
          using h2 ImpliesNot.prems by simp
        from this obtain \<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k where
            fp:\<open>(((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies not K\<^sub>2) # \<Phi>))
                \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k)\<close>
        and rc:\<open>\<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close> by blast
        have \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 implies not K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
              \<hookrightarrow> (((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies not K\<^sub>2) # \<Phi>))\<close>
          by (simp add: elims_part implies_not_e2)
        hence \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 implies not K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
                \<hookrightarrow>\<^bsup>Suc k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k)\<close>
          using fp relpowp_Suc_I2 by auto
        with rc show ?thesis by blast
      qed
      ultimately show ?case  using ImpliesNot.prems(2) by blast
  next
    case (TimeDelayedBy K\<^sub>1 \<delta>\<tau> K\<^sub>2 K\<^sub>3)
      have branches:
        \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = \<lbrakk> ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n
              \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          \<union> \<lbrakk> ((K\<^sub>1 \<Up> n) # (K\<^sub>2 @ n \<oplus> \<delta>\<tau> \<Rightarrow> K\<^sub>3) # \<Gamma>), n
              \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
        using HeronConf_interp_stepwise_timedelayed_cases by simp
      moreover have br1:
        \<open>\<rho> \<in> \<lbrakk> ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n
              \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          \<Longrightarrow> \<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k.
            ((\<Gamma>, n \<turnstile> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi>) \<triangleright> \<Phi>)
                \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))
            \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
      proof -
        assume h1: \<open>\<rho> \<in> \<lbrakk> ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n
                         \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
        then have \<open>\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k.
          ((((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>))
            \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))
          \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
          using h1 TimeDelayedBy.prems by simp
        from this obtain \<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k
          where fp:\<open>(((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n
                      \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>))
                    \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k)\<close>
            and rc:\<open>\<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close> by blast
        have \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi>) \<triangleright> \<Phi>)
              \<hookrightarrow> (((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n
                    \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>))\<close>
          by (simp add: elims_part timedelayed_e1)
        hence \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi>) \<triangleright> \<Phi>)
                \<hookrightarrow>\<^bsup>Suc k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k)\<close>
          using fp relpowp_Suc_I2 by auto
        with rc show ?thesis by blast
      qed
      moreover have br2:
        \<open>\<rho> \<in> \<lbrakk> ((K\<^sub>1 \<Up> n) # (K\<^sub>2 @ n \<oplus> \<delta>\<tau> \<Rightarrow> K\<^sub>3) # \<Gamma>), n
              \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          \<Longrightarrow> \<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k.
              ((\<Gamma>, n \<turnstile> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi>) \<triangleright> \<Phi>)
                \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))
              \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
      proof -
        assume h2: \<open>\<rho> \<in> \<lbrakk> ((K\<^sub>1 \<Up> n) # (K\<^sub>2 @ n \<oplus> \<delta>\<tau> \<Rightarrow> K\<^sub>3) # \<Gamma>), n
                    \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
        then have \<open>\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. ((((K\<^sub>1 \<Up> n) # (K\<^sub>2 @ n \<oplus> \<delta>\<tau> \<Rightarrow> K\<^sub>3) # \<Gamma>), n
                                 \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>))
                                 \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))
                                \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
          using h2 TimeDelayedBy.prems by simp
        from this obtain \<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k
          where fp:\<open>(((K\<^sub>1 \<Up> n) # (K\<^sub>2 @ n \<oplus> \<delta>\<tau> \<Rightarrow> K\<^sub>3) # \<Gamma>), n
                         \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>))
                       \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k)\<close>
            and rc:\<open>\<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close> by blast
        have \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi>) \<triangleright> \<Phi>)
              \<hookrightarrow> (((K\<^sub>1 \<Up> n) # (K\<^sub>2 @ n \<oplus> \<delta>\<tau> \<Rightarrow> K\<^sub>3) # \<Gamma>), n
                  \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>))\<close>
          by (simp add: elims_part timedelayed_e2)
        with fp relpowp_Suc_I2 have
          \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi>) \<triangleright> \<Phi>)
            \<hookrightarrow>\<^bsup>Suc k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k)\<close>
          by auto
        with rc show ?thesis by blast
      qed
      ultimately show ?case using TimeDelayedBy.prems(2) by blast
  next
    case (WeaklyPrecedes K\<^sub>1 K\<^sub>2)
      have \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((K\<^sub>1 weakly precedes K\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g =
        \<lbrakk> ((\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>\<le> K\<^sub>1 n\<rceil> \<in> (\<lambda>(x, y). x \<le> y)) # \<Gamma>), n
            \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 weakly precedes K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
        using HeronConf_interp_stepwise_weakly_precedes_cases by simp
      moreover have \<open>\<rho> \<in> \<lbrakk> ((\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>\<le> K\<^sub>1 n\<rceil> \<in> (\<lambda>(x, y). x \<le> y)) # \<Gamma>), n
                            \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 weakly precedes K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
            \<Longrightarrow> (\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. ((\<Gamma>, n \<turnstile> ((K\<^sub>1 weakly precedes K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
                                  \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))
                \<and> (\<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g))\<close>
      proof -
        assume \<open>\<rho> \<in> \<lbrakk> ((\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>\<le> K\<^sub>1 n\<rceil> \<in> (\<lambda>(x, y). x \<le> y)) # \<Gamma>), n
                        \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 weakly precedes K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
        hence \<open>\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. ((((\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>\<le> K\<^sub>1 n\<rceil> \<in> (\<lambda>(x, y). x \<le> y)) # \<Gamma>), n
                                  \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 weakly precedes K\<^sub>2) # \<Phi>))
                             \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))
                          \<and> (\<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g)\<close>
          using  WeaklyPrecedes.prems by simp
        from this obtain \<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k
          where fp:\<open>(((\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>\<le> K\<^sub>1 n\<rceil> \<in> (\<lambda>(x, y). x \<le> y)) # \<Gamma>), n
                                  \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 weakly precedes K\<^sub>2) # \<Phi>))
                             \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k)\<close>
            and rc:\<open>\<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close> by blast
        have \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 weakly precedes K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
                \<hookrightarrow> (((\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>\<le> K\<^sub>1 n\<rceil> \<in> (\<lambda>(x, y). x \<le> y)) # \<Gamma>), n
              \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 weakly precedes K\<^sub>2) # \<Phi>))\<close>
          by (simp add: elims_part weakly_precedes_e)
        with fp relpowp_Suc_I2 have \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 weakly precedes K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
                                      \<hookrightarrow>\<^bsup>Suc k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k)\<close>
          by auto
        with rc show ?thesis by blast
      qed
      ultimately show ?case using WeaklyPrecedes.prems(2) by blast
  next
    case (StrictlyPrecedes K\<^sub>1 K\<^sub>2)
      have \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((K\<^sub>1 strictly precedes K\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g =
        \<lbrakk> ((\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>< K\<^sub>1 n\<rceil> \<in> (\<lambda>(x, y). x \<le> y)) # \<Gamma>), n
          \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 strictly precedes K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
        using HeronConf_interp_stepwise_strictly_precedes_cases by simp
      moreover have \<open>\<rho> \<in> \<lbrakk> ((\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>< K\<^sub>1 n\<rceil> \<in> (\<lambda>(x, y). x \<le> y)) # \<Gamma>), n
                            \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 strictly precedes K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
            \<Longrightarrow> (\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. ((\<Gamma>, n \<turnstile> ((K\<^sub>1 strictly precedes K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
                                  \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))
                \<and> (\<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g))\<close>
      proof -
        assume \<open>\<rho> \<in> \<lbrakk> ((\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>< K\<^sub>1 n\<rceil> \<in> (\<lambda>(x, y). x \<le> y)) # \<Gamma>), n
                        \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 strictly precedes K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
        hence \<open>\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. ((((\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>< K\<^sub>1 n\<rceil> \<in> (\<lambda>(x, y). x \<le> y)) # \<Gamma>), n
                                  \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 strictly precedes K\<^sub>2) # \<Phi>))
                             \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))
                            \<and> (\<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g)\<close>
          using  StrictlyPrecedes.prems by simp
        from this obtain \<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k
          where fp:\<open>(((\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>< K\<^sub>1 n\<rceil> \<in> (\<lambda>(x, y). x \<le> y)) # \<Gamma>), n
                                  \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 strictly precedes K\<^sub>2) # \<Phi>))
                             \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k)\<close>
            and rc:\<open>\<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close> by blast
        have \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 strictly precedes K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
                \<hookrightarrow> (((\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>< K\<^sub>1 n\<rceil> \<in> (\<lambda>(x, y). x \<le> y)) # \<Gamma>), n
              \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 strictly precedes K\<^sub>2) # \<Phi>))\<close>
          by (simp add: elims_part strictly_precedes_e)
        with fp relpowp_Suc_I2 have \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 strictly precedes K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
                                      \<hookrightarrow>\<^bsup>Suc k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k)\<close>
          by auto
        with rc show ?thesis by blast
      qed
      ultimately show ?case using StrictlyPrecedes.prems(2) by blast
  next
    case (Kills K\<^sub>1 K\<^sub>2)
      have branches: \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((K\<^sub>1 kills K\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = \<lbrakk> ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 kills K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          \<union> \<lbrakk> ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> \<ge> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 kills K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
        using HeronConf_interp_stepwise_kills_cases by simp
      moreover have br1: \<open>\<rho> \<in> \<lbrakk> ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 kills K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                \<Longrightarrow> \<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. ((\<Gamma>, n \<turnstile> ((K\<^sub>1 kills K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
                                    \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))
                  \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
      proof -
        assume h1: \<open>\<rho> \<in> \<lbrakk> ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 kills K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
        then have \<open>\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k.
                    ((((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 kills K\<^sub>2) # \<Phi>))
                    \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))
                  \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
          using h1 Kills.prems by simp
        from this obtain \<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k where
          fp:\<open>((((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 kills K\<^sub>2) # \<Phi>))
                \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))\<close>
          and rc:\<open>\<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close> by blast
        have pc:\<open>(\<Gamma>, n \<turnstile> (K\<^sub>1 kills K\<^sub>2) # \<Psi> \<triangleright> \<Phi>)
                  \<hookrightarrow> (((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 kills K\<^sub>2) # \<Phi>))\<close>
          by (simp add: elims_part kills_e1)
        hence \<open>(\<Gamma>, n \<turnstile> (K\<^sub>1 kills K\<^sub>2) # \<Psi> \<triangleright> \<Phi>) \<hookrightarrow>\<^bsup>Suc k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k)\<close>
          using fp relpowp_Suc_I2 by auto
        with rc show ?thesis by blast
      qed
      moreover have br2:
        \<open>\<rho> \<in> \<lbrakk> ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> \<ge> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 kills K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          \<Longrightarrow> \<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. ((\<Gamma>, n \<turnstile> ((K\<^sub>1 kills K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
                                \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))
                          \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
      proof -
        assume h2: \<open>\<rho> \<in> \<lbrakk>((K\<^sub>1 \<Up> n)#(K\<^sub>2 \<not>\<Up> \<ge> n)#\<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 kills K\<^sub>2)#\<Phi>)\<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
        then have \<open>\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. (
                    (((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> \<ge> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 kills K\<^sub>2) # \<Phi>))
                      \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k)
                    ) \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
          using h2 Kills.prems by simp
        from this obtain \<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k where
            fp:\<open>(((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> \<ge> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 kills K\<^sub>2) # \<Phi>))
                \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k)\<close>
        and rc:\<open>\<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close> by blast
        have \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 kills K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
              \<hookrightarrow> (((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> \<ge> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 kills K\<^sub>2) # \<Phi>))\<close>
          by (simp add: elims_part kills_e2)
        hence \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 kills K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>) \<hookrightarrow>\<^bsup>Suc k\<^esup> (\<Gamma>\<^sub>k, Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k)\<close>
          using fp relpowp_Suc_I2 by auto
        with rc show ?thesis by blast
      qed
      ultimately show ?case using Kills.prems(2) by blast
  qed
qed

lemma instant_index_increase_generalized:
  assumes \<open>n < n\<^sub>k\<close>
  assumes \<open>\<rho> \<in> \<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
  shows   \<open>\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. ((\<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>) \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, n\<^sub>k \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))
                         \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, n\<^sub>k \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
proof -
  obtain \<delta>k where diff: \<open>n\<^sub>k = \<delta>k + Suc n\<close>
    using add.commute assms(1) less_iff_Suc_add by auto
  show ?thesis
    proof (subst diff, subst diff, insert assms(2), induct \<delta>k)
      case 0  thus ?case
        using instant_index_increase assms(2) by simp
    next
      case (Suc \<delta>k)
        have f0: \<open>\<rho> \<in> \<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<Longrightarrow> \<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k.
                  ((\<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>) \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, \<delta>k + Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))
                \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, \<delta>k + Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
          using Suc.hyps by blast
        obtain \<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k
          where cont: \<open>((\<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>) \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, \<delta>k + Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))
                      \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, \<delta>k + Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
          using f0 assms(1) Suc.prems by blast
        then have fcontinue: \<open>\<exists>\<Gamma>\<^sub>k' \<Psi>\<^sub>k' \<Phi>\<^sub>k' k'. ((\<Gamma>\<^sub>k, \<delta>k + Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k)
                                       \<hookrightarrow>\<^bsup>k'\<^esup> (\<Gamma>\<^sub>k', Suc (\<delta>k + Suc n) \<turnstile> \<Psi>\<^sub>k' \<triangleright> \<Phi>\<^sub>k'))
                                   \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k', Suc (\<delta>k + Suc n) \<turnstile> \<Psi>\<^sub>k' \<triangleright> \<Phi>\<^sub>k' \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
          using f0 cont instant_index_increase by blast
        obtain \<Gamma>\<^sub>k' \<Psi>\<^sub>k' \<Phi>\<^sub>k' k'
          where cont2: \<open>((\<Gamma>\<^sub>k, \<delta>k + Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k)
                        \<hookrightarrow>\<^bsup>k'\<^esup> (\<Gamma>\<^sub>k', Suc (\<delta>k + Suc n) \<turnstile> \<Psi>\<^sub>k' \<triangleright> \<Phi>\<^sub>k'))
                      \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k', Suc (\<delta>k + Suc n) \<turnstile> \<Psi>\<^sub>k' \<triangleright> \<Phi>\<^sub>k' \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
          using Suc.prems using fcontinue cont by blast
        have trans: \<open>(\<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>) \<hookrightarrow>\<^bsup>k + k'\<^esup> (\<Gamma>\<^sub>k', Suc (\<delta>k + Suc n) \<turnstile> \<Psi>\<^sub>k' \<triangleright> \<Phi>\<^sub>k')\<close>
          using operational_semantics_trans_generalized cont cont2 by blast
        moreover have suc_assoc: \<open>Suc \<delta>k + Suc n = Suc (\<delta>k + Suc n)\<close> by arith
        ultimately show ?case
          proof (subst suc_assoc)
            show \<open>\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k.
                   ((\<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>) \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, Suc (\<delta>k + Suc n) \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))
                  \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, Suc \<delta>k + Suc n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
            using cont2 local.trans by auto
          qed
    qed
qed

text\<open>
  Any run that belongs to a specification @{term \<open>\<Psi>\<close>} has a corresponding 
  configuration that develops it up to the @{term \<open>n\<close>}\textsuperscript{th} instant.
\<close>
theorem progress:
  assumes \<open>\<rho> \<in> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
    shows \<open>\<exists>k \<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k. (([], 0 \<turnstile> \<Psi> \<triangleright> [])  \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))
                         \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, n \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
proof -
  have 1:\<open>\<exists>\<Gamma>\<^sub>k \<Psi>\<^sub>k \<Phi>\<^sub>k k. (([], 0 \<turnstile> \<Psi> \<triangleright> []) \<hookrightarrow>\<^bsup>k\<^esup> (\<Gamma>\<^sub>k, 0 \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k))
                      \<and> \<rho> \<in> \<lbrakk> \<Gamma>\<^sub>k, 0 \<turnstile> \<Psi>\<^sub>k \<triangleright> \<Phi>\<^sub>k \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
    using assms relpowp_0_I solve_start by fastforce
  show ?thesis
  proof (cases \<open>n = 0\<close>)
    case True
      thus ?thesis using assms relpowp_0_I solve_start by fastforce
  next
    case False hence pos:\<open>n > 0\<close> by simp
      from assms solve_start have \<open>\<rho> \<in> \<lbrakk> [], 0 \<turnstile> \<Psi> \<triangleright> [] \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<close> by blast
      from instant_index_increase_generalized[OF pos this] show ?thesis by blast
  qed
qed

section \<open>Local termination\<close>
text \<open>
  Here, we prove that the computation of an instant in a run always terminates.
  Since this computation terminates when the list of constraints for the present
  instant becomes empty, we introduce a measure for this formula.
\<close>
primrec measure_interpretation :: \<open>'\<tau>::linordered_field TESL_formula \<Rightarrow> nat\<close> (\<open>\<mu>\<close>)
where
  \<open>\<mu> [] = (0::nat)\<close>
| \<open>\<mu> (\<phi> # \<Phi>) = (case \<phi> of
                      _ sporadic _ on _ \<Rightarrow> 1 + \<mu> \<Phi>
                    | _                 \<Rightarrow> 2 + \<mu> \<Phi>)\<close>

fun measure_interpretation_config :: \<open>'\<tau>::linordered_field config \<Rightarrow> nat\<close> (\<open>\<mu>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>)
where
  \<open>\<mu>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g (\<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi>) = \<mu> \<Psi>\<close>

text \<open>
  We then show that the elimination rules make this measure decrease.
\<close>
lemma elimation_rules_strictly_decreasing:
  assumes \<open>(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1)  \<hookrightarrow>\<^sub>e  (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2)\<close>
    shows \<open>\<mu> \<Psi>\<^sub>1 > \<mu> \<Psi>\<^sub>2\<close>
using assms by (auto elim: operational_semantics_elim.cases)

lemma elimation_rules_strictly_decreasing_meas:
  assumes \<open>(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1)  \<hookrightarrow>\<^sub>e  (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2)\<close>
    shows \<open>(\<Psi>\<^sub>2, \<Psi>\<^sub>1) \<in> measure \<mu>\<close>
using assms by (auto elim: operational_semantics_elim.cases)

lemma elimation_rules_strictly_decreasing_meas':
  assumes \<open>\<S>\<^sub>1  \<hookrightarrow>\<^sub>e  \<S>\<^sub>2\<close>
  shows \<open>(\<S>\<^sub>2, \<S>\<^sub>1) \<in> measure \<mu>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
proof -
  from assms obtain \<Gamma>\<^sub>1 n\<^sub>1 \<Psi>\<^sub>1 \<Phi>\<^sub>1 where p1:\<open>\<S>\<^sub>1 = (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1)\<close>
    using measure_interpretation_config.cases by blast
  from assms obtain \<Gamma>\<^sub>2 n\<^sub>2 \<Psi>\<^sub>2 \<Phi>\<^sub>2 where p2:\<open>\<S>\<^sub>2 = (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2)\<close>
    using measure_interpretation_config.cases by blast
  from elimation_rules_strictly_decreasing_meas assms p1 p2
    have \<open>(\<Psi>\<^sub>2, \<Psi>\<^sub>1) \<in> measure \<mu>\<close> by blast
  hence \<open>\<mu> \<Psi>\<^sub>2 < \<mu> \<Psi>\<^sub>1\<close> by simp
  hence \<open>\<mu>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2) < \<mu>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1)\<close> by simp
  with p1 p2 show ?thesis by simp
qed

text \<open>
  Therefore, the relation made up of elimination rules is well-founded and the
  computation of an instant terminates.
\<close>
theorem instant_computation_termination:
  \<open>wfP (\<lambda>(\<S>\<^sub>1::'a::linordered_field config) \<S>\<^sub>2. (\<S>\<^sub>1  \<hookrightarrow>\<^sub>e\<^sup>\<leftarrow>  \<S>\<^sub>2))\<close>
proof (simp add: wfP_def)
  show \<open>wf {((\<S>\<^sub>1::'a::linordered_field config), \<S>\<^sub>2). \<S>\<^sub>1 \<hookrightarrow>\<^sub>e\<^sup>\<leftarrow> \<S>\<^sub>2}\<close>
  proof (rule wf_subset)
    have \<open>measure \<mu>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = {(\<S>\<^sub>2, (\<S>\<^sub>1::'a::linordered_field config)).
                               \<mu>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<S>\<^sub>2 < \<mu>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<S>\<^sub>1}\<close>
      by (simp add: inv_image_def less_eq measure_def)
    thus \<open>{((\<S>\<^sub>1::'a::linordered_field config), \<S>\<^sub>2). \<S>\<^sub>1 \<hookrightarrow>\<^sub>e\<^sup>\<leftarrow> \<S>\<^sub>2} \<subseteq> (measure \<mu>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g)\<close>
      using elimation_rules_strictly_decreasing_meas'
            operational_semantics_elim_inv_def by blast
  next
    show \<open>wf (measure measure_interpretation_config)\<close> by simp
  qed
qed


end
