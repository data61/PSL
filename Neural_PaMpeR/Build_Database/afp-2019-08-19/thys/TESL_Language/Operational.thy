chapter \<open>Operational Semantics\<close>
text\<open>\label{chap:operational_semantics}\<close>

theory Operational
imports
  SymbolicPrimitive

begin

text\<open>
  The operational semantics defines rules to build symbolic runs from a TESL 
  specification (a set of TESL formulae).
  Symbolic runs are described using the symbolic primitives presented in the 
  previous chapter.
  Therefore, the operational semantics compiles a set of constraints on runs, 
  as defined by the denotational semantics, into a set of symbolic constraints 
  on the instants of the runs. Concrete runs can then be obtained by solving the 
  constraints at each instant.
\<close>

section\<open>Operational steps\<close>

text \<open>
  We introduce a notation to describe configurations:
  \<^item> @{term \<open>\<Gamma>\<close>} is the context, the set of symbolic constraints on past instants of the run;
  \<^item> @{term \<open>n\<close>} is the index of the current instant, the present;
  \<^item> @{term \<open>\<Psi>\<close>} is the TESL formula that must be satisfied at the current instant (present);
  \<^item> @{term \<open>\<Phi>\<close>} is the TESL formula that must be satisfied for the following instants (the future).
\<close>
abbreviation uncurry_conf
  ::\<open>('\<tau>::linordered_field) system \<Rightarrow> instant_index \<Rightarrow> '\<tau> TESL_formula \<Rightarrow> '\<tau> TESL_formula
      \<Rightarrow> '\<tau> config\<close>                                                  (\<open>_, _ \<turnstile> _ \<triangleright> _\<close> 80)
where
  \<open>\<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<equiv> (\<Gamma>, n, \<Psi>, \<Phi>)\<close>

text \<open>
  The only introduction rule allows us to progress to the next instant 
  when there are no more constraints to satisfy for the present instant.
\<close>
inductive operational_semantics_intro
  ::\<open>('\<tau>::linordered_field) config \<Rightarrow> '\<tau> config \<Rightarrow> bool\<close>              (\<open>_ \<hookrightarrow>\<^sub>i _\<close> 70)
where
  instant_i:
  \<open>(\<Gamma>, n \<turnstile> [] \<triangleright> \<Phi>) \<hookrightarrow>\<^sub>i  (\<Gamma>, Suc n \<turnstile> \<Phi> \<triangleright> [])\<close>

text \<open>
  The elimination rules describe how TESL formulae for the present are transformed 
  into constraints on the past and on the future.
\<close>
inductive operational_semantics_elim
  ::\<open>('\<tau>::linordered_field) config \<Rightarrow> '\<tau> config \<Rightarrow> bool\<close>              (\<open>_ \<hookrightarrow>\<^sub>e _\<close> 70)
where
  sporadic_on_e1:
\<comment> \<open>A sporadic constraint can be ignored in the present and rejected into the future.\<close>
  \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (\<Gamma>, n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi>))\<close>
| sporadic_on_e2:
\<comment> \<open>It can also be handled in the present by making the clock tick and have 
  the expected time. Once it has been handled, it is no longer a constraint 
  to satisfy, so it disappears from the future.\<close>
  \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Down> n @ \<tau>) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> \<Phi>)\<close>
| tagrel_e:
\<comment> \<open>A relation between time scales has to be obeyed at every instant.\<close>
  \<open>(\<Gamma>, n \<turnstile> ((time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((\<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n)\<rfloor> \<in> R) # \<Gamma>), n
              \<turnstile> \<Psi> \<triangleright> ((time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R) # \<Phi>))\<close>
| implies_e1:
\<comment> \<open>An implication can be handled in the present by forbidding a tick of the master
  clock. The implication is copied back into the future because it holds for 
  the whole run.\<close>
  \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 implies K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>))\<close>
| implies_e2:
\<comment> \<open>It can also be handled in the present by making both the master and the slave
    clocks tick.\<close>
  \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 implies K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>))\<close>
| implies_not_e1:
\<comment> \<open>A negative implication can be handled in the present by forbidding a tick of 
  the master clock. The implication is copied back into the future because 
  it holds for the whole run.\<close>
  \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 implies not K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies not K\<^sub>2) # \<Phi>))\<close>
| implies_not_e2:
\<comment> \<open>It can also be handled in the present by making the master clock ticks and 
    forbidding a tick on the slave clock.\<close>
  \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 implies not K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies not K\<^sub>2) # \<Phi>))\<close>
| timedelayed_e1:
\<comment> \<open>A timed delayed implication can be handled by forbidding a tick on 
    the master clock.\<close>
  \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>))\<close>
| timedelayed_e2:
\<comment> \<open>It can also be handled by making the master clock tick and adding a constraint 
    that makes the slave clock tick when the delay has elapsed on the measuring clock.\<close>
  \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((K\<^sub>1 \<Up> n) # (K\<^sub>2 @ n \<oplus> \<delta>\<tau> \<Rightarrow> K\<^sub>3) # \<Gamma>), n
            \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>))\<close>
| weakly_precedes_e:
\<comment> \<open>A weak precedence relation has to hold at every instant.\<close>
  \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 weakly precedes K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>\<le> K\<^sub>1 n\<rceil> \<in> (\<lambda>(x,y). x\<le>y)) # \<Gamma>), n
            \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 weakly precedes K\<^sub>2) # \<Phi>))\<close>
| strictly_precedes_e:
\<comment> \<open>A strict precedence relation has to hold at every instant.\<close>
  \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 strictly precedes K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>< K\<^sub>1 n\<rceil> \<in> (\<lambda>(x,y). x\<le>y)) # \<Gamma>), n
            \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 strictly precedes K\<^sub>2) # \<Phi>))\<close>
| kills_e1:
\<comment> \<open>A kill can be handled by forbidding a tick of the triggering clock.\<close>
  \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 kills K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 kills K\<^sub>2) # \<Phi>))\<close>
| kills_e2:
\<comment> \<open>It can also be handled by making the triggering clock tick and by forbidding 
    any further tick of the killed clock.\<close>
  \<open>(\<Gamma>, n \<turnstile> ((K\<^sub>1 kills K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>)
     \<hookrightarrow>\<^sub>e  (((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> \<ge> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 kills K\<^sub>2) # \<Phi>))\<close>

text \<open>
  A step of the operational semantics is either the application of the introduction 
  rule or the application of an elimination rule.
\<close>
inductive operational_semantics_step
  ::\<open>('\<tau>::linordered_field) config \<Rightarrow> '\<tau> config \<Rightarrow> bool\<close>              (\<open>_ \<hookrightarrow> _\<close> 70)
where
  intro_part:
  \<open>(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1)  \<hookrightarrow>\<^sub>i  (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2)
    \<Longrightarrow> (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1)  \<hookrightarrow>  (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2)\<close>
| elims_part:
  \<open>(\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1)  \<hookrightarrow>\<^sub>e  (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2)
    \<Longrightarrow> (\<Gamma>\<^sub>1, n\<^sub>1 \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1)  \<hookrightarrow>  (\<Gamma>\<^sub>2, n\<^sub>2 \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2)\<close>

text \<open>
  We introduce notations for the reflexive transitive closure of the operational 
  semantic step, its transitive closure and its reflexive closure.
\<close>
abbreviation operational_semantics_step_rtranclp
  ::\<open>('\<tau>::linordered_field) config \<Rightarrow> '\<tau> config \<Rightarrow> bool\<close>              (\<open>_ \<hookrightarrow>\<^sup>*\<^sup>* _\<close> 70)
where
  \<open>\<C>\<^sub>1 \<hookrightarrow>\<^sup>*\<^sup>* \<C>\<^sub>2 \<equiv> operational_semantics_step\<^sup>*\<^sup>* \<C>\<^sub>1 \<C>\<^sub>2\<close>

abbreviation operational_semantics_step_tranclp
  ::\<open>('\<tau>::linordered_field) config \<Rightarrow> '\<tau> config \<Rightarrow> bool\<close>              (\<open>_ \<hookrightarrow>\<^sup>+\<^sup>+ _\<close> 70)
where
  \<open>\<C>\<^sub>1 \<hookrightarrow>\<^sup>+\<^sup>+ \<C>\<^sub>2 \<equiv> operational_semantics_step\<^sup>+\<^sup>+ \<C>\<^sub>1 \<C>\<^sub>2\<close>

abbreviation operational_semantics_step_reflclp
  ::\<open>('\<tau>::linordered_field) config \<Rightarrow> '\<tau> config \<Rightarrow> bool\<close>              (\<open>_ \<hookrightarrow>\<^sup>=\<^sup>= _\<close> 70)
where
  \<open>\<C>\<^sub>1 \<hookrightarrow>\<^sup>=\<^sup>= \<C>\<^sub>2 \<equiv> operational_semantics_step\<^sup>=\<^sup>= \<C>\<^sub>1 \<C>\<^sub>2\<close>

abbreviation operational_semantics_step_relpowp
  ::\<open>('\<tau>::linordered_field) config \<Rightarrow> nat \<Rightarrow> '\<tau> config \<Rightarrow> bool\<close>       (\<open>_ \<hookrightarrow>\<^bsup>_\<^esup> _\<close> 70)
where
  \<open>\<C>\<^sub>1 \<hookrightarrow>\<^bsup>n\<^esup> \<C>\<^sub>2 \<equiv> (operational_semantics_step ^^ n) \<C>\<^sub>1 \<C>\<^sub>2\<close>

definition operational_semantics_elim_inv
  ::\<open>('\<tau>::linordered_field) config \<Rightarrow> '\<tau> config \<Rightarrow> bool\<close>              (\<open>_ \<hookrightarrow>\<^sub>e\<^sup>\<leftarrow> _\<close> 70)
where
  \<open>\<C>\<^sub>1 \<hookrightarrow>\<^sub>e\<^sup>\<leftarrow> \<C>\<^sub>2 \<equiv> \<C>\<^sub>2 \<hookrightarrow>\<^sub>e \<C>\<^sub>1\<close>


section\<open>Basic Lemmas\<close>

text \<open>
  If a configuration can be reached in @{term \<open>m\<close>} steps from a configuration that 
  can be reached in @{term \<open>n\<close>} steps from an original configuration, then it can be 
  reached in @{term \<open>n+m\<close>} steps from the original configuration.
\<close>
lemma operational_semantics_trans_generalized:
  assumes \<open>\<C>\<^sub>1 \<hookrightarrow>\<^bsup>n\<^esup> \<C>\<^sub>2\<close>
  assumes \<open>\<C>\<^sub>2 \<hookrightarrow>\<^bsup>m\<^esup> \<C>\<^sub>3\<close>
    shows \<open>\<C>\<^sub>1 \<hookrightarrow>\<^bsup>n + m\<^esup> \<C>\<^sub>3\<close>
using relcompp.relcompI[of  \<open>operational_semantics_step ^^ n\<close> _ _ 
                            \<open>operational_semantics_step ^^ m\<close>, OF assms]
by (simp add: relpowp_add) 

text \<open>
  We consider the set of configurations that can be reached in one operational
  step from a given configuration.
\<close>
abbreviation Cnext_solve
  ::\<open>('\<tau>::linordered_field) config \<Rightarrow> '\<tau> config set\<close> (\<open>\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t _\<close>)
where
  \<open>\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t \<S> \<equiv> { \<S>'. \<S> \<hookrightarrow> \<S>' }\<close>

text \<open>
  Advancing to the next instant is possible when there are no more constraints 
  on the current instant.
\<close>
lemma Cnext_solve_instant:
  \<open>(\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> [] \<triangleright> \<Phi>)) \<supseteq> { \<Gamma>, Suc n \<turnstile> \<Phi> \<triangleright> [] }\<close>
by (simp add: operational_semantics_step.simps operational_semantics_intro.instant_i)

text \<open>
  The following lemmas state that the configurations produced by the elimination 
  rules of the operational semantics belong to the configurations that can be 
  reached in one step.
\<close>
lemma Cnext_solve_sporadicon:
  \<open>(\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>))
    \<supseteq> { \<Gamma>, n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi>),
        ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Down> n @ \<tau>) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> \<Phi> }\<close>
by (simp add: operational_semantics_step.simps
              operational_semantics_elim.sporadic_on_e1
              operational_semantics_elim.sporadic_on_e2)

lemma Cnext_solve_tagrel:
  \<open>(\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> ((time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R) # \<Psi>) \<triangleright> \<Phi>))
    \<supseteq> { ((\<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n)\<rfloor> \<in> R) # \<Gamma>),n
          \<turnstile> \<Psi> \<triangleright> ((time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R) # \<Phi>) }\<close>
by (simp add: operational_semantics_step.simps operational_semantics_elim.tagrel_e)

lemma Cnext_solve_implies:
  \<open>(\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> ((K\<^sub>1 implies K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>))
    \<supseteq> { ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>),
         ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>) }\<close>
by (simp add: operational_semantics_step.simps operational_semantics_elim.implies_e1
              operational_semantics_elim.implies_e2)

lemma Cnext_solve_implies_not:
  \<open>(\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> ((K\<^sub>1 implies not K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>))
    \<supseteq> { ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies not K\<^sub>2) # \<Phi>),
        ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies not K\<^sub>2) # \<Phi>) }\<close>
by (simp add: operational_semantics_step.simps
              operational_semantics_elim.implies_not_e1
              operational_semantics_elim.implies_not_e2)

lemma Cnext_solve_timedelayed:
  \<open>(\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi>) \<triangleright> \<Phi>))
    \<supseteq> { ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>),
        ((K\<^sub>1 \<Up> n) # (K\<^sub>2 @ n \<oplus> \<delta>\<tau> \<Rightarrow> K\<^sub>3) # \<Gamma>), n
          \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>) }\<close>
by (simp add: operational_semantics_step.simps
              operational_semantics_elim.timedelayed_e1
              operational_semantics_elim.timedelayed_e2)

lemma Cnext_solve_weakly_precedes:
  \<open>(\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> ((K\<^sub>1 weakly precedes K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>))
    \<supseteq> { ((\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>\<le> K\<^sub>1 n\<rceil> \<in> (\<lambda>(x,y). x\<le>y)) # \<Gamma>), n
          \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 weakly precedes K\<^sub>2) # \<Phi>) }\<close>
by (simp add: operational_semantics_step.simps
              operational_semantics_elim.weakly_precedes_e)

lemma Cnext_solve_strictly_precedes:
  \<open>(\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> ((K\<^sub>1 strictly precedes K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>))
    \<supseteq> { ((\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>< K\<^sub>1 n\<rceil> \<in> (\<lambda>(x,y). x\<le>y)) # \<Gamma>), n
          \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 strictly precedes K\<^sub>2) # \<Phi>) }\<close>
by (simp add: operational_semantics_step.simps
              operational_semantics_elim.strictly_precedes_e)

lemma Cnext_solve_kills:
  \<open>(\<C>\<^sub>n\<^sub>e\<^sub>x\<^sub>t (\<Gamma>, n \<turnstile> ((K\<^sub>1 kills K\<^sub>2) # \<Psi>) \<triangleright> \<Phi>))
    \<supseteq> { ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 kills K\<^sub>2) # \<Phi>),
        ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> \<ge> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 kills K\<^sub>2) # \<Phi>) }\<close>
by (simp add: operational_semantics_step.simps operational_semantics_elim.kills_e1
              operational_semantics_elim.kills_e2)

text \<open>
  An empty specification can be reduced to an empty specification for 
  an arbitrary number of steps.
\<close>
lemma empty_spec_reductions:
  \<open>([], 0 \<turnstile> [] \<triangleright> []) \<hookrightarrow>\<^bsup>k\<^esup> ([], k \<turnstile> [] \<triangleright> [])\<close>
proof (induct k)
  case 0 thus ?case by simp
next
  case Suc thus ?case
    using instant_i operational_semantics_step.simps by fastforce 
qed

end
