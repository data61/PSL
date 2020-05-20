theory Conf
imports Store
begin

section \<open>Configurations, Subsumption and Symbolic Execution\<close>

text \<open>In this section, we first introduce most elements related to our modeling of program 
behaviors. We first define the type of configurations, on which symbolic execution performs, and 
define the various concepts we will rely upon in the following and state and prove properties about 
them. Then, we introduce symbolic execution. After giving a number of basic properties about 
symbolic execution, we prove that symbolic execution is monotonic with respect to the subsumption 
relation, which is a crucial point in order to prove the main theorems of \verb?RB.thy?. Moreover, 
Isabelle/HOL requires the actual formalization of a number of facts one would not worry when 
implementing or writing a sketch proof. Here, we will need to prove that there exist successors of 
the configurations on which symbolic execution is performed. Although this seems quite obvious in 
practice, proofs of such facts will be needed a number of times in the following theories. Finally, 
we define the feasibility of a sequence of labels.\<close>


subsection \<open>Basic Definitions and Properties\<close>

subsubsection\<open>Configurations\<close>

text \<open>Configurations are pairs @{term "(store,pred)"} where:
\begin{itemize}
  \item @{term "store"} is a store mapping program variable to symbolic variables,
  \item @{term "pred"} is a set of boolean expressions over program variables whose conjunction is
the actual path predicate.
\end{itemize}\<close>


record ('v,'d) conf = 
  store :: "'v store"
  pred  :: "('v symvar,'d) bexp set"


subsubsection \<open>Symbolic variables of a configuration.\<close>

text \<open>The set of symbolic variables of a configuration is the union of the set of symbolic 
variables of its store component with the set of variables of its path predicate.\<close>


definition symvars :: 
  "('v,'d) conf \<Rightarrow> 'v symvar set" 
where
  "symvars c = Store.symvars (store c) \<union> Bexp.vars (conjunct (pred c))"


subsubsection \<open>Freshness.\<close>

text \<open>A symbolic variable is said to be fresh for a configuration if it is not an element of its 
set of symbolic variables.\<close>


definition fresh_symvar :: 
  "'v symvar \<Rightarrow> ('v,'d) conf \<Rightarrow> bool" 
where
  "fresh_symvar sv c = (sv \<notin> symvars c)"


subsubsection \<open>Satisfiability\<close>

text \<open>A configuration is said to be satisfiable if its path predicate is satisfiable.\<close>


abbreviation sat :: 
  "('v,'d) conf \<Rightarrow> bool" 
where
  "sat c \<equiv> Bexp.sat (conjunct (pred c))"


subsubsection \<open>States of a configuration\<close>

text \<open>Configurations represent sets of program states. The set of program states represented by a 
configuration, or simply its set of program states, is defined as the set of program states such that 
consistent symbolic states wrt.\ the store component of the configuration satisfies its path 
predicate.\<close>


definition states :: 
  "('v,'d) conf \<Rightarrow> ('v,'d) state set" 
where
 "states c = {\<sigma>. \<exists> \<sigma>\<^sub>s\<^sub>y\<^sub>m. consistent \<sigma> \<sigma>\<^sub>s\<^sub>y\<^sub>m (store c) \<and> conjunct (pred c) \<sigma>\<^sub>s\<^sub>y\<^sub>m}"


text \<open>A configuration is satisfiable if and only if its set of states is not empty.\<close>


lemma sat_eq :  
  "sat c = (states c \<noteq> {})"
using consistentI2 by (simp add : sat_def states_def) fast



subsubsection \<open>Subsumption\<close>

text \<open>A configuration @{term "c\<^sub>2"} is subsumed by a configuration @{term "c\<^sub>1"} if the set of 
states of @{term "c\<^sub>2"} is a subset of the set of states of @{term "c\<^sub>1"}.\<close>


definition subsums :: 
  "('v,'d) conf \<Rightarrow> ('v,'d) conf \<Rightarrow> bool" (infixl "\<sqsubseteq>" 55) 
where     
  "c\<^sub>2 \<sqsubseteq> c\<^sub>1 \<equiv> (states c\<^sub>2 \<subseteq> states c\<^sub>1)"


text \<open>The subsumption relation is reflexive and transitive.\<close>


lemma subsums_refl :
  "c \<sqsubseteq> c"
by (simp only : subsums_def)


lemma subsums_trans :
  "c1 \<sqsubseteq> c2 \<Longrightarrow> c2 \<sqsubseteq> c3 \<Longrightarrow> c1 \<sqsubseteq> c3"
unfolding subsums_def by simp


text \<open>However, it is not anti-symmetric. This is due to the fact that different configurations 
can have the same sets of program states. However, the following lemma trivially follows the 
definition of subsumption.\<close>


lemma
  assumes "c1 \<sqsubseteq> c2"
  assumes "c2 \<sqsubseteq> c1"
  shows   "states c1 = states c2"
using assms by (simp add : subsums_def)


text \<open>A satisfiable configuration can only be subsumed by satisfiable configurations.\<close>


lemma sat_sub_by_sat :
  assumes "sat c\<^sub>2"
  and     "c\<^sub>2 \<sqsubseteq> c\<^sub>1"
  shows   "sat c\<^sub>1"
using assms sat_eq[of c\<^sub>1] sat_eq[of c\<^sub>2] 
by (simp add : subsums_def) fast


text \<open>On the other hand, an unsatisfiable configuration can only subsume unsatisfiable 
configurations.\<close>


lemma unsat_subs_unsat :
  assumes "\<not> sat c1"
  assumes "c2 \<sqsubseteq> c1"
  shows   "\<not> sat c2"
using assms sat_eq[of c1] sat_eq[of c2] 
by (simp add : subsums_def)


subsubsection \<open>Semantics of a configuration\<close>

text \<open>The semantics of a configuration @{term "c"} is a boolean expression @{term "e"} over 
program states associating \emph{true} to a program state if it is a state of @{term "c"}. In 
practice, given two configurations @{term "c\<^sub>1"} and @{term "c\<^sub>2"}, it is not possible to enumerate 
their sets of states to establish the inclusion in order to detect a subsumption. We detect the 
subsumption of the former by the latter by asking a constraint solver if @{term "sem c\<^sub>1"} entails 
@{term "sem c\<^sub>2"}. The following theorem shows that the way we detect subsumption in practice is 
correct.\<close>


definition sem :: 
  "('v,'d) conf \<Rightarrow> ('v,'d) bexp" 
where
 "sem c = (\<lambda> \<sigma>. \<sigma> \<in> states c)"


theorem
  "c\<^sub>2 \<sqsubseteq> c\<^sub>1 \<longleftrightarrow> sem c\<^sub>2 \<Turnstile>\<^sub>B sem c\<^sub>1"
unfolding subsums_def sem_def subset_iff entails_def by (rule refl)


subsubsection \<open>Abstractions\<close>

text \<open>Abstracting a configuration consists in removing a given expression from its @{term "pred"} 
component, i.e.\ weakening its path predicate. This definition of abstraction motivates the fact 
that the @{term "pred"} component of configurations has been defined as a set of boolean expressions 
instead of a boolean expression.\<close>


definition abstract ::
  "('v,'d) conf \<Rightarrow> ('v,'d) conf \<Rightarrow> bool"
where
  "abstract c c\<^sub>a \<equiv> c \<sqsubseteq> c\<^sub>a"


subsubsection \<open>Entailment\<close>

text \<open>A configuration \emph{entails} a boolean expression if its semantics entails this expression. 
This is equivalent to say that this expression holds for any state of this configuration.\<close>


abbreviation entails :: 
  "('v,'d) conf \<Rightarrow> ('v,'d) bexp \<Rightarrow> bool" (infixl "\<Turnstile>\<^sub>c" 55) 
where
  "c \<Turnstile>\<^sub>c \<phi> \<equiv> sem c \<Turnstile>\<^sub>B \<phi>"

lemma 
  "sem c \<Turnstile>\<^sub>B e \<longleftrightarrow> (\<forall> \<sigma> \<in> states c. e \<sigma>)"
by (auto simp add : states_def sem_def entails_def)



end
