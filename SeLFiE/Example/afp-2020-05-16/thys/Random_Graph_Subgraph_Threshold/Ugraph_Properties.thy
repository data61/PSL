section\<open>Classes and properties of graphs\<close>

theory Ugraph_Properties
imports
  Ugraph_Lemmas
  Girth_Chromatic.Girth_Chromatic
begin

text\<open>A ``graph property'' is a set of graphs which is closed under isomorphism.\<close>

type_synonym ugraph_class = "ugraph set"

definition ugraph_property :: "ugraph_class \<Rightarrow> bool" where
"ugraph_property C \<equiv> \<forall>G \<in> C. \<forall>G'. G \<simeq> G' \<longrightarrow> G' \<in> C"

abbreviation prob_in_class :: "(nat \<Rightarrow> real) \<Rightarrow> ugraph_class \<Rightarrow> nat \<Rightarrow> real" where
"prob_in_class p c n \<equiv> probGn p n (\<lambda>es. edge_space.edge_ugraph n es \<in> c)"

text\<open>From now on, we consider random graphs not with fixed edge probabilities but rather with a
probability function depending on the number of vertices. Such a function is called a ``threshold''
for a graph property iff
\begin{itemize}
  \item for asymptotically \emph{larger} probability functions, the probability that a random graph
    is an element of that class tends to \emph{$1$} (``$1$-statement''), and
  \item for asymptotically \emph{smaller} probability functions, the probability that a random graph
    is an element of that class tends to \emph{$0$} (``$0$-statement'').
\end{itemize}\<close>

definition is_threshold :: "ugraph_class \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> bool" where
"is_threshold c t \<equiv> ugraph_property c \<and> (\<forall>p. nonzero_prob_fun p \<longrightarrow>
  (p \<lless> t \<longrightarrow> prob_in_class p c \<longlonglongrightarrow> 0) \<and>
  (t \<lless> p \<longrightarrow> prob_in_class p c \<longlonglongrightarrow> 1))"

lemma is_thresholdI[intro]:
  assumes "ugraph_property c"
  assumes "\<And>p. \<lbrakk> nonzero_prob_fun p; p \<lless> t \<rbrakk> \<Longrightarrow> prob_in_class p c \<longlonglongrightarrow> 0"
  assumes "\<And>p. \<lbrakk> nonzero_prob_fun p; t \<lless> p \<rbrakk> \<Longrightarrow> prob_in_class p c \<longlonglongrightarrow> 1"
  shows "is_threshold c t"
using assms unfolding is_threshold_def by blast

end
