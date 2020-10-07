(*  Title:        C2KA Stimulus Structure
    Author:       Maxime Buyse <maxime.buyse at polytechnique.edu>, 2019
    Maintainers:  Maxime Buyse <maxime.buyse at polytechnique.edu> and Jason Jaskolka <jason.jaskolka at carleton.ca>
*)

section \<open>Stimulus Structure \label{sec:stimulus_structure}\<close>

text \<open>
A stimulus constitutes the basis for behaviour. Because of this, each discrete, observable event 
introduced to a system, such as that which occurs through the communication among agents or from the 
system environment, is considered to be a stimulus which invokes a response from each system agent.

A \emph{stimulus structure} is an idempotent semiring~$\STIMstructure$ with a multiplicatively 
absorbing~$\Dstim$ and identity~$\Nstim$. Within the context of stimuli,~$\STIMset$ is a set of 
stimuli which may be introduced to a system. The operator~$\STIMplus$ is interpreted as a choice 
between two stimuli and the operator~$\STIMdot$ is interpreted as a sequential composition of two 
stimuli. The element~$\Dstim$ represents the \emph{deactivation stimulus} which influences all agents 
to become inactive and the element~$\Nstim$ represents the \emph{neutral stimulus} which has no influence 
on the behaviour of all agents. The natural ordering relation~$\STIMle$ on a stimulus structure~$\stim$ 
is called the sub-stimulus relation. For stimuli~$s,t \in \STIMset$, we write~$s \STIMle t$ and say 
that~$s$ is a sub-stimulus of~$t$ if and only if~$s \STIMplus t = t$. 
\<close>

theory Stimuli
  imports Main
begin

text \<open>
The class \emph{stimuli} describes the stimulus structure for \CCKAabbrv. We do not use 
Isabelle's built-in theories for groups and orderings to allow a different notation for the operations 
on stimuli to be consistent with~\cite{Jaskolka2015ab}.
\<close>

class plus_ord =
  fixes leq::"'a \<Rightarrow> 'a \<Rightarrow> bool" ("(_/ \<le>\<^sub>\<S> _)"  [51, 51] 50)
  fixes add::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<oplus>" 65)
  assumes leq_def: "x \<le>\<^sub>\<S> y \<longleftrightarrow> x \<oplus> y = y"
  and add_assoc: "(x \<oplus> y) \<oplus> z = x \<oplus> (y \<oplus> z)"
  and add_comm: "x \<oplus> y = y \<oplus> x"
begin

notation
  leq  ("'(\<le>')") and
  leq ("(_/ \<le>\<^sub>\<S> _)"  [51, 51] 50)

end

class stimuli = plus_ord +
  fixes seq_comp::"'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<odot>" 70)
  fixes neutral :: 'a ("\<nn>")
  and deactivation :: 'a ("\<dd>")
  and basic :: "'a set" ("\<S>\<^sub>a")
  assumes stim_idem [simp]: "x \<oplus> x = x"
  and seq_nl [simp]: "\<nn> \<odot> x = x"
  and seq_nr [simp]: "x \<odot> \<nn> = x"
  and add_zero [simp]: "\<dd> \<oplus> x = x"
  and absorbingl [simp]: "\<dd> \<odot> x = \<dd>"
  and absorbingr [simp]: "x \<odot> \<dd> = \<dd>"
  and zero_not_basic: "\<dd> \<notin> \<S>\<^sub>a"
begin 

lemma inf_add_S_right: "x \<le>\<^sub>\<S> y \<Longrightarrow> x \<le>\<^sub>\<S> y \<oplus> z"
  unfolding leq_def
  by (simp add: add_assoc [symmetric])

lemma inf_add_S_left: "x \<le>\<^sub>\<S> y \<Longrightarrow> x \<le>\<^sub>\<S> z \<oplus> y"
  by (simp add: add_comm inf_add_S_right)

lemma leq_refl [simp]: "x \<le>\<^sub>\<S> x"
  unfolding leq_def
  by simp

end

end
