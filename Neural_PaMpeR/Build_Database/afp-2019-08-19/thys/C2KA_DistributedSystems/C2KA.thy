(*  Title:        C2KA: Communicating Concurrent Kleene Algebra
    Author:       Maxime Buyse <maxime.buyse at polytechnique.edu>, 2019
    Maintainers:  Maxime Buyse <maxime.buyse at polytechnique.edu> and Jason Jaskolka <jason.jaskolka at carleton.ca>
*)

section \<open>Communicating Concurrent Kleene Algebra \label{sec:ccka}\<close>

text \<open>
\CCKAabbrv extends the algebraic foundation of \CKAabbrv with the notions of semimodules and 
stimulus structures to capture the influence of stimuli on the behaviour of system agents.

A \CCKAabbrv is a mathematical system consisting of two semimodules which describe how a stimulus 
structure~$\stim$ and a \CKAabbrv~$\cka$ mutually act upon one another to characterize the response 
invoked by a stimulus on an agent behaviour as a next behaviour and a next stimulus. The 
\leftSemimodule{\stim}~$\ActSemimodule$ describes how the stimulus structure~$\stim$ acts upon the 
\CKAabbrv~$\cka$ via the mapping~$\actOp$. The mapping~$\actOp$ is called the \emph{next behaviour mapping} 
and it describes how a stimulus invokes a behavioural response from a given agent. From~$\ActSemimodule$, 
the next behaviour mapping~$\actOp$ distributes over~$+$ and~$\STIMplus$. Additionally, since~$\ActSemimodule$ 
is unitary, it is the case that the neutral stimulus has no influence on the behaviour of all agents and 
since~$\ActSemimodule$ is zero-preserving, the deactivation stimulus influences all agents to become inactive. 
The \rightSemimodule{\cka}~$\OutSemimodule$ describes how the \CKAabbrv~$\cka$ acts upon the stimulus 
structure~$\stim$ via the mapping~$\outOp$. The mapping~$\outOp$ is called the \emph{next stimulus mapping} 
and it describes how a new stimulus is generated as a result of the response invoked by a given stimulus on 
an agent behaviour. From~$\OutSemimodule$, the next stimulus mapping~$\outOp$ distributes over~$\STIMplus$ 
and~$+$. Also, since~$\OutSemimodule$ is unitary, it is the case that the idle agent forwards any stimulus that 
acts on it and since~$\OutSemimodule$ is zero-preserving, the inactive agent always generates the deactivation 
stimulus. A full account of \CCKAabbrv can be found in~\cite{Jaskolka2015ab,Jaskolka2013aa,Jaskolka2014aa}. 
\<close>

theory C2KA
  imports CKA Stimuli
begin

no_notation
comp (infixl "\<circ>" 55)
and rtrancl ("(_\<^sup>*)" [1000] 999)

text \<open>
The locale \emph{c2ka} contains an axiomatisation of \CCKAabbrv  and some basic theorems relying on the 
axiomatisations of stimulus structures and \CKAabbrv provided in Sections~\ref{sec:stimulus_structure} 
and~\ref{sec:behaviour_structure}, respectively. We use a locale instead of a class in order to allow 
stimuli and behaviours to have two different types.
\<close>

locale c2ka =
  fixes next_behaviour :: "'b::stimuli \<Rightarrow> 'a::cka \<Rightarrow> 'a" (infixr "\<circ>" 75)
  and next_stimulus :: "('b::stimuli \<times> 'a::cka) \<Rightarrow> 'b" ("\<lambda>")
  assumes lsemimodule1 [simp]: "s \<circ> (a + b) = (s \<circ> a) + (s \<circ> b)"
  and lsemimodule2 [simp]: "(s \<oplus> t) \<circ> a = (s \<circ> a) + (t \<circ> a)"
  and lsemimodule3 [simp]: "(s \<odot> t) \<circ> a = s \<circ> (t \<circ> a)"
  and lsemimodule4 [simp]: "\<nn> \<circ> a = a"
  and lsemimodule5 [simp]: "\<dd> \<circ> a = 0"
  and rsemimodule1 [simp]: "\<lambda>(s \<oplus> t, a) = \<lambda>(s, a) \<oplus> \<lambda>(t, a)"
  and rsemimodule2 [simp]: "\<lambda>(s, a + b) = \<lambda>(s, a) \<oplus> \<lambda>(s, b)"
  and rsemimodule3 [simp]: "\<lambda>(s, a ; b) = \<lambda>(\<lambda>(s, a), b)"
  and rsemimodule4 [simp]: "\<lambda>(s, 1) = s"
  and rsemimodule5 [simp]: "\<lambda>(s, 0) = \<dd>"
  and cascadingaxiom [simp]: "s \<circ> (a ; b) = (s \<circ> a);(\<lambda>(s, a) \<circ> b)"
  and cascadingoutputlaw: "a \<le>\<^sub>\<K> c \<or> b = 1 \<or> (s \<circ> a);(\<lambda>(s,c) \<circ> b) = 0"
  and sequentialoutputlaw [simp]: "\<lambda>(s \<odot> t, a) = \<lambda>(s, t\<circ>a) \<odot> \<lambda>(t, a)"
  and onefix: "s = \<dd> \<or> s \<circ> 1 = 1"
  and neutralunmodified: "a = 0 \<or> \<lambda>(\<nn>, a) = \<nn>"
begin

text \<open>
Lemmas \emph{inf-K-S-next-behaviour} and \emph{inf-K-S-next-stimulus} show basic results from the axiomatisation of \CCKAabbrv.
\<close>

lemma inf_K_S_next_behaviour: "(a \<le>\<^sub>\<K> b \<and> s \<le>\<^sub>\<S> t) \<Longrightarrow> (s \<circ> a \<le>\<^sub>\<K> t \<circ> b)"
  unfolding Stimuli.leq_def CKA.leq_def
proof -
  assume hyp: "a + b = b \<and> s \<oplus> t = t"
  hence "s \<circ> a + t \<circ> b = s \<circ> a + (s \<oplus> t) \<circ> b" by simp
  hence "s \<circ> a + t \<circ> b = s \<circ> a + s \<circ> b + t \<circ> b" by (simp add: algebra_simps)
  moreover have "s \<circ> (a + b) = s \<circ> a + s \<circ> b" by simp
  ultimately have "s \<circ> a + t \<circ> b = s \<circ> (a + b) + t \<circ> b" by simp
  hence "s \<circ> a + t \<circ> b = s \<circ> b + t \<circ> b" by (simp add: hyp)
  hence "s \<circ> a + t \<circ> b = (s \<oplus> t) \<circ> b" by simp
  thus "s \<circ> a + t \<circ> b = t \<circ> b" by (simp add: hyp)
qed

lemma inf_K_S_next_stimulus: "a \<le>\<^sub>\<K> b \<and> s \<le>\<^sub>\<S> t \<Longrightarrow> \<lambda>(s,a) \<le>\<^sub>\<S> \<lambda>(t,b)"
  unfolding Stimuli.leq_def CKA.leq_def
proof -
  assume hyp: "a + b = b \<and> s \<oplus> t = t"
  hence "\<lambda>(s,a) \<oplus> \<lambda>(t,b) = \<lambda>(s,a) \<oplus> \<lambda>(s\<oplus>t,b)" by simp
  hence "\<lambda>(s,a) \<oplus> \<lambda>(t,b) = \<lambda>(s,a) \<oplus> \<lambda>(s,b) \<oplus> \<lambda>(t,b)" by (simp add: add_assoc)
  moreover have "\<lambda>(s,a+b) = \<lambda>(s,a) \<oplus> \<lambda>(s,b)" by simp
  ultimately have "\<lambda>(s,a) \<oplus> \<lambda>(t,b) = \<lambda>(s,a+b) \<oplus> \<lambda>(t,b)" by simp
  hence "\<lambda>(s,a) \<oplus> \<lambda>(t,b) = \<lambda>(s,b) \<oplus> \<lambda>(t,b)" by (simp add: hyp)
  hence "\<lambda>(s,a) \<oplus> \<lambda>(t,b) = \<lambda>(s\<oplus>t,b)" by simp
  thus "\<lambda>(s,a) \<oplus> \<lambda>(t,b) = \<lambda>(t,b)" by (simp add: hyp)
qed

text \<open>
The following lemmas show additional results from the axiomatisation of \CCKAabbrv which follow from lemmas \emph{inf-K-S-next-behaviour} and \emph{inf-K-S-next-stimulus}.
\<close>

lemma inf_K_next_behaviour: "a \<le>\<^sub>\<K> b \<Longrightarrow> s \<circ> a \<le>\<^sub>\<K> s \<circ> b"
  by (simp add: inf_K_S_next_behaviour)

lemma inf_S_next_behaviour: "s \<le>\<^sub>\<S> t \<Longrightarrow> s \<circ> a \<le>\<^sub>\<K> t \<circ> a"
  by (simp add: inf_K_S_next_behaviour)

lemma inf_add_seq_par_next_behaviour: "s \<circ> (a;b + b;a) \<le>\<^sub>\<K> s \<circ> (a*b)"
  using inf_K_next_behaviour add_seq_inf_par by blast

lemma inf_seqstar_parstar_next_behaviour: "s \<circ> a\<^sup>; \<le>\<^sub>\<K> s \<circ> a\<^sup>*"
  by (simp add: seqstar_inf_parstar inf_K_next_behaviour)

lemma inf_S_next_stimulus: "s \<le>\<^sub>\<S> t \<Longrightarrow> \<lambda>(s,a) \<le>\<^sub>\<S> \<lambda>(t,a)"
  by (simp add: inf_K_S_next_stimulus)

lemma inf_K_next_stimulus: "a \<le>\<^sub>\<K> b \<Longrightarrow> \<lambda>(s,a) \<le>\<^sub>\<S> \<lambda>(s,b)"
  by (simp add: inf_K_S_next_stimulus)

lemma inf_add_seq_par_next_stimulus: "\<lambda>(s, a;b + b;a) \<le>\<^sub>\<S> \<lambda>(s, a*b)"
proof -
  have "a;b \<le>\<^sub>\<K> a*b" by (rule seq_inf_par)
  moreover have "b;a \<le>\<^sub>\<K> b*a" by (rule seq_inf_par)
  ultimately have "a;b + b;a \<le>\<^sub>\<K> a*b + b*a" by (simp add: add_mono)
  hence "a;b + b;a \<le>\<^sub>\<K> a*b" by (simp add: par_comm)
  thus "\<lambda>(s, a;b + b;a) \<le>\<^sub>\<S> \<lambda>(s, a*b)" by (rule inf_K_next_stimulus)
qed

lemma inf_seqstar_parstar_next_stimulus: "\<lambda>(s, a\<^sup>;) \<le>\<^sub>\<S> \<lambda>(s, a\<^sup>*)"
  by (simp add: seqstar_inf_parstar inf_K_next_stimulus)

end

end
