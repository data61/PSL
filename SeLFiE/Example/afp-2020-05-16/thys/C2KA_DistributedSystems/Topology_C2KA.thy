(*  Title:        Notions of Topology for C2KA
    Author:       Maxime Buyse <maxime.buyse at polytechnique.edu>, 2019
    Maintainers:  Maxime Buyse <maxime.buyse at polytechnique.edu> and Jason Jaskolka <jason.jaskolka at carleton.ca>
*)

section \<open>Notions of Topology for \CCKAabbrv \label{sec:topology}\<close>

text \<open>
Orbits, stabilisers, and fixed points are notions that allow us to perceive a kind of topology of a system 
with respect to the stimulus-response relationships among system agents. In this context, the term ``topology'' 
is used to capture the relationships (influence) and connectedness via stimuli of the agents in a distributed 
system. It intends to capture a kind of reachability in terms of the possible behaviours for a given agent.

A \CCKAabbrv consists of two semimodules~$\ActSemimodule$ and~$\OutSemimodule$ for which we have a 
\leftAct{\stim}~$\lSact$ and a \rightAct{\cka}~$\rKact$. Therefore, there are two complementary notions of orbits, 
stabilisers, and fixed points within the context of agent behaviours and stimuli, respectively. In this way, one 
can use these notions to think about distributed systems from two different perspectives, namely the behavioural 
perspective provided by the action of stimuli on agent behaviours described by~$\ActSemimodule$ and the external 
event (stimulus) perspective provided by the action of agent behaviours on stimuli described by~$\OutSemimodule$. 
In this section, only the treatment of these notions with respect to the \leftSemimodule{\stim}~$\ActSemimodule$ 
and agent behaviours is provided. The same notions for the \rightSemimodule{\cka}~$\OutSemimodule$ and stimuli 
can be provided in a very similar way.

When discussing the interplay between \CCKAabbrv and the notions of orbits, stabilisers, and fixed points, the 
partial order of sub-behaviours~$\CKAle$ is extended to sets in order to express sets of agent behaviours 
encompassing one another. For two subsets of agent behaviours~$A,B \STleq \CKAset$, we say that~$A$ 
\emph{is encompassed by}~$B$ (or~$B$ \emph{encompasses}~$A$), written~$\CKAencompass{A}{B}$, if and only 
if~$\biglnotation{\forall}{a}{a \in A}{\lnotation{\exists}{b}{b \in B}{a \CKAle b}}$. In essence,~$A \CKAenc B$ 
indicates that every behaviour contained within the set~$A$ is a sub-behaviour of at least one behaviour in the 
set~$B$. The encompassing relation~$\STIMenc$ for stimuli can be defined similarly. 

Throughout this section, let~$\ActSemimodule$ be the unitary and zero-preserving \leftSemimodule{\stim} of a 
\CCKAabbrv and let~$a \in \CKAset$.
\<close>

theory Topology_C2KA
  imports C2KA
begin

no_notation
comp (infixl "\<circ>" 55)
and rtrancl ("(_\<^sup>*)" [1000] 999)

text \<open>
The locale \emph{topology-c2ka} extends the axiomatisation of \emph{c2ka} to support the notions of topology. 
\<close>

locale topology_c2ka = c2ka +
  fixes orbit :: "'a::cka \<Rightarrow> 'a::cka set" ("Orb")
  and strong_orbit :: "'a::cka \<Rightarrow> 'a::cka set" ("Orb\<^sub>S")
  and stabiliser :: "'a::cka \<Rightarrow> 'b::stimuli set" ("Stab")
  and fixed :: "'a::cka \<Rightarrow> bool"
  and encompassing_relation_behaviours :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool"  (infix "\<lless>\<^sub>\<K>" 50)
  and encompassing_relation_stimuli :: "'b set \<Rightarrow> 'b set \<Rightarrow> bool"  (infix "\<lless>\<^sub>\<S>" 50)
  and induced :: "'a::cka \<Rightarrow> 'a::cka \<Rightarrow> bool" (infix "\<lhd>" 50)
  and orbit_equivalent :: "'a::cka \<Rightarrow> 'a::cka \<Rightarrow> bool" (infix "\<sim>\<^sub>\<K>" 50)
  assumes orb_def: "x \<in> Orb(a) \<longleftrightarrow> (\<exists>s. (s \<circ> a = x))"
  and orbs_def: "b \<in> Orb\<^sub>S(a) \<longleftrightarrow> Orb(b) = Orb(a)"
  and stab_def: "s \<in> Stab(a) \<longleftrightarrow> s \<circ> a = a"
  and fixed_def: "fixed(a) \<longleftrightarrow> (\<forall>s::'b. s\<noteq>\<dd> \<longrightarrow> s \<circ> a = a)"
  and erb_def: "A \<lless>\<^sub>\<K> B \<longleftrightarrow> (\<forall>a::'a. a \<in> A \<longrightarrow> (\<exists>b. b \<in> B \<and> a \<le>\<^sub>\<K> b))"
  and ers_def: "E \<lless>\<^sub>\<S> F \<longleftrightarrow> (\<forall>a::'b. a \<in> E \<longrightarrow> (\<exists>b. b \<in> F \<and> a \<le>\<^sub>\<S> b))"
  and induced_def: "a \<lhd> b \<longleftrightarrow> b \<in> Orb(a)"
  and orbit_equivalent_def: "a \<sim>\<^sub>\<K> b \<longleftrightarrow> Orb(a) = Orb(b)"
begin

subsection \<open>Orbits \label{sub:orbits}\<close>

text \<open>
The \emph{orbit} of~$a$ in~$\stim$ is the set given by~$\orb{a} = \sets{\lAct{a}{s}}{s \in \STIMset}$. The orbit of 
an agent~$a \in \CKAset$ represents the set of all possible behavioural responses from an agent behaving as~$a$ to 
any stimulus from~$\stim$. In this way, the orbit of a given agent can be perceived as the set of all possible 
future behaviours for that agent. 
\<close>


text \<open>
Lemma \emph{inf-K-enc-orb} provides an isotonicity law with respect to the orbits and the encompassing relation for agent behaviours.
\<close>

lemma inf_K_enc_orb: "a \<le>\<^sub>\<K> b \<Longrightarrow> Orb(a) \<lless>\<^sub>\<K> Orb(b)"
  unfolding erb_def orb_def
  using inf_K_next_behaviour by blast
  
text \<open>
The following lemmas provide a selection of properties regarding orbits and the encompassing relation for agent behaviours.
\<close>

lemma enc_orb_add: "Orb(a) \<lless>\<^sub>\<K> Orb(a + b)"
  using  inf_K_enc_orb inf_add_K_right by auto

lemma enc_orb_exchange: "Orb((a*b) ; (c*d)) \<lless>\<^sub>\<K> Orb((a;c) * (b;d))"
  using inf_K_enc_orb exchange_2 by blast

lemma enc_orb_seq_par: "Orb(a;b) \<lless>\<^sub>\<K> Orb(a*b)"
  using inf_K_enc_orb seq_inf_par by auto

lemma enc_orb_add_seq_par: "Orb(a;b + b;a) \<lless>\<^sub>\<K> Orb(a*b)"
  using inf_K_enc_orb add_seq_inf_par by auto

lemma enc_orb_parseq: "Orb((a*b);c) \<lless>\<^sub>\<K> Orb(a*(b;c))"
  using inf_K_enc_orb exchange_3 by blast

lemma enc_orb_seqpar: "Orb(a;(b*c)) \<lless>\<^sub>\<K> Orb((a;b)*c)"
  using inf_K_enc_orb exchange_4 by blast

lemma enc_orb_seqstar_parstar: "Orb(a\<^sup>;) \<lless>\<^sub>\<K> Orb(a\<^sup>*)"
  using inf_K_enc_orb seqstar_inf_parstar by auto

lemma enc_orb_union: "Orb(a) \<lless>\<^sub>\<K> Orb(c) \<and> Orb(b) \<lless>\<^sub>\<K> Orb(c) 
\<longleftrightarrow> Orb(a) \<union> Orb(b) \<lless>\<^sub>\<K>  Orb(c)"
  unfolding erb_def 
  by auto
   
subsection \<open>Stabilisers \label{sub:stabilisers}\<close>

text \<open>
The \emph{stabiliser} of~$a$ in~$\stim$ is the set given by~$\stab{a} = \sets{s \in \STIMset}{\lAct{a}{s} = a}$. 
The stabiliser of an agent~$a \in \CKAset$ represents the set of stimuli which have no observable influence 
(or act as neutral stimuli) on an agent behaving as~$a$.
\<close>  

text \<open>
Lemma \emph{enc-stab-inter-add} provides a property regarding stabilisers and the encompassing relation for stimuli.
\<close>

lemma enc_stab_inter_add: "Stab(a) \<inter> Stab(b) \<lless>\<^sub>\<S> Stab(a + b)"
  unfolding ers_def
  by (auto simp add: stab_def, rename_tac s, rule_tac x="s" in exI, simp)
  
subsection \<open>Fixed Points \label{sub:fixed_points}\<close>

text \<open>
An element~$a \in \CKAset$ is called a \emph{fixed point} if~$\lnotation{\forall}{s}{s \in \STIMset \STdiff \set{\Dstim}}{\lAct{a}{s} = a}$.\linebreak 
When an agent behaviour is a fixed point, it is not influenced by any stimulus other than the deactivation stimulus~$\Dstim$. 
It is important to note that since~$\ActSemimodule$ is zero-preserving, every agent behaviour becomes inactive when subjected to the 
deactivation stimulus~$\Dstim$. Because of this, we exclude this special case when discussing fixed point agent behaviours.
\<close>  

lemma zerofix [simp]: "s \<circ> 0 = 0"
proof -
  have "0 = \<dd> \<circ> a" by simp
  hence "s \<circ> 0 = s \<circ> (\<dd> \<circ> a)" by simp
  hence "s \<circ> 0 = (s \<odot> \<dd>) \<circ> a" by (simp only: lsemimodule3 [symmetric])
  thus "s \<circ> 0 = 0" by simp
qed

text \<open>
The following lemmas provide a selection of properties regarding fixed agent behaviours.
\<close>  

lemma fixed_zero: "fixed(0)"
  unfolding fixed_def
  by simp

lemma fixed_a_b_add: "fixed(a) \<and> fixed(b) \<longrightarrow> fixed(a + b)"
  unfolding fixed_def
  by simp

lemma fix_not_deactivation: "s \<circ> a = a \<and> \<lambda>(s,a) = \<dd> \<Longrightarrow> a = 0"
proof -
  assume E: "s \<circ> a = a \<and> \<lambda>(s,a) = \<dd>"
  hence "s \<circ> (a;1) = a" by simp
  hence "(s\<circ>a) ; (\<lambda>(s,a)\<circ>1) = a" by (simp only: cascadingaxiom)
  hence "0 = a" by (simp add: E)
  thus ?thesis by auto
qed

lemma fixed_a_b_seq: "fixed(a) \<and> fixed(b) \<longrightarrow> fixed(a ; b)"
  unfolding fixed_def
proof (rule impI)
  assume hyp: "(\<forall>s. s \<noteq> \<dd> \<longrightarrow> s \<circ> a = a) \<and> (\<forall>s. s \<noteq> \<dd> \<longrightarrow> s \<circ> b = b)"
  have C1: "(\<forall>s. \<lambda>(s,a) = \<dd> \<longrightarrow> s \<noteq> \<dd> \<longrightarrow> s \<circ> (a ; b) = a ; b)"
  proof -
    have E: "(\<forall>s. s \<noteq> \<dd> \<and> \<lambda>(s,a) = \<dd> \<longrightarrow> s \<circ> (a ; b) = 0)" by simp
    hence "(\<forall>s. s \<noteq> \<dd> \<and> \<lambda>(s,a) = \<dd> \<longrightarrow> s \<circ> a = a \<and> \<lambda>(s,a) = \<dd>)" 
      by (simp add: hyp)
    moreover have "(\<forall>s. s \<circ> a = a \<and> \<lambda>(s,a) = \<dd> \<longrightarrow> a = 0)" 
      by (simp add: fix_not_deactivation)
    ultimately have "(\<forall>s. s \<noteq> \<dd> \<and> \<lambda>(s,a) = \<dd> \<longrightarrow> a = 0)" by auto
    thus ?thesis by (auto simp add: E)
  qed
  moreover have C2: "(\<forall>s. \<lambda>(s,a) \<noteq> \<dd> \<longrightarrow> s \<noteq> \<dd> \<longrightarrow> s \<circ> (a ; b) = a ; b)" 
    by (simp add: hyp)
  ultimately show "(\<forall>s. s \<noteq> \<dd> \<longrightarrow> s \<circ> (a ; b) = a ; b)" by blast
qed

subsection \<open>Strong Orbits and Induced Behaviours \label{sub:strong_orbits_and_induced_behaviours}\<close>

text \<open>
The \emph{strong orbit} of~$a$ in~$\stim$ is the set given by~$\orbS{a} = \sets{b \in \CKAset}{\orb{b} = \orb{a}}$. 
Two agents are in the same strong orbit, denoted~$a \CKAsim b$ for~$a,b \in \CKAset$, if and only if their orbits are 
identical. This is to say when~$a \CKAsim b$, if an agent behaving as~$a$ is influenced by a stimulus to behave as~$b$, 
then there exists a stimulus which influences the agent, now behaving as~$b$, to revert back to its original behaviour~$a$. 

The influence of stimuli on agent behaviours is called the \emph{induced behaviours} via stimuli. Let~$a,b \in \CKAset$ 
be agent behaviours with~$a \neq b$. We say that~$b$ is \emph{induced by~$a$ via stimuli} (denoted by~$\induced{b}{a}$) 
if and only if~$\lnotation{\exists}{s}{s \in \STIMset}{\lAct{a}{s} = b}$. The notion of induced behaviours allows us to make 
some predictions about the evolution of agent behaviours in a given system by providing some insight into how different agents 
can respond to any stimuli.
\<close>  

text \<open>
Lemma \emph{fixed-not-induce} states that if an agent has a fixed point behaviour, then it does not induce any agent behaviours via  stimuli besides the inactive behaviour~$0$.
\<close>  

lemma fixed_not_induce: "fixed(a) \<longrightarrow> (\<forall>b. b \<noteq> 0 \<and> b \<noteq> a \<longrightarrow> \<not>(a \<lhd> b))"
proof -
  have "\<And>s. s = \<dd> \<or> s \<noteq> \<dd> \<Longrightarrow> (\<forall>t. t \<noteq> \<dd> \<longrightarrow> t \<circ> a = a) \<Longrightarrow> s \<circ> a \<noteq> 0 
\<Longrightarrow> s \<circ> a \<noteq> a \<Longrightarrow> False"
    by (erule disjE, simp_all)
  hence "\<And>s. (\<forall>t. t \<noteq> \<dd> \<longrightarrow> t \<circ> a = a) \<Longrightarrow> s \<circ> a \<noteq> 0 \<Longrightarrow> s \<circ> a \<noteq> a \<Longrightarrow> False"
    by simp
  thus ?thesis 
    unfolding fixed_def induced_def orb_def
    by auto
qed

text \<open>
Lemma \emph{strong-orbit-both-induced} states that all agent behaviours which belong to the same strong orbit are mutually induced via some (possibly different) stimuli.
This is to say that if two agent behaviours are in the same strong orbit, then there exists inverse stimuli for each agent behaviour in a 
strong orbit allowing an agent to revert back to its previous behaviour.
\<close>  

lemma in_own_orbit: "a \<in> Orb(a)"
  unfolding orb_def
  by (rule_tac x="\<nn>" in exI, simp)

lemma strong_orbit_both_induced: "a \<sim>\<^sub>\<K> b \<longrightarrow> a \<lhd> b \<and> b \<lhd> a"
  unfolding orbit_equivalent_def induced_def
  by (blast intro: in_own_orbit)

text \<open>
Lemma \emph{strong-orbit-induce-same} states that if two agent behaviours are in the same strong orbit, then a third behaviour can be induced via  stimuli by either of 
the behaviours within the strong orbit. This is to say that each behaviour in a strong orbit can induce the same set of behaviours
(perhaps via different stimuli).
\<close>  

lemma strong_orbit_induce_same: "a \<sim>\<^sub>\<K> b \<longrightarrow> (a \<lhd> c \<longleftrightarrow> b \<lhd> c)"
  unfolding induced_def orbit_equivalent_def
  by simp

end

end
