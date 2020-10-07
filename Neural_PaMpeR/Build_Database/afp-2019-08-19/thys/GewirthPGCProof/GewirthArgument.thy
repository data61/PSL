(*<*)
theory GewirthArgument
  imports ExtendedDDL
begin
nitpick_params[user_axioms=true, show_all, expect=genuine, format = 3] 
(*>*)

text\<open>\noindent{Before starting our formalisation in the next section. We show that the axioms defined so far are consistent.
Rather surprisingly, the \emph{nunchaku} model finder states that no model has been found, while \emph{nitpick}
is indeed able to find one:}\<close>
lemma True nunchaku[satisfy] nitpick[satisfy] oops

section \<open>Gewith's Argument for the Principle of Generic Consistency (PGC)\<close>

text\<open>\noindent{Alan Gewirth's meta-ethical position is known as moral (or ethical) rationalism. According to it, moral principles are knowable \emph{a priori},
by reason alone.
Immanuel Kant is perhaps the most famous figure who has defended such a position. He has argued for the existence of upper moral principles
(e.g. his "categorical imperative")
from which we can reason (in a top-down fashion) in order to deduce and evaluate other more concrete maxims and actions.
In contrast to Kant, Gewirth attempts to derive such upper moral principles by starting from non-moral considerations alone, namely from
an agent's self-reflection.
Gewirth's Principle of Generic Consistency (PGC) asserts that any agent (by virtue of its self-understanding as an agent) is rationally committed
to asserting that (i) it has rights to freedom and well-being, and (ii) that all other agents have those same rights. Gewirth claims that, in his informal proof,
the latter generalisation step (from "I" to all individuals) is done on purely logical grounds and does not presuppose any kind of universal moral principle.
Gewirth's result is thus meant to hold with some kind of apodicticity (i.e.~necessity).
Deryck Beyleveld, author of an authoritative book on Gewirth's argument, puts it this way:
"The argument purports to establish the PGC as a rationally necessary proposition with an apodictic status
\emph{for any PPA} equivalent to that enjoyed by the logical principle of noncontradiction itself." (@{cite "Beyleveld"} p. 1) 
If this is correct, then he succeeded in the task that Kant set himself, i.e.~to found certain basic principles of morality in reason alone.}\<close>
text\<open>\noindent{The argument for the PGC  employs what Gewirth calls "the dialectically necessary method" within the "internal viewpoint" (perspective) of an agent.
Although the drawn inferences are relative to the reasoning agent, Gewirth further argues that
"the dialectically necessary method propounds the contents of this relativity
as necessary ones, since the statements it presents reflect judgements all agents necessarily make on the basis of what is necessarily
involved in their actions ... The statements the method attributes to the agent are set forth as necessary ones in that they reflect what is conceptually
necessary to being an agent who voluntarily or freely acts for purposes he wants to attain." (@{cite "GewirthRM"}).
In other words, the "dialectical necessity" of the assertions and inferences made in the argument comes from the definitional features (conceptual analysis)
of the involved notions of agency, purposeful action, obligation, rights, etc. Hence the alternative notions of logical (i.e.~indexical) validity
and 'a priori necessity', developed in Kaplan's logical framework LD, have been considered by us as appropriate to model this kind of "dialectical necessity".}\<close>

subsection \<open>Conceptual Explications\<close>

type_synonym p = "e\<Rightarrow>m" \<comment> \<open> Type for properties (function from individuals to sentence meanings) \<close>

subsubsection \<open>Agency\<close>

text\<open>\noindent{The type chosen to represent what Gewirth calls "purposes" is not essential for the argument's validity.
We choose to give "purposes" the same type as sentence meanings (type 'm'), so "acting on a purpose" would be
represented in an analogous way to having a certain propositional attitude (e.g. "desiring that some proposition obtains"). }\<close>
consts ActsOnPurpose:: "e\<Rightarrow>m\<Rightarrow>m" \<comment> \<open>  ActsOnPurpose(A,E) gives the meaning of the sentence "A is acting on purpose E" \<close>
consts NeedsForPurpose:: "e\<Rightarrow>p\<Rightarrow>m\<Rightarrow>m" \<comment> \<open>  NeedsForPurpose(A,P,E) gives the meaning of "A needs to have property P in order to reach purpose E" \<close>

text\<open>\noindent{In Gewirth's argument, an individual with agency (i.e.~capable of purposive action) is said to be a PPA (prospective purposive agent).}\<close>
definition PPA:: "p" where "PPA a \<equiv> \<^bold>\<exists>E. ActsOnPurpose a E" \<comment> \<open>  Definition of PPA \<close>

text\<open>\noindent{We have added the following axiom in order to guarantee the argument's logical correctness. It basically says that being
a PPA is identity-constitutive for an individual (i.e.~it's an essential property).}\<close>
axiomatization where essentialPPA: "\<lfloor>\<^bold>\<forall>a. PPA a \<^bold>\<rightarrow> \<^bold>\<box>\<^sup>D(PPA a)\<rfloor>\<^sup>D" \<comment> \<open> being a PPA is an essential property \<close>

text\<open>\noindent{Quite interestingly, the axiom above entails, as a corollary, a kind of ability for a PPA to recognise other PPAs.
For instance, if some individual holds itself as a PPA (i.e.~seen from its own perspective/context 'd') then this individual
(Agent(d)) is considered as a PPA from any other agent's perspective/context 'c'.}\<close>
lemma recognizeOtherPPA: "\<forall>c d. \<lfloor>PPA (Agent d)\<rfloor>\<^sub>d \<longrightarrow> \<lfloor>PPA (Agent d)\<rfloor>\<^sub>c" using essentialPPA by blast


subsubsection \<open>Goodness\<close>

text\<open>\noindent{Gewirth's concept of (subjective) goodness, as employed in his argument, applies to purposes and is relative to some agent.
It is therefore modelled as a binary relation relating an individual (type 'e') with a purpose (type 'm').
Other readings given by Gewirth's for the expression "P is good for A" include among others: "A attaches a positive value to P",
"A values P proactively" and "A is motivated to achieve P".}\<close>
consts Good::"e\<Rightarrow>m\<Rightarrow>m"

text\<open>\noindent{The following axioms interrelate the concept of goodness with the concept of agency, thus providing
the above concepts with some meaning (by framing their inferential roles). Notice that such meaning-constitutive
axioms (which we call "explications") are given as indexically valid (i.e.~a priori) sentences.}\<close>
axiomatization where explicationGoodness1: "\<lfloor>\<^bold>\<forall>a P. ActsOnPurpose a P \<^bold>\<rightarrow> Good a P\<rfloor>\<^sup>D"
axiomatization where explicationGoodness2: "\<lfloor>\<^bold>\<forall>P M a. Good a P \<^bold>\<and> NeedsForPurpose a M P \<^bold>\<rightarrow> Good a (M a)\<rfloor>\<^sup>D"
axiomatization where explicationGoodness3: "\<lfloor>\<^bold>\<forall>\<phi> a. \<^bold>\<diamond>\<^sub>p\<phi> \<^bold>\<rightarrow> \<^bold>O\<langle>\<phi> | \<^bold>\<box>\<^sup>DGood a \<phi>\<rangle>\<rfloor>\<^sup>D"

text\<open>\noindent{Below we show that all axioms defined so far are consistent:}\<close>
lemma True nitpick[satisfy, card c = 1, card e = 1, card w = 1] oops \<comment> \<open> one-world model found (card w=1) \<close>


text\<open>\noindent{The first two assertions above have been explicitly provided by Gewirth as premises of his argument.
The third axiom, however, has been added by us as an implicit premise in order to render Gewirth's proof as correct.
This axiom aims at representing the intuitive notion of "seeking the good". In particular, it asserts
that, from the point of view of an agent, necessarily good purposes are not only action motivating,
but also entail an instrumental obligation to their realisation. The notion of necessity here involved 
is not the usual alethic one (which is represented in DDL with the modal box operators \<open>\<^bold>\<box>\<^sub>a\<close> and \<open>\<^bold>\<box>\<^sub>p\<close>), but the linguistic one
introduced above (\<open>\<^bold>\<box>\<^sup>D\<close>) derived from indexical validity, signaling that an agent holds some
purpose as being true almost 'by definition' (i.e.~a priori).
This sets quite high standards for the kind of purposes an agent would ever take to be (instrumentally) obligatory and is 
indeed the weakest implicit premise we could come up with so far (taking away the \<open>\<^bold>\<box>\<^sup>D\<close> 'a priori necessity' operator
would indeed make this premise much stronger and our proof less credible).}\<close>

subsubsection \<open>Freedom and Well-Being\<close>

text\<open>\noindent{According to Gewirth, enjoying freedom and well-being (which we take together as a predicate: FWB) is the property 
which represents the "necessary conditions" or "generic features" of agency (i.e.~being capable of purposeful action).
Gewirth argues, the property of enjoying freedom and well-being (FWB) is special amongst other action-enabling properties,
in that it is always required in order to act on any purpose (no matter which one).}\<close>

consts FWB::"p" \<comment> \<open> Enjoying freedom and well-being (FWB) is a property (i.e.~has type @{text "e\<Rightarrow>m"}) \<close>

axiomatization where
explicationFWB1: "\<lfloor>\<^bold>\<forall>P a. NeedsForPurpose a FWB P\<rfloor>\<^sup>D"

text\<open>\noindent{We use model finder \emph{nitpick} to verify that all axioms defined so far are consistent.
\emph{Nitpick} can indeed find a 'small' model with cardinality one for the sets of worlds and contexts.}\<close>
lemma True nitpick[satisfy, card c = 1, card e = 1, card w = 1] oops \<comment> \<open> one-world model found  \<close>

text\<open>\noindent{At some point in Gewirth's argument we have to show that there exists an (instrumental) obligation to enjoying freedom and well-being (FWB).
Since, according to the so-called "Kant's law" (which is a corollary of DDL), impossible or necessary things cannot be obligatory,
we can reasonably demand that
FWB be (metaphysically) possible for every agent. As before, we take this demand to be an a priori
characteristic of the concept of FWB and therefore axiomatise it as an indexically valid sentence.}\<close>
axiomatization where explicationFWB2: "\<lfloor>\<^bold>\<forall>a. \<^bold>\<diamond>\<^sub>p FWB a\<rfloor>\<^sup>D"  
axiomatization where explicationFWB3: "\<lfloor>\<^bold>\<forall>a. \<^bold>\<diamond>\<^sub>p \<^bold>\<not>FWB a\<rfloor>\<^sup>D"  

text\<open>\noindent{As a result of enforcing the contingency of FWB, the models found by \emph{nitpick} now have a cardinality
of two for the set of worlds:}\<close>
lemma True nitpick[satisfy, card c = 1, card e = 1, card w = 1, expect=none] oops \<comment> \<open> no model found for one-world models \<close>
lemma True nitpick[satisfy, card c = 1, card e = 1, card w = 2] oops \<comment> \<open> models need now at least two worlds \<close>

subsubsection \<open>Obligation and Interference\<close>

text\<open>\noindent{ Kant's Law ("ought implies can") is derivable directly from DDL: If \<open>\<phi>\<close> oughts to obtain then \<open>\<phi>\<close> is possible.
Note that we will use for the formalisation of Gewirth's argument the DDL ideal obligation operator (\<open>\<^bold>O\<^sub>i\<close>) but
we could have also used (mutatis mutandis) the DDL actual obligation operator (\<open>\<^bold>O\<^sub>a\<close>).}\<close>
lemma "\<lfloor>\<^bold>O\<^sub>i\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<^sub>p\<phi>\<rfloor>" using sem_5ab by simp


text\<open>\noindent{Furthermore, we have seen the need to postulate the following (implicit) premise in order to validate the argument.
This axiom can be seen as a variation of the so-called Kant's law ("ought implies can"), i.e.~an impossible act cannot be obligatory.
In the same vein, our variation can be read as "ought implies ought to can" and is closer to Gewirth's own description:
that having an obligation to do X implies that "I ought (in the same sense and the same criterion) to be free to do X,
that I ought not to be prevented from doing X, that my capacity to do X ought not to be interfered with." (@{cite "GewirthRM"} p. 91-95)}\<close>
axiomatization where OIOAC: "\<lfloor>\<^bold>O\<^sub>i\<phi> \<^bold>\<rightarrow> \<^bold>O\<^sub>i(\<^bold>\<diamond>\<^sub>a\<phi>)\<rfloor>\<^sup>D"

text\<open>\noindent{Concerning the concept of interference, we state that the existence of an individual (successfully) interfering
with some state of affairs S implies that S cannot possibly obtain in any of the actually possible situations (and the other way round).
Note that for this definition we have employed a possibility operator (\<open>\<^bold>\<diamond>\<^sub>a\<close>) which is weaker than metaphysical
possibility (\<open>\<^bold>\<diamond>\<^sub>p\<close>) (see Carmo and Jones DDL framework @{cite "CJDDL"} for details).
Also note that we have also employed the (stronger) classical notion of modal
validity instead of indexical validity. (So far we haven't been able to get theorem provers and model finders to prove/disprove
Gewirth's proof if formalizing this axiom as simply indexically valid.)}\<close>

consts InterferesWith::"e\<Rightarrow>m\<Rightarrow>m" \<comment> \<open> an individual can interfere with some state of affairs (from obtaining) \<close>
axiomatization where explicationInterference: "\<lfloor>(\<^bold>\<exists>b. InterferesWith b \<phi>) \<^bold>\<leftrightarrow> \<^bold>\<not>\<^bold>\<diamond>\<^sub>a\<phi>\<rfloor>"

text\<open>\noindent{From the previous axiom we can prove following corollaries: If someone (successfully) interferes with agent 'a' having FWB,
then 'a' can no longer possibly enjoy its FWB (and the other way round).}\<close>
lemma "\<lfloor>\<^bold>\<forall>a. (\<^bold>\<exists>b. InterferesWith b (FWB a)) \<^bold>\<leftrightarrow> \<^bold>\<not>\<^bold>\<diamond>\<^sub>a(FWB a)\<rfloor>" using explicationInterference by blast
lemma InterferenceWithFWB: "\<lfloor>\<^bold>\<forall>a.  \<^bold>\<diamond>\<^sub>a(FWB a) \<^bold>\<leftrightarrow> (\<^bold>\<forall>b. \<^bold>\<not>InterferesWith b (FWB a))\<rfloor>" using explicationInterference by blast

subsubsection \<open>Rights and Other-Directed Obligations\<close>
 
text\<open>\noindent{Gewirth points out the existence of a correlation between an agent's own claim rights and other-referring obligations (see e.g. @{cite "GewirthRM"}, p. 66).
A claim right is a right which entails duties or obligations on other agents regarding the right-holder
(so-called Hohfeldian claim rights in legal theory).
We model this concept of claim rights in such a way that an individual 'a' has a (claim) right to some property 'P' if and only if
it is obligatory that every
(other) individual 'b' does not interfere with the state of affairs 'P(a)' from obtaining.
Since there is no particular individual to whom this directive is addressed, this obligation has been referred to by Gewirth as being "other-directed"
(aka. "other-referring") in contrast to "other-directing" obligations which entail a moral obligation for some particular subject (@{cite "Beyleveld"} p. 41,51).
This latter distinction is essential to Gewirth's argument.}\<close>
definition RightTo::"e\<Rightarrow>(e\<Rightarrow>m)\<Rightarrow>m" where "RightTo a \<phi> \<equiv> \<^bold>O\<^sub>i(\<^bold>\<forall>b. \<^bold>\<not>InterferesWith b (\<phi> a))"

text\<open>\noindent{Now that all needed axioms and definitions are in place, we use model finder \emph{nitpick} to show that
they are consistent:}\<close>
lemma True nitpick[satisfy, card c = 1, card e = 1, card w = 2] oops \<comment> \<open> models with at least two worlds found \<close>

subsection \<open>Formal Proof of Gewirth's Argument for the PGC\<close>

text\<open>\noindent{Following Beyleveld's summary (@{cite "Beyleveld"}, ch. 2), the main steps of the argument are (with original numbering): }\<close>
text\<open>\noindent{(1) I act voluntarily for some (freely chosen) purpose E (equivalent --by definition-- to: I am a PPA).}\<close>
text\<open>\noindent{(2) E is (subjectively) good (i.e.~I value E proactively).}\<close>
text\<open>\noindent{(3) My freedom and well-being (FWB) are generically necessary conditions of my agency (i.e.~I need them to achieve any purpose whatsoever).}\<close>
text\<open>\noindent{(4) My FWB are necessary goods (at least for me).}\<close>
text\<open>\noindent{(5) I (even if no one else) have a claim right to my FWB.}\<close>
text\<open>\noindent{(13) Every PPA has a claim right to their FWB.}\<close>

subsubsection \<open>Weak Variant\<close>
text\<open>\noindent{In the following we present a formalised proof for a weak variant of the Principle of Generic Consistency (PGC),
which asserts that the following sentence is valid from every PPA's standpoint:
"I (as a PPA) have a claim right to my freedom and well-being".}\<close>
theorem PGC_weak: shows "\<forall>C. \<lfloor>PPA (Agent C) \<^bold>\<rightarrow> (RightTo (Agent C) FWB)\<rfloor>\<^sub>C"
proof - {
  fix C::c \<comment> \<open> 'C' is some arbitrarily chosen context (agent's perspective) \<close>
  let ?I = "(Agent C)" \<comment> \<open> 'I' is/am the agent with perspective 'C' \<close>
  {
    fix E::m \<comment> \<open> 'E' is some arbitrarily chosen purpose \<close>
    {
      assume P1: "\<lfloor>ActsOnPurpose ?I E\<rfloor>\<^sub>C" \<comment> \<open> (1) I act voluntarily on purpose E \<close>
      from P1 have P1a: "\<lfloor>PPA ?I\<rfloor>\<^sub>C" using PPA_def by auto \<comment> \<open> (1a) I am a PPA \<close>
      from P1 have C2: "\<lfloor>Good ?I E\<rfloor>\<^sub>C" using explicationGoodness1 essentialPPA by meson \<comment> \<open> (2) purpose E is good for me \<close>
      from explicationFWB1 have C3: "\<lfloor>\<^bold>\<forall>P. NeedsForPurpose ?I FWB P\<rfloor>\<^sup>D" by simp \<comment> \<open> (3) I need FWB for any purpose whatsoever \<close>
      hence "\<exists>P.\<lfloor>Good ?I P \<^bold>\<and> NeedsForPurpose ?I FWB P\<rfloor>\<^sup>D" using explicationFWB2 explicationGoodness3 sem_5ab by blast
      hence "\<lfloor>Good ?I (FWB ?I)\<rfloor>\<^sup>D" using explicationGoodness2 by blast \<comment> \<open> FWB is (a priori) good for me (in a kind of definitional sense) \<close>
      hence C4: "\<lfloor>\<^bold>\<box>\<^sup>D(Good ?I (FWB ?I))\<rfloor>\<^sub>C" by simp \<comment> \<open> (4) FWB is an (a priori) necessary good for me \<close> 
      have "\<lfloor>\<^bold>O\<langle>FWB ?I | \<^bold>\<box>\<^sup>D(Good ?I) (FWB ?I)\<rangle>\<rfloor>\<^sub>C" using explicationGoodness3 explicationFWB2 by blast \<comment> \<open> I ought to pursue my FWB on the condition that I consider it to be a necessary good \<close>
      hence "\<lfloor>\<^bold>O\<^sub>i(FWB ?I)\<rfloor>\<^sub>C" using explicationFWB2 explicationFWB3 C4 CJ_14p by fastforce \<comment> \<open> There is an (other-directed) obligation to my FWB \<close>
      hence "\<lfloor>\<^bold>O\<^sub>i(\<^bold>\<diamond>\<^sub>a(FWB ?I))\<rfloor>\<^sub>C" using OIOAC by simp \<comment> \<open> It must therefore be the case that my FWB is possible \<close>
      hence "\<lfloor>\<^bold>O\<^sub>i(\<^bold>\<forall>a. \<^bold>\<not>InterferesWith a (FWB ?I))\<rfloor>\<^sub>C" using InterferenceWithFWB by simp \<comment> \<open> There is an obligation for others not to interfere with my FWB  \<close>
      hence C5: "\<lfloor>RightTo ?I FWB\<rfloor>\<^sub>C" using RightTo_def by simp \<comment> \<open> (5) I have a claim right to my freedom and well-being \<close>
    }
    hence "\<lfloor>ActsOnPurpose ?I E \<^bold>\<rightarrow> RightTo ?I FWB\<rfloor>\<^sub>C" by (rule impI) \<comment> \<open> I have a claim right to my freedom and well-being (since I act on some purpose E) \<close>
  }
  hence "\<lfloor>\<^bold>\<forall>P. ActsOnPurpose ?I P \<^bold>\<rightarrow> RightTo ?I FWB\<rfloor>\<^sub>C" by (rule allI) \<comment> \<open>  "allI" is a logical generalisation rule: "all-quantifier introduction" \<close>
  hence "\<lfloor>PPA ?I \<^bold>\<rightarrow> RightTo ?I FWB\<rfloor>\<^sub>C" using PPA_def by simp \<comment> \<open> (seen from my perspective C) I have a claim right to my freedom and well-being since I am a PPA \<close>
  hence "\<lfloor>PPA (Agent C) \<^bold>\<rightarrow> RightTo (Agent C) FWB\<rfloor>\<^sub>C" by simp \<comment> \<open> (seen from the perspective C) C's agent has a claim right to its freedom and well-being since it is a PPA \<close>
}
  thus C13: "\<forall>C. \<lfloor>PPA (Agent C) \<^bold>\<rightarrow> (RightTo (Agent C) FWB)\<rfloor>\<^sub>C" by (rule allI) \<comment> \<open> (13) For every perspective C: C's agent has a claim right to its freedom and well-being \<close>
qed

text\<open>\noindent{Regarding the last inference step, given that the context (agent's perspective) 'C' has been arbitrarily fixed at the beginning, we can use again the "all-quantifier introduction" rule
to generalise the previous assertion to all possible contexts 'C' (and agents 'Agent(C)').
Note that the generalisation from "I" to all individuals has been done on purely logical grounds and does not involve any kind of universal moral principle.
This is a main requirement Gewirth has set for his argument.}\<close>

subsubsection \<open>Strong Variant\<close>
text\<open>\noindent{This is a proof for a stronger variant of the PGC, which asserts that the following
sentence is valid from every PPA's standpoint: "Every PPA has a claim right to its freedom and well-being (FWB)".}\<close>

theorem PGC_strong: shows "\<lfloor>\<^bold>\<forall>x. PPA x \<^bold>\<rightarrow> (RightTo x FWB)\<rfloor>\<^sup>D"
proof - {
fix C::c  \<comment> \<open> 'C' is some arbitrarily chosen context (agent's perspective) \<close>
{
  fix I::"e"  \<comment> \<open> 'I' is some arbitrarily chosen individual (agent's perspective) \<close> 
  {
    fix E::m  \<comment> \<open> 'E' is some arbitrarily chosen purpose \<close>
    {     
     assume P1: "\<lfloor>ActsOnPurpose I E\<rfloor>\<^sub>C" \<comment> \<open> (1) I act voluntarily on purpose E \<close>     
     from P1 have P1a: "\<lfloor>PPA I\<rfloor>\<^sub>C" using PPA_def by auto  \<comment> \<open> (1a) I am a PPA \<close>     
     from P1 have C2: "\<lfloor>Good I E\<rfloor>\<^sub>C" using explicationGoodness1 essentialPPA by meson  \<comment> \<open> (2) purpose E is good for me \<close>
     from explicationFWB1 have C3: "\<lfloor>\<^bold>\<forall>P. NeedsForPurpose I FWB P\<rfloor>\<^sup>D" by simp  \<comment> \<open> (3) I need FWB for any purpose whatsoever \<close>
     hence "\<exists>P.\<lfloor>Good I P \<^bold>\<and> NeedsForPurpose I FWB P\<rfloor>\<^sup>D" using explicationFWB2 explicationGoodness3 sem_5ab by blast     
     hence "\<lfloor>Good I (FWB I)\<rfloor>\<^sup>D" using explicationGoodness2 by blast  \<comment> \<open> FWB is (a priori) good for me (in a kind of definitional sense) \<close>   
     hence C4: "\<lfloor>\<^bold>\<box>\<^sup>D(Good I (FWB I))\<rfloor>\<^sub>C" by simp  \<comment> \<open> (4) FWB is an (a priori) necessary good for me\<close>  
     have "\<lfloor>\<^bold>O\<langle>FWB I | \<^bold>\<box>\<^sup>D(Good I) (FWB I)\<rangle>\<rfloor>\<^sub>C" using explicationGoodness3 explicationFWB2 by blast  \<comment> \<open> I ought to pursue my FWB on the condition that I consider it to be a necessary good\<close>            
     hence "\<lfloor>\<^bold>O\<^sub>i(FWB I)\<rfloor>\<^sub>C" using explicationFWB2 explicationFWB3 C4 CJ_14p by fastforce  \<comment> \<open> There is an (other-directed) obligation to my FWB\<close>  
     hence "\<lfloor>\<^bold>O\<^sub>i(\<^bold>\<diamond>\<^sub>a(FWB I))\<rfloor>\<^sub>C" using OIOAC by simp  \<comment> \<open> It must therefore be the case that my FWB is possible\<close>     
     hence "\<lfloor>\<^bold>O\<^sub>i(\<^bold>\<forall>a. \<^bold>\<not>InterferesWith a (FWB I))\<rfloor>\<^sub>C" using InterferenceWithFWB by simp  \<comment> \<open> There is an obligation for others not to interfere with my FWB\<close>
     hence C5: "\<lfloor>RightTo I FWB\<rfloor>\<^sub>C" using RightTo_def by simp  \<comment> \<open> (5) I have a claim right to my FWB\<close>
   }   
    hence "\<lfloor>ActsOnPurpose I E \<^bold>\<rightarrow> RightTo I FWB\<rfloor>\<^sub>C" by (rule impI)  \<comment> \<open> I have a claim right to my FWB (since I act on some purpose E)\<close>   
  }  
  hence "\<lfloor>\<^bold>\<forall>P. ActsOnPurpose I P \<^bold>\<rightarrow> RightTo I FWB\<rfloor>\<^sub>C" by (rule allI)  
  hence "\<lfloor>PPA I \<^bold>\<rightarrow> RightTo I FWB\<rfloor>\<^sub>C" using PPA_def by simp  \<comment> \<open> I have a claim right to my FWB since I am a PPA \<close>
}  
  hence "\<forall>x. \<lfloor>PPA x \<^bold>\<rightarrow> RightTo x FWB\<rfloor>\<^sub>C" by simp  \<comment> \<open> Every agent has a claim right to its FWB since it is a PPA\<close>  
}
thus C13: "\<forall>C. \<lfloor>\<^bold>\<forall>x. PPA x \<^bold>\<rightarrow> (RightTo x FWB)\<rfloor>\<^sub>C" by (rule allI)  \<comment> \<open> (13) For every perspective C: every agent has a claim right to its FWB\<close>  
qed

text\<open>\noindent{We show that the weaker variant of the PGC presented above can be derived 
from the stronger one.}\<close>
lemma PGC_weak2: "\<forall>C. \<lfloor>PPA (Agent C) \<^bold>\<rightarrow> (RightTo (Agent C) FWB)\<rfloor>\<^sub>C" using PGC_strong by simp

subsubsection \<open>Some Exemplary Inferences\<close>

text\<open>\noindent{In the following, we illustrate how to draw some inferences building upon Gewirth's PGC.}\<close>

consts X::c  \<comment> \<open> Context of use X (to which a certain speaker agent corresponds)\<close>
consts Y::c  \<comment> \<open> Context of use Y (to which another speaker agent corresponds)\<close>

text\<open>\noindent{The agent (of context) X holds itself as a PPA.}\<close>
axiomatization where AgentX_X_PPA: "\<lfloor>PPA (Agent X)\<rfloor>\<^sub>X"

text\<open>\noindent{The agent (of another context) Y holds the agent (of context) X  as a PPA.}\<close>
lemma AgentY_X_PPA: "\<lfloor>PPA (Agent X)\<rfloor>\<^sub>Y" using AgentX_X_PPA recognizeOtherPPA by simp

text\<open>\noindent{Now the agent (of context) Y holds itself as a PPA.}\<close>
axiomatization where AgentY_Y_PPA: "\<lfloor>PPA (Agent Y)\<rfloor>\<^sub>Y"

text\<open>\noindent{The agent Y claims a right to FWB.}\<close>
lemma AgentY_Y_FWB: "\<lfloor>RightTo (Agent Y) FWB\<rfloor>\<^sub>Y" using AgentY_Y_PPA PGC_weak by simp

text\<open>\noindent{The agent Y accepts X claiming a right to FWB.}\<close>
lemma AgentY_X_FWB: "\<lfloor>RightTo (Agent X) FWB\<rfloor>\<^sub>Y" using AgentY_X_PPA PGC_strong by simp

text\<open>\noindent{The agent Y accepts an (other-directed) obligation of non-interference with X's FWB.}\<close>
lemma AgentY_NonInterference_X_FWB: "\<lfloor>\<^bold>O\<^sub>i(\<^bold>\<forall>z. \<^bold>\<not>InterferesWith z (FWB (Agent X)))\<rfloor>\<^sub>Y" using AgentY_X_FWB RightTo_def by simp

text\<open>\noindent{Axiom consistency checked: Nitpick finds a two-world model (card w=2).}\<close>
lemma True nitpick[satisfy, card c = 1, card e = 1, card w = 2] oops

(*<*)
end
(*>*)
