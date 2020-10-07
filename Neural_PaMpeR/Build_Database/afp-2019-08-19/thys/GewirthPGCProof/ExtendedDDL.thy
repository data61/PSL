(*<*)
theory ExtendedDDL
  imports CJDDLplus
begin
nitpick_params[user_axioms=true, show_all, expect=genuine, format = 3]
(*>*)

section \<open>Extending the Carmo and Jones DDL Logical Framework\<close>
text\<open>\noindent{In the last section, we have modelled Kaplanian contexts by introducing a new type of object (type c) and modelled
sentence meanings as so-called "characters", i.e. functions from contexts to sets of worlds (type \<open>c\<Rightarrow>w\<Rightarrow>o\<close>).
We also made the corresponding adjustments to the original semantic embedding of Carmo and Jones' DDL @{cite "C71"} @{cite "BenzmuellerDDL"}.
So far we haven't said much about what these Kaplanian contexts are or which effect they should have on the evaluation
of logical validity. We restricted ourselves to illustrating that their introduction does not have any influence
on the (classical) modal validity of several DDL key theorems.
In this section we introduce an alternative notion of logical validity suited for working with contexts:
indexical validity @{cite "Kaplan1979"} @{cite "Kaplan1989"}.}\<close>

subsection \<open>Context Features\<close>
text\<open>\noindent{Kaplan's theory ("Logic of Demonstratives" @{cite "Kaplan1979"}) aims at modelling the behaviour of
certain context-sensitive linguistic expressions like
the pronouns 'I', 'my', 'you', 'he', 'his', 'she', 'it', the demonstrative pronouns 'that', 'this', the adverbs 'here', 'now',
'tomorrow', 'yesterday', the adjectives 'actual', 'present', and others. Such expressions are known as "indexicals"
and so Kaplan's logical system (among others) is usually referred to as a "logic of indexicals" (although
in his seminal work he referred to it as a "logic of demonstratives" (LD)) @{cite "Kaplan1979"}.
In the following we will refer to Kaplan's logic as the logic "LD".
It is characteristic of an indexical that its content varies with context, i.e. they have a context-sensitive character.
Non-indexicals have a fixed character. The same content is invoked in all contexts.
Kaplan's logical system models context-sensitivity by representing contexts as tuples of features 
(\<open>\<langle>Agent(c), Position(c), World(c), Time(c)\<rangle>\<close>). The agent and the position of context c can be seen as the actual speaker
and place of the utterance respectively, while c's world and time stand for the circumstances of evaluation of the
expression's content and allow for the interaction of indexicals with alethic and tense modalities respectively.}\<close>

text\<open>\noindent{To keep things simple (and relevant for our task) we restrict ourselves to representing a context c as the pair: \<open>\<langle>Agent(c), World(c)\<rangle>\<close>.
For this purpose we represent the functional concepts "Agent" and "World" as logical constants.}\<close>
consts Agent::"c\<Rightarrow>e"  \<comment> \<open> function retrieving the agent corresponding to context c \<close>   
consts World::"c\<Rightarrow>w"  \<comment> \<open> function retrieving the world corresponding to context c \<close>

subsection \<open>Logical Validity\<close>

text\<open>\noindent{Kaplan's notion of (context-dependent) logical truth for a sentence corresponds to its (context-sensitive) formula
(of type \<open>c\<Rightarrow>w\<Rightarrow>bool\<close> i.e. m) being true in the given context and at its corresponding world.}\<close>
abbreviation ldtruectx::"m\<Rightarrow>c\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sub>_") where "\<lfloor>\<phi>\<rfloor>\<^sub>c \<equiv> \<phi> c (World c)" \<comment> \<open>  truth in the given context \<close>

text\<open>\noindent{Kaplan's LD notion of logical validity for a sentence corresponds to its being true in all contexts.
This notion is also known as indexical validity.}\<close>
abbreviation ldvalid::"m\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sup>D") where "\<lfloor>\<phi>\<rfloor>\<^sup>D \<equiv> \<forall>c. \<lfloor>\<phi>\<rfloor>\<^sub>c" \<comment> \<open> LD validity (true in every context) \<close>

text\<open>\noindent{Here we show that indexical validity is indeed weaker than its classical modal counterpart (truth at all worlds for all contexts):}\<close>
lemma "\<lfloor>A\<rfloor> \<Longrightarrow> \<lfloor>A\<rfloor>\<^sup>D" by simp
lemma "\<lfloor>A\<rfloor>\<^sup>D \<Longrightarrow> \<lfloor>A\<rfloor>" nitpick oops \<comment> \<open> countermodel found \<close>

text\<open>\noindent{Here we show that the interplay between indexical validity and the DDL modal and deontic operators does not
result in modal collapse.}\<close>
lemma "\<lfloor>P \<^bold>\<rightarrow> \<^bold>O\<^sub>aP\<rfloor>\<^sup>D" nitpick oops
lemma "\<lfloor>P \<^bold>\<rightarrow> \<^bold>\<box>\<^sub>aP\<rfloor>\<^sup>D" nitpick oops

text\<open>\noindent{Next we show that the necessitation rule does not work for indexical validity (in contrast to classical modal validity as defined for DDL).}\<close>
lemma NecLDa: "\<lfloor>A\<rfloor>\<^sup>D \<Longrightarrow> \<lfloor>\<^bold>\<box>\<^sub>aA\<rfloor>\<^sup>D"  nitpick oops
lemma NecLDp:  "\<lfloor>A\<rfloor>\<^sup>D \<Longrightarrow> \<lfloor>\<^bold>\<box>\<^sub>pA\<rfloor>\<^sup>D" nitpick oops

text\<open>\noindent{The following can be seen as a kind of 'analytic/a priori necessity' operator (to be contrasted to the more
traditional alethic necessity).
In Kaplan's framework, a sentence being logically (i.e. indexically) valid means its being true \emph{a priori}: it is guaranteed to be true
in every possible context in which it is uttered, even though it may express distinct propositions in different contexts. This correlation
between indexical validity and \emph{a prioricity} has also been claimed in other two-dimensional semantic frameworks @{cite "SEP2DSem"}.}\<close>
abbreviation ldvalidbox :: "m\<Rightarrow>m" ("\<^bold>\<box>\<^sup>D_" [52]53) where "\<^bold>\<box>\<^sup>D\<phi> \<equiv> \<lambda>c w. \<lfloor>\<phi>\<rfloor>\<^sup>D" \<comment> \<open> notice the D superscript \<close>
lemma "\<lfloor>\<^bold>\<box>\<^sup>D\<phi>\<rfloor>\<^sub>C \<equiv> \<forall>c.\<lfloor>\<phi>\<rfloor>\<^sub>c" by simp \<comment> \<open>  this operator works analogously to the box operator in modal logic S5 \<close>

text\<open>\noindent{Quite trivially, the necessitation rule works for the combination of indexical validity with the previous operator.}\<close>
lemma NecLD: "\<lfloor>A\<rfloor>\<^sup>D \<Longrightarrow> \<lfloor>\<^bold>\<box>\<^sup>DA\<rfloor>\<^sup>D"  by simp

text\<open>\noindent{The operator above is not part of the original Kaplan's LD (@{cite "Kaplan1979"}) and has been added
by us in order to better highlight some semantic features of our formalisation of Gewirth's argument in the next section and to being able to
use the necessitation rule for some inference steps.}\<close>

subsection \<open>Quantification\<close>
text\<open>\noindent{ We also enrich our logic with (higher-order) quantifiers (using parameterised types).}\<close>
abbreviation mforall::"('t\<Rightarrow>m)\<Rightarrow>m" ("\<^bold>\<forall>") where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>c w.\<forall>x. (\<Phi> x c w)"
abbreviation mexists::"('t\<Rightarrow>m)\<Rightarrow>m" ("\<^bold>\<exists>") where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>c w.\<exists>x. (\<Phi> x c w)"    
abbreviation mforallBinder::"('t\<Rightarrow>m)\<Rightarrow>m" (binder"\<^bold>\<forall>"[8]9) where "\<^bold>\<forall>x. (\<phi> x) \<equiv> \<^bold>\<forall>\<phi>"  
abbreviation mexistsBinder::"('t\<Rightarrow>m)\<Rightarrow>m" (binder"\<^bold>\<exists>"[8]9) where "\<^bold>\<exists>x. (\<phi> x) \<equiv> \<^bold>\<exists>\<phi>"
(*<*)
end
(*>*)
