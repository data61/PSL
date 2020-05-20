(*<*)
theory Thesis
imports TAO_9_PLM TAO_98_ArtificialTheorems TAO_99_SanityTests TAO_99_Paradox TAO_10_PossibleWorlds
    "HOL-Library.LaTeXsugar"
    "HOL-Library.OptionalSugar"
begin
(*>*)

(*<*)
(* Pretty printing settings for antiquotations. *)
notation (latex output)
  validity_in ("[\<^latex>\<open>\\embeddedstyle{\<close>_\<^latex>\<open>}\<close> in _]")
notation (latex output)
  actual_validity ("[\<^latex>\<open>\\embeddedstyle{\<close>_\<^latex>\<open>}\<close>]")
notation (latex output)
  Axioms.axiom ("[[ \<^latex>\<open>\\embeddedstyle{\<close>_\<^latex>\<open>}\<close> ]]")
definition embedded_style where "embedded_style \<equiv> id"
lemma embedded_meta_def: "(A \<equiv> B) \<Longrightarrow> (embedded_style A) = B" unfolding embedded_style_def by auto
lemma embedded_meta_eq: "(A = B) \<Longrightarrow> (embedded_style A) = B" unfolding embedded_style_def by auto
lemma embedded_def: "(A \<equiv> B) \<Longrightarrow> (embedded_style A) = (embedded_style B)"
    unfolding embedded_style_def by auto
lemma embedded_eq: "(A = B) \<Longrightarrow> (embedded_style A) = (embedded_style B)"
    unfolding embedded_style_def by auto
notation (latex output)
  embedded_style ("\<^latex>\<open>\\embeddedstyle{\<close>_\<^latex>\<open>}\<close>")
translations
  "x" <= "CONST make\<kappa> x"
translations
  "p" <= "CONST make\<o> p"
translations
  "p" <= "CONST make\<Pi>\<^sub>1 p"
translations
  "p" <= "CONST make\<Pi>\<^sub>2 p"
translations
  "p" <= "CONST make\<Pi>\<^sub>3 p"
translations
  "x" <= "CONST eval\<kappa> x"
translations
  "p" <= "CONST eval\<o> p"
translations
  "p" <= "CONST eval\<Pi>\<^sub>1 p"
translations
  "p" <= "CONST eval\<Pi>\<^sub>2 p"
translations
  "p" <= "CONST eval\<Pi>\<^sub>3 p"
notation (latex output)
  that ("\<^bold>\<iota>x . _ x")
notation (latex output)
  forall\<^sub>\<nu> ("\<^bold>\<forall>\<^sub>\<nu> x . _ x")
notation (latex output)
  forall\<^sub>0 ("\<^bold>\<forall>\<^sub>0 p . _ p")
notation (latex output)
  forall\<^sub>1 ("\<^bold>\<forall>\<^sub>1 F . _ F")
notation (latex output)
  forall\<^sub>2 ("\<^bold>\<forall>\<^sub>2 F . _ F")
notation (latex output)
  forall\<^sub>3 ("\<^bold>\<forall>\<^sub>3 F . _ F")
notation (latex output)
  forall ("\<^bold>\<forall> \<alpha> . _ \<alpha>")
notation (latex output)
  exists ("\<^bold>\<exists> \<alpha> . _ \<alpha>")
notation (latex output)
  exists_unique ("\<^bold>\<exists>! \<alpha> . _ \<alpha>")
notation (latex output)
  lambdabinder1 ("\<^bold>\<lambda>x. _ x")
translations
  (type) "\<alpha>" <= (type) "\<Pi>\<^sub>1 set"
(* auxiliary lemmata and attributes to aid in pretty printing *)
lemma expand_def1: "p \<equiv> q \<Longrightarrow> (\<And>x . p x = q x)" by simp
lemma expand_def2: "p \<equiv> q \<Longrightarrow> (\<And>x y . p x y = q x y)" by simp
lemma expand_def3: "p \<equiv> q \<Longrightarrow> (\<And>x y z . p x y z = q x y z)" by simp
attribute_setup expand1 = \<open>
  Scan.succeed (Thm.rule_attribute [] 
    (fn _ => fn thm => thm RS @{thm expand_def1}))
\<close>
attribute_setup expand2 = \<open>
  Scan.succeed (Thm.rule_attribute [] 
    (fn _ => fn thm => thm RS @{thm expand_def2}))
\<close>
attribute_setup expand3 = \<open>
  Scan.succeed (Thm.rule_attribute [] 
    (fn _ => fn thm => thm RS @{thm expand_def3}))
\<close>
no_syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]") 
no_syntax "__listcompr" :: "args \<Rightarrow> 'a list" ("[(_)]")
(*>*)
  
(* abstract in thesis/root.tex *)

chapter\<open>Introduction\<close>

text\<open>
\epigraph{Calculemus!}{\textit{Leibniz}}
\<close>
  
section\<open>Universal Logical Reasoning\footnote{This introductory section is based on the description of the topic in @{cite UniversalReasoning}.}\<close>

text\<open>

The concept of understanding rational argumentation and reasoning using formal logical systems
has a long tradition and can already be found in the study of syllogistic arguments by
Aristotle. Since then a large variety of formal systems has evolved, each using different syntactical
and semantical structures to capture specific aspects of logical reasoning (e.g. propositional logic,
first-order/higher-order logic, modal logic, free logic, etc.). This diversity of formal systems
gives rise to the question, whether a \emph{universal} logic can be devised, that would be capable
of expressing statements of all existing specialized logical systems and provide a basis for
meta-logical considerations like the equivalence of or relations between those systems.

The idea of a universal logical framework is very prominent in the works of Gottfried Wilhelm Leibniz
(1646-1716) with his concept of a \emph{characteristica universalis}, i.e. a universal formal language
able to express metaphysical, scientific and mathematical concepts. Based thereupon he envisioned 
the \emph{calculus ratiocinator}, a universal logical calculus with which the truth of statements
formulated in the characteristica universalis could be decided purely by formal calculation and thereby
in an automated fashion, an idea that became famous under the slogan: \emph{Calculemus!}

Nowadays with the rise of powerful computer systems such a universal logical framework could have
repercussions throughout the sciences and may be a vital part of human-machine interaction in the
future. Leibniz' ideas have inspired recent efforts to use functional higher-order logic (HOL) as
such a universal logical language and to represent various logical systems by the use of
\emph{shallow semantical embeddings}@{cite UniversalReasoning}.

Notably this approach received attention due to the formalization, validation and analysis
of G\"odel's ontological proof of the existence of God by Christoph Benzm\"uller@{cite GoedelGod},
for which higher-order modal logic was embedded in the computerized logic framework Isabelle/HOL.
\<close>

section\<open>Shallow Semantical Embeddings in HOL\<close>

text\<open>
A semantic embedding of a target logical system defines the syntactic elements of the target language
in a background logic (e.g. in a framework like Isabelle/HOL) based on their semantics.
This way the background logic can be used as meta-logic to argue about the semantic truth of syntactic statements
in the embedded logic.

A \emph{deep} embedding represents the complete syntactic structure of the target language
separately from the background logic, i.e. every term, variable symbol, connective, etc. of the
target language is represented as a syntactic object and then the background logic is used to
evaluate a syntactic expression by quantifying over all models that can be associated with the
syntax. Variable symbols of the target logic for instance would be represented as constants in
the background logic and a proposition would be considered semantically valid if it holds for
all possible denotations an interpretation function can assign to them.

While this approach will work for most target logics, it has several drawbacks. It is likely that there are
principles that are shared between the target logic and the background logic, such as \<open>\<alpha>\<close>-conversion
for \<open>\<lambda>\<close>-expressions or the equivalence of terms with renamed variables in general. In a deep
embedding these principles usually have to be explicitly shown to hold for the syntactic representation
of the target logic, which is usually connected with significant complexity. Furthermore if the
framework used for the background logic allows automated reasoning, the degree of automation that
can be achieved in the embedded logic is limited, as any reasoning in the target logic will have
to consider the meta-logical evaluation process in the background logic which will usually be complex.

A \emph{shallow} embedding uses a different approach based on the idea that most contemporary
logical systems are semantically characterized by the means of set theory. A shallow embedding
defines primitive syntactic objects of the target language such as variables or propositions
using a set theoretic representation. For example propositions in a modal logic can be represented
as functions from possible worlds to truth values in a non-modal logic.

The shallow embedding aims to equationally define only the syntactic elements of the target logic
that are not already present in the background logic or whose semantics behaves differently than in
the background logic, while preserving as much of the logical structure of the background logic
as possible. The modal box operator for example can be represented as a quantification over all
possible worlds, satisfying an accessibility relation, while negation and quantification can be
directly represented using the negation and quantification of the background logic (preserving
the dependency on possible worlds).

This way basic principles of the background logic (such as alpha conversion) can often be directly
applied to the embedded logic and the equational, definitional nature of the representation preserves
a larger degree of automation. Furthermore, axioms in the embedded logic can often be equivalently
stated in the background logic, which makes the construction of models for the system easier and again increases
the degree of automation that can be retained.

The shallow semantical embedding of modal logic was the basis for the analysis of
G\"odel's ontological argument@{cite GoedelGod} and the general concept has shown great potential as a universal
tool for logical embeddings while retaining the existing infrastructure for automation as for
example present in a framework like Isabelle/HOL\footnote{See @{cite UniversalReasoning} for an
overview and an description of the ambitions of the approach.}.

\<close>

(* TODO: no new section? *)
section\<open>Relational Type Theory vs. Functional Type Theory\<close>

text\<open>
The universality of this approach has since been challenged by Paul Oppenheimer and Edward Zalta
who argue in the paper \emph{Relations Versus Functions at the Foundations of Logic: Type-Theoretic
Considerations}@{cite rtt} that relational type theory is more general than functional type theory.
In particular they argue that the Theory of Abstract Objects, which is founded in relational type
theory, cannot be properly characterized in functional type theory.

This has led to the question whether a shallow semantical embedding of the Theory of Abstract Objects
in a functional logic framework like Isabelle/HOL is at all possible, which is the core question
the work presented here attempts to examine and partially answer.

One of their main arguments is that unrestricted \<open>\<lambda>\<close>-expressions as present in functional type
theory lead to an inconsistency when combined with one of the axioms of the theory and indeed it
has been shown for early attempts on embedding the theory that despite significant efforts
to avoid the aforementioned inconsistency by excluding problematic \<open>\<lambda>\<close>-expressions in the embedded
logic, it could still be reproduced using an appropriate construction in the background logic\footnote{
Early attempts of an embedding by Christoph Benzm\"uller (see \url{https://github.com/cbenzmueller/PrincipiaMetaphysica})
were discussed in his university lecture \emph{Computational Metaphysics} (FU Berlin, SS2016) and the proof of
their inconsistency in the author's final project for the course inspired the continued research
in this master's thesis.}.

The solution presented here circumvents this problem by identifying \<open>\<lambda>\<close>-expressions as one element of the
target language that behaves differently than their counterparts in the background logic and
consequently by representing \<open>\<lambda>\<close>-expressions of the target logic using a new \emph{defined}
kind of \<open>\<lambda>\<close>-expressions. This forces \<open>\<lambda>\<close>-expressions in the embedded logic to have a particular
semantics that is inspired by the \emph{Aczel-model} of the target theory (see \ref{aczel-model})
and avoids prior inconsistencies. The mentioned issue and the employed solution is discussed in
more detail in sections~\ref{russell-paradox} and~\ref{lambda-expressions}.

\pagebreak
\<close>

section\<open>Overview of the following Chapters\<close>

text\<open>
  The following chapters are structured as follows:
  \begin{itemize}
    \item The second chapter gives an overview of the motivation and structure of
          the target theory of the embedding, the Theory of Abstract Objects. It also
          introduces the \emph{Aczel-model} of the theory, that was adapted as the basis
          for the embedding.
  
    \item The third chapter is a detailed documentation of the concepts and
          technical structure of the embedding. This chapter references the
          Isabelle theory that can be found in the appendix.
  
    \item The fourth chapter consists of a technical discussion about some of the issues encountered
          during the construction of the embedding due to limitations of the logic framework
          Isabelle/HOL and the solutions that were employed.
  
    \item The last chapter discusses the relation between the embedding and the target theory
          of PLM and describes some of the results achieved using the embedding. Furthermore it
          states some open questions for future research.
  \end{itemize}

  This entire document is generated from an Isabelle theory file and thereby in particular
  all formal statements in the third chapter are well-formed terms, resp. verified valid theorems
  in the constructed embedding unless the contrary is stated explicitly.
\<close>

chapter\<open>The Theory of Abstract Objects\<close>

text\<open>
  \epigraph{
It is widely supposed that every entity falls into one of two categories:
Some are concrete; the rest abstract. The distinction is supposed to be
of fundamental significance for metaphysics and epistemology.
}{\textit{Stanford Encyclopedia of Philosophy\cite{sep-abstract-objects}}}
\<close>

section\<open>Motivation\<close>

text\<open>

As the name suggests the Theory of Abstract Objects revolves around \emph{abstract objects} and
is thereby a metaphysical theory.
As Zalta puts it: \textquote{Whereas physics attempts a systematic description of fundamental
and complex concrete objects, metaphysics attempts a systematic description of fundamental
and complex abstract objects. \textelp{} The theory of abstract objects attempts to organize
these objects within a systematic and axiomatic framework. \textelp{We can} think of abstract
objects as possible and actual property-patterns. \textelp{} Our theory of abstract
objects will \emph{objectify} or \emph{reify} the group of properties satisfying \textins{such a}
pattern.}\cite{MallyTheory}\footnote{The introduction to the theory
in this and the next section is based on the documentation of the theory in @{cite MallyTheory} and @{cite MallyDistinction}, which
is paraphrased and summarized throughout the sections. Further references about the topic include @{cite PM},
@{cite zalta1988intensional}, @{cite zalta1983abstract}.}

So what is the fundamental distinction between abstract and concrete objects? The analysis
in the Theory of Abstract Objects is based on a distinction between two fundamental modes of
predication that is based on the ideas of Ernst Mally.
Whereas objects that are concrete (the Theory of Abstract Objects calls them \emph{ordinary objects})
are characterized by the classical mode of predication, i.e. \emph{exemplification},
a second mode of predication is introduced that is reserved for abstract objects. This new mode of
predication is called \emph{encoding} and formally written as \<open>xF\<close> (\<open>x\<close>
\emph{encodes} \<open>F\<close>) in contrast to \<open>Fx\<close> (\<open>x\<close> \emph{exemplifies} \<open>F\<close>).

Mally informally introduces this second mode of predication in order to represent sentences about
fictional objects. In his thinking, concrete objects, that for example have a fixed spatiotemporal
location, a body and shape, etc., only \emph{exemplify} their properties and are characterized
by the properties they exemplify. Sentences about fictional objects such as \textquote{Sherlock Holmes
is a detective} have a different meaning. Stating that \textquote{Sherlock Holmes is a detective} 
does not imply that there is some concrete object that is Sherlock Holmes and this object exemplifies
the property of being a detective - it rather states that the concept we have of the fictional
character Sherlock Holmes includes the property of being a detective. Sherlock Holmes is not concrete,
but an abstract object that is \emph{determined} by the properties Sherlock Holmes is given by the
fictional works involving him as character. This is expressed using the second mode of predication
\emph{Sherlock Holmes encodes the property of being a detective}.

To clarify the difference between the two concepts note that any object either exemplifies a property
or its negation. The same is not true for encoding. For example it is not determinate whether 
Sherlock Holmes has a mole on his left foot. Therefore the abstract object Sherlock Holmes neither
encodes the property of having a mole on his left foot, nor the property of not having a mole on
his left foot\footnote{see @{cite MallyDistinction}}.

The theory even allows for an abstract object to encode properties that no object
could possibly exemplify and reason about them, for example the quadratic circle. In classical logic
meaningful reasoning about a quadratic circle is impossible - as soon as I suppose that an object
\emph{exemplifies} the properties of being a circle and of being quadratic, this will lead to a
contradiction and every statement becomes derivable.

In the Theory of Abstract Objects on the other hand
there is an abstract object that encodes exactly these two properties and it is possible to reason
about it. For example we can state that this object \emph{exemplifies} the property of \emph{being
thought about by the reader of this paragraph}. This shows that the Theory of Abstract Objects provides
the means to reason about processes of human thought in a much broader sense than classical logic
would allow.

It turns out that by the means of abstract objects and encoding  the Theory of Abstract Objects
  can be used to represent and reason about a large variety of concepts that
regularly occur in philosophy, mathematics or linguistics.

In \cite{MallyTheory} the principal objectives of the theory are summarized as follows:
\begin{itemize}
  \item To describe the logic underlying (scientific) thought and reasoning by extending
        classical propositional, predicate, and modal logic.
  \item To describe the laws governing universal entities such as properties, relations,
        and propositions (i.e., states of affairs).
  \item To identify \emph{theoretical} mathematical objects and relations as well as
        the \emph{natural} mathematical objects such as natural numbers and natural sets.
  \item To analyze the distinction between fact and fiction and systematize the various
        relationships between stories, characters, and other fictional objects.
  \item To systematize our modal thoughts about possible (actual, necessary) objects,
        states of affairs, situations and worlds.
  \item To account for the deviant logic of propositional attitude reports, explain the
        informativeness of identity statements, and give a general account of the objective
        and cognitive content of natural language.
  \item To axiomatize philosophical objects postulated by other philosophers, such as Forms (Plato),
        concepts (Leibniz), monads (Leibniz), possible worlds (Leibniz), nonexistent objects (Meinong),
        senses (Frege), extensions of concepts (Frege), noematic senses (Husserl), the world as a
        state of affairs (early Wittgenstein), moments of time, etc.
\end{itemize}

The Theory of Abstract Objects has therefore the ambition and the potential to serve as a foundational
theory of metaphysics as well as mathematics and can provide a simple unified axiomatic framework that
allows reasoning about a huge variety of concepts throughout the sciences. This makes the attempt to represent the
theory using the universal reasoning approach of shallow semantical embeddings outlined in the previous
chapter particularly challenging and at the same time rewarding, if successful.

A successful implementation of
the theory which allows to utilize the existing sophisticated infrastructure for automated reasoning 
present in a framework like Isabelle/HOL would not only strongly support the applicability of shallow
semantical embeddings as a universal reasoning tool, but could also aid in spreading
the utilization of the theory itself as a foundational theory for various scientific fields by
enabling convenient interactive and automated reasoning in a verified framework.

\<close>

section\<open>Basic Principles\<close>

text\<open>
  Although the formal language of the theory is introduced in the next section,
  some of the basic concepts of the theory are presented in advance to provide
  further motivation for the formalism.

  The following are the two most important principles of the theory (see~@{cite MallyTheory}):

  \begin{itemize}
    \item \<open>\<exists>x(A!x & \<forall>F(xF \<equiv> \<phi>))\<close>
    \item \<open>x = y \<equiv> \<box>\<forall>F(xF \<equiv> yF)\<close>
  \end{itemize}

  The first statement asserts that for every condition on properties \<open>\<phi>\<close> there exists
  an abstract object that encodes exactly those properties satisfying \<open>\<phi>\<close>, whereas the
  second statement holds for two abstract objects \<open>x\<close> and \<open>y\<close> and states that
  they are equal, if and only if they necessarily encode the same properties.

  Together these two principles clarify the notion of abstract objects as the reification
  of property patterns: Any set of properties is objectified as a distinct abstract object.

  Using these principles it is already possible to postulate interesting abstract objects.

  For example the Leibnizian concept of an (ordinary) individual \<open>u\<close> can be 
  defined as \emph{the (unique) abstract object that encodes all properties that \<open>u\<close> exemplifies},
  formally: \mbox{\<open>\<iota>x A!x & \<forall>F (xF \<equiv> Fu)\<close>}
  
  Other interesting examples include possible worlds, Platonic Forms or even basic logical objects
  like truth values. The theory allows to formulate purely \emph{syntactic} definitions of
  objects like possible worlds and truth values and
  from these definitions it can be \emph{derived} that there are two truth values
  or that the application of the modal box operator to a proposition is equivalent to the proposition
  being true in all possible worlds (where \emph{being true in a possible world} is again defined
  syntactically).

  This is an impressive property of the Theory of Abstract Objects: it can \emph{syntactically}
  define objects that are usually only considered semantically.
\<close>
  
section\<open>The Language of PLM\<close>
  
text\<open>
The target of the embedding is the second-order fragment of object theory as described
in chapter 7 of Edward Zalta's upcoming \emph{Principia Logico-Metaphysica} (PLM)@{cite PM}.
The logical foundation of the theory uses a second-order modal logic (without primitive identity)
formulated using relational type theory that is modified to admit \emph{encoding} as a second mode
of predication besides the traditional \emph{exemplification}.
In the following an informal description of the important aspects of the language is provided;
for a detailed and fully formal description and the type-theoretic background refer to the respective
chapters of PLM@{cite PM}.

A compact description of the language can be given in Backus-Naur Form (BNF)\mbox{@{cite \<open>Definition (6)\<close> PM}},
as shown in figure~\ref{BNF}, in which the following grammatical categories are used:

\begin{tabular}[h]{ll}
  \<open>\<delta>\<close>   & individual constants \\
  \<open>\<nu>\<close>   & individual variables \\
  \<open>\<Sigma>\<^sup>n\<close>  & $n$-place relation constants ($n \geq 0$) \\
  \<open>\<Omega>\<^sup>n\<close>  & $n$-place relation variables ($n \geq 0$) \\
  \<open>\<alpha>\<close>   & variables \\
  \<open>\<kappa>\<close>   & individual terms \\
  \<open>\<Pi>\<^sup>n\<close>  & $n$-place relation terms ($n \geq 0$) \\
  \<open>\<Phi>\<^sup>*\<close>  & propositional formulas \\
  \<open>\<Phi>\<close>   & formulas \\
  \<open>\<tau>\<close>   & terms
\end{tabular}

\begin{figure}[!h]
  \caption{BNF grammar of the language of PLM\cite[p. 170]{PM}}
  \centering
  \includegraphics{BNF.pdf}
  \label{BNF}
\end{figure}

The language distinguishes between two types of basic formulas,
namely (non-propositional) \emph{formulas} that \emph{may} contain encoding subformulas and
\emph{propositional formulas} that \emph{may not} contain encoding subformulas. Only propositional
formulas may be used in \<open>\<lambda>\<close>-expressions. The main reason for this distinction will be explained
in section~\ref{russell-paradox}.

Note that there is a case in which propositional formulas \emph{can} contain encoding
expressions. This is due to the fact that \emph{subformula} is defined in such a
way that \<open>xQ\<close> is \emph{not} a subformula of \<open>\<iota>x(xQ)\<close>\footnote{For
a formal definition of subformula refer to definition (\ref{PM-df-subformula}) in @{cite PM}.}.
Thereby \<open>F\<iota>x(xQ)\<close> is a propositional formula and \<open>[\<lambda>y F\<iota>x(xQ)]\<close> a well-formed
\<open>\<lambda>\<close>-expression. On the other hand \<open>xF\<close> is not a propositional formula and therefore
\<open>[\<lambda>x xF]\<close> not a well-formed \<open>\<lambda>\<close>-expression. This fact will become relevant in
the discussion in section~\ref{paradox}, that describes a paradox in the formulation of
the theory in the draft of PLM at the time of writing\footnote{At the time of writing several
options are being considered that can restore the consistency of the theory while retaining all
theorems of PLM.}.

Furthermore the theory contains a designated relation constant \<open>E!\<close> to be read as
\emph{being concrete}. Using this constant the distinction between ordinary and abstract objects
is defined as follows:

  \begin{itemize}
    \item \<open>O! =\<^sub>d\<^sub>f [\<lambda>x \<^bold>\<diamond>E!x]\<close>
    \item \<open>A! =\<^sub>d\<^sub>f [\<lambda>x \<^bold>\<not>\<^bold>\<diamond>E!x]\<close>
  \end{itemize}

So ordinary objects are possibly concrete, whereas abstract objects cannot possibly be concrete.

The language does not contain a primitive identity, but
\emph{defines} an identity for each type of term as follows:

\begin{tabular}{lc}
  ordinary objects & \<open>x =\<^sub>E y =\<^sub>d\<^sub>f O!x & O!y & \<box>(\<forall>F Fx \<equiv> Fy)\<close>\\
  individuals & \<open>x = y =\<^sub>d\<^sub>f x =\<^sub>E y \<or> (A!x & A!y & \<box>(\<forall>F xF \<equiv> yF))\<close>\\
  one-place relations & \<open>F\<^sup>1 = G\<^sup>1 =\<^sub>d\<^sub>f \<box>(\<forall>x xF\<^sup>1 \<equiv> xG\<^sup>1)\<close>\\
  zero-place relations & \<open>F\<^sup>0 = G\<^sup>0 =\<^sub>d\<^sub>f [\<lambda>y F\<^sup>0] = [\<lambda>y G\<^sup>0]\<close>
\end{tabular}

The identity for \<open>n\<close>-place relations for \<open>n \<ge> 2\<close> is defined in terms of the
identity of one-place relations, see (\ref{PM-p-identity})@{cite PM} for the full details.

The identity for ordinary objects follows Leibniz' law of the identity of indiscernibles:
Two ordinary objects that necessarily exemplify the same properties are identical.
Abstract objects, however, are only identical if they necessarily \emph{encode} the same
properties. As mentioned in the previous section this goes along with the concept of
abstract objects as the reification of property patterns.

Notably the identity for properties has a different definition than one would expect from
classical logic. Classically two properties are considered identical if and only if they
necessarily are \emph{exemplified} by the same objects. The Theory of Abstract Objects, however,
defines two properties to be identical if and only if they are necessarily \emph{encoded} by
the same (abstract) objects. This has some interesting consequences that will be described
in more detail in section \ref{hyperintensionality} which describes the \emph{hyperintensionality}
of relations in the theory.
\<close>

section\<open>The Axioms\<close>
  
text\<open>

Based on the language above, an axiom system is defined that constructs a S5 modal logic with
an actuality operator, axioms for definite descriptions that go along with Russell's analysis
of descriptions, the substitution of identicals as per the defined identity, \<open>\<alpha>\<close>-,
\<open>\<beta>\<close>-, \<open>\<eta>\<close>- and a special \<open>\<iota>\<close>-conversion for \<open>\<lambda>\<close>-expressions, as well
as dedicated axioms for encoding. A full accounting of the axioms in their representation in the
embedding is found in section~\ref{axioms}. For the original axioms refer to @{cite \<open>Chap. 8\<close> PM}.
At this point the axioms of encoding are the most relevant, namely:

  \begin{itemize}
    \item \<open>xF \<rightarrow> \<box>xF\<close>
    \item \<open>O!x \<rightarrow> \<not>\<exists>F xF\<close>
    \item \<open>\<exists>x (A!x & \<forall>F (xF \<equiv> \<phi>))\<close>,\\ provided x doesn't occur free in \<open>\<phi>\<close>
  \end{itemize}

So encoding is modally rigid, ordinary objects do not encode properties and
most importantly the comprehension axiom for abstract objects that was already mentioned above:

For every condition on properties \<open>\<phi>\<close> there exists an abstract object, that encodes exactly
those properties, that satisfy \<open>\<phi>\<close>.

\<close>

section\<open>Hyperintensionality of Relations\<close>
  
text\<open>

\label{hyperintensionality}

An interesting property of the Theory of Abstract Objects results from the definition
of identity for one-place relations. Recall that two properties are defined to be identical
if and only if they are \emph{encoded} by the same (abstract) objects. The theory imposes no
restrictions whatsoever on which properties an abstract object encodes.
Let for example \<open>F\<close> be the property \emph{being the morning star} and \<open>G\<close> be the
property \emph{being the evening star}. Since the morning star and the evening star are
actually both the planet Venus, every object that \emph{exemplifies} \<open>F\<close> will also
\emph{exemplify} \<open>G\<close> and vice-versa: \<open>\<box>\<forall>x Fx \<equiv> Gx\<close>. However the concept of being
the morning star is different from the concept of being the evening star. The Theory of Abstract
Objects therefore does not prohibit the existence of an abstract object that \emph{encodes} \<open>F\<close>,
but does \emph{not} encode \<open>G\<close>. Therefore by the definition of identity for properties
it does \emph{not} hold that \<open>F = G\<close>. As a matter of fact the Theory of Abstract Objects
does not force \<open>F = G\<close> for any \<open>F\<close> and \<open>G\<close>. It rather stipulates what needs
to be proven, if \<open>F = G\<close> is to be established, namely that they are necessarily encoded by
the same objects. Therefore if two properties \emph{should} be equal in some context an axiom has to be added
to the theory that allows to prove that both properties are encoded by the same abstract objects.

The fact that the following relation terms do \emph{not} necessarily denote the same relations illustrates
the extent of this \emph{hyperintensionality}:

\begin{center}
    \<open>[\<lambda>y p \<or> \<not>p]\<close> and \<open>[\<lambda>y q \<or> \<not>q]\<close>\\
    \<open>[\<lambda>y p & q]\<close> and \<open>[\<lambda>y q & p]\<close>
\end{center}

Of course the theory can be extended in such a way that these properties are equal.
However, without additional axioms their equality is not derivable.

Although the relations of object theory are hyperintensional entities,
propositional reasoning is still governed by classical
extensionality. For example properties that are necessarily exemplified by the same objects can be
substituted for each other in an exemplification formula, the law of the excluded middle can be
used in propositional reasoning, etc.

The Theory of Abstract Objects is an \emph{extensional} theory of \emph{intensional}
entities\mbox{@{cite \<open>(\ref{PM-prop-equiv})\<close> PM}}.

\<close>
  
section\<open>The Aczel-Model\<close>

text\<open>
\label{aczel-model}

When thinking about a model for the theory one will quickly notice the following problem:
The comprehension axiom for abstract objects implies that for each set of properties there exists
an abstract object encoding exactly those properties. Considering the definition of identity there therefore
exists an injective map from the power set of properties to the set of abstract objects.
On the other hand for an object \<open>y\<close> the term \mbox{\<open>[\<lambda>x Rxy]\<close>} constitutes a property.
If for distinct abstract objects these properties were distinct, this would result in a violation of
Cantor's theorem, since this would mean that there is an injective map from the power set of properties
to the set of properties. So does the Theory of Abstract Objects as constructed above have a model?
An answer to this question was provided by Peter Aczel\footnote{In fact to our knowledge Dana Scott
proposed a first model for the theory before Peter Aczel that we believe is a special case of an
Aczel-model with only one \emph{special urelement}.} who proposed the model structure illustrated
in figure~\ref{aczel-model-graphic}.

\begin{figure}[!h]
  \caption{Illustration of the Aczel-Model, courtesy of Edward Zalta}
  \includegraphics[width=\textwidth]{aczel-model.pdf}
  \label{aczel-model-graphic}
\end{figure}

In the Aczel-model abstract objects are represented by sets of properties. This of course validates
the comprehension axiom of abstract objects. Properties on the other hand are not naively represented
by sets of objects, which would lead to a violation of Cantor's theorem, but rather as the sets of
\emph{urelements}. Urelements are partitioned into two groups, ordinary urelements
(\<open>C\<close> in the illustration) and special urelements (\<open>S\<close> in the illustration).
Ordinary urelements can serve as the denotations of ordinary objects. Every abstract object on
the other hand has a special urelement as its proxy. Which properties an abstract object exemplifies
depends solely on its proxy. However, the map from abstract objects to special urelements is
not injective; more than one abstract object can share the same proxy. This way a violation of
Cantor's theorem is avoided. As a consequence there are abstract objects, that
cannot be distinguished by the properties they exemplify. Interestingly the existence of abstract objects
that are exemplification-indistinguishable is a theorem of PLM, see (\ref{PM-aclassical2})@{cite PM}.

Although the Aczel-model illustrated in figure~\ref{aczel-model-graphic} is non-modal,
the extension to a modal version is straightforward by introducing primitive possible worlds
as in the Kripke semantics of modal logic.

Further note that relations in the Aczel-model are \emph{extensional}. Since properties are represented as the
power set of urelements, two properties are in fact equal if they are exemplified by the same objects.
Consequently statements like \<open>[\<lambda> p \<or> \<not>p] = [\<lambda> q \<or> \<not>q]\<close> are true in the model,
although they are not derivable from the axioms of object theory as explained in the previous section.

For this reason an \emph{intensional} variant of the Aczel-model is developed and used as the
basis of the embedding. The technicalities of this model are described in the next chapter
(see~\ref{hyper-aczel-model}).

\<close>
  
chapter\<open>The Embedding\<close>

text\<open>
  \label{embedding}
\<close>
  
section\<open>The Framework Isabelle/HOL\<close>

text\<open>
The embedding is implemented in Isabelle/HOL, that provides a functional higher-order logic
that serves as meta-logic. An introduction to Isabelle/HOL can be found in @{cite Isabelle}\footnote{
An updated version is available at \url{http://isabelle.in.tum.de/doc/tutorial.pdf} or in the
documentation of the current Isabelle release, see \url{http://isabelle.in.tum.de/}.}. For a general
introduction to HOL and its automation refer to @{cite B5}.

The Isabelle theory containing the embedding is included in the appendix and documented in this chapter.
Throughout the chapter references to the various sections of the appendix can be found.

This document itself is generated from a separate Isabelle theory that imports the complete
embedding. The terms and theorems discussed throughout this chapter (starting from~\ref{representation-layer})
are well-formed terms or valid theorems in the embedding, unless the contrary is stated explicitly. Furthermore
the \emph{pretty printing} facility of Isabelle's document generation has been utilized to
make it easier to distinguish between the embedded logic and the meta-logic: all expressions
that belong to the embedded logic are printed in blue color throughout the chapter.

For technical reasons this color coding could not be used for the raw Isabelle theory in the
appendix. Still note the use of bold print for the quantifiers and connectives of the embedded
logic.

\<close>
  
section\<open>A Russell-style Paradox\<close>

text\<open>
  \label{russell-paradox}

  One of the major challenges of an implementation of the Theory of Abstract Objects in functional
  logic is the fact that a naive representation of the \<open>\<lambda>\<close>-expressions of the theory using the
  unrestricted, \<open>\<beta>\<close>-convertible \<open>\<lambda>\<close>-expressions of functional logic results in the following
  paradox (see @{cite \<open>pp. 24-25\<close> rtt}):

  Assume \<open>[\<lambda>x \<exists>F (xF & \<not>Fx)]\<close> were a valid \<open>\<lambda>\<close>-expression denoting a relation.
  Now the comprehension axiom of abstract objects requires the following:

  \begin{center}
    \<open>\<exists>x (A!x & \<forall>F (xF \<equiv> F = [\<lambda>x \<exists>F (xF & \<not>Fx)]))\<close>
  \end{center}

  So there is an abstract object that encodes only the property \<open>[\<lambda>x \<exists>F (xF & \<not>Fx)]\<close>.
  Let \<open>b\<close> be such an object. Now first assume \<open>b\<close> exemplifies
  \<open>[\<lambda>x \<exists>F (xF & \<not>Fx)]\<close>. By \<open>\<beta>\<close>-reduction this implies that there exists a property, that
  \<open>b\<close> encodes, but does not exemplify. Since \<open>b\<close> only encodes \<open>[\<lambda>x \<exists>F (xF & \<not>Fx)]\<close>,
  but does also exemplify it by assumption this is a contradiction.

  Now assume \<open>b\<close> does not exemplify \<open>[\<lambda>x \<exists>F (xF & \<not>Fx)]\<close>. By \<open>\<beta>\<close>-reduction it
  follows that there does not exist a property that \<open>b\<close> encodes, but does not exemplify.
  Since \<open>b\<close> encodes \<open>[\<lambda>x \<exists>F (xF & \<not>Fx)]\<close> by construction and does not exemplify
  it by assumption this is again a contradiction.

  This paradox is prevented in the formulation of object theory by disallowing encoding
  subformulas in \<open>\<lambda>\<close>-expressions, so in particular \<open>[\<lambda>x \<exists>F (xF & \<not>Fx)]\<close> is not
  part of the language. However during the construction of the embedding it was discovered
  that this restriction is not sufficient to prevent paradoxes in general. This is discussed
  in section~\ref{paradox}. The solution used in the embedding is described in
  section~\ref{lambda-expressions}.
\<close>  

section\<open>Basic Concepts\<close>

text\<open>

The introduction mentioned that shallow semantical embeddings were used to successfully represent
different varieties of modal logic by implementing them using Kripke semantics. The advantage here
is that Kripke semantics is well understood and there are extensive results about its soundness and
completeness that can be utilized in the analysis of semantical embeddings (see~@{cite ModalLogics}).

For the Theory of Abstract Objects the situation is different. Section~\ref{aczel-model} already
established that even a modal version of the traditional Aczel-model is extensional and therefore
theorems are true in it, that are not derivable from the axioms of object theory.
On the other hand the last section showed that care has to be taken to ensure the consistency of
an embedding of the theory in functional logic.

For this reason the embedding first constructs a hyperintensional version of the Aczel-model
that serves as a provably consistent basis for the theory. Then several abstraction layers
are implemented on top of the model structure in order to enable reasoning that is independent
of the particular representation. These concepts are described in more
detail in the following sections.

\<close>

subsection\<open>Hyperintensional Aczel-model\<close>
  
text\<open>

\label{hyper-aczel-model}

As mentioned in section~\ref{aczel-model} it is straightforward to extend
the traditional (non-modal) Aczel-model to a modal version by introducing
primitive possible worlds following the Kripke semantics for a modal S5 logic.

Relations in the resulting Aczel-model are, however, still \emph{extensional}.
Two relations that are necessarily exemplified by the same objects are equal. 
The Aczel-model that is used as the basis for the embedding therefore introduces
\emph{states} as another primitive besides possible worlds. Truth values are
represented as ternary functions from states and possible worlds to booleans;
relations as functions from urelements, states and possible worlds to booleans.

Abstract objects are still defined as sets of one-place relations and the division
of urelements into ordinary urelements and special urelements, that serve as proxies
for abstract objects, is retained as well. Consequently encoding can still be defined
as set membership of a relation in an abstract object. Exemplification is defined
as function application of a relation to the urelement corresponding to an individual,
a state and a possible world.

The semantic truth evaluation of a proposition in a given possible world is defined
as its evaluation for a designated \emph{actual state} and the possible world.

Logical connectives are defined to behave classically in the \emph{actual state}, but
have undefined behavior in other states.

The reason for this construction becomes apparent if one considers the definition of
the identity of relations: relations are considered identical if they are \emph{encoded}
by the same abstract objects. In the constructed model encoding depends on the behavior of
a relation in all states. Two relations can necessarily be \emph{exemplified} by the
same objects in the actual state, but still not be identical, since they can differ
in other states. Therefore hyperintensionality of relations is achieved.

The dependency on states is not limited to relations, but introduced to propositions,
connectives and quantifiers as well, although the semantic truth conditions of formulas
only depend on the evaluation for the actual state. The reason for this is to be able to define
\<open>\<lambda>\<close>-expressions (see section~\ref{lambda-expressions}) and to extend the
hyperintensionality of relations to them. Since the behavior of logical connectives is undefined
in states other than the actual state, the behavior of \<open>\<lambda>\<close>-expressions - although classical
in the actual state - remains undefined for different states.

In summary, since the semantic truth of a proposition solely depends on its evaluation for the designated
actual state, in which the logical connectives are defined to behave classically, the reasoning about
propositions remains classical, as desired. On the other hand the additional dependency on states allows
a representation of the hyperintensionality of relations.

The technical details of the implementation are described in section~\ref{representation-layer}.
\<close>

subsection\<open>Layered Structure\<close>
  
text\<open>

Although the constructed variant of the Aczel-model preserves the hyperintensionality of relations
in the theory, it is still known that there are true theorems in this model
that are not derivable from the axioms of object theory (see~\ref{artificial-theorems}).

Given this lack of a model with a well-understood degree of soundness and completeness, the embedding uses
a different approach than other semantical embeddings, namely the embedding is divided into
several \emph{layers} as follows:

\begin{itemize}
  \item The first layer represents the primitives of PLM using the described hyperintensional
        and modal variant of the Aczel-model.
  \item In a second layer the objects of the embedded logic constructed in the first layer are
        considered as primitives and some of their semantic properties are derived using the
        background logic as meta-logic.
  \item The third layer derives the axiom system of PLM mostly using the semantics of the second
        layer and partly using the model structure directly.
  \item Based on the third layer the deductive system PLM as described in @{cite \<open>Chap. 9\<close> PM}
        is derived solely using the axiom system of the third layer and the fundamental meta-rules
        stated in PLM. The model structure and the constructed semantics are explicitly
        not used in any proofs. Thereby the reasoning in this last layer is independent of the
        first two layers.
\end{itemize}

The rationale behind this approach is the following:
The first layer provides a representation of the embedded logic that is provably consistent.
Only minimal axiomatization is necessary, whereas the main construction is purely definitional.
Since the subsequent layers don't contain any additional axiomatization (the axiom system in the third layer
is \emph{derived}) their consistency is thereby guaranteed as well.

The second layer tries to abstract away from the details of the representation by implementing an
approximation of the formal semantics of PLM\footnote{Our thanks to Edward Zalta for supplying
us with a preliminary version of the corresponding unpublished chapter of PLM.}. The long time goal
would be to arrive at the representation of a complete semantics in this layer, that would be sufficient
to derive the axiom system in the next layer and which any specific model structure would have to satisfy.
Unfortunately this could not be achieved so far, but it was possible to lay some foundations for future work.

At the moment full abstraction from the representation layer is only achieved after deriving the axiom
system in the third layer. Still it can be reasoned that in any model of object theory the axiom system
has to be derivable and therefore by disallowing all further proofs to rely on the representation
layer and model structure directly the derivation of the deductive system PLM is universal. The only
exceptions are the primitive meta-rules of PLM: modus ponens, RN (necessitation) and
GEN (universal generalization), as well as the deduction rule. These rules do not follow from the axiom system
itself, but are derived from the semantics in the second layer (see~\ref{PLM-metarules}).
Still as the corresponding semantical rules will again have to be derivable for \emph{any} model,
this does not have an impact on the universality of the subsequent reasoning.

The technical details of the constructed embedding are described in the following sections.
\pagebreak
\<close>

section\<open>The Representation Layer\<close>
  
text\<open>

\label{representation-layer}

The first layer of the embedding (see \ref{TAO_Embedding}) implements the variant
of the Aczel-model described in section~\ref{hyper-aczel-model} and builds a representation
of the language of PLM in the logic of Isabelle/HOL. This process is outlined step by step
throughout this section.

\<close>
  
subsection\<open>Primitives\<close>

text\<open>
The following primitive types are the basis of the embedding (see \ref{TAO_Embedding_Primitives}):

\begin{itemize}
  \item Type @{type i} represents possible worlds in the Kripke semantics.
  \item Type @{type j} represents \emph{states} as described in section~\ref{hyper-aczel-model}.
  \item Type @{type bool} represents meta-logical truth values (\<open>True\<close> or \<open>False\<close>)
        and is inherited from Isabelle/HOL.
  \item Type @{type \<omega>} represents ordinary urelements.
  \item Type @{type \<sigma>} represents special urelements.
\end{itemize}

Two constants are introduced:

\begin{itemize}
  \item The constant @{term dw} of type @{typeof dw} represents the designated actual world.
  \item The constant @{term dj} of type @{typeof dj} represents the designated actual state.
\end{itemize}

Based on the primitive types above the following types are defined (see \ref{TAO_Embedding_Derived_Types}):

\begin{itemize}
  \item Type @{type \<o>} is defined as the set of all functions of type @{typ "j\<Rightarrow>i\<Rightarrow>bool"} and
        represents propositions in the embedded logic.
  \item Type @{type \<upsilon>} is defined as @{datatype \<upsilon>}. This type represents urelements and an object
        of this type can be either an ordinary or a special urelement (with the respective type
        constructors @{term \<omega>\<upsilon>} and @{term \<sigma>\<upsilon>}).
  \item Type @{type \<Pi>\<^sub>0} is defined as a synonym for type @{type \<o>} and represents zero-place
        relations.
  \item Type @{type \<Pi>\<^sub>1} is defined as the set of all functions of type \mbox{@{typ "\<upsilon>\<Rightarrow>j\<Rightarrow>i\<Rightarrow>bool"}}
        and represents one-place relations (for an urelement a one-place relation evaluates
        to a truth value in the embedded logic; for an urelement, a state and a possible world
        it evaluates to a meta-logical truth value).
  \item Type @{type \<Pi>\<^sub>2} is defined as the set of all functions of type \mbox{@{typ "\<upsilon>\<Rightarrow>\<upsilon>\<Rightarrow>j\<Rightarrow>i\<Rightarrow>bool"}}
        and represents two-place relations.
  \item Type @{type \<Pi>\<^sub>3} is defined as the set of all functions of type \mbox{@{typ "\<upsilon>\<Rightarrow>\<upsilon>\<Rightarrow>\<upsilon>\<Rightarrow>j\<Rightarrow>i\<Rightarrow>bool"}}
        and represents three-place relations.
  \item Type @{type \<alpha>} is defined as a synonym of the type of sets of one-place relations \<open>\<Pi>\<^sub>1 set\<close>,
        i.e. every set of one-place relations constitutes an object of type @{type \<alpha>}. This type
        represents abstract objects.
  \item Type @{type \<nu>} is defined as @{datatype \<nu>}. This type represents individuals and can
        be either an ordinary urelement of type @{type \<omega>} or an abstract object of type @{type \<alpha>} (with the
        respective type constructors @{term \<omega>\<nu>} and @{term \<alpha>\<nu>}).
  \item Type @{type \<kappa>} is defined as the set of all objects of type @{typ "\<nu> option"} and
        represents individual terms. The type @{typ "'a option"} is part of Isabelle/HOL and
        consists of a type constructor @{term "Some x"} for an object @{term "x"} of type @{typ 'a}
        (in this case type @{type \<nu>}) and an additional special element called @{term "None"}.
        @{term "None"} is used to represent individual terms that are definite descriptions
        that are not logically proper (i.e. they do not denote an individual).
\end{itemize}

\begin{remark}
  The Isabelle syntax @{theory_text "typedef \<o> = UNIV::(j\<Rightarrow>i\<Rightarrow>bool) set morphisms eval\<o> make\<o> .."}
  found in the theory source in the appendix introduces a new abstract type @{type \<o>} that is represented
  by the full set (@{term UNIV})   of objects of type @{typ "j\<Rightarrow>i\<Rightarrow>bool"}. The morphism \<open>eval\<o>\<close> maps
  an object of abstract type @{type \<o>} to its representative of type @{typ "j\<Rightarrow>i\<Rightarrow>bool"}, whereas 
  the morphism \<open>make\<o>\<close> maps an object of type @{typ "j\<Rightarrow>i\<Rightarrow>bool"} to the object
  of type @{type \<o>} that is represented by it. Defining these abstract types makes it
  possible to consider the defined types as primitives in later stages of the embedding,
  once their meta-logical properties are derived from the underlying representation.
  For a theoretical analysis of the representation layer the type @{type \<o>} can be considered
  a synonym of @{typ "j\<Rightarrow>i\<Rightarrow>bool"}.

  The Isabelle syntax @{theory_text "setup_lifting type_definition_\<o>"} allows definitions for the
  abstract type @{type \<o>} to be stated directly for its representation type @{typ "j\<Rightarrow>i\<Rightarrow>bool"}
  using the syntax @{theory_text "lift_definition"}.

  For the sake of readability in the documentation of the embedding the morphisms are omitted
  and definitions are stated directly for the representation types\footnote{The omission of the
  morphisms is achieved using custom \emph{pretty printing} rules for the document generation
  facility of Isabelle. The full technical details without these minor omissions can be found in the
  raw Isabelle theory in the appendix.}.
\end{remark}

\<close>

subsection\<open>Individual Terms and Definite Descriptions\<close>

text\<open>
\label{individual-terms-and-descriptions}

There are two basic types of individual terms in PLM: definite descriptions and individual variables
(and constants). Every logically proper definite description denotes an individual. A definite
description is logically proper if its matrix is (actually) true for a unique individual.

In the embedding the type @{type \<kappa>} encompasses all individual terms, i.e. individual variables,
constants \emph{and} definite descriptions. An individual (i.e. a variable or constant
of type @{type \<nu>}) can be used in place of an individual term of type @{type \<kappa>} via the decoration
@{term "embedded_style (DUMMY\<^sup>P)"} (see~\ref{TAO_Embedding_IndividualTerms}):

\begin{center}
  @{thm \<nu>\<kappa>.rep_eq[where x=x, THEN embedded_meta_eq]}
\end{center}

The expression @{term "embedded_style (x\<^sup>P)"} (of type @{typeof "x\<^sup>P"}) is marked to be
logically proper (it can only be substituted by objects that are internally of the form @{term "Some x"})
and to denote the individual @{term "x"}.

Definite descriptions are defined as follows:

\begin{center}
  @{thm that.rep_eq[where x=\<phi>, THEN embedded_meta_eq]}
\end{center}

If the propriety condition of a definite description @{prop "\<exists>!x. \<phi> x dj dw"} holds,
i.e. \emph{there exists a unique @{term "x"}, such that @{term "\<phi> x"} holds for the actual state and
the actual world}, the term \mbox{@{term "embedded_style (\<^bold>\<iota>x . \<phi> x)"}} evaluates to @{term "Some (THE x . \<phi> x dj dw)"}.
Isabelle's @{theory_text THE} operator evaluates to the unique object, for which the given condition holds,
if there is such a unique object, and is undefined otherwise. If the propriety condition does not hold,
the term evaluates to @{term "None"}.

The following meta-logical functions are defined to aid in handling individual terms:

\begin{itemize}
  \item @{thm[display] proper.rep_eq}
  \item @{thm[display] rep.rep_eq}
\end{itemize}

@{term "the"} maps an object of type @{typ "'a option"} that is of the form @{term "Some x"} to
@{term "x"} and is undefined for @{term "None"}. For an object of type @{type \<kappa>} the expression
@{term "proper x"} is true, if the term is logically proper, and if this is the case,
the expression @{term "rep x"} evaluates to the individual of type @{type \<nu>} that the term denotes.
\<close>

subsection\<open>Mapping from Individuals to Urelements\<close>

text\<open>

\label{individuals-to-urelements}

To map abstract objects to urelements (for which relations can be evaluated), a constant
@{term \<alpha>\<sigma>} of type @{typeof \<alpha>\<sigma>} is introduced, which maps abstract objects (of type @{type \<alpha>})
to special urelements (of type @{type \<sigma>}), see \ref{TAO_Embedding_AbstractObjectsToSpecialUrelements}.

To assure that every object in the full domain of urelements actually is an urelement for (one or more)
individual objects, the constant @{term \<alpha>\<sigma>} is axiomatized to be surjective.

Now the mapping @{term "\<nu>\<upsilon>"} of type @{typeof "\<nu>\<upsilon>"} can be defined as follows:

\begin{center}
@{thm \<nu>\<upsilon>_def[atomize]}
\end{center}

To clarify the syntax note that this is equivalent to the following:

\begin{center}
@{lemma "(\<forall> x . \<nu>\<upsilon> (\<omega>\<nu> x) = \<omega>\<upsilon> x) \<and> (\<forall> x . \<nu>\<upsilon> (\<alpha>\<nu> x) = \<sigma>\<upsilon> (\<alpha>\<sigma> x))" by (simp add: \<nu>\<upsilon>_def)}
\end{center}

So ordinary objects are simply converted to an urelements by the type constructor
@{term "\<omega>\<upsilon>"}, whereas for abstract objects the corresponding
special urelement under \<open>\<alpha>\<sigma>\<close> is converted to an urelement using the type constructor
@{term "\<sigma>\<upsilon>"}.

\begin{remark}
  Future versions of the embedding may introduce a dependency of the mapping from individuals
  to urelements on states (see~\ref{artificial-theorems}).
\end{remark}

\<close>

subsection\<open>Exemplification of n-place relations\<close>

text\<open>
  Exemplification of n-place relations can now be defined. Exemplification of zero-place
  relations is simply defined as the identity, whereas exemplification of n-place relations
  for \<open>n \<ge> 1\<close> is defined to be true, if all individual terms are logically proper and
  the function application of the relation to the urelements corresponding to the individuals
  yields true for a given possible world and state (see \ref{TAO_Embedding_Exemplification}):
\pagebreak
  \begin{itemize}
    \item @{thm[display] exe0.rep_eq[where x=p, THEN embedded_meta_eq]}
    \item @{thm[display] exe1.rep_eq[where x=F and xa=x, THEN embedded_meta_eq]}
    \item @{thm[display] exe2.rep_eq[where x=F and xa=x and xb=y, THEN embedded_meta_eq]}
    \item @{thm[display] exe3.rep_eq[where x=F and xa=x and xb=y and xc=z, THEN embedded_meta_eq]}
  \end{itemize}
\<close>

subsection\<open>Encoding\<close>

text\<open>
  Encoding is defined as follows (see \ref{TAO_Embedding_Encoding}):

  \begin{center}
  @{thm enc.rep_eq[of x F, THEN embedded_meta_eq]}
  \end{center}

  For a given state @{term s} and a given possible world @{term w} it holds that
  an individual term @{term x} encodes @{term F}, if @{term x} is logically proper,
  the denoted individual @{term "rep x"} is of the form @{term "\<alpha>\<nu> \<alpha>"} for
  some object @{term \<alpha>} (i.e. it is an abstract object) and @{term F} is contained in @{term \<alpha>}
  (recall that abstract objects are defined to be sets of one-place relations).

  Encoding is represented as a function of states and possible worlds to ensure type-correctness,
  but its evaluation does not depend on either. On the other hand whether @{term F} is contained
  in @{term \<alpha>} does depend on the behavior of @{term F} in \emph{all} states.
\<close>

subsection\<open>Connectives and Quantifiers\<close>

text\<open>
  \label{connectives}

  Following the model described in section~\ref{hyper-aczel-model} the connectives and quantifiers
  are defined in such a way that they behave classically if evaluated for the designated actual state @{term "dj"},
  whereas their behavior is governed by uninterpreted constants in any other state\footnote{Early attempts
  in using an intuitionistic version of connectives and quantifiers based on \cite{DOttaviano2012} were
  found to be insufficient to capture the full hyperintensionality of PLM, but served as inspiration
  for the current construction.}.

  For this purpose the following uninterpreted constants are introduced (see \ref{TAO_Embedding_Connectives}):
  \begin{itemize}
    \item @{const I_NOT} of type @{typeof I_NOT}
    \item @{const I_IMPL} of type @{typeof I_IMPL}
  \end{itemize}

  Modality is represented using the dependency on primitive possible worlds using
  a standard Kripke semantics for a S5 modal logic.

  The basic connectives and quantifiers are defined as follows
  (see \ref{TAO_Embedding_Connectives}):
  \begin{itemize}
    \item @{thm[display] not.rep_eq[of p, THEN embedded_meta_eq]}
    \item @{thm[display] impl.rep_eq[of p q, THEN embedded_meta_eq]}
    \item @{thm[display] forall\<^sub>\<nu>.rep_eq[of \<phi>, rename_abs s w x, THEN embedded_meta_eq]}
    \item @{thm[display] forall\<^sub>0.rep_eq[of \<phi>, rename_abs s w p, THEN embedded_meta_eq]}
    \item @{thm[display] forall\<^sub>1.rep_eq[of \<phi>, rename_abs s w F, THEN embedded_meta_eq]}
    \item @{thm[display] forall\<^sub>2.rep_eq[of \<phi>, rename_abs s w F, THEN embedded_meta_eq]}
    \item @{thm[display] forall\<^sub>3.rep_eq[of \<phi>, rename_abs s w F, THEN embedded_meta_eq]}
    \item @{thm[display] box.rep_eq[of p, THEN embedded_meta_eq]}
    \item @{thm[display] actual.rep_eq[of p, THEN embedded_meta_eq]}
  \end{itemize}

  Note in particular that negation and implication behave
  classically if evaluated for the actual state @{term "s = dj"}, but
  are governed by the uninterpreted constants @{term I_NOT} and @{term I_IMPL} for
  @{term "s \<noteq> dj"}:

  \begin{itemize}
  \item @{lemma[display] "s = dj \<Longrightarrow> eval\<o> (embedded_style (\<^bold>\<not>p)) s w = (\<not>eval\<o> (embedded_style (p)) s w)"
          by (unfold embedded_style_def, transfer, auto)}
  \item @{lemma "s \<noteq> dj \<Longrightarrow> eval\<o> (embedded_style (\<^bold>\<not>p)) s w = (I_NOT s (eval\<o> (embedded_style (p)) s) w)"
          by (unfold embedded_style_def, transfer, auto)}
  \item @{lemma[display] "s = dj \<Longrightarrow> eval\<o> (embedded_style (p \<^bold>\<rightarrow> q)) s w = (eval\<o> (embedded_style p) s w \<longrightarrow> eval\<o> (embedded_style q) s w)"
          by (unfold embedded_style_def, transfer, auto)}
  \item @{lemma "s \<noteq> dj \<Longrightarrow> eval\<o> (embedded_style (p \<^bold>\<rightarrow> q)) s w = (I_IMPL s (eval\<o> (embedded_style p) s) (eval\<o> (embedded_style q) s) w)"
          by (unfold embedded_style_def, transfer, auto)}
  \end{itemize}

  \begin{remark}
    Future research may conclude that non-classical behavior in states @{term "s \<noteq> dj"}
    for negation and implication is not sufficient for achieving the desired level of
    hyperintensionality for \<open>\<lambda>\<close>-expressions. It would be trivial to introduce additional
    uninterpreted constants to govern the behavior of the remaining connectives and quantifiers
    in such states as well, though. The remainder of the embedding would not be affected, i.e.
    no assumption about the behavior of connectives and quantifiers in states other than @{term "dj"}
    is made in the subsequent reasoning. At the time of writing non-classical behavior for
    negation and implication is considered sufficient.
  \end{remark}

\<close>
  
subsection\<open>$\lambda$-Expressions\<close>
  
text\<open>

  \label{lambda-expressions}

  The bound variables of the \<open>\<lambda>\<close>-expressions of the embedded logic are individual
  variables, whereas relations are represented as functions acting on urelements.
  Therefore the definition of the \<open>\<lambda>\<close>-expressions of the embedded logic is non-trivial.
  The embedding defines them as follows (see \ref{TAO_Embedding_Lambda}):

  \begin{itemize}
    \item @{thm[display] lambdabinder0.rep_eq[of p, THEN embedded_meta_eq]}
    \item @{thm[display] lambdabinder1.rep_eq[of \<phi>, THEN embedded_meta_eq]}
    \item @{thm[display, eta_contract=false] lambdabinder2.rep_eq[of "\<lambda> x y . \<phi> x y", THEN embedded_meta_eq]}
    \item @{thm[display, eta_contract=false] lambdabinder3.rep_eq[of "\<lambda> x y z . \<phi> x y z", THEN embedded_meta_eq]}
  \end{itemize}

\begin{remark}
  For technical reasons Isabelle only allows \<open>\<lambda>\<close>-expressions for one-place relations
  to use a nice binder notation. Although better workarounds may be possible, for now the
  issue is avoided by the use of the primitive \<open>\<lambda>\<close>-expressions of the background
  logic in combination with the constants @{term "\<^bold>\<lambda>\<^sup>2"} and @{term "\<^bold>\<lambda>\<^sup>3"} as shown above.
\end{remark}

  The representation of zero-place \<open>\<lambda>\<close>-expressions as the identity is straight-forward;
  the representation of n-place \<open>\<lambda>\<close>-expressions for \mbox{\<open>n \<ge> 1\<close>}
  is illustrated for the case \mbox{\<open>n = 1\<close>}:

  The matrix of the \<open>\<lambda>\<close>-expression @{term "embedded_style \<phi>"} is a function from individuals
  (of type @{type \<nu>}) to truth values (of type @{type \<o>}, resp. @{typ "j\<Rightarrow>i\<Rightarrow>bool"}).
  One-place relations are represented as functions of type @{typ "\<upsilon>\<Rightarrow>j\<Rightarrow>i\<Rightarrow>bool"} though,
  where @{type \<upsilon>} is the type of urelements.

  The \<open>\<lambda>\<close>-expression @{term "embedded_style (\<^bold>\<lambda>x. \<phi> x)"} evaluates to @{term "True"} for an urelement @{term u},
  a state @{term s} and a world @{term w}, if there is an individual @{term "embedded_style x"} in the preimage
  of @{term "u"} under @{term "\<nu>\<upsilon>"} and it holds that \mbox{@{term "eval\<o> (embedded_style (\<phi> x)) s w"}}.

  \begin{center}
  @{lemma "eval\<Pi>\<^sub>1 (embedded_style (\<^bold>\<lambda>x . \<phi> x)) u s w = (\<exists> x . \<nu>\<upsilon> x = u \<and> eval\<o> (embedded_style (\<phi> x)) s w)"
    by (simp add: embedded_style_def meta_defs meta_aux)}
  \end{center}

  If restricted to ordinary objects, the definition can be simplified, since @{term "\<nu>\<upsilon>"} is bijective
  on the set of ordinary objects:

  \begin{center}
  @{lemma "eval\<Pi>\<^sub>1 (embedded_style (\<^bold>\<lambda>x . \<phi> x)) (\<omega>\<upsilon> u) s w = eval\<o> (embedded_style (\<phi>) (\<omega>\<nu> u)) s w"
    by (simp add: embedded_style_def meta_defs meta_aux, metis \<nu>.exhaust \<nu>\<upsilon>_\<omega>\<nu>_is_\<omega>\<upsilon> \<upsilon>.inject(1) no_\<alpha>\<omega>)}
  \end{center}

  However in general @{term "\<nu>\<upsilon>"} can map several abstract objects to the same special urelement,
  so an analog statement for abstract objects does not hold for arbitrary @{term "\<phi>"}. As described
  in section~\ref{russell-paradox} such a statement would in fact not be desirable, since it would
  lead to inconsistencies.

  Instead the embedding introduces the concept of \emph{proper maps}.
  A map from individuals to propositions is defined to be proper if its truth evaluation for the actual state only
  depends on the urelements corresponding to the individuals (see \ref{TAO_Embedding_Proper}):

  \begin{itemize}
    \item @{thm[display] IsProperInX.rep_eq[of \<phi>]}
    \item @{thm[display] IsProperInXY.rep_eq[of \<phi>]}
    \item @{thm[display] IsProperInXYZ.rep_eq[of \<phi>]}
  \end{itemize}

  Now by the definition of proper maps the evaluation of \<open>\<lambda>\<close>-expressions behaves as expected
  for proper @{term "embedded_style \<phi>"}:

  \begin{center}
  @{lemma "IsProperInX (embedded_style \<phi>) \<longleftrightarrow> (\<forall> w x . eval\<Pi>\<^sub>1 (embedded_style (\<^bold>\<lambda>x . \<phi> (x\<^sup>P))) (\<nu>\<upsilon> x) dj w = eval\<o> (embedded_style (\<phi> (x\<^sup>P))) dj w)"
    by (auto simp: embedded_style_def meta_defs meta_aux IsProperInX_def)}
  \end{center}

  \begin{remark}
    The right-hand side of the equation above does not quantify over all states,
    but is restricted to the actual state @{term "dj"}.
    This is sufficient given that truth evaluation only depends on the actual state
    and goes along with the desired semantics of \<open>\<lambda>\<close>-expressions (see~\ref{semantics-lambda}).
  \end{remark}

  Maps that contain encoding formulas in their arguments are in general
  not proper and thereby the paradox mentioned in section~\ref{russell-paradox} is prevented.

  In fact proper maps are the most general kind of functions that may appear in a lambda-expression,
  such that \<open>\<beta>\<close>-conversion holds. In what way proper maps correspond to the formulas that PLM
  allows as the matrix of a \<open>\<lambda>\<close>-expression is a complex question and discussed separately in
  section~\ref{differences-lambda}.
\<close>
 

subsection\<open>Validity\<close>

text\<open>
  Semantic validity is defined as follows (see \ref{TAO_Embedding_Validity}):
  
  \begin{center}
    @{thm valid_in.rep_eq[of v "embedded_style \<phi>"]}
  \end{center}

  A formula is considered semantically valid for a possible world @{term v} if it evaluates
  to @{term True} for the actual state @{term dj} and the given possible world @{term v}.

  \begin{remark}
    The Isabelle Theory in the appendix defines the syntax \mbox{\<open>v \<Turnstile> p\<close>} in the representation
    layer, following the syntax used in the formal semantics of PLM.
    The syntax \mbox{@{term "[p in v]"}} that is easier to use in Isabelle due to bracketing the expression
    is only introduced after the semantics is derived in \ref{TAO_Semantics_Validity}.
    For simplicity only the latter syntax is used in this documentation.
  \end{remark}
\<close>

subsection\<open>Concreteness\<close>

text\<open>
  \label{concreteness}

  PLM defines concreteness as a one-place relation constant. For the embedding care has to
  be taken that concreteness actually matches the primitive distinction between ordinary and
  abstract objects. The following requirements have to be satisfied by the introduced notion of
  concreteness:
  \begin{itemize}
    \item Ordinary objects are possibly concrete. In the meta-logic this means that for every
          ordinary object there exists at least one possible world, in which the object is concrete.
    \item Abstract objects are not possibly concrete.
  \end{itemize}

  An additional requirement is enforced by axiom (\ref{PM-qml}.4)\cite{PM}, see~\ref{axioms-necessity}.
  To satisfy this axiom the following has to be assured:
  \begin{itemize}
    \item Possibly contingent objects exist. In the meta-logic this means that there exists
          an ordinary object and two possible worlds, such that the ordinary object is
          concrete in one of the worlds, but not concrete in the other.
    \item Possibly no contingent objects exist. In the meta-logic this means that there exists
          a possible world, such that all objects that are concrete in this world, are concrete
          in all possible worlds.
  \end{itemize}

  In order to satisfy these requirements a constant @{const ConcreteInWorld} is introduced,
  that maps ordinary objects (of type @{type \<omega>}) and possible worlds (of type @{type i})
  to meta-logical truth values (of type @{type bool}). This constant is axiomatized in the
  following way (see~\ref{TAO_Embedding_Concreteness}):
  \begin{itemize}
    \item @{thm OrdinaryObjectsPossiblyConcreteAxiom}
    \item @{thm PossiblyContingentObjectExistsAxiom}
    \item @{thm PossiblyNoContingentObjectExistsAxiom}
  \end{itemize}

  Concreteness can now be defined as a one-place relation:
  \begin{center}
    @{thm Concrete.rep_eq[THEN embedded_meta_eq]}
  \end{center}

  Whether an ordinary object is concrete is governed by the introduced constant, whereas
  abstract objects are never concrete.

\<close>

subsection\<open>The Syntax of the Embedded Logic\<close>


text\<open>

The embedding aims to provide a readable syntax for the embedded logic that is as close as possible
to the syntax of PLM and clearly distinguishes between the embedded
logic and the meta-logic. Some concessions have to be made due to the limitations of definable syntax
in Isabelle, though. Moreover exemplification and encoding have to use a dedicated syntax in order
to be distinguishable from function application.

The syntax for the basic formulas of PLM used in the embedding is summarized in the
following table:

\begin{center}
\begin{tabular}{l|l|l|c}
PLM & syntax in words & embedded logic & type \\
\hline
\<open>\<phi>\<close> & it holds that \<open>\<phi>\<close> & @{term "embedded_style (\<phi>)"} & @{type \<o>} \\
\<open>\<not>\<phi>\<close> & not \<open>\<phi>\<close> & @{term "embedded_style (\<^bold>\<not>\<phi>)"} & @{type \<o>}  \\
\<open>\<phi> \<rightarrow> \<psi>\<close> & \<open>\<phi>\<close> implies \<open>\<psi>\<close> & @{term "embedded_style (\<phi> \<^bold>\<rightarrow> \<psi>)"} & @{type \<o>}  \\
\<open>\<box>\<phi>\<close> & necessarily \<open>\<phi>\<close> & @{term "embedded_style (\<^bold>\<box>\<phi>)"} & @{type \<o>}  \\
\<open>\<A>\<phi>\<close> & actually \<open>\<phi>\<close> & @{term "embedded_style (\<^bold>\<A>\<phi>)"} & @{type \<o>}  \\
\<open>\<Pi>\<upsilon>\<close> & \<open>\<upsilon>\<close> (an individual term) exemplifies \<open>\<Pi>\<close> & @{term "embedded_style \<lparr>\<Pi>,\<upsilon>\<rparr>"} & @{type \<o>}  \\
\<open>\<Pi>x\<close> & \<open>x\<close> (an individual variable) exemplifies \<open>\<Pi>\<close> & @{term "embedded_style \<lparr>\<Pi>,x\<^sup>P\<rparr>"} & @{type \<o>}  \\
\<open>\<Pi>\<upsilon>\<^sub>1\<upsilon>\<^sub>2\<close> & \<open>\<upsilon>\<^sub>1\<close> and \<open>\<upsilon>\<^sub>2\<close> exemplify \<open>\<Pi>\<close> & @{term "embedded_style \<lparr>\<Pi>,\<upsilon>\<^sub>1,\<upsilon>\<^sub>2\<rparr>"} & @{type \<o>}  \\
\<open>\<Pi>xy\<close> & \<open>x\<close> and \<open>y\<close> exemplify \<open>\<Pi>\<close> & @{term "embedded_style \<lparr>\<Pi>,x\<^sup>P,y\<^sup>P\<rparr>"} & @{type \<o>}  \\
\<open>\<Pi>\<upsilon>\<^sub>1\<upsilon>\<^sub>2\<upsilon>\<^sub>3\<close> & \<open>\<upsilon>\<^sub>1\<close>, \<open>\<upsilon>\<^sub>2\<close> and \<open>\<upsilon>\<^sub>3\<close> exemplify \<open>\<Pi>\<close> & @{term "embedded_style \<lparr>\<Pi>,\<upsilon>\<^sub>1,\<upsilon>\<^sub>2,\<upsilon>\<^sub>3\<rparr>"} & @{type \<o>}  \\
\<open>\<Pi>xyz\<close> & \<open>x\<close>, \<open>y\<close> and \<open>z\<close> exemplify \<open>\<Pi>\<close> & @{term "embedded_style \<lparr>\<Pi>,x\<^sup>P,y\<^sup>P,z\<^sup>P\<rparr>"} & @{type \<o>}  \\
\<open>\<upsilon>\<Pi>\<close> & \<open>\<upsilon>\<close> encodes \<open>\<Pi>\<close> & @{term "embedded_style \<lbrace>\<upsilon>,\<Pi>\<rbrace>"} & @{type \<o>}  \\
\<open>\<iota>x\<phi>\<close> & \emph{the} \<open>x\<close>, such that \<open>\<phi>\<close> & @{term "embedded_style (\<^bold>\<iota>x . \<phi> x)"} & @{type \<kappa>}  \\
\<open>\<forall>x(\<phi>)\<close> & for all individuals \<open>x\<close> it holds that \<open>\<phi>\<close> & @{term "embedded_style (\<^bold>\<forall>\<^sub>\<nu> x . \<phi> x)"} & @{type \<o>} \\
\<open>\<forall>p(\<phi>)\<close> & for all propositions \<open>p\<close> it holds that \<open>\<phi>\<close> & @{term "embedded_style (\<^bold>\<forall>\<^sub>0 p . \<phi> p)"} & @{type \<o>} \\
\<open>\<forall>F(\<phi>)\<close> & for all relations \<open>F\<close> it holds that \<open>\<phi>\<close> & @{term "embedded_style (\<^bold>\<forall>\<^sub>1 F . \<phi> F)"} & @{type \<o>} \\
& & @{term "embedded_style (\<^bold>\<forall>\<^sub>2 F . \<phi> F)"} & \\
& & @{term "embedded_style (\<^bold>\<forall>\<^sub>3 F . \<phi> F)"} & \\
\<open>[\<lambda> p]\<close> & being such that \<open>p\<close> & @{term "embedded_style (\<^bold>\<lambda>\<^sup>0 p)"}  & @{typ \<Pi>\<^sub>0} \\
\<open>[\<lambda>x \<phi>]\<close> & being \<open>x\<close> such that \<open>\<phi>\<close> & @{term "embedded_style (\<^bold>\<lambda> x . \<phi> x)"} & @{type \<Pi>\<^sub>1} \\
\<open>[\<lambda>xy \<phi>]\<close> & being \<open>x\<close> and \<open>y\<close> such that \<open>\<phi>\<close> & @{term[eta_contract=false] "embedded_style (\<^bold>\<lambda>\<^sup>2 (\<lambda> x y . \<phi> x y))"} & @{type \<Pi>\<^sub>2} \\
\<open>[\<lambda>xyz \<phi>]\<close> & being \<open>x\<close>, \<open>y\<close> and \<open>z\<close> such that \<open>\<phi>\<close> & @{term[eta_contract=false] "embedded_style (\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z . \<phi> x y z))"} & @{type \<Pi>\<^sub>3}
\end{tabular}
\end{center}

\pagebreak

Several subtleties have to be considered:
\begin{itemize}
  \item @{term "n"}-place relations are only represented for \mbox{\<open>n \<le> 3\<close>}.
        As the resulting language is already expressive enough to represent the most interesting
        parts of the theory and it would be trivial to add analog implementations for
        \mbox{\<open>n > 3\<close>}, this is considered to be sufficient. Future work may attempt to construct a general
        representation for \<open>n\<close>-place relations for arbitrary \<open>n\<close>.
  \item Individual terms (that can be descriptions) and individual variables, resp. constants have
        different types. Exemplification and encoding is defined for individual terms of type @{type \<kappa>}.
        Individual variables (i.e. variables of type @{type \<nu>}) or individual constants
        (i.e. constants of type @{type \<nu>}) can be converted to type @{type \<kappa>} using the
        decoration~@{term "embedded_style (DUMMY\<^sup>P)"}.
  \item In PLM a general term @{term "\<phi>"}, as it occurs in definite descriptions,
        quantification formulas and \<open>\<lambda>\<close>-expressions above, can contain \emph{free} variables. If
        such a term occurs within the scope of a variable binding operator, free occurrences of
        the variable are considered to be \emph{bound} by the operator. In the embedding this concept
        is replaced by representing @{term "embedded_style \<phi>"} as a \emph{function} acting on the bound variables
        and using the native concept of binding operators in Isabelle.
  \item The representation layer of the embedding defines a separate quantifier for every type of
        variable in PLM. This is done to assure that only quantification ranging over these types
        is part of the embedded language. The definition of a general quantifier in the representation layer
        could for example be used to quantify over individual \emph{terms} (of type @{type \<kappa>}), whereas
        only quantification ranging over individuals (of type @{type \<nu>}) is part of the language of PLM.
        After the semantics is introduced in section~\ref{semantics}, a \emph{type class} is constructed
        that is characterized by the semantics of quantification and instantiated for all variable types.
        This way a general binder that can be used for all variable types can be defined. The details
        of this approach are explained in section~\ref{general-quantifier}.
\end{itemize}

The syntax used for stating that a proposition is semantically valid is the following:
\begin{center}
    @{term "[\<phi> in v]"}
\end{center}

Here @{term "embedded_style \<phi>"} and @{term "v"} are free variables (in the meta-logic).
Therefore, stating the expression above as a lemma will implicitly be a quantified statement over all
propositions @{term "embedded_style \<phi>"} and all possible worlds @{term "v"} (unless
@{term "embedded_style \<phi>"} or @{term "v"} are explicitly restricted in the current scope
or globally declared as constants).

\vfill
\pagebreak
\<close>

(*<*)
context Semantics
begin
(*>*)

section\<open>Semantic Abstraction\<close>
  
text\<open>
\label{semantics}

The second layer of the embedding (see~\ref{TAO_Semantics}) abstracts away from the technicalities
of the representation layer and states the truth conditions for formulas of the embedded logic
in a similar way as the (at the time of writing unpublished) semantics of object theory.

\<close>

subsection\<open>Domains and Denotation Functions\<close>
  
text\<open>
In order to do so the abstract types introduced in the representation layer
@{typ \<kappa>}, @{typ \<o>} resp. @{typ \<Pi>\<^sub>0}, @{typ \<Pi>\<^sub>1}, @{typ \<Pi>\<^sub>2} and @{typ \<Pi>\<^sub>3} are considered
as primitive types and assigned semantic domains: @{type R\<^sub>\<kappa>}, @{typ R\<^sub>0}, @{typ R\<^sub>1},
@{typ R\<^sub>2} and @{typ R\<^sub>3} (see~\ref{TAO_Semantics_Semantics_Domains}).

For the embedding the definition of these semantic domains is trivial, since the abstract types of
the representation layer are already modeled using representation sets. Therefore the semantic domain
for each type can simply be defined as the type of its representatives.

As a next step denotation functions are defined that assign semantic denotations to the objects of each
abstract type (see~\ref{TAO_Semantics_Semantics_Denotations}).
The formal semantics of PLM does not a priori assume that every term has a denotation. Therefore,
the denotation functions are represented as functions that map to the \<open>option\<close> type of the
respective domain. This way they can either map a term to @{term "Some x"}, if the term denotes
@{term "x"}, or to @{term "None"}, if the term does not denote.

In the embedding all relation terms always denote, therefore the denotation functions @{term "d\<^sub>0"},
\<open>\<dots>\<close>, @{term "d\<^sub>3"} for relations can simply be defined as the type constructor @{term "Some"}.
Individual terms on the other hand are already represented by an \<open>option\<close> type,
so the denotation function @{term "d\<^sub>\<kappa>"} can be defined as the identity.

Moreover the primitive type of possible worlds @{type i} is used as the semantic domain of possible
worlds @{typ W} and the primitive actual world @{term "dw"} as the semantic actual world
@{term "w\<^sub>0"} (see~\ref{TAO_Semantics_Semantics_Actual_World}).

\begin{remark}
Although the definitions for semantic domains and denotations may seem redundant, conceptually
the abstract types of the representation layer now have the role of primitive types. Although for
simplicity the last section regarded the type @{type \<o>} as synonym of \mbox{@{typ "j\<Rightarrow>i\<Rightarrow>bool"}}, it was
introduced as a distinct type for which the set of all functions of type \mbox{@{typ "j\<Rightarrow>i\<Rightarrow>bool"}} merely
serves as the underlying set of representatives. An object of type @{type \<o>} cannot directly be
substituted for a variable of type \mbox{@{typ "j\<Rightarrow>i\<Rightarrow>bool"}}. To do so it first has to be mapped to its
representative of type \mbox{@{typ "j\<Rightarrow>i\<Rightarrow>bool"}} by the use of the morphism @{term "eval\<o>"} that was introduced
in the type definition and omitted in the last section for the sake of readability. Therefore although
the definitions of the semantic domains and denotation functions may seem superfluous, the domains are
different types than the corresponding abstract type and the denotation functions are functions between
distinct types (note the use of @{theory_text "lift_definition"} rather than @{theory_text "definition"} 
for the denotation functions in~\ref{TAO_Semantics_Semantics_Denotations} that allows to define
functions on abstract types in the terms of the underlying representation types).
\end{remark}

\<close>

subsection\<open>Exemplification and Encoding Extensions\<close>
  
text\<open>
Semantic truth conditions for exemplification formulas are defined using \emph{exemplification extensions}.
Exemplification extensions are functions relative to
semantic possible worlds that map objects in the domain of \<open>n\<close>-place relations to meta-logical truth
values in the case \mbox{\<open>n = 0\<close>} and sets of \<open>n\<close>-tuples of objects in the domain
of individuals in the case \mbox{\<open>n \<ge> 1\<close>}. Formally they are defined as follows
(see~\ref{TAO_Semantics_Semantics_Exemplification_Extensions}):

\begin{itemize}
  \item @{thm[display] ex0_def[expand2, of p w]}
  \item @{thm[display] ex1_def[expand2, of F w]}
  \item @{thm[display] ex2_def[expand2, of R w]}
  \item @{thm[display] ex3_def[expand2, of R w]}
\end{itemize}

The exemplification extension of a \<open>0\<close>-place relation is its evaluation for the actual state and the
given possible world. The exemplification extension of \<open>n\<close>-place relations \mbox{(\<open>n \<ge> 1\<close>)}
in a possible world is the set of all (tuples of) \emph{individuals} that are mapped to
\emph{urelements} for which the relation evaluates to true for the given possible world and the
actual state. This is in accordance with the constructed Aczel-model (see~\ref{hyper-aczel-model}).

Conceptually, exemplification extensions as maps to sets of \emph{individuals} are independent of the underlying
model and in particular do not require the concept of \emph{urelements} as they are present in an
Aczel-model. Their use in the definition of truth conditions for exemplification formulas below
is therefore an abstraction away from the technicalities of the representation layer.

Similarly to the exemplification extension for one-place relations an \emph{encoding extension}
is defined as follows (see~\ref{TAO_Semantics_Semantics_Encoding_Extension}):

\begin{center}
  @{thm en_def[expand1, of F]}
\end{center}

The encoding extension of a relation is defined as the set of all abstract objects that contain
the relation. Since encoding is modally rigid the encoding extension does not need to be relativized
for possible worlds.
\<close>

subsection\<open>Truth Conditions of Formulas\<close>

text\<open>

Based on the definitions above it is now possible to define truth conditions
for the atomic formulas of the language.

For exemplification formulas of \<open>n\<close>-place relations
it suffices to consider the case of one-place relations, for which the truth condition is defined
as follows (see~\ref{TAO_Semantics_Semantics_Exemplification}):

\begin{center}
  @{thm T1_1[of w "embedded_style \<Pi>" "embedded_style \<kappa>"]}
\end{center}

The relation term @{term "embedded_style \<Pi>"} is exemplified by an individual term @{term "embedded_style \<kappa>"} in a possible world
@{term "w"} if both terms have a denotation and the denoted individual is contained in the exemplification
extension of the denoted relation in @{term "w"}. The definitions for \<open>n\<close>-place relations
\mbox{(\<open>n > 1\<close>)} and \<open>0\<close>-place relations are analog.

The truth condition for encoding formulas is defined in a similar manner
(see~\ref{TAO_Semantics_Semantics_Encoding}):

\begin{center}
  @{thm T2[of w "embedded_style \<kappa>" "embedded_style \<Pi>"]}
\end{center}

The only difference to exemplification formulas is that the encoding extension does not depend
on the possible world @{term "w"}.

The truth conditions for complex formulas are straightforward
(see~\ref{TAO_Semantics_Semantics_Complex_Formulas}):

\begin{itemize}
  \item @{thm[display] T4[of w \<psi>]}
  \item @{thm[display] T5[of w \<psi> \<chi>]}
  \item @{thm[display] T6[of w \<psi>]}
  \item @{thm[display] T7[of w \<psi>]}
  \item @{thm[display] T8_\<nu>[of w \<psi>]}
  \item @{thm[display] T8_0[of w \<psi>]}
  \item @{thm[display] T8_1[of w \<psi>]}
  \item @{thm[display] T8_2[of w \<psi>]}
  \item @{thm[display] T8_3[of w \<psi>]}
\end{itemize}

A negation formula @{term "embedded_style (\<^bold>\<not>\<psi>)"} is semantically true in a possible world, if and only if
@{term "embedded_style \<psi>"} is not semantically true in the given possible world. Similarly truth conditions for
implication formulas and quantification formulas are defined canonically.

The truth condition of the modal box operator @{term "embedded_style (\<^bold>\<box>\<psi>)"} as @{term "embedded_style \<psi>"} being true in all
possible worlds, shows that modality follows a S5 logic. A formula involving the actuality operator @{term "embedded_style (\<^bold>\<A>\<psi>)"}
is defined to be semantically true, if and only if @{term "embedded_style \<psi>"} is true in the designated actual world.

\<close>

subsection\<open>Denotation of Definite Descriptions\<close>
  
text\<open>

The definition of the denotation of description terms (see~\ref{TAO_Semantics_Semantics_Descriptions})
can be presented in a more readable form by splitting it into its two cases and by using the meta-logical
quantifier for unique existence:
\begin{itemize}
  \item @{lemma[display] "(\<exists>!x. [\<psi> x in w\<^sub>0])
            \<Longrightarrow> d\<^sub>\<kappa> (embedded_style (\<^bold>\<iota>x. \<psi> x)) = Some (THE x. [\<psi> x in w\<^sub>0])"
    by (auto simp: embedded_style_def D3)}
  \item @{lemma[display] "\<not>(\<exists>!x. [\<psi> x in w\<^sub>0])
            \<Longrightarrow> d\<^sub>\<kappa> (embedded_style (\<^bold>\<iota>x. \<psi> x)) = None"
    by (auto simp: embedded_style_def D3)}
\end{itemize}

If there exists a unique @{term "x"}, such that @{term "embedded_style (\<psi> x)"} is true in the actual world,
the definite description denotes and its denotation is this unique @{term "x"}. Otherwise
the definite description fails to denote.

It is important to consider what happens if a non-denoting definite description occurs in a formula:
The only positions in which such a term could occur in a complex formula is in an exemplification expression
or in an encoding expression. Given the above truth conditions it becomes clear, that
the presence of non-denoting terms does \emph{not} mean that there are formulas without
truth conditions: Since exemplification and encoding formulas are defined to be true \emph{only if}
the contained individual terms have denotations, such formulas are @{term "False"} for non-denoting
individual terms.

\<close>

subsection\<open>Denotation of $\lambda$-Expressions\<close>

text\<open>

\label{semantics-lambda}

The most complex part of the semantic abstraction is the definition of denotations for \<open>\<lambda>\<close>-expressions.
The formal semantics of PLM is split into several cases and uses a special class of
\emph{Hilbert-Ackermann \<open>\<epsilon>\<close>-terms} that are challenging to represent. Therefore a simplified
formulation of the denotation criteria is used. Moreover the denotations of \<open>\<lambda>\<close>-expressions are
coupled to syntactical conditions. This fact is represented using the notion of \emph{proper maps}
as a restriction for the matrix of a \<open>\<lambda>\<close>-expression that was introduced in section~\ref{lambda-expressions}.
The definitions are implemented as follows (see~\ref{TAO_Semantics_Semantics_Lambda_Expressions}):

\begin{itemize}
  \item @{lemma[display] "d\<^sub>1 (embedded_style (\<^bold>\<lambda>x. \<lparr>\<Pi>, x\<^sup>P\<rparr>)) = d\<^sub>1 (embedded_style \<Pi>)"
          by (simp add: embedded_style_def D4_1)}
  \item @{lemma[display] "IsProperInX (embedded_style \<phi>) \<Longrightarrow> Some r = d\<^sub>1 (embedded_style (\<^bold>\<lambda>x. \<phi> (x\<^sup>P)))
          \<and> Some o\<^sub>1 = d\<^sub>\<kappa> (embedded_style x) \<longrightarrow> (o\<^sub>1 \<in> ex1 r w) = [\<phi> x in w]"
          by (simp add: embedded_style_def D5_1)}
  \item @{lemma[display] "Some r = d\<^sub>0 (embedded_style (\<^bold>\<lambda>\<^sup>0 \<phi>)) \<longrightarrow> ex0 r w = [\<phi> in w]"
    by (simp add: embedded_style_def D6)}
\end{itemize}

The first condition for \emph{elementary} \<open>\<lambda>\<close>-expressions is straightforward.
The general case in the second condition is more complex: Given that the matrix @{term "embedded_style \<phi>"}
is a proper map, the relation denoted by the \<open>\<lambda>\<close>-expression has the property, that for a
denoting individual term @{term "embedded_style x"}, the denoted individual is contained in
its exemplification extension for a possible world @{term "w"}, if and only if @{term "embedded_style (\<phi> x)"}
holds in @{term "w"}.
At a closer look this is the statement of \<open>\<beta>\<close>-conversion restricted to denoting individuals:
the truth condition of the \<open>\<lambda>\<close>-expression being exemplified by some denoting individual term,
is the same as the truth condition of the matrix of the term for the denoted individual.
Therefore it is clear that the precondition that @{term "embedded_style \<phi>"} is a proper map
is necessary and sufficient.
Given this consideration the case for \<open>0\<close>-place relations is straightforward and
the cases for \mbox{\<open>n \<ge> 2\<close>} are analog to the case \mbox{\<open>n = 1\<close>}.

\<close>

subsection\<open>Properties of the Semantics\<close>

text\<open>

  The formal semantics of PLM imposes several further restrictions some of which are derived as
  auxiliary lemmas. Furthermore some auxiliary statements that are specific to the underlying
  representation layer are proven.

  The following auxiliary statements are derived (see~\ref{TAO_Semantics_Semantics_Auxiliary_Lemmata}):
  \begin{enumerate}
    \item All relations denote, e.g. @{thm[display] propex\<^sub>1[of "embedded_style F"]}
    \item An individual term of the form @{term "embedded_style (x\<^sup>P)"} denotes @{term "x"}:
          @{lemma[display] "d\<^sub>\<kappa> (embedded_style (x\<^sup>P)) = Some x"
            by (simp add: embedded_style_def d\<^sub>\<kappa>_proper)}
    \item Every ordinary object is contained in the extension of the concreteness property for some
          possible world:
          @{lemma[display] "Some r = d\<^sub>1 (embedded_style (E!)) \<Longrightarrow> (\<forall> x . \<exists> w . \<omega>\<nu> x \<in> ex1 r w)"
            by (simp add: embedded_style_def ConcretenessSemantics1)}
    \item An object that is contained in the extension of the concreteness property in any world is
          an ordinary object:
          @{lemma[display] "Some r = d\<^sub>1 (embedded_style (E!)) \<Longrightarrow> (\<forall> x . x \<in> ex1 r w \<longrightarrow> (\<exists> y . x = \<omega>\<nu> y))"
            by (simp add: embedded_style_def ConcretenessSemantics2)}
    \item The denotation functions for relation terms are injective, e.g.
          @{thm[display] d\<^sub>1_inject[of "embedded_style F" "embedded_style G"]}
    \item The denotation function for individual terms is injective for denoting terms:
          @{thm[display] d\<^sub>\<kappa>_inject[of "o\<^sub>1" "embedded_style x" "embedded_style y"]}
  \end{enumerate}

  Especially statements 5 and 6 are only derivable due to the specific construction of
  the representation layer: since the semantic domains were defined as the representation sets
  of the respective abstract types and denotations were defined canonically, objects that have the
  same denotation are identical as objects of the abstract type. 3 and 4 are necessary to connect
  concreteness with the underlying distinction between ordinary and abstract objects in the model.
\<close>

subsection\<open>Proper Maps\<close>
  
text\<open>
  The definition of \emph{proper maps} as described in section~\ref{lambda-expressions} is
  formulated in terms of the meta-logic. Since denotation conditions in the semantics and
  later some of the axioms have to be restricted to proper maps, a method has to be devised
  by which the propriety of a map can easily be shown without using meta-logical concepts.

  Therefore introduction rules for @{term "IsProperInX"}, @{term "IsProperInXY"} and
  @{term "IsProperInXYZ"} are derived and a proving method @{method[names_short = true] "show_proper"}
  is defined that can be used to proof the propriety of a map using these introduction rules
  (see~\ref{TAO_Semantics_Proper}).

  The rules themselves rely on the power of the \emph{unifier} of Isabelle/HOL: Any map acting
  on individuals that can be expressed by another map that solely acts on exemplification expressions
  involving the individuals, is shown to be proper. This effectively means that all maps whose arguments
  only appear in exemplification expressions are proper. Using the provided introduction rules
  Isabelle's unifier can derive the propriety of such maps automatically.

  For a discussion about the relation between
  this concept and admissible \<open>\<lambda>\<close>-expressions in PLM see section~\ref{differences-lambda}.

\<close>

(*<*)
end (* context Semantics *)
(*>*)

section\<open>General All-Quantifier\<close>

text\<open>
  \label{general-quantifier}

  Since the last section established the semantic truth conditions of the specific versions of the
  all-quantifier for all variable types of PLM, it is now possible to define a binding symbol for general
  all-quantification.

  This is done using the concept of \emph{type classes} in Isabelle/HOL. Type classes define
  constants that depend on a \emph{type variable} and state assumptions about this constant.
  In subsequent reasoning the type of an object can be restricted to a type of the introduced
  type class. Thereby the reasoning can make use of all assumptions that have been stated about
  the constants of the type class. A priori it is not assumed that any type actually satisfies
  the requirements of the type class, so initially statements involving types restricted
  to a type class can not be applied to any specific type.

  To allow that the type class has to be \emph{instantiated} for the desired type. This is done
  by first providing definitions for the constants of the type class specific to the
  respective type. Then each assumption made by the type class has to be proven given the
  particular type and the provided definitions. After that any statement that was proven for
  the type class can be applied to the instantiated type.

  In the case of general all-quantification for the embedding this concept can be utilized by
  introducing the type class @{class quantifiable} that is equipped with a constant that is used
  as the general all-quantification binder (see~\ref{TAO_Quantifiable_Class}).
  For this constant it can now be assumed that it satisfies the semantic property of all
  quantification: \mbox{@{thm quantifiable_T8[of w \<psi>]}}.

  Since it was already shown in the last section that the specific all-quantifier for each
  variable type satisfies this property, the type class can immediately be instantiated for the
  types @{type \<nu>}, @{type \<Pi>\<^sub>0}, @{type \<Pi>\<^sub>1}, @{type \<Pi>\<^sub>2} and @{type \<Pi>\<^sub>3} (see~\ref{TAO_Quantifiable_Instantiations}).
  The instantiation proofs only need to refer to the statements derived in the semantics section for the respective version
  of the quantifier and are thereby independent of the representation layer.

  From this point onward the general all-quantifier can completely replace the type specific
  quantifiers. This is true even if a quantification is meant to only range over objects of a
  particular type: In this case the desired type (if it can not implicitly be deduced from the
  context) can be stated explicitly while still using the general quantifier.

  \begin{remark}
    Technically it would be possible to instantiate the type class @{class quantifiable} for
    any other type that satisfies the semantic criterion, thereby compromising the restriction
    of the all-quantifier to the primitive types of PLM. However, this is not done in the
    embedding and therefore the introduction of a general quantifier using a type class is
    considered a reasonable compromise.
  \end{remark}

\<close>

section\<open>Derived Language Elements\<close>

text\<open>
  The language of the embedded logic constructed so far is limited to a minimal set of
  primitive elements. This section introduces further derived language elements that are
  defined directly in the embedded logic.

  Notably identity is not part of the primitive language, but introduced as a \emph{defined}
  concept.
\<close>

subsection\<open>Connectives\<close>

text\<open>
  The remaining classical connectives and the modal diamond operator are defined in the traditional manner
  (see~\ref{TAO_BasicDefinitions_DerivedConnectives}):
  \begin{itemize}
    \item @{thm[display] conj_def[expand2, THEN embedded_eq, of \<phi> \<psi>]}
    \item @{thm[display] disj_def[expand2, THEN embedded_eq, of \<phi> \<psi>]}
    \item @{thm[display] equiv_def[expand2, THEN embedded_eq, of \<phi> \<psi>]}
    \item @{thm[display] diamond_def[expand1, THEN embedded_eq, of \<phi>]}
  \end{itemize}

  Furthermore, the general all-quantifier is supplemented by an existential quantifier as follows:
  \begin{itemize}
    \item @{thm[display] exists_def[expand1, of \<phi>, THEN embedded_eq, rename_abs \<alpha>]}
  \end{itemize}
\<close>

subsection\<open>Identity\<close>
  
text\<open>
  The definitions for identity are stated separately for each type of term
  (see~\ref{TAO_BasicDefinitions_Identity}):

  \begin{itemize}
    \item @{thm[display] basic_identity\<^sub>E_infix_def[unfolded basic_identity\<^sub>E_def, THEN embedded_def, of x y]}
    \item @{thm[display] basic_identity\<^sub>1_def[expand2, of F G, rename_abs x, THEN embedded_eq]}
    \item @{thm[display] basic_identity\<^sub>2_def[expand2, of F G, rename_abs x, THEN embedded_eq]}
    \item @{thm basic_identity\<^sub>3_def[expand2, of F G, rename_abs x y, THEN embedded_eq]}
    \item @{thm basic_identity\<^sub>0_def[expand2, of p q, rename_abs x x, THEN embedded_eq]}
  \end{itemize}

  Similarly to the general all-quantifier it makes sense to introduce a general identity
  relation for all types of terms (@{type \<kappa>}, @{type \<o>} resp. @{typ \<Pi>\<^sub>0}, @{typ \<Pi>\<^sub>1}, @{typ \<Pi>\<^sub>2}, @{typ \<Pi>\<^sub>3}).
  However, whereas all-quantification is characterized by a semantic criterion that can
  be generalized in a type class, identity is defined independently for each type. Therefore a general
  identity symbol will only be introduced in section~\ref{general-identity},
  since it will then be possible to formulate and prove a reasonable property shared
  by the identity of all types of terms.
\<close>

(*<*)
context MetaSolver
begin
(*>*)

section\<open>The Proving Method meta\_solver\<close>
 
text\<open>\label{meta_solver}\<close>
  
subsection\<open>General Concept\<close>
  
text\<open>

  Since the semantics in section~\ref{semantics} constructed a first abstraction on top of the
  representation layer, it makes sense to revisit the general concept of the layered structure
  of the embedding.

  The idea behind this structure is that reasoning in subsequent layers should - as far as possible - only
  rely on the previous layer. However, the restriction of proofs to a specific subset of the facts
  that are valid in the global context can be cumbersome for automated reasoning. While it is possible
  to restrict automated reasoning tools to only consider specific sets of facts, it is still an
  interesting question whether the process of automated reasoning in the layered approach can be made easier.

  To that end the embedding utilizes the Isabelle package \emph{Eisbach}. This package allows to conveniently
  define new proving methods that are based on the systematic application of existing methods.
  
  \begin{remark}
    The Eisbach package even allows the construction of more complex proving methods that involve
    pattern matching. This functionality is utilized in the construction of a substitution method as
    described in section~\ref{substitution-method}.
  \end{remark}

  The idea is to construct a simple resolution prover that can deconstruct complex
  formulas of the embedded logic to simpler formulas that are connected by a relation in the meta-logic
  as required by the semantics.

  For example an implication formula can be deconstructed as follows:
  \begin{center}
    @{thm ImplS[of v \<phi> \<psi>]}
  \end{center}

  Whereas the basic proving methods available in Isabelle cannot immediately prove
  \mbox{@{lemma "[\<phi> \<^bold>\<rightarrow> \<phi> in v]" by (simp add: ImplS)}} without any facts about the definitions of
  validity and implication, they \emph{can} prove \mbox{@{lemma "[\<phi> in v] \<longrightarrow> [\<phi> in v]" by simp}}
  directly as an instance of \mbox{@{lemma "p \<longrightarrow> p" by simp}}.
\<close>
  
subsection\<open>Implementation\<close>

text\<open>
  Following this idea the method @{method meta_solver} is introduced (see~\ref{TAO_MetaSolver})
  that repeatedly applies rules like the above in order to translate complex formulas of the embedded logic
  to meta-logical statements involving simpler formulas.

  The formulation of appropriate introduction, elimination and substitution rules for the logical
  connectives and quantifiers is straightforward. Beyond that the concept can be used to
  resolve exemplification and encoding formulas to their semantic truth conditions as well,
  e.g. (see~\ref{TAO_MetaSolver_Encoding}):
  \begin{center}
    @{thm Exe1S[of v F x]}
  \end{center}

  This way a large set of formulas can be decomposed to semantic expressions that can be automatically
  proven without having to rely on the meta-logical definitions directly.

  Additionally the @{method meta_solver} is equipped with rules for
  being abstract and ordinary and for the defined identity.

  Notably the representation layer has the property that the defined identities are equivalent to
  the identity in the meta-logic. Formally the following statements are true and derived as rules
  for the @{method meta_solver}:

  \begin{itemize}
    \item @{thm[display] Eq\<^sub>ES[of v "embedded_style x" "embedded_style y"]}
    \item @{thm[display] Eq\<kappa>S[of v "embedded_style x" "embedded_style y"]}
    \item @{thm[display] Eq\<^sub>1S[of v "embedded_style F" "embedded_style G"]}
    \item @{thm[display] Eq\<^sub>2S[of v "embedded_style F" "embedded_style G"]}
    \item @{thm[display] Eq\<^sub>3S[of v "embedded_style F" "embedded_style G"]}
    \item @{thm[display] Eq\<^sub>0S[of v "embedded_style F" "embedded_style G"]}
  \end{itemize}

  The proofs for these facts (see~\ref{TAO_MetaSolver_Identity}) are complex and do not
  solely rely on the properties of the formal semantics of PLM.

  The fact that they are derivable has a distinct advantage: since identical terms
  in the sense of PLM are identical in the meta-logic, proving the axiom of
  substitution (see~\ref{axioms-identity}) is trivial.
  A derivation that is solely based on the semantics on the other hand, would require a complex
  induction proof. For this reason it is considered a reasonable compromise to include these statements
  as admissible rules for the @{method meta_solver}. However, future work may attempt to enforce
  the separation of layers more strictly and consequently abstain from these rules.

  \begin{remark}
    Instead of introducing a custom proving method using the Eisbach package, a similar
    effect could be achieved by instead supplying the derived introduction, elimination and substitution
    rules directly to one of the existing proving methods like @{method auto} or @{method clarsimp}.
    In practice, however, we found that the custom @{method meta_solver} produces more reliable
    results, especially in the case that a proving objective cannot be solved completely by the supplied rules.
    Moreover the constructed custom proving method serves as a proof of concept
    and may inspire the development of further more complex proving methods that go beyond a simple
    resolution prover in the future.
  \end{remark}
\<close>

subsection\<open>Applicability\<close>

(*<*)
context
begin
  interpretation PLM .
(*>*)
  
text\<open>
  Given the discussion above and keeping the layered structure of the embedding in mind, it is
  important to precisely determine for which purposes it is valid to use the constructed
  @{method meta_solver}.

  The main application of the method in the embedding is to support the derivation of the axiom
  system as described in section~\ref{axioms}. Furthermore the @{method meta_solver} can aid in examining the
  meta-logical properties of the embedding. The @{method meta_solver} is only supplied with rules that
  are \emph{reversible}. Thereby it is justified to use it to simplify a statement
  before employing a tool like @{theory_text "nitpick"} in order to look for models or
  counter-models for a statement.

  However it is \emph{not} justified to assume that a theorem that can be proven with the aid of the
  @{method meta_solver} method is derivable in the formal system of PLM, since
  the result still depends on the specific structure of the representation layer. However,
  based on the concept of the @{method meta_solver} another proving method is
  introduced in section~\ref{PLM-solver}, namely the @{method PLM_solver}. This proving method
  only employs rules that are derivable from the formal system of PLM itself. Thereby this method
  \emph{can} be used in proofs without sacrificing the universality of the result.
\<close>

(*<*)
end (* anonymous context interpreting the PLM locale *)
end (* context MetaSolver *)
(*>*)

section\<open>General Identity Relation\<close>

text\<open>
  \label{general-identity}

  As already mentioned in section~\ref{general-quantifier} similarly to the general quantification
  binder it is desirable to introduce a general identity relation.

  Since the identity of PLM is not directly characterized by semantic truth conditions, but instead
  \emph{defined} using specific complex formulas in the embedded logic for each type of term,
  some other property has to be found that is shared by the respective definitions and can reasonably
  be used as the condition of a type class.

  A natural choice for such a condition is the axiom of the substitution of identicals
  (see~\ref{axioms-identity}). The axiom states that if two objects are identical (in the sense of the defined
  identity of PLM), then a formula involving the first object implies the formula resulting from
  substituting the second object for the first object. This inspires the following condition for
  the type class @{class identifiable} (see~\ref{TAO_Identifiable_Class}):

  \begin{center}
    @{thm identifiable_class.l_identity[of v \<alpha> \<beta> \<phi>]}
  \end{center}

  Using the fact that in the last section it was already derived, that the defined identity
  in the embedded-logic for each term implies the primitive identity of the meta-logical objects,
  this type class can be instantiated for all types of terms: @{type \<kappa>}, @{typ \<Pi>\<^sub>0} resp. @{type \<o>},
  @{type \<Pi>\<^sub>1}, @{type \<Pi>\<^sub>2}, @{type \<Pi>\<^sub>3} (see~\ref{TAO_Identifiable_Instantiation}).

  Since now general quantification and general identity are available, an additional quantifier
  for unique existence can be introduced (such a quantifier involves both quantification and identity).
  To that end a derived type class is introduced that is the combination of the @{class quantifiable}
  and the @{class identifiable} classes. Although this is straightforward for the relation types,
  this reveals a subtlety involving the distinction between individuals of type @{type \<nu>} and
  individual terms of type @{type \<kappa>}: The type @{type \<nu>} belongs to the class @{class quantifiable},
  the type @{type \<kappa>} on the other hand does not: no quantification over individual \emph{terms}
  (that may not denote) was defined. On the other hand the class @{class identifiable} was only
  instantiated for the type @{type \<kappa>}, but not for the type @{type \<nu>}.
  This issue can be solved by noticing that it is straightforward and
  justified to define an identity for @{type \<nu>} as follows:

  \begin{center}
    @{thm identity_\<nu>_def[expand2, of x y, THEN embedded_eq]}
  \end{center}

  This way type @{type \<nu>} is equipped with both the general all-quantifier and the general identity
  relation and unique existence can be defined for all variable types as expected:

  \begin{center}
    @{thm exists_unique_def[expand1, of \<phi>, THEN embedded_eq]}
  \end{center}

  Another subtlety has to be considered: at times it is necessary to expand the definitions
  of identity for a specific type to derive statements in PLM. Since the defined identities were
  introduced prior to the general identity symbol, such an expansion is therefore so far not possible
  for a statement that uses the general identity, even if the types are fixed in the context.

  To allow such an expansion the definitions of identity are equivalently restated for the general
  identity symbol and each specific type (see~\ref{TAO_Identifiable_Definitions}). This way
  the general identity can from this point onward completely replace the type-specific identity
  symbols.

\pagebreak

\<close>
  
(*<*)
context Axioms
begin
(*>*)

section\<open>The Axiom System of PLM\<close>

text\<open>
  \label{axioms}

  The last step in abstracting away from the representation layer is the derivation of the
  axiom system of PLM. Conceptionally the
  derivation of the axioms is the last moment in which it is deemed admissible to rely
  on the meta-logical properties of the underlying model structure. Future work may even
  restrict this further to only allow the use of the properties of the semantics in the
  proofs (if this is found to be possible).

  To be able to distinguish between the axioms and other statements and theorems in the
  embedded logic they are stated using a dedicated syntax (see~\ref{TAO_Axioms}):
  \begin{center}
    @{thm axiom_def[expand1, of \<phi>]}
  \end{center}

  Axioms are unconditionally true in all possible worlds. The only exceptions are
  \emph{necessitation-averse}, resp. \emph{modally-fragile} axioms\footnote{Currently PLM uses
  only one such axiom, see~\ref{axioms-actuality}.}. Such axioms are stated using the following syntax:
  \begin{center}
    @{thm actual_validity_def[expand1, of \<phi>]}
  \end{center}

\<close>
  
subsection\<open>Axioms as Schemata\<close>
  
text\<open>
  \label{axiom-schemata}

  Most of the axioms in PLM are stated as \emph{axiom schemata}. They use variables that range over
  and can therefore be instantiated for any formula and term.
  Furthermore PLM introduces the notion of \emph{closures} (see~@{cite \<open>(\ref{PM-closures})\<close> PM}). Effectively this means
  that the statement of an axiom schema implies that the universal generalization of the schema,
  the actualization of the schema and (except for modally-fragile axioms) the necessitation of the
  schema is also an axiom.

  Since in Isabelle/HOL free variables in a theorem already range over all terms of the same type
  no special measures have to be taken to allow instantiations for arbitrary terms. The concept of
  closures is introduced using the following rules (see~\ref{TAO_Axioms_Closures}):

  \begin{itemize}
    \item @{thm[display] axiom_instance[of \<phi> v]}
    \item @{thm[display] closures_universal[of \<phi>]}
    \item @{thm[display] closures_actualization[of \<phi>]}
    \item @{thm[display] closures_necessitation[of \<phi>]}
  \end{itemize}

  For modally-fragile axioms only the following rules are introduced:

  \begin{itemize}
    \item @{thm[display] necessitation_averse_axiom_instance[of \<phi>]}
    \item @{thm[display] necessitation_averse_closures_universal[of \<phi>]}
  \end{itemize}

  \begin{remark}
    To simplify the instantiation of the axioms in subsequent proofs,
    a set of \emph{attributes} is defined that can be used to transform
    the statement of the axioms using the rules defined above.

    This way for example the axiom \mbox{@{thm qml_2}} can be directly transformed
    to \mbox{@{thm qml_2[axiom_universal, axiom_instance, of v \<phi>]}} by not referencing
    it directly as @{theory_text qml_2}, but by applying the defined attributes
    to it: @{theory_text "qml_2[axiom_universal, axiom_instance]"}
  \end{remark}
\<close>

subsection\<open>Derivation of the Axioms\<close>

text\<open>
  To simplify the derivation of the axioms a proving method @{method axiom_meta_solver} is introduced, that
  unfolds the dedicated syntax, then applies the meta-solver and if possible resolves
  the proof objective automatically.

  Most of the axioms can be derived by the @{method axiom_meta_solver} directly.
  Some axioms, however, require more verbose proofs or their representation in the functional
  setting of Isabelle/HOL requires special attention.
  Therefore in the following the complete axiom system is listed and discussed in
  detail where necessary. Additionally each axiom is associated with the numbering in
  the current draft of PLM@{cite PM}.
\<close>
  
subsection\<open>Axioms for Negations and Conditionals\<close>
  
text\<open>
  The axioms for negations and conditionals can be derived automatically and
  present no further issues (see~\ref{TAO_Axioms_NegationsAndConditionals}):

  \begin{itemize}
    \item @{thm pl_1} \hfill{(\ref{PM-pl}.1)}
    \item @{thm pl_2} \hfill{(\ref{PM-pl}.2)}
    \item @{thm pl_3} \hfill{(\ref{PM-pl}.3)}
  \end{itemize}

\<close>

subsection\<open>Axioms of Identity\<close>

text\<open>
  \label{axioms-identity}

  The axiom of the substitution of identicals can be proven automatically,
  if additionally supplied with the defining assumption of the type class
  @{class identifiable}. The statement is the following (see~\ref{TAO_Axioms_Identity}):

  \begin{itemize}
    \item @{thm l_identity} \hfill{(\ref{PM-l-identity})}
  \end{itemize}
\<close>

subsection\<open>Axioms of Quantification\<close>

text\<open>
  \label{quantification-axioms}

  The axioms of quantification are formulated in a way that differs from the statements in
  PLM, as follows (see~\ref{TAO_Axioms_Quantification}):

  \begin{itemize}
    \item @{thm cqt_1[of \<phi> \<tau>]} \hfill{(\ref{PM-cqt}.1a)}
    \item @{thm cqt_1_\<kappa>[of \<phi> \<tau>]} \hfill{(\ref{PM-cqt}.1b)}
    \item @{thm cqt_3} \hfill{(\ref{PM-cqt}.3)}
    \item @{thm cqt_4} \hfill{(\ref{PM-cqt}.4)}
    \item @{thm cqt_5[of \<psi> \<phi>, rename_abs x \<nu> x]} \hfill{(\ref{PM-cqt}.5a)}
    \item @{thm cqt_5_mod[of \<psi> \<tau>, rename_abs \<nu>]} \hfill{(\ref{PM-cqt}.5b)}
  \end{itemize}

  The original axioms in PLM\footnote{Note that the axioms
  will in all likelihood be adjusted in future versions of PLM in order to prevent the paradox
  described in section~\ref{paradox}.} are the following:

  \begin{itemize}
    \item \<open>\<forall>\<alpha>\<phi> \<rightarrow> (\<exists>\<beta>(\<beta> = \<tau>) \<rightarrow> \<phi>\<^sup>\<tau>\<^sub>\<alpha>)\<close> \hfill{(\ref{PM-cqt}.1)}
    \item \<open>\<exists>\<beta>(\<beta> = \<tau>)\<close>, provided \<open>\<tau>\<close> is not a description and \<open>\<beta>\<close> doesn't occur free in \<open>\<tau>\<close>.\hfill{(\ref{PM-cqt}.2)}
    \item \<open>\<forall>\<alpha>(\<phi> \<rightarrow> \<psi>) \<rightarrow> (\<forall>\<alpha> \<phi> \<rightarrow> \<forall>\<alpha> \<psi>)\<close> \hfill{(\ref{PM-cqt}.3)}
    \item \<open>\<phi> \<rightarrow> (\<forall>\<alpha> \<phi>)\<close>, provided \<open>\<alpha>\<close> doesn't occur free in \<open>\<phi>\<close> \hfill{(\ref{PM-cqt}.4)}
    \item \<open>\<psi>\<^sup>\<iota>\<^sup>x\<^sup>\<phi>\<^sub>\<mu> \<rightarrow> \<exists>\<nu> (\<nu> = \<iota>x\<phi>)\<close>, provided (a) \<open>\<psi>\<close> is either an exemplification formula \<open>\<Pi>\<^sup>n\<kappa>\<^sub>1\<dots>\<kappa>\<^sub>n\<close> (\<open>n \<ge> 1\<close>)
          or an encoding formula \<open>\<kappa>\<^sub>1\<Pi>\<^sup>1\<close>, (b) \<open>\<mu>\<close> is an individual variable that occurs in \<open>\<psi>\<close>
          and only as one or more of the \<open>\<kappa>\<^sub>i\<close> (\<open>1 \<le> i \<le> n\<close>), and (c) \<open>\<nu>\<close> is any individual variable
          that doesn't occur free in \<open>\<phi>\<close>.\hfill{(\ref{PM-cqt}.5)}
  \end{itemize}

  In the embedding definite descriptions have the type @{type \<kappa>} that is different from the
  type for individuals @{type \<nu>}. Quantification is only defined for @{type \<nu>}, not for @{type \<kappa>}.

  Therefore, the restriction of (\ref{PM-cqt}.2) does not apply, since the type restriction of
  quantification ensures that @{term "\<tau>"} cannot be a definite description.
  Consequently the inner precondition of (\ref{PM-cqt}.1)
  can be dropped in (\ref{PM-cqt}.1a) - since a quantifier is used in the
  formulation, the problematic case of definite descriptions is excluded and the dropped
  precondition would always hold.

  The second formulation (\ref{PM-cqt}.1b) for definite descriptions involves the type
  conversion @{term "embedded_style (DUMMY\<^sup>P)"} and keeps the inner precondition (since descriptions
  may not denote).

  (\ref{PM-cqt}.5b) can be stated as a generalization of (\ref{PM-cqt}.5a) to general individual
  terms, since (\ref{PM-cqt}.2) already implies its right hand side for every term except descriptions.

  Consequently (\ref{PM-cqt}.1b) and (\ref{PM-cqt}.5b) can replace the original axioms
  (\ref{PM-cqt}.1) and (\ref{PM-cqt}.5) for individual terms.
  For individual variables and constants as well as relations the simplified formulation
  (\ref{PM-cqt}.1a) can be used instead.

  Future work may want to reconsider the reformulation of the axioms, especially considering the most
  recent developments described in section~\ref{paradox}. At the time of writing the reformulation is
  considered a reasonable compromise, since due to the type restrictions of the embedding the reformulated
  version of the axioms is an equivalent representation of the original axioms.

  The predicate @{term "SimpleExOrEnc"} used as the precondition for (\ref{PM-cqt}.5)
  is defined as an inductive predicate with the following introduction rules:

  \begin{itemize}
    \item @{lemma[eta_contract=false] "SimpleExOrEnc (\<lambda>x. embedded_style \<lparr>F,x\<rparr>)"
            by (simp add: SimpleExOrEnc.intros embedded_style_def)}
    \item @{lemma[eta_contract=false] "SimpleExOrEnc (\<lambda>x. embedded_style \<lparr>F,x,DUMMY\<rparr>)"
            by (simp add: SimpleExOrEnc.intros embedded_style_def)}
    \item @{lemma[eta_contract=false] "SimpleExOrEnc (\<lambda>x. embedded_style \<lparr>F,DUMMY,x\<rparr>)"
            by (simp add: SimpleExOrEnc.intros embedded_style_def)}
    \item @{lemma[eta_contract=false] "SimpleExOrEnc (\<lambda>x. embedded_style \<lparr>F,x,DUMMY,DUMMY\<rparr>)"
            by (simp add: SimpleExOrEnc.intros embedded_style_def)}
    \item @{lemma[eta_contract=false] "SimpleExOrEnc (\<lambda>x. embedded_style \<lparr>F,DUMMY,x,DUMMY\<rparr>)"
            by (simp add: SimpleExOrEnc.intros embedded_style_def)}
    \item @{lemma[eta_contract=false] "SimpleExOrEnc (\<lambda>x. embedded_style \<lparr>F,DUMMY,DUMMY,x\<rparr>)"
            by (simp add: SimpleExOrEnc.intros embedded_style_def)}
    \item @{lemma[eta_contract=false] "SimpleExOrEnc (\<lambda>x. embedded_style \<lbrace>x,F\<rbrace>)"
            by (simp add: SimpleExOrEnc.intros embedded_style_def)}              
  \end{itemize}

  This corresponds exactly to the restriction of @{term "embedded_style \<psi>"} to an exemplification
  or encoding formula in PLM.

\<close>

subsection\<open>Axioms of Actuality\<close>
  
text\<open>
  \label{axioms-actuality}

  As mentioned in the beginning of the section the modally-fragile axiom of actuality
  is stated using a different syntax (see~\ref{TAO_Axioms_Actuality}):

  \begin{itemize}
    \item @{thm logic_actual} \hfill{(\ref{PM-logic-actual})}
  \end{itemize}

  Note that the model finding tool @{theory_text nitpick} can find a counter-model for the
  formulation as a regular axiom, as expected.

  The remaining axioms of actuality are not modally-fragile and therefore stated as regular
  axioms:
  
  \begin{itemize}
    \item @{thm logic_actual_nec_1} \hfill{(\ref{PM-logic-actual-nec}.1)}
    \item @{thm logic_actual_nec_2} \hfill{(\ref{PM-logic-actual-nec}.2)}
    \item @{thm logic_actual_nec_3} \hfill{(\ref{PM-logic-actual-nec}.3)}
    \item @{thm logic_actual_nec_4} \hfill{(\ref{PM-logic-actual-nec}.4)}
  \end{itemize}

  All of the above can be proven automatically by the @{method axiom_meta_solver} method.
\<close>

subsection\<open>Axioms of Necessity\<close>

text\<open>
  \label{axioms-necessity}

  The axioms of necessity are the following (see~\ref{TAO_Axioms_Necessity}):

  \begin{itemize}
    \item @{thm qml_1} \hfill{(\ref{PM-qml}.1)}
    \item @{thm qml_2} \hfill{(\ref{PM-qml}.2)}
    \item @{thm qml_3} \hfill{(\ref{PM-qml}.3)}
    \item @{thm qml_4} \hfill{(\ref{PM-qml}.4)}
  \end{itemize}

  While the first three axioms can be derived automatically, the last axiom requires
  special attention. On a closer look the formulation may be familiar. The axiom
  was already mentioned in section~\ref{concreteness} while constructing the representation
  of the constant @{term "embedded_style E!"}. To be able to derive this axiom here the
  constant was specifically axiomatized. Consequently the derivation requires
  the use of these meta-logical axioms stated in the representation layer.

\<close>

subsection\<open>Axioms of Necessity and Actuality\<close>
  
text\<open>
  The axioms of necessity and actuality can be derived automatically
  and require no further attention (see~\ref{TAO_Axioms_NecessityAndActuality}):

  \begin{itemize}
    \item @{thm qml_act_1} \hfill{(\ref{PM-qml-act}.1)}
    \item @{thm qml_act_2} \hfill{(\ref{PM-qml-act}.2)}
  \end{itemize}
\<close>

subsection\<open>Axioms of Descriptions\<close>

text\<open>
  There is only one axiom dedicated to descriptions (note, however, that descriptions play
  a role in the axioms of quantification). The statement is the following (see~\ref{TAO_Axioms_Descriptions}):

  \begin{itemize}
    \item @{thm descriptions} \hfill{(\ref{PM-descriptions})}
  \end{itemize}

  Given the technicalities of descriptions already discussed in section~\ref{quantification-axioms}
  it comes at no surprise that this statement requires a verbose proof.

\<close>

subsection\<open>Axioms of Complex Relation Terms\<close>
(*<*)
context
begin
  interpretation MetaSolver .
(*>*)
text\<open>
  The axioms of complex relation terms deal with the properties of \<open>\<lambda>\<close>-expressions.
  
  Since the @{method meta_solver} was not equipped with explicit rules for \<open>\<lambda>\<close>-expressions,
  the statements rely on their semantic properties as described in section~\ref{semantics} directly.

\<close>
(*<*)
end (* unnamed subcontext with MetaSolver interpretation *)
(*>*)
text\<open>

  The statements are the following (see~\ref{TAO_Axioms_ComplexRelationTerms}):
  \begin{itemize}
    \item @{thm lambda_predicates_1[THEN embedded_eq, of \<phi>]} \hfill{(\ref{PM-lambda-predicates}.1)}
    \item @{thm lambda_predicates_2_1} \hfill{(\ref{PM-lambda-predicates}.2)}
    \item @{thm lambda_predicates_2_2} \hfill{(\ref{PM-lambda-predicates}.2)}
    \item @{thm[break=true] lambda_predicates_2_3} \hfill{(\ref{PM-lambda-predicates}.2)}
    \item @{thm lambda_predicates_3_0} \hfill{(\ref{PM-lambda-predicates}.3)}
    \item @{thm lambda_predicates_3_1} \hfill{(\ref{PM-lambda-predicates}.3)}
    \item @{thm lambda_predicates_3_2} \hfill{(\ref{PM-lambda-predicates}.3)}
    \item @{thm lambda_predicates_3_3} \hfill{(\ref{PM-lambda-predicates}.3)}
    \item @{thm lambda_predicates_4_0} \hfill{(\ref{PM-lambda-predicates}.4)}
    \item @{thm lambda_predicates_4_1} \hfill{(\ref{PM-lambda-predicates}.4)}
    \item @{thm lambda_predicates_4_2} \hfill{(\ref{PM-lambda-predicates}.4)}
    \item @{thm lambda_predicates_4_3} \hfill{(\ref{PM-lambda-predicates}.4)}
  \end{itemize}

  The first axiom, \<open>\<alpha>\<close>-conversion, could be omitted entirely. Since
  lambda-expressions are modeled using functions with bound variables and \<open>\<alpha>\<close>-conversion
  is part of the logic of Isabelle/HOL, it already holds implicitly.

  As explained in section~\ref{lambda-expressions} \<open>\<beta>\<close>-conversion has to be restricted
  to \emph{proper maps}. In PLM this restriction is implicit due to the fact that
  \<open>\<lambda>\<close>-expressions are only well-formed if their matrix is a propositional formula.

  The formulation of the last class of axioms
  ((\ref{PM-lambda-predicates}.4), @{term "\<iota>"}-conversion)
  has to be adjusted to be representable in the functional setting. The original axiom is stated as follows in PLM:
  \begin{center}
    \<open>\<A>(\<phi> \<equiv> \<psi>) \<rightarrow> ([\<lambda>x\<^sub>1\<cdots>x\<^sub>n \<chi>\<^sup>*] = [\<lambda>x\<^sub>1\<cdots>x\<^sub>n \<chi>\<^sup>*']\<close>
  \end{center}
  \<open>\<chi>\<^sup>*'\<close> is required to be the result of substituting  \<open>\<iota>x\<psi>\<close> for zero or more occurrences of \<open>\<iota>x\<phi>\<close>
  in \<open>\<chi>\<^sup>*\<close>. In the functional setting @{term "embedded_style \<chi>"} can be represented
  as function from individual terms of type @{type \<kappa>} to propositions of type @{type \<o>}.
  Thereby substituting \<open>\<iota>x\<psi>\<close> for occurrences of \<open>\<iota>x\<phi>\<close> can be expressed by
  comparing the function application of @{term "embedded_style \<chi>"} to @{term "embedded_style (\<^bold>\<iota>x. \<phi> x)"}
  with the function application of @{term "embedded_style \<chi>"} to @{term "embedded_style (\<^bold>\<iota>x. \<psi> x)"}.

  Since in this representation @{term "embedded_style \<phi>"} and @{term "embedded_style \<psi>"} are functions as well
  (from type @{type \<nu>} to type @{type \<o>}) the precondition has to be reformulated
  to hold for the application of @{term "embedded_style \<phi>"} and @{term "embedded_style \<psi>"} to
  an arbitrary individual @{term "embedded_style x"} to capture the concept of \<open>\<A>(\<phi> \<equiv> \<psi>)\<close> in PLM, where \<open>\<phi>\<close>
  and \<open>\<psi>\<close> may contain \<open>x\<close> as a free variable.
\<close>

subsection\<open>Axioms of Encoding\<close>
  
text\<open>
  The last class of axioms deals with encoding (see~\ref{TAO_Axioms_Encoding}):

  \begin{itemize}
    \item @{thm encoding} \hfill{(\ref{PM-encoding})}
    \item @{thm nocoder} \hfill{(\ref{PM-nocoder})}
    \item @{thm A_objects} \hfill{(\ref{PM-A-objects})}
  \end{itemize}

  Whereas the first statement, \emph{encoding is modally rigid}, is a direct consequence of the semantics
  (recall that the encoding extension of a property was not relativized to possible worlds; see
   section~\ref{semantics}), the second axiom, \emph{ordinary objects do not encode}, is only derivable
  by expanding the definition of the encoding extension and the meta-logical distinction
  between ordinary and abstract objects.

  Similarly the comprehension axiom for abstract objects
  depends on the model structure and follows from the representation of abstract objects as sets
  of one-place relations and the definition of encoding as set membership.

  Furthermore in the functional setting @{term "embedded_style \<phi>"} has to be represented as a function
  and the condition it imposes on @{term "embedded_style F"} is expressed as its application to @{term "embedded_style F"}.
  The formulation in PLM on the other hand has to explicitly exclude a free occurrence of \<open>x\<close>
  in \<open>\<phi>\<close>. In the functional setting this is not necessary. Since @{term "embedded_style x"}
  is bound by the existential quantifier and not explicitly given to @{term "embedded_style \<phi>"} 
  as an argument, the condition @{term "embedded_style \<phi>"} imposes on @{term "embedded_style F"}
  cannot depend on @{term "embedded_style x"} by construction.

\<close>

subsection\<open>Summary\<close>
  
text\<open>
  Although some of the axioms have to be adjusted to be representable in the functional environment,
  the resulting formulation faithfully represents the original axiom system of PLM.

  Furthermore a large part of the axioms can be derived independently of the technicalities of
  the representation layer with proofs that only depend on the representation of the semantics described in
  section~\ref{semantics}. Future work may explore available options to further minimize the dependency
  on the underlying model structure.

  To verify that the axiom system faithfully represents the reference system, the
  deductive system PLM as described in @{cite \<open>Chap. 9\<close> PM} is derived solely based on the
  formulation of the axioms without falling back to the model structure or the semantics (see~\ref{TAO_PLM}).

\pagebreak
\<close>

(*<*)
end (* context Axioms *)
(*>*)


(*<*)
context PLM
begin
(*>*)
  
section\<open>The Deductive System PLM\<close>
  
text\<open>
  The derivation of the deductive system PLM (@{cite \<open>Chap. 9\<close> PM}) from the axiom system constitutes
  a major part of the Isabelle theory in the appendix (see~\ref{TAO_PLM}). Its extent of
  over one hundred pages makes it infeasible to discuss every aspect in full detail.

  Nevertheless it is worthwhile to have a look at the mechanics of the derivation and to
  highlight some interesting concepts.
\<close>

subsection\<open>Modally Strict Proofs\<close>
  
text\<open>
  \label{PLM-modally-strict}

  PLM distinguishes between two sets of theorems: the theorems, that are derivable from
  the complete axiom system including the modally-fragile axiom,
  and the set of theorems, that have \emph{modally-strict} proofs (see~@{cite \<open>(\ref{PM-theoremhood})\<close> PM}).

  A proof is modally-strict, if it does not depend on any modally-fragile axioms.

  In the embedding modally-strict theorems are stated to be true for an arbitrary semantic
  possible world: \mbox{@{term "[\<phi> in v]"}}

  Here the variable @{term "v"} implicitly ranges over all semantic possible worlds of
  type @{type i}, including the designated actual world @{term "dw"}. Since modally-fragile axioms
  only hold in @{term "dw"}, they therefore cannot be used to prove a statement formulated
  this way, as desired.

  Modally-fragile theorems on the other hand are stated to be true only for the designated
  actual world: \mbox{@{term "[\<phi> in dw]"}}

  This way necessary axioms, as well as modally-fragile axioms can be used in their proofs. However
  it is not possible to infer from a modally-fragile theorem that the same statement holds as a
  modally-strict theorem.

  This representation of modally-strict and modally-fragile theorems is discussed in more detail
  in section~\ref{differences-modally-strict}.
\<close>

subsection\<open>Fundamental Metarules of PLM\<close>

text\<open>
  \label{PLM-metarules}

  The primitive rule of PLM is the modus ponens rule (see~\ref{TAO_PLM_ModusPonens}):
  
  \begin{itemize}
    \item @{thm modus_ponens[of v \<phi> \<psi>]} \hfill{(\ref{PM-modus-ponens})}
  \end{itemize}

  This rule is a direct consequence of the semantics of the implication.

  Additionally two fundamental Metarules are derived in PLM, \emph{GEN} and \emph{RN} (see~\ref{TAO_PLM_GEN_RN}):

  \begin{itemize}
    \item @{thm rule_gen[of v \<phi>]} \hfill{(\ref{PM-rule-gen})}
    \item @{thm RN_2[rename_abs w, of \<phi> \<psi> v]} \hfill{(\ref{PM-RN})}
  \end{itemize}

  Although in PLM these rules can be derived by structural induction on the length of
  a derivation, this proving mechanism cannot be reproduced in Isabelle. However,
  the rules are direct consequences of the semantics described in section~\ref{semantics}.
  The same is true for the deduction rule (see~\ref{TAO_PLM_NegationsAndConditionals}):

  \begin{itemize}
    \item @{thm deduction_theorem[of v \<phi> \<psi>]} \hfill{(\ref{PM-deduction-theorem})}
  \end{itemize}

  Consequently this rule is derived from the semantics as well.
  
  These rules are the \emph{only} exceptions to the concept that the deductive system of
  PLM is derived solely from the axiom system without relying on the previous layers of the
  embedding.

\<close>

subsection\<open>PLM Solver\<close>
  
(*<*)
context
begin
interpretation MetaSolver .
(*>*)
text\<open>
  \label{PLM-solver}

  Similarly to the @{method meta_solver} described in section~\ref{meta_solver} another proving
  method is introduced, namely the @{method PLM_solver} (see~\ref{TAO_PLM_Solver}).

  This proving method is initially not equipped with any rules. Throughout the derivation of the
  deductive system, whenever an appropriate rule is derived as part of PLM directly or becomes
  trivially derivable from the proven theorems, it is added to the @{method PLM_solver}.

  Additionally the @{method PLM_solver} can instantiate any theorem of the deductive system PLM 
  as well as any axiom, if doing so resolves the current proving goal.

  By its construction the @{method PLM_solver} has the property, that it can \emph{only} prove
  statements that are derivable from the deductive system PLM. Thereby it is safe to use to aid
  in any proof throughout the section. In practice it can automatically prove a variety of simple
  statements and aid in more complex proofs throughout the derivation of the deductive system.

\<close>
(*<*)
end (* unnamed subcontext with MetaSolver interpretation *)
(*>*)

subsection\<open>Additional Type Classes\<close>
  
text\<open>
  \label{PLM-type-classes}

  In PLM it is possible to derive statements involving the general identity symbol by case
  distinction: if such a statement is derivable for all types of terms in the language separately,
  it can be concluded that it is derivable for the identity symbol in general. Such a case distinction
  cannot be directly reproduced in the embedding, since it cannot be assumed that every instantiation of the
  type class @{class identifiable} is in fact one of the types of terms of PLM.

  However, there is a simple way to still formulate such general statements. This is done by
  the introduction of additional type classes. A simple example is the type class @{class id_eq}
  (see~\ref{TAO_PLM_Identity}). This new type class assumes the following statements to be true:

  \begin{itemize}
    \item @{thm id_eq_1[of v \<alpha>]} \hfill{(\ref{PM-id-eq}.1)}
    \item @{thm id_eq_2[of v \<alpha> \<beta>]} \hfill{(\ref{PM-id-eq}.2)}
    \item @{thm id_eq_3[of v \<alpha> \<beta> \<gamma>]} \hfill{(\ref{PM-id-eq}.3)}
  \end{itemize}

  Since these statements can be derived \emph{separately} for the types @{type \<nu>}, @{type \<Pi>\<^sub>0},
  @{type \<Pi>\<^sub>1}, @{type \<Pi>\<^sub>2} and @{type \<Pi>\<^sub>3}, the type class @{class id_eq} can be instantiated
  for each of these types.
\<close>

subsection\<open>The Rule of Substitution\<close>

text\<open>
  A challenge in the derivation of the deductive system that is worth to examine in
  detail is the \emph{rule of substitution}.  The rule is stated in PLM as follows
  (see~(\ref{PM-rule-sub-nec})@{cite PM}):

  \begin{addmargin}{1cm}
    If \<open>\<turnstile>\<^sub>\<box> \<psi> \<equiv> \<chi>\<close> and \<open>\<phi>'\<close> is the result of substituting the formula \<open>\<chi>\<close>
    for zero or more occurrences of \<open>\<psi>\<close> where the latter is a subformula of \<open>\<phi>\<close>,
    then if \<open>\<Gamma> \<turnstile> \<phi>\<close>, then \<open>\<Gamma> \<turnstile> \<phi>'\<close>. [Variant: If \<open>\<turnstile>\<^sub>\<box> \<psi> \<equiv> \<chi>\<close>, then \<open>\<phi> \<turnstile> \<phi>'\<close>]
  \end{addmargin}

  A naive representation of the rule would be the following:

  \begin{center}
    @{term "(\<And>v. [\<psi> \<^bold>\<equiv> \<chi> in v]) \<Longrightarrow> [\<phi> \<psi> in v] \<longleftrightarrow> [\<phi> \<chi> in v]"}
  \end{center}

  However this statement is \emph{not} derivable. The issue is connected to the restriction
  of @{term "\<psi>"} to be a \emph{subformula} of \<open>\<phi>\<close> in PLM. The formulation above would allow
  the rule to be instantiated for \emph{any function} @{term "embedded_style \<phi>"} from formulas to formulas.

  Formulas in the embedding have type @{type \<o>} which is internally represented by functions of the
  type @{typ "j\<Rightarrow>i\<Rightarrow>bool"}. Therefore the formulation above could be instantiated with a function
  @{term "embedded_style \<phi>"} that has the following internal representation:
  \mbox{@{term "\<lambda> \<psi> . make\<o>(\<lambda> s w .  \<forall> s . eval\<o> (embedded_style \<psi>) s w)"}}

  So nothing prevents @{term "embedded_style \<phi>"} from evaluating its argument for a state
  different from the designated actual state @{term "dj"}. The condition @{term "(\<And>v. [\<psi> \<^bold>\<equiv> \<chi> in v])"}
  on the other hand only requires @{term "embedded_style \<psi>"} and @{term "embedded_style \<chi>"} to be
  (necessarily) equivalent in the \emph{actual state} - no statement about other states is implied.

  Another issue arises if one considers one of the example cases of legitimate uses of the rule
  of substitution in PLM (see~@{cite \<open>(\ref{PM-rule-sub-nec})\<close> PM}):

  \begin{addmargin}{1cm}
    If \<open>\<turnstile> \<exists>x A!x\<close> and \<open>\<turnstile>\<^sub>\<box> A!x \<equiv> \<not>\<diamond>E!x\<close>, then \<open>\<turnstile> \<exists>x \<not>\<diamond>E!x\<close>.
  \end{addmargin}

  This would not follow from the naive formulation above, even if it were derivable.
  Since \<open>x\<close> is \emph{bound} by
  the existential quantifier, in the functional representation @{term "embedded_style \<phi>"}
  has to have a different type. In the example @{term "embedded_style \<phi>"}
  has to be \mbox{@{term[eta_contract=false] "(\<lambda> \<psi> . embedded_style (\<^bold>\<exists> x :: \<nu> . \<psi> x))"}} which is of
  type @{typeof "(\<lambda> \<psi> . embedded_style (\<^bold>\<exists> x :: \<nu> . \<psi> x))"}. @{term "embedded_style \<psi>"} and
  @{term "embedded_style \<chi>"} have to be functions as well:
  \mbox{@{term[eta_contract=false] "(embedded_style \<psi>) = (\<lambda> x . embedded_style \<lparr>A!,x\<rparr>)"}} and
  \mbox{@{term[eta_contract=false] "(embedded_style \<chi>) = (\<lambda> x . embedded_style (\<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<rparr>))"}}.
  Consequently the equivalence condition for this case has to be reformulated to
  \mbox{@{term "\<And> x v. [\<psi> x \<^bold>\<equiv> \<chi> x in v]"}}\footnote{This is analog to the fact that \<open>x\<close>
  is a free variable in the condition \<open>\<turnstile>\<^sub>\<box> A!x \<equiv> \<not>\<diamond>E!x\<close> in PLM.}.

  
\<close>

subsubsection\<open>Solution\<close>

text\<open>

  The embedding employs a solution that is complex, but can successfully address the described
  issues.

  The following definition is introduced (see~\ref{TAO_PLM_Necessity}):

  \begin{center}
    @{thm Substable_def[expand2, of cond \<phi>]}
  \end{center}

  Given a condition @{term "cond"} a function @{term "embedded_style \<phi>"}
  is considered @{term "Substable"}, if and only if for all @{term "embedded_style \<psi>"}
  and  @{term "embedded_style \<chi>"} that satisfy @{term "cond"} it follows in each
  possible world @{term "v"} that \mbox{@{term "[\<phi> \<psi> \<^bold>\<equiv> \<phi> \<chi> in v]"}}\footnote{@{term "embedded_style \<psi>"}
  and  @{term "embedded_style \<chi>"} can have an arbitrary type. @{term "embedded_style \<phi>"} is a function
  from this type to formulas.}.

  Now several introduction rules for this property are derived. The idea is to capture the
  notion of \emph{subformula} in PLM. A few examples are:

  \begin{itemize}
    \item @{lemma "Substable cond (\<lambda>\<phi>. embedded_style \<Theta>)"
            by (simp add: embedded_style_def Substable_intro_const)}
    \item @{lemma "Substable cond \<psi> \<Longrightarrow> Substable cond (\<lambda>\<phi>. embedded_style ( \<^bold>\<not>\<psi> \<phi>))"
            by (simp add: embedded_style_def Substable_intro_not)}
    \item @{lemma "Substable cond \<psi> \<and> Substable cond \<chi> \<Longrightarrow> Substable cond (\<lambda>\<phi>. embedded_style (\<psi> \<phi> \<^bold>\<rightarrow> \<chi> \<phi>))"
            by (simp add: embedded_style_def Substable_intro_impl)}
  \end{itemize}

  These rules can be derived using theorems of PLM.

  As illustrated above in the functional setting substitution has to be allowed not only for formulas,
  but also for \emph{functions} to formulas. To that end the type class @{class Substable} is introduced
  that fixes a condition @{term "Substable_Cond"} to be used as @{term "cond"} in the definition above
  and assumes the following:

  \begin{center}
    @{thm Substable_class.rule_sub_nec[of \<phi> \<psi> \<chi> \<Theta> v]}
  \end{center}

  If @{term "embedded_style \<phi>"} is @{term "Substable"} (as per the definition above) under the
  condition @{term "Substable_Cond"} that was fixed in the type class, and @{term "embedded_style \<psi>"}
  and @{term "embedded_style \<chi>"} satisfy the fixed condition @{term "Substable_Cond"}, then everything
  that is true for @{term "[\<phi> \<psi> in v]"} is also true for @{term "[\<phi> \<chi> in v]"}.

  As a base case this type class is \emph{instantiated} for the type of formulas @{type \<o>} with
  the following definition of @{term "Substable_Cond"}:

  \begin{center}
    @{thm Substable_Cond_\<o>_def[expand2, of \<psi> \<chi>]}
  \end{center}

  Furthermore the type class is instantiated for \emph{functions} from an arbitrary type to
  a type of the class @{class Substable} with the following definition of @{term "Substable_Cond"}:

  \begin{center}
    @{thm Substable_Cond_fun_def[expand2, of \<psi> \<chi>]}
  \end{center}
\<close>
  
subsubsection\<open>Proving Methods\<close>

text\<open>

  \label{substitution-method}

  Although the construction above covers exactly the cases in which PLM allows substitutions, it does
  not yet have a form that allows to conveniently \emph{apply} the rule of substitution. In order
  to apply the rule, it first has to be established that a formula can be decomposed into a
  function with the substituents as arguments and it further has to be shown that this function
  satisfies the appropriate @{term "Substable"} condition. This complexity prevents any reasonable
  use cases. This problem is mitigated by the introduction of proving methods.
  The main method is called @{method PLM_subst_method}.

  This method uses a combination of pattern matching and automatic rule application to provide
  a convenient way to apply the rule of substitution in practice.

  For example assume the current proof objective is @{term "[\<^bold>\<not>\<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<rparr> in v]"}. Now it is possible to
  apply @{method PLM_subst_method} as follows:
  \begin{center}
    @{theory_text "apply (PLM_subst_method \"\<lparr>A!,x\<rparr>\" \"(\<^bold>\<not>(\<^bold>\<diamond>\<lparr>E!,x\<rparr>))\""}
  \end{center}
  The method automatically analyzes the current proving goal, uses pattern matching to find an
  appropriate choice for a function @{term "embedded_style \<phi>"}, applies the substitution rule and
  resolves the substitutability claim about @{term "embedded_style \<phi>"}.

  Consequently it can resolve the current proof objective
  by producing two new proving goals: @{term "\<forall>v. [\<lparr>A!,x\<rparr> \<^bold>\<equiv> \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<rparr> in v]"} and @{term "[\<^bold>\<not>\<lparr>A!,x\<rparr> in v]"},
  as expected. The complexity of the construction above is hidden away entirely.

  Similarly assume the proof objective is @{term "[\<^bold>\<exists> x . (\<^bold>\<not>(\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>))  in v]"}. Now the method
  @{method PLM_subst_method} can be invoked as follows:
  \begin{center}
    @{theory_text "apply (PLM_subst_method \"\<lambda>x . \<lparr>A!,x\<^sup>P\<rparr>\" \"\<lambda>x . (\<^bold>\<not>(\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>))\""}
  \end{center}
  This will result in the new proving goals:
  \mbox{@{term "\<forall>x v. [\<lparr>A!,x\<^sup>P\<rparr> \<^bold>\<equiv> \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr> in v]"}} and \mbox{@{term "[\<^bold>\<exists>x. \<lparr>A!,x\<^sup>P\<rparr> in v]"}}, as
  desired.

\<close>  

subsubsection\<open>Conclusion\<close>

text\<open>
  Although an adequate representation of the rule of substitution in the functional setting
  is challenging, the above construction allows a convenient use of the rule. Moreover it is
  important to note that despite the complexity of the representation no assumptions about
  the underlying model structure were made. The construction is completely
  derivable from the rules of PLM itself, so the devised rule is safe to use without
  compromising the provability claim of the layered structure of the embedding.

  All statements that are proven using the constructed substitution methods, remain derivable
  from the deductive system of PLM.
\<close>

subsection\<open>An Example Proof\<close>

text\<open>
  To illustrate how the derivation of theorems in the embedding works in practice,
  consider the following example\footnote{Since the whole proof is stated as raw Isabelle code,
  unfortunately no color-coding can be applied.}:
\<close>
  lemma "[\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi>) \<^bold>\<rightarrow> ((\<^bold>\<not>\<^bold>\<box>\<phi>) \<^bold>\<equiv> (\<^bold>\<box>(\<^bold>\<not>\<phi>))) in v]"
  proof (rule CP)
    assume "[\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi>) in v]"
    hence "[(\<^bold>\<not>\<^bold>\<box>(\<^bold>\<not>\<phi>)) \<^bold>\<equiv> \<^bold>\<box>\<phi> in v]"
      by (metis sc_eq_box_box_1 diamond_def vdash_properties_10)
    thus "[((\<^bold>\<not>\<^bold>\<box>\<phi>) \<^bold>\<equiv> (\<^bold>\<box>(\<^bold>\<not>\<phi>))) in v]"
      by (meson CP "\<^bold>\<equiv>I" "\<^bold>\<equiv>E" "\<^bold>\<not>\<^bold>\<not>I" "\<^bold>\<not>\<^bold>\<not>E")
  qed
text\<open>
  Since the statement is an implication it is derived using a \emph{conditional proof}.
  To that end the proof statement already applies the initial rule @{theory_text CP}.

  The proof objective inside the proof body is now \mbox{@{term "[\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi>) in v] \<Longrightarrow> [\<^bold>\<not>\<^bold>\<box>\<phi> \<^bold>\<equiv> \<^bold>\<box>\<^bold>\<not>\<phi> in v]"}},
  so \mbox{@{term "[\<^bold>\<not>\<^bold>\<box>\<phi> \<^bold>\<equiv> \<^bold>\<box>\<^bold>\<not>\<phi> in v]"}} has to be shown under the assumption \mbox{@{term "[\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi>) in v]"}}.
  Therefore the first step is to assume \mbox{@{term "[\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi>) in v]"}}.

  The second statement can now be automatically derived using the previously proven theorem
  @{theory_text sc_eq_box_box_1}, the definition of the diamond operator and a deduction
  rule. The final proof objective follows from a combination of introduction and elimination
  rules.

  The automated reasoning tool @{theory_text sledgehammer} can find proofs for
  the second and final statement automatically. It can even automatically find a proof
  for the entire theorem resulting in the following one-line proof:
\<close>
  
  lemma "[\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi>) \<^bold>\<rightarrow> ((\<^bold>\<not>\<^bold>\<box>\<phi>) \<^bold>\<equiv> (\<^bold>\<box>(\<^bold>\<not>\<phi>))) in v]"
    by (metis "\<^bold>\<equiv>I" CP "\<^bold>\<equiv>E"(1) "\<^bold>\<equiv>E"(2) raa_cor_1 sc_eq_box_box_1 diamond_def)

text\<open>
  So it can be seen that the embedding can be used to interactively prove statements
  with the support of automated reasoning tools and often even complete proofs
  for complex statements can be found automatically.
\<close>

subsection\<open>Summary\<close>
  
text\<open>
  A full representation of the deductive system PLM, as described in @{cite \<open>Chap. 9\<close> PM}, could
  be derived without violating the layered structure of the embedding.

  Although compromises affecting the degree of automation had to be made, the resulting
  representation can conveniently be used for the interactive construction of complex proofs
  while retaining the support of the automation facilities of Isabelle/HOL.
\<close>

(*<*)
end (* context PLM*)
(*>*)

section\<open>Artificial Theorems\<close>

(*<*)
context ArtificialTheorems
begin
(*>*)
  
text\<open>

  \label{artificial-theorems}

  The layered approach of the embedding provides the means to derive theorems
  independently of the representation layer and model structure. It is still interesting to consider
  some examples of theorems that are \emph{not} part of PLM, but can be derived in the
  embedding using its meta-logical properties.
\<close>

subsection\<open>Non-Standard $\lambda$-Expressions\<close>
  
text\<open>
  \label{artificial-theorems-lambda}

  The following statement involves a \<open>\<lambda>\<close>-expressions that contains encoding subformulas
  and is consequently not part of PLM (see~\ref{TAO_ArtificialTheorems}):

  \begin{center}
    @{thm lambda_enc_2[of v F y x]}
  \end{center}

  In this case traditional \<open>\<beta>\<close>-conversion still holds, since the \<open>\<lambda>\<close>-expression
  does not contain encoding expressions involving its bound variable\footnote{Consequently the
  matrix is a \emph{proper map}.}. On the other hand the following is \emph{not} a theorem in
  the embedding (the tool @{theory_text nitpick} can find a counter-model):

  \begin{center}
    @{term "[(\<lparr>\<^bold>\<lambda> x . \<lbrace>x\<^sup>P, F\<rbrace>, x\<^sup>P\<rparr> \<^bold>\<rightarrow> \<lbrace>x\<^sup>P, F\<rbrace>) in v]"}
  \end{center}

  Instead the following generalized versions of \<open>\<beta>\<close>-conversion are theorems:

  \begin{itemize}
    \item @{thm lambda_enc_4[of v F z]}
    \item @{thm lambda_ex[of v \<phi> z]}
  \end{itemize}

  These theorems can be equivalently stated purely in the embedded logic:
  
  \begin{itemize}
    \item @{thm lambda_enc_emb[of v F z]}
    \item @{thm lambda_ex_emb[of v \<phi> z]}
  \end{itemize}

  The second statement shows that in general \<open>\<lambda>\<close>-expressions
  in the embedding have a \emph{non-standard} semantics. As a special case, however,
  the behavior of \<open>\<lambda>\<close>-expressions is classical if restricted to
  proper maps, which is due to the following theorem\footnote{Note that for propositional formulas
  an equivalent statement is derivable in PLM as well.}:

  \begin{center}
    @{thm proper_beta[of \<phi> v x]}
  \end{center}

  As a consequence of the generalized \<open>\<beta>\<close>-conversion
  there are theorems in the embedding involving \<open>\<lambda>\<close>-expressions
  that \emph{do} contain encoding subformulas in the bound variable, e.g.:
  
  \begin{center}
    @{thm lambda_enc_1[of v F y]}
  \end{center}
  
  This topic is discussed in more detail in section~\ref{differences-lambda}.
\<close>

subsection\<open>Consequences of the Aczel-model\<close>

text\<open>
  Independently the following theorem is a consequence of the constructed Aczel-model:

  \begin{center}
    @{thm lambda_rel_extensional[of v a b R, THEN embedded_eq]}
  \end{center}

  The reason for this theorem to hold is that the condition on @{term "a"} and @{term "b"}
  forces the embedding to map both objects to the same urelement. By the definition of
  exemplification the presented \<open>\<lambda>\<close>-expressions only depend on this urelement,
  therefore they are forced to be equal. Neither the deductive system of PLM nor its formal
  semantics require this equality.

  Initial research suggests that this artificial theorem can be avoided by extending the
  embedding in the following way: the mapping from abstract objects to special urelements
  constructed in section~\ref{individuals-to-urelements} can be modified to depend on states.
  This way the condition used in the theorem only implies that @{term "a"}
  and @{term "b"} are mapped to the same urelement in the \emph{actual state}. Since
  they can still be mapped to different urelements in different states, the derived equality
  no longer follows.

  This extension of the embedding increases the complexity of the representation
  layer slightly, but its preliminary analysis suggests that it presents no further issues, so
  future versions of the embedding will in all likelihood include such a modification.
\<close>

(*<*)
end (* context ArtificialTheorems *)
(*>*)

section\<open>Sanity Tests\<close>
  
text\<open>
  The consistency of the constructed embedding can be verified by
  the model-finding tool @{theory_text nitpick} (see~\ref{TAO_SanityTests_Consistency}).
  Since the main construction of the embedding is definitional and only a minimal set of meta-logical
  axioms is used, this is expected.

  The hyperintensionality of the constructed model can be verified for some simple
  example cases. The following statements have counter-models (see~\ref{TAO_SanityTests_Intensionality}):

  \begin{itemize}
    \item @{term "[(\<^bold>\<lambda>y. (q \<^bold>\<or> \<^bold>\<not>q)) \<^bold>= (\<^bold>\<lambda>y. (p \<^bold>\<or> \<^bold>\<not>p)) in v]"}
    \item @{term "[(\<^bold>\<lambda>y. (p \<^bold>\<or> q)) \<^bold>= (\<^bold>\<lambda>y. (q \<^bold>\<or> p)) in v]"}
  \end{itemize}

  Furthermore the meta-logical axioms stated in section~\ref{concreteness} can be justified
  (see~\ref{TAO_SanityTests_MetaAxioms}):
  \begin{itemize}
    \item @{thm[display] SanityTests.OrdAxiomCheck[rename_abs x v y u z z]}
    \item @{thm[display] SanityTests.AbsAxiomCheck[rename_abs x v y u z z]}
    \item @{thm[display] SanityTests.PossiblyContingentObjectExistsCheck}
    \item @{thm[display] SanityTests.PossiblyNoContingentObjectExistsCheck}
  \end{itemize}

  The first axiom is equivalent to the fact that concreteness matches the domains of ordinary, resp.
  abstract objects, whereas the second and third axiom correspond to the conjuncts of
  axiom~(\ref{PM-qml}.4)@{cite PM}.

\begin{remark}
  Additionally some further desirable meta-logical properties of the embedding are verified
  in~\ref{TAO_SanityTests_MetaRelations} and~\ref{TAO_SanityTests_MetaLambda}.
\end{remark}
\<close>


chapter\<open>Technical Limitations of Isabelle/HOL\<close>
  
text\<open>
  Although the presented embedding shows that the generic proof assistant Isabelle/HOL
  offers a lot of flexibility in expressing even a very complex and challenging theory
  as the Theory of Abstract Objects, it has some limitations that required compromises
  in the formulation of the theory.

  In this chapter some of these limitations and their consequences for the embedding
  are discussed. Future versions of Isabelle may allow a clearer implementation especially
  of the layered approach of the embedding.
  
\<close>
  
section\<open>Limitations of Type Classes and Locales\<close>

text\<open>
  Isabelle provides a powerful tool for abstract reasoning called @{theory_text locale}.
  Locales are used for \emph{parametric} reasoning. Type classes, as already described 
  briefly in section~\ref{general-quantifier} and further mentioned in sections~\ref{general-identity}
  and~\ref{PLM-type-classes}, are in fact special cases of locales that are additionally
  connected to Isabelle's internal type system.

  The definition of a locale defines a set of constants that can use arbitrary type variables\footnote{Type
  classes on the other hand are restricted to only one type variable.}. Assumptions about
  these constants can be postulated that can be used in the reasoning within the context of
  the locale. Similarly to the instantiation of a type class, a locale can be \emph{interpreted}
  for specific definitions of the introduced constants, if it can be proven that the postulated assumptions
  are satisfied for the interpretation.

  Thereby it is possible to reason about abstract structures that are solely characterized by a specific
  set of assumptions. Given that it can be shown that these assumptions are satisfied for a concrete
  case, an interpretation of the locale allows the use of all theorems shown
  for the abstract case in the concrete application.

  Therefore in principle locales would be a perfect fit for the layered structure of the embedding:
  If the representation of the formal semantics and the axiom system could both be formulated
  as locales, it could first be shown that the axiom system is a \emph{sublocale} of the formal
  semantics, i.e. every set of constants that satisfies the requirements of the formal semantics
  also satisfies the requirements of the axiom system, and further the formal semantics could
  be interpreted for a concrete model structure.

  Since the reasoning within a locale cannot use further assumptions that are only satisfied
  by a specific interpretation, this way the universality of the reasoning based on the axiom
  system could be formally guaranteed - no proof that is solely based on the axiom locale
  could use any meta-logical statement tied to the underlying representation layer and
  model structure\footnote{Although the construction of chapter~\ref{embedding} provides the means
  for universal reasoning that is independent of a model as well, it depends on \emph{fair use} of
  the provided layer structure.}.

  However, a major issue arises when trying to formulate the axiom system as a locale.
  Constants in a locale have to be introduced with a fixed type.
  Although this type can use type variables, e.g. @{typ "'a\<Rightarrow>'a\<Rightarrow>'\<o>"},
  the type variable @{typ "'a"} is fixed throughout the locale. This makes it impossible
  to introduce a general binder for all-quantification or a general identity symbol in a single axiom
  locale that could be used for the statement of the axioms of quantification and the substitution
  of identicals.

  Several solutions to this problem could be considered: the identity relation could be
  introduced as a polymorphic constant \emph{outside the locale} and the locale could assume some
  properties for this constant for specific type variables. Before interpreting the
  locale the polymorphic constant could then be \emph{overloaded} for concrete types
  in order to be able to satisfy the assumptions. However, it would still be
  impossible to prove a general statement about identity: every statement would have
  to be restricted to a specific type, because in general no assumptions about the
  properties of identity could be made.

  Another solution would be to refrain from using general quantifiers and identity relations
  altogether, but to introduce separate binders and identity symbols for the type of individuals and
  each relation type. However, this would add a significant amount of notational complexity
  and would require to duplicate all statements that hold for quantification
  and identity in general for every specific type. Statements ranging over multiple types
  would even have to be stated for every possible combination of types separately.

  It could also be considered to introduce the axioms of quantification and identity separately
  from the axiom locale in a type class. An interpretation of the complete axiom system would
  then have to interpret the axiom locale, as well as instantiate the respective type classes.
  Since type classes can only use one type variable, this would make it impossible to use a type
  variable for truth values in the definition of the respective type classes, though. Consequently
  it is unclear how appropriate assumptions for such type classes could be formulated.
  Using separate locales instead of type classes would be connected with different issues.

  Several other concepts were considered during the construction of the embedding,
  but no solution was found that would both accurately represent the axiom system and
  still be notationally convenient.

  The most natural extension of Isabelle's locale system that would solve the described
  issues, would be the ability to introduce polymorphic constants in a locale that
  can be restricted to a type class (resp. a \emph{sort}). The type class could potentially even
  be introduced simultaneously with the locale. However, such a construction is currently not possible
  in Isabelle and as of yet it is unknown whether the internal type system of Isabelle
  would allow such an extension in general.
\<close>
  
section\<open>Case Distinctions by Type\<close>
  
text\<open>
  Although a general identity relation can be represented using type classes
  as described in sections~\ref{general-quantifier} and~\ref{general-identity}, this
  construction differs from the concept used in PLM. The identity relation of PLM is
  not determined by some set of properties, but by its definition for the specific concrete types.

  Isabelle does not allow the restriction of a type variable in a statement
  to a specific set of types. Type variables can only be restricted to specific \emph{sorts},
  so effectively to type classes. As mentioned in section~\ref{PLM-type-classes}, this means
  that statements about the general identity relation, that depend on the specific
  definitions for the concrete types, cannot be proven as in PLM by case distinction
  on types. Instead additional type classes have to be introduced that \emph{assume} the statements
  and then have to be instantiated for the concrete types.

  Although this construction involves some technical overhead, the solution is elegant and provides
  a flexible representation for such general statements.
\<close>

section\<open>Structural Induction and Proof-Theoretic Reasoning\<close>

text\<open>
  As mentioned in section~\ref{PLM-metarules}, some of the meta-rules that PLM can derive
  by induction on the length of a derivation, have to be proven using the semantics instead
  in the embedding, e.g. the deduction theorem
  \mbox{@{thm PLM.deduction_theorem[of v \<phi> \<psi>]}}.

  While the derivation of these fundamental rules using the semantics is justified,
  it would be interesting to investigate whether the proof-theoretic reasoning
  PLM uses in these cases can be reproduced in Isabelle/HOL. A related topic is
  the representation of the concept of \emph{modally-strict proofs} as described
  in sections~\ref{PLM-modally-strict} and~\ref{differences-modally-strict}.
\<close>

chapter\<open>Discussion and Results\<close>

section\<open>Differences between the Embedding and PLM\<close>
  
text\<open>
  Although the embedding attempts to represent the language and logic of PLM as precisely
  as possible, there remain some differences between PLM and its representation in Isabelle/HOL.
  Some of the known differences are discussed in the following sections.
  A complete analysis of the precise relation between PLM and the embedding unfortunately
  goes beyond the scope of this thesis and will only be possible after PLM has recovered
  from the discovered paradox (see~\ref{paradox}). Such an analysis will be a highly
  interesting and relevant topic for future research.
\<close>

subsection\<open>Propositional Formulas and $\lambda$-Expressions\<close>

text\<open>
  \label{differences-lambda}

  The main difference between the embedding and PLM is the fact that the embedding does
  not distinguish between propositional and non-propositional formulas.

  This purely syntactic distinction is challenging to reproduce in a shallow embedding that
  does not introduce the complete term structure of the embedded language directly.
  Instead the embedding attempts to analyze the semantic reason for the
  syntactic distinction and to devise a semantic criterion that can be used as a replacement
  for the syntactic restriction.

  The identified issue, that is addressed by the distinction in PLM, is described
  in section~\ref{russell-paradox}: Allowing non-propositional formulas in \<open>\<beta>\<close>-convertible
  \<open>\<lambda>\<close>-expressions without restriction leads to paradoxes.

  Since the embedding is known to be consistent, the issue presents itself in a slightly
  different fashion: the paradox is constructed under the assumption that \<open>\<beta>\<close>-conversion
  holds unconditionally for all \<open>\<lambda>\<close>-expressions. In the embedding on the other hand in
  general \<open>\<lambda>\<close>-expressions have a \emph{non-standard} semantics and \<open>\<beta>\<close>-conversion
  only follows as a special case (see~\ref{artificial-theorems-lambda}).
  Thereby the consistency of the system is preserved.

  With the definition of \emph{proper maps} (see~\ref{lambda-expressions}), the embedding
  constructs a necessary and sufficient condition on functions that may serve as matrix of
  a \<open>\<lambda>\<close>-expression while allowing \<open>\<beta>\<close>-conversion.

  The idea is that every \<open>\<lambda>\<close>-expression that is syntactically well-formed
  in PLM should have a proper map as its matrix. Two subtleties have to be considered, though:

  It was discovered that there are \<open>\<lambda>\<close>-expressions which are part of PLM, whose matrix
  does not correspond to a proper map in the embedding. The analysis of this issue led to the
  discovery of a paradox in the formulation of PLM and is discussed in more detail in
  section~\ref{paradox}. As a consequence these cases will not constitute proper
  \<open>\<lambda>\<close>-expressions in future versions of PLM.

  The remaining subtlety is the fact that there are proper maps, that do not correspond to
  propositional formulas. Some examples have already been mentioned in section~\ref{artificial-theorems-lambda}.
  Therefore the embedding suggests that the theory of PLM can be consistently extended to include
  a larger set of proper, \<open>\<beta>\<close>-convertible \<open>\<lambda>\<close>-expressions. Since the set of
  relations of PLM already has to be adjusted to prevent the discovered paradox, such an extension presents
  a viable option.

  Once PLM has recovered from the paradox, future research can consider available
  options to align the set of relations present in the embedding with the resulting set of
  relations of the new version of PLM.
\<close>



subsection\<open>Terms and Variables\<close>

text\<open>

  In PLM an individual term can be an individual variable, an individual constant or a definite
  description. A large number of statements is formulated using specific object-language variables instead
  of metavariables ranging over arbitrary terms. From such a statement its universal generalization
  can be derived using the rule GEN,  which then can be instantiated for any individual term,
  given that it denotes (\mbox{\<open>\<exists>\<beta> \<beta> = \<tau>\<close>}).

  As already mentioned in sections~\ref{individual-terms-and-descriptions} and~\ref{quantification-axioms}
  the embedding uses a slightly different approach: In the embedding individuals and
  individual terms have different \emph{types}.

  The technicalities of this approach and a discussion about the accuracy of this representation
  were already given in the referenced sections, so at this point it suffices to summarize the
  resulting differences between the embedding and PLM:

  \begin{itemize}
    \item The individual variables of PLM are represented as variables of type @{type \<nu>} in the embedding.
    \item Individual constants can be represented by declaring constants of type @{type \<nu>}.
    \item Meta-level variables (like \<open>\<tau>\<close>) ranging over all individual terms
          in PLM can be represented as variables of type @{type \<kappa>}.
    \item Objects of type @{type \<nu>} have to be explicitly converted to objects of type @{type \<kappa>}
          using the decoration @{term "embedded_style (DUMMY\<^sup>P)"}, if they are to be used in a context
          that allows general individual terms.
    \item The axioms of quantification are adjusted to go along with this representation
          (see~\ref{quantification-axioms}).
  \end{itemize}

  In PLM the situation for relation variables, constants and terms is analog. However, the
  embedding uses the following simplification in order to avoid the additional complexity
  introduced for individuals:

  Since at the time of writing PLM unconditionally asserts \mbox{\<open>\<exists>\<beta> \<beta> = \<tau>\<close>}
  for any relation term by an axiom, the embedding uses only one type \<open>\<Pi>\<^sub>n\<close> for each
  arity of relations. Therefore no special type conversion between variables and terms is necessary
  and every relation term can immediately be instantiated for a variable of type \<open>\<Pi>\<^sub>n\<close>.
  This hides the additional steps PLM employs for such instantiations (the generalization by GEN
  followed by an instantiation using quantification theory). Since \mbox{\<open>\<exists>\<beta> \<beta> = \<tau>\<close>} holds
  unconditionally for relation terms, this simplification is justified.

  However, the recent developments described in section~\ref{paradox} suggest that \mbox{\<open>\<exists>\<beta> \<beta> = \<tau>\<close>}
  will in all likelihood no longer hold unconditionally for every relation term in future versions of PLM.
  Therefore, future versions of the embedding will have to include a distinction between relation
  terms and relation variables in a similar way as is already done for individuals. An alternative
  approach that could result in a more elegant representation would be to implement concepts of free
  logic based on the research in @{cite FreeLogic} for both individuals and relations.
\<close>

subsection\<open>Modally-strict Proofs and the Converse of RN\<close>

(*<*)
context PLM
begin
(*>*)
  
text\<open>

\label{differences-modally-strict}

As described in section~\ref{PLM-modally-strict} modally-strict theorems
in the embedding are stated in the form \mbox{@{term "[\<phi> in v]"}}, so they are stated
to be semantically true for an arbitrary possible world @{term "v"}.

Modally-strict theorems in PLM are defined using a proof-theoretic concept:
modally-strict proofs are not allowed to use modally-fragile axioms. They are solely derived
from axioms whose necessitations are axioms as well (see~\ref{axiom-schemata}).

The metarule RN states in essence that if there is a modally-strict proof for \<open>\<phi>\<close>,
then \<open>\<box>\<phi>\<close> is derivable as a theorem. PLM proves this fact by induction on the length
of the derivation. Remark (\ref{PM-abstraction-contingent})@{cite PM}
gives an example of a case in which the converse is false: if \<open>\<box>\<phi>\<close> is derivable as a
theorem, this does not imply that there is a modally-strict proof for \<open>\<phi>\<close>.

However, in the embedding the following is derivable from the semantics of
the box operator:

\begin{center}
  @{lemma "[\<^bold>\<box>\<phi> in dw] \<Longrightarrow> (\<forall> v . [\<phi> in v])" by (simp add: Semantics.T6) }
\end{center}

So although the converse of RN is not true in PLM, an equivalent statement for theorems of
the form \mbox{@{term "[\<phi> in v]"}} in the embedding can be derived from the semantics.

The modally-strict theorems of PLM are a subset of a larger class of theorems, namely the theorems
that are \emph{necessarily true}. Semantically a statement of the form \mbox{@{term "[\<phi> in v]"}}
in the embedding is derivable, whenever @{term "embedded_style \<phi>"} is a \emph{necessary theorem}.

Unfortunately there is no semantic criterion that allows to decide whether a statement is a necessary
theorem or a modally-strict theorem. Therefore, the embedding has to express modally-strict theorems
as necessary theorems, for which the converse of RN is in fact true.

This still does not compromise the claim that any statement that is derived in \ref{TAO_PLM}
is also derivable in PLM: the basis for this claim is that no proofs in this layer may rely on the
meta-logical properties of the embedding, but only the fundamental meta-rules of PLM are allowed
to derive theorems from the axioms.
Since the converse of RN is neither a fundamental meta-rule of PLM, nor derivable without using
the semantics, it is not stated as an admissible rule for these proofs. Thereby it is guaranteed
that no statement of the form \mbox{@{term "[\<phi> in v]"}} is derived that is not a modally-strict
theorem of PLM.

Unfortunately this has the consequence that the proving method @{method PLM_solver} cannot be
equipped with a reversible elimination rule for the box operator, which reduces its power
as a proving method. However, preserving the claim that theorems derived in the embedding
are also theorems of PLM even when restricting to modally-strict theorems was given preference
over an increased level of automation.
\<close>


section\<open>A Paradox in PLM\<close>

text\<open>
  \label{paradox}

  During the analysis of the constructed embedding it was discovered
  that the formulation of the theory in PLM at the time of writing
  allowed paradoxical constructions.

  This section first describes the process that led to the discovery of the paradox and
  the role the embedding played in it, after which the construction of the paradox is
  outlined in the language of PLM.

  The paradox has since been confirmed by Edward Zalta and a vivid discussion
  about its repercussions and possible solutions has developed. At the time of writing
  it has become clear that there are several options to recover from the paradox while
  in essence retaining the full set of theorems of PLM. So far no final decision has been
  reached about which option will be implemented in future versions of PLM.
\<close>

subsection\<open>Discovery of the Paradox\<close>
  
text\<open>
  The discovery of the paradox originates in the analysis of the concept of \emph{proper maps}
  in the embedding and its relation to propositional formulas in PLM, which are the only formulas
  PLM allows as the matrix of \<open>\<lambda>\<close>-expressions (see~\ref{differences-lambda}).

  While trying to verify the conjecture, that the matrix of every \<open>\<lambda>\<close>-expression allowed in PLM
  corresponds to a proper map in the embedding, it was discovered, that \<open>\<lambda>\<close>-expressions of
  the form \mbox{\<open>[\<lambda>y F\<iota>x(y[\<lambda>z Rxz])]\<close>} in which the bound variable \<open>y\<close> occurs in
  an encoding formula inside the matrix of a definite description, were part of PLM, but their
  matrix was \emph{not} a proper map in the embedding and therefore \<open>\<beta>\<close>-conversion
  was not derivable for these terms.

  Further analysis showed that a modification of the embedding which would allow \<open>\<beta>\<close>-conversion
  for such expressions, would have to involve a restriction of the Aczel-model (in particular of the map
  from abstract objects to urelements).

  In order to understand how the Aczel-model could be adequately restricted, the
  consequences of allowing \<open>\<beta>\<close>-conversion in the mentioned cases \emph{by assumption}
  were studied in the embedding. This led to the first proof of inconsistency
  (see~\ref{TAO_Paradox_original-paradox}):

  \begin{center}
    @{lemma "(\<And>G \<phi>. IsProperInX (\<lambda>x. embedded_style \<lparr>G,\<^bold>\<iota>y. \<phi> y x\<rparr>)) \<Longrightarrow> False"
      by (unfold embedded_style_def, simp, insert Paradox.original_paradox, simp)}
  \end{center}

  Under the assumption that @{term "(\<lambda>x. embedded_style \<lparr>G,\<^bold>\<iota>y. \<phi> y x\<rparr>)"} is a proper map for
  arbitrary @{term "embedded_style G"} and @{term "embedded_style \<phi>"},
  @{term "False"} is derivable in the embedding. However \<open>\<lambda>\<close>-expressions with the
  equivalent of such maps as matrix were in fact part of PLM.

  Since the inconsistency can be derived without relying on the meta-logical properties of
  the embedding, it was immediately possible to translate the proof back to the language of PLM.
  The resulting formulation then served as the basis for further
  discussions with Edward Zalta.

  Since then the issue leading to the paradox was identified as the \emph{description backdoor}
  (see~\ref{TAO_Paradox_description_backdoor}) that can be used to construct a variety of
  paradoxical cases, e.g. the paradox described in section~\ref{russell-paradox} can be reconstructed.
  This refined version of the paradox is used in the inconsistency proof in \ref{TAO_Paradox_russell-paradox}
  and is outlined in the language of PLM in the next section. The general situation
  leading to the paradox is repeated without referring to the particularities of the embedding.
\<close>

subsection\<open>Construction using the Language of PLM\<close>
  
text\<open>

  Object theory distinguishes between propositional and
  non-propositional formulas. Propositional formulas are not allowed to
  contain encoding subformulas, so for example \mbox{\<open>\<exists>F xF\<close>} is not
  propositional. Only propositional formulas can be the matrix of a
  \<open>\<lambda>\<close>-expression, so \mbox{\<open>[\<lambda>x \<exists>F xF]\<close>} is not a valid term of
  the theory - it is excluded syntactically.

  The reason for this is that considering \mbox{\<open>[\<lambda>x \<exists>F xF & \<not>Fx]\<close>} a valid, denoting
  \<open>\<lambda>\<close>-expression for which \<open>\<beta>\<close>-conversion holds would result in a
  paradox as described in section~\ref{russell-paradox}.

  Excluding non-propositional formulas in
  \<open>\<lambda>\<close>-expressions was believed to be sufficient to prevent such
  inconsistencies. This was shown to be incorrect, though.

  The problem is the \emph{description backdoor}. The term \mbox{\<open>[\<lambda>y F\<iota>x\<psi>]\<close>}
  is well-formed, even if \<open>\<psi>\<close> is \emph{not} propositional. This is due to the definition
  of \emph{subformula}: \<open>\<psi>\<close> is \emph{not} a subformula of \<open>F\<iota>x\<psi>\<close>, so \<open>\<psi>\<close> \emph{may} contain
  encoding subformulas itself and \<open>F\<iota>x\<psi>\<close> is still a propositional formula.

  This was deemed to be no problem and for cases like \mbox{\<open>[\<lambda>y F\<iota>x(xG)]\<close>} as
  they are mentioned and used in PLM this is indeed true.

  It had not been considered that \<open>y\<close> may appear within the matrix of
  such a description and more so, it may appear in an encoding expression, for example 
  \mbox{\<open>[\<lambda>y F\<iota>x(xG & yG)]\<close>} is still a propositional formula.

  Therefore, the following construction is possible:

  \begin{equation}\tag{1}
    \<open>[\<lambda>y [\<lambda>z \<forall>p(p\<rightarrow>p)]\<iota>x(x = y & \<psi>)]\<close>
  \end{equation}

  Here \<open>\<psi>\<close> can be an arbitrary non-propositional formula in which \<open>x\<close> and \<open>y\<close>
  may be free and (1) is still a valid, denoting \<open>\<lambda>\<close>-expression for which
  \<open>\<beta>\<close>-conversion holds.

  By \<open>\<beta>\<close>-conversion and description theory the following is derivable:

  \begin{equation}\tag{2}
    \<open>[\<lambda>y [\<lambda>z \<forall>p(p\<rightarrow>p)]\<iota>x(x = y & \<psi>)]x \<equiv> \<psi>\<^sup>x\<^sub>y\<close>
  \end{equation}

  \begin{remark}
    Using a modally-strict proof only the following is derivable:\\
    \mbox{\<open>[\<lambda>y [\<lambda>z \<forall>p(p\<rightarrow>p)]\<iota>x(x = y & \<psi>)]x \<equiv> \<A>\<psi>\<^sup>x\<^sub>y\<close>}\\
    For the construction of the paradox, the modally-fragile statement
    is sufficient. However, it is possible to construct similar paradoxical cases
    without appealing to any modally-fragile axioms or theorems as well.
  \end{remark}

  This effectively undermines the intention of restricting \<open>\<lambda>\<close>-expressions
  to only propositional formulas:

  Although \mbox{\<open>[\<lambda>x \<exists>F xF & \<not>Fx]\<close>} is not part of the language, it is possible to
  formulate the following instead:

  \begin{equation}\tag{3}
    \<open>[\<lambda>y [\<lambda>z \<forall>p(p\<rightarrow>p)]\<iota>x(x = y & (\<exists>F yF & \<not>Fy))]\<close>
  \end{equation}

  If one considers (2) now, one can see that this \<open>\<lambda>\<close>-expressions behaves
  exactly the way that \mbox{\<open>[\<lambda>x \<exists>F xF & \<not>Fx]\<close>} would, if it were part of the
  language, i.e. the result of \<open>\<beta>\<close>-reduction for \mbox{\<open>[\<lambda>x \<exists>F xF & \<not>Fx]\<close>} would be
  the same as the right hand side of (2) when applied to (3). Therefore, the \<open>\<lambda>\<close>-expression
  in (3) can be used to reproduce the paradox described in section~\ref{russell-paradox}.
\<close>

subsection\<open>Possible Solutions\<close>

text\<open>
  Fortunately no theorems were derived in PLM, that actually use problematic
  \<open>\<lambda>\<close>-expressions as described above. Therefore, it is possible to recover from the
  paradox without losing any theorems. At the time of writing, it seems likely that
  a concept of \emph{proper} \<open>\<lambda>\<close>-expressions will be introduced to the theory and only
  \emph{proper} \<open>\<lambda>\<close>-expressions will be forced to have denotations and allow \<open>\<beta>\<close>-conversion.
  Problematic \<open>\<lambda>\<close>-expressions that would lead to paradoxes, will not be considered \emph{proper}.
  Several options are available to define the propriety of \emph{\<open>\<lambda>\<close>-expressions}
  and to adjust PLM in detail.

  As a consequence the purely syntactical distinction between propositional
  and non-propositional formulas is no longer sufficient to guarantee
  that every relation term has a denotation. The embedding of the theory shows
  that an adequate definition of \emph{proper \<open>\<lambda>\<close>-expressions}
  can consistently replace this distinction entirely yielding a broader set of relations.
  The philosophical implications of such a radical modification of the theory
  have not yet been analyzed entirely though, and at the time of writing
  it is an open question whether such a modification may be implemented in
  future versions of PLM.

\<close>


(*<*)
end (* context PLM *)
(*>*)


section\<open>A Meta-Conjecture about Possible Worlds\<close>
  
(*<*)
context PossibleWorlds
begin
(*>*)
  
text\<open>
  A conversation between Bruno Woltzenlogel Paleo and Edward Zalta about the Theory
  of Abstract Objects led to the following meta-conjecture:

  \textquote{
      For every syntactic possible world \emph{w}, there exists a semantic
      point \emph{p} which is the denotation of \emph{w}.
  }\footnote{This formulation originates in the resulting e-mail correspondence between
  Bruno Woltzenlogel Paleo and Christoph Benzm\"uller.}

  Since the embedding constructs a representation of the semantics of PLM, it was
  possible to formally analyze the relationship between syntactic and semantic possible worlds
  and arrive at the following theorems (see~\ref{TAO_PossibleWorlds}):

  \begin{itemize}
    \item @{thm SemanticPossibleWorldForSyntacticPossibleWorlds[of w]}
    \item @{thm SyntacticPossibleWorldForSemanticPossibleWorlds[of w]}
  \end{itemize}

  The first statement shows that for every \emph{syntactic} possible world @{term "embedded_style x"}
  there is a \emph{semantic} possible world @{term "v"}, such that a proposition is syntactically
  true in @{term "embedded_style x"}, if and only if it is semantically true in @{term "v"}.

  The second statement shows that for every \emph{semantic} possible world @{term "v"} there
  is a \emph{syntactic} possible world @{term "embedded_style x"}, such that a proposition is semantically
  true in @{term "v"}, if and only if it is \emph{syntactically} true in @{term "embedded_style x"}.

  This result extends the following theorems already derived syntactically in PLM (\<open>w\<close> is restricted
  to only range over syntactic possible worlds):
  \begin{itemize}
    \item \<open>\<diamond>p \<equiv> \<exists>w(w \<Turnstile> p)\<close> \hfill{(\ref{PM-fund}.1)}
    \item \<open>\<box>p \<equiv> \<forall>w(w \<Turnstile> p)\<close> \hfill{(\ref{PM-fund}.2)}
  \end{itemize}

  Whereas the syntactic statements of PLM already show the relation between the modal operators
  and syntactic possible worlds, the semantic statements derived in the embedding show that
  there is in fact a natural bijection between syntactic and semantic possible worlds.

  This example shows that a semantical embedding allows a detailed analysis of the semantical
  properties of a theory and to arrive at interesting meta-logical results.
\<close>

(*<*)
end (* context PossibleWorlds *)
(*>*)

section\<open>Functional Object Theory\<close>
  
text\<open>
  The first and foremost goal of the presented work was to show that the second-order fragment of
  the Theory of Abstract Objects as described in PLM can be represented in functional
  higher-order logic using a shallow semantical embedding.

  As a result a theory was constructed in Isabelle/HOL that - although its faithfulness
  is yet to be formally verified - is most likely able to represent and verify all reasoning
  in the target theory. A formal analysis of the faithfulness of the embedding
  is unfortunately not possible at this time, since the theory of PLM first has to be adjusted
  to prevent the discovered paradox. Depending on the precise modifications of PLM the embedding
  will have to be adjusted accordingly, after which the question can be revisited.

  The embedding goes to great lengths to construct a restricted environment, in which it is possible
  to derive new theorems that can easily be translated back to the reference system of PLM.
  The fact that the construction of the paradox described in section~\ref{paradox} could be reproduced
  in the target logic, strongly indicates the merits and success of this approach.

  Independently of the relation between the embedding and the target system, a byproduct
  of the embedding is a working functional variant of object theory that deserves to be studied in
  its own right. To that end future research may want to drop the layered structure of the embedding and
  dismiss all constructions that solely serve to restrict reasoning in the embedding in order to
  more closely reproduce the language of PLM. Automated reasoning in the resulting theory will be
  significantly more powerful and the interesting properties of the original theory, that result
  from the introduction of abstract objects and encoding, can still be preserved.
\<close>

section\<open>Relations vs. Functions\<close>

text\<open>
  As mentioned in the introduction, Oppenheimer and Zalta argue that relational type theory is more
  fundamental than functional type theory (see @{cite rtt}). One of their main arguments is that the
  Theory of Abstract Objects is not representable in functional type theory.
  The success of the presented embedding, however, suggests that the topic has to be
  examined more closely.

  Their result is supported by the presented work in the following sense: it is impossible to
  represent the Theory of Abstract Objects by representing its \<open>\<lambda>\<close>-expressions directly as
  primitive \<open>\<lambda>\<close>-expressions in functional logic. Furthermore, exemplification cannot
  be represented classically as function application, while at the same time introducing encoding
  as a second mode of predication.

  This already establishes that the traditional approach of translating relational type theory
  to functional type theory in fact fails for the Theory of Abstract Objects. A simple version of
  functional type theory, that only involves two primitive types (for individuals and propositions),
  is insufficient for a representation of the theory.

  The embedding does not share several of the properties of
  the representative functional type theory constructed in @{cite \<open>pp. 9-12\<close> rtt}:

  \begin{itemize}
    \item Relations are \emph{not} represented as functions from individuals to propositions.
    \item Exemplification is \emph{not} represented as simple function application.
    \item The \<open>\<lambda>\<close>-expressions of object theory are \emph{not} represented as
          primitive \<open>\<lambda>\<close>-expressions.
  \end{itemize}

  To illustrate the general schema that the embedding uses instead assume
  that there is a primitive type for each arity of relations \<open>R\<^sub>n\<close>.
  Let further \<open>\<iota>\<close> be the type of individuals and \<open>\<o>\<close> be the type of propositions.
  The general construct is now the following:

  \begin{itemize}
    \item Exemplification (of an \<open>n\<close>-place relation) is a function of type \mbox{\<open>R\<^sub>n\<Rightarrow>\<iota>\<Rightarrow>\<dots>\<Rightarrow>\<iota>\<Rightarrow>\<o>\<close>}.
    \item Encoding is a function of type \mbox{\<open>\<iota>\<Rightarrow>R\<^sub>1\<Rightarrow>\<o>\<close>}.
    \item To represent \<open>\<lambda>\<close>-expressions functions \<open>\<Lambda>\<^sub>n\<close> of type \mbox{\<open>(\<iota>\<Rightarrow>\<dots>\<Rightarrow>\<iota>\<Rightarrow>\<o>)\<Rightarrow>R\<^sub>n\<close>} are introduced.
          The \<open>\<lambda>\<close>-expression \mbox{\<open>[\<lambda>x\<^sub>1\<dots>x\<^sub>n \<phi>]\<close>} of object theory is represented as
          \mbox{\<open>\<Lambda>\<^sub>n[\<lambda>x\<^sub>1\<dots>x\<^sub>n \<phi>]\<close>}.
  \end{itemize}

  The Theory of Abstract Objects restricts the matrix of \<open>\<lambda>\<close>-expressions to propositional
  formulas, so not all functions of type \mbox{\<open>\<iota>\<Rightarrow>\<dots>\<Rightarrow>\<iota>\<Rightarrow>\<o>\<close>} are supposed to denote relations.
  However, since in classical functional type theory functions are total, \<open>\<Lambda>\<^sub>n\<close> has to map
  all these functions to some object of type \<open>R\<^sub>n\<close>. To solve this problem concepts used in
  the embedding of free logic can help\footnote{See the embedding of free logic constructed in @{cite FreeLogic}.}.
  The function \<open>\<Lambda>\<^sub>n\<close> can map functions of type \mbox{\<open>\<iota>\<Rightarrow>\<dots>\<Rightarrow>\<iota>\<Rightarrow>\<o>\<close>} that do not
  correspond to propositional formulas to objects of type \<open>R\<^sub>n\<close> that
  represent invalid (resp. non-existing) relations. For invalid relations the functions used
  to represent encoding and exemplification can be defined to map to an object of type \<open>\<o>\<close>
  that represents invalid propositions.

  Oppenheimer and Zalta argue that using a free logic and letting non-propositional
  formulas fail to denote is not an option, since it prevents classical reasoning for non-propositional
  formulas\footnote{See @{cite \<open>pp. 30-31\<close> rtt}.}. Although this is true for the case of a simple
  functional type theory, it does not apply to the constructed theory: since only objects of
  type \<open>R\<^sub>n\<close> may fail to denote, non-propositional reasoning is unaffected.

\begin{remark}
  Although the constructed functional type theory is based on the general structure of the
  presented embedding, instead of introducing concepts of free logic, \<open>\<lambda>\<close>-expressions
  involving non-propositional formulas are assigned \emph{non-standard} denotations,
  i.e. they do denote, but \<open>\<beta>\<close>-conversion only holds under certain conditions
  (see~\ref{differences-lambda}). Although this concept has merits as well, future versions of the embedding
  may instead utilize the concepts described in @{cite FreeLogic} to replace this construction
  by a free logic implementation that will more closely reflect the concepts of propositional formulas
  and \<open>\<lambda>\<close>-expressions in object theory.
\end{remark}


  The constructed theory can represent the relations and \<open>\<lambda>\<close>-expressions of object theory,
  as well as exemplification and encoding. Furthermore, the embedding shows that it has a model and
  that an adequate intensional interpretation of propositions can be used to
  preserve the desired hyperintensionality of relations in \<open>\<lambda>\<close>-expressions.

  In summary it can be concluded that a representation of object theory in functional type theory
  is feasible, although it is connected with a fair amount of complexity (i.e. the introduction of
  additional primitive types and the usage of concepts of intensional and free logic).
  On the other hand, whether this result contradicts the philosophical claim that relations are
  more fundamental than functions, is still debatable considering the fact that the proposed
  construction has to introduce new primitive types for relations\footnote{Note, however,
  that the embedding can represent relations as functions acting on urelements following the
  Aczel-model.} and the construction is complex in general. Further it has to be noted that so
  far only the second-order fragment of object theory has been considered and the full
  type-theoretic version of the theory may present further challenges.

\pagebreak
\<close>

section\<open>Conclusion\<close>

text\<open>
  The presented work shows that shallow semantical embeddings in HOL have the potential to represent
  even highly complex theories that originate in a fundamentally different tradition of logical
  reasoning (e.g. relational instead of functional type theory). The presented embedding represents
  the most ambitious project in this area so far and its success clearly shows the merits of the approach.

  Not only could the embedding uncover a previously unknown paradox in the formulation of its target
  theory, but it could contribute to the understanding of the relation between functional and
  relational type theory and provide further insights into the general structure of the target theory,
  its semantics and possible models. It can even show that a consistent extension of the theory
  is possible that can increase its expressibility.

  For the field of mathematics an analysis of chapters 14 and 15 of PLM, that construct
  natural numbers and theoretical mathematical objects and relations in object theory,
  is of particular interest. The embedding can be a significant aid in the study of these chapters, since the
  properties of the derived objects and relations can immediately be analyzed and verified using the extensive library for abstract
  mathematical reasoning already present in Isabelle/HOL as a reference.

  The presented work introduces novel concepts that can benefit future endeavors of semantical
  embeddings in general: a layered structure allows the representation of a target theory without
  extensive prior results about its model structure and provides the means to comprehensively
  study potential models. Custom proving methods can benefit automated reasoning in an embedded
  logic and provide the means to reproduce even complex deductive rules of a target system
  in a user-friendly manner.

  The fact that the embedding can construct a verified environment which allows to conveniently
  prove and verify theorems in the complex target system while retaining the support of automated
  reasoning tools, shows the great potential of semantical embeddings in providing the means
  for a productive interaction between humans and computer systems.
\<close>
  
(*<*)
end
(*>*)
