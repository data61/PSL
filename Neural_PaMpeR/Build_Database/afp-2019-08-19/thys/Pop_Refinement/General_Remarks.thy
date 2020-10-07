chapter \<open>General Remarks\<close>

theory %invisible General_Remarks
imports Main
begin

text \<open>\label{chap:general}\<close>

text \<open>The following remarks apply to pop-refinement in general,
beyond the examples in \chapref{chap:exampleI} and \chapref{chap:exampleII}.\<close>


section \<open>Program-Level Requirements\<close>
text \<open>\label{sec:progreq}\<close>

text \<open>By predicating directly over programs,
a pop-refinement specification
(like @{term spec\<^sub>0}
in \secref{sec:specificationI} and \secref{sec:specificationII})
can express program-level requirements
that are defined in terms of the vocabulary of the target language,
e.g.\
constraints on memory footprint
(important for embedded software),
restrictions on calls to system libraries to avoid or limit information leaks
(important for security),
conformance to coding standards
(important for certain certifications),
and use or provision of interfaces
(important for integration with existing code).
Simple examples are
@{term "wfp p"} in \secref{sec:specificationI} and \secref{sec:specificationII},
@{term "para p = [''x'', ''y'']"} in \secref{sec:specificationI},
and @{term "iovars p"} in \secref{sec:specificationII}.\<close>


section \<open>Non-Functional Requirements\<close>
text \<open>\label{sec:nonfuncreq}\<close>

text \<open>Besides functional requirements,
a pop-refinement specification can express non-functional requirements,
e.g.\ constraints on
computational complexity,
timing,
power consumption,
etc.%
\footnote{In order to express these requirements,
the formalized semantics of the target language
must suitably include non-functional aspects,
as in the simple model in \secref{sec:nonfunc}.}
A simple example is
@{term "costp p \<le> (3::nat)"} in \secref{sec:specificationI}.\<close>


section \<open>Links with High-Level Requirements\<close>
text \<open>\label{sec:hilevreq}\<close>

text \<open>A pop-refinement specification can explicate links
between high-level requirements and target programs.\<close>

text \<open>For example,
@{term "\<forall>x y. exec p [x, y] = Some (f x y)"}
in @{term spec\<^sub>0} in \secref{sec:specificationI}
links the high-level functional requirement expressed by @{term f}
to the target program @{term p}.%
\footnote{Similarly, the functional requirements in \secref{sec:specificationII}
could be expressed abstractly
in terms of mappings between low and high inputs and outputs
(without reference to program variables and executions)
and linked to program variables and executions.
But \secref{sec:specificationII} expresses such functional requirements
directly in terms of programs
to keep the example (whose focus is on hyperproperties) simpler.}\<close>

text \<open>As another example,
a function \<open>sort :: nat list \<Rightarrow> nat list\<close>,
defined to map each list of natural numbers to its sorted permutation,
expresses a high-level functional requirement
that can be realized in different ways.
An option is a procedure that destructively sorts an array in place.
Another option is a procedure that returns a newly created sorted linked list
from a linked list passed as argument and left unmodified.
A pop-refinement specification can pin down the choice,
which matters to external code that uses the procedure.\<close>

text \<open>As a third example,
a high-level model of a video game or physical simulator
could use real numbers and differential equations.
A pop-refinement specification could
state required bounds on how
the idealized model is approximated by an implementation
that uses floating point numbers and difference equations.\<close>

text \<open>Different pop-refinement specifications
could use the same high-level requirements
to constrain programs in different target languages or in different ways,
as in the @{term sort} example above.
As another example,
the high-level behavior of an operating system
could be described by a state transition system
that abstractly models internal states and system calls;
the same state transition system could be used
in a pop-refinement specification of a Haskell simulator that runs on a desktop,
as well as in a pop-refinement specification of a C/Assembly implementation
that runs on a specific hardware platform.\<close>


section \<open>Non-Determinism and Under-Specification\<close>
text \<open>\label{sec:nondet}\<close>

text \<open>The interaction of refinement
with non-determinism and under-specification
is delicate in general.
The one-to-many associations of a relational specification
(e.g.\ a state transition system
where the next-state relation may associate
multiple new states to each old state)
could be interpreted as
non-determinism
(i.e.\ different outcomes at different times, from the same state)
or under-specification
(i.e.\ any outcome is allowed, deterministically or non-deterministically).
Hyperproperties like GNI
are consistent with the interpretation as non-determinism,
because security depends on the ability to yield different outcomes,
e.g.\ generating a nonce in a cryptographic protocol.
The popular notion of refinement as inclusion of sets of traces
(e.g.~\cite{AbadiLamportRefinement})
is consistent  with the interpretation as under-specification,
because a refined specification is allowed to reduce the possible outcomes.
Thus, hyperproperties are not always preserved by
refinement as trace set inclusion~\cite{ClarksonSchneiderHyperproperties}.\<close>

text \<open>As exemplified in \secref{sec:specificationII},
a pop-refinement specification can explicitly distinguish
non-determinism and under-specification.
Each pop-refinement step preserves all the hyperproperties
expressed or implied by the requirement specification.%
\footnote{Besides security hyperproperties expressed in terms of non-determinism,
pop-refinement can handle more explicit security randomness properties.
The formalized semantics of a target language could
manipulate probability distributions over values (instead of just values),
with random number generation libraries
that return known distributions (e.g.\ uniform),
and with language operators that transform distributions.
A pop-refinement specification could include
randomness requirements on program outcomes expressed in terms of distributions,
and each pop-refinement step would preserve such requirements.}\<close>


section \<open>Specialized Formalisms\<close>
text \<open>\label{sec:specform}\<close>

text \<open>Specialized formalisms (e.g.\ state machines, temporal logic),
shallowly or deeply embedded into the logic of the theorem prover
(e.g.~\cite{AFP-Statecharts,AFP_TLA}),
can be used to express some of the requirements
of a pop-refinement specification.
The logic of the theorem prover provides semantic integration
of different specialized formalisms.\<close>


section \<open>Strict and Non-Strict Refinement Steps\<close>
text \<open>\label{sec:strictref}\<close>

text \<open>In a pop-refinement step from @{term spec\<^sub>i} to \<open>spec\<^sub>i\<^sub>+\<^sub>1\<close>,
the two predicates may be equivalent, i.e.\ \<open>spec\<^sub>i\<^sub>+\<^sub>1 = spec\<^sub>i\<close>.
But the formulation of \<open>spec\<^sub>i\<^sub>+\<^sub>1\<close> should be ``closer''
to the implementation than the formulation of @{term spec\<^sub>i}.
An example is in \secref{sec:refI:stepI}.\<close>

text \<open>When the implication \<open>spec\<^sub>i\<^sub>+\<^sub>1 p \<Longrightarrow> spec\<^sub>i p\<close> is strict,
potential implementations are eliminated.
Since the final predicate of a pop-refinement derivation
must characterize a unique program,
some refinement steps must be strict---%
unless the initial predicate @{term spec\<^sub>0}
is satisfiable by a unique program,
which is unlikely.\<close>

text \<open>A strict refinement step may lead to a blind alley
where \<open>spec\<^sub>i\<^sub>+\<^sub>1 = \<lambda>p. False\<close>,
which cannot lead to a final predicate that characterizes a unique program.
An example is discussed in \secref{sec:refI:stepIV}.\<close>


section \<open>Final Predicate\<close>
text \<open>\label{sec:lastpred}\<close>

text \<open>The predicate that concludes a pop-refinement derivation
must have the form @{term "spec\<^sub>n p \<equiv> p = p\<^sub>0"},
where @{term p\<^sub>0} is the representation of a program's abstract syntax
in the theorem prover,
as in \secref{sec:refI:stepVII} and \secref{sec:refII:stepVI}.
This form guarantees that
the predicate characterizes exactly one program
and that the program is explicitly determined.
@{term p\<^sub>0} witnesses the consistency of the requirements,
i.e.\ the fact that @{term spec\<^sub>0} is not always false;
inconsistent requirements cannot lead to a predicate of this form.\<close>

text \<open>A predicate of the form @{term "spec\<^sub>i \<equiv> p = p\<^sub>0 \<and> \<Phi> p"}
may not characterize a unique program:
if @{term "\<Phi> p\<^sub>0"} is false, @{term spec\<^sub>i} is always false.
To conclude the derivation, @{term "\<Phi> p\<^sub>0"} must be proved.
But it may be easier to prove the constraints expressed by @{term \<Phi>}
as @{term p\<^sub>0} is constructed in the derivation.
For example,
deriving a program from @{term spec\<^sub>0} in \secref{sec:specificationI}
based on the functional constraint and ignoring the cost constraint
would lead to a predicate @{term "spec\<^sub>i \<equiv> p = p\<^sub>0 \<and> costp p \<le> (3::nat)"},
where @{term "costp p\<^sub>0 \<le> (3::nat)"} must be proved to conclude the derivation;
instead, the derivation in \secref{sec:refinementI}
proves the cost constraint as @{term p\<^sub>0} is constructed.
Taking all constraints into account at each stage of the derivation can help
choose the next refinement step
and reduce the chance of blind alleys
(cf.\ \secref{sec:refI:stepIV}).\<close>

text \<open>The final predicate @{term spec\<^sub>n} expresses
a purely syntactic requirement,
while the initial predicate @{term spec\<^sub>0} usually includes
semantic requirements.
A pop-refinement derivation progressively turns
semantic requirements into syntactic requirements.
This may involve
rephrasing functional requirements
to use only operations supported by the target language
(e.g.\ lemma \<open>f_rephrased\<close> in \secref{sec:refI:stepIV}),
obtaining shallowly embedded program fragments,
and turning them into their deeply embedded counterparts
(e.g.\ \secref{sec:refI:stepV} and \secref{sec:refI:stepVI}).%
\footnote{In \secref{sec:refinementII},
program fragments are introduced directly,
without going through shallow embeddings.}\<close>


section \<open>Proof Coverage\<close>
text \<open>\label {sec:allproved}\<close>

text \<open>In a chain of predicate inclusions
as in \secref{sec:refinementI} and \secref{sec:refinementII},
the proofs checked by the theorem prover encompass the range
from the specified requirements to the implementation code.
No separate code generator is needed
to turn low-level specifications into code:
pop-refinement folds code generation into the refinement sequence,
providing fine-grained control on the implementation code.\<close>

text \<open>A purely syntactic pretty-printer is needed
to turn program abstract syntax,
as in \secref{sec:refI:stepVII} and \secref{sec:refII:stepVI},
to concrete syntax.
This pretty-printer can be eliminated
by formalizing in the theorem prover
the concrete syntax of the target language
and its relation to the abstract syntax,
and by defining the @{term spec\<^sub>i} predicates over program concrete syntax---%
thus, folding pretty-printing into the refinement sequence.\<close>


section \<open>Generality and Flexibility\<close>
text \<open>\label{sec:genflex}\<close>

text \<open>Inclusion of predicates over programs
is a general and flexible notion of refinement.
More specialized notions of refinement
(e.g.~\cite{HoareData,MilnerSimulation})
can be used for any auxiliary types, functions, etc.\
out of which the @{term spec\<^sub>i} predicates may be constructed,
as long as the top-level implication
\<open>spec\<^sub>i\<^sub>+\<^sub>1 p \<Longrightarrow> spec\<^sub>i p\<close> holds at every step.\<close>


end %invisible
