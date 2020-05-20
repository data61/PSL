chapter \<open>Related Work\<close>

theory %invisible Related_Work
imports Main
begin

text \<open>\label{chap:related}\<close>

text \<open>In existing approaches to stepwise refinement
(e.g.~\cite{BBook,ZReference,SystematicVDM,RefinementCalculus}),
specifications express requirements less directly than pop-refinement:
a specification implicitly characterizes its possible implementations
as the set of programs that can be derived from the specification
via refinement (and code generation).
This is a more restrictive way to characterize a set of programs
than defining a predicate over deeply embedded programs
in a theorem prover's general-purpose logic
(as in pop-refinement).\<close>

text \<open>This restrictiveness precludes
some of the abilities discussed in \chapref{chap:general},
e.g.\ the ability to express, and guarantee through refinement,
certain program-level requirements like constraints on memory footprint.
A derivation may be steered to produce a program
that satisfies desired requirements not expressed by the specification,
but the derivation or program must be examined in order to assess that,
instead of just examining the specification
and letting the theorem prover automatically check
the sequence of refinement steps
(as with pop-refinement).
Existing refinement approaches could be extended
to handle additional kinds of requirements (e.g.\ non-functional),
but for pop-refinement no theorem prover extensions are necessary.\<close>

text \<open>In existing refinement approaches,
each refinement step yields a new specification that characterizes
a (strict or non-strict) subset of the implementations
characterized by the old specification,
analogously to pop-refinement.
However, the restrictiveness explained above,
together with any inherent constraints
imposed by the refinement relation over specifications,
limits the choice of the subset,
providing less fine-grained control than pop-refinement.\<close>

text \<open>In existing refinement approaches,
the ``indirection'' between a specification and its set of implementations
may create a disconnect between
properties of a specification and properties of its implementations.
For example, along the lines discussed in \secref{sec:nondet},
a relational specification may satisfy a hyperproperty
but some of its implementations may not,
because the refinement relation may reduce the possible behaviors.
Since a pop-refinement specification directly makes statements
about the possible implementations of the requirements,
this kind of disconnect is avoided.\<close>


end %invisible
