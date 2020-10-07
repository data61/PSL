chapter \<open>Definition\<close>

theory %invisible Definition
imports Main
begin

text \<open>\label{chap:definition}\<close>

text \<open>In stepwise refinement~\cite{DijkstraConstructive,WirthRefinement},
a program is derived from a specification
via a sequence of intermediate specifications.\<close>

text \<open>Pop-refinement (where `pop' stands for `predicates over programs')
is an approach to stepwise refinement,
carried out inside an interactive theorem prover
(e.g.\ Isabelle/HOL, HOL4, Coq, PVS, ACL2)
as follows:
\begin{enumerate}
\item
Formalize the syntax and semantics
of (the needed subset of) the target programming language (and libraries),
as a deep embedding.
\item
Specify the requirements
by defining a predicate over programs
that characterizes the possible implementations.
\item
Refine the specification stepwise
by defining monotonically decreasing predicates over programs
(decreasing with respect to inclusion, i.e.\ logical implication),
according to decisions that narrow down the possible implementations.
\item
Conclude the derivation
with a predicate that characterizes a unique program in explicit syntactic form,
from which the program text is readily obtained.
\end{enumerate}\<close>


end %invisible
