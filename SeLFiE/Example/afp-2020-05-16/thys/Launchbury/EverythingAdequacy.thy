(*<*)
theory EverythingAdequacy
imports CorrectnessOriginal Adequacy "HOL-Library.LaTeXsugar" 
begin

(*
notation (latex output) DenotationalUpd.ESem ("\<lbrakk>_\<rbrakk>\<^bsup>u\<^esup>\<^bsub>_\<^esub>"  [60,60] 60)
notation (latex output) "Denotational-PropsUpd.HSem_syn" ("\<lbrace>_\<rbrace>\<^bsup>u\<^esup>_"  [60,60] 60)
*)

translations
  "xs" <= "CONST set xs"
translations
  "a" <= "CONST atom a"
translations
  "a" <= "CONST image (CONST atom) a"

abbreviation map_of_syntax :: "'a::type \<Rightarrow> 'b::type \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> bool" ("'(_, _') \<in> _") 
  where "map_of_syntax x e \<Gamma> \<equiv> map_of \<Gamma> x = Some e"

abbreviation delete_syntax :: "heap \<Rightarrow> var \<Rightarrow> heap" ("_\\_") 
  where "delete_syntax \<Gamma> x \<equiv> delete x \<Gamma>"

notation (latex output) domA ("\<^latex>\<open>\\textrm{\\textsf{dom}}\<close> _")
notation (latex output) bn ("\<^latex>\<open>\\textrm{\\textsf{dom}}\<close> _")

declare [[names_short]]
declare [[show_question_marks = false]]


(*>*)
subsection \<open>Main definitions and theorems\<close>

text \<open>
For your convenience, the main definitions and theorems of the present work are assembled in this section. The following 
formulas are mechanically pretty-printed versions of the statements as defined resp.\ proven in Isabelle.
Free variables are all-quantified. Some type conversion functions (like @{term_type set}) are omitted.
The relations \<open>\<sharp>\<close> and \<open>\<sharp>*\<close> come from the Nominal package and express freshness of the
variables on the left with regard to the expressions on the right.

\input{map.tex}
\<close>

subsubsection \<open>Expressions\<close>

text \<open>
The type @{typ var} of variables is abstract and provided by the Nominal package. All we know about
it is that it is countably infinite.
Expressions of type @{typ exp} are given by the following grammar:
\begin{alignatstar}{2}
@{term e} \Coloneqq {}& @{term "Lam [x]. e"} &\quad& \text{lambda abstraction}\\
\mid {} & @{term "App e x"} && \text{application}\\
\mid {} & @{term "Var x"} && \text{variable} \\
\mid {} & @{term "Let as e"} && \text{recursive let}
\end{alignatstar}
In the introduction we pretty-print expressions to resemble the notation in \cite{launchbury} and omit
the constructor names @{term Var}, @{term App}, \<open>Lam\<close> and @{term Let}. In the actual theories, these are visible.
These expressions are, due to the machinery of the Nominal package, actually alpha-equivalency classes, so @{thm alpha_test} holds provably. This differs from Launchbury's original definition, which expects distinctly-named expressions and performs explicit alpha-renaming in the semantics.

The type @{type heap} is an abbreviation for @{typ "(var \<times> exp) list"}. These are \emph{not} alpha-equivalency classes, i.e.\ we manage the bindings in heaps explicitly.
\<close>

subsubsection \<open>The natural semantics\<close>

text_raw \<open>
\newlength{\rulelen}
\setlength{\rulelen}{\linewidth}
\newlength{\rulenamelen}
\settowidth{\rulenamelen}{~{\sc Application}}
\addtolength{\rulelen}{-\rulenamelen}
\<close>

text \<open>
Launchbury's original semantics, extended with some technical overhead related to name binding (following \cite{sestoft}),
is defined as follows:\\
%\begin{center}
\parbox[t]{\rulelen}{\centering@{thm[mode=Axiom] Launchbury.reds.Lambda}}~{\sc Lambda}\\[2ex]
\parbox[t]{\rulelen}{\centering@{thm[mode=Rule] Launchbury.reds.Application}}~{\sc Application}\\[2ex]
\parbox[t]{\rulelen}{\centering@{thm[mode=Rule] Launchbury.reds.Variable}}~{\sc Variable}\\[2ex]
\parbox[t]{\rulelen}{\centering@{thm[mode=Rule] Launchbury.reds.Let}}~{\sc Let}
%\end{center}
\<close>


subsubsection \<open>The denotational semantics\<close>

text \<open>
The value domain of the denotational semantics is the initial solution to
\[
D = [D \to D]_\bot
\]
as introduced in \cite{abramsky}. The type @{typ Value}, together with the bottom value @{term_type "\<bottom>::Value"}, the
injection @{term_type "Fn"} and the projection @{term "DUMMY \<down>Fn DUMMY"}\<open>::\<close>@{typeof "Fn_project"},
is constructed as a pointed chain-complete partial order from this equation by the HOLCF package.
The type of semantic environments is  @{typ "var \<Rightarrow> Value"}.

The semantics of an expression @{term_type "e :: exp"} in an environment @{term "\<rho>"}\<open>::\<close>@{typ "var \<Rightarrow> Value"} is 
written \mbox{@{term_type "Rep_cfun (Denotational.ESem e) \<rho>"}} and defined by the following equations:
\begin{alignstar}
@{thm (lhs) Denotational.ESem_simps(1)} & = @{thm (rhs) Denotational.ESem_simps(1)} \\
@{thm (lhs) Denotational.ESem_simps(2)} & = @{thm (rhs) Denotational.ESem_simps(2)} \\
@{thm (lhs) Denotational.ESem_simps(3)} & = @{thm (rhs) Denotational.ESem_simps(3)} \\
@{thm (lhs) Denotational.ESem_simps(6)} & = @{thm (rhs) Denotational.ESem_simps(6)}.
\end{alignstar}
\<close>

text\<open>
The expression @{term "Denotational.EvalHeapSem_syn \<Gamma> \<rho>"} 
maps the evaluation function over a heap, returning an environment:
\begin{alignstar}
@{thm (lhs) lookupEvalHeap'[where f = "(\<lambda> e. Denotational.ESem_syn e \<rho>)"]}
  & = @{thm (rhs) lookupEvalHeap'[where f = "(\<lambda> e. Denotational.ESem_syn e \<rho>)"]}
  && \text{if } @{thm (prem 1) lookupEvalHeap'[where f = "(\<lambda> e. Denotational.ESem_syn e \<rho>)"]} \\
@{thm (lhs) lookupEvalHeap_other[where f = "(\<lambda> e. Denotational.ESem_syn e \<rho>)"]}
  & = @{thm (rhs) lookupEvalHeap_other[where f = "(\<lambda> e. Denotational.ESem_syn e \<rho>)"]}
  && \text{if } @{thm (prem 1) lookupEvalHeap_other[where f = "(\<lambda> e. Denotational.ESem_syn e \<rho>)"]}
\end{alignstar}
\<close>

text \<open>
The semantics @{term "Rep_cfun (Denotational.HSem \<Gamma>) \<rho>"}\<open>::\<close>@{typ "var \<Rightarrow> Value"} of a
heap @{term "\<Gamma> :: heap"}\<open>::\<close>@{typ heap}
in an environment @{term "\<rho>"}\<open>::\<close>@{typ "var \<Rightarrow> Value"} is  defined by the recursive equation
\[ @{thm "Denotational.HSem_eq"} \]
where
\begin{alignstar}
@{thm (lhs) override_on_apply_notin} & = @{thm (rhs) override_on_apply_notin}  && \text{if } @{thm (prem 1) override_on_apply_notin} \\
@{thm (lhs) override_on_apply_in} & = @{thm (rhs) override_on_apply_in}  && \text{if } @{thm (prem 1) override_on_apply_in}.
\end{alignstar}

The semantics of the heap in the empty environment @{term "\<bottom>"} is abbreviated as @{term "Denotational.AHSem_bot \<Gamma>"}.
\<close>

subsubsection \<open>Correctness and Adequacy\<close>
text \<open>The statement of correctness  reads:
If @{thm (prem 1) CorrectnessOriginal.correctness(1)} and, as a side condition,
@{thm (prem 2) CorrectnessOriginal.correctness(1)} holds,
then
\[
@{thm (concl) CorrectnessOriginal.correctness(1)}.
\]
\<close>
(*
\]
and
\[
@{thm (concl) CorrectnessOriginal.correctness(2)}.
\]
The latter is phrased slightly different than in \cite{launchbury}, which defines a partial relation
@{text "\<le>"} on heaps, by being more explictit on what set of variables the heaps agree.
*)

text \<open>The statement of adequacy reads:
\[
\text{If }
@{thm (prem 1) adequacy}\text{ then }@{thm (concl) adequacy}.
\]
\<close>

subsection \<open>Differences to our previous work\<close>

text \<open>
We have previously published \cite{breitner2013} of which the present work is a continuation. They differ in scope and focus:

\subsubsection{The treatment of $\sqcup$}

In \cite{breitner2013}, the question of the precise meaning of $\sqcup$ is discussed in detail. The
original paper is not clear about whether this operator denotes the least upper bound, or the
right-sided override operator. A lemma stated in \cite{launchbury} only holds if $\sqcup$ is the least upper bound,
but with that definition, Launchbury's Theorem 2 -- the generalized correctness theorem -- is false;
a counter-example is given in \cite{breitner2013}.

We came up with an alternative operational semantics that keeps more of the
evaluation context in the judgments and allows the correctness theorem to be proved inductively
without the problematic generalization. We proved the two operational semantics equivalent and thus
obtained the (non-generalized) correctness of Launchbury's semantics.

We also showed that if one takes $\sqcup$ to be the update operator, Theorem 2 holds and the proof
goes through as it is. Furthermore, we showed that the resulting denotational semantics are
identical for expressions, and can differ only for heaps. Therefore, the question of the precise
meaning of $\sqcup$ can be considered of little importance and for the present work we soley work
with right sided updates. We also avoid the ambiguos syntax $\sqcup$ and write
@{term "DUMMY ++\<^bsub>DUMMY\<^esub> DUMMY"} instead (the index indicates on what set the function on the right
overrides the function on the left). The alternative operational semantics is not included in this work.

\subsubsection{The types of environments}

Another difference is the choice of the type for environments, which map variables to semantics values.
A naive choice is @{typ "var \<Rightarrow> Value"}, but this causes problems when defining the value semantics,
for which
\[
@{thm Denotational.ESem_simps(1)}
\]
is a defining equation. The argument on the left hand side is the representative of an equivalence class
(defined using the Nominal package), so this is only allowed if the right hand side is indeed independent
 of the actual choice of \<open>x\<close>. This is shown most commonly and easily if \<open>x\<close> is fresh in all the
other arguments (@{term "atom x \<sharp> \<rho>"}), and indeed the Nominal package allows us to specify this as a side
condition to the defining equation, which is what we did in \cite{breitner2013}.

But this convenience comes as a price: Such side-conditions are
only allowed if the argument has finite support (otherwise there might no variable fulfilling
@{term "atom x \<sharp> \<rho>"}). More precisely: The type of the argument must be a member of the @{class fs} typeclass
provided by the Nominal package. The type @{typ "var \<Rightarrow> Value"} cannot be made a member of this class,
as there obviously are elements that have infinite support. The fix here was to introduce a new type
 constructor, \<open>fmap\<close>, for partial functions with finite domain. This is fine: Only functions
with finite domain matter in our formalisation.

The introduction of \<open>fmap\<close> had further consequences. The main type class of the HOLCF package,
which we use to define domains and continuous functions on them, is the class @{class cpo}, of chain-complete
partial orders. With the usual ordering on partial functions, \<open>(var, Value) fmap\<close> cannot be
a member of this class. The fix here is to use a different ordering and only let elements be compareable
that have the same domain. In our formalisation, the domain is alway known (e.g.\ all variables
bound on some heap), so this worked out.

But not without causing yet another issue: With this ordering, \<open>(var, Value) fmap\<close> is a
@{class cpo}, but lacks a bottom element, i.e.\ now it is no @{class pcpo}, and HOLCF's built-in operator
@{term "\<mu> x. f x"} for expressing least fixed-points, as they occur in the semantics of heaps,
is not available. Furthermore, \<open>\<squnion>\<close> is not a total function, i.e.\ defined only on a subset of
all possible arguments. The solution was a rather convoluted set of theories that formalize functions that
are continuous on a specific set, fixed-points on such sets etc.

In the present work, this problems is solved in a much more elegant way. Using a small trick we defined
the semantics functions so that
\[
@{thm Denotational.ESem_simps(1)}
\]
holds unconditionally. The actual, technical definition is
\[
@{thm Denotational.ESem_simps_as_defined(1)}
\]
where the right-hand-side can be shown to be invariant of the choice of \<open>x\<close>, as
@{term "x \<notin> fv (Lam [x]. e)"}. Once the function is defined, the equality
@{thm Denotational.ESem_considers_fv'} can be proved. With that, the desired equation for
@{thm (lhs) Denotational.ESem_simps(1)} follows. The same trick is applied to the equation for
@{thm (lhs) Denotational.ESem_simps(6)}.

This allows us to use the type @{typ "var \<Rightarrow> Value"} for the semantic envionments and considerably
simplifies the formalization compared to \cite{breitner2013}.

\subsubsection{No type @{type assn}}

The nominal package provides means to define types that are alpha-equivalence classes, and we use that
to define our type @{type exp}, which contains a constructor @{term "Let binds expr"}. The desired type
of the parameter for the binding is @{typ "(var \<times> exp) list"}, but the Nominal package does not support
such nested recursion, and requires a mutual recursive definition with a custom type (@{type assn})
with constructors @{term ANil} and @{term ACons} that is isomorphic to @{typ "(var \<times> exp) list"}.
In \cite{breitner2013}, this type and conversion functions from and to @{typ "(var \<times> exp) list"}
cluttered the whole development. In the present work we improved this by defining the type with
a ``temporary'' constructor @{term_type LetA}. Afterwards we define conversions functions and
the desired constructor @{term_type Let}, and re-state all lemmas produced by the Nominal package
(such as type exhaustiveness, distinctiveness of constructors and the induction rules) with that
constructor. From that point on, the development is free of the crutch @{typ assn}.

In short, the notable changes in this work over \cite{breitner2013} are:
\begin{itemize}
\item We consider \<open>\<squnion>\<close> to be a right-sided update and do discuss neither the problem with
\<open>\<squnion>\<close> denoting the least uppper bound, nor possible solutions.
\item This, a simpler choice for the type of semantic environments and a better definition of the type for terms, considerably simplifies the
work.
\item Most importantly, this work contains a complete and formal proof of the adequacy of Launchbury's semantics.
\end{itemize}
\<close>

text\<open>
\subsection{Related work}

Lidia Sánchez-Gil, Mercedes Hidalgo-Herrero and Yolanda Ortega-Mallén have worked on formal aspects
of Launchbury's semantics as well.

They identified a step in his adequacy proof
relating the standard and the resourced denotational semantics that is not as trivial as it seems at
first and worked out a detailed pen-and-paper proof \cite{functionspaces}, where they first 
construct a similarity relation @{term "DUMMY \<triangleleft>\<triangleright> DUMMY"} between the standard semantic domain
(@{type Value}) and the resourced domain (@{type CValue}) and show that the denotation semantics yield
similar results (@{thm denotational_semantics_similar}), which is one step in the adequacy proof.
We formalized this (Sections \ref{sec_ValueSimilarity} and \ref{sec_Denotational-Related}), identifying
and fixing a mistake in the paper (Lemma 2.3(3) does not hold; the problem can be fixed by applying
an extra round of take-induction in the proof of Proposition 9).

Currently, they are working on completing the adequacy proof as outlined by Launchbury, i.e.\ by going
via the alternative natural semantics given in \cite{launchbury}, which differs from the semantics
above in that the application rule works with an indirection on the heap instead of a substitution
and that the variable rule has no blackholing and no update. In \cite{indirections}, they relate
the original semantics with one where indirections have been introduced. The next step, modifying
the variable rule, is under development. Once that is done they can close the loop and have
completed Launchbury's work.

This work proves the adequacy as stated by Launchbury as well, but in contrast to his proof outline no
alternative operational semantics is introduced. The problems of indirection vs. substitution and
of blackholing is solved on the denotational side instead, which turned out to be much easier than
proving the various operational semantics to be equivalent.
\<close>

(*<*)

end
(*>*)
