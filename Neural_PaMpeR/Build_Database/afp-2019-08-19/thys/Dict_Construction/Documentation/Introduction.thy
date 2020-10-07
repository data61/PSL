section \<open>Dictionary Construction\<close>

theory Introduction
imports Main
begin

subsection \<open>Introduction\<close>

text \<open>
 Isabelle's logic features \emph{type classes}~\cite{haftmann2007typeclasses,wenzel1997typeclasses}.
 These are built into the kernel and are used extensively in theory developments.
 The existing \emph{code generator}, when targeting Standard ML, performs the well-known dictionary
 construction or \emph{dictionary translation}~\cite{haftmann2010codegeneration}.
 This works by replacing type classes with records, instances with values, and occurrences with
 explicit parameters.

 Haftmann and Nipkow give a pen-and-paper correctness proof of this construction
 \cite[\<open>\<section>\<close>4.1]{haftmann2010codegeneration}, based on a notion of \emph{higher-order rewrite
 systems.}
 The resulting theorem then states that any well-typed term is reduction-equivalent before and after
 class elimination.
 In this work, the dictionary construction is performed in a certified fashion, that is, the
 equivalence is a theorem inside the logic.
\<close>

subsection \<open>Encoding classes\<close>

text \<open>
  The choice of representation of a dictionary itself is straightforward: We model it as a
  @{command datatype}, along with functions returning values of that type. The alternative here
  would have been to use the @{command record} package. The obvious advantage is that we could
  easily model subclass relationships through record inheritance. However, records do not support
  multiple inheritance. Since records offer no advantage over datatypes in that regard, we opted for
  the more modern @{command datatype} package.
\<close>

text \<open>Consider the following example:\<close>

class plus =
  fixes plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"

text \<open>
  This will get translated to a @{command datatype} with a single constructor taking a single
  argument:
\<close>

datatype 'a dict_plus =
  mk_plus (param_plus: "'a \<Rightarrow> 'a \<Rightarrow> 'a")

text \<open>A function using the @{class plus} constraint:\<close>

definition double :: "'a::plus \<Rightarrow> 'a" where
"double x = plus x x"

definition double' :: "'a dict_plus \<Rightarrow> 'a \<Rightarrow> 'a" where
"double' dict x = param_plus dict x x"

subsection \<open>Encoding instances\<close>

text \<open>
  A more controversial design decision is how to represent dictionary certificates. For example,
  given a value of type @{typ "nat dict_plus"}, how do we know that this is a faithful representation
  of the @{class plus} instance for @{typ nat}?
\<close>

text \<open>
  \<^item> Florian Haftmann proposed a ``shallow encoding''. It works by exploiting the internal treatment
    of constants with sort constraints in the Isabelle kernel. Constants themselves do not carry
    sort constraints, only their definitional equations. The fact that a constant only appears with
    these constraints on the surface of the system is a feature of type inference.

    Instead, we can instruct the system to ignore these constraints. However, any attempt at
    ``hiding'' the constraints behind a type definition ultimately does not work: The nonemptiness
    proof requires a witness of a valid dictionary for an arbitrary, but fixed type @{typ 'a}, which
    is of course not possible (see \<open>\<section>\<close>\ref{sec:impossibility} for details).

  \<^item> The certificates contain the class axioms directly. For example, the @{class semigroup_add}
    class requires @{term "(a + b) + c = a + (b + c)"}.

    Translated into a definition, this would look as follows:

    @{term
      "cert_plus dict \<longleftrightarrow>
        (\<forall>a b c. param_plus dict (param_plus dict a b) c = param_plus dict a (param_plus dict b c))"}

    Proving that instances satisfy this certificate is trivial.

    However, the equality proof of \<open>f'\<close> and \<open>f\<close> is impossible: they are simply not equal in general.
    Nothing would prevent someone from defining an alternative dictionary using multiplication
    instead of addition and the certificate would still hold; but obviously functions using
    @{const plus} on numbers would expect addition.

    Intuitively, this makes sense: the above notion of ``certificate'' establishes no connection
    between original instantiation and newly-generated dictionaries.

    Instead of proving equality, one would have to ``lift'' all existing theorems over the old
    constants to the new constants.

  \<^item> In order for equality between new and old constants to hold, the certificate needs to capture
    that the dictionary corresponds exactly to the class constants. This is achieved by the
    representation below.
    It literally states that the fields of the dictionary are equal to the class constants.
    The condition of the resulting equation can only be instantiated with dictionaries corresponding
    to existing class instances. This constitutes a \<^emph>\<open>closed world\<close> assumption, i.e., callers of
    generated code may not invent own instantiations.
\<close>

definition cert_plus :: "'a::plus dict_plus \<Rightarrow> bool" where
"cert_plus dict \<longleftrightarrow> (param_plus dict = plus)"

text \<open>
  Based on that definition, we can prove that @{const double} and @{const double'} are equivalent:
\<close>

lemma "cert_plus dict \<Longrightarrow> double' dict = double"
unfolding cert_plus_def double'_def double_def
by auto

text \<open>
  An unconditional equation can be obtained by specializing the theorem to a ground type and
  supplying a valid dictionary.
\<close>

subsection \<open>Implementation\<close>

text \<open>
  When translating a constant \<open>f\<close>, we use existing mechanisms in Isabelle to obtain its
  \<^emph>\<open>code graph\<close>. The graph contains the code equations of all transitive dependencies (i.e.,
  other constants) of \<open>f\<close>. In general, we have to re-define each of these dependencies. For that,
  we use the internal interface of the @{command function} package and feed it the code equations
  after performing the dictionary construction. In the standard case, where the user has not
  performed a custom code setup, the resulting function looks similar to its original definition.
  But the user may have also changed the implementation of a function significantly afterwards.
  This imposes some restrictions:

  \<^item> The new constant needs to be proven terminating. We apply some heuristics to transfer the
    original termination proof to the new definition. This only works when the termination condition
    does not rely on class axioms. (See \<open>\<section>\<close>\ref{sec:termination} for details.)
  \<^item> Pattern matching must be performed on datatypes, instead of the more general
    @{command code_datatype}s.
  \<^item> The set of code equations must be exhaustive and non-overlapping.
\<close>

end