(*  Title:      Monad_Normalisation.thy
    Author:     Manuel Eberl, TU München
    Author:     Joshua Schneider, ETH Zurich
    Author:     Andreas Lochbihler, ETH Zurich

Normalisation of monadic expressions.
*)

section \<open>Normalisation of monadic expressions\<close>

theory Monad_Normalisation
imports "HOL-Probability.Probability"
keywords "print_monad_rules" :: diag
begin

text \<open>
  The standard monad laws
  \begin{gather}
    \label{eq:return:bind}
    \<open>return a \<bind> f = f a\<close>
    \\
    \label{eq:bind:return}
    \<open>x \<bind> return = x\<close>
    \\
    \label{eq:bind:assoc}
    \<open>(x \<bind> f) \<bind> g = x \<bind> (\<lambda>a. f a \<bind> g)\<close>
  \end{gather}
  yield a confluent and terminating rewrite system.
  Thus, when these equations are added to the simpset, the simplifier can normalise monadic 
  expressions and decide the equivalence of monadic programs (in the free monad).

  However, many monads satisfy additional laws.
  In some monads, it is possible to discard unused effects
  \begin{gather}
    \label{eq:discard}
    \<open>x \<bind> (\<lambda>_. y) = y\<close>
  \end{gather}
  or duplicate effects
  \begin{gather}
    \label{eq:duplicate}
    \<open>x \<bind> (\<lambda>a. x \<bind> f a) = x \<bind> (\<lambda>a. f a a)\<close>
  \end{gather}
  or commute independent computations
  \begin{gather}
    \label{eq:commute}
    \<open>x \<bind> (\<lambda>a. y \<bind> f a) = y \<bind> (\<lambda>b. x \<bind> (\<lambda>a. f a b))\<close>.
  \end{gather}
  For example, @{typ "_ option"} satisfies \eqref{eq:duplicate} and \eqref{eq:commute},
  @{typ "_ set"} validates \eqref{eq:commute}, and
  @{typ "_ pmf"} satisfies \eqref{eq:discard} and \eqref{eq:commute}.
  Equations \eqref{eq:discard} and \eqref{eq:duplicate} can be directly used as rewrite rules.%
  \footnote{%
    If they both hold, then \eqref{eq:commute} holds, too \cite{LochbihlerSchneider2016ITP}.
  }
  However, the simplifier does not handle \eqref{eq:commute} well because \eqref{eq:commute} is a
  higher-order permutative rewrite rule and ordered rewriting in the simplifier can only handle 
  first-order permutative rewrite rules.
  Consequently, when \eqref{eq:commute} is added to the simpset, the simplifier will loop.

  This AFP entry implements a simproc for the simplifier to simplify HOL expressions over commutative
  monads based on ordered rewriting.  This yields a decision procedure for equality of monadic 
  expressions in any (free) monad satisfying any of the laws (\ref{eq:discard}--\ref{eq:commute}).
  If further commutative operators show up in the HOL term, then the ordered rewrite system need not
  be confluent and the simproc only performs a best effort.  We do not know whether this general case
  can be solved by ordered rewriting as a complete solution would have to solve the graph isomorphism
  problem by term rewriting \cite{Basin1994IPL}.
\<close>

ML_file \<open>monad_rules.ML\<close>

subsection \<open>Usage\<close>

text \<open>
  The monad laws \eqref{eq:return:bind}, \eqref{eq:bind:return}, \eqref{eq:bind:assoc}, \eqref{eq:commute}
  must be registered with the attribute @{attribute monad_rule}. 
  The simproc does not need \eqref{eq:discard} and \eqref{eq:duplicate}, so these properties need not
  be registered, but can simply be added to the simpset if needed.
  The simproc is activated by including the bundle \<open>monad_normalisation\<close>.

  Additionally, distributivity laws for control operators like @{const If} and @{const case_nat} 
  specialised to \<open>\<bind>\<close> can be declared with the attribute @{attribute monad_distrib}.
  Then, the simproc will also commute computations over these control operators.

  The set of registered monad laws can be inspected with the command @{command print_monad_rules}.
\<close>

subsection \<open>Registration of the monads from the Isabelle/HOL library\<close>

lemmas [monad_rule] = Set.bind_bind

lemma set_bind_commute [monad_rule]:
  fixes A :: "'a set" and B :: "'b set"
  shows "A \<bind> (\<lambda>x. B \<bind> C x) = B \<bind> (\<lambda>y. A \<bind> (\<lambda>x. C x y))"
  unfolding Set.bind_def by auto

lemma set_return_bind [monad_rule]:
  fixes A :: "'a \<Rightarrow> 'b set"
  shows "{x} \<bind> A = A x"
  unfolding Set.bind_def by auto

lemma set_bind_return [monad_rule]:
  fixes A :: "'a set"
  shows "A \<bind> (\<lambda>x. {x}) = A"
  unfolding Set.bind_def by auto

lemmas [monad_rule] = Predicate.bind_bind Predicate.bind_single Predicate.single_bind

lemma predicate_bind_commute [monad_rule]:
  fixes A :: "'a Predicate.pred" and B :: "'b Predicate.pred"
  shows "A \<bind> (\<lambda>x. B \<bind> C x) = B \<bind> (\<lambda>y. A \<bind> (\<lambda>x. C x y))"
  by (intro pred_eqI) auto


lemmas [monad_rule] = Option.bind_assoc Option.bind_lunit Option.bind_runit

lemma option_bind_commute [monad_rule]:
  fixes A :: "'a option" and B :: "'b option"
  shows "A \<bind> (\<lambda>x. B \<bind> C x) = B \<bind> (\<lambda>y. A \<bind> (\<lambda>x. C x y))"
  by (cases A) auto

lemmas [monad_rule] =
  bind_assoc_pmf
  bind_commute_pmf
  bind_return_pmf
  bind_return_pmf'

lemmas [monad_rule] =
  bind_spmf_assoc
  bind_commute_spmf
  bind_return_spmf
  return_bind_spmf


subsection \<open>Distributive operators\<close>

lemma bind_if [monad_distrib]:
  "f A (\<lambda>x. if P then B x else C x) = (if P then f A B else f A C)"
by simp

lemma bind_case_prod [monad_distrib]:
  "f A (\<lambda>x. case y of (a,b) \<Rightarrow> B a b x) = (case y of (a,b) \<Rightarrow> f A (B a b))"
by (simp split: prod.split)

lemma bind_case_sum [monad_distrib]:
  "f A (\<lambda>x. case y of Inl a \<Rightarrow> B a x | Inr a \<Rightarrow> C a x) =
    (case y of Inl a \<Rightarrow> f A (B a) | Inr a \<Rightarrow> f A (C a))"
by (simp split: sum.split)

lemma bind_case_option [monad_distrib]:
  "f A (\<lambda>x. case y of Some a \<Rightarrow> B a x | None \<Rightarrow> C x) =
    (case y of Some a \<Rightarrow> f A (B a) | None \<Rightarrow> f A C)"
by (simp split: option.split)

lemma bind_case_list [monad_distrib]:
  "f A (\<lambda>x. case y of [] \<Rightarrow> B x | y # ys \<Rightarrow> C y ys x) = (case y of [] \<Rightarrow> f A B | y # ys \<Rightarrow> f A (C y ys))"
by (simp split: list.split)

lemma bind_case_nat [monad_distrib]:
  "f A (\<lambda>x. case y of 0 \<Rightarrow> B x | Suc n \<Rightarrow> C n x) = (case y of 0 \<Rightarrow> f A B | Suc n \<Rightarrow> f A (C n))"
by (simp split: nat.split)


subsection \<open>Setup of the normalisation simproc\<close>

ML_file \<open>monad_normalisation.ML\<close>

simproc_setup monad_normalisation ("f x y") = \<open>K Monad_Normalisation.normalise_step\<close>
declare [[simproc del: monad_normalisation]]

text \<open>
  The following bundle enables normalisation of monadic expressions by the simplifier.
  We use @{attribute monad_rule_internal} instead of \<open>monad_rule[simp]\<close> such that
  the theorems in @{thm [source] monad_rule} get dynamically added to the simpset instead of
  only those that are in there when the bundle is declared.
\<close>

bundle monad_normalisation = [[simproc add: monad_normalisation, monad_rule_internal]]

end
