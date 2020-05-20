section \<open>Two approaches that failed \label{sec:two-approaches-that}\<close>

(*<*) theory Failure imports RealRandVar begin (*>*)

text\<open>
Defining Lebesgue integration can be quite involved, judging by the
process in \ref{sec:stepwise-approach} that imitates Bauer's way
\cite{Bauer}.  So it is quite tempting to try cutting a corner. The
following two alternative approaches back up my experience that this
almost never pays in formalization. The theory that seems most complex
at first sight is often the one that is closest to formal reasoning
and deliberately avoids ``hand-waving''.
\<close>

subsection \<open>A closed expression \label{sec:closed-expression}\<close>

text \<open>
  In contrast, Billingsley's definition \cite[p.~172]{Billingsley86} is
  strikingly short. For nonnegative measurable functions $f$:

  \begin{quote}
  
  $\int f d\mu = \mathit{sup} \sum_i \big[ \mathit{inf}_{\omega \in A_i} f(w) \big] \mu(A_i).$
  
  The supremum here extends over all finite decompositions $\{A_i\}$ of
  $\Omega$ into $\mathcal{F}$-sets.\footnote{The $\mathcal{F}$-sets are just the measurable sets of a measure
  space.}

  \end{quote}
  
  Like the definition, the proofs of the essential properties are also
  rather
  short, about three pages in the textbook for almost all the theorems
  in \ref{sec:stepwise-approach}; and a proof of uniqueness is obsolete
  for a closed expression like this. Therefore, I found this approach
  quite tempting. It turns out, however, that it is unfortunately not
  well suited for formalization, at least with the background we use.
  
  A complication shared by all possible styles of definition is the lack
  of infinite values in our theory, combined with the lack of partial
  functions in HOL. Like the sum operator in
  \ref{sec:measure-spaces}, the integral has to be defined
  indirectly. The classical way to do this employs predicates, invoking \<open>\<epsilon>\<close>
  to choose the value that satisfies the condition:

  \<open>\<integral> f dM \<equiv> (\<epsilon> i. is_integral M f i)\<close>

  To sensibly apply this principle, the predicate has to be \<open>\<epsilon>\<close>-free to supply the information if the integral is
  defined or not. Now the above definition contains up to three additional
  \<open>\<epsilon>\<close> when formalized naively in HOL, namely in the supremum,
  infimum and sum operators. The sum is over a finite set, so it can
  be replaced by a total function. For nonnegative functions, the
  infimum can also be shown to exist everywhere, but, like the
  supremum,  must
  itself be replaced by a predicate. 

  Also note that predicates require a proof of uniqueness, thus losing
  the prime advantage of a closed formula anyway. In this case,
  uniqueness can be reduced to uniqueness of the supremum/infimum. The
  problem is that neither suprema nor infima come predefined in
  Isabelle/Isar as of yet. It is an easy task to make up for this ---
  and I did --- but a much harder one to establish all the properties
  needed for reasoning with the defined entities.

  A lot of such reasoning is necessary to deduce from the above definition
  (or a formal version of it, as just outlined) the basic behavior of
  integration, which includes additivity, monotonicity and especially the
  integral of simple functions. It turns out that the brevity of the
  proofs in the textbook stems from a severely informal style that
  assumes ample background knowledge. Formalizing all this knowledge
  started to become overwhelming when the idea of a contrarian approach
  emerged.
\<close>

subsection \<open>A one-step inductive definition \label{sec:one-step}\<close>

text \<open>
  This idea was sparked by the following note: ``(\ldots) the integral
  is uniquely determined by certain simple properties it is natural to
  require of it'' \cite[p.~175]{Billingsley86}. Billingsley goes on
  discussing exactly those properties that are so hard to derive
  from his definition. So why not simply define integration using
  these properties? That is the gist of an inductive set definition, like
  the one we have seen in \ref{sec:sigma}. This time a functional operator is
  to be defined, but it can be represented as a set of pairs, where
  the first component is the function and the second its integral.
  To cut a long story short, here is the definition.\<close>

inductive_set
  integral_set:: "('a set set * ('a set \<Rightarrow> real)) \<Rightarrow> (('a \<Rightarrow> real) * real) set"
  for M :: "'a set set * ('a set \<Rightarrow> real)"
  where
    char: "\<lbrakk>f = \<chi> A; A \<in> measurable_sets M\<rbrakk> \<Longrightarrow> (f,measure M A) \<in> integral_set M"
  | add: "\<lbrakk>f = (\<lambda>w. g w + h w); (g,x) \<in> integral_set M; (h,y) \<in> integral_set M\<rbrakk> 
    \<Longrightarrow> (f,(x + y)) \<in> integral_set M"
  | times: "\<lbrakk>f = (\<lambda>w. a*g w); (g,x) \<in> integral_set M\<rbrakk> \<Longrightarrow> (f,a*x) \<in> integral_set M"
  | mon_conv: "\<lbrakk>u\<up>f; \<And>n. (u n, x n) \<in> integral_set M; x\<up>y\<rbrakk> 
    \<Longrightarrow> (f,y) \<in> integral_set M"

  text \<open>The technique is also encountered in the \<open>Finite_Set\<close> theory from the Isabelle library. It is used there
    to define the \<open>sum\<close> function, which calculates a sum
    indexed over a finite set and is employed in
    \ref{sec:stepwise-approach}. The definition here is much more
    intricate though. 

    An obvious advantage of this approach is that almost all
    important properties are gained without effort. The
    introduction rule \<open>mon_conv\<close> corresponds to what is known as
    the Monotone Convergence Theorem in scientific literature; negative functions are also provided for via
    the \<open>times\<close> rule. 
    To be precise,
    there is exactly one important theorem missing ---
    uniqueness. That is, every function appears in at most one pair. 
    
    From uniqueness together with the introduction rules, all the
    other statements about integration, monotonicity for example,
    could be derived. On the other hand, monotonicity implies
    uniqueness. Much to my regret, none of these two could be proven.
    The proof would basically amount to a double induction to show
    that an integral gained via one rule is the same when derived by
    another. A lot of effort was spent trying to strengthen the
    induction hypothesis or reduce the goal to a simpler case. All of
    this was in vain though, and it seems that the hypothesis would
    have to be strengthened as far as to include the concept of
    integration in the first place, which in a way defeats the
    advantages of the approach.\<close>
    

  (*<*)end  (*>*)
