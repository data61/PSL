(*  Title:       Deriving class instances for datatypes
    Author:      Christian Sternagel and René Thiemann  <christian.sternagel|rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann 
    License:     LGPL
*)
subsection \<open>Compare Generator\<close>

theory Compare_Generator
imports 
  Comparator_Generator
  Compare
begin

text \<open>We provide a generator which takes the comparators of the comparator generator
  to synthesize suitable @{const compare}-functions from the @{class compare}-class.

One can further also use these comparison functions to derive an instance of the
@{class compare_order}-class, and therefore also for @{class linorder}. In total, we provide the three
\<open>derive\<close>-methods where the example type @{type prod} can be replaced by any other datatype.

\begin{itemize}
\item \<open>derive compare prod\<close> creates an instance @{type prod} :: (@{class compare}, @{class compare}) @{class compare}.
\item \<open>derive compare_order prod\<close> creates an instance @{type prod} :: (@{class compare}, @{class compare}) @{class compare_order}.
\item \<open>derive linorder prod\<close> creates an instance @{type prod} :: (@{class linorder}, @{class linorder}) @{class linorder}.
\end{itemize}

Usually, the use of \<open>derive linorder\<close> is not recommended if there are comparators available:
Internally, the linear orders will directly be converted into comparators, so a direct use of the
comparators will result in more efficient generated code. This command is mainly provided as a convenience method
where comparators are not yet present. For example, at the time of writing, the Container Framework
has partly been adapted to internally use comparators, whereas in other AFP-entries, we did not
integrate comparators.
\<close>

lemma linorder_axiomsD: assumes "class.linorder le lt"
  shows 
  "lt x y = (le x y \<and> \<not> le y x)" (is ?a)
  "le x x" (is ?b)
  "le x y \<Longrightarrow> le y z \<Longrightarrow> le x z" (is "?c1 \<Longrightarrow> ?c2 \<Longrightarrow> ?c3") 
  "le x y \<Longrightarrow> le y x \<Longrightarrow> x = y" (is "?d1 \<Longrightarrow> ?d2 \<Longrightarrow> ?d3")
  "le x y \<or> le y x" (is ?e)
proof -
  interpret linorder le lt by fact
  show ?a ?b "?c1 \<Longrightarrow> ?c2 \<Longrightarrow> ?c3" "?d1 \<Longrightarrow> ?d2 \<Longrightarrow> ?d3" ?e by auto
qed
 
named_theorems compare_simps "simp theorems to derive \"compare = comparator_of\""

ML_file \<open>compare_generator.ML\<close>

end
