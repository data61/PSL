(*  Title:      Sort.thy
    Author:     Danijela Petrovi\'c, Facylty of Mathematics, University of Belgrade *)

section \<open>Locale Sort\<close>

theory Sort
imports Main 
  "HOL-Library.Permutation"
begin

text \<open>
First, we start from the definition of sorting algorithm. {\em What
  are the basic properties that any sorting algorithm must satisfy? }
There are two
basic features any sorting algorithm must satisfy:
\begin{itemize}
\item The elements of sorted array must be in some order,
  e.g. ascending or descending order. In this paper we are sorting in
  ascending order.
  $$sorted\ (sort\ \ l)$$

\item The algorithm does not change or delete elements of the given
  array, e.g. the sorted array is the permutation of the input
  array. 
  $$sort\ l\ <\sim \sim>\ l$$
\end{itemize}

\<close>

locale Sort =
  fixes sort :: "'a::linorder list \<Rightarrow> 'a list"
  assumes sorted: "sorted (sort l)"
  assumes permutation: "sort l <~~> l"

end
