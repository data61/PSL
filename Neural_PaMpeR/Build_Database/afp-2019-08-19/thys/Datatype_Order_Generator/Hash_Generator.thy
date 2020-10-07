(*  Title:       Deriving class instances for datatypes
    Author:      René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  René Thiemann
    License:     LGPL
*)

(*
Copyright 2013 René Thiemann

This file is part of IsaFoR/CeTA.

IsaFoR/CeTA is free software: you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

IsaFoR/CeTA is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along
with IsaFoR/CeTA. If not, see <http://www.gnu.org/licenses/>.
*)

section \<open>Hash functions\<close>

theory Hash_Generator
imports 
  Collections.HashCode
  Derive_Aux
begin

subsection "Introduction"

text \<open>
The interface for hash-functions is defined in the class @{class hashable} which has been developed
as part of the Isabelle Collection Framework \cite{rbt}. It requires a hash-function
(@{const hashcode}), a bounded hash-function (@{const bounded_hashcode}),
and a default hash-table size (@{const def_hashmap_size}).

The @{const hashcode} function for each datatype are created by instantiating the recursors of that 
datatype appropriately. E.g., for \texttt{datatype 'a test = C1 'a 'a | C2 "'a test list"} 
we get a hash-function which is equivalent to 
\begin{verbatim}
hashcode (C1 a b) = c1 * hashcode a + c2 * hashcode b
hashcode (C2 Nil) = c3
hashcode (C2 (a # as)) = c4 * hashcode a + c5 * hashcode as
\end{verbatim}
where each \texttt{c$_{i}$} is a non-negative 32-bit number which is dependent on the
datatype name, the constructor name, and the occurrence of the argument (i.e., 
in the example \texttt{c1} and \texttt{c2} will usually be different numbers.)
These parameters are used in linear combination with prime numbers to hopefully
get some useful hash-function.

The @{const bounded_hashcode} functions are constructed in the same way, except that after each
arithmetic operation a modulo operation is performed.

Finally, the default hash-table size is just set to 10, following Java's default
hash-table constructor.
\<close>

subsection "Features and Limitations"

text \<open>
We get same limitation as for the order generator. 
For mutual recursive datatypes, only
for the first mentioned datatype the instantiations of the @{class hashable}-class are
derived.
\<close>

subsection "Installing the generator"

lemma hash_mod_lemma: "1 < (n :: nat) \<Longrightarrow> x mod n < n" by auto

ML_file \<open>hash_generator.ML\<close>

end
