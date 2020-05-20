(*  Title:       Deriving class instances for datatypes
    Author:      Christian Sternagel and René Thiemann  <christian.sternagel|rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann 
    License:     LGPL
*)
section \<open>Generating Hash-Functions\<close>

theory Hash_Generator
imports
  "../Generator_Aux"
  "../Derive_Manager"
  Collections.HashCode
begin

text \<open>As usual, in the generator we use a dedicated function to combine the results
  from evaluating the hash-function of the arguments of a constructor, to deliver
  the global hash-value.\<close>

fun hash_combine :: "hashcode list \<Rightarrow> hashcode list \<Rightarrow> hashcode" where
  "hash_combine [] [x] = x"
| "hash_combine (y # ys) (z # zs) = y * z + hash_combine ys zs"
| "hash_combine _ _ = 0"

text \<open>The first argument of @{const hash_combine} originates from evaluating the hash-function 
  on the arguments of a constructor, and the second argument of @{const hash_combine} will be static \emph{magic} numbers
  which are generated within the generator.\<close>

subsection \<open>Improved Code for Non-Lazy Languages\<close>

lemma hash_combine_unfold: 
  "hash_combine [] [x] = x"
  "hash_combine (y # ys) (z # zs) = y * z + hash_combine ys zs" 
  by auto

subsection \<open>The Generator\<close>

ML_file \<open>hash_generator.ML\<close>

end
