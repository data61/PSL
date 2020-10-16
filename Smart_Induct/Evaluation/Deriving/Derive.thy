(*  Title:       Deriving class instances for datatypes
    Author:      Christian Sternagel and René Thiemann  <christian.sternagel|rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann 
    License:     LGPL
*)
section \<open>Loading Existing Derive-Commands\<close>
theory Derive
imports 
  "Comparator_Generator/Compare_Instances"
  "Equality_Generator/Equality_Instances"
  "Hash_Generator/Hash_Instances"
  "Countable_Generator/Countable_Generator"
begin

text\<open>
We just load the commands to derive comparators, equality-functions, hash-functions, and the
command to show that a datatype is countable, so that now all of them are available.
There are further generators available in the AFP entries Containers and Show.
\<close>

print_derives

end
