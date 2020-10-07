section \<open>Sequences as Lists\<close>

theory Sequences
imports Main
begin

locale Sequences 
begin

text \<open>We reverse the order of application of @{term "(#)"} and 
  @{term "(@)"} because it we think that it is easier to think of sequences as growing 
  to the right.\<close>
no_notation Cons (infixr "#" 65)
abbreviation Append  (infixl "#" 65)
  where "Append xs x \<equiv> Cons x xs"
no_notation append (infixr "@" 65)
abbreviation Concat  (infixl "@" 65)
  where "Concat xs ys \<equiv> append ys xs"

end

end
