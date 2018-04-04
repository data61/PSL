section {* Sequences as Lists *}

theory Sequences
imports Main
begin

locale Sequences 
begin

text {* We reverse the order of application of @{term "op #"} and 
  @{term "op @"} because it we think that it is easier to think of sequences as growing 
  to the right. *}
no_notation Cons (infixr "#" 65)
abbreviation Append  (infixl "#" 65)
  where "Append xs x \<equiv> Cons x xs"
no_notation append (infixr "@" 65)
abbreviation Concat  (infixl "@" 65)
  where "Concat xs ys \<equiv> append ys xs"

end

end
