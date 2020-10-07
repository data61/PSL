theory C2
imports "HOL-Algebra.Group"
begin

section \<open>The group C2\<close>

text \<open>
The two-element group is defined over the set of boolean values. This allows to 
use the equality of boolean values as the group operation.
\<close>

definition "C2"
  where "C2 = \<lparr> carrier = UNIV, mult = (=), one = True \<rparr>"

lemma [simp]: "(\<otimes>\<^bsub>C2\<^esub>) = (=)"
  unfolding C2_def by simp

lemma [simp]: "\<one>\<^bsub>C2\<^esub> = True"
  unfolding C2_def by simp

lemma [simp]: "carrier C2 = UNIV"
  unfolding C2_def by simp

lemma C2_is_group: "group C2"
  unfolding C2_def
  by (rule groupI, auto simp add:Units_def)

end
