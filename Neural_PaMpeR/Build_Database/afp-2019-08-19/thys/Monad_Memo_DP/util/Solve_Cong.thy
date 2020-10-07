subsection \<open>Setup for the Heap Monad\<close>

theory Solve_Cong
  imports Main "HOL-Eisbach.Eisbach"
begin

text \<open>Method for solving trivial equalities with congruence reasoning\<close>

named_theorems cong_rules

method solve_cong methods solve =
  rule HOL.refl |
  rule cong_rules; solve_cong solve |
  solve; fail

end
