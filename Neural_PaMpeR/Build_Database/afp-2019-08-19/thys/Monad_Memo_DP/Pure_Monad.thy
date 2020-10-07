section \<open>Monadification\<close>

subsection \<open>Monads\<close>

theory Pure_Monad
  imports Main
begin

definition Wrap :: "'a \<Rightarrow> 'a" where
  "Wrap x \<equiv> x"

definition App :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" where
  "App f \<equiv> f"

lemma Wrap_App_Wrap:
  "App (Wrap f) (Wrap x) \<equiv> f x"
  unfolding App_def Wrap_def .


end
