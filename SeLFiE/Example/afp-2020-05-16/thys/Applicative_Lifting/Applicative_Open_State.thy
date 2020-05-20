(* Author: Joshua Schneider, ETH Zurich *)

subsection \<open>Open state monad\<close>

theory Applicative_Open_State imports
  Applicative
  "HOL-Library.Adhoc_Overloading"
begin

type_synonym ('a, 's) state = "'s \<Rightarrow> 'a \<times> 's"

definition "ap_state f x = (\<lambda>s. case f s of (g, s') \<Rightarrow> case x s' of (y, s'') \<Rightarrow> (g y, s''))"

abbreviation (input) "pure_state \<equiv> Pair"

adhoc_overloading Applicative.ap ap_state

applicative state
for
  pure: pure_state
  ap: "ap_state :: ('a \<Rightarrow> 'b, 's) state \<Rightarrow> ('a, 's) state \<Rightarrow> ('b, 's) state"
unfolding ap_state_def
by (auto split: prod.split)

end
