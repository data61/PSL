(* Author: Lars Hupel, TU München *)

subsection \<open>State monad\<close>

theory Applicative_State
imports
  Applicative
  "HOL-Library.State_Monad"
begin

applicative state for
  pure: State_Monad.return
  ap: State_Monad.ap
unfolding State_Monad.return_def State_Monad.ap_def
by (auto split: prod.splits)

end
