theory Monad
  imports Main "HOL-Library.Monad_Syntax"
begin

datatype ('M, 'a) state = State (runState: "'M \<Rightarrow> 'a \<times> 'M")
term 0 (**)

definition return :: "'a \<Rightarrow> ('M, 'a) state" where
  "return a \<equiv> State (\<lambda>M. (a, M))"
term 0 (**)

definition bind :: "('M, 'a) state \<Rightarrow> ('a \<Rightarrow> ('M, 'b) state) \<Rightarrow> ('M, 'b) state" where
  "bind s k = State (\<lambda>M. let (a, M') = runState s M in runState (k a) M')"
term 0 (**)

adhoc_overloading
  Monad_Syntax.bind bind

definition get :: "('M, 'M) state" where
  "get \<equiv> State (\<lambda>M. (M, M))"

definition put :: "'M \<Rightarrow> ('M, unit) state" where
  "put M \<equiv> State (\<lambda>_. ((), M))"
term 0 (**)

term 0 (**)
lemma bind_assoc:
  "((s::(_,_)state) \<bind> k0) \<bind> k1 = s \<bind> (\<lambda>a. k0 a \<bind> k1)"
  unfolding bind_def by (auto split: prod.split)

lemma left_identity:
  "return v \<bind> k = k v"
  unfolding return_def bind_def by simp

lemma right_identity:
  "s \<bind> return = s"
  unfolding return_def bind_def by simp

lemma runState_return:
  "runState (return x) M = (x, M)"
  unfolding return_def by simp
end
