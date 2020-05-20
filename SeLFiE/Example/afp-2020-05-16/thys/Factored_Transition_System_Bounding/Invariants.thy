theory Invariants
  imports Main "FactoredSystem"
begin

definition fdom :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set" where 
  "fdom f \<equiv> {x. \<exists>y. f x = y}"

\<comment> \<open>TODO function domain for total function in Isabelle/HOL?\<close>
\<comment> \<open>TODO why is fm total? Shouldn't it be partial and thus needing the the premise `fm x = Some True` instead of just `fm x`?\<close>
definition invariant :: "('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "invariant fm \<equiv> (\<forall>x. (x \<in> fdom fm \<and> fm x) \<longrightarrow> False) \<and> (\<exists>x. x \<in> fdom fm \<and> fm x)"

end