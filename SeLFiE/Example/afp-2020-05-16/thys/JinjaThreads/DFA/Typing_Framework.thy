(*  Title:      HOL/MicroJava/BV/Typing_Framework.thy
    Author:     Tobias Nipkow
    Copyright   2000 TUM
*)

section \<open>Typing and Dataflow Analysis Framework\<close>

theory Typing_Framework
imports
  Semilattices
begin

text \<open>
  The relationship between dataflow analysis and a welltyped-instruction predicate. 
\<close>
type_synonym
  's step_type = "nat \<Rightarrow> 's \<Rightarrow> (nat \<times> 's) list"

definition stable :: "'s ord \<Rightarrow> 's step_type \<Rightarrow> 's list \<Rightarrow> nat \<Rightarrow> bool"
where
  "stable r step \<tau>s p \<longleftrightarrow> (\<forall>(q,\<tau>) \<in> set (step p (\<tau>s!p)). \<tau> \<sqsubseteq>\<^sub>r \<tau>s!q)"

definition stables :: "'s ord \<Rightarrow> 's step_type \<Rightarrow> 's list \<Rightarrow> bool"
where
  "stables r step \<tau>s \<longleftrightarrow> (\<forall>p < size \<tau>s. stable r step \<tau>s p)"

definition wt_step :: "'s ord \<Rightarrow> 's \<Rightarrow> 's step_type \<Rightarrow> 's list \<Rightarrow> bool"
where
  "wt_step r T step \<tau>s \<longleftrightarrow> (\<forall>p<size \<tau>s. \<tau>s!p \<noteq> T \<and> stable r step \<tau>s p)"

definition is_bcv :: "'s ord \<Rightarrow> 's \<Rightarrow> 's step_type \<Rightarrow> nat \<Rightarrow> 's set \<Rightarrow> ('s list \<Rightarrow> 's list) \<Rightarrow> bool"
where
  "is_bcv r T step n A bcv \<longleftrightarrow> (\<forall>\<tau>s\<^sub>0 \<in> list n A.
  (\<forall>p<n. (bcv \<tau>s\<^sub>0)!p \<noteq> T) = (\<exists>\<tau>s \<in> list n A. \<tau>s\<^sub>0 [\<sqsubseteq>\<^sub>r] \<tau>s \<and> wt_step r T step \<tau>s))"

end
