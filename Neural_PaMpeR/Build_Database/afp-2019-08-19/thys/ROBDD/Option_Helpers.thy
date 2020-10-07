section\<open>Option Helpers\<close>
text\<open>These definitions were contributed by Peter Lammich.\<close>
theory Option_Helpers
imports Main "HOL-Library.Monad_Syntax"
begin

primrec oassert :: "bool \<Rightarrow> unit option" where
  "oassert True = Some ()" | "oassert False = None"

lemma oassert_iff[simp]: 
  "oassert \<Phi> = Some x \<longleftrightarrow> \<Phi>" 
  "oassert \<Phi> = None \<longleftrightarrow> \<not>\<Phi>"  
  by (cases \<Phi>) auto

text\<open>The idea is that we want the result of some computation to be @{term "Some v"} and the contents of @{term v} to satisfy some property @{term Q}.\<close>

primrec ospec :: "('a option) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "ospec None _ = False"
| "ospec (Some v) Q = Q v"

named_theorems ospec_rules

lemma oreturn_rule[ospec_rules]: "\<lbrakk> P r \<rbrakk> \<Longrightarrow> ospec (Some r) P" by simp

lemma obind_rule[ospec_rules]: "\<lbrakk> ospec m Q; \<And>r. Q r \<Longrightarrow> ospec (f r) P \<rbrakk> \<Longrightarrow> ospec (m \<bind> f) P"
  apply (cases m)
   apply (auto split: Option.bind_splits)
  done

lemma ospec_alt: "ospec m P = (case m of None \<Rightarrow> False | Some x \<Rightarrow> P x)"
  by (auto split: option.splits)

lemma ospec_bind_simp: "ospec (m \<bind> f) P \<longleftrightarrow> (ospec m (\<lambda>r. ospec (f r) P))"
  apply (cases m)
   apply (auto split: Option.bind_splits)
  done

lemma ospec_cons: 
  assumes "ospec m Q"
  assumes "\<And>r. Q r \<Longrightarrow> P r"
  shows "ospec m P"
  using assms by (cases m) auto

lemma oreturn_synth: "ospec (Some x) (\<lambda>r. r=x)" by simp

lemma ospecD: "ospec x P \<Longrightarrow> x = Some y \<Longrightarrow> P y" by simp
lemma ospecD2: "ospec x P \<Longrightarrow> \<exists>y. x = Some y \<and> P y" by(cases x) simp_all

end
