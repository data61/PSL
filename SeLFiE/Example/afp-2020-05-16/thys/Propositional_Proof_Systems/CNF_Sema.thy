theory CNF_Sema
imports CNF
begin

(* 'a \<Rightarrow> bool is a valuation, but I do not want to include Sema just for that\<dots> *)
primrec lit_semantics :: "('a \<Rightarrow> bool) \<Rightarrow> 'a literal \<Rightarrow> bool" where
"lit_semantics \<A> (k\<^sup>+) = \<A> k" |
"lit_semantics \<A> (k\<inverse>) = (\<not>\<A> k)"
case_of_simps lit_semantics_cases: lit_semantics.simps
definition clause_semantics where
  "clause_semantics \<A> C \<equiv> \<exists>L \<in> C. lit_semantics \<A> L"
definition cnf_semantics where
  "cnf_semantics \<A> S \<equiv> \<forall>C \<in> S. clause_semantics \<A> C"


end
