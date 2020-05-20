theory Entailment
imports Main "HOL-Library.FSet"
begin

type_synonym 'form entailment = "('form fset \<times> 'form)"

abbreviation entails :: "'form fset \<Rightarrow> 'form \<Rightarrow> 'form entailment" (infix "\<turnstile>" 50)
  where "a \<turnstile> c \<equiv> (a, c)"

fun add_ctxt :: "'form fset \<Rightarrow> 'form entailment \<Rightarrow> 'form entailment" where
  "add_ctxt \<Delta> (\<Gamma> \<turnstile> c) = (\<Gamma> |\<union>| \<Delta> \<turnstile> c)"

end
