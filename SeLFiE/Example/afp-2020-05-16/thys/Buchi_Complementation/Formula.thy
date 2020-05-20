section \<open>Boolean Formulae\<close>

theory Formula
imports Main
begin

  datatype 'a formula =
    False |
    True |
    Variable 'a |
    Negation "'a formula" |
    Conjunction "'a formula" "'a formula" |
    Disjunction "'a formula" "'a formula"

  primrec satisfies :: "'a set \<Rightarrow> 'a formula \<Rightarrow> bool" where
    "satisfies A False \<longleftrightarrow> HOL.False" |
    "satisfies A True \<longleftrightarrow> HOL.True" |
    "satisfies A (Variable a) \<longleftrightarrow> a \<in> A" |
    "satisfies A (Negation x) \<longleftrightarrow> \<not> satisfies A x" |
    "satisfies A (Conjunction x y) \<longleftrightarrow> satisfies A x \<and> satisfies A y" |
    "satisfies A (Disjunction x y) \<longleftrightarrow> satisfies A x \<or> satisfies A y"

end