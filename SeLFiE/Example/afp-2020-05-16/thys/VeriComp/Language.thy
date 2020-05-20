section \<open>The Static Representation of a Language\<close>

theory Language
  imports Semantics
begin

locale language =
  semantics step final
  for
    step :: "'state \<Rightarrow> 'state \<Rightarrow> bool" and
    final :: "'state \<Rightarrow> bool" +
  fixes
    load :: "'prog \<Rightarrow> 'state option"

context language begin

text \<open>
The language locale represents the concrete program representation (type variable @{typ 'prog}), which can be transformed into a program state (type variable @{typ 'state}) by the @{term load } function.
The set of initial states of the transition system is implicitly defined by the codomain of @{term load}.
\<close>

end

end