(*  Title:       CoreC++

    Author:      Tobias Nipkow, Daniel Wasserrab 
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>

    Extracted from the Jinja theory Common/TypeRel.thy by Tobias Nipkow 
*)

section \<open>The subtype relation\<close>

theory TypeRel imports SubObj begin


inductive
  widen   :: "prog \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> _ \<le> _"   [71,71,71] 70)
  for P :: prog
where
  widen_refl[iff]: "P \<turnstile> T \<le> T"
| widen_subcls:    "P \<turnstile> Path C to D unique \<Longrightarrow> P \<turnstile> Class C \<le> Class D"
| widen_null[iff]: "P \<turnstile> NT \<le> Class C"

abbreviation
  widens :: "prog \<Rightarrow> ty list \<Rightarrow> ty list \<Rightarrow> bool"
    ("_ \<turnstile> _ [\<le>] _" [71,71,71] 70) where
  "widens P Ts Ts' \<equiv> list_all2 (widen P) Ts Ts'"

inductive_simps [iff]:
  "P \<turnstile> T \<le> Void"
  "P \<turnstile> T \<le> Boolean"
  "P \<turnstile> T \<le> Integer"
  "P \<turnstile> Void \<le> T"
  "P \<turnstile> Boolean \<le> T"
  "P \<turnstile> Integer \<le> T"
  "P \<turnstile> T \<le> NT"

lemmas widens_refl [iff] = list_all2_refl [of "widen P", OF widen_refl] for P
lemmas widens_Cons [iff] = list_all2_Cons1 [of "widen P"] for P

end
