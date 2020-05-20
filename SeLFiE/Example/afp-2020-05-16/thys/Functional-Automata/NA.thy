(*  Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

section "Nondeterministic automata"

theory NA
imports AutoProj
begin

type_synonym ('a,'s) na = "'s * ('a \<Rightarrow> 's \<Rightarrow> 's set) * ('s \<Rightarrow> bool)"

primrec delta :: "('a,'s)na \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> 's set" where
"delta A []    p = {p}" |
"delta A (a#w) p = Union(delta A w ` next A a p)"

definition
 accepts :: "('a,'s)na \<Rightarrow> 'a list \<Rightarrow> bool" where
"accepts A w = (\<exists>q \<in> delta A w (start A). fin A q)"

definition
 step :: "('a,'s)na \<Rightarrow> 'a \<Rightarrow> ('s * 's)set" where
"step A a = {(p,q) . q : next A a p}"

primrec steps :: "('a,'s)na \<Rightarrow> 'a list \<Rightarrow> ('s * 's)set" where
"steps A [] = Id" |
"steps A (a#w) = step A a  O  steps A w"

lemma steps_append[simp]:
 "steps A (v@w) = steps A v  O  steps A w"
by(induct v, simp_all add:O_assoc)

lemma in_steps_append[iff]:
  "(p,r) : steps A (v@w) = ((p,r) : (steps A v O steps A w))"
apply(rule steps_append[THEN equalityE])
apply blast
done

lemma delta_conv_steps: "\<And>p. delta A w p = {q. (p,q) : steps A w}"
by(induct w)(auto simp:step_def)

lemma accepts_conv_steps:
 "accepts A w = (\<exists>q. (start A,q) \<in> steps A w \<and> fin A q)"
by(simp add: delta_conv_steps accepts_def)

abbreviation
  Cons_syn :: "'a \<Rightarrow> 'a list set \<Rightarrow> 'a list set" (infixr "##" 65) where
  "x ## S \<equiv> Cons x ` S"

end
