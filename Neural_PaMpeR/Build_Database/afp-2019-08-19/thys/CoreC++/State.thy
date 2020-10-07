(*  Title:       CoreC++
    Author:      Tobias Nipkow
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>
*)

section \<open>Program State\<close>

theory State imports Exceptions begin

type_synonym
  locals = "vname \<rightharpoonup> val"      \<comment> \<open>local vars, incl. params and ``this''\<close>
type_synonym
  state  = "heap \<times> locals"

definition hp :: "state \<Rightarrow> heap" where
  "hp  \<equiv>  fst"

definition lcl :: "state \<Rightarrow> locals" where
  "lcl  \<equiv>  snd"

declare hp_def[simp] lcl_def[simp]

end
