(*  Title:      Jinja/J/State.thy

    Author:     Tobias Nipkow
    Copyright   2003 Technische Universitaet Muenchen
*)

section \<open>Program State\<close>

theory State imports "../Common/Exceptions" begin

type_synonym
  locals = "vname \<rightharpoonup> val"      \<comment> \<open>local vars, incl. params and ``this''\<close>
type_synonym
  state  = "heap \<times> locals"

definition hp :: "state \<Rightarrow> heap"
where
  "hp  \<equiv>  fst"
definition lcl :: "state \<Rightarrow> locals"
where
  "lcl  \<equiv>  snd"

(*<*)
declare hp_def[simp] lcl_def[simp]
(*>*)
end
