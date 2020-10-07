(*
Title: Strong-Security
Authors: Sylvia Grewe, Alexander Lux, Heiko Mantel, Jens Sauer
*)
theory Types
imports Main
begin

\<comment> \<open>type parameters:\<close>
\<comment> \<open>'exp: expressions (arithmetic, boolean...)\<close>
\<comment> \<open>'val: values\<close>
\<comment> \<open>'id: identifier names\<close>
\<comment> \<open>'com: commands\<close>
\<comment> \<open>'d: domains\<close>

text\<open>This is a collection of type synonyms. Note that not all of these type synonyms are 
  used within Strong-Security - some are used in WHATandWHERE-Security.\<close>

\<comment> \<open>type for memory states - map ids to values\<close>
type_synonym ('id, 'val) State = "'id \<Rightarrow> 'val"

\<comment> \<open>type for evaluation functions mapping expressions to a values depending on a state\<close>
type_synonym ('exp, 'id, 'val) Evalfunction = 
  "'exp \<Rightarrow> ('id, 'val) State \<Rightarrow> 'val"

\<comment> \<open>define configurations with threads as pair of commands and states\<close>
type_synonym ('id, 'val, 'com) TConfig = "'com \<times> ('id, 'val) State"

\<comment> \<open>define configurations with thread pools as pair of command lists (thread pool) and states\<close>
type_synonym ('id, 'val, 'com) TPConfig = 
  "('com list) \<times> ('id, 'val) State"

\<comment> \<open>type for program states (including the set of commands and a symbol for terminating - None)\<close>
type_synonym 'com ProgramState = "'com option"

\<comment> \<open>type for configurations with program states\<close>
type_synonym ('id, 'val, 'com) PSConfig = 
  "'com ProgramState \<times> ('id, 'val) State"

\<comment> \<open>type for labels with a list of spawned threads\<close>
type_synonym 'com Label = "'com list"

\<comment> \<open>type for step relations from single commands to a program state, with a label\<close>
type_synonym ('exp, 'id, 'val, 'com) TLSteps = "
  (('id, 'val, 'com) TConfig \<times> 'com Label 
    \<times> ('id, 'val, 'com) PSConfig) set"

\<comment> \<open>curried version of previously defined type\<close>
type_synonym ('exp, 'id, 'val, 'com) TLSteps_curry =
"'com \<Rightarrow> ('id, 'val) State \<Rightarrow> 'com Label \<Rightarrow> 'com ProgramState 
  \<Rightarrow> ('id, 'val) State \<Rightarrow> bool"

\<comment> \<open>type for step relations from thread pools to thread pools\<close>
type_synonym ('exp, 'id, 'val, 'com) TPSteps = "
  (('id, 'val, 'com) TPConfig \<times> ('id, 'val, 'com) TPConfig) set"

\<comment> \<open>curried version of previously defined type\<close>
type_synonym ('exp, 'id, 'val, 'com) TPSteps_curry =
"'com list \<Rightarrow> ('id, 'val) State \<Rightarrow> 'com list \<Rightarrow> ('id, 'val) State \<Rightarrow> bool"

\<comment> \<open>define type of step relations for single threads to thread pools\<close>
type_synonym ('exp, 'id, 'val, 'com) TSteps = 
  "(('id, 'val, 'com) TConfig \<times> ('id, 'val, 'com) TPConfig) set"

\<comment> \<open>define the same type as TSteps, but in a curried version (allowing syntax abbreviations)\<close>
type_synonym ('exp, 'id, 'val, 'com) TSteps_curry =
"'com \<Rightarrow> ('id, 'val) State \<Rightarrow> 'com list \<Rightarrow> ('id, 'val) State \<Rightarrow> bool"

\<comment> \<open>type for simple domain assignments; 'd has to be an instance of order (partial order\<close>
type_synonym ('id, 'd) DomainAssignment = "'id \<Rightarrow> 'd::order"

type_synonym 'com Bisimulation_type = "(('com list) \<times> ('com list)) set"

\<comment> \<open>type for escape hatches\<close>
type_synonym ('d, 'exp) Hatch = "'d \<times> 'exp"

\<comment> \<open>type for sets of escape hatches\<close>
type_synonym ('d, 'exp) Hatches = "(('d, 'exp) Hatch) set"

\<comment> \<open>type for local escape hatches\<close>
type_synonym ('d, 'exp) lHatch = "'d \<times> 'exp \<times> nat"

\<comment> \<open>type for sets of local escape hatches\<close>
type_synonym ('d, 'exp) lHatches = "(('d, 'exp) lHatch) set"


end
