(*  Author:     Gertrud Bauer, Tobias Nipkow
*)

section \<open>Neglectable Final Graphs\<close>

theory TameEnum
imports Generator
begin

definition is_tame :: "graph \<Rightarrow> bool" where
"is_tame g  \<equiv>  tame10 g \<and> tame11a g \<and> tame12o g \<and> is_tame13a g"

definition next_tame :: "nat \<Rightarrow> graph \<Rightarrow> graph list" ("next'_tame\<^bsub>_\<^esub>") where
"next_tame\<^bsub>p\<^esub> \<equiv> filter (\<lambda>g. \<not> final g \<or> is_tame g) \<circ> next_tame0\<^bsub>p\<^esub>"

definition TameEnumP :: "nat \<Rightarrow> graph set" ("TameEnum\<^bsub>_\<^esub>") where
"TameEnum\<^bsub>p\<^esub> \<equiv> {g. Seed\<^bsub>p\<^esub> [next_tame\<^bsub>p\<^esub>]\<rightarrow>* g \<and> final g}"

definition TameEnum :: "graph set" where
"TameEnum \<equiv> \<Union>p\<le>3. TameEnum\<^bsub>p\<^esub>"

end
