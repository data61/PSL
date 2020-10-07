(*  Author: Tobias Nipkow  *)

section \<open>Combining Computations With All Completeness Proofs\<close>

theory Completeness
imports ArchComp "Flyspeck-Tame.Relative_Completeness"
begin

global_interpretation relative?: archive_by_computation
by standard (fact pre_iso_test3 pre_iso_test4 pre_iso_test5 pre_iso_test6
  same3 same4 same5 same6)+

theorem TameEnum_Archive:  "fgraph ` TameEnum \<subseteq>\<^sub>\<simeq> Archive"
by (fact TameEnum_Archive)

lemma TameEnum_comp:
assumes "Seed\<^bsub>p\<^esub> [next_plane\<^bsub>p\<^esub>]\<rightarrow>* g" and "final g" and "tame g"
shows "Seed\<^bsub>p\<^esub> [next_tame\<^bsub>p\<^esub>]\<rightarrow>* g"
using assms by (fact TameEnum_comp)

lemma tame5:
assumes g: "Seed\<^bsub>p\<^esub> [next_plane0\<^bsub>p\<^esub>]\<rightarrow>* g" and "final g" and "tame g"
shows "p \<le> 3"
using assms by (fact tame5)

theorem completeness:
assumes "g \<in> PlaneGraphs" and "tame g" shows "fgraph g \<in>\<^sub>\<simeq> Archive"
using assms by (fact completeness)

end
