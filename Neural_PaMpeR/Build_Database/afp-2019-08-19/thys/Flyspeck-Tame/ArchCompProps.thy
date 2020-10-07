(*  Author: Tobias Nipkow  *)

section "Completeness of Archive Test"

theory ArchCompProps
imports TameEnumProps ArchCompAux
begin
lemma mgp_pre_iso_test: "minGraphProps g \<Longrightarrow> pre_iso_test(fgraph g)"
apply(simp add:pre_iso_test_def fgraph_def image_def)
apply(rule conjI) apply(blast dest: mgp_vertices_nonempty[symmetric])
apply(rule conjI) apply(blast intro:minGraphProps)
apply(drule minGraphProps11)
apply(simp add:normFaces_def normFace_def verticesFrom_def minVertex_def
               rotate_min_def o_def)
done

corollary iso_test_correct:
 "\<lbrakk> pre_iso_test Fs\<^sub>1; pre_iso_test Fs\<^sub>2 \<rbrakk> \<Longrightarrow>
  iso_test Fs\<^sub>1 Fs\<^sub>2 = (Fs\<^sub>1 \<simeq> Fs\<^sub>2)"
by(simp add:pre_iso_test_def iso_correct inj_on_rotate_min_iff[symmetric]
            distinct_map nof_vertices_def length_remdups_concat)

lemma trie_all_eq_set_of_trie:
  "invar_trie t \<Longrightarrow> all_trie (list_all P) t = (\<forall>v \<in> set_tries t. P v)"
by(simp add: all_trie_eq_ran set_tries_eq_ran)

lemma samet_imp_iso_seteq:
assumes pre1: "\<And>gs g. gsopt = Some gs \<Longrightarrow> g \<in> set_tries gs \<Longrightarrow> pre_iso_test g"
and pre2: "\<And>g. g \<in> set arch \<Longrightarrow> pre_iso_test g"
and inv: "\<And>gs. gsopt = Some gs \<Longrightarrow> invar_trie gs"
and same: "samet gsopt arch"
shows "\<exists>gs. gsopt = Some gs \<and> set_tries gs =\<^sub>\<simeq> set arch"
proof -
  obtain gs where [simp]: "gsopt = Some gs" and test1: "\<And>g. g \<in> set_tries gs \<Longrightarrow>
    \<exists>h \<in> set arch. iso_test g h" and test2: "\<And>g. g \<in> set arch \<Longrightarrow>
    \<exists>h \<in> set_tries gs. iso_test g h"
    using same inv
    by(force simp: samet_def trie_all_eq_set_of_trie invar_of_list all_tries_def
      split:option.splits
      dest: in_set_lookup_of_listD in_set_lookup_set_triesD)
  have "set_tries gs \<subseteq>\<^sub>\<simeq> set arch"
  proof (auto simp:qle_gr.defs)
    fix g assume g: "g \<in> set_tries gs"
    obtain h where h: "h \<in> set arch" and test: "iso_test g h"
      using test1[OF g] by blast
    thus "\<exists>h\<in>set arch. g \<simeq> h"
      using h pre1[OF _ g] pre2[OF h] by (auto simp:iso_test_correct)
  qed
  moreover
  have "set arch \<subseteq>\<^sub>\<simeq> set_tries gs"
  proof (auto simp:qle_gr.defs)
    fix g assume g: "g \<in> set arch"
    obtain h where h: "h \<in> set_tries gs" and test: "iso_test g h"
      using test2[OF g] by blast
    thus "\<exists>h \<in> set_tries gs. g \<simeq> h"
      using h pre1[OF _ h] pre2[OF g] by (auto simp:iso_test_correct)
  qed
  ultimately show ?thesis by (auto simp: qle_gr.seteq_qle_def)
qed

lemma samet_imp_iso_subseteq:
assumes pre1: "\<And>gs g. gsopt = Some gs \<Longrightarrow> g \<in> set_tries gs \<Longrightarrow> pre_iso_test g"
and pre2: "\<And>g. g \<in> set arch \<Longrightarrow> pre_iso_test g"
and inv: "\<And>gs. gsopt = Some gs \<Longrightarrow> invar_trie gs"
and same: "samet gsopt arch"
shows "\<exists>gs. gsopt = Some gs \<and> set_tries gs \<subseteq>\<^sub>\<simeq> set arch"
using qle_gr.seteq_qle_def assms samet_imp_iso_seteq by metis

global_interpretation set_mod_trie:
  set_mod_maps "Trie None []" update_trie lookup_tries invar_trie "(\<simeq>)" iso_test pre_iso_test hash
  defines insert_mod_trie = "set_mod_maps.insert_mod update_trie lookup_tries iso_test hash"
  and worklist_tree_coll_trie = "set_modulo.worklist_tree_coll (Trie None []) insert_mod_trie"
  and worklist_tree_coll_aux_trie = "set_modulo.worklist_tree_coll_aux insert_mod_trie"
  and insert_mod2_trie = "set_modulo.insert_mod2 insert_mod_trie"
  by standard (simp_all add: iso_test_correct)

definition enum_filter_finals ::
  "(graph \<Rightarrow> graph list) \<Rightarrow> graph list
   \<Rightarrow> (nat,nat fgraph) tries option" where
"enum_filter_finals succs = set_mod_trie.worklist_tree_coll succs final fgraph"

definition tameEnumFilter :: "nat \<Rightarrow> (nat,nat fgraph)tries option" where
"tameEnumFilter p = enum_filter_finals (next_tame p) [Seed p]"

lemma TameEnum_tameEnumFilter:
  "tameEnumFilter p = Some t \<Longrightarrow>  set_tries t  =\<^sub>\<simeq> fgraph ` TameEnum\<^bsub>p\<^esub>"
apply(auto simp: tameEnumFilter_def TameEnumP_def enum_filter_finals_def)
apply(drule set_mod_trie.worklist_tree_coll_equiv[OF _ inv_inv_next_tame])
apply (auto simp: set_of_conv inv_Seed mgp_pre_iso_test RTranCl_conv)
done

lemma tameEnumFilter_subseteq_TameEnum:
  "tameEnumFilter p = Some t \<Longrightarrow> set_tries t \<subseteq> fgraph ` TameEnum\<^bsub>p\<^esub>"
by(auto simp add:tameEnumFilter_def TameEnumP_def enum_filter_finals_def
     set_of_conv inv_Seed mgp_pre_iso_test RTranCl_conv
     dest!: set_mod_trie.worklist_tree_coll_subseteq[OF _ inv_inv_next_tame])


lemma inv_tries_tameEnumFilter:
  "tameEnumFilter p = Some t \<Longrightarrow> invar_trie t"
unfolding tameEnumFilter_def enum_filter_finals_def
by(erule set_mod_trie.worklist_tree_coll_inv)

theorem combine_evals_filter:
 "\<forall>g \<in> set arch. pre_iso_test g \<Longrightarrow> samet (tameEnumFilter p) arch
  \<Longrightarrow> fgraph ` TameEnum\<^bsub>p\<^esub> \<subseteq>\<^sub>\<simeq> set arch"
apply(subgoal_tac "\<exists>t. tameEnumFilter p = Some t \<and> set_tries t \<subseteq>\<^sub>\<simeq> set arch")
 apply(metis TameEnum_tameEnumFilter qle_gr.seteq_qle_def qle_gr.subseteq_qle_trans)
apply(fastforce intro!: samet_imp_iso_subseteq
  dest: inv_tries_tameEnumFilter tameEnumFilter_subseteq_TameEnum mgp_TameEnum mgp_pre_iso_test)
done

end
