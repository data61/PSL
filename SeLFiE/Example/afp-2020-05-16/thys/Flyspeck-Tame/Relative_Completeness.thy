(*  Author: Tobias Nipkow  *)

section \<open>Completeness Proofs under hypothetical computations\<close>

theory Relative_Completeness
imports ArchCompProps
begin

definition Archive :: "vertex fgraph set" where
"Archive \<equiv> set(Tri @ Quad @ Pent @ Hex)"

locale archive_by_computation =
  assumes pre_iso_test3: "\<forall>g \<in> set Tri. pre_iso_test g"
  assumes pre_iso_test4: "\<forall>g \<in> set Quad. pre_iso_test g"
  assumes pre_iso_test5: "\<forall>g \<in> set Pent. pre_iso_test g"
  assumes pre_iso_test6: "\<forall>g \<in> set Hex. pre_iso_test g"
  assumes same3: "samet (tameEnumFilter 0) Tri"
  assumes same4: "samet (tameEnumFilter 1) Quad"
  assumes same5: "samet (tameEnumFilter 2) Pent"
  assumes same6: "samet (tameEnumFilter 3) Hex"
begin

theorem TameEnum_Archive:  "fgraph ` TameEnum \<subseteq>\<^sub>\<simeq> Archive"
using combine_evals_filter[OF pre_iso_test3 same3]
      combine_evals_filter[OF pre_iso_test4 same4]
      combine_evals_filter[OF pre_iso_test5 same5]
      combine_evals_filter[OF pre_iso_test6 same6]
by(fastforce simp:TameEnum_def Archive_def image_def qle_gr.defs
       eval_nat_numeral le_Suc_eq)

lemma TameEnum_comp:
assumes "Seed\<^bsub>p\<^esub> [next_plane\<^bsub>p\<^esub>]\<rightarrow>* g" and "final g" and "tame g"
shows "Seed\<^bsub>p\<^esub> [next_tame\<^bsub>p\<^esub>]\<rightarrow>* g"
proof -
  from assms have "Seed\<^bsub>p\<^esub> [next_tame0 p]\<rightarrow>* g" by(rule next_tame0_comp)
  with assms show "Seed\<^bsub>p\<^esub> [next_tame\<^bsub>p\<^esub>]\<rightarrow>* g" by(blast intro: next_tame_comp)
qed

(* final not necessary but slightly simpler because of lemmas *)
lemma tame5:
assumes g: "Seed\<^bsub>p\<^esub> [next_plane0\<^bsub>p\<^esub>]\<rightarrow>* g" and "final g" and "tame g"
shows "p \<le> 3"
proof -
  from \<open>tame g\<close> have bound: "\<forall>f \<in> \<F> g. |vertices f| \<le> 6"
    by (simp add: tame_def tame9a_def)
  show "p \<le> 3"
  proof (rule ccontr)
    assume 6: "\<not> p \<le> 3"
    obtain f where "f \<in> set (finals g) \<and> |vertices f| = p+3"
      using max_face_ex[OF g] by auto
    also from \<open>final g\<close> have "set (finals g) = set (faces g)" by simp
    finally have "f \<in> \<F> g \<and> 6 < |vertices f|" using 6 by arith
    with bound show False by auto
  qed
qed

theorem completeness:
assumes "g \<in> PlaneGraphs" and "tame g" shows "fgraph g \<in>\<^sub>\<simeq> Archive"
proof -
  from \<open>g \<in> PlaneGraphs\<close> obtain p where g1: "Seed\<^bsub>p\<^esub> [next_plane\<^bsub>p\<^esub>]\<rightarrow>* g"
    and "final g"
    by(auto simp:PlaneGraphs_def PlaneGraphsP_def)
  have "Seed\<^bsub>p\<^esub> [next_plane0\<^bsub>p\<^esub>]\<rightarrow>* g"
    by(rule RTranCl_subset2[OF g1])
      (blast intro:inv_mgp inv_Seed mgp_next_plane0_if_next_plane
        dest:RTranCl_inv[OF inv_inv_next_plane])
  with \<open>tame g\<close> \<open>final g\<close> have "p \<le> 3" by(blast intro:tame5)
  with g1 \<open>tame g\<close> \<open>final g\<close> show ?thesis using TameEnum_Archive
    by(simp add: qle_gr.defs TameEnum_def TameEnumP_def)
      (blast intro: TameEnum_comp)
qed

end

end
