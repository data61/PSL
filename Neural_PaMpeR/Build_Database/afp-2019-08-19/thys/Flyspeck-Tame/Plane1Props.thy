(*  Author:  Gertrud Bauer, Tobias Nipkow  *)

theory Plane1Props
imports Plane1 PlaneProps Tame
begin

lemma next_plane_subset:
  "\<forall>f \<in> \<F> g. vertices f \<noteq> [] \<Longrightarrow>
   set (next_plane\<^bsub>p\<^esub> g) \<subseteq> set (next_plane0\<^bsub>p\<^esub> g)"
apply(clarsimp simp:next_plane0_def next_plane_def minimalFace_def finalGraph_def)
apply(rule_tac x = "minimal (size \<circ> vertices) (nonFinals g)" in bexI)
 apply(rule_tac x = "minimalVertex g (minimal (size \<circ> vertices) (nonFinals g))" in bexI)
  apply blast
 apply(subgoal_tac "\<forall>f\<in>set (nonFinals g). vertices f \<noteq> []")
  apply(simp add:minimalVertex_def)
 apply(simp add:nonFinals_def)
apply simp
done

lemma mgp_next_plane0_if_next_plane:
  "minGraphProps g \<Longrightarrow> g [next_plane\<^bsub>p\<^esub>]\<rightarrow> g' \<Longrightarrow> g [next_plane0\<^bsub>p\<^esub>]\<rightarrow> g'"
using next_plane_subset by(blast dest: mgp_vertices_nonempty)

lemma inv_inv_next_plane: "invariant inv next_plane\<^bsub>p\<^esub>"
apply(rule inv_subset[OF inv_inv_next_plane0])
apply(blast dest: mgp_next_plane0_if_next_plane[OF inv_mgp])
done

end
