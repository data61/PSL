(* Author: Andreas Lochbihler, ETH Zurich *)

theory MFMC_Finite imports
  EdmondsKarp_Maxflow.EdmondsKarp_Termination_Abstract
  "HOL-Library.While_Combinator"
begin

section \<open>Existence of maximum flows and minimal cuts in finite graphs\<close>

text \<open>This theory derives the existencs of a maximal flow or a minimal cut for finite graphs
from the termination proof of the Edmonds-Karp algorithm.\<close>

context Graph begin

lemma outgoing_outside: "x \<notin> V \<Longrightarrow> outgoing x = {}"
  by(auto simp add: outgoing_def V_def)

lemma incoming_outside: "x \<notin> V \<Longrightarrow> incoming x = {}"
  by(auto simp add: incoming_def V_def)

end

context NFlow begin

lemma conservation: "\<lbrakk> x \<noteq> s; x \<noteq> t \<rbrakk> \<Longrightarrow> sum f (incoming x) = sum f (outgoing x)"
  by(cases "x \<in> V")(auto simp add: conservation_const outgoing_outside incoming_outside)

lemma augmenting_path_imp_shortest: 
  "isAugmentingPath p \<Longrightarrow> \<exists>p. Graph.isShortestPath cf s p t"
  using Graph.obtain_shortest_path unfolding isAugmentingPath_def
  by (fastforce simp: Graph.isSimplePath_def Graph.connected_def)

lemma shortest_is_augmenting: 
  "Graph.isShortestPath cf s p t \<Longrightarrow> isAugmentingPath p"
  unfolding isAugmentingPath_def using Graph.shortestPath_is_simple
  by (fastforce)

definition "augment_with_path p \<equiv> augment (augmentingFlow p)"

end

context Network begin

definition "shortest_augmenting_path f = (SOME p. Graph.isShortestPath (residualGraph c f) s p t)"

lemma shortest_augmenting_path:
  assumes "NFlow c s t f" 
  and "\<exists>p. NPreflow.isAugmentingPath c s t f p"
  shows "Graph.isShortestPath (residualGraph c f) s (shortest_augmenting_path f) t"
  using assms unfolding shortest_augmenting_path_def
  by clarify(rule someI_ex, rule NFlow.augmenting_path_imp_shortest)

definition max_flow where
  "max_flow = while
     (\<lambda>f. \<exists>p. NPreflow.isAugmentingPath c s t f p)
     (\<lambda>f. NFlow.augment_with_path c f (shortest_augmenting_path f)) (\<lambda>_. 0)"

lemma max_flow:
  "NFlow c s t max_flow" (is ?thesis1)
  "\<not> (\<exists>p. NPreflow.isAugmentingPath c s t max_flow p)" (is ?thesis2)
proof -
  have "NFlow c s t (\<lambda>_. 0)"
    by unfold_locales(simp_all add: cap_non_negative)
  moreover have "NFlow c s t (NFlow.augment_with_path c f (shortest_augmenting_path f))"
    if "NFlow c s t f" and "\<exists>p. NPreflow.isAugmentingPath c s t f p" for f
  proof -
    interpret NFlow c s t f using that(1) .
    interpret F: Flow c s t "NFlow.augment c f (NPreflow.augmentingFlow c f (shortest_augmenting_path f))"
      by(intro augment_flow_presv augFlow_resFlow shortest_is_augmenting shortest_augmenting_path[OF that])
    show ?thesis using that
      by(simp add: NFlow.augment_with_path_def)(unfold_locales)
  qed
  ultimately have "NFlow c s t max_flow \<and> \<not> (\<exists>p. NPreflow.isAugmentingPath c s t max_flow p)"
    unfolding max_flow_def
    by(rule while_rule[where P="NFlow c s t" and r="measure (\<lambda>f. ek_analysis_defs.ekMeasure (residualGraph c f) s t)"])
      (auto intro: shortest_augmenting_path NFlow.shortest_path_decr_ek_measure simp add: NFlow.augment_with_path_def)
  thus ?thesis1 ?thesis2 by simp_all
qed

end

end
