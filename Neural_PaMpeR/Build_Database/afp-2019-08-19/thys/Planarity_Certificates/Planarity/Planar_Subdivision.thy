theory Planar_Subdivision
imports
  Graph_Genus
  Reachablen
  Permutations_2
begin

section \<open>Combinatorial Planarity and Subdivisions\<close>

locale subdiv1_contr = subdiv_step +
  fixes HM
  assumes H_map: "digraph_map H HM"
  assumes edge_rev_conv: "edge_rev HM = rev_H"

sublocale subdiv1_contr \<subseteq> H: digraph_map H HM
  rewrites "edge_rev HM = rev_H" by (intro H_map edge_rev_conv)+

sublocale subdiv1_contr \<subseteq> G: fin_digraph G
  by unfold_locales (auto simp: arcs_G verts_G)

context subdiv1_contr begin

  definition GM :: "'b pre_map" where
    "GM \<equiv>
      \<lparr> edge_rev = rev_G
      , edge_succ = perm_swap uw uv (perm_swap vw vu (fold perm_rem [wu, wv] (edge_succ HM)))
      \<rparr>"

  lemma edge_rev_GM:  "edge_rev GM = rev_G"
    by (simp add: GM_def)

  lemma edge_succ_GM: "edge_succ GM = perm_swap uw uv (perm_swap vw (rev_G uv) (fold perm_rem [wu, wv] (edge_succ HM)))"
    by (simp add: GM_def)

  lemma rev_H_eq_rev_G:
    assumes "x \<in> arcs G - {uv,vu}" shows "rev_H x = rev_G x"
  proof -
    have "perm_restrict rev_H (arcs G) = perm_restrict rev_G (arcs H)"
      using subdiv_step by (auto simp: subdivision_step_def)
    with assms show ?thesis
      unfolding arcs_H by (auto simp: perm_restrict_def fun_eq_iff split: if_splits)
  qed

  lemma edge_succ_permutes: "edge_succ GM permutes arcs G"
  proof -
    have "arcs H \<subseteq> (vw \<rightleftharpoons>\<^sub>F rev_G uv) ` (uw \<rightleftharpoons>\<^sub>F uv) ` arcs G \<union> {wv} \<union> {wu}"
      using subdiv_distinct_arcs in_arcs_G
      by (auto simp: arcs_H in_funswapid_image_iff swap_id_eq split: if_splits)
    then have "perm_swap uw uv (perm_swap vw (rev_G uv) (perm_rem (wv) (perm_rem (wu) (edge_succ HM)))) permutes arcs G"
      by (blast intro: perm_rem_permutes perm_swap_permutes2 permutes_subset H.edge_succ_permutes)
    then show ?thesis by (auto simp: edge_succ_GM)
  qed

  lemma out_arcs_empty:
    assumes "x \<in> verts G"
    shows "out_arcs G x = {} \<longleftrightarrow> out_arcs H x = {}"
  proof
    assume A: "out_arcs H x = {}"
    have tail_eqI: "\<And>a. tail H a = tail G a" by (simp only: tail_eq)

    { fix a assume "a \<in> out_arcs G x"
      moreover have "a \<in> arcs H \<Longrightarrow> a \<noteq> uv" "a \<in> arcs H \<Longrightarrow> a \<noteq> vu"
        using not_in_arcs_H by auto
      ultimately have "(uw \<rightleftharpoons>\<^sub>F uv) ((vw \<rightleftharpoons>\<^sub>F vu) a) \<in> out_arcs H x"
        using subdiv_distinct_arcs in_arcs_H not_in_arcs_H
        by (auto simp: arcs_G intro: tail_eqI)
    }
    then show "out_arcs G x = {}"
      using A by (auto simp del: in_out_arcs_conv)
  next
    assume A: "out_arcs G x = {}"
    have tail_eqI: "\<And>a. tail H a = tail G a" by (simp only: tail_eq)

    { fix a assume "a \<in> out_arcs H x"
      moreover have "x \<noteq> w" using assms not_in_verts_G by blast
      ultimately have "(uw \<rightleftharpoons>\<^sub>F uv) ((vw \<rightleftharpoons>\<^sub>F vu) a) \<in> out_arcs G x"
        using subdiv_distinct_arcs in_arcs_G not_in_arcs_G
        by (auto simp: arcs_H ) (auto simp: swap_id_eq intro: tail_eqI[symmetric])
    }
    then show "out_arcs H x = {}"
      using A by (auto simp del: in_out_arcs_conv)
  qed

  lemma cyclic_on_edge_succ:
    assumes "x \<in> verts G" "out_arcs G x \<noteq> {}"
    shows "cyclic_on (edge_succ GM) (out_arcs G x)"
  proof -
    have oa_Gx: "out_arcs G x = (uw \<rightleftharpoons>\<^sub>F uv) ` (vw \<rightleftharpoons>\<^sub>F vu) ` (out_arcs H x - {wu} - {wv})"
      using subdiv_distinct_arcs not_in_arcs_G in_arcs_G
      by (auto simp: in_funswapid_image_iff arcs_H swap_id_eq tail_eq[symmetric] split: if_splits)

    have "cyclic_on (perm_swap uw uv (perm_swap vw (rev_G uv) (perm_rem (wv) (perm_rem (wu) (edge_succ HM))))) (out_arcs G x)"
      unfolding oa_Gx
    proof (intro cyclic_on_perm_swap cyclic_on_perm_rem)
      show "cyclic_on (edge_succ HM) (out_arcs H x)"
        using assms by (auto simp: out_arcs_empty verts_H intro: H.edge_succ_cyclic)
      show "bij (edge_succ HM)" by (simp add: H.bij_edge_succ)
      show "bij (perm_rem (wu) (edge_succ HM))" by (simp add: H.bij_edge_succ)

      have "x \<noteq> w" using assms not_in_verts_G by auto
      then have "wu \<notin> out_arcs H x" "wv \<notin> out_arcs H x"
        by (auto simp: arc_to_ends_def)
      then show "out_arcs H x - {wu} \<noteq> {wv}" "out_arcs H x \<noteq> {wu}"
        by blast+
    qed
    then show ?thesis by (simp add: edge_succ_GM)
  qed

  lemma digraph_map_GM:
    shows "digraph_map G GM"
    by unfold_locales (auto simp: edge_rev_GM G.arev_dom edge_succ_permutes cyclic_on_edge_succ verts_G)

end


sublocale subdiv1_contr \<subseteq> GM: digraph_map G GM by (rule digraph_map_GM)

context subdiv1_contr begin

  lemma reachableGD:
    assumes "x \<rightarrow>\<^sup>*\<^bsub>G\<^esub> y" shows "x \<rightarrow>\<^sup>*\<^bsub>H\<^esub> y"
    using assms
  proof induct
    case base then show ?case by (auto simp: verts_H)
  next
    case (step x z)
    moreover
    have "u \<rightarrow>\<^sup>*\<^bsub>H\<^esub> v" "v \<rightarrow>\<^sup>*\<^bsub>H\<^esub> u" using adj_with_w by auto
    moreover
    { assume A: "(x,z) \<noteq> (u,v)" "(x,z) \<noteq> (v,u)"
      from \<open>x \<rightarrow>\<^bsub>G\<^esub> z\<close> obtain a where "a \<in> arcs G" "tail G a = x" "head G a = z"
        by auto
      with A have "a \<in> arcs H" "arc_to_ends H a = (x,z)" "tail H a = x" "head G a = z"
        by (auto simp: arcs_H tail_eq head_eq arc_to_ends_def fun_eq_iff)
      then have "x \<rightarrow>\<^bsub>H\<^esub> z" by (auto simp: arcs_ends_def intro: rev_image_eqI)
    }
    ultimately
    show ?case by (auto intro: H.reachable_trans)
  qed

  definition proj_verts_H :: "'a \<Rightarrow> 'a" where
    "proj_verts_H x \<equiv> if x = w then u else x"

  lemma proj_verts_H_in_G: "x \<in> verts H \<Longrightarrow> proj_verts_H x \<in> verts G"
    using in_verts_G by (auto simp: proj_verts_H_def verts_H)

  lemma dominatesHD:
    assumes "x \<rightarrow>\<^bsub>H\<^esub> y" shows "proj_verts_H x \<rightarrow>\<^sup>*\<^bsub>G\<^esub> proj_verts_H y"
  proof -
    have X1: "\<And>a. (w, y) = arc_to_ends G a \<Longrightarrow> a \<notin> arcs G"
      by (metis G.adj_in_verts(1) G.dominatesI not_in_verts_G)
    have X2: "\<And>a. (x, w) = arc_to_ends G a \<Longrightarrow> a \<notin> arcs G"
      by (metis G.adj_in_verts(2) G.dominatesI not_in_verts_G)
    show ?thesis
      using assms subdiv_ate_H_rev subdiv_ate in_verts_G
      by (auto simp: arcs_ends_def arcs_H arc_to_ends_eq proj_verts_H_def G_reach dest: X1 X2)
  qed

  lemma reachableHD:
    assumes reach:"x \<rightarrow>\<^sup>*\<^bsub>H\<^esub> y" shows "proj_verts_H x \<rightarrow>\<^sup>*\<^bsub>G\<^esub> proj_verts_H y"
    using assms by induct (blast intro: proj_verts_H_in_G G.reachable_trans dominatesHD)+

  lemma H_reach_conv: "\<And>x y. x \<rightarrow>\<^sup>*\<^bsub>H\<^esub> y \<longleftrightarrow> proj_verts_H x \<rightarrow>\<^sup>*\<^bsub>G\<^esub> proj_verts_H y"
    using w_reach by (auto simp: reachableHD)
      (auto simp: proj_verts_H_def verts_H split: if_splits dest: reachableGD intro: H.reachable_trans)

  lemma sccs_eq: "G.sccs_verts = (`) proj_verts_H ` H.sccs_verts" (is "?L = ?R")
  proof (intro set_eqI iffI)
    fix S assume "S \<in> ?L"
    then have "w \<notin> S" using G.sccs_verts_subsets not_in_verts_G by blast
    then have S_eq: "proj_verts_H ` proj_verts_H -` S = S"
        by (auto simp: proj_verts_H_def intro: range_eqI)
    then have "proj_verts_H -` S \<noteq> {}" using \<open>S \<in> ?L\<close> by safe (auto simp: G.sccs_verts_def)
    with \<open>S \<in> ?L\<close> have "proj_verts_H -` S \<in> H.sccs_verts"
      by (auto simp: G.in_sccs_verts_conv_reachable H.in_sccs_verts_conv_reachable H_reach_conv)
    then have "proj_verts_H ` proj_verts_H -` S \<in> (`) proj_verts_H ` H.sccs_verts" by (rule imageI)
    then show "S \<in> ?R" by (simp only: S_eq)
  next
    fix S assume "S \<in> ?R"
    have X: "\<And>v x. v \<notin> proj_verts_H ` x \<Longrightarrow> v = w \<or> (\<exists>y. v = proj_verts_H y \<and> y \<notin> x)"
      by (auto simp: proj_verts_H_def split: if_splits)
    from \<open>S \<in> ?R\<close> show "S \<in> ?L"
      using not_in_verts_G by (fastforce simp: G.reachable_in_verts G.in_sccs_verts_conv_reachable
        H.in_sccs_verts_conv_reachable H_reach_conv dest: X)
  qed

  lemma inj_on_proj_verts_H: "inj_on ((`) proj_verts_H) (pre_digraph.sccs_verts H)"
  proof (rule inj_onI)
    fix S T assume A: "S \<in> H.sccs_verts" "T \<in> H.sccs_verts" "proj_verts_H ` S = proj_verts_H ` T"
    have "\<And>x. w \<notin> x \<Longrightarrow> proj_verts_H ` x = x" by (auto simp: proj_verts_H_def)
    with A have "S \<noteq> T \<Longrightarrow> S \<inter> T \<noteq> {}"
      by (metis H.in_sccs_verts_conv_reachable Int_iff empty_iff image_eqI proj_verts_H_def w_reach(1,2))
    then show "S = T" using H.sccs_verts_disjoint[OF A(1,2)] by metis
  qed

  lemma card_sccs_verts: "card G.sccs_verts = card H.sccs_verts"
    unfolding sccs_eq by (intro card_image inj_on_proj_verts_H)

  lemma card_sccs_eq: "card G.sccs = card H.sccs"
    using card_sccs_verts G.inj_on_verts_sccs H.inj_on_verts_sccs
    by (auto simp: G.sccs_verts_conv H.sccs_verts_conv card_image)

  lemma isolated_verts_eq: "G.isolated_verts = H.isolated_verts"
    by (auto simp: G.isolated_verts_def H.isolated_verts_def verts_H out_arcs_w dest: out_arcs_empty)

  lemma card_verts: "card (verts H) = card (verts G) + 1"
    unfolding verts_H using not_in_verts_G by auto

  lemma card_arcs: "card (arcs H) = card (arcs G) + 2"
    unfolding arcs_H using not_in_arcs_G subdiv_distinct_arcs in_arcs_G by (auto simp: card_insert_if)

  lemma edge_succ_wu: "edge_succ HM wu = wv"
    using out_arcs_w out_degree_w edge_succ_permutes H.edge_succ_cyclic[of w]
    by (auto elim: eq_on_cyclic_on_iff1[where x="wu"] simp: verts_H out_degree_def)

  lemma edge_succ_wv: "edge_succ HM wv = wu"
    using out_arcs_w out_degree_w edge_succ_permutes H.edge_succ_cyclic[of w]
    by (auto elim: eq_on_cyclic_on_iff1[where x="wv"] simp: verts_H out_degree_def)

  lemmas edge_succ_w = edge_succ_wu edge_succ_wv

  lemma H_face_cycle_succ:
      "H.face_cycle_succ uw = wv"
      "H.face_cycle_succ vw = wu"
    unfolding H.face_cycle_succ_def by (auto simp: edge_succ_w)

  lemma H_edge_succ_tail_eqD:
    assumes "edge_succ HM a = b" shows "tail H a = tail H b"
    using assms H.tail_edge_succ[of a] by auto

  lemma YYY:
    "(wu \<rightleftharpoons>\<^sub>F wv) (edge_succ HM vw) = (edge_succ HM vw)"
    "(wu \<rightleftharpoons>\<^sub>F wv) (edge_succ HM uw) = (edge_succ HM uw)"
    using H.edge_succ_cyclic[of w] subdiv_distinct_verts0 by (auto simp: swap_id_eq dest: H_edge_succ_tail_eqD)

  text \<open>Project arcs of @{term H} to corresponding arcs of @{term G}\<close>
  definition proj_arcs_H :: "'b \<Rightarrow> 'b" where
    "proj_arcs_H x \<equiv>
      if x = uw \<or> x = wv then uv
      else if x = vw \<or> x = wu then vu
      else x"

  text \<open>Project arcs of @{term G} to corresponding arcs of @{term H}\<close>
  definition proj_arcs_G :: "'b \<Rightarrow> 'b" where
    "proj_arcs_G x \<equiv>
      if x = uv then uw
      else if x = vu then vw
      else x"

  lemma proj_arcs_H_simps[simp]:
      "proj_arcs_H uw = uv"
      "proj_arcs_H wv = uv"
      "proj_arcs_H vw = vu"
      "proj_arcs_H wu = vu"
      "x \<notin> {uw,vw,wu,wv} \<Longrightarrow> proj_arcs_H x = x"
      "a \<in> arcs G \<Longrightarrow> proj_arcs_H a = a"
    using subdiv_distinct_arcs not_in_arcs_G by (auto simp: proj_arcs_H_def)

  lemma proj_arcs_H_in_arcs_G: "a \<in> arcs H \<Longrightarrow> proj_arcs_H a \<in> arcs G"
    using subdiv_distinct_arcs in_arcs_G by (auto simp: proj_arcs_H_def arcs_H)

  lemma proj_arcs_eq_swap:
    assumes "a \<notin> {uv,vu,wu,wv}"
    shows "proj_arcs_H a = (uw \<rightleftharpoons>\<^sub>F uv o vw \<rightleftharpoons>\<^sub>F vu) a"
    using assms subdiv_distinct_arcs by (cases "a \<in> {uw,vw}") auto

  lemma proj_arcs_G_simps:
      "proj_arcs_G uv = uw"
      "proj_arcs_G vu = vw"
      "a \<notin> {uv,vu} \<Longrightarrow> proj_arcs_G a = a"
    using subdiv_distinct_arcs not_in_arcs_G by (auto simp: swap_id_eq proj_arcs_G_def)

  lemma proj_arcs_G_in_arcs_H:
    assumes "a \<in> arcs G" shows "proj_arcs_G a \<in> arcs H"
    using assms subdiv_distinct_arcs by (auto simp: proj_arcs_G_def arcs_H)

  lemma proj_arcs_HG: "a \<in> arcs G \<Longrightarrow> proj_arcs_H (proj_arcs_G a) = a"
    by (auto simp: proj_arcs_G_def)

  lemma fcs_proj_arcs_GH:
    assumes "a \<in> arcs H" shows "H.face_cycle_set (proj_arcs_G (proj_arcs_H a)) = H.face_cycle_set a"
  proof -
    have "H.face_cycle_set vw = H.face_cycle_set wu" "H.face_cycle_set uw = H.face_cycle_set wv"
      unfolding H.face_cycle_set_def by (auto simp add: H_face_cycle_succ[symmetric]
        self_in_orbit_step H.permutation_face_cycle_succ permutation_self_in_orbit)
    then show ?thesis
      using assms not_in_arcs_H by (cases "a \<in> {uv,vu,uw,wu,vw,wv}") (auto simp: proj_arcs_G_simps)
  qed 

  lemma H_face_cycle_succ_neq_uv:
    "a \<notin> {uv,vu} \<Longrightarrow> H.face_cycle_succ a \<notin> {uv,vu}"
    using not_in_arcs_H by (cases "a \<in> arcs H") (auto dest: H.face_cycle_succ_in_arcsI)

  lemma face_cycle_succ_choose_inter:
    "{H.face_cycle_succ uw, H.face_cycle_succ vw, H.face_cycle_succ wu, H.face_cycle_succ wv} \<inter> {uv,vu} = {}"
    using subdiv_distinct_arcs H_face_cycle_succ_neq_uv by safe (simp_all, metis+)

  lemma face_cycle_succ_choose_neq:
      "H.face_cycle_succ wu \<notin> {wu,wv}"
      "H.face_cycle_succ wv \<notin> {wu,wv}"
    using subdiv_distinct_verts0 in_arcs_H
    by (auto simp del: H.edge_rev_in_arcs dest: H.tail_face_cycle_succ)

  lemma H_face_cycle_succ_G_not_in:
    assumes "a \<in> arcs G" shows "H.face_cycle_succ a \<notin> {wu,wv}"
  proof (cases "a \<in> {uv,vu}")
    case True with assms show ?thesis using subdiv_distinct_arcs by (auto simp: arcs_H)
  next
    case False with assms have "a \<in> arcs H" by (auto simp: arcs_H)
    from assms have "head H a \<noteq> w" by (auto simp: head_eq verts_G arcs_H dest: G.head_in_verts)
    then show ?thesis using H.tail_face_cycle_succ[OF \<open>a \<in> arcs H\<close>] by auto
  qed

  lemma
    face_cycle_succ_uv: "GM.face_cycle_succ uv = proj_arcs_H (H.face_cycle_succ wv)" and
    face_cycle_succ_vu: "GM.face_cycle_succ vu = proj_arcs_H (H.face_cycle_succ wu)"
    unfolding GM.face_cycle_succ_def edge_rev_GM edge_succ_GM
    using face_cycle_succ_choose_neq face_cycle_succ_choose_inter subdiv_distinct_arcs
    apply (auto simp: fun_eq_iff perm_swap_def)
    apply (auto simp: perm_rem_def edge_succ_w H.face_cycle_succ_def YYY proj_arcs_H_def)
    done

  lemma face_cycle_succ_not_uv:
    assumes "a \<in> arcs G" "a \<notin> {uv,vu}"
    shows "GM.face_cycle_succ a = proj_arcs_H (H.face_cycle_succ a)"
  proof -
    have "GM.face_cycle_succ a = (uw \<rightleftharpoons>\<^sub>F uv) ((vw \<rightleftharpoons>\<^sub>F rev_G uv) (perm_rem (wv) (perm_rem (wu) (edge_succ HM)) (((vw \<rightleftharpoons>\<^sub>F vu) ((uw \<rightleftharpoons>\<^sub>F uv) (rev_G a))))))"
      by (simp add: GM.face_cycle_succ_def perm_swap_def edge_succ_GM edge_rev_GM)
    also have "(vw \<rightleftharpoons>\<^sub>F vu) ((uw \<rightleftharpoons>\<^sub>F uv) (rev_G a)) = rev_G a"
      using assms not_in_arcs_G by (auto simp: swap_id_eq G.arev_eq_iff)
    also have "perm_rem (wv) (perm_rem (wu) (edge_succ HM)) (rev_G a) = edge_succ HM (rev_G a)"
    proof -
      have *: "\<And>a. tail H a \<noteq> w \<Longrightarrow> (wu \<rightleftharpoons>\<^sub>F wv) a = a" by (auto simp: swap_id_eq)
      from assms have "head H a \<noteq> w" "tail H (rev_G a) = head H a"
        by (auto simp: tail_eq head_eq verts_G dest: G.head_in_verts)
      then have "((wu \<rightleftharpoons>\<^sub>F wv) (edge_succ HM (rev_G a))) = edge_succ HM (rev_G a)"
        by (intro *) auto
      then show ?thesis by (auto simp: perm_rem_def edge_succ_w)
    qed
    also have "edge_succ HM (rev_G a) = H.face_cycle_succ a"
      using assms unfolding H.face_cycle_succ_def by (simp add: rev_H_eq_rev_G)
    also have "(uw \<rightleftharpoons>\<^sub>F uv) ((vw \<rightleftharpoons>\<^sub>F rev_G uv) (H.face_cycle_succ a)) = proj_arcs_H (H.face_cycle_succ a)"
    proof -
      from assms have "a \<in> arcs H" by (auto simp: arcs_H)
      then have fcs_not_in: "H.face_cycle_succ a \<notin> {uv, vu, wu, wv}"
        using assms H_face_cycle_succ_G_not_in in_arcs_G not_in_arcs_H
        by (auto simp del: G.arev_in_arcs dest: H.face_cycle_succ_closed[THEN iffD2])
      then show ?thesis by (auto simp add: proj_arcs_eq_swap)
    qed
    finally show ?thesis .
  qed

  lemmas G_face_cycle_succ = face_cycle_succ_uv face_cycle_succ_vu face_cycle_succ_not_uv

  lemma in_G_fcs_in_H_fcs:
    assumes "a \<in> arcs G"
    assumes "x \<in> GM.face_cycle_set a"
    shows "x \<in> proj_arcs_H ` H.face_cycle_set (proj_arcs_G a)"
    using \<open>x \<in> _\<close>
  proof induct
    case base show ?case
      by (rule rev_image_eqI[where x="proj_arcs_G a"]) (auto simp: \<open>a \<in> arcs G\<close> proj_arcs_G_def)
  next
    case (step b)
    { fix x assume "x \<in> H.face_cycle_set (proj_arcs_G a)"
      then have "x \<in> arcs H"
        using \<open>a \<in> arcs G\<close> by (auto dest: H.in_face_cycle_setD simp: proj_arcs_G_in_arcs_H)
      moreover
      then have "x \<notin> {uv,vu}" "x \<notin> {uw,wu,vw,wv} \<Longrightarrow> x \<in> arcs G"
        using \<open>a \<in> arcs G\<close> by (auto simp: arcs_H dest: H.in_face_cycle_setD)
      ultimately
      have "GM.face_cycle_succ (proj_arcs_H x) \<in> {proj_arcs_H (H.face_cycle_succ x),
          proj_arcs_H (H.face_cycle_succ (H.face_cycle_succ x))}"
        by (cases "x \<in> {uw,vw,wu,wv}") (auto simp: G_face_cycle_succ H_face_cycle_succ)
    }
    moreover
    have "b \<in> arcs G"
      using step(1) \<open>a \<in> arcs G\<close> by (simp add: GM.in_face_cycle_setD GM.face_cycle_set_def)
    ultimately
    show ?case using \<open>b \<in> arcs G\<close> step(2) by (auto intro: H.face_cycle_succ_inI)
  qed

  lemma in_H_fcs_in_G_fcs:
    assumes "a \<in> arcs H"
    assumes "x \<in> H.face_cycle_set a"
    shows "x \<in> proj_arcs_H -` GM.face_cycle_set (proj_arcs_H a)"
    using \<open>x \<in> _\<close>
  proof induct
    case base then show ?case by auto
  next
    case (step y)
    then have "y \<in> arcs H" using \<open>a \<in> arcs H\<close> by (auto dest: H.in_face_cycle_setD)
    moreover then have "y \<notin> {uv,vu}" by (fastforce simp: arcs_H)
    ultimately have "proj_arcs_H (H.face_cycle_succ y) = GM.face_cycle_succ (proj_arcs_H y)
        \<or> proj_arcs_H (H.face_cycle_succ y) = proj_arcs_H y"
      by (cases "y \<in> {uw,vw,wv,wu}") (auto simp: H_face_cycle_succ G_face_cycle_succ arcs_G)
    with step show ?case by (auto intro: GM.face_cycle_succ_inI)
  qed

  lemma G_fcs_eq:
    assumes "a \<in> arcs G"
    shows "GM.face_cycle_set a = proj_arcs_H ` H.face_cycle_set (proj_arcs_G a)" (is "?L = ?R")
    using assms by (auto dest: in_H_fcs_in_G_fcs[rotated] in_G_fcs_in_H_fcs[rotated]
      simp: proj_arcs_G_in_arcs_H proj_arcs_HG)

  lemma H_fcs_eq:
    assumes "a \<in> arcs H"
    shows "proj_arcs_H ` H.face_cycle_set a = GM.face_cycle_set (proj_arcs_H a)"
    using assms by (auto dest: in_H_fcs_in_G_fcs[rotated] in_G_fcs_in_H_fcs[rotated]
      simp: proj_arcs_H_in_arcs_G fcs_proj_arcs_GH)

  lemma face_cycle_sets:
    shows "GM.face_cycle_sets = (`) proj_arcs_H ` H.face_cycle_sets" (is "?L = ?R")
    unfolding GM.face_cycle_sets_def H.face_cycle_sets_def
    by (blast intro!: H_fcs_eq G_fcs_eq proj_arcs_G_in_arcs_H proj_arcs_H_in_arcs_G)

  lemma inj_on_proj_arcs_H: "inj_on ((`) proj_arcs_H) H.face_cycle_sets"
  proof (rule inj_onI)
    fix A B assume fcs: "A \<in> H.face_cycle_sets" "B \<in> H.face_cycle_sets"
      and pa_eq: "proj_arcs_H ` A = proj_arcs_H ` B"

    have xw_iff_wy:
      "\<And>X. X \<in> H.face_cycle_sets \<Longrightarrow> uw \<in> X \<longleftrightarrow> wv \<in> X"
      "\<And>X. X \<in> H.face_cycle_sets \<Longrightarrow> vw \<in> X \<longleftrightarrow> wu \<in> X"
      using H_face_cycle_succ by (auto simp: H.face_cycle_sets_def dest: H.face_cycle_succ_inI intro: H.face_cycle_succ_inD)

    have not_in_A: "uv \<notin> A" "vu \<notin> A" and not_in_B: "vu \<notin> B" "uv \<notin> B" 
      using fcs not_in_arcs_H by (auto dest: H.in_face_cycle_setsD)

    have "A = proj_arcs_H -` (proj_arcs_H ` A) - {uv,vu}"
      using subdiv_distinct_arcs not_in_A by (auto simp: proj_arcs_H_def xw_iff_wy[OF fcs(1)] split: if_splits)
    also have "\<dots> = proj_arcs_H -` (proj_arcs_H ` B) - {uv,vu}" by (simp add: pa_eq)
    also have "\<dots> = B"
      using subdiv_distinct_arcs not_in_B by (auto simp: proj_arcs_H_def xw_iff_wy[OF fcs(2)] split: if_splits)
    finally show "A = B" .
  qed

  lemma card_face_cycle_sets: "card GM.face_cycle_sets = card H.face_cycle_sets"
    unfolding face_cycle_sets using inj_on_proj_arcs_H by (rule card_image)

  lemma euler_char_eq: "GM.euler_char = H.euler_char"
    by (auto simp: GM.euler_char_def H.euler_char_def card_verts card_arcs card_face_cycle_sets)

  lemma euler_genus_eq: "GM.euler_genus = H.euler_genus"
    by (auto simp: GM.euler_genus_def H.euler_genus_def euler_char_eq card_sccs_eq isolated_verts_eq)

end

lemma subdivision_genus_same_rev:
  assumes "subdivision (G, rev_G) (H, edge_rev HM)" "digraph_map H HM" "pre_digraph_map.euler_genus H HM = m"
  shows "\<exists>GM. digraph_map G GM \<and> pre_digraph_map.euler_genus G GM = m \<and> edge_rev GM = rev_G"
proof -
  from assms show ?thesis
  proof (induction rev_H\<equiv>"edge_rev HM" arbitrary: HM)
    case base then show ?case by auto
  next
    case (divide I rev_I H u v w uv uw vw)
    then interpret subdiv_step I rev_I H "edge_rev HM" u v w uv uw vw
      by unfold_locales simp

    interpret H: digraph_map H HM using \<open>digraph_map H HM\<close> .
    interpret IH: subdiv1_contr I rev_I H "edge_rev HM" u v w uv uw vw HM
      by unfold_locales simp

    have eulerI: "IH.GM.euler_genus = m" by (auto simp: IH.euler_genus_eq divide)
    with _ IH.digraph_map_GM show ?case by (rule divide) (simp add: IH.edge_rev_GM)
  qed
qed

lemma subdivision_genus:
  assumes "subdivision (G, rev_G) (H, rev_H)" "digraph_map H HM" "pre_digraph_map.euler_genus H HM = m"
  shows "\<exists>GM. digraph_map G GM \<and> pre_digraph_map.euler_genus G GM = m"
proof -
  interpret H: digraph_map H HM by fact
  show ?thesis
    using subdivision_genus_same_rev subdivision_choose_rev assms H.bidirected_digraph by metis
qed

lemma subdivision_comb_planar:
  assumes "subdivision (G, rev_G) (H, rev_H)" "comb_planar H" shows "comb_planar G"
  using assms unfolding comb_planar_def by (metis subdivision_genus)

end
