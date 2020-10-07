theory Planar_Subgraph
imports
  Graph_Genus
  Permutations_2
  "HOL-Library.FuncSet"
  "HOL-Library.Simps_Case_Conv"
begin

section \<open>Combinatorial Planarity and Subgraphs\<close>

lemma out_arcs_emptyD_dominates:
  assumes "out_arcs G x = {}" shows "\<not>x \<rightarrow>\<^bsub>G\<^esub> y"
  using assms by (auto simp: out_arcs_def)

lemma (in wf_digraph) reachable_refl_iff: "u \<rightarrow>\<^sup>* u \<longleftrightarrow> u \<in> verts G"
  by (auto simp: reachable_in_verts)

context digraph_map begin

  lemma face_cycle_set_succ[simp]: "face_cycle_set (face_cycle_succ a) = face_cycle_set a"
    by (metis face_cycle_eq face_cycle_set_self face_cycle_succ_inD)

  lemma face_cycle_succ_funpow_in[simp]:
    "(face_cycle_succ ^^ n) a \<in> arcs G \<longleftrightarrow> a \<in> arcs G"
    by (induct n) auto

  lemma segment_face_cycle_x_x_eq:
    "segment face_cycle_succ x x = face_cycle_set x - {x}"
    unfolding face_cycle_set_def using face_cycle_succ_permutes finite_arcs permutation_permutes
    by (intro segment_x_x_eq) blast

  lemma fcs_x_eq_x: "face_cycle_succ x = x \<longleftrightarrow> face_cycle_set x = {x}" (is "?L \<longleftrightarrow> ?R")
    unfolding face_cycle_set_def orbit_eq_singleton_iff ..

end


lemma (in bidirected_digraph) bidirected_digraph_del_arc:
    "bidirected_digraph (pre_digraph.del_arc (pre_digraph.del_arc G (arev a)) a) (perm_restrict arev (arcs G - {a , arev a}))"
proof unfold_locales
  fix b assume A: "b \<in> arcs (pre_digraph.del_arc (del_arc (arev a)) a)"
  have "arev b \<noteq> b \<Longrightarrow> b \<noteq> arev a \<Longrightarrow> b \<noteq> a \<Longrightarrow> perm_restrict arev (arcs G - {a, arev a}) (arev b) = b"
    using bij_arev arev_dom by (subst perm_restrict_simps) (auto simp: bij_iff)
  then show "perm_restrict arev (arcs G - {a, arev a}) (perm_restrict arev (arcs G - {a, arev a}) b) = b"
    using A
    by (auto simp: pre_digraph.del_arc_simps perm_restrict_simps arev_dom)
qed (auto simp: pre_digraph.del_arc_simps perm_restrict_simps arev_dom)

lemma (in bidirected_digraph) bidirected_digraph_del_vert: "bidirected_digraph (del_vert u) (perm_restrict arev (arcs (del_vert u)))"
  by unfold_locales (auto simp: del_vert_simps perm_restrict_simps arev_dom)

lemma (in pre_digraph) ends_del_arc: "arc_to_ends (del_arc u) = arc_to_ends G"
  by (simp add: arc_to_ends_def fun_eq_iff)

lemma (in pre_digraph) dominates_arcsD:
  assumes "v \<rightarrow>\<^bsub>del_arc u\<^esub> w" shows "v \<rightarrow>\<^bsub>G\<^esub> w"
  using assms by (auto simp: arcs_ends_def ends_del_arc)

lemma (in wf_digraph) reachable_del_arcD:
  assumes "v \<rightarrow>\<^sup>*\<^bsub>del_arc u\<^esub> w" shows "v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> w"
proof -
  interpret H: wf_digraph "del_arc u" by (rule wf_digraph_del_arc)
  from assms show ?thesis
    by (induct) (auto dest: dominates_arcsD intro: adj_reachable_trans)
qed

lemma (in fin_digraph) finite_isolated_verts[intro!]: "finite isolated_verts"
  by (auto simp: isolated_verts_def)

lemma (in wf_digraph) isolated_verts_in_sccs:
  assumes "u \<in> isolated_verts" shows "{u} \<in> sccs_verts"
proof -
  have "v = u" if "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v" for v
    using that assms by induct (auto simp: arcs_ends_def arc_to_ends_def isolated_verts_def)
  with assms show ?thesis by (auto simp: sccs_verts_def isolated_verts_def)
qed

lemma (in digraph_map) in_face_cycle_sets:
  "a \<in> arcs G \<Longrightarrow> face_cycle_set a \<in> face_cycle_sets"
  by (auto simp: face_cycle_sets_def)

lemma (in digraph_map) heads_face_cycle_set:
  assumes "a \<in> arcs G"
  shows "head G ` face_cycle_set a = tail G ` face_cycle_set a" (is "?L = ?R")
proof (intro set_eqI iffI)
  fix u assume "u \<in> ?L"
  then obtain b where "b \<in> face_cycle_set a" "head G b = u" by blast
  then have "face_cycle_succ b \<in> face_cycle_set a" "tail G (face_cycle_succ b) = u"
    using assms by (auto simp: tail_face_cycle_succ face_cycle_succ_inI in_face_cycle_setD)
  then show "u \<in> ?R" by auto
next
  fix u assume "u \<in> ?R"
  then obtain b where "b \<in> face_cycle_set a" "tail G b = u" by blast
  moreover
  then obtain c where "b = face_cycle_succ c" by (metis face_cycle_succ_pred)
  ultimately
  have "c \<in> face_cycle_set a" "head G c = u" 
    by (auto dest: face_cycle_succ_inD) (metis assms face_cycle_succ_no_arc in_face_cycle_setD tail_face_cycle_succ)
  then show "u \<in> ?L" by auto
qed

lemma (in pre_digraph) casI_nth:
  assumes "p \<noteq> []" "u = tail G (hd p)" "v = head G (last p)" "\<And>i. Suc i < length p \<Longrightarrow> head G (p ! i) = tail G (p ! Suc i)"
  shows "cas u p v"
  using assms
proof (induct p arbitrary: u)
  case Nil then show ?case by simp
next
  case (Cons a p)
  have "cas (head G a) p v"
  proof (cases "p = []")
    case False then show ?thesis
      using Cons.prems(1-3) Cons.prems(4)[of 0] Cons.prems(4)[of "Suc i" for i]
      by (intro Cons) (simp_all add: hd_conv_nth)
  qed (simp add: Cons)
  with Cons show ?case by simp
qed

lemma (in digraph_map) obtain_trail_in_fcs:
  assumes "a \<in> arcs G" "a0 \<in> face_cycle_set a" "an \<in> face_cycle_set a"
  obtains p where "trail (tail G a0) p (head G an)" "p \<noteq> []" "hd p = a0"  "last p = an"
    "set p \<subseteq> face_cycle_set a"
proof -
  have fcs_a: "face_cycle_set a = orbit face_cycle_succ a0"
    using assms face_cycle_eq by (simp add: face_cycle_set_def)
  have "a0 = (face_cycle_succ ^^ 0) a0" by simp
  have "an = (face_cycle_succ ^^ funpow_dist face_cycle_succ a0 an) a0"
    using assms by (simp add: fcs_a funpow_dist_prop)

  define p where "p = map (\<lambda>n. (face_cycle_succ ^^ n) a0) [0..<Suc (funpow_dist face_cycle_succ a0 an)]"
  have p_nth: "\<And>i. i < length p \<Longrightarrow> p ! i = (face_cycle_succ ^^ i) a0"
    by (auto simp: p_def simp del: upt_Suc)

  have P2: "p \<noteq> []" by (simp add: p_def)
  have P3: "hd p = a0" using \<open>a0 = _\<close> by (auto simp: p_def hd_map simp del: upt_Suc)
  have P4: "last p = an" using \<open>an = _\<close> by (simp add: p_def)
  have P5: "set p \<subseteq> face_cycle_set a"
    unfolding p_def fcs_a orbit_altdef_permutation[OF permutation_face_cycle_succ] by auto

  have P1: "trail (tail G a0) p (head G an)"
  proof -
    have "distinct p"
    proof -
      have "an \<in> orbit face_cycle_succ a0" using assms by (simp add: fcs_a)
      then have "inj_on (\<lambda>n. (face_cycle_succ ^^ n) a0) {0..funpow_dist face_cycle_succ a0 an}"
        by (rule inj_on_funpow_dist)
      also have "{0..funpow_dist face_cycle_succ a0 an} = (set [0..<Suc (funpow_dist face_cycle_succ a0 an)])"
        by auto
      finally have "inj_on (\<lambda>n. (face_cycle_succ ^^ n) a0) (set [0..<Suc (funpow_dist face_cycle_succ a0 an)])" .
      then show "distinct p" by (simp add: distinct_map p_def)
    qed
    moreover
    have "a0 \<in> arcs G" by (metis assms(1-2) in_face_cycle_setD) 
    then have "tail G a0 \<in> verts G" by simp
    moreover
    have "set p \<subseteq> arcs G" using P5
      by (metis assms(1) in_face_cycle_setD subset_code(1)) 
    moreover
    then have "\<And>i. Suc i < length p \<Longrightarrow> p ! Suc i \<in> arcs G" by auto
    then have "\<And>i. Suc i < length p \<Longrightarrow> head G (p ! i) = tail G (p ! Suc i)"
      by (auto simp: p_nth tail_face_cycle_succ)
    ultimately
    show ?thesis
      using P2 P3 P4 unfolding trail_def awalk_def by (auto intro: casI_nth)
  qed

  from P1 P2 P3 P4 P5 show ?thesis ..
qed

lemma (in digraph_map) obtain_trail_in_fcs':
  assumes "a \<in> arcs G" "u \<in> tail G ` face_cycle_set a" "v \<in> tail G ` face_cycle_set a"
  obtains p where "trail u p v" "set p \<subseteq> face_cycle_set a"
proof -
  from assms obtain a0 where "tail G a0 = u" "a0 \<in> face_cycle_set a" by auto
  moreover
  from assms obtain an where "head G an = v" "an \<in> face_cycle_set a"
    by (auto simp: heads_face_cycle_set[symmetric])
  ultimately obtain p where "trail u p v" "set p \<subseteq> face_cycle_set a"
    using \<open>a \<in> arcs G\<close> by (metis obtain_trail_in_fcs)
  then show ?thesis ..
qed




subsection \<open>Deleting an isolated vertex\<close>

locale del_vert_props = digraph_map +
  fixes u
  assumes u_in: "u \<in> verts G"
  assumes u_isolated: "out_arcs G u = {}"

begin

  lemma u_isolated_in: "in_arcs G u = {}"
    using u_isolated by (simp add: in_arcs_eq)

  lemma arcs_dv: "arcs (del_vert u) = arcs G" 
    using u_isolated u_isolated_in by (auto simp: del_vert_simps)

  lemma out_arcs_dv: "out_arcs (del_vert u) = out_arcs G"
    by (auto simp: fun_eq_iff arcs_dv tail_del_vert)

  lemma digraph_map_del_vert:
    shows "digraph_map (del_vert u) M"
  proof -
    have "perm_restrict (edge_rev M) (arcs (del_vert u)) = edge_rev M"
      using has_dom_arev arcs_dv by (auto simp: perm_restrict_dom_subset)
    then interpret H: bidirected_digraph "del_vert u" "edge_rev M"
      using bidirected_digraph_del_vert[of u] by simp  
    show ?thesis
      by unfold_locales (auto simp: arcs_dv edge_succ_permutes out_arcs_dv edge_succ_cyclic verts_del_vert)
  qed

end

sublocale del_vert_props \<subseteq> H: digraph_map "del_vert u" M by (rule digraph_map_del_vert)

context del_vert_props begin

  lemma card_verts_dv: "card (verts G) = Suc (card (verts (del_vert u)))"
    by (auto simp: verts_del_vert) (rule card.remove, auto simp: u_in)

  lemma card_arcs_dv: "card (arcs (del_vert u)) = card (arcs G)"
    using u_isolated by (auto simp add: arcs_dv in_arcs_eq)

  lemma isolated_verts_dv: "H.isolated_verts = isolated_verts - {u}"
    by (auto simp: isolated_verts_def H.isolated_verts_def verts_del_vert out_arcs_dv)

  lemma u_in_isolated_verts: "u \<in> isolated_verts"
    using u_in u_isolated by (auto simp: isolated_verts_def)

  lemma card_isolated_verts_dv: "card isolated_verts = Suc (card H.isolated_verts)"
    by (simp add: isolated_verts_dv) (rule card.remove, auto simp: u_in_isolated_verts)

  lemma face_cycles_dv: "H.face_cycle_sets = face_cycle_sets"
    unfolding H.face_cycle_sets_def face_cycle_sets_def arcs_dv ..

  lemma euler_char_dv: "euler_char = 1 + H.euler_char"
    by (auto simp: euler_char_def H.euler_char_def card_arcs_dv card_verts_dv face_cycles_dv)

  lemma adj_dv: "v \<rightarrow>\<^bsub>del_vert u\<^esub> w \<longleftrightarrow> v \<rightarrow>\<^bsub>G\<^esub> w"
    by (auto simp: arcs_ends_def arcs_dv ends_del_vert)

  lemma reachable_del_vertD:
    assumes "v \<rightarrow>\<^sup>*\<^bsub>del_vert u\<^esub> w" shows "v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> w"
    using assms by induct (auto simp: verts_del_vert adj_dv intro: adj_reachable_trans)

  lemma reachable_del_vertI:
    assumes "v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> w" "u \<noteq> v \<or> u \<noteq> w" shows "v \<rightarrow>\<^sup>*\<^bsub>del_vert u\<^esub> w"
    using assms
  proof induct
    case (step x y)
    from \<open>x \<rightarrow>\<^bsub>G\<^esub> y\<close> obtain a where "a \<in> arcs G" "head G a = y" by auto
    then have "a \<in> in_arcs G y" by auto
    then have "y \<noteq> u" using u_isolated in_arcs_eq[of u] by auto
    with step show ?case by (auto simp: adj_dv intro: H.adj_reachable_trans)
  qed (auto simp: verts_del_vert)

  lemma G_reach_conv: "v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> w \<longleftrightarrow> v \<rightarrow>\<^sup>*\<^bsub>del_vert u\<^esub> w \<or> (v = u \<and> w = u)"
    by (auto dest: reachable_del_vertI reachable_del_vertD intro: u_in)

  lemma sccs_verts_dv: "H.sccs_verts = sccs_verts - {{u}}" (is "?L = ?R")
  proof -
    have *:"\<And>S x. S \<in> sccs_verts \<Longrightarrow> S \<notin> H.sccs_verts  \<Longrightarrow> x \<in> S \<Longrightarrow> x = u"
      by (simp add: H.in_sccs_verts_conv_reachable in_sccs_verts_conv_reachable G_reach_conv)
        (meson H.reachable_trans)
    show ?thesis
      by (auto dest: *) (auto simp: H.in_sccs_verts_conv_reachable in_sccs_verts_conv_reachable
        G_reach_conv H.reachable_refl_iff verts_del_vert)
  qed

  lemma card_sccs_verts_dv: "card sccs_verts = Suc (card H.sccs_verts)"
    unfolding sccs_verts_dv
    by (rule card.remove) (auto simp: isolated_verts_in_sccs u_in_isolated_verts finite_sccs_verts)

  lemma card_sccs_dv: "card sccs = Suc (card H.sccs)"
    using card_sccs_verts_dv by (simp add: card_sccs_verts H.card_sccs_verts)

  lemma euler_genus_eq: "H.euler_genus = euler_genus"
    by (auto simp: pre_digraph_map.euler_genus_def card_sccs_dv card_isolated_verts_dv euler_char_dv)

end



subsection \<open>Deleting an arc pair\<close>

locale bidel_arc = G: digraph_map +
  fixes a
  assumes a_in: "a \<in> arcs G"

begin

  abbreviation "a' \<equiv> edge_rev M a"

  definition H :: "('a,'b) pre_digraph" where
    "H \<equiv> pre_digraph.del_arc (pre_digraph.del_arc G a') a"

  definition HM :: "'b pre_map" where
    "HM = 
      \<lparr> edge_rev = perm_restrict (edge_rev M) (arcs G - {a, a'})
      , edge_succ = perm_rem a (perm_rem a' (edge_succ M))
      \<rparr>"

  lemma
    verts_H: "verts H = verts G" and
    arcs_H:  "arcs H = arcs G - {a, a'}" and
    tail_H: "tail H = tail G" and
    head_H: "head H = head G" and
    ends_H: "arc_to_ends H = arc_to_ends G"and
    arcs_in: "{a,a'} \<subseteq> arcs G" and
    ends_in: "{tail G a, head G a} \<subseteq> verts G"
    by (auto simp: H_def pre_digraph.del_arc_simps a_in arc_to_ends_def)

  lemma cyclic_on_edge_succ:
    assumes "x \<in> verts H" "out_arcs H x \<noteq> {}"
    shows "cyclic_on (edge_succ HM) (out_arcs H x)"
  proof -
    have oa_H: "out_arcs H x = (out_arcs G x - {a'}) - {a}" by (auto simp: arcs_H tail_H)
    have "cyclic_on (perm_rem a (perm_rem a' (edge_succ M))) (out_arcs G x - {a'} - {a})"
      using assms
      by (intro cyclic_on_perm_rem G.edge_succ_cyclic) (auto simp: oa_H G.bij_edge_succ G.edge_succ_cyclic)
    then show ?thesis by (simp add: HM_def oa_H)
  qed

  lemma digraph_map: "digraph_map H HM"
  proof -
    interpret fin_digraph H unfolding H_def
      by (rule fin_digraph.fin_digraph_del_arc) (rule G.fin_digraph_del_arc)
    interpret bidirected_digraph H "edge_rev HM" unfolding H_def
      using G.bidirected_digraph_del_arc[of a] by (auto simp: HM_def)
    have *: "insert a' (insert a (arcs H)) = arcs G" using a_in by (auto simp: arcs_H)
    have "edge_succ HM permutes arcs H"
      unfolding HM_def by (auto simp: * intro!: perm_rem_permutes G.edge_succ_permutes)
    moreover
    { fix v assume "v \<in> verts H" "out_arcs H v \<noteq> {}"
      then have "cyclic_on (edge_succ HM) (out_arcs H v)" by (rule cyclic_on_edge_succ)
    }
    ultimately
    show ?thesis by unfold_locales
  qed

  lemma rev_H: "bidel_arc.H G M a' = H" (is ?t1)
    and rev_HM: "bidel_arc.HM G M a' = HM" (is ?t2)
  proof -
    interpret rev: bidel_arc G M a' using a_in by unfold_locales simp
    show ?t1
      by (rule pre_digraph.equality) (auto simp: rev.verts_H verts_H rev.arcs_H arcs_H
        rev.tail_H tail_H rev.head_H head_H)
    show ?t2 using G.edge_succ_permutes
      by (intro pre_map.equality) (auto simp: HM_def rev.HM_def insert_commute
        perm_rem_commutes permutes_conv_has_dom)
  qed

end

sublocale bidel_arc \<subseteq> H: digraph_map H HM by (rule digraph_map)

context bidel_arc begin

  lemma a_neq_a': "a \<noteq> a'"
    by (metis G.arev_neq a_in)

  lemma
    arcs_G: "arcs G = insert a (insert a' (arcs H))" and
    arcs_not_in: "{a,a'} \<inter> arcs H = {}"
    using arcs_in by (auto simp: arcs_H)

  lemma card_arcs_da: "card (arcs G) = 2 + card (arcs H)"
    using arcs_G arcs_not_in a_neq_a' by (auto simp: card_insert_if)

  lemma cas_da: "H.cas = G.cas"
  proof -
    { fix u p v have "H.cas u p v = G.cas u p v"
        by (induct p arbitrary: u) (simp_all add: tail_H head_H)
    } then show ?thesis by (simp add: fun_eq_iff)
  qed

  lemma reachable_daD:
    assumes "v \<rightarrow>\<^sup>*\<^bsub>H\<^esub> w" shows "v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> w"
    apply (rule G.reachable_del_arcD)
    apply (rule wf_digraph.reachable_del_arcD)
    apply (rule G.wf_digraph_del_arc)
    using assms unfolding H_def by assumption

  lemma not_G_isolated_a: "{tail G a, head G a} \<inter> G.isolated_verts = {}"
    using a_in G.in_arcs_eq[of "head G a"] by (auto simp: G.isolated_verts_def)

  lemma isolated_other_da:
    assumes "u \<notin> {tail G a, head G a}" shows "u \<in> H.isolated_verts \<longleftrightarrow> u \<in> G.isolated_verts"
    using assms by (auto simp: pre_digraph.isolated_verts_def verts_H arcs_H tail_H out_arcs_def)

  lemma isolated_da_pre: "H.isolated_verts = G.isolated_verts \<union>
      (if tail G a \<in> H.isolated_verts then {tail G a} else {}) \<union>
      (if head G a \<in> H.isolated_verts then {head G a} else {})" (is "?L = ?R")
  proof (intro set_eqI iffI)
    fix x assume "x \<in> ?L" then show "x \<in> ?R"
      by (cases "x \<in> {tail G a, head G a}") (auto simp:isolated_other_da)
  next
    fix x assume "x \<in> ?R" then show "x \<in> ?L" using not_G_isolated_a
      by (cases "x \<in> {tail G a, head G a}") (auto simp:isolated_other_da split: if_splits)
  qed

  lemma card_isolated_verts_da0:
    "card H.isolated_verts = card G.isolated_verts + card ({tail G a, head G a} \<inter> H.isolated_verts)"
    using not_G_isolated_a by (subst isolated_da_pre) (auto simp: card_insert_if G.finite_isolated_verts)

  lemma segments_neq:
    assumes "segment G.face_cycle_succ a' a \<noteq> {} \<or> segment G.face_cycle_succ a a' \<noteq> {}"
    shows "segment G.face_cycle_succ a a' \<noteq> segment G.face_cycle_succ a' a"
  proof -
    have bij_fcs: "bij G.face_cycle_succ"
      using G.face_cycle_succ_permutes by (auto simp: permutes_conv_has_dom)
    show ?thesis using segment_disj[OF a_neq_a' bij_fcs] assms by auto
  qed

  lemma H_fcs_eq_G_fcs:
    assumes "b \<in> arcs G" "{b,G.face_cycle_succ b} \<inter> {a,a'} = {}" 
    shows "H.face_cycle_succ b = G.face_cycle_succ b"
  proof -
    have "edge_rev M b \<notin> {a,a'}"
      using assms by auto (metis G.arev_arev)
    then show ?thesis
      using assms unfolding G.face_cycle_succ_def H.face_cycle_succ_def
      by (auto simp: HM_def perm_restrict_simps perm_rem_simps G.bij_edge_succ)
  qed

  lemma face_cycle_set_other_da:
    assumes "{a, a'} \<inter> G.face_cycle_set b = {}" "b \<in> arcs G"
    shows "H.face_cycle_set b = G.face_cycle_set b"
  proof -
    have "\<And>s. s \<in> G.face_cycle_set b \<Longrightarrow> b \<in> arcs G \<Longrightarrow> a \<notin> G.face_cycle_set b \<Longrightarrow> a' \<notin> G.face_cycle_set b
        \<Longrightarrow> pre_digraph_map.face_cycle_succ HM s = G.face_cycle_succ s"
      by (subst H_fcs_eq_G_fcs) (auto simp: G.in_face_cycle_setD G.face_cycle_succ_inI)
    then show ?thesis
      using assms unfolding pre_digraph_map.face_cycle_set_def
      by (intro orbit_cong) (auto simp add: pre_digraph_map.face_cycle_set_def[symmetric])
  qed

  lemma in_face_cycle_set_other:
    assumes "S \<in> G.face_cycle_sets" "{a, a'} \<inter> S = {}"
    shows "S \<in> H.face_cycle_sets"
  proof -
    from assms obtain b where "S = G.face_cycle_set b" "b \<in> arcs G"
      by (auto simp: G.face_cycle_sets_def)
    with assms have "S = H.face_cycle_set b" by (simp add: face_cycle_set_other_da)
    moreover
    with assms have "b \<in> arcs H" using \<open>b \<in> arcs G\<close> by (auto simp: arcs_H)
    ultimately show ?thesis by (auto simp: H.face_cycle_sets_def)
  qed

  lemma H_fcs_in_G_fcs:
    assumes "b \<in> arcs H - (G.face_cycle_set a \<union> G.face_cycle_set a')"
    shows "H.face_cycle_set b \<in> G.face_cycle_sets - {G.face_cycle_set a, G.face_cycle_set a'}"
  proof -
    have "H.face_cycle_set b = G.face_cycle_set b"
      using assms by (intro face_cycle_set_other_da) (auto simp: arcs_H G.face_cycle_eq)
    moreover have "G.face_cycle_set b \<notin> {G.face_cycle_set a, G.face_cycle_set a'}" "b \<in> arcs G"
      using G.face_cycle_eq assms by (auto simp: arcs_H)
    ultimately show ?thesis by (auto simp: G.face_cycle_sets_def)
  qed

  lemma face_cycle_sets_da0:
    "H.face_cycle_sets = G.face_cycle_sets - {G.face_cycle_set a, G.face_cycle_set a'}
      \<union> H.face_cycle_set ` ((G.face_cycle_set a \<union> G.face_cycle_set a') - {a,a'})" (is "?L = ?R")
  proof (intro set_eqI iffI)
    fix S assume "S \<in> ?L"
    then obtain b where "S = H.face_cycle_set b" "b \<in> arcs H" by (auto simp: H.face_cycle_sets_def)
    then show "S \<in> ?R"
      using arcs_not_in H_fcs_in_G_fcs by (cases "b \<in> G.face_cycle_set a \<union> G.face_cycle_set a'") auto
  next
    fix S assume "S \<in> ?R"
    show "S \<in> ?L"
    proof (cases "S \<in> G.face_cycle_sets - {G.face_cycle_set a, G.face_cycle_set a'}")
      case True
      then have "S \<inter> {a,a'} = {}" using G.face_cycle_set_parts by (auto simp: G.face_cycle_sets_def)
      with True show ?thesis by (intro in_face_cycle_set_other) auto
    next
      case False
      then have "S \<in> H.face_cycle_set ` ((G.face_cycle_set a \<union> G.face_cycle_set a') - {a,a'})"
        using \<open>S \<in> ?R\<close> by blast
      moreover have "(G.face_cycle_set a \<union> G.face_cycle_set a') - {a,a'} \<subseteq> arcs H"
        using a_in by (auto simp: arcs_H dest: G.in_face_cycle_setD)
      ultimately show ?thesis by (auto simp: H.face_cycle_sets_def)
    qed
  qed
    
  lemma card_fcs_aa'_le: "card {G.face_cycle_set a, G.face_cycle_set a'} \<le> card G.face_cycle_sets"
    using a_in by (intro card_mono) (auto simp: G.face_cycle_sets_def)

  lemma card_face_cycle_sets_da0:
    "card H.face_cycle_sets = card G.face_cycle_sets - card {G.face_cycle_set a, G.face_cycle_set a'}
      + card (H.face_cycle_set ` ((G.face_cycle_set a \<union> G.face_cycle_set a') - {a,a'}))"
  proof -
    have face_cycle_sets_inter:
      "(G.face_cycle_sets - {G.face_cycle_set a, G.face_cycle_set a'}) \<inter> H.face_cycle_set ` ((G.face_cycle_set a \<union> G.face_cycle_set a') - {a, a'}) = {}" (is "?L \<inter> ?R = _")
    proof -
      define L R P
        where "L = ?L" and "R = ?R" and "P x \<longleftrightarrow> x \<inter> (G.face_cycle_set a \<union> G.face_cycle_set a') = {}"
        for x
      then have "\<And>x. x \<in> L \<Longrightarrow> P x" "\<And>x. x \<in> R \<Longrightarrow> \<not>P x"
        using G.face_cycle_set_parts by (auto simp: G.face_cycle_sets_def)
      then have "L \<inter> R = {}" by blast
      then show ?thesis unfolding L_def R_def .
    qed
    then show ?thesis using arcs_G
      by (simp add: card_Diff_subset[symmetric] card_Un_disjoint[symmetric]
        G.in_face_cycle_sets face_cycle_sets_da0)
  qed

end


locale bidel_arc_same_face = bidel_arc +
  assumes same_face: "G.face_cycle_set a' = G.face_cycle_set a"
begin
  lemma a_in_o: "a \<in> orbit G.face_cycle_succ a'"
    unfolding G.face_cycle_set_def[symmetric] by (simp add: same_face)

  lemma segment_a'_a_in: "segment G.face_cycle_succ a' a \<subseteq> arcs H" (is "?seg \<subseteq> _")
  proof -
    have "?seg \<subseteq> G.face_cycle_set a'" by (auto simp: G.face_cycle_set_def segmentD_orbit)
    moreover have "G.face_cycle_set a' \<subseteq> arcs G" by (auto simp: G.face_cycle_set_altdef a_in)
    ultimately show ?thesis using a_in_o by (auto simp: arcs_H a_in not_in_segment1 not_in_segment2)
  qed

  lemma segment_a'_a_neD:
    assumes "segment G.face_cycle_succ a' a \<noteq> {}"
    shows "segment G.face_cycle_succ a' a \<in> H.face_cycle_sets" (is "?seg \<in> _")
  proof -
    let ?b = "G.face_cycle_succ a'"

    have fcs_a_neq_a': "G.face_cycle_succ a' \<noteq> a" by (metis assms segment1_empty)

    have in_aG: "\<And>x. x \<in> segment G.face_cycle_succ a' a \<Longrightarrow> x \<in> arcs G - {a,a'}"
        using not_in_segment1 not_in_segment2 segment_a'_a_in by (auto simp: arcs_H)

    { fix x assume A: "x \<in> segment G.face_cycle_succ a' a" and B: "G.face_cycle_succ x \<noteq> a"
      from A have "G.face_cycle_succ x \<noteq> a'"
      proof induct
        case base then show ?case
          by (metis a_neq_a' G.face_cycle_set_self not_in_segment1 G.face_cycle_set_def same_face segment.intros)
      next
        case step then show ?case by (metis a_in_o a_neq_a' not_in_segment1 segment.step)
      qed
      with A B have "{x, G.face_cycle_succ x} \<inter> {a, a'} = {}"
        using not_in_segment1[OF a_in_o] not_in_segment2[of a G.face_cycle_succ a'] by safe
      with in_aG have "H.face_cycle_succ x = G.face_cycle_succ x" by (intro H_fcs_eq_G_fcs) (auto intro: A)
    } note fcs_x_eq = this

    { fix x assume A: "x \<in> segment G.face_cycle_succ a' a" and B: "G.face_cycle_succ x = a"
      have "G.face_cycle_succ a \<noteq> a" using B in_aG[OF A] G.bij_face_cycle_succ by (auto simp: bij_eq_iff)
      then have "edge_succ M a \<noteq> edge_rev M a"
        by (metis a_in_o G.arev_arev comp_apply G.face_cycle_succ_def not_in_segment1 segment.base)
      then have "H.face_cycle_succ x = G.face_cycle_succ a'"
        using in_aG[OF A] B G.bij_edge_succ unfolding H.face_cycle_succ_def G.face_cycle_succ_def
        by (auto simp: HM_def perm_restrict_simps perm_rem_conv G.arev_eq_iff)
    } note fcs_last_x_eq = this

    have "segment G.face_cycle_succ a' a = H.face_cycle_set ?b"
    proof (intro set_eqI iffI)
      fix x assume "x \<in> segment G.face_cycle_succ a' a"
      then show "x \<in> H.face_cycle_set ?b"
      proof induct
        case base then show ?case by auto
      next
        case (step x) then show ?case by (subst fcs_x_eq[symmetric]) (auto simp: H.face_cycle_succ_inI)
      qed
    next
      fix x assume A: "x \<in> H.face_cycle_set ?b"
      then show "x \<in> segment G.face_cycle_succ a' a"
      proof induct
        case base then show ?case by (intro segment.base fcs_a_neq_a')
      next
        case (step x) then show ?case using fcs_a_neq_a'
          by (cases "G.face_cycle_succ x = a") (auto simp: fcs_last_x_eq fcs_x_eq intro: segment.intros)
      qed
    qed
    then show ?thesis using segment_a'_a_in by (auto simp:  H.face_cycle_sets_def)
  qed

  lemma segment_a_a'_neD:
    assumes "segment G.face_cycle_succ a a' \<noteq> {}"
    shows "segment G.face_cycle_succ a a' \<in> H.face_cycle_sets"
  proof -
    interpret rev: bidel_arc_same_face G M a'
      using a_in same_face by unfold_locales simp_all
    from assms show ?thesis using rev.segment_a'_a_neD by (simp add: rev_H rev_HM)
  qed

  lemma H_fcs_full:
    assumes "SS \<subseteq> H.face_cycle_sets" shows "H.face_cycle_set ` (\<Union>SS) = SS"
  proof -
   
    { fix x assume "x \<in> \<Union>SS"
      then obtain S where "S \<in> SS" "x \<in> S" "S \<in> H.face_cycle_sets" using assms by auto
      then have "H.face_cycle_set x = S"
        using H.face_cycle_set_parts by (auto simp: H.face_cycle_sets_def)
      then have "H.face_cycle_set x \<in> SS" using \<open>S \<in> SS\<close> by auto
    }
    moreover
    { fix S assume "S \<in> SS"
      then obtain x where "x \<in> arcs H" "S = H.face_cycle_set x" "x \<in> S"
        using assms by (auto simp: H.face_cycle_sets_def)
      then have "S \<in> H.face_cycle_set ` \<Union>SS"
        using \<open>S \<in> SS\<close> by auto
    }
    ultimately show ?thesis by auto
  qed

  lemma card_fcs_gt_0: "0 < card G.face_cycle_sets"
    using a_in by (auto simp: card_gt_0_iff dest: G.in_face_cycle_sets)

  lemma card_face_cycle_sets_da':
    "card H.face_cycle_sets = card G.face_cycle_sets - 1
      + card ({segment G.face_cycle_succ a a', segment G.face_cycle_succ a' a, {}} - {{}})"
  proof -
    have "G.face_cycle_set a
        = {a,a'} \<union> segment G.face_cycle_succ a a' \<union> segment G.face_cycle_succ a' a"
      using a_neq_a' same_face by (intro cyclic_split_segment) (auto simp: G.face_cycle_succ_cyclic)
    then have *: "G.face_cycle_set a \<union> G.face_cycle_set a' - {a, a'} = segment G.face_cycle_succ a a' \<union> segment G.face_cycle_succ a' a"
      by (auto simp: same_face G.face_cycle_set_def[symmetric] not_in_segment1 not_in_segment2)

    have **: "H.face_cycle_set ` (G.face_cycle_set a \<union> G.face_cycle_set a' - {a, a'})
        = (if segment G.face_cycle_succ a a' \<noteq> {} then {segment G.face_cycle_succ a a'} else {})
        \<union> (if segment G.face_cycle_succ a' a \<noteq> {} then {segment G.face_cycle_succ a' a} else {})"
      unfolding *
      using H_fcs_full[of "{segment G.face_cycle_succ a a', segment G.face_cycle_succ a' a}"]
      using H_fcs_full[of "{segment G.face_cycle_succ a a'}"]
      using H_fcs_full[of "{segment G.face_cycle_succ a' a}"]
      by (auto simp add: segment_a_a'_neD segment_a'_a_neD)
    show ?thesis
      unfolding card_face_cycle_sets_da0 ** by (simp add: same_face card_insert_if)
  qed

end

locale bidel_arc_diff_face = bidel_arc +
  assumes diff_face: "G.face_cycle_set a' \<noteq> G.face_cycle_set a"
begin

  definition S :: "'b set" where
    "S \<equiv> segment G.face_cycle_succ a a \<union> segment G.face_cycle_succ a' a'"

  lemma diff_face_not_in: "a \<notin> G.face_cycle_set a'" "a' \<notin> G.face_cycle_set a"
    using diff_face G.face_cycle_eq by auto

  lemma H_fcs_eq_for_a:
    assumes "b \<in> arcs H \<inter> G.face_cycle_set a"
    shows "H.face_cycle_set b = S" (is "?L = ?R")
  proof (intro set_eqI iffI)
    fix c assume "c \<in> ?L"
    then have "c \<in> arcs H" using assms by (auto dest: H.in_face_cycle_setD)
    moreover
    have "c \<in> G.face_cycle_set a \<union> G.face_cycle_set a'"
    proof (rule ccontr)
      assume A: "\<not>?thesis"
      then have "G.face_cycle_set c \<inter> (G.face_cycle_set a \<union> G.face_cycle_set a') = {}"
        using G.face_cycle_set_parts by (auto simp: arcs_H)
      also then have "G.face_cycle_set c = H.face_cycle_set c"
        using \<open>c \<in> arcs H\<close> by (subst face_cycle_set_other_da) (auto simp: arcs_H)
      also have "\<dots> = H.face_cycle_set b"
        using \<open>c \<in> ?L\<close> using H.face_cycle_set_parts by auto
      finally show False using assms by auto
    qed
    ultimately show "c \<in> ?R" unfolding S_def arcs_H G.segment_face_cycle_x_x_eq by auto

  next
    fix x assume "x \<in> ?R"

    from assms have "a \<noteq> b" by (auto simp: arcs_H)
    from assms have b_in: "b \<in> segment G.face_cycle_succ a a"
      using G.segment_face_cycle_x_x_eq by (auto simp: arcs_H)
    have fcs_a_neq_a: "G.face_cycle_succ a \<noteq> a"
      using assms \<open>a \<noteq> b\<close> by (auto simp add: G.segment_face_cycle_x_x_eq G.fcs_x_eq_x)

    have split_seg: "segment G.face_cycle_succ a a = segment G.face_cycle_succ a b \<union> {b}
        \<union> segment G.face_cycle_succ b a"
      using b_in by (intro segment_split)

    have a_in_orb_a: "a \<in> orbit G.face_cycle_succ a" by (simp add: G.face_cycle_set_def[symmetric])

    define c where "c = inv G.face_cycle_succ a"
    have c_succ: "G.face_cycle_succ c = a" unfolding c_def
      by (meson bij_inv_eq_iff permutation_bijective G.permutation_face_cycle_succ)
    have c_in_aa: "c \<in> segment G.face_cycle_succ a a"
      unfolding G.segment_face_cycle_x_x_eq c_def using fcs_a_neq_a c_succ c_def by force
    have c_in: "c \<in> {b} \<union> segment G.face_cycle_succ b a"
      using split_seg b_in c_succ c_in_aa
      by (auto dest: not_in_segment1[OF segmentD_orbit] intro: segment.intros)
    from c_in_aa have "c \<in> arcs H" unfolding G.segment_face_cycle_x_x_eq
      using arcs_in c_succ diff_face by (auto simp: arcs_H G.face_cycle_eq[of a'])

    have b_in_L: "b \<in> ?L" by auto
    moreover
    { fix x assume "x \<in> segment G.face_cycle_succ b a" then have "x \<in> ?L"
      proof induct
        case base then show ?case
          using assms diff_face_not_in(2) by (subst H_fcs_eq_G_fcs[symmetric])
            (auto simp: arcs_H intro: H.face_cycle_succ_inI G.face_cycle_succ_inI)
      next
        case (step x)
        have "G.face_cycle_succ x \<notin> G.face_cycle_set a  \<Longrightarrow> b \<in> G.face_cycle_set a \<Longrightarrow> False"
          using step(1) by (metis G.face_cycle_eq G.face_cycle_succ_inI pre_digraph_map.face_cycle_set_def segmentD_orbit)
        moreover
        have "x \<in> arcs G"
          using step assms H.in_face_cycle_setD arcs_H by auto
        moreover
        then have "(G.face_cycle_succ x \<notin> G.face_cycle_set a \<Longrightarrow> b \<in> G.face_cycle_set a \<Longrightarrow> False) \<Longrightarrow> {x, G.face_cycle_succ x} \<inter> {a, a'} = {}"
          using step(2,3) assms diff_face_not_in(2)  H.in_face_cycle_setD arcs_H by safe auto
        ultimately show ?case using step
          by (subst H_fcs_eq_G_fcs[symmetric]) (auto  intro: H.face_cycle_succ_inI)
      qed
    } note sba_in_L = this
    moreover
    { fix x assume A: "x \<in> segment G.face_cycle_succ a' a'" then have "x \<in> ?L"
      proof -
        from c_in have "c \<in> ?L" using b_in_L sba_in_L by blast

        have "G.face_cycle_succ a' \<noteq> a'"
          using A by (auto simp add: G.segment_face_cycle_x_x_eq G.fcs_x_eq_x)
        then have *: "G.face_cycle_succ a' = H.face_cycle_succ c"
          using a_neq_a' c_succ \<open>c \<in> arcs H\<close> unfolding G.face_cycle_succ_def H.face_cycle_succ_def arcs_H
          by (auto simp: HM_def perm_restrict_simps perm_rem_conv G.bij_edge_succ G.arev_eq_iff)

        from A have "x \<in> H.face_cycle_set c"
        proof induct
          case base then show ?case by (simp add: * H.face_cycle_succ_inI)
        next
          case (step x)
          have "x \<in> arcs G"
            using\<open>c \<in> arcs H\<close> step.hyps(2) by (auto simp: arcs_H dest: H.in_face_cycle_setD)
          moreover
          have "G.face_cycle_succ x \<noteq> a' \<Longrightarrow>  {x, G.face_cycle_succ x} \<inter> {a, a'} = {}"
            using step(1) diff_face_not_in(1) G.face_cycle_succ_inI G.segment_face_cycle_x_x_eq
            by (auto simp: not_in_segment2)
          ultimately
          show ?case using step by (subst H_fcs_eq_G_fcs[symmetric]) (auto intro: H.face_cycle_succ_inI)
        qed
        also have "H.face_cycle_set c = ?L"
          using \<open>c \<in> ?L\<close> H.face_cycle_set_parts by auto
        finally show ?thesis .
      qed
    } note sa'a'_in_L = this
    moreover
    { assume A: "x \<in> segment G.face_cycle_succ a b"

      obtain d where "d \<in> ?L" and d_succ: "H.face_cycle_succ d = G.face_cycle_succ a"
      proof (cases "G.face_cycle_succ a' = a'")
        case True
        from c_in have "c \<in> ?L" using b_in_L sba_in_L by blast
        moreover
        have "H.face_cycle_succ c = G.face_cycle_succ a"
          using fcs_a_neq_a c_succ  a_neq_a' True \<open>c \<in> arcs H\<close>
          unfolding G.face_cycle_succ_def H.face_cycle_succ_def arcs_H
          by (auto simp: HM_def perm_restrict_simps arcs_H perm_rem_conv G.bij_edge_succ G.arev_eq_iff)
        ultimately show ?thesis ..
      next
        case False

        define d where "d = inv G.face_cycle_succ a'"
        have d_succ: "G.face_cycle_succ d = a'" unfolding d_def
          by (meson bij_inv_eq_iff permutation_bijective G.permutation_face_cycle_succ)
        have *: "d \<in> ?L"
          using sa'a'_in_L False
          by (metis DiffI d_succ empty_iff G.face_cycle_set_self G.face_cycle_set_succ insert_iff G.permutation_face_cycle_succ pre_digraph_map.face_cycle_set_def segment_x_x_eq)
        then have "d \<in> arcs H" using assms by (auto dest: H.in_face_cycle_setD)
        have "H.face_cycle_succ d = G.face_cycle_succ a"
          using fcs_a_neq_a a_neq_a' \<open>d \<in> arcs H\<close> d_succ
          unfolding G.face_cycle_succ_def H.face_cycle_succ_def arcs_H
          by (auto simp: HM_def perm_restrict_simps arcs_H perm_rem_conv G.bij_edge_succ G.arev_eq_iff)
        with * show ?thesis ..
      qed
      then have "d \<in> arcs H" using assms 
        by - (drule H.in_face_cycle_setD, auto)

      from A have "x \<in> H.face_cycle_set d"
      proof induct
        case base then show ?case by (simp add: d_succ[symmetric] H.face_cycle_succ_inI)
      next
        case (step x)
        moreover
        have "x \<in> arcs G"
          using \<open>d \<in> arcs H\<close> arcs_H digraph_map.in_face_cycle_setD step.hyps(2) by fastforce
        moreover
        have " {x, G.face_cycle_succ x} \<inter> {a, a'} = {}"
        proof -
          have "a \<noteq> x" using step(2) H.in_face_cycle_setD \<open>d \<in> arcs H\<close> arcs_not_in by blast
          moreover
          have "a \<noteq> G.face_cycle_succ x"
            by (metis b_in not_in_segment1 segment.step segmentD_orbit step(1))
          moreover
          have "a' \<noteq> x" "a' \<noteq> G.face_cycle_succ x"
            using step(1) diff_face_not_in(2) by (auto simp: G.face_cycle_set_def dest!: segmentD_orbit intro: orbit.step)
          ultimately
          show ?thesis by auto
        qed
        ultimately
        show ?case using step
          by (subst H_fcs_eq_G_fcs[symmetric]) (auto intro: H.face_cycle_succ_inI)
      qed
      also have "H.face_cycle_set d = ?L"
        using \<open>d \<in> ?L\<close> H.face_cycle_set_parts by auto
      finally have "x \<in> ?L" .
    }
    ultimately show "x \<in> ?L"
      using \<open>x \<in> ?R\<close> unfolding S_def split_seg by blast
  qed

  lemma HJ_fcs_eq_for_a':
    assumes "b \<in> arcs H \<inter> G.face_cycle_set a'"
    shows "H.face_cycle_set b = S"
  proof -
    interpret rev: bidel_arc_diff_face G M a'
      using arcs_in diff_face by unfold_locales simp_all
    show ?thesis using rev.H_fcs_eq_for_a assms by (auto simp: rev_H rev_HM S_def rev.S_def)
  qed

  lemma card_face_cycle_sets_da':
    "card H.face_cycle_sets = card G.face_cycle_sets - card {G.face_cycle_set a, G.face_cycle_set a'} + (if S = {} then 0 else 1)"
  proof -
    have "S = G.face_cycle_set a \<union> G.face_cycle_set a' - {a, a'}"
      unfolding S_def using diff_face_not_in
      by (auto simp: segment_x_x_eq G.permutation_face_cycle_succ G.face_cycle_set_def)
    moreover
    { fix x assume "x \<in> S"
      then have "x \<in> arcs H \<inter> (G.face_cycle_set a \<union> G.face_cycle_set a' - {a, a'})"
        unfolding \<open>S = _\<close> arcs_H using a_in by (auto intro: G.in_face_cycle_setD)
      then have "H.face_cycle_set x = S" using H_fcs_eq_for_a HJ_fcs_eq_for_a' by blast
    }
    then have "H.face_cycle_set ` S = (if S = {} then {} else {S})"
      by auto
    ultimately show ?thesis by (simp add: card_face_cycle_sets_da0)
  qed

end


locale bidel_arc_biconnected = bidel_arc +
  assumes reach_a: "tail G a \<rightarrow>\<^sup>*\<^bsub>H\<^esub> head G a"
begin

  lemma reach_a': "tail G a' \<rightarrow>\<^sup>*\<^bsub>H\<^esub> head G a'"
    using reach_a a_in by (simp add: symmetric_reachable H.sym_arcs)

  lemma
    tail_a': "tail G a' = head G a" and
    head_a': "head G a' = tail G a"
    using a_in by simp_all

  lemma reachable_daI:
    assumes "v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> w" shows "v \<rightarrow>\<^sup>*\<^bsub>H\<^esub> w"
  proof -
    have *: "\<And>v w. v \<rightarrow>\<^bsub>G\<^esub> w \<Longrightarrow> v \<rightarrow>\<^sup>*\<^bsub>H\<^esub> w"
      using reach_a reach_a' by (auto simp: arcs_ends_def ends_H arcs_G arc_to_ends_def tail_a')
    show ?thesis using assms by induct (auto simp: verts_H intro: * H.reachable_trans)
  qed

  lemma reachable_da: "v \<rightarrow>\<^sup>*\<^bsub>H\<^esub> w \<longleftrightarrow> v \<rightarrow>\<^sup>*\<^bsub>G\<^esub> w"
    by (metis reachable_daD reachable_daI)

  lemma sccs_verts_da: "H.sccs_verts = G.sccs_verts"
    by (auto simp: G.in_sccs_verts_conv_reachable H.in_sccs_verts_conv_reachable reachable_da)

  lemma card_sccs_da: "card H.sccs = card G.sccs"
    by (simp add: G.card_sccs_verts[symmetric] H.card_sccs_verts[symmetric] sccs_verts_da)

end


locale bidel_arc_not_biconnected = bidel_arc +
  assumes not_reach_a: "\<not>tail G a \<rightarrow>\<^sup>*\<^bsub>H\<^esub> head G a"
begin

  lemma H_awalkI: "G.awalk u p v \<Longrightarrow> {a,a'} \<inter> set p = {} \<Longrightarrow> H.awalk u p v"
    by (auto simp: pre_digraph.apath_def pre_digraph.awalk_def verts_H arcs_H cas_da)

  lemma tail_neq_head: "tail G a \<noteq> head G a"
    using not_reach_a a_in by (metis H.reachable_refl G.head_in_verts verts_H)

  lemma scc_of_tail_neq_head: "H.scc_of (tail G a) \<noteq> H.scc_of (head G a)"
  proof -
    have "tail G a \<in> H.scc_of (tail G a)" "head G a \<in> H.scc_of (head G a)"
      using ends_in by (auto simp: H.in_scc_of_self verts_H)
    with not_reach_a show ?thesis by (auto simp: H.scc_of_def)
  qed

  lemma scc_of_G_tail:
    assumes "u \<in> G.scc_of (tail G a)"
    shows "H.scc_of u = H.scc_of (tail G a) \<or> H.scc_of u = H.scc_of (head G a)"
  proof -
    from assms have "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> tail G a" by (auto simp: G.scc_of_def)
    then obtain p where p: "G.apath u p (tail G a)" by (auto simp: G.reachable_apath)

    show ?thesis
    proof (cases "head G a \<in> set (G.awalk_verts u p)")
      case True
      with p obtain p' q where "p = p' @ q" "G.awalk (head G a) q (tail G a)"
          and p': "G.awalk u p' (head G a)"
        unfolding G.apath_def by (metis G.awalk_decomp)
      moreover
      then have "tail G a \<in> set (tl (G.awalk_verts (head G a) q))"
        using tail_neq_head
        apply (cases q)
        apply (simp add: G.awalk_Nil_iff )
        apply (simp add: G.awalk_Cons_iff)
        by (metis G.awalkE G.awalk_verts_non_Nil last_in_set)
      ultimately
      have "tail G a \<notin> set (G.awalk_verts u p')"
        using G.apath_decomp_disjoint[OF p, of p' q "tail G a"] by auto
      with p' have "{a,a'} \<inter> set p' = {}"
        by (auto simp: G.set_awalk_verts G.apath_def) (metis a_in imageI G.head_arev)
      with p' show ?thesis unfolding G.apath_def by (metis H.scc_ofI_awalk H.scc_of_eq H_awalkI)
    next
      case False
      with p have "{a,a'} \<inter> set p = {}"
        by (auto simp: G.set_awalk_verts G.apath_def) (metis a_in imageI G.tail_arev)
      with p show ?thesis unfolding G.apath_def by (metis H.scc_ofI_awalk H.scc_of_eq H_awalkI)
    qed
  qed

  lemma scc_of_other:
    assumes "u \<notin> G.scc_of (tail G a)"
    shows "H.scc_of u = G.scc_of u"
    using assms
  proof (intro set_eqI iffI)
    fix v assume "v \<in> H.scc_of u" then show "v \<in> G.scc_of u"
      by (auto simp: H.scc_of_def G.scc_of_def intro: reachable_daD)
  next
    fix v assume "v \<in> G.scc_of u"
    then obtain p where p: "G.awalk u p v" by (auto simp: G.scc_of_def G.reachable_awalk)
    moreover 
    have "{a,a'} \<inter> set p = {}"
    proof -
      have "\<not>u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> tail G a" using assms by (metis G.scc_ofI_reachable)
      then have "\<And>p. \<not>G.awalk u p (tail G a)" by (metis G.reachable_awalk)
      then have "tail G a \<notin> set (G.awalk_verts u p)"
        using p by (auto dest: G.awalk_decomp)
      with p show ?thesis
        by (auto simp: G.set_awalk_verts G.apath_def) (metis a_in imageI G.head_arev)
    qed
    ultimately have "H.awalk u p v" by (rule H_awalkI)
    then show "v \<in> H.scc_of u" by (metis H.scc_ofI_reachable' H.reachable_awalk)
  qed

  lemma scc_of_tail_inter:
    "tail G a \<in> G.scc_of (tail G a) \<inter> H.scc_of (tail G a)"
    using ends_in by (auto simp: G.in_scc_of_self H.in_scc_of_self verts_H)

  lemma scc_of_head_inter:
    "head G a \<in> G.scc_of (tail G a) \<inter> H.scc_of (head G a)"
  proof -
    have "tail G a \<rightarrow>\<^bsub>G\<^esub> head G a" "head G a \<rightarrow>\<^bsub>G\<^esub> tail G a"
      by (metis a_in G.in_arcs_imp_in_arcs_ends) (metis a_in G.graph_symmetric G.in_arcs_imp_in_arcs_ends)
    then have "tail G a \<rightarrow>\<^sup>*\<^bsub>G\<^esub> head G a" "head G a \<rightarrow>\<^sup>*\<^bsub>G\<^esub> tail G a" by auto
    then show ?thesis using ends_in by (auto simp: G.scc_of_def H.in_scc_of_self verts_H)
  qed

  lemma G_scc_of_tail_not_in: "G.scc_of (tail G a) \<notin> H.sccs_verts"
  proof
    assume A: "G.scc_of (tail G a) \<in> H.sccs_verts"
    from A scc_of_tail_inter have "G.scc_of (tail G a) = H.scc_of (tail G a)"
      by (metis H.scc_of_in_sccs_verts H.sccs_verts_disjoint a_in empty_iff G.tail_in_verts verts_H)
    moreover
    from A scc_of_head_inter have "G.scc_of (tail G a) = H.scc_of (head G a)"
      by (metis H.scc_of_in_sccs_verts H.sccs_verts_disjoint a_in empty_iff G.head_in_verts verts_H)
    ultimately show False using scc_of_tail_neq_head by blast
  qed

  lemma H_scc_of_a_not_in:
    "H.scc_of (tail G a) \<notin> G.sccs_verts" "H.scc_of (head G a) \<notin> G.sccs_verts"
  proof safe
    assume "H.scc_of (tail G a) \<in> G.sccs_verts"
    with scc_of_tail_inter have "G.scc_of (tail G a) = H.scc_of (tail G a)"
      by (metis G.scc_of_in_sccs_verts G.sccs_verts_disjoint a_in empty_iff G.tail_in_verts)
    with G_scc_of_tail_not_in show False
      using ends_in by (auto simp: H.scc_of_in_sccs_verts verts_H)
  next
    assume "H.scc_of (head G a) \<in> G.sccs_verts"
    with scc_of_head_inter have "G.scc_of (tail G a) = H.scc_of (head G a)"
      by (metis G.scc_of_in_sccs_verts G.sccs_verts_disjoint a_in empty_iff G.tail_in_verts)
    with G_scc_of_tail_not_in show False
      using ends_in by (auto simp: H.scc_of_in_sccs_verts verts_H)
  qed

  lemma scc_verts_da:
    "H.sccs_verts = (G.sccs_verts - {G.scc_of (tail G a)}) \<union> {H.scc_of (tail G a), H.scc_of (head G a)}" (is "?L = ?R")
  proof (intro set_eqI iffI)
    fix S assume "S \<in> ?L"
    then obtain u where "u \<in> verts G" "S = H.scc_of u" by (auto simp: verts_H H.sccs_verts_conv_scc_of)
    moreover
    then have "G.scc_of (tail G a) \<noteq> H.scc_of u" using \<open>S \<in> ?L\<close> G_scc_of_tail_not_in by auto
    ultimately show "S \<in> ?R"
      unfolding G.sccs_verts_conv_scc_of
      by (cases "u \<in> G.scc_of (tail G a)") (auto dest: scc_of_G_tail scc_of_other)
  next
    fix S assume "S \<in> ?R"
    show "S \<in> ?L"
    proof (cases "S \<in> G.sccs_verts")
      case True
      with \<open>S \<in> ?R\<close> obtain u where u: "u \<in> verts G" "S = G.scc_of u" and "S \<noteq> G.scc_of (tail G a)"
        using H_scc_of_a_not_in by (auto simp: G.sccs_verts_conv_scc_of)
      then have "G.scc_of u \<inter> G.scc_of (tail G a) = {}"
        using ends_in by (intro G.sccs_verts_disjoint) (auto simp: G.scc_of_in_sccs_verts)
      then have "u \<notin> G.scc_of (tail G a)"
        using u by (auto dest: G.in_scc_of_self)
      with u show ?thesis using scc_of_other
        by (auto simp: H.sccs_verts_conv_scc_of verts_H G.sccs_verts_conv_scc_of)
    next
      case False with \<open>S \<in> ?R\<close> ends_in show ?thesis by (auto simp: H.sccs_verts_conv_scc_of verts_H)
    qed
  qed

  lemma card_sccs_da: "card H.sccs = Suc (card G.sccs)"
    using H_scc_of_a_not_in ends_in
    unfolding G.card_sccs_verts[symmetric] H.card_sccs_verts[symmetric] scc_verts_da
    by (simp add: card_insert_if G.finite_sccs_verts scc_of_tail_neq_head card_Suc_Diff1
      G.scc_of_in_sccs_verts del: card_Diff_insert)

end

sublocale bidel_arc_not_biconnected \<subseteq> bidel_arc_same_face
proof
  note a_in
  moreover from a_in have "head G a \<in> tail G ` G.face_cycle_set a" 
    by (simp add: G.heads_face_cycle_set[symmetric])
  moreover have "tail G a \<in> tail G ` G.face_cycle_set a" by simp
  ultimately obtain p where p: "G.trail (head G a) p (tail G a)" "set p \<subseteq> G.face_cycle_set a"
    by (rule G.obtain_trail_in_fcs')
  define p' where "p' = G.awalk_to_apath p"
  from p have p': "G.apath (head G a) p' (tail G a)" "set p' \<subseteq> G.face_cycle_set a"
    by (auto simp: G.trail_def p'_def dest: G.apath_awalk_to_apath G.awalk_to_apath_subset)
  then have "set p' \<subseteq> arcs G"
    using a_in by (blast dest: G.in_face_cycle_setD)

  have "\<not>set p' \<subseteq> arcs H"
  proof
    assume "set p' \<subseteq> arcs H"
    then have "H.awalk (head G a) p' (tail G a)"
      using p' by (auto simp: G.apath_def arcs_H intro: H_awalkI)
    then show False using not_reach_a by (metis H.symmetric_reachable' H.reachable_awalk)
  qed
  then have "set p' \<inter> {a,a'} \<noteq> {}" using \<open>set p' \<subseteq> arcs G\<close> by (auto simp: arcs_H)
  moreover
  have "a \<notin> set p'"
  proof
    assume "a \<in> set p'"
    then have "head G a \<in> set (tl (G.awalk_verts (head G a) p'))"
      using \<open>G.apath _ p' _\<close>
      by (cases p') (auto simp: G.set_awalk_verts G.apath_def G.awalk_Cons_iff, metis imageI)
    moreover
    have "head G a \<notin> set (tl (G.awalk_verts (head G a) p'))"
      using \<open>G.apath _ p' _\<close> by (cases p') (auto simp: G.apath_def)
    ultimately show False by contradiction
  qed
  ultimately
  have "a' \<in> G.face_cycle_set a" using p'(2) by auto
  then show "G.face_cycle_set a' = G.face_cycle_set a" using G.face_cycle_set_parts by auto
qed

locale bidel_arc_tail_conn = bidel_arc +
  assumes conn_tail: "tail G a \<notin> H.isolated_verts"

locale bidel_arc_head_conn = bidel_arc +
  assumes conn_head: "head G a \<notin> H.isolated_verts"

locale bidel_arc_tail_isolated = bidel_arc +
  assumes isolated_tail: "tail G a \<in> H.isolated_verts"
  
locale bidel_arc_head_isolated = bidel_arc +
  assumes isolated_head: "head G a \<in> H.isolated_verts"
begin

  lemma G_edge_succ_a'_no_loop:
    assumes no_loop_a: "head G a \<noteq> tail G a" shows G_edge_succ_a': "edge_succ M a' = a'" (is ?t2)
  proof -
    have *: "out_arcs G (tail G a') = {a'}"
      using a_in isolated_head no_loop_a
      by (auto simp: H.isolated_verts_def verts_H out_arcs_def arcs_H tail_H)
    obtain "edge_succ M a' \<in> {a'}" 
      using G.edge_succ_cyclic[of "tail G a'"]
      apply (rule eq_on_cyclic_on_iff1[where x="a'"])
      using * a_in a_neq_a' no_loop_a by simp_all
    then show ?thesis by auto
  qed

  lemma G_face_cycle_succ_a_no_loop:
    assumes no_loop_a: "head G a \<noteq> tail G a" shows "G.face_cycle_succ a = a'"
    using assms by (auto simp: G.face_cycle_succ_def G_edge_succ_a'_no_loop)

end





locale bidel_arc_same_face_tail_conn = bidel_arc_same_face + bidel_arc_tail_conn
begin

  definition a_neigh :: 'b where
    "a_neigh \<equiv> SOME b. G.face_cycle_succ b = a"

  lemma face_cycle_succ_a_neigh: "G.face_cycle_succ a_neigh = a"
  proof -
    have "\<exists>b. G.face_cycle_succ b = a" by (metis G.face_cycle_succ_pred)
    then show ?thesis unfolding a_neigh_def by (rule someI_ex)
  qed

  lemma a_neigh_in: "a_neigh \<in> arcs G"
    using a_in by (metis face_cycle_succ_a_neigh G.face_cycle_succ_closed)

  lemma a_neigh_neq_a: "a_neigh \<noteq> a"
  proof 
    assume "a_neigh = a"
    then have "G.face_cycle_set a = {a}" using face_cycle_succ_a_neigh by (simp add: G.fcs_x_eq_x)
    with a_neq_a' same_face G.face_cycle_set_self[of a'] show False by simp
  qed

  lemma a_neigh_neq_a': "a_neigh \<noteq> a'"
  proof
    assume A: "a_neigh = a'"

    have a_in_oa: "a \<in> out_arcs G (tail G a)" using a_in by auto
    have cyc: "cyclic_on (edge_succ M) (out_arcs G (tail G a))"
      using a_in by (intro G.edge_succ_cyclic) auto

    from A have "G.face_cycle_succ a' = a" by (metis face_cycle_succ_a_neigh)
    then have "edge_succ M a = a " by (auto simp: G.face_cycle_succ_def)
    then have "card (out_arcs G (tail G a)) = 1"
      using cyc a_in by (auto elim: eq_on_cyclic_on_iff1)
    then have "out_arcs G (tail G a) = {a}"
      using a_in_oa by (auto simp del: in_out_arcs_conv dest: card_eq_SucD)
    then show False using conn_tail a_in
      by (auto simp: H.isolated_verts_def arcs_H tail_H verts_H out_arcs_def)
  qed

  lemma edge_rev_a_neigh_neq: "edge_rev M a_neigh \<noteq> a'"
    by (metis a_neigh_neq_a G.arev_arev)

  lemma edge_succ_a_neq: "edge_succ M a \<noteq> a'"
  proof
    assume "edge_succ M a = a'"
    then have "G.face_cycle_set a' = {a'}"
      using face_cycle_succ_a_neigh by (auto simp: G.face_cycle_set_altdef id_funpow_id G.face_cycle_succ_def)
    with a_neq_a' same_face G.face_cycle_set_self[of a] show False by auto
  qed

  lemma H_face_cycle_succ_a_neigh: "H.face_cycle_succ a_neigh = G.face_cycle_succ a'"
    using face_cycle_succ_a_neigh edge_succ_a_neq edge_rev_a_neigh_neq a_neigh_neq_a a_neigh_neq_a' a_neigh_in
    unfolding H.face_cycle_succ_def G.face_cycle_succ_def
    by (auto simp: HM_def perm_restrict_simps perm_rem_conv G.bij_edge_succ)

  lemma H_fcs_a_neigh: "H.face_cycle_set a_neigh = segment G.face_cycle_succ a' a" (is "?L = ?R")
  proof -
    { fix n assume A: "0 < n" "n < funpow_dist1 G.face_cycle_succ a' a"
      then have *: "(G.face_cycle_succ ^^ n) a' \<in> segment G.face_cycle_succ a' a"
        using a_in_o by (auto simp: segment_altdef)
      then have "(G.face_cycle_succ ^^ n) a' \<notin> {a,a'}" "(G.face_cycle_succ ^^ n) a' \<in> arcs G"
        using not_in_segment1[OF a_in_o] not_in_segment2[of a G.face_cycle_succ a']
        by (auto simp: segment_altdef a_in_o)
    } note X = this

    { fix n assume "0 < n" "n < funpow_dist1 G.face_cycle_succ a' a"
      then have "(H.face_cycle_succ ^^ n) a_neigh = (G.face_cycle_succ ^^ n) a'"
      proof (induct n)
        case 0 then show ?case by simp
      next
        case (Suc n)
        show ?case
        proof (cases "n=0")
          case True then show ?thesis by (simp add: H_face_cycle_succ_a_neigh)
        next
          case False
          then have "(H.face_cycle_succ ^^ n) a_neigh = (G.face_cycle_succ ^^ n) a'"
            using Suc by simp
          then show ?thesis
            using X[of "Suc n"] X[of n] False Suc by (simp add: H_fcs_eq_G_fcs)
        qed
      qed
    } note Y = this

    have fcs_a'_neq_a: "G.face_cycle_succ a' \<noteq> a"
      by (metis (no_types) a_neigh_neq_a' G.face_cycle_pred_succ face_cycle_succ_a_neigh)

    show ?thesis
    proof (intro set_eqI iffI)
      fix b assume "b \<in> ?L"

      define m where "m = funpow_dist1 G.face_cycle_succ a' a - 1"

      have b_in0: "b \<in> orbit H.face_cycle_succ (a_neigh)"
        using \<open>b \<in> ?L\<close> by (simp add: H.face_cycle_set_def[symmetric])

      have "0 < m"
        by (auto simp: m_def) (metis a_neigh_neq_a' G.face_cycle_pred_succ G.face_cycle_set_def
          G.face_cycle_set_self G.face_cycle_set_succ face_cycle_succ_a_neigh funpow_dist_0_eq neq0_conv
          same_face)
      then have pos_dist: "0 < funpow_dist1 H.face_cycle_succ a_neigh b"
        by (simp add: m_def)

      have *: "(G.face_cycle_succ ^^ Suc m) a' = a"
        using a_in_o by (simp add: m_def funpow_simp_l funpow_dist1_prop del: funpow.simps)
      have "(H.face_cycle_succ ^^ m) a_neigh = a_neigh"
      proof -
        have "a = G.face_cycle_succ ((H.face_cycle_succ ^^ m) a_neigh)"
          using * \<open>0 < m\<close> by (simp add: Y m_def)
        then show ?thesis using face_cycle_succ_a_neigh by (metis G.face_cycle_pred_succ)
      qed
      then have "funpow_dist1 H.face_cycle_succ a_neigh b \<le> m"
        using \<open>0 < m\<close> b_in0 by (intro funpow_dist1_le_self) simp_all
      also have "\<dots> < funpow_dist1 G.face_cycle_succ a' a" unfolding m_def by simp
      finally have dist_less: "funpow_dist1 H.face_cycle_succ a_neigh b
          < funpow_dist1 G.face_cycle_succ a' a" .
      have "b = (H.face_cycle_succ ^^ funpow_dist1 H.face_cycle_succ a_neigh b) a_neigh"
        using b_in0 by (simp add: funpow_dist1_prop del: funpow.simps)
      also have "\<dots> = (G.face_cycle_succ ^^ funpow_dist1 H.face_cycle_succ a_neigh b) a'"
        using pos_dist dist_less by (rule Y)
      also have "\<dots> \<in> ?R" using pos_dist dist_less by (simp add: segment_altdef a_in_o del: funpow.simps)
      finally show "b \<in> ?R" .
    next
      fix b assume "b \<in> ?R"
      then show "b \<in> ?L"
        using Y
        by (auto simp: segment_altdef a_in_o H.face_cycle_set_altdef Suc_le_eq) metis
    qed
  qed

end





locale bidel_arc_isolated_loop =
  bidel_arc_biconnected + bidel_arc_tail_isolated
begin

  lemma loop_a[simp]: "head G a = tail G a"
    using isolated_tail reach_a by (auto simp: H.isolated_verts_def
      elim: H.converse_reachable_cases dest: out_arcs_emptyD_dominates)

end

sublocale bidel_arc_isolated_loop \<subseteq> bidel_arc_head_isolated
  using isolated_tail loop_a by unfold_locales simp

context bidel_arc_isolated_loop begin
text \<open>The edges @{term a} and @{term a'} form a loop on an otherwise isolated vertex \<close>

  lemma card_isolated_verts_da: "card H.isolated_verts = Suc (card G.isolated_verts)"
    by (simp add: card_isolated_verts_da0 isolated_tail)

  lemma
    G_edge_succ_a[simp]: "edge_succ M a = a'" (is ?t1) and
    G_edge_succ_a'[simp]: "edge_succ M a' = a" (is ?t2)
  proof -
    have *: "out_arcs G (tail G a) = {a,a'}"
      using a_in isolated_tail 
      by (auto simp: H.isolated_verts_def verts_H out_arcs_def arcs_H tail_H)
    obtain "edge_succ M a' \<in> {a,a'}" "edge_succ M a' \<noteq> a'" 
      using G.edge_succ_cyclic[of "tail G a'"]
      apply (rule eq_on_cyclic_on_iff1[where x="a'"])
      using * a_in a_neq_a' loop_a by auto
    moreover
    obtain "edge_succ M a \<in> {a,a'}" "edge_succ M a \<noteq> a" 
      using G.edge_succ_cyclic[of "tail G a"]
      apply (rule eq_on_cyclic_on_iff1[where x="a"])
      using * a_in a_neq_a' loop_a by auto
    ultimately show ?t1 ?t2 by auto
  qed

  lemma
    G_face_cycle_succ_a[simp]: "G.face_cycle_succ a = a" and
    G_face_cycle_succ_a'[simp]: "G.face_cycle_succ a' = a'"
    by (auto simp: G.face_cycle_succ_def)

  lemma
    G_face_cycle_set_a[simp]: "G.face_cycle_set a = {a}" and
    G_face_cycle_set_a'[simp]: "G.face_cycle_set a' = {a'}"
    unfolding G.fcs_x_eq_x[symmetric] by simp_all

end

sublocale bidel_arc_isolated_loop \<subseteq> bidel_arc_diff_face
  using a_neq_a' by unfold_locales auto

context bidel_arc_isolated_loop begin

  lemma card_face_cycle_sets_da: "card G.face_cycle_sets = Suc (Suc (card H.face_cycle_sets))"
    unfolding card_face_cycle_sets_da' using diff_face card_fcs_aa'_le
    by (auto simp: card_insert_if S_def G.segment_face_cycle_x_x_eq)

  lemma euler_genus_da: "H.euler_genus = G.euler_genus"
    unfolding G.euler_genus_def H.euler_genus_def G.euler_char_def H.euler_char_def
    by (simp add: card_isolated_verts_da verts_H card_arcs_da card_face_cycle_sets_da card_sccs_da)

end

locale bidel_arc_two_isolated =
  bidel_arc_not_biconnected + bidel_arc_tail_isolated + bidel_arc_head_isolated
begin
text \<open>@{term "tail G a"} and @{term "head G a"} form an SCC with @{term a} and @{term a'} as the only arcs.\<close>

  lemma no_loop_a: "head G a \<noteq> tail G a"
    using not_reach_a a_in by (auto simp: verts_H)

  lemma card_isolated_verts_da: "card H.isolated_verts = Suc (Suc (card G.isolated_verts))"
    using no_loop_a isolated_tail isolated_head by (simp add: card_isolated_verts_da0 card_insert_if)

  lemma G_edge_succ_a'[simp]: "edge_succ M a' = a'"
    using G_edge_succ_a'_no_loop no_loop_a by simp

  lemma G_edge_succ_a[simp]: "edge_succ M a = a"
  proof -
    have *: "out_arcs G (tail G a) = {a}"
      using a_in isolated_tail isolated_head no_loop_a
      by (auto simp: H.isolated_verts_def verts_H out_arcs_def arcs_H tail_H)
    obtain "edge_succ M a \<in> {a}" 
      using G.edge_succ_cyclic[of "tail G a"]
      apply (rule eq_on_cyclic_on_iff1[where x="a"])
      using * a_in a_neq_a' no_loop_a by simp_all
    then show ?thesis  by auto
  qed

  lemma
    G_face_cycle_succ_a[simp]: "G.face_cycle_succ a = a'" and
    G_face_cycle_succ_a'[simp]: "G.face_cycle_succ a' = a"
    by (auto simp: G.face_cycle_succ_def)

  lemma
    G_face_cycle_set_a[simp]: "G.face_cycle_set a = {a,a'}" (is ?t1) and
    G_face_cycle_set_a'[simp]: "G.face_cycle_set a' = {a,a'}" (is ?t2)
  proof -
    { fix n have "(G.face_cycle_succ ^^ n) a \<in> {a,a'}" "(G.face_cycle_succ ^^ n) a' \<in> {a,a'}"
        by (induct n) auto
    }
    then
    show ?t1 ?t2 by (auto simp: G.face_cycle_set_altdef intro: exI[where x=0] exI[where x=1])
  qed

  lemma card_face_cycle_sets_da: "card G.face_cycle_sets = Suc (card H.face_cycle_sets)"
    unfolding card_face_cycle_sets_da0 using card_fcs_aa'_le by simp

  lemma euler_genus_da: "H.euler_genus = G.euler_genus"
    unfolding G.euler_genus_def H.euler_genus_def G.euler_char_def H.euler_char_def
    by (simp add: card_isolated_verts_da verts_H card_arcs_da card_face_cycle_sets_da card_sccs_da)

end

locale bidel_arc_tail_not_isol = bidel_arc_not_biconnected +
  bidel_arc_tail_conn

sublocale bidel_arc_tail_not_isol \<subseteq> bidel_arc_same_face_tail_conn
  by unfold_locales

locale bidel_arc_only_tail_not_isol = bidel_arc_tail_not_isol +
  bidel_arc_head_isolated

context bidel_arc_only_tail_not_isol
begin

  lemma card_isolated_verts_da: "card H.isolated_verts = Suc (card G.isolated_verts)"
    using isolated_head conn_tail by (simp add: card_isolated_verts_da0)

  lemma segment_a'_a_ne: "segment G.face_cycle_succ a' a \<noteq> {}"
    unfolding H_fcs_a_neigh[symmetric] by auto

  lemma segment_a_a'_e: "segment G.face_cycle_succ a a' = {}"
  proof -
    have "a' = G.face_cycle_succ a" using tail_neq_head
      by (simp add: G_face_cycle_succ_a_no_loop)
    then show ?thesis by (auto simp: segment1_empty)
  qed

  lemma card_face_cycle_sets_da: "card H.face_cycle_sets = card G.face_cycle_sets"
    unfolding card_face_cycle_sets_da' using segment_a'_a_ne segment_a_a'_e card_fcs_gt_0
    by (simp add: card_insert_if)

  lemma euler_genus_da: "H.euler_genus = G.euler_genus"
    unfolding G.euler_genus_def H.euler_genus_def G.euler_char_def H.euler_char_def
    by (simp add: card_isolated_verts_da verts_H card_arcs_da card_face_cycle_sets_da card_sccs_da)

end

locale bidel_arc_only_head_not_isol = bidel_arc_not_biconnected +
  bidel_arc_head_conn +
  bidel_arc_tail_isolated
begin

  interpretation rev: bidel_arc G M a'
    using a_in by unfold_locales simp

  interpretation rev: bidel_arc_only_tail_not_isol G M a'
    using a_in not_reach_a
    by unfold_locales (auto simp: rev_H isolated_tail conn_head dest: H.symmetric_reachable')

  lemma euler_genus_da: "H.euler_genus = G.euler_genus"
    using rev.euler_genus_da by (simp add: rev_H rev_HM)

end

locale bidel_arc_two_not_isol = bidel_arc_tail_not_isol +
  bidel_arc_head_conn
begin

  lemma isolated_verts_da: "H.isolated_verts = G.isolated_verts"
    using conn_head conn_tail by (subst isolated_da_pre) simp

  lemma segment_a'_a_ne': "segment G.face_cycle_succ a' a \<noteq> {}"
    unfolding H_fcs_a_neigh[symmetric] by auto

  interpretation rev: bidel_arc_tail_not_isol G M a'
    using arcs_in not_reach_a rev_H conn_head
    by unfold_locales (auto dest: H.symmetric_reachable')

  lemma segment_a_a'_ne': "segment G.face_cycle_succ a a' \<noteq> {}"
    using rev.H_fcs_a_neigh[symmetric] rev_H rev_HM by auto

  lemma card_face_cycle_sets_da: "card H.face_cycle_sets = Suc (card G.face_cycle_sets)"
    unfolding card_face_cycle_sets_da' using segment_a'_a_ne' segment_a_a'_ne' card_fcs_gt_0
    by (simp add: segments_neq card_insert_if)

  lemma euler_genus_da: "H.euler_genus = G.euler_genus"
    unfolding G.euler_genus_def H.euler_genus_def G.euler_char_def H.euler_char_def
    by (simp add: isolated_verts_da verts_H card_arcs_da card_face_cycle_sets_da card_sccs_da)

end

locale bidel_arc_biconnected_non_triv = bidel_arc_biconnected +
  bidel_arc_tail_conn

sublocale bidel_arc_biconnected_non_triv \<subseteq> bidel_arc_head_conn
  by unfold_locales (metis (mono_tags) G.in_sccs_verts_conv_reachable G.symmetric_reachable'
    H.isolated_verts_in_sccs conn_tail empty_iff insert_iff reach_a reachable_daD sccs_verts_da)

context bidel_arc_biconnected_non_triv begin

  lemma isolated_verts_da: "H.isolated_verts = G.isolated_verts"
    using conn_head conn_tail by (subst isolated_da_pre) simp

end

locale bidel_arc_biconnected_same = bidel_arc_biconnected_non_triv +
  bidel_arc_same_face

sublocale bidel_arc_biconnected_same \<subseteq> bidel_arc_same_face_tail_conn
  by unfold_locales


context bidel_arc_biconnected_same begin

  interpretation rev: bidel_arc_same_face_tail_conn G M a'
    using arcs_in conn_head by unfold_locales (auto simp: same_face rev_H)

  lemma card_face_cycle_sets_da: "Suc (card H.face_cycle_sets) \<ge> (card G.face_cycle_sets)"
    unfolding card_face_cycle_sets_da' using card_fcs_gt_0 by linarith

  lemma euler_genus_da: "H.euler_genus \<le> G.euler_genus"
    using card_face_cycle_sets_da
    unfolding G.euler_genus_def H.euler_genus_def G.euler_char_def H.euler_char_def
    by (simp add: isolated_verts_da verts_H card_arcs_da card_sccs_da )

end



locale bidel_arc_biconnected_diff = bidel_arc_biconnected_non_triv +
  bidel_arc_diff_face
begin

  lemma fcs_not_triv: "G.face_cycle_set a \<noteq> {a} \<or> G.face_cycle_set a' \<noteq> {a'}"
  proof (rule ccontr)
    assume "\<not>?thesis"
    then have "G.face_cycle_succ a = a" "G.face_cycle_succ a' = a'"
      by (auto simp: G.fcs_x_eq_x)
    then have *: "edge_succ M a = a'" "edge_succ M a' = a"
      by (auto simp: G.face_cycle_succ_def)
    then have "(edge_succ M ^^ 2) a = a" by (auto simp: eval_nat_numeral)
    { fix n
      have "(edge_succ M ^^ 2) a = a" by (auto simp: * eval_nat_numeral)
      then have "(edge_succ M ^^ n) a = (edge_succ M ^^ (n mod 2)) a"
        by (auto simp: funpow_mod_eq)
      moreover have "n mod 2 = 0 \<or> n mod 2 = 1" by auto
      ultimately have "(edge_succ M ^^ n) a \<in> {a, a'}" by (auto simp: *)
    }
    then have "orbit (edge_succ M) a = {a, a'}"
      by (auto simp: orbit_altdef_permutation[OF G.permutation_edge_succ] exI[where x=0] exI[where x=1] *)

    have "out_arcs G (tail G a) \<subseteq> {a,a'}"
    proof -
      have "cyclic_on (edge_succ M) (out_arcs G (tail G a))"
        using arcs_in by (intro G.edge_succ_cyclic) auto
      then have "orbit (edge_succ M) a = out_arcs G (tail G a)"
        using arcs_in by (intro orbit_cyclic_eq3) auto
      then show ?thesis using \<open>orbit _ _ = {_, _}\<close> by auto
    qed
    then have "out_arcs H (tail G a) = {}" by (auto simp: arcs_H tail_H)
    then have "tail G a \<in> H.isolated_verts" using arcs_in by (simp add: H.isolated_verts_def verts_H)
    then show False using conn_tail by contradiction
  qed

  lemma S_ne: "S \<noteq> {}"
    using fcs_not_triv by (auto simp: S_def G.segment_face_cycle_x_x_eq)

  lemma card_face_cycle_sets_da: "card G.face_cycle_sets = Suc (card H.face_cycle_sets)"
    unfolding card_face_cycle_sets_da' using S_ne diff_face card_fcs_aa'_le by simp

  lemma euler_genus_da: "H.euler_genus = G.euler_genus"
    unfolding G.euler_genus_def H.euler_genus_def G.euler_char_def H.euler_char_def
    by (simp add: isolated_verts_da verts_H card_arcs_da card_sccs_da card_face_cycle_sets_da)

end



context bidel_arc begin

  lemma euler_genus_da: "H.euler_genus \<le> G.euler_genus"
  proof -
    let ?biconnected = "tail G a \<rightarrow>\<^sup>*\<^bsub>H\<^esub> head G a"
    let ?isol_tail = "tail G a \<in> H.isolated_verts"
    let ?isol_head = "head G a \<in> H.isolated_verts"
    let ?same_face = "G.face_cycle_set a' = G.face_cycle_set a"
    { assume ?biconnected ?isol_tail
      then interpret EG: bidel_arc_isolated_loop by unfold_locales
      have ?thesis by (simp add: EG.euler_genus_da)
    }
    moreover
    { assume ?biconnected "\<not>?isol_tail" ?same_face
      then interpret EG: bidel_arc_biconnected_same by unfold_locales
      have ?thesis by (simp add: EG.euler_genus_da)
    }
    moreover
    { assume ?biconnected "\<not>?isol_tail" "\<not>?same_face"
      then interpret EG: bidel_arc_biconnected_diff by unfold_locales
      have ?thesis by (simp add: EG.euler_genus_da)
    }
    moreover
    { assume "\<not>?biconnected" ?isol_tail ?isol_head
      then interpret EG: bidel_arc_two_isolated by unfold_locales
      have ?thesis by (simp add: EG.euler_genus_da)
    }
    moreover
    { assume "\<not>?biconnected" "\<not>?isol_tail" ?isol_head
      then interpret EG: bidel_arc_only_tail_not_isol by unfold_locales
      have ?thesis by (simp add: EG.euler_genus_da)
    }
    moreover
    { assume "\<not>?biconnected" ?isol_tail "\<not>?isol_head"
      then interpret EG: bidel_arc_only_head_not_isol by unfold_locales
      have ?thesis by (simp add: EG.euler_genus_da)
    }
    moreover
    { assume "\<not>?biconnected" "\<not>?isol_tail" "\<not>?isol_head"
      then interpret EG: bidel_arc_two_not_isol by unfold_locales
      have ?thesis by (simp add: EG.euler_genus_da)
    }
    ultimately show ?thesis by satx
  qed
end



subsection \<open>Modifying @{term edge_rev}\<close>

definition (in pre_digraph_map) rev_swap :: "'b \<Rightarrow> 'b \<Rightarrow> 'b pre_map" where
  "rev_swap a b = \<lparr> edge_rev = perm_swap a b (edge_rev M), edge_succ = perm_swap a b (edge_succ M) \<rparr>"

context digraph_map begin

  lemma digraph_map_rev_swap:
    assumes "arc_to_ends G a = arc_to_ends G b" "{a,b} \<subseteq> arcs G"
    shows "digraph_map G (rev_swap a b)"
  proof
    let ?M' = "rev_swap a b"

    have tail_swap: "\<And>x. tail G ((a \<rightleftharpoons>\<^sub>F b) x) = tail G x"
      using assms by (case_tac "x \<in> {a,b}") (auto simp: arc_to_ends_def)
    have swap_in_arcs: "\<And>x. (a \<rightleftharpoons>\<^sub>F b) x \<in> arcs G \<longleftrightarrow> x \<in> arcs G"
      using assms by (case_tac "x \<in> {a,b}") auto

    have es_perm: "edge_succ ?M' permutes arcs G"
      using assms edge_succ_permutes unfolding permutes_conv_has_dom
      by (auto simp: rev_swap_def has_dom_perm_swap)

    {
      fix x show "(x \<in> arcs G) = (edge_rev (rev_swap a b) x \<noteq> x)"
        using assms(2)
        by (cases "x \<in> {a,b}") (auto simp: rev_swap_def perm_swap_def arev_dom swap_def split: if_splits)
    next
      fix x assume "x \<in> arcs G" then show "edge_rev ?M' (edge_rev ?M' x) = x"
        by (auto simp: rev_swap_def perm_swap_comp[symmetric])
    next
      fix x assume "x \<in> arcs G" then show "tail G (edge_rev ?M' x) = head G x"
        using assms by (case_tac "x \<in> {a,b}") (auto simp: rev_swap_def perm_swap_def tail_swap arc_to_ends_def)
    next
      show "edge_succ ?M' permutes arcs G" by fact
    next
      fix v assume A: "v \<in> verts G" "out_arcs G v \<noteq> {}"
      then obtain c where "c \<in> out_arcs G v" by blast
      have "inj (perm_swap a b (edge_succ M))" by (simp add: bij_is_inj bij_edge_succ)
  
      have "out_arcs G v = (a \<rightleftharpoons>\<^sub>F b) ` out_arcs G v"
        by (auto simp: tail_swap swap_swap_id swap_in_arcs intro: image_eqI[where x="(a \<rightleftharpoons>\<^sub>F b) y" for y])
      also have "(a \<rightleftharpoons>\<^sub>F b) `  out_arcs G v = (a \<rightleftharpoons>\<^sub>F b) `  orbit (edge_succ M) ((a \<rightleftharpoons>\<^sub>F b) c)"
        using edge_succ_cyclic using A \<open>c \<in> _\<close> 
        by (intro arg_cong[where f="(`) (a \<rightleftharpoons>\<^sub>F b)"])
           (intro orbit_cyclic_eq3[symmetric], auto simp: swap_in_arcs tail_swap)
      also have "\<dots> = orbit (edge_succ ?M') c"
        by (simp add: orbit_perm_swap rev_swap_def)
      finally have oa_orb: "out_arcs G v = orbit (edge_succ ?M') c" .
      
      show "cyclic_on (edge_succ ?M') (out_arcs G v)"
        unfolding oa_orb using es_perm finite_arcs by (rule cyclic_on_orbit)
    }
  qed

  lemma euler_genus_rev_swap:
    assumes "arc_to_ends G a = arc_to_ends G b" "{a,b} \<subseteq> arcs G"
    shows "pre_digraph_map.euler_genus G (rev_swap a b) = euler_genus"
  proof -
    let ?M' = "rev_swap a b"
  
    interpret G': digraph_map G ?M' using assms by (rule digraph_map_rev_swap)
  
    have swap_in_arcs: "\<And>x. (a \<rightleftharpoons>\<^sub>F b) x \<in> arcs G \<longleftrightarrow> x \<in> arcs G"
      using assms by (case_tac "x \<in> {a,b}") auto
  
    have G'_fcs: "G'.face_cycle_succ = perm_swap a b face_cycle_succ"
      unfolding G'.face_cycle_succ_def face_cycle_succ_def
      by (auto simp: fun_eq_iff rev_swap_def perm_swap_comp)
  
    have "\<And>x. G'.face_cycle_set x = (a \<rightleftharpoons>\<^sub>F b) ` face_cycle_set ((a \<rightleftharpoons>\<^sub>F b) x)"
      by (auto simp: face_cycle_set_def G'.face_cycle_set_def orbit_perm_swap G'_fcs imageI)
    then have "G'.face_cycle_sets = (\<lambda>S. (a \<rightleftharpoons>\<^sub>F b) ` S) ` face_cycle_sets"
      by (auto simp: pre_digraph_map.face_cycle_sets_def swap_in_arcs)
         (metis swap_swap_id image_eqI swap_in_arcs)
    then have "card G'.face_cycle_sets = card ((\<lambda>S. (a \<rightleftharpoons>\<^sub>F b) ` S) ` face_cycle_sets)" by simp
    also have "\<dots> = card face_cycle_sets"
      by (rule card_image) (rule inj_on_f_imageI[where S="UNIV"], auto)
    finally
    show "pre_digraph_map.euler_genus G ?M' = euler_genus"
      unfolding pre_digraph_map.euler_genus_def pre_digraph_map.euler_char_def by simp
  qed

end



subsection \<open>Conclusion\<close>

lemma bidirected_subgraph_obtain:
  assumes sg: "subgraph H G" "arcs H \<noteq> arcs G"
  assumes fin: "finite (arcs G)"
  assumes bidir: "\<exists>rev. bidirected_digraph G rev" "\<exists>rev. bidirected_digraph H rev"
  obtains a a' where "{a,a'} \<subseteq> arcs G - arcs H" "a' \<noteq> a"
    "tail G a' = head G a" "head G a'= tail G a"
proof -
  obtain a where a: "a \<in> arcs G - arcs H" using sg by blast

  obtain rev_G rev_H where rev: "bidirected_digraph G rev_G" "bidirected_digraph H rev_H"
    using bidir by blast
  interpret G: bidirected_digraph G rev_G by (rule rev)
  interpret H: bidirected_digraph H rev_H by (rule rev)

  have sg_props: "arcs H \<subseteq> arcs G" "tail H = tail G" "head H = head G"
    using sg by (auto simp: subgraph_def compatible_def)

  { fix w1 w2 assume A: "tail G a = w1" "head G a = w2"
    have "in_arcs H w1 \<inter> out_arcs H w2 = rev_H ` (out_arcs H w1 \<inter> in_arcs H w2)" (is "?Sh = _")
      unfolding H.in_arcs_eq by (simp add: image_Int image_image H.inj_on_arev)
    then have "card (in_arcs H w1 \<inter> out_arcs H w2) = card (out_arcs H w1 \<inter> in_arcs H w2)"
      by (metis card_image H.arev_arev inj_on_inverseI)
    also have "\<dots> < card (out_arcs G w1 \<inter> in_arcs G w2)" (is "card ?Sh1 < card ?Sg1")
    proof (rule psubset_card_mono)
      show "finite ?Sg1" using fin by (auto simp: out_arcs_def)
      show "?Sh1 \<subset> ?Sg1" using A a sg_props by auto
    qed
    also have "?Sg1 = rev_G ` (in_arcs G w1 \<inter> out_arcs G w2)" (is "_ = _ ` ?Sg")
      unfolding G.in_arcs_eq by (simp add: image_Int image_image G.inj_on_arev)
    also have "card \<dots> = card ?Sg"
      by (metis card_image G.arev_arev inj_on_inverseI)
    finally have card_less: "card ?Sh < card ?Sg" .

    have S_ss: "?Sh \<subseteq> ?Sg" using sg_props by auto

    have ?thesis
    proof (cases "w1 = w2")
      case True
      have "card (?Sh - {a}) = card ?Sh"
        using a by (intro arg_cong[where f=card]) auto
      also have "\<dots> < card ?Sg - 1"
      proof -
        from True have "even (card ?Sg)" "even (card ?Sh)"
          by (auto simp: G.even_card_loops H.even_card_loops)
        then show ?thesis using card_less
          by simp (metis Suc_pred even_Suc le_neq_implies_less lessE less_Suc_eq_le zero_less_Suc)
      qed
      also have "\<dots> = card (?Sg - {a})"
        using fin a A True by (auto simp: out_arcs_def card_Diff_singleton)
      finally have card_diff_a_less: "card (?Sh - {a}) < card (?Sg - {a})" .
      moreover
      from S_ss have "?Sh - {a} \<subseteq> ?Sg - {a}" using S_ss by blast
      ultimately have "?Sh - {a} \<subset> ?Sg - {a}" 
        by (intro card_psubset) auto
      then obtain a' where "a' \<in> (?Sg - {a})- ?Sh" by blast
      then have "{a,a'} \<subseteq> arcs G - arcs H" "a' \<noteq> a" "tail G a' = head G a" "head G a'= tail G a"
        using A a sg_props by auto
      then show ?thesis ..
    next
      case False
      from card_less S_ss have "?Sh \<subset> ?Sg" by auto
      then obtain a' where "a' \<in> ?Sg - ?Sh" by blast
      then have "{a,a'} \<subseteq> arcs G - arcs H" "a' \<noteq> a" "tail G a' = head G a" "head G a'= tail G a"
        using A a sg_props False by auto
      then show ?thesis ..
    qed
  }
  then show ?thesis by simp
qed

lemma subgraph_euler_genus_le:
  assumes G: "subgraph H G" "digraph_map G GM" and H: "\<exists>rev. bidirected_digraph H rev"
  obtains HM where "digraph_map H HM" "pre_digraph_map.euler_genus H HM \<le> pre_digraph_map.euler_genus G GM"
proof -
  let ?d = "\<lambda>G. card (arcs G) + card (verts G) - card (arcs H) - card (verts H)"
  from H obtain rev_H where "bidirected_digraph H rev_H" by blast
  then interpret H: bidirected_digraph H rev_H .

  from G
  have "\<exists>HM. digraph_map H HM \<and> pre_digraph_map.euler_genus H HM \<le> pre_digraph_map.euler_genus G GM"
  proof (induct "?d G" arbitrary: G GM rule: less_induct)
    case less

    from less interpret G: digraph_map G GM by -

    have H_ss: "arcs H \<subseteq> arcs G" "verts H \<subseteq> verts G" using \<open>subgraph H G\<close> by auto
    then have card_le: "card (arcs H) \<le> card (arcs G)" "card (verts H) \<le> card (verts G)"
      by (auto intro: card_mono)

    have ends: "tail H = tail G" "head H = head G"
      using \<open>subgraph H G\<close> by (auto simp: compatible_def)

    show ?case
    proof (cases "?d G = 0")
      case True
      then have "card (arcs H) = card (arcs G)" "card (verts H) = card (verts G)"
        using card_le by linarith+
      then have "arcs H = arcs G" "verts H = verts G"
        using H_ss by (auto simp: card_subset_eq)
      then have "H = G" using \<open>subgraph H G\<close> by (auto simp: compatible_def)
      then have "digraph_map H GM \<and> pre_digraph_map.euler_genus H GM \<le> G.euler_genus" by auto
      then show ?thesis ..
    next
      case False
      then have H_ne: "(arcs G - arcs H) \<noteq> {} \<or> (verts G - verts H) \<noteq> {}"
        using H_ss card_le by auto

      { assume A: "arcs G - arcs H \<noteq> {}"
        then obtain a a' where aa': "{a, a'} \<subseteq> arcs G - arcs H" "a' \<noteq> a" "tail G a' = head G a" "head G a' = tail G a"
          using H_ss \<open>subgraph H G\<close> by (auto intro: bidirected_subgraph_obtain)
        let ?GM' = "G.rev_swap (edge_rev GM a) a'"

        interpret G': digraph_map G ?GM'
          using aa' by (intro G.digraph_map_rev_swap) (auto simp: arc_to_ends_def)
        interpret G': bidel_arc G ?GM' a
          using aa' by unfold_locales simp

        have "edge_rev GM a \<noteq> a"
          using aa' by (intro G.arev_neq) auto
        then have er_a: "edge_rev ?GM' a = a'"
          using \<open>a' \<noteq> a\<close> by (auto simp: G.rev_swap_def perm_swap_def swap_id_eq dest: G.arev_neq)
        then have sg: "subgraph H G'.H"
          using H_ss aa' by (intro subgraphI) (auto simp: G'.verts_H G'.arcs_H G'.tail_H G'.head_H ends compatible_def intro: H.wf_digraph G'.H.wf_digraph)

        have "card {a,a'} \<le> card (arcs G)"
          using aa' by (intro card_mono) auto
        then obtain HM where HM: "digraph_map H HM" "pre_digraph_map.euler_genus H HM \<le> G'.H.euler_genus"
          using aa' False by atomize_elim (rule less, auto simp: G'.verts_H G'.arcs_H  card_insert_if sg er_a)

        have "G'.H.euler_genus \<le> G'.euler_genus" by (rule G'.euler_genus_da)
        also have "G'.euler_genus = G.euler_genus"
          using aa' by (auto simp: G.euler_genus_rev_swap arc_to_ends_def)
        finally have ?thesis using HM by auto
      }
      moreover
      { assume A: "arcs G - arcs H = {}"
        then have A': "verts G - verts H \<noteq> {}" and arcs_H: "arcs H = arcs G" using H_ss H_ne by auto
        then obtain v where v: "v \<in> verts G - verts H" by auto
        have card_lt: "card (verts H) < card (verts G)"
          using A' H_ss by (intro psubset_card_mono) auto

        have "out_arcs G v = out_arcs H v" using A H_ss by (auto simp: ends)
        then interpret G: del_vert_props G GM v
          using v by unfold_locales auto

        have "?d (G.del_vert v) < ?d G"
          using card_lt by (simp add: arcs_H G.arcs_dv G.card_verts_dv)
        moreover
        have "subgraph H (G.del_vert v)"
          using H_ss v by (auto simp: subgraph_def arcs_H G.arcs_dv G.verts_del_vert H.wf_digraph
            G.H.wf_digraph compatible_def G.tail_del_vert G.head_del_vert ends)
        moreover
        have "bidirected_digraph (G.del_vert v) (edge_rev GM)"
          using G.arev_dom by (intro G.H.bidirected_digraphI) (auto simp: G.arcs_dv)
        ultimately
        have ?thesis unfolding G.euler_genus_eq[symmetric] by (intro less) auto
      }
      ultimately show ?thesis by blast
    qed
  qed
  then obtain HM where "digraph_map H HM" "pre_digraph_map.euler_genus H HM \<le> pre_digraph_map.euler_genus G GM"
    by atomize_elim
  then show ?thesis ..
qed

lemma (in digraph_map) nonneg_euler_genus: "0 \<le> euler_genus"
proof -
  define H where "H = \<lparr> verts = {}, arcs = {}, tail = tail G, head = head G \<rparr>"
  then have H_simps: "verts H = {}" "arcs H = {}" "tail H = tail G" "head H = head G"
    by (simp_all add: H_def)

  interpret H: bidirected_digraph H id
    by unfold_locales (auto simp: H_def)
  have "wf_digraph H" "wf_digraph G" by unfold_locales
  then have "subgraph H G" by (intro subgraphI) (auto simp: H_def compatible_def)
  then obtain HM where "digraph_map H HM" "pre_digraph_map.euler_genus H HM \<le> euler_genus"
    by (rule subgraph_euler_genus_le) auto
  then interpret H: digraph_map H HM by -

  have "H.sccs = {}"
  proof -
    { fix x assume *: "x \<in> H.sccs_verts"
      then have "x = {}" by (auto dest: H.sccs_verts_subsets simp: H_simps)
      with * have False by (auto simp: H.in_sccs_verts_conv_reachable)
    } then show ?thesis by (auto simp: H.sccs_verts_conv)
  qed
  then have "H.euler_genus = 0"
    by (auto simp: H.euler_genus_def H.euler_char_def H.isolated_verts_def H.face_cycle_sets_def H_simps)
  then show ?thesis using \<open>H.euler_genus \<le> _\<close> by simp
qed

lemma subgraph_comb_planar:
  assumes "subgraph G H" "comb_planar H" "\<exists>rev. bidirected_digraph G rev" shows "comb_planar G"
proof -
  from \<open>comb_planar H\<close> obtain HM where "digraph_map H HM" and H_genus: "pre_digraph_map.euler_genus H HM = 0"
    unfolding comb_planar_def by metis

  obtain GM where G: "digraph_map G GM" "pre_digraph_map.euler_genus G GM \<le> pre_digraph_map.euler_genus H HM"
    using assms(1) \<open>digraph_map H HM\<close> assms(3) by (rule subgraph_euler_genus_le)
  interpret G: digraph_map G GM by fact

  show ?thesis using G H_genus G.nonneg_euler_genus unfolding comb_planar_def by auto
qed

end
