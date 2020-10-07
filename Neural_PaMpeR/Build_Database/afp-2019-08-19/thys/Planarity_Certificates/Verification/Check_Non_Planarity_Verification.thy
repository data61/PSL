section "Verification of a Non-Planarity Checker"

theory Check_Non_Planarity_Verification imports
  Check_Non_Planarity_Impl
  "../Planarity/Kuratowski_Combinatorial"
  "HOL-Library.Rewrite"
  "HOL-Eisbach.Eisbach"
begin

subsection \<open>Graph Basics and Implementation\<close>

context pre_digraph begin

lemma cas_nonempty_ends:
  assumes "p \<noteq> []" "cas u p v" "cas u' p v'"
  shows "u = u'" "v = v'"
  using assms apply (metis cas_simp)
  using assms by (metis append_Nil2 cas.simps(1) cas_append_iff cas_simp)

lemma awalk_nonempty_ends:
  assumes "p \<noteq> []" "awalk u p v" "awalk u' p v'"
  shows "u = u'" "v = v'"
  using assms by (auto simp: awalk_def intro: cas_nonempty_ends)

end

lemma (in pair_graph) verts2_awalk_distinct:
  assumes V: "verts3 G \<subseteq> V" "V \<subseteq> pverts G" "u \<in> V"
  assumes p: "awalk u p v" "set (inner_verts p) \<inter> V = {}" "progressing p"
  shows "distinct (inner_verts p)"
  using p
proof (induct p arbitrary: v rule: rev_induct)
  case Nil then show ?case by auto
next
  case (snoc e es)
  have "distinct (inner_verts es)"
    apply (rule snoc.hyps)
      using snoc.prems apply (auto dest: progressing_appendD1)
    apply (metis (hide_lams, no_types) disjoint_iff_not_equal in_set_inner_verts_appendI_l)
    done
  show ?case
  proof (rule ccontr)
    assume A: "\<not>?thesis"
    then obtain es' e' where "es = es' @ [e']" "es \<noteq> []"
      by (cases es rule: rev_cases) auto

    have "fst e \<in> set (inner_verts es)"
      using A \<open>distinct (inner_verts es)\<close>  \<open>es \<noteq> []\<close>
      by (auto simp: inner_verts_def)
    moreover
    have "fst e' \<noteq> fst e" "snd e' = fst e"
      using \<open>es = es' @ [e']\<close> snoc.prems(1)
      by (auto simp: awalk_Cons_iff dest: no_loops)
    ultimately
    obtain es'' e'' where "es' = es'' @ [e'']"
      by (cases es' rule: rev_cases) (auto simp: \<open>es = es' @ [e']\<close> inner_verts_def)
    then have "fst e'' \<noteq> fst e"
      using \<open>snd e' = fst e\<close>[symmetric] snoc.prems(1,3) unfolding \<open>es = _\<close>
      by (simp add: \<open>es = _\<close> awalk_Cons_iff progressing_append_iff progressing_Cons)

    have "fst e' \<in> set (inner_verts es)"
      using \<open>es = es' @ [e']\<close> \<open>es' = es'' @ [e'']\<close>
      by (cases es'') (auto simp: inner_verts_def)

    have "fst e \<in> set (inner_verts es')"
      using \<open>es = es' @ [e']\<close> \<open>fst e \<in> set (inner_verts es)\<close> \<open>fst e' \<noteq> fst e\<close>
      by (cases es')  (auto simp: inner_verts_def)
    then obtain q e'2 e'3 r where Z: "es' = q @ [e'2, e'3] @ r" "snd e'2 = fst e" "fst e'3 = fst e"
    proof -
      obtain e'3' where "e'3' \<in> set (tl es')" "fst e'3' = fst e"
        using \<open>fst e \<in> set (inner_verts es')\<close>
        by (cases es') (auto simp: inner_verts_def)
      then obtain q r where "tl es' = q @ e'3' # r"
        by (metis split_list)
      then have F2: "snd (last (hd es' # q)) = fst e"
        using \<open>es = es' @ [e']\<close> snoc.prems(1) \<open>fst e'3' = fst e\<close>
        apply (cases es')
         apply (case_tac [2] q rule: rev_cases)
          apply auto
        done
      then have "es' = (butlast (hd es' # q)) @ [last (hd es' # q), e'3'] @ r"
        using \<open>tl es' = q @ e'3' # r\<close> by (cases es') auto
      then show ?thesis using F2 \<open>fst e'3' = fst e\<close> by fact
    qed
    then have "fst e'2 \<noteq> snd e'3"
      using snoc.prems(3) unfolding \<open>es = _\<close>
      by (simp add: progressing_append_iff progressing_Cons)
    moreover
    from Z have B: "fst e'2 = u \<or> fst e'2 \<in> set (inner_verts es')"
      using \<open>es = es' @ [e']\<close> snoc.prems(1)
      by (cases q) (auto simp: inner_verts_def)
    then have "fst e'2 \<noteq> fst e'"
    proof
      assume "fst e'2 = u"
      then have "fst e'2 \<notin> set (inner_verts es)"
        using V \<open>es = es' @ [e']\<close> snoc.prems(2)
        by (cases es') (auto simp: inner_verts_def)
      moreover
      have "fst e' \<in> set (inner_verts es)"
        using \<open>es = es' @ [e']\<close> \<open>es' = es'' @ [e'']\<close>
        by (cases es'') (auto simp: inner_verts_def)
      ultimately show ?thesis by auto
    next
      assume "fst e'2 \<in> set (inner_verts es')"
      moreover
      have "fst e' \<in> set (inner_verts es)"
        using \<open>es = es' @ [e']\<close> \<open>es' = es'' @ [e'']\<close>
        by (cases es'') (auto simp: inner_verts_def)
      ultimately
      show ?thesis
        using \<open>distinct (inner_verts es)\<close> unfolding \<open>es = es' @ [e']\<close>
        by (cases es') (fastforce simp: inner_verts_def)+
    qed
    moreover
    have "snd e'3 \<noteq> fst e'"
    proof (rule notI, cases)
      assume "r = []" "snd e'3 = fst e'"
      then show False using Z \<open>es = es' @ [e']\<close> snoc.prems(3) \<open>snd e' = fst e\<close>
        by (simp add: progressing_append_iff progressing_Cons)
    next
      assume A: "r \<noteq> []" "snd e'3 = fst e'"
      then obtain r0 rs where "r = r0 # rs" by (cases r) auto
      then have "snd e'3 = fst r0"
        using Z \<open>es = es' @ [e']\<close> snoc.prems(1)
        by (auto simp: awalk_Cons_iff)
      with A have "fst r0 = fst e'" by auto
      have "\<not>distinct (inner_verts es)"
        by (cases q) (auto simp add: Z(1) \<open>es = es' @ [e']\<close>
          \<open>r = r0 # rs\<close> \<open>fst r0 = fst e'\<close> inner_verts_def)
      then show False using \<open>distinct (inner_verts es)\<close> by auto
    qed
    ultimately
    have card_to_fst_e: "card {e'2, (snd e'3, fst e'3), e'} = 3"
      by (auto simp: card_insert_if)
    moreover
    have "e'3 \<in> parcs G"
      using Z using snoc.prems(1) \<open>es = es' @ [e']\<close>
      by (auto intro: arcs_symmetric)
    then have "(snd e'3, fst e'3) \<in> parcs G"
      by (auto intro: arcs_symmetric)
    then have "{e'2, (snd e'3, fst e'3), e'} \<subseteq> {ed \<in> parcs G. snd ed = fst e}"
      using snoc.prems(1) \<open>es = es' @ [e']\<close> Z by auto
    moreover
    have "fst e \<in> pverts G" using snoc.prems(1) by auto
    then have card_to_fst_e_abs: "card {ed \<in> parcs G. snd ed = fst e} \<le> 2"
      using \<open>fst e \<in> set (inner_verts es)\<close> V snoc.prems(2)
      unfolding verts3_def in_degree_def
      by (cases es) (auto simp: inner_verts_def in_arcs_def)
    ultimately
    have "{e'2, (snd e'3, fst e'3), e'} = {ed \<in> parcs G. snd ed = fst e}"
      by (intro card_seteq) auto
    then show False
      using card_to_fst_e card_to_fst_e_abs by auto
  qed
qed


lemma (in wf_digraph) inner_verts_conv':
  assumes "awalk u p v" "2 \<le> length p" shows "inner_verts p = awalk_verts (head G (hd p)) (butlast (tl p))"
  using assms
  apply (cases p)
   apply (auto simp: awalk_Cons_iff; fail)
  apply (match premises in "p = _ # as" for as \<Rightarrow> \<open>cases as rule: rev_cases\<close>)
   apply (auto simp: inner_verts_def awalk_verts_conv)
  done

lemma verts3_in_verts:
  assumes "x \<in> verts3 G" shows "x \<in> verts G"
  using assms unfolding verts3_def by auto

lemma (in pair_graph) deg2_awalk_is_iapath:
  assumes V: "verts3 G \<subseteq> V" "V \<subseteq> pverts G"
  assumes p: "awalk u p v" "set (inner_verts p) \<inter> V = {}" "progressing p"
  assumes in_V: "u \<in> V" "v \<in> V"
  assumes "u \<noteq> v"
  shows "gen_iapath V u p v"
proof (cases p)
  case Nil then show ?thesis using p(1) in_V \<open>u \<noteq> v\<close> by (auto simp: apath_def gen_iapath_def)
next
  case (Cons p0 ps)
  then have ev_p: "awalk_verts u p = u # butlast (tl (awalk_verts u p)) @ [v]"
    using p(1) by (cases p) auto

  have "u \<notin> set (inner_verts p)" "v \<notin> set (inner_verts p)"
    using p(2) in_V by auto
  with verts2_awalk_distinct[OF V in_V(1) p] have "distinct (awalk_verts u p)"
    using p(1) \<open>u \<noteq> v\<close> by (subst ev_p) (auto simp: inner_verts_conv[of p u] verts3_def)
  then show ?thesis using p(1-2) in_V \<open>u \<noteq> v\<close> by (auto simp: apath_def gen_iapath_def)
qed

lemma (in pair_graph) inner_verts_min_degree:
  assumes walk_p: "awalk u p v" and progress: "progressing p"
  and w_p: "w \<in> set (inner_verts p)"
  shows "2 \<le>in_degree G w"
proof -
  from w_p have "2 \<le> length p" using not_le by fastforce
  moreover
  then obtain e1 es e2 where p_decomp: "p = e1 # es @ [e2]"
    by (metis One_nat_def Suc_1 Suc_eq_plus1 le0 list.size(3) list.size(4) neq_Nil_conv not_less_eq_eq rev_cases)
  ultimately
  have w_es: "w \<in> set (awalk_verts (snd e1) es)"
    using walk_p w_p by (auto simp: apath_def inner_verts_conv')

  have walk_es: "awalk (snd e1) es (fst e2)"
    using walk_p by (auto simp: p_decomp awalk_simps)
  obtain q r where es_decomp: "es = q @ r" "awalk (snd e1) q w" "awalk w r (fst e2)"
    using awalk_decomp[OF walk_es w_es] by auto

  define xs x y ys
    where "xs = butlast (e1 # q)" and "x = last (e1 # q)"
      and "y = hd (r @ [e2])" and "ys = tl (r @ [e2])"
  then have "p = xs @ x # y # ys"
    by (auto simp: p_decomp es_decomp)
  moreover
  have "awalk u (e1 # q) w" "awalk w (r @ [e2]) v"
    using walk_p es_decomp p_decomp by (auto simp: awalk_Cons_iff)
  then have inc_w: "snd x = w" "fst y = w"
    unfolding x_def y_def
     apply -
     apply (auto simp: awalk_Cons_iff awalk_verts_conv; fail)
    apply (cases r)
     apply auto
    done
  ultimately have "fst x \<noteq> snd y"
    using progress by (auto simp: progressing_append_iff progressing_Cons)

  have "x \<in> parcs G" "y \<in> parcs G"
    using walk_p \<open>p = xs @ x # y # ys\<close> by auto
  then have "{x, (snd y, w)} \<subseteq> {e \<in> parcs G. snd e = w}"
    using inc_w by auto (metis arcs_symmetric surjective_pairing)
  then have "card {x, (snd y, w)} \<le> in_degree G w"
    unfolding in_degree_def by (intro card_mono) auto
  then show ?thesis using \<open>fst x \<noteq> snd y\<close> inc_w
    by (auto simp: card_insert_if split: if_split_asm)
qed

lemma (in pair_pseudo_graph) gen_iapath_same2E:
  assumes "verts3 G \<subseteq> V" "V \<subseteq> pverts G"
  and "gen_iapath V u p v" "gen_iapath V w q x"
  and "e \<in> set p" "e \<in> set q"
  obtains "p = q"
using assms same_gen_iapath_by_common_arc by metis



definition mk_graph' :: "IGraph \<Rightarrow> ig_vertex pair_pre_digraph" where
  "mk_graph' IG \<equiv> \<lparr> pverts = set (ig_verts IG), parcs = set (ig_arcs IG)\<rparr>"

definition mk_graph :: "IGraph \<Rightarrow> ig_vertex pair_pre_digraph" where
  "mk_graph IG \<equiv> mk_symmetric (mk_graph' IG)"

lemma verts_mkg': "pverts (mk_graph' G) = set (ig_verts G)"
  unfolding mk_graph'_def by simp

lemma arcs_mkg': "parcs (mk_graph' G) = set (ig_arcs G)"
  unfolding mk_graph'_def by simp

lemmas mkg'_simps = verts_mkg' arcs_mkg'

lemma verts_mkg: "pverts (mk_graph G) = set (ig_verts G)"
  unfolding mk_graph_def by (simp add: mkg'_simps )

lemma parcs_mk_symmetric_symcl: "parcs (mk_symmetric G) = (arcs_ends G)\<^sup>s"
  by (auto simp: parcs_mk_symmetric symcl_def arcs_ends_conv)

lemma arcs_mkg: "parcs (mk_graph G) = (set (ig_arcs G))\<^sup>s"
  unfolding mk_graph_def parcs_mk_symmetric_symcl by (simp add: arcs_mkg')

lemmas mkg_simps = verts_mkg arcs_mkg



definition iadj :: "IGraph \<Rightarrow> ig_vertex \<Rightarrow> ig_vertex \<Rightarrow> bool" where
  "iadj G u v \<equiv> (u,v) \<in> set (ig_arcs G) \<or> (v,u) \<in> set (ig_arcs G)"

definition "loop_free G \<equiv> (\<forall>e \<in> parcs G. fst e \<noteq> snd e)"


lemma ig_opposite_simps:
  "ig_opposite G (u,v) u = v" "ig_opposite G (v,u) u = v"
unfolding ig_opposite_def by auto

lemma distinct_ig_verts:
  "distinct (ig_verts G)"
by (cases G) (auto simp: ig_verts_def Abs_IGraph_inverse)

lemma set_ig_arcs_verts:
  assumes "IGraph_inv G" "(u,v) \<in> set (ig_arcs G)" shows "u \<in> set (ig_verts G)" "v \<in> set (ig_verts G)"
  using assms unfolding IGraph_inv_def
  by (auto simp: mkg'_simps dest: all_nth_imp_all_set)

lemma IGraph_inv_conv:
  "IGraph_inv G \<longleftrightarrow> pair_fin_digraph (mk_graph' G)"
proof -
  { assume "\<forall>e\<in>set (ig_arcs G). fst e \<in> set (ig_verts G) \<and> snd e \<in> set (ig_verts G)"
    then have "pair_fin_digraph (mk_graph' G)"
      by unfold_locales (auto simp: mkg'_simps) }
  moreover
  { assume "pair_fin_digraph (mk_graph' G)"
    then interpret pair_fin_digraph "mk_graph' G" .
    have "\<forall>e\<in>set (ig_arcs G). fst e \<in> set (ig_verts G) \<and> snd e \<in> set (ig_verts G)"
      using tail_in_verts head_in_verts
      by (fastforce simp: mkg'_simps in_set_conv_nth) }
  ultimately
  show ?thesis unfolding IGraph_inv_def by blast
qed

lemma IGraph_inv_conv':
  "IGraph_inv G \<longleftrightarrow> pair_pseudo_graph (mk_graph G)"
  unfolding IGraph_inv_conv
proof
  assume "pair_fin_digraph (mk_graph' G)"
  interpret ppd: pair_fin_digraph "mk_graph' G" by fact
  interpret pd: pair_fin_digraph "mk_graph G"
    unfolding mk_graph_def ..
  show "pair_pseudo_graph (mk_graph G)"
    by unfold_locales (auto simp: mk_graph_def symmetric_mk_symmetric)
next
  assume A: "pair_pseudo_graph (mk_graph G)"
  interpret ppg: pair_pseudo_graph "mk_graph G" by fact
  show "pair_fin_digraph (mk_graph' G)"
    using ppg.wellformed'
    by unfold_locales (auto simp: mkg_simps mkg'_simps symcl_def, auto)
qed

lemma iadj_io_edge:
  assumes "u \<in> set (ig_verts G)" "e \<in> set (ig_in_out_arcs G u)"
  shows "iadj G u (ig_opposite G e u)"
proof -
  from assms obtain v where e: "e = (u,v) \<or>  e = (v,u)" "e \<in> set (ig_arcs G)"
    unfolding ig_in_out_arcs_def by (cases e) auto
  then have *: "ig_opposite G e u = v" by safe (auto simp: ig_opposite_def)

  show ?thesis using e unfolding iadj_def * by auto
qed

lemma All_set_ig_verts: "(\<forall>v \<in> set (ig_verts G). P v) \<longleftrightarrow> (\<forall>i < ig_verts_cnt G. P (ig_verts G ! i))"
  by (metis in_set_conv_nth ig_verts_cnt_def)

lemma IGraph_imp_ppd_mkg':
  assumes "IGraph_inv G" shows "pair_fin_digraph (mk_graph' G)"
  using assms unfolding IGraph_inv_conv by auto

lemma finite_symcl_iff: "finite (R\<^sup>s) \<longleftrightarrow> finite R"
  unfolding symcl_def by blast

lemma (in pair_fin_digraph) pair_pseudo_graphI_mk_symmetric:
  "pair_pseudo_graph (mk_symmetric G)"
  by unfold_locales
     (auto simp: parcs_mk_symmetric symmetric_mk_symmetric wellformed')

lemma IGraph_imp_ppg_mkg:
  assumes "IGraph_inv G" shows "pair_pseudo_graph (mk_graph G)"
  using assms unfolding mk_graph_def
  by (intro pair_fin_digraph.pair_pseudo_graphI_mk_symmetric IGraph_imp_ppd_mkg')

lemma IGraph_lf_imp_pg_mkg:
  assumes "IGraph_inv G" "loop_free (mk_graph G)" shows "pair_graph (mk_graph G)"
proof -
  interpret ppg: pair_pseudo_graph "mk_graph G"
    using assms(1) by (rule IGraph_imp_ppg_mkg)
  show "pair_graph (mk_graph G)"
    using assms by unfold_locales (auto simp: loop_free_def)
qed

lemma set_ig_arcs_imp_verts:
  assumes "(u,v) \<in> set (ig_arcs G)" "IGraph_inv G" shows "u \<in> set (ig_verts G)" "v \<in> set (ig_verts G)"
proof -
  interpret pair_pseudo_graph "mk_graph G"
    using assms by (auto intro: IGraph_imp_ppg_mkg)
  from assms have "(u,v) \<in> parcs (mk_graph G)" by (simp add: mkg_simps symcl_def)
  then have "u \<in> pverts (mk_graph G)" "v \<in> pverts (mk_graph G)" by (auto dest: wellformed')
  then show "u \<in> set (ig_verts G)" "v \<in> set (ig_verts G)" by (auto simp: mkg_simps)
qed

lemma iadj_imp_verts:
  assumes "iadj G u v" "IGraph_inv G" shows "u \<in> set (ig_verts G)" "v \<in> set (ig_verts G)"
  using assms unfolding iadj_def by (auto dest: set_ig_arcs_imp_verts)

lemma card_ig_neighbors_indegree:
  assumes "IGraph_inv G"
  shows "card (ig_neighbors G u) = in_degree (mk_graph G) u"
proof -
  have inj2: "inj_on (\<lambda>e. ig_opposite G e u) {e \<in> parcs (mk_graph G). snd e = u}"
    unfolding ig_opposite_def by (rule inj_onI) (fastforce split: if_split_asm)

  have "ig_neighbors G u = (\<lambda>e. ig_opposite G e u) ` {e \<in> parcs (mk_graph G). snd e = u}"
    using assms unfolding ig_neighbors_def
    by (auto simp: ig_opposite_simps symcl_def mkg_simps set_ig_arcs_verts intro!: rev_image_eqI)
  then have "card (ig_neighbors G u) = card ((\<lambda>e. ig_opposite G e u) ` {e \<in> parcs (mk_graph G). snd e = u})"
    by simp
  also have "\<dots> = in_degree (mk_graph G) u"
    unfolding in_degree_def in_arcs_def with_proj_simps
    using inj2 by (rule card_image)
  finally show ?thesis .
qed

lemma iadjD:
  assumes "iadj G u v"
  shows "\<exists>e \<in> set (ig_in_out_arcs G u). (e = (u,v) \<or> e = (v,u))"
proof -
  from assms obtain e where "e \<in> set (ig_arcs G)" "e = (u,v) \<or> e = (v,u)"
    unfolding iadj_def by auto
  then show ?thesis unfolding ig_in_out_arcs_def by auto
qed

lemma
  ig_verts_empty[simp]: "ig_verts ig_empty = []" and
  ig_verts_add_e[simp]: "ig_verts (ig_add_e G u v) = ig_verts G" and
  ig_verts_add_v[simp]: "ig_verts (ig_add_v G v) = ig_verts G @ (if v \<in> set (ig_verts G) then [] else [v])"
  unfolding ig_verts_def ig_empty_def ig_add_e_def ig_add_v_def
  by (auto simp: Abs_IGraph_inverse distinct_ig_verts[simplified ig_verts_def])

lemma
  ig_arcs_empty[simp]: "ig_arcs ig_empty = []" and
  ig_arcs_add_e[simp]: "ig_arcs (ig_add_e G u v) = ig_arcs G @ [(u,v)]" and
  ig_arcs_add_v[simp]: "ig_arcs (ig_add_v G v) = ig_arcs G"
  unfolding ig_arcs_def ig_empty_def ig_add_e_def ig_add_v_def
  by (auto simp: Abs_IGraph_inverse distinct_ig_verts)



subsection \<open>Total Correctness\<close>

subsubsection \<open>Procedure @{term is_subgraph}\<close>

definition is_subgraph_verts_inv :: "IGraph \<Rightarrow> IGraph \<Rightarrow> nat \<Rightarrow> bool" where
  "is_subgraph_verts_inv G H i \<equiv> set (take i (ig_verts G)) \<subseteq> set (ig_verts H)"

definition is_subgraph_arcs_inv :: "IGraph \<Rightarrow> IGraph \<Rightarrow> nat \<Rightarrow> bool" where
  "is_subgraph_arcs_inv G H i \<equiv> \<forall>j < i. let (u,v) = ig_arcs G ! j in
    ((u,v) \<in> set (ig_arcs H) \<or> (v,u) \<in> set (ig_arcs H))
    \<and> u \<in> set (ig_verts G) \<and> v \<in> set (ig_verts G)"

lemma is_subgraph_verts_0: "is_subgraph_verts_inv G H 0"
  unfolding is_subgraph_verts_inv_def by auto

lemma is_subgraph_verts_step:
  assumes "is_subgraph_verts_inv G H i" "ig_verts G ! i \<in> set (ig_verts H)"
  assumes "i < length (ig_verts G)"
  shows "is_subgraph_verts_inv G H (Suc i)"
  using assms by (auto simp: is_subgraph_verts_inv_def take_Suc_conv_app_nth)

lemma is_subgraph_verts_last:
  "is_subgraph_verts_inv G H (length (ig_verts G)) \<longleftrightarrow> pverts (mk_graph G) \<subseteq> pverts (mk_graph H)"
  apply (auto simp: is_subgraph_verts_inv_def mkg_simps)
  done

lemma is_subgraph_arcs_0: "is_subgraph_arcs_inv G H 0"
  unfolding is_subgraph_arcs_inv_def by auto

lemma is_subgraph_arcs_step:
  assumes "is_subgraph_arcs_inv G H i"
    "e \<in> set (ig_arcs H) \<or> (snd e, fst e) \<in> set (ig_arcs H)"
    "fst e \<in> set (ig_verts G)" "snd e \<in> set (ig_verts G)"
  assumes "e = ig_arcs G ! i"
  assumes "i < length (ig_arcs G)"
  shows "is_subgraph_arcs_inv G H (Suc i)"
  using assms by (auto simp: is_subgraph_arcs_inv_def less_Suc_eq)

lemma wellformed_pseudo_graph_mkg:
  shows "pair_wf_digraph (mk_graph G) = pair_pseudo_graph(mk_graph G)" (is "?L = ?R")
proof
  assume ?R
  then interpret ppg: pair_pseudo_graph "mk_graph G" .
  show ?L by unfold_locales
next
  assume ?L
  moreover have "symmetric (mk_graph G)"
    unfolding mk_graph_def by (simp add: symmetric_mk_symmetric)
  ultimately show ?R
    unfolding pair_wf_digraph_def
    by unfold_locales (auto simp: mkg_simps finite_symcl_iff)
qed

lemma is_subgraph_arcs_last:
  "is_subgraph_arcs_inv G H (length (ig_arcs G)) \<longleftrightarrow> parcs (mk_graph G) \<subseteq> parcs (mk_graph H) \<and> pair_pseudo_graph (mk_graph G)"
proof -
  have "is_subgraph_arcs_inv G H (length (ig_arcs G))
      = (\<forall>(u,v) \<in> set (ig_arcs G). ((u,v) \<in> set (ig_arcs H) \<or> (v,u) \<in> set (ig_arcs H))
        \<and> u \<in> set (ig_verts G) \<and> v \<in> set (ig_verts G))"
    unfolding is_subgraph_arcs_inv_def
    by (metis (lifting, no_types) all_nth_imp_all_set nth_mem)
  also have "... \<longleftrightarrow> parcs (mk_graph G) \<subseteq> parcs (mk_graph H) \<and> pair_pseudo_graph (mk_graph G)"
    unfolding wellformed_pseudo_graph_mkg[symmetric]
    by (auto simp: mkg_simps pair_wf_digraph_def symcl_def)
  finally show ?thesis .
qed

lemma is_subgraph_verts_arcs_last:
  assumes "is_subgraph_verts_inv G H (ig_verts_cnt G)"
  assumes "is_subgraph_arcs_inv G H (ig_arcs_cnt G)"
  assumes "IGraph_inv H"
  shows "subgraph (mk_graph G) (mk_graph H)" (is ?T1)
        "pair_pseudo_graph (mk_graph G)" (is ?T2)
proof -
  interpret ppg: pair_pseudo_graph "mk_graph G"
    using assms by (simp add: is_subgraph_arcs_last)
  interpret ppgH: pair_pseudo_graph "mk_graph H" using assms by (intro IGraph_imp_ppg_mkg)
  have "wf_digraph (with_proj (mk_graph G))" by unfold_locales
  with assms show ?T1 ?T2
    by (auto simp: is_subgraph_verts_last is_subgraph_arcs_last subgraph_def ppgH.wf_digraph)
qed

lemma is_subgraph_false:
  assumes "subgraph (mk_graph G) (mk_graph H)"
  obtains "\<forall>i < length (ig_verts G). ig_verts G ! i \<in> set (ig_verts H)"
    "\<forall>i < length (ig_arcs G). let (u,v) = ig_arcs G ! i in
      ((u,v)\<in> set (ig_arcs H) \<or> (v,u) \<in> set (ig_arcs H))
      \<and> u \<in> set (ig_verts G) \<and> v \<in> set (ig_verts G)"
proof
  from assms
  show "\<forall>i < length (ig_verts G). ig_verts G ! i \<in> set (ig_verts H)"
  unfolding subgraph_def by (auto simp: mkg_simps)
next
  from assms have "is_subgraph_arcs_inv G H (length (ig_arcs G))"
    unfolding is_subgraph_arcs_last subgraph_def wellformed_pseudo_graph_mkg[symmetric]
    by (auto simp: wf_digraph_wp_iff)
  then show "\<forall>i < length (ig_arcs G). let (u,v) = ig_arcs G ! i in
      ((u,v)\<in> set (ig_arcs H) \<or> (v,u) \<in> set (ig_arcs H))
      \<and> u \<in> set (ig_verts G) \<and> v \<in> set (ig_verts G)"
    by (auto simp: is_subgraph_arcs_inv_def)
qed

lemma (in is_subgraph_impl) is_subgraph_spec:
  "\<forall>\<sigma>. \<Gamma> \<turnstile>\<^sub>t \<lbrace>\<sigma>. IGraph_inv \<acute>H \<rbrace> \<acute>R :== PROC is_subgraph(\<acute>G, \<acute>H) \<lbrace> \<acute>G = \<^bsup>\<sigma>\<^esup>G \<and> \<acute>H = \<^bsup>\<sigma>\<^esup>H \<and> \<acute>R = (subgraph (mk_graph \<acute>G) (mk_graph \<acute>H) \<and> IGraph_inv \<acute>G)\<rbrace>"
  apply (vcg_step spec=none)
  apply (rewrite
    at "whileAnno _ (named_loop ''verts'') _ _"
    in for (\<sigma>)
    to "whileAnno _
      \<lbrace> is_subgraph_verts_inv \<acute>G \<acute>H \<acute>i \<and> \<acute>G = \<^bsup>\<sigma>\<^esup>G \<and> \<acute>H = \<^bsup>\<sigma>\<^esup>H \<and> \<acute>i \<le> ig_verts_cnt \<acute>G
      \<and> IGraph_inv \<acute>H\<rbrace>
      (MEASURE ig_verts_cnt \<acute>G - \<acute>i)
      _"
    annotate_named_loop_var)
  apply (rewrite
    at "whileAnno _ (named_loop ''arcs'') _ _"
    in for (\<sigma>)
    to "whileAnno _
      \<lbrace> is_subgraph_arcs_inv \<acute>G \<acute>H \<acute>i \<and> \<acute>G = \<^bsup>\<sigma>\<^esup>G \<and> \<acute>H = \<^bsup>\<sigma>\<^esup>H \<and> \<acute>i \<le> ig_arcs_cnt \<acute>G
      \<and> is_subgraph_verts_inv \<acute>G \<acute>H (length (ig_verts \<acute>G)) \<and> IGraph_inv \<acute>H \<rbrace>
      (MEASURE ig_arcs_cnt \<acute>G - \<acute>i)
      _"
    annotate_named_loop_var)
  apply vcg
      apply (fastforce simp: is_subgraph_verts_0)
     apply (fastforce simp: is_subgraph_verts_step elim: is_subgraph_false)
    apply (fastforce simp: is_subgraph_arcs_0 not_less)
   apply (auto simp: is_subgraph_arcs_step elim!: is_subgraph_false; fastforce)
  apply (fastforce simp: IGraph_inv_conv' is_subgraph_verts_arcs_last)
  done

subsubsection \<open>Procedure @{term is_loop_free}\<close>

definition "is_loopfree_inv G k \<equiv> \<forall>j<k. fst (ig_arcs G ! j) \<noteq> snd (ig_arcs G ! j)"

lemma is_loopfree_0:
  "is_loopfree_inv G 0"
  by (auto simp: is_loopfree_inv_def)

lemma is_loopfree_step1:
  assumes "is_loopfree_inv G n"
  assumes "fst (ig_arcs G ! n) \<noteq> snd (ig_arcs G ! n)"
  assumes "n < ig_arcs_cnt G"
  shows "is_loopfree_inv G (Suc n)"
  using assms unfolding is_loopfree_inv_def
  by (auto intro: less_SucI elim: less_SucE)

lemma is_loopfree_step2:
  assumes "loop_free (mk_graph G)"
  assumes "n < ig_arcs_cnt G"
  shows "fst (ig_arcs G ! n) \<noteq> snd (ig_arcs G ! n)"
  using assms unfolding is_loopfree_inv_def loop_free_def
  by (auto simp: mkg_simps symcl_def)

lemma is_loopfree_last:
  assumes "is_loopfree_inv G (ig_arcs_cnt G)"
  shows "loop_free (mk_graph G)"
  using assms apply (auto simp: is_loopfree_inv_def loop_free_def mkg_simps in_set_conv_nth symcl_def)
  apply (metis fst_eqD snd_eqD)+
  done

lemma (in is_loopfree_impl) is_loopfree_spec:
  "\<forall>\<sigma>. \<Gamma> \<turnstile>\<^sub>t \<lbrace>\<sigma>. IGraph_inv \<acute>G \<rbrace> \<acute>R :== PROC is_loopfree(\<acute>G) \<lbrace> \<acute>G = \<^bsup>\<sigma>\<^esup>G \<and> \<acute>R = loop_free (mk_graph \<acute>G) \<rbrace>"
  apply (vcg_step spec=none)
  apply (rewrite
    at "whileAnno _ (named_loop ''loop'') _ _"
    in for (\<sigma>)
    to "whileAnno _
      \<lbrace> is_loopfree_inv \<acute>G \<acute>i \<and> \<acute>G = \<^bsup>\<sigma>\<^esup>G \<and> \<acute>i \<le> ig_arcs_cnt \<acute>G \<rbrace>
      (MEASURE ig_arcs_cnt \<acute>G - \<acute>i)
      _"
    annotate_named_loop_var)
  apply vcg
    apply (fastforce simp: is_loopfree_0)
   apply (fastforce intro: is_loopfree_step1 dest: is_loopfree_step2)
  apply (fastforce simp: is_loopfree_last)
  done



subsubsection \<open>Procedure @{term select_nodes}\<close>

definition select_nodes_inv :: "IGraph \<Rightarrow> IGraph \<Rightarrow> nat \<Rightarrow> bool" where
  "select_nodes_inv G H i \<equiv> set (ig_verts H) = {v \<in> set (take i (ig_verts G)). card (ig_neighbors G v) \<ge> 3} \<and> IGraph_inv H"

lemma select_nodes_inv_step:
  fixes G H i
  defines "v \<equiv> ig_verts G ! i"
  assumes G_inv: "IGraph_inv G"
  assumes sni_inv: "select_nodes_inv G H i"
  assumes less: "i < ig_verts_cnt G"
  assumes H': "H' = (if 3 \<le> card (ig_neighbors G v) then ig_add_v H v else H)"
  shows "select_nodes_inv G H' (Suc i)"
proof -
  have *: "IGraph_inv H'" using sni_inv H'
    unfolding IGraph_inv_def select_nodes_inv_def by auto
  have take_Suc_i: "take (Suc i) (ig_verts G) = take i (ig_verts G) @ [v]"
    using less unfolding v_def by (auto simp: take_Suc_conv_app_nth)
  have X: "v \<notin> set (take i (ig_verts G))"
    using G_inv less distinct_ig_verts unfolding v_def IGraph_inv_conv
    by (auto simp: distinct_conv_nth in_set_conv_nth)

  show ?thesis
    unfolding select_nodes_inv_def using X sni_inv
    by (simp only: *) (auto simp: take_Suc_i select_nodes_inv_def H')
qed

definition select_nodes_prop :: "IGraph \<Rightarrow> IGraph \<Rightarrow> bool" where
  "select_nodes_prop G H \<equiv> pverts (mk_graph H) = verts3 (mk_graph G)"

lemma (in select_nodes_impl) select_nodes_spec:
  "\<forall>\<sigma>. \<Gamma> \<turnstile>\<^sub>t \<lbrace>\<sigma>. IGraph_inv \<acute>G\<rbrace> \<acute>R :== PROC select_nodes(\<acute>G)
   \<lbrace> select_nodes_prop \<^bsup>\<sigma>\<^esup>G \<acute>R \<and> IGraph_inv \<acute>R \<and> set (ig_arcs \<acute>R) = {}\<rbrace>"
  apply vcg_step
  apply (rewrite
    at "whileAnno _ (named_loop ''loop'') _ _"
    in for (\<sigma>)
    to "whileAnno _
      \<lbrace> select_nodes_inv \<acute>G \<acute>R \<acute>i \<and> \<acute>i \<le> ig_verts_cnt \<acute>G \<and> \<acute>G = \<^bsup>\<sigma>\<^esup>G  \<and> IGraph_inv \<acute>G \<and> set (ig_arcs \<acute>R) = {}\<rbrace>
      (MEASURE ig_verts_cnt \<acute>G - \<acute>i)
      _"
    annotate_named_loop_var)
  apply vcg
    apply (fastforce simp: select_nodes_inv_def IGraph_inv_def mkg'_simps)
   apply (fastforce simp add: select_nodes_inv_step)
  apply (fastforce simp add: select_nodes_inv_def select_nodes_prop_def card_ig_neighbors_indegree verts3_def mkg_simps)
  done



subsubsection \<open>Procedure @{term find_endpoint}\<close>

definition find_endpoint_path_inv where
  "find_endpoint_path_inv G H len u v w x \<equiv>
    \<exists>p. pre_digraph.awalk (mk_graph G) u p x \<and> length p = len \<and>
      hd p = (u,v) \<and> last p = (w, x) \<and>
      set (pre_digraph.inner_verts (mk_graph G) p) \<inter> set (ig_verts H) = {} \<and>
      progressing p "

definition find_endpoint_arcs_inv where
  "find_endpoint_arcs_inv G found k v0 v1 v0' v1' \<equiv>
    (found \<longrightarrow> (\<exists>i < k. v1' = ig_opposite G (ig_in_out_arcs G v1 ! i) v1 \<and> v0' = v1 \<and> v0 \<noteq> v1')) \<and>
    (\<not>found \<longrightarrow> (\<forall>i < k. v0 = ig_opposite G (ig_in_out_arcs G v1 ! i) v1) \<and> v0 = v0' \<and> v1 = v1')"

lemma find_endpoint_path_first:
  assumes "iadj G u v" "u \<noteq> v" "IGraph_inv G"
  shows "find_endpoint_path_inv G H (Suc 0) u v u v"
proof -
  interpret ppg: pair_pseudo_graph "mk_graph G"
    using assms by (auto intro: IGraph_imp_ppg_mkg)
  have "(u,v) \<in> parcs (mk_graph G)"
    using assms by (auto simp: iadj_def mkg_simps symcl_def)
  then have "ppg.awalk u [(u,v)] v" "length [(u,v)] = Suc 0" "hd [(u,v)] = (u,v)" "last [(u,v)] = (u,v)" "progressing [(u,v)]"
    using assms by (auto simp: ppg.awalk_simps iadj_imp_verts mkg_simps progressing_Cons)
  moreover
  have "set (ppg.inner_verts [(u,v)]) \<inter> set (ig_verts H) = {}"
    by (auto simp: ppg.inner_verts_def)
  ultimately
  show ?thesis unfolding find_endpoint_path_inv_def by blast
qed

lemma find_endpoint_arcs_0:
  "find_endpoint_arcs_inv G False 0 v0 v1 v0 v1"
  unfolding find_endpoint_arcs_inv_def by auto

lemma find_endpoint_path_lastE:
  assumes "find_endpoint_path_inv G H len u v w x"
  assumes ig: "IGraph_inv G" and lf: "loop_free (mk_graph G)"
  assumes snp: "select_nodes_prop G H"
  assumes "0 < len"
  assumes u: "u \<in> set (ig_verts H)"
  obtains p where "pre_digraph.awalk (mk_graph G) u ((u,v) # p) x"
    and "progressing ((u,v) # p)"
    and "set (pre_digraph.inner_verts (mk_graph G) ((u,v) # p)) \<inter> set (ig_verts H) = {}"
    and "len \<le> ig_verts_cnt G"
proof -
  from ig and lf interpret pair_graph "mk_graph G"
    by (rule IGraph_lf_imp_pg_mkg)
  have [simp]: "verts3 (mk_graph G) = set (ig_verts H)"
    using assms unfolding select_nodes_prop_def by (auto simp: mkg_simps)
  from assms obtain q where q: "awalk u q x" "length q = len" "hd q = (u,v)"
    and iv: "set (inner_verts q) \<inter> verts3 (mk_graph G) = {}"
    and prg: "progressing q"
    unfolding find_endpoint_path_inv_def by auto
  moreover then obtain q0 qs where "q = q0 # qs" using \<open>0 < len\<close> by (cases q) auto
  moreover
  have "len \<le> ig_verts_cnt G"
  proof -
    have ev_q: "awalk_verts u q = u # inner_verts q @ [x]"
      unfolding inner_verts_conv[of q u] using q \<open>q = q0 # qs\<close> by auto
    then have len_ev: "length (awalk_verts u q) = 2 + length (inner_verts q)"
      by auto

    have set_av: "set (awalk_verts u q) \<subseteq> pverts (mk_graph G)"
      using q(1) by auto

    from snp u have "u \<in> verts3 (mk_graph G)" by simp
    moreover
    with _ _ have "distinct (inner_verts  q)"
      using q(1) iv prg by (rule verts2_awalk_distinct) (auto simp: verts3_def)
    ultimately
    have "distinct (u # inner_verts q)" using iv by auto
    moreover
    have "set (u # inner_verts q) \<subseteq> pverts (mk_graph G)"
      using ev_q set_av by auto
    ultimately
    have "length (u # inner_verts q) \<le> card (pverts (mk_graph G))"
      by (metis card_mono distinct_card finite_set verts_mkg)
    then have "length (awalk_verts u q) \<le> 1 + card (pverts (mk_graph G))"
      by (simp add: len_ev)
    then have "length q \<le> card (pverts (mk_graph G))"
      by (auto simp: length_awalk_verts)
    also have "\<dots> \<le> ig_verts_cnt G" by (auto simp: mkg_simps card_length)
    finally show ?thesis by (simp add: q)
  qed
  ultimately show ?thesis by (intro that) auto
qed

lemma find_endpoint_path_last1:
  assumes "find_endpoint_path_inv G H len u v w x"
  assumes ig: "IGraph_inv G" and lf: "loop_free (mk_graph G)"
  assumes snp: "select_nodes_prop G H"
  assumes "0 < len"
  assumes mem: "u \<in> set (ig_verts H)" "x \<in> set (ig_verts H)" "u \<noteq> x"
  shows "\<exists>p. pre_digraph.iapath (mk_graph G) u ((u,v) # p) x"
proof -
  from ig and lf interpret pair_graph "mk_graph G"
    by (rule IGraph_lf_imp_pg_mkg)
  have [simp]: "verts3 (mk_graph G) = set (ig_verts H)"
    "\<And>x. x \<in> set (ig_verts H) \<Longrightarrow> x \<in> pverts (mk_graph G)"
    using assms unfolding select_nodes_prop_def by (auto simp: mkg_simps verts3_def)
  show ?thesis
    apply (rule find_endpoint_path_lastE[OF assms(1-5) mem(1)])
    by (drule deg2_awalk_is_iapath[rotated 2]) (auto simp: mem)
qed

lemma find_endpoint_path_last2D:
  assumes path: "find_endpoint_path_inv G H len u v w u"
  assumes ig: "IGraph_inv G" and lf: "loop_free (mk_graph G)"
  assumes snp: "select_nodes_prop G H"
  assumes "0 < len"
  assumes mem: "u \<in> set (ig_verts H)"
  assumes iapath: "pre_digraph.iapath (mk_graph G) u ((u,v) # p) x"
  shows False
proof -
  from ig and lf interpret pair_graph "mk_graph G"
    by (rule IGraph_lf_imp_pg_mkg)
  have [simp]: "verts3 (mk_graph G) = set (ig_verts H)"
    using assms unfolding select_nodes_prop_def by (auto simp: mkg_simps)
  have V: "verts3 (mk_graph G) \<subseteq> verts3 (mk_graph G)" "verts3 (mk_graph G) \<subseteq> pverts (mk_graph G)"
    using verts3_in_verts[where G="mk_graph G"] by auto

  obtain q where walk_q: "awalk u ((u, v) # q) u" and
      progress_q: "progressing ((u, v) # q)" and
      iv_q: "set (inner_verts  ((u, v) # q)) \<inter> verts3 (mk_graph G) = {}"
    by (rule find_endpoint_path_lastE[OF path ig lf snp \<open>0 < len\<close> mem]) auto

  from iapath have walk_p: "awalk u ((u,v) # p) x" and
      iv_p: "set (inner_verts ((u, v) # p)) \<inter> verts3 (mk_graph G) = {}" and
      uv_verts3: "u \<in> verts3 (mk_graph G)" "x \<in> verts3 (mk_graph G)"
    unfolding gen_iapath_def apath_def by auto
  from iapath have progress_p: "progressing ((u,v) # p)"
    unfolding gen_iapath_def by (auto intro: apath_imp_progressing)

  from V walk_q walk_p progress_q progress_p iv_q iv_p
  have "(u,v) # q = (u,v) # p"
    apply (rule same_awalk_by_common_arc[where e="(u,v)"])
      using uv_verts3
      apply auto
    done
  then show False
    by (metis iapath apath_nonempty_ends gen_iapath_def awalk_nonempty_ends(2) walk_p walk_q)
qed

lemma find_endpoint_arcs_last:
  assumes arcs: "find_endpoint_arcs_inv G False (length (ig_in_out_arcs G v1)) v0 v1 v0a v1a"
  assumes path: "find_endpoint_path_inv G H len v_tail v_next v0 v1"
  assumes ig: "IGraph_inv G" and lf: "loop_free (mk_graph G)"
  assumes snp: "select_nodes_prop G H"
  assumes mem: "v_tail \<in> set (ig_verts H)"
  assumes "0 < len"
  shows "\<not> pre_digraph.iapath (mk_graph G) v_tail ((v_tail, v_next) # p) x"
proof
  let "\<not>?A" = "?thesis"
  assume ?A

  interpret pair_graph "mk_graph G" using ig lf by (rule IGraph_lf_imp_pg_mkg)

  have v3G_eq: "verts3 (mk_graph G) = set (ig_verts H)"
    using assms unfolding select_nodes_prop_def by (auto simp: mkg_simps)

  txt \<open>
    If no extending edge was found (as implied by @{thm arcs}), the last vertex of the walk
    computed (as implied by @{thm path}) is of degree 1. Hence we consider all vertices
    except the degree-2 nodes.
  \<close>
  define V where "V = {v \<in> pverts (mk_graph G). in_degree (mk_graph G) v \<noteq> 2}"

  have V: "verts3 (mk_graph G) \<subseteq> V" "V \<subseteq> pverts (mk_graph G)"
    unfolding verts3_def V_def by auto

  from \<open>?A\<close> have walk_p: "awalk v_tail ((v_tail, v_next) # p) x" and
      progress_p: "progressing ((v_tail, v_next) # p)"
    by (auto simp: gen_iapath_def apath_def intro: apath_imp_progressing)
  have iapath_V_p: "gen_iapath  V v_tail ((v_tail, v_next) # p) x"
  proof -
    { fix u assume A: "u \<in> set (inner_verts ((v_tail, v_next) # p))"
      then have "u \<in> pverts (mk_graph G)" using \<open>?A\<close>
        by (auto 2 4 simp: set_inner_verts gen_iapath_def apath_Cons_iff dest: awalkI_apath)
      with A \<open>?A\<close> inner_verts_min_degree[OF walk_p progress_p A] have "u \<notin> V"
        unfolding gen_iapath_def verts3_def V_def by auto }
    with \<open>?A\<close> V show ?thesis by (auto simp: gen_iapath_def)
  qed

  have arcs_p: "(v_tail, v_next) \<in> set ((v_tail, v_next) # p)"
    unfolding gen_iapath_def apath_def by auto

  have id_x: "2 < in_degree (mk_graph G) x"
    using \<open>?A\<close> unfolding gen_iapath_def verts3_def by auto

  from arcs have edge_no_pr: "\<And>e. e \<in> set (ig_in_out_arcs G v1) \<Longrightarrow>
      v0 = ig_opposite G e v1" and"v0 = v0a" "v1 = v1a"
    by (auto simp: find_endpoint_arcs_inv_def in_set_conv_nth)

  have "{e \<in> parcs (mk_graph G). snd e = v1} \<subseteq> {(v0,v1)}" (is "?L \<subseteq> ?R")
  proof
    fix e assume "e \<in> ?L"
    then have "fst e \<noteq> snd e" by (auto dest: no_loops)
    moreover
    from \<open>e \<in> ?L\<close> have "e \<in> set (ig_in_out_arcs G v1) \<or> (snd e, fst e) \<in> set (ig_in_out_arcs G v1)"
      by (auto simp: mkg_simps ig_in_out_arcs_def symcl_def)
    then have "v0 = ig_opposite G e v1 \<or> v0 = ig_opposite G (snd e, fst e) v1"
      by (auto intro: edge_no_pr)
    ultimately show "e \<in> ?R" using \<open>e \<in> ?L\<close> by (auto simp: ig_opposite_def)
  qed
  then have id_v1: "in_degree (mk_graph G) v1 \<le> card {(v0,v1)}"
    unfolding in_degree_def in_arcs_def by (intro card_mono) auto

  from path obtain q where walk_q: "awalk v_tail q v1" and
      q_props: "length q = len" "hd q = (v_tail, v_next)" and
      iv_q': "set (inner_verts q) \<inter> verts3 (mk_graph G) = {}" and
      progress_q: "progressing q"
    by (auto simp: find_endpoint_path_inv_def v3G_eq)
  then have "v1 \<in> pverts (mk_graph G)"
    by (metis awalk_last_in_verts)
  then have "v1 \<in> V" using id_v1 unfolding V_def by auto

  { fix u assume A: "u \<in> set (inner_verts q)"
    then have "u \<in> set (pawalk_verts v_tail q)" using walk_q
      by (auto simp: inner_verts_conv[where u=v_tail] awalk_def dest: in_set_butlastD list_set_tl)
    then have "u \<in> pverts (mk_graph G)" using walk_q by auto
    with A iv_q' inner_verts_min_degree[OF walk_q progress_q A] have "u \<notin> V"
      unfolding verts3_def V_def by auto }
  then have iv_q: "set (inner_verts q) \<inter> V = {}" by auto

  have arcs_q: "(v_tail, v_next) \<in> set q"
    using q_props \<open>0 < len\<close> by (cases q) auto

  have neq: "v_tail \<noteq> v1"
    using find_endpoint_path_last2D[OF _ ig lf snp \<open>0 < len\<close> \<open>v_tail \<in> _\<close> \<open>?A\<close>] path by auto

  have in_V: "v_tail \<in> V" using iapath_V_p unfolding gen_iapath_def by auto
  have iapath_V_q: "gen_iapath V v_tail q v1"
    using V walk_q iv_q progress_q in_V \<open>v1 \<in> V\<close> neq by (rule deg2_awalk_is_iapath)

  have "((v_tail, v_next) # p) = q"
    using V iapath_V_p iapath_V_q arcs_p arcs_q
    by (rule same_gen_iapath_by_common_arc)
  then have "v1 = x" using walk_p walk_q by auto
  then show False using id_v1 id_x by auto
qed

lemma find_endpoint_arcs_step1E:
  assumes "find_endpoint_arcs_inv G False k v0 v1 v0' v1'"
  assumes "ig_opposite G (ig_in_out_arcs G v1 ! k) v1' \<noteq> v0'"
  obtains "v0 = v0'" "v1 = v1'" "find_endpoint_arcs_inv G True (Suc k) v0 v1 v1 (ig_opposite G (ig_in_out_arcs G v1 ! k) v1)"
  using assms unfolding find_endpoint_arcs_inv_def
  by (auto intro: less_SucI elim: less_SucE)

lemma find_endpoint_arcs_step2E:
  assumes "find_endpoint_arcs_inv G False k v0 v1 v0' v1'"
  assumes "ig_opposite G (ig_in_out_arcs G v1 ! k) v1' = v0'"
  obtains "v0 = v0'" "v1 = v1'" "find_endpoint_arcs_inv G False (Suc k) v0 v1 v0 v1"
  using assms unfolding find_endpoint_arcs_inv_def
  by (auto intro: less_SucI elim: less_SucE)

lemma find_endpoint_path_step:
  assumes path: "find_endpoint_path_inv G H len u v w x" and "0 < len"
  assumes arcs: "find_endpoint_arcs_inv G True k w x w' x'"
  "k \<le> length (ig_in_out_arcs G x)"
  assumes ig: "IGraph_inv G"
  assumes not_end: "x \<notin> set (ig_verts H)"
  shows "find_endpoint_path_inv G H (Suc len) u v w' x'"
proof -
  interpret pg: pair_pseudo_graph "mk_graph G"
    using ig by (auto intro: IGraph_imp_ppg_mkg)
  from path obtain p where awalk: "pg.awalk u p x" and
      p: "length p = len" "hd p = (u, v)" "last p = (w, x)" and
      iv: "set (pg.inner_verts p) \<inter> set (ig_verts H) = {}" and
      progress: "progressing p"
    by (auto simp: find_endpoint_path_inv_def)

  define p' where "p' = p @ [(x,x')]"

  from path have "x \<in> set (ig_verts G)"
    by (metis awalk pg.awalk_last_in_verts verts_mkg)

  with arcs have "iadj G x x'" "x = w'" "w \<noteq> x'"
    using \<open>x \<in> set (ig_verts G)\<close> unfolding find_endpoint_arcs_inv_def
    by (auto intro: iadj_io_edge)
  then have "(x,x') \<in> parcs (mk_graph G)" "x' \<in> set (ig_verts G)"
    using ig unfolding iadj_def by (auto simp: mkg_simps set_ig_arcs_imp_verts symcl_def)
  then have "pg.awalk u p' x'"
    unfolding p'_def using awalk by (auto simp: pg.awalk_simps mkg_simps)
  moreover
  have "length p' = Suc len" "hd p' = (u,v)" "last p' = (w',x')"
    using \<open>x = w'\<close> \<open>0 < len\<close> p by (auto simp: p'_def)
  moreover
  have "set (pg.inner_verts p') \<inter> set (ig_verts H) = {}"
    using iv not_end p \<open>0 < len\<close> unfolding p'_def by (auto simp: pg.inner_verts_def)
  moreover
  { fix ys y z zs have "p' \<noteq> ys @ [(y,z), (z,y)] @ zs"
    proof
      let "\<not>?A" = "?thesis"
      assume ?A
      from progress have "\<And>zs. p \<noteq> ys @ (y,z) # (z,y) # zs"
        by (auto simp: progressing_append_iff progressing_Cons)
      with \<open>?A\<close> have "zs = []" unfolding p'_def by (cases zs rule: rev_cases) auto
      then show False using \<open>?A\<close> using \<open>w \<noteq> x'\<close> \<open>last p = (w,x)\<close> unfolding p'_def by auto
    qed }
  then have "progressing p'" by (auto simp: progressing_def)
  ultimately show ?thesis unfolding find_endpoint_path_inv_def by blast
qed

lemma no_loop_path:
  assumes "u = v" and ig: "IGraph_inv G"
  shows "\<not> (\<exists>p w. pre_digraph.iapath (mk_graph G) u ((u, v) # p) w)"
proof -
  interpret ppg: pair_pseudo_graph "mk_graph G"
    using ig by (rule IGraph_imp_ppg_mkg)
  from \<open>u = v\<close> show ?thesis
    by (auto simp: ppg.gen_iapath_def ppg.apath_Cons_iff)
       (metis hd_in_set ppg.awalk_verts_non_Nil ppg.awhd_of_awalk pre_digraph.awalkI_apath)
qed

lemma (in find_endpoint_impl) find_endpoint_spec:
  "\<forall>\<sigma>. \<Gamma> \<turnstile>\<^sub>t \<lbrace>\<sigma>. select_nodes_prop \<acute>G \<acute>H \<and> loop_free (mk_graph \<acute>G) \<and> \<acute>v_tail \<in> set (ig_verts \<acute>H) \<and> iadj \<acute>G \<acute>v_tail \<acute>v_next \<and> IGraph_inv \<acute>G\<rbrace>
    \<acute>R :== PROC find_endpoint(\<acute>G, \<acute>H, \<acute>v_tail, \<acute>v_next)
  \<lbrace>case \<acute>R of None \<Rightarrow> \<not>(\<exists>p w. pre_digraph.iapath (mk_graph \<^bsup>\<sigma>\<^esup>G) \<^bsup>\<sigma>\<^esup>v_tail ((\<^bsup>\<sigma>\<^esup>v_tail, \<^bsup>\<sigma>\<^esup>v_next) # p) w)
    | Some w \<Rightarrow> (\<exists>p. pre_digraph.iapath (mk_graph \<^bsup>\<sigma>\<^esup>G) \<^bsup>\<sigma>\<^esup>v_tail ((\<^bsup>\<sigma>\<^esup>v_tail, \<^bsup>\<sigma>\<^esup>v_next) # p) w) \<rbrace>"
  apply vcg_step
  apply (rewrite
    at "whileAnno _ (named_loop ''path'') _ _"
    in for (\<sigma>)
    to "whileAnno _
      \<lbrace> find_endpoint_path_inv \<acute>G \<acute>H \<acute>len \<acute>v_tail \<acute>v_next \<acute>v0 \<acute>v1
        \<and> \<acute>v_tail = \<^bsup>\<sigma>\<^esup>v_tail \<and> \<acute>v_next = \<^bsup>\<sigma>\<^esup>v_next \<and> \<acute>G = \<^bsup>\<sigma>\<^esup>G \<and> \<acute>H = \<^bsup>\<sigma>\<^esup>H
        \<and> 0 < \<acute> len
        \<and> \<acute>v_tail \<in> set (ig_verts \<acute>H) \<and> select_nodes_prop \<acute>G \<acute>H \<and> IGraph_inv \<acute>G \<and> loop_free (mk_graph \<acute>G) \<rbrace>
      (MEASURE Suc (ig_verts_cnt \<acute>G) - \<acute>len)
      _"
    annotate_named_loop_var)
  apply (rewrite
    at "whileAnno _ (named_loop ''arcs'') _ _"
    in for (\<sigma>)
    to "whileAnnoFix _
      (\<lambda>(v0,v1,len). \<lbrace> find_endpoint_arcs_inv \<acute>G \<acute>found \<acute>i v0 v1 \<acute>v0 \<acute>v1
        \<and> \<acute>i \<le> length (ig_in_out_arcs \<acute>G v1) \<and> \<acute>io_arcs = ig_in_out_arcs \<acute>G v1
        \<and> \<acute>v_tail = \<^bsup>\<sigma>\<^esup>v_tail \<and> \<acute>v_next = \<^bsup>\<sigma>\<^esup>v_next \<and> \<acute>G = \<^bsup>\<sigma>\<^esup>G \<and> \<acute>H = \<^bsup>\<sigma>\<^esup> H
        \<and> \<acute>len = len
        \<and> \<acute>v_tail \<in> set (ig_verts \<acute>H) \<and> select_nodes_prop \<acute>G \<acute>H \<and> IGraph_inv \<acute>G \<rbrace>)
      (\<lambda>_. (MEASURE length \<acute>io_arcs - \<acute>i))
      _"
    annotate_named_loop_var_fix)
  apply vcg
     apply (fastforce simp: find_endpoint_path_first no_loop_path)
    apply (match premises in "find_endpoint_path_inv _ _ _ _ _ v0 v1" for v0 v1
      \<Rightarrow> \<open>rule exI[where x=v0], rule exI[where x=v1]\<close>)
    apply (fastforce simp: find_endpoint_arcs_last find_endpoint_arcs_0 find_endpoint_path_step elim: find_endpoint_path_lastE)
   apply (fastforce elim: find_endpoint_arcs_step1E find_endpoint_arcs_step2E)
  apply (fastforce dest: find_endpoint_path_last1 find_endpoint_path_last2D)
done


subsubsection \<open>Procedure @{term contract}\<close>

definition contract_iter_nodes_inv where
  "contract_iter_nodes_inv G H k \<equiv>
    set (ig_arcs H) = (\<Union>i<k. {(u,v). u = (ig_verts H ! i) \<and> (\<exists>p. pre_digraph.iapath (mk_graph G) u p v)})"

definition contract_iter_adj_inv :: "IGraph \<Rightarrow> IGraph \<Rightarrow> IGraph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "contract_iter_adj_inv G H0 H u l \<equiv> (set (ig_arcs H) - ({u} \<times> UNIV) = set (ig_arcs H0)) \<and>
    ig_verts H = ig_verts H0 \<and>
    (\<forall>v. (u,v) \<in> set (ig_arcs H) \<longleftrightarrow>
      ((\<exists>j<l. \<exists>p. pre_digraph.iapath (mk_graph G) u ((u, ig_opposite G (ig_in_out_arcs G u ! j) u) # p) v)))"

lemma contract_iter_adj_invE:
  assumes "contract_iter_adj_inv G H0 H u l"
  obtains "set (ig_arcs H) - ({u} \<times> UNIV) = set (ig_arcs H0)" "ig_verts H = ig_verts H0"
    "\<And>v. (u,v) \<in> set (ig_arcs H) \<longleftrightarrow> ((\<exists>j<l. \<exists>p. pre_digraph.iapath (mk_graph G) u ((u, ig_opposite G (ig_in_out_arcs G u ! j) u) # p) v))"
using assms unfolding contract_iter_adj_inv_def by auto

lemma contract_iter_adj_inv_def':
  "contract_iter_adj_inv G H0 H u l \<longleftrightarrow> (
    set (ig_arcs H) - ({u} \<times> UNIV) = set (ig_arcs H0)) \<and> ig_verts H = ig_verts H0 \<and>
    (\<forall>v. ((\<exists>j<l. \<exists>p. pre_digraph.iapath (mk_graph G) u ((u, ig_opposite G (ig_in_out_arcs G u ! j) u) # p) v) \<longrightarrow> (u,v) \<in> set (ig_arcs H)) \<and>
      ((u,v) \<in> set (ig_arcs H) \<longrightarrow> ((\<exists>j<l. \<exists>p. pre_digraph.iapath (mk_graph G) u ((u, ig_opposite G (ig_in_out_arcs G u ! j) u) # p) v))))"
      unfolding contract_iter_adj_inv_def by metis

lemma select_nodes_prop_add_e[simp]:
  "select_nodes_prop G (ig_add_e H u v) = select_nodes_prop G H"
  by (simp add: select_nodes_prop_def mkg_simps)

lemma contract_iter_adj_inv_step1:
  assumes "pair_pseudo_graph (mk_graph G)"
  assumes ciai: "contract_iter_adj_inv G H0 H u l"
  assumes iapath: "pre_digraph.iapath (mk_graph G) u ((u, ig_opposite G (ig_in_out_arcs G u ! l) u) # p) w"
  shows "contract_iter_adj_inv G H0 (ig_add_e H u w) u (Suc l)"
proof -
  interpret pair_pseudo_graph "mk_graph G" by fact
  { fix v j assume *: "j < Suc l" "\<exists>p. iapath u ((u, ig_opposite G (ig_in_out_arcs G u ! j) u) # p) v"
    then have "(u, v) \<in> set (ig_arcs (ig_add_e H u w))"
    proof (cases "j < l")
      case True with * ciai show ?thesis
        by (auto simp: contract_iter_adj_inv_def)[]
    next
      case False with * have "j = l" by arith
      with *(2) obtain q where **: "iapath u ((u, ig_opposite G (ig_in_out_arcs G u ! l) u) # q) v"
        by metis
      with iapath have "p = q"
        using verts3_in_verts[where G="mk_graph G"]
        by (auto elim: gen_iapath_same2E[rotated 2])
      with ** iapath have "v = w"
        by (auto simp: pre_digraph.gen_iapath_def pre_digraph.apath_def elim: pre_digraph.awalk_nonempty_ends[rotated])
      then show ?thesis by simp
    qed }
  moreover
  { fix v assume *: "(u,v) \<in> set (ig_arcs (ig_add_e H u w))"
    have "(\<exists>j<Suc l. \<exists>p. gen_iapath (verts3 (mk_graph G)) u ((u, ig_opposite G (ig_in_out_arcs G u ! j) u) # p) v)"
    proof cases
      assume "v = w" then show ?thesis using iapath by auto
    next
      assume "v \<noteq> w" then show ?thesis using ciai *
        unfolding contract_iter_adj_inv_def by (auto intro: less_SucI)
    qed }
  moreover
  have "set (ig_arcs (ig_add_e H u w)) - ({u} \<times> UNIV) = set (ig_arcs H0)"
      "ig_verts (ig_add_e H u w) = ig_verts H0"
    using ciai unfolding contract_iter_adj_inv_def by auto
  ultimately
  show ?thesis unfolding contract_iter_adj_inv_def by metis
qed

lemma contract_iter_adj_inv_step2:
  assumes ciai: "contract_iter_adj_inv G H0 H u l"
  assumes iapath: "\<And>p w. \<not>pre_digraph.iapath (mk_graph G) u ((u, ig_opposite G (ig_in_out_arcs G u ! l) u) # p) w"
  shows "contract_iter_adj_inv G H0 H u (Suc l)"
proof -
  { fix v j assume *: "j < Suc l" "\<exists>p. pre_digraph.iapath (mk_graph G) u ((u, ig_opposite G (ig_in_out_arcs G u ! j) u) # p) v"
    then have "(u, v) \<in> set (ig_arcs H)"
    proof (cases "j < l")
      case True with * ciai show ?thesis
        by (auto simp: contract_iter_adj_inv_def)
    next
      case False with * have "j = l" by auto
      with * show ?thesis using iapath by metis
    qed }
  moreover
  { fix v assume *: "(u,v) \<in> set (ig_arcs H)"
    then have "(\<exists>j<Suc l. \<exists>p. pre_digraph.gen_iapath (mk_graph G) (verts3 (mk_graph G)) u ((u, ig_opposite G (ig_in_out_arcs G u ! j) u) # p) v)"
      using ciai unfolding contract_iter_adj_inv_def by (auto intro: less_SucI) }
  moreover
  have "set (ig_arcs H) - ({u} \<times> UNIV) = set (ig_arcs H0)" "ig_verts H = ig_verts H0"
    using ciai unfolding contract_iter_adj_inv_def by (auto simp:)
  ultimately
  show ?thesis unfolding contract_iter_adj_inv_def by metis
qed



definition contract_iter_adj_prop where
  "contract_iter_adj_prop G H0 H u \<equiv> ig_verts H = ig_verts H0
    \<and> set (ig_arcs H) = set (ig_arcs H0) \<union> ({u} \<times> {v. \<exists>p. pre_digraph.iapath (mk_graph G) u p v})"

lemma contract_iter_adj_propI:
  assumes nodes: "contract_iter_nodes_inv G H i"
  assumes ciai: "contract_iter_adj_inv G H H' u (length (ig_in_out_arcs G u))"
  assumes u: "u = ig_verts H ! i"
  shows "contract_iter_adj_prop G H H' u"
proof -
  have "ig_verts H' = ig_verts H"
    using ciai unfolding contract_iter_adj_inv_def by auto
  moreover
  have "set (ig_arcs H') \<subseteq> set (ig_arcs H) \<union>({u} \<times> {v. \<exists>p. pre_digraph.iapath (mk_graph G) u p v})"
    using ciai unfolding contract_iter_adj_inv_def by auto
  moreover
  { fix v p assume path: "pre_digraph.iapath (mk_graph G) u p v"
    then obtain e es where "p = e # es" by (cases p) (auto simp: pre_digraph.gen_iapath_def)
    then have "e \<in> parcs (mk_graph G)" using path
      by (auto simp: pre_digraph.gen_iapath_def pre_digraph.apath_def pre_digraph.awalk_def)
    moreover
    then obtain w where "e = (u,w)" using \<open>p = e # es\<close> path
      by (cases e) (auto simp: pre_digraph.gen_iapath_def pre_digraph.apath_def pre_digraph.awalk_def pre_digraph.cas.simps)
    ultimately
    have "(u,w) \<in> set (ig_arcs G) \<or> (w,u) \<in> set (ig_arcs G)"
      unfolding mk_graph_def by (auto simp: parcs_mk_symmetric mkg'_simps)
    then obtain e' where H1: "e' = (u,w) \<or> e' = (w,u)" and "e' \<in> set (ig_arcs G)"
      by auto
    then have "e' \<in>  set (ig_in_out_arcs G u)"
      unfolding ig_in_out_arcs_def by auto
    then obtain k where H2: "ig_in_out_arcs G u ! k = e'" "k < length (ig_in_out_arcs G u)"
      by (auto simp: in_set_conv_nth)
    have opp_e': "ig_opposite G e' u = w" using H1 unfolding ig_opposite_def by auto
    have "(u,v) \<in> set (ig_arcs H')"
      using ciai unfolding contract_iter_adj_inv_def'
      apply safe
      apply (erule allE[where x=v])
      apply safe
      apply (erule notE)
      apply (rule exI[where x=k])
      apply (simp add: H2 opp_e')
      using path \<open>e = (u,w)\<close> \<open>p = e # es\<close> by auto }
  then have "set (ig_arcs H) \<union>({u} \<times> {v. \<exists>p. pre_digraph.iapath (mk_graph G) u p v}) \<subseteq> set (ig_arcs H')"
    using ciai unfolding contract_iter_adj_inv_def by auto
  ultimately
  show ?thesis unfolding contract_iter_adj_prop_def by blast
qed

lemma contract_iter_nodes_inv_step:
  assumes nodes: "contract_iter_nodes_inv G H i"
  assumes adj: "contract_iter_adj_inv G H H' (ig_verts H ! i) (length (ig_in_out_arcs G (ig_verts H ! i)))"
  assumes snp: "select_nodes_prop G H"
  shows "contract_iter_nodes_inv G H' (Suc i)"
proof -
  have ciap: "contract_iter_adj_prop G H H' (ig_verts H ! i)"
    using nodes adj by (rule contract_iter_adj_propI) simp
  then have ie_H': "set (ig_arcs H') = set (ig_arcs H) \<union> {(u,v). u = ig_verts H' ! i \<and> (\<exists>p. pre_digraph.gen_iapath (mk_graph G) (verts3 (mk_graph G)) u p v)}"
      and [simp]: "ig_verts H' = ig_verts H"
    unfolding contract_iter_adj_prop_def by auto
  have ie_H: "set (ig_arcs H) = (\<Union> j<i. {(u, v). u = ig_verts H' ! j \<and> (\<exists>p. pre_digraph.gen_iapath (mk_graph G) (verts3 (mk_graph G)) u p v)})"
    using nodes unfolding contract_iter_nodes_inv_def by simp

  have *: "\<And>S k. (\<Union>i < Suc k. S i) = (\<Union>i < k. S i) \<union> S k"
    by (metis UN_insert lessThan_Suc sup_commute)

  show ?thesis by (simp only: contract_iter_nodes_inv_def ie_H ie_H' *)
qed

lemma contract_iter_nodes_0:
  assumes "set (ig_arcs H) = {}" shows "contract_iter_nodes_inv G H 0"
  using assms unfolding contract_iter_nodes_inv_def by simp

lemma contract_iter_adj_0:
  assumes nodes: "contract_iter_nodes_inv G H i"
  assumes i: "i < ig_verts_cnt H"
  shows "contract_iter_adj_inv G H H (ig_verts H ! i) 0"
  using assms distinct_ig_verts
  unfolding contract_iter_adj_inv_def contract_iter_nodes_inv_def
  by (auto simp: distinct_conv_nth)

lemma snp_vertexes:
  assumes "select_nodes_prop G H" "u \<in> set (ig_verts H)" shows "u \<in> set (ig_verts G)"
  using assms unfolding select_nodes_prop_def by (auto simp: verts3_def mkg_simps)

lemma igraph_ig_add_eI:
  assumes "IGraph_inv G"
  assumes "u \<in> set (ig_verts G)" "v \<in> set (ig_verts G)"
  shows "IGraph_inv (ig_add_e G u v)"
using assms unfolding IGraph_inv_def  by auto

lemma snp_iapath_ends_in:
  assumes "select_nodes_prop G H"
  assumes "pre_digraph.iapath (mk_graph G) u p v"
  shows "u \<in> set (ig_verts H)" "v \<in> set (ig_verts H)"
  using assms unfolding pre_digraph.gen_iapath_def select_nodes_prop_def verts3_def
  by (auto simp: mkg_simps)

lemma contract_iter_nodes_last:
  assumes nodes: "contract_iter_nodes_inv G H (ig_verts_cnt H)"
  assumes snp: "select_nodes_prop G H"
  assumes igraph: "IGraph_inv G"
  shows "mk_graph' H = contr_graph (mk_graph G)" (is ?t1)
    and "symmetric (mk_graph' H)" (is ?t2)
proof -
  interpret ppg_mkG: pair_pseudo_graph "mk_graph G"
    using igraph by (rule IGraph_imp_ppg_mkg)
  { fix u v p assume "pre_digraph.iapath (mk_graph G) u p v"
    then have "\<exists>p. pre_digraph.iapath (mk_graph G) v p u"
      using ppg_mkG.gen_iapath_rev_path[where u=u and v=v, symmetric] by auto }
  then have ie_sym: "\<And>u v. (\<exists>p. pre_digraph.iapath (mk_graph G) u p v) \<longleftrightarrow> (\<exists>p. pre_digraph.iapath (mk_graph G) v p u)"
    by auto

  from nodes have "set (ig_arcs H) = {(u, v). u \<in> set (ig_verts H) \<and> (\<exists>p. pre_digraph.gen_iapath (mk_graph G) (verts3 (mk_graph G)) u p v)}"
    unfolding contract_iter_nodes_inv_def by (auto simp: in_set_conv_nth)
  then have *: "set (ig_arcs H) = {(u,v).  (\<exists>p. pre_digraph.iapath (mk_graph G) u p v)}"
    using snp by (auto simp: snp_iapath_ends_in(1))
  then have **: "set (ig_arcs H) = (\<lambda>(a,b). (b,a)) ` {(u,v). (\<exists>p. pre_digraph.iapath (mk_graph G) u p v)}"
    using ie_sym by fastforce

  have sym: "symmetric (mk_graph' H)"
    unfolding symmetric_conv by (auto simp: mkg'_simps * ie_sym)

  have "pverts (mk_graph' H) = verts3 (mk_graph G)"
    using snp unfolding select_nodes_prop_def by (simp add: mkg_simps mkg'_simps)
  moreover
  have "parcs (mk_graph' H) = {(u,v). (\<exists>p. ppg_mkG.iapath u p v)}"
    using *  by (auto simp: mkg_simps mkg'_simps)
  ultimately show ?t1 ?t2
    using snp sym unfolding gen_contr_graph_def select_nodes_prop_def by auto
qed

lemma (in contract_impl) contract_spec:
  "\<forall>\<sigma>. \<Gamma> \<turnstile>\<^sub>t \<lbrace>\<sigma>. select_nodes_prop \<acute>G \<acute>H \<and> IGraph_inv \<acute>G \<and> loop_free (mk_graph \<acute>G) \<and> IGraph_inv \<acute>H \<and> set (ig_arcs \<acute>H) = {}\<rbrace>
    \<acute>R :== PROC contract(\<acute>G, \<acute>H)
  \<lbrace>\<acute>G = \<^bsup>\<sigma>\<^esup>G \<and> mk_graph' \<acute>R = contr_graph (mk_graph \<acute>G) \<and> symmetric (mk_graph' \<acute>R) \<and> IGraph_inv \<acute>R\<rbrace>"
  apply vcg_step
  apply (rewrite
    at "whileAnno _ (named_loop ''iter_nodes'') _ _"
    in for (\<sigma>)
    to "whileAnno _
      \<lbrace>contract_iter_nodes_inv \<acute>G \<acute>H \<acute>i
        \<and> select_nodes_prop \<acute>G \<acute>H \<and> \<acute>i \<le> ig_verts_cnt \<acute>H \<and> IGraph_inv \<acute>G \<and> loop_free (mk_graph \<acute>G)
        \<and> IGraph_inv \<acute>H  \<and> \<acute>G = \<^bsup>\<sigma>\<^esup>G\<rbrace>
      (MEASURE ig_verts_cnt \<acute>H - \<acute>i)
      _"
    annotate_named_loop_var)
  apply (rewrite
    at "whileAnno _ (named_loop ''iter_adj'') _ _"
    in for (\<sigma>)
    to "whileAnnoFix _
      (\<lambda>(H, u, i). \<lbrace>contract_iter_adj_inv \<acute>G H \<acute>H u \<acute>j
        \<and> select_nodes_prop \<acute>G \<acute>H \<and> \<acute>u = u \<and> \<acute>j \<le> length (ig_in_out_arcs \<acute>G \<acute>u) \<and> \<acute>io_arcs = ig_in_out_arcs \<acute>G \<acute>u
        \<and> u \<in> set (ig_verts \<acute>H)  \<and>  IGraph_inv \<acute>G  \<and> loop_free (mk_graph \<acute>G) \<and> IGraph_inv \<acute>H \<and> \<acute>G = \<^bsup>\<sigma>\<^esup>G \<and> \<acute>i = i\<rbrace>)
      (\<lambda>_. (MEASURE length \<acute>io_arcs - \<acute>j))
      _"
    annotate_named_loop_var_fix)
  apply vcg
     apply (fastforce simp: contract_iter_nodes_0)
    apply (match premises in "select_nodes_prop _ H" for H \<Rightarrow> \<open>rule exI[where x=H]\<close>)
    apply (fastforce simp: contract_iter_adj_0 contract_iter_nodes_inv_step elim: contract_iter_adj_invE)
   apply (fastforce simp: contract_iter_adj_inv_step2 contract_iter_adj_inv_step1
     IGraph_imp_ppg_mkg igraph_ig_add_eI snp_iapath_ends_in iadj_io_edge snp_vertexes)
  apply (fastforce simp: not_less intro: contract_iter_nodes_last)
  done



subsubsection \<open>Procedure @{term is_K33}\<close>

definition is_K33_colorize_inv :: "IGraph \<Rightarrow> ig_vertex \<Rightarrow> nat \<Rightarrow> (ig_vertex \<Rightarrow> bool) \<Rightarrow> bool" where
  "is_K33_colorize_inv G u k blue \<equiv> \<forall>v \<in> set (ig_verts G). blue v \<longleftrightarrow>
    (\<exists>i < k. v = ig_opposite G (ig_in_out_arcs G u ! i) u)"

definition is_K33_component_size_inv :: "IGraph \<Rightarrow> nat \<Rightarrow> (ig_vertex \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool" where
  "is_K33_component_size_inv G k blue cnt \<equiv> cnt = card {i. i < k \<and> blue (ig_verts G ! i)}"

definition is_K33_outer_inv :: "IGraph \<Rightarrow> nat \<Rightarrow> (ig_vertex \<Rightarrow> bool) \<Rightarrow> bool" where
  "is_K33_outer_inv G k blue \<equiv> \<forall>i < k. \<forall>v \<in> set (ig_verts G).
    blue (ig_verts G ! i) = blue v \<longleftrightarrow> (ig_verts G ! i, v) \<notin> set (ig_arcs G)"

definition is_K33_inner_inv :: "IGraph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (ig_vertex \<Rightarrow> bool) \<Rightarrow> bool" where
  "is_K33_inner_inv G k l blue \<equiv> \<forall>j < l.
    blue (ig_verts G ! k) = blue (ig_verts G ! j) \<longleftrightarrow> (ig_verts G ! k, ig_verts G ! j) \<notin> set (ig_arcs G)"

lemma is_K33_colorize_0: "is_K33_colorize_inv G u 0 (\<lambda>_. False)"
  unfolding is_K33_colorize_inv_def by auto

lemma is_K33_component_size_0: "is_K33_component_size_inv G 0 blue 0"
  unfolding is_K33_component_size_inv_def by auto

lemma is_K33_outer_0: "is_K33_outer_inv G 0 blue"
  unfolding is_K33_outer_inv_def by auto

lemma is_K33_inner_0: "is_K33_inner_inv G k 0 blue"
  unfolding is_K33_inner_inv_def by auto

lemma is_K33_colorize_last:
  assumes "u \<in> set (ig_verts G)"
  shows "is_K33_colorize_inv G u (length (ig_in_out_arcs G u)) blue
    = (\<forall>v \<in> set (ig_verts G). blue v \<longleftrightarrow> iadj G u v)" (is "?L = ?R")
proof -
  { fix v
    have "(\<exists>i<length (ig_in_out_arcs G u). v = ig_opposite G (ig_in_out_arcs G u ! i) u)
        \<longleftrightarrow> (\<exists>e \<in> set (ig_in_out_arcs G u). v = ig_opposite G e u)" (is "?A \<longleftrightarrow> _")
      by auto (auto simp: in_set_conv_nth)
    also have "\<dots> \<longleftrightarrow> iadj G u v"
      using assms by (force simp: iadj_io_edge ig_opposite_simps dest: iadjD)
    finally have "?A \<longleftrightarrow> iadj G u v" . }
  then show ?thesis unfolding is_K33_colorize_inv_def by auto
qed

lemma is_K33_component_size_last:
  assumes "k = ig_verts_cnt G"
  shows "is_K33_component_size_inv G k blue cnt \<longleftrightarrow> card {u \<in> set (ig_verts G). blue u} = cnt"
proof -
  have *: "{u \<in> set (ig_verts G). blue u} = (\<lambda>n. ig_verts G ! n) ` {i. i < ig_verts_cnt G \<and> blue (ig_verts G ! i)}"
    by (auto simp: in_set_conv_nth )
  have "inj_on (\<lambda>n. ig_verts G ! n) {i. i < ig_verts_cnt G \<and> blue (ig_verts G ! i)}"
    using distinct_ig_verts by (auto simp: nth_eq_iff_index_eq intro: inj_onI)
  with assms show ?thesis
    unfolding * is_K33_component_size_inv_def
    by (auto intro: card_image)
qed

lemma is_K33_outer_last:
  "is_K33_outer_inv G (ig_verts_cnt G) blue \<longleftrightarrow> (\<forall>u \<in> set (ig_verts G). \<forall>v \<in> set (ig_verts G).
    blue u = blue v \<longleftrightarrow> (u,v) \<notin> set (ig_arcs G))"
  unfolding is_K33_outer_inv_def by (simp add: All_set_ig_verts)

lemma is_K33_inner_last:
  "is_K33_inner_inv G k (ig_verts_cnt G) blue \<longleftrightarrow> (\<forall>v \<in> set (ig_verts G).
    blue (ig_verts G ! k) = blue v \<longleftrightarrow> (ig_verts G ! k, v) \<notin> set (ig_arcs G))"
  unfolding is_K33_inner_inv_def by (simp add: All_set_ig_verts)

lemma is_K33_colorize_step:
  fixes G u i blue
  assumes colorize: "is_K33_colorize_inv G u k blue"
  shows " is_K33_colorize_inv G u (Suc k) (blue (ig_opposite G (ig_in_out_arcs G u ! k) u := True))"
  using assms by (auto simp: is_K33_colorize_inv_def elim: less_SucE intro: less_SucI)

lemma is_K33_component_size_step1:
  assumes comp:"is_K33_component_size_inv G k blue blue_cnt"
  assumes blue: "blue (ig_verts G ! k)"
  shows "is_K33_component_size_inv G (Suc k) blue (Suc blue_cnt)"
proof -
  have "{i. i < Suc k \<and> blue (ig_verts G ! i)}
      = insert k {i. i < k \<and> blue (ig_verts G ! i)}"
    using blue by auto
  with comp show ?thesis
    unfolding is_K33_component_size_inv_def by auto
qed

lemma is_K33_component_size_step2:
  assumes comp:"is_K33_component_size_inv G k blue blue_cnt"
  assumes blue: "\<not>blue (ig_verts G ! k)"
  shows "is_K33_component_size_inv G (Suc k) blue blue_cnt"
proof -
  have "{i. i < Suc k \<and> blue (ig_verts G ! i)} = {i. i < k \<and> blue (ig_verts G ! i)}"
    using blue by (auto elim: less_SucE)
  with comp show ?thesis
    unfolding is_K33_component_size_inv_def by auto
qed

lemma is_K33_outer_step:
  assumes "is_K33_outer_inv G i blue"
  assumes "is_K33_inner_inv G i (ig_verts_cnt G) blue"
  shows "is_K33_outer_inv G (Suc i) blue"
  using assms unfolding is_K33_outer_inv_def is_K33_inner_last
  by (auto intro: less_SucI elim: less_SucE)

lemma is_K33_inner_step:
  assumes "is_K33_inner_inv G i j blue"
  assumes "(blue (ig_verts G ! i) = blue (ig_verts G ! j)) \<longleftrightarrow> (ig_verts G ! i, ig_verts G ! j) \<notin> set (ig_arcs G)"
  shows "is_K33_inner_inv G i (Suc j) blue"
  using assms by (auto simp: is_K33_inner_inv_def elim: less_SucE)

lemma K33_mkg'I:
  fixes G col cnt
  defines "u \<equiv> ig_verts G ! 0"
  assumes ig: "IGraph_inv G"
  assumes iv_cnt: "ig_verts_cnt G = 6" and c1_cnt: "cnt = 3"
  assumes colorize: "is_K33_colorize_inv G u (length (ig_in_out_arcs G u)) blue"
  assumes comp: "is_K33_component_size_inv G (ig_verts_cnt G) blue cnt"
  assumes outer: "is_K33_outer_inv G (ig_verts_cnt G) blue"
  shows "K\<^bsub>3,3\<^esub> (mk_graph' G)"
proof -
  have "u \<in> set (ig_verts G)" unfolding u_def using iv_cnt by auto
  then have "(\<forall>v\<in>set (ig_verts G). blue v \<longleftrightarrow> iadj G u v)"
    using colorize by (rule is_K33_colorize_last[THEN iffD1])

  define U V where "U = {u \<in> set (ig_verts G). \<not>blue u}" and "V = {v \<in> set (ig_verts G). blue v}"
  then have UV_set: "U \<subseteq> set (ig_verts G)" "V \<subseteq> set (ig_verts G)" "U \<union> V = set (ig_verts G)" "U \<inter> V = {}"
    and fin_UV: "finite U" "finite V" by auto

  have card_verts: "card (set (ig_verts G)) = 6"
    using iv_cnt distinct_ig_verts by (simp add: distinct_card)

  from ig comp c1_cnt have "card V = 3" by (simp add: is_K33_component_size_last V_def)
  moreover have "card (U \<union> V) = 6" using UV_set distinct_ig_verts iv_cnt
    by (auto simp: distinct_card)
  ultimately have "card U = 3"
    by (simp add: card_Un_disjoint[OF fin_UV UV_set(4)])
  note cards = \<open>card V = 3\<close> \<open>card U = 3\<close> card_verts

  from is_K33_outer_last[THEN iffD1, OF outer]
  have "(\<forall>u\<in>U. \<forall>v\<in>V. (u, v) \<in> set (ig_arcs G) \<and> (v, u) \<in> set (ig_arcs G))
      \<and> (\<forall>u\<in>U. \<forall>u'\<in>U. (u, u') \<notin> set (ig_arcs G))
      \<and> (\<forall>v\<in>V. \<forall>v'\<in>V. (v, v') \<notin> set (ig_arcs G))"
    unfolding U_def V_def by auto
  then have "U \<times> V \<subseteq> set (ig_arcs G)" "V \<times> U \<subseteq> set (ig_arcs G)"
    "U \<times> U \<inter> set (ig_arcs G) = {}" "V \<times> V \<inter> set (ig_arcs G) = {}"
    by auto
  moreover have "set (ig_arcs G) \<subseteq> (U \<union> V) \<times> (U \<union> V)"
    unfolding \<open>U \<union> V = _\<close> by (auto simp: ig set_ig_arcs_verts)
  ultimately
  have conn: "set (ig_arcs G) = U \<times> V \<union> V \<times> U"
    by blast

  interpret ppg_mkg': pair_fin_digraph "mk_graph' G"
    using ig by (auto intro: IGraph_imp_ppd_mkg')

  show ?thesis
    unfolding complete_bipartite_digraph_pair_def mkg'_simps
    using cards UV_set conn by simp metis
qed

lemma K33_mkg'E:
  assumes K33: "K\<^bsub>3,3\<^esub> (mk_graph' G)"
  assumes ig: "IGraph_inv G"
  assumes colorize: "is_K33_colorize_inv G u (length (ig_in_out_arcs G u)) blue"
  and u: "u \<in> set (ig_verts G)"
  obtains "is_K33_component_size_inv G (ig_verts_cnt G) blue 3"
    "is_K33_outer_inv G (ig_verts_cnt G) blue"
proof -
  from K33 obtain U V where
      verts_G: "set (ig_verts G) = U \<union> V" and
      arcs_G: "set (ig_arcs G) = U \<times> V \<union> V \<times> U" and
      disj_UV: "U \<inter> V = {}"  and
      card: "card U = 3" "card V = 3"
    unfolding complete_bipartite_digraph_pair_def mkg'_simps by auto

  from colorize u have col_adj: "\<And>v. v \<in> set (ig_verts G) \<Longrightarrow> blue v \<longleftrightarrow> iadj G u v"
    using is_K33_colorize_last by auto

  have iadj_conv: "\<And>u v. iadj G u v \<longleftrightarrow> (u,v) \<in> U \<times> V \<union> V \<times> U"
    unfolding iadj_def arcs_G by auto

  { assume "u \<in> U"
    then have "V = {v \<in> set (ig_verts G). blue v}"
      using disj_UV by (auto simp: iadj_conv verts_G col_adj)
    then have "is_K33_component_size_inv G (ig_verts_cnt G) blue 3"
      using ig card by (simp add: is_K33_component_size_last)
    moreover
    have "\<And>v. v \<in> U \<union> V \<Longrightarrow> blue v \<longleftrightarrow> v \<in> V"
      using \<open>u \<in> U\<close> disj_UV by (auto simp: verts_G col_adj iadj_conv)
    then have "is_K33_outer_inv G (ig_verts_cnt G) blue"
      using \<open>U \<inter> V = {}\<close> by (subst is_K33_outer_last) (auto simp: arcs_G verts_G )
    ultimately have ?thesis by (rule that) }
  moreover
  { assume "u \<in> V"
    then have "U = {v \<in> set (ig_verts G). blue v}"
      using disj_UV by (auto simp: iadj_conv verts_G col_adj)
    then have "is_K33_component_size_inv G (ig_verts_cnt G) blue 3"
      using ig card by (simp add: is_K33_component_size_last)
    moreover
    have "\<And>v. v \<in> U \<union> V \<Longrightarrow> blue v \<longleftrightarrow> v \<in> U"
      using \<open>u \<in> V\<close> disj_UV by (auto simp: verts_G col_adj iadj_conv)
    then have "is_K33_outer_inv G (ig_verts_cnt G) blue"
      using \<open>U \<inter> V = {}\<close> by (subst is_K33_outer_last) (auto simp: arcs_G verts_G )
    ultimately have ?thesis by (rule that) }
  ultimately show ?thesis using verts_G u by blast
qed

lemma K33_card:
  assumes "K\<^bsub>3,3\<^esub> (mk_graph' G)" shows "ig_verts_cnt G = 6"
proof -
  from assms have "card (verts (mk_graph' G)) = 6"
    unfolding complete_bipartite_digraph_pair_def by (auto simp: card_Un_disjoint)
  then show ?thesis
    using distinct_ig_verts by (auto simp: mkg'_simps distinct_card)
qed

abbreviation (input) is_K33_colorize_inv_last :: "IGraph \<Rightarrow> (ig_vertex \<Rightarrow> bool) \<Rightarrow> bool" where
  "is_K33_colorize_inv_last G blue \<equiv> is_K33_colorize_inv G (ig_verts G ! 0) (length (ig_in_out_arcs G (ig_verts G ! 0))) blue"

abbreviation (input) is_K33_component_size_inv_last :: "IGraph \<Rightarrow> (ig_vertex \<Rightarrow> bool) \<Rightarrow> bool" where
  "is_K33_component_size_inv_last G blue \<equiv> is_K33_component_size_inv G (ig_verts_cnt G) blue 3"

lemma is_K33_outerD:
  assumes "is_K33_outer_inv G (ig_verts_cnt G) blue"
  assumes "i < ig_verts_cnt G" "j < ig_verts_cnt G"
  shows "(blue (ig_verts G ! i) = blue (ig_verts G ! j)) \<longleftrightarrow> (ig_verts G ! i, ig_verts G ! j) \<notin> set (ig_arcs G)"
  using assms unfolding is_K33_outer_last by auto

lemma (in is_K33_impl) is_K33_spec:
  "\<forall>\<sigma>. \<Gamma> \<turnstile>\<^sub>t \<lbrace>\<sigma>. IGraph_inv \<acute>G \<and> symmetric (mk_graph' \<acute>G)\<rbrace>
    \<acute>R :== PROC is_K33(\<acute>G)
  \<lbrace> \<acute>G = \<^bsup>\<sigma>\<^esup>G \<and> \<acute>R = K\<^bsub>3,3\<^esub>(mk_graph' \<acute>G) \<rbrace>"
  apply vcg_step
  apply (rewrite
    at "whileAnno _ (named_loop ''colorize'') _ _"
    in for (\<sigma>)
    to "whileAnno _
      \<lbrace> is_K33_colorize_inv \<acute>G \<acute>u \<acute>i \<acute>blue \<and> \<acute>i \<le> length \<acute>io_arcs
        \<and> \<acute>io_arcs = ig_in_out_arcs \<acute>G \<acute>u \<and> \<acute>u = ig_verts \<acute>G ! 0 \<and> \<acute>G = \<^bsup>\<sigma>\<^esup>G \<and> IGraph_inv \<acute>G
        \<and> \<acute>u = ig_verts \<acute>G ! 0 \<and> ig_verts_cnt \<acute>G = 6\<rbrace>
      (MEASURE length \<acute>io_arcs - \<acute>i)
      _"
    annotate_named_loop_var)
  apply (rewrite
    at "whileAnno _ (named_loop ''component_size'') _ _"
    in for (\<sigma>)
    to "whileAnnoFix _
      (\<lambda>blue. \<lbrace> is_K33_component_size_inv \<acute>G \<acute>i \<acute>blue \<acute>blue_cnt
      \<and> \<acute>i \<le> ig_verts_cnt \<acute>G \<and> \<acute>blue = blue \<and> \<acute>G = \<^bsup>\<sigma>\<^esup>G \<and> IGraph_inv \<acute>G
      \<and> ig_verts_cnt \<acute>G = 6 \<and> is_K33_colorize_inv_last \<acute>G \<acute>blue \<rbrace>)
      (\<lambda>_. (MEASURE ig_verts_cnt \<acute>G - \<acute>i))
      _"
    annotate_named_loop_var_fix)
  apply (rewrite
    at "whileAnno _ (named_loop ''connected_outer'') _ _"
    in for (\<sigma>)
    to "whileAnnoFix _
      (\<lambda>blue. \<lbrace> is_K33_outer_inv \<acute>G \<acute>i \<acute>blue \<and> \<acute>i \<le> ig_verts_cnt \<acute>G
        \<and> \<acute>blue = blue \<and> \<acute>G = \<^bsup>\<sigma>\<^esup>G \<and> IGraph_inv \<acute>G
        \<and> ig_verts_cnt \<acute>G = 6 \<and> is_K33_colorize_inv_last \<acute>G \<acute>blue \<and> is_K33_component_size_inv_last \<acute>G \<acute>blue \<rbrace>)
      (\<lambda>_. (MEASURE ig_verts_cnt \<acute>G - \<acute>i))
      _"
    annotate_named_loop_var_fix)
  apply (rewrite
    at "whileAnno _ (named_loop ''connected_inner'') _ _"
    in for (\<sigma>)
    to "whileAnnoFix _
      (\<lambda>(i,blue). \<lbrace> is_K33_inner_inv \<acute>G \<acute>i \<acute>j \<acute>blue \<and> \<acute>j \<le> ig_verts_cnt \<acute>G
        \<and> \<acute>i = i \<and>\<acute>i < ig_verts_cnt \<acute>G \<and> \<acute>blue = blue \<and> \<acute>G = \<^bsup>\<sigma>\<^esup>G \<and> IGraph_inv \<acute>G \<and> \<acute>u = ig_verts \<acute>G ! \<acute>i
        \<and> ig_verts_cnt \<acute>G = 6 \<and> is_K33_colorize_inv_last \<acute>G \<acute>blue \<and> is_K33_component_size_inv_last \<acute>G \<acute>blue \<rbrace>)
      (\<lambda>_. (MEASURE ig_verts_cnt \<acute>G - \<acute>j))
      _"
    annotate_named_loop_var_fix)
  apply vcg
       apply (fastforce simp: is_K33_colorize_0 is_K33_component_size_0 is_K33_outer_0 is_K33_component_size_last
         elim: K33_mkg'E dest: K33_card intro: K33_mkg'I)
      apply (fastforce simp add: is_K33_colorize_step)
     apply (fastforce simp: is_K33_colorize_0 is_K33_component_size_0 is_K33_outer_0 is_K33_component_size_last
       elim: K33_mkg'E  intro: K33_mkg'I)
    apply (fastforce simp: is_K33_component_size_step1 is_K33_component_size_step2)
   apply (fastforce simp: is_K33_inner_0 is_K33_outer_step)
  apply (simp only: simp_thms)
  apply (intro conjI allI impI notI)
     apply (fastforce elim: K33_mkg'E dest: is_K33_outerD)
    apply (fastforce elim: K33_mkg'E dest: is_K33_outerD)
   apply (simp add: is_K33_inner_step; fail)
  apply linarith
  done


subsubsection \<open>Procedure @{term is_K5}\<close>

definition
  "is_K5_outer_inv G k \<equiv> \<forall>i<k. \<forall>v \<in> set (ig_verts G). ig_verts G ! i \<noteq> v
    \<longleftrightarrow> (ig_verts G ! i, v) \<in> set (ig_arcs G)"

definition
  "is_K5_inner_inv G k l \<equiv> \<forall>j < l. ig_verts G ! k \<noteq> ig_verts G ! j
    \<longleftrightarrow> (ig_verts G ! k, ig_verts G ! j) \<in> set (ig_arcs G)"

lemma K5_card:
  assumes "K\<^bsub>5\<^esub> (mk_graph' G)" shows "ig_verts_cnt G = 5"
  using assms distinct_ig_verts unfolding complete_digraph_pair_def
  by (auto simp add: mkg'_simps distinct_card)

lemma is_K5_inner_0: "is_K5_inner_inv G k 0"
  unfolding is_K5_inner_inv_def by auto

lemma is_K5_inner_last:
  assumes "l = ig_verts_cnt G"
  shows "is_K5_inner_inv G k l \<longleftrightarrow> (\<forall>v \<in> set (ig_verts G). ig_verts G ! k \<noteq> v
    \<longleftrightarrow> (ig_verts G ! k, v) \<in> set (ig_arcs G))"
proof -
  have "\<And>v. v \<in> set (ig_verts G) \<Longrightarrow> \<exists>j<ig_verts_cnt G. ig_verts G ! j = v"
    by (auto simp: in_set_conv_nth)
  then show ?thesis using assms unfolding is_K5_inner_inv_def
    by auto metis
qed

lemma is_K5_outer_step:
  assumes "is_K5_outer_inv G k"
  assumes "is_K5_inner_inv G k (ig_verts_cnt G)"
  shows "is_K5_outer_inv G (Suc k)"
  using assms unfolding is_K5_outer_inv_def
  by (auto simp: is_K5_inner_last elim: less_SucE)

lemma is_K5_outer_last:
  assumes "is_K5_outer_inv G (ig_verts_cnt G)"
  assumes "IGraph_inv G" "ig_verts_cnt G = 5" "symmetric (mk_graph' G)"
  shows "K\<^bsub>5\<^esub> (mk_graph' G)"
proof -
  interpret ppg_mkg': pair_fin_digraph "mk_graph' G"
    using assms(2) by (auto intro: IGraph_imp_ppd_mkg')
  have "\<And>u v. (u, v) \<in> set (ig_arcs G) \<Longrightarrow> u \<noteq> v"
    using assms(1,2) unfolding is_K5_outer_inv_def ig_verts_cnt_def
    by (metis  in_set_conv_nth set_ig_arcs_verts(2))
  then interpret ppg_mkg': pair_graph "(mk_graph' G)"
    using assms(4) by unfold_locales (auto simp: mkg'_simps arc_to_ends_def)
  have "\<And>a b. a \<in> pverts (mk_graph' G) \<Longrightarrow>
           b \<in> pverts (mk_graph' G) \<Longrightarrow> a \<noteq> b \<Longrightarrow> (a, b) \<in> parcs (mk_graph' G)"
    using assms(1) unfolding is_K5_outer_inv_def mkg'_simps
    by (metis in_set_conv_nth ig_verts_cnt_def)
  moreover
  have "card (pverts (mk_graph' G)) = 5"
    using \<open>ig_verts_cnt G = 5\<close> distinct_ig_verts by (auto simp: mkg'_simps distinct_card)
  ultimately
  show ?thesis
    unfolding complete_digraph_pair_def
    by (auto dest: ppg_mkg'.in_arcsD1 ppg_mkg'.in_arcsD2 ppg_mkg'.no_loops')
qed


lemma is_K5_inner_step:
  assumes "is_K5_inner_inv G k l"
  assumes "k < ig_verts_cnt G"
  assumes "k \<noteq> l \<longleftrightarrow> (ig_verts G ! k, ig_verts G ! l) \<in> set (ig_arcs G)"
  shows "is_K5_inner_inv G k (Suc l)"
  using assms distinct_ig_verts unfolding is_K5_inner_inv_def
  apply (auto elim: less_SucE)
  by (metis (hide_lams, no_types) Suc_lessD less_SucE less_trans_Suc linorder_neqE_nat nth_eq_iff_index_eq)

lemma iK5E:
  assumes "K\<^bsub>5\<^esub> (mk_graph' G)"
  obtains "ig_verts_cnt G = 5" "\<lbrakk>i < ig_verts_cnt G; j < ig_verts_cnt G\<rbrakk> \<Longrightarrow> i \<noteq> j \<longleftrightarrow> (ig_verts G ! i, ig_verts G ! j) \<in> set (ig_arcs G)"
proof
  show "ig_verts_cnt G = 5"
      "i < ig_verts_cnt G \<Longrightarrow> j < ig_verts_cnt G \<Longrightarrow>
        (i \<noteq> j) = ((ig_verts G ! i, ig_verts G ! j) \<in> set (ig_arcs G))"
    using assms distinct_ig_verts
    by (auto simp: complete_digraph_pair_def mkg'_simps distinct_card nth_eq_iff_index_eq)
qed

lemma (in is_K5_impl) is_K5_spec:
  "\<forall>\<sigma>. \<Gamma> \<turnstile>\<^sub>t \<lbrace>\<sigma>. IGraph_inv \<acute>G \<and> symmetric (mk_graph' \<acute>G)\<rbrace>
    \<acute>R :== PROC is_K5(\<acute>G)
  \<lbrace> \<acute>G = \<^bsup>\<sigma>\<^esup>G \<and> \<acute>R = K\<^bsub>5\<^esub>(mk_graph' \<acute>G) \<rbrace>"
  apply vcg_step
  apply (rewrite
    at "whileAnno _ (named_loop ''outer_loop'') _ _"
    in for (\<sigma>)
    to "whileAnno _
      \<lbrace> is_K5_outer_inv \<acute>G \<acute>i \<and>\<acute>i \<le> 5 \<and> IGraph_inv \<acute>G \<and> symmetric (mk_graph' \<acute>G) \<and> \<acute>G = \<^bsup>\<sigma>\<^esup>G \<and> ig_verts_cnt \<acute>G = 5 \<rbrace>
      (MEASURE 5 - \<acute>i)
      _"
    annotate_named_loop_var)
  apply (rewrite
    at "whileAnno _ (named_loop ''inner_loop'') _ _"
    in for (\<sigma>)
    to "whileAnnoFix _
      (\<lambda>i. \<lbrace> is_K5_inner_inv \<acute>G \<acute>i \<acute>j
        \<and> \<acute>j \<le> 5 \<and> \<acute>i < 5 \<and> IGraph_inv \<acute>G \<and> symmetric (mk_graph' \<acute>G) \<and> \<acute>G = \<^bsup>\<sigma>\<^esup>G \<and> \<acute>i = i
        \<and> ig_verts_cnt \<acute>G = 5 \<and> \<acute>u = ig_verts \<acute>G ! \<acute>i\<rbrace>)
      (\<lambda>_. (MEASURE 5 - \<acute>j))
      _"
    annotate_named_loop_var_fix)
  apply vcg
     apply (fastforce simp: is_K5_outer_inv_def intro: K5_card)
    apply (fastforce simp add: is_K5_inner_0 is_K5_outer_step)
   apply (fastforce simp: is_K5_inner_step elim: iK5E)
  apply (fastforce simp: is_K5_outer_last)
  done



subsubsection \<open>Soundness of the Checker\<close>

lemma planar_theorem:
  assumes "pair_pseudo_graph G" "pair_pseudo_graph K"
  and "subgraph K G"
  and "K\<^bsub>3,3\<^esub> (contr_graph K) \<or> K\<^bsub>5\<^esub> (contr_graph K)"
  shows "\<not>kuratowski_planar G"
  using assms
  by (auto dest: pair_pseudo_graph.kuratowski_contr)

definition witness :: "'a pair_pre_digraph \<Rightarrow> 'a pair_pre_digraph \<Rightarrow> bool" where
  "witness G K \<equiv> loop_free K \<and> pair_pseudo_graph K \<and> subgraph K G
    \<and> (K\<^bsub>3,3\<^esub> (contr_graph K) \<or> K\<^bsub>5\<^esub> (contr_graph K))"

lemma "witness (mk_graph G) (mk_graph K) \<longleftrightarrow> pair_pre_digraph.certify (mk_graph G) (mk_graph K) \<and> loop_free (mk_graph K)"
  by (auto simp: witness_def pair_pre_digraph.certify_def Let_def wf_digraph_wp_iff wellformed_pseudo_graph_mkg)


lemma pwd_imp_ppg_mkg:
  assumes "pair_wf_digraph (mk_graph G)"
  shows "pair_pseudo_graph (mk_graph G)"
proof -
  interpret pair_wf_digraph "mk_graph G" by fact
  show ?thesis
    apply unfold_locales
      apply (auto simp: mkg_simps finite_symcl_iff)
    apply (auto simp: mk_graph_def symmetric_mk_symmetric)
    done
qed

theorem (in check_kuratowski_impl) check_kuratowski_spec:
  "\<forall>\<sigma>. \<Gamma> \<turnstile>\<^sub>t \<lbrace>\<sigma>. pair_wf_digraph (mk_graph \<acute>G)\<rbrace>
    \<acute>R :== PROC check_kuratowski(\<acute>G, \<acute>K)
  \<lbrace> \<acute>G = \<^bsup>\<sigma>\<^esup>G \<and> \<acute>K = \<^bsup>\<sigma>\<^esup>K \<and> \<acute>R \<longleftrightarrow> witness (mk_graph \<acute>G) (mk_graph \<acute>K)\<rbrace>"
  by vcg (auto simp: witness_def IGraph_inv_conv' pwd_imp_ppg_mkg)

lemma check_kuratowski_correct:
  assumes "pair_pseudo_graph G"
  assumes "witness G K"
  shows "\<not>kuratowski_planar G"
  using assms
  by (intro planar_theorem[where K=K]) (auto simp: witness_def)

lemma check_kuratowski_correct_comb:
  assumes "pair_pseudo_graph G"
  assumes "witness G K"
  shows "\<not>comb_planar G"
  using assms by (metis check_kuratowski_correct comb_planar_compat)

lemma check_kuratowski_complete:
  assumes "pair_pseudo_graph G" "pair_pseudo_graph K" "loop_free K"
  assumes "subgraph K G"
  assumes "subdivision_pair H K" "K\<^bsub>3,3\<^esub> H \<or> K\<^bsub>5\<^esub> H"
  shows "witness G K"
  using assms by (auto simp: witness_def intro: K33_contractedI K5_contractedI)

end
