theory Planar_Complete
imports
  Digraph_Map_Impl
begin

section \<open>Kuratowski Graphs are not Combinatorially Planar\<close>

subsection \<open>A concrete K5 graph\<close>

definition "c_K5_list \<equiv> ([0..4], [(x,y). x <- [0..4], y <- [0..4], x \<noteq> y])"

abbreviation c_K5 :: "int pair_pre_digraph" where
  "c_K5 \<equiv> list_digraph c_K5_list"

lemma c_K5_not_comb_planar: "\<not>comb_planar c_K5"
  by (subst comb_planar_impl_correct) eval+

lemma pverts_c_K5: "pverts c_K5 = {0..4}"
  by (simp add: c_K5_list_def list_digraph_ext_def)

lemma parcs_c_K5: "parcs c_K5 = {(u,v). u \<in> {0..4} \<and> v \<in> {0..4} \<and> u \<noteq> v}"
  by (auto simp: c_K5_list_def list_digraph_ext_def)

lemmas c_K5_simps = pverts_c_K5 parcs_c_K5

lemma complete_c_K5: "K\<^bsub>5\<^esub> c_K5"
proof -
  interpret K5: pair_graph c_K5 by eval
  show ?thesis unfolding complete_digraph_def by (auto simp: c_K5_simps)
qed


subsection \<open>A concrete K33 graph\<close>

definition "c_K33_list \<equiv> ([0..5], [(x,y). x <- [0..5], y <- [0..5], even x \<longleftrightarrow> odd y])"

abbreviation c_K33 :: "int pair_pre_digraph" where
  "c_K33 \<equiv> list_digraph c_K33_list"

lemma c_K33_not_comb_planar: "\<not>comb_planar c_K33"
  by (subst comb_planar_impl_correct) eval+

lemma complete_c_K33: "K\<^bsub>3,3\<^esub> c_K33"
proof -
  interpret K33: pair_graph c_K33 by eval
  show ?thesis
    unfolding complete_bipartite_digraph_def
    apply (intro conjI)
    apply unfold_locales
    apply (rule exI[of _ "{0,2,4}"])
    apply (rule exI[of _ "{1,3,5}"])
    unfolding c_K33_list_def list_digraph_simps with_proj_simps
    apply eval
    done
qed



subsection \<open>Generalization to arbitrary Kuratowski Graphs\<close>

subsubsection \<open>Number of Face Cycles is a Graph Invariant\<close>

lemma (in digraph_map) wrap_wrap_iso:
  assumes hom: "digraph_isomorphism hom"
  assumes f: "f \<in> arcs G \<rightarrow> arcs G" and g: "g \<in> arcs G \<rightarrow> arcs G"
  shows "wrap_iso_arcs hom f (wrap_iso_arcs hom g x) = wrap_iso_arcs hom (f o g) x"
proof -
  have "\<And>x. x \<in> arcs G \<Longrightarrow> g x \<in> arcs G" using g by auto
  with hom f show ?thesis
    by (cases "x \<in> iso_arcs hom ` arcs G") (auto simp: wrap_iso_arcs_def perm_restrict_simps)
qed

lemma (in digraph_map) face_cycle_succ_iso:
  assumes hom: "digraph_isomorphism hom" "x \<in> iso_arcs hom ` arcs G"
  shows "pre_digraph_map.face_cycle_succ (map_iso hom) x = wrap_iso_arcs hom face_cycle_succ x"
  using assms by (simp add: pre_digraph_map.face_cycle_succ_def map_iso_def wrap_wrap_iso)

lemma (in digraph_map) face_cycle_set_iso:
  assumes hom: "digraph_isomorphism hom" "x \<in> iso_arcs hom ` arcs G"
  shows "pre_digraph_map.face_cycle_set (map_iso hom) x = iso_arcs hom ` face_cycle_set (iso_arcs (inv_iso hom) x)"
proof -
  have *: "\<And>x y. x \<in> orbit face_cycle_succ y \<Longrightarrow> y \<in> arcs G \<Longrightarrow> x \<in> arcs G"
          "\<And>x. x \<in> arcs G \<Longrightarrow> x \<in> orbit face_cycle_succ x"
    using face_cycle_set_def by (auto simp: in_face_cycle_setD)
  show ?thesis
    using assms unfolding pre_digraph_map.face_cycle_set_def
    by (subst orbit_FOO[where g'="pre_digraph_map.face_cycle_succ (map_iso hom)"])
       (auto simp: * face_cycle_succ_iso)
qed

lemma (in digraph_map) face_cycle_sets_iso:
  assumes hom: "digraph_isomorphism hom"
  shows "pre_digraph_map.face_cycle_sets (app_iso hom G) (map_iso hom) = (\<lambda>x. iso_arcs hom ` x) ` face_cycle_sets" 
  using assms by (auto simp: pre_digraph_map.face_cycle_sets_def face_cycle_set_iso) (auto simp: face_cycle_set_iso intro: rev_image_eqI)

lemma (in digraph_map) card_face_cycle_sets_iso:
  assumes hom: "digraph_isomorphism hom"
  shows "card (pre_digraph_map.face_cycle_sets (app_iso hom G) (map_iso hom)) = card face_cycle_sets"
proof -
  have "inj_on ((`) (iso_arcs hom)) face_cycle_sets"
    by (rule inj_on_f_imageI digraph_isomorphism_inj_on_arcs hom in_face_cycle_setsD)+
  then show ?thesis using hom by (simp add: face_cycle_sets_iso card_image)
qed



subsubsection \<open>Combinatorial planarity is a Graph Invariant\<close>

lemma (in digraph_map) euler_char_iso:
  assumes "digraph_isomorphism hom"
  shows "pre_digraph_map.euler_char (app_iso hom G) (map_iso hom) = euler_char"
  using assms by (auto simp: pre_digraph_map.euler_char_def card_face_cycle_sets_iso)

lemma (in digraph_map) euler_genus_iso:
  assumes "digraph_isomorphism hom"
  shows "pre_digraph_map.euler_genus (app_iso hom G) (map_iso hom) = euler_genus"
  using assms by (auto simp: pre_digraph_map.euler_genus_def euler_char_iso)

lemma (in wf_digraph) comb_planar_iso:
  assumes "digraph_isomorphism hom"
  shows "comb_planar (app_iso hom G) \<longleftrightarrow> comb_planar G"
proof
  assume "comb_planar G"
  then obtain M where "digraph_map G M" "pre_digraph_map.euler_genus G M = 0"
    by (auto simp: comb_planar_def)
  then have "digraph_map (app_iso hom G) (pre_digraph_map.map_iso G M hom)"
      "pre_digraph_map.euler_genus (app_iso hom G) (pre_digraph_map.map_iso G M hom) = 0"
    using assms by (auto intro: digraph_map.digraph_map_isoI simp: digraph_map.euler_genus_iso)
  then show "comb_planar (app_iso hom G)"
    by (metis comb_planar_def)
next
  let ?G = "app_iso hom G"
  assume "comb_planar ?G"
  then obtain M where "digraph_map ?G M"
      "pre_digraph_map.euler_genus ?G M = 0"
    by (auto simp: comb_planar_def)
  moreover
  have "pre_digraph.digraph_isomorphism ?G (inv_iso hom)"
    using assms by (rule digraph_isomorphism_invI)
  ultimately
  have "digraph_map (app_iso (inv_iso hom) ?G) (pre_digraph_map.map_iso ?G M (inv_iso hom))"
      "pre_digraph_map.euler_genus (app_iso (inv_iso hom) ?G) (pre_digraph_map.map_iso ?G M (inv_iso hom)) = 0"
    using assms by (auto intro: digraph_map.digraph_map_isoI simp only: digraph_map.euler_genus_iso)
  then show "comb_planar G"
    using assms by (auto simp: comb_planar_def)
qed


subsubsection \<open>Completeness is a Graph Invariant\<close>

lemma (in loopfree_digraph) loopfree_digraphI_app_iso:
  assumes "digraph_isomorphism hom"
  shows "loopfree_digraph (app_iso hom G)"
proof -
  interpret iG: wf_digraph "app_iso hom G" using assms by (rule wf_digraphI_app_iso)
  show ?thesis
    using assms digraph_isomorphism_inj_on_verts[OF assms]
    by unfold_locales (auto simp: iso_verts_tail iso_verts_head dest: inj_onD no_loops)
qed

lemma (in nomulti_digraph) nomulti_digraphI_app_iso:
  assumes "digraph_isomorphism hom"
  shows "nomulti_digraph (app_iso hom G)"
proof -
  interpret iG: wf_digraph "app_iso hom G" using assms by (rule wf_digraphI_app_iso)
  show ?thesis
    using assms 
    by unfold_locales (auto simp: iso_verts_tail iso_verts_head arc_to_ends_def no_multi_arcs dest: inj_onD)
qed

lemma (in pre_digraph) symmetricI_app_iso:
  assumes "digraph_isomorphism hom"
  assumes "symmetric G"
  shows "symmetric (app_iso hom G)"
proof -
  let ?G = "app_iso hom G"
  have "sym (arcs_ends ?G)"
  proof (rule symI)
    fix u v assume "u \<rightarrow>\<^bsub>?G\<^esub> v"
    then obtain a where a: "a \<in> arcs ?G" "tail ?G a = u" "head ?G a = v" by auto
    then obtain a0 where a0: "a0 \<in> arcs G" "a = iso_arcs hom a0" by auto
    with \<open>symmetric G\<close> obtain b0 where "b0 \<in> arcs G" "tail G b0 = head G a0" "head G b0 = tail G a0"
      by (auto simp: symmetric_def arcs_ends_conv elim: symE)
    moreover
    define b where "b = iso_arcs hom b0"
    ultimately
    have "b \<in> iso_arcs hom ` arcs G" "tail ?G b = v" "head ?G b = u"
      using a a0 assms by (auto simp: iso_verts_tail iso_verts_head)
    then show "v \<rightarrow>\<^bsub>?G\<^esub> u" by (auto simp: arcs_ends_conv)
  qed
  then show ?thesis by (simp add: symmetric_def)
qed

lemma (in sym_digraph) sym_digraphI_app_iso:
  assumes "digraph_isomorphism hom"
  shows "sym_digraph (app_iso hom G)"
proof -
  interpret iG: wf_digraph "app_iso hom G" using assms by (rule wf_digraphI_app_iso)
  show ?thesis using assms by unfold_locales (intro symmetricI_app_iso sym_arcs) 
qed

lemma (in graph) graphI_app_iso:
  assumes "digraph_isomorphism hom"
  shows "graph (app_iso hom G)"
proof -
  interpret iG: fin_digraph "app_iso hom G"
    using assms by (rule fin_digraphI_app_iso)
  interpret iG: loopfree_digraph "app_iso hom G"
    using assms by (rule loopfree_digraphI_app_iso)
  interpret iG: nomulti_digraph "app_iso hom G"
    using assms by (rule nomulti_digraphI_app_iso)
  interpret iG: sym_digraph "app_iso hom G"
    using assms by (rule sym_digraphI_app_iso)
  show ?thesis by intro_locales
qed

lemma (in wf_digraph) graph_app_iso_eq:
  assumes "digraph_isomorphism hom"
  shows "graph (app_iso hom G) \<longleftrightarrow> graph G"
  using assms by (metis app_iso_inv digraph_isomorphism_invI graph.graphI_app_iso)

lemma (in pre_digraph) arcs_ends_iso:
  assumes "digraph_isomorphism hom"
  shows "arcs_ends (app_iso hom G) = (\<lambda>(u,v). (iso_verts hom u, iso_verts hom v)) ` arcs_ends G"
  using assms
  by (auto simp: arcs_ends_conv image_image iso_verts_tail iso_verts_head cong: image_cong)

lemma inj_onI_pair:
  assumes "inj_on f S" "T \<subseteq> S \<times> S"
  shows "inj_on (\<lambda>(u,v). (f u, f v)) T"
  using assms by (intro inj_onI) (auto dest: inj_onD)

lemma (in wf_digraph) complete_digraph_iso:
  assumes "digraph_isomorphism hom"
  shows "K\<^bsub>n\<^esub> (app_iso hom G) \<longleftrightarrow> K\<^bsub>n\<^esub> G" (is "?L \<longleftrightarrow> ?R")
proof 
  assume "?L"
  then interpret iG: graph "app_iso hom G" by (simp add: complete_digraph_def)
  { have "{(u, v). u \<in> iso_verts hom ` verts G \<and> v \<in> iso_verts hom ` verts G \<and> u \<noteq> v}
        = (\<lambda>(u,v). (iso_verts hom u, iso_verts hom v)) ` {(u,v). u \<in> verts G \<and> v \<in> verts G \<and> iso_verts hom u \<noteq> iso_verts hom v}" (is "?L = _")
      by auto
    also have "\<dots> = (\<lambda>(u,v). (iso_verts hom u, iso_verts hom v)) ` {(u,v). u \<in> verts G \<and> v \<in> verts G \<and> u \<noteq> v}"
      using digraph_isomorphism_inj_on_verts[OF assms] by (auto dest: inj_onD)
    finally have "?L = \<dots>" .
  } note X = this

  { fix A assume A: "A \<subseteq> verts G \<times> verts G"
    then have "inj_on (\<lambda>(u, v). (iso_verts hom u, iso_verts hom v)) A"
      using A digraph_isomorphism_inj_on_verts[OF assms] by (intro inj_onI_pair)
  } note Y = this
  have "(arcs_ends G \<union> {(u, v). u \<in> verts G \<and> v \<in> verts G \<and> u \<noteq> v}) \<subseteq> verts G \<times> verts G"
    by auto
  note Y' = Y[OF this]

  show ?R using assms \<open>?L\<close>
    by (simp add: complete_digraph_def X arcs_ends_iso graph_app_iso_eq inj_on_Un_image_eq_iff Y')
next
  assume "?R" then show ?L using assms
    by (fastforce simp add: complete_digraph_def arcs_ends_iso graph_app_iso_eq)
qed


subsubsection \<open>Conclusion\<close>

definition (in pre_digraph)
  mk_iso :: "('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> ('a, 'b, 'c, 'd) digraph_isomorphism"
where
  "mk_iso fv fa \<equiv> \<lparr> iso_verts = fv, iso_arcs = fa,
    iso_head = fv o head G o the_inv_into (arcs G) fa,
    iso_tail = fv o tail G o the_inv_into (arcs G) fa \<rparr>"

lemma (in pre_digraph) mk_iso_simps[simp]:
  "iso_verts (mk_iso fv fa) = fv"
  "iso_arcs (mk_iso fv fa) = fa"
  by (auto simp: mk_iso_def)

lemma (in wf_digraph) digraph_isomorphism_mk_iso:
  assumes "inj_on fv (verts G)" "inj_on fa (arcs G)"
  shows "digraph_isomorphism (mk_iso fv fa)"
  using assms by (auto simp: digraph_isomorphism_def mk_iso_def the_inv_into_f_f wf_digraph)

definition "pairself f \<equiv> \<lambda>x. case x of (u,v) \<Rightarrow> (f u, f v)"

lemma inj_on_pairself:
  assumes "inj_on f S" and "T \<subseteq> S \<times> S"
  shows "inj_on (pairself f) T"
  using assms unfolding pairself_def by (rule inj_onI_pair)

definition
  mk_iso_nomulti :: "('a,'b) pre_digraph \<Rightarrow> ('c,'d) pre_digraph \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> ('a, 'b, 'c, 'd) digraph_isomorphism"
where
  "mk_iso_nomulti G H fv \<equiv> \<lparr>
    iso_verts = fv,
    iso_arcs = the_inv_into (arcs H) (arc_to_ends H) o pairself fv o arc_to_ends G,
    iso_head = head H,
    iso_tail = tail H
  \<rparr>"

lemma (in pre_digraph) mk_iso_simps_nomulti[simp]:
  "iso_verts (mk_iso_nomulti G H fv) = fv"
  "iso_head (mk_iso_nomulti G H fv) = head H"
  "iso_tail (mk_iso_nomulti G H fv) = tail H"
  by (auto simp: mk_iso_nomulti_def)

lemma (in nomulti_digraph)  
  assumes "nomulti_digraph H"
  assumes fv: "inj_on fv (verts G)" "verts H = fv ` verts G" and arcs_ends: "arcs_ends H = pairself fv ` arcs_ends G"
  shows digraph_isomorphism_mk_iso_nomulti: "digraph_isomorphism (mk_iso_nomulti G H fv)" (is "?t_multi")
    and ap_iso_mk_iso_nomulti_eq: "app_iso (mk_iso_nomulti G H fv) G = H" (is "?t_app")
    and digraph_iso_mk_iso_nomulti: "digraph_iso G H" (is "?t_iso")
  using assms
proof -
  interpret H: nomulti_digraph H by fact
  let ?fa = "iso_arcs (mk_iso_nomulti G H fv)"

  have fa: "bij_betw ?fa (arcs G) (arcs H)"
  proof -
    have "bij_betw (arc_to_ends G) (arcs G) (arcs_ends G)"
      by (auto simp: bij_betw_def inj_on_arc_to_ends arcs_ends_def)
    also have "bij_betw (pairself fv) (arcs_ends G) (arcs_ends H)"
      using arcs_ends by (auto simp: bij_betw_def arcs_ends_def arc_to_ends_def intro: fv inj_on_pairself)
    also (bij_betw_trans) have "bij_betw (the_inv_into (arcs H) (arc_to_ends H)) (arcs_ends H) (arcs H)"
      by (auto simp: bij_betw_def the_inv_into_into H.inj_on_arc_to_ends arcs_ends_def inj_on_the_inv_into)
    finally (bij_betw_trans) show ?thesis
      by (simp add: mk_iso_nomulti_def o_assoc)
  qed
  moreover
  { fix a assume "a \<in> arcs G"
    then have "pairself fv (arc_to_ends G a) \<in> arcs_ends H"
      using arcs_ends by (auto simp: arcs_ends_def)
    then obtain b where "(pairself fv (arc_to_ends G a)) = arc_to_ends H b" "b \<in> arcs H"
      by (auto simp: arcs_ends_def)
    then have "fv (tail G a) = tail H (?fa a)" "fv (head G a) = head H (?fa a)"
      by (auto simp: mk_iso_nomulti_def the_inv_into_f_f H.inj_on_arc_to_ends)
        (auto simp: pairself_def arc_to_ends_def)
  }
  ultimately
  show ?t_multi ?t_app using fv by (auto simp: digraph_isomorphism_def bij_betw_def wf_digraph)
  then show ?t_iso by (auto simp: digraph_iso_def)
qed

lemma complete_digraph_are_iso:
  assumes "K\<^bsub>n\<^esub> G" "K\<^bsub>n\<^esub> H" shows "digraph_iso G H"
proof -
  interpret G: graph G using assms by (simp add: complete_digraph_def)
  interpret H: graph H using assms by (simp add: complete_digraph_def)

  from assms have "card (verts G) = n" "card (verts H) = n"
    by (auto simp: complete_digraph_def)
  with G.finite_verts H.finite_verts obtain fv where "bij_betw fv (verts G) (verts H)"
    by (metis finite_same_card_bij)
  then have fv: "inj_on fv (verts G)" "verts H = fv ` verts G" by (auto simp: bij_betw_def)

  have "arcs_ends H = {(u,v). u \<in> verts H \<and> v \<in> verts H \<and> u \<noteq> v}"
    using \<open>K\<^bsub>n\<^esub> H\<close> by (auto simp: complete_digraph_def)
  also have "\<dots> = pairself fv ` {(u,v). u \<in> verts G \<and> v \<in> verts G \<and> u \<noteq> v}" (is "?L = ?R")
  proof (intro set_eqI iffI)
    fix x assume "x \<in> ?L"
    then have "fst x \<in> fv ` verts G" "snd x \<in> fv ` verts G" "fst x \<noteq> snd x"
      using fv by auto
    then obtain u v where "fst x = fv u" "snd x = fv v" "u \<in> verts G" "v \<in> verts G" by auto
    then have "(fst x, snd x) \<in> ?R" using \<open>x \<in> ?L\<close> by (auto simp: pairself_def)
    then show "x \<in> ?R" by auto
  next
    fix x assume "x \<in> ?R" then show "x \<in> ?L"
    using fv by (auto simp: pairself_def dest: inj_onD)
  qed
  also have "\<dots> = pairself fv ` arcs_ends G"
    using \<open>K\<^bsub>n\<^esub> G\<close> by (auto simp: complete_digraph_def)
  finally  have arcs_ends: "arcs_ends H = pairself fv ` arcs_ends G" .

  show ?thesis using H.nomulti_digraph fv arcs_ends by (rule G.digraph_iso_mk_iso_nomulti)
qed

lemma pairself_image_prod:
  "pairself f ` (A \<times> B) = f ` A \<times> f ` B"
  by (auto simp: pairself_def)

lemma complete_bipartite_digraph_are_iso:
  assumes "K\<^bsub>m,n\<^esub> G" "K\<^bsub>m,n\<^esub> H" shows "digraph_iso G H"
proof -
  interpret G: graph G using assms by (simp add: complete_bipartite_digraph_def)
  interpret H: graph H using assms by (simp add: complete_bipartite_digraph_def)

  from assms obtain GU GV where G_parts: "verts G = GU \<union> GV" "GU \<inter> GV = {}"
      "card GU = m" "card GV = n" "arcs_ends G = GU \<times> GV \<union> GV \<times> GU"
    by (auto simp: complete_bipartite_digraph_def)
  from assms obtain HU HV where H_parts: "verts H = HU \<union> HV" "HU \<inter> HV = {}"
      "card HU = m" "card HV = n" "arcs_ends H = HU \<times> HV \<union> HV \<times> HU"
    by (auto simp: complete_bipartite_digraph_def)

  have fin: "finite GU" "finite GV" "finite HU" "finite HV"
    using G_parts H_parts G.finite_verts H.finite_verts by simp_all

  obtain fv_U where fv_U: "bij_betw fv_U GU HU"
    using \<open>card GU = _\<close> \<open>card HU = _\<close> \<open>finite GU\<close> \<open>finite HU\<close> by (metis finite_same_card_bij)
  obtain fv_V where fv_V: "bij_betw fv_V GV HV"
    using \<open>card GV = _\<close> \<open>card HV = _\<close> \<open>finite GV\<close> \<open>finite HV\<close> by (metis finite_same_card_bij)

  define fv where "fv x = (if x \<in> GU then fv_U x else fv_V x)" for x
  have "\<And>x. x \<in> GV \<Longrightarrow> x \<notin> GU" using \<open>GU \<inter> GV = {}\<close> by blast
  then have bij_fv_UV: "bij_betw fv GU HU" "bij_betw fv GV HV"
    using fv_U fv_V by (auto simp: fv_def cong: bij_betw_cong)
  then have "bij_betw fv (verts G) (verts H)"
    unfolding \<open>verts G = _\<close> \<open>verts H = _\<close> using \<open>HU \<inter> _ = {}\<close> by (rule bij_betw_combine)
  then have fv: "inj_on fv (verts G)" "verts H = fv ` verts G" by (auto simp: bij_betw_def)

  have "arcs_ends H = HU \<times> HV \<union> HV \<times> HU"
    using \<open>K\<^bsub>m,n\<^esub> H\<close> H_parts by (auto simp: complete_digraph_def)
  also have "\<dots> = pairself fv ` (GU \<times> GV \<union> GV \<times> GU)" (is "?L = ?R")
  proof (intro set_eqI iffI)
    fix x assume "x \<in> ?L"
    then have "(fst x \<in> fv ` GU \<and> snd x \<in> fv ` GV) \<or> (fst x \<in> fv ` GV \<and> snd x \<in> fv ` GU)"
      using bij_fv_UV by (auto simp: bij_betw_def)
    then show "x \<in> ?R"
      by (cases x) (auto simp: pairself_image_prod image_Un)
  next
    fix x assume "x \<in> ?R" then show "x \<in> ?L"
      using bij_fv_UV by (auto simp: pairself_image_prod image_Un bij_betw_def)
  qed
  also have "\<dots> = pairself fv ` arcs_ends G"
    using \<open>K\<^bsub>m,n\<^esub> G\<close> G_parts by (auto simp: complete_bipartite_digraph_def)
  finally have arcs_ends: "arcs_ends H = pairself fv ` arcs_ends G" .

  show ?thesis using H.nomulti_digraph fv arcs_ends by (rule G.digraph_iso_mk_iso_nomulti)
qed

lemma K5_not_comb_planar:
  assumes "K\<^bsub>5\<^esub> G" shows "\<not>comb_planar G"
proof -
  interpret graph G using assms by (auto simp: complete_digraph_def)
  have "digraph_iso G c_K5"
    using assms complete_c_K5 by (rule complete_digraph_are_iso)
  then obtain hom where hom: "digraph_isomorphism hom" "app_iso hom G = c_K5"
    by (auto simp: digraph_iso_def)
  then show ?thesis using c_K5_not_comb_planar comb_planar_iso by fastforce
qed

lemma K33_not_comb_planar:
  assumes "K\<^bsub>3,3\<^esub> G" shows "\<not>comb_planar G"
proof -
  interpret graph G using assms by (auto simp: complete_bipartite_digraph_def)
  have "digraph_iso G c_K33"
    using assms complete_c_K33 by (rule complete_bipartite_digraph_are_iso)
  then obtain hom where hom: "digraph_isomorphism hom" "app_iso hom G = c_K33"
    by (auto simp: digraph_iso_def)
  then show ?thesis using c_K33_not_comb_planar comb_planar_iso by fastforce 
qed

end
