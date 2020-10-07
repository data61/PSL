theory Graph_Genus
imports
  Graph_Theory.Graph_Theory
  "HOL-Library.Permutations"
begin

lemma nat_diff_mod_right:
  fixes a b c :: nat
  assumes "b < a"
  shows "(a - b) mod c = (a - b mod c) mod c"
proof -
  from assms have b_mod: "b mod c \<le> a"
    by (metis mod_less_eq_dividend linear not_le order_trans)
  have "int ((a - b) mod c) = (int a - int b mod int c) mod int c"
    using assms by (simp add: zmod_int of_nat_diff mod_simps)
  also have "\<dots> = int ((a - b mod c) mod c)"
    using assms b_mod
    by (simp add: zmod_int [symmetric] of_nat_diff [symmetric])
  finally show ?thesis by simp
qed

lemma inj_on_f_imageI:
  assumes "inj_on f S" "\<And>t. t \<in> T \<Longrightarrow> t \<subseteq> S"
  shows "inj_on ((`) f) T"
  using assms by (auto simp: inj_on_image_eq_iff intro: inj_onI)



section \<open>Combinatorial Maps\<close>

lemma (in bidirected_digraph) has_dom_arev:
  "has_dom arev (arcs G)"
  using arev_dom by (auto simp: has_dom_def)

record 'b pre_map =
  edge_rev :: "'b \<Rightarrow> 'b"
  edge_succ :: "'b \<Rightarrow> 'b"

definition edge_pred :: "'b pre_map \<Rightarrow> 'b \<Rightarrow> 'b" where
  "edge_pred M = inv (edge_succ M)"


locale pre_digraph_map = pre_digraph + fixes M :: "'b pre_map"

locale digraph_map = fin_digraph G
  + pre_digraph_map G M
  + bidirected_digraph G "edge_rev M" for G M +
  assumes edge_succ_permutes: "edge_succ M permutes arcs G"
  assumes edge_succ_cyclic: "\<And>v. v \<in> verts G \<Longrightarrow> out_arcs G v \<noteq> {} \<Longrightarrow> cyclic_on (edge_succ M) (out_arcs G v)"

lemma (in fin_digraph) digraph_mapI:
  assumes bidi: "\<And>a. a \<notin> arcs G \<Longrightarrow> edge_rev M a = a"
    "\<And>a. a \<in> arcs G \<Longrightarrow> edge_rev M a \<noteq> a"
    "\<And>a. a \<in> arcs G \<Longrightarrow> edge_rev M (edge_rev M a) = a"
    "\<And>a. a \<in> arcs G \<Longrightarrow> tail G (edge_rev M a) = head G a"
  assumes edge_succ_permutes: "edge_succ M permutes arcs G"
  assumes edge_succ_cyclic: "\<And>v. v \<in> verts G \<Longrightarrow> out_arcs G v \<noteq> {} \<Longrightarrow> cyclic_on (edge_succ M) (out_arcs G v)"
  shows "digraph_map G M"
  using assms by unfold_locales auto

lemma (in fin_digraph) digraph_mapI_permutes:
  assumes bidi: "edge_rev M permutes arcs G"
    "\<And>a. a \<in> arcs G \<Longrightarrow> edge_rev M a \<noteq> a"
    "\<And>a. a \<in> arcs G \<Longrightarrow> edge_rev M (edge_rev M a) = a"
    "\<And>a. a \<in> arcs G \<Longrightarrow> tail G (edge_rev M a) = head G a"
  assumes edge_succ_permutes: "edge_succ M permutes arcs G"
  assumes edge_succ_cyclic: "\<And>v. v \<in> verts G \<Longrightarrow> out_arcs G v \<noteq> {} \<Longrightarrow> cyclic_on (edge_succ M) (out_arcs G v)"
  shows "digraph_map G M"
proof -
  interpret bidirected_digraph G "edge_rev M" using bidi by unfold_locales (auto simp: permutes_def)
  show ?thesis
    using edge_succ_permutes edge_succ_cyclic by unfold_locales
qed


context digraph_map
begin

  lemma digraph_map[intro]: "digraph_map G M" by unfold_locales

  lemma permutation_edge_succ: "permutation (edge_succ M)"
    by (metis edge_succ_permutes finite_arcs permutation_permutes)

  lemma edge_pred_succ[simp]: "edge_pred M (edge_succ M a) = a"
    by (metis edge_pred_def edge_succ_permutes permutes_inverses(2))

  lemma edge_succ_pred[simp]: "edge_succ M (edge_pred M a) = a"
    by (metis edge_pred_def edge_succ_permutes permutes_inverses(1))

  lemma edge_pred_permutes: "edge_pred M permutes arcs G"
    unfolding edge_pred_def using edge_succ_permutes by (rule permutes_inv)

  lemma permutation_edge_pred: "permutation (edge_pred M)"
    by (metis edge_pred_permutes finite_arcs permutation_permutes)

  lemma edge_succ_eq_iff[simp]: "\<And>x y. edge_succ M x = edge_succ M y \<longleftrightarrow> x = y"
    by (metis edge_pred_succ)

  lemma edge_rev_in_arcs[simp]: "edge_rev M a \<in> arcs G \<longleftrightarrow> a \<in> arcs G"
    by (metis arev_arev arev_permutes_arcs permutes_not_in)

  lemma edge_succ_in_arcs[simp]: "edge_succ M a \<in> arcs G \<longleftrightarrow> a \<in> arcs G"
    by (metis edge_pred_succ edge_succ_permutes permutes_not_in)

  lemma edge_pred_in_arcs[simp]: "edge_pred M a \<in> arcs G \<longleftrightarrow> a \<in> arcs G"
    by (metis edge_succ_pred edge_pred_permutes permutes_not_in)

  lemma tail_edge_succ[simp]: "tail G (edge_succ M a) = tail G a"
  proof cases
    assume "a \<in> arcs G"
    then have "tail G a \<in> verts G" by auto
    moreover
    then have "out_arcs G (tail G a) \<noteq> {}"
      using \<open>a \<in> arcs G\<close> by auto
    ultimately
    have "cyclic_on (edge_succ M) (out_arcs G (tail G a))"
      by (rule edge_succ_cyclic)
    moreover
    have "a \<in> out_arcs G (tail G a)"
      using \<open>a \<in> arcs G\<close> by simp
    ultimately
    have "edge_succ M a \<in> out_arcs G (tail G a)"
      by (rule cyclic_on_inI)
    then show ?thesis by simp
  next
    assume "a \<notin> arcs G" then show ?thesis using edge_succ_permutes by (simp add: permutes_not_in)
  qed

  lemma tail_edge_pred[simp]: "tail G (edge_pred M a) = tail G a"
  by (metis edge_succ_pred tail_edge_succ)

  lemma bij_edge_succ[intro]: "bij (edge_succ M)"
    using edge_succ_permutes by (simp add: permutes_conv_has_dom)

  lemma edge_pred_cyclic:
    assumes "v \<in> verts G" "out_arcs G v \<noteq> {}"
    shows "cyclic_on (edge_pred M) (out_arcs G v)"
  proof -
    obtain a where orb_a_eq: "orbit (edge_succ M) a = out_arcs G v"
      using edge_succ_cyclic[OF assms] by (auto simp: cyclic_on_def)
    have "cyclic_on (edge_pred M) (orbit (edge_pred M) a)"
      using permutation_edge_pred by (rule cyclic_on_orbit')
    also have "orbit (edge_pred M) a = orbit (edge_succ M) a"
      unfolding edge_pred_def using permutation_edge_succ by (rule orbit_inv_eq)
    finally show "cyclic_on (edge_pred M) (out_arcs G v)" by (simp add: orb_a_eq)
  qed

  definition (in pre_digraph_map) face_cycle_succ :: "'b \<Rightarrow> 'b" where
    "face_cycle_succ \<equiv> edge_succ M o edge_rev M"

  definition (in pre_digraph_map) face_cycle_pred :: "'b \<Rightarrow> 'b" where
    "face_cycle_pred \<equiv> edge_rev M o edge_pred M"

  lemma face_cycle_pred_succ[simp]:
    shows "face_cycle_pred (face_cycle_succ a) = a"
    unfolding face_cycle_pred_def face_cycle_succ_def by simp

  lemma face_cycle_succ_pred[simp]:
    shows "face_cycle_succ (face_cycle_pred a) = a"
    unfolding face_cycle_pred_def face_cycle_succ_def by simp

  lemma tail_face_cycle_succ: "a \<in> arcs G \<Longrightarrow> tail G (face_cycle_succ a) = head G a"
    by (auto simp: face_cycle_succ_def)

  lemma funpow_prop:
    assumes "\<And>x. P (f x) \<longleftrightarrow> P x"
    shows "P ((f ^^ n) x) \<longleftrightarrow> P x"
    using assms by (induct n) (auto simp: )

  lemma face_cycle_succ_no_arc[simp]: "a \<notin> arcs G \<Longrightarrow> face_cycle_succ a = a"
    by (auto simp: face_cycle_succ_def permutes_not_in[OF arev_permutes_arcs]
      permutes_not_in[OF edge_succ_permutes])

  lemma funpow_face_cycle_succ_no_arc[simp]:
    assumes "a \<notin> arcs G" shows "(face_cycle_succ ^^ n) a = a"
    using assms by (induct n) auto

  lemma funpow_face_cycle_pred_no_arc[simp]:
    assumes "a \<notin> arcs G" shows "(face_cycle_pred ^^ n) a = a"
    using assms
    by (induct n) (auto simp: face_cycle_pred_def permutes_not_in[OF arev_permutes_arcs]
      permutes_not_in[OF edge_pred_permutes])

  lemma face_cycle_succ_closed[simp]:
    "face_cycle_succ a \<in> arcs G \<longleftrightarrow> a \<in> arcs G"
    by (metis comp_apply edge_rev_in_arcs edge_succ_in_arcs face_cycle_succ_def)

  lemma face_cycle_pred_closed[simp]:
    "face_cycle_pred a \<in> arcs G \<longleftrightarrow> a \<in> arcs G"
    by (metis face_cycle_succ_closed face_cycle_succ_pred)

  lemma face_cycle_succ_permutes:
    "face_cycle_succ permutes arcs G"
    unfolding face_cycle_succ_def
    using arev_permutes_arcs edge_succ_permutes by (rule permutes_compose)

  lemma permutation_face_cycle_succ: "permutation face_cycle_succ"
    using face_cycle_succ_permutes finite_arcs by (metis permutation_permutes)

  lemma bij_face_cycle_succ: "bij face_cycle_succ"
    using face_cycle_succ_permutes by (simp add: permutes_conv_has_dom)

  lemma face_cycle_pred_permutes:
    "face_cycle_pred permutes arcs G"
    unfolding face_cycle_pred_def
    using edge_pred_permutes arev_permutes_arcs by (rule permutes_compose)

  definition (in pre_digraph_map) face_cycle_set :: "'b \<Rightarrow> 'b set" where
    "face_cycle_set a = orbit face_cycle_succ a"

  definition (in pre_digraph_map) face_cycle_sets :: "'b set set" where
    "face_cycle_sets = face_cycle_set ` arcs G"

  lemma face_cycle_set_altdef: "face_cycle_set a = {(face_cycle_succ ^^ n) a | n. True}"
    unfolding face_cycle_set_def
    by (intro orbit_altdef_self_in permutation_self_in_orbit permutation_face_cycle_succ)

  lemma face_cycle_set_self[simp, intro]: "a \<in> face_cycle_set a"
    unfolding face_cycle_set_def using permutation_face_cycle_succ by (rule permutation_self_in_orbit)

  lemma empty_not_in_face_cycle_sets: "{} \<notin> face_cycle_sets"
      by (auto simp: face_cycle_sets_def)

  lemma finite_face_cycle_set[simp, intro]: "finite (face_cycle_set a)"
    using face_cycle_set_self unfolding face_cycle_set_def by (simp add: finite_orbit)

  lemma finite_face_cycle_sets[simp, intro]: "finite face_cycle_sets"
    by (auto simp: face_cycle_sets_def)

  lemma face_cycle_set_induct[case_names base step, induct set: face_cycle_set]:
    assumes consume: "a \<in> face_cycle_set x"
      and ih_base: "P x"
      and ih_step: "\<And>y. y \<in> face_cycle_set x \<Longrightarrow> P y \<Longrightarrow> P (face_cycle_succ y)"
    shows "P a"
    using consume unfolding face_cycle_set_def
    by induct (auto simp: ih_step face_cycle_set_def[symmetric] ih_base )

  lemma face_cycle_succ_cyclic:
    "cyclic_on face_cycle_succ (face_cycle_set a)"
    unfolding face_cycle_set_def using permutation_face_cycle_succ by (rule cyclic_on_orbit')

  lemma face_cycle_eq:
    assumes "b \<in> face_cycle_set a" shows "face_cycle_set b = face_cycle_set a"
    using assms unfolding face_cycle_set_def
    by (auto intro: orbit_swap orbit_trans permutation_face_cycle_succ permutation_self_in_orbit)

  lemma face_cycle_succ_in_arcsI: "\<And>a. a \<in> arcs G \<Longrightarrow> face_cycle_succ a \<in> arcs G"
    by (auto simp: face_cycle_succ_def)

  lemma face_cycle_succ_inI: "\<And>x y. x \<in> face_cycle_set y \<Longrightarrow> face_cycle_succ x \<in> face_cycle_set y"
    by (metis face_cycle_succ_cyclic cyclic_on_inI)

  lemma face_cycle_succ_inD: "\<And>x y. face_cycle_succ x \<in> face_cycle_set y \<Longrightarrow> x \<in> face_cycle_set y"
    by (metis face_cycle_eq face_cycle_set_self face_cycle_succ_inI)

  lemma face_cycle_set_parts:
    "face_cycle_set a = face_cycle_set b \<or> face_cycle_set a \<inter> face_cycle_set b = {}"
    by (metis disjoint_iff_not_equal face_cycle_eq)

  definition fc_equiv :: "'b \<Rightarrow> 'b \<Rightarrow> bool" where
    "fc_equiv a b \<equiv> a \<in> face_cycle_set b"

  lemma reflp_fc_equiv: "reflp fc_equiv"
    by (rule reflpI) (simp add: fc_equiv_def)

  lemma symp_fc_equiv: "symp fc_equiv"
    using face_cycle_set_parts
    by (intro sympI) (auto simp: fc_equiv_def)

  lemma transp_fc_equiv: "transp fc_equiv"
    using face_cycle_set_parts
    by (intro transpI) (auto simp: fc_equiv_def)

  lemma "equivp fc_equiv"
    by (intro equivpI reflp_fc_equiv symp_fc_equiv transp_fc_equiv)

  lemma in_face_cycle_setD:
    assumes "y \<in> face_cycle_set x" "x \<in> arcs G" shows "y \<in> arcs G"
    using assms
    by (auto simp: face_cycle_set_def dest: permutes_orbit_subset[OF face_cycle_succ_permutes])

  lemma in_face_cycle_setsD:
    assumes "x \<in> face_cycle_sets" shows "x \<subseteq> arcs G"
    using assms by (auto simp: face_cycle_sets_def dest: in_face_cycle_setD)

end

definition (in pre_digraph) isolated_verts :: "'a set" where
  "isolated_verts \<equiv> {v \<in> verts G. out_arcs G v = {}}"

definition (in pre_digraph_map) euler_char :: int where
  "euler_char \<equiv> int (card (verts G)) - int (card (arcs G) div 2) + int (card face_cycle_sets)"

definition (in pre_digraph_map) euler_genus :: int where
  "euler_genus \<equiv> (int (2 * card sccs) - int (card isolated_verts) - euler_char) div 2"

definition comb_planar :: "('a,'b) pre_digraph \<Rightarrow> bool" where
  "comb_planar G \<equiv> \<exists>M. digraph_map G M \<and> pre_digraph_map.euler_genus G M = 0"


text \<open>Number of isolated vertices is a graph invariant\<close>
context
  fixes G hom assumes hom: "pre_digraph.digraph_isomorphism G hom"
begin

  interpretation wf_digraph G using hom by (auto simp: pre_digraph.digraph_isomorphism_def)

  lemma isolated_verts_app_iso[simp]:
    "pre_digraph.isolated_verts (app_iso hom G) = iso_verts hom ` isolated_verts"
    using hom
    by (auto simp: pre_digraph.isolated_verts_def iso_verts_tail inj_image_mem_iff out_arcs_app_iso_eq)

  lemma card_isolated_verts_iso[simp]:
    "card (iso_verts hom ` pre_digraph.isolated_verts G) = card isolated_verts"
    apply (rule card_image)
    using hom apply (rule digraph_isomorphism_inj_on_verts[THEN subset_inj_on])
    apply (auto simp: isolated_verts_def)
    done

end



context digraph_map begin

  lemma face_cycle_succ_neq:
    assumes "a \<in> arcs G" "tail G a \<noteq> head G a" shows "face_cycle_succ a \<noteq> a "
  proof -
    from assms have "edge_rev M a \<in> arcs G"
      by (subst edge_rev_in_arcs) simp
    then have "cyclic_on (edge_succ M) (out_arcs G (tail G (edge_rev M a)))"
      by (intro edge_succ_cyclic) (auto dest: tail_in_verts simp: out_arcs_def intro: exI[where x="edge_rev M a"])
    then have "edge_succ M (edge_rev M a) \<in> (out_arcs G (tail G (edge_rev M a)))"
      by (rule cyclic_on_inI) (auto simp: \<open>edge_rev M a \<in> _\<close>[simplified])
    moreover have "tail G (edge_succ M (edge_rev M a)) = head G a"
      using assms by auto
    then have "edge_succ M (edge_rev M a) \<noteq> a" using assms by metis
    ultimately show ?thesis
      using assms by (auto simp: face_cycle_succ_def)
  qed

end


section \<open>Maps and Isomorphism\<close>

definition (in pre_digraph)
  "wrap_iso_arcs hom f = perm_restrict (iso_arcs hom o f o iso_arcs (inv_iso hom)) (arcs (app_iso hom G))"

definition (in pre_digraph_map) map_iso :: "('a,'b,'a2,'b2) digraph_isomorphism \<Rightarrow> 'b2 pre_map" where
  "map_iso f \<equiv> 
  \<lparr> edge_rev = wrap_iso_arcs f (edge_rev M)
  , edge_succ = wrap_iso_arcs f (edge_succ M)
  \<rparr>"

lemma funcsetI_permutes:
  assumes "f permutes S" shows "f \<in> S \<rightarrow> S"
  by (metis assms funcsetI permutes_in_image)

context
  fixes G hom assumes hom: "pre_digraph.digraph_isomorphism G hom"
begin

  interpretation wf_digraph G using hom by (auto simp: pre_digraph.digraph_isomorphism_def)

  lemma wrap_iso_arcs_iso_arcs[simp]:
    assumes "x \<in> arcs G"
    shows "wrap_iso_arcs hom f (iso_arcs hom x) = iso_arcs hom (f x)"
    using assms hom by (auto simp: wrap_iso_arcs_def perm_restrict_def)

  lemma inj_on_wrap_iso_arcs:
    assumes dom: "\<And>f. f \<in> F \<Longrightarrow> has_dom f (arcs G)"
    assumes funcset: "F \<subseteq> arcs G \<rightarrow> arcs G"
    shows "inj_on (wrap_iso_arcs hom) F"
  proof (rule inj_onI)
    fix f g assume F: "f \<in> F" "g \<in> F" and eq: "wrap_iso_arcs hom f = wrap_iso_arcs hom g"
    { fix x assume "x \<notin> arcs G"
      then have "f x = x" "g x = x" using F dom by (auto simp: has_dom_def)
      then have "f x = g x" by simp
    }
    moreover
    { fix x assume "x \<in> arcs G"
      then have "f x \<in> arcs G" "g x \<in> arcs G" using F funcset by auto
      with digraph_isomorphism_inj_on_arcs[OF hom] _
      have "iso_arcs hom (f x) = iso_arcs hom (g x) \<Longrightarrow> f x = g x"
        by (rule inj_onD)
      then have "f x = g x"
        using assms hom  \<open>x \<in> arcs G\<close> eq
        by (auto simp: wrap_iso_arcs_def fun_eq_iff perm_restrict_def split: if_splits)
    }
    ultimately show "f = g" by auto
  qed
  
  lemma inj_on_wrap_iso_arcs_f:
    assumes "A \<subseteq> arcs G" "f \<in> A \<rightarrow> A" "B = iso_arcs hom ` A"
    assumes "inj_on f A" shows "inj_on (wrap_iso_arcs hom f) B"
  proof (rule inj_onI)
    fix x y
    assume in_hom_A: "x \<in> B" "y \<in> B"
      and wia_eq: "wrap_iso_arcs hom f x = wrap_iso_arcs hom f y"
    from in_hom_A \<open>B = _\<close> obtain x0 where x0: "x = iso_arcs hom x0" "x0 \<in> A" by auto
    from in_hom_A \<open>B = _\<close> obtain y0 where y0: "y = iso_arcs hom y0" "y0 \<in> A" by auto
    have arcs_0: "x0 \<in> arcs G" "y0 \<in> arcs G" "f x0 \<in> arcs G" "f y0 \<in> arcs G"
      using x0 y0 \<open>A \<subseteq> _\<close> \<open>f \<in> _\<close> by auto
  
    have "(iso_arcs hom o f o iso_arcs (inv_iso hom)) x = (iso_arcs hom o f o iso_arcs (inv_iso hom)) y"
      using in_hom_A wia_eq assms(1) \<open>B = _\<close> by (auto simp: wrap_iso_arcs_def perm_restrict_def split: if_splits)
    then show "x = y"
      using hom assms digraph_isomorphism_inj_on_arcs[OF hom] x0 y0 arcs_0 \<open>inj_on f A\<close> \<open>A \<subseteq> _\<close>
      by (auto dest!:  inj_onD)
  qed
  
  lemma wrap_iso_arcs_in_funcsetI:
    assumes "A \<subseteq> arcs G" "f \<in> A \<rightarrow> A"
    shows "wrap_iso_arcs hom f \<in> iso_arcs hom ` A  \<rightarrow> iso_arcs hom ` A"
  proof
    fix x assume "x \<in> iso_arcs hom ` A"
    then obtain x0 where "x = iso_arcs hom x0" "x0 \<in> A" by blast
    then have "f x0 \<in> A" using \<open>f \<in> _\<close> by auto
    then show "wrap_iso_arcs hom f x \<in> iso_arcs hom ` A"
      unfolding \<open>x = _\<close> using \<open>x0 \<in> A\<close> assms hom by (auto simp: wrap_iso_arcs_def perm_restrict_def)
  qed
  
  lemma wrap_iso_arcs_permutes:
    assumes "A \<subseteq> arcs G" "f permutes A"
    shows "wrap_iso_arcs hom f permutes (iso_arcs hom ` A)"
  proof -
    { fix x assume A: "x \<notin> iso_arcs hom ` A"
      have "wrap_iso_arcs hom f x = x"
      proof cases
        assume "x \<in> iso_arcs hom ` arcs G"
        then have "iso_arcs (inv_iso hom) x \<notin> A" "x \<in> arcs (app_iso hom G)"
          using A hom by (metis arcs_app_iso image_eqI pre_digraph.iso_arcs_iso_inv, simp)
        then have "f (iso_arcs (inv_iso hom) x) = (iso_arcs (inv_iso hom) x)"
          using \<open>f permutes A\<close> by (simp add: permutes_not_in) 
        then show ?thesis using hom assms \<open>x \<in> arcs _\<close>
          by (simp add: wrap_iso_arcs_def perm_restrict_def)
      next
        assume "x \<notin> iso_arcs hom ` arcs G"
        then show ?thesis
          by (simp add: wrap_iso_arcs_def perm_restrict_def)
      qed
    } note not_in_id = this
  
    have "f \<in> A \<rightarrow> A" using assms by (intro funcsetI_permutes)
    have inj_on_wrap: "inj_on (wrap_iso_arcs hom f) (iso_arcs hom ` A)"
      using assms \<open>f \<in> A \<rightarrow> A\<close> by (intro inj_on_wrap_iso_arcs_f) (auto intro: subset_inj_on permutes_inj)
    have woa_in_fs: "wrap_iso_arcs hom f \<in> iso_arcs hom ` A \<rightarrow> iso_arcs hom ` A"
      using assms \<open>f \<in> A \<rightarrow> A\<close> by (intro wrap_iso_arcs_in_funcsetI)
  
    { fix x y assume "wrap_iso_arcs hom f x = wrap_iso_arcs hom f y"
      then have "x = y"
        apply (cases "x \<in> iso_arcs hom ` A"; cases "y \<in> iso_arcs hom ` A")
        using woa_in_fs inj_on_wrap by (auto dest: inj_onD simp: not_in_id)
    } note uniqueD = this
  
    note \<open>f permutes A\<close>
    moreover
    note not_in_id
    moreover
    { fix y have "\<exists>x. wrap_iso_arcs hom f x = y"
      proof cases
        assume "y \<in> iso_arcs hom ` A"
        then obtain y0 where "y0 \<in> A" "iso_arcs hom y0 = y" by blast
        with \<open>f permutes A\<close> obtain x0 where "x0 \<in> A" "f x0 = y0" unfolding permutes_def by metis
        moreover
        then have "\<And>x. x \<in> arcs G \<Longrightarrow> iso_arcs hom x0 = iso_arcs hom x \<Longrightarrow> x0 = x"
          using assms hom by (auto simp: digraph_isomorphism_def dest: inj_onD)
        ultimately
        have "wrap_iso_arcs hom f (iso_arcs hom x0) = y"
          using \<open>_ = y\<close> assms hom by (auto simp: wrap_iso_arcs_def perm_restrict_def)
        then show ?thesis ..
      qed (metis not_in_id)
    }
    ultimately
    show ?thesis unfolding permutes_def by (auto simp: dest: uniqueD)
  qed
  
end

lemma (in digraph_map) digraph_map_isoI:
  assumes "digraph_isomorphism hom" shows "digraph_map (app_iso hom G) (map_iso hom)"
proof -
  interpret iG: fin_digraph "app_iso hom G" using assms by (rule fin_digraphI_app_iso)
  show ?thesis
  proof (rule iG.digraph_mapI_permutes)
    show "edge_rev (map_iso hom) permutes arcs (app_iso hom G)"
      using assms unfolding map_iso_def by (simp add: wrap_iso_arcs_permutes arev_permutes_arcs)
  next
    show "edge_succ (map_iso hom) permutes arcs (app_iso hom G)"
      using assms unfolding map_iso_def by (simp add: wrap_iso_arcs_permutes edge_succ_permutes)
  next
    fix a assume A: "a \<in> arcs (app_iso hom G)"
    show "tail (app_iso hom G) (edge_rev (map_iso hom) a) = head (app_iso hom G) a"
      using A assms
      by (cases rule: in_arcs_app_iso_cases) (auto simp: map_iso_def iso_verts_tail iso_verts_head)
    show "edge_rev (map_iso hom) (edge_rev (map_iso hom) a) = a"
      using A assms by (cases rule: in_arcs_app_iso_cases) (auto simp: map_iso_def)
    show "edge_rev (map_iso hom) a \<noteq> a"
      using A assms by (auto simp: map_iso_def arev_neq)
  next
    fix v assume "v \<in> verts (app_iso hom G)" and oa_hom: "out_arcs (app_iso hom G) v \<noteq> {}"
    then obtain v0 where "v0 \<in> verts G" "v = iso_verts hom v0" by auto
    moreover
    then have oa: "out_arcs G v0 \<noteq> {}"
      using assms oa_hom by (auto simp: out_arcs_def iso_verts_tail)
    ultimately
    have cyclic_on_v0: "cyclic_on (edge_succ M) (out_arcs G v0)"
      by (intro edge_succ_cyclic)

    from oa_hom obtain a where "a \<in> out_arcs (app_iso hom G) v" by blast
    then obtain a0 where "a0 \<in> arcs G" "a = iso_arcs hom a0" by auto
    then have "a0 \<in> out_arcs G v0"
      using \<open>v = _\<close> \<open>v0 \<in> _\<close> \<open>a \<in> _\<close> assms by (simp add: iso_verts_tail)

    show "cyclic_on (edge_succ (map_iso hom)) (out_arcs (app_iso hom G) v)"
    proof (rule cyclic_on_singleI)
      show "a \<in> out_arcs (app_iso hom G) v" by fact
    next
      have "out_arcs (app_iso hom G) v = iso_arcs hom ` out_arcs G v0"
        unfolding \<open>v = _\<close> by (rule out_arcs_app_iso_eq) fact+
      also have "out_arcs G v0 = orbit (edge_succ M) a0"
        using cyclic_on_v0 \<open>a0 \<in> out_arcs G v0\<close> unfolding cyclic_on_alldef by simp
      also have "iso_arcs hom ` \<dots> = orbit (edge_succ (map_iso hom)) a"
      proof -
        have "\<And>x. x \<in> orbit (edge_succ M) a0 \<Longrightarrow> x \<in> arcs G"
          using \<open>out_arcs G v0 = _\<close> by auto
        then show ?thesis using \<open>out_arcs G v0 = _\<close>
          unfolding \<open>a = _\<close> assms using \<open>a0 \<in> out_arcs G v0\<close>
          by (intro orbit_FOO) (insert assms, auto simp: map_iso_def)
      qed
      finally show "out_arcs (app_iso hom G) v = orbit (edge_succ (map_iso hom)) a" .
    qed
  qed
qed

end

