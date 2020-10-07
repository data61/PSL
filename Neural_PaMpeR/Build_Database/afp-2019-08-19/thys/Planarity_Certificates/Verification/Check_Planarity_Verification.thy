section \<open>Verififcation of a Planarity Checker\<close>

theory Check_Planarity_Verification
imports
  "../Planarity/Graph_Genus"
  Setup_AutoCorres
  "HOL-Library.Rewrite"
begin

subsection  \<open>Implementation Types\<close>

type_synonym IVert = "nat"
type_synonym IEdge = "IVert \<times> IVert"
type_synonym IGraph = "IVert list \<times> IEdge list"

abbreviation (input) ig_edges :: "IGraph \<Rightarrow> IEdge list" where
  "ig_edges G \<equiv> snd G"

abbreviation (input) ig_verts :: "IGraph \<Rightarrow> IVert list" where
  "ig_verts G \<equiv> fst G"

definition ig_tail :: "IGraph \<Rightarrow> nat \<Rightarrow> IVert" where
  "ig_tail IG a = fst (ig_edges IG ! a)"

definition ig_head :: "IGraph \<Rightarrow> nat \<Rightarrow> IVert" where
  "ig_head IG a = snd (ig_edges IG ! a)"

type_synonym IMap = "(nat \<Rightarrow> nat) \<times> (nat \<Rightarrow> nat) \<times> (nat \<Rightarrow> nat)"

definition im_rev :: "IMap \<Rightarrow> (nat \<Rightarrow> nat)" where
  "im_rev iM = fst iM"

definition im_succ :: "IMap \<Rightarrow> (nat \<Rightarrow> nat)" where
  "im_succ iM = fst (snd iM)"

definition im_pred :: "IMap \<Rightarrow> (nat \<Rightarrow> nat)" where
  "im_pred iM = snd (snd iM)"


definition mk_graph :: "IGraph \<Rightarrow> (IVert, nat) pre_digraph" where
  "mk_graph IG \<equiv> \<lparr>
    verts = set (ig_verts IG),
    arcs = {0..< length (ig_edges IG)},
    tail = ig_tail IG,
    head = ig_head IG
  \<rparr>"

lemma mkg_simps:
  "verts (mk_graph IG) = set (ig_verts IG)"
  "tail (mk_graph IG) = ig_tail IG"
  "head (mk_graph IG) = ig_head IG"
  by (auto simp: mk_graph_def)

lemma arcs_mkg: "arcs (mk_graph IG) = {0..< length (ig_edges IG)}"
  by (auto simp: mk_graph_def)

lemma arc_to_ends_mkg: "arc_to_ends (mk_graph IG) a = ig_edges IG ! a"
  by (auto simp: arc_to_ends_def mkg_simps ig_tail_def ig_head_def)

definition mk_map :: "(_, nat) pre_digraph \<Rightarrow> IMap \<Rightarrow> nat pre_map" where
  "mk_map G iM \<equiv> \<lparr>
    edge_rev = perm_restrict (im_rev iM) (arcs G),
    edge_succ = perm_restrict (im_succ iM) (arcs G)
  \<rparr>"

lemma mkm_simps:
  "edge_rev (mk_map G iM) = perm_restrict (im_rev iM) (arcs G)"
  "edge_succ (mk_map G iM) = perm_restrict (im_succ iM) (arcs G)"
  by (auto simp: mk_map_def)

lemma es_eq_im: "a \<in> arcs (mk_graph iG) \<Longrightarrow> edge_succ (mk_map (mk_graph iG) iM) a = im_succ iM a"
  by (auto simp: mkm_simps arcs_mkg perm_restrict_simps)


subsection \<open>Implementation\<close>

definition "is_map iG iM \<equiv>
  DO ecnt \<leftarrow> oreturn (length (snd iG));
     vcnt \<leftarrow> oreturn (length (fst iG));
     (i, revOk) \<leftarrow> owhile
      (\<lambda>(i, ok) s. i < ecnt \<and> ok)
      (\<lambda>(i, ok).
        DO
          j \<leftarrow> oreturn (im_rev iM i);
          revIn \<leftarrow> oreturn (j < length (ig_edges iG));
          revNeq \<leftarrow> oreturn (j \<noteq> i);
          revRevs \<leftarrow> oreturn (ig_edges iG ! j = prod.swap (ig_edges iG ! i));
          invol \<leftarrow> oreturn (im_rev iM j = i);
          oreturn (i + 1, revIn \<and> revNeq \<and> revRevs \<and> invol)
        OD)
      (0, True);
     (i, succPerm) \<leftarrow> owhile
      (\<lambda>(i, ok) s. i < ecnt \<and> ok)
      (\<lambda>(i, ok).
        DO
          j \<leftarrow> oreturn (im_succ iM i);
          succIn \<leftarrow> oreturn (j < length (ig_edges iG));
          succEnd \<leftarrow> oreturn (ig_tail iG i = ig_tail iG j);
          isPerm \<leftarrow> oreturn (im_pred iM j = i);
          oreturn (i + 1, succIn \<and> succEnd \<and> isPerm)
        OD)
      (0, True);
     (i, succOrbits, V, A) \<leftarrow> owhile
      (\<lambda>(i, ok, V, A) s. i < ecnt \<and> succPerm \<and> ok)
      (\<lambda>(i, ok, V, A).
        DO
          (x,V,A) \<leftarrow> ocondition (\<lambda>_. ig_tail iG i \<in> V)
            (oreturn (i \<in> A, V, A))
            (DO
              (A',j) \<leftarrow> owhile
                (\<lambda>(A',j) s. j \<notin> A')
                (\<lambda>(A',j). DO
                    A' \<leftarrow> oreturn (insert j A');
                    j \<leftarrow> oreturn (im_succ iM j);
                    oreturn (A', j)
                  OD)
                ({},i);
              V \<leftarrow> oreturn (insert (ig_tail iG j) V);
              oreturn (True,V,A \<union> A')
            OD);
          oreturn (i + 1, x, V, A)
        OD)
      (0, True, {}, {});
     oreturn (revOk \<and> succPerm \<and> succOrbits)
  OD
"

definition isolated_nodes :: "IGraph \<Rightarrow> _ \<Rightarrow> nat option" where
"isolated_nodes iG \<equiv>
  DO ecnt \<leftarrow> oreturn (length (snd iG));
     vcnt \<leftarrow> oreturn (length (fst iG));
     (i, nz) \<leftarrow>
     owhile
      (\<lambda>(i, nz) a. i < vcnt)
      (\<lambda>(i, nz).
          DO v \<leftarrow> oreturn (fst iG ! i);
             j \<leftarrow> oreturn 0;
             ret \<leftarrow> ocondition (\<lambda>s. j < ecnt) (oreturn (ig_tail iG j \<noteq> v)) (oreturn False);
             ret \<leftarrow> ocondition (\<lambda>s. ret) (oreturn (ig_head iG j \<noteq> v)) (oreturn ret);
             (j, _) \<leftarrow>
             owhile
              (\<lambda>(j, cond) a. cond)
              (\<lambda>(j, cond).
                  DO j \<leftarrow> oreturn (j + 1);
                     cond \<leftarrow> ocondition (\<lambda>s. j < ecnt) (oreturn (ig_tail iG j \<noteq> v)) (oreturn False);
                     cond \<leftarrow> ocondition (\<lambda>s. cond) (oreturn (ig_head iG j \<noteq> v)) (oreturn cond);
                     oreturn (j, cond)
                  OD)
              (j, ret);
             nz \<leftarrow> oreturn (if j = ecnt then nz + 1 else nz);
             oreturn (i + 1, nz)
          OD)
      (0, 0);
     oreturn nz
  OD"

definition face_cycles :: "IGraph \<Rightarrow> nat pre_map \<Rightarrow> _  \<Rightarrow> nat option" where
"face_cycles iG iM \<equiv>
  DO ecnt \<leftarrow> oreturn (length (snd iG));
     (edge_info, c, i) \<leftarrow>
     owhile
      (\<lambda>(edge_info, c, i) s. i < ecnt)
      (\<lambda>(edge_info, c, i).
          DO (edge_info, c) \<leftarrow>
             ocondition (\<lambda>s. i \<notin> edge_info)
              (DO j \<leftarrow> oreturn i;
                  edge_info \<leftarrow> oreturn (insert j edge_info);
                  ret' \<leftarrow> oreturn (pre_digraph_map.face_cycle_succ iM j);
                  (edge_info, j) \<leftarrow>
                  owhile
                   (\<lambda>(edge_info, j) s. i \<noteq> j)
                   (\<lambda>(edge_info, j).
                       oreturn (insert j edge_info, pre_digraph_map.face_cycle_succ iM j))
                   (edge_info, ret');
                  oreturn (edge_info, c + 1)
               OD)
              (oreturn (edge_info, c));
             oreturn (edge_info, c, i + 1)
          OD)
      ({}, 0, 0);
     oreturn c
  OD"

definition "euler_genus iG iM c \<equiv>
   DO n \<leftarrow> oreturn (length (ig_edges iG));
      m \<leftarrow> oreturn (length (ig_verts iG));
      nz \<leftarrow> isolated_nodes iG;
      fc \<leftarrow> face_cycles iG iM;
      oreturn ((int n div 2 + 2 * int c - int m - int nz - int fc) div 2)
   OD"

definition "certify iG iM c \<equiv>
  DO
     map \<leftarrow> is_map iG iM;
     ocondition (\<lambda>_. map)
       (DO
          gen \<leftarrow> euler_genus iG (mk_map (mk_graph iG) iM) c;
          oreturn (gen = 0)
       OD)
       (oreturn False)
  OD"


subsection \<open>Verification\<close>

context begin
  interpretation Labeling_Syntax .
  lemma trivial_label: "P \<Longrightarrow> CTXT IC CT OC P"
    unfolding LABEL_simps .
end

lemma ovalidNF_wp:
  assumes "ovalidNF P c (\<lambda>r s. r = x)"
  shows "ovalidNF (\<lambda>s. Q x s \<and> P s) c Q"
  using assms unfolding ovalidNF_def by auto

subsubsection \<open>@{term is_map}\<close>

definition "is_map_rev_ok_inv iG iM k ok \<equiv> ok \<longleftrightarrow> (\<forall>i < k.
  im_rev iM i < length (ig_edges iG)
  \<and> ig_edges iG ! im_rev iM i = prod.swap (ig_edges iG ! i)
  \<and> im_rev iM i \<noteq> i
  \<and> im_rev iM (im_rev iM i) = i)
"

definition "is_map_succ_perm_inv iG iM k ok \<equiv> ok \<longleftrightarrow> (\<forall>i < k.
  im_succ iM i < length (ig_edges iG)
  \<and> ig_tail iG (im_succ iM i) = ig_tail iG i
  \<and> im_pred iM (im_succ iM i) = i)
"

definition "is_map_succ_orbits_inv iG iM k ok V A \<equiv>
  A = (\<Union>i<(if ok then k else k - 1). orbit (im_succ iM) i) \<and>
  V = {ig_tail iG i | i. i<(if ok then k else k - 1)} \<and>
  ok = (\<forall>i < k. \<forall>j < k. ig_tail iG i = ig_tail iG j \<longrightarrow> j \<in> orbit (im_succ iM) i)
"

definition "is_map_succ_orbits_inner_inv iG iM i j A' \<equiv>
  A' = (if i = j \<and> i \<notin> A' then {} else {i} \<union> segment (im_succ iM) i j)
  \<and> j \<in> orbit (im_succ iM) i
"

definition "is_map_final iG k ok \<equiv> (ok \<longrightarrow> k = length (ig_edges iG)) \<and> k \<le> length (ig_edges iG)"

lemma bij_betwI_finite_dom:
  assumes "finite A" "f \<in> A \<rightarrow> A" "\<And>a. a \<in> A \<Longrightarrow> g (f a) = a"
  shows "bij_betw f A A"
proof -
  have "inj_on f A" by (metis assms(3) inj_onI)
  moreover
  then have "f ` A = A" by (metis Pi_iff assms(1-2) endo_inj_surj image_subsetI)
  ultimately show ?thesis unfolding bij_betw_def by simp
qed

lemma permutesI_finite_dom:
  assumes "finite A"
  assumes "f \<in> A \<rightarrow> A"
  assumes "\<And>a. a \<notin> A \<Longrightarrow> f a = a"
  assumes "\<And>a. a \<in> A \<Longrightarrow> g (f a) = a"
  shows "f permutes A"
  using assms by (intro bij_imp_permutes bij_betwI_finite_dom)

lemma orbit_ss:
  assumes "f \<in> A \<rightarrow> A" "a \<in> A"
  shows "orbit f a \<subseteq> A"
proof -
  { fix x assume "x \<in> orbit f a" then have "x \<in> A" using assms by induct auto }
  then show ?thesis by blast
qed

lemma segment_eq_orbit:
  assumes "y \<notin> orbit f x" shows "segment f x y = orbit f x"
proof (intro set_eqI iffI)
  fix z assume "z \<in> segment f x y" then show "z \<in> orbit f x" by (rule segmentD_orbit)
next
  fix z assume "z \<in> orbit f x" then show "z \<in> segment f x y"
    using assms by induct (auto intro: segment.intros orbit_eqI elim: orbit.cases)
qed

lemma funpow_in_funcset:
  assumes "x \<in> A" "f \<in> A \<rightarrow> A" shows "(f ^^ n) x \<in> A"
  using assms by (induct n) auto

lemma funpow_eq_funcset:
  assumes "x \<in> A" "f \<in> A \<rightarrow> A" "\<And>y. y \<in> A \<Longrightarrow> f y = g y"
  shows "(f ^^ n) x = (g ^^ n) x"
  using assms by (induct n) (auto, metis funpow_in_funcset)

lemma funpow_dist1_eq_funcset:
  assumes "y \<in> orbit f x" "x \<in> A" "f \<in> A \<rightarrow> A" "\<And>y. y \<in> A \<Longrightarrow> f y = g y"
  shows "funpow_dist1 f x y = funpow_dist1 g x y"
proof -
  have "y = (f ^^ funpow_dist1 f x y) x" by (metis assms(1) funpow_dist1_prop)
  also have "\<dots> = (g ^^ funpow_dist1 f x y) x" by (metis assms(2-) funpow_eq_funcset)
  finally have *: "y = (g ^^ funpow_dist1 f x y) x" .
  then have "(g ^^ funpow_dist1 g x y) x = y" by (metis funpow_dist1_prop1 zero_less_Suc)
  with * have gf: "funpow_dist1 g x y \<le> funpow_dist1 f x y"
    by (metis funpow_dist1_least not_le zero_less_Suc)

  have "(f ^^ funpow_dist1 g x y) x = y"
    using \<open>(g ^^ funpow_dist1 g x y) x = y\<close> by (metis assms(2-) funpow_eq_funcset)
  then have fg: "funpow_dist1 f x y \<le> funpow_dist1 g x y"
    using \<open>y = (f ^^ _) x\<close> by (metis funpow_dist1_least not_le zero_less_Suc)

  from gf fg show ?thesis by simp
qed

lemma segment_cong0:
  assumes "x \<in> A" "f \<in> A \<rightarrow> A" "\<And>y. y \<in> A \<Longrightarrow> f y = g y" shows "segment f x y = segment g x y"
proof (cases "y \<in> orbit f x")
  case True
  moreover
  from assms have "orbit f x = orbit g x" by (rule orbit_cong0)
  moreover
  have "(f ^^ n) x = (g ^^ n) x \<and> (f ^^ n) x \<in> A" for n
    by (induct n rule: nat.induct) (insert assms, auto)
  ultimately show ?thesis
    using True by (auto simp: segment_altdef funpow_dist1_eq_funcset[OF _ assms])
next
  case False
  moreover from assms have "orbit f x = orbit g x" by (rule orbit_cong0)
  ultimately show ?thesis by (simp add: segment_eq_orbit)
qed

lemma rev_ok_final:
  assumes wf_iG: "wf_digraph (mk_graph iG)"
  assumes rev: "is_map_rev_ok_inv iG iM rev_i rev_ok" "is_map_final iG rev_i rev_ok"
  shows "rev_ok \<longleftrightarrow> bidirected_digraph (mk_graph iG) (edge_rev (mk_map (mk_graph iG) iM))" (is "?L \<longleftrightarrow> ?R")
proof
  assume "rev_ok"
  interpret wf_digraph "mk_graph iG" by (rule wf_iG)
  have rev_inv_sep:
      "\<And>i. i < length (ig_edges iG) \<Longrightarrow> im_rev iM i < length (ig_edges iG)"
      "\<And>i. i < length (ig_edges iG) \<Longrightarrow> ig_edges iG ! im_rev iM i = prod.swap (ig_edges iG ! i)"
      "\<And>i. i < length (ig_edges iG) \<Longrightarrow> im_rev iM i \<noteq> i"
      "\<And>i. i < length (ig_edges iG) \<Longrightarrow> im_rev iM (im_rev iM i) = i"
    using rev \<open>rev_ok\<close> by (auto simp: is_map_rev_ok_inv_def is_map_final_def)
  moreover
  { fix i assume "i < length (ig_edges iG)"
    then have "ig_tail iG (im_rev iM i) = ig_head iG i"
      using rev_inv_sep(2) by (cases "ig_edges iG ! i") (auto simp: ig_head_def ig_tail_def)
  }
  ultimately show ?R
    using wf by unfold_locales (auto simp: mkg_simps arcs_mkg mkm_simps perm_restrict_def)
next
  assume ?R
  let ?rev = "perm_restrict (im_rev iM) (arcs (mk_graph iG))"
  interpret bidirected_digraph "mk_graph iG" "perm_restrict (im_rev iM) (arcs (mk_graph iG))"
    using \<open>?R\<close> by (simp add: mkm_simps mkg_simps)
  have "\<And>a. a \<in> arcs (mk_graph iG) \<Longrightarrow> ?rev a \<in> arcs (mk_graph iG)"
       "\<And>a. a \<in> arcs (mk_graph iG) \<Longrightarrow>
        arc_to_ends (mk_graph iG) (?rev a) = prod.swap (arc_to_ends (mk_graph iG) a)"
       "\<And>a. a \<in> arcs (mk_graph iG) \<Longrightarrow> ?rev a \<noteq> a"
       "\<And>a. a \<in> arcs (mk_graph iG) \<Longrightarrow> ?rev (?rev a) = a"
    by (auto simp: arev_dom)
  then show rev_ok
    using rev unfolding is_map_rev_ok_inv_def is_map_final_def
    by (simp add: perm_restrict_simps arcs_mkg arc_to_ends_mkg)
qed

locale is_map_postcondition0 =
  fixes iG iM rev_ok succ_i succ_ok
  assumes succ_perm: "is_map_succ_perm_inv iG iM succ_i succ_ok" "is_map_final iG succ_i succ_ok"
begin

  lemma succ_ok_tail_eq:
    "succ_ok \<Longrightarrow> i < length (ig_edges iG) \<Longrightarrow> ig_tail iG (im_succ iM i) = ig_tail iG i "
    using succ_perm unfolding is_map_succ_perm_inv_def is_map_final_def by auto

  lemma succ_ok_imp_pred:
    "succ_ok \<Longrightarrow> i < length (ig_edges iG) \<Longrightarrow> im_pred iM (im_succ iM i) = i"
    using succ_perm unfolding is_map_succ_perm_inv_def is_map_final_def by auto

  lemma succ_ok_imp_permutes:
    assumes "succ_ok"
    shows "edge_succ (mk_map (mk_graph iG) iM) permutes arcs (mk_graph iG)"
  proof -
    from assms have "\<forall>a \<in> arcs (mk_graph iG). edge_succ (mk_map (mk_graph iG) iM) a \<in> arcs (mk_graph iG)"
      using succ_perm unfolding is_map_succ_perm_inv_def is_map_final_def
      by (auto simp: mkg_simps mkm_simps arcs_mkg perm_restrict_def)
    with succ_ok_imp_pred[OF assms] show ?thesis
      by - (rule permutesI_finite_dom[where g="im_pred iM"], auto simp: perm_restrict_simps mkm_simps arcs_mkg)
  qed

  lemma es_A2A: "succ_ok \<Longrightarrow> edge_succ (mk_map (mk_graph iG) iM) \<in> arcs (mk_graph iG) \<rightarrow> arcs (mk_graph iG)"
    using succ_ok_imp_permutes by (auto dest: permutes_in_image)

  lemma im_succ_le_length: "succ_ok \<Longrightarrow> i < length (ig_edges iG) \<Longrightarrow> im_succ iM i < length (ig_edges iG)"
    using is_map_final_def is_map_succ_perm_inv_def succ_perm(1) succ_perm(2) by auto

  lemma orbit_es_eq_im:
    "succ_ok \<Longrightarrow> a \<in> arcs (mk_graph iG) \<Longrightarrow> orbit (edge_succ (mk_map (mk_graph iG) iM)) a = orbit (im_succ iM) a"
    using _ es_A2A es_eq_im by (rule orbit_cong0)

  lemma segment_es_eq_im:
    "succ_ok \<Longrightarrow> a \<in> arcs (mk_graph iG) \<Longrightarrow> segment (edge_succ (mk_map (mk_graph iG) iM)) a b = segment (im_succ iM) a b"
    using _ es_A2A es_eq_im by (rule segment_cong0)


  lemma in_orbit_im_succE:
    assumes "j \<in> orbit (im_succ iM) i" "succ_ok" "i < length (ig_edges iG)"
    obtains "ig_tail iG j = ig_tail iG i" "j < length (ig_edges iG)"
    using assms es_A2A by induct (force simp add: succ_ok_tail_eq es_eq_im arcs_mkg)+

  lemma self_in_orbit_im_succ:
    assumes "succ_ok" "i < length (ig_edges iG)" shows "i \<in> orbit (im_succ iM) i"
  proof -
    have "i \<in> orbit (edge_succ (mk_map (mk_graph iG) iM)) i"
      using assms succ_ok_imp_permutes
      by (intro permutation_self_in_orbit) (auto simp: permutation_permutes arcs_mkg)
    with assms show ?thesis by (simp add:orbit_es_eq_im arcs_mkg)
  qed

end

locale is_map_postcondition = is_map_postcondition0 +
  fixes so_i so_ok V A
  assumes rev: "rev_ok \<longleftrightarrow> bidirected_digraph (mk_graph iG) (edge_rev (mk_map (mk_graph iG) iM))"
  assumes succ_orbits: "is_map_succ_orbits_inv iG iM so_i so_ok V A" "succ_ok \<longrightarrow> is_map_final iG so_i so_ok"
begin

  lemma ok_imp_digraph:
    assumes rev_ok succ_ok so_ok
    shows "digraph_map (mk_graph iG) (mk_map (mk_graph iG) iM)"
  proof -
    interpret bidirected_digraph "mk_graph iG" "edge_rev (mk_map (mk_graph iG) iM)"
      using \<open>rev_ok\<close> by (simp add: rev)

    from \<open>succ_ok\<close> have perm: "edge_succ (mk_map (mk_graph iG) iM) permutes arcs (mk_graph iG)"
      by (simp add: succ_ok_imp_permutes)
    from \<open>succ_ok\<close> have ig_tail: "\<And>a. a \<in> arcs (mk_graph iG) \<Longrightarrow> ig_tail iG (im_succ iM a) = ig_tail iG a"
      by (simp_all add: succ_ok_tail_eq arcs_mkg)

    { fix v assume "v \<in> verts (mk_graph iG)" "out_arcs (mk_graph iG) v \<noteq> {}"
      then obtain a where a: "a \<in> arcs (mk_graph iG)" "tail (mk_graph iG) a = v" by auto metis
      then have "out_arcs (mk_graph iG) v = {b \<in> arcs (mk_graph iG). ig_tail iG a = ig_tail iG b}"
        by (auto simp: mkg_simps)
      also have "\<dots> \<subseteq> orbit (im_succ iM) a"
      proof -
        have "(\<forall>i<length (snd iG). \<forall>j<length (snd iG).
            ig_tail iG i = ig_tail iG j \<longrightarrow> j \<in> orbit (im_succ iM) i)"
          using \<open>succ_ok \<close>\<open>so_ok\<close> succ_orbits unfolding is_map_succ_orbits_inv_def is_map_final_def by metis
        with a show ?thesis by (auto simp: arcs_mkg)
      qed
      finally have "out_arcs (mk_graph iG) v \<subseteq> orbit (im_succ iM) a" .
      moreover
      have "orbit (im_succ iM) a \<subseteq> out_arcs (mk_graph iG) v"
      proof -
        { fix x assume "x \<in> orbit (im_succ iM) a" then have "tail (mk_graph iG) x = v"
            using a ig_tail
            apply induct
             apply (auto simp: mkg_simps intro: orbit.intros)
            by (metis \<open>succ_ok\<close> contra_subsetD orbit_es_eq_im permutes_orbit_subset perm)
        } moreover
        have "orbit (im_succ iM) a \<subseteq> arcs (mk_graph iG)"
          using _ a(1) apply (rule orbit_ss)
          using assms arcs_mkg is_map_final_def is_map_succ_perm_inv_def succ_perm(1) succ_perm(2) by auto
        ultimately
        show ?thesis by auto
      qed
      ultimately
      have "out_arcs (mk_graph iG) v = orbit (edge_succ (mk_map (mk_graph iG) iM)) a"
        using \<open>succ_ok\<close> a by (auto simp: orbit_es_eq_im)
      then
      have "cyclic_on (edge_succ (mk_map (mk_graph iG) iM)) (out_arcs (mk_graph iG) v)"
        unfolding cyclic_on_def using a by force
    }
    with perm show ?thesis
      using \<open>rev_ok\<close> by unfold_locales (auto simp: mkg_simps arcs_mkg)
  qed

  lemma digraph_imp_ok:
    assumes dm: "digraph_map (mk_graph iG) (mk_map (mk_graph iG) iM)"
    assumes pred: "\<And>i. i < length (ig_edges iG) \<Longrightarrow> im_pred iM (im_succ iM i) = i"
    obtains rev_ok succ_ok so_ok
  proof
    interpret dm: digraph_map "mk_graph iG" "mk_map (mk_graph iG) iM" by (fact dm)

    show rev_ok unfolding rev by unfold_locales

    show succ_ok
    proof -
      { fix i assume "i \<in> arcs (mk_graph iG)"
        then have
            "edge_succ (mk_map (mk_graph iG) iM) i \<in> arcs (mk_graph iG)"
            "tail (mk_graph iG) (edge_succ (mk_map (mk_graph iG) iM) i) = tail (mk_graph iG) i"
          by auto
        then have
            "im_succ iM i < length (snd iG)"
            "ig_tail iG (im_succ iM i) = ig_tail iG i"
          unfolding es_eq_im[OF \<open>i \<in> arcs _\<close>] by (auto simp: arcs_mkg mkg_simps)
      }
      then have "(\<forall>i<length (ig_edges iG).
        im_succ iM i < length (snd iG) \<and>
        ig_tail iG (im_succ iM i) = ig_tail iG i \<and> im_pred iM (im_succ iM i) = i)"
        using pred by (auto simp: arcs_mkg es_eq_im)
      with succ_perm show ?thesis
        unfolding is_map_succ_perm_inv_def is_map_final_def by simp
    qed

    show so_ok
    proof -
      { fix i j assume "i < length (ig_edges iG)" "j < length (ig_edges iG)" "ig_tail iG i = ig_tail iG j"
        then have A: "i \<in> arcs (mk_graph iG)" "j \<in> arcs (mk_graph iG)" "tail (mk_graph iG) i = tail (mk_graph iG) j"
          by (auto simp: mkg_simps arcs_mkg)
        then have "cyclic_on (edge_succ (mk_map (mk_graph iG) iM)) (out_arcs (mk_graph iG) (tail (mk_graph iG) i))"
          by (auto intro!: dm.edge_succ_cyclic)
        then have "orbit (edge_succ (mk_map (mk_graph iG) iM)) i = out_arcs (mk_graph iG) (ig_tail iG i)"
          by (simp add: \<open>i \<in> arcs (mk_graph iG)\<close> mkg_simps orbit_cyclic_eq3)
        then have "j \<in> orbit (edge_succ (mk_map (mk_graph iG) iM)) i" using A by (simp add: mkg_simps)
        also have "orbit (edge_succ (mk_map (mk_graph iG) iM)) i = orbit (im_succ iM) i"
          using \<open>i \<in> arcs _\<close>
          by (rule orbit_cong0) (fastforce, simp add: es_eq_im)
        finally have "j \<in> orbit (im_succ iM) i" .
      }
      then show ?thesis
        using succ_orbits unfolding is_map_succ_orbits_inv_def is_map_final_def
        by safe (simp_all only: \<open>succ_ok\<close> simp_thms)
    qed
  qed

end

lemma all_less_Suc_eq: "(\<forall>x < Suc n. P x) \<longleftrightarrow> (\<forall>x < n. P x) \<and> P n"
  by (auto elim: less_SucE)

lemma in_orbit_imp_in_segment:
  assumes "y \<in> orbit f x" "x \<noteq> y" "bij f" shows "y \<in> segment f x (f y)"
  using assms
proof induct
  case base then show ?case by (auto intro: segment.intros simp: bij_iff)
next
  case (step y)
  show ?case
  proof (cases "x = y")
    case True then show ?thesis using step by (auto intro: segment.intros simp: bij_iff)
  next
    case False
    with step have "f y \<noteq> f (f y)" by (metis bij_is_inj inv_f_f not_in_segment2)
    then show ?thesis using step False
      by (auto intro: segment.intros segment_step_2 bij_is_inj)
  qed
qed


lemma ovalidNF_is_map: "
  ovalidNF (\<lambda>s. distinct (ig_verts iG) \<and> wf_digraph (mk_graph iG))
    (is_map iG iM)
  (\<lambda>r s. r \<longleftrightarrow> digraph_map (mk_graph iG) (mk_map (mk_graph iG) iM) \<and> (\<forall>i < length (ig_edges iG). im_pred iM (im_succ iM i) = i))
"
  unfolding is_map_def
  apply (rewrite
    in "oreturn (length (ig_edges iG)) |>> (\<lambda>ecnt. \<hole>)"
    to "owhile_inv _ _ _
      (\<lambda>(i, ok) s. is_map_rev_ok_inv iG iM i ok
        \<and> i \<le> ecnt \<and> wf_digraph (mk_graph iG))
      (measure (\<lambda>(i, ok). ecnt - i))
    " owhile_inv_def[symmetric] )
  apply (rewrite
    in "owhile_inv _ _ _ _ _ |>> (\<lambda>(rev_i, rev_ok). \<hole>)"
    in "oreturn (length (ig_edges iG)) |>> (\<lambda>ecnt. \<hole>)"
    to "owhile_inv _ _ _
      (\<lambda>(i, ok) s. is_map_succ_perm_inv iG iM i ok
        \<and> rev_ok = bidirected_digraph (mk_graph iG) (edge_rev (mk_map (mk_graph iG) iM))
        \<and> i \<le> ecnt \<and> wf_digraph (mk_graph iG))
      (measure (\<lambda>(i, ok). ecnt - i))
    " owhile_inv_def[symmetric] )
  apply (rewrite
    in "owhile_inv _ _ _ _ _ |>> (\<lambda>(succ_i, succ_ok). \<hole>)"
    in "owhile_inv _ _ _ _ _ |>> (\<lambda>(rev_i, rev_ok). \<hole>)"
    in "oreturn (length (ig_edges iG)) |>> (\<lambda>ecnt. \<hole>)"
    to "owhile_inv _ _ _
      (\<lambda>(i, ok, V, A) s. is_map_succ_orbits_inv iG iM i ok V A
        \<and> rev_ok = bidirected_digraph (mk_graph iG) (edge_rev (mk_map (mk_graph iG) iM))
        \<and> is_map_succ_perm_inv iG iM succ_i succ_ok \<and> is_map_final iG succ_i succ_ok
        \<and> i \<le> ecnt \<and> wf_digraph (mk_graph iG))
      (measure (\<lambda>(i, ok, V, A). ecnt - i))
    " owhile_inv_def[symmetric] )
  apply (rewrite
    in "owhile_inv _ (\<lambda>(i, ok, V, A). \<hole>) _ _ _"
    in "owhile_inv _ _ _ _ _ |>> (\<lambda>(succ_i, succ_ok). \<hole>)"
    in "owhile_inv _ _ _ _ _ |>> (\<lambda>(rev_i, rev_ok). \<hole>)"
    in "oreturn (length (ig_edges iG)) |>> (\<lambda>ecnt. \<hole>)"
    to "owhile_inv _ _ _
      (\<lambda>(A', j) s. is_map_succ_orbits_inner_inv iG iM i j A'
        \<and> ig_tail iG i \<notin> V \<and> succ_ok \<and> ok \<and> is_map_succ_orbits_inv iG iM i ok V A
        \<and> rev_ok = bidirected_digraph (mk_graph iG) (edge_rev (mk_map (mk_graph iG) iM))
        \<and> is_map_succ_perm_inv iG iM succ_i succ_ok \<and> is_map_final iG succ_i succ_ok
        \<and> i < ecnt \<and> wf_digraph (mk_graph iG))
      (measure (\<lambda>(A',j). length (ig_edges iG) - card A'))
    " owhile_inv_def[symmetric] )
proof vcg_casify
  let ?es = "edge_succ (mk_map (mk_graph iG) iM)"

  { case weaken then show ?case by (auto simp: is_map_rev_ok_inv_def)
  }
  { case (while i ok)
    { case invariant
      case weaken then show ?case by (auto simp: is_map_rev_ok_inv_def elim: less_SucE)
    }
    { case wf show ?case by auto
    }
    { case postcondition
      then have "ok \<longleftrightarrow> bidirected_digraph (mk_graph iG) (edge_rev (mk_map (mk_graph iG) iM))"
        by (intro rev_ok_final) (auto simp: is_map_final_def)
      with postcondition show ?case by (auto simp: is_map_succ_perm_inv_def)
    }
  }
  case (bind _ rev_ok)
  { case (while i ok)
    { case invariant case weaken
      then show ?case by (auto simp: is_map_succ_perm_inv_def elim: less_SucE)
    }
    { case wf show ?case by auto
    }
    { case postcondition
      then show ?case by (auto simp: is_map_final_def is_map_succ_orbits_inv_def)
    }
  }
  case (bind succ_i succ_ok)
  { case (while i ok V A)
    { case invariant
      { case weaken
        then interpret pc0: is_map_postcondition0 iG iM rev_ok succ_i succ_ok
          by unfold_locales auto
        from weaken.loop_cond have "i < length (ig_edges iG)" succ_ok ok by auto
        with weaken.loop_inv have
            V: "V = {ig_tail iG k |k. k < i}" and
            A: "A = (\<Union> k<i. orbit (im_succ iM) k)"
          by (simp_all add: is_map_succ_orbits_inv_def)
        show ?case
        proof branch_casify
          case "then" case g
          have V': "V = {ig_tail iG ia |ia. ia < (if i \<in> A then Suc i else Suc i - 1)}"
            using g \<open>V = _\<close> by (auto elim: less_SucE)

          have "is_map_succ_orbits_inv iG iM (Suc i) (i \<in> A) V A"
          proof (cases "i \<in> A")
            case True
            obtain j where j: "j < i" "i \<in> orbit (im_succ iM) j"
              using True \<open>A = _\<close> by auto
            have i_in_less_i: "\<exists>x\<in>{..<i}. i \<in> orbit (im_succ iM) x"
              using True \<open>A = _\<close> by auto
            have A': "A = (\<Union> i<if True then Suc i else Suc i - 1. orbit (im_succ iM) i)"
              using True unfolding \<open>A = _\<close> by (auto 4 3 intro: orbit_trans elim: less_SucE)

            have X: "\<forall>k<i. \<forall>l<i. ig_tail iG k = ig_tail iG l \<longrightarrow> l \<in> orbit (im_succ iM) k"
              using weaken unfolding is_map_succ_orbits_inv_def by metis
            moreover
            { fix j assume j: "j < i" "ig_tail iG j = ig_tail iG i"
              from i_in_less_i obtain k where k: "k < i" "i \<in> orbit (im_succ iM) k" by auto
              then have "ig_tail iG k = ig_tail iG i"
                using \<open>succ_ok\<close> \<open>i < _\<close> by (auto elim: pc0.in_orbit_im_succE)
              then have "k \<in> orbit (im_succ iM) j"
                using j \<open>ig_tail iG k = _\<close> k X by auto
              then have "i \<in> orbit (im_succ iM) j" using k by (auto intro: orbit_trans)
            }
            ultimately
            have "\<forall>k<Suc i. \<forall>l<Suc i. ig_tail iG k = ig_tail iG l \<longrightarrow> l \<in> orbit (im_succ iM) k"
              unfolding all_less_Suc_eq using \<open>i < _\<close> \<open>succ_ok\<close>
              by (auto intro: orbit_swap pc0.self_in_orbit_im_succ)
            with True show ?thesis
              by (simp only: A' V' simp_thms is_map_succ_orbits_inv_def)
          next
            case False

            from V g obtain j where j: "j < i" "ig_tail iG j = ig_tail iG i" by auto
            with False show ?thesis
              by (auto 0 3 simp: is_map_succ_orbits_inv_def V' A intro: exI[where x=j] exI[where x=i])
          qed
          then show ?case using weaken by auto
        next
          case "else" case g
          have "is_map_succ_orbits_inner_inv iG iM i i {}"
            unfolding is_map_succ_orbits_inner_inv_def
            using \<open>succ_ok\<close> \<open>i < _\<close> by (auto simp: pc0.self_in_orbit_im_succ)
          with g weaken show ?case by blast
        qed
      }
      { case "if" case else case (while A' i')
        { case invariant case weaken
          then interpret pc0: is_map_postcondition0 iG iM rev_ok succ_i succ_ok
            by unfold_locales auto
          have "succ_ok" "i < length (ig_edges iG)" "i' \<in> orbit (im_succ iM) i"
            using weaken by (auto simp: is_map_succ_orbits_inner_inv_def)
          have "i' < length (ig_edges iG)"
            using \<open>i' \<in> _\<close> \<open>succ_ok\<close> \<open>i < _\<close> by (rule pc0.in_orbit_im_succE)

          { assume "i' \<in> orbit (im_succ iM) i" "i \<noteq> i'"
            then have "i' \<in> orbit (?es) i"
              by (subst pc0.orbit_es_eq_im) (auto simp add: \<open>succ_ok\<close> \<open>i < _\<close> arcs_mkg)
            then have "i' \<in> segment (?es) i (?es i')"
              using \<open>i \<noteq> i'\<close> pc0.succ_ok_imp_permutes \<open>succ_ok \<close>
              by (intro in_orbit_imp_in_segment) (auto simp: permutes_conv_has_dom)
            then have "i' \<in> segment (im_succ iM) i (im_succ iM i')"
              by (subst pc0.segment_es_eq_im[symmetric] es_eq_im[symmetric];
                  auto simp add: \<open>succ_ok\<close> \<open>i < _\<close> \<open>i' < _\<close> arcs_mkg)+
          } note X = this

          { fix x assume "x \<in> segment (im_succ iM) i i'" "i \<noteq> i'"
            then have "x \<in> segment (?es) i i'"
              by (subst pc0.segment_es_eq_im) (auto simp add: \<open>succ_ok\<close> \<open>i < _\<close> \<open>i' < _\<close> arcs_mkg)
            then have "x \<in> segment (?es) i (?es i')"
              using \<open>i \<noteq> i'\<close> pc0.succ_ok_imp_permutes \<open>succ_ok \<close>
              by (auto simp: permutes_conv_has_dom bij_is_inj intro: segment_step_2)
            then have "x \<in> segment (im_succ iM) i (im_succ iM i')"
              by (subst pc0.segment_es_eq_im[symmetric] es_eq_im[symmetric];
                  auto simp add: \<open>succ_ok\<close> \<open>i < _\<close> \<open>i' < _\<close> arcs_mkg)+
          } note Y = this

          have Z: "is_map_succ_orbits_inner_inv iG iM i (im_succ iM i') (insert i' A')"
            using weaken unfolding is_map_succ_orbits_inner_inv_def
            by (auto dest: segment_step_2D X Y simp: orbit.intros segment1_empty split: if_splits)

          have "A' \<subseteq> orbit (im_succ iM) i"
            using weaken unfolding is_map_succ_orbits_inner_inv_def
            by (auto simp: pc0.self_in_orbit_im_succ dest: segmentD_orbit split: if_splits)
          also have "\<dots> \<subseteq> arcs (mk_graph iG)"
            by (rule orbit_ss) (auto simp: arcs_mkg pc0.im_succ_le_length \<open>succ_ok\<close> \<open>i < _\<close>)
          finally have "card A' < card (arcs (mk_graph iG))" "finite A'"
            using \<open>i' \<notin> A'\<close>  \<open>i' < _\<close>
            by - (intro psubset_card_mono, auto simp: arcs_mkg intro: finite_subset)
          then have "card A' < length (ig_edges iG)" by (simp add: arcs_mkg)
          show ?case
            using weaken Z \<open>card A' < length _\<close> by (auto simp: card_insert_if \<open>finite A'\<close>)
        }
        { case wf show ?case by simp
        }
        { case postcondition
          then interpret pc0: is_map_postcondition0 iG iM rev_ok succ_i succ_ok
            by unfold_locales auto
          from postcondition have "ok" "succ_ok" "i < length (ig_edges iG)" by simp_all

          from postcondition
          have "i' \<in> A'"
              "A' = (if i = i' \<and> i \<notin> A' then {} else {i} \<union> segment (im_succ iM) i i')"
              "i' \<in> orbit (im_succ iM) i"
              "ig_tail iG i \<notin> V"
            by (simp_all add: is_map_succ_orbits_inner_inv_def)
          moreover
          then have "i = i'" by (simp split: if_splits add: not_in_segment2)
          ultimately
          have "A' = {i} \<union> segment (im_succ iM) i i" by simp
          also have "segment (im_succ iM) i i = segment ?es i i"
            by (auto simp: pc0.segment_es_eq_im \<open>succ_ok\<close> \<open>i < _\<close> arcs_mkg)
          also have "\<dots> = orbit ?es i - {i}"
            using pc0.succ_ok_imp_permutes \<open>succ_ok\<close>
            by (auto simp: permutation_permutes arcs_mkg intro!: segment_x_x_eq)
          also have "\<dots> = orbit (im_succ iM) i - {i}"
            by (auto simp: pc0.orbit_es_eq_im \<open>succ_ok\<close> \<open>i < _\<close> arcs_mkg)
          finally
          have A': "A' = orbit (im_succ iM) i"
            using \<open>i < _\<close> \<open>succ_ok\<close> by (auto simp: pc0.self_in_orbit_im_succ)

          from postcondition
          have "A = (\<Union>k<i. orbit (im_succ iM) k)"
            unfolding is_map_succ_orbits_inner_inv_def by (simp add: is_map_succ_orbits_inv_def)
          have "A \<union> A' = (\<Union>k<Suc i. orbit (im_succ iM) k)"
            unfolding A' \<open>A = _\<close> by (auto 2 3 elim: less_SucE)

          from postcondition have "V = {ig_tail iG ia |ia. ia < i}"
            by (auto simp: \<open>ok\<close> is_map_succ_orbits_inv_def)
          then have V': "insert (ig_tail iG i') V = {ig_tail iG ia |ia. ia < Suc i}"
            by (auto simp add: \<open>i = i'\<close> elim: less_SucE)

          have *: "\<And>k. k < i \<Longrightarrow> ig_tail iG k \<noteq> ig_tail iG i"
            using \<open>V = _\<close> \<open>ig_tail iG i \<notin> V\<close> by auto

          from postcondition have "(\<forall>k<i. \<forall>l<i. ig_tail iG k = ig_tail iG l \<longrightarrow> l \<in> orbit (im_succ iM) k)"
            by (simp add: is_map_succ_orbits_inv_def \<open>ok\<close>)
          then have X: "(\<forall>k<Suc i. \<forall>l<Suc i. ig_tail iG k = ig_tail iG l \<longrightarrow> l \<in> orbit (im_succ iM) k)"
            by (auto simp add: all_less_Suc_eq pc0.self_in_orbit_im_succ \<open>succ_ok\<close> \<open>i < _\<close> dest: *)

          have "is_map_succ_orbits_inv iG iM (i + 1) True (insert (ig_tail iG i') V) (A \<union> A')"
            unfolding is_map_succ_orbits_inv_def by (simp add: \<open>A \<union> A' = _\<close> V' X)
          then show ?case
            using postcondition \<open>i < _\<close> by auto
        }
      }
    }
    { case wf show ?case by auto
    }
    { case postcondition
      interpret pc: is_map_postcondition iG iM rev_ok succ_i succ_ok i ok V A
        using postcondition by unfold_locales (auto simp: is_map_final_def)

      show ?case (is "?L = ?R")
        by (auto simp add: pc.ok_imp_digraph dest: pc.succ_ok_imp_pred elim: pc.digraph_imp_ok)
    }
  }
qed

declare ovalidNF_is_map[THEN ovalidNF_wp, THEN trivial_label, vcg_l]


subsubsection \<open>@{term isolated_nodes}\<close>

definition "inv_isolated_nodes s iG vcnt ecnt \<equiv>
  vcnt = length (ig_verts iG)
  \<and> ecnt = length (ig_edges iG)
  \<and> distinct (ig_verts iG)
  \<and> sym_digraph (mk_graph iG)
  "

definition "inv_isolated_nodes_outer iG i nz \<equiv>
  nz = card (pre_digraph.isolated_verts (mk_graph iG) \<inter> set (take i (ig_verts iG)))"

definition "inv_isolated_nodes_inner iG v j \<equiv>
  \<forall>k < j. v \<noteq> ig_tail iG k \<and> v \<noteq> ig_head iG k"

lemma (in sym_digraph) in_arcs_empty_iff:
  "in_arcs G v = {} \<longleftrightarrow> out_arcs G v = {}"
  by (auto simp: out_arcs_def in_arcs_def)
     (metis graph_symmetric in_arcs_imp_in_arcs_ends reachableE)+

lemma take_nth_distinct:
  "\<lbrakk>distinct xs; n < length xs; xs ! n \<in> set (take n xs)\<rbrakk> \<Longrightarrow> False"
  by (fastforce simp: distinct_conv_nth in_set_conv_nth)

lemma ovalidNF_isolated_nodes: "
  ovalidNF (\<lambda>s. distinct (ig_verts iG) \<and> sym_digraph (mk_graph iG))
    (isolated_nodes iG)
  (\<lambda>r s. r = (card (pre_digraph.isolated_verts (mk_graph iG))))"
  unfolding isolated_nodes_def
  apply (rewrite
    in "oreturn (length (ig_verts iG)) |>> (\<lambda>vcnt. \<hole>)"
    in "oreturn (length (ig_edges iG)) |>> (\<lambda>ecnt. \<hole>)"
    to "owhile_inv _ _ _
      (\<lambda>(i, nz) s. inv_isolated_nodes s iG vcnt ecnt
            \<and> inv_isolated_nodes_outer iG i nz
            \<and> i \<le> vcnt)
      (measure (\<lambda>(i, nz). vcnt - i))
    " owhile_inv_def[symmetric] )
  apply (rewrite
    in "oreturn (fst iG ! i) |>> (\<lambda>v. \<hole>)"
    in "owhile_inv _ (\<lambda>(i, nz). \<hole>)"
    in "oreturn (length (ig_verts iG)) |>> (\<lambda>vcnt. \<hole>)"
    in "oreturn (length (ig_edges iG)) |>> (\<lambda>ecnt. \<hole>)"
    to "owhile_inv _ _ _
      (\<lambda>(j, ret) s. inv_isolated_nodes s iG vcnt ecnt
           \<and> inv_isolated_nodes_inner iG v j
           \<and> inv_isolated_nodes_outer iG i nz
           \<and> v = ig_verts iG ! i
           \<and> ret = (j < ecnt \<and> ig_tail iG j \<noteq> v \<and> ig_head iG j \<noteq> v)
           \<and> i < vcnt
           \<and> j \<le> ecnt)
      (measure (\<lambda>(j, ret). ecnt - j))
    " owhile_inv_def[symmetric])
proof vcg_casify
  case (weaken s)
  then show ?case
    by (auto simp: inv_isolated_nodes_def inv_isolated_nodes_outer_def)
next
  case (while i nz)
  { case invariant
    { case (weaken s')
      then show ?case unfolding BRANCH_def by (auto simp: inv_isolated_nodes_inner_def)
    next
      case bind
      case bind
      case (while j cond)
      { case invariant
        { case weaken
          show ?case
          proof branch_casify
            case "else" case "else" case g
            with weaken have "length (ig_edges iG) = j + 1" by linarith
            with weaken show ?case
              by (auto simp: inv_isolated_nodes_inner_def elim: less_SucE)
          qed (insert weaken, auto simp: inv_isolated_nodes_inner_def elim: less_SucE)
        }
      next
        case wf show ?case by auto
      next
        case postcondition
        interpret G: sym_digraph "mk_graph iG" using postcondition by (simp add: inv_isolated_nodes_def)

        have ?var using postcondition by auto

        let ?v = "ig_verts iG ! i"

        { assume A: "j = length (snd iG)"
          have "?v \<in> pre_digraph.isolated_verts (mk_graph iG)"
            using A postcondition by (auto simp: pre_digraph.isolated_verts_def mkg_simps inv_isolated_nodes_inner_def arcs_mkg)

          have "distinct (ig_verts iG)" "?v = ig_verts iG ! i" "i < length (ig_verts iG)"
            using postcondition by (auto simp: inv_isolated_nodes_def)
          then have "?v \<notin> set (take i (ig_verts iG))"
            by (metis take_nth_distinct)

          have "Suc (card (pre_digraph.isolated_verts (mk_graph iG) \<inter> set (take i (fst iG))))
              = card (insert ?v (pre_digraph.isolated_verts (mk_graph iG) \<inter> set (take i (fst iG))))" (is "_ = card ?S")
            using \<open>?v \<notin> _\<close> by simp
          also have "?S = pre_digraph.isolated_verts (mk_graph iG) \<inter> set (take (Suc i) (fst iG))"
            using \<open>?v \<in> _\<close> \<open>i < _\<close> \<open>?v = _\<close> by (auto simp: take_Suc_conv_app_nth)
          finally
          have "inv_isolated_nodes_outer iG (Suc i) (Suc nz)"
            using postcondition by (auto simp: inv_isolated_nodes_outer_def)
        }
        moreover
        { assume A: "j \<noteq> length (snd iG)"

          then have *: "j \<in> (out_arcs (mk_graph iG) ?v \<union> in_arcs (mk_graph iG) ?v)"
            using postcondition by (auto simp: arcs_mkg mkg_simps ig_tail_def ig_head_def)
          then have "out_arcs (mk_graph iG) ?v \<noteq> {}"
            by (auto simp del: in_in_arcs_conv in_out_arcs_conv)
               (auto simp: G.in_arcs_empty_iff[symmetric])
          then have "?v \<notin> pre_digraph.isolated_verts (mk_graph iG)"
            by (auto simp: pre_digraph.isolated_verts_def)
          then have "inv_isolated_nodes_outer iG (Suc i) nz"
            using postcondition by (auto simp: inv_isolated_nodes_outer_def take_Suc_conv_app_nth)
        }
        ultimately
        have ?inv using postcondition by auto
        from \<open>?var\<close> \<open>?inv\<close> show ?case by blast
      }
    }
  next
    case wf show ?case by auto
  next
    case postcondition
    have "pre_digraph.isolated_verts (mk_graph iG) \<inter> set (fst iG) = pre_digraph.isolated_verts (mk_graph iG)"
      by (auto simp: pre_digraph.isolated_verts_def mkg_simps)
    with postcondition show ?case
      by (auto simp: inv_isolated_nodes_def inv_isolated_nodes_outer_def)
  }
qed

declare ovalidNF_isolated_nodes[THEN ovalidNF_wp, THEN trivial_label, vcg_l]



subsubsection \<open>@{term face_cycles}\<close>

definition "inv_face_cycles s iG iM ecnt \<equiv>
  ecnt = length (ig_edges iG)
  \<and> digraph_map (mk_graph iG) iM
  "

definition fcs_upto :: "nat pre_map \<Rightarrow> nat \<Rightarrow> nat set set" where
  "fcs_upto iM i \<equiv> {pre_digraph_map.face_cycle_set iM k | k. k < i}"

definition "inv_face_cycles_outer s iG iM i c edge_info \<equiv>
  let fcs = fcs_upto iM i in
  c = card fcs
  \<and> (\<forall>k < length (ig_edges iG). k \<in> edge_info \<longleftrightarrow> k \<in> \<Union>fcs)"

definition "inv_face_cycles_inner s iG iM i j c edge_info \<equiv>
  j \<in> pre_digraph_map.face_cycle_set iM i
  \<and> c = card (fcs_upto iM i)
  \<and> i \<notin> \<Union>(fcs_upto iM i)
  \<and> (\<forall>k < length (ig_edges iG). k \<in> edge_info \<longleftrightarrow>
    (k \<in> \<Union>(fcs_upto iM i)
    \<or> (\<exists>l < funpow_dist1 (pre_digraph_map.face_cycle_succ iM) i j. (pre_digraph_map.face_cycle_succ iM ^^ l) i = k)))"

lemma finite_fcs_upto: "finite (fcs_upto iM i)"
  by (auto simp: fcs_upto_def)

lemma card_orbit_eq_funpow_dist1:
  assumes "x \<in> orbit f x" shows "card (orbit f x) = funpow_dist1 f x x"
proof -
  have "card (orbit f x) = card ((\<lambda>n. (f ^^ n) x) ` {0..<funpow_dist1 f x x})"
    using assms by (simp only: orbit_conv_funpow_dist1[symmetric])
  also have "\<dots> = card {0..<funpow_dist1 f x x}"
    using assms by (intro card_image inj_on_funpow_dist1)
  finally show ?thesis by simp
qed

lemma funpow_dist1_le:
  assumes "y \<in> orbit f x" "x \<in> orbit f x"
  shows "funpow_dist1 f x y \<le> funpow_dist1 f x x"
    using assms by (intro funpow_dist1_le_self funpow_dist1_prop) simp_all

lemma funpow_dist1_le_card:
  assumes "y \<in> orbit f x" "x \<in> orbit f x"
  shows "funpow_dist1 f x y \<le> card (orbit f x)"
  using funpow_dist1_le[OF assms] using assms
  by (simp add: card_orbit_eq_funpow_dist1)

lemma (in digraph_map) funpow_dist1_le_card_fcs:
  assumes "b \<in> face_cycle_set a"
  shows "funpow_dist1 face_cycle_succ a b \<le> card (face_cycle_set a)"
  by (metis assms face_cycle_set_def face_cycle_set_self funpow_dist1_le_card)

lemma funpow_dist1_f_eq:
  assumes "b \<in> orbit f a" "a \<in> orbit f a" "a \<noteq> b"
  shows "funpow_dist1 f a (f b) = Suc (funpow_dist1 f a b)"
proof -
  have f_inj: "inj_on (\<lambda>n. (f ^^ n) a) {0..<funpow_dist1 f a a}"
    by (rule inj_on_funpow_dist1) (rule assms)
  have "funpow_dist1 f a b \<le> funpow_dist1 f a a"
    using assms by (intro funpow_dist1_le)
  moreover
  have "funpow_dist1 f a b \<noteq> funpow_dist1 f a a"
    by (metis assms funpow_dist1_prop)
  ultimately
  have f_less: "funpow_dist1 f a b < funpow_dist1 f a a" by simp

  have f_Suc_eq: "(f ^^ Suc (funpow_dist1 f a b)) a = f b"
    using assms by (metis funpow.simps(2) o_apply funpow_dist1_prop)
  show ?thesis
  proof (cases "f b = a")
    case True
    then show ?thesis
      by (metis Suc_lessI f_Suc_eq f_less assms(2) funpow.simps(1) funpow_neq_less_funpow_dist1 id_apply old.nat.distinct(1) zero_less_Suc)
  next
    case False
    then have *: "Suc (funpow_dist1 f a b) < funpow_dist1 f a a"
      using f_Suc_eq by (metis assms(2) f_less funpow_dist1_prop le_less_Suc_eq less_Suc_eq_le not_less_eq)
    from f_inj have **: "\<And>n. n < funpow_dist1 f a a \<Longrightarrow> n \<noteq> Suc (funpow_dist1 f a b) \<Longrightarrow> (f ^^ n) a \<noteq> f b"
      using f_Suc_eq by (auto dest!: inj_onD) (metis * assms(2) f_Suc_eq funpow_neq_less_funpow_dist1)
    show ?thesis
    proof (rule ccontr)
      assume A: "\<not>?thesis"
      have "(f ^^ (funpow_dist1 f a (f b))) a  = f b"
        using assms by (intro funpow_dist1_prop) (simp add: orbit.intros)
      with A ** have "funpow_dist1 f a a \<le> (funpow_dist1 f a (f b))"
        by (metis less_Suc_eq_le not_less_eq)
      then have "Suc (funpow_dist1 f a b) < (funpow_dist1 f a (f b))" using * by linarith
      then have "(f ^^ Suc (funpow_dist1 f a b)) a \<noteq> f b"
        by (intro funpow_dist1_least) simp_all
      then show False using f_Suc_eq by simp
    qed
  qed
qed

lemma (in -) funpow_dist1_less_f:
  assumes "b \<in> orbit f a" "a \<in> orbit f a" "a \<noteq> b"
  shows "funpow_dist1 f a b < funpow_dist1 f a (f b)"
  using assms by (simp add: funpow_dist1_f_eq)

lemma ovalidNF_face_cycles: "
  ovalidNF (\<lambda>s. digraph_map (mk_graph iG) iM)
    (face_cycles iG iM)
  (\<lambda>r s. r = card (pre_digraph_map.face_cycle_sets (mk_graph iG) iM))
"
  unfolding face_cycles_def
  apply (rewrite
    in "oreturn (length (ig_edges iG)) |>> (\<lambda>ecnt. \<hole>)"
    to "owhile_inv _ _ _
          (\<lambda>(edge_info, c, i) s. inv_face_cycles s iG iM ecnt
            \<and> inv_face_cycles_outer s iG iM i c edge_info
            \<and> i \<le> ecnt)
          (measure (\<lambda>(edge_info, c, i). ecnt - i))
      " owhile_inv_def[symmetric]
  )
  apply (rewrite
    in "owhile_inv _ (\<lambda>(_, c, i). \<hole>)"
    in "oreturn (length (ig_edges iG)) |>> (\<lambda>ecnt. \<hole>)"
    to "owhile_inv _ _ _
          (\<lambda>(edge_info, j) s. inv_face_cycles s iG iM ecnt
            \<and> inv_face_cycles_inner s iG iM i j c edge_info
            \<and> i < ecnt)
          (measure (\<lambda>(edge_info, j). card (pre_digraph_map.face_cycle_set iM i) - funpow_dist1 (pre_digraph_map.face_cycle_succ iM) i j))
      " owhile_inv_def[symmetric]
  )
proof vcg_casify
  { case (weaken s)
    then show ?case by (auto simp add: inv_face_cycles_def inv_face_cycles_outer_def fcs_upto_def)
  }
  { case (while edge_info c i)
    { case (postcondition s)
      moreover have "fcs_upto iM (length (ig_edges iG))
          = pre_digraph_map.face_cycle_sets (mk_graph iG) iM"
        by (auto simp: pre_digraph_map.face_cycle_sets_def arcs_mkg fcs_upto_def)
      ultimately show ?case by (auto simp: inv_face_cycles_outer_def Let_def)
    }
    { case (invariant s)
      { case (weaken s')
        interpret G: digraph_map "mk_graph iG" iM
          using weaken by (auto simp: inv_face_cycles_def)
        show ?case
        proof branch_casify
          case else case g
          then have "G.face_cycle_set i \<in> {G.face_cycle_set k |k. k < i}"
            using weaken by (auto simp: inv_face_cycles_outer_def fcs_upto_def dest: G.face_cycle_eq)
          then have "{G.face_cycle_set k |k. k < Suc i} = {G.face_cycle_set k |k. k < i}"
            by (auto elim: less_SucE)
          then have "inv_face_cycles_outer s' iG iM (i + 1) c edge_info"
            using weaken unfolding inv_face_cycles_outer_def by (auto simp: fcs_upto_def)
          then have ?inv using weaken by auto
          then show ?case using weaken by auto
        next
          case "then" case g
          have fd1_triv: "\<And>f x. funpow_dist1 f x (f x) = 1"
            by (simp add: funpow_dist_0)
          have fcs_in: "G.face_cycle_succ i \<in> G.face_cycle_set i"
            by (simp add: G.face_cycle_succ_inI)

          have i_not_in_fcs: "i \<notin> \<Union>(fcs_upto iM i)"
            using g weaken
            by (auto simp: inv_face_cycles_outer_def fcs_upto_def)

          from weaken show ?case
            unfolding inv_face_cycles_inner_def inv_face_cycles_outer_def
            using i_not_in_fcs by (auto simp: fd1_triv fcs_in fcs_upto_def)
        qed
      }
      { case "if" case "then"
        { case (while edge_info j)
          { case (postcondition s')

            interpret G: digraph_map "mk_graph iG" iM
              using postcondition by (auto simp: inv_face_cycles_def)

            have ?var using postcondition by auto

            have fu_Suc: "fcs_upto iM (Suc j) = fcs_upto iM j \<union> {G.face_cycle_set j}"
              by (auto simp: fcs_upto_def elim: less_SucE)
            moreover
            have "G.face_cycle_set j \<notin> fcs_upto iM j" "c  = card (fcs_upto iM j)"
              using postcondition by (auto simp: inv_face_cycles_inner_def)
            ultimately
            have "Suc c = card (fcs_upto iM (Suc j))" by (simp add: finite_fcs_upto)

            have *: "\<forall>k<length (snd iG). k \<in> edge_info \<longleftrightarrow> (\<exists>x\<in>fcs_upto iM (Suc j). k \<in> x)"
            proof -
              have *: "j \<in> orbit G.face_cycle_succ j"
                by (simp add: G.face_cycle_set_def[symmetric])
              have "\<And>k. (\<exists>l<funpow_dist1 G.face_cycle_succ j j. (G.face_cycle_succ ^^ l) j = k) \<longleftrightarrow> (k \<in> G.face_cycle_set j)"
                by (auto simp: G.face_cycle_set_def orbit_conv_funpow_dist1[OF *])
              moreover
              from postcondition have "inv_face_cycles_inner s' iG iM j j c edge_info"
                by auto
              ultimately
              show ?thesis unfolding inv_face_cycles_inner_def fu_Suc by auto
            qed

            have ?inv using postcondition *
              by (auto simp: inv_face_cycles_outer_def \<open>Suc c = _\<close>)
            with \<open>?var\<close> show ?case by blast
          }
          { case (invariant s')
            { case (weaken s'')
              interpret G: digraph_map "mk_graph iG" iM
                using weaken by (auto simp: inv_face_cycles_def)
              have "j \<in> G.face_cycle_set i"
                using weaken by (auto simp: inv_face_cycles_inner_def)
              then have "j \<in> arcs (mk_graph iG)"
                by (metis G.face_cycle_set_def G.funpow_face_cycle_succ_no_arc G.in_face_cycle_setD
                  funpow_dist1_prop weaken.loop_cond)

              have A: "j \<in> pre_digraph_map.face_cycle_set iM i"
                using weaken by (auto simp: inv_face_cycles_inner_def)
              then have A': "(G.face_cycle_succ ^^ funpow_dist1 G.face_cycle_succ i j) i = j"
                by (intro funpow_dist1_prop) (simp add: G.face_cycle_set_def[symmetric])

              { fix k
                have *: "\<And>i n f x . i < n \<Longrightarrow> \<exists>j<n. (f ^^ j) x = (f ^^ i) x" by auto

                have "(\<exists>l<funpow_dist1 G.face_cycle_succ i (G.face_cycle_succ j). (G.face_cycle_succ ^^ l) i = k)
                    \<longleftrightarrow> (\<exists>l<Suc (funpow_dist1 G.face_cycle_succ i j). (G.face_cycle_succ ^^ l) i = k)" (is "?L \<longleftrightarrow> _")
                  using A \<open>i \<noteq> j\<close>
                  by (subst funpow_dist1_f_eq) (simp_all add: G.face_cycle_set_def[symmetric])
                also have "\<dots> \<longleftrightarrow> (\<exists>l<funpow_dist1 G.face_cycle_succ i j. (G.face_cycle_succ ^^ l) i = k) \<or> k = j" (is "_ \<longleftrightarrow> ?R")
                  using A' by (fastforce elim: less_SucE
                    intro: * exI[where x="(funpow_dist1 G.face_cycle_succ i j)"])
                finally have "?L \<longleftrightarrow> ?R" .
              } note B = this

              have ?inv
                using weaken unfolding inv_face_cycles_inner_def B
                by (auto simp: G.face_cycle_succ_inI)

              have X: "funpow_dist1 G.face_cycle_succ i j < card (G.face_cycle_set i)"
              proof -
                have "funpow_dist1 G.face_cycle_succ i j \<le> funpow_dist1 G.face_cycle_succ i i"
                  using _ _ A unfolding G.face_cycle_set_def
                  apply (rule funpow_dist1_le_self)
                   apply (rule funpow_dist1_prop)
                   unfolding G.face_cycle_set_def[symmetric]
                   by simp_all
                moreover have "funpow_dist1 G.face_cycle_succ i j \<noteq> funpow_dist1 G.face_cycle_succ i i"
                  by (metis A G.face_cycle_set_def G.face_cycle_set_self funpow_dist1_prop
                    weaken.loop_cond)
                ultimately
                have "funpow_dist1 G.face_cycle_succ i j < funpow_dist1 G.face_cycle_succ i i"
                  by simp
                also have "\<dots> \<le> card (G.face_cycle_set i)"
                  by (rule G.funpow_dist1_le_card_fcs) simp
                finally show ?thesis .
              qed

              have ?var
                apply simp
                using _ X apply (rule diff_less_mono2)
                apply (rule funpow_dist1_less_f)
                  using \<open>i \<noteq> j\<close> A by (auto simp: G.face_cycle_set_def[symmetric])
              with \<open>?inv\<close> show ?case by blast
            }
          }
        }
      }
    }
  }
qed auto
declare ovalidNF_face_cycles[THEN ovalidNF_wp, THEN trivial_label, vcg_l]

lemma ovalidNF_euler_genus: "
  ovalidNF (\<lambda>s. distinct (ig_verts iG) \<and> digraph_map (mk_graph iG) iM \<and> c = card (pre_digraph.sccs (mk_graph iG)))
    (euler_genus iG iM c)
  (\<lambda>r s. r = pre_digraph_map.euler_genus (mk_graph iG) iM)
"
  unfolding euler_genus_def
proof vcg_casify
  case weaken
  have "distinct (ig_verts iG)" using weaken by simp
  interpret G: digraph_map "mk_graph iG" iM using weaken by simp
  have len_card:
      "length (ig_verts iG) = card (verts (mk_graph iG))"
      "length (ig_edges iG) = card (arcs (mk_graph iG))"
    using \<open>distinct _\<close> by (auto simp: mkg_simps arcs_mkg distinct_card)
  show ?case
    using weaken by (auto simp: G.euler_genus_def G.euler_char_def len_card)
qed

declare ovalidNF_euler_genus[THEN ovalidNF_wp, THEN trivial_label, vcg_l]

lemma ovalidNF_certify: "
  ovalidNF (\<lambda>s. distinct (ig_verts iG) \<and> fin_digraph (mk_graph iG) \<and> c = card (pre_digraph.sccs (mk_graph iG)))
    (certify iG iM c)
  (\<lambda>r s. r \<longleftrightarrow> pre_digraph_map.euler_genus (mk_graph iG) (mk_map (mk_graph iG) iM) = 0
    \<and> digraph_map (mk_graph iG) (mk_map (mk_graph iG) iM)
    \<and> (\<forall>i < length (ig_edges iG). im_pred iM (im_succ iM i) = i) )
"
  unfolding certify_def
proof vcg_casify
  case weaken
  then interpret fin_digraph "mk_graph iG" by auto
  from weaken show ?case by (auto simp: BRANCH_def intro: wf_digraph)
qed

end
