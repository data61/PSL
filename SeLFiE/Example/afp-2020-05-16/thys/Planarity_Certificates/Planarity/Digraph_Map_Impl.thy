theory Digraph_Map_Impl
imports
  Graph_Genus
  Executable_Permutations
  "Transitive-Closure.Transitive_Closure_Impl"
begin

section \<open>Enumerating Maps\<close>

definition grouped_by_fst :: "('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list list" where
  "grouped_by_fst xs = map (\<lambda>u. filter (\<lambda>x. fst x = u) xs) (remdups (map fst xs))"

fun grouped_out_arcs :: "'a list \<times> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list list" where
  "grouped_out_arcs (vs,as) = grouped_by_fst as"

definition all_maps_list :: "('a list \<times> ('a \<times> 'a) list) \<Rightarrow> ('a \<times> 'a) list list list" where
  "all_maps_list G_list = (cyc_permutationss o grouped_out_arcs) G_list"

definition "list_digraph_ext ext G_list  \<equiv> \<lparr> pverts = set (fst G_list), parcs = set (snd G_list), \<dots> = ext \<rparr>"
abbreviation "list_digraph \<equiv> list_digraph_ext ()"

code_datatype list_digraph_ext


lemma list_digraph_simps:
  "pverts (list_digraph G_list) = set (fst G_list)"
  "parcs (list_digraph G_list) = set (snd G_list)"
  by (auto simp: list_digraph_ext_def)



lemma union_grouped_by_fst:
  "(\<Union>xs \<in> set (grouped_by_fst ys). set xs) = set ys"
  by (auto simp: grouped_by_fst_def)

lemma union_grouped_out_arcs:
  "(\<Union>xs \<in> set (grouped_out_arcs G_list). set xs) = set (snd G_list)"
  by (cases G_list) (simp add: union_grouped_by_fst)

lemma nil_not_in_grouped_out_arcs: "[] \<notin> set (grouped_out_arcs G_list)"
  apply (cases G_list) apply (auto simp: grouped_by_fst_def )
  by (metis (mono_tags) filter_empty_conv fst_conv)

lemma set_grouped_out_arcs:
  assumes "pair_wf_digraph (list_digraph G_list)"
  shows "set ` set (grouped_out_arcs G_list) = {out_arcs (list_digraph G_list) v | v. v \<in> pverts (list_digraph G_list) \<and> out_arcs (list_digraph G_list) v \<noteq> {} }"
    (is "?L = ?R")
proof -
  interpret pair_wf_digraph "list_digraph G_list" by fact
  define vs where "vs = remdups (map fst (snd G_list))"
  have "set vs = {v. out_arcs (list_digraph G_list) v \<noteq> {}}"
    by (auto simp: out_arcs_def list_digraph_ext_def vs_def intro: rev_image_eqI )
  then have vs: "set vs = {v \<in> pverts (list_digraph G_list). out_arcs (list_digraph G_list) v \<noteq> {}}"
    by (auto dest: in_arcsD1)
  have goa: "grouped_out_arcs G_list = map (\<lambda>u. filter (\<lambda>x. fst x = u) (snd G_list)) vs"
    by (cases G_list) (auto simp: grouped_by_fst_def vs_def)
  have filter: "set \<circ> (\<lambda>u. filter (\<lambda>x. fst x = u) (snd G_list)) = out_arcs (list_digraph G_list)"
    by (rule ext) (auto simp: list_digraph_ext_def)
    
  have "set (map set (grouped_out_arcs G_list)) = ?R" by (auto simp add: goa filter vs)
  then show ?thesis by simp
qed

lemma distincts_grouped_by_fst:
  assumes "distinct xs" shows "distincts (grouped_by_fst xs)"
proof -
  have list_eq_setD: "\<And>xs ys. xs = ys \<Longrightarrow> set xs = set ys" by auto
  have inj: "inj_on (\<lambda>u. filter (\<lambda>x. fst x = u) xs) (fst ` set xs)"
    by (rule inj_onI) (drule list_eq_setD, auto)
  with assms show ?thesis
    by (auto simp: grouped_by_fst_def distincts_def distinct_map filter_empty_conv)
qed

lemma distincts_grouped_arcs:
  assumes "distinct (snd G_list)" shows "distincts (grouped_out_arcs G_list)"
  using assms by (cases G_list) (simp add: distincts_grouped_by_fst)

lemma distincts_in_all_maps_list:
  "distinct (snd X) \<Longrightarrow> xss \<in> set (all_maps_list X) \<Longrightarrow> distincts xss"
  by (simp add: all_maps_list_def distincts_grouped_arcs in_set_cyc_permutationss)



definition to_map :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a \<Rightarrow> 'a \<times> 'a) \<Rightarrow> ('a \<times> 'a) pre_map" where
  "to_map A f = \<lparr> edge_rev = swap_in A, edge_succ = f \<rparr>"

abbreviation "to_map' as xss \<equiv> to_map (set as) (lists_succ xss)"


definition all_maps :: "'a pair_pre_digraph \<Rightarrow> ('a \<times> 'a) pre_map set" where
  "all_maps G \<equiv> to_map (arcs G) ` {f. f permutes arcs G \<and> (\<forall>v \<in> verts G. out_arcs G v \<noteq> {} \<longrightarrow> cyclic_on f (out_arcs G v))}"

definition maps_all_maps_list :: "('a list \<times> ('a \<times> 'a) list) \<Rightarrow> ('a \<times> 'a) pre_map list" where
  "maps_all_maps_list G_list = map (to_map (set (snd G_list)) o lists_succ) (all_maps_list G_list)"

lemma (in pair_graph) all_maps_correct:
  shows "all_maps G = {M. digraph_map G M}"
proof (intro set_eqI iffI)
  fix M assume A:"M \<in> all_maps G"
  then have [simp]: "edge_rev M = swap_in (arcs G)" "edge_succ M permutes parcs G"
    by (auto simp: all_maps_def to_map_def)

  have "digraph_map G M"
  proof (rule digraph_mapI)
    fix a assume "a \<notin> parcs G" then show "edge_rev M a = a" by (auto simp: swap_in_def)
  next
    fix a assume "a \<in> parcs G"
    then show "edge_rev M (edge_rev M a) = a" "fst (edge_rev M a) = snd a" "edge_rev M a \<noteq> a"
      by (case_tac [!] "a") (auto intro: arcs_symmetric simp: swap_in_def dest: no_loops)
  next
    show "edge_succ M permutes parcs G" by simp
  next
    fix v assume "v \<in> pverts G" "out_arcs (with_proj G) v \<noteq> {}"
    then show "cyclic_on (edge_succ M) (out_arcs (with_proj G) v)"
      using A unfolding all_maps_def by (auto simp: to_map_def)
  qed
  then show "M \<in> {M. digraph_map G M}" by simp
next
  fix M assume A: "M \<in> {M. digraph_map G M}"
  then interpret M: digraph_map G M by simp
  from A have "\<And>x. fst (edge_rev M x) = fst (swap_in (arcs G) x)"
      "\<And>x. snd (edge_rev M x) = snd (swap_in (arcs G) x)"
    using M.tail_arev M.head_arev by (auto simp: fun_eq_iff swap_in_def M.arev_eq)
  then have "edge_rev M = swap_in (arcs G)"
    by (metis prod.collapse fun_eq_iff)
  then show "M \<in> all_maps G"
    using M.edge_succ_permutes M.edge_succ_cyclic
    unfolding all_maps_def
    by (auto simp: to_map_def intro!: image_eqI[where x="edge_succ M"])
qed


lemma set_maps_all_maps_list:
  assumes "pair_wf_digraph (list_digraph G_list)" "distinct (snd G_list)"
  shows "all_maps (list_digraph G_list) = set (maps_all_maps_list G_list)"
proof -
  let ?G = "list_digraph G_list"

  { fix f
    have "(\<forall>x\<in>set (grouped_out_arcs G_list). cyclic_on f (set x))
        \<longleftrightarrow> (\<forall>x\<in>set ` set (grouped_out_arcs G_list). cyclic_on f x)" (is "?all1 = _")
      by simp
    also have "\<dots> \<longleftrightarrow> (\<forall>v\<in>pverts ?G. out_arcs ?G v \<noteq> {} \<longrightarrow> cyclic_on f (out_arcs ?G v))" (is "_ = ?all2")
      using assms by (auto simp: set_grouped_out_arcs)
    finally have "?all1 = ?all2" .
  } note all_eq = this

  have "lists_succ ` set (all_maps_list G_list)
      = {f. f permutes arcs ?G \<and> (\<forall>v \<in> pverts ?G. out_arcs ?G v \<noteq> {} \<longrightarrow> cyclic_on f (out_arcs ?G v))}"
    unfolding all_maps_list_def using assms all_eq
    by (simp add: lists_succ_set_cyc_permutationss distincts_grouped_arcs union_grouped_out_arcs list_digraph_simps)
  then have *: "lists_succ ` set (all_maps_list G_list) = {f. f permutes set (snd G_list) \<and> (\<forall>v\<in>set (fst G_list). out_arcs (with_proj \<lparr>pverts = set (fst G_list), parcs = set (snd G_list)\<rparr>) v \<noteq> {} \<longrightarrow> cyclic_on f (out_arcs (with_proj \<lparr>pverts = set (fst G_list), parcs = set (snd G_list)\<rparr>) v))}"
    by (auto simp add: maps_all_maps_list_def all_maps_def list_digraph_simps list_digraph_ext_def)
  then have **: "\<And>f. \<not> (f permutes set (snd G_list) \<and> (\<forall>a. a \<in> set (fst G_list) \<longrightarrow> out_arcs (with_proj \<lparr>pverts = set (fst G_list), parcs = set (snd G_list)\<rparr>) a \<noteq> {} \<longrightarrow> cyclic_on f (out_arcs (with_proj \<lparr>pverts = set (fst G_list), parcs = set (snd G_list)\<rparr>) a))) \<or> f \<in> lists_succ ` set (all_maps_list G_list)"
    by force
  from * show ?thesis
    by (auto simp add: maps_all_maps_list_def all_maps_def list_digraph_simps list_digraph_ext_def) (use ** in blast)
qed


section \<open>Compute Face Cycles\<close>

definition lists_fc_succ :: "('a \<times> 'a) list list \<Rightarrow> ('a \<times> 'a) \<Rightarrow> ('a \<times> 'a)" where
  "lists_fc_succ xss = (let sxss = \<Union>(sset xss) in (\<lambda>x. lists_succ xss (swap_in sxss x)))"

locale lists_digraph_map =
  fixes G_list :: "'b list \<times> ('b \<times> 'b) list"
    and xss :: "('b \<times> 'b) list list"
  assumes digraph_map: "digraph_map (list_digraph G_list) (to_map' (snd G_list) xss)"
  assumes no_loops: "\<And>a. a \<in> parcs (list_digraph G_list) \<Longrightarrow> fst a \<noteq> snd a"
  assumes distincts_xss: "distincts xss"
  assumes parcs_xss: "parcs (list_digraph G_list) = \<Union>(sset xss)"
begin

abbreviation (input) "G \<equiv> list_digraph G_list"
abbreviation (input) "M \<equiv> to_map' (snd G_list) xss"

lemma edge_rev_simps:
  assumes "(u,v) \<in> parcs G" shows "edge_rev M (u,v) = (v,u)"
  using assms
  unfolding to_map_def list_digraph_ext_def by (auto simp: swap_in_def to_map_def)

end

sublocale lists_digraph_map \<subseteq> digraph_map G M by (rule local.digraph_map)

sublocale lists_digraph_map \<subseteq> pair_graph G
proof
  fix e assume "e \<in> parcs G"
  then have "e \<in> arcs G" by simp
  then have "head G e \<in> verts G" "tail G e \<in> verts G" by (blast dest: wellformed)+
  then show "fst e \<in> pverts G" "snd e \<in> pverts G" by auto
next
  fix e assume "e \<in> parcs G" then show "fst e \<noteq> snd e" using no_loops by simp
next
  show "finite (pverts G)" "finite (parcs G)"
    unfolding list_digraph_ext_def by simp_all
next
  { fix u v assume "(u,v) \<in> parcs G"
    then have "edge_rev M (u,v) \<in> parcs G"
      using edge_rev_in_arcs by simp
    then have "(v,u) \<in> parcs G" using \<open>(u,v) \<in> _ \<close> by (simp add: edge_rev_simps) }
  then show "symmetric G"
    unfolding symmetric_def by (auto intro: symI)
qed

context lists_digraph_map begin

definition "lists_fcs \<equiv> orbits_list (lists_fc_succ xss)"

lemma M_simps:
  "edge_succ M = lists_succ xss"
  unfolding to_map_def by (cases G_list) auto

lemma lists_fc_succ_permutes: "lists_fc_succ xss permutes (\<Union>(sset xss))"
proof -
  have "\<forall>(u,v) \<in> \<Union>(sset xss). (v,u) \<in> \<Union>(sset xss)"
    using sym_arcs unfolding parcs_xss[symmetric] symmetric_def by (auto elim: symE)
  then have "swap_in (\<Union>(sset xss)) permutes \<Union>(sset xss)"
    using distincts_xss
    apply (auto simp: permutes_def split: if_splits)
    unfolding swap_in_def
    apply (simp_all split: if_splits prod.splits)
    apply metis+
    done
  moreover
  have "lists_succ xss permutes (\<Union>(sset xss))"
    using lists_succ_permutes[OF distincts_xss] by simp
  moreover
  have "lists_fc_succ xss = lists_succ xss o swap_in (\<Union>(sset xss))"
    by (simp add: fun_eq_iff lists_fc_succ_def)
  ultimately
  show ?thesis by (metis permutes_compose)
qed

lemma permutation_lists_fc_succ[intro, simp]: "permutation (lists_fc_succ xss)"
  using lists_fc_succ_permutes by (auto simp: permutation_permutes)

lemma face_cycle_succ_conv: "face_cycle_succ = lists_fc_succ xss"
  using parcs_xss unfolding face_cycle_succ_def
  by (simp add: fun_eq_iff to_map_def lists_fc_succ_def swap_in_def list_digraph_ext_def)

lemma sset_lists_fcs:
  "sset (lists_fcs as) = {face_cycle_set a | a. a \<in> set as}"
  by (auto simp: lists_fcs_def sset_orbits_list face_cycle_set_def face_cycle_succ_conv)

lemma distincts_lists_fcs: "distinct as \<Longrightarrow>distincts (lists_fcs as)"
  by (simp add: lists_fcs_def distincts_orbits_list)

lemma face_cycle_set_ss: "a \<in> parcs G \<Longrightarrow> face_cycle_set a \<subseteq> parcs G"
  using in_face_cycle_setD with_proj_simps(2) by blast

lemma face_cycle_succ_neq:
  assumes "a \<in> parcs G" shows "face_cycle_succ a \<noteq> a"
  using assms no_loops by (intro face_cycle_succ_neq) auto

lemma card_face_cycle_sets_conv:
  shows "card (pre_digraph_map.face_cycle_sets G M) = length (lists_fcs (remdups (snd G_list)))"
proof -
  interpret digraph_map G M by (rule digraph_map)

  have "face_cycle_sets = {face_cycle_set a | a. a \<in> parcs G}"
    by (auto simp: face_cycle_sets_def)
  also have "\<dots> = sset (lists_fcs (remdups (snd G_list)))"
    unfolding sset_lists_fcs by (simp add: list_digraph_simps)
  also have "card \<dots> = length (lists_fcs (remdups (snd G_list)))"
    by (simp add: card_image distincts_inj_on_set distinct_card distincts_distinct distincts_lists_fcs)
  finally show ?thesis .
qed

end


definition "gen_succ \<equiv> \<lambda>as xs. [b. (a,b) <- as, a \<in> set xs]"
interpretation RTLI: set_access_gen set "\<lambda>x xs. x \<in> set xs" "[]" "\<lambda>xs ys. remdups (xs @ ys)" "gen_succ"
  by standard (auto simp: gen_succ_def)
hide_const (open) gen_succ

text \<open>
  It would suffice to check that @{term "set (RTLI.rtrancl_i A [u]) = set V"}. We don't do
  this here, since it makes the proof more complicated (and is not necessary for the graphs
  we care about
\<close>
definition sccs_verts_impl :: "'a list \<times> ('a \<times> 'a) list \<Rightarrow> 'a set set" where
  "sccs_verts_impl G \<equiv> set ` (\<lambda>x. RTLI.rtrancl_i (snd G) [x]) ` set (fst G)"

definition isolated_verts_impl :: "'a list \<times> ('a \<times> 'a) list \<Rightarrow> 'a list" where
  "isolated_verts_impl G = [v \<leftarrow> (fst G). \<not>(\<exists>e \<in> set (snd G). fst e = v)]"

definition pair_graph_impl :: "'a list \<times> ('a \<times> 'a) list \<Rightarrow> bool" where
  "pair_graph_impl G \<equiv> case G of (V,A) \<Rightarrow> (\<forall>(u,v) \<in> set A. u \<noteq> v \<and> u \<in> set V \<and> v \<in> set V \<and> (v,u) \<in> set A)"

definition genus_impl :: "'a list \<times> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list list \<Rightarrow> int" where
  "genus_impl G M \<equiv> case G of (V,A) \<Rightarrow>
    (int (2*card (sccs_verts_impl G)) - int (length (isolated_verts_impl G))
      - (int (length V) - int (length A) div 2
      + int (length (orbits_list_impl (lists_fc_succ M) A)))) div 2"

definition comb_planar_impl :: "'a list \<times> ('a \<times> 'a) list \<Rightarrow> bool" where
  "comb_planar_impl G \<equiv> case G of (V,A) \<Rightarrow>
    let i = int (2*card (sccs_verts_impl G)) - int (length (isolated_verts_impl G))
      - int (length V) + int (length A) div 2
    in (\<exists>M\<in>set (all_maps_list G). (i - int (length (orbits_list_impl (lists_fc_succ M) A))) div 2 = 0)"

(*
definition comb_planar_impl :: "'a list \<times> ('a \<times> 'a) list \<Rightarrow> bool" where
  "comb_planar_impl G \<equiv> \<exists>M\<in>set (all_maps_list G). genus_impl G M = 0"
*)

lemma sccs_verts_impl_correct:
  assumes "pair_pseudo_graph (list_digraph G)"
  shows "pre_digraph.sccs_verts (list_digraph G) = sccs_verts_impl G"
proof -
  interpret pair_pseudo_graph "list_digraph G" by fact
  { fix u assume "u \<in> set (fst G)"
    then have "\<And>x. (u, x) \<in> (set (snd G))\<^sup>* \<Longrightarrow> x \<in> set (fst G)"
      by (metis in_arcsD2 list_digraph_simps rtrancl.cases)
    then have "set (RTLI.rtrancl_i (snd G) [u]) = {v. u \<rightarrow>\<^sup>*\<^bsub>list_digraph G\<^esub> v }"
      unfolding RTLI.rtrancl_impl reachable_conv by (auto simp: list_digraph_simps \<open>u \<in> _\<close>)
    also have "\<dots> = scc_of u"
      unfolding scc_of_def by (auto intro: symmetric_reachable')
    finally have "scc_of u = set (RTLI.rtrancl_i (snd G) [u])" by simp
  }
  then have "pre_digraph.sccs_verts (list_digraph G) = set ` (\<lambda>x. RTLI.rtrancl_i (snd G) [x]) ` set (fst G)"
    unfolding sccs_verts_conv_scc_of list_digraph_simps
    by (force intro: rev_image_eqI)
  then show ?thesis unfolding sccs_verts_impl_def by simp
qed

lemma isolated_verts_impl_correct:
  "pre_digraph.isolated_verts (list_digraph G) = set (isolated_verts_impl G)"
  by (auto simp: pre_digraph.isolated_verts_def isolated_verts_impl_def list_digraph_simps out_arcs_def)

lemma pair_graph_impl_correct[code]:
  "pair_graph (list_digraph G) = pair_graph_impl G" (is "?L = ?R")
  unfolding pair_graph_def pair_digraph_def pair_fin_digraph_def pair_wf_digraph_def
    pair_fin_digraph_axioms_def pair_loopfree_digraph_def pair_loopfree_digraph_axioms_def
    pair_sym_digraph_def pair_sym_digraph_axioms_def pair_pseudo_graph_def
    pair_graph_impl_def
  by (auto simp: pair_graph_impl_def list_digraph_simps symmetric_def intro: symI dest: symD split: prod.splits)

lemma genus_impl_correct:
  assumes dist_V: "distinct (fst G)" and dist_A: "distinct (snd G)"
  assumes "lists_digraph_map G M"
  shows "pre_digraph_map.euler_genus (list_digraph G) (to_map' (snd G) M) = genus_impl G M"
proof -
  interpret lists_digraph_map G M by fact
  obtain V A where G_eq: "G = (V,A)" by (cases G)
  moreover
  have "distinct (isolated_verts_impl G)"
    using dist_V by (auto simp: isolated_verts_impl_def )
  moreover
  have faces: "card face_cycle_sets = length (orbits_list_impl (lists_fc_succ M) (snd G))"
    using dist_A
    by (simp add: card_face_cycle_sets_conv lists_fcs_def orbits_list_conv_impl distinct_remdups_id)
  ultimately show ?thesis
    using pair_pseudo_graph dist_V dist_A
    unfolding euler_genus_def euler_char_def genus_impl_def card_sccs_verts[symmetric] 
    by (simp add: sccs_verts_impl_correct isolated_verts_impl_correct
      distinct_card list_digraph_simps zdiv_int)
qed

lemma elems_all_maps_list:
  assumes "M \<in> set (all_maps_list G)" "distinct (snd G)"
  shows "\<Union>(sset M) = set (snd G)"
    using assms
    by (simp add: all_maps_list_def in_set_cyc_permutationss distincts_grouped_arcs union_grouped_out_arcs[symmetric])
       (metis set_map)

lemma comb_planar_impl_altdef: "comb_planar_impl G = (\<exists>M\<in>set (all_maps_list G). genus_impl G M = 0)"
  unfolding comb_planar_impl_def Let_def genus_impl_def by (cases G) (simp add: algebra_simps)

lemma comb_planar_impl_correct:
  assumes "pair_graph (list_digraph G)"
  assumes dist_V: "distinct (fst G)" and dist_A: "distinct (snd G)"
  shows "comb_planar (list_digraph G) = comb_planar_impl G" (is "?L = ?R")
proof -
  interpret G: pair_graph "list_digraph G" by fact
  let ?G = "list_digraph G"
  have *: "all_maps (list_digraph G) = set (maps_all_maps_list G)"
    by (rule set_maps_all_maps_list) (unfold_locales, simp add: dist_A)

  obtain V A where "G = (V,A)" by (cases G)

  { fix M assume "M \<in> set (all_maps_list G)"
    have "digraph_map (list_digraph G) (to_map' (snd G) M)"
      using \<open>M \<in> _\<close> G.all_maps_correct by (auto simp: * maps_all_maps_list_def)
    then interpret G: digraph_map "list_digraph G" "to_map' (snd G) M" .

    have "distincts M" using \<open>M \<in> _\<close>
      using dist_A distincts_in_all_maps_list by blast

    have "lists_digraph_map G M"
      using elems_all_maps_list[OF \<open>M \<in> _\<close> \<open>distinct (snd G)\<close>]
      apply unfold_locales
      by (auto intro: \<open>distincts M\<close> dest: G.adj_not_same) (auto simp: list_digraph_simps)
  } note ldm = this

  have "comb_planar ?G = (\<exists>M \<in> {M. digraph_map ?G M}. pre_digraph_map.euler_genus ?G M = 0)"
    unfolding comb_planar_def by simp
  also have "\<dots> = (\<exists>M\<in>set (all_maps_list G). pre_digraph_map.euler_genus (list_digraph G)
      (to_map (set (snd G)) (lists_succ M)) = 0)"
    unfolding comb_planar_def comb_planar_impl_def Let_def G.all_maps_correct[symmetric]
      set_maps_all_maps_list[OF G.pair_wf_digraph dist_A] maps_all_maps_list_def by simp
  also have "\<dots> = (\<exists>M\<in>set (all_maps_list G). genus_impl G M = 0)"
    using ldm assms by (simp add: genus_impl_correct)
  also have "\<dots> = comb_planar_impl G"
    unfolding comb_planar_impl_def genus_impl_def Let_def by (simp add: \<open>G = (V,A)\<close> algebra_simps)
  finally show ?thesis .
qed

end
