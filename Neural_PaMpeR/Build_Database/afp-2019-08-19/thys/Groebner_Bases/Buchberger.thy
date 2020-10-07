(* Author: Alexander Maletzky *)

section \<open>Buchberger's Algorithm\<close>

theory Buchberger
  imports Algorithm_Schema
begin

context gd_term
begin

subsection \<open>Reduction\<close>

definition trdsp::"('t \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('t, 'b, 'c) pdata_pair \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::field)"
  where "trdsp bs p \<equiv> trd bs (spoly (fst (fst p)) (fst (snd p)))"

lemma trdsp_alt: "trdsp bs (p, q) = trd bs (spoly (fst p) (fst q))"
  by (simp add: trdsp_def)

lemma trdsp_in_pmdl: "trdsp bs (p, q) \<in> pmdl (insert (fst p) (insert (fst q) (set bs)))"
  unfolding trdsp_alt
proof (rule pmdl_closed_trd)
  have "spoly (fst p) (fst q) \<in> pmdl {fst p, fst q}"
  proof (rule pmdl_closed_spoly)
    show "fst p \<in> pmdl {fst p, fst q}" by (rule pmdl.span_base, simp)
  next
    show "fst q \<in> pmdl {fst p, fst q}" by (rule pmdl.span_base, simp)
  qed
  also have "... \<subseteq> pmdl (insert (fst p) (insert (fst q) (set bs)))"
    by (rule pmdl.span_mono, simp)
  finally show "spoly (fst p) (fst q) \<in> pmdl (insert (fst p) (insert (fst q) (set bs)))" .
next
  have "set bs \<subseteq> insert (fst p) (insert (fst q) (set bs))" by blast
  also have "... \<subseteq> pmdl (insert (fst p) (insert (fst q) (set bs)))"
    by (fact pmdl.span_superset)
  finally show "set bs \<subseteq> pmdl (insert (fst p) (insert (fst q) (set bs)))" .
qed

lemma dgrad_p_set_le_trdsp:
  assumes "dickson_grading d"
  shows "dgrad_p_set_le d {trdsp bs (p, q)} (insert (fst p) (insert (fst q) (set bs)))"
proof -
  let ?h = "trdsp bs (p, q)"
  have "(red (set bs))\<^sup>*\<^sup>* (spoly (fst p) (fst q)) ?h" unfolding trdsp_alt by (rule trd_red_rtrancl)
  with assms have "dgrad_p_set_le d {?h} (insert (spoly (fst p) (fst q)) (set bs))"
    by (rule dgrad_p_set_le_red_rtrancl)
  also have "dgrad_p_set_le d ... ({fst p, fst q} \<union> set bs)"
  proof (rule dgrad_p_set_leI_insert)
    show "dgrad_p_set_le d (set bs) ({fst p, fst q} \<union> set bs)" by (rule dgrad_p_set_le_subset, blast)
  next
    from assms have "dgrad_p_set_le d {spoly (fst p) (fst q)} {fst p, fst q}"
      by (rule dgrad_p_set_le_spoly)
    also have "dgrad_p_set_le d ... ({fst p, fst q} \<union> set bs)"
      by (rule dgrad_p_set_le_subset, blast)
    finally show "dgrad_p_set_le d {spoly (fst p) (fst q)} ({fst p, fst q} \<union> set bs)" .
  qed
  finally show ?thesis by simp
qed

lemma components_trdsp_subset:
  "component_of_term ` keys (trdsp bs (p, q)) \<subseteq> component_of_term ` Keys (insert (fst p) (insert (fst q) (set bs)))"
proof -
  let ?h = "trdsp bs (p, q)"
  have "(red (set bs))\<^sup>*\<^sup>* (spoly (fst p) (fst q)) ?h" unfolding trdsp_alt by (rule trd_red_rtrancl)
  hence "component_of_term ` keys ?h \<subseteq>
              component_of_term ` keys (spoly (fst p) (fst q)) \<union> component_of_term ` Keys (set bs)"
    by (rule components_red_rtrancl_subset)
  also have "... \<subseteq> component_of_term ` Keys {fst p, fst q} \<union> component_of_term ` Keys (set bs)"
    using components_spoly_subset by force
  also have "... = component_of_term ` Keys (insert (fst p) (insert (fst q) (set bs)))"
    by (simp add: Keys_insert image_Un Un_assoc)
  finally show ?thesis .
qed

definition gb_red_aux :: "('t, 'b::field, 'c) pdata list \<Rightarrow> ('t, 'b, 'c) pdata_pair list \<Rightarrow>
                          ('t \<Rightarrow>\<^sub>0 'b) list"
  where "gb_red_aux bs ps =
              (let bs' = map fst bs in
                filter (\<lambda>h. h \<noteq> 0) (map (trdsp bs') ps)
              )"

text \<open>Actually, @{const gb_red_aux} is only called on singleton lists.\<close>

lemma set_gb_red_aux: "set (gb_red_aux bs ps) = (trdsp (map fst bs)) ` set ps - {0}"
  by (simp add: gb_red_aux_def, blast)

lemma in_set_gb_red_auxI:
  assumes "(p, q) \<in> set ps" and "h = trdsp (map fst bs) (p, q)" and "h \<noteq> 0"
  shows "h \<in> set (gb_red_aux bs ps)"
  using assms(1, 3) unfolding set_gb_red_aux assms(2) by force

lemma in_set_gb_red_auxE:
  assumes "h \<in> set (gb_red_aux bs ps)"
  obtains p q where "(p, q) \<in> set ps" and "h = trdsp (map fst bs) (p, q)"
  using assms unfolding set_gb_red_aux by force

lemma gb_red_aux_not_zero: "0 \<notin> set (gb_red_aux bs ps)"
  by (simp add: set_gb_red_aux)

lemma gb_red_aux_irredudible:
  assumes "h \<in> set (gb_red_aux bs ps)" and "b \<in> set bs" and "fst b \<noteq> 0"
  shows "\<not> lt (fst b) adds\<^sub>t lt h"
proof
  assume "lt (fst b) adds\<^sub>t (lt h)"
  from assms(1) obtain p q :: "('t, 'b, 'c) pdata" where h: "h = trdsp (map fst bs) (p, q)"
    by (rule in_set_gb_red_auxE)
  have "\<not> is_red (set (map fst bs)) h" unfolding h trdsp_def by (rule trd_irred)
  moreover have "is_red (set (map fst bs)) h"
  proof (rule is_red_addsI)
    from assms(2) show "fst b \<in> set (map fst bs)" by (simp)
  next
    from assms(1) have "h \<noteq> 0" by (simp add: set_gb_red_aux)
    thus "lt h \<in> keys h" by (rule lt_in_keys)
  qed fact+
  ultimately show False ..
qed

lemma gb_red_aux_dgrad_p_set_le:
  assumes "dickson_grading d"
  shows "dgrad_p_set_le d (set (gb_red_aux bs ps)) (args_to_set ([], bs, ps))"
proof (rule dgrad_p_set_leI)
  fix h
  assume "h \<in> set (gb_red_aux bs ps)"
  then obtain p q where "(p, q) \<in> set ps" and h: "h = trdsp (map fst bs) (p, q)"
    by (rule in_set_gb_red_auxE)
  from assms have "dgrad_p_set_le d {h} (insert (fst p) (insert (fst q) (set (map fst bs))))"
    unfolding h by (rule dgrad_p_set_le_trdsp)
  also have "dgrad_p_set_le d ... (args_to_set ([], bs, ps))"
  proof (rule dgrad_p_set_le_subset, intro insert_subsetI)
    from \<open>(p, q) \<in> set ps\<close> have "fst p \<in> fst ` fst ` set ps" by force
    thus "fst p \<in> args_to_set ([], bs, ps)" by (auto simp add: args_to_set_alt)
  next
    from \<open>(p, q) \<in> set ps\<close> have "fst q \<in> fst ` snd ` set ps" by force
    thus "fst q \<in> args_to_set ([], bs, ps)" by (auto simp add: args_to_set_alt)
  next
    show "set (map fst bs) \<subseteq> args_to_set ([], bs, ps)" by (auto simp add: args_to_set_alt)
  qed
  finally show "dgrad_p_set_le d {h} (args_to_set ([], bs, ps))" .
qed

lemma components_gb_red_aux_subset:
  "component_of_term ` Keys (set (gb_red_aux bs ps)) \<subseteq> component_of_term ` Keys (args_to_set ([], bs, ps))"
proof
  fix k
  assume "k \<in> component_of_term ` Keys (set (gb_red_aux bs ps))"
  then obtain v where "v \<in> Keys (set (gb_red_aux bs ps))" and k: "k = component_of_term v" ..
  from this(1) obtain h where "h \<in> set (gb_red_aux bs ps)" and "v \<in> keys h" by (rule in_KeysE)
  from this(1) obtain p q where "(p, q) \<in> set ps" and h: "h = trdsp (map fst bs) (p, q)"
    by (rule in_set_gb_red_auxE)
  from \<open>v \<in> keys h\<close> have "k \<in> component_of_term ` keys h" by (simp add: k)
  have "component_of_term ` keys h \<subseteq> component_of_term ` Keys (insert (fst p) (insert (fst q) (set (map fst bs))))"
    unfolding h by (rule components_trdsp_subset)
  also have "... \<subseteq> component_of_term ` Keys (args_to_set ([], bs, ps))"
  proof (rule image_mono, rule Keys_mono, intro insert_subsetI)
    from \<open>(p, q) \<in> set ps\<close> have "fst p \<in> fst ` fst ` set ps" by force
    thus "fst p \<in> args_to_set ([], bs, ps)" by (auto simp add: args_to_set_alt)
  next
    from \<open>(p, q) \<in> set ps\<close> have "fst q \<in> fst ` snd ` set ps" by force
    thus "fst q \<in> args_to_set ([], bs, ps)" by (auto simp add: args_to_set_alt)
  next
    show "set (map fst bs) \<subseteq> args_to_set ([], bs, ps)" by (auto simp add: args_to_set_alt)
  qed
  finally have "component_of_term ` keys h \<subseteq> component_of_term ` Keys (args_to_set ([], bs, ps))" .
  with \<open>k \<in> component_of_term ` keys h\<close> show "k \<in> component_of_term ` Keys (args_to_set ([], bs, ps))" ..
qed

lemma pmdl_gb_red_aux: "set (gb_red_aux bs ps) \<subseteq> pmdl (args_to_set ([], bs, ps))"
proof
  fix h
  assume "h \<in> set (gb_red_aux bs ps)"
  then obtain p q where "(p, q) \<in> set ps" and h: "h = trdsp (map fst bs) (p, q)"
    by (rule in_set_gb_red_auxE)
  have "h \<in> pmdl (insert (fst p) (insert (fst q) (set (map fst bs))))" unfolding h
    by (fact trdsp_in_pmdl)
  also have "... \<subseteq> pmdl (args_to_set ([], bs, ps))"
  proof (rule pmdl.span_mono, intro insert_subsetI)
    from \<open>(p, q) \<in> set ps\<close> have "fst p \<in> fst ` fst ` set ps" by force
    thus "fst p \<in> args_to_set ([], bs, ps)" by (auto simp add: args_to_set_alt)
  next
    from \<open>(p, q) \<in> set ps\<close> have "fst q \<in> fst ` snd ` set ps" by force
    thus "fst q \<in> args_to_set ([], bs, ps)" by (auto simp add: args_to_set_alt)
  next
    show "set (map fst bs) \<subseteq> args_to_set ([], bs, ps)" by (auto simp add: args_to_set_alt)
  qed
  finally show "h \<in> pmdl (args_to_set ([], bs, ps))" .
qed

lemma gb_red_aux_spoly_reducible:
  assumes "(p, q) \<in> set ps"
  shows "(red (fst ` set bs \<union> set (gb_red_aux bs ps)))\<^sup>*\<^sup>* (spoly (fst p) (fst q)) 0"
proof -
  define h where "h = trdsp (map fst bs) (p, q)"
  from trd_red_rtrancl[of "map fst bs" "spoly (fst p) (fst q)"]
  have "(red (set (map fst bs)))\<^sup>*\<^sup>* (spoly (fst p) (fst q)) h"
    by (simp only: h_def trdsp_alt)
  hence "(red (fst ` set bs \<union> set (gb_red_aux bs ps)))\<^sup>*\<^sup>* (spoly (fst p) (fst q)) h"
  proof (rule red_rtrancl_subset)
    show "set (map fst bs) \<subseteq> fst ` set bs \<union> set (gb_red_aux bs ps)" by simp
  qed
  moreover have "(red (fst ` set bs \<union> set (gb_red_aux bs ps)))\<^sup>*\<^sup>* h 0"
  proof (cases "h = 0")
    case True
    show ?thesis unfolding True ..
  next
    case False
    hence "red {h} h 0" by (rule red_self)
    hence "red (fst ` set bs \<union> set (gb_red_aux bs ps)) h 0"
    proof (rule red_subset)
      from assms h_def False have "h \<in> set (gb_red_aux bs ps)" by (rule in_set_gb_red_auxI)
      thus "{h} \<subseteq> fst ` set bs \<union> set (gb_red_aux bs ps)" by simp
    qed
    thus ?thesis ..
  qed
  ultimately show ?thesis by simp
qed

definition gb_red :: "('t, 'b::field, 'c::default, 'd) complT"
  where "gb_red gs bs ps sps data = (map (\<lambda>h. (h, default)) (gb_red_aux (gs @ bs) sps), snd data)"

lemma fst_set_fst_gb_red: "fst ` set (fst (gb_red gs bs ps sps data)) = set (gb_red_aux (gs @ bs) sps)"
  by (simp add: gb_red_def, force)

lemma rcp_spec_gb_red: "rcp_spec gb_red"
proof (rule rcp_specI)
  fix gs bs::"('t, 'b, 'c) pdata list" and ps sps and data::"nat \<times> 'd"
  from gb_red_aux_not_zero show "0 \<notin> fst ` set (fst (gb_red gs bs ps sps data))"
    unfolding fst_set_fst_gb_red .
next
  fix gs bs::"('t, 'b, 'c) pdata list" and ps sps h b and data::"nat \<times> 'd"
  assume "h \<in> set (fst (gb_red gs bs ps sps data))" and "b \<in> set gs \<union> set bs"
  from this(1) have "fst h \<in> fst ` set (fst (gb_red gs bs ps sps data))" by simp
  hence "fst h \<in> set (gb_red_aux (gs @ bs) sps)" by (simp only: fst_set_fst_gb_red)
  moreover from \<open>b \<in> set gs \<union> set bs\<close> have "b \<in> set (gs @ bs)" by simp
  moreover assume "fst b \<noteq> 0"
  ultimately show "\<not> lt (fst b) adds\<^sub>t lt (fst h)" by (rule gb_red_aux_irredudible)
next
  fix gs bs::"('t, 'b, 'c) pdata list" and ps sps and d::"'a \<Rightarrow> nat" and data::"nat \<times> 'd"
  assume "dickson_grading d"
  hence "dgrad_p_set_le d (set (gb_red_aux (gs @ bs) sps)) (args_to_set ([], gs @ bs, sps))"
    by (rule gb_red_aux_dgrad_p_set_le)
  also have "... = args_to_set (gs, bs, sps)" by (simp add: args_to_set_alt image_Un)
  finally show "dgrad_p_set_le d (fst ` set (fst (gb_red gs bs ps sps data))) (args_to_set (gs, bs, sps))"
    by (simp only: fst_set_fst_gb_red)
next
  fix gs bs::"('t, 'b, 'c) pdata list" and ps sps and data::"nat \<times> 'd"
  have "component_of_term ` Keys (set (gb_red_aux (gs @ bs) sps)) \<subseteq>
          component_of_term ` Keys (args_to_set ([], gs @ bs, sps))"
    by (rule components_gb_red_aux_subset)
  also have "... = component_of_term ` Keys (args_to_set (gs, bs, sps))"
    by (simp add: args_to_set_alt image_Un)
  finally show "component_of_term ` Keys (fst ` set (fst (gb_red gs bs ps sps data))) \<subseteq>
                component_of_term ` Keys (args_to_set (gs, bs, sps))" by (simp only: fst_set_fst_gb_red)
next
  fix gs bs::"('t, 'b, 'c) pdata list" and ps sps and data::"nat \<times> 'd"
  have "set (gb_red_aux (gs @ bs) sps) \<subseteq> pmdl (args_to_set ([], gs @ bs, sps))"
    by (fact pmdl_gb_red_aux)
  also have "... = pmdl (args_to_set (gs, bs, sps))" by (simp add: args_to_set_alt image_Un)
  finally have "fst ` set (fst (gb_red gs bs ps sps data)) \<subseteq> pmdl (args_to_set (gs, bs, sps))"
    by (simp only: fst_set_fst_gb_red)
  moreover {
    fix p q :: "('t, 'b, 'c) pdata"
    assume "(p, q) \<in> set sps"
    hence "(red (fst ` set (gs @ bs) \<union> set (gb_red_aux (gs @ bs) sps)))\<^sup>*\<^sup>* (spoly (fst p) (fst q)) 0"
      by (rule gb_red_aux_spoly_reducible)
  }
  ultimately show
    "fst ` set (fst (gb_red gs bs ps sps data)) \<subseteq> pmdl (args_to_set (gs, bs, sps)) \<and>
     (\<forall>(p, q)\<in>set sps.
         set sps \<subseteq> set bs \<times> (set gs \<union> set bs) \<longrightarrow>
         (red (fst ` (set gs \<union> set bs) \<union> fst ` set (fst (gb_red gs bs ps sps data))))\<^sup>*\<^sup>* (spoly (fst p) (fst q)) 0)"
    by (auto simp add: image_Un fst_set_fst_gb_red)
qed

lemmas compl_struct_gb_red = compl_struct_rcp[OF rcp_spec_gb_red]
lemmas compl_pmdl_gb_red = compl_pmdl_rcp[OF rcp_spec_gb_red]
lemmas compl_conn_gb_red = compl_conn_rcp[OF rcp_spec_gb_red]

subsection \<open>Pair Selection\<close>

primrec gb_sel :: "('t, 'b::zero, 'c, 'd) selT" where
  "gb_sel gs bs [] data = []"|
  "gb_sel gs bs (p # ps) data = [p]"

lemma sel_spec_gb_sel: "sel_spec gb_sel"
proof (rule sel_specI)
  fix gs bs :: "('t, 'b, 'c) pdata list" and ps::"('t, 'b, 'c) pdata_pair list" and data::"nat \<times> 'd"
  assume "ps \<noteq> []"
  then obtain p ps' where ps: "ps = p # ps'" by (meson list.exhaust)
  show "gb_sel gs bs ps data \<noteq> [] \<and> set (gb_sel gs bs ps data) \<subseteq> set ps" by (simp add: ps)
qed

subsection \<open>Buchberger's Algorithm\<close>

lemma struct_spec_gb: "struct_spec gb_sel add_pairs_canon add_basis_canon gb_red"
  using sel_spec_gb_sel ap_spec_add_pairs_canon ab_spec_add_basis_sorted compl_struct_gb_red
  by (rule struct_specI)

definition gb_aux :: "('t, 'b, 'c) pdata list \<Rightarrow> nat \<times> nat \<times> 'd \<Rightarrow> ('t, 'b, 'c) pdata list \<Rightarrow>
                   ('t, 'b, 'c) pdata_pair list \<Rightarrow> ('t, 'b::field, 'c::default) pdata list"
  where "gb_aux = gb_schema_aux gb_sel add_pairs_canon add_basis_canon gb_red"

lemmas gb_aux_simps [code] = gb_schema_aux_simps[OF struct_spec_gb, folded gb_aux_def]

definition gb :: "('t, 'b, 'c) pdata' list \<Rightarrow> 'd \<Rightarrow> ('t, 'b::field, 'c::default) pdata' list"
  where "gb = gb_schema_direct gb_sel add_pairs_canon add_basis_canon gb_red"

lemmas gb_simps [code] = gb_schema_direct_def[of gb_sel add_pairs_canon add_basis_canon gb_red, folded gb_def gb_aux_def]

lemmas gb_isGB = gb_schema_direct_isGB[OF struct_spec_gb compl_conn_gb_red, folded gb_def]

lemmas gb_pmdl = gb_schema_direct_pmdl[OF struct_spec_gb compl_pmdl_gb_red, folded gb_def]

subsubsection \<open>Special Case: \<open>punit\<close>\<close>

lemma (in gd_term) struct_spec_gb_punit: "punit.struct_spec punit.gb_sel add_pairs_punit_canon punit.add_basis_canon punit.gb_red"
  using punit.sel_spec_gb_sel ap_spec_add_pairs_punit_canon ab_spec_add_basis_sorted punit.compl_struct_gb_red
  by (rule punit.struct_specI)

definition gb_aux_punit :: "('a, 'b, 'c) pdata list \<Rightarrow> nat \<times> nat \<times> 'd \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow>
                   ('a, 'b, 'c) pdata_pair list \<Rightarrow> ('a, 'b::field, 'c::default) pdata list"
  where "gb_aux_punit = punit.gb_schema_aux punit.gb_sel add_pairs_punit_canon punit.add_basis_canon punit.gb_red"

lemmas gb_aux_punit_simps [code] = punit.gb_schema_aux_simps[OF struct_spec_gb_punit, folded gb_aux_punit_def]

definition gb_punit :: "('a, 'b, 'c) pdata' list \<Rightarrow> 'd \<Rightarrow> ('a, 'b::field, 'c::default) pdata' list"
  where "gb_punit = punit.gb_schema_direct punit.gb_sel add_pairs_punit_canon punit.add_basis_canon punit.gb_red"

lemmas gb_punit_simps [code] = punit.gb_schema_direct_def[of "punit.gb_sel" add_pairs_punit_canon
                                "punit.add_basis_canon" "punit.gb_red", folded gb_punit_def gb_aux_punit_def]

lemmas gb_punit_isGB = punit.gb_schema_direct_isGB[OF struct_spec_gb_punit punit.compl_conn_gb_red, folded gb_punit_def]

lemmas gb_punit_pmdl = punit.gb_schema_direct_pmdl[OF struct_spec_gb_punit punit.compl_pmdl_gb_red, folded gb_punit_def]

end (* gd_term *)

end (* theory *)
