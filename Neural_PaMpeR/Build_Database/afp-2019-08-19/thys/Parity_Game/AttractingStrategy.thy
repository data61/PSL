section \<open>Attracting Strategies\<close>

theory AttractingStrategy
imports
  Main
  Strategy
begin

text \<open>Here we introduce the concept of attracting strategies.\<close>

context ParityGame begin

subsection \<open>Paths Visiting a Set\<close>

text \<open>A path that stays in \<open>A\<close> until eventually it visits \<open>W\<close>.\<close>
definition "visits_via P A W \<equiv> \<exists>n. enat n < llength P \<and> P $ n \<in> W \<and> lset (ltake (enat n) P) \<subseteq> A"

lemma visits_via_monotone: "\<lbrakk> visits_via P A W; A \<subseteq> A' \<rbrakk> \<Longrightarrow> visits_via P A' W"
  unfolding visits_via_def by blast

lemma visits_via_visits: "visits_via P A W \<Longrightarrow> lset P \<inter> W \<noteq> {}"
  unfolding visits_via_def by (meson disjoint_iff_not_equal in_lset_conv_lnth)

lemma (in vmc_path) visits_via_trivial: "v0 \<in> W \<Longrightarrow> visits_via P A W"
  unfolding visits_via_def apply (rule exI[of _ 0]) using zero_enat_def by auto

lemma visits_via_LCons:
  assumes "visits_via P A W"
  shows "visits_via (LCons v0 P) (insert v0 A) W"
proof-
  obtain n where n: "enat n < llength P" "P $ n \<in> W" "lset (ltake (enat n) P) \<subseteq> A"
    using assms unfolding visits_via_def by blast
  define P' where "P' = LCons v0 P"
  have "enat (Suc n) < llength P'" unfolding P'_def
    by (metis n(1) ldropn_Suc_LCons ldropn_Suc_conv_ldropn ldropn_eq_LConsD)
  moreover have "P' $ Suc n \<in> W" unfolding P'_def by (simp add: n(2))
  moreover have "lset (ltake (enat (Suc n)) P') \<subseteq> insert v0 A"
    using lset_ltake_Suc[of P' v0 n A] unfolding P'_def by (simp add: n(3))
  ultimately show ?thesis unfolding visits_via_def P'_def by blast
qed

lemma (in vmc_path_no_deadend) visits_via_ltl:
  assumes "visits_via P A W"
    and v0: "v0 \<notin> W"
  shows "visits_via (ltl P) A W"
proof-
  obtain n where n: "enat n < llength P" "P $ n \<in> W" "lset (ltake (enat n) P) \<subseteq> A"
    using assms(1)[unfolded visits_via_def] by blast
  have "n \<noteq> 0" using v0 n(2) DiffE by force
  then obtain n' where n': "Suc n' = n" using nat.exhaust by metis
  have "\<exists>n. enat n < llength (ltl P) \<and> (ltl P) $ n \<in> W \<and> lset (ltake (enat n) (ltl P)) \<subseteq> A"
    apply (rule exI[of _ n'])
    using n n' enat_Suc_ltl[of n' P] P_lnth_Suc lset_ltake_ltl[of n' P] by auto
  thus ?thesis using visits_via_def by blast
qed

lemma (in vm_path) visits_via_deadend:
  assumes "visits_via P A (deadends p)"
  shows "winning_path p** P"
  using assms visits_via_visits visits_deadend by blast

subsection \<open>Attracting Strategy from a Single Node\<close>

text \<open>
  All @{term \<sigma>}-paths starting from @{term v0} visit @{term W} and until then they stay in @{term A}.
\<close>
definition strategy_attracts_via :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "strategy_attracts_via p \<sigma> v0 A W \<equiv> \<forall>P. vmc_path G P v0 p \<sigma> \<longrightarrow> visits_via P A W"

lemma (in vmc_path) strategy_attracts_viaE:
  assumes "strategy_attracts_via p \<sigma> v0 A W"
  shows "visits_via P A W"
  using strategy_attracts_via_def assms vmc_path_axioms by blast

lemma (in vmc_path) strategy_attracts_via_SucE:
  assumes "strategy_attracts_via p \<sigma> v0 A W" "v0 \<notin> W"
  shows "\<exists>n. enat (Suc n) < llength P \<and> P $ Suc n \<in> W \<and> lset (ltake (enat (Suc n)) P) \<subseteq> A"
proof-
  obtain n where n: "enat n < llength P" "P $ n \<in> W" "lset (ltake (enat n) P) \<subseteq> A"
    using strategy_attracts_viaE[unfolded visits_via_def] assms(1) by blast
  have "n \<noteq> 0" using assms(2) n(2) by (metis P_0)
  thus ?thesis using n not0_implies_Suc by blast
qed

lemma (in vmc_path) strategy_attracts_via_lset:
  assumes "strategy_attracts_via p \<sigma> v0 A W"
  shows "lset P \<inter> W \<noteq> {}"
  using assms[THEN strategy_attracts_viaE, unfolded visits_via_def]
  by (meson disjoint_iff_not_equal lset_lnth_member subset_refl)

lemma strategy_attracts_via_v0:
  assumes \<sigma>: "strategy p \<sigma>" "strategy_attracts_via p \<sigma> v0 A W"
    and v0: "v0 \<in> V"
  shows "v0 \<in> A \<union> W"
proof-
  obtain P where "vmc_path G P v0 p \<sigma>" using strategy_conforming_path_exists_single assms by blast
  then interpret vmc_path G P v0 p \<sigma> .
  obtain n where n: "enat n < llength P" "P $ n \<in> W" "lset (ltake (enat n) P) \<subseteq> A"
    using \<sigma>(2)[unfolded strategy_attracts_via_def visits_via_def] vmc_path_axioms by blast
  show ?thesis proof (cases "n = 0")
    case True thus ?thesis using n(2) by simp
  next
    case False
    hence "lhd (ltake (enat n) P) = lhd P" by (simp add: enat_0_iff(1))
    hence "v0 \<in> lset (ltake (enat n) P)"
      by (metis \<open>n \<noteq> 0\<close> P_not_null P_v0 enat_0_iff(1) llist.set_sel(1) ltake.disc(2))
    thus ?thesis using n(3) by blast
  qed
qed
corollary strategy_attracts_not_outside:
  "\<lbrakk> v0 \<in> V - A - W; strategy p \<sigma> \<rbrakk> \<Longrightarrow> \<not>strategy_attracts_via p \<sigma> v0 A W"
  using strategy_attracts_via_v0 by blast


lemma strategy_attracts_viaI [intro]:
  assumes "\<And>P. vmc_path G P v0 p \<sigma> \<Longrightarrow> visits_via P A W"
  shows "strategy_attracts_via p \<sigma> v0 A W"
  unfolding strategy_attracts_via_def using assms by blast

lemma strategy_attracts_via_no_deadends:
  assumes "v \<in> V" "v \<in> A - W" "strategy_attracts_via p \<sigma> v A W"
  shows "\<not>deadend v"
proof
  assume "deadend v"
  define P where [simp]: "P = LCons v LNil"
  interpret vmc_path G P v p \<sigma> proof
    show "valid_path P" using \<open>v \<in> A - W\<close> \<open>v \<in> V\<close> valid_path_base' by auto
    show "maximal_path P" using \<open>deadend v\<close> by (simp add: maximal_path.intros(2))
    show "path_conforms_with_strategy p P \<sigma>" by (simp add: path_conforms_LCons_LNil)
  qed simp_all
  have "visits_via P A W" using assms(3) strategy_attracts_viaE by blast
  moreover have "llength P = eSuc 0" by simp
  ultimately have "P $ 0 \<in> W" by (simp add: enat_0_iff(1) visits_via_def)
  with \<open>v \<in> A - W\<close> show False by auto
qed

lemma attractor_strategy_on_extends:
  "\<lbrakk> strategy_attracts_via p \<sigma> v0 A W; A \<subseteq> A' \<rbrakk> \<Longrightarrow> strategy_attracts_via p \<sigma> v0 A' W"
  unfolding strategy_attracts_via_def using visits_via_monotone by blast

lemma strategy_attracts_via_trivial: "v0 \<in> W \<Longrightarrow> strategy_attracts_via p \<sigma> v0 A W"
proof
  fix P assume "v0 \<in> W" "vmc_path G P v0 p \<sigma>"
  then interpret vmc_path G P v0 p \<sigma> by blast
  show "visits_via P A W" using visits_via_trivial using \<open>v0 \<in> W\<close> by blast
qed

lemma strategy_attracts_via_successor:
  assumes \<sigma>: "strategy p \<sigma>" "strategy_attracts_via p \<sigma> v0 A W"
    and v0: "v0 \<in> A - W"
    and w0: "v0\<rightarrow>w0" "v0 \<in> VV p \<Longrightarrow> \<sigma> v0 = w0"
  shows "strategy_attracts_via p \<sigma> w0 A W"
proof
  fix P assume "vmc_path G P w0 p \<sigma>"
  then interpret vmc_path G P w0 p \<sigma> .
  define P' where [simp]: "P' = LCons v0 P"
  then interpret P': vmc_path G P' v0 p \<sigma>
    using extension_valid_maximal_conforming w0 by blast
  interpret P': vmc_path_no_deadend G P' v0 p \<sigma> using \<open>v0\<rightarrow>w0\<close> by unfold_locales blast
  have "visits_via P' A W" using \<sigma>(2) P'.strategy_attracts_viaE by blast
  thus "visits_via P A W" using P'.visits_via_ltl v0 by simp
qed

lemma strategy_attracts_VVp:
  assumes \<sigma>: "strategy p \<sigma>" "strategy_attracts_via p \<sigma> v0 A W"
    and v: "v0 \<in> A - W" "v0 \<in> VV p" "\<not>deadend v0"
  shows "\<sigma> v0 \<in> A \<union> W"
proof-
  have "v0\<rightarrow>\<sigma> v0" using \<sigma>(1)[unfolded strategy_def] v(2,3) by blast
  hence "strategy_attracts_via p \<sigma> (\<sigma> v0) A W"
    using strategy_attracts_via_successor \<sigma> v(1) by blast
  thus ?thesis using strategy_attracts_via_v0 \<open>v0\<rightarrow>\<sigma> v0\<close> \<sigma>(1) by blast
qed

lemma strategy_attracts_VVpstar:
  assumes "strategy p \<sigma>" "strategy_attracts_via p \<sigma> v0 A W"
    and "v0 \<in> A - W" "v0 \<notin> VV p" "w0 \<in> V - A - W"
  shows "\<not>v0 \<rightarrow> w0"
  by (metis assms strategy_attracts_not_outside strategy_attracts_via_successor)

subsection \<open>Attracting strategy from a set of nodes\<close>

text \<open>
  All @{term \<sigma>}-paths starting from @{term A} visit @{term W} and until then they stay in @{term A}.
\<close>
definition strategy_attracts :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "strategy_attracts p \<sigma> A W \<equiv> \<forall>v0 \<in> A. strategy_attracts_via p \<sigma> v0 A W"

lemma (in vmc_path) strategy_attractsE:
  assumes "strategy_attracts p \<sigma> A W" "v0 \<in> A"
  shows "visits_via P A W"
  using assms(1)[unfolded strategy_attracts_def] assms(2) strategy_attracts_viaE by blast

lemma strategy_attractsI [intro]:
  assumes "\<And>P v. \<lbrakk> v \<in> A; vmc_path G P v p \<sigma> \<rbrakk> \<Longrightarrow> visits_via P A W"
  shows "strategy_attracts p \<sigma> A W"
  unfolding strategy_attracts_def using assms by blast

lemma (in vmc_path) strategy_attracts_lset:
  assumes "strategy_attracts p \<sigma> A W" "v0 \<in> A"
  shows "lset P \<inter> W \<noteq> {}"
  using assms(1)[unfolded strategy_attracts_def] assms(2) strategy_attracts_via_lset(1)[of A W]
  by blast

lemma strategy_attracts_empty [simp]: "strategy_attracts p \<sigma> {} W" by blast

lemma strategy_attracts_invalid_path:
  assumes P: "P = LCons v (LCons w P')" "v \<in> A - W" "w \<notin> A \<union> W"
  shows "\<not>visits_via P A W" (is "\<not>?A")
proof
  assume ?A
  then obtain n where n: "enat n < llength P" "P $ n \<in> W" "lset (ltake (enat n) P) \<subseteq> A"
    unfolding visits_via_def by blast
  have "n \<noteq> 0" using \<open>v \<in> A - W\<close> n(2) P(1) DiffD2 by force
  moreover have "n \<noteq> Suc 0" using \<open>w \<notin> A \<union> W\<close> n(2) P(1) by auto
  ultimately have "Suc (Suc 0) \<le> n" by presburger
  hence "lset (ltake (enat (Suc (Suc 0))) P) \<subseteq> A" using n(3)
    by (meson contra_subsetD enat_ord_simps(1) lset_ltake_prefix lset_lnth_member lset_subset)
  moreover have "enat (Suc 0) < llength (ltake (eSuc (eSuc 0)) P)" proof-
    have *: "enat (Suc (Suc 0)) < llength P"
      using \<open>Suc (Suc 0) \<le> n\<close> n(1) by (meson enat_ord_simps(2) le_less_linear less_le_trans neq_iff)
    have "llength (ltake (enat (Suc (Suc 0))) P) = min (enat (Suc (Suc 0))) (llength P)" by simp
    hence "llength (ltake (enat (Suc (Suc 0))) P) = enat (Suc (Suc 0))"
      using * by (simp add: min_absorb1)
    thus ?thesis by (simp add: eSuc_enat zero_enat_def)
  qed
  ultimately have "ltake (enat (Suc (Suc 0))) P $ Suc 0 \<in> A" by (simp add: lset_lnth_member)
  hence "P $ Suc 0 \<in> A" by (simp add: lnth_ltake)
  thus False using P(1,3) by auto
qed

text \<open>
  If @{term A} is an attractor set of @{term W} and an edge leaves @{term A} without going through
  @{term W}, then @{term v} belongs to @{term "VV p"} and the attractor strategy @{term \<sigma>} avoids
  this edge.  All other cases give a contradiction.
\<close>
lemma strategy_attracts_does_not_leave:
  assumes \<sigma>: "strategy_attracts p \<sigma> A W" "strategy p \<sigma>"
    and v: "v\<rightarrow>w" "v \<in> A - W" "w \<notin> A \<union> W"
  shows "v \<in> VV p \<and> \<sigma> v \<noteq> w"
proof (rule ccontr)
  assume contra: "\<not>(v \<in> VV p \<and> \<sigma> v \<noteq> w)"
  (* Define a strategy for p** which tries to take this edge. *)
  define \<sigma>' where "\<sigma>' = \<sigma>_arbitrary(v := w)"
  hence "strategy p** \<sigma>'" using \<open>v\<rightarrow>w\<close> by (simp add: valid_strategy_updates)
  then obtain P where P: "vmc2_path G P v p \<sigma> \<sigma>'"
    using \<open>v\<rightarrow>w\<close> strategy_conforming_path_exists \<sigma>(2) by blast
  then interpret vmc2_path G P v p \<sigma> \<sigma>' .
  interpret vmc_path_no_deadend G P v p \<sigma> using \<open>v\<rightarrow>w\<close> by unfold_locales blast
  interpret comp: vmc_path_no_deadend G P v "p**" \<sigma>' using \<open>v\<rightarrow>w\<close> by unfold_locales blast
  have "w = w0" using contra \<sigma>'_def v0_conforms comp.v0_conforms by (cases "v \<in> VV p") auto
  hence "\<not>visits_via P A W"
    using strategy_attracts_invalid_path[of P v w "ltl (ltl P)"] v(2,3) P_LCons' by simp
  thus False by (meson DiffE \<sigma>(1) strategy_attractsE v(2))
qed

text \<open>
  Given an attracting strategy @{term \<sigma>}, we can turn every strategy @{term \<sigma>'} into an attracting
  strategy by overriding @{term \<sigma>'} on a suitable subset of the nodes.  This also means that
  an attracting strategy is still attracting if we override it outside of @{term "A - W"}.
\<close>
lemma strategy_attracts_irrelevant_override:
  assumes "strategy_attracts p \<sigma> A W" "strategy p \<sigma>" "strategy p \<sigma>'"
  shows "strategy_attracts p (override_on \<sigma>' \<sigma> (A - W)) A W"
proof (rule strategy_attractsI, rule ccontr)
  fix P v
  let ?\<sigma> = "override_on \<sigma>' \<sigma> (A - W)"
  assume "vmc_path G P v p ?\<sigma>"
  then interpret vmc_path G P v p ?\<sigma> .
  assume "v \<in> A"
  hence "P $ 0 \<in> A" using \<open>v \<in> A\<close> by simp
  moreover assume contra: "\<not>visits_via P A W"
  ultimately have "P $ 0 \<in> A - W" unfolding visits_via_def by (meson DiffI P_len not_less0 lset_ltake)
  have "\<not>lset P \<subseteq> A - W" proof
    assume "lset P \<subseteq> A - W"
    hence "\<And>v. v \<in> lset P \<Longrightarrow> override_on \<sigma>' \<sigma> (A - W) v = \<sigma> v" by auto
    hence "path_conforms_with_strategy p P \<sigma>"
      using path_conforms_with_strategy_irrelevant_updates[OF P_conforms] by blast
    hence "vmc_path G P (P $ 0) p \<sigma>"
      using conforms_to_another_strategy P_0 by blast
    thus False
      using contra \<open>P $ 0 \<in> A\<close> assms(1)
      by (meson vmc_path.strategy_attractsE)
  qed
  hence "\<exists>n. enat n < llength P \<and> P $ n \<notin> A - W" by (meson lset_subset)
  then obtain n where n: "enat n < llength P \<and> P $ n \<notin> A - W"
    "\<And>i. i < n \<Longrightarrow> \<not>(enat i < llength P \<and> P $ i \<notin> A - W)"
    using ex_least_nat_le[of "\<lambda>n. enat n < llength P \<and> P $ n \<notin> A - W"] by blast
  hence n_min: "\<And>i. i < n \<Longrightarrow> P $ i \<in> A - W"
    using dual_order.strict_trans enat_ord_simps(2) by blast
  have "n \<noteq> 0" using \<open>P $ 0 \<in> A - W\<close> n(1) by meson
  then obtain n' where n': "Suc n' = n" using not0_implies_Suc by blast
  hence "P $ n' \<in> A - W" using n_min by blast
  moreover have "P $ n' \<rightarrow> P $ Suc n'" using P_valid n(1) n' valid_path_edges by blast
  moreover have "P $ Suc n' \<notin> A \<union> W" proof-
    have "P $ n \<notin> W" using contra n(1) n_min unfolding visits_via_def
      by (meson Diff_subset lset_ltake subsetCE)
    thus ?thesis using n(1) n' by blast
  qed
  ultimately have "P $ n' \<in> VV p \<and> \<sigma> (P $ n') \<noteq> P $ Suc n'"
    using strategy_attracts_does_not_leave[of p \<sigma> A W "P $ n'" "P $ Suc n'"]
          assms(1,2) by blast
  thus False
    using n(1) n' vmc_path_conforms \<open>P $ n' \<in> A - W\<close> by (metis override_on_apply_in)
qed

lemma strategy_attracts_trivial [simp]: "strategy_attracts p \<sigma> W W"
  by (simp add: strategy_attracts_def strategy_attracts_via_trivial)

text \<open>If a @{term \<sigma>}-conforming path @{term P} hits an attractor @{term A}, it will visit @{term W}.\<close>
lemma (in vmc_path) attracted_path:
  assumes "W \<subseteq> V"
    and \<sigma>: "strategy_attracts p \<sigma> A W"
    and P_hits_A: "lset P \<inter> A \<noteq> {}"
  shows "lset P \<inter> W \<noteq> {}"
proof-
  obtain n where n: "enat n < llength P" "P $ n \<in> A" using P_hits_A by (meson lset_intersect_lnth)
  define P' where "P' = ldropn n P"
  interpret vmc_path G P' "P $ n" p \<sigma> unfolding P'_def using vmc_path_ldropn n(1) by blast
  have "visits_via P' A W" using \<sigma> n(2) strategy_attractsE by blast
  thus ?thesis unfolding P'_def using visits_via_visits in_lset_ldropnD[of _ n P] by blast
qed

lemma attracted_strategy_step:
  assumes \<sigma>: "strategy p \<sigma>" "strategy_attracts p \<sigma> A W"
    and v0: "\<not>deadend v0" "v0 \<in> A - W" "v0 \<in> VV p"
  shows "\<sigma> v0 \<in> A \<union> W"
  by (metis DiffD1 strategy_attracts_VVp assms strategy_attracts_def)

lemma (in vmc_path_no_deadend) attracted_path_step:
  assumes \<sigma>: "strategy_attracts p \<sigma> A W"
    and v0: "v0 \<in> A - W"
  shows "w0 \<in> A \<union> W"
  by (metis (no_types) DiffD1 P_LCons' \<sigma> strategy_attractsE strategy_attracts_invalid_path v0)

end \<comment> \<open>context ParityGame\<close>

end
