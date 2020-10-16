(* Author: Julian Brunner *)
(* This is originally a part of the CAVA model checker *)
theory Sequence_LTL
imports
  Sequence
  "HOL-Library.Linear_Temporal_Logic_on_Streams"
begin

  (* basics *)

  lemmas [iff] = ev_sconst alw_sconst ev_smap alw_smap hld_smap'

  lemmas [iff] = alw_ev_stl
  lemma alw_ev_sdrop[iff]: "alw (ev P) (sdrop n w) \<longleftrightarrow> alw (ev P) w"
    using alw_ev_sdrop alw_sdrop by blast
  lemma alw_ev_scons[iff]: "alw (ev P) (a ## w) \<longleftrightarrow> alw (ev P) w" by (metis alw_ev_stl stream.sel(2))
  lemma alw_ev_shift[iff]: "alw (ev P) (u @- v) \<longleftrightarrow> alw (ev P) v" by (induct u) (auto)

  lemmas [simp del, iff] = ev_alw_stl
  lemma ev_alw_sdrop[iff]: "ev (alw P) (sdrop n w) \<longleftrightarrow> ev (alw P) w"
    using alwD alw_alw alw_sdrop ev_alw_imp_alw_ev not_ev_iff by metis
  lemma ev_alw_scons[iff]: "ev (alw P) (a ## w) \<longleftrightarrow> ev (alw P) w" by (metis ev_alw_stl stream.sel(2))
  lemma ev_alw_shift[iff]: "ev (alw P) (u @- v) \<longleftrightarrow> ev (alw P) v" by (induct u) (auto)

  lemma HLD_sconst[iff]: "HLD A (sconst a) \<longleftrightarrow> a \<in> A" unfolding HLD_def by simp

  lemma ev_stl: "ev \<phi> (stl w) \<longleftrightarrow> (\<exists> u v. w = u @- v \<and> u \<noteq> [] \<and> \<phi> v)"
    by (metis ev.base ev_shift list.distinct(1) rotate1.simps(2) rotate1_is_Nil_conv
        sdrop.simps(2) sdrop_wait shift_simps(2) stake_Suc stake_sdrop
      )

  lemma ev_HLD_sset: "ev (HLD A) w \<longleftrightarrow> sset w \<inter> A \<noteq> {}" unfolding HLD_def ev_holds_sset by auto

  lemma alw_ev_coinduct[case_names alw_ev, consumes 1]:
    assumes "R w"
    assumes "\<And> w. R w \<Longrightarrow> ev \<phi> w \<and> ev R (stl w)"
    shows "alw (ev \<phi>) w"
  proof -
    have "ev R w" using assms(1) by rule
    then show ?thesis using assms(2) by (coinduct) (metis alw_sdrop not_ev_iff sdrop_stl sdrop_wait)
  qed

  (* acceptance conditions *)

  abbreviation "infs A w \<equiv> alw (ev (HLD A)) w"

  lemma infs_suffix: "infs A w \<longleftrightarrow> (\<forall> u v. w = u @- v \<longrightarrow> sset v \<inter> A \<noteq> {})"
    using alwD alw_iff_sdrop alw_shift ev_HLD_sset stake_sdrop by metis
  lemma infs_snth: "infs A w \<longleftrightarrow> (\<forall> n. \<exists> k \<ge> n. w !! k \<in> A)"
    by (auto simp: alw_iff_sdrop ev_iff_sdrop HLD_iff intro: le_add1 dest: le_Suc_ex)
  lemma infs_infm: "infs A w \<longleftrightarrow> (\<exists>\<^sub>\<infinity> i. w !! i \<in> A)"
    unfolding infs_snth INFM_nat_le by rule

  lemma infs_coinduct[case_names infs, coinduct pred: infs]:
    assumes "R w"
    assumes "\<And> w. R w \<Longrightarrow> \<exists> u v. w = u @- v \<and> set u \<inter> A \<noteq> {} \<and> R v"
    shows "infs A w"
    using assms by (coinduct rule: alw_ev_coinduct) (force simp: ev_HLD_sset ev_stl)
  lemma infs_flat_coinduct[case_names infs_flat, consumes 1]:
    assumes "R xss"
    assumes "\<And> xs xss. R (xs ## xss) \<Longrightarrow> set xs \<inter> A \<noteq> {} \<and> R xss"
    shows "infs A (flat xss)"
    using assms by (coinduction arbitrary: xss) (metis empty_set inf_bot_left flat_Stream stream.exhaust)

  lemma infs_supset[trans]: "infs A w \<Longrightarrow> sset w \<inter> A \<subseteq> B \<Longrightarrow> infs B w" unfolding infs_snth by force

  lemma infsI_sset: "sset w \<subseteq> A \<Longrightarrow> infs A w" unfolding infs_snth by force
  lemma infsD_sset: "infs A w \<Longrightarrow> sset w \<inter> A \<noteq> {}" unfolding ev_HLD_sset by auto

  lemma infs_sset[intro!, simp]: "infs (sset w) w" by (auto intro: infsI_sset)
  lemma infs_UNIV[intro!, simp]: "infs UNIV w" by (auto intro: infsI_sset)

  lemma infs_union[iff]: "infs (A \<union> B) w \<longleftrightarrow> infs A w \<or> infs B w"
    unfolding infs_snth by (auto) (meson le_trans nat_le_linear)

  lemma infs_cycle[iff]:
    assumes "w \<noteq> []"
    shows "infs A (cycle w) \<longleftrightarrow> set w \<inter> A \<noteq> {}"
  proof
    show "infs A (cycle w) \<Longrightarrow> set w \<inter> A \<noteq> {}"
      using assms by (auto simp: ev_HLD_sset dest: alwD)
    show "set w \<inter> A \<noteq> {} \<Longrightarrow> infs A (cycle w)"
      using assms by (coinduction rule: infs_coinduct) (blast dest: cycle_decomp)
  qed

end
