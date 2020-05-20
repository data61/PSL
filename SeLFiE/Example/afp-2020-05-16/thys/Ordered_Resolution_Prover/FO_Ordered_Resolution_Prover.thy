(*  Title:       An Ordered Resolution Prover for First-Order Clauses
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2016, 2017
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2014, 2017
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>An Ordered Resolution Prover for First-Order Clauses\<close>

theory FO_Ordered_Resolution_Prover
  imports FO_Ordered_Resolution
begin

text \<open>
This material is based on Section 4.3 (``A Simple Resolution Prover for First-Order Clauses'') of
Bachmair and Ganzinger's chapter. Specifically, it formalizes the RP prover defined in Figure 5 and
its related lemmas and theorems, including Lemmas 4.10 and 4.11 and Theorem 4.13 (completeness).
\<close>

(* FIXME: Used only twice, really -- inline? *)
definition is_least :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool" where
  "is_least P n \<longleftrightarrow> P n \<and> (\<forall>n' < n. \<not> P n')"

lemma least_exists: "P n \<Longrightarrow> \<exists>n. is_least P n"
  using exists_least_iff unfolding is_least_def by auto

text \<open>
The following corresponds to page 42 and 43 of Section 4.3, from the explanation of RP to
Lemma 4.10.
\<close>

type_synonym 'a state = "'a clause set \<times> 'a clause set \<times> 'a clause set"

locale FO_resolution_prover =
  FO_resolution subst_atm id_subst comp_subst renamings_apart atm_of_atms mgu less_atm +
  selection S
  for
    S :: "('a :: wellorder) clause \<Rightarrow> 'a clause" and
    subst_atm :: "'a \<Rightarrow> 's \<Rightarrow> 'a" and
    id_subst :: "'s" and
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's" and
    renamings_apart :: "'a clause list \<Rightarrow> 's list" and
    atm_of_atms :: "'a list \<Rightarrow> 'a" and
    mgu :: "'a set set \<Rightarrow> 's option" and
    less_atm :: "'a \<Rightarrow> 'a \<Rightarrow> bool" +
  assumes
    sel_stable: "\<And>\<rho> C. is_renaming \<rho> \<Longrightarrow> S (C \<cdot> \<rho>) = S C \<cdot> \<rho>" and
    less_atm_ground: "is_ground_atm A \<Longrightarrow> is_ground_atm B \<Longrightarrow> less_atm A B \<Longrightarrow> A < B"
begin

fun N_of_state :: "'a state \<Rightarrow> 'a clause set" where
  "N_of_state (N, P, Q) = N"

fun P_of_state :: "'a state \<Rightarrow> 'a clause set" where
  "P_of_state (N, P, Q) = P"

text \<open>
\<open>O\<close> denotes relation composition in Isabelle, so the formalization uses \<open>Q\<close> instead.
\<close>

fun Q_of_state :: "'a state \<Rightarrow> 'a clause set" where
  "Q_of_state (N, P, Q) = Q"

definition clss_of_state :: "'a state \<Rightarrow> 'a clause set" where
  "clss_of_state St = N_of_state St \<union> P_of_state St \<union> Q_of_state St"

abbreviation grounding_of_state :: "'a state \<Rightarrow> 'a clause set" where
  "grounding_of_state St \<equiv> grounding_of_clss (clss_of_state St)"

interpretation ord_FO_resolution: inference_system "ord_FO_\<Gamma> S" .

text \<open>
The following inductive predicate formalizes the resolution prover in Figure 5.
\<close>

inductive RP :: "'a state \<Rightarrow> 'a state \<Rightarrow> bool" (infix "\<leadsto>" 50) where
  tautology_deletion: "Neg A \<in># C \<Longrightarrow> Pos A \<in># C \<Longrightarrow> (N \<union> {C}, P, Q) \<leadsto> (N, P, Q)"
| forward_subsumption: "D \<in> P \<union> Q \<Longrightarrow> subsumes D C \<Longrightarrow> (N \<union> {C}, P, Q) \<leadsto> (N, P, Q)"
| backward_subsumption_P: "D \<in> N \<Longrightarrow> strictly_subsumes D C \<Longrightarrow> (N, P \<union> {C}, Q) \<leadsto> (N, P, Q)"
| backward_subsumption_Q: "D \<in> N \<Longrightarrow> strictly_subsumes D C \<Longrightarrow> (N, P, Q \<union> {C}) \<leadsto> (N, P, Q)"
| forward_reduction: "D + {#L'#} \<in> P \<union> Q \<Longrightarrow> - L = L' \<cdot>l \<sigma> \<Longrightarrow> D \<cdot> \<sigma> \<subseteq># C \<Longrightarrow>
    (N \<union> {C + {#L#}}, P, Q) \<leadsto> (N \<union> {C}, P, Q)"
| backward_reduction_P: "D + {#L'#} \<in> N \<Longrightarrow> - L = L' \<cdot>l \<sigma> \<Longrightarrow> D \<cdot> \<sigma> \<subseteq># C \<Longrightarrow>
    (N, P \<union> {C + {#L#}}, Q) \<leadsto> (N, P \<union> {C}, Q)"
| backward_reduction_Q: "D + {#L'#} \<in> N \<Longrightarrow> - L = L' \<cdot>l \<sigma> \<Longrightarrow> D \<cdot> \<sigma> \<subseteq># C \<Longrightarrow>
    (N, P, Q \<union> {C + {#L#}}) \<leadsto> (N, P \<union> {C}, Q)"
| clause_processing: "(N \<union> {C}, P, Q) \<leadsto> (N, P \<union> {C}, Q)"
| inference_computation: "N = concls_of (ord_FO_resolution.inferences_between Q C) \<Longrightarrow>
    ({}, P \<union> {C}, Q) \<leadsto> (N, P, Q \<union> {C})"

lemma final_RP: "\<not> ({}, {}, Q) \<leadsto> St"
  by (auto elim: RP.cases)

definition Sup_state :: "'a state llist \<Rightarrow> 'a state" where
  "Sup_state Sts =
   (Sup_llist (lmap N_of_state Sts), Sup_llist (lmap P_of_state Sts),
    Sup_llist (lmap Q_of_state Sts))"

definition Liminf_state :: "'a state llist \<Rightarrow> 'a state" where
  "Liminf_state Sts =
   (Liminf_llist (lmap N_of_state Sts), Liminf_llist (lmap P_of_state Sts),
    Liminf_llist (lmap Q_of_state Sts))"

context
  fixes Sts Sts' :: "'a state llist"
  assumes Sts: "lfinite Sts" "lfinite Sts'" "\<not> lnull Sts" "\<not> lnull Sts'" "llast Sts' = llast Sts"
begin

lemma
  N_of_Liminf_state_fin: "N_of_state (Liminf_state Sts') = N_of_state (Liminf_state Sts)" and
  P_of_Liminf_state_fin: "P_of_state (Liminf_state Sts') = P_of_state (Liminf_state Sts)" and
  Q_of_Liminf_state_fin: "Q_of_state (Liminf_state Sts') = Q_of_state (Liminf_state Sts)"
  using Sts by (simp_all add: Liminf_state_def lfinite_Liminf_llist llast_lmap)

lemma Liminf_state_fin: "Liminf_state Sts' = Liminf_state Sts"
  using N_of_Liminf_state_fin P_of_Liminf_state_fin Q_of_Liminf_state_fin
  by (simp add: Liminf_state_def)

end

context
  fixes Sts Sts' :: "'a state llist"
  assumes Sts: "\<not> lfinite Sts" "emb Sts Sts'"
begin

lemma
  N_of_Liminf_state_inf: "N_of_state (Liminf_state Sts') \<subseteq> N_of_state (Liminf_state Sts)" and
  P_of_Liminf_state_inf: "P_of_state (Liminf_state Sts') \<subseteq> P_of_state (Liminf_state Sts)" and
  Q_of_Liminf_state_inf: "Q_of_state (Liminf_state Sts') \<subseteq> Q_of_state (Liminf_state Sts)"
  using Sts by (simp_all add: Liminf_state_def emb_Liminf_llist_infinite emb_lmap)

lemma clss_of_Liminf_state_inf:
  "clss_of_state (Liminf_state Sts') \<subseteq> clss_of_state (Liminf_state Sts)"
  unfolding clss_of_state_def
  using N_of_Liminf_state_inf P_of_Liminf_state_inf Q_of_Liminf_state_inf by blast

end

definition fair_state_seq :: "'a state llist \<Rightarrow> bool" where
  "fair_state_seq Sts \<longleftrightarrow> N_of_state (Liminf_state Sts) = {} \<and> P_of_state (Liminf_state Sts) = {}"

text \<open>
The following formalizes Lemma 4.10.
\<close>

context
  fixes
    Sts :: "'a state llist"
  assumes
    deriv: "chain (\<leadsto>) Sts" and
    empty_Q0: "Q_of_state (lhd Sts) = {}" 
    (* FIXME: make hypothesis empty_Q0 more local---and is it really needed? *)
begin

lemmas lhd_lmap_Sts = llist.map_sel(1)[OF chain_not_lnull[OF deriv]]

definition S_Q :: "'a clause \<Rightarrow> 'a clause" where
  "S_Q = S_M S (Q_of_state (Liminf_state Sts))"

interpretation sq: selection S_Q
  unfolding S_Q_def using S_M_selects_subseteq S_M_selects_neg_lits selection_axioms
  by unfold_locales auto

interpretation gr: ground_resolution_with_selection S_Q
  by unfold_locales

interpretation sr: standard_redundancy_criterion_reductive gr.ord_\<Gamma>
  by unfold_locales

interpretation sr: standard_redundancy_criterion_counterex_reducing gr.ord_\<Gamma>
  "ground_resolution_with_selection.INTERP S_Q"
  by unfold_locales

text \<open>
The extension of ordered resolution mentioned in 4.10. We let it consist of all sound rules.
\<close>

definition ground_sound_\<Gamma>:: "'a inference set" where
  "ground_sound_\<Gamma> = {Infer CC D E | CC D E. (\<forall>I. I \<Turnstile>m CC \<longrightarrow> I \<Turnstile> D \<longrightarrow> I \<Turnstile> E)}"

text \<open>
We prove that we indeed defined an extension.
\<close>

lemma gd_ord_\<Gamma>_ngd_ord_\<Gamma>: "gr.ord_\<Gamma> \<subseteq> ground_sound_\<Gamma>"
  unfolding ground_sound_\<Gamma>_def using gr.ord_\<Gamma>_def gr.ord_resolve_sound by fastforce

lemma sound_ground_sound_\<Gamma>: "sound_inference_system ground_sound_\<Gamma>"
  unfolding sound_inference_system_def ground_sound_\<Gamma>_def by auto

lemma sat_preserving_ground_sound_\<Gamma>: "sat_preserving_inference_system ground_sound_\<Gamma>"
  using sound_ground_sound_\<Gamma> sat_preserving_inference_system.intro
    sound_inference_system.\<Gamma>_sat_preserving by blast

definition sr_ext_Ri :: "'a clause set \<Rightarrow> 'a inference set" where
  "sr_ext_Ri N = sr.Ri N \<union> (ground_sound_\<Gamma> - gr.ord_\<Gamma>)"

interpretation sr_ext:
  sat_preserving_redundancy_criterion "ground_sound_\<Gamma>" "sr.Rf" "sr_ext_Ri"
  unfolding sat_preserving_redundancy_criterion_def sr_ext_Ri_def
  using sat_preserving_ground_sound_\<Gamma> redundancy_criterion_standard_extension gd_ord_\<Gamma>_ngd_ord_\<Gamma>
    sr.redundancy_criterion_axioms by auto

lemma strict_subset_subsumption_redundant_clause:
  assumes
    sub: "D \<cdot> \<sigma> \<subset># C" and
    ground_\<sigma>: "is_ground_subst \<sigma>"
  shows "C \<in> sr.Rf (grounding_of_cls D)"
proof -
  from sub have "\<forall>I. I \<Turnstile> D \<cdot> \<sigma> \<longrightarrow> I \<Turnstile> C"
    unfolding true_cls_def by blast
  moreover have "C > D \<cdot> \<sigma>"
    using sub by (simp add: subset_imp_less_mset)
  moreover have "D \<cdot> \<sigma> \<in> grounding_of_cls D"
    using ground_\<sigma> by (metis (mono_tags, lifting) mem_Collect_eq substitution_ops.grounding_of_cls_def)
  ultimately have "set_mset {#D \<cdot> \<sigma>#} \<subseteq> grounding_of_cls D" 
    "(\<forall>I. I \<Turnstile>m {#D \<cdot> \<sigma>#} \<longrightarrow> I \<Turnstile> C)"
    "(\<forall>D'. D' \<in># {#D \<cdot> \<sigma>#} \<longrightarrow> D' < C)"
    by auto
  then show ?thesis
    using sr.Rf_def by blast
qed

lemma strict_subset_subsumption_redundant_clss:
  assumes
    "D \<cdot> \<sigma> \<subset># C" and
    "is_ground_subst \<sigma>" and
    "D \<in> CC"
  shows "C \<in> sr.Rf (grounding_of_clss CC)"
  using assms
proof -
  have "C \<in> sr.Rf (grounding_of_cls D)"
    using strict_subset_subsumption_redundant_clause assms by auto
  then show ?thesis
    using assms unfolding clss_of_state_def grounding_of_clss_def
    by (metis (no_types) sr.Rf_mono sup_ge1 SUP_absorb contra_subsetD)
qed

lemma strict_subset_subsumption_grounding_redundant_clss:
  assumes 
    D\<sigma>_subset_C: "D \<cdot> \<sigma> \<subset># C" and
    D_in_St: "D \<in> CC"
  shows "grounding_of_cls C \<subseteq> sr.Rf (grounding_of_clss CC)"
proof
  fix C\<mu>
  assume "C\<mu> \<in> grounding_of_cls C"
  then obtain \<mu> where
    \<mu>_p: "C\<mu> = C \<cdot> \<mu> \<and> is_ground_subst \<mu>"
    unfolding grounding_of_cls_def by auto
  have D\<sigma>\<mu>C\<mu>: "D \<cdot> \<sigma> \<cdot> \<mu> \<subset># C \<cdot> \<mu>"
    using D\<sigma>_subset_C subst_subset_mono by auto
  then show "C\<mu> \<in> sr.Rf (grounding_of_clss CC)"
    using \<mu>_p strict_subset_subsumption_redundant_clss[of D "\<sigma> \<odot> \<mu>" "C \<cdot> \<mu>"] D_in_St 
    unfolding clss_of_state_def by auto
qed

lemma subst_cls_eq_grounding_of_cls_subset_eq:
  assumes "D \<cdot> \<sigma> = C"
  shows "grounding_of_cls C \<subseteq> grounding_of_cls D"
proof
  fix C\<sigma>'
  assume "C\<sigma>' \<in> grounding_of_cls C"
  then obtain \<sigma>' where
    C\<sigma>': "C \<cdot> \<sigma>' = C\<sigma>'" "is_ground_subst \<sigma>'"
    unfolding grounding_of_cls_def by auto
  then have "C \<cdot> \<sigma>' = D \<cdot> \<sigma> \<cdot> \<sigma>' \<and> is_ground_subst (\<sigma> \<odot> \<sigma>')"
    using assms by auto
  then show "C\<sigma>' \<in> grounding_of_cls D"
    unfolding grounding_of_cls_def using C\<sigma>'(1) by force
qed

lemma derive_if_remove_subsumed:
  assumes 
    "D \<in> clss_of_state St" and  
    "subsumes D C"
  shows "sr_ext.derive (grounding_of_state St \<union> grounding_of_cls C) (grounding_of_state St)"
proof -
  from assms obtain \<sigma> where
    "D \<cdot> \<sigma> = C \<or> D \<cdot> \<sigma> \<subset># C"
    by (auto simp: subsumes_def subset_mset_def)
  then have "D \<cdot> \<sigma> = C \<or> D \<cdot> \<sigma> \<subset># C"
    by (simp add: subset_mset_def)
  then show ?thesis
  proof
    assume "D \<cdot> \<sigma> = C"
    then have "grounding_of_cls C \<subseteq> grounding_of_cls D"
      using subst_cls_eq_grounding_of_cls_subset_eq by simp
    then have "(grounding_of_state St \<union> grounding_of_cls C) = grounding_of_state St"
      using assms unfolding clss_of_state_def grounding_of_clss_def by auto
    then show ?thesis
      by (auto intro: sr_ext.derive.intros)
  next
    assume a: "D \<cdot> \<sigma> \<subset># C"
    then have "grounding_of_cls C \<subseteq> sr.Rf (grounding_of_state St)"
      using strict_subset_subsumption_grounding_redundant_clss assms by auto
    then show ?thesis
      unfolding clss_of_state_def grounding_of_clss_def by (force intro: sr_ext.derive.intros)
  qed
qed

(* FIXME: better name *)
lemma reduction_in_concls_of:
  assumes 
    "C\<mu> \<in> grounding_of_cls C" and
    "D + {#L'#} \<in> CC" and
    "- L = L' \<cdot>l \<sigma>" and
    "D \<cdot> \<sigma> \<subseteq># C"
  shows "C\<mu> \<in> concls_of (sr_ext.inferences_from (grounding_of_clss (CC \<union> {C + {#L#}})))"
proof -
  from assms 
  obtain \<mu> where
    \<mu>_p: "C\<mu> = C \<cdot> \<mu> \<and> is_ground_subst \<mu>"
    unfolding grounding_of_cls_def by auto

  define \<gamma> where
    "\<gamma> = Infer {#(C + {#L#})\<cdot> \<mu>#} ((D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu>) (C \<cdot> \<mu>)"

  have "(D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu> \<in> grounding_of_clss (CC \<union> {C + {#L#}})"
    unfolding grounding_of_clss_def grounding_of_cls_def 
    by (rule UN_I[of "D + {#L'#}"], use assms(2) clss_of_state_def in simp,
        metis (mono_tags, lifting) \<mu>_p is_ground_comp_subst mem_Collect_eq subst_cls_comp_subst)
  moreover have "(C + {#L#}) \<cdot> \<mu> \<in> grounding_of_clss (CC \<union> {C + {#L#}})"
    using \<mu>_p unfolding  grounding_of_clss_def grounding_of_cls_def by auto
  moreover have "\<forall>I. I \<Turnstile> D \<cdot> \<sigma> \<cdot> \<mu> + {#- (L  \<cdot>l \<mu>)#} \<longrightarrow> I \<Turnstile> C  \<cdot> \<mu> + {#L  \<cdot>l \<mu>#} \<longrightarrow> I \<Turnstile> D \<cdot> \<sigma> \<cdot> \<mu> + C \<cdot> \<mu>"
    by auto
  then have "\<forall>I. I \<Turnstile> (D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu> \<longrightarrow> I \<Turnstile> (C + {#L#}) \<cdot> \<mu> \<longrightarrow> I \<Turnstile> D \<cdot> \<sigma> \<cdot> \<mu> + C \<cdot> \<mu>"
    using assms
    by (metis add_mset_add_single subst_cls_add_mset subst_cls_union subst_minus) 
  then have "\<forall>I. I \<Turnstile> (D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu> \<longrightarrow> I \<Turnstile> (C + {#L#}) \<cdot> \<mu> \<longrightarrow> I \<Turnstile> C \<cdot> \<mu>"
    using assms by (metis (no_types, lifting) subset_mset.le_iff_add subst_cls_union true_cls_union)
  then have "\<forall>I. I \<Turnstile>m {#(D + {#L'#}) \<cdot> \<sigma> \<cdot> \<mu>#} \<longrightarrow> I \<Turnstile> (C + {#L#}) \<cdot> \<mu> \<longrightarrow> I \<Turnstile> C \<cdot> \<mu>"
    by (meson true_cls_mset_singleton)
  ultimately have "\<gamma> \<in> sr_ext.inferences_from (grounding_of_clss (CC \<union> {C + {#L#}}))"
    unfolding sr_ext.inferences_from_def unfolding ground_sound_\<Gamma>_def infer_from_def \<gamma>_def by auto
  then have "C \<cdot> \<mu> \<in> concls_of (sr_ext.inferences_from (grounding_of_clss (CC \<union> {C + {#L#}})))"
    using image_iff unfolding \<gamma>_def by fastforce
  then show "C\<mu> \<in> concls_of (sr_ext.inferences_from (grounding_of_clss (CC \<union> {C + {#L#}})))"
    using \<mu>_p by auto
qed

lemma reduction_derivable:
  assumes
    "D + {#L'#} \<in> CC" and
    "- L = L' \<cdot>l \<sigma>" and
    "D \<cdot> \<sigma> \<subseteq># C"
  shows "sr_ext.derive (grounding_of_clss (CC \<union> {C + {#L#}})) (grounding_of_clss (CC \<union> {C}))"
proof -
  from assms have "grounding_of_clss (CC \<union> {C}) - grounding_of_clss (CC \<union> {C + {#L#}}) 
    \<subseteq> concls_of (sr_ext.inferences_from (grounding_of_clss (CC \<union> {C + {#L#}})))"
    using reduction_in_concls_of unfolding grounding_of_clss_def clss_of_state_def 
    by auto
  moreover
  have "grounding_of_cls (C + {#L#}) \<subseteq> sr.Rf (grounding_of_clss (CC \<union> {C}))"
    using strict_subset_subsumption_grounding_redundant_clss[of C "id_subst"]
    by auto
  then have "grounding_of_clss (CC \<union> {C + {#L#}}) - grounding_of_clss (CC \<union> {C}) 
    \<subseteq> sr.Rf (grounding_of_clss (CC \<union> {C}))"
    unfolding clss_of_state_def grounding_of_clss_def by auto
  ultimately show "sr_ext.derive (grounding_of_clss (CC \<union> {C + {#L#}}))  (grounding_of_clss (CC \<union> {C}))"
    using sr_ext.derive.intros[of "grounding_of_clss (CC \<union> {C})" 
        "grounding_of_clss (CC \<union> {C + {#L#}})"]
    by auto
qed

text \<open>
The following corresponds the part of Lemma 4.10 that states we have a theorem proving process:
\<close>

lemma RP_ground_derive:
  "St \<leadsto> St' \<Longrightarrow> sr_ext.derive (grounding_of_state St) (grounding_of_state St')"
proof (induction rule: RP.induct)
  case (tautology_deletion A C N P Q)
  {
    fix C\<sigma>
    assume "C\<sigma> \<in> grounding_of_cls C"
    then obtain \<sigma> where
      "C\<sigma> = C \<cdot> \<sigma>"
      unfolding grounding_of_cls_def by auto
    then have "Neg (A \<cdot>a \<sigma>) \<in># C\<sigma> \<and> Pos (A \<cdot>a \<sigma>) \<in># C\<sigma>"
      using tautology_deletion Neg_Melem_subst_atm_subst_cls Pos_Melem_subst_atm_subst_cls by auto
    then have "C\<sigma> \<in> sr.Rf (grounding_of_state (N, P, Q))"
      using sr.tautology_redundant by auto
  }
  then have "grounding_of_state (N \<union> {C}, P, Q) - grounding_of_state (N, P, Q)
    \<subseteq> sr.Rf (grounding_of_state (N, P, Q))"
    unfolding clss_of_state_def grounding_of_clss_def by auto
  moreover have "grounding_of_state (N, P, Q) - grounding_of_state (N \<union> {C}, P, Q) = {}"
    unfolding clss_of_state_def grounding_of_clss_def by auto
  ultimately show ?case
    using sr_ext.derive.intros[of "grounding_of_state (N, P, Q)" "grounding_of_state (N \<union> {C}, P, Q)"]
    by auto
next
  case (forward_subsumption D P Q C N)
  then show ?case
    using derive_if_remove_subsumed[of D "(N, P, Q)" C] unfolding grounding_of_clss_def clss_of_state_def
    by (simp add: sup_commute sup_left_commute)
next
  case (backward_subsumption_P D N C P Q)
  then show ?case
    using derive_if_remove_subsumed[of D "(N, P, Q)" C] strictly_subsumes_def unfolding grounding_of_clss_def clss_of_state_def
    by (simp add: sup_commute sup_left_commute)
next
  case (backward_subsumption_Q D N C P Q)
  then show ?case
    using derive_if_remove_subsumed[of D "(N, P, Q)" C] strictly_subsumes_def unfolding grounding_of_clss_def clss_of_state_def
    by (simp add: sup_commute sup_left_commute)
next
  case (forward_reduction D L' P Q L \<sigma> C N)
  then show ?case
    using reduction_derivable[of _ _ "N \<union> P \<union> Q"] unfolding clss_of_state_def by force
next
  case (backward_reduction_P D L' N L \<sigma> C P Q)
  then show ?case
    using reduction_derivable[of _ _ "N \<union> P \<union> Q"] unfolding clss_of_state_def by force
next
  case (backward_reduction_Q D L' N L \<sigma> C P Q)
  then show ?case
    using reduction_derivable[of _ _ "N \<union> P \<union> Q"] unfolding clss_of_state_def by force
next
  case (clause_processing N C P Q)
  then show ?case
    unfolding clss_of_state_def using sr_ext.derive.intros by auto
next
  case (inference_computation N Q C P)
  {
    fix E\<mu>
    assume "E\<mu> \<in> grounding_of_clss N"
    then obtain \<mu> E where
      E_\<mu>_p: "E\<mu> = E \<cdot> \<mu> \<and> E \<in> N \<and> is_ground_subst \<mu>"
      unfolding grounding_of_clss_def grounding_of_cls_def by auto
    then have E_concl: "E \<in> concls_of (ord_FO_resolution.inferences_between Q C)"
      using inference_computation by auto
    then obtain \<gamma> where
      \<gamma>_p: "\<gamma> \<in> ord_FO_\<Gamma> S \<and> infer_from (Q \<union> {C}) \<gamma> \<and> C \<in># prems_of \<gamma> \<and> concl_of \<gamma> = E"
      unfolding ord_FO_resolution.inferences_between_def by auto
    then obtain CC CAs D AAs As \<sigma> where
      \<gamma>_p2: "\<gamma> = Infer CC D E \<and> ord_resolve_rename S CAs D AAs As \<sigma> E \<and> mset CAs = CC"
      unfolding ord_FO_\<Gamma>_def by auto
    define \<rho> where
      "\<rho> = hd (renamings_apart (D # CAs))"
    define \<rho>s where
      "\<rho>s = tl (renamings_apart (D # CAs))"
    define \<gamma>_ground where
      "\<gamma>_ground = Infer (mset (CAs \<cdot>\<cdot>cl \<rho>s) \<cdot>cm \<sigma> \<cdot>cm \<mu>) (D \<cdot> \<rho> \<cdot> \<sigma> \<cdot> \<mu>) (E \<cdot> \<mu>)"
    have "\<forall>I. I \<Turnstile>m mset (CAs \<cdot>\<cdot>cl \<rho>s) \<cdot>cm \<sigma> \<cdot>cm \<mu> \<longrightarrow> I \<Turnstile> D \<cdot> \<rho> \<cdot> \<sigma> \<cdot> \<mu> \<longrightarrow> I \<Turnstile> E \<cdot> \<mu>"
      using ord_resolve_rename_ground_inst_sound[of _ _ _ _ _ _ _ _ _ _ \<mu>] \<rho>_def \<rho>s_def E_\<mu>_p \<gamma>_p2
      by auto
    then have "\<gamma>_ground \<in> {Infer cc d e | cc d e. \<forall>I. I \<Turnstile>m cc \<longrightarrow> I \<Turnstile> d \<longrightarrow> I \<Turnstile> e}"
      unfolding \<gamma>_ground_def by auto
    moreover have "set_mset (prems_of \<gamma>_ground) \<subseteq> grounding_of_state ({}, P \<union> {C}, Q)"
    proof -
      have "D = C \<or> D \<in> Q"
        unfolding \<gamma>_ground_def using E_\<mu>_p \<gamma>_p2 \<gamma>_p unfolding infer_from_def
        unfolding clss_of_state_def grounding_of_clss_def
        unfolding grounding_of_cls_def
        by simp
      then have "D \<cdot> \<rho> \<cdot> \<sigma> \<cdot> \<mu> \<in> grounding_of_cls C \<or> (\<exists>x \<in> Q. D \<cdot> \<rho> \<cdot> \<sigma> \<cdot> \<mu> \<in> grounding_of_cls x)"
        using E_\<mu>_p
        unfolding grounding_of_cls_def 
        by (metis (mono_tags, lifting) is_ground_comp_subst mem_Collect_eq subst_cls_comp_subst)
      then have "(D \<cdot> \<rho> \<cdot> \<sigma> \<cdot> \<mu> \<in> grounding_of_cls C \<or> 
        (\<exists>x \<in> P. D \<cdot> \<rho> \<cdot> \<sigma> \<cdot> \<mu> \<in> grounding_of_cls x) \<or> 
        (\<exists>x \<in> Q. D \<cdot> \<rho> \<cdot> \<sigma> \<cdot> \<mu> \<in> grounding_of_cls x))"
        by metis
      moreover have "\<forall>i < length (CAs \<cdot>\<cdot>cl \<rho>s \<cdot>cl \<sigma> \<cdot>cl \<mu>). ((CAs \<cdot>\<cdot>cl \<rho>s \<cdot>cl \<sigma> \<cdot>cl \<mu>) ! i) \<in> 
        {C \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>} \<union> 
        ((\<Union>C \<in> P. {C \<cdot> \<sigma> | \<sigma>. is_ground_subst \<sigma>}) \<union> (\<Union>C\<in>Q. {C \<cdot> \<sigma> | \<sigma>. is_ground_subst \<sigma>}))"
      proof (rule, rule)
        fix i
        assume "i < length (CAs \<cdot>\<cdot>cl \<rho>s \<cdot>cl \<sigma> \<cdot>cl \<mu>)"
        then have a: "i < length CAs \<and> i < length \<rho>s"
          by simp
        moreover from a have "CAs ! i \<in> {C} \<union> Q"
          using \<gamma>_p2 \<gamma>_p unfolding infer_from_def
          by (metis (no_types, lifting) Un_subset_iff inference.sel(1) set_mset_union 
              sup_commute nth_mem_mset subsetCE)
        ultimately have "(CAs \<cdot>\<cdot>cl \<rho>s \<cdot>cl \<sigma> \<cdot>cl \<mu>) ! i \<in> 
          {C \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>} \<or> 
          ((CAs \<cdot>\<cdot>cl \<rho>s \<cdot>cl \<sigma> \<cdot>cl \<mu>) ! i \<in> (\<Union>C\<in>P. {C \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>}) \<or> 
          (CAs \<cdot>\<cdot>cl \<rho>s \<cdot>cl \<sigma> \<cdot>cl \<mu>) ! i \<in> (\<Union>C \<in> Q. {C \<cdot> \<sigma> | \<sigma>. is_ground_subst \<sigma>}))"
          unfolding \<gamma>_ground_def using E_\<mu>_p \<gamma>_p2 \<gamma>_p unfolding infer_from_def
          unfolding clss_of_state_def grounding_of_clss_def
          unfolding grounding_of_cls_def
          apply -
          apply (cases "CAs ! i = C")
          subgoal
            apply (rule disjI1)
            apply (rule Set.CollectI)
            apply (rule_tac x="(\<rho>s ! i) \<odot> \<sigma> \<odot> \<mu>" in exI)
            using \<rho>s_def using renamings_apart_length apply (auto;fail)
            done
          subgoal
            apply (rule disjI2)
            apply (rule disjI2)
            apply (rule_tac a="CAs ! i" in UN_I)
            subgoal
              apply blast
              done
            subgoal
              apply (rule Set.CollectI)
              apply (rule_tac x="(\<rho>s ! i) \<odot> \<sigma> \<odot> \<mu>" in exI)
              using \<rho>s_def using renamings_apart_length apply (auto;fail)
              done
            done
          done
        then show "(CAs \<cdot>\<cdot>cl \<rho>s \<cdot>cl \<sigma> \<cdot>cl \<mu>) ! i \<in> {C \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>} \<union> 
          ((\<Union>C \<in> P. {C \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>}) \<union> (\<Union>C \<in> Q. {C \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>}))"
          by blast
      qed
      then have "\<forall>x \<in># mset (CAs \<cdot>\<cdot>cl \<rho>s \<cdot>cl \<sigma> \<cdot>cl \<mu>). x \<in> {C \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>} \<union> 
        ((\<Union>C \<in> P. {C \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>}) \<union> (\<Union>C \<in> Q. {C \<cdot> \<sigma> |\<sigma>. is_ground_subst \<sigma>}))"
        by (metis (lifting) in_set_conv_nth set_mset_mset)
      then have "set_mset (mset (CAs \<cdot>\<cdot>cl \<rho>s) \<cdot>cm \<sigma> \<cdot>cm \<mu>) \<subseteq> 
        grounding_of_cls C \<union> grounding_of_clss P \<union> grounding_of_clss Q"
        unfolding grounding_of_cls_def grounding_of_clss_def
        using mset_subst_cls_list_subst_cls_mset by auto
      ultimately show ?thesis
        unfolding \<gamma>_ground_def clss_of_state_def grounding_of_clss_def by auto
    qed
    ultimately have "E \<cdot> \<mu> \<in> concls_of (sr_ext.inferences_from (grounding_of_state ({}, P \<union> {C}, Q)))"
      unfolding sr_ext.inferences_from_def inference_system.inferences_from_def ground_sound_\<Gamma>_def infer_from_def
      using \<gamma>_ground_def by (metis (no_types, lifting) imageI inference.sel(3) mem_Collect_eq)
    then have "E\<mu> \<in> concls_of (sr_ext.inferences_from (grounding_of_state ({}, P \<union> {C}, Q)))"
      using E_\<mu>_p by auto
  }
  then have "grounding_of_state (N, P, Q \<union> {C}) - grounding_of_state ({}, P \<union> {C}, Q) 
    \<subseteq> concls_of (sr_ext.inferences_from (grounding_of_state ({}, P \<union> {C}, Q)))"
    unfolding clss_of_state_def grounding_of_clss_def by auto
  moreover have "grounding_of_state ({}, P \<union> {C}, Q) - grounding_of_state (N, P, Q \<union> {C}) = {}"
    unfolding clss_of_state_def grounding_of_clss_def by auto
  ultimately show ?case
    using sr_ext.derive.intros[of "(grounding_of_state (N, P, Q \<union> {C}))" 
        "(grounding_of_state ({}, P \<union> {C}, Q))"] by auto
qed

text \<open>
A useful consequence:
\<close>

theorem RP_model:
  "St \<leadsto> St' \<Longrightarrow> I \<Turnstile>s grounding_of_state St' \<longleftrightarrow> I \<Turnstile>s grounding_of_state St"
proof (drule RP_ground_derive, erule sr_ext.derive.cases, hypsubst)
  let
    ?gSt = "grounding_of_state St" and
    ?gSt' = "grounding_of_state St'"

  assume
    deduct: "?gSt' - ?gSt \<subseteq> concls_of (sr_ext.inferences_from ?gSt)" (is "_ \<subseteq> ?concls") and
    delete: "?gSt - ?gSt' \<subseteq> sr.Rf ?gSt'"

  show "I \<Turnstile>s ?gSt' \<longleftrightarrow> I \<Turnstile>s ?gSt"
  proof
    assume bef: "I \<Turnstile>s ?gSt"
    then have "I \<Turnstile>s ?concls"
      unfolding ground_sound_\<Gamma>_def inference_system.inferences_from_def true_clss_def true_cls_mset_def
      by (auto simp add: image_def infer_from_def dest!: spec[of _ I])
    then have diff: "I \<Turnstile>s ?gSt' - ?gSt"
      using deduct by (blast intro: true_clss_mono)
    then show "I \<Turnstile>s ?gSt'"
      using bef unfolding true_clss_def by blast
  next
    assume aft: "I \<Turnstile>s ?gSt'"
    have "I \<Turnstile>s ?gSt' \<union> sr.Rf ?gSt'"
      by (rule sr.Rf_model) (metis aft sr.Rf_mono[OF Un_upper1] Diff_eq_empty_iff Diff_subset
          Un_Diff true_clss_mono true_clss_union)
    then have "I \<Turnstile>s sr.Rf ?gSt'"
      using true_clss_union by blast
    then have diff: "I \<Turnstile>s ?gSt - ?gSt'"
      using delete by (blast intro: true_clss_mono)
    then show "I \<Turnstile>s ?gSt"
      using aft unfolding true_clss_def by blast
  qed
qed

text \<open>
Another formulation of the part of Lemma 4.10 that states we have a theorem proving process:
\<close>

(* FIXME: rename *)
lemma RP_ground_derive_chain:
  "chain sr_ext.derive (lmap grounding_of_state Sts)"
  using deriv RP_ground_derive by (simp add: chain_lmap[of "(\<leadsto>)"])

text \<open>
The following is used prove to Lemma 4.11:
\<close>

lemma in_Sup_llist_in_nth: "C \<in> Sup_llist Gs \<Longrightarrow> \<exists>j. enat j < llength Gs \<and> C \<in> lnth Gs j"
  unfolding Sup_llist_def by auto
    \<comment> \<open>Note: Gs is called Ns in the chapter\<close>

lemma Sup_llist_grounding_of_state_ground:
  assumes "C \<in> Sup_llist (lmap grounding_of_state Sts)"
  shows "is_ground_cls C"
proof -
  have "\<exists>j. enat j < llength (lmap grounding_of_state Sts) \<and> C \<in> lnth (lmap grounding_of_state Sts) j"
    using assms in_Sup_llist_in_nth by metis
  then obtain j where
    "enat j < llength (lmap grounding_of_state Sts)"
    "C \<in> lnth (lmap grounding_of_state Sts) j"
    by blast
  then show ?thesis
    unfolding grounding_of_clss_def grounding_of_cls_def by auto
qed

lemma Liminf_grounding_of_state_ground:
  "C \<in> Liminf_llist (lmap grounding_of_state Sts) \<Longrightarrow> is_ground_cls C"
  using Liminf_llist_subset_Sup_llist[of "lmap grounding_of_state Sts"]
    Sup_llist_grounding_of_state_ground
  by blast

lemma in_Sup_llist_in_Sup_state:
  assumes "C \<in> Sup_llist (lmap grounding_of_state Sts)"
  shows "\<exists>D \<sigma>. D \<in> clss_of_state (Sup_state Sts) \<and> D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>"
proof -
  from assms obtain i where
    i_p: "enat i < llength Sts \<and> C \<in> lnth (lmap grounding_of_state Sts) i"
    using in_Sup_llist_in_nth by fastforce
  then obtain D \<sigma> where
    "D \<in> clss_of_state (lnth Sts i) \<and> D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>"
    using assms unfolding grounding_of_clss_def grounding_of_cls_def by fastforce
  then have "D \<in> clss_of_state (Sup_state Sts) \<and> D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>"
    using i_p unfolding Sup_state_def clss_of_state_def
    by (metis (no_types, lifting) UnCI UnE contra_subsetD N_of_state.simps P_of_state.simps
        Q_of_state.simps llength_lmap lnth_lmap lnth_subset_Sup_llist)
  then show ?thesis
    by auto
qed

lemma
  N_of_state_Liminf: "N_of_state (Liminf_state Sts) = Liminf_llist (lmap N_of_state Sts)" and
  P_of_state_Liminf: "P_of_state (Liminf_state Sts) = Liminf_llist (lmap P_of_state Sts)"
  unfolding Liminf_state_def by auto

lemma eventually_removed_from_N:
  assumes
    d_in: "D \<in> N_of_state (lnth Sts i)" and
    fair: "fair_state_seq Sts" and
    i_Sts: "enat i < llength Sts"
  shows "\<exists>l. D \<in> N_of_state (lnth Sts l) \<and> D \<notin> N_of_state (lnth Sts (Suc l)) \<and> i \<le> l \<and> enat (Suc l) < llength Sts"
proof (rule ccontr)
  assume a: "\<not> ?thesis"
  have "i \<le> l \<Longrightarrow> enat l < llength Sts \<Longrightarrow> D \<in> N_of_state (lnth Sts l)" for l
    using d_in by (induction l, blast, metis a Suc_ile_eq le_SucE less_imp_le)
  then have "D \<in> Liminf_llist (lmap N_of_state Sts)"
    unfolding Liminf_llist_def using i_Sts by auto
  then show False
    using fair unfolding fair_state_seq_def by (simp add: N_of_state_Liminf)
qed

lemma eventually_removed_from_P:
  assumes
    d_in: "D \<in> P_of_state (lnth Sts i)" and
    fair: "fair_state_seq Sts" and
    i_Sts: "enat i < llength Sts"
  shows "\<exists>l. D \<in> P_of_state (lnth Sts l) \<and> D \<notin> P_of_state (lnth Sts (Suc l)) \<and> i \<le> l \<and> enat (Suc l) < llength Sts"
proof (rule ccontr)
  assume a: "\<not> ?thesis"
  have "i \<le> l \<Longrightarrow> enat l < llength Sts \<Longrightarrow> D \<in> P_of_state (lnth Sts l)" for l
    using d_in by (induction l, blast, metis a Suc_ile_eq le_SucE less_imp_le)
  then have "D \<in> Liminf_llist (lmap P_of_state Sts)"
    unfolding Liminf_llist_def using i_Sts by auto
  then show False
    using fair unfolding fair_state_seq_def by (simp add: P_of_state_Liminf)
qed

(* FIXME: come up with a better name *)
lemma instance_if_subsumed_and_in_limit:
  assumes
    ns: "Gs = lmap grounding_of_state Sts" and
    c: "C \<in> Liminf_llist Gs - sr.Rf (Liminf_llist Gs)" and
    (* FIXME: use clss_of_state below *)
    d: "D \<in> N_of_state (lnth Sts i) \<union> P_of_state (lnth Sts i) \<union> Q_of_state (lnth Sts i)" 
      "enat i < llength Sts" "subsumes D C"
  shows "\<exists>\<sigma>. D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>"
proof -
  let ?Ps = "\<lambda>i. P_of_state (lnth Sts i)"
  let ?Qs = "\<lambda>i. Q_of_state (lnth Sts i)"

  have ground_C: "is_ground_cls C"
    using c using Liminf_grounding_of_state_ground ns by auto

  have derivns: "chain sr_ext.derive Gs"
    using RP_ground_derive_chain deriv ns by auto

  have "\<exists>\<sigma>. D \<cdot> \<sigma> = C"
  proof (rule ccontr)
    assume "\<nexists>\<sigma>. D \<cdot> \<sigma> = C"
    moreover from d(3) obtain \<tau>_proto where
      "D \<cdot> \<tau>_proto \<subseteq># C" unfolding subsumes_def
      by blast
    then obtain \<tau> where
      \<tau>_p: "D \<cdot> \<tau> \<subseteq># C \<and> is_ground_subst \<tau>"
      using ground_C by (metis is_ground_cls_mono make_ground_subst subset_mset.order_refl)
    ultimately have subsub: "D \<cdot> \<tau> \<subset># C"
      using subset_mset.le_imp_less_or_eq by auto
    moreover have "is_ground_subst \<tau>"
      using \<tau>_p by auto
    moreover have "D \<in> clss_of_state (lnth Sts i)"
      using d unfolding clss_of_state_def by auto
    ultimately have "C \<in> sr.Rf (grounding_of_state (lnth Sts i))"
      using strict_subset_subsumption_redundant_clss by auto
    then have "C \<in> sr.Rf (Sup_llist Gs)"
      using d ns by (metis contra_subsetD llength_lmap lnth_lmap lnth_subset_Sup_llist sr.Rf_mono)
    then have "C \<in> sr.Rf (Liminf_llist Gs)"
      unfolding ns using local.sr_ext.Rf_limit_Sup derivns ns by auto
    then show False
      using c by auto
  qed
  then obtain \<sigma> where
    "D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>"
    using ground_C by (metis make_ground_subst)
  then show ?thesis
    by auto
qed

lemma from_Q_to_Q_inf:
  assumes
    fair: "fair_state_seq Sts" and
    ns: "Gs = lmap grounding_of_state Sts" and
    c: "C \<in> Liminf_llist Gs - sr.Rf (Liminf_llist Gs)" and
    d: "D \<in> Q_of_state (lnth Sts i)" "enat i < llength Sts" "subsumes D C" and
    d_least: "\<forall>E \<in> {E. E \<in> (clss_of_state (Sup_state Sts)) \<and> subsumes E C}. \<not> strictly_subsumes E D"
  shows "D \<in> Q_of_state (Liminf_state Sts)"
proof -
  let ?Ps = "\<lambda>i. P_of_state (lnth Sts i)"
  let ?Qs = "\<lambda>i. Q_of_state (lnth Sts i)"

  have ground_C: "is_ground_cls C"
    using c using Liminf_grounding_of_state_ground ns by auto

  have derivns: "chain sr_ext.derive Gs"
    using RP_ground_derive_chain deriv ns by auto

  have "\<exists>\<sigma>. D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>"
    using instance_if_subsumed_and_in_limit ns c d by blast
  then obtain \<sigma> where
    \<sigma>: "D \<cdot> \<sigma> = C" "is_ground_subst \<sigma>"
    by auto

  have in_Sts_in_Sts_Suc:
    "\<forall>l \<ge> i. enat (Suc l) < llength Sts \<longrightarrow> D \<in> Q_of_state (lnth Sts l) \<longrightarrow> D \<in> Q_of_state (lnth Sts (Suc l))"
  proof (rule, rule, rule, rule)
    fix l
    assume
      len: "i \<le> l" and
      llen: "enat (Suc l) < llength Sts" and
      d_in_q: "D \<in> Q_of_state (lnth Sts l)"

    have "lnth Sts l \<leadsto> lnth Sts (Suc l)"
      using llen deriv chain_lnth_rel by blast
    then show "D \<in> Q_of_state (lnth Sts (Suc l))"
    proof (cases rule: RP.cases)
      case (backward_subsumption_Q D' N D_removed P Q)
      moreover
      {
        assume "D_removed = D"
        then obtain D_subsumes where
          D_subsumes_p: "D_subsumes \<in> N \<and> strictly_subsumes D_subsumes D"
          using backward_subsumption_Q by auto
        moreover from D_subsumes_p have "subsumes D_subsumes C"
          using d subsumes_trans unfolding strictly_subsumes_def by blast
        moreover from backward_subsumption_Q have "D_subsumes \<in> clss_of_state (Sup_state Sts)"
          using D_subsumes_p llen
          by (metis (no_types) UnI1 clss_of_state_def N_of_state.simps llength_lmap lnth_lmap 
              lnth_subset_Sup_llist rev_subsetD Sup_state_def)
        ultimately have False
          using d_least unfolding subsumes_def by auto
      }
      ultimately show ?thesis
        using d_in_q by auto
    next
      case (backward_reduction_Q E L' N L \<sigma> D' P Q)
      {
        assume "D' + {#L#} = D"
        then have D'_p: "strictly_subsumes D' D \<and> D' \<in> ?Ps (Suc l)"
          using subset_strictly_subsumes[of D' D] backward_reduction_Q by auto
        then have subc: "subsumes D' C"
          using d(3) subsumes_trans unfolding strictly_subsumes_def by auto
        from D'_p have "D' \<in> clss_of_state (Sup_state Sts)"
          using llen by (metis (no_types) UnI1 clss_of_state_def P_of_state.simps llength_lmap
              lnth_lmap lnth_subset_Sup_llist subsetCE sup_ge2 Sup_state_def)
        then have False
          using d_least D'_p subc by auto
      }
      then show ?thesis
        using backward_reduction_Q d_in_q by auto
    qed (use d_in_q in auto)
  qed
  have D_in_Sts: "D \<in> Q_of_state (lnth Sts l)" and D_in_Sts_Suc: "D \<in> Q_of_state (lnth Sts (Suc l))"
    if l_i: "l \<ge> i" and enat: "enat (Suc l) < llength Sts" for l
  proof -
    show "D \<in> Q_of_state (lnth Sts l)"
      using l_i enat
      apply (induction "l - i" arbitrary: l)
      subgoal using d by auto
      subgoal using d(1) in_Sts_in_Sts_Suc
        by (metis (no_types, lifting) Suc_ile_eq add_Suc_right add_diff_cancel_left' le_SucE
            le_Suc_ex less_imp_le)
      done
    then show "D \<in> Q_of_state (lnth Sts (Suc l))"
      using l_i enat in_Sts_in_Sts_Suc by blast
  qed
  have "i \<le> x \<Longrightarrow> enat x < llength Sts \<Longrightarrow> D \<in> Q_of_state (lnth Sts x)" for x
    apply (cases x)
    subgoal using d(1) by (auto intro!: exI[of _ i] simp: less_Suc_eq)
    subgoal for x'
      using d(1) D_in_Sts_Suc[of x'] by (cases \<open>i \<le> x'\<close>) (auto simp: not_less_eq_eq)
    done
  then have "D \<in> Liminf_llist (lmap Q_of_state Sts)"
    unfolding Liminf_llist_def by (auto intro!: exI[of _ i] simp: d)
  then show ?thesis
    unfolding Liminf_state_def by auto
qed

lemma from_P_to_Q:
  assumes
    fair: "fair_state_seq Sts" and
    ns: "Gs = lmap grounding_of_state Sts" and
    c: "C \<in> Liminf_llist Gs - sr.Rf (Liminf_llist Gs)" and
    d: "D \<in> P_of_state (lnth Sts i)" "enat i < llength Sts" "subsumes D C" and
    d_least: "\<forall>E \<in> {E. E \<in> (clss_of_state (Sup_state Sts)) \<and> subsumes E C}. \<not> strictly_subsumes E D"
  shows "\<exists>l. D \<in> Q_of_state (lnth Sts l) \<and> enat l < llength Sts"
proof -
  let ?Ns = "\<lambda>i. N_of_state (lnth Sts i)"
  let ?Ps = "\<lambda>i. P_of_state (lnth Sts i)"
  let ?Qs = "\<lambda>i. Q_of_state (lnth Sts i)"

  have ground_C: "is_ground_cls C"
    using c using Liminf_grounding_of_state_ground ns by auto

  have derivns: "chain sr_ext.derive Gs"
    using RP_ground_derive_chain deriv ns by auto

  have "\<exists>\<sigma>. D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>"
    using instance_if_subsumed_and_in_limit ns c d by blast
  then obtain \<sigma> where
    \<sigma>: "D \<cdot> \<sigma> = C" "is_ground_subst \<sigma>"
    by auto

  obtain l where
    l_p: "D \<in> P_of_state (lnth Sts l) \<and> D \<notin> P_of_state (lnth Sts (Suc l)) \<and> i \<le> l \<and> enat (Suc l) < llength Sts"
    using fair using eventually_removed_from_P d unfolding ns by auto
  then have l_Gs: "enat (Suc l) < llength Gs"
    using ns by auto
  from l_p have "lnth Sts l \<leadsto> lnth Sts (Suc l)"
    using deriv using chain_lnth_rel by auto
  then show ?thesis
  proof (cases rule: RP.cases)
    case (backward_subsumption_P D' N D_twin P Q)
    note lrhs = this(1,2) and D'_p = this(3,4)
    then have twins: "D_twin = D" "?Ns (Suc l) = N" "?Ns l = N"  "?Ps (Suc l) = P" 
      "?Ps l = P \<union> {D_twin}" "?Qs (Suc l) = Q" "?Qs l = Q"
      using l_p by auto
    note D'_p = D'_p[unfolded twins(1)]
    then have subc: "subsumes D' C"
      unfolding strictly_subsumes_def subsumes_def using \<sigma>
      by (metis subst_cls_comp_subst subst_cls_mono_mset)
    from D'_p have "D' \<in> clss_of_state (Sup_state Sts)"
      unfolding twins(2)[symmetric] using l_p
      by (metis (no_types) UnI1 clss_of_state_def N_of_state.simps llength_lmap lnth_lmap
          lnth_subset_Sup_llist subsetCE Sup_state_def)
    then have False
      using d_least D'_p subc by auto
    then show ?thesis
      by auto
  next
    case (backward_reduction_P E L' N L \<sigma> D' P Q)
    then have twins: "D' + {#L#} = D" "?Ns (Suc l) = N" "?Ns l = N"  "?Ps (Suc l) = P \<union> {D'}" 
      "?Ps l = P \<union> {D' + {#L#}}" "?Qs (Suc l) = Q" "?Qs l = Q"
      using l_p by auto
    then have D'_p: "strictly_subsumes D' D \<and> D' \<in> ?Ps (Suc l)"
      using subset_strictly_subsumes[of D' D] by auto
    then have subc: "subsumes D' C"
      using d(3) subsumes_trans unfolding strictly_subsumes_def by auto
    from D'_p have "D' \<in> clss_of_state (Sup_state Sts)"
      using l_p by (metis (no_types) UnI1 clss_of_state_def P_of_state.simps llength_lmap lnth_lmap
          lnth_subset_Sup_llist subsetCE sup_ge2 Sup_state_def)
    then have False
      using d_least D'_p subc by auto
    then show ?thesis
      by auto
  next
    case (inference_computation N Q D_twin P)
    then have twins: "D_twin = D" "?Ps (Suc l) = P" "?Ps l = P \<union> {D_twin}" 
      "?Qs (Suc l) = Q \<union> {D_twin}" "?Qs l = Q"
      using l_p by auto
    then show ?thesis
      using d \<sigma> l_p by auto
  qed (use l_p in auto)
qed

lemma variants_sym: "variants D D' \<longleftrightarrow> variants D' D"
  unfolding variants_def by auto

lemma variants_imp_exists_subtitution: "variants D D' \<Longrightarrow> \<exists>\<sigma>. D \<cdot> \<sigma> = D'"
  unfolding variants_iff_subsumes subsumes_def
  by (meson strictly_subsumes_def subset_mset_def strict_subset_subst_strictly_subsumes subsumes_def)

lemma properly_subsume_variants:
  assumes "strictly_subsumes E D" and "variants D D'"
  shows "strictly_subsumes E D'"
proof -
  from assms obtain \<sigma> \<sigma>' where
    \<sigma>_\<sigma>'_p: "D \<cdot> \<sigma> = D' \<and> D' \<cdot> \<sigma>' = D"
    using variants_imp_exists_subtitution variants_sym by metis

  from assms obtain \<sigma>'' where
    "E \<cdot> \<sigma>'' \<subseteq># D"
    unfolding strictly_subsumes_def subsumes_def by auto
  then have "E \<cdot> \<sigma>'' \<cdot> \<sigma> \<subseteq># D \<cdot> \<sigma>"
    using subst_cls_mono_mset by blast
  then have "E \<cdot> (\<sigma>'' \<odot> \<sigma>)  \<subseteq># D'"
    using \<sigma>_\<sigma>'_p by auto
  moreover from assms have n: "(\<nexists>\<sigma>. D \<cdot> \<sigma> \<subseteq># E)"
    unfolding strictly_subsumes_def subsumes_def by auto
  have "\<nexists>\<sigma>. D' \<cdot> \<sigma> \<subseteq># E"
  proof
    assume "\<exists>\<sigma>'''. D' \<cdot> \<sigma>''' \<subseteq># E"
    then obtain \<sigma>''' where
      "D' \<cdot> \<sigma>''' \<subseteq># E"
      by auto
    then have "D \<cdot> (\<sigma> \<odot> \<sigma>''') \<subseteq># E"
      using \<sigma>_\<sigma>'_p by auto
    then show False
      using n by metis
  qed
  ultimately show ?thesis
    unfolding strictly_subsumes_def subsumes_def by metis
qed

lemma neg_properly_subsume_variants:
  assumes "\<not> strictly_subsumes E D" and "variants D D'"
  shows "\<not> strictly_subsumes E D'"
  using assms properly_subsume_variants variants_sym by auto

lemma from_N_to_P_or_Q:
  assumes
    fair: "fair_state_seq Sts" and
    ns: "Gs = lmap grounding_of_state Sts" and
    c: "C \<in> Liminf_llist Gs - sr.Rf (Liminf_llist Gs)" and
    d: "D \<in> N_of_state (lnth Sts i)" "enat i < llength Sts" "subsumes D C" and
    d_least: "\<forall>E \<in> {E. E \<in> (clss_of_state (Sup_state Sts)) \<and> subsumes E C}. \<not> strictly_subsumes E D"
  shows "\<exists>l D' \<sigma>'. D' \<in> P_of_state (lnth Sts l) \<union> Q_of_state (lnth Sts l) \<and> 
    enat l < llength Sts \<and> 
    (\<forall>E \<in> {E. E \<in> (clss_of_state (Sup_state Sts)) \<and> subsumes E C}. \<not> strictly_subsumes E D') \<and> 
    D' \<cdot> \<sigma>' = C \<and> is_ground_subst \<sigma>' \<and> subsumes D' C"
proof -
  let ?Ns = "\<lambda>i. N_of_state (lnth Sts i)"
  let ?Ps = "\<lambda>i. P_of_state (lnth Sts i)"
  let ?Qs = "\<lambda>i. Q_of_state (lnth Sts i)"

  have ground_C: "is_ground_cls C"
    using c using Liminf_grounding_of_state_ground ns by auto

  have derivns: "chain sr_ext.derive Gs"
    using RP_ground_derive_chain deriv ns by auto

  have "\<exists>\<sigma>. D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>"
    using instance_if_subsumed_and_in_limit ns c d by blast
  then obtain \<sigma> where
    \<sigma>: "D \<cdot> \<sigma> = C" "is_ground_subst \<sigma>"
    by auto

  from c have no_taut: "\<not> (\<exists>A. Pos A \<in># C \<and> Neg A \<in># C)"
    using sr.tautology_redundant by auto

  have "\<exists>l. D \<in> N_of_state (lnth Sts l) \<and> D \<notin> N_of_state (lnth Sts (Suc l)) \<and> i \<le> l \<and> enat (Suc l) < llength Sts"
    using fair using eventually_removed_from_N d unfolding ns by auto
  then obtain l where
    l_p: "D \<in> N_of_state (lnth Sts l) \<and> D \<notin> N_of_state (lnth Sts (Suc l)) \<and> i \<le> l \<and> enat (Suc l) < llength Sts"
    by auto
  then have l_Gs: "enat (Suc l) < llength Gs"
    using ns by auto
  from l_p have "lnth Sts l \<leadsto> lnth Sts (Suc l)"
    using deriv using chain_lnth_rel by auto
  then show ?thesis
  proof (cases rule: RP.cases)
    case (tautology_deletion A D_twin N P Q)
    then have "D_twin = D"
      using l_p by auto
    then have "Pos (A \<cdot>a \<sigma>) \<in># C \<and> Neg (A \<cdot>a \<sigma>) \<in># C"
      using tautology_deletion(3,4) \<sigma>
      by (metis Melem_subst_cls eql_neg_lit_eql_atm eql_pos_lit_eql_atm)
    then have False
      using no_taut by metis
    then show ?thesis
      by blast
  next
    case (forward_subsumption D' P Q D_twin N)
    note lrhs = this(1,2) and D'_p = this(3,4)
    then have twins: "D_twin = D" "?Ns (Suc l) = N" "?Ns l = N \<union> {D_twin}"  "?Ps (Suc l) = P " 
      "?Ps l = P" "?Qs (Suc l) = Q" "?Qs l = Q"
      using l_p by auto
    note D'_p = D'_p[unfolded twins(1)]
    from D'_p(2) have subs: "subsumes D' C"
      using d(3) by (blast intro: subsumes_trans)
    moreover have "D' \<in> clss_of_state (Sup_state Sts)"
      using twins D'_p l_p unfolding clss_of_state_def Sup_state_def
      by simp (metis (no_types) contra_subsetD llength_lmap lnth_lmap lnth_subset_Sup_llist)
    ultimately have "\<not> strictly_subsumes D' D"
      using d_least by auto
    then have "subsumes D D'"
      unfolding strictly_subsumes_def using D'_p by auto
    then have v: "variants D D'"
      using D'_p unfolding variants_iff_subsumes by auto
    then have mini: "\<forall>E \<in> {E \<in> clss_of_state (Sup_state Sts). subsumes E C}. \<not> strictly_subsumes E D'"
      using d_least D'_p neg_properly_subsume_variants[of _ D D'] by auto

    from v have "\<exists>\<sigma>'. D' \<cdot> \<sigma>' = C"
      using \<sigma> variants_imp_exists_subtitution variants_sym by (metis subst_cls_comp_subst)
    then have "\<exists>\<sigma>'. D' \<cdot> \<sigma>' = C \<and> is_ground_subst \<sigma>'"
      using ground_C by (meson make_ground_subst refl)
    then obtain \<sigma>' where
      \<sigma>'_p: "D' \<cdot> \<sigma>' = C \<and> is_ground_subst \<sigma>'"
      by metis

    show ?thesis
      using D'_p twins l_p subs mini \<sigma>'_p by auto
  next
    case (forward_reduction E L' P Q L \<sigma> D' N)
    then have twins: "D' + {#L#} = D" "?Ns (Suc l) = N \<union> {D'}" "?Ns l = N \<union> {D' + {#L#}}" 
      "?Ps (Suc l) = P " "?Ps l = P" "?Qs (Suc l) = Q" "?Qs l = Q"
      using l_p by auto
    then have D'_p: "strictly_subsumes D' D \<and> D' \<in> ?Ns (Suc l)"
      using subset_strictly_subsumes[of D' D] by auto
    then have subc: "subsumes D' C"
      using d(3) subsumes_trans unfolding strictly_subsumes_def by blast
    from D'_p have "D' \<in> clss_of_state (Sup_state Sts)"
      using l_p by (metis (no_types) UnI1 clss_of_state_def N_of_state.simps llength_lmap lnth_lmap
          lnth_subset_Sup_llist subsetCE Sup_state_def)
    then have False
      using d_least D'_p subc by auto
    then show ?thesis
      by auto
  next
    case (clause_processing N D_twin P Q)
    then have twins:  "D_twin = D" "?Ns (Suc l) = N" "?Ns l = N \<union> {D}"  "?Ps (Suc l) = P \<union> {D}" 
      "?Ps l = P" "?Qs (Suc l) = Q" "?Qs l = Q"
      using l_p by auto
    then show ?thesis
      using d \<sigma> l_p d_least by blast
  qed (use l_p in auto)
qed

lemma eventually_in_Qinf:
  assumes
    D_p: "D \<in> clss_of_state (Sup_state Sts)"
      "subsumes D C" "\<forall>E \<in> {E. E \<in> (clss_of_state (Sup_state Sts)) \<and> subsumes E C}. \<not> strictly_subsumes E D" and
    fair: "fair_state_seq Sts" and
    (* We could also, we guess, in this proof obtain a D with property D_p(3) from one with only properties D_p(2,3). *)
    ns: "Gs = lmap grounding_of_state Sts" and
    c: "C \<in> Liminf_llist Gs - sr.Rf (Liminf_llist Gs)" and
    ground_C: "is_ground_cls C"
  shows "\<exists>D' \<sigma>'. D' \<in> Q_of_state (Liminf_state Sts) \<and> D' \<cdot> \<sigma>' = C \<and> is_ground_subst \<sigma>'"
proof -
  let ?Ns = "\<lambda>i. N_of_state (lnth Sts i)"
  let ?Ps = "\<lambda>i. P_of_state (lnth Sts i)"
  let ?Qs = "\<lambda>i. Q_of_state (lnth Sts i)"

  from D_p obtain i where
    i_p: "i < llength Sts" "D \<in> ?Ns i \<or> D \<in> ?Ps i \<or> D \<in> ?Qs i"
    unfolding clss_of_state_def Sup_state_def
    by simp_all (metis (no_types) in_Sup_llist_in_nth llength_lmap lnth_lmap)

  have derivns: "chain sr_ext.derive Gs" using RP_ground_derive_chain deriv ns by auto

  have "\<exists>\<sigma>. D \<cdot> \<sigma> = C \<and> is_ground_subst \<sigma>"
    using instance_if_subsumed_and_in_limit[OF ns c] D_p i_p by blast
  then obtain \<sigma> where
    \<sigma>: "D \<cdot> \<sigma> = C" "is_ground_subst \<sigma>"
    by blast

  {
    assume a: "D \<in> ?Ns i"
    then obtain D' \<sigma>' l where D'_p:
      "D' \<in> ?Ps l \<union> ?Qs l"
      "D' \<cdot> \<sigma>' = C"
      "enat l < llength Sts"
      "is_ground_subst \<sigma>'"
      "\<forall>E \<in> {E. E \<in> (clss_of_state (Sup_state Sts)) \<and> subsumes E C}. \<not> strictly_subsumes E D'"
      "subsumes D' C"
      using from_N_to_P_or_Q deriv fair ns c i_p(1) D_p(2) D_p(3) by blast
    then obtain l' where
      l'_p: "D' \<in> ?Qs l'" "l' < llength Sts"
      using from_P_to_Q[OF fair ns c _ D'_p(3) D'_p(6) D'_p(5)] by blast
    then have "D' \<in> Q_of_state (Liminf_state Sts)"
      using from_Q_to_Q_inf[OF fair ns c _ l'_p(2)] D'_p by auto
    then have ?thesis
      using D'_p by auto
  }
  moreover
  {
    assume a: "D \<in> ?Ps i"
    then obtain l' where
      l'_p: "D \<in> ?Qs l'" "l' < llength Sts"
      using from_P_to_Q[OF fair ns c a i_p(1) D_p(2) D_p(3)] by auto
    then have "D \<in> Q_of_state (Liminf_state Sts)"
      using from_Q_to_Q_inf[OF fair ns c l'_p(1) l'_p(2)] D_p(3) \<sigma>(1) \<sigma>(2) D_p(2) by auto
    then have ?thesis
      using D_p \<sigma> by auto
  }
  moreover
  {
    assume a: "D \<in> ?Qs i"
    then have "D \<in> Q_of_state (Liminf_state Sts)"
      using from_Q_to_Q_inf[OF fair ns c a i_p(1)] \<sigma> D_p(2,3) by auto
    then have ?thesis
      using D_p \<sigma> by auto
  }
  ultimately show ?thesis
    using i_p by auto
qed

text \<open>
The following corresponds to Lemma 4.11:
\<close>

lemma fair_imp_Liminf_minus_Rf_subset_ground_Liminf_state:
  assumes
    fair: "fair_state_seq Sts" and
    ns: "Gs = lmap grounding_of_state Sts"
  shows "Liminf_llist Gs - sr.Rf (Liminf_llist Gs) \<subseteq> grounding_of_clss (Q_of_state (Liminf_state Sts))"
proof
  let ?Ns = "\<lambda>i. N_of_state (lnth Sts i)"
  let ?Ps = "\<lambda>i. P_of_state (lnth Sts i)"
  let ?Qs = "\<lambda>i. Q_of_state (lnth Sts i)"

  have SQinf: "clss_of_state (Liminf_state Sts) = Liminf_llist (lmap Q_of_state Sts)"
    using fair unfolding fair_state_seq_def Liminf_state_def clss_of_state_def by auto

  fix C
  assume C_p: "C \<in> Liminf_llist Gs - sr.Rf (Liminf_llist Gs)"
  then have "C \<in> Sup_llist Gs"
    using Liminf_llist_subset_Sup_llist[of Gs] by blast
  then obtain D_proto where
    "D_proto \<in> clss_of_state (Sup_state Sts) \<and> subsumes D_proto C"
    using in_Sup_llist_in_Sup_state unfolding ns subsumes_def by blast
  then obtain D where
    D_p: "D \<in> clss_of_state (Sup_state Sts)"
    "subsumes D C"
    "\<forall>E \<in> {E. E \<in> clss_of_state (Sup_state Sts) \<and> subsumes E C}. \<not> strictly_subsumes E D"
    using strictly_subsumes_has_minimum[of "{E. E \<in> clss_of_state (Sup_state Sts) \<and> subsumes E C}"]
    by auto

  have ground_C: "is_ground_cls C"
    using C_p using Liminf_grounding_of_state_ground ns by auto

  have "\<exists>D' \<sigma>'. D' \<in> Q_of_state (Liminf_state Sts) \<and> D' \<cdot> \<sigma>' = C \<and> is_ground_subst \<sigma>'"
    using eventually_in_Qinf[of D C Gs] using D_p(1) D_p(2) D_p(3) fair ns C_p ground_C by auto
  then obtain D' \<sigma>' where
    D'_p: "D' \<in> Q_of_state (Liminf_state Sts) \<and> D' \<cdot> \<sigma>' = C \<and> is_ground_subst \<sigma>'"
    by blast
  then have "D' \<in> clss_of_state (Liminf_state Sts)"
    by (simp add: clss_of_state_def)
  then have "C \<in> grounding_of_state (Liminf_state Sts)"
    unfolding grounding_of_clss_def grounding_of_cls_def using D'_p by auto
  then show "C \<in> grounding_of_clss (Q_of_state (Liminf_state Sts))"
    using SQinf clss_of_state_def fair fair_state_seq_def by auto
qed

text \<open>
The following corresponds to (one direction of) Theorem 4.13:
\<close>

lemma ground_subclauses:
  assumes
    "\<forall>i < length CAs. CAs ! i = Cs ! i + poss (AAs ! i)" and
    "length Cs = length CAs" and
    "is_ground_cls_list CAs"
  shows "is_ground_cls_list Cs"
  unfolding is_ground_cls_list_def
  by (metis assms in_set_conv_nth is_ground_cls_list_def is_ground_cls_union)

lemma subseteq_Liminf_state_eventually_always:
  fixes CC
  assumes
    "finite CC" and
    "CC \<noteq> {}" and
    "CC \<subseteq> Q_of_state (Liminf_state Sts)"
  shows "\<exists>j. enat j < llength Sts \<and> (\<forall>j' \<ge> enat j. j' < llength Sts \<longrightarrow> CC \<subseteq> Q_of_state (lnth Sts j'))"
proof -
  from assms(3) have "\<forall>C \<in> CC. \<exists>j. enat j < llength Sts \<and> 
    (\<forall>j' \<ge> enat j. j' < llength Sts \<longrightarrow> C \<in> Q_of_state (lnth Sts j'))"
    unfolding Liminf_state_def Liminf_llist_def by force
  then obtain f where
    f_p: "\<forall>C \<in> CC. f C < llength Sts \<and> (\<forall>j' \<ge> enat (f C). j' < llength Sts \<longrightarrow> C \<in> Q_of_state (lnth Sts j'))"
    by moura

  define j :: nat where
    "j = Max (f ` CC)"

  have "enat j < llength Sts"
    unfolding j_def using f_p assms(1)
    by (metis (mono_tags) Max_in assms(2) finite_imageI imageE image_is_empty)
  moreover have "\<forall>C j'. C \<in> CC \<longrightarrow> enat j \<le> j' \<longrightarrow> j' < llength Sts \<longrightarrow> C \<in> Q_of_state (lnth Sts j')"
  proof (intro allI impI)
    fix C :: "'a clause" and j' :: nat
    assume a: "C \<in> CC" "enat j \<le> enat j'" "enat j' < llength Sts"
    then have "f C \<le> j'"
      unfolding j_def using assms(1) Max.bounded_iff by auto
    then show "C \<in> Q_of_state (lnth Sts j')"
      using f_p a by auto
  qed
  ultimately show ?thesis
    by auto
qed

lemma empty_clause_in_Q_of_Liminf_state:
  assumes
    empty_in: "{#} \<in> Liminf_llist (lmap grounding_of_state Sts)" and
    fair: "fair_state_seq Sts"
  shows "{#} \<in> Q_of_state (Liminf_state Sts)"
proof -
  define Gs :: "'a clause set llist" where
    ns: "Gs = lmap grounding_of_state Sts"
  from empty_in have in_Liminf_not_Rf: "{#} \<in> Liminf_llist Gs - sr.Rf (Liminf_llist Gs)"
    unfolding ns sr.Rf_def by auto
  then have "{#} \<in> grounding_of_clss (Q_of_state (Liminf_state Sts))"
    using fair_imp_Liminf_minus_Rf_subset_ground_Liminf_state[OF fair ns] by auto
  then show ?thesis
    unfolding grounding_of_clss_def grounding_of_cls_def by auto
qed

lemma grounding_of_state_Liminf_state_subseteq:
  "grounding_of_state (Liminf_state Sts) \<subseteq> Liminf_llist (lmap grounding_of_state Sts)"
proof
  fix C :: "'a clause"
  assume "C \<in> grounding_of_state (Liminf_state Sts)"
  then obtain D \<sigma> where
    D_\<sigma>_p: "D \<in> clss_of_state (Liminf_state Sts)" "D \<cdot> \<sigma> = C" "is_ground_subst \<sigma>"
    unfolding clss_of_state_def grounding_of_clss_def grounding_of_cls_def by auto
  then have ii: "D \<in> Liminf_llist (lmap N_of_state Sts) \<or> 
    D \<in> Liminf_llist (lmap P_of_state Sts) \<or> 
    D \<in> Liminf_llist (lmap Q_of_state Sts)"
    unfolding clss_of_state_def  Liminf_state_def by simp
  then have "C \<in> Liminf_llist (lmap grounding_of_clss (lmap N_of_state Sts)) \<or>
    C \<in> Liminf_llist (lmap grounding_of_clss (lmap P_of_state Sts)) \<or>
    C \<in> Liminf_llist (lmap grounding_of_clss (lmap Q_of_state Sts))"
    unfolding Liminf_llist_def grounding_of_clss_def grounding_of_cls_def
    apply -
    apply (erule disjE)
    subgoal
      apply (rule disjI1)
      using D_\<sigma>_p by auto
    subgoal
      apply (erule HOL.disjE)
      subgoal
        apply (rule disjI2)
        apply (rule disjI1)
        using D_\<sigma>_p by auto
      subgoal
        apply (rule disjI2)
        apply (rule disjI2)
        using D_\<sigma>_p by auto
      done
    done
  then show "C \<in> Liminf_llist (lmap grounding_of_state Sts)"
    unfolding Liminf_llist_def clss_of_state_def grounding_of_clss_def by auto
qed

theorem RP_sound:
  assumes "{#} \<in> clss_of_state (Liminf_state Sts)"
  shows "\<not> satisfiable (grounding_of_state (lhd Sts))"
proof -
  from assms have "{#} \<in> grounding_of_state (Liminf_state Sts)"
    unfolding grounding_of_clss_def by (force intro: ex_ground_subst)
  then have "{#} \<in> Liminf_llist (lmap grounding_of_state Sts)"
    using grounding_of_state_Liminf_state_subseteq by auto
  then have "\<not> satisfiable (Liminf_llist (lmap grounding_of_state Sts))"
    using true_clss_def by auto
  then have "\<not> satisfiable (lhd (lmap grounding_of_state Sts))"
    using sr_ext.sat_limit_iff RP_ground_derive_chain by metis
  then show ?thesis
    unfolding lhd_lmap_Sts .
qed

lemma ground_ord_resolve_ground: 
  assumes 
    CAs_p: "gr.ord_resolve CAs DA AAs As E" and
    ground_cas: "is_ground_cls_list CAs" and
    ground_da: "is_ground_cls DA"
  shows "is_ground_cls E"
proof -
  have a1: "atms_of E \<subseteq> (\<Union>CA \<in> set CAs. atms_of CA) \<union> atms_of DA"
    using gr.ord_resolve_atms_of_concl_subset[of CAs DA _ _ E] CAs_p by auto
  {
    fix L :: "'a literal"
    assume "L \<in># E"
    then have "atm_of L \<in> atms_of E"
      by (meson atm_of_lit_in_atms_of)
    then have "is_ground_atm (atm_of L)"
      using a1 ground_cas ground_da is_ground_cls_imp_is_ground_atm is_ground_cls_list_def
      by auto
  }
  then show ?thesis
    unfolding is_ground_cls_def is_ground_lit_def by simp
qed

theorem RP_saturated_if_fair:
  assumes fair: "fair_state_seq Sts"
  shows "sr.saturated_upto (Liminf_llist (lmap grounding_of_state Sts))"
proof -
  define Gs :: "'a clause set llist" where
    ns: "Gs = lmap grounding_of_state Sts"

  let ?N = "\<lambda>i. grounding_of_state (lnth Sts i)"

  let ?Ns = "\<lambda>i. N_of_state (lnth Sts i)"
  let ?Ps = "\<lambda>i. P_of_state (lnth Sts i)"
  let ?Qs = "\<lambda>i. Q_of_state (lnth Sts i)"

  have ground_ns_in_ground_limit_st:
    "Liminf_llist Gs - sr.Rf (Liminf_llist Gs) \<subseteq> grounding_of_clss (Q_of_state (Liminf_state Sts))"
    using fair deriv fair_imp_Liminf_minus_Rf_subset_ground_Liminf_state ns by blast

  have derivns: "chain sr_ext.derive Gs"
    using RP_ground_derive_chain deriv ns by auto

  {
    fix \<gamma> :: "'a inference"
    assume \<gamma>_p: "\<gamma> \<in> gr.ord_\<Gamma>"
    let ?CC = "side_prems_of \<gamma>"
    let ?DA = "main_prem_of \<gamma>"
    let ?E = "concl_of \<gamma>"
    assume a: "set_mset ?CC \<union> {?DA} 
      \<subseteq> Liminf_llist (lmap grounding_of_state Sts) - sr.Rf (Liminf_llist (lmap grounding_of_state Sts))"

    have ground_ground_Liminf: "is_ground_clss (Liminf_llist (lmap grounding_of_state Sts))"
      using Liminf_grounding_of_state_ground unfolding is_ground_clss_def by auto

    have ground_cc: "is_ground_clss (set_mset ?CC)"
      using a ground_ground_Liminf is_ground_clss_def by auto

    have ground_da: "is_ground_cls ?DA"
      using a grounding_ground singletonI ground_ground_Liminf
      by (simp add: Liminf_grounding_of_state_ground)

    from \<gamma>_p obtain CAs AAs As where
      CAs_p: "gr.ord_resolve CAs ?DA AAs As ?E \<and> mset CAs = ?CC"
      unfolding gr.ord_\<Gamma>_def by auto

    have DA_CAs_in_ground_Liminf:
      "{?DA} \<union> set CAs \<subseteq> grounding_of_clss (Q_of_state (Liminf_state Sts))"
      using a CAs_p unfolding clss_of_state_def using fair unfolding fair_state_seq_def
      by (metis (no_types, lifting) Un_empty_left ground_ns_in_ground_limit_st a clss_of_state_def
          ns set_mset_mset subset_trans sup_commute)

    then have ground_cas: "is_ground_cls_list CAs"
      using CAs_p unfolding is_ground_cls_list_def by auto

    then have ground_e: "is_ground_cls ?E"
      using ground_ord_resolve_ground CAs_p ground_da by auto

    have "\<exists>AAs As \<sigma>. ord_resolve (S_M S (Q_of_state (Liminf_state Sts))) CAs ?DA AAs As \<sigma> ?E"
      using CAs_p[THEN conjunct1]
    proof (cases rule: gr.ord_resolve.cases)
      case (ord_resolve n Cs D)
      note DA = this(1) and e = this(2) and cas_len = this(3) and cs_len = this(4) and
        aas_len = this(5) and as_len = this(6) and nz = this(7) and cas = this(8) and
        aas_not_empt = this(9) and as_aas = this(10) and eligibility = this(11) and
        str_max = this(12) and sel_empt = this(13)

      have len_aas_len_as: "length AAs = length As"
        using aas_len as_len by auto

      from as_aas have "\<forall>i<n. \<forall>A \<in># add_mset (As ! i) (AAs ! i). A = As ! i"
        using ord_resolve by simp
      then have "\<forall>i < n. card (set_mset (add_mset (As ! i) (AAs ! i))) \<le> Suc 0"
        using all_the_same by metis
      then have "\<forall>i < length AAs. card (set_mset (add_mset (As ! i) (AAs ! i))) \<le> Suc 0"
        using aas_len by auto
      then have "\<forall>AA \<in> set (map2 add_mset As AAs). card (set_mset AA) \<le> Suc 0"
        using set_map2_ex[of AAs As add_mset, OF len_aas_len_as] by auto
      then have "is_unifiers id_subst (set_mset ` set (map2 add_mset As AAs))"
        unfolding is_unifiers_def is_unifier_def by auto
      moreover have "finite (set_mset ` set (map2 add_mset As AAs))"
        by auto
      moreover have "\<forall>AA \<in> set_mset ` set (map2 add_mset As AAs). finite AA"
        by auto
      ultimately obtain \<sigma> where
        \<sigma>_p: "Some \<sigma> = mgu (set_mset ` set (map2 add_mset As AAs))"
        using mgu_complete by metis

      have ground_elig: "gr.eligible As (D + negs (mset As))"
        using ord_resolve by simp
      have ground_cs: "\<forall>i < n. is_ground_cls (Cs ! i)"
        using ord_resolve(8) ord_resolve(3,4) ground_cas
        using ground_subclauses[of CAs Cs AAs] unfolding is_ground_cls_list_def by auto
      have ground_set_as: "is_ground_atms (set As)"
        using ord_resolve(1) ground_da
        by (metis atms_of_negs is_ground_cls_union set_mset_mset is_ground_cls_is_ground_atms_atms_of)
      then have ground_mset_as: "is_ground_atm_mset (mset As)"
        unfolding is_ground_atm_mset_def is_ground_atms_def by auto
      have ground_as: "is_ground_atm_list As"
        using ground_set_as is_ground_atm_list_def is_ground_atms_def by auto
      have ground_d: "is_ground_cls D"
        using ground_da ord_resolve by simp

      from as_len nz have "atms_of D \<union> set As \<noteq> {}" "finite (atms_of D \<union> set As)"
        by auto
      then have "Max (atms_of D \<union> set As) \<in> atms_of D \<union> set As"
        using Max_in by metis
      then have is_ground_Max: "is_ground_atm (Max (atms_of D \<union> set As))"
        using ground_d ground_mset_as is_ground_cls_imp_is_ground_atm
        unfolding is_ground_atm_mset_def by auto
      then have Max\<sigma>_is_Max: "\<forall>\<sigma>. Max (atms_of D \<union> set As) \<cdot>a \<sigma> = Max (atms_of D \<union> set As)"
        by auto

      have ann1: "maximal_wrt (Max (atms_of D \<union> set As)) (D + negs (mset As))"
        unfolding maximal_wrt_def
        by clarsimp (metis Max_less_iff UnCI \<open>atms_of D \<union> set As \<noteq> {}\<close>
            \<open>finite (atms_of D \<union> set As)\<close> ground_d ground_set_as infinite_growing is_ground_Max
            is_ground_atms_def is_ground_cls_imp_is_ground_atm less_atm_ground)

      from ground_elig have ann2:
        "Max (atms_of D \<union> set As) \<cdot>a \<sigma> = Max (atms_of D \<union> set As)"
        "D \<cdot> \<sigma> + negs (mset As \<cdot>am \<sigma>) = D + negs (mset As)"
        using is_ground_Max ground_mset_as ground_d by auto

      from ground_elig have fo_elig:
        "eligible (S_M S (Q_of_state (Liminf_state Sts))) \<sigma> As (D + negs (mset As))"
        unfolding gr.eligible.simps eligible.simps gr.maximal_wrt_def using ann1 ann2
        by (auto simp: S_Q_def)

      have l: "\<forall>i < n. gr.strictly_maximal_wrt (As ! i) (Cs ! i)"
        using ord_resolve by simp
      then have "\<forall>i < n. strictly_maximal_wrt (As ! i) (Cs ! i)"
        unfolding gr.strictly_maximal_wrt_def strictly_maximal_wrt_def
        using ground_as[unfolded is_ground_atm_list_def] ground_cs as_len less_atm_ground
        by clarsimp (fastforce simp: is_ground_cls_as_atms)+

      then have ll: "\<forall>i < n. strictly_maximal_wrt (As ! i \<cdot>a \<sigma>) (Cs ! i \<cdot> \<sigma>)"
        by (simp add: ground_as ground_cs as_len)

      have m: "\<forall>i < n. S_Q (CAs ! i) = {#}"
        using ord_resolve by simp

      have ground_e: "is_ground_cls (\<Union># (mset Cs) + D)"
        using ground_d ground_cs ground_e e by simp
      show ?thesis
        using ord_resolve.intros[OF cas_len cs_len aas_len as_len nz cas aas_not_empt \<sigma>_p fo_elig ll] m DA e ground_e
        unfolding S_Q_def by auto
    qed
    then obtain AAs As \<sigma> where
      \<sigma>_p: "ord_resolve (S_M S (Q_of_state (Liminf_state Sts))) CAs ?DA AAs As \<sigma> ?E"
      by auto
    then obtain \<eta>s' \<eta>' \<eta>2' CAs' DA' AAs' As' \<tau>' E' where s_p:
      "is_ground_subst \<eta>'"
      "is_ground_subst_list \<eta>s'"
      "is_ground_subst \<eta>2'"
      "ord_resolve_rename S CAs' DA' AAs' As' \<tau>' E'"
      "CAs' \<cdot>\<cdot>cl \<eta>s' = CAs"
      "DA' \<cdot> \<eta>' = ?DA"
      "E' \<cdot> \<eta>2' = ?E"
      "{DA'} \<union> set CAs' \<subseteq> Q_of_state (Liminf_state Sts)"
      using ord_resolve_rename_lifting[OF sel_stable, of "Q_of_state (Liminf_state Sts)" CAs ?DA]
        \<sigma>_p selection_axioms DA_CAs_in_ground_Liminf by metis
    from this(8) have "\<exists>j. enat j < llength Sts \<and> (set CAs' \<union> {DA'} \<subseteq> ?Qs j)"
      unfolding Liminf_llist_def
      using subseteq_Liminf_state_eventually_always[of "{DA'} \<union> set CAs'"] by auto
    then obtain j where
      j_p: "is_least (\<lambda>j. enat j < llength Sts \<and> set CAs' \<union> {DA'} \<subseteq> ?Qs j) j"
      using least_exists[of "\<lambda>j. enat j < llength Sts \<and> set CAs' \<union> {DA'} \<subseteq> ?Qs j"] by force
    then have j_p': "enat j < llength Sts" "set CAs' \<union> {DA'} \<subseteq> ?Qs j"
      unfolding is_least_def by auto
    then have jn0: "j \<noteq> 0"
      using empty_Q0 by (metis bot_eq_sup_iff gr_implies_not_zero insert_not_empty llength_lnull
          lnth_0_conv_lhd sup.orderE)
    then have j_adds_CAs': "\<not> set CAs' \<union> {DA'} \<subseteq> ?Qs (j - 1)" "set CAs' \<union> {DA'} \<subseteq> ?Qs j"
      using j_p unfolding is_least_def
       apply (metis (no_types) One_nat_def Suc_diff_Suc Suc_ile_eq diff_diff_cancel diff_zero
          less_imp_le less_one neq0_conv zero_less_diff)
      using j_p'(2) by blast
    have "lnth Sts (j - 1) \<leadsto> lnth Sts j"
      using j_p'(1) jn0  deriv chain_lnth_rel[of _ _ "j - 1"] by force
    then obtain C' where C'_p:
      "?Ns (j - 1) = {}"
      "?Ps (j - 1) = ?Ps j \<union> {C'}"
      "?Qs j = ?Qs (j - 1) \<union> {C'}"
      "?Ns j = concls_of (ord_FO_resolution.inferences_between (?Qs (j - 1)) C')"
      "C' \<in> set CAs' \<union> {DA'}"
      "C' \<notin> ?Qs (j - 1)"
      using j_adds_CAs' by (induction rule: RP.cases) auto
    have "E' \<in> ?Ns j"
    proof -
      have "E' \<in> concls_of (ord_FO_resolution.inferences_between (Q_of_state (lnth Sts (j - 1))) C')"
        unfolding infer_from_def ord_FO_\<Gamma>_def unfolding inference_system.inferences_between_def
        apply (rule_tac x = "Infer (mset CAs') DA' E'" in image_eqI)
        subgoal by auto
        subgoal
          using s_p(4)
          unfolding infer_from_def
          apply (rule ord_resolve_rename.cases)
          using s_p(4)
          using C'_p(3) C'_p(5) j_p'(2) apply force
          done
        done
      then show ?thesis
        using C'_p(4) by auto
    qed
    then have "E' \<in> clss_of_state (lnth Sts j)"
      using j_p' unfolding clss_of_state_def by auto
    then have "?E \<in> grounding_of_state (lnth Sts j)"
      using s_p(7) s_p(3) unfolding grounding_of_clss_def grounding_of_cls_def by force
    then have "\<gamma> \<in> sr.Ri (grounding_of_state (lnth Sts j))"
      using sr.Ri_effective \<gamma>_p by auto
    then have "\<gamma> \<in> sr_ext_Ri (?N j)"
      unfolding sr_ext_Ri_def by auto
    then have "\<gamma> \<in> sr_ext_Ri (Sup_llist (lmap grounding_of_state Sts))"
      using j_p' contra_subsetD llength_lmap lnth_lmap lnth_subset_Sup_llist sr_ext.Ri_mono by metis
    then have "\<gamma> \<in> sr_ext_Ri (Liminf_llist (lmap grounding_of_state Sts))"
      using sr_ext.Ri_limit_Sup[of Gs] derivns ns by blast
  }
  then have "sr_ext.saturated_upto (Liminf_llist (lmap grounding_of_state Sts))"
    unfolding sr_ext.saturated_upto_def sr_ext.inferences_from_def infer_from_def sr_ext_Ri_def
    by auto
  then show ?thesis
    using gd_ord_\<Gamma>_ngd_ord_\<Gamma> sr.redundancy_criterion_axioms
      redundancy_criterion_standard_extension_saturated_upto_iff[of gr.ord_\<Gamma>]
    unfolding sr_ext_Ri_def by auto
qed

corollary RP_complete_if_fair:
  assumes
    fair: "fair_state_seq Sts" and
    unsat: "\<not> satisfiable (grounding_of_state (lhd Sts))"
  shows "{#} \<in> Q_of_state (Liminf_state Sts)"
proof -
  have "\<not> satisfiable (Liminf_llist (lmap grounding_of_state Sts))"
    unfolding sr_ext.sat_limit_iff[OF RP_ground_derive_chain]
    by (rule unsat[folded lhd_lmap_Sts[of grounding_of_state]])
  moreover have "sr.saturated_upto (Liminf_llist (lmap grounding_of_state Sts))"
    by (rule RP_saturated_if_fair[OF fair, simplified])
  ultimately have "{#} \<in> Liminf_llist (lmap grounding_of_state Sts)"
    using sr.saturated_upto_complete_if by auto
  then show ?thesis
    using empty_clause_in_Q_of_Liminf_state fair by auto
qed

end

end

end
