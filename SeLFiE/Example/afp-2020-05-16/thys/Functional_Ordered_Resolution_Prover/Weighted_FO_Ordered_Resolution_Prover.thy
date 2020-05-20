(*  Title:       A Fair Ordered Resolution Prover for First-Order Clauses with Weights
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2017
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2017
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>A Fair Ordered Resolution Prover for First-Order Clauses with Weights\<close>

text \<open>
The \<open>weighted_RP\<close> prover introduced below operates on finite multisets of clauses and
organizes the multiset of processed clauses as a priority queue to ensure that inferences are
performed in a fair manner, to guarantee completeness.
\<close>

theory Weighted_FO_Ordered_Resolution_Prover
  imports Ordered_Resolution_Prover.FO_Ordered_Resolution_Prover
begin


subsection \<open>Library\<close>

(* TODO: Move to "Coinductive"? *)
lemma ldrop_Suc_conv_ltl: "ldrop (enat (Suc k)) xs = ltl (ldrop (enat k) xs)"
  by (metis eSuc_enat ldrop_eSuc_conv_ltl)

(* TODO: Move to "Coinductive"? *)
lemma lhd_ldrop':
  assumes "enat k < llength xs"
  shows "lhd (ldrop (enat k) xs) = lnth xs k"
  using assms by (simp add: lhd_ldrop)

(* TODO: Move to "Multiset_More.thy". *)
lemma filter_mset_empty_if_finite_and_filter_set_empty:
  assumes
    "{x \<in> X. P x} = {}" and
    "finite X"
  shows "{#x \<in># mset_set X. P x#} = {#}"
proof -
  have empty_empty: "\<And>Y. set_mset Y = {} \<Longrightarrow> Y = {#}"
    by auto
  from assms have "set_mset {#x \<in># mset_set X. P x#} = {}"
    by auto
  then show ?thesis
    by (rule empty_empty)
qed

(* TODO: Move to "Lazy_List_Chain.thy". *)
lemma inf_chain_ltl_chain: "chain R xs \<Longrightarrow> llength xs = \<infinity> \<Longrightarrow> chain R (ltl xs)"
  unfolding chain.simps[of R xs] llength_eq_infty_conv_lfinite
  by (metis lfinite_code(1) lfinite_ltl llist.sel(3))

(* TODO: Move to "Lazy_List_Chain.thy". *)
lemma inf_chain_ldrop_chain:
  assumes
    chain: "chain R xs" and
    inf: "\<not> lfinite xs"
  shows "chain R (ldrop (enat k) xs)"
proof (induction k)
  case 0
  then show ?case
    using zero_enat_def chain by auto
next
  case (Suc k)
  have "llength (ldrop (enat k) xs) = \<infinity>"
    using inf by (simp add: not_lfinite_llength)
  with Suc have "chain R (ltl (ldrop (enat k) xs))"
    using inf_chain_ltl_chain[of R "(ldrop (enat k) xs)"] by auto
  then show ?case
    using ldrop_Suc_conv_ltl[of k xs] by auto
qed


subsection \<open>Prover\<close>

type_synonym 'a wclause = "'a clause \<times> nat"
type_synonym 'a wstate = "'a wclause multiset \<times> 'a wclause multiset \<times> 'a wclause multiset \<times> nat"

fun state_of_wstate :: "'a wstate \<Rightarrow> 'a state" where
  "state_of_wstate (N, P, Q, n) =
   (set_mset (image_mset fst N), set_mset (image_mset fst P), set_mset (image_mset fst Q))"

locale weighted_FO_resolution_prover =
  FO_resolution_prover S subst_atm id_subst comp_subst renamings_apart atm_of_atms mgu less_atm
  for
    S :: "('a :: wellorder) clause \<Rightarrow> 'a clause" and
    subst_atm :: "'a \<Rightarrow> 's \<Rightarrow> 'a" and
    id_subst :: "'s" and
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's" and
    renamings_apart :: "'a clause list \<Rightarrow> 's list" and
    atm_of_atms :: "'a list \<Rightarrow> 'a" and
    mgu :: "'a set set \<Rightarrow> 's option" and
    less_atm :: "'a \<Rightarrow> 'a \<Rightarrow> bool" +
  fixes
    weight :: "'a clause \<times> nat \<Rightarrow> nat"
  assumes
    weight_mono: "i < j \<Longrightarrow> weight (C, i) < weight (C, j)"
begin

abbreviation clss_of_wstate :: "'a wstate \<Rightarrow> 'a clause set" where
  "clss_of_wstate St \<equiv> clss_of_state (state_of_wstate St)"

abbreviation N_of_wstate :: "'a wstate \<Rightarrow> 'a clause set" where
  "N_of_wstate St \<equiv> N_of_state (state_of_wstate St)"

abbreviation P_of_wstate :: "'a wstate \<Rightarrow> 'a clause set" where
  "P_of_wstate St \<equiv> P_of_state (state_of_wstate St)"

abbreviation Q_of_wstate :: "'a wstate \<Rightarrow> 'a clause set" where
  "Q_of_wstate St \<equiv> Q_of_state (state_of_wstate St)"

fun wN_of_wstate :: "'a wstate \<Rightarrow> 'a wclause multiset" where
  "wN_of_wstate (N, P, Q, n) = N"

fun wP_of_wstate :: "'a wstate \<Rightarrow> 'a wclause multiset" where
  "wP_of_wstate (N, P, Q, n) = P"

fun wQ_of_wstate :: "'a wstate \<Rightarrow> 'a wclause multiset" where
  "wQ_of_wstate (N, P, Q, n) = Q"

fun n_of_wstate :: "'a wstate \<Rightarrow> nat" where
  "n_of_wstate (N, P, Q, n) = n"

lemma of_wstate_split[simp]:
  "(wN_of_wstate St, wP_of_wstate St, wQ_of_wstate St, n_of_wstate St) = St"
  by (cases St) auto

abbreviation grounding_of_wstate :: "'a wstate \<Rightarrow> 'a clause set" where
  "grounding_of_wstate St \<equiv> grounding_of_state (state_of_wstate St)"

abbreviation Liminf_wstate :: "'a wstate llist \<Rightarrow> 'a state" where
  "Liminf_wstate Sts \<equiv> Liminf_state (lmap state_of_wstate Sts)"

lemma timestamp_le_weight: "n \<le> weight (C, n)"
  by (induct n, simp, metis weight_mono[of k "Suc k" for k] Suc_le_eq le_less le_trans)

inductive weighted_RP :: "'a wstate \<Rightarrow> 'a wstate \<Rightarrow> bool" (infix "\<leadsto>\<^sub>w" 50) where
  tautology_deletion: "Neg A \<in># C \<Longrightarrow> Pos A \<in># C \<Longrightarrow> (N + {#(C, i)#}, P, Q, n) \<leadsto>\<^sub>w (N, P, Q, n)"
| forward_subsumption: "D \<in># image_mset fst (P + Q) \<Longrightarrow> subsumes D C \<Longrightarrow>
    (N + {#(C, i)#}, P, Q, n) \<leadsto>\<^sub>w (N, P, Q, n)"
| backward_subsumption_P: "D \<in># image_mset fst N \<Longrightarrow> C \<in># image_mset fst P \<Longrightarrow>
    strictly_subsumes D C \<Longrightarrow> (N, P, Q, n) \<leadsto>\<^sub>w (N, {#(E, k) \<in># P. E \<noteq> C#}, Q, n)"
| backward_subsumption_Q: "D \<in># image_mset fst N \<Longrightarrow> strictly_subsumes D C \<Longrightarrow>
    (N, P, Q + {#(C, i)#}, n) \<leadsto>\<^sub>w (N, P, Q, n)"
| forward_reduction: "D + {#L'#} \<in># image_mset fst (P + Q) \<Longrightarrow> - L = L' \<cdot>l \<sigma> \<Longrightarrow> D \<cdot> \<sigma> \<subseteq># C \<Longrightarrow>
    (N + {#(C + {#L#}, i)#}, P, Q, n) \<leadsto>\<^sub>w (N + {#(C, i)#}, P, Q, n)"
| backward_reduction_P: "D + {#L'#} \<in># image_mset fst N \<Longrightarrow> - L = L' \<cdot>l \<sigma> \<Longrightarrow> D \<cdot> \<sigma> \<subseteq># C \<Longrightarrow>
    (\<forall>j. (C + {#L#}, j) \<in># P \<longrightarrow> j \<le> i) \<Longrightarrow>
    (N, P + {#(C + {#L#}, i)#}, Q, n) \<leadsto>\<^sub>w (N, P + {#(C, i)#}, Q, n)"
| backward_reduction_Q: "D + {#L'#} \<in># image_mset fst N \<Longrightarrow> - L = L' \<cdot>l \<sigma> \<Longrightarrow> D \<cdot> \<sigma> \<subseteq># C \<Longrightarrow>
    (N, P, Q + {#(C + {#L#}, i)#}, n) \<leadsto>\<^sub>w (N, P + {#(C, i)#}, Q, n)"
| clause_processing: "(N + {#(C, i)#}, P, Q, n) \<leadsto>\<^sub>w (N, P + {#(C, i)#}, Q, n)"
| inference_computation: "(\<forall>(D, j) \<in># P. weight (C, i) \<le> weight (D, j)) \<Longrightarrow>
    N = mset_set ((\<lambda>D. (D, n)) ` concls_of
      (inference_system.inferences_between (ord_FO_\<Gamma> S) (set_mset (image_mset fst Q)) C)) \<Longrightarrow>
    ({#}, P + {#(C, i)#}, Q, n) \<leadsto>\<^sub>w (N, {#(D, j) \<in># P. D \<noteq> C#}, Q + {#(C, i)#}, Suc n)"

lemma weighted_RP_imp_RP: "St \<leadsto>\<^sub>w St' \<Longrightarrow> state_of_wstate St \<leadsto> state_of_wstate St'"
proof (induction rule: weighted_RP.induct)
  case (backward_subsumption_P D N C P Q n)
  show ?case
    by (rule arg_cong2[THEN iffD1, of _ _ _ _ "(\<leadsto>)", OF _ _
          RP.backward_subsumption_P[of D "fst ` set_mset N" C "fst ` set_mset P - {C}"
            "fst ` set_mset Q"]])
      (use backward_subsumption_P in auto)
next
  case (inference_computation P C i N n Q)
  show ?case
     by (rule arg_cong2[THEN iffD1, of _ _ _ _ "(\<leadsto>)", OF _ _
           RP.inference_computation[of "fst ` set_mset N" "fst ` set_mset Q" C
             "fst ` set_mset P - {C}"]],
         use inference_computation(2) finite_ord_FO_resolution_inferences_between in
           \<open>auto simp: comp_def image_comp inference_system.inferences_between_def\<close>)
qed (use RP.intros in simp_all)

lemma final_weighted_RP: "\<not> ({#}, {#}, Q, n) \<leadsto>\<^sub>w St"
  by (auto elim: weighted_RP.cases)

context
  fixes
    Sts :: "'a wstate llist"
  assumes
    full_deriv: "full_chain (\<leadsto>\<^sub>w) Sts" and
    empty_P0: "P_of_wstate (lhd Sts) = {}" and
    empty_Q0: "Q_of_wstate (lhd Sts) = {}"
begin

lemma finite_Sts0: "finite (clss_of_wstate (lhd Sts))"
  unfolding clss_of_state_def by (cases "lhd Sts") auto

lemmas deriv = full_chain_imp_chain[OF full_deriv]
lemmas lhd_lmap_Sts = llist.map_sel(1)[OF chain_not_lnull[OF deriv]]

lemma deriv_RP: "chain (\<leadsto>) (lmap state_of_wstate Sts)"
  using deriv weighted_RP_imp_RP by (metis chain_lmap)

lemma finite_Sts0_RP: "finite (clss_of_state (lhd (lmap state_of_wstate Sts)))"
  using finite_Sts0 chain_length_pos[OF deriv] by auto

lemma empty_P0_RP: "P_of_state (lhd (lmap state_of_wstate Sts)) = {}"
  using empty_P0 chain_length_pos[OF deriv] by auto

lemma empty_Q0_RP: "Q_of_state (lhd (lmap state_of_wstate Sts)) = {}"
  using empty_Q0 chain_length_pos[OF deriv] by auto

lemmas Sts_thms = deriv_RP finite_Sts0_RP empty_P0_RP empty_Q0_RP

theorem weighted_RP_model:
  "St \<leadsto>\<^sub>w St' \<Longrightarrow> I \<Turnstile>s grounding_of_wstate St' \<longleftrightarrow> I \<Turnstile>s grounding_of_wstate St"
  using RP_model Sts_thms weighted_RP_imp_RP by (simp only: comp_def)

abbreviation S_gQ :: "'a clause \<Rightarrow> 'a clause" where
  "S_gQ \<equiv> S_Q (lmap state_of_wstate Sts)"

interpretation sq: selection S_gQ
  unfolding S_Q_def[OF deriv_RP empty_Q0_RP]
  using S_M_selects_subseteq S_M_selects_neg_lits selection_axioms
  by unfold_locales auto

interpretation gd: ground_resolution_with_selection S_gQ
  by unfold_locales

interpretation src: standard_redundancy_criterion_reductive gd.ord_\<Gamma>
  by unfold_locales

interpretation src: standard_redundancy_criterion_counterex_reducing gd.ord_\<Gamma>
  "ground_resolution_with_selection.INTERP S_gQ"
  by unfold_locales

lemmas ord_\<Gamma>_saturated_upto_def = src.saturated_upto_def
lemmas ord_\<Gamma>_saturated_upto_complete = src.saturated_upto_complete
lemmas ord_\<Gamma>_contradiction_Rf = src.contradiction_Rf

theorem weighted_RP_sound:
  assumes "{#} \<in> clss_of_state (Liminf_wstate Sts)"
  shows "\<not> satisfiable (grounding_of_wstate (lhd Sts))"
  by (rule RP_sound[OF deriv_RP empty_Q0_RP assms, unfolded lhd_lmap_Sts])

abbreviation RP_filtered_measure :: "('a wclause \<Rightarrow> bool) \<Rightarrow> 'a wstate \<Rightarrow> nat \<times> nat \<times> nat" where
  "RP_filtered_measure \<equiv> \<lambda>p (N, P, Q, n).
     (sum_mset (image_mset (\<lambda>(C, i). Suc (size C)) {#Di \<in># N + P + Q. p Di#}),
      size {#Di \<in># N. p Di#}, size {#Di \<in># P. p Di#})"

abbreviation RP_combined_measure :: "nat \<Rightarrow> 'a wstate \<Rightarrow> nat \<times> (nat \<times> nat \<times> nat) \<times> (nat \<times> nat \<times> nat)" where
  "RP_combined_measure \<equiv> \<lambda>w St.
     (w + 1 - n_of_wstate St, RP_filtered_measure (\<lambda>(C, i). i \<le> w) St,
      RP_filtered_measure (\<lambda>Ci. True) St)"

abbreviation (input) RP_filtered_relation :: "((nat \<times> nat \<times> nat) \<times> (nat \<times> nat \<times> nat)) set" where
  "RP_filtered_relation \<equiv> natLess <*lex*> natLess <*lex*> natLess"

abbreviation (input) RP_combined_relation :: "((nat \<times> ((nat \<times> nat \<times> nat) \<times> (nat \<times> nat \<times> nat))) \<times>
    (nat \<times> ((nat \<times> nat \<times> nat) \<times> (nat \<times> nat \<times> nat)))) set" where
  "RP_combined_relation \<equiv> natLess <*lex*> RP_filtered_relation <*lex*> RP_filtered_relation"

abbreviation "(fst3 :: 'b * 'c * 'd \<Rightarrow> 'b) \<equiv> fst"
abbreviation "(snd3 :: 'b * 'c * 'd \<Rightarrow> 'c) \<equiv> \<lambda>x. fst (snd x)"
abbreviation "(trd3 :: 'b * 'c * 'd \<Rightarrow> 'd) \<equiv> \<lambda>x. snd (snd x)"

lemma
  wf_RP_filtered_relation: "wf RP_filtered_relation" and
  wf_RP_combined_relation: "wf RP_combined_relation"
  unfolding natLess_def using wf_less wf_mult by auto

lemma multiset_sum_of_Suc_f_monotone: "N \<subset># M \<Longrightarrow> (\<Sum>x \<in># N. Suc (f x)) < (\<Sum>x \<in># M. Suc (f x))"
proof (induction N arbitrary: M)
  case empty
  then obtain y where "y \<in># M"
    by force
  then have "(\<Sum>x \<in># M. 1) = (\<Sum>x \<in># M - {#y#} + {#y#}. 1)"
    by auto
  also have "... = (\<Sum>x \<in># M - {#y#}. 1) + (\<Sum>x \<in># {#y#}. 1)"
    by (metis image_mset_union sum_mset.union)
  also have "... > (0 :: nat)"
    by auto
  finally have "0 < (\<Sum>x \<in># M. Suc (f x))"
    by (fastforce intro: gr_zeroI)
  then show ?case
    using empty by auto
next
  case (add x N)
  from this(2) have "(\<Sum>y \<in># N. Suc (f y)) < (\<Sum>y \<in># M - {#x#}. Suc (f y))"
    using add(1)[of "M - {#x#}"] by (simp add: insert_union_subset_iff)
  moreover have "add_mset x (remove1_mset x M) = M"
    by (meson add.prems add_mset_remove_trivial_If mset_subset_insertD)
  ultimately show ?case
    by (metis (no_types) add.commute add_less_cancel_right sum_mset.insert)
qed

lemma multiset_sum_monotone_f':
  assumes "CC \<subset># DD"
  shows "(\<Sum>(C, i) \<in># CC. Suc (f C)) < (\<Sum>(C, i) \<in># DD. Suc (f C))"
  using multiset_sum_of_Suc_f_monotone[OF assms, of "f \<circ> fst"]
  by (metis (mono_tags) comp_apply image_mset_cong2 split_beta)

lemma filter_mset_strict_subset:
  assumes "x \<in># M" and "\<not> p x"
  shows "{#y \<in># M. p y#} \<subset># M"
proof -
  have subseteq: "{#E \<in># M. p E#} \<subseteq># M"
    by auto
  have "count {#E \<in># M. p E#} x = 0"
    using assms by auto
  moreover have "0 < count M x"
    using assms by auto
  ultimately have lt_count: "count {#y \<in># M. p y#} x < count M x"
    by auto
  then show ?thesis
    using subseteq by (metis less_not_refl2 subset_mset.le_neq_trans)
qed

lemma weighted_RP_measure_decreasing_N:
  assumes "St \<leadsto>\<^sub>w St'" and "(C, l) \<in># wN_of_wstate St"
  shows "(RP_filtered_measure (\<lambda>Ci. True) St', RP_filtered_measure (\<lambda>Ci. True) St)
    \<in> RP_filtered_relation"
using assms proof (induction rule: weighted_RP.induct)
  case (backward_subsumption_P D N C' P Q n)
  then obtain i' where  "(C', i') \<in># P"
    by auto
  then have "{#(E, k) \<in># P. E \<noteq> C'#} \<subset># P"
    using filter_mset_strict_subset[of "(C', i')" P "\<lambda>X. \<not>fst X =  C'"]
    by (metis (mono_tags, lifting) filter_mset_cong fst_conv prod.case_eq_if)
  then have "(\<Sum>(C, i) \<in># {#(E, k) \<in># P. E \<noteq> C'#}. Suc (size C)) < (\<Sum>(C, i) \<in># P. Suc (size C))"
    using multiset_sum_monotone_f'[of "{#(E, k) \<in># P. E \<noteq> C'#}" P size] by metis
  then show ?case
    unfolding natLess_def by auto
qed (auto simp: natLess_def)

lemma weighted_RP_measure_decreasing_P:
  assumes "St \<leadsto>\<^sub>w St'" and "(C, i) \<in># wP_of_wstate St"
  shows "(RP_combined_measure (weight (C, i)) St', RP_combined_measure (weight (C, i)) St)
    \<in> RP_combined_relation"
using assms proof (induction rule: weighted_RP.induct)
  case (backward_subsumption_P D N C' P Q n)

  define St where "St = (N, P, Q, n)"
  define P' where "P' = {#(E, k) \<in># P. E \<noteq> C'#}"
  define St' where "St' = (N, P', Q, n)"

  from backward_subsumption_P obtain i' where  "(C', i') \<in># P"
    by auto
  then have P'_sub_P: "P' \<subset># P"
    unfolding P'_def using filter_mset_strict_subset[of "(C', i')" P "\<lambda>Dj. fst Dj \<noteq> C'"]
    by (metis (no_types, lifting) filter_mset_cong fst_conv prod.case_eq_if)

  have P'_subeq_P_filter:
    "{#(Ca, ia) \<in># P'. ia \<le> weight (C, i)#} \<subseteq># {#(Ca, ia) \<in># P. ia \<le> weight (C, i)#}"
    using P'_sub_P by (auto intro: multiset_filter_mono)

  have "fst3 (RP_combined_measure (weight (C, i)) St')
    \<le> fst3 (RP_combined_measure (weight (C, i)) St)"
    unfolding St'_def St_def by auto
  moreover have "(\<Sum>(C, i) \<in># {#(Ca, ia) \<in># P'. ia \<le> weight (C, i)#}. Suc (size C))
    \<le> (\<Sum>x \<in># {#(Ca, ia) \<in># P. ia \<le> weight (C, i)#}. case x of (C, i) \<Rightarrow> Suc (size C))"
    using P'_subeq_P_filter by (rule sum_image_mset_mono)
  then have "fst3 (snd3 (RP_combined_measure (weight (C, i)) St'))
    \<le> fst3 (snd3 (RP_combined_measure (weight (C, i)) St))"
    unfolding St'_def St_def by auto
  moreover have "snd3 (snd3 (RP_combined_measure (weight (C, i)) St'))
    \<le> snd3 (snd3 (RP_combined_measure (weight (C, i)) St))"
    unfolding St'_def St_def by auto
  moreover from P'_subeq_P_filter have "size {#(Ca, ia) \<in># P'. ia \<le> weight (C, i)#}
    \<le> size {#(Ca, ia) \<in># P. ia \<le> weight (C, i)#}"
    by (simp add: size_mset_mono)
  then have "trd3 (snd3 (RP_combined_measure (weight (C, i)) St'))
    \<le> trd3 (snd3 (RP_combined_measure (weight (C, i)) St))"
    unfolding St'_def St_def unfolding fst_def snd_def by auto
  moreover from P'_sub_P have "(\<Sum>(C, i) \<in># P'. Suc (size C)) < (\<Sum>(C, i) \<in># P. Suc (size C))"
    using multiset_sum_monotone_f'[of "{#(E, k) \<in># P. E \<noteq> C'#}" P size] unfolding P'_def by metis
  then have "fst3 (trd3 (RP_combined_measure (weight (C, i)) St'))
    < fst3 (trd3 (RP_combined_measure (weight (C, i)) St))"
    unfolding P'_def St'_def St_def by auto
  ultimately show ?case
    unfolding natLess_def P'_def St'_def St_def by auto
next
  case (inference_computation P C' i' N n Q)
  then show ?case
  proof (cases "n \<le> weight (C, i)")
    case True
    then have "weight (C, i) + 1 - n > weight (C, i) + 1 - Suc n"
      by auto
    then show ?thesis
      unfolding natLess_def by auto
  next
    case n_nle_w: False

    define St :: "'a wstate" where "St = ({#}, P + {#(C', i')#}, Q, n)"
    define St' :: "'a wstate" where "St' =  (N, {#(D, j) \<in># P. D \<noteq> C'#}, Q + {#(C', i')#}, Suc n)"
    define concls :: "'a wclause set" where
      "concls = (\<lambda>D. (D, n)) ` concls_of (inference_system.inferences_between (ord_FO_\<Gamma> S)
         (fst ` set_mset Q) C')"

    have fin: "finite concls"
      unfolding concls_def using finite_ord_FO_resolution_inferences_between by auto

    have "{(D, ia) \<in> concls. ia \<le> weight (C, i)} = {}"
      unfolding concls_def using n_nle_w by auto
    then have "{#(D, ia) \<in># mset_set concls. ia \<le> weight (C, i)#} = {#}"
      using fin filter_mset_empty_if_finite_and_filter_set_empty[of concls] by auto
    then have n_low_weight_empty: "{#(D, ia) \<in># N. ia \<le> weight (C, i)#} = {#}"
      unfolding inference_computation unfolding concls_def by auto

    have "weight (C', i') \<le> weight (C, i)"
      using inference_computation by auto
    then have i'_le_w_Ci: "i' \<le> weight (C, i)"
      using timestamp_le_weight[of i' C'] by auto

    have subs: "{#(D, ia) \<in># N + {#(D, j) \<in># P. D \<noteq> C'#} + (Q + {#(C', i')#}). ia \<le> weight (C, i)#}
      \<subseteq># {#(D, ia) \<in># {#} + (P + {#(C', i')#}) + Q. ia \<le> weight (C, i)#}"
      using n_low_weight_empty by (auto simp: multiset_filter_mono)

    have "fst3 (RP_combined_measure (weight (C, i)) St')
      \<le> fst3 (RP_combined_measure (weight (C, i)) St)"
      unfolding St'_def St_def by auto
    moreover have "fst (RP_filtered_measure ((\<lambda>(D, ia). ia \<le> weight (C, i))) St') =
      (\<Sum>(C, i) \<in># {#(D, ia) \<in># N + {#(D, j) \<in># P. D \<noteq> C'#} + (Q + {#(C', i')#}).
         ia \<le> weight (C, i)#}. Suc (size C))"
      unfolding St'_def by auto
    also have "... \<le> (\<Sum>(C, i) \<in># {#(D, ia) \<in># {#} + (P + {#(C', i')#}) + Q. ia \<le> weight (C, i)#}.
      Suc (size C))"
      using subs sum_image_mset_mono by blast
    also have "... = fst (RP_filtered_measure (\<lambda>(D, ia). ia \<le> weight (C, i)) St)"
      unfolding St_def by auto
    finally have "fst3 (snd3 (RP_combined_measure (weight (C, i)) St'))
      \<le> fst3 (snd3 (RP_combined_measure (weight (C, i)) St))"
      by auto
    moreover have "snd3 (snd3 (RP_combined_measure (weight (C, i)) St')) =
      snd3 (snd3 (RP_combined_measure (weight (C, i)) St))"
      unfolding St_def St'_def using n_low_weight_empty by auto
    moreover have "trd3 (snd3 (RP_combined_measure (weight (C, i)) St')) <
      trd3 (snd3 (RP_combined_measure (weight (C, i)) St))"
      unfolding St_def St'_def using i'_le_w_Ci
      by (simp add: le_imp_less_Suc multiset_filter_mono size_mset_mono)
    ultimately show ?thesis
      unfolding natLess_def St'_def St_def lex_prod_def by force
  qed
qed (auto simp: natLess_def)

lemma preserve_min_or_delete_completely:
  assumes "St \<leadsto>\<^sub>w St'" "(C, i) \<in># wP_of_wstate St"
    "\<forall>k. (C, k) \<in># wP_of_wstate St \<longrightarrow> i \<le> k"
  shows "(C, i) \<in># wP_of_wstate St' \<or> (\<forall>j. (C, j) \<notin># wP_of_wstate St')"
using assms proof (induction rule: weighted_RP.induct)
  case (backward_reduction_P D L' N L \<sigma> C' P i' Q n)
  show ?case
  proof (cases "C = C' + {#L#}")
    case True_outer: True
    then have C_i_in: "(C, i) \<in># P + {#(C, i')#}"
      using backward_reduction_P by auto
    then have max: "\<And>k. (C, k) \<in># P + {#(C, i')#} \<Longrightarrow> k \<le> i'"
      using backward_reduction_P unfolding True_outer[symmetric] by auto
    then have "count (P + {#(C, i')#}) (C, i') \<ge> 1"
      by auto
    moreover
    {
      assume asm: "count (P + {#(C, i')#}) (C, i') = 1"
      then have nin_P: "(C, i') \<notin># P"
        using not_in_iff by force
      have ?thesis
      proof (cases "(C, i) = (C, i')")
        case True
        then have "i = i'"
          by auto
        then have "\<forall>j. (C, j) \<in># P + {#(C, i')#} \<longrightarrow> j = i'"
          using max backward_reduction_P(6) unfolding True_outer[symmetric] by force
        then show ?thesis
          using True_outer[symmetric] nin_P by auto
      next
        case False
        then show ?thesis
          using C_i_in by auto
      qed
    }
    moreover
    {
      assume "count (P + {#(C, i')#}) (C, i') > 1"
      then have ?thesis
        using C_i_in by auto
    }
    ultimately show ?thesis
      by (cases "count (P + {#(C, i')#}) (C, i') = 1") auto
  next
    case False
    then show ?thesis
      using backward_reduction_P by auto
  qed
qed auto

lemma preserve_min_P:
  assumes
    "St \<leadsto>\<^sub>w St'" "(C, j) \<in># wP_of_wstate St'" and
    "(C, i) \<in># wP_of_wstate St" and
    "\<forall>k. (C, k) \<in># wP_of_wstate St \<longrightarrow> i \<le> k"
  shows "(C, i) \<in># wP_of_wstate St'"
  using assms preserve_min_or_delete_completely by blast

lemma preserve_min_P_Sts:
  assumes
    "enat (Suc k) < llength Sts" and
    "(C, i) \<in># wP_of_wstate (lnth Sts k)" and
    "(C, j) \<in># wP_of_wstate (lnth Sts (Suc k))" and
    "\<forall>j. (C, j) \<in># wP_of_wstate (lnth Sts k) \<longrightarrow> i \<le> j"
  shows "(C, i) \<in># wP_of_wstate (lnth Sts (Suc k))"
  using deriv assms chain_lnth_rel preserve_min_P by metis

lemma in_lnth_in_Supremum_ldrop:
  assumes "i < llength xs" and "x \<in># (lnth xs i)"
  shows "x \<in> Sup_llist (lmap set_mset (ldrop (enat i) xs))"
  using assms by (metis (no_types) ldrop_eq_LConsD ldropn_0 llist.simps(13) contra_subsetD
      ldrop_enat ldropn_Suc_conv_ldropn lnth_0 lnth_lmap lnth_subset_Sup_llist)

lemma persistent_wclause_in_P_if_persistent_clause_in_P:
  assumes "C \<in> Liminf_llist (lmap P_of_state (lmap state_of_wstate Sts))"
  shows "\<exists>i. (C, i) \<in> Liminf_llist (lmap (set_mset \<circ> wP_of_wstate) Sts)"
proof -
  obtain t_C where t_C_p:
    "enat t_C < llength Sts"
    "\<And>t. t_C \<le> t \<Longrightarrow> t < llength Sts \<Longrightarrow> C \<in> P_of_state (state_of_wstate (lnth Sts t))"
    using assms unfolding Liminf_llist_def by auto
  then obtain i where i_p:
    "(C, i) \<in># wP_of_wstate (lnth Sts t_C)"
    using t_C_p by (cases "lnth Sts t_C") force

  have Ci_in_nth_wP: "\<exists>i. (C, i) \<in># wP_of_wstate (lnth Sts (t_C + t))" if "t_C + t < llength Sts"
    for t
    using that t_C_p(2)[of "t_C + _"] by (cases "lnth Sts (t_C + t)") force

  define in_Sup_wP :: "nat \<Rightarrow> bool" where
    "in_Sup_wP = (\<lambda>i. (C, i) \<in> Sup_llist (lmap (set_mset \<circ> wP_of_wstate) (ldrop t_C Sts)))"

  have "in_Sup_wP i"
    using i_p assms(1) in_lnth_in_Supremum_ldrop[of t_C "lmap wP_of_wstate Sts" "(C, i)"] t_C_p
    by (simp add: in_Sup_wP_def llist.map_comp)
  then obtain j where j_p: "is_least in_Sup_wP j"
    unfolding in_Sup_wP_def[symmetric] using least_exists by metis
  then have "\<forall>i. (C, i) \<in> Sup_llist (lmap (set_mset \<circ> wP_of_wstate) (ldrop t_C Sts)) \<longrightarrow> j \<le> i"
    unfolding is_least_def in_Sup_wP_def using not_less by blast
  then have j_smallest:
    "\<And>i t. enat (t_C + t) < llength Sts \<Longrightarrow> (C, i) \<in># wP_of_wstate (lnth Sts (t_C + t)) \<Longrightarrow> j \<le> i"
    unfolding comp_def
    by (smt add.commute ldrop_enat ldrop_eq_LConsD ldrop_ldrop ldropn_Suc_conv_ldropn
        plus_enat_simps(1)  lnth_ldropn Sup_llist_def UN_I ldrop_lmap llength_lmap lnth_lmap
        mem_Collect_eq)
  from j_p have "\<exists>t_Cj. t_Cj < llength (ldrop (enat t_C) Sts)
    \<and> (C, j) \<in># wP_of_wstate (lnth (ldrop t_C Sts) t_Cj)"
    unfolding in_Sup_wP_def Sup_llist_def is_least_def by simp
  then obtain t_Cj where j_p:
    "(C,j) \<in># wP_of_wstate (lnth Sts (t_C + t_Cj))"
    "enat (t_C + t_Cj) < llength Sts"
    by (smt add.commute ldrop_enat ldrop_eq_LConsD ldrop_ldrop ldropn_Suc_conv_ldropn
        plus_enat_simps(1) lhd_ldropn)
  have Ci_stays:
    "t_C + t_Cj + t < llength Sts \<Longrightarrow> (C,j) \<in># wP_of_wstate (lnth Sts (t_C + t_Cj + t))" for t
  proof (induction t)
    case 0
    then show ?case
      using j_p by (simp add: add.commute)
  next
    case (Suc t)
    have any_Ck_in_wP: "j \<le> k" if "(C, k) \<in># wP_of_wstate (lnth Sts (t_C + t_Cj + t))" for k
      using that j_p j_smallest Suc
      by (smt Suc_ile_eq add.commute add.left_commute add_Suc less_imp_le plus_enat_simps(1)
          the_enat.simps)
    from Suc have Cj_in_wP: "(C, j) \<in># wP_of_wstate (lnth Sts (t_C + t_Cj + t))"
      by (metis (no_types, hide_lams) Suc_ile_eq add.commute add_Suc_right less_imp_le)
    moreover have "C \<in> P_of_state (state_of_wstate (lnth Sts (Suc (t_C + t_Cj + t))))"
      using t_C_p(2) Suc.prems by auto
    then have "\<exists>k. (C, k) \<in># wP_of_wstate (lnth Sts (Suc (t_C + t_Cj + t)))"
      by (smt Suc.prems Ci_in_nth_wP add.commute add.left_commute add_Suc_right enat_ord_code(4))
    ultimately have "(C, j) \<in># wP_of_wstate (lnth Sts (Suc (t_C + t_Cj + t)))"
      using preserve_min_P_Sts Cj_in_wP any_Ck_in_wP Suc.prems by force
    then have "(C, j) \<in># lnth (lmap wP_of_wstate Sts) (Suc (t_C + t_Cj + t))"
      using Suc.prems by auto
    then show ?case
      by (smt Suc.prems add.commute add_Suc_right lnth_lmap)
  qed
  then have "(\<And>t. t_C + t_Cj \<le> t \<Longrightarrow> t < llength (lmap (set_mset \<circ> wP_of_wstate) Sts) \<Longrightarrow>
    (C, j) \<in># wP_of_wstate (lnth Sts t))"
    using Ci_stays[of "_ - (t_C + t_Cj)"] by (metis le_add_diff_inverse llength_lmap)
  then have "(C, j) \<in> Liminf_llist (lmap (set_mset \<circ> wP_of_wstate) Sts)"
    unfolding Liminf_llist_def using j_p by auto
  then show "\<exists>i. (C, i) \<in> Liminf_llist (lmap (set_mset \<circ> wP_of_wstate) Sts)"
    by auto
qed

lemma lfinite_not_LNil_nth_llast:
  assumes "lfinite Sts" and "Sts \<noteq> LNil"
  shows "\<exists>i < llength Sts. lnth Sts i = llast Sts \<and> (\<forall>j < llength Sts. j \<le> i)"
using assms proof (induction rule: lfinite.induct)
  case (lfinite_LConsI xs x)
  then show ?case
  proof (cases "xs = LNil")
    case True
    show ?thesis
      using True zero_enat_def by auto
  next
    case False
    then obtain i where
      i_p: "enat i < llength xs \<and> lnth xs i = llast xs \<and> (\<forall>j < llength xs. j \<le> enat i)"
      using lfinite_LConsI by auto
    then have "enat (Suc i) < llength (LCons x xs)"
      by (simp add: Suc_ile_eq)
    moreover from i_p have "lnth (LCons x xs) (Suc i) = llast (LCons x xs)"
      by (metis gr_implies_not_zero llast_LCons llength_lnull lnth_Suc_LCons)
    moreover from i_p have "\<forall>j < llength (LCons x xs). j \<le> enat (Suc i)"
      by (metis antisym_conv2 eSuc_enat eSuc_ile_mono ileI1 iless_Suc_eq llength_LCons)
    ultimately show ?thesis
      by auto
  qed
qed auto

lemma fair_if_finite:
  assumes fin: "lfinite Sts"
  shows "fair_state_seq (lmap state_of_wstate Sts)"
proof (rule ccontr)
  assume unfair: "\<not> fair_state_seq (lmap state_of_wstate Sts)"

  have no_inf_from_last: "\<forall>y. \<not> llast Sts \<leadsto>\<^sub>w y"
    using fin full_chain_iff_chain[of "(\<leadsto>\<^sub>w)" Sts] full_deriv by auto

  from unfair obtain C where
    "C \<in> Liminf_llist (lmap N_of_state (lmap state_of_wstate Sts))
       \<union> Liminf_llist (lmap P_of_state (lmap state_of_wstate Sts))"
    unfolding fair_state_seq_def Liminf_state_def by auto
  then obtain i where i_p:
    "enat i < llength Sts"
    "\<And>j. i \<le> j \<Longrightarrow> enat j < llength Sts \<Longrightarrow>
     C \<in> N_of_state (state_of_wstate (lnth Sts j)) \<union> P_of_state (state_of_wstate (lnth Sts j))"
    unfolding Liminf_llist_def by auto

  have C_in_llast:
    "C \<in> N_of_state (state_of_wstate (llast Sts)) \<union> P_of_state (state_of_wstate (llast Sts))"
  proof -
    obtain l where
      l_p: "enat l < llength Sts \<and> lnth Sts l = llast Sts \<and> (\<forall>j < llength Sts. j \<le> enat l)"
      using fin lfinite_not_LNil_nth_llast i_p(1) by fastforce
    then have
      "C \<in> N_of_state (state_of_wstate (lnth Sts l)) \<union> P_of_state (state_of_wstate (lnth Sts l))"
      using i_p(1) i_p(2)[of l] by auto
    then show ?thesis
      using l_p by auto
  qed

  define N :: "'a wclause multiset" where "N = wN_of_wstate (llast Sts)"
  define P :: "'a wclause multiset" where "P = wP_of_wstate (llast Sts)"
  define Q :: "'a wclause multiset" where "Q = wQ_of_wstate (llast Sts)"
  define n :: nat where "n = n_of_wstate (llast Sts)"

  {
    assume "N_of_state (state_of_wstate (llast Sts)) \<noteq> {}"
    then obtain D j where "(D, j) \<in># N"
      unfolding N_def by (cases "llast Sts") auto
    then have "llast Sts \<leadsto>\<^sub>w (N - {#(D, j)#}, P + {#(D, j)#}, Q, n)"
      using weighted_RP.clause_processing[of "N - {#(D, j)#}" D j P Q n]
      unfolding N_def P_def Q_def n_def by auto
    then have "\<exists>St'. llast Sts \<leadsto>\<^sub>w St'"
      by auto
  }
  moreover
  {
    assume a: "N_of_state (state_of_wstate (llast Sts)) = {}"
    then have b: "N = {#}"
      unfolding N_def by (cases "llast Sts") auto
    from a have "C \<in> P_of_state (state_of_wstate (llast Sts))"
      using C_in_llast by auto
    then obtain D j where "(D, j) \<in># P"
      unfolding P_def by (cases "llast Sts") auto
    then have "weight (D, j) \<in> weight ` set_mset P"
      by auto
    then have "\<exists>w. is_least (\<lambda>w. w \<in> (weight ` set_mset P)) w"
      using least_exists by auto
    then have "\<exists>D j. (\<forall>(D', j') \<in># P. weight (D, j) \<le> weight (D', j')) \<and> (D, j) \<in># P"
      using assms linorder_not_less unfolding is_least_def by (auto 6 0)
    then obtain D j where
      min: "(\<forall>(D', j') \<in># P. weight (D, j) \<le> weight (D', j'))" and
      Dj_in_p: "(D, j) \<in># P"
      by auto
    from min have min: "(\<forall>(D', j') \<in># P - {#(D, j)#}. weight (D, j) \<le> weight (D', j'))"
      using mset_subset_diff_self[OF Dj_in_p] by auto

    define N' where
      "N' = mset_set ((\<lambda>D'. (D', n)) ` concls_of (inference_system.inferences_between (ord_FO_\<Gamma> S)
         (set_mset (image_mset fst Q)) D))"

    have "llast Sts \<leadsto>\<^sub>w (N', {#(D', j') \<in># P - {#(D, j)#}. D' \<noteq> D#}, Q + {#(D,j)#}, Suc n)"
      using weighted_RP.inference_computation[of "P - {#(D, j)#}" D j N' n Q, OF min N'_def]
        of_wstate_split[symmetric, of "llast Sts"] Dj_in_p
      unfolding N_def[symmetric] P_def[symmetric] Q_def[symmetric] n_def[symmetric] b by auto
    then have "\<exists>St'. llast Sts \<leadsto>\<^sub>w St'"
      by auto
  }
  ultimately have "\<exists>St'. llast Sts \<leadsto>\<^sub>w St'"
    by auto
  then show False
    using no_inf_from_last by metis
qed

lemma N_of_state_state_of_wstate_wN_of_wstate:
  assumes "C \<in> N_of_state (state_of_wstate St)"
  shows "\<exists>i. (C, i) \<in># wN_of_wstate St"
  by (smt N_of_state.elims assms eq_fst_iff fstI fst_conv image_iff of_wstate_split set_image_mset
      state_of_wstate.simps)

lemma in_wN_of_wstate_in_N_of_wstate: "(C, i) \<in># wN_of_wstate St \<Longrightarrow> C \<in> N_of_wstate St"
  by (metis (mono_guards_query_query) N_of_state.simps fst_conv image_eqI of_wstate_split
      set_image_mset state_of_wstate.simps)

lemma in_wP_of_wstate_in_P_of_wstate: "(C, i) \<in># wP_of_wstate St \<Longrightarrow> C \<in> P_of_wstate St"
  by (metis (mono_guards_query_query) P_of_state.simps fst_conv image_eqI of_wstate_split
      set_image_mset state_of_wstate.simps)

lemma in_wQ_of_wstate_in_Q_of_wstate: "(C, i) \<in># wQ_of_wstate St \<Longrightarrow> C \<in> Q_of_wstate St"
  by (metis (mono_guards_query_query) Q_of_state.simps fst_conv image_eqI of_wstate_split
      set_image_mset state_of_wstate.simps)

lemma n_of_wstate_weighted_RP_increasing: "St \<leadsto>\<^sub>w St' \<Longrightarrow> n_of_wstate St \<le> n_of_wstate St'"
  by (induction rule: weighted_RP.induct) auto

lemma nth_of_wstate_monotonic:
  assumes "j < llength Sts" and "i \<le> j"
  shows "n_of_wstate (lnth Sts i) \<le> n_of_wstate (lnth Sts j)"
using assms proof (induction "j - i" arbitrary: i)
  case (Suc x)
  then have "x = j - (i + 1)"
    by auto
  then have "n_of_wstate (lnth Sts (i + 1)) \<le> n_of_wstate (lnth Sts j)"
    using Suc by auto
  moreover have "i < j"
    using Suc by auto
  then have "Suc i < llength Sts"
    using Suc by (metis enat_ord_simps(2) le_less_Suc_eq less_le_trans not_le)
  then have "lnth Sts i \<leadsto>\<^sub>w lnth Sts (Suc i)"
    using deriv chain_lnth_rel[of "(\<leadsto>\<^sub>w)" Sts i] by auto
  then have "n_of_wstate (lnth Sts i) \<le> n_of_wstate (lnth Sts (i + 1))"
    using n_of_wstate_weighted_RP_increasing[of "lnth Sts i" "lnth Sts (i + 1)"] by auto
  ultimately show ?case
    by auto
qed auto

lemma infinite_chain_relation_measure:
  assumes
    measure_decreasing: "\<And>St St'. P St \<Longrightarrow> R St St' \<Longrightarrow> (m St', m St) \<in> mR" and
    non_infer_chain: "chain R (ldrop (enat k) Sts)" and
    inf: "llength Sts = \<infinity>" and
    P: "\<And>i. P (lnth (ldrop (enat k) Sts) i)"
  shows "chain (\<lambda>x y. (x, y) \<in> mR)\<inverse>\<inverse> (lmap m (ldrop (enat k) Sts))"
proof (rule lnth_rel_chain)
  show "\<not> lnull (lmap m (ldrop (enat k) Sts))"
    using assms by auto
next
  from inf have ldrop_inf: "llength (ldrop (enat k) Sts) = \<infinity> \<and> \<not> lfinite (ldrop (enat k) Sts)"
    using inf by (auto simp: llength_eq_infty_conv_lfinite)
  {
    fix j :: "nat"
    define St where "St = lnth (ldrop (enat k) Sts) j"
    define St' where "St' = lnth (ldrop (enat k) Sts) (j + 1)"
    have P': "P St \<and> P St'"
      unfolding St_def St'_def using P by auto
    from ldrop_inf have "R St St'"
      unfolding St_def St'_def
      using non_infer_chain infinite_chain_lnth_rel[of "ldrop (enat k) Sts" R j] by auto
    then have "(m St', m St) \<in> mR"
      using measure_decreasing P' by auto
    then have "(lnth (lmap m (ldrop (enat k) Sts)) (j + 1), lnth (lmap m (ldrop (enat k) Sts)) j)
      \<in> mR"
      unfolding St_def St'_def using lnth_lmap
      by (smt enat.distinct(1) enat_add_left_cancel enat_ord_simps(4) inf ldrop_lmap llength_lmap
          lnth_ldrop plus_enat_simps(3))
  }
  then show "\<forall>j. enat (j + 1) < llength (lmap m (ldrop (enat k) Sts)) \<longrightarrow>
    (\<lambda>x y. (x, y) \<in> mR)\<inverse>\<inverse> (lnth (lmap m (ldrop (enat k) Sts)) j)
      (lnth (lmap m (ldrop (enat k) Sts)) (j + 1))"
    by blast
qed

theorem weighted_RP_fair: "fair_state_seq (lmap state_of_wstate Sts)"
proof (rule ccontr)
  assume asm: "\<not> fair_state_seq (lmap state_of_wstate Sts)"
  then have inff: "\<not> lfinite Sts" using fair_if_finite
    by auto
  then have inf: "llength Sts = \<infinity>"
    using llength_eq_infty_conv_lfinite by auto
  from asm obtain C where
    "C \<in> Liminf_llist (lmap N_of_state (lmap state_of_wstate Sts))
       \<union> Liminf_llist (lmap P_of_state (lmap state_of_wstate Sts))"
    unfolding fair_state_seq_def Liminf_state_def by auto
  then show False
  proof
    assume "C \<in> Liminf_llist (lmap N_of_state (lmap state_of_wstate Sts))"
    then obtain x where "enat x < llength Sts"
      "\<forall>xa. x \<le> xa \<and> enat xa < llength Sts \<longrightarrow> C \<in> N_of_state (state_of_wstate (lnth Sts xa))"
      unfolding Liminf_llist_def by auto
    then have "\<exists>k. \<forall>j. k \<le> j \<longrightarrow> (\<exists>i. (C, i) \<in># wN_of_wstate (lnth Sts j))"
      unfolding Liminf_llist_def by (force simp add: inf N_of_state_state_of_wstate_wN_of_wstate)
    then obtain k where k_p:
      "\<And>j. k \<le> j \<Longrightarrow> \<exists>i. (C, i) \<in># wN_of_wstate (lnth Sts j)"
      unfolding Liminf_llist_def
      by auto
    have chain_drop_Sts: "chain (\<leadsto>\<^sub>w) (ldrop k Sts)"
      using deriv inf inff inf_chain_ldrop_chain by auto
    have in_N_j: "\<And>j. \<exists>i. (C, i) \<in># wN_of_wstate (lnth (ldrop k Sts) j)"
      using k_p by (simp add: add.commute inf)
    then have "chain (\<lambda>x y. (x, y) \<in> RP_filtered_relation)\<inverse>\<inverse> (lmap (RP_filtered_measure (\<lambda>Ci. True))
      (ldrop k Sts))"
      using inff inf weighted_RP_measure_decreasing_N chain_drop_Sts
        infinite_chain_relation_measure[of "\<lambda>St. \<exists>i. (C, i) \<in># wN_of_wstate St" "(\<leadsto>\<^sub>w)"] by blast
    then show False
      using wfP_iff_no_infinite_down_chain_llist[of "\<lambda>x y. (x, y) \<in> RP_filtered_relation"]
        wf_RP_filtered_relation inff
      by (metis (no_types, lifting) inf_llist_lnth ldrop_enat_inf_llist lfinite_inf_llist
        lfinite_lmap wfPUNIVI wf_induct_rule)
  next
    assume asm: "C \<in> Liminf_llist (lmap P_of_state (lmap state_of_wstate Sts))"
    from asm obtain i where i_p:
      "enat i < llength Sts"
      "\<And>j. i \<le> j \<and> enat j < llength Sts \<Longrightarrow> C \<in> P_of_state (state_of_wstate (lnth Sts j))"
      unfolding Liminf_llist_def by auto
    then obtain i where "(C, i) \<in> Liminf_llist (lmap (set_mset \<circ> wP_of_wstate) Sts)"
      using persistent_wclause_in_P_if_persistent_clause_in_P[of C] using asm inf by auto
    then have "\<exists>l. \<forall>k \<ge> l. (C, i) \<in> (set_mset \<circ> wP_of_wstate) (lnth Sts k)"
      unfolding Liminf_llist_def using inff inf by auto
    then obtain k where k_p:
      "(\<forall>k'\<ge>k. (C, i) \<in> (set_mset \<circ> wP_of_wstate) (lnth Sts k'))"
      by blast
    have Ci_in: "\<forall>k'. (C, i) \<in> (set_mset \<circ> wP_of_wstate) (lnth (ldrop k Sts) k')"
      using k_p lnth_ldrop[of k _ Sts] inf inff by force
    then have Ci_inn: "\<forall>k'. (C, i) \<in># (wP_of_wstate) (lnth (ldrop k Sts) k')"
      by auto
    have "chain (\<leadsto>\<^sub>w) (ldrop k Sts)"
      using deriv inf_chain_ldrop_chain inf inff by auto
    then have "chain (\<lambda>x y. (x, y) \<in> RP_combined_relation)\<inverse>\<inverse>
      (lmap (RP_combined_measure (weight (C, i))) (ldrop k Sts))"
      using inff inf Ci_in weighted_RP_measure_decreasing_P
        infinite_chain_relation_measure[of "\<lambda>St. (C, i) \<in># wP_of_wstate St" "(\<leadsto>\<^sub>w)"
          "RP_combined_measure (weight (C, i))" ]
      by auto
    then show False
      using wfP_iff_no_infinite_down_chain_llist[of "\<lambda>x y. (x, y) \<in> RP_combined_relation"]
        wf_RP_combined_relation inff
      by (smt inf_llist_lnth ldrop_enat_inf_llist lfinite_inf_llist lfinite_lmap wfPUNIVI
          wf_induct_rule)
  qed
qed

corollary weighted_RP_saturated: "src.saturated_upto (Liminf_llist (lmap grounding_of_wstate Sts))"
  using RP_saturated_if_fair[OF deriv_RP empty_Q0_RP weighted_RP_fair, unfolded llist.map_comp]
  by simp

corollary weighted_RP_complete:
  "\<not> satisfiable (grounding_of_wstate (lhd Sts)) \<Longrightarrow> {#} \<in> Q_of_state (Liminf_wstate Sts)"
  using RP_complete_if_fair[OF deriv_RP empty_Q0_RP weighted_RP_fair, simplified lhd_lmap_Sts]
  by simp

end

end

locale weighted_FO_resolution_prover_with_size_timestamp_factors =
  FO_resolution_prover S subst_atm id_subst comp_subst renamings_apart atm_of_atms mgu less_atm
  for
    S :: "('a :: wellorder) clause \<Rightarrow> 'a clause" and
    subst_atm :: "'a \<Rightarrow> 's \<Rightarrow> 'a" and
    id_subst :: "'s" and
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's" and
    renamings_apart :: "'a literal multiset list \<Rightarrow> 's list" and
    atm_of_atms :: "'a list \<Rightarrow> 'a" and
    mgu :: "'a set set \<Rightarrow> 's option" and
    less_atm :: "'a \<Rightarrow> 'a \<Rightarrow> bool" +
  fixes
    size_atm :: "'a \<Rightarrow> nat" and
    size_factor :: nat and
    timestamp_factor :: nat
  assumes
    timestamp_factor_pos: "timestamp_factor > 0"
begin

fun weight :: "'a wclause \<Rightarrow> nat" where
  "weight (C, i) = size_factor * size_multiset (size_literal size_atm) C + timestamp_factor * i"

lemma weight_mono: "i < j \<Longrightarrow> weight (C, i) < weight (C, j)"
  using timestamp_factor_pos by simp

declare weight.simps [simp del]

sublocale wrp: weighted_FO_resolution_prover _ _ _ _ _ _ _ _ weight
  by unfold_locales (rule weight_mono)

notation wrp.weighted_RP (infix "\<leadsto>\<^sub>w" 50)

end

end
