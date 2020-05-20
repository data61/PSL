(*  Title:       Labeled Lifting to Non-Ground Calculi of the Saturation Framework
 *  Author:      Sophie Tourret <stourret at mpi-inf.mpg.de>, 2019-2020 *)

section \<open>Labeled Liftings\<close>

text \<open>This section formalizes the extension of the lifting results to labeled
  calculi. This corresponds to section 3.4 of the report.\<close>

theory Labeled_Lifting_to_Non_Ground_Calculi
  imports Lifting_to_Non_Ground_Calculi
begin

subsection \<open>Labeled Lifting with a Family of Well-founded Orderings\<close>

locale labeled_lifting_w_wf_ord_family =
  lifting_with_wf_ordering_family Bot_F Inf_F Bot_G entails_G Inf_G Red_Inf_G Red_F_G \<G>_F \<G>_Inf Prec_F
  for
    Bot_F :: "'f set" and
    Inf_F :: "'f inference set" and
    Bot_G :: "'g set" and
    entails_G :: "'g set \<Rightarrow> 'g set \<Rightarrow> bool"  (infix "\<Turnstile>G" 50) and
    Inf_G :: "'g inference set" and
    Red_Inf_G :: "'g set \<Rightarrow> 'g inference set" and
    Red_F_G :: "'g set \<Rightarrow> 'g set" and
    \<G>_F :: "'f \<Rightarrow> 'g set" and
    \<G>_Inf :: "'f inference \<Rightarrow> 'g inference set option" and
    Prec_F :: "'g \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> bool"  (infix "\<sqsubset>" 50)
  + fixes
    l :: \<open>'l itself\<close> and
    Inf_FL :: \<open>('f \<times> 'l) inference set\<close>
  assumes
    Inf_F_to_Inf_FL: \<open>\<iota>\<^sub>F \<in> Inf_F \<Longrightarrow> length (Ll :: 'l list) = length (prems_of \<iota>\<^sub>F) \<Longrightarrow>
      \<exists>L0. Infer (zip (prems_of \<iota>\<^sub>F) Ll) (concl_of \<iota>\<^sub>F, L0) \<in> Inf_FL\<close> and
    Inf_FL_to_Inf_F: \<open>\<iota>\<^sub>F\<^sub>L \<in> Inf_FL \<Longrightarrow> Infer (map fst (prems_of \<iota>\<^sub>F\<^sub>L)) (fst (concl_of \<iota>\<^sub>F\<^sub>L)) \<in> Inf_F\<close>
begin

definition to_F :: \<open>('f \<times> 'l) inference \<Rightarrow> 'f inference\<close> where
  \<open>to_F \<iota>\<^sub>F\<^sub>L = Infer (map fst (prems_of \<iota>\<^sub>F\<^sub>L)) (fst (concl_of \<iota>\<^sub>F\<^sub>L))\<close>

definition Bot_FL :: \<open>('f \<times> 'l) set\<close> where \<open>Bot_FL = Bot_F \<times> UNIV\<close>

definition \<G>_F_L :: \<open>('f \<times> 'l) \<Rightarrow> 'g set\<close> where \<open>\<G>_F_L CL = \<G>_F (fst CL)\<close>

definition \<G>_Inf_L :: \<open>('f \<times> 'l) inference \<Rightarrow> 'g inference set option\<close> where \<open>\<G>_Inf_L \<iota>\<^sub>F\<^sub>L = \<G>_Inf (to_F \<iota>\<^sub>F\<^sub>L)\<close>

(* lem:labeled-grounding-function *)
sublocale labeled_standard_lifting: standard_lifting
  where
    Bot_F = Bot_FL and
    Inf_F = Inf_FL and
    \<G>_F = \<G>_F_L and
    \<G>_Inf = \<G>_Inf_L
proof
  show "Bot_FL \<noteq> {}"
    unfolding Bot_FL_def using Bot_F_not_empty by simp
next
  show "B\<in>Bot_FL \<Longrightarrow> \<G>_F_L B \<noteq> {}" for B
    unfolding \<G>_F_L_def Bot_FL_def using Bot_map_not_empty by auto
next
  show "B\<in>Bot_FL \<Longrightarrow> \<G>_F_L B \<subseteq> Bot_G" for B
    unfolding \<G>_F_L_def Bot_FL_def using Bot_map by force
next
  fix CL
  show "\<G>_F_L CL \<inter> Bot_G \<noteq> {} \<longrightarrow> CL \<in> Bot_FL"
    unfolding \<G>_F_L_def Bot_FL_def using Bot_cond
    by (metis SigmaE UNIV_I UNIV_Times_UNIV mem_Sigma_iff prod.sel(1))
next
  fix \<iota>
  assume
    i_in: \<open>\<iota> \<in> Inf_FL\<close> and
    ground_not_none: \<open>\<G>_Inf_L \<iota> \<noteq> None\<close>
  then show "the (\<G>_Inf_L \<iota>) \<subseteq> Red_Inf_G (\<G>_F_L (concl_of \<iota>))"
    unfolding \<G>_Inf_L_def \<G>_F_L_def to_F_def using inf_map Inf_FL_to_Inf_F by fastforce
qed

abbreviation Labeled_Empty_Order :: \<open> ('f \<times> 'l) \<Rightarrow> ('f \<times> 'l) \<Rightarrow> bool\<close> where
  "Labeled_Empty_Order C1 C2 \<equiv> False"

sublocale labeled_lifting_w_empty_ord_family :
  lifting_with_wf_ordering_family Bot_FL Inf_FL Bot_G entails_G Inf_G Red_Inf_G Red_F_G
    \<G>_F_L \<G>_Inf_L "\<lambda>g. Labeled_Empty_Order"
proof
  show "po_on Labeled_Empty_Order UNIV"
    unfolding po_on_def by (simp add: transp_onI wfp_on_imp_irreflp_on)
  show "wfp_on Labeled_Empty_Order UNIV"
    unfolding wfp_on_def by simp
qed

notation "labeled_standard_lifting.entails_\<G>" (infix "\<Turnstile>\<G>L" 50)

(* lem:labeled-consequence *)
lemma labeled_entailment_lifting: "NL1 \<Turnstile>\<G>L NL2 \<longleftrightarrow> fst ` NL1 \<Turnstile>\<G> fst ` NL2"
  unfolding labeled_standard_lifting.entails_\<G>_def \<G>_F_L_def entails_\<G>_def by auto

lemma (in-) subset_fst: "A \<subseteq> fst ` AB \<Longrightarrow> \<forall>x \<in> A. \<exists>y. (x,y) \<in> AB" by fastforce

lemma red_inf_impl: "\<iota> \<in> labeled_lifting_w_empty_ord_family.Red_Inf_\<G> NL \<Longrightarrow> to_F \<iota> \<in> Red_Inf_\<G> (fst ` NL)"
  unfolding labeled_lifting_w_empty_ord_family.Red_Inf_\<G>_def Red_Inf_\<G>_def \<G>_Inf_L_def \<G>_F_L_def to_F_def
  using Inf_FL_to_Inf_F by auto

(* lem:labeled-saturation *)
lemma labeled_saturation_lifting:
  "labeled_lifting_w_empty_ord_family.lifted_calculus_with_red_crit.saturated NL \<Longrightarrow>
    empty_order_lifting.lifted_calculus_with_red_crit.saturated (fst ` NL)"
  unfolding labeled_lifting_w_empty_ord_family.lifted_calculus_with_red_crit.saturated_def
    empty_order_lifting.lifted_calculus_with_red_crit.saturated_def
    labeled_standard_lifting.Non_ground.Inf_from_def Non_ground.Inf_from_def
proof clarify
  fix \<iota>
  assume
    subs_Red_Inf: "{\<iota> \<in> Inf_FL. set (prems_of \<iota>) \<subseteq> NL} \<subseteq> labeled_lifting_w_empty_ord_family.Red_Inf_\<G> NL" and
    i_in: "\<iota> \<in> Inf_F" and
    i_prems: "set (prems_of \<iota>) \<subseteq> fst ` NL"
  define Lli where "Lli i \<equiv> (SOME x. ((prems_of \<iota>)!i,x) \<in> NL)" for i
  have [simp]:"((prems_of \<iota>)!i,Lli i) \<in> NL" if "i < length (prems_of \<iota>)" for i
    using that subset_fst[OF i_prems] unfolding Lli_def by (meson nth_mem someI_ex)
  define Ll where "Ll \<equiv> map Lli [0..<length (prems_of \<iota>)]"
  have Ll_length: "length Ll = length (prems_of \<iota>)" unfolding Ll_def by auto
  have subs_NL: "set (zip (prems_of \<iota>) Ll) \<subseteq> NL" unfolding Ll_def by (auto simp:in_set_zip)
  obtain L0 where L0: "Infer (zip (prems_of \<iota>) Ll) (concl_of \<iota>, L0) \<in> Inf_FL"
    using Inf_F_to_Inf_FL[OF i_in Ll_length] ..
  define \<iota>_FL where "\<iota>_FL = Infer (zip (prems_of \<iota>) Ll) (concl_of \<iota>, L0)"
  then have "set (prems_of \<iota>_FL) \<subseteq> NL" using subs_NL by simp
  then have "\<iota>_FL \<in> {\<iota> \<in> Inf_FL. set (prems_of \<iota>) \<subseteq> NL}" unfolding \<iota>_FL_def using L0 by blast
  then have "\<iota>_FL \<in> labeled_lifting_w_empty_ord_family.Red_Inf_\<G> NL" using subs_Red_Inf by fast
  moreover have "\<iota> = to_F \<iota>_FL" unfolding to_F_def \<iota>_FL_def using Ll_length by (cases \<iota>) auto
  ultimately show "\<iota> \<in> Red_Inf_\<G> (fst ` NL)" by (auto intro:red_inf_impl)
qed

(* lem:labeled-static-ref-compl *)
lemma stat_ref_comp_to_labeled_sta_ref_comp: "static_refutational_complete_calculus Bot_F Inf_F (\<Turnstile>\<G>) Red_Inf_\<G> Red_F_\<G> \<Longrightarrow>
  static_refutational_complete_calculus Bot_FL Inf_FL (\<Turnstile>\<G>L)
    labeled_lifting_w_empty_ord_family.Red_Inf_\<G> labeled_lifting_w_empty_ord_family.Red_F_\<G>"
  unfolding static_refutational_complete_calculus_def
proof (rule conjI impI; clarify)
  interpret calculus_with_red_crit Bot_FL Inf_FL labeled_standard_lifting.entails_\<G>
    labeled_lifting_w_empty_ord_family.Red_Inf_\<G> labeled_lifting_w_empty_ord_family.Red_F_\<G>
    by (simp add:
      labeled_lifting_w_empty_ord_family.lifted_calculus_with_red_crit.calculus_with_red_crit_axioms)
  show "calculus_with_red_crit Bot_FL Inf_FL (\<Turnstile>\<G>L) labeled_lifting_w_empty_ord_family.Red_Inf_\<G>
    labeled_lifting_w_empty_ord_family.Red_F_\<G>"
    by standard
next
  assume
    calc: "calculus_with_red_crit Bot_F Inf_F (\<Turnstile>\<G>) Red_Inf_\<G> Red_F_\<G>" and
    static: "static_refutational_complete_calculus_axioms Bot_F Inf_F (\<Turnstile>\<G>) Red_Inf_\<G>"
  show "static_refutational_complete_calculus_axioms Bot_FL Inf_FL (\<Turnstile>\<G>L)
    labeled_lifting_w_empty_ord_family.Red_Inf_\<G>"
    unfolding static_refutational_complete_calculus_axioms_def
  proof (intro conjI impI allI)
    fix Bl :: \<open>'f \<times> 'l\<close> and Nl :: \<open>('f \<times> 'l) set\<close>
    assume
      Bl_in: \<open>Bl \<in> Bot_FL\<close> and
      Nl_sat: \<open>labeled_lifting_w_empty_ord_family.lifted_calculus_with_red_crit.saturated Nl\<close> and
      Nl_entails_Bl: \<open>Nl \<Turnstile>\<G>L {Bl}\<close>
    have static_axioms: "B \<in> Bot_F \<longrightarrow> empty_order_lifting.lifted_calculus_with_red_crit.saturated N \<longrightarrow>
      N \<Turnstile>\<G> {B} \<longrightarrow> (\<exists>B'\<in>Bot_F. B' \<in> N)" for B N
      using static[unfolded static_refutational_complete_calculus_axioms_def] by fast
    define B where "B = fst Bl"
    have B_in: "B \<in> Bot_F" using Bl_in Bot_FL_def B_def SigmaE by force
    define N where "N = fst ` Nl"
    have N_sat: "empty_order_lifting.lifted_calculus_with_red_crit.saturated N"
      using N_def Nl_sat labeled_saturation_lifting by blast
    have N_entails_B: "N \<Turnstile>\<G> {B}"
      using Nl_entails_Bl unfolding labeled_entailment_lifting N_def B_def by force
    have "\<exists>B' \<in> Bot_F. B' \<in> N" using B_in N_sat N_entails_B static_axioms[of B N] by blast
    then obtain B' where in_Bot: "B' \<in> Bot_F" and in_N: "B' \<in> N" by force
    then have "B' \<in> fst ` Bot_FL" unfolding Bot_FL_def by fastforce
    obtain Bl' where in_Nl: "Bl' \<in> Nl" and fst_Bl': "fst Bl' = B'"
      using in_N unfolding N_def by blast
    have "Bl' \<in> Bot_FL" unfolding Bot_FL_def using fst_Bl' in_Bot vimage_fst by fastforce
    then show \<open>\<exists>Bl'\<in>Bot_FL. Bl' \<in> Nl\<close> using in_Nl by blast
  qed
qed

end

subsection \<open>Labeled Lifting with a Family of Redundancy Criteria\<close>

locale labeled_lifting_with_red_crit_family = no_labels: standard_lifting_with_red_crit_family Inf_F
  Bot_G Inf_G Q entails_q Red_Inf_q Red_F_q Bot_F \<G>_F_q \<G>_Inf_q "\<lambda>g. Empty_Order"
  for
    Bot_F :: "'f set" and
    Inf_F :: "'f inference set" and
    Bot_G :: "'g set" and
    Q :: "'q itself" and
    entails_q :: "'q \<Rightarrow> 'g set \<Rightarrow> 'g set \<Rightarrow> bool"  and
    Inf_G :: "'g inference set" and
    Red_Inf_q :: "'q \<Rightarrow> 'g set \<Rightarrow> 'g inference set" and
    Red_F_q :: "'q \<Rightarrow> 'g set \<Rightarrow> 'g set" and
    \<G>_F_q :: "'q \<Rightarrow> 'f \<Rightarrow> 'g set" and
    \<G>_Inf_q :: "'q \<Rightarrow> 'f inference \<Rightarrow> 'g inference set option"
  + fixes
    l :: "'l itself" and
    Inf_FL :: \<open>('f \<times> 'l) inference set\<close>
  assumes
    Inf_F_to_Inf_FL: \<open>\<iota>\<^sub>F \<in> Inf_F \<Longrightarrow> length (Ll :: 'l list) = length (prems_of \<iota>\<^sub>F) \<Longrightarrow> \<exists>L0. Infer (zip (prems_of \<iota>\<^sub>F) Ll) (concl_of \<iota>\<^sub>F, L0) \<in> Inf_FL\<close> and
    Inf_FL_to_Inf_F: \<open>\<iota>\<^sub>F\<^sub>L \<in> Inf_FL \<Longrightarrow> Infer (map fst (prems_of \<iota>\<^sub>F\<^sub>L)) (fst (concl_of \<iota>\<^sub>F\<^sub>L)) \<in> Inf_F\<close>
begin

definition to_F :: \<open>('f \<times> 'l) inference \<Rightarrow> 'f inference\<close> where
  \<open>to_F \<iota>\<^sub>F\<^sub>L = Infer (map fst (prems_of \<iota>\<^sub>F\<^sub>L)) (fst (concl_of \<iota>\<^sub>F\<^sub>L))\<close>

definition Bot_FL :: \<open>('f \<times> 'l) set\<close> where \<open>Bot_FL = Bot_F \<times> UNIV\<close>

definition \<G>_F_L_q :: \<open>'q \<Rightarrow> ('f \<times> 'l) \<Rightarrow> 'g set\<close> where \<open>\<G>_F_L_q q CL = \<G>_F_q q (fst CL)\<close>

definition \<G>_Inf_L_q :: \<open>'q \<Rightarrow> ('f \<times> 'l) inference \<Rightarrow> 'g inference set option\<close> where
  \<open>\<G>_Inf_L_q q \<iota>\<^sub>F\<^sub>L = \<G>_Inf_q q (to_F \<iota>\<^sub>F\<^sub>L)\<close>

definition \<G>_set_L_q :: "'q \<Rightarrow> ('f \<times> 'l) set \<Rightarrow> 'g set" where
  "\<G>_set_L_q q N \<equiv> \<Union> (\<G>_F_L_q q ` N)"

definition Red_Inf_\<G>_L_q :: "'q \<Rightarrow> ('f \<times> 'l) set \<Rightarrow> ('f \<times> 'l) inference set" where
  "Red_Inf_\<G>_L_q q N = {\<iota> \<in> Inf_FL. ((\<G>_Inf_L_q q \<iota>) \<noteq> None \<and> the (\<G>_Inf_L_q q \<iota>) \<subseteq> Red_Inf_q q (\<G>_set_L_q q N))
    \<or> ((\<G>_Inf_L_q q \<iota> = None) \<and> \<G>_F_L_q q (concl_of \<iota>) \<subseteq> (\<G>_set_L_q q N \<union> Red_F_q q (\<G>_set_L_q q N)))}"

definition Red_Inf_\<G>_L_Q :: "('f \<times> 'l) set \<Rightarrow> ('f \<times> 'l) inference set" where
  "Red_Inf_\<G>_L_Q N = \<Inter> {X N |X. X \<in> (Red_Inf_\<G>_L_q ` UNIV)}"

definition Labeled_Empty_Order :: \<open> ('f \<times> 'l) \<Rightarrow> ('f \<times> 'l) \<Rightarrow> bool\<close> where
  "Labeled_Empty_Order C1 C2 \<equiv> False"

definition Red_F_\<G>_empty_L_q :: "'q \<Rightarrow> ('f \<times> 'l) set \<Rightarrow> ('f \<times> 'l) set" where
  "Red_F_\<G>_empty_L_q q N = {C. \<forall>D \<in> \<G>_F_L_q q C. D \<in> Red_F_q q (\<G>_set_L_q q N) \<or>
    (\<exists>E \<in> N. Labeled_Empty_Order E C \<and> D \<in> \<G>_F_L_q q E)}"

definition Red_F_\<G>_empty_L :: "('f \<times> 'l) set \<Rightarrow> ('f \<times> 'l) set" where
  "Red_F_\<G>_empty_L N = \<Inter> {X N |X. X \<in> (Red_F_\<G>_empty_L_q ` UNIV)}"

definition entails_\<G>_L_q :: "'q \<Rightarrow> ('f \<times> 'l) set \<Rightarrow> ('f \<times> 'l) set \<Rightarrow> bool" where
  "entails_\<G>_L_q q N1 N2 \<equiv> entails_q q (\<G>_set_L_q q N1) (\<G>_set_L_q q N2)"

definition entails_\<G>_L_Q :: "('f \<times> 'l) set \<Rightarrow> ('f \<times> 'l) set \<Rightarrow> bool" (infix "\<Turnstile>\<inter>L" 50) where
  "entails_\<G>_L_Q N1 N2 \<equiv> \<forall>q. entails_\<G>_L_q q N1 N2"

lemma lifting_q: "labeled_lifting_w_wf_ord_family Bot_F Inf_F Bot_G (entails_q q) Inf_G (Red_Inf_q q)
  (Red_F_q q) (\<G>_F_q q) (\<G>_Inf_q q) (\<lambda>g. Empty_Order) Inf_FL"
proof -
  fix q
  show "labeled_lifting_w_wf_ord_family Bot_F Inf_F Bot_G (entails_q q) Inf_G (Red_Inf_q q)
    (Red_F_q q) (\<G>_F_q q) (\<G>_Inf_q q) (\<lambda>g. Empty_Order) Inf_FL"
    using no_labels.standard_lifting_family Inf_F_to_Inf_FL Inf_FL_to_Inf_F
    by (simp add: labeled_lifting_w_wf_ord_family_axioms_def labeled_lifting_w_wf_ord_family_def)
qed

lemma lifted_q: "standard_lifting Bot_FL Inf_FL Bot_G Inf_G (entails_q q) (Red_Inf_q q)
  (Red_F_q q) (\<G>_F_L_q q) (\<G>_Inf_L_q q)"
proof -
  fix q
  interpret q_lifting: labeled_lifting_w_wf_ord_family Bot_F Inf_F Bot_G "entails_q q" Inf_G
    "Red_Inf_q q" "Red_F_q q" "\<G>_F_q q" "\<G>_Inf_q q" "\<lambda>g. Empty_Order" l Inf_FL
    using lifting_q .
  have "\<G>_F_L_q q = q_lifting.\<G>_F_L"
    unfolding \<G>_F_L_q_def q_lifting.\<G>_F_L_def by simp
  moreover have "\<G>_Inf_L_q q = q_lifting.\<G>_Inf_L"
    unfolding \<G>_Inf_L_q_def q_lifting.\<G>_Inf_L_def to_F_def q_lifting.to_F_def by simp
  moreover have "Bot_FL = q_lifting.Bot_FL"
    unfolding Bot_FL_def q_lifting.Bot_FL_def by simp
  ultimately show "standard_lifting Bot_FL Inf_FL Bot_G Inf_G (entails_q q) (Red_Inf_q q) (Red_F_q q)
    (\<G>_F_L_q q) (\<G>_Inf_L_q q)"
    using q_lifting.labeled_standard_lifting.standard_lifting_axioms by simp
qed

lemma ord_fam_lifted_q: "lifting_with_wf_ordering_family Bot_FL Inf_FL Bot_G (entails_q q) Inf_G
    (Red_Inf_q q) (Red_F_q q) (\<G>_F_L_q q) (\<G>_Inf_L_q q) (\<lambda>g. Labeled_Empty_Order)"
proof -
  fix q
  interpret standard_q_lifting: standard_lifting Bot_FL Inf_FL Bot_G Inf_G "entails_q q"
    "Red_Inf_q q" "Red_F_q q" "\<G>_F_L_q q" "\<G>_Inf_L_q q"
    using lifted_q .
  have "minimal_element Labeled_Empty_Order UNIV"
    unfolding Labeled_Empty_Order_def
    by (simp add: minimal_element.intro po_on_def transp_onI wfp_on_imp_irreflp_on)
  then show "lifting_with_wf_ordering_family Bot_FL Inf_FL Bot_G (entails_q q) Inf_G
    (Red_Inf_q q) (Red_F_q q) (\<G>_F_L_q q) (\<G>_Inf_L_q q) (\<lambda>g. Labeled_Empty_Order)"
    using standard_q_lifting.standard_lifting_axioms
    by (simp add: lifting_with_wf_ordering_family_axioms.intro lifting_with_wf_ordering_family_def)
qed

lemma all_lifted_red_crit: "calculus_with_red_crit Bot_FL Inf_FL (entails_\<G>_L_q q) (Red_Inf_\<G>_L_q q)
  (Red_F_\<G>_empty_L_q q)"
proof -
  fix q
  interpret ord_q_lifting: lifting_with_wf_ordering_family Bot_FL Inf_FL Bot_G "entails_q q" Inf_G
    "Red_Inf_q q" "Red_F_q q" "\<G>_F_L_q q" "\<G>_Inf_L_q q" "\<lambda>g. Labeled_Empty_Order"
    using ord_fam_lifted_q .
  have "entails_\<G>_L_q q = ord_q_lifting.entails_\<G>"
    unfolding entails_\<G>_L_q_def \<G>_set_L_q_def ord_q_lifting.entails_\<G>_def by simp
  moreover have "Red_Inf_\<G>_L_q q = ord_q_lifting.Red_Inf_\<G>"
    unfolding Red_Inf_\<G>_L_q_def ord_q_lifting.Red_Inf_\<G>_def \<G>_set_L_q_def by simp
  moreover have "Red_F_\<G>_empty_L_q q = ord_q_lifting.Red_F_\<G>"
    unfolding Red_F_\<G>_empty_L_q_def ord_q_lifting.Red_F_\<G>_def \<G>_set_L_q_def by simp
  ultimately show "calculus_with_red_crit Bot_FL Inf_FL (entails_\<G>_L_q q) (Red_Inf_\<G>_L_q q)
    (Red_F_\<G>_empty_L_q q)"
    using ord_q_lifting.lifted_calculus_with_red_crit.calculus_with_red_crit_axioms by argo
qed

lemma all_lifted_cons_rel: "consequence_relation Bot_FL (entails_\<G>_L_q q)"
proof -
  fix q
  interpret q_red_crit: calculus_with_red_crit Bot_FL Inf_FL "entails_\<G>_L_q q" "Red_Inf_\<G>_L_q q"
    "Red_F_\<G>_empty_L_q q"
    using all_lifted_red_crit .
  show "consequence_relation Bot_FL (entails_\<G>_L_q q)"
    using q_red_crit.consequence_relation_axioms .
qed

sublocale labeled_cons_rel_family: consequence_relation_family Bot_FL Q entails_\<G>_L_q
  using all_lifted_cons_rel no_labels.lifted_calc_w_red_crit_family.Bot_not_empty
  unfolding Bot_FL_def
  by (simp add: consequence_relation_family.intro)

sublocale with_labels: calculus_with_red_crit_family Bot_FL Inf_FL Q entails_\<G>_L_q Red_Inf_\<G>_L_q
  Red_F_\<G>_empty_L_q
  using calculus_with_red_crit_family.intro[OF labeled_cons_rel_family.consequence_relation_family_axioms]
    all_lifted_cons_rel
  by (simp add: all_lifted_red_crit calculus_with_red_crit_family_axioms_def)

notation "no_labels.entails_\<G>_Q" (infix "\<Turnstile>\<inter>" 50)

(* lem:labeled-consequence-intersection *)
lemma labeled_entailment_lifting: "NL1 \<Turnstile>\<inter>L NL2 \<longleftrightarrow> fst ` NL1 \<Turnstile>\<inter> fst ` NL2"
  unfolding no_labels.entails_\<G>_Q_def no_labels.entails_\<G>_q_def no_labels.\<G>_set_q_def
    entails_\<G>_L_Q_def entails_\<G>_L_q_def \<G>_set_L_q_def \<G>_F_L_q_def
  by force

lemma subset_fst: "A \<subseteq> fst ` AB \<Longrightarrow> \<forall>x \<in> A. \<exists>y. (x,y) \<in> AB" by fastforce

lemma red_inf_impl: "\<iota> \<in> with_labels.Red_Inf_Q NL \<Longrightarrow>
  to_F \<iota> \<in> no_labels.empty_ord_lifted_calc_w_red_crit_family.Red_Inf_Q (fst ` NL)"
  unfolding no_labels.empty_ord_lifted_calc_w_red_crit_family.Red_Inf_Q_def with_labels.Red_Inf_Q_def
proof clarify
  fix X Xa q
  assume
    i_in_inter: "\<iota> \<in> \<Inter> {X NL |X. X \<in> Red_Inf_\<G>_L_q ` UNIV}"
  have i_in_q: "\<iota> \<in> Red_Inf_\<G>_L_q q NL" using i_in_inter image_eqI by blast
  then have i_in: "\<iota> \<in> Inf_FL" unfolding Red_Inf_\<G>_L_q_def by blast
  have to_F_in: "to_F \<iota> \<in> Inf_F" unfolding to_F_def using Inf_FL_to_Inf_F[OF i_in] .
  have rephrase1: "(\<Union>CL\<in>NL. \<G>_F_q q (fst CL)) = (\<Union> (\<G>_F_q q ` fst ` NL))" by blast
  have rephrase2: "fst (concl_of \<iota>) = concl_of (to_F \<iota>)"
    unfolding concl_of_def to_F_def by simp
  have subs_red: "((\<G>_Inf_L_q q \<iota>) \<noteq> None \<and> the (\<G>_Inf_L_q q \<iota>) \<subseteq> Red_Inf_q q (\<G>_set_L_q q NL))
    \<or> ((\<G>_Inf_L_q q \<iota> = None) \<and> \<G>_F_L_q q (concl_of \<iota>) \<subseteq> (\<G>_set_L_q q NL \<union> Red_F_q q (\<G>_set_L_q q NL)))"
    using i_in_q unfolding Red_Inf_\<G>_L_q_def by blast
  then have to_F_subs_red: "((\<G>_Inf_q q (to_F \<iota>)) \<noteq> None \<and>
      the (\<G>_Inf_q q (to_F \<iota>)) \<subseteq> Red_Inf_q q (no_labels.\<G>_set_q q (fst ` NL)))
    \<or> ((\<G>_Inf_q q (to_F \<iota>) = None) \<and>
      \<G>_F_q q (concl_of (to_F \<iota>)) \<subseteq> (no_labels.\<G>_set_q q (fst ` NL) \<union> Red_F_q q (no_labels.\<G>_set_q q (fst ` NL))))"
    unfolding \<G>_Inf_L_q_def \<G>_set_L_q_def no_labels.\<G>_set_q_def \<G>_F_L_q_def
    using rephrase1 rephrase2 by metis
  then show "to_F \<iota> \<in> no_labels.Red_Inf_\<G>_q q (fst ` NL)"
    using to_F_in unfolding no_labels.Red_Inf_\<G>_q_def by simp
qed

(* lem:labeled-saturation-intersection *)
lemma labeled_family_saturation_lifting: "with_labels.inter_red_crit_calculus.saturated NL \<Longrightarrow>
  no_labels.lifted_calc_w_red_crit_family.inter_red_crit_calculus.saturated (fst ` NL)"
  unfolding with_labels.inter_red_crit_calculus.saturated_def
    no_labels.lifted_calc_w_red_crit_family.inter_red_crit_calculus.saturated_def
    with_labels.Inf_from_def no_labels.Non_ground.Inf_from_def
proof clarify
  fix \<iota>F
  assume
    labeled_sat: "{\<iota> \<in> Inf_FL. set (prems_of \<iota>) \<subseteq> NL} \<subseteq> with_labels.Red_Inf_Q NL" and
    iF_in: "\<iota>F \<in> Inf_F" and
    iF_prems: "set (prems_of \<iota>F) \<subseteq> fst ` NL"
  define Lli where "Lli i \<equiv> (SOME x. ((prems_of \<iota>F)!i,x) \<in> NL)" for i
  have [simp]:"((prems_of \<iota>F)!i,Lli i) \<in> NL" if "i < length (prems_of \<iota>F)" for i
    using that subset_fst[OF iF_prems] nth_mem someI_ex unfolding Lli_def
    by metis
  define Ll where "Ll \<equiv> map Lli [0..<length (prems_of \<iota>F)]"
  have Ll_length: "length Ll = length (prems_of \<iota>F)" unfolding Ll_def by auto
  have subs_NL: "set (zip (prems_of \<iota>F) Ll) \<subseteq> NL" unfolding Ll_def by (auto simp:in_set_zip)
  obtain L0 where L0: "Infer (zip (prems_of \<iota>F) Ll) (concl_of \<iota>F, L0) \<in> Inf_FL"
    using Inf_F_to_Inf_FL[OF iF_in Ll_length] ..
  define \<iota>FL where "\<iota>FL = Infer (zip (prems_of \<iota>F) Ll) (concl_of \<iota>F, L0)"
  then have "set (prems_of \<iota>FL) \<subseteq> NL" using subs_NL by simp
  then have "\<iota>FL \<in> {\<iota> \<in> Inf_FL. set (prems_of \<iota>) \<subseteq> NL}" unfolding \<iota>FL_def using L0 by blast
  then have "\<iota>FL \<in> with_labels.Red_Inf_Q NL" using labeled_sat by fast
  moreover have "\<iota>F = to_F \<iota>FL" unfolding to_F_def \<iota>FL_def using Ll_length by (cases \<iota>F) auto
  ultimately show "\<iota>F \<in> no_labels.empty_ord_lifted_calc_w_red_crit_family.Red_Inf_Q (fst ` NL)"
    by (auto intro:red_inf_impl)
qed

(* thm:labeled-static-ref-compl-intersection *)
theorem labeled_static_ref: "static_refutational_complete_calculus Bot_F Inf_F (\<Turnstile>\<inter>)
  no_labels.empty_ord_lifted_calc_w_red_crit_family.Red_Inf_Q
  no_labels.empty_ord_lifted_calc_w_red_crit_family.Red_F_Q
  \<Longrightarrow> static_refutational_complete_calculus Bot_FL Inf_FL (\<Turnstile>\<inter>L) with_labels.Red_Inf_Q with_labels.Red_F_Q"
  unfolding static_refutational_complete_calculus_def
proof (rule conjI impI; clarify)
  show "calculus_with_red_crit Bot_FL Inf_FL (\<Turnstile>\<inter>L) with_labels.Red_Inf_Q with_labels.Red_F_Q"
    using with_labels.inter_red_crit_calculus.calculus_with_red_crit_axioms
    unfolding labeled_cons_rel_family.entails_Q_def entails_\<G>_L_Q_def .
next
  assume
    calc: "calculus_with_red_crit Bot_F Inf_F (\<Turnstile>\<inter>)
      no_labels.empty_ord_lifted_calc_w_red_crit_family.Red_Inf_Q
      no_labels.empty_ord_lifted_calc_w_red_crit_family.Red_F_Q" and
    static: "static_refutational_complete_calculus_axioms Bot_F Inf_F (\<Turnstile>\<inter>)
      no_labels.empty_ord_lifted_calc_w_red_crit_family.Red_Inf_Q"
  show "static_refutational_complete_calculus_axioms Bot_FL Inf_FL (\<Turnstile>\<inter>L) with_labels.Red_Inf_Q"
    unfolding static_refutational_complete_calculus_axioms_def
  proof (intro conjI impI allI)
    fix Bl :: \<open>'f \<times> 'l\<close> and Nl :: \<open>('f \<times> 'l) set\<close>
    assume
      Bl_in: \<open>Bl \<in> Bot_FL\<close> and
      Nl_sat: \<open>with_labels.inter_red_crit_calculus.saturated Nl\<close> and
      Nl_entails_Bl: \<open>Nl \<Turnstile>\<inter>L {Bl}\<close>
    have static_axioms: "B \<in> Bot_F \<longrightarrow>
      no_labels.lifted_calc_w_red_crit_family.inter_red_crit_calculus.saturated N \<longrightarrow>
      N \<Turnstile>\<inter> {B} \<longrightarrow> (\<exists>B'\<in>Bot_F. B' \<in> N)" for B N
      using static[unfolded static_refutational_complete_calculus_axioms_def] by fast
    define B where "B = fst Bl"
    have B_in: "B \<in> Bot_F" using Bl_in Bot_FL_def B_def SigmaE by force
    define N where "N = fst ` Nl"
    have N_sat: "no_labels.lifted_calc_w_red_crit_family.inter_red_crit_calculus.saturated N"
      using N_def Nl_sat labeled_family_saturation_lifting by blast
    have N_entails_B: "N \<Turnstile>\<inter> {B}"
      using Nl_entails_Bl unfolding labeled_entailment_lifting N_def B_def by force
    have "\<exists>B' \<in> Bot_F. B' \<in> N" using B_in N_sat N_entails_B static_axioms[of B N] by blast
    then obtain B' where in_Bot: "B' \<in> Bot_F" and in_N: "B' \<in> N" by force
    then have "B' \<in> fst ` Bot_FL" unfolding Bot_FL_def by fastforce
    obtain Bl' where in_Nl: "Bl' \<in> Nl" and fst_Bl': "fst Bl' = B'"
      using in_N unfolding N_def by blast
    have "Bl' \<in> Bot_FL" unfolding Bot_FL_def using fst_Bl' in_Bot vimage_fst by fastforce
    then show \<open>\<exists>Bl'\<in>Bot_FL. Bl' \<in> Nl\<close> using in_Nl by blast
  qed
qed

end

end
