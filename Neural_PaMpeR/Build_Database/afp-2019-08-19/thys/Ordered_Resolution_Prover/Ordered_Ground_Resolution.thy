(*  Title:       Ground Ordered Resolution Calculus with Selection
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2016, 2017
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2014, 2017
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>Ground Ordered Resolution Calculus with Selection\<close>

theory Ordered_Ground_Resolution
  imports Inference_System Ground_Resolution_Model
begin

text \<open>
Ordered ground resolution with selection is the second inference system studied in Section~3
(``Standard Resolution'') of Bachmair and Ganzinger's chapter.
\<close>


subsection \<open>Inference Rule\<close>

text \<open>
Ordered ground resolution consists of a single rule, called \<open>ord_resolve\<close> below. Like
\<open>unord_resolve\<close>, the rule is sound and counterexample-reducing. In addition, it is reductive.
\<close>

context ground_resolution_with_selection
begin

text \<open>
The following inductive definition corresponds to Figure 2.
\<close>

definition maximal_wrt :: "'a \<Rightarrow> 'a literal multiset \<Rightarrow> bool" where
  "maximal_wrt A DA \<equiv> A = Max (atms_of DA)" (* FIXME: change definition so that it returns true if DA is empty *)

definition strictly_maximal_wrt :: "'a \<Rightarrow> 'a literal multiset \<Rightarrow> bool" where
  "strictly_maximal_wrt A CA \<longleftrightarrow> (\<forall>B \<in> atms_of CA. B < A)"

inductive eligible :: "'a list \<Rightarrow> 'a clause \<Rightarrow> bool" where
  eligible: "(S DA = negs (mset As)) \<or> (S DA = {#} \<and> length As = 1 \<and> maximal_wrt (As ! 0) DA) \<Longrightarrow>
    eligible As DA"

lemma "(S DA = negs (mset As) \<or> S DA = {#} \<and> length As = 1 \<and> maximal_wrt (As ! 0) DA) \<longleftrightarrow>
    eligible As DA"
  using eligible.intros ground_resolution_with_selection.eligible.cases ground_resolution_with_selection_axioms by blast


inductive
  ord_resolve :: "'a clause list \<Rightarrow> 'a clause \<Rightarrow> 'a multiset list \<Rightarrow> 'a list \<Rightarrow> 'a clause \<Rightarrow> bool"
where
  ord_resolve:
    "length CAs = n \<Longrightarrow>
     length Cs = n \<Longrightarrow>
     length AAs = n \<Longrightarrow>
     length As = n \<Longrightarrow>
     n \<noteq> 0 \<Longrightarrow>
     (\<forall>i < n. CAs ! i = Cs ! i + poss (AAs ! i)) \<Longrightarrow>
     (\<forall>i < n. AAs ! i \<noteq> {#}) \<Longrightarrow>
     (\<forall>i < n. \<forall>A \<in># AAs ! i. A = As ! i) \<Longrightarrow>
     eligible As (D + negs (mset As)) \<Longrightarrow>
     (\<forall>i < n. strictly_maximal_wrt (As ! i) (Cs ! i)) \<Longrightarrow>
     (\<forall>i < n. S (CAs ! i) = {#}) \<Longrightarrow>
     ord_resolve CAs (D + negs (mset As)) AAs As (\<Union># (mset Cs) + D)"

lemma ord_resolve_sound:
  assumes
    res_e: "ord_resolve CAs DA AAs As E" and
    cc_true: "I \<Turnstile>m mset CAs" and
    d_true: "I \<Turnstile> DA"
  shows "I \<Turnstile> E"
  using res_e
proof (cases rule: ord_resolve.cases)
  case (ord_resolve n Cs D)
  note DA = this(1) and e = this(2) and cas_len = this(3) and cs_len = this(4) and
    as_len = this(6) and cas = this(8) and aas_ne = this(9) and a_eq = this(10)

  show ?thesis
  proof (cases "\<forall>A \<in> set As. A \<in> I")
    case True
    then have "\<not> I \<Turnstile> negs (mset As)"
      unfolding true_cls_def by fastforce
    then have "I \<Turnstile> D"
      using d_true DA by fast
    then show ?thesis
      unfolding e by blast
  next
    case False
    then obtain i where
      a_in_aa: "i < n" and
      a_false: "As ! i \<notin> I"
      using cas_len as_len by (metis in_set_conv_nth)
    have "\<not> I \<Turnstile> poss (AAs ! i)"
      using a_false a_eq aas_ne a_in_aa unfolding true_cls_def by auto
    moreover have "I \<Turnstile> CAs ! i"
      using a_in_aa cc_true unfolding true_cls_mset_def using cas_len by auto
    ultimately have "I \<Turnstile> Cs ! i"
      using cas a_in_aa by auto
    then show ?thesis
      using a_in_aa cs_len unfolding e true_cls_def
      by (meson in_Union_mset_iff nth_mem_mset union_iff)
  qed
qed

lemma filter_neg_atm_of_S: "{#Neg (atm_of L). L \<in># S C#} = S C"
  by (simp add: S_selects_neg_lits)

text \<open>
This corresponds to Lemma 3.13:
\<close>

lemma ord_resolve_reductive:
  assumes "ord_resolve CAs DA AAs As E"
  shows "E < DA"
  using assms
proof (cases rule: ord_resolve.cases)
  case (ord_resolve n Cs D)
  note DA = this(1) and e = this(2) and cas_len = this(3) and cs_len = this(4) and
    ai_len = this(6) and nz = this(7) and cas = this(8) and maxim = this(12)

  show ?thesis
  proof (cases "\<Union># (mset Cs) = {#}")
    case True
    have "negs (mset As) \<noteq> {#}"
       using nz ai_len by auto
    then show ?thesis
       unfolding True e DA by auto
  next
    case False

    define max_A_of_Cs where "max_A_of_Cs = Max (atms_of (\<Union># (mset Cs)))"

    have
      mc_in: "max_A_of_Cs \<in> atms_of (\<Union># (mset Cs))" and
      mc_max: "\<And>B. B \<in> atms_of (\<Union># (mset Cs)) \<Longrightarrow> B \<le> max_A_of_Cs"
      using max_A_of_Cs_def False by auto

    then have "\<exists>C_max \<in> set Cs. max_A_of_Cs \<in> atms_of (C_max)"
      by (metis atm_imp_pos_or_neg_lit in_Union_mset_iff neg_lit_in_atms_of pos_lit_in_atms_of
          set_mset_mset)
    then obtain max_i where
      cm_in_cas: "max_i < length CAs" and
      mc_in_cm: "max_A_of_Cs \<in> atms_of (Cs ! max_i)"
      using in_set_conv_nth[of _ CAs] by (metis cas_len cs_len in_set_conv_nth)

    define CA_max where "CA_max = CAs ! max_i"
    define A_max where "A_max = As ! max_i"
    define C_max where "C_max = Cs ! max_i"

    have mc_lt_ma: "max_A_of_Cs < A_max"
      using maxim cm_in_cas mc_in_cm cas_len unfolding strictly_maximal_wrt_def A_max_def by auto

    then have ucas_ne_neg_aa: "\<Union># (mset Cs) \<noteq> negs (mset As)"
      using mc_in mc_max mc_lt_ma cm_in_cas cas_len ai_len unfolding A_max_def
      by (metis atms_of_negs nth_mem set_mset_mset leD)
    moreover have ucas_lt_ma: "\<forall>B \<in> atms_of (\<Union># (mset Cs)). B < A_max"
      using mc_max mc_lt_ma by fastforce
    moreover have "\<not> Neg A_max \<in># \<Union># (mset Cs)"
      using ucas_lt_ma neg_lit_in_atms_of[of A_max "\<Union># (mset Cs)"] by auto
    moreover have "Neg A_max \<in># negs (mset As)"
      using cm_in_cas cas_len ai_len A_max_def by auto
    ultimately have "\<Union># (mset Cs) < negs (mset As)"
      unfolding less_multiset\<^sub>H\<^sub>O
      by (metis (no_types) atms_less_eq_imp_lit_less_eq_neg count_greater_zero_iff
          count_inI le_imp_less_or_eq less_imp_not_less not_le)
    then show ?thesis
      unfolding e DA by auto
  qed
qed

text \<open>
This corresponds to Theorem 3.15:
\<close>

theorem ord_resolve_counterex_reducing:
  assumes
    ec_ni_n: "{#} \<notin> N" and
    d_in_n: "DA \<in> N" and
    d_cex: "\<not> INTERP N \<Turnstile> DA" and
    d_min: "\<And>C. C \<in> N \<Longrightarrow> \<not> INTERP N \<Turnstile> C \<Longrightarrow> DA \<le> C"
  obtains CAs AAs As E where
    "set CAs \<subseteq> N"
    "INTERP N \<Turnstile>m mset CAs"
    "\<And>CA. CA \<in> set CAs \<Longrightarrow> productive N CA"
    "ord_resolve CAs DA AAs As E"
    "\<not> INTERP N \<Turnstile> E"
    "E < DA"
proof -
  have d_ne: "DA \<noteq> {#}"
    using d_in_n ec_ni_n by blast
  have "\<exists>As. As \<noteq> [] \<and> negs (mset As) \<le># DA \<and> eligible As DA"
  proof (cases "S DA = {#}")
    assume s_d_e: "S DA = {#}"

    define A where "A = Max (atms_of DA)"
    define As where "As = [A]"
    define D where "D = DA-{#Neg A #}"

    have na_in_d: "Neg A \<in># DA"
      unfolding A_def using s_d_e d_ne d_in_n d_cex d_min
      by (metis Max_in_lits Max_lit_eq_pos_or_neg_Max_atm max_pos_imp_Interp Interp_imp_INTERP)
    then have das: "DA = D + negs (mset As)" unfolding D_def As_def by auto
    moreover from na_in_d have "negs (mset As) \<subseteq># DA"
      by (simp add: As_def)
    moreover have "As ! 0 = Max (atms_of (D + negs (mset As)))"
      using A_def As_def das by auto
    then have "eligible As DA"
      using eligible s_d_e As_def das maximal_wrt_def by auto
    ultimately show ?thesis
      using As_def by blast
  next
    assume s_d_e: "S DA \<noteq> {#}"

    define As :: "'a list" where
      "As = list_of_mset {#atm_of L. L \<in># S DA#}"
    define D :: "'a clause" where
      "D = DA - negs {#atm_of L. L \<in># S DA#}"

    have "As \<noteq> []" unfolding As_def using s_d_e
      by (metis image_mset_is_empty_iff list_of_mset_empty)
    moreover have da_sub_as: "negs {#atm_of L. L \<in># S DA#} \<subseteq># DA"
      using S_selects_subseteq by (auto simp: filter_neg_atm_of_S)
    then have "negs (mset As) \<subseteq># DA"
      unfolding As_def by auto
    moreover have das: "DA = D + negs (mset As)"
      using da_sub_as unfolding D_def As_def by auto
    moreover have "S DA = negs {#atm_of L. L \<in># S DA#}"
      by (auto simp: filter_neg_atm_of_S)
    then have "S DA = negs (mset As)"
      unfolding As_def by auto
    then have "eligible As DA"
      unfolding das using eligible by auto
    ultimately show ?thesis
      by blast
  qed
  then obtain As :: "'a list" where
    as_ne: "As \<noteq> []" and
    negs_as_le_d: "negs (mset As) \<le># DA" and
    s_d: "eligible As DA"
    by blast

  define D :: "'a clause" where
    "D = DA - negs (mset As)"

  have "set As \<subseteq> INTERP N"
    using d_cex negs_as_le_d by force
  then have prod_ex: "\<forall>A \<in> set As. \<exists>D. produces N D A"
    unfolding INTERP_def
    by (metis (no_types, lifting) INTERP_def subsetCE UN_E not_produces_imp_notin_production)
  then have "\<And>A. \<exists>D. produces N D A \<longrightarrow> A \<in> set As"
    using ec_ni_n by (auto intro: productive_in_N)
  then have "\<And>A. \<exists>D. produces N D A \<longleftrightarrow> A \<in> set As"
    using prod_ex by blast
  then obtain CA_of where c_of0: "\<And>A. produces N (CA_of A) A \<longleftrightarrow> A \<in> set As"
    by metis
  then have prod_c0: "\<forall>A \<in> set As. produces N (CA_of A) A"
    by blast

  define C_of where
    "\<And>A. C_of A = {#L \<in># CA_of A. L \<noteq> Pos A#}"
  define Aj_of where
    "\<And>A. Aj_of A = image_mset atm_of {#L \<in># CA_of A. L = Pos A#}"

  have pospos: "\<And>LL A. {#Pos (atm_of x). x \<in># {#L \<in># LL. L = Pos A#}#} = {#L \<in># LL. L = Pos A#}"
    by (metis (mono_tags, lifting) image_filter_cong literal.sel(1) multiset.map_ident)
  have ca_of_c_of_aj_of: "\<And>A. CA_of A = C_of A + poss (Aj_of A)"
    using pospos[of _ "CA_of _"] by (simp add: C_of_def Aj_of_def)

  define n :: nat where
    "n = length As"
  define Cs :: "'a clause list" where
    "Cs = map C_of As"
  define AAs :: "'a multiset list" where
    "AAs = map Aj_of As"
  define CAs :: "'a literal multiset list" where
    "CAs = map CA_of As"

  have m_nz: "\<And>A. A \<in> set As \<Longrightarrow> Aj_of A \<noteq> {#}"
    unfolding Aj_of_def using prod_c0 produces_imp_Pos_in_lits
    by (metis (full_types) filter_mset_empty_conv image_mset_is_empty_iff)

  have prod_c: "productive N CA" if ca_in: "CA \<in> set CAs" for CA
  proof -
    obtain i where i_p: "i < length CAs" "CAs ! i = CA"
      using ca_in by (meson in_set_conv_nth)
    have "production N (CA_of (As ! i)) = {As ! i}"
      using i_p CAs_def prod_c0 by auto
    then show "productive N CA"
      using i_p CAs_def by auto
  qed
  then have cs_subs_n: "set CAs \<subseteq> N"
    using productive_in_N by auto
  have cs_true: "INTERP N \<Turnstile>m mset CAs"
    unfolding true_cls_mset_def using prod_c productive_imp_INTERP by auto

  have "\<And>A. A \<in> set As \<Longrightarrow> \<not> Neg A \<in># CA_of A"
    using prod_c0 produces_imp_neg_notin_lits by auto
  then have a_ni_c': "\<And>A. A \<in> set As \<Longrightarrow> A \<notin> atms_of (C_of A)"
    unfolding C_of_def using atm_imp_pos_or_neg_lit by force
  have c'_le_c: "\<And>A. C_of A \<le> CA_of A"
    unfolding C_of_def by (auto intro: subset_eq_imp_le_multiset)
  have a_max_c: "\<And>A. A \<in> set As \<Longrightarrow> A = Max (atms_of (CA_of A))"
    using prod_c0 productive_imp_produces_Max_atom[of N] by auto
  then have "\<And>A. A \<in> set As \<Longrightarrow> C_of A \<noteq> {#} \<Longrightarrow> Max (atms_of (C_of A)) \<le> A"
    using c'_le_c by (metis less_eq_Max_atms_of)
  moreover have "\<And>A. A \<in> set As \<Longrightarrow> C_of A \<noteq> {#} \<Longrightarrow> Max (atms_of (C_of A)) \<noteq> A"
    using a_ni_c' Max_in by (metis (no_types) atms_empty_iff_empty finite_atms_of)
  ultimately have max_c'_lt_a: "\<And>A. A \<in> set As \<Longrightarrow> C_of A \<noteq> {#} \<Longrightarrow> Max (atms_of (C_of A)) < A"
    by (metis order.strict_iff_order)

  have le_cs_as: "length CAs = length As"
    unfolding CAs_def by simp

  have "length CAs = n"
    by (simp add: le_cs_as n_def)
  moreover have "length Cs = n"
    by (simp add: Cs_def n_def)
  moreover have "length AAs = n"
    by (simp add: AAs_def n_def)
  moreover have "length As = n"
    using n_def by auto
  moreover have "n \<noteq> 0"
    by (simp add: as_ne n_def)
  moreover have " \<forall>i. i < length AAs \<longrightarrow> (\<forall>A \<in># AAs ! i. A = As ! i)"
    using AAs_def Aj_of_def by auto

  have "\<And>x B. production N (CA_of x) = {x} \<Longrightarrow> B \<in># CA_of x \<Longrightarrow> B \<noteq> Pos x \<Longrightarrow> atm_of B < x"
    by (metis atm_of_lit_in_atms_of insert_not_empty le_imp_less_or_eq Pos_atm_of_iff
        Neg_atm_of_iff pos_neg_in_imp_true produces_imp_Pos_in_lits produces_imp_atms_leq
        productive_imp_not_interp)
  then have "\<And>B A. A\<in>set As \<Longrightarrow> B \<in># CA_of A \<Longrightarrow> B \<noteq> Pos A \<Longrightarrow> atm_of B < A"
    using prod_c0 by auto
  have "\<forall>i. i < length AAs \<longrightarrow> AAs ! i \<noteq> {#}"
    unfolding AAs_def using m_nz by simp
  have "\<forall>i < n. CAs ! i = Cs ! i + poss (AAs ! i)"
    unfolding CAs_def Cs_def AAs_def using ca_of_c_of_aj_of by (simp add: n_def)

  moreover have "\<forall>i < n. AAs ! i \<noteq> {#}"
    using \<open>\<forall>i < length AAs. AAs ! i \<noteq> {#}\<close> calculation(3) by blast
  moreover have "\<forall>i < n. \<forall>A \<in># AAs ! i. A = As ! i"
    by (simp add: \<open>\<forall>i < length AAs. \<forall>A \<in># AAs ! i. A = As ! i\<close> calculation(3))
  moreover have "eligible As DA"
    using s_d by auto
  then have "eligible As (D + negs (mset As))"
    using D_def negs_as_le_d by auto
  moreover have "\<And>i. i < length AAs \<Longrightarrow> strictly_maximal_wrt (As ! i) ((Cs ! i))"
    by (simp add: C_of_def Cs_def \<open>\<And>x B. \<lbrakk>production N (CA_of x) = {x}; B \<in># CA_of x; B \<noteq> Pos x\<rbrakk> \<Longrightarrow> atm_of B < x\<close> atms_of_def calculation(3) n_def prod_c0 strictly_maximal_wrt_def)

  have "\<forall>i < n. strictly_maximal_wrt (As ! i) (Cs ! i)"
    by (simp add: \<open>\<And>i. i < length AAs \<Longrightarrow> strictly_maximal_wrt (As ! i) (Cs ! i)\<close> calculation(3))
  moreover have "\<forall>CA \<in> set CAs. S CA = {#}"
    using prod_c producesD productive_imp_produces_Max_literal by blast
  have "\<forall>CA\<in>set CAs. S CA = {#}"
    using \<open>\<forall>CA\<in>set CAs. S CA = {#}\<close> by simp
  then have "\<forall>i < n. S (CAs ! i) = {#}"
    using \<open>length CAs = n\<close> nth_mem by blast
  ultimately have res_e: "ord_resolve CAs (D + negs (mset As)) AAs As (\<Union># (mset Cs) + D)"
    using ord_resolve by auto

  have "\<And>A. A \<in> set As \<Longrightarrow> \<not> interp N (CA_of A) \<Turnstile> CA_of A"
    by (simp add: prod_c0 producesD)
  then have "\<And>A. A \<in> set As \<Longrightarrow> \<not> Interp N (CA_of A) \<Turnstile> C_of A"
    unfolding prod_c0 C_of_def Interp_def true_cls_def using true_lit_def not_gr_zero prod_c0
    by auto
  then have c'_at_n: "\<And>A. A \<in> set As \<Longrightarrow> \<not> INTERP N \<Turnstile> C_of A"
    using a_max_c c'_le_c max_c'_lt_a not_Interp_imp_not_INTERP unfolding true_cls_def
    by (metis true_cls_def true_cls_empty)

  have "\<not> INTERP N \<Turnstile> \<Union># (mset Cs)"
    unfolding Cs_def true_cls_def using c'_at_n by fastforce
  moreover have "\<not> INTERP N \<Turnstile> D"
    using d_cex by (metis D_def add_diff_cancel_right' negs_as_le_d subset_mset.add_diff_assoc2
        true_cls_def union_iff)
  ultimately have e_cex: "\<not> INTERP N \<Turnstile> \<Union># (mset Cs) + D"
    by simp

  have "set CAs \<subseteq> N"
    by (simp add: cs_subs_n)
  moreover have "INTERP N \<Turnstile>m mset CAs"
    by (simp add: cs_true)
  moreover have "\<And>CA. CA \<in> set CAs \<Longrightarrow> productive N CA"
    by (simp add: prod_c)
  moreover have "ord_resolve CAs DA AAs As (\<Union># (mset Cs) + D)"
    using D_def negs_as_le_d res_e by auto
  moreover have "\<not> INTERP N \<Turnstile> \<Union># (mset Cs) + D"
    using e_cex by simp
  moreover have "\<Union># (mset Cs) + D < DA"
    using calculation(4) ord_resolve_reductive by auto
  ultimately show thesis
    ..
qed

lemma ord_resolve_atms_of_concl_subset:
  assumes "ord_resolve CAs DA AAs As E"
  shows "atms_of E \<subseteq> (\<Union>C \<in> set CAs. atms_of C) \<union> atms_of DA"
  using assms
proof (cases rule: ord_resolve.cases)
  case (ord_resolve n Cs D)
  note DA = this(1) and e = this(2) and cas_len = this(3) and cs_len = this(4) and cas = this(8)

  have "\<forall>i < n. set_mset (Cs ! i) \<subseteq> set_mset (CAs ! i)"
    using cas by auto
  then have "\<forall>i < n. Cs ! i \<subseteq># \<Union># (mset CAs)"
    by (metis cas cas_len mset_subset_eq_add_left nth_mem_mset sum_mset.remove union_assoc)
  then have "\<forall>C \<in> set Cs. C \<subseteq># \<Union># (mset CAs)"
    using cs_len in_set_conv_nth[of _ Cs] by auto
  then have "set_mset (\<Union># (mset Cs)) \<subseteq> set_mset (\<Union># (mset CAs))"
    by auto (meson in_mset_sum_list2 mset_subset_eqD)
  then have "atms_of (\<Union># (mset Cs)) \<subseteq> atms_of (\<Union># (mset CAs))"
    by (meson lits_subseteq_imp_atms_subseteq mset_subset_eqD subsetI)
  moreover have "atms_of (\<Union># (mset CAs)) = (\<Union>CA \<in> set CAs. atms_of CA)"
    by (intro set_eqI iffI, simp_all,
      metis in_mset_sum_list2 atm_imp_pos_or_neg_lit neg_lit_in_atms_of pos_lit_in_atms_of,
      metis in_mset_sum_list atm_imp_pos_or_neg_lit neg_lit_in_atms_of pos_lit_in_atms_of)
  ultimately have "atms_of (\<Union># (mset Cs)) \<subseteq> (\<Union>CA \<in> set CAs. atms_of CA)"
    by auto
  moreover have "atms_of D \<subseteq> atms_of DA"
    using DA by auto
  ultimately show ?thesis
    unfolding e by auto
qed


subsection \<open>Inference System\<close>

text \<open>
Theorem 3.16 is subsumed in the counterexample-reducing inference system framework, which is
instantiated below. Unlike its unordered cousin, ordered resolution is additionally a reductive
inference system.
\<close>

definition ord_\<Gamma> :: "'a inference set" where
  "ord_\<Gamma> = {Infer (mset CAs) DA E | CAs DA AAs As E. ord_resolve CAs DA AAs As E}"

sublocale ord_\<Gamma>_sound_counterex_reducing?:
  sound_counterex_reducing_inference_system "ground_resolution_with_selection.ord_\<Gamma> S"
    "ground_resolution_with_selection.INTERP S" +
  reductive_inference_system "ground_resolution_with_selection.ord_\<Gamma> S"
proof unfold_locales
  fix DA :: "'a clause" and N :: "'a clause set"
  assume "{#} \<notin> N" and "DA \<in> N" and "\<not> INTERP N \<Turnstile> DA" and "\<And>C. C \<in> N \<Longrightarrow> \<not> INTERP N \<Turnstile> C \<Longrightarrow> DA \<le> C"
  then obtain CAs AAs As E where
    dd_sset_n: "set CAs \<subseteq> N" and
    dd_true: "INTERP N \<Turnstile>m mset CAs" and
    res_e: "ord_resolve CAs DA AAs As E" and
    e_cex: "\<not> INTERP N \<Turnstile> E" and
    e_lt_c: "E < DA"
    using ord_resolve_counterex_reducing[of N DA thesis] by auto

  have "Infer (mset CAs) DA E \<in> ord_\<Gamma>"
    using res_e unfolding ord_\<Gamma>_def by (metis (mono_tags, lifting) mem_Collect_eq)
  then show "\<exists>CC E. set_mset CC \<subseteq> N \<and> INTERP N \<Turnstile>m CC \<and> Infer CC DA E \<in> ord_\<Gamma>
    \<and> \<not> INTERP N \<Turnstile> E \<and> E < DA"
    using dd_sset_n dd_true e_cex e_lt_c by (metis set_mset_mset)
qed (auto simp: ord_\<Gamma>_def intro: ord_resolve_sound ord_resolve_reductive)

lemmas clausal_logic_compact = ord_\<Gamma>_sound_counterex_reducing.clausal_logic_compact

end

text \<open>
A second proof of Theorem 3.12, compactness of clausal logic:
\<close>

lemmas clausal_logic_compact = ground_resolution_with_selection.clausal_logic_compact

end
