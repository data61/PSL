(*  Title:       First-Order Ordered Resolution Calculus with Selection
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2016, 2017
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2014, 2017
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>First-Order Ordered Resolution Calculus with Selection\<close>

theory FO_Ordered_Resolution
  imports Abstract_Substitution Ordered_Ground_Resolution Standard_Redundancy
begin

text \<open>
This material is based on Section 4.3 (``A Simple Resolution Prover for First-Order Clauses'') of
Bachmair and Ganzinger's chapter. Specifically, it formalizes the ordered resolution calculus for
first-order standard clauses presented in Figure 4 and its related lemmas and theorems, including
soundness and Lemma 4.12 (the lifting lemma).

The following corresponds to pages 41--42 of Section 4.3, until Figure 5 and its explanation.
\<close>

locale FO_resolution = mgu subst_atm id_subst comp_subst atm_of_atms renamings_apart mgu
  for
    subst_atm :: "'a :: wellorder \<Rightarrow> 's \<Rightarrow> 'a" and
    id_subst :: "'s" and
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's" and
    renamings_apart :: "'a literal multiset list \<Rightarrow> 's list" and
    atm_of_atms :: "'a list \<Rightarrow> 'a" and
    mgu :: "'a set set \<Rightarrow> 's option" +
  fixes
    less_atm :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes
    less_atm_stable: "less_atm A B \<Longrightarrow> less_atm (A \<cdot>a \<sigma>) (B \<cdot>a \<sigma>)"
begin


subsection \<open>Library\<close>

lemma Bex_cartesian_product: "(\<exists>xy \<in> A \<times> B. P xy) \<equiv> (\<exists>x \<in> A. \<exists>y \<in> B. P (x, y))"
  by simp

(* FIXME: Move to "Multiset.thy" *)
lemma length_sorted_list_of_multiset[simp]: "length (sorted_list_of_multiset A) = size A"
  by (metis mset_sorted_list_of_multiset size_mset)

(* FIXME: move? or avoid? *)
lemma eql_map_neg_lit_eql_atm:
  assumes "map (\<lambda>L. L \<cdot>l \<eta>) (map Neg As') = map Neg As"
  shows "As' \<cdot>al \<eta> = As"
  using assms by (induction As' arbitrary: As) auto

lemma instance_list:
  assumes "negs (mset As) = SDA' \<cdot> \<eta>"
  shows "\<exists>As'. negs (mset As') = SDA' \<and> As' \<cdot>al \<eta> = As"
proof -
  from assms have negL: "\<forall>L \<in># SDA'. is_neg L"
    using Melem_subst_cls subst_lit_in_negs_is_neg by metis

  from assms have "{#L \<cdot>l \<eta>. L \<in># SDA'#} = mset (map Neg As)"
    using subst_cls_def by auto
  then have "\<exists>NAs'. map (\<lambda>L. L \<cdot>l \<eta>) NAs' = map Neg As \<and> mset NAs' = SDA'"
    using image_mset_of_subset_list[of "\<lambda>L. L \<cdot>l \<eta>" SDA' "map Neg As"] by auto
  then obtain As' where As'_p:
    "map (\<lambda>L. L \<cdot>l \<eta>) (map Neg As') = map Neg As \<and> mset (map Neg As') = SDA'"
    by (metis (no_types, lifting) Neg_atm_of_iff negL ex_map_conv set_mset_mset)

  have "negs (mset As') = SDA'"
    using As'_p by auto
  moreover have "map (\<lambda>L. L \<cdot>l \<eta>) (map Neg As') = map Neg As"
    using As'_p by auto
  then have "As' \<cdot>al \<eta> = As"
    using eql_map_neg_lit_eql_atm by auto
  ultimately show ?thesis
    by blast
qed


context
  fixes S :: "'a clause \<Rightarrow> 'a clause"
begin


subsection \<open>Calculus\<close>

text \<open>
The following corresponds to Figure 4.
\<close>

definition maximal_wrt :: "'a \<Rightarrow> 'a literal multiset \<Rightarrow> bool" where
  "maximal_wrt A C \<longleftrightarrow> (\<forall>B \<in> atms_of C. \<not> less_atm A B)"

definition strictly_maximal_wrt :: "'a \<Rightarrow> 'a literal multiset \<Rightarrow> bool" where
  "strictly_maximal_wrt A C \<equiv> \<forall>B \<in> atms_of C. A \<noteq> B \<and> \<not> less_atm A B"

lemma strictly_maximal_wrt_maximal_wrt: "strictly_maximal_wrt A C \<Longrightarrow> maximal_wrt A C"
  unfolding maximal_wrt_def strictly_maximal_wrt_def by auto

(* FIXME: use hd instead of ! 0 *)
inductive eligible :: "'s \<Rightarrow> 'a list \<Rightarrow> 'a clause \<Rightarrow> bool" where
  eligible:
    "S DA = negs (mset As) \<or> S DA = {#} \<and> length As = 1 \<and> maximal_wrt (As ! 0 \<cdot>a \<sigma>) (DA \<cdot> \<sigma>) \<Longrightarrow>
     eligible \<sigma> As DA"

inductive
  ord_resolve
  :: "'a clause list \<Rightarrow> 'a clause \<Rightarrow> 'a multiset list \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> 'a clause \<Rightarrow> bool"
where
  ord_resolve:
    "length CAs = n \<Longrightarrow>
     length Cs = n \<Longrightarrow>
     length AAs = n \<Longrightarrow>
     length As = n \<Longrightarrow>
     n \<noteq> 0 \<Longrightarrow>
     (\<forall>i < n. CAs ! i = Cs ! i + poss (AAs ! i)) \<Longrightarrow>
     (\<forall>i < n. AAs ! i \<noteq> {#}) \<Longrightarrow>
     Some \<sigma> = mgu (set_mset ` set (map2 add_mset As AAs)) \<Longrightarrow>
     eligible \<sigma> As (D + negs (mset As)) \<Longrightarrow>
     (\<forall>i < n. strictly_maximal_wrt (As ! i \<cdot>a \<sigma>) (Cs ! i \<cdot> \<sigma>)) \<Longrightarrow>
     (\<forall>i < n. S (CAs ! i) = {#}) \<Longrightarrow>
     ord_resolve CAs (D + negs (mset As)) AAs As \<sigma> ((\<Union># (mset Cs) + D) \<cdot> \<sigma>)"

inductive
  ord_resolve_rename
  :: "'a clause list \<Rightarrow> 'a clause \<Rightarrow> 'a multiset list \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> 'a clause \<Rightarrow> bool"
where
  ord_resolve_rename:
    "length CAs = n \<Longrightarrow>
     length AAs = n \<Longrightarrow>
     length As = n \<Longrightarrow>
     (\<forall>i < n. poss (AAs ! i) \<subseteq># CAs ! i) \<Longrightarrow>
     negs (mset As) \<subseteq># DA \<Longrightarrow>
     \<rho> = hd (renamings_apart (DA # CAs)) \<Longrightarrow>
     \<rho>s = tl (renamings_apart (DA # CAs)) \<Longrightarrow>
     ord_resolve (CAs \<cdot>\<cdot>cl \<rho>s) (DA \<cdot> \<rho>) (AAs \<cdot>\<cdot>aml \<rho>s) (As \<cdot>al \<rho>) \<sigma> E \<Longrightarrow>
     ord_resolve_rename CAs DA AAs As \<sigma> E"

lemma ord_resolve_empty_main_prem: "\<not> ord_resolve Cs {#} AAs As \<sigma> E"
  by (simp add: ord_resolve.simps)

lemma ord_resolve_rename_empty_main_prem: "\<not> ord_resolve_rename Cs {#} AAs As \<sigma> E"
  by (simp add: ord_resolve_empty_main_prem ord_resolve_rename.simps)


subsection \<open>Soundness\<close>

text \<open>
Soundness is not discussed in the chapter, but it is an important property.
\<close>

lemma ord_resolve_ground_inst_sound:
  assumes
    res_e: "ord_resolve CAs DA AAs As \<sigma> E" and
    cc_inst_true: "I \<Turnstile>m mset CAs \<cdot>cm \<sigma> \<cdot>cm \<eta>" and
    d_inst_true: "I \<Turnstile> DA \<cdot> \<sigma> \<cdot> \<eta>" and
    ground_subst_\<eta>: "is_ground_subst \<eta>"
  shows "I \<Turnstile> E \<cdot> \<eta>"
  using res_e
proof (cases rule: ord_resolve.cases)
  case (ord_resolve n Cs D)
  note da = this(1) and e = this(2) and cas_len = this(3) and cs_len = this(4) and
    aas_len = this(5) and as_len = this(6) and cas = this(8) and mgu = this(10) and
    len = this(1)

  have len: "length CAs = length As"
    using as_len cas_len by auto
  have "is_ground_subst (\<sigma> \<odot> \<eta>)"
    using ground_subst_\<eta> by (rule is_ground_comp_subst)
  then have cc_true: "I \<Turnstile>m mset CAs \<cdot>cm \<sigma> \<cdot>cm \<eta>" and d_true: "I \<Turnstile> DA \<cdot> \<sigma> \<cdot> \<eta>"
    using cc_inst_true d_inst_true by auto

  from mgu have unif: "\<forall>i < n. \<forall>A\<in>#AAs ! i. A \<cdot>a \<sigma> = As ! i \<cdot>a \<sigma>"
    using mgu_unifier as_len aas_len by blast

  show "I \<Turnstile> E \<cdot> \<eta>"
  proof (cases "\<forall>A \<in> set As. A \<cdot>a \<sigma> \<cdot>a \<eta> \<in> I")
    case True
    then have "\<not> I \<Turnstile> negs (mset As) \<cdot> \<sigma> \<cdot> \<eta>"
      unfolding true_cls_def[of I] by auto
    then have "I \<Turnstile> D \<cdot> \<sigma> \<cdot> \<eta>"
      using d_true da by auto
    then show ?thesis
      unfolding e by auto
  next
    case False
    then obtain i where a_in_aa: "i < length CAs" and a_false: "(As ! i) \<cdot>a \<sigma> \<cdot>a \<eta> \<notin> I"
      using da len by (metis in_set_conv_nth)
    define C where "C \<equiv> Cs ! i"
    define BB where "BB \<equiv> AAs ! i"
    have c_cf': "C \<subseteq># \<Union># (mset CAs)"
      unfolding C_def using a_in_aa cas cas_len
      by (metis less_subset_eq_Union_mset mset_subset_eq_add_left subset_mset.order.trans)
    have c_in_cc: "C + poss BB \<in># mset CAs"
      using C_def BB_def a_in_aa cas_len in_set_conv_nth cas by fastforce
    {
      fix B
      assume "B \<in># BB"
      then have "B \<cdot>a \<sigma> = (As ! i) \<cdot>a \<sigma>"
        using unif a_in_aa cas_len unfolding BB_def by auto
    }
    then have "\<not> I \<Turnstile> poss BB \<cdot> \<sigma> \<cdot> \<eta>"
      using a_false by (auto simp: true_cls_def)
    moreover have "I \<Turnstile> (C + poss BB) \<cdot> \<sigma> \<cdot> \<eta>"
      using c_in_cc cc_true true_cls_mset_true_cls[of I "mset CAs \<cdot>cm \<sigma> \<cdot>cm \<eta>"] by force
    ultimately have "I \<Turnstile> C \<cdot> \<sigma> \<cdot> \<eta>"
      by simp
    then show ?thesis
      unfolding e subst_cls_union using c_cf' C_def a_in_aa cas_len cs_len
      by (metis (no_types, lifting) mset_subset_eq_add_left nth_mem_mset set_mset_mono sum_mset.remove true_cls_mono subst_cls_mono)
  qed
qed

text \<open>
The previous lemma is not only used to prove soundness, but also the following lemma which is 
used to prove Lemma 4.10.
\<close>

lemma ord_resolve_rename_ground_inst_sound:
  assumes
    "ord_resolve_rename CAs DA AAs As \<sigma> E" and
    "\<rho>s = tl (renamings_apart (DA # CAs))" and
    "\<rho> = hd (renamings_apart (DA # CAs))" and
    "I \<Turnstile>m (mset (CAs \<cdot>\<cdot>cl \<rho>s)) \<cdot>cm \<sigma> \<cdot>cm \<eta>" and
    "I \<Turnstile> DA \<cdot> \<rho> \<cdot> \<sigma> \<cdot> \<eta>" and
    "is_ground_subst \<eta>"
  shows "I \<Turnstile> E \<cdot> \<eta>"
  using assms by (cases rule: ord_resolve_rename.cases) (fast intro: ord_resolve_ground_inst_sound)

text \<open>
Here follows the soundness theorem for the resolution rule.
\<close>

theorem ord_resolve_sound:
 assumes
   res_e: "ord_resolve CAs DA AAs As \<sigma> E" and
   cc_d_true: "\<And>\<sigma>. is_ground_subst \<sigma> \<Longrightarrow> I \<Turnstile>m (mset CAs + {#DA#}) \<cdot>cm \<sigma>" and
   ground_subst_\<eta>: "is_ground_subst \<eta>"
 shows "I \<Turnstile> E \<cdot> \<eta>"
proof (use res_e in \<open>cases rule: ord_resolve.cases\<close>)
  case (ord_resolve n Cs D)
  note da = this(1) and e = this(2) and cas_len = this(3) and cs_len = this(4)
    and aas_len = this(5) and as_len = this(6) and cas = this(8) and mgu = this(10)
  have ground_subst_\<sigma>_\<eta>: "is_ground_subst (\<sigma> \<odot> \<eta>)"
    using ground_subst_\<eta> by (rule is_ground_comp_subst)
  have cas_true: "I \<Turnstile>m mset CAs \<cdot>cm \<sigma> \<cdot>cm \<eta>"
    using cc_d_true ground_subst_\<sigma>_\<eta> by fastforce
  have da_true: "I \<Turnstile> DA \<cdot> \<sigma> \<cdot> \<eta>"
    using cc_d_true ground_subst_\<sigma>_\<eta> by fastforce
  show "I \<Turnstile> E \<cdot> \<eta>"
    using ord_resolve_ground_inst_sound[OF res_e cas_true da_true] ground_subst_\<eta> by auto
qed

lemma subst_sound:
  assumes 
    "\<And>\<sigma>. is_ground_subst \<sigma> \<Longrightarrow> I \<Turnstile> (C \<cdot> \<sigma>)" and
    "is_ground_subst \<eta>"
  shows "I \<Turnstile> (C \<cdot> \<rho>) \<cdot> \<eta>"
  using assms is_ground_comp_subst subst_cls_comp_subst by metis 

lemma subst_sound_scl:
  assumes
    len: "length P = length CAs" and
    true_cas: "\<And>\<sigma>. is_ground_subst \<sigma> \<Longrightarrow> I \<Turnstile>m (mset CAs) \<cdot>cm \<sigma>" and
    ground_subst_\<eta>: "is_ground_subst \<eta>" 
  shows "I \<Turnstile>m mset (CAs \<cdot>\<cdot>cl P) \<cdot>cm \<eta>"
proof -
  from true_cas have "\<And>CA. CA\<in># mset CAs \<Longrightarrow> (\<And>\<sigma>. is_ground_subst \<sigma> \<Longrightarrow> I \<Turnstile> CA \<cdot> \<sigma>)"
    unfolding true_cls_mset_def by force
  then have "\<forall>i < length CAs. \<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> (I \<Turnstile> CAs ! i \<cdot> \<sigma>)"
    using in_set_conv_nth by auto
  then have true_cp: "\<forall>i < length CAs. \<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I \<Turnstile> CAs ! i \<cdot> P ! i \<cdot> \<sigma>"
    using subst_sound len by auto

  {
    fix CA
    assume "CA \<in># mset (CAs \<cdot>\<cdot>cl P)"
    then obtain i where
      i_x: "i < length (CAs \<cdot>\<cdot>cl P)" "CA = (CAs \<cdot>\<cdot>cl P) ! i"
      by (metis in_mset_conv_nth)
    then have "\<forall>\<sigma>. is_ground_subst \<sigma> \<longrightarrow> I \<Turnstile> CA \<cdot> \<sigma>"
      using true_cp unfolding subst_cls_lists_def by (simp add: len)
  }
  then show ?thesis
    using assms unfolding true_cls_mset_def by auto
qed

text \<open>
Here follows the soundness theorem for the resolution rule with renaming.
\<close>

lemma ord_resolve_rename_sound:
  assumes
    res_e: "ord_resolve_rename CAs DA AAs As \<sigma> E" and
    cc_d_true: "\<And>\<sigma>. is_ground_subst \<sigma> \<Longrightarrow> I \<Turnstile>m ((mset CAs) + {#DA#}) \<cdot>cm \<sigma>" and
    ground_subst_\<eta>: "is_ground_subst \<eta>"
  shows "I \<Turnstile> E \<cdot> \<eta>"
  using res_e
proof (cases rule: ord_resolve_rename.cases)
  case (ord_resolve_rename n \<rho> \<rho>s)
  note \<rho>s = this(7) and res = this(8)
  have len: "length \<rho>s = length CAs"
    using \<rho>s renamings_apart_length by auto
  have "\<And>\<sigma>. is_ground_subst \<sigma> \<Longrightarrow> I \<Turnstile>m (mset (CAs \<cdot>\<cdot>cl \<rho>s) + {#DA \<cdot> \<rho>#}) \<cdot>cm \<sigma>"
    using subst_sound_scl[OF len, of I] subst_sound cc_d_true by auto
  then show "I \<Turnstile> E \<cdot> \<eta>"
    using ground_subst_\<eta> ord_resolve_sound[OF res] by simp
qed


subsection \<open>Other Basic Properties\<close>

lemma ord_resolve_unique:
  assumes
    "ord_resolve CAs DA AAs As \<sigma> E" and
    "ord_resolve CAs DA AAs As \<sigma>' E'"
  shows "\<sigma> = \<sigma>' \<and> E = E'"
  using assms
proof (cases rule: ord_resolve.cases[case_product ord_resolve.cases], intro conjI)
  case (ord_resolve_ord_resolve CAs n Cs AAs As \<sigma>'' DA CAs' n' Cs' AAs' As' \<sigma>''' DA')
  note res = this(1-17) and res' = this(18-34)

  show \<sigma>: "\<sigma> = \<sigma>'"
    using res(3-5,14) res'(3-5,14) by (metis option.inject)

  have "Cs = Cs'"
    using res(1,3,7,8,12) res'(1,3,7,8,12) by (metis add_right_imp_eq nth_equalityI)
  moreover have "DA = DA'"
    using res(2,4) res'(2,4) by fastforce
  ultimately show "E = E'"
    using res(5,6) res'(5,6) \<sigma> by blast
qed

lemma ord_resolve_rename_unique:
  assumes
    "ord_resolve_rename CAs DA AAs As \<sigma> E" and
    "ord_resolve_rename CAs DA AAs As \<sigma>' E'"
  shows "\<sigma> = \<sigma>' \<and> E = E'"
  using assms unfolding ord_resolve_rename.simps using ord_resolve_unique by meson

lemma ord_resolve_max_side_prems: "ord_resolve CAs DA AAs As \<sigma> E \<Longrightarrow> length CAs \<le> size DA"
  by (auto elim!: ord_resolve.cases)

lemma ord_resolve_rename_max_side_prems:
  "ord_resolve_rename CAs DA AAs As \<sigma> E \<Longrightarrow> length CAs \<le> size DA"
  by (elim ord_resolve_rename.cases, drule ord_resolve_max_side_prems, simp add: renamings_apart_length)


subsection \<open>Inference System\<close>

definition ord_FO_\<Gamma> :: "'a inference set" where
  "ord_FO_\<Gamma> = {Infer (mset CAs) DA E | CAs DA AAs As \<sigma> E. ord_resolve_rename CAs DA AAs As \<sigma> E}"

interpretation ord_FO_resolution: inference_system ord_FO_\<Gamma> .

lemma exists_compose: "\<exists>x. P (f x) \<Longrightarrow> \<exists>y. P y"
  by meson

lemma finite_ord_FO_resolution_inferences_between:
  assumes fin_cc: "finite CC"
  shows "finite (ord_FO_resolution.inferences_between CC C)"
proof -
  let ?CCC = "CC \<union> {C}"

  define all_AA where "all_AA = (\<Union>D \<in> ?CCC. atms_of D)"
  define max_ary where "max_ary = Max (size ` ?CCC)"
  define CAS where "CAS = {CAs. CAs \<in> lists ?CCC \<and> length CAs \<le> max_ary}"
  define AS where "AS = {As. As \<in> lists all_AA \<and> length As \<le> max_ary}"
  define AAS where "AAS = {AAs. AAs \<in> lists (mset ` AS) \<and> length AAs \<le> max_ary}"

  note defs = all_AA_def max_ary_def CAS_def AS_def AAS_def

  let ?infer_of =
    "\<lambda>CAs DA AAs As. Infer (mset CAs) DA (THE E. \<exists>\<sigma>. ord_resolve_rename CAs DA AAs As \<sigma> E)"

  let ?Z = "{\<gamma> | CAs DA AAs As \<sigma> E \<gamma>. \<gamma> = Infer (mset CAs) DA E
    \<and> ord_resolve_rename CAs DA AAs As \<sigma> E \<and> infer_from ?CCC \<gamma> \<and> C \<in># prems_of \<gamma>}"
  let ?Y = "{Infer (mset CAs) DA E | CAs DA AAs As \<sigma> E.
    ord_resolve_rename CAs DA AAs As \<sigma> E \<and> set CAs \<union> {DA} \<subseteq> ?CCC}"
  let ?X = "{?infer_of CAs DA AAs As | CAs DA AAs As. CAs \<in> CAS \<and> DA \<in> ?CCC \<and> AAs \<in> AAS \<and> As \<in> AS}"
  let ?W = "CAS \<times> ?CCC \<times> AAS \<times> AS"

  have fin_w: "finite ?W"
    unfolding defs using fin_cc by (simp add: finite_lists_length_le lists_eq_set)

  have "?Z \<subseteq> ?Y"
    by (force simp: infer_from_def)
  also have "\<dots> \<subseteq> ?X"
  proof -
    {
      fix CAs DA AAs As \<sigma> E
      assume
        res_e: "ord_resolve_rename CAs DA AAs As \<sigma> E" and
        da_in: "DA \<in> ?CCC" and
        cas_sub: "set CAs \<subseteq> ?CCC"

      have "E = (THE E. \<exists>\<sigma>. ord_resolve_rename CAs DA AAs As \<sigma> E)
        \<and> CAs \<in> CAS \<and> AAs \<in> AAS \<and> As \<in> AS" (is "?e \<and> ?cas \<and> ?aas \<and> ?as")
      proof (intro conjI)
        show ?e
          using res_e ord_resolve_rename_unique by (blast intro: the_equality[symmetric])
      next
        show ?cas
          unfolding CAS_def max_ary_def using cas_sub
            ord_resolve_rename_max_side_prems[OF res_e] da_in fin_cc
          by (auto simp add: Max_ge_iff)
      next
        show ?aas
          using res_e
        proof (cases rule: ord_resolve_rename.cases)
          case (ord_resolve_rename n \<rho> \<rho>s)
          note len_cas = this(1) and len_aas = this(2) and len_as = this(3) and
            aas_sub = this(4) and as_sub = this(5) and res_e' = this(8)

          show ?thesis
            unfolding AAS_def
          proof (clarify, intro conjI)
            show "AAs \<in> lists (mset ` AS)"
              unfolding AS_def image_def
            proof clarsimp
              fix AA
              assume "AA \<in> set AAs"
              then obtain i where
                i_lt: "i < n" and
                aa: "AA = AAs ! i"
                by (metis in_set_conv_nth len_aas)

              have casi_in: "CAs ! i \<in> ?CCC"
                using i_lt len_cas cas_sub nth_mem by blast

              have pos_aa_sub: "poss AA \<subseteq># CAs ! i"
                using aa aas_sub i_lt by blast
              then have "set_mset AA \<subseteq> atms_of (CAs ! i)"
                by (metis atms_of_poss lits_subseteq_imp_atms_subseteq set_mset_mono)
              also have aa_sub: "\<dots> \<subseteq> all_AA"
                unfolding all_AA_def using casi_in by force
              finally have aa_sub: "set_mset AA \<subseteq> all_AA"
                .

              have "size AA = size (poss AA)"
                by simp
              also have "\<dots> \<le> size (CAs ! i)"
                by (rule size_mset_mono[OF pos_aa_sub])
              also have "\<dots> \<le> max_ary"
                unfolding max_ary_def using fin_cc casi_in by auto
              finally have sz_aa: "size AA \<le> max_ary"
                .

              let ?As' = "sorted_list_of_multiset AA"

              have "?As' \<in> lists all_AA"
                using aa_sub by auto
              moreover have "length ?As' \<le> max_ary"
                using sz_aa by simp
              moreover have "AA = mset ?As'"
                by simp
              ultimately show "\<exists>xa. xa \<in> lists all_AA \<and> length xa \<le> max_ary \<and> AA = mset xa"
                by blast
            qed
          next
            have "length AAs = length As"
              unfolding len_aas len_as ..
            also have "\<dots> \<le> size DA"
              using as_sub size_mset_mono by fastforce
            also have "\<dots> \<le> max_ary"
              unfolding max_ary_def using fin_cc da_in by auto
            finally show "length AAs \<le> max_ary"
              .
          qed
        qed
      next
        show ?as
          unfolding AS_def
        proof (clarify, intro conjI)
          have "set As \<subseteq> atms_of DA"
            using res_e[simplified ord_resolve_rename.simps]
            by (metis atms_of_negs lits_subseteq_imp_atms_subseteq set_mset_mono set_mset_mset)
          also have "\<dots> \<subseteq> all_AA"
            unfolding all_AA_def using da_in by blast
          finally show "As \<in> lists all_AA"
            unfolding lists_eq_set by simp
        next
          have "length As \<le> size DA"
            using res_e[simplified ord_resolve_rename.simps]
              ord_resolve_rename_max_side_prems[OF res_e] by auto
          also have "size DA \<le> max_ary"
            unfolding max_ary_def using fin_cc da_in by auto
          finally show "length As \<le> max_ary"
            .
        qed
      qed
    }
    then show ?thesis
      by simp fast
  qed
  also have "\<dots> \<subseteq> (\<lambda>(CAs, DA, AAs, As). ?infer_of CAs DA AAs As) ` ?W"
    unfolding image_def Bex_cartesian_product by fast
  finally show ?thesis
    unfolding inference_system.inferences_between_def ord_FO_\<Gamma>_def mem_Collect_eq
    by (fast intro: rev_finite_subset[OF finite_imageI[OF fin_w]])
qed

lemma ord_FO_resolution_inferences_between_empty_empty:
  "ord_FO_resolution.inferences_between {} {#} = {}"
  unfolding ord_FO_resolution.inferences_between_def inference_system.inferences_between_def
    infer_from_def ord_FO_\<Gamma>_def
  using ord_resolve_rename_empty_main_prem by auto


subsection \<open>Lifting\<close>

text \<open>
The following corresponds to the passage between Lemmas 4.11 and 4.12.
\<close>

context
  fixes M :: "'a clause set"
  assumes select: "selection S"
begin

interpretation selection
  by (rule select)

definition S_M :: "'a literal multiset \<Rightarrow> 'a literal multiset" where
  "S_M C =
   (if C \<in> grounding_of_clss M then
      (SOME C'. \<exists>D \<sigma>. D \<in> M \<and> C = D \<cdot> \<sigma> \<and> C' = S D \<cdot> \<sigma> \<and> is_ground_subst \<sigma>)
    else
      S C)"

lemma S_M_grounding_of_clss:
  assumes "C \<in> grounding_of_clss M"
  obtains D \<sigma> where
    "D \<in> M \<and> C = D \<cdot> \<sigma> \<and> S_M C = S D \<cdot> \<sigma> \<and> is_ground_subst \<sigma>"
proof (atomize_elim, unfold S_M_def eqTrueI[OF assms] if_True, rule someI_ex)
  from assms show "\<exists>C' D \<sigma>. D \<in> M \<and> C = D \<cdot> \<sigma> \<and> C' = S D \<cdot> \<sigma> \<and> is_ground_subst \<sigma>"
    by (auto simp: grounding_of_clss_def grounding_of_cls_def)
qed

lemma S_M_not_grounding_of_clss: "C \<notin> grounding_of_clss M \<Longrightarrow> S_M C = S C"
  unfolding S_M_def by simp

lemma S_M_selects_subseteq: "S_M C \<subseteq># C"
  by (metis S_M_grounding_of_clss S_M_not_grounding_of_clss S_selects_subseteq subst_cls_mono_mset)

lemma S_M_selects_neg_lits: "L \<in># S_M C \<Longrightarrow> is_neg L"
  by (metis Melem_subst_cls S_M_grounding_of_clss S_M_not_grounding_of_clss S_selects_neg_lits
      subst_lit_is_neg)

end

end

text \<open>
The following corresponds to Lemma 4.12:
\<close>

lemma map2_add_mset_map:
  assumes "length AAs' = n" and "length As' = n"
  shows "map2 add_mset (As' \<cdot>al \<eta>) (AAs' \<cdot>aml \<eta>) = map2 add_mset As' AAs' \<cdot>aml \<eta>"
  using assms
proof (induction n arbitrary: AAs' As')
  case (Suc n)
  then have "map2 add_mset (tl (As' \<cdot>al \<eta>)) (tl (AAs' \<cdot>aml \<eta>)) = map2 add_mset (tl As') (tl AAs') \<cdot>aml \<eta>"
    by simp
  moreover
  have Succ: "length (As' \<cdot>al \<eta>) = Suc n" "length (AAs' \<cdot>aml \<eta>) = Suc n"
    using Suc(3) Suc(2) by auto
  then have "length (tl (As' \<cdot>al \<eta>)) = n" "length (tl (AAs' \<cdot>aml \<eta>)) = n"
    by auto
  then have "length (map2 add_mset (tl (As' \<cdot>al \<eta>)) (tl (AAs' \<cdot>aml \<eta>))) = n"
    "length (map2 add_mset (tl As') (tl AAs') \<cdot>aml \<eta>) = n"
    using Suc(2,3) by auto
  ultimately have "\<forall>i < n. tl (map2 add_mset ( (As' \<cdot>al \<eta>)) ((AAs' \<cdot>aml \<eta>))) ! i =
    tl (map2 add_mset (As') (AAs') \<cdot>aml \<eta>) ! i"
    using Suc(2,3) Succ by (simp add: map2_tl map_tl subst_atm_mset_list_def del: subst_atm_list_tl)
  moreover have nn: "length (map2 add_mset ((As' \<cdot>al \<eta>)) ((AAs' \<cdot>aml \<eta>))) = Suc n"
    "length (map2 add_mset (As') (AAs') \<cdot>aml \<eta>) = Suc n"
    using Succ Suc by auto
  ultimately have "\<forall>i. i < Suc n \<longrightarrow> i > 0 \<longrightarrow>
    map2 add_mset (As' \<cdot>al \<eta>) (AAs' \<cdot>aml \<eta>) ! i = (map2 add_mset As' AAs' \<cdot>aml \<eta>) ! i"
    by (auto simp: subst_atm_mset_list_def gr0_conv_Suc subst_atm_mset_def)
  moreover have "add_mset (hd As' \<cdot>a \<eta>) (hd AAs' \<cdot>am \<eta>) = add_mset (hd As') (hd AAs') \<cdot>am \<eta>"
    unfolding subst_atm_mset_def by auto
  then have "(map2 add_mset (As' \<cdot>al \<eta>) (AAs' \<cdot>aml \<eta>)) ! 0  = (map2 add_mset (As') (AAs') \<cdot>aml \<eta>) ! 0"
    using Suc by (simp add: Succ(2) subst_atm_mset_def)
  ultimately have "\<forall>i < Suc n. (map2 add_mset (As' \<cdot>al \<eta>) (AAs' \<cdot>aml \<eta>)) ! i =
    (map2 add_mset (As') (AAs') \<cdot>aml \<eta>) ! i"
    using Suc by auto
  then show ?case
    using nn list_eq_iff_nth_eq by metis
qed auto

lemma maximal_wrt_subst: "maximal_wrt (A \<cdot>a \<sigma>) (C \<cdot> \<sigma>) \<Longrightarrow> maximal_wrt A C"
  unfolding maximal_wrt_def using in_atms_of_subst less_atm_stable by blast

lemma strictly_maximal_wrt_subst: "strictly_maximal_wrt (A \<cdot>a \<sigma>) (C \<cdot> \<sigma>) \<Longrightarrow> strictly_maximal_wrt A C"
  unfolding strictly_maximal_wrt_def using in_atms_of_subst less_atm_stable by blast

lemma ground_resolvent_subset:
  assumes
    gr_cas: "is_ground_cls_list CAs" and
    gr_da: "is_ground_cls DA" and
    res_e: "ord_resolve S CAs DA AAs As \<sigma> E"
  shows "E \<subseteq># \<Union># (mset CAs) + DA"
  using res_e
proof (cases rule: ord_resolve.cases)
  case (ord_resolve n Cs D)
  note da = this(1) and e = this(2) and cas_len = this(3) and cs_len = this(4)
    and aas_len = this(5) and as_len = this(6) and cas = this(8) and mgu = this(10)
  then have cs_sub_cas: "\<Union># (mset Cs) \<subseteq># \<Union># (mset CAs)"
    using subseteq_list_Union_mset cas_len cs_len by force
  then have cs_sub_cas: "\<Union># (mset Cs) \<subseteq># \<Union># (mset CAs)"
    using subseteq_list_Union_mset cas_len cs_len by force
  then have gr_cs: "is_ground_cls_list Cs"
    using gr_cas by simp
  have d_sub_da: "D \<subseteq># DA"
    by (simp add: da)
  then have gr_d: "is_ground_cls D"
    using gr_da is_ground_cls_mono by auto

  have "is_ground_cls (\<Union># (mset Cs) + D)"
    using gr_cs gr_d by auto
  with e have "E = \<Union># (mset Cs) + D"
    by auto
  then show ?thesis
    using cs_sub_cas d_sub_da by (auto simp: subset_mset.add_mono)
qed

lemma ord_resolve_obtain_clauses:
  assumes
    res_e: "ord_resolve (S_M S M) CAs DA AAs As \<sigma> E" and
    select: "selection S" and
    grounding: "{DA} \<union> set CAs \<subseteq> grounding_of_clss M" and
    n: "length CAs = n" and
    d: "DA = D + negs (mset As)" and
    c: "(\<forall>i < n. CAs ! i = Cs ! i + poss (AAs ! i))" "length Cs = n" "length AAs = n"
  obtains DA0 \<eta>0 CAs0 \<eta>s0 As0 AAs0 D0 Cs0 where
    "length CAs0 = n"
    "length \<eta>s0 = n"
    "DA0 \<in> M"
    "DA0 \<cdot> \<eta>0 = DA"
    "S DA0 \<cdot> \<eta>0 = S_M S M DA"
    "\<forall>CA0 \<in> set CAs0. CA0 \<in> M"
    "CAs0 \<cdot>\<cdot>cl \<eta>s0 = CAs"
    "map S CAs0 \<cdot>\<cdot>cl \<eta>s0 = map (S_M S M) CAs"
    "is_ground_subst \<eta>0"
    "is_ground_subst_list \<eta>s0"
    "As0  \<cdot>al \<eta>0 = As"
    "AAs0 \<cdot>\<cdot>aml \<eta>s0 = AAs"
    "length As0 = n"
    "D0 \<cdot> \<eta>0 = D"
    "DA0 = D0 + (negs (mset As0))"
    "S_M S M (D + negs (mset As)) \<noteq> {#} \<Longrightarrow> negs (mset As0) = S DA0"
    "length Cs0 = n"
    "Cs0 \<cdot>\<cdot>cl \<eta>s0 = Cs"
    "\<forall>i < n. CAs0 ! i = Cs0 ! i + poss (AAs0 ! i)"
    "length AAs0 = n"
  using res_e
proof (cases rule: ord_resolve.cases)
  case (ord_resolve n_twin Cs_twins D_twin)
  note da = this(1) and e = this(2) and cas = this(8) and mgu = this(10) and eligible = this(11)
  from ord_resolve have "n_twin = n" "D_twin = D"
    using n d by auto
  moreover have "Cs_twins = Cs"
    using c cas n calculation(1) \<open>length Cs_twins = n_twin\<close> by (auto simp add: nth_equalityI)
  ultimately
  have nz: "n \<noteq> 0" and cs_len: "length Cs = n" and aas_len: "length AAs = n" and as_len: "length As = n"
    and da: "DA = D + negs (mset As)" and eligible: "eligible (S_M S M) \<sigma> As (D + negs (mset As))"
    and cas: "\<forall>i<n. CAs ! i = Cs ! i + poss (AAs ! i)"
    using ord_resolve by force+

  note n = \<open>n \<noteq> 0\<close> \<open>length CAs = n\<close> \<open>length Cs = n\<close> \<open>length AAs = n\<close> \<open>length As = n\<close>

  interpret S: selection S by (rule select)

  \<comment> \<open>Obtain FO side premises\<close>
  have "\<forall>CA \<in> set CAs. \<exists>CA0 \<eta>c0. CA0 \<in> M \<and> CA0 \<cdot> \<eta>c0 = CA \<and> S CA0 \<cdot> \<eta>c0 = S_M S M CA \<and> is_ground_subst \<eta>c0"
    using grounding S_M_grounding_of_clss select by (metis (no_types) le_supE subset_iff)
  then have "\<forall>i < n. \<exists>CA0 \<eta>c0. CA0 \<in> M \<and> CA0 \<cdot> \<eta>c0 = (CAs ! i) \<and> S CA0 \<cdot> \<eta>c0 = S_M S M (CAs ! i) \<and> is_ground_subst \<eta>c0"
    using n by force
  then obtain \<eta>s0f CAs0f where f_p:
    "\<forall>i < n. CAs0f i \<in> M"
    "\<forall>i < n. (CAs0f i) \<cdot> (\<eta>s0f i) = (CAs ! i)"
    "\<forall>i < n. S (CAs0f i)  \<cdot> (\<eta>s0f i) = S_M S M (CAs ! i)"
    "\<forall>i < n. is_ground_subst (\<eta>s0f i)"
    using n by (metis (no_types))

  define \<eta>s0 where
    "\<eta>s0 = map \<eta>s0f [0 ..<n]"
  define CAs0 where
    "CAs0 = map CAs0f [0 ..<n]"

  have "length \<eta>s0 = n" "length CAs0 = n"
    unfolding \<eta>s0_def CAs0_def by auto
  note n = \<open>length \<eta>s0 = n\<close> \<open>length CAs0 = n\<close> n

  \<comment> \<open>The properties we need of the FO side premises\<close>
  have CAs0_in_M: "\<forall>CA0 \<in> set CAs0. CA0 \<in> M"
    unfolding CAs0_def using f_p(1) by auto
  have CAs0_to_CAs: "CAs0 \<cdot>\<cdot>cl \<eta>s0 = CAs"
    unfolding CAs0_def \<eta>s0_def using f_p(2)  by (auto simp: n intro: nth_equalityI)
  have SCAs0_to_SMCAs: "(map S CAs0) \<cdot>\<cdot>cl \<eta>s0 = map (S_M S M) CAs"
    unfolding CAs0_def \<eta>s0_def using f_p(3) n by (force intro: nth_equalityI)
  have sub_ground: "\<forall>\<eta>c0 \<in> set \<eta>s0. is_ground_subst \<eta>c0"
    unfolding \<eta>s0_def using f_p n by force
  then have "is_ground_subst_list \<eta>s0"
    using n unfolding is_ground_subst_list_def by auto

  \<comment> \<open>Split side premises CAs0 into Cs0 and AAs0\<close>
  obtain AAs0 Cs0 where AAs0_Cs0_p:
   "AAs0 \<cdot>\<cdot>aml \<eta>s0 = AAs" "length Cs0 = n" "Cs0 \<cdot>\<cdot>cl \<eta>s0 = Cs"
   "\<forall>i < n. CAs0 ! i = Cs0 ! i + poss (AAs0 ! i)" "length AAs0 = n"
  proof -
    have "\<forall>i < n. \<exists>AA0. AA0 \<cdot>am \<eta>s0 ! i = AAs ! i \<and> poss AA0 \<subseteq># CAs0 ! i"
    proof (rule, rule)
      fix i
      assume "i < n"
      have "CAs0 ! i \<cdot> \<eta>s0 ! i = CAs ! i"
        using \<open>i < n\<close> \<open>CAs0 \<cdot>\<cdot>cl \<eta>s0 = CAs\<close> n by force
      moreover have "poss (AAs ! i) \<subseteq># CAs !i"
        using \<open>i < n\<close> cas by auto
      ultimately obtain poss_AA0 where
        nn: "poss_AA0 \<cdot> \<eta>s0 ! i = poss (AAs ! i) \<and> poss_AA0 \<subseteq># CAs0 ! i"
        using cas image_mset_of_subset unfolding subst_cls_def by metis
      then have l: "\<forall>L \<in># poss_AA0. is_pos L"
        unfolding subst_cls_def by (metis Melem_subst_cls imageE literal.disc(1)
            literal.map_disc_iff set_image_mset subst_cls_def subst_lit_def)

      define AA0 where
        "AA0 = image_mset atm_of poss_AA0"

      have na: "poss AA0 = poss_AA0"
        using l unfolding AA0_def by auto
      then have "AA0 \<cdot>am \<eta>s0 ! i = AAs ! i"
        using nn by (metis (mono_tags) literal.inject(1) multiset.inj_map_strong subst_cls_poss)
      moreover have "poss AA0 \<subseteq># CAs0 ! i"
        using na nn by auto
      ultimately show "\<exists>AA0. AA0 \<cdot>am \<eta>s0 ! i = AAs ! i \<and> poss AA0 \<subseteq># CAs0 ! i"
        by blast
    qed
    then obtain AAs0f where 
      AAs0f_p: "\<forall>i < n. AAs0f i \<cdot>am \<eta>s0 ! i = AAs ! i \<and> (poss (AAs0f i)) \<subseteq># CAs0 ! i"
      by metis

    define AAs0 where "AAs0 = map AAs0f [0 ..<n]"

    then have "length AAs0 = n"
      by auto
    note n = n \<open>length AAs0 = n\<close>

    from AAs0_def have "\<forall>i < n. AAs0 ! i \<cdot>am \<eta>s0 ! i = AAs ! i"
      using AAs0f_p by auto
    then have AAs0_AAs: "AAs0 \<cdot>\<cdot>aml \<eta>s0 = AAs"
      using n by (auto intro: nth_equalityI)

    from AAs0_def have AAs0_in_CAs0: "\<forall>i < n. poss (AAs0 ! i) \<subseteq># CAs0 ! i"
      using AAs0f_p by auto

    define Cs0 where
      "Cs0 = map2 (-) CAs0 (map poss AAs0)"

    have "length Cs0 = n"
      using Cs0_def n by auto
    note n = n \<open>length Cs0 = n\<close>

    have "\<forall>i < n. CAs0 ! i = Cs0 ! i + poss (AAs0 ! i)"
      using AAs0_in_CAs0 Cs0_def n by auto
    then have "Cs0 \<cdot>\<cdot>cl \<eta>s0 = Cs"
      using \<open>CAs0 \<cdot>\<cdot>cl \<eta>s0 = CAs\<close> AAs0_AAs cas n by (auto intro: nth_equalityI)

    show ?thesis
      using that 
        \<open>AAs0 \<cdot>\<cdot>aml \<eta>s0 = AAs\<close> \<open>Cs0 \<cdot>\<cdot>cl \<eta>s0 = Cs\<close> \<open>\<forall>i < n. CAs0 ! i = Cs0 ! i + poss (AAs0 ! i)\<close>
        \<open>length AAs0 = n\<close> \<open>length Cs0 = n\<close>
      by blast
  qed

  \<comment> \<open>Obtain FO main premise\<close>
  have "\<exists>DA0 \<eta>0. DA0 \<in> M \<and> DA = DA0 \<cdot> \<eta>0 \<and> S DA0 \<cdot> \<eta>0 = S_M S M DA \<and> is_ground_subst \<eta>0"
    using grounding S_M_grounding_of_clss select by (metis le_supE singletonI subsetCE)
  then obtain DA0 \<eta>0 where 
    DA0_\<eta>0_p: "DA0 \<in> M \<and> DA = DA0 \<cdot> \<eta>0 \<and> S DA0 \<cdot> \<eta>0 = S_M S M DA \<and> is_ground_subst \<eta>0"
    by auto
  \<comment> \<open>The properties we need of the FO main premise\<close>
  have DA0_in_M: "DA0 \<in> M"
    using DA0_\<eta>0_p by auto
  have DA0_to_DA: "DA0 \<cdot> \<eta>0 = DA"
    using DA0_\<eta>0_p by auto
  have SDA0_to_SMDA: "S DA0 \<cdot> \<eta>0 = S_M S M DA"
    using DA0_\<eta>0_p by auto
  have "is_ground_subst \<eta>0"
    using DA0_\<eta>0_p by auto

  \<comment> \<open>Split main premise DA0 into D0 and As0\<close>
  obtain D0 As0 where D0As0_p:
     "As0  \<cdot>al \<eta>0 = As" "length As0 = n" "D0 \<cdot> \<eta>0 = D" "DA0 = D0 + (negs (mset As0))"
    "S_M S M (D + negs (mset As)) \<noteq> {#} \<Longrightarrow> negs (mset As0) = S DA0"
  proof -
    {
      assume a: "S_M S M (D + negs (mset As)) = {#} \<and> length As = (Suc 0)
        \<and> maximal_wrt (As ! 0 \<cdot>a \<sigma>) ((D + negs (mset As)) \<cdot> \<sigma>)"
      then have as: "mset As = {#As ! 0#}"
        by (auto intro: nth_equalityI)
      then have "negs (mset As) = {#Neg (As ! 0)#}"
        by (simp add: \<open>mset As = {#As ! 0#}\<close>)
      then have "DA = D + {#Neg (As ! 0)#}"
        using da by auto
      then obtain L where "L \<in># DA0 \<and> L \<cdot>l \<eta>0 = Neg (As ! 0)"
        using DA0_to_DA by (metis Melem_subst_cls mset_subset_eq_add_right single_subset_iff)
      then have "Neg (atm_of L) \<in># DA0 \<and> Neg (atm_of L) \<cdot>l \<eta>0 = Neg (As ! 0)"
        by (metis Neg_atm_of_iff literal.sel(2) subst_lit_is_pos)
      then have "[atm_of L] \<cdot>al \<eta>0 = As \<and> negs (mset [atm_of L]) \<subseteq># DA0"
        using as subst_lit_def by auto
      then have "\<exists>As0. As0 \<cdot>al \<eta>0 = As \<and> negs (mset As0) \<subseteq># DA0
        \<and> (S_M S M (D + negs (mset As)) \<noteq> {#} \<longrightarrow> negs (mset As0) = S DA0)"
        using a by blast
    }
    moreover
    {
      assume "S_M S M (D + negs (mset As)) = negs (mset As)"
      then have "negs (mset As) = S DA0 \<cdot> \<eta>0"
        using da \<open>S DA0 \<cdot> \<eta>0 = S_M S M DA\<close> by auto
      then have "\<exists>As0. negs (mset As0) = S DA0 \<and> As0 \<cdot>al \<eta>0 = As"
        using instance_list[of As "S DA0" \<eta>0] S.S_selects_neg_lits by auto
      then have "\<exists>As0. As0 \<cdot>al \<eta>0 = As \<and> negs (mset As0) \<subseteq># DA0
        \<and> (S_M S M (D + negs (mset As)) \<noteq> {#} \<longrightarrow> negs (mset As0) = S DA0)"
        using S.S_selects_subseteq by auto
    }
    ultimately have "\<exists>As0. As0 \<cdot>al \<eta>0 = As \<and> (negs (mset As0)) \<subseteq># DA0
      \<and> (S_M S M (D + negs (mset As)) \<noteq> {#} \<longrightarrow> negs (mset As0) = S DA0)"
      using eligible unfolding eligible.simps by auto
    then obtain As0 where
      As0_p: "As0 \<cdot>al \<eta>0 = As \<and> negs (mset As0) \<subseteq># DA0
      \<and> (S_M S M (D + negs (mset As)) \<noteq> {#} \<longrightarrow> negs (mset As0) = S DA0)"
      by blast
    then have "length As0 = n"
      using as_len by auto
    note n = n this

    have "As0 \<cdot>al \<eta>0 = As"
      using As0_p by auto

    define D0 where
      "D0 = DA0 - negs (mset As0)"
    then have "DA0 = D0 + negs (mset As0)"
      using As0_p by auto
    then have "D0 \<cdot> \<eta>0 = D"
      using DA0_to_DA da As0_p by auto

    have "S_M S M (D + negs (mset As)) \<noteq> {#} \<Longrightarrow> negs (mset As0) = S DA0"
      using As0_p by blast
    then show ?thesis
      using that \<open>As0 \<cdot>al \<eta>0 = As\<close> \<open>D0 \<cdot> \<eta>0= D\<close> \<open>DA0 = D0 +  (negs (mset As0))\<close> \<open>length As0 = n\<close>
      by metis
  qed

  show ?thesis
    using that[OF n(2,1) DA0_in_M  DA0_to_DA SDA0_to_SMDA CAs0_in_M CAs0_to_CAs SCAs0_to_SMCAs
        \<open>is_ground_subst \<eta>0\<close> \<open>is_ground_subst_list \<eta>s0\<close> \<open>As0  \<cdot>al \<eta>0 = As\<close>
        \<open>AAs0 \<cdot>\<cdot>aml \<eta>s0 = AAs\<close>
        \<open>length As0 = n\<close>
        \<open>D0 \<cdot> \<eta>0 = D\<close>
        \<open>DA0 = D0 + (negs (mset As0))\<close>
        \<open>S_M S M (D + negs (mset As)) \<noteq> {#} \<Longrightarrow> negs (mset As0) = S DA0\<close>
        \<open>length Cs0 = n\<close>
        \<open>Cs0 \<cdot>\<cdot>cl \<eta>s0 = Cs\<close>
        \<open>\<forall>i < n. CAs0 ! i = Cs0 ! i + poss (AAs0 ! i)\<close>
        \<open>length AAs0 = n\<close>]
    by auto
qed

lemma
  assumes "Pos A \<in># C"
  shows "A \<in> atms_of C"
  using assms
  by (simp add: atm_iff_pos_or_neg_lit)

lemma ord_resolve_rename_lifting:
  assumes
    sel_stable: "\<And>\<rho> C. is_renaming \<rho> \<Longrightarrow> S (C \<cdot> \<rho>) = S C \<cdot> \<rho>" and
    res_e: "ord_resolve (S_M S M) CAs DA AAs As \<sigma> E" and
    select: "selection S" and
    grounding: "{DA} \<union> set CAs \<subseteq> grounding_of_clss M"
  obtains \<eta>s \<eta> \<eta>2 CAs0 DA0 AAs0 As0 E0 \<tau> where
    "is_ground_subst \<eta>"
    "is_ground_subst_list \<eta>s"
    "is_ground_subst \<eta>2"
    "ord_resolve_rename S CAs0 DA0 AAs0 As0 \<tau> E0"
    (* In the previous proofs we have CAs and DA on lhs of equality... which is better? *)
    "CAs0 \<cdot>\<cdot>cl \<eta>s = CAs" "DA0 \<cdot> \<eta> = DA" "E0 \<cdot> \<eta>2 = E" 
    "{DA0} \<union> set CAs0 \<subseteq> M"
  using res_e
proof (cases rule: ord_resolve.cases)
  case (ord_resolve n Cs D)
  note da = this(1) and e = this(2) and cas_len = this(3) and cs_len = this(4) and
    aas_len = this(5) and as_len = this(6) and nz = this(7) and cas = this(8) and
    aas_not_empt = this(9) and mgu = this(10) and eligible = this(11) and str_max = this(12) and
    sel_empt = this(13)

  have sel_ren_list_inv:
    "\<And>\<rho>s Cs. length \<rho>s = length Cs \<Longrightarrow> is_renaming_list \<rho>s \<Longrightarrow> map S (Cs \<cdot>\<cdot>cl \<rho>s) = map S Cs \<cdot>\<cdot>cl \<rho>s"
    using sel_stable unfolding is_renaming_list_def by (auto intro: nth_equalityI)

  note n = \<open>n \<noteq> 0\<close> \<open>length CAs = n\<close> \<open>length Cs = n\<close> \<open>length AAs = n\<close> \<open>length As = n\<close>

  interpret S: selection S by (rule select)

  obtain DA0 \<eta>0 CAs0 \<eta>s0 As0 AAs0 D0 Cs0 where as0:
    "length CAs0 = n"
    "length \<eta>s0 = n"
    "DA0 \<in> M"
    "DA0 \<cdot> \<eta>0 = DA"
    "S DA0 \<cdot> \<eta>0 = S_M S M DA"
    "\<forall>CA0 \<in> set CAs0. CA0 \<in> M"
    "CAs0 \<cdot>\<cdot>cl \<eta>s0 = CAs"
    "map S CAs0 \<cdot>\<cdot>cl \<eta>s0 = map (S_M S M) CAs"
    "is_ground_subst \<eta>0"
    "is_ground_subst_list \<eta>s0"
    "As0 \<cdot>al \<eta>0 = As"
    "AAs0 \<cdot>\<cdot>aml \<eta>s0 = AAs"
    "length As0 = n"
    "D0 \<cdot> \<eta>0 = D"
    "DA0 = D0 + (negs (mset As0))"
    "S_M S M (D + negs (mset As)) \<noteq> {#} \<Longrightarrow> negs (mset As0) = S DA0"
    "length Cs0 = n"
    "Cs0 \<cdot>\<cdot>cl \<eta>s0 = Cs"
    "\<forall>i < n. CAs0 ! i = Cs0 ! i + poss (AAs0 ! i)"
    "length AAs0 = n"
    using ord_resolve_obtain_clauses[of S M CAs DA, OF res_e select grounding n(2) \<open>DA = D + negs (mset As)\<close>
      \<open>\<forall>i<n. CAs ! i = Cs ! i + poss (AAs ! i)\<close> \<open>length Cs = n\<close> \<open>length AAs = n\<close>, of thesis] by blast

  note n = \<open>length CAs0 = n\<close> \<open>length \<eta>s0 = n\<close> \<open>length As0 = n\<close> \<open>length AAs0 = n\<close> \<open>length Cs0 = n\<close> n

  have "length (renamings_apart (DA0 # CAs0)) = Suc n"
    using n renamings_apart_length by auto

  note n = this n

  define \<rho> where
    "\<rho> = hd (renamings_apart (DA0 # CAs0))"
  define \<rho>s where
    "\<rho>s = tl (renamings_apart (DA0 # CAs0))"
  define DA0' where
    "DA0' = DA0 \<cdot> \<rho>"
  define D0' where
    "D0' = D0 \<cdot> \<rho>"
  define As0' where
    "As0' = As0 \<cdot>al \<rho>"
  define CAs0' where
    "CAs0' = CAs0 \<cdot>\<cdot>cl \<rho>s"
  define Cs0' where
    "Cs0' = Cs0 \<cdot>\<cdot>cl \<rho>s"
  define AAs0' where
    "AAs0' = AAs0 \<cdot>\<cdot>aml \<rho>s"
  define \<eta>0' where
    "\<eta>0' = inv_renaming \<rho> \<odot> \<eta>0"
  define \<eta>s0' where
    "\<eta>s0' = map inv_renaming \<rho>s \<odot>s \<eta>s0"

  have renames_DA0: "is_renaming \<rho>"
    using renamings_apart_length renamings_apart_renaming unfolding \<rho>_def
    by (metis length_greater_0_conv list.exhaust_sel list.set_intros(1) list.simps(3))

  have renames_CAs0: "is_renaming_list \<rho>s"
    using renamings_apart_length renamings_apart_renaming unfolding \<rho>s_def
    by (metis is_renaming_list_def length_greater_0_conv list.set_sel(2) list.simps(3))

  have "length \<rho>s = n"
    unfolding \<rho>s_def using n by auto
  note n = n \<open>length \<rho>s = n\<close>
  have "length As0' = n"
    unfolding As0'_def using n by auto
  have "length CAs0' = n"
    using as0(1) n unfolding CAs0'_def by auto
  have "length Cs0' = n"
    unfolding Cs0'_def using n by auto
  have "length AAs0' = n"
    unfolding AAs0'_def using n by auto
  have "length \<eta>s0' = n"
    using as0(2) n unfolding \<eta>s0'_def by auto
  note n = \<open>length CAs0' = n\<close> \<open>length \<eta>s0' = n\<close> \<open>length As0' = n\<close> \<open>length AAs0' = n\<close> \<open>length Cs0' = n\<close> n

  have DA0'_DA: "DA0' \<cdot> \<eta>0' = DA"
    using as0(4) unfolding \<eta>0'_def DA0'_def using renames_DA0 by simp
  have D0'_D: "D0' \<cdot> \<eta>0' = D"
    using as0(14) unfolding \<eta>0'_def D0'_def using renames_DA0 by simp
  have As0'_As: "As0' \<cdot>al \<eta>0' = As"
    using as0(11) unfolding \<eta>0'_def As0'_def using renames_DA0 by auto
  have "S DA0' \<cdot> \<eta>0' = S_M S M DA"
    using as0(5) unfolding \<eta>0'_def DA0'_def using renames_DA0 sel_stable by auto
  have CAs0'_CAs: "CAs0' \<cdot>\<cdot>cl \<eta>s0' = CAs"
    using as0(7) unfolding CAs0'_def \<eta>s0'_def using renames_CAs0 n by auto
  have Cs0'_Cs: "Cs0' \<cdot>\<cdot>cl \<eta>s0' = Cs"
    using as0(18) unfolding Cs0'_def \<eta>s0'_def using renames_CAs0 n by auto
  have AAs0'_AAs: "AAs0' \<cdot>\<cdot>aml \<eta>s0' = AAs"
    using as0(12) unfolding \<eta>s0'_def AAs0'_def using renames_CAs0 using n by auto
  have "map S CAs0' \<cdot>\<cdot>cl \<eta>s0' = map (S_M S M) CAs"
    unfolding CAs0'_def \<eta>s0'_def using as0(8) n renames_CAs0 sel_ren_list_inv by auto

  have DA0'_split: "DA0' = D0' + negs (mset As0')"
    using as0(15) DA0'_def D0'_def As0'_def by auto
  then have D0'_subset_DA0': "D0' \<subseteq># DA0'"
    by auto
  from DA0'_split have negs_As0'_subset_DA0': "negs (mset As0') \<subseteq># DA0'"
    by auto

  have CAs0'_split: "\<forall>i<n. CAs0' ! i = Cs0' ! i + poss (AAs0' ! i)"
    using as0(19) CAs0'_def Cs0'_def AAs0'_def n by auto
  then have "\<forall>i<n. Cs0' ! i \<subseteq># CAs0' ! i"
    by auto
  from CAs0'_split have poss_AAs0'_subset_CAs0': "\<forall>i<n. poss (AAs0' ! i) \<subseteq># CAs0' ! i"
    by auto
  then have AAs0'_in_atms_of_CAs0': "\<forall>i < n. \<forall>A\<in>#AAs0' ! i. A \<in> atms_of (CAs0' ! i)"
    by (auto simp add: atm_iff_pos_or_neg_lit)

  have as0':
    "S_M S M (D + negs (mset As)) \<noteq> {#} \<Longrightarrow> negs (mset As0') = S DA0'"
  proof -
    assume a: "S_M S M (D + negs (mset As)) \<noteq> {#}"
    then have "negs (mset As0) \<cdot> \<rho> = S DA0 \<cdot> \<rho>"
      using as0(16) unfolding \<rho>_def by metis
    then show "negs (mset As0') = S DA0'"
      using  As0'_def DA0'_def using sel_stable[of \<rho> DA0] renames_DA0 by auto
  qed

  have vd: "var_disjoint (DA0' # CAs0')"
    unfolding DA0'_def CAs0'_def using renamings_apart_var_disjoint
    unfolding \<rho>_def \<rho>s_def
    by (metis length_greater_0_conv list.exhaust_sel n(6) substitution.subst_cls_lists_Cons
        substitution_axioms zero_less_Suc)

  \<comment> \<open>Introduce ground substitution\<close>
  from vd DA0'_DA CAs0'_CAs have "\<exists>\<eta>. \<forall>i < Suc n. \<forall>S. S \<subseteq># (DA0' # CAs0') ! i \<longrightarrow> S \<cdot> (\<eta>0'#\<eta>s0') ! i = S \<cdot> \<eta>"
    unfolding var_disjoint_def using n by auto
  then obtain \<eta> where \<eta>_p: "\<forall>i < Suc n. \<forall>S. S \<subseteq># (DA0' # CAs0') ! i \<longrightarrow> S \<cdot> (\<eta>0'#\<eta>s0') ! i = S \<cdot> \<eta>"
    by auto
  have \<eta>_p_lit: "\<forall>i < Suc n. \<forall>L. L \<in># (DA0' # CAs0') ! i \<longrightarrow> L \<cdot>l (\<eta>0'#\<eta>s0') ! i = L \<cdot>l \<eta>"
  proof (rule, rule, rule, rule)
    fix i :: "nat" and L :: "'a literal"
    assume a:
      "i < Suc n"
      "L \<in># (DA0' # CAs0') ! i"
    then have "\<forall>S. S \<subseteq># (DA0' # CAs0') ! i \<longrightarrow> S \<cdot> (\<eta>0' # \<eta>s0') ! i = S \<cdot> \<eta>"
      using \<eta>_p by auto
    then have "{# L #} \<cdot> (\<eta>0' # \<eta>s0') ! i = {# L #} \<cdot> \<eta>"
      using a by (meson single_subset_iff)
    then show "L \<cdot>l (\<eta>0' # \<eta>s0') ! i = L \<cdot>l \<eta>" by auto
  qed
  have \<eta>_p_atm: "\<forall>i < Suc n. \<forall>A. A \<in> atms_of ((DA0' # CAs0') ! i) \<longrightarrow> A \<cdot>a (\<eta>0'#\<eta>s0') ! i = A \<cdot>a \<eta>"
  proof (rule, rule, rule, rule)
    fix i :: "nat" and A :: "'a"
    assume a:
      "i < Suc n"
      "A \<in> atms_of ((DA0' # CAs0') ! i)"
    then obtain L where L_p: "atm_of L = A \<and> L \<in># (DA0' # CAs0') ! i"
      unfolding atms_of_def by auto
    then have "L \<cdot>l (\<eta>0'#\<eta>s0') ! i = L \<cdot>l \<eta>"
      using \<eta>_p_lit a by auto
    then show "A \<cdot>a (\<eta>0' # \<eta>s0') ! i = A \<cdot>a \<eta>"
      using L_p unfolding subst_lit_def by (cases L) auto
  qed

  have DA0'_DA: "DA0' \<cdot> \<eta> = DA"
    using DA0'_DA \<eta>_p by auto
  have "D0' \<cdot> \<eta> = D" using \<eta>_p D0'_D n D0'_subset_DA0' by auto
  have "As0' \<cdot>al \<eta> = As"
  proof (rule nth_equalityI)
    show "length (As0' \<cdot>al \<eta>) = length As"
      using n by auto
  next
    show "(As0' \<cdot>al \<eta>) ! i = As ! i" if a: "i < length (As0' \<cdot>al \<eta>)" for i
    proof -
      have A_eq: "\<forall>A. A \<in> atms_of DA0' \<longrightarrow> A \<cdot>a \<eta>0' = A \<cdot>a \<eta>"
        using \<eta>_p_atm n by force
      have "As0' ! i \<in> atms_of DA0'"
        using negs_As0'_subset_DA0' unfolding atms_of_def
        using a n by force
      then have "As0' ! i \<cdot>a \<eta>0' = As0' ! i \<cdot>a \<eta>"
         using A_eq by simp
      then show "(As0' \<cdot>al \<eta>) ! i = As ! i"
        using As0'_As \<open>length As0' = n\<close> a by auto
    qed
  qed

  have "S DA0' \<cdot> \<eta> = S_M S M DA"
    using \<open>S DA0' \<cdot> \<eta>0' = S_M S M DA\<close> \<eta>_p S.S_selects_subseteq by auto

  from \<eta>_p have \<eta>_p_CAs0': "\<forall>i < n. (CAs0' ! i) \<cdot> (\<eta>s0' ! i) = (CAs0'! i) \<cdot> \<eta>"
    using n by auto
  then have "CAs0' \<cdot>\<cdot>cl \<eta>s0' = CAs0' \<cdot>cl \<eta>"
    using n by (auto intro: nth_equalityI)
  then have CAs0'_\<eta>_fo_CAs: "CAs0' \<cdot>cl \<eta> = CAs"
    using CAs0'_CAs \<eta>_p n by auto

  from \<eta>_p have "\<forall>i < n. S (CAs0' ! i) \<cdot> \<eta>s0' ! i = S (CAs0' ! i) \<cdot> \<eta>"
    using S.S_selects_subseteq n by auto
  then have "map S CAs0' \<cdot>\<cdot>cl \<eta>s0' = map S CAs0' \<cdot>cl \<eta>"
    using n by (auto intro: nth_equalityI)
  then have SCAs0'_\<eta>_fo_SMCAs: "map S CAs0' \<cdot>cl \<eta> = map (S_M S M) CAs"
    using \<open>map S CAs0' \<cdot>\<cdot>cl \<eta>s0' = map (S_M S M) CAs\<close> by auto

  have "Cs0' \<cdot>cl \<eta> = Cs"
  proof (rule nth_equalityI)
    show "length (Cs0' \<cdot>cl \<eta>) = length Cs"
      using n by auto
  next
    show "(Cs0' \<cdot>cl \<eta>) ! i = Cs ! i" if "i < length (Cs0' \<cdot>cl \<eta>)" for i
    proof -
      have a: "i < n"
        using that n by force
      have "(Cs0' \<cdot>\<cdot>cl \<eta>s0') ! i = Cs ! i"
        using Cs0'_Cs a n by force
      moreover
      have \<eta>_p_CAs0': "\<forall>S. S \<subseteq># CAs0' ! i \<longrightarrow> S \<cdot> \<eta>s0' ! i = S \<cdot> \<eta>"
        using \<eta>_p a by force
      have "Cs0' ! i \<cdot> \<eta>s0' ! i = (Cs0' \<cdot>cl \<eta>) ! i"
        using \<eta>_p_CAs0' \<open>\<forall>i<n. Cs0' ! i \<subseteq># CAs0' ! i\<close> a n by force
      then have "(Cs0' \<cdot>\<cdot>cl \<eta>s0') ! i = (Cs0' \<cdot>cl \<eta>) ! i "
        using a n by force
      ultimately show "(Cs0' \<cdot>cl \<eta>) ! i = Cs ! i"
        by auto
    qed
  qed

  have AAs0'_AAs: "AAs0' \<cdot>aml \<eta> = AAs"
  proof (rule nth_equalityI)
    show "length (AAs0' \<cdot>aml \<eta>) = length AAs"
      using n by auto
  next
    show "(AAs0' \<cdot>aml \<eta>) ! i = AAs ! i" if a: "i < length (AAs0' \<cdot>aml \<eta>)" for i
    proof -
      have "i < n"
        using that n by force
      then have "\<forall>A. A \<in> atms_of ((DA0' # CAs0') ! Suc i) \<longrightarrow> A \<cdot>a (\<eta>0' # \<eta>s0') ! Suc i = A \<cdot>a \<eta>"
        using \<eta>_p_atm n by force
      then have A_eq: "\<forall>A. A \<in> atms_of (CAs0' ! i) \<longrightarrow> A \<cdot>a \<eta>s0' ! i = A \<cdot>a \<eta>"
        by auto
      have AAs_CAs0': "\<forall>A \<in># AAs0' ! i. A \<in> atms_of (CAs0' ! i)"
        using AAs0'_in_atms_of_CAs0' unfolding atms_of_def
        using a n by force
      then have "AAs0' ! i \<cdot>am  \<eta>s0' ! i = AAs0' ! i \<cdot>am \<eta>"
        unfolding subst_atm_mset_def using A_eq unfolding subst_atm_mset_def by auto
      then show "(AAs0' \<cdot>aml \<eta>) ! i = AAs ! i"
         using AAs0'_AAs \<open>length AAs0' = n\<close> \<open>length \<eta>s0' = n\<close> a by auto
    qed
  qed

  \<comment> \<open>Obtain MGU and substitution\<close>
  obtain \<tau> \<phi> where \<tau>\<phi>:
    "Some \<tau> = mgu (set_mset ` set (map2 add_mset As0' AAs0'))"
    "\<tau> \<odot> \<phi> = \<eta> \<odot> \<sigma>"
  proof -
    have uu: "is_unifiers \<sigma> (set_mset ` set (map2 add_mset (As0' \<cdot>al \<eta>) (AAs0' \<cdot>aml \<eta>)))"
      using mgu mgu_sound is_mgu_def unfolding \<open>AAs0' \<cdot>aml \<eta> = AAs\<close> using \<open>As0' \<cdot>al \<eta> = As\<close> by auto
    have \<eta>\<sigma>uni: "is_unifiers (\<eta> \<odot> \<sigma>) (set_mset ` set (map2 add_mset As0' AAs0'))"
    proof -
      have "set_mset ` set (map2 add_mset As0' AAs0' \<cdot>aml \<eta>) =
        set_mset ` set (map2 add_mset As0' AAs0') \<cdot>ass \<eta>"
        unfolding subst_atmss_def subst_atm_mset_list_def using subst_atm_mset_def subst_atms_def
        by (simp add: image_image subst_atm_mset_def subst_atms_def)
      then have "is_unifiers \<sigma> (set_mset ` set (map2 add_mset As0' AAs0') \<cdot>ass \<eta>)"
        using uu by (auto simp: n map2_add_mset_map)
      then show ?thesis
        using is_unifiers_comp by auto
    qed
    then obtain \<tau> where
      \<tau>_p: "Some \<tau> = mgu (set_mset ` set (map2 add_mset As0' AAs0'))"
      using mgu_complete
      by (metis (mono_tags, hide_lams) List.finite_set finite_imageI finite_set_mset image_iff)
    moreover then obtain \<phi> where \<phi>_p: "\<tau> \<odot> \<phi> = \<eta> \<odot> \<sigma>"
      by (metis (mono_tags, hide_lams) finite_set \<eta>\<sigma>uni finite_imageI finite_set_mset image_iff
          mgu_sound set_mset_mset substitution_ops.is_mgu_def) (* should be simpler *)
    ultimately show thesis
      using that by auto
  qed

  \<comment> \<open>Lifting eligibility\<close>
  have eligible0': "eligible S \<tau> As0' (D0' + negs (mset As0'))"
  proof -
    have "S_M S M (D + negs (mset As)) = negs (mset As) \<or> S_M S M (D + negs (mset As)) = {#} \<and>
      length As = 1 \<and> maximal_wrt (As ! 0 \<cdot>a \<sigma>) ((D + negs (mset As)) \<cdot> \<sigma>)"
      using eligible unfolding eligible.simps by auto
    then show ?thesis
    proof
      assume "S_M S M (D + negs (mset As)) = negs (mset As)"
      then have "S_M S M (D + negs (mset As)) \<noteq> {#}"
        using n by force
      then have "S (D0' + negs (mset As0')) = negs (mset As0')"
        using as0' DA0'_split by auto
      then show ?thesis
        unfolding eligible.simps[simplified]  by auto
    next
      assume asm: "S_M S M (D + negs (mset As)) = {#} \<and> length As = 1 \<and>
        maximal_wrt (As ! 0 \<cdot>a \<sigma>) ((D + negs (mset As)) \<cdot> \<sigma>)"
      then have "S (D0' + negs (mset As0')) = {#}"
        using \<open>D0' \<cdot> \<eta> = D\<close>[symmetric] \<open>As0' \<cdot>al \<eta> = As\<close>[symmetric] \<open>S (DA0') \<cdot> \<eta> = S_M S M (DA)\<close>
          da DA0'_split subst_cls_empty_iff by metis
      moreover from asm have l: "length As0' = 1"
        using \<open>As0' \<cdot>al \<eta> = As\<close> by auto
      moreover from asm have "maximal_wrt (As0' ! 0 \<cdot>a (\<tau> \<odot> \<phi>)) ((D0' + negs (mset As0')) \<cdot> (\<tau> \<odot> \<phi>))"
        using \<open>As0' \<cdot>al \<eta> = As\<close> \<open>D0' \<cdot> \<eta> = D\<close> using l \<tau>\<phi> by auto
      then have "maximal_wrt (As0' ! 0 \<cdot>a \<tau> \<cdot>a \<phi>) ((D0' + negs (mset As0')) \<cdot> \<tau> \<cdot> \<phi>)"
        by auto
      then have "maximal_wrt (As0' ! 0 \<cdot>a \<tau>) ((D0' + negs (mset As0')) \<cdot> \<tau>)"
        using maximal_wrt_subst by blast
      ultimately show ?thesis
        unfolding eligible.simps[simplified] by auto
    qed
  qed

  \<comment> \<open>Lifting maximality\<close>
  have maximality: "\<forall>i < n. strictly_maximal_wrt (As0' ! i \<cdot>a \<tau>) (Cs0' ! i \<cdot> \<tau>)"
    (* Reformulate in list notation? *)
  proof -
    from str_max have "\<forall>i < n. strictly_maximal_wrt ((As0' \<cdot>al \<eta>) ! i \<cdot>a \<sigma>) ((Cs0' \<cdot>cl \<eta>) ! i \<cdot> \<sigma>)"
      using \<open>As0' \<cdot>al \<eta> = As\<close>  \<open>Cs0' \<cdot>cl \<eta> = Cs\<close> by simp
    then have "\<forall>i < n. strictly_maximal_wrt (As0' ! i \<cdot>a (\<tau> \<odot> \<phi>)) (Cs0' ! i \<cdot> (\<tau> \<odot> \<phi>))"
      using n \<tau>\<phi> by simp
    then have "\<forall>i < n. strictly_maximal_wrt (As0' ! i \<cdot>a \<tau> \<cdot>a \<phi>) (Cs0' ! i \<cdot> \<tau> \<cdot> \<phi>)"
      by auto
    then show "\<forall>i < n. strictly_maximal_wrt (As0' ! i \<cdot>a \<tau>) (Cs0' ! i \<cdot> \<tau>)"
      using strictly_maximal_wrt_subst \<tau>\<phi> by blast
  qed

  \<comment> \<open>Lifting nothing being selected\<close>
  have nothing_selected: "\<forall>i < n. S (CAs0' ! i) = {#}"
  proof -
    have "\<forall>i < n. (map S CAs0' \<cdot>cl \<eta>) ! i = map (S_M S M) CAs ! i"
      by (simp add: \<open>map S CAs0' \<cdot>cl \<eta> = map (S_M S M) CAs\<close>)
    then have "\<forall>i < n. S (CAs0' ! i) \<cdot> \<eta> = S_M S M (CAs ! i)"
      using n by auto
    then have "\<forall>i < n. S (CAs0' ! i)  \<cdot> \<eta> = {#}"
      using sel_empt \<open>\<forall>i < n.  S (CAs0' ! i) \<cdot> \<eta> = S_M S M (CAs ! i)\<close> by auto
    then show "\<forall>i < n. S (CAs0' ! i) = {#}"
      using subst_cls_empty_iff by blast
  qed

  \<comment> \<open>Lifting AAs0's non-emptiness\<close>
  have "\<forall>i < n. AAs0' ! i \<noteq> {#}"
    using n aas_not_empt \<open>AAs0' \<cdot>aml \<eta> = AAs\<close> by auto

  \<comment> \<open>Resolve the lifted clauses\<close>
  define E0' where
    "E0' = (\<Union># (mset Cs0') + D0') \<cdot> \<tau>"

  have res_e0': "ord_resolve S CAs0' DA0' AAs0' As0' \<tau> E0'"
    using ord_resolve.intros[of CAs0' n Cs0' AAs0' As0' \<tau> S D0',
      OF _ _ _ _ _ _ \<open>\<forall>i < n. AAs0' ! i \<noteq> {#}\<close> \<tau>\<phi>(1) eligible0'
        \<open>\<forall>i < n. strictly_maximal_wrt (As0' ! i \<cdot>a \<tau>) (Cs0' ! i \<cdot> \<tau>)\<close> \<open>\<forall>i < n. S (CAs0' ! i) = {#}\<close>]
    unfolding E0'_def using DA0'_split n \<open>\<forall>i<n. CAs0' ! i = Cs0' ! i + poss (AAs0' ! i)\<close> by blast

  \<comment> \<open>Prove resolvent instantiates to ground resolvent\<close>
  have e0'\<phi>e: "E0' \<cdot> \<phi> = E"
  proof -
    have "E0' \<cdot> \<phi> = (\<Union># (mset Cs0') + D0') \<cdot> (\<tau> \<odot> \<phi>)"
      unfolding E0'_def by auto
    also have "\<dots> = (\<Union># (mset Cs0') + D0') \<cdot> (\<eta> \<odot> \<sigma>)"
      using \<tau>\<phi> by auto
    also have "\<dots> = (\<Union># (mset Cs) + D) \<cdot> \<sigma>"
      using \<open>Cs0' \<cdot>cl \<eta> = Cs\<close> \<open>D0' \<cdot> \<eta> = D\<close> by auto
    also have "\<dots> = E"
      using e by auto
    finally show e0'\<phi>e: "E0' \<cdot> \<phi> = E"
      .
  qed

  \<comment> \<open>Replace @{term \<phi>} with a true ground substitution\<close>
  obtain \<eta>2 where
    ground_\<eta>2: "is_ground_subst \<eta>2" "E0' \<cdot> \<eta>2 = E"
  proof -
    have "is_ground_cls_list CAs" "is_ground_cls DA"
      using grounding grounding_ground unfolding is_ground_cls_list_def by auto
    then have "is_ground_cls E"
      using res_e ground_resolvent_subset by (force intro: is_ground_cls_mono)
    then show thesis
      using that e0'\<phi>e make_ground_subst by auto
  qed


  \<comment> \<open>Wrap up the proof\<close>
  have "ord_resolve S (CAs0 \<cdot>\<cdot>cl \<rho>s) (DA0 \<cdot> \<rho>) (AAs0 \<cdot>\<cdot>aml \<rho>s) (As0 \<cdot>al \<rho>) \<tau> E0'"
    using res_e0' As0'_def \<rho>_def AAs0'_def \<rho>s_def DA0'_def \<rho>_def CAs0'_def \<rho>s_def by simp
  moreover have "\<forall>i<n. poss (AAs0 ! i) \<subseteq># CAs0 ! i"
    using as0(19) by auto
  moreover have "negs (mset As0) \<subseteq># DA0"
    using local.as0(15) by auto
  ultimately have "ord_resolve_rename S CAs0 DA0 AAs0 As0 \<tau> E0'"
    using ord_resolve_rename[of CAs0 n AAs0 As0 DA0 \<rho> \<rho>s S \<tau> E0'] \<rho>_def \<rho>s_def n by auto
  then show thesis
    using that[of \<eta>0 \<eta>s0 \<eta>2 CAs0 DA0] \<open>is_ground_subst \<eta>0\<close> \<open>is_ground_subst_list \<eta>s0\<close>
      \<open>is_ground_subst \<eta>2\<close> \<open>CAs0 \<cdot>\<cdot>cl \<eta>s0 = CAs\<close> \<open>DA0 \<cdot> \<eta>0 = DA\<close> \<open>E0' \<cdot> \<eta>2 = E\<close> \<open>DA0 \<in> M\<close>
      \<open>\<forall>CA \<in> set CAs0. CA \<in> M\<close> by blast
qed

end

end
