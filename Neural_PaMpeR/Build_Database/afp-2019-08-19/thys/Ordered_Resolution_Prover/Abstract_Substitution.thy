(*  Title:       Abstract Substitutions
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2014
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2014, 2017
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2016, 2017
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>Abstract Substitutions\<close>

theory Abstract_Substitution
  imports Clausal_Logic Map2
begin

text \<open>
Atoms and substitutions are abstracted away behind some locales, to avoid having a direct dependency
on the IsaFoR library.

Conventions: \<open>'s\<close> substitutions, \<open>'a\<close> atoms.
\<close>


subsection \<open>Library\<close>

(* TODO: move to Isabelle? *)
lemma f_Suc_decr_eventually_const:
  fixes f :: "nat \<Rightarrow> nat"
  assumes leq: "\<forall>i. f (Suc i) \<le> f i"
  shows "\<exists>l. \<forall>l' \<ge> l. f l' = f (Suc l')"
proof (rule ccontr)
  assume a: "\<nexists>l. \<forall>l' \<ge> l. f l' = f (Suc l')"
  have "\<forall>i. \<exists>i'. i' > i \<and> f i' < f i"
  proof
    fix i
    from a have "\<exists>l' \<ge> i. f l' \<noteq> f (Suc l')"
      by auto
    then obtain l' where
      l'_p: "l' \<ge> i \<and> f l' \<noteq> f (Suc l')"
      by metis
    then have "f l' > f (Suc l')"
      using leq le_eq_less_or_eq by auto
    moreover have "f i \<ge> f l'"
      using leq l'_p by (induction l' arbitrary: i) (blast intro: lift_Suc_antimono_le)+
    ultimately show "\<exists>i' > i. f i' < f i"
      using l'_p less_le_trans by blast
  qed
  then obtain g_sm :: "nat \<Rightarrow> nat" where
    g_sm_p: "\<forall>i. g_sm i > i \<and> f (g_sm i) < f i"
    by metis

  define c :: "nat \<Rightarrow> nat" where
    "\<And>n. c n = (g_sm ^^ n) 0"

  have "f (c i) > f (c (Suc i))" for i
    by (induction i) (auto simp: c_def g_sm_p)
  then have "\<forall>i. (f \<circ> c) i > (f \<circ> c) (Suc i)"
    by auto
  then have "\<exists>fc :: nat \<Rightarrow> nat. \<forall>i. fc i > fc (Suc i)"
    by metis
  then show False
    using wf_less_than by (simp add: wf_iff_no_infinite_down_chain)
qed


subsection \<open>Substitution Operators\<close>

locale substitution_ops =
  fixes
    subst_atm :: "'a \<Rightarrow> 's \<Rightarrow> 'a" and
    id_subst :: 's and
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's"
begin

abbreviation subst_atm_abbrev :: "'a \<Rightarrow> 's \<Rightarrow> 'a" (infixl "\<cdot>a" 67) where
  "subst_atm_abbrev \<equiv> subst_atm"

abbreviation comp_subst_abbrev :: "'s \<Rightarrow> 's \<Rightarrow> 's" (infixl "\<odot>" 67) where
  "comp_subst_abbrev \<equiv> comp_subst"

definition comp_substs :: "'s list \<Rightarrow> 's list \<Rightarrow> 's list" (infixl "\<odot>s" 67) where
  "\<sigma>s \<odot>s \<tau>s = map2 comp_subst \<sigma>s \<tau>s"

definition subst_atms :: "'a set \<Rightarrow> 's \<Rightarrow> 'a set" (infixl "\<cdot>as" 67) where
  "AA \<cdot>as \<sigma> = (\<lambda>A. A \<cdot>a \<sigma>) ` AA"

definition subst_atmss :: "'a set set \<Rightarrow> 's \<Rightarrow> 'a set set" (infixl "\<cdot>ass" 67) where
  "AAA \<cdot>ass \<sigma> = (\<lambda>AA. AA \<cdot>as \<sigma>) ` AAA"

definition subst_atm_list :: "'a list \<Rightarrow> 's \<Rightarrow> 'a list" (infixl "\<cdot>al" 67) where
  "As \<cdot>al \<sigma> = map (\<lambda>A. A \<cdot>a \<sigma>) As"

definition subst_atm_mset :: "'a multiset \<Rightarrow> 's \<Rightarrow> 'a multiset" (infixl "\<cdot>am" 67) where
  "AA \<cdot>am \<sigma> = image_mset (\<lambda>A. A \<cdot>a \<sigma>) AA"

definition
  subst_atm_mset_list :: "'a multiset list \<Rightarrow> 's \<Rightarrow> 'a multiset list" (infixl "\<cdot>aml" 67)
where
  "AAA \<cdot>aml \<sigma> = map (\<lambda>AA. AA \<cdot>am \<sigma>) AAA"

definition
  subst_atm_mset_lists :: "'a multiset list \<Rightarrow> 's list \<Rightarrow> 'a multiset list" (infixl "\<cdot>\<cdot>aml" 67)
where
  "AAs \<cdot>\<cdot>aml \<sigma>s = map2 (\<cdot>am) AAs \<sigma>s"

definition subst_lit :: "'a literal \<Rightarrow> 's \<Rightarrow> 'a literal" (infixl "\<cdot>l" 67) where
  "L \<cdot>l \<sigma> = map_literal (\<lambda>A. A \<cdot>a \<sigma>) L"

lemma atm_of_subst_lit[simp]: "atm_of (L \<cdot>l \<sigma>) = atm_of L \<cdot>a \<sigma>"
  unfolding subst_lit_def by (cases L) simp+

definition subst_cls :: "'a clause \<Rightarrow> 's \<Rightarrow> 'a clause" (infixl "\<cdot>" 67) where
  "AA \<cdot> \<sigma> = image_mset (\<lambda>A. A \<cdot>l \<sigma>) AA"

definition subst_clss :: "'a clause set \<Rightarrow> 's \<Rightarrow> 'a clause set" (infixl "\<cdot>cs" 67) where
  "AA \<cdot>cs \<sigma> = (\<lambda>A. A \<cdot> \<sigma>) ` AA"

definition subst_cls_list :: "'a clause list \<Rightarrow> 's \<Rightarrow> 'a clause list" (infixl "\<cdot>cl" 67) where
  "Cs \<cdot>cl \<sigma> = map (\<lambda>A. A \<cdot> \<sigma>) Cs"

definition subst_cls_lists :: "'a clause list \<Rightarrow> 's list \<Rightarrow> 'a clause list" (infixl "\<cdot>\<cdot>cl" 67) where
  "Cs \<cdot>\<cdot>cl \<sigma>s = map2 (\<cdot>) Cs \<sigma>s"

definition subst_cls_mset :: "'a clause multiset \<Rightarrow> 's \<Rightarrow> 'a clause multiset" (infixl "\<cdot>cm" 67) where
  "CC \<cdot>cm \<sigma> = image_mset (\<lambda>A. A \<cdot> \<sigma>) CC"

lemma subst_cls_add_mset[simp]: "add_mset L C \<cdot> \<sigma> = add_mset (L \<cdot>l \<sigma>) (C \<cdot> \<sigma>)"
  unfolding subst_cls_def by simp

lemma subst_cls_mset_add_mset[simp]: "add_mset C CC \<cdot>cm \<sigma> = add_mset (C \<cdot> \<sigma>) (CC \<cdot>cm \<sigma>)"
  unfolding subst_cls_mset_def by simp

definition generalizes_atm :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "generalizes_atm A B \<longleftrightarrow> (\<exists>\<sigma>. A \<cdot>a \<sigma> = B)"

definition strictly_generalizes_atm :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "strictly_generalizes_atm A B \<longleftrightarrow> generalizes_atm A B \<and> \<not> generalizes_atm B A"

definition generalizes_lit :: "'a literal \<Rightarrow> 'a literal \<Rightarrow> bool" where
  "generalizes_lit L M \<longleftrightarrow> (\<exists>\<sigma>. L \<cdot>l \<sigma> = M)"

definition strictly_generalizes_lit :: "'a literal \<Rightarrow> 'a literal \<Rightarrow> bool" where
  "strictly_generalizes_lit L M \<longleftrightarrow> generalizes_lit L M \<and> \<not> generalizes_lit M L"

definition generalizes_cls :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" where
  "generalizes_cls C D \<longleftrightarrow> (\<exists>\<sigma>. C \<cdot> \<sigma> = D)"

definition strictly_generalizes_cls :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" where
  "strictly_generalizes_cls C D \<longleftrightarrow> generalizes_cls C D \<and> \<not> generalizes_cls D C"

definition subsumes :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" where
  "subsumes C D \<longleftrightarrow> (\<exists>\<sigma>. C \<cdot> \<sigma> \<subseteq># D)"

definition strictly_subsumes :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" where
  "strictly_subsumes C D \<longleftrightarrow> subsumes C D \<and> \<not> subsumes D C"

(* FIXME: define as exists renaming from one to the other? *)
definition variants :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> bool" where
  "variants C D \<longleftrightarrow> generalizes_cls C D \<and> generalizes_cls D C"

definition is_renaming :: "'s \<Rightarrow> bool" where
  "is_renaming \<sigma> \<longleftrightarrow> (\<exists>\<tau>. \<sigma> \<odot> \<tau> = id_subst)"

definition is_renaming_list :: "'s list \<Rightarrow> bool" where
  "is_renaming_list \<sigma>s \<longleftrightarrow> (\<forall>\<sigma> \<in> set \<sigma>s. is_renaming \<sigma>)"

definition inv_renaming :: "'s \<Rightarrow> 's" where
  "inv_renaming \<sigma> = (SOME \<tau>. \<sigma> \<odot> \<tau> = id_subst)"

definition is_ground_atm :: "'a \<Rightarrow> bool" where
  "is_ground_atm A \<longleftrightarrow> (\<forall>\<sigma>. A = A \<cdot>a \<sigma>)"

definition is_ground_atms :: "'a set \<Rightarrow> bool" where
  "is_ground_atms AA = (\<forall>A \<in> AA. is_ground_atm A)"

definition is_ground_atm_list :: "'a list \<Rightarrow> bool" where
  "is_ground_atm_list As \<longleftrightarrow> (\<forall>A \<in> set As. is_ground_atm A)"

definition is_ground_atm_mset :: "'a multiset \<Rightarrow> bool" where
  "is_ground_atm_mset AA \<longleftrightarrow> (\<forall>A. A \<in># AA \<longrightarrow> is_ground_atm A)"

definition is_ground_lit :: "'a literal \<Rightarrow> bool" where
  "is_ground_lit L \<longleftrightarrow> is_ground_atm (atm_of L)"

definition is_ground_cls :: "'a clause \<Rightarrow> bool" where
  "is_ground_cls C \<longleftrightarrow> (\<forall>L. L \<in># C \<longrightarrow> is_ground_lit L)"

definition is_ground_clss :: "'a clause set \<Rightarrow> bool" where
  "is_ground_clss CC \<longleftrightarrow> (\<forall>C \<in> CC. is_ground_cls C)"

definition is_ground_cls_list :: "'a clause list \<Rightarrow> bool" where
  "is_ground_cls_list CC \<longleftrightarrow> (\<forall>C \<in> set CC. is_ground_cls C)"

definition is_ground_subst :: "'s \<Rightarrow> bool" where
  "is_ground_subst \<sigma> \<longleftrightarrow> (\<forall>A. is_ground_atm (A \<cdot>a \<sigma>))"

definition is_ground_subst_list :: "'s list \<Rightarrow> bool" where
  "is_ground_subst_list \<sigma>s \<longleftrightarrow> (\<forall>\<sigma> \<in> set \<sigma>s. is_ground_subst \<sigma>)"

definition grounding_of_cls :: "'a clause \<Rightarrow> 'a clause set" where
  "grounding_of_cls C = {C \<cdot> \<sigma> | \<sigma>. is_ground_subst \<sigma>}"

definition grounding_of_clss :: "'a clause set \<Rightarrow> 'a clause set" where
  "grounding_of_clss CC = (\<Union>C \<in> CC. grounding_of_cls C)"

definition is_unifier :: "'s \<Rightarrow> 'a set \<Rightarrow> bool" where
  "is_unifier \<sigma> AA \<longleftrightarrow> card (AA \<cdot>as \<sigma>) \<le> 1"

definition is_unifiers :: "'s \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "is_unifiers \<sigma> AAA \<longleftrightarrow> (\<forall>AA \<in> AAA. is_unifier \<sigma> AA)"

definition is_mgu :: "'s \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "is_mgu \<sigma> AAA \<longleftrightarrow> is_unifiers \<sigma> AAA \<and> (\<forall>\<tau>. is_unifiers \<tau> AAA \<longrightarrow> (\<exists>\<gamma>. \<tau> = \<sigma> \<odot> \<gamma>))"

definition var_disjoint :: "'a clause list \<Rightarrow> bool" where
  "var_disjoint Cs \<longleftrightarrow>
   (\<forall>\<sigma>s. length \<sigma>s = length Cs \<longrightarrow> (\<exists>\<tau>. \<forall>i < length Cs. \<forall>S. S \<subseteq># Cs ! i \<longrightarrow> S \<cdot> \<sigma>s ! i = S \<cdot> \<tau>))"

end


subsection \<open>Substitution Lemmas\<close>

locale substitution = substitution_ops subst_atm id_subst comp_subst
  for
    subst_atm :: "'a \<Rightarrow> 's \<Rightarrow> 'a" and
    id_subst :: 's and
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's" +
  fixes
    renamings_apart :: "'a clause list \<Rightarrow> 's list" and
    atm_of_atms :: "'a list \<Rightarrow> 'a"
  assumes
    subst_atm_id_subst[simp]: "A \<cdot>a id_subst = A" and
    subst_atm_comp_subst[simp]: "A \<cdot>a (\<sigma> \<odot> \<tau>) = (A \<cdot>a \<sigma>) \<cdot>a \<tau>" and
    subst_ext: "(\<And>A. A \<cdot>a \<sigma> = A \<cdot>a \<tau>) \<Longrightarrow> \<sigma> = \<tau>" and
    make_ground_subst: "is_ground_cls (C \<cdot> \<sigma>) \<Longrightarrow> \<exists>\<tau>. is_ground_subst \<tau> \<and>C \<cdot> \<tau> = C \<cdot> \<sigma>" and
    wf_strictly_generalizes_atm: "wfP strictly_generalizes_atm" and
    renamings_apart_length:  "length (renamings_apart Cs) = length Cs" and
    renamings_apart_renaming: "\<rho> \<in> set (renamings_apart Cs) \<Longrightarrow> is_renaming \<rho>" and
    renamings_apart_var_disjoint: "var_disjoint (Cs \<cdot>\<cdot>cl (renamings_apart Cs))" and
    atm_of_atms_subst:
      "\<And>As Bs. atm_of_atms As \<cdot>a \<sigma> = atm_of_atms Bs \<longleftrightarrow> map (\<lambda>A. A \<cdot>a \<sigma>) As = Bs"
begin

lemma subst_ext_iff: "\<sigma> = \<tau> \<longleftrightarrow> (\<forall>A. A \<cdot>a \<sigma> = A \<cdot>a \<tau>)"
  by (blast intro: subst_ext)


subsubsection \<open>Identity Substitution\<close>

lemma id_subst_comp_subst[simp]: "id_subst \<odot> \<sigma> = \<sigma>"
  by (rule subst_ext) simp

lemma comp_subst_id_subst[simp]: "\<sigma> \<odot> id_subst = \<sigma>"
  by (rule subst_ext) simp

lemma id_subst_comp_substs[simp]: "replicate (length \<sigma>s) id_subst \<odot>s \<sigma>s = \<sigma>s"
  using comp_substs_def by (induction \<sigma>s) auto

lemma comp_substs_id_subst[simp]: "\<sigma>s \<odot>s replicate (length \<sigma>s) id_subst = \<sigma>s"
  using comp_substs_def by (induction \<sigma>s) auto

lemma subst_atms_id_subst[simp]: "AA \<cdot>as id_subst = AA"
  unfolding subst_atms_def by simp

lemma subst_atmss_id_subst[simp]: "AAA \<cdot>ass id_subst = AAA"
  unfolding subst_atmss_def by simp

lemma subst_atm_list_id_subst[simp]: "As \<cdot>al id_subst = As"
  unfolding subst_atm_list_def by auto

lemma subst_atm_mset_id_subst[simp]: "AA \<cdot>am id_subst = AA"
  unfolding subst_atm_mset_def by simp

lemma subst_atm_mset_list_id_subst[simp]: "AAs \<cdot>aml id_subst = AAs"
  unfolding subst_atm_mset_list_def by simp

lemma subst_atm_mset_lists_id_subst[simp]: "AAs \<cdot>\<cdot>aml replicate (length AAs) id_subst = AAs"
  unfolding subst_atm_mset_lists_def by (induct AAs) auto

lemma subst_lit_id_subst[simp]: "L \<cdot>l id_subst = L"
  unfolding subst_lit_def by (simp add: literal.map_ident)

lemma subst_cls_id_subst[simp]: "C \<cdot> id_subst = C"
  unfolding subst_cls_def by simp

lemma subst_clss_id_subst[simp]: "CC \<cdot>cs id_subst = CC"
  unfolding subst_clss_def by simp

lemma subst_cls_list_id_subst[simp]: "Cs \<cdot>cl id_subst = Cs"
  unfolding subst_cls_list_def by simp

lemma subst_cls_lists_id_subst[simp]: "Cs \<cdot>\<cdot>cl replicate (length Cs) id_subst = Cs"
  unfolding subst_cls_lists_def by (induct Cs) auto

lemma subst_cls_mset_id_subst[simp]: "CC \<cdot>cm id_subst = CC"
  unfolding subst_cls_mset_def by simp


subsubsection \<open>Associativity of Composition\<close>

lemma comp_subst_assoc[simp]: "\<sigma> \<odot> (\<tau> \<odot> \<gamma>) = \<sigma> \<odot> \<tau> \<odot> \<gamma>"
  by (rule subst_ext) simp


subsubsection \<open>Compatibility of Substitution and Composition\<close>

lemma subst_atms_comp_subst[simp]: "AA \<cdot>as (\<tau> \<odot> \<sigma>) = AA \<cdot>as \<tau> \<cdot>as \<sigma>"
  unfolding subst_atms_def by auto

lemma subst_atmss_comp_subst[simp]: "AAA \<cdot>ass (\<tau> \<odot> \<sigma>) = AAA \<cdot>ass \<tau> \<cdot>ass \<sigma>"
  unfolding subst_atmss_def by auto

lemma subst_atm_list_comp_subst[simp]: "As \<cdot>al (\<tau> \<odot> \<sigma>) = As \<cdot>al \<tau> \<cdot>al \<sigma>"
  unfolding subst_atm_list_def by auto

lemma subst_atm_mset_comp_subst[simp]: "AA \<cdot>am (\<tau> \<odot> \<sigma>) = AA \<cdot>am \<tau> \<cdot>am \<sigma>"
  unfolding subst_atm_mset_def by auto

lemma subst_atm_mset_list_comp_subst[simp]: "AAs \<cdot>aml (\<tau> \<odot> \<sigma>) = (AAs \<cdot>aml \<tau>) \<cdot>aml \<sigma>"
  unfolding subst_atm_mset_list_def by auto

lemma subst_atm_mset_lists_comp_substs[simp]: "AAs \<cdot>\<cdot>aml (\<tau>s \<odot>s \<sigma>s) = AAs \<cdot>\<cdot>aml \<tau>s \<cdot>\<cdot>aml \<sigma>s"
  unfolding subst_atm_mset_lists_def comp_substs_def map_zip_map map_zip_map2 map_zip_assoc
  by (simp add: split_def)

lemma subst_lit_comp_subst[simp]: "L \<cdot>l (\<tau> \<odot> \<sigma>) = L \<cdot>l \<tau> \<cdot>l \<sigma>"
  unfolding subst_lit_def by (auto simp: literal.map_comp o_def)

lemma subst_cls_comp_subst[simp]: "C \<cdot> (\<tau> \<odot> \<sigma>) = C \<cdot> \<tau> \<cdot> \<sigma>"
  unfolding subst_cls_def by auto

lemma subst_clsscomp_subst[simp]: "CC \<cdot>cs (\<tau> \<odot> \<sigma>) = CC \<cdot>cs \<tau> \<cdot>cs \<sigma>"
  unfolding subst_clss_def by auto

lemma subst_cls_list_comp_subst[simp]: "Cs \<cdot>cl (\<tau> \<odot> \<sigma>) = Cs \<cdot>cl \<tau> \<cdot>cl \<sigma>"
  unfolding subst_cls_list_def by auto

lemma subst_cls_lists_comp_substs[simp]: "Cs \<cdot>\<cdot>cl (\<tau>s \<odot>s \<sigma>s) = Cs \<cdot>\<cdot>cl \<tau>s \<cdot>\<cdot>cl \<sigma>s"
  unfolding subst_cls_lists_def comp_substs_def map_zip_map map_zip_map2 map_zip_assoc
  by (simp add: split_def)

lemma subst_cls_mset_comp_subst[simp]: "CC \<cdot>cm (\<tau> \<odot> \<sigma>) = CC \<cdot>cm \<tau> \<cdot>cm \<sigma>"
  unfolding subst_cls_mset_def by auto


subsubsection \<open>``Commutativity'' of Membership and Substitution\<close>

lemma Melem_subst_atm_mset[simp]: "A \<in># AA \<cdot>am \<sigma> \<longleftrightarrow> (\<exists>B. B \<in># AA \<and> A = B \<cdot>a \<sigma>)"
  unfolding subst_atm_mset_def by auto

lemma Melem_subst_cls[simp]: "L \<in># C \<cdot> \<sigma> \<longleftrightarrow> (\<exists>M. M \<in># C \<and> L = M \<cdot>l \<sigma>)"
  unfolding subst_cls_def by auto

lemma Melem_subst_cls_mset[simp]: "AA \<in># CC \<cdot>cm \<sigma> \<longleftrightarrow> (\<exists>BB. BB \<in># CC \<and> AA = BB \<cdot> \<sigma>)"
  unfolding subst_cls_mset_def by auto


subsubsection \<open>Signs and Substitutions\<close>

lemma subst_lit_is_neg[simp]: "is_neg (L \<cdot>l \<sigma>) = is_neg L"
  unfolding subst_lit_def by auto

lemma subst_lit_is_pos[simp]: "is_pos (L \<cdot>l \<sigma>) = is_pos L"
  unfolding subst_lit_def by auto

lemma subst_minus[simp]: "(- L) \<cdot>l \<mu> = - (L  \<cdot>l \<mu>)"
  by (simp add: literal.map_sel subst_lit_def uminus_literal_def)


subsubsection \<open>Substitution on Literal(s)\<close>

lemma eql_neg_lit_eql_atm[simp]: "(Neg A' \<cdot>l \<eta>) = Neg A \<longleftrightarrow> A' \<cdot>a \<eta> = A"
  by (simp add: subst_lit_def)

lemma eql_pos_lit_eql_atm[simp]: "(Pos A' \<cdot>l \<eta>) = Pos A \<longleftrightarrow> A' \<cdot>a \<eta> = A"
  by (simp add: subst_lit_def)

lemma subst_cls_negs[simp]: "(negs AA) \<cdot> \<sigma> = negs (AA \<cdot>am \<sigma>)"
  unfolding subst_cls_def subst_lit_def subst_atm_mset_def by auto

lemma subst_cls_poss[simp]: "(poss AA) \<cdot> \<sigma> = poss (AA \<cdot>am \<sigma>)"
  unfolding subst_cls_def subst_lit_def subst_atm_mset_def by auto

lemma atms_of_subst_atms: "atms_of C \<cdot>as \<sigma> = atms_of (C \<cdot> \<sigma>)"
proof -
  have "atms_of (C \<cdot> \<sigma>) = set_mset (image_mset atm_of (image_mset (map_literal (\<lambda>A. A \<cdot>a \<sigma>)) C))"
    unfolding subst_cls_def subst_atms_def subst_lit_def atms_of_def by auto
  also have "... = set_mset (image_mset (\<lambda>A. A \<cdot>a \<sigma>) (image_mset atm_of C))"
    by simp (meson literal.map_sel)
  finally show "atms_of C \<cdot>as \<sigma> = atms_of (C \<cdot> \<sigma>)"
    unfolding subst_atms_def atms_of_def by auto
qed

lemma in_image_Neg_is_neg[simp]: "L \<cdot>l \<sigma> \<in> Neg ` AA \<Longrightarrow> is_neg L"
  by (metis bex_imageD literal.disc(2) literal.map_disc_iff subst_lit_def)

lemma subst_lit_in_negs_subst_is_neg: "L \<cdot>l \<sigma> \<in># (negs AA) \<cdot> \<tau> \<Longrightarrow> is_neg L"
  by simp

lemma subst_lit_in_negs_is_neg: "L \<cdot>l \<sigma> \<in># negs AA \<Longrightarrow> is_neg L"
  by simp


subsubsection \<open>Substitution on Empty\<close>

lemma subst_atms_empty[simp]: "{} \<cdot>as \<sigma> = {}"
  unfolding subst_atms_def by auto

lemma subst_atmss_empty[simp]: "{} \<cdot>ass \<sigma> = {}"
  unfolding subst_atmss_def by auto

lemma comp_substs_empty_iff[simp]: "\<sigma>s \<odot>s \<eta>s = [] \<longleftrightarrow> \<sigma>s = [] \<or> \<eta>s = []"
  using comp_substs_def map2_empty_iff by auto

lemma subst_atm_list_empty[simp]: "[] \<cdot>al \<sigma> = []"
  unfolding subst_atm_list_def by auto

lemma subst_atm_mset_empty[simp]: "{#} \<cdot>am \<sigma> = {#}"
  unfolding subst_atm_mset_def by auto

lemma subst_atm_mset_list_empty[simp]: "[] \<cdot>aml \<sigma> = []"
  unfolding subst_atm_mset_list_def by auto

lemma subst_atm_mset_lists_empty[simp]: "[] \<cdot>\<cdot>aml \<sigma>s = []"
  unfolding subst_atm_mset_lists_def by auto

lemma subst_cls_empty[simp]: "{#} \<cdot> \<sigma> = {#}"
  unfolding subst_cls_def by auto

lemma subst_clss_empty[simp]: "{} \<cdot>cs \<sigma> = {}"
  unfolding subst_clss_def by auto

lemma subst_cls_list_empty[simp]: "[] \<cdot>cl \<sigma> = []"
  unfolding subst_cls_list_def by auto

lemma subst_cls_lists_empty[simp]: "[] \<cdot>\<cdot>cl \<sigma>s = []"
  unfolding subst_cls_lists_def by auto

lemma subst_scls_mset_empty[simp]: "{#} \<cdot>cm \<sigma> = {#}"
  unfolding subst_cls_mset_def by auto

lemma subst_atms_empty_iff[simp]: "AA \<cdot>as \<eta> = {} \<longleftrightarrow> AA = {}"
  unfolding subst_atms_def by auto

lemma subst_atmss_empty_iff[simp]: "AAA \<cdot>ass \<eta> = {} \<longleftrightarrow> AAA = {}"
  unfolding subst_atmss_def by auto

lemma subst_atm_list_empty_iff[simp]: "As \<cdot>al \<eta> = [] \<longleftrightarrow> As = []"
  unfolding subst_atm_list_def by auto

lemma subst_atm_mset_empty_iff[simp]: "AA \<cdot>am \<eta> = {#} \<longleftrightarrow> AA = {#}"
  unfolding subst_atm_mset_def by auto

lemma subst_atm_mset_list_empty_iff[simp]: "AAs \<cdot>aml \<eta> = [] \<longleftrightarrow> AAs = []"
  unfolding subst_atm_mset_list_def by auto

lemma subst_atm_mset_lists_empty_iff[simp]: "AAs \<cdot>\<cdot>aml \<eta>s = [] \<longleftrightarrow> (AAs = [] \<or> \<eta>s = [])"
  using map2_empty_iff subst_atm_mset_lists_def by auto

lemma subst_cls_empty_iff[simp]: "C \<cdot> \<eta> = {#} \<longleftrightarrow> C = {#}"
  unfolding subst_cls_def by auto

lemma subst_clss_empty_iff[simp]: "CC \<cdot>cs \<eta> = {} \<longleftrightarrow> CC = {}"
  unfolding subst_clss_def by auto

lemma subst_cls_list_empty_iff[simp]: "Cs \<cdot>cl \<eta> = [] \<longleftrightarrow> Cs = []"
  unfolding subst_cls_list_def by auto

lemma subst_cls_lists_empty_iff[simp]: "Cs \<cdot>\<cdot>cl \<eta>s = [] \<longleftrightarrow> (Cs = [] \<or> \<eta>s = [])"
  using map2_empty_iff subst_cls_lists_def by auto

lemma subst_cls_mset_empty_iff[simp]: "CC \<cdot>cm \<eta> = {#} \<longleftrightarrow> CC = {#}"
  unfolding subst_cls_mset_def by auto


subsubsection \<open>Substitution on a Union\<close>

lemma subst_atms_union[simp]: "(AA \<union> BB) \<cdot>as \<sigma> = AA \<cdot>as \<sigma> \<union> BB \<cdot>as \<sigma>"
  unfolding subst_atms_def by auto

lemma subst_atmss_union[simp]: "(AAA \<union> BBB) \<cdot>ass \<sigma> = AAA \<cdot>ass \<sigma> \<union> BBB \<cdot>ass \<sigma>"
  unfolding subst_atmss_def by auto

lemma subst_atm_list_append[simp]: "(As @ Bs) \<cdot>al \<sigma> = As \<cdot>al \<sigma> @ Bs \<cdot>al \<sigma>"
  unfolding subst_atm_list_def by auto

lemma subst_atm_mset_union[simp]: "(AA + BB) \<cdot>am \<sigma> = AA \<cdot>am \<sigma> + BB \<cdot>am \<sigma>"
  unfolding subst_atm_mset_def by auto

lemma subst_atm_mset_list_append[simp]: "(AAs @ BBs) \<cdot>aml \<sigma> = AAs \<cdot>aml \<sigma> @ BBs \<cdot>aml \<sigma>"
  unfolding subst_atm_mset_list_def by auto

lemma subst_cls_union[simp]: "(C + D) \<cdot> \<sigma> = C \<cdot> \<sigma> + D \<cdot> \<sigma>"
  unfolding subst_cls_def by auto

lemma subst_clss_union[simp]: "(CC \<union> DD) \<cdot>cs \<sigma> = CC \<cdot>cs \<sigma> \<union> DD \<cdot>cs \<sigma>"
  unfolding subst_clss_def by auto

lemma subst_cls_list_append[simp]: "(Cs @ Ds) \<cdot>cl \<sigma> = Cs \<cdot>cl \<sigma> @ Ds \<cdot>cl \<sigma>"
  unfolding subst_cls_list_def by auto

lemma subst_cls_mset_union[simp]: "(CC + DD) \<cdot>cm \<sigma> = CC \<cdot>cm \<sigma> + DD \<cdot>cm \<sigma>"
  unfolding subst_cls_mset_def by auto


subsubsection \<open>Substitution on a Singleton\<close>

lemma subst_atms_single[simp]: "{A} \<cdot>as \<sigma> = {A \<cdot>a \<sigma>}"
  unfolding subst_atms_def by auto

lemma subst_atmss_single[simp]: "{AA} \<cdot>ass \<sigma> = {AA \<cdot>as \<sigma>}"
  unfolding subst_atmss_def by auto

lemma subst_atm_list_single[simp]: "[A] \<cdot>al \<sigma> = [A \<cdot>a \<sigma>]"
  unfolding subst_atm_list_def by auto

lemma subst_atm_mset_single[simp]: "{#A#} \<cdot>am \<sigma> = {#A \<cdot>a \<sigma>#}"
  unfolding subst_atm_mset_def by auto

lemma subst_atm_mset_list[simp]: "[AA] \<cdot>aml \<sigma> = [AA \<cdot>am \<sigma>]"
  unfolding subst_atm_mset_list_def by auto

lemma subst_cls_single[simp]: "{#L#} \<cdot> \<sigma> = {#L \<cdot>l \<sigma>#}"
  by simp

lemma subst_clss_single[simp]: "{C} \<cdot>cs \<sigma> = {C \<cdot> \<sigma>}"
  unfolding subst_clss_def by auto

lemma subst_cls_list_single[simp]: "[C] \<cdot>cl \<sigma> = [C \<cdot> \<sigma>]"
  unfolding subst_cls_list_def by auto

lemma subst_cls_mset_single[simp]: "{#C#} \<cdot>cm \<sigma> = {#C \<cdot> \<sigma>#}"
  by simp


subsubsection \<open>Substitution on @{term Cons}\<close>

lemma subst_atm_list_Cons[simp]: "(A # As) \<cdot>al \<sigma> = A \<cdot>a \<sigma> # As \<cdot>al \<sigma>"
  unfolding subst_atm_list_def by auto

lemma subst_atm_mset_list_Cons[simp]: "(A # As) \<cdot>aml \<sigma> = A \<cdot>am \<sigma> # As \<cdot>aml \<sigma>"
  unfolding subst_atm_mset_list_def by auto

lemma subst_atm_mset_lists_Cons[simp]: "(C # Cs) \<cdot>\<cdot>aml (\<sigma> # \<sigma>s) = C \<cdot>am \<sigma> # Cs \<cdot>\<cdot>aml \<sigma>s"
  unfolding subst_atm_mset_lists_def by auto

lemma subst_cls_list_Cons[simp]: "(C # Cs) \<cdot>cl \<sigma> = C \<cdot> \<sigma> # Cs \<cdot>cl \<sigma>"
  unfolding subst_cls_list_def by auto

lemma subst_cls_lists_Cons[simp]: "(C # Cs) \<cdot>\<cdot>cl (\<sigma> # \<sigma>s) = C \<cdot> \<sigma> # Cs \<cdot>\<cdot>cl \<sigma>s"
  unfolding subst_cls_lists_def by auto


subsubsection \<open>Substitution on @{term tl}\<close>

lemma subst_atm_list_tl[simp]: "tl (As \<cdot>al \<eta>) = tl As \<cdot>al \<eta>"
  by (induction As) auto

lemma subst_atm_mset_list_tl[simp]: "tl (AAs \<cdot>aml \<eta>) = tl AAs \<cdot>aml \<eta>"
  by (induction AAs) auto


subsubsection \<open>Substitution on @{term nth}\<close>

lemma comp_substs_nth[simp]:
  "length \<tau>s = length \<sigma>s \<Longrightarrow> i < length \<tau>s \<Longrightarrow> (\<tau>s \<odot>s \<sigma>s) ! i = (\<tau>s ! i) \<odot> (\<sigma>s ! i)"
  by (simp add: comp_substs_def)

lemma subst_atm_list_nth[simp]: "i < length As \<Longrightarrow> (As \<cdot>al \<tau>) ! i = As ! i \<cdot>a \<tau>"
  unfolding subst_atm_list_def using less_Suc_eq_0_disj nth_map by force

lemma subst_atm_mset_list_nth[simp]: "i < length AAs \<Longrightarrow> (AAs \<cdot>aml \<eta>) ! i = (AAs ! i) \<cdot>am \<eta>"
  unfolding subst_atm_mset_list_def by auto

lemma subst_atm_mset_lists_nth[simp]:
  "length AAs = length \<sigma>s \<Longrightarrow> i < length AAs \<Longrightarrow> (AAs \<cdot>\<cdot>aml \<sigma>s) ! i = (AAs ! i) \<cdot>am (\<sigma>s ! i)"
  unfolding subst_atm_mset_lists_def by auto

lemma subst_cls_list_nth[simp]: "i < length Cs \<Longrightarrow> (Cs \<cdot>cl \<tau>) ! i = (Cs ! i) \<cdot> \<tau>"
  unfolding subst_cls_list_def using less_Suc_eq_0_disj nth_map by (induction Cs) auto

lemma subst_cls_lists_nth[simp]:
  "length Cs = length \<sigma>s \<Longrightarrow> i < length Cs \<Longrightarrow> (Cs \<cdot>\<cdot>cl \<sigma>s) ! i = (Cs ! i) \<cdot> (\<sigma>s ! i)"
  unfolding subst_cls_lists_def by auto


subsubsection \<open>Substitution on Various Other Functions\<close>

lemma subst_clss_image[simp]: "image f X \<cdot>cs \<sigma> = {f x \<cdot> \<sigma> | x. x \<in> X}"
  unfolding subst_clss_def by auto

lemma subst_cls_mset_image_mset[simp]: "image_mset f X \<cdot>cm \<sigma> = {# f x \<cdot> \<sigma>. x \<in># X #}"
  unfolding subst_cls_mset_def by auto

lemma mset_subst_atm_list_subst_atm_mset[simp]: "mset (As \<cdot>al \<sigma>) = mset (As) \<cdot>am \<sigma>"
  unfolding subst_atm_list_def subst_atm_mset_def by auto

lemma mset_subst_cls_list_subst_cls_mset: "mset (Cs \<cdot>cl \<sigma>) = (mset Cs) \<cdot>cm \<sigma>"
  unfolding subst_cls_mset_def subst_cls_list_def by auto

lemma sum_list_subst_cls_list_subst_cls[simp]: "sum_list (Cs \<cdot>cl \<eta>) = sum_list Cs \<cdot> \<eta>"
  unfolding subst_cls_list_def by (induction Cs) auto

lemma set_mset_subst_cls_mset_subst_clss: "set_mset (CC \<cdot>cm \<mu>) = (set_mset CC) \<cdot>cs \<mu>"
  by (simp add: subst_cls_mset_def subst_clss_def)

lemma Neg_Melem_subst_atm_subst_cls[simp]: "Neg A \<in># C \<Longrightarrow> Neg (A \<cdot>a \<sigma>) \<in># C \<cdot> \<sigma> "
  by (metis Melem_subst_cls eql_neg_lit_eql_atm)

lemma Pos_Melem_subst_atm_subst_cls[simp]: "Pos A \<in># C \<Longrightarrow> Pos (A \<cdot>a \<sigma>) \<in># C \<cdot> \<sigma> "
  by (metis Melem_subst_cls eql_pos_lit_eql_atm)

lemma in_atms_of_subst[simp]: "B \<in> atms_of C \<Longrightarrow> B \<cdot>a \<sigma> \<in> atms_of (C \<cdot> \<sigma>)"
  by (metis atms_of_subst_atms image_iff subst_atms_def)


subsubsection \<open>Renamings\<close>

lemma is_renaming_id_subst[simp]: "is_renaming id_subst"
  unfolding is_renaming_def by simp

lemma is_renamingD: "is_renaming \<sigma> \<Longrightarrow> (\<forall>A1 A2. A1 \<cdot>a \<sigma> = A2 \<cdot>a \<sigma> \<longleftrightarrow> A1 = A2)"
  by (metis is_renaming_def subst_atm_comp_subst subst_atm_id_subst)

lemma inv_renaming_cancel_r[simp]: "is_renaming r \<Longrightarrow> r \<odot> inv_renaming r = id_subst"
  unfolding inv_renaming_def is_renaming_def by (metis (mono_tags) someI_ex)

lemma inv_renaming_cancel_r_list[simp]:
  "is_renaming_list rs \<Longrightarrow> rs \<odot>s map inv_renaming rs = replicate (length rs) id_subst"
  unfolding is_renaming_list_def by (induction rs) (auto simp add: comp_substs_def)

lemma Nil_comp_substs[simp]: "[] \<odot>s s = []"
  unfolding comp_substs_def by auto

lemma comp_substs_Nil[simp]: "s \<odot>s [] = []"
  unfolding comp_substs_def by auto

lemma is_renaming_idempotent_id_subst: "is_renaming r \<Longrightarrow> r \<odot> r = r \<Longrightarrow> r = id_subst"
  by (metis comp_subst_assoc comp_subst_id_subst inv_renaming_cancel_r)

lemma is_renaming_left_id_subst_right_id_subst:
  "is_renaming r \<Longrightarrow> s \<odot> r = id_subst \<Longrightarrow> r \<odot> s = id_subst"
  by (metis comp_subst_assoc comp_subst_id_subst is_renaming_def)

lemma is_renaming_closure: "is_renaming r1 \<Longrightarrow> is_renaming r2 \<Longrightarrow> is_renaming (r1 \<odot> r2)"
  unfolding is_renaming_def by (metis comp_subst_assoc comp_subst_id_subst)

lemma is_renaming_inv_renaming_cancel_atm[simp]: "is_renaming \<rho> \<Longrightarrow> A \<cdot>a \<rho> \<cdot>a inv_renaming \<rho> = A"
  by (metis inv_renaming_cancel_r subst_atm_comp_subst subst_atm_id_subst)

lemma is_renaming_inv_renaming_cancel_atms[simp]: "is_renaming \<rho> \<Longrightarrow> AA \<cdot>as \<rho> \<cdot>as inv_renaming \<rho> = AA"
  by (metis inv_renaming_cancel_r subst_atms_comp_subst subst_atms_id_subst)

lemma is_renaming_inv_renaming_cancel_atmss[simp]: "is_renaming \<rho> \<Longrightarrow> AAA \<cdot>ass \<rho> \<cdot>ass inv_renaming \<rho> = AAA"
  by (metis inv_renaming_cancel_r subst_atmss_comp_subst subst_atmss_id_subst)

lemma is_renaming_inv_renaming_cancel_atm_list[simp]: "is_renaming \<rho> \<Longrightarrow> As \<cdot>al \<rho> \<cdot>al inv_renaming \<rho> = As"
  by (metis inv_renaming_cancel_r subst_atm_list_comp_subst subst_atm_list_id_subst)

lemma is_renaming_inv_renaming_cancel_atm_mset[simp]: "is_renaming \<rho> \<Longrightarrow> AA \<cdot>am \<rho> \<cdot>am inv_renaming \<rho> = AA"
  by (metis inv_renaming_cancel_r subst_atm_mset_comp_subst subst_atm_mset_id_subst)

lemma is_renaming_inv_renaming_cancel_atm_mset_list[simp]: "is_renaming \<rho> \<Longrightarrow> (AAs \<cdot>aml \<rho>) \<cdot>aml inv_renaming \<rho> = AAs"
  by (metis inv_renaming_cancel_r subst_atm_mset_list_comp_subst subst_atm_mset_list_id_subst)

lemma is_renaming_list_inv_renaming_cancel_atm_mset_lists[simp]:
  "length AAs = length \<rho>s \<Longrightarrow> is_renaming_list \<rho>s \<Longrightarrow> AAs \<cdot>\<cdot>aml \<rho>s \<cdot>\<cdot>aml map inv_renaming \<rho>s = AAs"
  by (metis inv_renaming_cancel_r_list subst_atm_mset_lists_comp_substs subst_atm_mset_lists_id_subst)

lemma is_renaming_inv_renaming_cancel_lit[simp]: "is_renaming \<rho> \<Longrightarrow> (L \<cdot>l \<rho>) \<cdot>l inv_renaming \<rho> = L"
  by (metis inv_renaming_cancel_r subst_lit_comp_subst subst_lit_id_subst)

lemma is_renaming_inv_renaming_cancel_cls[simp]: "is_renaming \<rho> \<Longrightarrow> C  \<cdot> \<rho> \<cdot> inv_renaming \<rho> = C"
  by (metis inv_renaming_cancel_r subst_cls_comp_subst subst_cls_id_subst)

lemma is_renaming_inv_renaming_cancel_clss[simp]: "is_renaming \<rho> \<Longrightarrow> CC \<cdot>cs \<rho> \<cdot>cs inv_renaming \<rho> = CC"
  by (metis inv_renaming_cancel_r subst_clss_id_subst subst_clsscomp_subst)

lemma is_renaming_inv_renaming_cancel_cls_list[simp]: "is_renaming \<rho> \<Longrightarrow> Cs \<cdot>cl \<rho> \<cdot>cl inv_renaming \<rho> = Cs"
  by (metis inv_renaming_cancel_r subst_cls_list_comp_subst subst_cls_list_id_subst)

lemma is_renaming_list_inv_renaming_cancel_cls_list[simp]:
  "length Cs = length \<rho>s \<Longrightarrow> is_renaming_list \<rho>s \<Longrightarrow> Cs \<cdot>\<cdot>cl \<rho>s \<cdot>\<cdot>cl map inv_renaming \<rho>s = Cs"
  by (metis inv_renaming_cancel_r_list subst_cls_lists_comp_substs subst_cls_lists_id_subst)

lemma is_renaming_inv_renaming_cancel_cls_mset[simp]: "is_renaming \<rho> \<Longrightarrow> CC \<cdot>cm \<rho> \<cdot>cm inv_renaming \<rho> = CC"
  by (metis inv_renaming_cancel_r subst_cls_mset_comp_subst subst_cls_mset_id_subst)


subsubsection \<open>Monotonicity\<close>

lemma subst_cls_mono: "set_mset C \<subseteq> set_mset D \<Longrightarrow> set_mset (C \<cdot> \<sigma>) \<subseteq> set_mset (D \<cdot> \<sigma>)"
  by force

lemma subst_cls_mono_mset: "C \<subseteq># D \<Longrightarrow> C \<cdot> \<sigma> \<subseteq># D \<cdot> \<sigma>"
  unfolding subst_clss_def by (metis mset_subset_eq_exists_conv subst_cls_union)

lemma subst_subset_mono: "D \<subset># C \<Longrightarrow> D \<cdot> \<sigma> \<subset># C \<cdot> \<sigma>"
  unfolding subst_cls_def by (simp add: image_mset_subset_mono)


subsubsection \<open>Size after Substitution\<close>

lemma size_subst[simp]: "size (D \<cdot> \<sigma>) = size D"
  unfolding subst_cls_def by auto

lemma subst_atm_list_length[simp]: "length (As \<cdot>al \<sigma>) = length As"
  unfolding subst_atm_list_def by auto

lemma length_subst_atm_mset_list[simp]: "length (AAs \<cdot>aml \<eta>) = length AAs"
  unfolding subst_atm_mset_list_def by auto

lemma subst_atm_mset_lists_length[simp]: "length (AAs \<cdot>\<cdot>aml \<sigma>s) = min (length AAs) (length \<sigma>s)"
  unfolding subst_atm_mset_lists_def by auto

lemma subst_cls_list_length[simp]: "length (Cs \<cdot>cl \<sigma>) = length Cs"
  unfolding subst_cls_list_def by auto

lemma comp_substs_length[simp]: "length (\<tau>s \<odot>s \<sigma>s) = min (length \<tau>s) (length \<sigma>s)"
  unfolding comp_substs_def by auto

lemma subst_cls_lists_length[simp]: "length (Cs \<cdot>\<cdot>cl \<sigma>s) = min (length Cs) (length \<sigma>s)"
  unfolding subst_cls_lists_def by auto


subsubsection \<open>Variable Disjointness\<close>

lemma var_disjoint_clauses:
  assumes "var_disjoint Cs"
  shows "\<forall>\<sigma>s. length \<sigma>s = length Cs \<longrightarrow> (\<exists>\<tau>. Cs \<cdot>\<cdot>cl \<sigma>s = Cs \<cdot>cl \<tau>)"
proof clarify
  fix \<sigma>s :: "'s list"
  assume a: "length \<sigma>s = length Cs"
  then obtain \<tau> where "\<forall>i < length Cs. \<forall>S. S \<subseteq># Cs ! i \<longrightarrow> S \<cdot> \<sigma>s ! i = S \<cdot> \<tau>"
    using assms unfolding var_disjoint_def by blast
  then have "\<forall>i < length Cs. (Cs ! i) \<cdot> \<sigma>s ! i = (Cs ! i) \<cdot> \<tau>"
    by auto
  then have "Cs \<cdot>\<cdot>cl \<sigma>s = Cs \<cdot>cl \<tau>"
    using a by (auto intro: nth_equalityI)
  then show "\<exists>\<tau>. Cs \<cdot>\<cdot>cl \<sigma>s = Cs \<cdot>cl \<tau>"
    by auto
qed


subsubsection \<open>Ground Expressions and Substitutions\<close>

lemma ex_ground_subst: "\<exists>\<sigma>. is_ground_subst \<sigma>"
  using make_ground_subst[of "{#}"]
  by (simp add: is_ground_cls_def)

lemma is_ground_cls_list_Cons[simp]:
  "is_ground_cls_list (C # Cs) = (is_ground_cls C \<and> is_ground_cls_list Cs)"
  unfolding is_ground_cls_list_def by auto


paragraph \<open>Ground union\<close>

lemma is_ground_atms_union[simp]: "is_ground_atms (AA \<union> BB) \<longleftrightarrow> is_ground_atms AA \<and> is_ground_atms BB"
  unfolding is_ground_atms_def by auto

lemma is_ground_atm_mset_union[simp]:
  "is_ground_atm_mset (AA + BB) \<longleftrightarrow> is_ground_atm_mset AA \<and> is_ground_atm_mset BB"
  unfolding is_ground_atm_mset_def by auto

lemma is_ground_cls_union[simp]: "is_ground_cls (C + D) \<longleftrightarrow> is_ground_cls C \<and> is_ground_cls D"
  unfolding is_ground_cls_def by auto

lemma is_ground_clss_union[simp]:
  "is_ground_clss (CC \<union> DD) \<longleftrightarrow> is_ground_clss CC \<and> is_ground_clss DD"
  unfolding is_ground_clss_def by auto

lemma is_ground_cls_list_is_ground_cls_sum_list[simp]:
  "is_ground_cls_list Cs \<Longrightarrow> is_ground_cls (sum_list Cs)"
  by (meson in_mset_sum_list2 is_ground_cls_def is_ground_cls_list_def)


paragraph \<open>Ground mono\<close>

lemma is_ground_cls_mono: "C \<subseteq># D \<Longrightarrow> is_ground_cls D \<Longrightarrow> is_ground_cls C"
  unfolding is_ground_cls_def by (metis set_mset_mono subsetD)

lemma is_ground_clss_mono: "CC \<subseteq> DD \<Longrightarrow> is_ground_clss DD \<Longrightarrow> is_ground_clss CC"
  unfolding is_ground_clss_def by blast

lemma grounding_of_clss_mono: "CC \<subseteq> DD \<Longrightarrow> grounding_of_clss CC \<subseteq> grounding_of_clss DD"
  using grounding_of_clss_def by auto

lemma sum_list_subseteq_mset_is_ground_cls_list[simp]:
  "sum_list Cs \<subseteq># sum_list Ds \<Longrightarrow> is_ground_cls_list Ds \<Longrightarrow> is_ground_cls_list Cs"
  by (meson in_mset_sum_list is_ground_cls_def is_ground_cls_list_is_ground_cls_sum_list
      is_ground_cls_mono is_ground_cls_list_def)


paragraph \<open>Substituting on ground expression preserves ground\<close>

lemma is_ground_comp_subst[simp]: "is_ground_subst \<sigma> \<Longrightarrow> is_ground_subst (\<tau> \<odot> \<sigma>)"
  unfolding is_ground_subst_def is_ground_atm_def by auto

lemma ground_subst_ground_atm[simp]: "is_ground_subst \<sigma> \<Longrightarrow> is_ground_atm (A \<cdot>a \<sigma>)"
  by (simp add: is_ground_subst_def)

lemma ground_subst_ground_lit[simp]: "is_ground_subst \<sigma> \<Longrightarrow> is_ground_lit (L \<cdot>l \<sigma>)"
  unfolding is_ground_lit_def subst_lit_def by (cases L) auto

lemma ground_subst_ground_cls[simp]: "is_ground_subst \<sigma> \<Longrightarrow> is_ground_cls (C \<cdot> \<sigma>)"
  unfolding is_ground_cls_def by auto

lemma ground_subst_ground_clss[simp]: "is_ground_subst \<sigma> \<Longrightarrow> is_ground_clss (CC \<cdot>cs \<sigma>)"
  unfolding is_ground_clss_def subst_clss_def by auto

lemma ground_subst_ground_cls_list[simp]: "is_ground_subst \<sigma> \<Longrightarrow> is_ground_cls_list (Cs \<cdot>cl \<sigma>)"
  unfolding is_ground_cls_list_def subst_cls_list_def by auto

lemma ground_subst_ground_cls_lists[simp]:
  "\<forall>\<sigma> \<in> set \<sigma>s. is_ground_subst \<sigma> \<Longrightarrow> is_ground_cls_list (Cs \<cdot>\<cdot>cl \<sigma>s)"
  unfolding is_ground_cls_list_def subst_cls_lists_def by (auto simp: set_zip)


paragraph \<open>Substituting on ground expression has no effect\<close>

lemma is_ground_subst_atm[simp]: "is_ground_atm A \<Longrightarrow> A \<cdot>a \<sigma> = A"
  unfolding is_ground_atm_def by simp

lemma is_ground_subst_atms[simp]: "is_ground_atms AA \<Longrightarrow> AA \<cdot>as \<sigma> = AA"
  unfolding is_ground_atms_def subst_atms_def image_def by auto

lemma is_ground_subst_atm_mset[simp]: "is_ground_atm_mset AA \<Longrightarrow> AA \<cdot>am \<sigma> = AA"
  unfolding is_ground_atm_mset_def subst_atm_mset_def by auto

lemma is_ground_subst_atm_list[simp]: "is_ground_atm_list As \<Longrightarrow> As \<cdot>al \<sigma> = As"
  unfolding is_ground_atm_list_def subst_atm_list_def by (auto intro: nth_equalityI)

lemma is_ground_subst_atm_list_member[simp]:
  "is_ground_atm_list As \<Longrightarrow> i < length As \<Longrightarrow> As ! i \<cdot>a \<sigma> = As ! i"
  unfolding is_ground_atm_list_def by auto

lemma is_ground_subst_lit[simp]: "is_ground_lit L \<Longrightarrow> L \<cdot>l \<sigma> = L"
  unfolding is_ground_lit_def subst_lit_def by (cases L) simp_all

lemma is_ground_subst_cls[simp]: "is_ground_cls C \<Longrightarrow> C \<cdot> \<sigma> = C"
  unfolding is_ground_cls_def subst_cls_def by simp

lemma is_ground_subst_clss[simp]: "is_ground_clss CC \<Longrightarrow> CC \<cdot>cs \<sigma> = CC"
  unfolding is_ground_clss_def subst_clss_def image_def by auto

lemma is_ground_subst_cls_lists[simp]:
  assumes "length P = length Cs" and "is_ground_cls_list Cs"
  shows "Cs \<cdot>\<cdot>cl P = Cs"
  using assms by (metis is_ground_cls_list_def is_ground_subst_cls min.idem nth_equalityI nth_mem
      subst_cls_lists_nth subst_cls_lists_length)

lemma is_ground_subst_lit_iff: "is_ground_lit L \<longleftrightarrow> (\<forall>\<sigma>. L = L \<cdot>l \<sigma>)"
  using is_ground_atm_def is_ground_lit_def subst_lit_def by (cases L) auto

lemma is_ground_subst_cls_iff: "is_ground_cls C \<longleftrightarrow> (\<forall>\<sigma>. C = C \<cdot> \<sigma>)"
  by (metis ex_ground_subst ground_subst_ground_cls is_ground_subst_cls)


paragraph \<open>Members of ground expressions are ground\<close>

lemma is_ground_cls_as_atms: "is_ground_cls C \<longleftrightarrow> (\<forall>A \<in> atms_of C. is_ground_atm A)"
  by (auto simp: atms_of_def is_ground_cls_def is_ground_lit_def)

lemma is_ground_cls_imp_is_ground_lit: "L \<in># C \<Longrightarrow> is_ground_cls C \<Longrightarrow> is_ground_lit L"
  by (simp add: is_ground_cls_def)

lemma is_ground_cls_imp_is_ground_atm: "A \<in> atms_of C \<Longrightarrow> is_ground_cls C \<Longrightarrow> is_ground_atm A"
  by (simp add: is_ground_cls_as_atms)

lemma is_ground_cls_is_ground_atms_atms_of[simp]: "is_ground_cls C \<Longrightarrow> is_ground_atms (atms_of C)"
  by (simp add: is_ground_cls_imp_is_ground_atm is_ground_atms_def)

lemma grounding_ground: "C \<in> grounding_of_clss M \<Longrightarrow> is_ground_cls C"
  unfolding grounding_of_clss_def grounding_of_cls_def by auto

lemma in_subset_eq_grounding_of_clss_is_ground_cls[simp]:
  "C \<in> CC \<Longrightarrow> CC \<subseteq> grounding_of_clss DD \<Longrightarrow> is_ground_cls C"
  unfolding grounding_of_clss_def grounding_of_cls_def by auto

lemma is_ground_cls_empty[simp]: "is_ground_cls {#}"
  unfolding is_ground_cls_def by simp

lemma grounding_of_cls_ground: "is_ground_cls C \<Longrightarrow> grounding_of_cls C = {C}"
  unfolding grounding_of_cls_def by (simp add: ex_ground_subst)

lemma grounding_of_cls_empty[simp]: "grounding_of_cls {#} = {{#}}"
  by (simp add: grounding_of_cls_ground)


subsubsection \<open>Subsumption\<close>

lemma subsumes_empty_left[simp]: "subsumes {#} C"
  unfolding subsumes_def subst_cls_def by simp

lemma strictly_subsumes_empty_left[simp]: "strictly_subsumes {#} C \<longleftrightarrow> C \<noteq> {#}"
  unfolding strictly_subsumes_def subsumes_def subst_cls_def by simp


subsubsection \<open>Unifiers\<close>

lemma card_le_one_alt: "finite X \<Longrightarrow> card X \<le> 1 \<longleftrightarrow> X = {} \<or> (\<exists>x. X = {x})"
  by (induct rule: finite_induct) auto

lemma is_unifier_subst_atm_eqI:
  assumes "finite AA"
  shows "is_unifier \<sigma> AA \<Longrightarrow> A \<in> AA \<Longrightarrow> B \<in> AA \<Longrightarrow> A \<cdot>a \<sigma> = B \<cdot>a \<sigma>"
  unfolding is_unifier_def subst_atms_def card_le_one_alt[OF finite_imageI[OF assms]]
  by (metis equals0D imageI insert_iff)

lemma is_unifier_alt:
  assumes "finite AA"
  shows "is_unifier \<sigma> AA \<longleftrightarrow> (\<forall>A \<in> AA. \<forall>B \<in> AA. A \<cdot>a \<sigma> = B \<cdot>a \<sigma>)"
  unfolding is_unifier_def subst_atms_def card_le_one_alt[OF finite_imageI[OF assms(1)]]
  by (rule iffI, metis empty_iff insert_iff insert_image, blast)

lemma is_unifiers_subst_atm_eqI:
  assumes "finite AA" "is_unifiers \<sigma> AAA" "AA \<in> AAA" "A \<in> AA" "B \<in> AA"
  shows "A \<cdot>a \<sigma> = B \<cdot>a \<sigma>"
  by (metis assms is_unifiers_def is_unifier_subst_atm_eqI)

theorem is_unifiers_comp:
  "is_unifiers \<sigma> (set_mset ` set (map2 add_mset As Bs) \<cdot>ass \<eta>) \<longleftrightarrow>
   is_unifiers (\<eta> \<odot> \<sigma>) (set_mset ` set (map2 add_mset As Bs))"
  unfolding is_unifiers_def is_unifier_def subst_atmss_def by auto


subsubsection \<open>Most General Unifier\<close>

lemma is_mgu_is_unifiers: "is_mgu \<sigma> AAA \<Longrightarrow> is_unifiers \<sigma> AAA"
  using is_mgu_def by blast

lemma is_mgu_is_most_general: "is_mgu \<sigma> AAA \<Longrightarrow> is_unifiers \<tau> AAA \<Longrightarrow> \<exists>\<gamma>. \<tau> = \<sigma> \<odot> \<gamma>"
  using is_mgu_def by blast

lemma is_unifiers_is_unifier: "is_unifiers \<sigma> AAA \<Longrightarrow> AA \<in> AAA \<Longrightarrow> is_unifier \<sigma> AA"
  using is_unifiers_def by simp


subsubsection \<open>Generalization and Subsumption\<close>

lemma variants_iff_subsumes: "variants C D \<longleftrightarrow> subsumes C D \<and> subsumes D C"
proof
  assume "variants C D"
  then show "subsumes C D \<and> subsumes D C"
    unfolding variants_def generalizes_cls_def subsumes_def by (metis subset_mset.order.refl)
next
  assume sub: "subsumes C D \<and> subsumes D C"
  then have "size C = size D"
    unfolding subsumes_def by (metis antisym size_mset_mono size_subst)
  then show "variants C D"
    using sub unfolding subsumes_def variants_def generalizes_cls_def
    by (metis leD mset_subset_size size_mset_mono size_subst
        subset_mset.order.not_eq_order_implies_strict)
qed

lemma wf_strictly_generalizes_cls: "wfP strictly_generalizes_cls"
proof -
  {
    assume "\<exists>C_at. \<forall>i. strictly_generalizes_cls (C_at (Suc i)) (C_at i)"
    then obtain C_at :: "nat \<Rightarrow> 'a clause" where
      sg_C: "\<And>i. strictly_generalizes_cls (C_at (Suc i)) (C_at i)"
      by blast

    define n :: nat where
      "n = size (C_at 0)"

    have sz_C: "size (C_at i) = n" for i
    proof (induct i)
      case (Suc i)
      then show ?case
        using sg_C[of i] unfolding strictly_generalizes_cls_def generalizes_cls_def subst_cls_def
        by (metis size_image_mset)
    qed (simp add: n_def)

    obtain \<sigma>_at :: "nat \<Rightarrow> 's" where
      C_\<sigma>: "\<And>i. image_mset (\<lambda>L. L \<cdot>l \<sigma>_at i) (C_at (Suc i)) = C_at i"
      using sg_C[unfolded strictly_generalizes_cls_def generalizes_cls_def subst_cls_def] by metis

    define Ls_at :: "nat \<Rightarrow> 'a literal list" where
      "Ls_at = rec_nat (SOME Ls. mset Ls = C_at 0)
         (\<lambda>i Lsi. SOME Ls. mset Ls = C_at (Suc i) \<and> map (\<lambda>L. L \<cdot>l \<sigma>_at i) Ls = Lsi)"

    have
      Ls_at_0: "Ls_at 0 = (SOME Ls. mset Ls = C_at 0)" and
      Ls_at_Suc: "\<And>i. Ls_at (Suc i) =
        (SOME Ls. mset Ls = C_at (Suc i) \<and> map (\<lambda>L. L \<cdot>l \<sigma>_at i) Ls = Ls_at i)"
      unfolding Ls_at_def by simp+

    have mset_Lt_at_0: "mset (Ls_at 0) = C_at 0"
      unfolding Ls_at_0 by (rule someI_ex) (metis list_of_mset_exi)

    have "mset (Ls_at (Suc i)) = C_at (Suc i) \<and> map (\<lambda>L. L \<cdot>l \<sigma>_at i) (Ls_at (Suc i)) = Ls_at i"
      for i
    proof (induct i)
      case 0
      then show ?case
        by (simp add: Ls_at_Suc, rule someI_ex,
            metis C_\<sigma> image_mset_of_subset_list mset_Lt_at_0)
    next
      case Suc
      then show ?case
        by (subst (1 2) Ls_at_Suc) (rule someI_ex, metis C_\<sigma> image_mset_of_subset_list)
    qed
    note mset_Ls = this[THEN conjunct1] and Ls_\<sigma> = this[THEN conjunct2]

    have len_Ls: "\<And>i. length (Ls_at i) = n"
      by (metis mset_Ls mset_Lt_at_0 not0_implies_Suc size_mset sz_C)

    have is_pos_Ls: "\<And>i j. j < n \<Longrightarrow> is_pos (Ls_at (Suc i) ! j) \<longleftrightarrow> is_pos (Ls_at i ! j)"
      using Ls_\<sigma> len_Ls by (metis literal.map_disc_iff nth_map subst_lit_def)

    have Ls_\<tau>_strict_lit: "\<And>i \<tau>. map (\<lambda>L. L \<cdot>l \<tau>) (Ls_at i) \<noteq> Ls_at (Suc i)"
      by (metis C_\<sigma> mset_Ls Ls_\<sigma> mset_map sg_C generalizes_cls_def strictly_generalizes_cls_def
          subst_cls_def)

    have Ls_\<tau>_strict_tm:
      "map ((\<lambda>t. t \<cdot>a \<tau>) \<circ> atm_of) (Ls_at i) \<noteq> map atm_of (Ls_at (Suc i))" for i \<tau>
    proof -
      obtain j :: nat where
        j_lt: "j < n" and
        j_\<tau>: "Ls_at i ! j \<cdot>l \<tau> \<noteq> Ls_at (Suc i) ! j"
        using Ls_\<tau>_strict_lit[of \<tau> i] len_Ls
        by (metis (no_types, lifting) length_map list_eq_iff_nth_eq nth_map)

      have "atm_of (Ls_at i ! j) \<cdot>a \<tau> \<noteq> atm_of (Ls_at (Suc i) ! j)"
        using j_\<tau> is_pos_Ls[OF j_lt]
        by (metis (mono_guards) literal.expand literal.map_disc_iff literal.map_sel subst_lit_def)
      then show ?thesis
        using j_lt len_Ls by (metis nth_map o_apply)
    qed

    define tm_at :: "nat \<Rightarrow> 'a" where
      "\<And>i. tm_at i = atm_of_atms (map atm_of (Ls_at i))"

    have "\<And>i. generalizes_atm (tm_at (Suc i)) (tm_at i)"
      unfolding tm_at_def generalizes_atm_def atm_of_atms_subst
      using Ls_\<sigma>[THEN arg_cong, of "map atm_of"] by (auto simp: comp_def)
    moreover have "\<And>i. \<not> generalizes_atm (tm_at i) (tm_at (Suc i))"
      unfolding tm_at_def generalizes_atm_def atm_of_atms_subst by (simp add: Ls_\<tau>_strict_tm)
    ultimately have "\<And>i. strictly_generalizes_atm (tm_at (Suc i)) (tm_at i)"
      unfolding strictly_generalizes_atm_def by blast
    then have False
      using wf_strictly_generalizes_atm[unfolded wfP_def wf_iff_no_infinite_down_chain] by blast
  }
  then show "wfP (strictly_generalizes_cls :: 'a clause \<Rightarrow> _ \<Rightarrow> _)"
    unfolding wfP_def by (blast intro: wf_iff_no_infinite_down_chain[THEN iffD2])
qed

lemma strict_subset_subst_strictly_subsumes:
  assumes c\<eta>_sub: "C \<cdot> \<eta> \<subset># D"
  shows "strictly_subsumes C D"
  by (metis c\<eta>_sub leD mset_subset_size size_mset_mono size_subst strictly_subsumes_def
      subset_mset.dual_order.strict_implies_order substitution_ops.subsumes_def)

lemma subsumes_trans: "subsumes C D \<Longrightarrow> subsumes D E \<Longrightarrow> subsumes C E"
  unfolding subsumes_def
  by (metis (no_types) subset_mset.order.trans subst_cls_comp_subst subst_cls_mono_mset)

lemma subset_strictly_subsumes: "C \<subset># D \<Longrightarrow> strictly_subsumes C D"
  using strict_subset_subst_strictly_subsumes[of C id_subst] by auto

lemma strictly_subsumes_neq: "strictly_subsumes D' D \<Longrightarrow> D' \<noteq> D \<cdot> \<sigma>"
  unfolding strictly_subsumes_def subsumes_def by blast

lemma strictly_subsumes_has_minimum:
  assumes "CC \<noteq> {}"
  shows "\<exists>C \<in> CC. \<forall>D \<in> CC. \<not> strictly_subsumes D C"
proof (rule ccontr)
  assume "\<not> (\<exists>C \<in> CC. \<forall>D\<in>CC. \<not> strictly_subsumes D C)"
  then have "\<forall>C \<in> CC. \<exists>D \<in> CC. strictly_subsumes D C"
    by blast
  then obtain f where
    f_p: "\<forall>C \<in> CC. f C \<in> CC \<and> strictly_subsumes (f C) C"
    by metis
  from assms obtain C where
    C_p: "C \<in> CC"
    by auto

  define c :: "nat \<Rightarrow> 'a clause" where
    "\<And>n. c n = (f ^^ n) C"

  have incc: "c i \<in> CC" for i
    by (induction i) (auto simp: c_def f_p C_p)
  have ps: "\<forall>i. strictly_subsumes (c (Suc i)) (c i)"
    using incc f_p unfolding c_def by auto
  have "\<forall>i. size (c i) \<ge> size (c (Suc i))"
    using ps unfolding strictly_subsumes_def subsumes_def by (metis size_mset_mono size_subst)
  then have lte: "\<forall>i. (size \<circ> c) i \<ge> (size \<circ> c) (Suc i)"
    unfolding comp_def .
  then have "\<exists>l. \<forall>l' \<ge> l. size (c l') = size (c (Suc l'))"
    using f_Suc_decr_eventually_const comp_def by auto
  then obtain l where
    l_p: "\<forall>l' \<ge> l. size (c l') = size (c (Suc l'))"
    by metis
  then have "\<forall>l' \<ge> l. strictly_generalizes_cls (c (Suc l')) (c l')"
    using ps unfolding strictly_generalizes_cls_def generalizes_cls_def
    by (metis size_subst less_irrefl strictly_subsumes_def mset_subset_size
        subset_mset_def subsumes_def strictly_subsumes_neq)
  then have "\<forall>i. strictly_generalizes_cls (c (Suc i + l)) (c (i + l))"
    unfolding strictly_generalizes_cls_def generalizes_cls_def by auto
  then have "\<exists>f. \<forall>i. strictly_generalizes_cls (f (Suc i)) (f i)"
    by (rule exI[of _ "\<lambda>x. c (x + l)"])
  then show False
    using wf_strictly_generalizes_cls
      wf_iff_no_infinite_down_chain[of "{(x, y). strictly_generalizes_cls x y}"]
    unfolding wfP_def by auto
qed

end


subsection \<open>Most General Unifiers\<close>

locale mgu = substitution subst_atm id_subst comp_subst renamings_apart atm_of_atms
  for
    subst_atm :: "'a \<Rightarrow> 's \<Rightarrow> 'a" and
    id_subst :: 's and
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's" and
    atm_of_atms :: "'a list \<Rightarrow> 'a" and
    renamings_apart :: "'a literal multiset list \<Rightarrow> 's list" +
  fixes
    mgu :: "'a set set \<Rightarrow> 's option"
  assumes
    mgu_sound: "finite AAA \<Longrightarrow> (\<forall>AA \<in> AAA. finite AA) \<Longrightarrow> mgu AAA = Some \<sigma> \<Longrightarrow> is_mgu \<sigma> AAA" and
    mgu_complete:
      "finite AAA \<Longrightarrow> (\<forall>AA \<in> AAA. finite AA) \<Longrightarrow> is_unifiers \<sigma> AAA \<Longrightarrow> \<exists>\<tau>. mgu AAA = Some \<tau>"
begin

lemmas is_unifiers_mgu = mgu_sound[unfolded is_mgu_def, THEN conjunct1]
lemmas is_mgu_most_general = mgu_sound[unfolded is_mgu_def, THEN conjunct2]

lemma mgu_unifier:
  assumes
    aslen: "length As = n" and
    aaslen: "length AAs = n" and
    mgu: "Some \<sigma> = mgu (set_mset ` set (map2 add_mset As AAs))" and
    i_lt: "i < n" and
    a_in: "A \<in># AAs ! i"
  shows "A \<cdot>a \<sigma> = As ! i \<cdot>a \<sigma>"
proof -
  from mgu have "is_mgu \<sigma> (set_mset ` set (map2 add_mset As AAs))"
    using mgu_sound by auto
  then have "is_unifiers \<sigma> (set_mset ` set (map2 add_mset As AAs))"
    using is_mgu_is_unifiers by auto
  then have "is_unifier \<sigma> (set_mset (add_mset (As ! i) (AAs ! i)))"
    using i_lt aslen aaslen unfolding is_unifiers_def is_unifier_def
    by simp (metis length_zip min.idem nth_mem nth_zip prod.case set_mset_add_mset_insert)
  then show ?thesis
    using aslen aaslen a_in is_unifier_subst_atm_eqI
    by (metis finite_set_mset insertCI set_mset_add_mset_insert)
qed

end

end
