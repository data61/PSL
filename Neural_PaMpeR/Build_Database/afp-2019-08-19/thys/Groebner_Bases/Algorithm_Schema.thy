(* Author: Alexander Maletzky *)

section \<open>A General Algorithm Schema for Computing Gr\"obner Bases\<close>

theory Algorithm_Schema
  imports General Groebner_Bases
begin

text \<open>This theory formalizes a general algorithm schema for computing Gr\"obner bases, generalizing
  Buchberger's original critical-pair/completion algorithm. The algorithm schema depends on several
  functional parameters that can be instantiated by a variety of concrete functions. Possible instances
  yield Buchberger's algorithm, Faug\`ere's F4 algorithm, and (as far as we can tell) even his F5
  algorithm.\<close>

subsection \<open>@{term processed}\<close>

definition minus_pairs (infixl "-\<^sub>p" 65) where "minus_pairs A B = A - (B \<union> prod.swap ` B)"
definition Int_pairs (infixl "\<inter>\<^sub>p" 65) where "Int_pairs A B = A \<inter> (B \<union> prod.swap ` B)"
definition in_pair (infix "\<in>\<^sub>p" 50) where "in_pair p A \<longleftrightarrow> (p \<in> A \<union> prod.swap ` A)"
definition subset_pairs (infix "\<subseteq>\<^sub>p" 50) where "subset_pairs A B \<longleftrightarrow> (\<forall>x. x \<in>\<^sub>p A \<longrightarrow> x \<in>\<^sub>p B)"
abbreviation not_in_pair (infix "\<notin>\<^sub>p" 50) where "not_in_pair p A \<equiv> \<not> p \<in>\<^sub>p A"

lemma in_pair_alt: "p \<in>\<^sub>p A \<longleftrightarrow> (p \<in> A \<or> prod.swap p \<in> A)"
  by (metis (mono_tags, lifting) UnCI UnE image_iff in_pair_def prod.collapse swap_simp)

lemma in_pair_iff: "(a, b) \<in>\<^sub>p A \<longleftrightarrow> ((a, b) \<in> A \<or> (b, a) \<in> A)"
  by (simp add: in_pair_alt)

lemma in_pair_minus_pairs [simp]: "p \<in>\<^sub>p A -\<^sub>p B \<longleftrightarrow> (p \<in>\<^sub>p A \<and> p \<notin>\<^sub>p B)"
  by (metis Diff_iff in_pair_def in_pair_iff minus_pairs_def prod.collapse)

lemma in_minus_pairs [simp]: "p \<in> A -\<^sub>p B \<longleftrightarrow> (p \<in> A \<and> p \<notin>\<^sub>p B)"
  by (metis Diff_iff in_pair_def minus_pairs_def)

lemma in_pair_Int_pairs [simp]: "p \<in>\<^sub>p A \<inter>\<^sub>p B \<longleftrightarrow> (p \<in>\<^sub>p A \<and> p \<in>\<^sub>p B)"
  by (metis (no_types, hide_lams) Int_iff Int_pairs_def in_pair_alt in_pair_def old.prod.exhaust swap_simp)

lemma in_pair_Un [simp]: "p \<in>\<^sub>p A \<union> B \<longleftrightarrow> (p \<in>\<^sub>p A \<or> p \<in>\<^sub>p B)"
  by (metis (mono_tags, lifting) UnE UnI1 UnI2 image_Un in_pair_def)

lemma in_pair_trans [trans]:
  assumes "p \<in>\<^sub>p A" and "A \<subseteq> B"
  shows "p \<in>\<^sub>p B"
  using assms by (auto simp: in_pair_def)

lemma in_pair_same [simp]: "p \<in>\<^sub>p A \<times> A \<longleftrightarrow> p \<in> A \<times> A"
  by (auto simp: in_pair_def swap_def)

lemma subset_pairsI [intro]:
  assumes "\<And>x. x \<in>\<^sub>p A \<Longrightarrow> x \<in>\<^sub>p B"
  shows "A \<subseteq>\<^sub>p B"
  unfolding subset_pairs_def using assms by blast

lemma subset_pairsD [trans]:
  assumes "x \<in>\<^sub>p A" and "A \<subseteq>\<^sub>p B"
  shows "x \<in>\<^sub>p B"
  using assms unfolding subset_pairs_def by blast

definition processed :: "('a \<times> 'a) \<Rightarrow> 'a list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> bool"
  where "processed p xs ps \<longleftrightarrow> p \<in> set xs \<times> set xs \<and> p \<notin>\<^sub>p set ps"

lemma processed_alt:
  "processed (a, b) xs ps \<longleftrightarrow> ((a \<in> set xs) \<and> (b \<in> set xs) \<and> (a, b) \<notin>\<^sub>p set ps)"
  unfolding processed_def by auto

lemma processedI:
  assumes "a \<in> set xs" and "b \<in> set xs" and "(a, b) \<notin>\<^sub>p set ps"
  shows "processed (a, b) xs ps"
  unfolding processed_alt using assms by simp

lemma processedD1:
  assumes "processed (a, b) xs ps"
  shows "a \<in> set xs"
  using assms by (simp add: processed_alt)

lemma processedD2:
  assumes "processed (a, b) xs ps"
  shows "b \<in> set xs"
  using assms by (simp add: processed_alt)

lemma processedD3:
  assumes "processed (a, b) xs ps"
  shows "(a, b) \<notin>\<^sub>p set ps"
  using assms by (simp add: processed_alt)

lemma processed_Nil: "processed (a, b) xs [] \<longleftrightarrow> (a \<in> set xs \<and> b \<in> set xs)"
  by (simp add: processed_alt in_pair_iff)

lemma processed_Cons:
  assumes "processed (a, b) xs ps"
    and a1: "a = p \<Longrightarrow> b = q \<Longrightarrow> thesis"
    and a2: "a = q \<Longrightarrow> b = p \<Longrightarrow> thesis"
    and a3: "processed (a, b) xs ((p, q) # ps) \<Longrightarrow> thesis"
  shows thesis
proof -
  from assms(1) have "a \<in> set xs" and "b \<in> set xs" and "(a, b) \<notin>\<^sub>p set ps"
    by (simp_all add: processed_alt)
  show ?thesis
  proof (cases "(a, b) = (p, q)")
    case True
    hence "a = p" and "b = q" by simp_all
    thus ?thesis by (rule a1)
  next
    case False
    with \<open>(a, b) \<notin>\<^sub>p set ps\<close> have *: "(a, b) \<notin> set ((p, q) # ps)" by (auto simp: in_pair_iff)
    show ?thesis
    proof (cases "(b, a) = (p, q)")
      case True
      hence "a = q" and "b = p" by simp_all
      thus ?thesis by (rule a2)
    next
      case False
      with \<open>(a, b) \<notin>\<^sub>p set ps\<close> have "(b, a) \<notin> set ((p, q) # ps)" by (auto simp: in_pair_iff)
      with * have "(a, b) \<notin>\<^sub>p set ((p, q) # ps)" by (simp add: in_pair_iff)
      with \<open>a \<in> set xs\<close> \<open>b \<in> set xs\<close> have "processed (a, b) xs ((p, q) # ps)"
        by (rule processedI)
      thus ?thesis by (rule a3)
    qed
  qed
qed

lemma processed_minus:
  assumes "processed (a, b) xs (ps -- qs)"
    and a1: "(a, b) \<in>\<^sub>p set qs \<Longrightarrow> thesis"
    and a2: "processed (a, b) xs ps \<Longrightarrow> thesis"
  shows thesis
proof -
  from assms(1) have "a \<in> set xs" and "b \<in> set xs" and "(a, b) \<notin>\<^sub>p set (ps -- qs)"
    by (simp_all add: processed_alt)
  show ?thesis
  proof (cases "(a, b) \<in>\<^sub>p set qs")
    case True
    thus ?thesis by (rule a1)
  next
    case False
    with \<open>(a, b) \<notin>\<^sub>p set (ps -- qs)\<close> have "(a, b) \<notin>\<^sub>p set ps"
      by (auto simp: set_diff_list in_pair_iff)
    with \<open>a \<in> set xs\<close> \<open>b \<in> set xs\<close> have "processed (a, b) xs ps"
      by (rule processedI)
    thus ?thesis by (rule a2)
  qed
qed

subsection \<open>Algorithm Schema\<close>

subsubsection \<open>\<open>const_lt_component\<close>\<close>

context ordered_term
begin

definition const_lt_component :: "('t \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> 'k option"
  where "const_lt_component p =
                      (let v = lt p in if pp_of_term v = 0 then Some (component_of_term v) else None)"

lemma const_lt_component_SomeI:
  assumes "lp p = 0" and "component_of_term (lt p) = cmp"
  shows "const_lt_component p = Some cmp"
  using assms by (simp add: const_lt_component_def)

lemma const_lt_component_SomeD1:
  assumes "const_lt_component p = Some cmp"
  shows "lp p = 0"
  using assms by (simp add: const_lt_component_def Let_def split: if_split_asm)

lemma const_lt_component_SomeD2:
  assumes "const_lt_component p = Some cmp"
  shows "component_of_term (lt p) = cmp"
  using assms by (simp add: const_lt_component_def Let_def split: if_split_asm)

lemma const_lt_component_subset:
  "const_lt_component ` (B - {0}) - {None} \<subseteq> Some ` component_of_term ` Keys B"
proof
  fix k
  assume "k \<in> const_lt_component ` (B - {0}) - {None}"
  hence "k \<in> const_lt_component ` (B - {0})" and "k \<noteq> None" by simp_all
  from this(1) obtain p where "p \<in> B - {0}" and "k = const_lt_component p" ..
  moreover from \<open>k \<noteq> None\<close> obtain k' where "k = Some k'" by blast
  ultimately have "const_lt_component p = Some k'" and "p \<in> B" and "p \<noteq> 0" by simp_all
  from this(1) have "component_of_term (lt p) = k'" by (rule const_lt_component_SomeD2)
  moreover have "lt p \<in> Keys B" by (rule in_KeysI, rule lt_in_keys, fact+)
  ultimately have "k' \<in> component_of_term ` Keys B" by fastforce
  thus "k \<in> Some ` component_of_term ` Keys B" by (simp add: \<open>k = Some k'\<close>)
qed

corollary card_const_lt_component_le:
  assumes "finite B"
  shows "card (const_lt_component ` (B - {0}) - {None}) \<le> card (component_of_term ` Keys B)"
proof (rule surj_card_le)
  show "finite (component_of_term ` Keys B)"
    by (intro finite_imageI finite_Keys, fact)
next
  show "const_lt_component ` (B - {0}) - {None} \<subseteq> Some ` component_of_term ` Keys B"
    by (fact const_lt_component_subset)
qed

end (* ordered_term *)

subsubsection \<open>Type synonyms\<close>

type_synonym ('a, 'b, 'c) pdata' = "('a \<Rightarrow>\<^sub>0 'b) \<times> 'c"
type_synonym ('a, 'b, 'c) pdata = "('a \<Rightarrow>\<^sub>0 'b) \<times> nat \<times> 'c"
type_synonym ('a, 'b, 'c) pdata_pair = "('a, 'b, 'c) pdata \<times> ('a, 'b, 'c) pdata"
type_synonym ('a, 'b, 'c, 'd) selT = "('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow>
                                    ('a, 'b, 'c) pdata_pair list \<Rightarrow> nat \<times> 'd \<Rightarrow> ('a, 'b, 'c) pdata_pair list"
type_synonym ('a, 'b, 'c, 'd) complT = "('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow>
                                    ('a, 'b, 'c) pdata_pair list \<Rightarrow> ('a, 'b, 'c) pdata_pair list \<Rightarrow>
                                    nat \<times> 'd \<Rightarrow> (('a, 'b, 'c) pdata' list \<times> 'd)"
type_synonym ('a, 'b, 'c, 'd) apT = "('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow>
                                    ('a, 'b, 'c) pdata_pair list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow> nat \<times> 'd \<Rightarrow>
                                    ('a, 'b, 'c) pdata_pair list"
type_synonym ('a, 'b, 'c, 'd) abT = "('a, 'b, 'c) pdata list \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow>
                                    ('a, 'b, 'c) pdata list \<Rightarrow> nat \<times> 'd \<Rightarrow> ('a, 'b, 'c) pdata list"

subsubsection \<open>Specification of the @{emph \<open>selector\<close>} parameter\<close>

definition sel_spec :: "('a, 'b, 'c, 'd) selT \<Rightarrow> bool"
  where "sel_spec sel \<longleftrightarrow>
          (\<forall>gs bs ps data. ps \<noteq> [] \<longrightarrow> (sel gs bs ps data \<noteq> [] \<and> set (sel gs bs ps data) \<subseteq> set ps))"

lemma sel_specI:
  assumes "\<And>gs bs ps data. ps \<noteq> [] \<Longrightarrow> (sel gs bs ps data \<noteq> [] \<and> set (sel gs bs ps data) \<subseteq> set ps)"
  shows "sel_spec sel"
  unfolding sel_spec_def using assms by blast

lemma sel_specD1:
  assumes "sel_spec sel" and "ps \<noteq> []"
  shows "sel gs bs ps data \<noteq> []"
  using assms unfolding sel_spec_def by blast

lemma sel_specD2:
  assumes "sel_spec sel" and "ps \<noteq> []"
  shows "set (sel gs bs ps data) \<subseteq> set ps"
  using assms unfolding sel_spec_def by blast

subsubsection \<open>Specification of the @{emph \<open>add-basis\<close>} parameter\<close>

definition ab_spec :: "('a, 'b, 'c, 'd) abT \<Rightarrow> bool"
  where "ab_spec ab \<longleftrightarrow>
              (\<forall>gs bs ns data. ns \<noteq> [] \<longrightarrow> set (ab gs bs ns data) = set bs \<union> set ns) \<and>
              (\<forall>gs bs data. ab gs bs [] data = bs)"

lemma ab_specI:
  assumes "\<And>gs bs ns data. ns \<noteq> [] \<Longrightarrow> set (ab gs bs ns data) = set bs \<union> set ns"
    and "\<And>gs bs data. ab gs bs [] data = bs"
  shows "ab_spec ab"
  unfolding ab_spec_def using assms by blast

lemma ab_specD1:
  assumes "ab_spec ab"
  shows "set (ab gs bs ns data) = set bs \<union> set ns"
  using assms unfolding ab_spec_def by (metis empty_set sup_bot.right_neutral)

lemma ab_specD2:
  assumes "ab_spec ab"
  shows "ab gs bs [] data = bs"
  using assms unfolding ab_spec_def by blast

subsubsection \<open>Specification of the @{emph \<open>add-pairs\<close>} parameter\<close>

definition unique_idx :: "('t, 'b, 'c) pdata list \<Rightarrow> (nat \<times> 'd) \<Rightarrow> bool"
  where "unique_idx bs data \<longleftrightarrow>
                         (\<forall>f\<in>set bs. \<forall>g\<in>set bs. fst (snd f) = fst (snd g) \<longrightarrow> f = g) \<and>
                         (\<forall>f\<in>set bs. fst (snd f) < fst data)"

lemma unique_idxI:
  assumes "\<And>f g. f \<in> set bs \<Longrightarrow> g \<in> set bs \<Longrightarrow> fst (snd f) = fst (snd g) \<Longrightarrow> f = g"
    and "\<And>f. f \<in> set bs \<Longrightarrow> fst (snd f) < fst data"
  shows "unique_idx bs data"
  unfolding unique_idx_def using assms by blast

lemma unique_idxD1:
  assumes "unique_idx bs data" and "f \<in> set bs" and "g \<in> set bs" and "fst (snd f) = fst (snd g)"
  shows "f = g"
  using assms unfolding unique_idx_def by blast

lemma unique_idxD2:
  assumes "unique_idx bs data" and "f \<in> set bs"
  shows "fst (snd f) < fst data"
  using assms unfolding unique_idx_def by blast

lemma unique_idx_Nil: "unique_idx [] data"
  by (simp add: unique_idx_def)

lemma unique_idx_subset:
  assumes "unique_idx bs data" and "set bs' \<subseteq> set bs"
  shows "unique_idx bs' data"
proof (rule unique_idxI)
  fix f g
  assume "f \<in> set bs'" and "g \<in> set bs'"
  with assms have "unique_idx bs data" and "f \<in> set bs" and "g \<in> set bs" by auto
  moreover assume "fst (snd f) = fst (snd g)"
  ultimately show "f = g" by (rule unique_idxD1)
next
  fix f
  assume "f \<in> set bs'"
  with assms(2) have "f \<in> set bs" by auto
  with assms(1) show "fst (snd f) < fst data" by (rule unique_idxD2)
qed

context gd_term
begin

definition ap_spec :: "('t, 'b::field, 'c, 'd) apT \<Rightarrow> bool"
  where "ap_spec ap \<longleftrightarrow> (\<forall>gs bs ps hs data.
      set (ap gs bs ps hs data) \<subseteq> set ps \<union> (set hs \<times> (set gs \<union> set bs \<union> set hs)) \<and>
      (\<forall>B d m. \<forall>h\<in>set hs. \<forall>g\<in>set gs \<union> set bs \<union> set hs. dickson_grading d \<longrightarrow>
        set gs \<union> set bs \<union> set hs \<subseteq> B \<longrightarrow> fst ` B \<subseteq> dgrad_p_set d m \<longrightarrow>
        set ps \<subseteq> set bs \<times> (set gs \<union> set bs) \<longrightarrow> unique_idx (gs @ bs @ hs) data \<longrightarrow>
        is_Groebner_basis (fst ` set gs) \<longrightarrow> h \<noteq> g \<longrightarrow> fst h \<noteq> 0 \<longrightarrow> fst g \<noteq> 0 \<longrightarrow>
        (\<forall>a b. (a, b) \<in>\<^sub>p set (ap gs bs ps hs data) \<longrightarrow> fst a \<noteq> 0 \<longrightarrow> fst b \<noteq> 0 \<longrightarrow>
               crit_pair_cbelow_on d m (fst ` B) (fst a) (fst b)) \<longrightarrow>
        (\<forall>a b. a \<in> set gs \<union> set bs \<longrightarrow> b \<in> set gs \<union> set bs \<longrightarrow> fst a \<noteq> 0 \<longrightarrow> fst b \<noteq> 0 \<longrightarrow>
               crit_pair_cbelow_on d m (fst ` B) (fst a) (fst b)) \<longrightarrow>
        crit_pair_cbelow_on d m (fst ` B) (fst h) (fst g)) \<and>
      (\<forall>B d m. \<forall>h g. dickson_grading d \<longrightarrow>
        set gs \<union> set bs \<union> set hs \<subseteq> B \<longrightarrow> fst ` B \<subseteq> dgrad_p_set d m \<longrightarrow>
        set ps \<subseteq> set bs \<times> (set gs \<union> set bs) \<longrightarrow> (set gs \<union> set bs) \<inter> set hs = {} \<longrightarrow>
        unique_idx (gs @ bs @ hs) data \<longrightarrow> is_Groebner_basis (fst ` set gs) \<longrightarrow>
        h \<noteq> g \<longrightarrow> fst h \<noteq> 0 \<longrightarrow> fst g \<noteq> 0 \<longrightarrow>
        (h, g) \<in> set ps -\<^sub>p set (ap gs bs ps hs data) \<longrightarrow>
        (\<forall>a b. (a, b) \<in>\<^sub>p set (ap gs bs ps hs data) \<longrightarrow> (a, b) \<in>\<^sub>p set hs \<times> (set gs \<union> set bs \<union> set hs) \<longrightarrow>
               fst a \<noteq> 0 \<longrightarrow> fst b \<noteq> 0 \<longrightarrow> crit_pair_cbelow_on d m (fst ` B) (fst a) (fst b)) \<longrightarrow>
        crit_pair_cbelow_on d m (fst ` B) (fst h) (fst g)))"

text \<open>Informally, \<open>ap_spec ap\<close> means that, for suitable arguments \<open>gs\<close>, \<open>bs\<close>, \<open>ps\<close> and \<open>hs\<close>,
  the value of \<open>ap gs bs ps hs\<close> is a list of pairs \<open>ps'\<close> such that for every element \<open>(a, b)\<close> missing in \<open>ps'\<close>
  there exists a set of pairs \<open>C\<close> by reference to which \<open>(a, b)\<close> can be discarded, i.\,e. as soon as
  all critical pairs of the elements in \<open>C\<close> can be connected below some set \<open>B\<close>, the same is true for
  the critical pair of \<open>(a, b)\<close>.\<close>

lemma ap_specI:
  assumes "\<And>gs bs ps hs data. set (ap gs bs ps hs data) \<subseteq> set ps \<union> (set hs \<times> (set gs \<union> set bs \<union> set hs))"
  assumes "\<And>gs bs ps hs data B d m h g. dickson_grading d \<Longrightarrow>
              set gs \<union> set bs \<union> set hs \<subseteq> B \<Longrightarrow> fst ` B \<subseteq> dgrad_p_set d m \<Longrightarrow>
              h \<in> set hs \<Longrightarrow> g \<in> set gs \<union> set bs \<union> set hs \<Longrightarrow>
              set ps \<subseteq> set bs \<times> (set gs \<union> set bs) \<Longrightarrow> unique_idx (gs @ bs @ hs) data \<Longrightarrow>
              is_Groebner_basis (fst ` set gs) \<Longrightarrow> h \<noteq> g \<Longrightarrow> fst h \<noteq> 0 \<Longrightarrow> fst g \<noteq> 0 \<Longrightarrow>
              (\<And>a b. (a, b) \<in>\<^sub>p set (ap gs bs ps hs data) \<Longrightarrow> fst a \<noteq> 0 \<Longrightarrow> fst b \<noteq> 0 \<Longrightarrow>
                     crit_pair_cbelow_on d m (fst ` B) (fst a) (fst b)) \<Longrightarrow>
              (\<And>a b. a \<in> set gs \<union> set bs \<Longrightarrow> b \<in> set gs \<union> set bs \<Longrightarrow> fst a \<noteq> 0 \<Longrightarrow> fst b \<noteq> 0 \<Longrightarrow>
                     crit_pair_cbelow_on d m (fst ` B) (fst a) (fst b)) \<Longrightarrow>
              crit_pair_cbelow_on d m (fst ` B) (fst h) (fst g)"
  assumes "\<And>gs bs ps hs data B d m h g. dickson_grading d \<Longrightarrow>
              set gs \<union> set bs \<union> set hs \<subseteq> B \<Longrightarrow> fst ` B \<subseteq> dgrad_p_set d m \<Longrightarrow>
              set ps \<subseteq> set bs \<times> (set gs \<union> set bs) \<Longrightarrow> (set gs \<union> set bs) \<inter> set hs = {} \<Longrightarrow>
              unique_idx (gs @ bs @ hs) data \<Longrightarrow> is_Groebner_basis (fst ` set gs) \<Longrightarrow> h \<noteq> g \<Longrightarrow>
              fst h \<noteq> 0 \<Longrightarrow> fst g \<noteq> 0 \<Longrightarrow> (h, g) \<in> set ps -\<^sub>p set (ap gs bs ps hs data) \<Longrightarrow>
              (\<And>a b. (a, b) \<in>\<^sub>p set (ap gs bs ps hs data) \<Longrightarrow> (a, b) \<in>\<^sub>p set hs \<times> (set gs \<union> set bs \<union> set hs) \<Longrightarrow>
                     fst a \<noteq> 0 \<Longrightarrow> fst b \<noteq> 0 \<Longrightarrow> crit_pair_cbelow_on d m (fst ` B) (fst a) (fst b)) \<Longrightarrow>
              crit_pair_cbelow_on d m (fst ` B) (fst h) (fst g)"
  shows "ap_spec ap"
  unfolding ap_spec_def
  apply (intro allI conjI impI)
    subgoal by (rule assms(1))
    subgoal by (intro ballI impI, rule assms(2), blast+)
    subgoal by (rule assms(3), blast+)
  done

lemma ap_specD1:
  assumes "ap_spec ap"
  shows "set (ap gs bs ps hs data) \<subseteq> set ps \<union> (set hs \<times> (set gs \<union> set bs \<union> set hs))"
  using assms unfolding ap_spec_def by (elim allE conjE) (assumption)

lemma ap_specD2:
  assumes "ap_spec ap" and "dickson_grading d" and "set gs \<union> set bs \<union> set hs \<subseteq> B"
    and "fst ` B \<subseteq> dgrad_p_set d m" and "(h, g) \<in>\<^sub>p set hs \<times> (set gs \<union> set bs \<union> set hs)"
    and "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)" and "unique_idx (gs @ bs @ hs) data"
    and "is_Groebner_basis (fst ` set gs)" and "h \<noteq> g" and "fst h \<noteq> 0" and "fst g \<noteq> 0"
    and "\<And>a b. (a, b) \<in>\<^sub>p set (ap gs bs ps hs data) \<Longrightarrow> fst a \<noteq> 0 \<Longrightarrow> fst b \<noteq> 0 \<Longrightarrow>
               crit_pair_cbelow_on d m (fst ` B) (fst a) (fst b)"
    and "\<And>a b. a \<in> set gs \<union> set bs \<Longrightarrow> b \<in> set gs \<union> set bs \<Longrightarrow> fst a \<noteq> 0 \<Longrightarrow> fst b \<noteq> 0 \<Longrightarrow>
               crit_pair_cbelow_on d m (fst ` B) (fst a) (fst b)"
  shows "crit_pair_cbelow_on d m (fst ` B) (fst h) (fst g)"
proof -
  from assms(5) have "(h, g) \<in> set hs \<times> (set gs \<union> set bs \<union> set hs) \<or> (g, h) \<in> set hs \<times> (set gs \<union> set bs \<union> set hs)"
    by (simp only: in_pair_iff)
  thus ?thesis
  proof
    assume "(h, g) \<in> set hs \<times> (set gs \<union> set bs \<union> set hs)"
    hence "h \<in> set hs" and "g \<in> set gs \<union> set bs \<union> set hs" by simp_all
    from assms(1)[unfolded ap_spec_def, rule_format, of gs bs ps hs data] assms(2-4) this assms (6-)
    show ?thesis by metis
  next
    assume "(g, h) \<in> set hs \<times> (set gs \<union> set bs \<union> set hs)"
    hence "g \<in> set hs" and "h \<in> set gs \<union> set bs \<union> set hs" by simp_all
    hence "crit_pair_cbelow_on d m (fst ` B) (fst g) (fst h)"
      using assms(1)[unfolded ap_spec_def, rule_format, of gs bs ps hs data]
            assms(2,3,4,6,7,8,10,11,12,13) assms(9)[symmetric]
      by metis
    thus ?thesis by (rule crit_pair_cbelow_sym)
  qed
qed

lemma ap_specD3:
  assumes "ap_spec ap" and "dickson_grading d" and "set gs \<union> set bs \<union> set hs \<subseteq> B"
    and "fst ` B \<subseteq> dgrad_p_set d m" and "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)"
    and "(set gs \<union> set bs) \<inter> set hs = {}" and "unique_idx (gs @ bs @ hs) data"
    and "is_Groebner_basis (fst ` set gs)" and "h \<noteq> g" and "fst h \<noteq> 0" and "fst g \<noteq> 0"
    and "(h, g) \<in>\<^sub>p set ps -\<^sub>p set (ap gs bs ps hs data)"
    and "\<And>a b. a \<in> set hs \<Longrightarrow> b \<in> set gs \<union> set bs \<union> set hs \<Longrightarrow> (a, b) \<in>\<^sub>p set (ap gs bs ps hs data) \<Longrightarrow>
               fst a \<noteq> 0 \<Longrightarrow> fst b \<noteq> 0 \<Longrightarrow> crit_pair_cbelow_on d m (fst ` B) (fst a) (fst b)"
  shows "crit_pair_cbelow_on d m (fst ` B) (fst h) (fst g)"
proof -
  have *: "crit_pair_cbelow_on d m (fst ` B) (fst a) (fst b)"
    if 1: "(a, b) \<in>\<^sub>p set (ap gs bs ps hs data)" and 2: "(a, b) \<in>\<^sub>p set hs \<times> (set gs \<union> set bs \<union> set hs)"
    and 3: "fst a \<noteq> 0" and 4: "fst b \<noteq> 0" for a b
  proof -
    from 2 have "(a, b) \<in> set hs \<times> (set gs \<union> set bs \<union> set hs) \<or> (b, a) \<in> set hs \<times> (set gs \<union> set bs \<union> set hs)"
      by (simp only: in_pair_iff)
    thus ?thesis
    proof
      assume "(a, b) \<in> set hs \<times> (set gs \<union> set bs \<union> set hs)"
      hence "a \<in> set hs" and "b \<in> set gs \<union> set bs \<union> set hs" by simp_all
      thus ?thesis using 1 3 4 by (rule assms(13))
    next
      assume "(b, a) \<in> set hs \<times> (set gs \<union> set bs \<union> set hs)"
      hence "b \<in> set hs" and "a \<in> set gs \<union> set bs \<union> set hs" by simp_all
      moreover from 1 have "(b, a) \<in>\<^sub>p set (ap gs bs ps hs data)" by (auto simp: in_pair_iff)
      ultimately have "crit_pair_cbelow_on d m (fst ` B) (fst b) (fst a)" using 4 3 by (rule assms(13))
      thus ?thesis by (rule crit_pair_cbelow_sym)
    qed
  qed
  from assms(12) have "(h, g) \<in> set ps -\<^sub>p set (ap gs bs ps hs data) \<or>
                        (g, h) \<in> set ps -\<^sub>p set (ap gs bs ps hs data)" by (simp only: in_pair_iff)
  thus ?thesis
  proof
    assume "(h, g) \<in> set ps -\<^sub>p set (ap gs bs ps hs data)"
    with assms(1)[unfolded ap_spec_def, rule_format, of gs bs ps hs data] assms(2-11)
    show ?thesis using assms(10) * by metis
  next
    assume "(g, h) \<in> set ps -\<^sub>p set (ap gs bs ps hs data)"
    with assms(1)[unfolded ap_spec_def, rule_format, of gs bs ps hs data] assms(2-11)
    have "crit_pair_cbelow_on d m (fst ` B) (fst g) (fst h)" using assms(10) * by metis
    thus ?thesis by (rule crit_pair_cbelow_sym)
  qed
qed

lemma ap_spec_Nil_subset:
  assumes "ap_spec ap"
  shows "set (ap gs bs ps [] data) \<subseteq> set ps"
  using ap_specD1[OF assms] by fastforce

lemma ap_spec_fst_subset:
  assumes "ap_spec ap"
  shows "fst ` set (ap gs bs ps hs data) \<subseteq> fst ` set ps \<union> set hs"
proof -
  from ap_specD1[OF assms]
  have "fst ` set (ap gs bs ps hs data) \<subseteq> fst ` (set ps \<union> set hs \<times> (set gs \<union> set bs \<union> set hs))"
    by (rule image_mono)
  thus ?thesis by auto
qed

lemma ap_spec_snd_subset:
  assumes "ap_spec ap"
  shows "snd ` set (ap gs bs ps hs data) \<subseteq> snd ` set ps \<union> set gs \<union> set bs \<union> set hs"
proof -
  from ap_specD1[OF assms]
  have "snd ` set (ap gs bs ps hs data) \<subseteq> snd ` (set ps \<union> set hs \<times> (set gs \<union> set bs \<union> set hs))"
    by (rule image_mono)
  thus ?thesis by auto
qed

lemma ap_spec_inE:
  assumes "ap_spec ap" and "(p, q) \<in> set (ap gs bs ps hs data)"
  assumes 1: "(p, q) \<in> set ps \<Longrightarrow> thesis"
  assumes 2: "p \<in> set hs \<Longrightarrow> q \<in> set gs \<union> set bs \<union> set hs \<Longrightarrow> thesis"
  shows thesis
proof -
  from assms(2) ap_specD1[OF assms(1)] have "(p, q) \<in> set ps \<union> set hs \<times> (set gs \<union> set bs \<union> set hs)" ..
  thus ?thesis
  proof
    assume "(p, q) \<in> set ps"
    thus ?thesis by (rule 1)
  next
    assume "(p, q) \<in> set hs \<times> (set gs \<union> set bs \<union> set hs)"
    hence "p \<in> set hs" and "q \<in> set gs \<union> set bs \<union> set hs" by blast+
    thus ?thesis by (rule 2)
  qed
qed

lemma subset_Times_ap:
  assumes "ap_spec ap" and "ab_spec ab" and "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)"
  shows "set (ap gs bs (ps -- sps) hs data) \<subseteq> set (ab gs bs hs data) \<times> (set gs \<union> set (ab gs bs hs data))"
proof
  fix p q
  assume "(p, q) \<in> set (ap gs bs (ps -- sps) hs data)"
  with assms(1) show "(p, q) \<in> set (ab gs bs hs data) \<times> (set gs \<union> set (ab gs bs hs data))"
  proof (rule ap_spec_inE)
    assume "(p, q) \<in> set (ps -- sps)"
    hence "(p, q) \<in> set ps" by (simp add: set_diff_list)
    from this assms(3) have "(p, q) \<in> set bs \<times> (set gs \<union> set bs)" ..
    hence "p \<in> set bs" and "q \<in> set gs \<union> set bs" by blast+
    thus ?thesis by (auto simp add: ab_specD1[OF assms(2)])
  next
    assume "p \<in> set hs" and "q \<in> set gs \<union> set bs \<union> set hs"
    thus ?thesis by (simp add: ab_specD1[OF assms(2)])
  qed
qed

subsubsection \<open>Function \<open>args_to_set\<close>\<close>

definition args_to_set :: "('t, 'b::field, 'c) pdata list \<times> ('t, 'b, 'c) pdata list \<times> ('t, 'b, 'c) pdata_pair list \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) set"
  where "args_to_set x = fst ` (set (fst x) \<union> set (fst (snd x)) \<union> fst ` set (snd (snd x)) \<union> snd ` set (snd (snd x)))"

lemma args_to_set_alt:
  "args_to_set (gs, bs, ps) = fst ` set gs \<union> fst ` set bs \<union> fst ` fst ` set ps \<union> fst ` snd ` set ps"
  by (simp add: args_to_set_def image_Un)

lemma args_to_set_subset_Times:
  assumes "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)"
  shows "args_to_set (gs, bs, ps) = fst ` set gs \<union> fst ` set bs"
  unfolding args_to_set_alt using assms by auto

lemma args_to_set_subset:
  assumes "ap_spec ap" and "ab_spec ab"
  shows "args_to_set (gs, ab gs bs hs data, ap gs bs ps hs data) \<subseteq>
              fst ` (set gs \<union> set bs \<union> fst ` set ps \<union> snd ` set ps \<union> set hs)" (is "?l \<subseteq> fst ` ?r")
proof (simp only: args_to_set_alt Un_subset_iff, intro conjI image_mono)
  show "set (ab gs bs hs data) \<subseteq> ?r" by (auto simp add: ab_specD1[OF assms(2)])
next
  from assms(1) have "fst ` set (ap gs bs ps hs data) \<subseteq> fst ` set ps \<union> set hs"
    by (rule ap_spec_fst_subset)
  thus "fst ` set (ap gs bs ps hs data) \<subseteq> ?r" by blast
next
  from assms(1) have "snd ` set (ap gs bs ps hs data) \<subseteq> snd ` set ps \<union> set gs \<union> set bs \<union> set hs"
    by (rule ap_spec_snd_subset)
  thus "snd ` set (ap gs bs ps hs data) \<subseteq> ?r" by blast
qed blast

lemma args_to_set_alt2:
  assumes "ap_spec ap" and "ab_spec ab" and "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)"
  shows "args_to_set (gs, ab gs bs hs data, ap gs bs (ps -- sps) hs data) =
              fst ` (set gs \<union> set bs \<union> set hs)" (is "?l = fst ` ?r")
proof
  from assms(1, 2) have "?l \<subseteq> fst ` (set gs \<union> set bs \<union> fst ` set (ps -- sps) \<union> snd ` set (ps -- sps) \<union> set hs)"
    by (rule args_to_set_subset)
  also have "... \<subseteq> fst ` ?r"
  proof (rule image_mono)
    have "set gs \<union> set bs \<union> fst ` set (ps -- sps) \<union> snd ` set (ps -- sps) \<union> set hs \<subseteq>
            set gs \<union> set bs \<union> fst ` set ps \<union> snd ` set ps \<union> set hs" by (auto simp: set_diff_list)
    also from assms(3) have "... \<subseteq> ?r" by fastforce
    finally show "set gs \<union> set bs \<union> fst ` set (ps -- sps) \<union> snd ` set (ps -- sps) \<union> set hs \<subseteq> ?r" .
  qed
  finally show "?l \<subseteq> fst ` ?r" .
next
  from assms(2) have eq: "set (ab gs bs hs data) = set bs \<union> set hs" by (rule ab_specD1)
  have "fst ` ?r \<subseteq> fst ` set gs \<union> fst ` set (ab gs bs hs data)" unfolding eq using assms(3)
    by fastforce
  also have "... \<subseteq> ?l" unfolding args_to_set_alt by fastforce
  finally show "fst ` ?r \<subseteq> ?l" .
qed

lemma args_to_set_subset1:
  assumes "set gs1 \<subseteq> set gs2"
  shows "args_to_set (gs1, bs, ps) \<subseteq> args_to_set (gs2, bs, ps)"
  using assms by (auto simp add: args_to_set_alt)

lemma args_to_set_subset2:
  assumes "set bs1 \<subseteq> set bs2"
  shows "args_to_set (gs, bs1, ps) \<subseteq> args_to_set (gs, bs2, ps)"
  using assms by (auto simp add: args_to_set_alt)

lemma args_to_set_subset3:
  assumes "set ps1 \<subseteq> set ps2"
  shows "args_to_set (gs, bs, ps1) \<subseteq> args_to_set (gs, bs, ps2)"
  using assms unfolding args_to_set_alt by blast

subsubsection \<open>Functions \<open>count_const_lt_components\<close>, \<open>count_rem_comps\<close> and \<open>full_gb\<close>\<close>

definition rem_comps_spec :: "('t, 'b::zero, 'c) pdata list \<Rightarrow> nat \<times> 'd \<Rightarrow> bool"
  where "rem_comps_spec bs data \<longleftrightarrow> (card (component_of_term ` Keys (fst ` set bs)) =
                                  fst data + card (const_lt_component ` (fst ` set bs - {0}) - {None}))"

definition count_const_lt_components :: "('t, 'b::zero, 'c) pdata' list \<Rightarrow> nat"
  where "count_const_lt_components hs = length (remdups (filter (\<lambda>x. x \<noteq> None) (map (const_lt_component \<circ> fst) hs)))"

definition count_rem_components :: "('t, 'b::zero, 'c) pdata' list \<Rightarrow> nat"
  where "count_rem_components bs = length (remdups (map component_of_term (Keys_to_list (map fst bs)))) -
                                    count_const_lt_components [b\<leftarrow>bs . fst b \<noteq> 0]"

lemma count_const_lt_components_alt:
  "count_const_lt_components hs = card (const_lt_component ` fst ` set hs - {None})"
  by (simp add: count_const_lt_components_def card_set[symmetric] set_diff_eq image_comp del: not_None_eq)

lemma count_rem_components_alt:
  "count_rem_components bs + card (const_lt_component ` (fst ` set bs - {0}) - {None}) =
    card (component_of_term ` Keys (fst ` set bs))"
proof -
  have eq: "fst ` {x \<in> set bs. fst x \<noteq> 0} = fst ` set bs - {0}" by fastforce
  have "card (const_lt_component ` (fst ` set bs - {0}) - {None}) \<le> card (component_of_term ` Keys (fst ` set bs))"
    by (rule card_const_lt_component_le, rule finite_imageI, fact finite_set)
  thus ?thesis
    by (simp add: count_rem_components_def card_set[symmetric] set_Keys_to_list count_const_lt_components_alt eq)
qed

lemma rem_comps_spec_count_rem_components: "rem_comps_spec bs (count_rem_components bs, data)"
  by (simp only: rem_comps_spec_def fst_conv count_rem_components_alt)

definition full_gb :: "('t, 'b, 'c) pdata list \<Rightarrow> ('t, 'b::zero_neq_one, 'c::default) pdata list"
  where "full_gb bs = map (\<lambda>k. (monomial 1 (term_of_pair (0, k)), 0, default))
                          (remdups (map component_of_term (Keys_to_list (map fst bs))))"

lemma fst_set_full_gb:
  "fst ` set (full_gb bs) = (\<lambda>v. monomial 1 (term_of_pair (0, component_of_term v))) ` Keys (fst ` set bs)"
  by (simp add: full_gb_def set_Keys_to_list image_comp)

lemma Keys_full_gb:
  "Keys (fst ` set (full_gb bs)) = (\<lambda>v. term_of_pair (0, component_of_term v)) ` Keys (fst ` set bs)"
  by (auto simp add: fst_set_full_gb Keys_def image_image)

lemma pps_full_gb: "pp_of_term ` Keys (fst ` set (full_gb bs)) \<subseteq> {0}"
  by (simp add: Keys_full_gb image_comp image_subset_iff term_simps)

lemma components_full_gb:
  "component_of_term ` Keys (fst ` set (full_gb bs)) = component_of_term ` Keys (fst ` set bs)"
  by (simp add: Keys_full_gb image_comp, rule image_cong, fact refl, simp add: term_simps)

lemma full_gb_is_full_pmdl: "is_full_pmdl (fst ` set (full_gb bs))"
    for bs::"('t, 'b::field, 'c::default) pdata list"
proof (rule is_full_pmdlI_lt_finite)
  from finite_set show "finite (fst ` set (full_gb bs))" by (rule finite_imageI)
next
  fix k
  assume "k \<in> component_of_term ` Keys (fst ` set (full_gb bs))"
  then obtain v where "v \<in> Keys (fst ` set (full_gb bs))" and k: "k = component_of_term v" ..
  from this(1) obtain b where "b \<in> fst ` set (full_gb bs)" and "v \<in> keys b" by (rule in_KeysE)
  from this(1) obtain u where "u \<in> Keys (fst ` set bs)" and b: "b = monomial 1 (term_of_pair (0, component_of_term u))"
    unfolding fst_set_full_gb ..
  have lt: "lt b = term_of_pair (0, component_of_term u)" by (simp add: b lt_monomial)
  from \<open>v \<in> keys b\<close> have v: "v = term_of_pair (0, component_of_term u)" by (simp add: b)
  show "\<exists>b\<in>fst ` set (full_gb bs). b \<noteq> 0 \<and> component_of_term (lt b) = k \<and> lp b = 0"
  proof (intro bexI conjI)
    show "b \<noteq> 0" by (simp add: b monomial_0_iff)
  next
    show "component_of_term (lt b) = k" by (simp add: lt term_simps k v)
  next
    show "lp b = 0" by (simp add: lt term_simps)
  qed fact
qed

text \<open>In fact, @{thm full_gb_is_full_pmdl} also holds if @{typ 'b} is no field.\<close>

lemma full_gb_isGB: "is_Groebner_basis (fst ` set (full_gb bs))"
proof (rule Buchberger_criterion_finite)
  from finite_set show "finite (fst ` set (full_gb bs))" by (rule finite_imageI)
next
  fix p q :: "'t \<Rightarrow>\<^sub>0 'b"
  assume "p \<in> fst ` set (full_gb bs)"
  then obtain v where p: "p = monomial 1 (term_of_pair (0, component_of_term v))"
    unfolding fst_set_full_gb ..
  hence lt: "component_of_term (lt p) = component_of_term v" by (simp add: lt_monomial term_simps)
  assume "q \<in> fst ` set (full_gb bs)"
  then obtain u where q: "q = monomial 1 (term_of_pair (0, component_of_term u))"
    unfolding fst_set_full_gb ..
  hence lq: "component_of_term (lt q) = component_of_term u" by (simp add: lt_monomial term_simps)
  assume "component_of_term (lt p) = component_of_term (lt q)"
  hence "component_of_term v = component_of_term u" by (simp only: lt lq)
  hence "p = q" by (simp only: p q)
  moreover assume "p \<noteq> q"
  ultimately show "(red (fst ` set (full_gb bs)))\<^sup>*\<^sup>* (spoly p q) 0" by (simp only:)
qed

subsubsection \<open>Specification of the @{emph \<open>completion\<close>} parameter\<close>

definition compl_struct :: "('t, 'b::field, 'c, 'd) complT \<Rightarrow> bool"
  where "compl_struct compl \<longleftrightarrow>
          (\<forall>gs bs ps sps data. sps \<noteq> [] \<longrightarrow> set sps \<subseteq> set ps \<longrightarrow>
              (\<forall>d. dickson_grading d \<longrightarrow>
                  dgrad_p_set_le d (fst ` (set (fst (compl gs bs (ps -- sps) sps data)))) (args_to_set (gs, bs, ps))) \<and>
              component_of_term ` Keys (fst ` (set (fst (compl gs bs (ps -- sps) sps data)))) \<subseteq>
                component_of_term ` Keys (args_to_set (gs, bs, ps)) \<and>
              0 \<notin> fst ` set (fst (compl gs bs (ps -- sps) sps data)) \<and>
              (\<forall>h\<in>set (fst (compl gs bs (ps -- sps) sps data)). \<forall>b\<in>set gs \<union> set bs. fst b \<noteq> 0 \<longrightarrow> \<not> lt (fst b) adds\<^sub>t lt (fst h)))"

lemma compl_structI:
  assumes "\<And>d gs bs ps sps data. dickson_grading d \<Longrightarrow> sps \<noteq> [] \<Longrightarrow> set sps \<subseteq> set ps \<Longrightarrow>
              dgrad_p_set_le d (fst ` (set (fst (compl gs bs (ps -- sps) sps data)))) (args_to_set (gs, bs, ps))"
  assumes "\<And>gs bs ps sps data. sps \<noteq> [] \<Longrightarrow> set sps \<subseteq> set ps \<Longrightarrow>
              component_of_term ` Keys (fst ` (set (fst (compl gs bs (ps -- sps) sps data)))) \<subseteq>
                component_of_term ` Keys (args_to_set (gs, bs, ps))"
  assumes "\<And>gs bs ps sps data. sps \<noteq> [] \<Longrightarrow> set sps \<subseteq> set ps \<Longrightarrow> 0 \<notin> fst ` set (fst (compl gs bs (ps -- sps) sps data))"
  assumes "\<And>gs bs ps sps h b data. sps \<noteq> [] \<Longrightarrow> set sps \<subseteq> set ps \<Longrightarrow> h \<in> set (fst (compl gs bs (ps -- sps) sps data)) \<Longrightarrow>
              b \<in> set gs \<union> set bs \<Longrightarrow> fst b \<noteq> 0 \<Longrightarrow> \<not> lt (fst b) adds\<^sub>t lt (fst h)"
  shows "compl_struct compl"
  unfolding compl_struct_def using assms by auto

lemma compl_structD1:
  assumes "compl_struct compl" and "dickson_grading d" and "sps \<noteq> []" and "set sps \<subseteq> set ps"
  shows "dgrad_p_set_le d (fst ` (set (fst (compl gs bs (ps -- sps) sps data)))) (args_to_set (gs, bs, ps))"
  using assms unfolding compl_struct_def by blast

lemma compl_structD2:
  assumes "compl_struct compl" and "sps \<noteq> []" and "set sps \<subseteq> set ps"
  shows "component_of_term ` Keys (fst ` (set (fst (compl gs bs (ps -- sps) sps data)))) \<subseteq>
           component_of_term ` Keys (args_to_set (gs, bs, ps))"
  using assms unfolding compl_struct_def by blast

lemma compl_structD3:
  assumes "compl_struct compl" and "sps \<noteq> []" and "set sps \<subseteq> set ps"
  shows "0 \<notin> fst ` set (fst (compl gs bs (ps -- sps) sps data))"
  using assms unfolding compl_struct_def by blast

lemma compl_structD4:
  assumes "compl_struct compl" and "sps \<noteq> []" and "set sps \<subseteq> set ps"
    and "h \<in> set (fst (compl gs bs (ps -- sps) sps data))" and "b \<in> set gs \<union> set bs" and "fst b \<noteq> 0"
  shows "\<not> lt (fst b) adds\<^sub>t lt (fst h)"
  using assms unfolding compl_struct_def by blast

definition struct_spec :: "('t, 'b::field, 'c, 'd) selT \<Rightarrow> ('t, 'b, 'c, 'd) apT \<Rightarrow> ('t, 'b, 'c, 'd) abT \<Rightarrow>
                            ('t, 'b, 'c, 'd) complT \<Rightarrow> bool"
  where "struct_spec sel ap ab compl \<longleftrightarrow> (sel_spec sel \<and> ap_spec ap \<and> ab_spec ab \<and> compl_struct compl)"

lemma struct_specI:
  assumes "sel_spec sel" and "ap_spec ap" and "ab_spec ab" and "compl_struct compl"
  shows "struct_spec sel ap ab compl"
  unfolding struct_spec_def using assms by (intro conjI)

lemma struct_specD1:
  assumes "struct_spec sel ap ab compl"
  shows "sel_spec sel"
  using assms unfolding struct_spec_def by (elim conjE)

lemma struct_specD2:
  assumes "struct_spec sel ap ab compl"
  shows "ap_spec ap"
  using assms unfolding struct_spec_def by (elim conjE)

lemma struct_specD3:
  assumes "struct_spec sel ap ab compl"
  shows "ab_spec ab"
  using assms unfolding struct_spec_def by (elim conjE)

lemma struct_specD4:
  assumes "struct_spec sel ap ab compl"
  shows "compl_struct compl"
  using assms unfolding struct_spec_def by (elim conjE)

lemmas struct_specD = struct_specD1 struct_specD2 struct_specD3 struct_specD4

definition compl_pmdl :: "('t, 'b::field, 'c, 'd) complT \<Rightarrow> bool"
  where "compl_pmdl compl \<longleftrightarrow>
          (\<forall>gs bs ps sps data. is_Groebner_basis (fst ` set gs) \<longrightarrow> sps \<noteq> [] \<longrightarrow> set sps \<subseteq> set ps \<longrightarrow>
              unique_idx (gs @ bs) data \<longrightarrow>
              fst ` (set (fst (compl gs bs (ps -- sps) sps data))) \<subseteq> pmdl (args_to_set (gs, bs, ps)))"

lemma compl_pmdlI:
  assumes "\<And>gs bs ps sps data. is_Groebner_basis (fst ` set gs) \<Longrightarrow> sps \<noteq> [] \<Longrightarrow> set sps \<subseteq> set ps \<Longrightarrow>
              unique_idx (gs @ bs) data \<Longrightarrow>
              fst ` (set (fst (compl gs bs (ps -- sps) sps data))) \<subseteq> pmdl (args_to_set (gs, bs, ps))"
  shows "compl_pmdl compl"
  unfolding compl_pmdl_def using assms by blast

lemma compl_pmdlD:
  assumes "compl_pmdl compl" and "is_Groebner_basis (fst ` set gs)"
    and "sps \<noteq> []" and "set sps \<subseteq> set ps" and "unique_idx (gs @ bs) data"
  shows "fst ` (set (fst (compl gs bs (ps -- sps) sps data))) \<subseteq> pmdl (args_to_set (gs, bs, ps))"
  using assms unfolding compl_pmdl_def by blast

definition compl_conn :: "('t, 'b::field, 'c, 'd) complT \<Rightarrow> bool"
  where "compl_conn compl \<longleftrightarrow>
            (\<forall>d m gs bs ps sps p q data. dickson_grading d \<longrightarrow> fst ` set gs \<subseteq> dgrad_p_set d m \<longrightarrow>
              is_Groebner_basis (fst ` set gs) \<longrightarrow> fst ` set bs \<subseteq> dgrad_p_set d m \<longrightarrow>
              set ps \<subseteq> set bs \<times> (set gs \<union> set bs) \<longrightarrow> sps \<noteq> [] \<longrightarrow> set sps \<subseteq> set ps \<longrightarrow>
              unique_idx (gs @ bs) data \<longrightarrow> (p, q) \<in> set sps \<longrightarrow> fst p \<noteq> 0 \<longrightarrow> fst q \<noteq> 0 \<longrightarrow>
              crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> fst ` set (fst (compl gs bs (ps -- sps) sps data))) (fst p) (fst q))"

text \<open>Informally, \<open>compl_conn compl\<close> means that, for suitable arguments \<open>gs\<close>, \<open>bs\<close>, \<open>ps\<close> and \<open>sps\<close>,
  the value of \<open>compl gs bs ps sps\<close> is a list \<open>hs\<close> such that the critical pairs of all elements in
  \<open>sps\<close> can be connected modulo \<open>set gs \<union> set bs \<union> set hs\<close>.\<close>

lemma compl_connI:
  assumes "\<And>d m gs bs ps sps p q data. dickson_grading d \<Longrightarrow> fst ` set gs \<subseteq> dgrad_p_set d m \<Longrightarrow>
            is_Groebner_basis (fst ` set gs) \<Longrightarrow> fst ` set bs \<subseteq> dgrad_p_set d m \<Longrightarrow>
            set ps \<subseteq> set bs \<times> (set gs \<union> set bs) \<Longrightarrow> sps \<noteq> [] \<Longrightarrow> set sps \<subseteq> set ps \<Longrightarrow>
            unique_idx (gs @ bs) data \<Longrightarrow> (p, q) \<in> set sps \<Longrightarrow> fst p \<noteq> 0 \<Longrightarrow> fst q \<noteq> 0 \<Longrightarrow>
            crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> fst ` set (fst (compl gs bs (ps -- sps) sps data))) (fst p) (fst q)"
  shows "compl_conn compl"
  unfolding compl_conn_def using assms by presburger

lemma compl_connD:
  assumes "compl_conn compl" and "dickson_grading d" and "fst ` set gs \<subseteq> dgrad_p_set d m"
    and "is_Groebner_basis (fst ` set gs)" and "fst ` set bs \<subseteq> dgrad_p_set d m"
    and "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)" and "sps \<noteq> []" and "set sps \<subseteq> set ps"
    and "unique_idx (gs @ bs) data" and "(p, q) \<in> set sps" and "fst p \<noteq> 0" and "fst q \<noteq> 0"
  shows "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> fst ` set (fst (compl gs bs (ps -- sps) sps data))) (fst p) (fst q)"
  using assms unfolding compl_conn_def Un_assoc by blast

subsubsection \<open>Function \<open>gb_schema_dummy\<close>\<close>

definition (in -) add_indices :: "(('a, 'b, 'c) pdata' list \<times> 'd) \<Rightarrow> (nat \<times> 'd) \<Rightarrow> (('a, 'b, 'c) pdata list \<times> nat \<times> 'd)"
  where [code del]: "add_indices ns data =
        (map_idx (\<lambda>h i. (fst h, i, snd h)) (fst ns) (fst data), fst data + length (fst ns), snd ns)"

lemma (in -) add_indices_code [code]:
  "add_indices (ns, data) (n, data') = (map_idx (\<lambda>(h, d) i. (h, i, d)) ns n, n + length ns, data)"
  by (simp add: add_indices_def case_prod_beta')

lemma fst_add_indices: "map fst (fst (add_indices ns data')) = map fst (fst ns)"
  by (simp add: add_indices_def map_map_idx map_idx_no_idx)

corollary fst_set_add_indices: "fst ` set (fst (add_indices ns data')) = fst ` set (fst ns)"
  using fst_add_indices by (metis set_map)

lemma in_set_add_indicesE:
  assumes "f \<in> set (fst (add_indices aux data))"
  obtains i where "i < length (fst aux)" and "f = (fst ((fst aux) ! i), fst data + i, snd ((fst aux) ! i))"
proof -
  let ?hs = "fst (add_indices aux data)"
  from assms obtain i where "i < length ?hs" and "f = ?hs ! i" by (metis in_set_conv_nth)
  from this(1) have "i < length (fst aux)" by (simp add: add_indices_def)
  hence "?hs ! i = (fst ((fst aux) ! i), fst data + i, snd ((fst aux) ! i))"
    unfolding add_indices_def fst_conv by (rule map_idx_nth)
  hence "f = (fst ((fst aux) ! i), fst data + i, snd ((fst aux) ! i))" by (simp add: \<open>f = ?hs ! i\<close>)
  with \<open>i < length (fst aux)\<close> show ?thesis ..
qed

definition gb_schema_aux_term1 :: "((('t, 'b::field, 'c) pdata list \<times> ('t, 'b, 'c) pdata_pair list) \<times>
                                    (('t, 'b, 'c) pdata list \<times> ('t, 'b, 'c) pdata_pair list)) set"
  where "gb_schema_aux_term1 = {(a, b::('t, 'b, 'c) pdata list). (fst ` set a) \<sqsupset>p (fst ` set b)} <*lex*>
                              (measure (card \<circ> set))"

definition gb_schema_aux_term2 ::
    "('a \<Rightarrow> nat) \<Rightarrow> ('t, 'b::field, 'c) pdata list \<Rightarrow> ((('t, 'b, 'c) pdata list \<times> ('t, 'b, 'c) pdata_pair list) \<times>
                    (('t, 'b, 'c) pdata list \<times> ('t, 'b, 'c) pdata_pair list)) set"
  where "gb_schema_aux_term2 d gs = {(a, b). dgrad_p_set_le d (args_to_set (gs, a)) (args_to_set (gs, b)) \<and>
                          component_of_term ` Keys (args_to_set (gs, a)) \<subseteq> component_of_term ` Keys (args_to_set (gs, b))}"

definition gb_schema_aux_term where "gb_schema_aux_term d gs = gb_schema_aux_term1 \<inter> gb_schema_aux_term2 d gs"

text \<open>@{const gb_schema_aux_term} is needed for proving termination of function \<open>gb_schema_aux\<close>.\<close>

lemma gb_schema_aux_term1_wf_on:
  assumes "dickson_grading d" and "finite K"
  shows "wfp_on (\<lambda>x y. (x, y) \<in> gb_schema_aux_term1)
                {x::(('t, 'b, 'c) pdata list) \<times> ((('t, 'b::field, 'c) pdata_pair list)).
                    args_to_set (gs, x) \<subseteq> dgrad_p_set d m \<and> component_of_term ` Keys (args_to_set (gs, x)) \<subseteq> K}"
proof (rule wfp_onI_min)
  let ?B = "dgrad_p_set d m"
  let ?A = "{x::(('t, 'b, 'c) pdata list) \<times> ((('t, 'b, 'c) pdata_pair list)).
              args_to_set (gs, x) \<subseteq> ?B \<and> component_of_term ` Keys (args_to_set (gs, x)) \<subseteq> K}"
  let ?C = "Pow ?B \<inter> {F. component_of_term ` Keys F \<subseteq> K}"
  have A_sub_Pow: "(image fst) ` set ` fst ` ?A \<subseteq> ?C"
  proof
    fix x
    assume "x \<in> (image fst) ` set ` fst ` ?A"
    then obtain x1 where "x1 \<in> set ` fst ` ?A" and x: "x = fst ` x1" by auto
    from this(1) obtain x2 where "x2 \<in> fst ` ?A" and x1: "x1 = set x2" by auto
    from this(1) obtain x3 where "x3 \<in> ?A" and x2: "x2 = fst x3" by auto
    from this(1) have "args_to_set (gs, x3) \<subseteq> ?B" and "component_of_term ` Keys (args_to_set (gs, x3)) \<subseteq> K"
      by simp_all
    thus "x \<in> ?C" by (simp add: args_to_set_def x x1 x2 image_Un Keys_Un)
  qed

  fix x Q
  assume "x \<in> Q" and "Q \<subseteq> ?A"
  have Q_sub_A: "(image fst) ` set ` fst ` Q \<subseteq> (image fst) ` set ` fst ` ?A"
    by ((rule image_mono)+, fact)
  from assms have "wfp_on (\<sqsupset>p) ?C" by (rule red_supset_wf_on)
  moreover have "fst ` set (fst x) \<in> (image fst) ` set ` fst ` Q"
    by (rule, fact refl, rule, fact refl, rule, fact refl, simp add: \<open>x \<in> Q\<close>)
  moreover from Q_sub_A A_sub_Pow have "(image fst) ` set ` fst ` Q \<subseteq> ?C" by (rule subset_trans)
  ultimately obtain z1 where "z1 \<in> (image fst) ` set ` fst ` Q"
    and 2: "\<And>y. y \<sqsupset>p z1 \<Longrightarrow> y \<notin> (image fst) ` set ` fst ` Q" by (rule wfp_onE_min, auto)
  from this(1) obtain x1 where "x1 \<in> Q" and z1: "z1 = fst ` set (fst x1)" by auto

  let ?Q2 = "{q \<in> Q. fst ` set (fst q) = z1}"
  have "snd x1 \<in> snd ` ?Q2" by (rule, fact refl, simp add: \<open>x1 \<in> Q\<close> z1)
  with wf_measure obtain z2 where "z2 \<in> snd ` ?Q2"
    and 3: "\<And>y. (y, z2) \<in> measure (card \<circ> set) \<Longrightarrow> y \<notin> snd ` ?Q2"
    by (rule wfE_min, blast)
  from this(1) obtain z where "z \<in> ?Q2" and z2: "z2 = snd z" ..
  from this(1) have "z \<in> Q" and eq1: "fst ` set (fst z) = z1" by blast+
  from this(1) show "\<exists>z\<in>Q. \<forall>y\<in>?A. (y, z) \<in> gb_schema_aux_term1 \<longrightarrow> y \<notin> Q"
  proof
    show "\<forall>y\<in>?A. (y, z) \<in> gb_schema_aux_term1 \<longrightarrow> y \<notin> Q"
    proof (intro ballI impI)
      fix y
      assume "y \<in> ?A"
      assume "(y, z) \<in> gb_schema_aux_term1"
      hence "(fst ` set (fst y) \<sqsupset>p z1 \<or> (fst y = fst z \<and> (snd y, z2) \<in> measure (card \<circ> set)))"
        by (simp add: gb_schema_aux_term1_def eq1[symmetric] z2 in_lex_prod_alt)
      thus "y \<notin> Q"
      proof (elim disjE conjE)
        assume "fst ` set (fst y) \<sqsupset>p z1"
        hence "fst ` set (fst y) \<notin> (image fst) ` set ` fst ` Q" by (rule 2)
        thus ?thesis by auto
      next
        assume "(snd y, z2) \<in> measure (card \<circ> set)"
        hence "snd y \<notin> snd ` ?Q2" by (rule 3)
        hence "y \<notin> ?Q2" by blast
        moreover assume "fst y = fst z"
        ultimately show ?thesis by (simp add: eq1)
      qed
    qed
  qed
qed

lemma gb_schema_aux_term_wf:
  assumes "dickson_grading d"
  shows "wf (gb_schema_aux_term d gs)"
proof (rule wfI_min)
  fix x::"(('t, 'b, 'c) pdata list) \<times> (('t, 'b, 'c) pdata_pair list)" and Q
  assume "x \<in> Q"
  let ?A = "args_to_set (gs, x)"
  have "finite ?A" by (simp add: args_to_set_def)
  then obtain m where A: "?A \<subseteq> dgrad_p_set d m" by (rule dgrad_p_set_exhaust)
  define K where "K = component_of_term ` Keys ?A"
  from \<open>finite ?A\<close> have "finite K" unfolding K_def by (rule finite_imp_finite_component_Keys)
  let ?B = "dgrad_p_set d m"
  let ?Q = "{q \<in> Q. args_to_set (gs, q) \<subseteq> ?B \<and> component_of_term ` Keys (args_to_set (gs, q)) \<subseteq> K}"
  from assms \<open>finite K\<close> have "wfp_on (\<lambda>x y. (x, y) \<in> gb_schema_aux_term1)
                {x. args_to_set (gs, x) \<subseteq> ?B \<and> component_of_term ` Keys (args_to_set (gs, x)) \<subseteq> K}"
    by (rule gb_schema_aux_term1_wf_on)
  moreover from \<open>x \<in> Q\<close> A have "x \<in> ?Q" by (simp add: K_def)
  moreover have "?Q \<subseteq> {x. args_to_set (gs, x) \<subseteq> ?B \<and> component_of_term ` Keys (args_to_set (gs, x)) \<subseteq> K}" by auto
  ultimately obtain z where "z \<in> ?Q"
    and *: "\<And>y. (y, z) \<in> gb_schema_aux_term1 \<Longrightarrow> y \<notin> ?Q" by (rule wfp_onE_min, blast)
  from this(1) have "z \<in> Q" and a: "args_to_set (gs, z) \<subseteq> ?B" and b: "component_of_term ` Keys (args_to_set (gs, z)) \<subseteq> K"
    by simp_all
  from this(1) show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> gb_schema_aux_term d gs \<longrightarrow> y \<notin> Q"
  proof
    show "\<forall>y. (y, z) \<in> gb_schema_aux_term d gs \<longrightarrow> y \<notin> Q"
    proof (intro allI impI)
      fix y
      assume "(y, z) \<in> gb_schema_aux_term d gs"
      hence "(y, z) \<in> gb_schema_aux_term1" and "(y, z) \<in> gb_schema_aux_term2 d gs"
        by (simp_all add: gb_schema_aux_term_def)
      from this(2) have "dgrad_p_set_le d (args_to_set (gs, y)) (args_to_set (gs, z))"
        and comp_sub: "component_of_term ` Keys (args_to_set (gs, y)) \<subseteq> component_of_term ` Keys (args_to_set (gs, z))"
        by (simp_all add: gb_schema_aux_term2_def)
      from this(1) \<open>args_to_set (gs, z) \<subseteq> ?B\<close> have "args_to_set (gs, y) \<subseteq> ?B"
        by (rule dgrad_p_set_le_dgrad_p_set)
      moreover from comp_sub b have "component_of_term ` Keys (args_to_set (gs, y)) \<subseteq> K"
        by (rule subset_trans)
      moreover from \<open>(y, z) \<in> gb_schema_aux_term1\<close> have "y \<notin> ?Q" by (rule *)
      ultimately show "y \<notin> Q" by simp
    qed
  qed
qed

lemma dgrad_p_set_le_args_to_set_ab:
  assumes "dickson_grading d" and "ap_spec ap" and "ab_spec ab" and "compl_struct compl"
  assumes "sps \<noteq> []" and "set sps \<subseteq> set ps" and "hs = fst (add_indices (compl gs bs (ps -- sps) sps data) data)"
  shows "dgrad_p_set_le d (args_to_set (gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data')) (args_to_set (gs, bs, ps))"
    (is "dgrad_p_set_le _ ?l ?r")
proof -
  have "dgrad_p_set_le d ?l
          (fst ` (set gs \<union> set bs \<union> fst ` set (ps -- sps) \<union> snd ` set (ps -- sps) \<union> set hs))"
    by (rule dgrad_p_set_le_subset, rule args_to_set_subset[OF assms(2, 3)])
  also have "dgrad_p_set_le d ... ?r" unfolding image_Un
  proof (intro dgrad_p_set_leI_Un)
    show "dgrad_p_set_le d (fst ` set gs) (args_to_set (gs, bs, ps))"
      by (rule dgrad_p_set_le_subset, auto simp add: args_to_set_def)
  next
    show "dgrad_p_set_le d (fst ` set bs) (args_to_set (gs, bs, ps))"
      by (rule dgrad_p_set_le_subset, auto simp add: args_to_set_def)
  next
    show "dgrad_p_set_le d (fst ` fst ` set (ps -- sps)) (args_to_set (gs, bs, ps))"
      by (rule dgrad_p_set_le_subset, auto simp add: args_to_set_def set_diff_list)
  next
    show "dgrad_p_set_le d (fst ` snd ` set (ps -- sps)) (args_to_set (gs, bs, ps))"
      by (rule dgrad_p_set_le_subset, auto simp add: args_to_set_def set_diff_list)
  next
    from assms(4, 1, 5, 6) show "dgrad_p_set_le d (fst ` set hs) (args_to_set (gs, bs, ps))"
      unfolding assms(7) fst_set_add_indices by (rule compl_structD1)
  qed
  finally show ?thesis .
qed

corollary dgrad_p_set_le_args_to_set_struct:
  assumes "dickson_grading d" and "struct_spec sel ap ab compl" and "ps \<noteq> []"
  assumes "sps = sel gs bs ps data" and "hs = fst (add_indices (compl gs bs (ps -- sps) sps data) data)"
  shows "dgrad_p_set_le d (args_to_set (gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data')) (args_to_set (gs, bs, ps))"
proof -
  from assms(2) have sel: "sel_spec sel" and ap: "ap_spec ap" and ab: "ab_spec ab"
    and compl: "compl_struct compl" by (rule struct_specD)+
  from sel assms(3) have "sps \<noteq> []" and "set sps \<subseteq> set ps"
    unfolding assms(4) by (rule sel_specD1, rule sel_specD2)
  from assms(1) ap ab compl this assms(5) show ?thesis by (rule dgrad_p_set_le_args_to_set_ab)
qed

lemma components_subset_ab:
  assumes "ap_spec ap" and "ab_spec ab" and "compl_struct compl"
  assumes "sps \<noteq> []" and "set sps \<subseteq> set ps" and "hs = fst (add_indices (compl gs bs (ps -- sps) sps data) data)"
  shows "component_of_term ` Keys (args_to_set (gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data')) \<subseteq>
          component_of_term ` Keys (args_to_set (gs, bs, ps))" (is "?l \<subseteq> ?r")
proof -
  have "?l \<subseteq> component_of_term ` Keys (fst ` (set gs \<union> set bs \<union> fst ` set (ps -- sps) \<union> snd ` set (ps -- sps) \<union> set hs))"
    by (rule image_mono, rule Keys_mono, rule args_to_set_subset[OF assms(1, 2)])
  also have "... \<subseteq> ?r" unfolding image_Un Keys_Un Un_subset_iff
  proof (intro conjI)
    show "component_of_term ` Keys (fst ` set gs) \<subseteq> component_of_term ` Keys (args_to_set (gs, bs, ps))"
      by (rule image_mono, rule Keys_mono, auto simp add: args_to_set_def)
  next
    show "component_of_term ` Keys (fst ` set bs) \<subseteq> component_of_term ` Keys (args_to_set (gs, bs, ps))"
      by (rule image_mono, rule Keys_mono, auto simp add: args_to_set_def)
  next
    show "component_of_term ` Keys (fst ` fst ` set (ps -- sps)) \<subseteq> component_of_term ` Keys (args_to_set (gs, bs, ps))"
      by (rule image_mono, rule Keys_mono, auto simp add: set_diff_list args_to_set_def)
  next
    show "component_of_term ` Keys (fst ` snd ` set (ps -- sps)) \<subseteq> component_of_term ` Keys (args_to_set (gs, bs, ps))"
      by (rule image_mono, rule Keys_mono, auto simp add: args_to_set_def set_diff_list)
  next
    from assms(3, 4, 5) show "component_of_term ` Keys (fst ` set hs) \<subseteq> component_of_term ` Keys (args_to_set (gs, bs, ps))"
      unfolding assms(6) fst_set_add_indices by (rule compl_structD2)
  qed
  finally show ?thesis .
qed

corollary components_subset_struct:
  assumes "struct_spec sel ap ab compl" and "ps \<noteq> []"
  assumes "sps = sel gs bs ps data" and "hs = fst (add_indices (compl gs bs (ps -- sps) sps data) data)"
  shows "component_of_term ` Keys (args_to_set (gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data')) \<subseteq>
          component_of_term ` Keys (args_to_set (gs, bs, ps))"
proof -
  from assms(1) have sel: "sel_spec sel" and ap: "ap_spec ap" and ab: "ab_spec ab"
    and compl: "compl_struct compl" by (rule struct_specD)+
  from sel assms(2) have "sps \<noteq> []" and "set sps \<subseteq> set ps"
    unfolding assms(3) by (rule sel_specD1, rule sel_specD2)
  from ap ab compl this assms(4) show ?thesis by (rule components_subset_ab)
qed

corollary components_struct:
  assumes "struct_spec sel ap ab compl" and "ps \<noteq> []" and "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)"
  assumes "sps = sel gs bs ps data" and "hs = fst (add_indices (compl gs bs (ps -- sps) sps data) data)"
  shows "component_of_term ` Keys (args_to_set (gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data')) =
          component_of_term ` Keys (args_to_set (gs, bs, ps))" (is "?l = ?r")
proof
  from assms(1, 2, 4, 5) show "?l \<subseteq> ?r" by (rule components_subset_struct)
next
  from assms(1) have ap: "ap_spec ap" and ab: "ab_spec ab" and compl: "compl_struct compl"
    by (rule struct_specD)+
  from ap ab assms(3)
  have sub: "set (ap gs bs (ps -- sps) hs data') \<subseteq> set (ab gs bs hs data') \<times> (set gs \<union> set (ab gs bs hs data'))"
    by (rule subset_Times_ap)
  show "?r \<subseteq> ?l"
    by (simp add: args_to_set_subset_Times[OF sub] args_to_set_subset_Times[OF assms(3)] ab_specD1[OF ab],
        rule image_mono, rule Keys_mono, blast)
qed

lemma struct_spec_red_supset:
  assumes "struct_spec sel ap ab compl" and "ps \<noteq> []" and "sps = sel gs bs ps data"
    and "hs = fst (add_indices (compl gs bs (ps -- sps) sps data) data)" and "hs \<noteq> []"
  shows "(fst ` set (ab gs bs hs data')) \<sqsupset>p (fst ` set bs)"
proof -
  from assms(5) have "set hs \<noteq> {}" by simp
  then obtain h' where "h' \<in> set hs" by fastforce
  let ?h = "fst h'"
  let ?m = "monomial (lc ?h) (lt ?h)"
  from \<open>h' \<in> set hs\<close> have h_in: "?h \<in> fst ` set hs" by simp
  hence "?h \<in> fst ` set (fst (compl gs bs (ps -- sps) sps data))"
    by (simp only: assms(4) fst_set_add_indices)
  then obtain h'' where h''_in: "h'' \<in> set (fst (compl gs bs (ps -- sps) sps data))"
    and "?h = fst h''" ..
  from assms(1) have sel: "sel_spec sel" and ap: "ap_spec ap" and ab: "ab_spec ab"
    and compl: "compl_struct compl" by (rule struct_specD)+
  from sel assms(2) have "sps \<noteq> []" and "set sps \<subseteq> set ps" unfolding assms(3)
    by (rule sel_specD1, rule sel_specD2)
  from h_in compl_structD3[OF compl this] have "?h \<noteq> 0" unfolding assms(4) fst_set_add_indices
    by metis
  show ?thesis
  proof (simp add: ab_specD1[OF ab] image_Un, rule)
    fix q
    assume "is_red (fst ` set bs) q"
    moreover have "fst ` set bs \<subseteq> fst ` set bs \<union> fst ` set hs" by simp
    ultimately show "is_red (fst ` set bs \<union> fst ` set hs) q" by (rule is_red_subset)
  next
    from \<open>?h \<noteq> 0\<close> have "lc ?h \<noteq> 0" by (rule lc_not_0)
    moreover have "?h \<in> {?h}" ..
    ultimately have "is_red {?h} ?m" using \<open>?h \<noteq> 0\<close> adds_term_refl by (rule is_red_monomialI)
    moreover have "{?h} \<subseteq> fst ` set bs \<union> fst ` set hs" using h_in by simp
    ultimately show "is_red (fst ` set bs \<union> fst ` set hs) ?m" by (rule is_red_subset)
  next
    show "\<not> is_red (fst ` set bs) ?m"
    proof
      assume "is_red (fst ` set bs) ?m"
      then obtain b' where "b' \<in> fst ` set bs" and "b' \<noteq> 0" and "lt b' adds\<^sub>t lt ?h"
        by (rule is_red_monomialE)
      from this(1) obtain b where "b \<in> set bs" and b': "b' = fst b" ..
      from this(1) have "b \<in> set gs \<union> set bs" by simp
      from \<open>b' \<noteq> 0\<close> have "fst b \<noteq> 0" by (simp add: b')
      with compl \<open>sps \<noteq> []\<close> \<open>set sps \<subseteq> set ps\<close> h''_in \<open>b \<in> set gs \<union> set bs\<close> have "\<not> lt (fst b) adds\<^sub>t lt ?h"
        unfolding \<open>?h = fst h''\<close> by (rule compl_structD4)
      from this \<open>lt b' adds\<^sub>t lt ?h\<close> show False by (simp add: b')
    qed
  qed
qed

lemma unique_idx_append:
  assumes "unique_idx gs data" and "(hs, data') = add_indices aux data"
  shows "unique_idx (gs @ hs) data'"
proof -
  from assms(2) have hs: "hs = fst (add_indices aux data)" and data': "data' = snd (add_indices aux data)"
    by (metis fst_conv, metis snd_conv)
  have len: "length hs = length (fst aux)" by (simp add: hs add_indices_def)
  have eq: "fst data' = fst data + length hs" by (simp add: data' add_indices_def hs)
  show ?thesis
  proof (rule unique_idxI)
    fix f g
    assume "f \<in> set (gs @ hs)" and "g \<in> set (gs @ hs)"
    hence d1: "f \<in> set gs \<union> set hs" and d2: "g \<in> set gs \<union> set hs" by simp_all
    assume id_eq: "fst (snd f) = fst (snd g)"
    from d1 show "f = g"
    proof
      assume "f \<in> set gs"
      from d2 show ?thesis
      proof
        assume "g \<in> set gs"
        from assms(1) \<open>f \<in> set gs\<close> this id_eq show ?thesis by (rule unique_idxD1)
      next
        assume "g \<in> set hs"
        then obtain j where "g = (fst (fst aux ! j), fst data + j, snd (fst aux ! j))" unfolding hs
          by (rule in_set_add_indicesE)
        hence "fst (snd g) = fst data + j" by simp
        moreover from assms(1) \<open>f \<in> set gs\<close> have "fst (snd f) < fst data"
          by (rule unique_idxD2)
        ultimately show ?thesis by (simp add: id_eq)
      qed
    next
      assume "f \<in> set hs"
      then obtain i where f: "f = (fst (fst aux ! i), fst data + i, snd (fst aux ! i))" unfolding hs
        by (rule in_set_add_indicesE)
      hence *: "fst (snd f) = fst data + i" by simp
      from d2 show ?thesis
      proof
        assume "g \<in> set gs"
        with assms(1) have "fst (snd g) < fst data" by (rule unique_idxD2)
        with * show ?thesis by (simp add: id_eq)
      next
        assume "g \<in> set hs"
        then obtain j where g: "g = (fst (fst aux ! j), fst data + j, snd (fst aux ! j))" unfolding hs
          by (rule in_set_add_indicesE)
        hence "fst (snd g) = fst data + j" by simp
        with * have "i = j" by (simp add: id_eq)
        thus ?thesis by (simp add: f g)
      qed
    qed
  next
    fix f
    assume "f \<in> set (gs @ hs)"
    hence "f \<in> set gs \<union> set hs" by simp
    thus "fst (snd f) < fst data'"
    proof
      assume "f \<in> set gs"
      with assms(1) have "fst (snd f) < fst data" by (rule unique_idxD2)
      also have "... \<le> fst data'" by (simp add: eq)
      finally show ?thesis .
    next
      assume "f \<in> set hs"
      then obtain i where "i < length (fst aux)"
        and "f = (fst (fst aux ! i), fst data + i, snd (fst aux ! i))" unfolding hs
        by (rule in_set_add_indicesE)
      from this(2) have "fst (snd f) = fst data + i" by simp
      also from \<open>i < length (fst aux)\<close> have "... < fst data + length (fst aux)" by simp
      finally show ?thesis by (simp only: eq len)
    qed
  qed
qed

corollary unique_idx_ab:
  assumes "ab_spec ab" and "unique_idx (gs @ bs) data" and "(hs, data') = add_indices aux data"
  shows "unique_idx (gs @ ab gs bs hs data') data'"
proof -
  from assms(2, 3) have "unique_idx ((gs @ bs) @ hs) data'" by (rule unique_idx_append)
  thus ?thesis by (simp add: unique_idx_def ab_specD1[OF assms(1)])
qed

lemma rem_comps_spec_struct:
  assumes "struct_spec sel ap ab compl" and "rem_comps_spec (gs @ bs) data" and "ps \<noteq> []"
    and "set ps \<subseteq> (set bs) \<times> (set gs \<union> set bs)" and "sps = sel gs bs ps (snd data)"
    and "aux = compl gs bs (ps -- sps) sps (snd data)" and "(hs, data') = add_indices aux (snd data)"
  shows "rem_comps_spec (gs @ ab gs bs hs data') (fst data - count_const_lt_components (fst aux), data')"
proof -
  from assms(1) have sel: "sel_spec sel" and ap: "ap_spec ap" and ab: "ab_spec ab" and compl: "compl_struct compl"
    by (rule struct_specD)+
  from ap ab assms(4)
  have sub: "set (ap gs bs (ps -- sps) hs data') \<subseteq> set (ab gs bs hs data') \<times> (set gs \<union> set (ab gs bs hs data'))"
    by (rule subset_Times_ap)
  have hs: "hs = fst (add_indices aux (snd data))" by (simp add: assms(7)[symmetric])
  from sel assms(3) have "sps \<noteq> []" and "set sps \<subseteq> set ps" unfolding assms(5)
    by (rule sel_specD1, rule sel_specD2)
  have eq0: "fst ` set (fst aux) - {0} = fst ` set (fst aux)"
    by (rule Diff_triv, simp add: Int_insert_right assms(6), rule compl_structD3, fact+)
  have "component_of_term ` Keys (fst ` set (gs @ ab gs bs hs data')) =
        component_of_term ` Keys (args_to_set (gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data'))"
    by (simp add: args_to_set_subset_Times[OF sub] image_Un)
  also from assms(1, 3, 4, 5) hs
  have "... = component_of_term ` Keys (args_to_set (gs, bs, ps))" unfolding assms(6)
    by (rule components_struct)
  also have "... = component_of_term ` Keys (fst ` set (gs @ bs))"
    by (simp add: args_to_set_subset_Times[OF assms(4)] image_Un)
  finally have eq: "component_of_term ` Keys (fst ` set (gs @ ab gs bs hs data')) =
                      component_of_term ` Keys (fst ` set (gs @ bs))" .
  from assms(2)
  have eq2: "card (component_of_term ` Keys (fst ` set (gs @ bs))) =
             fst data + card (const_lt_component ` (fst ` set (gs @ bs) - {0}) - {None})" (is "?a = _ + ?b")
    by (simp only: rem_comps_spec_def)
  have eq3: "card (const_lt_component ` (fst ` set (gs @ ab gs bs hs data') - {0}) - {None}) =
              ?b + count_const_lt_components (fst aux)" (is "?c = _")
  proof (simp add: ab_specD1[OF ab] image_Un Un_assoc[symmetric] Un_Diff count_const_lt_components_alt
        hs fst_set_add_indices eq0, rule card_Un_disjoint)
    show "finite (const_lt_component ` (fst ` set gs - {0}) - {None} \<union> (const_lt_component ` (fst ` set bs - {0}) - {None}))"
      by (intro finite_UnI finite_Diff finite_imageI finite_set)
  next
    show "finite (const_lt_component ` fst ` set (fst aux) - {None})"
      by (rule finite_Diff, intro finite_imageI, fact finite_set)
  next
    have "(const_lt_component ` (fst ` (set gs \<union> set bs) - {0}) - {None}) \<inter>
          (const_lt_component ` fst ` set (fst aux) - {None}) =
          (const_lt_component ` (fst ` (set gs \<union> set bs) - {0}) \<inter>
          const_lt_component ` fst ` set (fst aux)) - {None}" by blast
    also have "... = {}"
    proof (simp, rule, simp, elim conjE)
      fix k
      assume "k \<in> const_lt_component ` (fst ` (set gs \<union> set bs) - {0})"
      then obtain b where "b \<in> set gs \<union> set bs" and "fst b \<noteq> 0" and k1: "k = const_lt_component (fst b)"
        by blast
      assume "k \<in> const_lt_component ` fst ` set (fst aux)"
      then obtain h where "h \<in> set (fst aux)" and k2: "k = const_lt_component (fst h)" by blast
      show "k = None"
      proof (rule ccontr, simp, elim exE)
        fix k'
        assume "k = Some k'"
        hence "lp (fst b) = 0" and "component_of_term (lt (fst b)) = k'" unfolding k1
          by (rule const_lt_component_SomeD1, rule const_lt_component_SomeD2)
        moreover from \<open>k = Some k'\<close> have "lp (fst h) = 0" and "component_of_term (lt (fst h)) = k'"
          unfolding k2 by (rule const_lt_component_SomeD1, rule const_lt_component_SomeD2)
        ultimately have "lt (fst b) adds\<^sub>t lt (fst h)" by (simp add: adds_term_def)
        moreover from compl \<open>sps \<noteq> []\<close> \<open>set sps \<subseteq> set ps\<close> \<open>h \<in> set (fst aux)\<close> \<open>b \<in> set gs \<union> set bs\<close> \<open>fst b \<noteq> 0\<close>
        have "\<not> lt (fst b) adds\<^sub>t lt (fst h)" unfolding assms(6) by (rule compl_structD4)
        ultimately show False by simp
      qed
    qed
    finally show "(const_lt_component ` (fst ` set gs - {0}) - {None} \<union> (const_lt_component ` (fst ` set bs - {0}) - {None})) \<inter>
          (const_lt_component ` fst ` set (fst aux) - {None}) = {}" by (simp only: Un_Diff image_Un)
  qed
  have "?c \<le> ?a" unfolding eq[symmetric]
    by (rule card_const_lt_component_le, rule finite_imageI, fact finite_set)
  hence le: "count_const_lt_components (fst aux) \<le> fst data" by (simp only: eq2 eq3)
  show ?thesis by (simp only: rem_comps_spec_def eq eq2 eq3, simp add: le)
qed

lemma pmdl_struct:
  assumes "struct_spec sel ap ab compl" and "compl_pmdl compl" and "is_Groebner_basis (fst ` set gs)"
    and "ps \<noteq> []" and "set ps \<subseteq> (set bs) \<times> (set gs \<union> set bs)" and "unique_idx (gs @ bs) (snd data)"
    and "sps = sel gs bs ps (snd data)" and "aux = compl gs bs (ps -- sps) sps (snd data)"
    and "(hs, data') = add_indices aux (snd data)"
  shows "pmdl (fst ` set (gs @ ab gs bs hs data')) = pmdl (fst ` set (gs @ bs))"
proof -
  have hs: "hs = fst (add_indices aux (snd data))" by (simp add: assms(9)[symmetric])
  from assms(1) have sel: "sel_spec sel" and ab: "ab_spec ab" by (rule struct_specD)+
  have eq: "fst ` (set gs \<union> set (ab gs bs hs data')) = fst ` (set gs \<union> set bs) \<union> fst ` set hs"
    by (auto simp add: ab_specD1[OF ab])
  show ?thesis
  proof (simp add: eq, rule)
    show "pmdl (fst ` (set gs \<union> set bs) \<union> fst ` set hs) \<subseteq> pmdl (fst ` (set gs \<union> set bs))"
    proof (rule pmdl.span_subset_spanI, simp only: Un_subset_iff, rule)
      show "fst ` (set gs \<union> set bs) \<subseteq> pmdl (fst ` (set gs \<union> set bs))"
        by (fact pmdl.span_superset)
    next
      from sel assms(4) have "sps \<noteq> []" and "set sps \<subseteq> set ps"
        unfolding assms(7) by (rule sel_specD1, rule sel_specD2)
      with assms(2, 3) have "fst ` set hs \<subseteq> pmdl (args_to_set (gs, bs, ps))"
        unfolding hs assms(8) fst_set_add_indices using assms(6) by (rule compl_pmdlD)
      thus "fst ` set hs \<subseteq> pmdl (fst ` (set gs \<union> set bs))"
        by (simp only: args_to_set_subset_Times[OF assms(5)] image_Un)
    qed
  next
    show "pmdl (fst ` (set gs \<union> set bs)) \<subseteq> pmdl (fst ` (set gs \<union> set bs) \<union> fst ` set hs)"
      by (rule pmdl.span_mono, blast)
  qed
qed


lemma discarded_subset:
  assumes "ab_spec ab"
    and "D' = D \<union> (set hs \<times> (set gs \<union> set bs \<union> set hs) \<union> set (ps -- sps) -\<^sub>p set (ap gs bs (ps -- sps) hs data'))"
    and "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)" and "D \<subseteq> (set gs \<union> set bs) \<times> (set gs \<union> set bs)"
  shows "D' \<subseteq> (set gs \<union> set (ab gs bs hs data')) \<times> (set gs \<union> set (ab gs bs hs data'))"
proof -
  from assms(1) have eq: "set (ab gs bs hs data') = set bs \<union> set hs" by (rule ab_specD1)
  from assms(4) have "D \<subseteq> (set gs \<union> (set bs \<union> set hs)) \<times> (set gs \<union> (set bs \<union> set hs))" by fastforce
  moreover have "set hs \<times> (set gs \<union> set bs \<union> set hs) \<union> set (ps -- sps) -\<^sub>p set (ap gs bs (ps -- sps) hs data') \<subseteq>
                  (set gs \<union> (set bs \<union> set hs)) \<times> (set gs \<union> (set bs \<union> set hs))" (is "?l \<subseteq> ?r")
  proof (rule subset_trans)
    show "?l \<subseteq> set hs \<times> (set gs \<union> set bs \<union> set hs) \<union> set (ps -- sps)"
      by (simp add: minus_pairs_def)
  next
    have "set hs \<times> (set gs \<union> set bs \<union> set hs) \<subseteq> ?r" by fastforce
    moreover have "set (ps -- sps) \<subseteq> ?r"
    proof (rule subset_trans)
      show "set (ps -- sps) \<subseteq> set ps" by (auto simp: set_diff_list)
    next
      from assms(3) show "set ps \<subseteq> ?r" by fastforce
    qed
    ultimately show "set hs \<times> (set gs \<union> set bs \<union> set hs) \<union> set (ps -- sps) \<subseteq> ?r" by (rule Un_least)
  qed
  ultimately show ?thesis unfolding eq assms(2) by (rule Un_least)
qed

lemma compl_struct_disjoint:
  assumes "compl_struct compl" and "sps \<noteq> []" and "set sps \<subseteq> set ps"
  shows "fst ` set (fst (compl gs bs (ps -- sps) sps data)) \<inter> fst ` (set gs \<union> set bs) = {}"
proof (rule, rule)
  fix x
  assume "x \<in> fst ` set (fst (compl gs bs (ps -- sps) sps data)) \<inter> fst ` (set gs \<union> set bs)"
  hence x_in: "x \<in> fst ` set (fst (compl gs bs (ps -- sps) sps data))" and "x \<in> fst ` (set gs \<union> set bs)"
    by simp_all
  from x_in obtain h where h_in: "h \<in> set (fst (compl gs bs (ps -- sps) sps data))" and x1: "x = fst h" ..
  from compl_structD3[OF assms, of gs bs data] x_in have "x \<noteq> 0" by auto
  from \<open>x \<in> fst ` (set gs \<union> set bs)\<close> obtain b where b_in: "b \<in> set gs \<union> set bs" and x2: "x = fst b" ..
  from \<open>x \<noteq> 0\<close> have "fst b \<noteq> 0" by (simp add: x2)
  with assms h_in b_in have "\<not> lt (fst b) adds\<^sub>t lt (fst h)" by (rule compl_structD4)
  hence "\<not> lt x adds\<^sub>t lt x" by (simp add: x1[symmetric] x2)
  from this adds_term_refl show "x \<in> {}" ..
qed simp

context
  fixes sel::"('t, 'b::field, 'c::default, 'd) selT" and ap::"('t, 'b, 'c, 'd) apT"
    and ab::"('t, 'b, 'c, 'd) abT" and compl::"('t, 'b, 'c, 'd) complT"
    and gs::"('t, 'b, 'c) pdata list"
begin

function (domintros) gb_schema_dummy :: "nat \<times> nat \<times> 'd \<Rightarrow> ('t, 'b, 'c) pdata_pair set \<Rightarrow>
                        ('t, 'b, 'c) pdata list \<Rightarrow> ('t, 'b, 'c) pdata_pair list \<Rightarrow>
                        (('t, 'b, 'c) pdata list \<times> ('t, 'b, 'c) pdata_pair set)"
  where
    "gb_schema_dummy data D bs ps =
        (if ps = [] then
          (gs @ bs, D)
        else
          (let sps = sel gs bs ps (snd data); ps0 = ps -- sps; aux = compl gs bs ps0 sps (snd data);
               remcomps = fst (data) - count_const_lt_components (fst aux) in
            (if remcomps = 0 then
              (full_gb (gs @ bs), D)
            else
              let (hs, data') = add_indices aux (snd data) in
                gb_schema_dummy (remcomps, data')
                  (D \<union> ((set hs \<times> (set gs \<union> set bs \<union> set hs) \<union> set (ps -- sps)) -\<^sub>p set (ap gs bs ps0 hs data')))
                  (ab gs bs hs data') (ap gs bs ps0 hs data')
            )
          )
        )"
  by pat_completeness auto

lemma gb_schema_dummy_domI1: "gb_schema_dummy_dom (data, D, bs, [])"
  by (rule gb_schema_dummy.domintros, simp)

lemma gb_schema_dummy_domI2:
  assumes "struct_spec sel ap ab compl"
  shows "gb_schema_dummy_dom (data, D, args)"
proof -
  from assms have sel: "sel_spec sel" and ap: "ap_spec ap" and ab: "ab_spec ab" by (rule struct_specD)+
  from ex_dgrad obtain d::"'a \<Rightarrow> nat" where dg: "dickson_grading d" ..
  let ?R = "(gb_schema_aux_term d gs)"
  from dg have "wf ?R" by (rule gb_schema_aux_term_wf)
  thus ?thesis
  proof (induct args arbitrary: data D rule: wf_induct_rule)
    fix x data D
    assume IH: "\<And>y data' D'. (y, x) \<in> ?R \<Longrightarrow> gb_schema_dummy_dom (data', D', y)"
    obtain bs ps where x: "x = (bs, ps)" by (meson case_prodE case_prodI2)
    show "gb_schema_dummy_dom (data, D, x)" unfolding x
    proof (rule gb_schema_dummy.domintros)
      fix rc0 n0 data0 hs n1 data1
      assume "ps \<noteq> []"
        and hs_data': "(hs, n1, data1) = add_indices (compl gs bs (ps -- sel gs bs ps (n0, data0))
                                               (sel gs bs ps (n0, data0)) (n0, data0)) (n0, data0)"
        and data: "data = (rc0, n0, data0)"
      define sps where "sps = sel gs bs ps (n0, data0)"
      define data' where "data' = (n1, data1)"
      define D' where "D' = D \<union>
         (set hs \<times> (set gs \<union> set bs \<union> set hs) \<union> set (ps -- sps) -\<^sub>p
          set (ap gs bs (ps -- sps) hs data'))"
      define rc where "rc = rc0 - count_const_lt_components (fst (compl gs bs (ps -- sel gs bs ps (n0, data0))
                                                                  (sel gs bs ps (n0, data0)) (n0, data0)))"
      from hs_data' have hs: "hs = fst (add_indices (compl gs bs (ps -- sps) sps (snd data)) (snd data))"
        unfolding sps_def data snd_conv by (metis fstI)
      show "gb_schema_dummy_dom ((rc, data'), D', ab gs bs hs data', ap gs bs (ps -- sps) hs data')"
      proof (rule IH, simp add: x gb_schema_aux_term_def gb_schema_aux_term1_def gb_schema_aux_term2_def, intro conjI)
        show "fst ` set (ab gs bs hs data') \<sqsupset>p fst ` set bs \<or>
                ab gs bs hs data' = bs \<and> card (set (ap gs bs (ps -- sps) hs data')) < card (set ps)"
        proof (cases "hs = []")
          case True
          have "ab gs bs hs data' = bs \<and> card (set (ap gs bs (ps -- sps) hs data')) < card (set ps)"
          proof (simp only: True, rule)
            from ab show "ab gs bs [] data' = bs" by (rule ab_specD2)
          next
            from sel \<open>ps \<noteq> []\<close> have "sps \<noteq> []" and "set sps \<subseteq> set ps"
              unfolding sps_def by (rule sel_specD1, rule sel_specD2)
            moreover from sel_specD1[OF sel \<open>ps \<noteq> []\<close>] have "set sps \<noteq> {}" by (simp add: sps_def)
            ultimately have "set ps \<inter> set sps \<noteq> {}" by (simp add: inf.absorb_iff2)
            hence "set (ps -- sps) \<subset> set ps" unfolding set_diff_list by fastforce
            hence "card (set (ps -- sps)) < card (set ps)" by (simp add: psubset_card_mono)
            moreover have "card (set (ap gs bs (ps -- sps) [] data')) \<le> card (set (ps -- sps))"
              by (rule card_mono, fact finite_set, rule ap_spec_Nil_subset, fact ap)
            ultimately show "card (set (ap gs bs (ps -- sps) [] data')) < card (set ps)" by simp
          qed
          thus ?thesis ..
        next
          case False
          with assms \<open>ps \<noteq> []\<close> sps_def hs have "fst ` set (ab gs bs hs data') \<sqsupset>p fst ` set bs"
            unfolding data snd_conv by (rule struct_spec_red_supset)
          thus ?thesis ..
        qed
      next
        from dg assms \<open>ps \<noteq> []\<close> sps_def hs
        show "dgrad_p_set_le d (args_to_set (gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data')) (args_to_set (gs, bs, ps))"
          unfolding data snd_conv by (rule dgrad_p_set_le_args_to_set_struct)
      next
        from assms \<open>ps \<noteq> []\<close> sps_def hs
        show "component_of_term ` Keys (args_to_set (gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data')) \<subseteq>
              component_of_term ` Keys (args_to_set (gs, bs, ps))"
          unfolding data snd_conv by (rule components_subset_struct)
      qed
    qed
  qed
qed

lemmas gb_schema_dummy_simp = gb_schema_dummy.psimps[OF gb_schema_dummy_domI2]

lemma gb_schema_dummy_Nil [simp]: "gb_schema_dummy data D bs [] = (gs @ bs, D)"
  by (simp add: gb_schema_dummy.psimps[OF gb_schema_dummy_domI1])

lemma gb_schema_dummy_not_Nil:
  assumes "struct_spec sel ap ab compl" and "ps \<noteq> []"
  shows "gb_schema_dummy data D bs ps =
          (let sps = sel gs bs ps (snd data); ps0 = ps -- sps; aux = compl gs bs ps0 sps (snd data);
               remcomps = fst (data) - count_const_lt_components (fst aux) in
            (if remcomps = 0 then
              (full_gb (gs @ bs), D)
            else
              let (hs, data') = add_indices aux (snd data) in
                gb_schema_dummy (remcomps, data')
                  (D \<union> ((set hs \<times> (set gs \<union> set bs \<union> set hs) \<union> set (ps -- sps)) -\<^sub>p set (ap gs bs ps0 hs data')))
                  (ab gs bs hs data') (ap gs bs ps0 hs data')
            )
          )"
  by (simp add: gb_schema_dummy_simp[OF assms(1)] assms(2))

lemma gb_schema_dummy_induct [consumes 1, case_names base rec1 rec2]:
  assumes "struct_spec sel ap ab compl"
  assumes base: "\<And>bs data D. P data D bs [] (gs @ bs, D)"
    and rec1: "\<And>bs ps sps data D. ps \<noteq> [] \<Longrightarrow> sps = sel gs bs ps (snd data) \<Longrightarrow>
                fst (data) \<le> count_const_lt_components (fst (compl gs bs (ps -- sps) sps (snd data))) \<Longrightarrow>
                P data D bs ps (full_gb (gs @ bs), D)"
    and rec2: "\<And>bs ps sps aux hs rc data data' D D'. ps \<noteq> [] \<Longrightarrow> sps = sel gs bs ps (snd data) \<Longrightarrow>
                aux = compl gs bs (ps -- sps) sps (snd data) \<Longrightarrow> (hs, data') = add_indices aux (snd data) \<Longrightarrow>
                rc = fst data - count_const_lt_components (fst aux) \<Longrightarrow> 0 < rc \<Longrightarrow>
                D' = (D \<union> ((set hs \<times> (set gs \<union> set bs \<union> set hs) \<union> set (ps -- sps)) -\<^sub>p set (ap gs bs (ps -- sps) hs data'))) \<Longrightarrow>
                P (rc, data') D' (ab gs bs hs data') (ap gs bs (ps -- sps) hs data')
                  (gb_schema_dummy (rc, data') D' (ab gs bs hs data') (ap gs bs (ps -- sps) hs data')) \<Longrightarrow>
                P data D bs ps (gb_schema_dummy (rc, data') D' (ab gs bs hs data') (ap gs bs (ps -- sps) hs data'))"
  shows "P data D bs ps (gb_schema_dummy data D bs ps)"
proof -
  from assms(1) have "gb_schema_dummy_dom (data, D, bs, ps)" by (rule gb_schema_dummy_domI2)
  thus ?thesis
  proof (induct data D bs ps rule: gb_schema_dummy.pinduct)
    case (1 data D bs ps)
    show ?case
    proof (cases "ps = []")
      case True
      show ?thesis by (simp add: True, rule base)
    next
      case False
      show ?thesis
      proof (simp only: gb_schema_dummy_not_Nil[OF assms(1) False] Let_def split: if_split, intro conjI impI)
        define sps where "sps = sel gs bs ps (snd data)"
        assume "fst data - count_const_lt_components (fst (compl gs bs (ps -- sps) sps (snd data))) = 0"
        hence "fst data \<le> count_const_lt_components (fst (compl gs bs (ps -- sps) sps (snd data)))"
          by simp
        with False sps_def show "P data D bs ps (full_gb (gs @ bs), D)" by (rule rec1)
      next
        define sps where "sps = sel gs bs ps (snd data)"
        define aux where "aux = compl gs bs (ps -- sps) sps (snd data)"
        define hs where "hs = fst (add_indices aux (snd data))"
        define data' where "data' = snd (add_indices aux (snd data))"
        define rc where "rc = fst data - count_const_lt_components (fst aux)"
        define D' where "D' = (D \<union> ((set hs \<times> (set gs \<union> set bs \<union> set hs) \<union> set (ps -- sps)) -\<^sub>p set (ap gs bs (ps -- sps) hs data')))"
        have eq: "add_indices aux (snd data) = (hs, data')" by (simp add: hs_def data'_def)
        assume "rc \<noteq> 0"
        hence "0 < rc" by simp
        show "P data D bs ps
           (case add_indices aux (snd data) of
            (hs, data') \<Rightarrow>
              gb_schema_dummy (rc, data')
               (D \<union> (set hs \<times> (set gs \<union> set bs \<union> set hs) \<union> set (ps -- sps) -\<^sub>p set (ap gs bs (ps -- sps) hs data')))
               (ab gs bs hs data') (ap gs bs (ps -- sps) hs data'))"
          unfolding eq prod.case D'_def[symmetric] using False sps_def aux_def eq[symmetric] rc_def \<open>0 < rc\<close> D'_def
        proof (rule rec2)
          show "P (rc, data') D' (ab gs bs hs data') (ap gs bs (ps -- sps) hs data')
                  (gb_schema_dummy (rc, data') D' (ab gs bs hs data') (ap gs bs (ps -- sps) hs data'))"
            unfolding D'_def using False sps_def refl aux_def rc_def \<open>rc \<noteq> 0\<close> eq[symmetric] refl
            by (rule 1)
        qed
      qed
    qed
  qed
qed

lemma fst_gb_schema_dummy_dgrad_p_set_le:
  assumes "dickson_grading d" and "struct_spec sel ap ab compl"
  shows "dgrad_p_set_le d (fst ` set (fst (gb_schema_dummy data D bs ps))) (args_to_set (gs, bs, ps))"
  using assms(2)
proof (induct rule: gb_schema_dummy_induct)
  case (base bs data D)
  show ?case by (simp add: args_to_set_def, rule dgrad_p_set_le_subset, fact subset_refl)
next
  case (rec1 bs ps sps data D)
  show ?case
  proof (cases "fst ` set gs \<union> fst ` set bs \<subseteq> {0}")
    case True
    hence "Keys (fst ` set (gs @ bs)) = {}" by (auto simp add: image_Un Keys_def)
    hence "component_of_term ` Keys (fst ` set (full_gb (gs @ bs))) = {}"
      by (simp add: components_full_gb)
    hence "Keys (fst ` set (full_gb (gs @ bs))) = {}" by simp
    thus ?thesis by (simp add: dgrad_p_set_le_def dgrad_set_le_def)
  next
    case False
    from pps_full_gb have "dgrad_set_le d (pp_of_term ` Keys (fst ` set (full_gb (gs @ bs)))) {0}"
      by (rule dgrad_set_le_subset)
    also have "dgrad_set_le d ... (pp_of_term ` Keys (args_to_set (gs, bs, ps)))"
    proof (rule dgrad_set_leI, simp)
      from False have "Keys (args_to_set (gs, bs, ps)) \<noteq> {}"
        by (simp add: args_to_set_alt Keys_Un, metis Keys_not_empty singletonI subsetI)
      then obtain v where "v \<in> Keys (args_to_set (gs, bs, ps))" by blast
      moreover have "d 0 \<le> d (pp_of_term v)" by (simp add: assms(1) dickson_grading_adds_imp_le)
      ultimately show "\<exists>t\<in>Keys (args_to_set (gs, bs, ps)). d 0 \<le> d (pp_of_term t)" ..
    qed
    finally show ?thesis by (simp add: dgrad_p_set_le_def)
  qed
next
  case (rec2 bs ps sps aux hs rc data data' D D')
  from rec2(4) have "hs = fst (add_indices (compl gs bs (ps -- sps) sps (snd data)) (snd data))"
    unfolding rec2(3) by (metis fstI)
  with assms rec2(1, 2)
  have "dgrad_p_set_le d (args_to_set (gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data')) (args_to_set (gs, bs, ps))"
    by (rule dgrad_p_set_le_args_to_set_struct)
  with rec2(8) show ?case by (rule dgrad_p_set_le_trans)
qed

lemma fst_gb_schema_dummy_components:
  assumes "struct_spec sel ap ab compl" and "set ps \<subseteq> (set bs) \<times> (set gs \<union> set bs)"
  shows "component_of_term ` Keys (fst ` set (fst (gb_schema_dummy data D bs ps))) =
          component_of_term ` Keys (args_to_set (gs, bs, ps))"
  using assms
proof (induct rule: gb_schema_dummy_induct)
  case (base bs data D)
  show ?case by (simp add: args_to_set_def)
next
  case (rec1 bs ps sps data D)
  have "component_of_term ` Keys (fst ` set (full_gb (gs @ bs))) =
        component_of_term ` Keys (fst ` set (gs @ bs))" by (fact components_full_gb)
  also have "... = component_of_term ` Keys (args_to_set (gs, bs, ps))"
    by (simp add: args_to_set_subset_Times[OF rec1.prems] image_Un)
  finally show ?case by simp
next
  case (rec2 bs ps sps aux hs rc data data' D D')
  from assms(1) have ap: "ap_spec ap" and ab: "ab_spec ab" by (rule struct_specD)+
  from this rec2.prems
  have sub: "set (ap gs bs (ps -- sps) hs data') \<subseteq> set (ab gs bs hs data') \<times> (set gs \<union> set (ab gs bs hs data'))"
    by (rule subset_Times_ap)
  from rec2(4) have hs: "hs = fst (add_indices (compl gs bs (ps -- sps) sps (snd data)) (snd data))"
    unfolding rec2(3) by (metis fstI)
  have "component_of_term ` Keys (args_to_set (gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data')) =
        component_of_term ` Keys (args_to_set (gs, bs, ps))" (is "?l = ?r")
  proof
    from assms(1) rec2(1, 2) hs show "?l \<subseteq> ?r" by (rule components_subset_struct)
  next
    show "?r \<subseteq> ?l"
      by (simp add: args_to_set_subset_Times[OF rec2.prems] args_to_set_alt2[OF ap ab rec2.prems] image_Un,
          rule image_mono, rule Keys_mono, blast)
  qed
  with rec2.hyps(8)[OF sub] show ?case by (rule trans)
qed

lemma fst_gb_schema_dummy_pmdl:
  assumes "struct_spec sel ap ab compl" and "compl_pmdl compl" and "is_Groebner_basis (fst ` set gs)"
    and "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)" and "unique_idx (gs @ bs) (snd data)"
    and "rem_comps_spec (gs @ bs) data"
  shows "pmdl (fst ` set (fst (gb_schema_dummy data D bs ps))) = pmdl (fst ` set (gs @ bs))"
proof -
  from assms(1) have sel: "sel_spec sel" and ap: "ap_spec ap" and ab: "ab_spec ab" and compl: "compl_struct compl"
    by (rule struct_specD)+
  from assms(1, 4, 5, 6) show ?thesis
  proof (induct bs ps rule: gb_schema_dummy_induct)
    case (base bs data D)
    show ?case by simp
  next
    case (rec1 bs ps sps data D)
    define aux where "aux = compl gs bs (ps -- sps) sps (snd data)"
    define data' where "data' = snd (add_indices aux (snd data))"
    define hs where "hs = fst (add_indices aux (snd data))"
    have hs_data': "(hs, data') = add_indices aux (snd data)" by (simp add: hs_def data'_def)
    have eq: "set (gs @ ab gs bs hs data') = set (gs @ bs @ hs)" by (simp add: ab_specD1[OF ab])
    from sel rec1(1) have "sps \<noteq> []" and "set sps \<subseteq> set ps" unfolding rec1(2)
      by (rule sel_specD1, rule sel_specD2)
    from full_gb_is_full_pmdl have "pmdl (fst ` set (full_gb (gs @ bs))) = pmdl (fst ` set (gs @ ab gs bs hs data'))"
    proof (rule is_full_pmdl_eq)
      show "is_full_pmdl (fst ` set (gs @ ab gs bs hs data'))"
      proof (rule is_full_pmdlI_lt_finite)
        from finite_set show "finite (fst ` set (gs @ ab gs bs hs data'))" by (rule finite_imageI)
      next
        fix k
        assume "k \<in> component_of_term ` Keys (fst ` set (gs @ ab gs bs hs data'))"
        hence "Some k \<in> Some ` component_of_term ` Keys (fst ` set (gs @ ab gs bs hs data'))" by simp
        also have "... = const_lt_component ` (fst ` set (gs @ ab gs bs hs data') - {0}) - {None}" (is "?A = ?B")
        proof (rule card_seteq[symmetric])
          show "finite ?A" by (intro finite_imageI finite_Keys, fact finite_set)
        next
          have "rem_comps_spec (gs @ ab gs bs hs data') (fst data - count_const_lt_components (fst aux), data')"
            using assms(1) rec1.prems(3) rec1.hyps(1) rec1.prems(1) rec1.hyps(2) aux_def hs_data'
            by (rule rem_comps_spec_struct)
          also have "... = (0, data')" by (simp add: aux_def rec1.hyps(3))
          finally have "card (const_lt_component ` (fst ` set (gs @ ab gs bs hs data') - {0}) - {None}) =
                        card (component_of_term ` Keys (fst ` set (gs @ ab gs bs hs data')))"
            by (simp add: rem_comps_spec_def)
          also have "... = card (Some ` component_of_term ` Keys (fst ` set (gs @ ab gs bs hs data')))"
            by (rule card_image[symmetric], simp)
          finally show "card ?A \<le> card ?B" by simp
        qed (fact const_lt_component_subset)
        finally have "Some k \<in> const_lt_component ` (fst ` set (gs @ ab gs bs hs data') - {0})"
          by simp
        then obtain b where "b \<in> fst ` set (gs @ ab gs bs hs data')" and "b \<noteq> 0"
          and *: "const_lt_component b = Some k" by fastforce
        show "\<exists>b\<in>fst ` set (gs @ ab gs bs hs data'). b \<noteq> 0 \<and> component_of_term (lt b) = k \<and> lp b = 0"
        proof (intro bexI conjI)
          from * show "component_of_term (lt b) = k" by (rule const_lt_component_SomeD2)
        next
          from * show "lp b = 0" by (rule const_lt_component_SomeD1)
        qed fact+
      qed
    next
      from compl \<open>sps \<noteq> []\<close> \<open>set sps \<subseteq> set ps\<close>
      have "component_of_term ` Keys (fst ` set hs) \<subseteq> component_of_term ` Keys (args_to_set (gs, bs, ps))"
        unfolding hs_def aux_def fst_set_add_indices by (rule compl_structD2)
      hence sub: "component_of_term ` Keys (fst ` set hs) \<subseteq> component_of_term ` Keys (fst ` set (gs @ bs))"
        by (simp add: args_to_set_subset_Times[OF rec1.prems(1)] image_Un)
      have "component_of_term ` Keys (fst ` set (full_gb (gs @ bs))) =
            component_of_term ` Keys (fst ` set (gs @ bs))" by (fact components_full_gb)
      also have "... = component_of_term ` Keys (fst ` set ((gs @ bs) @ hs))"
        by (simp only: set_append[of _ hs] image_Un Keys_Un Un_absorb2 sub)
      finally show "component_of_term ` Keys (fst ` set (full_gb (gs @ bs))) =
                    component_of_term ` Keys (fst ` set (gs @ ab gs bs hs data'))"
        by (simp only: eq append_assoc)
    qed
    also have "... = pmdl (fst ` set (gs @ bs))"
      using assms(1, 2, 3) rec1.hyps(1) rec1.prems(1, 2) rec1.hyps(2) aux_def hs_data'
      by (rule pmdl_struct)
    finally show ?case by simp
  next
    case (rec2 bs ps sps aux hs rc data data' D D')
    from rec2(4) have hs: "hs = fst (add_indices aux (snd data))" by (metis fstI)
    have "pmdl (fst ` set (fst (gb_schema_dummy (rc, data') D' (ab gs bs hs data') (ap gs bs (ps -- sps) hs data')))) =
          pmdl (fst ` set (gs @ ab gs bs hs data'))"
    proof (rule rec2.hyps(8))
      from ap ab rec2.prems(1)
      show "set (ap gs bs (ps -- sps) hs data') \<subseteq> set (ab gs bs hs data') \<times> (set gs \<union> set (ab gs bs hs data'))"
        by (rule subset_Times_ap)
    next
      from ab rec2.prems(2) rec2(4) show "unique_idx (gs @ ab gs bs hs data') (snd (rc, data'))"
        unfolding snd_conv by (rule unique_idx_ab)
    next
      show "rem_comps_spec (gs @ ab gs bs hs data') (rc, data')" unfolding rec2.hyps(5)
        using assms(1) rec2.prems(3) rec2.hyps(1) rec2.prems(1) rec2.hyps(2, 3, 4)
        by (rule rem_comps_spec_struct)
    qed
    also have "... = pmdl (fst ` set (gs @ bs))"
      using assms(1, 2, 3) rec2.hyps(1) rec2.prems(1, 2) rec2.hyps(2, 3, 4) by (rule pmdl_struct)
    finally show ?case .
  qed
qed

lemma snd_gb_schema_dummy_subset:
  assumes "struct_spec sel ap ab compl" and "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)"
    and "D \<subseteq> (set gs \<union> set bs) \<times> (set gs \<union> set bs)" and "res = gb_schema_dummy data D bs ps"
  shows "snd res \<subseteq> set (fst res) \<times> set (fst res) \<or> (\<exists>xs. fst (res) = full_gb xs)"
  using assms
proof (induct data D bs ps rule: gb_schema_dummy_induct)
  case (base bs data D)
  from base(2) show ?case by (simp add: base(3))
next
  case (rec1 bs ps sps data D)
  have "\<exists>xs. fst res = full_gb xs" by (auto simp: rec1(6))
  thus ?case ..
next
  case (rec2 bs ps sps aux hs rc data data' D D')
  from assms(1) have ab: "ab_spec ab" and ap: "ap_spec ap" by (rule struct_specD)+
  from _ _ rec2.prems(3) show ?case
  proof (rule rec2.hyps(8))
    from ap ab rec2.prems(1)
    show "set (ap gs bs (ps -- sps) hs data') \<subseteq> set (ab gs bs hs data') \<times> (set gs \<union> set (ab gs bs hs data'))"
      by (rule subset_Times_ap)
  next
    from ab rec2.hyps(7) rec2.prems(1) rec2.prems(2)
    show "D' \<subseteq> (set gs \<union> set (ab gs bs hs data')) \<times> (set gs \<union> set (ab gs bs hs data'))"
      by (rule discarded_subset)
  qed
qed

lemma gb_schema_dummy_connectible1:
  assumes "struct_spec sel ap ab compl" and "compl_conn compl" and "dickson_grading d"
    and "fst ` set gs \<subseteq> dgrad_p_set d m" and "is_Groebner_basis (fst ` set gs)"
    and "fst ` set bs \<subseteq> dgrad_p_set d m"
    and "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)"
    and "unique_idx (gs @ bs) (snd data)"
    and "\<And>p q. processed (p, q) (gs @ bs) ps \<Longrightarrow> (p, q) \<notin>\<^sub>p D \<Longrightarrow> fst p \<noteq> 0 \<Longrightarrow> fst q \<noteq> 0 \<Longrightarrow>
                crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs)) (fst p) (fst q)"
    and "\<not>(\<exists>xs. fst (gb_schema_dummy data D bs ps) = full_gb xs)"
  assumes "f \<in> set (fst (gb_schema_dummy data D bs ps))"
    and "g \<in> set (fst (gb_schema_dummy data D bs ps))"
    and "(f, g) \<notin>\<^sub>p snd (gb_schema_dummy data D bs ps)"
    and "fst f \<noteq> 0" and "fst g \<noteq> 0"
  shows "crit_pair_cbelow_on d m (fst ` set (fst (gb_schema_dummy data D bs ps))) (fst f) (fst g)"
  using assms(1, 6, 7, 8, 9, 10, 11, 12, 13)
proof (induct data D bs ps rule: gb_schema_dummy_induct)
  case (base bs data D)
  show ?case
  proof (cases "f \<in> set gs")
    case True
    show ?thesis
    proof (cases "g \<in> set gs")
      case True
      note assms(3, 4, 5)
      moreover from \<open>f \<in> set gs\<close> have "fst f \<in> fst ` set gs" by simp
      moreover from \<open>g \<in> set gs\<close> have "fst g \<in> fst ` set gs" by simp
      ultimately have "crit_pair_cbelow_on d m (fst ` set gs) (fst f) (fst g)"
        using assms(14, 15) by (rule GB_imp_crit_pair_cbelow_dgrad_p_set)
      moreover have "fst ` set gs \<subseteq> fst ` set (fst (gs @ bs, D))" by auto
      ultimately show ?thesis by (rule crit_pair_cbelow_mono)
    next
      case False
      from this base(6, 7) have "processed (g, f) (gs @ bs) []" by (simp add: processed_Nil)
      moreover from base.prems(8) have "(g, f) \<notin>\<^sub>p D" by (simp add: in_pair_iff)
      ultimately have "crit_pair_cbelow_on d m (fst ` set (gs @ bs)) (fst g) (fst f)"
        using \<open>fst g \<noteq> 0\<close> \<open>fst f \<noteq> 0\<close> unfolding set_append by (rule base(4))
      thus ?thesis unfolding fst_conv by (rule crit_pair_cbelow_sym)
    qed
  next
    case False
    from this base(6, 7) have "processed (f, g) (gs @ bs) []" by (simp add: processed_Nil)
    moreover from base.prems(8) have "(f, g) \<notin>\<^sub>p D" by simp
    ultimately show ?thesis unfolding fst_conv set_append using \<open>fst f \<noteq> 0\<close> \<open>fst g \<noteq> 0\<close> by (rule base(4))
  qed
next
  case (rec1 bs ps sps data D)
  from rec1.prems(5) show ?case by auto
next
  case (rec2 bs ps sps aux hs rc data data' D D')
  from rec2.hyps(4) have hs: "hs = fst (add_indices aux (snd data))" by (metis fstI)
  from assms(1) have sel: "sel_spec sel" and ap: "ap_spec ap" and ab: "ab_spec ab"
    and compl: "compl_struct compl"
    by (rule struct_specD1, rule struct_specD2, rule struct_specD3, rule struct_specD4)
  from sel rec2.hyps(1) have "sps \<noteq> []" and "set sps \<subseteq> set ps"
    unfolding rec2.hyps(2) by (rule sel_specD1, rule sel_specD2)
  from ap ab rec2.prems(2) have ap_sub: "set (ap gs bs (ps -- sps) hs data') \<subseteq>
                                    set (ab gs bs hs data') \<times> (set gs \<union> set (ab gs bs hs data'))"
    by (rule subset_Times_ap)
  have ns_sub: "fst ` set hs \<subseteq> dgrad_p_set d m"
  proof (rule dgrad_p_set_le_dgrad_p_set)
    from compl assms(3) \<open>sps \<noteq> []\<close> \<open>set sps \<subseteq> set ps\<close>
    show "dgrad_p_set_le d (fst ` set hs) (args_to_set (gs, bs, ps))"
      unfolding hs rec2.hyps(3) fst_set_add_indices by (rule compl_structD1)
  next
    from assms(4) rec2.prems(1) show "args_to_set (gs, bs, ps) \<subseteq> dgrad_p_set d m"
      by (simp add: args_to_set_subset_Times[OF rec2.prems(2)])
  qed
  with rec2.prems(1) have ab_sub: "fst ` set (ab gs bs hs data') \<subseteq> dgrad_p_set d m"
    by (auto simp add: ab_specD1[OF ab])

  have cpq: "(p, q) \<in>\<^sub>p set sps \<Longrightarrow> fst p \<noteq> 0 \<Longrightarrow> fst q \<noteq> 0 \<Longrightarrow>
              crit_pair_cbelow_on d m (fst ` (set gs \<union> set (ab gs bs hs data'))) (fst p) (fst q)" for p q
  proof -
    assume "(p, q) \<in>\<^sub>p set sps" and "fst p \<noteq> 0" and "fst q \<noteq> 0"
    from this(1) have "(p, q) \<in> set sps \<or> (q, p) \<in> set sps" by (simp only: in_pair_iff)
    hence "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> fst ` set (fst (compl gs bs (ps -- sps) sps (snd data))))
            (fst p) (fst q)"
    proof
      assume "(p, q) \<in> set sps"
      from assms(2, 3, 4, 5) rec2.prems(1, 2) \<open>sps \<noteq> []\<close> \<open>set sps \<subseteq> set ps\<close> rec2.prems(3) this
        \<open>fst p \<noteq> 0\<close> \<open>fst q \<noteq> 0\<close> show ?thesis by (rule compl_connD)
    next
      assume "(q, p) \<in> set sps"
      from assms(2, 3, 4, 5) rec2.prems(1, 2) \<open>sps \<noteq> []\<close> \<open>set sps \<subseteq> set ps\<close> rec2.prems(3) this
        \<open>fst q \<noteq> 0\<close> \<open>fst p \<noteq> 0\<close>
      have "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> fst ` set (fst (compl gs bs (ps -- sps) sps (snd data))))
            (fst q) (fst p)" by (rule compl_connD)
      thus ?thesis by (rule crit_pair_cbelow_sym)
    qed
    thus "crit_pair_cbelow_on d m (fst ` (set gs \<union> set (ab gs bs hs data'))) (fst p) (fst q)"
      by (simp add: ab_specD1[OF ab] hs rec2.hyps(3) fst_set_add_indices image_Un Un_assoc)
  qed

  from ab_sub ap_sub _ _ rec2.prems(5, 6, 7, 8) show ?case
  proof (rule rec2.hyps(8))
    from ab rec2.prems(3) rec2(4) show "unique_idx (gs @ ab gs bs hs data') (snd (rc, data'))"
      unfolding snd_conv by (rule unique_idx_ab)
  next
    fix p q :: "('t, 'b, 'c) pdata"
    define ps' where "ps' = ap gs bs (ps -- sps) hs data'"
    assume "fst p \<noteq> 0" and "fst q \<noteq> 0" and "(p, q) \<notin>\<^sub>p D'"
    assume "processed (p, q) (gs @ ab gs bs hs data') ps'"
    hence p_in: "p \<in> set gs \<union> set bs \<union> set hs" and q_in: "q \<in> set gs \<union> set bs \<union> set hs"
      and "(p, q) \<notin>\<^sub>p set ps'" by (simp_all add: processed_alt ab_specD1[OF ab])
    from this(3) \<open>(p, q) \<notin>\<^sub>p D'\<close> have "(p, q) \<notin>\<^sub>p D" and "(p, q) \<notin>\<^sub>p set (ps -- sps)"
      and "(p, q) \<notin>\<^sub>p set hs \<times> (set gs \<union> set bs \<union> set hs)"
      by (auto simp: in_pair_iff rec2.hyps(7) ps'_def)
    from this(3) p_in q_in have "p \<in> set gs \<union> set bs" and "q \<in> set gs \<union> set bs"
      by (meson SigmaI UnE in_pair_iff)+
    show "crit_pair_cbelow_on d m (fst ` (set gs \<union> set (ab gs bs hs data'))) (fst p) (fst q)"
    proof (cases "component_of_term (lt (fst p)) = component_of_term (lt (fst q))")
      case True
      show ?thesis
      proof (cases "(p, q) \<in>\<^sub>p set sps")
        case True
        from this \<open>fst p \<noteq> 0\<close> \<open>fst q \<noteq> 0\<close> show ?thesis by (rule cpq)
      next
        case False
        with \<open>(p, q) \<notin>\<^sub>p set (ps -- sps)\<close> have "(p, q) \<notin>\<^sub>p set ps"
          by (auto simp: in_pair_iff set_diff_list)
        with \<open>p \<in> set gs \<union> set bs\<close> \<open>q \<in> set gs \<union> set bs\<close> have "processed (p, q) (gs @ bs) ps"
          by (simp add: processed_alt)
        from this \<open>(p, q) \<notin>\<^sub>p D\<close> \<open>fst p \<noteq> 0\<close> \<open>fst q \<noteq> 0\<close>
        have "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs)) (fst p) (fst q)"
          by (rule rec2.prems(4))
        moreover have "fst ` (set gs \<union> set bs) \<subseteq> fst ` (set gs \<union> set (ab gs bs hs data'))"
          by (auto simp: ab_specD1[OF ab])
        ultimately show ?thesis by (rule crit_pair_cbelow_mono)
      qed
    next
      case False
      thus ?thesis by (rule crit_pair_cbelow_distinct_component)
    qed
  qed
qed

lemma gb_schema_dummy_connectible2:
  assumes "struct_spec sel ap ab compl" and "compl_conn compl" and "dickson_grading d"
    and "fst ` set gs \<subseteq> dgrad_p_set d m" and "is_Groebner_basis (fst ` set gs)"
    and "fst ` set bs \<subseteq> dgrad_p_set d m"
    and "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)" and "D \<subseteq> (set gs \<union> set bs) \<times> (set gs \<union> set bs)"
    and "set ps \<inter>\<^sub>p D = {}" and "unique_idx (gs @ bs) (snd data)"
    and "\<And>B a b. set gs \<union> set bs \<subseteq> B \<Longrightarrow> fst ` B \<subseteq> dgrad_p_set d m \<Longrightarrow> (a, b) \<in>\<^sub>p D \<Longrightarrow>
            fst a \<noteq> 0 \<Longrightarrow> fst b \<noteq> 0 \<Longrightarrow>
            (\<And>x y. x \<in> set gs \<union> set bs \<Longrightarrow> y \<in> set gs \<union> set bs \<Longrightarrow> \<not> (x, y) \<in>\<^sub>p D \<Longrightarrow>
              fst x \<noteq> 0 \<Longrightarrow> fst y \<noteq> 0 \<Longrightarrow> crit_pair_cbelow_on d m (fst ` B) (fst x) (fst y)) \<Longrightarrow>
            crit_pair_cbelow_on d m (fst ` B) (fst a) (fst b)"
    and "\<And>x y. x \<in> set (fst (gb_schema_dummy data D bs ps)) \<Longrightarrow> y \<in> set (fst (gb_schema_dummy data D bs ps)) \<Longrightarrow>
            (x, y) \<notin>\<^sub>p snd (gb_schema_dummy data D bs ps) \<Longrightarrow> fst x \<noteq> 0 \<Longrightarrow> fst y \<noteq> 0 \<Longrightarrow>
            crit_pair_cbelow_on d m (fst ` set (fst (gb_schema_dummy data D bs ps))) (fst x) (fst y)"
    and "\<not>(\<exists>xs. fst (gb_schema_dummy data D bs ps) = full_gb xs)"
  assumes "(f, g) \<in>\<^sub>p snd (gb_schema_dummy data D bs ps)"
    and "fst f \<noteq> 0" and "fst g \<noteq> 0"
  shows "crit_pair_cbelow_on d m (fst ` set (fst (gb_schema_dummy data D bs ps))) (fst f) (fst g)"
  using assms(1, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16)
proof (induct data D bs ps rule: gb_schema_dummy_induct)
  case (base bs data D)
  have "set gs \<union> set bs \<subseteq> set (fst (gs @ bs, D))" by simp
  moreover from assms(4) base.prems(1) have "fst ` set (fst (gs @ bs, D)) \<subseteq> dgrad_p_set d m" by auto
  moreover from base.prems(9) have "(f, g) \<in>\<^sub>p D" by simp
  moreover note assms(15, 16)
  ultimately show ?case
  proof (rule base.prems(6))
    fix x y
    assume "x \<in> set gs \<union> set bs" and "y \<in> set gs \<union> set bs" and "(x, y) \<notin>\<^sub>p D"
    hence "x \<in> set (fst (gs @ bs, D))" and "y \<in> set (fst (gs @ bs, D))" and "(x, y) \<notin>\<^sub>p snd (gs @ bs, D)"
      by simp_all
    moreover assume "fst x \<noteq> 0" and "fst y \<noteq> 0"
    ultimately show "crit_pair_cbelow_on d m (fst ` set (fst (gs @ bs, D))) (fst x) (fst y)"
      by (rule base.prems(7))
  qed
next
  case (rec1 bs ps sps data D)
  from rec1.prems(8) show ?case by auto
next
  case (rec2 bs ps sps aux hs rc data data' D D')
  from rec2.hyps(4) have hs: "hs = fst (add_indices aux (snd data))" by (metis fstI)
  from assms(1) have sel: "sel_spec sel" and ap: "ap_spec ap" and ab: "ab_spec ab"
    and compl: "compl_struct compl" by (rule struct_specD)+

  let ?X = "set (ps -- sps) \<union> set hs \<times> (set gs \<union> set bs \<union> set hs)"

  from sel rec2.hyps(1) have "sps \<noteq> []" and "set sps \<subseteq> set ps"
    unfolding rec2.hyps(2) by (rule sel_specD1, rule sel_specD2)

  have "fst ` set hs \<inter> fst ` (set gs \<union> set bs) = {}"
    unfolding hs fst_set_add_indices rec2.hyps(3) using compl \<open>sps \<noteq> []\<close> \<open>set sps \<subseteq> set ps\<close>
    by (rule compl_struct_disjoint)
  hence disj1: "(set gs \<union> set bs) \<inter> set hs = {}" by fastforce

  have disj2: "set (ap gs bs (ps -- sps) hs data') \<inter>\<^sub>p D' = {}"
  proof (rule, rule)
    fix x y
    assume "(x, y) \<in> set (ap gs bs (ps -- sps) hs data') \<inter>\<^sub>p D'"
    hence "(x, y) \<in>\<^sub>p set (ap gs bs (ps -- sps) hs data') \<inter>\<^sub>p D'" by (simp add: in_pair_alt)
    hence 1: "(x, y) \<in>\<^sub>p set (ap gs bs (ps -- sps) hs data')" and "(x, y) \<in>\<^sub>p D'" by simp_all
    hence "(x, y) \<in>\<^sub>p D" by (simp add: rec2.hyps(7))
    from this rec2.prems(3) have "x \<in> set gs \<union> set bs" and "y \<in> set gs \<union> set bs"
      by (auto simp: in_pair_iff)
    from 1 ap_specD1[OF ap] have "(x, y) \<in>\<^sub>p ?X" by (rule in_pair_trans)
    thus "(x, y) \<in> {}" unfolding in_pair_Un
    proof
      assume "(x, y) \<in>\<^sub>p set (ps -- sps)"
      also have "... \<subseteq> set ps" by (auto simp: set_diff_list)
      finally have "(x, y) \<in>\<^sub>p set ps \<inter>\<^sub>p D" using \<open>(x, y) \<in>\<^sub>p D\<close> by simp
      also have "... = {}" by (fact rec2.prems(4))
      finally show ?thesis by (simp add: in_pair_iff)
    next
      assume "(x, y) \<in>\<^sub>p set hs \<times> (set gs \<union> set bs \<union> set hs)"
      hence "x \<in> set hs \<or> y \<in> set hs" by (auto simp: in_pair_iff)
      thus ?thesis
      proof
        assume "x \<in> set hs"
        with \<open>x \<in> set gs \<union> set bs\<close> have "x \<in> (set gs \<union> set bs) \<inter> set hs" ..
        thus ?thesis by (simp add: disj1)
      next
        assume "y \<in> set hs"
        with \<open>y \<in> set gs \<union> set bs\<close> have "y \<in> (set gs \<union> set bs) \<inter> set hs" ..
        thus ?thesis by (simp add: disj1)
      qed
    qed
  qed simp

  have hs_sub: "fst ` set hs \<subseteq> dgrad_p_set d m"
  proof (rule dgrad_p_set_le_dgrad_p_set)
    from compl assms(3) \<open>sps \<noteq> []\<close> \<open>set sps \<subseteq> set ps\<close>
    show "dgrad_p_set_le d (fst ` set hs) (args_to_set (gs, bs, ps))"
      unfolding hs rec2.hyps(3) fst_set_add_indices by (rule compl_structD1)
  next
    from assms(4) rec2.prems(1) show "args_to_set (gs, bs, ps) \<subseteq> dgrad_p_set d m"
      by (simp add: args_to_set_subset_Times[OF rec2.prems(2)])
  qed
  with rec2.prems(1) have ab_sub: "fst ` set (ab gs bs hs data') \<subseteq> dgrad_p_set d m"
    by (auto simp add: ab_specD1[OF ab])

  moreover from ap ab rec2.prems(2)
  have ap_sub: "set (ap gs bs (ps -- sps) hs data') \<subseteq> set (ab gs bs hs data') \<times> (set gs \<union> set (ab gs bs hs data'))"
    by (rule subset_Times_ap)

  moreover from ab rec2.hyps(7) rec2.prems(2) rec2.prems(3)
  have "D' \<subseteq> (set gs \<union> set (ab gs bs hs data')) \<times> (set gs \<union> set (ab gs bs hs data'))"
    by (rule discarded_subset)

  moreover note disj2

  moreover from ab rec2.prems(5) rec2.hyps(4) have uid: "unique_idx (gs @ ab gs bs hs data') (snd (rc, data'))"
      unfolding snd_conv by (rule unique_idx_ab)

  ultimately show ?case using _ _ rec2.prems(8, 9, 10, 11)
  proof (rule rec2.hyps(8), simp only: ab_specD1[OF ab] Un_assoc[symmetric])
    define ps' where "ps' = ap gs bs (ps -- sps) hs data'"
    fix B a b
    assume B_sup: "set gs \<union> set bs \<union> set hs \<subseteq> B"
    hence "set gs \<union> set bs \<subseteq> B" and "set hs \<subseteq> B" by simp_all
    assume "(a, b) \<in>\<^sub>p D'"
    hence ab_cases: "(a, b) \<in>\<^sub>p D \<or> (a, b) \<in>\<^sub>p set hs \<times> (set gs \<union> set bs \<union> set hs) -\<^sub>p set ps' \<or>
                      (a, b) \<in>\<^sub>p set (ps -- sps) -\<^sub>p set ps'" by (auto simp: rec2.hyps(7) ps'_def)
    assume B_sub: "fst ` B \<subseteq> dgrad_p_set d m" and "fst a \<noteq> 0" and "fst b \<noteq> 0"
    assume *: "\<And>x y. x \<in> set gs \<union> set bs \<union> set hs \<Longrightarrow> y \<in> set gs \<union> set bs \<union> set hs \<Longrightarrow>
                     (x, y) \<notin>\<^sub>p D' \<Longrightarrow> fst x \<noteq> 0 \<Longrightarrow> fst y \<noteq> 0 \<Longrightarrow>
                     crit_pair_cbelow_on d m (fst ` B) (fst x) (fst y)"

    from rec2.prems(2) have ps_sps_sub: "set (ps -- sps) \<subseteq> set bs \<times> (set gs \<union> set bs)"
      by (auto simp: set_diff_list)
    from uid have uid': "unique_idx (gs @ bs @ hs) data'" by (simp add: unique_idx_def ab_specD1[OF ab])

    have a: "crit_pair_cbelow_on d m (fst ` B) (fst x) (fst y)"
      if "fst x \<noteq> 0" and "fst y \<noteq> 0" and xy_in: "(x, y) \<in>\<^sub>p set (ps -- sps) -\<^sub>p set ps'" for x y
    proof (cases "x = y")
      case True
      from xy_in rec2.prems(2) have "y \<in> set gs \<union> set bs"
        unfolding in_pair_minus_pairs unfolding True in_pair_iff set_diff_list by auto
      hence "fst y \<in> fst ` set gs \<union> fst ` set bs" by fastforce
      from this assms(4) rec2.prems(1) have "fst y \<in> dgrad_p_set d m" by blast
      with assms(3) show ?thesis unfolding True by (rule crit_pair_cbelow_same)
    next
      case False
      from ap assms(3) B_sup B_sub ps_sps_sub disj1 uid' assms(5) False \<open>fst x \<noteq> 0\<close> \<open>fst y \<noteq> 0\<close> xy_in
      show ?thesis unfolding ps'_def
      proof (rule ap_specD3)
        fix a1 b1 :: "('t, 'b, 'c) pdata"
        assume "fst a1 \<noteq> 0" and "fst b1 \<noteq> 0"
        assume "a1 \<in> set hs" and b1_in: "b1 \<in> set gs \<union> set bs \<union> set hs"
        hence a1_in: "a1 \<in> set gs \<union> set bs \<union> set hs" by fastforce
        assume "(a1, b1) \<in>\<^sub>p set (ap gs bs (ps -- sps) hs data')"
        hence "(a1, b1) \<in>\<^sub>p set ps'" by (simp only: ps'_def)
        with disj2 have "(a1, b1) \<notin>\<^sub>p D'" unfolding ps'_def
          by (metis empty_iff in_pair_Int_pairs in_pair_alt)
        with a1_in b1_in show "crit_pair_cbelow_on d m (fst ` B) (fst a1) (fst b1)"
          using \<open>fst a1 \<noteq> 0\<close> \<open>fst b1 \<noteq> 0\<close> by (rule *)
      qed
    qed

    have b: "crit_pair_cbelow_on d m (fst ` B) (fst x) (fst y)"
      if "(x, y) \<in>\<^sub>p D" and "fst x \<noteq> 0" and "fst y \<noteq> 0" for x y
      using \<open>set gs \<union> set bs \<subseteq> B\<close> B_sub that
    proof (rule rec2.prems(6))
      fix a1 b1 :: "('t, 'b, 'c) pdata"
      assume "a1 \<in> set gs \<union> set bs" and "b1 \<in> set gs \<union> set bs"
      hence a1_in: "a1 \<in> set gs \<union> set bs \<union> set hs" and b1_in: "b1 \<in> set gs \<union> set bs \<union> set hs"
        by fastforce+
      assume "(a1, b1) \<notin>\<^sub>p D" and "fst a1 \<noteq> 0" and "fst b1 \<noteq> 0"
      show "crit_pair_cbelow_on d m (fst ` B) (fst a1) (fst b1)"
      proof (cases "(a1, b1) \<in>\<^sub>p ?X -\<^sub>p set ps'")
        case True
        moreover from \<open>a1 \<in> set gs \<union> set bs\<close> \<open>b1 \<in> set gs \<union> set bs\<close> disj1
        have "(a1, b1) \<notin>\<^sub>p set hs \<times> (set gs \<union> set bs \<union> set hs)"
          by (auto simp: in_pair_def swap_def)
        ultimately have "(a1, b1) \<in>\<^sub>p set (ps -- sps) -\<^sub>p set ps'" by auto
        with \<open>fst a1 \<noteq> 0\<close> \<open>fst b1 \<noteq> 0\<close> show ?thesis by (rule a)
      next
        case False
        with \<open>(a1, b1) \<notin>\<^sub>p D\<close> have "(a1, b1) \<notin>\<^sub>p D'" by (auto simp: rec2.hyps(7) ps'_def)
        with a1_in b1_in show ?thesis using \<open>fst a1 \<noteq> 0\<close> \<open>fst b1 \<noteq> 0\<close> by (rule *)
      qed
    qed

    have c: "crit_pair_cbelow_on d m (fst ` B) (fst x) (fst y)"
      if x_in: "x \<in> set gs \<union> set bs \<union> set hs" and y_in: "y \<in> set gs \<union> set bs \<union> set hs"
      and xy: "(x, y) \<notin>\<^sub>p (?X -\<^sub>p set ps')" and "fst x \<noteq> 0" and "fst y \<noteq> 0" for x y
    proof (cases "(x, y) \<in>\<^sub>p D")
      case True
      thus ?thesis using \<open>fst x \<noteq> 0\<close> \<open>fst y \<noteq> 0\<close> by (rule b)
    next
      case False
      with xy have "(x, y) \<notin>\<^sub>p D'" unfolding rec2.hyps(7) ps'_def by auto
      with x_in y_in show ?thesis using \<open>fst x \<noteq> 0\<close> \<open>fst y \<noteq> 0\<close> by (rule *)
    qed

    from ab_cases show "crit_pair_cbelow_on d m (fst ` B) (fst a) (fst b)"
    proof (elim disjE)
      assume "(a, b) \<in>\<^sub>p D"
      thus ?thesis using \<open>fst a \<noteq> 0\<close> \<open>fst b \<noteq> 0\<close> by (rule b)
    next
      assume ab_in: "(a, b) \<in>\<^sub>p set hs \<times> (set gs \<union> set bs \<union> set hs) -\<^sub>p set ps'"
      hence ab_in': "(a, b) \<in>\<^sub>p set hs \<times> (set gs \<union> set bs \<union> set hs)" and "(a, b) \<notin>\<^sub>p set ps'" by simp_all
      show ?thesis
      proof (cases "a = b")
        case True
        from ab_in' rec2.prems(2) have "b \<in> set hs" unfolding True in_pair_iff set_diff_list by auto
        hence "fst b \<in> fst ` set hs" by fastforce
        from this hs_sub have "fst b \<in> dgrad_p_set d m" ..
        with assms(3) show ?thesis unfolding True by (rule crit_pair_cbelow_same)
      next
        case False
        from ap assms(3) B_sup B_sub ab_in' ps_sps_sub uid' assms(5) False \<open>fst a \<noteq> 0\<close> \<open>fst b \<noteq> 0\<close>
        show ?thesis
        proof (rule ap_specD2)
          fix x y :: "('t, 'b, 'c) pdata"
          assume "(x, y) \<in>\<^sub>p set (ap gs bs (ps -- sps) hs data')"
          also from ap_sub have "... \<subseteq> (set bs \<union> set hs) \<times> (set gs \<union> set bs \<union> set hs)"
            by (simp only: ab_specD1[OF ab] Un_assoc)
          also have "... \<subseteq> (set gs \<union> set bs \<union> set hs) \<times> (set gs \<union> set bs \<union> set hs)" by fastforce
          finally have "(x, y) \<in> (set gs \<union> set bs \<union> set hs) \<times> (set gs \<union> set bs \<union> set hs)"
            unfolding in_pair_same .
          hence "x \<in> set gs \<union> set bs \<union> set hs" and "y \<in> set gs \<union> set bs \<union> set hs" by simp_all
          moreover from \<open>(x, y) \<in>\<^sub>p set (ap gs bs (ps -- sps) hs data')\<close> have "(x, y) \<notin>\<^sub>p ?X -\<^sub>p set ps'"
            by (simp add: ps'_def)
          moreover assume "fst x \<noteq> 0" and "fst y \<noteq> 0"
          ultimately show "crit_pair_cbelow_on d m (fst ` B) (fst x) (fst y)" by (rule c)
        next
          fix x y :: "('t, 'b, 'c) pdata"
          assume "fst x \<noteq> 0" and "fst y \<noteq> 0"
          assume 1: "x \<in> set gs \<union> set bs" and 2: "y \<in> set gs \<union> set bs"
          hence x_in: "x \<in> set gs \<union> set bs \<union> set hs" and y_in: "y \<in> set gs \<union> set bs \<union> set hs" by simp_all
          show "crit_pair_cbelow_on d m (fst ` B) (fst x) (fst y)"
          proof (cases "(x, y) \<in>\<^sub>p set (ps -- sps) -\<^sub>p set ps'")
            case True
            with \<open>fst x \<noteq> 0\<close> \<open>fst y \<noteq> 0\<close> show ?thesis by (rule a)
          next
            case False
            have "(x, y) \<notin>\<^sub>p set (ps -- sps) \<union> set hs \<times> (set gs \<union> set bs \<union> set hs) -\<^sub>p set ps'"
            proof
              assume "(x, y) \<in>\<^sub>p set (ps -- sps) \<union> set hs \<times> (set gs \<union> set bs \<union> set hs) -\<^sub>p set ps'"
              hence "(x, y) \<in>\<^sub>p set hs \<times> (set gs \<union> set bs \<union> set hs)" using False
                by simp
              hence "x \<in> set hs \<or> y \<in> set hs" by (auto simp: in_pair_iff)
              with 1 2 disj1 show False by blast
            qed
            with x_in y_in show ?thesis using \<open>fst x \<noteq> 0\<close> \<open>fst y \<noteq> 0\<close> by (rule c)
          qed
        qed
      qed
    next
      assume "(a, b) \<in>\<^sub>p set (ps -- sps) -\<^sub>p set ps'"
      with \<open>fst a \<noteq> 0\<close> \<open>fst b \<noteq> 0\<close> show ?thesis by (rule a)
    qed
  next
    fix x y :: "('t, 'b, 'c) pdata"
    let ?res = "gb_schema_dummy (rc, data') D' (ab gs bs hs data') (ap gs bs (ps -- sps) hs data')"
    assume "x \<in> set (fst ?res)" and "y \<in> set (fst ?res)" and "(x, y) \<notin>\<^sub>p snd ?res" and "fst x \<noteq> 0" and "fst y \<noteq> 0"
    thus "crit_pair_cbelow_on d m (fst ` set (fst ?res)) (fst x) (fst y)" by (rule rec2.prems(7))
  qed
qed

corollary gb_schema_dummy_connectible:
  assumes "struct_spec sel ap ab compl" and "compl_conn compl" and "dickson_grading d"
    and "fst ` set gs \<subseteq> dgrad_p_set d m" and "is_Groebner_basis (fst ` set gs)"
    and "fst ` set bs \<subseteq> dgrad_p_set d m"
    and "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)" and "D \<subseteq> (set gs \<union> set bs) \<times> (set gs \<union> set bs)"
    and "set ps \<inter>\<^sub>p D = {}" and "unique_idx (gs @ bs) (snd data)"
    and "\<And>p q. processed (p, q) (gs @ bs) ps \<Longrightarrow> (p, q) \<notin>\<^sub>p D \<Longrightarrow> fst p \<noteq> 0 \<Longrightarrow> fst q \<noteq> 0 \<Longrightarrow>
            crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs)) (fst p) (fst q)"
    and "\<And>B a b. set gs \<union> set bs \<subseteq> B \<Longrightarrow> fst ` B \<subseteq> dgrad_p_set d m \<Longrightarrow> (a, b) \<in>\<^sub>p D \<Longrightarrow>
            fst a \<noteq> 0 \<Longrightarrow> fst b \<noteq> 0 \<Longrightarrow>
            (\<And>x y. x \<in> set gs \<union> set bs \<Longrightarrow> y \<in> set gs \<union> set bs \<Longrightarrow> \<not> (x, y) \<in>\<^sub>p D \<Longrightarrow>
              fst x \<noteq> 0 \<Longrightarrow> fst y \<noteq> 0 \<Longrightarrow> crit_pair_cbelow_on d m (fst ` B) (fst x) (fst y)) \<Longrightarrow>
            crit_pair_cbelow_on d m (fst ` B) (fst a) (fst b)"
  assumes "f \<in> set (fst (gb_schema_dummy data D bs ps))"
    and "g \<in> set (fst (gb_schema_dummy data D bs ps))"
    and "fst f \<noteq> 0" and "fst g \<noteq> 0"
  shows "crit_pair_cbelow_on d m (fst ` set (fst (gb_schema_dummy data D bs ps))) (fst f) (fst g)"
proof (cases "\<exists>xs. fst (gb_schema_dummy data D bs ps) = full_gb xs")
  case True
  then obtain xs where xs: "fst (gb_schema_dummy data D bs ps) = full_gb xs" ..
  note assms(3)
  moreover have "fst ` set (full_gb xs) \<subseteq> dgrad_p_set d m"
  proof (rule dgrad_p_set_le_dgrad_p_set)
    have "dgrad_p_set_le d (fst ` set (full_gb xs)) (args_to_set (gs, bs, ps))"
      unfolding xs[symmetric] using assms(3, 1) by (rule fst_gb_schema_dummy_dgrad_p_set_le)
    also from assms(7) have "... = fst ` set gs \<union> fst ` set bs" by (rule args_to_set_subset_Times)
    finally show "dgrad_p_set_le d (fst ` set (full_gb xs)) (fst ` set gs \<union> fst ` set bs)" .
  next
    from assms(4, 6) show "fst ` set gs \<union> fst ` set bs \<subseteq> dgrad_p_set d m" by blast
  qed
  moreover note full_gb_isGB
  moreover from assms(13) have "fst f \<in> fst ` set (full_gb xs)" by (simp add: xs)
  moreover from assms(14) have "fst g \<in> fst ` set (full_gb xs)" by (simp add: xs)
  ultimately show ?thesis using assms(15, 16) unfolding xs
    by (rule GB_imp_crit_pair_cbelow_dgrad_p_set)
next
  case not_full: False
  show ?thesis
  proof (cases "(f, g) \<in>\<^sub>p snd (gb_schema_dummy data D bs ps)")
    case True
    from assms(1-10,12) _ not_full True assms(15,16) show ?thesis
    proof (rule gb_schema_dummy_connectible2)
      fix x y
      assume "x \<in> set (fst (gb_schema_dummy data D bs ps))"
        and "y \<in> set (fst (gb_schema_dummy data D bs ps))"
        and "(x, y) \<notin>\<^sub>p snd (gb_schema_dummy data D bs ps)"
        and "fst x \<noteq> 0" and "fst y \<noteq> 0"
      with assms(1-7,10,11) not_full
      show "crit_pair_cbelow_on d m (fst ` set (fst (gb_schema_dummy data D bs ps))) (fst x) (fst y)"
        by (rule gb_schema_dummy_connectible1)
    qed
  next
    case False
    from assms(1-7,10,11) not_full assms(13,14) False assms(15,16) show ?thesis
      by (rule gb_schema_dummy_connectible1)
  qed
qed

lemma fst_gb_schema_dummy_dgrad_p_set_le_init:
  assumes "dickson_grading d" and "struct_spec sel ap ab compl"
  shows "dgrad_p_set_le d (fst ` set (fst (gb_schema_dummy data D (ab gs [] bs (snd data)) (ap gs [] [] bs (snd data)))))
                          (fst ` (set gs \<union> set bs))"
proof -
  let ?bs = "ab gs [] bs (snd data)"
  from assms(2) have ap: "ap_spec ap" and ab: "ab_spec ab" by (rule struct_specD)+
  from ap_specD1[OF ap, of gs "[]" "[]" bs]
  have *: "set (ap gs [] [] bs (snd data)) \<subseteq> set ?bs \<times> (set gs \<union> set ?bs)"
    by (simp add: ab_specD1[OF ab])
  from assms have "dgrad_p_set_le d (fst ` set (fst (gb_schema_dummy data D ?bs (ap gs [] [] bs (snd data)))))
                          (args_to_set (gs, ?bs, (ap gs [] [] bs (snd data))))"
    by (rule fst_gb_schema_dummy_dgrad_p_set_le)
  also have "... = fst ` (set gs \<union> set bs)"
    by (simp add: args_to_set_subset_Times[OF *] image_Un ab_specD1[OF ab])
  finally show ?thesis .
qed

corollary fst_gb_schema_dummy_dgrad_p_set_init:
  assumes "dickson_grading d" and "struct_spec sel ap ab compl"
    and "fst ` (set gs \<union> set bs) \<subseteq> dgrad_p_set d m"
  shows "fst ` set (fst (gb_schema_dummy (rc, data) D (ab gs [] bs data) (ap gs [] [] bs data))) \<subseteq> dgrad_p_set d m"
proof (rule dgrad_p_set_le_dgrad_p_set)
  let ?data = "(rc, data)"
  from assms(1, 2)
  have "dgrad_p_set_le d (fst ` set (fst (gb_schema_dummy ?data D (ab gs [] bs (snd ?data)) (ap gs [] [] bs (snd ?data)))))
          (fst ` (set gs \<union> set bs))"
    by (rule fst_gb_schema_dummy_dgrad_p_set_le_init)
  thus "dgrad_p_set_le d (fst ` set (fst (gb_schema_dummy ?data D (ab gs [] bs data) (ap gs [] [] bs data))))
          (fst ` (set gs \<union> set bs))"
    by (simp only: snd_conv)
qed fact

lemma fst_gb_schema_dummy_components_init:
  fixes bs data
  defines "bs0 \<equiv> ab gs [] bs data"
  defines "ps0 \<equiv> ap gs [] [] bs data"
  assumes "struct_spec sel ap ab compl"
  shows "component_of_term ` Keys (fst ` set (fst (gb_schema_dummy (rc, data) D bs0 ps0))) =
          component_of_term ` Keys (fst ` set (gs @ bs))" (is "?l = ?r")
proof -
  from assms(3) have ap: "ap_spec ap" and ab: "ab_spec ab" by (rule struct_specD)+
  from ap_specD1[OF ap, of gs "[]" "[]" bs]
  have *: "set ps0 \<subseteq> set bs0 \<times> (set gs \<union> set bs0)" by (simp add: ps0_def bs0_def ab_specD1[OF ab])
  with assms(3) have "?l = component_of_term ` Keys (args_to_set (gs, bs0, ps0))"
    by (rule fst_gb_schema_dummy_components)
  also have "... = ?r"
    by (simp only: args_to_set_subset_Times[OF *], simp add: ab_specD1[OF ab] bs0_def image_Un)
  finally show ?thesis .
qed

lemma fst_gb_schema_dummy_pmdl_init:
  fixes bs data
  defines "bs0 \<equiv> ab gs [] bs data"
  defines "ps0 \<equiv> ap gs [] [] bs data"
  assumes "struct_spec sel ap ab compl" and "compl_pmdl compl" and "is_Groebner_basis (fst ` set gs)"
    and "unique_idx (gs @ bs0) data" and "rem_comps_spec (gs @ bs0) (rc, data)"
  shows "pmdl (fst ` set (fst (gb_schema_dummy (rc, data) D bs0 ps0))) =
          pmdl (fst ` (set (gs @ bs)))" (is "?l = ?r")
proof -
  from assms(3) have ab: "ab_spec ab" by (rule struct_specD3)
  let ?data = "(rc, data)"
  from assms(6) have "unique_idx (gs @ bs0) (snd ?data)" by (simp only: snd_conv)
  from assms(3, 4, 5) _ this assms(7) have "?l = pmdl (fst ` (set (gs @ bs0)))"
  proof (rule fst_gb_schema_dummy_pmdl)
    from assms(3) have "ap_spec ap" by (rule struct_specD2)
    from ap_specD1[OF this, of gs "[]" "[]" bs]
    show "set ps0 \<subseteq> set bs0 \<times> (set gs \<union> set bs0)" by (simp add: ps0_def bs0_def ab_specD1[OF ab])
  qed
  also have "... = ?r" by (simp add: bs0_def ab_specD1[OF ab])
  finally show ?thesis .
qed

lemma fst_gb_schema_dummy_isGB_init:
  fixes bs data
  defines "bs0 \<equiv> ab gs [] bs data"
  defines "ps0 \<equiv> ap gs [] [] bs data"
  defines "D0 \<equiv> set bs \<times> (set gs \<union> set bs) -\<^sub>p set ps0"
  assumes "struct_spec sel ap ab compl" and "compl_conn compl" and "is_Groebner_basis (fst ` set gs)"
    and "unique_idx (gs @ bs0) data" and "rem_comps_spec (gs @ bs0) (rc, data)"
  shows "is_Groebner_basis (fst ` set (fst (gb_schema_dummy (rc, data) D0 bs0 ps0)))"
proof -
  let ?data = "(rc, data)"
  let ?res = "gb_schema_dummy ?data D0 bs0 ps0"
  from assms(4) have ap: "ap_spec ap" and ab: "ab_spec ab" by (rule struct_specD2, rule struct_specD3)
  have set_bs0: "set bs0 = set bs" by (simp add: bs0_def ab_specD1[OF ab])
  from ap_specD1[OF ap, of gs "[]" "[]" bs] have ps0_sub: "set ps0 \<subseteq> set bs0 \<times> (set gs \<union> set bs0)"
    by (simp add: ps0_def set_bs0)
  from ex_dgrad obtain d::"'a \<Rightarrow> nat" where dg: "dickson_grading d" ..
  have "finite (fst ` (set gs \<union> set bs))" by (rule, rule finite_UnI, fact finite_set, fact finite_set)
  then obtain m where gs_bs_sub: "fst ` (set gs \<union> set bs) \<subseteq> dgrad_p_set d m" by (rule dgrad_p_set_exhaust)
  with dg assms(4) have "fst ` set (fst ?res) \<subseteq> dgrad_p_set d m" unfolding bs0_def ps0_def
    by (rule fst_gb_schema_dummy_dgrad_p_set_init)
  with dg show ?thesis
  proof (rule crit_pair_cbelow_imp_GB_dgrad_p_set)
    fix p0 q0
    assume p0_in: "p0 \<in> fst ` set (fst ?res)" and q0_in: "q0 \<in> fst ` set (fst ?res)"
    assume "p0 \<noteq> 0" and "q0 \<noteq> 0"
    from \<open>fst ` (set gs \<union> set bs) \<subseteq> dgrad_p_set d m\<close>
    have "fst ` set gs \<subseteq> dgrad_p_set d m" and "fst ` set bs \<subseteq> dgrad_p_set d m"
      by (simp_all add: image_Un)
    from p0_in obtain p where p_in: "p \<in> set (fst ?res)" and p0: "p0 = fst p" ..
    from q0_in obtain q where q_in: "q \<in> set (fst ?res)" and q0: "q0 = fst q" ..
    from assms(7) have "unique_idx (gs @ bs0) (snd ?data)" by (simp only: snd_conv)
    from assms(4, 5) dg \<open>fst ` set gs \<subseteq> dgrad_p_set d m\<close> assms(6) _ ps0_sub _ _ this _ _ p_in q_in \<open>p0 \<noteq> 0\<close> \<open>q0 \<noteq> 0\<close>
    show "crit_pair_cbelow_on d m (fst ` set (fst ?res)) p0 q0" unfolding p0 q0
    proof (rule gb_schema_dummy_connectible)
      from \<open>fst ` set bs \<subseteq> dgrad_p_set d m\<close> show "fst ` set bs0 \<subseteq> dgrad_p_set d m"
        by (simp only: set_bs0)
    next
      have "D0 \<subseteq> set bs \<times> (set gs \<union> set bs)" by (auto simp: assms(3) minus_pairs_def)
      also have "... \<subseteq> (set gs \<union> set bs) \<times> (set gs \<union> set bs)" by fastforce
      finally show "D0 \<subseteq> (set gs \<union> set bs0) \<times> (set gs \<union> set bs0)" by (simp only: set_bs0)
    next
      show "set ps0 \<inter>\<^sub>p D0 = {}"
      proof
        show "set ps0 \<inter>\<^sub>p D0 \<subseteq> {}"
        proof
          fix x
          assume "x \<in> set ps0 \<inter>\<^sub>p D0"
          hence "x \<in>\<^sub>p set ps0 \<inter>\<^sub>p D0" by (simp add: in_pair_alt)
          thus "x \<in> {}" by (auto simp: assms(3))
        qed
      qed simp
    next
      fix p' q'
      assume "processed (p', q') (gs @ bs0) ps0"
      hence proc: "processed (p', q') (gs @ bs) ps0"
        by (simp add: set_bs0 processed_alt)
      hence "p' \<in> set gs \<union> set bs" and "q' \<in> set gs \<union> set bs" and "(p', q') \<notin>\<^sub>p set ps0"
        by (auto dest: processedD1 processedD2 processedD3)
      assume "(p', q') \<notin>\<^sub>p D0" and "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
      have "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs)) (fst p') (fst q')"
      proof (cases "p' = q'")
        case True
        from dg show ?thesis unfolding True
        proof (rule crit_pair_cbelow_same)
          from \<open>q' \<in> set gs \<union> set bs\<close> have "fst q' \<in> fst ` (set gs \<union> set bs)" by simp
          from this \<open>fst ` (set gs \<union> set bs) \<subseteq> dgrad_p_set d m\<close> show "fst q' \<in> dgrad_p_set d m" ..
        qed
      next
        case False
        show ?thesis
        proof (cases "component_of_term (lt (fst p')) = component_of_term (lt (fst q'))")
          case True
          show ?thesis
          proof (cases "p' \<in> set gs \<and> q' \<in> set gs")
            case True
            note dg \<open>fst ` set gs \<subseteq> dgrad_p_set d m\<close> assms(6)
            moreover from True have "fst p' \<in> fst ` set gs" and "fst q' \<in> fst ` set gs" by simp_all
            ultimately have "crit_pair_cbelow_on d m (fst ` set gs) (fst p') (fst q')"
              using \<open>fst p' \<noteq> 0\<close> \<open>fst q' \<noteq> 0\<close> by (rule GB_imp_crit_pair_cbelow_dgrad_p_set)
            moreover have "fst ` set gs \<subseteq> fst ` (set gs \<union> set bs)" by blast
            ultimately show ?thesis by (rule crit_pair_cbelow_mono)
          next
            case False
            with \<open>p' \<in> set gs \<union> set bs\<close> \<open>q' \<in> set gs \<union> set bs\<close>
            have "(p', q') \<in>\<^sub>p set bs \<times> (set gs \<union> set bs)" by (auto simp: in_pair_iff)
            with \<open>(p', q') \<notin>\<^sub>p D0\<close> have "(p', q') \<in>\<^sub>p set ps0" by (simp add: assms(3))
            with \<open>(p', q') \<notin>\<^sub>p set ps0\<close> show ?thesis ..
          qed
        next
          case False
          thus ?thesis by (rule crit_pair_cbelow_distinct_component)
        qed
      qed
      thus "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs0)) (fst p') (fst q')"
        by (simp only: set_bs0)
    next
      fix B a b
      assume "set gs \<union> set bs0 \<subseteq> B"
      hence B_sup: "set gs \<union> set bs \<subseteq> B" by (simp only: set_bs0)
      assume B_sub: "fst ` B \<subseteq> dgrad_p_set d m"
      assume "(a, b) \<in>\<^sub>p D0"
      hence ab_in: "(a, b) \<in>\<^sub>p set bs \<times> (set gs \<union> set bs)" and "(a, b) \<notin>\<^sub>p set ps0"
        by (simp_all add: assms(3))
      assume "fst a \<noteq> 0" and "fst b \<noteq> 0"
      assume *: "\<And>x y. x \<in> set gs \<union> set bs0 \<Longrightarrow> y \<in> set gs \<union> set bs0 \<Longrightarrow> (x, y) \<notin>\<^sub>p D0 \<Longrightarrow>
                    fst x \<noteq> 0 \<Longrightarrow> fst y \<noteq> 0 \<Longrightarrow> crit_pair_cbelow_on d m (fst ` B) (fst x) (fst y)"
      show "crit_pair_cbelow_on d m (fst ` B) (fst a) (fst b)"
      proof (cases "a = b")
        case True
        from ab_in have "b \<in> set gs \<union> set bs" unfolding True in_pair_iff set_diff_list by auto
        hence "fst b \<in> fst ` (set gs \<union> set bs)" by fastforce
        from this gs_bs_sub have "fst b \<in> dgrad_p_set d m" ..
        with dg show ?thesis unfolding True by (rule crit_pair_cbelow_same)
      next
        case False
        note ap dg
        moreover from B_sup have B_sup': "set gs \<union> set [] \<union> set bs \<subseteq> B" by simp
        moreover note B_sub
        moreover from ab_in have "(a, b) \<in>\<^sub>p set bs \<times> (set gs \<union> set [] \<union> set bs)" by simp
        moreover have "set [] \<subseteq> set [] \<times> (set gs \<union> set [])" by simp
        moreover from assms(7) have "unique_idx (gs @ [] @ bs) data" by (simp add: unique_idx_def set_bs0)
        ultimately show ?thesis using assms(6) False \<open>fst a \<noteq> 0\<close> \<open>fst b \<noteq> 0\<close>
        proof (rule ap_specD2)
          fix x y :: "('t, 'b, 'c) pdata"
          assume "(x, y) \<in>\<^sub>p set (ap gs [] [] bs data)"
          hence "(x, y) \<in>\<^sub>p set ps0" by (simp only: ps0_def)
          also have "... \<subseteq> set bs0 \<times> (set gs \<union> set bs0)" by (fact ps0_sub)
          also have "... \<subseteq> (set gs \<union> set bs0) \<times> (set gs \<union> set bs0)" by fastforce
          finally have "(x, y) \<in> (set gs \<union> set bs0) \<times> (set gs \<union> set bs0)" by (simp only: in_pair_same)
          hence "x \<in> set gs \<union> set bs0" and "y \<in> set gs \<union> set bs0" by simp_all
          moreover from \<open>(x, y) \<in>\<^sub>p set ps0\<close> have "(x, y) \<notin>\<^sub>p D0" by (simp add: D0_def)
          moreover assume "fst x \<noteq> 0" and "fst y \<noteq> 0"
          ultimately show "crit_pair_cbelow_on d m (fst ` B) (fst x) (fst y)" by (rule *)
        next
          fix x y :: "('t, 'b, 'c) pdata"
          assume "x \<in> set gs \<union> set []" and "y \<in> set gs \<union> set []"
          hence "fst x \<in> fst ` set gs" and "fst y \<in> fst ` set gs" by simp_all
          assume "fst x \<noteq> 0" and "fst y \<noteq> 0"
          with dg \<open>fst ` set gs \<subseteq> dgrad_p_set d m\<close> assms(6) \<open>fst x \<in> fst ` set gs\<close> \<open>fst y \<in> fst ` set gs\<close>
          have "crit_pair_cbelow_on d m (fst ` set gs) (fst x) (fst y)"
            by (rule GB_imp_crit_pair_cbelow_dgrad_p_set)
          moreover from B_sup have "fst ` set gs \<subseteq> fst ` B" by fastforce
          ultimately show "crit_pair_cbelow_on d m (fst ` B) (fst x) (fst y)"
            by (rule crit_pair_cbelow_mono)
        qed
      qed
    qed
  qed
qed

subsubsection \<open>Function \<open>gb_schema_aux\<close>\<close>

function (domintros) gb_schema_aux :: "nat \<times> nat \<times> 'd \<Rightarrow> ('t, 'b, 'c) pdata list \<Rightarrow>
                        ('t, 'b, 'c) pdata_pair list \<Rightarrow> ('t, 'b, 'c) pdata list"
  where
    "gb_schema_aux data bs ps =
        (if ps = [] then
          gs @ bs
        else
          (let sps = sel gs bs ps (snd data); ps0 = ps -- sps; aux = compl gs bs ps0 sps (snd data);
               remcomps = fst (data) - count_const_lt_components (fst aux) in
            (if remcomps = 0 then
              full_gb (gs @ bs)
            else
              let (hs, data') = add_indices aux (snd data) in
                gb_schema_aux (remcomps, data') (ab gs bs hs data') (ap gs bs ps0 hs data')
            )
          )
        )"
  by pat_completeness auto

text \<open>The \<open>data\<close> parameter of @{const gb_schema_aux} is a triple \<open>(c, i, d)\<close>, where \<open>c\<close> is the
  number of components \<open>cmp\<close> of the input list for which the current basis \<open>gs @ bs\<close> does @{emph \<open>not\<close>}
  yet contain an element whose leading power-product is \<open>0\<close> and has component \<open>cmp\<close>. As soon as \<open>c\<close>
  gets \<open>0\<close>, the function can return a trivial Gr\"obner basis, since then the submodule generated by
  the input list is just the full module. This idea generalizes the well-known fact that if a set of
  scalar polynomials contains a non-zero constant, the ideal generated by that set is the whole ring.
  \<open>i\<close> is the total number of polynomials generated during the execution of the function so far; it
  is used to attach unique indices to the polynomials for fast equality tests.
  \<open>d\<close>, finally, is some arbitrary data-field that may be used by concrete instances of
  @{const gb_schema_aux} for storing information.\<close>

lemma gb_schema_aux_domI1: "gb_schema_aux_dom (data, bs, [])"
  by (rule gb_schema_aux.domintros, simp)

lemma gb_schema_aux_domI2:
  assumes "struct_spec sel ap ab compl"
  shows "gb_schema_aux_dom (data, args)"
proof -
  from assms have sel: "sel_spec sel" and ap: "ap_spec ap" and ab: "ab_spec ab" by (rule struct_specD)+
  from ex_dgrad obtain d::"'a \<Rightarrow> nat" where dg: "dickson_grading d" ..
  let ?R = "gb_schema_aux_term d gs"
  from dg have "wf ?R" by (rule gb_schema_aux_term_wf)
  thus ?thesis
  proof (induct args arbitrary: data rule: wf_induct_rule)
    fix x data
    assume IH: "\<And>y data'. (y, x) \<in> ?R \<Longrightarrow> gb_schema_aux_dom (data', y)"
    obtain bs ps where x: "x = (bs, ps)" by (meson case_prodE case_prodI2)
    show "gb_schema_aux_dom (data, x)" unfolding x
    proof (rule gb_schema_aux.domintros)
      fix rc0 n0 data0 hs n1 data1
      assume "ps \<noteq> []"
        and hs_data': "(hs, n1, data1) = add_indices (compl gs bs (ps -- sel gs bs ps (n0, data0))
                                               (sel gs bs ps (n0, data0)) (n0, data0)) (n0, data0)"
        and data: "data = (rc0, n0, data0)"
      define sps where "sps = sel gs bs ps (n0, data0)"
      define data' where "data' = (n1, data1)"
      define rc where "rc = rc0 - count_const_lt_components (fst (compl gs bs (ps -- sel gs bs ps (n0, data0))
                                                                  (sel gs bs ps (n0, data0)) (n0, data0)))"
      from hs_data' have hs: "hs = fst (add_indices (compl gs bs (ps -- sps) sps (snd data)) (snd data))"
        unfolding sps_def data snd_conv by (metis fstI)
      show "gb_schema_aux_dom ((rc, data'), ab gs bs hs data', ap gs bs (ps -- sps) hs data')"
      proof (rule IH, simp add: x gb_schema_aux_term_def gb_schema_aux_term1_def gb_schema_aux_term2_def, intro conjI)
        show "fst ` set (ab gs bs hs data') \<sqsupset>p fst ` set bs \<or>
                ab gs bs hs data' = bs \<and> card (set (ap gs bs (ps -- sps) hs data')) < card (set ps)"
        proof (cases "hs = []")
          case True
          have "ab gs bs hs data' = bs \<and> card (set (ap gs bs (ps -- sps) hs data')) < card (set ps)"
          proof (simp only: True, rule)
            from ab show "ab gs bs [] data' = bs" by (rule ab_specD2)
          next
            from sel \<open>ps \<noteq> []\<close> have "sps \<noteq> []" and "set sps \<subseteq> set ps"
              unfolding sps_def by (rule sel_specD1, rule sel_specD2)
            moreover from sel_specD1[OF sel \<open>ps \<noteq> []\<close>] have "set sps \<noteq> {}" by (simp add: sps_def)
            ultimately have "set ps \<inter> set sps \<noteq> {}" by (simp add: inf.absorb_iff2)
            hence "set (ps -- sps) \<subset> set ps" unfolding set_diff_list by fastforce
            hence "card (set (ps -- sps)) < card (set ps)" by (simp add: psubset_card_mono)
            moreover have "card (set (ap gs bs (ps -- sps) [] data')) \<le> card (set (ps -- sps))"
              by (rule card_mono, fact finite_set, rule ap_spec_Nil_subset, fact ap)
            ultimately show "card (set (ap gs bs (ps -- sps) [] data')) < card (set ps)" by simp
          qed
          thus ?thesis ..
        next
          case False
          with assms \<open>ps \<noteq> []\<close> sps_def hs have "fst ` set (ab gs bs hs data') \<sqsupset>p fst ` set bs"
            unfolding data snd_conv by (rule struct_spec_red_supset)
          thus ?thesis ..
        qed
      next
        from dg assms \<open>ps \<noteq> []\<close> sps_def hs
        show "dgrad_p_set_le d (args_to_set (gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data')) (args_to_set (gs, bs, ps))"
          unfolding data snd_conv by (rule dgrad_p_set_le_args_to_set_struct)
      next
        from assms \<open>ps \<noteq> []\<close> sps_def hs
        show "component_of_term ` Keys (args_to_set (gs, ab gs bs hs data', ap gs bs (ps -- sps) hs data')) \<subseteq>
              component_of_term ` Keys (args_to_set (gs, bs, ps))"
          unfolding data snd_conv by (rule components_subset_struct)
      qed
    qed
  qed
qed

lemma gb_schema_aux_Nil [simp, code]: "gb_schema_aux data bs [] = gs @ bs"
  by (simp add: gb_schema_aux.psimps[OF gb_schema_aux_domI1])

lemmas gb_schema_aux_simps = gb_schema_aux.psimps[OF gb_schema_aux_domI2]

lemma gb_schema_aux_induct [consumes 1, case_names base rec1 rec2]:
  assumes "struct_spec sel ap ab compl"
  assumes base: "\<And>bs data. P data bs [] (gs @ bs)"
    and rec1: "\<And>bs ps sps data. ps \<noteq> [] \<Longrightarrow> sps = sel gs bs ps (snd data) \<Longrightarrow>
                fst (data) \<le> count_const_lt_components (fst (compl gs bs (ps -- sps) sps (snd data))) \<Longrightarrow>
                P data bs ps (full_gb (gs @ bs))"
    and rec2: "\<And>bs ps sps aux hs rc data data'. ps \<noteq> [] \<Longrightarrow> sps = sel gs bs ps (snd data) \<Longrightarrow>
                aux = compl gs bs (ps -- sps) sps (snd data) \<Longrightarrow> (hs, data') = add_indices aux (snd data) \<Longrightarrow>
                rc = fst data - count_const_lt_components (fst aux) \<Longrightarrow> 0 < rc \<Longrightarrow>
                P (rc, data') (ab gs bs hs data') (ap gs bs (ps -- sps) hs data')
                  (gb_schema_aux (rc, data') (ab gs bs hs data') (ap gs bs (ps -- sps) hs data')) \<Longrightarrow>
                P data bs ps (gb_schema_aux (rc, data') (ab gs bs hs data') (ap gs bs (ps -- sps) hs data'))"
  shows "P data bs ps (gb_schema_aux data bs ps)"
proof -
  from assms(1) have "gb_schema_aux_dom (data, bs, ps)" by (rule gb_schema_aux_domI2)
  thus ?thesis
  proof (induct data bs ps rule: gb_schema_aux.pinduct)
    case (1 data bs ps)
    show ?case
    proof (cases "ps = []")
      case True
      show ?thesis by (simp add: True, rule base)
    next
      case False
      show ?thesis
      proof (simp add: gb_schema_aux_simps[OF assms(1), of data bs ps] False Let_def split: if_split,
            intro conjI impI)
        define sps where "sps = sel gs bs ps (snd data)"
        assume "fst data \<le> count_const_lt_components (fst (compl gs bs (ps -- sps) sps (snd data)))"
        with False sps_def show "P data bs ps (full_gb (gs @ bs))" by (rule rec1)
      next
        define sps where "sps = sel gs bs ps (snd data)"
        define aux where "aux = compl gs bs (ps -- sps) sps (snd data)"
        define hs where "hs = fst (add_indices aux (snd data))"
        define data' where "data' = snd (add_indices aux (snd data))"
        define rc where "rc = fst data - count_const_lt_components (fst aux)"
        have eq: "add_indices aux (snd data) = (hs, data')" by (simp add: hs_def data'_def)
        assume "\<not> fst data \<le> count_const_lt_components (fst aux)"
        hence "0 < rc" by (simp add: rc_def)
        hence "rc \<noteq> 0" by simp
        show "P data bs ps
           (case add_indices aux (snd data) of
            (hs, data') \<Rightarrow> gb_schema_aux (rc, data') (ab gs bs hs data') (ap gs bs (ps -- sps) hs data'))"
          unfolding eq prod.case using False sps_def aux_def eq[symmetric] rc_def \<open>0 < rc\<close>
        proof (rule rec2)
          show "P (rc, data') (ab gs bs hs data') (ap gs bs (ps -- sps) hs data')
                  (gb_schema_aux (rc, data') (ab gs bs hs data') (ap gs bs (ps -- sps) hs data'))"
            using False sps_def refl aux_def rc_def \<open>rc \<noteq> 0\<close> eq[symmetric] refl by (rule 1)
        qed
      qed
    qed
  qed
qed

lemma gb_schema_dummy_eq_gb_schema_aux:
  assumes "struct_spec sel ap ab compl"
  shows "fst (gb_schema_dummy data D bs ps) = gb_schema_aux data bs ps"
  using assms
proof (induct data D bs ps rule: gb_schema_dummy_induct)
  case (base bs data D)
  show ?case by simp
next
  case (rec1 bs ps sps data D)
  thus ?case by (simp add: gb_schema_aux.psimps[OF gb_schema_aux_domI2, OF assms])
next
  case (rec2 bs ps sps aux hs rc data data' D D')
  note rec2.hyps(8)
  also from rec2.hyps(1, 2, 3) rec2.hyps(4)[symmetric] rec2.hyps(5, 6, 7)
  have "gb_schema_aux (rc, data') (ab gs bs hs data') (ap gs bs (ps -- sps) hs data') =
        gb_schema_aux data bs ps"
    by (simp add: gb_schema_aux.psimps[OF gb_schema_aux_domI2, OF assms, of data] Let_def)
  finally show ?case .
qed

corollary gb_schema_aux_dgrad_p_set_le:
  assumes "dickson_grading d" and "struct_spec sel ap ab compl"
  shows "dgrad_p_set_le d (fst ` set (gb_schema_aux data bs ps)) (args_to_set (gs, bs, ps))"
  using fst_gb_schema_dummy_dgrad_p_set_le[OF assms] unfolding gb_schema_dummy_eq_gb_schema_aux[OF assms(2)] .

corollary gb_schema_aux_components:
  assumes "struct_spec sel ap ab compl" and "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)"
  shows "component_of_term ` Keys (fst ` set (gb_schema_aux data bs ps)) =
          component_of_term ` Keys (args_to_set (gs, bs, ps))"
  using fst_gb_schema_dummy_components[OF assms] unfolding gb_schema_dummy_eq_gb_schema_aux[OF assms(1)] .

lemma gb_schema_aux_pmdl:
  assumes "struct_spec sel ap ab compl" and "compl_pmdl compl" and "is_Groebner_basis (fst ` set gs)"
    and "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)" and "unique_idx (gs @ bs) (snd data)"
    and "rem_comps_spec (gs @ bs) data"
  shows "pmdl (fst ` set (gb_schema_aux data bs ps)) = pmdl (fst ` set (gs @ bs))"
  using fst_gb_schema_dummy_pmdl[OF assms] unfolding gb_schema_dummy_eq_gb_schema_aux[OF assms(1)] .

corollary gb_schema_aux_dgrad_p_set_le_init:
  assumes "dickson_grading d" and "struct_spec sel ap ab compl"
  shows "dgrad_p_set_le d (fst ` set (gb_schema_aux data (ab gs [] bs (snd data)) (ap gs [] [] bs (snd data))))
                          (fst ` (set gs \<union> set bs))"
  using fst_gb_schema_dummy_dgrad_p_set_le_init[OF assms] unfolding gb_schema_dummy_eq_gb_schema_aux[OF assms(2)] .

corollary gb_schema_aux_dgrad_p_set_init:
  assumes "dickson_grading d" and "struct_spec sel ap ab compl"
    and "fst ` (set gs \<union> set bs) \<subseteq> dgrad_p_set d m"
  shows "fst ` set (gb_schema_aux (rc, data) (ab gs [] bs data) (ap gs [] [] bs data)) \<subseteq> dgrad_p_set d m"
  using fst_gb_schema_dummy_dgrad_p_set_init[OF assms] unfolding gb_schema_dummy_eq_gb_schema_aux[OF assms(2)] .

corollary gb_schema_aux_components_init:
  assumes "struct_spec sel ap ab compl"
  shows "component_of_term ` Keys (fst ` set (gb_schema_aux (rc, data) (ab gs [] bs data) (ap gs [] [] bs data))) =
          component_of_term ` Keys (fst ` set (gs @ bs))"
  using fst_gb_schema_dummy_components_init[OF assms] unfolding gb_schema_dummy_eq_gb_schema_aux[OF assms] .

corollary gb_schema_aux_pmdl_init:
  assumes "struct_spec sel ap ab compl" and "compl_pmdl compl" and "is_Groebner_basis (fst ` set gs)"
    and "unique_idx (gs @ ab gs [] bs data) data" and "rem_comps_spec (gs @ ab gs [] bs data) (rc, data)"
  shows "pmdl (fst ` set (gb_schema_aux (rc, data) (ab gs [] bs data) (ap gs [] [] bs data))) =
          pmdl (fst ` (set (gs @ bs)))"
  using fst_gb_schema_dummy_pmdl_init[OF assms] unfolding gb_schema_dummy_eq_gb_schema_aux[OF assms(1)] .

lemma gb_schema_aux_isGB_init:
  assumes "struct_spec sel ap ab compl" and "compl_conn compl" and "is_Groebner_basis (fst ` set gs)"
    and "unique_idx (gs @ ab gs [] bs data) data" and "rem_comps_spec (gs @ ab gs [] bs data) (rc, data)"
  shows "is_Groebner_basis (fst ` set (gb_schema_aux (rc, data) (ab gs [] bs data) (ap gs [] [] bs data)))"
  using fst_gb_schema_dummy_isGB_init[OF assms] unfolding gb_schema_dummy_eq_gb_schema_aux[OF assms(1)] .

end

subsubsection \<open>Functions \<open>gb_schema_direct\<close> and \<open>term gb_schema_incr\<close>\<close>

definition gb_schema_direct :: "('t, 'b, 'c, 'd) selT \<Rightarrow> ('t, 'b, 'c, 'd) apT \<Rightarrow> ('t, 'b, 'c, 'd) abT \<Rightarrow>
                                ('t, 'b, 'c, 'd) complT \<Rightarrow> ('t, 'b, 'c) pdata' list \<Rightarrow> 'd \<Rightarrow>
                                ('t, 'b::field, 'c::default) pdata' list"
  where "gb_schema_direct sel ap ab compl bs0 data0 =
            (let data = (length bs0, data0); bs1 = fst (add_indices (bs0, data0) (0, data0));
                 bs = ab [] [] bs1 data in
              map (\<lambda>(f, _, d). (f, d))
                    (gb_schema_aux sel ap ab compl [] (count_rem_components bs, data) bs (ap [] [] [] bs1 data))
            )"

primrec gb_schema_incr :: "('t, 'b, 'c, 'd) selT \<Rightarrow> ('t, 'b, 'c, 'd) apT \<Rightarrow> ('t, 'b, 'c, 'd) abT \<Rightarrow>
                                ('t, 'b, 'c, 'd) complT \<Rightarrow>
                                (('t, 'b, 'c) pdata list \<Rightarrow> ('t, 'b, 'c) pdata \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow>
                                ('t, 'b, 'c) pdata' list \<Rightarrow> 'd \<Rightarrow> ('t, 'b::field, 'c::default) pdata' list"
  where
    "gb_schema_incr _ _ _ _ _ [] _ = []"|
    "gb_schema_incr sel ap ab compl upd (b0 # bs) data =
      (let (gs, n, data') = add_indices (gb_schema_incr sel ap ab compl upd bs data, data) (0, data);
           b = (fst b0, n, snd b0); data'' = upd gs b data' in
        map (\<lambda>(f, _, d). (f, d))
          (gb_schema_aux sel ap ab compl gs (count_rem_components (b # gs), Suc n, data'')
                        (ab gs [] [b] (Suc n, data'')) (ap gs [] [] [b] (Suc n, data'')))
      )"

lemma (in -) fst_set_drop_indices:
  "fst ` (\<lambda>(f, _, d). (f, d)) ` A = fst ` A" for A::"('x \<times> 'y \<times> 'z) set"
  by (simp add: image_image, rule image_cong, fact refl, simp add: prod.case_eq_if)

lemma fst_gb_schema_direct:
  "fst ` set (gb_schema_direct sel ap ab compl bs0 data0) =
      (let data = (length bs0, data0); bs1 = fst (add_indices (bs0, data0) (0, data0)); bs = ab [] [] bs1 data in
        fst ` set (gb_schema_aux sel ap ab compl [] (count_rem_components bs, data)
                                bs (ap [] [] [] bs1 data))
      )"
  by (simp add: gb_schema_direct_def Let_def fst_set_drop_indices)

lemma gb_schema_direct_dgrad_p_set:
  assumes "dickson_grading d" and "struct_spec sel ap ab compl" and "fst ` set bs \<subseteq> dgrad_p_set d m"
  shows "fst ` set (gb_schema_direct sel ap ab compl bs data) \<subseteq> dgrad_p_set d m"
  unfolding fst_gb_schema_direct Let_def using assms(1, 2)
proof (rule gb_schema_aux_dgrad_p_set_init)
  show "fst ` (set [] \<union> set (fst (add_indices (bs, data) (0, data)))) \<subseteq> dgrad_p_set d m"
    using assms(3) by (simp add: image_Un fst_set_add_indices)
qed

theorem gb_schema_direct_isGB:
  assumes "struct_spec sel ap ab compl" and "compl_conn compl"
  shows "is_Groebner_basis (fst ` set (gb_schema_direct sel ap ab compl bs data))"
  unfolding fst_gb_schema_direct Let_def using assms
proof (rule gb_schema_aux_isGB_init)
  from is_Groebner_basis_empty show "is_Groebner_basis (fst ` set [])" by simp
next
  let ?data = "(length bs, data)"
  from assms(1) have "ab_spec ab" by (rule struct_specD)
  moreover have "unique_idx ([] @ []) (0, data)" by (simp add: unique_idx_Nil)
  ultimately show "unique_idx ([] @ ab [] [] (fst (add_indices (bs, data) (0, data))) ?data) ?data"
  proof (rule unique_idx_ab)
    show "(fst (add_indices (bs, data) (0, data)), length bs, data) = add_indices (bs, data) (0, data)"
      by (simp add: add_indices_def)
  qed
qed (simp add: rem_comps_spec_count_rem_components)

theorem gb_schema_direct_pmdl:
  assumes "struct_spec sel ap ab compl" and "compl_pmdl compl"
  shows "pmdl (fst ` set (gb_schema_direct sel ap ab compl bs data)) = pmdl (fst ` set bs)"
proof -
  have "pmdl (fst ` set (gb_schema_direct sel ap ab compl bs data)) =
          pmdl (fst ` set ([] @ (fst (add_indices (bs, data) (0, data)))))"
    unfolding fst_gb_schema_direct Let_def using assms
  proof (rule gb_schema_aux_pmdl_init)
    from is_Groebner_basis_empty show "is_Groebner_basis (fst ` set [])" by simp
  next
    let ?data = "(length bs, data)"
    from assms(1) have "ab_spec ab" by (rule struct_specD)
    moreover have "unique_idx ([] @ []) (0, data)" by (simp add: unique_idx_Nil)
    ultimately show "unique_idx ([] @ ab [] [] (fst (add_indices (bs, data) (0, data))) ?data) ?data"
    proof (rule unique_idx_ab)
      show "(fst (add_indices (bs, data) (0, data)), length bs, data) = add_indices (bs, data) (0, data)"
        by (simp add: add_indices_def)
    qed
  qed (simp add: rem_comps_spec_count_rem_components)
  thus ?thesis by (simp add: fst_set_add_indices)
qed

lemma fst_gb_schema_incr:
  "fst ` set (gb_schema_incr sel ap ab compl upd (b0 # bs) data) =
      (let (gs, n, data') = add_indices (gb_schema_incr sel ap ab compl upd bs data, data) (0, data);
            b = (fst b0, n, snd b0); data'' = upd gs b data' in
        fst ` set (gb_schema_aux sel ap ab compl gs (count_rem_components (b # gs), Suc n, data'')
                                (ab gs [] [b] (Suc n, data'')) (ap gs [] [] [b] (Suc n, data'')))
      )"
  by (simp only: gb_schema_incr.simps Let_def prod.case_distrib[of set]
        prod.case_distrib[of "image fst"] set_map fst_set_drop_indices)

lemma gb_schema_incr_dgrad_p_set:
  assumes "dickson_grading d" and "struct_spec sel ap ab compl"
    and "fst ` set bs \<subseteq> dgrad_p_set d m"
  shows "fst ` set (gb_schema_incr sel ap ab compl upd bs data) \<subseteq> dgrad_p_set d m"
  using assms(3)
proof (induct bs)
  case Nil
  show ?case by simp
next
  case (Cons b0 bs)
  from Cons(2) have 1: "fst b0 \<in> dgrad_p_set d m" and 2: "fst ` set bs \<subseteq> dgrad_p_set d m" by simp_all
  show ?case
  proof (simp only: fst_gb_schema_incr Let_def split: prod.splits, simp, intro allI impI)
    fix gs n data'
    assume "add_indices (gb_schema_incr sel ap ab compl upd bs data, data) (0, data) = (gs, n, data')"
    hence gs: "gs = fst (add_indices (gb_schema_incr sel ap ab compl upd bs data, data) (0, data))" by simp
    define b where "b = (fst b0, n, snd b0)"
    define data'' where "data'' = upd gs b data'"
    from assms(1, 2)
    show "fst ` set (gb_schema_aux sel ap ab compl gs (count_rem_components (b # gs), Suc n, data'')
                (ab gs [] [b] (Suc n, data'')) (ap gs [] [] [b] (Suc n, data''))) \<subseteq> dgrad_p_set d m"
    proof (rule gb_schema_aux_dgrad_p_set_init)
      from 1 Cons(1)[OF 2] show "fst ` (set gs \<union> set [b]) \<subseteq> dgrad_p_set d m"
        by (simp add: gs fst_set_add_indices b_def)
    qed
  qed
qed

theorem gb_schema_incr_dgrad_p_set_isGB:
  assumes "struct_spec sel ap ab compl" and "compl_conn compl"
  shows "is_Groebner_basis (fst ` set (gb_schema_incr sel ap ab compl upd bs data))"
proof (induct bs)
  case Nil
  from is_Groebner_basis_empty show ?case by simp
next
  case (Cons b0 bs)
  show ?case
  proof (simp only: fst_gb_schema_incr Let_def split: prod.splits, simp, intro allI impI)
    fix gs n data'
    assume *: "add_indices (gb_schema_incr sel ap ab compl upd bs data, data) (0, data) = (gs, n, data')"
    hence gs: "gs = fst (add_indices (gb_schema_incr sel ap ab compl upd bs data, data) (0, data))" by simp
    define b where "b = (fst b0, n, snd b0)"
    define data'' where "data'' = upd gs b data'"
    from assms(1) have ab: "ab_spec ab" by (rule struct_specD3)
    from Cons have "is_Groebner_basis (fst ` set gs)" by (simp add: gs fst_set_add_indices)
    with assms
    show "is_Groebner_basis (fst ` set (gb_schema_aux sel ap ab compl gs (count_rem_components (b # gs), Suc n, data'')
                                (ab gs [] [b] (Suc n, data'')) (ap gs [] [] [b] (Suc n, data''))))"
    proof (rule gb_schema_aux_isGB_init)
      from ab show "unique_idx (gs @ ab gs [] [b] (Suc n, data'')) (Suc n, data'')"
      proof (rule unique_idx_ab)
        from unique_idx_Nil *[symmetric] have "unique_idx ([] @ gs) (n, data')"
          by (rule unique_idx_append)
        thus "unique_idx (gs @ []) (n, data')" by simp
      next
        show "([b], Suc n, data'') = add_indices ([b0], data'') (n, data')"
          by (simp add: add_indices_def b_def)
      qed
    next
      have "rem_comps_spec (b # gs) (count_rem_components (b # gs), Suc n, data'')"
        by (fact rem_comps_spec_count_rem_components)
      moreover have "set (b # gs) = set (gs @ ab gs [] [b] (Suc n, data''))"
        by (simp add: ab_specD1[OF ab])
      ultimately show "rem_comps_spec (gs @ ab gs [] [b] (Suc n, data''))
                                      (count_rem_components (b # gs), Suc n, data'')"
        by (simp only: rem_comps_spec_def)
    qed
  qed
qed

theorem gb_schema_incr_pmdl:
  assumes "struct_spec sel ap ab compl" and "compl_conn compl" "compl_pmdl compl"
  shows "pmdl (fst ` set (gb_schema_incr sel ap ab compl upd bs data)) = pmdl (fst ` set bs)"
proof (induct bs)
  case Nil
  show ?case by simp
next
  case (Cons b0 bs)
  show ?case
  proof (simp only: fst_gb_schema_incr Let_def split: prod.splits, simp, intro allI impI)
    fix gs n data'
    assume *: "add_indices (gb_schema_incr sel ap ab compl upd bs data, data) (0, data) = (gs, n, data')"
    hence gs: "gs = fst (add_indices (gb_schema_incr sel ap ab compl upd bs data, data) (0, data))" by simp
    define b where "b = (fst b0, n, snd b0)"
    define data'' where "data'' = upd gs b data'"
    from assms(1) have ab: "ab_spec ab" by (rule struct_specD3)
    from assms(1, 2) have "is_Groebner_basis (fst ` set gs)" unfolding gs fst_conv fst_set_add_indices
      by (rule gb_schema_incr_dgrad_p_set_isGB)
    with assms(1, 3)
    have eq: "pmdl (fst ` set (gb_schema_aux sel ap ab compl gs (count_rem_components (b # gs), Suc n, data'')
                          (ab gs [] [b] (Suc n, data'')) (ap gs [] [] [b] (Suc n, data'')))) =
              pmdl (fst ` set (gs @ [b]))"
    proof (rule gb_schema_aux_pmdl_init)
      from ab show "unique_idx (gs @ ab gs [] [b] (Suc n, data'')) (Suc n, data'')"
      proof (rule unique_idx_ab)
        from unique_idx_Nil *[symmetric] have "unique_idx ([] @ gs) (n, data')"
          by (rule unique_idx_append)
        thus "unique_idx (gs @ []) (n, data')" by simp
      next
        show "([b], Suc n, data'') = add_indices ([b0], data'') (n, data')"
          by (simp add: add_indices_def b_def)
      qed
    next
      have "rem_comps_spec (b # gs) (count_rem_components (b # gs), Suc n, data'')"
        by (fact rem_comps_spec_count_rem_components)
      moreover have "set (b # gs) = set (gs @ ab gs [] [b] (Suc n, data''))"
        by (simp add: ab_specD1[OF ab])
      ultimately show "rem_comps_spec (gs @ ab gs [] [b] (Suc n, data''))
                                      (count_rem_components (b # gs), Suc n, data'')"
        by (simp only: rem_comps_spec_def)
    qed
    also have "... = pmdl (insert (fst b) (fst ` set gs))" by simp
    also from Cons have "... = pmdl (insert (fst b) (fst ` set bs))"
      unfolding gs fst_conv fst_set_add_indices by (rule pmdl.span_insert_cong)
    finally show "pmdl (fst ` set (gb_schema_aux sel ap ab compl gs (count_rem_components (b # gs), Suc n, data'')
                              (ab gs [] [b] (Suc n, data'')) (ap gs [] [] [b] (Suc n, data'')))) =
                  pmdl (insert (fst b0) (fst ` set bs))" by (simp add: b_def)
  qed
qed

subsection \<open>Suitable Instances of the @{emph \<open>add-pairs\<close>} Parameter\<close>

subsubsection \<open>Specification of the @{emph \<open>crit\<close>} parameters\<close>

type_synonym (in -) ('t, 'b, 'c, 'd) icritT = "nat \<times> 'd \<Rightarrow> ('t, 'b, 'c) pdata list \<Rightarrow> ('t, 'b, 'c) pdata list \<Rightarrow>
                                          ('t, 'b, 'c) pdata list \<Rightarrow> ('t, 'b, 'c) pdata \<Rightarrow> ('t, 'b, 'c) pdata \<Rightarrow> bool"

type_synonym (in -) ('t, 'b, 'c, 'd) ncritT = "nat \<times> 'd \<Rightarrow> ('t, 'b, 'c) pdata list \<Rightarrow> ('t, 'b, 'c) pdata list \<Rightarrow>
                                          ('t, 'b, 'c) pdata list \<Rightarrow> bool \<Rightarrow>
                                          (bool \<times> ('t, 'b, 'c) pdata_pair) list \<Rightarrow> ('t, 'b, 'c) pdata \<Rightarrow>
                                          ('t, 'b, 'c) pdata \<Rightarrow> bool"

type_synonym (in -) ('t, 'b, 'c, 'd) ocritT = "nat \<times> 'd \<Rightarrow> ('t, 'b, 'c) pdata list \<Rightarrow>
                                          (bool \<times> ('t, 'b, 'c) pdata_pair) list \<Rightarrow> ('t, 'b, 'c) pdata \<Rightarrow>
                                          ('t, 'b, 'c) pdata \<Rightarrow> bool"

definition icrit_spec :: "('t, 'b::field, 'c, 'd) icritT \<Rightarrow> bool"
  where "icrit_spec crit \<longleftrightarrow>
            (\<forall>d m data gs bs hs p q. dickson_grading d \<longrightarrow>
              fst ` (set gs \<union> set bs \<union> set hs) \<subseteq> dgrad_p_set d m \<longrightarrow> unique_idx (gs @ bs @ hs) data \<longrightarrow>
              is_Groebner_basis (fst ` set gs) \<longrightarrow> p \<in> set hs \<longrightarrow> q \<in> set gs \<union> set bs \<union> set hs \<longrightarrow>
              fst p \<noteq> 0 \<longrightarrow> fst q \<noteq> 0 \<longrightarrow> crit data gs bs hs p q \<longrightarrow>
              crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs \<union> set hs)) (fst p) (fst q))"

text \<open>Criteria satisfying @{const icrit_spec} can be used for discarding pairs @{emph \<open>instantly\<close>},
  without reference to any other pairs.
  The product criterion for scalar polynomials satisfies @{const icrit_spec}, and so does the
  component criterion (which checks whether the component-indices of the leading terms of two
  polynomials are identical).\<close>

definition ncrit_spec :: "('t, 'b::field, 'c, 'd) ncritT \<Rightarrow> bool"
  where "ncrit_spec crit \<longleftrightarrow>
            (\<forall>d m data gs bs hs ps B q_in_bs p q. dickson_grading d \<longrightarrow> set gs \<union> set bs \<union> set hs \<subseteq> B \<longrightarrow>
              fst ` B \<subseteq> dgrad_p_set d m \<longrightarrow> snd ` set ps \<subseteq> set hs \<times> (set gs \<union> set bs \<union> set hs) \<longrightarrow>
              unique_idx (gs @ bs @ hs) data \<longrightarrow> is_Groebner_basis (fst ` set gs) \<longrightarrow>
              (q_in_bs \<longrightarrow> (q \<in> set gs \<union> set bs)) \<longrightarrow>
              (\<forall>p' q'. (p', q') \<in>\<^sub>p snd ` set ps \<longrightarrow> fst p' \<noteq> 0 \<longrightarrow> fst q' \<noteq> 0 \<longrightarrow>
                  crit_pair_cbelow_on d m (fst ` B) (fst p') (fst q')) \<longrightarrow>
              (\<forall>p' q'. p' \<in> set gs \<union> set bs \<longrightarrow> q' \<in> set gs \<union> set bs \<longrightarrow> fst p' \<noteq> 0 \<longrightarrow> fst q' \<noteq> 0 \<longrightarrow>
                  crit_pair_cbelow_on d m (fst ` B) (fst p') (fst q')) \<longrightarrow>
              p \<in> set hs \<longrightarrow> q \<in> set gs \<union> set bs \<union> set hs \<longrightarrow> fst p \<noteq> 0 \<longrightarrow> fst q \<noteq> 0 \<longrightarrow>
              crit data gs bs hs q_in_bs ps p q \<longrightarrow>
              crit_pair_cbelow_on d m (fst ` B) (fst p) (fst q))"

definition ocrit_spec :: "('t, 'b::field, 'c, 'd) ocritT \<Rightarrow> bool"
  where "ocrit_spec crit \<longleftrightarrow>
            (\<forall>d m data hs ps B p q. dickson_grading d \<longrightarrow> set hs \<subseteq> B \<longrightarrow> fst ` B \<subseteq> dgrad_p_set d m \<longrightarrow>
              unique_idx (p # q # hs @ (map (fst \<circ> snd) ps) @ (map (snd \<circ> snd) ps)) data \<longrightarrow>
              (\<forall>p' q'. (p', q') \<in>\<^sub>p snd ` set ps \<longrightarrow> fst p' \<noteq> 0 \<longrightarrow> fst q' \<noteq> 0 \<longrightarrow>
                  crit_pair_cbelow_on d m (fst ` B) (fst p') (fst q')) \<longrightarrow>
              p \<in> B \<longrightarrow> q \<in> B \<longrightarrow> fst p \<noteq> 0 \<longrightarrow> fst q \<noteq> 0 \<longrightarrow>
              crit data hs ps p q \<longrightarrow> crit_pair_cbelow_on d m (fst ` B) (fst p) (fst q))"

text \<open>Criteria satisfying @{const ncrit_spec} can be used for discarding new pairs by reference to
  new and old elements, whereas criteria satisfying @{const ocrit_spec} can be used for
  discarding old pairs by reference to new elements @{emph \<open>only\<close>} (no existing ones!).
  The chain criterion satisfies both @{const ncrit_spec} and @{const ocrit_spec}.\<close>

lemma icrit_specI:
  assumes "\<And>d m data gs bs hs p q.
              dickson_grading d \<Longrightarrow> fst ` (set gs \<union> set bs \<union> set hs) \<subseteq> dgrad_p_set d m \<Longrightarrow>
              unique_idx (gs @ bs @ hs) data \<Longrightarrow> is_Groebner_basis (fst ` set gs) \<Longrightarrow>
              p \<in> set hs \<Longrightarrow> q \<in> set gs \<union> set bs \<union> set hs \<Longrightarrow> fst p \<noteq> 0 \<Longrightarrow> fst q \<noteq> 0 \<Longrightarrow>
              crit data gs bs hs p q \<Longrightarrow>
              crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs \<union> set hs)) (fst p) (fst q)"
  shows "icrit_spec crit"
  unfolding icrit_spec_def using assms by auto

lemma icrit_specD:
  assumes "icrit_spec crit" and "dickson_grading d"
    and "fst ` (set gs \<union> set bs \<union> set hs) \<subseteq> dgrad_p_set d m" and "unique_idx (gs @ bs @ hs) data"
    and "is_Groebner_basis (fst ` set gs)" and "p \<in> set hs" and "q \<in> set gs \<union> set bs \<union> set hs"
    and "fst p \<noteq> 0" and "fst q \<noteq> 0" and "crit data gs bs hs p q"
  shows "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs \<union> set hs)) (fst p) (fst q)"
  using assms unfolding icrit_spec_def by blast

lemma ncrit_specI:
  assumes "\<And>d m data gs bs hs ps B q_in_bs p q.
              dickson_grading d \<Longrightarrow> set gs \<union> set bs \<union> set hs \<subseteq> B \<Longrightarrow>
              fst ` B \<subseteq> dgrad_p_set d m \<Longrightarrow> snd ` set ps \<subseteq> set hs \<times> (set gs \<union> set bs \<union> set hs) \<Longrightarrow>
              unique_idx (gs @ bs @ hs) data \<Longrightarrow> is_Groebner_basis (fst ` set gs) \<Longrightarrow>
              (q_in_bs \<longrightarrow> q \<in> set gs \<union> set bs) \<Longrightarrow>
              (\<And>p' q'. (p', q') \<in>\<^sub>p snd ` set ps \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
                  crit_pair_cbelow_on d m (fst ` B) (fst p') (fst q')) \<Longrightarrow>
              (\<And>p' q'. p' \<in> set gs \<union> set bs \<Longrightarrow> q' \<in> set gs \<union> set bs \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
                  crit_pair_cbelow_on d m (fst ` B) (fst p') (fst q')) \<Longrightarrow>
              p \<in> set hs \<Longrightarrow> q \<in> set gs \<union> set bs \<union> set hs \<Longrightarrow> fst p \<noteq> 0 \<Longrightarrow> fst q \<noteq> 0 \<Longrightarrow>
              crit data gs bs hs q_in_bs ps p q \<Longrightarrow>
              crit_pair_cbelow_on d m (fst ` B) (fst p) (fst q)"
  shows "ncrit_spec crit"
  unfolding ncrit_spec_def by (intro allI impI, rule assms, assumption+, meson, meson, assumption+)

lemma ncrit_specD:
  assumes "ncrit_spec crit" and "dickson_grading d" and "set gs \<union> set bs \<union> set hs \<subseteq> B"
    and "fst ` B \<subseteq> dgrad_p_set d m" and "snd ` set ps \<subseteq> set hs \<times> (set gs \<union> set bs \<union> set hs)"
    and "unique_idx (gs @ bs @ hs) data" and "is_Groebner_basis (fst ` set gs)"
    and "q_in_bs \<Longrightarrow> q \<in> set gs \<union> set bs"
    and "\<And>p' q'. (p', q') \<in>\<^sub>p snd ` set ps \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
                  crit_pair_cbelow_on d m (fst ` B) (fst p') (fst q')"
    and "\<And>p' q'. p' \<in> set gs \<union> set bs \<Longrightarrow> q' \<in> set gs \<union> set bs \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
                  crit_pair_cbelow_on d m (fst ` B) (fst p') (fst q')"
    and "p \<in> set hs" and "q \<in> set gs \<union> set bs \<union> set hs" and "fst p \<noteq> 0" and "fst q \<noteq> 0"
    and "crit data gs bs hs q_in_bs ps p q"
  shows "crit_pair_cbelow_on d m (fst ` B) (fst p) (fst q)"
  using assms unfolding ncrit_spec_def by blast

lemma ocrit_specI:
  assumes "\<And>d m data hs ps B p q.
              dickson_grading d \<Longrightarrow> set hs \<subseteq> B \<Longrightarrow> fst ` B \<subseteq> dgrad_p_set d m \<Longrightarrow>
              unique_idx (p # q # hs @ (map (fst \<circ> snd) ps) @ (map (snd \<circ> snd) ps)) data \<Longrightarrow>
              (\<And>p' q'. (p', q') \<in>\<^sub>p snd ` set ps \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
                  crit_pair_cbelow_on d m (fst ` B) (fst p') (fst q')) \<Longrightarrow>
              p \<in> B \<Longrightarrow> q \<in> B \<Longrightarrow> fst p \<noteq> 0 \<Longrightarrow> fst q \<noteq> 0 \<Longrightarrow>
              crit data hs ps p q \<Longrightarrow> crit_pair_cbelow_on d m (fst ` B) (fst p) (fst q)"
  shows "ocrit_spec crit"
  unfolding ocrit_spec_def by (intro allI impI, rule assms, assumption+, meson, assumption+)

lemma ocrit_specD:
  assumes "ocrit_spec crit" and "dickson_grading d" and "set hs \<subseteq> B" and "fst ` B \<subseteq> dgrad_p_set d m"
    and "unique_idx (p # q # hs @ (map (fst \<circ> snd) ps) @ (map (snd \<circ> snd) ps)) data"
    and "\<And>p' q'. (p', q') \<in>\<^sub>p snd ` set ps \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
                  crit_pair_cbelow_on d m (fst ` B) (fst p') (fst q')"
    and "p \<in> B" and "q \<in> B" and "fst p \<noteq> 0" and "fst q \<noteq> 0"
    and "crit data hs ps p q"
  shows "crit_pair_cbelow_on d m (fst ` B) (fst p) (fst q)"
  using assms unfolding ocrit_spec_def by blast

subsubsection \<open>Suitable instances of the @{emph \<open>crit\<close>} parameters\<close>

definition component_crit :: "('t, 'b::zero, 'c, 'd) icritT"
  where "component_crit data gs bs hs p q \<longleftrightarrow> (component_of_term (lt (fst p)) \<noteq> component_of_term (lt (fst q)))"

lemma icrit_spec_component_crit: "icrit_spec (component_crit::('t, 'b::field, 'c, 'd) icritT)"
proof (rule icrit_specI)
  fix d m and data::"nat \<times> 'd" and gs bs hs and p q::"('t, 'b, 'c) pdata"
  assume "component_crit data gs bs hs p q"
  hence "component_of_term (lt (fst p)) \<noteq> component_of_term (lt (fst q))"
    by (simp add: component_crit_def)
  thus "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs \<union> set hs)) (fst p) (fst q)"
    by (rule crit_pair_cbelow_distinct_component)
qed

text \<open>The product criterion is only applicable to scalar polynomials.\<close>

definition product_crit :: "('a, 'b::zero, 'c, 'd) icritT"
  where "product_crit data gs bs hs p q \<longleftrightarrow> (gcs (punit.lt (fst p)) (punit.lt (fst q)) = 0)"

lemma (in gd_term) icrit_spec_product_crit: "punit.icrit_spec (product_crit::('a, 'b::field, 'c, 'd) icritT)"
proof (rule punit.icrit_specI)
  fix d m and data::"nat \<times> 'd" and gs bs hs and p q::"('a, 'b, 'c) pdata"
  assume "product_crit data gs bs hs p q"
  hence *: "gcs (punit.lt (fst p)) (punit.lt (fst q)) = 0" by (simp only: product_crit_def)
  assume "p \<in> set hs" and q_in: "q \<in> set gs \<union> set bs \<union> set hs" (is "_ \<in> ?B")
  assume "dickson_grading d" and sub: "fst ` (set gs \<union> set bs \<union> set hs) \<subseteq> punit.dgrad_p_set d m"
  moreover from \<open>p \<in> set hs\<close> have "fst p \<in> fst ` ?B" by simp
  moreover from q_in have "fst q \<in> fst ` ?B" by simp
  moreover assume "fst p \<noteq> 0" and "fst q \<noteq> 0"
  ultimately show "punit.crit_pair_cbelow_on d m (fst ` ?B) (fst p) (fst q)"
    using * by (rule product_criterion)
qed

text \<open>@{const component_crit} and @{const product_crit} ignore the \<open>data\<close> parameter.\<close>

fun (in -) pair_in_list :: "(bool \<times> ('a, 'b, 'c) pdata_pair) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
 "pair_in_list [] _ _ = False"
|"pair_in_list ((_, (_, i', _), (_, j', _)) # ps) i j =
    ((i = i' \<and> j = j') \<or> (i = j' \<and> j = i') \<or> pair_in_list ps i j)"

lemma (in -) pair_in_listE:
  assumes "pair_in_list ps i j"
  obtains p q a b where "((p, i, a), (q, j, b)) \<in>\<^sub>p snd ` set ps"
  using assms
proof (induct ps i j arbitrary: thesis rule: pair_in_list.induct)
  case (1 i j)
  from 1(2) show ?case by simp
next
  case (2 c p i' a q j' b ps i j)
  from 2(3) have "(i = i' \<and> j = j') \<or> (i = j' \<and> j = i') \<or> pair_in_list ps i j" by simp
  thus ?case
  proof (elim disjE conjE)
    assume "i = i'" and "j = j'"
    have "((p, i, a), (q, j, b)) \<in>\<^sub>p snd ` set ((c, (p, i', a), q, j', b) # ps)"
      unfolding \<open>i = i'\<close> \<open>j = j'\<close> in_pair_iff by fastforce
    thus ?thesis by (rule 2(2))
  next
    assume "i = j'" and "j = i'"
    have "((q, i, b), (p, j, a)) \<in>\<^sub>p snd ` set ((c, (p, i', a), q, j', b) # ps)"
      unfolding \<open>i = j'\<close> \<open>j = i'\<close> in_pair_iff by fastforce
    thus ?thesis by (rule 2(2))
  next
    assume "pair_in_list ps i j"
    obtain p' q' a' b' where "((p', i, a'), (q', j, b')) \<in>\<^sub>p snd ` set ps"
      by (rule 2(1), assumption, rule \<open>pair_in_list ps i j\<close>)
    also have "... \<subseteq> snd ` set ((c, (p, i', a), q, j', b) # ps)" by auto
    finally show ?thesis by (rule 2(2))
  qed
qed

definition chain_ncrit :: "('t, 'b::zero, 'c, 'd) ncritT"
  where "chain_ncrit data gs bs hs q_in_bs ps p q \<longleftrightarrow>
          (let v = lt (fst p); l = term_of_pair (lcs (pp_of_term v) (lp (fst q)), component_of_term v);
               i = fst (snd p); j = fst (snd q) in
            (\<exists>r\<in>set gs. let k = fst (snd r) in
                  k \<noteq> i \<and> k \<noteq> j \<and> lt (fst r) adds\<^sub>t l \<and> pair_in_list ps i k \<and> (q_in_bs \<or> pair_in_list ps j k) \<and> fst r \<noteq> 0) \<or>
            (\<exists>r\<in>set bs. let k = fst (snd r) in
                  k \<noteq> i \<and> k \<noteq> j \<and> lt (fst r) adds\<^sub>t l \<and> pair_in_list ps i k \<and> (q_in_bs \<or> pair_in_list ps j k) \<and> fst r \<noteq> 0) \<or>
            (\<exists>h\<in>set hs. let k = fst (snd h) in
                  k \<noteq> i \<and> k \<noteq> j \<and> lt (fst h) adds\<^sub>t l \<and> pair_in_list ps i k \<and> pair_in_list ps j k \<and> fst h \<noteq> 0))"

definition chain_ocrit :: "('t, 'b::zero, 'c, 'd) ocritT"
  where "chain_ocrit data hs ps p q \<longleftrightarrow>
          (let v = lt (fst p); l = term_of_pair (lcs (pp_of_term v) (lp (fst q)), component_of_term v);
               i = fst (snd p); j = fst (snd q) in
            (\<exists>h\<in>set hs. let k = fst (snd h) in
                  k \<noteq> i \<and> k \<noteq> j \<and> lt (fst h) adds\<^sub>t l \<and> pair_in_list ps i k \<and> pair_in_list ps j k \<and> fst h \<noteq> 0))"

text \<open>@{const chain_ncrit} and @{const chain_ocrit} ignore the \<open>data\<close> parameter.\<close>

lemma chain_ncritE:
  assumes "chain_ncrit data gs bs hs q_in_bs ps p q" and "snd ` set ps \<subseteq> set hs \<times> (set gs \<union> set bs \<union> set hs)"
    and "unique_idx (gs @ bs @ hs) data" and "p \<in> set hs" and "q \<in> set gs \<union> set bs \<union> set hs"
  obtains r where "r \<in> set gs \<union> set bs \<union> set hs" and "fst r \<noteq> 0" and "r \<noteq> p" and "r \<noteq> q"
    and "lt (fst r) adds\<^sub>t term_of_pair (lcs (lp (fst p)) (lp (fst q)), component_of_term (lt (fst p)))"
    and "(p, r) \<in>\<^sub>p snd ` set ps" and "(r \<in> set gs \<union> set bs \<and> q_in_bs) \<or> (q, r) \<in>\<^sub>p snd ` set ps"
proof -
  let ?l = "term_of_pair (lcs (lp (fst p)) (lp (fst q)), component_of_term (lt (fst p)))"
  let ?i = "fst (snd p)"
  let ?j = "fst (snd q)"
  let ?xs = "gs @ bs @ hs"
  have 3: "x \<in> set ?xs" if "(x, y) \<in>\<^sub>p snd ` set ps" for x y
  proof -
    note that
    also have "snd ` set ps \<subseteq> set hs \<times> (set gs \<union> set bs \<union> set hs)" by (fact assms(2))
    also have "... \<subseteq> (set gs \<union> set bs \<union> set hs) \<times> (set gs \<union> set bs \<union> set hs)" by fastforce
    finally have "(x, y) \<in> (set gs \<union> set bs \<union> set hs) \<times> (set gs \<union> set bs \<union> set hs)"
      by (simp only: in_pair_same)
    thus ?thesis by simp
  qed
  have 4: "x \<in> set ?xs" if "(y, x) \<in>\<^sub>p snd ` set ps" for x y
  proof -
    from that have "(x, y) \<in>\<^sub>p snd ` set ps" by (simp add: in_pair_iff disj_commute)
    thus ?thesis by (rule 3)
  qed

  from assms(1) have
    "\<exists>r \<in> set gs \<union> set bs \<union> set hs. let k = fst (snd r) in
          k \<noteq> ?i \<and> k \<noteq> ?j \<and> lt (fst r) adds\<^sub>t ?l \<and> pair_in_list ps ?i k \<and>
         ((r \<in> set gs \<union> set bs \<and> q_in_bs) \<or> pair_in_list ps ?j k) \<and> fst r \<noteq> 0"
    by (smt UnI1 chain_ncrit_def sup_commute)

  then obtain r where r_in: "r \<in> set gs \<union> set bs \<union> set hs" and "fst r \<noteq> 0" and rp: "fst (snd r) \<noteq> ?i"
    and rq: "fst (snd r) \<noteq> ?j" and "lt (fst r) adds\<^sub>t ?l"
    and 1: "pair_in_list ps ?i (fst (snd r))"
    and 2: "(r \<in> set gs \<union> set bs \<and> q_in_bs) \<or> pair_in_list ps ?j (fst (snd r))"
    unfolding Let_def by blast
  let ?k = "fst (snd r)"
  note r_in \<open>fst r \<noteq> 0\<close>
  moreover from rp have "r \<noteq> p" by auto
  moreover from rq have "r \<noteq> q" by auto
  ultimately show ?thesis using \<open>lt (fst r) adds\<^sub>t ?l\<close>
  proof
    from 1 obtain p' r' a b where *: "((p', ?i, a), (r', ?k, b)) \<in>\<^sub>p snd ` set ps"
      by (rule pair_in_listE)

    note assms(3)
    moreover from * have "(p', ?i, a) \<in> set ?xs" by (rule 3)
    moreover from assms(4) have "p \<in> set ?xs" by simp
    moreover have "fst (snd (p', ?i, a)) = ?i" by simp
    ultimately have p': "(p', ?i, a) = p" by (rule unique_idxD1)

    note assms(3)
    moreover from * have "(r', ?k, b) \<in> set ?xs" by (rule 4)
    moreover from r_in have "r \<in> set ?xs" by simp
    moreover have "fst (snd (r', ?k, b)) = ?k" by simp
    ultimately have r': "(r', ?k, b) = r" by (rule unique_idxD1)

    from * show "(p, r) \<in>\<^sub>p snd ` set ps" by (simp only: p' r')
  next
    from 2 show "(r \<in> set gs \<union> set bs \<and> q_in_bs) \<or> (q, r) \<in>\<^sub>p snd ` set ps"
    proof
      assume "r \<in> set gs \<union> set bs \<and> q_in_bs"
      thus ?thesis ..
    next
      assume "pair_in_list ps ?j ?k"
      then obtain q' r' a b where *: "((q', ?j, a), (r', ?k, b)) \<in>\<^sub>p snd ` set ps"
        by (rule pair_in_listE)

      note assms(3)
      moreover from * have "(q', ?j, a) \<in> set ?xs" by (rule 3)
      moreover from assms(5) have "q \<in> set ?xs" by simp
      moreover have "fst (snd (q', ?j, a)) = ?j" by simp
      ultimately have q': "(q', ?j, a) = q" by (rule unique_idxD1)
  
      note assms(3)
      moreover from * have "(r', ?k, b) \<in> set ?xs" by (rule 4)
      moreover from r_in have "r \<in> set ?xs" by simp
      moreover have "fst (snd (r', ?k, b)) = ?k" by simp
      ultimately have r': "(r', ?k, b) = r" by (rule unique_idxD1)
  
      from * have "(q, r) \<in>\<^sub>p snd ` set ps" by (simp only: q' r')
      thus ?thesis ..
    qed
  qed
qed

lemma chain_ocritE:
  assumes "chain_ocrit data hs ps p q"
    and "unique_idx (p # q # hs @ (map (fst \<circ> snd) ps) @ (map (snd \<circ> snd) ps)) data" (is "unique_idx ?xs _")
  obtains h where "h \<in> set hs" and "fst h \<noteq> 0" and "h \<noteq> p" and "h \<noteq> q"
    and "lt (fst h) adds\<^sub>t term_of_pair (lcs (lp (fst p)) (lp (fst q)), component_of_term (lt (fst p)))"
    and "(p, h) \<in>\<^sub>p snd ` set ps" and "(q, h) \<in>\<^sub>p snd ` set ps"
proof -
  let ?l = "term_of_pair (lcs (lp (fst p)) (lp (fst q)), component_of_term (lt (fst p)))"
  have 3: "x \<in> set ?xs" if "(x, y) \<in>\<^sub>p snd ` set ps" for x y
  proof -
    from that have "(x, y) \<in> snd ` set ps \<or> (y, x) \<in> snd ` set ps" by (simp only: in_pair_iff)
    thus ?thesis
    proof
      assume "(x, y) \<in> snd ` set ps"
      hence "fst (x, y) \<in> fst ` snd ` set ps" by fastforce
      thus ?thesis by (simp add: image_comp)
    next
      assume "(y, x) \<in> snd ` set ps"
      hence "snd (y, x) \<in> snd ` snd ` set ps" by fastforce
      thus ?thesis by (simp add: image_comp)
    qed
  qed
  have 4: "x \<in> set ?xs" if "(y, x) \<in>\<^sub>p snd ` set ps" for x y
  proof -
    from that have "(x, y) \<in>\<^sub>p snd ` set ps" by (simp add: in_pair_iff disj_commute)
    thus ?thesis by (rule 3)
  qed

  from assms(1) obtain h where "h \<in> set hs" and "fst h \<noteq> 0" and hp: "fst (snd h) \<noteq> fst (snd p)"
    and hq: "fst (snd h) \<noteq> fst (snd q)" and "lt (fst h) adds\<^sub>t ?l"
    and 1: "pair_in_list ps (fst (snd p)) (fst (snd h))" and 2: "pair_in_list ps (fst (snd q)) (fst (snd h))"
    unfolding chain_ocrit_def Let_def by blast
  let ?i = "fst (snd p)"
  let ?j = "fst (snd q)"
  let ?k = "fst (snd h)"
  note \<open>h \<in> set hs\<close> \<open>fst h \<noteq> 0\<close>
  moreover from hp have "h \<noteq> p" by auto
  moreover from hq have "h \<noteq> q" by auto
  ultimately show ?thesis using \<open>lt (fst h) adds\<^sub>t ?l\<close>
  proof
    from 1 obtain p' h' a b where *: "((p', ?i, a), (h', ?k, b)) \<in>\<^sub>p snd ` set ps"
      by (rule pair_in_listE)

    note assms(2)
    moreover from * have "(p', ?i, a) \<in> set ?xs" by (rule 3)
    moreover have "p \<in> set ?xs" by simp
    moreover have "fst (snd (p', ?i, a)) = ?i" by simp
    ultimately have p': "(p', ?i, a) = p" by (rule unique_idxD1)

    note assms(2)
    moreover from * have "(h', ?k, b) \<in> set ?xs" by (rule 4)
    moreover from \<open>h \<in> set hs\<close> have "h \<in> set ?xs" by simp
    moreover have "fst (snd (h', ?k, b)) = ?k" by simp
    ultimately have h': "(h', ?k, b) = h" by (rule unique_idxD1)

    from * show "(p, h) \<in>\<^sub>p snd ` set ps" by (simp only: p' h')
  next
    from 2 obtain q' h' a b where *: "((q', ?j, a), (h', ?k, b)) \<in>\<^sub>p snd ` set ps"
      by (rule pair_in_listE)

    note assms(2)
    moreover from * have "(q', ?j, a) \<in> set ?xs" by (rule 3)
    moreover have "q \<in> set ?xs" by simp
    moreover have "fst (snd (q', ?j, a)) = ?j" by simp
    ultimately have q': "(q', ?j, a) = q" by (rule unique_idxD1)

    note assms(2)
    moreover from * have "(h', ?k, b) \<in> set ?xs" by (rule 4)
    moreover from \<open>h \<in> set hs\<close> have "h \<in> set ?xs" by simp
    moreover have "fst (snd (h', ?k, b)) = ?k" by simp
    ultimately have h': "(h', ?k, b) = h" by (rule unique_idxD1)

    from * show "(q, h) \<in>\<^sub>p snd ` set ps" by (simp only: q' h')
  qed
qed

lemma ncrit_spec_chain_ncrit: "ncrit_spec (chain_ncrit::('t, 'b::field, 'c, 'd) ncritT)"
proof (rule ncrit_specI)
  fix d m and data::"nat \<times> 'd" and gs bs hs and ps::"(bool \<times> ('t, 'b, 'c) pdata_pair) list"
    and B q_in_bs and p q::"('t, 'b, 'c) pdata"
  assume dg: "dickson_grading d" and B_sup: "set gs \<union> set bs \<union> set hs \<subseteq> B"
    and B_sub: "fst ` B \<subseteq> dgrad_p_set d m" and q_in_bs: "q_in_bs \<longrightarrow> q \<in> set gs \<union> set bs"
    and 1: "\<And>p' q'. (p', q') \<in>\<^sub>p snd ` set ps \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
              crit_pair_cbelow_on d m (fst ` B) (fst p') (fst q')"
    and 2: "\<And>p' q'. p' \<in> set gs \<union> set bs \<Longrightarrow> q' \<in> set gs \<union> set bs \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
              crit_pair_cbelow_on d m (fst ` B) (fst p') (fst q')"
    and "fst p \<noteq> 0" and "fst q \<noteq> 0"
  let ?l = "term_of_pair (lcs (lp (fst p)) (lp (fst q)), component_of_term (lt (fst p)))"
  assume "chain_ncrit data gs bs hs q_in_bs ps p q" and "snd ` set ps \<subseteq> set hs \<times> (set gs \<union> set bs \<union> set hs)" and
    "unique_idx (gs @ bs @ hs) data" and "p \<in> set hs" and "q \<in> set gs \<union> set bs \<union> set hs"
  then obtain r where "r \<in> set gs \<union> set bs \<union> set hs" and "fst r \<noteq> 0" and "r \<noteq> p" and "r \<noteq> q"
    and adds: "lt (fst r) adds\<^sub>t ?l" and "(p, r) \<in>\<^sub>p snd ` set ps"
    and disj: "(r \<in> set gs \<union> set bs \<and> q_in_bs) \<or> (q, r) \<in>\<^sub>p snd ` set ps" by (rule chain_ncritE)
  note dg B_sub
  moreover from \<open>p \<in> set hs\<close> \<open>q \<in> set gs \<union> set bs \<union> set hs\<close> B_sup
  have "fst p \<in> fst ` B" and "fst q \<in> fst ` B"
    by auto
  moreover note \<open>fst p \<noteq> 0\<close> \<open>fst q \<noteq> 0\<close>
  moreover from adds have "lp (fst r) adds lcs (lp (fst p)) (lp (fst q))"
    by (simp add: adds_term_def term_simps)
  moreover from adds have "component_of_term (lt (fst r)) = component_of_term (lt (fst p))"
    by (simp add: adds_term_def term_simps)
  ultimately show "crit_pair_cbelow_on d m (fst ` B) (fst p) (fst q)"
  proof (rule chain_criterion)
    from \<open>(p, r) \<in>\<^sub>p snd ` set ps\<close> \<open>fst p \<noteq> 0\<close> \<open>fst r \<noteq> 0\<close>
    show "crit_pair_cbelow_on d m (fst ` B) (fst p) (fst r)" by (rule 1)
  next
    from disj show "crit_pair_cbelow_on d m (fst ` B) (fst r) (fst q)"
    proof
      assume "r \<in> set gs \<union> set bs \<and> q_in_bs"
      hence "r \<in> set gs \<union> set bs" and q_in_bs by simp_all
      from q_in_bs this(2) have "q \<in> set gs \<union> set bs" ..
      with \<open>r \<in> set gs \<union> set bs\<close> show ?thesis using \<open>fst r \<noteq> 0\<close> \<open>fst q \<noteq> 0\<close> by (rule 2)
    next
      assume "(q, r) \<in>\<^sub>p snd ` set ps"
      hence "(r, q) \<in>\<^sub>p snd ` set ps" by (simp only: in_pair_iff disj_commute)
      thus ?thesis using \<open>fst r \<noteq> 0\<close> \<open>fst q \<noteq> 0\<close> by (rule 1)
    qed
  qed
qed

lemma ocrit_spec_chain_ocrit: "ocrit_spec (chain_ocrit::('t, 'b::field, 'c, 'd) ocritT)"
proof (rule ocrit_specI)
  fix d m and data::"nat \<times> 'd" and hs::"('t, 'b, 'c) pdata list" and ps::"(bool \<times> ('t, 'b, 'c) pdata_pair) list"
    and B and p q::"('t, 'b, 'c) pdata"
  assume dg: "dickson_grading d" and B_sup: "set hs \<subseteq> B"
    and B_sub: "fst ` B \<subseteq> dgrad_p_set d m"
    and 1: "\<And>p' q'. (p', q') \<in>\<^sub>p snd ` set ps \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
              crit_pair_cbelow_on d m (fst ` B) (fst p') (fst q')"
    and "fst p \<noteq> 0" and "fst q \<noteq> 0" and "p \<in> B" and "q \<in> B"
  let ?l = "term_of_pair (lcs (lp (fst p)) (lp (fst q)), component_of_term (lt (fst p)))"
  assume "chain_ocrit data hs ps p q" and "unique_idx (p # q # hs @ map (fst \<circ> snd) ps @ map (snd \<circ> snd) ps) data"
  then obtain h where "h \<in> set hs" and "fst h \<noteq> 0" and "h \<noteq> p" and "h \<noteq> q"
    and adds: "lt (fst h) adds\<^sub>t ?l" and "(p, h) \<in>\<^sub>p snd ` set ps" and "(q, h) \<in>\<^sub>p snd ` set ps"
    by (rule chain_ocritE)
  note dg B_sub
  moreover from \<open>p \<in> B\<close> \<open>q \<in> B\<close> B_sup
  have "fst p \<in> fst ` B" and "fst q \<in> fst ` B" by auto
  moreover note \<open>fst p \<noteq> 0\<close> \<open>fst q \<noteq> 0\<close>
  moreover from adds have "lp (fst h) adds lcs (lp (fst p)) (lp (fst q))"
    by (simp add: adds_term_def term_simps)
  moreover from adds have "component_of_term (lt (fst h)) = component_of_term (lt (fst p))"
    by (simp add: adds_term_def term_simps)
  ultimately show "crit_pair_cbelow_on d m (fst ` B) (fst p) (fst q)"
  proof (rule chain_criterion)
    from \<open>(p, h) \<in>\<^sub>p snd ` set ps\<close> \<open>fst p \<noteq> 0\<close> \<open>fst h \<noteq> 0\<close>
    show "crit_pair_cbelow_on d m (fst ` B) (fst p) (fst h)" by (rule 1)
  next
    from \<open>(q, h) \<in>\<^sub>p snd ` set ps\<close> have "(h, q) \<in>\<^sub>p snd ` set ps" by (simp only: in_pair_iff disj_commute)
    thus "crit_pair_cbelow_on d m (fst ` B) (fst h) (fst q)" using \<open>fst h \<noteq> 0\<close> \<open>fst q \<noteq> 0\<close> by (rule 1)
  qed
qed

lemma icrit_spec_no_crit: "icrit_spec ((\<lambda>_ _ _ _ _ _. False)::('t, 'b::field, 'c, 'd) icritT)"
  by (rule icrit_specI, simp)

lemma ncrit_spec_no_crit: "ncrit_spec ((\<lambda>_ _ _ _ _ _ _ _. False)::('t, 'b::field, 'c, 'd) ncritT)"
  by (rule ncrit_specI, simp)

lemma ocrit_spec_no_crit: "ocrit_spec ((\<lambda>_ _ _ _ _. False)::('t, 'b::field, 'c, 'd) ocritT)"
  by (rule ocrit_specI, simp)

subsubsection \<open>Creating Initial List of New Pairs\<close>

type_synonym (in -) ('t, 'b, 'c) apsT = "bool \<Rightarrow> ('t, 'b, 'c) pdata list \<Rightarrow> ('t, 'b, 'c) pdata list \<Rightarrow>
                                    ('t, 'b, 'c) pdata \<Rightarrow> (bool \<times> ('t, 'b, 'c) pdata_pair) list \<Rightarrow>
                                    (bool \<times> ('t, 'b, 'c) pdata_pair) list"

type_synonym (in -) ('t, 'b, 'c, 'd) npT = "('t, 'b, 'c) pdata list \<Rightarrow> ('t, 'b, 'c) pdata list \<Rightarrow>
                                            ('t, 'b, 'c) pdata list \<Rightarrow> nat \<times> 'd \<Rightarrow>
                                            (bool \<times> ('t, 'b, 'c) pdata_pair) list"

definition np_spec :: "('t, 'b, 'c, 'd) npT \<Rightarrow> bool"
  where "np_spec np \<longleftrightarrow> (\<forall>gs bs hs data.
                            snd ` set (np gs bs hs data) \<subseteq> set hs \<times> (set gs \<union> set bs \<union> set hs) \<and>
                            set hs \<times> (set gs \<union> set bs) \<subseteq> snd ` set (np gs bs hs data) \<and>
                            (\<forall>a b. a \<in> set hs \<longrightarrow> b \<in> set hs \<longrightarrow> a \<noteq> b \<longrightarrow> (a, b) \<in>\<^sub>p snd ` set (np gs bs hs data)) \<and>
                            (\<forall>p q. (True, p, q) \<in> set (np gs bs hs data) \<longrightarrow> q \<in> set gs \<union> set bs))"

lemma np_specI:
  assumes "\<And>gs bs hs data.
              snd ` set (np gs bs hs data) \<subseteq> set hs \<times> (set gs \<union> set bs \<union> set hs) \<and>
              set hs \<times> (set gs \<union> set bs) \<subseteq> snd ` set (np gs bs hs data) \<and>
              (\<forall>a b. a \<in> set hs \<longrightarrow> b \<in> set hs \<longrightarrow> a \<noteq> b \<longrightarrow> (a, b) \<in>\<^sub>p snd ` set (np gs bs hs data)) \<and>
              (\<forall>p q. (True, p, q) \<in> set (np gs bs hs data) \<longrightarrow> q \<in> set gs \<union> set bs)"
  shows "np_spec np"
  unfolding np_spec_def using assms by meson

lemma np_specD1:
  assumes "np_spec np"
  shows "snd ` set (np gs bs hs data) \<subseteq> set hs \<times> (set gs \<union> set bs \<union> set hs)"
  using assms[unfolded np_spec_def, rule_format, of gs bs hs data] ..

lemma np_specD2:
  assumes "np_spec np"
  shows "set hs \<times> (set gs \<union> set bs) \<subseteq> snd ` set (np gs bs hs data)"
  using assms[unfolded np_spec_def, rule_format, of gs bs hs data] by auto

lemma np_specD3:
  assumes "np_spec np" and "a \<in> set hs" and "b \<in> set hs" and "a \<noteq> b"
  shows "(a, b) \<in>\<^sub>p snd ` set (np gs bs hs data)"
  using assms(1)[unfolded np_spec_def, rule_format, of gs bs hs data] assms(2,3,4) by blast

lemma np_specD4:
  assumes "np_spec np" and "(True, p, q) \<in> set (np gs bs hs data)"
  shows "q \<in> set gs \<union> set bs"
  using assms(1)[unfolded np_spec_def, rule_format, of gs bs hs data] assms(2) by blast

lemma np_specE:
  assumes "np_spec np" and "p \<in> set hs" and "q \<in> set gs \<union> set bs \<union> set hs" and "p \<noteq> q"
  assumes 1: "\<And>q_in_bs. (q_in_bs, p, q) \<in> set (np gs bs hs data) \<Longrightarrow> thesis"
  assumes 2: "\<And>p_in_bs. (p_in_bs, q, p) \<in> set (np gs bs hs data) \<Longrightarrow> thesis"
  shows thesis
proof (cases "q \<in> set gs \<union> set bs")
  case True
  with assms(2) have "(p, q) \<in> set hs \<times> (set gs \<union> set bs)" by simp
  also from assms(1) have "... \<subseteq> snd ` set (np gs bs hs data)" by (rule np_specD2)
  finally obtain q_in_bs where "(q_in_bs, p, q) \<in> set (np gs bs hs data)" by fastforce
  thus ?thesis by (rule 1)
next
  case False
  with assms(3) have "q \<in> set hs" by simp
  from assms(1,2) this assms(4) have "(p, q) \<in>\<^sub>p snd ` set (np gs bs hs data)" by (rule np_specD3)
  hence "(p, q) \<in> snd ` set (np gs bs hs data) \<or> (q, p) \<in> snd ` set (np gs bs hs data)"
    by (simp only: in_pair_iff)
  thus ?thesis
  proof
    assume "(p, q) \<in> snd ` set (np gs bs hs data)"
    then obtain q_in_bs where "(q_in_bs, p, q) \<in> set (np gs bs hs data)" by fastforce
    thus ?thesis by (rule 1)
  next
    assume "(q, p) \<in> snd ` set (np gs bs hs data)"
    then obtain p_in_bs where "(p_in_bs, q, p) \<in> set (np gs bs hs data)" by fastforce
    thus ?thesis by (rule 2)
  qed
qed

definition add_pairs_single_naive :: "'d \<Rightarrow> ('t, 'b::zero, 'c) apsT"
  where "add_pairs_single_naive data flag gs bs h ps = ps @ (map (\<lambda>g. (flag, h, g)) gs) @ (map (\<lambda>b. (flag, h, b)) bs)"

lemma set_add_pairs_single_naive:
  "set (add_pairs_single_naive data flag gs bs h ps) = set ps \<union> Pair flag ` ({h} \<times> (set gs \<union> set bs))"
  by (auto simp add: add_pairs_single_naive_def Let_def)

fun add_pairs_single_sorted :: "((bool \<times> ('t, 'b, 'c) pdata_pair) \<Rightarrow> (bool \<times> ('t, 'b, 'c) pdata_pair) \<Rightarrow> bool) \<Rightarrow>
                                    ('t, 'b::zero, 'c) apsT" where
  "add_pairs_single_sorted _ _ [] [] _ ps = ps"|
  "add_pairs_single_sorted rel flag [] (b # bs) h ps =
    add_pairs_single_sorted rel flag [] bs h (insort_wrt rel (flag, h, b) ps)"|
  "add_pairs_single_sorted rel flag (g # gs) bs h ps =
    add_pairs_single_sorted rel flag gs bs h (insort_wrt rel (flag, h, g) ps)"

lemma set_add_pairs_single_sorted:
  "set (add_pairs_single_sorted rel flag gs bs h ps) = set ps \<union> Pair flag ` ({h} \<times> (set gs \<union> set bs))"
proof (induct gs arbitrary: ps)
  case Nil
  show ?case
  proof (induct bs arbitrary: ps)
    case Nil
    show ?case by simp
  next
    case (Cons b bs)
    show ?case by (simp add: Cons)
  qed
next
  case (Cons g gs)
  show ?case by (simp add: Cons)
qed

primrec (in -) pairs :: "('t, 'b, 'c) apsT \<Rightarrow> bool \<Rightarrow> ('t, 'b, 'c) pdata list \<Rightarrow> (bool \<times> ('t, 'b, 'c) pdata_pair) list"
  where
  "pairs _ _ [] = []"|
  "pairs aps flag (x # xs) = aps flag [] xs x (pairs aps flag xs)"

lemma pairs_subset:
  assumes "\<And>gs bs h ps. set (aps flag gs bs h ps) = set ps \<union> Pair flag ` ({h} \<times> (set gs \<union> set bs))"
  shows "set (pairs aps flag xs) \<subseteq> Pair flag ` (set xs \<times> set xs)"
proof (induct xs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  from Cons have "set (pairs aps flag xs) \<subseteq> Pair flag ` (set (x # xs) \<times> set (x # xs))" by fastforce
  moreover have "{x} \<times> set xs \<subseteq> set (x # xs) \<times> set (x # xs)" by fastforce
  ultimately show ?case by (auto simp add: assms)
qed

lemma in_pairsI:
  assumes "\<And>gs bs h ps. set (aps flag gs bs h ps) = set ps \<union> Pair flag ` ({h} \<times> (set gs \<union> set bs))"
    and "a \<noteq> b" and "a \<in> set xs" and "b \<in> set xs"
  shows "(flag, a, b) \<in> set (pairs aps flag xs) \<or> (flag, b, a) \<in> set (pairs aps flag xs)"
  using assms(3, 4)
proof (induct xs)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  from Cons(3) have d: "b = x \<or> b \<in> set xs" by simp
  from Cons(2) have "a = x \<or> a \<in> set xs" by simp
  thus ?case
  proof
    assume "a = x"
    with assms(2) have "b \<noteq> x" by simp
    with d have "b \<in> set xs" by simp
    hence "(flag, a, b) \<in> set (pairs aps flag (x # xs))" by (simp add: \<open>a = x\<close> assms(1))
    thus ?thesis by simp
  next
    assume "a \<in> set xs"
    from d show ?thesis
    proof
      assume "b = x"
      from \<open>a \<in> set xs\<close> have "(flag, b, a) \<in> set (pairs aps flag (x # xs))" by (simp add: \<open>b = x\<close> assms(1))
      thus ?thesis by simp
    next
      assume "b \<in> set xs"
      with \<open>a \<in> set xs\<close> have "(flag, a, b) \<in> set (pairs aps flag xs) \<or> (flag, b, a) \<in> set (pairs aps flag xs)"
        by (rule Cons(1))
      thus ?thesis by (auto simp: assms(1))
    qed
  qed
qed

corollary in_pairsI':
  assumes "\<And>gs bs h ps. set (aps flag gs bs h ps) = set ps \<union> Pair flag ` ({h} \<times> (set gs \<union> set bs))"
    and "a \<in> set xs" and "b \<in> set xs" and "a \<noteq> b"
  shows "(a, b) \<in>\<^sub>p snd ` set (pairs aps flag xs)"
proof -
  from assms(1,4,2,3) have "(flag, a, b) \<in> set (pairs aps flag xs) \<or> (flag, b, a) \<in> set (pairs aps flag xs)"
    by (rule in_pairsI)
  thus ?thesis
  proof
    assume "(flag, a, b) \<in> set (pairs aps flag xs)"
    hence "snd (flag, a, b) \<in> snd ` set (pairs aps flag xs)" by fastforce
    thus ?thesis by (simp add: in_pair_iff)
  next
    assume "(flag, b, a) \<in> set (pairs aps flag xs)"
    hence "snd (flag, b, a) \<in> snd ` set (pairs aps flag xs)" by fastforce
    thus ?thesis by (simp add: in_pair_iff)
  qed
qed

definition new_pairs_naive :: "('t, 'b::zero, 'c, 'd) npT"
  where "new_pairs_naive gs bs hs data =
            fold (add_pairs_single_naive data True gs bs) hs (pairs (add_pairs_single_naive data) False hs)"

definition new_pairs_sorted :: "(nat \<times> 'd \<Rightarrow> (bool \<times> ('t, 'b, 'c) pdata_pair) \<Rightarrow> (bool \<times> ('t, 'b, 'c) pdata_pair) \<Rightarrow> bool) \<Rightarrow>
                                    ('t, 'b::zero, 'c, 'd) npT"
  where "new_pairs_sorted rel gs bs hs data =
          fold (add_pairs_single_sorted (rel data) True gs bs) hs (pairs (add_pairs_single_sorted (rel data)) False hs)"

lemma set_fold_aps:
  assumes "\<And>gs bs h ps. set (aps flag gs bs h ps) = set ps \<union> Pair flag ` ({h} \<times> (set gs \<union> set bs))"
  shows "set (fold (aps flag gs bs) hs ps) = Pair flag ` (set hs \<times> (set gs \<union> set bs)) \<union> set ps"
proof (induct hs arbitrary: ps)
  case Nil
  show ?case by simp
next
  case (Cons h hs)
  show ?case by (auto simp add: Cons assms)
qed

lemma set_new_pairs_naive:
  "set (new_pairs_naive gs bs hs data) =
     Pair True ` (set hs \<times> (set gs \<union> set bs)) \<union> set (pairs (add_pairs_single_naive data) False hs)"
proof -
  have "set (new_pairs_naive gs bs hs data) =
          Pair True ` (set hs \<times> (set gs \<union> set bs)) \<union> set (pairs (add_pairs_single_naive data) False hs)"
    unfolding new_pairs_naive_def by (rule set_fold_aps, fact set_add_pairs_single_naive)
  thus ?thesis by (simp add: ac_simps)
qed

lemma set_new_pairs_sorted:
  "set (new_pairs_sorted rel gs bs hs data) =
      Pair True ` (set hs \<times> (set gs \<union> set bs)) \<union> set (pairs (add_pairs_single_sorted (rel data)) False hs)"
proof -
  have "set (new_pairs_sorted rel gs bs hs data) =
          Pair True ` (set hs \<times> (set gs \<union> set bs)) \<union> set (pairs (add_pairs_single_sorted (rel data)) False hs)"
    unfolding new_pairs_sorted_def by (rule set_fold_aps, fact set_add_pairs_single_sorted)
  thus ?thesis by (simp add: set_merge_wrt ac_simps)
qed

lemma (in -) fst_snd_Pair [simp]:
  shows "fst \<circ> Pair x = (\<lambda>_. x)" and "snd \<circ> Pair x = id"
  by auto

lemma np_spec_new_pairs_naive: "np_spec new_pairs_naive"
proof (rule np_specI)
  fix gs bs hs :: "('t, 'b, 'c) pdata list" and data::"nat \<times> 'd"
  have 1: "set hs \<times> (set gs \<union> set bs) \<subseteq> set hs \<times> (set gs \<union> set bs \<union> set hs)" by fastforce
  have "set (pairs (add_pairs_single_naive data) False hs) \<subseteq> Pair False ` (set hs \<times> set hs)"
    by (rule pairs_subset, simp add: set_add_pairs_single_naive)
  hence "snd ` set (pairs (add_pairs_single_naive data) False hs) \<subseteq> snd ` Pair False ` (set hs \<times> set hs)"
    by (rule image_mono)
  also have "... = set hs \<times> set hs" by (simp add: image_comp)
  finally have 2: "snd ` set (pairs (add_pairs_single_naive data) False hs) \<subseteq> set hs \<times> (set gs \<union> set bs \<union> set hs)"
    by fastforce
  
  show "snd ` set (new_pairs_naive gs bs hs data) \<subseteq> set hs \<times> (set gs \<union> set bs \<union> set hs) \<and>
       set hs \<times> (set gs \<union> set bs) \<subseteq> snd ` set (new_pairs_naive gs bs hs data) \<and>
       (\<forall>a b. a \<in> set hs \<longrightarrow> b \<in> set hs \<longrightarrow> a \<noteq> b \<longrightarrow> (a, b) \<in>\<^sub>p snd ` set (new_pairs_naive gs bs hs data)) \<and>
       (\<forall>p q. (True, p, q) \<in> set (new_pairs_naive gs bs hs data) \<longrightarrow> q \<in> set gs \<union> set bs)"
  proof (intro conjI allI impI)
    show "snd ` set (new_pairs_naive gs bs hs data) \<subseteq> set hs \<times> (set gs \<union> set bs \<union> set hs)"
      by (simp add: set_new_pairs_naive image_Un image_comp 1 2)
  next
    show "set hs \<times> (set gs \<union> set bs) \<subseteq> snd ` set (new_pairs_naive gs bs hs data)"
      by (simp add: set_new_pairs_naive image_Un image_comp)
  next
    fix a b
    assume "a \<in> set hs" and "b \<in> set hs" and "a \<noteq> b"
    with set_add_pairs_single_naive
    have "(a, b) \<in>\<^sub>p snd ` set (pairs (add_pairs_single_naive data) False hs)"
      by (rule in_pairsI')
    thus "(a, b) \<in>\<^sub>p snd ` set (new_pairs_naive gs bs hs data)"
      by (simp add: set_new_pairs_naive image_Un)
  next
    fix p q
    assume "(True, p, q) \<in> set (new_pairs_naive gs bs hs data)"
    hence "q \<in> set gs \<union> set bs \<or> (True, p, q) \<in> set (pairs (add_pairs_single_naive data) False hs)"
      by (auto simp: set_new_pairs_naive)
    thus "q \<in> set gs \<union> set bs"
    proof
      assume "(True, p, q) \<in> set (pairs (add_pairs_single_naive data) False hs)"
      also from set_add_pairs_single_naive have "... \<subseteq> Pair False ` (set hs \<times> set hs)"
        by (rule pairs_subset)
      finally show ?thesis by auto
    qed
  qed
qed

lemma np_spec_new_pairs_sorted: "np_spec (new_pairs_sorted rel)"
proof (rule np_specI)
  fix gs bs hs :: "('t, 'b, 'c) pdata list" and data::"nat \<times> 'd"
  have 1: "set hs \<times> (set gs \<union> set bs) \<subseteq> set hs \<times> (set gs \<union> set bs \<union> set hs)" by fastforce
  have "set (pairs (add_pairs_single_sorted (rel data)) False hs) \<subseteq> Pair False ` (set hs \<times> set hs)"
    by (rule pairs_subset, simp add: set_add_pairs_single_sorted)
  hence "snd ` set (pairs (add_pairs_single_sorted (rel data)) False hs) \<subseteq> snd ` Pair False ` (set hs \<times> set hs)"
    by (rule image_mono)
  also have "... = set hs \<times> set hs" by (simp add: image_comp)
  finally have 2: "snd ` set (pairs (add_pairs_single_sorted (rel data)) False hs) \<subseteq> set hs \<times> (set gs \<union> set bs \<union> set hs)"
    by fastforce
  
  show "snd ` set (new_pairs_sorted rel gs bs hs data) \<subseteq> set hs \<times> (set gs \<union> set bs \<union> set hs) \<and>
       set hs \<times> (set gs \<union> set bs) \<subseteq> snd ` set (new_pairs_sorted rel gs bs hs data) \<and>
       (\<forall>a b. a \<in> set hs \<longrightarrow> b \<in> set hs \<longrightarrow> a \<noteq> b \<longrightarrow> (a, b) \<in>\<^sub>p snd ` set (new_pairs_sorted rel gs bs hs data)) \<and>
       (\<forall>p q. (True, p, q) \<in> set (new_pairs_sorted rel gs bs hs data) \<longrightarrow> q \<in> set gs \<union> set bs)"
  proof (intro conjI allI impI)
    show "snd ` set (new_pairs_sorted rel gs bs hs data) \<subseteq> set hs \<times> (set gs \<union> set bs \<union> set hs)"
      by (simp add: set_new_pairs_sorted image_Un image_comp 1 2)
  next
    show "set hs \<times> (set gs \<union> set bs) \<subseteq> snd ` set (new_pairs_sorted rel gs bs hs data)"
      by (simp add: set_new_pairs_sorted image_Un image_comp)
  next
    fix a b
    assume "a \<in> set hs" and "b \<in> set hs" and "a \<noteq> b"
    with set_add_pairs_single_sorted
    have "(a, b) \<in>\<^sub>p snd ` set (pairs (add_pairs_single_sorted (rel data)) False hs)"
      by (rule in_pairsI')
    thus "(a, b) \<in>\<^sub>p snd ` set (new_pairs_sorted rel gs bs hs data)"
      by (simp add: set_new_pairs_sorted image_Un)
  next
    fix p q
    assume "(True, p, q) \<in> set (new_pairs_sorted rel gs bs hs data)"
    hence "q \<in> set gs \<union> set bs \<or> (True, p, q) \<in> set (pairs (add_pairs_single_sorted (rel data)) False hs)"
      by (auto simp: set_new_pairs_sorted)
    thus "q \<in> set gs \<union> set bs"
    proof
      assume "(True, p, q) \<in> set (pairs (add_pairs_single_sorted (rel data)) False hs)"
      also from set_add_pairs_single_sorted have "... \<subseteq> Pair False ` (set hs \<times> set hs)"
        by (rule pairs_subset)
      finally show ?thesis by auto
    qed
  qed
qed

text \<open>@{term "new_pairs_naive gs bs hs data"} and @{term "new_pairs_sorted rel gs bs hs data"} return
  lists of triples @{term "(q_in_bs, p, q)"}, where \<open>q_in_bs\<close> indicates whether \<open>q\<close> is contained in
  the list @{term "gs @ bs"} or in the list \<open>hs\<close>. \<open>p\<close> is always contained in \<open>hs\<close>.\<close>

definition canon_pair_order_aux :: "('t, 'b::zero, 'c) pdata_pair \<Rightarrow> ('t, 'b, 'c) pdata_pair \<Rightarrow> bool"
  where "canon_pair_order_aux p q \<longleftrightarrow>
          (lcs (lp (fst (fst p))) (lp (fst (snd p))) \<preceq> lcs (lp (fst (fst q))) (lp (fst (snd q))))"

abbreviation "canon_pair_order data p q \<equiv> canon_pair_order_aux (snd p) (snd q)"

abbreviation "canon_pair_comb \<equiv> merge_wrt canon_pair_order_aux"

subsubsection \<open>Applying Criteria to New Pairs\<close>

definition apply_icrit :: "('t, 'b, 'c, 'd) icritT \<Rightarrow> (nat \<times> 'd) \<Rightarrow> ('t, 'b, 'c) pdata list \<Rightarrow>
                                ('t, 'b, 'c) pdata list \<Rightarrow> ('t, 'b, 'c) pdata list \<Rightarrow>
                                (bool \<times> ('t, 'b, 'c) pdata_pair) list \<Rightarrow>
                                (bool \<times> bool \<times> ('t, 'b, 'c) pdata_pair) list"
  where "apply_icrit crit data gs bs hs ps = (let c = crit data gs bs hs in map (\<lambda>(q_in_bs, p, q). (c p q, q_in_bs, p, q)) ps)"

lemma fst_apply_icrit:
  assumes "icrit_spec crit" and "dickson_grading d"
    and "fst ` (set gs \<union> set bs \<union> set hs) \<subseteq> dgrad_p_set d m" and "unique_idx (gs @ bs @ hs) data"
    and "is_Groebner_basis (fst ` set gs)" and "p \<in> set hs" and "q \<in> set gs \<union> set bs \<union> set hs"
    and "fst p \<noteq> 0" and "fst q \<noteq> 0" and "(True, q_in_bs, p, q) \<in> set (apply_icrit crit data gs bs hs ps)"
  shows "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs \<union> set hs)) (fst p) (fst q)"
proof -
  from assms(10) have "crit data gs bs hs p q" by (auto simp: apply_icrit_def)
  with assms(1-9) show ?thesis by (rule icrit_specD)
qed

lemma snd_apply_icrit [simp]: "map snd (apply_icrit crit data gs bs hs ps) = ps"
  by (auto simp add: apply_icrit_def case_prod_beta' intro: nth_equalityI)

lemma set_snd_apply_icrit [simp]: "snd ` set (apply_icrit crit data gs bs hs ps) = set ps"
proof -
  have "snd ` set (apply_icrit crit data gs bs hs ps) = set (map snd (apply_icrit crit data gs bs hs ps))"
    by (simp del: snd_apply_icrit)
  also have "... = set ps" by (simp only: snd_apply_icrit)
  finally show ?thesis .
qed

definition apply_ncrit :: "('t, 'b, 'c, 'd) ncritT \<Rightarrow> (nat \<times> 'd) \<Rightarrow> ('t, 'b, 'c) pdata list \<Rightarrow>
                                ('t, 'b, 'c) pdata list \<Rightarrow> ('t, 'b, 'c) pdata list \<Rightarrow>
                                (bool \<times> bool \<times> ('t, 'b, 'c) pdata_pair) list \<Rightarrow>
                                (bool \<times> ('t, 'b, 'c) pdata_pair) list"
  where "apply_ncrit crit data gs bs hs ps =
          (let c = crit data gs bs hs in
              rev (fold (\<lambda>(ic, q_in_bs, p, q). \<lambda>ps'. if \<not> ic \<and> c q_in_bs ps' p q then ps' else (ic, p, q) # ps') ps []))"

lemma apply_ncrit_append:
  "apply_ncrit crit data gs bs hs (xs @ ys) =
    rev (fold (\<lambda>(ic, q_in_bs, p, q). \<lambda>ps'. if \<not> ic \<and> crit data gs bs hs q_in_bs ps' p q then ps' else (ic, p, q) # ps') ys
          (rev (apply_ncrit crit data gs bs hs xs)))"
  by (simp add: apply_ncrit_def Let_def)

lemma fold_superset:
  "set acc \<subseteq>
    set (fold (\<lambda>(ic, q_in_bs, p, q). \<lambda>ps'. if \<not> ic \<and> c q_in_bs ps' p q then ps' else (ic, p, q) # ps') ps acc)"
proof (induct ps arbitrary: acc)
  case Nil
  show ?case by simp
next
  case (Cons x ps)
  obtain ic' q_in_bs' p' q' where x: "x = (ic', q_in_bs', p', q')" using prod_cases4 by blast
  have 1: "set acc0 \<subseteq> set (fold (\<lambda>(ic, q_in_bs, p, q) ps'. if \<not> ic \<and> c q_in_bs ps' p q then ps' else (ic, p, q) # ps') ps acc0)"
    for acc0 by (rule Cons)
  have "set acc \<subseteq> set ((ic', p', q') # acc)" by fastforce
  also have "... \<subseteq> set (fold (\<lambda>(ic, q_in_bs, p, q) ps'. if \<not> ic \<and> c q_in_bs ps' p q then ps' else (ic, p, q) # ps') ps
                    ((ic', p', q') # acc))" by (fact 1)
  finally have 2: "set acc \<subseteq> set (fold (\<lambda>(ic, q_in_bs, p, q) ps'. if \<not> ic \<and> c q_in_bs ps' p q then ps' else (ic, p, q) # ps') ps
                              ((ic', p', q') # acc))" .
  show ?case by (simp add: x 1 2)
qed

lemma apply_ncrit_superset:
  "set (apply_ncrit crit data gs bs hs ps) \<subseteq> set (apply_ncrit crit data gs bs hs (ps @ qs))" (is "?l \<subseteq> ?r")
proof -
  have "?l = set (rev (apply_ncrit crit data gs bs hs ps))" by simp
  also have "... \<subseteq> set (fold (\<lambda>(ic, q_in_bs, p, q) ps'.
                          if \<not> ic \<and> crit data gs bs hs q_in_bs ps' p q then ps' else (ic, p, q) # ps')
                  qs (rev (apply_ncrit crit data gs bs hs ps)))" by (fact fold_superset)
  also have "... = ?r" by (simp add: apply_ncrit_append)
  finally show ?thesis .
qed

lemma apply_ncrit_subset_aux:
  assumes "(ic, p, q) \<in> set (fold
            (\<lambda>(ic, q_in_bs, p, q). \<lambda>ps'. if \<not> ic \<and> c q_in_bs ps' p q then ps' else (ic, p, q) # ps') ps acc)"
  shows "(ic, p, q) \<in> set acc \<or> (\<exists>q_in_bs. (ic, q_in_bs, p, q) \<in> set ps)"
  using assms
proof (induct ps arbitrary: acc)
  case Nil
  thus ?case by simp
next
  case (Cons x ps)
  obtain ic' q_in_bs' p' q' where x: "x = (ic', q_in_bs', p', q')" using prod_cases4 by blast
  from Cons(2) have "(ic, p, q) \<in>
      set (fold (\<lambda>(ic, q_in_bs, p, q) ps'. if \<not> ic \<and> c q_in_bs ps' p q then ps' else (ic, p, q) # ps') ps
             (if \<not> ic' \<and> c q_in_bs' acc p' q' then acc else (ic', p', q') # acc))" by (simp add: x)
  hence "(ic, p, q) \<in> set (if \<not> ic' \<and> c q_in_bs' acc p' q' then acc else (ic', p', q') # acc) \<or>
          (\<exists>q_in_bs. (ic, q_in_bs, p, q) \<in> set ps)" by (rule Cons(1))
  hence "(ic, p, q) \<in> set acc \<or> (ic, p, q) = (ic', p', q') \<or> (\<exists>q_in_bs. (ic, q_in_bs, p, q) \<in> set ps)"
    by (auto split: if_splits)
  thus ?case
  proof (elim disjE)
    assume "(ic, p, q) \<in> set acc"
    thus ?thesis ..
  next
    assume "(ic, p, q) = (ic', p', q')"
    hence "x = (ic, q_in_bs', p, q)" by (simp add: x)
    thus ?thesis by auto
  next
    assume "\<exists>q_in_bs. (ic, q_in_bs, p, q) \<in> set ps"
    then obtain q_in_bs where "(ic, q_in_bs, p, q) \<in> set ps" ..
    thus ?thesis by auto
  qed
qed

corollary apply_ncrit_subset:
  assumes "(ic, p, q) \<in> set (apply_ncrit crit data gs bs hs ps)"
  obtains q_in_bs where "(ic, q_in_bs, p, q) \<in> set ps"
proof -
  from assms
  have "(ic, p, q) \<in> set (fold
          (\<lambda>(ic, q_in_bs, p, q). \<lambda>ps'. if \<not> ic \<and> crit data gs bs hs q_in_bs ps' p q then ps' else (ic, p, q) # ps') ps [])"
    by (simp add: apply_ncrit_def)
  hence "(ic, p, q) \<in> set [] \<or> (\<exists>q_in_bs. (ic, q_in_bs, p, q) \<in> set ps)"
    by (rule apply_ncrit_subset_aux)
  hence "\<exists>q_in_bs. (ic, q_in_bs, p, q) \<in> set ps" by simp
  then obtain q_in_bs where "(ic, q_in_bs, p, q) \<in> set ps" ..
  thus ?thesis ..
qed

corollary apply_ncrit_subset': "snd ` set (apply_ncrit crit data gs bs hs ps) \<subseteq> snd ` snd ` set ps"
proof
  fix p q
  assume "(p, q) \<in> snd ` set (apply_ncrit crit data gs bs hs ps)"
  then obtain ic where "(ic, p, q) \<in> set (apply_ncrit crit data gs bs hs ps)" by fastforce
  then obtain q_in_bs where "(ic, q_in_bs, p, q) \<in> set ps" by (rule apply_ncrit_subset)
  thus "(p, q) \<in> snd ` snd ` set ps" by force
qed

lemma not_in_apply_ncrit:
  assumes "(ic, p, q) \<notin> set (apply_ncrit crit data gs bs hs (xs @ ((ic, q_in_bs, p, q) # ys)))"
  shows "crit data gs bs hs q_in_bs (rev (apply_ncrit crit data gs bs hs xs)) p q"
  using assms
proof (simp add: apply_ncrit_append split: if_splits)
  assume "(ic, p, q) \<notin>
            set (fold (\<lambda>(ic, q_in_bs, p, q) ps'. if \<not> ic \<and> crit data gs bs hs q_in_bs ps' p q then ps' else (ic, p, q) # ps')
             ys ((ic, p, q) # rev (apply_ncrit crit data gs bs hs xs)))" (is "_ \<notin> ?A")
  have "(ic, p, q) \<in> set ((ic, p, q) # rev (apply_ncrit crit data gs bs hs xs))" by simp
  also have "... \<subseteq> ?A" by (rule fold_superset)
  finally have "(ic, p, q) \<in> ?A" .
  with \<open>(ic, p, q) \<notin> ?A\<close> show ?thesis ..
qed

lemma (in -) setE:
  assumes "x \<in> set xs"
  obtains ys zs where "xs = ys @ (x # zs)"
  using assms
proof (induct xs arbitrary: thesis)
  case Nil
  from Nil(2) show ?case by simp
next
  case (Cons a xs)
  from Cons(3) have "x = a \<or> x \<in> set xs" by simp
  thus ?case
  proof
    assume "x = a"
    show ?thesis by (rule Cons(2)[of "[]" xs], simp add: \<open>x = a\<close>)
  next
    assume "x \<in> set xs"
    then obtain ys zs where "xs = ys @ (x # zs)" by (meson Cons(1))
    show ?thesis by (rule Cons(2)[of "a # ys" zs], simp add: \<open>xs = ys @ (x # zs)\<close>)
  qed
qed

lemma apply_ncrit_connectible:
  assumes "ncrit_spec crit" and "dickson_grading d"
    and "set gs \<union> set bs \<union> set hs \<subseteq> B" and "fst ` B \<subseteq> dgrad_p_set d m"
    and "snd ` snd ` set ps \<subseteq> set hs \<times> (set gs \<union> set bs \<union> set hs)" and "unique_idx (gs @ bs @ hs) data"
    and "is_Groebner_basis (fst ` set gs)"
    and "\<And>p' q'. (p', q') \<in> snd ` set (apply_ncrit crit data gs bs hs ps) \<Longrightarrow>
                 fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow> crit_pair_cbelow_on d m (fst ` B) (fst p') (fst q')"
    and "\<And>p' q'. p' \<in> set gs \<union> set bs \<Longrightarrow> q' \<in> set gs \<union> set bs \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
                 crit_pair_cbelow_on d m (fst ` B) (fst p') (fst q')"
  assumes "(ic, q_in_bs, p, q) \<in> set ps" and "fst p \<noteq> 0" and "fst q \<noteq> 0"
    and "q_in_bs \<Longrightarrow> (q \<in> set gs \<union> set bs)"
  shows "crit_pair_cbelow_on d m (fst ` B) (fst p) (fst q)"
proof (cases "(p, q) \<in> snd ` set (apply_ncrit crit data gs bs hs ps)")
  case True
  thus ?thesis using assms(11,12) by (rule assms(8))
next
  case False
  from assms(10) have "(p, q) \<in> snd ` snd ` set ps" by force
  also have "... \<subseteq> set hs \<times> (set gs \<union> set bs \<union> set hs)" by (fact assms(5))
  finally have "p \<in> set hs" and "q \<in> set gs \<union> set bs \<union> set hs" by simp_all
  from \<open>(ic, q_in_bs, p, q) \<in> set ps\<close> obtain xs ys where ps: "ps = xs @ ((ic, q_in_bs, p, q) # ys)"
    by (rule setE)

  let ?ps = "rev (apply_ncrit crit data gs bs hs xs)"
  have "snd ` set ?ps \<subseteq> snd ` snd ` set xs" by (simp add: apply_ncrit_subset')
  also have "... \<subseteq> snd ` snd ` set ps" unfolding ps by fastforce
  finally have sub: "snd ` set ?ps \<subseteq> set hs \<times> (set gs \<union> set bs \<union> set hs)"
    using assms(5) by (rule subset_trans)
  from False have "(p, q) \<notin> snd ` set (apply_ncrit crit data gs bs hs ps)" by (simp add: in_pair_iff)
  hence "(ic, p, q) \<notin> set (apply_ncrit crit data gs bs hs (xs @ ((ic, q_in_bs, p, q) # ys)))"
    unfolding ps by force
  hence "crit data gs bs hs q_in_bs ?ps p q" by (rule not_in_apply_ncrit)
  with assms(1-4) sub assms(6,7,13) _ _ \<open>p \<in> set hs\<close> \<open>q \<in> set gs \<union> set bs \<union> set hs\<close> assms(11,12)
  show ?thesis
  proof (rule ncrit_specD)
    fix p' q'
    assume "(p', q') \<in>\<^sub>p snd ` set ?ps"
    also have "... \<subseteq> snd ` set (apply_ncrit crit data gs bs hs ps)"
      by (rule image_mono, simp add: ps apply_ncrit_superset)
    finally have disj: "(p', q') \<in> snd ` set (apply_ncrit crit data gs bs hs ps) \<or>
                    (q', p') \<in> snd ` set (apply_ncrit crit data gs bs hs ps)" by (simp only: in_pair_iff)
    assume "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
    from disj show "crit_pair_cbelow_on d m (fst ` B) (fst p') (fst q')"
    proof
      assume "(p', q') \<in> snd ` set (apply_ncrit crit data gs bs hs ps)"
      thus ?thesis using \<open>fst p' \<noteq> 0\<close> \<open>fst q' \<noteq> 0\<close> by (rule assms(8))
    next
      assume "(q', p') \<in> snd ` set (apply_ncrit crit data gs bs hs ps)"
      hence "crit_pair_cbelow_on d m (fst ` B) (fst q') (fst p')"
        using \<open>fst q' \<noteq> 0\<close> \<open>fst p' \<noteq> 0\<close> by (rule assms(8))
      thus ?thesis by (rule crit_pair_cbelow_sym)
    qed
  qed (assumption, fact assms(9))
qed

subsubsection \<open>Applying Criteria to Old Pairs\<close>

definition apply_ocrit :: "('t, 'b, 'c, 'd) ocritT \<Rightarrow> (nat \<times> 'd) \<Rightarrow> ('t, 'b, 'c) pdata list \<Rightarrow>
                                (bool \<times> ('t, 'b, 'c) pdata_pair) list \<Rightarrow> ('t, 'b, 'c) pdata_pair list \<Rightarrow>
                                ('t, 'b, 'c) pdata_pair list"
  where "apply_ocrit crit data hs ps' ps = (let c = crit data hs ps' in [(p, q)\<leftarrow>ps . \<not> c p q])"

lemma set_apply_ocrit:
  "set (apply_ocrit crit data hs ps' ps) = {(p, q) | p q. (p, q) \<in> set ps \<and> \<not> crit data hs ps' p q}"
  by (auto simp: apply_ocrit_def)

corollary set_apply_ocrit_iff:
  "(p, q) \<in> set (apply_ocrit crit data hs ps' ps) \<longleftrightarrow> ((p, q) \<in> set ps \<and> \<not> crit data hs ps' p q)"
  by (auto simp: apply_ocrit_def)

lemma apply_ocrit_connectible:
  assumes "ocrit_spec crit" and "dickson_grading d" and "set hs \<subseteq> B" and "fst ` B \<subseteq> dgrad_p_set d m"
  and "unique_idx (p # q # hs @ (map (fst \<circ> snd) ps') @ (map (snd \<circ> snd) ps')) data"
  and "\<And>p' q'. (p', q') \<in> snd ` set ps' \<Longrightarrow> fst p' \<noteq> 0 \<Longrightarrow> fst q' \<noteq> 0 \<Longrightarrow>
                crit_pair_cbelow_on d m (fst ` B) (fst p') (fst q')"
  assumes "p \<in> B" and "q \<in> B" and "fst p \<noteq> 0" and "fst q \<noteq> 0"
    and "(p, q) \<in> set ps" and "(p, q) \<notin> set (apply_ocrit crit data hs ps' ps)"
  shows "crit_pair_cbelow_on d m (fst ` B) (fst p) (fst q)"
proof -
  from assms(11,12) have "crit data hs ps' p q" by (simp add: set_apply_ocrit_iff)
  with assms(1-5) _ assms(7-10) show ?thesis
  proof (rule ocrit_specD)
    fix p' q'
    assume "(p', q') \<in>\<^sub>p snd ` set ps'"
    hence disj: "(p', q') \<in> snd ` set ps' \<or> (q', p') \<in> snd ` set ps'" by (simp only: in_pair_iff)
    assume "fst p' \<noteq> 0" and "fst q' \<noteq> 0"
    from disj show "crit_pair_cbelow_on d m (fst ` B) (fst p') (fst q')"
    proof
      assume "(p', q') \<in> snd ` set ps'"
      thus ?thesis using \<open>fst p' \<noteq> 0\<close> \<open>fst q' \<noteq> 0\<close> by (rule assms(6))
    next
      assume "(q', p') \<in> snd ` set ps'"
      hence "crit_pair_cbelow_on d m (fst ` B) (fst q') (fst p')" using \<open>fst q' \<noteq> 0\<close> \<open>fst p' \<noteq> 0\<close>
        by (rule assms(6))
      thus ?thesis by (rule crit_pair_cbelow_sym)
    qed
  qed
qed

subsubsection \<open>Creating Final List of Pairs\<close>

context
  fixes np::"('t, 'b::field, 'c, 'd) npT"
    and icrit::"('t, 'b, 'c, 'd) icritT"
    and ncrit::"('t, 'b, 'c, 'd) ncritT"
    and ocrit::"('t, 'b, 'c, 'd) ocritT"
    and comb::"('t, 'b, 'c) pdata_pair list \<Rightarrow> ('t, 'b, 'c) pdata_pair list \<Rightarrow> ('t, 'b, 'c) pdata_pair list"
begin

definition add_pairs :: "('t, 'b, 'c, 'd) apT"
  where "add_pairs gs bs ps hs data =
          (let ps1 = apply_ncrit ncrit data gs bs hs (apply_icrit icrit data gs bs hs (np gs bs hs data));
               ps2 = apply_ocrit ocrit data hs ps1 ps in comb (map snd [x\<leftarrow>ps1 . \<not> fst x]) ps2)"

lemma set_add_pairs:
  assumes "\<And>xs ys. set (comb xs ys) = set xs \<union> set ys"
  assumes "ps1 = apply_ncrit ncrit data gs bs hs (apply_icrit icrit data gs bs hs (np gs bs hs data))"
  shows "set (add_pairs gs bs ps hs data) =
              {(p, q) | p q. (False, p, q) \<in> set ps1 \<or> ((p, q) \<in> set ps \<and> \<not> ocrit data hs ps1 p q)}"
proof -
  have eq: "snd ` {x \<in> set ps1. \<not> fst x} = {(p, q) | p q. (False, p, q) \<in> set ps1}" by force
  thus ?thesis by (auto simp: add_pairs_def Let_def assms(1) assms(2)[symmetric] set_apply_ocrit)
qed

lemma set_add_pairs_iff:
  assumes "\<And>xs ys. set (comb xs ys) = set xs \<union> set ys"
  assumes "ps1 = apply_ncrit ncrit data gs bs hs (apply_icrit icrit data gs bs hs (np gs bs hs data))"
  shows "((p, q) \<in> set (add_pairs gs bs ps hs data)) \<longleftrightarrow>
              ((False, p, q) \<in> set ps1 \<or> ((p, q) \<in> set ps \<and> \<not> ocrit data hs ps1 p q))"
proof -
  from assms have eq: "set (add_pairs gs bs ps hs data) =
              {(p, q) | p q. (False, p, q) \<in> set ps1 \<or> ((p, q) \<in> set ps \<and> \<not> ocrit data hs ps1 p q)}"
    by (rule set_add_pairs)
  obtain a aa b where p: "p = (a, aa, b)" using prod_cases3 by blast
  obtain ab ac ba where q: "q = (ab, ac, ba)" using prod_cases3 by blast
  show ?thesis by (simp add: eq p q)
qed

lemma ap_spec_add_pairs:
  assumes "np_spec np" and "icrit_spec icrit" and "ncrit_spec ncrit" and "ocrit_spec ocrit"
    and "\<And>xs ys. set (comb xs ys) = set xs \<union> set ys"
  shows "ap_spec add_pairs"
proof (rule ap_specI)
  fix gs bs :: "('t, 'b, 'c) pdata list" and ps hs and data::"nat \<times> 'd"
  define ps1 where "ps1 = apply_ncrit ncrit data gs bs hs (apply_icrit icrit data gs bs hs (np gs bs hs data))"
  show "set (add_pairs gs bs ps hs data) \<subseteq> set ps \<union> set hs \<times> (set gs \<union> set bs \<union> set hs)"
  proof
    fix p q
    assume "(p, q) \<in> set (add_pairs gs bs ps hs data)"
    with assms(5) ps1_def have "(False, p, q) \<in> set ps1 \<or> ((p, q) \<in> set ps \<and> \<not> ocrit data hs ps1 p q)"
      by (simp add: set_add_pairs_iff)
    thus "(p, q) \<in> set ps \<union> set hs \<times> (set gs \<union> set bs \<union> set hs)"
    proof
      assume "(False, p, q) \<in> set ps1"
      hence "snd (False, p, q) \<in> snd ` set ps1" by fastforce
      hence "(p, q) \<in> snd ` set ps1" by simp
      also have "... \<subseteq> snd ` snd ` set (apply_icrit icrit data gs bs hs (np gs bs hs data))"
        unfolding ps1_def by (fact apply_ncrit_subset')
      also have "... = snd ` set (np gs bs hs data)" by simp
      also from assms(1) have "... \<subseteq> set hs \<times> (set gs \<union> set bs \<union> set hs)" by (rule np_specD1)
      finally show ?thesis ..
    next
      assume "(p, q) \<in> set ps \<and> \<not> ocrit data hs ps1 p q"
      thus ?thesis by simp
    qed
  qed
next
  fix gs bs :: "('t, 'b, 'c) pdata list" and ps hs and data::"nat \<times> 'd" and B and d::"'a \<Rightarrow> nat" and m h g
  assume dg: "dickson_grading d" and B_sup: "set gs \<union> set bs \<union> set hs \<subseteq> B"
    and B_sub: "fst ` B \<subseteq> dgrad_p_set d m" and h_in: "h \<in> set hs" and g_in: "g \<in> set gs \<union> set bs \<union> set hs"
    and ps_sub: "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)"
    and uid: "unique_idx (gs @ bs @ hs) data" and gb: "is_Groebner_basis (fst ` set gs)" and "h \<noteq> g"
    and "fst h \<noteq> 0" and "fst g \<noteq> 0"
  assume a: "\<And>a b. (a, b) \<in>\<^sub>p set (add_pairs gs bs ps hs data) \<Longrightarrow>
               fst a \<noteq> 0 \<Longrightarrow> fst b \<noteq> 0 \<Longrightarrow> crit_pair_cbelow_on d m (fst ` B) (fst a) (fst b)"
  assume b: "\<And>a b. a \<in> set gs \<union> set bs \<Longrightarrow>
               b \<in> set gs \<union> set bs \<Longrightarrow>
               fst a \<noteq> 0 \<Longrightarrow> fst b \<noteq> 0 \<Longrightarrow> crit_pair_cbelow_on d m (fst ` B) (fst a) (fst b)"
  define ps0 where "ps0 = apply_icrit icrit data gs bs hs (np gs bs hs data)"
  define ps1 where "ps1 = apply_ncrit ncrit data gs bs hs ps0"

  have "snd ` snd ` set ps0 = snd ` set (np gs bs hs data)" by (simp add: ps0_def)
  also from assms(1) have "... \<subseteq> set hs \<times> (set gs \<union> set bs \<union> set hs)" by (rule np_specD1)
  finally have ps0_sub: "snd ` snd ` set ps0 \<subseteq> set hs \<times> (set gs \<union> set bs \<union> set hs)" .

  have "crit_pair_cbelow_on d m (fst ` B) (fst p) (fst q)"
    if "(p, q) \<in> snd ` set ps1" and "fst p \<noteq> 0" and "fst q \<noteq> 0" for p q
  proof -
    from \<open>(p, q) \<in> snd ` set ps1\<close> obtain ic where "(ic, p, q) \<in> set ps1" by fastforce
    show ?thesis
    proof (cases "ic")
      case True
      from \<open>(ic, p, q) \<in> set ps1\<close> obtain q_in_bs where "(ic, q_in_bs, p, q) \<in> set ps0"
        unfolding ps1_def by (rule apply_ncrit_subset)
      with True have "(True, q_in_bs, p, q) \<in> set ps0" by simp
      hence "snd (snd (True, q_in_bs, p, q)) \<in> snd ` snd ` set ps0" by fastforce
      hence "(p, q) \<in> snd ` snd ` set ps0" by simp
      also have "... \<subseteq> set hs \<times> (set gs \<union> set bs \<union> set hs)" by (fact ps0_sub)
      finally have "p \<in> set hs" and "q \<in> set gs \<union> set bs \<union> set hs" by simp_all
      from B_sup have B_sup': "fst ` (set gs \<union> set bs \<union> set hs) \<subseteq> fst ` B" by (rule image_mono)
      hence "fst ` (set gs \<union> set bs \<union> set hs) \<subseteq> dgrad_p_set d m" using B_sub by (rule subset_trans)
      from assms(2) dg this uid gb \<open>p \<in> set hs\<close> \<open>q \<in> set gs \<union> set bs \<union> set hs\<close> \<open>fst p \<noteq> 0\<close> \<open>fst q \<noteq> 0\<close>
        \<open>(True, q_in_bs, p, q) \<in> set ps0\<close>
      have "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs \<union> set hs)) (fst p) (fst q)"
        unfolding ps0_def by (rule fst_apply_icrit)
      thus ?thesis using B_sup' by (rule crit_pair_cbelow_mono)
    next
      case False
      with \<open>(ic, p, q) \<in> set ps1\<close> have "(False, p, q) \<in> set ps1" by simp
      with assms(5) ps1_def have "(p, q) \<in> set (add_pairs gs bs ps hs data)"
        by (simp add: set_add_pairs_iff ps0_def)
      hence "(p, q) \<in>\<^sub>p set (add_pairs gs bs ps hs data)" by (simp add: in_pair_iff)
      thus ?thesis using \<open>fst p \<noteq> 0\<close> \<open>fst q \<noteq> 0\<close> by (rule a)
    qed
  qed
  with assms(3) dg B_sup B_sub ps0_sub uid gb
  have *: "(ic, q_in_bs, p, q) \<in> set ps0 \<Longrightarrow> fst p \<noteq> 0 \<Longrightarrow> fst q \<noteq> 0 \<Longrightarrow>
            (q_in_bs \<Longrightarrow> q \<in> set gs \<union> set bs) \<Longrightarrow> crit_pair_cbelow_on d m (fst ` B) (fst p) (fst q)"
    for ic q_in_bs p q using b unfolding ps1_def by (rule apply_ncrit_connectible)

  show "crit_pair_cbelow_on d m (fst ` B) (fst h) (fst g)"
  proof (cases "h = g")
    case True
    from g_in B_sup have "g \<in> B" ..
    hence "fst g \<in> fst ` B" by simp
    hence "fst g \<in> dgrad_p_set d m" using B_sub ..
    with dg show ?thesis unfolding True by (rule crit_pair_cbelow_same)
  next
    case False
    with assms(1) h_in g_in show ?thesis
    proof (rule np_specE)
      fix g_in_bs
      assume "(g_in_bs, h, g) \<in> set (np gs bs hs data)"
      also have "... = snd ` set ps0" by (simp add: ps0_def)
      finally obtain ic where "(ic, g_in_bs, h, g) \<in> set ps0" by fastforce
      moreover note \<open>fst h \<noteq> 0\<close> \<open>fst g \<noteq> 0\<close>
      moreover from assms(1) have "g \<in> set gs \<union> set bs" if "g_in_bs"
      proof (rule np_specD4)
        from \<open>(g_in_bs, h, g) \<in> set (np gs bs hs data)\<close> that show "(True, h, g) \<in> set (np gs bs hs data)"
          by simp
      qed
      ultimately show ?thesis by (rule *)
    next
      fix h_in_bs
      assume "(h_in_bs, g, h) \<in> set (np gs bs hs data)"
      also have "... = snd ` set ps0" by (simp add: ps0_def)
      finally obtain ic where "(ic, h_in_bs, g, h) \<in> set ps0" by fastforce
      moreover note \<open>fst g \<noteq> 0\<close> \<open>fst h \<noteq> 0\<close>
      moreover from assms(1) have "h \<in> set gs \<union> set bs" if "h_in_bs"
      proof (rule np_specD4)
        from \<open>(h_in_bs, g, h) \<in> set (np gs bs hs data)\<close> that show "(True, g, h) \<in> set (np gs bs hs data)"
          by simp
      qed
      ultimately have "crit_pair_cbelow_on d m (fst ` B) (fst g) (fst h)" by (rule *)
      thus ?thesis by (rule crit_pair_cbelow_sym)
    qed
  qed
next
  fix gs bs :: "('t, 'b, 'c) pdata list" and ps hs and data::"nat \<times> 'd" and B and d::"'a \<Rightarrow> nat" and m h g
  define ps1 where "ps1 = apply_ncrit ncrit data gs bs hs (apply_icrit icrit data gs bs hs (np gs bs hs data))"
  assume "(h, g) \<in> set ps -\<^sub>p set (add_pairs gs bs ps hs data)"
  hence "(h, g) \<in> set ps" and "(h, g) \<notin>\<^sub>p set (add_pairs gs bs ps hs data)" by simp_all
  from this(2) have "(h, g) \<notin> set (add_pairs gs bs ps hs data)" by (simp add: in_pair_iff)
  assume dg: "dickson_grading d" and B_sup: "set gs \<union> set bs \<union> set hs \<subseteq> B" and B_sub: "fst ` B \<subseteq> dgrad_p_set d m"
    and ps_sub: "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)"
    and "(set gs \<union> set bs) \<inter> set hs = {}" \<comment> \<open>unused\<close>
    and uid: "unique_idx (gs @ bs @ hs) data" and gb: "is_Groebner_basis (fst ` set gs)"
    and "h \<noteq> g" and "fst h \<noteq> 0" and "fst g \<noteq> 0"
  assume *: "\<And>a b. (a, b) \<in>\<^sub>p set (add_pairs gs bs ps hs data) \<Longrightarrow>
               (a, b) \<in>\<^sub>p set hs \<times> (set gs \<union> set bs \<union> set hs) \<Longrightarrow>
               fst a \<noteq> 0 \<Longrightarrow> fst b \<noteq> 0 \<Longrightarrow> crit_pair_cbelow_on d m (fst ` B) (fst a) (fst b)"

  have "snd ` set ps1 \<subseteq> snd ` snd ` set (apply_icrit icrit data gs bs hs (np gs bs hs data))"
    unfolding ps1_def by (rule apply_ncrit_subset')
  also have "... = snd ` set (np gs bs hs data)" by simp
  also from assms(1) have "... \<subseteq> set hs \<times> (set gs \<union> set bs \<union> set hs)" by (rule np_specD1)
  finally have ps1_sub: "snd ` set ps1 \<subseteq> set hs \<times> (set gs \<union> set bs \<union> set hs)" .

  from \<open>(h, g) \<in> set ps\<close> ps_sub have h_in: "h \<in> set gs \<union> set bs" and g_in: "g \<in> set gs \<union> set bs"
    by fastforce+
  with B_sup have "h \<in> B" and "g \<in> B" by auto
  with assms(4) dg _ B_sub _ _ show "crit_pair_cbelow_on d m (fst ` B) (fst h) (fst g)"
    using \<open>fst h \<noteq> 0\<close> \<open>fst g \<noteq> 0\<close> \<open>(h, g) \<in> set ps\<close>
  proof (rule apply_ocrit_connectible)
    from B_sup show "set hs \<subseteq> B" by simp
  next
    from ps1_sub h_in g_in
    have "set (h # g # hs @ map (fst \<circ> snd) ps1 @ map (snd \<circ> snd) ps1) \<subseteq> set (gs @ bs @ hs)"
      by fastforce
    with uid show "unique_idx (h # g # hs @ map (fst \<circ> snd) ps1 @ map (snd \<circ> snd) ps1) data"
      by (rule unique_idx_subset)
  next
    fix p q
    assume "(p, q) \<in> snd ` set ps1"
    hence pq_in: "(p, q) \<in> set hs \<times> (set gs \<union> set bs \<union> set hs)" using ps1_sub ..
    hence p_in: "p \<in> set hs" and q_in: "q \<in> set gs \<union> set bs \<union> set hs" by simp_all
    assume "fst p \<noteq> 0" and "fst q \<noteq> 0"
    from \<open>(p, q) \<in> snd ` set ps1\<close> obtain ic where "(ic, p, q) \<in> set ps1" by fastforce
    show "crit_pair_cbelow_on d m (fst ` B) (fst p) (fst q)"
    proof (cases "ic")
      case True
      hence "ic = True" by simp
      from B_sup have B_sup': "fst ` (set gs \<union> set bs \<union> set hs) \<subseteq> fst ` B" by (rule image_mono)
      note assms(2) dg
      moreover from B_sup' B_sub have "fst ` (set gs \<union> set bs \<union> set hs) \<subseteq> dgrad_p_set d m"
        by (rule subset_trans)
      moreover note uid gb p_in q_in \<open>fst p \<noteq> 0\<close> \<open>fst q \<noteq> 0\<close>
      moreover from \<open>(ic, p, q) \<in> set ps1\<close> obtain q_in_bs
        where "(True, q_in_bs, p, q) \<in> set (apply_icrit icrit data gs bs hs (np gs bs hs data))"
        unfolding ps1_def \<open>ic = True\<close> by (rule apply_ncrit_subset)
      ultimately have "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs \<union> set hs)) (fst p) (fst q)"
        by (rule fst_apply_icrit)
      thus ?thesis using B_sup' by (rule crit_pair_cbelow_mono)
    next
      case False
      with \<open>(ic, p, q) \<in> set ps1\<close> have "(False, p, q) \<in> set ps1" by simp
      with assms(5) ps1_def have "(p, q) \<in> set (add_pairs gs bs ps hs data)"
        by (simp add: set_add_pairs_iff)
      hence "(p, q) \<in>\<^sub>p set (add_pairs gs bs ps hs data)" by (simp add: in_pair_iff)
      moreover from pq_in have "(p, q) \<in>\<^sub>p set hs \<times> (set gs \<union> set bs \<union> set hs)"
        by (simp add: in_pair_iff)
      ultimately show ?thesis using \<open>fst p \<noteq> 0\<close> \<open>fst q \<noteq> 0\<close> by (rule *)
    qed
  next
    show "(h, g) \<notin> set (apply_ocrit ocrit data hs ps1 ps)"
    proof
      assume "(h, g) \<in> set (apply_ocrit ocrit data hs ps1 ps)"
      hence "(h, g) \<in> set (add_pairs gs bs ps hs data)"
        by (simp add: add_pairs_def assms(5) Let_def ps1_def)
      with \<open>(h, g) \<notin> set (add_pairs gs bs ps hs data)\<close> show False ..
    qed
  qed
qed

end

abbreviation "add_pairs_canon \<equiv>
  add_pairs (new_pairs_sorted canon_pair_order) component_crit chain_ncrit chain_ocrit canon_pair_comb"

lemma ap_spec_add_pairs_canon: "ap_spec add_pairs_canon"
  using np_spec_new_pairs_sorted icrit_spec_component_crit ncrit_spec_chain_ncrit
    ocrit_spec_chain_ocrit set_merge_wrt
  by (rule ap_spec_add_pairs)

subsection \<open>Suitable Instances of the @{emph \<open>completion\<close>} Parameter\<close>

definition rcp_spec :: "('t, 'b::field, 'c, 'd) complT \<Rightarrow> bool"
  where "rcp_spec rcp \<longleftrightarrow>
            (\<forall>gs bs ps sps data.
              0 \<notin> fst ` set (fst (rcp gs bs ps sps data)) \<and>
              (\<forall>h b. h \<in> set (fst (rcp gs bs ps sps data)) \<longrightarrow> b \<in> set gs \<union> set bs \<longrightarrow> fst b \<noteq> 0 \<longrightarrow>
                     \<not> lt (fst b) adds\<^sub>t lt (fst h)) \<and>
              (\<forall>d. dickson_grading d \<longrightarrow>
                     dgrad_p_set_le d (fst ` set (fst (rcp gs bs ps sps data))) (args_to_set (gs, bs, sps))) \<and>
              component_of_term ` Keys (fst ` (set (fst (rcp gs bs ps sps data)))) \<subseteq>
                component_of_term ` Keys (args_to_set (gs, bs, sps)) \<and>
              (is_Groebner_basis (fst ` set gs) \<longrightarrow> unique_idx (gs @ bs) data \<longrightarrow>
                (fst ` set (fst (rcp gs bs ps sps data)) \<subseteq> pmdl (args_to_set (gs, bs, sps)) \<and>
                (\<forall>(p, q)\<in>set sps.  set sps \<subseteq> set bs \<times> (set gs \<union> set bs) \<longrightarrow>
                  (red (fst ` (set gs \<union> set bs) \<union> fst ` set (fst (rcp gs bs ps sps data))))\<^sup>*\<^sup>* (spoly (fst p) (fst q)) 0))))"

text \<open>Informally, \<open>rcp_spec rcp\<close> expresses that, for suitable \<open>gs\<close>, \<open>bs\<close> and \<open>sps\<close>, the value of
  \<open>rcp gs bs ps sps\<close>
  \begin{itemize}
    \item is a list consisting exclusively of non-zero polynomials contained in the module generated
      by \<open>set bs \<union> set gs\<close>, whose leading terms are not divisible by the leading
      term of any non-zero @{prop "b \<in> set bs"}, and
    \item contains sufficiently many new polynomials such that all S-polynomials originating from
      \<open>sps\<close> can be reduced to \<open>0\<close> modulo the enlarged list of polynomials.
  \end{itemize}\<close>

lemma rcp_specI:
  assumes "\<And>gs bs ps sps data. 0 \<notin> fst ` set (fst (rcp gs bs ps sps data))"
  assumes "\<And>gs bs ps sps h b data. h \<in> set (fst (rcp gs bs ps sps data)) \<Longrightarrow> b \<in> set gs \<union> set bs \<Longrightarrow> fst b \<noteq> 0 \<Longrightarrow>
                          \<not> lt (fst b) adds\<^sub>t lt (fst h)"
  assumes "\<And>gs bs ps sps d data. dickson_grading d \<Longrightarrow>
                         dgrad_p_set_le d (fst ` set (fst (rcp gs bs ps sps data))) (args_to_set (gs, bs, sps))"
  assumes "\<And>gs bs ps sps data. component_of_term ` Keys (fst ` (set (fst (rcp gs bs ps sps data)))) \<subseteq>
                            component_of_term ` Keys (args_to_set (gs, bs, sps))"
  assumes "\<And>gs bs ps sps data. is_Groebner_basis (fst ` set gs) \<Longrightarrow> unique_idx (gs @ bs) data \<Longrightarrow>
                (fst ` set (fst (rcp gs bs ps sps data)) \<subseteq> pmdl (args_to_set (gs, bs, sps)) \<and>
                (\<forall>(p, q)\<in>set sps.  set sps \<subseteq> set bs \<times> (set gs \<union> set bs) \<longrightarrow>
                  (red (fst ` (set gs \<union> set bs) \<union> fst ` set (fst (rcp gs bs ps sps data))))\<^sup>*\<^sup>* (spoly (fst p) (fst q)) 0))"
  shows "rcp_spec rcp"
  unfolding rcp_spec_def using assms by auto

lemma rcp_specD1:
  assumes "rcp_spec rcp"
  shows "0 \<notin> fst ` set (fst (rcp gs bs ps sps data))"
  using assms unfolding rcp_spec_def by (elim allE conjE)

lemma rcp_specD2:
  assumes "rcp_spec rcp"
    and "h \<in> set (fst (rcp gs bs ps sps data))" and "b \<in> set gs \<union> set bs" and "fst b \<noteq> 0"
  shows "\<not> lt (fst b) adds\<^sub>t lt (fst h)"
  using assms unfolding rcp_spec_def by (elim allE conjE, blast)

lemma rcp_specD3:
  assumes "rcp_spec rcp" and "dickson_grading d"
  shows "dgrad_p_set_le d (fst ` set (fst (rcp gs bs ps sps data))) (args_to_set (gs, bs, sps))"
  using assms unfolding rcp_spec_def by (elim allE conjE, blast)

lemma rcp_specD4:
  assumes "rcp_spec rcp"
  shows "component_of_term ` Keys (fst ` (set (fst (rcp gs bs ps sps data)))) \<subseteq>
          component_of_term ` Keys (args_to_set (gs, bs, sps))"
  using assms unfolding rcp_spec_def by (elim allE conjE)

lemma rcp_specD5:
  assumes "rcp_spec rcp" and "is_Groebner_basis (fst ` set gs)" and "unique_idx (gs @ bs) data"
  shows "fst ` set (fst (rcp gs bs ps sps data)) \<subseteq> pmdl (args_to_set (gs, bs, sps))"
  using assms unfolding rcp_spec_def by blast

lemma rcp_specD6:
  assumes "rcp_spec rcp" and "is_Groebner_basis (fst ` set gs)" and "unique_idx (gs @ bs) data"
    and "set sps \<subseteq> set bs \<times> (set gs \<union> set bs)"
    and "(p, q) \<in> set sps"
  shows "(red (fst ` (set gs \<union> set bs) \<union> fst ` set (fst (rcp gs bs ps sps data))))\<^sup>*\<^sup>* (spoly (fst p) (fst q)) 0"
  using assms unfolding rcp_spec_def by blast

lemma compl_struct_rcp:
  assumes "rcp_spec rcp"
  shows "compl_struct rcp"
proof (rule compl_structI)
  fix d::"'a \<Rightarrow> nat" and gs bs ps and sps::"('t, 'b, 'c) pdata_pair list" and data::"nat \<times> 'd"
  assume "dickson_grading d" and "set sps \<subseteq> set ps"
  from assms this(1) have "dgrad_p_set_le d (fst ` set (fst (rcp gs bs (ps -- sps) sps data)))
                                    (args_to_set (gs, bs, sps))"
    by (rule rcp_specD3)
  also have "dgrad_p_set_le d ... (args_to_set (gs, bs, ps))"
    by (rule dgrad_p_set_le_subset, rule args_to_set_subset3, fact \<open>set sps \<subseteq> set ps\<close>)
  finally show "dgrad_p_set_le d (fst ` set (fst (rcp gs bs (ps -- sps) sps data)))
                                    (args_to_set (gs, bs, ps))" .
next
  fix gs bs ps and sps::"('t, 'b, 'c) pdata_pair list" and data::"nat \<times> 'd"
  from assms show "0 \<notin> fst ` set (fst (rcp gs bs (ps -- sps) sps data))"
    by (rule rcp_specD1)
next
  fix gs bs ps sps h b data
  assume "h \<in> set (fst (rcp gs bs (ps -- sps) sps data))"
    and "b \<in> set gs \<union> set bs" and "fst b \<noteq> 0"
  with assms show "\<not> lt (fst b) adds\<^sub>t lt (fst h)" by (rule rcp_specD2)
next
  fix gs bs ps and sps::"('t, 'b, 'c) pdata_pair list" and data::"nat \<times> 'd"
  assume "set sps \<subseteq> set ps"
  from assms
  have "component_of_term ` Keys (fst ` set (fst (rcp gs bs (ps -- sps) sps data))) \<subseteq>
        component_of_term ` Keys (args_to_set (gs, bs, sps))"
    by (rule rcp_specD4)
  also have "... \<subseteq> component_of_term ` Keys (args_to_set (gs, bs, ps))"
    by (rule image_mono, rule Keys_mono, rule args_to_set_subset3, fact \<open>set sps \<subseteq> set ps\<close>)
  finally show "component_of_term ` Keys (fst ` set (fst (rcp gs bs (ps -- sps) sps data))) \<subseteq>
                component_of_term ` Keys (args_to_set (gs, bs, ps))" .
qed

lemma compl_pmdl_rcp:
  assumes "rcp_spec rcp"
  shows "compl_pmdl rcp"
proof (rule compl_pmdlI)
  fix gs bs :: "('t, 'b, 'c) pdata list" and ps sps :: "('t, 'b, 'c) pdata_pair list" and data::"nat \<times> 'd"
  assume gb: "is_Groebner_basis (fst ` set gs)" and "set sps \<subseteq> set ps"
    and un: "unique_idx (gs @ bs) data"
  let ?res = "fst (rcp gs bs (ps -- sps) sps data)"
  from assms gb un have "fst ` set ?res \<subseteq> pmdl (args_to_set (gs, bs, sps))"
    by (rule rcp_specD5)
  also have "... \<subseteq> pmdl (args_to_set (gs, bs, ps))"
    by (rule pmdl.span_mono, rule args_to_set_subset3, fact \<open>set sps \<subseteq> set ps\<close>)
  finally show "fst ` set ?res \<subseteq> pmdl (args_to_set (gs, bs, ps))" .
qed

lemma compl_conn_rcp:
  assumes "rcp_spec rcp"
  shows "compl_conn rcp"
proof (rule compl_connI)
  fix d::"'a \<Rightarrow> nat" and m gs bs ps sps p and q::"('t, 'b, 'c) pdata" and data::"nat \<times> 'd"
  assume dg: "dickson_grading d" and gs_sub: "fst ` set gs \<subseteq> dgrad_p_set d m"
    and gb: "is_Groebner_basis (fst ` set gs)" and bs_sub: "fst ` set bs \<subseteq> dgrad_p_set d m"
    and ps_sub: "set ps \<subseteq> set bs \<times> (set gs \<union> set bs)" and "set sps \<subseteq> set ps"
    and uid: "unique_idx (gs @ bs) data"
    and "(p, q) \<in> set sps" and "fst p \<noteq> 0" and "fst q \<noteq> 0"

  from \<open>set sps \<subseteq> set ps\<close> ps_sub have sps_sub: "set sps \<subseteq> set bs \<times> (set gs \<union> set bs)"
    by (rule subset_trans)

  let ?res = "fst (rcp gs bs (ps -- sps) sps data)"
  have "fst ` set ?res \<subseteq> dgrad_p_set d m"
  proof (rule dgrad_p_set_le_dgrad_p_set, rule rcp_specD3, fact+)
    show "args_to_set (gs, bs, sps) \<subseteq> dgrad_p_set d m"
      by (simp add: args_to_set_subset_Times[OF sps_sub], rule, fact+)
  qed
  moreover have gs_bs_sub: "fst ` (set gs \<union> set bs) \<subseteq> dgrad_p_set d m" by (simp add: image_Un, rule, fact+)
  ultimately have res_sub: "fst ` (set gs \<union> set bs) \<union> fst ` set ?res \<subseteq> dgrad_p_set d m" by simp

  from \<open>(p, q) \<in> set sps\<close> \<open>set sps \<subseteq> set ps\<close> ps_sub
  have "fst p \<in> fst ` set bs" and "fst q \<in> fst ` (set gs \<union> set bs)" by auto
  with \<open>fst ` set bs \<subseteq> dgrad_p_set d m\<close> gs_bs_sub
  have "fst p \<in> dgrad_p_set d m" and "fst q \<in> dgrad_p_set d m" by auto

  with dg res_sub show "crit_pair_cbelow_on d m (fst ` (set gs \<union> set bs) \<union> fst ` set ?res) (fst p) (fst q)"
    using \<open>fst p \<noteq> 0\<close> \<open>fst q \<noteq> 0\<close>
  proof (rule spoly_red_zero_imp_crit_pair_cbelow_on)
    from assms gb uid sps_sub \<open>(p, q) \<in> set sps\<close>
    show "(red (fst ` (set gs \<union> set bs) \<union> fst ` set (fst (rcp gs bs (ps -- sps) sps data))))\<^sup>*\<^sup>*
            (spoly (fst p) (fst q)) 0"
      by (rule rcp_specD6)
  qed
qed

end (* gd_term *)

subsection \<open>Suitable Instances of the @{emph \<open>add-basis\<close>} Parameter\<close>

definition add_basis_naive :: "('a, 'b, 'c, 'd) abT"
  where "add_basis_naive gs bs ns data = bs @ ns"

lemma ab_spec_add_basis_naive: "ab_spec add_basis_naive"
  by (rule ab_specI, simp_all add: add_basis_naive_def)

definition add_basis_sorted :: "(nat \<times> 'd \<Rightarrow> ('a, 'b, 'c) pdata \<Rightarrow> ('a, 'b, 'c) pdata \<Rightarrow> bool) \<Rightarrow> ('a, 'b, 'c, 'd) abT"
  where "add_basis_sorted rel gs bs ns data = merge_wrt (rel data) bs ns"

lemma ab_spec_add_basis_sorted: "ab_spec (add_basis_sorted rel)"
  by (rule ab_specI, simp_all add: add_basis_sorted_def set_merge_wrt)

definition card_keys :: "('a \<Rightarrow>\<^sub>0 'b::zero) \<Rightarrow> nat"
  where "card_keys = card \<circ> keys"

definition (in ordered_term) canon_basis_order :: "'d \<Rightarrow> ('t, 'b::zero, 'c) pdata \<Rightarrow> ('t, 'b, 'c) pdata \<Rightarrow> bool"
  where "canon_basis_order data p q \<longleftrightarrow>
          (let cp = card_keys (fst p); cq = card_keys (fst q) in
            cp < cq \<or> (cp = cq \<and> lt (fst p) \<prec>\<^sub>t lt (fst q)))"

abbreviation (in ordered_term) "add_basis_canon \<equiv> add_basis_sorted canon_basis_order"

subsection \<open>Special Case: Scalar Polynomials\<close>

context gd_powerprod
begin

lemma remdups_map_component_of_term_punit:
  "remdups (map (\<lambda>_. ()) (punit.Keys_to_list (map fst bs))) =
    (if (\<forall>b\<in>set bs. fst b = 0) then [] else [()])"
proof (split if_split, intro conjI impI)
  assume "\<forall>b\<in>set bs. fst b = 0"
  hence "fst ` set bs \<subseteq> {0}" by blast
  hence "Keys (fst ` set bs) = {}" by (metis Keys_empty Keys_zero subset_singleton_iff)
  hence "punit.Keys_to_list (map fst bs) = []"
    by (simp add: set_empty[symmetric] punit.set_Keys_to_list del: set_empty)
  thus "remdups (map (\<lambda>_. ()) (punit.Keys_to_list (map fst bs))) = []" by simp
next
  assume "\<not> (\<forall>b\<in>set bs. fst b = 0)"
  hence "\<exists>b\<in>set bs. fst b \<noteq> 0" by simp
  then obtain b where "b \<in> set bs" and "fst b \<noteq> 0" ..
  hence "Keys (fst ` set bs) \<noteq> {}" by (meson Keys_not_empty \<open>fst b \<noteq> 0\<close> imageI)
  hence "set (punit.Keys_to_list (map fst bs)) \<noteq> {}" by (simp add: punit.set_Keys_to_list)
  hence "punit.Keys_to_list (map fst bs) \<noteq> []" by simp
  thus "remdups (map (\<lambda>_. ()) (punit.Keys_to_list (map fst bs))) = [()]"
    by (metis (full_types) old.unit.exhaust sorted.cases Nil_is_map_conv \<open>punit.Keys_to_list (map fst bs) \<noteq> []\<close> distinct_length_2_or_more distinct_remdups remdups_eq_nil_right_iff) 
    (*SLOW: 13s*)
qed

lemma count_const_lt_components_punit [code]:
  "punit.count_const_lt_components hs =
    (if (\<exists>h\<in>set hs. punit.const_lt_component (fst h) = Some ()) then 1 else 0)"
proof (simp add: punit.count_const_lt_components_def cong del: image_cong_simp,
  simp add: card_set [symmetric] cong del: image_cong_simp, rule)
  assume "\<exists>h\<in>set hs. punit.const_lt_component (fst h) = Some ()"
  then obtain h where "h \<in> set hs" and "punit.const_lt_component (fst h) = Some ()" ..
  from this(2) have "(punit.const_lt_component \<circ> fst) h = Some ()" by simp
  with \<open>h \<in> set hs\<close> have "Some () \<in> (punit.const_lt_component \<circ> fst) ` set hs"
    by (metis rev_image_eqI)
  hence "{x. x = Some () \<and> x \<in> (punit.const_lt_component \<circ> fst) ` set hs} = {Some ()}" by auto
  thus "card {x. x = Some () \<and> x \<in> (punit.const_lt_component \<circ> fst) ` set hs} = Suc 0" by simp
qed

lemma count_rem_components_punit [code]:
  "punit.count_rem_components bs =
    (if (\<forall>b\<in>set bs. fst b = 0) then 0
    else
      if (\<exists>b\<in>set bs. fst b \<noteq> 0 \<and> punit.const_lt_component (fst b) = Some ()) then 0 else 1)"
proof (cases "\<forall>b\<in>set bs. fst b = 0")
  case True
  thus ?thesis by (simp add: punit.count_rem_components_def remdups_map_component_of_term_punit)
next
  case False
  have eq: "(\<exists>b\<in>set [b\<leftarrow>bs . fst b \<noteq> 0]. punit.const_lt_component (fst b) = Some ()) =
            (\<exists>b\<in>set bs. fst b \<noteq> 0 \<and> punit.const_lt_component (fst b) = Some ())"
    by (metis (mono_tags, lifting) filter_set member_filter)
  show ?thesis
    by (simp only: False punit.count_rem_components_def eq if_False
        remdups_map_component_of_term_punit count_const_lt_components_punit punit_component_of_term, simp)
qed

lemma full_gb_punit [code]:
  "punit.full_gb bs = (if (\<forall>b\<in>set bs. fst b = 0) then [] else [(1, 0, default)])"
  by (simp add: punit.full_gb_def remdups_map_component_of_term_punit)

abbreviation "add_pairs_punit_canon \<equiv>
  punit.add_pairs (punit.new_pairs_sorted punit.canon_pair_order) punit.product_crit punit.chain_ncrit
                  punit.chain_ocrit punit.canon_pair_comb"

lemma ap_spec_add_pairs_punit_canon: "punit.ap_spec add_pairs_punit_canon"
  using punit.np_spec_new_pairs_sorted punit.icrit_spec_product_crit punit.ncrit_spec_chain_ncrit
    punit.ocrit_spec_chain_ocrit set_merge_wrt
  by (rule punit.ap_spec_add_pairs)

end (* gd_powerprod *)

end (* theory *)
