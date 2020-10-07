(*  
  Title:    Preference_Profiles.thy
  Author:   Manuel Eberl, TU München

  Definition of (weak) preference profiles and functions for building
  and manipulating them
*)

section \<open>Preference Profiles\<close>

theory Preference_Profiles
imports
  Main 
  Order_Predicates 
  "HOL-Library.Multiset"
  "HOL-Library.Disjoint_Sets"
begin

text \<open>The type of preference profiles\<close>
type_synonym ('agent, 'alt) pref_profile = "'agent \<Rightarrow> 'alt relation"

locale preorder_family = 
  fixes dom :: "'a set" and carrier :: "'b set" and R :: "'a \<Rightarrow> 'b relation"
  assumes nonempty_dom: "dom \<noteq> {}"
  assumes in_dom [simp]: "i \<in> dom \<Longrightarrow> preorder_on carrier (R i)"
  assumes not_in_dom [simp]: "i \<notin> dom \<Longrightarrow> \<not>R i x y"
begin

lemma not_in_dom': "i \<notin> dom \<Longrightarrow> R i = (\<lambda>_ _. False)"
  by (simp add: fun_eq_iff)

end


locale pref_profile_wf =
  fixes agents :: "'agent set" and alts :: "'alt set" and R :: "('agent, 'alt) pref_profile"
  assumes nonempty_agents [simp]: "agents \<noteq> {}" and nonempty_alts [simp]: "alts \<noteq> {}"
  assumes prefs_wf [simp]: "i \<in> agents \<Longrightarrow> finite_total_preorder_on alts (R i)"
  assumes prefs_undefined [simp]: "i \<notin> agents \<Longrightarrow> \<not>R i x y"
begin

lemma finite_alts [simp]: "finite alts"
proof -
  from nonempty_agents obtain i where "i \<in> agents" by blast
  then interpret finite_total_preorder_on alts "R i" by simp
  show ?thesis by (rule finite_carrier)
qed

lemma prefs_wf' [simp]:
  "i \<in> agents \<Longrightarrow> total_preorder_on alts (R i)" "i \<in> agents \<Longrightarrow> preorder_on alts (R i)"
  using prefs_wf[of i]
  by (simp_all add: finite_total_preorder_on_def total_preorder_on_def del: prefs_wf)

lemma not_outside: 
  assumes "x \<preceq>[R i] y"
  shows   "i \<in> agents" "x \<in> alts" "y \<in> alts"
proof -
  from assms show "i \<in> agents" by (cases "i \<in> agents") auto
  then interpret preorder_on alts "R i" by simp
  from assms show "x \<in> alts" "y \<in> alts" by (simp_all add: not_outside)
qed

sublocale preorder_family agents alts R
  by (intro preorder_family.intro) simp_all

lemmas prefs_undefined' = not_in_dom'

lemma wf_update:
  assumes "i \<in> agents" "total_preorder_on alts Ri'"
  shows   "pref_profile_wf agents alts (R(i := Ri'))"
proof -
  interpret total_preorder_on alts Ri' by fact
  from finite_alts have "finite_total_preorder_on alts Ri'" by unfold_locales
  with assms show ?thesis
    by (auto intro!: pref_profile_wf.intro split: if_splits)
qed

lemma wf_permute_agents:
  assumes "\<sigma> permutes agents"
  shows   "pref_profile_wf agents alts (R \<circ> \<sigma>)"
  unfolding o_def using permutes_in_image[OF assms(1)]
  by (intro pref_profile_wf.intro prefs_wf) simp_all

lemma (in -) pref_profile_eqI:
  assumes "pref_profile_wf agents alts R1" "pref_profile_wf agents alts R2"
  assumes "\<And>x. x \<in> agents \<Longrightarrow> R1 x = R2 x"
  shows   "R1 = R2"
proof
  interpret R1: pref_profile_wf agents alts R1 by fact
  interpret R2: pref_profile_wf agents alts R2 by fact
  fix x show "R1 x = R2 x"
    by (cases "x \<in> agents"; intro ext) (simp_all add: assms(3)) 
qed

end


text \<open>
  Permutes a preference profile w.r.t. alternatives in the way described in the paper.
  This is needed for the definition of neutrality.
\<close>
definition permute_profile where
  "permute_profile \<sigma> R = (\<lambda>i x y. R i (inv \<sigma> x) (inv \<sigma> y))"
  
lemma permute_profile_map_relation:
  "permute_profile \<sigma> R = (\<lambda>i. map_relation (inv \<sigma>) (R i))"
  by (simp add: permute_profile_def map_relation_def)

lemma permute_profile_compose [simp]:
  "permute_profile \<sigma> (R \<circ> \<pi>) = permute_profile \<sigma> R \<circ> \<pi>"
  by (auto simp: fun_eq_iff permute_profile_def o_def)

lemma permute_profile_id [simp]: "permute_profile id R = R"
  by (simp add: permute_profile_def)

lemma permute_profile_o:
  assumes "bij f" "bij g"
  shows   "permute_profile f (permute_profile g R) = permute_profile (f \<circ> g) R"
  using assms by (simp add: permute_profile_def o_inv_distrib)

lemma (in pref_profile_wf) wf_permute_alts:
  assumes "\<sigma> permutes alts"
  shows   "pref_profile_wf agents alts (permute_profile \<sigma> R)"
proof (rule pref_profile_wf.intro)
  fix i assume "i \<in> agents"
  with assms interpret R: finite_total_preorder_on alts "R i" by simp
    
  from assms have [simp]: "inv \<sigma> x \<in> alts \<longleftrightarrow> x \<in> alts" for x
    by (simp add: permutes_in_image permutes_inv)

  show "finite_total_preorder_on alts (permute_profile \<sigma> R i)"
  proof
    fix x y assume "permute_profile \<sigma> R i x y"
    thus "x \<in> alts" "y \<in> alts"
      using R.not_outside[of "inv \<sigma> x" "inv \<sigma> y"]
      by (auto simp: permute_profile_def)
  next
    fix x y z assume "permute_profile \<sigma> R i x y" "permute_profile \<sigma> R i y z"
    thus "permute_profile \<sigma> R i x z"
      using R.trans[of "inv \<sigma> x" "inv \<sigma> y" "inv \<sigma> z"] 
      by (simp_all add: permute_profile_def)
  qed (insert R.total R.refl R.finite_carrier, simp_all add: permute_profile_def)
qed (insert assms, simp_all add: permute_profile_def pref_profile_wf_def)


text \<open>
  This shows that the above definition is equivalent to that in the paper.  
\<close>
lemma permute_profile_iff [simp]:
  fixes R :: "('agent, 'alt) pref_profile"
  assumes "\<sigma> permutes alts" "x \<in> alts" "y \<in> alts"
  defines "R' \<equiv> permute_profile \<sigma> R"
  shows   "\<sigma> x \<preceq>[R' i] \<sigma> y \<longleftrightarrow> x \<preceq>[R i] y"
  using assms by (simp add: permute_profile_def permutes_inverses)


subsection \<open>Pareto dominance\<close>

definition Pareto :: "('agent \<Rightarrow> 'alt relation) \<Rightarrow> 'alt relation" where
  "x \<preceq>[Pareto(R)] y \<longleftrightarrow> (\<exists>j. x \<preceq>[R j] x) \<and> (\<forall>i. x \<preceq>[R i] x \<longrightarrow> x \<preceq>[R i] y)"

text \<open>
  A Pareto loser is an alternative that is Pareto-dominated by some other alternative.
\<close>
definition pareto_losers :: "('agent, 'alt) pref_profile \<Rightarrow> 'alt set" where
  "pareto_losers R = {x. \<exists>y. y \<succ>[Pareto(R)] x}"

lemma pareto_losersI [intro?, simp]: "y \<succ>[Pareto(R)] x \<Longrightarrow> x \<in> pareto_losers R"
  by (auto simp: pareto_losers_def)

context preorder_family
begin

lemma Pareto_iff:
  "x \<preceq>[Pareto(R)] y \<longleftrightarrow> (\<forall>i\<in>dom. x \<preceq>[R i] y)"
proof
  assume A: "x \<preceq>[Pareto(R)] y"
  then obtain j where j: "x \<preceq>[R j] x" by (auto simp: Pareto_def)
  hence j': "j \<in> dom" by (cases "j \<in> dom") auto
  then interpret preorder_on carrier "R j" by simp
  from j have "x \<in> carrier" by (auto simp: carrier_eq)
  with A preorder_on.refl[OF in_dom]
    show "(\<forall>i\<in>dom. x \<preceq>[R i] y)" by (auto simp: Pareto_def)
next
  assume A: "(\<forall>i\<in>dom. x \<preceq>[R i] y)"
  from nonempty_dom obtain j where j: "j \<in> dom" by blast
  then interpret preorder_on carrier "R j" by simp 
  from j A have "x \<preceq>[R j] y" by simp
  hence "x \<preceq>[R j] x" using not_outside refl by blast
  with A show "x \<preceq>[Pareto(R)] y" by (auto simp: Pareto_def)
qed

lemma Pareto_strict_iff: 
  "x \<prec>[Pareto(R)] y \<longleftrightarrow> (\<forall>i\<in>dom. x \<preceq>[R i] y) \<and> (\<exists>i\<in>dom. x \<prec>[R i] y)"
  by (auto simp: strongly_preferred_def Pareto_iff nonempty_dom)

lemma Pareto_strictI:
  assumes "\<And>i. i \<in> dom \<Longrightarrow> x \<preceq>[R i] y" "i \<in> dom" "x \<prec>[R i] y"
  shows   "x \<prec>[Pareto(R)] y"
  using assms by (auto simp: Pareto_strict_iff)

lemma Pareto_strictI':
  assumes "\<And>i. i \<in> dom \<Longrightarrow> x \<preceq>[R i] y" "i \<in> dom" "\<not>x \<succeq>[R i] y"
  shows   "x \<prec>[Pareto(R)] y"
proof -
  from assms interpret preorder_on carrier "R i" by simp
  from assms have "x \<prec>[R i] y" by (simp add: strongly_preferred_def)
  with assms show ?thesis by (auto simp: Pareto_strict_iff )
qed


sublocale Pareto: preorder_on carrier "Pareto(R)"
proof -
  have "preorder_on carrier (R i)" if "i \<in> dom" for i using that by simp_all
  note A = preorder_on.not_outside[OF this(1)] preorder_on.refl[OF this(1)]
           preorder_on.trans[OF this(1)]
  from nonempty_dom obtain i where i: "i \<in> dom" by blast
  show "preorder_on carrier (Pareto R)"
  proof
    fix x y assume "x \<preceq>[Pareto(R)] y"
    with A(1,2)[OF i] i show "x \<in> carrier" "y \<in> carrier" by (auto simp: Pareto_iff)
  qed (auto simp: Pareto_iff intro: A)
qed

lemma pareto_loser_in_alts: 
  assumes "x \<in> pareto_losers R"
  shows   "x \<in> carrier"
proof -
  from assms obtain y i where "i \<in> dom" "x \<prec>[R i] y"
    by (auto simp: pareto_losers_def Pareto_strict_iff)
  then interpret preorder_on carrier "R i" by simp
  from \<open>x \<prec>[R i] y\<close> have "x \<preceq>[R i] y" by (simp add: strongly_preferred_def)
  thus "x \<in> carrier" using not_outside by simp
qed

lemma pareto_losersE:
  assumes "x \<in> pareto_losers R"
  obtains y where "y \<in> carrier" "y \<succ>[Pareto(R)] x"
proof -
  from assms obtain y where y: "y \<succ>[Pareto(R)] x" unfolding pareto_losers_def by blast
  with Pareto.not_outside[of x y] have "y \<in> carrier" 
    by (simp add: strongly_preferred_def)
  with y show ?thesis using that by blast
qed

end


subsection \<open>Preferred alternatives\<close>

context pref_profile_wf
begin

lemma preferred_alts_subset_alts: "preferred_alts (R i) x \<subseteq> alts" (is ?A)
  and finite_preferred_alts [simp,intro!]: "finite (preferred_alts (R i) x)" (is ?B)
proof -
  have "?A \<and> ?B"
  proof (cases "i \<in> agents")
    assume "i \<in> agents"
    then interpret total_preorder_on alts "R i" by simp
    have "preferred_alts (R i) x \<subseteq> alts" using not_outside
      by (auto simp: preferred_alts_def)
    thus ?thesis by (auto dest: finite_subset)
  qed (auto simp: preferred_alts_def)
  thus ?A ?B by blast+
qed

lemma preferred_alts_altdef: 
  "i \<in> agents \<Longrightarrow> preferred_alts (R i) x = {y\<in>alts. y \<succeq>[R i] x}"
  by (simp add: preorder_on.preferred_alts_altdef)  

end


subsection \<open>Favourite alternatives\<close>

definition favorites :: "('agent, 'alt) pref_profile \<Rightarrow> 'agent \<Rightarrow> 'alt set" where
  "favorites R i = Max_wrt (R i)"

definition favorite :: "('agent, 'alt) pref_profile \<Rightarrow> 'agent \<Rightarrow> 'alt" where
  "favorite R i = the_elem (favorites R i)"

definition has_unique_favorites :: "('agent, 'alt) pref_profile \<Rightarrow> bool" where
  "has_unique_favorites R \<longleftrightarrow> (\<forall>i. favorites R i = {} \<or> is_singleton (favorites R i))"

context pref_profile_wf
begin

lemma favorites_altdef:
  "favorites R i = Max_wrt_among (R i) alts"
proof (cases "i \<in> agents")
  assume "i \<in> agents"
  then interpret total_preorder_on alts "R i" by simp
  show ?thesis 
    by (simp add: favorites_def Max_wrt_total_preorder Max_wrt_among_total_preorder)
qed (simp_all add: favorites_def Max_wrt_def Max_wrt_among_def pref_profile_wf_def)

lemma favorites_no_agent [simp]: "i \<notin> agents \<Longrightarrow> favorites R i = {}"
  by (auto simp: favorites_def Max_wrt_def Max_wrt_among_def)

lemma favorites_altdef':
  "favorites R i = {x\<in>alts. \<forall>y\<in>alts. x \<succeq>[R i] y}"
proof (cases "i \<in> agents")
  assume "i \<in> agents"
  then interpret finite_total_preorder_on alts "R i" by simp
  show ?thesis using Max_wrt_among_nonempty[of alts] Max_wrt_among_subset[of alts]
    by (auto simp: favorites_altdef Max_wrt_among_total_preorder)
qed simp_all

lemma favorites_subset_alts: "favorites R i \<subseteq> alts"
  by (auto simp: favorites_altdef')

lemma finite_favorites [simp, intro]: "finite (favorites R i)"
  using favorites_subset_alts finite_alts  by (rule finite_subset)

lemma favorites_nonempty: "i \<in> agents \<Longrightarrow> favorites R i \<noteq> {}"
proof -
  assume "i \<in> agents"
  then interpret finite_total_preorder_on alts "R i" by simp
  show ?thesis unfolding favorites_def by (intro Max_wrt_nonempty) simp_all
qed

lemma favorites_permute: 
  assumes i: "i \<in> agents" and perm: "\<sigma> permutes alts"
  shows   "favorites (permute_profile \<sigma> R) i = \<sigma> ` favorites R i"
proof -
  from i interpret finite_total_preorder_on alts "R i" by simp
  from perm show ?thesis
  unfolding favorites_def
    by (subst Max_wrt_map_relation_bij)
       (simp_all add: permute_profile_def map_relation_def permutes_bij)
qed

lemma has_unique_favorites_altdef:
  "has_unique_favorites R \<longleftrightarrow> (\<forall>i\<in>agents. is_singleton (favorites R i))"
proof safe
  fix i assume "has_unique_favorites R" "i \<in> agents"
  thus "is_singleton (favorites R i)" using favorites_nonempty[of i]
    by (auto simp: has_unique_favorites_def)
next
  assume "\<forall>i\<in>agents. is_singleton (favorites R i)"
  hence "is_singleton (favorites R i) \<or> favorites R i = {}" for i
    by (cases "i \<in> agents") (simp add: favorites_nonempty, simp add: favorites_altdef')
  thus "has_unique_favorites R" by (auto simp: has_unique_favorites_def)
qed

end


locale pref_profile_unique_favorites = pref_profile_wf agents alts R
  for agents :: "'agent set" and alts :: "'alt set" and R +
  assumes unique_favorites': "has_unique_favorites R"
begin
  
lemma unique_favorites: "i \<in> agents \<Longrightarrow> favorites R i = {favorite R i}"
  using unique_favorites' 
  by (auto simp: favorite_def has_unique_favorites_altdef is_singleton_the_elem)

lemma favorite_in_alts: "i \<in> agents \<Longrightarrow> favorite R i \<in> alts"
  using favorites_subset_alts[of i] by (simp add: unique_favorites)

end

  

subsection \<open>Anonymous profiles\<close>

type_synonym ('agent, 'alt) apref_profile = "'alt set list multiset"

definition anonymous_profile :: "('agent, 'alt) pref_profile \<Rightarrow> ('agent, 'alt) apref_profile" 
  where anonymous_profile_auxdef:
    "anonymous_profile R = image_mset (weak_ranking \<circ> R) (mset_set {i. R i \<noteq> (\<lambda>_ _. False)})"

lemma (in pref_profile_wf) agents_eq:
  "agents = {i. R i \<noteq> (\<lambda>_ _. False)}"
proof safe
  fix i assume i: "i \<in> agents" and Ri: "R i = (\<lambda>_ _. False)"
  from i interpret preorder_on alts "R i" by simp
  from carrier_eq Ri nonempty_alts show False by simp
next
  fix i assume "R i \<noteq> (\<lambda>_ _. False)"
  thus "i \<in> agents" using prefs_undefined'[of i] by (cases "i \<in> agents") auto
qed

lemma (in pref_profile_wf) anonymous_profile_def:
  "anonymous_profile R = image_mset (weak_ranking \<circ> R) (mset_set agents)"
  by (simp only: agents_eq anonymous_profile_auxdef)

lemma (in pref_profile_wf) anonymous_profile_permute:
  assumes "\<sigma> permutes alts"  "finite agents" 
  shows   "anonymous_profile (permute_profile \<sigma> R) = 
             image_mset (map ((`) \<sigma>)) (anonymous_profile R)"
proof -
  from assms(1) interpret R': pref_profile_wf agents alts "permute_profile \<sigma> R"
    by (rule wf_permute_alts)
  have "anonymous_profile (permute_profile \<sigma> R) = 
          {#weak_ranking (map_relation (inv \<sigma>) (R x)). x \<in># mset_set agents#}"
    unfolding R'.anonymous_profile_def
    by (simp add:  multiset.map_comp permute_profile_map_relation o_def)
  also from assms have "\<dots> = {#map ((`) \<sigma>) (weak_ranking (R x)). x \<in># mset_set agents#}"
    by (intro image_mset_cong)
       (simp add: finite_total_preorder_on.weak_ranking_permute[of alts])
  also have "\<dots> = image_mset (map ((`) \<sigma>)) (anonymous_profile R)"
    by (simp add: anonymous_profile_def multiset.map_comp o_def)
  finally show ?thesis .
qed

lemma (in pref_profile_wf) anonymous_profile_update:
  assumes i:  "i \<in> agents" and fin [simp]: "finite agents" and "total_preorder_on alts Ri'"
  shows   "anonymous_profile (R(i := Ri')) =
             anonymous_profile R - {#weak_ranking (R i)#} + {#weak_ranking Ri'#}"
proof -
  from assms interpret R': pref_profile_wf agents alts "R(i := Ri')"
    by (simp add: finite_total_preorder_on_iff wf_update)
  have "anonymous_profile (R(i := Ri')) = 
          {#weak_ranking (if x = i then Ri' else R x). x \<in># mset_set agents#}"
    by (simp add: R'.anonymous_profile_def o_def)
  also have "\<dots> = {#if x = i then weak_ranking Ri' else weak_ranking (R x). x \<in># mset_set agents#}"
    by (intro image_mset_cong) simp_all
  also have "\<dots> = {#weak_ranking Ri'. x \<in># mset_set {x \<in> agents. x = i}#} +
                    {#weak_ranking (R x). x \<in># mset_set {x \<in> agents. x \<noteq> i}#}"
    by (subst image_mset_If) ((subst filter_mset_mset_set, simp)+, rule refl)
  also from i have "{x \<in> agents. x = i} = {i}" by auto
  also have "{x \<in> agents. x \<noteq> i} = agents - {i}" by auto
  also have "{#weak_ranking Ri'. x \<in># mset_set {i}#} = {#weak_ranking Ri'#}" by simp
  also from i have "mset_set (agents - {i}) = mset_set agents - {#i#}"
    by (simp add: mset_set_Diff)
  also from i 
    have "{#weak_ranking (R x). x \<in># \<dots>#} =
            {#weak_ranking (R x). x \<in># mset_set agents#} - {#weak_ranking (R i)#}"
      by (subst image_mset_Diff) (simp_all add: in_multiset_in_set mset_subset_eq_single)
  also have "{#weak_ranking Ri'#} + \<dots> = 
               anonymous_profile R - {#weak_ranking (R i)#} + {#weak_ranking Ri'#}"
    by (simp add: anonymous_profile_def add_ac o_def)
  finally show ?thesis .
qed


subsection \<open>Preference profiles from lists\<close>

definition prefs_from_table :: "('agent \<times> 'alt set list) list \<Rightarrow> ('agent, 'alt) pref_profile" where
  "prefs_from_table xss = (\<lambda>i. case_option (\<lambda>_ _. False) of_weak_ranking (map_of xss i))"

definition prefs_from_table_wf where
  "prefs_from_table_wf agents alts xss \<longleftrightarrow> agents \<noteq> {} \<and> alts \<noteq> {} \<and> distinct (map fst xss) \<and> 
       set (map fst xss) = agents \<and> (\<forall>xs\<in>set (map snd xss). \<Union>(set xs) = alts \<and> 
       is_finite_weak_ranking xs)"

lemma prefs_from_table_wfI:
  assumes "agents \<noteq> {}" "alts \<noteq> {}" "distinct (map fst xss)"
  assumes "set (map fst xss) = agents"
  assumes "\<And>xs. xs \<in> set (map snd xss) \<Longrightarrow> \<Union>(set xs) = alts"
  assumes "\<And>xs. xs \<in> set (map snd xss) \<Longrightarrow> is_finite_weak_ranking xs"
  shows   "prefs_from_table_wf agents alts xss"
  using assms unfolding prefs_from_table_wf_def by auto

lemma prefs_from_table_wfD:
  assumes "prefs_from_table_wf agents alts xss"
  shows "agents \<noteq> {}" "alts \<noteq> {}" "distinct (map fst xss)"
    and "set (map fst xss) = agents"
    and "\<And>xs. xs \<in> set (map snd xss) \<Longrightarrow> \<Union>(set xs) = alts"
    and "\<And>xs. xs \<in> set (map snd xss) \<Longrightarrow> is_finite_weak_ranking xs"
  using assms unfolding prefs_from_table_wf_def by auto
       
lemma pref_profile_from_tableI: 
  "prefs_from_table_wf agents alts xss \<Longrightarrow> pref_profile_wf agents alts (prefs_from_table xss)"
proof (intro pref_profile_wf.intro)
  assume wf: "prefs_from_table_wf agents alts xss"
  fix i assume i: "i \<in> agents"
  with wf have "i \<in> set (map fst xss)" by (simp add: prefs_from_table_wf_def)
  then obtain xs where xs: "xs \<in> set (map snd xss)" "prefs_from_table xss i = of_weak_ranking xs"
    by (cases "map_of xss i")
       (fastforce dest: map_of_SomeD simp: prefs_from_table_def map_of_eq_None_iff)+
  with wf show "finite_total_preorder_on alts (prefs_from_table xss i)"
    by (auto simp: prefs_from_table_wf_def intro!: finite_total_preorder_of_weak_ranking)
next
  assume wf: "prefs_from_table_wf agents alts xss"
  fix i x y assume i: "i \<notin> agents"
  with wf have "i \<notin> set (map fst xss)" by (simp add: prefs_from_table_wf_def)
  hence "map_of xss i = None" by (simp add: map_of_eq_None_iff)
  thus "\<not>prefs_from_table xss i x y" by (simp add: prefs_from_table_def)
qed (simp_all add: prefs_from_table_wf_def)

lemma prefs_from_table_eqI:
  assumes "distinct (map fst xs)" "distinct (map fst ys)" "set xs = set ys"
  shows   "prefs_from_table xs = prefs_from_table ys"
proof -
  from assms have "map_of xs = map_of ys" by (subst map_of_inject_set) simp_all
  thus ?thesis by (simp add: prefs_from_table_def)
qed

lemma prefs_from_table_undef:
  assumes "prefs_from_table_wf agents alts xss" "i \<notin> agents"
  shows   "prefs_from_table xss i = (\<lambda>_ _. False)"
proof -
  from assms have "i \<notin> fst ` set xss"
    by (simp add: prefs_from_table_wf_def)
  hence "map_of xss i = None" by (simp add: map_of_eq_None_iff)
  thus ?thesis by (simp add: prefs_from_table_def)
qed

lemma prefs_from_table_map_of:
  assumes "prefs_from_table_wf agents alts xss" "i \<in> agents"
  shows   "prefs_from_table xss i = of_weak_ranking (the (map_of xss i))"
  using assms 
  by (auto simp: prefs_from_table_def map_of_eq_None_iff prefs_from_table_wf_def
           split: option.splits)

lemma prefs_from_table_update:
  fixes x xs
  assumes "i \<in> set (map fst xs)"
  defines "xs' \<equiv> map (\<lambda>(j,y). if j = i then (j, x) else (j, y)) xs"
  shows   "(prefs_from_table xs)(i := of_weak_ranking x) =
             prefs_from_table xs'" (is "?lhs = ?rhs")
proof
  have xs': "set (map fst xs') = set (map fst xs)" by (force simp: xs'_def)  
  fix k
  consider "k = i" | "k \<notin> set (map fst xs)" | "k \<noteq> i" "k \<in> set (map fst xs)" by blast
  thus "?lhs k = ?rhs k"
  proof cases 
    assume k: "k = i"
    moreover from k have "y = x" if "(i, y) \<in> set xs'" for y
      using that by (auto simp: xs'_def split: if_splits)
    ultimately show ?thesis using assms(1) k xs'
      by (auto simp add: prefs_from_table_def map_of_eq_None_iff 
               dest!: map_of_SomeD split: option.splits)
  next
    assume k: "k \<notin> set (map fst xs)"
    with assms(1) have k': "k \<noteq> i" by auto
    with k xs' have "map_of xs k = None" "map_of xs' k = None"
      by (simp_all add: map_of_eq_None_iff)
    thus ?thesis by (simp add: prefs_from_table_def k')
  next
    assume k: "k \<noteq> i" "k \<in> set (map fst xs)"
    with k(1) have "map_of xs k = map_of xs' k" unfolding xs'_def
      by (induction xs) fastforce+
    with k show ?thesis by (simp add: prefs_from_table_def)
  qed
qed

lemma prefs_from_table_swap:
  "x \<noteq> y \<Longrightarrow> prefs_from_table ((x,x')#(y,y')#xs) = prefs_from_table ((y,y')#(x,x')#xs)"
  by (intro ext) (auto simp: prefs_from_table_def)

lemma permute_prefs_from_table:
  assumes "\<sigma> permutes fst ` set xs"
  shows   "prefs_from_table xs \<circ> \<sigma> = prefs_from_table (map (\<lambda>(x,y). (inv \<sigma> x, y)) xs)"
proof
  fix i
  have "(prefs_from_table xs \<circ> \<sigma>) i = 
          (case map_of xs (\<sigma> i) of
             None \<Rightarrow> \<lambda>_ _. False
           | Some x \<Rightarrow> of_weak_ranking x)"
    by (simp add: prefs_from_table_def o_def)
  also have "map_of xs (\<sigma> i) = map_of (map (\<lambda>(x,y). (inv \<sigma> x, y)) xs) i"
    using map_of_permute[OF assms] by (simp add: o_def fun_eq_iff)
  finally show "(prefs_from_table xs \<circ> \<sigma>) i = prefs_from_table (map (\<lambda>(x,y). (inv \<sigma> x, y)) xs) i"
    by (simp only: prefs_from_table_def)
qed

lemma permute_profile_from_table:
  assumes wf: "prefs_from_table_wf agents alts xss"
  assumes perm: "\<sigma> permutes alts"
  shows   "permute_profile \<sigma> (prefs_from_table xss) = 
             prefs_from_table (map (\<lambda>(x,y). (x, map ((`) \<sigma>) y)) xss)" (is "?f = ?g")
proof
  fix i
  have wf': "prefs_from_table_wf agents alts (map (\<lambda>(x, y). (x, map ((`) \<sigma>) y)) xss)"
  proof (intro prefs_from_table_wfI, goal_cases)
    case (5 xs)
    then obtain y where "y \<in> set xss" "xs = map ((`) \<sigma>) (snd y)"
      by (auto simp add: o_def case_prod_unfold)
    with assms show ?case
      by (simp add: image_Union [symmetric] prefs_from_table_wf_def permutes_image o_def case_prod_unfold)
  next
    case (6 xs)
    then obtain y where "y \<in> set xss" "xs = map ((`) \<sigma>) (snd y)"
      by (auto simp add: o_def case_prod_unfold)
    with assms show ?case
      by (auto simp: is_finite_weak_ranking_def is_weak_ranking_iff prefs_from_table_wf_def
            distinct_map permutes_inj_on inj_on_image intro!: disjoint_image)
  qed (insert assms, simp_all add: image_Union [symmetric] prefs_from_table_wf_def permutes_image o_def case_prod_unfold)
  show "?f i = ?g i"
  proof (cases "i \<in> agents")
    assume "i \<notin> agents"
    with assms wf' show ?thesis
      by (simp add: permute_profile_def prefs_from_table_undef)
  next
    assume i: "i \<in> agents"
    define xs where "xs = the (map_of xss i)"
    from i wf have xs: "map_of xss i = Some xs"
      by (cases "map_of xss i") (auto simp: prefs_from_table_wf_def xs_def)
    have xs_in_xss: "xs \<in> snd ` set xss"
      using xs by (force dest!: map_of_SomeD)
    with wf have set_xs: "\<Union>(set xs) = alts"
      by (simp add: prefs_from_table_wfD)

    from i have "prefs_from_table (map (\<lambda>(x,y). (x, map ((`) \<sigma>) y)) xss) i =
                   of_weak_ranking (the (map_of (map (\<lambda>(x,y). (x, map ((`) \<sigma>) y)) xss) i))"
      using wf' by (intro prefs_from_table_map_of) simp_all
    also have "\<dots> = of_weak_ranking (map ((`) \<sigma>) xs)"
      by (subst map_of_map) (simp add: xs)
    also have "\<dots> = (\<lambda>a b. of_weak_ranking xs (inv \<sigma> a) (inv \<sigma> b))"
      by (intro ext) (simp add: of_weak_ranking_permute map_relation_def set_xs perm)
    also have "\<dots> = permute_profile \<sigma> (prefs_from_table xss) i"
      by (simp add: prefs_from_table_def xs permute_profile_def)
    finally show ?thesis ..
  qed
qed


subsection \<open>Automatic evaluation of preference profiles\<close>

lemma eval_prefs_from_table [simp]:
  "prefs_from_table []i = (\<lambda>_ _. False)"
  "prefs_from_table ((i, y) # xs) i = of_weak_ranking y"
  "i \<noteq> j \<Longrightarrow> prefs_from_table ((j, y) # xs) i = prefs_from_table xs i"
  by (simp_all add: prefs_from_table_def)

lemma eval_of_weak_ranking [simp]:
  "a \<notin> \<Union>(set xs) \<Longrightarrow> \<not>of_weak_ranking xs a b"
  "b \<in> x \<Longrightarrow> a \<in> \<Union>(set (x#xs)) \<Longrightarrow> of_weak_ranking (x # xs) a b"
  "b \<notin> x \<Longrightarrow> of_weak_ranking (x # xs) a b \<longleftrightarrow> of_weak_ranking xs a b"
  by (induction xs) (simp_all add: of_weak_ranking_Cons)

lemma prefs_from_table_cong [cong]:
  assumes "prefs_from_table xs = prefs_from_table ys"
  shows   "prefs_from_table (x#xs) = prefs_from_table (x#ys)"
proof
  fix i
  show "prefs_from_table (x # xs) i = prefs_from_table (x # ys) i"
    using assms by (cases x, cases "i = fst x") simp_all
qed

definition of_weak_ranking_Collect_ge where
  "of_weak_ranking_Collect_ge xs x = {y. of_weak_ranking xs y x}"

lemma eval_Collect_of_weak_ranking:
  "Collect (of_weak_ranking xs x) = of_weak_ranking_Collect_ge (rev xs) x"
  by (simp add: of_weak_ranking_Collect_ge_def)

lemma of_weak_ranking_Collect_ge_empty [simp]:
  "of_weak_ranking_Collect_ge [] x = {}"
  by (simp add: of_weak_ranking_Collect_ge_def)

lemma of_weak_ranking_Collect_ge_Cons [simp]:
  "y \<in> x \<Longrightarrow> of_weak_ranking_Collect_ge (x#xs) y = \<Union>(set (x#xs))"
  "y \<notin> x \<Longrightarrow> of_weak_ranking_Collect_ge (x#xs) y = of_weak_ranking_Collect_ge xs y"
  by (auto simp: of_weak_ranking_Cons of_weak_ranking_Collect_ge_def)

lemma of_weak_ranking_Collect_ge_Cons':
  "of_weak_ranking_Collect_ge (x#xs) = (\<lambda>y.
     (if y \<in> x then \<Union>(set (x#xs)) else of_weak_ranking_Collect_ge xs y))"
  by (auto simp: of_weak_ranking_Cons of_weak_ranking_Collect_ge_def fun_eq_iff)

lemma anonymise_prefs_from_table:
  assumes "prefs_from_table_wf agents alts xs"
  shows   "anonymous_profile (prefs_from_table xs) = mset (map snd xs)"
proof -
  from assms interpret pref_profile_wf agents alts "prefs_from_table xs"
    by (simp add: pref_profile_from_tableI) 
  from assms have agents: "agents = fst ` set xs"
    by (simp add: prefs_from_table_wf_def)
  hence [simp]: "finite agents" by auto
  have "anonymous_profile (prefs_from_table xs) = 
          {#weak_ranking (prefs_from_table xs x). x \<in># mset_set agents#}"
    by (simp add: o_def anonymous_profile_def)
  also from assms have "\<dots> = {#the (map_of xs i). i \<in># mset_set agents#}"
  proof (intro image_mset_cong)
    fix i assume i: "i \<in># mset_set agents"
    from i assms 
      have "weak_ranking (prefs_from_table xs i) = 
              weak_ranking (of_weak_ranking (the (map_of xs i))) "
      by (simp add: prefs_from_table_map_of)
    also from assms i have "\<dots> = the (map_of xs i)"
      by (intro weak_ranking_of_weak_ranking)
         (auto simp: prefs_from_table_wf_def)
    finally show "weak_ranking (prefs_from_table xs i) = the (map_of xs i)" .
  qed
  also from agents have "mset_set agents = mset_set (set (map fst xs))" by simp
  also from assms have "\<dots> = mset (map fst xs)"
    by (intro mset_set_set) (simp_all add: prefs_from_table_wf_def)
  also from assms have "{#the (map_of xs i). i \<in># mset (map fst xs)#} = mset (map snd xs)"
    by (intro image_mset_map_of) (simp_all add: prefs_from_table_wf_def)
  finally show ?thesis .
qed

lemma prefs_from_table_agent_permutation:
  assumes wf: "prefs_from_table_wf agents alts xs" "prefs_from_table_wf agents alts ys"
  assumes mset_eq: "mset (map snd xs) = mset (map snd ys)"
  obtains \<pi> where "\<pi> permutes agents" "prefs_from_table xs \<circ> \<pi> = prefs_from_table ys"
proof -
  from wf(1) have agents: "agents = set (map fst xs)"
    by (simp_all add: prefs_from_table_wf_def)
  from wf(2) have agents': "agents = set (map fst ys)"
    by (simp_all add: prefs_from_table_wf_def)
  from agents agents' wf(1) wf(2) have "mset (map fst xs) = mset (map fst ys)"
    by (subst set_eq_iff_mset_eq_distinct [symmetric]) (simp_all add: prefs_from_table_wfD)
  hence same_length: "length xs = length ys" by (auto dest: mset_eq_length simp del: mset_map)

  from \<open>mset (map fst xs) = mset (map fst ys)\<close>
    obtain g where g: "g permutes {..<length ys}" "permute_list g (map fst ys) = map fst xs"
    by (auto elim: mset_eq_permutation simp: same_length simp del: mset_map)

  from mset_eq g 
    have "mset (map snd ys) = mset (permute_list g (map snd ys))" by simp
  with mset_eq obtain f 
    where f: "f permutes {..<length xs}" 
             "permute_list f (permute_list g (map snd ys)) = map snd xs"
    by (auto elim: mset_eq_permutation simp: same_length simp del: mset_map)
  from permutes_in_image[OF f(1)]
  have [simp]: "f x < length xs \<longleftrightarrow> x < length xs" 
                 "f x < length ys \<longleftrightarrow> x < length ys" for x by (simp_all add: same_length)

  define idx unidx where "idx = index (map fst xs)" and "unidx i = map fst xs ! i" for i
  from wf(1) have "bij_betw idx agents {0..<length xs}" unfolding idx_def
    by (intro bij_betw_index) (simp_all add: prefs_from_table_wf_def)
  hence bij_betw_idx: "bij_betw idx agents {..<length xs}" by (simp add: atLeast0LessThan)
  have [simp]: "idx x < length xs" if "x \<in> agents" for x
    using that by (simp add: idx_def agents)
  have [simp]: "unidx i \<in> agents" if "i < length xs" for i
    using that by (simp add: agents unidx_def)

  have unidx_idx: "unidx (idx x) = x" if x: "x \<in> agents" for x
    using x unfolding idx_def unidx_def using nth_index[of x "map fst xs"]
    by (simp add: agents set_map [symmetric] nth_map [symmetric] del: set_map)
  have idx_unidx: "idx (unidx i) = i" if i: "i < length xs" for i
    unfolding idx_def unidx_def using wf(1) index_nth_id[of "map fst xs" i] i
    by (simp add: prefs_from_table_wfD(3))
 
  define \<pi> where "\<pi> x = (if x \<in> agents then (unidx \<circ> f \<circ> idx) x else x)" for x
  define \<pi>' where "\<pi>' x = (if x \<in> agents then (unidx \<circ> inv f \<circ> idx) x else x)" for x
  have "bij_betw (unidx \<circ> f \<circ> idx) agents agents" (is "?P") unfolding unidx_def
    by (rule bij_betw_trans bij_betw_idx permutes_imp_bij f g bij_betw_nth)+
       (insert wf(1) g, simp_all add: prefs_from_table_wf_def same_length)
  also have "?P \<longleftrightarrow> bij_betw \<pi> agents agents"
    by (intro bij_betw_cong) (simp add: \<pi>_def)
  finally have perm: "\<pi> permutes agents"
    by (intro bij_imp_permutes) (simp_all add: \<pi>_def)

  define h where "h = g \<circ> f"
  from f g have h: "h permutes {..<length ys}" unfolding h_def
    by (intro permutes_compose) (simp_all add: same_length)

  have inv_\<pi>: "inv \<pi> = \<pi>'"
  proof (rule permutes_invI[OF perm])
    fix x assume "x \<in> agents"
    with f(1) show "\<pi>' (\<pi> x) = x"
      by (simp add: \<pi>_def \<pi>'_def idx_unidx unidx_idx inv_f_f permutes_inj)
  qed (simp add: \<pi>_def \<pi>'_def)
  with perm have inv_\<pi>': "inv \<pi>' = \<pi>" by (auto simp: inv_inv_eq permutes_bij)

  from wf h have "prefs_from_table ys = prefs_from_table (permute_list h ys)"
    by (intro prefs_from_table_eqI)
       (simp_all add: prefs_from_table_wfD permute_list_map [symmetric])
  also have "permute_list h ys = permute_list h (zip (map fst ys) (map snd ys))"
    by (simp add: zip_map_fst_snd)
  also from same_length f g
    have "permute_list h (zip (map fst ys) (map snd ys)) = 
            zip (permute_list f (map fst xs)) (map snd xs)"
    by (subst permute_list_zip[OF h]) (simp_all add: h_def permute_list_compose)
  also {
    fix i assume i: "i < length xs"
    from i have "permute_list f (map fst xs) ! i = unidx (f i)"
      using permutes_in_image[OF f(1)] f(1) 
      by (subst permute_list_nth) (simp_all add: same_length unidx_def)
    also from i have "\<dots> = \<pi> (unidx i)" by (simp add: \<pi>_def idx_unidx)
    also from i have "\<dots> = map \<pi> (map fst xs) ! i" by (simp add: unidx_def)
    finally have "permute_list f (map fst xs) ! i = map \<pi> (map fst xs) ! i" .
  }
  hence "permute_list f (map fst xs) = map \<pi> (map fst xs)"
    by (intro nth_equalityI) simp_all
  also have "zip (map \<pi> (map fst xs)) (map snd xs) = map (\<lambda>(x,y). (inv \<pi>' x, y)) xs"
    by (induction xs) (simp_all add: case_prod_unfold inv_\<pi>')
  also from permutes_inv[OF perm] inv_\<pi> have "prefs_from_table \<dots> = prefs_from_table xs \<circ> \<pi>'"
    by (intro permute_prefs_from_table [symmetric]) (simp_all add: agents)
  finally have "prefs_from_table xs \<circ> \<pi>' = prefs_from_table ys" ..
  with that[of \<pi>'] permutes_inv[OF perm] inv_\<pi> show ?thesis by auto
qed

lemma permute_list_distinct:
  assumes "f ` {..<length xs} \<subseteq> {..<length xs}" "distinct xs"
  shows   "permute_list f xs = map (\<lambda>x. xs ! f (index xs x)) xs"
  using assms by (intro nth_equalityI) (auto simp: index_nth_id permute_list_def)

lemma image_mset_eq_permutation:
  assumes "{#f x. x \<in># mset_set A#} = {#g x. x \<in># mset_set A#}" "finite A"
  obtains \<pi> where "\<pi> permutes A" "\<And>x. x \<in> A \<Longrightarrow> g (\<pi> x) = f x"
proof -
  from assms(2) obtain xs where xs: "A = set xs" "distinct xs"
    using finite_distinct_list by blast
  with assms have "mset (map f xs) = mset (map g xs)" 
    by (simp add: mset_set_set)
  from mset_eq_permutation[OF this] obtain \<pi> where
    \<pi>: "\<pi> permutes {0..<length xs}" "permute_list \<pi> (map g xs) = map f xs"
    by (auto simp: atLeast0LessThan)
  define \<pi>' where "\<pi>' x = (if x \<in> A then ((!) xs \<circ> \<pi> \<circ> index xs) x else x)" for x
  have "bij_betw ((!) xs \<circ> \<pi> \<circ> index xs) A A" (is "?P")
    by (rule bij_betw_trans bij_betw_index xs refl permutes_imp_bij \<pi> bij_betw_nth)+
       (simp_all add: atLeast0LessThan xs)
  also have "?P \<longleftrightarrow> bij_betw \<pi>' A A"
    by (intro bij_betw_cong) (simp_all add: \<pi>'_def)
  finally have "\<pi>' permutes A"
    by (rule bij_imp_permutes) (simp_all add: \<pi>'_def)
  moreover from \<pi> xs(1)[symmetric] xs(2) have "g (\<pi>' x) = f x" if "x \<in> A" for x
    by (simp add: permute_list_map permute_list_distinct
          permutes_image \<pi>'_def that atLeast0LessThan)
  ultimately show ?thesis by (rule that)
qed

lemma anonymous_profile_agent_permutation:
  assumes eq:  "anonymous_profile R1 = anonymous_profile R2"
  assumes wf:  "pref_profile_wf agents alts R1" "pref_profile_wf agents alts R2"
  assumes fin: "finite agents"
  obtains \<pi> where "\<pi> permutes agents" "R2 \<circ> \<pi> = R1"
proof -
  interpret R1: pref_profile_wf agents alts R1 by fact
  interpret R2: pref_profile_wf agents alts R2 by fact

  from eq have "{#weak_ranking (R1 x). x \<in># mset_set agents#} = 
                  {#weak_ranking (R2 x). x \<in># mset_set agents#}"
    by (simp add: R1.anonymous_profile_def R2.anonymous_profile_def o_def)
  from image_mset_eq_permutation[OF this fin] guess \<pi> . note \<pi> = this
  from \<pi> have wf': "pref_profile_wf agents alts (R2 \<circ> \<pi>)"
    by (intro R2.wf_permute_agents)
  then interpret R2': pref_profile_wf agents alts "R2 \<circ> \<pi>" .
  have "R2 \<circ> \<pi> = R1"
  proof (intro pref_profile_eqI[OF wf' wf(1)])
    fix x assume x: "x \<in> agents"
    with \<pi> have "weak_ranking ((R2 o \<pi>) x) = weak_ranking (R1 x)" by simp
    with wf' wf(1) x show "(R2 \<circ> \<pi>) x = R1 x"
      by (intro weak_ranking_eqD[of alts] R2'.prefs_wf) simp_all
  qed
  from \<pi>(1) and this show ?thesis by (rule that)
qed

end
