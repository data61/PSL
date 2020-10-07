(* License: LGPL *)
(*
Author: Julian Parsert <julian.parsert@gmail.com>
Author: Cezary Kaliszyk
*)

section \<open>Preference Relations\<close>

text \<open> Preferences modeled as a set of pairs \<close>

theory Preferences
  imports
    "HOL-Analysis.Analysis"
    Syntax
begin


subsection \<open>Basic Preference Relation\<close>

text \<open> Basic preference relation locale with carrier and relation modeled as a set of pairs. \<close>

locale preference =
  fixes carrier :: "'a set"
  fixes relation :: "'a relation"
  assumes not_outside: "(x,y) \<in> relation \<Longrightarrow> x \<in> carrier"
    and "(x,y) \<in> relation \<Longrightarrow> y \<in> carrier"
  assumes trans_refl: "preorder_on  carrier relation"

context preference
begin

abbreviation geq ("_ \<succeq> _" [51,51] 60)
  where
    "x \<succeq> y \<equiv> x \<succeq>[relation] y"

abbreviation str_gr ("_ \<succ> _" [51,51] 60)
  where
    "x \<succ> y \<equiv> x \<succeq> y \<and> \<not>y \<succeq> x"

abbreviation indiff ("_ \<approx> _" [51,51] 60)
  where
    "x \<approx> y \<equiv> x \<succeq> y \<and> y \<succeq> x"

lemma reflexivity: "refl_on carrier relation"
  using preorder_on_def trans_refl by blast

lemma transitivity: "trans relation"
  using preorder_on_def trans_refl by auto

lemma indiff_trans [simp]: "x \<approx> y \<Longrightarrow> y \<approx> z \<Longrightarrow> x \<approx> z"
  by (meson transE transitivity)

end


subsubsection \<open> Contour sets \<close>

definition at_least_as_good :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a relation \<Rightarrow> 'a set"
  where
    "at_least_as_good x B P = {y \<in> B. y \<succeq>[P] x }"

definition no_better_than :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a relation \<Rightarrow> 'a set"
  where
    "no_better_than x B P = {y \<in> B. x \<succeq>[P] y}"

definition as_good_as :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a relation \<Rightarrow> 'a set"
  where
    "as_good_as x B P = {y \<in> B. x \<approx>[P] y}"

lemma at_lst_asgd_ge:
  assumes "x \<in> at_least_as_good y B Pr"
  shows "x \<succeq>[Pr] y"
  using assms at_least_as_good_def by fastforce

lemma strict_contour_is_diff:
  "{a \<in> B. a \<succ>[Pr] y} = at_least_as_good y B Pr - as_good_as y B Pr"
  by(auto simp add: at_least_as_good_def as_good_as_def)

lemma strict_countour_def [simp]:
  "(at_least_as_good y B Pr) - as_good_as y B Pr = {x \<in> B. x \<succ>[Pr] y}"
  by (simp add: as_good_as_def at_least_as_good_def strict_contour_is_diff)

lemma at_least_as_goodD [dest]:
  assumes "z \<in> at_least_as_good y B Pr"
  shows "z \<succeq>[Pr] y"
  using assms at_least_as_good_def by fastforce


subsection \<open>Rational Preference Relation\<close>

text \<open> Rational preferences add totality to the basic preferences. \<close>

locale rational_preference = preference +
  assumes total: "total_on carrier relation"
begin

lemma compl: "\<forall>x \<in> carrier . \<forall>y\<in> carrier . x \<succeq> y \<or> y \<succeq> x"
  by (metis refl_onD reflexivity total total_on_def)

lemma strict_not_refl_weak [iff]: "x \<in> carrier \<and> y \<in> carrier \<Longrightarrow> \<not> (y \<succeq> x) \<longleftrightarrow> x \<succ> y"
  by (metis refl_onD reflexivity total total_on_def)

lemma strict_trans [simp]: "x \<succ> y \<Longrightarrow> y \<succ> z \<Longrightarrow> x \<succ> z"
  by (meson transE transitivity)

lemma completeD [dest]: "x \<in> carrier \<Longrightarrow> y \<in> carrier \<Longrightarrow> x \<noteq> y \<Longrightarrow> x \<succeq> y \<or> y \<succeq> x"
  by blast

lemma pref_in_at_least_as:
  assumes "x \<succeq> y"
  shows "x \<in> at_least_as_good y carrier relation"
  by (metis (no_types, lifting) CollectI assms
      at_least_as_good_def preference.not_outside preference_axioms)

lemma worse_in_no_better:
  assumes "x \<succeq> y"
  shows "y \<in> no_better_than y carrier relation"
  by (metis (no_types, lifting) CollectI assms no_better_than_def
      preference_axioms preference_def strict_not_refl_weak)

lemma strict_is_neg_transitive :
  assumes "x \<in> carrier \<and> y \<in> carrier \<and> z \<in> carrier"
  shows "x \<succ> y \<Longrightarrow> x \<succ> z \<or> z \<succ> y"
  by (meson assms compl transE transitivity)

lemma weak_is_transitive:
 assumes "x \<in> carrier \<and> y \<in> carrier \<and> z \<in> carrier"
 shows "x \<succeq> y \<Longrightarrow> y \<succeq> z \<Longrightarrow> x \<succeq> z"
  by (meson transD transitivity)

lemma no_better_than_nonepty:
  assumes "carrier \<noteq> {}"
  shows "\<And>x. x \<in> carrier \<Longrightarrow> (no_better_than x carrier relation) \<noteq> {}"
  by (metis (no_types, lifting) empty_iff mem_Collect_eq
      no_better_than_def refl_onD reflexivity)

lemma no_better_subset_pref :
  assumes "x \<succeq> y"
  shows "no_better_than y carrier relation \<subseteq> no_better_than x carrier relation"
proof
  fix a
  assume "a \<in> no_better_than y carrier relation"
  then show "a \<in> no_better_than x carrier relation"
    by (metis (no_types, lifting) assms mem_Collect_eq no_better_than_def transE transitivity)
qed

lemma no_better_thansubset_rel :
  assumes "x \<in> carrier" and "y \<in> carrier"
  assumes "no_better_than y carrier relation \<subseteq> no_better_than x carrier relation"
  shows "x \<succeq> y"
proof -
  have  "{a \<in> carrier. y \<succeq> a} \<subseteq> {a \<in> carrier. x \<succeq> a}"
    by (metis (no_types) assms(3) no_better_than_def)
  then show ?thesis
    by (metis (mono_tags, lifting) Collect_mono_iff assms(2) compl)
qed

lemma nbt_nest :
  shows "(no_better_than y carrier relation \<subseteq> no_better_than x carrier relation) \<or>
        (no_better_than x carrier relation \<subseteq> no_better_than y carrier relation)"
  by (metis (no_types, lifting) CollectD compl no_better_subset_pref no_better_than_def not_outside subsetI)

lemma at_lst_asgd_not_ge:
  assumes "carrier \<noteq> {}"
  assumes "x \<in> carrier" and "y \<in> carrier"
  assumes "x \<notin> at_least_as_good y carrier relation"
  shows "\<not> x \<succeq> y"
  by (metis (no_types, lifting) CollectI assms(2) assms(4) at_least_as_good_def)

lemma as_good_as_sameIff[iff]:
  "z \<in> as_good_as y carrier relation \<longleftrightarrow> z \<succeq> y \<and> y \<succeq> z"
  by (metis (no_types, lifting) as_good_as_def mem_Collect_eq not_outside)

lemma same_at_least_as_equal:
  assumes "z \<approx> y"
  shows "at_least_as_good z carrier relation =
         at_least_as_good y carrier relation" (is "?az = ?ay")
proof
  have "z \<in> carrier \<and> y \<in> carrier"
    by (meson assms refl_onD2 reflexivity)
  moreover have "\<forall>x \<in> carrier. x \<succeq> z \<longrightarrow> x \<succeq> y"
    by (meson assms transD transitivity)
  ultimately show "?az \<subseteq> ?ay"
    by (metis at_lst_asgd_ge at_lst_asgd_not_ge
        equals0D not_outside subsetI)
next
   have "z \<in> carrier \<and> y \<in> carrier"
    by (meson assms refl_onD2 reflexivity)
  moreover have "\<forall>x \<in> carrier. x \<succeq> y \<longrightarrow> x \<succeq> z"
    by (meson assms transD transitivity)
  ultimately show "?ay \<subseteq> ?az"
    by (metis at_lst_asgd_ge at_lst_asgd_not_ge
        equals0D not_outside subsetI)
qed

lemma as_good_asIff [iff]:
  "x \<in> as_good_as y carrier relation \<longleftrightarrow> x \<approx>[relation] y"
  by blast

lemma nbt_subset:
  assumes "finite carrier"
  assumes "x \<in> carrier" and "y \<in> carrier"
  shows "no_better_than x carrier relation \<subseteq> no_better_than x carrier relation \<or>
         no_better_than x carrier relation \<subseteq> no_better_than x carrier relation"
  by auto

lemma fnt_carrier_fnt_rel: "finite carrier \<Longrightarrow> finite relation"
  by (metis finite_SigmaI refl_on_def reflexivity rev_finite_subset)

lemma nbt_subset_carrier:
  assumes "x \<in> carrier"
  shows "no_better_than x carrier relation \<subseteq> carrier"
  using no_better_than_def by fastforce

lemma xy_in_eachothers_nbt:
  assumes "x \<in> carrier" "y \<in> carrier"
  shows "x \<in> no_better_than y carrier relation \<or>
         y \<in> no_better_than x carrier relation"
  by (meson assms(1) assms(2) contra_subsetD nbt_nest refl_onD reflexivity worse_in_no_better)

lemma same_nbt_same_pref:
  assumes "x \<in> carrier" "y \<in> carrier"
  shows "x \<in> no_better_than y carrier relation \<and>
         y \<in> no_better_than x carrier relation \<longleftrightarrow> x \<approx> y"
    by (metis (mono_tags, lifting) CollectD contra_subsetD no_better_subset_pref
        no_better_than_def worse_in_no_better)

lemma indifferent_imp_weak_pref: 
  assumes "x \<approx> y"
  shows" x \<succeq> y" "y \<succeq> x"
  by (simp add: assms)+

subsection \<open> Finite carrier\<close>

context
  assumes "finite carrier"
begin

lemma fnt_carrier_fnt_nbt:
  shows "\<forall>x\<in>carrier. finite (no_better_than x carrier relation)"
proof
  fix x
  assume "x \<in> carrier"
  then show "finite (no_better_than x carrier relation)"
  using  finite_subset nbt_subset_carrier \<open>finite carrier\<close> by blast
qed

lemma nbt_subset_imp_card_leq:
  assumes "x \<in> carrier" and "y \<in> carrier"
  shows "no_better_than x carrier relation \<subseteq> no_better_than y carrier relation \<longleftrightarrow>
  card (no_better_than x carrier relation) \<le> card  (no_better_than y carrier relation)"
  (is "?nbt \<longleftrightarrow> ?card")
proof
  assume "?nbt"
  then show "?card"
    by (simp add: assms(2) card_mono fnt_carrier_fnt_nbt)
next
  assume "?card"
  then show "?nbt"
    by (metis  assms(1) card_seteq fnt_carrier_fnt_nbt nbt_nest)
qed

lemma card_leq_pref:
  assumes "x \<in> carrier" and "y \<in> carrier"
  shows "card (no_better_than x carrier relation) \<le> card (no_better_than y carrier relation)
   \<longleftrightarrow> y \<succeq> x"
proof (rule iffI, goal_cases)
  case 1
  then show ?case
    using assms(1) assms(2) nbt_subset_imp_card_leq no_better_thansubset_rel by presburger
next
  case 2
  then show ?case
    using assms(1) assms(2) nbt_subset_imp_card_leq no_better_subset_pref by blast
qed

lemma finite_ne_remove_induct:
  assumes "finite B" "B \<noteq> {}"
    "\<And>A. finite A  \<Longrightarrow> A \<subseteq> B \<Longrightarrow> A \<noteq> {} \<Longrightarrow>
         (\<And>x. x \<in> A \<Longrightarrow> A - {x} \<noteq> {} \<Longrightarrow> P (A - {x})) \<Longrightarrow> P A"
  shows "P B"
  by (metis assms finite_remove_induct[where P = "\<lambda>F. F = {} \<or> P F" for P])


lemma finite_nempty_preorder_has_max:
  assumes "finite B" "B \<noteq> {}" "refl_on B R" "trans R" "total_on B R"
  shows "\<exists>x \<in> B. \<forall>y \<in> B. (x, y) \<in> R"
  using assms(1) subset_refl[of B] assms(2)
proof (induct B rule: finite_subset_induct)
  case (insert x F)
  then show ?case using assms(3-)
    by (cases "F = {}") (auto simp: refl_onD total_on_def, metis refl_onD2 transE)
qed auto

lemma finite_nempty_preorder_has_min:
  assumes "finite B" "B \<noteq> {}" "refl_on B R" "trans R" "total_on B R"
  shows "\<exists>x \<in> B. \<forall>y \<in> B. (y, x) \<in> R"
  using assms(1) subset_refl[of B] assms(2)
proof (induct B rule: finite_subset_induct)
  case (insert x F)
  then show ?case using assms(3-)
    by (cases "F = {}") (auto simp: refl_onD total_on_def, metis refl_onD2 transE)
qed auto

lemma finite_nonempty_carrier_has_maximum:
  assumes "carrier \<noteq> {}"
  shows "\<exists>e \<in> carrier. \<forall>m \<in> carrier. e \<succeq>[relation] m"
  using finite_nempty_preorder_has_max[of carrier relation] assms
     \<open>finite carrier\<close> reflexivity total transitivity by blast

lemma finite_nonempty_carrier_has_minimum:
  assumes "carrier \<noteq> {}"
  shows "\<exists>e \<in> carrier. \<forall>m \<in> carrier. m \<succeq>[relation] e"
  using finite_nempty_preorder_has_min[of carrier relation] assms
     \<open>finite carrier\<close> reflexivity total transitivity by blast

end (*finite carrier*)


lemma all_carrier_ex_sub_rel: 
  "\<forall>c \<subseteq> carrier. \<exists>r \<subseteq> relation. rational_preference c r"
proof (standard,standard)
  fix c
  assume c_in: "c \<subseteq> carrier"
  define r' where
    "r' = {(x,y) \<in> relation. x \<in> c \<and> y \<in> c}"
  have r'_sub: "r' \<subseteq> c \<times> c"
    using r'_def by blast
  have "\<forall>x \<in> c. x \<succeq>[r'] x"
    by (metis (no_types, lifting) CollectI c_in case_prodI compl r'_def subsetCE)
  then have refl: "refl_on c r'"
    by (meson r'_sub refl_onI)
  have trans: "trans r'"
  proof
    fix x y z
    assume a1: "x \<succeq>[r'] y"
    assume a2: "y \<succeq>[r'] z"
    show " x \<succeq>[r'] z"
      by (metis (mono_tags, lifting) CollectD CollectI a1 a2 case_prodD case_prodI r'_def transE transitivity)
  qed
  have total: "total_on c r'"
  proof (standard)
    fix x y
    assume a1:"x \<in> c"
    assume a2: "y \<in> c"
    assume a3: "x \<noteq> y"
    show "x \<succeq>[r'] y \<or> y \<succeq>[r'] x "
      by (metis (no_types, lifting) CollectI a1 a2 c_in case_prodI compl r'_def subset_iff)
  qed
  have "rational_preference c r'"
    by (meson local.refl local.trans preference.intro preorder_on_def rational_preference.intro 
        rational_preference_axioms.intro refl_on_domain total)
  thus "\<exists>r\<subseteq>relation. rational_preference c r"
    by (metis (no_types, lifting) CollectD case_prodD r'_def subrelI)
qed

end (*rational preference*)


subsection \<open> Local Non-Satiation \<close>

text \<open> Defining local non-satiation. \<close>

definition local_nonsatiation
  where
  "local_nonsatiation B P \<longleftrightarrow>
   (\<forall>x\<in>B. \<forall>e>0. \<exists>y\<in>B. norm (y - x) \<le> e \<and> y \<succ>[P] x)"

text \<open> Alternate definitions and intro/dest rules with them \<close>

lemma lns_alt_def1 [iff] :
  shows "local_nonsatiation B P \<longleftrightarrow> (\<forall>x \<in> B. \<forall>e>0. (\<exists>y \<in> B. dist y x \<le> e \<and> y \<succ>[P] x))"
  by(simp add : dist_norm local_nonsatiation_def)

lemma lns_normI [intro]:
  assumes "\<And>x e. x \<in> B \<Longrightarrow> e > 0 \<Longrightarrow> (\<exists>y\<in>B. norm (y - x) \<le> e \<and> y \<succ>[P] x)"
  shows "local_nonsatiation B P"
  by (simp add: assms dist_norm)

lemma lns_distI [intro]:
  assumes "\<And>x e. x \<in> B \<Longrightarrow> e > 0 \<Longrightarrow> (\<exists>y\<in>B. (dist y x) \<le> e \<and> y \<succ>[P] x)"
  shows "local_nonsatiation B P"
  by (meson lns_alt_def1 assms)

lemma lns_alt_def2 [iff]:
  "local_nonsatiation B P \<longleftrightarrow> (\<forall>x\<in>B. \<forall>e>0. (\<exists>y.  y \<in> (ball x e) \<and> y \<in> B \<and> y \<succ>[P] x))"
proof
  assume "local_nonsatiation B P"
  then show "\<forall>x\<in>B. \<forall>e>0. \<exists>x'. x' \<in> ball x e \<and> x' \<in> B \<and> x' \<succ>[P] x"
    by (auto simp add : ball_def) (metis dense le_less_trans dist_commute)
next
  assume "\<forall>x\<in>B. \<forall>e>0. \<exists>y. y \<in> ball x e \<and> y \<in> B \<and> y \<succ>[P] x"
  then show "local_nonsatiation B P"
    by (metis (no_types, lifting) ball_def dist_commute
        less_le_not_le lns_alt_def1 mem_Collect_eq)
qed

lemma lns_normD [dest]:
  assumes "local_nonsatiation B P"
  shows "\<forall>x \<in> B. \<forall>e>0. \<exists>y \<in> B. (norm (y - x) \<le> e \<and> y \<succ>[P] x)"
  by (meson assms local_nonsatiation_def)


subsection \<open> Convex preferences \<close>

definition weak_convex_pref :: "('a::real_vector) relation \<Rightarrow> bool"
  where
    "weak_convex_pref Pr \<longleftrightarrow> (\<forall>x y. x \<succeq>[Pr] y \<longrightarrow>
      (\<forall>\<alpha> \<beta>. \<alpha> + \<beta> = 1 \<and> \<alpha> > 0 \<and> \<beta> > 0 \<longrightarrow> \<alpha> *\<^sub>R x + \<beta> *\<^sub>R y \<succeq>[Pr] y))"

definition convex_pref :: "('a::real_vector) relation \<Rightarrow> bool"
  where
    "convex_pref Pr \<longleftrightarrow> (\<forall>x y. x \<succ>[Pr] y \<longrightarrow>
      (\<forall>\<alpha>. 1 > \<alpha> \<and> \<alpha> > 0 \<longrightarrow> \<alpha> *\<^sub>R x + (1-\<alpha>) *\<^sub>R y \<succ>[Pr] y))"

definition strict_convex_pref :: "('a::real_vector) relation \<Rightarrow> bool"
  where
    "strict_convex_pref Pr \<longleftrightarrow> (\<forall>x y. x \<succeq>[Pr] y \<and> x \<noteq> y \<longrightarrow>
      (\<forall>\<alpha>. 1 > \<alpha> \<and> \<alpha> > 0 \<longrightarrow> \<alpha> *\<^sub>R x + (1-\<alpha>) *\<^sub>R y \<succ>[Pr] y))"

lemma convex_ge_imp_conved:
  assumes "\<forall>x y. x \<succeq>[Pr] y \<longrightarrow> (\<forall>\<alpha> \<beta>. \<alpha> + \<beta> = 1 \<and> \<alpha> \<ge> 0 \<and> \<beta> \<ge> 0 \<longrightarrow> \<alpha> *\<^sub>R x + \<beta> *\<^sub>R y \<succeq>[Pr] y)"
  shows "weak_convex_pref Pr"
  by (simp add: assms weak_convex_pref_def)

lemma weak_convexI [intro]:
  assumes "\<And>x y \<alpha> \<beta>. x \<succeq>[Pr] y \<Longrightarrow> \<alpha> + \<beta> = 1 \<Longrightarrow> 0 < \<alpha> \<Longrightarrow> 0 < \<beta> \<Longrightarrow> \<alpha> *\<^sub>R x + \<beta> *\<^sub>R y \<succeq>[Pr] y"
  shows "weak_convex_pref Pr"
  by (simp add: assms weak_convex_pref_def)

lemma weak_convexD [dest]:
  assumes "weak_convex_pref Pr" and "x \<succeq>[Pr] y" and "0 < u" and "0 < v" and "u + v = 1"
  shows "u *\<^sub>R x + v *\<^sub>R y \<succeq>[Pr] y"
    using assms weak_convex_pref_def by blast


subsection \<open> Real Vector Preferences \<close>

text \<open> Preference relations on real vector type class. \<close>

locale real_vector_rpr = rational_preference carrier relation
for carrier :: "'a::real_vector set"
and relation :: "'a relation"

sublocale  real_vector_rpr \<subseteq> rational_preference carrier relation
  by (simp add: rational_preference_axioms)

context real_vector_rpr
begin

lemma have_rpr: "rational_preference carrier relation"
  by (simp add: rational_preference_axioms)

text \<open> Multiple convexity alternate definitions intro/dest rules. \<close>

lemma weak_convex1D [dest]:
  assumes "weak_convex_pref relation" and "x \<succeq>[relation] y" and "0 \<le> u" and "0 \<le> v" and "u + v = 1"
  shows "u *\<^sub>R x + v *\<^sub>R y \<succeq>[relation] y"
proof-
  have u_0: "u = 0 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<succeq>[relation] y"
  proof
    assume u_0: "u = 0"
    have "v = 1"
      using assms(5) u_0 by auto
    then have "?thesis"
      by (metis add.left_neutral assms(2) preference.reflexivity preference_axioms
          real_vector.scale_zero_left refl_onD2 scaleR_one strict_not_refl_weak)
    thus "u *\<^sub>R x + v *\<^sub>R y \<succeq>[relation] y "
      using u_0 by blast
  qed
  have "u \<noteq> 0 \<and> u \<noteq> 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<succeq>[relation] y"
    by (metis add_cancel_right_right antisym_conv not_le assms weak_convexD )
  then show ?thesis
    by (metis u_0 assms(2,5) add_cancel_right_right real_vector.scale_zero_left scaleR_one)
qed

lemma weak_convex1I [intro] :
  assumes "\<forall>x. convex (at_least_as_good x carrier relation)"
  shows "weak_convex_pref relation"
proof (rule weak_convexI)
  fix x and y and \<alpha> \<beta> :: real
  assume assum : "x \<succeq>[relation] y"
  assume reals: "0 < \<alpha>" "0 < \<beta>" " \<alpha> + \<beta> = 1"
  then have "x \<in> carrier"
    by (meson assum preference.not_outside rational_preference.axioms(1) have_rpr)
  have "y \<in> carrier"
    by (meson assum refl_onD2 reflexivity)
  then have y_in_upper_cont: "y \<in> (at_least_as_good y carrier relation)"
    using assms rational_preference.at_lst_asgd_not_ge
      rational_preference.compl  by (metis empty_iff have_rpr)
  then have "x \<in> (at_least_as_good y carrier relation)"
    using assum pref_in_at_least_as by blast
  moreover have "0 \<le> \<beta>" and "0 \<le> \<alpha>"
    using reals by (auto)
  ultimately show "(\<alpha> *\<^sub>R x + \<beta> *\<^sub>R y) \<succeq>[relation] y"
    by (meson assms(1) at_least_as_goodD convexD reals(3) y_in_upper_cont)
qed

text \<open> Definition of convexity in "Handbook of Social Choice and Welfare"@{cite "arrow2010handbook"}. \<close>

lemma convex_def_alt:
  assumes "rational_preference carrier relation"
  assumes "weak_convex_pref relation"
  shows "(\<forall>x \<in> carrier. convex (at_least_as_good x carrier relation))"
proof
  fix x
  assume x_in: "x \<in> carrier"
  show "convex (at_least_as_good x carrier relation)" (is "convex ?x")
  proof (rule convexI)
    fix a b :: "'a" and  \<alpha> :: "real" and \<beta> :: "real"
    assume a_in: "a \<in> ?x"
    assume b_in: "b \<in> ?x"
    assume reals: " 0 \<le> \<alpha>" "0 \<le> \<beta>" "\<alpha> + \<beta> = 1"
    have a_g_x: "a \<succeq>[relation] x"
      using a_in by blast
    have b_g_x: "b \<succeq>[relation] x"
      using b_in by blast
    have "a \<succeq>[relation] b \<or> b \<succeq>[relation] a"
      by (meson a_in at_least_as_goodD b_in preference.not_outside
          rational_preference.compl rational_preference_def assms(1))
    then show "\<alpha> *\<^sub>R a + \<beta> *\<^sub>R b \<in> ?x"
    proof(rule disjE)
      assume "a \<succeq>[relation] b"
      then have "\<alpha> *\<^sub>R a + \<beta> *\<^sub>R b  \<succeq>[relation] b"
        using assms reals by blast
      then have "\<alpha> *\<^sub>R a + \<beta> *\<^sub>R b \<succeq>[relation] x"
        by (meson b_g_x  assms(1) preference.not_outside x_in
            rational_preference.strict_is_neg_transitive
            rational_preference.strict_not_refl_weak rational_preference_def)
      then show ?thesis
        by (metis (no_types, lifting) CollectI  assms(1)
            at_least_as_good_def preference_def rational_preference_def)
    next
      assume as: "b \<succeq>[relation] a"
      then have "\<alpha> *\<^sub>R a + \<beta> *\<^sub>R b \<succeq>[relation] a"
        by (metis add.commute assms(2) reals weak_convex1D)
      have "\<alpha> *\<^sub>R a + \<beta> *\<^sub>R b \<succeq>[relation] a"
        by (metis as add.commute  assms(2)
            reals(1,2,3) weak_convex1D)
      then have "\<alpha> *\<^sub>R a + \<beta> *\<^sub>R b \<succeq>[relation] x"
        by (meson a_g_x assms(1) preference.indiff_trans x_in
            preference.not_outside rational_preference.axioms(1)
            rational_preference.strict_is_neg_transitive )
      then show ?thesis
        using pref_in_at_least_as by blast
    qed
  qed
qed

lemma convex_imp_convex_str_upper_cnt:
  assumes "\<forall>x \<in> carrier. convex (at_least_as_good x carrier relation)"
  shows "convex (at_least_as_good x carrier relation - as_good_as x carrier relation)"
    (is "convex ( ?a - ?b)")
proof (rule convexI)
  fix a y u v
  assume as_a: "a \<in> ?a - ?b"
  assume as_y: "y \<in> ?a - ?b"
  assume reals: "0 \<le> (u::real)" "0 \<le> v" "u + v = 1"
  have cvx: "weak_convex_pref relation "
    by (meson assms at_least_as_goodD convexI have_rpr
        preference_def rational_preference.axioms(1) weak_convex1I)
  then have a_g_x: "a \<succ>[relation] x"
    using as_a by blast
  then have y_gt_x: "y \<succ>[relation] x"
    using as_y by blast
  show "u *\<^sub>R a + v *\<^sub>R y \<in> ?a - ?b"
  proof
    show "u *\<^sub>R a + v *\<^sub>R y \<in> ?a"
      by (metis DiffD1 a_g_x as_a as_y assms convexD reals have_rpr
          preference_def rational_preference.axioms(1))
  next
    have "a \<succeq>[relation] y \<or> y \<succeq>[relation] a"
      by (meson a_g_x y_gt_x assms(1) preference.not_outside have_rpr
          rational_preference.axioms(1) rational_preference.strict_not_refl_weak)
    then show "u *\<^sub>R a + v *\<^sub>R y \<notin> ?b"
    proof
      assume "a \<succeq>[relation] y"
      then have "u *\<^sub>R a + v *\<^sub>R y \<succeq>[relation] y"
        using cvx assms(1) reals by blast
      then have "u *\<^sub>R a + v *\<^sub>R y \<succ>[relation] x"
        using y_gt_x by (meson assms(1) rational_preference.axioms(1) have_rpr
            rational_preference.strict_is_neg_transitive preference_def)
      then show "u *\<^sub>R a + v *\<^sub>R y \<notin> as_good_as x carrier relation"
        by blast
    next
      assume "y \<succeq>[relation] a"
      then have "u *\<^sub>R a + v *\<^sub>R y \<succeq>[relation] a"
        using cvx assms(1) reals by (metis add.commute weak_convex1D)
      then have "u *\<^sub>R a + v *\<^sub>R y \<succ>[relation] x"
        by (meson a_g_x assms(1) rational_preference.strict_is_neg_transitive
            rational_preference.axioms(1) preference_def have_rpr)
      then show "u *\<^sub>R a + v *\<^sub>R y \<notin> ?b"
        by blast
    qed
  qed
qed

end

subsubsection \<open> Monotone preferences \<close>

definition weak_monotone_prefs :: "'a set \<Rightarrow> ('a::ord) relation \<Rightarrow> bool"
  where
    "weak_monotone_prefs B P \<longleftrightarrow> (\<forall>x \<in> B. \<forall>y \<in> B. x \<ge> y \<longrightarrow> x \<succeq>[P]y)"

definition monotone_preference :: "'a set \<Rightarrow> ('a::ord) relation \<Rightarrow> bool"
  where
    "monotone_preference B P \<longleftrightarrow> (\<forall>x \<in> B. \<forall>y \<in> B. x > y \<longrightarrow> x \<succ>[P] y)"


text \<open> Given a carrier set that is unbounded above (not the "standard" mathematical definition),
       monotonicity implies local non-satiation. \<close>

lemma unbounded_above_mono_imp_lns:
  assumes "\<forall>M \<in> carrier. (\<forall>x > M. x \<in> carrier)"
  assumes mono: "monotone_preference (carrier:: 'a::ordered_euclidean_space set) relation"
  shows "local_nonsatiation carrier relation"
proof(rule lns_distI)
  fix x and e::"real"
  assume x_in: "x \<in> carrier"
  assume gz : "e > 0"
  show "\<exists>y\<in>carrier. dist y x \<le> e \<and> y \<succeq>[relation] x \<and> (x, y) \<notin> relation"
  proof-
    obtain v :: real where
      v:"v < e" "0 < v" using gz dense by blast
    obtain i where
      i:"(i::'a) \<in> Basis" by fastforce
    define y where
      y_value : "y = x + v *\<^sub>R i"
    have ge:"y \<ge> x"
      using y_value i unfolding y_value
      by (simp add: v(2) zero_le_scaleR_iff)
    have "y \<noteq> x"
      using y_value i unfolding y_value
      using v(2) by auto
    hence y_str_g_x : "y > x"
      using ge by auto
    have y_in: "y \<in> carrier"
      using assms(1) x_in y_str_g_x by blast
    then have y_pref_x : "y \<succ>[relation] x"
      using y_str_g_x x_in mono monotone_preference_def  by blast
    hence " norm (y - x) \<le> e"
      using \<open>0 < v\<close> y_value y_value i v by auto
    hence dist_less_e : "dist y x \<le> e"
      by (simp add: dist_norm)
    thus ?thesis
      using y_pref_x dist_less_e y_in by blast
  qed
qed

end