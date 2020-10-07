(*
Author:  Christian Sternagel <c.sternagel@gmail.com>
Author:  René Thiemann <rene.thiemann@uibk.ac.at>
License: LGPL
*)
section \<open>Abstract Matching\<close>

theory Abstract_Matching
  imports
    Term_Pair_Multiset
    "Abstract-Rewriting.Abstract_Rewriting"
begin

(*FIXME: move(?)*)
lemma singleton_eq_union_iff [iff]:
  "{#x#} = M + {#y#} \<longleftrightarrow> M = {#} \<and> x = y"
  by (metis multi_self_add_other_not_self single_eq_single single_is_union)

text \<open>Turning functional maps into substitutions.\<close>
definition "subst_of_map d \<sigma> x =
  (case \<sigma> x of
    None \<Rightarrow> d x
  | Some t \<Rightarrow> t)"

lemma size_mset_mset_less [simp]:
  assumes "length ss = length ts"
  shows "size_mset (mset (zip ss ts)) < 3 + (size_list size ss + size_list size ts)"
  using assms by (induct ss ts rule: list_induct2) (auto simp: pair_size_def)

definition matchers :: "(('f, 'v) term \<times> ('f, 'w) term) set \<Rightarrow> ('f, 'v, 'w) gsubst set"
  where
    "matchers P = {\<sigma>. \<forall>e\<in>P. fst e \<cdot> \<sigma> = snd e}"

lemma matchers_vars_term_eq:
  assumes "\<sigma> \<in> matchers P" and "\<tau> \<in> matchers P"
    and "(s, t) \<in> P"
  shows "\<forall>x\<in>vars_term s. \<sigma> x = \<tau> x"
  using assms unfolding term_subst_eq_conv [symmetric] by (force simp: matchers_def)

lemma matchers_empty [simp]:
  "matchers {} = UNIV"
  by (simp add: matchers_def)

lemma matchers_insert [simp]:
  "matchers (insert e P) = {\<sigma>. fst e \<cdot> \<sigma> = snd e} \<inter> matchers P"
  by (auto simp: matchers_def)

lemma matchers_Un [simp]:
  "matchers (P \<union> P') = matchers P \<inter> matchers P'"
  by (auto simp: matchers_def)

lemma matchers_set_zip [simp]:
  assumes "length ss = length ts"
  shows "matchers (set (zip ss ts)) = {\<sigma>. map (\<lambda>t. t \<cdot> \<sigma>) ss = ts}"
  using assms by (induct ss ts rule: list_induct2) auto

definition "matchers_map m = matchers ((\<lambda>x. (Var x, the (m x))) ` Map.dom m)"

lemma matchers_map_empty [simp]:
  "matchers_map Map.empty = UNIV"
  by (simp add: matchers_map_def)

lemma matchers_map_upd [simp]:
  assumes "\<sigma> x = None \<or> \<sigma> x = Some t"
  shows "matchers_map (\<lambda>y. if y = x then Some t else \<sigma> y) =
    matchers_map \<sigma> \<inter> {\<tau>. \<tau> x = t}" (is "?L = ?R")
proof
  show "?L \<supseteq> ?R" by (auto simp: matchers_map_def matchers_def)
next
  show "?L \<subseteq> ?R"
    by (rule subsetI)
       (insert assms, auto simp: matchers_map_def matchers_def dom_def)
qed

lemma matchers_map_upd' [simp]:
  assumes "\<sigma> x = None \<or> \<sigma> x = Some t"
  shows "matchers_map (\<sigma> (x \<mapsto> t)) = matchers_map \<sigma> \<inter> {\<tau>. \<tau> x = t}"
  using matchers_map_upd [of \<sigma> x t, OF assms]
  by (simp add: matchers_map_def matchers_def dom_def)

inductive MATCH1 where
  Var [intro!, simp]: "\<sigma> x = None \<or> \<sigma> x = Some t \<Longrightarrow>
    MATCH1 (P + {#(Var x, t)#}, \<sigma>) (P, \<sigma> (x \<mapsto> t))" |
  Fun [intro]: "length ss = length ts \<Longrightarrow>
    MATCH1 (P + {#(Fun f ss, Fun f ts)#}, \<sigma>) (P + mset (zip ss ts), \<sigma>)"
  
lemma MATCH1_matchers [simp]:
  assumes "MATCH1 x y"
  shows "matchers_map (snd x) \<inter> matchers (set_mset (fst x)) =
    matchers_map (snd y) \<inter> matchers (set_mset (fst y))"
  using assms by (induct) (simp_all add: ac_simps)

definition "matchrel = {(x, y). MATCH1 x y}"

lemma MATCH1_matchrel_conv:
  "MATCH1 x y \<longleftrightarrow> (x, y) \<in> matchrel"
  by (simp add: matchrel_def)

lemma matchrel_rtrancl_matchers [simp]:
  assumes "(x, y) \<in> matchrel\<^sup>*"
  shows "matchers_map (snd x) \<inter> matchers (set_mset (fst x)) =
    matchers_map (snd y) \<inter> matchers (set_mset (fst y))"
  using assms by (induct) (simp_all add: matchrel_def)

lemma subst_of_map_in_matchers_map [simp]:
  "subst_of_map d m \<in> matchers_map m"
  by (auto simp: subst_of_map_def [abs_def] matchers_map_def matchers_def)

lemma matchrel_sound:
  assumes "((P, Map.empty), ({#}, \<sigma>)) \<in> matchrel\<^sup>*"
  shows "subst_of_map d \<sigma> \<in> matchers (set_mset P)"
  using matchrel_rtrancl_matchers [OF assms] by simp

lemma MATCH1_size_mset:
  assumes "MATCH1 x y"
  shows "size_mset (fst x) > size_mset (fst y)"
  using assms by (cases) (auto simp: pair_size_def)+

definition "matchless = inv_image (measure size_mset) fst"

lemma wf_matchless:
  "wf matchless"
  by (auto simp: matchless_def)

lemma MATCH1_matchless:
  assumes "MATCH1 x y"
  shows "(y, x) \<in> matchless"
  using MATCH1_size_mset [OF assms]
  by (simp add: matchless_def)

lemma converse_matchrel_subset_matchless:
  "matchrel\<inverse> \<subseteq> matchless"
  using MATCH1_matchless by (auto simp: matchrel_def)

lemma wf_converse_matchrel:
  "wf (matchrel\<inverse>)"
  by (rule wf_subset [OF wf_matchless converse_matchrel_subset_matchless])

lemma MATCH1_singleton_Var [intro]:
  "\<sigma> x = None \<Longrightarrow> MATCH1 ({#(Var x, t)#}, \<sigma>) ({#}, \<sigma> (x \<mapsto> t))"
  "\<sigma> x = Some t \<Longrightarrow> MATCH1 ({#(Var x, t)#}, \<sigma>) ({#}, \<sigma> (x \<mapsto> t))"
  using MATCH1.Var [of \<sigma> x t "{#}"] by simp_all

lemma MATCH1_singleton_Fun [intro]:
  "length ss = length ts \<Longrightarrow> MATCH1 ({#(Fun f ss, Fun f ts)#}, \<sigma>) (mset (zip ss ts), \<sigma>)"
  using MATCH1.Fun [of ss ts "{#}" f \<sigma>] by simp

lemma not_MATCH1_singleton_Var [dest]:
  "\<not> MATCH1 ({#(Var x, t)#}, \<sigma>) ({#}, \<sigma> (x \<mapsto> t)) \<Longrightarrow> \<sigma> x \<noteq> None \<and> \<sigma> x \<noteq> Some t"
  by auto

lemma not_matchrelD:
  assumes "\<not> (\<exists>y. (({#e#}, \<sigma>), y) \<in> matchrel)"
  shows "(\<exists>f ss x. e = (Fun f ss, Var x)) \<or>
    (\<exists>x t. e = (Var x, t) \<and> \<sigma> x \<noteq> None \<and> \<sigma> x \<noteq> Some t) \<or>
    (\<exists>f g ss ts. e = (Fun f ss, Fun g ts) \<and> (f \<noteq> g \<or> length ss \<noteq> length ts))"
proof (rule ccontr)
  assume *: "\<not> ?thesis"
  show False
  proof (cases e)
    case (Pair s t)
    with assms and * show ?thesis
      by (cases s) (cases t, auto simp: matchrel_def)+
  qed
qed

lemma ne_matchers_imp_matchrel:
  assumes "matchers_map \<sigma> \<inter> matchers {e} \<noteq> {}"
  shows "\<exists>y. (({#e#}, \<sigma>), y) \<in> matchrel"
proof (rule ccontr)
  assume "\<not> ?thesis"
  from not_matchrelD [OF this] and assms
    show False by (auto simp: matchers_map_def matchers_def dom_def)
qed

lemma MATCH1_mono:
  assumes "MATCH1 (P, \<sigma>) (P', \<sigma>')"
  shows "MATCH1 (P + M, \<sigma>) (P' + M, \<sigma>')"
  using assms apply (cases) apply (auto simp: ac_simps)
  using Var apply force
  using Var apply force
  using Fun
  by (metis (no_types, lifting) add.assoc add_mset_add_single)

lemma matchrel_mono:
  assumes "(x, y) \<in> matchrel"
  shows "((fst x + M, snd x), (fst y + M, snd y)) \<in> matchrel"
  using assms and MATCH1_mono [of "fst x"]
  by (simp add: MATCH1_matchrel_conv)

lemma matchrel_rtrancl_mono:
  assumes "(x, y) \<in> matchrel\<^sup>*"
  shows "((fst x + M, snd x), (fst y + M, snd y)) \<in> matchrel\<^sup>*"
  using assms by (induct) (auto dest:  matchrel_mono [of _ _ M])

lemma ne_matchers_imp_empty_or_matchrel:
  assumes "matchers_map \<sigma> \<inter> matchers (set_mset P) \<noteq> {}"
  shows "P = {#} \<or> (\<exists>y. ((P, \<sigma>), y) \<in> matchrel)"
proof (cases P)
  case (add e P')
  then have [simp]: "P = P' + {#e#}" by simp
  from assms have "matchers_map \<sigma> \<inter> matchers {e} \<noteq> {}" by auto
  from ne_matchers_imp_matchrel [OF this]
    obtain P'' \<sigma>' where "MATCH1 ({#e#}, \<sigma>) (P'', \<sigma>')"
    by (auto simp: matchrel_def)
  from MATCH1_mono [OF this, of P'] have "MATCH1 (P, \<sigma>) (P' + P'', \<sigma>')" by (simp add: ac_simps)
  then show ?thesis by (auto simp: matchrel_def)
qed simp

lemma matchrel_imp_converse_matchless [dest]:
  "(x, y) \<in> matchrel \<Longrightarrow> (y, x) \<in> matchless"
  using MATCH1_matchless by (cases x, cases y) (auto simp: matchrel_def)

lemma ne_matchers_imp_empty:
  fixes P :: "(('f, 'v) term \<times> ('f, 'w) term) multiset"
  assumes "matchers_map \<sigma> \<inter> matchers (set_mset P) \<noteq> {}"
  shows "\<exists>\<sigma>'. ((P, \<sigma>), ({#}, \<sigma>')) \<in> matchrel\<^sup>*"
using assms
proof (induct P arbitrary: \<sigma> rule: wf_induct [OF wf_measure [of size_mset]])
  fix P :: "(('f, 'v) term \<times> ('f, 'w) term) multiset"
    and \<sigma>
  presume IH: "\<And>P' \<sigma>. \<lbrakk>(P', P) \<in> measure size_mset; matchers_map \<sigma> \<inter> matchers (set_mset P') \<noteq> {}\<rbrakk> \<Longrightarrow>
    \<exists>\<sigma>'. ((P', \<sigma>), {#}, \<sigma>') \<in> matchrel\<^sup>*"
    and *: "matchers_map \<sigma> \<inter> matchers (set_mset P) \<noteq> {}"
  show "\<exists>\<sigma>'. ((P, \<sigma>), {#}, \<sigma>') \<in> matchrel\<^sup>*"
  proof (cases "P = {#}")
    assume "P \<noteq> {#}"
    with ne_matchers_imp_empty_or_matchrel [OF *]
      obtain P' \<sigma>' where **: "((P, \<sigma>), (P', \<sigma>')) \<in> matchrel" by (auto)
    with * have "(P', P) \<in> measure size_mset"
      and "matchers_map \<sigma>' \<inter> matchers (set_mset P') \<noteq> {}"
      using MATCH1_matchers [of "(P, \<sigma>)" "(P', \<sigma>')"]
      by (auto simp: matchrel_def dest: MATCH1_size_mset)
    from IH [OF this] and **
      show ?thesis by (auto intro: converse_rtrancl_into_rtrancl)
  qed force
qed simp

lemma empty_not_reachable_imp_matchers_empty:
  assumes "\<And>\<sigma>'. ((P, \<sigma>), ({#}, \<sigma>')) \<notin> matchrel\<^sup>*"
  shows "matchers_map \<sigma> \<inter> matchers (set_mset P) = {}"
  using ne_matchers_imp_empty [of \<sigma> P] and assms by blast

lemma irreducible_reachable_imp_matchers_empty:
  assumes "((P, \<sigma>), y) \<in> matchrel\<^sup>!" and "fst y \<noteq> {#}"
  shows "matchers_map \<sigma> \<inter> matchers (set_mset P) = {}"
proof -
  have "((P, \<sigma>), y) \<in> matchrel\<^sup>*"
    and "\<And>\<tau>. (y, ({#}, \<tau>)) \<notin> matchrel\<^sup>*"
    using assms by  auto (metis NF_not_suc fst_conv normalizability_E)
  moreover with empty_not_reachable_imp_matchers_empty
    have "matchers_map (snd y) \<inter> matchers (set_mset (fst y)) = {}" by (cases y) auto
  ultimately show ?thesis using matchrel_rtrancl_matchers [of "(P, \<sigma>)"] by simp
qed

lemma matchers_map_not_empty [simp]:
  "matchers_map \<sigma> \<noteq> {}"
  "{} \<noteq> matchers_map \<sigma>"
  by (auto simp: matchers_map_def matchers_def)

lemma matchers_empty_imp_not_empty_NF:
  assumes "matchers (set_mset P) = {}"
  shows "\<exists>y. fst y \<noteq> {#} \<and> ((P, Map.empty), y) \<in> matchrel\<^sup>!"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have *: "\<And>y. ((P, Map.empty), y) \<in> matchrel\<^sup>! \<Longrightarrow> fst y = {#}" by auto
  have "SN matchrel" using wf_converse_matchrel by (auto simp: SN_iff_wf)
  then obtain y where "((P, Map.empty), y) \<in> matchrel\<^sup>!"
    by (metis SN_imp_WN UNIV_I WN_onE)
  with * [OF this] obtain \<tau> where "((P, Map.empty), ({#}, \<tau>)) \<in> matchrel\<^sup>*" by (cases y) auto
  from matchrel_rtrancl_matchers [OF this] and assms
    show False by simp
qed

end
