section \<open>Many-Typed (Many-Sorted) First-Order Logic\<close>
theory Sig imports Preliminaries
begin

text\<open>In this formalization, we call ``types" what the first-order logic community usually calls ``sorts".\<close> 


subsection\<open>Signatures\<close> 

locale Signature =
fixes
    wtFsym :: "'fsym \<Rightarrow> bool"
and wtPsym :: "'psym \<Rightarrow> bool"
and arOf :: "'fsym \<Rightarrow> 'tp list"
and resOf :: "'fsym \<Rightarrow> 'tp"
and parOf :: "'psym \<Rightarrow> 'tp list"
assumes
    countable_tp: "countable (UNIV :: 'tp set)"
and countable_wtFsym: "countable {f::'fsym. wtFsym f}"
and countable_wtPsym: "countable {p::'psym. wtPsym p}"
begin

text\<open>Partitioning of the variables in countable sets for each type:\<close>

definition tpOfV_pred :: "(var \<Rightarrow> 'tp) \<Rightarrow> bool" where
"tpOfV_pred f \<equiv> \<forall> \<sigma>. infinite (f -` {\<sigma>})"

definition "tpOfV \<equiv> SOME f. tpOfV_pred f"

lemma infinite_fst_vimage:
"infinite ((fst :: 'a \<times> nat \<Rightarrow> 'a) -` {a})" (is "infinite (?f -` {a})")
proof-
  have "?f -` {a} = {(a,n::nat) | n . True}" (is "_ = ?A") by auto
  moreover
  {have 0: "?A = range (Pair a)" by auto
   have "infinite ?A" unfolding 0 apply(rule range_inj_infinite)
   unfolding inj_on_def by auto
  }
  ultimately show ?thesis by auto
qed

lemma tpOfV_pred: "\<exists> f. tpOfV_pred f"
proof-
  define Ut Uv where "Ut = (UNIV :: 'tp set)" and "Uv = (UNIV :: var set)"
  define Unt where "Unt = (UNIV :: nat set)"
  define U2 where "U2 = (UNIV :: ('tp \<times> nat) set)"
  have U2: "U2 \<equiv> Ut \<times> Unt" unfolding Ut_def Unt_def U2_def UNIV_Times_UNIV .
  have "|U2| =o |Unt \<times> Ut|" unfolding U2 by (metis card_of_Times_commute)
  also have "|Unt \<times> Ut| =o |Unt|"
  apply(rule card_of_Times_infinite_simps(1)) unfolding Ut_def Unt_def
  apply (metis nat_not_finite)
  apply (metis UNIV_not_empty)
  by (metis countable_card_of_nat countable_tp)
  also have "|Unt| =o |Uv|" apply(rule ordIso_symmetric)
  unfolding Unt_def Uv_def using card_of_var card_of_nat[THEN ordIso_symmetric]
  by(rule ordIso_transitive)
  finally have "|U2| =o |Uv|" .
  hence "|Uv| =o |U2|" by(rule ordIso_symmetric)
  then obtain g where g: "bij_betw g Uv U2" unfolding card_of_ordIso[symmetric] by blast
  show ?thesis apply(rule exI[of _ "fst o g"]) unfolding tpOfV_pred_def apply safe
  unfolding vimage_comp [symmetric] apply (drule finite_vimageD)
  using g unfolding bij_betw_def Uv_def U2_def by (auto simp: infinite_fst_vimage)
qed

lemma tpOfV_pred_tpOfV: "tpOfV_pred tpOfV"
using tpOfV_pred unfolding tpOfV_def by (rule someI_ex)

lemma tpOfV: "infinite (tpOfV -` {\<sigma>})"
using tpOfV_pred_tpOfV unfolding tpOfV_pred_def by auto

definition "tpart1 V \<equiv> \<Union> \<sigma>. part1 (V \<inter> tpOfV -` {\<sigma>})"
definition "tpart2 V \<equiv> \<Union> \<sigma>. part2 (V \<inter> tpOfV -` {\<sigma>})"
definition "tinfinite V \<equiv> \<forall> \<sigma>. infinite (V \<inter> tpOfV -` {\<sigma>})"

lemma tinfinite_var[simp,intro]: "tinfinite (UNIV :: var set)"
unfolding tinfinite_def using tpOfV by auto

lemma tinifnite_singl[simp]:
assumes "tinfinite V"  shows "tinfinite (V - {x})"
unfolding tinfinite_def proof safe
  fix \<sigma> assume 0: "finite ((V - {x}) \<inter> tpOfV -` {\<sigma>})"
  have "finite ((V \<inter> tpOfV -` {\<sigma>}) - {x})" apply(rule finite_subset[OF _ 0]) by auto
  thus False using assms unfolding tinfinite_def by auto
qed

lemma tpart1_Un_tpart2[simp]:
assumes "tinfinite V" shows "tpart1 V \<union> tpart2 V = V"
using assms part1_Un_part2 unfolding tinfinite_def tpart1_def tpart2_def
unfolding UN_Un_distrib[symmetric] by blast

lemma tpart1_Int_tpart2[simp]:
assumes "tinfinite V" shows "tpart1 V \<inter> tpart2 V = {}"
using assms part1_Int_part2 unfolding tinfinite_def tpart1_def tpart2_def
unfolding Int_UN_distrib2 apply auto apply (case_tac "xa = xb", auto)
using part1_su part2_su by blast (* fixme: clean proof *)

lemma tpart1_su:
assumes "tinfinite V"  shows "tpart1 V \<subseteq> V"
using assms unfolding tinfinite_def tpart1_def
using part1_su by (auto intro: UN_least)

lemma tpart1_in:
assumes "tinfinite V" and "x \<in> tpart1 V" shows "x \<in> V"
using assms tpart1_su by auto

lemma tinfinite_tpart1[simp]:
assumes "tinfinite V"
shows "tinfinite (tpart1 V)"
unfolding tinfinite_def tpart1_def proof safe
  fix \<sigma> assume
  "finite ((\<Union>\<sigma>'. part1 (V \<inter> tpOfV -` {\<sigma>'})) \<inter> tpOfV -` {\<sigma>})" (is "finite ?A")
  moreover have "?A = part1 (V \<inter> tpOfV -` {\<sigma>})"
  using assms part1_su unfolding tinfinite_def by auto
  moreover have "infinite ..."
  using assms infinite_part1 unfolding tinfinite_def by auto
  ultimately show False by auto
qed

lemma tinfinite_tpart2[simp]:
assumes "tinfinite V"
shows "tinfinite (tpart2 V)"
unfolding tinfinite_def tpart2_def proof safe
  fix \<sigma> assume
  "finite ((\<Union>\<sigma>'. part2 (V \<inter> tpOfV -` {\<sigma>'})) \<inter> tpOfV -` {\<sigma>})" (is "finite ?A")
  moreover have "?A = part2 (V \<inter> tpOfV -` {\<sigma>})"
  using assms part2_su unfolding tinfinite_def by auto
  moreover have "infinite ..."
  using assms infinite_part2 unfolding tinfinite_def by auto
  ultimately show False by auto
qed

lemma tpart2_su:
assumes "tinfinite V"  shows "tpart2 V \<subseteq> V"
using assms unfolding tinfinite_def tpart2_def
using part2_su by (auto intro: UN_least)

lemma tpart2_in:
assumes "tinfinite V" and "x \<in> tpart2 V" shows "x \<in> V"
using assms tpart2_su by auto

text\<open>Typed-pick: picking a variable of a given type\<close>

definition "tpick \<sigma> V \<equiv> pick (V \<inter> tpOfV -` {\<sigma>})"

lemma tinfinite_ex: "tinfinite V \<Longrightarrow> \<exists> x \<in> V. tpOfV x = \<sigma>"
unfolding tinfinite_def using infinite_imp_nonempty by auto

lemma tpick: assumes "tinfinite V" shows "tpick \<sigma> V \<in> V \<inter> tpOfV -` {\<sigma>}"
proof-
  obtain x where "x \<in> V \<and> tpOfV x = \<sigma>"
  using tinfinite_ex[OF assms] by auto
  hence "x \<in> V \<inter> tpOfV -` {\<sigma>}" by blast
  thus ?thesis unfolding tpick_def by (rule pick)
qed

lemma tpick_in[simp]: "tinfinite V \<Longrightarrow> tpick \<sigma> V \<in> V"
and tpOfV_tpick[simp]: "tinfinite V \<Longrightarrow> tpOfV (tpick \<sigma> V) = \<sigma>"
using tpick by auto

lemma finite_tinfinite:
assumes "finite V"
shows "tinfinite (UNIV - V)"
using assms infinite_var unfolding tinfinite_def
by (metis Diff_Int2 Diff_Int_distrib2 Int_UNIV_left finite_Diff2 tpOfV)

(* get variable terms for the given types: *)
fun getVars where
"getVars [] = []"
|
"getVars (\<sigma> # \<sigma>l) =
 (let xl = getVars \<sigma>l in (tpick \<sigma> (UNIV - set xl)) # xl)"

lemma distinct_getVars: "distinct (getVars \<sigma>l)"
using tpick_in[OF finite_tinfinite] by (induct \<sigma>l, auto simp: Let_def)

lemma length_getVars[simp]: "length (getVars \<sigma>l) = length \<sigma>l"
by(induct \<sigma>l, auto simp: Let_def)

lemma map_tpOfV_getVars[simp]: "map tpOfV (getVars \<sigma>l) = \<sigma>l"
using tpOfV_tpick[OF finite_tinfinite] by (induct \<sigma>l, auto simp: Let_def)

lemma tpOfV_getVars_nth[simp]:
assumes "i < length \<sigma>l"  shows "tpOfV (getVars \<sigma>l ! i) = \<sigma>l ! i"
using assms using map_tpOfV_getVars by (metis length_getVars nth_map)


end (* context Signature *)


end
