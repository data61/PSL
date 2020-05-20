(* Author: Joshua Schneider, ETH Zurich *)

section \<open>Formalisation of idiomatic terms and lifting\<close>

subsection \<open>Immediate joinability under a relation\<close>

theory Joinable
imports Main
begin

subsubsection \<open>Definition and basic properties\<close>

definition joinable :: "('a \<times> 'b) set \<Rightarrow> ('a \<times> 'a) set"
where "joinable R = {(x, y). \<exists>z. (x, z) \<in> R \<and> (y, z) \<in> R}"

lemma joinable_simp: "(x, y) \<in> joinable R \<longleftrightarrow> (\<exists>z. (x, z) \<in> R \<and> (y, z) \<in> R)"
unfolding joinable_def by simp

lemma joinableI: "(x, z) \<in> R \<Longrightarrow> (y, z) \<in> R \<Longrightarrow> (x, y) \<in> joinable R"
unfolding joinable_simp by blast

lemma joinableD: "(x, y) \<in> joinable R \<Longrightarrow> \<exists>z. (x, z) \<in> R \<and> (y, z) \<in> R"
unfolding joinable_simp .

lemma joinableE:
  assumes "(x, y) \<in> joinable R"
  obtains z where "(x, z) \<in> R" and "(y, z) \<in> R"
using assms unfolding joinable_simp by blast

lemma refl_on_joinable: "refl_on {x. \<exists>y. (x, y) \<in> R} (joinable R)"
by (auto intro!: refl_onI simp only: joinable_simp)

lemma refl_joinable_iff: "(\<forall>x. \<exists>y. (x, y) \<in> R) = refl (joinable R)"
by (auto intro!: refl_onI dest: refl_onD simp add: joinable_simp)

lemma refl_joinable: "refl R \<Longrightarrow> refl (joinable R)"
using refl_joinable_iff by (blast dest: refl_onD)

lemma joinable_refl: "refl R \<Longrightarrow> (x, x) \<in> joinable R"
using refl_joinable by (blast dest: refl_onD)

lemma sym_joinable: "sym (joinable R)"
by (auto intro!: symI simp only: joinable_simp)

lemma joinable_sym: "(x, y) \<in> joinable R \<Longrightarrow> (y, x) \<in> joinable R"
using sym_joinable by (rule symD)

lemma joinable_mono: "R \<subseteq> S \<Longrightarrow> joinable R \<subseteq> joinable S"
by (rule subrelI) (auto simp only: joinable_simp)

lemma refl_le_joinable:
  assumes "refl R"
  shows "R \<subseteq> joinable R"
proof (rule subrelI)
  fix x y
  assume "(x, y) \<in> R"
  moreover from \<open>refl R\<close> have "(y, y) \<in> R" by (blast dest: refl_onD)
  ultimately show "(x, y) \<in> joinable R" by (rule joinableI)
qed

lemma joinable_subst:
  assumes R_subst: "\<And>x y. (x, y) \<in> R \<Longrightarrow> (P x, P y) \<in> R"
  assumes joinable: "(x, y) \<in> joinable R"
  shows "(P x, P y) \<in> joinable R"
proof -
  from joinable obtain z where xz: "(x, z) \<in> R" and yz: "(y, z) \<in> R" by (rule joinableE)
  from R_subst xz have "(P x, P z) \<in> R" .
  moreover from R_subst yz have "(P y, P z) \<in> R" .
  ultimately show ?thesis by (rule joinableI)
qed


subsubsection \<open>Confluence\<close>

definition confluent :: "'a rel \<Rightarrow> bool"
where "confluent R \<longleftrightarrow> (\<forall>x y y'. (x, y) \<in> R \<and> (x, y') \<in> R \<longrightarrow> (y, y') \<in> joinable R)"

lemma confluentI:
  "(\<And>x y y'. (x, y) \<in> R \<Longrightarrow> (x, y') \<in> R \<Longrightarrow> \<exists>z. (y, z) \<in> R \<and> (y', z) \<in> R) \<Longrightarrow> confluent R"
unfolding confluent_def by (blast intro: joinableI)

lemma confluentD:
  "confluent R \<Longrightarrow> (x, y) \<in> R \<Longrightarrow> (x,y') \<in> R \<Longrightarrow> (y, y') \<in> joinable R"
unfolding confluent_def by blast

lemma confluentE:
  assumes "confluent R" and "(x, y) \<in> R" and "(x, y') \<in> R"
  obtains z where "(y, z) \<in> R" and "(y', z) \<in> R"
using assms unfolding confluent_def by (blast elim: joinableE)

lemma trans_joinable:
  assumes "trans R" and "confluent R"
  shows "trans (joinable R)"
proof (rule transI)
  fix x y z
  assume "(x, y) \<in> joinable R"
  then obtain u where xu: "(x, u) \<in> R" and yu: "(y, u) \<in> R" by (rule joinableE)
  assume "(y, z) \<in> joinable R"
  then obtain v where yv: "(y, v) \<in> R" and zv: "(z, v) \<in> R" by (rule joinableE)
  from yu yv \<open>confluent R\<close> obtain w where uw: "(u, w) \<in> R" and vw: "(v, w) \<in> R"
    by (blast elim: confluentE)
  from xu uw \<open>trans R\<close> have "(x, w) \<in> R" by (blast elim: transE)
  moreover from zv vw \<open>trans R\<close> have "(z, w) \<in> R" by (blast elim: transE)
  ultimately show "(x, z) \<in> joinable R" by (rule joinableI)
qed


subsubsection \<open>Relation to reflexive transitive symmetric closure\<close>

lemma joinable_le_rtscl: "joinable (R\<^sup>*) \<subseteq> (R \<union> R\<inverse>)\<^sup>*"
proof (rule subrelI)
  fix x y
  assume "(x, y) \<in> joinable (R\<^sup>*)"
  then obtain z where xz: "(x, z) \<in> R\<^sup>*" and yz: "(y,z) \<in> R\<^sup>*" by (rule joinableE)
  from xz have "(x, z) \<in> (R \<union> R\<inverse>)\<^sup>*" by (blast intro: in_rtrancl_UnI)
  moreover from yz have "(z, y) \<in> (R \<union> R\<inverse>)\<^sup>*" by (blast intro: in_rtrancl_UnI rtrancl_converseI)
  ultimately show "(x, y) \<in> (R \<union> R\<inverse>)\<^sup>*" by (rule rtrancl_trans)
qed

theorem joinable_eq_rtscl:
  assumes "confluent (R\<^sup>*)"
  shows "joinable (R\<^sup>*) = (R \<union> R\<inverse>)\<^sup>*"
proof
  show "joinable (R\<^sup>*) \<subseteq> (R \<union> R\<inverse>)\<^sup>*" using joinable_le_rtscl .
next
  show "joinable (R\<^sup>*) \<supseteq> (R \<union> R\<inverse>)\<^sup>*" proof (rule subrelI)
    fix x y
    assume "(x, y) \<in> (R \<union> R\<inverse>)\<^sup>*"
    thus "(x, y) \<in> joinable (R\<^sup>*)" proof (induction set: rtrancl)
      case base
      show "(x, x) \<in> joinable (R\<^sup>*)" using joinable_refl refl_rtrancl .
    next
      case (step y z)
      have "R \<subseteq> joinable (R\<^sup>*)" using refl_le_joinable refl_rtrancl by fast
      with \<open>(y, z) \<in> R \<union> R\<inverse>\<close> have "(y, z) \<in> joinable (R\<^sup>*)" using joinable_sym by fast
      with \<open>(x, y) \<in> joinable (R\<^sup>*)\<close> show "(x, z) \<in> joinable (R\<^sup>*)"
        using trans_joinable trans_rtrancl \<open>confluent (R\<^sup>*)\<close> by (blast dest: transD)
    qed
  qed
qed


subsubsection \<open>Predicate version\<close>

definition joinablep :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where "joinablep P x y \<longleftrightarrow> (\<exists>z. P x z \<and> P y z)"

lemma joinablep_joinable[pred_set_conv]:
  "joinablep (\<lambda>x y. (x, y) \<in> R) = (\<lambda>x y. (x, y) \<in> joinable R)"
by (fastforce simp only: joinablep_def joinable_simp)

lemma reflp_joinablep: "reflp P \<Longrightarrow> reflp (joinablep P)"
by (blast intro: reflpI joinable_refl[to_pred] refl_onI[to_pred] dest: reflpD)

lemma joinablep_refl: "reflp P \<Longrightarrow> joinablep P x x"
using reflp_joinablep by (rule reflpD)

lemma reflp_le_joinablep: "reflp P \<Longrightarrow> P \<le> joinablep P"
by (blast intro!: refl_le_joinable[to_pred] refl_onI[to_pred] dest: reflpD)

end
