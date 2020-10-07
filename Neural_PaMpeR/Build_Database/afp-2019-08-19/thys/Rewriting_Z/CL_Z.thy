(*
 * Title:      Z  
 * Author:     Bertram Felgenhauer (2016)
 * Author:     Julian Nagele (2016)
 * Author:     Vincent van Oostrom (2016)
 * Author:     Christian Sternagel (2016)
 * Maintainer: Bertram Felgenhauer <bertram.felgenhauer@uibk.ac.at>
 * Maintainer: Juilan Nagele <julian.nagele@uibk.ac.at>
 * Maintainer: Christian Sternagel <c.sternagel@gmail.com>
 * License:    BSD
 *)

section \<open>Combinatory Logic has the Church-Rosser property\<close>

theory CL_Z imports Z
begin

datatype CL = S | K | I | App CL CL ("` _ _" [999, 999] 999)

inductive_set red :: "CL rel" where
  L: "(t, t') \<in> red \<Longrightarrow> (` t u, ` t' u) \<in> red"
| R: "(u, u') \<in> red \<Longrightarrow> (` t u, ` t u') \<in> red"
| S: "(` ` ` S x y z, ` ` x z ` y z) \<in> red"
| K: "(` ` K x y, x) \<in> red"
| I: "(` I x, x) \<in> red"

lemma App_mono:
  "(t, t') \<in> red\<^sup>* \<Longrightarrow> (u, u') \<in> red\<^sup>* \<Longrightarrow> (` t u, ` t' u') \<in> red\<^sup>*"
proof -
  assume "(t, t') \<in> red\<^sup>*" hence "(` t u, ` t' u) \<in> red\<^sup>*"
    by (induct t' rule: rtrancl_induct) (auto intro: rtrancl_into_rtrancl red.intros)
  moreover assume "(u, u') \<in> red\<^sup>*" hence "(` t' u, ` t' u') \<in> red\<^sup>*"
    by (induct u' rule: rtrancl_induct) (auto intro: rtrancl_into_rtrancl red.intros)
  ultimately show ?thesis by auto
qed

fun bullet_app :: "CL \<Rightarrow> CL \<Rightarrow> CL" where
  "bullet_app (` ` S x y) z = ` ` x z ` y z"
| "bullet_app (` K x) y = x"
| "bullet_app I x = x"
| "bullet_app t u = ` t u"

lemma bullet_app_red:
  "(` t u, bullet_app t u) \<in> red\<^sup>="
by (induct t u rule: bullet_app.induct) (auto intro: red.intros)

lemma bullet_app_redsI:
  "(s, ` t u) \<in> red\<^sup>* \<Longrightarrow> (s, bullet_app t u) \<in> red\<^sup>*"
using bullet_app_red[of t u] by auto

lemma bullet_app_redL:
  "(t, t') \<in> red \<Longrightarrow> (bullet_app t u, bullet_app t' u) \<in> red\<^sup>*"
by (induct t u rule: bullet_app.induct)
   (auto 0 6 intro: App_mono bullet_app_redsI elim: red.cases simp only: bullet_app.simps)

lemma bullet_app_redR:
  "(u, u') \<in> red \<Longrightarrow> (bullet_app t u, bullet_app t u') \<in> red\<^sup>*"
by (induct t u rule: bullet_app.induct) (auto intro: App_mono)

lemma bullet_app_mono:
  assumes "(t, t') \<in> red\<^sup>*" "(u, u') \<in> red\<^sup>*" shows "(bullet_app t u, bullet_app t' u') \<in> red\<^sup>*"
proof -
  have "(bullet_app t u, bullet_app t' u) \<in> red\<^sup>*" using assms(1)
    by (induct t' rule: rtrancl_induct) (auto intro: rtrancl_trans bullet_app_redL)
  moreover have "(bullet_app t' u, bullet_app t' u') \<in> red\<^sup>*" using assms(2)
    by (induct u' rule: rtrancl_induct) (auto intro: rtrancl_trans bullet_app_redR)
  ultimately show ?thesis by auto
qed

fun bullet :: "CL \<Rightarrow> CL" where
  "bullet (` t u) = bullet_app (bullet t) (bullet u)"
| "bullet t = t"

lemma bullet_incremental:
  "(t, bullet t) \<in> red\<^sup>*"
by (induct t rule: bullet.induct) (auto intro: App_mono bullet_app_redsI)

interpretation CL:z_property bullet red
proof (unfold_locales, intro conjI)
  fix t u assume "(t, u) \<in> red" thus "(u, bullet t) \<in> red\<^sup>*"
  proof (induct t arbitrary: u rule: bullet.induct)
    case (1 t1 t2) show ?case using 1(3)
      by (cases) (auto intro: 1 App_mono bullet_app_redsI bullet_incremental)
  qed (auto elim: red.cases)
next
  fix t u assume "(t, u) \<in> red" thus "(bullet t, bullet u) \<in> red\<^sup>*"
    by (induct t u rule: red.induct) (auto intro: App_mono bullet_app_mono bullet_app_redsI)
qed

lemmas CR_red = CL.CR

end
