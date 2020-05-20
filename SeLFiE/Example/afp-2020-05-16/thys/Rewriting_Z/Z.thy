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

section \<open>The Z property\<close>

theory Z
imports "Abstract-Rewriting.Abstract_Rewriting"
begin

locale z_property =
  fixes bullet :: "'a \<Rightarrow> 'a" ("_\<^sup>\<bullet>" [1000] 1000)
  and R :: "'a rel"
  assumes Z: "(a, b) \<in> R \<Longrightarrow> (b, a\<^sup>\<bullet>) \<in> R\<^sup>* \<and> (a\<^sup>\<bullet>, b\<^sup>\<bullet>) \<in> R\<^sup>*"
begin

lemma monotonicity:
  assumes "(a, b) \<in> R\<^sup>*"
  shows "(a\<^sup>\<bullet>, b\<^sup>\<bullet>) \<in> R\<^sup>*"
using assms
by (induct) (auto dest: Z)

lemma semi_confluence:
  shows "(R\<inverse> O R\<^sup>*) \<subseteq> R\<^sup>\<down>"
proof (intro subrelI, elim relcompEpair, drule converseD)
  fix d a c
  assume "(a, c) \<in> R\<^sup>*" and "(a, d) \<in> R"
  then show "(d, c) \<in> R\<^sup>\<down>"
  proof (cases)
    case (step b)
    then have "(a\<^sup>\<bullet>, b\<^sup>\<bullet>) \<in> R\<^sup>*" by (auto simp: monotonicity)
    then have "(d, b\<^sup>\<bullet>) \<in> R\<^sup>*" using \<open>(a, d) \<in> R\<close> by (auto dest: Z)
    then show ?thesis using \<open>(b, c) \<in> R\<close> by (auto dest: Z)
  qed auto
qed

lemma CR: "CR R"
by (intro semi_confluence_imp_CR semi_confluence)

definition "R\<^sub>d = {(a, b). (a, b) \<in> R\<^sup>* \<and> (b, a\<^sup>\<bullet>) \<in> R\<^sup>*}"

end

locale angle_property =
  fixes bullet :: "'a \<Rightarrow> 'a" ("_\<^sup>\<bullet>" [1000] 1000)
  and R :: "'a rel"
  and R\<^sub>d :: "'a rel"
  assumes intermediate: "R \<subseteq> R\<^sub>d" "R\<^sub>d \<subseteq> R\<^sup>*"
  and angle: "(a, b) \<in> R\<^sub>d \<Longrightarrow> (b, a\<^sup>\<bullet>) \<in> R\<^sub>d"

sublocale angle_property \<subseteq> z_property
proof
  fix a b
  assume "(a, b) \<in> R"
  with angle intermediate have "(b, a\<^sup>\<bullet>) \<in> R\<^sub>d" and "(a\<^sup>\<bullet>, b\<^sup>\<bullet>) \<in> R\<^sub>d" by auto
  then show "(b, a\<^sup>\<bullet>) \<in> R\<^sup>* \<and> (a\<^sup>\<bullet>, b\<^sup>\<bullet>) \<in> R\<^sup>*" using intermediate by auto
qed

sublocale z_property \<subseteq> angle_property bullet R "z_property.R\<^sub>d bullet R"
proof
  show "R \<subseteq> R\<^sub>d" and "R\<^sub>d \<subseteq> R\<^sup>*" unfolding R\<^sub>d_def using Z by auto
  fix a b
  assume "(a, b) \<in> R\<^sub>d"
  then show "(b, a\<^sup>\<bullet>) \<in> R\<^sub>d" using monotonicity unfolding R\<^sub>d_def by auto
qed

end
