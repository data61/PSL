(*<*)
theory Quorums
imports Consensus_Types
begin
(*>*)

subsection \<open>Quorums\<close>
(******************************************************************************)


locale quorum = 
  fixes Quorum :: "'a set set"
  assumes 
    qintersect: "\<lbrakk> Q \<in> Quorum; Q' \<in> Quorum \<rbrakk> \<Longrightarrow> Q \<inter> Q' \<noteq> {}"
    \<comment> \<open>Non-emptiness needed for some invariants of Coordinated Voting\<close>
    and Quorum_not_empty: "\<exists>Q. Q \<in> Quorum"

lemma (in quorum) quorum_non_empty: "Q \<in> Quorum \<Longrightarrow> Q \<noteq> {}"
by (auto dest: qintersect)

lemma (in quorum) empty_not_quorum: "{} \<in> Quorum \<Longrightarrow> False"
  using quorum_non_empty
  by blast

locale quorum_process = quorum Quorum
  for Quorum :: "process set set"

locale mono_quorum = quorum_process +
  assumes mono_quorum: "\<lbrakk> Q \<in> Quorum; Q \<subseteq> Q' \<rbrakk> \<Longrightarrow> Q' \<in> Quorum"

lemma (in mono_quorum) UNIV_quorum:
  "UNIV \<in> Quorum"
  using Quorum_not_empty mono_quorum
  by(blast)

definition majs :: "(process set) set" where
  "majs \<equiv> {S. card S > N div 2}"

lemma majsI:
  "N div 2 < card S \<Longrightarrow> S \<in> majs"
  by(simp add: majs_def)

lemma card_Compl:
  fixes S :: "('a :: finite) set"
  shows "card (-S) = card (UNIV :: 'a set) - card S"
proof-
  have "card S + card (-S) = card (UNIV :: 'a set)"
    by(rule card_Un_disjoint[of S "-S", simplified Compl_partition, symmetric])
      (auto)
  thus ?thesis
    by simp
qed

lemma majorities_intersect:
  "card (Q :: process set) + card Q' > N \<Longrightarrow> Q \<inter> Q' \<noteq> {}"
  by (metis card_Un_disjoint card_mono finite not_le top_greatest)

interpretation majorities: mono_quorum majs
proof
  fix Q Q' assume "Q \<in> majs" "Q' \<in> majs"
  thus "Q \<inter> Q' \<noteq> {}"
    by (intro majorities_intersect) (auto simp add: majs_def)
next
  show "\<exists>Q. Q \<in> majs" 
    apply(rule_tac x=UNIV in exI)
    apply(auto simp add: majs_def intro!: div_less_dividend finite_UNIV_card_ge_0)
    done
next
  fix Q Q'
  assume "Q \<in> majs" "Q \<subseteq> Q'"
  thus "Q' \<in> majs" using card_mono[OF _ \<open>Q \<subseteq> Q'\<close>]
    by(auto simp add: majs_def)
qed

end
