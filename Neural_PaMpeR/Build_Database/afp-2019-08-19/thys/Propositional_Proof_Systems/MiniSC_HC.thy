subsubsection\<open>SC to HC\<close>
theory MiniSC_HC
imports MiniSC HC
begin

inductive_set AX1 where
"F \<in> AX0 \<Longrightarrow> F \<in> AX1" |
"((F \<^bold>\<rightarrow> \<bottom>) \<^bold>\<rightarrow> \<bottom>) \<^bold>\<rightarrow> F \<in> AX1"
lemma AX01: "AX0 \<subseteq> AX1" by (simp add: AX1.intros(1) subsetI)
lemma AX1_away: "AX1 \<union> \<Gamma> = AX0 \<union> (\<Gamma> \<union> AX1)" using AX01 by blast

lemma Deduction1: "F \<triangleright> (AX1 \<union> \<Gamma> ) \<turnstile>\<^sub>H \<bottom> \<longleftrightarrow> (AX1 \<union> \<Gamma>) \<turnstile>\<^sub>H (F \<^bold>\<rightarrow> \<bottom>)" unfolding AX1_away by (metis Deduction_theorem HC.simps HC_mono Un_commute Un_insert_left insertI1 subset_insertI)
lemma Deduction2: "(F \<^bold>\<rightarrow> \<bottom>) \<triangleright> (AX1 \<union> \<Gamma>) \<turnstile>\<^sub>H \<bottom> \<longleftrightarrow> (AX1 \<union> \<Gamma>) \<turnstile>\<^sub>H F" (is "?l \<longleftrightarrow> ?r")
proof
  assume l: ?l
  with Deduction_theorem[where \<Gamma>="AX1 \<union> \<Gamma>" and F="F \<^bold>\<rightarrow> \<bottom>" and G=\<bottom>]
  have "AX1 \<union> \<Gamma> \<turnstile>\<^sub>H (F \<^bold>\<rightarrow> \<bottom>) \<^bold>\<rightarrow> \<bottom>" unfolding AX1_away by(simp add: Un_commute)
  moreover have "AX1 \<union> \<Gamma> \<turnstile>\<^sub>H ((F \<^bold>\<rightarrow> \<bottom>) \<^bold>\<rightarrow> \<bottom>) \<^bold>\<rightarrow> F" using AX1.intros(2) HC.Ax by blast
  ultimately show ?r using HC.MP by blast
next
  assume r: ?r thus ?l by (meson HC.simps HC_mono insertI1 subset_insertI)
qed

lemma 
  "\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> is_mini_mset \<Gamma> \<Longrightarrow> is_mini_mset \<Delta> \<Longrightarrow>
  (set_mset \<Gamma> \<union> (\<lambda>F. F \<^bold>\<rightarrow> \<bottom>) ` set_mset \<Delta> \<union> AX1) \<turnstile>\<^sub>H \<bottom>"
proof(induction "\<Gamma>" "\<Delta>" rule: SCp.induct)
  case (ImpL \<Gamma> F \<Delta> G)
  from ImpL.prems have "is_mini_mset \<Gamma>" "is_mini_mset (F, \<Delta>)" by simp_all
  with ImpL.IH(1) have IH1: "set_mset \<Gamma> \<union> (\<lambda>F. F \<^bold>\<rightarrow> \<bottom>) ` set_mset (F, \<Delta>) \<union> AX1 \<turnstile>\<^sub>H \<bottom>" .
  hence IH1: "F \<^bold>\<rightarrow> \<bottom> \<triangleright> set_mset \<Gamma> \<union> (\<lambda>F. F \<^bold>\<rightarrow> \<bottom>) ` set_mset \<Delta> \<union> AX1 \<turnstile>\<^sub>H \<bottom>" by simp
  from ImpL.prems have "is_mini_mset (G, \<Gamma>)" "is_mini_mset \<Delta>" by simp_all
  with ImpL.IH(2) have IH2: "set_mset (G, \<Gamma>) \<union> (\<lambda>F. F \<^bold>\<rightarrow> \<bottom>) ` set_mset \<Delta> \<union> AX1 \<turnstile>\<^sub>H \<bottom>" .
  hence IH2: "G \<triangleright> (set_mset \<Gamma> \<union> (\<lambda>F. F \<^bold>\<rightarrow> \<bottom>) ` set_mset \<Delta> \<union> AX1) \<turnstile>\<^sub>H \<bottom>" by simp
  have R: "F \<^bold>\<rightarrow> G \<triangleright> AX1 \<union> \<Gamma> \<turnstile>\<^sub>H \<bottom>" if "G \<triangleright> AX1 \<union> \<Gamma> \<turnstile>\<^sub>H \<bottom>" "F \<^bold>\<rightarrow> \<bottom> \<triangleright> AX1 \<union> \<Gamma> \<turnstile>\<^sub>H \<bottom>" for \<Gamma> 
    using that by (metis Ax Deduction1 Deduction2 HC_mono MP insertI1 subset_insertI)
    (* I don't construct the actual proofs for the Rs. Sledgehammer is doing all the interesting work. :/ *)
  from R[where \<Gamma>="set_mset \<Gamma> \<union> (\<lambda>F. F \<^bold>\<rightarrow> \<bottom>) ` set_mset \<Delta>"]
  have "F \<^bold>\<rightarrow> G \<triangleright> (set_mset \<Gamma> \<union> (\<lambda>F. F \<^bold>\<rightarrow> \<bottom>) ` set_mset \<Delta> \<union> AX1) \<turnstile>\<^sub>H \<bottom>" using IH2 IH1 by(simp add: Un_commute)
  thus ?case by simp
next
  case (ImpR F \<Gamma> G \<Delta>)
  hence "is_mini_mset (F, \<Gamma>)" "is_mini_mset (G, \<Delta>)" by simp_all
  with ImpR.IH have IH: "F \<triangleright> G \<^bold>\<rightarrow> \<bottom> \<triangleright> set_mset \<Gamma> \<union> (\<lambda>F. F \<^bold>\<rightarrow> \<bottom>) ` set_mset \<Delta> \<union> AX1 \<turnstile>\<^sub>H \<bottom>" by(simp add: insert_commute)
  have R: "(F \<^bold>\<rightarrow> G) \<^bold>\<rightarrow> \<bottom> \<triangleright> \<Gamma> \<union> AX1 \<turnstile>\<^sub>H \<bottom>" if "F \<triangleright> G \<^bold>\<rightarrow> \<bottom> \<triangleright> \<Gamma> \<union> AX1 \<turnstile>\<^sub>H \<bottom>" for \<Gamma> using that
    by (metis AX1_away Deduction2 Deduction_theorem Un_commute Un_insert_right)
  thus ?case using IH by simp
next
  case (Ax k \<Gamma> \<Delta>)
  have R: "F \<triangleright> F \<^bold>\<rightarrow> \<bottom> \<triangleright> \<Gamma> \<union> AX1 \<turnstile>\<^sub>H \<bottom>" for F :: "'a formula" and \<Gamma> by (meson HC.simps insert_iff)
  from R[where F="Atom k" and \<Gamma>="set_mset \<Gamma> \<union> (\<lambda>F. F \<^bold>\<rightarrow> \<bottom>) ` set_mset \<Delta>"] show ?case using Ax.hyps
    by (simp add: insert_absorb)
next
  case BotL thus ?case by (simp add: HC.Ax)
qed simp_all

end
