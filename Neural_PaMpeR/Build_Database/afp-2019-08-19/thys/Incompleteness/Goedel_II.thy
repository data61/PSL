chapter\<open>Gödel's Second Incompleteness Theorem\<close>

theory Goedel_II
imports Goedel_I Quote 
begin

text\<open>The connection between @{term Quote} and @{term HR} (for interest only).\<close>

lemma Quote_q_Eats [intro]:
  "Quote y y' \<Longrightarrow> Quote z z' \<Longrightarrow> Quote (y \<triangleleft> z) (q_Eats y' z')"
  by (auto simp: Quote_def SeqQuote_def intro: BuildSeq2_combine)

lemma Quote_q_Succ [intro]:  "Quote y y' \<Longrightarrow> Quote (succ y) (q_Succ y')"
  by (auto simp: succ_def q_Succ_def)

lemma HR_imp_eq_H: "HR x z \<Longrightarrow> z = \<lbrakk>HF x\<rbrakk>e"
  apply (auto simp add: SeqHR_def HR_def)
  apply (erule BuildSeq2_induct, auto simp add: q_defs WR_iff_eq_W [where e=e])
  done

lemma HR_Ord_D: "HR x y \<Longrightarrow> Ord x \<Longrightarrow> WR x y"
  by (metis HF_Ord HR_imp_eq_H WR_iff_eq_W)

lemma WR_Quote: "WR (ord_of i) y \<Longrightarrow> Quote (ord_of i) y"
  by (induct i arbitrary: y) (auto simp: Quote_0 WR0_iff WR_succ_iff q_Succ_def [symmetric])

lemma [simp]: "\<langle>\<langle>0,0,0\<rangle>, x, y\<rangle> = q_Eats x y"
  by (simp add: q_Eats_def)

lemma HR_imp_Quote: "coding_hf x \<Longrightarrow> HR x y \<Longrightarrow> Quote x y"
  apply (induct x arbitrary: y rule: coding_hf.induct, auto simp: WR_Quote HR_Ord_D)
  apply (auto dest!: HR_imp_eq_H [where e= e0])
  by (metis hpair_def' Quote_0 HR_H Quote_q_Eats)


interpretation qp0: quote_perm 0 "{}" "make_F {} 0"
  proof unfold_locales qed auto

lemma MonPon_PfP_implies_PfP:
  "\<lbrakk>{} \<turnstile> \<alpha> IMP \<beta>; ground_fm \<alpha>; ground_fm \<beta>\<rbrakk> \<Longrightarrow> {PfP \<lceil>\<alpha>\<rceil>} \<turnstile> PfP \<lceil>\<beta>\<rceil>"
  using qp0.quote_all_MonPon_PfP_ssubst
  by auto (metis Assume PfP_implies_ModPon_PfP_quot proved_iff_proved_PfP thin0)

lemma PfP_quot_contra: "ground_fm \<alpha> \<Longrightarrow> {} \<turnstile> PfP \<lceil>\<alpha>\<rceil> IMP PfP \<lceil>Neg \<alpha>\<rceil> IMP PfP \<lceil>Fls\<rceil>"
  using qp0.quote_all_Contra_PfP_ssubst 
  by (auto simp: qp0.quote_all_Contra_PfP_ssubst ground_fm_aux_def)


text\<open>Gödel's second incompleteness theorem:
      If consistent, our theory cannot prove its own consistency.\<close>
theorem Goedel_II:
  assumes "\<not> {} \<turnstile> Fls"
    shows "\<not> {} \<turnstile> Neg (PfP \<lceil>Fls\<rceil>)"
proof -
  from assms Goedel_I obtain \<delta> 
    where diag: "{} \<turnstile> \<delta> IFF Neg (PfP \<lceil>\<delta>\<rceil>)"  "\<not> {} \<turnstile> \<delta>"
      and gnd:  "ground_fm \<delta>"
    by metis
  have "{PfP \<lceil>\<delta>\<rceil>} \<turnstile> PfP \<lceil>PfP \<lceil>\<delta>\<rceil>\<rceil>"
    by (auto simp: Provability ground_fm_aux_def supp_conv_fresh)
  moreover have "{PfP \<lceil>\<delta>\<rceil>} \<turnstile> PfP \<lceil>Neg (PfP \<lceil>\<delta>\<rceil>)\<rceil>"
    apply (rule MonPon_PfP_implies_PfP [OF _ gnd])
    apply (metis Conj_E2 Iff_def Iff_sym diag(1))
    apply (auto simp: ground_fm_aux_def supp_conv_fresh) 
    done
  moreover have "ground_fm (PfP \<lceil>\<delta>\<rceil>)"
    by (auto simp: ground_fm_aux_def supp_conv_fresh)
  ultimately have "{PfP \<lceil>\<delta>\<rceil>} \<turnstile> PfP \<lceil>Fls\<rceil>" using PfP_quot_contra  
    by (metis (no_types) anti_deduction cut2)
  thus "\<not> {} \<turnstile> Neg (PfP \<lceil>Fls\<rceil>)"
    by (metis Iff_MP2_same Neg_mono cut1 diag)
qed

end

