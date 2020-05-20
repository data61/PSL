section \<open> Fixed-points and Recursion \<close>

theory utp_recursion
  imports 
    utp_pred_laws
    utp_rel
begin

subsection \<open> Fixed-point Laws \<close>
  
lemma mu_id: "(\<mu> X \<bullet> X) = true"
  by (simp add: antisym gfp_upperbound)

lemma mu_const: "(\<mu> X \<bullet> P) = P"
  by (simp add: gfp_const)

lemma nu_id: "(\<nu> X \<bullet> X) = false"                                                            
  by (meson lfp_lowerbound utp_pred_laws.bot.extremum_unique)

lemma nu_const: "(\<nu> X \<bullet> P) = P"
  by (simp add: lfp_const)

lemma mu_refine_intro:
  assumes "(C \<Rightarrow> S) \<sqsubseteq> F(C \<Rightarrow> S)" "(C \<and> \<mu> F) = (C \<and> \<nu> F)"
  shows "(C \<Rightarrow> S) \<sqsubseteq> \<mu> F"
proof -
  from assms have "(C \<Rightarrow> S) \<sqsubseteq> \<nu> F"
    by (simp add: lfp_lowerbound)
  with assms show ?thesis
    by (pred_auto)
qed

subsection \<open> Obtaining Unique Fixed-points \<close>
    
text \<open> Obtaining termination proofs via approximation chains. Theorems and proofs adapted
  from Chapter 2, page 63 of the UTP book~\cite{Hoare&98}.  \<close>

type_synonym 'a chain = "nat \<Rightarrow> 'a upred"

definition chain :: "'a chain \<Rightarrow> bool" where
  "chain Y = ((Y 0 = false) \<and> (\<forall> i. Y (Suc i) \<sqsubseteq> Y i))"

lemma chain0 [simp]: "chain Y \<Longrightarrow> Y 0 = false"
  by (simp add:chain_def)

lemma chainI:
  assumes "Y 0 = false" "\<And> i. Y (Suc i) \<sqsubseteq> Y i"
  shows "chain Y"
  using assms by (auto simp add: chain_def)

lemma chainE:
  assumes "chain Y" "\<And> i. \<lbrakk> Y 0 = false; Y (Suc i) \<sqsubseteq> Y i \<rbrakk> \<Longrightarrow> P"
  shows "P"
  using assms by (simp add: chain_def)

lemma L274:
  assumes "\<forall> n. ((E n \<and>\<^sub>p X) = (E n \<and> Y))"
  shows "(\<Sqinter> (range E) \<and> X) = (\<Sqinter> (range E) \<and> Y)"
  using assms by (pred_auto)

text \<open> Constructive chains \<close>

definition constr ::
  "('a upred \<Rightarrow> 'a upred) \<Rightarrow> 'a chain \<Rightarrow> bool" where
"constr F E \<longleftrightarrow> chain E \<and> (\<forall> X n. ((F(X) \<and> E(n + 1)) = (F(X \<and> E(n)) \<and> E (n + 1))))"

lemma constrI:
  assumes "chain E" "\<And> X n. ((F(X) \<and> E(n + 1)) = (F(X \<and> E(n)) \<and> E (n + 1)))"
  shows "constr F E"
  using assms by (auto simp add: constr_def)

text \<open> This lemma gives a way of showing that there is a unique fixed-point when
        the predicate function can be built using a constructive function F
        over an approximation chain E \<close>

lemma chain_pred_terminates:
  assumes "constr F E" "mono F"
  shows "(\<Sqinter> (range E) \<and> \<mu> F) = (\<Sqinter> (range E) \<and> \<nu> F)"
proof -
  from assms have "\<forall> n. (E n \<and> \<mu> F) = (E n \<and> \<nu> F)"
  proof (rule_tac allI)
    fix n
    from assms show "(E n \<and> \<mu> F) = (E n \<and> \<nu> F)"
    proof (induct n)
      case 0 thus ?case by (simp add: constr_def)
    next
      case (Suc n)
      note hyp = this
      thus ?case
      proof -
        have "(E (n + 1) \<and> \<mu> F) = (E (n + 1) \<and> F (\<mu> F))"
          using gfp_unfold[OF hyp(3), THEN sym] by (simp add: constr_def)
        also from hyp have "... = (E (n + 1) \<and> F (E n \<and> \<mu> F))"
          by (metis conj_comm constr_def)
        also from hyp have "... = (E (n + 1) \<and> F (E n \<and> \<nu> F))"
          by simp
        also from hyp have "... = (E (n + 1) \<and> \<nu> F)"
          by (metis (no_types, lifting) conj_comm constr_def lfp_unfold)
        ultimately show ?thesis
          by simp
      qed
    qed
  qed
  thus ?thesis
    by (auto intro: L274)
qed

theorem constr_fp_uniq:
  assumes "constr F E" "mono F" "\<Sqinter> (range E) = C"
  shows "(C \<and> \<mu> F) = (C \<and> \<nu> F)"
  using assms(1) assms(2) assms(3) chain_pred_terminates by blast
    
subsection \<open> Noetherian Induction Instantiation\<close>
      
text \<open> Contribution from Yakoub Nemouchi.The following generalization was used by Tobias Nipkow
        and Peter Lammich  in \emph{Refine\_Monadic} \<close>

lemma  wf_fixp_uinduct_pure_ueq_gen:     
  assumes fixp_unfold: "fp B = B (fp B)"
  and              WF: "wf R"
  and     induct_step:
          "\<And>f st. \<lbrakk>\<And>st'. (st',st) \<in> R  \<Longrightarrow> (((Pre \<and> \<lceil>e\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st'\<guillemotright>) \<Rightarrow> Post) \<sqsubseteq> f)\<rbrakk>
               \<Longrightarrow> fp B = f \<Longrightarrow>((Pre \<and> \<lceil>e\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright>) \<Rightarrow> Post) \<sqsubseteq> (B f)"
        shows "((Pre \<Rightarrow> Post) \<sqsubseteq> fp B)"  
proof -  
  { fix st
    have "((Pre \<and> \<lceil>e\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright>) \<Rightarrow> Post) \<sqsubseteq> (fp B)" 
    using WF proof (induction rule: wf_induct_rule)
      case (less x)
      hence "(Pre \<and> \<lceil>e\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>x\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> B (fp B)"
        by (rule induct_step, rel_blast, simp)
      then show ?case
        using fixp_unfold by auto
    qed
  }
  thus ?thesis 
  by pred_simp  
qed
  
text \<open> The next lemma shows that using substitution also work. However it is not that generic
        nor practical for proof automation ... \<close>

lemma refine_usubst_to_ueq:
  "vwb_lens E \<Longrightarrow> (Pre \<Rightarrow> Post)\<lbrakk>\<guillemotleft>st'\<guillemotright>/$E\<rbrakk> \<sqsubseteq> f\<lbrakk>\<guillemotleft>st'\<guillemotright>/$E\<rbrakk> = (((Pre \<and> $E =\<^sub>u \<guillemotleft>st'\<guillemotright>) \<Rightarrow> Post) \<sqsubseteq> f)"
  by (rel_auto, metis vwb_lens_wb wb_lens.get_put)  

text \<open> By instantiation of @{thm wf_fixp_uinduct_pure_ueq_gen} with @{term \<mu>} and lifting of the 
        well-founded relation we have ... \<close>
  
lemma mu_rec_total_pure_rule: 
  assumes WF: "wf R"
  and     M: "mono B"  
  and     induct_step:
          "\<And> f st.  \<lbrakk>(Pre \<and> (\<lceil>e\<rceil>\<^sub><,\<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> f\<rbrakk>
               \<Longrightarrow> \<mu> B = f \<Longrightarrow>(Pre \<and> \<lceil>e\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> (B f)"
        shows "(Pre \<Rightarrow> Post) \<sqsubseteq> \<mu> B"  
proof (rule wf_fixp_uinduct_pure_ueq_gen[where fp=\<mu> and Pre=Pre and B=B and R=R and e=e])
  show "\<mu> B = B (\<mu> B)"
    by (simp add: M def_gfp_unfold)
  show "wf R"
    by (fact WF)
  show "\<And>f st. (\<And>st'. (st', st) \<in> R \<Longrightarrow> (Pre \<and> \<lceil>e\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st'\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> f) \<Longrightarrow> 
                \<mu> B = f \<Longrightarrow> 
                (Pre \<and> \<lceil>e\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> B f"
    by (rule induct_step, rel_simp, simp)
qed

lemma nu_rec_total_pure_rule: 
  assumes WF: "wf R"
  and     M: "mono B"  
  and     induct_step:
          "\<And> f st.  \<lbrakk>(Pre \<and> (\<lceil>e\<rceil>\<^sub><,\<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> f\<rbrakk>
               \<Longrightarrow> \<nu> B = f \<Longrightarrow>(Pre \<and> \<lceil>e\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> (B f)"
        shows "(Pre \<Rightarrow> Post) \<sqsubseteq> \<nu> B"  
proof (rule wf_fixp_uinduct_pure_ueq_gen[where fp=\<nu> and Pre=Pre and B=B and R=R and e=e])
  show "\<nu> B = B (\<nu> B)"
    by (simp add: M def_lfp_unfold)
  show "wf R"
    by (fact WF)
  show "\<And>f st. (\<And>st'. (st', st) \<in> R \<Longrightarrow> (Pre \<and> \<lceil>e\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st'\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> f) \<Longrightarrow> 
                \<nu> B = f \<Longrightarrow> 
                (Pre \<and> \<lceil>e\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> B f"
    by (rule induct_step, rel_simp, simp)
qed

text \<open>Since @{term "B ((Pre \<and> (\<lceil>E\<rceil>\<^sub><,\<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright> \<Rightarrow> Post)) \<sqsubseteq> B (\<mu> B)"} and 
      @{term "mono B"}, thus,  @{thm mu_rec_total_pure_rule} can be expressed as follows\<close>
  
lemma mu_rec_total_utp_rule: 
  assumes WF: "wf R"
    and     M: "mono B"  
    and     induct_step:
    "\<And>st. (Pre \<and> \<lceil>e\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> (B ((Pre \<and> (\<lceil>e\<rceil>\<^sub><,\<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright> \<Rightarrow> Post)))"
  shows "(Pre \<Rightarrow> Post) \<sqsubseteq> \<mu> B"  
proof (rule mu_rec_total_pure_rule[where R=R and e=e], simp_all add: assms)
  show "\<And>f st. (Pre \<and> (\<lceil>e\<rceil>\<^sub><, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> f \<Longrightarrow> \<mu> B = f \<Longrightarrow> (Pre \<and> \<lceil>e\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> B f"
    by (simp add: M induct_step monoD order_subst2)
qed

lemma nu_rec_total_utp_rule: 
  assumes WF: "wf R"
    and     M: "mono B"  
    and     induct_step:
    "\<And>st. (Pre \<and> \<lceil>e\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> (B ((Pre \<and> (\<lceil>e\<rceil>\<^sub><,\<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright> \<Rightarrow> Post)))"
  shows "(Pre \<Rightarrow> Post) \<sqsubseteq> \<nu> B"  
proof (rule nu_rec_total_pure_rule[where R=R and e=e], simp_all add: assms)
  show "\<And>f st. (Pre \<and> (\<lceil>e\<rceil>\<^sub><, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> f \<Longrightarrow> \<nu> B = f \<Longrightarrow> (Pre \<and> \<lceil>e\<rceil>\<^sub>< =\<^sub>u \<guillemotleft>st\<guillemotright> \<Rightarrow> Post) \<sqsubseteq> B f"
    by (simp add: M induct_step monoD order_subst2)
qed

end