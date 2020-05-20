theory Adequacy
imports ResourcedAdequacy "Denotational-Related"
begin

theorem adequacy:
  assumes "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<^esub> \<noteq> \<bottom>"
  shows "\<exists> \<Delta> v. \<Gamma> : e \<Down>\<^bsub>S\<^esub> \<Delta> : v"
proof-
  have "\<lbrace>\<Gamma>\<rbrace> \<triangleleft>\<triangleright>\<^sup>* \<N>\<lbrace>\<Gamma>\<rbrace>" by (rule heaps_similar)
  hence  "\<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<^esub> \<triangleleft>\<triangleright> (\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^sup>\<infinity>" by (rule denotational_semantics_similar)
  from bot_or_not_bot[OF this] assms
  have "(\<N>\<lbrakk>e\<rbrakk>\<^bsub>\<N>\<lbrace>\<Gamma>\<rbrace>\<^esub>)\<cdot>C\<^sup>\<infinity> \<noteq> \<bottom>" by metis
  thus ?thesis by (rule resourced_adequacy)
qed

end
