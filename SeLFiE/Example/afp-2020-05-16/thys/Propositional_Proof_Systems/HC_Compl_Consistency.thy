theory HC_Compl_Consistency
imports Consistency HC
begin

context begin
private lemma dt: "F \<triangleright> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H G \<Longrightarrow> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H F \<^bold>\<rightarrow> G"
  by (metis AX100 Deduction_theorem Un_insert_right sup_left_commute)
lemma sim: "\<Gamma> \<union> AX10 \<turnstile>\<^sub>H F \<Longrightarrow> F \<triangleright> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H G \<Longrightarrow> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H G"
  using MP dt by blast
lemma sim_conj: "F \<triangleright> G \<triangleright> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H H \<Longrightarrow> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H F \<Longrightarrow> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H G \<Longrightarrow> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H H"
  using MP dt by (metis Un_insert_left)
lemma sim_disj: "\<lbrakk>F \<triangleright> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H H; G \<triangleright> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H H; \<Gamma> \<union> AX10 \<turnstile>\<^sub>H F \<^bold>\<or> G\<rbrakk> \<Longrightarrow> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H H"
proof goal_cases
  case 1
  have 2: "\<Gamma> \<union> AX10 \<turnstile>\<^sub>H F \<^bold>\<rightarrow> H" by (simp add: 1 dt)
  have 3: "\<Gamma> \<union> AX10 \<turnstile>\<^sub>H G \<^bold>\<rightarrow> H" by (simp add: 1 dt)
  have 4: "\<Gamma> \<union> AX10 \<turnstile>\<^sub>H (F \<^bold>\<or> G) \<^bold>\<rightarrow> H" by (meson 2 3 HC.simps HC_intros(7) HC_mono sup_ge2)
  thus ?case  using 1(3) MP by blast
qed

private lemma someax: "\<Gamma> \<union> AX10 \<turnstile>\<^sub>H F \<^bold>\<rightarrow> \<^bold>\<not> F \<^bold>\<rightarrow> \<bottom>"
proof -
  have "F \<triangleright> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H \<^bold>\<not> F \<^bold>\<rightarrow> F \<^bold>\<rightarrow> \<bottom>"
    by (meson HC_intros(12) HC_mono subset_insertI sup_ge2)
  then have "\<^bold>\<not> F \<triangleright> F \<triangleright> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H \<bottom>"
    by (meson HC.simps HC_mono insertI1 subset_insertI)
  then show ?thesis
    by (metis (no_types) Un_insert_left dt)
qed

lemma lem: "\<Gamma> \<union> AX10 \<turnstile>\<^sub>H \<^bold>\<not> F \<^bold>\<or> F"
proof -
  thm HC_intros(7)[of F \<bottom> "Not F"]
  have "F \<triangleright> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H ( \<^bold>\<not> F \<^bold>\<or> F)"
    by (metis AX10.intros(3) Ax HC_mono MP Un_commute Un_insert_left insertI1 sup_ge1)
  hence "F \<triangleright> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H \<^bold>\<not> ( \<^bold>\<not> F \<^bold>\<or> F) \<^bold>\<rightarrow> \<bottom>" using someax by (metis HC.simps Un_insert_left)
  hence "\<^bold>\<not> ( \<^bold>\<not> F \<^bold>\<or> F) \<triangleright> F \<triangleright> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H \<bottom>" by (meson Ax HC_mono MP insertI1 subset_insertI)
  hence "\<^bold>\<not> ( \<^bold>\<not> F \<^bold>\<or> F) \<triangleright> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H F \<^bold>\<rightarrow> \<bottom>"
    by (metis Un_insert_left dt insert_commute)
      
  have "\<^bold>\<not>F \<triangleright> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H ( \<^bold>\<not> F \<^bold>\<or> F)"
    by (metis HC.simps HC_intros(5) HC_mono inf_sup_ord(4) insertI1 insert_is_Un)
  hence "\<^bold>\<not>F \<triangleright> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H \<^bold>\<not> ( \<^bold>\<not> F \<^bold>\<or> F) \<^bold>\<rightarrow> \<bottom>" using someax by (metis HC.simps Un_insert_left)
  hence "\<^bold>\<not> ( \<^bold>\<not> F \<^bold>\<or> F) \<triangleright> \<^bold>\<not>F \<triangleright> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H \<bottom>" by (meson Ax HC_mono MP insertI1 subset_insertI)
  hence "\<^bold>\<not> ( \<^bold>\<not> F \<^bold>\<or> F) \<triangleright> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H \<^bold>\<not>F \<^bold>\<rightarrow> \<bottom>"
    by (metis Un_insert_left dt insert_commute)
  
  hence "\<Gamma> \<union> AX10 \<turnstile>\<^sub>H \<^bold>\<not> ( \<^bold>\<not> F \<^bold>\<or> F) \<^bold>\<rightarrow> \<bottom>"
    by (meson HC_intros(13) HC_mono MP \<open>\<^bold>\<not> (\<^bold>\<not> F \<^bold>\<or> F) \<triangleright> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H F \<^bold>\<rightarrow> \<bottom>\<close> dt subset_insertI sup_ge2)
  thus ?thesis by (meson HC.simps HC_intros(13) HC_mono sup_ge2)
(*    apply(insert HC_mono dt HC_intros(3-)[THEN HC_mono, OF sup_ge2] sim HC.intros)
    sledgehammer[debug,max_facts=50,timeout=120]*)
qed

lemma exchg: "\<Gamma> \<union> AX10 \<turnstile>\<^sub>H F \<^bold>\<or> G \<Longrightarrow> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H G \<^bold>\<or> F"
  by (meson AX10.intros(3) HC.simps HC_intros(5) HC_intros(7) HC_mono sup_ge2)
    
lemma lem2: "\<Gamma> \<union> AX10 \<turnstile>\<^sub>H F \<^bold>\<or> \<^bold>\<not> F" by (simp add: exchg lem)
  
  
lemma imp_sim: "\<Gamma> \<union> AX10 \<turnstile>\<^sub>H F \<^bold>\<rightarrow> G \<Longrightarrow> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H \<^bold>\<not> F \<^bold>\<or> G"
proof goal_cases case 1
  have "\<Gamma> \<union> AX10 \<turnstile>\<^sub>H F \<^bold>\<rightarrow> \<^bold>\<not> F \<^bold>\<or> G"
  proof -
    have f1: "\<forall>F f Fa. \<not> (F \<turnstile>\<^sub>H f) \<or> \<not> F \<subseteq> Fa \<or> Fa \<turnstile>\<^sub>H f"
      using HC_mono by blast
    then have f2: "F \<triangleright> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H F \<^bold>\<rightarrow> G"
      by (metis "1" subset_insertI) (* > 1.0 s, timed out *)
    have "\<Gamma> \<union> AX10 \<turnstile>\<^sub>H G \<^bold>\<rightarrow> \<^bold>\<not> F \<^bold>\<or> G"
      using f1 by blast
    then show ?thesis
      using f2 f1 by (metis (no_types) HC.simps dt insertI1 subset_insertI)
  qed
  moreover have "\<Gamma> \<union> AX10 \<turnstile>\<^sub>H \<^bold>\<not>F \<^bold>\<rightarrow> \<^bold>\<not> F \<^bold>\<or> G" by (simp add: AX10.intros(2) Ax)
  ultimately show ?case
  proof -
    have "\<And>F f fa fb. \<not> (F \<turnstile>\<^sub>H f \<^bold>\<rightarrow> fa) \<or> \<not> (fb \<triangleright> F \<turnstile>\<^sub>H f) \<or> fb \<triangleright> F \<turnstile>\<^sub>H fa"
      by (meson HC_mono MP subset_insertI)
    then show ?thesis
      by (metis Ax \<open>\<Gamma> \<union> AX10 \<turnstile>\<^sub>H F \<^bold>\<rightarrow> \<^bold>\<not> F \<^bold>\<or> G\<close> \<open>\<Gamma> \<union> AX10 \<turnstile>\<^sub>H \<^bold>\<not> F \<^bold>\<rightarrow> \<^bold>\<not> F \<^bold>\<or> G\<close> insertI1 lem sim_disj)
  qed
qed
  
lemma inpcp: "\<Gamma> \<union> AX10 \<turnstile>\<^sub>H \<bottom> \<Longrightarrow> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H F"
  by (meson HC_intros(13) HC_mono MP dt subset_insertI sup_ge2)
    
lemma HC_case_distinction: "\<Gamma> \<union> AX10 \<turnstile>\<^sub>H F \<^bold>\<rightarrow> G \<Longrightarrow> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H \<^bold>\<not> F \<^bold>\<rightarrow> G \<Longrightarrow> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H G"
  using HC_intros(7)[of F G "Not F"] lem2
  by (metis (no_types, hide_lams) HC.simps HC_mono insertI1 sim_disj subset_insertI)
  
lemma nand_sim: "\<Gamma> \<union> AX10 \<turnstile>\<^sub>H \<^bold>\<not> (F \<^bold>\<and> G) \<Longrightarrow> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H \<^bold>\<not> F \<^bold>\<or> \<^bold>\<not> G"
proof goal_cases case 1
  have "\<Gamma> \<union> AX10 \<turnstile>\<^sub>H F \<^bold>\<rightarrow> G \<^bold>\<rightarrow> F \<^bold>\<and> G" by (simp add: AX10.intros(7) Ax)
  hence 2: "F \<triangleright> G \<triangleright> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H F \<^bold>\<and> G"
    by (meson Ax HC_mono MP insertI1 subset_insertI)
  hence 3: "F \<triangleright> G \<triangleright> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H \<bottom>" using 1 by (meson HC_intros(12) HC_mono MP subset_insertI sup_ge2)
  from 2 have "\<Gamma> \<union> AX10 \<turnstile>\<^sub>H G \<^bold>\<rightarrow> F \<^bold>\<rightarrow> F \<^bold>\<and> G" by (metis Un_insert_left dt)
  have 4: "\<Gamma> \<union> AX10 \<turnstile>\<^sub>H \<^bold>\<not> F \<^bold>\<rightarrow> \<^bold>\<not> F \<^bold>\<or> \<^bold>\<not> G" by (simp add: AX10.intros(2) Ax)
  have 5: "\<Gamma> \<union> AX10 \<turnstile>\<^sub>H \<^bold>\<not> G \<^bold>\<rightarrow> F \<^bold>\<rightarrow> \<^bold>\<not> F \<^bold>\<or> \<^bold>\<not> G"
    by (metis (full_types) AX10.intros(3) AX100 Ax HC_mono MP Un_assoc Un_insert_left dt inf_sup_ord(4) insertI1 subset_insertI sup_ge2)
  have 6: "\<Gamma> \<union> AX10 \<turnstile>\<^sub>H G \<^bold>\<rightarrow> F \<^bold>\<rightarrow> \<^bold>\<not> F \<^bold>\<or> \<^bold>\<not> G" using 3 inpcp by (metis Un_insert_left dt)
  have 7: "\<Gamma> \<union> AX10 \<turnstile>\<^sub>H F \<^bold>\<rightarrow> \<^bold>\<not> F \<^bold>\<or> \<^bold>\<not> G" using 5 6 HC_case_distinction by blast
  show ?case using 4 7 HC_case_distinction by blast
qed
  
lemma HC_contrapos_nn:
  "\<lbrakk>\<Gamma> \<union> AX10 \<turnstile>\<^sub>H \<^bold>\<not> F; \<Gamma> \<union> AX10 \<turnstile>\<^sub>H G \<^bold>\<rightarrow> F\<rbrakk> \<Longrightarrow> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H \<^bold>\<not> G"
proof goal_cases case 1
  from 1(1) have "\<Gamma> \<union> AX10 \<turnstile>\<^sub>H F \<^bold>\<rightarrow> \<bottom>" using HC_intros(12) using HC_mono MP by blast
  hence "\<Gamma> \<union> AX10 \<turnstile>\<^sub>H G \<^bold>\<rightarrow> \<bottom>" by (meson 1(2) HC.intros(1) HC_mono MP dt insertI1 subset_insertI)
  thus ?case by(meson HC_intros(11) HC_intros(3) HC_mono MP sup_ge2)
qed
      

lemma nor_sim: 
assumes "\<Gamma> \<union> AX10 \<turnstile>\<^sub>H \<^bold>\<not> (F \<^bold>\<or> G)"
shows "\<Gamma> \<union> AX10 \<turnstile>\<^sub>H \<^bold>\<not> F" " \<Gamma> \<union> AX10 \<turnstile>\<^sub>H \<^bold>\<not> G"
  using HC_contrapos_nn assms by (metis HC_intros(5,6) HC_mono sup_ge2)+
    
lemma HC_contrapos_np:
  "\<lbrakk>\<Gamma> \<union> AX10 \<turnstile>\<^sub>H \<^bold>\<not> F; \<Gamma> \<union> AX10 \<turnstile>\<^sub>H \<^bold>\<not> G \<^bold>\<rightarrow> F\<rbrakk> \<Longrightarrow> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H G"
    by (meson HC_intros(12) HC_intros(13) HC_mono MP sup_ge2  HC_contrapos_nn[of \<Gamma> F "Not G"])    
    
lemma not_imp: "\<Gamma> \<union> AX10 \<turnstile>\<^sub>H \<^bold>\<not> F \<^bold>\<rightarrow> F \<^bold>\<rightarrow> G"
proof goal_cases case 1
  have "\<Gamma> \<union> AX10 \<turnstile>\<^sub>H \<^bold>\<not> F \<^bold>\<rightarrow> F \<^bold>\<rightarrow> \<bottom>" by (simp add: AX10.intros(9) Ax)
  hence "\<^bold>\<not> F \<triangleright> F \<triangleright> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H \<bottom>" by (meson HC.simps HC_mono insertI1 subset_insertI)
  hence "\<^bold>\<not> F \<triangleright> F \<triangleright> \<Gamma> \<union> AX10 \<turnstile>\<^sub>H G" by (metis (no_types, hide_lams) Un_commute Un_insert_right inpcp)
  thus ?case by (metis Un_insert_left dt insert_commute)
qed

lemma HC_consistent:  "pcp {\<Gamma>| \<Gamma>. \<not>(\<Gamma> \<union> AX10 \<turnstile>\<^sub>H \<bottom>)}"
  unfolding pcp_def
  apply(intro ballI conjI; unfold mem_Collect_eq; elim exE conjE; erule contrapos_np; clarsimp)
          subgoal by (simp add: HC.Ax)
         subgoal by (meson Ax HC_intros(12) HC_mono MP Un_upper1 sup_ge2)
        subgoal using sim_conj by (metis (no_types, lifting) Ax HC_intros(8) HC_intros(9) HC_mono MP sup_ge1 sup_ge2)
       subgoal using sim_disj using Ax by blast
      subgoal by (erule (1) sim_disj) (simp add: Ax imp_sim)
     subgoal by (metis Ax HC_contrapos_nn MP Un_iff Un_insert_left dt inpcp someax)  
    subgoal by(erule (1) sim_disj) (simp add: Ax nand_sim)
   subgoal by(erule  sim_conj) (meson Ax Un_iff nor_sim)+
  subgoal for \<Gamma> F G apply(erule sim_conj) 
     subgoal by (meson Ax HC_Compl_Consistency.not_imp HC_contrapos_np Un_iff) 
    subgoal by (metis Ax HC_contrapos_nn HC_intros(3) HC_mono sup_ge1 sup_ge2)
  done
done

end

corollary HC_complete: 
  fixes F :: "'a :: countable formula"
  shows "\<Turnstile> F \<Longrightarrow> AX10 \<turnstile>\<^sub>H F"
proof(erule contrapos_pp)
  let ?W = "{\<Gamma>| \<Gamma>. \<not>((\<Gamma> :: ('a :: countable) formula set) \<union> AX10 \<turnstile>\<^sub>H \<bottom>)}"
    note [[show_types]]
  assume \<open>\<not> (AX10 \<turnstile>\<^sub>H F)\<close>
  hence "\<not> (\<^bold>\<not>F \<triangleright> AX10 \<turnstile>\<^sub>H \<bottom>)"
    by (metis AX100 Deduction_theorem HC_intros(13) MP Un_insert_right)
  hence "{\<^bold>\<not>F} \<in> ?W" by simp
  with pcp_sat HC_consistent have "sat {\<^bold>\<not> F}" .
  thus "\<not> \<Turnstile> F" by (simp add: sat_def)
qed
    

  
end
