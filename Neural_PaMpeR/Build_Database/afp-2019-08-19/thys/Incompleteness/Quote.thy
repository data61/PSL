chapter\<open>Quotations of the Free Variables\<close>

theory Quote
imports Pseudo_Coding
begin

section \<open>Sequence version of the ``Special p-Function, F*''\<close>

text\<open>The definition below describes a relation, not a function. 
      This material relates to Section 8, but omits the ordering of the universe.\<close>

definition SeqQuote :: "hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> bool"
where "SeqQuote x x' s k \<equiv> 
       BuildSeq2 (\<lambda>y y'. y=0 \<and> y' = 0)
                 (\<lambda>u u' v v' w w'. u = v \<triangleleft> w \<and> u' = q_Eats v' w') s k x x'"

subsection \<open>Defining the syntax: quantified body\<close>

nominal_function SeqQuoteP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom l \<sharp> (s,k,sl,sl',m,n,sm,sm',sn,sn'); 
          atom sl \<sharp> (s,sl',m,n,sm,sm',sn,sn'); atom sl' \<sharp> (s,m,n,sm,sm',sn,sn'); 
          atom m \<sharp> (s,n,sm,sm',sn,sn');  atom n \<sharp> (s,sm,sm',sn,sn');  
          atom sm \<sharp> (s,sm',sn,sn');  atom sm' \<sharp> (s,sn,sn');  
          atom sn \<sharp> (s,sn');  atom sn' \<sharp> s\<rbrakk> \<Longrightarrow>
    SeqQuoteP t u s k = 
      LstSeqP s k (HPair t u) AND 
      All2 l (SUCC k) (Ex sl (Ex sl' (HPair (Var l) (HPair (Var sl) (Var sl')) IN s AND
                ((Var sl EQ Zero AND Var sl' EQ Zero) OR
                Ex m (Ex n (Ex sm (Ex sm' (Ex sn (Ex sn' (Var m IN Var l AND Var n IN Var l AND 
                       HPair (Var m) (HPair (Var sm) (Var sm')) IN s AND 
                       HPair (Var n) (HPair (Var sn) (Var sn')) IN s AND
                       Var sl EQ Eats (Var sm) (Var sn) AND
                       Var sl' EQ Q_Eats (Var sm') (Var sn')))))))))))"
by (auto simp: eqvt_def SeqQuoteP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows SeqQuoteP_fresh_iff [simp]:
      "a \<sharp> SeqQuoteP t u s k \<longleftrightarrow> a \<sharp> t \<and> a \<sharp> u \<and> a \<sharp> s \<and> a \<sharp> k"  (is ?thesis1)
  and eval_fm_SeqQuoteP [simp]: 
      "eval_fm e (SeqQuoteP t u s k) \<longleftrightarrow> SeqQuote \<lbrakk>t\<rbrakk>e \<lbrakk>u\<rbrakk>e \<lbrakk>s\<rbrakk>e \<lbrakk>k\<rbrakk>e"    (is ?thesis2)
  and SeqQuoteP_sf [iff]:
      "Sigma_fm (SeqQuoteP t u s k)"    (is ?thsf) 
  and SeqQuoteP_imp_OrdP:
      "{ SeqQuoteP t u s k } \<turnstile> OrdP k"  (is ?thord)
  and SeqQuoteP_imp_LstSeqP:
      "{ SeqQuoteP t u s k } \<turnstile> LstSeqP s k (HPair t u)"  (is ?thlstseq)
proof -
  obtain l::name and sl::name and sl'::name and m::name and n::name and 
         sm::name and sm'::name and sn::name and sn'::name
    where atoms:
         "atom l \<sharp> (s,k,sl,sl',m,n,sm,sm',sn,sn')"
         "atom sl \<sharp> (s,sl',m,n,sm,sm',sn,sn')"  "atom sl' \<sharp> (s,m,n,sm,sm',sn,sn')"
         "atom m \<sharp> (s,n,sm,sm',sn,sn')"  "atom n \<sharp> (s,sm,sm',sn,sn')"
         "atom sm \<sharp> (s,sm',sn,sn')"  "atom sm' \<sharp> (s,sn,sn')"
         "atom sn \<sharp> (s,sn')"  "atom sn' \<sharp> s"
    by (metis obtain_fresh) 
  thus ?thesis1 ?thsf ?thord ?thlstseq
    by auto (auto simp: LstSeqP.simps)
  show ?thesis2 using atoms
    by (force simp add: LstSeq_imp_Ord SeqQuote_def 
             BuildSeq2_def BuildSeq_def Builds_def HBall_def q_Eats_def 
             Seq_iff_app [of "\<lbrakk>s\<rbrakk>e", OF LstSeq_imp_Seq_succ]  
             Ord_trans [of _ _ "succ \<lbrakk>k\<rbrakk>e"] 
             cong: conj_cong)
qed
      
lemma SeqQuoteP_subst [simp]:
      "(SeqQuoteP t u s k)(j::=w) = 
       SeqQuoteP (subst j w t) (subst j w u) (subst j w s) (subst j w k)"
proof -
  obtain l::name and sl::name and sl'::name and m::name and n::name and 
         sm::name and sm'::name and sn::name and sn'::name
    where "atom l \<sharp> (s,k,w,j,sl,sl',m,n,sm,sm',sn,sn')"
          "atom sl \<sharp> (s,w,j,sl',m,n,sm,sm',sn,sn')"  "atom sl' \<sharp> (s,w,j,m,n,sm,sm',sn,sn')"
          "atom m \<sharp> (s,w,j,n,sm,sm',sn,sn')"  "atom n \<sharp> (s,w,j,sm,sm',sn,sn')"
          "atom sm \<sharp> (s,w,j,sm',sn,sn')"  "atom sm' \<sharp> (s,w,j,sn,sn')"
          "atom sn \<sharp> (s,w,j,sn')"  "atom sn' \<sharp> (s,w,j)"
    by (metis obtain_fresh) 
  thus ?thesis
    by (force simp add: SeqQuoteP.simps [of l _ _ sl sl' m n sm sm' sn sn']) 
qed

declare SeqQuoteP.simps [simp del]

subsection \<open>Correctness properties\<close>

lemma SeqQuoteP_lemma:
  fixes m::name and sm::name and sm'::name and n::name and sn::name and sn'::name
  assumes "atom m \<sharp> (t,u,s,k,n,sm,sm',sn,sn')"  "atom n \<sharp> (t,u,s,k,sm,sm',sn,sn')"
          "atom sm \<sharp> (t,u,s,k,sm',sn,sn')"  "atom sm' \<sharp> (t,u,s,k,sn,sn')"
          "atom sn \<sharp> (t,u,s,k,sn')"  "atom sn' \<sharp> (t,u,s,k)"
    shows "{ SeqQuoteP t u s k }
           \<turnstile> (t EQ Zero AND u EQ Zero) OR
             Ex m (Ex n (Ex sm (Ex sm' (Ex sn (Ex sn' (Var m IN k AND Var n IN k AND
                 SeqQuoteP (Var sm) (Var sm') s (Var m) AND
                 SeqQuoteP (Var sn) (Var sn') s (Var n) AND
                 t EQ Eats (Var sm) (Var sn) AND
                 u EQ Q_Eats (Var sm') (Var sn')))))))"
proof -
  obtain l::name and sl::name and sl'::name
    where "atom l \<sharp> (t,u,s,k,sl,sl',m,n,sm,sm',sn,sn')"
          "atom sl \<sharp> (t,u,s,k,sl',m,n,sm,sm',sn,sn')"
          "atom sl' \<sharp> (t,u,s,k,m,n,sm,sm',sn,sn')"
    by (metis obtain_fresh)
  thus ?thesis using assms
    apply (simp add: SeqQuoteP.simps [of l s k sl sl' m n sm sm' sn sn'])
    apply (rule Conj_EH Ex_EH All2_SUCC_E [THEN rotate2] | simp)+
    apply (rule cut_same [where A = "HPair t u EQ HPair (Var sl) (Var sl')"])
    apply (metis Assume AssumeH(4) LstSeqP_EQ)
    apply clarify
    apply (rule Disj_EH)
    apply (rule Disj_I1)
    apply (rule anti_deduction)
    apply (rule Var_Eq_subst_Iff [THEN Sym_L, THEN Iff_MP_same])
    apply (rule rotate2)
    apply (rule Var_Eq_subst_Iff [THEN Sym_L, THEN Iff_MP_same], force)
    \<comment> \<open>now the quantified case\<close>
    apply (rule Ex_EH Conj_EH)+
    apply simp_all
    apply (rule Disj_I2)
    apply (rule Ex_I [where x = "Var m"], simp)
    apply (rule Ex_I [where x = "Var n"], simp)
    apply (rule Ex_I [where x = "Var sm"], simp)
    apply (rule Ex_I [where x = "Var sm'"], simp)
    apply (rule Ex_I [where x = "Var sn"], simp)
    apply (rule Ex_I [where x = "Var sn'"], simp)
    apply (simp_all add: SeqQuoteP.simps [of l s _ sl sl' m n sm sm' sn sn'])
    apply ((rule Conj_I)+, blast intro: LstSeqP_Mem)+
    \<comment> \<open>first SeqQuoteP subgoal\<close>
    apply (rule All2_Subset [OF Hyp])
    apply (blast intro!: SUCC_Subset_Ord LstSeqP_OrdP)+
    apply simp
    \<comment> \<open>next SeqQuoteP subgoal\<close>
    apply ((rule Conj_I)+, blast intro: LstSeqP_Mem)+
    apply (rule All2_Subset [OF Hyp], blast)
    apply (auto intro!: SUCC_Subset_Ord LstSeqP_OrdP intro: Trans)
    done
qed

section \<open>The ``special function'' itself\<close>

definition Quote :: "hf \<Rightarrow> hf \<Rightarrow> bool"
  where "Quote x x' \<equiv> \<exists>s k. SeqQuote x x' s k"

subsection \<open>Defining the syntax\<close>

nominal_function QuoteP :: "tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom s \<sharp> (t,u,k); atom k \<sharp> (t,u)\<rbrakk> \<Longrightarrow>
    QuoteP t u = Ex s (Ex k (SeqQuoteP t u (Var s) (Var k)))"
by (auto simp: eqvt_def QuoteP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order


lemma
  shows QuoteP_fresh_iff [simp]: "a \<sharp> QuoteP t u \<longleftrightarrow> a \<sharp> t \<and> a \<sharp> u"  (is ?thesis1)
  and eval_fm_QuoteP [simp]: "eval_fm e (QuoteP t u) \<longleftrightarrow> Quote \<lbrakk>t\<rbrakk>e \<lbrakk>u\<rbrakk>e"  (is ?thesis2)
  and QuoteP_sf [iff]: "Sigma_fm (QuoteP t u)"  (is ?thsf)
proof -
  obtain s::name and k::name  where "atom s \<sharp> (t,u,k)"  "atom k \<sharp> (t,u)"
    by (metis obtain_fresh) 
  thus ?thesis1 ?thesis2 ?thsf
    by (auto simp: Quote_def)
qed

lemma QuoteP_subst [simp]:
  "(QuoteP t u)(j::=w) = QuoteP (subst j w t) (subst j w u)"
proof -
  obtain s::name and k::name  where "atom s \<sharp> (t,u,w,j,k)"  "atom k \<sharp> (t,u,w,j)"
    by (metis obtain_fresh) 
  thus ?thesis
    by (simp add: QuoteP.simps [of s _ _ k]) 
qed

declare QuoteP.simps [simp del]

subsection \<open>Correctness properties\<close>

lemma Quote_0: "Quote 0 0"
  by (auto simp: Quote_def SeqQuote_def intro: BuildSeq2_exI)

lemma QuoteP_Zero: "{} \<turnstile> QuoteP Zero Zero"
  by (auto intro: Sigma_fm_imp_thm [OF QuoteP_sf]
           simp: ground_fm_aux_def supp_conv_fresh Quote_0)

lemma SeqQuoteP_Eats:
  assumes "atom s \<sharp> (k,s1,s2,k1,k2,t1,t2,u1,u2)" "atom k \<sharp> (s1,s2,k1,k2,t1,t2,u1,u2)"
    shows "{SeqQuoteP t1 u1 s1 k1, SeqQuoteP t2 u2 s2 k2} \<turnstile>
           Ex s (Ex k (SeqQuoteP (Eats t1 t2) (Q_Eats u1 u2) (Var s) (Var k)))"
proof -
  obtain km::name and kn::name and j::name and k'::name and l::name 
     and sl::name and sl'::name and m::name and n::name and sm::name 
     and sm'::name and sn::name and sn'::name
   where atoms2:
         "atom km \<sharp> (kn,j,k',l,s1,s2,s,k1,k2,k,t1,t2,u1,u2,sl,sl',m,n,sm,sm',sn,sn')"
         "atom kn \<sharp> (j,k',l,s1,s2,s,k1,k2,k,t1,t2,u1,u2,sl,sl',m,n,sm,sm',sn,sn')"
         "atom j \<sharp> (k',l,s1,s2,s,k1,k2,k,t1,t2,u1,u2,sl,sl',m,n,sm,sm',sn,sn')"
     and atoms: "atom k' \<sharp> (l,s1,s2,s,k1,k2,k,t1,t2,u1,u2,sl,sl',m,n,sm,sm',sn,sn')"
         "atom l \<sharp> (s1,s2,s,k1,k2,k,t1,t2,u1,u2,sl,sl',m,n,sm,sm',sn,sn')"
         "atom sl \<sharp> (s1,s2,s,k1,k2,k,t1,t2,u1,u2,sl',m,n,sm,sm',sn,sn')"
         "atom sl' \<sharp> (s1,s2,s,k1,k2,k,t1,t2,u1,u2,m,n,sm,sm',sn,sn')"
         "atom m \<sharp> (s1,s2,s,k1,k2,k,t1,t2,u1,u2,n,sm,sm',sn,sn')"
         "atom n \<sharp> (s1,s2,s,k1,k2,k,t1,t2,u1,u2,sm,sm',sn,sn')"
         "atom sm \<sharp> (s1,s2,s,k1,k2,k,t1,t2,u1,u2,sm',sn,sn')"
         "atom sm' \<sharp> (s1,s2,s,k1,k2,k,t1,t2,u1,u2,sn,sn')"
         "atom sn \<sharp> (s1,s2,s,k1,k2,k,t1,t2,u1,u2,sn')"
         "atom sn' \<sharp> (s1,s2,s,k1,k2,k,t1,t2,u1,u2)"
    by (metis obtain_fresh) 
  show ?thesis
     using assms atoms
     apply (auto simp: SeqQuoteP.simps [of l "Var s" _ sl sl' m n sm sm' sn sn'])
     apply (rule cut_same [where A="OrdP k1 AND OrdP k2"])
     apply (metis Conj_I SeqQuoteP_imp_OrdP thin1 thin2)
     apply (rule cut_same [OF exists_SeqAppendP [of s s1 "SUCC k1" s2 "SUCC k2"]])
     apply (rule AssumeH Ex_EH Conj_EH | simp)+
     apply (rule cut_same [OF exists_HaddP [where j=k' and x=k1 and y=k2]])
     apply (rule AssumeH Ex_EH Conj_EH | simp)+
     apply (rule Ex_I [where x="Eats (Var s) (HPair (SUCC (SUCC (Var k'))) (HPair (Eats t1 t2) (Q_Eats u1 u2)))"])
     apply (simp_all (no_asm_simp))
     apply (rule Ex_I [where x="SUCC (SUCC (Var k'))"])
     apply simp
     apply (rule Conj_I [OF LstSeqP_SeqAppendP_Eats])
     apply (blast intro: SeqQuoteP_imp_LstSeqP [THEN cut1])+
     proof (rule All2_SUCC_I, simp_all)
       show "{HaddP k1 k2 (Var k'), OrdP k1, OrdP k2, SeqAppendP s1 (SUCC k1) s2 (SUCC k2) (Var s), 
              SeqQuoteP t1 u1 s1 k1, SeqQuoteP t2 u2 s2 k2}
             \<turnstile> Ex sl (Ex sl'
                 (HPair (SUCC (SUCC (Var k'))) (HPair (Var sl) (Var sl')) IN
                  Eats (Var s) (HPair (SUCC (SUCC (Var k'))) (HPair (Eats t1 t2) (Q_Eats u1 u2))) AND
                  (Var sl EQ Zero AND Var sl' EQ Zero OR
                   Ex m (Ex n (Ex sm (Ex sm' (Ex sn (Ex sn'
                    (Var m IN SUCC (SUCC (Var k')) AND
                     Var n IN SUCC (SUCC (Var k')) AND
                     HPair (Var m) (HPair (Var sm) (Var sm')) IN
                     Eats (Var s) (HPair (SUCC (SUCC (Var k'))) (HPair (Eats t1 t2) (Q_Eats u1 u2))) AND
                     HPair (Var n) (HPair (Var sn) (Var sn')) IN
                     Eats (Var s) (HPair (SUCC (SUCC (Var k'))) (HPair (Eats t1 t2) (Q_Eats u1 u2))) AND
                     Var sl EQ Eats (Var sm) (Var sn) AND Var sl' EQ Q_Eats (Var sm') (Var sn'))))))))))"
       \<comment> \<open>verifying the final values\<close>
       apply (rule Ex_I [where x="Eats t1 t2"])
       using assms atoms apply simp
       apply (rule Ex_I [where x="Q_Eats u1 u2"], simp)
       apply (rule Conj_I [OF Mem_Eats_I2 [OF Refl]])
       apply (rule Disj_I2)
       apply (rule Ex_I [where x=k1], simp)
       apply (rule Ex_I [where x="SUCC (Var k')"], simp)
       apply (rule Ex_I [where x=t1], simp)
       apply (rule Ex_I [where x=u1], simp)
       apply (rule Ex_I [where x=t2], simp)
       apply (rule Ex_I [where x=u2], simp)
       apply (rule Conj_I)
       apply (blast intro: HaddP_Mem_I Mem_SUCC_I1)
       apply (rule Conj_I [OF Mem_SUCC_Refl])
       apply (rule Conj_I)
       apply (blast intro: Mem_Eats_I1 SeqAppendP_Mem1 [THEN cut3] Mem_SUCC_Refl 
                SeqQuoteP_imp_LstSeqP [THEN cut1] LstSeqP_imp_Mem)
       apply (blast intro: Mem_Eats_I1 SeqAppendP_Mem2 [THEN cut4] Mem_SUCC_Refl 
                SeqQuoteP_imp_LstSeqP [THEN cut1] LstSeqP_imp_Mem  HaddP_SUCC1 [THEN cut1])
       done
     next
       show "{HaddP k1 k2 (Var k'), OrdP k1, OrdP k2, SeqAppendP s1 (SUCC k1) s2 (SUCC k2) (Var s), 
              SeqQuoteP t1 u1 s1 k1, SeqQuoteP t2 u2 s2 k2} 
             \<turnstile> All2 l (SUCC (SUCC (Var k')))
                 (Ex sl (Ex sl'
                   (HPair (Var l) (HPair (Var sl) (Var sl')) IN
                    Eats (Var s) (HPair (SUCC (SUCC (Var k'))) (HPair (Eats t1 t2) (Q_Eats u1 u2))) AND
                    (Var sl EQ Zero AND Var sl' EQ Zero OR
                     Ex m (Ex n (Ex sm (Ex sm' (Ex sn (Ex sn'
                      (Var m IN Var l AND
                       Var n IN Var l AND
                       HPair (Var m) (HPair (Var sm) (Var sm')) IN
                       Eats (Var s) (HPair (SUCC (SUCC (Var k'))) (HPair (Eats t1 t2) (Q_Eats u1 u2))) AND
                       HPair (Var n) (HPair (Var sn) (Var sn')) IN
                       Eats (Var s) (HPair (SUCC (SUCC (Var k'))) (HPair (Eats t1 t2) (Q_Eats u1 u2))) AND
                       Var sl EQ Eats (Var sm) (Var sn) AND Var sl' EQ Q_Eats (Var sm') (Var sn')))))))))))"
     \<comment> \<open>verifying the sequence buildup\<close>
     apply (rule cut_same [where A="HaddP (SUCC k1) (SUCC k2) (SUCC (SUCC (Var k')))"])
     apply (blast intro: HaddP_SUCC1 [THEN cut1] HaddP_SUCC2 [THEN cut1])
     apply (rule All_I Imp_I)+
     apply (rule HaddP_Mem_cases [where i=j])
     using assms atoms atoms2 apply simp_all
     apply (rule AssumeH)
     apply (blast intro: OrdP_SUCC_I)
     \<comment> \<open>... the sequence buildup via s1\<close>
     apply (simp add: SeqQuoteP.simps [of l s1 _ sl sl' m n sm sm' sn sn'])
     apply (rule AssumeH Ex_EH Conj_EH)+
     apply (rule All2_E [THEN rotate2])
     apply (simp | rule AssumeH Ex_EH Conj_EH)+
     apply (rule Ex_I [where x="Var sl"], simp)
     apply (rule Ex_I [where x="Var sl'"], simp)
     apply (rule Conj_I)
     apply (rule Mem_Eats_I1)
     apply (metis SeqAppendP_Mem1 rotate3 thin2 thin4)
     apply (rule AssumeH Disj_IE1H Ex_EH Conj_EH)+
     apply (rule Ex_I [where x="Var m"], simp)
     apply (rule Ex_I [where x="Var n"], simp)
     apply (rule Ex_I [where x="Var sm"], simp)
     apply (rule Ex_I [where x="Var sm'"], simp)
     apply (rule Ex_I [where x="Var sn"], simp)
     apply (rule Ex_I [where x="Var sn'"], simp_all)
     apply (rule Conj_I, rule AssumeH)+
     apply (blast intro: OrdP_Trans [OF OrdP_SUCC_I] Mem_Eats_I1 [OF SeqAppendP_Mem1 [THEN cut3]] Hyp)
     \<comment> \<open>... the sequence buildup via s2\<close>
     apply (simp add: SeqQuoteP.simps [of l s2 _ sl sl' m n sm sm' sn sn'])
     apply (rule AssumeH Ex_EH Conj_EH)+
     apply (rule All2_E [THEN rotate2])
     apply (simp | rule AssumeH Ex_EH Conj_EH)+
     apply (rule Ex_I [where x="Var sl"], simp)
     apply (rule Ex_I [where x="Var sl'"], simp)
     apply (rule cut_same [where A="OrdP (Var j)"])
     apply (metis HaddP_imp_OrdP rotate2 thin2)
     apply (rule Conj_I)
     apply (blast intro: Mem_Eats_I1 SeqAppendP_Mem2 [THEN cut4]  del: Disj_EH)
     apply (rule AssumeH Disj_IE1H Ex_EH Conj_EH)+
     apply (rule cut_same [OF exists_HaddP [where j=km and x="SUCC k1" and y="Var m"]])
     apply (blast intro: Ord_IN_Ord, simp)
     apply (rule cut_same [OF exists_HaddP [where j=kn and x="SUCC k1" and y="Var n"]])
     apply (metis AssumeH(6) Ord_IN_Ord0 rotate8, simp)
     apply (rule AssumeH Ex_EH Conj_EH | simp)+
     apply (rule Ex_I [where x="Var km"], simp)
     apply (rule Ex_I [where x="Var kn"], simp)
     apply (rule Ex_I [where x="Var sm"], simp)
     apply (rule Ex_I [where x="Var sm'"], simp)
     apply (rule Ex_I [where x="Var sn"], simp)
     apply (rule Ex_I [where x="Var sn'"], simp_all)
     apply (rule Conj_I [OF _ Conj_I])
     apply (blast intro: Hyp OrdP_SUCC_I HaddP_Mem_cancel_left [THEN Iff_MP2_same])
     apply (blast intro: Hyp OrdP_SUCC_I HaddP_Mem_cancel_left [THEN Iff_MP2_same])
     apply (blast intro: Hyp Mem_Eats_I1 SeqAppendP_Mem2 [THEN cut4] OrdP_Trans HaddP_imp_OrdP [THEN cut1])
     done
   qed
qed


lemma QuoteP_Eats: "{QuoteP t1 u1, QuoteP t2 u2} \<turnstile> QuoteP (Eats t1 t2) (Q_Eats u1 u2)"
proof -
  obtain k1::name and s1::name and k2::name and s2::name and k::name and s::name
    where "atom s1 \<sharp> (t1,u1,t2,u2)"             "atom k1 \<sharp> (t1,u1,t2,u2,s1)"  
          "atom s2 \<sharp> (t1,u1,t2,u2,k1,s1)"       "atom k2 \<sharp> (t1,u1,t2,u2,s2,k1,s1)"
          "atom s  \<sharp> (t1,u1,t2,u2,k2,s2,k1,s1)" "atom k  \<sharp> (t1,u1,t2,u2,s,k2,s2,k1,s1)" 
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: QuoteP.simps [of s _ "(Q_Eats u1 u2)" k] 
                   QuoteP.simps [of s1 t1 u1 k1] QuoteP.simps [of s2 t2 u2 k2]
             intro!: SeqQuoteP_Eats [THEN cut2])
qed

lemma exists_QuoteP:
  assumes j: "atom j \<sharp> x"  shows "{} \<turnstile> Ex j (QuoteP x (Var j))"
proof -
  obtain i::name and j'::name and k::name
    where atoms: "atom i \<sharp> (j,x)"  "atom j' \<sharp> (i,j,x)"  "atom (k::name) \<sharp> (i,j,j',x)"
    by (metis obtain_fresh) 
  have "{} \<turnstile> Ex j (QuoteP (Var i) (Var j))" (is "{} \<turnstile> ?scheme")
  proof (rule Ind [of k])
    show "atom k \<sharp> (i, ?scheme)" using atoms
      by simp 
  next
    show "{} \<turnstile> ?scheme(i::=Zero)" using j atoms
      by (auto intro: Ex_I [where x=Zero] simp add: QuoteP_Zero)
  next
    show "{} \<turnstile> All i (All k (?scheme IMP ?scheme(i::=Var k) IMP ?scheme(i::=Eats (Var i) (Var k))))"
      apply (rule All_I Imp_I)+
      using atoms assms 
      apply simp_all
      apply (rule Ex_E)
      apply (rule Ex_E_with_renaming [where i'=j', THEN rotate2], auto)
      apply (rule Ex_I [where x= "Q_Eats (Var j') (Var j)"], auto intro: QuoteP_Eats)
      done
  qed
  hence "{} \<turnstile> (Ex j (QuoteP (Var i) (Var j))) (i::= x)" 
    by (rule Subst) auto
  thus ?thesis 
    using atoms j by auto
qed

lemma QuoteP_imp_ConstP: "{ QuoteP x y } \<turnstile> ConstP y"
proof -
  obtain j::name and j'::name and l::name and s::name and k::name
     and m::name and n::name and sm::name and sn::name and sm'::name and sn'::name
    where atoms: "atom j \<sharp> (x,y,s,k,j',l,m,n,sm,sm',sn,sn')"
             "atom j' \<sharp> (x,y,s,k,l,m,n,sm,sm',sn,sn')"
             "atom l \<sharp> (s,k,m,n,sm,sm',sn,sn')"
             "atom m \<sharp> (s,k,n,sm,sm',sn,sn')" "atom n \<sharp> (s,k,sm,sm',sn,sn')"
             "atom sm \<sharp> (s,k,sm',sn,sn')" "atom sm' \<sharp> (s,k,sn,sn')"
             "atom sn \<sharp> (s,k,sn')" "atom sn' \<sharp> (s,k)" "atom s \<sharp> (k,x,y)" "atom k \<sharp> (x,y)"
    by (metis obtain_fresh)
  have "{OrdP (Var k)}
        \<turnstile> All j (All j' (SeqQuoteP (Var j) (Var j') (Var s) (Var k) IMP ConstP (Var j')))"
        (is "_ \<turnstile> ?scheme")
    proof (rule OrdIndH [where j=l])
      show "atom l \<sharp> (k, ?scheme)" using atoms
        by simp
    next
      show "{} \<turnstile> All k (OrdP (Var k) IMP (All2 l (Var k) (?scheme(k::= Var l)) IMP ?scheme))"
        apply (rule All_I Imp_I)+
        using atoms
        apply (simp_all add: fresh_at_base fresh_finite_set_at_base)
        \<comment> \<open>freshness finally proved!\<close>
        apply (rule cut_same)
        apply (rule cut1 [OF SeqQuoteP_lemma [of m "Var j" "Var j'" "Var s" "Var k" n sm sm' sn sn']], simp_all, blast)        
        apply (rule Imp_I Disj_EH Conj_EH)+
        \<comment> \<open>case 1, Var j EQ Zero\<close>
        apply (rule thin1)
        apply (rule Var_Eq_subst_Iff [THEN Iff_MP_same], simp)
        apply (metis thin0 ConstP_Zero)
        \<comment> \<open>case 2, @{term "Var j EQ Eats (Var sm) (Var sn)"}\<close>
        apply (rule Imp_I Conj_EH Ex_EH)+
        apply simp_all
        apply (rule Var_Eq_subst_Iff [THEN Iff_MP_same, THEN rotate2], simp)
        apply (rule ConstP_Eats [THEN cut2])
        \<comment> \<open>Operand 1. IH for sm\<close>
        apply (rule All2_E [where x="Var m", THEN rotate8], auto)
        apply (rule All_E [where x="Var sm"], simp)
        apply (rule All_E [where x="Var sm'"], auto)
        \<comment> \<open>Operand 2. IH for sm\<close>
        apply (rule All2_E [where x="Var n", THEN rotate8], auto)
        apply (rule All_E [where x="Var sn"], simp)
        apply (rule All_E [where x="Var sn'"], auto)
        done
    qed
  hence "{OrdP(Var k)}
         \<turnstile> (All j' (SeqQuoteP (Var j) (Var j') (Var s) (Var k) IMP ConstP (Var j'))) (j::=x)"
    by (metis All_D)
  hence "{OrdP(Var k)} \<turnstile> All j' (SeqQuoteP x (Var j') (Var s) (Var k) IMP ConstP (Var j'))"
    using atoms by simp
  hence "{OrdP(Var k)} \<turnstile> (SeqQuoteP x (Var j') (Var s) (Var k) IMP ConstP (Var j')) (j'::=y)"
    by (metis All_D)
  hence "{OrdP(Var k)} \<turnstile> SeqQuoteP x y (Var s) (Var k) IMP ConstP y"
    using atoms by simp
  hence "{ SeqQuoteP x y (Var s) (Var k) } \<turnstile> ConstP y"
    by (metis Imp_cut SeqQuoteP_imp_OrdP anti_deduction)
  thus "{ QuoteP x y } \<turnstile> ConstP y" using atoms
    by (auto simp: QuoteP.simps [of s _ _ k])
qed

lemma SeqQuoteP_imp_QuoteP: "{SeqQuoteP t u s k} \<turnstile> QuoteP t u"
proof -
  obtain s'::name and k'::name  where "atom s' \<sharp> (k',t,u,s,k)"  "atom k' \<sharp> (t,u,s,k)"
    by (metis obtain_fresh) 
  thus ?thesis
    apply (simp add: QuoteP.simps [of s' _ _ k'])
    apply (rule Ex_I [where x = s], simp)
    apply (rule Ex_I [where x = k], auto)
    done
qed

lemmas QuoteP_I = SeqQuoteP_imp_QuoteP [THEN cut1]


section \<open>The Operator @{term quote_all}\<close>

subsection \<open>Definition and basic properties\<close>

definition quote_all :: "[perm, name set] \<Rightarrow> fm set"
  where "quote_all p V = {QuoteP (Var i) (Var (p \<bullet> i)) | i. i \<in> V}"

lemma quote_all_empty [simp]: "quote_all p {} = {}"
  by (simp add: quote_all_def)

lemma quote_all_insert [simp]:
  "quote_all p (insert i V) = insert (QuoteP (Var i) (Var (p \<bullet> i))) (quote_all p V)"
  by (auto simp: quote_all_def)

lemma finite_quote_all [simp]: "finite V \<Longrightarrow> finite (quote_all p V)"
  by (induct rule: finite_induct) auto

lemma fresh_quote_all [simp]: "finite V \<Longrightarrow> i \<sharp> quote_all p V \<longleftrightarrow> i \<sharp> V \<and> i \<sharp> p\<bullet>V"
  by (induct rule: finite_induct) (auto simp: fresh_finite_insert)

lemma fresh_quote_all_mem: "\<lbrakk>A \<in> quote_all p V; finite V; i \<sharp> V; i \<sharp> p \<bullet> V\<rbrakk> \<Longrightarrow> i \<sharp> A"
  by (metis Set.set_insert finite_insert finite_quote_all fresh_finite_insert fresh_quote_all)

lemma quote_all_perm_eq:
  assumes "finite V" "atom i \<sharp> (p,V)" "atom i' \<sharp> (p,V)"
    shows "quote_all ((atom i \<rightleftharpoons> atom i') + p) V = quote_all p V"
proof -
  { fix W
    assume w: "W \<subseteq> V"
    have "finite W"
      by (metis \<open>finite V\<close> finite_subset w)
    hence "quote_all ((atom i \<rightleftharpoons> atom i') + p) W = quote_all p W" using w
        apply induction  using assms
        apply (auto simp: fresh_Pair perm_commute)
        apply (metis fresh_finite_set_at_base swap_at_base_simps(3))+
        done}
  thus ?thesis
    by (metis order_refl)
qed


subsection \<open>Transferring theorems to the level of derivability\<close>

context quote_perm
begin

lemma QuoteP_imp_ConstP_F_hyps:
  assumes "Us \<subseteq> Vs" "{ConstP (F i) | i. i \<in> Us} \<turnstile> A"  shows "quote_all p Us \<turnstile> A"
proof -
  show ?thesis using finite_V [OF \<open>Us \<subseteq> Vs\<close>]  assms
  proof (induction arbitrary: A rule: finite_induct)
    case empty thus ?case by simp
  next
    case (insert v Us) thus ?case
      by (auto simp: Collect_disj_Un)
         (metis (lifting) anti_deduction Imp_cut [OF _ QuoteP_imp_ConstP] Disj_I2 F_unfold)
  qed
qed

text\<open>Lemma 8.3\<close>
theorem quote_all_PfP_ssubst:
  assumes \<beta>: "{} \<turnstile> \<beta>"
      and V: "V \<subseteq> Vs"
      and s: "supp \<beta> \<subseteq> atom ` Vs"
    shows    "quote_all p V \<turnstile> PfP (ssubst \<lfloor>\<beta>\<rfloor>V V F)"
proof -
  have "{} \<turnstile> PfP \<lceil>\<beta>\<rceil>"
    by (metis \<beta> proved_iff_proved_PfP)
  hence "{ConstP (F i) | i. i \<in> V} \<turnstile> PfP (ssubst \<lfloor>\<beta>\<rfloor>V V F)"
    by (simp add: PfP_implies_PfP_ssubst V s)
  thus ?thesis
    by (rule QuoteP_imp_ConstP_F_hyps [OF V])
qed

text\<open>Lemma 8.4\<close>
corollary quote_all_MonPon_PfP_ssubst:
  assumes A: "{} \<turnstile> \<alpha> IMP \<beta>"
      and V: "V \<subseteq> Vs"
      and s: "supp \<alpha> \<subseteq> atom ` Vs" "supp \<beta> \<subseteq> atom ` Vs"
    shows    "quote_all p V \<turnstile> PfP (ssubst \<lfloor>\<alpha>\<rfloor>V V F) IMP PfP (ssubst \<lfloor>\<beta>\<rfloor>V V F)"
using quote_all_PfP_ssubst [OF A V] s
  by (auto simp: V vquot_fm_def intro: PfP_implies_ModPon_PfP thin1)

text\<open>Lemma 8.4b\<close>
corollary quote_all_MonPon2_PfP_ssubst:
  assumes A: "{} \<turnstile> \<alpha>1 IMP \<alpha>2 IMP \<beta>"
      and V: "V \<subseteq> Vs"
      and s: "supp \<alpha>1 \<subseteq> atom ` Vs" "supp \<alpha>2 \<subseteq> atom ` Vs" "supp \<beta> \<subseteq> atom ` Vs"
    shows "quote_all p V \<turnstile> PfP (ssubst \<lfloor>\<alpha>1\<rfloor>V V F) IMP PfP (ssubst \<lfloor>\<alpha>2\<rfloor>V V F) IMP PfP (ssubst \<lfloor>\<beta>\<rfloor>V V F)"
using quote_all_PfP_ssubst [OF A V] s
  by (force simp: V vquot_fm_def intro: PfP_implies_ModPon_PfP [OF PfP_implies_ModPon_PfP] thin1)

lemma quote_all_Disj_I1_PfP_ssubst:
  assumes "V \<subseteq> Vs" "supp \<alpha> \<subseteq> atom ` Vs" "supp \<beta> \<subseteq> atom ` Vs"
      and prems: "H \<turnstile> PfP (ssubst \<lfloor>\<alpha>\<rfloor>V V F)" "quote_all p V \<subseteq> H"
    shows "H \<turnstile> PfP (ssubst \<lfloor>\<alpha> OR \<beta>\<rfloor>V V F)"
proof -
  have "{} \<turnstile> \<alpha> IMP (\<alpha> OR \<beta>)"
    by (blast intro: Disj_I1)
  hence "quote_all p V \<turnstile> PfP (ssubst \<lfloor>\<alpha>\<rfloor>V V F) IMP PfP (ssubst \<lfloor>\<alpha> OR \<beta>\<rfloor>V V F)" 
    using assms by (auto simp: quote_all_MonPon_PfP_ssubst)
  thus ?thesis
    by (metis MP_same prems thin)
qed

lemma quote_all_Disj_I2_PfP_ssubst:
  assumes "V \<subseteq> Vs" "supp \<alpha> \<subseteq> atom ` Vs" "supp \<beta> \<subseteq> atom ` Vs"
      and prems: "H \<turnstile> PfP (ssubst \<lfloor>\<beta>\<rfloor>V V F)" "quote_all p V \<subseteq> H"
    shows "H \<turnstile> PfP (ssubst \<lfloor>\<alpha> OR \<beta>\<rfloor>V V F)"
proof -
  have "{} \<turnstile> \<beta> IMP (\<alpha> OR \<beta>)"
    by (blast intro: Disj_I2)
  hence "quote_all p V \<turnstile> PfP (ssubst \<lfloor>\<beta>\<rfloor>V V F) IMP PfP (ssubst \<lfloor>\<alpha> OR \<beta>\<rfloor>V V F)" 
    using assms by (auto simp: quote_all_MonPon_PfP_ssubst)
  thus ?thesis
    by (metis MP_same prems thin)
qed

lemma quote_all_Conj_I_PfP_ssubst:
  assumes "V \<subseteq> Vs" "supp \<alpha> \<subseteq> atom ` Vs" "supp \<beta> \<subseteq> atom ` Vs"
      and prems: "H \<turnstile> PfP (ssubst \<lfloor>\<alpha>\<rfloor>V V F)" "H \<turnstile> PfP (ssubst \<lfloor>\<beta>\<rfloor>V V F)" "quote_all p V \<subseteq> H"
    shows "H \<turnstile> PfP (ssubst \<lfloor>\<alpha> AND \<beta>\<rfloor>V V F)"
proof -
  have "{} \<turnstile> \<alpha> IMP \<beta> IMP (\<alpha> AND \<beta>)"
    by blast
  hence "quote_all p V 
         \<turnstile> PfP (ssubst \<lfloor>\<alpha>\<rfloor>V V F) IMP PfP (ssubst \<lfloor>\<beta>\<rfloor>V V F) IMP PfP (ssubst \<lfloor>\<alpha> AND \<beta>\<rfloor>V V F)" 
    using assms by (auto simp: quote_all_MonPon2_PfP_ssubst)
  thus ?thesis
    by (metis MP_same prems thin)
qed

lemma quote_all_Contra_PfP_ssubst:
  assumes "V \<subseteq> Vs" "supp \<alpha> \<subseteq> atom ` Vs" 
  shows "quote_all p V 
         \<turnstile> PfP (ssubst \<lfloor>\<alpha>\<rfloor>V V F) IMP PfP (ssubst \<lfloor>Neg \<alpha>\<rfloor>V V F) IMP PfP (ssubst \<lfloor>Fls\<rfloor>V V F)"
proof -
  have "{} \<turnstile> \<alpha> IMP Neg \<alpha> IMP Fls"
    by blast
  thus ?thesis
    using assms by (auto simp: quote_all_MonPon2_PfP_ssubst supp_conv_fresh)
qed

lemma fresh_ssubst_dbtm: "\<lbrakk>atom i \<sharp> p\<bullet>V; V \<subseteq> Vs\<rbrakk> \<Longrightarrow> atom i \<sharp> ssubst (vquot_dbtm V t) V F"
  by (induct t rule: dbtm.induct) (auto simp: F_unfold fresh_image permute_set_eq_image)

lemma fresh_ssubst_dbfm: "\<lbrakk>atom i \<sharp> p\<bullet>V; V \<subseteq> Vs\<rbrakk> \<Longrightarrow> atom i \<sharp> ssubst (vquot_dbfm V A) V F"
  by (nominal_induct A rule: dbfm.strong_induct) (auto simp: fresh_ssubst_dbtm)

lemma fresh_ssubst_fm:
  fixes A::fm shows "\<lbrakk>atom i \<sharp> p\<bullet>V; V \<subseteq> Vs\<rbrakk> \<Longrightarrow> atom i \<sharp> ssubst (\<lfloor>A\<rfloor>V) V F"
  by (simp add: fresh_ssubst_dbfm vquot_fm_def) 

end


section \<open>Star Property. Equality and Membership: Lemmas 9.3 and 9.4\<close>

lemma SeqQuoteP_Mem_imp_QMem_and_Subset:
  assumes "atom i \<sharp> (j,j',i',si,ki,sj,kj)" "atom i' \<sharp> (j,j',si,ki,sj,kj)"
          "atom j \<sharp> (j',si,ki,sj,kj)" "atom j' \<sharp> (si,ki,sj,kj)"
          "atom si \<sharp> (ki,sj,kj)" "atom sj \<sharp> (ki,kj)"
  shows "{SeqQuoteP (Var i) (Var i') (Var si) ki, SeqQuoteP (Var j) (Var j') (Var sj) kj}
         \<turnstile> (Var i IN Var j IMP PfP (Q_Mem (Var i') (Var j')))  AND
           (Var i SUBS Var j IMP PfP (Q_Subset (Var i') (Var j')))"
proof -
  obtain k::name and l::name and li::name and lj::name 
     and m::name and n::name and sm::name and sn::name and sm'::name and sn'::name
   where atoms: "atom lj \<sharp> (li,l,i,j,j',i',si,ki,sj,kj,i,i',k,m,n,sm,sm',sn,sn')"  
                "atom li \<sharp> (l,j,j',i,i',si,ki,sj,kj,i,i',k,m,n,sm,sm',sn,sn')"  
                "atom l \<sharp> (j,j',i,i',si,ki,sj,kj,i,i',k,m,n,sm,sm',sn,sn')"  
                "atom k \<sharp> (j,j',i,i',si,ki,sj,kj,m,n,sm,sm',sn,sn')"
                "atom m \<sharp> (j,j',i,i',si,ki,sj,kj,n,sm,sm',sn,sn')"
                "atom n \<sharp> (j,j',i,i',si,ki,sj,kj,sm,sm',sn,sn')"
                "atom sm \<sharp> (j,j',i,i',si,ki,sj,kj,sm',sn,sn')"
                "atom sm' \<sharp> (j,j',i,i',si,ki,sj,kj,sn,sn')"
                "atom sn \<sharp> (j,j',i,i',si,ki,sj,kj,sn')"
                "atom sn' \<sharp> (j,j',i,i',si,ki,sj,kj)"
    by (metis obtain_fresh)
  have "{OrdP(Var k)}
       \<turnstile> All i (All i' (All si (All li (All j (All j' (All sj (All lj
          (SeqQuoteP (Var i) (Var i') (Var si) (Var li) IMP
           SeqQuoteP (Var j) (Var j') (Var sj) (Var lj) IMP
           HaddP (Var li) (Var lj) (Var k) IMP
             ( (Var i IN Var j IMP PfP (Q_Mem (Var i') (Var j')))  AND
               (Var i SUBS Var j IMP PfP (Q_Subset (Var i') (Var j'))))))))))))"
        (is "_ \<turnstile> ?scheme")
    proof (rule OrdIndH [where j=l])
      show "atom l \<sharp> (k, ?scheme)" using atoms
        by simp 
    next
      define V p where "V = {i,j,sm,sn}"
        and "p = (atom i \<rightleftharpoons> atom i') + (atom j \<rightleftharpoons> atom j') +
                 (atom sm \<rightleftharpoons> atom sm') + (atom sn \<rightleftharpoons> atom sn')"
      define F where "F \<equiv> make_F V p"
      interpret qp: quote_perm p V F
        proof unfold_locales
          show "finite V" by (simp add: V_def)
          show "atom ` (p \<bullet> V) \<sharp>* V"
            using atoms assms 
            by (auto simp: p_def V_def F_def make_F_def fresh_star_def fresh_finite_insert)
          show "-p = p"  using assms atoms
            by (simp add: p_def add.assoc perm_self_inverseI fresh_swap fresh_plus_perm)
          show "F \<equiv> make_F V p"
            by (rule F_def)
        qed
      have V_mem: "i \<in> V" "j \<in> V" "sm \<in> V" "sn \<in> V" 
        by (auto simp: V_def)  \<comment> \<open>Part of (2) from page 32\<close>
      have Mem1: "{} \<turnstile> (Var i IN Var sm) IMP (Var i IN Eats (Var sm) (Var sn))"
        by (blast intro: Mem_Eats_I1)
      have Q_Mem1: "quote_all p V
                     \<turnstile> PfP (Q_Mem (Var i') (Var sm')) IMP
                       PfP (Q_Mem (Var i') (Q_Eats (Var sm') (Var sn')))"
         using qp.quote_all_MonPon_PfP_ssubst [OF Mem1 subset_refl] assms atoms V_mem
         by (simp add: vquot_fm_def qp.Vs) (simp add: qp.F_unfold p_def)
      have Mem2: "{} \<turnstile> (Var i EQ Var sn) IMP (Var i IN Eats (Var sm) (Var sn))"
        by (blast intro: Mem_Eats_I2)
      have Q_Mem2: "quote_all p V
                 \<turnstile> PfP (Q_Eq (Var i') (Var sn')) IMP
                   PfP (Q_Mem (Var i') (Q_Eats (Var sm') (Var sn')))"
         using qp.quote_all_MonPon_PfP_ssubst [OF Mem2 subset_refl] assms atoms V_mem
         by (simp add: vquot_fm_def qp.Vs) (simp add: qp.F_unfold p_def)
      have Subs1: "{} \<turnstile> Zero SUBS Var j"
        by blast
      have Q_Subs1: "{QuoteP (Var j) (Var j')} \<turnstile> PfP (Q_Subset Zero (Var j'))"
         using qp.quote_all_PfP_ssubst [OF Subs1, of "{j}"] assms atoms
         by (simp add: qp.ssubst_Subset vquot_tm_def supp_conv_fresh fresh_at_base del: qp.ssubst_single)
            (simp add: qp.F_unfold p_def V_def)
      have Subs2: "{} \<turnstile> Var sm SUBS Var j IMP Var sn IN Var j IMP Eats (Var sm) (Var sn) SUBS Var j"
        by blast
      have Q_Subs2: "quote_all p V 
                     \<turnstile> PfP (Q_Subset (Var sm') (Var j')) IMP
                       PfP (Q_Mem (Var sn') (Var j')) IMP
                       PfP (Q_Subset (Q_Eats (Var sm') (Var sn')) (Var j'))"
         using qp.quote_all_MonPon2_PfP_ssubst [OF Subs2 subset_refl] assms atoms V_mem
         by (simp add: qp.ssubst_Subset vquot_tm_def supp_conv_fresh subset_eq fresh_at_base)
            (simp add: vquot_fm_def qp.F_unfold p_def V_def)
      have Ext: "{} \<turnstile> Var i SUBS Var sn IMP Var sn SUBS Var i IMP Var i EQ Var sn"
        by (blast intro: Equality_I)
      have Q_Ext: "{QuoteP (Var i) (Var i'), QuoteP (Var sn) (Var sn')} 
                   \<turnstile> PfP (Q_Subset (Var i') (Var sn')) IMP
                     PfP (Q_Subset (Var sn') (Var i')) IMP
                     PfP (Q_Eq (Var i') (Var sn'))"
         using qp.quote_all_MonPon2_PfP_ssubst [OF Ext, of "{i,sn}"] assms atoms
         by (simp add: qp.ssubst_Subset vquot_tm_def supp_conv_fresh subset_eq fresh_at_base 
                  del: qp.ssubst_single)
            (simp add: vquot_fm_def qp.F_unfold p_def V_def)
      show "{} \<turnstile> All k (OrdP (Var k) IMP (All2 l (Var k) (?scheme(k::= Var l)) IMP ?scheme))"
        apply (rule All_I Imp_I)+
        using atoms assms 
        apply simp_all
        apply (rule cut_same [where A = "QuoteP (Var i) (Var i')"])
        apply (blast intro: QuoteP_I)
        apply (rule cut_same [where A = "QuoteP (Var j) (Var j')"])
        apply (blast intro: QuoteP_I)
        apply (rule rotate6)
        apply (rule Conj_I)
        \<comment> \<open>@{term"Var i IN Var j IMP PfP (Q_Mem (Var i') (Var j'))"}\<close>
        apply (rule cut_same)
        apply (rule cut1 [OF SeqQuoteP_lemma [of m "Var j" "Var j'" "Var sj" "Var lj" n sm sm' sn sn']], simp_all, blast)
        apply (rule Imp_I Disj_EH Conj_EH)+
        \<comment> \<open>case 1, @{term "Var j EQ Zero"}\<close>
        apply (rule cut_same [where A = "Var i IN Zero"])
        apply (blast intro: Mem_cong [THEN Iff_MP_same], blast)
        \<comment> \<open>case 2, @{term "Var j EQ Eats (Var sm) (Var sn)"}\<close>
        apply (rule Imp_I Conj_EH Ex_EH)+
        apply simp_all
        apply (rule Var_Eq_subst_Iff [THEN rotate2, THEN Iff_MP_same], simp)
        apply (rule cut_same [where A = "QuoteP (Var sm) (Var sm')"])
        apply (blast intro: QuoteP_I)
        apply (rule cut_same [where A = "QuoteP (Var sn) (Var sn')"])
        apply (blast intro: QuoteP_I)
        apply (rule cut_same [where A = "Var i IN Eats (Var sm) (Var sn)"])
        apply (rule Mem_cong [OF Refl, THEN Iff_MP_same])
        apply (rule AssumeH Mem_Eats_E)+
        \<comment> \<open>Eats case 1. IH for sm\<close>
        apply (rule cut_same [where A = "OrdP (Var m)"])
        apply (blast intro: Hyp Ord_IN_Ord SeqQuoteP_imp_OrdP [THEN cut1])
        apply (rule cut_same [OF exists_HaddP [where j=l and x="Var li" and y="Var m"]])
        apply auto
        apply (rule All2_E [where x="Var l", THEN rotate13], simp_all)
        apply (blast intro: Hyp HaddP_Mem_cancel_left [THEN Iff_MP2_same] SeqQuoteP_imp_OrdP [THEN cut1])
        apply (rule All_E [where x="Var i"], simp)
        apply (rule All_E [where x="Var i'"], simp)
        apply (rule All_E [where x="Var si"], simp)
        apply (rule All_E [where x="Var li"], simp)
        apply (rule All_E [where x="Var sm"], simp)
        apply (rule All_E [where x="Var sm'"], simp)
        apply (rule All_E [where x="Var sj"], simp)
        apply (rule All_E [where x="Var m"], simp)
        apply (force intro: MP_thin [OF Q_Mem1] simp add: V_def p_def)
        \<comment> \<open>Eats case 2\<close>
        apply (rule rotate13)
        apply (rule cut_same [where A = "OrdP (Var n)"])
        apply (blast intro: Hyp Ord_IN_Ord SeqQuoteP_imp_OrdP [THEN cut1])
        apply (rule cut_same [OF exists_HaddP [where j=l and x="Var li" and y="Var n"]])
        apply auto
        apply (rule MP_same)
        apply (rule Q_Mem2 [THEN thin])
        apply (simp add: V_def p_def)
        apply (rule MP_same)
        apply (rule MP_same)
        apply (rule Q_Ext [THEN thin])
        apply (simp add: V_def p_def)
        \<comment> \<open>@{term"PfP (Q_Subset (Var i') (Var sn'))"}\<close>
        apply (rule All2_E [where x="Var l", THEN rotate14], simp_all)
        apply (blast intro: Hyp HaddP_Mem_cancel_left [THEN Iff_MP2_same] SeqQuoteP_imp_OrdP [THEN cut1])
        apply (rule All_E [where x="Var i"], simp)
        apply (rule All_E [where x="Var i'"], simp)
        apply (rule All_E [where x="Var si"], simp)
        apply (rule All_E [where x="Var li"], simp)
        apply (rule All_E [where x="Var sn"], simp)
        apply (rule All_E [where x="Var sn'"], simp)
        apply (rule All_E [where x="Var sj"], simp)
        apply (rule All_E [where x="Var n"], simp)
        apply (rule Imp_E, blast intro: Hyp)+
        apply (rule Conj_E)
        apply (rule thin1)
        apply (blast intro!: Imp_E EQ_imp_SUBS [THEN cut1])
        \<comment> \<open>@{term"PfP (Q_Subset (Var sn') (Var i'))"}\<close>
        apply (rule All2_E [where x="Var l", THEN rotate14], simp_all)
        apply (blast intro: Hyp HaddP_Mem_cancel_left [THEN Iff_MP2_same] SeqQuoteP_imp_OrdP [THEN cut1])
        apply (rule All_E [where x="Var sn"], simp)
        apply (rule All_E [where x="Var sn'"], simp)
        apply (rule All_E [where x="Var sj"], simp)
        apply (rule All_E [where x="Var n"], simp)
        apply (rule All_E [where x="Var i"], simp)
        apply (rule All_E [where x="Var i'"], simp)
        apply (rule All_E [where x="Var si"], simp)
        apply (rule All_E [where x="Var li"], simp)
        apply (rule Imp_E, blast intro: Hyp)+
        apply (rule Imp_E)
        apply (blast intro: Hyp HaddP_commute [THEN cut2] SeqQuoteP_imp_OrdP [THEN cut1])
        apply (rule Conj_E)
        apply (rule thin1)
        apply (blast intro!: Imp_E EQ_imp_SUBS2 [THEN cut1])
        \<comment> \<open>@{term"Var i SUBS Var j IMP PfP (Q_Subset (Var i') (Var j'))"}\<close>
        apply (rule cut_same)
        apply (rule cut1 [OF SeqQuoteP_lemma [of m "Var i" "Var i'" "Var si" "Var li" n sm sm' sn sn']], simp_all, blast)
        apply (rule Imp_I Disj_EH Conj_EH)+
        \<comment> \<open>case 1, Var i EQ Zero\<close>
        apply (rule cut_same [where A = "PfP (Q_Subset Zero (Var j'))"])
        apply (blast intro: Q_Subs1 [THEN cut1] SeqQuoteP_imp_QuoteP [THEN cut1])
        apply (force intro: Var_Eq_subst_Iff [THEN Iff_MP_same, THEN rotate3])
        \<comment> \<open>case 2, @{term "Var i EQ Eats (Var sm) (Var sn)"}\<close>
        apply (rule Conj_EH Ex_EH)+
        apply simp_all
        apply (rule cut_same [where A = "OrdP (Var lj)"])
        apply (blast intro: Hyp SeqQuoteP_imp_OrdP [THEN cut1])
        apply (rule Var_Eq_subst_Iff [THEN Iff_MP_same, THEN rotate3], simp)
        apply (rule cut_same [where A = "QuoteP (Var sm) (Var sm')"])
        apply (blast intro: QuoteP_I)
        apply (rule cut_same [where A = "QuoteP (Var sn) (Var sn')"])
        apply (blast intro: QuoteP_I)
        apply (rule cut_same [where A = "Eats (Var sm) (Var sn) SUBS Var j"])
        apply (rule Subset_cong [OF _ Refl, THEN Iff_MP_same])
        apply (rule AssumeH Mem_Eats_E)+
        \<comment> \<open>Eats case split\<close>
        apply (rule Eats_Subset_E)
        apply (rule rotate15)
        apply (rule MP_same [THEN MP_same])
        apply (rule Q_Subs2 [THEN thin])
        apply (simp add: V_def p_def)
        \<comment> \<open>Eats case 1: @{term "PfP (Q_Subset (Var sm') (Var j'))"}\<close>
        apply (rule cut_same [OF exists_HaddP [where j=l and x="Var m" and y="Var lj"]])
        apply (rule AssumeH Ex_EH Conj_EH | simp)+
        \<comment> \<open>IH for sm\<close>
        apply (rule All2_E [where x="Var l", THEN rotate15], simp_all)
        apply (blast intro: Hyp HaddP_Mem_cancel_right_Mem SeqQuoteP_imp_OrdP [THEN cut1])
        apply (rule All_E [where x="Var sm"], simp)
        apply (rule All_E [where x="Var sm'"], simp)
        apply (rule All_E [where x="Var si"], simp)
        apply (rule All_E [where x="Var m"], simp)
        apply (rule All_E [where x="Var j"], simp)
        apply (rule All_E [where x="Var j'"], simp)
        apply (rule All_E [where x="Var sj"], simp)
        apply (rule All_E [where x="Var lj"], simp)
        apply (blast intro: thin1 Imp_E)
        \<comment> \<open>Eats case 2: @{term "PfP (Q_Mem (Var sn') (Var j'))"}\<close>
        apply (rule cut_same [OF exists_HaddP [where j=l and x="Var n" and y="Var lj"]])
        apply (rule AssumeH Ex_EH Conj_EH | simp)+
        \<comment> \<open>IH for sn\<close>
        apply (rule All2_E [where x="Var l", THEN rotate15], simp_all)
        apply (blast intro: Hyp HaddP_Mem_cancel_right_Mem SeqQuoteP_imp_OrdP [THEN cut1])
        apply (rule All_E [where x="Var sn"], simp)
        apply (rule All_E [where x="Var sn'"], simp)
        apply (rule All_E [where x="Var si"], simp)
        apply (rule All_E [where x="Var n"], simp)
        apply (rule All_E [where x="Var j"], simp)
        apply (rule All_E [where x="Var j'"], simp)
        apply (rule All_E [where x="Var sj"], simp)
        apply (rule All_E [where x="Var lj"], simp)
        apply (blast intro: Hyp Imp_E)
        done
    qed
  hence p1: "{OrdP(Var k)}
             \<turnstile> (All i' (All si (All li
                  (All j (All j' (All sj (All lj
                        (SeqQuoteP (Var i) (Var i') (Var si) (Var li) IMP
                         SeqQuoteP (Var j) (Var j') (Var sj) (Var lj) IMP
                         HaddP (Var li) (Var lj) (Var k) IMP
                         (Var i IN Var j IMP PfP (Q_Mem (Var i') (Var j'))) AND
                         (Var i SUBS Var j IMP PfP (Q_Subset (Var i') (Var j'))))))))))) (i::= Var i)"
        by (metis All_D)
  have p2: "{OrdP(Var k)}
            \<turnstile> (All si (All li
                (All j (All j' (All sj (All lj
                      (SeqQuoteP (Var i) (Var i') (Var si) (Var li) IMP
                       SeqQuoteP (Var j) (Var j') (Var sj) (Var lj) IMP
                       HaddP (Var li) (Var lj) (Var k) IMP
                       (Var i IN Var j IMP PfP (Q_Mem (Var i') (Var j'))) AND
                       (Var i SUBS Var j IMP PfP (Q_Subset (Var i') (Var j'))))))))))(i'::= Var i')"
    apply (rule All_D)
    using atoms p1 by simp
  have p3: "{OrdP(Var k)}
            \<turnstile> (All li
              (All j (All j' (All sj (All lj
                    (SeqQuoteP (Var i) (Var i') (Var si) (Var li) IMP
                     SeqQuoteP (Var j) (Var j') (Var sj) (Var lj) IMP
                     HaddP (Var li) (Var lj) (Var k) IMP
                     (Var i IN Var j IMP PfP (Q_Mem (Var i') (Var j'))) AND
                     (Var i SUBS Var j IMP PfP (Q_Subset (Var i') (Var j'))))))))) (si::= Var si)"
    apply (rule All_D)
    using atoms p2 by simp
  have p4: "{OrdP(Var k)}
            \<turnstile> (All j (All j' (All sj (All lj
                    (SeqQuoteP (Var i) (Var i') (Var si) (Var li) IMP
                     SeqQuoteP (Var j) (Var j') (Var sj) (Var lj) IMP
                     HaddP (Var li) (Var lj) (Var k) IMP
                     (Var i IN Var j IMP PfP (Q_Mem (Var i') (Var j'))) AND
                     (Var i SUBS Var j IMP PfP (Q_Subset (Var i') (Var j')))))))) (li::= ki)"
    apply (rule All_D)
    using atoms p3 by simp
  have p5: "{OrdP(Var k)}
            \<turnstile> (All j' (All sj (All lj
                (SeqQuoteP (Var i) (Var i') (Var si) ki IMP
                 SeqQuoteP (Var j) (Var j') (Var sj) (Var lj) IMP
                 HaddP ki (Var lj) (Var k) IMP
                 (Var i IN Var j IMP PfP (Q_Mem (Var i') (Var j'))) AND
                 (Var i SUBS Var j IMP PfP (Q_Subset (Var i') (Var j'))))))) (j::= Var j)"
    apply (rule All_D)
    using atoms assms p4 by simp
  have p6: "{OrdP(Var k)}
            \<turnstile> (All sj (All lj
                  (SeqQuoteP (Var i) (Var i') (Var si) ki IMP
                   SeqQuoteP (Var j) (Var j') (Var sj) (Var lj) IMP
                   HaddP ki (Var lj) (Var k) IMP
                   (Var i IN Var j IMP PfP (Q_Mem (Var i') (Var j'))) AND
                   (Var i SUBS Var j IMP PfP (Q_Subset (Var i') (Var j')))))) (j'::= Var j')"
    apply (rule All_D)
    using atoms p5 by simp
  have p7: "{OrdP(Var k)}
            \<turnstile> (All lj (SeqQuoteP (Var i) (Var i') (Var si) ki IMP
                       SeqQuoteP (Var j) (Var j') (Var sj) (Var lj) IMP
                       HaddP ki (Var lj) (Var k) IMP
                       (Var i IN Var j IMP PfP (Q_Mem (Var i') (Var j'))) AND
                       (Var i SUBS Var j IMP PfP (Q_Subset (Var i') (Var j'))))) (sj::= Var sj)"
    apply (rule All_D)
    using atoms p6 by simp
  have p8: "{OrdP(Var k)}
            \<turnstile> (SeqQuoteP (Var i) (Var i') (Var si) ki IMP
               SeqQuoteP (Var j) (Var j') (Var sj) (Var lj) IMP
               HaddP ki (Var lj) (Var k) IMP
               (Var i IN Var j IMP PfP (Q_Mem (Var i') (Var j'))) AND
               (Var i SUBS Var j IMP PfP (Q_Subset (Var i') (Var j')))) (lj::= kj)"
    apply (rule All_D)
    using atoms p7 by simp
  hence p9: "{OrdP(Var k)}
             \<turnstile> SeqQuoteP (Var i) (Var i') (Var si) ki IMP
               SeqQuoteP (Var j) (Var j') (Var sj) kj IMP
               HaddP ki kj (Var k) IMP
               (Var i IN Var j IMP PfP (Q_Mem (Var i') (Var j'))) AND
               (Var i SUBS Var j IMP PfP (Q_Subset (Var i') (Var j')))"
    using assms atoms by simp
  have p10:  "{ HaddP ki kj (Var k),
               SeqQuoteP (Var i) (Var i') (Var si) ki,
               SeqQuoteP (Var j) (Var j') (Var sj) kj, OrdP (Var k) }
             \<turnstile> (Var i IN Var j IMP PfP (Q_Mem (Var i') (Var j'))) AND
               (Var i SUBS Var j IMP PfP (Q_Subset (Var i') (Var j')))"
    apply (rule MP_same [THEN MP_same [THEN MP_same]])
    apply (rule p9 [THEN thin])
    apply (auto intro: MP_same)
    done
  show ?thesis 
    apply (rule cut_same [OF exists_HaddP [where j=k and x=ki and y=kj]])
    apply (metis SeqQuoteP_imp_OrdP thin1)
    prefer 2
    apply (rule Ex_E)
    apply (rule p10 [THEN cut4])
    using assms atoms
    apply (auto intro: HaddP_OrdP SeqQuoteP_imp_OrdP [THEN cut1])
    done
qed


lemma 
  assumes "atom i \<sharp> (j,j',i')" "atom i' \<sharp> (j,j')" "atom j \<sharp> (j')" 
  shows QuoteP_Mem_imp_QMem:
        "{QuoteP (Var i) (Var i'), QuoteP (Var j) (Var j'), Var i IN Var j}
         \<turnstile> PfP (Q_Mem (Var i') (Var j'))"     (is ?thesis1)
    and QuoteP_Mem_imp_QSubset:
        "{QuoteP (Var i) (Var i'), QuoteP (Var j) (Var j'), Var i SUBS Var j}
         \<turnstile> PfP (Q_Subset (Var i') (Var j'))"  (is ?thesis2)
proof -
  obtain si::name and ki::name and sj::name and kj::name
    where atoms: "atom si \<sharp> (ki,sj,kj,i,j,j',i')"  "atom ki \<sharp> (sj,kj,i,j,j',i')"
                 "atom sj \<sharp> (kj,i,j,j',i')"  "atom kj \<sharp> (i,j,j',i')"
    by (metis obtain_fresh) 
  hence C:  "{QuoteP (Var i) (Var i'), QuoteP (Var j) (Var j')}
             \<turnstile> (Var i IN Var j IMP PfP (Q_Mem (Var i') (Var j')))  AND
               (Var i SUBS Var j IMP PfP (Q_Subset (Var i') (Var j')))"
    using assms 
    by (auto simp: QuoteP.simps [of si "Var i" _ ki] QuoteP.simps [of sj "Var j" _ kj]
             intro!: SeqQuoteP_Mem_imp_QMem_and_Subset del: Conj_I)
  show ?thesis1
    by (best intro: Conj_E1 [OF C, THEN MP_thin])
  show ?thesis2
    by (best intro: Conj_E2 [OF C, THEN MP_thin])
qed


section \<open>Star Property. Universal Quantifier: Lemma 9.7\<close>

lemma (in quote_perm) SeqQuoteP_Mem_imp_All2:
  assumes IH: "insert (QuoteP (Var i) (Var i')) (quote_all p Vs) 
               \<turnstile> \<alpha> IMP PfP (ssubst \<lfloor>\<alpha>\<rfloor>(insert i Vs) (insert i Vs) Fi)"
      and sp: "supp \<alpha> - {atom i} \<subseteq> atom ` Vs"
      and j: "j \<in> Vs" and j': "p \<bullet> j = j'"
      and pi: "pi = (atom i \<rightleftharpoons> atom i') + p" 
      and Fi: "Fi = make_F (insert i Vs) pi"
      and atoms: "atom i \<sharp> (j,j',s,k,p)" "atom i' \<sharp> (i,p,\<alpha>)" 
                 "atom j \<sharp> (j',s,k,\<alpha>)" "atom j' \<sharp> (s,k,\<alpha>)" 
                 "atom s \<sharp> (k,\<alpha>)" "atom k \<sharp> (\<alpha>,p)"
  shows "insert (SeqQuoteP (Var j) (Var j') (Var s) (Var k)) (quote_all p (Vs-{j}))
         \<turnstile> All2 i (Var j) \<alpha> IMP PfP (ssubst \<lfloor>All2 i (Var j) \<alpha>\<rfloor>Vs Vs F)"
proof -
  have pj' [simp]: "p \<bullet> j' = j" using pinv j'
    by (metis permute_minus_cancel(2))
  have [simp]: "F j = Var j'" using j j' 
    by (auto simp: F_unfold)
  hence i': "atom i' \<sharp> Vs" using atoms
    by (auto simp: Vs)
  have fresh_ss [simp]: "\<And>i A::fm. atom i \<sharp> p \<Longrightarrow> atom i \<sharp> ssubst (\<lfloor>A\<rfloor>Vs) Vs F"
    by (simp add: vquot_fm_def fresh_ssubst_dbfm)
  obtain l::name and m::name and n::name and sm::name and sn::name and sm'::name and sn'::name
    where atoms': "atom l \<sharp> (p,\<alpha>,i,j,j',s,k,m,n,sm,sm',sn,sn')"
       "atom m \<sharp> (p,\<alpha>,i,j,j',s,k,n,sm,sm',sn,sn')" "atom n \<sharp> (p,\<alpha>,i,j,j',s,k,sm,sm',sn,sn')"
       "atom sm \<sharp> (p,\<alpha>,i,j,j',s,k,sm',sn,sn')" "atom sm' \<sharp> (p,\<alpha>,i,j,j',s,k,sn,sn')"
       "atom sn \<sharp> (p,\<alpha>,i,j,j',s,k,sn')" "atom sn' \<sharp> (p,\<alpha>,i,j,j',s,k)"
    by (metis obtain_fresh)
  define V' p'
    where "V' = {sm,sn} \<union> Vs"
      and "p' = (atom sm \<rightleftharpoons> atom sm') + (atom sn \<rightleftharpoons> atom sn') + p"
  define F' where "F' \<equiv> make_F V' p'"
  interpret qp': quote_perm p' V' F'
    proof unfold_locales 
      show "finite V'" by (simp add: V'_def)
      show "atom ` (p' \<bullet> V') \<sharp>* V'"
        using atoms atoms' p
        by (auto simp: p'_def V'_def swap_fresh_fresh fresh_at_base_permI 
                fresh_star_finite_insert fresh_finite_insert atom_fresh_star_atom_set_conv)
      show "F' \<equiv> make_F V' p'"
        by (rule F'_def)
      show "- p' = p'" using atoms atoms' pinv
        by (simp add: p'_def add.assoc perm_self_inverseI fresh_swap fresh_plus_perm)
    qed
  have All2_Zero: "{} \<turnstile> All2 i Zero \<alpha>"
    by auto
  have Q_All2_Zero: 
    "quote_all p Vs \<turnstile> PfP (Q_All (Q_Imp (Q_Mem (Q_Ind Zero) Zero) 
                                (ssubst (vquot_dbfm Vs (trans_fm [i] \<alpha>)) Vs F)))"
         using quote_all_PfP_ssubst [OF All2_Zero] assms
         by (force simp add: vquot_fm_def supp_conv_fresh)
  have All2_Eats: "{} \<turnstile> All2 i (Var sm) \<alpha> IMP \<alpha>(i::=Var sn) IMP All2 i (Eats (Var sm) (Var sn)) \<alpha>"
    using atoms'  apply auto
    apply (rule Ex_I [where x = "Var i"], auto)
    apply (rule rotate2)
    apply (blast intro: ContraProve Var_Eq_imp_subst_Iff [THEN Iff_MP_same])
    done
  have [simp]: "F' sm = Var sm'" "F' sn = Var sn'" using atoms' 
    by (auto simp: V'_def p'_def qp'.F_unfold swap_fresh_fresh fresh_at_base_permI)
  have smn' [simp]: "sm \<in> V'" "sn \<in> V'" "sm \<notin> Vs" "sn \<notin> Vs" using atoms' 
    by (auto simp: V'_def fresh_finite_set_at_base [symmetric])
  hence Q_All2_Eats: "quote_all p' V'
                      \<turnstile> PfP (ssubst \<lfloor>All2 i (Var sm) \<alpha>\<rfloor>V' V' F') IMP
                        PfP (ssubst \<lfloor>\<alpha>(i::=Var sn)\<rfloor>V' V' F') IMP 
                        PfP (ssubst \<lfloor>All2 i (Eats (Var sm) (Var sn)) \<alpha>\<rfloor>V' V' F')"
     using sp  qp'.quote_all_MonPon2_PfP_ssubst [OF All2_Eats subset_refl] 
     by (simp add: supp_conv_fresh subset_eq V'_def)
        (metis Diff_iff empty_iff fresh_ineq_at_base insertE mem_Collect_eq)
  interpret qpi: quote_perm pi "insert i Vs" Fi
    unfolding pi
    apply (rule qp_insert) using atoms
    apply (auto simp: Fi pi)
    done
  have F'_eq_F: "\<And>name. name \<in> Vs \<Longrightarrow> F' name = F name"
    using atoms'
    by (auto simp: F_unfold qp'.F_unfold p'_def swap_fresh_fresh V'_def fresh_pj)
  { fix t::dbtm
    assume "supp t \<subseteq> atom ` V'" "supp t \<subseteq> atom ` Vs"
    hence "ssubst (vquot_dbtm V' t) V' F' = ssubst (vquot_dbtm Vs t) Vs F"
      by (induction t rule: dbtm.induct) (auto simp: F'_eq_F)
  } note ssubst_v_tm = this
  { fix A::dbfm
    assume "supp A \<subseteq> atom ` V'" "supp A \<subseteq> atom ` Vs"
    hence "ssubst (vquot_dbfm V' A) V' F' = ssubst (vquot_dbfm Vs A) Vs F"
      by (induction A rule: dbfm.induct) (auto simp: ssubst_v_tm F'_eq_F)
  } note ssubst_v_fm = this
  have ss_noprimes: "ssubst (vquot_dbfm V' (trans_fm [i] \<alpha>)) V' F' = 
                     ssubst (vquot_dbfm Vs (trans_fm [i] \<alpha>)) Vs F"
    apply (rule ssubst_v_fm)
    using sp  apply (auto simp: V'_def supp_conv_fresh)
    done
  { fix t::dbtm
    assume "supp t - {atom i} \<subseteq> atom ` Vs"
    hence "subst i' (Var sn') (ssubst (vquot_dbtm (insert i Vs) t) (insert i Vs) Fi) =
           ssubst (vquot_dbtm V' (subst_dbtm (DBVar sn) i t)) V' F'"
      apply (induction t rule: dbtm.induct)
      using atoms atoms' 
      apply (auto simp: vquot_tm_def pi V'_def qpi.F_unfold qp'.F_unfold p'_def fresh_pj swap_fresh_fresh fresh_at_base_permI)
      done
  } note perm_v_tm = this
  { fix A::dbfm
    assume "supp A - {atom i} \<subseteq> atom ` Vs"
    hence "subst i' (Var sn') (ssubst (vquot_dbfm (insert i Vs) A) (insert i Vs) Fi) =
           ssubst (vquot_dbfm V' (subst_dbfm (DBVar sn) i A)) V' F'"
      by (induct A rule: dbfm.induct) (auto simp: Un_Diff perm_v_tm)
  } note perm_v_fm = this
  have "quote_all p Vs \<turnstile> QuoteP (Var i) (Var i') IMP 
                 (\<alpha> IMP PfP (ssubst \<lfloor>\<alpha>\<rfloor>(insert i Vs) (insert i Vs) Fi))"
    using IH by auto
  hence "quote_all p Vs 
         \<turnstile> (QuoteP (Var i) (Var i') IMP 
                 (\<alpha> IMP PfP (ssubst \<lfloor>\<alpha>\<rfloor>(insert i Vs) (insert i Vs) Fi))) (i'::=Var sn')"
    using atoms IH
    by (force intro!: Subst elim!: fresh_quote_all_mem)
  hence "quote_all p Vs 
         \<turnstile> QuoteP (Var i) (Var sn') IMP 
           (\<alpha> IMP PfP (subst i' (Var sn') (ssubst \<lfloor>\<alpha>\<rfloor>(insert i Vs) (insert i Vs) Fi)))"
    using atoms by simp
  moreover have "subst i' (Var sn') (ssubst \<lfloor>\<alpha>\<rfloor>(insert i Vs) (insert i Vs) Fi)
                 = ssubst \<lfloor>\<alpha>(i::=Var sn)\<rfloor>V' V' F'"
    using sp
    by (auto simp: vquot_fm_def perm_v_fm supp_conv_fresh subst_fm_trans_commute [symmetric])
  ultimately 
  have "quote_all p Vs 
         \<turnstile> QuoteP (Var i) (Var sn') IMP (\<alpha> IMP PfP (ssubst \<lfloor>\<alpha>(i::=Var sn)\<rfloor>V' V' F'))"
    by simp
  hence "quote_all p Vs 
         \<turnstile> (QuoteP (Var i) (Var sn') IMP (\<alpha> IMP PfP (ssubst \<lfloor>\<alpha>(i::=Var sn)\<rfloor>V' V' F'))) (i::=Var sn)"
    using \<open>atom i \<sharp> _\<close>
    by (force intro!: Subst elim!: fresh_quote_all_mem)
  hence "quote_all p Vs 
         \<turnstile> (QuoteP (Var sn) (Var sn') IMP 
           (\<alpha>(i::=Var sn) IMP PfP (subst i (Var sn) (ssubst \<lfloor>\<alpha>(i::=Var sn)\<rfloor>V' V' F'))))"
    using atoms atoms' by simp
  moreover have "subst i (Var sn) (ssubst \<lfloor>\<alpha>(i::=Var sn)\<rfloor>V' V' F')
                 = ssubst \<lfloor>\<alpha>(i::=Var sn)\<rfloor>V' V' F'"
    using atoms atoms' i'
    by (auto simp: swap_fresh_fresh fresh_at_base_permI p'_def 
             intro!: forget_subst_tm [OF qp'.fresh_ssubst'])
  ultimately 
  have "quote_all p Vs 
         \<turnstile> QuoteP (Var sn) (Var sn') IMP (\<alpha>(i::=Var sn) IMP PfP (ssubst \<lfloor>\<alpha>(i::=Var sn)\<rfloor>V' V' F'))"
    using atoms atoms' by simp
  hence star0: "insert (QuoteP (Var sn) (Var sn')) (quote_all p Vs) 
                \<turnstile> \<alpha>(i::=Var sn) IMP PfP (ssubst \<lfloor>\<alpha>(i::=Var sn)\<rfloor>V' V' F')"
    by (rule anti_deduction)
  have subst_i_star: "quote_all p' V' \<turnstile> \<alpha>(i::=Var sn) IMP PfP (ssubst \<lfloor>\<alpha>(i::=Var sn)\<rfloor>V' V' F')"
    apply (rule thin [OF star0])
    using atoms'
    apply (force simp: V'_def p'_def fresh_swap fresh_plus_perm fresh_at_base_permI add.assoc 
                       quote_all_perm_eq)
    done
  have "insert (OrdP (Var k)) (quote_all p (Vs-{j}))
        \<turnstile> All j (All j' (SeqQuoteP (Var j) (Var j') (Var s) (Var k) IMP
                         All2 i (Var j) \<alpha> IMP PfP (ssubst \<lfloor>All2 i (Var j) \<alpha>\<rfloor>Vs Vs F)))"
        (is "_ \<turnstile> ?scheme")
    proof (rule OrdIndH [where j=l])
      show "atom l \<sharp> (k, ?scheme)" using atoms atoms' j j' fresh_pVs
        by (simp add: fresh_Pair F_unfold)
    next
      have substj: "\<And>t j. atom j \<sharp> \<alpha> \<Longrightarrow> atom (p \<bullet> j) \<sharp> \<alpha> \<Longrightarrow> 
                           subst j t (ssubst (vquot_dbfm Vs (trans_fm [i] \<alpha>)) Vs F) = 
                           ssubst (vquot_dbfm Vs (trans_fm [i] \<alpha>)) Vs F"
        by (auto simp: fresh_ssubst')
      { fix W 
        assume W: "W \<subseteq> Vs"
        hence "finite W" by (metis Vs infinite_super)
        hence "quote_all p' W = quote_all p W" using W
        proof (induction)
          case empty thus ?case
            by simp
        next
          case (insert w W) 
          hence "w \<in> Vs" "atom sm \<sharp> p \<bullet> Vs" "atom sm' \<sharp> p \<bullet> Vs" "atom sn \<sharp> p \<bullet> Vs" "atom sn' \<sharp> p \<bullet> Vs"
            using atoms' Vs by (auto simp: fresh_pVs)
          hence "atom sm \<sharp> p \<bullet> w" "atom sm' \<sharp> p \<bullet> w" "atom sn \<sharp> p \<bullet> w" "atom sn' \<sharp> p \<bullet> w"
            by (metis Vs fresh_at_base(2) fresh_finite_set_at_base fresh_permute_left)+
          thus ?case using insert 
          by (simp add: p'_def swap_fresh_fresh)
        qed 
      }
      hence "quote_all p' Vs = quote_all p Vs"
        by (metis subset_refl)
      also have "... = insert (QuoteP (Var j) (Var j')) (quote_all p (Vs - {j}))"
        using j j' by (auto simp: quote_all_def)
      finally have "quote_all p' V' = 
                    {QuoteP (Var sn) (Var sn'), QuoteP (Var sm) (Var sm')} \<union> 
                    insert (QuoteP (Var j) (Var j')) (quote_all p (Vs - {j}))"
        using atoms'
        by (auto simp: p'_def V'_def fresh_at_base_permI Collect_disj_Un)
      also have "... = {QuoteP (Var sn) (Var sn'), QuoteP (Var sm) (Var sm'), QuoteP (Var j) (Var j')}
                       \<union> quote_all p (Vs - {j})"
        by blast
      finally have quote_all'_eq: 
            "quote_all p' V' = 
              {QuoteP (Var sn) (Var sn'), QuoteP (Var sm) (Var sm'), QuoteP (Var j) (Var j')}
              \<union> quote_all p (Vs - {j})" .
      have pjV: "p \<bullet> j \<notin> Vs" 
        by (metis j perm_exits_Vs) 
      hence jpV: "atom j \<sharp> p \<bullet> Vs" 
        by (simp add: fresh_permute_left pinv fresh_finite_set_at_base)
      show "quote_all p (Vs-{j}) \<turnstile> All k (OrdP (Var k) IMP (All2 l (Var k) (?scheme(k::= Var l)) IMP ?scheme))"
        apply (rule All_I Imp_I)+
        using atoms atoms' j jpV pjV
        apply (auto simp: fresh_at_base fresh_finite_set_at_base j' elim!: fresh_quote_all_mem)
        apply (rule cut_same [where A = "QuoteP (Var j) (Var j')"])
        apply (blast intro: QuoteP_I)
        apply (rule cut_same)
        apply (rule cut1 [OF SeqQuoteP_lemma [of m "Var j" "Var j'" "Var s" "Var k" n sm sm' sn sn']], simp_all, blast)        
        apply (rule Imp_I Disj_EH Conj_EH)+
        \<comment> \<open>case 1, Var j EQ Zero\<close>
        apply (simp add: vquot_fm_def)
        apply (rule thin1)
        apply (rule Var_Eq_subst_Iff [THEN Iff_MP_same], simp)
        apply (simp add: substj)
        apply (rule Q_All2_Zero [THEN thin])
        using assms
        apply (simp add: quote_all_def, blast)
        \<comment> \<open>case 2, @{term "Var j EQ Eats (Var sm) (Var sn)"}\<close>
        apply (rule Imp_I Conj_EH Ex_EH)+
        using atoms  apply (auto elim!: fresh_quote_all_mem)
        apply (rule cut_same [where A = "QuoteP (Var sm) (Var sm')"])
        apply (blast intro: QuoteP_I)
        apply (rule cut_same [where A = "QuoteP (Var sn) (Var sn')"])
        apply (blast intro: QuoteP_I)
        \<comment> \<open>Eats case. IH for sm\<close>
        apply (rule All2_E [where x="Var m", THEN rotate12], simp_all, blast)
        apply (rule All_E [where x="Var sm"], simp)
        apply (rule All_E [where x="Var sm'"], simp)
        apply (rule Imp_E, blast)
        \<comment> \<open>Setting up the subgoal\<close>
        apply (rule cut_same [where A = "PfP (ssubst \<lfloor>All2 i (Eats (Var sm) (Var sn)) \<alpha>\<rfloor>V' V' F')"])
         defer 1
         apply (rule rotate6)
         apply (simp add: vquot_fm_def)
         apply (rule Var_Eq_subst_Iff [THEN Iff_MP_same], force simp add: substj ss_noprimes j')
        apply (rule cut_same [where A = "All2 i (Eats (Var sm) (Var sn)) \<alpha>"])
         apply (rule All2_cong [OF Hyp Iff_refl, THEN Iff_MP_same], blast)
          apply (force elim!: fresh_quote_all_mem 
                       simp add: fresh_at_base fresh_finite_set_at_base, blast)
        apply (rule All2_Eats_E, simp)
        apply (rule MP_same [THEN MP_same])
        apply (rule Q_All2_Eats [THEN thin])
        apply (force simp add: quote_all'_eq)
        \<comment> \<open>Proving @{term "PfP (ssubst \<lfloor>All2 i (Var sm) \<alpha>\<rfloor>V' V' F')"}\<close>
        apply (force intro!: Imp_E [THEN rotate3] simp add: vquot_fm_def substj j' ss_noprimes)
        \<comment> \<open>Proving @{term "PfP (ssubst \<lfloor>\<alpha>(i::=Var sn)\<rfloor>V' V' F')"}\<close>
        apply (rule MP_same [OF subst_i_star [THEN thin]])
        apply (force simp add: quote_all'_eq, blast)
        done
    qed
  hence p1: "insert (OrdP (Var k)) (quote_all p (Vs-{j}))
             \<turnstile> (All j' (SeqQuoteP (Var j) (Var j') (Var s) (Var k) IMP
                All2 i (Var j) \<alpha> IMP PfP (ssubst \<lfloor>All2 i (Var j) \<alpha>\<rfloor>Vs Vs F))) (j::=Var j)"
    by (metis All_D)
  have "insert (OrdP (Var k)) (quote_all p (Vs-{j}))
        \<turnstile> (SeqQuoteP (Var j) (Var j') (Var s) (Var k) IMP
            All2 i (Var j) \<alpha> IMP PfP (ssubst \<lfloor>All2 i (Var j) \<alpha>\<rfloor>Vs Vs F)) (j'::=Var j')"
    apply (rule All_D)
    using p1 atoms by simp
  thus ?thesis
    using atoms 
    by simp (metis SeqQuoteP_imp_OrdP Imp_cut anti_deduction)
qed

lemma (in quote_perm) quote_all_Mem_imp_All2:
  assumes IH: "insert (QuoteP (Var i) (Var i')) (quote_all p Vs) 
               \<turnstile> \<alpha> IMP PfP (ssubst \<lfloor>\<alpha>\<rfloor>(insert i Vs) (insert i Vs) Fi)"
      and "supp (All2 i (Var j) \<alpha>) \<subseteq> atom ` Vs" 
      and j: "atom j \<sharp> (i,\<alpha>)" and i: "atom i \<sharp> p" and i': "atom i' \<sharp> (i,p,\<alpha>)" 
      and pi: "pi = (atom i \<rightleftharpoons> atom i') + p" 
      and Fi: "Fi = make_F (insert i Vs) pi"
  shows "insert (All2 i (Var j) \<alpha>) (quote_all p Vs) \<turnstile> PfP (ssubst \<lfloor>All2 i (Var j) \<alpha>\<rfloor>Vs Vs F)"
proof -
  have sp: "supp \<alpha> - {atom i} \<subseteq> atom ` Vs" and jV: "j \<in> Vs"
    using assms
    by (auto simp: fresh_def supp_Pair)
  obtain s::name and k::name
    where atoms: "atom s \<sharp> (k,i,j,p\<bullet>j,\<alpha>,p)" "atom k \<sharp> (i,j,p\<bullet>j,\<alpha>,p)" 
    by (metis obtain_fresh)
  hence ii: "atom i \<sharp> (j, p \<bullet> j, s, k, p)" using i j
    by (simp add: fresh_Pair) (metis fresh_at_base(2) fresh_perm fresh_permute_left pinv)
  have jj: "atom j \<sharp> (p \<bullet> j, s, k, \<alpha>)" using atoms j
    by (auto simp: fresh_Pair) (metis atom_fresh_perm jV)
  have pj: "atom (p \<bullet> j) \<sharp> (s, k, \<alpha>)" using atoms ii sp jV
    by (simp add: fresh_Pair) (auto simp: fresh_def perm_exits_Vs dest!: subsetD)
  show ?thesis
    apply (rule cut_same [where A = "QuoteP (Var j) (Var (p \<bullet> j))"])
    apply (force intro: jV Hyp simp add: quote_all_def)
    using atoms 
    apply (auto simp: QuoteP.simps [of s _ _ k] elim!: fresh_quote_all_mem)
    apply (rule MP_same)
    apply (rule SeqQuoteP_Mem_imp_All2 [OF IH sp jV refl pi Fi ii i' jj pj, THEN thin])
    apply (auto simp: fresh_at_base_permI quote_all_def intro!: fresh_ssubst')
    done
qed


section \<open>The Derivability Condition, Theorem 9.1\<close>

lemma SpecI: "H \<turnstile> A IMP Ex i A"
  by (metis Imp_I Assume Ex_I subst_fm_id)

lemma star:
  fixes p :: perm and F :: "name \<Rightarrow> tm"
  assumes C: "ss_fm \<alpha>" 
      and p: "atom ` (p \<bullet> V) \<sharp>* V" "-p = p"
      and V: "finite V" "supp \<alpha> \<subseteq> atom ` V"
      and F: "F = make_F V p"
    shows "insert \<alpha> (quote_all p V) \<turnstile> PfP (ssubst \<lfloor>\<alpha>\<rfloor>V V F)"
using C V p F
proof (nominal_induct avoiding: p arbitrary: V F rule: ss_fm.strong_induct)
    case (MemI i j) show ?case
    proof (cases "i=j")
      case True thus ?thesis
        by auto
    next
      case False
      hence ij: "atom i \<sharp> j" "{i, j} \<subseteq> V" using MemI
        by auto  
      interpret qp: quote_perm p V F
        by unfold_locales (auto simp: image_iff F make_F_def p MemI)
      have "insert (Var i IN Var j) (quote_all p V) \<turnstile> PfP (Q_Mem (Var (p \<bullet> i)) (Var (p \<bullet> j)))"
        apply (rule QuoteP_Mem_imp_QMem [of i j, THEN cut3]) 
        using ij  apply (auto simp: quote_all_def qp.atom_fresh_perm intro: Hyp)
        apply (metis atom_eqvt fresh_Pair fresh_at_base(2) fresh_permute_iff qp.atom_fresh_perm)
        done
      thus ?thesis
        apply (simp add: vquot_fm_def) 
        using MemI  apply (auto simp: make_F_def)
        done
    qed
  next
    case (DisjI A B) 
      interpret qp: quote_perm p V F
        by unfold_locales (auto simp: image_iff DisjI)
    show ?case 
      apply auto
      apply (rule_tac [2] qp.quote_all_Disj_I2_PfP_ssubst)
      apply (rule qp.quote_all_Disj_I1_PfP_ssubst)
      using DisjI by auto
  next
    case (ConjI A B) 
      interpret qp: quote_perm p V F
        by unfold_locales (auto simp: image_iff ConjI)
    show ?case 
      apply (rule qp.quote_all_Conj_I_PfP_ssubst)
      using ConjI  by (auto intro: thin1 thin2)
  next
    case (ExI A i)
    interpret qp: quote_perm p V F 
      by unfold_locales (auto simp: image_iff ExI)
    obtain i'::name where i': "atom i' \<sharp> (i,p,A)"
      by (metis obtain_fresh)
    define p' where "p' = (atom i \<rightleftharpoons> atom i') + p" 
    define F' where "F' = make_F (insert i V) p'"
    have p'_apply [simp]: "!!v. p' \<bullet> v = (if v=i then i' else if v=i' then i else p \<bullet> v)"
      using  \<open>atom i \<sharp> p\<close>  i'
      by (auto simp: p'_def fresh_Pair fresh_at_base_permI) 
         (metis atom_eq_iff fresh_at_base_permI permute_eq_iff swap_at_base_simps(3)) 
    have p'V: "p' \<bullet> V = p \<bullet> V"
      by (metis i' p'_def permute_plus fresh_Pair qp.fresh_pVs swap_fresh_fresh \<open>atom i \<sharp> p\<close>)
    have i: "i \<notin> V" "i \<notin> p \<bullet> V"  "atom i \<sharp> V" "atom i \<sharp> p \<bullet> V"  "atom i \<sharp> p' \<bullet> V" using ExI
      by (auto simp: p'V fresh_finite_set_at_base notin_V)
    interpret qp': quote_perm p' "insert i V" F' 
      by (auto simp: qp.qp_insert i' p'_def F'_def  \<open>atom i \<sharp> p\<close>)
    { fix W t assume W: "W \<subseteq> V" "i\<notin>W" "i'\<notin>W"
      hence "finite W" by (metis \<open>finite V\<close> infinite_super)
      hence "ssubst t W F' = ssubst t W F" using W
        by induct (auto simp: qp.ssubst_insert_if qp'.ssubst_insert_if qp.F_unfold qp'.F_unfold)
    }
    hence ss_simp: "ssubst \<lfloor>Ex i A\<rfloor>(insert i V) (insert i V) F' = ssubst \<lfloor>Ex i A\<rfloor>V V F" using i
      by (metis equalityE insertCI p'_apply qp'.perm_exits_Vs qp'.ssubst_vquot_Ex qp.Vs) 
    have qa_p': "quote_all p' V = quote_all p V" using i i' ExI.hyps(1) 
      by (auto simp: p'_def quote_all_perm_eq)
    have ss: "(quote_all p' (insert i V))
              \<turnstile> PfP (ssubst \<lfloor>A\<rfloor>(insert i V) (insert i V) F') IMP 
                PfP (ssubst \<lfloor>Ex i A\<rfloor>(insert i V) (insert i V) F')" 
      apply (rule qp'.quote_all_MonPon_PfP_ssubst [OF SpecI])
      using ExI  apply auto
      done
    hence "insert A (quote_all p' (insert i V)) 
           \<turnstile> PfP (ssubst \<lfloor>Ex i A\<rfloor>(insert i V) (insert i V) F')"
      apply (rule MP_thin)
      apply (rule ExI(3) [of "insert i V" p' F'])
      apply (metis \<open>finite V\<close> finite_insert)
      using \<open>supp (Ex i A) \<subseteq> _\<close> qp'.p qp'.pinv i'
      apply (auto simp: F'_def fresh_finite_insert)
      done
    hence "insert (QuoteP (Var i) (Var i')) (insert A (quote_all p V)) 
           \<turnstile> PfP (ssubst \<lfloor>Ex i A\<rfloor>V V F)"
      by (auto simp: insert_commute ss_simp qa_p')
    hence Exi': "insert (Ex i' (QuoteP (Var i) (Var i'))) (insert A (quote_all p V)) 
                 \<turnstile> PfP (ssubst \<lfloor>Ex i A\<rfloor>V V F)"
      by (auto intro!: qp.fresh_ssubst_fm) (auto simp: ExI i' fresh_quote_all_mem)
    have "insert A (quote_all p V) \<turnstile> PfP (ssubst \<lfloor>Ex i A\<rfloor>V V F)" 
      using i'  by (auto intro: cut0 [OF exists_QuoteP Exi']) 
    thus "insert (Ex i A) (quote_all p V) \<turnstile> PfP (ssubst \<lfloor>Ex i A\<rfloor>V V F)"
      apply (rule Ex_E, simp)
      apply (rule qp.fresh_ssubst_fm)  using i ExI
      apply (auto simp: fresh_quote_all_mem)
      done
   next
    case (All2I A j i p V F)
    interpret qp: quote_perm p V F 
      by unfold_locales (auto simp: image_iff All2I)
    obtain i'::name where i': "atom i' \<sharp> (i,p,A)"
      by (metis obtain_fresh)
    define p' where "p' = (atom i \<rightleftharpoons> atom i') + p" 
    define F' where "F' = make_F (insert i V) p'"
    interpret qp': quote_perm p' "insert i V" F' 
      using \<open>atom i \<sharp> p\<close> i'
      by (auto simp: qp.qp_insert p'_def F'_def)
    have p'_apply [simp]: "p' \<bullet> i = i'"
      using \<open>atom i \<sharp> p\<close> by (auto simp: p'_def fresh_at_base_permI)
    have qa_p': "quote_all p' V = quote_all p V" using i' All2I
      by (auto simp: p'_def quote_all_perm_eq)
    have "insert A (quote_all p' (insert i V)) 
          \<turnstile> PfP (ssubst \<lfloor>A\<rfloor>(insert i V) (insert i V) F')"
      apply (rule All2I.hyps)
      using \<open>supp (All2 i _ A) \<subseteq> _\<close>   qp'.p qp'.pinv
      apply (auto simp: F'_def fresh_finite_insert)
      done
    hence "insert (QuoteP (Var i) (Var i')) (quote_all p V) 
           \<turnstile> A IMP PfP (ssubst \<lfloor>A\<rfloor>(insert i V) (insert i V) (make_F (insert i V) p'))"
      by (auto simp: insert_commute qa_p' F'_def)
    thus "insert (All2 i (Var j) A) (quote_all p V) \<turnstile> PfP (ssubst \<lfloor>All2 i (Var j) A\<rfloor>V V F)" 
      using All2I i' qp.quote_all_Mem_imp_All2 by (simp add: p'_def)
qed

theorem Provability: 
  assumes "Sigma_fm \<alpha>" "ground_fm \<alpha>" 
    shows "{\<alpha>} \<turnstile> PfP \<lceil>\<alpha>\<rceil>"
proof -
  obtain \<beta> where \<beta>: "ss_fm \<beta>" "ground_fm \<beta>" "{} \<turnstile> \<alpha> IFF \<beta>" using assms
    by (auto simp: Sigma_fm_def ground_fm_aux_def)
  hence "{\<beta>} \<turnstile> PfP \<lceil>\<beta>\<rceil>" using star [of \<beta> 0 "{}"]
    by (auto simp: ground_fm_aux_def fresh_star_def)
  then have "{\<alpha>} \<turnstile> PfP \<lceil>\<beta>\<rceil>" using \<beta>
    by (metis Iff_MP_left')
  moreover have "{} \<turnstile> PfP \<lceil>\<beta> IMP \<alpha>\<rceil>" using \<beta>
    by (metis Conj_E2 Iff_def proved_imp_proved_PfP)
  ultimately show ?thesis
    by (metis PfP_implies_ModPon_PfP_quot thin0)
qed

end

