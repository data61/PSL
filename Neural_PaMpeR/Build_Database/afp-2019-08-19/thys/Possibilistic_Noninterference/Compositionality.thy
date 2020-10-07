section \<open>Compasitionality of the during-execution security notions\<close> 

theory Compositionality imports During_Execution begin


(*******************************************)
context PL_Indis 
begin 

(* The end-product compositionality results are listed as theorems 
(as opposed to lemmas). *)

subsection \<open>Discreetness versus language constructs:\<close>

theorem discr_Atm[simp]:
"discr (Atm atm) = presAtm atm"  
proof-    
  {fix c
   have 
   "(\<exists> atm. c = Atm atm \<and> presAtm atm) 
    \<Longrightarrow> discr c"
   apply(erule discr_coind) 
   apply (metis Atm_transC_invert)
   by (metis PL.Atm_transT_invert presAtm_def)
  }
  moreover have "discr (Atm atm) \<Longrightarrow> presAtm atm"
    by (metis Atm presAtm_def discr_transT)
  ultimately show ?thesis by blast
qed

theorem discr_If[simp]:
assumes "discr c1" and "discr c2"
shows "discr (If tst c1 c2)"
proof-    
  {fix c
   have 
   "(\<exists> tst c1 c2. c = If tst c1 c2 \<and> discr c1 \<and> discr c2) \<Longrightarrow> discr c"
   apply(erule discr_coind) 
   apply (metis PL.If_transC_invert indis_refl)
   by (metis If_transT_invert)
  }
  thus ?thesis using assms by blast
qed

theorem discr_Seq[simp]:
assumes *: "discr c1" and **: "discr c2"
shows "discr (c1 ;; c2)"
proof-
  {fix c
   have 
   "(\<exists> c1 c2. c = c1 ;; c2 \<and> discr c1 \<and> discr c2) 
    \<Longrightarrow> discr c"
   apply(erule discr_coind) 
   proof(tactic\<open>clarify_all_tac @{context}\<close>)
     fix c s c' s' c1 c2
     assume c1: "discr c1" and c2: "discr c2" 
     assume "(c1 ;; c2, s) \<rightarrow>c (c', s')"
     thus "s \<approx> s' \<and> ((\<exists>c1 c2. c' = c1 ;; c2 \<and> discr c1 \<and> discr c2) \<or> discr c')"
     apply - apply(erule Seq_transC_invert)
     apply (metis c1 c2 discr_transC discr_transC_indis)
     by (metis c1 c2 discr.cases)
   qed (insert Seq_transT_invert, blast)
  }
  thus ?thesis using assms by blast
qed

theorem discr_While[simp]:
assumes "discr c"
shows "discr (While tst c)"
proof-
  {fix c
   have 
   "(\<exists> tst d. c = While tst d \<and> discr d) \<or> 
    (\<exists> tst d1 d. c = d1 ;; (While tst d) \<and> discr d1 \<and> discr d)
    \<Longrightarrow> discr c"
   apply(erule discr_coind)
   apply(tactic \<open>mauto_no_simp_tac @{context}\<close>)
   apply (metis While_transC_invert indis_refl)
   apply (metis Seq_transC_invert discr.cases)
   apply (metis While_transC_invert)
   apply (metis Seq_transC_invert discr.cases)
   apply (metis PL.While_transT_invert indis_refl)
   by (metis Seq_transT_invert)
  }
  thus ?thesis using assms by blast
qed

theorem discr_Par[simp]:
assumes *: "discr c1" and **: "discr c2"
shows "discr (Par c1 c2)"
proof-
  {fix c
   have 
   "(\<exists> c1 c2. c = Par c1 c2 \<and> discr c1 \<and> discr c2) 
    \<Longrightarrow> discr c"
   apply(erule discr_coind) 
   proof(tactic\<open>clarify_all_tac @{context}\<close>)
     fix c s c' s' c1 c2
     assume c1: "discr c1" and c2: "discr c2" 
     assume "(Par c1 c2, s) \<rightarrow>c (c', s')"
     thus "s \<approx> s' \<and> ((\<exists>c1 c2. c' = Par c1 c2 \<and> discr c1 \<and> discr c2) \<or> discr c')"
     apply - apply(erule Par_transC_invert)
     by(metis c1 c2 discr.cases)+
   qed
  }
  thus ?thesis using assms by blast
qed


subsection \<open>Discreetness versus language constructs:\<close>

theorem discr0_Atm[simp]:
"discr0 (Atm atm) = presAtm atm"  
proof-    
  {fix c
   have 
   "(\<exists> atm. c = Atm atm \<and> presAtm atm) 
    \<Longrightarrow> discr0 c"
   apply(erule discr0_coind) 
   apply (metis Atm_transC_invert)
   by (metis discr_Atm discr_transT)
  }
  moreover have "discr0 (Atm atm) \<Longrightarrow> presAtm atm"
  by (metis Atm discr0_MtransT presAtm_def mustT_Atm transT_MtransT)
  ultimately show ?thesis by blast
qed

theorem discr0_If[simp]:
assumes "discr0 c1" and "discr0 c2"
shows "discr0 (If tst c1 c2)"
proof-    
  {fix c
   have 
   "(\<exists> tst c1 c2. c = If tst c1 c2 \<and> discr0 c1 \<and> discr0 c2) \<Longrightarrow> discr0 c"
   apply(erule discr0_coind) 
   apply (metis If_transC_invert indis_refl)
   by (metis If_transT_invert)
  }
  thus ?thesis using assms by blast
qed

theorem discr0_Seq[simp]:
assumes *: "discr0 c1" and **: "discr0 c2"
shows "discr0 (c1 ;; c2)"
proof-
  {fix c
   have 
   "(\<exists> c1 c2. c = c1 ;; c2 \<and> discr0 c1 \<and> discr0 c2) 
    \<Longrightarrow> discr0 c"
   apply(erule discr0_coind) 
   proof(tactic\<open>clarify_all_tac @{context}\<close>)
     fix c s c' s' c1 c2
     assume mt: "mustT (c1 ;; c2) s" 
     and c1: "discr0 c1" and c2: "discr0 c2" 
     assume "(c1 ;; c2, s) \<rightarrow>c (c', s')"
     thus "s \<approx> s' \<and> ((\<exists>c1 c2. c' = c1 ;; c2 \<and> discr0 c1 \<and> discr0 c2) \<or> discr0 c')"
     apply - apply(erule Seq_transC_invert)
     apply (metis mustT_Seq_L c1 c2 discr0_MtransC discr0_MtransC_indis mt 
                  transC_MtransC)
     by (metis c1 c2 discr0_transT mt mustT_Seq_L)
   qed (insert Seq_transT_invert, blast)
  }
  thus ?thesis using assms by blast
qed

theorem discr0_While[simp]:
assumes "discr0 c"
shows "discr0 (While tst c)"
proof-
  {fix c
   have 
   "(\<exists> tst d. c = While tst d \<and> discr0 d) \<or> 
    (\<exists> tst d1 d. c = d1 ;; (While tst d) \<and> discr0 d1 \<and> discr0 d)
    \<Longrightarrow> discr0 c"
   proof (induct rule: discr0_coind)
     case (Term c s s')
     thus "s \<approx> s'" 
     apply (elim exE disjE conjE)
     apply (metis While_transT_invert indis_refl)
     by (metis Seq_transT_invert)
   next
     case (Cont c s c' s')
     thus ?case
     apply(intro conjI)
     apply (elim exE disjE conjE)
     apply (metis While_transC_invert indis_refl)
     apply (metis Seq_transC_invert discr0_MtransC_indis discr0_transT 
                  mustT_Seq_L transC_MtransC)
     (*  *)
     apply (elim exE disjE conjE)
     apply (metis While_transC_invert)
     by (metis Cont(3) Seq_transC_invert discr0_transC mustT_Seq_L)
   qed   
  }
  thus ?thesis using assms by blast
qed

theorem discr0_Par[simp]:
assumes *: "discr0 c1" and **: "discr0 c2"
shows "discr0 (Par c1 c2)"
proof-
  {fix c
   have 
   "(\<exists> c1 c2. c = Par c1 c2 \<and> discr0 c1 \<and> discr0 c2) 
    \<Longrightarrow> discr0 c"
   apply(induct rule: discr0_coind) 
   proof(tactic\<open>clarify_all_tac @{context}\<close>)
     fix c s c' s' c1 c2
     assume mt: "mustT (Par c1 c2) s" and c1: "discr0 c1" and c2: "discr0 c2" 
     assume "(Par c1 c2, s) \<rightarrow>c (c', s')"
     thus "s \<approx> s' \<and> ((\<exists>c1 c2. c' = Par c1 c2 \<and> discr0 c1 \<and> discr0 c2) \<or> discr0 c')"
     apply(elim Par_transC_invert)
     apply (metis c1 c2 discr0.simps mt mustT_Par_L)
     apply (metis c1 c2 discr0_transT mt mustT_Par_L)
     apply (metis c1 c2 discr0.simps indis_sym mt mustT_Par_R)
     by (metis PL.mustT_Par_R c1 c2 discr0_transT mt)
   qed
  }
  thus ?thesis using assms by blast
qed


subsection \<open>Self-Isomorphism versus language constructs:\<close>

theorem siso_Atm[simp]:
"siso (Atm atm) = compatAtm atm"  
proof-    
  {fix c
   have 
   "(\<exists> atm. c = Atm atm \<and> compatAtm atm) 
    \<Longrightarrow> siso c"
   apply(erule siso_coind) 
   apply (metis Atm_transC_invert)
   apply (metis PL.Atm_transC_invert)
   by (metis Atm_transT_invert PL.Atm compatAtm_def)
  }
  moreover have "siso (Atm atm) \<Longrightarrow> compatAtm atm" unfolding compatAtm_def
  by (metis Atm Atm_transT_invert siso_transT)
  ultimately show ?thesis by blast
qed 

theorem siso_If[simp]:
assumes  "compatTst tst" and "siso c1" and "siso c2"
shows "siso (If tst c1 c2)"
proof-    
  {fix c
   have 
   "(\<exists> tst c1 c2. c = If tst c1 c2 \<and> compatTst tst \<and> siso c1 \<and> siso c2) \<Longrightarrow> siso c"
   apply(erule siso_coind) 
   apply (metis PL.If_transC_invert indis_refl)
   apply (metis IfTrue PL.IfFalse PL.If_transC_invert compatTst_def)
   by (metis If_transT_invert)
  }
  thus ?thesis using assms by blast
qed

theorem siso_Seq[simp]:
assumes *: "siso c1" and **: "siso c2"
shows "siso (c1 ;; c2)"
proof-
  {fix c
   have 
   "(\<exists> c1 c2. c = c1 ;; c2 \<and> siso c1 \<and> siso c2) 
    \<Longrightarrow> siso c"
   apply(erule siso_coind) 
   proof(tactic\<open>clarify_all_tac @{context}\<close>)
     fix c s t c' s' c1 c2
     assume "s \<approx> t" and "(c1 ;; c2, s) \<rightarrow>c (c', s')" and "siso c1" and "siso c2"
     thus "\<exists>t'. s' \<approx> t' \<and> (c1 ;; c2, t) \<rightarrow>c (c', t')"
     apply - apply(erule Seq_transC_invert)
     apply (metis SeqC siso_transC_indis)
     by (metis PL.SeqT siso_transT)
   qed (insert Seq_transT_invert siso_transC, blast+)
  }
  thus ?thesis using assms by blast
qed

theorem siso_While[simp]:
assumes "compatTst tst" and "siso c"
shows "siso (While tst c)"
proof-
  {fix c
   have 
   "(\<exists> tst d. compatTst tst \<and> c = While tst d \<and> siso d) \<or> 
    (\<exists> tst d1 d. compatTst tst \<and> c = d1 ;; (While tst d) \<and> siso d1 \<and> siso d)
    \<Longrightarrow> siso c"
   apply(erule siso_coind)
   apply auto
   apply (metis PL.Seq_transC_invert siso_transC)
   apply (metis WhileTrue While_transC_invert compatTst_def)
   apply (metis PL.SeqC siso_transC_indis)
   apply (metis PL.SeqT siso_transT)
   by (metis WhileFalse compatTst_def) 
  }
  thus ?thesis using assms by blast
qed

theorem siso_Par[simp]:
assumes *: "siso c1" and **: "siso c2"
shows "siso (Par c1 c2)"
proof-
  {fix c
   have 
   "(\<exists> c1 c2. c = Par c1 c2 \<and> siso c1 \<and> siso c2) 
    \<Longrightarrow> siso c"
   apply(erule siso_coind)
   proof(tactic\<open>clarify_all_tac @{context}\<close>)
     fix c s t c' s' c1 c2
     assume "s \<approx> t" and "(Par c1 c2, s) \<rightarrow>c (c', s')" and c1: "siso c1" and c2: "siso c2"
     thus "\<exists>t'. s' \<approx> t' \<and> (Par c1 c2, t) \<rightarrow>c (c', t')"
     apply - apply(erule Par_transC_invert)
     by(metis ParCL ParTL ParCR ParTR c1 c2 siso_transT siso_transC_indis)+   
   qed (insert Par_transC_invert siso_transC Par_transT_invert, blast+)
  }
  thus ?thesis using assms by blast
qed


subsection \<open>Self-Isomorphism versus language constructs:\<close>

theorem siso0_Atm[simp]:
"siso0 (Atm atm) = compatAtm atm"  
proof-    
  {fix c
   have 
   "(\<exists> atm. c = Atm atm \<and> compatAtm atm) 
    \<Longrightarrow> siso0 c"
   apply(erule siso0_coind) 
   apply (metis Atm_transC_invert)
   apply (metis PL.Atm_transC_invert)
   by (metis Atm_transT_invert PL.Atm compatAtm_def)
  }
  moreover have "siso0 (Atm atm) \<Longrightarrow> compatAtm atm" unfolding compatAtm_def
  by (metis Atm Atm_transT_invert siso0_transT mustT_Atm)
  ultimately show ?thesis by blast
qed 

theorem siso0_If[simp]:
assumes  "compatTst tst" and "siso0 c1" and "siso0 c2"
shows "siso0 (If tst c1 c2)"
proof-    
  {fix c
   have 
   "(\<exists> tst c1 c2. c = If tst c1 c2 \<and> compatTst tst \<and> siso0 c1 \<and> siso0 c2) \<Longrightarrow> siso0 c"
   apply(erule siso0_coind) 
   apply (metis PL.If_transC_invert indis_refl)
   apply (metis IfTrue PL.IfFalse PL.If_transC_invert compatTst_def)
   by (metis If_transT_invert)
  }
  thus ?thesis using assms by blast
qed

theorem siso0_Seq[simp]:
assumes *: "siso0 c1" and **: "siso0 c2"
shows "siso0 (c1 ;; c2)"
proof-
  {fix c
   have 
   "(\<exists> c1 c2. c = c1 ;; c2 \<and> siso0 c1 \<and> siso0 c2) 
    \<Longrightarrow> siso0 c"
   proof (induct rule: siso0_coind)
     case (Indef c s c' s')
     thus ?case
     by (metis Seq_transC_invert mustT_Seq_L siso0_transC) 
   next
     case (Cont c s t c' s')
     then obtain c1 c2
     where c: "c = c1 ;; c2" and mt: "mustT (c1 ;; c2) s" "mustT (c1 ;; c2) t" 
     and st: "s \<approx> t" and siso1: "siso0 c1" and siso2: "siso0 c2" by auto
     hence mt1: "mustT c1 s" "mustT c1 t"
     by (metis mustT_Seq_L)+
     have "(c1 ;; c2, s) \<rightarrow>c (c', s')" using c Cont by auto
     thus ?case
     proof (elim Seq_transC_invert)
       fix c1' assume c1: "(c1, s) \<rightarrow>c (c1', s')" and c': "c' = c1' ;; c2"
       obtain t' where "(c1, t) \<rightarrow>c (c1', t')" and "s' \<approx> t'"
       using siso1 c1 st mt1 by (metis siso0_transC_indis) 
       thus ?thesis by (metis SeqC c c') 
     next
       assume "(c1, s) \<rightarrow>t s'" and "c' = c2"
       thus ?thesis by (metis c SeqT mt1 siso0_transT siso1 st)
     qed
   qed auto
  }
  thus ?thesis using assms by blast
qed

theorem siso0_While[simp]:
assumes "compatTst tst" and "siso0 c"
shows "siso0 (While tst c)"
proof-
  {fix c
   have 
   "(\<exists> tst d. compatTst tst \<and> c = While tst d \<and> siso0 d) \<or> 
    (\<exists> tst d1 d. compatTst tst \<and> c = d1 ;; (While tst d) \<and> siso0 d1 \<and> siso0 d)
    \<Longrightarrow> siso0 c"
   apply(erule siso0_coind)
   apply auto
   apply (metis mustT_Seq_L siso0_transC)
   apply (metis WhileTrue While_transC_invert compatTst_def)
   apply (metis SeqC mustT_Seq_L siso0_transC_indis)
   apply (metis SeqT mustT_Seq_L siso0_transT)
   by (metis WhileFalse compatTst_def)
  }
  thus ?thesis using assms by blast
qed

theorem siso0_Par[simp]:
assumes *: "siso0 c1" and **: "siso0 c2"
shows "siso0 (Par c1 c2)"
proof-
  {fix c
   have 
   "(\<exists> c1 c2. c = Par c1 c2 \<and> siso0 c1 \<and> siso0 c2) 
    \<Longrightarrow> siso0 c"
   proof (induct rule: siso0_coind)
     case (Indef c s c' s')
     then obtain c1 c2 where c: "c = Par c1 c2" 
     and c1: "siso0 c1" and c2: "siso0 c2" by auto
     hence "(Par c1 c2, s) \<rightarrow>c (c', s')" using c Indef by auto
     thus ?case
     apply(elim Par_transC_invert)
     by (metis Indef c c1 c2 mustT_Par_L mustT_Par_R siso0_transC)+ 
   next
     case (Cont c s t c' s')
     then obtain c1 c2 where c: "c = Par c1 c2" 
     and c1: "siso0 c1" and c2: "siso0 c2" by auto
     hence mt: "mustT c1 s" "mustT c1 t" "mustT c2 s" "mustT c2 t"
     by (metis Cont mustT_Par_L mustT_Par_R)+
     have "(Par c1 c2, s) \<rightarrow>c (c', s')" using c Cont by auto
     thus ?case
     apply(elim Par_transC_invert)
     apply (metis Cont ParCL c c1 mt siso0_transC_indis)
     apply (metis Cont ParTL c c1 mt siso0_transT)
     apply (metis Cont ParCR c c2 mt siso0_transC_indis)
     by (metis Cont ParTR c c2 mt siso0_transT)
   qed auto 
  }
  thus ?thesis using assms by blast
qed


subsection\<open>Strong bisimilarity versus language constructs\<close>

text \<open>Atomic commands:\<close>

definition thetaAtm where 
"thetaAtm atm \<equiv> {(Atm atm, Atm atm)}"

lemma thetaAtm_sym:
"sym (thetaAtm atm)"
unfolding thetaAtm_def sym_def by blast

lemma thetaAtm_Sretr:
assumes "compatAtm atm"
shows "thetaAtm atm \<subseteq> Sretr (thetaAtm atm)"
using assms 
unfolding compatAtm_def Sretr_def matchC_C_def matchT_T_def thetaAtm_def
apply simp by (metis Atm_transT_invert Atm) 

lemma thetaAtm_Sbis:
assumes "compatAtm atm"
shows "thetaAtm atm \<subseteq> Sbis"
apply(rule Sbis_raw_coind)
using assms thetaAtm_sym thetaAtm_Sretr by auto

theorem Atm_Sbis[simp]:
assumes "compatAtm atm" 
shows "Atm atm \<approx>s Atm atm"
using assms thetaAtm_Sbis unfolding thetaAtm_def by auto

text\<open>Sequential composition:\<close> 

definition thetaSeq where 
"thetaSeq \<equiv> 
 {(c1 ;; c2, d1 ;; d2) | c1 c2 d1 d2. c1 \<approx>s d1 \<and> c2 \<approx>s d2}"

lemma thetaSeq_sym:
"sym thetaSeq"
unfolding thetaSeq_def sym_def using Sbis_Sym by blast

lemma thetaSeq_Sretr:
"thetaSeq \<subseteq> Sretr (thetaSeq Un Sbis)"
proof-
  {fix c1 c2 d1 d2
   assume c1d1: "c1 \<approx>s d1" and c2d2: "c2 \<approx>s d2"
   hence matchC_C1: "matchC_C Sbis c1 d1" and matchC_C2: "matchC_C Sbis c2 d2"
     and matchT_T1: "matchT_T c1 d1" and matchT_T2: "matchT_T c2 d2"
   using Sbis_matchC_C Sbis_matchT_T by auto
   have "(c1 ;; c2, d1 ;; d2) \<in> Sretr (thetaSeq Un Sbis)"
   unfolding Sretr_def proof (clarify, intro conjI)
     show "matchC_C (thetaSeq Un Sbis) (c1 ;; c2) (d1 ;; d2)"
     unfolding matchC_C_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s'
       assume st: "s \<approx> t" assume "(c1 ;; c2, s) \<rightarrow>c (c', s')"
       thus "\<exists>d' t'. (d1 ;; d2, t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> (c', d') \<in> thetaSeq Un Sbis"
       apply - proof(erule Seq_transC_invert) 
         fix c1' assume c1s: "(c1, s) \<rightarrow>c (c1', s')" and c': "c' = c1' ;; c2"
         hence "\<exists>d1' t'. (d1, t) \<rightarrow>c (d1', t') \<and> s' \<approx> t' \<and> c1' \<approx>s d1'"
         using st matchC_C1 unfolding matchC_C_def by blast
         thus ?thesis unfolding c' thetaSeq_def
         apply simp by (metis SeqC c2d2 ) 
       next      
         assume "(c1, s) \<rightarrow>t s'" and c': "c' = c2"
         hence "\<exists>t'. (d1, t) \<rightarrow>t t' \<and> s' \<approx> t'"
         using st matchT_T1 unfolding matchT_T_def by auto
         thus ?thesis 
         unfolding c' thetaSeq_def
         apply simp by (metis PL.SeqT c2d2) 
       qed
     qed 
   qed (unfold matchT_T_def, auto)
  }
  thus ?thesis unfolding thetaSeq_def by auto
qed

lemma thetaSeq_Sbis:
"thetaSeq \<subseteq> Sbis"
apply(rule Sbis_coind)
using thetaSeq_sym thetaSeq_Sretr by auto

theorem Seq_Sbis[simp]:
assumes "c1 \<approx>s d1" and "c2 \<approx>s d2"
shows "c1 ;; c2 \<approx>s d1 ;; d2"
using assms thetaSeq_Sbis unfolding thetaSeq_def by blast 

text\<open>Conditional:\<close>

definition thetaIf where 
"thetaIf \<equiv> 
 {(If tst c1 c2, If tst d1 d2) | tst c1 c2 d1 d2. compatTst tst \<and> c1 \<approx>s d1 \<and> c2 \<approx>s d2}"

lemma thetaIf_sym:
"sym thetaIf"
unfolding thetaIf_def sym_def using Sbis_Sym by blast

lemma thetaIf_Sretr:
"thetaIf \<subseteq> Sretr (thetaIf Un Sbis)"
proof-
  {fix tst c1 c2 d1 d2
   assume tst: "compatTst tst" and c1d1: "c1 \<approx>s d1" and c2d2: "c2 \<approx>s d2"
   hence matchC_C1: "matchC_C Sbis c1 d1" and matchC_C2: "matchC_C Sbis c2 d2"
     and matchT_T1: "matchT_T c1 d1" and matchT_T2: "matchT_T c2 d2"
   using Sbis_matchC_C Sbis_matchT_T by auto
   have "(If tst c1 c2, If tst d1 d2) \<in> Sretr (thetaIf Un Sbis)"
   unfolding Sretr_def proof (clarify, intro conjI)
     show "matchC_C (thetaIf Un Sbis) (If tst c1 c2) (If tst d1 d2)"
     unfolding matchC_C_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s'
       assume st: "s \<approx> t" assume "(If tst c1 c2, s) \<rightarrow>c (c', s')"
       thus "\<exists>d' t'. (If tst d1 d2, t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> (c', d') \<in> thetaIf Un Sbis"
       apply - apply(erule If_transC_invert)
       unfolding thetaIf_def 
       apply simp apply (metis IfTrue c1d1 compatTst_def st tst)
       apply simp by (metis IfFalse c2d2 compatTst_def st tst)
     qed
   qed (unfold matchT_T_def, auto)
  }
  thus ?thesis unfolding thetaIf_def by auto
qed

lemma thetaIf_Sbis:
"thetaIf \<subseteq> Sbis"
apply(rule Sbis_coind)
using thetaIf_sym thetaIf_Sretr by auto

theorem If_Sbis[simp]:
assumes "compatTst tst" and "c1 \<approx>s d1" and "c2 \<approx>s d2"
shows "If tst c1 c2 \<approx>s If tst d1 d2"
using assms thetaIf_Sbis unfolding thetaIf_def by blast

text\<open>While loop:\<close>

definition thetaWhile where 
"thetaWhile \<equiv> 
 {(While tst c, While tst d) | tst c d. compatTst tst \<and> c \<approx>s d} Un 
 {(c1 ;; (While tst c), d1 ;; (While tst d)) | tst c1 d1 c d. compatTst tst \<and> c1 \<approx>s d1 \<and> c \<approx>s d}"

lemma thetaWhile_sym:
"sym thetaWhile"
unfolding thetaWhile_def sym_def using Sbis_Sym by blast

lemma thetaWhile_Sretr:
"thetaWhile \<subseteq> Sretr (thetaWhile Un Sbis)"
proof-
  {fix tst c d 
   assume tst: "compatTst tst" and c_d: "c \<approx>s d"
   hence matchC_C: "matchC_C Sbis c d" 
     and matchT_T: "matchT_T c d" 
   using Sbis_matchC_C Sbis_matchT_T by auto
   have "(While tst c, While tst d) \<in> Sretr (thetaWhile Un Sbis)"
   unfolding Sretr_def proof (clarify, intro conjI)
     show "matchC_C (thetaWhile \<union> Sbis) (While tst c) (While tst d)"
     unfolding matchC_C_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s'
       assume st: "s \<approx> t" assume "(While tst c, s) \<rightarrow>c (c', s')"
       thus "\<exists>d' t'. (While tst d, t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> (c', d') \<in> thetaWhile \<union> Sbis"
       apply - apply(erule While_transC_invert)
       unfolding thetaWhile_def apply simp
       by (metis WhileTrue c_d compatTst_def st tst)
     qed
   next
     show "matchT_T (While tst c) (While tst d)"
     unfolding matchT_T_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t s' assume st: "s \<approx> t" assume "(While tst c, s) \<rightarrow>t s'"
       thus "\<exists>t'. (While tst d, t) \<rightarrow>t t' \<and> s' \<approx> t' "
       apply - apply(erule While_transT_invert)
       unfolding thetaWhile_def apply simp
       by (metis PL.WhileFalse compatTst_def st tst)    
     qed
   qed
  }
  moreover 
  {fix tst c1 d1  c d
   assume tst: "compatTst tst" and c1d1: "c1 \<approx>s d1" and c_d: "c \<approx>s d"
   hence matchC_C1: "matchC_C Sbis c1 d1" and matchC_C: "matchC_C Sbis c d" 
     and matchT_T1: "matchT_T c1 d1" and matchT_T: "matchT_T c d"
   using Sbis_matchC_C Sbis_matchT_T by auto
   have "(c1 ;; (While tst c), d1 ;; (While tst d)) \<in> Sretr (thetaWhile Un Sbis)"
   unfolding Sretr_def proof (clarify, intro conjI)
     show "matchC_C (thetaWhile \<union> Sbis) (c1 ;; (While tst c)) (d1 ;; (While tst d))"
     unfolding matchC_C_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s'
       assume st: "s \<approx> t" assume "(c1 ;; (While tst c), s) \<rightarrow>c (c', s')"
       thus "\<exists>d' t'. (d1 ;; (While tst d), t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> (c', d') \<in> thetaWhile \<union> Sbis"
       apply - proof(erule Seq_transC_invert)
         fix c1' assume "(c1, s) \<rightarrow>c (c1', s')" and c': "c' = c1' ;; (While tst c)"
         hence "\<exists>d' t'. (d1, t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> c1' \<approx>s d'" 
         using st matchC_C1 unfolding matchC_C_def by blast
         thus ?thesis
         unfolding c' thetaWhile_def
         apply simp by (metis SeqC c_d tst) 
       next
         assume "(c1, s) \<rightarrow>t s'" and c': "c' = While tst c"
         hence "\<exists>t'. (d1, t) \<rightarrow>t t' \<and> s' \<approx> t'"
         using st matchT_T1 unfolding matchT_T_def by auto
         thus ?thesis
         unfolding c' thetaWhile_def 
         apply simp by (metis PL.SeqT c_d tst) 
       qed
     qed
   qed (unfold matchT_T_def, auto)
  }
  ultimately show ?thesis unfolding thetaWhile_def by auto
qed

lemma thetaWhile_Sbis:
"thetaWhile \<subseteq> Sbis"
apply(rule Sbis_coind)
using thetaWhile_sym thetaWhile_Sretr by auto

theorem While_Sbis[simp]:
assumes "compatTst tst" and "c \<approx>s d"
shows "While tst c \<approx>s While tst d"
using assms thetaWhile_Sbis unfolding thetaWhile_def by auto

text\<open>Parallel composition:\<close>

definition thetaPar where 
"thetaPar \<equiv> 
 {(Par c1 c2, Par d1 d2) | c1 c2 d1 d2. c1 \<approx>s d1 \<and> c2 \<approx>s d2}"

lemma thetaPar_sym:
"sym thetaPar"
unfolding thetaPar_def sym_def using Sbis_Sym by blast

lemma thetaPar_Sretr:
"thetaPar \<subseteq> Sretr (thetaPar Un Sbis)"
proof-
  {fix c1 c2 d1 d2
   assume c1d1: "c1 \<approx>s d1" and c2d2: "c2 \<approx>s d2"
   hence matchC_C1: "matchC_C Sbis c1 d1" and matchC_C2: "matchC_C Sbis c2 d2"
     and matchT_T1: "matchT_T c1 d1" and matchT_T2: "matchT_T c2 d2"
   using Sbis_matchC_C Sbis_matchT_T by auto
   have "(Par c1 c2, Par d1 d2) \<in> Sretr (thetaPar Un Sbis)"
   unfolding Sretr_def proof (clarify, intro conjI)
     show "matchC_C (thetaPar \<union> Sbis) (Par c1 c2) (Par d1 d2)"
     unfolding matchC_C_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s'
       assume st: "s \<approx> t" assume "(Par c1 c2, s) \<rightarrow>c (c', s')"
       thus "\<exists>d' t'. (Par d1 d2, t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> (c', d') \<in> thetaPar \<union> Sbis"
       apply - proof(erule Par_transC_invert)
         fix c1' assume c1s: "(c1, s) \<rightarrow>c (c1', s')" and c': "c' = Par c1' c2"
         hence "\<exists>d' t'. (d1, t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> c1' \<approx>s d'"
         using st matchC_C1 unfolding matchC_C_def by blast
         thus ?thesis unfolding c' thetaPar_def
         apply simp by(metis ParCL c2d2)
       next      
         assume "(c1, s) \<rightarrow>t s'" and c': "c' = c2"
         hence "\<exists>t'. (d1, t) \<rightarrow>t t' \<and> s' \<approx> t'"
         using st matchT_T1 unfolding matchT_T_def by auto
         thus ?thesis 
         unfolding c' thetaPar_def
         apply simp by (metis PL.ParTL c2d2) 
       next
         fix c2' assume "(c2, s) \<rightarrow>c (c2', s')" and c': "c' = Par c1 c2'"
         hence "\<exists>d' t'. (d2, t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> c2' \<approx>s d'"
         using st matchC_C2 unfolding matchC_C_def by blast
         thus ?thesis 
         unfolding c' thetaPar_def
         apply simp by (metis ParCR c1d1)
       next
         assume "(c2, s) \<rightarrow>t s'" and c': "c' = c1"
         hence "\<exists>t'. (d2, t) \<rightarrow>t t' \<and> s' \<approx> t'"
         using st matchT_T2 unfolding matchT_T_def by auto
         thus ?thesis 
         unfolding c' thetaPar_def
         apply simp by (metis PL.ParTR c1d1) 
       qed
     qed 
   qed (unfold matchT_T_def, auto)
  }
  thus ?thesis unfolding thetaPar_def by auto
qed

lemma thetaPar_Sbis:
"thetaPar \<subseteq> Sbis"
apply(rule Sbis_coind)
using thetaPar_sym thetaPar_Sretr by auto

theorem Par_Sbis[simp]:
assumes "c1 \<approx>s d1" and "c2 \<approx>s d2"
shows "Par c1 c2 \<approx>s Par d1 d2"
using assms thetaPar_Sbis unfolding thetaPar_def by blast


subsubsection\<open>01T-bisimilarity versus language constructs\<close>

text \<open>Atomic commands:\<close>

theorem Atm_ZObisT:
assumes "compatAtm atm" 
shows "Atm atm \<approx>01T Atm atm"
by (metis Atm_Sbis assms bis_imp)

text\<open>Sequential composition:\<close> 

definition thetaSeqZOT where 
"thetaSeqZOT \<equiv> 
 {(c1 ;; c2, d1 ;; d2) | c1 c2 d1 d2. c1 \<approx>01T d1 \<and> c2 \<approx>01T d2}"

lemma thetaSeqZOT_sym:
"sym thetaSeqZOT"
unfolding thetaSeqZOT_def sym_def using ZObisT_Sym by blast

lemma thetaSeqZOT_ZOretrT:
"thetaSeqZOT \<subseteq> ZOretrT (thetaSeqZOT Un ZObisT)"
proof-
  {fix c1 c2 d1 d2
   assume c1d1: "c1 \<approx>01T d1" and c2d2: "c2 \<approx>01T d2"
   hence matchC_ZOC1: "matchC_ZOC ZObisT c1 d1" and matchC_ZOC2: "matchC_ZOC ZObisT c2 d2"
     and matchT_T1: "matchT_T c1 d1" and matchT_T2: "matchT_T c2 d2"
   using ZObisT_matchC_ZOC ZObisT_matchT_T by auto
   have "(c1 ;; c2, d1 ;; d2) \<in> ZOretrT (thetaSeqZOT Un ZObisT)"
   unfolding ZOretrT_def proof (clarify, intro conjI)
     show "matchC_ZOC (thetaSeqZOT Un ZObisT) (c1 ;; c2) (d1 ;; d2)"
     unfolding matchC_ZOC_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s'
       assume st: "s \<approx> t" assume "(c1 ;; c2, s) \<rightarrow>c (c', s')"
       thus 
       "(s' \<approx> t \<and> (c', d1 ;; d2) \<in> thetaSeqZOT Un ZObisT) \<or>
        (\<exists>d' t'. (d1 ;; d2, t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> (c', d') \<in> thetaSeqZOT Un ZObisT)"
       apply - proof(erule Seq_transC_invert)
         fix c1' assume c1s: "(c1, s) \<rightarrow>c (c1', s')" and c': "c' = c1' ;; c2"
         hence
         "(s' \<approx> t \<and> c1' \<approx>01T d1) \<or> 
          (\<exists>d1' t'. (d1, t) \<rightarrow>c (d1', t') \<and> s' \<approx> t' \<and> c1' \<approx>01T d1')"
         using st matchC_ZOC1 unfolding matchC_ZOC_def by auto
         thus ?thesis unfolding c' thetaSeqZOT_def
         apply - apply(tactic \<open>mauto_no_simp_tac @{context}\<close>)
         apply simp apply (metis c2d2)
         apply simp by (metis SeqC c2d2 ) 
       next      
         assume "(c1, s) \<rightarrow>t s'" and c': "c' = c2"
         hence "\<exists>t'. (d1, t) \<rightarrow>t t' \<and> s' \<approx> t'"
         using st matchT_T1 unfolding matchT_T_def by auto
         thus ?thesis 
         unfolding c' thetaSeqZOT_def
         apply - apply(tactic \<open>mauto_no_simp_tac @{context}\<close>)
         apply simp by (metis PL.SeqT c2d2) 
       qed
     qed 
   qed (unfold matchT_T_def, auto)
  }
  thus ?thesis unfolding thetaSeqZOT_def by auto
qed

lemma thetaSeqZOT_ZObisT:
"thetaSeqZOT \<subseteq> ZObisT"
apply(rule ZObisT_coind)
using thetaSeqZOT_sym thetaSeqZOT_ZOretrT by auto

theorem Seq_ZObisT[simp]:
assumes "c1 \<approx>01T d1" and "c2 \<approx>01T d2"
shows "c1 ;; c2 \<approx>01T d1 ;; d2"
using assms thetaSeqZOT_ZObisT unfolding thetaSeqZOT_def by blast 

text\<open>Conditional:\<close>

definition thetaIfZOT where 
"thetaIfZOT \<equiv> 
 {(If tst c1 c2, If tst d1 d2) | tst c1 c2 d1 d2. compatTst tst \<and> c1 \<approx>01T d1 \<and> c2 \<approx>01T d2}"

lemma thetaIfZOT_sym:
"sym thetaIfZOT"
unfolding thetaIfZOT_def sym_def using ZObisT_Sym by blast

lemma thetaIfZOT_ZOretrT:
"thetaIfZOT \<subseteq> ZOretrT (thetaIfZOT Un ZObisT)"
proof-
  {fix tst c1 c2 d1 d2
   assume tst: "compatTst tst" and c1d1: "c1 \<approx>01T d1" and c2d2: "c2 \<approx>01T d2"
   hence matchC_ZOC1: "matchC_ZOC ZObisT c1 d1" and matchC_ZOC2: "matchC_ZOC ZObisT c2 d2"
     and matchT_T1: "matchT_T c1 d1" and matchT_T2: "matchT_T c2 d2"
   using ZObisT_matchC_ZOC ZObisT_matchT_T by auto
   have "(If tst c1 c2, If tst d1 d2) \<in> ZOretrT (thetaIfZOT Un ZObisT)"
   unfolding ZOretrT_def proof (clarify, intro conjI)
     show "matchC_ZOC (thetaIfZOT Un ZObisT) (If tst c1 c2) (If tst d1 d2)"
     unfolding matchC_ZOC_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s'
       assume st: "s \<approx> t" assume "(If tst c1 c2, s) \<rightarrow>c (c', s')"
       thus 
       "(s' \<approx> t \<and> (c', If tst d1 d2) \<in> thetaIfZOT Un ZObisT) \<or>
        (\<exists>d' t'. (If tst d1 d2, t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> (c', d') \<in> thetaIfZOT Un ZObisT)"
       apply - apply(erule If_transC_invert)
       unfolding thetaIfZOT_def 
       apply simp apply (metis IfTrue c1d1 compatTst_def st tst)
       apply simp by (metis IfFalse c2d2 compatTst_def st tst)
     qed
   qed (unfold matchT_T_def, auto)
  }
  thus ?thesis unfolding thetaIfZOT_def by auto
qed

lemma thetaIfZOT_ZObisT:
"thetaIfZOT \<subseteq> ZObisT"
apply(rule ZObisT_coind)
using thetaIfZOT_sym thetaIfZOT_ZOretrT by auto

theorem If_ZObisT[simp]:
assumes "compatTst tst" and "c1 \<approx>01T d1" and "c2 \<approx>01T d2"
shows "If tst c1 c2 \<approx>01T If tst d1 d2"
using assms thetaIfZOT_ZObisT unfolding thetaIfZOT_def by blast

text\<open>While loop:\<close>

definition thetaWhileZOT where 
"thetaWhileZOT \<equiv> 
 {(While tst c, While tst d) | tst c d. compatTst tst \<and> c \<approx>01T d} Un 
 {(c1 ;; (While tst c), d1 ;; (While tst d)) | tst c1 d1 c d. compatTst tst \<and> c1 \<approx>01T d1 \<and> c \<approx>01T d}"

lemma thetaWhileZOT_sym:
"sym thetaWhileZOT"
unfolding thetaWhileZOT_def sym_def using ZObisT_Sym by blast

lemma thetaWhileZOT_ZOretrT:
"thetaWhileZOT \<subseteq> ZOretrT (thetaWhileZOT Un ZObisT)"
proof-
  {fix tst c d 
   assume tst: "compatTst tst" and c_d: "c \<approx>01T d"
   hence matchC_ZOC: "matchC_ZOC ZObisT c d" 
     and matchT_T: "matchT_T c d" 
   using ZObisT_matchC_ZOC ZObisT_matchT_T by auto
   have "(While tst c, While tst d) \<in> ZOretrT (thetaWhileZOT Un ZObisT)"
   unfolding ZOretrT_def proof (clarify, intro conjI)
     show "matchC_ZOC (thetaWhileZOT \<union> ZObisT) (While tst c) (While tst d)"
     unfolding matchC_ZOC_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s'
       assume st: "s \<approx> t" assume "(While tst c, s) \<rightarrow>c (c', s')"
       thus 
       "(s' \<approx> t \<and> (c', While tst d) \<in> thetaWhileZOT \<union> ZObisT) \<or> 
        (\<exists>d' t'. (While tst d, t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> (c', d') \<in> thetaWhileZOT \<union> ZObisT)"
       apply - apply(erule While_transC_invert)
       unfolding thetaWhileZOT_def apply simp
       by (metis WhileTrue c_d compatTst_def st tst)
     qed
   next
     show "matchT_T (While tst c) (While tst d)"
     unfolding matchT_T_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t s' assume st: "s \<approx> t" assume "(While tst c, s) \<rightarrow>t s'"
       thus "\<exists>t'. (While tst d, t) \<rightarrow>t t' \<and> s' \<approx> t' "
       apply - apply(erule While_transT_invert)
       unfolding thetaWhileZOT_def apply simp
       by (metis PL.WhileFalse compatTst_def st tst)    
     qed
   qed
  }
  moreover 
  {fix tst c1 d1  c d
   assume tst: "compatTst tst" and c1d1: "c1 \<approx>01T d1" and c_d: "c \<approx>01T d"
   hence matchC_ZOC1: "matchC_ZOC ZObisT c1 d1" and matchC_ZOC: "matchC_ZOC ZObisT c d" 
     and matchT_T1: "matchT_T c1 d1" and matchT_T: "matchT_T c d"
   using ZObisT_matchC_ZOC ZObisT_matchT_T by auto
   have "(c1 ;; (While tst c), d1 ;; (While tst d)) \<in> ZOretrT (thetaWhileZOT Un ZObisT)"
   unfolding ZOretrT_def proof (clarify, intro conjI)
     show "matchC_ZOC (thetaWhileZOT \<union> ZObisT) (c1 ;; (While tst c)) (d1 ;; (While tst d))"
     unfolding matchC_ZOC_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s'
       assume st: "s \<approx> t" assume "(c1 ;; (While tst c), s) \<rightarrow>c (c', s')"
       thus 
       "(s' \<approx> t \<and> (c', d1 ;; (While tst d)) \<in> thetaWhileZOT \<union> ZObisT) \<or> 
        (\<exists>d' t'. (d1 ;; (While tst d), t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> (c', d') \<in> thetaWhileZOT \<union> ZObisT)"
       apply - proof(erule Seq_transC_invert)
         fix c1' assume "(c1, s) \<rightarrow>c (c1', s')" and c': "c' = c1' ;; (While tst c)"
         hence 
         "(s' \<approx> t \<and> c1' \<approx>01T d1) \<or> 
          (\<exists>d' t'. (d1, t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> c1' \<approx>01T d')" 
         using st matchC_ZOC1 unfolding matchC_ZOC_def by auto
         thus ?thesis
         unfolding c' thetaWhileZOT_def
         apply - apply(tactic \<open>mauto_no_simp_tac @{context}\<close>)
         apply simp apply (metis c_d tst)
         apply simp by (metis SeqC c_d tst) 
       next
         assume "(c1, s) \<rightarrow>t s'" and c': "c' = While tst c"
         hence "\<exists>t'. (d1, t) \<rightarrow>t t' \<and> s' \<approx> t'"
         using st matchT_T1 unfolding matchT_T_def by auto
         thus ?thesis
         unfolding c' thetaWhileZOT_def 
         apply simp by (metis PL.SeqT c_d tst) 
       qed
     qed
   qed (unfold matchT_T_def, auto)
  }
  ultimately show ?thesis unfolding thetaWhileZOT_def by auto
qed

lemma thetaWhileZOT_ZObisT:
"thetaWhileZOT \<subseteq> ZObisT"
apply(rule ZObisT_coind)
using thetaWhileZOT_sym thetaWhileZOT_ZOretrT by auto

theorem While_ZObisT[simp]:
assumes "compatTst tst" and "c \<approx>01T d"
shows "While tst c \<approx>01T While tst d"
using assms thetaWhileZOT_ZObisT unfolding thetaWhileZOT_def by auto

text\<open>Parallel composition:\<close>

definition thetaParZOT where 
"thetaParZOT \<equiv> 
 {(Par c1 c2, Par d1 d2) | c1 c2 d1 d2. c1 \<approx>01T d1 \<and> c2 \<approx>01T d2}"

lemma thetaParZOT_sym:
"sym thetaParZOT"
unfolding thetaParZOT_def sym_def using ZObisT_Sym by blast

lemma thetaParZOT_ZOretrT:
"thetaParZOT \<subseteq> ZOretrT (thetaParZOT Un ZObisT)"
proof-
  {fix c1 c2 d1 d2
   assume c1d1: "c1 \<approx>01T d1" and c2d2: "c2 \<approx>01T d2"
   hence matchC_ZOC1: "matchC_ZOC ZObisT c1 d1" and matchC_ZOC2: "matchC_ZOC ZObisT c2 d2"
     and matchT_T1: "matchT_T c1 d1" and matchT_T2: "matchT_T c2 d2"
   using ZObisT_matchC_ZOC ZObisT_matchT_T by auto
   have "(Par c1 c2, Par d1 d2) \<in> ZOretrT (thetaParZOT Un ZObisT)"
   unfolding ZOretrT_def proof (clarify, intro conjI)
     show "matchC_ZOC (thetaParZOT \<union> ZObisT) (Par c1 c2) (Par d1 d2)"
     unfolding matchC_ZOC_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s'
       assume st: "s \<approx> t" assume "(Par c1 c2, s) \<rightarrow>c (c', s')"
       thus 
       "(s' \<approx> t \<and> (c', Par d1 d2) \<in> thetaParZOT \<union> ZObisT) \<or>
        (\<exists>d' t'. (Par d1 d2, t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> (c', d') \<in> thetaParZOT \<union> ZObisT)"
       apply - proof(erule Par_transC_invert)
         fix c1' assume c1s: "(c1, s) \<rightarrow>c (c1', s')" and c': "c' = Par c1' c2"
         hence
         "(s' \<approx> t \<and> c1' \<approx>01T d1) \<or> 
          (\<exists>d' t'. (d1, t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> c1' \<approx>01T d')"
         using st matchC_ZOC1 unfolding matchC_ZOC_def by auto
         thus ?thesis unfolding c' thetaParZOT_def
         apply - apply(tactic \<open>mauto_no_simp_tac @{context}\<close>)
         apply simp apply (metis c2d2)
         apply simp by(metis ParCL c2d2)
       next      
         assume "(c1, s) \<rightarrow>t s'" and c': "c' = c2"
         hence "\<exists>t'. (d1, t) \<rightarrow>t t' \<and> s' \<approx> t'"
         using st matchT_T1 unfolding matchT_T_def by auto
         thus ?thesis 
         unfolding c' thetaParZOT_def
         apply simp by (metis PL.ParTL c2d2) 
       next
         fix c2' assume "(c2, s) \<rightarrow>c (c2', s')" and c': "c' = Par c1 c2'"
         hence 
         "(s' \<approx> t \<and> c2' \<approx>01T d2) \<or> 
          (\<exists>d' t'. (d2, t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> c2' \<approx>01T d')"
         using st matchC_ZOC2 unfolding matchC_ZOC_def by auto
         thus ?thesis 
         unfolding c' thetaParZOT_def
         apply - apply(tactic \<open>mauto_no_simp_tac @{context}\<close>)
         apply simp apply (metis c1d1)
         apply simp by (metis ParCR c1d1)
       next
         assume "(c2, s) \<rightarrow>t s'" and c': "c' = c1"
         hence "\<exists>t'. (d2, t) \<rightarrow>t t' \<and> s' \<approx> t'"
         using st matchT_T2 unfolding matchT_T_def by auto
         thus ?thesis 
         unfolding c' thetaParZOT_def
         apply simp by (metis PL.ParTR c1d1) 
       qed
     qed 
   qed (unfold matchT_T_def, auto)
  }
  thus ?thesis unfolding thetaParZOT_def by auto
qed

lemma thetaParZOT_ZObisT:
"thetaParZOT \<subseteq> ZObisT"
apply(rule ZObisT_coind)
using thetaParZOT_sym thetaParZOT_ZOretrT by auto

theorem Par_ZObisT[simp]:
assumes "c1 \<approx>01T d1" and "c2 \<approx>01T d2"
shows "Par c1 c2 \<approx>01T Par d1 d2"
using assms thetaParZOT_ZObisT unfolding thetaParZOT_def by blast


subsubsection\<open>01-bisimilarity versus language constructs\<close>

text\<open>Discreetness:\<close>

theorem discr_ZObis[simp]:
assumes *: "discr c" and **: "discr d"
shows "c \<approx>01 d"
proof-
  let ?theta = "{(c,d) | c d. discr c \<and> discr d}"
  have "?theta \<subseteq> ZObis"
  proof(rule ZObis_raw_coind)
    show "sym ?theta" unfolding sym_def by blast
  next
    show "?theta \<subseteq> ZOretr ?theta"
    proof clarify
      fix c d assume c: "discr c" and d: "discr d"
      show "(c, d) \<in> ZOretr ?theta"
      unfolding ZOretr_def proof (clarify, intro conjI)
        show "matchC_ZO ?theta c d"
        unfolding matchC_ZO_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
          fix s t c' s'
          assume st: "s \<approx> t" and cs: "(c, s) \<rightarrow>c (c', s')"
          show 
          "(s' \<approx> t \<and> (c', d) \<in> ?theta) \<or>
           (\<exists>d' t'. (d, t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> (c', d') \<in> ?theta) \<or>
           (\<exists>t'. (d, t) \<rightarrow>t t' \<and> s' \<approx> t' \<and> discr c')"
          proof-
            have "s \<approx> s'" using c cs discr_transC_indis by blast
            hence s't: "s' \<approx> t" using st indis_trans indis_sym by blast
            have "discr c'" using c cs discr_transC by blast
            hence "(c',d) \<in> ?theta" using d by blast
            thus ?thesis using s't by blast
          qed
        qed
      next
        show "matchT_ZO c d"
        unfolding matchT_ZO_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
          fix s t s'
          assume st: "s \<approx> t" and cs: "(c, s) \<rightarrow>t s'"
          show 
          "(s' \<approx> t \<and> discr d) \<or>
           (\<exists>d' t'. (d, t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> discr d') \<or>
           (\<exists>t'. (d, t) \<rightarrow>t t' \<and> s' \<approx> t')"
          proof-
            have "s \<approx> s'" using c cs discr_transT by blast
            hence s't: "s' \<approx> t" using st indis_trans indis_sym by blast
            thus ?thesis using d by blast
          qed
        qed
      qed
    qed
  qed
  thus ?thesis using assms by blast
qed

text \<open>Atomic commands:\<close>

theorem Atm_ZObis[simp]:
assumes "compatAtm atm" 
shows "Atm atm \<approx>01 Atm atm"
by (metis Atm_Sbis assms bis_imp) 

text\<open>Sequential composition:\<close>

definition thetaSeqZO where 
"thetaSeqZO \<equiv> 
 {(c1 ;; c2, d1 ;; d2) | c1 c2 d1 d2. c1 \<approx>01T d1 \<and> c2 \<approx>01 d2}"

lemma thetaSeqZO_sym:
"sym thetaSeqZO"
unfolding thetaSeqZO_def sym_def using ZObisT_Sym ZObis_Sym by blast

lemma thetaSeqZO_ZOretr:
"thetaSeqZO \<subseteq> ZOretr (thetaSeqZO Un ZObis)"
proof-
  {fix c1 c2 d1 d2
   assume c1d1: "c1 \<approx>01T d1" and c2d2: "c2 \<approx>01 d2"
   hence matchC_ZOC1: "matchC_ZOC ZObisT c1 d1" and matchC_ZO2: "matchC_ZO ZObis c2 d2"
     and matchT_T1: "matchT_T c1 d1" and matchT_ZO2: "matchT_ZO c2 d2"
   using ZObisT_matchC_ZOC ZObisT_matchT_T ZObis_matchC_ZO ZObis_matchT_ZO by auto
   have "(c1 ;; c2, d1 ;; d2) \<in> ZOretr (thetaSeqZO Un ZObis)"
   unfolding ZOretr_def proof (clarify, intro conjI)
     show "matchC_ZO (thetaSeqZO Un ZObis) (c1 ;; c2) (d1 ;; d2)"
     unfolding matchC_ZO_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s'
       assume st: "s \<approx> t" assume "(c1 ;; c2, s) \<rightarrow>c (c', s')"
       thus 
       "(s' \<approx> t \<and> (c', d1 ;; d2) \<in> thetaSeqZO Un ZObis) \<or>
        (\<exists>d' t'. (d1 ;; d2, t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> (c', d') \<in> thetaSeqZO Un ZObis) \<or> 
        (\<exists>t'. (d1 ;; d2, t) \<rightarrow>t t' \<and> s' \<approx> t' \<and> discr c')"
       apply - proof(erule Seq_transC_invert)
         fix c1' assume c1s: "(c1, s) \<rightarrow>c (c1', s')" and c': "c' = c1' ;; c2"
         hence
         "(s' \<approx> t \<and> c1' \<approx>01T d1) \<or> 
          (\<exists>d1' t'. (d1, t) \<rightarrow>c (d1', t') \<and> s' \<approx> t' \<and> c1' \<approx>01T d1')"
         using st matchC_ZOC1 unfolding matchC_ZOC_def by auto
         thus ?thesis unfolding c' thetaSeqZO_def
         apply - apply(tactic \<open>mauto_no_simp_tac @{context}\<close>)
         apply simp apply (metis c2d2)
         apply simp by (metis SeqC c2d2 ) 
       next      
         assume "(c1, s) \<rightarrow>t s'" and c': "c' = c2"
         hence "\<exists>t'. (d1, t) \<rightarrow>t t' \<and> s' \<approx> t'"
         using st matchT_T1 unfolding matchT_T_def by auto
         thus ?thesis 
         unfolding c' thetaSeqZO_def
         apply - apply(tactic \<open>mauto_no_simp_tac @{context}\<close>)
         apply simp by (metis PL.SeqT c2d2) 
       qed
     qed 
   qed (unfold matchT_ZO_def, auto)
  }
  thus ?thesis unfolding thetaSeqZO_def by auto
qed

lemma thetaSeqZO_ZObis:
"thetaSeqZO \<subseteq> ZObis"
apply(rule ZObis_coind)
using thetaSeqZO_sym thetaSeqZO_ZOretr by auto

theorem Seq_ZObisT_ZObis[simp]:
assumes "c1 \<approx>01T d1" and "c2 \<approx>01 d2"
shows "c1 ;; c2 \<approx>01 d1 ;; d2"
using assms thetaSeqZO_ZObis unfolding thetaSeqZO_def by blast

theorem Seq_siso_ZObis[simp]:
assumes "siso e" and "c2 \<approx>01 d2"
shows "e ;; c2 \<approx>01 e ;; d2"
using assms by auto

(*  *)

definition thetaSeqZOD where 
"thetaSeqZOD \<equiv> 
 {(c1 ;; c2, d1 ;; d2) | c1 c2 d1 d2. c1 \<approx>01 d1 \<and> discr c2 \<and> discr d2}"

lemma thetaSeqZOD_sym:
"sym thetaSeqZOD"
unfolding thetaSeqZOD_def sym_def using ZObis_Sym by blast

lemma thetaSeqZOD_ZOretr:
"thetaSeqZOD \<subseteq> ZOretr (thetaSeqZOD Un ZObis)"
proof-
  {fix c1 c2 d1 d2
   assume c1d1: "c1 \<approx>01 d1" and c2: "discr c2" and d2: "discr d2"
   hence matchC_ZO: "matchC_ZO ZObis c1 d1" 
     and matchT_ZO: "matchT_ZO c1 d1"
   using ZObis_matchC_ZO ZObis_matchT_ZO by auto
   have "(c1 ;; c2, d1 ;; d2) \<in> ZOretr (thetaSeqZOD Un ZObis)"
   unfolding ZOretr_def proof (clarify, intro conjI)
     show "matchC_ZO (thetaSeqZOD Un ZObis) (c1 ;; c2) (d1 ;; d2)"
     unfolding matchC_ZO_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s'
       assume st: "s \<approx> t" assume "(c1 ;; c2, s) \<rightarrow>c (c', s')"
       thus 
       "(s' \<approx> t \<and> (c', d1 ;; d2) \<in> thetaSeqZOD Un ZObis) \<or>
        (\<exists>d' t'. (d1 ;; d2, t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> (c', d') \<in> thetaSeqZOD Un ZObis) \<or> 
        (\<exists>t'. (d1 ;; d2, t) \<rightarrow>t t' \<and> s' \<approx> t' \<and> discr c')"
       apply - proof(erule Seq_transC_invert)
         fix c1' assume c1s: "(c1, s) \<rightarrow>c (c1', s')" and c': "c' = c1' ;; c2"
         hence
         "(s' \<approx> t \<and> c1' \<approx>01 d1) \<or> 
          (\<exists>d' t'. (d1, t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> c1' \<approx>01 d') \<or> 
          (\<exists>t'. (d1, t) \<rightarrow>t t' \<and> s' \<approx> t' \<and> discr c1')"
         using st matchC_ZO unfolding matchC_ZO_def by auto
         thus ?thesis unfolding c' thetaSeqZOD_def
         apply - apply(tactic \<open>mauto_no_simp_tac @{context}\<close>)
         apply simp apply (metis c2 d2)
         apply simp apply (metis SeqC c2 d2)
         apply simp by (metis SeqT c2 d2 discr_Seq discr_ZObis) 
       next      
         assume "(c1, s) \<rightarrow>t s'" and c': "c' = c2"
         hence 
         "(s' \<approx> t \<and> discr d1) \<or> 
          (\<exists>d' t'. (d1, t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> discr d') \<or> 
          (\<exists>t'. (d1, t) \<rightarrow>t t' \<and> s' \<approx> t')"
         using st matchT_ZO unfolding matchT_ZO_def by auto
         thus ?thesis 
         unfolding c' thetaSeqZOD_def
         apply - apply(tactic \<open>mauto_no_simp_tac @{context}\<close>)
         apply simp apply (metis c2 d2 discr_Seq discr_ZObis)
         apply simp apply (metis SeqC c2 d2 discr_Seq discr_ZObis)
         apply simp by (metis SeqT c2 d2 discr_ZObis) 
       qed
     qed 
   qed (unfold matchT_ZO_def, auto)
  }
  thus ?thesis unfolding thetaSeqZOD_def by auto
qed

lemma thetaSeqZOD_ZObis:
"thetaSeqZOD \<subseteq> ZObis"
apply(rule ZObis_coind)
using thetaSeqZOD_sym thetaSeqZOD_ZOretr by auto

theorem Seq_ZObis_discr[simp]:
assumes "c1 \<approx>01 d1" and "discr c2" and "discr d2"
shows "c1 ;; c2 \<approx>01 d1 ;; d2"
using assms thetaSeqZOD_ZObis unfolding thetaSeqZOD_def by blast

text\<open>Conditional:\<close>

definition thetaIfZO where 
"thetaIfZO \<equiv> 
 {(If tst c1 c2, If tst d1 d2) | tst c1 c2 d1 d2. compatTst tst \<and> c1 \<approx>01 d1 \<and> c2 \<approx>01 d2}"

lemma thetaIfZO_sym:
"sym thetaIfZO"
unfolding thetaIfZO_def sym_def using ZObis_Sym by blast

lemma thetaIfZO_ZOretr:
"thetaIfZO \<subseteq> ZOretr (thetaIfZO Un ZObis)"
proof-
  {fix tst c1 c2 d1 d2
   assume tst: "compatTst tst" and c1d1: "c1 \<approx>01 d1" and c2d2: "c2 \<approx>01 d2"
   hence matchC_ZO1: "matchC_ZO ZObis c1 d1" and matchC_ZO2: "matchC_ZO ZObis c2 d2"
     and matchT_ZO1: "matchT_ZO c1 d1" and matchT_ZO2: "matchT_ZO c2 d2"
   using ZObis_matchC_ZO ZObis_matchT_ZO by auto
   have "(If tst c1 c2, If tst d1 d2) \<in> ZOretr (thetaIfZO Un ZObis)"
   unfolding ZOretr_def proof (clarify, intro conjI)
     show "matchC_ZO (thetaIfZO Un ZObis) (If tst c1 c2) (If tst d1 d2)"
     unfolding matchC_ZO_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s'
       assume st: "s \<approx> t" assume "(If tst c1 c2, s) \<rightarrow>c (c', s')"
       thus 
       "(s' \<approx> t \<and> (c', If tst d1 d2) \<in> thetaIfZO Un ZObis) \<or>
        (\<exists>d' t'. (If tst d1 d2, t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> (c', d') \<in> thetaIfZO Un ZObis) \<or> 
        (\<exists>t'. (If tst d1 d2, t) \<rightarrow>t t' \<and> s' \<approx> t' \<and> discr c')"
       apply - apply(erule If_transC_invert)
       unfolding thetaIfZO_def 
       apply simp apply (metis IfTrue c1d1 compatTst_def st tst)
       apply simp by (metis IfFalse c2d2 compatTst_def st tst)
     qed
   qed (unfold matchT_ZO_def, auto)
  }
  thus ?thesis unfolding thetaIfZO_def by auto
qed

lemma thetaIfZO_ZObis:
"thetaIfZO \<subseteq> ZObis"
apply(rule ZObis_coind)
using thetaIfZO_sym thetaIfZO_ZOretr by auto

theorem If_ZObis[simp]:
assumes "compatTst tst" and "c1 \<approx>01 d1" and "c2 \<approx>01 d2"
shows "If tst c1 c2 \<approx>01 If tst d1 d2"
using assms thetaIfZO_ZObis unfolding thetaIfZO_def by blast

text\<open>While loop:\<close>

text\<open>01-bisimilarity does not interact with / preserve the While construct in 
any interesting way.\<close>

(* Indeed, assume c \<approx>01 d and try to prove while tst c \<approx>01 while tst d.  
If tst is True in some state, we obtain the task of proving c ;; (while tst c) \<approx>01 d ;; (while tst d).  
Now, assume c takes a step to c' and d terminates, possibility allowed by ~01-bisimilarity, 
provided c' is discr.  So now we need to have, for discr c', the following: 
c' ;; (while tst c) \<approx>01 while tst d.  This is not true in general. *)

text\<open>Parallel composition:\<close>

definition thetaParZOL1 where 
"thetaParZOL1 \<equiv> 
 {(Par c1 c2, d) | c1 c2 d. c1 \<approx>01 d \<and> discr c2}"

lemma thetaParZOL1_ZOretr:
"thetaParZOL1 \<subseteq> ZOretr (thetaParZOL1 Un ZObis)"
proof-
  {fix c1 c2 d
   assume c1d: "c1 \<approx>01 d" and c2: "discr c2"
   hence matchC_ZO: "matchC_ZO ZObis c1 d" 
     and matchT_ZO: "matchT_ZO c1 d" 
   using ZObis_matchC_ZO ZObis_matchT_ZO by auto
   have "(Par c1 c2, d) \<in> ZOretr (thetaParZOL1 Un ZObis)"
   unfolding ZOretr_def proof (clarify, intro conjI)
     show "matchC_ZO (thetaParZOL1 \<union> ZObis) (Par c1 c2) d"
     unfolding matchC_ZO_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s'
       assume st: "s \<approx> t" assume "(Par c1 c2, s) \<rightarrow>c (c', s')"
       thus
       "(s' \<approx> t \<and> (c', d) \<in> thetaParZOL1 \<union> ZObis) \<or>
        (\<exists>d' t'. (d, t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> (c', d') \<in> thetaParZOL1 \<union> ZObis) \<or>
        (\<exists>t'. (d, t) \<rightarrow>t t' \<and> s' \<approx> t' \<and> discr c')"
       apply - proof(erule Par_transC_invert)
         fix c1' assume "(c1, s) \<rightarrow>c (c1', s')" and c': "c' = Par c1' c2"
         hence 
         "(s' \<approx> t \<and> c1' \<approx>01 d) \<or> 
          (\<exists>d' t'. (d, t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> c1' \<approx>01 d') \<or> 
          (\<exists>t'. (d, t) \<rightarrow>t t' \<and> s' \<approx> t' \<and> discr c1')"
         using st matchC_ZO unfolding matchC_ZO_def by blast
         thus ?thesis unfolding thetaParZOL1_def
         apply - apply(elim disjE exE conjE) 
         apply simp apply (metis c2 c')
         apply simp apply (metis c2 c')
         apply simp by (metis c' c2 discr_Par) 
       next
         assume "(c1, s) \<rightarrow>t s'" and c': "c' = c2"
         hence 
         "(s' \<approx> t \<and> discr d) \<or> 
          (\<exists>d' t'. (d, t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> discr d') \<or> 
          (\<exists>t'. (d, t) \<rightarrow>t t' \<and> s' \<approx> t')"
         using st matchT_ZO unfolding matchT_ZO_def by blast
         thus ?thesis unfolding thetaParZOL1_def
         apply - apply(elim disjE exE conjE)
         apply simp apply (metis c' c2 discr_ZObis)
         apply simp apply (metis c' c2 discr_ZObis)
         apply simp by (metis c' c2)  
       next
         fix c2' assume c2s: "(c2, s) \<rightarrow>c (c2', s')" and c': "c' = Par c1 c2'"
         hence "s \<approx> s'" using c2 discr_transC_indis by blast
         hence s't: "s' \<approx> t" using st indis_sym indis_trans by blast
         have "discr c2'" using c2 c2s discr_transC by blast
         thus ?thesis using s't c1d unfolding thetaParZOL1_def c' by simp
       next
         assume "(c2, s) \<rightarrow>t s'" and c': "c' = c1"
         hence "s \<approx> s'" using c2 discr_transT by blast
         hence s't: "s' \<approx> t" using st indis_sym indis_trans by blast
         thus ?thesis using c1d unfolding thetaParZOL1_def c' by simp
       qed
     qed
   qed (unfold matchT_ZO_def, auto)
  }
  thus ?thesis unfolding thetaParZOL1_def by blast
qed

lemma thetaParZOL1_converse_ZOretr:
"thetaParZOL1 ^-1 \<subseteq> ZOretr (thetaParZOL1 ^-1 Un ZObis)"
proof-
  {fix c1 c2 d
   assume c1d: "c1 \<approx>01 d" and c2: "discr c2"
   hence matchC_ZO: "matchC_ZO ZObis d c1" 
     and matchT_ZO: "matchT_ZO d c1" 
   using ZObis_matchC_ZO_rev ZObis_matchT_ZO_rev by auto
   have "(d, Par c1 c2) \<in> ZOretr (thetaParZOL1\<inverse> \<union> ZObis)"
   unfolding ZOretr_def proof (clarify, intro conjI)
     show "matchC_ZO (thetaParZOL1\<inverse> \<union> ZObis) d (Par c1 c2)"
     unfolding matchC_ZO_def2 ZObis_converse proof (tactic \<open>mauto_no_simp_tac @{context}\<close>) 
       fix s t d' t'
       assume "s \<approx> t" and "(d, t) \<rightarrow>c (d', t')"
       hence 
       "(s \<approx> t' \<and> d' \<approx>01 c1) \<or> 
        (\<exists>c' s'. (c1, s) \<rightarrow>c (c', s') \<and> s' \<approx> t' \<and> d' \<approx>01 c') \<or> 
        (\<exists>s'. (c1, s) \<rightarrow>t s' \<and> s' \<approx> t' \<and> discr d')"
       using matchC_ZO unfolding matchC_ZO_def2 by auto
       thus
       "(s \<approx> t' \<and> (Par c1 c2, d') \<in> thetaParZOL1 \<union> ZObis) \<or>
        (\<exists>c' s'. (Par c1 c2, s) \<rightarrow>c (c', s') \<and> s' \<approx> t' \<and> (c', d') \<in> thetaParZOL1 \<union> ZObis) \<or>
        (\<exists>s'. (Par c1 c2, s) \<rightarrow>t s' \<and> s' \<approx> t' \<and> discr d')"
       unfolding thetaParZOL1_def 
       apply - apply(tactic \<open>mauto_no_simp_tac @{context}\<close>)
       apply simp apply (metis ZObis_Sym c2)
       apply simp apply (metis ParCL ZObis_sym c2 sym_def)
       apply simp by (metis ParTL c2 discr_ZObis) 
     qed
   next
     show "matchT_ZO d (Par c1 c2)"
     unfolding matchT_ZO_def2 ZObis_converse proof (tactic \<open>mauto_no_simp_tac @{context}\<close>) 
       fix s t t'
       assume "s \<approx> t" and "(d, t) \<rightarrow>t t'"
       hence 
       "(s \<approx> t' \<and> discr c1) \<or> 
        (\<exists>c' s'. (c1, s) \<rightarrow>c (c', s') \<and> s' \<approx> t' \<and> discr c') \<or> 
        (\<exists>s'. (c1, s) \<rightarrow>t s' \<and> s' \<approx> t')"
       using matchT_ZO unfolding matchT_ZO_def2 by auto
       thus
       "(s \<approx> t' \<and> discr (Par c1 c2)) \<or> 
        (\<exists>c' s'. (Par c1 c2, s) \<rightarrow>c (c', s') \<and> s' \<approx> t' \<and> discr c') \<or> 
        (\<exists>s'. (Par c1 c2, s) \<rightarrow>t s' \<and> s' \<approx> t')"
       apply - apply(tactic \<open>mauto_no_simp_tac @{context}\<close>)
       apply simp apply (metis c2 discr_Par)
       apply simp apply (metis ParCL c2 discr_Par)
       apply simp by (metis ParTL c2)
     qed
   qed
  }
  thus ?thesis unfolding thetaParZOL1_def by blast
qed

lemma thetaParZOL1_ZObis:
"thetaParZOL1 \<subseteq> ZObis"
apply(rule ZObis_coind2)
using thetaParZOL1_ZOretr thetaParZOL1_converse_ZOretr by auto

theorem Par_ZObis_discrL1[simp]:
assumes "c1 \<approx>01 d" and "discr c2"
shows "Par c1 c2 \<approx>01 d"
using assms thetaParZOL1_ZObis unfolding thetaParZOL1_def by blast

theorem Par_ZObis_discrR1[simp]:
assumes "c \<approx>01 d1" and "discr d2"
shows "c \<approx>01 Par d1 d2"
using assms Par_ZObis_discrL1 ZObis_Sym by blast

(*  *)

definition thetaParZOL2 where 
"thetaParZOL2 \<equiv> 
 {(Par c1 c2, d) | c1 c2 d. discr c1 \<and> c2 \<approx>01 d}"

lemma thetaParZOL2_ZOretr:
"thetaParZOL2 \<subseteq> ZOretr (thetaParZOL2 Un ZObis)"
proof-
  {fix c1 c2 d
   assume c2d: "c2 \<approx>01 d" and c1: "discr c1" 
   hence matchC_ZO: "matchC_ZO ZObis c2 d" 
     and matchT_ZO: "matchT_ZO c2 d" 
   using ZObis_matchC_ZO ZObis_matchT_ZO by auto
   have "(Par c1 c2, d) \<in> ZOretr (thetaParZOL2 Un ZObis)"
   unfolding ZOretr_def proof (clarify, intro conjI)
     show "matchC_ZO (thetaParZOL2 \<union> ZObis) (Par c1 c2) d"
     unfolding matchC_ZO_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s'
       assume st: "s \<approx> t" assume "(Par c1 c2, s) \<rightarrow>c (c', s')"
       thus
       "(s' \<approx> t \<and> (c', d) \<in> thetaParZOL2 \<union> ZObis) \<or>
        (\<exists>d' t'. (d, t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> (c', d') \<in> thetaParZOL2 \<union> ZObis) \<or>
        (\<exists>t'. (d, t) \<rightarrow>t t' \<and> s' \<approx> t' \<and> discr c')"
       apply - proof(erule Par_transC_invert)
         fix c1' assume c1s: "(c1, s) \<rightarrow>c (c1', s')" and c': "c' = Par c1' c2"
         hence "s \<approx> s'" using c1 discr_transC_indis by blast
         hence s't: "s' \<approx> t" using st indis_sym indis_trans by blast
         have "discr c1'" using c1 c1s discr_transC by blast
         thus ?thesis using s't c2d unfolding thetaParZOL2_def c' by simp
       next
         assume "(c1, s) \<rightarrow>t s'" and c': "c' = c2"
         hence "s \<approx> s'" using c1 discr_transT by blast
         hence s't: "s' \<approx> t" using st indis_sym indis_trans by blast
         thus ?thesis using c2d unfolding thetaParZOL2_def c' by simp
       next
         fix c2' assume "(c2, s) \<rightarrow>c (c2', s')" and c': "c' = Par c1 c2'"
         hence 
         "(s' \<approx> t \<and> c2' \<approx>01 d) \<or> 
          (\<exists>d' t'. (d, t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> c2' \<approx>01 d') \<or> 
          (\<exists>t'. (d, t) \<rightarrow>t t' \<and> s' \<approx> t' \<and> discr c2')"
         using st matchC_ZO unfolding matchC_ZO_def by blast
         thus ?thesis unfolding thetaParZOL2_def
         apply - apply(elim disjE exE conjE) 
         apply simp apply (metis c1 c')
         apply simp apply (metis c1 c')
         apply simp by (metis c' c1 discr_Par) 
       next
         assume "(c2, s) \<rightarrow>t s'" and c': "c' = c1"
         hence 
         "(s' \<approx> t \<and> discr d) \<or> 
          (\<exists>d' t'. (d, t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> discr d') \<or> 
          (\<exists>t'. (d, t) \<rightarrow>t t' \<and> s' \<approx> t')"
         using st matchT_ZO unfolding matchT_ZO_def by blast
         thus ?thesis unfolding thetaParZOL2_def
         apply - apply(elim disjE exE conjE)
         apply simp apply (metis c' c1 discr_ZObis)
         apply simp apply (metis c' c1 discr_ZObis)
         apply simp by (metis c' c1)          
       qed
     qed
   qed (unfold matchT_ZO_def, auto)
  }
  thus ?thesis unfolding thetaParZOL2_def by blast
qed

lemma thetaParZOL2_converse_ZOretr:
"thetaParZOL2 ^-1 \<subseteq> ZOretr (thetaParZOL2 ^-1 Un ZObis)"
proof-
  {fix c1 c2 d
   assume c2d: "c2 \<approx>01 d" and c1: "discr c1"
   hence matchC_ZO: "matchC_ZO ZObis d c2" 
     and matchT_ZO: "matchT_ZO d c2" 
   using ZObis_matchC_ZO_rev ZObis_matchT_ZO_rev by auto
   have "(d, Par c1 c2) \<in> ZOretr (thetaParZOL2\<inverse> \<union> ZObis)"
   unfolding ZOretr_def proof (clarify, intro conjI)
     show "matchC_ZO (thetaParZOL2\<inverse> \<union> ZObis) d (Par c1 c2)"
     unfolding matchC_ZO_def2 ZObis_converse proof (tactic \<open>mauto_no_simp_tac @{context}\<close>) 
       fix s t d' t'
       assume "s \<approx> t" and "(d, t) \<rightarrow>c (d', t')"
       hence 
       "(s \<approx> t' \<and> d' \<approx>01 c2) \<or> 
        (\<exists>c' s'. (c2, s) \<rightarrow>c (c', s') \<and> s' \<approx> t' \<and> d' \<approx>01 c') \<or> 
        (\<exists>s'. (c2, s) \<rightarrow>t s' \<and> s' \<approx> t' \<and> discr d')"
       using matchC_ZO unfolding matchC_ZO_def2 by auto
       thus
       "(s \<approx> t' \<and> (Par c1 c2, d') \<in> thetaParZOL2 \<union> ZObis) \<or>
        (\<exists>c' s'. (Par c1 c2, s) \<rightarrow>c (c', s') \<and> s' \<approx> t' \<and> (c', d') \<in> thetaParZOL2 \<union> ZObis) \<or>
        (\<exists>s'. (Par c1 c2, s) \<rightarrow>t s' \<and> s' \<approx> t' \<and> discr d')"
       unfolding thetaParZOL2_def 
       apply - apply(tactic \<open>mauto_no_simp_tac @{context}\<close>)
       apply simp apply (metis ZObis_Sym c1)
       apply simp apply (metis ParCR ZObis_sym c1 sym_def)
       apply simp by (metis ParTR c1 discr_ZObis) 
     qed
   next
     show "matchT_ZO d (Par c1 c2)"
     unfolding matchT_ZO_def2 ZObis_converse proof (tactic \<open>mauto_no_simp_tac @{context}\<close>) 
       fix s t t'
       assume "s \<approx> t" and "(d, t) \<rightarrow>t t'"
       hence 
       "(s \<approx> t' \<and> discr c2) \<or> 
        (\<exists>c' s'. (c2, s) \<rightarrow>c (c', s') \<and> s' \<approx> t' \<and> discr c') \<or> 
        (\<exists>s'. (c2, s) \<rightarrow>t s' \<and> s' \<approx> t')"
       using matchT_ZO unfolding matchT_ZO_def2 by auto
       thus
       "(s \<approx> t' \<and> discr (Par c1 c2)) \<or> 
        (\<exists>c' s'. (Par c1 c2, s) \<rightarrow>c (c', s') \<and> s' \<approx> t' \<and> discr c') \<or> 
        (\<exists>s'. (Par c1 c2, s) \<rightarrow>t s' \<and> s' \<approx> t')"
       apply - apply(tactic \<open>mauto_no_simp_tac @{context}\<close>)
       apply simp apply (metis c1 discr_Par)
       apply simp apply (metis ParCR c1 discr_Par)
       apply simp by (metis ParTR c1)
     qed
   qed
  }
  thus ?thesis unfolding thetaParZOL2_def by blast
qed

lemma thetaParZOL2_ZObis:
"thetaParZOL2 \<subseteq> ZObis"
apply(rule ZObis_coind2)
using thetaParZOL2_ZOretr thetaParZOL2_converse_ZOretr by auto

theorem Par_ZObis_discrL2[simp]:
assumes "c2 \<approx>01 d" and "discr c1"
shows "Par c1 c2 \<approx>01 d"
using assms thetaParZOL2_ZObis unfolding thetaParZOL2_def by blast

theorem Par_ZObis_discrR2[simp]:
assumes "c \<approx>01 d2" and "discr d1"
shows "c \<approx>01 Par d1 d2"
using assms Par_ZObis_discrL2 ZObis_Sym by blast

(*  *)

definition thetaParZO where 
"thetaParZO \<equiv> 
 {(Par c1 c2, Par d1 d2) | c1 c2 d1 d2. c1 \<approx>01 d1 \<and> c2 \<approx>01 d2}"

lemma thetaParZO_sym:
"sym thetaParZO"
unfolding thetaParZO_def sym_def using ZObis_Sym by blast

lemma thetaParZO_ZOretr:
"thetaParZO \<subseteq> ZOretr (thetaParZO Un ZObis)"
proof-
  {fix c1 c2 d1 d2
   assume c1d1: "c1 \<approx>01 d1" and c2d2: "c2 \<approx>01 d2"
   hence matchC_ZO1: "matchC_ZO ZObis c1 d1" and matchC_ZO2: "matchC_ZO ZObis c2 d2"
     and matchT_ZO1: "matchT_ZO c1 d1" and matchT_ZO2: "matchT_ZO c2 d2"
   using ZObis_matchC_ZO ZObis_matchT_ZO by auto
   have "(Par c1 c2, Par d1 d2) \<in> ZOretr (thetaParZO Un ZObis)"
   unfolding ZOretr_def proof (clarify, intro conjI)
     show "matchC_ZO (thetaParZO \<union> ZObis) (Par c1 c2) (Par d1 d2)"
     unfolding matchC_ZO_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s'
       assume st: "s \<approx> t" assume "(Par c1 c2, s) \<rightarrow>c (c', s')"
       thus 
       "(s' \<approx> t \<and> (c', Par d1 d2) \<in> thetaParZO \<union> ZObis) \<or>
        (\<exists>d' t'. (Par d1 d2, t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> (c', d') \<in> thetaParZO \<union> ZObis) \<or> 
        (\<exists>t'. (Par d1 d2, t) \<rightarrow>t t' \<and> s' \<approx> t' \<and> discr c')"
       apply - proof(erule Par_transC_invert)
         fix c1' assume c1s: "(c1, s) \<rightarrow>c (c1', s')" and c': "c' = Par c1' c2"
         hence
         "(s' \<approx> t \<and> c1' \<approx>01 d1) \<or> 
          (\<exists>d' t'. (d1, t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> c1' \<approx>01 d') \<or> 
          (\<exists>t'. (d1, t) \<rightarrow>t t' \<and> s' \<approx> t' \<and> discr c1')"
         using st matchC_ZO1 unfolding matchC_ZO_def by auto
         thus ?thesis unfolding c' thetaParZO_def
         apply - apply(tactic \<open>mauto_no_simp_tac @{context}\<close>)
         apply simp apply (metis c2d2)
         apply simp apply (metis ParCL c2d2)
         apply simp by (metis ParTL Par_ZObis_discrL2 c2d2)   
       next      
         assume "(c1, s) \<rightarrow>t s'" and c': "c' = c2"
         hence 
         "(s' \<approx> t \<and> discr d1) \<or> 
          (\<exists>d' t'. (d1, t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> discr d') \<or> 
          (\<exists>t'. (d1, t) \<rightarrow>t t' \<and> s' \<approx> t')"
         using st matchT_ZO1 unfolding matchT_ZO_def by auto
         thus ?thesis 
         unfolding c' thetaParZO_def
         apply - apply(tactic \<open>mauto_no_simp_tac @{context}\<close>)
         apply simp apply (metis Par_ZObis_discrR2 c2d2)
         apply simp apply (metis PL.ParCL Par_ZObis_discrR2 c2d2)
         apply simp by (metis PL.ParTL c2d2) 
       next
         fix c2' assume "(c2, s) \<rightarrow>c (c2', s')" and c': "c' = Par c1 c2'"
         hence 
         "(s' \<approx> t \<and> c2' \<approx>01 d2) \<or> 
          (\<exists>d' t'. (d2, t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> c2' \<approx>01 d') \<or> 
          (\<exists>t'. (d2, t) \<rightarrow>t t' \<and> s' \<approx> t' \<and> discr c2')"
         using st matchC_ZO2 unfolding matchC_ZO_def by auto
         thus ?thesis 
         unfolding c' thetaParZO_def
         apply - apply(tactic \<open>mauto_no_simp_tac @{context}\<close>)
         apply simp apply (metis c1d1)
         apply simp apply (metis PL.ParCR c1d1)
         apply simp by (metis PL.ParTR Par_ZObis_discrL1 c1d1)
       next
         assume "(c2, s) \<rightarrow>t s'" and c': "c' = c1"
         hence 
         "(s' \<approx> t \<and> discr d2) \<or> 
          (\<exists>d' t'. (d2, t) \<rightarrow>c (d', t') \<and> s' \<approx> t' \<and> discr d') \<or> 
          (\<exists>t'. (d2, t) \<rightarrow>t t' \<and> s' \<approx> t')"
         using st matchT_ZO2 unfolding matchT_ZO_def by auto
         thus ?thesis 
         unfolding c' thetaParZO_def
         apply - apply(tactic \<open>mauto_no_simp_tac @{context}\<close>)
         apply simp apply (metis Par_ZObis_discrR1 c1d1)
         apply simp apply (metis PL.ParCR Par_ZObis_discrR1 c1d1)
         apply simp by (metis PL.ParTR c1d1) 
       qed
     qed 
   qed (unfold matchT_ZO_def, auto)
  }
  thus ?thesis unfolding thetaParZO_def by auto
qed

lemma thetaParZO_ZObis:
"thetaParZO \<subseteq> ZObis"
apply(rule ZObis_coind)
using thetaParZO_sym thetaParZO_ZOretr by auto

theorem Par_ZObis[simp]:
assumes "c1 \<approx>01 d1" and "c2 \<approx>01 d2"
shows "Par c1 c2 \<approx>01 Par d1 d2"
using assms thetaParZO_ZObis unfolding thetaParZO_def by blast


subsubsection\<open>WT-bisimilarity versus language constructs\<close>

text\<open>Discreetness:\<close>

theorem noWhile_discr_WbisT[simp]:
  assumes "noWhile c1" and "noWhile c2" 
  and "discr c1" and "discr c2"
  shows "c1 \<approx>wT c2"
proof -
  from assms have "noWhile c1 \<and> noWhile c2 \<and> discr c1 \<and> discr c2" by auto
  then show ?thesis
  proof (induct rule: WbisT_coinduct)
    case cont then show ?case
      by (metis MtransC_Refl noWhile_transC discr_transC discr_transC_indis indis_sym indis_trans) 
  next
    case termi then show ?case
      by (metis discr_MtransT indis_sym indis_trans noWhile_MtransT transT_MtransT)
  qed simp
qed

text \<open>Atomic commands:\<close>

theorem Atm_WbisT:
assumes "compatAtm atm" 
shows "Atm atm \<approx>wT Atm atm"
by (metis Atm_Sbis assms bis_imp)

text\<open>Sequential composition:\<close> 

definition thetaSeqWT where 
"thetaSeqWT \<equiv> 
 {(c1 ;; c2, d1 ;; d2) | c1 c2 d1 d2. c1 \<approx>wT d1 \<and> c2 \<approx>wT d2}"

lemma thetaSeqWT_sym:
"sym thetaSeqWT"
unfolding thetaSeqWT_def sym_def using WbisT_Sym by blast

lemma thetaSeqWT_WretrT:
"thetaSeqWT \<subseteq> WretrT (thetaSeqWT Un WbisT)"
proof- 
  {fix c1 c2 d1 d2
   assume c1d1: "c1 \<approx>wT d1" and c2d2: "c2 \<approx>wT d2"
   hence matchC_MC1: "matchC_MC WbisT c1 d1" and matchC_MC2: "matchC_MC WbisT c2 d2"
     and matchT_MT1: "matchT_MT c1 d1" and matchT_T2: "matchT_MT c2 d2"
   using WbisT_matchC_MC WbisT_matchT_MT by auto
   have "(c1 ;; c2, d1 ;; d2) \<in> WretrT (thetaSeqWT Un WbisT)"
   unfolding WretrT_def proof (clarify, intro conjI)
     show "matchC_MC (thetaSeqWT Un WbisT) (c1 ;; c2) (d1 ;; d2)"
     unfolding matchC_MC_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s'
       assume st: "s \<approx> t" assume "(c1 ;; c2, s) \<rightarrow>c (c', s')"
       thus "(\<exists>d' t'. (d1 ;; d2, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> (c', d') \<in> thetaSeqWT Un WbisT)"
       apply - proof(erule Seq_transC_invert)
         fix c1' assume c1s: "(c1, s) \<rightarrow>c (c1', s')" and c': "c' = c1' ;; c2"
         hence "\<exists>d1' t'. (d1, t) \<rightarrow>*c (d1', t') \<and> s' \<approx> t' \<and> c1' \<approx>wT d1'"
         using st matchC_MC1 unfolding matchC_MC_def by blast
         thus ?thesis unfolding c' thetaSeqWT_def
         apply simp by (metis PL.Seq_MtransC c2d2) 
       next      
         assume "(c1, s) \<rightarrow>t s'" and c': "c' = c2"
         hence "\<exists>t'. (d1, t) \<rightarrow>*t t' \<and> s' \<approx> t'"
         using st matchT_MT1 unfolding matchT_MT_def by auto
         thus ?thesis 
         unfolding c' thetaSeqWT_def
         apply - apply(tactic \<open>mauto_no_simp_tac @{context}\<close>)
         apply simp by (metis Seq_MtransT_MtransC c2d2) 
       qed
     qed 
   qed (unfold matchT_MT_def, auto)
  }
  thus ?thesis unfolding thetaSeqWT_def by auto
qed

lemma thetaSeqWT_WbisT:
"thetaSeqWT \<subseteq> WbisT"
apply(rule WbisT_coind)
using thetaSeqWT_sym thetaSeqWT_WretrT by auto

theorem Seq_WbisT[simp]:
assumes "c1 \<approx>wT d1" and "c2 \<approx>wT d2"
shows "c1 ;; c2 \<approx>wT d1 ;; d2"
using assms thetaSeqWT_WbisT unfolding thetaSeqWT_def by blast 

text\<open>Conditional:\<close>

definition thetaIfWT where 
"thetaIfWT \<equiv> 
 {(If tst c1 c2, If tst d1 d2) | tst c1 c2 d1 d2. compatTst tst \<and> c1 \<approx>wT d1 \<and> c2 \<approx>wT d2}"

lemma thetaIfWT_sym:
"sym thetaIfWT"
unfolding thetaIfWT_def sym_def using WbisT_Sym by blast

lemma thetaIfWT_WretrT:
"thetaIfWT \<subseteq> WretrT (thetaIfWT Un WbisT)"
proof- 
  {fix tst c1 c2 d1 d2
   assume tst: "compatTst tst" and c1d1: "c1 \<approx>wT d1" and c2d2: "c2 \<approx>wT d2"
   hence matchC_MC1: "matchC_MC WbisT c1 d1" and matchC_MC2: "matchC_MC WbisT c2 d2"
     and matchT_MT1: "matchT_MT c1 d1" and matchT_MT2: "matchT_MT c2 d2"
   using WbisT_matchC_MC WbisT_matchT_MT by auto
   have "(If tst c1 c2, If tst d1 d2) \<in> WretrT (thetaIfWT Un WbisT)"
   unfolding WretrT_def proof (clarify, intro conjI)
     show "matchC_MC (thetaIfWT Un WbisT) (If tst c1 c2) (If tst d1 d2)"
     unfolding matchC_MC_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s'
       assume st: "s \<approx> t" assume "(If tst c1 c2, s) \<rightarrow>c (c', s')"
       thus "\<exists>d' t'. (If tst d1 d2, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> (c', d') \<in> thetaIfWT Un WbisT"
       apply - apply(erule If_transC_invert)
       unfolding thetaIfWT_def 
       apply simp apply (metis IfTrue c1d1 compatTst_def st transC_MtransC tst) 
       apply simp by (metis IfFalse c2d2 compatTst_def st transC_MtransC tst) 
     qed
   qed (unfold matchT_MT_def, auto)
  }
  thus ?thesis unfolding thetaIfWT_def by auto
qed

lemma thetaIfWT_WbisT:
"thetaIfWT \<subseteq> WbisT"
apply(rule WbisT_coind)
using thetaIfWT_sym thetaIfWT_WretrT by auto

theorem If_WbisT[simp]:
assumes "compatTst tst" and "c1 \<approx>wT d1" and "c2 \<approx>wT d2"
shows "If tst c1 c2 \<approx>wT If tst d1 d2"
using assms thetaIfWT_WbisT unfolding thetaIfWT_def by blast

text\<open>While loop:\<close>

definition thetaWhileW where 
"thetaWhileW \<equiv> 
 {(While tst c, While tst d) | tst c d. compatTst tst \<and> c \<approx>wT d} Un 
 {(c1 ;; (While tst c), d1 ;; (While tst d)) | tst c1 d1 c d. 
               compatTst tst \<and> c1 \<approx>wT d1 \<and> c \<approx>wT d}"

lemma thetaWhileW_sym:
"sym thetaWhileW"
unfolding thetaWhileW_def sym_def using WbisT_Sym by blast

lemma thetaWhileW_WretrT:
"thetaWhileW \<subseteq> WretrT (thetaWhileW Un WbisT)"
proof-
  {fix tst c d 
   assume tst: "compatTst tst" and c_d: "c \<approx>wT d"
   hence matchC_MC: "matchC_MC WbisT c d" 
     and matchT_MT: "matchT_MT c d" 
   using WbisT_matchC_MC WbisT_matchT_MT by auto
   have "(While tst c, While tst d) \<in> WretrT (thetaWhileW Un WbisT)"
   unfolding WretrT_def proof (clarify, intro conjI)
     show "matchC_MC (thetaWhileW \<union> WbisT) (While tst c) (While tst d)"
     unfolding matchC_MC_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s'
       assume st: "s \<approx> t" assume "(While tst c, s) \<rightarrow>c (c', s')"
       thus "\<exists>d' t'. (While tst d, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> 
                     (c', d') \<in> thetaWhileW \<union> WbisT"
       apply - apply(erule While_transC_invert)
       unfolding thetaWhileW_def apply simp
       by (metis PL.WhileTrue PL.transC_MtransC c_d compatTst_def st tst)
     qed
   next
     show "matchT_MT (While tst c) (While tst d)"
     unfolding matchT_MT_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t s' assume st: "s \<approx> t" assume "(While tst c, s) \<rightarrow>t s'"
       thus "\<exists>t'. (While tst d, t) \<rightarrow>*t t' \<and> s' \<approx> t' "
       apply - apply(erule While_transT_invert)
       unfolding thetaWhileW_def apply simp
       by (metis WhileFalse compatTst_def st transT_MtransT tst)       
     qed
   qed
  }
  moreover 
  {fix tst c1 d1  c d
   assume tst: "compatTst tst" and c1d1: "c1 \<approx>wT d1" and c_d: "c \<approx>wT d"
   hence matchC_MC1: "matchC_MC WbisT c1 d1" and matchC_MC: "matchC_MC WbisT c d" 
     and matchT_MT1: "matchT_MT c1 d1" and matchT_MT: "matchT_MT c d"
   using WbisT_matchC_MC WbisT_matchT_MT by auto
   have "(c1 ;; (While tst c), d1 ;; (While tst d)) \<in> WretrT (thetaWhileW Un WbisT)"
   unfolding WretrT_def proof (clarify, intro conjI)
     show "matchC_MC (thetaWhileW \<union> WbisT) (c1 ;; (While tst c)) (d1 ;; (While tst d))"
     unfolding matchC_MC_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s'
       assume st: "s \<approx> t" assume "(c1 ;; (While tst c), s) \<rightarrow>c (c', s')"
       thus "\<exists>d' t'. (d1 ;; (While tst d), t) \<rightarrow>*c (d', t') \<and> 
                     s' \<approx> t' \<and> (c', d') \<in> thetaWhileW \<union> WbisT"
       apply - proof(erule Seq_transC_invert)
         fix c1' assume "(c1, s) \<rightarrow>c (c1', s')" and c': "c' = c1' ;; (While tst c)"
         hence "\<exists>d' t'. (d1, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> c1' \<approx>wT d'" 
         using st matchC_MC1 unfolding matchC_MC_def by blast
         thus ?thesis
         unfolding c' thetaWhileW_def
         apply simp by (metis PL.Seq_MtransC c_d tst)
       next
         assume "(c1, s) \<rightarrow>t s'" and c': "c' = While tst c"
         hence "\<exists>t'. (d1, t) \<rightarrow>*t t' \<and> s' \<approx> t'"
         using st matchT_MT1 unfolding matchT_MT_def by auto
         thus ?thesis
         unfolding c' thetaWhileW_def 
         apply simp by (metis PL.Seq_MtransT_MtransC c_d tst)
       qed
     qed
   qed (unfold matchT_MT_def, auto)
  }
  ultimately show ?thesis unfolding thetaWhileW_def by auto
qed

lemma thetaWhileW_WbisT:
"thetaWhileW \<subseteq> WbisT"
apply(rule WbisT_coind)
using thetaWhileW_sym thetaWhileW_WretrT by auto

theorem While_WbisT[simp]:
assumes "compatTst tst" and "c \<approx>wT d"
shows "While tst c \<approx>wT While tst d"
using assms thetaWhileW_WbisT unfolding thetaWhileW_def by auto

text\<open>Parallel composition:\<close>

definition thetaParWT where 
"thetaParWT \<equiv> 
 {(Par c1 c2, Par d1 d2) | c1 c2 d1 d2. c1 \<approx>wT d1 \<and> c2 \<approx>wT d2}"

lemma thetaParWT_sym:
"sym thetaParWT"
unfolding thetaParWT_def sym_def using WbisT_Sym by blast

lemma thetaParWT_WretrT:
"thetaParWT \<subseteq> WretrT (thetaParWT Un WbisT)"
proof-
  {fix c1 c2 d1 d2
   assume c1d1: "c1 \<approx>wT d1" and c2d2: "c2 \<approx>wT d2"
   hence matchC_MC1: "matchC_MC WbisT c1 d1" and matchC_MC2: "matchC_MC WbisT c2 d2"
     and matchT_MT1: "matchT_MT c1 d1" and matchT_MT2: "matchT_MT c2 d2"
   using WbisT_matchC_MC WbisT_matchT_MT by auto
   have "(Par c1 c2, Par d1 d2) \<in> WretrT (thetaParWT Un WbisT)"
   unfolding WretrT_def proof (clarify, intro conjI)
     show "matchC_MC (thetaParWT \<union> WbisT) (Par c1 c2) (Par d1 d2)"
     unfolding matchC_MC_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s'
       assume st: "s \<approx> t" assume "(Par c1 c2, s) \<rightarrow>c (c', s')"
       thus "\<exists>d' t'. (Par d1 d2, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> 
                     (c', d') \<in> thetaParWT \<union> WbisT"
       apply - proof(erule Par_transC_invert)
         fix c1' assume c1s: "(c1, s) \<rightarrow>c (c1', s')" and c': "c' = Par c1' c2"
         hence "\<exists>d' t'. (d1, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> c1' \<approx>wT d'"
         using st matchC_MC1 unfolding matchC_MC_def by blast
         thus ?thesis unfolding c' thetaParWT_def
         apply simp by (metis PL.ParCL_MtransC c2d2) 
       next      
         assume "(c1, s) \<rightarrow>t s'" and c': "c' = c2"
         hence "\<exists>t'. (d1, t) \<rightarrow>*t t' \<and> s' \<approx> t'"
         using st matchT_MT1 unfolding matchT_MT_def by blast
         thus ?thesis 
         unfolding c' thetaParWT_def
         apply simp by (metis PL.ParTL_MtransC c2d2)
       next
         fix c2' assume "(c2, s) \<rightarrow>c (c2', s')" and c': "c' = Par c1 c2'"
         hence "\<exists>d' t'. (d2, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> c2' \<approx>wT d'"
         using st matchC_MC2 unfolding matchC_MC_def by blast
         thus ?thesis 
         unfolding c' thetaParWT_def
         apply simp by (metis PL.ParCR_MtransC c1d1)
       next
         assume "(c2, s) \<rightarrow>t s'" and c': "c' = c1"
         hence "\<exists>t'. (d2, t) \<rightarrow>*t t' \<and> s' \<approx> t'"
         using st matchT_MT2 unfolding matchT_MT_def by blast
         thus ?thesis 
         unfolding c' thetaParWT_def
         apply simp by (metis PL.ParTR_MtransC c1d1)
       qed
     qed 
   qed (unfold matchT_MT_def, auto)
  }
  thus ?thesis unfolding thetaParWT_def by auto
qed

lemma thetaParWT_WbisT:
"thetaParWT \<subseteq> WbisT"
apply(rule WbisT_coind)
using thetaParWT_sym thetaParWT_WretrT by auto

theorem Par_WbisT[simp]:
assumes "c1 \<approx>wT d1" and "c2 \<approx>wT d2"
shows "Par c1 c2 \<approx>wT Par d1 d2"
using assms thetaParWT_WbisT unfolding thetaParWT_def by blast


subsubsection\<open>T-bisimilarity versus language constructs\<close>

text\<open>T-Discreetness:\<close>

definition thetaFDW0 where 
"thetaFDW0 \<equiv> 
 {(c1,c2). discr0 c1 \<and> discr0 c2}"

lemma thetaFDW0_sym:
"sym thetaFDW0"
unfolding thetaFDW0_def sym_def using Sbis_Sym by blast

lemma thetaFDW0_RetrT:
"thetaFDW0 \<subseteq> RetrT thetaFDW0"
proof-
  {fix c d 
   assume c: "discr0 c" and d: "discr0 d"
   have "(c,d) \<in> RetrT thetaFDW0"
   unfolding RetrT_def proof (clarify, intro conjI)
     show "matchC_TMC thetaFDW0 c d"
     unfolding matchC_TMC_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s' assume "mustT c s" "mustT d t" 
       "s \<approx> t" and "(c, s) \<rightarrow>c (c', s')"
       thus "\<exists>d' t'. (d, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> (c', d') \<in> thetaFDW0"
       unfolding thetaFDW0_def apply simp
       by (metis MtransC_Refl noWhile_transC c d discr0_transC discr0_transC_indis 
                 indis_sym indis_trans) 
     qed
   next
     show "matchT_TMT c d"
     unfolding matchT_TMT_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t s' assume mt: "mustT c s" "mustT d t"  
       and st: "s \<approx> t" and cs: "(c, s) \<rightarrow>t s'"
       obtain t' where dt: "(d, t) \<rightarrow>*t t'" by (metis mt mustT_MtransT)
       hence "t \<approx> t'" and "s \<approx> s'" using mt cs c d discr0_transT discr0_MtransT by blast+
       hence "s' \<approx> t'" using st indis_trans indis_sym by blast
       thus "\<exists>t'. (d, t) \<rightarrow>*t t' \<and> s' \<approx> t'" using dt by blast     
     qed
   qed
  }
  thus ?thesis unfolding thetaFDW0_def by blast
qed

lemma thetaFDW0_BisT:
"thetaFDW0 \<subseteq> BisT"
apply(rule BisT_raw_coind)
using thetaFDW0_sym thetaFDW0_RetrT by auto

theorem discr0_BisT[simp]:
assumes "discr0 c1" and "discr0 c2"
shows "c1 \<approx>T c2"
using assms thetaFDW0_BisT unfolding thetaFDW0_def by blast   

text \<open>Atomic commands:\<close>

theorem Atm_BisT:
assumes "compatAtm atm" 
shows "Atm atm \<approx>T Atm atm"
by (metis assms siso0_Atm siso0_Sbis)

text\<open>Sequential composition:\<close> 

definition thetaSeqTT where 
"thetaSeqTT \<equiv> 
 {(c1 ;; c2, d1 ;; d2) | c1 c2 d1 d2. c1 \<approx>T d1 \<and> c2 \<approx>T d2}"

lemma thetaSeqTT_sym:
"sym thetaSeqTT"
unfolding thetaSeqTT_def sym_def using BisT_Sym by blast

lemma thetaSeqTT_RetrT:
"thetaSeqTT \<subseteq> RetrT (thetaSeqTT \<union> BisT)"
proof- 
  {fix c1 c2 d1 d2
   assume c1d1: "c1 \<approx>T d1" and c2d2: "c2 \<approx>T d2"
   hence matchC_TMC1: "matchC_TMC BisT c1 d1" and matchC_TMC2: "matchC_TMC BisT c2 d2"
     and matchT_TMT1: "matchT_TMT c1 d1" and matchT_T2: "matchT_TMT c2 d2"
   using BisT_matchC_TMC BisT_matchT_TMT by auto
   have "(c1 ;; c2, d1 ;; d2) \<in> RetrT (thetaSeqTT \<union> BisT)"
   unfolding RetrT_def proof (clarify, intro conjI)
     show "matchC_TMC (thetaSeqTT \<union> BisT) (c1 ;; c2) (d1 ;; d2)"
     unfolding matchC_TMC_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s'
       assume mt: "mustT (c1 ;; c2) s" "mustT (d1 ;; d2) t"
       and st: "s \<approx> t" 
       hence mt1: "mustT c1 s" "mustT d1 t"
       by (metis mustT_Seq_L mustT_Seq_R)+
       assume 0: "(c1 ;; c2, s) \<rightarrow>c (c', s')"
       thus "(\<exists>d' t'. (d1 ;; d2, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> 
                      (c', d') \<in> thetaSeqTT \<union> BisT)"
       proof(elim Seq_transC_invert)
         fix c1' assume c1s: "(c1, s) \<rightarrow>c (c1', s')" and c': "c' = c1' ;; c2"
         hence "\<exists>d1' t'. (d1, t) \<rightarrow>*c (d1', t') \<and> s' \<approx> t' \<and> c1' \<approx>T d1'"
         using mt1 st matchC_TMC1 unfolding matchC_TMC_def by blast
         thus ?thesis unfolding c' thetaSeqTT_def
         apply simp by (metis Seq_MtransC c2d2) 
       next      
         assume c1: "(c1, s) \<rightarrow>t s'" and c': "c' = c2"
         then obtain t' where d1: "(d1, t) \<rightarrow>*t t'" and s't': "s' \<approx> t'"
         using mt1 st matchT_TMT1 unfolding matchT_TMT_def by blast
         hence mt1: "mustT c2 s'" "mustT d2 t'"
         apply (metis 0 c' mt mustT_transC)
         by (metis mustT_Seq_R d1 mt(2))
         thus ?thesis 
         unfolding c' thetaSeqTT_def
         apply - apply(tactic \<open>mauto_no_simp_tac @{context}\<close>)
         apply simp by (metis Seq_MtransT_MtransC c2d2 d1 s't') 
       qed
     qed 
   qed (unfold matchT_TMT_def, auto)
  }
  thus ?thesis unfolding thetaSeqTT_def by auto
qed

lemma thetaSeqTT_BisT:
"thetaSeqTT \<subseteq> BisT"
apply(rule BisT_coind)
using thetaSeqTT_sym thetaSeqTT_RetrT by auto

theorem Seq_BisT[simp]:
assumes "c1 \<approx>T d1" and "c2 \<approx>T d2"
shows "c1 ;; c2 \<approx>T d1 ;; d2"
using assms thetaSeqTT_BisT unfolding thetaSeqTT_def by blast 

text\<open>Conditional:\<close>

definition thetaIfTT where 
"thetaIfTT \<equiv> 
 {(If tst c1 c2, If tst d1 d2) | tst c1 c2 d1 d2. compatTst tst \<and> c1 \<approx>T d1 \<and> c2 \<approx>T d2}"

lemma thetaIfTT_sym:
"sym thetaIfTT"
unfolding thetaIfTT_def sym_def using BisT_Sym by blast

lemma thetaIfTT_RetrT:
"thetaIfTT \<subseteq> RetrT (thetaIfTT \<union> BisT)"
proof- 
  {fix tst c1 c2 d1 d2
   assume tst: "compatTst tst" and c1d1: "c1 \<approx>T d1" and c2d2: "c2 \<approx>T d2"
   hence matchC_TMC1: "matchC_TMC BisT c1 d1" and matchC_TMC2: "matchC_TMC BisT c2 d2"
     and matchT_TMT1: "matchT_TMT c1 d1" and matchT_TMT2: "matchT_TMT c2 d2"
   using BisT_matchC_TMC BisT_matchT_TMT by auto
   have "(If tst c1 c2, If tst d1 d2) \<in> RetrT (thetaIfTT \<union> BisT)"
   unfolding RetrT_def proof (clarify, intro conjI)
     show "matchC_TMC (thetaIfTT \<union> BisT) (If tst c1 c2) (If tst d1 d2)"
     unfolding matchC_TMC_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s'
       assume st: "s \<approx> t" assume "(If tst c1 c2, s) \<rightarrow>c (c', s')"
       thus "\<exists>d' t'. (If tst d1 d2, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> 
                     (c', d') \<in> thetaIfTT \<union> BisT"
       apply - apply(erule If_transC_invert)
       unfolding thetaIfTT_def 
       apply simp apply (metis IfTrue c1d1 compatTst_def st transC_MtransC tst) 
       apply simp by (metis IfFalse c2d2 compatTst_def st transC_MtransC tst) 
     qed
   qed (unfold matchT_TMT_def, auto)
  }
  thus ?thesis unfolding thetaIfTT_def by auto
qed

lemma thetaIfTT_BisT:
"thetaIfTT \<subseteq> BisT"
apply(rule BisT_coind)
using thetaIfTT_sym thetaIfTT_RetrT by auto

theorem If_BisT[simp]:
assumes "compatTst tst" and "c1 \<approx>T d1" and "c2 \<approx>T d2"
shows "If tst c1 c2 \<approx>T If tst d1 d2"
using assms thetaIfTT_BisT unfolding thetaIfTT_def by blast

text\<open>While loop:\<close>

definition thetaWhileW0 where 
"thetaWhileW0 \<equiv> 
 {(While tst c, While tst d) | tst c d. compatTst tst \<and> c \<approx>T d} \<union> 
 {(c1 ;; (While tst c), d1 ;; (While tst d)) | tst c1 d1 c d. 
               compatTst tst \<and> c1 \<approx>T d1 \<and> c \<approx>T d}"

lemma thetaWhileW0_sym:
"sym thetaWhileW0"
unfolding thetaWhileW0_def sym_def using BisT_Sym by blast

lemma thetaWhileW0_RetrT:
"thetaWhileW0 \<subseteq> RetrT (thetaWhileW0 \<union> BisT)"
proof-
  {fix tst c d 
   assume tst: "compatTst tst" and c_d: "c \<approx>T d"
   hence matchC_TMC: "matchC_TMC BisT c d" 
     and matchT_TMT: "matchT_TMT c d" 
   using BisT_matchC_TMC BisT_matchT_TMT by auto
   have "(While tst c, While tst d) \<in> RetrT (thetaWhileW0 \<union> BisT)"
   unfolding RetrT_def proof (clarify, intro conjI)
     show "matchC_TMC (thetaWhileW0 \<union> BisT) (While tst c) (While tst d)"
     unfolding matchC_TMC_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s'
       assume st: "s \<approx> t" assume "(While tst c, s) \<rightarrow>c (c', s')"
       thus "\<exists>d' t'. (While tst d, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> 
                     (c', d') \<in> thetaWhileW0 \<union> BisT"
       apply - apply(erule While_transC_invert)
       unfolding thetaWhileW0_def apply simp
       by (metis WhileTrue transC_MtransC c_d compatTst_def st tst)
     qed
   next
     show "matchT_TMT (While tst c) (While tst d)"
     unfolding matchT_TMT_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t s' assume st: "s \<approx> t" assume "(While tst c, s) \<rightarrow>t s'"
       thus "\<exists>t'. (While tst d, t) \<rightarrow>*t t' \<and> s' \<approx> t' "
       apply - apply(erule While_transT_invert)
       unfolding thetaWhileW0_def apply simp
       by (metis WhileFalse compatTst_def st transT_MtransT tst)       
     qed
   qed
  }
  moreover 
  {fix tst c1 d1  c d
   assume tst: "compatTst tst" and c1d1: "c1 \<approx>T d1" and c_d: "c \<approx>T d"
   hence matchC_TMC1: "matchC_TMC BisT c1 d1" and matchC_TMC: "matchC_TMC BisT c d" 
     and matchT_TMT1: "matchT_TMT c1 d1" and matchT_TMT: "matchT_TMT c d"
   using BisT_matchC_TMC BisT_matchT_TMT by auto
   have "(c1 ;; (While tst c), d1 ;; (While tst d)) \<in> RetrT (thetaWhileW0 \<union> BisT)"
   unfolding RetrT_def proof (clarify, intro conjI)
     show "matchC_TMC (thetaWhileW0 \<union> BisT) (c1 ;; (While tst c)) (d1 ;; (While tst d))"
     unfolding matchC_TMC_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s'
       assume mt: "mustT (c1 ;; While tst c) s" "mustT (d1 ;; While tst d) t"
       and st: "s \<approx> t" 
       hence mt1: "mustT c1 s" "mustT d1 t"
       by (metis mustT_Seq_L mustT_Seq_R)+     
       assume 0: "(c1 ;; (While tst c), s) \<rightarrow>c (c', s')"
       thus "\<exists>d' t'. (d1 ;; (While tst d), t) \<rightarrow>*c (d', t') \<and> 
                     s' \<approx> t' \<and> (c', d') \<in> thetaWhileW0 \<union> BisT"
       apply - proof(erule Seq_transC_invert)
         fix c1' assume "(c1, s) \<rightarrow>c (c1', s')" and c': "c' = c1' ;; (While tst c)"
         hence "\<exists>d' t'. (d1, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> c1' \<approx>T d'" 
         using mt1 st matchC_TMC1 unfolding matchC_TMC_def by blast
         thus ?thesis
         unfolding c' thetaWhileW0_def
         apply simp by (metis Seq_MtransC c_d tst)
       next
         assume "(c1, s) \<rightarrow>t s'" and c': "c' = While tst c"
         then obtain t' where "(d1, t) \<rightarrow>*t t' \<and> s' \<approx> t'"
         using mt1 st matchT_TMT1 unfolding matchT_TMT_def by metis
         thus ?thesis
         unfolding c' thetaWhileW0_def 
         apply simp by (metis Seq_MtransT_MtransC c_d tst)
       qed
     qed
   qed (unfold matchT_TMT_def, auto)
  }
  ultimately show ?thesis unfolding thetaWhileW0_def by auto
qed

lemma thetaWhileW0_BisT:
"thetaWhileW0 \<subseteq> BisT"
apply(rule BisT_coind)
using thetaWhileW0_sym thetaWhileW0_RetrT by auto

theorem While_BisT[simp]:
assumes "compatTst tst" and "c \<approx>T d"
shows "While tst c \<approx>T While tst d"
using assms thetaWhileW0_BisT unfolding thetaWhileW0_def by auto

text\<open>Parallel composition:\<close>

definition thetaParTT where 
"thetaParTT \<equiv> 
 {(Par c1 c2, Par d1 d2) | c1 c2 d1 d2. c1 \<approx>T d1 \<and> c2 \<approx>T d2}"

lemma thetaParTT_sym:
"sym thetaParTT"
unfolding thetaParTT_def sym_def using BisT_Sym by blast

lemma thetaParTT_RetrT:
"thetaParTT \<subseteq> RetrT (thetaParTT \<union> BisT)"
proof-
  {fix c1 c2 d1 d2
   assume c1d1: "c1 \<approx>T d1" and c2d2: "c2 \<approx>T d2"
   hence matchC_TMC1: "matchC_TMC BisT c1 d1" and matchC_TMC2: "matchC_TMC BisT c2 d2"
     and matchT_TMT1: "matchT_TMT c1 d1" and matchT_TMT2: "matchT_TMT c2 d2"
   using BisT_matchC_TMC BisT_matchT_TMT by auto
   have "(Par c1 c2, Par d1 d2) \<in> RetrT (thetaParTT \<union> BisT)"
   unfolding RetrT_def proof (clarify, intro conjI)
     show "matchC_TMC (thetaParTT \<union> BisT) (Par c1 c2) (Par d1 d2)"
     unfolding matchC_TMC_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s'
       assume "mustT (Par c1 c2) s" and "mustT (Par d1 d2) t"
       and st: "s \<approx> t" 
       hence mt: "mustT c1 s" "mustT c2 s"
                 "mustT d1 t" "mustT d2 t"
       by (metis mustT_Par_L mustT_Par_R)+        
       assume "(Par c1 c2, s) \<rightarrow>c (c', s')"
       thus "\<exists>d' t'. (Par d1 d2, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> 
                     (c', d') \<in> thetaParTT \<union> BisT"
       proof(elim Par_transC_invert)
         fix c1' assume c1s: "(c1, s) \<rightarrow>c (c1', s')" and c': "c' = Par c1' c2"
         hence "\<exists>d' t'. (d1, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> c1' \<approx>T d'"
         using mt st matchC_TMC1 unfolding matchC_TMC_def by blast
         thus ?thesis unfolding c' thetaParTT_def
         apply simp by (metis ParCL_MtransC c2d2) 
       next      
         assume "(c1, s) \<rightarrow>t s'" and c': "c' = c2"
         hence "\<exists>t'. (d1, t) \<rightarrow>*t t' \<and> s' \<approx> t'"
         using mt st matchT_TMT1 unfolding matchT_TMT_def by blast
         thus ?thesis 
         unfolding c' thetaParTT_def
         apply simp by (metis PL.ParTL_MtransC c2d2)
       next
         fix c2' assume "(c2, s) \<rightarrow>c (c2', s')" and c': "c' = Par c1 c2'"
         hence "\<exists>d' t'. (d2, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> c2' \<approx>T d'"
         using mt st matchC_TMC2 unfolding matchC_TMC_def by blast
         thus ?thesis 
         unfolding c' thetaParTT_def
         apply simp by (metis PL.ParCR_MtransC c1d1)
       next
         assume "(c2, s) \<rightarrow>t s'" and c': "c' = c1"
         hence "\<exists>t'. (d2, t) \<rightarrow>*t t' \<and> s' \<approx> t'"
         using mt st matchT_TMT2 unfolding matchT_TMT_def by blast
         thus ?thesis 
         unfolding c' thetaParTT_def
         apply simp by (metis PL.ParTR_MtransC c1d1)
       qed
     qed 
   qed (unfold matchT_TMT_def, auto)
  }
  thus ?thesis unfolding thetaParTT_def by auto
qed

lemma thetaParTT_BisT:
"thetaParTT \<subseteq> BisT"
apply(rule BisT_coind)
using thetaParTT_sym thetaParTT_RetrT by auto

theorem Par_BisT[simp]:
assumes "c1 \<approx>T d1" and "c2 \<approx>T d2"
shows "Par c1 c2 \<approx>T Par d1 d2"
using assms thetaParTT_BisT unfolding thetaParTT_def by blast


subsubsection\<open>W-bisimilarity versus language constructs\<close>

text \<open>Atomic commands:\<close>

theorem Atm_Wbis[simp]:
assumes "compatAtm atm" 
shows "Atm atm \<approx>w Atm atm"
by (metis Atm_Sbis assms bis_imp)

text\<open>Discreetness:\<close>

theorem discr_Wbis[simp]:
assumes *: "discr c" and **: "discr d"
shows "c \<approx>w d"
by (metis * ** bis_imp(4) discr_ZObis)

text\<open>Sequential composition:\<close>

definition thetaSeqW where 
"thetaSeqW \<equiv> 
 {(c1 ;; c2, d1 ;; d2) | c1 c2 d1 d2. c1 \<approx>wT d1 \<and> c2 \<approx>w d2}"

lemma thetaSeqW_sym:
"sym thetaSeqW"
unfolding thetaSeqW_def sym_def using WbisT_Sym Wbis_Sym by blast

lemma thetaSeqW_Wretr:
"thetaSeqW \<subseteq> Wretr (thetaSeqW \<union> Wbis)"
proof- 
  {fix c1 c2 d1 d2
   assume c1d1: "c1 \<approx>wT d1" and c2d2: "c2 \<approx>w d2"
   hence matchC_MC1: "matchC_MC WbisT c1 d1" and matchC_W2: "matchC_M Wbis c2 d2"
     and matchT_MT1: "matchT_MT c1 d1" and matchT_M2: "matchT_M c2 d2" 
   using WbisT_matchC_MC WbisT_matchT_MT Wbis_matchC_M Wbis_matchT_M by auto
   have "(c1 ;; c2, d1 ;; d2) \<in> Wretr (thetaSeqW \<union> Wbis)"
   unfolding Wretr_def proof (clarify, intro conjI)
     show "matchC_M (thetaSeqW \<union> Wbis) (c1 ;; c2) (d1 ;; d2)"
     unfolding matchC_M_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s'
       assume st: "s \<approx> t" assume "(c1 ;; c2, s) \<rightarrow>c (c', s')"
       thus 
       "(\<exists>d' t'. (d1 ;; d2, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> (c', d') \<in> thetaSeqW \<union> Wbis) \<or> 
        (\<exists>t'. (d1 ;; d2, t) \<rightarrow>*t t' \<and> s' \<approx> t' \<and> discr c')"
       apply - proof(erule Seq_transC_invert)
         fix c1' assume c1s: "(c1, s) \<rightarrow>c (c1', s')" and c': "c' = c1' ;; c2"
         hence "\<exists>d1' t'. (d1, t) \<rightarrow>*c (d1', t') \<and> s' \<approx> t' \<and> c1' \<approx>wT d1'"
         using st matchC_MC1 unfolding matchC_MC_def by blast
         thus ?thesis unfolding c' thetaSeqW_def
         apply simp by (metis PL.Seq_MtransC c2d2)
       next      
         assume "(c1, s) \<rightarrow>t s'" and c': "c' = c2"
         hence "\<exists>t'. (d1, t) \<rightarrow>*t t' \<and> s' \<approx> t'"
         using st matchT_MT1 unfolding matchT_MT_def by auto
         thus ?thesis 
         unfolding c' thetaSeqW_def
         apply simp by (metis PL.Seq_MtransT_MtransC c2d2) 
       qed
     qed 
   qed (unfold matchT_M_def, auto)
  }
  thus ?thesis unfolding thetaSeqW_def by auto
qed

lemma thetaSeqW_Wbis:
"thetaSeqW \<subseteq> Wbis"
apply(rule Wbis_coind)
using thetaSeqW_sym thetaSeqW_Wretr by auto

theorem Seq_WbisT_Wbis[simp]:
assumes "c1 \<approx>wT d1" and "c2 \<approx>w d2"
shows "c1 ;; c2 \<approx>w d1 ;; d2"
using assms thetaSeqW_Wbis unfolding thetaSeqW_def by blast

theorem Seq_siso_Wbis[simp]:
assumes "siso e" and "c2 \<approx>w d2"
shows "e ;; c2 \<approx>w e ;; d2"
using assms by auto

(*  *)

definition thetaSeqWD where 
"thetaSeqWD \<equiv> 
 {(c1 ;; c2, d1 ;; d2) | c1 c2 d1 d2. c1 \<approx>w d1 \<and> discr c2 \<and> discr d2}"

lemma thetaSeqWD_sym:
"sym thetaSeqWD"
unfolding thetaSeqWD_def sym_def using Wbis_Sym by blast

lemma thetaSeqWD_Wretr:
"thetaSeqWD \<subseteq> Wretr (thetaSeqWD \<union> Wbis)"
proof-
  {fix c1 c2 d1 d2
   assume c1d1: "c1 \<approx>w d1" and c2: "discr c2" and d2: "discr d2"
   hence matchC_M: "matchC_M Wbis c1 d1" 
     and matchT_M: "matchT_M c1 d1"
   using Wbis_matchC_M Wbis_matchT_M by auto
   have "(c1 ;; c2, d1 ;; d2) \<in> Wretr (thetaSeqWD \<union> Wbis)"
   unfolding Wretr_def proof (clarify, intro conjI)
     show "matchC_M (thetaSeqWD \<union> Wbis) (c1 ;; c2) (d1 ;; d2)"
     unfolding matchC_M_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s'
       assume st: "s \<approx> t" assume "(c1 ;; c2, s) \<rightarrow>c (c', s')"
       thus 
       "(\<exists>d' t'. (d1 ;; d2, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> (c', d') \<in> thetaSeqWD \<union> Wbis) \<or> 
        (\<exists>t'. (d1 ;; d2, t) \<rightarrow>*t t' \<and> s' \<approx> t' \<and> discr c')"
       apply - proof(erule Seq_transC_invert)
         fix c1' assume c1s: "(c1, s) \<rightarrow>c (c1', s')" and c': "c' = c1' ;; c2"
         hence
         "(\<exists>d' t'. (d1, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> c1' \<approx>w d') \<or> 
          (\<exists>t'. (d1, t) \<rightarrow>*t t' \<and> s' \<approx> t' \<and> discr c1')"
         using st matchC_M unfolding matchC_M_def by blast
         thus ?thesis unfolding c' thetaSeqWD_def
         apply - apply(tactic \<open>mauto_no_simp_tac @{context}\<close>)
         apply simp apply (metis PL.Seq_MtransC c2 d2)
         apply simp by (metis PL.Seq_MtransT_MtransC c2 d2 discr_Seq discr_Wbis)
       next      
         assume "(c1, s) \<rightarrow>t s'" and c': "c' = c2"
         hence 
         "(\<exists>d' t'. (d1, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> discr d') \<or> 
          (\<exists>t'. (d1, t) \<rightarrow>*t t' \<and> s' \<approx> t')"
         using st matchT_M unfolding matchT_M_def by blast
         thus ?thesis 
         unfolding c' thetaSeqWD_def
         apply - apply(tactic \<open>mauto_no_simp_tac @{context}\<close>)
         apply simp apply (metis PL.Seq_MtransC c2 d2 discr_Seq discr_Wbis)
         apply simp by (metis PL.Seq_MtransT_MtransC c2 d2 discr_Wbis)
       qed
     qed 
   qed (unfold matchT_M_def, auto)
  }
  thus ?thesis unfolding thetaSeqWD_def by auto
qed

lemma thetaSeqWD_Wbis:
"thetaSeqWD \<subseteq> Wbis"
apply(rule Wbis_coind)
using thetaSeqWD_sym thetaSeqWD_Wretr by auto

theorem Seq_Wbis_discr[simp]:
assumes "c1 \<approx>w d1" and "discr c2" and "discr d2"
shows "c1 ;; c2 \<approx>w d1 ;; d2"
using assms thetaSeqWD_Wbis unfolding thetaSeqWD_def by blast

text\<open>Conditional:\<close>

definition thetaIfW where 
"thetaIfW \<equiv> 
 {(If tst c1 c2, If tst d1 d2) | tst c1 c2 d1 d2. compatTst tst \<and> c1 \<approx>w d1 \<and> c2 \<approx>w d2}"

lemma thetaIfW_sym:
"sym thetaIfW"
unfolding thetaIfW_def sym_def using Wbis_Sym by blast

lemma thetaIfW_Wretr:
"thetaIfW \<subseteq> Wretr (thetaIfW \<union> Wbis)"
proof-
  {fix tst c1 c2 d1 d2
   assume tst: "compatTst tst" and c1d1: "c1 \<approx>w d1" and c2d2: "c2 \<approx>w d2"
   hence matchC_M1: "matchC_M Wbis c1 d1" and matchC_M2: "matchC_M Wbis c2 d2"
     and matchT_M1: "matchT_M c1 d1" and matchT_M2: "matchT_M c2 d2"
   using Wbis_matchC_M Wbis_matchT_M by auto
   have "(If tst c1 c2, If tst d1 d2) \<in> Wretr (thetaIfW \<union> Wbis)"
   unfolding Wretr_def proof (clarify, intro conjI)
     show "matchC_M (thetaIfW \<union> Wbis) (If tst c1 c2) (If tst d1 d2)"
     unfolding matchC_M_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s'
       assume st: "s \<approx> t" assume "(If tst c1 c2, s) \<rightarrow>c (c', s')"
       thus 
       "(\<exists>d' t'. (If tst d1 d2, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> (c', d') \<in> thetaIfW \<union> Wbis) \<or> 
        (\<exists>t'. (If tst d1 d2, t) \<rightarrow>*t t' \<and> s' \<approx> t' \<and> discr c')"
       apply - apply(erule If_transC_invert)
       unfolding thetaIfW_def 
       apply simp apply (metis IfTrue c1d1 compatTst_def st transC_MtransC tst)
       apply simp by (metis IfFalse c2d2 compatTst_def st transC_MtransC tst)
     qed
   qed (unfold matchT_M_def, auto)
  }
  thus ?thesis unfolding thetaIfW_def by auto
qed

lemma thetaIfW_Wbis:
"thetaIfW \<subseteq> Wbis"
apply(rule Wbis_coind)
using thetaIfW_sym thetaIfW_Wretr by auto

theorem If_Wbis[simp]:
assumes "compatTst tst" and "c1 \<approx>w d1" and "c2 \<approx>w d2"
shows "If tst c1 c2 \<approx>w If tst d1 d2"
using assms thetaIfW_Wbis unfolding thetaIfW_def by blast

text\<open>While loop:\<close>

text\<open>Again, w-bisimilarity does not interact with / preserve the While construct in 
any interesting way.\<close>

text\<open>Parallel composition:\<close>

definition thetaParWL1 where 
"thetaParWL1 \<equiv> 
 {(Par c1 c2, d) | c1 c2 d. c1 \<approx>w d \<and> discr c2}"

lemma thetaParWL1_Wretr:
"thetaParWL1 \<subseteq> Wretr (thetaParWL1 \<union> Wbis)"
proof-
  {fix c1 c2 d
   assume c1d: "c1 \<approx>w d" and c2: "discr c2"
   hence matchC_M: "matchC_M Wbis c1 d" 
     and matchT_M: "matchT_M c1 d" 
   using Wbis_matchC_M Wbis_matchT_M by auto
   have "(Par c1 c2, d) \<in> Wretr (thetaParWL1 \<union> Wbis)"
   unfolding Wretr_def proof (clarify, intro conjI)
     show "matchC_M (thetaParWL1 \<union> Wbis) (Par c1 c2) d"
     unfolding matchC_M_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s'
       assume st: "s \<approx> t" assume "(Par c1 c2, s) \<rightarrow>c (c', s')"
       thus
       "(\<exists>d' t'. (d, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> (c', d') \<in> thetaParWL1 \<union> Wbis) \<or>
        (\<exists>t'. (d, t) \<rightarrow>*t t' \<and> s' \<approx> t' \<and> discr c')"
       apply - proof(erule Par_transC_invert)
         fix c1' assume "(c1, s) \<rightarrow>c (c1', s')" and c': "c' = Par c1' c2"
         hence 
         "(\<exists>d' t'. (d, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> c1' \<approx>w d') \<or> 
          (\<exists>t'. (d, t) \<rightarrow>*t t' \<and> s' \<approx> t' \<and> discr c1')"
         using st matchC_M unfolding matchC_M_def by blast
         thus ?thesis unfolding thetaParWL1_def
         apply - apply(elim disjE exE conjE) 
         apply simp apply (metis c2 c')
         apply simp by (metis c' c2 discr_Par) 
       next
         assume "(c1, s) \<rightarrow>t s'" and c': "c' = c2"
         hence 
         "(\<exists>d' t'. (d, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> discr d') \<or> 
          (\<exists>t'. (d, t) \<rightarrow>*t t' \<and> s' \<approx> t')"
         using st matchT_M unfolding matchT_M_def by blast
         thus ?thesis unfolding thetaParWL1_def
         apply - apply(elim disjE exE conjE)
         apply simp apply (metis c' c2 discr_Wbis)
         apply simp by (metis c' c2)  
       next
         fix c2' assume c2s: "(c2, s) \<rightarrow>c (c2', s')" and c': "c' = Par c1 c2'"
         hence "s \<approx> s'" using c2 discr_transC_indis by blast
         hence s't: "s' \<approx> t" using st indis_sym indis_trans by blast
         have "discr c2'" using c2 c2s discr_transC by blast
         thus ?thesis using s't c1d unfolding thetaParWL1_def c' by auto
       next
         assume "(c2, s) \<rightarrow>t s'" and c': "c' = c1"
         hence "s \<approx> s'" using c2 discr_transT by blast
         hence s't: "s' \<approx> t" using st indis_sym indis_trans by blast
         thus ?thesis using c1d unfolding thetaParWL1_def c' by auto
       qed
     qed
   qed (unfold matchT_M_def, auto)
  }
  thus ?thesis unfolding thetaParWL1_def by blast
qed

lemma thetaParWL1_converse_Wretr:
"thetaParWL1 ^-1 \<subseteq> Wretr (thetaParWL1 ^-1 \<union> Wbis)"
proof-
  {fix c1 c2 d
   assume c1d: "c1 \<approx>w d" and c2: "discr c2"
   hence matchC_M: "matchC_M Wbis d c1" 
     and matchT_M: "matchT_M d c1" 
   using Wbis_matchC_M_rev Wbis_matchT_M_rev by auto
   have "(d, Par c1 c2) \<in> Wretr (thetaParWL1\<inverse> \<union> Wbis)"
   unfolding Wretr_def proof (clarify, intro conjI)
     show "matchC_M (thetaParWL1\<inverse> \<union> Wbis) d (Par c1 c2)"
     unfolding matchC_M_def2 Wbis_converse proof (tactic \<open>mauto_no_simp_tac @{context}\<close>) 
       fix s t d' t'
       assume "s \<approx> t" and "(d, t) \<rightarrow>c (d', t')"
       hence 
       "(\<exists>c' s'. (c1, s) \<rightarrow>*c (c', s') \<and> s' \<approx> t' \<and> d' \<approx>w c') \<or> 
        (\<exists>s'. (c1, s) \<rightarrow>*t s' \<and> s' \<approx> t' \<and> discr d')"
       using matchC_M unfolding matchC_M_def2 by blast
       thus
       "(\<exists>c' s'. (Par c1 c2, s) \<rightarrow>*c (c', s') \<and> s' \<approx> t' \<and> (c', d') \<in> thetaParWL1 \<union> Wbis) \<or>
        (\<exists>s'. (Par c1 c2, s) \<rightarrow>*t s' \<and> s' \<approx> t' \<and> discr d')"
       unfolding thetaParWL1_def 
       apply - apply(tactic \<open>mauto_no_simp_tac @{context}\<close>)
       apply simp apply (metis PL.ParCL_MtransC Wbis_Sym c2)
       apply simp by (metis PL.ParTL_MtransC c2 discr_Wbis)
     qed
   next
     show "matchT_M d (Par c1 c2)"
     unfolding matchT_M_def2 Wbis_converse proof (tactic \<open>mauto_no_simp_tac @{context}\<close>) 
       fix s t t'
       assume "s \<approx> t" and "(d, t) \<rightarrow>t t'"
       hence 
       "(\<exists>c' s'. (c1, s) \<rightarrow>*c (c', s') \<and> s' \<approx> t' \<and> discr c') \<or> 
        (\<exists>s'. (c1, s) \<rightarrow>*t s' \<and> s' \<approx> t')"
       using matchT_M unfolding matchT_M_def2 by blast
       thus
       "(\<exists>c' s'. (Par c1 c2, s) \<rightarrow>*c (c', s') \<and> s' \<approx> t' \<and> discr c') \<or> 
        (\<exists>s'. (Par c1 c2, s) \<rightarrow>*t s' \<and> s' \<approx> t')"
       apply - apply(tactic \<open>mauto_no_simp_tac @{context}\<close>)
       apply (metis PL.ParCL_MtransC c2 discr_Par)
       by (metis PL.ParTL_MtransC c2)  
     qed
   qed
  }
  thus ?thesis unfolding thetaParWL1_def by blast
qed

lemma thetaParWL1_Wbis:
"thetaParWL1 \<subseteq> Wbis"
apply(rule Wbis_coind2)
using thetaParWL1_Wretr thetaParWL1_converse_Wretr by auto

theorem Par_Wbis_discrL1[simp]:
assumes "c1 \<approx>w d" and "discr c2"
shows "Par c1 c2 \<approx>w d"
using assms thetaParWL1_Wbis unfolding thetaParWL1_def by blast

theorem Par_Wbis_discrR1[simp]:
assumes "c \<approx>w d1" and "discr d2"
shows "c \<approx>w Par d1 d2"
using assms Par_Wbis_discrL1 Wbis_Sym by blast

(*  *)

definition thetaParWL2 where 
"thetaParWL2 \<equiv> 
 {(Par c1 c2, d) | c1 c2 d. discr c1 \<and> c2 \<approx>w d}"

lemma thetaParWL2_Wretr:
"thetaParWL2 \<subseteq> Wretr (thetaParWL2 \<union> Wbis)"
proof-
  {fix c1 c2 d
   assume c2d: "c2 \<approx>w d" and c1: "discr c1" 
   hence matchC_M: "matchC_M Wbis c2 d" 
     and matchT_M: "matchT_M c2 d" 
   using Wbis_matchC_M Wbis_matchT_M by auto
   have "(Par c1 c2, d) \<in> Wretr (thetaParWL2 \<union> Wbis)"
   unfolding Wretr_def proof (clarify, intro conjI)
     show "matchC_M (thetaParWL2 \<union> Wbis) (Par c1 c2) d"
     unfolding matchC_M_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s'
       assume st: "s \<approx> t" assume "(Par c1 c2, s) \<rightarrow>c (c', s')"
       thus
       "(\<exists>d' t'. (d, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> (c', d') \<in> thetaParWL2 \<union> Wbis) \<or>
        (\<exists>t'. (d, t) \<rightarrow>*t t' \<and> s' \<approx> t' \<and> discr c')"
       apply - proof(erule Par_transC_invert)
         fix c1' assume c1s: "(c1, s) \<rightarrow>c (c1', s')" and c': "c' = Par c1' c2"
         hence "s \<approx> s'" using c1 discr_transC_indis by blast
         hence s't: "s' \<approx> t" using st indis_sym indis_trans by blast
         have "discr c1'" using c1 c1s discr_transC by blast
         thus ?thesis using s't c2d unfolding thetaParWL2_def c' by auto
       next
         assume "(c1, s) \<rightarrow>t s'" and c': "c' = c2"
         hence "s \<approx> s'" using c1 discr_transT by blast
         hence s't: "s' \<approx> t" using st indis_sym indis_trans by blast
         thus ?thesis using c2d unfolding thetaParWL2_def c' by auto
       next
         fix c2' assume "(c2, s) \<rightarrow>c (c2', s')" and c': "c' = Par c1 c2'"
         hence 
         "(\<exists>d' t'. (d, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> c2' \<approx>w d') \<or> 
          (\<exists>t'. (d, t) \<rightarrow>*t t' \<and> s' \<approx> t' \<and> discr c2')"
         using st matchC_M unfolding matchC_M_def by blast
         thus ?thesis unfolding thetaParWL2_def
         apply - apply(elim disjE exE conjE) 
         apply simp apply (metis c1 c')
         apply simp by (metis c' c1 discr_Par) 
       next
         assume "(c2, s) \<rightarrow>t s'" and c': "c' = c1"
         hence 
         "(\<exists>d' t'. (d, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> discr d') \<or> 
          (\<exists>t'. (d, t) \<rightarrow>*t t' \<and> s' \<approx> t')"
         using st matchT_M unfolding matchT_M_def by blast
         thus ?thesis unfolding thetaParWL2_def
         apply - apply(elim disjE exE conjE)
         apply simp apply (metis c' c1 discr_Wbis)
         apply simp by (metis c' c1)          
       qed
     qed
   qed (unfold matchT_M_def, auto)
  }
  thus ?thesis unfolding thetaParWL2_def by blast
qed

lemma thetaParWL2_converse_Wretr:
"thetaParWL2 ^-1 \<subseteq> Wretr (thetaParWL2 ^-1 \<union> Wbis)"
proof-
  {fix c1 c2 d
   assume c2d: "c2 \<approx>w d" and c1: "discr c1"
   hence matchC_M: "matchC_M Wbis d c2" 
     and matchT_M: "matchT_M d c2" 
   using Wbis_matchC_M_rev Wbis_matchT_M_rev by auto
   have "(d, Par c1 c2) \<in> Wretr (thetaParWL2\<inverse> \<union> Wbis)"
   unfolding Wretr_def proof (clarify, intro conjI)
     show "matchC_M (thetaParWL2\<inverse> \<union> Wbis) d (Par c1 c2)"
     unfolding matchC_M_def2 Wbis_converse proof (tactic \<open>mauto_no_simp_tac @{context}\<close>) 
       fix s t d' t'
       assume "s \<approx> t" and "(d, t) \<rightarrow>c (d', t')"
       hence 
       "(\<exists>c' s'. (c2, s) \<rightarrow>*c (c', s') \<and> s' \<approx> t' \<and> d' \<approx>w c') \<or> 
        (\<exists>s'. (c2, s) \<rightarrow>*t s' \<and> s' \<approx> t' \<and> discr d')"
       using matchC_M unfolding matchC_M_def2 by blast
       thus
       "(\<exists>c' s'. (Par c1 c2, s) \<rightarrow>*c (c', s') \<and> s' \<approx> t' \<and> (c', d') \<in> thetaParWL2 \<union> Wbis) \<or>
        (\<exists>s'. (Par c1 c2, s) \<rightarrow>*t s' \<and> s' \<approx> t' \<and> discr d')"
       unfolding thetaParWL2_def 
       apply - apply(tactic \<open>mauto_no_simp_tac @{context}\<close>)
       apply simp apply (metis PL.ParCR_MtransC Wbis_Sym c1)
       apply simp by (metis PL.ParTR_MtransC c1 discr_Wbis) 
     qed
   next
     show "matchT_M d (Par c1 c2)"
     unfolding matchT_M_def2 Wbis_converse proof (tactic \<open>mauto_no_simp_tac @{context}\<close>) 
       fix s t t'
       assume "s \<approx> t" and "(d, t) \<rightarrow>t t'"
       hence 
       "(\<exists>c' s'. (c2, s) \<rightarrow>*c (c', s') \<and> s' \<approx> t' \<and> discr c') \<or> 
        (\<exists>s'. (c2, s) \<rightarrow>*t s' \<and> s' \<approx> t')"
       using matchT_M unfolding matchT_M_def2 by blast
       thus
       "(\<exists>c' s'. (Par c1 c2, s) \<rightarrow>*c (c', s') \<and> s' \<approx> t' \<and> discr c') \<or> 
        (\<exists>s'. (Par c1 c2, s) \<rightarrow>*t s' \<and> s' \<approx> t')"
       apply - apply(tactic \<open>mauto_no_simp_tac @{context}\<close>)
       apply (metis PL.ParCR_MtransC c1 discr_Par)
       by (metis PL.ParTR_MtransC c1)
     qed
   qed
  }
  thus ?thesis unfolding thetaParWL2_def by blast
qed

lemma thetaParWL2_Wbis:
"thetaParWL2 \<subseteq> Wbis"
apply(rule Wbis_coind2)
using thetaParWL2_Wretr thetaParWL2_converse_Wretr by auto

theorem Par_Wbis_discrL2[simp]:
assumes "c2 \<approx>w d" and "discr c1"
shows "Par c1 c2 \<approx>w d"
using assms thetaParWL2_Wbis unfolding thetaParWL2_def by blast

theorem Par_Wbis_discrR2[simp]:
assumes "c \<approx>w d2" and "discr d1"
shows "c \<approx>w Par d1 d2"
using assms Par_Wbis_discrL2 Wbis_Sym by blast

(*  *)

definition thetaParW where 
"thetaParW \<equiv> 
 {(Par c1 c2, Par d1 d2) | c1 c2 d1 d2. c1 \<approx>w d1 \<and> c2 \<approx>w d2}"

lemma thetaParW_sym:
"sym thetaParW"
unfolding thetaParW_def sym_def using Wbis_Sym by blast

lemma thetaParW_Wretr:
"thetaParW \<subseteq> Wretr (thetaParW \<union> Wbis)"
proof-
  {fix c1 c2 d1 d2
   assume c1d1: "c1 \<approx>w d1" and c2d2: "c2 \<approx>w d2"
   hence matchC_M1: "matchC_M Wbis c1 d1" and matchC_M2: "matchC_M Wbis c2 d2"
     and matchT_M1: "matchT_M c1 d1" and matchT_M2: "matchT_M c2 d2"
   using Wbis_matchC_M Wbis_matchT_M by auto
   have "(Par c1 c2, Par d1 d2) \<in> Wretr (thetaParW \<union> Wbis)"
   unfolding Wretr_def proof (clarify, intro conjI)
     show "matchC_M (thetaParW \<union> Wbis) (Par c1 c2) (Par d1 d2)"
     unfolding matchC_M_def proof (tactic \<open>mauto_no_simp_tac @{context}\<close>)
       fix s t c' s'
       assume st: "s \<approx> t" assume "(Par c1 c2, s) \<rightarrow>c (c', s')"
       thus 
       "(\<exists>d' t'. (Par d1 d2, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> (c', d') \<in> thetaParW \<union> Wbis) \<or> 
        (\<exists>t'. (Par d1 d2, t) \<rightarrow>*t t' \<and> s' \<approx> t' \<and> discr c')"
       apply - proof(erule Par_transC_invert)
         fix c1' assume c1s: "(c1, s) \<rightarrow>c (c1', s')" and c': "c' = Par c1' c2"
         hence
         "(\<exists>d' t'. (d1, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> c1' \<approx>w d') \<or> 
          (\<exists>t'. (d1, t) \<rightarrow>*t t' \<and> s' \<approx> t' \<and> discr c1')"
         using st matchC_M1 unfolding matchC_M_def by blast
         thus ?thesis unfolding c' thetaParW_def
         apply - apply(tactic \<open>mauto_no_simp_tac @{context}\<close>)
         apply simp apply (metis PL.ParCL_MtransC c2d2) 
         apply simp by (metis PL.ParTL_MtransC Par_Wbis_discrL2 c2d2)
       next      
         assume "(c1, s) \<rightarrow>t s'" and c': "c' = c2"
         hence 
         "(\<exists>d' t'. (d1, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> discr d') \<or> 
          (\<exists>t'. (d1, t) \<rightarrow>*t t' \<and> s' \<approx> t')"
         using st matchT_M1 unfolding matchT_M_def by blast
         thus ?thesis 
         unfolding c' thetaParW_def
         apply - apply(tactic \<open>mauto_no_simp_tac @{context}\<close>)
         apply simp apply (metis PL.ParCL_MtransC Par_Wbis_discrR2 c2d2)
         apply simp by (metis PL.ParTL_MtransC c2d2) 
       next
         fix c2' assume "(c2, s) \<rightarrow>c (c2', s')" and c': "c' = Par c1 c2'"
         hence 
         "(\<exists>d' t'. (d2, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> c2' \<approx>w d') \<or> 
          (\<exists>t'. (d2, t) \<rightarrow>*t t' \<and> s' \<approx> t' \<and> discr c2')"
         using st matchC_M2 unfolding matchC_M_def by blast
         thus ?thesis 
         unfolding c' thetaParW_def
         apply - apply(tactic \<open>mauto_no_simp_tac @{context}\<close>)
         apply simp apply (metis PL.ParCR_MtransC c1d1)
         apply simp by (metis PL.ParTR_MtransC Par_Wbis_discrL1 c1d1) 
       next
         assume "(c2, s) \<rightarrow>t s'" and c': "c' = c1"
         hence 
         "(\<exists>d' t'. (d2, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> discr d') \<or> 
          (\<exists>t'. (d2, t) \<rightarrow>*t t' \<and> s' \<approx> t')"
         using st matchT_M2 unfolding matchT_M_def by blast
         thus ?thesis 
         unfolding c' thetaParW_def
         apply - apply(tactic \<open>mauto_no_simp_tac @{context}\<close>)
         apply simp apply (metis PL.ParCR_MtransC Par_Wbis_discrR1 c1d1) 
         apply simp by (metis PL.ParTR_MtransC c1d1)
       qed
     qed 
   qed (unfold matchT_M_def, auto)
  }
  thus ?thesis unfolding thetaParW_def by auto
qed

lemma thetaParW_Wbis:
"thetaParW \<subseteq> Wbis"
apply(rule Wbis_coind)
using thetaParW_sym thetaParW_Wretr by auto

theorem Par_Wbis[simp]:
assumes "c1 \<approx>w d1" and "c2 \<approx>w d2"
shows "Par c1 c2 \<approx>w Par d1 d2"
using assms thetaParW_Wbis unfolding thetaParW_def by blast

end (* context PL_Indis *)
(*******************************************)


end
