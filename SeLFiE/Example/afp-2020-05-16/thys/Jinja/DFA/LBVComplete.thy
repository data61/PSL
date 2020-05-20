(*  Title:      HOL/MicroJava/BV/LBVComplete.thy
    Author:     Gerwin Klein
    Copyright   2000 Technische Universitaet Muenchen
*)

section \<open>Completeness of the LBV\<close>

theory LBVComplete
imports LBVSpec Typing_Framework
begin

definition is_target :: "'s step_type \<Rightarrow> 's list \<Rightarrow> nat \<Rightarrow> bool" where
  "is_target step \<tau>s pc' \<longleftrightarrow> (\<exists>pc s'. pc' \<noteq> pc+1 \<and> pc < size \<tau>s \<and> (pc',s') \<in> set (step pc (\<tau>s!pc)))"

definition make_cert :: "'s step_type \<Rightarrow> 's list \<Rightarrow> 's \<Rightarrow> 's certificate" where
  "make_cert step \<tau>s B = map (\<lambda>pc. if is_target step \<tau>s pc then \<tau>s!pc else B) [0..<size \<tau>s] @ [B]"

lemma [code]:
  "is_target step \<tau>s pc' =
  list_ex (\<lambda>pc. pc' \<noteq> pc+1 \<and> List.member (map fst (step pc (\<tau>s!pc))) pc') [0..<size \<tau>s]"
(*<*)
  apply (simp add: list_ex_iff is_target_def member_def)
  apply force
  done
(*>*)

locale lbvc = lbv + 
  fixes \<tau>s :: "'a list" 
  fixes c :: "'a list" 
  defines cert_def: "c \<equiv> make_cert step \<tau>s \<bottom>"

  assumes mono: "mono r step (size \<tau>s) A"
  assumes pres: "pres_type step (size \<tau>s) A" 
  assumes \<tau>s:  "\<forall>pc < size \<tau>s. \<tau>s!pc \<in> A \<and> \<tau>s!pc \<noteq> \<top>"
  assumes bounded: "bounded step (size \<tau>s)"

  assumes B_neq_T: "\<bottom> \<noteq> \<top>" 


lemma (in lbvc) cert: "cert_ok c (size \<tau>s) \<top> \<bottom> A"
(*<*)
proof (unfold cert_ok_def, intro strip conjI)  
  note [simp] = make_cert_def cert_def nth_append 

  show "c!size \<tau>s = \<bottom>" by simp

  fix pc assume pc: "pc < size \<tau>s" 
  from pc \<tau>s B_A show "c!pc \<in> A" by simp
  from pc \<tau>s B_neq_T show "c!pc \<noteq> \<top>" by simp
qed
(*>*)

lemmas [simp del] = split_paired_Ex

lemma (in lbvc) cert_target [intro?]:
  "\<lbrakk> (pc',s') \<in> set (step pc (\<tau>s!pc));
      pc' \<noteq> pc+1; pc < size \<tau>s; pc' < size \<tau>s \<rbrakk>
  \<Longrightarrow> c!pc' = \<tau>s!pc'"
(*<*) by (auto simp add: cert_def make_cert_def nth_append is_target_def) (*>*)

lemma (in lbvc) cert_approx [intro?]:
  "\<lbrakk> pc < size \<tau>s; c!pc \<noteq> \<bottom> \<rbrakk> \<Longrightarrow> c!pc = \<tau>s!pc"
(*<*) by (auto simp add: cert_def make_cert_def nth_append) (*>*)

lemma (in lbv) le_top [simp, intro]: "x <=_r \<top>"
(*<*) by (insert top) simp (*>*)
  
lemma (in lbv) merge_mono:
  assumes less:  "set ss\<^sub>2 {\<sqsubseteq>\<^bsub>r\<^esub>} set ss\<^sub>1"
  assumes x:     "x \<in> A"
  assumes ss\<^sub>1:   "snd`set ss\<^sub>1 \<subseteq> A"
  assumes ss\<^sub>2:   "snd`set ss\<^sub>2 \<subseteq> A"
  shows "merge c pc ss\<^sub>2 x \<sqsubseteq>\<^sub>r merge c pc ss\<^sub>1 x" (is "?s\<^sub>2 \<sqsubseteq>\<^sub>r ?s\<^sub>1")
(*<*)
proof-
  have "?s\<^sub>1 = \<top> \<Longrightarrow> ?thesis" by simp
  moreover {
    assume merge: "?s\<^sub>1 \<noteq> T" 
    from x ss\<^sub>1 have "?s\<^sub>1 =
      (if \<forall>(pc',s')\<in>set ss\<^sub>1. pc' \<noteq> pc + 1 \<longrightarrow> s' \<sqsubseteq>\<^sub>r c!pc'
      then (map snd [(p', t') \<leftarrow> ss\<^sub>1 . p'=pc+1]) \<Squnion>\<^bsub>f\<^esub> x
      else \<top>)" by (rule merge_def)  
    with merge obtain
      app: "\<forall>(pc',s')\<in>set ss\<^sub>1. pc' \<noteq> pc+1 \<longrightarrow> s' \<sqsubseteq>\<^sub>r c!pc'" 
           (is "?app ss\<^sub>1") and
      sum: "(map snd [(p',t') \<leftarrow> ss\<^sub>1 . p' = pc+1] \<Squnion>\<^bsub>f\<^esub> x) = ?s\<^sub>1" 
           (is "?map ss\<^sub>1 \<Squnion>\<^bsub>f\<^esub> x = _" is "?sum ss\<^sub>1 = _")
      by (simp split: if_split_asm)
    from app less have "?app ss\<^sub>2" by (blast dest: trans_r lesub_step_typeD)
    moreover {
      from ss\<^sub>1 have map1: "set (?map ss\<^sub>1) \<subseteq> A" by auto
      with x and semilat Semilat_axioms have "?sum ss\<^sub>1 \<in> A" by (auto intro!: plusplus_closed)
      with sum have "?s\<^sub>1 \<in> A" by simp
      moreover    
      have mapD: "\<And>x ss. x \<in> set (?map ss) \<Longrightarrow> \<exists>p. (p,x) \<in> set ss \<and> p=pc+1" by auto
      from x map1 have "\<forall>x \<in> set (?map ss\<^sub>1). x \<sqsubseteq>\<^sub>r ?sum ss\<^sub>1" by clarify (rule pp_ub1)
      with sum have "\<forall>x \<in> set (?map ss\<^sub>1). x \<sqsubseteq>\<^sub>r ?s\<^sub>1" by simp
      with less have "\<forall>x \<in> set (?map ss\<^sub>2). x \<sqsubseteq>\<^sub>r ?s\<^sub>1"
        by (fastforce dest!: mapD lesub_step_typeD intro: trans_r)
      moreover from map1 x have "x \<sqsubseteq>\<^sub>r (?sum ss\<^sub>1)" by (rule pp_ub2)
      with sum have "x \<sqsubseteq>\<^sub>r ?s\<^sub>1" by simp
      moreover from ss\<^sub>2 have "set (?map ss\<^sub>2) \<subseteq> A" by auto
      ultimately  have "?sum ss\<^sub>2 \<sqsubseteq>\<^sub>r ?s\<^sub>1" using x by - (rule pp_lub)
    }
    moreover from x ss\<^sub>2 have "?s\<^sub>2 =
      (if \<forall>(pc', s')\<in>set ss\<^sub>2. pc' \<noteq> pc + 1 \<longrightarrow> s' \<sqsubseteq>\<^sub>r c!pc'
      then map snd [(p', t') \<leftarrow> ss\<^sub>2 . p' = pc + 1] \<Squnion>\<^bsub>f\<^esub> x
      else \<top>)" by (rule merge_def)
    ultimately have ?thesis by simp
  }
  ultimately show ?thesis by (cases "?s\<^sub>1 = \<top>") auto
qed
(*>*)

lemma (in lbvc) wti_mono:
  assumes less: "s\<^sub>2 \<sqsubseteq>\<^sub>r s\<^sub>1"
  assumes pc: "pc < size \<tau>s" and s\<^sub>1: "s\<^sub>1 \<in> A" and s\<^sub>2: "s\<^sub>2 \<in> A"
  shows "wti c pc s\<^sub>2 \<sqsubseteq>\<^sub>r wti c pc s\<^sub>1" (is "?s\<^sub>2' \<sqsubseteq>\<^sub>r ?s\<^sub>1'")
(*<*)
proof -
  from mono pc s\<^sub>2 less have "set (step pc s\<^sub>2) {\<sqsubseteq>\<^bsub>r\<^esub>} set (step pc s\<^sub>1)" by (rule monoD)
  moreover from cert B_A pc have "c!Suc pc \<in> A" by (rule cert_okD3)
  moreover from pres s\<^sub>1 pc have "snd`set (step pc s\<^sub>1) \<subseteq> A" by (rule pres_typeD2)
  moreover from pres s\<^sub>2 pc have "snd`set (step pc s\<^sub>2) \<subseteq> A" by (rule pres_typeD2)
  ultimately show ?thesis by (simp add: wti merge_mono)
qed 
(*>*)

lemma (in lbvc) wtc_mono:
  assumes less: "s\<^sub>2 \<sqsubseteq>\<^sub>r s\<^sub>1"
  assumes pc: "pc < size \<tau>s" and s\<^sub>1: "s\<^sub>1 \<in> A" and s\<^sub>2: "s\<^sub>2 \<in> A"
  shows "wtc c pc s\<^sub>2 \<sqsubseteq>\<^sub>r wtc c pc s\<^sub>1" (is "?s\<^sub>2' \<sqsubseteq>\<^sub>r ?s\<^sub>1'")
(*<*)
proof (cases "c!pc = \<bottom>")
  case True 
  moreover from less pc s\<^sub>1 s\<^sub>2 have "wti c pc s\<^sub>2 \<sqsubseteq>\<^sub>r wti c pc s\<^sub>1" by (rule wti_mono)
  ultimately show ?thesis by (simp add: wtc)
next
  case False
  have "?s\<^sub>1' = \<top> \<Longrightarrow> ?thesis" by simp
  moreover {
    assume "?s\<^sub>1' \<noteq> \<top>" 
    with False have c: "s\<^sub>1 \<sqsubseteq>\<^sub>r c!pc" by (simp add: wtc split: if_split_asm)
    with less have "s\<^sub>2 \<sqsubseteq>\<^sub>r c!pc" ..
    with False c have ?thesis by (simp add: wtc)
  }
  ultimately show ?thesis by (cases "?s\<^sub>1' = \<top>") auto
qed
(*>*)

lemma (in lbv) top_le_conv [simp]: "\<top> \<sqsubseteq>\<^sub>r x = (x = \<top>)"
(*<*) by (insert semilat) (simp add: top top_le_conv)  (*>*)

lemma (in lbv) neq_top [simp, elim]: "\<lbrakk> x \<sqsubseteq>\<^sub>r y; y \<noteq> \<top> \<rbrakk> \<Longrightarrow> x \<noteq> \<top>"
(*<*) by (cases "x = T") auto (*>*)

lemma (in lbvc) stable_wti:
  assumes stable:  "stable r step \<tau>s pc" and pc: "pc < size \<tau>s"
  shows "wti c pc (\<tau>s!pc) \<noteq> \<top>"
(*<*)
proof -
  let ?step = "step pc (\<tau>s!pc)"
  from stable 
  have less: "\<forall>(q,s')\<in>set ?step. s' \<sqsubseteq>\<^sub>r \<tau>s!q" by (simp add: stable_def)
  
  from cert B_A pc have cert_suc: "c!Suc pc \<in> A" by (rule cert_okD3)
  moreover from \<tau>s pc have "\<tau>s!pc \<in> A" by simp
  with pres pc have stepA: "snd`set ?step \<subseteq> A" by - (rule pres_typeD2)
  ultimately
  have "merge c pc ?step (c!Suc pc) =
    (if \<forall>(pc',s')\<in>set ?step. pc'\<noteq>pc+1 \<longrightarrow> s' \<sqsubseteq>\<^sub>r c!pc'
    then map snd [(p',t') \<leftarrow> ?step.p'=pc+1] \<Squnion>\<^bsub>f\<^esub> c!Suc pc
    else \<top>)" unfolding mrg_def by (rule lbv.merge_def [OF lbvc.axioms(1), OF lbvc_axioms])
  moreover {
    fix pc' s' assume s': "(pc',s') \<in> set ?step" and suc_pc: "pc' \<noteq> pc+1"
    with less have "s' \<sqsubseteq>\<^sub>r \<tau>s!pc'" by auto
    also from bounded pc s' have "pc' < size \<tau>s" by (rule boundedD)
    with s' suc_pc pc have "c!pc' = \<tau>s!pc'" ..
    hence "\<tau>s!pc' = c!pc'" ..
    finally have "s' \<sqsubseteq>\<^sub>r c!pc'" .
  } hence "\<forall>(pc',s')\<in>set ?step. pc'\<noteq>pc+1 \<longrightarrow> s' \<sqsubseteq>\<^sub>r c!pc'" by auto
  moreover from pc have "Suc pc = size \<tau>s \<or> Suc pc < size \<tau>s" by auto
  hence "map snd [(p',t') \<leftarrow> ?step.p'=pc+1] \<Squnion>\<^bsub>f\<^esub> c!Suc pc \<noteq> \<top>" (is "?map \<Squnion>\<^bsub>f\<^esub> _ \<noteq> _")
  proof (rule disjE)
    assume pc': "Suc pc = size \<tau>s"
    with cert have "c!Suc pc = \<bottom>" by (simp add: cert_okD2)
    moreover 
    from pc' bounded pc 
    have "\<forall>(p',t')\<in>set ?step. p'\<noteq>pc+1" by clarify (drule boundedD, auto)
    hence "[(p',t') \<leftarrow> ?step. p'=pc+1] = []" by (blast intro: filter_False)
    hence "?map = []" by simp
    ultimately show ?thesis by (simp add: B_neq_T)
  next
    assume pc': "Suc pc < size \<tau>s"
    from pc' \<tau>s have "\<tau>s!Suc pc \<in> A" by simp
    moreover note cert_suc
    moreover from stepA have "set ?map \<subseteq> A" by auto
    moreover have "\<And>s. s \<in> set ?map \<Longrightarrow> \<exists>t. (Suc pc, t) \<in> set ?step" by auto
    with less have "\<forall>s' \<in> set ?map. s' \<sqsubseteq>\<^sub>r \<tau>s!Suc pc" by auto
    moreover from pc' have "c!Suc pc \<sqsubseteq>\<^sub>r \<tau>s!Suc pc" 
      by (cases "c!Suc pc = \<bottom>") (auto dest: cert_approx)
    ultimately have "?map \<Squnion>\<^bsub>f\<^esub> c!Suc pc \<sqsubseteq>\<^sub>r \<tau>s!Suc pc" by (rule pp_lub)
    moreover from pc' \<tau>s have "\<tau>s!Suc pc \<noteq> \<top>" by simp
    ultimately show ?thesis by auto
  qed
  ultimately have "merge c pc ?step (c!Suc pc) \<noteq> \<top>" by simp
  thus ?thesis by (simp add: wti)  
qed
(*>*)

lemma (in lbvc) wti_less:
  assumes stable: "stable r step \<tau>s pc" and suc_pc: "Suc pc < size \<tau>s"
  shows "wti c pc (\<tau>s!pc) \<sqsubseteq>\<^sub>r \<tau>s!Suc pc" (is "?wti \<sqsubseteq>\<^sub>r _")
(*<*)
proof -
  let ?step = "step pc (\<tau>s!pc)"

  from stable
  have less: "\<forall>(q,s')\<in>set ?step. s' \<sqsubseteq>\<^sub>r \<tau>s!q" by (simp add: stable_def)
   
  from suc_pc have pc: "pc < size \<tau>s" by simp
  with cert B_A have cert_suc: "c!Suc pc \<in> A" by (rule cert_okD3)
  moreover from \<tau>s pc have "\<tau>s!pc \<in> A" by simp
  with pres pc have stepA: "snd`set ?step \<subseteq> A" by - (rule pres_typeD2)
  moreover from stable pc have "?wti \<noteq> \<top>" by (rule stable_wti)
  hence "merge c pc ?step (c!Suc pc) \<noteq> \<top>" by (simp add: wti)
  ultimately
  have "merge c pc ?step (c!Suc pc) =
    map snd [(p',t') \<leftarrow> ?step.p'=pc+1] \<Squnion>\<^bsub>f\<^esub> c!Suc pc" by (rule merge_not_top_s) 
  hence "?wti = \<dots>" (is "_ = (?map \<Squnion>\<^bsub>f\<^esub> _)" is "_ = ?sum") by (simp add: wti)
  also {
    from suc_pc \<tau>s have "\<tau>s!Suc pc \<in> A" by simp
    moreover note cert_suc
    moreover from stepA have "set ?map \<subseteq> A" by auto
    moreover have "\<And>s. s \<in> set ?map \<Longrightarrow> \<exists>t. (Suc pc, t) \<in> set ?step" by auto
    with less have "\<forall>s' \<in> set ?map. s' \<sqsubseteq>\<^sub>r \<tau>s!Suc pc" by auto
    moreover from suc_pc have "c!Suc pc \<sqsubseteq>\<^sub>r \<tau>s!Suc pc"
      by (cases "c!Suc pc = \<bottom>") (auto dest: cert_approx)
    ultimately have "?sum \<sqsubseteq>\<^sub>r \<tau>s!Suc pc" by (rule pp_lub)
  }
  finally show ?thesis .
qed
(*>*)

lemma (in lbvc) stable_wtc:
  assumes stable: "stable r step \<tau>s pc" and pc: "pc < size \<tau>s"
  shows "wtc c pc (\<tau>s!pc) \<noteq> \<top>"
(*<*)
proof -
  from stable pc have wti: "wti c pc (\<tau>s!pc) \<noteq> \<top>" by (rule stable_wti)
  show ?thesis
  proof (cases "c!pc = \<bottom>")
    case True with wti show ?thesis by (simp add: wtc)
  next
    case False
    with pc have "c!pc = \<tau>s!pc" ..    
    with False wti show ?thesis by (simp add: wtc)
  qed
qed
(*>*)

lemma (in lbvc) wtc_less:
  assumes stable: "stable r step \<tau>s pc" and suc_pc: "Suc pc < size \<tau>s"
  shows "wtc c pc (\<tau>s!pc) \<sqsubseteq>\<^sub>r \<tau>s!Suc pc" (is "?wtc \<sqsubseteq>\<^sub>r _")
(*<*)
proof (cases "c!pc = \<bottom>")
  case True
  moreover from stable suc_pc have "wti c pc (\<tau>s!pc) \<sqsubseteq>\<^sub>r \<tau>s!Suc pc" by (rule wti_less)
  ultimately show ?thesis by (simp add: wtc)
next
  case False
  from suc_pc have pc: "pc < size \<tau>s" by simp
  with stable have "?wtc \<noteq> \<top>" by (rule stable_wtc)
  with False have "?wtc = wti c pc (c!pc)" 
    by (unfold wtc) (simp split: if_split_asm)
  also from pc False have "c!pc = \<tau>s!pc" .. 
  finally have "?wtc = wti c pc (\<tau>s!pc)" .
  also from stable suc_pc have "wti c pc (\<tau>s!pc) \<sqsubseteq>\<^sub>r \<tau>s!Suc pc" by (rule wti_less)
  finally show ?thesis .
qed
(*>*)

lemma (in lbvc) wt_step_wtl_lemma:
  assumes wt_step: "wt_step r \<top> step \<tau>s"
  shows "\<And>pc s. pc+size ls = size \<tau>s \<Longrightarrow> s \<sqsubseteq>\<^sub>r \<tau>s!pc \<Longrightarrow> s \<in> A \<Longrightarrow> s\<noteq>\<top> \<Longrightarrow>
                wtl ls c pc s \<noteq> \<top>"
  (is "\<And>pc s. _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> _ \<Longrightarrow> ?wtl ls pc s \<noteq> _")
(*<*)
proof (induct ls)
  fix pc s assume "s\<noteq>\<top>" thus "?wtl [] pc s \<noteq> \<top>" by simp
next
  fix pc s i ls
  assume "\<And>pc s. pc+size ls=size \<tau>s \<Longrightarrow> s \<sqsubseteq>\<^sub>r \<tau>s!pc \<Longrightarrow> s \<in> A \<Longrightarrow> s\<noteq>\<top> \<Longrightarrow> 
                  ?wtl ls pc s \<noteq> \<top>"
  moreover
  assume pc_l: "pc + size (i#ls) = size \<tau>s"
  hence suc_pc_l: "Suc pc + size ls = size \<tau>s" by simp
  ultimately
  have IH: "\<And>s. s \<sqsubseteq>\<^sub>r \<tau>s!Suc pc \<Longrightarrow> s \<in> A \<Longrightarrow> s \<noteq> \<top> \<Longrightarrow> ?wtl ls (Suc pc) s \<noteq> \<top>" .

  from pc_l obtain pc: "pc < size \<tau>s" by simp
  with wt_step have stable: "stable r step \<tau>s pc" by (simp add: wt_step_def)
  moreover note pc
  ultimately have wt_\<tau>s: "wtc c pc (\<tau>s!pc) \<noteq> \<top>" by (rule stable_wtc)

  assume s_\<tau>s: "s \<sqsubseteq>\<^sub>r \<tau>s!pc"
  assume sA: "s \<in> A"
  from \<tau>s pc have \<tau>s_pc: "\<tau>s!pc \<in> A" by simp
  from s_\<tau>s pc \<tau>s_pc sA have wt_s_\<tau>s: "wtc c pc s \<sqsubseteq>\<^sub>r wtc c pc (\<tau>s!pc)" by (rule wtc_mono)
  with wt_\<tau>s have wt_s: "wtc c pc s \<noteq> \<top>" by simp
  moreover assume s: "s \<noteq> \<top>" 
  ultimately have "ls = [] \<Longrightarrow> ?wtl (i#ls) pc s \<noteq> \<top>" by simp
  moreover {
    assume "ls \<noteq> []" 
    with pc_l have suc_pc: "Suc pc < size \<tau>s" by (auto simp add: neq_Nil_conv)
    with stable have "wtc c pc (\<tau>s!pc) \<sqsubseteq>\<^sub>r \<tau>s!Suc pc" by (rule wtc_less)
    with wt_s_\<tau>s have "wtc c pc s \<sqsubseteq>\<^sub>r \<tau>s!Suc pc" by (rule trans_r)      
    moreover from cert suc_pc have "c!pc \<in> A" "c!(pc+1) \<in> A" 
      by (auto simp add: cert_ok_def)
    from pres this sA pc have "wtc c pc s \<in> A" by (rule wtc_pres)
    ultimately have "?wtl ls (Suc pc) (wtc c pc s) \<noteq> \<top>" using IH wt_s by blast
    with s wt_s have "?wtl (i#ls) pc s \<noteq> \<top>" by simp 
  }
  ultimately show "?wtl (i#ls) pc s \<noteq> \<top>" by (cases ls) blast+
qed
(*>*)

theorem (in lbvc) wtl_complete:
  assumes wt: "wt_step r \<top> step \<tau>s"
  assumes s: "s \<sqsubseteq>\<^sub>r \<tau>s!0" "s \<in> A" "s \<noteq> \<top>" and eq: "size ins = size \<tau>s"
  shows "wtl ins c 0 s \<noteq> \<top>"
(*<*)
proof -  
  from eq have "0+size ins = size \<tau>s" by simp
  from wt this s show ?thesis by (rule wt_step_wtl_lemma)
qed
(*>*)

end
