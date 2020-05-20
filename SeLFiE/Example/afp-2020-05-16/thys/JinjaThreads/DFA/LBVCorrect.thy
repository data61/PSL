(*
    Author:     Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen
*)

section \<open>Correctness of the LBV\<close>

theory LBVCorrect
imports LBVSpec Typing_Framework
begin

locale lbvs = lbv +
  fixes s\<^sub>0  :: 'a
  fixes c   :: "'a list"
  fixes ins :: "'b list"
  fixes \<tau>s  :: "'a list"
  defines phi_def:
  "\<tau>s \<equiv> map (\<lambda>pc. if c!pc = \<bottom> then wtl (take pc ins) c 0 s\<^sub>0 else c!pc) 
       [0..<size ins]"

  assumes bounded: "bounded step (size ins)"
  assumes cert: "cert_ok c (size ins) \<top> \<bottom> A"
  assumes pres: "pres_type step (size ins) A"

lemma (in lbvs) phi_None [intro?]:
  "\<lbrakk> pc < size ins; c!pc = \<bottom> \<rbrakk> \<Longrightarrow> \<tau>s!pc = wtl (take pc ins) c 0 s\<^sub>0"
(*<*) by (simp add: phi_def) (*>*)

lemma (in lbvs) phi_Some [intro?]:
  "\<lbrakk> pc < size ins; c!pc \<noteq> \<bottom> \<rbrakk> \<Longrightarrow> \<tau>s!pc = c!pc"
(*<*) by (simp add: phi_def) (*>*)

lemma (in lbvs) phi_len [simp]: "size \<tau>s = size ins"
(*<*) by (simp add: phi_def) (*>*)

lemma (in lbvs) wtl_suc_pc:
  assumes all: "wtl ins c 0 s\<^sub>0 \<noteq> \<top>" 
  assumes pc:  "pc+1 < size ins"
  shows "wtl (take (pc+1) ins) c 0 s\<^sub>0 \<sqsubseteq>\<^sub>r \<tau>s!(pc+1)"
(*<*)
proof -
  from all pc
  have "wtc c (pc+1) (wtl (take (pc+1) ins) c 0 s\<^sub>0) \<noteq> T" by (rule wtl_all)
  with pc show ?thesis by (simp add: phi_def wtc split: if_split_asm)
qed
(*>*)

lemma (in lbvs) wtl_stable:
  assumes wtl: "wtl ins c 0 s\<^sub>0 \<noteq> \<top>" 
  assumes s\<^sub>0:  "s\<^sub>0 \<in> A" and  pc:  "pc < size ins" 
  shows "stable r step \<tau>s pc"
(*<*)
proof (unfold stable_def, clarify)
  fix pc' s' assume step: "(pc',s') \<in> set (step pc (\<tau>s ! pc))" 
                      (is "(pc',s') \<in> set (?step pc)")
  
  from bounded pc step have pc': "pc' < size ins" by (rule boundedD)

  have tkpc: "wtl (take pc ins) c 0 s\<^sub>0 \<noteq> \<top>" (is "?s\<^sub>1 \<noteq> _") using wtl by (rule wtl_take)
  have s\<^sub>2: "wtl (take (pc+1) ins) c 0 s\<^sub>0 \<noteq> \<top>" (is "?s\<^sub>2 \<noteq> _") using wtl by (rule wtl_take)
  
  from wtl pc have wt_s\<^sub>1: "wtc c pc ?s\<^sub>1 \<noteq> \<top>" by (rule wtl_all)

  have c_Some: "\<forall>pc t. pc < size ins \<longrightarrow> c!pc \<noteq> \<bottom> \<longrightarrow> \<tau>s!pc = c!pc" 
    by (simp add: phi_def)
  have c_None: "c!pc = \<bottom> \<Longrightarrow> \<tau>s!pc = ?s\<^sub>1" using pc ..

  from wt_s\<^sub>1 pc c_None c_Some
  have inst: "wtc c pc ?s\<^sub>1  = wti c pc (\<tau>s!pc)"
    by (simp add: wtc split: if_split_asm)

  have "?s\<^sub>1 \<in> A" using pres cert s\<^sub>0 wtl pc by (rule wtl_pres)
  with pc c_Some cert c_None
  have "\<tau>s!pc \<in> A" by (cases "c!pc = \<bottom>") (auto dest: cert_okD1)
  with pc pres
  have step_in_A: "snd`set (?step pc) \<subseteq> A" by (auto dest: pres_typeD2)

  show "s' \<sqsubseteq>\<^sub>r \<tau>s!pc'" 
  proof (cases "pc' = pc+1")
    case True
    with pc' cert
    have cert_in_A: "c!(pc+1) \<in> A" by (auto dest: cert_okD1)
    from True pc' have pc1: "pc+1 < size ins" by simp
    with tkpc have "?s\<^sub>2 = wtc c pc ?s\<^sub>1" by - (rule wtl_Suc)
    with inst 
    have merge: "?s\<^sub>2 = merge c pc (?step pc) (c!(pc+1))" by (simp add: wti)
    also from s\<^sub>2 merge have "\<dots> \<noteq> \<top>" (is "?merge \<noteq> _") by simp
    with cert_in_A step_in_A
    have "?merge = (map snd [(p',t') \<leftarrow> ?step pc. p'=pc+1] \<Squnion>\<^bsub>f\<^esub> c!(pc+1))"
      by (rule merge_not_top_s) 
    finally have "s' \<sqsubseteq>\<^sub>r ?s\<^sub>2" using step_in_A cert_in_A True step 
      by (auto intro: pp_ub1')
    also from wtl pc1 have "?s\<^sub>2 \<sqsubseteq>\<^sub>r \<tau>s!(pc+1)" by (rule wtl_suc_pc)
    also note True [symmetric]
    finally show ?thesis by simp    
  next
    case False
    from wt_s\<^sub>1 inst 
    have "merge c pc (?step pc) (c!(pc+1)) \<noteq> \<top>" by (simp add: wti)
    with step_in_A have "\<forall>(pc', s')\<in>set (?step pc). pc'\<noteq>pc+1 \<longrightarrow> s' \<sqsubseteq>\<^sub>r c!pc'"
      by - (rule merge_not_top)
    with step False  have ok: "s' \<sqsubseteq>\<^sub>r c!pc'" by blast
    moreover from ok have "c!pc' = \<bottom> \<Longrightarrow> s' = \<bottom>" by simp
    moreover from c_Some pc'  have "c!pc' \<noteq> \<bottom> \<Longrightarrow> \<tau>s!pc' = c!pc'" by auto
    ultimately show ?thesis by (cases "c!pc' = \<bottom>") auto 
  qed
qed
(*>*)
  
lemma (in lbvs) phi_not_top:
  assumes wtl: "wtl ins c 0 s\<^sub>0 \<noteq> \<top>" and pc:  "pc < size ins"
  shows "\<tau>s!pc \<noteq> \<top>"
(*<*)
proof (cases "c!pc = \<bottom>")
  case False with pc
  have "\<tau>s!pc = c!pc" ..
  also from cert pc have "\<dots> \<noteq> \<top>" by (rule cert_okD4)
  finally show ?thesis .
next
  case True with pc
  have "\<tau>s!pc = wtl (take pc ins) c 0 s\<^sub>0" ..
  also from wtl have "\<dots> \<noteq> \<top>" by (rule wtl_take)
  finally show ?thesis .
qed
(*>*)

lemma (in lbvs) phi_in_A:
  assumes wtl: "wtl ins c 0 s\<^sub>0 \<noteq> \<top>" and s\<^sub>0: "s\<^sub>0 \<in> A"
  shows "\<tau>s \<in> list (size ins) A"
(*<*)
proof -
  { fix x assume "x \<in> set \<tau>s"
    then obtain xs ys where "\<tau>s = xs @ x # ys" 
      by (auto simp add: in_set_conv_decomp)
    then obtain pc where pc: "pc < size \<tau>s" and x: "\<tau>s!pc = x"
      by (simp add: that [of "size xs"] nth_append)
    
    from pres cert wtl s\<^sub>0 pc 
    have "wtl (take pc ins) c 0 s\<^sub>0 \<in> A" by (auto intro!: wtl_pres)
    moreover
    from pc have "pc < size ins" by simp
    with cert have "c!pc \<in> A" ..
    ultimately
    have "\<tau>s!pc \<in> A" using pc by (simp add: phi_def)
    hence "x \<in> A" using x by simp
  } 
  hence "set \<tau>s \<subseteq> A" ..
  thus ?thesis by (unfold list_def) simp
qed
(*>*)

lemma (in lbvs) phi0:
  assumes wtl: "wtl ins c 0 s\<^sub>0 \<noteq> \<top>" and 0: "0 < size ins"
  shows "s\<^sub>0 \<sqsubseteq>\<^sub>r \<tau>s!0"
(*<*)
proof (cases "c!0 = \<bottom>")
  case True
  with 0 have "\<tau>s!0 = wtl (take 0 ins) c 0 s\<^sub>0" ..
  moreover have "wtl (take 0 ins) c 0 s\<^sub>0 = s\<^sub>0" by simp
  ultimately have "\<tau>s!0 = s\<^sub>0" by simp
  thus ?thesis by simp
next
  case False
  with 0 have "\<tau>s!0 = c!0" ..
  moreover 
  have "wtl (take 1 ins) c 0 s\<^sub>0 \<noteq> \<top>" using wtl by (rule wtl_take)
  with 0 False 
  have "s\<^sub>0 \<sqsubseteq>\<^sub>r c!0" by (auto simp add: neq_Nil_conv wtc split: if_split_asm)
  ultimately
  show ?thesis by simp
qed
(*>*)


theorem (in lbvs) wtl_sound:
  assumes wtl: "wtl ins c 0 s\<^sub>0 \<noteq> \<top>" and s\<^sub>0: "s\<^sub>0 \<in> A" 
  shows "\<exists>\<tau>s. wt_step r \<top> step \<tau>s"
(*<*)
proof -
  have "wt_step r \<top> step \<tau>s"
  proof (unfold wt_step_def, intro strip conjI)
    fix pc assume "pc < size \<tau>s"
    then obtain pc: "pc < size ins" by simp
    with wtl show "\<tau>s!pc \<noteq> \<top>" by (rule phi_not_top)
    from wtl s\<^sub>0 pc show "stable r step \<tau>s pc" by (rule wtl_stable)
  qed
  thus ?thesis ..
qed
(*>*)


theorem (in lbvs) wtl_sound_strong:
  assumes wtl: "wtl ins c 0 s\<^sub>0 \<noteq> \<top>" 
  assumes s\<^sub>0: "s\<^sub>0 \<in> A" and ins: "0 < size ins"
  shows "\<exists>\<tau>s \<in> list (size ins) A. wt_step r \<top> step \<tau>s \<and> s\<^sub>0 \<sqsubseteq>\<^sub>r \<tau>s!0"
(*<*)
proof -
  have "\<tau>s \<in> list (size ins) A" using wtl s\<^sub>0 by (rule phi_in_A)
  moreover
  have "wt_step r \<top> step \<tau>s"
  proof (unfold wt_step_def, intro strip conjI)
    fix pc assume "pc < size \<tau>s"
    then obtain pc: "pc < size ins" by simp
    with wtl show "\<tau>s!pc \<noteq> \<top>" by (rule phi_not_top)
    from wtl s\<^sub>0 and pc show "stable r step \<tau>s pc" by (rule wtl_stable)
  qed
  moreover from wtl ins have "s\<^sub>0 \<sqsubseteq>\<^sub>r \<tau>s!0" by (rule phi0)
  ultimately show ?thesis by fast
qed
(*>*)

end
