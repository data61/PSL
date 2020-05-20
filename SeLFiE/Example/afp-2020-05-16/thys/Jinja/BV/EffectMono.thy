(*  Title:      HOL/MicroJava/BV/EffMono.thy

    Author:     Gerwin Klein
    Copyright   2000 Technische Universitaet Muenchen
*)

section \<open>Monotonicity of eff and app\<close>

theory EffectMono imports Effect begin

declare not_Err_eq [iff]

lemma app\<^sub>i_mono: 
  assumes wf: "wf_prog p P"
  assumes less: "P \<turnstile> \<tau> \<le>\<^sub>i \<tau>'"
  shows "app\<^sub>i (i,P,mxs,mpc,rT,\<tau>') \<Longrightarrow> app\<^sub>i (i,P,mxs,mpc,rT,\<tau>)"
(*<*)
proof -
  assume app: "app\<^sub>i (i,P,mxs,mpc,rT,\<tau>')"
  
  obtain ST LT ST' LT' where
    [simp]: "\<tau> = (ST,LT)" and
    [simp]: "\<tau>' = (ST',LT')" 
    by (cases \<tau>, cases \<tau>')

  from less have [simp]: "size ST = size ST'" and [simp]: "size LT = size LT'"
    by (auto dest: list_all2_lengthD)

  note [iff] = list_all2_Cons2 widen_Class  
  note [simp] = fun_of_def 

  from app less show "app\<^sub>i (i,P,mxs,mpc,rT,\<tau>)"
  proof (cases i)
    case Load
    with app less show ?thesis by (auto dest!: list_all2_nthD)
  next
    case (Invoke M n)
    with app have n: "n < size ST'" by simp
    
    { assume "ST!n = NT" hence ?thesis using n app Invoke by simp }
    moreover {
      assume "ST'!n = NT"
      moreover with n less have "ST!n = NT" 
        by (auto dest: list_all2_nthD)
      ultimately have ?thesis using n app Invoke by simp
    }
    moreover {
      assume ST: "ST!n \<noteq> NT" and ST': "ST'!n \<noteq> NT" 

      from ST' app Invoke obtain D Ts T m C' where
        D:   "ST' ! n = Class D" and
        Ts:  "P \<turnstile> rev (take n ST') [\<le>] Ts" and
        D_M: "P \<turnstile> D sees M: Ts\<rightarrow>T = m in C'"
        by auto

      from n D less have "P \<turnstile> ST!n \<le> ST'!n" 
        by (fastforce dest: list_all2_nthD2)
      with D ST obtain D' where
        D': "ST!n = Class D'" and DsubC: "P \<turnstile> D' \<preceq>\<^sup>* D" by auto

      from wf D_M DsubC obtain Ts' T' m' C'' where
        D'_M: "P \<turnstile> D' sees M: Ts'\<rightarrow>T' = m' in C''" and
        Ts': "P \<turnstile> Ts [\<le>] Ts'"
        by (blast dest: sees_method_mono) 

      from less have "P \<turnstile> rev (take n ST) [\<le>] rev (take n ST')" by simp
      also note Ts also note Ts' 
      finally have "P \<turnstile> rev (take n ST) [\<le>] Ts'" .
      with D'_M D' app less Invoke have ?thesis by fastforce
    }
    ultimately show ?thesis by blast
  next 
    case Getfield
    with app less show ?thesis by (fastforce intro: rtrancl_trans)
  next
    case (Putfield F C)
    with app less show ?thesis by (fastforce intro: widen_trans rtrancl_trans)
  next
    case Return
    with app less show ?thesis by (fastforce intro: widen_trans)
  qed (auto elim!: refTE not_refTE)
qed
(*>*)

lemma succs_mono:
  assumes wf: "wf_prog p P" and app\<^sub>i: "app\<^sub>i (i,P,mxs,mpc,rT,\<tau>')"
  shows "P \<turnstile> \<tau> \<le>\<^sub>i \<tau>' \<Longrightarrow> set (succs i \<tau> pc) \<subseteq> set (succs i \<tau>' pc)"
(*<*)
proof (cases i)
  case (Invoke M n)
  obtain ST LT ST' LT' where 
    [simp]: "\<tau> = (ST,LT)" and [simp]: "\<tau>' = (ST',LT')" by (cases \<tau>, cases \<tau>') 
  assume "P \<turnstile> \<tau> \<le>\<^sub>i \<tau>'"
  moreover
  with app\<^sub>i Invoke have "n < size ST" by (auto dest: list_all2_lengthD)
  ultimately
  have "P \<turnstile> ST!n \<le> ST'!n" by (auto simp add: fun_of_def dest: list_all2_nthD)
  with Invoke show ?thesis by auto 
qed auto
(*>*)
  

lemma app_mono: 
  assumes wf: "wf_prog p P"
  assumes less': "P \<turnstile> \<tau> \<le>' \<tau>'"
  shows "app i P m rT pc mpc xt \<tau>' \<Longrightarrow> app i P m rT pc mpc xt \<tau>"
(*<*)
proof (cases \<tau>)
  case None thus ?thesis by simp
next
  case (Some \<tau>\<^sub>1) 
  moreover
  with less' obtain \<tau>\<^sub>2 where \<tau>\<^sub>2: "\<tau>' = Some \<tau>\<^sub>2" by (cases \<tau>') auto
  ultimately have less: "P \<turnstile> \<tau>\<^sub>1 \<le>\<^sub>i \<tau>\<^sub>2" using less' by simp
  
  assume "app i P m rT pc mpc xt \<tau>'"
  with Some \<tau>\<^sub>2 obtain
    app\<^sub>i: "app\<^sub>i (i, P, pc, m, rT, \<tau>\<^sub>2)" and
    xcpt: "xcpt_app i P pc m xt \<tau>\<^sub>2" and
    succs: "\<forall>(pc',s')\<in>set (eff i P pc xt (Some \<tau>\<^sub>2)). pc' < mpc"
    by (auto simp add: app_def)
  
  from wf less app\<^sub>i have "app\<^sub>i (i, P, pc, m, rT, \<tau>\<^sub>1)" by (rule app\<^sub>i_mono)
  moreover
  from less have "size (fst \<tau>\<^sub>1) = size (fst \<tau>\<^sub>2)" 
    by (cases \<tau>\<^sub>1, cases \<tau>\<^sub>2) (auto dest: list_all2_lengthD)
  with xcpt have "xcpt_app i P pc m xt \<tau>\<^sub>1" by (simp add: xcpt_app_def)
  moreover
  from wf app\<^sub>i less have "\<forall>pc. set (succs i \<tau>\<^sub>1 pc) \<subseteq> set (succs i \<tau>\<^sub>2 pc)"
    by (blast dest: succs_mono)
  with succs
  have "\<forall>(pc',s')\<in>set (eff i P pc xt (Some \<tau>\<^sub>1)). pc' < mpc"
    by (cases \<tau>\<^sub>1, cases \<tau>\<^sub>2)
       (auto simp add: eff_def norm_eff_def xcpt_eff_def dest: bspec)
  ultimately
  show ?thesis using Some by (simp add: app_def)
qed
(*>*)


lemma eff\<^sub>i_mono:
  assumes wf: "wf_prog p P"
  assumes less: "P \<turnstile> \<tau> \<le>\<^sub>i \<tau>'"
  assumes app\<^sub>i: "app i P m rT pc mpc xt (Some \<tau>')"
  assumes succs: "succs i \<tau> pc \<noteq> []"  "succs i \<tau>' pc \<noteq> []"
  shows "P \<turnstile> eff\<^sub>i (i,P,\<tau>) \<le>\<^sub>i eff\<^sub>i (i,P,\<tau>')"
(*<*)
proof -
  obtain ST LT ST' LT' where
    [simp]: "\<tau> = (ST,LT)" and
    [simp]: "\<tau>' = (ST',LT')" 
    by (cases \<tau>, cases \<tau>')
  
  note [simp] = eff_def app_def fun_of_def 

  from less have "P \<turnstile> (Some \<tau>) \<le>' (Some \<tau>')" by simp
  from wf this app\<^sub>i 
  have app: "app i P m rT pc mpc xt (Some \<tau>)" by (rule app_mono)

  from less app app\<^sub>i show ?thesis
  proof (cases i)
    case Throw with succs have False by simp
    thus ?thesis ..
  next
    case Return with succs have False by simp
    thus ?thesis ..
  next
    case (Load i)
    from Load app obtain y where
       y:  "i < size LT" "LT!i = OK y" by clarsimp
    from Load app\<^sub>i obtain y' where
       y': "i < size LT'" "LT'!i = OK y'" by clarsimp

    from less have "P \<turnstile> LT [\<le>\<^sub>\<top>] LT'" by simp
    with y y' have "P \<turnstile> y \<le> y'" by (auto dest: list_all2_nthD)    
    with Load less y y' app app\<^sub>i
    show ?thesis by auto
  next
    case Store with less app app\<^sub>i
    show ?thesis by (auto simp add: list_all2_update_cong) 
  next
    case (Invoke M n) 
    with app\<^sub>i have n: "n < size ST'" by simp
    from less have [simp]: "size ST = size ST'" 
      by (auto dest: list_all2_lengthD)

    from Invoke succs have ST: "ST!n \<noteq> NT" and ST': "ST'!n \<noteq> NT"
      by (auto split: if_split_asm)
    
    from ST' app\<^sub>i Invoke obtain D Ts T m C' where
      D:   "ST' ! n = Class D" and
      D_M: "P \<turnstile> D sees M: Ts\<rightarrow>T = m in C'"
      by auto

    from n D less have "P \<turnstile> ST!n \<le> ST'!n" 
      by (fastforce dest: list_all2_nthD2)
    with D ST obtain D' where
      D': "ST ! n = Class D'" and DsubC: "P \<turnstile> D' \<preceq>\<^sup>* D"
      by (auto simp: widen_Class)
      
    from wf D_M DsubC obtain Ts' T' m' C'' where
      D'_M: "P \<turnstile> D' sees M: Ts'\<rightarrow>T' = m' in C''" and
      Ts': "P \<turnstile> T' \<le> T"
      by (blast dest: sees_method_mono) 

    with Invoke n D D' D_M less 
    show ?thesis by (auto intro: list_all2_dropI)
  qed auto
qed
(*>*)

end

