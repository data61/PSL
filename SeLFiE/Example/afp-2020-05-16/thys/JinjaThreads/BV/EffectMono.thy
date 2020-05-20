(*  Title:      JinjaThreads/BV/EffectMono.thy
    Author:     Gerwin Klein, Andreas Lochbihler
*)

section \<open>Monotonicity of eff and app\<close>

theory EffectMono
imports
  Effect
begin

declare not_Err_eq [iff]

declare widens_trans[trans]

lemma app\<^sub>i_mono: 
  assumes wf: "wf_prog p P"
  assumes less: "P \<turnstile> \<tau> \<le>\<^sub>i \<tau>'"
  shows "app\<^sub>i (i,P,mxs,mpc,rT,\<tau>') \<Longrightarrow> app\<^sub>i (i,P,mxs,mpc,rT,\<tau>)"
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
      ultimately have ?thesis using n app Invoke by simp }
    moreover {
      assume ST: "ST!n \<noteq> NT" and ST': "ST'!n \<noteq> NT" 

      from ST' app Invoke
      obtain D Ts T m C'
        where D: "class_type_of' (ST' ! n) = \<lfloor>D\<rfloor>"
        and Ts: "P \<turnstile> rev (take n ST') [\<le>] Ts"
        and D_M: "P \<turnstile> D sees M: Ts\<rightarrow>T = m in C'"
        by fastforce

      from less have "P \<turnstile> ST!n \<le> ST'!n"
        by(auto dest: list_all2_nthD2[OF _ n])
      with D obtain D' where D': "class_type_of' (ST ! n) = \<lfloor>D'\<rfloor>" 
        and DsubC: "P \<turnstile> D' \<preceq>\<^sup>* D"
        using ST by(rule widen_is_class_type_of)
      from wf D_M DsubC obtain Ts' T' m' C'' where
        D'_M: "P \<turnstile> D' sees M: Ts'\<rightarrow>T' = m' in C''" and
        Ts': "P \<turnstile> Ts [\<le>] Ts'"
        by (blast dest: sees_method_mono)
      from less have "P \<turnstile> rev (take n ST) [\<le>] rev (take n ST')" by simp
      also note Ts also note Ts' 
      finally have "P \<turnstile> rev (take n ST) [\<le>] Ts'" .
      with D'_M D' app less Invoke D have ?thesis by(auto)
    }
    ultimately show ?thesis by blast
  next 
    case Getfield
    with app less show ?thesis
      by(fastforce simp add: sees_field_def widen_Array dest: has_fields_fun)
  next
    case Putfield
    with app less show ?thesis
      by (fastforce intro: widen_trans rtrancl_trans simp add: sees_field_def widen_Array dest: has_fields_fun)
  next
    case CAS
    with app less show ?thesis
      by (fastforce intro: widen_trans rtrancl_trans simp add: sees_field_def widen_Array dest: has_fields_fun)
  next
    case Return
    with app less show ?thesis by (fastforce intro: widen_trans)
  next
    case ALoad
    with app less show ?thesis by(auto simp add: widen_Array)
  next
    case AStore
    with app less show ?thesis by(auto simp add: widen_Array)
  next
    case ALength
    with app less show ?thesis by(auto simp add: widen_Array)
  next
    case (Checkcast T)
    with app less show ?thesis
      by(auto elim!: refTE simp: widen_Array)
  next
    case (Instanceof T)
    with app less show ?thesis
      by(auto elim!: refTE simp: widen_Array)
  next
    case ThrowExc
    with app less show ?thesis
      by(auto elim!: refTE simp: widen_Array)
  next
    case MEnter
    with app less show ?thesis
      by(auto elim!: refTE simp: widen_Array)
  next
    case MExit
    with app less show ?thesis
      by(auto elim!: refTE simp: widen_Array)
  next
    case (BinOpInstr bop)
    with app less show ?thesis by(force dest: WTrt_binop_widen_mono)
  next
    case Dup
    with app less show ?thesis
      by(auto dest: list_all2_lengthD)
  next
    case Swap
    with app less show ?thesis
      by(auto dest: list_all2_lengthD)
  qed (auto elim!: refTE not_refTE)
qed

lemma succs_mono:
  assumes wf: "wf_prog p P" and app\<^sub>i: "app\<^sub>i (i,P,mxs,mpc,rT,\<tau>')"
  shows "P \<turnstile> \<tau> \<le>\<^sub>i \<tau>' \<Longrightarrow> set (succs i \<tau> pc) \<subseteq> set (succs i \<tau>' pc)"
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
next
  case ALoad
  obtain ST LT ST' LT' where 
    [simp]: "\<tau> = (ST,LT)" and [simp]: "\<tau>' = (ST',LT')" by (cases \<tau>, cases \<tau>') 
  assume "P \<turnstile> \<tau> \<le>\<^sub>i \<tau>'"
  moreover
  with app\<^sub>i ALoad have "1 < size ST" by (auto dest: list_all2_lengthD)
  ultimately
  have "P \<turnstile> ST!1 \<le> ST'!1" by (auto simp add: fun_of_def dest: list_all2_nthD)
  with ALoad show ?thesis by auto
next 
  case AStore
  obtain ST LT ST' LT' where 
    [simp]: "\<tau> = (ST,LT)" and [simp]: "\<tau>' = (ST',LT')" by (cases \<tau>, cases \<tau>') 
  assume "P \<turnstile> \<tau> \<le>\<^sub>i \<tau>'"
  moreover
  with app\<^sub>i AStore have "2 < size ST" by (auto dest: list_all2_lengthD)
  ultimately
  have "P \<turnstile> ST!2 \<le> ST'!2" by (auto simp add: fun_of_def dest: list_all2_nthD)
  with AStore show ?thesis by auto
next
  case ALength
  obtain ST LT ST' LT' where 
    [simp]: "\<tau> = (ST,LT)" and [simp]: "\<tau>' = (ST',LT')" by (cases \<tau>, cases \<tau>') 
  assume "P \<turnstile> \<tau> \<le>\<^sub>i \<tau>'"
  moreover
  with app\<^sub>i ALength have "0 < size ST" by (auto dest: list_all2_lengthD)
  ultimately
  have "P \<turnstile> ST!0 \<le> ST'!0" by (auto simp add: fun_of_def dest: list_all2_nthD)
  with ALength show ?thesis by auto
next
  case MEnter
  obtain ST LT ST' LT' where 
    [simp]: "\<tau> = (ST,LT)" and [simp]: "\<tau>' = (ST',LT')" by (cases \<tau>, cases \<tau>') 
  assume "P \<turnstile> \<tau> \<le>\<^sub>i \<tau>'"
  moreover
  with app\<^sub>i MEnter have "0 < size ST" by (auto dest: list_all2_lengthD)
  ultimately
  have "P \<turnstile> ST!0 \<le> ST'!0" by (auto simp add: fun_of_def dest: list_all2_nthD)
  with MEnter show ?thesis by auto
next
  case MExit
  obtain ST LT ST' LT' where 
    [simp]: "\<tau> = (ST,LT)" and [simp]: "\<tau>' = (ST',LT')" by (cases \<tau>, cases \<tau>') 
  assume "P \<turnstile> \<tau> \<le>\<^sub>i \<tau>'"
  moreover
  with app\<^sub>i MExit have "0 < size ST" by (auto dest: list_all2_lengthD)
  ultimately
  have "P \<turnstile> ST!0 \<le> ST'!0" by (auto simp add: fun_of_def dest: list_all2_nthD)
  with MExit show ?thesis by auto
qed auto

lemma app_mono: 
  assumes wf: "wf_prog p P"
  assumes less': "P \<turnstile> \<tau> \<le>' \<tau>'"
  shows "app i P m rT pc mpc xt \<tau>' \<Longrightarrow> app i P m rT pc mpc xt \<tau>"
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

lemma eff\<^sub>i_mono:
  assumes wf: "wf_prog p P"
  assumes less: "P \<turnstile> \<tau> \<le>\<^sub>i \<tau>'"
  assumes app\<^sub>i: "app i P m rT pc mpc xt (Some \<tau>')"
  assumes succs: "succs i \<tau> pc \<noteq> []"  "succs i \<tau>' pc \<noteq> []"
  shows "P \<turnstile> eff\<^sub>i (i,P,\<tau>) \<le>\<^sub>i eff\<^sub>i (i,P,\<tau>')"
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
    case ThrowExc with succs have False by simp
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

    from Invoke succs have ST: "ST!n \<noteq> NT" and ST': "ST'!n \<noteq> NT" by (auto)
    
    from ST' app\<^sub>i Invoke obtain D Ts T m C'
      where D: "class_type_of' (ST' ! n) = \<lfloor>D\<rfloor>"
      and Ts: "P \<turnstile> rev (take n ST') [\<le>] Ts"
      and D_M: "P \<turnstile> D sees M: Ts\<rightarrow>T = m in C'"
      by fastforce

    from less have "P \<turnstile> ST!n \<le> ST'!n" by(auto dest: list_all2_nthD2[OF _ n])
    with D obtain D' where D': "class_type_of' (ST ! n) = \<lfloor>D'\<rfloor>" 
      and DsubC: "P \<turnstile> D' \<preceq>\<^sup>* D"
      using ST by(rule widen_is_class_type_of)

    from wf D_M DsubC obtain Ts' T' m' C'' where
      D'_M: "P \<turnstile> D' sees M: Ts'\<rightarrow>T' = m' in C''" and
      Ts': "P \<turnstile> Ts [\<le>] Ts'" and "P \<turnstile> T' \<le> T" by (blast dest: sees_method_mono)

    show ?thesis using Invoke n D D' D_M less D'_M Ts' \<open>P \<turnstile> T' \<le> T\<close>
      by(auto intro: list_all2_dropI)
  next
    case ALoad with less app app\<^sub>i succs
    show ?thesis by(auto split: if_split_asm dest: Array_Array_widen)
  next
    case AStore with less app app\<^sub>i succs
    show ?thesis by(auto split: if_split_asm dest: Array_Array_widen)
  next
    case (BinOpInstr bop)
    with less app app\<^sub>i succs show ?thesis
      by auto(force dest: WTrt_binop_widen_mono WTrt_binop_fun)
  qed auto
qed

end
