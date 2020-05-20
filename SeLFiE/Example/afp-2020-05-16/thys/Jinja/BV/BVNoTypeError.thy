(*  Title:      HOL/MicroJava/BV/BVNoTypeErrors.thy

    Author:     Gerwin Klein
    Copyright   GPL
*)

section \<open>Welltyped Programs produce no Type Errors\<close>

theory BVNoTypeError
imports "../JVM/JVMDefensive" BVSpecTypeSafe
begin

lemma has_methodI:
  "P \<turnstile> C sees M:Ts\<rightarrow>T = m in D \<Longrightarrow> P \<turnstile> C has M"
  by (unfold has_method_def) blast

text \<open>
  Some simple lemmas about the type testing functions of the
  defensive JVM:
\<close>
lemma typeof_NoneD [simp,dest]: "typeof v = Some x \<Longrightarrow> \<not>is_Addr v"
  by (cases v) auto

lemma is_Ref_def2:
  "is_Ref v = (v = Null \<or> (\<exists>a. v = Addr a))"
  by (cases v) (auto simp add: is_Ref_def)

lemma [iff]: "is_Ref Null" by (simp add: is_Ref_def2)

lemma is_RefI [intro, simp]: "P,h \<turnstile> v :\<le> T \<Longrightarrow> is_refT T \<Longrightarrow> is_Ref v"
(*<*)
  apply (cases T)
  apply (auto simp add: is_refT_def is_Ref_def dest: conf_ClassD)
  done
(*>*)

lemma is_IntgI [intro, simp]: "P,h \<turnstile> v :\<le> Integer \<Longrightarrow> is_Intg v"
(*<*)
  apply (unfold conf_def)
  apply auto
  done
(*>*)

lemma is_BoolI [intro, simp]: "P,h \<turnstile> v :\<le> Boolean \<Longrightarrow> is_Bool v"
(*<*)
  apply (unfold conf_def)
  apply auto
  done
(*>*)

declare defs1 [simp del]

lemma wt_jvm_prog_states:
  "\<lbrakk> wf_jvm_prog\<^bsub>\<Phi>\<^esub> P; P \<turnstile> C sees M: Ts\<rightarrow>T = (mxs, mxl, ins, et) in C; 
     \<Phi> C M ! pc = \<tau>; pc < size ins \<rbrakk>
  \<Longrightarrow> OK \<tau> \<in> states P mxs (1+size Ts+mxl)"
(*<*)
  apply (unfold wf_jvm_prog_phi_def)
  apply (drule (1) sees_wf_mdecl)
  apply (simp add: wf_mdecl_def wt_method_def check_types_def)
  apply (blast intro: nth_in)
  done
(*>*)

text \<open>
  The main theorem: welltyped programs do not produce type errors if they
  are started in a conformant state.
\<close>
theorem no_type_error:
  fixes \<sigma> :: jvm_state
  assumes welltyped: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P" and conforms: "P,\<Phi> \<turnstile> \<sigma> \<surd>"
  shows "exec_d P \<sigma> \<noteq> TypeError"
(*<*)
proof -
  from welltyped obtain mb where wf: "wf_prog mb P" by (fast dest: wt_jvm_progD)
  
  obtain xcp h frs where s [simp]: "\<sigma> = (xcp, h, frs)" by (cases \<sigma>)

  from conforms have "xcp \<noteq> None \<or> frs = [] \<Longrightarrow> check P \<sigma>" 
    by (unfold correct_state_def check_def) auto
  moreover {
    assume "\<not>(xcp \<noteq> None \<or> frs = [])"
    then obtain stk reg C M pc frs' where
      xcp [simp]: "xcp = None" and
      frs [simp]: "frs = (stk,reg,C,M,pc)#frs'" 
      by (clarsimp simp add: neq_Nil_conv)

    from conforms obtain  ST LT Ts T mxs mxl ins xt where
      hconf:  "P \<turnstile> h \<surd>" and
      meth:   "P \<turnstile> C sees M:Ts\<rightarrow>T = (mxs, mxl, ins, xt) in C" and
      \<Phi>:      "\<Phi> C M ! pc = Some (ST,LT)" and
      frame:  "conf_f P h (ST,LT) ins (stk,reg,C,M,pc)" and
      frames: "conf_fs P h \<Phi> M (size Ts) T frs'"
      by (fastforce simp add: correct_state_def dest: sees_method_fun)
    
    from frame obtain
      stk: "P,h \<turnstile> stk [:\<le>] ST" and
      reg: "P,h \<turnstile> reg [:\<le>\<^sub>\<top>] LT" and
      pc:  "pc < size ins" 
      by (simp add: conf_f_def)

    from welltyped meth \<Phi> pc
    have "OK (Some (ST, LT)) \<in> states P mxs (1+size Ts+mxl)"
      by (rule wt_jvm_prog_states)
    hence "size ST \<le> mxs" by (auto simp add: JVM_states_unfold)
    with stk have mxs: "size stk \<le> mxs" 
      by (auto dest: list_all2_lengthD)

    from welltyped meth pc
    have "P,T,mxs,size ins,xt \<turnstile> ins!pc,pc :: \<Phi> C M"
      by (rule wt_jvm_prog_impl_wt_instr)
    hence app\<^sub>0: "app (ins!pc) P mxs T pc (size ins) xt (\<Phi> C M!pc) "
      by (simp add: wt_instr_def)
    with \<Phi> have eff: 
      "\<forall>(pc',s')\<in>set (eff (ins ! pc) P pc xt (\<Phi> C M ! pc)). pc' < size ins"
      by (unfold app_def) simp

    from app\<^sub>0 \<Phi> have app:
      "xcpt_app (ins!pc) P pc mxs xt (ST,LT) \<and> app\<^sub>i (ins!pc, P, pc, mxs, T, (ST,LT))"
      by (clarsimp simp add: app_def)

    with eff stk reg 
    have "check_instr (ins!pc) P h stk reg C M pc frs'"
    proof (cases "ins!pc")
      case (Getfield F C) 
      with app stk reg \<Phi> obtain v vT stk' where
        field: "P \<turnstile> C sees F:vT in C" and
        stk:   "stk = v # stk'" and
        conf:  "P,h \<turnstile> v :\<le> Class C"
        by auto
      from conf have is_Ref: "is_Ref v" by auto
      moreover {
        assume "v \<noteq> Null" 
        with conf field is_Ref wf
        have "\<exists>D vs. h (the_Addr v) = Some (D,vs) \<and> P \<turnstile> D \<preceq>\<^sup>* C" 
          by (auto dest!: non_npD)
      }
      ultimately show ?thesis using Getfield field stk hconf
        apply clarsimp
        apply (rule conjI, fastforce)
        apply clarsimp
        apply (drule has_visible_field)
        apply (drule (1) has_field_mono)
        apply (drule (1) hconfD)
        apply (unfold oconf_def has_field_def)
        apply clarsimp
        apply (fastforce dest: has_fields_fun)
        done                            
    next
      case (Putfield F C)
      with app stk reg \<Phi> obtain v ref vT stk' where
        field: "P \<turnstile> C sees F:vT in C" and
        stk:   "stk = v # ref # stk'" and
        confv: "P,h \<turnstile> v :\<le> vT" and
        confr: "P,h \<turnstile> ref :\<le> Class C"
        by fastforce
      from confr have is_Ref: "is_Ref ref" by simp
      moreover {
        assume "ref \<noteq> Null" 
        with confr field is_Ref wf
        have "\<exists>D vs. h (the_Addr ref) = Some (D,vs) \<and> P \<turnstile> D \<preceq>\<^sup>* C"
          by (auto dest: non_npD)
      }
      ultimately show ?thesis using Putfield field stk confv by fastforce
    next      
      case (Invoke M' n)
      with app have n: "n < size ST" by simp

      from stk have [simp]: "size stk = size ST" by (rule list_all2_lengthD)
      
      { assume "stk!n = Null" with n Invoke have ?thesis by simp }
      moreover { 
        assume "ST!n = NT"
        with n stk have "stk!n = Null" by (auto simp: list_all2_conv_all_nth)
        with n Invoke have ?thesis by simp
      }
      moreover {
        assume Null: "stk!n \<noteq> Null" and NT: "ST!n \<noteq> NT"

        from NT app Invoke
        obtain D D' Ts T m where
          D:  "ST!n = Class D" and
          M': "P \<turnstile> D sees M': Ts\<rightarrow>T = m in D'" and
          Ts: "P \<turnstile> rev (take n ST) [\<le>] Ts"
          by auto
        
        from D stk n have "P,h \<turnstile> stk!n :\<le> Class D" 
          by (auto simp: list_all2_conv_all_nth)
        with Null obtain a C' fs where 
          [simp]: "stk!n = Addr a" "h a = Some (C',fs)" and
          "P \<turnstile> C' \<preceq>\<^sup>* D"
          by (fastforce dest!: conf_ClassD) 

        with M' wf obtain m' Ts' T' D'' where 
          C': "P \<turnstile> C' sees M': Ts'\<rightarrow>T' = m' in D''" and
          Ts': "P \<turnstile> Ts [\<le>] Ts'"
          by (auto dest!: sees_method_mono)

        from stk have "P,h \<turnstile> take n stk [:\<le>] take n ST" ..
        hence "P,h \<turnstile> rev (take n stk) [:\<le>] rev (take n ST)" ..
        also note Ts also note Ts'
        finally have "P,h \<turnstile> rev (take n stk) [:\<le>] Ts'" .

        with Invoke Null n C'
        have ?thesis by (auto simp add: is_Ref_def2 has_methodI)
      }
      ultimately show ?thesis by blast      
    next
      case Return with stk app \<Phi> meth frames 
      show ?thesis by (auto simp add: has_methodI)
    qed (auto simp add: list_all2_lengthD)
    hence "check P \<sigma>" using meth pc mxs by (simp add: check_def has_methodI)
  } ultimately
  have "check P \<sigma>" by blast
  thus "exec_d P \<sigma> \<noteq> TypeError" ..
qed
(*>*)


text \<open>
  The theorem above tells us that, in welltyped programs, the
  defensive machine reaches the same result as the aggressive
  one (after arbitrarily many steps).
\<close>
theorem welltyped_aggressive_imp_defensive:
  "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P \<Longrightarrow> P,\<Phi> \<turnstile> \<sigma> \<surd> \<Longrightarrow> P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>'
  \<Longrightarrow> P \<turnstile> (Normal \<sigma>) -jvmd\<rightarrow> (Normal \<sigma>')"
(*<*)
  apply (simp only: exec_all_def) 
  apply (erule rtrancl_induct)
   apply (simp add: exec_all_d_def1)
  apply simp
  apply (simp only: exec_all_def [symmetric])
  apply (frule BV_correct, assumption+) 
  apply (drule no_type_error, assumption, drule no_type_error_commutes, simp)
  apply (simp add: exec_all_d_def1)
  apply (rule rtrancl_trans, assumption)
  apply (drule exec_1_d_NormalI)
  apply auto
  done
(*>*)


text \<open>
  As corollary we get that the aggressive and the defensive machine
  are equivalent for welltyped programs (if started in a conformant
  state or in the canonical start state)
\<close> 
corollary welltyped_commutes:
  fixes \<sigma> :: jvm_state
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P" and conforms: "P,\<Phi> \<turnstile> \<sigma> \<surd>" 
  shows "P \<turnstile> (Normal \<sigma>) -jvmd\<rightarrow> (Normal \<sigma>') = P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>'"
  apply rule
  apply (erule defensive_imp_aggressive)
  apply (erule welltyped_aggressive_imp_defensive [OF wf conforms])
  done

corollary welltyped_initial_commutes:
  assumes wf: "wf_jvm_prog P"  
  assumes meth: "P \<turnstile> C sees M:[]\<rightarrow>T = b in C" 
  defines start: "\<sigma> \<equiv> start_state P C M"
  shows "P \<turnstile> (Normal \<sigma>) -jvmd\<rightarrow> (Normal \<sigma>') = P \<turnstile> \<sigma> -jvm\<rightarrow> \<sigma>'"
proof -
  from wf obtain \<Phi> where wf': "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P" by (auto simp: wf_jvm_prog_def)
  from this meth have "P,\<Phi> \<turnstile> \<sigma> \<surd>" unfolding start by (rule BV_correct_initial)
  with wf' show ?thesis by (rule welltyped_commutes)
qed


lemma not_TypeError_eq [iff]:
  "x \<noteq> TypeError = (\<exists>t. x = Normal t)"
  by (cases x) auto

locale cnf =
  fixes P and \<Phi> and \<sigma>
  assumes wf: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P"  
  assumes cnf: "correct_state P \<Phi> \<sigma>" 

theorem (in cnf) no_type_errors:
  "P \<turnstile> (Normal \<sigma>) -jvmd\<rightarrow> \<sigma>' \<Longrightarrow> \<sigma>' \<noteq> TypeError"
  apply (unfold exec_all_d_def1)   
  apply (erule rtrancl_induct)
   apply simp
  apply (fold exec_all_d_def1)
  apply (insert cnf wf)
  apply clarsimp
  apply (drule defensive_imp_aggressive)
  apply (frule (2) BV_correct)
  apply (drule (1) no_type_error) back
  apply (auto simp add: exec_1_d_eq)
  done

locale start =
  fixes P and C and M and \<sigma> and T and b
  assumes wf: "wf_jvm_prog P"  
  assumes sees: "P \<turnstile> C sees M:[]\<rightarrow>T = b in C" 
  defines "\<sigma> \<equiv> Normal (start_state P C M)"

corollary (in start) bv_no_type_error:
  shows "P \<turnstile> \<sigma> -jvmd\<rightarrow> \<sigma>' \<Longrightarrow> \<sigma>' \<noteq> TypeError"
proof -
  from wf obtain \<Phi> where "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P" by (auto simp: wf_jvm_prog_def)
  moreover
  with sees have "correct_state P \<Phi> (start_state P C M)" 
    by - (rule BV_correct_initial)
  ultimately have "cnf P \<Phi> (start_state P C M)" by (rule cnf.intro)
  moreover assume "P \<turnstile> \<sigma> -jvmd\<rightarrow> \<sigma>'"
  ultimately show ?thesis by (unfold \<sigma>_def) (rule cnf.no_type_errors) 
qed

 
end  
