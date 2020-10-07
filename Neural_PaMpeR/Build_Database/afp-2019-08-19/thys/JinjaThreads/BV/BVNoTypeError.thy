(*  Title:      JinjaThreads/BV/BVNoTypeError.thy
    Author:     Gerwin Klein, Andreas Lochbihler
*)

section \<open>Welltyped Programs produce no Type Errors\<close>

theory BVNoTypeError
imports
  "../JVM/JVMDefensive"
  BVSpecTypeSafe
begin

lemma wt_jvm_prog_states:
  "\<lbrakk> wf_jvm_prog\<^bsub>\<Phi>\<^esub> P; P \<turnstile> C sees M: Ts\<rightarrow>T = \<lfloor>(mxs, mxl, ins, et)\<rfloor> in C; 
     \<Phi> C M ! pc = \<tau>; pc < size ins \<rbrakk>
  \<Longrightarrow> OK \<tau> \<in> states P mxs (1+size Ts+mxl)"
(*<*)
  apply (unfold wf_jvm_prog_phi_def)
  apply (drule (1) sees_wf_mdecl)
  apply (simp add: wf_mdecl_def wt_method_def check_types_def)
  apply (blast intro: nth_in)
  done
(*>*)

context JVM_heap_conf_base' begin

declare is_IntgI [simp, intro]
declare is_BoolI [simp, intro]
declare is_RefI [simp]

text \<open>
  The main theorem: welltyped programs do not produce type errors if they
  are started in a conformant state.
\<close>
theorem no_type_error:
  assumes welltyped: "wf_jvm_prog\<^bsub>\<Phi>\<^esub> P" and conforms: "\<Phi> \<turnstile> t:\<sigma> \<surd>"
  shows "exec_d P t \<sigma> \<noteq> TypeError"
(*<*)
proof -
  from welltyped obtain mb where wf: "wf_prog mb P" by (fast dest: wt_jvm_progD)
  
  obtain xcp h frs where s [simp]: "\<sigma> = (xcp, h, frs)" by (cases \<sigma>)

  have "check P \<sigma>"
  proof(cases frs)
    case Nil with conforms show ?thesis by (unfold correct_state_def check_def) auto
  next
    case (Cons f frs')
    then obtain stk reg C M pc where frs [simp]: "frs = (stk,reg,C,M,pc)#frs'"
      and f: "f = (stk,reg,C,M,pc)" by(cases f) fastforce

    from conforms obtain  ST LT Ts T mxs mxl ins xt where
      hconf:  "hconf h" and
      tconf:  "P,h \<turnstile> t \<surd>t" and
      meth:   "P \<turnstile> C sees M:Ts\<rightarrow>T = \<lfloor>(mxs, mxl, ins, xt)\<rfloor> in C" and
      \<Phi>:      "\<Phi> C M ! pc = Some (ST,LT)" and
      frame:  "conf_f P h (ST,LT) ins (stk,reg,C,M,pc)" and
      frames: "conf_fs P h \<Phi> M (size Ts) T frs'" and
      confxcp: "conf_xcp P h xcp (ins ! pc)"
      by (fastforce simp add: correct_state_def dest: sees_method_fun)

    from frame obtain
      stk: "P,h \<turnstile> stk [:\<le>] ST" and
      reg: "P,h \<turnstile> reg [:\<le>\<^sub>\<top>] LT" and
      pc:  "pc < size ins" 
      by (simp add: conf_f_def)

    from welltyped meth \<Phi> pc
    have "OK (Some (ST, LT)) \<in> states P mxs (1+size Ts+mxl)"
      by (rule wt_jvm_prog_states)
    hence "size ST \<le> mxs" by (auto simp add: JVM_states_unfold listE_length)
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

    show ?thesis
    proof(cases xcp)
      case None
      note xcp[simp] = this

      from app eff stk reg 
      have "check_instr (ins!pc) P h stk reg C M pc frs'"
      proof (cases "ins!pc")
        case ALoad
        with app stk reg \<Phi> obtain T ST' where
          ST: "ST = Integer # T # ST'" and
          TNT: "T \<noteq> NT \<longrightarrow> (\<exists>T'. T = T'\<lfloor>\<rceil>)"
          by auto
        from stk ST obtain i stk' ref where
          stk': "stk = Intg i # ref # stk'" and
          ref: "P,h \<turnstile> ref :\<le> T"
          by(auto simp add: conf_def list_all2_Cons2)
        
        from ref TNT have is_Ref: "is_Ref ref"
          by(cases ref)(auto simp add: is_Ref_def conf_def)
        moreover
        { assume refN: "ref \<noteq> Null"
          with ref have "T \<noteq> NT" by auto
          with TNT obtain T' where T': "T = T'\<lfloor>\<rceil>" by auto
          with ref refN is_Ref wf
          have "\<exists>T n. typeof_addr h (the_Addr ref) = \<lfloor>Array_type T n\<rfloor>"
            by(cases ref)(auto simp add:conf_def widen_Array) }
        ultimately show ?thesis using ALoad stk'
          by(auto)
      next
        case AStore
        with app stk reg \<Phi> obtain T U ST' where
          ST: "ST = T # Integer # U # ST'" and
          TNT: "U \<noteq> NT \<longrightarrow> (\<exists>T'. U = T'\<lfloor>\<rceil>)"
          by auto
        from stk ST obtain e i stk' ref where
          stk': "stk = e # Intg i # ref # stk'" and
          ref: "P,h \<turnstile> ref :\<le> U" and
          e: "P,h \<turnstile> e :\<le> T"
          by(fastforce simp add: conf_def list_all2_Cons2)
        
        from ref TNT have is_Ref: "is_Ref ref"
          by(cases ref)(auto simp add: is_Ref_def conf_def)
        moreover
        { assume refN: "ref \<noteq> Null"
          with ref have "U \<noteq> NT" by auto
          with TNT obtain T' where T': "U = T'\<lfloor>\<rceil>" by auto
          with ref refN is_Ref wf
          have "\<exists>T n. typeof_addr h (the_Addr ref) = \<lfloor>Array_type T n\<rfloor>"
            by(cases ref)(auto simp add:conf_def widen_Array) }
        ultimately show ?thesis using AStore stk' e by(auto simp add: conf_def)
      next
        case ALength
        with app stk reg \<Phi> obtain T ST' where
          ST: "ST = T # ST'" and
          TNT: "T \<noteq> NT \<longrightarrow> (\<exists>T'. T = T'\<lfloor>\<rceil>)"
          by auto
        from stk ST obtain stk' ref where
          stk': "stk = ref # stk'" and
          ref: "P,h \<turnstile> ref :\<le> T"
          by(auto simp add: conf_def list_all2_Cons2)
      
        from ref TNT have is_Ref: "is_Ref ref"
          by(cases ref)(auto simp add: is_Ref_def conf_def)
        moreover
        { assume refN: "ref \<noteq> Null"
          with ref have "T \<noteq> NT" by auto
          with TNT obtain T' where T': "T = T'\<lfloor>\<rceil>" by auto
          with ref refN is_Ref wf
          have "\<exists>T n. typeof_addr h (the_Addr ref) = \<lfloor>Array_type T n\<rfloor>"
            by(cases ref)(auto simp add:conf_def widen_Array) }
        ultimately show ?thesis using ALength stk'
          by(auto)
      next
        case (Getfield F C) 
        with app stk reg \<Phi> obtain v vT stk' fm where
          field: "P \<turnstile> C sees F:vT (fm) in C" and
          stk:   "stk = v # stk'" and
          conf:  "P,h \<turnstile> v :\<le> Class C"
          by(fastforce simp add: list_all2_Cons2)
        from conf have is_Ref: "is_Ref v" by(cases v)(auto simp add: is_Ref_def conf_def)
        moreover {
          assume "v \<noteq> Null" 
          with conf field is_Ref wf 
          have "\<exists>U. typeof_addr h (the_Addr v) = Some U \<and> P \<turnstile> class_type_of U \<preceq>\<^sup>* C"
            by (auto dest!: non_npD2)
        }
        ultimately show ?thesis using Getfield field stk by auto
      next
        case (Putfield F C)
        with app stk reg \<Phi> obtain v ref vT stk' fm where
          field: "P \<turnstile> C sees F:vT (fm) in C" and
          stk:   "stk = v # ref # stk'" and
          confv: "P,h \<turnstile> v :\<le> vT" and
          confr: "P,h \<turnstile> ref :\<le> Class C"
          by(fastforce simp add: list_all2_Cons2)
        from confr have is_Ref: "is_Ref ref"
          by(cases ref)(auto simp add: is_Ref_def conf_def)
        moreover {
          assume "ref \<noteq> Null" 
          with confr field is_Ref wf
          have "\<exists>U. typeof_addr h (the_Addr ref) = Some U \<and> P \<turnstile> class_type_of U \<preceq>\<^sup>* C"
            by (auto dest: non_npD2)
        }
        ultimately show ?thesis using Putfield field stk confv by auto
      next
        case (CAS F C)
        with app stk reg \<Phi> obtain v v' v'' T' stk' fm where
          field: "P \<turnstile> C sees F:T' (fm) in C" and
          stk:   "stk = v'' # v' # v # stk'" and
          confv: "P,h \<turnstile> v' :\<le> T'" "P,h \<turnstile> v'' :\<le> T'" and
          confr: "P,h \<turnstile> v :\<le> Class C" and vol: "volatile fm"
          by(fastforce simp add: list_all2_Cons2)
        from confr have is_Ref: "is_Ref v"
          by(cases v)(auto simp add: is_Ref_def conf_def)
        moreover {
          assume "v \<noteq> Null" 
          with confr field is_Ref wf
          have "\<exists>U. typeof_addr h (the_Addr v) = Some U \<and> P \<turnstile> class_type_of U \<preceq>\<^sup>* C"
            by (auto dest: non_npD2)
        }
        ultimately show ?thesis using CAS field stk confv vol by auto
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
          obtain D D' Ts T m
            where D: "class_type_of' (ST!n) = \<lfloor>D\<rfloor>"
            and M': "P \<turnstile> D sees M': Ts\<rightarrow>T = m in D'"
            and Ts: "P \<turnstile> rev (take n ST) [\<le>] Ts" by auto
          from stk n have "P,h \<turnstile> stk!n :\<le> ST!n" 
            by (auto simp: list_all2_conv_all_nth)
          with Null D obtain a U where 
            [simp]: "stk!n = Addr a" "typeof_addr h a = Some U" and UsubSTn: "P \<turnstile> ty_of_htype U \<le> ST!n"
            by(cases "stk ! n")(auto simp add: conf_def widen_Class)
          from D UsubSTn obtain C'
            where U: "class_type_of' (ty_of_htype U) = \<lfloor>C'\<rfloor>" and "P \<turnstile> C' \<preceq>\<^sup>* D"
            by(rule widen_is_class_type_of) simp

          from \<open>P \<turnstile> C' \<preceq>\<^sup>* D\<close> wf M' obtain m' Ts' T' D'' where 
            C': "P \<turnstile> C' sees M': Ts'\<rightarrow>T' = m' in D''" and
            Ts': "P \<turnstile> Ts [\<le>] Ts'"
            by (auto dest!: sees_method_mono)

          from stk have "P,h \<turnstile> take n stk [:\<le>] take n ST" ..
          hence "P,h \<turnstile> rev (take n stk) [:\<le>] rev (take n ST)" ..
          also note Ts also note Ts'
          finally have "P,h \<turnstile> rev (take n stk) [:\<le>] Ts'" .
          hence ?thesis using Invoke Null n C' U
            by (auto simp add: is_Ref_def2 has_methodI intro: sees_wf_native[OF wf]) }
        ultimately show ?thesis by blast      
      next
        case Return with stk app \<Phi> meth frames 
        show ?thesis by (fastforce simp add: has_methodI list_all2_Cons2)
      next
        case ThrowExc with stk app \<Phi> meth frames show ?thesis
          by(auto 4 3 simp add: xcpt_app_def conf_def list_all2_Cons2 intro!: is_RefI intro: widen_trans[OF _ widen_subcls])
      next
        case (BinOpInstr bop) with stk app \<Phi> meth frames
        show ?thesis by(auto simp add: conf_def list_all2_Cons2)(force dest: WTrt_binop_widen_mono)
      qed (auto simp add: list_all2_lengthD list_all2_Cons2)
      thus "check P \<sigma>" using meth pc mxs by (simp add: check_def has_methodI)
    next
      case (Some a)
      with confxcp obtain D where "typeof_addr h a = \<lfloor>Class_type D\<rfloor>"
        by(auto simp add: check_xcpt_def)
      moreover from stk have "length stk = length ST" by(rule list_all2_lengthD)
      ultimately show ?thesis using meth pc mxs Some confxcp app
        using match_is_relevant[of P D ins pc pc xt]
        by(auto simp add: check_def has_methodI check_xcpt_def xcpt_app_def dest: bspec)
    qed
  qed
  thus "exec_d P t \<sigma> \<noteq> TypeError" ..
qed

lemma welltyped_commute:
  "\<lbrakk>wf_jvm_prog\<^bsub>\<Phi>\<^esub> P; \<Phi> \<turnstile> t:\<sigma> \<surd>\<rbrakk> \<Longrightarrow> P,t \<turnstile> Normal \<sigma> -ta-jvmd\<rightarrow> Normal \<sigma>' = P,t \<turnstile> \<sigma> -ta-jvm\<rightarrow> \<sigma>'"
apply(rule iffI)
 apply(erule exec_1_d.cases, simp, fastforce simp add: exec_d_def exec_1_iff split: if_split_asm)
by(auto dest!: no_type_error intro!: exec_1_d.intros simp add: exec_d_def exec_1_iff split: if_split_asm)

end

lemma (in JVM_conf_read) BV_correct_d_1:
  "\<lbrakk> wf_jvm_prog\<^bsub>\<Phi>\<^esub> P; P,t \<turnstile> Normal \<sigma> -ta-jvmd\<rightarrow> Normal \<sigma>'; \<Phi> \<turnstile> t:\<sigma> \<surd> \<rbrakk> \<Longrightarrow> \<Phi> \<turnstile> t:\<sigma>' \<surd>"
  unfolding welltyped_commute
  by(rule BV_correct_1)


lemma not_TypeError_eq [iff]:
  "x \<noteq> TypeError = (\<exists>t. x = Normal t)"
  by (cases x) auto

end  
