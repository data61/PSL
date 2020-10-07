(*  Title:      JinjaThreads/BV/BVConform.thy
    Author:     Cornelia Pusch, Gerwin Klein, Andreas Lochbihler

The invariant for the type safety proof.
*)

section \<open>BV Type Safety Invariant\<close>

theory BVConform
imports
  BVSpec
  "../JVM/JVMExec"
begin

context JVM_heap_base begin

definition confT :: "'c prog \<Rightarrow> 'heap \<Rightarrow> 'addr val \<Rightarrow> ty err \<Rightarrow> bool"
    ("_,_ \<turnstile> _ :\<le>\<^sub>\<top> _" [51,51,51,51] 50)
where
  "P,h \<turnstile> v :\<le>\<^sub>\<top> E \<equiv> case E of Err \<Rightarrow> True | OK T \<Rightarrow> P,h \<turnstile> v :\<le> T"

notation (ASCII) 
  confT  ("_,_ |- _ :<=T _" [51,51,51,51] 50)

abbreviation confTs :: "'c prog \<Rightarrow> 'heap \<Rightarrow> 'addr val list \<Rightarrow> ty\<^sub>l \<Rightarrow> bool"
  ("_,_ \<turnstile> _ [:\<le>\<^sub>\<top>] _" [51,51,51,51] 50)
where
  "P,h \<turnstile> vs [:\<le>\<^sub>\<top>] Ts \<equiv> list_all2 (confT P h) vs Ts"

notation (ASCII)
  confTs  ("_,_ |- _ [:<=T] _" [51,51,51,51] 50)

definition conf_f :: "'addr jvm_prog \<Rightarrow> 'heap \<Rightarrow> ty\<^sub>i \<Rightarrow> 'addr bytecode \<Rightarrow> 'addr frame \<Rightarrow> bool"
where
  "conf_f P h \<equiv> \<lambda>(ST,LT) is (stk,loc,C,M,pc). P,h \<turnstile> stk [:\<le>] ST \<and> P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT \<and> pc < size is"

primrec conf_fs :: "['addr jvm_prog,'heap,ty\<^sub>P,mname,nat,ty,'addr frame list] \<Rightarrow> bool"
where
  "conf_fs P h \<Phi> M\<^sub>0 n\<^sub>0 T\<^sub>0 [] = True"

| "conf_fs P h \<Phi> M\<^sub>0 n\<^sub>0 T\<^sub>0 (f#frs) =
  (let (stk,loc,C,M,pc) = f in
  (\<exists>ST LT Ts T mxs mxl\<^sub>0 is xt.
    \<Phi> C M ! pc = Some (ST,LT) \<and> 
    (P \<turnstile> C sees M:Ts \<rightarrow> T = \<lfloor>(mxs,mxl\<^sub>0,is,xt)\<rfloor> in C) \<and>
    (\<exists>Ts' T' D m D'.  
       is!pc = (Invoke M\<^sub>0 n\<^sub>0) \<and> class_type_of' (ST!n\<^sub>0) = \<lfloor>D\<rfloor> \<and> P \<turnstile> D sees M\<^sub>0:Ts' \<rightarrow> T' = m in D' \<and> P \<turnstile> T\<^sub>0 \<le> T') \<and>
    conf_f P h (ST, LT) is f \<and> conf_fs P h \<Phi> M (size Ts) T frs))"

primrec conf_xcp :: "'addr jvm_prog \<Rightarrow> 'heap \<Rightarrow> 'addr option \<Rightarrow> 'addr instr \<Rightarrow> bool" where
  "conf_xcp P h None i = True"
| "conf_xcp P h \<lfloor>a\<rfloor>   i = (\<exists>D. typeof_addr h a = \<lfloor>Class_type D\<rfloor> \<and> P \<turnstile> D \<preceq>\<^sup>* Throwable \<and>
                               (\<forall>D'. P \<turnstile> D \<preceq>\<^sup>* D' \<longrightarrow> is_relevant_class i P D'))"

end

context JVM_heap_conf_base begin

definition correct_state :: "[ty\<^sub>P,'thread_id,('addr, 'heap) jvm_state] \<Rightarrow> bool"
where
  "correct_state \<Phi> t \<equiv> \<lambda>(xp,h,frs).
        P,h \<turnstile> t \<surd>t \<and> hconf h \<and> preallocated h \<and>
        (case frs of
             [] \<Rightarrow> True
             | (f#fs) \<Rightarrow> 
             (let (stk,loc,C,M,pc) = f
              in \<exists>Ts T mxs mxl\<^sub>0 is xt \<tau>.
                    (P \<turnstile> C sees M:Ts\<rightarrow>T = \<lfloor>(mxs,mxl\<^sub>0,is,xt)\<rfloor> in C) \<and>
                    \<Phi> C M ! pc = Some \<tau> \<and>
                    conf_f P h \<tau> is f \<and> conf_fs P h \<Phi> M (size Ts) T fs \<and>
                    conf_xcp P h xp (is ! pc) ))"

notation
  correct_state  ("_ \<turnstile> _:_ \<surd>"  [61,0,0] 61)

notation (ASCII)
  correct_state  ("_ |- _:_ [ok]"  [61,0,0] 61)

end

context JVM_heap_base begin

lemma conf_f_def2:
  "conf_f P h (ST,LT) is (stk,loc,C,M,pc) \<equiv>
  P,h \<turnstile> stk [:\<le>] ST \<and> P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT \<and> pc < size is"
  by (simp add: conf_f_def)

subsection \<open>Values and \<open>\<top>\<close>\<close>

lemma confT_Err [iff]: "P,h \<turnstile> x :\<le>\<^sub>\<top> Err" 
  by (simp add: confT_def)

lemma confT_OK [iff]:  "P,h \<turnstile> x :\<le>\<^sub>\<top> OK T = (P,h \<turnstile> x :\<le> T)"
  by (simp add: confT_def)

lemma confT_cases:
  "P,h \<turnstile> x :\<le>\<^sub>\<top> X = (X = Err \<or> (\<exists>T. X = OK T \<and> P,h \<turnstile> x :\<le> T))"
  by (cases X) auto

lemma confT_widen [intro?, trans]:
  "\<lbrakk> P,h \<turnstile> x :\<le>\<^sub>\<top> T; P \<turnstile> T \<le>\<^sub>\<top> T' \<rbrakk> \<Longrightarrow> P,h \<turnstile> x :\<le>\<^sub>\<top> T'"
  by (cases T', auto intro: conf_widen)

end

context JVM_heap begin

lemma confT_hext [intro?, trans]:
  "\<lbrakk> P,h \<turnstile> x :\<le>\<^sub>\<top> T; h \<unlhd> h' \<rbrakk> \<Longrightarrow> P,h' \<turnstile> x :\<le>\<^sub>\<top> T"
  by (cases T) (blast intro: conf_hext)+

end

subsection \<open>Stack and Registers\<close>

context JVM_heap_base begin

lemma confTs_Cons1 [iff]:
  "P,h \<turnstile> x # xs [:\<le>\<^sub>\<top>] Ts = (\<exists>z zs. Ts = z # zs \<and> P,h \<turnstile> x :\<le>\<^sub>\<top> z \<and> list_all2 (confT P h) xs zs)"
by(rule list_all2_Cons1)

lemma confTs_confT_sup:
  "\<lbrakk> P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT; n < size LT; LT!n = OK T; P \<turnstile> T \<le> T' \<rbrakk> 
  \<Longrightarrow> P,h \<turnstile> (loc!n) :\<le> T'"
  apply (frule list_all2_lengthD)
  apply (drule list_all2_nthD, simp)
  apply simp
  apply (erule conf_widen, assumption+)
  done

lemma confTs_widen [intro?, trans]:
  "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT \<Longrightarrow> P \<turnstile> LT [\<le>\<^sub>\<top>] LT' \<Longrightarrow> P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT'"
  by (rule list_all2_trans, rule confT_widen)

lemma confTs_map [iff]:
  "(P,h \<turnstile> vs [:\<le>\<^sub>\<top>] map OK Ts) = (P,h \<turnstile> vs [:\<le>] Ts)"
  by (induct Ts arbitrary: vs) (auto simp add: list_all2_Cons2)

lemma (in -) reg_widen_Err:
  "(P \<turnstile> replicate n Err [\<le>\<^sub>\<top>] LT) = (LT = replicate n Err)"
  by (induct n arbitrary: LT) (auto simp add: list_all2_Cons1)

declare reg_widen_Err [iff]

lemma confTs_Err [iff]:
  "P,h \<turnstile> replicate n v [:\<le>\<^sub>\<top>] replicate n Err"
  by (induct n) auto

end

context JVM_heap begin

lemma confTs_hext [intro?]:
  "P,h \<turnstile> loc [:\<le>\<^sub>\<top>] LT \<Longrightarrow> h \<unlhd> h' \<Longrightarrow> P,h' \<turnstile> loc [:\<le>\<^sub>\<top>] LT"
  by (fast elim: list_all2_mono confT_hext)    
  
subsection \<open>correct-frames\<close>

declare fun_upd_apply[simp del]

lemma conf_f_hext:
  "\<lbrakk> conf_f P h \<Phi> M f; h \<unlhd> h' \<rbrakk> \<Longrightarrow> conf_f P h' \<Phi> M f"
by(cases f, cases \<Phi>, auto simp add: conf_f_def intro: confs_hext confTs_hext)

lemma conf_fs_hext:
  "\<lbrakk> conf_fs P h \<Phi> M n T\<^sub>r frs; h \<unlhd> h' \<rbrakk> \<Longrightarrow> conf_fs P h' \<Phi> M n T\<^sub>r frs"
apply (induct frs arbitrary: M n T\<^sub>r)
 apply simp
apply clarify
apply (simp (no_asm_use))
apply clarify
apply (unfold conf_f_def)
apply (simp (no_asm_use) split: if_split_asm)
apply (fast elim!: confs_hext confTs_hext)+
done

declare fun_upd_apply[simp]

lemma conf_xcp_hext:
  "\<lbrakk> conf_xcp P h xcp i; h \<unlhd> h' \<rbrakk> \<Longrightarrow> conf_xcp P h' xcp i"
by(cases xcp)(auto elim: typeof_addr_hext_mono)

end

context JVM_heap_conf_base begin

lemmas defs1 = correct_state_def conf_f_def wt_instr_def eff_def norm_eff_def app_def xcpt_app_def

lemma correct_state_impl_Some_method:
  "\<Phi> \<turnstile> t: (None, h, (stk,loc,C,M,pc)#frs)\<surd> 
  \<Longrightarrow> \<exists>m Ts T. P \<turnstile> C sees M:Ts\<rightarrow>T = \<lfloor>m\<rfloor> in C"
  by(fastforce simp add: defs1)

end

context JVM_heap_conf_base' begin

lemma correct_state_hext_mono:
  "\<lbrakk> \<Phi> \<turnstile> t: (xcp, h, frs) \<surd>; h \<unlhd> h'; hconf h' \<rbrakk> \<Longrightarrow> \<Phi> \<turnstile> t: (xcp, h', frs) \<surd>"
unfolding correct_state_def
by(fastforce elim: tconf_hext_mono preallocated_hext conf_f_hext conf_fs_hext conf_xcp_hext split: list.split)

end

end
