theory Preprocessor 
imports 
  PCompiler
  "../J/Annotate"
  "../J/JWellForm"
begin

primrec annotate_Mb ::
  "'addr J_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> (vname list \<times> 'addr expr) \<Rightarrow> (vname list \<times> 'addr expr)"
where "annotate_Mb P C M Ts T (pns, e) = (pns, annotate P [this # pns [\<mapsto>] Class C # Ts] e)"
declare annotate_Mb.simps [simp del]

primrec annotate_Mb_code :: 
  "'addr J_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> (vname list \<times> 'addr expr) \<Rightarrow> (vname list \<times> 'addr expr)"
where "annotate_Mb_code P C M Ts T (pns, e) = (pns, annotate_code P [this # pns [\<mapsto>] Class C # Ts] e)"
declare annotate_Mb_code.simps [simp del]

definition annotate_prog :: "'addr J_prog \<Rightarrow> 'addr J_prog"
where "annotate_prog P = compP (annotate_Mb P) P"

definition annotate_prog_code :: "'addr J_prog \<Rightarrow> 'addr J_prog"
where "annotate_prog_code P = compP (annotate_Mb_code P) P"

lemma fixes is_lub
  shows WT_compP: "is_lub,P,E \<turnstile> e :: T \<Longrightarrow> is_lub,compP f P,E \<turnstile> e :: T"
  and WTs_compP: "is_lub,P,E \<turnstile> es [::] Ts \<Longrightarrow> is_lub,compP f P,E \<turnstile> es [::] Ts"
proof(induct rule: WT_WTs.inducts)
  case (WTCall E e U C M Ts T meth D es Ts')
  from \<open>P \<turnstile> C sees M: Ts\<rightarrow>T = meth in D\<close>
  have "compP f P \<turnstile> C sees M: Ts\<rightarrow>T = map_option (f D M Ts T) meth in D"
    by(auto dest: sees_method_compP[where f=f])
  with WTCall show ?case by(auto)
qed(auto simp del: fun_upd_apply)

lemma fixes is_lub
  shows Anno_compP: "is_lub,P,E \<turnstile> e \<leadsto> e' \<Longrightarrow> is_lub,compP f P,E \<turnstile> e \<leadsto> e'"
  and Annos_compP: "is_lub,P,E \<turnstile> es [\<leadsto>] es' \<Longrightarrow> is_lub,compP f P,E \<turnstile> es [\<leadsto>] es'"
apply(induct rule: Anno_Annos.inducts)
apply(auto intro: Anno_Annos.intros simp del: fun_upd_apply dest: WT_compP simp add: compC_def)
done

lemma annotate_prog_code_eq_annotate_prog:
  assumes wf: "wf_J_prog (annotate_prog_code P)"
  shows "annotate_prog_code P = annotate_prog P"
proof -
  let ?wf_md = "\<lambda>_ _ (_,_,_,_,body). set (block_types body) \<subseteq> types P"
  from wf have "wf_prog ?wf_md (annotate_prog_code P)"
    unfolding annotate_prog_code_def
    by(rule wf_prog_lift)(auto dest!: WT_block_types_is_type[OF wf[unfolded annotate_prog_code_def]] simp add: wf_J_mdecl_def)
  hence wf': "wf_prog ?wf_md P"
    unfolding annotate_prog_code_def [abs_def]
  proof(rule wf_prog_compPD)
    fix C M Ts T m
    assume "compP (annotate_Mb_code P) P \<turnstile> C sees M: Ts\<rightarrow>T = \<lfloor>annotate_Mb_code P C M Ts T m\<rfloor> in C"
      and "wf_mdecl ?wf_md (compP (annotate_Mb_code P) P) C (M, Ts, T, \<lfloor>annotate_Mb_code P C M Ts T m\<rfloor>)"
    moreover obtain pns body where "m = (pns, body)" by(cases m)
    ultimately show "wf_mdecl ?wf_md P C (M, Ts, T, \<lfloor>m\<rfloor>)"
      by(fastforce simp add: annotate_Mb_code_def annotate_code_def wf_mdecl_def THE_default_def the_equality Anno_code_def split: if_split_asm dest: Anno_block_types)
  qed

  { fix C D fs ms M Ts T pns body
    assume "(C, D, fs, ms) \<in> set (classes P)"
      and "(M, Ts, T, \<lfloor>(pns, body)\<rfloor>) \<in> set ms"
    from \<open>(C, D, fs, ms) \<in> set (classes P)\<close> have "class P C = \<lfloor>(D, fs, ms)\<rfloor>" using wf'
      by(cases P)(auto simp add: wf_prog_def dest: map_of_SomeI)
    with wf' have sees: "P \<turnstile> C sees M:Ts\<rightarrow>T = \<lfloor>(pns, body)\<rfloor> in C"
      using \<open>(M, Ts, T, \<lfloor>(pns, body)\<rfloor>) \<in> set ms\<close> by(rule mdecl_visible)

    from sees_method_compP[OF this, where f="annotate_Mb_code P"]
    have sees': "annotate_prog_code P \<turnstile> C sees M:Ts\<rightarrow>T = \<lfloor>(pns, annotate_code P [this \<mapsto> Class C, pns [\<mapsto>] Ts] body)\<rfloor> in C"
      unfolding annotate_prog_code_def annotate_Mb_code_def by(auto)
    with wf
    have "wf_mdecl wf_J_mdecl (annotate_prog_code P) C (M, Ts, T, \<lfloor>(pns, annotate_code P [this \<mapsto> Class C, pns [\<mapsto>] Ts] body)\<rfloor>)"
      by(rule sees_wf_mdecl)
    hence "set Ts \<subseteq> types P" by(auto simp add: wf_mdecl_def annotate_prog_code_def)
    moreover from sees have "is_class P C" by(rule sees_method_is_class)
    moreover from wf' sees have "wf_mdecl ?wf_md P C (M, Ts, T, \<lfloor>(pns, body)\<rfloor>)" by(rule sees_wf_mdecl)
    hence "set (block_types body) \<subseteq> types P" by(simp add: wf_mdecl_def)
    ultimately have "ran [this \<mapsto> Class C, pns [\<mapsto>] Ts] \<union> set (block_types body) \<subseteq> types P"
      by(auto simp add: ran_def wf_mdecl_def map_upds_def split: if_split_asm dest!: map_of_SomeD set_zip_rightD)
    hence "annotate_code P [this \<mapsto> Class C, pns [\<mapsto>] Ts] body = annotate P [this \<mapsto> Class C, pns [\<mapsto>] Ts] body"
      unfolding annotate_code_def annotate_def
      by -(rule arg_cong[where f="THE_default body"], auto intro!: ext intro: Anno_code_into_Anno[OF wf'] Anno_into_Anno_code[OF wf']) }
  thus ?thesis unfolding annotate_prog_code_def annotate_prog_def
    by(cases P)(auto simp add: compC_def compM_def annotate_Mb_def annotate_Mb_code_def map_option_case)
qed

end
