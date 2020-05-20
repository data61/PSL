(*  Title:      JinjaThreads/J/Deadlocked.thy
    Author:     Andreas Lochbihler
*)

section \<open>Preservation of Deadlock\<close>

theory Deadlocked
imports
  ProgressThreaded
begin

context J_progress begin

lemma red_wt_hconf_hext:
  assumes wf: "wf_J_prog P"
  and hconf: "hconf H"
  and tconf: "P,H \<turnstile> t \<surd>t"
  shows "\<lbrakk> convert_extTA extNTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; P,E,H \<turnstile> e : T; hext H (hp s) \<rbrakk>
        \<Longrightarrow> \<exists>ta' e' s'. convert_extTA extNTA,P,t \<turnstile> \<langle>e, (H, lcl s)\<rangle> -ta'\<rightarrow> \<langle>e', s'\<rangle> \<and>
                       collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<and> collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> = collect_cond_actions \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<and>
                       collect_interrupts \<lbrace>ta\<rbrace>\<^bsub>i\<^esub> = collect_interrupts \<lbrace>ta'\<rbrace>\<^bsub>i\<^esub>"
  and "\<lbrakk> convert_extTA extNTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; P,E,H \<turnstile> es [:] Ts; hext H (hp s) \<rbrakk>
        \<Longrightarrow> \<exists>ta' es' s'. convert_extTA extNTA,P,t \<turnstile> \<langle>es, (H, lcl s)\<rangle> [-ta'\<rightarrow>] \<langle>es', s'\<rangle> \<and> 
                        collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<and> collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> = collect_cond_actions \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<and>
                        collect_interrupts \<lbrace>ta\<rbrace>\<^bsub>i\<^esub> = collect_interrupts \<lbrace>ta'\<rbrace>\<^bsub>i\<^esub>"
proof(induct arbitrary: E T and E Ts rule: red_reds.inducts)
  case (RedNew h' a h C l)
  thus ?case
    by(cases "allocate H (Class_type C) = {}")(fastforce simp add: ta_upd_simps intro: RedNewFail red_reds.RedNew)+
next
  case (RedNewFail h C l)
  thus ?case
    by(cases "allocate H (Class_type C) = {}")(fastforce simp add: ta_upd_simps intro: red_reds.RedNewFail RedNew)+
next 
  case NewArrayRed thus ?case by(fastforce intro: red_reds.intros)
next
  case (RedNewArray i h' a h T l E T')
  thus ?case
    by(cases "allocate H (Array_type T (nat (sint i))) = {}")(fastforce simp add: ta_upd_simps intro: red_reds.RedNewArray RedNewArrayFail)+
next
  case RedNewArrayNegative thus ?case by(fastforce intro: red_reds.intros)
next
  case (RedNewArrayFail i h T l E T')
  thus ?case 
    by(cases "allocate H (Array_type T (nat (sint i))) = {}")(fastforce simp add: ta_upd_simps intro: RedNewArray red_reds.RedNewArrayFail)+
next
  case CastRed thus ?case by(fastforce intro: red_reds.intros)
next
  case (RedCast s v U T E T')
  from \<open>P,E,H \<turnstile> Cast T (Val v) : T'\<close> show ?case
  proof(rule WTrt_elim_cases)
    fix T''
    assume wt: "P,E,H \<turnstile> Val v : T''" "T = T'"
    thus ?thesis
      by(cases "P \<turnstile> T'' \<le> T")(fastforce intro: red_reds.RedCast red_reds.RedCastFail)+
  qed
next 
  case (RedCastFail s v U T E T')
  from \<open>P,E,H \<turnstile> Cast T (Val v) : T'\<close> 
  obtain T'' where "P,E,H \<turnstile> Val v : T''" "T = T'" by auto
  thus ?case
    by(cases "P \<turnstile> T'' \<le> T")(fastforce intro: red_reds.RedCast red_reds.RedCastFail)+
next
  case InstanceOfRed thus ?case by(fastforce intro: red_reds.intros)
next
  case RedInstanceOf thus ?case
    using [[hypsubst_thin = true]] 
    by auto((rule exI conjI red_reds.RedInstanceOf)+, auto)
next
  case BinOpRed1 thus ?case by(fastforce intro: red_reds.intros)
next
  case BinOpRed2 thus ?case by(fastforce intro: red_reds.intros)
next
  case RedBinOp thus ?case by(fastforce intro: red_reds.intros)
next
  case RedBinOpFail thus ?case by(fastforce intro: red_reds.intros)
next
  case RedVar thus ?case by(fastforce intro: red_reds.intros)
next
  case LAssRed thus ?case by(fastforce intro: red_reds.intros)
next
  case RedLAss thus ?case by(fastforce intro: red_reds.intros)
next
  case AAccRed1 thus ?case by(fastforce intro: red_reds.intros)
next
  case AAccRed2 thus ?case by(fastforce intro: red_reds.intros)
next
  case RedAAccNull thus ?case by(fastforce intro: red_reds.intros)
next
  case RedAAccBounds thus ?case
    by(fastforce intro: red_reds.RedAAccBounds dest: hext_arrD)
next 
  case (RedAAcc h a T n i v l E T')
  from \<open>P,E,H \<turnstile> addr a\<lfloor>Val (Intg i)\<rceil> : T'\<close> 
  have wt: "P,E,H \<turnstile> addr a : T'\<lfloor>\<rceil>" by(auto)
  with \<open>H \<unlhd> hp (h, l)\<close> \<open>typeof_addr h a = \<lfloor>Array_type T n\<rfloor>\<close>
  have Ha: "typeof_addr H a = \<lfloor>Array_type T n\<rfloor>" by(auto dest: hext_arrD)
  with \<open>0 <=s i\<close> \<open>sint i < int n\<close>
  have "nat (sint i) < n" by(metis nat_less_iff sint_0 word_sle_def)
  with Ha have "P,H \<turnstile> a@ACell (nat (sint i)) : T"
    by(auto intro: addr_loc_type.intros)
  from heap_read_total[OF hconf this]
  obtain v where "heap_read H a (ACell (nat (sint i))) v" by blast
  with Ha \<open>0 <=s i\<close> \<open>sint i < int n\<close> show ?case
    by(fastforce intro: red_reds.RedAAcc simp add: ta_upd_simps)
next
  case AAssRed1 thus ?case by(fastforce intro: red_reds.intros)
next
  case AAssRed2 thus ?case by(fastforce intro: red_reds.intros)
next
  case AAssRed3 thus ?case by(fastforce intro: red_reds.intros)
next
  case RedAAssNull thus ?case by(fastforce intro: red_reds.intros)
next
  case RedAAssBounds thus ?case by(fastforce intro: red_reds.RedAAssBounds dest: hext_arrD)
next
  case (RedAAssStore s a T n i w U E T')
  from \<open>P,E,H \<turnstile> addr a\<lfloor>Val (Intg i)\<rceil> := Val w : T'\<close> 
  obtain T'' T''' where wt: "P,E,H \<turnstile> addr a : T''\<lfloor>\<rceil>"
    and wtw: "P,E,H \<turnstile> Val w : T'''" by auto
  with \<open>H \<unlhd> hp s\<close> \<open>typeof_addr (hp s) a = \<lfloor>Array_type T n\<rfloor>\<close>
  have Ha: "typeof_addr H a = \<lfloor>Array_type T n\<rfloor>" by(auto dest: hext_arrD)
  from \<open>typeof\<^bsub>hp s\<^esub> w = \<lfloor>U\<rfloor>\<close> wtw \<open>H \<unlhd> hp s\<close> have "typeof\<^bsub>H\<^esub> w = \<lfloor>U\<rfloor>" 
    by(auto dest: type_of_hext_type_of)
  with Ha \<open>0 <=s i\<close> \<open>sint i < int n\<close> \<open>\<not> P \<turnstile> U \<le> T\<close> show ?case
    by(fastforce intro: red_reds.RedAAssStore)
next
  case (RedAAss h a T n i w U h' l E T')
  from \<open>P,E,H \<turnstile> addr a\<lfloor>Val (Intg i)\<rceil> := Val w : T'\<close>
  obtain T'' T''' where wt: "P,E,H \<turnstile> addr a : T''\<lfloor>\<rceil>"
      and wtw: "P,E,H \<turnstile> Val w : T'''" by auto
  with \<open>H \<unlhd> hp (h, l)\<close> \<open>typeof_addr h a = \<lfloor>Array_type T n\<rfloor>\<close>
  have Ha: "typeof_addr H a = \<lfloor>Array_type T n\<rfloor>" by(auto dest: hext_arrD)
  from \<open>typeof\<^bsub>h\<^esub> w = \<lfloor>U\<rfloor>\<close> wtw \<open>H \<unlhd> hp (h, l)\<close> have "typeof\<^bsub>H\<^esub> w = \<lfloor>U\<rfloor>" 
    by(auto dest: type_of_hext_type_of)
  moreover
  with \<open>P \<turnstile> U \<le> T\<close> have conf: "P,H \<turnstile> w :\<le> T"
    by(auto simp add: conf_def)
  from \<open>0 <=s i\<close> \<open>sint i < int n\<close>
  have "nat (sint i) < n"
    by (metis nat_less_iff sint_0 word_sle_def)
  with Ha have "P,H \<turnstile> a@ACell (nat (sint i)) : T"
    by(auto intro: addr_loc_type.intros)
  from heap_write_total[OF hconf this conf]
  obtain H' where "heap_write H a (ACell (nat (sint i))) w H'" ..
  ultimately show ?case using \<open>0 <=s i\<close> \<open>sint i < int n\<close> Ha \<open>P \<turnstile> U \<le> T\<close>
    by(fastforce simp del: split_paired_Ex intro: red_reds.RedAAss)
next
  case ALengthRed thus ?case by(fastforce intro: red_reds.intros)
next
  case (RedALength h a T n l E T')
  from \<open>P,E,H \<turnstile> addr a\<bullet>length : T'\<close>
  obtain T'' where [simp]: "T' = Integer"
      and wta: "P,E,H \<turnstile> addr a : T''\<lfloor>\<rceil>" by(auto)
  then obtain n'' where "typeof_addr H a = \<lfloor>Array_type T'' n''\<rfloor>" by(auto)
  thus ?case by(fastforce intro: red_reds.RedALength)
next
  case RedALengthNull show ?case by(fastforce intro: red_reds.RedALengthNull)
next
  case FAccRed thus ?case by(fastforce intro: red_reds.intros)
next
  case (RedFAcc h a D F v l E T)
  from \<open>P,E,H \<turnstile> addr a\<bullet>F{D} : T\<close> obtain U C' fm
    where wt: "P,E,H \<turnstile> addr a : U"
    and icto: "class_type_of' U = \<lfloor>C'\<rfloor>"
    and has: "P \<turnstile> C' has F:T (fm) in D"
    by(auto)
  then obtain hU where Ha: "typeof_addr H a = \<lfloor>hU\<rfloor>" "U = ty_of_htype hU" by(auto)
  with icto \<open>P \<turnstile> C' has F:T (fm) in D\<close> have "P,H \<turnstile> a@CField D F : T"
    by(auto intro: addr_loc_type.intros)
  from heap_read_total[OF hconf this]
  obtain v where "heap_read H a (CField D F) v" by blast
  thus ?case by(fastforce intro: red_reds.RedFAcc simp add: ta_upd_simps)
next
  case RedFAccNull thus ?case by(fastforce intro: red_reds.intros)
next
  case FAssRed1 thus ?case by(fastforce intro: red_reds.intros)
next
  case FAssRed2 thus ?case by(fastforce intro: red_reds.intros)
next
  case RedFAssNull thus ?case by(fastforce intro: red_reds.intros)
next
  case (RedFAss h a D F v h' l E T)
  from \<open>P,E,H \<turnstile> addr a\<bullet>F{D} := Val v : T\<close> obtain U C' T' T2 fm
    where wt: "P,E,H \<turnstile> addr a : U"
    and icto: "class_type_of' U = \<lfloor>C'\<rfloor>"
    and has: "P \<turnstile> C' has F:T' (fm) in D"
    and wtv: "P,E,H \<turnstile> Val v : T2"
    and T2T: "P \<turnstile> T2 \<le> T'" by(auto)
  moreover from wt obtain hU where Ha: "typeof_addr H a = \<lfloor>hU\<rfloor>" "U = ty_of_htype hU" by(auto)
  with icto has have adal: "P,H \<turnstile> a@CField D F : T'" by(auto intro: addr_loc_type.intros)
  from wtv T2T have "P,H \<turnstile> v :\<le> T'" by(auto simp add: conf_def)
  from heap_write_total[OF hconf adal this]
  obtain h' where "heap_write H a (CField D F) v h'" ..
  thus ?case by(fastforce intro: red_reds.RedFAss)
next
  case CASRed1 thus ?case by(fastforce intro: red_reds.intros)
next
  case CASRed2 thus ?case by(fastforce intro: red_reds.intros)
next
  case CASRed3 thus ?case by(fastforce intro: red_reds.intros)
next
  case CASNull thus ?case by(fastforce intro: red_reds.intros)
next
  case (RedCASSucceed h a D F v v' h' l)
  note split_paired_Ex[simp del]
  from RedCASSucceed.prems(1) obtain T' fm T2 T3 U C where *:
    "T = Boolean" "class_type_of' U = \<lfloor>C\<rfloor>" "P \<turnstile> C has F:T' (fm) in D" 
    "volatile fm" "P \<turnstile> T2 \<le> T'" "P \<turnstile> T3 \<le> T'"
    "P,E,H \<turnstile> Val v : T2" "P,E,H \<turnstile> Val v' : T3" "P,E,H \<turnstile> addr a : U" by auto
  then have adal: "P,H \<turnstile> a@CField D F : T'" by(auto intro: addr_loc_type.intros)
  from heap_read_total[OF hconf this] obtain v'' where v': "heap_read H a (CField D F) v''" by blast
  show ?case
  proof(cases "v'' = v")
    case True
    from * have "P,H \<turnstile> v' :\<le> T'" by(auto simp add: conf_def)
    from heap_write_total[OF hconf adal this] True * v'
    show ?thesis by(fastforce intro: red_reds.RedCASSucceed)
  next
    case False
    then show ?thesis using * v' by(fastforce intro: RedCASFail)
  qed
next
  case (RedCASFail h a D F v'' v v' l)
  note split_paired_Ex[simp del]
  from RedCASFail.prems(1) obtain T' fm T2 T3 U C where *:
    "T = Boolean" "class_type_of' U = \<lfloor>C\<rfloor>" "P \<turnstile> C has F:T' (fm) in D" 
    "volatile fm" "P \<turnstile> T2 \<le> T'" "P \<turnstile> T3 \<le> T'"
    "P,E,H \<turnstile> Val v : T2" "P,E,H \<turnstile> Val v' : T3" "P,E,H \<turnstile> addr a : U" by auto
  then have adal: "P,H \<turnstile> a@CField D F : T'" by(auto intro: addr_loc_type.intros)
  from heap_read_total[OF hconf this] obtain v''' where v'': "heap_read H a (CField D F) v'''" by blast
  show ?case
  proof(cases "v''' = v")
    case True
    from * have "P,H \<turnstile> v' :\<le> T'" by(auto simp add: conf_def)
    from heap_write_total[OF hconf adal this] True * v''
    show ?thesis by(fastforce intro: red_reds.RedCASSucceed)
  next
    case False
    then show ?thesis using * v'' by(fastforce intro: red_reds.RedCASFail)
  qed
next
  case CallObj thus ?case by(fastforce intro: red_reds.intros)
next
  case CallParams thus ?case by(fastforce intro: red_reds.intros)
next
  case (RedCall s a U M Ts T pns body D vs E T')
  from \<open>P,E,H \<turnstile> addr a\<bullet>M(map Val vs) : T'\<close> 
  obtain U' C' Ts' meth D' Ts''
    where wta: "P,E,H \<turnstile> addr a : U'"
    and icto: "class_type_of' U' = \<lfloor>C'\<rfloor>"
    and sees: "P \<turnstile> C' sees M: Ts'\<rightarrow>T' = meth in D'"
    and wtes: "P,E,H \<turnstile> map Val vs [:] Ts''"
    and widens: "P \<turnstile> Ts'' [\<le>] Ts'" by auto
  from wta obtain hU' where Ha: "typeof_addr H a = \<lfloor>hU'\<rfloor>" "U' = ty_of_htype hU'" by(auto)
  moreover from \<open>typeof_addr (hp s) a = \<lfloor>U\<rfloor>\<close> \<open>H \<unlhd> hp s\<close> Ha
  have [simp]: "U = hU'" by(auto dest: typeof_addr_hext_mono)
  from wtes have "length vs = length Ts''"
    by(auto intro: map_eq_imp_length_eq)
  moreover from widens have "length Ts'' = length Ts'"
    by(auto dest: widens_lengthD)
  moreover from sees icto sees \<open>P \<turnstile> class_type_of U sees M: Ts\<rightarrow>T = \<lfloor>(pns, body)\<rfloor> in D\<close> Ha
  have [simp]: "meth = \<lfloor>(pns, body)\<rfloor>" by(auto dest: sees_method_fun)
  with sees wf have "wf_mdecl wf_J_mdecl P D' (M, Ts', T', \<lfloor>(pns, body)\<rfloor>)"
    by(auto intro: sees_wf_mdecl)
  hence "length pns = length Ts'" by(simp add: wf_mdecl_def)
  ultimately show ?case using sees icto 
    by(fastforce intro: red_reds.RedCall)
next
  case (RedCallExternal s a U M Ts T' D vs ta va h' ta' e' s')
  from \<open>P,E,H \<turnstile> addr a\<bullet>M(map Val vs) : T\<close> 
  obtain U' C' Ts' meth D' Ts'' 
    where wta: "P,E,H \<turnstile> addr a : U'" and icto: "class_type_of' U' = \<lfloor>C'\<rfloor>"
    and sees: "P \<turnstile> C' sees M: Ts'\<rightarrow>T = meth in D'"
    and wtvs: "P,E,H \<turnstile> map Val vs [:] Ts''" 
    and sub: "P \<turnstile> Ts'' [\<le>] Ts'" by auto
  from wta \<open>typeof_addr (hp s) a = \<lfloor>U\<rfloor>\<close> \<open>hext H (hp s)\<close> have [simp]: "U' = ty_of_htype U"
    by(auto dest: typeof_addr_hext_mono)
  with icto have [simp]: "C' = class_type_of U" by(auto)
  from sees \<open>P \<turnstile> class_type_of U sees M: Ts\<rightarrow>T' = Native in D\<close>
  have [simp]: "meth = Native" by(auto dest: sees_method_fun)
  with wta sees icto wtvs sub have "P,H \<turnstile> a\<bullet>M(vs) : T"
    by(cases U)(auto 4 4 simp add: external_WT'_iff)
  from red_external_wt_hconf_hext[OF wf \<open>P,t \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>\<close> \<open>H \<unlhd> hp s\<close> this tconf hconf]
    wta icto sees \<open>ta' = convert_extTA extNTA ta\<close> \<open>e' = extRet2J (addr a\<bullet>M(map Val vs)) va\<close> \<open>s' = (h', lcl s)\<close>
  show ?case by(cases U)(auto 4 5 intro: red_reds.RedCallExternal simp del: split_paired_Ex)
next
  case RedCallNull thus ?case by(fastforce intro: red_reds.intros)
next
  case (BlockRed e h l V vo ta e' h' l' T E T')
  note IH = BlockRed.hyps(2)
  from IH[of "E(V \<mapsto> T)" T'] \<open>P,E,H \<turnstile> {V:T=vo; e} : T'\<close> \<open>hext H (hp (h, l))\<close>
  show ?case by(fastforce dest: red_reds.BlockRed)
next
  case RedBlock thus ?case by(fastforce intro: red_reds.intros)
next
  case SynchronizedRed1 thus ?case by(fastforce intro: red_reds.intros)
next
  case SynchronizedNull thus ?case by(fastforce intro: red_reds.intros)
next
  case LockSynchronized thus ?case by(fastforce intro: red_reds.intros)
next
  case SynchronizedRed2 thus ?case by(fastforce intro: red_reds.intros)
next
  case UnlockSynchronized thus ?case by(fastforce intro: red_reds.intros)
next
  case SeqRed thus ?case by(fastforce intro: red_reds.intros)
next
  case RedSeq thus ?case by(fastforce intro: red_reds.intros)
next
  case CondRed thus ?case by(fastforce intro: red_reds.intros)
next
  case RedCondT thus ?case by(fastforce intro: red_reds.intros)
next
  case RedCondF thus ?case by(fastforce intro: red_reds.intros)
next
  case RedWhile thus ?case by(fastforce intro: red_reds.intros)
next
  case ThrowRed thus ?case by(fastforce intro: red_reds.intros)
next
  case RedThrowNull thus ?case by(fastforce intro: red_reds.intros)
next
  case TryRed thus ?case by(fastforce intro: red_reds.intros)
next
  case RedTry thus ?case by(fastforce intro: red_reds.intros)
next
  case (RedTryCatch s a D C V e2 E T)
  from \<open>P,E,H \<turnstile> try Throw a catch(C V) e2 : T\<close>
  obtain T' where "P,E,H \<turnstile> addr a : T'" by auto
  with \<open>typeof_addr (hp s) a = \<lfloor>Class_type D\<rfloor>\<close> \<open>hext H (hp s)\<close>
  have Ha: "typeof_addr H a = \<lfloor>Class_type D\<rfloor>"
    by(auto dest: typeof_addr_hext_mono)
  with \<open>P \<turnstile> D \<preceq>\<^sup>* C\<close> show ?case
    by(fastforce intro: red_reds.RedTryCatch)
next
  case (RedTryFail s a D C V e2 E T)
  from \<open>P,E,H \<turnstile> try Throw a catch(C V) e2 : T\<close>
  obtain T' where "P,E,H \<turnstile> addr a : T'" by auto
  with \<open>typeof_addr (hp s) a = \<lfloor>Class_type D\<rfloor>\<close> \<open>hext H (hp s)\<close>
  have Ha: "typeof_addr H a = \<lfloor>Class_type D\<rfloor>" 
    by(auto dest: typeof_addr_hext_mono)
  with \<open>\<not> P \<turnstile> D \<preceq>\<^sup>* C\<close> show ?case
    by(fastforce intro: red_reds.RedTryFail)
next
  case ListRed1 thus ?case by(fastforce intro: red_reds.intros)
next
  case ListRed2 thus ?case by(fastforce intro: red_reds.intros)
next
  case NewArrayThrow thus ?case by(fastforce intro: red_reds.intros)
next
  case CastThrow thus ?case by(fastforce intro: red_reds.intros)
next
  case InstanceOfThrow thus ?case by(fastforce intro: red_reds.intros)
next
  case BinOpThrow1 thus ?case by(fastforce intro: red_reds.intros)
next
  case BinOpThrow2 thus ?case by(fastforce intro: red_reds.intros)
next
  case LAssThrow thus ?case by(fastforce intro: red_reds.intros)
next
  case AAccThrow1 thus ?case by(fastforce intro: red_reds.intros)
next
  case AAccThrow2 thus ?case by(fastforce intro: red_reds.intros)
next
  case AAssThrow1 thus ?case by(fastforce intro: red_reds.intros)
next
  case AAssThrow2 thus ?case by(fastforce intro: red_reds.intros)
next
  case AAssThrow3 thus ?case by(fastforce intro: red_reds.intros)
next
  case ALengthThrow thus ?case by(fastforce intro: red_reds.intros)
next
  case FAccThrow thus ?case by(fastforce intro: red_reds.intros)
next
  case FAssThrow1 thus ?case by(fastforce intro: red_reds.intros)
next 
  case FAssThrow2 thus ?case by(fastforce intro: red_reds.intros)
next
  case CASThrow thus ?case by(fastforce intro: red_reds.intros)
next
  case CASThrow2 thus ?case by(fastforce intro: red_reds.intros)
next
  case CASThrow3 thus ?case by(fastforce intro: red_reds.intros)
next
  case CallThrowObj thus ?case by(fastforce intro: red_reds.intros)
next
  case CallThrowParams thus ?case by(fastforce intro: red_reds.intros)
next
  case BlockThrow thus ?case by(fastforce intro: red_reds.intros)
next
  case SynchronizedThrow1 thus ?case by(fastforce intro: red_reds.intros)
next
  case SynchronizedThrow2 thus ?case by(fastforce intro: red_reds.intros)
next
  case SeqThrow thus ?case by(fastforce intro: red_reds.intros)
next
  case CondThrow thus ?case by(fastforce intro: red_reds.intros)
next
  case ThrowThrow thus ?case by(fastforce intro: red_reds.intros)
qed

lemma can_lock_devreserp:
  "\<lbrakk> wf_J_prog P; red_mthr.can_sync P t (e, l) h' L; P,E,h \<turnstile> e : T; P,h \<turnstile> t \<surd>t; hconf h; h \<unlhd> h' \<rbrakk> 
  \<Longrightarrow> red_mthr.can_sync P t (e, l) h L"
apply(erule red_mthr.can_syncE)
apply(clarsimp)
apply(drule red_wt_hconf_hext, assumption+)
 apply(simp)
apply(fastforce intro!: red_mthr.can_syncI)
done

end

context J_typesafe begin

lemma preserve_deadlocked:
  assumes wf: "wf_J_prog P"
  shows "preserve_deadlocked final_expr (mred P) convert_RA ({s. sync_es_ok (thr s) (shr s) \<and> lock_ok (locks s) (thr s)} \<inter> {s. \<exists>Es. sconf_type_ts_ok Es (thr s) (shr s)} \<inter> {s. def_ass_ts_ok (thr s) (shr s)})"
  (is "preserve_deadlocked _ _ _ ?wf_state")
proof(unfold_locales)
  show inv: "invariant3p (mredT P) ?wf_state"
    by(intro invariant3p_IntI invariant3p_sync_es_ok_lock_ok[OF wf] lifting_inv.invariant3p_ts_inv[OF lifting_inv_sconf_subject_ok[OF wf]] lifting_wf.invariant3p_ts_ok[OF lifting_wf_def_ass[OF wf]])
  
  fix s t' ta' s' t x ln
  assume wfs: "s \<in> ?wf_state" 
    and redT: "P \<turnstile> s -t'\<triangleright>ta'\<rightarrow> s'"
    and tst: "thr s t = \<lfloor>(x, ln)\<rfloor>" 
  from redT have hext: "shr s \<unlhd> shr s'" by(rule redT_hext_incr)
  
  from inv redT wfs have wfs': "s' \<in> ?wf_state" by(rule invariant3pD)
  from redT tst obtain x' ln' where ts't: "thr s' t= \<lfloor>(x', ln')\<rfloor>"
    by(cases "thr s' t")(cases s, cases s', auto dest: red_mthr.redT_thread_not_disappear)

  from wfs tst obtain E T where wt: "P,E,shr s \<turnstile> fst x : T" 
    and hconf: "hconf (shr s)"
    and da: "\<D> (fst x) \<lfloor>dom (snd x)\<rfloor>"
    and tconf: "P,shr s \<turnstile> t \<surd>t"
    by(force dest: ts_invD ts_okD simp add: type_ok_def sconf_def sconf_type_ok_def)
  from wt hext have wt': "P,E,shr s' \<turnstile> fst x : T" by(rule WTrt_hext_mono)
  from wfs' ts't have hconf': "hconf (shr s')" 
    by(auto dest: ts_invD simp add: type_ok_def sconf_def sconf_type_ok_def)

  {
    assume cs: "red_mthr.must_sync P t x (shr s)"
    from cs have "\<not> final (fst x)" by(auto elim!: red_mthr.must_syncE simp add: split_beta)

    from progress[OF wf_prog_wwf_prog[OF wf] hconf' wt' da this, of "extTA2J P" t]
    obtain e' h x' ta where "P,t \<turnstile> \<langle>fst x,(shr s', snd x)\<rangle> -ta\<rightarrow> \<langle>e', (h, x')\<rangle>" by auto
    with red_ta_satisfiable[OF this]
    show "red_mthr.must_sync P t x (shr s')"
      by-(rule red_mthr.must_syncI, fastforce simp add: split_beta)
  next
    fix LT
    assume "red_mthr.can_sync P t x (shr s') LT"
    with can_lock_devreserp[OF wf _ wt tconf hconf hext, of "snd x" LT]
    show "\<exists>LT'\<subseteq>LT. red_mthr.can_sync P t x (shr s) LT'" by auto
  }
qed

end

end
