(*  Title:      JinjaThreads/Compiler/J0Bisim.thy
    Author:     Andreas Lochbihler
*)

section \<open>Bisimulation proof for between source code small step semantics
  with and without callstacks for single threads\<close>

theory J0Bisim imports
  J0
  "../J/JWellForm"
  "../Common/ExternalCallWF"
begin

inductive wf_state :: "'addr expr \<times> 'addr expr list \<Rightarrow> bool"
  where
  "\<lbrakk> fvs (e # es) = {}; \<forall>e \<in> set es. is_call e \<rbrakk>
   \<Longrightarrow> wf_state (e, es)"

inductive bisim_red_red0 :: "('addr expr \<times> 'addr locals) \<times> 'heap \<Rightarrow> ('addr expr \<times> 'addr expr list) \<times> 'heap \<Rightarrow> bool"
  where
  "wf_state ees \<Longrightarrow> bisim_red_red0 ((collapse ees, Map.empty), h) (ees, h)"

abbreviation ta_bisim0 :: "('addr, 'thread_id, 'heap) J_thread_action \<Rightarrow> ('addr, 'thread_id, 'heap) J0_thread_action \<Rightarrow> bool"
where "ta_bisim0 \<equiv> ta_bisim (\<lambda>t. bisim_red_red0)"

lemma wf_state_iff [simp, code]:
  "wf_state (e, es) \<longleftrightarrow> fvs (e # es) = {} \<and> (\<forall>e \<in> set es. is_call e)"
by(simp add: wf_state.simps)

lemma bisim_red_red0I [intro]:
  "\<lbrakk> e' = collapse ees; xs = Map.empty; h' = h; wf_state ees \<rbrakk> \<Longrightarrow> bisim_red_red0 ((e', xs), h') (ees, h)"
by(simp add: bisim_red_red0.simps del: split_paired_Ex)

lemma bisim_red_red0_final0D:
  "\<lbrakk> bisim_red_red0 (x1, m1) (x2, m2); final_expr0 x2 \<rbrakk> \<Longrightarrow> final_expr x1"
by(erule bisim_red_red0.cases) auto

context J_heap_base begin

lemma red0_preserves_wf_state:
  assumes wf: "wwf_J_prog P"
  and red: "P,t \<turnstile>0 \<langle>e / es, h\<rangle> -ta\<rightarrow> \<langle>e' / es', h'\<rangle>"
  and wf_state: "wf_state (e, es)"
  shows "wf_state (e', es')"
using wf_state
proof(cases)
  assume "fvs (e # es) = {}" and icl: "\<forall>e \<in> set es. is_call e"
  hence fv: "fv e = {}" "fvs es = {}" by auto
  show ?thesis
  proof
    from red show "fvs (e' # es') = {}"
    proof cases
      case (red0Red xs')
      hence [simp]: "es' = es"
        and red: "extTA2J0 P,P,t \<turnstile> \<langle>e,(h, Map.empty)\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>" by auto
      from red_fv_subset[OF wf red] fv have "fv e' = {}" by auto
      with fv show ?thesis by simp
    next
      case (red0Call a M vs U Ts T pns body D)
      hence [simp]: "ta = \<epsilon>"
        "e' = blocks (this # pns) (Class D # Ts) (Addr a # vs) body"
        "es' = e # es" "h' = h"
        and sees: "P \<turnstile> class_type_of U sees M: Ts\<rightarrow>T = \<lfloor>(pns, body)\<rfloor> in D" by auto
      from sees_wf_mdecl[OF wf sees]
      have "fv body \<subseteq> insert this (set pns)" "length Ts = length pns" by(simp_all add: wf_mdecl_def)
      thus ?thesis using fv \<open>length vs = length pns\<close> by auto
    next
      case (red0Return E)
      with fv_inline_call[of e E] show ?thesis using fv by auto
    qed
  next
    from red icl show "\<forall>e\<in>set es'. is_call e"
      by cases(simp_all add: is_call_def)
  qed
qed

lemma new_thread_bisim0_extNTA2J_extNTA2J0:
  assumes wf: "wwf_J_prog P"
  and red: "P,t \<turnstile> \<langle>a'\<bullet>M'(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle>"
  and nt: "NewThread t' CMa m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  shows "bisim_red_red0 (extNTA2J P CMa, m) (extNTA2J0 P CMa, m)"
proof -
  obtain C M a where CMa [simp]: "CMa = (C, M, a)" by(cases CMa)
  from red nt have [simp]: "m = h'" by(rule red_ext_new_thread_heap)
  from red_external_new_thread_sees[OF wf red nt[unfolded CMa]]
  obtain T pns body D where h'a: "typeof_addr h' a = \<lfloor>Class_type C\<rfloor>"
    and sees: "P \<turnstile> C sees M: []\<rightarrow>T = \<lfloor>(pns, body)\<rfloor> in D" by auto
  from sees_wf_mdecl[OF wf sees] have "fv body \<subseteq> {this}" by(auto simp add: wf_mdecl_def)
  with red nt h'a sees show ?thesis by(fastforce simp add: is_call_def intro: bisim_red_red0.intros)
qed

lemma ta_bisim0_extNTA2J_extNTA2J0:
  "\<lbrakk> wwf_J_prog P; P,t \<turnstile> \<langle>a'\<bullet>M'(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle> \<rbrakk>
  \<Longrightarrow> ta_bisim0 (extTA2J P ta) (extTA2J0 P ta)"
apply(auto simp add: ta_bisim_def intro!: list_all2_all_nthI)
apply(case_tac "\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> ! n")
apply(simp_all)
apply(erule (1) new_thread_bisim0_extNTA2J_extNTA2J0)
apply(auto simp add: in_set_conv_nth)
done

lemma assumes wf: "wwf_J_prog P"
  shows red_red0_tabisim0:
  "P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> \<exists>ta'. extTA2J0 P,P,t \<turnstile> \<langle>e, s\<rangle> -ta'\<rightarrow> \<langle>e', s'\<rangle> \<and> ta_bisim0 ta ta'"
  and reds_reds0_tabisim0:
  "P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> \<exists>ta'. extTA2J0 P,P,t \<turnstile> \<langle>es, s\<rangle> [-ta'\<rightarrow>] \<langle>es', s'\<rangle> \<and> ta_bisim0 ta ta'"
proof(induct rule: red_reds.inducts)
  case (RedCallExternal s a T M Ts Tr D vs ta va h' ta' e' s')
  note red = \<open>P,t \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>\<close>
  note T = \<open>typeof_addr (hp s) a = \<lfloor>T\<rfloor>\<close>
  from T \<open>P \<turnstile> class_type_of T sees M: Ts\<rightarrow>Tr = Native in D\<close> red
  have "extTA2J0 P,P,t \<turnstile> \<langle>addr a\<bullet>M(map Val vs),s\<rangle> -extTA2J0 P ta\<rightarrow> \<langle>e',(h', lcl s)\<rangle>"
    by(rule red_reds.RedCallExternal)(simp_all add: \<open>e' = extRet2J (addr a\<bullet>M(map Val vs)) va\<close>)
  moreover from \<open>ta' = extTA2J P ta\<close> T red wf
  have "ta_bisim0 ta' (extTA2J0 P ta)" by(auto intro: ta_bisim0_extNTA2J_extNTA2J0)
  ultimately show ?case unfolding \<open>s' = (h', lcl s)\<close> by blast
next
  case RedTryFail thus ?case by(force intro: red_reds.RedTryFail)
qed(fastforce intro: red_reds.intros simp add: ta_bisim_def ta_upd_simps)+

lemma assumes wf: "wwf_J_prog P"
  shows red0_red_tabisim0:
  "extTA2J0 P,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> \<exists>ta'. P,t \<turnstile> \<langle>e, s\<rangle> -ta'\<rightarrow> \<langle>e', s'\<rangle> \<and> ta_bisim0 ta' ta"
  and reds0_reds_tabisim0:
  "extTA2J0 P,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> \<exists>ta'. P,t \<turnstile> \<langle>es, s\<rangle> [-ta'\<rightarrow>] \<langle>es', s'\<rangle> \<and> ta_bisim0 ta' ta"
proof(induct rule: red_reds.inducts)
  case (RedCallExternal s a T M Ts Tr D vs ta va h' ta' e' s')
  note red = \<open>P,t \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>\<close>
  note T = \<open>typeof_addr (hp s) a = \<lfloor>T\<rfloor>\<close>
  from T \<open>P \<turnstile> class_type_of T sees M: Ts\<rightarrow>Tr = Native in D\<close> red
  have "P,t \<turnstile> \<langle>addr a\<bullet>M(map Val vs),s\<rangle> -extTA2J P ta\<rightarrow> \<langle>e',(h', lcl s)\<rangle>"
    by(rule red_reds.RedCallExternal)(simp_all add: \<open>e' = extRet2J (addr a\<bullet>M(map Val vs)) va\<close>)
  moreover from \<open>ta' = extTA2J0 P ta\<close> T red wf
  have "ta_bisim0 (extTA2J P ta) ta'" by(auto intro: ta_bisim0_extNTA2J_extNTA2J0)
  ultimately show ?case unfolding \<open>s' = (h', lcl s)\<close> by blast
next
  case RedTryFail thus ?case by(force intro: red_reds.RedTryFail)
qed(fastforce intro: red_reds.intros simp add: ta_bisim_def ta_upd_simps)+

lemma red_inline_call_red:
  assumes red: "P,t \<turnstile> \<langle>e, (h, Map.empty)\<rangle> -ta\<rightarrow> \<langle>e', (h', Map.empty)\<rangle>"
  shows "call E = \<lfloor>aMvs\<rfloor> \<Longrightarrow> P,t \<turnstile> \<langle>inline_call e E, (h, x)\<rangle> -ta\<rightarrow> \<langle>inline_call e' E, (h', x)\<rangle>"
  (is "_ \<Longrightarrow> ?concl E x")

  and
  "calls Es = \<lfloor>aMvs\<rfloor> \<Longrightarrow> P,t \<turnstile> \<langle>inline_calls e Es, (h, x)\<rangle> [-ta\<rightarrow>] \<langle>inline_calls e' Es, (h', x)\<rangle>"
  (is "_ \<Longrightarrow> ?concls Es x")
proof(induct E and Es arbitrary: x and x rule: call.induct calls.induct)
  case (Call obj M pns x)
  note IHobj = \<open>\<And>x. call obj = \<lfloor>aMvs\<rfloor> \<Longrightarrow> ?concl obj x\<close>
  note IHpns = \<open>\<And>x. calls pns = \<lfloor>aMvs\<rfloor> \<Longrightarrow> ?concls pns x\<close>
  obtain a M' vs where [simp]: "aMvs = (a, M', vs)" by(cases aMvs, auto)
  from \<open>call (obj\<bullet>M(pns)) = \<lfloor>aMvs\<rfloor>\<close> have "call (obj\<bullet>M(pns)) = \<lfloor>(a, M', vs)\<rfloor>" by simp
  thus ?case
  proof(induct rule: call_callE)
    case CallObj
    with IHobj[of x] show ?case by(fastforce intro: red_reds.CallObj)
  next
    case (CallParams v'')
    with IHpns[of x] show ?case by(fastforce intro: red_reds.CallParams)
  next
    case Call
    from red_lcl_add[OF red, where ?l0.0=x]
    have "P,t \<turnstile> \<langle>e,(h, x)\<rangle> -ta\<rightarrow> \<langle>e', (h', x)\<rangle>" by simp
    with Call show ?case by(fastforce dest: BlockRed)
  qed
next
  case (Block V T' vo exp x)
  note IH = \<open>\<And>x. call exp = \<lfloor>aMvs\<rfloor> \<Longrightarrow> ?concl exp x\<close>
  from IH[of "x(V := vo)"] \<open>call {V:T'=vo; exp} = \<lfloor>aMvs\<rfloor>\<close>
  show ?case by(clarsimp simp del: fun_upd_apply)(drule BlockRed, auto)
next
  case (Cons_exp exp exps x)
  show ?case
  proof(cases "is_val exp")
    case True
    with \<open>calls (exp # exps) = \<lfloor>aMvs\<rfloor>\<close> have "calls exps = \<lfloor>aMvs\<rfloor>" by auto
    with \<open>calls exps = \<lfloor>aMvs\<rfloor> \<Longrightarrow> ?concls exps x\<close> True
    show ?thesis by(fastforce intro: ListRed2)
  next
    case False
    with \<open>calls (exp # exps) = \<lfloor>aMvs\<rfloor>\<close> have "call exp = \<lfloor>aMvs\<rfloor>" by auto
    with \<open>call exp = \<lfloor>aMvs\<rfloor> \<Longrightarrow> ?concl exp x\<close>
    show ?thesis by(fastforce intro: ListRed1)
  qed
qed(fastforce intro: red_reds.intros)+

lemma 
  assumes "P \<turnstile> class_type_of T sees M:Us\<rightarrow>U = \<lfloor>(pns, body)\<rfloor> in D" "length vs = length pns" "length Us = length pns"
  shows is_call_red_inline_call:
  "\<lbrakk> call e = \<lfloor>(a, M, vs)\<rfloor>; typeof_addr (hp s) a = \<lfloor>T\<rfloor> \<rbrakk> 
  \<Longrightarrow> P,t \<turnstile> \<langle>e, s\<rangle> -\<epsilon>\<rightarrow> \<langle>inline_call (blocks (this # pns) (Class D # Us) (Addr a # vs) body) e, s\<rangle>"
  (is "_ \<Longrightarrow> _ \<Longrightarrow> ?red e s")
  and is_calls_reds_inline_calls:
  "\<lbrakk> calls es = \<lfloor>(a, M, vs)\<rfloor>; typeof_addr (hp s) a = \<lfloor>T\<rfloor> \<rbrakk> 
  \<Longrightarrow> P,t \<turnstile> \<langle>es, s\<rangle> [-\<epsilon>\<rightarrow>] \<langle>inline_calls (blocks (this # pns) (Class D # Us) (Addr a # vs) body) es, s\<rangle>"
  (is "_ \<Longrightarrow> _ \<Longrightarrow> ?reds es s")
proof(induct e and es arbitrary: s and s rule: call.induct calls.induct)
  case (Call obj M' params s)
  note IHObj = \<open>\<And>s. \<lbrakk>call obj = \<lfloor>(a, M, vs)\<rfloor>; typeof_addr (hp s) a = \<lfloor>T\<rfloor> \<rbrakk> \<Longrightarrow> ?red obj s\<close>
  note IHParams = \<open>\<And>s. \<lbrakk> calls params = \<lfloor>(a, M, vs)\<rfloor>; typeof_addr (hp s) a = \<lfloor>T\<rfloor> \<rbrakk> \<Longrightarrow> ?reds params s\<close>
  from \<open>call (obj\<bullet>M'(params)) = \<lfloor>(a, M, vs)\<rfloor>\<close>
  show ?case
  proof(induct rule: call_callE)
    case CallObj
    from IHObj[OF CallObj] \<open>typeof_addr (hp s) a = \<lfloor>T\<rfloor>\<close> have "?red obj s" by blast
    moreover from CallObj have "\<not> is_val obj" by auto
    ultimately show ?case by(auto intro: red_reds.CallObj)
  next
    case (CallParams v)
    from IHParams[OF \<open>calls params = \<lfloor>(a, M, vs)\<rfloor>\<close>] \<open>typeof_addr (hp s) a = \<lfloor>T\<rfloor>\<close>
    have "?reds params s" by blast
    moreover from CallParams have "\<not> is_vals params" by auto
    ultimately show ?case using \<open>obj = Val v\<close> by(auto intro: red_reds.CallParams)
  next
    case Call
    with RedCall[where s=s, simplified, OF \<open>typeof_addr (hp s) a = \<lfloor>T\<rfloor>\<close> \<open>P \<turnstile> class_type_of T sees M:Us\<rightarrow>U = \<lfloor>(pns, body)\<rfloor> in D\<close> \<open>length vs = length pns\<close> \<open>length Us = length pns\<close>] 
    show ?thesis by(simp)
  qed
next
  case (Block V ty vo exp s)
  note IH = \<open>\<And>s. \<lbrakk>call exp = \<lfloor>(a, M, vs)\<rfloor>; typeof_addr (hp s) a = \<lfloor>T\<rfloor> \<rbrakk> \<Longrightarrow> ?red exp s\<close>
  from \<open>call {V:ty=vo; exp} = \<lfloor>(a, M, vs)\<rfloor>\<close> IH[of "(hp s, (lcl s)(V := vo))"] \<open>typeof_addr (hp s) a = \<lfloor>T\<rfloor>\<close>
  show ?case by(cases s, simp del: fun_upd_apply)(drule red_reds.BlockRed, simp)
qed(fastforce intro: red_reds.intros)+

lemma red_inline_call_red':
  assumes fv: "fv ee = {}"
  and eefin: "\<not> final ee"
  shows "\<lbrakk> call E = \<lfloor>aMvs\<rfloor>; P,t \<turnstile> \<langle>inline_call ee E, (h, x)\<rangle> -ta\<rightarrow> \<langle>E', (h', x')\<rangle> \<rbrakk> 
         \<Longrightarrow> \<exists>ee'. E' = inline_call ee' E \<and> P,t \<turnstile> \<langle>ee, (h, Map.empty)\<rangle> -ta\<rightarrow> \<langle>ee', (h', Map.empty)\<rangle> \<and> x = x'"
  (is "\<lbrakk> _; _ \<rbrakk> \<Longrightarrow> ?concl E E' x x'")
  and   "\<lbrakk> calls Es = \<lfloor>aMvs\<rfloor>; P,t \<turnstile> \<langle>inline_calls ee Es, (h, x)\<rangle> [-ta\<rightarrow>] \<langle>Es', (h', x')\<rangle> \<rbrakk> 
         \<Longrightarrow> \<exists>ee'. Es' = inline_calls ee' Es \<and> P,t \<turnstile> \<langle>ee, (h, Map.empty)\<rangle> -ta\<rightarrow> \<langle>ee', (h', Map.empty)\<rangle> \<and> x = x'"
  (is "\<lbrakk> _; _ \<rbrakk> \<Longrightarrow> ?concls Es Es' x x'")
proof(induct E and Es arbitrary: E' x x' and Es' x x' rule: call.induct calls.induct)
  case new thus ?case by simp
next
  case (newArray T exp E' x x')
  thus ?case using eefin by(auto elim!: red_cases)
next
  case Cast thus ?case using eefin by(auto elim!:red_cases) 
next
  case InstanceOf thus ?case using eefin by(auto elim!:red_cases) 
next
  case Val thus ?case by simp
next
  case Var thus ?case by simp
next
  case LAss
  thus ?case using eefin by(auto elim!: red_cases)
next
  case BinOp
  thus ?case using eefin by(auto elim!: red_cases split: if_split_asm)
next
  case AAcc
  thus ?case using eefin by(auto elim!: red_cases split: if_split_asm)
next
  case AAss thus ?case using eefin by(auto elim!: red_cases split: if_split_asm)
next
  case ALen thus ?case using eefin by(auto elim!: red_cases split: if_split_asm)
next
  case FAcc thus ?case using eefin by(auto elim!: red_cases)
next
  case FAss thus ?case using eefin by(auto elim!: red_cases split: if_split_asm)
next
  case CompareAndSwap thus ?case using eefin by(auto elim!: red_cases split: if_split_asm)
next
  case (Call obj M pns E' x x')
  note IHobj = \<open>\<And>x E' x'. \<lbrakk>call obj = \<lfloor>aMvs\<rfloor>; P,t \<turnstile> \<langle>inline_call ee obj,(h, x)\<rangle> -ta\<rightarrow> \<langle>E',(h', x')\<rangle>\<rbrakk>
                \<Longrightarrow> ?concl obj E' x x'\<close>
  note IHpns = \<open>\<And>Es' x x'. \<lbrakk>calls pns = \<lfloor>aMvs\<rfloor>; P,t \<turnstile> \<langle>inline_calls ee pns,(h, x)\<rangle> [-ta\<rightarrow>] \<langle>Es',(h', x')\<rangle>\<rbrakk>
               \<Longrightarrow> ?concls pns Es' x x'\<close>
  note red = \<open>P,t \<turnstile> \<langle>inline_call ee (obj\<bullet>M(pns)),(h, x)\<rangle> -ta\<rightarrow>  \<langle>E',(h', x')\<rangle>\<close>
  obtain a M' vs where [simp]: "aMvs = (a, M', vs)" by(cases aMvs, auto)
  from \<open>call (obj\<bullet>M(pns)) = \<lfloor>aMvs\<rfloor>\<close> have "call (obj\<bullet>M(pns)) = \<lfloor>(a,M',vs)\<rfloor>" by simp
  thus ?case
  proof(cases rule: call_callE)
    case CallObj
    hence "\<not> is_val obj" by auto
    with red CallObj eefin obtain obj' where "E' = obj'\<bullet>M(pns)" 
      and red': "P,t \<turnstile> \<langle>inline_call ee obj,(h, x)\<rangle> -ta\<rightarrow> \<langle>obj',(h', x')\<rangle>"
      by(auto elim!: red_cases)
    from IHobj[OF _ red'] CallObj obtain ee' 
      where "inline_call ee' obj = obj'" "x = x'"
      and "P,t \<turnstile> \<langle>ee,(h, Map.empty)\<rangle> -ta\<rightarrow> \<langle>ee',(h', Map.empty)\<rangle>" by(auto simp del: fun_upd_apply)
    with \<open>E' = obj'\<bullet>M(pns)\<close> CallObj red' show ?thesis by(fastforce simp del: fun_upd_apply)
  next
    case (CallParams v'')
    hence "\<not> is_vals pns" by auto
    with red CallParams eefin obtain pns' where "E' = obj\<bullet>M(pns')" 
      and red': "P,t \<turnstile> \<langle>inline_calls ee pns,(h, x)\<rangle> [-ta\<rightarrow>] \<langle>pns',(h', x')\<rangle>"
      by(auto elim!: red_cases)
    from IHpns[OF _ red'] CallParams obtain ee' 
      where "inline_calls ee' pns = pns'" "x = x'"
      and "P,t \<turnstile> \<langle>ee,(h, Map.empty)\<rangle> -ta\<rightarrow> \<langle>ee',(h', Map.empty)\<rangle>"
      by(auto simp del: fun_upd_apply)
    with \<open>E' = obj\<bullet>M(pns')\<close> CallParams red' \<open>\<not> is_vals pns\<close>
    show ?thesis by(auto simp del: fun_upd_apply)
  next
    case Call
    with red have red': "P,t \<turnstile> \<langle>ee,(h, x)\<rangle> -ta\<rightarrow> \<langle>E',(h', x')\<rangle>" by(auto)
    from red_lcl_sub[OF red', of "{}"] fv
    have "P,t \<turnstile> \<langle>ee,(h, Map.empty)\<rangle> -ta\<rightarrow> \<langle>E',(h', Map.empty)\<rangle>" by simp
    moreover have "x' = x"
    proof(rule ext)
      fix V
      from red_notfree_unchanged[OF red', of V] fv
      show "x' V = x V" by simp
    qed
    ultimately show ?thesis using Call by simp
  qed
next
  case (Block V ty voo exp E' x x')
  note IH = \<open>\<And>x E' x'. \<lbrakk>call exp = \<lfloor>aMvs\<rfloor>; P,t \<turnstile> \<langle>inline_call ee exp,(h, x)\<rangle> -ta\<rightarrow> \<langle>E',(h', x')\<rangle>\<rbrakk>
            \<Longrightarrow> ?concl exp E' x x'\<close>
  from \<open>call {V:ty=voo; exp} = \<lfloor>aMvs\<rfloor>\<close> have ic: "call exp = \<lfloor>aMvs\<rfloor>" by simp
  note red = \<open>P,t \<turnstile> \<langle>inline_call ee {V:ty=voo; exp},(h, x)\<rangle> -ta\<rightarrow> \<langle>E',(h', x')\<rangle>\<close>
  hence "P,t \<turnstile> \<langle>{V:ty=voo; inline_call ee exp},(h, x)\<rangle> -ta\<rightarrow> \<langle>E',(h', x')\<rangle>" by simp
  with ic eefin obtain exp' x'' where "E' = {V:ty=x'' V; exp'}"
    and red': "P,t \<turnstile> \<langle>inline_call ee exp,(h, fun_upd x V voo)\<rangle> -ta\<rightarrow> \<langle>exp',(h', x'')\<rangle>"
    and "x' = fun_upd x'' V (x V)"
    by -(erule red.cases,auto dest: inline_call_eq_Val)
  from IH[OF ic red'] obtain ee' vo' 
    where icl: "inline_call ee' exp = exp'" "x'' = fun_upd x V voo"
    and red'': "P,t \<turnstile> \<langle>ee,(h, Map.empty)\<rangle> -ta\<rightarrow> \<langle>ee',(h', Map.empty)\<rangle>" by blast
  from \<open>x'' = fun_upd x V voo\<close> have "x'' V = voo" by(simp add: fun_eq_iff)
  with icl red'' \<open>E' = {V:ty=x'' V; exp'}\<close> \<open>x' = fun_upd x'' V (x V)\<close> red'
  show ?case by(auto simp del: fun_upd_apply)
next
  case Synchronized thus ?case using eefin by(auto elim!: red_cases)
next
  case InSynchronized thus ?case using eefin by(auto elim!: red_cases)
next
  case Seq 
  thus ?case using eefin by(auto elim!: red_cases)
next
  case Cond thus ?case using eefin by(auto elim!: red_cases)
next
  case While thus ?case by simp
next
  case throw
  thus ?case using eefin by(auto elim!: red_cases)
next
  case TryCatch
  thus ?case using eefin by(auto elim!: red_cases)
next
  case Nil_exp thus ?case by simp
next
  case Cons_exp
  thus ?case using eefin by(auto elim!: reds_cases split: if_split_asm)
qed

lemma assumes sees: "P \<turnstile> class_type_of T sees M:Us\<rightarrow>U = \<lfloor>(pns, body)\<rfloor> in D"
  shows is_call_red_inline_callD:
  "\<lbrakk> P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; call e = \<lfloor>(a, M, vs)\<rfloor>; typeof_addr (hp s) a = \<lfloor>T\<rfloor> \<rbrakk>
  \<Longrightarrow> e' = inline_call (blocks (this # pns) (Class D # Us) (Addr a # vs) body) e"
  and is_calls_reds_inline_callsD:
  "\<lbrakk> P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; calls es = \<lfloor>(a, M, vs)\<rfloor>; typeof_addr (hp s) a = \<lfloor>T\<rfloor> \<rbrakk>
  \<Longrightarrow> es' = inline_calls (blocks (this # pns) (Class D # Us) (Addr a # vs) body) es"
proof(induct rule: red_reds.inducts)
  case RedCall with sees show ?case by(auto dest: sees_method_fun)
next
  case RedCallExternal
  with sees show ?case by(auto dest: sees_method_fun)
next
  case (BlockRed e h x V vo ta e' h' x' T')
  from \<open>call {V:T'=vo; e} = \<lfloor>(a, M, vs)\<rfloor>\<close> \<open>typeof_addr (hp (h, x)) a = \<lfloor>T\<rfloor>\<close> sees
  have "call e = \<lfloor>(a, M, vs)\<rfloor>" and "\<not> synthesized_call P h (a, M, vs)"
    by(auto simp add: synthesized_call_conv dest: sees_method_fun)
  with \<open>P,t \<turnstile> \<langle>e,(h, x(V := vo))\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>\<close>
  have "x(V := vo) = x'" by(auto dest: is_call_red_state_unchanged)
  hence "x' V = vo" by auto
  with BlockRed show ?case by(simp)
qed(fastforce split: if_split_asm)+

lemma (in -) wf_state_ConsD: "wf_state (e, e' # es) \<Longrightarrow> wf_state (e', es)"
by(simp)

lemma red_fold_exs:
  "\<lbrakk> P,t \<turnstile> \<langle>e,(h, Map.empty)\<rangle> -ta\<rightarrow> \<langle>e',(h', Map.empty)\<rangle>; wf_state (e, es) \<rbrakk>
  \<Longrightarrow>  P,t \<turnstile> \<langle>collapse (e, es), (h, Map.empty)\<rangle> -ta\<rightarrow> \<langle>collapse (e', es), (h', Map.empty)\<rangle>"
  (is "\<lbrakk> _; _ \<rbrakk> \<Longrightarrow> ?concl e e' es")
proof(induction es arbitrary: e e')
  case Nil thus ?case by simp
next
  case (Cons E es)
  note wf = \<open>wf_state (e, E # es)\<close>
  note red = \<open>P,t \<turnstile> \<langle>e,(h, Map.empty)\<rangle> -ta\<rightarrow> \<langle>e',(h', Map.empty)\<rangle>\<close>
  from wf obtain a M vs arrobj where call: "call E = \<lfloor>(a, M, vs)\<rfloor>" 
    by(auto simp add: is_call_def)
  from red call have "P,t \<turnstile> \<langle>inline_call e E,(h, Map.empty)\<rangle> -ta\<rightarrow> \<langle>inline_call e' E,(h', Map.empty)\<rangle>"
    by(rule red_inline_call_red)
  hence "P,t \<turnstile> \<langle>collapse (inline_call e E, es),(h, Map.empty)\<rangle> -ta\<rightarrow>  \<langle>collapse (inline_call e' E, es),(h', Map.empty)\<rangle>"
  proof(rule Cons.IH)
    from wf have "fv E = {}" "fv e = {}" by auto
    with fv_inline_call[of e E] have "fv (inline_call e E) = {}" by auto
    thus "wf_state (inline_call e E, es)" using wf by auto
  qed
  thus ?case by simp
qed

lemma red_fold_exs':
  "\<lbrakk> P,t \<turnstile> \<langle>collapse (e, es), (h, Map.empty)\<rangle> -ta\<rightarrow> \<langle>e', (h', x')\<rangle>; wf_state (e, es); \<not> final e \<rbrakk>
  \<Longrightarrow> \<exists>E'. e' = collapse (E', es) \<and> P,t \<turnstile> \<langle>e, (h, Map.empty)\<rangle> -ta\<rightarrow> \<langle>E', (h', Map.empty)\<rangle>"
  (is "\<lbrakk> _; _; _ \<rbrakk> \<Longrightarrow> ?concl e es")
proof(induction es arbitrary: e)
  case Nil
  hence red': "P,t \<turnstile> \<langle>e,(h, Map.empty)\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>" by simp
  with red_dom_lcl[OF this] \<open>wf_state (e, [])\<close> show ?case by auto
next
  case (Cons E es)
  note wf = \<open>wf_state (e, E # es)\<close>
  note nfin = \<open>\<not> final e\<close>
  from wf have "fv e = {}" by simp
  from wf obtain a M vs where call: "call E = \<lfloor>(a, M, vs)\<rfloor>" by(auto simp add: is_call_def)
  from \<open>P,t \<turnstile> \<langle>collapse (e, E # es),(h, Map.empty)\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>\<close>
  have "P,t \<turnstile> \<langle>collapse (inline_call e E, es),(h, Map.empty)\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>" by simp
  moreover from wf fv_inline_call[of e E] have "wf_state (inline_call e E, es)" by auto
  moreover from nfin call have "\<not> final (inline_call e E)" by(auto elim!: final.cases)
  ultimately have "?concl (inline_call e E) es" by(rule Cons.IH)
  then obtain E' where e': "e' = collapse (E', es)" 
    and red': "P,t \<turnstile> \<langle>inline_call e E,(h, Map.empty)\<rangle> -ta\<rightarrow> \<langle>E',(h', Map.empty)\<rangle>" by blast
  from red_inline_call_red'(1)[OF \<open>fv e = {}\<close> nfin \<open>call E = \<lfloor>(a, M, vs)\<rfloor>\<close> red']
  obtain e' where "E' = inline_call e' E" "P,t \<turnstile> \<langle>e,(h, Map.empty)\<rangle> -ta\<rightarrow> \<langle>e',(h', Map.empty)\<rangle>" by auto
  thus ?case using e' by auto
qed

lemma \<tau>Red0r_inline_call_not_final:
  "\<exists>e' es'. \<tau>Red0r P t h (e, es) (e', es') \<and> (final e' \<longrightarrow> es' = []) \<and> collapse (e, es) = collapse (e', es')"
proof(induct es arbitrary: e)
  case Nil thus ?case by blast
next
  case (Cons e es E) show ?case
  proof(cases "final E")
    case True
    hence "\<tau>Red0 P t h (E, e # es) (inline_call E e, es)" by(auto intro: red0Return)
    moreover from Cons[of "inline_call E e"] obtain e' es'
      where "\<tau>Red0r P t h (inline_call E e, es) (e', es')" "final e' \<longrightarrow> es' = []"
      "collapse (inline_call E e, es) = collapse (e', es')" by blast
    ultimately show ?thesis unfolding collapse.simps by(blast intro: converse_rtranclp_into_rtranclp)
  qed blast
qed

lemma \<tau>Red0_preserves_wf_state:
  "\<lbrakk> wwf_J_prog P; \<tau>Red0 P t h (e, es) (e', es'); wf_state (e, es) \<rbrakk> \<Longrightarrow> wf_state (e', es')"
by(auto simp del: wf_state_iff intro: red0_preserves_wf_state)

lemma \<tau>Red0r_preserves_wf_state:
  assumes wf: "wwf_J_prog P"
  shows "\<lbrakk> \<tau>Red0r P t h (e, es) (e', es'); wf_state (e, es) \<rbrakk> \<Longrightarrow> wf_state (e', es')"
by(induct rule: rtranclp_induct2)(blast intro: \<tau>Red0_preserves_wf_state[OF wf])+

lemma \<tau>Red0t_preserves_wf_state:
  assumes wf: "wwf_J_prog P"
  shows "\<lbrakk> \<tau>Red0t P t h (e, es) (e', es'); wf_state (e, es) \<rbrakk> \<Longrightarrow> wf_state (e', es')"
by(induct rule: tranclp_induct2)(blast intro: \<tau>Red0_preserves_wf_state[OF wf])+

lemma collapse_\<tau>move0_inv:
  "\<lbrakk> \<forall>e\<in>set es. is_call e; \<not> final e \<rbrakk> \<Longrightarrow> \<tau>move0 P h (collapse (e, es)) = \<tau>move0 P h e"
proof(induction es arbitrary: e)
  case Nil thus ?case by clarsimp
next
  case (Cons e es e'')
  from \<open>\<forall>a\<in>set (e # es). is_call a\<close> obtain aMvs where calls: "\<forall>e\<in>set es. is_call e"
    and call: "call e = \<lfloor>aMvs\<rfloor>" by(auto simp add: is_call_def)
  note calls moreover
  from \<open>\<not> final e''\<close> call have "\<not> final (inline_call e'' e)" by(auto simp add: final_iff)
  ultimately have "\<tau>move0 P h (collapse (inline_call e'' e, es)) = \<tau>move0 P h (inline_call e'' e)"
    by(rule Cons.IH)
  also from call \<open>\<not> final e''\<close> have "\<dots> = \<tau>move0 P h e''" by(auto simp add: inline_call_\<tau>move0_inv)
  finally show ?case by simp
qed

lemma \<tau>Red0r_into_silent_moves:
  "\<tau>Red0r P t h (e, es) (e', es') \<Longrightarrow> red0_mthr.silent_moves P t ((e, es), h) ((e', es'), h)"
by(induct rule: rtranclp_induct2)(fastforce intro: \<tau>trsys.silent_move.intros elim!: rtranclp.rtrancl_into_rtrancl)+

lemma \<tau>Red0t_into_silent_movet:
  "\<tau>Red0t P t h (e, es) (e', es') \<Longrightarrow> red0_mthr.silent_movet P t ((e, es), h) ((e', es'), h)"
by(induct rule: tranclp_induct2)(fastforce intro: \<tau>trsys.silent_move.intros elim!: tranclp.trancl_into_trancl)+

lemma red_simulates_red0:
  assumes wwf: "wwf_J_prog P"
  and sim: "bisim_red_red0 s1 s2" "mred0 P t s2 ta2 s2'" "\<not> \<tau>MOVE0 P s2 ta2 s2'"
  shows "\<exists>s1' ta1. mred P t s1 ta1 s1' \<and> \<not> \<tau>MOVE P s1 ta1 s1' \<and> bisim_red_red0 s1' s2' \<and> ta_bisim0 ta1 ta2"
proof -
  note sim
  moreover obtain e1 h1 x1 where s1: "s1 = ((e1, x1), h1)" by(cases s1, auto)
  moreover obtain e' es' h2' where s2': "s2' = ((e', es'), h2')" by(cases s2', auto)
  moreover obtain e es h2 where s2: "s2 = ((e, es), h2)" by(cases s2, auto)
  ultimately have bisim: "bisim_red_red0 ((e1, x1), h1) ((e, es), h2)"
    and red: "P,t \<turnstile>0 \<langle>e/es, h2\<rangle> -ta2\<rightarrow> \<langle>e'/es', h2'\<rangle>" 
    and \<tau>: "\<not> \<tau>move0 P h2 e \<and> \<not> final e \<or> ta2 \<noteq> \<epsilon>" by auto
  from red \<tau> have \<tau>: "\<not> \<tau>move0 P h2 e" and nfin: "\<not> final e"
    by(cases, auto dest: red_\<tau>_taD[where extTA="extTA2J0 P", OF extTA2J0_\<epsilon>])+
  from bisim have heap: "h1 = h2" and fold: "e1 = collapse (e, es)"
    and x1: "x1 = Map.empty" and wf_state: "wf_state (e, es)"
    by(auto elim!: bisim_red_red0.cases)
  from red wf_state have wf_state': "wf_state (e', es')" by(rule red0_preserves_wf_state[OF wwf])
  from red show ?thesis
  proof(cases)
    case (red0Red xs')
    hence [simp]: "es' = es"
      and "extTA2J0 P,P,t \<turnstile> \<langle>e, (h2, Map.empty)\<rangle> -ta2\<rightarrow> \<langle>e', (h2', xs')\<rangle>" by auto
    from red0_red_tabisim0[OF wwf this(2)] obtain ta1
      where red': "P,t \<turnstile> \<langle>e,(h2, Map.empty)\<rangle> -ta1\<rightarrow> \<langle>e',(h2', xs')\<rangle>"
      and tasim: "ta_bisim0 ta1 ta2" by auto
    moreover from wf_state have "fv e = {}" by auto
    with red_dom_lcl[OF red'] red_fv_subset[OF wwf red'] have "xs' = Map.empty" by auto
    ultimately have "P,t \<turnstile> \<langle>e,(h2, Map.empty)\<rangle> -ta1\<rightarrow> \<langle>e',(h2', Map.empty)\<rangle>" by simp
    with wf_state have "P,t \<turnstile> \<langle>collapse (e, es),(h2, Map.empty)\<rangle> -ta1\<rightarrow> \<langle>collapse (e', es),(h2', Map.empty)\<rangle>"
      by -(erule red_fold_exs, auto)
    moreover from \<tau> wf_state fold nfin have "\<not> \<tau>move0 P h2 e1" by(auto simp add: collapse_\<tau>move0_inv)
    hence "\<not> \<tau>MOVE P ((collapse (e, es), Map.empty), h2) ta1 ((collapse (e', es), Map.empty), h2')"
      unfolding fold by auto
    moreover from wf_state' have "bisim_red_red0 ((collapse (e', es), Map.empty), h2') s2'" 
      unfolding s2' by(auto)
    ultimately show ?thesis unfolding heap s1 s2 s2' fold x1
      using tasim by(fastforce intro!: exI rtranclp.rtrancl_refl)
  next
    case red0Call
    with \<tau> have False
      by(auto simp add: synthesized_call_def \<tau>external'_def dest!: \<tau>move0_callD[where P=P and h=h2] dest: sees_method_fun)
    thus ?thesis ..
  next
    case red0Return with nfin show ?thesis by simp
  qed
qed

lemma delay_bisimulation_measure_red_red0:
  assumes wf: "wwf_J_prog P"
  shows "delay_bisimulation_measure (mred P t) (mred0 P t) bisim_red_red0 ta_bisim0 (\<tau>MOVE P) (\<tau>MOVE0 P) (\<lambda>e e'. False) (\<lambda>((e, es), h) ((e, es'), h). length es < length es')"
proof
  show "wfP (\<lambda>e e'. False)" by auto
next
  have "wf {(x :: nat, y). x < y}" by(rule wf_less)
  hence "wf (inv_image {(x :: nat, y). x < y} (length o snd o fst))" by(rule wf_inv_image)
  also have "inv_image {(x :: nat, y). x < y} (length o snd o fst) = {(x, y). (\<lambda>((e, es), h) ((e, es'), h). length es < length es') x y}" by auto
  finally show "wfP (\<lambda>((e, es), h) ((e, es'), h). length es < length es')"
    unfolding wfP_def .
next
  fix s1 s2 s1'
  assume "bisim_red_red0 s1 s2" and "red_mthr.silent_move P t s1 s1'"
  moreover obtain e1 h1 x1 where s1: "s1 = ((e1, x1), h1)" by(cases s1, auto)
  moreover obtain e1' h1' x1' where s1': "s1' = ((e1', x1'), h1')" by(cases s1', auto)
  moreover obtain e es h2 where s2: "s2 = ((e, es), h2)" by(cases s2, auto)
  ultimately have bisim: "bisim_red_red0 ((e1, x1), h1) ((e, es), h2)"
    and red: "P,t \<turnstile> \<langle>e1, (h1, x1)\<rangle> -\<epsilon>\<rightarrow> \<langle>e1', (h1', x1')\<rangle>" 
    and \<tau>: "\<tau>move0 P h1 e1" by(auto elim: \<tau>trsys.silent_move.cases)
  from bisim have heap: "h1 = h2"
    and fold: "e1 = collapse (e, es)"
    and x1: "x1 = Map.empty"
    and wf_state: "wf_state (e, es)"
    by(auto elim!: bisim_red_red0.cases)
  from \<tau>Red0r_inline_call_not_final[of P t h1 e es]
  obtain e' es' where red1: "\<tau>Red0r P t h1 (e, es) (e', es')"
    and "final e' \<Longrightarrow> es' = []" 
    and feq: "collapse (e, es) = collapse (e', es')" by blast
  have nfin: "\<not> final e'"
  proof
    assume fin: "final e'"
    hence "es' = []" by(rule \<open>final e' \<Longrightarrow> es' = []\<close>)
    with fold fin feq have "final e1" by simp
    with red show False by auto
  qed
  from red1 wf_state have wf_state': "wf_state (e', es')" by(rule \<tau>Red0r_preserves_wf_state[OF wf])
  hence fv: "fvs (e' # es') = {}" and icl: "\<forall>e\<in>set es'. is_call e" by auto
  from red_fold_exs'[OF red[unfolded fold x1 feq] wf_state' nfin]
  obtain E' where e1': "e1' = collapse (E', es')" 
    and red': "P,t \<turnstile> \<langle>e',(h1, Map.empty)\<rangle> -\<epsilon>\<rightarrow> \<langle>E',(h1', Map.empty)\<rangle>" by auto
  from fv fv_collapse[of es e] wf_state fold feq have "fv e1 = {}" by(auto)
  with red_dom_lcl[OF red] x1 have x1': "x1' = Map.empty" by simp
  from red_red0_tabisim0[OF wf red']
  have red'': "extTA2J0 P,P,t \<turnstile> \<langle>e',(h1, Map.empty)\<rangle> -\<epsilon>\<rightarrow> \<langle>E',(h1', Map.empty)\<rangle>" by simp
  show "bisim_red_red0 s1' s2 \<and> (\<lambda>e e'. False)^++ s1' s1 \<or>
        (\<exists>s2'. red0_mthr.silent_movet P t s2 s2' \<and> bisim_red_red0 s1' s2')"
  proof(cases "no_call P h1 e'")
    case True
    with red'' have "P,t \<turnstile>0 \<langle>e'/es', h1\<rangle> -\<epsilon>\<rightarrow> \<langle>E'/es', h1'\<rangle>" unfolding no_call_def by(rule red0Red)
    moreover from red \<tau> have [simp]: "h1' = h1" by(auto dest: \<tau>move0_heap_unchanged)
    moreover from \<tau> fold feq icl nfin have "\<tau>move0 P h1 e'" by(simp add: collapse_\<tau>move0_inv)
    ultimately have "\<tau>Red0 P t h1 (e', es') (E', es')" using \<open>\<tau>move0 P h1 e'\<close> by auto
    with red1 have "\<tau>Red0t P t h1 (e, es) (E', es')" by(rule rtranclp_into_tranclp1)
    moreover hence "wf_state (E', es')" using wf_state by(rule \<tau>Red0t_preserves_wf_state[OF wf])
    hence "bisim_red_red0 ((e1', x1'), h1) ((E', es'), h1)" unfolding x1' e1' by(auto)
    ultimately show ?thesis using s1 s1' s2 heap by simp(blast intro:  \<tau>Red0t_into_silent_movet)
  next
    case False
    then obtain a M vs where call: "call e' = \<lfloor>(a, M, vs)\<rfloor>"
      and notsynth: "\<not> synthesized_call P h1 (a, M, vs)" by(auto simp add: no_call_def)
    from notsynth called_methodD[OF red'' call] obtain T D Us U pns body
      where "h1' = h1"
      and ha: "typeof_addr h1 a = \<lfloor>T\<rfloor>"
      and sees: "P \<turnstile> class_type_of T sees M: Us\<rightarrow>U = \<lfloor>(pns, body)\<rfloor> in D"
      and length: "length vs = length pns" "length Us = length pns"
      by(auto)
    let ?e = "blocks (this # pns) (Class D # Us) (Addr a # vs) body"
    from call ha have "P,t \<turnstile>0 \<langle>e'/es',h1\<rangle> -\<epsilon>\<rightarrow> \<langle>?e/e' # es',h1\<rangle>"
      using sees length by(rule red0Call)
    moreover from \<tau> fold feq icl nfin False have "\<tau>move0 P h1 e'" by(simp add: collapse_\<tau>move0_inv)
    ultimately have "\<tau>Red0 P t h1 (e', es') (?e, e' # es')" by auto
    with red1 have "\<tau>Red0t P t h1 (e, es) (?e, e' # es')" by(rule rtranclp_into_tranclp1)
    moreover {
      from \<open>P,t \<turnstile>0 \<langle>e'/es',h1\<rangle> -\<epsilon>\<rightarrow> \<langle>?e/e' # es',h1\<rangle>\<close> have "wf_state (?e, e' # es')"
        using wf_state' by(rule red0_preserves_wf_state[OF wf])
      moreover from is_call_red_inline_callD[OF sees red' call] ha
      have "E' = inline_call ?e e'" by auto
      ultimately have "bisim_red_red0 s1' ((?e, e' # es'), h1')" unfolding s1' e1' x1'
        by(auto del: wf_state.cases wf_state.intros) }
    moreover from red' call notsynth have "h1 = h1'"
      by(auto dest: is_call_red_state_unchanged)
    ultimately show ?thesis unfolding heap x1' x1 s2 s1' \<open>h1' = h1\<close>
      by(blast intro: \<tau>Red0t_into_silent_movet)
  qed
next
  fix s1 s2 s2'
  assume "bisim_red_red0 s1 s2" and "red0_mthr.silent_move P t s2 s2'"
  moreover obtain e1 h1 x1 where s1: "s1 = ((e1, x1), h1)" by(cases s1, auto)
  moreover obtain e' es' h2' where s2': "s2' = ((e', es'), h2')" by(cases s2', auto)
  moreover obtain e es h2 where s2: "s2 = ((e, es), h2)" by(cases s2, auto)
  ultimately have bisim: "bisim_red_red0 ((e1, x1), h1) ((e, es), h2)"
    and red: "P,t \<turnstile>0 \<langle>e/es, h2\<rangle> -\<epsilon>\<rightarrow> \<langle>e'/es', h2'\<rangle>" 
    and \<tau>: "\<tau>move0 P h2 e \<or> final e" by(auto elim: \<tau>trsys.silent_move.cases)
  from bisim have heap: "h1 = h2"
    and fold: "e1 = collapse (e, es)"
    and x1: "x1 = Map.empty" and wf_state: "wf_state (e, es)"
    by(auto elim!: bisim_red_red0.cases)
  from red wf_state have wf_state': "wf_state (e', es')" by(rule red0_preserves_wf_state[OF wf])
  from red show "bisim_red_red0 s1 s2' \<and> (\<lambda>((e, es), h) ((e, es'), h). length es < length es')\<^sup>+\<^sup>+ s2' s2 \<or>
        (\<exists>s1'. red_mthr.silent_movet P t s1 s1' \<and> bisim_red_red0 s1' s2')"
  proof cases
    case (red0Red xs')
    hence [simp]: "es' = es"
      and "extTA2J0 P,P,t \<turnstile> \<langle>e, (h2, Map.empty)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h2', xs')\<rangle>" by auto
    from red0_red_tabisim0[OF wf this(2)] have red': "P,t \<turnstile> \<langle>e,(h2, Map.empty)\<rangle> -\<epsilon>\<rightarrow> \<langle>e',(h2', xs')\<rangle>" by auto
    moreover from wf_state have "fv e = {}" by auto
    with red_dom_lcl[OF red'] red_fv_subset[OF wf red'] have "xs' = Map.empty" by auto
    ultimately have "P,t \<turnstile> \<langle>e,(h2, Map.empty)\<rangle> -\<epsilon>\<rightarrow> \<langle>e',(h2', Map.empty)\<rangle>" by simp
    hence "P,t \<turnstile> \<langle>collapse (e, es),(h2, Map.empty)\<rangle> -\<epsilon>\<rightarrow> \<langle>collapse (e', es),(h2', Map.empty)\<rangle>" 
      using wf_state by(rule red_fold_exs)
    moreover from red' have "\<not> final e" by auto
    with \<tau> wf_state fold have "\<tau>move0 P h2 e1" by(auto simp add: collapse_\<tau>move0_inv)
    ultimately have "red_mthr.silent_movet P t s1 ((collapse (e', es), Map.empty), h2')"
      using s1 fold \<tau> x1 heap by(auto intro: \<tau>trsys.silent_move.intros)
    moreover from wf_state' have "bisim_red_red0 ((collapse (e', es), Map.empty), h2') s2'"
      unfolding s2' by(auto)
    ultimately show ?thesis by blast
  next
    case (red0Call a M vs U Ts T pns body D)
    hence [simp]: "es' = e # es" "h2' = h2" "e' = blocks (this # pns) (Class D # Ts) (Addr a # vs) body"
      and call: "call e = \<lfloor>(a, M, vs)\<rfloor>"
      and ha: "typeof_addr h2 a = \<lfloor>U\<rfloor>"
      and sees: "P \<turnstile> class_type_of U sees M: Ts\<rightarrow>T = \<lfloor>(pns, body)\<rfloor> in D"
      and len: "length vs = length pns" "length Ts = length pns" by auto
    from is_call_red_inline_call(1)[OF sees len call, of "(h2, Map.empty)"] ha
    have "P,t \<turnstile> \<langle>e,(h2, Map.empty)\<rangle> -\<epsilon>\<rightarrow> \<langle>inline_call e' e, (h2, Map.empty)\<rangle>" by simp
    hence "P,t \<turnstile> \<langle>collapse (e, es), (h2, Map.empty)\<rangle> -\<epsilon>\<rightarrow> \<langle>collapse (inline_call e' e, es), (h2, Map.empty)\<rangle>"
      using wf_state by(rule red_fold_exs)
    moreover from call ha wf_state \<tau> have "\<tau>move0 P h2 (collapse (e, es))"
      by(subst collapse_\<tau>move0_inv) auto
    hence "\<tau>MOVE P ((collapse (e, es), Map.empty), h2) \<epsilon> ((collapse (inline_call e' e, es), Map.empty), h2)" by auto
    moreover from wf_state'
    have "bisim_red_red0 ((collapse (inline_call e' e, es), Map.empty), h2) ((e', es'), h2')"
      by(auto)
    ultimately show ?thesis unfolding s1 s2 s2' fold heap x1 by(fastforce)
  next
    case (red0Return E)
    hence [simp]: "es = E # es'" "e' = inline_call e E" "h2' = h2" by auto
    from fold wf_state'
    have "bisim_red_red0 ((e1, Map.empty), h1) ((inline_call e E, es'), h2)"
      unfolding heap by(auto)
    thus ?thesis using s1 s2' s2 x1 by auto
  qed
next
  fix s1 s2 ta1 s1'
  assume "bisim_red_red0 s1 s2" and "mred P t s1 ta1 s1'" and "\<not> \<tau>MOVE P s1 ta1 s1'"
  moreover obtain e1 h1 x1 where s1: "s1 = ((e1, x1), h1)" by(cases s1, auto)
  moreover obtain e1' h1' x1' where s1': "s1' = ((e1', x1'), h1')" by(cases s1', auto)
  moreover obtain e es h2 where s2: "s2 = ((e, es), h2)" by(cases s2, auto)
  ultimately have bisim: "bisim_red_red0 ((e1, x1), h1) ((e, es), h2)"
    and red: "P,t \<turnstile> \<langle>e1, (h1, x1)\<rangle> -ta1\<rightarrow> \<langle>e1', (h1', x1')\<rangle>" 
    and \<tau>: "\<not> \<tau>move0 P h1 e1" by(auto dest: red_\<tau>_taD[where extTA="extTA2J P", OF extTA2J_\<epsilon>])
  from bisim have heap: "h1 = h2"
    and fold: "e1 = collapse (e, es)"
    and x1: "x1 = Map.empty"
    and wf_state: "wf_state (e, es)"
    by(auto elim!: bisim_red_red0.cases)
  from \<tau>Red0r_inline_call_not_final[of P t h1 e es]
  obtain e' es' where red1: "\<tau>Red0r P t h1 (e, es) (e', es')"
    and "final e' \<Longrightarrow> es' = []" and feq: "collapse (e, es) = collapse (e', es')" by blast
  hence red1': "red0_mthr.silent_moves P t ((e, es), h2) ((e', es'), h2)"
    unfolding heap by -(rule \<tau>Red0r_into_silent_moves)
  have nfin: "\<not> final e'"
  proof
    assume fin: "final e'"
    hence "es' = []" by(rule \<open>final e' \<Longrightarrow> es' = []\<close>)
    with fold fin feq have "final e1" by simp
    with red show False by auto
  qed
  from red1 wf_state have wf_state': "wf_state (e', es')" by(rule \<tau>Red0r_preserves_wf_state[OF wf])
  hence fv: "fvs (e' # es') = {}" and icl: "\<forall>e \<in> set es'. is_call e" by auto
  from red_fold_exs'[OF red[unfolded fold x1 feq] wf_state' nfin]
  obtain E' where e1': "e1' = collapse (E', es')" 
    and red': "P,t \<turnstile> \<langle>e',(h1, Map.empty)\<rangle> -ta1\<rightarrow> \<langle>E',(h1', Map.empty)\<rangle>" by auto
  from fv fv_collapse[OF icl, of e'] fold feq have "fv e1 = {}" by(auto)
  with red_dom_lcl[OF red] x1 have x1': "x1' = Map.empty" by simp
  from red_red0_tabisim0[OF wf red'] obtain ta2
    where red'': "extTA2J0 P,P,t \<turnstile> \<langle>e',(h1, Map.empty)\<rangle> -ta2\<rightarrow> \<langle>E',(h1', Map.empty)\<rangle>"
    and tasim: "ta_bisim0 ta1 ta2" by auto
  from \<tau> fold feq icl nfin have "\<not> \<tau>move0 P h1 e'" by(simp add: collapse_\<tau>move0_inv)
  hence "\<forall>aMvs. call e' = \<lfloor>aMvs\<rfloor> \<longrightarrow> synthesized_call P h1 aMvs"
    by(auto dest: \<tau>move0_callD)
  with red'' have red''': "P,t \<turnstile>0 \<langle>e'/es', h1\<rangle> -ta2\<rightarrow> \<langle>E'/es', h1'\<rangle>" by(rule red0Red)
  moreover from \<tau> fold feq icl nfin have "\<not> \<tau>move0 P h1 e'" by(simp add: collapse_\<tau>move0_inv)
  hence "\<not> \<tau>MOVE0 P ((e', es'), h1) ta2 ((E', es'), h1')" using nfin by auto
  moreover from red''' wf_state' have "wf_state (E', es')" by(rule red0_preserves_wf_state[OF wf])
  hence "bisim_red_red0 s1' ((E', es'), h1')" unfolding s1' e1' x1' by(auto)
  ultimately show "\<exists>s2' s2'' ta2. red0_mthr.silent_moves P t s2 s2' \<and> mred0 P t s2' ta2 s2'' \<and>
                       \<not> \<tau>MOVE0 P s2' ta2 s2'' \<and> bisim_red_red0 s1' s2'' \<and> ta_bisim0 ta1 ta2"
    using tasim red1' heap unfolding s1' s2 by -(rule exI conjI|assumption|auto)+
next
  fix s1 s2 ta2 s2'
  assume "bisim_red_red0 s1 s2" and "mred0 P t s2 ta2 s2'" "\<not> \<tau>MOVE0 P s2 ta2 s2'"
  from red_simulates_red0[OF wf this]
  show "\<exists>s1' s1'' ta1. red_mthr.silent_moves P t s1 s1' \<and> mred P t s1' ta1 s1'' \<and>
                       \<not> \<tau>MOVE P s1' ta1 s1'' \<and> bisim_red_red0 s1'' s2' \<and> ta_bisim0 ta1 ta2"
    by(blast intro: rtranclp.rtrancl_refl)
qed

lemma delay_bisimulation_diverge_red_red0:
  assumes "wwf_J_prog P"
  shows "delay_bisimulation_diverge (mred P t) (mred0 P t) bisim_red_red0 ta_bisim0 (\<tau>MOVE P) (\<tau>MOVE0 P)"
proof -
  interpret delay_bisimulation_measure
    "mred P t" "mred0 P t" "bisim_red_red0" "ta_bisim0" "\<tau>MOVE P" "\<tau>MOVE0 P"
    "\<lambda>e e'. False" "\<lambda>((e, es), h) ((e, es'), h). length es < length es'"
    using assms by(rule delay_bisimulation_measure_red_red0)
  show ?thesis by unfold_locales
qed

lemma bisim_red_red0_finalD:
  assumes bisim: "bisim_red_red0 (x1, m1) (x2, m2)"
  and "final_expr x1"
  shows "\<exists>x2'. red0_mthr.silent_moves P t (x2, m2) (x2', m2) \<and> bisim_red_red0 (x1, m1) (x2', m2) \<and> final_expr0 x2'"
proof -
  from bisim
  obtain e' e es where wf_state: "wf_state (e, es)"
    and [simp]: "x1 = (e', Map.empty)" "x2 = (e, es)" "e' = collapse (e, es)" "m2 = m1"
    by cases(cases x2, auto)
  from \<open>final_expr x1\<close> have "final (collapse (e, es))" by simp
  moreover from wf_state have "\<forall>e\<in>set es. is_call e" by auto
  ultimately have "red0_mthr.silent_moves P t ((e, es), m1) ((collapse (e, es), []), m1)"
  proof(induction es arbitrary: e)
    case Nil thus ?case by simp
  next
    case (Cons e' es)
    from \<open>final (collapse (e, e' # es))\<close> have "final (collapse (inline_call e e', es))" by simp
    moreover from \<open>\<forall>e\<in>set (e' # es). is_call e\<close> have "\<forall>e\<in>set es. is_call e" by simp
    ultimately have "red0_mthr.silent_moves P t ((inline_call e e', es), m1) ((collapse (inline_call e e', es), []), m1)"
      by(rule Cons.IH)
    moreover from \<open>final (collapse (e, e' # es))\<close> \<open>\<forall>e\<in>set (e' # es). is_call e\<close>
    have "final e" by(rule collapse_finalD)
    hence "P,t \<turnstile>0 \<langle>e/e'#es, m1\<rangle> -\<epsilon>\<rightarrow> \<langle>inline_call e e'/es, m1\<rangle>" by(rule red0Return)
    with \<open>final e\<close> have "red0_mthr.silent_move P t ((e, e'#es), m1) ((inline_call e e', es), m1)" by auto
    ultimately show ?case by -(erule converse_rtranclp_into_rtranclp, simp)
  qed
  moreover have "bisim_red_red0 ((collapse (e, es), Map.empty), m1) ((collapse (e, es), []), m1)"
    using \<open>final (collapse (e, es))\<close> by(auto intro!: bisim_red_red0I)
  ultimately show ?thesis using \<open>final (collapse (e, es))\<close> by auto
qed

lemma red0_simulates_red_not_final:
  assumes wwf: "wwf_J_prog P"
  assumes bisim: "bisim_red_red0 ((e, xs), h) ((e0, es0), h0)"
  and red: "P,t \<turnstile> \<langle>e, (h, xs)\<rangle> -ta\<rightarrow> \<langle>e', (h', xs')\<rangle>"
  and fin: "\<not> final e0"
  and n\<tau>: "\<not> \<tau>move0 P h e"
  shows "\<exists>e0' ta0. P,t \<turnstile>0 \<langle>e0/es0, h\<rangle> -ta0\<rightarrow> \<langle>e0'/es0, h'\<rangle> \<and> bisim_red_red0 ((e', xs'), h') ((e0', es0), h') \<and> ta_bisim0 ta ta0"
proof -
  from bisim have [simp]: "xs = Map.empty" "h0 = h" and e: "e = collapse (e0, es0)"
    and wfs: "wf_state (e0, es0)" by(auto elim!: bisim_red_red0.cases)
  with red have "P,t \<turnstile> \<langle>collapse (e0, es0), (h, Map.empty)\<rangle> -ta\<rightarrow> \<langle>e', (h', xs')\<rangle>" by simp
  from wfs red_fold_exs'[OF this] fin obtain e0' where e': "e' = collapse (e0', es0)"
    and red': "P,t \<turnstile> \<langle>e0,(h, Map.empty)\<rangle> -ta\<rightarrow> \<langle>e0',(h', Map.empty)\<rangle>" by(auto)
  from wfs fv_collapse[of es0, of e0] e have "fv e = {}" by(auto)
  with red_dom_lcl[OF red] have [simp]: "xs' = Map.empty" by simp
  from red_red0_tabisim0[OF wwf red'] obtain ta0
    where red'': "extTA2J0 P,P,t \<turnstile> \<langle>e0,(h, Map.empty)\<rangle> -ta0\<rightarrow> \<langle>e0',(h', Map.empty)\<rangle>"
    and tasim: "ta_bisim0 ta ta0" by auto
  from n\<tau> e wfs fin have "\<not> \<tau>move0 P h e0" by(auto simp add: collapse_\<tau>move0_inv)
  hence "\<forall>aMvs. call e0 = \<lfloor>aMvs\<rfloor> \<longrightarrow> synthesized_call P h aMvs"
    by(auto dest: \<tau>move0_callD)
  with red'' have red''': "P,t \<turnstile>0 \<langle>e0/es0, h\<rangle> -ta0\<rightarrow> \<langle>e0'/es0, h'\<rangle>" by(rule red0Red)
  moreover from red''' wfs have "wf_state (e0', es0)" by(rule red0_preserves_wf_state[OF wwf])
  hence "bisim_red_red0 ((e', xs'), h') ((e0', es0), h')" unfolding e' by(auto)
  ultimately show ?thesis using tasim by(auto simp del: split_paired_Ex)
qed

lemma red_red0_FWbisim:
  assumes wf: "wwf_J_prog P"
  shows "FWdelay_bisimulation_diverge final_expr (mred P) final_expr0 (mred0 P)
                                      (\<lambda>t. bisim_red_red0) (\<lambda>exs (e0, es0). \<not> final e0) (\<tau>MOVE P) (\<tau>MOVE0 P)"
proof -
  interpret delay_bisimulation_diverge "mred P t" "mred0 P t" "bisim_red_red0" "ta_bisim0" "\<tau>MOVE P" "\<tau>MOVE0 P"
    for t by(rule delay_bisimulation_diverge_red_red0[OF wf])
  show ?thesis
  proof
    fix t and s1 :: "(('addr expr \<times> 'addr locals) \<times> 'heap)" and s2 :: "(('addr expr \<times> 'addr expr list) \<times> 'heap)"
    assume "bisim_red_red0 s1 s2" "(\<lambda>(x1, m). final_expr x1) s1"
    moreover obtain x1 m1 where [simp]: "s1 = (x1, m1)" by(cases s1)
    moreover obtain x2 m2 where [simp]: "s2 = (x2, m2)" by(cases s2)
    ultimately have "bisim_red_red0 (x1, m1) (x2, m2)" "final_expr x1" by simp_all
    from bisim_red_red0_finalD[OF this, of P t]
    show "\<exists>s2'. red0_mthr.silent_moves P t s2 s2' \<and> bisim_red_red0 s1 s2' \<and> (\<lambda>(x2, m). final_expr0 x2) s2'" by auto
  next
    fix t and s1 :: "(('addr expr \<times> 'addr locals) \<times> 'heap)" and s2 :: "(('addr expr \<times> 'addr expr list) \<times> 'heap)"
    assume "bisim_red_red0 s1 s2" "(\<lambda>(x2, m). final_expr0 x2) s2"
    moreover obtain x1 m1 where [simp]: "s1 = (x1, m1)" by(cases s1)
    moreover obtain x2 m2 where [simp]: "s2 = (x2, m2)" by(cases s2)
    ultimately have "bisim_red_red0 (x1, m1) (x2, m2)" "final_expr0 x2" by simp_all
    moreover hence "final_expr x1" by(rule bisim_red_red0_final0D)
    ultimately show "\<exists>s1'. red_mthr.silent_moves P t s1 s1' \<and> bisim_red_red0 s1' s2 \<and> (\<lambda>(x1, m). final_expr x1) s1'" by auto
  next
    fix t' x m1 xx m2 t x1 x2 x1' ta1 x1'' m1' x2' ta2 x2'' m2'
    assume b: "bisim_red_red0 (x, m1) (xx, m2)" and bo: "bisim_red_red0 (x1, m1) (x2, m2)"
      and "red_mthr.silent_moves P t (x1, m1) (x1', m1)"
      and red1: "mred P t (x1', m1) ta1 (x1'', m1')" and "\<not> \<tau>MOVE P (x1', m1) ta1 (x1'', m1')"
      and "red0_mthr.silent_moves P t (x2, m2) (x2', m2)"
      and red2: "mred0 P t (x2', m2) ta2 (x2'', m2')" and "\<not> \<tau>MOVE0 P (x2', m2) ta2 (x2'', m2')"
      and bo': "bisim_red_red0 (x1'', m1') (x2'', m2')"
      and tb: "ta_bisim0 ta1 ta2"
    from b have "m1 = m2" by(auto elim: bisim_red_red0.cases)
    moreover from bo' have "m1' = m2'" by(auto elim: bisim_red_red0.cases)
    ultimately show "bisim_red_red0 (x, m1') (xx, m2')" using b
      by(auto elim: bisim_red_red0.cases)
  next
    fix t x1 m1 x2 m2 x1' ta1 x1'' m1' x2' ta2 x2'' m2' w
    assume b: "bisim_red_red0 (x1, m1) (x2, m2)"
      and "red_mthr.silent_moves P t (x1, m1) (x1', m1)"
      and red1: "mred P t (x1', m1) ta1 (x1'', m1')" and "\<not> \<tau>MOVE P (x1', m1) ta1 (x1'', m1')"
      and "red0_mthr.silent_moves P t (x2, m2) (x2', m2)" 
      and red2: "mred0 P t (x2', m2) ta2 (x2'', m2')" and "\<not> \<tau>MOVE0 P (x2', m2) ta2 (x2'', m2')"
      and b': "bisim_red_red0 (x1'', m1') (x2'', m2')" and "ta_bisim0 ta1 ta2"
      and Suspend: "Suspend w \<in> set \<lbrace>ta1\<rbrace>\<^bsub>w\<^esub>" "Suspend w \<in> set \<lbrace>ta2\<rbrace>\<^bsub>w\<^esub>"
    hence "(\<lambda>exs (e0, es0). is_call e0) x1'' x2''"
      by(cases x1')(cases x2', auto dest: Red_Suspend_is_call simp add: final_iff)
    thus "(\<lambda>exs (e0, es0). \<not> final e0) x1'' x2''" by(auto simp add: final_iff is_call_def)
  next
    fix t x1 m1 x2 m2 ta1 x1' m1'
    assume b: "bisim_red_red0 (x1, m1) (x2, m2)"
      and c: "(\<lambda>(e0, es0). \<not> final e0) x2"
      and red1: "mred P t (x1, m1) ta1 (x1', m1')"
      and wakeup: "Notified \<in> set \<lbrace>ta1\<rbrace>\<^bsub>w\<^esub> \<or> WokenUp \<in> set \<lbrace>ta1\<rbrace>\<^bsub>w\<^esub>"
    from c have "\<not> final (fst x2)" by(auto simp add: is_call_def)
    moreover from red1 wakeup have "\<not> \<tau>move0 P m1 (fst x1)"
      by(cases x1)(auto dest: red_\<tau>_taD[where extTA="extTA2J P", simplified] simp add: ta_upd_simps)
    moreover from b have "m2 = m1" by(cases) auto
    ultimately obtain e0' ta0 where "P,t \<turnstile>0 \<langle>fst x2/snd x2,m2\<rangle> -ta0\<rightarrow> \<langle>e0'/snd x2,m1'\<rangle>"
      "bisim_red_red0 ((fst x1', snd x1'), m1') ((e0', snd x2), m1')" "ta_bisim0 ta1 ta0"
      using red0_simulates_red_not_final[OF wf, of "fst x1" "snd x1" m1 "fst x2" "snd x2" m2 t ta1 "fst x1'" m1' "snd x1'"]
      using b red1 by(auto simp add: split_beta)
    thus "\<exists>ta2 x2' m2'. mred0 P t (x2, m2) ta2 (x2', m2') \<and> bisim_red_red0 (x1', m1') (x2', m2') \<and> ta_bisim0 ta1 ta2"
      by(cases ta0)(fastforce simp add: split_beta)
  next
    fix t x1 m1 x2 m2 ta2 x2' m2'
    assume b: "bisim_red_red0 (x1, m1) (x2, m2)"
      and c: "(\<lambda>(e0, es0). \<not> final e0) x2"
      and red2: "mred0 P t (x2, m2) ta2 (x2', m2')"
      and wakeup: "Notified \<in> set \<lbrace>ta2\<rbrace>\<^bsub>w\<^esub> \<or> WokenUp \<in> set \<lbrace>ta2\<rbrace>\<^bsub>w\<^esub>"
    from b have [simp]: "m1 = m2" by cases auto
    with red_simulates_red0[OF wf b red2] wakeup obtain s1' ta1
      where "mred P t (x1, m1) ta1 s1'" "bisim_red_red0 s1' (x2', m2')" "ta_bisim0 ta1 ta2"
      by(fastforce simp add: split_paired_Ex)
    moreover from \<open>bisim_red_red0 s1' (x2', m2')\<close> have "m2' = snd s1'" by cases auto
    ultimately
    show "\<exists>ta1 x1' m1'. mred P t (x1, m1) ta1 (x1', m1') \<and> bisim_red_red0 (x1', m1') (x2', m2') \<and> ta_bisim0 ta1 ta2"
      by(cases ta1)(fastforce simp add: split_beta)
  next
    show "(\<exists>x. final_expr x) \<longleftrightarrow> (\<exists>x. final_expr0 x)"
      by(auto simp add: final_iff)
  qed
qed

end

sublocale J_heap_base < red_red0:
  FWdelay_bisimulation_base 
    final_expr
    "mred P"
    final_expr0 
    "mred0 P"
    convert_RA
    "\<lambda>t. bisim_red_red0" 
    "\<lambda>exs (e0, es0). \<not> final e0"
    "\<tau>MOVE P" "\<tau>MOVE0 P" 
  for P
by(unfold_locales)

context J_heap_base begin

lemma bisim_J_J0_start:
  assumes wf: "wwf_J_prog P"
  and wf_start: "wf_start_state P C M vs"
  shows "red_red0.mbisim (J_start_state P C M vs) (J0_start_state P C M vs)"
proof -
  from wf_start obtain Ts T pns body D
    where sees: "P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>(pns,body)\<rfloor> in D"
    and conf: "P,start_heap \<turnstile> vs [:\<le>] Ts"
    by cases auto

  from conf have vs: "length vs = length Ts" by(rule list_all2_lengthD)
  from sees_wf_mdecl[OF wf sees] 
  have wwfCM: "wwf_J_mdecl P D (M, Ts, T, pns, body)"
    and len: "length pns = length Ts" by(auto simp add: wf_mdecl_def)
  from wwfCM have fvbody: "fv body \<subseteq> {this} \<union> set pns"
    and pns: "length pns = length Ts" by simp_all
  with vs len have fv: "fv (blocks pns Ts vs body) \<subseteq> {this}" by auto
  with len vs sees show ?thesis unfolding start_state_def
    by(auto intro!: red_red0.mbisimI)(auto intro!: bisim_red_red0.intros wset_thread_okI simp add: is_call_def split: if_split_asm)
qed

end

end
