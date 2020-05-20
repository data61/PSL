(*  Title:      JinjaThreads/Compiler/Correctness1Threaded.thy
    Author:     Andreas Lochbihler
*)

section \<open>Unlocking a sync block never fails\<close>

theory Correctness1Threaded imports 
  J0J1Bisim
  "../Framework/FWInitFinLift"
begin

definition lock_oks1 :: 
  "('addr,'thread_id) locks 
  \<Rightarrow> ('addr,'thread_id,(('a,'b,'addr) exp \<times> 'c) \<times> (('a,'b,'addr) exp \<times> 'c) list) thread_info \<Rightarrow> bool" 
where
  "\<And>ln. lock_oks1 ls ts \<equiv> \<forall>t. (case (ts t) of None    \<Rightarrow> (\<forall>l. has_locks (ls $ l) t = 0)
                            | \<lfloor>((ex, exs), ln)\<rfloor> \<Rightarrow> (\<forall>l. has_locks (ls $ l) t + ln $ l = expr_lockss (map fst (ex # exs)) l))"

primrec el_loc_ok :: "'addr expr1 \<Rightarrow> 'addr locals1 \<Rightarrow> bool"
  and els_loc_ok :: "'addr expr1 list \<Rightarrow> 'addr locals1 \<Rightarrow> bool"
where
  "el_loc_ok (new C) xs \<longleftrightarrow> True"
| "el_loc_ok (newA T\<lfloor>e\<rceil>) xs \<longleftrightarrow> el_loc_ok e xs"
| "el_loc_ok (Cast T e) xs \<longleftrightarrow> el_loc_ok e xs"
| "el_loc_ok (e instanceof T) xs \<longleftrightarrow> el_loc_ok e xs"
| "el_loc_ok (e\<guillemotleft>bop\<guillemotright>e') xs \<longleftrightarrow> el_loc_ok e xs \<and> el_loc_ok e' xs"
| "el_loc_ok (Var V) xs \<longleftrightarrow> True"
| "el_loc_ok (Val v) xs \<longleftrightarrow> True"
| "el_loc_ok (V := e) xs \<longleftrightarrow> el_loc_ok e xs"
| "el_loc_ok (a\<lfloor>i\<rceil>) xs \<longleftrightarrow> el_loc_ok a xs \<and> el_loc_ok i xs"
| "el_loc_ok (a\<lfloor>i\<rceil> := e) xs \<longleftrightarrow> el_loc_ok a xs \<and> el_loc_ok i xs \<and> el_loc_ok e xs"
| "el_loc_ok (a\<bullet>length) xs \<longleftrightarrow> el_loc_ok a xs"
| "el_loc_ok (e\<bullet>F{D}) xs \<longleftrightarrow> el_loc_ok e xs"
| "el_loc_ok (e\<bullet>F{D} := e') xs \<longleftrightarrow> el_loc_ok e xs \<and> el_loc_ok e' xs"
| "el_loc_ok (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) xs \<longleftrightarrow> el_loc_ok e xs \<and> el_loc_ok e' xs \<and> el_loc_ok e'' xs"
| "el_loc_ok (e\<bullet>M(ps)) xs \<longleftrightarrow> el_loc_ok e xs \<and> els_loc_ok ps xs"
| "el_loc_ok {V:T=vo; e} xs \<longleftrightarrow> (case vo of None \<Rightarrow> el_loc_ok e xs | \<lfloor>v\<rfloor> \<Rightarrow> el_loc_ok e (xs[V := v]))"
| "el_loc_ok (sync\<^bsub>V\<^esub>(e) e') xs \<longleftrightarrow> el_loc_ok e xs \<and> el_loc_ok e' xs \<and> unmod e' V"
| "el_loc_ok (insync\<^bsub>V\<^esub>(a) e) xs \<longleftrightarrow> xs ! V = Addr a \<and> el_loc_ok e xs \<and> unmod e V"
| "el_loc_ok (e;;e') xs \<longleftrightarrow> el_loc_ok e xs \<and> el_loc_ok e' xs"
| "el_loc_ok (if (b) e else e') xs \<longleftrightarrow> el_loc_ok b xs \<and> el_loc_ok e xs \<and> el_loc_ok e' xs"
| "el_loc_ok (while (b) c) xs \<longleftrightarrow> el_loc_ok b xs \<and> el_loc_ok c xs"
| "el_loc_ok (throw e) xs \<longleftrightarrow> el_loc_ok e xs"
| "el_loc_ok (try e catch(C V) e') xs \<longleftrightarrow> el_loc_ok e xs \<and> el_loc_ok e' xs"

| "els_loc_ok [] xs \<longleftrightarrow> True"
| "els_loc_ok (e # es) xs \<longleftrightarrow> el_loc_ok e xs \<and> els_loc_ok es xs"

lemma el_loc_okI: "\<lbrakk> \<not> contains_insync e; syncvars e; \<B> e n \<rbrakk> \<Longrightarrow> el_loc_ok e xs"
  and els_loc_okI: "\<lbrakk> \<not> contains_insyncs es; syncvarss es; \<B>s es n \<rbrakk> \<Longrightarrow> els_loc_ok es xs"
by(induct e and es arbitrary: xs n and xs n rule: el_loc_ok.induct els_loc_ok.induct)(auto intro: fv_B_unmod)

lemma el_loc_ok_compE1: "\<lbrakk> \<not> contains_insync e; fv e \<subseteq> set Vs \<rbrakk> \<Longrightarrow> el_loc_ok (compE1 Vs e) xs"
  and els_loc_ok_compEs1: "\<lbrakk> \<not> contains_insyncs es; fvs es \<subseteq> set Vs \<rbrakk> \<Longrightarrow> els_loc_ok (compEs1 Vs es) xs"
by(auto intro: el_loc_okI els_loc_okI syncvars_compE1 syncvarss_compEs1 \<B> \<B>s simp del: compEs1_conv_map)

lemma shows el_loc_ok_not_contains_insync_local_change:
  "\<lbrakk> \<not> contains_insync e; el_loc_ok e xs \<rbrakk> \<Longrightarrow> el_loc_ok e xs'"
  and els_loc_ok_not_contains_insyncs_local_change:
  "\<lbrakk> \<not> contains_insyncs es; els_loc_ok es xs \<rbrakk> \<Longrightarrow> els_loc_ok es xs'"
by(induct e and es arbitrary: xs xs' and xs xs' rule: el_loc_ok.induct els_loc_ok.induct)(fastforce)+

lemma el_loc_ok_update: "\<lbrakk> \<B> e n; V < n \<rbrakk> \<Longrightarrow> el_loc_ok e (xs[V := v]) = el_loc_ok e xs"
  and els_loc_ok_update: "\<lbrakk> \<B>s es n; V < n \<rbrakk> \<Longrightarrow> els_loc_ok es (xs[V := v]) = els_loc_ok es xs"
apply(induct e and es arbitrary: n xs and n xs rule: el_loc_ok.induct els_loc_ok.induct) 
apply(auto simp add: list_update_swap)
done

lemma els_loc_ok_map_Val [simp]:
  "els_loc_ok (map Val vs) xs"
by(induct vs) auto

lemma els_loc_ok_map_Val_append [simp]:
  "els_loc_ok (map Val vs @ es) xs = els_loc_ok es xs"
by(induct vs) auto

lemma el_loc_ok_extRet2J [simp]:
  "el_loc_ok e xs \<Longrightarrow> el_loc_ok (extRet2J e va) xs"
by(cases va) auto

definition el_loc_ok1 :: "((nat, nat, 'addr) exp \<times> 'addr locals1) \<times> ((nat, nat, 'addr) exp \<times> 'addr locals1) list \<Rightarrow> bool"
  where "el_loc_ok1 = (\<lambda>((e, xs), exs). el_loc_ok e xs \<and> sync_ok e \<and> (\<forall>(e,xs)\<in>set exs. el_loc_ok e xs \<and> sync_ok e))"

lemma el_loc_ok1_simps:
  "el_loc_ok1 ((e, xs), exs) = (el_loc_ok e xs \<and> sync_ok e \<and> (\<forall>(e,xs)\<in>set exs. el_loc_ok e xs \<and> sync_ok e))"
by(simp add: el_loc_ok1_def)

lemma el_loc_ok_blocks1 [simp]:
   "el_loc_ok (blocks1 n Ts body) xs = el_loc_ok body xs"
by(induct n Ts body rule: blocks1.induct) auto

lemma sync_oks_blocks1 [simp]: "sync_ok (blocks1 n Ts e) = sync_ok e"
by(induct n Ts e rule: blocks1.induct) auto

lemma assumes fin: "final e'"
  shows el_loc_ok_inline_call: "el_loc_ok e xs \<Longrightarrow> el_loc_ok (inline_call e' e) xs"
  and els_loc_ok_inline_calls: "els_loc_ok es xs \<Longrightarrow> els_loc_ok (inline_calls e' es) xs"
apply(induct e and es arbitrary: xs and xs rule: el_loc_ok.induct els_loc_ok.induct)
apply(insert fin)
apply(auto simp add: unmod_inline_call)
done

lemma assumes "sync_ok e'"
  shows sync_ok_inline_call: "sync_ok e \<Longrightarrow> sync_ok (inline_call e' e)"
  and sync_oks_inline_calls: "sync_oks es \<Longrightarrow> sync_oks (inline_calls e' es)"
apply(induct e and es rule: sync_ok.induct sync_oks.induct)
apply(insert \<open>sync_ok e'\<close>)
apply auto
done

lemma bisim_sync_ok:
  "bisim Vs e e' xs \<Longrightarrow> sync_ok e"
  "bisim Vs e e' xs \<Longrightarrow> sync_ok e'"

  and bisims_sync_oks:
  "bisims Vs es es' xs \<Longrightarrow> sync_oks es"
  "bisims Vs es es' xs \<Longrightarrow> sync_oks es'"
apply(induct rule: bisim_bisims.inducts)
apply(auto intro: not_contains_insync_sync_ok not_contains_insyncs_sync_oks simp del: compEs1_conv_map)
done  

lemma assumes "final e'"
  shows expr_locks_inline_call_final:
  "expr_locks (inline_call e' e) = expr_locks e"
  and expr_lockss_inline_calls_final:
  "expr_lockss (inline_calls e' es) = expr_lockss es"
apply(induct e and es rule: expr_locks.induct expr_lockss.induct)
apply(insert \<open>final e'\<close>)
apply(auto simp add: is_vals_conv intro: ext)
done

lemma lock_oks1I:
  "\<lbrakk> \<And>t l. ts t = None \<Longrightarrow> has_locks (ls $ l) t = 0;
     \<And>t e x exs ln l. ts t = \<lfloor>(((e, x), exs), ln)\<rfloor> \<Longrightarrow> has_locks (ls $ l) t + ln $ l= expr_locks e l + expr_lockss (map fst exs) l \<rbrakk>
  \<Longrightarrow> lock_oks1 ls ts"
apply(fastforce simp add: lock_oks1_def)
done

lemma lock_oks1E:
  "\<lbrakk> lock_oks1 ls ts;
     \<forall>t. ts t = None \<longrightarrow> (\<forall>l. has_locks (ls $ l) t = 0) \<Longrightarrow> Q;
     \<forall>t e x exs ln. ts t = \<lfloor>(((e, x), exs), ln)\<rfloor> \<longrightarrow> (\<forall>l. has_locks (ls $ l) t + ln $ l = expr_locks e l + expr_lockss (map fst exs) l) \<Longrightarrow> Q \<rbrakk>
  \<Longrightarrow> Q"
by(fastforce simp add: lock_oks1_def)

lemma lock_oks1D1:
  "\<lbrakk> lock_oks1 ls ts; ts t = None \<rbrakk> \<Longrightarrow> \<forall>l. has_locks (ls $ l) t = 0"
apply(simp add: lock_oks1_def)
apply(erule_tac x="t" in allE)
apply(auto)
done

lemma lock_oks1D2:
  "\<And>ln. \<lbrakk> lock_oks1 ls ts; ts t = \<lfloor>(((e, x), exs), ln)\<rfloor> \<rbrakk> 
  \<Longrightarrow> \<forall>l. has_locks (ls $ l) t + ln $ l = expr_locks e l + expr_lockss (map fst exs) l"
apply(fastforce simp add: lock_oks1_def)
done

lemma lock_oks1_thr_updI:
  "\<And>ln. \<lbrakk> lock_oks1 ls ts; ts t = \<lfloor>(((e, xs), exs), ln)\<rfloor>;
     \<forall>l. expr_locks e l + expr_lockss (map fst exs) l = expr_locks e' l + expr_lockss (map fst exs') l \<rbrakk>
  \<Longrightarrow> lock_oks1 ls (ts(t \<mapsto> (((e', xs'), exs'), ln)))"
by(rule lock_oks1I)(auto split: if_split_asm dest: lock_oks1D2 lock_oks1D1)


definition mbisim_Red1'_Red1 ::
  "(('addr,'thread_id,('addr expr1 \<times> 'addr locals1) \<times> ('addr expr1 \<times> 'addr locals1) list,'heap,'addr) state, 
    ('addr,'thread_id,('addr expr1 \<times> 'addr locals1) \<times> ('addr expr1 \<times> 'addr locals1) list,'heap,'addr) state) bisim"
where
  "mbisim_Red1'_Red1 s1 s2 = 
  (s1 = s2 \<and> lock_oks1 (locks s1) (thr s1) \<and> ts_ok (\<lambda>t exexs h. el_loc_ok1 exexs) (thr s1) (shr s1))"

lemma sync_ok_blocks:
  "\<lbrakk> length vs = length pns; length Ts = length pns\<rbrakk>
  \<Longrightarrow> sync_ok (blocks pns Ts vs body) = sync_ok body"
by(induct pns Ts vs body rule: blocks.induct) auto

context J1_heap_base begin

lemma red1_True_into_red1_False:
  "\<lbrakk> True,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; el_loc_ok e (lcl s) \<rbrakk> 
  \<Longrightarrow> False,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<or> (\<exists>l. ta = \<lbrace>UnlockFail\<rightarrow>l\<rbrace> \<and> expr_locks e l > 0)"
  and reds1_True_into_reds1_False:
  "\<lbrakk> True,P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; els_loc_ok es (lcl s) \<rbrakk>
  \<Longrightarrow> False,P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<or> (\<exists>l. ta = \<lbrace>UnlockFail\<rightarrow>l\<rbrace> \<and> expr_lockss es l > 0)"
apply(induct rule: red1_reds1.inducts)
apply(auto intro: red1_reds1.intros split: if_split_asm)
done

lemma Red1_True_into_Red1_False:
  assumes "True,P,t \<turnstile>1 \<langle>ex/exs,shr s\<rangle> -ta\<rightarrow> \<langle>ex'/exs',m'\<rangle>"
  and "el_loc_ok1 (ex, exs)"
  shows "False,P,t \<turnstile>1 \<langle>ex/exs,shr s\<rangle> -ta\<rightarrow> \<langle>ex'/exs',m'\<rangle> \<or> 
         (\<exists>l. ta = \<lbrace>UnlockFail\<rightarrow>l\<rbrace> \<and> expr_lockss (fst ex # map fst exs) l > 0)"
using assms
by(cases)(auto dest: Red1.intros red1_True_into_red1_False simp add: el_loc_ok1_def ta_upd_simps)

lemma shows red1_preserves_el_loc_ok:
  "\<lbrakk> uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; sync_ok e; el_loc_ok e (lcl s) \<rbrakk> \<Longrightarrow> el_loc_ok e' (lcl s')"

  and reds1_preserves_els_loc_ok:
  "\<lbrakk> uf,P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; sync_oks es; els_loc_ok es (lcl s) \<rbrakk> \<Longrightarrow> els_loc_ok es' (lcl s')"
proof(induct rule: red1_reds1.inducts)
  case (Synchronized1Red2 e s ta e' s' V a)
  from \<open>el_loc_ok (insync\<^bsub>V\<^esub> (a) e) (lcl s)\<close>
  have "el_loc_ok e (lcl s)" "unmod e V" "lcl s ! V = Addr a" by auto
  from \<open>sync_ok (insync\<^bsub>V\<^esub> (a) e)\<close> have "sync_ok e" by simp
  hence "el_loc_ok e' (lcl s')"
    using \<open>el_loc_ok e (lcl s)\<close>
    by(rule Synchronized1Red2)
  moreover from \<open>uf,P,t \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>\<close> \<open>unmod e V\<close> have "unmod e' V"
    by(rule red1_unmod_preserved)
  moreover from red1_preserves_unmod[OF \<open>uf,P,t \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>\<close> \<open>unmod e V\<close>] \<open>lcl s ! V = Addr a\<close>
  have "lcl s' ! V = Addr a" by simp
  ultimately show ?case by auto
qed(auto elim: el_loc_ok_not_contains_insync_local_change els_loc_ok_not_contains_insyncs_local_change)

lemma red1_preserves_sync_ok: "\<lbrakk> uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; sync_ok e \<rbrakk> \<Longrightarrow> sync_ok e'"
  and reds1_preserves_sync_oks: "\<lbrakk> uf,P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; sync_oks es \<rbrakk> \<Longrightarrow> sync_oks es'"
by(induct rule: red1_reds1.inducts)(auto elim: not_contains_insync_sync_ok)

lemma Red1_preserves_el_loc_ok1:
  assumes wf: "wf_J1_prog P"
  shows "\<lbrakk> uf,P,t \<turnstile>1 \<langle>ex/exs,m\<rangle> -ta\<rightarrow> \<langle>ex'/exs',m'\<rangle>; el_loc_ok1 (ex, exs) \<rbrakk>  \<Longrightarrow> el_loc_ok1 (ex', exs')"
apply(erule Red1.cases)
  apply(auto simp add: el_loc_ok1_def dest: red1_preserves_el_loc_ok red1_preserves_sync_ok intro: el_loc_ok_inline_call sync_ok_inline_call)
 apply(fastforce dest!: sees_wf_mdecl[OF wf] simp add: wf_mdecl_def intro!: el_loc_okI dest: WT1_not_contains_insync intro: not_contains_insync_sync_ok)+
done

lemma assumes wf: "wf_J1_prog P"
  shows red1_el_loc_ok1_new_thread:
  "\<lbrakk> uf,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewThread t' (C, M, a) h \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> el_loc_ok1 (({0:Class (fst (method P C M))=None; the (snd (snd (snd (method P C M))))}, xs), [])"

  and reds1_el_loc_ok1_new_thread:
  "\<lbrakk> uf,P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; NewThread t' (C, M, a) h \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> el_loc_ok1 (({0:Class (fst (method P C M))=None; the (snd (snd (snd (method P C M))))}, xs), [])"
proof(induct rule: red1_reds1.inducts)
  case Red1CallExternal thus ?case
    apply(auto dest!: red_external_new_thread_sees[OF wf] simp add: el_loc_ok1_simps)
    apply(auto dest!: sees_wf_mdecl[OF wf] WT1_not_contains_insync simp add: wf_mdecl_def intro!: el_loc_okI not_contains_insync_sync_ok)
    done
qed auto

lemma Red1_el_loc_ok1_new_thread:
  assumes wf: "wf_J1_prog P"
  shows "\<lbrakk> uf,P,t \<turnstile>1 \<langle>ex/exs,m\<rangle> -ta\<rightarrow> \<langle>ex'/exs',m'\<rangle>; NewThread t' exexs m' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
         \<Longrightarrow> el_loc_ok1 exexs"
by(erule Red1.cases)(fastforce elim: red1_el_loc_ok1_new_thread[OF wf] simp add: ta_upd_simps)+

lemma Red1_el_loc_ok: 
  assumes wf: "wf_J1_prog P"
  shows "lifting_wf final_expr1 (mred1g uf P) (\<lambda>t exexs h. el_loc_ok1 exexs)"
by(unfold_locales)(auto elim: Red1_preserves_el_loc_ok1[OF wf] Red1_el_loc_ok1_new_thread[OF wf])

lemma mred1_eq_mred1':
  assumes lok: "lock_oks1 (locks s) (thr s)"
  and elo: "ts_ok (\<lambda>t exexs h. el_loc_ok1 exexs) (thr s) (shr s)"
  and tst: "thr s t = \<lfloor>(exexs, no_wait_locks)\<rfloor>"
  and aoe: "Red1_mthr.actions_ok s t ta"
  shows "mred1 P t (exexs, shr s) ta = mred1' P t (exexs, shr s) ta"
proof(intro ext iffI)
  fix xm'
  assume "mred1 P t (exexs, shr s) ta xm'"
  moreover obtain ex exs where exexs [simp]: "exexs = (ex, exs)" by(cases exexs)
  moreover obtain ex' exs' m' where xm' [simp]: "xm' = ((ex', exs'), m')" by(cases xm') auto
  ultimately have red: "True,P,t \<turnstile>1 \<langle>ex/exs,shr s\<rangle> -ta\<rightarrow> \<langle>ex'/exs',m'\<rangle>" by simp
  from elo tst have "el_loc_ok1 (ex, exs)" by(auto dest: ts_okD)
  from Red1_True_into_Red1_False[OF red this]
  have "False,P,t \<turnstile>1 \<langle>ex/exs,shr s\<rangle> -ta\<rightarrow> \<langle>ex'/exs',m'\<rangle>"
  proof
    assume "\<exists>l. ta = \<lbrace>UnlockFail\<rightarrow>l\<rbrace> \<and> 0 < expr_lockss (fst ex # map fst exs) l"
    then obtain l where ta: "ta = \<lbrace>UnlockFail\<rightarrow>l\<rbrace>" 
      and el: "expr_lockss (fst ex # map fst exs) l > 0" by blast
    from aoe have "lock_actions_ok (locks s $ l) t (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> $ l)"
      by(auto simp add: lock_ok_las_def)
    with ta have "has_locks (locks s $ l) t = 0" by simp
    with lok tst have "expr_lockss (map fst (ex # exs)) l = 0"
      by(cases ex)(auto 4 6 simp add: lock_oks1_def)
    with el have False by simp
    thus ?thesis ..
  qed
  thus "mred1' P t (exexs, shr s) ta xm'" by simp
next
  fix xm'
  assume "mred1' P t (exexs, shr s) ta xm'"
  thus "mred1 P t (exexs, shr s) ta xm'"
    by(cases xm')(auto simp add: split_beta intro: Red1_False_into_Red1_True)
qed

lemma Red1_mthr_eq_Red1_mthr':
  assumes lok: "lock_oks1 (locks s) (thr s)"
  and elo: "ts_ok (\<lambda>t exexs h. el_loc_ok1 exexs) (thr s) (shr s)"
  shows "Red1_mthr.redT True P s = Red1_mthr.redT False P s"
proof(intro ext)
  fix tta s'
  show "Red1_mthr.redT True P s tta s' = Red1_mthr.redT False P s tta s'" (is "?lhs = ?rhs")
  proof
    assume "?lhs" thus ?rhs
    proof cases
      case (redT_normal t x ta x' m')
      from \<open>mred1 P t (x, shr s) ta (x', m')\<close> have "mred1' P t (x, shr s) ta (x', m')"
        unfolding mred1_eq_mred1'[OF lok elo \<open>thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>\<close> \<open>Red1_mthr.actions_ok s t ta\<close>] .
      thus ?thesis using redT_normal(3-) unfolding \<open>tta = (t, ta)\<close> ..
    next
      case (redT_acquire t x ln n)
      from this(2-) show ?thesis unfolding redT_acquire(1) ..
    qed
  next
    assume ?rhs thus ?lhs
    proof(cases)
      case (redT_normal t x ta x' m')
      from \<open>mred1' P t (x, shr s) ta (x', m')\<close> have "mred1 P t (x, shr s) ta (x', m')"
        unfolding mred1_eq_mred1'[OF lok elo \<open>thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>\<close> \<open>Red1_mthr.actions_ok s t ta\<close>] .
      thus ?thesis using redT_normal(3-) unfolding \<open>tta = (t, ta)\<close> ..
    next
      case (redT_acquire t x ln n)
      from this(2-) show ?thesis unfolding redT_acquire(1) ..
    qed
  qed
qed

lemma assumes wf: "wf_J1_prog P"
  shows expr_locks_new_thread1:
  "\<lbrakk> uf,P,t \<turnstile>1 \<langle>e,s\<rangle> -TA\<rightarrow> \<langle>e',s'\<rangle>; NewThread t' (ex, exs) h \<in> set (map (convert_new_thread_action (extNTA2J1 P)) \<lbrace>TA\<rbrace>\<^bsub>t\<^esub>) \<rbrakk>
  \<Longrightarrow> expr_lockss (map fst (ex # exs)) = (\<lambda>ad. 0)"
  and expr_lockss_new_thread1:
  "\<lbrakk> uf,P,t \<turnstile>1 \<langle>es,s\<rangle> [-TA\<rightarrow>] \<langle>es',s'\<rangle>; NewThread t' (ex, exs) h \<in> set (map (convert_new_thread_action (extNTA2J1 P)) \<lbrace>TA\<rbrace>\<^bsub>t\<^esub>) \<rbrakk>
  \<Longrightarrow> expr_lockss (map fst (ex # exs)) = (\<lambda>ad. 0)"
proof(induct rule: red1_reds1.inducts)
  case (Red1CallExternal s a T M vs ta va h' e' s')
  then obtain C fs ad where subThread: "P \<turnstile> C \<preceq>\<^sup>* Thread" and ext: "extNTA2J1 P (C, run, ad) = (ex, exs)"
    by(fastforce dest: red_external_new_thread_sub_thread)
  from sub_Thread_sees_run[OF wf subThread] obtain D body
    where sees: "P \<turnstile> C sees run: []\<rightarrow>Void = \<lfloor>body\<rfloor> in D" by auto
  from sees_wf_mdecl[OF wf this] obtain T where "P,[Class D] \<turnstile>1 body :: T"
    by(auto simp add: wf_mdecl_def)
  hence "\<not> contains_insync body" by(rule WT1_not_contains_insync)
  hence "expr_locks body = (\<lambda>ad. 0)" by(auto simp add: contains_insync_conv fun_eq_iff)
  with sees ext show ?case by(auto)
qed auto

lemma assumes wf: "wf_J1_prog P"
  shows red1_update_expr_locks:
  "\<lbrakk> False,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; sync_ok e; el_loc_ok e (lcl s) \<rbrakk>
  \<Longrightarrow> upd_expr_locks (int o expr_locks e) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int o expr_locks e'"

  and reds1_update_expr_lockss:
  "\<lbrakk> False,P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; sync_oks es; els_loc_ok es (lcl s) \<rbrakk>
  \<Longrightarrow> upd_expr_locks (int o expr_lockss es) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int o expr_lockss es'"
proof -
  have "\<lbrakk> False,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; sync_ok e; el_loc_ok e (lcl s) \<rbrakk> 
       \<Longrightarrow> upd_expr_locks (\<lambda>ad. 0) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = (\<lambda>ad. (int o expr_locks e') ad - (int o expr_locks e) ad)"
    and "\<lbrakk> False,P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; sync_oks es; els_loc_ok es (lcl s) \<rbrakk>
       \<Longrightarrow> upd_expr_locks (\<lambda>ad. 0) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = (\<lambda>ad. (int o expr_lockss es') ad - (int o expr_lockss es) ad)"
  proof(induct rule: red1_reds1.inducts)
    case Red1CallExternal thus ?case
      by(auto simp add: fun_eq_iff contains_insync_conv contains_insyncs_conv finfun_upd_apply elim!: red_external.cases)
  qed(fastforce simp add: fun_eq_iff contains_insync_conv contains_insyncs_conv finfun_upd_apply)+
  hence "\<lbrakk> False,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; sync_ok e; el_loc_ok e (lcl s) \<rbrakk>
        \<Longrightarrow> upd_expr_locks (\<lambda>ad. 0 + (int \<circ> expr_locks e) ad) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int \<circ> expr_locks e'"
    and "\<lbrakk> False,P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; sync_oks es; els_loc_ok es (lcl s) \<rbrakk>
        \<Longrightarrow> upd_expr_locks (\<lambda>ad. 0 + (int \<circ> expr_lockss es) ad) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int \<circ> expr_lockss es'"
    by(fastforce simp only: upd_expr_locks_add)+
  thus "\<lbrakk> False,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; sync_ok e; el_loc_ok e (lcl s) \<rbrakk>
        \<Longrightarrow> upd_expr_locks (int o expr_locks e) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int o expr_locks e'"
    and "\<lbrakk> False,P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; sync_oks es; els_loc_ok es (lcl s) \<rbrakk>
        \<Longrightarrow> upd_expr_locks (int o expr_lockss es) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> = int o expr_lockss es'"
    by(auto simp add: o_def)
qed

lemma Red1'_preserves_lock_oks:
  assumes wf: "wf_J1_prog P"
  and Red: "Red1_mthr.redT False P s1 ta1 s1'"
  and loks: "lock_oks1 (locks s1) (thr s1)"
  and sync: "ts_ok (\<lambda>t exexs h. el_loc_ok1 exexs) (thr s1) (shr s1)"
  shows "lock_oks1 (locks s1') (thr s1')"
using Red
proof(cases rule: Red1_mthr.redT.cases)
  case (redT_normal t x ta x' m')
  note [simp] = \<open>ta1 = (t, ta)\<close>
  obtain ex exs where x: "x = (ex, exs)" by (cases x)
  obtain ex' exs' where x': "x' = (ex', exs')" by (cases x')
  note thrst = \<open>thr s1 t = \<lfloor>(x, no_wait_locks)\<rfloor>\<close>
  note aoe = \<open>Red1_mthr.actions_ok s1 t ta\<close>
  from \<open>mred1' P t (x, shr s1) ta (x', m')\<close>
  have red: "False,P,t \<turnstile>1 \<langle>ex/exs,shr s1\<rangle> -ta\<rightarrow> \<langle>ex'/exs',m'\<rangle>"
    unfolding x x' by simp_all
  note s1' = \<open>redT_upd s1 t ta x' m' s1'\<close>
  moreover from red 
  have "lock_oks1 (locks s1') (thr s1')"
  proof cases
    case (red1Red e x TA e' x')
    note [simp] = \<open>ex = (e, x)\<close> \<open>ta = extTA2J1 P TA\<close> \<open>ex' = (e', x')\<close> \<open>exs' = exs\<close>
      and red = \<open>False,P,t \<turnstile>1 \<langle>e,(shr s1, x)\<rangle> -TA\<rightarrow> \<langle>e',(m', x')\<rangle>\<close>
    { fix t'
      assume None: "(redT_updTs (thr s1) (map (convert_new_thread_action (extNTA2J1 P)) \<lbrace>TA\<rbrace>\<^bsub>t\<^esub>)(t \<mapsto> (((e', x'), exs), redT_updLns (locks s1) t (snd (the (thr s1 t))) \<lbrace>TA\<rbrace>\<^bsub>l\<^esub>))) t' = None"
      { fix l
        from aoe have "lock_actions_ok (locks s1 $ l) t (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> $ l)" by(auto simp add: lock_ok_las_def)
        with None have "has_locks ((redT_updLs (locks s1) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>) $ l) t' = has_locks (locks s1 $ l) t'"
          by(auto split: if_split_asm)
        also from loks None have "has_locks (locks s1 $ l) t' = 0" unfolding lock_oks1_def
          by(force split: if_split_asm dest!: redT_updTs_None)
        finally have "has_locks (upd_locks (locks s1 $ l) t (\<lbrace>TA\<rbrace>\<^bsub>l\<^esub> $ l)) t' = 0" by simp }
      hence "\<forall>l. has_locks (upd_locks (locks s1 $ l) t (\<lbrace>TA\<rbrace>\<^bsub>l\<^esub> $ l)) t' = 0" .. }
    moreover {
      fix t' eX eXS LN
      assume Some: "(redT_updTs (thr s1) (map (convert_new_thread_action (extNTA2J1 P)) \<lbrace>TA\<rbrace>\<^bsub>t\<^esub>)(t \<mapsto> (((e', x'), exs), redT_updLns (locks s1) t (snd (the (thr s1 t))) \<lbrace>TA\<rbrace>\<^bsub>l\<^esub>))) t' = \<lfloor>((eX, eXS), LN)\<rfloor>"
      { fix l
        from aoe have lao: "lock_actions_ok (locks s1 $ l) t (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> $ l)" by(auto simp add: lock_ok_las_def)
        have "has_locks ((redT_updLs (locks s1) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>) $ l) t' + LN $ l = expr_lockss (map fst (eX # eXS)) l"
        proof(cases "t = t'")
          case True
          from loks thrst x
          have "has_locks (locks s1 $ l) t = expr_locks e l + expr_lockss (map fst exs) l"
            by(force simp add: lock_oks1_def)
          hence "lock_expr_locks_ok (locks s1 $ l) t 0 (int (expr_locks e l + expr_lockss (map fst exs) l))"
            by(simp add: lock_expr_locks_ok_def)
          with lao have "lock_expr_locks_ok (upd_locks (locks s1 $ l) t (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> $ l)) t (upd_threadRs 0 (locks s1 $ l) t (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> $ l))
 (upd_expr_lock_actions (int (expr_locks e l + expr_lockss (map fst exs) l)) (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> $ l))"
            by(rule upd_locks_upd_expr_lock_preserve_lock_expr_locks_ok)
          moreover from sync thrst x have "sync_ok e" "el_loc_ok e x"
            unfolding el_loc_ok1_def by(auto dest: ts_okD)
          with red1_update_expr_locks[OF wf red]
          have "upd_expr_locks (int \<circ> expr_locks e) \<lbrace>TA\<rbrace>\<^bsub>l\<^esub> = int \<circ> expr_locks e'" by(simp)
          hence "upd_expr_lock_actions (int (expr_locks e l)) (\<lbrace>TA\<rbrace>\<^bsub>l\<^esub> $ l) = int (expr_locks e' l)"
            by(simp add: upd_expr_locks_def fun_eq_iff)
          ultimately show ?thesis using lao Some thrst x True
            by(auto simp add: lock_expr_locks_ok_def upd_expr_locks_def)
        next
          case False
          from aoe have tok: "thread_oks (thr s1) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>" by auto
          show ?thesis
          proof(cases "thr s1 t' = None")
            case True
            with Some tok False obtain m 
              where nt: "NewThread t' (eX, eXS) m \<in> set (map (convert_new_thread_action (extNTA2J1 P)) \<lbrace>TA\<rbrace>\<^bsub>t\<^esub>)"
              and [simp]: "LN = no_wait_locks" by(auto dest: redT_updTs_new_thread)
            note expr_locks_new_thread1[OF wf red nt]
            moreover from loks True have "has_locks (locks s1 $ l) t' = 0"
              by(force simp add: lock_oks1_def)
            ultimately show ?thesis using lao False by simp
          next
            case False
            with Some \<open>t \<noteq> t'\<close> tok 
            have "thr s1 t' = \<lfloor>((eX, eXS), LN)\<rfloor>" by(fastforce dest: redT_updTs_Some[OF _ tok])
            with loks tok lao \<open>t \<noteq> t'\<close> show ?thesis by(cases eX)(auto simp add: lock_oks1_def)
          qed
        qed }
      hence "\<forall>l. has_locks ((redT_updLs (locks s1) t \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>) $ l) t' + LN $ l = expr_lockss (map fst (eX # eXS)) l" .. }
    ultimately show ?thesis using s1' unfolding lock_oks1_def x' by(clarsimp simp del: fun_upd_apply)
  next
    case (red1Call e a M vs U Ts T body D x)
    from wf \<open>P \<turnstile> class_type_of U sees M: Ts\<rightarrow>T = \<lfloor>body\<rfloor> in D\<close>
    obtain T' where "P,Class D # Ts \<turnstile>1 body :: T'"
      by(auto simp add: wf_mdecl_def dest!: sees_wf_mdecl)
    hence "expr_locks (blocks1 0 (Class D#Ts) body) = (\<lambda>l. 0)"
      by(auto simp add: expr_locks_blocks1 contains_insync_conv fun_eq_iff dest!: WT1_not_contains_insync)
    thus ?thesis using red1Call thrst loks s1'
      unfolding lock_oks1_def x' x
      by auto force+
  next
    case (red1Return e' x' e x)
    thus ?thesis using thrst loks s1'
      unfolding lock_oks1_def x' x
      apply(auto simp add: redT_updWs_def elim!: rtrancl3p_cases)
       apply(erule_tac x=t in allE)
       apply(erule conjE)
       apply(erule disjE)
        apply(force simp add: expr_locks_inline_call_final ac_simps)
       apply(fastforce simp add: expr_locks_inline_call_final)
      apply hypsubst_thin
      apply(erule_tac x=ta in allE)
      apply fastforce
      done
  qed
  moreover from sync \<open>mred1' P t (x, shr s1) ta (x', m')\<close> thrst aoe s1'
  have "ts_ok (\<lambda>t exexs h. el_loc_ok1 exexs) (thr s1') (shr s1')"
    by(auto intro: lifting_wf.redT_updTs_preserves[OF Red1_el_loc_ok[OF wf]])
  ultimately show ?thesis by simp
next
  case (redT_acquire t x n ln)
  thus ?thesis using loks unfolding lock_oks1_def
    apply auto
     apply force
    apply(case_tac "ln $ l::nat")
     apply simp
     apply(erule allE)
     apply(erule conjE)
     apply(erule allE)+
     apply(erule (1) impE)
     apply(erule_tac x=l in allE)
     apply fastforce
    apply(erule may_acquire_allE)
    apply(erule allE)
    apply(erule_tac x=l in allE)
    apply(erule impE)
     apply simp
    apply(simp only: has_locks_acquire_locks_conv)
    apply(erule conjE)
    apply(erule allE)+
    apply(erule (1) impE)
    apply(erule_tac x=l in allE)
    apply simp
    done
qed

lemma Red1'_Red1_bisimulation:
  assumes wf: "wf_J1_prog P"
  shows "bisimulation (Red1_mthr.redT False P) (Red1_mthr.redT True P) mbisim_Red1'_Red1 (=)"
proof
  fix s1 s2 tl1 s1'
  assume "mbisim_Red1'_Red1 s1 s2" and "Red1_mthr.redT False P s1 tl1 s1'"
  thus "\<exists>s2' tl2. Red1_mthr.redT True P s2 tl2 s2' \<and> mbisim_Red1'_Red1 s1' s2' \<and> tl1 = tl2"
    by(cases tl1)(auto simp add: mbisim_Red1'_Red1_def Red1_mthr_eq_Red1_mthr' simp del: split_paired_Ex elim: Red1'_preserves_lock_oks[OF wf] lifting_wf.redT_preserves[OF Red1_el_loc_ok, OF wf])
next
  fix s1 s2 tl2 s2'
  assume "mbisim_Red1'_Red1 s1 s2" "Red1_mthr.redT True P s2 tl2 s2'"
  thus "\<exists>s1' tl1. Red1_mthr.redT False P s1 tl1 s1' \<and> mbisim_Red1'_Red1 s1' s2' \<and> tl1 = tl2"
    by(cases tl2)(auto simp add: mbisim_Red1'_Red1_def Red1_mthr_eq_Red1_mthr' simp del: split_paired_Ex elim: Red1'_preserves_lock_oks[OF wf] lifting_wf.redT_preserves[OF Red1_el_loc_ok, OF wf])
qed

lemma Red1'_Red1_bisimulation_final:
  "wf_J1_prog P 
  \<Longrightarrow> bisimulation_final (Red1_mthr.redT False P) (Red1_mthr.redT True P) 
       mbisim_Red1'_Red1 (=) Red1_mthr.mfinal Red1_mthr.mfinal"
apply(intro_locales)
 apply(erule Red1'_Red1_bisimulation)
apply(unfold_locales)
apply(auto simp add: mbisim_Red1'_Red1_def)
done

lemma bisim_J1_J1_start:
  assumes wf: "wf_J1_prog P"
  and wf_start: "wf_start_state P C M vs"
  shows "mbisim_Red1'_Red1 (J1_start_state P C M vs) (J1_start_state P C M vs)"
proof -
  from wf_start obtain Ts T body D 
    where sees: "P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>body\<rfloor> in D"
    and conf: "P,start_heap \<turnstile> vs [:\<le>] Ts"
    by cases
  let ?e = "blocks1 0 (Class C#Ts) body"
  let ?xs = "Null # vs @ replicate (max_vars body) undefined_value"

  from sees_wf_mdecl[OF wf sees] obtain T'
    where B: "\<B> body (Suc (length Ts))"
    and wt: "P,Class D # Ts \<turnstile>1 body :: T'"
    and da: "\<D> body \<lfloor>{..length Ts}\<rfloor>"
    and sv: "syncvars body"
    by(auto simp add: wf_mdecl_def)

  from wt have "expr_locks ?e = (\<lambda>_. 0)" by(auto intro: WT1_expr_locks)
  thus ?thesis using da sees sv B
    unfolding start_state_def
    by(fastforce simp add: mbisim_Red1'_Red1_def lock_oks1_def el_loc_ok1_def contains_insync_conv intro!: ts_okI expr_locks_sync_ok split: if_split_asm intro: el_loc_okI)
qed

lemma Red1'_Red1_bisim_into_weak:
  assumes wf: "wf_J1_prog P"
  shows "bisimulation_into_delay (Red1_mthr.redT False P) (Red1_mthr.redT True P) mbisim_Red1'_Red1 (=) (Red1_mthr.m\<tau>move P) (Red1_mthr.m\<tau>move P)"
proof -
  interpret b: bisimulation "Red1_mthr.redT False P" "Red1_mthr.redT True P" "mbisim_Red1'_Red1" "(=)"
    by(rule Red1'_Red1_bisimulation[OF wf])
  show ?thesis by(unfold_locales)(simp add: mbisim_Red1'_Red1_def)
qed

end

sublocale J1_heap_base < Red1_mthr:
  if_\<tau>multithreaded_wf
    final_expr1
    "mred1g uf P"
    convert_RA
    "\<tau>MOVE1 P"
  for uf P
by(unfold_locales)

context J1_heap_base begin

abbreviation if_lock_oks1 ::
  "('addr,'thread_id) locks 
  \<Rightarrow> ('addr,'thread_id,(status \<times> (('a,'b,'addr) exp \<times> 'c) \<times> (('a,'b,'addr) exp \<times> 'c) list)) thread_info
  \<Rightarrow> bool" 
where
  "if_lock_oks1 ls ts \<equiv> lock_oks1 ls (init_fin_descend_thr ts)"

definition if_mbisim_Red1'_Red1 ::
  "(('addr,'thread_id,status \<times> (('addr expr1 \<times> 'addr locals1) \<times> ('addr expr1 \<times> 'addr locals1) list),'heap,'addr) state, 
    ('addr,'thread_id,status \<times> (('addr expr1 \<times> 'addr locals1) \<times> ('addr expr1 \<times> 'addr locals1) list),'heap,'addr) state) bisim"
where
  "if_mbisim_Red1'_Red1 s1 s2 \<longleftrightarrow>
  s1 = s2 \<and> if_lock_oks1 (locks s1) (thr s1) \<and> ts_ok (init_fin_lift (\<lambda>t exexs h. el_loc_ok1 exexs)) (thr s1) (shr s1)"

lemma if_mbisim_Red1'_Red1_imp_mbisim_Red1'_Red1:
  "if_mbisim_Red1'_Red1 s1 s2 \<Longrightarrow> mbisim_Red1'_Red1 (init_fin_descend_state s1) (init_fin_descend_state s2)"
by(auto simp add: mbisim_Red1'_Red1_def if_mbisim_Red1'_Red1_def ts_ok_init_fin_descend_state)

lemma if_Red1_mthr_imp_if_Red1_mthr':
  assumes lok: "if_lock_oks1 (locks s) (thr s)"
  and elo: "ts_ok (init_fin_lift (\<lambda>t exexs h. el_loc_ok1 exexs)) (thr s) (shr s)"
  and Red: "Red1_mthr.if.redT uf P s tta s'"
  shows "Red1_mthr.if.redT (\<not> uf) P s tta s'"
using Red
proof(cases)
  case (redT_acquire t x ln n)
  from this(2-) show ?thesis unfolding redT_acquire(1) ..
next
  case (redT_normal t x ta x' m')
  note aok = \<open>Red1_mthr.if.actions_ok s t ta\<close>
    and tst = \<open>thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>\<close>
  from \<open>Red1_mthr.init_fin uf P t (x, shr s) ta (x', m')\<close>
  have "Red1_mthr.init_fin (\<not> uf) P t (x, shr s) ta (x', m')"
  proof(cases)
    case InitialThreadAction show ?thesis unfolding InitialThreadAction ..
  next
    case (ThreadFinishAction exexs)
    from \<open>final_expr1 exexs\<close> show ?thesis unfolding ThreadFinishAction ..
  next
    case (NormalAction exexs ta' exexs')
    let ?s = "init_fin_descend_state s"

    from lok have "lock_oks1 (locks ?s) (thr ?s)" by(simp)
    moreover from elo have elo: "ts_ok (\<lambda>t exexs h. el_loc_ok1 exexs) (thr ?s) (shr ?s)"
      by(simp add: ts_ok_init_fin_descend_state)
    moreover from tst \<open>x = (Running, exexs)\<close>
    have "thr ?s t = \<lfloor>(exexs, no_wait_locks)\<rfloor>" by simp
    moreover from aok have "Red1_mthr.actions_ok ?s t ta'"
      using \<open>ta = convert_TA_initial (convert_obs_initial ta')\<close> by auto
    ultimately have "mred1 P t (exexs, shr ?s) ta' = mred1' P t (exexs, shr ?s) ta'"
      by(rule mred1_eq_mred1')
    with \<open>mred1g uf P t (exexs, shr s) ta' (exexs', m')\<close>
    have "mred1g (\<not> uf) P t (exexs, shr s) ta' (exexs', m')"
      by(cases uf) simp_all
    thus ?thesis unfolding NormalAction(1-3) by(rule Red1_mthr.init_fin.NormalAction)
  qed
  thus ?thesis using tst aok \<open>redT_upd s t ta x' m' s'\<close> unfolding \<open>tta = (t, ta)\<close> ..
qed

lemma if_Red1_mthr_eq_if_Red1_mthr':
  assumes lok: "if_lock_oks1 (locks s) (thr s)"
  and elo: "ts_ok (init_fin_lift (\<lambda>t exexs h. el_loc_ok1 exexs)) (thr s) (shr s)"
  shows "Red1_mthr.if.redT True P s = Red1_mthr.if.redT False P s"
using if_Red1_mthr_imp_if_Red1_mthr'[OF assms, of True P, simplified]
  if_Red1_mthr_imp_if_Red1_mthr'[OF assms, of False P, simplified]
by(blast del: equalityI)

lemma if_Red1_el_loc_ok: 
  assumes wf: "wf_J1_prog P"
  shows "lifting_wf Red1_mthr.init_fin_final (Red1_mthr.init_fin uf P) (init_fin_lift (\<lambda>t exexs h. el_loc_ok1 exexs))"
by(rule lifting_wf.lifting_wf_init_fin_lift)(rule Red1_el_loc_ok[OF wf])

lemma if_Red1'_preserves_if_lock_oks:
  assumes wf: "wf_J1_prog P"
  and Red: "Red1_mthr.if.redT False P s1 ta1 s1'"
  and loks: "if_lock_oks1 (locks s1) (thr s1)"
  and sync: "ts_ok (init_fin_lift (\<lambda>t exexs h. el_loc_ok1 exexs)) (thr s1) (shr s1)"
  shows "if_lock_oks1 (locks s1') (thr s1')"
proof -
  let ?s1 = "init_fin_descend_state s1"
  let ?s1' = "init_fin_descend_state s1'"
  from loks have loks': "lock_oks1 (locks ?s1) (thr ?s1)" by simp
  from sync have sync': "ts_ok (\<lambda>t exexs h. el_loc_ok1 exexs) (thr ?s1) (shr ?s1)"
    by(simp add: ts_ok_init_fin_descend_state)
  from Red show ?thesis
  proof(cases)
    case (redT_acquire t x n ln)
    hence "Red1_mthr.redT False P ?s1 (t, K$ [], [], [], [], [], convert_RA ln) ?s1'"
      by(cases x)(auto intro!: Red1_mthr.redT.redT_acquire simp add: init_fin_descend_thr_def)
    with wf have "lock_oks1 (locks ?s1') (thr ?s1')" using loks' sync' by(rule Red1'_preserves_lock_oks)
    thus ?thesis by simp
  next
    case (redT_normal t sx ta sx' m')
    note tst = \<open>thr s1 t = \<lfloor>(sx, no_wait_locks)\<rfloor>\<close>
    from \<open>Red1_mthr.init_fin False P t (sx, shr s1) ta (sx', m')\<close>
    show ?thesis
    proof(cases)
      case (InitialThreadAction x) thus ?thesis using redT_normal loks
        by(cases x)(auto 4 3 simp add: init_fin_descend_thr_def redT_updLns_def expand_finfun_eq fun_eq_iff intro: lock_oks1_thr_updI)
    next
      case (ThreadFinishAction x) thus ?thesis using redT_normal loks
        by(cases x)(auto 4 3 simp add: init_fin_descend_thr_def redT_updLns_def expand_finfun_eq fun_eq_iff intro: lock_oks1_thr_updI)
    next
      case (NormalAction x ta' x')
      note ta = \<open>ta = convert_TA_initial (convert_obs_initial ta')\<close>
      from \<open>mred1' P t (x, shr s1) ta' (x', m')\<close>
      have "mred1' P t (x, shr ?s1) ta' (x', m')" by simp
      moreover have tst': "thr ?s1 t = \<lfloor>(x, no_wait_locks)\<rfloor>" 
        using tst \<open>sx = (Running, x)\<close> by simp
      moreover have "Red1_mthr.actions_ok ?s1 t ta'"
        using ta \<open>Red1_mthr.if.actions_ok s1 t ta\<close> by simp
      moreover from \<open>redT_upd s1 t ta sx' m' s1'\<close> tst tst' ta \<open>sx' = (Running, x')\<close>
      have "redT_upd ?s1 t ta' x' m' ?s1'" by auto
      ultimately have "Red1_mthr.redT False P ?s1 (t, ta') ?s1'" ..
      with wf have "lock_oks1 (locks ?s1') (thr ?s1')" using loks' sync' by(rule Red1'_preserves_lock_oks)
      thus ?thesis by simp
    qed
  qed
qed

lemma Red1'_Red1_if_bisimulation:
  assumes wf: "wf_J1_prog P"
  shows "bisimulation (Red1_mthr.if.redT False P) (Red1_mthr.if.redT True P) if_mbisim_Red1'_Red1 (=)"
proof
  fix s1 s2 tl1 s1'
  assume "if_mbisim_Red1'_Red1 s1 s2" and "Red1_mthr.if.redT False P s1 tl1 s1'"
  thus "\<exists>s2' tl2. Red1_mthr.if.redT True P s2 tl2 s2' \<and> if_mbisim_Red1'_Red1 s1' s2' \<and> tl1 = tl2"
    by(cases tl1)(auto simp add: if_mbisim_Red1'_Red1_def if_Red1_mthr_eq_if_Red1_mthr' simp del: split_paired_Ex elim: if_Red1'_preserves_if_lock_oks[OF wf] lifting_wf.redT_preserves[OF if_Red1_el_loc_ok, OF wf])
next
  fix s1 s2 tl2 s2'
  assume "if_mbisim_Red1'_Red1 s1 s2" "Red1_mthr.if.redT True P s2 tl2 s2'"
  thus "\<exists>s1' tl1. Red1_mthr.if.redT False P s1 tl1 s1' \<and> if_mbisim_Red1'_Red1 s1' s2' \<and> tl1 = tl2"
    by(cases tl2)(auto simp add: if_mbisim_Red1'_Red1_def if_Red1_mthr_eq_if_Red1_mthr' simp del: split_paired_Ex elim: if_Red1'_preserves_if_lock_oks[OF wf] lifting_wf.redT_preserves[OF if_Red1_el_loc_ok, OF wf])
qed

lemma if_bisim_J1_J1_start:
  assumes wf: "wf_J1_prog P"
  and wf_start: "wf_start_state P C M vs"
  shows "if_mbisim_Red1'_Red1 (init_fin_lift_state status (J1_start_state P C M vs)) (init_fin_lift_state status (J1_start_state P C M vs))"
proof -
  from assms have "mbisim_Red1'_Red1 (J1_start_state P C M vs) (J1_start_state P C M vs)" by(rule bisim_J1_J1_start)
  thus ?thesis
    by(simp add: if_mbisim_Red1'_Red1_def mbisim_Red1'_Red1_def)(simp add: init_fin_lift_state_conv_simps init_fin_descend_thr_def thr_init_fin_list_state' o_def map_option.compositionality map_option.identity split_beta)
qed

lemma if_Red1'_Red1_bisim_into_weak:
  assumes wf: "wf_J1_prog P"
  shows "bisimulation_into_delay (Red1_mthr.if.redT False P) (Red1_mthr.if.redT True P) if_mbisim_Red1'_Red1 (=) (Red1_mthr.if.m\<tau>move P) (Red1_mthr.if.m\<tau>move P)"
proof -
  interpret b: bisimulation "Red1_mthr.if.redT False P" "Red1_mthr.if.redT True P" "if_mbisim_Red1'_Red1" "(=)"
    by(rule Red1'_Red1_if_bisimulation[OF wf])
  show ?thesis by(unfold_locales)(simp add: if_mbisim_Red1'_Red1_def)
qed

lemma if_Red1'_Red1_bisimulation_final:
  "wf_J1_prog P 
  \<Longrightarrow> bisimulation_final (Red1_mthr.if.redT False P) (Red1_mthr.if.redT True P) 
       if_mbisim_Red1'_Red1 (=) Red1_mthr.if.mfinal Red1_mthr.if.mfinal"
apply(intro_locales)
 apply(erule Red1'_Red1_if_bisimulation)
apply(unfold_locales)
apply(auto simp add: if_mbisim_Red1'_Red1_def)
done

end

end
