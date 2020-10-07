(*  Title:      JinjaThreads/Compiler/J0.thy
    Author:     Andreas Lochbihler
*)

section \<open>The JinjaThreads source language with explicit call stacks\<close>

theory J0 imports
  "../J/WWellForm"
  "../J/WellType"
  "../J/Threaded" 
  "../Framework/FWBisimulation" 
  CallExpr
begin

declare widen_refT [elim]

abbreviation final_expr0 :: "'addr expr \<times> 'addr expr list \<Rightarrow> bool" where
  "final_expr0 \<equiv> \<lambda>(e, es). final e \<and> es = []"

type_synonym
  ('addr, 'thread_id, 'heap) J0_thread_action = 
  "('addr, 'thread_id, 'addr expr \<times> 'addr expr list,'heap) Jinja_thread_action"

type_synonym
  ('addr, 'thread_id, 'heap) J0_state = "('addr,'thread_id,'addr expr \<times> 'addr expr list,'heap,'addr) state"

(* pretty printing for J_thread_action type *)
print_translation \<open>
  let
    fun tr'
       [a1, t
       , Const (@{type_syntax "prod"}, _) $ 
           (Const (@{type_syntax "exp"}, _) $
              Const (@{type_syntax "String.literal"}, _) $ Const (@{type_syntax "unit"}, _) $ a2) $
           (Const (@{type_syntax "list"}, _) $
              (Const (@{type_syntax "exp"}, _) $
                 Const (@{type_syntax "String.literal"}, _) $
                 Const (@{type_syntax "unit"}, _) $ a3))
       , h] =
      if a1 = a2 andalso a2 = a3 then Syntax.const @{type_syntax "J0_thread_action"} $ a1 $ t $ h
      else raise Match;
    in [(@{type_syntax "Jinja_thread_action"}, K tr')]
  end
\<close>
typ "('addr,'thread_id,'heap) J0_thread_action"

(* pretty printing for J0_state type *)
print_translation \<open>
  let
    fun tr'
       [a1, t
       , Const (@{type_syntax "prod"}, _) $ 
           (Const (@{type_syntax "exp"}, _) $
              Const (@{type_syntax "String.literal"}, _) $ Const (@{type_syntax "unit"}, _) $ a2) $
           (Const (@{type_syntax "list"}, _) $
              (Const (@{type_syntax "exp"}, _) $
                 Const (@{type_syntax "String.literal"}, _) $
                 Const (@{type_syntax "unit"}, _) $ a3))
       , h, a4] =
      if a1 = a2 andalso a2 = a3 then Syntax.const @{type_syntax "J0_state"} $ a1 $ t $ h
      else raise Match;
    in [(@{type_syntax "state"}, K tr')]
  end
\<close>
typ "('addr, 'thread_id, 'heap) J0_state"

definition extNTA2J0 :: "'addr J_prog \<Rightarrow> (cname \<times> mname \<times> 'addr) \<Rightarrow> ('addr expr \<times> 'addr expr list)"
where
  "extNTA2J0 P = (\<lambda>(C, M, a). let (D, _, _, meth) = method P C M; (_, body) = the meth
                               in ({this:Class D=\<lfloor>Addr a\<rfloor>; body}, []))"

lemma extNTA2J0_iff [simp]:
  "extNTA2J0 P (C, M, a) = 
   ({this:Class (fst (method P C M))=\<lfloor>Addr a\<rfloor>; snd (the (snd (snd (snd (method P C M)))))}, [])"
by(simp add: extNTA2J0_def split_def)

abbreviation extTA2J0 :: 
  "'addr J_prog \<Rightarrow> ('addr, 'thread_id, 'heap) external_thread_action \<Rightarrow> ('addr, 'thread_id, 'heap) J0_thread_action"
where "extTA2J0 P \<equiv> convert_extTA (extNTA2J0 P)"

lemma obs_a_extTA2J_eq_obs_a_extTA2J0 [simp]: "\<lbrace>extTA2J P ta\<rbrace>\<^bsub>o\<^esub> = \<lbrace>extTA2J0 P ta\<rbrace>\<^bsub>o\<^esub>"
by(cases ta)(simp add: ta_upd_simps)

lemma extTA2J0_\<epsilon>: "extTA2J0 P \<epsilon> = \<epsilon>"
by(simp)

context J_heap_base begin

definition no_call :: "'m prog \<Rightarrow> 'heap \<Rightarrow> ('a, 'b, 'addr) exp \<Rightarrow> bool"
where "no_call P h e = (\<forall>aMvs. call e = \<lfloor>aMvs\<rfloor> \<longrightarrow> synthesized_call P h aMvs)"

definition no_calls :: "'m prog \<Rightarrow> 'heap \<Rightarrow> ('a, 'b, 'addr) exp list \<Rightarrow> bool"
where "no_calls P h es = (\<forall>aMvs. calls es = \<lfloor>aMvs\<rfloor> \<longrightarrow> synthesized_call P h aMvs)"

inductive red0 :: 
  "'addr J_prog \<Rightarrow> 'thread_id \<Rightarrow> 'addr expr \<Rightarrow> 'addr expr list \<Rightarrow> 'heap
  \<Rightarrow> ('addr, 'thread_id, 'heap) J0_thread_action \<Rightarrow> 'addr expr \<Rightarrow> 'addr expr list \<Rightarrow> 'heap \<Rightarrow> bool"
  ("_,_ \<turnstile>0 ((1\<langle>_'/_,/_\<rangle>) -_\<rightarrow>/ (1\<langle>_'/_,/_\<rangle>))" [51,0,0,0,0,0,0,0,0] 81)
for P :: "'addr J_prog" and t :: 'thread_id
where

  red0Red:
  "\<lbrakk> extTA2J0 P,P,t \<turnstile> \<langle>e, (h, Map.empty)\<rangle> -ta\<rightarrow> \<langle>e', (h', xs')\<rangle>;
     \<forall>aMvs. call e = \<lfloor>aMvs\<rfloor> \<longrightarrow> synthesized_call P h aMvs \<rbrakk>
  \<Longrightarrow> P,t \<turnstile>0 \<langle>e/es, h\<rangle> -ta\<rightarrow> \<langle>e'/es, h'\<rangle>"

| red0Call:
  "\<lbrakk> call e = \<lfloor>(a, M, vs)\<rfloor>; typeof_addr h a = \<lfloor>U\<rfloor>; 
     P \<turnstile> class_type_of U sees M:Ts\<rightarrow>T = \<lfloor>(pns, body)\<rfloor> in D; 
     size vs = size pns; size Ts = size pns \<rbrakk>
  \<Longrightarrow> P,t \<turnstile>0 \<langle>e/es, h\<rangle> -\<epsilon>\<rightarrow> \<langle>blocks (this # pns) (Class D # Ts) (Addr a # vs) body/e#es, h\<rangle>"

| red0Return:
  "final e' \<Longrightarrow> P,t \<turnstile>0 \<langle>e'/e#es, h\<rangle> -\<epsilon>\<rightarrow> \<langle>inline_call e' e/es, h\<rangle>"

abbreviation J0_start_state :: "'addr J_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> 'addr val list \<Rightarrow> ('addr, 'thread_id, 'heap) J0_state"
where
  "J0_start_state \<equiv> 
   start_state (\<lambda>C M Ts T (pns, body) vs. (blocks (this # pns) (Class C # Ts) (Null # vs) body, []))"

abbreviation mred0 ::
  "'addr J_prog \<Rightarrow> ('addr,'thread_id,'addr expr \<times> 'addr expr list,'heap,'addr,('addr, 'thread_id) obs_event) semantics"
where "mred0 P \<equiv> (\<lambda>t ((e, es), h) ta ((e', es'), h'). red0 P t e es h ta e' es' h')"

end

declare domIff[iff, simp del]

context J_heap_base begin

lemma assumes wf: "wwf_J_prog P"
  shows red_fv_subset: "extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> fv e' \<subseteq> fv e"
  and reds_fvs_subset: "extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> fvs es' \<subseteq> fvs es"
proof(induct rule: red_reds.inducts)
  case (RedCall s a U M Ts T pns body D vs)
  hence "fv body \<subseteq> {this} \<union> set pns"
    using wf by(fastforce dest!:sees_wf_mdecl simp:wf_mdecl_def)
  with RedCall show ?case by fastforce
next
  case RedCallExternal thus ?case by(auto simp add: extRet2J_def split: extCallRet.split_asm)
qed(fastforce)+

end

declare domIff[iff del]

context J_heap_base begin

lemma assumes wwf: "wwf_J_prog P"
  shows red_fv_ok: "\<lbrakk> extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; fv e \<subseteq> dom (lcl s) \<rbrakk> \<Longrightarrow> fv e' \<subseteq> dom (lcl s')"
  and reds_fvs_ok: "\<lbrakk> extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; fvs es \<subseteq> dom (lcl s) \<rbrakk> \<Longrightarrow> fvs es' \<subseteq> dom (lcl s')"
proof(induct rule: red_reds.inducts)
  case (RedCall s a U M Ts T pns body D vs)
  from \<open>P \<turnstile> class_type_of U sees M: Ts\<rightarrow>T = \<lfloor>(pns, body)\<rfloor> in D\<close> have "wwf_J_mdecl P D (M,Ts,T,pns,body)"
    by(auto dest!: sees_wf_mdecl[OF wwf] simp add: wf_mdecl_def)
  with RedCall show ?case by(auto)
next
  case RedCallExternal thus ?case by(auto simp add: extRet2J_def split: extCallRet.split_asm)
next
  case (BlockRed e h x V vo ta e' h' x' T)
  note red = \<open>extTA,P,t \<turnstile> \<langle>e,(h, x(V := vo))\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>\<close>
  hence "fv e' \<subseteq> fv e" by(auto dest: red_fv_subset[OF wwf] del: subsetI)
  moreover from \<open> fv {V:T=vo; e} \<subseteq> dom (lcl (h, x))\<close>
  have "fv e - {V} \<subseteq> dom x" by(simp)
  ultimately have "fv e' - {V} \<subseteq> dom x - {V}" by(auto)
  moreover from red have "dom (x(V := vo)) \<subseteq> dom x'"
    by(auto dest: red_lcl_incr del: subsetI)
  ultimately have "fv e' - {V} \<subseteq> dom x' - {V}"
    by(auto split: if_split_asm)
  thus ?case by(auto simp del: fun_upd_apply)
qed(fastforce dest: red_lcl_incr del: subsetI)+

lemma is_call_red_state_unchanged: 
  "\<lbrakk> extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; call e = \<lfloor>aMvs\<rfloor>; \<not> synthesized_call P (hp s) aMvs \<rbrakk> \<Longrightarrow> s' = s \<and> ta = \<epsilon>"

  and is_calls_reds_state_unchanged:
  "\<lbrakk> extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; calls es = \<lfloor>aMvs\<rfloor>; \<not> synthesized_call P (hp s) aMvs \<rbrakk> \<Longrightarrow> s' = s \<and> ta = \<epsilon>"
apply(induct rule: red_reds.inducts)
apply(fastforce split: if_split_asm simp add: synthesized_call_def)+
done

lemma called_methodD:
  "\<lbrakk> extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; call e = \<lfloor>(a, M, vs)\<rfloor>; \<not> synthesized_call P (hp s) (a, M, vs) \<rbrakk> 
  \<Longrightarrow> \<exists>hT D Us U pns body. hp s' = hp s \<and> typeof_addr (hp s) a = \<lfloor>hT\<rfloor> \<and>
                           P \<turnstile> class_type_of hT sees M: Us\<rightarrow>U = \<lfloor>(pns, body)\<rfloor> in D \<and> 
                           length vs = length pns \<and> length Us = length pns"

  and called_methodsD:
  "\<lbrakk> extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; calls es = \<lfloor>(a, M, vs)\<rfloor>; \<not> synthesized_call P (hp s) (a, M, vs) \<rbrakk> 
  \<Longrightarrow> \<exists>hT D Us U pns body. hp s' = hp s \<and> typeof_addr (hp s) a = \<lfloor>hT\<rfloor> \<and>
                           P \<turnstile> class_type_of hT sees M: Us\<rightarrow>U = \<lfloor>(pns, body)\<rfloor> in D \<and>
                           length vs = length pns \<and> length Us = length pns"
apply(induct rule: red_reds.inducts)
apply(auto split: if_split_asm simp add: synthesized_call_def)
apply(fastforce)
done

subsection \<open>Silent moves\<close>

primrec  \<tau>move0 :: "'m prog \<Rightarrow> 'heap \<Rightarrow> ('a, 'b, 'addr) exp \<Rightarrow> bool"
  and \<tau>moves0 :: "'m prog \<Rightarrow> 'heap \<Rightarrow> ('a, 'b, 'addr) exp list \<Rightarrow> bool"
where
  "\<tau>move0 P h (new C) \<longleftrightarrow> False"
| "\<tau>move0 P h (newA T\<lfloor>e\<rceil>) \<longleftrightarrow> \<tau>move0 P h e \<or> (\<exists>a. e = Throw a)"
| "\<tau>move0 P h (Cast U e) \<longleftrightarrow> \<tau>move0 P h e \<or> (\<exists>a. e = Throw a) \<or> (\<exists>v. e = Val v)"
| "\<tau>move0 P h (e instanceof T) \<longleftrightarrow> \<tau>move0 P h e \<or> (\<exists>a. e = Throw a) \<or> (\<exists>v. e = Val v)"
| "\<tau>move0 P h (e \<guillemotleft>bop\<guillemotright> e') \<longleftrightarrow> \<tau>move0 P h e \<or> (\<exists>a. e = Throw a) \<or> (\<exists>v. e = Val v \<and>
   (\<tau>move0 P h e' \<or> (\<exists>a. e' = Throw a) \<or> (\<exists>v. e' = Val v)))"
| "\<tau>move0 P h (Val v) \<longleftrightarrow> False"
| "\<tau>move0 P h (Var V) \<longleftrightarrow> True"
| "\<tau>move0 P h (V := e) \<longleftrightarrow> \<tau>move0 P h e \<or> (\<exists>a. e = Throw a) \<or> (\<exists>v. e = Val v)"
| "\<tau>move0 P h (a\<lfloor>i\<rceil>) \<longleftrightarrow> \<tau>move0 P h a \<or> (\<exists>ad. a = Throw ad) \<or> (\<exists>v. a = Val v \<and> (\<tau>move0 P h i \<or> (\<exists>a. i = Throw a)))"
| "\<tau>move0 P h (AAss a i e) \<longleftrightarrow> \<tau>move0 P h a \<or> (\<exists>ad. a = Throw ad) \<or> (\<exists>v. a = Val v \<and> 
   (\<tau>move0 P h i \<or> (\<exists>a. i = Throw a) \<or> (\<exists>v. i = Val v \<and> (\<tau>move0 P h e \<or> (\<exists>a. e = Throw a)))))"
| "\<tau>move0 P h (a\<bullet>length) \<longleftrightarrow> \<tau>move0 P h a \<or> (\<exists>ad. a = Throw ad)"
| "\<tau>move0 P h (e\<bullet>F{D}) \<longleftrightarrow> \<tau>move0 P h e \<or> (\<exists>a. e = Throw a)"
| "\<tau>move0 P h (FAss e F D e') \<longleftrightarrow> \<tau>move0 P h e \<or> (\<exists>a. e = Throw a) \<or> (\<exists>v. e = Val v \<and> (\<tau>move0 P h e' \<or> (\<exists>a. e' = Throw a)))"
| "\<tau>move0 P h (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) \<longleftrightarrow> \<tau>move0 P h e \<or> (\<exists>a. e = Throw a) \<or> (\<exists>v. e = Val v \<and>
   (\<tau>move0 P h e' \<or> (\<exists>a. e' = Throw a) \<or> (\<exists>v. e' = Val v \<and> (\<tau>move0 P h e'' \<or> (\<exists>a. e'' = Throw a)))))"
| "\<tau>move0 P h (e\<bullet>M(es)) \<longleftrightarrow> \<tau>move0 P h e \<or> (\<exists>a. e = Throw a) \<or> (\<exists>v. e = Val v \<and>
   ((\<tau>moves0 P h es \<or> (\<exists>vs a es'. es = map Val vs @ Throw a # es')) \<or> 
    (\<exists>vs. es = map Val vs \<and> (v = Null \<or> (\<forall>T C Ts Tr D. typeof\<^bsub>h\<^esub> v = \<lfloor>T\<rfloor> \<longrightarrow> class_type_of' T = \<lfloor>C\<rfloor> \<longrightarrow> P \<turnstile> C sees M:Ts\<rightarrow>Tr = Native in D \<longrightarrow> \<tau>external_defs D M)))))"
| "\<tau>move0 P h ({V:T=vo; e}) \<longleftrightarrow> \<tau>move0 P h e \<or> ((\<exists>a. e = Throw a) \<or> (\<exists>v. e = Val v))"
| "\<tau>move0 P h (sync\<^bsub>V'\<^esub>(e) e') \<longleftrightarrow> \<tau>move0 P h e \<or> (\<exists>a. e = Throw a)"
| "\<tau>move0 P h (insync\<^bsub>V'\<^esub>(ad) e) \<longleftrightarrow> \<tau>move0 P h e"
| "\<tau>move0 P h (e;;e') \<longleftrightarrow> \<tau>move0 P h e \<or> (\<exists>a. e = Throw a) \<or> (\<exists>v. e = Val v)"
| "\<tau>move0 P h (if (e) e' else e'') \<longleftrightarrow> \<tau>move0 P h e \<or> (\<exists>a. e = Throw a) \<or> (\<exists>v. e = Val v)"
| "\<tau>move0 P h (while (e) e') = True"
| \<comment> \<open>@{term "Throw a"} is no @{text "\<tau>move0"} because there is no reduction for it.
  If it were, most defining equations would be simpler. However, @{term "insync\<^bsub>V'\<^esub>(ad) (Throw ad)"}
  must not be a @{text "\<tau>move0"}, but would be if @{term "Throw a"} was.\<close>
  "\<tau>move0 P h (throw e) \<longleftrightarrow> \<tau>move0 P h e \<or> (\<exists>a. e = Throw a) \<or> e = null"
| "\<tau>move0 P h (try e catch(C V) e') \<longleftrightarrow> \<tau>move0 P h e \<or> (\<exists>a. e = Throw a) \<or> (\<exists>v. e = Val v)"

| "\<tau>moves0 P h [] \<longleftrightarrow> False"
| "\<tau>moves0 P h (e # es) \<longleftrightarrow> \<tau>move0 P h e \<or> (\<exists>v. e = Val v \<and> \<tau>moves0 P h es)"

abbreviation \<tau>MOVE :: "'m prog \<Rightarrow> (('addr expr \<times> 'addr locals) \<times> 'heap, ('addr, 'thread_id, 'heap) J_thread_action) trsys"
where "\<tau>MOVE \<equiv> \<lambda>P ((e, x), h) ta s'. \<tau>move0 P h e \<and> ta = \<epsilon>"

primrec \<tau>Move0 :: "'m prog \<Rightarrow> 'heap \<Rightarrow> ('addr expr \<times> 'addr expr list) \<Rightarrow> bool"
where
  "\<tau>Move0 P h (e, exs) = (\<tau>move0 P h e \<or> final e)"
  
abbreviation \<tau>MOVE0 :: "'m prog \<Rightarrow> (('addr expr \<times> 'addr expr list) \<times> 'heap, ('addr, 'thread_id, 'heap) J0_thread_action) trsys"
where "\<tau>MOVE0 \<equiv> \<lambda>P (es, h) ta s. \<tau>Move0 P h es \<and> ta = \<epsilon>"

definition \<tau>red0 ::
  "(('addr, 'thread_id, 'heap) external_thread_action \<Rightarrow> ('addr, 'thread_id, 'x,'heap) Jinja_thread_action)
  \<Rightarrow> 'addr J_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr \<times> 'addr locals) \<Rightarrow> ('addr expr \<times> 'addr locals) \<Rightarrow> bool"
where
  "\<tau>red0 extTA P t h exs e'xs' =
   (extTA,P,t \<turnstile> \<langle>fst exs, (h, snd exs)\<rangle> -\<epsilon>\<rightarrow> \<langle>fst e'xs', (h, snd e'xs')\<rangle> \<and> \<tau>move0 P h (fst exs) \<and> no_call P h (fst exs))"

definition \<tau>reds0 :: 
  "(('addr, 'thread_id, 'heap) external_thread_action \<Rightarrow> ('addr, 'thread_id, 'x,'heap) Jinja_thread_action) 
  \<Rightarrow> 'addr J_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr list \<times> 'addr locals) \<Rightarrow> ('addr expr list \<times> 'addr locals) \<Rightarrow> bool"
where 
  "\<tau>reds0 extTA P t h esxs es'xs' = 
   (extTA,P,t \<turnstile> \<langle>fst esxs, (h, snd esxs)\<rangle> [-\<epsilon>\<rightarrow>] \<langle>fst es'xs', (h, snd es'xs')\<rangle> \<and> \<tau>moves0 P h (fst esxs) \<and>
    no_calls P h (fst esxs))"

abbreviation \<tau>red0t ::
  "(('addr, 'thread_id, 'heap) external_thread_action \<Rightarrow> ('addr, 'thread_id, 'x,'heap) Jinja_thread_action) 
  \<Rightarrow> 'addr J_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr \<times> 'addr locals) \<Rightarrow> ('addr expr \<times> 'addr locals) \<Rightarrow> bool"
where "\<tau>red0t extTA P t h \<equiv> (\<tau>red0 extTA P t h)^++"

abbreviation \<tau>reds0t ::
  "(('addr, 'thread_id, 'heap) external_thread_action \<Rightarrow> ('addr, 'thread_id, 'x,'heap) Jinja_thread_action) 
  \<Rightarrow> 'addr J_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr list \<times> 'addr locals) \<Rightarrow> ('addr expr list \<times> 'addr locals) \<Rightarrow> bool"
where "\<tau>reds0t extTA P t h \<equiv> (\<tau>reds0 extTA P t h)^++"

abbreviation \<tau>red0r :: 
  "(('addr, 'thread_id, 'heap) external_thread_action \<Rightarrow> ('addr, 'thread_id, 'x,'heap) Jinja_thread_action) 
  \<Rightarrow> 'addr J_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr \<times> 'addr locals) \<Rightarrow> ('addr expr \<times> 'addr locals) \<Rightarrow> bool"
where "\<tau>red0r extTA P t h \<equiv> (\<tau>red0 extTA P t h)^**"

abbreviation \<tau>reds0r :: 
  "(('addr, 'thread_id, 'heap) external_thread_action \<Rightarrow> ('addr, 'thread_id, 'x,'heap) Jinja_thread_action)
  \<Rightarrow> 'addr J_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr list \<times> 'addr locals) \<Rightarrow> ('addr expr list \<times> 'addr locals) \<Rightarrow> bool"
where "\<tau>reds0r extTA P t h \<equiv> (\<tau>reds0 extTA P t h)^**"

definition \<tau>Red0 :: 
  "'addr J_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr \<times> 'addr expr list) \<Rightarrow> ('addr expr \<times> 'addr expr list) \<Rightarrow> bool"
where "\<tau>Red0 P t h ees e'es' = (P,t \<turnstile>0 \<langle>fst ees/snd ees, h\<rangle> -\<epsilon>\<rightarrow> \<langle>fst e'es'/snd e'es', h\<rangle> \<and> \<tau>Move0 P h ees)"

abbreviation \<tau>Red0r ::
  "'addr J_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr \<times> 'addr expr list) \<Rightarrow> ('addr expr \<times> 'addr expr list) \<Rightarrow> bool"
where "\<tau>Red0r P t h \<equiv> (\<tau>Red0 P t h)^**"

abbreviation \<tau>Red0t ::
  "'addr J_prog \<Rightarrow> 'thread_id \<Rightarrow> 'heap \<Rightarrow> ('addr expr \<times> 'addr expr list) \<Rightarrow> ('addr expr \<times> 'addr expr list) \<Rightarrow> bool"
where "\<tau>Red0t P t h \<equiv> (\<tau>Red0 P t h)^++"

lemma \<tau>move0_\<tau>moves0_intros:
  fixes e e1 e2 e' :: "('a, 'b, 'addr) exp" and es :: "('a, 'b, 'addr) exp list"
  shows \<tau>move0NewArray: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (newA T\<lfloor>e\<rceil>)"
  and \<tau>move0Cast: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (Cast U e)"
  and \<tau>move0CastRed: "\<tau>move0 P h (Cast U (Val v))"
  and \<tau>move0InstanceOf: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (e instanceof T)"
  and \<tau>move0InstanceOfRed: "\<tau>move0 P h ((Val v) instanceof T)"
  and \<tau>move0BinOp1: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (e\<guillemotleft>bop\<guillemotright>e')"
  and \<tau>move0BinOp2: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (Val v\<guillemotleft>bop\<guillemotright>e)"
  and \<tau>move0BinOp: "\<tau>move0 P h (Val v\<guillemotleft>bop\<guillemotright>Val v')"
  and \<tau>move0Var: "\<tau>move0 P h (Var V)"
  and \<tau>move0LAss: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (V := e)"
  and \<tau>move0LAssRed: "\<tau>move0 P h (V := Val v)"
  and \<tau>move0AAcc1: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (e\<lfloor>e'\<rceil>)"
  and \<tau>move0AAcc2: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (Val v\<lfloor>e\<rceil>)"
  and \<tau>move0AAss1: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (e\<lfloor>e1\<rceil> := e2)"
  and \<tau>move0AAss2: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (Val v\<lfloor>e\<rceil> := e')"
  and \<tau>move0AAss3: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (Val v\<lfloor>Val v'\<rceil> := e)"
  and \<tau>move0ALength: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (e\<bullet>length)"
  and \<tau>move0FAcc: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (e\<bullet>F{D})"
  and \<tau>move0FAss1: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (FAss e F D e')"
  and \<tau>move0FAss2: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (Val v\<bullet>F{D} := e)"
  and \<tau>move0CAS1: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (e\<bullet>compareAndSwap(D\<bullet>F, e', e''))"
  and \<tau>move0CAS2: "\<tau>move0 P h e' \<Longrightarrow> \<tau>move0 P h (Val v\<bullet>compareAndSwap(D\<bullet>F, e', e''))"
  and \<tau>move0CAS3: "\<tau>move0 P h e'' \<Longrightarrow> \<tau>move0 P h (Val v\<bullet>compareAndSwap(D\<bullet>F, Val v', e''))"
  and \<tau>move0CallObj: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (e\<bullet>M(es))"
  and \<tau>move0CallParams: "\<tau>moves0 P h es \<Longrightarrow> \<tau>move0 P h (Val v\<bullet>M(es))"
  and \<tau>move0Call: "(\<And>T C Ts Tr D. \<lbrakk> typeof\<^bsub>h\<^esub> v = \<lfloor>T\<rfloor>; class_type_of' T = \<lfloor>C\<rfloor>; P \<turnstile> C sees M:Ts\<rightarrow>Tr = Native in D \<rbrakk> \<Longrightarrow> \<tau>external_defs D M) \<Longrightarrow> \<tau>move0 P h (Val v\<bullet>M(map Val vs))"
  and \<tau>move0Block: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h {V:T=vo; e}"
  and \<tau>move0BlockRed: "\<tau>move0 P h {V:T=vo; Val v}"
  and \<tau>move0Sync: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (sync\<^bsub>V'\<^esub> (e) e')"
  and \<tau>move0InSync: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (insync\<^bsub>V'\<^esub> (a) e)"
  and \<tau>move0Seq: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (e;;e')"
  and \<tau>move0SeqRed: "\<tau>move0 P h (Val v;; e')"
  and \<tau>move0Cond: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (if (e) e1 else e2)"
  and \<tau>move0CondRed: "\<tau>move0 P h (if (Val v) e1 else e2)"
  and \<tau>move0WhileRed: "\<tau>move0 P h (while (e) e')"
  and \<tau>move0Throw: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (throw e)"
  and \<tau>move0ThrowNull: "\<tau>move0 P h (throw null)"
  and \<tau>move0Try: "\<tau>move0 P h e \<Longrightarrow> \<tau>move0 P h (try e catch(C V) e')"
  and \<tau>move0TryRed: "\<tau>move0 P h (try Val v catch(C V) e)"
  and \<tau>move0TryThrow: "\<tau>move0 P h (try Throw a catch(C V) e)"
  and \<tau>move0NewArrayThrow: "\<tau>move0 P h (newA T\<lfloor>Throw a\<rceil>)"
  and \<tau>move0CastThrow: "\<tau>move0 P h (Cast T (Throw a))"
  and \<tau>move0CInstanceOfThrow: "\<tau>move0 P h ((Throw a) instanceof T)"
  and \<tau>move0BinOpThrow1: "\<tau>move0 P h (Throw a \<guillemotleft>bop\<guillemotright> e')"
  and \<tau>move0BinOpThrow2: "\<tau>move0 P h (Val v \<guillemotleft>bop\<guillemotright> Throw a)"
  and \<tau>move0LAssThrow: "\<tau>move0 P h (V:=(Throw a))"
  and \<tau>move0AAccThrow1: "\<tau>move0 P h (Throw a\<lfloor>e\<rceil>)"
  and \<tau>move0AAccThrow2: "\<tau>move0 P h (Val v\<lfloor>Throw a\<rceil>)"
  and \<tau>move0AAssThrow1: "\<tau>move0 P h (AAss (Throw a) e e')"
  and \<tau>move0AAssThrow2: "\<tau>move0 P h (AAss (Val v) (Throw a) e')"
  and \<tau>move0AAssThrow3: "\<tau>move0 P h (AAss (Val v) (Val v') (Throw a))"
  and \<tau>move0ALengthThrow: "\<tau>move0 P h (Throw a\<bullet>length)"
  and \<tau>move0FAccThrow: "\<tau>move0 P h (Throw a\<bullet>F{D})"
  and \<tau>move0FAssThrow1: "\<tau>move0 P h (Throw a\<bullet>F{D} := e)"
  and \<tau>move0FAssThrow2: "\<tau>move0 P h (FAss (Val v) F D (Throw a))"
  and \<tau>move0CallThrowObj: "\<tau>move0 P h (Throw a\<bullet>M(es))"
  and \<tau>move0CallThrowParams: "\<tau>move0 P h (Val v\<bullet>M(map Val vs @ Throw a # es))"
  and \<tau>move0BlockThrow: "\<tau>move0 P h {V:T=vo; Throw a}"
  and \<tau>move0SyncThrow: "\<tau>move0 P h (sync\<^bsub>V'\<^esub> (Throw a) e)"
  and \<tau>move0SeqThrow: "\<tau>move0 P h (Throw a;;e)"
  and \<tau>move0CondThrow: "\<tau>move0 P h (if (Throw a) e1 else e2)"
  and \<tau>move0ThrowThrow: "\<tau>move0 P h (throw (Throw a))"

  and \<tau>moves0Hd: "\<tau>move0 P h e \<Longrightarrow> \<tau>moves0 P h (e # es)"
  and \<tau>moves0Tl: "\<tau>moves0 P h es \<Longrightarrow> \<tau>moves0 P h (Val v # es)"
by auto

lemma \<tau>moves0_map_Val [iff]:
  "\<not> \<tau>moves0 P h (map Val vs)"
by(induct vs) auto

lemma \<tau>moves0_map_Val_append [simp]:
  "\<tau>moves0 P h (map Val vs @ es) = \<tau>moves0 P h es"
by(induct vs)(auto)

lemma no_reds_map_Val_Throw [simp]:
  "extTA,P,t \<turnstile> \<langle>map Val vs @ Throw a # es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> = False"
by(induct vs arbitrary: es')(auto elim: reds.cases)

lemma assumes [simp]: "extTA \<epsilon> = \<epsilon>"
  shows red_\<tau>_taD: "\<lbrakk> extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<tau>move0 P (hp s) e \<rbrakk> \<Longrightarrow> ta = \<epsilon>"
  and reds_\<tau>_taD: "\<lbrakk> extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; \<tau>moves0 P (hp s) es \<rbrakk> \<Longrightarrow> ta = \<epsilon>"
apply(induct rule: red_reds.inducts)
apply(fastforce simp add: map_eq_append_conv \<tau>external'_def \<tau>external_def dest: \<tau>external'_red_external_TA_empty)+
done

lemma \<tau>move0_heap_unchanged: "\<lbrakk> extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<tau>move0 P (hp s) e \<rbrakk> \<Longrightarrow> hp s' = hp s"
  and \<tau>moves0_heap_unchanged: "\<lbrakk> extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; \<tau>moves0 P (hp s) es \<rbrakk> \<Longrightarrow> hp s' = hp s"
apply(induct rule: red_reds.inducts)
apply(auto)
apply(fastforce simp add: map_eq_append_conv \<tau>external'_def \<tau>external_def dest: \<tau>external'_red_external_heap_unchanged)+
done

lemma \<tau>Move0_iff:
  "\<tau>Move0 P h ees \<longleftrightarrow> (let (e, _) = ees in \<tau>move0 P h e \<or> final e)"
by(cases ees)(simp)

lemma no_call_simps [simp]:
  "no_call P h (new C) = True"
  "no_call P h (newA T\<lfloor>e\<rceil>) = no_call P h e"
  "no_call P h (Cast T e) = no_call P h e"
  "no_call P h (e instanceof T) = no_call P h e"
  "no_call P h (Val v) = True"
  "no_call P h (Var V) = True"
  "no_call P h (V := e) = no_call P h e"
  "no_call P h (e \<guillemotleft>bop\<guillemotright> e') = (if is_val e then no_call P h e' else no_call P h e)"
  "no_call P h (a\<lfloor>i\<rceil>) = (if is_val a then no_call P h i else no_call P h a)"
  "no_call P h (AAss a i e) = (if is_val a then (if is_val i then no_call P h e else no_call P h i) else no_call P h a)"
  "no_call P h (a\<bullet>length) = no_call P h a"
  "no_call P h (e\<bullet>F{D}) = no_call P h e"
  "no_call P h (FAss e F D e') = (if is_val e then no_call P h e' else no_call P h e)"
  "no_call P h (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) = (if is_val e then (if is_val e' then no_call P h e'' else no_call P h e') else no_call P h e)"
  "no_call P h (e\<bullet>M(es)) = (if is_val e then (if is_vals es \<and> is_addr e then synthesized_call P h (THE a. e = addr a, M, THE vs. es = map Val vs) else no_calls P h es) else no_call P h e)"
  "no_call P h ({V:T=vo; e}) = no_call P h e"
  "no_call P h (sync\<^bsub>V'\<^esub> (e) e') = no_call P h e"
  "no_call P h (insync\<^bsub>V'\<^esub> (ad) e) = no_call P h e"
  "no_call P h (e;;e') = no_call P h e"
  "no_call P h (if (e) e1 else e2) = no_call P h e"
  "no_call P h (while(e) e') = True"
  "no_call P h (throw e) = no_call P h e"
  "no_call P h (try e catch(C V) e') = no_call P h e"
by(auto simp add: no_call_def no_calls_def)

lemma no_calls_simps [simp]:
  "no_calls P h [] = True"
  "no_calls P h (e # es) = (if is_val e then no_calls P h es else no_call P h e)"
by(simp_all add: no_call_def no_calls_def)

lemma no_calls_map_Val [simp]:
  "no_calls P h (map Val vs)"
by(induct vs) simp_all

lemma assumes nfin: "\<not> final e'"
 shows inline_call_\<tau>move0_inv: "call e = \<lfloor>aMvs\<rfloor> \<Longrightarrow> \<tau>move0 P h (inline_call e' e) = \<tau>move0 P h e'"
  and inline_calls_\<tau>moves0_inv: "calls es = \<lfloor>aMvs\<rfloor> \<Longrightarrow> \<tau>moves0 P h (inline_calls e' es) = \<tau>move0 P h e'"
apply(induct e and es rule: \<tau>move0.induct \<tau>moves0.induct)
apply(insert nfin)
apply simp_all
apply auto
done

lemma \<tau>red0_iff [iff]:
  "\<tau>red0 extTA P t h (e, xs) (e', xs') = (extTA,P,t \<turnstile> \<langle>e, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h, xs')\<rangle> \<and> \<tau>move0 P h e \<and> no_call P h e)"
by(simp add: \<tau>red0_def)

lemma \<tau>reds0_iff [iff]:
  "\<tau>reds0 extTA P t h (es, xs) (es', xs') =
  (extTA,P,t \<turnstile> \<langle>es, (h, xs)\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es', (h, xs')\<rangle> \<and> \<tau>moves0 P h es \<and> no_calls P h es)"
by(simp add: \<tau>reds0_def)

lemma \<tau>red0t_1step:
  "\<lbrakk> extTA,P,t \<turnstile> \<langle>e, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h, xs')\<rangle>; \<tau>move0 P h e; no_call P h e \<rbrakk>
  \<Longrightarrow> \<tau>red0t extTA P t h (e, xs) (e', xs')"
by(blast intro: tranclp.r_into_trancl)

lemma \<tau>red0t_2step:
  "\<lbrakk> extTA,P,t \<turnstile> \<langle>e, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h, xs')\<rangle>; \<tau>move0 P h e; no_call P h e;
     extTA,P,t \<turnstile> \<langle>e', (h, xs')\<rangle> -\<epsilon>\<rightarrow> \<langle>e'', (h, xs'')\<rangle>; \<tau>move0 P h e'; no_call P h e' \<rbrakk>
  \<Longrightarrow> \<tau>red0t extTA P t h (e, xs) (e'', xs'')"
by(blast intro: tranclp.trancl_into_trancl[OF \<tau>red0t_1step])

lemma \<tau>red1t_3step:
  "\<lbrakk> extTA,P,t \<turnstile> \<langle>e, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h, xs')\<rangle>; \<tau>move0 P h e; no_call P h e; 
     extTA,P,t \<turnstile> \<langle>e', (h, xs')\<rangle> -\<epsilon>\<rightarrow> \<langle>e'', (h, xs'')\<rangle>; \<tau>move0 P h e'; no_call P h e';
     extTA,P,t \<turnstile> \<langle>e'', (h, xs'')\<rangle> -\<epsilon>\<rightarrow> \<langle>e''', (h, xs''')\<rangle>; \<tau>move0 P h e''; no_call P h e'' \<rbrakk>
  \<Longrightarrow> \<tau>red0t extTA P t h (e, xs) (e''', xs''')"
by(blast intro: tranclp.trancl_into_trancl[OF \<tau>red0t_2step])

lemma \<tau>reds0t_1step:
  "\<lbrakk> extTA,P,t \<turnstile> \<langle>es, (h, xs)\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es', (h, xs')\<rangle>; \<tau>moves0 P h es; no_calls P h es \<rbrakk>
  \<Longrightarrow> \<tau>reds0t extTA P t h (es, xs) (es', xs')"
by(blast intro: tranclp.r_into_trancl)

lemma \<tau>reds0t_2step:
  "\<lbrakk> extTA,P,t \<turnstile> \<langle>es, (h, xs)\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es', (h, xs')\<rangle>; \<tau>moves0 P h es; no_calls P h es; 
     extTA,P,t \<turnstile> \<langle>es', (h, xs')\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es'', (h, xs'')\<rangle>; \<tau>moves0 P h es'; no_calls P h es' \<rbrakk>
  \<Longrightarrow> \<tau>reds0t extTA P t h (es, xs) (es'', xs'')"
by(blast intro: tranclp.trancl_into_trancl[OF \<tau>reds0t_1step])

lemma \<tau>reds0t_3step:
  "\<lbrakk> extTA,P,t \<turnstile> \<langle>es, (h, xs)\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es', (h, xs')\<rangle>; \<tau>moves0 P h es; no_calls P h es; 
     extTA,P,t \<turnstile> \<langle>es', (h, xs')\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es'', (h, xs'')\<rangle>; \<tau>moves0 P h es'; no_calls P h es';
     extTA,P,t \<turnstile> \<langle>es'', (h, xs'')\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es''', (h, xs''')\<rangle>; \<tau>moves0 P h es''; no_calls P h es'' \<rbrakk>
  \<Longrightarrow> \<tau>reds0t extTA P t h (es, xs) (es''', xs''')"
by(blast intro: tranclp.trancl_into_trancl[OF \<tau>reds0t_2step])

lemma \<tau>red0r_1step:
  "\<lbrakk> extTA,P,t \<turnstile> \<langle>e, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h, xs')\<rangle>; \<tau>move0 P h e; no_call P h e \<rbrakk>
  \<Longrightarrow> \<tau>red0r extTA P t h (e, xs) (e', xs')"
by(blast intro: r_into_rtranclp)

lemma \<tau>red0r_2step:
  "\<lbrakk> extTA,P,t \<turnstile> \<langle>e, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h, xs')\<rangle>; \<tau>move0 P h e; no_call P h e;
     extTA,P,t \<turnstile> \<langle>e', (h, xs')\<rangle> -\<epsilon>\<rightarrow> \<langle>e'', (h, xs'')\<rangle>; \<tau>move0 P h e'; no_call P h e' \<rbrakk>
  \<Longrightarrow> \<tau>red0r extTA P t h (e, xs) (e'', xs'')"
by(blast intro: rtranclp.rtrancl_into_rtrancl[OF \<tau>red0r_1step])

lemma \<tau>red0r_3step:
  "\<lbrakk> extTA,P,t \<turnstile> \<langle>e, (h, xs)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h, xs')\<rangle>; \<tau>move0 P h e; no_call P h e; 
     extTA,P,t \<turnstile> \<langle>e', (h, xs')\<rangle> -\<epsilon>\<rightarrow> \<langle>e'', (h, xs'')\<rangle>; \<tau>move0 P h e'; no_call P h e';
     extTA,P,t \<turnstile> \<langle>e'', (h, xs'')\<rangle> -\<epsilon>\<rightarrow> \<langle>e''', (h, xs''')\<rangle>; \<tau>move0 P h e''; no_call P h e'' \<rbrakk>
  \<Longrightarrow> \<tau>red0r extTA P t h (e, xs) (e''', xs''')"
by(blast intro: rtranclp.rtrancl_into_rtrancl[OF \<tau>red0r_2step])

lemma \<tau>reds0r_1step:
  "\<lbrakk> extTA,P,t \<turnstile> \<langle>es, (h, xs)\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es', (h, xs')\<rangle>; \<tau>moves0 P h es; no_calls P h es \<rbrakk>
  \<Longrightarrow> \<tau>reds0r extTA P t h (es, xs) (es', xs')"
by(blast intro: r_into_rtranclp)

lemma \<tau>reds0r_2step:
  "\<lbrakk> extTA,P,t \<turnstile> \<langle>es, (h, xs)\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es', (h, xs')\<rangle>; \<tau>moves0 P h es; no_calls P h es; 
     extTA,P,t \<turnstile> \<langle>es', (h, xs')\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es'', (h, xs'')\<rangle>; \<tau>moves0 P h es'; no_calls P h es' \<rbrakk>
  \<Longrightarrow> \<tau>reds0r extTA P t h (es, xs) (es'', xs'')"
by(blast intro: rtranclp.rtrancl_into_rtrancl[OF \<tau>reds0r_1step])

lemma \<tau>reds0r_3step:
  "\<lbrakk> extTA,P,t \<turnstile> \<langle>es, (h, xs)\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es', (h, xs')\<rangle>; \<tau>moves0 P h es; no_calls P h es; 
     extTA,P,t \<turnstile> \<langle>es', (h, xs')\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es'', (h, xs'')\<rangle>; \<tau>moves0 P h es'; no_calls P h es';
     extTA,P,t \<turnstile> \<langle>es'', (h, xs'')\<rangle> [-\<epsilon>\<rightarrow>] \<langle>es''', (h, xs''')\<rangle>; \<tau>moves0 P h es''; no_calls P h es'' \<rbrakk>
  \<Longrightarrow> \<tau>reds0r extTA P t h (es, xs) (es''', xs''')"
by(blast intro: rtranclp.rtrancl_into_rtrancl[OF \<tau>reds0r_2step])

lemma \<tau>red0t_inj_\<tau>reds0t:
  "\<tau>red0t extTA P t h (e, xs) (e', xs')
  \<Longrightarrow> \<tau>reds0t extTA P t h (e # es, xs) (e' # es, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl ListRed1)

lemma \<tau>reds0t_cons_\<tau>reds0t:
  "\<tau>reds0t extTA P t h (es, xs) (es', xs')
  \<Longrightarrow> \<tau>reds0t extTA P t h (Val v # es, xs) (Val v # es', xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl ListRed2)

lemma \<tau>red0r_inj_\<tau>reds0r:
  "\<tau>red0r extTA P t h (e, xs) (e', xs')
  \<Longrightarrow> \<tau>reds0r extTA P t h (e # es, xs) (e' # es, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl ListRed1)

lemma \<tau>reds0r_cons_\<tau>reds0r:
  "\<tau>reds0r extTA P t h (es, xs) (es', xs') 
  \<Longrightarrow> \<tau>reds0r extTA P t h (Val v # es, xs) (Val v # es', xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl ListRed2)

lemma NewArray_\<tau>red0t_xt:
  "\<tau>red0t extTA P t h (e, xs) (e', xs')
  \<Longrightarrow> \<tau>red0t extTA P t h (newA T\<lfloor>e\<rceil>, xs) (newA T\<lfloor>e'\<rceil>, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl NewArrayRed)

lemma Cast_\<tau>red0t_xt:
  "\<tau>red0t extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0t extTA P t h (Cast T e, xs) (Cast T e', xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl CastRed)

lemma InstanceOf_\<tau>red0t_xt:
  "\<tau>red0t extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0t extTA P t h (e instanceof T, xs) (e' instanceof T, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl InstanceOfRed)

lemma BinOp_\<tau>red0t_xt1:
  "\<tau>red0t extTA P t h (e1, xs) (e1', xs') \<Longrightarrow> \<tau>red0t extTA P t h (e1 \<guillemotleft>bop\<guillemotright> e2, xs) (e1' \<guillemotleft>bop\<guillemotright> e2, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl BinOpRed1)

lemma BinOp_\<tau>red0t_xt2:
  "\<tau>red0t extTA P t h (e2, xs) (e2', xs') \<Longrightarrow> \<tau>red0t extTA P t h (Val v \<guillemotleft>bop\<guillemotright> e2, xs) (Val v \<guillemotleft>bop\<guillemotright> e2', xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl BinOpRed2)

lemma LAss_\<tau>red0t:
  "\<tau>red0t extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0t extTA P t h (V := e, xs) (V := e', xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl LAssRed)

lemma AAcc_\<tau>red0t_xt1:
  "\<tau>red0t extTA P t h (a, xs) (a', xs') \<Longrightarrow> \<tau>red0t extTA P t h (a\<lfloor>i\<rceil>, xs) (a'\<lfloor>i\<rceil>, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl AAccRed1)

lemma AAcc_\<tau>red0t_xt2:
  "\<tau>red0t extTA P t h (i, xs) (i', xs') \<Longrightarrow> \<tau>red0t extTA P t h (Val a\<lfloor>i\<rceil>, xs) (Val a\<lfloor>i'\<rceil>, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl AAccRed2)

lemma AAss_\<tau>red0t_xt1:
  "\<tau>red0t extTA P t h (a, xs) (a', xs') \<Longrightarrow> \<tau>red0t extTA P t h (a\<lfloor>i\<rceil> := e, xs) (a'\<lfloor>i\<rceil> := e, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl AAssRed1)

lemma AAss_\<tau>red0t_xt2:
  "\<tau>red0t extTA P t h (i, xs) (i', xs') \<Longrightarrow> \<tau>red0t extTA P t h (Val a\<lfloor>i\<rceil> := e, xs) (Val a\<lfloor>i'\<rceil> := e, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl AAssRed2)

lemma AAss_\<tau>red0t_xt3:
  "\<tau>red0t extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0t extTA P t h (Val a\<lfloor>Val i\<rceil> := e, xs) (Val a\<lfloor>Val i\<rceil> := e', xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl AAssRed3)

lemma ALength_\<tau>red0t_xt:
  "\<tau>red0t extTA P t h (a, xs) (a', xs') \<Longrightarrow> \<tau>red0t extTA P t h (a\<bullet>length, xs) (a'\<bullet>length, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl ALengthRed)

lemma FAcc_\<tau>red0t_xt:
  "\<tau>red0t extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0t extTA P t h (e\<bullet>F{D}, xs) (e'\<bullet>F{D}, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl FAccRed)

lemma FAss_\<tau>red0t_xt1:
  "\<tau>red0t extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0t extTA P t h (e\<bullet>F{D} := e2, xs) (e'\<bullet>F{D} := e2, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl FAssRed1)

lemma FAss_\<tau>red0t_xt2:
  "\<tau>red0t extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0t extTA P t h (Val v\<bullet>F{D} := e, xs) (Val v\<bullet>F{D} := e', xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl FAssRed2)

lemma CAS_\<tau>red0t_xt1:
  "\<tau>red0t extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0t extTA P t h (e\<bullet>compareAndSwap(D\<bullet>F, e2, e3), xs) (e'\<bullet>compareAndSwap(D\<bullet>F, e2, e3), xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl CASRed1)

lemma CAS_\<tau>red0t_xt2:
  "\<tau>red0t extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0t extTA P t h (Val v\<bullet>compareAndSwap(D\<bullet>F, e, e3), xs) (Val v\<bullet>compareAndSwap(D\<bullet>F, e', e3), xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl CASRed2)

lemma CAS_\<tau>red0t_xt3:
  "\<tau>red0t extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0t extTA P t h (Val v\<bullet>compareAndSwap(D\<bullet>F, Val v', e), xs) (Val v\<bullet>compareAndSwap(D\<bullet>F, Val v', e'), xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl CASRed3)

lemma Call_\<tau>red0t_obj:
  "\<tau>red0t extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0t extTA P t h (e\<bullet>M(ps), xs) (e'\<bullet>M(ps), xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl CallObj)

lemma Call_\<tau>red0t_param:
  "\<tau>reds0t extTA P t h (es, xs) (es', xs') \<Longrightarrow> \<tau>red0t extTA P t h (Val v\<bullet>M(es), xs) (Val v\<bullet>M(es'), xs')"
by(induct rule: tranclp_induct2)(fastforce intro: tranclp.trancl_into_trancl CallParams)+

lemma Block_\<tau>red0t_xt:
  "\<tau>red0t extTA P t h (e, xs(V := vo)) (e', xs') \<Longrightarrow> \<tau>red0t extTA P t h ({V:T=vo; e}, xs) ({V:T=xs' V; e'}, xs'(V := xs V))"
proof(induct rule: tranclp_induct2)
  case base thus ?case by(auto intro: BlockRed simp del: fun_upd_apply)
next
  case (step e' xs' e'' xs'')
  from \<open>\<tau>red0 extTA P t h (e', xs') (e'', xs'')\<close> 
  have "extTA,P,t \<turnstile> \<langle>e',(h, xs')\<rangle> -\<epsilon>\<rightarrow> \<langle>e'',(h, xs'')\<rangle>" "\<tau>move0 P h e'" "no_call P h e'" by auto
  hence "extTA,P,t \<turnstile> \<langle>e',(h, xs'(V := xs V, V := xs' V))\<rangle> -\<epsilon>\<rightarrow> \<langle>e'',(h, xs'')\<rangle>" by simp
  from BlockRed[OF this, of T] \<open>\<tau>move0 P h e'\<close> \<open>no_call P h e'\<close>
  have "\<tau>red0 extTA P t h ({V:T=xs' V; e'}, xs'(V := xs V)) ({V:T=xs'' V; e''}, xs''(V := xs V))" by(auto)
  with \<open>\<tau>red0t extTA P t h ({V:T=vo; e}, xs) ({V:T=xs' V; e'}, xs'(V := xs V))\<close> show ?case ..
qed

lemma Sync_\<tau>red0t_xt:
  "\<tau>red0t extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0t extTA P t h (sync\<^bsub>V\<^esub> (e) e2, xs) (sync\<^bsub>V\<^esub> (e') e2, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl SynchronizedRed1)

lemma InSync_\<tau>red0t_xt:
  "\<tau>red0t extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0t extTA P t h (insync\<^bsub>V\<^esub> (a) e, xs) (insync\<^bsub>V\<^esub> (a) e', xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl SynchronizedRed2)

lemma Seq_\<tau>red0t_xt:
  "\<tau>red0t extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0t extTA P t h (e;;e2, xs) (e';;e2, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl SeqRed)

lemma Cond_\<tau>red0t_xt:
  "\<tau>red0t extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0t extTA P t h (if (e) e1 else e2, xs) (if (e') e1 else e2, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl CondRed)

lemma Throw_\<tau>red0t_xt:
  "\<tau>red0t extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0t extTA P t h (throw e, xs) (throw e', xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl ThrowRed)

lemma Try_\<tau>red0t_xt:
  "\<tau>red0t extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0t extTA P t h (try e catch(C V) e2, xs) (try e' catch(C V) e2, xs')"
by(induct rule: tranclp_induct2)(auto intro: tranclp.trancl_into_trancl TryRed)

lemma NewArray_\<tau>red0r_xt:
  "\<tau>red0r extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0r extTA P t h (newA T\<lfloor>e\<rceil>, xs) (newA T\<lfloor>e'\<rceil>, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl NewArrayRed)

lemma Cast_\<tau>red0r_xt:
  "\<tau>red0r extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0r extTA P t h (Cast T e, xs) (Cast T e', xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl CastRed)

lemma InstanceOf_\<tau>red0r_xt:
  "\<tau>red0r extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0r extTA P t h (e instanceof T, xs) (e' instanceof T, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl InstanceOfRed)

lemma BinOp_\<tau>red0r_xt1:
  "\<tau>red0r extTA P t h (e1, xs) (e1', xs') \<Longrightarrow> \<tau>red0r extTA P t h (e1 \<guillemotleft>bop\<guillemotright> e2, xs) (e1' \<guillemotleft>bop\<guillemotright> e2, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl BinOpRed1)

lemma BinOp_\<tau>red0r_xt2:
  "\<tau>red0r extTA P t h (e2, xs) (e2', xs') \<Longrightarrow> \<tau>red0r extTA P t h (Val v \<guillemotleft>bop\<guillemotright> e2, xs) (Val v \<guillemotleft>bop\<guillemotright> e2', xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl BinOpRed2)

lemma LAss_\<tau>red0r:
  "\<tau>red0r extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0r extTA P t h (V := e, xs) (V := e', xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl LAssRed)

lemma AAcc_\<tau>red0r_xt1:
  "\<tau>red0r extTA P t h (a, xs) (a', xs') \<Longrightarrow> \<tau>red0r extTA P t h (a\<lfloor>i\<rceil>, xs) (a'\<lfloor>i\<rceil>, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl AAccRed1)

lemma AAcc_\<tau>red0r_xt2:
  "\<tau>red0r extTA P t h (i, xs) (i', xs') \<Longrightarrow> \<tau>red0r extTA P t h (Val a\<lfloor>i\<rceil>, xs) (Val a\<lfloor>i'\<rceil>, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl AAccRed2)

lemma AAss_\<tau>red0r_xt1:
  "\<tau>red0r extTA P t h (a, xs) (a', xs') \<Longrightarrow> \<tau>red0r extTA P t h (a\<lfloor>i\<rceil> := e, xs) (a'\<lfloor>i\<rceil> := e, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl AAssRed1)

lemma AAss_\<tau>red0r_xt2:
  "\<tau>red0r extTA P t h (i, xs) (i', xs') \<Longrightarrow> \<tau>red0r extTA P t h (Val a\<lfloor>i\<rceil> := e, xs) (Val a\<lfloor>i'\<rceil> := e, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl AAssRed2)

lemma AAss_\<tau>red0r_xt3:
  "\<tau>red0r extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0r extTA P t h (Val a\<lfloor>Val i\<rceil> := e, xs) (Val a\<lfloor>Val i\<rceil> := e', xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl AAssRed3)

lemma ALength_\<tau>red0r_xt:
  "\<tau>red0r extTA P t h (a, xs) (a', xs') \<Longrightarrow> \<tau>red0r extTA P t h (a\<bullet>length, xs) (a'\<bullet>length, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl ALengthRed)

lemma FAcc_\<tau>red0r_xt:
  "\<tau>red0r extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0r extTA P t h (e\<bullet>F{D}, xs) (e'\<bullet>F{D}, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl FAccRed)

lemma FAss_\<tau>red0r_xt1:
  "\<tau>red0r extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0r extTA P t h (e\<bullet>F{D} := e2, xs) (e'\<bullet>F{D} := e2, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl FAssRed1)

lemma FAss_\<tau>red0r_xt2:
  "\<tau>red0r extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0r extTA P t h (Val v\<bullet>F{D} := e, xs) (Val v\<bullet>F{D} := e', xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl FAssRed2)

lemma CAS_\<tau>red0r_xt1:
  "\<tau>red0r extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0r extTA P t h (e\<bullet>compareAndSwap(D\<bullet>F, e2, e3), xs) (e'\<bullet>compareAndSwap(D\<bullet>F, e2, e3), xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl CASRed1)

lemma CAS_\<tau>red0r_xt2:
  "\<tau>red0r extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0r extTA P t h (Val v\<bullet>compareAndSwap(D\<bullet>F, e, e3), xs) (Val v\<bullet>compareAndSwap(D\<bullet>F, e', e3), xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl CASRed2)

lemma CAS_\<tau>red0r_xt3:
  "\<tau>red0r extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0r extTA P t h (Val v\<bullet>compareAndSwap(D\<bullet>F, Val v', e), xs) (Val v\<bullet>compareAndSwap(D\<bullet>F, Val v', e'), xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl CASRed3)

lemma Call_\<tau>red0r_obj:
  "\<tau>red0r extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0r extTA P t h (e\<bullet>M(ps), xs) (e'\<bullet>M(ps), xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl CallObj)

lemma Call_\<tau>red0r_param:
  "\<tau>reds0r extTA P t h (es, xs) (es', xs') \<Longrightarrow> \<tau>red0r extTA P t h (Val v\<bullet>M(es), xs) (Val v\<bullet>M(es'), xs')"
by(induct rule: rtranclp_induct2)(fastforce intro: rtranclp.rtrancl_into_rtrancl CallParams)+

lemma Block_\<tau>red0r_xt:
  "\<tau>red0r extTA P t h (e, xs(V := vo)) (e', xs') \<Longrightarrow> \<tau>red0r extTA P t h ({V:T=vo; e}, xs) ({V:T=xs' V; e'}, xs'(V := xs V))"
proof(induct rule: rtranclp_induct2)
  case refl thus ?case by(simp del: fun_upd_apply)(auto simp add: fun_upd_apply)
next
  case (step e' xs' e'' xs'')
  from \<open>\<tau>red0 extTA P t h (e', xs') (e'', xs'')\<close> 
  have "extTA,P,t \<turnstile> \<langle>e',(h, xs')\<rangle> -\<epsilon>\<rightarrow> \<langle>e'',(h, xs'')\<rangle>" "\<tau>move0 P h e'" "no_call P h e'" by auto
  hence "extTA,P,t \<turnstile> \<langle>e',(h, xs'(V := xs V, V := xs' V))\<rangle> -\<epsilon>\<rightarrow> \<langle>e'',(h, xs'')\<rangle>" by simp
  from BlockRed[OF this, of T] \<open>\<tau>move0 P h e'\<close> \<open>no_call P h e'\<close>
  have "\<tau>red0 extTA P t h ({V:T=xs' V; e'}, xs'(V := xs V)) ({V:T=xs'' V; e''}, xs''(V := xs V))" by auto
  with \<open>\<tau>red0r extTA P t h ({V:T=vo; e}, xs) ({V:T=xs' V; e'}, xs'(V := xs V))\<close> show ?case ..
qed

lemma Sync_\<tau>red0r_xt:
  "\<tau>red0r extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0r extTA P t h (sync\<^bsub>V\<^esub> (e) e2, xs) (sync\<^bsub>V\<^esub> (e') e2, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl SynchronizedRed1)

lemma InSync_\<tau>red0r_xt:
  "\<tau>red0r extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0r extTA P t h (insync\<^bsub>V\<^esub> (a) e, xs) (insync\<^bsub>V\<^esub> (a) e', xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl SynchronizedRed2)

lemma Seq_\<tau>red0r_xt:
  "\<tau>red0r extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0r extTA P t h (e;;e2, xs) (e';;e2, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl SeqRed)

lemma Cond_\<tau>red0r_xt:
  "\<tau>red0r extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0r extTA P t h (if (e) e1 else e2, xs) (if (e') e1 else e2, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl CondRed)

lemma Throw_\<tau>red0r_xt:
  "\<tau>red0r extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0r extTA P t h (throw e, xs) (throw e', xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl ThrowRed)

lemma Try_\<tau>red0r_xt:
  "\<tau>red0r extTA P t h (e, xs) (e', xs') \<Longrightarrow> \<tau>red0r extTA P t h (try e catch(C V) e2, xs) (try e' catch(C V) e2, xs')"
by(induct rule: rtranclp_induct2)(auto intro: rtranclp.rtrancl_into_rtrancl TryRed)

lemma \<tau>Red0_conv [iff]:
  "\<tau>Red0 P t h (e, es) (e', es') = (P,t \<turnstile>0 \<langle>e/es, h\<rangle> -\<epsilon>\<rightarrow> \<langle>e'/es', h\<rangle> \<and> \<tau>Move0 P h (e, es))"
by(simp add: \<tau>Red0_def)

lemma \<tau>red0r_lcl_incr:
  "\<tau>red0r extTA P t h (e, xs) (e', xs') \<Longrightarrow> dom xs \<subseteq> dom xs'"
by(induct rule: rtranclp_induct2)(auto dest: red_lcl_incr del: subsetI)

lemma \<tau>red0t_lcl_incr:
  "\<tau>red0t extTA P t h (e, xs) (e', xs') \<Longrightarrow> dom xs \<subseteq> dom xs'"
by(rule \<tau>red0r_lcl_incr)(rule tranclp_into_rtranclp)

lemma \<tau>red0r_dom_lcl:
  assumes wwf: "wwf_J_prog P"
  shows "\<tau>red0r extTA P t h (e, xs) (e', xs') \<Longrightarrow> dom xs' \<subseteq> dom xs \<union> fv e"
apply(induct rule: converse_rtranclp_induct2)
 apply blast
apply(clarsimp del: subsetI)
apply(frule red_dom_lcl)
 apply(drule red_fv_subset[OF wwf])
apply auto
done

lemma \<tau>red0t_dom_lcl:
  assumes wwf: "wwf_J_prog P"
  shows "\<tau>red0t extTA P t h (e, xs) (e', xs') \<Longrightarrow> dom xs' \<subseteq> dom xs \<union> fv e"
by(rule \<tau>red0r_dom_lcl[OF wwf])(rule tranclp_into_rtranclp)

lemma \<tau>red0r_fv_subset:
  assumes wwf: "wwf_J_prog P"
  shows "\<tau>red0r extTA P t h (e, xs) (e', xs') \<Longrightarrow> fv e' \<subseteq> fv e"
by(induct rule: converse_rtranclp_induct2)(auto dest: red_fv_subset[OF wwf])

lemma \<tau>red0t_fv_subset:
  assumes wwf: "wwf_J_prog P"
  shows "\<tau>red0t extTA P t h (e, xs) (e', xs') \<Longrightarrow> fv e' \<subseteq> fv e"
by(rule \<tau>red0r_fv_subset[OF wwf])(rule tranclp_into_rtranclp)

lemma fixes e :: "('a, 'b, 'addr) exp" and es :: "('a, 'b, 'addr) exp list"
  shows \<tau>move0_callD: "call e = \<lfloor>(a, M, vs)\<rfloor> \<Longrightarrow> \<tau>move0 P h e \<longleftrightarrow> (synthesized_call P h (a, M, vs) \<longrightarrow> \<tau>external' P h a M)"
  and \<tau>moves0_callsD: "calls es = \<lfloor>(a, M, vs)\<rfloor> \<Longrightarrow> \<tau>moves0 P h es \<longleftrightarrow> (synthesized_call P h (a, M, vs) \<longrightarrow> \<tau>external' P h a M)"
apply(induct e and es rule: call.induct calls.induct)
apply(auto split: if_split_asm simp add: is_vals_conv)
apply(fastforce simp add: synthesized_call_def map_eq_append_conv \<tau>external'_def \<tau>external_def dest: sees_method_fun)+
done

lemma fixes e :: "('a, 'b, 'addr) exp" and es :: "('a, 'b, 'addr) exp list"
  shows \<tau>move0_not_call: "\<lbrakk> \<tau>move0 P h e; call e = \<lfloor>(a, M, vs)\<rfloor>; synthesized_call P h (a, M, vs) \<rbrakk> \<Longrightarrow> \<tau>external' P h a M"
  and \<tau>moves0_not_calls: "\<lbrakk> \<tau>moves0 P h es; calls es = \<lfloor>(a, M, vs)\<rfloor>; synthesized_call P h (a, M, vs) \<rbrakk> \<Longrightarrow> \<tau>external' P h a M"
apply(drule \<tau>move0_callD[where P=P and h=h], simp)
apply(drule \<tau>moves0_callsD[where P=P and h=h], simp)
done

lemma \<tau>red0_into_\<tau>Red0:
  assumes red: "\<tau>red0 (extTA2J0 P) P t h (e, Map.empty) (e', xs')"
  shows "\<tau>Red0 P t h (e, es) (e', es)"
proof -
  from red have red: "extTA2J0 P,P,t \<turnstile> \<langle>e, (h, Map.empty)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h, xs')\<rangle>"
    and "\<tau>move0 P h e" and "no_call P h e" by auto
  hence "P,t \<turnstile>0 \<langle>e/es,h\<rangle> -\<epsilon>\<rightarrow> \<langle>e'/es,h\<rangle>"
    by-(erule red0Red,auto simp add: no_call_def)
  thus ?thesis using \<open>\<tau>move0 P h e\<close> by(auto)
qed

lemma \<tau>red0r_into_\<tau>Red0r:
  assumes wwf: "wwf_J_prog P"
  shows
  "\<lbrakk> \<tau>red0r (extTA2J0 P) P t h (e, Map.empty) (e'', Map.empty); fv e = {} \<rbrakk>
  \<Longrightarrow> \<tau>Red0r P t h (e, es) (e'', es)"
proof(induct e xs\<equiv>"Map.empty :: 'addr locals" rule: converse_rtranclp_induct2)
  case refl show ?case by blast
next
  case (step e e' xs')
  from \<open>\<tau>red0 (extTA2J0 P) P t h (e, Map.empty) (e', xs')\<close>
  have red: "extTA2J0 P,P,t \<turnstile> \<langle>e, (h, Map.empty)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h, xs')\<rangle>"
    and "\<tau>move0 P h e"  and "no_call P h e" by auto
  from red_dom_lcl[OF red] \<open>fv e = {}\<close> 
  have "dom xs' = {}" by(auto split:if_split_asm)
  hence "xs' = Map.empty" by(auto)
  moreover
  from wwf red have "fv e' \<subseteq> fv e" by(rule red_fv_subset)
  with \<open>fv e = {}\<close> have "fv e' = {}" by blast
  ultimately have "\<tau>Red0r P t h (e', es) (e'', es)" by(rule step)
  moreover from red \<open>\<tau>move0 P h e\<close> \<open>xs' = Map.empty\<close> \<open>no_call P h e\<close>
  have "\<tau>Red0 P t h (e, es) (e', es)" by(auto simp add: no_call_def intro!: red0Red)
  ultimately show ?case by(blast intro: converse_rtranclp_into_rtranclp)
qed


lemma \<tau>red0t_into_\<tau>Red0t:
  assumes wwf: "wwf_J_prog P"
  shows
  "\<lbrakk> \<tau>red0t (extTA2J0 P) P t h (e, Map.empty) (e'', Map.empty); fv e = {} \<rbrakk>
  \<Longrightarrow> \<tau>Red0t P t h (e, es) (e'', es)"
proof(induct e xs\<equiv>"Map.empty :: 'addr locals" rule: converse_tranclp_induct2)
  case base thus ?case
    by(blast intro!: tranclp.r_into_trancl \<tau>red0_into_\<tau>Red0)
next
  case (step e e' xs')
  from \<open>\<tau>red0 (extTA2J0 P) P t h (e, Map.empty) (e', xs')\<close> 
  have red: "extTA2J0 P,P,t \<turnstile> \<langle>e, (h, Map.empty)\<rangle> -\<epsilon>\<rightarrow> \<langle>e', (h, xs')\<rangle>" and "\<tau>move0 P h e" and "no_call P h e" by auto
  from red_dom_lcl[OF red] \<open>fv e = {}\<close>
  have "dom xs' = {}" by(auto split:if_split_asm)
  hence "xs' = Map.empty" by auto
  moreover from wwf red have "fv e' \<subseteq> fv e" by(rule red_fv_subset)
  with \<open>fv e = {}\<close> have "fv e' = {}" by blast
  ultimately have "\<tau>Red0t P t h (e', es) (e'', es)" by(rule step)
  moreover from red \<open>\<tau>move0 P h e\<close> \<open>xs' = Map.empty\<close> \<open>no_call P h e\<close>
  have "\<tau>Red0 P t h (e, es) (e', es)" by(auto simp add: no_call_def intro!: red0Red)
  ultimately show ?case by(blast intro: tranclp_into_tranclp2)
qed

lemma \<tau>red0r_Val:
  "\<tau>red0r extTA P t h (Val v, xs) s' \<longleftrightarrow> s' = (Val v, xs)"
proof
  assume "\<tau>red0r extTA P t h (Val v, xs) s'"
  thus "s' = (Val v, xs)" by induct(auto)
qed auto

lemma \<tau>red0t_Val:
  "\<tau>red0t extTA P t h (Val v, xs) s' \<longleftrightarrow> False"
proof
  assume "\<tau>red0t extTA P t h (Val v, xs) s'"
  thus False by induct auto
qed auto

lemma \<tau>reds0r_map_Val:
  "\<tau>reds0r extTA P t h (map Val vs, xs) s' \<longleftrightarrow> s' = (map Val vs, xs)"
proof
  assume "\<tau>reds0r extTA P t h (map Val vs, xs) s'"
  thus "s' = (map Val vs, xs)" by induct auto
qed auto

lemma \<tau>reds0t_map_Val:
  "\<tau>reds0t extTA P t h (map Val vs, xs) s' \<longleftrightarrow> False"
proof
  assume "\<tau>reds0t extTA P t h (map Val vs, xs) s'"
  thus "False" by induct auto
qed auto

lemma Red_Suspend_is_call:
  "\<lbrakk> P,t \<turnstile>0 \<langle>e/exs, h\<rangle> -ta\<rightarrow> \<langle>e'/exs', h'\<rangle>; Suspend w \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<rbrakk> \<Longrightarrow> is_call e'"
by(auto elim!: red0.cases dest: red_Suspend_is_call simp add: is_call_def)


lemma red0_mthr: "multithreaded final_expr0 (mred0 P)"
by(unfold_locales)(auto elim!: red0.cases dest: red_new_thread_heap)

lemma red0_\<tau>mthr_wf: "\<tau>multithreaded_wf final_expr0 (mred0 P) (\<tau>MOVE0 P)"
proof -
  interpret multithreaded final_expr0 "mred0 P" by(rule red0_mthr)
  show ?thesis
  proof
    fix x1 m1 t ta1 x1' m1'
    assume "mred0 P t (x1, m1) ta1 (x1', m1')" "\<tau>MOVE0 P (x1, m1) ta1 (x1', m1')"
    thus "m1 = m1'" by(cases x1)(fastforce elim!: red0.cases dest: \<tau>move0_heap_unchanged)
  qed(simp add: split_beta)
qed

lemma red_\<tau>mthr_wf: "\<tau>multithreaded_wf final_expr (mred P) (\<tau>MOVE P)"
proof
  fix x1 m1 t ta1 x1' m1'
  assume "mred P t (x1, m1) ta1 (x1', m1')" "\<tau>MOVE P (x1, m1) ta1 (x1', m1')"
  thus "m1 = m1'" by(auto dest: \<tau>move0_heap_unchanged simp add: split_def)
qed(simp add: split_beta)

end

sublocale J_heap_base < red_mthr: 
  \<tau>multithreaded_wf 
    final_expr
    "mred P"
    convert_RA
    "\<tau>MOVE P"
  for P
by(rule red_\<tau>mthr_wf)

sublocale J_heap_base < red0_mthr:
  \<tau>multithreaded_wf 
    final_expr0
    "mred0 P"
    convert_RA
    "\<tau>MOVE0 P"
  for P
by(rule red0_\<tau>mthr_wf)

context J_heap_base begin

lemma \<tau>Red0r_into_red0_\<tau>mthr_silent_moves:
  "\<tau>Red0r P t h (e, es) (e'', es'') \<Longrightarrow> red0_mthr.silent_moves P t ((e, es), h) ((e'', es''), h)"
apply(induct rule: rtranclp_induct2)
 apply blast
apply(erule rtranclp.rtrancl_into_rtrancl)
apply(simp add: red0_mthr.silent_move_iff)
done

lemma \<tau>Red0t_into_red0_\<tau>mthr_silent_movet:
  "\<tau>Red0t P t h (e, es) (e'', es'') \<Longrightarrow> red0_mthr.silent_movet P t ((e, es), h) ((e'', es''), h)"
apply(induct rule: tranclp_induct2)
apply(fastforce simp add: red0_mthr.silent_move_iff elim: tranclp.trancl_into_trancl)+
done

end

end
