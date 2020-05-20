(*  Title:      JinjaThreads/MM/DRF_J.thy
    Author:     Andreas Lochbihler
*)

section \<open>JMM Instantiation for J\<close>

theory DRF_J
imports
  JMM_Common
  JMM_J
  "../J/ProgressThreaded"
  SC_Legal
begin

primrec ka :: "'addr expr \<Rightarrow> 'addr set"
  and kas :: "'addr expr list \<Rightarrow> 'addr set"
where 
  "ka (new C) = {}"
| "ka (newA T\<lfloor>e\<rceil>) = ka e"
| "ka (Cast T e) = ka e"
| "ka (e instanceof T) = ka e"
| "ka (Val v) = ka_Val v"
| "ka (Var V) = {}"
| "ka (e1 \<guillemotleft>bop\<guillemotright> e2) = ka e1 \<union> ka e2"
| "ka (V := e) = ka e"
| "ka (a\<lfloor>e\<rceil>) = ka a \<union> ka e"
| "ka (a\<lfloor>e\<rceil> := e') = ka a \<union> ka e \<union> ka e'"
| "ka (a\<bullet>length) = ka a"
| "ka (e\<bullet>F{D}) = ka e"
| "ka (e\<bullet>F{D} := e') = ka e \<union> ka e'"
| "ka (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) = ka e \<union> ka e' \<union> ka e''"
| "ka (e\<bullet>M(es)) = ka e \<union> kas es"
| "ka {V:T=vo; e} = ka e \<union> (case vo of None \<Rightarrow> {} | Some v \<Rightarrow> ka_Val v)"
| "ka (Synchronized x e e') = ka e \<union> ka e'"
| "ka (InSynchronized x a e) = insert a (ka e)"
| "ka (e;; e') = ka e \<union> ka e'"
| "ka (if (e) e1 else e2) = ka e \<union> ka e1 \<union> ka e2"
| "ka (while (b) e) = ka b \<union> ka e"
| "ka (throw e) = ka e"
| "ka (try e catch(C V) e') = ka e \<union> ka e'"

| "kas [] = {}"
| "kas (e # es) = ka e \<union> kas es" 

definition ka_locals :: "'addr locals \<Rightarrow> 'addr set"
where "ka_locals xs = {a. Addr a \<in> ran xs}"

lemma ka_Val_subset_ka_locals:
  "xs V = \<lfloor>v\<rfloor> \<Longrightarrow> ka_Val v \<subseteq> ka_locals xs"
by(cases v)(auto simp add: ka_locals_def ran_def)

lemma ka_locals_update_subset: 
  "ka_locals (xs(V := None)) \<subseteq> ka_locals xs"
  "ka_locals (xs(V \<mapsto> v)) \<subseteq> ka_Val v \<union> ka_locals xs"
by(auto simp add: ka_locals_def ran_def)

lemma ka_locals_empty [simp]: "ka_locals Map.empty = {}"
by(simp add: ka_locals_def)

lemma kas_append [simp]: "kas (es @ es') = kas es \<union> kas es'"
by(induct es) auto

lemma kas_map_Val [simp]: "kas (map Val vs) = \<Union>(ka_Val ` set vs)"
by(induct vs) auto

lemma ka_blocks:
  "\<lbrakk> length pns = length Ts; length vs = length Ts \<rbrakk> 
  \<Longrightarrow> ka (blocks pns Ts vs body) = \<Union>(ka_Val ` set vs) \<union> ka body"
by(induct pns Ts vs body rule: blocks.induct)(auto)

lemma WT_ka: "P,E \<turnstile> e :: T \<Longrightarrow> ka e = {}"
  and WTs_kas: "P,E \<turnstile> es [::] Ts \<Longrightarrow> kas es = {}"
by(induct rule: WT_WTs.inducts)(auto simp add: typeof_ka)

context J_heap_base begin

primrec J_known_addrs :: "'thread_id \<Rightarrow> 'addr expr \<times> 'addr locals \<Rightarrow> 'addr set"
where "J_known_addrs t (e, xs) = insert (thread_id2addr t) (ka e \<union> ka_locals xs \<union> set start_addrs)"

lemma assumes wf: "wf_J_prog P" 
  and ok: "start_heap_ok"
  shows red_known_addrs_mono:
  "P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> J_known_addrs t (e', lcl s') \<subseteq> J_known_addrs t (e, lcl s) \<union> new_obs_addrs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  and reds_known_addrs_mono:
  "P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> kas es' \<union> ka_locals (lcl s') \<subseteq> insert (thread_id2addr t) (kas es \<union> ka_locals (lcl s)) \<union> new_obs_addrs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<union> set start_addrs"
proof(induct rule: red_reds.inducts)
  case RedVar thus ?case by(auto dest: ka_Val_subset_ka_locals)
next
  case RedLAss thus ?case by(auto simp add: ka_locals_def ran_def)
next
  case RedBinOp thus ?case by(auto dest: binop_known_addrs[OF ok])
next
  case RedBinOpFail thus ?case by(auto dest: binop_known_addrs[OF ok])
next
  case RedCall thus ?case
    by(auto simp add: ka_blocks new_obs_addrs_def wf_mdecl_def dest!: sees_wf_mdecl[OF wf] WT_ka)
next
  case (RedCallExternal s a T M Ts T D vs ta va h') thus ?case
    by(cases va)(auto dest!: red_external_known_addrs_mono[OF ok])
next
  case (BlockRed e h l V vo ta e' h' l')
  thus ?case using ka_locals_update_subset[where xs = l and V=V] ka_locals_update_subset[where xs = l' and V=V]
    apply(cases "l V")
    apply(auto simp del: fun_upd_apply del: subsetI)
    apply(blast dest: ka_Val_subset_ka_locals)+
    done
qed(simp_all add: new_obs_addrs_def addr_of_sys_xcpt_start_addr[OF ok] subset_Un1 subset_Un2 subset_insert ka_Val_subset_new_obs_Addr_ReadMem ka_blocks del: fun_upd_apply, blast+)

lemma red_known_addrs_ReadMem:
  "\<lbrakk> P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk> \<Longrightarrow> ad \<in> J_known_addrs t (e, lcl s)"
  and reds_known_addrss_ReadMem:
  "\<lbrakk> P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> ad \<in> insert (thread_id2addr t) (kas es \<union> ka_locals (lcl s)) \<union> set start_addrs"
proof(induct rule: red_reds.inducts)
  case RedCallExternal thus ?case by simp (blast dest: red_external_known_addrs_ReadMem)
next
  case (BlockRed e h l V vo ta e' h' l')
  thus ?case using ka_locals_update_subset[where xs = l and V=V] ka_locals_update_subset[where xs = l' and V=V]
    by(auto simp del: fun_upd_apply)
qed(simp_all, blast+)

lemma red_known_addrs_WriteMem:
  "\<lbrakk> P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n = WriteMem ad al (Addr a); n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> a \<in> J_known_addrs t (e, lcl s) \<or> a \<in> new_obs_addrs (take n \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
  and reds_known_addrss_WriteMem:
  "\<lbrakk> P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n = WriteMem ad al (Addr a); n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> a \<in> insert (thread_id2addr t) (kas es \<union> ka_locals (lcl s)) \<union> set start_addrs \<union> new_obs_addrs (take n \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
proof(induct rule: red_reds.inducts)
  case RedCASSucceed thus ?case by(auto simp add: nth_Cons split: nat.split_asm)
next
  case RedCallExternal thus ?case by simp (blast dest: red_external_known_addrs_WriteMem)
next                                                            
  case (BlockRed e h l V vo ta e' h' l')
  thus ?case using ka_locals_update_subset[where xs = l and V=V] ka_locals_update_subset[where xs = l' and V=V]
    by(auto simp del: fun_upd_apply)
qed(simp_all, blast+)

end

context J_heap begin

lemma
  assumes wf: "wf_J_prog P" 
  and ok: "start_heap_ok"
  shows red_known_addrs_new_thread:
  "\<lbrakk> P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewThread t' x' h' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> J_known_addrs t' x' \<subseteq> J_known_addrs t (e, lcl s)"
  and reds_known_addrss_new_thread:
  "\<lbrakk> P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; NewThread t' x' h' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> J_known_addrs t' x' \<subseteq> insert (thread_id2addr t) (kas es \<union> ka_locals (lcl s) \<union> set start_addrs)"
proof(induct rule: red_reds.inducts)
  case RedCallExternal thus ?case
    apply clarsimp
    apply(frule (1) red_external_new_thread_sub_thread)
    apply(frule (1) red_external_NewThread_idD)
    apply clarsimp
    
    apply(drule (1) addr2thread_id_inverse)
    apply simp
    apply(drule sub_Thread_sees_run[OF wf])
    apply clarsimp
    apply(auto 4 4 dest: sees_wf_mdecl[OF wf] WT_ka simp add: wf_mdecl_def)
    done
next
  case (BlockRed e h l V vo ta e' h' l')
  thus ?case using ka_locals_update_subset[where xs = l and V=V] ka_locals_update_subset[where xs = l' and V=V]
    by(cases "l V")(auto simp del: fun_upd_apply)
qed(simp_all, blast+)

lemma red_New_same_addr_same:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; 
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NewHeapElem a x; i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NewHeapElem a x'; j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> i = j"
  and reds_New_same_addr_same:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; 
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NewHeapElem a x; i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NewHeapElem a x'; j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> i = j"
apply(induct rule: red_reds.inducts)
apply(auto dest: red_external_New_same_addr_same simp add: nth_Cons split: nat.split_asm)
done

end

locale J_allocated_heap = allocated_heap +
  constrains addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and spurious_wakeups :: bool
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
  and P :: "'addr J_prog"

sublocale J_allocated_heap < J_heap
by(unfold_locales)

context J_allocated_heap begin

lemma red_allocated_mono: "P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle> \<Longrightarrow> allocated (hp s) \<subseteq> allocated (hp s')"
  and reds_allocated_mono: "P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle> \<Longrightarrow> allocated (hp s) \<subseteq> allocated (hp s')"
by(induct rule: red_reds.inducts)(auto dest: allocate_allocatedD heap_write_allocated_same red_external_allocated_mono del: subsetI)

lemma red_allocatedD:
  "\<lbrakk> P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk> \<Longrightarrow> ad \<in> allocated (hp s') \<and> ad \<notin> allocated (hp s)"
  and reds_allocatedD:
  "\<lbrakk> P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk> \<Longrightarrow> ad \<in> allocated (hp s') \<and> ad \<notin> allocated (hp s)"
by(induct rule: red_reds.inducts)(auto dest: allocate_allocatedD heap_write_allocated_same red_external_allocatedD)

lemma red_allocated_NewHeapElemD:
  "\<lbrakk> P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; ad \<in> allocated (hp s'); ad \<notin> allocated (hp s) \<rbrakk> \<Longrightarrow> \<exists>CTn. NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  and reds_allocated_NewHeapElemD:
  "\<lbrakk> P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; ad \<in> allocated (hp s'); ad \<notin> allocated (hp s) \<rbrakk> \<Longrightarrow> \<exists>CTn. NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
by(induct rule: red_reds.inducts)(auto dest: allocate_allocatedD heap_write_allocated_same red_external_NewHeapElemD)

lemma mred_allocated_multithreaded:
  "allocated_multithreaded addr2thread_id thread_id2addr empty_heap allocate typeof_addr heap_write allocated final_expr (mred P) P"
proof
  fix t x m ta x' m'
  assume "mred P t (x, m) ta (x', m')"
  thus "allocated m \<subseteq> allocated m'"
    by(auto dest: red_allocated_mono del: subsetI simp add: split_beta)
next
  fix x t m ta x' m' ad CTn
  assume "mred P t (x, m) ta (x', m')"
    and "NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  thus "ad \<in> allocated m' \<and> ad \<notin> allocated m"
    by(auto dest: red_allocatedD simp add: split_beta)
next
  fix t x m ta x' m' ad
  assume "mred P t (x, m) ta (x', m')"
    and "ad \<in> allocated m'" "ad \<notin> allocated m"
  thus "\<exists>CTn. NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
    by(auto dest: red_allocated_NewHeapElemD simp add: split_beta)
next
  fix t x m ta x' m' i a CTn j CTn'
  assume "mred P t (x, m) ta (x', m')"
    and "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NewHeapElem a CTn" "i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
    and "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NewHeapElem a CTn'" "j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  thus "i = j" by(auto dest: red_New_same_addr_same simp add: split_beta)
qed

end

sublocale J_allocated_heap < red_mthr: allocated_multithreaded 
  addr2thread_id thread_id2addr 
  spurious_wakeups
  empty_heap allocate typeof_addr heap_read heap_write allocated 
  final_expr "mred P" 
  P
by(rule mred_allocated_multithreaded)

context J_allocated_heap begin

lemma mred_known_addrs: 
  assumes wf: "wf_J_prog P"
  and ok: "start_heap_ok"
  shows "known_addrs addr2thread_id thread_id2addr empty_heap allocate typeof_addr heap_write allocated J_known_addrs final_expr (mred P) P"
proof
  fix t x m ta x' m'
  assume "mred P t (x, m) ta (x', m')"
  thus "J_known_addrs t x' \<subseteq> J_known_addrs t x \<union> new_obs_addrs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
    by(auto del: subsetI simp add: split_beta dest: red_known_addrs_mono[OF wf ok])
next
  fix t x m ta x' m' t' x'' m''
  assume "mred P t (x, m) ta (x', m')"
    and "NewThread t' x'' m'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  thus "J_known_addrs t' x'' \<subseteq> J_known_addrs t x"
    by(auto del: subsetI simp add: split_beta dest: red_known_addrs_new_thread[OF wf ok])
next
  fix t x m ta x' m' ad al v
  assume "mred P t (x, m) ta (x', m')"
    and "ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  thus "ad \<in> J_known_addrs t x"
    by(auto simp add: split_beta dest: red_known_addrs_ReadMem)
next
  fix t x m ta x' m' n ad al ad'
  assume "mred P t (x, m) ta (x', m')"
    and "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n = WriteMem ad al (Addr ad')" "n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  thus "ad' \<in> J_known_addrs t x \<or> ad' \<in> new_obs_addrs (take n \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
    by(auto simp add: split_beta dest: red_known_addrs_WriteMem)
qed

end


context J_heap begin

lemma red_read_typeable:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; P,E,hp s \<turnstile> e : T; ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk> 
  \<Longrightarrow> \<exists>T'. P,hp s \<turnstile> ad@al : T'"
  and reds_read_typeable:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; P,E,hp s \<turnstile> es [:] Ts; ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk> 
  \<Longrightarrow> \<exists>T'. P,hp s \<turnstile> ad@al : T'"
proof(induct arbitrary: E T and E Ts rule: red_reds.inducts)
  case RedAAcc thus ?case
    by(fastforce intro: addr_loc_type.intros simp add: nat_less_iff word_sle_def)
next
  case RedFAcc thus ?case
    by(fastforce intro: addr_loc_type.intros)
next
  case RedCASSucceed thus ?case
    by(fastforce intro: addr_loc_type.intros)
next
  case RedCASFail thus ?case
    by(fastforce intro: addr_loc_type.intros)
next
  case RedCallExternal thus ?case
    by(auto intro: red_external_read_mem_typeable)
qed auto

end

primrec new_types :: "('a, 'b, 'addr) exp \<Rightarrow> ty set"
  and new_typess :: "('a, 'b, 'addr) exp list \<Rightarrow> ty set"
where 
  "new_types (new C) = {Class C}"
| "new_types (newA T\<lfloor>e\<rceil>) = insert (T\<lfloor>\<rceil>) (new_types e)"
| "new_types (Cast T e) = new_types e"
| "new_types (e instanceof T) = new_types e"
| "new_types (Val v) = {}"
| "new_types (Var V) = {}"
| "new_types (e1 \<guillemotleft>bop\<guillemotright> e2) = new_types e1 \<union> new_types e2"
| "new_types (V := e) = new_types e"
| "new_types (a\<lfloor>e\<rceil>) = new_types a \<union> new_types e"
| "new_types (a\<lfloor>e\<rceil> := e') = new_types a \<union> new_types e \<union> new_types e'"
| "new_types (a\<bullet>length) = new_types a"
| "new_types (e\<bullet>F{D}) = new_types e"
| "new_types (e\<bullet>F{D} := e') = new_types e \<union> new_types e'"
| "new_types (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) = new_types e \<union> new_types e' \<union> new_types e''"
| "new_types (e\<bullet>M(es)) = new_types e \<union> new_typess es"
| "new_types {V:T=vo; e} = new_types e"
| "new_types (Synchronized x e e') = new_types e \<union> new_types e'"
| "new_types (InSynchronized x a e) = new_types e"
| "new_types (e;; e') = new_types e \<union> new_types e'"
| "new_types (if (e) e1 else e2) = new_types e \<union> new_types e1 \<union> new_types e2"
| "new_types (while (b) e) = new_types b \<union> new_types e"
| "new_types (throw e) = new_types e"
| "new_types (try e catch(C V) e') = new_types e \<union> new_types e'"

| "new_typess [] = {}"
| "new_typess (e # es) = new_types e \<union> new_typess es"

lemma new_types_blocks:
  "\<lbrakk> length pns = length Ts; length vs = length Ts \<rbrakk> \<Longrightarrow> new_types (blocks pns vs Ts e) = new_types e"
apply(induct rule: blocks.induct)
apply(simp_all)
done

context J_heap_base begin

lemma WTrt_new_types_types: "P,E,h \<turnstile> e : T \<Longrightarrow> new_types e \<subseteq> types P"
  and WTrts_new_typess_types: "P,E,h \<turnstile> es [:] Ts \<Longrightarrow> new_typess es \<subseteq> types P"
by(induct rule: WTrt_WTrts.inducts) simp_all

end

lemma WT_new_types_types: "P,E \<turnstile> e :: T \<Longrightarrow> new_types e \<subseteq> types P"
  and WTs_new_typess_types: "P,E \<turnstile> es [::] Ts \<Longrightarrow> new_typess es \<subseteq> types P"
by(induct rule: WT_WTs.inducts) simp_all

context J_heap_conf begin

lemma red_New_typeof_addrD:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; new_types e \<subseteq> types P; hconf (hp s); NewHeapElem a x \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> typeof_addr (hp s') a = Some x"
  and reds_New_typeof_addrD:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; new_typess es \<subseteq> types P; hconf (hp s); NewHeapElem a x \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> typeof_addr (hp s') a = Some x"
apply(induct rule: red_reds.inducts)
apply(auto dest: allocate_SomeD red_external_New_typeof_addrD)
done

lemma J_conf_read_heap_read_typed:
  "J_conf_read addr2thread_id thread_id2addr empty_heap allocate typeof_addr (heap_read_typed P) heap_write hconf P"
proof -
  interpret conf: heap_conf_read
    addr2thread_id thread_id2addr 
    spurious_wakeups
    empty_heap allocate typeof_addr "heap_read_typed P" heap_write hconf 
    P
    by(rule heap_conf_read_heap_read_typed)
  show ?thesis by(unfold_locales)
qed

lemma red_non_speculative_vs_conf:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; P,E,hp s \<turnstile> e : T;
    non_speculative P vs (llist_of (take n (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))); vs_conf P (hp s) vs; hconf (hp s) \<rbrakk>
  \<Longrightarrow> vs_conf P (hp s') (w_values P vs (take n (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)))"
  and reds_non_speculative_vs_conf:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; P,E,hp s \<turnstile> es [:] Ts;
    non_speculative P vs (llist_of (take n (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))); vs_conf P (hp s) vs; hconf (hp s) \<rbrakk>
  \<Longrightarrow> vs_conf P (hp s') (w_values P vs (take n (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)))"
proof(induct arbitrary: E T and E Ts rule: red_reds.inducts)
  case (RedAAss h a U n i w V h' xs)
  from \<open>sint i < int n\<close> \<open>0 <=s i\<close> have "nat (sint i) < n"
    by (metis nat_less_iff sint_0 word_sle_def)
  with \<open>typeof_addr h a = \<lfloor>Array_type U n\<rfloor>\<close> have "P,h \<turnstile> a@ACell (nat (sint i)) : U"
    by(auto intro: addr_loc_type.intros)
  moreover from \<open>heap_write h a (ACell (nat (sint i))) w h'\<close> have "h \<unlhd> h'" by(rule hext_heap_write)
  ultimately have "P,h' \<turnstile> a@ACell (nat (sint i)) : U" by(rule addr_loc_type_hext_mono)
  moreover from \<open>typeof\<^bsub>h\<^esub> w = \<lfloor>V\<rfloor>\<close> \<open>P \<turnstile> V \<le> U\<close> have "P,h \<turnstile> w :\<le> U" by(simp add: conf_def)
  with \<open>h \<unlhd> h'\<close> have "P,h' \<turnstile> w :\<le> U" by(rule conf_hext)
  ultimately have "\<exists>T. P,h' \<turnstile> a@ACell (nat (sint i)) : T \<and> P,h' \<turnstile> w :\<le> T" by blast 
  thus ?case using RedAAss
    by(auto intro!: vs_confI split: if_split_asm dest: vs_confD simp add: take_Cons')(blast dest: vs_confD hext_heap_write intro: addr_loc_type_hext_mono conf_hext)+
next
  case (RedFAss h e D F v h' xs)
  hence "\<exists>T. P,h' \<turnstile> e@CField D F : T \<and> P,h' \<turnstile> v :\<le> T"
    by(force dest!: hext_heap_write intro!: addr_loc_type.intros intro: typeof_addr_hext_mono type_of_hext_type_of simp add: conf_def)
  thus ?case using RedFAss
    by(auto intro!: vs_confI simp add: take_Cons' split: if_split_asm dest: vs_confD)(blast dest: vs_confD hext_heap_write intro: addr_loc_type_hext_mono conf_hext)+
next
  case (RedCASSucceed h a D F v v' h' l)
  hence "\<exists>T. P,h' \<turnstile> a@CField D F : T \<and> P,h' \<turnstile> v' :\<le> T"
    by(force dest!: hext_heap_write intro!: addr_loc_type.intros intro: typeof_addr_hext_mono type_of_hext_type_of simp add: conf_def take_Cons')
  thus ?case using RedCASSucceed
    by(auto simp add: take_Cons' split: if_split_asm dest: vs_confD intro!: vs_confI)
      (blast dest: vs_confD hext_heap_write intro: addr_loc_type_hext_mono conf_hext)+
next
  case RedCallExternal thus ?case by(auto intro: red_external_non_speculative_vs_conf)
qed(auto dest: vs_conf_allocate hext_allocate intro: vs_conf_hext simp add: take_Cons')

lemma red_non_speculative_typeable:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>; P,E,hp s \<turnstile> e : T;
    non_speculative P vs (llist_of (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)); vs_conf P (hp s) vs; hconf (hp s) \<rbrakk>
  \<Longrightarrow> J_heap_base.red addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate typeof_addr (heap_read_typed P) heap_write (convert_extTA extTA) P t e s ta e' s'"
  and reds_non_speculative_typeable:
  "\<lbrakk> convert_extTA extTA,P,t \<turnstile> \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>; P,E,hp s \<turnstile> es [:] Ts;
    non_speculative P vs (llist_of (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)); vs_conf P (hp s) vs; hconf (hp s) \<rbrakk>
  \<Longrightarrow> J_heap_base.reds addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate typeof_addr (heap_read_typed P) heap_write (convert_extTA extTA) P t es s ta es' s'"
proof(induct arbitrary: E T and E Ts rule: red_reds.inducts)
  case RedCall thus ?case by(blast intro: J_heap_base.red_reds.RedCall)
next
  case RedCallExternal thus ?case
    by(auto intro: J_heap_base.red_reds.RedCallExternal red_external_non_speculative_typeable)
qed(auto intro: J_heap_base.red_reds.intros intro!: heap_read_typedI dest: vs_confD addr_loc_type_fun)

end

sublocale J_heap_base < red_mthr: 
  if_multithreaded
    final_expr
    "mred P"
    convert_RA
  for P
by(unfold_locales)


locale J_allocated_heap_conf = 
  J_heap_conf 
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write hconf
    P
  +
  J_allocated_heap 
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write
    allocated
    P
  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and spurious_wakeups :: bool
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
  and hconf :: "'heap \<Rightarrow> bool"
  and allocated :: "'heap \<Rightarrow> 'addr set"
  and P :: "'addr J_prog"
begin

lemma mred_known_addrs_typing:
  assumes wf: "wf_J_prog P"
  and ok: "start_heap_ok"
  shows "known_addrs_typing addr2thread_id thread_id2addr empty_heap allocate typeof_addr heap_write allocated J_known_addrs final_expr (mred P) (\<lambda>t x h. \<exists>ET. sconf_type_ok ET t x h) P"
proof -
  interpret known_addrs
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write 
    allocated J_known_addrs
    final_expr "mred P" P
    using wf ok by(rule mred_known_addrs)
  
  show ?thesis
  proof
    fix t x m ta x' m'
    assume "mred P t (x, m) ta (x', m')"
    thus "m \<unlhd> m'" by(auto dest: red_hext_incr simp add: split_beta)
  next
    fix t x m ta x' m' vs
    assume red: "mred P t (x, m) ta (x', m')"
      and ts_ok: "\<exists>ET. sconf_type_ok ET t x m"
      and vs: "vs_conf P m vs"
      and ns: "non_speculative P vs (llist_of (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))"
    
    let ?mred = "J_heap_base.mred addr2thread_id thread_id2addr spurious_wakeups empty_heap allocate typeof_addr (heap_read_typed P) heap_write P"

    have lift: "lifting_inv final_expr ?mred sconf_type_ok"
      by(intro J_conf_read.lifting_inv_sconf_subject_ok J_conf_read_heap_read_typed wf)
    moreover
    from ts_ok obtain ET where type: "sconf_type_ok ET t x m" ..
    with red vs ns have red': "?mred t (x, m) ta (x', m')"
      by(auto simp add: split_beta sconf_type_ok_def sconf_def type_ok_def dest: red_non_speculative_typeable)
    ultimately have "sconf_type_ok ET t x' m'" using type
      by(rule lifting_inv.invariant_red[where r="?mred"])
    thus "\<exists>ET. sconf_type_ok ET t x' m'" ..
    { fix t'' x'' m''
      assume New: "NewThread t'' x'' m'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
      with red have "m'' = snd (x', m')" by(rule red_mthr.new_thread_memory)
      with lift red' type New
      show "\<exists>ET. sconf_type_ok ET t'' x'' m''"
        by-(rule lifting_inv.invariant_NewThread[where r="?mred"], simp_all) }
    { fix t'' x''
      assume "\<exists>ET. sconf_type_ok ET t'' x'' m"
      with lifting_inv.invariant_other[where r="?mred", OF lift red' type]
      show "\<exists>ET. sconf_type_ok ET t'' x'' m'" by blast }
  next
    fix t x m ta x' m' vs n
    assume red: "mred P t (x, m) ta (x', m')"
      and ts_ok: "\<exists>ET. sconf_type_ok ET t x m"
      and vs: "vs_conf P m vs"
      and ns: "non_speculative P vs (llist_of (take n (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)))"
    thus "vs_conf P m' (w_values P vs (take n (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)))"
      by(cases x)(auto dest: red_non_speculative_vs_conf simp add: sconf_type_ok_def type_ok_def sconf_def)
  next
    fix t x m ta x' m' ad al v
    assume "mred P t (x, m) ta (x', m')"
      and "\<exists>ET. sconf_type_ok ET t x m"
      and "ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
    thus "\<exists>T. P,m \<turnstile> ad@al : T"
      by(fastforce simp add: sconf_type_ok_def type_ok_def sconf_def split_beta dest: red_read_typeable)
  next
    fix t x m ta x' m' ad hT
    assume "mred P t (x, m) ta (x', m')"
      and "\<exists>ET. sconf_type_ok ET t x m"
      and "NewHeapElem ad hT \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
    thus "typeof_addr m' ad = \<lfloor>hT\<rfloor>"
      by(auto dest: red_New_typeof_addrD[where x="hT"] dest!: WTrt_new_types_types simp add: split_beta sconf_type_ok_def sconf_def type_ok_def)
  qed
qed

end

context J_allocated_heap_conf begin

lemma executions_sc:
  assumes wf: "wf_J_prog P"
  and wf_start: "wf_start_state P C M vs"
  and vs2: "\<Union>(ka_Val ` set vs) \<subseteq> set start_addrs"
  shows "executions_sc_hb (J_\<E> P C M vs status) P"
  (is "executions_sc_hb ?E P")
proof -
  from wf_start obtain Ts T pns body D where ok: "start_heap_ok"
    and sees: "P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>(pns, body)\<rfloor> in D"
    and vs1: "P,start_heap \<turnstile> vs [:\<le>] Ts" by cases auto
  
  interpret known_addrs_typing
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write 
    allocated J_known_addrs
    final_expr "mred P" "\<lambda>t x h. \<exists>ET. sconf_type_ok ET t x h" P
    using wf ok by(rule mred_known_addrs_typing)
  
  from wf_prog_wf_syscls[OF wf] J_start_state_sconf_type_ok[OF wf wf_start]
  show ?thesis
  proof(rule executions_sc_hb)
    from wf sees have "wf_mdecl wf_J_mdecl P D (M, Ts, T, \<lfloor>(pns, body)\<rfloor>)" by(rule sees_wf_mdecl)
    then obtain T' where len1: "length pns = length Ts" and wt: "P,[this\<mapsto>Class D,pns [\<mapsto>] Ts] \<turnstile> body :: T'"
      by(auto simp add: wf_mdecl_def)
    from vs1 have len2: "length vs = length Ts" by(rule list_all2_lengthD)
    show "J_known_addrs start_tid ((\<lambda>(pns, body) vs. (blocks (this # pns) (Class (fst (method P C M)) # fst (snd (method P C M))) (Null # vs) body, Map.empty)) (the (snd (snd (snd (method P C M))))) vs) \<subseteq> allocated start_heap"
      using sees vs2 len1 len2 WT_ka[OF wt]
      by(auto simp add: split_beta start_addrs_allocated ka_blocks intro: start_tid_start_addrs[OF wf_prog_wf_syscls[OF wf] ok])
  qed
qed

end

declare split_paired_Ex [simp del]

context J_progress begin

lemma ex_WTrt_simps:
  "P,E,h \<turnstile> e : T \<Longrightarrow> \<exists>E T. P,E,h \<turnstile> e : T"
by blast

abbreviation (input) J_non_speculative_read_bound :: nat
  where "J_non_speculative_read_bound \<equiv> 2"

lemma assumes hrt: "heap_read_typeable hconf P"
  and vs: "vs_conf P (shr s) vs"
  and hconf: "hconf (shr s)"
  shows red_non_speculative_read:
  "\<lbrakk> P,t \<turnstile> \<langle>e, (shr s, xs)\<rangle> -ta\<rightarrow> \<langle>e', (h', xs')\<rangle>; \<exists>E T. P,E,shr s \<turnstile> e : T;
    red_mthr.mthr.if.actions_ok s t ta; 
    I < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>; \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! I = ReadMem a'' al'' v; v' \<in> w_values P vs (map NormalAction (take I \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (a'', al'');
    non_speculative P vs (llist_of (map NormalAction (take I \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))) \<rbrakk>
  \<Longrightarrow> \<exists>ta' e'' xs'' h''. P,t \<turnstile> \<langle>e, (shr s, xs)\<rangle> -ta'\<rightarrow> \<langle>e'', (h'', xs'')\<rangle> \<and> 
           red_mthr.mthr.if.actions_ok s t ta' \<and> 
           I < length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> \<and> take I \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> = take I \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<and> 
           \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! I = ReadMem a'' al'' v' \<and> length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> \<le> max J_non_speculative_read_bound (length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
  and reds_non_speculative_read:
  "\<lbrakk> P,t \<turnstile> \<langle>es, (shr s, xs)\<rangle> [-ta\<rightarrow>] \<langle>es', (h', xs')\<rangle>; \<exists>E Ts. P,E,shr s \<turnstile> es [:] Ts;
     red_mthr.mthr.if.actions_ok s t ta;
    I < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>; \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! I = ReadMem a'' al'' v; v' \<in> w_values P vs (map NormalAction (take I \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (a'', al'');
    non_speculative P vs (llist_of (map NormalAction (take I \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))) \<rbrakk>
  \<Longrightarrow> \<exists>ta' es'' xs'' h''. P,t \<turnstile> \<langle>es, (shr s, xs)\<rangle> [-ta'\<rightarrow>] \<langle>es'', (h'', xs'')\<rangle> \<and> 
           red_mthr.mthr.if.actions_ok s t ta' \<and> 
           I < length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> \<and> take I \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> = take I \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<and> 
           \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! I = ReadMem a'' al'' v' \<and> length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> \<le> max J_non_speculative_read_bound (length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
proof(induct e hxs\<equiv>"(shr s, xs)" ta e' hxs'\<equiv>"(h', xs')" 
        and es hxs\<equiv>"(shr s, xs)" ta es' hxs'\<equiv>"(h', xs')"
      arbitrary: xs xs' and xs xs' rule: red_reds.inducts)
  case (RedAAcc a U n i v e)
  hence [simp]: "I = 0" "al'' = ACell (nat (sint i))" "a'' = a" 
    and v': "v' \<in> vs (a, ACell (nat (sint i)))" by simp_all
  from RedAAcc have adal: "P,shr s \<turnstile> a@ACell (nat (sint i)) : U"
    by(auto intro: addr_loc_type.intros simp add: nat_less_iff word_sle_def)
  from v' vs adal have "P,shr s \<turnstile> v' :\<le> U" by(auto dest!: vs_confD dest: addr_loc_type_fun)  
  with hrt adal have "heap_read (shr s) a (ACell (nat (sint i))) v'" using hconf by(rule heap_read_typeableD)
  with \<open>typeof_addr (shr s) a = \<lfloor>Array_type U n\<rfloor>\<close> \<open>0 <=s i\<close> \<open>sint i < int n\<close> 
    \<open>red_mthr.mthr.if.actions_ok s t \<lbrace>ReadMem a (ACell (nat (sint i))) v\<rbrace>\<close>
  show ?case by(fastforce intro: red_reds.RedAAcc)
next
  case (RedFAcc a D F v)
  hence [simp]: "I = 0" "al'' = CField D F" "a'' = a"
    and v': "v' \<in> vs (a, CField D F)" by simp_all
  from RedFAcc obtain E T where "P,E,shr s \<turnstile> addr a\<bullet>F{D} : T" by blast
  with RedFAcc have adal: "P,shr s \<turnstile> a@CField D F : T" by(auto 4 4 intro: addr_loc_type.intros)
  from v' vs adal have "P,shr s \<turnstile> v' :\<le> T" by(auto dest!: vs_confD dest: addr_loc_type_fun)  
  with hrt adal have "heap_read (shr s) a (CField D F) v'" using hconf by(rule heap_read_typeableD)
  with \<open>red_mthr.mthr.if.actions_ok s t \<lbrace>ReadMem a (CField D F) v\<rbrace>\<close>
  show ?case by(fastforce intro: red_reds.RedFAcc)
next
  case (RedCASSucceed a D F v'' v''')
  hence [simp]: "I = 0" "al'' = CField D F" "a'' = a" "v'' = v" 
    and v': "v' \<in> vs (a, CField D F)" by(auto simp add: take_Cons' split: if_split_asm)
  from RedCASSucceed.prems(1) obtain E T where
    "P,E,shr s \<turnstile> addr a\<bullet>compareAndSwap(D\<bullet>F, Val v'', Val v''') : T" by clarify
  then obtain T where adal: "P,shr s \<turnstile> a@CField D F : T" 
    and v'': "P,shr s \<turnstile> v'' :\<le> T" and v''': "P,shr s \<turnstile> v''' :\<le> T"
    by(fastforce intro: addr_loc_type.intros simp add: conf_def)
  from v' vs adal have "P,shr s \<turnstile> v' :\<le> T" by(auto dest!: vs_confD dest: addr_loc_type_fun)  
  from hrt adal this hconf have read: "heap_read (shr s) a (CField D F) v'" by(rule heap_read_typeableD)
  show ?case
  proof(cases "v' = v''")
    case True
    then show ?thesis using RedCASSucceed 
      by(fastforce intro: red_reds.RedCASSucceed)
  next
    case False
    then show ?thesis using read RedCASSucceed
      by(fastforce intro: RedCASFail)
  qed
next
  case (RedCASFail a D F v'' v''' v'''')
  hence [simp]: "I = 0" "al'' = CField D F" "a'' = a" "v'' = v" 
    and v': "v' \<in> vs (a, CField D F)" by(auto simp add: take_Cons' split: if_split_asm)
  from RedCASFail.prems(1) obtain E T where
    "P,E,shr s \<turnstile> addr a\<bullet>compareAndSwap(D\<bullet>F, Val v''', Val v'''') : T" by(iprover)
  then obtain T where adal: "P,shr s \<turnstile> a@CField D F : T" 
    and v''': "P,shr s \<turnstile> v''' :\<le> T" and v'''': "P,shr s \<turnstile> v'''' :\<le> T"
    by(fastforce intro: addr_loc_type.intros simp add: conf_def)
  from v' vs adal have "P,shr s \<turnstile> v' :\<le> T" by(auto dest!: vs_confD dest: addr_loc_type_fun)  
  from hrt adal this hconf have read: "heap_read (shr s) a (CField D F) v'" by(rule heap_read_typeableD)
  show ?case
  proof(cases "v' = v'''")
    case True
    from heap_write_total[OF hconf adal v''''] obtain h' where
      "heap_write (shr s) a (CField D F) v'''' h'" ..
    with read RedCASFail True show ?thesis 
      by(fastforce intro: RedCASSucceed)
  next
    case False
    with read RedCASFail show ?thesis by(fastforce intro: red_reds.RedCASFail)
  qed
next
  case (RedCallExternal a U M Ts Tr D ps ta' va h' ta e')
  from \<open>P,t \<turnstile> \<langle>a\<bullet>M(ps),hp (shr s, xs)\<rangle> -ta'\<rightarrow>ext \<langle>va,h'\<rangle>\<close>
  have red: "P,t \<turnstile> \<langle>a\<bullet>M(ps),shr s\<rangle> -ta'\<rightarrow>ext \<langle>va,h'\<rangle>" by simp
  from RedCallExternal have aok: "red_mthr.mthr.if.actions_ok s t ta'" by simp
  from RedCallExternal have "I < length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>"
    and "\<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! I = ReadMem a'' al'' v"
    and "v' \<in> w_values P vs (map NormalAction (take I \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)) (a'', al'')"
    and "non_speculative P vs (llist_of (map NormalAction (take I \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)))" by simp_all
  from red_external_non_speculative_read[OF hrt vs red aok hconf this]
    \<open>typeof_addr (hp (shr s, xs)) a = \<lfloor>U\<rfloor>\<close> 
    \<open>P \<turnstile> class_type_of U sees M: Ts\<rightarrow>Tr = Native in D\<close> \<open>ta = extTA2J P ta'\<close>
    \<open>I < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>\<close>
  show ?case by(fastforce intro: red_reds.RedCallExternal)
next
  case NewArrayRed thus ?case by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.NewArrayRed)
next 
  case CastRed thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.CastRed)
next
  case InstanceOfRed thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.InstanceOfRed)
next
  case BinOpRed1 thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.BinOpRed1)
next
  case BinOpRed2 thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.BinOpRed2)
next
  case LAssRed thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.LAssRed)
next
  case AAccRed1 thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.AAccRed1)
next
  case AAccRed2 thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.AAccRed2)
next
  case AAssRed1 thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.AAssRed1)
next
  case AAssRed2 thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.AAssRed2)
next
  case AAssRed3 thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.AAssRed3)+
next
  case ALengthRed thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.ALengthRed)
next
  case FAccRed thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.FAccRed)
next
  case FAssRed1 thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.FAssRed1)
next
  case FAssRed2 thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.FAssRed2)
next
  case CASRed1 thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.CASRed1)
next
  case CASRed2 thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.CASRed2)
next
  case CASRed3 thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.CASRed3)
next
  case CallObj thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.CallObj)
next
  case CallParams thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.CallParams)
next
  case BlockRed thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(fastforce intro: red_reds.BlockRed)+
next
  case SynchronizedRed1 thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.SynchronizedRed1)
next
  case SynchronizedRed2 thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.SynchronizedRed2)
next
  case SeqRed thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.SeqRed)
next
  case CondRed thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.CondRed)
next
  case ThrowRed thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.ThrowRed)
next
  case TryRed thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.TryRed)
next
  case ListRed1 thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.ListRed1)
next
  case ListRed2 thus ?case
    by(clarsimp simp add: split_paired_Ex ex_WTrt_simps)(blast intro: red_reds.ListRed2)
qed(simp_all)

end


sublocale J_allocated_heap_conf < if_known_addrs_base
  J_known_addrs
  final_expr "mred P" convert_RA 
.


declare split_paired_Ex [simp]
declare eq_upto_seq_inconsist_simps [simp del]

locale J_allocated_progress = 
  J_progress
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write hconf
    P
  +
  J_allocated_heap_conf
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write hconf
    allocated
    P
  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and spurious_wakeups :: bool
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
  and hconf :: "'heap \<Rightarrow> bool"
  and allocated :: "'heap \<Rightarrow> 'addr set"
  and P :: "'addr J_prog"
begin

lemma non_speculative_read:
  assumes wf: "wf_J_prog P"
  and hrt: "heap_read_typeable hconf P"
  and wf_start: "wf_start_state P C M vs"
  and ka: "\<Union>(ka_Val ` set vs) \<subseteq> set start_addrs"
  shows "red_mthr.if.non_speculative_read J_non_speculative_read_bound
      (init_fin_lift_state status (J_start_state P C M vs)) 
      (w_values P (\<lambda>_. {}) (map snd (lift_start_obs start_tid start_heap_obs)))"
  (is "red_mthr.if.non_speculative_read _ ?start_state ?start_vs")
proof(rule red_mthr.if.non_speculative_readI)
  fix ttas s' t x ta x' m' i ad al v v'
  assume \<tau>Red: "red_mthr.mthr.if.RedT P ?start_state ttas s'"
    and sc: "non_speculative P ?start_vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
    and ts't: "thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor>"
    and red: "red_mthr.init_fin P t (x, shr s') ta (x', m')"
    and aok: "red_mthr.mthr.if.actions_ok s' t ta"
    and i: "i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
    and ns': "non_speculative P (w_values P ?start_vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (llist_of (take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))"
    and read: "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NormalAction (ReadMem ad al v)"
    and v': "v' \<in> w_values P ?start_vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas) @ take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (ad, al)" 

  from wf_start obtain Ts T pns body D where ok: "start_heap_ok"
    and sees: "P \<turnstile> C sees M:Ts\<rightarrow>T = \<lfloor>(pns, body)\<rfloor> in D"
    and conf: "P,start_heap \<turnstile> vs [:\<le>] Ts" by cases auto

  let ?conv = "\<lambda>ttas. concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)"
  let ?vs' = "w_values P ?start_vs (?conv ttas)"
  let ?wt_ok = "init_fin_lift_inv sconf_type_ok"
  let ?ET_start = "J_sconf_type_ET_start P C M"
  let ?start_obs = "map snd (lift_start_obs start_tid start_heap_obs)"
  let ?start_state = "init_fin_lift_state status (J_start_state P C M vs)"

  interpret known_addrs_typing
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write 
    allocated J_known_addrs
    final_expr "mred P" "\<lambda>t x h. \<exists>ET. sconf_type_ok ET t x h" P
    using wf ok by(rule mred_known_addrs_typing)

  from wf sees have "wf_mdecl wf_J_mdecl P D (M, Ts, T, \<lfloor>(pns, body)\<rfloor>)" by(rule sees_wf_mdecl)
  then obtain T' where len1: "length pns = length Ts" and wt: "P,[this\<mapsto>Class D,pns [\<mapsto>] Ts] \<turnstile> body :: T'"
    by(auto simp add: wf_mdecl_def)
  from conf have len2: "length vs = length Ts" by(rule list_all2_lengthD)

  from wf wf_start have ts_ok_start: "ts_ok (init_fin_lift (\<lambda>t x h. \<exists>ET. sconf_type_ok ET t x h)) (thr ?start_state) (shr ?start_state)"
    unfolding ts_ok_init_fin_lift_init_fin_lift_state shr_start_state by(rule J_start_state_sconf_type_ok)
  have sc': "non_speculative P ?start_vs (lmap snd (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of ttas))))"
    using sc by(simp add: lmap_lconcat llist.map_comp o_def split_def lconcat_llist_of[symmetric])

  from start_state_vs_conf[OF wf_prog_wf_syscls[OF wf]]
  have vs_conf_start: "vs_conf P (shr ?start_state) ?start_vs"
    by(simp add:init_fin_lift_state_conv_simps start_state_def split_beta)
  with \<tau>Red ts_ok_start sc
  have wt': "ts_ok (init_fin_lift (\<lambda>t x h. \<exists>ET. sconf_type_ok ET t x h)) (thr s') (shr s')"
    and vs': "vs_conf P (shr s') ?vs'" by(rule if_RedT_non_speculative_invar)+

  from red i read obtain e xs e' xs' ta'
    where x: "x = (Running, e, xs)" and x': "x' = (Running, e', xs')"
    and ta: "ta = convert_TA_initial (convert_obs_initial ta')"
    and red': "P,t \<turnstile> \<langle>e, (shr s', xs)\<rangle> -ta'\<rightarrow> \<langle>e', (m', xs')\<rangle>"
    by cases fastforce+
  
  from ts't wt' x obtain E T where wte: "P,E,shr s' \<turnstile> e : T"
    and hconf: "hconf (shr s')"
    by(auto dest!: ts_okD simp add: sconf_type_ok_def sconf_def type_ok_def)

  have aok': "red_mthr.mthr.if.actions_ok s' t ta'" using aok unfolding ta by simp

  from i read v' ta ns' have "i < length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>" and "\<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! i = ReadMem ad al v" 
    and "v' \<in> w_values P ?vs' (map NormalAction (take i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)) (ad, al)"
    and "non_speculative P ?vs' (llist_of (map NormalAction (take i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)))"
    by(simp_all add: take_map)

  from red_non_speculative_read[OF hrt vs' hconf red' _ aok' this] wte
  obtain ta'' e'' xs'' h''
    where red'': "P,t \<turnstile> \<langle>e, (shr s', xs)\<rangle> -ta''\<rightarrow> \<langle>e'', (h'', xs'')\<rangle>"
    and aok'': "red_mthr.mthr.if.actions_ok s' t ta''"
    and i'': "i < length \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>"
    and eq'': "take i \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub> = take i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>"
    and read'': "\<lbrace>ta''\<rbrace>\<^bsub>o\<^esub> ! i = ReadMem ad al v'"
    and len'': "length \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub> \<le> max J_non_speculative_read_bound (length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)" by blast

  let ?x' = "(Running, e'', xs'')"
  let ?ta' = "convert_TA_initial (convert_obs_initial ta'')"
  from red'' have "red_mthr.init_fin P t (x, shr s') ?ta' (?x', h'')"
    unfolding x by -(rule red_mthr.init_fin.NormalAction, simp)
  moreover from aok'' have "red_mthr.mthr.if.actions_ok s' t ?ta'" by simp
  moreover from i'' have "i < length \<lbrace>?ta'\<rbrace>\<^bsub>o\<^esub>" by simp
  moreover from eq'' have "take i \<lbrace>?ta'\<rbrace>\<^bsub>o\<^esub> = take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" unfolding ta by(simp add: take_map)
  moreover from read'' i'' have "\<lbrace>?ta'\<rbrace>\<^bsub>o\<^esub> ! i = NormalAction (ReadMem ad al v')" by(simp add: nth_map)
  moreover from len'' have "length \<lbrace>?ta'\<rbrace>\<^bsub>o\<^esub> \<le> max J_non_speculative_read_bound (length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
    unfolding ta by simp
  ultimately
  show "\<exists>ta' x'' m''. red_mthr.init_fin P t (x, shr s') ta' (x'', m'') \<and>
                      red_mthr.mthr.if.actions_ok s' t ta' \<and>
                      i < length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> \<and> take i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> = take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<and>
                      \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! i = NormalAction (ReadMem ad al v') \<and> 
                      length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> \<le> max J_non_speculative_read_bound (length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
    by blast
qed

lemma J_cut_and_update:
  assumes wf: "wf_J_prog P"
  and hrt: "heap_read_typeable hconf P"
  and wf_start: "wf_start_state P C M vs"
  and ka: "\<Union>(ka_Val ` set vs) \<subseteq> set start_addrs"
  shows "red_mthr.if.cut_and_update (init_fin_lift_state status (J_start_state P C M vs))
           (mrw_values P Map.empty (map snd (lift_start_obs start_tid start_heap_obs)))"
proof -
  from wf_start obtain Ts T pns body D where ok: "start_heap_ok"
    and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = \<lfloor>(pns, body)\<rfloor> in D"
    and conf: "P,start_heap \<turnstile> vs [:\<le>] Ts" by cases auto

  interpret known_addrs_typing
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write 
    allocated J_known_addrs
    final_expr "mred P" "\<lambda>t x h. \<exists>ET. sconf_type_ok ET t x h" P
    using wf ok by(rule mred_known_addrs_typing)

  let ?start_vs = "w_values P (\<lambda>_. {}) (map snd (lift_start_obs start_tid start_heap_obs))"
  let ?wt_ok = "init_fin_lift_inv sconf_type_ok"
  let ?ET_start = "J_sconf_type_ET_start P C M"
  let ?start_obs = "map snd (lift_start_obs start_tid start_heap_obs)"
  let ?start_state = "init_fin_lift_state status (J_start_state P C M vs)"

  from wf sees have "wf_mdecl wf_J_mdecl P D (M, Ts, T, \<lfloor>(pns, body)\<rfloor>)" by(rule sees_wf_mdecl)
  then obtain T' where len1: "length pns = length Ts" and wt: "P,[this\<mapsto>Class D,pns [\<mapsto>] Ts] \<turnstile> body :: T'"
    by(auto simp add: wf_mdecl_def)
  from conf have len2: "length vs = length Ts" by(rule list_all2_lengthD)

  note wf_prog_wf_syscls[OF wf] non_speculative_read[OF wf hrt wf_start ka]
  moreover 
  from wf wf_start have ts_ok_start: "ts_ok (init_fin_lift (\<lambda>t x h. \<exists>ET. sconf_type_ok ET t x h)) (thr ?start_state) (shr ?start_state)"
    unfolding ts_ok_init_fin_lift_init_fin_lift_state shr_start_state by(rule J_start_state_sconf_type_ok)
  moreover
  have ka: "J_known_addrs start_tid ((\<lambda>(pns, body) vs. (blocks (this # pns) (Class (fst (method P C M)) # fst (snd (method P C M))) (Null # vs) body, Map.empty)) (the (snd (snd (snd (method P C M))))) vs) \<subseteq> allocated start_heap"
    using sees ka len1 len2 WT_ka[OF wt]
    by(auto simp add: split_beta start_addrs_allocated ka_blocks intro: start_tid_start_addrs[OF wf_prog_wf_syscls[OF wf] ok])
  ultimately show ?thesis by(rule non_speculative_read_into_cut_and_update)
qed

lemma J_drf:
  assumes wf: "wf_J_prog P"
  and hrt: "heap_read_typeable hconf P"
  and wf_start: "wf_start_state P C M vs"
  and ka: "\<Union>(ka_Val ` set vs) \<subseteq> set start_addrs"
  shows "drf (J_\<E> P C M vs status) P"
proof -
  from wf_start obtain Ts T pns body D where ok: "start_heap_ok"
    and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = \<lfloor>(pns, body)\<rfloor> in D"
    and conf: "P,start_heap \<turnstile> vs [:\<le>] Ts" by cases auto

  from J_cut_and_update[OF assms] wf_prog_wf_syscls[OF wf] J_start_state_sconf_type_ok[OF wf wf_start] show ?thesis
  proof(rule known_addrs_typing.drf[OF mred_known_addrs_typing[OF wf ok]])
    from wf sees have "wf_mdecl wf_J_mdecl P D (M, Ts, T, \<lfloor>(pns, body)\<rfloor>)" by(rule sees_wf_mdecl)
    then obtain T' where len1: "length pns = length Ts" and wt: "P,[this\<mapsto>Class D,pns [\<mapsto>] Ts] \<turnstile> body :: T'"
      by(auto simp add: wf_mdecl_def)
    from conf have len2: "length vs = length Ts" by(rule list_all2_lengthD)
    show "J_known_addrs start_tid ((\<lambda>(pns, body) vs. (blocks (this # pns) (Class (fst (method P C M)) # fst (snd (method P C M))) (Null # vs) body, Map.empty)) (the (snd (snd (snd (method P C M))))) vs) \<subseteq> allocated start_heap"
      using sees ka len1 len2 WT_ka[OF wt]
      by(auto simp add: split_beta start_addrs_allocated ka_blocks intro: start_tid_start_addrs[OF wf_prog_wf_syscls[OF wf] ok])
  qed
qed

lemma J_sc_legal:
  assumes wf: "wf_J_prog P"
  and hrt: "heap_read_typeable hconf P"
  and wf_start: "wf_start_state P C M vs"
  and ka: "\<Union>(ka_Val ` set vs) \<subseteq> set start_addrs"
  shows "sc_legal (J_\<E> P C M vs status) P"
proof -
  from wf_start obtain Ts T pns body D where ok: "start_heap_ok"
    and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = \<lfloor>(pns, body)\<rfloor> in D"
    and conf: "P,start_heap \<turnstile> vs [:\<le>] Ts" by cases auto
  interpret known_addrs_typing
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write 
    allocated J_known_addrs
    final_expr "mred P" "\<lambda>t x h. \<exists>ET. sconf_type_ok ET t x h" P
    using wf ok by(rule mred_known_addrs_typing)

  let ?start_vs = "w_values P (\<lambda>_. {}) (map snd (lift_start_obs start_tid start_heap_obs))"
  let ?wt_ok = "init_fin_lift_inv sconf_type_ok"
  let ?ET_start = "J_sconf_type_ET_start P C M"
  let ?start_obs = "map snd (lift_start_obs start_tid start_heap_obs)"
  let ?start_state = "init_fin_lift_state status (J_start_state P C M vs)"

  from wf sees have "wf_mdecl wf_J_mdecl P D (M, Ts, T, \<lfloor>(pns, body)\<rfloor>)" by(rule sees_wf_mdecl)
  then obtain T' where len1: "length pns = length Ts" and wt: "P,[this\<mapsto>Class D,pns [\<mapsto>] Ts] \<turnstile> body :: T'"
    by(auto simp add: wf_mdecl_def)
  from conf have len2: "length vs = length Ts" by(rule list_all2_lengthD)

  note wf_prog_wf_syscls[OF wf] non_speculative_read[OF wf hrt wf_start ka]
  moreover
  from wf wf_start have ts_ok_start: "ts_ok (init_fin_lift (\<lambda>t x h. \<exists>ET. sconf_type_ok ET t x h)) (thr ?start_state) (shr ?start_state)"
    unfolding ts_ok_init_fin_lift_init_fin_lift_state shr_start_state by(rule J_start_state_sconf_type_ok)
  moreover have ka_allocated: "J_known_addrs start_tid ((\<lambda>(pns, body) vs. (blocks (this # pns) (Class (fst (method P C M)) # fst (snd (method P C M))) (Null # vs) body, Map.empty)) (the (snd (snd (snd (method P C M))))) vs) \<subseteq> allocated start_heap"
    using sees ka len1 len2 WT_ka[OF wt]
    by(auto simp add: split_beta start_addrs_allocated ka_blocks intro: start_tid_start_addrs[OF wf_prog_wf_syscls[OF wf] ok])
  ultimately have "red_mthr.if.hb_completion ?start_state (lift_start_obs start_tid start_heap_obs)"
    by(rule non_speculative_read_into_hb_completion)

  thus ?thesis using wf_prog_wf_syscls[OF wf] J_start_state_sconf_type_ok[OF wf wf_start]
    by(rule sc_legal)(rule ka_allocated)
qed

lemma J_jmm_consistent:
  assumes wf: "wf_J_prog P"
  and hrt: "heap_read_typeable hconf P"
  and wf_start: "wf_start_state P C M vs"
  and ka: "\<Union>(ka_Val ` set vs) \<subseteq> set start_addrs"
  shows "jmm_consistent (J_\<E> P C M vs status) P"
  (is "jmm_consistent ?\<E> P")
proof -
  interpret drf "?\<E>" P using assms by(rule J_drf)
  interpret sc_legal "?\<E>" P using assms by(rule J_sc_legal)
  show ?thesis by unfold_locales
qed

lemma J_ex_sc_exec:
  assumes wf: "wf_J_prog P"
  and hrt: "heap_read_typeable hconf P"
  and wf_start: "wf_start_state P C M vs"
  and ka: "\<Union>(ka_Val ` set vs) \<subseteq> set start_addrs"
  shows "\<exists>E ws. E \<in> J_\<E> P C M vs status \<and> P \<turnstile> (E, ws) \<surd> \<and> sequentially_consistent P (E, ws)"
  (is "\<exists>E ws. _ \<in> ?\<E> \<and> _")
proof -
  interpret jmm: executions_sc_hb ?\<E> P using assms by -(rule executions_sc)

  let ?start_state = "init_fin_lift_state status (J_start_state P C M vs)"
  let ?start_mrw = "mrw_values P Map.empty (map snd (lift_start_obs start_tid start_heap_obs))"

  from red_mthr.if.sequential_completion_Runs[OF red_mthr.if.cut_and_update_imp_sc_completion[OF J_cut_and_update[OF assms]] ta_seq_consist_convert_RA]
  obtain ttas where Red: "red_mthr.mthr.if.mthr.Runs P ?start_state ttas"
    and sc: "ta_seq_consist P ?start_mrw (lconcat (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))" by blast
  let ?E = "lappend (llist_of (lift_start_obs start_tid start_heap_obs)) (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ttas))"
  from Red have "?E \<in> ?\<E>" by(blast intro: red_mthr.mthr.if.\<E>.intros)
  moreover from Red have tsa: "thread_start_actions_ok ?E"
    by(blast intro: red_mthr.thread_start_actions_ok_init_fin red_mthr.mthr.if.\<E>.intros)
  from sc have "ta_seq_consist P Map.empty (lmap snd ?E)"
    unfolding lmap_lappend_distrib lmap_lconcat llist.map_comp split_def o_def lmap_llist_of map_map snd_conv
    by(simp add: ta_seq_consist_lappend ta_seq_consist_start_heap_obs)
  from ta_seq_consist_imp_sequentially_consistent[OF tsa jmm.\<E>_new_actions_for_fun[OF \<open>?E \<in> ?\<E>\<close>] this]
  obtain ws where "sequentially_consistent P (?E, ws)" "P \<turnstile> (?E, ws) \<surd>" by iprover
  ultimately show ?thesis by blast
qed

theorem J_consistent:
  assumes wf: "wf_J_prog P"
  and hrt: "heap_read_typeable hconf P"
  and wf_start: "wf_start_state P C M vs"
  and ka: "\<Union>(ka_Val ` set vs) \<subseteq> set start_addrs"
  shows "\<exists>E ws. legal_execution P (J_\<E> P C M vs status) (E, ws)"
proof -
  let ?\<E> = "J_\<E> P C M vs status"
  interpret sc_legal "?\<E>" P using assms by(rule J_sc_legal)
  from J_ex_sc_exec[OF assms]
  obtain E ws where "E \<in> ?\<E>" "P \<turnstile> (E, ws) \<surd>" "sequentially_consistent P (E, ws)" by blast
  hence "legal_execution P ?\<E> (E, ws)" by(rule SC_is_legal)
  thus ?thesis by blast
qed

end

end
