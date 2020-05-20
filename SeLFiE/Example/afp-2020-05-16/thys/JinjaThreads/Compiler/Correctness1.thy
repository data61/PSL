(*  Title:      JinjaThreads/Compiler/Correctness1.thy
    Author:     Andreas Lochbihler, Tobias Nipkow

    reminiscent of the Jinja theory Compiler/Correctness1
*)

section \<open>Semantic Correctness of Stage 1\<close>

theory Correctness1 imports
  J0J1Bisim
  "../J/DefAssPreservation"
begin

lemma finals_map_Val [simp]: "finals (map Val vs)"
by(simp add: finals_iff)

context J_heap_base begin

lemma \<tau>red0r_preserves_defass:
  assumes wf: "wf_J_prog P"
  shows "\<lbrakk> \<tau>red0r extTA P t h (e, xs) (e', xs'); \<D> e \<lfloor>dom xs\<rfloor> \<rbrakk> \<Longrightarrow> \<D> e' \<lfloor>dom xs'\<rfloor>"
by(induct rule: rtranclp_induct2)(auto dest: red_preserves_defass[OF wf])

lemma \<tau>red0t_preserves_defass:
  assumes wf: "wf_J_prog P"
  shows "\<lbrakk> \<tau>red0t extTA P t h (e, xs) (e', xs'); \<D> e \<lfloor>dom xs\<rfloor> \<rbrakk> \<Longrightarrow> \<D> e' \<lfloor>dom xs'\<rfloor>"
by(rule \<tau>red0r_preserves_defass[OF wf])(rule tranclp_into_rtranclp)

end

lemma LAss_lem:
  "\<lbrakk>x \<in> set xs; size xs \<le> size ys \<rbrakk>
  \<Longrightarrow> m1 \<subseteq>\<^sub>m m2(xs[\<mapsto>]ys) \<Longrightarrow> m1(x\<mapsto>y) \<subseteq>\<^sub>m m2(xs[\<mapsto>]ys[index xs x := y])"
apply(simp add:map_le_def)
apply(simp add:fun_upds_apply index_less_aux eq_sym_conv)
done

lemma Block_lem:
fixes l :: "'a \<rightharpoonup> 'b"
assumes 0: "l \<subseteq>\<^sub>m [Vs [\<mapsto>] ls]"
    and 1: "l' \<subseteq>\<^sub>m [Vs [\<mapsto>] ls', V\<mapsto>v]"
    and hidden: "V \<in> set Vs \<Longrightarrow> ls ! index Vs V = ls' ! index Vs V"
    and size: "size ls = size ls'"    "size Vs < size ls'"
shows "l'(V := l V) \<subseteq>\<^sub>m [Vs [\<mapsto>] ls']"
proof -
  have "l'(V := l V) \<subseteq>\<^sub>m [Vs [\<mapsto>] ls', V\<mapsto>v](V := l V)"
    using 1 by(rule map_le_upd)
  also have "\<dots> = [Vs [\<mapsto>] ls'](V := l V)" by simp
  also have "\<dots> \<subseteq>\<^sub>m [Vs [\<mapsto>] ls']"
  proof (cases "l V")
    case None thus ?thesis by simp
  next
    case (Some w)
    hence "[Vs [\<mapsto>] ls] V = Some w"
      using 0 by(force simp add: map_le_def split:if_splits)
    hence VinVs: "V \<in> set Vs" and w: "w = ls ! index Vs V"
      using size by(auto simp add:fun_upds_apply split:if_splits)
    hence "w = ls' ! index Vs V" using hidden[OF VinVs] by simp
    hence "[Vs [\<mapsto>] ls'](V := l V) = [Vs [\<mapsto>] ls']"
      using Some size VinVs by(simp add:index_less_aux map_upds_upd_conv_index)
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

subsection \<open>Correctness proof\<close>

locale J0_J1_heap_base =
  J?: J_heap_base +
  J1?: J1_heap_base + 
  constrains addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool"
begin

lemma ta_bisim01_extTA2J0_extTA2J1:
  assumes wf: "wf_J_prog P"
  and nt: "\<And>n T C M a h. \<lbrakk> n < length \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>; \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> ! n = NewThread T (C, M, a) h \<rbrakk>
           \<Longrightarrow> typeof_addr h a = \<lfloor>Class_type C\<rfloor> \<and> (\<exists>T meth D. P \<turnstile> C sees M:[]\<rightarrow>T =\<lfloor>meth\<rfloor> in D)"
  shows "ta_bisim01 (extTA2J0 P ta) (extTA2J1 (compP1 P) ta)"
apply(simp add: ta_bisim_def ta_upd_simps)
apply(auto intro!: list_all2_all_nthI)
apply(case_tac "\<lbrace>ta\<rbrace>\<^bsub>t\<^esub> ! n")
  apply(auto simp add: bisim_red0_Red1_def)
apply(drule (1) nt)
apply(clarify)
apply(erule bisim_list_extTA2J0_extTA2J1[OF wf, simplified])
done

lemma red_external_ta_bisim01: 
  "\<lbrakk> wf_J_prog P; P,t \<turnstile> \<langle>a\<bullet>M(vs), h\<rangle> -ta\<rightarrow>ext \<langle>va, h'\<rangle> \<rbrakk> \<Longrightarrow> ta_bisim01 (extTA2J0 P ta) (extTA2J1 (compP1 P) ta)"
apply(rule ta_bisim01_extTA2J0_extTA2J1, assumption)
apply(drule (1) red_external_new_thread_sees, auto simp add: in_set_conv_nth)
apply(drule red_ext_new_thread_heap, auto simp add: in_set_conv_nth)
done

lemmas \<tau>red1t_expr =
  NewArray_\<tau>red1t_xt Cast_\<tau>red1t_xt InstanceOf_\<tau>red1t_xt BinOp_\<tau>red1t_xt1 BinOp_\<tau>red1t_xt2 LAss_\<tau>red1t
  AAcc_\<tau>red1t_xt1 AAcc_\<tau>red1t_xt2 AAss_\<tau>red1t_xt1 AAss_\<tau>red1t_xt2 AAss_\<tau>red1t_xt3
  ALength_\<tau>red1t_xt FAcc_\<tau>red1t_xt FAss_\<tau>red1t_xt1 FAss_\<tau>red1t_xt2 
  CAS_\<tau>red1t_xt1 CAS_\<tau>red1t_xt2 CAS_\<tau>red1t_xt3 Call_\<tau>red1t_obj
  Call_\<tau>red1t_param Block_None_\<tau>red1t_xt Block_\<tau>red1t_Some Sync_\<tau>red1t_xt InSync_\<tau>red1t_xt
  Seq_\<tau>red1t_xt Cond_\<tau>red1t_xt Throw_\<tau>red1t_xt Try_\<tau>red1t_xt

lemmas \<tau>red1r_expr =
  NewArray_\<tau>red1r_xt Cast_\<tau>red1r_xt InstanceOf_\<tau>red1r_xt BinOp_\<tau>red1r_xt1 BinOp_\<tau>red1r_xt2 LAss_\<tau>red1r
  AAcc_\<tau>red1r_xt1 AAcc_\<tau>red1r_xt2 AAss_\<tau>red1r_xt1 AAss_\<tau>red1r_xt2 AAss_\<tau>red1r_xt3
  ALength_\<tau>red1r_xt FAcc_\<tau>red1r_xt FAss_\<tau>red1r_xt1 FAss_\<tau>red1r_xt2
  CAS_\<tau>red1r_xt1 CAS_\<tau>red1r_xt2 CAS_\<tau>red1r_xt3 Call_\<tau>red1r_obj
  Call_\<tau>red1r_param Block_None_\<tau>red1r_xt Block_\<tau>red1r_Some Sync_\<tau>red1r_xt InSync_\<tau>red1r_xt
  Seq_\<tau>red1r_xt Cond_\<tau>red1r_xt Throw_\<tau>red1r_xt Try_\<tau>red1r_xt

definition sim_move01 :: 
  "'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> ('addr, 'thread_id, 'heap) J0_thread_action \<Rightarrow> 'addr expr \<Rightarrow> 'addr expr1 \<Rightarrow> 'heap
  \<Rightarrow> 'addr locals1 \<Rightarrow> ('addr, 'thread_id, 'heap) external_thread_action \<Rightarrow> 'addr expr1 \<Rightarrow> 'heap \<Rightarrow> 'addr locals1 \<Rightarrow> bool"
where
  "sim_move01 P t ta0 e0 e h xs ta e' h' xs' \<longleftrightarrow> \<not> final e0 \<and>
  (if \<tau>move0 P h e0 then h' = h \<and> ta0 = \<epsilon> \<and> ta = \<epsilon> \<and> \<tau>red1't P t h (e, xs) (e', xs')
   else ta_bisim01 ta0 (extTA2J1 P ta) \<and>
     (if call e0 = None \<or> call1 e = None
      then (\<exists>e'' xs''. \<tau>red1'r P t h (e, xs) (e'', xs'') \<and> False,P,t \<turnstile>1 \<langle>e'', (h, xs'')\<rangle> -ta\<rightarrow> \<langle>e', (h', xs')\<rangle> \<and>
                       \<not> \<tau>move1 P h e'')
      else False,P,t \<turnstile>1 \<langle>e, (h, xs)\<rangle> -ta\<rightarrow> \<langle>e', (h', xs')\<rangle> \<and> \<not> \<tau>move1 P h e))"

definition sim_moves01 :: 
  "'addr J1_prog \<Rightarrow> 'thread_id \<Rightarrow> ('addr, 'thread_id, 'heap) J0_thread_action \<Rightarrow> 'addr expr list \<Rightarrow> 'addr expr1 list \<Rightarrow> 'heap
  \<Rightarrow> 'addr locals1 \<Rightarrow> ('addr, 'thread_id, 'heap) external_thread_action \<Rightarrow> 'addr expr1 list \<Rightarrow> 'heap \<Rightarrow> 'addr locals1 \<Rightarrow> bool"
where
  "sim_moves01 P t ta0 es0 es h xs ta es' h' xs' \<longleftrightarrow> \<not> finals es0 \<and>
  (if \<tau>moves0 P h es0 then h' = h \<and> ta0 = \<epsilon> \<and> ta = \<epsilon> \<and> \<tau>reds1't P t h (es, xs) (es', xs')
   else ta_bisim01 ta0 (extTA2J1 P ta) \<and>
     (if calls es0 = None \<or> calls1 es = None
      then (\<exists>es'' xs''. \<tau>reds1'r P t h (es, xs) (es'', xs'') \<and> False,P,t \<turnstile>1 \<langle>es'', (h, xs'')\<rangle> [-ta\<rightarrow>] \<langle>es', (h', xs')\<rangle> \<and> 
                        \<not> \<tau>moves1 P h es'')
      else False,P,t \<turnstile>1 \<langle>es, (h, xs)\<rangle> [-ta\<rightarrow>] \<langle>es', (h', xs')\<rangle> \<and> \<not> \<tau>moves1 P h es))"

declare \<tau>red1t_expr [elim!] \<tau>red1r_expr[elim!]

lemma sim_move01_expr:
  assumes "sim_move01 P t ta0 e0 e h xs ta e' h' xs'"
  shows
  "sim_move01 P t ta0 (newA T\<lfloor>e0\<rceil>) (newA T\<lfloor>e\<rceil>) h xs ta (newA T\<lfloor>e'\<rceil>) h' xs'"
  "sim_move01 P t ta0 (Cast T e0) (Cast T e) h xs ta (Cast T e') h' xs'"
  "sim_move01 P t ta0 (e0 instanceof T) (e instanceof T) h xs ta (e' instanceof T) h' xs'"
  "sim_move01 P t ta0 (e0 \<guillemotleft>bop\<guillemotright> e2) (e \<guillemotleft>bop\<guillemotright> e2') h xs ta (e' \<guillemotleft>bop\<guillemotright> e2') h' xs'"
  "sim_move01 P t ta0 (Val v \<guillemotleft>bop\<guillemotright> e0) (Val v \<guillemotleft>bop\<guillemotright> e) h xs ta (Val v \<guillemotleft>bop\<guillemotright> e') h' xs'"
  "sim_move01 P t ta0 (V := e0) (V' := e) h xs ta (V' := e') h' xs'"
  "sim_move01 P t ta0 (e0\<lfloor>e2\<rceil>) (e\<lfloor>e2'\<rceil>) h xs ta (e'\<lfloor>e2'\<rceil>) h' xs'"
  "sim_move01 P t ta0 (Val v\<lfloor>e0\<rceil>) (Val v\<lfloor>e\<rceil>) h xs ta (Val v\<lfloor>e'\<rceil>) h' xs'"
  "sim_move01 P t ta0 (e0\<lfloor>e2\<rceil> := e3) (e\<lfloor>e2'\<rceil> := e3') h xs ta (e'\<lfloor>e2'\<rceil> := e3') h' xs'"
  "sim_move01 P t ta0 (Val v\<lfloor>e0\<rceil> := e3) (Val v\<lfloor>e\<rceil> := e3') h xs ta (Val v\<lfloor>e'\<rceil> := e3') h' xs'"
  "sim_move01 P t ta0 (AAss (Val v) (Val v') e0) (AAss (Val v) (Val v') e) h xs ta (AAss (Val v) (Val v') e') h' xs'"
  "sim_move01 P t ta0 (e0\<bullet>length) (e\<bullet>length) h xs ta (e'\<bullet>length) h' xs'"
  "sim_move01 P t ta0 (e0\<bullet>F{D}) (e\<bullet>F'{D'}) h xs ta (e'\<bullet>F'{D'}) h' xs'"
  "sim_move01 P t ta0 (FAss e0 F D e2) (FAss e F' D' e2') h xs ta (FAss e' F' D' e2') h' xs'"
  "sim_move01 P t ta0 (FAss (Val v) F D e0) (FAss (Val v) F' D' e) h xs ta (FAss (Val v) F' D' e') h' xs'"
  "sim_move01 P t ta0 (CompareAndSwap e0 D F e2 e3) (CompareAndSwap e D F e2' e3') h xs ta (CompareAndSwap e' D F e2' e3') h' xs'"
  "sim_move01 P t ta0 (CompareAndSwap (Val v) D F e0 e3) (CompareAndSwap (Val v) D F e e3') h xs ta (CompareAndSwap (Val v) D F e' e3') h' xs'"
  "sim_move01 P t ta0 (CompareAndSwap (Val v) D F (Val v') e0) (CompareAndSwap (Val v) D F (Val v') e) h xs ta (CompareAndSwap (Val v) D F (Val v') e') h' xs'"
  "sim_move01 P t ta0 (e0\<bullet>M(es)) (e\<bullet>M(es')) h xs ta (e'\<bullet>M(es')) h' xs'"
  "sim_move01 P t ta0 ({V:T=vo; e0}) ({V':T=None; e}) h xs ta ({V':T=None; e'}) h' xs'"
  "sim_move01 P t ta0 (sync(e0) e2) (sync\<^bsub>V'\<^esub>(e) e2') h xs ta (sync\<^bsub>V'\<^esub>(e') e2') h' xs'"
  "sim_move01 P t ta0 (insync(a) e0) (insync\<^bsub>V'\<^esub>(a') e) h xs ta (insync\<^bsub>V'\<^esub>(a') e') h' xs'"
  "sim_move01 P t ta0 (e0;;e2) (e;;e2') h xs ta (e';;e2') h' xs'"
  "sim_move01 P t ta0 (if (e0) e2 else e3) (if (e) e2' else e3') h xs ta (if (e') e2' else e3') h' xs'"
  "sim_move01 P t ta0 (throw e0) (throw e) h xs ta (throw e') h' xs'"
  "sim_move01 P t ta0 (try e0 catch(C V) e2) (try e catch(C' V') e2') h xs ta (try e' catch(C' V') e2') h' xs'"
using assms
apply(simp_all add: sim_move01_def final_iff \<tau>red1r_Val \<tau>red1t_Val split: if_split_asm split del: if_split)
apply(fastforce simp add: final_iff \<tau>red1r_Val \<tau>red1t_Val split!: if_splits intro: red1_reds1.intros)+
done

lemma sim_moves01_expr:
  "sim_move01 P t ta0 e0 e h xs ta e' h' xs' \<Longrightarrow> sim_moves01 P t ta0 (e0 # es2) (e # es2') h xs ta (e' # es2') h' xs'"
  "sim_moves01 P t ta0 es0 es h xs ta es' h' xs' \<Longrightarrow> sim_moves01 P t ta0 (Val v # es0) (Val v # es) h xs ta (Val v # es') h' xs'"
apply(simp_all add: sim_move01_def sim_moves01_def final_iff finals_iff Cons_eq_append_conv \<tau>red1t_Val \<tau>red1r_Val split: if_split_asm split del: if_split)
apply(auto simp add: Cons_eq_append_conv \<tau>red1t_Val \<tau>red1r_Val split!: if_splits intro: List1Red1 List1Red2 \<tau>red1t_inj_\<tau>reds1t \<tau>red1r_inj_\<tau>reds1r \<tau>reds1t_cons_\<tau>reds1t \<tau>reds1r_cons_\<tau>reds1r)
apply(force elim!: \<tau>red1r_inj_\<tau>reds1r List1Red1)
apply(force elim!: \<tau>red1r_inj_\<tau>reds1r List1Red1)
apply(force elim!: \<tau>red1r_inj_\<tau>reds1r List1Red1)
apply(force elim!: \<tau>red1r_inj_\<tau>reds1r List1Red1)
apply(force elim!: \<tau>reds1r_cons_\<tau>reds1r intro!: List1Red2)
apply(force elim!: \<tau>reds1r_cons_\<tau>reds1r intro!: List1Red2)
done

lemma sim_move01_CallParams:
  "sim_moves01 P t ta0 es0 es h xs ta es' h' xs'
  \<Longrightarrow> sim_move01 P t ta0 (Val v\<bullet>M(es0)) (Val v\<bullet>M(es)) h xs ta (Val v\<bullet>M(es')) h' xs'"
apply(clarsimp simp add: sim_move01_def sim_moves01_def \<tau>reds1r_map_Val \<tau>reds1t_map_Val is_vals_conv split: if_split_asm split del: if_split)
  apply(fastforce simp add: sim_move01_def sim_moves01_def \<tau>reds1r_map_Val \<tau>reds1t_map_Val intro: Call_\<tau>red1r_param Call1Params)
 apply(rule conjI, fastforce)
 apply(split if_split)
 apply(rule conjI)
  apply(clarsimp simp add: finals_iff)
 apply(clarify)
 apply(split if_split)
 apply(rule conjI)
  apply(simp del: call.simps calls.simps call1.simps calls1.simps)
  apply(fastforce simp add: sim_move01_def sim_moves01_def \<tau>red1r_Val \<tau>red1t_Val \<tau>reds1r_map_Val_Throw intro: Call_\<tau>red1r_param Call1Params split: if_split_asm)
 apply(fastforce split: if_split_asm simp add: is_vals_conv \<tau>reds1r_map_Val \<tau>reds1r_map_Val_Throw)
apply(rule conjI, fastforce)
apply(fastforce simp add: sim_move01_def sim_moves01_def \<tau>red1r_Val \<tau>red1t_Val \<tau>reds1t_map_Val \<tau>reds1r_map_Val is_vals_conv intro: Call_\<tau>red1r_param Call1Params split: if_split_asm)
done

lemma sim_move01_reds:
  "\<lbrakk> (h', a) \<in> allocate h (Class_type C); ta0 = \<lbrace>NewHeapElem a (Class_type C)\<rbrace>; ta = \<lbrace>NewHeapElem a (Class_type C)\<rbrace> \<rbrakk>
  \<Longrightarrow> sim_move01 P t ta0 (new C) (new C) h xs ta (addr a) h' xs"
  "allocate h (Class_type C) = {} \<Longrightarrow> sim_move01 P t \<epsilon> (new C) (new C) h xs \<epsilon> (THROW OutOfMemory) h xs"
  "\<lbrakk> (h', a) \<in> allocate h (Array_type T (nat (sint i))); 0 <=s i;
     ta0 = \<lbrace>NewHeapElem a (Array_type T (nat (sint i)))\<rbrace>; ta = \<lbrace>NewHeapElem a (Array_type T (nat (sint i)))\<rbrace> \<rbrakk>
  \<Longrightarrow> sim_move01 P t ta0 (newA T\<lfloor>Val (Intg i)\<rceil>) (newA T\<lfloor>Val (Intg i)\<rceil>) h xs ta (addr a) h' xs"
  "i <s 0 \<Longrightarrow> sim_move01 P t \<epsilon> (newA T\<lfloor>Val (Intg i)\<rceil>) (newA T\<lfloor>Val (Intg i)\<rceil>) h xs \<epsilon> (THROW NegativeArraySize) h xs"
  "\<lbrakk> allocate h (Array_type T (nat (sint i))) = {}; 0 <=s i \<rbrakk>
  \<Longrightarrow> sim_move01 P t \<epsilon> (newA T\<lfloor>Val (Intg i)\<rceil>) (newA T\<lfloor>Val (Intg i)\<rceil>) h xs \<epsilon> (THROW OutOfMemory) h xs"
  "\<lbrakk> typeof\<^bsub>h\<^esub> v = \<lfloor>U\<rfloor>; P \<turnstile> U \<le> T \<rbrakk>
  \<Longrightarrow> sim_move01 P t \<epsilon> (Cast T (Val v)) (Cast T (Val v)) h xs \<epsilon> (Val v) h xs"
  "\<lbrakk> typeof\<^bsub>h\<^esub> v = \<lfloor>U\<rfloor>; \<not> P \<turnstile> U \<le> T \<rbrakk>
  \<Longrightarrow> sim_move01 P t \<epsilon> (Cast T (Val v)) (Cast T (Val v)) h xs \<epsilon> (THROW ClassCast) h xs"
  "\<lbrakk> typeof\<^bsub>h\<^esub> v = \<lfloor>U\<rfloor>; b \<longleftrightarrow> v \<noteq> Null \<and> P \<turnstile> U \<le> T \<rbrakk>
  \<Longrightarrow> sim_move01 P t \<epsilon> ((Val v) instanceof T) ((Val v) instanceof T) h xs \<epsilon> (Val (Bool b)) h xs"
  "binop bop v1 v2 = Some (Inl v) \<Longrightarrow> sim_move01 P t \<epsilon> ((Val v1) \<guillemotleft>bop\<guillemotright> (Val v2)) (Val v1 \<guillemotleft>bop\<guillemotright> Val v2) h xs \<epsilon> (Val v) h xs"
  "binop bop v1 v2 = Some (Inr a) \<Longrightarrow> sim_move01 P t \<epsilon> ((Val v1) \<guillemotleft>bop\<guillemotright> (Val v2)) (Val v1 \<guillemotleft>bop\<guillemotright> Val v2) h xs \<epsilon> (Throw a) h xs"
  "\<lbrakk> xs!V = v; V < size xs \<rbrakk> \<Longrightarrow> sim_move01 P t \<epsilon> (Var V') (Var V) h xs \<epsilon> (Val v) h xs"
  "V < length xs \<Longrightarrow> sim_move01 P t \<epsilon> (V' := Val v) (V := Val v) h xs \<epsilon> unit h (xs[V := v])"
  "sim_move01 P t \<epsilon> (null\<lfloor>Val v\<rceil>) (null\<lfloor>Val v\<rceil>) h xs \<epsilon> (THROW NullPointer) h xs"
  "\<lbrakk> typeof_addr h a = \<lfloor>Array_type T n\<rfloor>; i <s 0 \<or> sint i \<ge> int n \<rbrakk>
  \<Longrightarrow> sim_move01 P t \<epsilon> (addr a\<lfloor>Val (Intg i)\<rceil>) ((addr a)\<lfloor>Val (Intg i)\<rceil>) h xs \<epsilon> (THROW ArrayIndexOutOfBounds) h xs"
  "\<lbrakk> typeof_addr h a = \<lfloor>Array_type T n\<rfloor>; 0 <=s i; sint i < int n;
     heap_read h a (ACell (nat (sint i))) v;
     ta0 = \<lbrace>ReadMem a (ACell (nat (sint i))) v\<rbrace>; 
     ta = \<lbrace>ReadMem a (ACell (nat (sint i))) v\<rbrace> \<rbrakk>
  \<Longrightarrow> sim_move01 P t ta0 (addr a\<lfloor>Val (Intg i)\<rceil>) ((addr a)\<lfloor>Val (Intg i)\<rceil>) h xs ta (Val v) h xs"
  "sim_move01 P t \<epsilon> (null\<lfloor>Val v\<rceil> := Val v') (null\<lfloor>Val v\<rceil> := Val v') h xs \<epsilon> (THROW NullPointer) h xs"
  "\<lbrakk> typeof_addr h a = \<lfloor>Array_type T n\<rfloor>; i <s 0 \<or> sint i \<ge> int n \<rbrakk>
  \<Longrightarrow> sim_move01 P t \<epsilon> (AAss (addr a) (Val (Intg i)) (Val v)) (AAss (addr a) (Val (Intg i)) (Val v)) h xs \<epsilon> (THROW ArrayIndexOutOfBounds) h xs"
 "\<lbrakk> typeof_addr h a = \<lfloor>Array_type T n\<rfloor>; 0 <=s i; sint i < int n; typeof\<^bsub>h\<^esub> v = \<lfloor>U\<rfloor>; \<not> (P \<turnstile> U \<le> T) \<rbrakk>
  \<Longrightarrow> sim_move01 P t \<epsilon> (AAss (addr a) (Val (Intg i)) (Val v)) (AAss (addr a) (Val (Intg i)) (Val v)) h xs \<epsilon> (THROW ArrayStore) h xs"
  "\<lbrakk> typeof_addr h a = \<lfloor>Array_type T n\<rfloor>; 0 <=s i; sint i < int n; typeof\<^bsub>h\<^esub> v = Some U; P \<turnstile> U \<le> T;
     heap_write h a (ACell (nat (sint i))) v h'; 
     ta0 = \<lbrace>WriteMem a (ACell (nat (sint i))) v\<rbrace>; ta = \<lbrace>WriteMem a (ACell (nat (sint i))) v \<rbrace> \<rbrakk>
  \<Longrightarrow> sim_move01 P t ta0 (AAss (addr a) (Val (Intg i)) (Val v)) (AAss (addr a) (Val (Intg i)) (Val v)) h xs ta unit h' xs"
  "typeof_addr h a = \<lfloor>Array_type T n\<rfloor> \<Longrightarrow> sim_move01 P t \<epsilon> (addr a\<bullet>length) (addr a\<bullet>length) h xs \<epsilon> (Val (Intg (word_of_int (int n)))) h xs"
  "sim_move01 P t \<epsilon> (null\<bullet>length) (null\<bullet>length) h xs \<epsilon> (THROW NullPointer) h xs"

  "\<lbrakk> heap_read h a (CField D F) v; ta0 = \<lbrace>ReadMem a (CField D F) v\<rbrace>; ta = \<lbrace>ReadMem a (CField D F) v\<rbrace> \<rbrakk>
  \<Longrightarrow> sim_move01 P t ta0 (addr a\<bullet>F{D}) (addr a\<bullet>F{D}) h xs ta (Val v) h xs"
  "sim_move01 P t \<epsilon> (null\<bullet>F{D}) (null\<bullet>F{D}) h xs \<epsilon> (THROW NullPointer) h xs"
  "\<lbrakk> heap_write h a (CField D F) v h'; ta0 = \<lbrace>WriteMem a (CField D F) v\<rbrace>; ta = \<lbrace>WriteMem a (CField D F) v\<rbrace> \<rbrakk>
  \<Longrightarrow> sim_move01 P t ta0 (addr a\<bullet>F{D} := Val v) (addr a\<bullet>F{D} := Val v) h xs ta unit h' xs"
  "sim_move01 P t \<epsilon> (null\<bullet>compareAndSwap(D\<bullet>F, Val v, Val v')) (null\<bullet>compareAndSwap(D\<bullet>F, Val v, Val v')) h xs \<epsilon> (THROW NullPointer) h xs"
  "\<lbrakk> heap_read h a (CField D F) v''; heap_write h a (CField D F) v' h'; v'' = v; 
     ta0 = \<lbrace>ReadMem a (CField D F) v'', WriteMem a (CField D F) v'\<rbrace>; ta = \<lbrace>ReadMem a (CField D F) v'', WriteMem a (CField D F) v'\<rbrace> \<rbrakk>
  \<Longrightarrow> sim_move01 P t ta0 (addr a\<bullet>compareAndSwap(D\<bullet>F, Val v, Val v')) (addr a\<bullet>compareAndSwap(D\<bullet>F, Val v, Val v')) h xs ta true h' xs"
  "\<lbrakk> heap_read h a (CField D F) v''; v'' \<noteq> v; 
     ta0 = \<lbrace>ReadMem a (CField D F) v''\<rbrace>; ta = \<lbrace>ReadMem a (CField D F) v''\<rbrace> \<rbrakk>
  \<Longrightarrow> sim_move01 P t ta0 (addr a\<bullet>compareAndSwap(D\<bullet>F, Val v, Val v')) (addr a\<bullet>compareAndSwap(D\<bullet>F, Val v, Val v')) h xs ta false h xs"
  "sim_move01 P t \<epsilon> (null\<bullet>F{D} := Val v) (null\<bullet>F{D} := Val v) h xs \<epsilon> (THROW NullPointer) h xs"
  "sim_move01 P t \<epsilon> ({V':T=vo; Val u}) ({V:T=None; Val u}) h xs \<epsilon> (Val u) h xs"
  "V < length xs \<Longrightarrow> sim_move01 P t \<epsilon> (sync(null) e0) (sync\<^bsub>V\<^esub> (null) e1) h xs \<epsilon> (THROW NullPointer) h (xs[V := Null])"
  "sim_move01 P t \<epsilon> (Val v;;e0) (Val v;; e1) h xs \<epsilon> e1 h xs"
  "sim_move01 P t \<epsilon> (if (true) e0 else e0') (if (true) e1 else e1') h xs \<epsilon> e1 h xs"
  "sim_move01 P t \<epsilon> (if (false) e0 else e0') (if (false) e1 else e1') h xs \<epsilon> e1' h xs"
  "sim_move01 P t \<epsilon> (throw null) (throw null) h xs \<epsilon> (THROW NullPointer) h xs"
  "sim_move01 P t \<epsilon> (try (Val v) catch(C V') e0) (try (Val v) catch(C V) e1) h xs \<epsilon> (Val v) h xs"
  "\<lbrakk> typeof_addr h a = \<lfloor>Class_type D\<rfloor>; P \<turnstile> D \<preceq>\<^sup>* C; V < length xs \<rbrakk>
  \<Longrightarrow> sim_move01 P t \<epsilon> (try (Throw a) catch(C V') e0) (try (Throw a) catch(C V) e1) h xs \<epsilon> ({V:Class C=None; e1}) h (xs[V := Addr a])"
  "sim_move01 P t \<epsilon> (newA T\<lfloor>Throw a\<rceil>) (newA T\<lfloor>Throw a\<rceil>) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P t \<epsilon> (Cast T (Throw a)) (Cast T (Throw a)) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P t \<epsilon> ((Throw a) instanceof T) ((Throw a) instanceof T) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P t \<epsilon> ((Throw a) \<guillemotleft>bop\<guillemotright> e0) ((Throw a) \<guillemotleft>bop\<guillemotright> e1) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P t \<epsilon> (Val v \<guillemotleft>bop\<guillemotright> (Throw a)) (Val v \<guillemotleft>bop\<guillemotright> (Throw a)) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P t \<epsilon> (V' := Throw a) (V := Throw a) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P t \<epsilon> (Throw a\<lfloor>e0\<rceil>) (Throw a\<lfloor>e1\<rceil>) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P t \<epsilon> (Val v\<lfloor>Throw a\<rceil>) (Val v\<lfloor>Throw a\<rceil>) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P t \<epsilon> (Throw a\<lfloor>e0\<rceil> := e0') (Throw a\<lfloor>e1\<rceil> := e1') h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P t \<epsilon> (Val v\<lfloor>Throw a\<rceil> := e0) (Val v\<lfloor>Throw a\<rceil> := e1) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P t \<epsilon> (Val v\<lfloor>Val v'\<rceil> := Throw a) (Val v\<lfloor>Val v'\<rceil> := Throw a) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P t \<epsilon> (Throw a\<bullet>length) (Throw a\<bullet>length) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P t \<epsilon> (Throw a\<bullet>F{D}) (Throw a\<bullet>F{D}) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P t \<epsilon> (Throw a\<bullet>F{D} := e0) (Throw a\<bullet>F{D} := e1) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P t \<epsilon> (Val v\<bullet>F{D} := Throw a) (Val v\<bullet>F{D} := Throw a) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P t \<epsilon> (Throw a\<bullet>compareAndSwap(D\<bullet>F, e2, e3)) (Throw a\<bullet>compareAndSwap(D\<bullet>F, e2', e3')) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P t \<epsilon> (Val v\<bullet>compareAndSwap(D\<bullet>F, Throw a, e3)) (Val v\<bullet>compareAndSwap(D\<bullet>F, Throw a, e3')) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P t \<epsilon> (Val v\<bullet>compareAndSwap(D\<bullet>F, Val v', Throw a)) (Val v\<bullet>compareAndSwap(D\<bullet>F, Val v', Throw a)) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P t \<epsilon> (Throw a\<bullet>M(es0)) (Throw a\<bullet>M(es1)) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P t \<epsilon> ({V':T=vo; Throw a}) ({V:T=None; Throw a}) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P t \<epsilon> (sync(Throw a) e0) (sync\<^bsub>V\<^esub>(Throw a) e1) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P t \<epsilon> (Throw a;;e0) (Throw a;;e1) h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P t \<epsilon> (if (Throw a) e0 else e0') (if (Throw a) e1 else e1') h xs \<epsilon> (Throw a) h xs"
  "sim_move01 P t \<epsilon> (throw (Throw a)) (throw (Throw a)) h xs \<epsilon> (Throw a) h xs"
apply(simp_all add: sim_move01_def ta_bisim_def split: if_split_asm split del: if_split)
apply(fastforce intro: red1_reds1.intros)+
done

lemma sim_move01_ThrowParams:
  "sim_move01 P t \<epsilon> (Val v\<bullet>M(map Val vs @ Throw a # es0)) (Val v\<bullet>M(map Val vs @ Throw a # es1)) h xs \<epsilon> (Throw a) h xs"
apply(simp add: sim_move01_def split del: if_split)
apply(rule conjI, fastforce)
apply(split if_split)
apply(rule conjI)
 apply(fastforce intro: red1_reds1.intros)
apply(fastforce simp add: sim_move01_def intro: red1_reds1.intros)
done

lemma sim_move01_CallNull:
  "sim_move01 P t \<epsilon> (null\<bullet>M(map Val vs)) (null\<bullet>M(map Val vs)) h xs \<epsilon> (THROW NullPointer) h xs"
by(fastforce simp add: sim_move01_def map_eq_append_conv intro: red1_reds1.intros)

lemma sim_move01_SyncLocks:
  "\<lbrakk> V < length xs; ta0 = \<lbrace>Lock\<rightarrow>a, SyncLock a\<rbrace>; ta = \<lbrace>Lock\<rightarrow>a, SyncLock a\<rbrace> \<rbrakk>
   \<Longrightarrow> sim_move01 P t ta0 (sync(addr a) e0) (sync\<^bsub>V\<^esub> (addr a) e1) h xs ta (insync\<^bsub>V\<^esub> (a) e1) h (xs[V := Addr a])"
  "\<lbrakk> xs ! V = Addr a'; V < length xs; ta0 = \<lbrace>Unlock\<rightarrow>a', SyncUnlock a'\<rbrace>; ta = \<lbrace>Unlock\<rightarrow>a', SyncUnlock a'\<rbrace> \<rbrakk>
  \<Longrightarrow> sim_move01 P t ta0 (insync(a') (Val v)) (insync\<^bsub>V\<^esub> (a) (Val v)) h xs ta (Val v) h xs"
  "\<lbrakk> xs ! V = Addr a'; V < length xs; ta0 = \<lbrace>Unlock\<rightarrow>a', SyncUnlock a'\<rbrace>; ta = \<lbrace>Unlock\<rightarrow>a', SyncUnlock a'\<rbrace> \<rbrakk>
  \<Longrightarrow> sim_move01 P t ta0 (insync(a') (Throw a'')) (insync\<^bsub>V\<^esub> (a) (Throw a'')) h xs ta (Throw a'') h xs"
by(fastforce simp add: sim_move01_def ta_bisim_def expand_finfun_eq fun_eq_iff finfun_upd_apply ta_upd_simps  intro: red1_reds1.intros[simplified] split: if_split_asm)+

lemma sim_move01_TryFail:
  "\<lbrakk> typeof_addr h a = \<lfloor>Class_type D\<rfloor>; \<not> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> sim_move01 P t \<epsilon> (try (Throw a) catch(C V') e0) (try (Throw a) catch(C V) e1) h xs \<epsilon> (Throw a) h xs"
by(auto simp add: sim_move01_def intro!: Red1TryFail)

lemma sim_move01_BlockSome:
  "\<lbrakk> sim_move01 P t ta0 e0 e h (xs[V := v]) ta e' h' xs'; V < length xs \<rbrakk>
  \<Longrightarrow> sim_move01 P t ta0 ({V':T=\<lfloor>v\<rfloor>; e0}) ({V:T=\<lfloor>v\<rfloor>; e}) h xs ta ({V:T=None; e'}) h' xs'"
  "V < length xs \<Longrightarrow> sim_move01 P t \<epsilon> ({V':T=\<lfloor>v\<rfloor>; Val u}) ({V:T=\<lfloor>v\<rfloor>; Val u}) h xs \<epsilon> (Val u) h (xs[V := v])"
  "V < length xs \<Longrightarrow> sim_move01 P t \<epsilon> ({V':T=\<lfloor>v\<rfloor>; Throw a}) ({V:T=\<lfloor>v\<rfloor>; Throw a}) h xs \<epsilon> (Throw a) h (xs[V := v])"
apply(auto simp add: sim_move01_def)
apply(split if_split_asm)
 apply(fastforce intro: intro: converse_rtranclp_into_rtranclp Block1Some Block1Red Block_\<tau>red1r_Some)
apply(fastforce intro: intro: converse_rtranclp_into_rtranclp Block1Some Block1Red Block_\<tau>red1r_Some)
apply(fastforce simp add: sim_move01_def intro!: \<tau>red1t_2step[OF Block1Some] \<tau>red1r_1step[OF Block1Some] Red1Block Block1Throw)+
done

lemmas sim_move01_intros =
  sim_move01_expr sim_move01_reds sim_move01_ThrowParams sim_move01_CallNull sim_move01_TryFail
  sim_move01_BlockSome sim_move01_CallParams

declare sim_move01_intros[intro]

lemma sim_move01_preserves_len: "sim_move01 P t ta0 e0 e h xs ta e' h' xs' \<Longrightarrow> length xs' = length xs"
by(fastforce simp add: sim_move01_def split: if_split_asm dest: \<tau>red1r_preserves_len \<tau>red1t_preserves_len red1_preserves_len)

lemma sim_move01_preserves_unmod:
  "\<lbrakk> sim_move01 P t ta0 e0 e h xs ta e' h' xs'; unmod e i; i < length xs \<rbrakk> \<Longrightarrow> xs' ! i = xs ! i"
apply(auto simp add: sim_move01_def split: if_split_asm dest: \<tau>red1t_preserves_unmod)
apply(frule (2) \<tau>red1'r_preserves_unmod)
apply(frule (1) \<tau>red1r_unmod_preserved)
apply(frule \<tau>red1r_preserves_len)
apply(auto dest: red1_preserves_unmod)
apply(frule (2) \<tau>red1'r_preserves_unmod)
apply(frule (1) \<tau>red1r_unmod_preserved)
apply(frule \<tau>red1r_preserves_len)
apply(auto dest: red1_preserves_unmod)
done

lemma assumes wf: "wf_J_prog P"
  shows red1_simulates_red_aux:
  "\<lbrakk> extTA2J0 P,P,t \<turnstile> \<langle>e1, S\<rangle> -TA\<rightarrow> \<langle>e1', S'\<rangle>; bisim vs e1 e2 XS; fv e1 \<subseteq> set vs;
     lcl S \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_vars e1 \<le> length XS;
     \<forall>aMvs. call e1 = \<lfloor>aMvs\<rfloor> \<longrightarrow> synthesized_call P (hp S) aMvs \<rbrakk>
  \<Longrightarrow> \<exists>ta e2' XS'. sim_move01 (compP1 P) t TA e1 e2 (hp S) XS ta e2' (hp S') XS' \<and> bisim vs e1' e2' XS' \<and> lcl S' \<subseteq>\<^sub>m [vs [\<mapsto>] XS']"
  (is "\<lbrakk> _; _; _; _; _; ?synth e1 S \<rbrakk> \<Longrightarrow> ?concl e1 e2 S XS e1' S' TA vs")

  and reds1_simulates_reds_aux:
  "\<lbrakk> extTA2J0 P,P,t \<turnstile> \<langle>es1, S\<rangle> [-TA\<rightarrow>] \<langle>es1', S'\<rangle>; bisims vs es1 es2 XS; fvs es1 \<subseteq> set vs;
    lcl S \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_varss es1 \<le> length XS;
    \<forall>aMvs. calls es1 = \<lfloor>aMvs\<rfloor> \<longrightarrow> synthesized_call P (hp S) aMvs \<rbrakk>
  \<Longrightarrow> \<exists>ta es2' xs'. sim_moves01 (compP1 P) t TA es1 es2 (hp S) XS ta es2' (hp S') xs' \<and> bisims vs es1' es2' xs' \<and> lcl S' \<subseteq>\<^sub>m [vs [\<mapsto>] xs']"
  (is "\<lbrakk> _; _; _; _; _; ?synths es1 S \<rbrakk> \<Longrightarrow> ?concls es1 es2 S XS es1' S' TA vs")
proof(induct arbitrary: vs e2 XS and vs es2 XS rule: red_reds.inducts)
  case (BinOpRed1 e s ta e' s' bop e2 Vs E2 xs)
  note IH = \<open>\<And>vs e2 XS. \<lbrakk>bisim vs e e2 XS; fv e \<subseteq> set vs; lcl s \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_vars e \<le> length XS;
            ?synth e s \<rbrakk> \<Longrightarrow> ?concl e e2 s XS e' s' ta vs\<close>
  from \<open>extTA2J0 P,P,t \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>\<close> have "\<not> is_val e" by auto
  with \<open>bisim Vs (e \<guillemotleft>bop\<guillemotright> e2) E2 xs\<close> obtain E
    where "E2 = E \<guillemotleft>bop\<guillemotright> compE1 Vs e2" and "bisim Vs e E xs" and "\<not> contains_insync e2" by auto
  with IH[of Vs E xs] \<open>fv (e \<guillemotleft>bop\<guillemotright> e2) \<subseteq> set Vs\<close> \<open>lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]\<close> \<open>\<not> is_val e\<close>
    \<open>length Vs + max_vars (e \<guillemotleft>bop\<guillemotright> e2) \<le> length xs\<close> \<open>?synth (e \<guillemotleft>bop\<guillemotright> e2) s\<close> \<open>extTA2J0 P,P,t \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>\<close>
  show ?case by(cases "is_val e'")(fastforce elim!: sim_move01_expr)+
next
  case (BinOpRed2 e s ta e' s' v bop Vs E2 xs)
  note IH = \<open>\<And>vs e2 XS. \<lbrakk>bisim vs e e2 XS; fv e \<subseteq> set vs; lcl s \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_vars e \<le> length XS;
            ?synth e s \<rbrakk> \<Longrightarrow> ?concl e e2 s XS e' s' ta vs\<close>
  from \<open>bisim Vs (Val v \<guillemotleft>bop\<guillemotright> e) E2 xs\<close> obtain E
    where "E2 = Val v \<guillemotleft>bop\<guillemotright> E" and "bisim Vs e E xs" by auto
  with IH[of Vs E xs] \<open>fv (Val v \<guillemotleft>bop\<guillemotright> e) \<subseteq> set Vs\<close> \<open>lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]\<close>
    \<open>length Vs + max_vars (Val v \<guillemotleft>bop\<guillemotright> e) \<le> length xs\<close> \<open>?synth (Val v \<guillemotleft>bop\<guillemotright> e) s\<close> \<open>extTA2J0 P,P,t \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>\<close>
  show ?case by(fastforce elim!: sim_move01_expr)
next
  case RedVar thus ?case
    by(fastforce simp add: index_less_aux map_le_def fun_upds_apply intro!: exI dest: bspec)
next
  case RedLAss thus ?case
    by(fastforce intro: index_less_aux LAss_lem intro!: exI simp del: fun_upd_apply)
next
  case (AAccRed1 a s ta a' s' i Vs E2 xs)
  note IH = \<open>\<And>vs e2 XS. \<lbrakk>bisim vs a e2 XS; fv a \<subseteq> set vs; lcl s \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_vars a \<le> length XS;
            ?synth a s \<rbrakk> \<Longrightarrow> ?concl a e2 s XS a' s' ta vs\<close>
  from \<open>extTA2J0 P,P,t \<turnstile> \<langle>a,s\<rangle> -ta\<rightarrow> \<langle>a',s'\<rangle>\<close> have "\<not> is_val a" by auto
  with \<open>bisim Vs (a\<lfloor>i\<rceil>) E2 xs\<close> obtain E
    where "E2 = E\<lfloor>compE1 Vs i\<rceil>" and "bisim Vs a E xs" and "\<not> contains_insync i" by auto
  with IH[of Vs E xs] \<open>fv (a\<lfloor>i\<rceil>) \<subseteq> set Vs\<close> \<open>lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]\<close> \<open>\<not> is_val a\<close>
    \<open>length Vs + max_vars (a\<lfloor>i\<rceil>) \<le> length xs\<close> \<open>?synth (a\<lfloor>i\<rceil>) s\<close> \<open>extTA2J0 P,P,t \<turnstile> \<langle>a,s\<rangle> -ta\<rightarrow> \<langle>a',s'\<rangle>\<close>
  show ?case by(cases "is_val a'")(fastforce elim!: sim_move01_expr)+
next
  case (AAccRed2 i s ta i' s' a Vs E2 xs)
  note IH = \<open>\<And>vs e2 XS. \<lbrakk>bisim vs i e2 XS; fv i \<subseteq> set vs; lcl s \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_vars i \<le> length XS;
            ?synth i s \<rbrakk> \<Longrightarrow> ?concl i e2 s XS i' s' ta vs\<close>
  from \<open>bisim Vs (Val a\<lfloor>i\<rceil>) E2 xs\<close> obtain E
    where "E2 = Val a\<lfloor>E\<rceil>" and "bisim Vs i E xs" by auto
  with IH[of Vs E xs] \<open>fv (Val a\<lfloor>i\<rceil>) \<subseteq> set Vs\<close> \<open>lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]\<close>
    \<open>length Vs + max_vars (Val a\<lfloor>i\<rceil>) \<le> length xs\<close> \<open>?synth (Val a\<lfloor>i\<rceil>) s\<close> \<open>extTA2J0 P,P,t \<turnstile> \<langle>i,s\<rangle> -ta\<rightarrow> \<langle>i',s'\<rangle>\<close>
  show ?case by(fastforce elim!: sim_move01_expr)
next
  case RedAAcc thus ?case by(auto simp del: split_paired_Ex)
next
  case (AAssRed1 a s ta a' s' i e Vs E2 xs)
  note IH = \<open>\<And>vs e2 XS. \<lbrakk>bisim vs a e2 XS; fv a \<subseteq> set vs; lcl s \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_vars a \<le> length XS;
            ?synth a s \<rbrakk> \<Longrightarrow> ?concl a e2 s XS a' s' ta vs\<close>
  from \<open>extTA2J0 P,P,t \<turnstile> \<langle>a,s\<rangle> -ta\<rightarrow> \<langle>a',s'\<rangle>\<close> have "\<not> is_val a" by auto
  with \<open>bisim Vs (a\<lfloor>i\<rceil>:=e) E2 xs\<close> obtain E
    where E2: "E2 = E\<lfloor>compE1 Vs i\<rceil>:=compE1 Vs e" and "bisim Vs a E xs"
    and sync: "\<not> contains_insync i" "\<not> contains_insync e" by auto
  with IH[of Vs E xs] \<open>fv (a\<lfloor>i\<rceil>:=e) \<subseteq> set Vs\<close> \<open>lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]\<close> \<open>\<not> is_val a\<close> \<open>extTA2J0 P,P,t \<turnstile> \<langle>a,s\<rangle> -ta\<rightarrow> \<langle>a',s'\<rangle>\<close>
    \<open>length Vs + max_vars (a\<lfloor>i\<rceil>:=e) \<le> length xs\<close> \<open>?synth (a\<lfloor>i\<rceil>:=e) s\<close>
  obtain ta' e2' xs'
    where IH': "sim_move01 (compP1 P) t ta a E (hp s) xs ta' e2' (hp s') xs'"
    "bisim Vs a' e2' xs'" "lcl s' \<subseteq>\<^sub>m [Vs [\<mapsto>] xs']"
    by auto
  show ?case
  proof(cases "is_val a'")
    case True
    from \<open>fv (a\<lfloor>i\<rceil>:=e) \<subseteq> set Vs\<close> sync
    have "bisim Vs i (compE1 Vs i) xs'" "bisim Vs e (compE1 Vs e) xs'" by auto
    with IH' E2 True sync  \<open>\<not> is_val a\<close> \<open>extTA2J0 P,P,t \<turnstile> \<langle>a,s\<rangle> -ta\<rightarrow> \<langle>a',s'\<rangle>\<close> show ?thesis
      by(cases "is_val i")(fastforce elim!: sim_move01_expr)+
  next
    case False with IH' E2 sync \<open>\<not> is_val a\<close> \<open>extTA2J0 P,P,t \<turnstile> \<langle>a,s\<rangle> -ta\<rightarrow> \<langle>a',s'\<rangle>\<close>
    show ?thesis by(fastforce elim!: sim_move01_expr)
  qed
next
  case (AAssRed2 i s ta i' s' a e Vs E2 xs)
  note IH = \<open>\<And>vs e2 XS. \<lbrakk>bisim vs i e2 XS; fv i \<subseteq> set vs; lcl s \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_vars i \<le> length XS;
            ?synth i s \<rbrakk> \<Longrightarrow> ?concl i e2 s XS i' s' ta vs\<close>
  from \<open>extTA2J0 P,P,t \<turnstile> \<langle>i,s\<rangle> -ta\<rightarrow> \<langle>i',s'\<rangle>\<close> have "\<not> is_val i" by auto
  with \<open>bisim Vs (Val a\<lfloor>i\<rceil> := e) E2 xs\<close> obtain E
    where "E2 = Val a\<lfloor>E\<rceil>:=compE1 Vs e" and "bisim Vs i E xs" and "\<not> contains_insync e" by auto
  with IH[of Vs E xs] \<open>fv (Val a\<lfloor>i\<rceil>:=e) \<subseteq> set Vs\<close> \<open>lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]\<close> \<open>\<not> is_val i\<close> \<open>extTA2J0 P,P,t \<turnstile> \<langle>i,s\<rangle> -ta\<rightarrow> \<langle>i',s'\<rangle>\<close>
    \<open>length Vs + max_vars (Val a\<lfloor>i\<rceil>:=e) \<le> length xs\<close> \<open>?synth (Val a\<lfloor>i\<rceil>:=e) s\<close>
  show ?case by(cases "is_val i'")(fastforce elim!: sim_move01_expr)+
next
  case (AAssRed3 e s ta e' s' a i Vs E2 xs)
  note IH = \<open>\<And>vs e2 XS. \<lbrakk>bisim vs e e2 XS; fv e \<subseteq> set vs; lcl s \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_vars e \<le> length XS;
            ?synth e s \<rbrakk> \<Longrightarrow> ?concl e e2 s XS e' s' ta vs\<close>
  from \<open>bisim Vs (Val a\<lfloor>Val i\<rceil> := e) E2 xs\<close> obtain E
    where "E2 = Val a\<lfloor>Val i\<rceil>:=E" and "bisim Vs e E xs" by auto
  with IH[of Vs E xs] \<open>fv (Val a\<lfloor>Val i\<rceil>:=e) \<subseteq> set Vs\<close> \<open>lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]\<close> \<open>extTA2J0 P,P,t \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>\<close>
    \<open>length Vs + max_vars (Val a\<lfloor>Val i\<rceil>:=e) \<le> length xs\<close> \<open>?synth (Val a\<lfloor>Val i\<rceil>:=e) s\<close>
  show ?case by(fastforce elim!: sim_move01_expr)
next
  case RedAAssStore thus ?case by(auto intro!: exI)
next
  case (FAssRed1 e s ta e' s' F D e2 Vs E2 xs)
  note IH = \<open>\<And>vs e2 XS. \<lbrakk>bisim vs e e2 XS; fv e \<subseteq> set vs; lcl s \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_vars e \<le> length XS;
            ?synth e s \<rbrakk> \<Longrightarrow> ?concl e e2 s XS e' s' ta vs\<close>
  from \<open>extTA2J0 P,P,t \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>\<close> have "\<not> is_val e" by auto
  with \<open>bisim Vs (e\<bullet>F{D} := e2) E2 xs\<close> obtain E
    where "E2 = E\<bullet>F{D} := compE1 Vs e2" and "bisim Vs e E xs" and "\<not> contains_insync e2" by auto
  with IH[of Vs E xs] \<open>fv (e\<bullet>F{D} := e2) \<subseteq> set Vs\<close> \<open>lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]\<close> \<open>\<not> is_val e\<close> \<open>extTA2J0 P,P,t \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>\<close>
    \<open>length Vs + max_vars (e\<bullet>F{D} := e2) \<le> length xs\<close> \<open>?synth (e\<bullet>F{D} := e2) s\<close>
  show ?case by(cases "is_val e'")(fastforce elim!: sim_move01_expr)+
next
  case (FAssRed2 e s ta e' s' v F D Vs E2 xs)
  note IH = \<open>\<And>vs e2 XS. \<lbrakk>bisim vs e e2 XS; fv e \<subseteq> set vs; lcl s \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_vars e \<le> length XS;
            ?synth e s \<rbrakk> \<Longrightarrow> ?concl e e2 s XS e' s' ta vs\<close>
  from \<open>bisim Vs (Val v\<bullet>F{D} := e) E2 xs\<close> obtain E
    where "E2 = Val v\<bullet>F{D} := E" and "bisim Vs e E xs" by auto
  with IH[of Vs E xs] \<open>fv (Val v\<bullet>F{D} := e) \<subseteq> set Vs\<close> \<open>lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]\<close> \<open>extTA2J0 P,P,t \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>\<close>
    \<open>length Vs + max_vars (Val v\<bullet>F{D} := e) \<le> length xs\<close> \<open>?synth (Val v\<bullet>F{D} := e) s\<close>
  show ?case by(fastforce elim!: sim_move01_expr)
next
  case (CASRed1 e s ta e' s' D F e2 e3 Vs E2 xs)
  note IH = \<open>\<And>vs e2 XS. \<lbrakk>bisim vs e e2 XS; fv e \<subseteq> set vs; lcl s \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_vars e \<le> length XS;
            ?synth e s \<rbrakk> \<Longrightarrow> ?concl e e2 s XS e' s' ta vs\<close>
  from \<open>extTA2J0 P,P,t \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>\<close> have "\<not> is_val e" by auto
  with \<open>bisim Vs _ E2 xs\<close> obtain E
    where E2: "E2 = E\<bullet>compareAndSwap(D\<bullet>F, compE1 Vs e2, compE1 Vs e3)" and "bisim Vs e E xs"
    and sync: "\<not> contains_insync e2" "\<not> contains_insync e3" by(auto)
  with IH[of Vs E xs] \<open>fv _ \<subseteq> set Vs\<close> \<open>lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]\<close> \<open>\<not> is_val e\<close> \<open>extTA2J0 P,P,t \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>\<close>
    \<open>length Vs + max_vars _ \<le> length xs\<close> \<open>?synth _ s\<close>
  obtain ta' e2' xs'
    where IH': "sim_move01 (compP1 P) t ta e E (hp s) xs ta' e2' (hp s') xs'"
    "bisim Vs e' e2' xs'" "lcl s' \<subseteq>\<^sub>m [Vs [\<mapsto>] xs']"
    by auto
  show ?case
  proof(cases "is_val e'")
    case True
    from \<open>fv _ \<subseteq> set Vs\<close> sync
    have "bisim Vs e2 (compE1 Vs e2) xs'" "bisim Vs e3 (compE1 Vs e3) xs'" by auto
    with IH' E2 True sync  \<open>\<not> is_val e\<close> \<open>extTA2J0 P,P,t \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>\<close> show ?thesis
      by(cases "is_val e2")(fastforce elim!: sim_move01_expr)+
  next
    case False with IH' E2 sync \<open>\<not> is_val e\<close> \<open>extTA2J0 P,P,t \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>\<close>
    show ?thesis by(fastforce elim!: sim_move01_expr)
  qed
next
  case (CASRed2 e s ta e' s' v D F e3 Vs E2 xs)
  note IH = \<open>\<And>vs e2 XS. \<lbrakk>bisim vs e e2 XS; fv e \<subseteq> set vs; lcl s \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_vars e \<le> length XS;
            ?synth e s \<rbrakk> \<Longrightarrow> ?concl e e2 s XS e' s' ta vs\<close>
  from \<open>extTA2J0 P,P,t \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>\<close> have "\<not> is_val e" by auto
  with \<open>bisim Vs _ E2 xs\<close> obtain E
    where "E2 = Val v\<bullet>compareAndSwap(D\<bullet>F, E, compE1 Vs e3)" and "bisim Vs e E xs" and "\<not> contains_insync e3" by(auto)
  with IH[of Vs E xs] \<open>fv _ \<subseteq> set Vs\<close> \<open>lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]\<close> \<open>\<not> is_val e\<close> \<open>extTA2J0 P,P,t \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>\<close>
    \<open>length Vs + max_vars _ \<le> length xs\<close> \<open>?synth _ s\<close>
  show ?case by(cases "is_val e'")(fastforce elim!: sim_move01_expr)+
next
  case (CASRed3 e s ta e' s' v D F v' Vs E2 xs)
  note IH = \<open>\<And>vs e2 XS. \<lbrakk>bisim vs e e2 XS; fv e \<subseteq> set vs; lcl s \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_vars e \<le> length XS;
            ?synth e s \<rbrakk> \<Longrightarrow> ?concl e e2 s XS e' s' ta vs\<close>
  from \<open>bisim Vs _ E2 xs\<close> obtain E
    where "E2 = Val v\<bullet>compareAndSwap(D\<bullet>F, Val v', E)" and "bisim Vs e E xs" by auto
  with IH[of Vs E xs] \<open>fv _ \<subseteq> set Vs\<close> \<open>lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]\<close> \<open>extTA2J0 P,P,t \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>\<close>
    \<open>length Vs + max_vars _ \<le> length xs\<close> \<open>?synth _ s\<close>
  show ?case by(fastforce elim!: sim_move01_expr)
next
  case (CallObj e s ta e' s' M es Vs E2 xs)
  note IH = \<open>\<And>vs e2 XS. \<lbrakk>bisim vs e e2 XS; fv e \<subseteq> set vs; lcl s \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_vars e \<le> length XS;
            ?synth e s \<rbrakk> \<Longrightarrow> ?concl e e2 s XS e' s' ta vs\<close>
  from \<open>extTA2J0 P,P,t \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>\<close> have "\<not> is_val e" by auto
  with \<open>bisim Vs (e\<bullet>M(es)) E2 xs\<close> obtain E
    where "E2 = E\<bullet>M(compEs1 Vs es)" and "bisim Vs e E xs" and "\<not> contains_insyncs es"
    by(auto simp add: compEs1_conv_map)
  with IH[of Vs E xs] \<open>fv (e\<bullet>M(es)) \<subseteq> set Vs\<close> \<open>lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]\<close>
    \<open>length Vs + max_vars (e\<bullet>M(es)) \<le> length xs\<close> \<open>?synth (e\<bullet>M(es)) s\<close>
  show ?case by(cases "is_val e'")(fastforce elim!: sim_move01_expr split: if_split_asm)+
next
  case (CallParams es s ta es' s' v M Vs E2 xs)
  note IH = \<open>\<And>vs es2 XS. \<lbrakk>bisims vs es es2 XS; fvs es \<subseteq> set vs; lcl s \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_varss es \<le> length XS;
            ?synths es s \<rbrakk> \<Longrightarrow> ?concls es es2 s XS es' s' ta vs\<close>
  from \<open>bisim Vs (Val v\<bullet>M(es)) E2 xs\<close> obtain Es 
    where "E2 = Val v\<bullet>M(Es)" and "bisims Vs es Es xs" by auto
  moreover from \<open>extTA2J0 P,P,t \<turnstile> \<langle>es,s\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle>\<close> have "\<not> is_vals es" by auto
  with \<open>?synth (Val v\<bullet>M(es)) s\<close> have "?synths es s" by(auto)
  moreover note IH[of Vs Es xs] \<open>fv (Val v\<bullet>M(es)) \<subseteq> set Vs\<close> \<open>lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]\<close> 
    \<open>length Vs + max_vars (Val v\<bullet>M(es)) \<le> length xs\<close>
  ultimately show ?case by(fastforce elim!: sim_move01_CallParams)
next
  case (RedCall s a U M Ts T pns body D vs Vs E2 xs)
  from \<open>typeof_addr (hp s) a = \<lfloor>U\<rfloor>\<close>
  have "call (addr a\<bullet>M(map Val vs)) = \<lfloor>(a, M, vs)\<rfloor>" by auto
  with \<open>?synth (addr a\<bullet>M(map Val vs)) s\<close> have "synthesized_call P (hp s) (a, M, vs)" by auto
  with \<open>typeof_addr (hp s) a = \<lfloor>U\<rfloor>\<close> \<open>P \<turnstile> class_type_of U sees M: Ts\<rightarrow>T = \<lfloor>(pns, body)\<rfloor> in D\<close>
  have False by(auto simp add: synthesized_call_conv dest: sees_method_fun)
  thus ?case ..
next
  case (RedCallExternal s a T M Ts Tr D vs ta va h' ta' e' s' Vs E2 xs)
  from \<open>bisim Vs (addr a\<bullet>M(map Val vs)) E2 xs\<close> have "E2 = addr a\<bullet>M(map Val vs)" by auto
  moreover note \<open>P \<turnstile> class_type_of T sees M: Ts\<rightarrow>Tr = Native in D\<close> \<open>typeof_addr (hp s) a = \<lfloor>T\<rfloor>\<close> \<open>ta' = extTA2J0 P ta\<close>
    \<open>e' = extRet2J (addr a\<bullet>M(map Val vs)) va\<close> \<open>s' = (h', lcl s)\<close> \<open>P,t \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>\<close>
    \<open>lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]\<close>
  moreover from wf \<open>P,t \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>\<close>
  have "ta_bisim01 (extTA2J0 P ta) (extTA2J1 (compP1 P) ta)" by(rule red_external_ta_bisim01)
  moreover from \<open>P,t \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>\<close> \<open>typeof_addr (hp s) a = \<lfloor>T\<rfloor>\<close>
    \<open>P \<turnstile> class_type_of T sees M: Ts\<rightarrow>Tr = Native in D\<close>
  have "\<tau>external_defs D M \<Longrightarrow> h' = hp s \<and> ta = \<epsilon>"
    by(fastforce dest: \<tau>external'_red_external_heap_unchanged \<tau>external'_red_external_TA_empty simp add: \<tau>external'_def \<tau>external_def)
  ultimately show ?case 
    by(cases va)(fastforce intro!: exI[where x=ta] intro: Red1CallExternal simp add: map_eq_append_conv sim_move01_def dest: sees_method_fun simp del: split_paired_Ex)+
next
  case (BlockRed e h x V vo ta e' h' x' T Vs E2 xs)
  note IH = \<open>\<And>vs e2 XS. \<lbrakk>bisim vs e e2 XS; fv e \<subseteq> set vs; lcl (h, x(V := vo)) \<subseteq>\<^sub>m [vs [\<mapsto>] XS];
                         length vs + max_vars e \<le> length XS; ?synth e (h, (x(V := vo)))\<rbrakk>
            \<Longrightarrow> ?concl e e2 (h, x(V := vo)) XS e' (h', x') ta vs\<close>
  note red = \<open>extTA2J0 P,P,t \<turnstile> \<langle>e,(h, x(V := vo))\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>\<close>
  note len = \<open>length Vs + max_vars {V:T=vo; e} \<le> length xs\<close>
  from \<open>fv {V:T=vo; e} \<subseteq> set Vs\<close> have fv: "fv e \<subseteq> set (Vs@[V])" by auto
  from \<open>bisim Vs {V:T=vo; e} E2 xs\<close> show ?case
  proof(cases rule: bisim_cases(7)[consumes 1, case_names BlockNone BlockSome BlockSomeNone])
    case (BlockNone E')
    with red IH[of "Vs@[V]" E' xs] fv \<open>lcl (h, x) \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]\<close>
      \<open>length Vs + max_vars {V:T=vo; e} \<le> length xs\<close> \<open>?synth {V:T=vo; e} (h, x)\<close>
    obtain TA' e2' xs' where red': "sim_move01 (compP1 P) t ta e E' h xs TA' e2' h' xs'"
      and bisim': "bisim (Vs @ [V]) e' e2' xs'" "x' \<subseteq>\<^sub>m [Vs @ [V] [\<mapsto>] xs']" by auto 
    from red' \<open>length Vs + max_vars {V:T=vo; e} \<le> length xs\<close>
    have "length (Vs@[V]) + max_vars e \<le> length xs'"
      by(fastforce simp add: sim_move01_def dest: red1_preserves_len \<tau>red1t_preserves_len \<tau>red1r_preserves_len split: if_split_asm)
    with \<open>x' \<subseteq>\<^sub>m [Vs @ [V] [\<mapsto>] xs']\<close> have "x' \<subseteq>\<^sub>m [Vs [\<mapsto>] xs', V \<mapsto> xs' ! length Vs]" by(simp)
    moreover 
    { assume "V \<in> set Vs"
      hence "hidden (Vs @ [V]) (index Vs V)" by(rule hidden_index)
      with \<open>bisim (Vs @ [V]) e E' xs\<close> have "unmod E' (index Vs V)"
        by -(rule hidden_bisim_unmod)
      moreover from \<open>length Vs + max_vars {V:T=vo; e} \<le> length xs\<close> \<open>V \<in> set Vs\<close>
      have "index Vs V < length xs" by(auto intro: index_less_aux)
      ultimately have "xs ! index Vs V = xs' ! index Vs V"
        using sim_move01_preserves_unmod[OF red'] by(simp) }
    moreover from red' have "length xs = length xs'" by(rule sim_move01_preserves_len[symmetric])
    ultimately have rel: "x'(V := x V) \<subseteq>\<^sub>m [Vs [\<mapsto>] xs']"
      using \<open>lcl (h, x) \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]\<close> \<open>length Vs + max_vars {V:T=vo; e} \<le> length xs\<close>
      by(auto intro: Block_lem)
    show ?thesis
    proof(cases "x' V")
      case None
      with red' bisim' BlockNone len
      show ?thesis by(fastforce simp del: split_paired_Ex fun_upd_apply intro: rel)
    next
      case (Some v)
      moreover
      with \<open>x' \<subseteq>\<^sub>m [Vs @ [V] [\<mapsto>] xs']\<close> have "[Vs @ [V] [\<mapsto>] xs'] V = \<lfloor>v\<rfloor>"
        by(auto simp add: map_le_def dest: bspec)
      moreover
      from \<open>length Vs + max_vars {V:T=vo; e} \<le> length xs\<close> have "length Vs < length xs" by auto
      ultimately have "xs' ! length Vs = v" using \<open>length xs = length xs'\<close> by(simp)
      with red' bisim' BlockNone Some len
      show ?thesis by(fastforce simp del: fun_upd_apply intro: rel)
    qed
  next
    case (BlockSome E' v)
    with red IH[of "Vs@[V]" E' "xs[length Vs := v]"] fv \<open>lcl (h, x) \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]\<close>
      \<open>length Vs + max_vars {V:T=vo; e} \<le> length xs\<close> \<open>?synth {V:T=vo; e} (h, x)\<close>
    obtain TA' e2' xs' where red': "sim_move01 (compP1 P) t ta e E' h (xs[length Vs := v]) TA' e2' h' xs'"
      and bisim': "bisim (Vs @ [V]) e' e2' xs'" "x' \<subseteq>\<^sub>m [Vs @ [V] [\<mapsto>] xs']" by auto
    from red' \<open>length Vs + max_vars {V:T=vo; e} \<le> length xs\<close>
    have "length (Vs@[V]) + max_vars e \<le> length xs'" by(auto dest: sim_move01_preserves_len)
    with \<open>x' \<subseteq>\<^sub>m [Vs @ [V] [\<mapsto>] xs']\<close> have "x' \<subseteq>\<^sub>m [Vs [\<mapsto>] xs', V \<mapsto> xs' ! length Vs]" by(simp)
    moreover 
    { assume "V \<in> set Vs"
      hence "hidden (Vs @ [V]) (index Vs V)" by(rule hidden_index)
      with \<open>bisim (Vs @ [V]) e E' (xs[length Vs := v])\<close> have "unmod E' (index Vs V)"
        by -(rule hidden_bisim_unmod)
      moreover from \<open>length Vs + max_vars {V:T=vo; e} \<le> length xs\<close> \<open>V \<in> set Vs\<close>
      have "index Vs V < length xs" by(auto intro: index_less_aux)
      moreover from \<open>length Vs + max_vars {V:T=vo; e} \<le> length xs\<close> \<open>V \<in> set Vs\<close>
      have "(xs[length Vs := v]) ! index Vs V = xs ! index Vs V" by(simp)
      ultimately have "xs ! index Vs V = xs' ! index Vs V"
        using sim_move01_preserves_unmod[OF red', of "index Vs V"] by(simp) }
    moreover from red' have "length xs = length xs'" by(auto dest: sim_move01_preserves_len)
    ultimately have rel: "x'(V := x V) \<subseteq>\<^sub>m [Vs [\<mapsto>] xs']"
      using \<open>lcl (h, x) \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]\<close> \<open>length Vs + max_vars {V:T=vo; e} \<le> length xs\<close>
      by(auto intro: Block_lem)
    from BlockSome red obtain v' where Some: "x' V = \<lfloor>v'\<rfloor>" by(auto dest!: red_lcl_incr)
    with \<open>x' \<subseteq>\<^sub>m [Vs @ [V] [\<mapsto>] xs']\<close> have "[Vs @ [V] [\<mapsto>] xs'] V = \<lfloor>v'\<rfloor>"
      by(auto simp add: map_le_def dest: bspec)
    moreover
    from \<open>length Vs + max_vars {V:T=vo; e} \<le> length xs\<close> have "length Vs < length xs" by auto
    ultimately have "xs' ! length Vs = v'" using \<open>length xs = length xs'\<close> by(simp)
    with red' bisim' BlockSome Some \<open>length Vs < length xs\<close>
    show ?thesis by(fastforce simp del: fun_upd_apply intro: rel)
  next 
    case (BlockSomeNone E')
    with red IH[of "Vs@[V]" E' xs] fv \<open>lcl (h, x) \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]\<close>
      \<open>length Vs + max_vars {V:T=vo; e} \<le> length xs\<close> \<open>?synth {V:T=vo; e} (h, x)\<close>
    obtain TA' e2' xs' where red': "sim_move01 (compP1 P) t ta e E' h xs TA' e2' h' xs'"
      and IH': "bisim (Vs @ [V]) e' e2' xs'" "x' \<subseteq>\<^sub>m [Vs @ [V] [\<mapsto>] xs']" by auto
    from red' \<open>length Vs + max_vars {V:T=vo; e} \<le> length xs\<close>
    have "length (Vs@[V]) + max_vars e \<le> length xs'" by(auto dest: sim_move01_preserves_len)
    with \<open>x' \<subseteq>\<^sub>m [Vs @ [V] [\<mapsto>] xs']\<close> have "x' \<subseteq>\<^sub>m [Vs [\<mapsto>] xs', V \<mapsto> xs' ! length Vs]" by(simp)
    moreover 
    { assume "V \<in> set Vs"
      hence "hidden (Vs @ [V]) (index Vs V)" by(rule hidden_index)
      with \<open>bisim (Vs @ [V]) e E' xs\<close> have "unmod E' (index Vs V)"
        by -(rule hidden_bisim_unmod)
      moreover from \<open>length Vs + max_vars {V:T=vo; e} \<le> length xs\<close> \<open>V \<in> set Vs\<close>
      have "index Vs V < length xs" by(auto intro: index_less_aux)
      moreover from \<open>length Vs + max_vars {V:T=vo; e} \<le> length xs\<close> \<open>V \<in> set Vs\<close>
      have "(xs[length Vs := v]) ! index Vs V = xs ! index Vs V" by(simp)
      ultimately have "xs ! index Vs V = xs' ! index Vs V"
        using sim_move01_preserves_unmod[OF red', of "index Vs V"] by(simp) }
    moreover from red' have "length xs = length xs'" by(auto dest: sim_move01_preserves_len)
    ultimately have rel: "x'(V := x V) \<subseteq>\<^sub>m [Vs [\<mapsto>] xs']"
      using \<open>lcl (h, x) \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]\<close> \<open>length Vs + max_vars {V:T=vo; e} \<le> length xs\<close>
      by(auto intro: Block_lem)
    from BlockSomeNone red obtain v' where Some: "x' V = \<lfloor>v'\<rfloor>" by(auto dest!: red_lcl_incr)
    with \<open>x' \<subseteq>\<^sub>m [Vs @ [V] [\<mapsto>] xs']\<close> have "[Vs @ [V] [\<mapsto>] xs'] V = \<lfloor>v'\<rfloor>"
      by(auto simp add: map_le_def dest: bspec)
    moreover
    from \<open>length Vs + max_vars {V:T=vo; e} \<le> length xs\<close> have "length Vs < length xs" by auto
    ultimately have "xs' ! length Vs = v'" using \<open>length xs = length xs'\<close> by(simp)
    with red' IH' BlockSomeNone Some \<open>length Vs < length xs\<close>
    show ?thesis by(fastforce simp del: fun_upd_apply intro: rel)
  qed
next
  case (RedBlock V T vo u s Vs E2 xs)
  from \<open>bisim Vs {V:T=vo; Val u} E2 xs\<close> obtain vo'
    where [simp]: "E2 = {length Vs:T=vo'; Val u}" by auto
  from RedBlock show ?case
  proof(cases vo)
    case (Some v)
    with \<open>bisim Vs {V:T=vo; Val u} E2 xs\<close>
    have vo': "case vo' of None \<Rightarrow> xs ! length Vs = v | Some v' \<Rightarrow> v = v'" by auto
    have "sim_move01 (compP1 P) t \<epsilon> {V:T=vo; Val u} E2 (hp s) xs \<epsilon> (Val u) (hp s) (xs[length Vs := v])"
    proof(cases vo')
      case None with vo'
      have "xs[length Vs := v] = xs" by auto
      thus ?thesis using Some None by auto
    next
      case Some
      from \<open>length Vs + max_vars {V:T=vo; Val u} \<le> length xs\<close> have "length Vs < length xs" by simp
      with vo' Some show ?thesis using \<open>vo = Some v\<close> by auto
    qed
    thus ?thesis using RedBlock by fastforce
  qed fastforce
next
  case SynchronizedNull thus ?case by fastforce
next
  case (LockSynchronized a e s Vs E2 xs)
  from \<open>bisim Vs (sync(addr a) e) E2 xs\<close>
  have E2: "E2 = sync\<^bsub>length Vs\<^esub> (addr a) (compE1 (Vs@[fresh_var Vs]) e)" 
    and sync: "\<not> contains_insync e" by auto
  moreover have "fresh_var Vs \<notin> set Vs" by(rule fresh_var_fresh)
  with \<open>fv (sync(addr a) e) \<subseteq> set Vs\<close> have "fresh_var Vs \<notin> fv e" by auto
  from E2 \<open>fv (sync(addr a) e) \<subseteq> set Vs\<close> sync
  have "bisim (Vs@[fresh_var Vs]) e (compE1 (Vs@[fresh_var Vs]) e) (xs[length Vs := Addr a])"
    by(auto intro!: compE1_bisim)
  hence "bisim Vs (insync(a) e) (insync\<^bsub>length Vs\<^esub> (a) (compE1 (Vs@[fresh_var Vs]) e)) (xs[length Vs := Addr a])"
    using \<open>fresh_var Vs \<notin> fv e\<close> \<open>length Vs + max_vars (sync(addr a) e) \<le> length xs\<close> by auto
  moreover from \<open>length Vs + max_vars (sync(addr a) e) \<le> length xs\<close>
  have "False,compP1 P,t \<turnstile>1 \<langle>sync\<^bsub>length Vs\<^esub> (addr a) (compE1 (Vs@[fresh_var Vs]) e), (hp s, xs)\<rangle>
        -\<lbrace>Lock\<rightarrow>a, SyncLock a\<rbrace>\<rightarrow>
        \<langle>insync\<^bsub>length Vs\<^esub> (a) (compE1 (Vs@[fresh_var Vs]) e), (hp s, xs[length Vs := Addr a])\<rangle>"
    by -(rule Lock1Synchronized, auto)
  hence "sim_move01 (compP1 P) t \<lbrace>Lock\<rightarrow>a, SyncLock a\<rbrace> (sync(addr a) e) E2 (hp s) xs \<lbrace>Lock\<rightarrow>a, SyncLock a\<rbrace> (insync\<^bsub>length Vs\<^esub> (a) (compE1 (Vs@[fresh_var Vs]) e)) (hp s) (xs[length Vs := Addr a])"
    using E2 by(fastforce simp add: sim_move01_def ta_bisim_def)
  moreover have "zip Vs (xs[length Vs := Addr a]) = (zip Vs xs)[length Vs := (arbitrary, Addr a)]"
    by(rule sym)(simp add: update_zip)
  hence "zip Vs (xs[length Vs := Addr a]) = zip Vs xs" by simp
  with \<open>lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]\<close> have "lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs[length Vs := Addr a]]"
    by(auto simp add: map_le_def map_upds_def)
  ultimately show ?case using \<open>lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]\<close> by fastforce
next
  case (SynchronizedRed2 e s ta e' s' a Vs E2 xs)
  note IH = \<open>\<And>vs e2 XS. \<lbrakk>bisim vs e e2 XS; fv e \<subseteq> set vs; lcl s \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_vars e \<le> length XS;
            ?synth e s \<rbrakk> \<Longrightarrow> ?concl e e2 s XS e' s' ta vs\<close>
  from \<open>bisim Vs (insync(a) e) E2 xs\<close> obtain E
    where E2: "E2 = insync\<^bsub>length Vs\<^esub> (a) E" and bisim: "bisim (Vs@[fresh_var Vs]) e E xs"
    and xsa: "xs ! length Vs = Addr a" by auto
  from \<open>fv (insync(a) e) \<subseteq> set Vs\<close> fresh_var_fresh[of Vs] have fv: "fresh_var Vs \<notin> fv e" by auto
  from \<open>length Vs + max_vars (insync(a) e) \<le> length xs\<close> have "length Vs < length xs" by simp
  { assume "lcl s (fresh_var Vs) \<noteq> None"
    then obtain v where "lcl s (fresh_var Vs) = \<lfloor>v\<rfloor>" by auto
    with \<open>lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]\<close> have "[Vs [\<mapsto>] xs] (fresh_var Vs) = \<lfloor>v\<rfloor>" 
      by(auto simp add: map_le_def dest: bspec)
    hence "fresh_var Vs \<in> set Vs" 
      by(auto simp add: map_upds_def set_zip dest!: map_of_SomeD )
    moreover have "fresh_var Vs \<notin> set Vs" by(rule fresh_var_fresh)
    ultimately have False by contradiction }
  hence "lcl s (fresh_var Vs) = None" by(cases "lcl s (fresh_var Vs)", auto)
  hence "(lcl s)(fresh_var Vs := None) = lcl s" by(auto intro: ext)
  moreover from \<open>lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]\<close>
  have "(lcl s)(fresh_var Vs := None) \<subseteq>\<^sub>m [Vs [\<mapsto>] xs, fresh_var Vs \<mapsto> xs ! length Vs]" by(simp)
  ultimately have "lcl s \<subseteq>\<^sub>m [Vs @ [fresh_var Vs] [\<mapsto>] xs]"
    using \<open>length Vs < length xs\<close> by(auto)
  with IH[of "Vs@[fresh_var Vs]" E xs] \<open>fv (insync(a) e) \<subseteq> set Vs\<close> bisim
    \<open>length Vs + max_vars (insync(a) e) \<le> length xs\<close> \<open>?synth (insync(a) e) s\<close> 
  obtain TA' e2' xs' where IH': "sim_move01 (compP1 P) t ta e E (hp s) xs TA' e2' (hp s') xs'"
    "bisim (Vs @ [fresh_var Vs]) e' e2' xs'" "lcl s' \<subseteq>\<^sub>m [Vs @ [fresh_var Vs] [\<mapsto>] xs']" by auto
  from \<open>extTA2J0 P,P,t \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>\<close> have "dom (lcl s') \<subseteq> dom (lcl s) \<union> fv e" by(auto dest: red_dom_lcl)
  with fv \<open>lcl s (fresh_var Vs) = None\<close> have "(fresh_var Vs) \<notin> dom (lcl s')" by auto
  hence "lcl s' (fresh_var Vs) = None" by auto
  moreover from IH' have "length xs = length xs'" by(auto dest: sim_move01_preserves_len)
  moreover note \<open>lcl s' \<subseteq>\<^sub>m [Vs @ [fresh_var Vs] [\<mapsto>] xs']\<close> \<open>length Vs < length xs\<close>
  ultimately have "lcl s' \<subseteq>\<^sub>m [Vs [\<mapsto>] xs']" by(auto simp add: map_le_def dest: bspec)
  moreover from bisim fv have "unmod E (length Vs)" by(auto intro: bisim_fv_unmod)
  with IH' \<open>length Vs < length xs\<close> have "xs ! length Vs = xs' ! length Vs"
    by(auto dest!: sim_move01_preserves_unmod)
  with xsa have "xs' ! length Vs = Addr a" by simp
  ultimately show ?case using IH' E2 by(fastforce)
next
  case (UnlockSynchronized a v s Vs E2 xs)
  from \<open>bisim Vs (insync(a) Val v) E2 xs\<close> have E2: "E2 = insync\<^bsub>length Vs\<^esub> (a) Val v" 
    and xsa: "xs ! length Vs = Addr a" by auto
  moreover from \<open>length Vs + max_vars (insync(a) Val v) \<le> length xs\<close> xsa
  have "False,compP1 P,t \<turnstile>1 \<langle>insync\<^bsub>length Vs\<^esub> (a) (Val v), (hp s, xs)\<rangle> -\<lbrace>Unlock\<rightarrow>a, SyncUnlock a\<rbrace>\<rightarrow> \<langle>Val v, (hp s, xs)\<rangle>"
    by-(rule Unlock1Synchronized, auto)
  hence "sim_move01 (compP1 P) t \<lbrace>Unlock\<rightarrow>a, SyncUnlock a\<rbrace> (insync(a) Val v) (insync\<^bsub>length Vs\<^esub> (a) Val v) (hp s) xs \<lbrace>Unlock\<rightarrow>a, SyncUnlock a\<rbrace> (Val v) (hp s) xs"
    by(fastforce simp add: sim_move01_def ta_bisim_def)
  ultimately show ?case using \<open>lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]\<close> by fastforce
next
  case (RedWhile b c s Vs E2 xs)
  from \<open>bisim Vs (while (b) c) E2 xs\<close> have "E2 = while (compE1 Vs b) (compE1 Vs c)"
    and sync: "\<not> contains_insync b" "\<not> contains_insync c" by auto
  moreover have "False,compP1 P,t \<turnstile>1 \<langle>while(compE1 Vs b) (compE1 Vs c), (hp s, xs)\<rangle> 
                 -\<epsilon>\<rightarrow> \<langle>if (compE1 Vs b) (compE1 Vs c;;while(compE1 Vs b) (compE1 Vs c)) else unit, (hp s, xs)\<rangle>"
    by(rule Red1While)
  hence "sim_move01 (compP1 P) t \<epsilon> (while (b) c) (while (compE1 Vs b) (compE1 Vs c)) (hp s) xs \<epsilon> (if (compE1 Vs b) (compE1 Vs c;;while(compE1 Vs b) (compE1 Vs c)) else unit) (hp s) xs"
    by(auto simp add: sim_move01_def)
  moreover from \<open>fv (while (b) c) \<subseteq> set Vs\<close> sync
  have "bisim Vs (if (b) (c;; while (b) c) else unit)
                 (if (compE1 Vs b) (compE1 Vs (c;; while(b) c)) else (compE1 Vs unit)) xs"
    by -(rule bisimCond, auto)
  ultimately show ?case using \<open>lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]\<close>
    by(simp)((rule exI)+, erule conjI, auto)
next
  case (RedTryCatch s a D C V e2 Vs E2 xs)
  thus ?case by(auto intro!: exI)(auto intro!: compE1_bisim)
next
  case RedTryFail thus ?case by(auto intro!: exI)
next
  case (ListRed1 e s ta e' s' es Vs ES2 xs)
  note IH = \<open>\<And>vs e2 XS. \<lbrakk>bisim vs e e2 XS; fv e \<subseteq> set vs; lcl s \<subseteq>\<^sub>m [vs [\<mapsto>] XS]; length vs + max_vars e \<le> length XS;
                         ?synth e s\<rbrakk> \<Longrightarrow> ?concl e e2 s XS e' s' ta vs\<close>
  from \<open>extTA2J0 P,P,t \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>\<close> have "\<not> is_val e" by auto
  with \<open>bisims Vs (e # es) ES2 xs\<close> obtain E' 
    where "bisim Vs e E' xs" and ES2: "ES2 = E' # compEs1 Vs es" 
    and sync: "\<not> contains_insyncs es" by(auto simp add: compEs1_conv_map)
  with IH[of Vs E' xs] \<open>fvs (e # es) \<subseteq> set Vs\<close> \<open>lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]\<close> \<open>extTA2J0 P,P,t \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>\<close>
    \<open>length Vs + max_varss (e # es) \<le> length xs\<close> \<open>?synths (e # es) s\<close> \<open>\<not> is_val e\<close>
  show ?case by(cases "is_val e'")(fastforce elim!: sim_moves01_expr split: if_split_asm)+
next
  case (ListRed2 es s ta es' s' v Vs ES2 xs)
  thus ?case by(fastforce elim!: bisims_cases elim!: sim_moves01_expr)
next
  case CallThrowParams thus ?case
    by(fastforce elim!:bisim_cases simp add: bisims_map_Val_Throw)
next
  case (BlockThrow V T vo a s Vs e2 xs) thus ?case
    by(cases vo)(fastforce elim!: bisim_cases)+
next    
  case (SynchronizedThrow2 a ad s Vs E2 xs)
  from \<open>bisim Vs (insync(a) Throw ad) E2 xs\<close> have "xs ! length Vs = Addr a" by auto
  with \<open>length Vs + max_vars (insync(a) Throw ad) \<le> length xs\<close>
  have "False,compP1 P,t \<turnstile>1 \<langle>insync\<^bsub>length Vs\<^esub> (a) Throw ad, (hp s, xs)\<rangle> -\<lbrace>Unlock\<rightarrow>a, SyncUnlock a\<rbrace>\<rightarrow> \<langle>Throw ad, (hp s, xs)\<rangle>"
    by-(rule Synchronized1Throw2, auto)
  hence "sim_move01 (compP1 P) t \<lbrace>Unlock\<rightarrow>a, SyncUnlock a\<rbrace> (insync(a) Throw ad) (insync\<^bsub>length Vs\<^esub> (a) Throw ad) (hp s) xs \<lbrace>Unlock\<rightarrow>a, SyncUnlock a\<rbrace> (Throw ad) (hp s) xs"
    by(fastforce simp add: sim_move01_def ta_bisim_def fun_eq_iff expand_finfun_eq finfun_upd_apply ta_upd_simps split: if_split_asm)
  moreover note \<open>lcl s \<subseteq>\<^sub>m [Vs [\<mapsto>] xs]\<close> \<open>bisim Vs (insync(a) Throw ad) E2 xs\<close>
  ultimately show ?case by(fastforce)
next
  case InstanceOfRed thus ?case by(fastforce)
next
  case RedInstanceOf thus ?case by(auto intro!: exI)
next
  case InstanceOfThrow thus ?case by fastforce
qed(fastforce simp del: fun_upd_apply split: if_split_asm)+

end

declare max_dest [iff del]

declare split_paired_Ex [simp del]

primrec countInitBlock :: "('a, 'b, 'addr) exp \<Rightarrow> nat"
  and countInitBlocks :: "('a, 'b, 'addr) exp list \<Rightarrow> nat"
where 
  "countInitBlock (new C) = 0"
| "countInitBlock (newA T\<lfloor>e\<rceil>) = countInitBlock e"
| "countInitBlock (Cast T e) = countInitBlock e"
| "countInitBlock (e instanceof T) = countInitBlock e"
| "countInitBlock (Val v) = 0"
| "countInitBlock (Var V) = 0"
| "countInitBlock (V := e) = countInitBlock e"
| "countInitBlock (e \<guillemotleft>bop\<guillemotright> e') = countInitBlock e + countInitBlock e'"
| "countInitBlock (a\<lfloor>i\<rceil>) = countInitBlock a + countInitBlock i"
| "countInitBlock (AAss a i e) = countInitBlock a + countInitBlock i + countInitBlock e"
| "countInitBlock (a\<bullet>length) = countInitBlock a"
| "countInitBlock (e\<bullet>F{D}) = countInitBlock e"
| "countInitBlock (FAss e F D e') = countInitBlock e + countInitBlock e'"
| "countInitBlock (e\<bullet>compareAndSwap(D\<bullet>F, e', e'')) = 
   countInitBlock e + countInitBlock e' + countInitBlock e''"
| "countInitBlock (e\<bullet>M(es)) = countInitBlock e + countInitBlocks es"
| "countInitBlock ({V:T=vo; e}) = (case vo of None \<Rightarrow> 0 | Some v \<Rightarrow> 1) + countInitBlock e"
| "countInitBlock (sync\<^bsub>V'\<^esub> (e) e') = countInitBlock e + countInitBlock e'"
| "countInitBlock (insync\<^bsub>V'\<^esub> (ad) e) = countInitBlock e"
| "countInitBlock (e;;e') = countInitBlock e + countInitBlock e'"
| "countInitBlock (if (e) e1 else e2) = countInitBlock e + countInitBlock e1 + countInitBlock e2"
| "countInitBlock (while(b) e) = countInitBlock b + countInitBlock e"
| "countInitBlock (throw e) = countInitBlock e"
| "countInitBlock (try e catch(C V) e') = countInitBlock e + countInitBlock e'"

| "countInitBlocks [] = 0"
| "countInitBlocks (e # es) = countInitBlock e + countInitBlocks es"

context J0_J1_heap_base begin

lemmas \<tau>red0r_expr =
  NewArray_\<tau>red0r_xt Cast_\<tau>red0r_xt InstanceOf_\<tau>red0r_xt BinOp_\<tau>red0r_xt1 BinOp_\<tau>red0r_xt2 LAss_\<tau>red0r
  AAcc_\<tau>red0r_xt1 AAcc_\<tau>red0r_xt2 AAss_\<tau>red0r_xt1 AAss_\<tau>red0r_xt2 AAss_\<tau>red0r_xt3
  ALength_\<tau>red0r_xt FAcc_\<tau>red0r_xt FAss_\<tau>red0r_xt1 FAss_\<tau>red0r_xt2
  CAS_\<tau>red0r_xt1 CAS_\<tau>red0r_xt2 CAS_\<tau>red0r_xt3 Call_\<tau>red0r_obj
  Call_\<tau>red0r_param Block_\<tau>red0r_xt Sync_\<tau>red0r_xt InSync_\<tau>red0r_xt
  Seq_\<tau>red0r_xt Cond_\<tau>red0r_xt Throw_\<tau>red0r_xt Try_\<tau>red0r_xt

lemmas \<tau>red0t_expr =
  NewArray_\<tau>red0t_xt Cast_\<tau>red0t_xt InstanceOf_\<tau>red0t_xt BinOp_\<tau>red0t_xt1 BinOp_\<tau>red0t_xt2 LAss_\<tau>red0t
  AAcc_\<tau>red0t_xt1 AAcc_\<tau>red0t_xt2 AAss_\<tau>red0t_xt1 AAss_\<tau>red0t_xt2 AAss_\<tau>red0t_xt3
  ALength_\<tau>red0t_xt FAcc_\<tau>red0t_xt FAss_\<tau>red0t_xt1 FAss_\<tau>red0t_xt2
  CAS_\<tau>red0t_xt1 CAS_\<tau>red0t_xt2 CAS_\<tau>red0t_xt3 Call_\<tau>red0t_obj
  Call_\<tau>red0t_param Block_\<tau>red0t_xt Sync_\<tau>red0t_xt InSync_\<tau>red0t_xt
  Seq_\<tau>red0t_xt Cond_\<tau>red0t_xt Throw_\<tau>red0t_xt Try_\<tau>red0t_xt

declare \<tau>red0r_expr [elim!]
declare \<tau>red0t_expr [elim!]

definition sim_move10 :: 
  "'addr J_prog \<Rightarrow> 'thread_id \<Rightarrow> ('addr, 'thread_id, 'heap) external_thread_action \<Rightarrow> 'addr expr1 \<Rightarrow> 'addr expr1 \<Rightarrow> 'addr expr
  \<Rightarrow> 'heap \<Rightarrow> 'addr locals \<Rightarrow> ('addr, 'thread_id, 'heap) J0_thread_action \<Rightarrow> 'addr expr \<Rightarrow> 'heap \<Rightarrow> 'addr locals \<Rightarrow> bool"
where
  "sim_move10 P t ta1 e1 e1' e h xs ta e' h' xs' \<longleftrightarrow> \<not> final e1 \<and>
  (if \<tau>move1 P h e1 then (\<tau>red0t (extTA2J0 P) P t h (e, xs) (e', xs') \<or> countInitBlock e1' < countInitBlock e1 \<and> e' = e \<and> xs' = xs) \<and> h' = h \<and> ta1 = \<epsilon> \<and> ta = \<epsilon>
   else ta_bisim01 ta (extTA2J1 (compP1 P) ta1) \<and>
     (if call e = None \<or> call1 e1 = None 
      then (\<exists>e'' xs''. \<tau>red0r (extTA2J0 P) P t h (e, xs) (e'', xs'') \<and> extTA2J0 P,P,t \<turnstile> \<langle>e'', (h, xs'')\<rangle> -ta\<rightarrow> \<langle>e', (h', xs')\<rangle> \<and> no_call P h e'' \<and> \<not> \<tau>move0 P h e'')
      else extTA2J0 P,P,t \<turnstile> \<langle>e, (h, xs)\<rangle> -ta\<rightarrow> \<langle>e', (h', xs')\<rangle> \<and> no_call P h e \<and> \<not> \<tau>move0 P h e))"

definition sim_moves10 :: 
  "'addr J_prog \<Rightarrow> 'thread_id \<Rightarrow> ('addr, 'thread_id, 'heap) external_thread_action \<Rightarrow> 'addr expr1 list \<Rightarrow> 'addr expr1 list
  \<Rightarrow> 'addr expr list \<Rightarrow> 'heap \<Rightarrow> 'addr locals \<Rightarrow> ('addr, 'thread_id, 'heap) J0_thread_action \<Rightarrow> 'addr expr list \<Rightarrow> 'heap 
  \<Rightarrow> 'addr locals \<Rightarrow> bool"
where
  "sim_moves10 P t ta1 es1 es1' es h xs ta es' h' xs' \<longleftrightarrow> \<not> finals es1 \<and>
  (if \<tau>moves1 P h es1 then (\<tau>reds0t (extTA2J0 P) P t h (es, xs) (es', xs') \<or> countInitBlocks es1' < countInitBlocks es1 \<and> es' = es \<and> xs' = xs) \<and> h' = h \<and> ta1 = \<epsilon> \<and> ta = \<epsilon>
   else ta_bisim01 ta (extTA2J1 (compP1 P) ta1) \<and>
     (if calls es = None \<or> calls1 es1 = None
      then (\<exists>es'' xs''. \<tau>reds0r (extTA2J0 P) P t h (es, xs) (es'', xs'') \<and> extTA2J0 P,P,t \<turnstile> \<langle>es'', (h, xs'')\<rangle> [-ta\<rightarrow>] \<langle>es', (h', xs')\<rangle> \<and> no_calls P h es'' \<and> \<not> \<tau>moves0 P h es'')
      else extTA2J0 P,P,t \<turnstile> \<langle>es, (h, xs)\<rangle> [-ta\<rightarrow>] \<langle>es', (h', xs')\<rangle> \<and> no_calls P h es \<and> \<not> \<tau>moves0 P h es))"

lemma sim_move10_expr:
  assumes "sim_move10 P t ta1 e1 e1' e h xs ta e' h' xs'"
  shows
  "sim_move10 P t ta1 (newA T\<lfloor>e1\<rceil>) (newA T\<lfloor>e1'\<rceil>) (newA T\<lfloor>e\<rceil>) h xs ta (newA T\<lfloor>e'\<rceil>) h' xs'"
  "sim_move10 P t ta1 (Cast T e1) (Cast T e1') (Cast T e) h xs ta (Cast T e') h' xs'"
  "sim_move10 P t ta1 (e1 instanceof T) (e1' instanceof T) (e instanceof T) h xs ta (e' instanceof T) h' xs'"
  "sim_move10 P t ta1 (e1 \<guillemotleft>bop\<guillemotright> e2) (e1' \<guillemotleft>bop\<guillemotright> e2) (e \<guillemotleft>bop\<guillemotright> e2') h xs ta (e' \<guillemotleft>bop\<guillemotright> e2') h' xs'"
  "sim_move10 P t ta1 (Val v \<guillemotleft>bop\<guillemotright> e1) (Val v \<guillemotleft>bop\<guillemotright> e1') (Val v \<guillemotleft>bop\<guillemotright> e) h xs ta (Val v \<guillemotleft>bop\<guillemotright> e') h' xs'"
  "sim_move10 P t ta1 (V := e1) (V := e1') (V' := e) h xs ta (V' := e') h' xs'"
  "sim_move10 P t ta1 (e1\<lfloor>e2\<rceil>) (e1'\<lfloor>e2\<rceil>) (e\<lfloor>e2'\<rceil>) h xs ta (e'\<lfloor>e2'\<rceil>) h' xs'"
  "sim_move10 P t ta1 (Val v\<lfloor>e1\<rceil>) (Val v\<lfloor>e1'\<rceil>) (Val v\<lfloor>e\<rceil>) h xs ta (Val v\<lfloor>e'\<rceil>) h' xs'"
  "sim_move10 P t ta1 (e1\<lfloor>e2\<rceil> := e3) (e1'\<lfloor>e2\<rceil> := e3) (e\<lfloor>e2'\<rceil> := e3') h xs ta (e'\<lfloor>e2'\<rceil> := e3') h' xs'"
  "sim_move10 P t ta1 (Val v\<lfloor>e1\<rceil> := e3) (Val v\<lfloor>e1'\<rceil> := e3) (Val v\<lfloor>e\<rceil> := e3') h xs ta (Val v\<lfloor>e'\<rceil> := e3') h' xs'"
  "sim_move10 P t ta1 (AAss (Val v) (Val v') e1) (AAss (Val v) (Val v') e1') (AAss (Val v) (Val v') e) h xs ta (AAss (Val v) (Val v') e') h' xs'"
  "sim_move10 P t ta1 (e1\<bullet>length) (e1'\<bullet>length) (e\<bullet>length) h xs ta (e'\<bullet>length) h' xs'"
  "sim_move10 P t ta1 (e1\<bullet>F{D}) (e1'\<bullet>F{D}) (e\<bullet>F'{D'}) h xs ta (e'\<bullet>F'{D'}) h' xs'"
  "sim_move10 P t ta1 (FAss e1 F D e2) (FAss e1' F D e2) (FAss e F' D' e2') h xs ta (FAss e' F' D' e2') h' xs'"
  "sim_move10 P t ta1 (FAss (Val v) F D e1) (FAss (Val v) F D e1') (FAss (Val v) F' D' e) h xs ta (FAss (Val v) F' D' e') h' xs'"
  "sim_move10 P t ta1 (CompareAndSwap e1 F D e2 e3) (CompareAndSwap e1' F D e2 e3) (CompareAndSwap e F' D' e2' e3') h xs ta (CompareAndSwap e' F' D' e2' e3') h' xs'"
  "sim_move10 P t ta1 (CompareAndSwap (Val v) F D e1 e3) (CompareAndSwap (Val v) F D e1' e3) (CompareAndSwap (Val v) F' D' e e3') h xs ta (CompareAndSwap (Val v) F' D' e' e3') h' xs'"
  "sim_move10 P t ta1 (CompareAndSwap (Val v) F D (Val v') e1) (CompareAndSwap (Val v) F D (Val v') e1') (CompareAndSwap (Val v) F' D' (Val v') e) h xs ta (CompareAndSwap (Val v) F' D' (Val v') e') h' xs'"
  "sim_move10 P t ta1 (e1\<bullet>M(es)) (e1'\<bullet>M(es)) (e\<bullet>M(es')) h xs ta (e'\<bullet>M(es')) h' xs'"
  "sim_move10 P t ta1 (sync\<^bsub>V\<^esub>(e1) e2) (sync\<^bsub>V\<^esub>(e1') e2) (sync(e) e2') h xs ta (sync(e') e2') h' xs'"
  "sim_move10 P t ta1 (insync\<^bsub>V\<^esub>(a) e1) (insync\<^bsub>V\<^esub>(a) e1') (insync(a') e) h xs ta (insync(a') e') h' xs'"
  "sim_move10 P t ta1 (e1;;e2) (e1';;e2) (e;;e2') h xs ta (e';;e2') h' xs'"
  "sim_move10 P t ta1 (if (e1) e2 else e3) (if (e1') e2 else e3) (if (e) e2' else e3') h xs ta (if (e') e2' else e3') h' xs'"
  "sim_move10 P t ta1 (throw e1) (throw e1') (throw e) h xs ta (throw e') h' xs'"
  "sim_move10 P t ta1 (try e1 catch(C V) e2) (try e1' catch(C V) e2) (try e catch(C' V') e2') h xs ta (try e' catch(C' V') e2') h' xs'"
using assms
apply(simp_all add: sim_move10_def final_iff split del: if_split split: if_split_asm)
apply(fastforce simp: \<tau>red0t_Val \<tau>red0r_Val intro: red_reds.intros split!: if_splits)+
done

lemma sim_moves10_expr:
  "sim_move10 P t ta1 e1 e1' e h xs ta e' h' xs' \<Longrightarrow> sim_moves10 P t ta1 (e1 # es2) (e1' # es2) (e # es2') h xs ta (e' # es2') h' xs'"
  "sim_moves10 P t ta1 es1 es1' es h xs ta es' h' xs' \<Longrightarrow> sim_moves10 P t ta1 (Val v # es1) (Val v # es1') (Val v # es) h xs ta (Val v # es') h' xs'"
unfolding sim_moves10_def sim_move10_def final_iff finals_iff
apply(simp_all add: Cons_eq_append_conv split del: if_split split: if_split_asm)
apply(safe intro!: if_split)
apply(fastforce simp add: is_vals_conv \<tau>reds0t_map_Val \<tau>reds0r_map_Val \<tau>red0t_Val \<tau>red0r_Val intro!: \<tau>red0r_inj_\<tau>reds0r \<tau>reds0r_cons_\<tau>reds0r \<tau>red0t_inj_\<tau>reds0t \<tau>reds0t_cons_\<tau>reds0t ListRed1 ListRed2 split: if_split_asm)+
done

lemma sim_move10_CallParams:
  "sim_moves10 P t ta1 es1 es1' es h xs ta es' h' xs'
  \<Longrightarrow> sim_move10 P t ta1 (Val v\<bullet>M(es1)) (Val v\<bullet>M(es1')) (Val v\<bullet>M(es)) h xs ta (Val v\<bullet>M(es')) h' xs'"
unfolding sim_move10_def sim_moves10_def
apply(simp split: if_split_asm split del: if_split add: is_vals_conv)
  apply(fastforce simp add: \<tau>red0t_Val \<tau>red0r_Val \<tau>reds0t_map_Val \<tau>reds0r_map_Val intro: Call_\<tau>red0r_param Call_\<tau>red0t_param CallParams split: if_split_asm split del: if_split intro!: if_split)
 apply(rule conjI)
  apply fastforce
 apply(rule if_intro)
  apply fastforce
 apply(clarsimp split del: if_split)
 apply(rule if_intro)
  apply(clarsimp split: if_split_asm simp add: is_vals_conv)
   apply(rule exI conjI)+
    apply(erule Call_\<tau>red0r_param)
   apply(fastforce intro: CallParams)
  apply(rule exI conjI)+
   apply(erule Call_\<tau>red0r_param)
  apply(fastforce intro!: CallParams)
 apply(clarsimp split del: if_split split: if_split_asm simp add: is_vals_conv \<tau>reds0r_map_Val)
 apply fastforce
apply(rule conjI)
 apply fastforce
apply(rule if_intro)
 apply fastforce
apply(rule conjI)
 apply fastforce
apply(rule if_intro)
 apply(clarsimp split: if_split_asm)
apply(clarsimp split: if_split_asm split del: if_split simp add: is_vals_conv)
apply(fastforce intro: CallParams)
done

lemma sim_move10_Block:
  "sim_move10 P t ta1 e1 e1' e h (xs(V' := vo)) ta e' h' xs'
  \<Longrightarrow> sim_move10 P t ta1 ({V:T=None; e1}) ({V:T=None; e1'}) ({V':T=vo; e}) h xs ta ({V':T=xs' V'; e'}) h' (xs'(V' := xs V'))"
proof -
  assume "sim_move10 P t ta1 e1 e1' e h (xs(V' := vo)) ta e' h' xs'"
  moreover {
    fix e'' xs''
    assume "extTA2J0 P,P,t \<turnstile> \<langle>e'',(h, xs'')\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>"
    hence "extTA2J0 P,P,t \<turnstile> \<langle>e'',(h, xs''(V' := xs V', V' := xs'' V'))\<rangle> -ta\<rightarrow> \<langle>e',(h', xs')\<rangle>" by simp
    from BlockRed[OF this, of T]
    have "extTA2J0 P,P,t \<turnstile> \<langle>{V':T=xs'' V'; e''},(h, xs''(V' := xs V'))\<rangle> -ta\<rightarrow> \<langle>{V':T=xs' V'; e'},(h', xs'(V' := xs V'))\<rangle>"
      by simp }
  ultimately show ?thesis
    by(fastforce simp add: sim_move10_def final_iff split: if_split_asm)
qed

lemma sim_move10_reds:
  "\<lbrakk> (h', a) \<in> allocate h (Class_type C); ta1 = \<lbrace>NewHeapElem a (Class_type C)\<rbrace>; ta = \<lbrace>NewHeapElem a (Class_type C)\<rbrace> \<rbrakk>
  \<Longrightarrow> sim_move10 P t ta1 (new C) e1' (new C) h xs ta (addr a) h' xs"
  "allocate h (Class_type C) = {} \<Longrightarrow> sim_move10 P t \<epsilon> (new C) e1' (new C) h xs \<epsilon> (THROW OutOfMemory) h xs"
  "\<lbrakk> (h', a) \<in> allocate h (Array_type T (nat (sint i))); 0 <=s i;
     ta1 = \<lbrace>NewHeapElem a (Array_type T (nat (sint i)))\<rbrace>; ta = \<lbrace>NewHeapElem a (Array_type T (nat (sint i)))\<rbrace> \<rbrakk>
  \<Longrightarrow> sim_move10 P t ta1 (newA T\<lfloor>Val (Intg i)\<rceil>) e1' (newA T\<lfloor>Val (Intg i)\<rceil>) h xs ta (addr a) h' xs"
  "i <s 0 \<Longrightarrow> sim_move10 P t \<epsilon> (newA T\<lfloor>Val (Intg i)\<rceil>) e1' (newA T\<lfloor>Val (Intg i)\<rceil>) h xs \<epsilon> (THROW NegativeArraySize) h xs"
  "\<lbrakk> allocate h (Array_type T (nat (sint i))) = {}; 0 <=s i \<rbrakk>
  \<Longrightarrow> sim_move10 P t \<epsilon> (newA T\<lfloor>Val (Intg i)\<rceil>) e1' (newA T\<lfloor>Val (Intg i)\<rceil>) h xs \<epsilon> (THROW OutOfMemory) h xs"
  "\<lbrakk> typeof\<^bsub>h\<^esub> v = \<lfloor>U\<rfloor>; P \<turnstile> U \<le> T \<rbrakk>
  \<Longrightarrow> sim_move10 P t \<epsilon> (Cast T (Val v)) e1' (Cast T (Val v)) h xs \<epsilon> (Val v) h xs"
  "\<lbrakk> typeof\<^bsub>h\<^esub> v = \<lfloor>U\<rfloor>; \<not> P \<turnstile> U \<le> T \<rbrakk>
  \<Longrightarrow> sim_move10 P t \<epsilon> (Cast T (Val v)) e1' (Cast T (Val v)) h xs \<epsilon> (THROW ClassCast) h xs"
  "\<lbrakk> typeof\<^bsub>h\<^esub> v = \<lfloor>U\<rfloor>; b \<longleftrightarrow> v \<noteq> Null \<and> P \<turnstile> U \<le> T \<rbrakk>
  \<Longrightarrow> sim_move10 P t \<epsilon> ((Val v) instanceof T) e1' ((Val v) instanceof T) h xs \<epsilon> (Val (Bool b)) h xs"
  "binop bop v1 v2 = Some (Inl v) \<Longrightarrow> sim_move10 P t \<epsilon> ((Val v1) \<guillemotleft>bop\<guillemotright> (Val v2)) e1' (Val v1 \<guillemotleft>bop\<guillemotright> Val v2) h xs \<epsilon> (Val v) h xs"
  "binop bop v1 v2 = Some (Inr a) \<Longrightarrow> sim_move10 P t \<epsilon> ((Val v1) \<guillemotleft>bop\<guillemotright> (Val v2)) e1' (Val v1 \<guillemotleft>bop\<guillemotright> Val v2) h xs \<epsilon> (Throw a) h xs"
  "xs V = \<lfloor>v\<rfloor> \<Longrightarrow> sim_move10 P t \<epsilon> (Var V') e1' (Var V) h xs \<epsilon> (Val v) h xs"
  "sim_move10 P t \<epsilon> (V' := Val v) e1' (V := Val v) h xs \<epsilon> unit h (xs(V \<mapsto> v))"
  "sim_move10 P t \<epsilon> (null\<lfloor>Val v\<rceil>) e1' (null\<lfloor>Val v\<rceil>) h xs \<epsilon> (THROW NullPointer) h xs"
  "\<lbrakk> typeof_addr h a = \<lfloor>Array_type T n\<rfloor>; i <s 0 \<or> sint i \<ge> int n \<rbrakk>
  \<Longrightarrow> sim_move10 P t \<epsilon> (addr a\<lfloor>Val (Intg i)\<rceil>) e1' ((addr a)\<lfloor>Val (Intg i)\<rceil>) h xs \<epsilon> (THROW ArrayIndexOutOfBounds) h xs"
  "\<lbrakk> typeof_addr h a = \<lfloor>Array_type T n\<rfloor>; 0 <=s i; sint i < int n;
     heap_read h a (ACell (nat (sint i))) v;
     ta1 = \<lbrace>ReadMem a (ACell (nat (sint i))) v\<rbrace>; ta = \<lbrace>ReadMem a (ACell (nat (sint i))) v\<rbrace> \<rbrakk>
  \<Longrightarrow> sim_move10 P t ta1 (addr a\<lfloor>Val (Intg i)\<rceil>) e1' ((addr a)\<lfloor>Val (Intg i)\<rceil>) h xs ta (Val v) h xs"
  "sim_move10 P t \<epsilon> (null\<lfloor>Val v\<rceil> := Val v') e1' (null\<lfloor>Val v\<rceil> := Val v') h xs \<epsilon> (THROW NullPointer) h xs"
  "\<lbrakk> typeof_addr h a = \<lfloor>Array_type T n\<rfloor>; i <s 0 \<or> sint i \<ge> int n \<rbrakk>
  \<Longrightarrow> sim_move10 P t \<epsilon> (AAss (addr a) (Val (Intg i)) (Val v)) e1' (AAss (addr a) (Val (Intg i)) (Val v)) h xs \<epsilon> (THROW ArrayIndexOutOfBounds) h xs"
 "\<lbrakk> typeof_addr h a = \<lfloor>Array_type T n\<rfloor>; 0 <=s i; sint i < int n; typeof\<^bsub>h\<^esub> v = \<lfloor>U\<rfloor>; \<not> (P \<turnstile> U \<le> T) \<rbrakk>
  \<Longrightarrow> sim_move10 P t \<epsilon> (AAss (addr a) (Val (Intg i)) (Val v)) e1' (AAss (addr a) (Val (Intg i)) (Val v)) h xs \<epsilon> (THROW ArrayStore) h xs"
  "\<lbrakk> typeof_addr h a = \<lfloor>Array_type T n\<rfloor>; 0 <=s i; sint i < int n; typeof\<^bsub>h\<^esub> v = Some U; P \<turnstile> U \<le> T;
     heap_write h a (ACell (nat (sint i))) v h';
     ta1 = \<lbrace>WriteMem a (ACell (nat (sint i))) v\<rbrace>; ta = \<lbrace>WriteMem a (ACell (nat (sint i))) v\<rbrace> \<rbrakk>
  \<Longrightarrow> sim_move10 P t ta1 (AAss (addr a) (Val (Intg i)) (Val v)) e1' (AAss (addr a) (Val (Intg i)) (Val v)) h xs ta unit h' xs"
  "typeof_addr h a = \<lfloor>Array_type T n\<rfloor> \<Longrightarrow> sim_move10 P t \<epsilon> (addr a\<bullet>length) e1' (addr a\<bullet>length) h xs \<epsilon> (Val (Intg (word_of_int (int n)))) h xs"
  "sim_move10 P t \<epsilon> (null\<bullet>length) e1' (null\<bullet>length) h xs \<epsilon> (THROW NullPointer) h xs"
  "\<lbrakk> heap_read h a (CField D F) v; ta1 = \<lbrace>ReadMem a (CField D F) v\<rbrace>; ta = \<lbrace>ReadMem a (CField D F) v\<rbrace> \<rbrakk>
  \<Longrightarrow> sim_move10 P t ta1 (addr a\<bullet>F{D}) e1' (addr a\<bullet>F{D}) h xs ta (Val v) h xs"
  "sim_move10 P t \<epsilon> (null\<bullet>F{D}) e1' (null\<bullet>F{D}) h xs \<epsilon> (THROW NullPointer) h xs"
  "\<lbrakk> heap_write h a (CField D F) v h'; ta1 = \<lbrace>WriteMem a (CField D F) v\<rbrace>; ta = \<lbrace>WriteMem a (CField D F) v\<rbrace> \<rbrakk>
  \<Longrightarrow> sim_move10 P t ta1 (addr a\<bullet>F{D} := Val v) e1' (addr a\<bullet>F{D} := Val v) h xs ta unit h' xs"
  "sim_move10 P t \<epsilon> (null\<bullet>compareAndSwap(D\<bullet>F, Val v, Val v')) e1' (null\<bullet>compareAndSwap(D\<bullet>F, Val v, Val v')) h xs \<epsilon> (THROW NullPointer) h xs"
  "\<lbrakk> heap_read h a (CField D F) v''; heap_write h a (CField D F) v' h'; v'' = v;
     ta1 = \<lbrace> ReadMem a (CField D F) v'', WriteMem a (CField D F) v' \<rbrace>; ta = \<lbrace> ReadMem a (CField D F) v'', WriteMem a (CField D F) v' \<rbrace> \<rbrakk>
  \<Longrightarrow> sim_move10 P t ta1 (addr a\<bullet>compareAndSwap(D\<bullet>F, Val v, Val v')) e1' (addr a\<bullet>compareAndSwap(D\<bullet>F, Val v, Val v')) h xs ta true h' xs"
  "\<lbrakk> heap_read h a (CField D F) v''; v'' \<noteq> v;
     ta1 = \<lbrace> ReadMem a (CField D F) v'' \<rbrace>; ta = \<lbrace> ReadMem a (CField D F) v'' \<rbrace> \<rbrakk>
  \<Longrightarrow> sim_move10 P t ta1 (addr a\<bullet>compareAndSwap(D\<bullet>F, Val v, Val v')) e1' (addr a\<bullet>compareAndSwap(D\<bullet>F, Val v, Val v')) h xs ta false h xs"

  "sim_move10 P t \<epsilon> (null\<bullet>F{D} := Val v) e1' (null\<bullet>F{D} := Val v) h xs \<epsilon> (THROW NullPointer) h xs"
  "sim_move10 P t \<epsilon> ({V':T=None; Val u}) e1' ({V:T=vo; Val u}) h xs \<epsilon> (Val u) h xs"
  "sim_move10 P t \<epsilon> ({V':T=\<lfloor>v\<rfloor>; e}) ({V':T=None; e}) ({V:T=vo; e'}) h xs \<epsilon> ({V:T=vo; e'}) h xs"

  "sim_move10 P t \<epsilon> (sync\<^bsub>V'\<^esub>(null) e0) e1' (sync(null) e1) h xs \<epsilon> (THROW NullPointer) h xs"
  "sim_move10 P t \<epsilon> (Val v;;e0) e1' (Val v;; e1) h xs \<epsilon> e1 h xs"
  "sim_move10 P t \<epsilon> (if (true) e0 else e0') e1' (if (true) e1 else e2) h xs \<epsilon> e1 h xs"
  "sim_move10 P t \<epsilon> (if (false) e0 else e0') e1' (if (false) e1 else e2) h xs \<epsilon> e2 h xs"
  "sim_move10 P t \<epsilon> (throw null) e1' (throw null) h xs \<epsilon> (THROW NullPointer) h xs"
  "sim_move10 P t \<epsilon> (try (Val v) catch(C V') e0) e1' (try (Val v) catch(C V) e1) h xs \<epsilon> (Val v) h xs"
  "\<lbrakk> typeof_addr h a = \<lfloor>Class_type D\<rfloor>; P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> sim_move10 P t \<epsilon> (try (Throw a) catch(C V') e0) e1' (try (Throw a) catch(C V) e1) h xs \<epsilon> ({V:Class C=\<lfloor>Addr a\<rfloor>; e1}) h xs"
  "sim_move10 P t \<epsilon> (newA T\<lfloor>Throw a\<rceil>) e1' (newA T\<lfloor>Throw a\<rceil>) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P t \<epsilon> (Cast T (Throw a)) e1' (Cast T (Throw a)) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P t \<epsilon> ((Throw a) instanceof T) e1' ((Throw a) instanceof T) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P t \<epsilon> ((Throw a) \<guillemotleft>bop\<guillemotright> e0) e1' ((Throw a) \<guillemotleft>bop\<guillemotright> e1) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P t \<epsilon> (Val v \<guillemotleft>bop\<guillemotright> (Throw a)) e1' (Val v \<guillemotleft>bop\<guillemotright> (Throw a)) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P t \<epsilon> (V' := Throw a) e1' (V := Throw a) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P t \<epsilon> (Throw a\<lfloor>e0\<rceil>) e1' (Throw a\<lfloor>e1\<rceil>) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P t \<epsilon> (Val v\<lfloor>Throw a\<rceil>) e1' (Val v\<lfloor>Throw a\<rceil>) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P t \<epsilon> (Throw a\<lfloor>e0\<rceil> := e0') e1' (Throw a\<lfloor>e1\<rceil> := e2) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P t \<epsilon> (Val v\<lfloor>Throw a\<rceil> := e0) e1' (Val v\<lfloor>Throw a\<rceil> := e1) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P t \<epsilon> (Val v\<lfloor>Val v'\<rceil> := Throw a) e1' (Val v\<lfloor>Val v'\<rceil> := Throw a) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P t \<epsilon> (Throw a\<bullet>length) e1' (Throw a\<bullet>length) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P t \<epsilon> (Throw a\<bullet>F{D}) e1' (Throw a\<bullet>F{D}) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P t \<epsilon> (Throw a\<bullet>F{D} := e0) e1' (Throw a\<bullet>F{D} := e1) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P t \<epsilon> (Val v\<bullet>F{D} := Throw a) e1' (Val v\<bullet>F{D} := Throw a) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P t \<epsilon> (CompareAndSwap (Throw a) D F e0 e0') e1' (Throw a\<bullet>compareAndSwap(D\<bullet>F, e1'', e1''')) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P t \<epsilon> (CompareAndSwap (Val v) D F (Throw a) e0') e1' (Val v\<bullet>compareAndSwap(D\<bullet>F, Throw a, e1'')) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P t \<epsilon> (CompareAndSwap (Val v) D F (Val v') (Throw a)) e1' (Val v\<bullet>compareAndSwap(D\<bullet>F, Val v', Throw a)) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P t \<epsilon> (Throw a\<bullet>M(es0)) e1' (Throw a\<bullet>M(es1)) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P t \<epsilon> (Val v\<bullet>M(map Val vs @ Throw a # es0)) e1' (Val v\<bullet>M(map Val vs @ Throw a # es1)) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P t \<epsilon> ({V':T=None; Throw a}) e1' ({V:T=vo; Throw a}) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P t \<epsilon> (sync\<^bsub>V'\<^esub>(Throw a) e0) e1' (sync(Throw a) e1) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P t \<epsilon> (Throw a;;e0) e1' (Throw a;;e1) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P t \<epsilon> (if (Throw a) e0 else e0') e1' (if (Throw a) e1 else e2) h xs \<epsilon> (Throw a) h xs"
  "sim_move10 P t \<epsilon> (throw (Throw a)) e1' (throw (Throw a)) h xs \<epsilon> (Throw a) h xs"
apply(fastforce simp add: sim_move10_def no_calls_def no_call_def ta_bisim_def intro: red_reds.intros)+
done

lemma sim_move10_CallNull:
  "sim_move10 P t \<epsilon> (null\<bullet>M(map Val vs)) e1' (null\<bullet>M(map Val vs)) h xs \<epsilon> (THROW NullPointer) h xs"
by(fastforce simp add: sim_move10_def map_eq_append_conv intro: RedCallNull)

lemma sim_move10_SyncLocks:
  "\<lbrakk> ta1 = \<lbrace>Lock\<rightarrow>a, SyncLock a\<rbrace>; ta = \<lbrace>Lock\<rightarrow>a, SyncLock a\<rbrace> \<rbrakk>
   \<Longrightarrow> sim_move10 P t ta1 (sync\<^bsub>V\<^esub>(addr a) e0) e1' (sync(addr a) e1) h xs ta (insync(a) e1) h xs"
  "\<lbrakk> ta1 = \<lbrace>Unlock\<rightarrow>a, SyncUnlock a\<rbrace>; ta = \<lbrace>Unlock\<rightarrow>a, SyncUnlock a\<rbrace> \<rbrakk>
  \<Longrightarrow> sim_move10 P t ta1 (insync\<^bsub>V\<^esub>(a') (Val v)) e1' (insync(a) (Val v)) h xs ta (Val v) h xs"
  "\<lbrakk> ta1 = \<lbrace>Unlock\<rightarrow>a, SyncUnlock a\<rbrace>; ta = \<lbrace>Unlock\<rightarrow>a, SyncUnlock a\<rbrace> \<rbrakk>
  \<Longrightarrow> sim_move10 P t ta1 (insync\<^bsub>V\<^esub>(a') (Throw a'')) e1' (insync(a) (Throw a'')) h xs ta (Throw a'') h xs"
by(fastforce simp add: sim_move10_def ta_bisim_def ta_upd_simps intro: red_reds.intros[simplified])+

lemma sim_move10_TryFail:
  "\<lbrakk> typeof_addr h a = \<lfloor>Class_type D\<rfloor>; \<not> P \<turnstile> D \<preceq>\<^sup>* C \<rbrakk>
  \<Longrightarrow> sim_move10 P t \<epsilon> (try (Throw a) catch(C V') e0) e1' (try (Throw a) catch(C V) e1) h xs \<epsilon> (Throw a) h xs"
by(auto simp add: sim_move10_def intro!: RedTryFail)

lemmas sim_move10_intros =
  sim_move10_expr sim_move10_reds sim_move10_CallNull sim_move10_TryFail sim_move10_Block sim_move10_CallParams

lemma sim_move10_preserves_defass:
  assumes wf: "wf_J_prog P"
  shows "\<lbrakk> sim_move10 P t ta1 e1 e1' e h xs ta e' h' xs'; \<D> e \<lfloor>dom xs\<rfloor> \<rbrakk> \<Longrightarrow> \<D> e' \<lfloor>dom xs'\<rfloor>"
by(auto simp add: sim_move10_def split: if_split_asm dest!: \<tau>red0r_preserves_defass[OF wf] \<tau>red0t_preserves_defass[OF wf] red_preserves_defass[OF wf])

declare sim_move10_intros[intro]

lemma assumes wf: "wf_J_prog P"
  shows red_simulates_red1_aux:
  "\<lbrakk> False,compP1 P,t \<turnstile>1 \<langle>e1, S\<rangle> -TA\<rightarrow> \<langle>e1', S'\<rangle>; bisim vs e2 e1 (lcl S); fv e2 \<subseteq> set vs;
     x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl S]; length vs + max_vars e1 \<le> length (lcl S);
     \<D> e2 \<lfloor>dom x\<rfloor> \<rbrakk>
  \<Longrightarrow> \<exists>ta e2' x'. sim_move10 P t TA e1 e1' e2 (hp S) x ta e2' (hp S') x' \<and> bisim vs e2' e1' (lcl S') \<and> x' \<subseteq>\<^sub>m [vs [\<mapsto>] lcl S']"
  (is "\<lbrakk> _; _; _; _; _; _ \<rbrakk> \<Longrightarrow> ?concl e1 e1' e2 S x TA S' e1' vs")

  and reds_simulates_reds1_aux:
  "\<lbrakk> False,compP1 P,t \<turnstile>1 \<langle>es1, S\<rangle> [-TA\<rightarrow>] \<langle>es1', S'\<rangle>; bisims vs es2 es1 (lcl S); fvs es2 \<subseteq> set vs;
     x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl S]; length vs + max_varss es1 \<le> length (lcl S);
     \<D>s es2 \<lfloor>dom x\<rfloor> \<rbrakk>
  \<Longrightarrow> \<exists>ta es2' x'. sim_moves10 P t TA es1 es1' es2 (hp S) x ta es2' (hp S') x' \<and> bisims vs es2' es1' (lcl S') \<and> x' \<subseteq>\<^sub>m [vs [\<mapsto>] lcl S']"
  (is "\<lbrakk> _; _; _; _; _; _ \<rbrakk> \<Longrightarrow> ?concls es1 es1' es2 S x TA S' es1' vs")
proof(induct arbitrary: vs e2 x and vs es2 x rule: red1_reds1.inducts)
  case (Bin1OpRed1 e s ta e' s' bop e2 Vs E2 X)
  note IH = \<open>\<And>vs e2 x. \<lbrakk> bisim vs e2 e (lcl s); fv e2 \<subseteq> set vs;
             x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_vars e \<le> length (lcl s); \<D> e2 \<lfloor>dom x\<rfloor>\<rbrakk>
             \<Longrightarrow> ?concl e e' e2 s x ta s' e' vs\<close>
  from \<open>False,compP1 P,t \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>\<close> have "\<not> is_val e" by auto
  with \<open>bisim Vs E2 (e \<guillemotleft>bop\<guillemotright> e2) (lcl s)\<close> obtain E E2'
    where E2: "E2 = E \<guillemotleft>bop\<guillemotright> E2'" "e2 = compE1 Vs E2'" and "bisim Vs E e (lcl s)"
    and sync: "\<not> contains_insync E2'"
    by(auto elim!: bisim_cases)
  moreover note IH[of Vs E X] \<open>fv E2 \<subseteq> set Vs\<close> \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]\<close>
    \<open>length Vs + max_vars (e \<guillemotleft>bop\<guillemotright> e2) \<le> length (lcl s)\<close> \<open>\<D> E2 \<lfloor>dom X\<rfloor>\<close>
  ultimately obtain TA' e2' x' where "sim_move10 P t ta e e' E (hp s) X TA' e2' (hp s') x'"
    "bisim Vs e2' e' (lcl s')" "x' \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s']" by(auto)
  with E2 \<open>fv E2 \<subseteq> set Vs\<close> sync show ?case by(cases "is_val e2'")(auto intro: BinOpRed1)
next
  case (Bin1OpRed2 e s ta e' s' v bop Vs E2 X)
  note IH = \<open>\<And>vs e2 x. \<lbrakk> bisim vs e2 e (lcl s); fv e2 \<subseteq> set vs;
             x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_vars e \<le> length (lcl s); \<D> e2 \<lfloor>dom x\<rfloor>\<rbrakk>
              \<Longrightarrow> ?concl e e' e2 s x ta s' e' vs\<close>
  from \<open>bisim Vs E2 (Val v \<guillemotleft>bop\<guillemotright> e) (lcl s)\<close> obtain E 
    where E2: "E2 = Val v \<guillemotleft>bop\<guillemotright> E" and "bisim Vs E e (lcl s)" by(auto)
  moreover note IH[of Vs E X] \<open>fv E2 \<subseteq> set Vs\<close> \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]\<close>
    \<open>length Vs + max_vars (Val v \<guillemotleft>bop\<guillemotright> e) \<le> length (lcl s)\<close> \<open>\<D> E2 \<lfloor>dom X\<rfloor>\<close> E2
  ultimately show ?case by(auto intro: BinOpRed2)
next
  case (Red1Var s V v Vs E2 X)
  from \<open>bisim Vs E2 (Var V) (lcl s)\<close> \<open>fv E2 \<subseteq> set Vs\<close>
  obtain V' where "E2 = Var V'" "V' = Vs ! V" "V = index Vs V'" by(clarify, simp)
  from \<open>E2 = Var V'\<close> \<open>\<D> E2 \<lfloor>dom X\<rfloor>\<close>
  obtain v' where "X V' = \<lfloor>v'\<rfloor>" by(auto simp add: hyperset_defs)
  with \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]\<close> have "[Vs [\<mapsto>] lcl s] V' = \<lfloor>v'\<rfloor>" by(rule map_le_SomeD)
  with \<open>length Vs + max_vars (Var V) \<le> length (lcl s)\<close>
  have "lcl s ! (index Vs V') = v'" by(auto intro: map_upds_Some_eq_nth_index)
  with \<open>V = index Vs V'\<close> \<open>lcl s ! V = v\<close> have "v = v'" by simp
  with \<open>X V' = \<lfloor>v'\<rfloor>\<close> \<open>E2 = Var V'\<close> \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]\<close>
  show ?case by(fastforce intro: RedVar)
next
  case (LAss1Red e s ta e' s' V Vs E2 X)
  note IH = \<open>\<And>vs e2 x. \<lbrakk> bisim vs e2 e (lcl s); fv e2 \<subseteq> set vs;
             x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_vars e \<le> length (lcl s); \<D> e2 \<lfloor>dom x\<rfloor>\<rbrakk>
            \<Longrightarrow> ?concl e e' e2 s x ta s' e' vs\<close>
  from \<open>bisim Vs E2 (V:=e) (lcl s)\<close> obtain E V'
    where E2: "E2 = (V':=E)" "V = index Vs V'" and "bisim Vs E e (lcl s)" by auto
  with IH[of Vs E X] \<open>fv E2 \<subseteq> set Vs\<close> \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]\<close>
    \<open>length Vs + max_vars (V:=e) \<le> length (lcl s)\<close> \<open>\<D> E2 \<lfloor>dom X\<rfloor>\<close>
    E2 show ?case by(auto intro: LAssRed)
next
  case (Red1LAss V l v h Vs E2 X)
  from \<open>bisim Vs E2 (V:=Val v) (lcl (h, l))\<close> obtain V' where "E2 = (V' := Val v)" "V = index Vs V'" by(auto)
  moreover with \<open>fv E2 \<subseteq> set Vs\<close> \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl (h, l)]\<close> \<open>length Vs + max_vars (V:=Val v) \<le> length (lcl (h, l))\<close>
  have "X(V' \<mapsto> v) \<subseteq>\<^sub>m [Vs [\<mapsto>] l[index Vs V' := v]]" by(auto intro: LAss_lem)
  ultimately show ?case by(auto intro: RedLAss simp del: fun_upd_apply)
next
  case (AAcc1Red1 a s ta a' s' i Vs E2 X)
  note IH = \<open>\<And>vs e2 x. \<lbrakk> bisim vs e2 a (lcl s); fv e2 \<subseteq> set vs;
             x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_vars a \<le> length (lcl s); \<D> e2 \<lfloor>dom x\<rfloor>\<rbrakk>
             \<Longrightarrow> ?concl a a' e2 s x ta s' a' vs\<close>
  from \<open>False,compP1 P,t \<turnstile>1 \<langle>a,s\<rangle> -ta\<rightarrow> \<langle>a',s'\<rangle>\<close> have "\<not> is_val a" by auto
  with \<open>bisim Vs E2 (a\<lfloor>i\<rceil>) (lcl s)\<close> obtain E E2'
    where E2: "E2 = E\<lfloor>E2'\<rceil>" "i = compE1 Vs E2'" and "bisim Vs E a (lcl s)"
    and sync: "\<not> contains_insync E2'" by(fastforce)
  moreover note IH[of Vs E X] \<open>fv E2 \<subseteq> set Vs\<close> \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]\<close>
    \<open>length Vs + max_vars (a\<lfloor>i\<rceil>) \<le> length (lcl s)\<close> \<open>\<D> E2 \<lfloor>dom X\<rfloor>\<close>
  ultimately obtain TA' e2' x' where "sim_move10 P t ta a a' E (hp s) X TA' e2' (hp s') x'"
    "bisim Vs e2' a' (lcl s')" "x' \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s']" by(auto)
  with E2 \<open>fv E2 \<subseteq> set Vs\<close> sync show ?case
    by(cases "is_val e2'")(auto intro: AAccRed1)
next
  case (AAcc1Red2 i s ta i' s' a Vs E2 X)
  note IH = \<open>\<And>vs e2 x. \<lbrakk> bisim vs e2 i (lcl s); fv e2 \<subseteq> set vs;
             x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_vars i \<le> length (lcl s); \<D> e2 \<lfloor>dom x\<rfloor>\<rbrakk>
            \<Longrightarrow> ?concl i i' e2 s x ta s' i' vs\<close>
  from \<open>bisim Vs E2 (Val a\<lfloor>i\<rceil>) (lcl s)\<close> obtain E 
    where E2: "E2 = Val a\<lfloor>E\<rceil>" and "bisim Vs E i (lcl s)" by(auto)
  moreover note IH[of Vs E X] \<open>fv E2 \<subseteq> set Vs\<close> \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]\<close> E2
    \<open>length Vs + max_vars (Val a\<lfloor>i\<rceil>) \<le> length (lcl s)\<close> \<open>\<D> E2 \<lfloor>dom X\<rfloor>\<close>
  ultimately show ?case by(auto intro: AAccRed2)
next
  case Red1AAcc thus ?case by(fastforce intro: RedAAcc simp del: fun_upd_apply)
next
  case (AAss1Red1 a s ta a' s' i e Vs E2 X)
  note IH = \<open>\<And>vs e2 x. \<lbrakk> bisim vs e2 a (lcl s); fv e2 \<subseteq> set vs;
             x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_vars a \<le> length (lcl s); \<D> e2 \<lfloor>dom x\<rfloor> \<rbrakk>
             \<Longrightarrow> ?concl a a' e2 s x ta s' a' vs\<close>
  from \<open>False,compP1 P,t \<turnstile>1 \<langle>a,s\<rangle> -ta\<rightarrow> \<langle>a',s'\<rangle>\<close> have "\<not> is_val a" by auto
  with \<open>bisim Vs E2 (a\<lfloor>i\<rceil>:=e) (lcl s)\<close> obtain E E2' E2''
    where E2: "E2 = E\<lfloor>E2'\<rceil>:=E2''" "i = compE1 Vs E2'" "e = compE1 Vs E2''" and "bisim Vs E a (lcl s)"
    and sync: "\<not> contains_insync E2'" "\<not> contains_insync E2''" by(fastforce)
  moreover note IH[of Vs E X] \<open>fv E2 \<subseteq> set Vs\<close> \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]\<close>
    \<open>length Vs + max_vars (a\<lfloor>i\<rceil>:=e) \<le> length (lcl s)\<close> \<open>\<D> E2 \<lfloor>dom X\<rfloor>\<close>
  ultimately obtain TA' e2' x' where IH': "sim_move10 P t ta a a' E (hp s) X TA' e2' (hp s') x'"
    "bisim Vs e2' a' (lcl s')" "x' \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s']" by(auto)
  show ?case
  proof(cases "is_val e2'")
    case True
    from E2 \<open>fv E2 \<subseteq> set Vs\<close> sync have "bisim Vs E2' i (lcl s')" "bisim Vs E2'' e (lcl s')" by auto
    with IH' E2 True sync show ?thesis
      by(cases "is_val E2'")(fastforce intro: AAssRed1)+
  next
    case False with IH' E2 sync show ?thesis by(fastforce intro: AAssRed1)
  qed
next
  case (AAss1Red2 i s ta i' s' a e Vs E2 X)
  note IH = \<open>\<And>vs e2 x. \<lbrakk> bisim vs e2 i (lcl s); fv e2 \<subseteq> set vs;
             x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_vars i \<le> length (lcl s); \<D> e2 \<lfloor>dom x\<rfloor>\<rbrakk>
            \<Longrightarrow> ?concl i i' e2 s x ta s' i' vs\<close>
  from \<open>False,compP1 P,t \<turnstile>1 \<langle>i,s\<rangle> -ta\<rightarrow> \<langle>i',s'\<rangle>\<close> have "\<not> is_val i" by auto
  with \<open>bisim Vs E2 (Val a\<lfloor>i\<rceil>:=e) (lcl s)\<close> obtain E E2'
    where E2: "E2 = Val a\<lfloor>E\<rceil>:=E2'" "e = compE1 Vs E2'" and "bisim Vs E i (lcl s)"
    and sync: "\<not> contains_insync E2'" by(fastforce)
  moreover note IH[of Vs E X] \<open>fv E2 \<subseteq> set Vs\<close> \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]\<close>
    \<open>length Vs + max_vars (Val a\<lfloor>i\<rceil>:=e) \<le> length (lcl s)\<close> \<open>\<D> E2 \<lfloor>dom X\<rfloor>\<close>
  ultimately obtain TA' e2' x' where "sim_move10 P t ta i i' E (hp s) X TA' e2' (hp s') x'"
    "bisim Vs e2' i' (lcl s')" "x' \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s']" by(auto)
  with E2 \<open>fv E2 \<subseteq> set Vs\<close> sync show ?case
    by(cases "is_val e2'")(fastforce intro: AAssRed2)+
next
  case (AAss1Red3 e s ta e' s' a i Vs E2 X)
  note IH = \<open>\<And>vs e2 x. \<lbrakk> bisim vs e2 e (lcl s); fv e2 \<subseteq> set vs;
             x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_vars e \<le> length (lcl s); \<D> e2 \<lfloor>dom x\<rfloor>\<rbrakk>
            \<Longrightarrow> ?concl e e' e2 s x ta s' e' vs\<close>
  from \<open>bisim Vs E2 (Val a\<lfloor>Val i\<rceil>:=e) (lcl s)\<close> obtain E
    where E2: "E2 = Val a\<lfloor>Val i\<rceil>:=E" and "bisim Vs E e (lcl s)" by(fastforce)
  moreover note IH[of Vs E X] \<open>fv E2 \<subseteq> set Vs\<close> \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]\<close> E2
    \<open>length Vs + max_vars (Val a\<lfloor>Val i\<rceil>:=e) \<le> length (lcl s)\<close> \<open>\<D> E2 \<lfloor>dom X\<rfloor>\<close>
  ultimately show ?case by(fastforce intro: AAssRed3)
next
  case Red1AAssStore thus ?case by(auto)((rule exI conjI)+, auto)
next
  case Red1AAss thus ?case 
    by(fastforce simp del: fun_upd_apply)
next 
  case (FAss1Red1 e s ta e' s' F D e2 Vs E2 X)
  note IH = \<open>\<And>vs e2 x. \<lbrakk> bisim vs e2 e (lcl s); fv e2 \<subseteq> set vs;
             x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_vars e \<le> length (lcl s); \<D> e2 \<lfloor>dom x\<rfloor>\<rbrakk>
             \<Longrightarrow> ?concl e e' e2 s x ta s' e' vs\<close>
  from \<open>False,compP1 P,t \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>\<close> have "\<not> is_val e" by auto
  with \<open>bisim Vs E2 (e\<bullet>F{D}:=e2) (lcl s)\<close> obtain E E2'
    where E2: "E2 = E\<bullet>F{D}:=E2'" "e2 = compE1 Vs E2'" and "bisim Vs E e (lcl s)" 
    and sync: "\<not> contains_insync E2'" by(fastforce)
  with IH[of Vs E X] \<open>fv E2 \<subseteq> set Vs\<close> \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]\<close>
    \<open>length Vs + max_vars (e\<bullet>F{D}:=e2) \<le> length (lcl s)\<close> \<open>\<D> E2 \<lfloor>dom X\<rfloor>\<close>
  obtain TA' e2' x' where "sim_move10 P t ta e e' E (hp s) X TA' e2' (hp s') x'"
    "bisim Vs e2' e' (lcl s')" "x' \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s']" by(fastforce)
  with E2 \<open>fv E2 \<subseteq> set Vs\<close> sync show ?case by(cases "is_val e2'")(auto intro: FAssRed1)
next 
  case (FAss1Red2 e s ta e' s' v F D Vs E2 X)
  note IH = \<open>\<And>vs e2 x. \<lbrakk> bisim vs e2 e (lcl s); fv e2 \<subseteq> set vs;
             x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_vars e \<le> length (lcl s); \<D> e2 \<lfloor>dom x\<rfloor>\<rbrakk>
            \<Longrightarrow> ?concl e e' e2 s x ta s' e' vs\<close>
  from \<open>bisim Vs E2 (Val v\<bullet>F{D}:=e) (lcl s)\<close> obtain E
    where E2: "E2 = (Val v\<bullet>F{D}:=E)" and "bisim Vs E e (lcl s)" by(fastforce)
  with IH[of Vs E X] \<open>fv E2 \<subseteq> set Vs\<close> \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]\<close>
    \<open>length Vs + max_vars (Val v\<bullet>F{D}:=e) \<le> length (lcl s)\<close> \<open>\<D> E2 \<lfloor>dom X\<rfloor>\<close>
    E2 show ?case by(fastforce intro: FAssRed2)
next
  case (CAS1Red1 e s ta e' s' D F e2 e3 Vs E2 X)
  note IH = \<open>\<And>vs e2 x. \<lbrakk> bisim vs e2 e (lcl s); fv e2 \<subseteq> set vs;
             x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_vars e \<le> length (lcl s); \<D> e2 \<lfloor>dom x\<rfloor> \<rbrakk>
             \<Longrightarrow> ?concl e e' e2 s x ta s' e' vs\<close>
  from \<open>False,compP1 P,t \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>\<close> have "\<not> is_val e" by auto
  with \<open>bisim Vs E2 _ (lcl s)\<close> obtain E E2' E2''
    where E2: "E2 = E\<bullet>compareAndSwap(D\<bullet>F, E2', E2'')" "e2 = compE1 Vs E2'" "e3 = compE1 Vs E2''" and "bisim Vs E e (lcl s)"
    and sync: "\<not> contains_insync E2'" "\<not> contains_insync E2''" by(fastforce)
  moreover note IH[of Vs E X] \<open>fv E2 \<subseteq> set Vs\<close> \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]\<close>
    \<open>length Vs + max_vars _ \<le> length (lcl s)\<close> \<open>\<D> E2 \<lfloor>dom X\<rfloor>\<close>
  ultimately obtain TA' e2' x' where IH': "sim_move10 P t ta e e' E (hp s) X TA' e2' (hp s') x'"
    "bisim Vs e2' e' (lcl s')" "x' \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s']" by(auto)
  show ?case
  proof(cases "is_val e2'")
    case True
    from E2 \<open>fv E2 \<subseteq> set Vs\<close> sync have "bisim Vs E2' e2 (lcl s')" "bisim Vs E2'' e3 (lcl s')" by auto
    with IH' E2 True sync show ?thesis by(cases "is_val E2'")(fastforce)+
  next
    case False with IH' E2 sync show ?thesis by(fastforce)
  qed
next
  case (CAS1Red2 e s ta e' s' v D F e3 Vs E2 X)
  note IH = \<open>\<And>vs e2 x. \<lbrakk> bisim vs e2 e (lcl s); fv e2 \<subseteq> set vs;
             x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_vars e \<le> length (lcl s); \<D> e2 \<lfloor>dom x\<rfloor>\<rbrakk>
            \<Longrightarrow> ?concl e e' e2 s x ta s' e' vs\<close>
  from \<open>False,compP1 P,t \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>\<close> have "\<not> is_val e" by auto
  with \<open>bisim Vs E2 _ (lcl s)\<close> obtain E E2'
    where E2: "E2 = (Val v\<bullet>compareAndSwap(D\<bullet>F, E, E2'))" "e3 = compE1 Vs E2'" and "bisim Vs E e (lcl s)"
    and sync: "\<not> contains_insync E2'" by(auto)
  moreover note IH[of Vs E X] \<open>fv E2 \<subseteq> set Vs\<close> \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]\<close>
    \<open>length Vs + max_vars _ \<le> length (lcl s)\<close> \<open>\<D> E2 \<lfloor>dom X\<rfloor>\<close>
  ultimately obtain TA' e2' x' where "sim_move10 P t ta e e' E (hp s) X TA' e2' (hp s') x'"
    "bisim Vs e2' e' (lcl s')" "x' \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s']" by(auto)
  with E2 \<open>fv E2 \<subseteq> set Vs\<close> sync show ?case
    by(cases "is_val e2'")(fastforce)+
next
  case (CAS1Red3 e s ta e' s' v D F v' Vs E2 X)
  note IH = \<open>\<And>vs e2 x. \<lbrakk> bisim vs e2 e (lcl s); fv e2 \<subseteq> set vs;
             x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_vars e \<le> length (lcl s); \<D> e2 \<lfloor>dom x\<rfloor>\<rbrakk>
            \<Longrightarrow> ?concl e e' e2 s x ta s' e' vs\<close>
  from \<open>bisim Vs E2 _ (lcl s)\<close> obtain E
    where E2: "E2 = (Val v\<bullet>compareAndSwap(D\<bullet>F, Val v', E))" and "bisim Vs E e (lcl s)" by(fastforce)
  moreover note IH[of Vs E X] \<open>fv E2 \<subseteq> set Vs\<close> \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]\<close> E2
    \<open>length Vs + max_vars _ \<le> length (lcl s)\<close> \<open>\<D> E2 \<lfloor>dom X\<rfloor>\<close>
  ultimately show ?case by(fastforce)
next
  case (Call1Obj e s ta e' s' M es Vs E2 X)
  note IH = \<open>\<And>vs e2 x. \<lbrakk> bisim vs e2 e (lcl s); fv e2 \<subseteq> set vs;
            x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_vars e \<le> length (lcl s);
            \<D> e2 \<lfloor>dom x\<rfloor> \<rbrakk> \<Longrightarrow> ?concl e e' e2 s x ta s' e' vs\<close> 
  from \<open>False,compP1 P,t \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>\<close> \<open>bisim Vs E2 (e\<bullet>M(es)) (lcl s)\<close>
  obtain E es' where E2: "E2 = E\<bullet>M(es')" "es = compEs1 Vs es'" and "bisim Vs E e (lcl s)"
    and sync: "\<not> contains_insyncs es'" by(auto elim!: bisim_cases simp add: compEs1_conv_map)
  with IH[of Vs E X] \<open>fv E2 \<subseteq> set Vs\<close> \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]\<close>
    \<open>length Vs + max_vars (e\<bullet>M(es)) \<le> length (lcl s)\<close> \<open>\<D> E2 \<lfloor>dom X\<rfloor>\<close>
  obtain TA' e2' x' where IH': "sim_move10 P t ta e e' E (hp s) X TA' e2' (hp s') x'"
    "bisim Vs e2' e' (lcl s')" "x' \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s']" by(fastforce)
  with E2 \<open>fv E2 \<subseteq> set Vs\<close> \<open>E2 = E\<bullet>M(es')\<close> sync show ?case
    by(cases "is_val e2'")(auto intro: CallObj)
next
  case (Call1Params es s ta es' s' v M Vs E2 X)
  note IH = \<open>\<And>vs es2 x. \<lbrakk> bisims vs es2 es (lcl s); fvs es2 \<subseteq> set vs;
            x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_varss es \<le> length (lcl s); \<D>s es2 \<lfloor>dom x\<rfloor>\<rbrakk> 
           \<Longrightarrow> ?concls es es' es2 s x ta s' es' vs\<close>
  from \<open>bisim Vs E2 (Val v\<bullet>M(es)) (lcl s)\<close> obtain Es
    where "E2 = Val v \<bullet>M(Es)" "bisims Vs Es es (lcl s)" by(auto)
  with IH[of Vs Es X] \<open>fv E2 \<subseteq> set Vs\<close> \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]\<close>
    \<open>length Vs + max_vars (Val v\<bullet>M(es)) \<le> length (lcl s)\<close> \<open>\<D> E2 \<lfloor>dom X\<rfloor>\<close>
    \<open>E2 = Val v \<bullet>M(Es)\<close> show ?case by(fastforce intro: CallParams)
next
  case (Red1CallExternal s a T M Ts Tr D vs ta va h' e' s' Vs E2 X)
  from \<open>bisim Vs E2 (addr a\<bullet>M(map Val vs)) (lcl s)\<close> have E2: "E2 = addr a\<bullet>M(map Val vs)" by auto
  moreover from \<open>compP1 P \<turnstile> class_type_of T sees M: Ts\<rightarrow>Tr = Native in D\<close>
  have "P \<turnstile> class_type_of T sees M: Ts\<rightarrow>Tr = Native in D" by simp
  moreover from \<open>compP1 P,t \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>\<close>
  have "P,t \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>" by simp
  moreover from wf \<open>P,t \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>\<close>
  have "ta_bisim01 (extTA2J0 P ta) (extTA2J1 (compP1 P) ta)"
    by(rule red_external_ta_bisim01)
  moreover note \<open>typeof_addr (hp s) a = \<lfloor>T\<rfloor>\<close> \<open>e' = extRet2J1 (addr a\<bullet>M(map Val vs)) va\<close> \<open>s' = (h', lcl s)\<close>
  moreover from \<open>typeof_addr (hp s) a = \<lfloor>T\<rfloor>\<close> \<open>P,t \<turnstile> \<langle>a\<bullet>M(vs),hp s\<rangle> -ta\<rightarrow>ext \<langle>va,h'\<rangle>\<close>
    \<open>P \<turnstile> class_type_of T sees M: Ts\<rightarrow>Tr = Native in D\<close>
  have "\<tau>external_defs D M \<Longrightarrow> ta = \<epsilon> \<and> h' = hp s"
    by(fastforce dest: \<tau>external'_red_external_heap_unchanged \<tau>external'_red_external_TA_empty simp add: \<tau>external'_def \<tau>external_def)
  ultimately show ?case using \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]\<close>
    by(fastforce intro!: exI[where x="extTA2J0 P ta"] intro: RedCallExternal simp add: map_eq_append_conv sim_move10_def synthesized_call_def dest: sees_method_fun del: disjCI intro: disjI1 disjI2)
next
  case (Block1Red e h x ta e' h' x' V T Vs E2 X)
  note IH = \<open>\<And>vs e2 xa. \<lbrakk> bisim vs e2 e (lcl (h, x)); fv e2 \<subseteq> set vs; xa \<subseteq>\<^sub>m [vs [\<mapsto>] lcl (h, x)];
                       length vs + max_vars e \<le> length (lcl (h, x)); \<D> e2 \<lfloor>dom xa\<rfloor>\<rbrakk>
             \<Longrightarrow> ?concl e e' e2 (h, x) xa ta (h', x') e' vs\<close> 
  from \<open>False,compP1 P,t \<turnstile>1 \<langle>e,(h, x)\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>\<close>
  have "length x = length x'" by(auto dest: red1_preserves_len)
  with \<open>length Vs + max_vars {V:T=None; e} \<le> length (lcl (h, x))\<close>
  have "length Vs < length x'" by simp
  from \<open>bisim Vs E2 {V:T=None; e} (lcl (h, x))\<close>
  show ?case
  proof(cases rule: bisim_cases(14)[consumes 1, case_names BlockNone BlockSome BlockSomeNone])
    case (BlockNone V' E)
    with \<open>fv E2 \<subseteq> set Vs\<close> have "fv E \<subseteq> set (Vs@[V'])" by auto
    with IH[of "Vs@[V']" E "X(V' := None)"] BlockNone \<open>fv E2 \<subseteq> set Vs\<close> \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl (h, x)]\<close>
      \<open>length Vs + max_vars {V:T=None; e} \<le> length (lcl (h, x))\<close> \<open>\<D> E2 \<lfloor>dom X\<rfloor>\<close>
    obtain TA' e2' X' where IH': "sim_move10 P t ta e e' E h (X(V' := None)) TA' e2' h' X'"
      "bisim (Vs @ [V']) e2' e' x'" "X' \<subseteq>\<^sub>m [Vs @ [V'] [\<mapsto>] x']"
      by(fastforce simp del: fun_upd_apply)
    { assume "V' \<in> set Vs"
      hence "hidden (Vs @ [V']) (index Vs V')" by(rule hidden_index)
      with \<open>bisim (Vs @ [V']) E e (lcl (h, x))\<close> have "unmod e (index Vs V')"
        by(auto intro: hidden_bisim_unmod)
      moreover from \<open>length Vs + max_vars {V:T=None; e} \<le> length (lcl (h, x))\<close> \<open>V' \<in> set Vs\<close>
      have "index Vs V' < length x" by(auto intro: index_less_aux)
      ultimately have "x ! index Vs V' = x' ! index Vs V'"
        using red1_preserves_unmod[OF \<open>False,compP1 P,t \<turnstile>1 \<langle>e,(h, x)\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>\<close>]
        by(simp) }
    with \<open>length Vs + max_vars {V:T=None; e} \<le> length (lcl (h, x))\<close> 
      \<open>X' \<subseteq>\<^sub>m [Vs @ [V'] [\<mapsto>] x']\<close> \<open>length x = length x'\<close> \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl (h, x)]\<close>
    have rel: "X'(V' := X V') \<subseteq>\<^sub>m [Vs [\<mapsto>] x']" by(auto intro: Block_lem)

    show ?thesis
    proof(cases "X' V'")
      case None
      with BlockNone IH' rel show ?thesis by(fastforce intro: BlockRed)
    next
      case (Some v)
      with \<open>X' \<subseteq>\<^sub>m [Vs @ [V'] [\<mapsto>] x']\<close> \<open>length Vs < length x'\<close>
      have "x' ! length Vs = v" by(auto dest: map_le_SomeD)
      with BlockNone IH' rel Some show ?thesis by(fastforce intro: BlockRed)
    qed
  next
    case BlockSome thus ?thesis by simp
  next
    case (BlockSomeNone V' E)
    with \<open>fv E2 \<subseteq> set Vs\<close> have "fv E \<subseteq> set (Vs@[V'])" by auto
    with IH[of "Vs@[V']" E "X(V' \<mapsto> x ! length Vs)"] BlockSomeNone \<open>fv E2 \<subseteq> set Vs\<close> \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl (h, x)]\<close>
      \<open>length Vs + max_vars {V:T=None; e} \<le> length (lcl (h, x))\<close> \<open>\<D> E2 \<lfloor>dom X\<rfloor>\<close>
    obtain TA' e2' X' where IH': "sim_move10 P t ta e e' E h (X(V' \<mapsto> x ! length Vs)) TA' e2' h' X'"
      "bisim (Vs @ [V']) e2' e' x'" "X' \<subseteq>\<^sub>m [Vs @ [V'] [\<mapsto>] x']"
      by(fastforce simp del: fun_upd_apply)
    { assume "V' \<in> set Vs"
      hence "hidden (Vs @ [V']) (index Vs V')" by(rule hidden_index)
      with \<open>bisim (Vs @ [V']) E e (lcl (h, x))\<close> have "unmod e (index Vs V')"
        by(auto intro: hidden_bisim_unmod)
      moreover from \<open>length Vs + max_vars {V:T=None; e} \<le> length (lcl (h, x))\<close> \<open>V' \<in> set Vs\<close>
      have "index Vs V' < length x" by(auto intro: index_less_aux)
      ultimately have "x ! index Vs V' = x' ! index Vs V'"
        using red1_preserves_unmod[OF \<open>False,compP1 P,t \<turnstile>1 \<langle>e,(h, x)\<rangle> -ta\<rightarrow> \<langle>e',(h', x')\<rangle>\<close>]
        by(simp) }
    with \<open>length Vs + max_vars {V:T=None; e} \<le> length (lcl (h, x))\<close> 
      \<open>X' \<subseteq>\<^sub>m [Vs @ [V'] [\<mapsto>] x']\<close> \<open>length x = length x'\<close> \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl (h, x)]\<close>
    have rel: "X'(V' := X V') \<subseteq>\<^sub>m [Vs [\<mapsto>] x']" by(auto intro: Block_lem)
    from \<open>sim_move10 P t ta e e' E h (X(V' \<mapsto> x ! length Vs)) TA' e2' h' X'\<close>
    obtain v' where "X' V' = \<lfloor>v'\<rfloor>"
      by(auto simp: sim_move10_def split: if_split_asm dest!: \<tau>red0t_lcl_incr \<tau>red0r_lcl_incr red_lcl_incr subsetD)
    with \<open>X' \<subseteq>\<^sub>m [Vs @ [V'] [\<mapsto>] x']\<close> \<open>length Vs < length x'\<close>
    have "x' ! length Vs = v'" by(auto dest: map_le_SomeD)
    with BlockSomeNone IH' rel \<open>X' V' = \<lfloor>v'\<rfloor>\<close>
    show ?thesis by(fastforce intro: BlockRed)
  qed
next
  case(Block1Some V xs T v e h)
  from \<open>bisim vs e2 {V:T=\<lfloor>v\<rfloor>; e} (lcl (h, xs))\<close> obtain e' V' where "e2 = {V':T=\<lfloor>v\<rfloor>; e'}"
    and "V = length vs" "bisim (vs @ [V']) e' e (xs[length vs := v])" by(fastforce)
  moreover have "sim_move10 P t \<epsilon> {length vs:T=\<lfloor>v\<rfloor>; e} {length vs:T=None; e} {V':T=\<lfloor>v\<rfloor>; e'} h x \<epsilon> {V':T=\<lfloor>v\<rfloor>; e'} h x"
    by(auto)
  moreover from \<open>bisim (vs @ [V']) e' e (xs[length vs := v])\<close>
    \<open>length vs + max_vars {V:T=\<lfloor>v\<rfloor>; e} \<le> length (lcl (h, xs))\<close>
  have "bisim vs {V':T=\<lfloor>v\<rfloor>; e'} {length vs:T=None; e} (xs[length vs := v])" by auto
  moreover from \<open>x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl (h, xs)]\<close> \<open>length vs + max_vars {V:T=\<lfloor>v\<rfloor>; e} \<le> length (lcl (h, xs))\<close>
  have "x \<subseteq>\<^sub>m [vs [\<mapsto>] xs[length vs := v]]" by auto
  ultimately show ?case by auto
next
  case (Lock1Synchronized V xs a e h Vs E2 X)
  note len = \<open>length Vs + max_vars (sync\<^bsub>V\<^esub> (addr a) e) \<le> length (lcl (h, xs))\<close>
  from \<open>bisim Vs E2 (sync\<^bsub>V\<^esub> (addr a) e) (lcl (h, xs))\<close> obtain E
    where E2: "E2 = sync(addr a) E" "e = compE1 (Vs@[fresh_var Vs]) E" 
    and sync: "\<not> contains_insync E" and [simp]: "V = length Vs" by auto
  moreover
  have "extTA2J0 P,P,t \<turnstile> \<langle>sync(addr a) E, (h, X)\<rangle> -\<lbrace>Lock\<rightarrow>a, SyncLock a\<rbrace>\<rightarrow> \<langle>insync(a) E, (h, X)\<rangle>"
    by(rule LockSynchronized)
  moreover from \<open>fv E2 \<subseteq> set Vs\<close> fresh_var_fresh[of Vs] sync len
  have "bisim Vs (insync(a) E) (insync\<^bsub>length Vs\<^esub> (a) e) (xs[length Vs := Addr a])"
    unfolding \<open>e = compE1 (Vs@[fresh_var Vs]) E\<close> \<open>E2 = sync(addr a) E\<close>
    by -(rule bisimInSynchronized,rule compE1_bisim, auto)
  moreover have "zip Vs (xs[length Vs := Addr a]) = (zip Vs xs)[length Vs := (arbitrary, Addr a)]"
    by(rule sym)(simp add: update_zip)
  hence "zip Vs (xs[length Vs := Addr a]) = zip Vs xs" by simp
  with \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] (lcl (h, xs))]\<close> have "X \<subseteq>\<^sub>m [Vs [\<mapsto>] xs[length Vs := Addr a]]"
    by(auto simp add: map_le_def map_upds_def)
  ultimately show ?case by(fastforce intro: sim_move10_SyncLocks)
next
  case (Synchronized1Red2 e s ta e' s' V a Vs E2 X)
  note IH = \<open>\<And>vs e2 x. \<lbrakk> bisim vs e2 e (lcl s); fv e2 \<subseteq> set vs;
            x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_vars e \<le> length (lcl s);
            \<D> e2 \<lfloor>dom x\<rfloor> \<rbrakk> \<Longrightarrow> ?concl e e' e2 s x ta s' e' vs\<close> 
  from \<open>bisim Vs E2 (insync\<^bsub>V\<^esub> (a) e) (lcl s)\<close> obtain E
    where E2: "E2 = insync(a) E" and bisim: "bisim (Vs@[fresh_var Vs]) E e (lcl s)"
    and xsa: "lcl s ! length Vs = Addr a" and [simp]: "V = length Vs" by auto
  with \<open>fv E2 \<subseteq> set Vs\<close> fresh_var_fresh[of Vs] have fv: "(fresh_var Vs) \<notin> fv E" by auto
  from \<open>length Vs + max_vars (insync\<^bsub>V\<^esub> (a) e) \<le> length (lcl s)\<close> have "length Vs < length (lcl s)" by simp
  { assume "X (fresh_var Vs) \<noteq> None"
    then obtain v where "X (fresh_var Vs) = \<lfloor>v\<rfloor>" by auto
    with \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]\<close> have "[Vs [\<mapsto>] lcl s] (fresh_var Vs) = \<lfloor>v\<rfloor>" 
      by(auto simp add: map_le_def dest: bspec)
    hence "(fresh_var Vs) \<in> set Vs" 
      by(auto simp add: map_upds_def set_zip dest!: map_of_SomeD )
    moreover have "(fresh_var Vs) \<notin> set Vs" by(rule fresh_var_fresh)
    ultimately have False by contradiction }
  hence "X (fresh_var Vs) = None" by(cases "X (fresh_var Vs)", auto)
  hence "X(fresh_var Vs := None) = X" by(auto intro: ext)
  moreover from \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]\<close>
  have "X(fresh_var Vs := None) \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s, (fresh_var Vs) \<mapsto> (lcl s) ! length Vs]" by(simp)
  ultimately have "X \<subseteq>\<^sub>m [Vs @ [fresh_var Vs] [\<mapsto>] lcl s]"
    using \<open>length Vs < length (lcl s)\<close> by(auto)
  moreover note IH[of "Vs@[fresh_var Vs]" E X] bisim E2 \<open>fv E2 \<subseteq> set Vs\<close> \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]\<close> 
    \<open>length Vs + max_vars (insync\<^bsub>V\<^esub> (a) e) \<le> length (lcl s)\<close> \<open>\<D> E2 \<lfloor>dom X\<rfloor>\<close>
  ultimately obtain TA' e2' x' where IH': "sim_move10 P t ta e e' E (hp s) X TA' e2' (hp s') x'"
    "bisim (Vs @ [fresh_var Vs]) e2' e' (lcl s')" "x' \<subseteq>\<^sub>m [Vs @ [fresh_var Vs] [\<mapsto>] lcl s']" by auto
  hence "dom x' \<subseteq> dom X \<union> fv E"
    by(fastforce iff del: domIff simp add: sim_move10_def dest: red_dom_lcl \<tau>red0r_dom_lcl[OF wf_prog_wwf_prog[OF wf]] \<tau>red0t_dom_lcl[OF wf_prog_wwf_prog[OF wf]] \<tau>red0r_fv_subset[OF wf_prog_wwf_prog[OF wf]] split: if_split_asm)
  with fv \<open>X (fresh_var Vs) = None\<close> have "(fresh_var Vs) \<notin> dom x'" by auto
  hence "x' (fresh_var Vs) = None" by auto
  moreover from \<open>False,compP1 P,t \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>\<close>
  have "length (lcl s) = length (lcl s')" by(auto dest: red1_preserves_len)
  moreover note \<open>x' \<subseteq>\<^sub>m [Vs @ [fresh_var Vs] [\<mapsto>] lcl s']\<close> \<open>length Vs < length (lcl s)\<close>
  ultimately have "x' \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s']" by(auto simp add: map_le_def dest: bspec)
  moreover from bisim fv have "unmod e (length Vs)" by(auto intro: bisim_fv_unmod)
  with \<open>False,compP1 P,t \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>\<close> \<open>length Vs < length (lcl s)\<close>
  have "lcl s ! length Vs = lcl s' ! length Vs"
    by(auto dest!: red1_preserves_unmod)
  with xsa have "lcl s' ! length Vs = Addr a" by simp
  ultimately show ?case using IH' E2 by(auto intro: SynchronizedRed2)
next
  case (Unlock1Synchronized xs V a' a v h Vs E2 X)
  from \<open>bisim Vs E2 (insync\<^bsub>V\<^esub> (a) Val v) (lcl (h, xs))\<close>
  have E2: "E2 = insync(a) Val v" "V = length Vs" "xs ! length Vs = Addr a" by auto
  moreover with \<open>xs ! V = Addr a'\<close> have [simp]: "a' = a" by simp
  have "extTA2J0 P,P,t \<turnstile> \<langle>insync(a) (Val v), (h, X)\<rangle> -\<lbrace>Unlock\<rightarrow>a, SyncUnlock a\<rbrace>\<rightarrow> \<langle>Val v, (h, X)\<rangle>"
    by(rule UnlockSynchronized)
  ultimately show ?case using \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl (h, xs)]\<close> by(fastforce intro: sim_move10_SyncLocks)
next
  case (Unlock1SynchronizedNull xs V a v h Vs E2 X)
  from \<open>bisim Vs E2 (insync\<^bsub>V\<^esub> (a) Val v) (lcl (h, xs))\<close>
  have "V = length Vs" "xs ! length Vs = Addr a" by(auto)
  with \<open>xs ! V = Null\<close> have False by simp
  thus ?case ..
next
  case (Unlock1SynchronizedFail xs V A' a' v h Vs E2 X)
  from \<open>False\<close> show ?case ..
next
  case (Red1While b c s Vs E2 X)
  from \<open>bisim Vs E2 (while (b) c) (lcl s)\<close> obtain B C
    where E2: "E2 = while (B) C" "b = compE1 Vs B" "c = compE1 Vs C" 
    and sync: "\<not> contains_insync B" "\<not> contains_insync C" by auto
  moreover have "extTA2J0 P,P,t \<turnstile> \<langle>while (B) C, (hp s, X)\<rangle> -\<epsilon>\<rightarrow> \<langle>if (B) (C;;while (B) C) else unit, (hp s, X)\<rangle>"
    by(rule RedWhile)
  hence "sim_move10 P t \<epsilon> (while (compE1 Vs B) (compE1 Vs C)) (if (compE1 Vs B) (compE1 Vs C;;while (compE1 Vs B) (compE1 Vs C)) else unit) (while (B) C) (hp s) X \<epsilon> (if (B) (C;;while (B) C) else unit) (hp s) X"
    by(auto simp add: sim_move10_def)
  moreover from \<open>fv E2 \<subseteq> set Vs\<close> E2 sync
  have "bisim Vs (if (B) (C;; while (B) C) else unit)
                 (if (compE1 Vs B) (compE1 Vs (C;; while(B) C)) else (compE1 Vs unit)) (lcl s)"
    by -(rule bisimCond, auto)
  ultimately show ?case using \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]\<close>
    by(simp)(rule exI, rule exI, rule exI, erule conjI, auto)
next
  case (Red1TryCatch h a D C V x e2 Vs E2 X)
  from \<open>bisim Vs E2 (try Throw a catch(C V) e2) (lcl (h, x))\<close>
  obtain E2' V' where "E2 = try Throw a catch(C V') E2'" "V = length Vs" "e2 = compE1 (Vs @ [V']) E2'"
    and sync: "\<not> contains_insync E2'" by(auto)
  with \<open>fv E2 \<subseteq> set Vs\<close> have "fv E2' \<subseteq> set (Vs @[V'])" by auto
  with \<open>e2 = compE1 (Vs @ [V']) E2'\<close>  sync have "bisim (Vs @[V']) E2' e2 (x[V := Addr a])"
    by(auto intro!: compE1_bisim)
  with \<open>V = length Vs\<close> \<open>length Vs + max_vars (try Throw a catch(C V) e2) \<le> length (lcl (h, x))\<close>
  have "bisim Vs {V':Class C=\<lfloor>Addr a\<rfloor>; E2'} {length Vs:Class C=None; e2} (x[V := Addr a])"
    by(auto intro: bisimBlockSomeNone)
  moreover from \<open>length Vs + max_vars (try Throw a catch(C V) e2) \<le> length (lcl (h, x))\<close>
  have "[Vs [\<mapsto>] x[length Vs := Addr a]] = [Vs [\<mapsto>] x]" by simp
  with \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl (h, x)]\<close> have "X \<subseteq>\<^sub>m [Vs [\<mapsto>] x[length Vs := Addr a]]" by simp
  moreover note \<open>e2 = compE1 (Vs @ [V']) E2'\<close> \<open>E2 = try Throw a catch(C V') E2'\<close>
    \<open>typeof_addr h a = \<lfloor>Class_type D\<rfloor>\<close> \<open>compP1 P \<turnstile> D \<preceq>\<^sup>* C\<close> \<open>V = length Vs\<close>
  ultimately show ?case by(auto intro!: exI)
next
  case Red1TryFail thus ?case by(auto intro!: exI sim_move10_TryFail)
next
  case (List1Red1 e s ta e' s' es Vs ES2 X)
  note IH = \<open>\<And>vs e2 x. \<lbrakk> bisim vs e2 e (lcl s); fv e2 \<subseteq> set vs;
            x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_vars e \<le> length (lcl s); \<D> e2 \<lfloor>dom x\<rfloor>\<rbrakk>
           \<Longrightarrow> \<exists>TA' e2' x'. sim_move10 P t ta e e' e2 (hp s) x TA' e2' (hp s') x' \<and> 
                 bisim vs e2' e' (lcl s') \<and> x' \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s']\<close>
  from \<open>bisims Vs ES2 (e # es) (lcl s)\<close> \<open>False,compP1 P,t \<turnstile>1 \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle>\<close>
  obtain E ES where "ES2 = E # ES" "\<not> is_val E" "es = compEs1 Vs ES" "bisim Vs E e (lcl s)"
    and sync: "\<not> contains_insyncs ES" by(auto elim!: bisims_cases simp add: compEs1_conv_map)
  with IH[of Vs E X] \<open>fvs ES2 \<subseteq> set Vs\<close> \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]\<close>
    \<open>length Vs + max_varss (e # es) \<le> length (lcl s)\<close> \<open>\<D>s ES2 \<lfloor>dom X\<rfloor>\<close>
  obtain TA' e2' x' where IH': "sim_move10 P t ta e e' E (hp s) X TA' e2' (hp s') x'"
    "bisim Vs e2' e' (lcl s')" "x' \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s']" by fastforce
  show ?case
  proof(cases "is_val e2'")
    case False
    with IH' \<open>ES2 = E # ES\<close> \<open>es = compEs1 Vs ES\<close> sync show ?thesis by(auto intro: sim_moves10_expr)
  next
    case True
    from \<open>fvs ES2 \<subseteq> set Vs\<close> \<open>ES2 = E # ES\<close> \<open>es = compEs1 Vs ES\<close> sync
    have "bisims Vs ES es (lcl s')" by(auto intro: compEs1_bisims)
    with IH' True \<open>ES2 = E # ES\<close> \<open>es = compEs1 Vs ES\<close> show ?thesis by(auto intro: sim_moves10_expr)
  qed
next
  case (List1Red2 es s ta es' s' v Vs ES2 X)
  note IH = \<open>\<And>vs es2 x. \<lbrakk>bisims vs es2 es (lcl s); fvs es2 \<subseteq> set vs;
            x \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s]; length vs + max_varss es \<le> length (lcl s); \<D>s es2 \<lfloor>dom x\<rfloor>\<rbrakk>
           \<Longrightarrow> \<exists>TA' es2' x'. sim_moves10 P t ta es es' es2 (hp s) x TA' es2' (hp s') x' \<and> bisims vs es2' es' (lcl s') \<and> x' \<subseteq>\<^sub>m [vs [\<mapsto>] lcl s']\<close>
  from \<open>bisims Vs ES2 (Val v # es) (lcl s)\<close> obtain ES where "ES2 = Val v # ES" "bisims Vs ES es (lcl s)"
    by(auto elim!: bisims_cases)
  with IH[of Vs ES X] \<open>fvs ES2 \<subseteq> set Vs\<close> \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl s]\<close>
    \<open>length Vs + max_varss (Val v # es) \<le> length (lcl s)\<close> \<open>\<D>s ES2 \<lfloor>dom X\<rfloor>\<close>
    \<open>ES2 = Val v # ES\<close> show ?case by(fastforce intro: sim_moves10_expr)
next
  case Call1ThrowParams
  thus ?case by(fastforce intro: CallThrowParams elim!: bisim_cases simp add: bisims_map_Val_Throw2)
next
  case (Synchronized1Throw2 xs V a' a ad h Vs E2 X)
  from \<open>bisim Vs E2 (insync\<^bsub>V\<^esub> (a) Throw ad) (lcl (h, xs))\<close>
  have "xs ! length Vs = Addr a" and "V = length Vs" by auto
  with \<open>xs ! V = Addr a'\<close> have [simp]: "a' = a" by simp
  have "extTA2J0 P,P,t \<turnstile> \<langle>insync(a) Throw ad, (h, X)\<rangle> -\<lbrace>Unlock\<rightarrow>a, SyncUnlock a\<rbrace>\<rightarrow> \<langle>Throw ad, (h, X)\<rangle>"
    by(rule SynchronizedThrow2)
  with \<open>X \<subseteq>\<^sub>m [Vs [\<mapsto>] lcl (h, xs)]\<close> \<open>bisim Vs E2 (insync\<^bsub>V\<^esub> (a) Throw ad) (lcl (h, xs))\<close>
  show ?case by(auto intro: sim_move10_SyncLocks intro!: exI)
next
  case (Synchronized1Throw2Null xs V a a' h Vs E2 X)
  from \<open>bisim Vs E2 (insync\<^bsub>V\<^esub> (a) Throw a') (lcl (h, xs))\<close>
  have "V = length Vs" "xs ! length Vs = Addr a" by(auto)
  with \<open>xs ! V = Null\<close> have False by simp
  thus ?case ..
next
  case (Synchronized1Throw2Fail xs V A' a' a h Vs E2 X)
  from \<open>False\<close> show ?case ..
next
  case InstanceOf1Red thus ?case by auto(blast)
next
  case Red1InstanceOf thus ?case by hypsubst_thin auto
next
  case InstanceOf1Throw thus ?case by auto
next
  case CAS1Throw thus ?case by fastforce
next
  case CAS1Throw2 thus ?case by fastforce
next
  case CAS1Throw3 thus ?case by fastforce
qed(simp_all del: fun_upd_apply, (fastforce intro: red_reds.intros simp del: fun_upd_apply simp add: finfun_upd_apply)+)

lemma bisim_call_Some_call1:
  "\<lbrakk> bisim Vs e e' xs; call e = \<lfloor>aMvs\<rfloor>; length Vs + max_vars e' \<le> length xs \<rbrakk>
  \<Longrightarrow> \<exists>e'' xs'. \<tau>red1'r P t h (e', xs) (e'', xs') \<and> call1 e'' = \<lfloor>aMvs\<rfloor> \<and> 
               bisim Vs e e'' xs' \<and> take (length Vs) xs = take (length Vs) xs'"

  and bisims_calls_Some_calls1:
  "\<lbrakk> bisims Vs es es' xs; calls es = \<lfloor>aMvs\<rfloor>; length Vs + max_varss es' \<le> length xs \<rbrakk> 
  \<Longrightarrow> \<exists>es'' xs'. \<tau>reds1'r P t h (es', xs) (es'', xs') \<and> calls1 es'' = \<lfloor>aMvs\<rfloor> \<and> 
                bisims Vs es es'' xs' \<and> take (length Vs) xs = take (length Vs) xs'"
proof(induct rule: bisim_bisims.inducts)
  case bisimCallParams thus ?case
    by(fastforce simp add: is_vals_conv split: if_split_asm)
next
  case bisimBlockNone thus ?case by(fastforce intro: take_eq_take_le_eq)
next
  case (bisimBlockSome Vs V e e' xs v T)
  from \<open>length Vs + max_vars {length Vs:T=\<lfloor>v\<rfloor>; e'} \<le> length xs\<close>
  have "\<tau>red1'r P t h ({length Vs:T=\<lfloor>v\<rfloor>; e'}, xs) ({length Vs:T=None; e'}, xs[length Vs := v])"
    by(auto intro!: \<tau>red1r_1step Block1Some)
  also from bisimBlockSome obtain e'' xs'
    where "\<tau>red1'r P t h (e', xs[length Vs := v]) (e'', xs')"
    and "call1 e'' = \<lfloor>aMvs\<rfloor>" "bisim (Vs @ [V]) e e'' xs'" 
    and "take (length (Vs @ [V])) (xs[length Vs := v]) = take (length (Vs @ [V])) xs'" by auto
  hence "\<tau>red1'r P t h ({length Vs:T=None; e'}, xs[length Vs := v]) ({length Vs:T=None; e''}, xs')" by auto
  also from \<open>call1 e'' = \<lfloor>aMvs\<rfloor>\<close> have "call1 {length Vs:T=None; e''} = \<lfloor>aMvs\<rfloor>" by simp
  moreover from \<open>take (length (Vs @ [V])) (xs[length Vs := v]) = take (length (Vs @ [V])) xs'\<close>
  have "take (length Vs) xs = take (length Vs) xs'"
    by(auto dest: take_eq_take_le_eq[where m="length Vs"] simp add: take_list_update_beyond)
  moreover {
    have "xs' ! length Vs = take (length (Vs @ [V])) xs' ! length Vs" by simp
    also note \<open>take (length (Vs @ [V])) (xs[length Vs := v]) = take (length (Vs @ [V])) xs'\<close>[symmetric]
    also have "take (length (Vs @ [V])) (xs[length Vs := v]) ! length Vs = v"
      using \<open>length Vs + max_vars {length Vs:T=\<lfloor>v\<rfloor>; e'} \<le> length xs\<close> by simp
    finally have "bisim Vs {V:T=\<lfloor>v\<rfloor>; e} {length Vs:T=None; e''} xs'"
      using \<open>bisim (Vs @ [V]) e e'' xs'\<close> by auto }
  ultimately show ?case by blast
next
  case (bisimBlockSomeNone Vs V e e' xs v T)
  then obtain e'' xs' where "\<tau>red1'r P t h (e', xs) (e'', xs')" "call1 e'' = \<lfloor>aMvs\<rfloor>" "bisim (Vs @ [V]) e e'' xs'"
    and "take (length (Vs @ [V])) xs = take (length (Vs @ [V])) xs'" by auto
  hence "\<tau>red1'r P t h ({length Vs:T=None; e'}, xs) ({length Vs:T=None; e''}, xs')" by auto
  moreover from \<open>call1 e'' = \<lfloor>aMvs\<rfloor>\<close> have "call1 ({length Vs:T=None; e''}) = \<lfloor>aMvs\<rfloor>" by simp
  moreover from \<open>take (length (Vs @ [V])) xs = take (length (Vs @ [V])) xs'\<close>
  have "take (length Vs) xs = take (length Vs) xs'" by(auto intro: take_eq_take_le_eq)
  moreover {
    have "xs' ! length Vs = take (length (Vs @ [V])) xs' ! length Vs" by simp
    also note \<open>take (length (Vs @ [V])) xs = take (length (Vs @ [V])) xs'\<close>[symmetric]
    also have "take (length (Vs @ [V])) xs ! length Vs = v" using \<open>xs ! length Vs = v\<close> by simp
    finally have "bisim Vs {V:T=\<lfloor>v\<rfloor>; e} {length Vs:T=None; e''} xs'"
      using \<open>bisim (Vs @ [V]) e e'' xs'\<close> by auto }
  ultimately show ?case by blast
next
  case (bisimInSynchronized Vs e e' xs a)
  then obtain e'' xs' where "\<tau>red1'r P t h (e', xs) (e'', xs')" "call1 e'' = \<lfloor>aMvs\<rfloor>" "bisim (Vs @ [fresh_var Vs]) e e'' xs'"
    and "take (Suc (length Vs)) xs = take (Suc (length Vs)) xs'" by auto
  hence "\<tau>red1'r P t h (insync\<^bsub>length Vs\<^esub> (a) e', xs) (insync\<^bsub>length Vs\<^esub> (a) e'', xs')" by auto
  moreover from \<open>call1 e'' = \<lfloor>aMvs\<rfloor>\<close> have "call1 (insync\<^bsub>length Vs\<^esub> (a) e'') = \<lfloor>aMvs\<rfloor>" by simp
  moreover from \<open>take (Suc (length Vs)) xs = take (Suc (length Vs)) xs'\<close>
  have "take (length Vs) xs = take (length Vs) xs'" by(auto intro: take_eq_take_le_eq)
  moreover {
    have "xs' ! length Vs = take (Suc (length Vs)) xs' ! length Vs" by simp
    also note \<open>take (Suc (length Vs)) xs = take (Suc (length Vs)) xs'\<close>[symmetric]
    also have "take (Suc (length Vs)) xs ! length Vs = Addr a"
      using \<open>xs ! length Vs = Addr a\<close> by simp
    finally have "bisim Vs (insync(a) e) (insync\<^bsub>length Vs\<^esub> (a) e'') xs'"
      using \<open>bisim (Vs @ [fresh_var Vs]) e e'' xs'\<close> by auto }
  ultimately show ?case by blast
next
  case bisimsCons1 thus ?case by(fastforce intro!: \<tau>red1r_inj_\<tau>reds1r)
next
  case bisimsCons2 thus ?case by(fastforce intro!: \<tau>reds1r_cons_\<tau>reds1r)
qed fastforce+

lemma sim_move01_into_Red1:
  "sim_move01 P t ta e E' h xs ta' e2' h' xs'
  \<Longrightarrow> if \<tau>Move0 P h (e, es1)
      then \<tau>Red1't P t h ((E', xs), exs2) ((e2', xs'), exs2) \<and> ta = \<epsilon> \<and> h = h'
      else \<exists>ex2' exs2' ta'. \<tau>Red1'r P t h ((E', xs), exs2) (ex2', exs2') \<and>
                           (call e = None \<or> call1 E' = None \<or> ex2' = (E', xs) \<and> exs2' = exs2) \<and>
                           False,P,t \<turnstile>1 \<langle>ex2'/exs2',h\<rangle> -ta'\<rightarrow> \<langle>(e2', xs')/exs2,h'\<rangle> \<and>
                           \<not> \<tau>Move1 P h (ex2', exs2') \<and> ta_bisim01 ta ta'"
apply(auto simp add: sim_move01_def intro: \<tau>red1t_into_\<tau>Red1t \<tau>red1r_into_\<tau>Red1r red1Red split: if_split_asm)
apply(fastforce intro: red1Red intro!: \<tau>red1r_into_\<tau>Red1r)+
done

lemma sim_move01_max_vars_decr:
  "sim_move01 P t ta e0 e h xs ta' e' h' xs' \<Longrightarrow> max_vars e' \<le> max_vars e"
by(fastforce simp add: sim_move01_def split: if_split_asm dest: \<tau>red1t_max_vars red1_max_vars_decr \<tau>red1r_max_vars)

lemma Red1_simulates_red0:
  assumes wf: "wf_J_prog P"
  and red: "P,t \<turnstile>0 \<langle>e1/es1, h\<rangle> -ta\<rightarrow> \<langle>e1'/es1', h'\<rangle>"
  and bisiml: "bisim_list1 (e1, es1) (ex2, exs2)"
  shows "\<exists>ex2'' exs2''. bisim_list1 (e1', es1') (ex2'', exs2'') \<and>
        (if \<tau>Move0 P h (e1, es1)
         then \<tau>Red1't (compP1 P) t h (ex2, exs2) (ex2'', exs2'') \<and> ta = \<epsilon> \<and> h = h'
         else \<exists>ex2' exs2' ta'. \<tau>Red1'r (compP1 P) t h (ex2, exs2) (ex2', exs2') \<and> 
                               (call e1 = None \<or> call1 (fst ex2) = None \<or> ex2' = ex2 \<and> exs2' = exs2) \<and>
                               False,compP1 P,t \<turnstile>1 \<langle>ex2'/exs2', h\<rangle> -ta'\<rightarrow> \<langle>ex2''/exs2'', h'\<rangle> \<and>
                               \<not> \<tau>Move1 P h (ex2', exs2') \<and> ta_bisim01 ta ta')"
  (is "\<exists>ex2'' exs2'' . _ \<and> ?red ex2'' exs2''")
using red
proof(cases)
  case (red0Red XS')
  note [simp] = \<open>es1' = es1\<close>
    and red = \<open>extTA2J0 P,P,t \<turnstile> \<langle>e1,(h, Map.empty)\<rangle> -ta\<rightarrow> \<langle>e1',(h', XS')\<rangle>\<close>
    and notsynth = \<open>\<forall>aMvs. call e1 = \<lfloor>aMvs\<rfloor> \<longrightarrow> synthesized_call P h aMvs\<close>
  from bisiml obtain E xs where ex2: "ex2 = (E, xs)"
    and bisim: "bisim [] e1 E xs" and fv: "fv e1 = {}" 
    and length: "max_vars E \<le> length xs" and bsl: "bisim_list es1 exs2"
    and D: "\<D> e1 \<lfloor>{}\<rfloor>" by(auto elim!: bisim_list1_elim)
  from bisim_max_vars[OF bisim] length red1_simulates_red_aux[OF wf red bisim] fv notsynth
  obtain ta' e2' xs' where sim: "sim_move01 (compP1 P) t ta e1 E h xs ta' e2' h' xs'"
    and bisim': "bisim [] e1' e2' xs'" and XS': "XS' \<subseteq>\<^sub>m Map.empty" by auto
  from sim_move01_into_Red1[OF sim, of es1 exs2]
  have "?red (e2', xs') exs2" unfolding ex2 by auto
  moreover {
    note bsl bisim' moreover
    from fv red_fv_subset[OF wf_prog_wwf_prog[OF wf] red]
    have "fv e1' = {}" by simp
    moreover from red D have "\<D> e1' \<lfloor>dom XS'\<rfloor>"
      by(auto dest: red_preserves_defass[OF wf] split: if_split_asm)
    with red_dom_lcl[OF red] \<open>fv e1 = {}\<close> have "\<D> e1' \<lfloor>{}\<rfloor>"
      by(auto elim!: D_mono' simp add: hyperset_defs)
    moreover from sim have "length xs = length xs'" "max_vars e2' \<le> max_vars E"
      by(auto dest: sim_move01_preserves_len sim_move01_max_vars_decr)
    with length have length': "max_vars e2' \<le> length xs'" by(auto)
    ultimately have "bisim_list1 (e1', es1) ((e2', xs'), exs2)" by(rule bisim_list1I) }
  ultimately show ?thesis using ex2 by(simp split del: if_split)(rule exI conjI|assumption)+
next
  case (red0Call a M vs U Ts T pns body D)
  note [simp] = \<open>ta = \<epsilon>\<close> \<open>h' = h\<close>
    and es1' = \<open>es1' = e1 # es1\<close>
    and e1' = \<open>e1' = blocks (this # pns) (Class D # Ts) (Addr a # vs) body\<close>
    and call = \<open>call e1 = \<lfloor>(a, M, vs)\<rfloor>\<close>
    and ha = \<open>typeof_addr h a = \<lfloor>U\<rfloor>\<close>
    and sees = \<open>P \<turnstile> class_type_of U sees M: Ts\<rightarrow>T = \<lfloor>(pns, body)\<rfloor> in D\<close>
    and len = \<open>length vs = length pns\<close> \<open>length Ts = length pns\<close>
  from bisiml obtain E xs where ex2: "ex2 = (E, xs)"
    and bisim: "bisim [] e1 E xs" and fv: "fv e1 = {}" 
    and length: "max_vars E \<le> length xs" and bsl: "bisim_list es1 exs2"
    and D: "\<D> e1 \<lfloor>{}\<rfloor>" by(auto elim!: bisim_list1_elim)
  
  from bisim_call_Some_call1[OF bisim call, of "compP1 P" t h] length
  obtain e' xs' where red: "\<tau>red1'r (compP1 P) t h (E, xs) (e', xs')"
    and "call1 e' = \<lfloor>(a, M, vs)\<rfloor>" "bisim [] e1 e' xs'" 
    and "take 0 xs = take 0 xs'" by auto
    
  let ?e1' = "blocks (this # pns) (Class D # Ts) (Addr a # vs) body"
  let ?e2' = "blocks1 0 (Class D#Ts) (compE1 (this # pns) body)"
  let ?xs2' = "Addr a # vs @ replicate (max_vars (compE1 (this # pns) body)) undefined_value"
  let ?exs2' = "(e', xs') # exs2"

  have "\<tau>Red1'r (compP1 P) t h ((E, xs), exs2) ((e', xs'), exs2)"
    using red by(rule \<tau>red1r_into_\<tau>Red1r)
  moreover {
    note \<open>call1 e' = \<lfloor>(a, M, vs)\<rfloor>\<close> 
    moreover note ha
    moreover have "compP1 P \<turnstile> class_type_of U sees M:Ts \<rightarrow> T = map_option (\<lambda>(pns, body). compE1 (this # pns) body) \<lfloor>(pns, body)\<rfloor> in D"
      using sees unfolding compP1_def by(rule sees_method_compP)
    hence sees': "compP1 P \<turnstile> class_type_of U sees M:Ts \<rightarrow> T = \<lfloor>compE1 (this # pns) body\<rfloor> in D" by simp
    moreover from len have "length vs = length Ts" by simp
    ultimately have "False,compP1 P,t \<turnstile>1 \<langle>(e', xs')/exs2,h\<rangle> -\<epsilon>\<rightarrow> \<langle>(?e2', ?xs2')/?exs2', h\<rangle>" by(rule red1Call) 
    moreover have "\<tau>Move1 P h ((e', xs'), exs2)" using \<open>call1 e' = \<lfloor>(a, M, vs)\<rfloor>\<close> ha sees
      by(auto simp add: synthesized_call_def \<tau>external'_def dest: sees_method_fun dest!: \<tau>move1_not_call1[where P=P and h=h])
    ultimately have "\<tau>Red1' (compP1 P) t h ((e', xs'), exs2) ((?e2', ?xs2'), ?exs2')" by auto }
  ultimately have "\<tau>Red1't (compP1 P) t h ((E, xs), exs2) ((?e2', ?xs2'), ?exs2')" by(rule rtranclp_into_tranclp1)
  moreover
  { from red have "length xs' = length xs" by(rule \<tau>red1r_preserves_len)
    moreover from red have "max_vars e' \<le> max_vars E" by(rule \<tau>red1r_max_vars)
    ultimately have "max_vars e' \<le> length xs'" using length by simp }
  with bsl \<open>bisim [] e1 e' xs'\<close> fv D have "bisim_list (e1 # es1) ?exs2'"
    using \<open>call e1 = \<lfloor>(a, M, vs)\<rfloor>\<close> \<open>call1 e' = \<lfloor>(a, M, vs)\<rfloor>\<close> by(rule bisim_listCons)
  hence "bisim_list1 (e1', es1') ((?e2', ?xs2'), ?exs2')"
    unfolding e1' es1'
  proof(rule bisim_list1I)
    from wf_prog_wwf_prog[OF wf] sees
    have "wf_mdecl wwf_J_mdecl P D (M,Ts,T,\<lfloor>(pns,body)\<rfloor>)" by(rule sees_wf_mdecl)
    hence fv': "fv body \<subseteq> set pns \<union> {this}" by(auto simp add: wf_mdecl_def)
    moreover from \<open>P \<turnstile> class_type_of U sees M: Ts\<rightarrow>T = \<lfloor>(pns, body)\<rfloor> in D\<close> have "\<not> contains_insync body"
      by(auto dest!: sees_wf_mdecl[OF wf] WT_expr_locks simp add: wf_mdecl_def contains_insync_conv)
    ultimately have "bisim ([this] @ pns) body (compE1 ([this] @ pns) body) ?xs2'"
      by -(rule compE1_bisim, auto)
    with \<open>length vs = length pns\<close> \<open>length Ts = length pns\<close>
    have "bisim ([] @ [this]) (blocks pns Ts vs body) (blocks1 (Suc 0) Ts (compE1 (this # pns) body)) ?xs2'"
      by -(drule blocks_bisim,auto simp add: nth_append)
    from bisimBlockSomeNone[OF this, of "Addr a" "Class D"]
    show "bisim [] ?e1' ?e2' ?xs2'" by simp
    from fv' len show "fv ?e1' = {}" by auto

    from wf sees
    have "wf_mdecl wf_J_mdecl P D (M,Ts,T,\<lfloor>(pns,body)\<rfloor>)" by(rule sees_wf_mdecl)
    hence "\<D> body \<lfloor>set pns \<union> {this}\<rfloor>" by(auto simp add: wf_mdecl_def)
    with \<open>length vs = length pns\<close> \<open>length Ts = length pns\<close>
    have "\<D> (blocks pns Ts vs body) \<lfloor>dom [this \<mapsto> Addr a]\<rfloor>" by(auto)
    thus "\<D> ?e1' \<lfloor>{}\<rfloor>" by auto
    
    from len show "max_vars ?e2' \<le> length ?xs2'" by(auto simp add: blocks1_max_vars)
  qed
  moreover have "\<tau>Move0 P h (e1, es1)" using call ha sees
    by(fastforce simp add: synthesized_call_def  \<tau>external'_def dest: sees_method_fun \<tau>move0_callD[where P=P and h=h])
  ultimately show ?thesis using ex2 \<open>call e1 = \<lfloor>(a, M, vs)\<rfloor>\<close> 
    by(simp del: \<tau>Move1.simps)(rule exI conjI|assumption)+
next
  case (red0Return e)
  note es1 = \<open>es1 = e # es1'\<close> and e1' = \<open>e1' = inline_call e1 e\<close>
    and [simp] = \<open>ta = \<epsilon>\<close> \<open>h' = h\<close>
    and fin = \<open>final e1\<close>
  from bisiml es1 obtain E' xs' E xs exs' aMvs where ex2: "ex2 = (E', xs')" and exs2: "exs2 = (E, xs) # exs'"
    and bisim': "bisim [] e1 E' xs'"
    and bisim: "bisim [] e E xs"
    and fv: "fv e = {}"
    and length: "max_vars E \<le> length xs"
    and bisiml: "bisim_list es1' exs'"
    and D: "\<D> e \<lfloor>{}\<rfloor>"
    and call: "call e = \<lfloor>aMvs\<rfloor>"
    and call1: "call1 E = \<lfloor>aMvs\<rfloor>"
    by(fastforce elim: bisim_list1_elim)
  let ?e2' = "inline_call E' E"

  from \<open>final e1\<close> bisim' have "final E'" by(auto)
  hence red': "False,compP1 P,t \<turnstile>1 \<langle>ex2/exs2, h\<rangle> -\<epsilon>\<rightarrow> \<langle>(?e2', xs)/exs', h\<rangle>"
    unfolding ex2 exs2 by(rule red1Return)
  moreover have "\<tau>Move0 P h (e1, es1) = \<tau>Move1 P h ((E', xs'), exs2)"
    using \<open>final e1\<close> \<open>final E'\<close> by auto
  moreover {
    note bisiml
    moreover
    from bisim' fin bisim
    have "bisim [] (inline_call e1 e) (inline_call E' E) xs"
      using call by(rule bisim_inline_call)(simp add: fv)
    moreover from fv_inline_call[of e1 e] fv fin 
    have "fv (inline_call e1 e) = {}" by auto
    moreover from fin have "\<D> (inline_call e1 e) \<lfloor>{}\<rfloor>"
      using call D by(rule defass_inline_call)
    moreover have "max_vars ?e2' \<le> max_vars E + max_vars E'" by(rule inline_call_max_vars1)
    with \<open>final E'\<close> length have "max_vars ?e2' \<le> length xs" by(auto elim!: final.cases)
    ultimately have "bisim_list1 (inline_call e1 e, es1') ((?e2', xs), exs')"
      by(rule bisim_list1I) }
  ultimately show ?thesis using e1' \<open>final e1\<close> \<open>final E'\<close> ex2 
    apply(simp del: \<tau>Move0.simps \<tau>Move1.simps)
    apply(rule exI conjI impI|assumption)+
     apply(rule tranclp.r_into_trancl, simp)
    apply blast
    done
qed

lemma sim_move10_into_red0:
  assumes wwf: "wwf_J_prog P"
  and sim: "sim_move10 P t ta e2 e2' e h Map.empty ta' e' h' x'"
  and fv: "fv e = {}"
  shows "if \<tau>move1 P h e2
         then (\<tau>Red0t P t h (e, es) (e', es) \<or> countInitBlock e2' < countInitBlock e2 \<and> e' = e \<and> x' = Map.empty) \<and> ta = \<epsilon> \<and> h = h'
         else \<exists>e'' ta'. \<tau>Red0r P t h (e, es) (e'', es) \<and>
                        (call1 e2 = None \<or> call e = None \<or> e'' = e) \<and>
                        P,t \<turnstile>0 \<langle>e''/es,h\<rangle> -ta'\<rightarrow> \<langle>e'/es,h'\<rangle> \<and>
                        \<not> \<tau>Move0 P h (e'', es) \<and> ta_bisim01 ta' (extTA2J1 (compP1 P) ta)"
proof(cases "\<tau>move1 P h e2")
  case True
  with sim have "\<not> final e2"
    and red: "\<tau>red0t (extTA2J0 P) P t h (e, Map.empty) (e', x') \<or>
              countInitBlock e2' < countInitBlock e2 \<and> e' = e \<and> x' = Map.empty"
    and [simp]: "h' = h" "ta = \<epsilon>" "ta' = \<epsilon>" by(simp_all add: sim_move10_def)
  from red have "\<tau>Red0t P t h (e, es) (e', es) \<or>
                 countInitBlock e2' < countInitBlock e2 \<and> e' = e \<and> x' = Map.empty"
  proof
    assume red: "\<tau>red0t (extTA2J0 P) P t h (e, Map.empty) (e', x')"
    from \<tau>red0t_fv_subset[OF wwf red] \<tau>red0t_dom_lcl[OF wwf red] fv
    have "dom x' \<subseteq> {}" by(auto split: if_split_asm)
    hence "x' = Map.empty" by auto
    with red have "\<tau>red0t (extTA2J0 P) P t h (e, Map.empty) (e', Map.empty)" by simp
    with wwf have "\<tau>Red0t P t h (e, es) (e', es)"
      using fv by(rule \<tau>red0t_into_\<tau>Red0t)
    thus ?thesis ..
  qed simp
  with True show ?thesis by simp
next
  case False
  with sim obtain e'' xs'' where "\<not> final e2"
    and \<tau>red: "\<tau>red0r (extTA2J0 P) P t h (e, Map.empty) (e'', xs'')"
    and red: "extTA2J0 P,P,t \<turnstile> \<langle>e'',(h, xs'')\<rangle> -ta'\<rightarrow> \<langle>e',(h', x')\<rangle>"
    and call: "call1 e2 = None \<or> call e = None \<or> e'' = e"
    and "\<not> \<tau>move0 P h e''" "ta_bisim01 ta' (extTA2J1 (compP1 P) ta)" "no_call P h e''"
    by(auto simp add: sim_move10_def split: if_split_asm)
  from \<tau>red0r_fv_subset[OF wwf \<tau>red] \<tau>red0r_dom_lcl[OF wwf \<tau>red] fv
  have "dom xs'' \<subseteq> {}" by(auto)
  hence "xs'' = Map.empty" by(auto)
  with \<tau>red have "\<tau>red0r (extTA2J0 P) P t h (e, Map.empty) (e'', Map.empty)" by simp
  with wwf have "\<tau>Red0r P t h (e, es) (e'', es)"
    using fv by(rule \<tau>red0r_into_\<tau>Red0r)
  moreover from red \<open>xs'' = Map.empty\<close>
  have "extTA2J0 P,P,t \<turnstile> \<langle>e'',(h, Map.empty)\<rangle> -ta'\<rightarrow> \<langle>e',(h', x')\<rangle>" by simp
  from red0Red[OF this] \<open>no_call P h e''\<close> 
  have "P,t \<turnstile>0 \<langle>e''/es,h\<rangle> -ta'\<rightarrow> \<langle>e'/es,h'\<rangle>" by(simp add: no_call_def)
  moreover from \<open>\<not> \<tau>move0 P h e''\<close> red
  have "\<not> \<tau>Move0 P h (e'', es)" by auto
  ultimately show ?thesis using False \<open>ta_bisim01 ta' (extTA2J1 (compP1 P) ta)\<close> call
    by(simp del: \<tau>Move0.simps) blast
qed

lemma red0_simulates_Red1:
  assumes wf: "wf_J_prog P"
  and red: "False,compP1 P,t \<turnstile>1 \<langle>ex2/exs2, h\<rangle> -ta\<rightarrow> \<langle>ex2'/exs2', h'\<rangle>"
  and bisiml: "bisim_list1 (e, es) (ex2, exs2)"
  shows "\<exists>e' es'. bisim_list1 (e', es') (ex2', exs2') \<and>
                 (if \<tau>Move1 P h (ex2, exs2)
                  then (\<tau>Red0t P t h (e, es) (e', es') \<or> countInitBlock (fst ex2') < countInitBlock (fst ex2) \<and> exs2' = exs2 \<and> e' = e \<and> es' = es) \<and>
                        ta = \<epsilon> \<and> h = h'
                  else \<exists>e'' es'' ta'. \<tau>Red0r P t h (e, es) (e'', es'') \<and>
                                      (call1 (fst ex2) = None \<or> call e = None \<or> e'' = e \<and> es'' = es) \<and>
                                      P,t \<turnstile>0 \<langle>e''/es'', h\<rangle> -ta'\<rightarrow> \<langle>e'/es', h'\<rangle> \<and>
                                      \<not> \<tau>Move0 P h (e'', es'') \<and> ta_bisim01 ta' ta)"
  (is "\<exists>e' es' . _ \<and> ?red e' es'")
using red
proof(cases)
  case (red1Red E xs TA E' xs')
  note red = \<open>False,compP1 P,t \<turnstile>1 \<langle>E,(h, xs)\<rangle> -TA\<rightarrow> \<langle>E',(h', xs')\<rangle>\<close>
    and ex2 = \<open>ex2 = (E, xs)\<close>
    and ex2' = \<open>ex2' = (E', xs')\<close>
    and [simp] = \<open>ta = extTA2J1 (compP1 P) TA\<close> \<open>exs2' = exs2\<close>
  from bisiml ex2 have bisim: "bisim [] e E xs" and fv: "fv e = {}"
    and length: "max_vars E \<le> length xs" and bsl: "bisim_list es exs2"
    and D: "\<D> e \<lfloor>{}\<rfloor>" by(auto elim: bisim_list1_elim)
  from red_simulates_red1_aux[OF wf red, simplified, OF bisim, of Map.empty] fv length D
  obtain TA' e2' x' where red': "sim_move10 P t TA E E' e h Map.empty TA' e2' h' x'"
    and bisim'': "bisim [] e2' E' xs'" and lcl': "x' \<subseteq>\<^sub>m Map.empty" by auto
  from red have "\<not> final E" by auto
  with sim_move10_into_red0[OF wf_prog_wwf_prog[OF wf] red', of es] fv ex2 ex2'
  have red'': "?red e2' es" by fastforce
  moreover {
    note bsl bisim''
    moreover from red' fv have "fv e2' = {}"
      by(fastforce simp add: sim_move10_def split: if_split_asm dest: \<tau>red0r_fv_subset[OF wf_prog_wwf_prog[OF wf]] \<tau>red0t_fv_subset[OF wf_prog_wwf_prog[OF wf]] red_fv_subset[OF wf_prog_wwf_prog[OF wf]])
    moreover from red' have "dom x' \<subseteq> dom (Map.empty) \<union> fv e"
      unfolding sim_move10_def
      apply(auto split: if_split_asm del: subsetI dest: \<tau>red0r_dom_lcl[OF wf_prog_wwf_prog[OF wf]] \<tau>red0t_dom_lcl[OF wf_prog_wwf_prog[OF wf]])
      apply(frule_tac [1-2] \<tau>red0r_fv_subset[OF wf_prog_wwf_prog[OF wf]])
      apply(auto dest!: \<tau>red0r_dom_lcl[OF wf_prog_wwf_prog[OF wf]] red_dom_lcl del: subsetI, blast+)
      done
    with fv have "dom x' \<subseteq> {}" by(auto)
    hence "x' = Map.empty" by(auto)
    with D red' have "\<D> e2' \<lfloor>{}\<rfloor>"
      by(auto dest!: sim_move10_preserves_defass[OF wf] split: if_split_asm)
    moreover from red have "length xs' = length xs" by(auto dest: red1_preserves_len)
    with red1_max_vars[OF red] length
    have "max_vars E' \<le> length xs'" by simp
    ultimately have "bisim_list1 (e2', es) ((E', xs'), exs2)"
      by(rule bisim_list1I) }
  ultimately show ?thesis using ex2'
    by(clarsimp split: if_split_asm)(rule exI conjI|assumption|simp)+
next
  case (red1Call E a M vs U Ts T body D xs)
  note [simp] = \<open>ex2 = (E, xs)\<close> \<open>h' = h\<close> \<open>ta = \<epsilon>\<close>
    and ex2' = \<open>ex2' = (blocks1 0 (Class D#Ts) body, Addr a # vs @ replicate (max_vars body) undefined_value)\<close>
    and exs' = \<open>exs2' = (E, xs) # exs2\<close>
    and call = \<open>call1 E = \<lfloor>(a, M, vs)\<rfloor>\<close> and ha = \<open>typeof_addr h a = \<lfloor>U\<rfloor>\<close>
    and sees = \<open>compP1 P \<turnstile> class_type_of U sees M: Ts\<rightarrow>T = \<lfloor>body\<rfloor> in D\<close>
    and len = \<open>length vs = length Ts\<close>
  let ?e2' = "blocks1 0 (Class D#Ts) body"
  let ?xs2' = "Addr a # vs @ replicate (max_vars body) undefined_value"
  from bisiml have bisim: "bisim [] e E xs" and fv: "fv e = {}"
    and length: "max_vars E \<le> length xs" and bsl: "bisim_list es exs2"
    and D: "\<D> e \<lfloor>{}\<rfloor>" by(auto elim: bisim_list1_elim)

  from bisim \<open>call1 E = \<lfloor>(a, M, vs)\<rfloor>\<close>
  have "call e = \<lfloor>(a, M, vs)\<rfloor>" by(rule bisim_call1_Some_call)
  moreover note ha
  moreover from \<open>compP1 P \<turnstile> class_type_of U sees M: Ts\<rightarrow>T = \<lfloor>body\<rfloor> in D\<close>
  obtain pns Jbody where sees': "P \<turnstile> class_type_of U sees M: Ts\<rightarrow>T = \<lfloor>(pns, Jbody)\<rfloor> in D"
    and body: "body = compE1 (this # pns) Jbody"
    by(auto dest: sees_method_compPD)
  let ?e' = "blocks (this # pns) (Class D # Ts) (Addr a # vs) Jbody"
  note sees' moreover from wf sees' have "length Ts = length pns"
    by(auto dest!: sees_wf_mdecl simp add: wf_mdecl_def)
  with len have "length vs = length pns" "length Ts = length pns" by simp_all
  ultimately have red': "P,t \<turnstile>0 \<langle>e/es, h\<rangle> -\<epsilon>\<rightarrow> \<langle>?e'/e#es, h\<rangle>" by(rule red0Call)
  moreover from \<open>call e = \<lfloor>(a, M, vs)\<rfloor>\<close> ha sees'
  have "\<tau>Move0 P h (e, es)"
    by(fastforce simp add: synthesized_call_def dest: \<tau>move0_callD[where P=P and h=h] sees_method_fun)
  ultimately have "\<tau>Red0t P t h (e, es) (?e', e#es)" by auto
  moreover
  from bsl bisim fv D length \<open>call e = \<lfloor>(a, M, vs)\<rfloor>\<close> \<open>call1 E = \<lfloor>(a, M, vs)\<rfloor>\<close>
  have "bisim_list (e # es) ((E, xs) # exs2)" by(rule bisim_list.intros)
  hence "bisim_list1 (?e', e # es) (ex2', (E, xs) # exs2)" unfolding ex2'
  proof(rule bisim_list1I)
    from wf_prog_wwf_prog[OF wf] sees'
    have "wf_mdecl wwf_J_mdecl P D (M,Ts,T,\<lfloor>(pns,Jbody)\<rfloor>)" by(rule sees_wf_mdecl)
    hence "fv Jbody \<subseteq> set pns \<union> {this}" by(auto simp add: wf_mdecl_def)
    moreover from sees' have "\<not> contains_insync Jbody"
      by(auto dest!: sees_wf_mdecl[OF wf] WT_expr_locks simp add: wf_mdecl_def contains_insync_conv)
    ultimately have "bisim ([] @ this # pns) Jbody (compE1 ([] @ this # pns) Jbody) ?xs2'"
      by -(rule compE1_bisim, auto)
    with \<open>length vs = length Ts\<close> \<open>length Ts = length pns\<close> body
    have "bisim [] ?e' (blocks1 (length ([] :: vname list)) (Class D # Ts) body) ?xs2'"
      by -(rule blocks_bisim, auto simp add: nth_append nth_Cons')
    thus "bisim [] ?e' ?e2' ?xs2'" by simp
    from \<open>length vs = length Ts\<close> \<open>length Ts = length pns\<close> \<open>fv Jbody \<subseteq> set pns \<union> {this}\<close>
    show "fv ?e' = {}" by auto
    from wf sees'
    have "wf_mdecl wf_J_mdecl P D (M,Ts,T,\<lfloor>(pns,Jbody)\<rfloor>)" by(rule sees_wf_mdecl)
    hence "\<D> Jbody \<lfloor>set pns \<union> {this}\<rfloor>" by(auto simp add: wf_mdecl_def)
    with \<open>length vs = length Ts\<close> \<open>length Ts = length pns\<close>
    have "\<D> (blocks pns Ts vs Jbody) \<lfloor>dom [this \<mapsto> Addr a]\<rfloor>" by(auto)
    thus "\<D> ?e' \<lfloor>{}\<rfloor>" by simp
    from len show "max_vars ?e2' \<le> length ?xs2'" by(simp add: blocks1_max_vars)
  qed
  moreover have "\<tau>Move1 P h (ex2, exs2)" using ha \<open>call1 E = \<lfloor>(a, M, vs)\<rfloor>\<close> sees'
    by(auto simp add: synthesized_call_def \<tau>external'_def dest!: \<tau>move1_not_call1[where P=P and h=h] dest: sees_method_fun)
  ultimately show ?thesis using exs'
    by(simp del: \<tau>Move1.simps \<tau>Move0.simps)(rule exI conjI rtranclp.rtrancl_refl|assumption)+
next
  case (red1Return E' x' E x)
  note [simp] = \<open>h' = h\<close> \<open>ta = \<epsilon>\<close>
    and ex2 = \<open>ex2 = (E', x')\<close> and exs2 = \<open>exs2 = (E, x) # exs2'\<close>
    and ex2' = \<open>ex2' = (inline_call E' E, x)\<close>
    and fin = \<open>final E'\<close>
  from bisiml ex2 exs2 obtain e' es' aMvs where es: "es = e' # es'"
    and bsl: "bisim_list es' exs2'"
    and bisim: "bisim [] e E' x'"
    and bisim': "bisim [] e' E x"
    and fv: "fv e' = {}"
    and length: "max_vars E \<le> length x"
    and D: "\<D> e' \<lfloor>{}\<rfloor>"
    and call: "call e' = \<lfloor>aMvs\<rfloor>"
    and call1: "call1 E = \<lfloor>aMvs\<rfloor>"
    by(fastforce elim!: bisim_list1_elim)
  
  from \<open>final E'\<close> bisim have fin': "final e" by(auto)
  hence "P,t \<turnstile>0 \<langle>e/e' # es',h\<rangle> -\<epsilon>\<rightarrow> \<langle>inline_call e e'/es',h\<rangle>" by(rule red0Return)
  moreover from bisim fin' bisim' call
  have "bisim [] (inline_call e e') (inline_call E' E) x"
    by(rule bisim_inline_call)(simp add: fv)
  with bsl have "bisim_list1 (inline_call e e', es') (ex2', exs2')" unfolding ex2'
  proof(rule bisim_list1I)
    from fin' fv_inline_call[of e e'] fv show "fv (inline_call e e') = {}" by auto
    from fin' show "\<D> (inline_call e e') \<lfloor>{}\<rfloor>" using call D by(rule defass_inline_call)
    
    from call1_imp_call[OF call1]
    have "max_vars (inline_call E' E) \<le> max_vars E + max_vars E'"
      by(rule inline_call_max_vars)
    with fin length show "max_vars (inline_call E' E) \<le> length x" by(auto elim!: final.cases)
  qed
  moreover have "\<tau>Move1 P h (ex2, exs2) = \<tau>Move0 P h (e, es)" using ex2 call1 call fin fin' by(auto)
  ultimately show ?thesis using es
    by(simp del: \<tau>Move1.simps \<tau>Move0.simps) blast
qed

end

sublocale J0_J1_heap_base < red0_Red1': FWdelay_bisimulation_base
  final_expr0
  "mred0 P"
  final_expr1
  "mred1' (compP1 P)"
  convert_RA
  "\<lambda>t. bisim_red0_Red1" 
  bisim_wait01
  "\<tau>MOVE0 P"
  "\<tau>MOVE1 (compP1 P)"
  for P
.

context J0_J1_heap_base begin

lemma delay_bisimulation_red0_Red1: 
  assumes wf: "wf_J_prog P"
  shows "delay_bisimulation_measure (mred0 P t) (mred1' (compP1 P) t) bisim_red0_Red1 (ta_bisim (\<lambda>t. bisim_red0_Red1)) (\<tau>MOVE0 P) (\<tau>MOVE1 (compP1 P)) (\<lambda>es es'. False) (\<lambda>(((e', xs'), exs'), h') (((e, xs), exs), h). countInitBlock e'< countInitBlock e)"
  (is "delay_bisimulation_measure _ _ _ _ _ _ ?\<mu>1 ?\<mu>2")
proof(unfold_locales)
  fix s1 s2 s1'
  assume "bisim_red0_Red1 s1 s2" "red0_mthr.silent_move P t s1 s1'"
  moreover obtain ex1 exs1 h1 where s1: "s1 = ((ex1, exs1), h1)" by(cases s1, auto)
  moreover obtain ex1' exs1' h1' where s1': "s1' = ((ex1', exs1'), h1')" by(cases s1', auto)
  moreover obtain ex2 exs2 h2 where s2: "s2 = ((ex2, exs2), h2)" by(cases s2, auto)
  ultimately have bisim: "bisim_list1 (ex1, exs1) (ex2, exs2)"
    and heap: "h1 = h2"
    and red: "P,t \<turnstile>0 \<langle>ex1/exs1,h1\<rangle> -\<epsilon>\<rightarrow> \<langle>ex1'/exs1',h1'\<rangle>"
    and \<tau>: "\<tau>Move0 P h1 (ex1, exs1)"
    by(auto simp add: bisim_red0_Red1_def red0_mthr.silent_move_iff)
  from Red1_simulates_red0[OF wf red bisim] \<tau>
  obtain ex2'' exs2'' where bisim': "bisim_list1 (ex1', exs1') (ex2'', exs2'')" 
    and red': "\<tau>Red1't (compP1 P) t h1 (ex2, exs2) (ex2'', exs2'')"
    and [simp]: "h1' = h1" by auto
  from \<tau>Red1't_into_Red1'_\<tau>mthr_silent_movet[OF red'] bisim' heap
  have "\<exists>s2'. Red1_mthr.silent_movet False (compP1 P) t s2 s2' \<and> bisim_red0_Red1 s1' s2'"
    unfolding s2 s1' by(auto simp add: bisim_red0_Red1_def)
  thus "bisim_red0_Red1 s1' s2 \<and> ?\<mu>1^++ s1' s1 \<or> (\<exists>s2'. Red1_mthr.silent_movet False (compP1 P) t s2 s2' \<and> bisim_red0_Red1 s1' s2')" ..
next
  fix s1 s2 s2'
  assume "bisim_red0_Red1 s1 s2" "Red1_mthr.silent_move False (compP1 P) t s2 s2'"
  moreover obtain ex1 exs1 h1 where s1: "s1 = ((ex1, exs1), h1)" by(cases s1, auto)
  moreover obtain ex2 exs2 h2 where s2: "s2 = ((ex2, exs2), h2)" by(cases s2, auto)
  moreover obtain ex2' exs2' h2' where s2': "s2' = ((ex2', exs2'), h2')" by(cases s2', auto)
  ultimately have bisim: "bisim_list1 (ex1, exs1) (ex2, exs2)"
    and heap: "h1 = h2"
    and red: "False,compP1 P,t \<turnstile>1 \<langle>ex2/exs2,h2\<rangle> -\<epsilon>\<rightarrow> \<langle>ex2'/exs2',h2'\<rangle>"
    and \<tau>: "\<tau>Move1 P h2 (ex2, exs2)"
    by(fastforce simp add: bisim_red0_Red1_def Red1_mthr.silent_move_iff)+
  from red0_simulates_Red1[OF wf red bisim] \<tau>
  obtain e' es' where bisim': "bisim_list1 (e', es') (ex2', exs2')"
    and red': "\<tau>Red0t P t h2 (ex1, exs1) (e', es') \<or> 
               countInitBlock (fst ex2') < countInitBlock (fst ex2) \<and> exs2' = exs2 \<and> e' = ex1 \<and> es' = exs1"
    and [simp]: "h2' = h2" by auto
  from red'
  show "bisim_red0_Red1 s1 s2' \<and> ?\<mu>2^++ s2' s2 \<or> (\<exists>s1'. red0_mthr.silent_movet P t s1 s1' \<and> bisim_red0_Red1 s1' s2')"
    (is "?refl \<or> ?step")
  proof
    assume "\<tau>Red0t P t h2 (ex1, exs1) (e', es')"
    from \<tau>Red0t_into_red0_\<tau>mthr_silent_movet[OF this] bisim' heap
    have ?step unfolding s1 s2' by(auto simp add: bisim_red0_Red1_def)
    thus ?thesis ..
  next
    assume "countInitBlock (fst ex2') < countInitBlock (fst ex2) \<and> exs2' = exs2 \<and> e' = ex1 \<and> es' = exs1"
    hence ?refl using bisim' heap unfolding s1 s2' s2
      by (auto simp add: bisim_red0_Red1_def split_beta)
    thus ?thesis ..
  qed
next
  fix s1 s2 ta1 s1'
  assume "bisim_red0_Red1 s1 s2"  and "mred0 P t s1 ta1 s1'" and \<tau>: "\<not> \<tau>MOVE0 P s1 ta1 s1'"
  moreover obtain ex1 exs1 h1 where s1: "s1 = ((ex1, exs1), h1)" by(cases s1, auto)
  moreover obtain ex1' exs1' h1' where s1': "s1' = ((ex1', exs1'), h1')" by(cases s1', auto)
  moreover obtain ex2 exs2 h2 where s2: "s2 = ((ex2, exs2), h2)" by(cases s2, auto)
  ultimately have heap: "h2 = h1"
    and bisim: "bisim_list1 (ex1, exs1) (ex2, exs2)"
    and red: "P,t \<turnstile>0 \<langle>ex1/exs1,h1\<rangle> -ta1\<rightarrow> \<langle>ex1'/exs1',h1'\<rangle>"
    by(auto simp add: bisim_red0_Red1_def)
  from \<tau> have "\<not> \<tau>Move0 P h1 (ex1, exs1)" unfolding s1
    using red by(auto elim!: red0.cases dest: red_\<tau>_taD[where extTA="extTA2J0 P", OF extTA2J0_\<epsilon>])
  with Red1_simulates_red0[OF wf red bisim]
  obtain ex2'' exs2'' ex2' exs2' ta'
    where bisim': "bisim_list1 (ex1', exs1') (ex2'', exs2'')"
    and red': "\<tau>Red1'r (compP1 P) t h1 (ex2, exs2) (ex2', exs2')"
    and red'': "False,compP1 P,t \<turnstile>1 \<langle>ex2'/exs2',h1\<rangle> -ta'\<rightarrow> \<langle>ex2''/exs2'',h1'\<rangle>"
    and \<tau>': "\<not> \<tau>Move1 P h1 (ex2', exs2')"
    and ta: "ta_bisim01 ta1 ta'" by fastforce
  from red'' have "mred1' (compP1 P) t ((ex2', exs2'), h1) ta' ((ex2'', exs2''), h1')" by auto
  moreover from \<tau>' have "\<not> \<tau>MOVE1 (compP1 P) ((ex2', exs2'), h1) ta' ((ex2'', exs2''), h1')" by simp
  moreover from red' have "Red1_mthr.silent_moves False (compP1 P) t s2 ((ex2', exs2'), h1)"
    unfolding s2 heap by(rule \<tau>Red1'r_into_Red1'_\<tau>mthr_silent_moves)
  moreover from bisim' have "bisim_red0_Red1 ((ex1', exs1'), h1') ((ex2'', exs2''), h1')"
    by(auto simp add: bisim_red0_Red1_def)
  ultimately
  show "\<exists>s2' s2'' ta2. Red1_mthr.silent_moves False (compP1 P) t s2 s2' \<and> mred1' (compP1 P) t s2' ta2 s2'' \<and>
             \<not> \<tau>MOVE1 (compP1 P) s2' ta2 s2'' \<and> bisim_red0_Red1 s1' s2'' \<and> ta_bisim01 ta1 ta2"
    using ta unfolding s1' by blast
next
  fix s1 s2 ta2 s2'
  assume "bisim_red0_Red1 s1 s2"  and "mred1' (compP1 P) t s2 ta2 s2'" and \<tau>: "\<not> \<tau>MOVE1 (compP1 P) s2 ta2 s2'"
  moreover obtain ex1 exs1 h1 where s1: "s1 = ((ex1, exs1), h1)" by(cases s1, auto)
  moreover obtain ex2 exs2 h2 where s2: "s2 = ((ex2, exs2), h2)" by(cases s2, auto)
  moreover obtain ex2' exs2' h2' where s2': "s2' = ((ex2', exs2'), h2')" by(cases s2', auto)
  ultimately have heap: "h2 = h1"
    and bisim: "bisim_list1 (ex1, exs1) (ex2, exs2)"
    and red: "False,compP1 P,t \<turnstile>1 \<langle>ex2/exs2,h1\<rangle> -ta2\<rightarrow> \<langle>ex2'/exs2',h2'\<rangle>"
    by(auto simp add: bisim_red0_Red1_def)
  from \<tau> heap have "\<not> \<tau>Move1 P h2 (ex2, exs2)" unfolding s2
    using red by(fastforce elim!: Red1.cases dest: red1_\<tau>_taD)
  with red0_simulates_Red1[OF wf red bisim]
  obtain e' es' e'' es'' ta'
    where bisim': "bisim_list1 (e', es') (ex2', exs2')"
    and red': "\<tau>Red0r P t h1 (ex1, exs1) (e'', es'')"
    and red'': "P,t \<turnstile>0 \<langle>e''/es'',h1\<rangle> -ta'\<rightarrow> \<langle>e'/es',h2'\<rangle>"
    and \<tau>': "\<not> \<tau>Move0 P h1 (e'', es'')"
    and ta: "ta_bisim01 ta' ta2" using heap by fastforce
  from red'' have "mred0 P t ((e'', es''), h1) ta' ((e', es'), h2')" by auto
  moreover from red' have "red0_mthr.silent_moves P t ((ex1, exs1), h1) ((e'', es''), h1)"
    by(rule \<tau>Red0r_into_red0_\<tau>mthr_silent_moves)
  moreover from \<tau>' have "\<not> \<tau>MOVE0 P ((e'', es''), h1) ta' ((e', es'), h2')" by simp
  moreover from bisim' have "bisim_red0_Red1 ((e', es'), h2') ((ex2', exs2'), h2')"
    by(auto simp add: bisim_red0_Red1_def)
  ultimately
  show "\<exists>s1' s1'' ta1. red0_mthr.silent_moves P t s1 s1' \<and>
             mred0 P t s1' ta1 s1'' \<and> \<not> \<tau>MOVE0 P s1' ta1 s1'' \<and>
             bisim_red0_Red1 s1'' s2' \<and> ta_bisim01 ta1 ta2"
    using ta unfolding s1 s2' by blast
next
  show "wfP ?\<mu>1" by auto
next
  have "wf (measure countInitBlock)" ..
  hence "wf (inv_image (measure countInitBlock) (\<lambda>(((e', xs'), exs'), h'). e'))" ..
  also have "inv_image (measure countInitBlock) (\<lambda>(((e', xs'), exs'), h'). e') = {(s2', s2). ?\<mu>2 s2' s2}"
    by(simp add: inv_image_def split_beta)
  finally show "wfP ?\<mu>2" by(simp add: wfP_def)
qed

lemma delay_bisimulation_diverge_red0_Red1: 
  assumes "wf_J_prog P"
  shows "delay_bisimulation_diverge (mred0 P t) (mred1' (compP1 P) t) bisim_red0_Red1 (ta_bisim (\<lambda>t. bisim_red0_Red1)) (\<tau>MOVE0 P) (\<tau>MOVE1 (compP1 P))"
proof -
  interpret delay_bisimulation_measure
    "mred0 P t" "mred1' (compP1 P) t" "bisim_red0_Red1" "ta_bisim (\<lambda>t. bisim_red0_Red1)" "\<tau>MOVE0 P" "\<tau>MOVE1 (compP1 P)"
    "\<lambda>es es'. False" "\<lambda>(((e', xs'), exs'), h') (((e, xs), exs), h). countInitBlock e'< countInitBlock e"
    using assms by(rule delay_bisimulation_red0_Red1)
  show ?thesis by unfold_locales
qed

lemma red0_Red1'_FWweak_bisim:
  assumes wf: "wf_J_prog P"
  shows "FWdelay_bisimulation_diverge final_expr0 (mred0 P) final_expr1 (mred1' (compP1 P))
           (\<lambda>t. bisim_red0_Red1) bisim_wait01 (\<tau>MOVE0 P) (\<tau>MOVE1 (compP1 P))"
proof -
  interpret delay_bisimulation_diverge
    "mred0 P t"
    "mred1' (compP1 P) t" 
    bisim_red0_Red1 
    "ta_bisim (\<lambda>t. bisim_red0_Red1)" "\<tau>MOVE0 P" "\<tau>MOVE1 (compP1 P)"
    for t
    using wf by(rule delay_bisimulation_diverge_red0_Red1)
  show ?thesis
  proof
    fix t and s1 and s2 :: "(('addr expr1 \<times> 'addr locals1) \<times> ('addr expr1 \<times> 'addr locals1) list) \<times> 'heap"
    assume "bisim_red0_Red1 s1 s2" "(\<lambda>(x1, m). final_expr0 x1) s1"
    moreover hence "(\<lambda>(x2, m). final_expr1 x2) s2"
      by(cases s1)(cases s2,auto simp add: bisim_red0_Red1_def final_iff elim!: bisim_list1_elim elim: bisim_list.cases)
    ultimately show "\<exists>s2'. Red1_mthr.silent_moves False (compP1 P) t s2 s2' \<and> bisim_red0_Red1 s1 s2' \<and> (\<lambda>(x2, m). final_expr1 x2) s2'"
      by blast
  next
    fix t s1 and s2 :: "(('addr expr1 \<times> 'addr locals1) \<times> ('addr expr1 \<times> 'addr locals1) list) \<times> 'heap"
    assume "bisim_red0_Red1 s1 s2" "(\<lambda>(x2, m). final_expr1 x2) s2"
    moreover hence "(\<lambda>(x1, m). final_expr0 x1) s1"
      by(cases s1)(cases s2,auto simp add: bisim_red0_Red1_def final_iff elim!: bisim_list1_elim elim: bisim_list.cases)
    ultimately show "\<exists>s1'. red0_mthr.silent_moves P t s1 s1' \<and> bisim_red0_Red1 s1' s2 \<and> (\<lambda>(x1, m). final_expr0 x1) s1'"
      by blast
  next
    fix t' x m1 x' m2 t x1 x2 x1' ta1 x1'' m1' x2' ta2 x2'' m2'
    assume b: "bisim_red0_Red1 (x, m1) (x', m2)"
      and bo: "bisim_red0_Red1 (x1, m1) (x2, m2)"
      and \<tau>red1: "red0_mthr.silent_moves P t (x1, m1) (x1', m1)"
      and red1: "mred0 P t (x1', m1) ta1 (x1'', m1')"
      and \<tau>1: "\<not> \<tau>MOVE0 P (x1', m1) ta1 (x1'', m1')"
      and \<tau>red2: "Red1_mthr.silent_moves False (compP1 P) t (x2, m2) (x2', m2)"
      and red2: "mred1' (compP1 P) t (x2', m2) ta2 (x2'', m2')"
      and bo': "bisim_red0_Red1 (x1'', m1') (x2'', m2')"
      and tb: "ta_bisim (\<lambda>t. bisim_red0_Red1) ta1 ta2"
    from b have "m1 = m2" by(auto simp add: bisim_red0_Red1_def split_beta)
    moreover from bo' have "m1' = m2'" by(auto simp add: bisim_red0_Red1_def split_beta)
    ultimately show "bisim_red0_Red1 (x, m1') (x', m2')" using b
      by(auto simp add: bisim_red0_Red1_def split_beta)
  next
    fix t x1 m1 x2 m2 x1' ta1 x1'' m1' x2' ta2 x2'' m2' w
    assume "bisim_red0_Red1 (x1, m1) (x2, m2)"
      and "red0_mthr.silent_moves P t (x1, m1) (x1', m1)"
      and red0: "mred0 P t (x1', m1) ta1 (x1'', m1')"
      and "\<not> \<tau>MOVE0 P (x1', m1) ta1 (x1'', m1')"
      and "Red1_mthr.silent_moves False (compP1 P) t (x2, m2) (x2', m2)"
      and red1: "mred1' (compP1 P) t (x2', m2) ta2 (x2'', m2')"
      and "\<not> \<tau>MOVE1 (compP1 P) (x2', m2) ta2 (x2'', m2')"
      and "bisim_red0_Red1 (x1'', m1') (x2'', m2')"
      and "ta_bisim01 ta1 ta2"
      and Suspend: "Suspend w \<in> set \<lbrace>ta1\<rbrace>\<^bsub>w\<^esub>" "Suspend w \<in> set \<lbrace>ta2\<rbrace>\<^bsub>w\<^esub>"
    from red0 red1 Suspend show "bisim_wait01 x1'' x2''"
      by(cases x2')(cases x2'', auto dest: Red_Suspend_is_call Red1_Suspend_is_call simp add: split_beta bisim_wait01_def is_call_def)
  next
    fix t x1 m1 x2 m2 ta1 x1' m1'
    assume "bisim_red0_Red1 (x1, m1) (x2, m2)"
      and "bisim_wait01 x1 x2"
      and "mred0 P t (x1, m1) ta1 (x1', m1')"
      and wakeup: "Notified \<in> set \<lbrace>ta1\<rbrace>\<^bsub>w\<^esub> \<or> WokenUp \<in> set \<lbrace>ta1\<rbrace>\<^bsub>w\<^esub>"
    moreover obtain e0 es0 where [simp]: "x1 = (e0, es0)" by(cases x1)
    moreover obtain e0' es0' where [simp]: "x1' = (e0', es0')" by(cases x1')
    moreover obtain e1 xs1 exs1 where [simp]: "x2 = ((e1, xs1), exs1)" by(cases x2) auto
    ultimately have bisim: "bisim_list1 (e0, es0) ((e1, xs1), exs1)"
      and m1: "m2 = m1"
      and call: "call e0 \<noteq> None" "call1 e1 \<noteq> None"
      and red: "P,t \<turnstile>0 \<langle>e0/es0, m1\<rangle> -ta1\<rightarrow> \<langle>e0'/es0', m1'\<rangle>"
      by(auto simp add: bisim_wait01_def bisim_red0_Red1_def)
    from red wakeup have "\<not> \<tau>Move0 P m1 (e0, es0)"
      by(auto elim!: red0.cases dest: red_\<tau>_taD[where extTA="extTA2J0 P", simplified])
    with Red1_simulates_red0[OF wf red bisim] call m1
    show "\<exists>ta2 x2' m2'. mred1' (compP1 P) t (x2, m2) ta2 (x2', m2') \<and> bisim_red0_Red1 (x1', m1') (x2', m2') \<and> ta_bisim01 ta1 ta2"
      by(auto simp add: bisim_red0_Red1_def)
  next
    fix t x1 m1 x2 m2 ta2 x2' m2'
    assume "bisim_red0_Red1 (x1, m1) (x2, m2)"
      and "bisim_wait01 x1 x2" 
      and "mred1' (compP1 P) t (x2, m2) ta2 (x2', m2')"
      and wakeup: "Notified \<in> set \<lbrace>ta2\<rbrace>\<^bsub>w\<^esub> \<or> WokenUp \<in> set \<lbrace>ta2\<rbrace>\<^bsub>w\<^esub>"
    moreover obtain e0 es0 where [simp]: "x1 = (e0, es0)" by(cases x1)
    moreover obtain e1 xs1 exs1 where [simp]: "x2 = ((e1, xs1), exs1)" by(cases x2) auto
    moreover obtain e1' xs1' exs1' where [simp]: "x2' = ((e1', xs1'), exs1')" by(cases x2') auto
    ultimately have bisim: "bisim_list1 (e0, es0) ((e1, xs1), exs1)"
      and m1: "m2 = m1"
      and call: "call e0 \<noteq> None" "call1 e1 \<noteq> None"
      and red: "False,compP1 P,t \<turnstile>1 \<langle>(e1, xs1)/exs1, m1\<rangle> -ta2\<rightarrow> \<langle>(e1', xs1')/exs1', m2'\<rangle>"
      by(auto simp add: bisim_wait01_def bisim_red0_Red1_def)
    from red wakeup have "\<not> \<tau>Move1 P m1 ((e1, xs1), exs1)"
      by(auto elim!: Red1.cases dest: red1_\<tau>_taD)
    with red0_simulates_Red1[OF wf red bisim] m1 call
    show "\<exists>ta1 x1' m1'. mred0 P t (x1, m1) ta1 (x1', m1') \<and> bisim_red0_Red1 (x1', m1') (x2', m2') \<and> ta_bisim01 ta1 ta2"
      by(auto simp add: bisim_red0_Red1_def)
  next
    show "(\<exists>x. final_expr0 x) \<longleftrightarrow> (\<exists>x. final_expr1 x)"
      by(auto simp add: split_paired_Ex final_iff)
  qed
qed

lemma bisim_J0_J1_start:
  assumes wf: "wf_J_prog P"
  and start: "wf_start_state P C M vs"
  shows "red0_Red1'.mbisim (J0_start_state P C M vs) (J1_start_state (compP1 P) C M vs)"
proof -
  from start obtain Ts T pns body D
    where sees: "P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>(pns,body)\<rfloor> in D"
    and conf: "P,start_heap \<turnstile> vs [:\<le>] Ts"
    by cases auto
  from conf have vs: "length vs = length Ts" by(rule list_all2_lengthD)
  from sees_wf_mdecl[OF wf_prog_wwf_prog[OF wf] sees]
  have fvbody: "fv body \<subseteq> {this} \<union> set pns" and len: "length pns = length Ts"
    by(auto simp add: wf_mdecl_def)
  with vs have fv: "fv (blocks pns Ts vs body) \<subseteq> {this}" by auto
  have wfCM: "wf_J_mdecl P D (M, Ts, T, pns, body)"
    using sees_wf_mdecl[OF wf sees] by(auto simp add: wf_mdecl_def)
  then obtain T' where wtbody: "P,[this # pns [\<mapsto>] Class D # Ts] \<turnstile> body :: T'" by auto
  hence elbody: "expr_locks body = (\<lambda>l. 0)" by(rule WT_expr_locks)
  hence cisbody: "\<not> contains_insync body" by(auto simp add: contains_insync_conv)
  from wfCM len vs have dabody: "\<D> (blocks pns Ts vs body) \<lfloor>{this}\<rfloor>" by auto
  from sees have sees1: "compP1 P \<turnstile> C sees M:Ts\<rightarrow>T = \<lfloor>compE1 (this # pns) body\<rfloor> in D"
    by(auto dest: sees_method_compP[where f="(\<lambda>C M Ts T (pns, body). compE1 (this # pns) body)"])

  let ?e = "blocks1 0 (Class C#Ts) (compE1 (this # pns) body)"
  let ?xs = "Null # vs @ replicate (max_vars body) undefined_value"
  from fvbody cisbody len vs
  have "bisim [] (blocks (this # pns) (Class D # Ts) (Null # vs) body) (blocks1 (length ([] :: vname list)) (Class D # Ts) (compE1 (this # pns) body)) ?xs"
    by-(rule blocks_bisim,(fastforce simp add: nth_Cons' nth_append)+)
  with fv dabody len vs elbody sees sees1
  show ?thesis unfolding start_state_def
    by(auto intro!: red0_Red1'.mbisimI split: if_split_asm)(auto simp add: bisim_red0_Red1_def blocks1_max_vars intro!: bisim_list.intros bisim_list1I wset_thread_okI)
qed

end

end
