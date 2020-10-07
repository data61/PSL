(*  Title:      JinjaThreads/Compiler/Correctness2.thy
    Author:     Andreas Lochbihler
*)

section \<open>Correctness of Stage 2: The multithreaded setting\<close>

theory Correctness2
imports
  J1JVM
  JVMJ1
  "../BV/BVProgressThreaded"
begin

declare Listn.lesub_list_impl_same_size[simp del]

context J1_JVM_heap_conf_base begin

lemma bisim1_list1_has_methodD: "bisim1_list1 t h ex exs xcp ((stk, loc, C, M, pc) # frs) \<Longrightarrow> P \<turnstile> C has M"
by(fastforce elim!: bisim1_list1.cases intro: has_methodI)

end

declare compP_has_method [simp]

sublocale J1_JVM_heap_conf_base < Red1_exec: 
  delay_bisimulation_base "mred1 P t" "mexec (compP2 P) t" "wbisim1 t" "ta_bisim wbisim1" "\<tau>MOVE1 P" "\<tau>MOVE2 (compP2 P)" 
  for t
.

sublocale J1_JVM_heap_conf_base < Red1_execd: delay_bisimulation_base
  "mred1 P t"
  "mexecd (compP2 P) t"
  "wbisim1 t"
  "ta_bisim wbisim1" 
  "\<tau>MOVE1 P"
  "\<tau>MOVE2 (compP2 P)" 
  for t
.

context JVM_heap_base begin

lemma \<tau>exec_1_d_silent_move:
  "\<tau>exec_1_d P t (xcp, h, frs) (xcp', h', frs')
  \<Longrightarrow> \<tau>trsys.silent_move (mexecd P t) (\<tau>MOVE2 P) ((xcp, frs), h) ((xcp', frs'), h')"
apply(rule \<tau>trsys.silent_move.intros)
apply auto
apply(rule exec_1_d_NormalI)
apply(auto simp add: exec_1_iff exec_d_def)
done

lemma silent_move_\<tau>exec_1_d:
  "\<tau>trsys.silent_move (mexecd P t) (\<tau>MOVE2 P) ((xcp, frs), h) ((xcp', frs'), h')
  \<Longrightarrow> \<tau>exec_1_d P t (xcp, h, frs) (xcp', h', frs')"
apply(erule \<tau>trsys.silent_move.cases)
apply clarsimp
apply(erule jvmd_NormalE)
apply(auto simp add: exec_1_iff)
done

lemma \<tau>Exec_1_dr_rtranclpD:
  "\<tau>Exec_1_dr P t (xcp, h, frs) (xcp', h', frs')
  \<Longrightarrow> \<tau>trsys.silent_moves (mexecd P t) (\<tau>MOVE2 P) ((xcp, frs), h) ((xcp', frs'), h')"
by(induct rule: rtranclp_induct3)(blast intro: rtranclp.rtrancl_into_rtrancl \<tau>exec_1_d_silent_move)+

lemma \<tau>Exec_1_dt_tranclpD:
  "\<tau>Exec_1_dt P t (xcp, h, frs) (xcp', h', frs')
  \<Longrightarrow> \<tau>trsys.silent_movet (mexecd P t) (\<tau>MOVE2 P) ((xcp, frs), h) ((xcp', frs'), h')"
by(induct rule: tranclp_induct3)(blast intro: tranclp.trancl_into_trancl \<tau>exec_1_d_silent_move)+

lemma rtranclp_\<tau>Exec_1_dr:
  "\<tau>trsys.silent_moves (mexecd P t) (\<tau>MOVE2 P) ((xcp, frs), h) ((xcp', frs'), h')
  \<Longrightarrow> \<tau>Exec_1_dr P t (xcp, h, frs) (xcp', h', frs')"
by(induct rule: rtranclp_induct[of _ "((ax, ay), az)" "((bx, by), bz)", split_rule, consumes 1])(blast intro: rtranclp.rtrancl_into_rtrancl silent_move_\<tau>exec_1_d)+

lemma tranclp_\<tau>Exec_1_dt:
  "\<tau>trsys.silent_movet (mexecd P t) (\<tau>MOVE2 P) ((xcp, frs), h) ((xcp', frs'), h')
  \<Longrightarrow> \<tau>Exec_1_dt P t (xcp, h, frs) (xcp', h', frs')"
by(induct rule: tranclp_induct[of _ "((ax, ay), az)" "((bx, by), bz)", split_rule, consumes 1])(blast intro: tranclp.trancl_into_trancl silent_move_\<tau>exec_1_d)+

lemma \<tau>Exec_1_dr_conv_rtranclp:
  "\<tau>Exec_1_dr P t (xcp, h, frs) (xcp', h', frs') = 
  \<tau>trsys.silent_moves (mexecd P t) (\<tau>MOVE2 P) ((xcp, frs), h) ((xcp', frs'), h')"
by(blast intro: \<tau>Exec_1_dr_rtranclpD rtranclp_\<tau>Exec_1_dr)

lemma \<tau>Exec_1_dt_conv_tranclp:
  "\<tau>Exec_1_dt P t (xcp, h, frs) (xcp', h', frs') = 
  \<tau>trsys.silent_movet (mexecd P t) (\<tau>MOVE2 P) ((xcp, frs), h) ((xcp', frs'), h')"
by(blast intro: \<tau>Exec_1_dt_tranclpD tranclp_\<tau>Exec_1_dt)

end

context J1_JVM_conf_read begin

lemma Red1_execd_weak_bisim:
  assumes wf: "wf_J1_prog P"
  shows "delay_bisimulation_measure (mred1 P t) (mexecd (compP2 P) t) (wbisim1 t) (ta_bisim wbisim1) (\<tau>MOVE1 P) (\<tau>MOVE2 (compP2 P)) (\<lambda>(((e, xs), exs), h) (((e', xs'), exs'), h'). sim12_size e < sim12_size e') (\<lambda>(xcpfrs, h) (xcpfrs', h). sim21_size (compP2 P) xcpfrs xcpfrs')"
proof
  fix s1 s2 s1'
  assume "wbisim1 t s1 s2" and "\<tau>trsys.silent_move (mred1 P t) (\<tau>MOVE1 P) s1 s1'" 
  moreover obtain e xs exs h where s1: "s1 = (((e, xs), exs), h)" by(cases s1) auto
  moreover obtain e' xs' exs' h1' where s1': "s1' = (((e', xs'), exs'), h1')" by(cases s1') auto
  moreover obtain xcp frs h2 where s2: "s2 = ((xcp, frs), h2)" by(cases s2) auto
  ultimately have [simp]: "h2 = h" and red: "True,P,t \<turnstile>1 \<langle>(e, xs)/exs,h\<rangle> -\<epsilon>\<rightarrow> \<langle>(e', xs')/exs',h1'\<rangle>"
    and \<tau>: "\<tau>Move1 P h ((e, xs), exs)" and bisim: "bisim1_list1 t h (e, xs) exs xcp frs" by(auto)
  from red \<tau> bisim have h1' [simp]: "h1' = h" by(auto dest: \<tau>move1_heap_unchanged elim!: Red1.cases bisim1_list1.cases)
  from exec_1_simulates_Red1_\<tau>[OF wf red[unfolded h1'] bisim \<tau>] obtain xcp' frs'
    where exec: "(if sim12_size e' < sim12_size e then \<tau>Exec_1_dr else \<tau>Exec_1_dt) (compP2 P) t (xcp, h, frs) (xcp', h, frs')"
    and bisim': "bisim1_list1 t h (e', xs') exs' xcp' frs'" by blast
  from exec have "(if (\<lambda>(((e, xs), exs), h) (((e', xs'), exs'), h'). sim12_size e < sim12_size e') (((e', xs'), exs'), h) (((e, xs), exs), h) then \<tau>trsys.silent_moves (mexecd (compP2 P) t) (\<tau>MOVE2 (compP2 P)) else \<tau>trsys.silent_movet (mexecd (compP2 P) t) (\<tau>MOVE2 (compP2 P))) ((xcp, frs), h) ((xcp', frs'), h)"
    by(auto simp add: \<tau>Exec_1_dr_conv_rtranclp \<tau>Exec_1_dt_conv_tranclp)
  thus "wbisim1 t s1' s2 \<and> (\<lambda>(((e, xs), exs), h) (((e', xs'), exs'), h'). sim12_size e < sim12_size e')\<^sup>+\<^sup>+ s1' s1 \<or>
       (\<exists>s2'. (\<tau>trsys.silent_movet (mexecd (compP2 P) t) (\<tau>MOVE2 (compP2 P))) s2 s2' \<and> wbisim1 t s1' s2')"
    using bisim' s1 s1' s2
    by -(rule delay_bisimulation_base.simulation_silent1I', auto split del: if_split)
next
  fix s1 s2 s2'
  assume "wbisim1 t s1 s2" and "\<tau>trsys.silent_move (mexecd (compP2 P) t) (\<tau>MOVE2 (compP2 P)) s2 s2'"
  moreover obtain e xs exs h1 where s1: "s1 = (((e, xs), exs), h1)" by(cases s1) auto
  moreover obtain xcp frs h where s2: "s2 = ((xcp, frs), h)" by(cases s2) auto
  moreover obtain xcp' frs' h2' where s2': "s2' = ((xcp', frs'), h2')" by(cases s2') auto
  ultimately have [simp]: "h1 = h" and exec: "exec_1_d (compP2 P) t (Normal (xcp, h, frs)) \<epsilon> (Normal (xcp', h2', frs'))"
    and \<tau>: "\<tau>Move2 (compP2 P) (xcp, h, frs)" and bisim: "bisim1_list1 t h (e, xs) exs xcp frs" by(auto)
  from \<tau>Red1_simulates_exec_1_\<tau>[OF wf exec bisim \<tau>]
  obtain e' xs' exs' where [simp]: "h2' = h"
    and red: "(if sim21_size (compP2 P) (xcp', frs') (xcp, frs) then \<tau>Red1r else \<tau>Red1t) P t h ((e, xs), exs) ((e', xs'), exs')"
    and bisim': "bisim1_list1 t h (e', xs') exs' xcp' frs'" by blast
  from red have "(if ((\<lambda>(xcpfrs, h) (xcpfrs', h). sim21_size (compP2 P) xcpfrs xcpfrs') ((xcp', frs'), h2') ((xcp, frs), h)) then \<tau>trsys.silent_moves (mred1 P t) (\<tau>MOVE1 P) else \<tau>trsys.silent_movet (mred1 P t) (\<tau>MOVE1 P)) (((e, xs), exs), h) (((e', xs'), exs'), h)"
    by(auto dest: \<tau>Red1r_rtranclpD \<tau>Red1t_tranclpD)
  thus "wbisim1 t s1 s2' \<and> (\<lambda>(xcpfrs, h) (xcpfrs', h). sim21_size (compP2 P) xcpfrs xcpfrs')\<^sup>+\<^sup>+ s2' s2 \<or>
       (\<exists>s1'. \<tau>trsys.silent_movet (mred1 P t) (\<tau>MOVE1 P) s1 s1' \<and> wbisim1 t s1' s2')"
    using bisim' s1 s2 s2'
    by -(rule delay_bisimulation_base.simulation_silent2I', auto split del: if_split)
next
  fix s1 s2 tl1 s1'
  assume "wbisim1 t s1 s2" and "mred1 P t s1 tl1 s1'" and "\<not> \<tau>MOVE1 P s1 tl1 s1'"
  moreover obtain e xs exs h where s1: "s1 = (((e, xs), exs), h)" by(cases s1) auto
  moreover obtain e' xs' exs' h1' where s1': "s1' = (((e', xs'), exs'), h1')" by(cases s1') auto
  moreover obtain xcp frs h2 where s2: "s2 = ((xcp, frs), h2)" by(cases s2) auto
  ultimately have [simp]: "h2 = h"  and red: "True,P,t \<turnstile>1 \<langle>(e, xs)/exs,h\<rangle> -tl1\<rightarrow> \<langle>(e', xs')/exs',h1'\<rangle>"
    and \<tau>: "\<not> \<tau>Move1 P h ((e, xs), exs)" and bisim: "bisim1_list1 t h (e, xs) exs xcp frs"
    by(fastforce elim!: Red1.cases dest: red1_\<tau>_taD)+
  from exec_1_simulates_Red1_not_\<tau>[OF wf red bisim \<tau>] obtain ta' xcp' frs' xcp'' frs''
    where exec1: "\<tau>Exec_1_dr (compP2 P) t (xcp, h, frs) (xcp', h, frs')"
    and exec2: "exec_1_d (compP2 P) t (Normal (xcp', h, frs')) ta' (Normal (xcp'', h1', frs''))"
    and \<tau>': "\<not> \<tau>Move2 (compP2 P) (xcp', h, frs')"
    and bisim': "bisim1_list1 t h1' (e', xs') exs' xcp'' frs''"
    and ta': "ta_bisim wbisim1 tl1 ta'" by blast
  from exec1 have "\<tau>trsys.silent_moves (mexecd (compP2 P) t) (\<tau>MOVE2 (compP2 P)) ((xcp, frs), h) ((xcp', frs'), h)"
    by(rule \<tau>Exec_1_dr_rtranclpD)
  thus "\<exists>s2' s2'' tl2. \<tau>trsys.silent_moves (mexecd (compP2 P) t) (\<tau>MOVE2 (compP2 P)) s2 s2' \<and> 
                       mexecd (compP2 P) t s2' tl2 s2'' \<and> \<not> \<tau>MOVE2 (compP2 P) s2' tl2 s2'' \<and>
                       wbisim1 t s1' s2'' \<and> ta_bisim wbisim1 tl1 tl2"
    using bisim' exec2 \<tau>' s1 s1' s2 ta' unfolding \<open>h2 = h\<close>
    apply(subst (1 2) split_paired_Ex)
    apply(subst (1 2) split_paired_Ex)
    by clarify ((rule exI conjI|assumption)+, auto)
next
  fix s1 s2 tl2 s2'
  assume "wbisim1 t s1 s2" and "mexecd (compP2 P) t s2 tl2 s2'" and "\<not> \<tau>MOVE2 (compP2 P) s2 tl2 s2'"
  moreover obtain e xs exs h1 where s1: "s1 = (((e, xs), exs), h1)" by(cases s1) auto
  moreover obtain xcp frs h where s2: "s2 = ((xcp, frs), h)" by(cases s2) auto
  moreover obtain xcp' frs' h2' where s2': "s2' = ((xcp', frs'), h2')" by(cases s2') auto
  ultimately have [simp]: "h1 = h"  and exec: "exec_1_d (compP2 P) t (Normal (xcp, h, frs)) tl2 (Normal (xcp', h2', frs'))"
    and \<tau>: "\<not> \<tau>Move2 (compP2 P) (xcp, h, frs)" and bisim: "bisim1_list1 t h (e, xs) exs xcp frs"
    apply auto
    apply(erule jvmd_NormalE)
    apply(cases xcp)
    apply auto
    apply(rename_tac stk loc C M pc frs)
    apply(case_tac "instrs_of (compP2 P) C M ! pc")
    apply(simp_all split: if_split_asm)
    apply(auto dest!: \<tau>external_red_external_aggr_TA_empty simp add: check_def has_method_def \<tau>external_def \<tau>external'_def)
    done
  from \<tau>Red1_simulates_exec_1_not_\<tau>[OF wf exec bisim \<tau>] obtain e' xs' exs' ta' e'' xs'' exs''
    where red1: "\<tau>Red1r P t h ((e, xs), exs) ((e', xs'), exs')"
    and red2: "True,P,t \<turnstile>1 \<langle>(e', xs')/exs',h\<rangle> -ta'\<rightarrow> \<langle>(e'', xs'')/exs'',h2'\<rangle>"
    and \<tau>': "\<not> \<tau>Move1 P h ((e', xs'), exs')" and ta': "ta_bisim wbisim1 ta' tl2"
    and bisim': "bisim1_list1 t h2' (e'', xs'') exs'' xcp' frs'" by blast
  from red1 have "\<tau>trsys.silent_moves (mred1 P t) (\<tau>MOVE1 P) (((e, xs), exs), h) (((e', xs'), exs'), h)"
    by(rule \<tau>Red1r_rtranclpD)
  thus "\<exists>s1' s1'' tl1. \<tau>trsys.silent_moves (mred1 P t) (\<tau>MOVE1 P) s1 s1' \<and> mred1 P t s1' tl1 s1'' \<and>
                      \<not> \<tau>MOVE1 P s1' tl1 s1'' \<and> wbisim1 t s1'' s2' \<and> ta_bisim wbisim1 tl1 tl2"
    using bisim' red2 \<tau>' s1 s2 s2' \<open>h1 = h\<close> ta'
    apply -
    apply(rule exI[where x="(((e', xs'), exs'), h)"])
    apply(rule exI[where x="(((e'', xs''), exs''), h2')"])
    apply(rule exI[where x="ta'"])
    apply auto
    done
next
  have "wf (inv_image {(x, y). x < y} (\<lambda>(((e, xs), exs), h). sim12_size e))"
    by(rule wf_inv_image)(rule wf_less)
  also have "inv_image {(x, y). x < y} (\<lambda>(((e, xs), exs), h). sim12_size e) =
    {(x, y). (\<lambda>(((e, xs), exs), h) (((e', xs'), exs'), h'). sim12_size e < sim12_size e') x y}" by auto
  finally show "wfP (\<lambda>(((e, xs), exs), h) (((e', xs'), exs'), h'). sim12_size e < sim12_size e')"
    unfolding wfP_def .
next
  from wfP_sim21_size
  have "wf {(xcpfrs, xcpfrs'). sim21_size (compP2 P) xcpfrs xcpfrs'}" by(unfold wfP_def)
  hence "wf (inv_image {(xcpfrs, xcpfrs'). sim21_size (compP2 P) xcpfrs xcpfrs'} fst)" by(rule wf_inv_image)
  also have "inv_image {(xcpfrs, xcpfrs'). sim21_size (compP2 P) xcpfrs xcpfrs'} fst =
    {((xcpfrs, h), (xcpfrs', h)). sim21_size (compP2 P) xcpfrs xcpfrs'}" by auto
  also have "\<dots> = {(x, y). (\<lambda>(xcpfrs, h) (xcpfrs', h). sim21_size (compP2 P) xcpfrs xcpfrs') x y}" by(auto)
  finally show "wfP (\<lambda>(xcpfrs, h) (xcpfrs', h). sim21_size (compP2 P) xcpfrs xcpfrs')"
    unfolding wfP_def .
qed

lemma Red1_execd_delay_bisim:
  assumes wf: "wf_J1_prog P"
  shows "delay_bisimulation_diverge (mred1 P t) (mexecd (compP2 P) t) (wbisim1 t) (ta_bisim wbisim1) (\<tau>MOVE1 P) (\<tau>MOVE2 (compP2 P))"
proof -
  interpret delay_bisimulation_measure
    "mred1 P t" "mexecd (compP2 P) t" "wbisim1 t" "ta_bisim wbisim1" "\<tau>MOVE1 P" "\<tau>MOVE2 (compP2 P)"
    "\<lambda>(((e, xs), exs), h) (((e', xs'), exs'), h'). sim12_size e < sim12_size e'"
    "\<lambda>(xcpfrs, h) (xcpfrs', h). sim21_size (compP2 P) xcpfrs xcpfrs'"
    using wf by(rule Red1_execd_weak_bisim)
  show ?thesis by(unfold_locales)
qed

end

definition bisim_wait1JVM :: 
  "'addr jvm_prog \<Rightarrow> ('addr expr1 \<times> 'addr locals1) \<times> ('addr expr1 \<times> 'addr locals1) list \<Rightarrow> 'addr jvm_thread_state \<Rightarrow> bool"
where
  "bisim_wait1JVM P \<equiv> 
  \<lambda>((e1, xs1), exs1) (xcp, frs). call1 e1 \<noteq> None \<and> 
     (case frs of Nil \<Rightarrow> False | (stk, loc, C, M, pc) # frs' \<Rightarrow> \<exists>M' n. instrs_of P C M ! pc = Invoke M' n)"

sublocale J1_JVM_heap_conf_base < Red1_execd:
  FWbisimulation_base 
    final_expr1
    "mred1 P"
    JVM_final
    "mexecd (compP2 P)"
    convert_RA
    wbisim1
    "bisim_wait1JVM (compP2 P)" 
.

sublocale JVM_heap_base < execd_mthr:
  \<tau>multithreaded
    JVM_final
    "mexecd P"
    convert_RA
    "\<tau>MOVE2 P"
  for P
by(unfold_locales)

sublocale J1_JVM_heap_conf_base < Red1_execd:
  FWdelay_bisimulation_base 
    final_expr1
    "mred1 P"
    JVM_final
    "mexecd (compP2 P)"
    convert_RA
    "wbisim1"
    "bisim_wait1JVM (compP2 P)" 
    "\<tau>MOVE1 P"
    "\<tau>MOVE2 (compP2 P)"
by(unfold_locales)

context J1_JVM_conf_read begin

theorem Red1_exec1_FWwbisim:
  assumes wf: "wf_J1_prog P"
  shows "FWdelay_bisimulation_diverge final_expr1 (mred1 P) JVM_final (mexecd (compP2 P)) wbisim1 (bisim_wait1JVM (compP2 P)) (\<tau>MOVE1 P) (\<tau>MOVE2 (compP2 P))"
proof -
  let ?exec = "mexecd (compP2 P)"
  let ?\<tau>exec = "\<lambda>t. \<tau>trsys.silent_moves (mexecd (compP2 P) t) (\<tau>MOVE2 (compP2 P))"
  let ?\<tau>red = "\<lambda>t. \<tau>trsys.silent_moves (mred1 P t) (\<tau>MOVE1 P)"
  interpret delay_bisimulation_diverge 
    "mred1 P t" "?exec t" "wbisim1 t" "ta_bisim wbisim1" "\<tau>MOVE1 P" "\<tau>MOVE2 (compP2 P)"
    for t
    using wf by(rule Red1_execd_delay_bisim)
  show ?thesis
  proof
    fix t s1 s2
    assume "wbisim1 t s1 s2" "(\<lambda>(x1, m). final_expr1 x1) s1"
    moreover obtain e xs exs m1 where [simp]: "s1 = (((e, xs), exs), m1)" by(cases s1) auto
    moreover obtain xcp frs m2 where [simp]: "s2 = ((xcp, frs), m2)" by(cases s2) auto
    ultimately have [simp]: "m2 = m1" "exs = []"
      and "bisim1_list1 t m1 (e, xs) [] xcp frs" 
      and "final e" by auto
    from \<open>bisim1_list1 t m1 (e, xs) [] xcp frs\<close> \<open>final e\<close>
    show "\<exists>s2'. ?\<tau>exec t s2 s2' \<and> wbisim1 t s1 s2' \<and> (\<lambda>(x2, m). JVM_final x2) s2'"
    proof cases
      case (bl1_Normal stk loc C M pc frs' Ts T body D)
      hence [simp]: "frs = [(stk, loc, C, M, pc)]"
        and conf: "compTP P \<turnstile> t:(xcp, m1, frs) \<surd>"
        and sees: "P \<turnstile> C sees M: Ts\<rightarrow>T = \<lfloor>body\<rfloor> in D"
        and bisim: "P,blocks1 0 (Class D # Ts) body,m1 \<turnstile> (e, xs) \<leftrightarrow> (stk, loc, pc, xcp)"
        and var: "max_vars e \<le> length xs" by auto
      from \<open>final e\<close> show ?thesis
      proof cases
        fix v
        assume [simp]: "e = Val v"
        with bisim have [simp]: "xcp = None" "xs = loc"
          and exec: "\<tau>Exec_mover_a P t (blocks1 0 (Class D # Ts) body) m1 (stk, loc, pc, xcp) ([v], loc, length (compE2 body), None)"
          by(auto dest!: bisim1Val2D1)
        from exec have "\<tau>Exec_mover_a P t body m1 (stk, loc, pc, xcp) ([v], loc, length (compE2 body), None)"
          unfolding  \<tau>Exec_mover_blocks1 .
        with sees have "\<tau>Exec_1r (compP2 P) t (xcp, m1, frs) (None, m1, [([v], loc, C, M, length (compE2 body))])"
          by(auto intro: \<tau>Exec_mover_\<tau>Exec_1r)
        with wt_compTP_compP2[OF wf]
        have execd: "\<tau>Exec_1_dr (compP2 P) t (xcp, m1, frs) (None, m1, [([v], loc, C, M, length (compE2 body))])"
          using conf by(rule \<tau>Exec_1r_\<tau>Exec_1_dr)
        also from sees_method_compP[OF sees, of "\<lambda>C M Ts T. compMb2"] sees max_stack1[of body]
        have "\<tau>exec_1_d (compP2 P) t (None, m1, [([v], loc, C, M, length (compE2 body))]) (None, m1, [])"
          by(auto simp add: \<tau>exec_1_d_def compP2_def compMb2_def check_def has_methodI intro: exec_1I)
        finally have "?\<tau>exec t s2 ((None, []), m1)"
          unfolding \<tau>Exec_1_dr_conv_rtranclp by simp
        moreover have "JVM_final (None, [])" by simp
        moreover from conf have "hconf m1" "preallocated m1" unfolding correct_state_def by(simp_all)
        hence "wbisim1 t s1 ((None, []), m1)" by(auto intro: bisim1_list1.intros)
        ultimately show ?thesis by blast
      next
        fix a
        assume [simp]: "e = throw (addr a)"
        hence "\<exists>stk' loc' pc'. \<tau>Exec_mover_a P t body m1 (stk, loc, pc, xcp) (stk', loc', pc', \<lfloor>a\<rfloor>) \<and> P,blocks1 0 (Class D # Ts) body,m1 \<turnstile> (Throw a, xs) \<leftrightarrow> (stk', loc', pc', \<lfloor>a\<rfloor>)"
        proof(cases xcp)
          case None
          with bisim show ?thesis
            by(fastforce dest!: bisim1_Throw_\<tau>Exec_movet simp del: blocks1.simps intro: tranclp_into_rtranclp)
        next
          case (Some a')
          with bisim have "a = a'" by(auto dest: bisim1_ThrowD)
          with Some bisim show ?thesis by(auto)
        qed
        then obtain stk' loc' pc'
          where exec: "\<tau>Exec_mover_a P t body m1 (stk, loc, pc, xcp) (stk', loc', pc', \<lfloor>a\<rfloor>)" 
          and bisim': "P,blocks1 0 (Class D # Ts) body,m1 \<turnstile> (throw (addr a), xs) \<leftrightarrow> (stk', loc', pc', \<lfloor>a\<rfloor>)" by blast
        with sees have "\<tau>Exec_1r (compP2 P) t (xcp, m1, frs) (\<lfloor>a\<rfloor>, m1, [(stk', loc', C, M, pc')])"
          by(auto intro: \<tau>Exec_mover_\<tau>Exec_1r)
        with wt_compTP_compP2[OF wf]
        have execd: "\<tau>Exec_1_dr (compP2 P) t (xcp, m1, frs) (\<lfloor>a\<rfloor>, m1, [(stk', loc', C, M, pc')])"
          using conf by(rule \<tau>Exec_1r_\<tau>Exec_1_dr)
        also {
          from bisim1_xcp_Some_not_caught[OF bisim', of "\<lambda>C M Ts T. compMb2" 0 0]
          have "match_ex_table (compP2 P) (cname_of m1 a) pc' (compxE2 body 0 0) = None" by(simp add: compP2_def)
          moreover from bisim' have "pc' < length (compE2 body)" by(auto dest: bisim1_ThrowD)
          ultimately have "\<tau>exec_1 (compP2 P) t (\<lfloor>a\<rfloor>, m1, [(stk', loc', C, M, pc')]) (\<lfloor>a\<rfloor>, m1, [])"
            using sees_method_compP[OF sees, of "\<lambda>C M Ts T. compMb2"] sees
            by(auto simp add: \<tau>exec_1_def compP2_def compMb2_def has_methodI intro: exec_1I)
          moreover from wt_compTP_compP2[OF wf] execd conf
          have "compTP P \<turnstile> t:(\<lfloor>a\<rfloor>, m1, [(stk', loc', C, M, pc')]) \<surd>" by(rule \<tau>Exec_1_dr_preserves_correct_state)
          ultimately have "\<tau>exec_1_d (compP2 P) t (\<lfloor>a\<rfloor>, m1, [(stk', loc', C, M, pc')]) (\<lfloor>a\<rfloor>, m1, [])"
            using wt_compTP_compP2[OF wf]
            by(auto simp add: \<tau>exec_1_def \<tau>exec_1_d_def welltyped_commute[symmetric] elim: jvmd_NormalE) }
        finally have "?\<tau>exec t s2 ((\<lfloor>a\<rfloor>, []), m1)"
          unfolding \<tau>Exec_1_dr_conv_rtranclp by simp
        moreover have "JVM_final (\<lfloor>a\<rfloor>, [])" by simp
        moreover from conf have "hconf m1" "preallocated m1" by(simp_all add: correct_state_def)
        hence "wbisim1 t s1 ((\<lfloor>a\<rfloor>, []), m1)" by(auto intro: bisim1_list1.intros)
        ultimately show ?thesis by blast
      qed
    qed(auto intro!: exI bisim1_list1.intros)
  next
    fix t s1 s2
    assume "wbisim1 t s1 s2" "(\<lambda>(x2, m). JVM_final x2) s2"
    moreover obtain e xs exs m1 where [simp]: "s1 = (((e, xs), exs), m1)" by(cases s1) auto
    moreover obtain xcp frs m2 where [simp]: "s2 = ((xcp, frs), m2)" by(cases s2) auto
    ultimately have [simp]: "m2 = m1" "exs = []" "frs = []"
      and bisim: "bisim1_list1 t m1 (e, xs) [] xcp []" by(auto elim: bisim1_list1.cases)
    hence "final e" by(auto elim: bisim1_list1.cases)
    thus "\<exists>s1'. ?\<tau>red t s1 s1' \<and> wbisim1 t s1' s2 \<and> (\<lambda>(x1, m). final_expr1 x1) s1'" using bisim by auto
  next
    fix t' x m1 xx m2 t x1 x2 x1' ta1 x1'' m1' x2' ta2 x2'' m2'
    assume b: "wbisim1 t' (x, m1) (xx, m2)" and b': "wbisim1 t (x1, m1) (x2, m2)"
      and \<tau>red: "?\<tau>red t (x1, m1) (x1', m1)"
      and red: "mred1 P t (x1', m1) ta1 (x1'', m1')"
      and "\<not> \<tau>MOVE1 P (x1', m1) ta1 (x1'', m1')"
      and \<tau>exec: "?\<tau>exec t (x2, m2) (x2', m2)"
      and exec: "?exec t (x2', m2) ta2 (x2'', m2')"
      and "\<not> \<tau>MOVE2 (compP2 P) (x2', m2) ta2 (x2'', m2')"
      and b2: "wbisim1 t (x1'', m1') (x2'', m2')"
    from red have "hext m1 m1'" by(auto simp add: split_beta intro: Red1_hext_incr)
    moreover from b2 have "m1' = m2'" by(cases x1'', cases x2'') simp
    moreover from b2 have "hconf m2'"
      by(cases x1'', cases x2'')(auto elim!: bisim1_list1.cases simp add: correct_state_def)
    moreover from b' exec have "preallocated m2"
      by(cases x1, cases x2)(auto elim!: bisim1_list1.cases simp add: correct_state_def)
    moreover from b' \<tau>red red have tconf: "compP2 P,m2 \<turnstile> t \<surd>t"
      by(cases x1, cases x2)(auto elim!: bisim1_list1.cases Red1.cases simp add: correct_state_def \<tau>mreds1_Val_Nil \<tau>mreds1_Throw_Nil)
    from \<tau>exec have \<tau>exec': "\<tau>Exec_1_dr (compP2 P) t (fst x2, m2, snd x2) (fst x2', m2, snd x2')"
      unfolding \<tau>Exec_1_dr_conv_rtranclp by simp
    with b' tconf have "compTP P \<turnstile> t: (fst x2', m2, snd x2') \<surd>"
      using \<open>preallocated m2\<close>
      apply(cases x1, cases x2)
      apply(erule \<tau>Exec_1_dr_preserves_correct_state[OF wt_compTP_compP2[OF wf]])
      apply(auto elim!: bisim1_list1.cases simp add: correct_state_def)
      done
    ultimately show "wbisim1 t' (x, m1') (xx, m2')" using b exec
      apply(cases x, cases xx)
      apply(auto elim!: bisim1_list1.cases intro!: bisim1_list1.intros simp add: split_beta intro: preallocated_hext)
        apply(erule (2) correct_state_heap_change[OF wt_compTP_compP2[OF wf]])
       apply(erule (1) bisim1_hext_mono)
      apply(erule List.list_all2_mono)
      apply(erule (1) bisim1_fr_hext_mono)
      done
  next
    fix t x1 m1 x2 m2 x1' ta1 x1'' m1' x2' ta2 x2'' m2' w
    assume b: "wbisim1 t (x1, m1) (x2, m2)"
      and \<tau>red: "?\<tau>red t (x1, m1) (x1', m1)"
      and red: "mred1 P t (x1', m1) ta1 (x1'', m1')"
      and "\<not> \<tau>MOVE1 P (x1', m1) ta1 (x1'', m1')"
      and \<tau>exec: "?\<tau>exec t (x2, m2) (x2', m2)"
      and exec: "?exec t (x2', m2) ta2 (x2'', m2')"
      and "\<not> \<tau>MOVE2 (compP2 P) (x2', m2) ta2 (x2'', m2')"
      and b': "wbisim1 t (x1'', m1') (x2'', m2')"
      and "ta_bisim wbisim1 ta1 ta2"
      and Suspend: "Suspend w \<in> set \<lbrace>ta1\<rbrace>\<^bsub>w\<^esub>" "Suspend w \<in> set \<lbrace>ta2\<rbrace>\<^bsub>w\<^esub>"
    from red Suspend 
    have "call1 (fst (fst x1'')) \<noteq> None"
      by(cases x1')(cases x1'', auto dest: Red1_Suspend_is_call)
    moreover from mexecd_Suspend_Invoke[OF exec Suspend(2)]
    obtain xcp stk loc C M pc frs' M' n where "x2'' = (xcp, (stk, loc, C, M, pc) # frs')"
      "instrs_of (compP2 P) C M ! pc = Invoke M' n" by blast
    ultimately show "bisim_wait1JVM (compP2 P) x1'' x2''"
      by(simp add: bisim_wait1JVM_def split_beta)
  next
    fix t x1 m1 x2 m2 ta1 x1' m1'
    assume "wbisim1 t (x1, m1) (x2, m2)"
      and "bisim_wait1JVM (compP2 P) x1 x2"
      and "mred1 P t (x1, m1) ta1 (x1', m1')"
      and wakeup: "Notified \<in> set \<lbrace>ta1\<rbrace>\<^bsub>w\<^esub> \<or> WokenUp \<in> set \<lbrace>ta1\<rbrace>\<^bsub>w\<^esub>"
    moreover obtain e1 xs1 exs1 where [simp]: "x1 = ((e1, xs1), exs1)" by(cases x1) auto
    moreover obtain xcp frs where [simp]: "x2 = (xcp, frs)" by(cases x2)
    moreover obtain e1' xs1' exs1' where [simp]: "x1' = ((e1', xs1'), exs1')" by(cases x1') auto
    ultimately have [simp]: "m1 = m2" 
      and bisim: "bisim1_list1 t m2 (e1, xs1) exs1 xcp frs"
      and red: "True,P,t \<turnstile>1 \<langle>(e1, xs1)/exs1, m2\<rangle> -ta1\<rightarrow> \<langle>(e1', xs1')/exs1', m1'\<rangle>"
      and call: "call1 e1 \<noteq> None" 
                "case frs of [] \<Rightarrow> False | (stk, loc, C, M, pc) # frs' \<Rightarrow> \<exists>M' n. instrs_of (compP2 P) C M ! pc = Invoke M' n"
      by(auto simp add: bisim_wait1JVM_def split_def)
    from red wakeup have "\<not> \<tau>Move1 P m2 ((e1, xs1), exs1)"
      by(auto elim!: Red1.cases dest: red1_\<tau>_taD simp add: split_beta ta_upd_simps)
    from exec_1_simulates_Red1_not_\<tau>[OF wf red bisim this] call
    show "\<exists>ta2 x2' m2'. mexecd (compP2 P) t (x2, m2) ta2 (x2', m2') \<and> wbisim1 t (x1', m1') (x2', m2') \<and> ta_bisim wbisim1 ta1 ta2"
      by(auto simp del: not_None_eq simp add: split_paired_Ex ta_bisim_def ta_upd_simps split: list.split_asm)
  next
    fix t x1 m1 x2 m2 ta2 x2' m2'
    assume "wbisim1 t (x1, m1) (x2, m2)"
      and "bisim_wait1JVM (compP2 P) x1 x2"
      and "mexecd (compP2 P) t (x2, m2) ta2 (x2', m2')"
      and wakeup: "Notified \<in> set \<lbrace>ta2\<rbrace>\<^bsub>w\<^esub> \<or> WokenUp \<in> set \<lbrace>ta2\<rbrace>\<^bsub>w\<^esub>"
    moreover obtain e1 xs1 exs1 where [simp]: "x1 = ((e1, xs1), exs1)" by(cases x1) auto
    moreover obtain xcp frs where [simp]: "x2 = (xcp, frs)" by(cases x2)
    moreover obtain xcp' frs' where [simp]: "x2' = (xcp', frs')" by(cases x2')
    ultimately have [simp]: "m1 = m2" 
      and bisim: "bisim1_list1 t m2 (e1, xs1) exs1 xcp frs"
      and exec: "compP2 P,t \<turnstile> Normal (xcp, m2, frs) -ta2-jvmd\<rightarrow> Normal (xcp', m2', frs')"
      and call: "call1 e1 \<noteq> None" 
                "case frs of [] \<Rightarrow> False | (stk, loc, C, M, pc) # frs' \<Rightarrow> \<exists>M' n. instrs_of (compP2 P) C M ! pc = Invoke M' n"
      by(auto simp add: bisim_wait1JVM_def split_def)
    from exec wakeup have "\<not> \<tau>Move2 (compP2 P) (xcp, m2, frs)"
      by(auto dest: \<tau>exec_1_taD simp add: split_beta ta_upd_simps)
    from \<tau>Red1_simulates_exec_1_not_\<tau>[OF wf exec bisim this] call
    show "\<exists>ta1 x1' m1'. mred1 P t (x1, m1) ta1 (x1', m1') \<and> wbisim1 t (x1', m1') (x2', m2') \<and> ta_bisim wbisim1 ta1 ta2"
      by(auto simp del: not_None_eq simp add: split_paired_Ex ta_bisim_def ta_upd_simps split: list.split_asm)
  next
    show "(\<exists>x. final_expr1 x) \<longleftrightarrow> (\<exists>x. JVM_final x)"
      by(auto simp add: split_paired_Ex final_iff)
  qed
qed

end

sublocale J1_JVM_heap_conf_base < Red1_mexecd:
  FWbisimulation_base
    final_expr1
    "mred1 P"
    JVM_final
    "mexecd (compP2 P)"
    convert_RA
    "wbisim1"
    "bisim_wait1JVM (compP2 P)"
.

context J1_JVM_heap_conf begin

lemma bisim_J1_JVM_start:
  assumes wf: "wf_J1_prog P"
  and wf_start: "wf_start_state P C M vs"
  shows "Red1_execd.mbisim (J1_start_state P C M vs) (JVM_start_state (compP2 P) C M vs)"
proof -
  from wf_start obtain Ts T body D where start: "start_heap_ok"
  and sees: "P \<turnstile> C sees M:Ts\<rightarrow>T=\<lfloor>body\<rfloor> in D" and conf: "P,start_heap \<turnstile> vs [:\<le>] Ts" by cases

  let ?e = "blocks1 0 (Class D#Ts) body"
  let ?xs = "Null # vs @ replicate (max_vars body) undefined_value"

  from sees_wf_mdecl[OF wf sees] obtain T'
    where B: "\<B> body (Suc (length Ts))"
    and wt: "P,Class D # Ts \<turnstile>1 body :: T'"
    and da: "\<D> body \<lfloor>{..length Ts}\<rfloor>"
    and sv: "syncvars body"
    by(auto simp add: wf_mdecl_def)

  have "P,?e,start_heap \<turnstile> (?e, ?xs) \<leftrightarrow> ([], ?xs, 0, None)" by(rule bisim1_refl)
  moreover
  from wf have wf': "wf_jvm_prog\<^bsub>compTP P\<^esub> (compP2 P)" by(rule wt_compTP_compP2)
  from sees_method_compP[OF sees, of "\<lambda>C M Ts T. compMb2"]
  have sees': "compP2 P \<turnstile> C sees M: Ts\<rightarrow>T = \<lfloor>compMb2 body\<rfloor> in D" by(simp add: compP2_def)
  from conf have "compP2 P,start_heap \<turnstile> vs [:\<le>] Ts" by(simp add: compP2_def heap_base.compP_confs)
  from BV_correct_initial[OF wf' start sees' this] sees'
  have "compTP P \<turnstile> start_tid:(None, start_heap, [([], ?xs, D, M, 0)]) \<surd>"
      by(simp add: JVM_start_state'_def compP2_def compMb2_def)
  hence "bisim1_list1 start_tid start_heap (?e, ?xs) [] None [([], ?xs, D, M, 0)]"
    using sees_method_idemp[OF sees]
  proof
    show "P,?e,start_heap \<turnstile> (?e, ?xs) \<leftrightarrow> ([], ?xs, 0, None)"
      by(rule bisim1_refl)
    show "max_vars ?e \<le> length ?xs" using conf
      by(auto simp add: blocks1_max_vars dest: list_all2_lengthD)
  qed simp
  thus ?thesis
    using sees sees' unfolding start_state_def
    by -(rule Red1_execd.mbisimI, auto split: if_split_asm intro: wset_thread_okI simp add: compP2_def compMb2_def)
qed

lemmas \<tau>red1_Val_simps = \<tau>red1r_Val \<tau>red1t_Val \<tau>reds1r_map_Val \<tau>reds1t_map_Val

end

end
