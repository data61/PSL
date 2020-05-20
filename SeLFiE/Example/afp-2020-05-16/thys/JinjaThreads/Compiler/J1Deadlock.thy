(*  Title:      JinjaThreads/Compiler/J1Deadlock.thy
    Author:     Andreas Lochbihler
*)

section \<open>Deadlock perservation for the intermediate language\<close>

theory J1Deadlock imports
  J1
  "../Framework/FWDeadlock"
  "../Common/ExternalCallWF"
begin

context J1_heap_base begin

lemma IUF_red_taD:
  "True,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta\<rightarrow> \<langle>e', s'\<rangle>
  \<Longrightarrow> \<exists>e' ta' s'. False,P,t \<turnstile>1 \<langle>e, s\<rangle> -ta'\<rightarrow> \<langle>e', s'\<rangle> \<and>
     collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and> set \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<subseteq> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> \<and> collect_interrupts \<lbrace>ta'\<rbrace>\<^bsub>i\<^esub> \<subseteq> collect_interrupts \<lbrace>ta\<rbrace>\<^bsub>i\<^esub> \<and>
     (\<exists>s. Red1_mthr.actions_ok s t ta')"

  and IUFs_reds_taD:
  "True,P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta\<rightarrow>] \<langle>es', s'\<rangle>
  \<Longrightarrow> \<exists>es' ta' s'. False,P,t \<turnstile>1 \<langle>es, s\<rangle> [-ta'\<rightarrow>] \<langle>es', s'\<rangle> \<and>
     collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and> set \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<subseteq> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> \<and> collect_interrupts \<lbrace>ta'\<rbrace>\<^bsub>i\<^esub> \<subseteq> collect_interrupts \<lbrace>ta\<rbrace>\<^bsub>i\<^esub> \<and>
     (\<exists>s. Red1_mthr.actions_ok s t ta')"
proof(induct rule: red1_reds1.inducts)
  case Red1InstanceOf thus ?case
    using [[hypsubst_thin = true]]
    by(auto intro!: exI red1_reds1.Red1InstanceOf simp del: split_paired_Ex)((subst fst_conv snd_conv wset_def)+, simp)
next
  case Red1CallExternal thus ?case
    by(fastforce simp del: split_paired_Ex dest: red_external_ta_satisfiable[where final="final_expr1 :: ('addr expr1 \<times> 'addr val list) \<times> ('addr expr1 \<times> 'addr val list) list \<Rightarrow> bool"] intro: red1_reds1.Red1CallExternal)
next
  case Lock1Synchronized thus ?case
    by(auto intro!: exI exI[where x="(K$ None, (Map.empty, undefined), Map.empty, {})"] red1_reds1.Lock1Synchronized simp del: split_paired_Ex simp add: lock_ok_las_def finfun_upd_apply may_lock.intros(1))
next
  case (Synchronized1Red2 e s ta e' s' V a)
  then obtain e' ta' s'
    where "False,P,t \<turnstile>1 \<langle>e,s\<rangle> -ta'\<rightarrow> \<langle>e',s'\<rangle>"
    and L: "collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and> set \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<subseteq> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> \<and> collect_interrupts \<lbrace>ta'\<rbrace>\<^bsub>i\<^esub> \<subseteq> collect_interrupts \<lbrace>ta\<rbrace>\<^bsub>i\<^esub>"
    and aok: "\<exists>s. Red1_mthr.actions_ok s t ta'"
    by blast
  from \<open>False,P,t \<turnstile>1 \<langle>e,s\<rangle> -ta'\<rightarrow> \<langle>e',s'\<rangle>\<close> have "False,P,t \<turnstile>1 \<langle>insync\<^bsub>V\<^esub> (a) e, s\<rangle> -ta'\<rightarrow> \<langle>insync\<^bsub>V\<^esub> (a) e', s'\<rangle>"
    by(rule red1_reds1.Synchronized1Red2)
  thus ?case using L aok by blast
next
  case Unlock1Synchronized thus ?case
    by(auto simp del: split_paired_Ex intro!: exI exI[where x="(K$ \<lfloor>(t, 0)\<rfloor>, (Map.empty, undefined), Map.empty, {})"] red1_reds1.Unlock1Synchronized simp add: lock_ok_las_def finfun_upd_apply)
next
  case Unlock1SynchronizedFail thus ?case
    by(auto simp del: split_paired_Ex intro!: exI exI[where x="(K$ \<lfloor>(t, 0)\<rfloor>, (Map.empty, undefined), Map.empty, {})"] red1_reds1.Unlock1Synchronized simp add: lock_ok_las_def finfun_upd_apply collect_locks_def split: if_split_asm)
next
  case Synchronized1Throw2 thus ?case
    by(auto simp del: split_paired_Ex intro!: exI exI[where x="(K$ \<lfloor>(t, 0)\<rfloor>, (Map.empty, undefined), Map.empty, {})"] red1_reds1.Synchronized1Throw2 simp add: lock_ok_las_def finfun_upd_apply)
next
  case Synchronized1Throw2Fail thus ?case
    by(auto simp del: split_paired_Ex intro!: exI exI[where x="(K$ \<lfloor>(t, 0)\<rfloor>, (Map.empty, undefined), Map.empty, {})"] red1_reds1.Synchronized1Throw2 simp add: lock_ok_las_def finfun_upd_apply collect_locks_def split: if_split_asm)
qed(fastforce intro: red1_reds1.intros)+

lemma IUF_Red1_taD:
  assumes "True,P,t \<turnstile>1 \<langle>ex/exs, h\<rangle> -ta\<rightarrow> \<langle>ex'/exs', h'\<rangle>"
  shows "\<exists>ex' exs' h' ta'. False,P,t \<turnstile>1 \<langle>ex/exs, h\<rangle> -ta'\<rightarrow> \<langle>ex'/exs', h'\<rangle> \<and>
     collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> \<and> set \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> \<subseteq> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> \<and> collect_interrupts \<lbrace>ta'\<rbrace>\<^bsub>i\<^esub> \<subseteq> collect_interrupts \<lbrace>ta\<rbrace>\<^bsub>i\<^esub> \<and>
     (\<exists>s. Red1_mthr.actions_ok s t ta')"
using assms
apply(cases)
apply(safe dest!: IUF_red_taD)
  apply(simp del: split_paired_Ex)
  apply(rule exI conjI)+
  apply(erule red1Red)
  apply simp
  apply blast
 apply(rule exI conjI red1Call)+
 apply(auto simp add: lock_ok_las_def)
apply(rule exI conjI red1Return)+
apply auto
done

lemma mred1'_mred1_must_sync_eq:
  "Red1_mthr.must_sync False P t x (shr s) = Red1_mthr.must_sync True P t x (shr s)"
proof
  assume "Red1_mthr.must_sync False P t x (shr s)"
  thus "Red1_mthr.must_sync True P t x (shr s)"
    by(rule Red1_mthr.must_syncE)(rule Red1_mthr.must_syncI, auto simp add: split_def simp del: split_paired_Ex intro: Red1_False_into_Red1_True)
next
  assume "Red1_mthr.must_sync True P t x (shr s)"
  thus "Red1_mthr.must_sync False P t x (shr s)"
    apply(rule Red1_mthr.must_syncE)
    apply(rule Red1_mthr.must_syncI)
    apply(cases x)
    apply(auto simp add: split_beta split_paired_Ex)
    apply(drule IUF_Red1_taD)
    apply simp
    apply blast
    done
qed

lemma Red1_Red1'_deadlock_inv:
  "Red1_mthr.deadlock True P s = Red1_mthr.deadlock False P s"
proof(rule iffI)
  assume dead: "Red1_mthr.deadlock True P s"
  show "Red1_mthr.deadlock False P s"
  proof(rule multithreaded_base.deadlockI)
    fix t x
    assume tst: "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
      and nfin: "\<not> final_expr1 x"
      and wst: "wset s t = None"
    with dead obtain ms: "Red1_mthr.must_sync True P t x (shr s)"
      and cs [rule_format]: "\<forall>LT. Red1_mthr.can_sync True P t x (shr s) LT \<longrightarrow>
               (\<exists>lt\<in>LT. final_thread.must_wait final_expr1 s t lt (dom (thr s)))"
      by(rule Red1_mthr.deadlockD1)
    from ms[folded mred1'_mred1_must_sync_eq]
    show "Red1_mthr.must_sync False P t x (shr s) \<and>
             (\<forall>LT. Red1_mthr.can_sync False P t x (shr s) LT \<longrightarrow>
                   (\<exists>lt\<in>LT. final_thread.must_wait final_expr1 s t lt (dom (thr s))))"
    proof
      show "\<forall>LT. Red1_mthr.can_sync False P t x (shr s) LT \<longrightarrow>
         (\<exists>lt\<in>LT. final_thread.must_wait final_expr1 s t lt (dom (thr s)))"
      proof(intro strip)
        fix LT
        assume "Red1_mthr.can_sync False P t x (shr s) LT"
        then obtain ta x' m' where "mred1' P t (x, shr s) ta (x', m')" 
          and [simp]: "LT = collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> <+> collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> <+> collect_interrupts \<lbrace>ta\<rbrace>\<^bsub>i\<^esub>"
          by(rule Red1_mthr.can_syncE)
        hence "mred1 P t (x, shr s) ta (x', m')" by(auto simp add: split_beta intro: Red1_False_into_Red1_True)
        hence "Red1_mthr.can_sync True P t x (shr s) LT" by(rule Red1_mthr.can_syncI) simp
        thus "\<exists>lt\<in>LT. final_thread.must_wait final_expr1 s t lt (dom (thr s))" by(rule cs)
      qed
    qed
  next
    fix t x ln l
    assume "thr s t = \<lfloor>(x, ln)\<rfloor>" "0 < ln $ l" "\<not> waiting (wset s t)"
    thus "\<exists>l t'. 0 < ln $ l \<and> t \<noteq> t' \<and> thr s t' \<noteq> None \<and> has_lock ((locks s) $ l) t'"
      by(rule Red1_mthr.deadlockD2[OF dead]) blast
  next
    fix t x w
    assume "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
    thus "wset s t \<noteq> \<lfloor>PostWS w\<rfloor>"
      by(rule Red1_mthr.deadlockD3[OF dead, rule_format])
  qed
next
  assume dead: "Red1_mthr.deadlock False P s"
  show "Red1_mthr.deadlock True P s"
  proof(rule Red1_mthr.deadlockI)
    fix t x
    assume tst: "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
      and nfin: "\<not> final_expr1 x"
      and wst: "wset s t = None"
    with dead obtain ms: "Red1_mthr.must_sync False P t x (shr s)"
      and cs [rule_format]: "\<forall>LT. Red1_mthr.can_sync False P t x (shr s) LT \<longrightarrow>
               (\<exists>lt\<in>LT. final_thread.must_wait final_expr1 s t lt (dom (thr s)))"
      by(rule Red1_mthr.deadlockD1)
    from ms[unfolded mred1'_mred1_must_sync_eq]
    show "Red1_mthr.must_sync True P t x (shr s) \<and>
             (\<forall>LT. Red1_mthr.can_sync True P t x (shr s) LT \<longrightarrow>
                   (\<exists>lt\<in>LT. final_thread.must_wait final_expr1 s t lt (dom (thr s))))"
    proof
      show "\<forall>LT. Red1_mthr.can_sync True P t x (shr s) LT \<longrightarrow>
         (\<exists>lt\<in>LT. final_thread.must_wait final_expr1 s t lt (dom (thr s)))"
      proof(intro strip)
        fix LT
        assume "Red1_mthr.can_sync True P t x (shr s) LT"
        then obtain ta x' m' where "mred1 P t (x, shr s) ta (x', m')" 
          and [simp]: "LT = collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> <+> collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> <+> collect_interrupts \<lbrace>ta\<rbrace>\<^bsub>i\<^esub>"
          by(rule Red1_mthr.can_syncE)
        then obtain e xs exs e' xs' exs' where x [simp]: "x = ((e, xs), exs)" "x' = ((e', xs'), exs')"
          and red: "True,P,t \<turnstile>1 \<langle>(e, xs)/exs, shr s\<rangle> -ta\<rightarrow> \<langle>(e', xs')/exs', m'\<rangle>" by(cases x, cases x') fastforce
        from IUF_Red1_taD[OF red] obtain ex'' exs'' h'' ta' 
          where red': "False,P,t \<turnstile>1 \<langle>(e, xs)/exs,shr s\<rangle> -ta'\<rightarrow> \<langle>ex''/exs'',h''\<rangle>"
          and "collect_locks \<lbrace>ta'\<rbrace>\<^bsub>l\<^esub> <+> collect_cond_actions \<lbrace>ta'\<rbrace>\<^bsub>c\<^esub> <+> collect_interrupts \<lbrace>ta'\<rbrace>\<^bsub>i\<^esub> \<subseteq> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> <+> collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> <+> collect_interrupts \<lbrace>ta\<rbrace>\<^bsub>i\<^esub>"
          by auto blast
        then obtain LT' where cs': "Red1_mthr.can_sync False P t x (shr s) LT'" 
          and LT': "LT' \<subseteq> LT" by(cases ex'')(fastforce intro!: Red1_mthr.can_syncI)
        with cs[of LT'] show "\<exists>lt\<in>LT. final_thread.must_wait final_expr1 s t lt (dom (thr s))" by auto
      qed
    qed
  next
    fix t x ln l
    assume "thr s t = \<lfloor>(x, ln)\<rfloor>" "0 < ln $ l" "\<not> waiting (wset s t)"
    thus "\<exists>l t'. 0 < ln $ l \<and> t \<noteq> t' \<and> thr s t' \<noteq> None \<and> has_lock ((locks s) $ l) t'"
      by(rule Red1_mthr.deadlockD2[OF dead]) blast
  next
    fix t x w
    assume "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
    thus "wset s t \<noteq> \<lfloor>PostWS w\<rfloor>"
      by(rule Red1_mthr.deadlockD3[OF dead, rule_format])
  qed
qed

end

end
