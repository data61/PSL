(*  Title:      JinjaThreads/Framework/FWProgressAux.thy
    Author:     Andreas Lochbihler
*)

section \<open>Auxiliary definitions for the progress theorem for the multithreaded semantics\<close>

theory FWProgressAux
imports
  FWSemantics
begin

abbreviation collect_waits :: "('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> ('l + 't + 't) set"
where "collect_waits ta \<equiv> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub> <+> collect_cond_actions \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> <+> collect_interrupts \<lbrace>ta\<rbrace>\<^bsub>i\<^esub>"

lemma collect_waits_unfold:
  "collect_waits ta = {l. Lock \<in> set (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> $ l)} <+> {t. Join t \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>} <+> collect_interrupts \<lbrace>ta\<rbrace>\<^bsub>i\<^esub>"
by(simp add: collect_locks_def)

context multithreaded_base begin

definition must_sync :: "'t \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool" ("_ \<turnstile> \<langle>_,/ _\<rangle>/ \<wrong>" [50, 0,0] 81) where
  "t \<turnstile> \<langle>x, m\<rangle> \<wrong> \<longleftrightarrow> (\<exists>ta x' m' s. t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<and> shr s = m \<and> actions_ok s t ta)"

lemma must_sync_def2:
  "t \<turnstile> \<langle>x, m\<rangle> \<wrong> \<longleftrightarrow> (\<exists>ta x' m' s. t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<and> actions_ok s t ta)"
by(fastforce simp add: must_sync_def intro: cond_action_oks_shr_change)

lemma must_syncI:
  "\<exists>ta x' m' s. t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<and> actions_ok s t ta \<Longrightarrow> t \<turnstile> \<langle>x, m\<rangle> \<wrong>"
by(fastforce simp add: must_sync_def2)

lemma must_syncE:
  "\<lbrakk> t \<turnstile> \<langle>x, m\<rangle> \<wrong>; \<And>ta x' m' s. \<lbrakk> t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>; actions_ok s t ta; m = shr s \<rbrakk> \<Longrightarrow> thesis \<rbrakk> \<Longrightarrow> thesis"
by(fastforce simp only: must_sync_def)

definition can_sync :: "'t \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> ('l + 't + 't) set \<Rightarrow> bool" ("_ \<turnstile> \<langle>_,/ _\<rangle>/ _/ \<wrong>" [50,0,0,0] 81) where
  "t \<turnstile> \<langle>x, m\<rangle> LT \<wrong> \<equiv> \<exists>ta x' m'. t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<and> (LT = collect_waits ta)"

lemma can_syncI:
  "\<lbrakk> t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>;
     LT = collect_waits ta \<rbrakk>
  \<Longrightarrow> t \<turnstile> \<langle>x, m\<rangle> LT \<wrong>"
by(cases ta)(fastforce simp add: can_sync_def)

lemma can_syncE:
  assumes "t \<turnstile> \<langle>x, m\<rangle> LT \<wrong>"
  obtains ta x' m'
  where "t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>"
  and "LT = collect_waits ta"
  using assms
by(clarsimp simp add: can_sync_def)

inductive_set active_threads :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't set"
for s :: "('l,'t,'x,'m,'w) state"
where
  normal:
  "\<And>ln. \<lbrakk> thr s t = Some (x, ln);
     ln = no_wait_locks;
     t \<turnstile> (x, shr s) -ta\<rightarrow> x'm';
     actions_ok s t ta \<rbrakk>
  \<Longrightarrow> t \<in> active_threads s"
| acquire: 
  "\<And>ln. \<lbrakk> thr s t = Some (x, ln);
     ln \<noteq> no_wait_locks;
     \<not> waiting (wset s t);
     may_acquire_all (locks s) t ln \<rbrakk>
  \<Longrightarrow> t \<in> active_threads s"

lemma active_threads_iff:
  "active_threads s = 
  {t. \<exists>x ln. thr s t = Some (x, ln) \<and>
             (if ln = no_wait_locks 
              then \<exists>ta x' m'. t \<turnstile> (x, shr s) -ta\<rightarrow> (x', m') \<and> actions_ok s t ta
              else \<not> waiting (wset s t) \<and> may_acquire_all (locks s) t ln)}"
apply(auto elim!: active_threads.cases intro: active_threads.intros)
apply blast
done

lemma active_thread_ex_red:
  assumes "t \<in> active_threads s"
  shows "\<exists>ta s'. s -t\<triangleright>ta\<rightarrow> s'"
using assms
proof cases
  case (normal x ta x'm' ln)
  with redT_updWs_total[of t "wset s" "\<lbrace>ta\<rbrace>\<^bsub>w\<^esub>"]
  show ?thesis
    by(cases x'm')(fastforce intro!: redT_normal simp del: split_paired_Ex)
next
  case acquire thus ?thesis
    by(fastforce intro: redT_acquire simp del: split_paired_Ex simp add: neq_no_wait_locks_conv)
qed

end

text \<open>Well-formedness conditions for final\<close>

context final_thread begin

inductive not_final_thread :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> bool"
for s :: "('l,'t,'x,'m,'w) state" and t :: "'t" where
  not_final_thread_final: "\<And>ln. \<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; \<not> final x \<rbrakk> \<Longrightarrow> not_final_thread s t"
| not_final_thread_wait_locks: "\<And>ln. \<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; ln \<noteq> no_wait_locks \<rbrakk> \<Longrightarrow> not_final_thread s t"
| not_final_thread_wait_set: "\<And>ln. \<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; wset s t = \<lfloor>w\<rfloor> \<rbrakk> \<Longrightarrow> not_final_thread s t"


declare not_final_thread.cases [elim]

lemmas not_final_thread_cases = not_final_thread.cases [consumes 1, case_names final wait_locks wait_set]

lemma not_final_thread_cases2 [consumes 2, case_names final wait_locks wait_set]:
  "\<And>ln. \<lbrakk> not_final_thread s t; thr s t = \<lfloor>(x, ln)\<rfloor>;
     \<not> final x \<Longrightarrow> thesis; ln \<noteq> no_wait_locks \<Longrightarrow> thesis; \<And>w. wset s t = \<lfloor>w\<rfloor> \<Longrightarrow> thesis \<rbrakk>
  \<Longrightarrow> thesis"
by(auto)

lemma not_final_thread_iff:
  "not_final_thread s t \<longleftrightarrow> (\<exists>x ln. thr s t = \<lfloor>(x, ln)\<rfloor> \<and> (\<not> final x \<or> ln \<noteq> no_wait_locks \<or> (\<exists>w. wset s t = \<lfloor>w\<rfloor>)))"
by(auto intro: not_final_thread.intros)

lemma not_final_thread_conv:
  "not_final_thread s t \<longleftrightarrow> thr s t \<noteq> None \<and> \<not> final_thread s t"
by(auto simp add: final_thread_def intro: not_final_thread.intros)

lemma not_final_thread_existsE:
  assumes "not_final_thread s t"
  and "\<And>x ln. thr s t = \<lfloor>(x, ln)\<rfloor> \<Longrightarrow> thesis"
  shows thesis
using assms by blast

lemma not_final_thread_final_thread_conv:
  "thr s t \<noteq> None \<Longrightarrow> \<not> final_thread s t \<longleftrightarrow> not_final_thread s t"
by(simp add: not_final_thread_iff final_thread_def)

lemma may_join_cond_action_oks:
  assumes "\<And>t'. Join t' \<in> set cas \<Longrightarrow> \<not> not_final_thread s t' \<and> t \<noteq> t'"
  shows "cond_action_oks s t cas"
using assms
proof (induct cas)
  case Nil thus ?case by clarsimp
next
  case (Cons ca cas)
  note IH = \<open>\<lbrakk> \<And>t'. Join t' \<in> set cas \<Longrightarrow> \<not> not_final_thread s t' \<and> t \<noteq> t' \<rbrakk>
             \<Longrightarrow> cond_action_oks s t cas\<close>
  note ass = \<open>\<And>t'. Join t' \<in> set (ca # cas) \<Longrightarrow> \<not> not_final_thread s t' \<and> t \<noteq> t'\<close>
  hence "\<And>t'. Join t' \<in> set cas \<Longrightarrow> \<not> not_final_thread s t' \<and> t \<noteq> t'" by simp
  hence "cond_action_oks s t cas" by(rule IH)
  moreover have "cond_action_ok s t ca"
  proof(cases ca)
    case (Join t')
    with ass have "\<not> not_final_thread s t'" "t \<noteq> t'" by auto
    thus ?thesis using Join by(auto simp add: not_final_thread_iff)
  next
    case Yield thus ?thesis by simp
  qed
  ultimately show ?case by simp
qed

end

context multithreaded begin

lemma red_not_final_thread:
  "s -t\<triangleright>ta\<rightarrow> s' \<Longrightarrow> not_final_thread s t"
by(fastforce elim: redT.cases intro: not_final_thread.intros dest: final_no_red)

lemma redT_preserves_final_thread:
  "\<lbrakk> s -t'\<triangleright>ta\<rightarrow> s'; final_thread s t \<rbrakk> \<Longrightarrow> final_thread s' t"
apply(erule redT.cases)
 apply(clarsimp simp add: final_thread_def)
apply(auto simp add: final_thread_def dest: redT_updTs_None redT_updTs_Some final_no_red intro: redT_updWs_None_implies_None)
done

end

context multithreaded_base begin

definition wset_Suspend_ok :: "('l,'t,'x,'m,'w) state set \<Rightarrow> ('l,'t,'x,'m,'w) state set"
where
  "wset_Suspend_ok I = 
  {s. s \<in> I \<and> 
      (\<forall>t \<in> dom (wset s). \<exists>s0\<in>I. \<exists>s1\<in>I. \<exists>ttas x x0 ta w' ln' ln''. s0 -t\<triangleright>ta\<rightarrow> s1 \<and> s1 -\<triangleright>ttas\<rightarrow>* s \<and> 
           thr s0 t = \<lfloor>(x0, no_wait_locks)\<rfloor> \<and> t \<turnstile> \<langle>x0, shr s0\<rangle> -ta\<rightarrow> \<langle>x, shr s1\<rangle> \<and> Suspend w' \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<and>
           actions_ok s0 t ta \<and> thr s1 t = \<lfloor>(x, ln')\<rfloor> \<and> thr s t = \<lfloor>(x, ln'')\<rfloor>)}"

lemma wset_Suspend_okI:
  "\<lbrakk> s \<in> I;
     \<And>t w. wset s t = \<lfloor>w\<rfloor> \<Longrightarrow> \<exists>s0\<in>I. \<exists>s1\<in>I. \<exists>ttas x x0 ta w' ln' ln''. s0 -t\<triangleright>ta\<rightarrow> s1 \<and> s1 -\<triangleright>ttas\<rightarrow>* s \<and> 
           thr s0 t = \<lfloor>(x0, no_wait_locks)\<rfloor> \<and> t \<turnstile> \<langle>x0, shr s0\<rangle> -ta\<rightarrow> \<langle>x, shr s1\<rangle> \<and> Suspend w' \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<and>
           actions_ok s0 t ta \<and> thr s1 t = \<lfloor>(x, ln')\<rfloor> \<and> thr s t = \<lfloor>(x, ln'')\<rfloor> \<rbrakk>
  \<Longrightarrow> s \<in> wset_Suspend_ok I"
unfolding wset_Suspend_ok_def by blast

lemma wset_Suspend_okD1:
  "s \<in> wset_Suspend_ok I \<Longrightarrow> s \<in> I"
unfolding wset_Suspend_ok_def by blast

lemma wset_Suspend_okD2:
  "\<lbrakk> s \<in> wset_Suspend_ok I; wset s t = \<lfloor>w\<rfloor> \<rbrakk>
  \<Longrightarrow> \<exists>s0\<in>I. \<exists>s1\<in>I. \<exists>ttas x x0 ta w' ln' ln''. s0 -t\<triangleright>ta\<rightarrow> s1 \<and> s1 -\<triangleright>ttas\<rightarrow>* s \<and> 
            thr s0 t = \<lfloor>(x0, no_wait_locks)\<rfloor> \<and> t \<turnstile> \<langle>x0, shr s0\<rangle> -ta\<rightarrow> \<langle>x, shr s1\<rangle> \<and> Suspend w' \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<and>
            actions_ok s0 t ta \<and> thr s1 t = \<lfloor>(x, ln')\<rfloor> \<and> thr s t = \<lfloor>(x, ln'')\<rfloor>"
unfolding wset_Suspend_ok_def by blast

lemma wset_Suspend_ok_imp_wset_thread_ok:
  "s \<in> wset_Suspend_ok I \<Longrightarrow> wset_thread_ok (wset s) (thr s)"
apply(rule wset_thread_okI)
apply(rule ccontr)
apply(auto dest: wset_Suspend_okD2)
done

lemma invariant3p_wset_Suspend_ok:
  assumes I: "invariant3p redT I"
  shows "invariant3p redT (wset_Suspend_ok I)"
proof(rule invariant3pI)
  fix s tl s'
  assume wso: "s \<in> wset_Suspend_ok I" 
    and "redT s tl s'"
  moreover obtain t' ta where tl: "tl = (t', ta)" by(cases tl)
  ultimately have red: "s -t'\<triangleright>ta\<rightarrow> s'" by simp 
  moreover from wso have "s \<in> I" by(rule wset_Suspend_okD1)
  ultimately have "s' \<in> I" by(rule invariant3pD[OF I])
  thus "s' \<in> wset_Suspend_ok I"
  proof(rule wset_Suspend_okI)
    fix t w
    assume ws't: "wset s' t = \<lfloor>w\<rfloor>"
    show "\<exists>s0\<in>I. \<exists>s1\<in>I. \<exists>ttas x x0 ta w' ln' ln''. s0 -t\<triangleright>ta\<rightarrow> s1 \<and> s1 -\<triangleright>ttas\<rightarrow>* s' \<and>
                   thr s0 t = \<lfloor>(x0, no_wait_locks)\<rfloor> \<and> t \<turnstile> \<langle>x0, shr s0\<rangle> -ta\<rightarrow> \<langle>x, shr s1\<rangle> \<and>
                   Suspend w' \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<and> actions_ok s0 t ta \<and>
                   thr s1 t = \<lfloor>(x, ln')\<rfloor> \<and> thr s' t = \<lfloor>(x, ln'')\<rfloor>"
    proof(cases "t = t'")
      case False
      with red ws't obtain w' where wst: "wset s t = \<lfloor>w'\<rfloor>"
        by cases(auto 4 4 dest: redT_updWs_Some_otherD split: wait_set_status.split_asm)
      from wset_Suspend_okD2[OF wso this] obtain s0 s1 ttas x x0 ta' w' ln' ln''
        where reuse: "s0 \<in> I" "s1 \<in> I" "s0 -t\<triangleright>ta'\<rightarrow> s1" "thr s0 t = \<lfloor>(x0, no_wait_locks)\<rfloor>"
          "t \<turnstile> \<langle>x0, shr s0\<rangle> -ta'\<rightarrow> \<langle>x, shr s1\<rangle>" "Suspend w' \<in> set \<lbrace>ta'\<rbrace>\<^bsub>w\<^esub>" "actions_ok s0 t ta'" "thr s1 t = \<lfloor>(x, ln')\<rfloor>"
        and step: "s1 -\<triangleright>ttas\<rightarrow>* s" and tst: "thr s t = \<lfloor>(x, ln'')\<rfloor>" by blast
      from step red have "s1 -\<triangleright>ttas@[(t', ta)]\<rightarrow>* s'" unfolding RedT_def by(rule rtrancl3p_step)
      moreover from red tst False have "thr s' t = \<lfloor>(x, ln'')\<rfloor>"
        by(cases)(auto intro: redT_updTs_Some)
      ultimately show ?thesis using reuse by blast
    next
      case True
      from red show ?thesis
      proof(cases)
        case (redT_normal x x' m)
        note red' = \<open>t' \<turnstile> \<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x', m\<rangle>\<close>
          and tst' = \<open>thr s t' = \<lfloor>(x, no_wait_locks)\<rfloor>\<close>
          and aok = \<open>actions_ok s t' ta\<close>
          and s' = \<open>redT_upd s t' ta x' m s'\<close>
        from s' have ws': "redT_updWs t' (wset s) \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> (wset s')"
          and m: "m = shr s'" 
          and ts't: "thr s' t' = \<lfloor>(x', redT_updLns (locks s) t' (snd (the (thr s t'))) \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>)\<rfloor>" by auto
        from aok have nwait: "\<not> waiting (wset s t')"
          by(auto simp add: wset_actions_ok_def waiting_def split: if_split_asm)
        have "\<exists>w'. Suspend w' \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>"
        proof(cases "wset s t")
          case None
          from redT_updWs_None_SomeD[OF ws', OF ws't None] 
          show ?thesis ..
        next
          case (Some w')
          with True aok have "Notified \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub> \<or> WokenUp \<in> set \<lbrace>ta\<rbrace>\<^bsub>w\<^esub>"
            by(auto simp add: wset_actions_ok_def split: if_split_asm)
          with ws' show ?thesis using ws't unfolding True
            by(rule redT_updWs_WokenUp_SuspendD)
        qed
        with tst' ts't aok \<open>s \<in> I\<close> \<open>s' \<in> I\<close> red red' show ?thesis 
          unfolding True m by blast
      next
        case (redT_acquire x n ln) 
        with ws't True have "wset s t = \<lfloor>w\<rfloor>" by auto
        from wset_Suspend_okD2[OF wso this] \<open>thr s t' = \<lfloor>(x, ln)\<rfloor>\<close> True
        obtain s0 s1 ttas x0 ta' w' ln' ln''
          where reuse: "s0 \<in> I" "s1 \<in> I" "s0 -t\<triangleright>ta'\<rightarrow> s1" "thr s0 t = \<lfloor>(x0, no_wait_locks)\<rfloor>"
            "t \<turnstile> \<langle>x0, shr s0\<rangle> -ta'\<rightarrow> \<langle>x, shr s1\<rangle>" "Suspend w' \<in> set \<lbrace>ta'\<rbrace>\<^bsub>w\<^esub>" "actions_ok s0 t ta'" "thr s1 t = \<lfloor>(x, ln')\<rfloor>"
          and step: "s1 -\<triangleright>ttas\<rightarrow>* s" by fastforce
        from step red have "s1 -\<triangleright>ttas@[(t', ta)]\<rightarrow>* s'" unfolding RedT_def by(rule rtrancl3p_step)
        moreover from redT_acquire True have "thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor>" by simp
        ultimately show ?thesis using reuse by blast
      qed
    qed
  qed
qed

end

end
