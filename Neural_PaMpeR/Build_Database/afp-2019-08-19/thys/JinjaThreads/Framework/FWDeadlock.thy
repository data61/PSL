(*  Title:      JinjaThreads/Framework/FWDeadlock.thy
    Author:     Andreas Lochbihler
*)

section \<open>Deadlock formalisation\<close>

theory FWDeadlock
imports
  FWProgressAux
begin

context final_thread begin

definition all_final_except :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't set \<Rightarrow> bool" where
  "all_final_except s Ts \<equiv> \<forall>t. not_final_thread s t \<longrightarrow> t \<in> Ts"

lemma all_final_except_mono [mono]:
  "(\<And>x. x \<in> A \<longrightarrow> x \<in> B) \<Longrightarrow> all_final_except ts A \<longrightarrow> all_final_except ts B"
by(auto simp add: all_final_except_def)

lemma all_final_except_mono':
  "\<lbrakk> all_final_except ts A; \<And>x. x \<in> A \<Longrightarrow> x \<in> B \<rbrakk> \<Longrightarrow> all_final_except ts B"
by(blast intro: all_final_except_mono[rule_format])

lemma all_final_exceptI:
  "(\<And>t. not_final_thread s t \<Longrightarrow> t \<in> Ts) \<Longrightarrow> all_final_except s Ts"
by(auto simp add: all_final_except_def)

lemma all_final_exceptD:
  "\<lbrakk> all_final_except s Ts; not_final_thread s t \<rbrakk> \<Longrightarrow> t \<in> Ts"
by(auto simp add: all_final_except_def)


inductive must_wait :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> ('l + 't + 't) \<Rightarrow> 't set \<Rightarrow> bool"
  for s :: "('l,'t,'x,'m,'w) state" and t :: "'t" where
  \<comment> \<open>Lock l\<close>
  "\<lbrakk> has_lock (locks s $ l) t'; t' \<noteq> t; t' \<in> Ts \<rbrakk> \<Longrightarrow> must_wait s t (Inl l) Ts"
| \<comment> \<open>Join t'\<close>
  "\<lbrakk> not_final_thread s t'; t' \<in> Ts \<rbrakk> \<Longrightarrow> must_wait s t (Inr (Inl t')) Ts"
| \<comment> \<open>IsInterrupted t' True\<close>
  "\<lbrakk> all_final_except s Ts; t' \<notin> interrupts s \<rbrakk> \<Longrightarrow> must_wait s t (Inr (Inr t')) Ts"

declare must_wait.cases [elim]
declare must_wait.intros [intro]

lemma must_wait_elims [consumes 1, case_names lock join interrupt, cases pred]:
  assumes "must_wait s t lt Ts"
  obtains l t' where "lt = Inl l" "has_lock (locks s $ l) t'" "t' \<noteq> t" "t' \<in> Ts"
  | t' where "lt = Inr (Inl t')" "not_final_thread s t'" "t' \<in> Ts"
  | t' where "lt = Inr (Inr t')" "all_final_except s Ts" "t' \<notin> interrupts s"
using assms
by(auto)

inductive_cases must_wait_elims2 [elim!]:
  "must_wait s t (Inl l) Ts"
  "must_wait s t (Inr (Inl t'')) Ts"
  "must_wait s t (Inr (Inr t'')) Ts"

lemma must_wait_iff:
  "must_wait s t lt Ts \<longleftrightarrow> 
  (case lt of Inl l \<Rightarrow> \<exists>t'\<in>Ts. t \<noteq> t' \<and> has_lock (locks s $ l) t'
     | Inr (Inl t') \<Rightarrow> not_final_thread s t' \<and> t' \<in> Ts
     | Inr (Inr t') \<Rightarrow> all_final_except s Ts \<and> t' \<notin> interrupts s)"
by(auto simp add: must_wait.simps split: sum.splits)

end

text\<open>Deadlock as a system-wide property\<close>

context multithreaded_base begin

definition
  deadlock :: "('l,'t,'x,'m,'w) state \<Rightarrow> bool"
where
  "deadlock s
   \<equiv>   (\<forall>t x. thr s t = \<lfloor>(x, no_wait_locks)\<rfloor> \<and> \<not> final x \<and> wset s t = None
        \<longrightarrow> t \<turnstile> \<langle>x, shr s\<rangle> \<wrong> \<and> (\<forall>LT. t \<turnstile> \<langle>x, shr s\<rangle> LT \<wrong> \<longrightarrow> (\<exists>lt \<in> LT. must_wait s t lt (dom (thr s)))))
     \<and> (\<forall>t x ln. thr s t = \<lfloor>(x, ln)\<rfloor> \<and> (\<exists>l. ln $ l > 0) \<and> \<not> waiting (wset s t)
        \<longrightarrow> (\<exists>l t'. ln $ l > 0 \<and> t \<noteq> t' \<and> thr s t' \<noteq> None \<and> has_lock (locks s $ l) t'))
     \<and> (\<forall>t x w. thr s t = \<lfloor>(x, no_wait_locks)\<rfloor> \<longrightarrow> wset s t \<noteq> \<lfloor>PostWS w\<rfloor>)"

lemma deadlockI:
  "\<lbrakk> \<And>t x. \<lbrakk> thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; \<not> final x; wset s t = None \<rbrakk>
    \<Longrightarrow> t \<turnstile> \<langle>x, shr s\<rangle> \<wrong> \<and> (\<forall>LT. t \<turnstile> \<langle>x, shr s\<rangle> LT \<wrong> \<longrightarrow> (\<exists>lt \<in> LT. must_wait s t lt (dom (thr s))));
    \<And>t x ln l. \<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; ln $ l > 0; \<not> waiting (wset s t) \<rbrakk>
    \<Longrightarrow> \<exists>l t'. ln $ l > 0 \<and> t \<noteq> t' \<and> thr s t' \<noteq> None \<and> has_lock (locks s $ l) t';
    \<And>t x w. thr s t = \<lfloor>(x, no_wait_locks)\<rfloor> \<Longrightarrow> wset s t \<noteq> \<lfloor>PostWS w\<rfloor> \<rbrakk>
  \<Longrightarrow> deadlock s"
by(auto simp add: deadlock_def)

lemma deadlockE:
  assumes "deadlock s"
  obtains "\<forall>t x. thr s t = \<lfloor>(x, no_wait_locks)\<rfloor> \<and> \<not> final x \<and> wset s t = None
        \<longrightarrow> t \<turnstile> \<langle>x, shr s\<rangle> \<wrong> \<and> (\<forall>LT. t \<turnstile> \<langle>x, shr s\<rangle> LT \<wrong> \<longrightarrow> (\<exists>lt \<in> LT. must_wait s t lt (dom (thr s))))"
  and "\<forall>t x ln. thr s t = \<lfloor>(x, ln)\<rfloor> \<and> (\<exists>l. ln $ l > 0) \<and> \<not> waiting (wset s t)
                \<longrightarrow> (\<exists>l t'. ln $ l > 0 \<and> t \<noteq> t' \<and> thr s t' \<noteq> None \<and> has_lock (locks s $ l) t')"
  and "\<forall>t x w. thr s t = \<lfloor>(x, no_wait_locks)\<rfloor> \<longrightarrow> wset s t \<noteq> \<lfloor>PostWS w\<rfloor>"
using assms unfolding deadlock_def by(blast)

lemma deadlockD1:
  assumes "deadlock s"
  and "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
  and "\<not> final x"
  and "wset s t = None"
  obtains "t \<turnstile> \<langle>x, shr s\<rangle> \<wrong>"
  and "\<forall>LT. t \<turnstile> \<langle>x, shr s\<rangle> LT \<wrong> \<longrightarrow> (\<exists>lt \<in> LT. must_wait s t lt (dom (thr s)))"
using assms unfolding deadlock_def by(blast)

lemma deadlockD2:
  fixes ln
  assumes "deadlock s"
  and "thr s t = \<lfloor>(x, ln)\<rfloor>"
  and "ln $ l > 0"
  and "\<not> waiting (wset s t)"
  obtains l' t' where "ln $ l' > 0" "t \<noteq> t'" "thr s t' \<noteq> None" "has_lock (locks s $ l') t'"
using assms unfolding deadlock_def by blast

lemma deadlockD3:
  assumes "deadlock s"
  and "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
  shows "\<forall>w. wset s t \<noteq> \<lfloor>PostWS w\<rfloor>"
using assms unfolding deadlock_def by blast

lemma deadlock_def2:
  "deadlock s \<longleftrightarrow>
    (\<forall>t x. thr s t = \<lfloor>(x, no_wait_locks)\<rfloor> \<and> \<not> final x \<and> wset s t = None
    \<longrightarrow> t \<turnstile> \<langle>x, shr s\<rangle> \<wrong> \<and> (\<forall>LT. t \<turnstile> \<langle>x, shr s\<rangle> LT \<wrong> \<longrightarrow> (\<exists>lt \<in> LT. must_wait s t lt (dom (thr s)))))
  \<and> (\<forall>t x ln. thr s t = \<lfloor>(x, ln)\<rfloor> \<and> ln \<noteq> no_wait_locks \<and> \<not> waiting (wset s t)
    \<longrightarrow> (\<exists>l. ln $ l > 0 \<and> must_wait s t (Inl l) (dom (thr s))))
  \<and> (\<forall>t x w. thr s t = \<lfloor>(x, no_wait_locks)\<rfloor> \<longrightarrow> wset s t \<noteq> \<lfloor>PostWS WSNotified\<rfloor> \<and> wset s t \<noteq> \<lfloor>PostWS WSWokenUp\<rfloor>)"
unfolding neq_no_wait_locks_conv
apply(rule iffI)
 apply(intro strip conjI)
     apply(blast dest: deadlockD1)
    apply(blast dest: deadlockD1)
   apply(blast elim: deadlockD2)
  apply(blast dest: deadlockD3)
 apply(blast dest: deadlockD3)
apply(elim conjE exE)
apply(rule deadlockI)
  apply blast
 apply(rotate_tac 1)
 apply(erule allE, rotate_tac -1)
 apply(erule allE, rotate_tac -1)
 apply(erule allE, rotate_tac -1)
 apply(erule impE, blast)
 apply(elim exE conjE)
 apply(erule must_wait.cases)
   apply(clarify)
   apply(rotate_tac 3)
   apply(rule exI conjI|erule not_sym|assumption)+
    apply blast
   apply blast
  apply blast
 apply blast
apply(case_tac w)
 apply blast
apply blast
done

lemma all_waiting_implies_deadlock:
  assumes "lock_thread_ok (locks s) (thr s)"
  and normal: "\<And>t x. \<lbrakk> thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; \<not> final x; wset s t = None \<rbrakk> 
               \<Longrightarrow> t \<turnstile> \<langle>x, shr s\<rangle> \<wrong> \<and> (\<forall>LT. t \<turnstile> \<langle>x, shr s\<rangle> LT \<wrong> \<longrightarrow> (\<exists>lt \<in> LT. must_wait s t lt (dom (thr s))))"
  and acquire: "\<And>t x ln l. \<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; \<not> waiting (wset s t); ln $ l > 0 \<rbrakk>
                 \<Longrightarrow> \<exists>l'. ln $ l' > 0 \<and> \<not> may_lock (locks s $ l') t"
  and wakeup: "\<And>t x w. thr s t = \<lfloor>(x, no_wait_locks)\<rfloor> \<Longrightarrow> wset s t \<noteq> \<lfloor>PostWS w\<rfloor>"
  shows "deadlock s"
proof(rule deadlockI)
  fix T X
  assume "thr s T = \<lfloor>(X, no_wait_locks)\<rfloor>" "\<not> final X" "wset s T = None"
  thus "T \<turnstile> \<langle>X, shr s\<rangle> \<wrong> \<and> (\<forall>LT. T \<turnstile> \<langle>X, shr s\<rangle> LT \<wrong> \<longrightarrow> (\<exists>lt\<in>LT. must_wait s T lt (dom (thr s))))" 
    by(rule normal)
next
  fix T X LN l'
  assume "thr s T = \<lfloor>(X, LN)\<rfloor>"
    and "0 < LN $ l'"
    and wset: "\<not> waiting (wset s T)"
  from acquire[OF \<open>thr s T = \<lfloor>(X, LN)\<rfloor>\<close> wset, OF \<open>0 < LN $ l'\<close>]
  obtain l' where "0 < LN $ l'" "\<not> may_lock (locks s $ l') T" by blast
  then obtain t' where "T \<noteq> t'" "has_lock (locks s $ l') t'"
    unfolding not_may_lock_conv by fastforce
  moreover with \<open>lock_thread_ok (locks s) (thr s)\<close>
  have "thr s t' \<noteq> None" by(auto dest: lock_thread_okD)
  ultimately show "\<exists>l t'. 0 < LN $ l \<and> T \<noteq> t' \<and> thr s t' \<noteq> None \<and> has_lock (locks s $ l) t'"
    using \<open>0 < LN $ l'\<close> by(auto)
qed(rule wakeup)

lemma mfinal_deadlock:
  "mfinal s \<Longrightarrow> deadlock s"
unfolding mfinal_def2
by(rule deadlockI)(auto simp add: final_thread_def)

text \<open>Now deadlock for single threads\<close>

lemma must_wait_mono:
  "(\<And>x. x \<in> A \<longrightarrow> x \<in> B) \<Longrightarrow> must_wait s t lt A \<longrightarrow> must_wait s t lt B"
by(auto simp add: must_wait_iff split: sum.split elim: all_final_except_mono')

lemma must_wait_mono':
  "\<lbrakk> must_wait s t lt A; A \<subseteq> B \<rbrakk> \<Longrightarrow> must_wait s t lt B"
using must_wait_mono[of A B s t lt]
by blast

end

lemma UN_mono: "\<lbrakk> x \<in> A \<longrightarrow> x \<in> A'; x \<in> B \<longrightarrow> x \<in> B' \<rbrakk> \<Longrightarrow> x \<in> A \<union> B \<longrightarrow> x \<in> A' \<union> B'"
by blast

lemma Collect_mono_conv [mono]: "x \<in> {x. P x} \<longleftrightarrow> P x"
by blast

context multithreaded_base begin

coinductive_set deadlocked :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't set"
  for s :: "('l,'t,'x,'m,'w) state" where
  deadlockedLock:
    "\<lbrakk> thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; t \<turnstile> \<langle>x, shr s\<rangle> \<wrong>; wset s t = None;
       \<And>LT. t \<turnstile> \<langle>x, shr s\<rangle> LT \<wrong> \<Longrightarrow> \<exists>lt \<in> LT. must_wait s t lt (deadlocked s \<union> final_threads s) \<rbrakk>
     \<Longrightarrow> t \<in> deadlocked s"

| deadlockedWait:
    "\<And>ln. \<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; all_final_except s (deadlocked s); waiting (wset s t) \<rbrakk> \<Longrightarrow> t \<in> deadlocked s"

| deadlockedAcquire:
    "\<And>ln. \<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; \<not> waiting (wset s t); ln $ l > 0; has_lock (locks s $ l) t'; t' \<noteq> t; 
       t' \<in> deadlocked s \<or> final_thread s t' \<rbrakk> 
     \<Longrightarrow> t \<in> deadlocked s"
monos must_wait_mono UN_mono

lemma deadlockedAcquire_must_wait:
  "\<And>ln. \<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; \<not> waiting (wset s t); ln $ l > 0; must_wait s t (Inl l) (deadlocked s \<union> final_threads s) \<rbrakk>
  \<Longrightarrow> t \<in> deadlocked s"
apply(erule must_wait_elims)
apply(erule (2) deadlockedAcquire)
apply auto
done

lemma deadlocked_elims [consumes 1, case_names lock wait acquire]:
  assumes "t \<in> deadlocked s"
  and lock: "\<And>x. \<lbrakk> thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; t \<turnstile> \<langle>x, shr s\<rangle> \<wrong>; wset s t = None;
     \<And>LT. t \<turnstile> \<langle>x, shr s\<rangle> LT \<wrong> \<Longrightarrow> \<exists>lt \<in> LT. must_wait s t lt (deadlocked s \<union> final_threads s) \<rbrakk>
     \<Longrightarrow> thesis"
  and wait: "\<And>x ln. \<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; all_final_except s (deadlocked s); waiting (wset s t) \<rbrakk>
     \<Longrightarrow> thesis"
  and acquire: "\<And>x ln l t'. 
    \<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; \<not> waiting (wset s t); 0 < ln $ l; has_lock (locks s $ l) t'; t \<noteq> t';
      t' \<in> deadlocked s \<or> final_thread s t' \<rbrakk> \<Longrightarrow> thesis"
  shows thesis
using assms by cases blast+

lemma deadlocked_coinduct 
  [consumes 1, case_names deadlocked, case_conclusion deadlocked Lock Wait Acquire, coinduct set: deadlocked]:
  assumes major: "t \<in> X"
  and step: 
  "\<And>t. t \<in> X \<Longrightarrow>
     (\<exists>x. thr s t = \<lfloor>(x, no_wait_locks)\<rfloor> \<and> t \<turnstile> \<langle>x, shr s\<rangle> \<wrong> \<and> wset s t = None \<and>
         (\<forall>LT. t \<turnstile> \<langle>x, shr s\<rangle> LT \<wrong> \<longrightarrow> (\<exists>lt\<in>LT. must_wait s t lt (X \<union> deadlocked s \<union> final_threads s)))) \<or>
     (\<exists>x ln. thr s t = \<lfloor>(x, ln)\<rfloor> \<and> all_final_except s (X \<union> deadlocked s) \<and> waiting (wset s t)) \<or>
     (\<exists>x l t' ln. thr s t = \<lfloor>(x, ln)\<rfloor> \<and> \<not> waiting (wset s t) \<and> 0 < ln $ l \<and> has_lock (locks s $ l) t' \<and>
         t' \<noteq> t \<and> ((t' \<in> X \<or> t' \<in> deadlocked s) \<or> final_thread s t'))"
  shows "t \<in> deadlocked s"
using major
proof(coinduct)
  case (deadlocked t)
  have "X \<union> deadlocked s \<union> final_threads s = {x. x \<in> X \<or> x \<in> deadlocked s \<or> x \<in> final_threads s}"
    by auto
  moreover have "X \<union> deadlocked s = {x. x \<in> X \<or> x \<in> deadlocked s}" by blast
  ultimately show ?case using step[OF deadlocked] by(elim disjE) simp_all
qed

definition deadlocked' :: "('l,'t,'x,'m,'w) state \<Rightarrow> bool" where
  "deadlocked' s \<equiv> (\<forall>t. not_final_thread s t \<longrightarrow> t \<in> deadlocked s)"

lemma deadlocked'I:
  "(\<And>t. not_final_thread s t \<Longrightarrow> t \<in> deadlocked s) \<Longrightarrow> deadlocked' s"
by(auto simp add: deadlocked'_def)

lemma deadlocked'D2:
  "\<lbrakk> deadlocked' s; not_final_thread s t; t \<in> deadlocked s \<Longrightarrow> thesis \<rbrakk> \<Longrightarrow> thesis"
by(auto simp add: deadlocked'_def)

lemma not_deadlocked'I:
  "\<lbrakk> not_final_thread s t; t \<notin> deadlocked s \<rbrakk> \<Longrightarrow> \<not> deadlocked' s"
by(auto dest: deadlocked'D2)

lemma deadlocked'_intro:
  "\<lbrakk> \<forall>t. not_final_thread s t \<longrightarrow> t \<in> deadlocked s \<rbrakk> \<Longrightarrow> deadlocked' s"
by(rule deadlocked'I)(blast)+

lemma deadlocked_thread_exists: 
  assumes "t \<in> deadlocked s"
  and "\<And>x ln. thr s t = \<lfloor>(x, ln)\<rfloor> \<Longrightarrow> thesis"
  shows thesis
using assms
by cases blast+

end

context multithreaded begin 

lemma red_no_deadlock: 
  assumes P: "s -t\<triangleright>ta\<rightarrow> s'"
  and dead: "t \<in> deadlocked s"
  shows False
proof -
  from P show False
  proof(cases)
    case (redT_normal x x' m')
    note red = \<open>t \<turnstile> \<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>\<close>
    note tst = \<open>thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>\<close>
    note aok = \<open>actions_ok s t ta\<close>
    show False
    proof(cases "\<exists>w. wset s t = \<lfloor>InWS w\<rfloor>")
      case True with aok show ?thesis by(auto simp add: wset_actions_ok_def split: if_split_asm)
    next
      case False
      with dead tst
      have mle: "t \<turnstile> \<langle>x, shr s\<rangle> \<wrong>"
        and cledead: "\<forall>LT. t \<turnstile> \<langle>x, shr s\<rangle> LT \<wrong> \<longrightarrow> (\<exists>lt \<in> LT. must_wait s t lt (deadlocked s \<union> final_threads s))"
        by(cases, auto simp add: waiting_def)+
      let ?LT = "collect_waits ta"
      from red have "t \<turnstile> \<langle>x, shr s\<rangle> ?LT \<wrong>" by(auto intro: can_syncI)
      then obtain lt where lt: "lt \<in> ?LT" and mw: "must_wait s t lt (deadlocked s \<union> final_threads s)"
        by(blast dest: cledead[rule_format])
      from mw show False
      proof(cases rule: must_wait_elims)
        case (lock l t')
        from \<open>lt = Inl l\<close> lt have "l \<in> collect_locks \<lbrace>ta\<rbrace>\<^bsub>l\<^esub>" by(auto)
        with aok have "may_lock (locks s $ l) t"
          by(auto elim!: collect_locksE lock_ok_las_may_lock)
        with \<open>has_lock (locks s $ l) t'\<close> have "t' = t"
          by(auto dest: has_lock_may_lock_t_eq)
        with \<open>t' \<noteq> t\<close> show False by contradiction
      next
        case (join t')
        from \<open>lt = Inr (Inl t')\<close> lt have "Join t' \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>" by auto
        from \<open>not_final_thread s t'\<close>  obtain x'' ln''
          where "thr s t' = \<lfloor>(x'', ln'')\<rfloor>" by(rule not_final_thread_existsE)
        moreover with \<open>Join t' \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub>\<close> aok
        have "final x''" "ln'' = no_wait_locks" "wset s t' = None"
          by(auto dest: cond_action_oks_Join)
        ultimately show False using \<open>not_final_thread s t'\<close> by(auto)
      next
        case (interrupt t')
        from  aok lt \<open>lt = Inr (Inr t')\<close>
        have "t' \<in> interrupts s"
          by(auto intro: collect_interrupts_interrupted)
        with \<open>t' \<notin> interrupts s\<close> show False by contradiction
      qed
    qed
  next
    case (redT_acquire x n ln)
    show False
    proof(cases "\<exists>w. wset s t = \<lfloor>InWS w\<rfloor>")
      case True with \<open>\<not> waiting (wset s t)\<close> show ?thesis
        by(auto simp add: not_waiting_iff)
    next
      case False
      with dead \<open>thr s t = \<lfloor>(x, ln)\<rfloor>\<close> \<open>0 < ln $ n\<close>
      obtain l t' where "0 < ln $ l" "t \<noteq> t'"
        and "has_lock (locks s $ l) t'"
        by(cases)(fastforce simp add: waiting_def)+
      hence "\<not> may_acquire_all (locks s) t ln"
        by(auto elim: may_acquire_allE dest: has_lock_may_lock_t_eq)
      with \<open>may_acquire_all (locks s) t ln\<close> show ?thesis by contradiction
    qed
  qed
qed

lemma deadlocked'_no_red:
  "\<lbrakk> s -t\<triangleright>ta\<rightarrow> s'; deadlocked' s \<rbrakk> \<Longrightarrow> False"
apply(rule red_no_deadlock)
 apply(assumption)
apply(erule deadlocked'D2)
by(rule red_not_final_thread)

lemma not_final_thread_deadlocked_final_thread [iff]: 
  "thr s t = \<lfloor>xln\<rfloor> \<Longrightarrow> not_final_thread s t \<or> t \<in> deadlocked s \<or> final_thread s t"
by(auto simp add: not_final_thread_final_thread_conv[symmetric])

lemma all_waiting_deadlocked:
  assumes "not_final_thread s t"
  and "lock_thread_ok (locks s) (thr s)" 
  and normal: "\<And>t x. \<lbrakk> thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; \<not> final x; wset s t = None \<rbrakk> 
               \<Longrightarrow> t \<turnstile> \<langle>x, shr s\<rangle> \<wrong> \<and> (\<forall>LT. t \<turnstile> \<langle>x, shr s\<rangle> LT \<wrong> \<longrightarrow> (\<exists>lt\<in>LT. must_wait s t lt (final_threads s)))"
  and acquire: "\<And>t x ln l. \<lbrakk> thr s t = \<lfloor>(x, ln)\<rfloor>; \<not> waiting (wset s t); ln $ l > 0 \<rbrakk>
                \<Longrightarrow> \<exists>l'. ln $ l' > 0 \<and> \<not> may_lock (locks s $ l') t"
  and wakeup: "\<And>t x w. thr s t = \<lfloor>(x, no_wait_locks)\<rfloor> \<Longrightarrow> wset s t \<noteq> \<lfloor>PostWS w\<rfloor>"
  shows "t \<in> deadlocked s"
proof -
  from \<open>not_final_thread s t\<close>
  have "t \<in> {t. not_final_thread s t}" by simp
  thus ?thesis
  proof(coinduct)
    case (deadlocked z)
    hence "not_final_thread s z" by simp
    then obtain x' ln' where "thr s z = \<lfloor>(x', ln')\<rfloor>" by(fastforce elim!: not_final_thread_existsE)
    {
      assume "wset s z = None" "\<not> final x'"
        and [simp]: "ln' = no_wait_locks"
      with \<open>thr s z = \<lfloor>(x', ln')\<rfloor>\<close>
      have "z \<turnstile> \<langle>x', shr s\<rangle> \<wrong> \<and> (\<forall>LT. z \<turnstile> \<langle>x', shr s\<rangle> LT \<wrong> \<longrightarrow> (\<exists>lt \<in> LT. must_wait s z lt (final_threads s)))"
        by(auto dest: normal)
      then obtain "z \<turnstile> \<langle>x', shr s\<rangle> \<wrong>"
        and clnml: "\<And>LT. z \<turnstile> \<langle>x', shr s\<rangle> LT \<wrong> \<Longrightarrow> \<exists>lt \<in> LT. must_wait s z lt (final_threads s)" by(blast)
      { fix LT
        assume "z \<turnstile> \<langle>x', shr s\<rangle> LT \<wrong>"
        then obtain lt where mw: "must_wait s z lt (final_threads s)" and lt: "lt \<in> LT"
          by(blast dest: clnml)
        from mw have "must_wait s z lt ({t. not_final_thread s t} \<union> deadlocked s \<union> final_threads s)"
          by(blast intro: must_wait_mono')
        with lt have "\<exists>lt \<in> LT. must_wait s z lt ({t. not_final_thread s t} \<union> deadlocked s \<union> final_threads s)"
          by blast }
      with \<open>z \<turnstile> \<langle>x', shr s\<rangle> \<wrong>\<close> \<open>thr s z = \<lfloor>(x', ln')\<rfloor>\<close> \<open>wset s z = None\<close> have ?case by(simp) }
    note c1 = this
    { 
      assume wsz: "\<not> waiting (wset s z)"
        and "ln' \<noteq> no_wait_locks"
      from \<open>ln' \<noteq> no_wait_locks\<close> obtain l where "0 < ln' $ l"
        by(auto simp add: neq_no_wait_locks_conv)
      with wsz \<open>thr s z = \<lfloor>(x', ln')\<rfloor>\<close> 
      obtain l' where "0 < ln' $ l'" "\<not> may_lock (locks s $ l') z"
        by(blast dest: acquire)
      then obtain t'' where "t'' \<noteq> z" "has_lock (locks s $ l') t''"
        unfolding not_may_lock_conv by blast
      with \<open>lock_thread_ok (locks s) (thr s)\<close>
      obtain x'' ln'' where "thr s t'' = \<lfloor>(x'', ln'')\<rfloor>"
        by(auto elim!: lock_thread_ok_has_lockE)
      hence "(not_final_thread s t'' \<or> t'' \<in> deadlocked s) \<or> final_thread s t''"
        by(clarsimp simp add: not_final_thread_iff final_thread_def)
      with wsz \<open>0 < ln' $ l'\<close> \<open>thr s z = \<lfloor>(x', ln')\<rfloor>\<close> \<open>t'' \<noteq> z\<close> \<open>has_lock (locks s $ l') t''\<close>
      have ?Acquire by simp blast
      hence ?case by simp }
    note c2 = this
    { fix w
      assume "waiting (wset s z)"
      with \<open>thr s z = \<lfloor>(x', ln')\<rfloor>\<close>
      have "?Wait" by(clarsimp simp add: all_final_except_def)
      hence ?case by simp }
    note c3 = this
    from \<open>not_final_thread s z\<close> \<open>thr s z = \<lfloor>(x', ln')\<rfloor>\<close> show ?case
    proof(cases rule: not_final_thread_cases2)
      case final show ?thesis
      proof(cases "wset s z")
        case None show ?thesis
        proof(cases "ln' = no_wait_locks")
          case True with None final show ?thesis by(rule c1)
        next
          case False
          from None have "\<not> waiting (wset s z)" by(simp add: not_waiting_iff)
          thus ?thesis using False by(rule c2)
        qed
      next
        case (Some w)
        show ?thesis
        proof(cases w)
          case (InWS w') 
          with Some have "waiting (wset s z)" by(simp add: waiting_def)
          thus ?thesis by(rule c3)
        next
          case (PostWS w')
          with Some have "\<not> waiting (wset s z)" by(simp add: not_waiting_iff)
          moreover from PostWS \<open>thr s z = \<lfloor>(x', ln')\<rfloor>\<close> Some
          have "ln' \<noteq> no_wait_locks" by(auto dest: wakeup)
          ultimately show ?thesis by(rule c2)
        qed
      qed
    next
      case wait_locks show ?thesis
      proof(cases "wset s z")
        case None
        hence "\<not> waiting (wset s z)" by(simp add: not_waiting_iff)
        thus ?thesis using wait_locks by(rule c2)
      next
        case (Some w)
        show ?thesis
        proof(cases w)
          case (InWS w')
          with Some have "waiting (wset s z)" by(simp add: waiting_def)
          thus ?thesis by(rule c3)
        next
          case (PostWS w')
          with Some have "\<not> waiting (wset s z)" by(simp add: not_waiting_iff)
          moreover from PostWS \<open>thr s z = \<lfloor>(x', ln')\<rfloor>\<close> Some
          have "ln' \<noteq> no_wait_locks" by(auto dest: wakeup)
          ultimately show ?thesis by(rule c2)
        qed
      qed
    next
      case (wait_set w)
      show ?thesis
      proof(cases w)
        case (InWS w')
        with wait_set have "waiting (wset s z)" by(simp add: waiting_def)
        thus ?thesis by(rule c3)
      next
        case (PostWS w')
        with wait_set have "\<not> waiting (wset s z)" by(simp add: not_waiting_iff)
        moreover from PostWS \<open>thr s z = \<lfloor>(x', ln')\<rfloor>\<close> wait_set
        have "ln' \<noteq> no_wait_locks" by(auto dest: wakeup[simplified])
        ultimately show ?thesis by(rule c2)
      qed
    qed
  qed
qed

text \<open>Equivalence proof for both notions of deadlock\<close>

lemma deadlock_implies_deadlocked':
  assumes dead: "deadlock s" 
  shows "deadlocked' s"
proof -
  show ?thesis
  proof(rule deadlocked'I)
    fix t
    assume "not_final_thread s t"
    hence "t \<in> {t. not_final_thread s t}" ..
    thus "t \<in> deadlocked s"
    proof(coinduct)
      case (deadlocked t'')
      hence "not_final_thread s t''" ..
      then obtain x'' ln'' where tst'': "thr s t'' = \<lfloor>(x'', ln'')\<rfloor>"
        by(rule not_final_thread_existsE)
      { assume "waiting (wset s t'')"
        moreover
        with tst'' have nfine: "not_final_thread s t''"
          unfolding waiting_def
          by(blast intro: not_final_thread.intros)
        ultimately have ?case using tst''
          by(blast intro: all_final_exceptI not_final_thread_final) }
      note c1 = this
      { 
        assume wst'': "\<not> waiting (wset s t'')"
          and "ln'' \<noteq> no_wait_locks"
        then obtain l where l: "ln'' $ l > 0"
          by(auto simp add: neq_no_wait_locks_conv)
        with dead wst'' tst'' obtain l' T
          where "ln'' $ l' > 0" "t'' \<noteq> T" 
          and hl: "has_lock (locks s $ l') T"
          and tsT: "thr s T \<noteq> None"
          by - (erule deadlockD2)
        moreover from \<open>thr s T \<noteq> None\<close>
        obtain xln where tsT: "thr s T = \<lfloor>xln\<rfloor>" by auto
        then obtain X LN where "thr s T = \<lfloor>(X, LN)\<rfloor>"
          by(cases xln, auto)
        moreover hence "not_final_thread s T \<or> final_thread s T"
          by(auto simp add: final_thread_def not_final_thread_iff)
        ultimately have ?case using wst'' tst'' by blast }
      note c2 = this
      { assume "wset s t'' = None"
        and [simp]: "ln'' = no_wait_locks"
        moreover
        with \<open>not_final_thread s t''\<close> tst''
        have "\<not> final x''" by(auto)
        ultimately obtain "t'' \<turnstile> \<langle>x'', shr s\<rangle> \<wrong>"
          and clnml: "\<And>LT. t'' \<turnstile> \<langle>x'', shr s\<rangle> LT \<wrong> \<Longrightarrow> \<exists>t'. thr s t' \<noteq> None \<and> (\<exists>lt\<in>LT. must_wait s t'' lt (dom (thr s)))"
          using \<open>thr s t'' = \<lfloor>(x'', ln'')\<rfloor>\<close> \<open>deadlock s\<close>
          by(blast elim: deadlockD1)
        { fix LT
          assume "t'' \<turnstile> \<langle>x'', shr s\<rangle> LT \<wrong>"
          then obtain lt where lt: "lt \<in> LT"
            and mw: "must_wait s t'' lt (dom (thr s))"
            by(blast dest: clnml)
          note mw
          also have "dom (thr s) = {t. not_final_thread s t} \<union> deadlocked s \<union> final_threads s"
            by(auto simp add: not_final_thread_conv dest: deadlocked_thread_exists elim: final_threadE)
          finally have "\<exists>lt\<in>LT. must_wait s t'' lt ({t. not_final_thread s t} \<union> deadlocked s \<union> final_threads s)"
            using lt by blast }
        with \<open>t'' \<turnstile> \<langle>x'', shr s\<rangle> \<wrong>\<close> tst'' \<open>wset s t'' = None\<close> have ?case by(simp) }
      note c3 = this
      from \<open>not_final_thread s t''\<close> tst'' show ?case
      proof(cases rule: not_final_thread_cases2)
        case final show ?thesis
        proof(cases "wset s t''")
          case None show ?thesis
          proof(cases "ln'' = no_wait_locks")
            case True with None show ?thesis by(rule c3)
          next
            case False
            from None have "\<not> waiting (wset s t'')" by(simp add: not_waiting_iff)
            thus ?thesis using False by(rule c2)
          qed
        next
          case (Some w)
          show ?thesis
          proof(cases w)
            case (InWS w')
            with Some have "waiting (wset s t'')" by(simp add: waiting_def)
            thus ?thesis by(rule c1)
          next
            case (PostWS w')
            hence "\<not> waiting (wset s t'')" using Some by(simp add: not_waiting_iff)
            moreover from PostWS Some tst''
            have "ln'' \<noteq> no_wait_locks" by(auto dest: deadlockD3[OF dead])
            ultimately show ?thesis by(rule c2)
          qed            
        qed
      next
        case wait_locks show ?thesis
        proof(cases "waiting (wset s t'')")
          case False
          thus ?thesis using wait_locks by(rule c2)
        next
          case True thus ?thesis by(rule c1)
        qed
      next
        case (wait_set w)
        show ?thesis
        proof(cases w)
          case InWS
          with wait_set have "waiting (wset s t'')" by(simp add: waiting_def)
          thus ?thesis by(rule c1)
        next
          case (PostWS w')
          hence "\<not> waiting (wset s t'')" using wait_set
            by(simp add: not_waiting_iff)
          moreover from PostWS wait_set tst''
          have "ln'' \<noteq> no_wait_locks" by(auto dest: deadlockD3[OF dead])
          ultimately show ?thesis by(rule c2)
        qed
      qed
    qed
  qed
qed

lemma deadlocked'_implies_deadlock:
  assumes dead: "deadlocked' s" 
  shows "deadlock s"
proof -
  have deadlocked: "\<And>t. not_final_thread s t \<Longrightarrow> t \<in> deadlocked s"
    using dead by(rule deadlocked'D2)
  show ?thesis
  proof(rule deadlockI)
    fix t' x'
    assume "thr s t' = \<lfloor>(x', no_wait_locks)\<rfloor>"
      and "\<not> final x'"
      and "wset s t' = None"
    hence "not_final_thread s t'" by(auto intro: not_final_thread_final)
    hence "t' \<in> deadlocked s" by(rule deadlocked)
    thus "t' \<turnstile> \<langle>x', shr s\<rangle> \<wrong> \<and> (\<forall>LT. t' \<turnstile> \<langle>x', shr s\<rangle> LT \<wrong> \<longrightarrow> (\<exists>lt \<in> LT. must_wait s t' lt (dom (thr s))))"
    proof(cases rule: deadlocked_elims)
      case (lock x'')
      note lock = \<open>\<And>LT. t' \<turnstile> \<langle>x'', shr s\<rangle> LT \<wrong> \<Longrightarrow> \<exists>lt \<in> LT. must_wait s t' lt (deadlocked s \<union> final_threads s)\<close>
      from \<open>thr s t' = \<lfloor>(x'', no_wait_locks)\<rfloor>\<close> \<open>thr s t' = \<lfloor>(x', no_wait_locks)\<rfloor>\<close>
      have [simp]: "x' = x''" by auto
      { fix LT
        assume "t' \<turnstile> \<langle>x'', shr s\<rangle> LT \<wrong>"
        from lock[OF this] obtain lt where lt: "lt \<in> LT"
          and mw: "must_wait s t' lt (deadlocked s \<union> final_threads s)" by blast
        have "deadlocked s \<union> final_threads s \<subseteq> dom (thr s)"
          by(auto elim: final_threadE dest: deadlocked_thread_exists)
        with mw have "must_wait s t' lt (dom (thr s))" by(rule must_wait_mono')
        with lt have "\<exists>lt\<in>LT. must_wait s t' lt (dom (thr s))" by blast }
      with \<open>t' \<turnstile> \<langle>x'', shr s\<rangle> \<wrong>\<close> show ?thesis by(auto)
    next
      case (wait x'' ln'')
      from \<open>wset s t' = None\<close> \<open>waiting (wset s t')\<close>
      have False by(simp add: waiting_def)
      thus ?thesis ..
    next
      case (acquire x'' ln'' l'' T)
      from \<open>thr s t' = \<lfloor>(x'', ln'')\<rfloor>\<close> \<open>thr s t' = \<lfloor>(x', no_wait_locks)\<rfloor>\<close> \<open>0 < ln'' $ l''\<close>
      have False by(auto)
      thus ?thesis ..
    qed
  next
    fix t' x' ln' l
    assume "thr s t' = \<lfloor>(x', ln')\<rfloor>"
      and "0 < ln' $ l"
      and wst': "\<not> waiting (wset s t')"
    hence "not_final_thread s t'" by(auto intro: not_final_thread_wait_locks)
    hence "t' \<in> deadlocked s" by(rule deadlocked)
    thus "\<exists>l T. 0 < ln' $ l \<and> t' \<noteq> T \<and> thr s T \<noteq> None \<and> has_lock (locks s $ l) T"
    proof(cases rule: deadlocked_elims)
      case (lock x'')
      from \<open>thr s t' = \<lfloor>(x', ln')\<rfloor>\<close> \<open>thr s t' = \<lfloor>(x'', no_wait_locks)\<rfloor>\<close> \<open>0 < ln' $ l\<close>
      have False by auto
      thus ?thesis ..
    next
      case (wait x' ln')
      from wst' \<open>waiting (wset s t')\<close>
      have False by contradiction
      thus ?thesis ..
    next
      case (acquire x'' ln'' l'' t'')
      from \<open>thr s t' = \<lfloor>(x'', ln'')\<rfloor>\<close> \<open>thr s t' = \<lfloor>(x', ln')\<rfloor>\<close>
      have [simp]: "x' = x''" "ln' = ln''" by auto
      moreover from \<open>t'' \<in> deadlocked s \<or> final_thread s t''\<close>
      have "thr s t'' \<noteq> None"
        by(auto elim: deadlocked_thread_exists simp add: final_thread_def)
      with \<open>0 < ln'' $ l''\<close> \<open>has_lock (locks s $ l'') t''\<close> \<open>t' \<noteq> t''\<close> \<open>thr s t' = \<lfloor>(x'', ln'')\<rfloor>\<close>
      show ?thesis by auto
    qed
  next
    fix t x w
    assume tst: "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>"
    show "wset s t \<noteq> \<lfloor>PostWS w\<rfloor>"
    proof
      assume "wset s t = \<lfloor>PostWS w\<rfloor>"
      moreover with tst have "not_final_thread s t"
        by(auto simp add: not_final_thread_iff)
      hence "t \<in> deadlocked s" by(rule deadlocked)
      ultimately show False using tst
        by(auto elim: deadlocked.cases simp add: waiting_def)
    qed
  qed
qed

lemma deadlock_eq_deadlocked':
  "deadlock = deadlocked'"
by(rule ext)(auto intro: deadlock_implies_deadlocked' deadlocked'_implies_deadlock)

lemma deadlock_no_red:
  "\<lbrakk> s -t\<triangleright>ta\<rightarrow> s'; deadlock s \<rbrakk> \<Longrightarrow> False"
unfolding deadlock_eq_deadlocked'
by(rule deadlocked'_no_red)

lemma deadlock_no_active_threads:
  assumes dead: "deadlock s"
  shows "active_threads s = {}"
proof(rule equals0I)
  fix t
  assume active: "t \<in> active_threads s"
  then obtain ta s' where "s -t\<triangleright>ta\<rightarrow> s'" by(auto dest: active_thread_ex_red)
  thus False using dead by(rule deadlock_no_red)
qed

end

locale preserve_deadlocked = multithreaded final r convert_RA 
  for final :: "'x \<Rightarrow> bool"
  and r :: "('l,'t,'x,'m,'w,'o) semantics" ("_ \<turnstile> _ -_\<rightarrow> _" [50,0,0,50] 80) 
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  +
  fixes wf_state :: "('l,'t,'x,'m,'w) state set"
  assumes invariant3p_wf_state: "invariant3p redT wf_state"
  assumes can_lock_preserved: 
    "\<lbrakk> s \<in> wf_state; s -t'\<triangleright>ta'\<rightarrow> s';
       thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; t \<turnstile> \<langle>x, shr s\<rangle> \<wrong> \<rbrakk>
    \<Longrightarrow> t \<turnstile> \<langle>x, shr s'\<rangle> \<wrong>"
  and can_lock_devreserp:
    "\<lbrakk> s \<in> wf_state; s -t'\<triangleright>ta'\<rightarrow> s';
       thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; t \<turnstile> \<langle>x, shr s'\<rangle> L \<wrong> \<rbrakk>
    \<Longrightarrow> \<exists>L'\<subseteq>L. t \<turnstile> \<langle>x, shr s\<rangle> L' \<wrong>"
begin

lemma redT_deadlocked_subset:
  assumes wfs: "s \<in> wf_state"
  and Red: "s -t\<triangleright>ta\<rightarrow> s'"
  shows "deadlocked s \<subseteq> deadlocked s'"
proof
  fix t'
  assume t'dead: "t' \<in> deadlocked s"
  from Red have tndead: "t \<notin> deadlocked s"
    by(auto dest: red_no_deadlock)
  with t'dead have t't: "t' \<noteq> t" by auto
  { fix t'
    assume "final_thread s t'"
    then obtain x' ln' where tst': "thr s t' = \<lfloor>(x', ln')\<rfloor>" by(auto elim!: final_threadE)
    with \<open>final_thread s t'\<close> have "final x'" 
      and "wset s t' = None" and [simp]: "ln' = no_wait_locks"
      by(auto elim: final_threadE)
    with Red tst' have "t \<noteq> t'" by cases(auto dest: final_no_red)
    with Red tst' have "thr s' t' = \<lfloor>(x', ln')\<rfloor>"
      by cases(auto intro: redT_updTs_Some)
    moreover from Red  \<open>t \<noteq> t'\<close> \<open>wset s t' = None\<close>
    have "wset s' t' = None" by cases(auto simp: redT_updWs_None_implies_None)
    ultimately have "final_thread s' t'" using tst' \<open>final x'\<close>
      by(auto simp add: final_thread_def) }
  hence subset: "deadlocked s \<union> final_threads s \<subseteq> deadlocked s \<union> deadlocked s' \<union> final_threads s'" by(auto)

  from Red show "t' \<in> deadlocked s'"
  proof(cases)
    case (redT_normal x x' m')
    note red = \<open>t \<turnstile> \<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>\<close>
      and tst = \<open>thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>\<close>
      and aok = \<open>actions_ok s t ta\<close>
      and s' = \<open>redT_upd s t ta x' m' s'\<close>
    from red have "\<not> final x" by(auto dest: final_no_red)
    with tndead tst have nafe: "\<not> all_final_except s (deadlocked s)"
      by(fastforce simp add: all_final_except_def not_final_thread_iff)
    from t'dead show ?thesis
    proof(coinduct)
      case (deadlocked t'')
      note t''dead = this
      with Red have t''t: "t'' \<noteq> t"
        by(auto dest: red_no_deadlock)
      from t''dead show ?case
      proof(cases rule: deadlocked_elims)
        case (lock X)
        hence est'': "thr s t'' = \<lfloor>(X, no_wait_locks)\<rfloor>"
          and msE: "t'' \<turnstile> \<langle>X, shr s\<rangle> \<wrong>"
          and csexdead: "\<And>LT. t'' \<turnstile> \<langle>X, shr s\<rangle> LT \<wrong> \<Longrightarrow> \<exists>lt \<in> LT. must_wait s t'' lt (deadlocked s \<union> final_threads s)"
          by auto
        from t''t Red est''
        have es't'': "thr s' t'' = \<lfloor>(X, no_wait_locks)\<rfloor>"
          by(cases s)(cases s', auto elim!: redT_ts_Some_inv)
        note es't'' moreover
        from wfs Red est'' msE have msE': "t'' \<turnstile> \<langle>X, shr s'\<rangle> \<wrong>" by(rule can_lock_preserved)
        moreover
        { fix LT
          assume clL'': "t'' \<turnstile> \<langle>X, shr s'\<rangle> LT \<wrong>"
          with est'' have "\<exists>LT'\<subseteq>LT. t'' \<turnstile> \<langle>X, shr s\<rangle> LT' \<wrong>"
            by(rule can_lock_devreserp[OF wfs Red])
          then obtain LT' where clL': "t'' \<turnstile> \<langle>X, shr s\<rangle> LT' \<wrong>"
            and LL': "LT' \<subseteq> LT" by blast
          with csexdead obtain lt
            where lt: "lt \<in> LT" and mw: "must_wait s t'' lt (deadlocked s \<union> final_threads s)"
            by blast
          from mw have "must_wait s' t'' lt (deadlocked s \<union> deadlocked s' \<union> final_threads s')"
          proof(cases rule: must_wait_elims)
            case (lock l t')
            from \<open>t' \<in> deadlocked s \<union> final_threads s\<close> Red have tt': "t \<noteq> t'"
              by(auto dest: red_no_deadlock final_no_redT elim: final_threadE)
            from aok have "lock_actions_ok (locks s $ l) t (\<lbrace>ta\<rbrace>\<^bsub>l\<^esub> $ l)"
              by(auto simp add: lock_ok_las_def)
            with tt' \<open>has_lock (locks s $ l) t'\<close> s'
            have hl't': "has_lock (locks s' $ l) t'" by(auto)
            moreover note \<open>t' \<noteq> t''\<close>
            moreover from \<open>t' \<in> deadlocked s \<union> final_threads s\<close>
            have "t' \<in> (deadlocked s \<union> deadlocked s' \<union> final_threads s')"
              using subset by blast
            ultimately show ?thesis unfolding \<open>lt = Inl l\<close> ..
          next
            case (join t')
            note t'dead = \<open>t' \<in> deadlocked s \<union> final_threads s\<close>
            with Red have tt': "t \<noteq> t'"
              by(auto dest: red_no_deadlock final_no_redT elim: final_threadE)
            note nftt' = \<open>not_final_thread s t'\<close>
            from t'dead Red aok s' tt' have ts't': "thr s' t' = thr s t'"
              by(auto elim!: deadlocked_thread_exists final_threadE intro: redT_updTs_Some)
            from nftt' have "thr s t' \<noteq> None" by auto
            with nftt' t'dead have "t' \<in> deadlocked s"
              by(simp add: not_final_thread_final_thread_conv[symmetric])
            hence "not_final_thread s' t'"
            proof(cases rule: deadlocked_elims)
              case (lock x'')
              from \<open>t' \<turnstile> \<langle>x'', shr s\<rangle> \<wrong>\<close> have "\<not> final x''"
                by(auto elim: must_syncE dest: final_no_red)
              with \<open>thr s t' = \<lfloor>(x'', no_wait_locks)\<rfloor>\<close> ts't' show ?thesis
                by(auto intro: not_final_thread.intros)
            next
              case (wait x'' ln'')
              from \<open>\<not> final x\<close> tst \<open>all_final_except s (deadlocked s)\<close>
              have "t \<in> deadlocked s" by(fastforce dest: all_final_exceptD simp add: not_final_thread_iff)
              with Red have False by(auto dest: red_no_deadlock)
              thus ?thesis ..
            next
              case (acquire x'' ln'' l'' T'')
              from \<open>thr s t' = \<lfloor>(x'', ln'')\<rfloor>\<close> \<open>0 < ln'' $ l''\<close> ts't'
              show ?thesis by(auto intro: not_final_thread.intros(2))
            qed
            moreover from t'dead subset have "t' \<in> deadlocked s \<union> deadlocked s' \<union> final_threads s'" ..
            ultimately show ?thesis unfolding \<open>lt = Inr (Inl t')\<close> ..
          next
            case (interrupt t')
            from tst red aok have "not_final_thread s t"
              by(auto simp add: wset_actions_ok_def not_final_thread_iff split: if_split_asm dest: final_no_red)
            with \<open>all_final_except s (deadlocked s \<union> final_threads s)\<close>
            have "t \<in> deadlocked s \<union> final_threads s" by(rule all_final_exceptD)
            moreover have "t \<notin> deadlocked s" using Red by(blast dest: red_no_deadlock)
            moreover have "\<not> final_thread s t" using red tst by(auto simp add: final_thread_def dest: final_no_red)
            ultimately have False by blast
            thus ?thesis ..
          qed
          with lt have "\<exists>lt\<in>LT. must_wait s' t'' lt (deadlocked s \<union> deadlocked s' \<union> final_threads s')" by blast }
        moreover have "wset s' t'' = None" using s' t''t \<open>wset s t'' = None\<close> 
          by(auto intro: redT_updWs_None_implies_None)
        ultimately show ?thesis by(auto)
      next
        case (wait x ln)
        from \<open>all_final_except s (deadlocked s)\<close> nafe have False by simp
        thus ?thesis by simp
      next
        case (acquire X ln l T)
        from t''t Red \<open>thr s t'' = \<lfloor>(X, ln)\<rfloor>\<close> s'
        have es't'': "thr s' t'' = \<lfloor>(X, ln)\<rfloor>"
          by(cases s)(auto dest: redT_ts_Some_inv)
        moreover
        from \<open>T \<in> deadlocked s \<or> final_thread s T\<close>
        have "T \<noteq> t"
        proof(rule disjE)
          assume "T \<in> deadlocked s"
          with Red show ?thesis by(auto dest: red_no_deadlock)
        next
          assume "final_thread s T"
          with Red show ?thesis
            by(auto dest!: final_no_redT simp add: final_thread_def)
        qed
        with s' tst Red \<open>has_lock (locks s $ l) T\<close> have "has_lock (locks s' $ l) T"
          by -(cases s, auto dest: redT_has_lock_inv[THEN iffD2])
        moreover
        from s' \<open>T \<noteq> t\<close> have wset: "wset s T = None \<Longrightarrow> wset s' T = None"
          by(auto intro: redT_updWs_None_implies_None)
        { fix x
          assume "thr s T = \<lfloor>(x, no_wait_locks)\<rfloor>"
          with \<open>T \<noteq> t\<close> Red s' aok tst have "thr s' T = \<lfloor>(x, no_wait_locks)\<rfloor>"
            by(auto intro: redT_updTs_Some) }
        moreover
        hence "final_thread s T \<Longrightarrow> final_thread s' T"
          by(auto simp add: final_thread_def intro: wset)
        moreover from \<open>\<not> waiting (wset s t'')\<close> s' t''t
        have "\<not> waiting (wset s' t'')"
          by(auto simp add: redT_updWs_None_implies_None redT_updWs_PostWS_imp_PostWS not_waiting_iff)
        ultimately have ?Acquire
          using \<open>0 < ln $ l\<close> \<open>t'' \<noteq> T\<close> \<open>T \<in> deadlocked s \<or> final_thread s T\<close> by(auto)
        thus ?thesis by simp
      qed
    qed
  next
    case (redT_acquire x n ln)
    hence [simp]: "ta = (K$ [], [], [], [], [], convert_RA ln)"
      and s': "s' = (acquire_all (locks s) t ln, (thr s(t \<mapsto> (x, no_wait_locks)), shr s), wset s, interrupts s)"
      and tst: "thr s t = \<lfloor>(x, ln)\<rfloor>" 
      and wst: "\<not> waiting (wset s t)" by auto
    from t'dead show ?thesis
    proof(coinduct)
      case (deadlocked t'')
      note t''dead = this
      with Red have t''t: "t'' \<noteq> t"
        by(auto dest: red_no_deadlock)
      from t''dead show ?case
      proof(cases rule: deadlocked_elims)
        case (lock X)
        note clnml = \<open>\<And>LT. t'' \<turnstile> \<langle>X, shr s\<rangle> LT \<wrong> \<Longrightarrow> \<exists>lt \<in> LT. must_wait s t'' lt (deadlocked s \<union> final_threads s)\<close>
        note tst'' = \<open>thr s t'' = \<lfloor>(X, no_wait_locks)\<rfloor>\<close>
        with s' t''t have ts't'': "thr s' t'' = \<lfloor>(X, no_wait_locks)\<rfloor>" by simp
        moreover 
        { fix LT
          assume "t'' \<turnstile> \<langle>X, shr s'\<rangle> LT \<wrong>"
          hence "t'' \<turnstile> \<langle>X, shr s\<rangle> LT \<wrong>" using s' by simp
          then obtain lt where lt: "lt \<in> LT" and hlnft: "must_wait s t'' lt (deadlocked s \<union> final_threads s)"
            by(blast dest: clnml)
          from hlnft have "must_wait s' t'' lt (deadlocked s \<union> deadlocked s' \<union> final_threads s')"
          proof(cases rule: must_wait_elims)
            case (lock l' T)
            from \<open>has_lock (locks s $ l') T\<close> s'
            have "has_lock (locks s' $ l') T"
              by(auto intro: has_lock_has_lock_acquire_locks)
            moreover note \<open>T \<noteq> t''\<close>
            moreover from \<open>T \<in> deadlocked s \<union> final_threads s\<close>
            have "T \<in> deadlocked s \<union> deadlocked s' \<union> final_threads s'" using subset by blast
            ultimately show ?thesis unfolding \<open>lt = Inl l'\<close> ..
          next
            case (join T)
            from \<open>not_final_thread s T\<close> have "thr s T \<noteq> None"
              by(auto simp add: not_final_thread_iff)
            moreover
            from \<open>T \<in> deadlocked s \<union> final_threads s\<close>
            have "T \<noteq> t"
            proof
              assume "T \<in> deadlocked s"
              with Red show ?thesis by(auto dest: red_no_deadlock)
            next
              assume "T \<in> final_threads s"
              with \<open>0 < ln $ n\<close> tst show ?thesis
                by(auto simp add: final_thread_def)
            qed
            ultimately have "not_final_thread s' T" using \<open>not_final_thread s T\<close> s'
              by(auto simp add: not_final_thread_iff)
            moreover from \<open>T \<in> deadlocked s \<union> final_threads s\<close>
            have "T \<in> deadlocked s \<union> deadlocked s' \<union> final_threads s'" using subset by blast
            ultimately show ?thesis unfolding \<open>lt = Inr (Inl T)\<close> ..
          next
            case (interrupt T)
            from tst wst \<open>0 < ln $ n\<close> have "not_final_thread s t"
              by(auto simp add: waiting_def not_final_thread_iff)
            with \<open>all_final_except s (deadlocked s \<union> final_threads s)\<close>
            have "t \<in> deadlocked s \<union> final_threads s" by(rule all_final_exceptD)
            moreover have "t \<notin> deadlocked s" using Red by(blast dest: red_no_deadlock)
            moreover have "\<not> final_thread s t" using tst \<open>0 < ln $ n\<close> by(auto simp add: final_thread_def)
            ultimately have False by blast
            thus ?thesis ..
          qed
          with lt have "\<exists>lt\<in>LT. must_wait s' t'' lt (deadlocked s \<union> deadlocked s' \<union> final_threads s')" by blast }
        moreover from \<open>wset s t'' = None\<close> s' have "wset s' t'' = None" by simp
        ultimately show ?thesis using \<open>thr s t'' = \<lfloor>(X, no_wait_locks)\<rfloor>\<close> \<open>t'' \<turnstile> \<langle>X, shr s\<rangle> \<wrong>\<close> s' by fastforce
      next
        case (wait X LN)
        have "all_final_except s' (deadlocked s)"
        proof(rule all_final_exceptI)
          fix T
          assume "not_final_thread s' T"
          hence "not_final_thread s T" using wst tst s'
            by(auto simp add: not_final_thread_iff split: if_split_asm)
          with \<open>all_final_except s (deadlocked s)\<close> \<open>thr s t = \<lfloor>(x, ln)\<rfloor>\<close>
          show "T \<in> deadlocked s" by-(erule all_final_exceptD)
        qed
        hence "all_final_except s' (deadlocked s \<union> deadlocked s')"
          by(rule all_final_except_mono') blast
        with t''t \<open>thr s t'' = \<lfloor>(X, LN)\<rfloor>\<close> \<open>waiting (wset s t'')\<close> s' 
        have ?Wait by simp
        thus ?thesis by simp
      next
        case (acquire X LN l T)
        from \<open>thr s t'' = \<lfloor>(X, LN)\<rfloor>\<close> t''t s'
        have "thr s' t'' = \<lfloor>(X, LN)\<rfloor>" by(simp)
        moreover from \<open>T \<in> deadlocked s \<or> final_thread s T\<close> s' tst 
        have "T \<in> deadlocked s \<or> final_thread s' T"
          by(clarsimp simp add: final_thread_def)
        moreover from \<open>has_lock (locks s $ l) T\<close> s'
        have "has_lock (locks s' $ l) T"
          by(auto intro: has_lock_has_lock_acquire_locks)
        moreover have "\<not> waiting (wset s' t'')" using \<open>\<not> waiting (wset s t'')\<close> s' by simp
        ultimately show ?thesis using \<open>0 < LN $ l\<close> \<open>t'' \<noteq> T\<close> by blast
      qed
    qed
  qed
qed

corollary RedT_deadlocked_subset:
  assumes wfs: "s \<in> wf_state"
  and Red: "s -\<triangleright>ttas\<rightarrow>* s'"
  shows "deadlocked s \<subseteq> deadlocked s'"
using Red 
apply(induct rule: RedT_induct')
apply(unfold RedT_def)
apply(blast dest: invariant3p_rtrancl3p[OF invariant3p_wf_state _ wfs] redT_deadlocked_subset)+
done

end

end
