(*  Title:      JinjaThreads/Execute/Round_Robin.thy
    Author:     Andreas Lochbihler
*)

section \<open>Round robin scheduler\<close>

theory Round_Robin
imports
  Scheduler
begin

text \<open>
  A concrete scheduler must pick one possible reduction step from the small-step semantics for invidivual threads.
  Currently, this is only possible if there is only one such by using @{term Predicate.the}.
\<close>

subsection \<open>Concrete schedulers\<close>

subsection \<open>Round-robin schedulers\<close>

type_synonym 'queue round_robin = "'queue \<times> nat"
  \<comment> \<open>Waiting queue of threads and remaining number of steps of the first thread until it has to return resources\<close>

primrec enqueue_new_thread :: "'t list \<Rightarrow> ('t,'x,'m) new_thread_action \<Rightarrow> 't list"
where 
  "enqueue_new_thread queue (NewThread t x m) = queue @ [t]"
| "enqueue_new_thread queue (ThreadExists t b) = queue"

definition enqueue_new_threads :: "'t list \<Rightarrow> ('t,'x,'m) new_thread_action list \<Rightarrow> 't list"
where
  "enqueue_new_threads = foldl enqueue_new_thread"

primrec round_robin_update_state :: "nat \<Rightarrow> 't list round_robin \<Rightarrow> 't \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 't list round_robin"
where 
  "round_robin_update_state n0 (queue, n) t ta =
   (let queue' = enqueue_new_threads queue \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>
    in if n = 0 \<or> Yield \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> then (rotate1 queue', n0) else (queue', n - 1))"

context multithreaded_base begin

abbreviation round_robin_step :: "nat \<Rightarrow> 't list round_robin \<Rightarrow> ('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> ('t \<times> (('l,'t,'x,'m,'w,'o) thread_action \<times> 'x \<times> 'm) option \<times> 't list round_robin) option"
where
  "round_robin_step n0 \<sigma> s t \<equiv> step_thread (round_robin_update_state n0 \<sigma> t) s t"

partial_function (option) round_robin_reschedule :: "'t \<Rightarrow> 
    't list \<Rightarrow> nat \<Rightarrow> ('l,'t,'x,'m,'w) state \<Rightarrow> ('t \<times> (('l,'t,'x,'m,'w,'o) thread_action \<times> 'x \<times> 'm) option \<times> 't list round_robin) option"
where
  "round_robin_reschedule t0 queue n0 s =
   (let
      t = hd queue;
      queue' = tl queue
    in
      if t = t0 then
        None
      else
        case round_robin_step n0 (t # queue', n0) s t of
          None \<Rightarrow> round_robin_reschedule t0 (queue' @ [t]) n0 s
        | \<lfloor>ttaxm\<sigma>\<rfloor> \<Rightarrow> \<lfloor>ttaxm\<sigma>\<rfloor>)"

fun round_robin :: "nat \<Rightarrow> 't list round_robin \<Rightarrow> ('l,'t,'x,'m,'w) state \<Rightarrow> ('t \<times> (('l,'t,'x,'m,'w,'o) thread_action \<times> 'x \<times> 'm) option \<times> 't list round_robin) option"
where 
  "round_robin n0 ([], n) s = None"
| "round_robin n0 (t # queue, n) s =
   (case round_robin_step n0 (t # queue, n) s t of
      \<lfloor>ttaxm\<sigma>\<rfloor> \<Rightarrow> \<lfloor>ttaxm\<sigma>\<rfloor>
    | None \<Rightarrow> round_robin_reschedule t (queue @ [t]) n0 s)"

end

primrec round_robin_invar :: "'t list round_robin \<Rightarrow> 't set \<Rightarrow> bool"
where "round_robin_invar (queue, n) T \<longleftrightarrow> set queue = T \<and> distinct queue"

lemma set_enqueue_new_thread: 
  "set (enqueue_new_thread queue nta) = set queue \<union> {t. \<exists>x m. nta = NewThread t x m}"
by(cases nta) auto

lemma set_enqueue_new_threads: 
  "set (enqueue_new_threads queue ntas) = set queue \<union> {t. \<exists>x m. NewThread t x m \<in> set ntas}"
apply(induct ntas arbitrary: queue)
apply(auto simp add: enqueue_new_threads_def set_enqueue_new_thread)
done

lemma enqueue_new_thread_eq_Nil [simp]:
  "enqueue_new_thread queue nta = [] \<longleftrightarrow> queue = [] \<and> (\<exists>t b. nta = ThreadExists t b)"
by(cases nta) simp_all

lemma enqueue_new_threads_eq_Nil [simp]:
  "enqueue_new_threads queue ntas = [] \<longleftrightarrow> queue = [] \<and> set ntas \<subseteq> {ThreadExists t b|t b. True}"
apply(induct ntas arbitrary: queue)
apply(auto simp add: enqueue_new_threads_def)
done

lemma distinct_enqueue_new_threads:
  fixes ts :: "('l,'t,'x) thread_info"
  and ntas :: "('t,'x,'m) new_thread_action list"
  assumes "thread_oks ts ntas" "set queue = dom ts" "distinct queue"
  shows "distinct (enqueue_new_threads queue ntas)"
using assms
proof(induct ntas arbitrary: ts queue)
  case Nil thus ?case by(simp add: enqueue_new_threads_def)
next
  case (Cons nt ntas)
  from \<open>thread_oks ts (nt # ntas)\<close>
  have "thread_ok ts nt" and "thread_oks (redT_updT ts nt) ntas" by simp_all
  from \<open>thread_ok ts nt\<close> \<open>set queue = dom ts\<close> \<open>distinct queue\<close>
  have "set (enqueue_new_thread queue nt) = dom (redT_updT ts nt) \<and> distinct (enqueue_new_thread queue nt)"
    by(cases nt)(auto)
  with \<open>thread_oks (redT_updT ts nt) ntas\<close>
  have "distinct (enqueue_new_threads (enqueue_new_thread queue nt) ntas)"
    by(blast intro: Cons.hyps)
  thus ?case by(simp add: enqueue_new_threads_def)
qed

lemma round_robin_reschedule_induct [consumes 1, case_names head rotate]:
  assumes major: "t0 \<in> set queue"
  and head: "\<And>queue. P (t0 # queue)"
  and rotate: "\<And>queue t. \<lbrakk> t \<noteq> t0; t0 \<in> set queue; P (queue @ [t]) \<rbrakk> \<Longrightarrow> P (t # queue)"
  shows "P queue"
using major
proof(induct n\<equiv>"length (takeWhile (\<lambda>x. x\<noteq>t0) queue)" arbitrary: queue)
  case 0
  then obtain queue' where "queue = t0 # queue'"
    by(cases queue)(auto split: if_split_asm)
  thus ?case by(simp add: head)
next
  case (Suc n)
  then obtain t queue' where [simp]: "queue = t # queue'"
    and t: "t \<noteq> t0" and n: "n = length (takeWhile (\<lambda>x. x \<noteq> t0) queue')"
    and t0: "t0 \<in> set queue'"
    by(cases queue)(auto split: if_split_asm)
  from n t0 have "n = length (takeWhile (\<lambda>x. x \<noteq> t0) (queue' @ [t]))" by(simp)
  moreover from t0 have "t0 \<in> set (queue' @ [t])" by simp
  ultimately have "P (queue' @ [t])" by(rule Suc.hyps)
  with t t0 show ?case by(simp add: rotate)
qed

context multithreaded_base begin

declare actions_ok_iff [simp del]
declare actions_ok.cases [rule del]

lemma round_robin_step_invar_None:
  "\<lbrakk> round_robin_step n0 \<sigma> s t' = \<lfloor>(t, None, \<sigma>')\<rfloor>; round_robin_invar \<sigma> (dom (thr s)) \<rbrakk>
  \<Longrightarrow> round_robin_invar \<sigma>' (dom (thr s))"
by(cases \<sigma>)(auto dest: step_thread_Some_NoneD simp add: set_enqueue_new_threads distinct_enqueue_new_threads)

lemma round_robin_step_invar_Some:
  "\<lbrakk> deterministic I; round_robin_step n0 \<sigma> s t' = \<lfloor>(t, \<lfloor>(ta, x', m')\<rfloor>, \<sigma>')\<rfloor>; round_robin_invar \<sigma> (dom (thr s)); s \<in> I \<rbrakk>
  \<Longrightarrow> round_robin_invar \<sigma>' (dom (thr s) \<union> {t. \<exists>x m. NewThread t x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>})"
apply(cases \<sigma>)
apply clarsimp
apply(frule (1) step_thread_Some_SomeD)
apply(auto split: if_split_asm simp add: split_beta set_enqueue_new_threads deterministic_THE)
apply(auto simp add: actions_ok_iff distinct_enqueue_new_threads)
done

lemma round_robin_reschedule_Cons:
  "round_robin_reschedule t0 (t0 # queue) n0 s = None"
  "t \<noteq> t0 \<Longrightarrow> round_robin_reschedule t0 (t # queue) n0 s =
   (case round_robin_step n0 (t # queue, n0) s t of
      None \<Rightarrow> round_robin_reschedule t0 (queue @ [t]) n0 s
    | Some ttaxm\<sigma> \<Rightarrow> Some ttaxm\<sigma>)"
by(simp_all add: round_robin_reschedule.simps)

lemma round_robin_reschedule_NoneD:
  assumes rrr: "round_robin_reschedule t0 queue n0 s = None"
  and t0: "t0 \<in> set queue"
  shows "set (takeWhile (\<lambda>t'. t' \<noteq> t0) queue) \<inter> active_threads s = {}"
using t0 rrr
proof(induct queue rule: round_robin_reschedule_induct)
  case (head queue)
  thus ?case by simp
next
  case (rotate queue t)
  from \<open>round_robin_reschedule t0 (t # queue) n0 s = None\<close> \<open>t \<noteq> t0\<close>
  have "round_robin_step n0 (t # queue, n0) s t = None" 
    and "round_robin_reschedule t0 (queue @ [t]) n0 s = None"
    by(simp_all add: round_robin_reschedule_Cons)
  from this(1) have "t \<notin> active_threads s" by(rule step_thread_NoneD)
  moreover from \<open>round_robin_reschedule t0 (queue @ [t]) n0 s = None\<close> 
  have "set (takeWhile (\<lambda>t'. t' \<noteq> t0) (queue @ [t])) \<inter> active_threads s = {}"
    by(rule rotate.hyps)
  moreover have "takeWhile (\<lambda>t'. t' \<noteq> t0) (queue @ [t]) = takeWhile (\<lambda>t'. t' \<noteq> t0) queue"
    using \<open>t0 \<in> set queue\<close> by simp
  ultimately show ?case using \<open>t \<noteq> t0\<close> by simp
qed

lemma round_robin_reschedule_Some_NoneD:
  assumes rrr: "round_robin_reschedule t0 queue n0 s = \<lfloor>(t, None, \<sigma>')\<rfloor>"
  and t0: "t0 \<in> set queue"
  shows "\<exists>x ln n. thr s t = \<lfloor>(x, ln)\<rfloor> \<and> ln $ n > 0 \<and> \<not> waiting (wset s t) \<and> may_acquire_all (locks s) t ln"
using t0 rrr
proof(induct queue rule: round_robin_reschedule_induct)
  case head thus ?case by(simp add: round_robin_reschedule_Cons)
next
  case (rotate queue t')
  show ?case
  proof(cases "round_robin_step n0 (t' # queue, n0) s t'")
    case None
    with \<open>round_robin_reschedule t0 (t' # queue) n0 s = \<lfloor>(t, None, \<sigma>')\<rfloor>\<close> \<open>t' \<noteq> t0\<close>
    have "round_robin_reschedule t0 (queue @ [t']) n0 s = \<lfloor>(t, None, \<sigma>')\<rfloor>"
      by(simp add: round_robin_reschedule_Cons)
    thus ?thesis by(rule rotate.hyps)
  next
    case (Some a)
    with \<open>round_robin_reschedule t0 (t' # queue) n0 s = \<lfloor>(t, None, \<sigma>')\<rfloor>\<close> \<open>t' \<noteq> t0\<close>
    have "round_robin_step n0 (t' # queue, n0) s t' = \<lfloor>(t, None, \<sigma>')\<rfloor>"
      by(simp add: round_robin_reschedule_Cons)
    thus ?thesis by(blast dest: step_thread_Some_NoneD)
  qed
qed

lemma round_robin_reschedule_Some_SomeD:
  assumes "deterministic I"
  and rrr: "round_robin_reschedule t0 queue n0 s = \<lfloor>(t, \<lfloor>(ta, x', m')\<rfloor>, \<sigma>')\<rfloor>"
  and t0: "t0 \<in> set queue"
  and I: "s \<in> I"
  shows "\<exists>x. thr s t = \<lfloor>(x, no_wait_locks)\<rfloor> \<and> t \<turnstile> \<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<and> actions_ok s t ta"
using t0 rrr
proof(induct queue rule: round_robin_reschedule_induct)
  case head thus ?case by(simp add: round_robin_reschedule_Cons)
next
  case (rotate queue t')
  show ?case
  proof(cases "round_robin_step n0 (t' # queue, n0) s t'")
    case None
    with \<open>round_robin_reschedule t0 (t' # queue) n0 s = \<lfloor>(t, \<lfloor>(ta, x', m')\<rfloor>, \<sigma>')\<rfloor>\<close> \<open>t' \<noteq> t0\<close>
    have "round_robin_reschedule t0 (queue @ [t']) n0 s = \<lfloor>(t, \<lfloor>(ta, x', m')\<rfloor>, \<sigma>')\<rfloor>"
      by(simp add: round_robin_reschedule_Cons)
    thus ?thesis by(rule rotate.hyps)
  next
    case (Some a)
    with \<open>round_robin_reschedule t0 (t' # queue) n0 s = \<lfloor>(t, \<lfloor>(ta, x', m')\<rfloor>, \<sigma>')\<rfloor>\<close> \<open>t' \<noteq> t0\<close>
    have "round_robin_step n0 (t' # queue, n0) s t' = \<lfloor>(t, \<lfloor>(ta, x', m')\<rfloor>, \<sigma>')\<rfloor>"
      by(simp add: round_robin_reschedule_Cons)
    thus ?thesis using I by(blast dest: step_thread_Some_SomeD[OF \<open>deterministic I\<close>])
  qed
qed

lemma round_robin_reschedule_invar_None:
  assumes rrr: "round_robin_reschedule t0 queue n0 s = \<lfloor>(t, None, \<sigma>')\<rfloor>"
  and invar: "round_robin_invar (queue, n0) (dom (thr s))"
  and t0: "t0 \<in> set queue"
  shows "round_robin_invar \<sigma>' (dom (thr s))"
using t0 rrr invar
proof(induct queue rule: round_robin_reschedule_induct)
  case head thus ?case by(simp add: round_robin_reschedule_Cons)
next
  case (rotate queue t')
  show ?case
  proof(cases "round_robin_step n0 (t' # queue, n0) s t'")
    case None
    with \<open>round_robin_reschedule t0 (t' # queue) n0 s = \<lfloor>(t, None, \<sigma>')\<rfloor>\<close> \<open>t' \<noteq> t0\<close>
    have "round_robin_reschedule t0 (queue @ [t']) n0 s = \<lfloor>(t, None, \<sigma>')\<rfloor>"
      by(simp add: round_robin_reschedule_Cons)
    moreover from \<open>round_robin_invar (t' # queue, n0) (dom (thr s))\<close>
    have "round_robin_invar (queue @ [t'], n0) (dom (thr s))" by simp
    ultimately show ?thesis by(rule rotate.hyps)
  next
    case (Some a)
    with \<open>round_robin_reschedule t0 (t' # queue) n0 s = \<lfloor>(t, None, \<sigma>')\<rfloor>\<close> \<open>t' \<noteq> t0\<close>
    have "round_robin_step n0 (t' # queue, n0) s t' = \<lfloor>(t, None, \<sigma>')\<rfloor>"
      by(simp add: round_robin_reschedule_Cons)
    thus ?thesis using \<open>round_robin_invar (t' # queue, n0) (dom (thr s))\<close>
      by(rule round_robin_step_invar_None)
  qed
qed

lemma round_robin_reschedule_invar_Some:
  assumes "deterministic I"
  and rrr: "round_robin_reschedule t0 queue n0 s = \<lfloor>(t, \<lfloor>(ta, x', m')\<rfloor>, \<sigma>')\<rfloor>"
  and invar: "round_robin_invar (queue, n0) (dom (thr s))"
  and t0: "t0 \<in> set queue"
  and "s \<in> I"
  shows "round_robin_invar \<sigma>' (dom (thr s) \<union> {t. \<exists>x m. NewThread t x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>})"
using t0 rrr invar
proof(induct queue rule: round_robin_reschedule_induct)
  case head thus ?case by(simp add: round_robin_reschedule_Cons)
next
  case (rotate queue t')
  show ?case
  proof(cases "round_robin_step n0 (t' # queue, n0) s t'")
    case None
    with \<open>round_robin_reschedule t0 (t' # queue) n0 s = \<lfloor>(t, \<lfloor>(ta, x', m')\<rfloor>, \<sigma>')\<rfloor>\<close> \<open>t' \<noteq> t0\<close>
    have "round_robin_reschedule t0 (queue @ [t']) n0 s = \<lfloor>(t, \<lfloor>(ta, x', m')\<rfloor>, \<sigma>')\<rfloor>"
      by(simp add: round_robin_reschedule_Cons)
    moreover from \<open>round_robin_invar (t' # queue, n0) (dom (thr s))\<close>
    have "round_robin_invar (queue @ [t'], n0) (dom (thr s))" by simp
    ultimately show ?thesis by(rule rotate.hyps)
  next
    case (Some a)
    with \<open>round_robin_reschedule t0 (t' # queue) n0 s = \<lfloor>(t, \<lfloor>(ta, x', m')\<rfloor>, \<sigma>')\<rfloor>\<close> \<open>t' \<noteq> t0\<close>
    have "round_robin_step n0 (t' # queue, n0) s t' = \<lfloor>(t, \<lfloor>(ta, x', m')\<rfloor>, \<sigma>')\<rfloor>"
      by(simp add: round_robin_reschedule_Cons)
    thus ?thesis using \<open>round_robin_invar (t' # queue, n0) (dom (thr s))\<close> \<open>s \<in> I\<close>
      by(rule round_robin_step_invar_Some[OF \<open>deterministic I\<close>])
  qed
qed

lemma round_robin_NoneD: 
  assumes rr: "round_robin n0 \<sigma> s = None"
  and invar: "round_robin_invar \<sigma> (dom (thr s))"
  shows "active_threads s = {}"
proof -
  obtain queue n where \<sigma>: "\<sigma> = (queue, n)" by(cases \<sigma>)
  show ?thesis
  proof(cases queue)
    case Nil
    thus ?thesis using invar \<sigma> by(fastforce elim: active_threads.cases)
  next
    case (Cons t queue')
    with rr \<sigma> have "round_robin_step n0 (t # queue', n) s t = None"
      and "round_robin_reschedule t (queue' @ [t]) n0 s = None" by simp_all
    from \<open>round_robin_step n0 (t # queue', n) s t = None\<close>
    have "t \<notin> active_threads s" by(rule step_thread_NoneD)
    moreover from \<open>round_robin_reschedule t (queue' @ [t]) n0 s = None\<close>
    have "set (takeWhile (\<lambda>x. x \<noteq> t) (queue' @ [t])) \<inter> active_threads s = {}"
      by(rule round_robin_reschedule_NoneD) simp
    moreover from invar \<sigma> Cons
    have "takeWhile (\<lambda>x. x \<noteq> t) (queue' @ [t]) = queue'"
      by(subst takeWhile_append2) auto
    moreover from invar have "active_threads s \<subseteq> set queue"
      using \<sigma> by(auto elim: active_threads.cases)
    ultimately show ?thesis using Cons by auto
  qed
qed

lemma round_robin_Some_NoneD:
  assumes rr: "round_robin n0 \<sigma> s = \<lfloor>(t, None, \<sigma>')\<rfloor>"
  shows "\<exists>x ln n. thr s t = \<lfloor>(x, ln)\<rfloor> \<and> ln $ n > 0 \<and> \<not> waiting (wset s t) \<and> may_acquire_all (locks s) t ln"
proof -
  obtain queue n where \<sigma>: "\<sigma> = (queue, n)" by(cases \<sigma>)
  with rr have "queue \<noteq> []" by clarsimp
  then obtain t' queue' where queue: "queue = t' # queue'"
    by(auto simp add: neq_Nil_conv)
  show ?thesis
  proof(cases "round_robin_step n0 (t' # queue', n) s t'")
    case (Some a)
    with rr queue \<sigma> have "round_robin_step n0 (t' # queue', n) s t' = \<lfloor>(t, None, \<sigma>')\<rfloor>" by simp
    thus ?thesis by(blast dest: step_thread_Some_NoneD)
  next
    case None
    with rr queue \<sigma> have "round_robin_reschedule t' (queue' @ [t']) n0 s = \<lfloor>(t, None, \<sigma>')\<rfloor>" by simp
    thus ?thesis by(rule round_robin_reschedule_Some_NoneD)simp
  qed
qed

lemma round_robin_Some_SomeD:
  assumes "deterministic I"
  and rr: "round_robin n0 \<sigma> s = \<lfloor>(t, \<lfloor>(ta, x', m')\<rfloor>, \<sigma>')\<rfloor>"
  and "s \<in> I"
  shows "\<exists>x. thr s t = \<lfloor>(x, no_wait_locks)\<rfloor> \<and> t \<turnstile> \<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle> \<and> actions_ok s t ta"
proof -
  obtain queue n where \<sigma>: "\<sigma> = (queue, n)" by(cases \<sigma>)
  with rr have "queue \<noteq> []" by clarsimp
  then obtain t' queue' where queue: "queue = t' # queue'"
    by(auto simp add: neq_Nil_conv)
  show ?thesis
  proof(cases "round_robin_step n0 (t' # queue', n) s t'")
    case (Some a)
    with rr queue \<sigma> have "round_robin_step n0 (t' # queue', n) s t' = \<lfloor>(t, \<lfloor>(ta, x', m')\<rfloor>, \<sigma>')\<rfloor>" by simp
    thus ?thesis using \<open>s \<in> I\<close> by(blast dest: step_thread_Some_SomeD[OF \<open>deterministic I\<close>])
  next
    case None
    with rr queue \<sigma> have "round_robin_reschedule t' (queue' @ [t']) n0 s = \<lfloor>(t, \<lfloor>(ta, x', m')\<rfloor>, \<sigma>')\<rfloor>" by simp
    thus ?thesis by(rule round_robin_reschedule_Some_SomeD[OF \<open>deterministic I\<close>])(simp_all add: \<open>s \<in> I\<close>)
  qed
qed

lemma round_robin_invar_None:
  assumes rr: "round_robin n0 \<sigma> s = \<lfloor>(t, None, \<sigma>')\<rfloor>"
  and invar: "round_robin_invar \<sigma> (dom (thr s))"
  shows "round_robin_invar \<sigma>' (dom (thr s))"
proof -
  obtain queue n where \<sigma>: "\<sigma> = (queue, n)" by(cases \<sigma>)
  with rr have "queue \<noteq> []" by clarsimp
  then obtain t' queue' where queue: "queue = t' # queue'"
    by(auto simp add: neq_Nil_conv)
  show ?thesis
  proof(cases "round_robin_step n0 (t' # queue', n) s t'")
    case (Some a)
    with rr queue \<sigma> have "round_robin_step n0 (t' # queue', n) s t' = \<lfloor>(t, None, \<sigma>')\<rfloor>" by simp
    thus ?thesis using invar unfolding \<sigma> queue by(rule round_robin_step_invar_None)
  next
    case None
    with rr queue \<sigma> have "round_robin_reschedule t' (queue' @ [t']) n0 s = \<lfloor>(t, None, \<sigma>')\<rfloor>" by simp
    moreover from invar queue \<sigma> have "round_robin_invar (queue' @ [t'], n0) (dom (thr s))" by simp
    ultimately show ?thesis by(rule round_robin_reschedule_invar_None) simp
  qed
qed

lemma round_robin_invar_Some:
  assumes "deterministic I"
  and rr: "round_robin n0 \<sigma> s = \<lfloor>(t, \<lfloor>(ta, x', m')\<rfloor>, \<sigma>')\<rfloor>"
  and invar: "round_robin_invar \<sigma> (dom (thr s))" "s \<in> I"
  shows "round_robin_invar \<sigma>' (dom (thr s) \<union> {t. \<exists>x m. NewThread t x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>})"
proof -
  obtain queue n where \<sigma>: "\<sigma> = (queue, n)" by(cases \<sigma>)
  with rr have "queue \<noteq> []" by clarsimp
  then obtain t' queue' where queue: "queue = t' # queue'"
    by(auto simp add: neq_Nil_conv)
  show ?thesis
  proof(cases "round_robin_step n0 (t' # queue', n) s t'")
    case (Some a)
    with rr queue \<sigma> have "round_robin_step n0 (t' # queue', n) s t' = \<lfloor>(t, \<lfloor>(ta, x', m')\<rfloor>, \<sigma>')\<rfloor>" by simp
    thus ?thesis using invar unfolding \<sigma> queue by(rule round_robin_step_invar_Some[OF \<open>deterministic I\<close>])
  next
    case None
    with rr queue \<sigma> have "round_robin_reschedule t' (queue' @ [t']) n0 s = \<lfloor>(t, \<lfloor>(ta, x', m')\<rfloor>, \<sigma>')\<rfloor>" by simp
    moreover from invar queue \<sigma>
    have "round_robin_invar (queue' @ [t'], n0) (dom (thr s))" by simp
    ultimately show ?thesis by(rule round_robin_reschedule_invar_Some[OF \<open>deterministic I\<close>])(simp_all add: \<open>s \<in> I\<close>)
  qed
qed

end

locale round_robin_base =
  scheduler_base_aux
    final r convert_RA
    thr_\<alpha> thr_invar thr_lookup thr_update
    ws_\<alpha> ws_invar ws_lookup
    is_\<alpha> is_invar is_memb is_ins is_delete
  for final :: "'x \<Rightarrow> bool"
  and r :: "'t \<Rightarrow> ('x \<times> 'm) \<Rightarrow> (('l,'t,'x,'m,'w,'o) thread_action \<times> 'x \<times> 'm) Predicate.pred"
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and "output" :: "'queue round_robin \<Rightarrow> 't \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 'q option"
  and thr_\<alpha> :: "'m_t \<Rightarrow> ('l,'t,'x) thread_info"
  and thr_invar :: "'m_t \<Rightarrow> bool"
  and thr_lookup :: "'t \<Rightarrow> 'm_t \<rightharpoonup> ('x \<times> 'l released_locks)"
  and thr_update :: "'t \<Rightarrow> 'x \<times> 'l released_locks \<Rightarrow> 'm_t \<Rightarrow> 'm_t"
  and ws_\<alpha> :: "'m_w \<Rightarrow> ('w,'t) wait_sets"
  and ws_invar :: "'m_w \<Rightarrow> bool"
  and ws_lookup :: "'t \<Rightarrow> 'm_w \<rightharpoonup> 'w wait_set_status"
  and ws_update :: "'t \<Rightarrow> 'w wait_set_status \<Rightarrow> 'm_w \<Rightarrow> 'm_w"
  and ws_delete :: "'t \<Rightarrow> 'm_w \<Rightarrow> 'm_w"
  and ws_iterate :: "'m_w \<Rightarrow> ('t \<times> 'w wait_set_status, 'm_w) set_iterator"
  and ws_sel :: "'m_w \<Rightarrow> ('t \<times> 'w wait_set_status \<Rightarrow> bool) \<rightharpoonup> ('t \<times> 'w wait_set_status)"
  and is_\<alpha> :: "'s_i \<Rightarrow> 't interrupts"
  and is_invar :: "'s_i \<Rightarrow> bool"
  and is_memb :: "'t \<Rightarrow> 's_i \<Rightarrow> bool"
  and is_ins :: "'t \<Rightarrow> 's_i \<Rightarrow> 's_i"
  and is_delete :: "'t \<Rightarrow> 's_i \<Rightarrow> 's_i"
  +
  fixes queue_\<alpha> :: "'queue \<Rightarrow> 't list"
  and queue_invar :: "'queue \<Rightarrow> bool"
  and queue_empty :: "unit \<Rightarrow> 'queue"
  and queue_isEmpty :: "'queue \<Rightarrow> bool"
  and queue_enqueue :: "'t \<Rightarrow> 'queue \<Rightarrow> 'queue"
  and queue_dequeue :: "'queue \<Rightarrow> 't \<times> 'queue"
  and queue_push :: "'t \<Rightarrow> 'queue \<Rightarrow> 'queue"
begin

definition queue_rotate1 :: "'queue \<Rightarrow> 'queue"
where "queue_rotate1 = case_prod queue_enqueue \<circ> queue_dequeue"

primrec enqueue_new_thread :: "'queue \<Rightarrow> ('t,'x,'m) new_thread_action \<Rightarrow> 'queue"
where 
  "enqueue_new_thread ts (NewThread t x m) = queue_enqueue t ts"
| "enqueue_new_thread ts (ThreadExists t b) = ts"

definition enqueue_new_threads :: "'queue \<Rightarrow> ('t,'x,'m) new_thread_action list \<Rightarrow> 'queue"
where
  "enqueue_new_threads = foldl enqueue_new_thread"

primrec round_robin_update_state :: "nat \<Rightarrow> 'queue round_robin \<Rightarrow> 't \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 'queue round_robin"
where 
  "round_robin_update_state n0 (queue, n) t ta =
   (let queue' = enqueue_new_threads queue \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>
    in if n = 0 \<or> Yield \<in> set \<lbrace>ta\<rbrace>\<^bsub>c\<^esub> then (queue_rotate1 queue', n0) else (queue', n - 1))"

abbreviation round_robin_step ::
  "nat \<Rightarrow> 'queue round_robin \<Rightarrow> ('l,'t,'m,'m_t,'m_w,'s_i) state_refine \<Rightarrow> 't 
  \<Rightarrow> ('t \<times> (('l,'t,'x,'m,'w,'o) thread_action \<times> 'x \<times> 'm) option \<times> 'queue round_robin) option"
where
  "round_robin_step n0 \<sigma> s t \<equiv> step_thread (round_robin_update_state n0 \<sigma> t) s t"

partial_function (option) round_robin_reschedule ::
  "'t \<Rightarrow> 'queue \<Rightarrow> nat \<Rightarrow> ('l,'t,'m,'m_t,'m_w,'s_i) state_refine 
  \<Rightarrow> ('t \<times> (('l,'t,'x,'m,'w,'o) thread_action \<times> 'x \<times> 'm) option \<times> 'queue round_robin) option"
where
  "round_robin_reschedule t0 queue n0 s =
   (let
      (t, queue') = queue_dequeue queue
    in
      if t = t0 then
        None 
      else
        case round_robin_step n0 (queue_push t queue', n0) s t of
          None \<Rightarrow> round_robin_reschedule t0 (queue_enqueue t queue') n0 s
        | \<lfloor>ttaxm\<sigma>\<rfloor> \<Rightarrow> \<lfloor>ttaxm\<sigma>\<rfloor>)"

primrec round_robin :: "nat \<Rightarrow> ('l,'t,'x,'m,'w,'o,'m_t,'m_w,'s_i,'queue round_robin) scheduler"
where 
  "round_robin n0 (queue, n) s = 
   (if queue_isEmpty queue then None
    else
      let
        (t, queue') = queue_dequeue queue
      in
        (case round_robin_step n0 (queue_push t queue', n) s t of
           \<lfloor>ttaxm\<sigma>\<rfloor> \<Rightarrow> \<lfloor>ttaxm\<sigma>\<rfloor>
         | None \<Rightarrow> round_robin_reschedule t (queue_enqueue t queue') n0 s))"

primrec round_robin_invar :: "'queue round_robin \<Rightarrow> 't set \<Rightarrow> bool"
where "round_robin_invar (queue, n) T \<longleftrightarrow> queue_invar queue \<and> Round_Robin.round_robin_invar (queue_\<alpha> queue, n) T"

definition round_robin_\<alpha> :: "'queue round_robin \<Rightarrow> 't list round_robin"
where "round_robin_\<alpha> = apfst queue_\<alpha>"

definition round_robin_start :: "nat \<Rightarrow> 't \<Rightarrow> 'queue round_robin"
where "round_robin_start n0 t = (queue_enqueue t (queue_empty ()), n0)"

lemma round_robin_invar_correct:
  "round_robin_invar \<sigma> T \<Longrightarrow> Round_Robin.round_robin_invar (round_robin_\<alpha> \<sigma>) T"
by(cases \<sigma>)(simp add: round_robin_\<alpha>_def)

end

locale round_robin =
  round_robin_base
    final r convert_RA "output"
    thr_\<alpha> thr_invar thr_lookup thr_update
    ws_\<alpha> ws_invar ws_lookup ws_update ws_delete ws_iterate ws_sel
    is_\<alpha> is_invar is_memb is_ins is_delete
    queue_\<alpha> queue_invar queue_empty queue_isEmpty queue_enqueue queue_dequeue queue_push
  +
  scheduler_aux
    final r convert_RA
    thr_\<alpha> thr_invar thr_lookup thr_update
    ws_\<alpha> ws_invar ws_lookup
    is_\<alpha> is_invar is_memb is_ins is_delete
  +
  ws: map_update ws_\<alpha> ws_invar ws_update +
  ws: map_delete ws_\<alpha> ws_invar ws_delete +
  ws: map_iteratei ws_\<alpha> ws_invar ws_iterate +
  ws: map_sel' ws_\<alpha> ws_invar ws_sel +
  queue: list queue_\<alpha> queue_invar +
  queue: list_empty queue_\<alpha> queue_invar queue_empty +
  queue: list_isEmpty queue_\<alpha> queue_invar queue_isEmpty +
  queue: list_enqueue queue_\<alpha> queue_invar queue_enqueue +
  queue: list_dequeue queue_\<alpha> queue_invar queue_dequeue +
  queue: list_push queue_\<alpha> queue_invar queue_push
  for final :: "'x \<Rightarrow> bool"
  and r :: "'t \<Rightarrow> ('x \<times> 'm) \<Rightarrow> (('l,'t,'x,'m,'w,'o) thread_action \<times> 'x \<times> 'm) Predicate.pred"
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and "output" :: "'queue round_robin \<Rightarrow> 't \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 'q option"
  and thr_\<alpha> :: "'m_t \<Rightarrow> ('l,'t,'x) thread_info"
  and thr_invar :: "'m_t \<Rightarrow> bool"
  and thr_lookup :: "'t \<Rightarrow> 'm_t \<rightharpoonup> ('x \<times> 'l released_locks)"
  and thr_update :: "'t \<Rightarrow> 'x \<times> 'l released_locks \<Rightarrow> 'm_t \<Rightarrow> 'm_t"
  and ws_\<alpha> :: "'m_w \<Rightarrow> ('w,'t) wait_sets"
  and ws_invar :: "'m_w \<Rightarrow> bool"
  and ws_lookup :: "'t \<Rightarrow> 'm_w \<rightharpoonup> 'w wait_set_status"
  and ws_update :: "'t \<Rightarrow> 'w wait_set_status \<Rightarrow> 'm_w \<Rightarrow> 'm_w"
  and ws_delete :: "'t \<Rightarrow> 'm_w \<Rightarrow> 'm_w"
  and ws_iterate :: "'m_w \<Rightarrow> ('t \<times> 'w wait_set_status, 'm_w) set_iterator"
  and ws_sel :: "'m_w \<Rightarrow> ('t \<times> 'w wait_set_status \<Rightarrow> bool) \<rightharpoonup> ('t \<times> 'w wait_set_status)"
  and is_\<alpha> :: "'s_i \<Rightarrow> 't interrupts"
  and is_invar :: "'s_i \<Rightarrow> bool"
  and is_memb :: "'t \<Rightarrow> 's_i \<Rightarrow> bool"
  and is_ins :: "'t \<Rightarrow> 's_i \<Rightarrow> 's_i"
  and is_delete :: "'t \<Rightarrow> 's_i \<Rightarrow> 's_i"
  and queue_\<alpha> :: "'queue \<Rightarrow> 't list"
  and queue_invar :: "'queue \<Rightarrow> bool"
  and queue_empty :: "unit \<Rightarrow> 'queue"
  and queue_isEmpty :: "'queue \<Rightarrow> bool"
  and queue_enqueue :: "'t \<Rightarrow> 'queue \<Rightarrow> 'queue"
  and queue_dequeue :: "'queue \<Rightarrow> 't \<times> 'queue"
  and queue_push :: "'t \<Rightarrow> 'queue \<Rightarrow> 'queue"
begin

lemma queue_rotate1_correct:
  assumes "queue_invar queue" "queue_\<alpha> queue \<noteq> []"
  shows "queue_\<alpha> (queue_rotate1 queue) = rotate1 (queue_\<alpha> queue)"
  and "queue_invar (queue_rotate1 queue)"
using assms
apply(auto simp add: queue_rotate1_def split_beta queue.dequeue_correct queue.enqueue_correct)
by(cases "queue_\<alpha> queue") simp_all

lemma enqueue_thread_correct:
  assumes "queue_invar queue"
  shows "queue_\<alpha> (enqueue_new_thread queue nta) = Round_Robin.enqueue_new_thread (queue_\<alpha> queue) nta"
  and "queue_invar (enqueue_new_thread queue nta)"
using assms
by(case_tac [!] nta)(simp_all add: queue.enqueue_correct)

lemma enqueue_threads_correct:
  assumes "queue_invar queue"
  shows "queue_\<alpha> (enqueue_new_threads queue ntas) = Round_Robin.enqueue_new_threads (queue_\<alpha> queue) ntas"
  and "queue_invar (enqueue_new_threads queue ntas)"
using assms
apply(induct ntas arbitrary: queue)
apply(simp_all add: enqueue_new_threads_def Round_Robin.enqueue_new_threads_def enqueue_thread_correct)
done

lemma round_robin_update_thread_correct:
  assumes "round_robin_invar \<sigma> T" "t' \<in> T"
  shows "round_robin_\<alpha> (round_robin_update_state n0 \<sigma> t ta) = Round_Robin.round_robin_update_state n0 (round_robin_\<alpha> \<sigma>) t ta"
using assms
apply(cases \<sigma>)
apply(auto simp add: round_robin_\<alpha>_def queue_rotate1_correct enqueue_threads_correct del: conjI)
apply(subst (1 2) queue_rotate1_correct)
apply(auto simp add: enqueue_threads_correct)
done

lemma round_robin_step_correct:
  assumes det: "\<alpha>.deterministic I"
  and invar: "round_robin_invar \<sigma> (dom (thr_\<alpha> (thr s)))" "state_invar s" "state_\<alpha> s \<in> I"
  shows
  "map_option (apsnd (apsnd round_robin_\<alpha>)) (round_robin_step n0 \<sigma> s t) = 
   \<alpha>.round_robin_step n0 (round_robin_\<alpha> \<sigma>) (state_\<alpha> s) t" (is ?thesis1)
  and "case_option True (\<lambda>(t, taxm, \<sigma>). round_robin_invar \<sigma> (case taxm of None \<Rightarrow> dom (thr_\<alpha> (thr s)) | Some (ta, x', m') \<Rightarrow> dom (thr_\<alpha> (thr s)) \<union> {t. \<exists>x m. NewThread t x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>})) (round_robin_step n0 \<sigma> s t)"
  (is ?thesis2)
proof -
  have "?thesis1 \<and> ?thesis2"
  proof(cases "dom (thr_\<alpha> (thr s)) = {}")
    case True
    thus ?thesis using invar
      apply(cases \<sigma>)
      apply(auto dest: step_thread_Some_NoneD[OF det] step_thread_Some_SomeD[OF det])
      apply(fastforce simp add: \<alpha>.step_thread_eq_None_conv elim: \<alpha>.active_threads.cases intro: sym)
      done
  next
    case False
    then obtain t' where t': "t' \<in> dom (thr_\<alpha> (thr s))" by blast
    hence ?thesis1
      using step_thread_correct(1)[of I round_robin_invar \<sigma> s round_robin_\<alpha> "round_robin_update_state n0 \<sigma> t" t, OF det invar]
      unfolding o_def using invar
      by(subst (asm) round_robin_update_thread_correct) auto
    moreover
    { fix ta :: "('l, 't, 'x, 'm, 'w, 'o) thread_action"
      assume "FWThread.thread_oks (thr_\<alpha> (thr s)) \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
      moreover from t' invar have "queue_\<alpha> (fst \<sigma>) \<noteq> []" by(cases \<sigma>) auto
      ultimately have "round_robin_invar (round_robin_update_state n0 \<sigma> t ta) (dom (thr_\<alpha> (thr s)) \<union> {t. \<exists>x m. NewThread t x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>})"
        using invar t' by(cases \<sigma>)(auto simp add: queue_rotate1_correct enqueue_threads_correct set_enqueue_new_threads iff del: domIff intro: distinct_enqueue_new_threads) }
    from step_thread_correct(2)[OF det, of round_robin_invar \<sigma> s "round_robin_update_state n0 \<sigma> t" t, OF invar this]
    have ?thesis2 using t' invar by simp
    ultimately show ?thesis by blast
  qed
  thus ?thesis1 ?thesis2 by blast+
qed

lemma round_robin_reschedule_correct:
  assumes det: "\<alpha>.deterministic I"
  and invar: "round_robin_invar (queue, n) (dom (thr_\<alpha> (thr s)))" "state_invar s" "state_\<alpha> s \<in> I"
  and t0: "t0 \<in> set (queue_\<alpha> queue)"
  shows "map_option (apsnd (apsnd round_robin_\<alpha>)) (round_robin_reschedule t0 queue n0 s) =
     \<alpha>.round_robin_reschedule t0 (queue_\<alpha> queue) n0 (state_\<alpha> s)"
  and "case_option True (\<lambda>(t, taxm, \<sigma>). round_robin_invar \<sigma> (case taxm of None \<Rightarrow> dom (thr_\<alpha> (thr s)) | Some (ta, x', m') \<Rightarrow> dom (thr_\<alpha> (thr s)) \<union> {t. \<exists>x m. NewThread t x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>})) (round_robin_reschedule t0 queue n0 s)"
using t0 invar
proof(induct "queue_\<alpha> queue" arbitrary: queue n rule: round_robin_reschedule_induct)
  case head
  { case 1 thus ?case using head[symmetric]
      by(subst round_robin_reschedule.simps)(subst \<alpha>.round_robin_reschedule.simps, clarsimp simp add: split_beta queue.dequeue_correct) 
  next
    case 2 thus ?case using head[symmetric]
      by(subst round_robin_reschedule.simps)(clarsimp simp add: split_beta queue.dequeue_correct) }
next
  case (rotate \<alpha>queue' t)
  obtain t' queue' where queue': "queue_dequeue queue = (t', queue')" by(cases "queue_dequeue queue")
  note [simp] = \<open>t # \<alpha>queue' = queue_\<alpha> queue\<close>[symmetric]
  { case 1
    with queue' have [simp]: "t' = t" "\<alpha>queue' = queue_\<alpha> queue'" "queue_invar queue'" by(auto elim: queue.removelE)
    from 1 queue' have invar': "round_robin_invar (queue_push t queue', n0) (dom (thr_\<alpha> (thr s)))"
      by(auto simp add: queue.push_correct)
    show ?case
    proof(cases "round_robin_step n0 (queue_push t queue', n0) s t")
      case Some thus ?thesis
        using queue' \<open>t \<noteq> t0\<close> round_robin_step_correct[OF det invar' \<open>state_invar s\<close>, of n0 t] invar' \<open>state_\<alpha> s \<in> I\<close>
        by(subst round_robin_reschedule.simps)(subst \<alpha>.round_robin_reschedule.simps, auto simp add: round_robin_\<alpha>_def queue.push_correct)
    next
      case None
      hence \<alpha>None: "\<alpha>.round_robin_step n0 (queue_\<alpha> (queue_push t queue'), n0) (state_\<alpha> s) t = None"
        using round_robin_step_correct[OF det invar' \<open>state_invar s\<close>, of n0 t] invar' \<open>state_\<alpha> s \<in> I\<close>
        by(auto simp add: queue.push_correct round_robin_\<alpha>_def)
      have "\<alpha>queue' @ [t] = queue_\<alpha> (queue_enqueue t queue')" by(simp add: queue.enqueue_correct)
      moreover from invar'
      have "round_robin_invar (queue_enqueue t queue', n0) (dom (thr_\<alpha> (thr s)))"
        by(auto simp add: queue.enqueue_correct queue.push_correct)
      ultimately 
      have "map_option (apsnd (apsnd round_robin_\<alpha>)) (round_robin_reschedule t0 (queue_enqueue t queue') n0 s) =
            \<alpha>.round_robin_reschedule t0 (queue_\<alpha> (queue_enqueue t queue')) n0 (state_\<alpha> s)"
        using \<open>state_invar s\<close> \<open>state_\<alpha> s \<in> I\<close> by(rule rotate.hyps)
      thus ?thesis using None \<alpha>None \<open>t \<noteq> t0\<close> invar' queue'
        by(subst round_robin_reschedule.simps)(subst \<alpha>.round_robin_reschedule.simps, auto simp add: queue.enqueue_correct queue.push_correct)
    qed
  next
    case 2
    with queue' have [simp]: "t' = t" "\<alpha>queue' = queue_\<alpha> queue'" "queue_invar queue'" by(auto elim: queue.removelE)
    from 2 queue' have invar': "round_robin_invar (queue_push t queue', n0) (dom (thr_\<alpha> (thr s)))"
      by(auto simp add: queue.push_correct)
    show ?case
    proof(cases "round_robin_step n0 (queue_push t queue', n0) s t")
      case Some thus ?thesis
        using queue' \<open>t \<noteq> t0\<close> round_robin_step_correct[OF det invar' \<open>state_invar s\<close>, of n0 t] invar' \<open>state_\<alpha> s \<in> I\<close>
        by(subst round_robin_reschedule.simps)(auto simp add: round_robin_\<alpha>_def queue.push_correct)
    next
      case None
      have "\<alpha>queue' @ [t] = queue_\<alpha> (queue_enqueue t queue')" by(simp add: queue.enqueue_correct)
      moreover from invar'
      have "round_robin_invar (queue_enqueue t queue', n0) (dom (thr_\<alpha> (thr s)))"
        by(auto simp add: queue.enqueue_correct queue.push_correct)
      ultimately 
      have "case_option True (\<lambda>(t, taxm, \<sigma>). round_robin_invar \<sigma> (case_option (dom (thr_\<alpha> (thr s))) (\<lambda>(ta, x', m'). dom (thr_\<alpha> (thr s)) \<union> {t. \<exists>x m. NewThread t x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>}) taxm)) (round_robin_reschedule t0 (queue_enqueue t queue') n0 s)"
        using \<open>state_invar s\<close> \<open>state_\<alpha> s \<in> I\<close> by(rule rotate.hyps)
      thus ?thesis using None \<open>t \<noteq> t0\<close> invar' queue'
        by(subst round_robin_reschedule.simps)(auto simp add: queue.enqueue_correct queue.push_correct)
    qed
  }
qed

lemma round_robin_correct:
  assumes det: "\<alpha>.deterministic I"
  and invar: "round_robin_invar \<sigma> (dom (thr_\<alpha> (thr s)))" "state_invar s" "state_\<alpha> s \<in> I"
  shows "map_option (apsnd (apsnd round_robin_\<alpha>)) (round_robin n0 \<sigma> s) =
         \<alpha>.round_robin n0 (round_robin_\<alpha> \<sigma>) (state_\<alpha> s)"
    (is ?thesis1)
  and "case_option True (\<lambda>(t, taxm, \<sigma>). round_robin_invar \<sigma> (case taxm of None \<Rightarrow> dom (thr_\<alpha> (thr s)) | Some (ta, x', m') \<Rightarrow> dom (thr_\<alpha> (thr s)) \<union> {t. \<exists>x m. NewThread t x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>})) (round_robin n0 \<sigma> s)"
    (is ?thesis2)
proof -
  obtain queue n where \<sigma>: "\<sigma> = (queue, n)" by(cases \<sigma>)
  have "?thesis1 \<and> ?thesis2"
  proof(cases "queue_\<alpha> queue")
    case Nil thus ?thesis using invar \<sigma>
      by(auto simp add: split_beta queue.isEmpty_correct round_robin_\<alpha>_def)
  next
    case (Cons t \<alpha>queue')
    with invar \<sigma> obtain queue'
      where [simp]: "queue_dequeue queue = (t, queue')" "\<alpha>queue' = queue_\<alpha> queue'" "queue_invar queue'"
      by(auto elim: queue.removelE)
    from invar \<sigma> Cons have invar': "round_robin_invar (queue_push t queue', n) (dom (thr_\<alpha> (thr s)))"
      by(auto simp add: queue.push_correct)
    from invar \<sigma> Cons have invar'': "round_robin_invar (queue_enqueue t queue', n0) (dom (thr_\<alpha> (thr s)))"
      by(auto simp add: queue.enqueue_correct)
    show ?thesis
    proof(cases "round_robin_step n0 (queue_push t queue', n) s t")
      case Some
      with \<sigma> Cons invar show ?thesis
        using round_robin_step_correct[OF det invar' \<open>state_invar s\<close>, of n0 t]
        by(auto simp add: queue.isEmpty_correct queue.push_correct round_robin_\<alpha>_def)
    next
      case None
      from invar \<sigma> Cons have "t \<in> set (queue_\<alpha> (queue_enqueue t queue'))"
        by(auto simp add: queue.enqueue_correct)      
      from round_robin_reschedule_correct[OF det invar'' \<open>state_invar s\<close>, OF \<open>state_\<alpha> s \<in> I\<close> this, of n0] None \<sigma> Cons invar
        round_robin_step_correct[OF det invar' \<open>state_invar s\<close>, of n0 t]
      show ?thesis by(auto simp add: queue.isEmpty_correct queue.push_correct round_robin_\<alpha>_def queue.enqueue_correct)
    qed
  qed
  thus ?thesis1 ?thesis2 by simp_all
qed

lemma round_robin_scheduler_spec:
  assumes det: "\<alpha>.deterministic I"
  shows "scheduler_spec final r (round_robin n0) round_robin_invar thr_\<alpha> thr_invar ws_\<alpha> ws_invar is_\<alpha> is_invar I"
proof
  fix \<sigma> s
  assume rr: "round_robin n0 \<sigma> s = None"
    and invar: "round_robin_invar \<sigma> (dom (thr_\<alpha> (thr s)))" "state_invar s" "state_\<alpha> s \<in> I"
  from round_robin_correct[OF det, OF invar, of n0] rr
  have "\<alpha>.round_robin n0 (round_robin_\<alpha> \<sigma>) (state_\<alpha> s) = None" by simp
  moreover from invar have "Round_Robin.round_robin_invar (round_robin_\<alpha> \<sigma>) (dom (thr (state_\<alpha> s)))"
    by(simp add: round_robin_invar_correct)
  ultimately show "\<alpha>.active_threads (state_\<alpha> s) = {}" by(rule \<alpha>.round_robin_NoneD)
next
  fix \<sigma> s t \<sigma>'
  assume rr: "round_robin n0 \<sigma> s = \<lfloor>(t, None, \<sigma>')\<rfloor>"
    and invar: "round_robin_invar \<sigma> (dom (thr_\<alpha> (thr s)))" "state_invar s" "state_\<alpha> s \<in> I"
  from round_robin_correct[OF det, OF invar, of n0] rr
  have rr': "\<alpha>.round_robin n0 (round_robin_\<alpha> \<sigma>) (state_\<alpha> s) = \<lfloor>(t, None, round_robin_\<alpha> \<sigma>')\<rfloor>" by simp
  then show "\<exists>x ln n. thr_\<alpha> (thr s) t = \<lfloor>(x, ln)\<rfloor> \<and> 0 < ln $ n \<and> \<not> waiting (ws_\<alpha> (wset s) t) \<and> may_acquire_all (locks s) t ln"
    by(rule \<alpha>.round_robin_Some_NoneD[where s="state_\<alpha> s", unfolded state_\<alpha>_conv])
next
  fix \<sigma> s t ta x' m' \<sigma>'
  assume rr: "round_robin n0 \<sigma> s = \<lfloor>(t, \<lfloor>(ta, x', m')\<rfloor>, \<sigma>')\<rfloor>"
    and invar: "round_robin_invar \<sigma> (dom (thr_\<alpha> (thr s)))" "state_invar s" "state_\<alpha> s \<in> I"
  from round_robin_correct[OF det, OF invar, of n0] rr
  have rr': "\<alpha>.round_robin n0 (round_robin_\<alpha> \<sigma>) (state_\<alpha> s) = \<lfloor>(t, \<lfloor>(ta, x', m')\<rfloor>, round_robin_\<alpha> \<sigma>')\<rfloor>" by simp
  thus "\<exists>x. thr_\<alpha> (thr s) t = \<lfloor>(x, no_wait_locks)\<rfloor> \<and> Predicate.eval (r t (x, shr s)) (ta, x', m') \<and> \<alpha>.actions_ok (state_\<alpha> s) t ta"
    using \<open>state_\<alpha> s \<in> I\<close> by(rule \<alpha>.round_robin_Some_SomeD[OF det, where s="state_\<alpha> s", unfolded state_\<alpha>_conv])
next
  fix \<sigma> s t \<sigma>'
  assume rr: "round_robin n0 \<sigma> s = \<lfloor>(t, None, \<sigma>')\<rfloor>"
    and invar: "round_robin_invar \<sigma> (dom (thr_\<alpha> (thr s)))" "state_invar s" "state_\<alpha> s \<in> I"
  from round_robin_correct[OF det, OF invar, of n0] rr
  show "round_robin_invar \<sigma>' (dom (thr_\<alpha> (thr s)))" by simp
next
  fix \<sigma> s t ta x' m' \<sigma>'
  assume rr: "round_robin n0 \<sigma> s = \<lfloor>(t, \<lfloor>(ta, x', m')\<rfloor>, \<sigma>')\<rfloor>"
    and invar: "round_robin_invar \<sigma> (dom (thr_\<alpha> (thr s)))" "state_invar s" "state_\<alpha> s \<in> I"
  from round_robin_correct[OF det, OF invar, of n0] rr
  show "round_robin_invar \<sigma>' (dom (thr_\<alpha> (thr s)) \<union> {t. \<exists>x m. NewThread t x m \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>})" by simp
qed

lemma round_robin_start_invar:
  "round_robin_invar (round_robin_start n0 t0) {t0}"
by(simp add: round_robin_start_def queue.empty_correct queue.enqueue_correct)

end

sublocale round_robin_base <
  scheduler_base
    final r convert_RA
    "round_robin n0" "output" "pick_wakeup_via_sel (\<lambda>s P. ws_sel s (\<lambda>(k,v). P k v))" round_robin_invar
    thr_\<alpha> thr_invar thr_lookup thr_update
    ws_\<alpha> ws_invar ws_lookup ws_update ws_delete ws_iterate
    is_\<alpha> is_invar is_memb is_ins is_delete
  for n0 .

sublocale round_robin <
  pick_wakeup_spec
    final r convert_RA
    "pick_wakeup_via_sel (\<lambda>s P. ws_sel s (\<lambda>(k,v). P k v))" round_robin_invar
    thr_\<alpha> thr_invar
    ws_\<alpha> ws_invar
    is_\<alpha> is_invar
by(rule pick_wakeup_spec_via_sel)(unfold_locales)

context round_robin begin

lemma round_robin_scheduler:
  assumes det: "\<alpha>.deterministic I"
  shows 
  "scheduler
     final r convert_RA
     (round_robin n0) (pick_wakeup_via_sel (\<lambda>s P. ws_sel s (\<lambda>(k,v). P k v))) round_robin_invar 
     thr_\<alpha> thr_invar thr_lookup thr_update 
     ws_\<alpha> ws_invar ws_lookup ws_update ws_delete ws_iterate
     is_\<alpha> is_invar is_memb is_ins is_delete
     I"
proof -
  interpret scheduler_spec
      final r convert_RA
      "round_robin n0" round_robin_invar
      thr_\<alpha> thr_invar
      ws_\<alpha> ws_invar
      is_\<alpha> is_invar
      I
    using det by(rule round_robin_scheduler_spec)

  show ?thesis by(unfold_locales)(rule \<alpha>.deterministic_invariant3p[OF det])
qed

end

lemmas [code] =
  round_robin_base.queue_rotate1_def
  round_robin_base.enqueue_new_thread.simps
  round_robin_base.enqueue_new_threads_def
  round_robin_base.round_robin_update_state.simps
  round_robin_base.round_robin_reschedule.simps
  round_robin_base.round_robin.simps
  round_robin_base.round_robin_start_def

end
