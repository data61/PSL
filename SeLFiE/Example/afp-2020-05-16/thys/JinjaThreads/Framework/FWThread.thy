(*  Title:      JinjaThreads/Framework/FWThread.thy
    Author:     Andreas Lochbihler
*)

section \<open>Semantics of the thread actions for thread creation\<close>

theory FWThread
imports
  FWState
begin

text\<open>Abstractions for thread ids\<close>

context
  notes [[inductive_internals]]
begin

inductive free_thread_id :: "('l,'t,'x) thread_info \<Rightarrow> 't \<Rightarrow> bool"
for ts :: "('l,'t,'x) thread_info" and t :: 't
where "ts t = None \<Longrightarrow> free_thread_id ts t"

declare free_thread_id.cases [elim]

end

lemma free_thread_id_iff: "free_thread_id ts t = (ts t = None)"
by(auto elim: free_thread_id.cases intro: free_thread_id.intros)

text\<open>Update functions for the multithreaded state\<close>

fun redT_updT :: "('l,'t,'x) thread_info \<Rightarrow> ('t,'x,'m) new_thread_action \<Rightarrow> ('l,'t,'x) thread_info"
where
  "redT_updT ts (NewThread t' x m) = ts(t' \<mapsto> (x, no_wait_locks))"
| "redT_updT ts _ = ts"

fun redT_updTs :: "('l,'t,'x) thread_info \<Rightarrow> ('t,'x,'m) new_thread_action list \<Rightarrow> ('l,'t,'x) thread_info"
where
  "redT_updTs ts [] = ts"
| "redT_updTs ts (ta#tas) = redT_updTs (redT_updT ts ta) tas"

lemma redT_updTs_append [simp]:
  "redT_updTs ts (tas @ tas') = redT_updTs (redT_updTs ts tas) tas'"
by(induct ts tas rule: redT_updTs.induct) auto

lemma redT_updT_None: 
  "redT_updT ts ta t = None \<Longrightarrow> ts t = None"
by(cases ta)(auto split: if_splits)

lemma redT_updTs_None: "redT_updTs ts tas t = None \<Longrightarrow> ts t = None"
by(induct ts tas rule: redT_updTs.induct)(auto intro: redT_updT_None)

lemma redT_updT_Some1:
  "ts t = \<lfloor>xw\<rfloor> \<Longrightarrow> \<exists>xw. redT_updT ts ta t = \<lfloor>xw\<rfloor>"
by(cases ta) auto

lemma redT_updTs_Some1:
  "ts t = \<lfloor>xw\<rfloor> \<Longrightarrow> \<exists>xw. redT_updTs ts tas t = \<lfloor>xw\<rfloor>"
unfolding not_None_eq[symmetric]
by(induct ts tas arbitrary: xw rule: redT_updTs.induct)(simp_all del: split_paired_Ex, blast dest: redT_updT_Some1)

lemma redT_updT_finite_dom_inv:
  "finite (dom (redT_updT ts ta)) = finite (dom ts)"
by(cases ta) auto

lemma redT_updTs_finite_dom_inv:
  "finite (dom (redT_updTs ts tas)) = finite (dom ts)"
by(induct ts tas rule: redT_updTs.induct)(simp_all add: redT_updT_finite_dom_inv)

text\<open>Preconditions for thread creation actions\<close>

text\<open>These primed versions are for checking preconditions only. They allow the thread actions to have a type for thread-local information that is different than the thread info state itself.\<close>

fun redT_updT' :: "('l,'t,'x) thread_info \<Rightarrow> ('t,'x','m) new_thread_action \<Rightarrow> ('l,'t,'x) thread_info"
where
  "redT_updT' ts (NewThread t' x m) = ts(t' \<mapsto> (undefined, no_wait_locks))"
| "redT_updT' ts _ = ts"

fun redT_updTs' :: "('l,'t,'x) thread_info \<Rightarrow> ('t,'x','m) new_thread_action list \<Rightarrow> ('l,'t,'x) thread_info"
where
  "redT_updTs' ts [] = ts"
| "redT_updTs' ts (ta#tas) = redT_updTs' (redT_updT' ts ta) tas"

lemma redT_updT'_None: 
  "redT_updT' ts ta t = None \<Longrightarrow> ts t = None"
by(cases ta)(auto split: if_splits)

primrec thread_ok :: "('l,'t,'x) thread_info \<Rightarrow> ('t,'x','m) new_thread_action \<Rightarrow> bool"
where
  "thread_ok ts (NewThread t x m) = free_thread_id ts t"
| "thread_ok ts (ThreadExists t b) = (b \<noteq> free_thread_id ts t)"

fun thread_oks :: "('l,'t,'x) thread_info \<Rightarrow> ('t,'x','m) new_thread_action list \<Rightarrow> bool"
where
  "thread_oks ts [] = True"
| "thread_oks ts (ta#tas) = (thread_ok ts ta \<and> thread_oks (redT_updT' ts ta) tas)"

lemma thread_ok_ts_change:
  "(\<And>t. ts t = None \<longleftrightarrow> ts' t = None) \<Longrightarrow> thread_ok ts ta \<longleftrightarrow> thread_ok ts' ta"
by(cases ta)(auto simp add: free_thread_id_iff)

lemma thread_oks_ts_change:
  "(\<And>t. ts t = None \<longleftrightarrow> ts' t = None) \<Longrightarrow> thread_oks ts tas \<longleftrightarrow> thread_oks ts' tas"
proof(induct tas arbitrary: ts ts')
  case Nil thus ?case by simp
next
  case (Cons ta tas ts ts')
  note IH = \<open>\<And>ts ts'. (\<And>t. (ts t = None) = (ts' t = None)) \<Longrightarrow> thread_oks ts tas = thread_oks ts' tas\<close>
  note eq = \<open>\<And>t. (ts t = None) = (ts' t = None)\<close>
  from eq have "thread_ok ts ta \<longleftrightarrow> thread_ok ts' ta" by(rule thread_ok_ts_change)
  moreover from eq have "\<And>t. (redT_updT' ts ta t = None) = (redT_updT' ts' ta t = None)"
    by(cases ta)(auto)
  hence "thread_oks (redT_updT' ts ta) tas = thread_oks (redT_updT' ts' ta) tas" by(rule IH)
  ultimately show ?case by simp
qed

lemma redT_updT'_eq_None_conv: 
  "(\<And>t. ts t = None \<longleftrightarrow> ts' t = None) \<Longrightarrow> redT_updT' ts ta t = None \<longleftrightarrow> redT_updT ts' ta t = None"
by(cases ta) simp_all

lemma redT_updTs'_eq_None_conv:
  "(\<And>t. ts t = None \<longleftrightarrow> ts' t = None) \<Longrightarrow> redT_updTs' ts tas t = None \<longleftrightarrow> redT_updTs ts' tas t = None"
apply(induct tas arbitrary: ts ts')
apply simp_all
apply(blast intro: redT_updT'_eq_None_conv del: iffI)
done

lemma thread_oks_redT_updT_conv [simp]:
  "thread_oks (redT_updT' ts ta) tas = thread_oks (redT_updT ts ta) tas"
by(rule thread_oks_ts_change)(rule redT_updT'_eq_None_conv refl)+

lemma thread_oks_append [simp]:
  "thread_oks ts (tas @ tas') = (thread_oks ts tas \<and> thread_oks (redT_updTs' ts tas) tas')"
by(induct tas arbitrary: ts, auto)

lemma thread_oks_redT_updTs_conv [simp]:
  "thread_oks (redT_updTs' ts ta) tas = thread_oks (redT_updTs ts ta) tas"
by(rule thread_oks_ts_change)(rule redT_updTs'_eq_None_conv refl)+


lemma redT_updT_Some:
  "\<lbrakk> ts t = \<lfloor>xw\<rfloor>; thread_ok ts ta \<rbrakk> \<Longrightarrow> redT_updT ts ta t = \<lfloor>xw\<rfloor>"
by(cases ta) auto

lemma redT_updTs_Some:
  "\<lbrakk> ts t = \<lfloor>xw\<rfloor>; thread_oks ts tas \<rbrakk> \<Longrightarrow> redT_updTs ts tas t = \<lfloor>xw\<rfloor>"
by(induct ts tas rule: redT_updTs.induct)(auto intro: redT_updT_Some)

lemma redT_updT'_Some:
  "\<lbrakk> ts t = \<lfloor>xw\<rfloor>; thread_ok ts ta \<rbrakk> \<Longrightarrow> redT_updT' ts ta t = \<lfloor>xw\<rfloor>"
by(cases ta) auto

lemma redT_updTs'_Some:
  "\<lbrakk> ts t = \<lfloor>xw\<rfloor>; thread_oks ts tas \<rbrakk> \<Longrightarrow> redT_updTs' ts tas t = \<lfloor>xw\<rfloor>"
by(induct ts tas rule: redT_updTs'.induct)(auto intro: redT_updT'_Some)


lemma thread_ok_new_thread:
  "thread_ok ts (NewThread t m' x) \<Longrightarrow> ts t = None"
by(auto)

lemma thread_oks_new_thread:
  "\<lbrakk> thread_oks ts tas; NewThread t x m \<in> set tas \<rbrakk> \<Longrightarrow> ts t = None"
by(induct ts tas rule: thread_oks.induct)(auto intro: redT_updT'_None)


lemma redT_updT_new_thread_ts:
  "thread_ok ts (NewThread t x m) \<Longrightarrow> redT_updT ts (NewThread t x m) t = \<lfloor>(x, no_wait_locks)\<rfloor>"
by(simp)

lemma redT_updTs_new_thread_ts:
  "\<lbrakk> thread_oks ts tas; NewThread t x m \<in> set tas \<rbrakk> \<Longrightarrow> redT_updTs ts tas t = \<lfloor>(x, no_wait_locks)\<rfloor>"
by(induct ts tas rule: redT_updTs.induct)(auto intro: redT_updTs_Some)


lemma redT_updT_new_thread:
  "\<lbrakk> redT_updT ts ta t = \<lfloor>(x, w)\<rfloor>; thread_ok ts ta; ts t = None \<rbrakk> \<Longrightarrow> \<exists>m. ta = NewThread t x m \<and> w = no_wait_locks"
by(cases ta)(auto split: if_split_asm)

lemma redT_updTs_new_thread:
  "\<lbrakk> redT_updTs ts tas t = \<lfloor>(x, w)\<rfloor>; thread_oks ts tas; ts t = None \<rbrakk> 
  \<Longrightarrow> \<exists>m .NewThread t x m \<in> set tas \<and> w = no_wait_locks"
proof(induct tas arbitrary: ts)
  case Nil thus ?case by simp
next
  case (Cons TA TAS TS)
  note IH = \<open>\<And>ts. \<lbrakk>redT_updTs ts TAS t = \<lfloor>(x, w)\<rfloor>; thread_oks ts TAS; ts t = None\<rbrakk> \<Longrightarrow> \<exists>m. NewThread t x m \<in> set TAS \<and> w = no_wait_locks\<close>
  note es't = \<open>redT_updTs TS (TA # TAS) t = \<lfloor>(x, w)\<rfloor>\<close>
  note cct = \<open>thread_oks TS (TA # TAS)\<close>
  hence cctta: "thread_ok TS TA" and ccts: "thread_oks (redT_updT TS TA) TAS" by auto
  note est = \<open>TS t = None\<close>
  { fix X W
    assume rest: "redT_updT TS TA t = \<lfloor>(X, W)\<rfloor>"
    then obtain m where "TA = NewThread t X m \<and> W = no_wait_locks" using cctta est
      by (auto dest!: redT_updT_new_thread)
    then obtain "TA = NewThread t X m" "W = no_wait_locks" ..
    moreover from rest ccts
    have "redT_updTs TS (TA # TAS) t = \<lfloor>(X, W)\<rfloor>" 
      by(auto intro:redT_updTs_Some)
    with es't have "X = x" "W = w" by auto
    ultimately have ?case by auto }
  moreover
  { assume rest: "redT_updT TS TA t = None"
    hence "\<And>m. TA \<noteq> NewThread t x m" using est cct
      by(clarsimp)
    with rest ccts es't have ?case by(auto dest: IH) }
  ultimately show ?case by(cases "redT_updT TS TA t", auto)
qed

lemma redT_updT_upd:
  "\<lbrakk> ts t = \<lfloor>xw\<rfloor>; thread_ok ts ta \<rbrakk> \<Longrightarrow> redT_updT ts ta(t \<mapsto> xw') = redT_updT (ts(t \<mapsto> xw')) ta"
by(cases ta)(fastforce intro: fun_upd_twist)+

lemma redT_updTs_upd:
  "\<lbrakk> ts t = \<lfloor>xw\<rfloor>; thread_oks ts tas \<rbrakk> \<Longrightarrow> redT_updTs ts tas(t \<mapsto> xw') = redT_updTs (ts(t \<mapsto> xw')) tas"
by(induct ts tas rule: redT_updTs.induct)(auto simp del: fun_upd_apply simp add: redT_updT_upd dest: redT_updT_Some)

lemma thread_ok_upd:
  "ts t = \<lfloor>xln\<rfloor> \<Longrightarrow> thread_ok (ts(t \<mapsto> xln')) ta = thread_ok ts ta"
by(rule thread_ok_ts_change) simp

lemma thread_oks_upd:
  "ts t = \<lfloor>xln\<rfloor> \<Longrightarrow> thread_oks (ts(t \<mapsto> xln')) tas = thread_oks ts tas"
by(rule thread_oks_ts_change) simp

lemma thread_ok_convert_new_thread_action [simp]:
  "thread_ok ts (convert_new_thread_action f ta) = thread_ok ts ta"
by(cases ta) auto

lemma redT_updT'_convert_new_thread_action_eq_None:
  "redT_updT' ts (convert_new_thread_action f ta) t = None \<longleftrightarrow> redT_updT' ts ta t = None"
by(cases ta) auto

lemma thread_oks_convert_new_thread_action [simp]:
  "thread_oks ts (map (convert_new_thread_action f) tas) = thread_oks ts tas"
by(induct ts tas rule: thread_oks.induct)(simp_all add: thread_oks_ts_change[OF redT_updT'_convert_new_thread_action_eq_None])

lemma map_redT_updT:
  "map_option (map_prod f id) (redT_updT ts ta t) = 
  redT_updT (\<lambda>t. map_option (map_prod f id) (ts t)) (convert_new_thread_action f ta) t"
by(cases ta) auto

lemma map_redT_updTs:
  "map_option (map_prod f id) (redT_updTs ts tas t) = 
  redT_updTs (\<lambda>t. map_option (map_prod f id) (ts t)) (map (convert_new_thread_action f) tas) t"
by(induct tas arbitrary: ts)(auto simp add: map_redT_updT)

end
