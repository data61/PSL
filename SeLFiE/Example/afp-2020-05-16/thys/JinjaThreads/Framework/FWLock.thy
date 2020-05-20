(*  Title:      JinjaThreads/Framework/FWLock.thy
    Author:     Andreas Lochbihler
*)

section \<open>All about a managing a single lock\<close>

theory FWLock
imports
  FWState
begin

fun has_locks :: "'t lock \<Rightarrow> 't \<Rightarrow> nat" where
  "has_locks None t = 0"
| "has_locks \<lfloor>(t', n)\<rfloor> t = (if t = t' then Suc n else 0)"

lemma has_locks_iff: 
  "has_locks l t = n \<longleftrightarrow>
  (l = None \<and> n = 0) \<or> 
  (\<exists>n'. l = \<lfloor>(t, n')\<rfloor> \<and> Suc n' = n) \<or> (\<exists>t' n'. l = \<lfloor>(t', n')\<rfloor> \<and> t' \<noteq> t \<and> n = 0)"
by(cases l, auto)

lemma has_locksE:
  "\<lbrakk> has_locks l t = n;
     \<lbrakk> l = None; n = 0 \<rbrakk> \<Longrightarrow> P;
     \<And>n'. \<lbrakk> l = \<lfloor>(t, n')\<rfloor>; Suc n' = n \<rbrakk> \<Longrightarrow> P;
     \<And>t' n'. \<lbrakk> l = \<lfloor>(t', n')\<rfloor>; t' \<noteq> t; n = 0 \<rbrakk> \<Longrightarrow> P \<rbrakk>
  \<Longrightarrow> P"
by(auto simp add: has_locks_iff split: if_split_asm prod.split_asm)


inductive may_lock :: "'t lock \<Rightarrow> 't \<Rightarrow> bool" where
  "may_lock None t"
| "may_lock \<lfloor>(t, n)\<rfloor> t"

lemma may_lock_iff [code]:
  "may_lock l t = (case l of None \<Rightarrow> True | \<lfloor>(t', n)\<rfloor> \<Rightarrow> t = t')"
by(auto intro: may_lock.intros elim: may_lock.cases)

lemma may_lockI:
  "l = None \<or> (\<exists>n. l = \<lfloor>(t, n)\<rfloor>) \<Longrightarrow> may_lock l t"
by(cases l, auto intro: may_lock.intros)

lemma may_lockE [consumes 1, case_names None Locked]:
  "\<lbrakk> may_lock l t; l = None \<Longrightarrow> P; \<And>n. l = \<lfloor>(t, n)\<rfloor>  \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
by(auto elim: may_lock.cases)

lemma may_lock_may_lock_t_eq:
  "\<lbrakk> may_lock l t; may_lock l t' \<rbrakk> \<Longrightarrow> (l = None) \<or> (t = t')"
by(auto elim!: may_lockE)

abbreviation has_lock :: "'t lock \<Rightarrow> 't \<Rightarrow> bool"
where "has_lock l t \<equiv> 0 < has_locks l t"

lemma has_locks_Suc_has_lock:
  "has_locks l t = Suc n \<Longrightarrow> has_lock l t"
by(auto)

lemmas has_lock_has_locks_Suc = gr0_implies_Suc[where n = "has_locks l t"] for l t

lemma has_lock_has_locks_conv:
  "has_lock l t \<longleftrightarrow> (\<exists>n. has_locks l t = (Suc n))"
by(auto intro: has_locks_Suc_has_lock has_lock_has_locks_Suc)

lemma has_lock_may_lock:
  "has_lock l t \<Longrightarrow> may_lock l t"
by(cases l, auto intro: may_lockI)

lemma has_lock_may_lock_t_eq:
  "\<lbrakk> has_lock l t; may_lock l t' \<rbrakk> \<Longrightarrow> t = t'"
by(auto elim!: may_lockE split: if_split_asm)

lemma has_locks_has_locks_t_eq: 
  "\<lbrakk>has_locks l t = Suc n; has_locks l t' = Suc n'\<rbrakk> \<Longrightarrow> t = t'"
by(auto elim: has_locksE)

lemma has_lock_has_lock_t_eq:
  "\<lbrakk> has_lock l t; has_lock l t' \<rbrakk> \<Longrightarrow> t = t'"
unfolding has_lock_has_locks_conv
by(auto intro: has_locks_has_locks_t_eq)

lemma not_may_lock_conv:
  "\<not> may_lock l t \<longleftrightarrow> (\<exists>t'. t' \<noteq> t \<and> has_lock l t')"
by(cases l, auto intro: may_lock.intros elim: may_lockE)



(* State update functions for locking *)

fun lock_lock :: "'t lock \<Rightarrow> 't \<Rightarrow> 't lock" where
  "lock_lock None t = \<lfloor>(t, 0)\<rfloor>"
| "lock_lock \<lfloor>(t', n)\<rfloor> t = \<lfloor>(t', Suc n)\<rfloor>"

fun unlock_lock :: "'t lock \<Rightarrow> 't lock" where
  "unlock_lock None = None"
| "unlock_lock \<lfloor>(t, n)\<rfloor> = (case n of 0 \<Rightarrow> None | Suc n' \<Rightarrow> \<lfloor>(t, n')\<rfloor>)"

fun release_all :: "'t lock \<Rightarrow> 't \<Rightarrow> 't lock" where
  "release_all None t = None"
| "release_all \<lfloor>(t', n)\<rfloor> t = (if t = t' then None else \<lfloor>(t', n)\<rfloor>)"

fun acquire_locks :: "'t lock \<Rightarrow> 't \<Rightarrow> nat \<Rightarrow> 't lock" where
  "acquire_locks L t 0 = L"
| "acquire_locks L t (Suc m) = acquire_locks (lock_lock L t) t m"

lemma acquire_locks_conv:
  "acquire_locks L t n = (case L of None \<Rightarrow> (case n of 0 \<Rightarrow> None | Suc m \<Rightarrow> \<lfloor>(t, m)\<rfloor>) | \<lfloor>(t', m)\<rfloor> \<Rightarrow> \<lfloor>(t', n + m)\<rfloor>)"
by(induct n arbitrary: L)(auto)

lemma lock_lock_ls_Some:
  "\<exists>t' n. lock_lock l t = \<lfloor>(t', n)\<rfloor>"
by(cases l, auto)

lemma unlock_lock_SomeD:
  "unlock_lock l = \<lfloor>(t', n)\<rfloor> \<Longrightarrow> l = \<lfloor>(t', Suc n)\<rfloor>"
by(cases l, auto split: nat.split_asm)

lemma has_locks_Suc_lock_lock_has_locks_Suc_Suc:
  "has_locks l t = Suc n \<Longrightarrow> has_locks (lock_lock l t) t = Suc (Suc n)"
by(auto elim!: has_locksE)

lemma has_locks_lock_lock_conv [simp]:
  "may_lock l t \<Longrightarrow> has_locks (lock_lock l t) t = Suc (has_locks l t)"
by(auto elim: may_lockE)

lemma has_locks_release_all_conv [simp]:
  "has_locks (release_all l t) t = 0"
by(cases l, auto split: if_split_asm)

lemma may_lock_lock_lock_conv [simp]: "may_lock (lock_lock l t) t = may_lock l t"
by(cases l, auto elim!: may_lock.cases intro: may_lock.intros)

lemma has_locks_acquire_locks_conv [simp]:
  "may_lock l t \<Longrightarrow> has_locks (acquire_locks l t n) t = has_locks l t + n"
by(induct n arbitrary: l, auto)

lemma may_lock_unlock_lock_conv [simp]:
  "has_lock l t \<Longrightarrow> may_lock (unlock_lock l) t = may_lock l t"
by(cases l)(auto split: if_split_asm nat.splits elim!: may_lock.cases intro: may_lock.intros)

lemma may_lock_release_all_conv [simp]:
  "may_lock (release_all l t) t = may_lock l t"
by(cases l, auto split: if_split_asm intro!: may_lockI elim: may_lockE)

lemma may_lock_t_may_lock_unlock_lock_t: 
  "may_lock l t \<Longrightarrow> may_lock (unlock_lock l) t"
by(auto intro: may_lock.intros elim!: may_lockE split: nat.split)


lemma may_lock_has_locks_lock_lock_0: 
  "\<lbrakk>may_lock l t'; t \<noteq> t'\<rbrakk> \<Longrightarrow> has_locks (lock_lock l t') t = 0"
by(auto elim!: may_lock.cases)

lemma has_locks_unlock_lock_conv [simp]:
  "has_lock l t \<Longrightarrow> has_locks (unlock_lock l) t = has_locks l t - 1"
by(cases l)(auto split: nat.split)

lemma has_lock_lock_lock_unlock_lock_id [simp]:
  "has_lock l t \<Longrightarrow> lock_lock (unlock_lock l) t = l"
by(cases l)(auto split: if_split_asm nat.split)

lemma may_lock_unlock_lock_lock_lock_id [simp]:
  "may_lock l t \<Longrightarrow> unlock_lock (lock_lock l t) = l"
by(cases l) auto


lemma may_lock_has_locks_0:
  "\<lbrakk> may_lock l t; t \<noteq> t' \<rbrakk> \<Longrightarrow> has_locks l t' = 0"
by(auto elim!: may_lockE)


fun upd_lock :: "'t lock \<Rightarrow> 't \<Rightarrow> lock_action \<Rightarrow> 't lock"
where
  "upd_lock l t Lock = lock_lock l t"
| "upd_lock l t Unlock = unlock_lock l"
| "upd_lock l t UnlockFail = l"
| "upd_lock l t ReleaseAquire = release_all l t"

fun upd_locks :: "'t lock \<Rightarrow> 't \<Rightarrow> lock_action list \<Rightarrow> 't lock"
where
  "upd_locks l t [] = l"
| "upd_locks l t (L # Ls) = upd_locks (upd_lock l t L) t Ls"

lemma upd_locks_append [simp]:
  "upd_locks l t (Ls @ Ls') = upd_locks (upd_locks l t Ls) t Ls'"
by(induct Ls arbitrary: l, auto)

lemma upd_lock_Some_thread_idD:
  assumes ul: "upd_lock l t L = \<lfloor>(t', n)\<rfloor>"
  and tt': "t \<noteq> t'"
  shows "\<exists>n. l = \<lfloor>(t', n)\<rfloor>"
proof(cases L)
  case Lock
  with ul tt' show ?thesis
    by(cases l, auto)
next
  case Unlock
  with ul tt' show ?thesis
    by(auto dest: unlock_lock_SomeD)
next
  case UnlockFail
  with ul show ?thesis by(simp)
next
  case ReleaseAcquire
  with ul show ?thesis
    by(cases l, auto split: if_split_asm)
qed


lemma has_lock_upd_lock_implies_has_lock:
  "\<lbrakk> has_lock (upd_lock l t L) t'; t \<noteq> t' \<rbrakk> \<Longrightarrow> has_lock l t'"
by(cases l L rule: option.exhaust[case_product lock_action.exhaust])(auto split: if_split_asm nat.split_asm)

lemma has_lock_upd_locks_implies_has_lock:
  "\<lbrakk> has_lock (upd_locks l t Ls) t'; t \<noteq> t' \<rbrakk> \<Longrightarrow> has_lock l t'"
by(induct l t Ls rule: upd_locks.induct)(auto intro: has_lock_upd_lock_implies_has_lock)

(* Preconditions for lock actions *)

fun lock_action_ok :: "'t lock \<Rightarrow> 't \<Rightarrow> lock_action \<Rightarrow> bool" where
  "lock_action_ok l t Lock = may_lock l t"
| "lock_action_ok l t Unlock = has_lock l t"
| "lock_action_ok l t UnlockFail = (\<not> has_lock l t)"
| "lock_action_ok l t ReleaseAcquire = True"

fun lock_actions_ok :: "'t lock \<Rightarrow> 't \<Rightarrow> lock_action list \<Rightarrow> bool" where
  "lock_actions_ok l t [] = True"
| "lock_actions_ok l t (L # Ls) = (lock_action_ok l t L \<and> lock_actions_ok (upd_lock l t L) t Ls)"

lemma lock_actions_ok_append [simp]:
  "lock_actions_ok l t (Ls @ Ls') \<longleftrightarrow> lock_actions_ok l t Ls \<and> lock_actions_ok (upd_locks l t Ls) t Ls'"
by(induct Ls arbitrary: l) auto

lemma not_lock_action_okE [consumes 1, case_names Lock Unlock UnlockFail]:
  "\<lbrakk> \<not> lock_action_ok l t L;
     \<lbrakk> L = Lock; \<not> may_lock l t \<rbrakk> \<Longrightarrow> Q;
     \<lbrakk> L = Unlock; \<not> has_lock l t \<rbrakk> \<Longrightarrow> Q;
     \<lbrakk> L = UnlockFail; has_lock l t \<rbrakk> \<Longrightarrow> Q\<rbrakk>
  \<Longrightarrow> Q"
by(cases L) auto

lemma may_lock_upd_lock_conv [simp]:
  "lock_action_ok l t L \<Longrightarrow> may_lock (upd_lock l t L) t = may_lock l t"
by(cases L) auto

lemma may_lock_upd_locks_conv [simp]:
  "lock_actions_ok l t Ls \<Longrightarrow> may_lock (upd_locks l t Ls) t = may_lock l t"
by(induct l t Ls rule: upd_locks.induct) simp_all

lemma lock_actions_ok_Lock_may_lock:
  "\<lbrakk> lock_actions_ok l t Ls; Lock \<in> set Ls \<rbrakk> \<Longrightarrow> may_lock l t"
by(induct l t Ls rule: lock_actions_ok.induct) auto

lemma has_locks_lock_lock_conv' [simp]:
  "\<lbrakk> may_lock l t'; t \<noteq> t' \<rbrakk> \<Longrightarrow> has_locks (lock_lock l t') t = has_locks l t"
by(cases l)(auto elim: may_lock.cases)

lemma has_locks_unlock_lock_conv' [simp]:
  "\<lbrakk> has_lock l t'; t \<noteq> t' \<rbrakk> \<Longrightarrow> has_locks (unlock_lock l) t = has_locks l t"
by(cases l)(auto split: if_split_asm nat.split)

lemma has_locks_release_all_conv' [simp]:
  "t \<noteq> t' \<Longrightarrow> has_locks (release_all l t') t = has_locks l t"
by(cases l) auto

lemma has_locks_acquire_locks_conv' [simp]:
  "\<lbrakk> may_lock l t; t \<noteq> t' \<rbrakk> \<Longrightarrow> has_locks (acquire_locks l t n) t' = has_locks l t'"
by(induct l t n rule: acquire_locks.induct) simp_all

lemma lock_action_ok_has_locks_upd_lock_eq_has_locks [simp]:
  "\<lbrakk> lock_action_ok l t' L; t \<noteq> t' \<rbrakk> \<Longrightarrow> has_locks (upd_lock l t' L) t = has_locks l t"
by(cases L) auto

lemma lock_actions_ok_has_locks_upd_locks_eq_has_locks [simp]:
  "\<lbrakk> lock_actions_ok l t' Ls; t \<noteq> t' \<rbrakk> \<Longrightarrow> has_locks (upd_locks l t' Ls) t = has_locks l t"
by(induct l t' Ls rule: upd_locks.induct) simp_all

lemma has_lock_acquire_locks_implies_has_lock:
  "\<lbrakk> has_lock (acquire_locks l t n) t'; t \<noteq> t' \<rbrakk> \<Longrightarrow> has_lock l t'"
 unfolding acquire_locks_conv
 by(cases n)(auto split: if_split_asm)

lemma has_lock_has_lock_acquire_locks:
  "has_lock l T \<Longrightarrow> has_lock (acquire_locks l t n) T"
  unfolding acquire_locks_conv
  by(auto)


fun lock_actions_ok' :: "'t lock \<Rightarrow> 't \<Rightarrow> lock_action list \<Rightarrow> bool" where
  "lock_actions_ok' l t [] = True"
| "lock_actions_ok' l t (L#Ls) = ((L = Lock \<and> \<not> may_lock l t) \<or>
                                  lock_action_ok l t L \<and> lock_actions_ok' (upd_lock l t L) t Ls)"

lemma lock_actions_ok'_iff:
  "lock_actions_ok' l t las \<longleftrightarrow> 
   lock_actions_ok l t las \<or> (\<exists>xs ys. las = xs @ Lock # ys \<and> lock_actions_ok l t xs \<and> \<not> may_lock (upd_locks l t xs) t)"
proof(induct l t las rule: lock_actions_ok.induct)
  case (2 L t LA LAS)
  show ?case
  proof(cases "LA = Lock \<and> \<not> may_lock L t")
    case True
    hence "(\<exists>ys. Lock # LAS = [] @ Lock # ys) \<and> lock_actions_ok L t [] \<and> \<not> may_lock (upd_locks L t []) t"
      by(simp)
    with True show ?thesis by(simp (no_asm))(blast)
  next
    case False
    with 2 show ?thesis
      by(fastforce simp add: Cons_eq_append_conv elim: allE[where x="LA # xs" for xs])
  qed
qed simp

lemma lock_actions_ok'E[consumes 1, case_names ok Lock]:
  "\<lbrakk> lock_actions_ok' l t las;
     lock_actions_ok l t las \<Longrightarrow> P;
     \<And>xs ys. \<lbrakk> las = xs @ Lock # ys; lock_actions_ok l t xs; \<not> may_lock (upd_locks l t xs) t \<rbrakk> \<Longrightarrow> P \<rbrakk> 
  \<Longrightarrow> P"
by(auto simp add: lock_actions_ok'_iff)

end
