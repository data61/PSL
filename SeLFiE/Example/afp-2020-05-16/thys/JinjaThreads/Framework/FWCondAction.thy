(*  Title:      JinjaThreads/Framework/FWCondAction.thy
    Author:     Andreas Lochbihler
*)

section \<open>Semantics of the thread actions for purely conditional purpose such as Join\<close>

theory FWCondAction
imports
  FWState
begin

locale final_thread =
  fixes final :: "'x \<Rightarrow> bool"
begin

primrec cond_action_ok :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> 't conditional_action \<Rightarrow> bool" where
  "\<And>ln. cond_action_ok s t (Join T) = 
   (case thr s T of None \<Rightarrow> True | \<lfloor>(x, ln)\<rfloor> \<Rightarrow> t \<noteq> T \<and> final x \<and> ln = no_wait_locks \<and> wset s T = None)"
| "cond_action_ok s t Yield = True"

primrec cond_action_oks :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> 't conditional_action list \<Rightarrow> bool" where
  "cond_action_oks s t [] = True"
| "cond_action_oks s t (ct#cts) = (cond_action_ok s t ct \<and> cond_action_oks s t cts)"

lemma cond_action_oks_append [simp]:
  "cond_action_oks s t (cts @ cts') \<longleftrightarrow> cond_action_oks s t cts \<and> cond_action_oks s t cts'"
by(induct cts, auto)

lemma cond_action_oks_conv_set:
  "cond_action_oks s t cts \<longleftrightarrow> (\<forall>ct \<in> set cts. cond_action_ok s t ct)"
by(induct cts) simp_all

lemma cond_action_ok_Join:
  "\<And>ln. \<lbrakk> cond_action_ok s t (Join T); thr s T = \<lfloor>(x, ln)\<rfloor> \<rbrakk> \<Longrightarrow> final x \<and> ln = no_wait_locks \<and> wset s T = None"
by(auto)

lemma cond_action_oks_Join:
  "\<And>ln. \<lbrakk> cond_action_oks s t cas; Join T \<in> set cas; thr s T = \<lfloor>(x, ln)\<rfloor> \<rbrakk> 
  \<Longrightarrow> final x \<and> ln = no_wait_locks \<and> wset s T = None \<and> t \<noteq> T"
by(induct cas)(auto)

lemma cond_action_oks_upd:
  assumes tst: "thr s t = \<lfloor>xln\<rfloor>"
  shows "cond_action_oks (locks s, (thr s(t \<mapsto> xln'), shr s), wset s, interrupts s) t cas = cond_action_oks s t cas"
proof(induct cas)
  case Nil thus ?case by simp
next
  case (Cons ca cas)
  from tst have eq: "cond_action_ok (locks s, (thr s(t \<mapsto> xln'), shr s), wset s, interrupts s) t ca = cond_action_ok s t ca"
    by(cases ca) auto
  with Cons show ?case by(auto simp del: fun_upd_apply)
qed

lemma cond_action_ok_shr_change:
  "cond_action_ok (ls, (ts, m), ws, is) t ct \<Longrightarrow> cond_action_ok (ls, (ts, m'), ws, is) t ct"
by(cases ct) auto

lemma cond_action_oks_shr_change:
  "cond_action_oks (ls, (ts, m), ws, is) t cts \<Longrightarrow> cond_action_oks (ls, (ts, m'), ws, is) t cts"
by(auto simp add: cond_action_oks_conv_set intro: cond_action_ok_shr_change)

primrec cond_action_ok' :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> 't conditional_action \<Rightarrow> bool" 
where
  "cond_action_ok' _ _ (Join t) = True"
| "cond_action_ok' _ _ Yield = True"

primrec cond_action_oks' :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> 't conditional_action list \<Rightarrow> bool" where
  "cond_action_oks' s t [] = True"
| "cond_action_oks' s t (ct#cts) = (cond_action_ok' s t ct \<and> cond_action_oks' s t cts)"

lemma cond_action_oks'_append [simp]:
  "cond_action_oks' s t (cts @ cts') \<longleftrightarrow> cond_action_oks' s t cts \<and> cond_action_oks' s t cts'"
by(induct cts, auto)

lemma cond_action_oks'_subset_Join:
  "set cts \<subseteq> insert Yield (range Join) \<Longrightarrow> cond_action_oks' s t cts"
apply(induct cts)
apply(auto)
done

end

definition collect_cond_actions :: "'t conditional_action list \<Rightarrow> 't set" where
  "collect_cond_actions cts = {t. Join t \<in> set cts}"

declare collect_cond_actions_def [simp]

lemma cond_action_ok_final_change:
  "\<lbrakk> final_thread.cond_action_ok final1 s1 t ca;
     \<And>t. thr s1 t = None \<longleftrightarrow> thr s2 t = None; 
     \<And>t x1. \<lbrakk> thr s1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>; final1 x1; wset s1 t = None \<rbrakk> 
     \<Longrightarrow> \<exists>x2. thr s2 t = \<lfloor>(x2, no_wait_locks)\<rfloor> \<and> final2 x2 \<and> ln2 = no_wait_locks \<and> wset s2 t = None \<rbrakk>
  \<Longrightarrow> final_thread.cond_action_ok final2 s2 t ca"
apply(cases ca)
apply(fastforce simp add: final_thread.cond_action_ok.simps)+
done

lemma cond_action_oks_final_change:
  assumes major: "final_thread.cond_action_oks final1 s1 t cas"
  and minor: "\<And>t. thr s1 t = None \<longleftrightarrow> thr s2 t = None"
    "\<And>t x1. \<lbrakk> thr s1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>; final1 x1; wset s1 t = None \<rbrakk> 
     \<Longrightarrow> \<exists>x2. thr s2 t = \<lfloor>(x2, no_wait_locks)\<rfloor> \<and> final2 x2 \<and> ln2 = no_wait_locks \<and> wset s2 t = None"
  shows "final_thread.cond_action_oks final2 s2 t cas"
using major
by(induct cas)(auto simp add: final_thread.cond_action_oks.simps intro: cond_action_ok_final_change[OF _ minor])

end
