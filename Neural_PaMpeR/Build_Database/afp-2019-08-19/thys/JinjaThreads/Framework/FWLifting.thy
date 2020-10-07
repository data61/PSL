(*  Title:      JinjaThreads/Framework/FWLifting.thy
    Author:     Andreas Lochbihler
*)

section \<open>Lifting of thread-local properties to the multithreaded case\<close>

theory FWLifting
imports
  FWWellform
begin

text\<open>Lifting for properties that only involve thread-local state information and the shared memory.\<close>

definition
  ts_ok :: "('t \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool) \<Rightarrow> ('l, 't,'x) thread_info \<Rightarrow> 'm \<Rightarrow> bool"
where
  "\<And>ln. ts_ok P ts m \<equiv> \<forall>t. case (ts t) of None \<Rightarrow> True | \<lfloor>(x, ln)\<rfloor> \<Rightarrow> P t x m"

lemma ts_okI:
  "\<lbrakk> \<And>t x ln. ts t = \<lfloor>(x, ln)\<rfloor> \<Longrightarrow> P t x m \<rbrakk> \<Longrightarrow> ts_ok P ts m"
by(auto simp add: ts_ok_def)

lemma ts_okE:
  "\<lbrakk> ts_ok P ts m; \<lbrakk> \<And>t x ln. ts t = \<lfloor>(x, ln)\<rfloor> \<Longrightarrow> P t x m \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
by(auto simp add: ts_ok_def)

lemma ts_okD:
  "\<And>ln. \<lbrakk> ts_ok P ts m; ts t = \<lfloor>(x, ln)\<rfloor> \<rbrakk> \<Longrightarrow> P t x m"
by(auto simp add: ts_ok_def)

lemma ts_ok_True [simp]:
  "ts_ok (\<lambda>t m x. True) ts m"
by(auto intro: ts_okI)

lemma ts_ok_conj:
  "ts_ok (\<lambda>t x m. P t x m \<and> Q t x m) = (\<lambda>ts m. ts_ok P ts m \<and> ts_ok Q ts m)"
by(auto intro: ts_okI intro!: ext dest: ts_okD)

lemma ts_ok_mono:
  "\<lbrakk> ts_ok P ts m; \<And>t x. P t x m \<Longrightarrow> Q t x m \<rbrakk> \<Longrightarrow> ts_ok Q ts m"
by(auto intro!: ts_okI dest: ts_okD)

text\<open>Lifting for properites, that also require additional data that does not change during execution\<close>

definition
  ts_inv :: "('i \<Rightarrow> 't \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool) \<Rightarrow> ('t \<rightharpoonup> 'i) \<Rightarrow> ('l,'t,'x) thread_info \<Rightarrow> 'm \<Rightarrow> bool"
where
  "\<And>ln. ts_inv P I ts m \<equiv> \<forall>t. case (ts t) of None \<Rightarrow> True | \<lfloor>(x, ln)\<rfloor> \<Rightarrow> \<exists>i. I t = \<lfloor>i\<rfloor> \<and> P i t x m" 

lemma ts_invI:
  "\<lbrakk> \<And>t x ln. ts t = \<lfloor>(x, ln)\<rfloor> \<Longrightarrow> \<exists>i. I t = \<lfloor>i\<rfloor> \<and> P i t x m \<rbrakk> \<Longrightarrow> ts_inv P I ts m"
by(simp add: ts_inv_def)

lemma ts_invE:
  "\<lbrakk> ts_inv P I ts m; \<forall>t x ln. ts t = \<lfloor>(x, ln)\<rfloor> \<longrightarrow> (\<exists>i. I t = \<lfloor>i\<rfloor> \<and> P i t x m) \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
by(auto simp add: ts_inv_def)

lemma ts_invD:
  "\<And>ln. \<lbrakk> ts_inv P I ts m; ts t = \<lfloor>(x, ln)\<rfloor> \<rbrakk> \<Longrightarrow> \<exists>i. I t = \<lfloor>i\<rfloor> \<and> P i t x m"
by(auto simp add: ts_inv_def)

text \<open>Wellformedness properties for lifting\<close>

definition
  ts_inv_ok :: "('l,'t,'x) thread_info \<Rightarrow> ('t \<rightharpoonup> 'i) \<Rightarrow> bool"
where
  "ts_inv_ok ts I \<equiv> \<forall>t. ts t = None \<longleftrightarrow> I t = None"

lemma ts_inv_okI:
  "(\<And>t. ts t = None \<longleftrightarrow> I t = None) \<Longrightarrow> ts_inv_ok ts I"
by(clarsimp simp add: ts_inv_ok_def)

lemma ts_inv_okI2:
  "(\<And>t. (\<exists>v. ts t = \<lfloor>v\<rfloor>) \<longleftrightarrow> (\<exists>v. I t = \<lfloor>v\<rfloor>)) \<Longrightarrow> ts_inv_ok ts I"
by(force simp add: ts_inv_ok_def)

lemma ts_inv_okE:
  "\<lbrakk> ts_inv_ok ts I; \<forall>t. ts t = None \<longleftrightarrow> I t = None \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
by(force simp add: ts_inv_ok_def)

lemma ts_inv_okE2:
  "\<lbrakk> ts_inv_ok ts I; \<forall>t. (\<exists>v. ts t = \<lfloor>v\<rfloor>) \<longleftrightarrow> (\<exists>v. I t = \<lfloor>v\<rfloor>) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
by(force simp add: ts_inv_ok_def)

lemma ts_inv_okD:
  "ts_inv_ok ts I \<Longrightarrow> (ts t = None) \<longleftrightarrow> (I t = None)"
by(erule ts_inv_okE, blast)

lemma ts_inv_okD2:
  "ts_inv_ok ts I \<Longrightarrow> (\<exists>v. ts t = \<lfloor>v\<rfloor>) \<longleftrightarrow> (\<exists>v. I t = \<lfloor>v\<rfloor>)"
by(erule ts_inv_okE2, blast)

lemma ts_inv_ok_conv_dom_eq:
  "ts_inv_ok ts I \<longleftrightarrow> (dom ts = dom I)"
proof -
  have "ts_inv_ok ts I \<longleftrightarrow> (\<forall>t. ts t = None \<longleftrightarrow> I t = None)"
    unfolding ts_inv_ok_def by blast
  also have "\<dots> \<longleftrightarrow> (\<forall>t. t \<in> - dom ts \<longleftrightarrow> t \<in> - dom I)" by(force)
  also have "\<dots> \<longleftrightarrow> dom ts = dom I" by auto
  finally show ?thesis .
qed

lemma ts_inv_ok_upd_ts:
  "\<lbrakk> ts t = \<lfloor>x\<rfloor>; ts_inv_ok ts I \<rbrakk> \<Longrightarrow> ts_inv_ok (ts(t \<mapsto> x')) I"
by(auto dest!: ts_inv_okD intro!: ts_inv_okI split: if_splits)

lemma ts_inv_upd_map_option:
  assumes "ts_inv P I ts m"
  and "\<And>x ln. ts t = \<lfloor>(x, ln)\<rfloor> \<Longrightarrow> P (the (I t)) t (fst (f (x, ln))) m"
  shows "ts_inv P I (ts(t := (map_option f (ts t)))) m"
using assms
by(fastforce intro!: ts_invI split: if_split_asm dest: ts_invD)

fun upd_inv :: "('t \<rightharpoonup> 'i) \<Rightarrow> ('i \<Rightarrow> 't \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool) \<Rightarrow> ('t,'x,'m) new_thread_action \<Rightarrow> ('t \<rightharpoonup> 'i)"
where
  "upd_inv I P (NewThread t x m) = I(t \<mapsto> SOME i. P i t x m)"
| "upd_inv I P _ = I"

fun upd_invs :: "('t \<rightharpoonup> 'i) \<Rightarrow> ('i \<Rightarrow> 't \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> bool) \<Rightarrow> ('t,'x,'m) new_thread_action list \<Rightarrow> ('t \<rightharpoonup> 'i)"
where
  "upd_invs I P [] = I"
| "upd_invs I P (ta#tas) = upd_invs (upd_inv I P ta) P tas"

lemma upd_invs_append [simp]:
  "upd_invs I P (xs @ ys) = upd_invs (upd_invs I P xs) P ys"
by(induct xs arbitrary: I)(auto)

lemma ts_inv_ok_upd_inv':
 "ts_inv_ok ts I \<Longrightarrow> ts_inv_ok (redT_updT' ts ta) (upd_inv I P ta)"
by(cases ta)(auto intro!: ts_inv_okI elim: ts_inv_okD del: iffI)

lemma ts_inv_ok_upd_invs':
  "ts_inv_ok ts I \<Longrightarrow> ts_inv_ok (redT_updTs' ts tas) (upd_invs I P tas)"
proof(induct tas arbitrary: ts I)
  case Nil thus ?case by simp
next
  case (Cons TA TAS TS I)
  note IH = \<open>\<And>ts I. ts_inv_ok ts I \<Longrightarrow> ts_inv_ok (redT_updTs' ts TAS) (upd_invs I P TAS)\<close>
  note esok = \<open>ts_inv_ok TS I\<close>
  from esok have "ts_inv_ok (redT_updT' TS TA) (upd_inv I P TA)"
    by -(rule ts_inv_ok_upd_inv')
  hence "ts_inv_ok (redT_updTs' (redT_updT' TS TA) TAS) (upd_invs (upd_inv I P TA) P TAS)"
    by (rule IH)
  thus ?case by simp
qed

lemma ts_inv_ok_upd_inv:
 "ts_inv_ok ts I \<Longrightarrow> ts_inv_ok (redT_updT ts ta) (upd_inv I P ta)"
apply(cases ta)
apply(auto intro!: ts_inv_okI elim: ts_inv_okD del: iffI)
done

lemma ts_inv_ok_upd_invs:
  "ts_inv_ok ts I \<Longrightarrow> ts_inv_ok (redT_updTs ts tas) (upd_invs I P tas)"
proof(induct tas arbitrary: ts I)
  case Nil thus ?case by simp
next
  case (Cons TA TAS TS I)
  note IH = \<open>\<And>ts I. ts_inv_ok ts I \<Longrightarrow> ts_inv_ok (redT_updTs ts TAS) (upd_invs I P TAS)\<close>
  note esok = \<open>ts_inv_ok TS I\<close>
  from esok have "ts_inv_ok (redT_updT TS TA) (upd_inv I P TA)"
    by -(rule ts_inv_ok_upd_inv)
  hence "ts_inv_ok (redT_updTs (redT_updT TS TA) TAS) (upd_invs (upd_inv I P TA) P TAS)"
    by (rule IH)
  thus ?case by simp
qed

lemma ts_inv_ok_inv_ext_upd_inv:
  "\<lbrakk> ts_inv_ok ts I; thread_ok ts ta \<rbrakk> \<Longrightarrow> I \<subseteq>\<^sub>m upd_inv I P ta"
by(cases ta)(auto intro!: map_le_same_upd dest: ts_inv_okD)

lemma ts_inv_ok_inv_ext_upd_invs:
  "\<lbrakk> ts_inv_ok ts I; thread_oks ts tas\<rbrakk>
  \<Longrightarrow> I \<subseteq>\<^sub>m upd_invs I P tas"
proof(induct tas arbitrary: ts I)
  case Nil thus ?case by simp
next
  case (Cons TA TAS TS I)
  note IH = \<open>\<And>ts I. \<lbrakk> ts_inv_ok ts I; thread_oks ts TAS\<rbrakk> \<Longrightarrow> I \<subseteq>\<^sub>m upd_invs I P TAS\<close>
  note esinv = \<open>ts_inv_ok TS I\<close>
  note cct = \<open>thread_oks TS (TA # TAS)\<close>
  from esinv cct have "I \<subseteq>\<^sub>m upd_inv I P TA"
    by(auto intro: ts_inv_ok_inv_ext_upd_inv)
  also from esinv cct have "ts_inv_ok (redT_updT' TS TA) (upd_inv I P TA)"
    by(auto intro: ts_inv_ok_upd_inv')
  with cct have "upd_inv I P TA \<subseteq>\<^sub>m upd_invs (upd_inv I P TA) P TAS"
    by(auto intro: IH)
  finally show ?case by simp
qed

lemma upd_invs_Some:
  "\<lbrakk> thread_oks ts tas; I t = \<lfloor>i\<rfloor>; ts t = \<lfloor>x\<rfloor> \<rbrakk> \<Longrightarrow> upd_invs I Q tas t = \<lfloor>i\<rfloor>"
proof(induct tas arbitrary: ts I)
  case Nil thus ?case by simp
next
  case (Cons TA TAS TS I)
  note IH = \<open>\<And>ts I. \<lbrakk>thread_oks ts TAS; I t = \<lfloor>i\<rfloor>; ts t = \<lfloor>x\<rfloor>\<rbrakk> \<Longrightarrow> upd_invs I Q TAS t = \<lfloor>i\<rfloor>\<close>
  note cct = \<open>thread_oks TS (TA # TAS)\<close>
  note it = \<open>I t = \<lfloor>i\<rfloor>\<close>
  note est = \<open>TS t = \<lfloor>x\<rfloor>\<close>
  from cct have cctta: "thread_ok TS TA"
    and ccttas: "thread_oks (redT_updT' TS TA) TAS" by auto
  from cctta it est have "upd_inv I Q TA t = \<lfloor>i\<rfloor>"
    by(cases TA, auto)
  moreover
  have "redT_updT' TS TA t = \<lfloor>x\<rfloor>" using cctta est
    by - (rule redT_updT'_Some) 
  ultimately have "upd_invs (upd_inv I Q TA) Q TAS t = \<lfloor>i\<rfloor>" using ccttas
    by -(erule IH)
  thus ?case by simp
qed

lemma upd_inv_Some_eq:
  "\<lbrakk> thread_ok ts ta; ts t = \<lfloor>x\<rfloor> \<rbrakk> \<Longrightarrow> upd_inv I Q ta t = I t"
by(cases ta, auto)

lemma upd_invs_Some_eq: "\<lbrakk> thread_oks ts tas; ts t = \<lfloor>x\<rfloor> \<rbrakk> \<Longrightarrow> upd_invs I Q tas t = I t"
proof(induct tas arbitrary: ts I)
  case Nil thus ?case by simp
next
  case (Cons TA TAS TS I)
  note IH = \<open>\<And>ts I. \<lbrakk>thread_oks ts TAS; ts t = \<lfloor>x\<rfloor>\<rbrakk> \<Longrightarrow> upd_invs I Q TAS t = I t\<close>
  note cct = \<open>thread_oks TS (TA # TAS)\<close>
  note est = \<open>TS t = \<lfloor>x\<rfloor>\<close>
  from cct est have "upd_invs (upd_inv I Q TA) Q TAS t = upd_inv I Q TA t"
    apply(clarsimp)
    apply(erule IH)
    by(rule redT_updT'_Some)
  also from cct est have "\<dots> = I t" 
    by(auto elim: upd_inv_Some_eq)
  finally show ?case by simp
qed

lemma SOME_new_thread_upd_invs:
  assumes Qsome: "Q (SOME i. Q i t x m) t x m"
  and nt: "NewThread t x m \<in> set tas"
  and cct: "thread_oks ts tas"
  shows "\<exists>i. upd_invs I Q tas t = \<lfloor>i\<rfloor> \<and> Q i t x m"
proof(rule exI[where x="SOME i. Q i t x m"])
  from nt cct have "upd_invs I Q tas t = \<lfloor>SOME i. Q i t x m\<rfloor>"
  proof(induct tas arbitrary: ts I)
    case Nil thus ?case by simp
  next
    case (Cons TA TAS TS I)
    note IH = \<open>\<And>ts I. \<lbrakk> NewThread t x m \<in> set TAS; thread_oks ts TAS \<rbrakk> \<Longrightarrow> upd_invs I Q TAS t = \<lfloor>SOME i. Q i t x m\<rfloor>\<close>
    note nt = \<open>NewThread t x m \<in> set (TA # TAS)\<close>
    note cct = \<open>thread_oks TS (TA # TAS)\<close>
    { assume nt': "NewThread t x m \<in> set TAS"
      from cct have ?case
        apply(clarsimp)
        by(rule IH[OF nt']) }
    moreover
    { assume ta: "TA = NewThread t x m"
      with cct have rup: "redT_updT' TS TA t = \<lfloor>(undefined, no_wait_locks)\<rfloor>"
        by(simp)
      from cct have cctta: "thread_oks (redT_updT' TS TA) TAS" by simp
      from ta have "upd_inv I Q TA t = \<lfloor>SOME i. Q i t x m\<rfloor>"
        by(simp)
      hence ?case 
        by(clarsimp simp add: upd_invs_Some_eq[OF cctta, OF rup]) }
    ultimately show ?case using nt by auto
  qed
  with Qsome show "upd_invs I Q tas t = \<lfloor>SOME i. Q i t x m\<rfloor> \<and> Q (SOME i. Q i t x m) t x m"
    by(simp)
qed

lemma ts_ok_into_ts_inv_const:
  assumes "ts_ok P ts m"
  obtains I where "ts_inv (\<lambda>_. P) I ts m"
proof -
  from assms have "ts_inv (\<lambda>_. P) (\<lambda>t. if t \<in> dom ts then Some undefined else None) ts m"
    by(auto intro!: ts_invI dest: ts_okD)
  thus thesis by(rule that)
qed

lemma ts_inv_const_into_ts_ok:
  "ts_inv (\<lambda>_. P) I ts m \<Longrightarrow> ts_ok P ts m"
by(auto intro!: ts_okI dest: ts_invD)

lemma ts_inv_into_ts_ok_Ex:
  "ts_inv Q I ts m \<Longrightarrow> ts_ok (\<lambda>t x m. \<exists>i. Q i t x m) ts m"
by(rule ts_okI)(blast dest: ts_invD)

lemma ts_ok_Ex_into_ts_inv:
  "ts_ok (\<lambda>t x m. \<exists>i. Q i t x m) ts m \<Longrightarrow> \<exists>I. ts_inv Q I ts m"
by(rule exI[where x="\<lambda>t. \<lfloor>SOME i. Q i t (fst (the (ts t))) m\<rfloor>"])(auto 4 4 dest: ts_okD intro: someI intro: ts_invI)

lemma Ex_ts_inv_conv_ts_ok:
  "(\<exists>I. ts_inv Q I ts m) \<longleftrightarrow> (ts_ok (\<lambda>t x m. \<exists>i. Q i t x m) ts m)"
by(auto dest: ts_inv_into_ts_ok_Ex ts_ok_Ex_into_ts_inv)

end
