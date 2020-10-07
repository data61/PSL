(*  Title:       AWN.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke
*)

section "Terms of the Algebra for Wireless Networks"

theory AWN
imports Lib
begin

subsection "Sequential Processes"

type_synonym ip = nat
type_synonym data = nat

text \<open>
  Most of AWN is independent of the type of messages, but the closed layer turns
  newpkt actions into the arrival of newpkt messages. We use a type class to maintain
  some abstraction (and independence from the definition of particular protocols).
\<close>

class msg =
  fixes newpkt :: "data \<times> ip \<Rightarrow> 'a"
    and eq_newpkt :: "'a \<Rightarrow> bool"
  assumes eq_newpkt_eq [simp]: "eq_newpkt (newpkt (d, i))"

text \<open>
  Sequential process terms abstract over the types of data states (@{typ 's}),
  messages (@{typ 'm}), process names (@{typ 'p}),and labels (@{typ 'l}).
\<close>

datatype (dead 's, dead 'm, dead 'p, 'l) seqp =
    GUARD "'l" "'s \<Rightarrow> 's set" "('s, 'm, 'p, 'l) seqp"
  | ASSIGN "'l" "'s \<Rightarrow> 's" "('s, 'm, 'p, 'l) seqp"
  | CHOICE "('s, 'm, 'p, 'l) seqp" "('s, 'm, 'p, 'l) seqp"
  | UCAST "'l" "'s \<Rightarrow> ip" "'s \<Rightarrow> 'm" "('s, 'm, 'p, 'l) seqp" "('s, 'm, 'p, 'l) seqp"
  | BCAST "'l" "'s \<Rightarrow> 'm" "('s, 'm, 'p, 'l) seqp"
  | GCAST "'l" "'s \<Rightarrow> ip set" "'s \<Rightarrow> 'm" "('s, 'm, 'p, 'l) seqp"
  | SEND "'l" "'s \<Rightarrow> 'm" "('s, 'm, 'p, 'l) seqp"
  | DELIVER "'l" "'s \<Rightarrow> data" "('s, 'm, 'p, 'l) seqp"
  | RECEIVE "'l" "'m \<Rightarrow> 's \<Rightarrow> 's" "('s, 'm, 'p, 'l) seqp"
  | CALL 'p
  for map: labelmap

syntax
  "_guard"    :: "['a,  ('s, 'm, 'p, unit) seqp] \<Rightarrow>  ('s, 'm, 'p, unit) seqp"
                 ("(\<open>unbreakable\<close>\<langle>_\<rangle>)//_" [0, 60] 60)
  "_lguard"   :: "['a, 'a,  ('s, 'm, 'p, unit) seqp] \<Rightarrow>  ('s, 'm, 'p, unit) seqp"
                 ("{_}(\<open>unbreakable\<close>\<langle>_\<rangle>)//_" [0, 0, 60] 60)
  "_ifguard"  :: "[pttrn, bool,  ('s, 'm, 'p, unit) seqp] \<Rightarrow>  ('s, 'm, 'p, unit) seqp"
                 ("(\<open>unbreakable\<close>\<langle>_. _\<rangle>)//_" [0, 0, 60] 60)

  "_bassign"  :: "[pttrn, 'a,  ('s, 'm, 'p, unit) seqp] \<Rightarrow>  ('s, 'm, 'p, unit) seqp"
                 ("(\<open>unbreakable\<close>\<lbrakk>_. _\<rbrakk>)//_" [0, 0, 60] 60)
  "_lbassign" :: "['a, pttrn, 'a, ('s, 'm, 'p, 'a) seqp] \<Rightarrow> ('s, 'm, 'p, 'a) seqp"
                 ("{_}(\<open>unbreakable\<close>\<lbrakk>_. _\<rbrakk>)//_" [0, 0, 0, 60] 60)

  "_assign"  :: "['a,  ('s, 'm, 'p, unit) seqp] \<Rightarrow>  ('s, 'm, 'p, unit) seqp"
                 ("((\<open>unbreakable\<close>\<lbrakk>_\<rbrakk>))//_" [0, 60] 60)
  "_lassign" :: "['a, 'a, ('s, 'm, 'p, 'a) seqp] \<Rightarrow> ('s, 'm, 'p, 'a) seqp"
                 ("({_}(\<open>unbreakable\<close>\<lbrakk>_\<rbrakk>))//_" [0, 0, 60] 60)

  "_unicast"  :: "['a, 'a,  ('s, 'm, 'p, unit) seqp,  ('s, 'm, 'p, unit) seqp] \<Rightarrow>  ('s, 'm, 'p, unit) seqp"
                 ("(3unicast'((1(3_),/ (3_))') .//(_)/ (2\<triangleright> _))" [0, 0, 60, 60] 60)
  "_lunicast" :: "['a, 'a, 'a, ('s, 'm, 'p, 'a) seqp, ('s, 'm, 'p, 'a) seqp] \<Rightarrow> ('s, 'm, 'p, 'a) seqp"
                 ("(3{_}unicast'((1(3_),/ (3_))') .//(_)/ (2\<triangleright> _))" [0, 0, 0, 60, 60] 60)

  "_bcast"    :: "['a,  ('s, 'm, 'p, unit) seqp] \<Rightarrow>  ('s, 'm, 'p, unit) seqp"
                 ("(3broadcast'((1(_))') .)//_" [0, 60] 60)
  "_lbcast"   :: "['a, 'a, ('s, 'm, 'p, 'a) seqp] \<Rightarrow> ('s, 'm, 'p, 'a) seqp"
                 ("(3{_}broadcast'((1(_))') .)//_" [0, 0, 60] 60)

  "_gcast"    :: "['a, 'a,  ('s, 'm, 'p, unit) seqp] \<Rightarrow>  ('s, 'm, 'p, unit) seqp"
                 ("(3groupcast'((1(_),/ (_))') .)//_" [0, 0, 60] 60)
  "_lgcast"   :: "['a, 'a, 'a, ('s, 'm, 'p, 'a) seqp] \<Rightarrow> ('s, 'm, 'p, 'a) seqp"
                 ("(3{_}groupcast'((1(_),/ (_))') .)//_" [0, 0, 0, 60] 60)

  "_send"     :: "['a,  ('s, 'm, 'p, unit) seqp] \<Rightarrow>  ('s, 'm, 'p, unit) seqp"
                 ("(3send'((_)') .)//_" [0, 60] 60)
  "_lsend"    :: "['a, 'a, ('s, 'm, 'p, 'a) seqp] \<Rightarrow> ('s, 'm, 'p, 'a) seqp"
                 ("(3{_}send'((_)') .)//_" [0, 0, 60] 60)

  "_deliver"  :: "['a,  ('s, 'm, 'p, unit) seqp] \<Rightarrow>  ('s, 'm, 'p, unit) seqp"
                 ("(3deliver'((_)') .)//_" [0, 60] 60)
  "_ldeliver" :: "['a, 'a, ('s, 'm, 'p, 'a) seqp] \<Rightarrow> ('s, 'm, 'p, 'a) seqp"
                 ("(3{_}deliver'((_)') .)//_" [0, 0, 60] 60)

  "_receive"  :: "['a,  ('s, 'm, 'p, unit) seqp] \<Rightarrow>  ('s, 'm, 'p, unit) seqp"
                 ("(3receive'((_)') .)//_" [0, 60] 60)
  "_lreceive" :: "['a, 'a, ('s, 'm, 'p, 'a) seqp] \<Rightarrow> ('s, 'm, 'p, 'a) seqp"
                 ("(3{_}receive'((_)') .)//_" [0, 0, 60] 60)

translations
  "_guard f p"     \<rightleftharpoons> "CONST GUARD () f p"
  "_lguard l f p"  \<rightleftharpoons> "CONST GUARD l f p"
  "_ifguard \<xi> e p" \<rightharpoonup> "CONST GUARD () (\<lambda>\<xi>. if e then {\<xi>} else {}) p"

  "_assign f p"    \<rightleftharpoons> "CONST ASSIGN () f p"
  "_lassign l f p" \<rightleftharpoons> "CONST ASSIGN l f p"

  "_bassign \<xi> e p"    \<rightleftharpoons> "CONST ASSIGN () (\<lambda>\<xi>. e) p"
  "_lbassign l \<xi> e p" \<rightleftharpoons> "CONST ASSIGN l (\<lambda>\<xi>. e) p"

  "_unicast fip fmsg p q"    \<rightleftharpoons> "CONST UCAST () fip fmsg p q"
  "_lunicast l fip fmsg p q" \<rightleftharpoons> "CONST UCAST l fip fmsg p q"

  "_bcast fmsg p"    \<rightleftharpoons> "CONST BCAST () fmsg p"
  "_lbcast l fmsg p" \<rightleftharpoons> "CONST BCAST l fmsg p"

  "_gcast fipset fmsg p"    \<rightleftharpoons> "CONST GCAST () fipset fmsg p"
  "_lgcast l fipset fmsg p" \<rightleftharpoons> "CONST GCAST l fipset fmsg p"

  "_send fmsg p"    \<rightleftharpoons> "CONST SEND () fmsg p"
  "_lsend l fmsg p" \<rightleftharpoons> "CONST SEND l fmsg p"

  "_deliver fdata p"    \<rightleftharpoons> "CONST DELIVER () fdata p"
  "_ldeliver l fdata p" \<rightleftharpoons> "CONST DELIVER l fdata p"

  "_receive fmsg p"    \<rightleftharpoons> "CONST RECEIVE () fmsg p"
  "_lreceive l fmsg p" \<rightleftharpoons> "CONST RECEIVE l fmsg p"

notation "CHOICE" ("((_)//\<oplus>//(_))" [56, 55] 55)
     and "CALL"   ("(3call'((3_)'))" [0] 60)

definition not_call :: "('s, 'm, 'p, 'l) seqp \<Rightarrow> bool"
where "not_call p \<equiv> \<forall>pn. p \<noteq> call(pn)"

lemma not_call_simps [simp]:
  "\<And>l fg p.         not_call ({l}\<langle>fg\<rangle> p)"
  "\<And>l fa p.         not_call ({l}\<lbrakk>fa\<rbrakk> p)"
  "\<And>p1 p2.          not_call (p1 \<oplus> p2)"
  "\<And>l fip fmsg p q. not_call ({l}unicast(fip, fmsg).p \<triangleright> q)"
  "\<And>l fmsg p.       not_call ({l}broadcast(fmsg).p)"
  "\<And>l fips fmsg p.  not_call ({l}groupcast(fips, fmsg).p)"
  "\<And>l fmsg p.       not_call ({l}send(fmsg).p)"
  "\<And>l fdata p.      not_call ({l}deliver(fdata).p)"
  "\<And>l fmsg p.       not_call ({l}receive(fmsg).p)"
  "\<And>l pn.         \<not>(not_call (call(pn)))"
  unfolding not_call_def by auto

definition not_choice :: "('s, 'm, 'p, 'l) seqp \<Rightarrow> bool"
where "not_choice p \<equiv> \<forall>p1 p2. p \<noteq> p1 \<oplus> p2"

lemma not_choice_simps [simp]:
  "\<And>l fg p.         not_choice ({l}\<langle>fg\<rangle> p)"
  "\<And>l fa p.         not_choice ({l}\<lbrakk>fa\<rbrakk> p)"
  "\<And>p1 p2.        \<not>(not_choice (p1 \<oplus> p2))"
  "\<And>l fip fmsg p q. not_choice ({l}unicast(fip, fmsg).p \<triangleright> q)"
  "\<And>l fmsg p.       not_choice ({l}broadcast(fmsg).p)"
  "\<And>l fips fmsg p.  not_choice ({l}groupcast(fips, fmsg).p)"
  "\<And>l fmsg p.       not_choice ({l}send(fmsg).p)"
  "\<And>l fdata p.      not_choice ({l}deliver(fdata).p)"
  "\<And>l fmsg p.       not_choice ({l}receive(fmsg).p)"
  "\<And>l pn.           not_choice (call(pn))"
  unfolding not_choice_def by auto

lemma seqp_congs:
  "\<And>l fg p. {l}\<langle>fg\<rangle> p = {l}\<langle>fg\<rangle> p"
  "\<And>l fa p. {l}\<lbrakk>fa\<rbrakk> p = {l}\<lbrakk>fa\<rbrakk> p"
  "\<And>p1 p2. p1 \<oplus> p2 = p1 \<oplus> p2"
  "\<And>l fip fmsg p q. {l}unicast(fip, fmsg).p \<triangleright> q = {l}unicast(fip, fmsg).p \<triangleright> q"
  "\<And>l fmsg p. {l}broadcast(fmsg).p = {l}broadcast(fmsg).p"
  "\<And>l fips fmsg p. {l}groupcast(fips, fmsg).p = {l}groupcast(fips, fmsg).p"
  "\<And>l fmsg p. {l}send(fmsg).p = {l}send(fmsg).p"
  "\<And>l fdata p. {l}deliver(fdata).p = {l}deliver(fdata).p"
  "\<And>l fmsg p. {l}receive(fmsg).p = {l}receive(fmsg).p"
  "\<And>l pn. call(pn) = call(pn)"
  by auto

text \<open>Remove data expressions from process terms.\<close>

fun seqp_skeleton :: "('s, 'm, 'p, 'l) seqp \<Rightarrow> (unit, unit, 'p, 'l) seqp"
where
    "seqp_skeleton ({l}\<langle>_\<rangle> p)                 = {l}\<langle>\<lambda>_. {()}\<rangle> (seqp_skeleton p)"
  | "seqp_skeleton ({l}\<lbrakk>_\<rbrakk> p)                 = {l}\<lbrakk>\<lambda>_. ()\<rbrakk> (seqp_skeleton p)"
  | "seqp_skeleton (p \<oplus> q)                   = (seqp_skeleton p) \<oplus> (seqp_skeleton q)"
  | "seqp_skeleton ({l}unicast(_, _). p \<triangleright> q) = {l}unicast(\<lambda>_. 0, \<lambda>_. ()). (seqp_skeleton p) \<triangleright> (seqp_skeleton q)"
  | "seqp_skeleton ({l}broadcast(_). p)      = {l}broadcast(\<lambda>_. ()). (seqp_skeleton p)"
  | "seqp_skeleton ({l}groupcast(_, _). p)   = {l}groupcast(\<lambda>_. {}, \<lambda>_. ()). (seqp_skeleton p)"
  | "seqp_skeleton ({l}send(_). p)           = {l}send(\<lambda>_. ()). (seqp_skeleton p)"
  | "seqp_skeleton ({l}deliver(_). p)        = {l}deliver(\<lambda>_. 0). (seqp_skeleton p)"
  | "seqp_skeleton ({l}receive(_). p)        = {l}receive(\<lambda>_ _. ()). (seqp_skeleton p)"
  | "seqp_skeleton (call(pn))                = call(pn)"

text \<open>Calculate the subterms of a term.\<close>

fun subterms :: "('s, 'm, 'p, 'l) seqp \<Rightarrow> ('s, 'm, 'p, 'l) seqp set"
where
    "subterms ({l}\<langle>fg\<rangle> p) = {{l}\<langle>fg\<rangle> p} \<union> subterms p"
  | "subterms ({l}\<lbrakk>fa\<rbrakk> p) = {{l}\<lbrakk>fa\<rbrakk> p} \<union> subterms p"
  | "subterms (p1 \<oplus> p2) = {p1 \<oplus> p2} \<union> subterms p1 \<union> subterms p2"
  | "subterms ({l}unicast(fip, fmsg). p \<triangleright> q) =
       {{l}unicast(fip, fmsg). p \<triangleright> q} \<union> subterms p \<union> subterms q"
  | "subterms ({l}broadcast(fmsg). p) = {{l}broadcast(fmsg). p} \<union> subterms p"
  | "subterms ({l}groupcast(fips, fmsg). p) = {{l}groupcast(fips, fmsg). p} \<union> subterms p"
  | "subterms ({l}send(fmsg). p) = {{l}send(fmsg).p} \<union> subterms p"
  | "subterms ({l}deliver(fdata). p) = {{l}deliver(fdata).p} \<union> subterms p"
  | "subterms ({l}receive(fmsg). p) = {{l}receive(fmsg).p} \<union> subterms p"
  | "subterms (call(pn)) = {call(pn)}"

lemma subterms_refl [simp]: "p \<in> subterms p"
  by (cases p) simp_all

lemma subterms_trans [elim]:
  assumes "q \<in> subterms p"
      and "r \<in> subterms q"
    shows "r \<in> subterms p"
  using assms by (induction p) auto

lemma root_in_subterms [simp]:
   "\<And>\<Gamma> pn. \<exists>pn'. \<Gamma> pn \<in> subterms (\<Gamma> pn')"
  by (rule_tac x=pn in exI) simp

lemma deriv_in_subterms [elim, dest]:
  "\<And>l f p q. {l}\<langle>f\<rangle> q \<in> subterms p \<Longrightarrow> q \<in> subterms p"
  "\<And>l fa p q. {l}\<lbrakk>fa\<rbrakk> q \<in> subterms p \<Longrightarrow> q \<in> subterms p"
  "\<And>p1 p2 p. p1 \<oplus> p2 \<in> subterms p \<Longrightarrow> p1 \<in> subterms p"
  "\<And>p1 p2 p. p1 \<oplus> p2 \<in> subterms p \<Longrightarrow> p2 \<in> subterms p"
  "\<And>l fip fmsg p q r. {l}unicast(fip, fmsg). q \<triangleright> r \<in> subterms p \<Longrightarrow> q \<in> subterms p"
  "\<And>l fip fmsg p q r. {l}unicast(fip, fmsg). q \<triangleright> r \<in> subterms p \<Longrightarrow> r \<in> subterms p"
  "\<And>l fmsg p q. {l}broadcast(fmsg). q \<in> subterms p \<Longrightarrow> q \<in> subterms p"
  "\<And>l fips fmsg p q. {l}groupcast(fips, fmsg). q \<in> subterms p \<Longrightarrow> q \<in> subterms p"
  "\<And>l fmsg p q. {l}send(fmsg). q \<in> subterms p \<Longrightarrow> q \<in> subterms p"
  "\<And>l fdata p q. {l}deliver(fdata). q \<in> subterms p \<Longrightarrow> q \<in> subterms p"
  "\<And>l fmsg p q. {l}receive(fmsg). q \<in> subterms p \<Longrightarrow> q \<in> subterms p"
  by auto

subsection "Actions"

text \<open>
  There are two sorts of \<open>\<tau>\<close> actions in AWN: one at the level of individual processes
  (within nodes), and one at the network level (outside nodes). We define a class so that
  we can ignore this distinction whenever it is not critical.
\<close>

class tau =
  fixes tau :: "'a" ("\<tau>")

subsubsection "Sequential Actions (and related predicates)"

datatype 'm seq_action =
    broadcast 'm
  | groupcast "ip set" 'm
  | unicast ip 'm
  | notunicast ip           ("\<not>unicast _" [1000] 60)
  | send 'm
  | deliver data
  | receive 'm
  | seq_tau                 ("\<tau>\<^sub>s")

instantiation "seq_action" :: (type) tau
begin
definition step_seq_tau [simp]: "\<tau> \<equiv> \<tau>\<^sub>s"
instance ..
end

definition recvmsg :: "('m \<Rightarrow> bool) \<Rightarrow> 'm seq_action \<Rightarrow> bool"
where "recvmsg P a \<equiv> case a of receive m \<Rightarrow> P m
                             | _ \<Rightarrow> True"

lemma recvmsg_simps[simp]:
  "\<And>m.     recvmsg P (broadcast m)     = True"
  "\<And>ips m. recvmsg P (groupcast ips m) = True"
  "\<And>ip m.  recvmsg P (unicast ip m)    = True"
  "\<And>ip.    recvmsg P (notunicast ip)   = True"
  "\<And>m.     recvmsg P (send m)          = True"
  "\<And>d.     recvmsg P (deliver d)       = True"
  "\<And>m.     recvmsg P (receive m)       = P m"
  "        recvmsg P \<tau>\<^sub>s                 = True"
  unfolding recvmsg_def by simp_all

lemma recvmsgTT [simp]: "recvmsg TT a"
  by (cases a) simp_all

lemma recvmsgE [elim]:
  assumes "recvmsg (R \<sigma>) a"
      and "\<And>m. R \<sigma> m \<Longrightarrow> R \<sigma>' m"
    shows "recvmsg (R \<sigma>') a"
  using assms(1) by (cases a) (auto elim!: assms(2))

definition anycast :: "('m \<Rightarrow> bool) \<Rightarrow> 'm seq_action \<Rightarrow> bool"
where "anycast P a \<equiv> case a of broadcast m \<Rightarrow> P m
                             | groupcast _ m \<Rightarrow> P m
                             | unicast _ m \<Rightarrow> P m
                             | _ \<Rightarrow> True"

lemma anycast_simps [simp]:
  "\<And>m.     anycast P (broadcast m)     = P m"
  "\<And>ips m. anycast P (groupcast ips m) = P m"
  "\<And>ip m.  anycast P (unicast ip m)    = P m"
  "\<And>ip.    anycast P (notunicast ip)   = True"
  "\<And>m.     anycast P (send m)          = True"
  "\<And>d.     anycast P (deliver d)       = True"
  "\<And>m.     anycast P (receive m)       = True"
  "        anycast P \<tau>\<^sub>s                 = True"
  unfolding anycast_def by simp_all

definition orecvmsg :: "((ip \<Rightarrow> 's) \<Rightarrow> 'm \<Rightarrow> bool) \<Rightarrow> (ip \<Rightarrow> 's) \<Rightarrow> 'm seq_action \<Rightarrow> bool"
where "orecvmsg P \<sigma> a \<equiv> (case a of receive m \<Rightarrow> P \<sigma> m
                                         | _ \<Rightarrow> True)"

lemma orecvmsg_simps [simp]:
  "\<And>m.     orecvmsg P \<sigma> (broadcast m)     = True"
  "\<And>ips m. orecvmsg P \<sigma> (groupcast ips m) = True"
  "\<And>ip m.  orecvmsg P \<sigma> (unicast ip m)    = True"
  "\<And>ip.    orecvmsg P \<sigma> (notunicast ip)   = True"
  "\<And>m.     orecvmsg P \<sigma> (send m)          = True"
  "\<And>d.     orecvmsg P \<sigma> (deliver d)       = True"
  "\<And>m.     orecvmsg P \<sigma> (receive m)       = P \<sigma> m"
  "         orecvmsg P \<sigma> \<tau>\<^sub>s                = True"
  unfolding orecvmsg_def by simp_all

lemma orecvmsgEI [elim]:
  "\<lbrakk> orecvmsg P \<sigma> a; \<And>\<sigma> a. P \<sigma> a \<Longrightarrow> Q \<sigma> a \<rbrakk> \<Longrightarrow> orecvmsg Q \<sigma> a"
  by (cases a) simp_all

lemma orecvmsg_stateless_recvmsg [elim]:
  "orecvmsg (\<lambda>_. P) \<sigma> a \<Longrightarrow> recvmsg P a"
  by (cases a) simp_all

lemma orecvmsg_recv_weaken [elim]:
  "\<lbrakk> orecvmsg P \<sigma> a; \<And>\<sigma> a. P \<sigma> a \<Longrightarrow> Q a \<rbrakk> \<Longrightarrow> recvmsg Q a"
  by (cases a) simp_all

lemma orecvmsg_recvmsg [elim]:
  "orecvmsg P \<sigma> a \<Longrightarrow> recvmsg (P \<sigma>) a"
  by (cases a) simp_all

definition sendmsg :: "('m \<Rightarrow> bool) \<Rightarrow> 'm seq_action \<Rightarrow> bool"
where "sendmsg P a \<equiv> case a of send m \<Rightarrow> P m | _ \<Rightarrow> True"

lemma sendmsg_simps [simp]:
  "\<And>m.     sendmsg P (broadcast m)     = True"
  "\<And>ips m. sendmsg P (groupcast ips m) = True"
  "\<And>ip m.  sendmsg P (unicast ip m)    = True"
  "\<And>ip.    sendmsg P (notunicast ip)   = True"
  "\<And>m.     sendmsg P (send m)          = P m"
  "\<And>d.     sendmsg P (deliver d)       = True"
  "\<And>m.     sendmsg P (receive m)       = True"
  "        sendmsg P \<tau>\<^sub>s                 = True"
  unfolding sendmsg_def by simp_all

type_synonym ('s, 'm, 'p, 'l) seqp_env = "'p \<Rightarrow> ('s, 'm, 'p, 'l) seqp"

subsubsection "Node Actions (and related predicates)"

datatype 'm node_action =
    node_cast "ip set" 'm             ("_:*cast'(_')"       [200, 200] 200)                                                 
  | node_deliver ip data              ("_:deliver'(_')"     [200, 200] 200)
  | node_arrive "ip set" "ip set" 'm  ("_\<not>_:arrive'(_')"    [200, 200, 200] 200)
  | node_connect ip ip                ("connect'(_, _')"    [200, 200] 200)
  | node_disconnect ip ip             ("disconnect'(_, _')" [200, 200] 200)
  | node_newpkt ip data ip            ("_:newpkt'(_, _')"   [200, 200, 200] 200)
  | node_tau                          ("\<tau>\<^sub>n")

instantiation "node_action" :: (type) tau
begin
definition step_node_tau [simp]: "\<tau> \<equiv> \<tau>\<^sub>n"
instance ..
end

definition arrivemsg :: "ip \<Rightarrow> ('m \<Rightarrow> bool) \<Rightarrow> 'm node_action \<Rightarrow> bool"
where "arrivemsg i P a \<equiv> case a of node_arrive ii ni m \<Rightarrow> ((ii = {i} \<longrightarrow> P m))
                                  | _ \<Rightarrow> True"

lemma arrivemsg_simps[simp]:
  "\<And>R m.       arrivemsg i P (R:*cast(m))         = True"
  "\<And>d m.       arrivemsg i P (d:deliver(m))       = True"
  "\<And>i ii ni m. arrivemsg i P (ii\<not>ni:arrive(m))    = (ii = {i} \<longrightarrow> P m)"
  "\<And>i1 i2.     arrivemsg i P (connect(i1, i2))    = True"
  "\<And>i1 i2.     arrivemsg i P (disconnect(i1, i2)) = True"
  "\<And>i i' d di. arrivemsg i P (i':newpkt(d, di))   = True"
  "             arrivemsg i P \<tau>\<^sub>n                   = True"
  unfolding arrivemsg_def by simp_all

lemma arrivemsgTT [simp]: "arrivemsg i TT = TT"
  by (rule ext) (clarsimp simp: arrivemsg_def split: node_action.split)

definition oarrivemsg :: "((ip \<Rightarrow> 's) \<Rightarrow> 'm \<Rightarrow> bool) \<Rightarrow> (ip \<Rightarrow> 's) \<Rightarrow> 'm node_action \<Rightarrow> bool"
where "oarrivemsg P \<sigma> a \<equiv> case a of node_arrive ii ni m \<Rightarrow> P \<sigma> m | _ \<Rightarrow> True"

lemma oarrivemsg_simps[simp]:
  "\<And>R m.       oarrivemsg P \<sigma> (R:*cast(m))         = True"
  "\<And>d m.       oarrivemsg P \<sigma> (d:deliver(m))       = True"
  "\<And>i ii ni m. oarrivemsg P \<sigma> (ii\<not>ni:arrive(m))    = P \<sigma> m"
  "\<And>i1 i2.     oarrivemsg P \<sigma> (connect(i1, i2))    = True"
  "\<And>i1 i2.     oarrivemsg P \<sigma> (disconnect(i1, i2)) = True"
  "\<And>i i' d di. oarrivemsg P \<sigma> (i':newpkt(d, di))   = True"
  "             oarrivemsg P \<sigma> \<tau>\<^sub>n                   = True"
  unfolding oarrivemsg_def by simp_all

lemma oarrivemsg_True [simp, intro]: "oarrivemsg (\<lambda>_ _. True) \<sigma> a"
  by (cases a) auto

definition castmsg :: "('m \<Rightarrow> bool) \<Rightarrow> 'm node_action \<Rightarrow> bool"
where "castmsg P a \<equiv> case a of _:*cast(m) \<Rightarrow> P m
                              | _ \<Rightarrow> True"

lemma castmsg_simps[simp]:
  "\<And>R m.       castmsg P (R:*cast(m))         = P m"
  "\<And>d m.       castmsg P (d:deliver(m))       = True"
  "\<And>i ii ni m. castmsg P (ii\<not>ni:arrive(m))    = True"
  "\<And>i1 i2.     castmsg P (connect(i1, i2))    = True"
  "\<And>i1 i2.     castmsg P (disconnect(i1, i2)) = True"
  "\<And>i i' d di. castmsg P (i':newpkt(d, di))   = True"
  "             castmsg P \<tau>\<^sub>n                   = True"
  unfolding castmsg_def by simp_all

subsection "Networks"

datatype net_tree =
    Node ip "ip set"          ("\<langle>_; _\<rangle>")
  | Subnet net_tree net_tree  (infixl "\<parallel>" 90)

declare net_tree.induct [[induct del]]
lemmas net_tree_induct [induct type: net_tree] = net_tree.induct [rename_abs i R p1 p2]

datatype 's net_state =
    NodeS ip 's "ip set"
  | SubnetS "'s net_state" "'s net_state"

fun net_ips :: "'s net_state \<Rightarrow> ip set"
where
    "net_ips (NodeS i s R) = {i}"
  | "net_ips (SubnetS n1 n2) = net_ips n1 \<union> net_ips n2"

fun net_tree_ips :: "net_tree \<Rightarrow> ip set"
where
    "net_tree_ips (p1 \<parallel> p2) = net_tree_ips p1 \<union> net_tree_ips p2"
  | "net_tree_ips (\<langle>i; R\<rangle>) = {i}"

lemma net_tree_ips_commute:
  "net_tree_ips (p1 \<parallel> p2) = net_tree_ips (p2 \<parallel> p1)"
  by simp (rule Un_commute)

fun wf_net_tree :: "net_tree \<Rightarrow> bool"
where
   "wf_net_tree (p1 \<parallel> p2) = (net_tree_ips p1 \<inter> net_tree_ips p2 = {}
                             \<and> wf_net_tree p1 \<and> wf_net_tree p2)"
 | "wf_net_tree (\<langle>i; R\<rangle>) = True"

lemma wf_net_tree_children [elim]:
  assumes "wf_net_tree (p1 \<parallel> p2)"
  obtains "wf_net_tree p1"
      and "wf_net_tree p2"
  using assms by simp

fun netmap :: "'s net_state \<Rightarrow> ip \<Rightarrow> 's option"
where
    "netmap (NodeS i p R\<^sub>i) = [i \<mapsto> p]"
  | "netmap (SubnetS s t) = netmap s ++ netmap t"

lemma not_in_netmap [simp]:
  assumes "i \<notin> net_ips ns"
    shows "netmap ns i = None"
  using assms by (induction ns) simp_all

lemma netmap_none_not_in_net_ips:
  assumes "netmap ns i = None"
    shows "i\<notin>net_ips ns"
  using assms by (induction ns) auto

lemma net_ips_is_dom_netmap: "net_ips s = dom(netmap s)"
  proof (induction s)
    fix i R\<^sub>i and p :: 's
    show "net_ips (NodeS i p R\<^sub>i) = dom (netmap (NodeS i p R\<^sub>i))"
      by auto
  next
    fix s1 s2 :: "'s net_state"
    assume "net_ips s1 = dom (netmap s1)"
       and "net_ips s2 = dom (netmap s2)"
    thus "net_ips (SubnetS s1 s2) = dom (netmap (SubnetS s1 s2))"
      by auto
  qed

lemma in_netmap [simp]:
  assumes "i \<in> net_ips ns"
    shows "netmap ns i \<noteq> None"
  using assms by (auto simp add: net_ips_is_dom_netmap)

lemma netmap_subnets_same:
  assumes "netmap s1 i = x"
      and "netmap s2 i = x"
    shows "netmap (SubnetS s1 s2) i = x"
  using assms by simp (metis map_add_dom_app_simps(1) map_add_dom_app_simps(3))

lemma netmap_subnets_samef:
  assumes "netmap s1 = f"
      and "netmap s2 = f"
    shows "netmap (SubnetS s1 s2) = f"
  using assms by simp (metis map_add_le_mapI map_le_antisym map_le_map_add map_le_refl)

lemma netmap_add_disjoint [elim]:
  assumes "\<forall>i\<in>net_ips s1 \<union> net_ips s2. the ((netmap s1 ++ netmap s2) i) = \<sigma> i"
      and "net_ips s1 \<inter> net_ips s2 = {}"
    shows "\<forall>i\<in>net_ips s1. the (netmap s1 i) = \<sigma> i"
  proof
    fix i
    assume "i \<in> net_ips s1"
    hence "i \<in> dom(netmap s1)" by (simp add: net_ips_is_dom_netmap)
    moreover with assms(2) have "i \<notin> dom(netmap s2)" by (auto simp add: net_ips_is_dom_netmap)
    ultimately have "the (netmap s1 i) = the ((netmap s1 ++ netmap s2) i)"
      by (simp add: map_add_dom_app_simps)
    with assms(1) and \<open>i\<in>net_ips s1\<close> show "the (netmap s1 i) = \<sigma> i" by simp
  qed

lemma netmap_add_disjoint2 [elim]:
  assumes "\<forall>i\<in>net_ips s1 \<union> net_ips s2. the ((netmap s1 ++ netmap s2) i) = \<sigma> i"
    shows "\<forall>i\<in>net_ips s2. the (netmap s2 i) = \<sigma> i"
  using assms by (simp add: net_ips_is_dom_netmap)
                 (metis Un_iff map_add_dom_app_simps(1))

lemma net_ips_netmap_subnet [elim]:
  assumes "net_ips s1 \<inter> net_ips s2 = {}"
      and "\<forall>i\<in>net_ips (SubnetS s1 s2). the (netmap (SubnetS s1 s2) i) = \<sigma> i"
    shows "\<forall>i\<in>net_ips s1. the (netmap s1 i) = \<sigma> i"
      and "\<forall>i\<in>net_ips s2. the (netmap s2 i) = \<sigma> i"
  proof -
    from assms(2) have "\<forall>i\<in>net_ips s1 \<union> net_ips s2. the ((netmap s1 ++ netmap s2) i) = \<sigma> i" by auto
    with assms(1) show "\<forall>i\<in>net_ips s1. the (netmap s1 i) = \<sigma> i"
      by - (erule(1) netmap_add_disjoint)
  next
    from assms(2) have "\<forall>i\<in>net_ips s1 \<union> net_ips s2. the ((netmap s1 ++ netmap s2) i) = \<sigma> i" by auto
    thus "\<forall>i\<in>net_ips s2. the (netmap s2 i) = \<sigma> i"
      by - (erule netmap_add_disjoint2)
  qed

fun inoclosed :: "'s \<Rightarrow> 'm::msg node_action \<Rightarrow> bool"
where
    "inoclosed _ (node_arrive ii ni m) = eq_newpkt m"
  | "inoclosed _ (node_newpkt i d di)  = False"
  | "inoclosed _ _ = True"

lemma inclosed_simps [simp]:
  "\<And>\<sigma> ii ni. inoclosed \<sigma> (ii\<not>ni:arrive(m))   = eq_newpkt m"
  "\<And>\<sigma> d di.  inoclosed \<sigma> (i:newpkt(d, di))   = False"
  "\<And>\<sigma> R m.   inoclosed \<sigma> (R:*cast(m))        = True"
  "\<And>\<sigma> i d.   inoclosed \<sigma> (i:deliver(d))      = True"
  "\<And>\<sigma> i i'.  inoclosed \<sigma> (connect(i, i'))    = True"
  "\<And>\<sigma> i i'.  inoclosed \<sigma> (disconnect(i, i')) = True"
  "\<And>\<sigma>.       inoclosed \<sigma> (\<tau>)                 = True"
  by auto

definition
  netmask :: "ip set \<Rightarrow> ((ip \<Rightarrow> 's) \<times> 'l) \<Rightarrow> ((ip \<Rightarrow> 's option) \<times> 'l)"
where
  "netmask I s \<equiv> (\<lambda>i. if i\<in>I then Some (fst s i) else None, snd s)"

lemma netmask_def' [simp]:
  "netmask I (\<sigma>, \<zeta>) = (\<lambda>i. if i\<in>I then Some (\<sigma> i) else None, \<zeta>)"
  unfolding netmask_def by auto

fun netgmap :: "('s \<Rightarrow> 'g \<times> 'l) \<Rightarrow> 's net_state \<Rightarrow> (nat \<Rightarrow> 'g option) \<times> 'l net_state"
  where
    "netgmap sr (NodeS i s R) = ([i \<mapsto> fst (sr s)], NodeS i (snd (sr s)) R)"
  | "netgmap sr (SubnetS s\<^sub>1 s\<^sub>2) = (let (\<sigma>\<^sub>1, ss) = netgmap sr s\<^sub>1 in
                                   let (\<sigma>\<^sub>2, tt) = netgmap sr s\<^sub>2 in
                                   (\<sigma>\<^sub>1 ++ \<sigma>\<^sub>2, SubnetS ss tt))"

lemma dom_fst_netgmap [simp, intro]: "dom (fst (netgmap sr n)) = net_ips n"
  proof (induction n)
    fix i s R
    show "dom (fst (netgmap sr (NodeS i s R))) = net_ips (NodeS i s R)"
      by simp
  next
    fix n1 n2
    assume a1: "dom (fst (netgmap sr n1)) = net_ips n1"
       and a2: "dom (fst (netgmap sr n2)) = net_ips n2"
    obtain \<sigma>\<^sub>1 \<zeta>\<^sub>1 \<sigma>\<^sub>2 \<zeta>\<^sub>2 where nm1: "netgmap sr n1 = (\<sigma>\<^sub>1, \<zeta>\<^sub>1)"
                        and nm2: "netgmap sr n2 = (\<sigma>\<^sub>2, \<zeta>\<^sub>2)"
      by (metis surj_pair)
    hence "netgmap sr (SubnetS n1 n2) = (\<sigma>\<^sub>1 ++ \<sigma>\<^sub>2, SubnetS \<zeta>\<^sub>1 \<zeta>\<^sub>2)" by simp
    hence "dom (fst (netgmap sr (SubnetS n1 n2))) = dom (\<sigma>\<^sub>1 ++ \<sigma>\<^sub>2)" by simp
    also from a1 a2 nm1 nm2 have "dom (\<sigma>\<^sub>1 ++ \<sigma>\<^sub>2) = net_ips (SubnetS n1 n2)" by auto
    finally show "dom (fst (netgmap sr (SubnetS n1 n2))) = net_ips (SubnetS n1 n2)" .
  qed

lemma netgmap_pair_dom [elim]:
  obtains \<sigma> \<zeta> where "netgmap sr n = (\<sigma>, \<zeta>)"
                and "dom \<sigma> = net_ips n"
    by (metis dom_fst_netgmap surjective_pairing)

lemma net_ips_netgmap [simp]:
  "net_ips (snd (netgmap sr s)) = net_ips s"
  proof (induction s)
    fix s1 s2
    assume "net_ips (snd (netgmap sr s1)) = net_ips s1"
       and "net_ips (snd (netgmap sr s2)) = net_ips s2"
    thus "net_ips (snd (netgmap sr (SubnetS s1 s2))) = net_ips (SubnetS s1 s2)"
      by (cases "netgmap sr s1", cases "netgmap sr s2") auto
  qed simp

lemma some_the_fst_netgmap:
  assumes "i \<in> net_ips s"
    shows "Some (the (fst (netgmap sr s) i)) = fst (netgmap sr s) i"
  using assms by (metis domIff dom_fst_netgmap option.collapse)


lemma fst_netgmap_none [simp]:
  assumes "i \<notin> net_ips s"
    shows "fst (netgmap sr s) i = None"
  using assms by (metis domIff dom_fst_netgmap)

lemma fst_netgmap_subnet [simp]:
  "fst (case netgmap sr s1 of (\<sigma>\<^sub>1, ss) \<Rightarrow>
        case netgmap sr s2 of (\<sigma>\<^sub>2, tt) \<Rightarrow>
        (\<sigma>\<^sub>1 ++ \<sigma>\<^sub>2, SubnetS ss tt)) = (fst (netgmap sr s1) ++ fst (netgmap sr s2))"
  by (metis (mono_tags) fst_conv netgmap_pair_dom split_conv)

lemma snd_netgmap_subnet [simp]:
  "snd (case netgmap sr s1 of (\<sigma>\<^sub>1, ss) \<Rightarrow>
        case netgmap sr s2 of (\<sigma>\<^sub>2, tt) \<Rightarrow>
        (\<sigma>\<^sub>1 ++ \<sigma>\<^sub>2, SubnetS ss tt)) = (SubnetS (snd (netgmap sr s1)) (snd (netgmap sr s2)))"
  by (metis (lifting, no_types) Pair_inject split_beta' surjective_pairing)

lemma fst_netgmap_not_none [simp]:
  assumes "i \<in> net_ips s"
    shows "fst (netgmap sr s) i \<noteq> None"
  using assms by (induction s) auto

lemma netgmap_netgmap_not_rhs [simp]:
  assumes "i \<notin> net_ips s2"
    shows "(fst (netgmap sr s1) ++ fst (netgmap sr s2)) i = (fst (netgmap sr s1)) i"
  proof -
    from assms(1) have "i \<notin> dom (fst (netgmap sr s2))" by simp
    thus ?thesis by (simp add: map_add_dom_app_simps)
  qed

lemma netgmap_netgmap_rhs [simp]:
  assumes "i \<in> net_ips s2"
    shows "(fst (netgmap sr s1) ++ fst (netgmap sr s2)) i = (fst (netgmap sr s2)) i"
  using assms by (simp add: map_add_dom_app_simps)

lemma netgmap_netmask_subnets [elim]:
  assumes "netgmap sr s1 = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1))"
      and "netgmap sr s2 = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2))"
    shows "fst (netgmap sr (SubnetS s1 s2))
            = fst (netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, snd (netgmap sr (SubnetS s1 s2))))"
  proof (rule ext)
    fix i
    have "i \<in> net_tree_ips n1 \<or> i \<in> net_tree_ips n2 \<or> (i\<notin>net_tree_ips n1 \<union> net_tree_ips n2)"
      by auto
    thus "fst (netgmap sr (SubnetS s1 s2)) i
            = fst (netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, snd (netgmap sr (SubnetS s1 s2)))) i"
    proof (elim disjE)
      assume "i \<in> net_tree_ips n1"
      with \<open>netgmap sr s1 = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1))\<close>
           \<open>netgmap sr s2 = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2))\<close>
        show ?thesis
          by (cases "netgmap sr s1", cases "netgmap sr s2", clarsimp)
             (metis (lifting, mono_tags) map_add_Some_iff)
    next
      assume "i \<in> net_tree_ips n2"
      with \<open>netgmap sr s2 = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2))\<close>
        show ?thesis
          by simp (metis (lifting, mono_tags) fst_conv map_add_find_right)
    next
      assume "i\<notin>net_tree_ips n1 \<union> net_tree_ips n2"
      with \<open>netgmap sr s1 = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1))\<close>
           \<open>netgmap sr s2 = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2))\<close>
        show ?thesis
          by simp (metis (lifting, mono_tags) fst_conv)
    qed
  qed

lemma netgmap_netmask_subnets' [elim]:
  assumes "netgmap sr s1 = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1))"
      and "netgmap sr s2 = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2))"
      and "s = SubnetS s1 s2"
    shows "netgmap sr s = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, snd (netgmap sr s))"
  by (simp only: assms(3))
     (rule prod_eqI [OF netgmap_netmask_subnets [OF assms(1-2)]], simp)

lemma netgmap_subnet_split1:
  assumes "netgmap sr (SubnetS s1 s2) = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, \<zeta>)"
      and "net_tree_ips n1 \<inter> net_tree_ips n2 = {}"
      and "net_ips s1 = net_tree_ips n1"
      and "net_ips s2 = net_tree_ips n2"
    shows "netgmap sr s1 = netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1))"
  proof (rule prod_eqI)
    show "fst (netgmap sr s1) = fst (netmask (net_tree_ips n1) (\<sigma>, snd (netgmap sr s1)))"
    proof (rule ext, simp, intro conjI impI)
      fix i
      assume "i\<in>net_tree_ips n1"
      with \<open>net_tree_ips n1 \<inter> net_tree_ips n2 = {}\<close> have "i\<notin>net_tree_ips n2"
        by auto
      from assms(1) [simplified prod_eq_iff]
        have "(fst (netgmap sr s1) ++ fst (netgmap sr s2)) i =
                 (if i \<in> net_tree_ips n1 \<or> i \<in> net_tree_ips n2 then Some (\<sigma> i) else None)"
          by simp
      also from \<open>i\<notin>net_tree_ips n2\<close> and \<open>net_ips s2 = net_tree_ips n2\<close>
        have "(fst (netgmap sr s1) ++ fst (netgmap sr s2)) i = fst (netgmap sr s1) i"
          by (metis dom_fst_netgmap map_add_dom_app_simps(3))
      finally show "fst (netgmap sr s1) i = Some (\<sigma> i)"
        using \<open>i\<in>net_tree_ips n1\<close> by simp
    next
      fix i
      assume "i \<notin> net_tree_ips n1"
      with \<open>net_ips s1 = net_tree_ips n1\<close> have "i \<notin> net_ips s1" by simp
      thus "fst (netgmap sr s1) i = None" by simp
    qed
  qed simp

lemma netgmap_subnet_split2:
  assumes "netgmap sr (SubnetS s1 s2) = netmask (net_tree_ips (n1 \<parallel> n2)) (\<sigma>, \<zeta>)"
      and "net_ips s1 = net_tree_ips n1"
      and "net_ips s2 = net_tree_ips n2"
    shows "netgmap sr s2 = netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2))"
  proof (rule prod_eqI)
    show "fst (netgmap sr s2) = fst (netmask (net_tree_ips n2) (\<sigma>, snd (netgmap sr s2)))"
    proof (rule ext, simp, intro conjI impI)
      fix i
      assume "i\<in>net_tree_ips n2"
      from assms(1) [simplified prod_eq_iff]
        have "(fst (netgmap sr s1) ++ fst (netgmap sr s2)) i =
                 (if i \<in> net_tree_ips n1 \<or> i \<in> net_tree_ips n2 then Some (\<sigma> i) else None)"
          by simp
      also from \<open>i\<in>net_tree_ips n2\<close> and \<open>net_ips s2 = net_tree_ips n2\<close>
        have "(fst (netgmap sr s1) ++ fst (netgmap sr s2)) i = fst (netgmap sr s2) i"
          by (metis dom_fst_netgmap map_add_dom_app_simps(1))
      finally show "fst (netgmap sr s2) i = Some (\<sigma> i)"
        using \<open>i\<in>net_tree_ips n2\<close> by simp
    next
      fix i
      assume "i \<notin> net_tree_ips n2"
      with \<open>net_ips s2 = net_tree_ips n2\<close> have "i \<notin> net_ips s2" by simp
      thus "fst (netgmap sr s2) i = None" by simp
    qed
  qed simp

lemma netmap_fst_netgmap_rel:
  shows "(\<lambda>i. map_option (fst o sr) (netmap s i)) = fst (netgmap sr s)"
  proof (induction s)
    fix ii s R
    show "(\<lambda>i. map_option (fst \<circ> sr) (netmap (NodeS ii s R) i)) = fst (netgmap sr (NodeS ii s R))"
      by auto
  next
    fix s1 s2
    assume a1: "(\<lambda>i. map_option (fst \<circ> sr) (netmap s1 i)) = fst (netgmap sr s1)"
       and a2: "(\<lambda>i. map_option (fst \<circ> sr) (netmap s2 i)) = fst (netgmap sr s2)"
    show "(\<lambda>i. map_option (fst \<circ> sr) (netmap (SubnetS s1 s2) i)) = fst (netgmap sr (SubnetS s1 s2))"
    proof (rule ext)
      fix i
      from a1 a2 have "map_option (fst \<circ> sr) ((netmap s1 ++ netmap s2) i)
                                    = (fst (netgmap sr s1) ++ fst (netgmap sr s2)) i"
        by (metis fst_conv map_add_dom_app_simps(1) map_add_dom_app_simps(3)
                  net_ips_is_dom_netmap netgmap_pair_dom)
      thus "map_option (fst \<circ> sr) (netmap (SubnetS s1 s2) i) = fst (netgmap sr (SubnetS s1 s2)) i"
        by simp
    qed
  qed

lemma netmap_is_fst_netgmap:
  assumes "netmap s' = netmap s"
    shows "fst (netgmap sr s') = fst (netgmap sr s)"
  using assms by (metis netmap_fst_netgmap_rel)

lemma netmap_is_fst_netgmap':
  assumes "netmap s' i = netmap s i"
    shows "fst (netgmap sr s') i = fst (netgmap sr s) i"
  using assms by (metis netmap_fst_netgmap_rel)

lemma fst_netgmap_pair_fst [simp]:
  "fst (netgmap (\<lambda>(p, q). (fst p, snd p, q)) s) = fst (netgmap fst s)"
  by (induction s) auto

text \<open>Introduce streamlined alternatives to netgmap to simplify certain property
        statements and thus make them easier to understand and to present.\<close>

fun netlift :: "('s \<Rightarrow> 'g \<times> 'l) \<Rightarrow> 's net_state \<Rightarrow> (nat \<Rightarrow> 'g option)"
  where
    "netlift sr (NodeS i s R) = [i \<mapsto> fst (sr s)]"
  | "netlift sr (SubnetS s t) = (netlift sr s) ++ (netlift sr t)"

lemma fst_netgmap_netlift:
  "fst (netgmap sr s) = netlift sr s"
  by (induction s) simp_all

fun netliftl :: "('s \<Rightarrow> 'g \<times> 'l) \<Rightarrow> 's net_state \<Rightarrow> 'l net_state"
  where
    "netliftl sr (NodeS i s R) = NodeS i (snd (sr s)) R"
  | "netliftl sr (SubnetS s t) = SubnetS (netliftl sr s) (netliftl sr t)"

lemma snd_netgmap_netliftl:
  "snd (netgmap sr s) = netliftl sr s"
  by (induction s) simp_all
 
lemma netgmap_netlift_netliftl: "netgmap sr s = (netlift sr s, netliftl sr s)"
  by rule (simp_all add: fst_netgmap_netlift snd_netgmap_netliftl)

end
