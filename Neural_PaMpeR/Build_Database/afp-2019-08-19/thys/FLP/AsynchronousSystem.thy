section \<open>AsynchronousSystem\<close>

text \<open>
  \file{AsynchronousSystem} defines a message datatype and a transition system locale to
  model asynchronous distributed computation. It establishes a diamond property for a
  special reachability relation within such transition systems.
\<close>

theory AsynchronousSystem
imports Multiset
begin

text\<open>
  The formalization is type-parameterized over
  \begin{description}
    \item[\var{'p} process identifiers.] Corresponds to the set $P$ in Völzer.
      Finiteness is not yet demanded, but will be in \file{FLPSystem}.
    \item[\var{'s} process states.] Corresponds to $S$, countability is not
      imposed.
    \item[\var{'v} message payloads.] Corresponds to the interprocess
      communication part of $M$ from Völzer. The whole of $M$ is captured by
      \isb{messageValue}.
  \end{description}
\<close>

subsection\<open>Messages\<close>

text \<open>
  A \isb{message} is either an initial input message telling a process
  which value it should introduce to the consensus negotiation, a message
  to the environment communicating the consensus outcome, or a message
  passed from one process to some other.
\<close>

datatype ('p, 'v) message =
  InMsg 'p bool  ("<_, inM _>")
| OutMsg bool    ("<\<bottom>, outM _>")
| Msg 'p 'v      ("<_, _>")

text \<open>
  A message value is the content of a message, which a process may receive. 
\<close>

datatype 'v messageValue = 
  Bool bool
| Value 'v

primrec unpackMessage :: "('p, 'v) message \<Rightarrow> 'v messageValue"
where
  "unpackMessage <p, inM b>  = Bool b"
| "unpackMessage <p, v>      = Value v"
| "unpackMessage <\<bottom>, outM v> = Bool False"

primrec isReceiverOf :: 
  "'p \<Rightarrow> ('p, 'v) message \<Rightarrow> bool"
where 
   "isReceiverOf p1 (<p2, inM v>) = (p1 = p2)"
 | "isReceiverOf p1 (<p2, v>) =     (p1 = p2)"
 | "isReceiverOf p1 (<\<bottom>,outM v>) =  False"

lemma UniqueReceiverOf:
fixes 
  msg  :: "('p, 'v) message" and
  p q :: 'p
assumes
  "isReceiverOf q msg"
  "p \<noteq> q"
shows 
  "\<not> isReceiverOf p msg"
using assms by (cases msg, auto)

subsection\<open>Configurations\<close>

text \<open>
  Here we formalize a configuration as detailed in section 2 of Völzer's paper.

  Note that Völzer imposes the finiteness of the message multiset by
  definition while we do not do so. In \isb{FiniteMessages}
  We prove the finiteness to follow from the assumption that only
  finitely many messages can be sent at once.
\<close>

record ('p, 'v, 's) configuration =
  states :: "'p \<Rightarrow> 's"
  msgs :: "(('p, 'v) message) multiset"

text \<open>
  C.f. Völzer: \textquote{A step is identified with a message $(p, m)$. A step $(p, m)$ is enabled
  in a configuration c if $\var{msgs}_c$ contains the message $(p, m)$.}
\<close>

definition enabled ::
  "('p, 'v, 's) configuration \<Rightarrow> ('p, 'v) message \<Rightarrow> bool"
where 
  "enabled cfg msg \<equiv> (msg \<in># msgs cfg)"

subsection \<open>The system locale\<close>

text \<open>
  The locale describing a system is derived by slight refactoring from the
  following passage of Völzer:
  \begin{displayquote}
    A process $p$ consists of an initial state $s_p \in S$ and a step transition
    function, which assigns to each pair $(m, s)$ of a message value $m$ and
    a process state $s$ a follower state and a finite set of messages (the
    messages to be sent by $p$ in a step).
  \end{displayquote}
\<close>

locale asynchronousSystem =
fixes 
  trans :: "'p \<Rightarrow> 's \<Rightarrow> 'v messageValue \<Rightarrow> 's" and
  sends :: "'p \<Rightarrow> 's \<Rightarrow> 'v messageValue \<Rightarrow> ('p, 'v) message multiset" and
  start :: "'p \<Rightarrow> 's"
begin

abbreviation Proc :: "'p set"
where "Proc \<equiv> (UNIV :: 'p set)"

subsection \<open>The step relation\<close>

text \<open>
  The step relation is defined analogously to Völzer:
  \begin{displayquote}
    {[}If enabled, a step may{]} occur, resulting in a follower
    configuration $c^\prime$, where $c^\prime$ is obtained from $c$ by removing
    $(p, m)$ from $\var{msgs}_c$, changing $p$'s state and adding the set of
    messages to $\var{msgs}_c$ according to the step transition function
    associated with $p$. We denote this by $c \xrightarrow{p,m} c^\prime$.
  \end{displayquote}
  There are no steps consuming output messages.
\<close>

primrec steps :: 
  "('p, 'v, 's) configuration
   \<Rightarrow> ('p, 'v) message
   \<Rightarrow> ('p, 'v, 's) configuration
   \<Rightarrow> bool"
   ("_ \<turnstile> _ \<mapsto> _" [70,70,70])
where 
  StepInMsg: "cfg1 \<turnstile> <p, inM v> \<mapsto> cfg2 = (
  (\<forall> s. ((s = p) \<longrightarrow> states cfg2 p = trans p (states cfg1 p) (Bool v))
      \<and> ((s \<noteq> p) \<longrightarrow> states cfg2 s = states cfg1 s))
   \<and> enabled cfg1 <p, inM v>
   \<and> msgs cfg2 = (sends p (states cfg1 p) (Bool v)
                  \<union># (msgs cfg1 -# <p, inM v>)))"
| StepMsg: "cfg1 \<turnstile> <p, v> \<mapsto> cfg2 = (
  (\<forall> s. ((s = p) \<longrightarrow> states cfg2 p = trans p (states cfg1 p) (Value v))
      \<and> ((s \<noteq> p) \<longrightarrow> states cfg2 s = states cfg1 s))
   \<and> enabled cfg1 <p, v>
   \<and> msgs cfg2 = (sends p (states cfg1 p) (Value v)
                  \<union># (msgs cfg1 -# <p, v>)))"
| StepOutMsg: "cfg1 \<turnstile> <\<bottom>,outM v> \<mapsto> cfg2 = 
    False"

text \<open>
  The system is distributed and asynchronous in the sense that the processing
  of messages only affects the process the message is directed to while the
  rest stays unchanged.
\<close>
lemma NoReceivingNoChange:
fixes
  cfg1 cfg2 :: "('p,'v,'s) configuration" and
  m :: "('p,'v) message" and
  p :: 'p
assumes
  Step: "cfg1 \<turnstile> m \<mapsto> cfg2" and
  Rec: "\<not> isReceiverOf p m"
shows
  "states cfg1 p = states cfg2 p "
proof(cases m)
  case (OutMsg b')
  thus ?thesis using Step by auto
next
  case (InMsg q b')
  assume CaseM:  "m = <q, inM b'>"
  with assms have "p \<noteq> q" by simp
  with Step CaseM show ?thesis by simp
next
  case (Msg q v')
  assume CaseM:  "m = <q, v'>"
  with assms have "p \<noteq> q" by simp
  with Step CaseM show ?thesis by simp
qed

lemma ExistsMsg:
fixes
  cfg1 cfg2 :: "('p,'v,'s) configuration" and
  m :: "('p,'v) message"
assumes
  Step: "cfg1 \<turnstile> m \<mapsto> cfg2"
shows
  "m \<in># (msgs cfg1)"
using assms enabled_def by (cases m, auto)

lemma NoMessageLossStep:
fixes
  cfg1 :: "('p,'v,'s) configuration" and
  cfg2 :: "('p,'v,'s) configuration" and
  p :: 'p and
  m :: "('p,'v) message" and
  m' :: "('p,'v) message"
assumes
  Step: "cfg1 \<turnstile> m \<mapsto> cfg2" and
  Rec1: "isReceiverOf p m" and
  Rec2: "\<not>isReceiverOf p m'"
shows 
  "msgs cfg1 m' \<le> msgs cfg2 m'"
using assms by (induct m, simp_all, auto)

lemma OutOnlyGrowing:
fixes 
  cfg1 cfg2 :: "('p,'v,'s) configuration" and
  b::bool and
  m::"('p, 'v) message" and
  p::'p
assumes
  "cfg1 \<turnstile> m \<mapsto> cfg2"
  "isReceiverOf p m"
shows 
  "msgs cfg2 <\<bottom>, outM b> 
  = (msgs cfg1 <\<bottom>, outM b>) + 
    sends p (states cfg1 p) (unpackMessage m) <\<bottom>, outM b>" 
proof(-)
  have "m = <\<bottom>, outM b> \<Longrightarrow> False" using assms proof(auto) qed
  hence MNotOut: "m \<noteq> <\<bottom>, outM b>" by auto
  have MsgFunction: "msgs cfg2 
                    = ((sends p (states cfg1 p) (unpackMessage m)) 
                      \<union># ((msgs cfg1) -# m))"
  proof(cases m) 
    case (InMsg pa bool)
    then have PaIsP: "pa = p" "(unpackMessage m) = Bool bool" 
      using isReceiverOf_def assms(2) by (auto simp add: UniqueReceiverOf)
    hence "cfg1 \<turnstile> <p, inM bool> \<mapsto> cfg2" using assms(1) InMsg by simp
    hence "msgs cfg2 = (sends p (states cfg1 p) (Bool bool) 
                       \<union># (msgs cfg1 -# <p, inM bool>))" 
      by simp
    hence "msgs cfg2 = (sends p (states cfg1 p) (Bool bool) 
                       \<union># (msgs cfg1 -# m))" 
      using PaIsP(1) InMsg by simp
    thus ?thesis using StepInMsg assms PaIsP by simp
  next case (OutMsg b)
    hence False using assms by auto
    thus ?thesis by simp
  next case (Msg pa va)
    hence PaIsP: "pa = p" "(unpackMessage m) = Value va" 
      using isReceiverOf_def assms(2) by (auto simp add: UniqueReceiverOf)
    hence "cfg1 \<turnstile> <p, va> \<mapsto> cfg2" using assms(1) Msg by simp
    hence "msgs cfg2 = (sends p (states cfg1 p) (Value va) 
                       \<union># (msgs cfg1 -# <p, va>))" by simp
    hence "msgs cfg2 = (sends p (states cfg1 p) (Value va) 
                       \<union># (msgs cfg1 -# m))" 
      using PaIsP(1) Msg by simp
    thus ?thesis using StepInMsg assms PaIsP by simp
  qed
  have "((sends p (states cfg1 p) (unpackMessage m)) 
         \<union># ((msgs cfg1) -# m)) <\<bottom>, outM b> 
       = ((sends p (states cfg1 p) (unpackMessage m)) 
         \<union># (msgs cfg1)) <\<bottom>, outM b>"
    using MNotOut by auto
  thus "msgs cfg2 <\<bottom>, outM b> 
       = (msgs cfg1 <\<bottom>, outM b>) + 
         sends p (states cfg1 p) (unpackMessage m) <\<bottom>, outM b>" 
    using MsgFunction by simp
qed

lemma OtherMessagesOnlyGrowing:
fixes
  cfg1 :: "('p,'v,'s) configuration" and
  cfg2 :: "('p,'v,'s) configuration" and
  p :: 'p and
  m :: "('p,'v) message" and
  m' :: "('p,'v) message"
assumes
  Step: "cfg1 \<turnstile> m \<mapsto> cfg2" and
  "m \<noteq> m'"
shows
  "msgs cfg1 m' \<le> msgs cfg2 m'"
using assms by (cases m, auto)

text \<open>
  Völzer: \textquote{Note that steps are enabled persistently, i.e., an
  enabled step remains enabled as long as it does not occur.}
\<close>
lemma OnlyOccurenceDisables:
fixes
  cfg1 :: "('p,'v,'s) configuration" and
  cfg2 :: "('p,'v,'s) configuration" and
  p :: 'p and
  m :: "('p,'v) message" and
  m' :: "('p,'v) message"
assumes
  Step: "cfg1 \<turnstile> m \<mapsto> cfg2" and
  En: "enabled cfg1 m'" and
  NotEn: "\<not> (enabled cfg2 m')"
shows
  "m = m'"
using assms proof (cases m) print_cases
  case (InMsg p bool)
  with Step have "msgs cfg2 = (sends p (states cfg1 p) (Bool bool) 
                              \<union># (msgs cfg1 -# <p, inM bool>))" by auto
  thus "m = m'" using InMsg En NotEn 
    by (auto simp add: enabled_def, metis less_nat_zero_code)
next
  case (OutMsg bool)
  with Step show "m = m'" by auto
next
  case (Msg p v)
  with Step have "msgs cfg2 = (sends p (states cfg1 p) (Value v) 
                              \<union># (msgs cfg1 -# <p, v>))" by auto
  thus "m = m'" using Msg En NotEn 
    by (auto simp add: enabled_def, metis less_nat_zero_code)
qed

subsection \<open>Reachability\<close>

inductive reachable :: 
  "  ('p, 'v, 's) configuration 
  \<Rightarrow> ('p, 'v, 's) configuration
  \<Rightarrow> bool"
where 
  init: "reachable cfg1 cfg1"
| step: "\<lbrakk> reachable cfg1 cfg2; (cfg2 \<turnstile> msg \<mapsto> cfg3) \<rbrakk> 
          \<Longrightarrow> reachable cfg1 cfg3"

lemma ReachableStepFirst: 
assumes
  "reachable cfg cfg'"
shows 
  "cfg = cfg' \<or> (\<exists> cfg1 msg p . (cfg \<turnstile> msg \<mapsto> cfg1) \<and> enabled cfg msg 
                    \<and> isReceiverOf p msg  
                    \<and> reachable cfg1 cfg')" 
using assms 
by (induct rule: reachable.induct, auto, 
    metis StepOutMsg ExistsMsg init enabled_def isReceiverOf.simps(1) 
    isReceiverOf.simps(2) message.exhaust, metis asynchronousSystem.step)

lemma ReachableTrans: 
fixes 
  cfg1 cfg2 cfg3 :: "('p, 'v, 's ) configuration" and 
  Q :: " 'p set"
assumes 
  "reachable cfg1 cfg2" and 
  "reachable cfg2 cfg3"
shows "reachable cfg1 cfg3"
proof - 
  have "reachable cfg2 cfg3 \<Longrightarrow> reachable cfg1 cfg2 \<Longrightarrow> reachable cfg1 cfg3" 
  proof (induct rule: reachable.induct, auto)
    fix cfg1' cfg2' msg cfg3'
    assume 
      "reachable cfg1 cfg2'"
      "cfg2' \<turnstile> msg \<mapsto> cfg3'"
    thus "reachable cfg1 cfg3'" using reachable.simps by metis
  qed
  thus ?thesis using assms by simp
qed

definition stepReachable ::
    "('p, 'v, 's) configuration
  \<Rightarrow> ('p ,'v) message
  \<Rightarrow> ('p, 'v, 's) configuration
  \<Rightarrow> bool" 
where
  "stepReachable c1 msg c2 \<equiv> 
    \<exists> c' c''. reachable c1 c' \<and> (c' \<turnstile> msg \<mapsto> c'') \<and> reachable c'' c2 "

lemma StepReachable:
fixes
  cfg cfg' :: "('p,'v,'s) configuration" and
  msg :: "('p, 'v) message"
assumes
  "reachable cfg cfg'" and
  "enabled cfg msg" and
  "\<not> (enabled cfg' msg)"
shows "stepReachable cfg msg cfg'" 
using assms
proof(induct rule: reachable.induct, simp)
  fix cfg1 cfg2 msga cfg3
  assume Step: "cfg2 \<turnstile> msga \<mapsto> cfg3" and
    ReachCfg1Cfg2: "reachable cfg1 cfg2" and
    IV: "(enabled cfg1 msg \<Longrightarrow> \<not> enabled cfg2 msg 
        \<Longrightarrow> stepReachable cfg1 msg cfg2)" and
    AssumpInduct: "enabled cfg1 msg" "\<not> enabled cfg3 msg"
  have ReachCfg2Cfg3: "reachable cfg2 cfg3" using Step 
    by (metis reachable.init reachable.step)
  show "stepReachable cfg1 msg cfg3" 
  proof (cases "enabled cfg2 msg")
    assume AssumpEnabled: "enabled cfg2 msg"
    hence "msga = msg" using OnlyOccurenceDisables Step AssumpInduct(2) by blast
    thus "stepReachable cfg1 msg cfg3" using ReachCfg1Cfg2 Step 
      unfolding stepReachable_def by (metis init)
  next
    assume AssumpNotEnabled: "\<not> enabled cfg2 msg"
    hence "stepReachable cfg1 msg cfg2" using IV AssumpInduct(1) by simp
    thus "stepReachable cfg1 msg cfg3"
      using ReachCfg2Cfg3 ReachableTrans asynchronousSystem.stepReachable_def
      by blast
  qed
qed

subsection \<open>Reachability with special process activity\<close>

text \<open>
  We say that \isb{qReachable cfg1 Q cfg2} iff cfg2 is reachable from cfg1
  only by activity of processes from Q.
\<close>
inductive qReachable ::
  "('p,'v,'s) configuration 
  \<Rightarrow> 'p set 
  \<Rightarrow> ('p,'v,'s) configuration 
  \<Rightarrow> bool"
where  
  InitQ: "qReachable cfg1 Q cfg1"
| StepQ: "\<lbrakk> qReachable cfg1 Q cfg2; (cfg2 \<turnstile> msg \<mapsto> cfg3) ;
            \<exists> p \<in> Q . isReceiverOf p msg \<rbrakk> 
          \<Longrightarrow> qReachable cfg1 Q cfg3"

text \<open>
  We say that \isb{withoutQReachable cfg1 Q cfg2} iff cfg2 is reachable from cfg1
  with no activity of processes from Q.
\<close>
abbreviation withoutQReachable ::
   "('p,'v,'s) configuration 
  \<Rightarrow> 'p set 
  \<Rightarrow> ('p,'v,'s) configuration 
  \<Rightarrow> bool"
where
  "withoutQReachable cfg1 Q cfg2 \<equiv> 
    qReachable cfg1 ((UNIV :: 'p set ) - Q) cfg2"

text\<open>
  Obviously q-reachability (and thus also without-q-reachability) implies 
  reachability.
\<close>
lemma QReachImplReach:
fixes
  cfg1 cfg2::  "('p, 'v, 's ) configuration" and
  Q :: " 'p set"
assumes
  "qReachable cfg1 Q cfg2"
shows 
  "reachable cfg1 cfg2"
using assms 
proof (induct rule: qReachable.induct)
  case InitQ thus ?case using reachable.simps by blast
next
  case StepQ thus ?case using reachable.step by simp
qed

lemma QReachableTrans: 
fixes cfg1 cfg2 cfg3 :: "('p, 'v, 's ) configuration" and
  Q :: " 'p set"
assumes "qReachable cfg2 Q cfg3" and
  "qReachable cfg1 Q cfg2"
shows "qReachable cfg1 Q cfg3"
using assms
proof (induct rule: qReachable.induct, simp)
  case (StepQ)
  thus ?case using qReachable.simps by metis
qed

lemma NotInQFrozenQReachability: 
fixes
  cfg1 cfg2 :: "('p,'v,'s) configuration" and
  p :: 'p and
  Q :: "'p set"
assumes
  "qReachable cfg1 Q cfg2" and
  "p \<notin> Q"
shows
  "states cfg1 p = states cfg2 p"
using assms 
proof(induct rule: qReachable.induct, auto)
  fix cfg1' Q' cfg2' msg cfg3 p'
  assume "qReachable cfg1' Q' cfg2'"
  assume Step: "cfg2' \<turnstile> msg \<mapsto> cfg3"
  assume Rec: "isReceiverOf p' msg"
  assume "p' \<in> Q'"  "p \<notin> Q'"
  hence notEq: "p \<noteq> p'" by blast
  with Rec have "\<not> (isReceiverOf p msg)" by (cases msg, simp_all)
  thus "states cfg2' p = states cfg3 p"
    using Step NoReceivingNoChange by simp
qed

corollary WithoutQReachablFrozenQ:
fixes
  cfg1 cfg2 :: "('p,'v,'s) configuration" and
  p :: 'p and
  Q :: "'p set"
assumes
  Steps: "withoutQReachable cfg1 Q cfg2" and
  P: "p \<in> Q"
shows
  "states cfg1 p = states cfg2 p"
using assms NotInQFrozenQReachability by simp

lemma NoActivityNoMessageLoss :
fixes
  cfg1 cfg2 :: "('p,'v,'s) configuration" and
  p :: 'p and
  Q :: "'p set" and
  m' :: "('p, 'v) message"
assumes
  "qReachable cfg1 Q cfg2" and
  "p \<notin> Q" and
  "isReceiverOf p m'"
shows
  "(msgs cfg1 m') \<le> (msgs cfg2 m')"
using assms
proof (induct rule: qReachable.induct, simp)
  case (StepQ cfg1' Q' cfg2' msg cfg3)
  then obtain p' where
    P': "p' \<in> Q'" "isReceiverOf p' msg" "p \<noteq> p'" by blast
  with assms(3) have "\<not>(isReceiverOf p' m')" 
    by (cases m', simp_all)
  with NoMessageLossStep StepQ(3) P'
    have "msgs cfg2' m' \<le> msgs cfg3 m'" 
    by simp
  with StepQ
    show "msgs cfg1' m' \<le> msgs cfg3 m'" by simp
qed

lemma NoMessageLoss:
fixes
  cfg1 cfg2 :: "('p,'v,'s) configuration" and
  p :: 'p and
  Q :: "'p set" and
  m' :: "('p, 'v) message"
assumes
  "withoutQReachable cfg1 Q cfg2" and
  "p \<in> Q" and
  "isReceiverOf p m'"
shows
  "(msgs cfg1 m') \<le> (msgs cfg2 m')" 
using assms NoActivityNoMessageLoss by simp

lemma NoOutMessageLoss:
fixes
  cfg1 cfg2 :: "('p,'v,'s) configuration" and
  v :: bool
assumes
  "reachable cfg1 cfg2"
shows
  "(msgs cfg1 <\<bottom>, outM v>) \<le> (msgs cfg2 <\<bottom>, outM v>)"
using assms 
proof(induct rule: reachable.induct, auto)
  fix cfg1 cfg' msg cfg2
  assume AssInduct:
    "reachable cfg1 cfg'"
    "msgs cfg1 <\<bottom>, outM v> \<le> msgs cfg' <\<bottom>, outM v>" 
    "cfg' \<turnstile> msg \<mapsto> cfg2"
  from AssInduct(3) have "msgs cfg' <\<bottom>, outM v> \<le> msgs cfg2 <\<bottom>, outM v>"  
    by (cases msg, auto)
  with AssInduct(2) show " msgs cfg1 <\<bottom>, outM v> \<le> msgs cfg2 <\<bottom>, outM v>"
    using le_trans by blast
qed 

lemma StillEnabled:
fixes 
  cfg1 cfg2:: "('p,'v,'s) configuration" and
  p :: 'p and
  msg :: "('p,'v) message" and
  Q :: "'p set"
assumes 
  "withoutQReachable cfg1 Q cfg2" and
  "p \<in> Q" and
  "isReceiverOf p msg" and
  "enabled cfg1 msg"
shows
  "enabled cfg2 msg"
using assms enabled_def NoMessageLoss 
  by (metis le_0_eq neq0_conv)

subsection\<open>Initial reachability\<close>

definition initial :: 
  "('p, 'v, 's) configuration \<Rightarrow> bool"
where
  "initial cfg \<equiv>
        (\<forall> p::'p . (\<exists> v::bool . ((msgs cfg (<p, inM v>)) = 1)))
      \<and> (\<forall> p m1 m2 . ((m1 \<in># (msgs cfg)) \<and> (m2 \<in># (msgs cfg)) 
         \<and> isReceiverOf p m1 \<and> isReceiverOf p m2) \<longrightarrow> (m1 = m2))
      \<and> (\<forall> v::bool . (msgs cfg) (<\<bottom>, outM v>) = 0)
      \<and> (\<forall> p v. (msgs cfg) (<p, v>) = 0)
      \<and> states cfg = start"

definition initReachable ::
  "('p, 'v, 's) configuration \<Rightarrow> bool"
where
  "initReachable cfg \<equiv> \<exists>cfg0 . initial cfg0 \<and> reachable cfg0 cfg"

lemma InitialIsInitReachable :
assumes "initial c"
shows "initReachable c"
  using assms reachable.init
  unfolding initReachable_def by blast

subsection \<open>Diamond property of reachability\<close>

lemma DiamondOne:
fixes
  cfg cfg1 cfg2 :: "('p,'v,'s) configuration" and
  p q :: 'p and
  m m' :: "('p,'v) message"
assumes
  StepP: "cfg \<turnstile> m  \<mapsto> cfg1" and
  PNotQ: "p \<noteq> q" and
  Rec: "isReceiverOf p m" "\<not> (isReceiverOf p m')" and
  Rec': "isReceiverOf q m'" "\<not> (isReceiverOf q m)" and
  StepWithoutP: "cfg \<turnstile> m' \<mapsto> cfg2"
shows
  "\<exists> cfg' :: ('p,'v,'s) configuration . (cfg1 \<turnstile> m' \<mapsto> cfg')
        \<and> (cfg2 \<turnstile> m \<mapsto> cfg')"
proof (cases m)
  case (InMsg p b)
  from StepWithoutP ExistsMsg have " m' \<in># (msgs cfg) " by simp          
  hence "m' \<in># (msgs cfg1)" 
    using StepP Rec NoMessageLossStep le_neq_implies_less le_antisym 
    by (metis  gr_implies_not0 neq0_conv)
  hence EnM': "enabled cfg1 m'" using enabled_def by auto
  from StepP ExistsMsg have "m \<in># (msgs cfg) " by simp
  hence "m \<in># (msgs cfg2)"
    using StepWithoutP Rec' NoMessageLossStep
    by (metis le_0_eq neq0_conv)
  hence EnM: "enabled cfg2 m" using enabled_def by auto
  assume CaseM:  "m = <p, inM b>"
  
  thus ?thesis 
  proof (cases m') 
    case (OutMsg b')
    thus ?thesis using StepWithoutP by simp
  next
    case (InMsg q b')
    define cfg' where "cfg' = \<lparr>states = \<lambda>s. (
      if s = q then
        trans q (states cfg q) (Bool b')
      else if s = p then
        trans p (states cfg p) (Bool b)
      else
        states cfg s),
      msgs = ((sends q (states cfg q) (Bool b')) 
        \<union># (((sends p (states cfg p) (Bool b))
            \<union># ((msgs cfg)-# m)) -# m'))\<rparr> "
    have StepP': "(cfg1 \<turnstile> m' \<mapsto> cfg')"
      using StepP  EnM' Rec
      unfolding cfg'_def InMsg CaseM by auto
    moreover from EnM have "(cfg2 \<turnstile> m \<mapsto> cfg')"
      using InMsg cfg'_def StepP StepP' StepWithoutP NoReceivingNoChange  
            Rec' CaseM EnM'
    proof (simp, clarify)
      assume msgCfg:
        "msgs cfg1 = (sends p (states cfg p) (Bool b)  
                     \<union># (msgs cfg -# <p, inM b>))"
        "msgs cfg2 = (sends q (states cfg q) (Bool b') 
                     \<union># (msgs cfg -# <q, inM b'>))"
      have "enabled cfg m" "enabled cfg m'" 
        using StepP StepWithoutP CaseM InMsg 
        by auto
      with msgCfg show 
        "(sends q (states cfg q) (Bool b') \<union># (msgs cfg1 -# <q, inM b'>)) =
         (sends p (states cfg p) (Bool b) \<union># (msgs cfg2 -# <p, inM b>))"
        using CaseM InMsg StepP StepWithoutP Rec' AXc[of "m'" "m" "msgs cfg"
          "sends q (states cfg q) (Bool b')" 
          "sends p (states cfg p) (Bool b)"]         
        unfolding enabled_def
        by metis
    qed
    ultimately show ?thesis by blast
  next
    case (Msg q v')
    define cfg' where "cfg' = \<lparr>states = \<lambda>s. (
      if s = q then
        trans q (states cfg q) (Value v')
      else if s = p then
        trans p (states cfg p) (Bool b)
      else
        states cfg s),
      msgs = ((sends q (states cfg q) (Value v')) 
        \<union># (((sends p (states cfg p) (Bool b))
            \<union># ((msgs cfg)-# m))
            -# m'))\<rparr>"
    have StepP': "(cfg1 \<turnstile> m' \<mapsto> cfg')"
      using StepP EnM' Rec
      unfolding Msg CaseM cfg'_def by auto

    moreover from EnM have "(cfg2 \<turnstile> m \<mapsto> cfg')"
      using Msg cfg'_def StepP StepP' StepWithoutP NoReceivingNoChange Rec' CaseM EnM'
    proof (simp,clarify) 
      assume msgCfg1:
        "msgs cfg1 = (sends p (states cfg p) (Bool b)   
                      \<union># (msgs cfg -# <p, inM b>))"
        "msgs cfg2 = (sends q (states cfg q) (Value v') 
                      \<union># (msgs cfg -# <q,  v'>))" 
      have "enabled cfg m" "enabled cfg m'" 
        using StepP StepWithoutP CaseM Msg 
        by auto
      with msgCfg1 show 
        "(sends q (states cfg q) (Value v') \<union># (msgs cfg1 -# <q, v'>)) =
         (sends p (states cfg p) (Bool b) \<union># (msgs cfg2 -# <p, inM b>))"
        using CaseM Msg StepP StepWithoutP Rec' AXc[of "m'" "m" "msgs cfg"
          "sends q (states cfg q) (Value v')" 
          "sends p (states cfg p) (Bool b)"]
        unfolding enabled_def by metis
    qed
    ultimately show ?thesis by blast
  qed
next
  case (OutMsg b)
  thus ?thesis using StepP by simp
next
  case (Msg p v)
  from StepWithoutP ExistsMsg have " m' \<in># (msgs cfg) " by simp
  hence "m' \<in># (msgs cfg1)" 
    using StepP Rec NoMessageLossStep le_neq_implies_less le_antisym 
    by (metis  gr_implies_not0 neq0_conv)
  hence EnM': "enabled cfg1 m'" using enabled_def by auto
  from StepP ExistsMsg have "m \<in># (msgs cfg) " by simp
  hence "m \<in># (msgs cfg2)"
    using StepWithoutP Rec' NoMessageLossStep
    by (metis le_0_eq neq0_conv)
  hence EnM: "enabled cfg2 m" using enabled_def by auto
  assume CaseM:  "m = <p, v>" 
  thus ?thesis 
  proof (cases m')
    case (OutMsg b')
    thus ?thesis using StepWithoutP by simp
  next
    case (InMsg q b')
    define cfg' where "cfg' = \<lparr>states = \<lambda>s. (
      if s = q then
        trans q (states cfg q) (Bool b')
      else if s = p then
        trans p (states cfg p) (Value v)
      else
        states cfg s),
      msgs = ((sends q (states cfg q) (Bool b')) 
        \<union># (((sends p (states cfg p) (Value v))
        \<union># ((msgs cfg)-# m))
        -# m'))\<rparr> "
    hence StepP': "(cfg1 \<turnstile> m' \<mapsto> cfg')"
      using StepP InMsg EnM' Rec CaseM
      by auto
    moreover from EnM have "(cfg2 \<turnstile> m \<mapsto> cfg')"
      using InMsg cfg'_def StepP StepP' StepWithoutP NoReceivingNoChange Rec' 
            CaseM EnM'
    proof (simp, clarify)
      assume msgCfg:
        "msgs cfg1 = (sends p (states cfg p) (Value v)
          \<union># (msgs cfg -# <p, v>))"
        "msgs cfg2 = (sends q (states cfg q) (Bool b')
          \<union># (msgs cfg -# <q, inM b'>))"
      have "enabled cfg m" "enabled cfg m'"
        using StepP StepWithoutP CaseM InMsg by auto
      with msgCfg show " (sends q (states cfg q) (Bool b') 
                         \<union># (msgs cfg1 -# <q, inM b'>)) 
                       = (sends p (states cfg p) (Value v) 
                         \<union># (msgs cfg2 -# <p, v>))"
        using CaseM StepP StepWithoutP Rec' InMsg AXc[of "m'" "m" "msgs cfg"
          "sends q (states cfg q) (Bool b')"
          "sends p (states cfg p) (Value v)"]
          unfolding enabled_def by metis
    qed
    ultimately show ?thesis by blast
  next
    case (Msg q v')
    define cfg' where "cfg' = \<lparr>states = \<lambda>s. (
      if s = q then
        trans q (states cfg q) (Value v')
      else if s = p then
        trans p (states cfg p) (Value v)
      else
        states cfg s),
      msgs = ((sends q (states cfg q) (Value v')) 
        \<union># (((sends p (states cfg p) (Value v))
        \<union># ((msgs cfg)-# m))
        -# m'))\<rparr> "
    hence StepP': "(cfg1 \<turnstile> m' \<mapsto> cfg')"
      using StepP Msg EnM' Rec CaseM by auto
    moreover from EnM have "(cfg2 \<turnstile> m \<mapsto> cfg')"
      using Msg cfg'_def StepP StepP' StepWithoutP NoReceivingNoChange Rec' CaseM EnM'
    proof (simp, clarify)
      assume msgCfg:
        "msgs cfg1 = (sends p (states cfg p) (Value v)
          \<union># (msgs cfg -# <p, v>))"
        "msgs cfg2 = (sends q (states cfg q) (Value v')
          \<union># (msgs cfg -# <q, v'>))"
      have "enabled cfg m" "enabled cfg m'"
        using StepP StepWithoutP CaseM Msg by auto

      with msgCfg show " (sends q (states cfg q) (Value v') 
                         \<union># (msgs cfg1 -# <q, v'>)) 
                       = (sends p (states cfg p) (Value v) 
                         \<union># (msgs cfg2 -# <p, v>))"
        using CaseM StepP StepWithoutP Rec' Msg 
          AXc[of "m'" "m" "msgs cfg" "sends q (states cfg q) (Value v')"
          "sends p (states cfg p) (Value v)"]
        unfolding enabled_def by metis
    qed
    ultimately show ?thesis by blast          
  qed
qed

lemma DiamondTwo:
fixes
  cfg cfg1 cfg2 :: "('p,'v,'s) configuration" and
  Q :: "'p set" and
  msg :: "('p, 'v) message"
assumes
  QReach: "qReachable cfg Q cfg1" and
  Step: "cfg  \<turnstile> msg \<mapsto> cfg2"
        "\<exists>p\<in>Proc - Q. isReceiverOf p msg"
shows
  "\<exists> (cfg' :: ('p,'v,'s) configuration) . (cfg1  \<turnstile> msg \<mapsto> cfg') 
  \<and> qReachable cfg2 Q cfg'"
using assms 
proof(induct rule: qReachable.induct)
  fix cfg Q
  have "qReachable cfg2 Q cfg2" using qReachable.simps(1) by blast
  moreover assume "cfg \<turnstile> msg \<mapsto> cfg2" "\<exists>p\<in>UNIV - Q. isReceiverOf p msg"
  ultimately have "(cfg \<turnstile> msg \<mapsto> cfg2) \<and> qReachable cfg2 Q cfg2" by blast
  thus "\<exists>cfg'.(cfg \<turnstile> msg \<mapsto> cfg') \<and> qReachable cfg2 Q cfg'" by blast
next
  fix cfg Q cfg1' msga cfg1
  assume   "(cfg \<turnstile> msg \<mapsto> cfg2)"
    "(\<exists>p\<in>UNIV - Q. isReceiverOf p msg)"
    "((cfg \<turnstile> msg \<mapsto> cfg2) \<Longrightarrow>
     (\<exists>p\<in>UNIV - Q. isReceiverOf p msg) \<Longrightarrow>
     (\<exists>cfg'. (cfg1' \<turnstile> msg \<mapsto> cfg') \<and> qReachable cfg2 Q cfg'))"
  hence "(\<exists>cfg'. (cfg1' \<turnstile> msg \<mapsto> cfg') \<and> (\<exists>p\<in>UNIV - Q. isReceiverOf p msg) 
        \<and> qReachable cfg2 Q cfg')" by blast
  then obtain cfg' where Cfg': "(cfg1' \<turnstile> msg \<mapsto> cfg')" 
    "(\<exists>p\<in>UNIV - Q. isReceiverOf p msg)" "qReachable cfg2 Q cfg'" by blast
  then obtain p where P: "p\<in>UNIV - Q" "isReceiverOf p msg" by blast
  assume Step2: "(cfg1' \<turnstile> msga \<mapsto> cfg1)"
    "(\<exists>p\<in>Q. isReceiverOf p msga)"
    "(qReachable cfg Q cfg1')"
  then obtain p' where P': "p'\<in>Q" "isReceiverOf p' msga" by blast
  from P'(1) P(1) have notEq: "p \<noteq> p'" by blast
  with P(2) P'(2) have "\<not> isReceiverOf p' msg" "\<not> isReceiverOf p msga"
    using UniqueReceiverOf[of p' msga p] UniqueReceiverOf[of p msg p']
    by auto
  with notEq P'(2) P(2) Cfg'(1) Step2(1) have 
    "\<exists>cfg''. (cfg' \<turnstile> msga \<mapsto> cfg'') \<and> (cfg1 \<turnstile> msg \<mapsto> cfg'')"
    using DiamondOne by simp
  then obtain cfg'' where Cfg'': "cfg' \<turnstile> msga \<mapsto> cfg''" "cfg1 \<turnstile> msg \<mapsto> cfg''" 
    by blast
  from Cfg''(1) Step2(2) Cfg'(3) have "qReachable cfg2 Q cfg''" 
    using qReachable.simps[of cfg2 Q cfg''] by auto
  with Cfg'(2) Cfg''(2) have 
    "(cfg1 \<turnstile> msg \<mapsto> cfg'') \<and> qReachable cfg2 Q cfg''"  by simp
  thus "\<exists>cfg'. (cfg1 \<turnstile> msg \<mapsto> cfg') \<and> qReachable cfg2 Q cfg'" by blast 
qed

text \<open>Proposition 1 of Völzer.\<close>
lemma Diamond:
fixes
  cfg cfg1 cfg2 :: "('p,'v,'s) configuration" and
  Q :: "'p set"
assumes
  QReach: "qReachable cfg Q cfg1" and
  WithoutQReach: "withoutQReachable cfg Q cfg2"
shows 
  "\<exists> cfg'. withoutQReachable cfg1 Q cfg' 
     \<and> qReachable cfg2 Q cfg'"
proof -
  define notQ where "notQ \<equiv> UNIV - Q"
  with WithoutQReach have "qReachable cfg notQ cfg2" by simp
  thus ?thesis using QReach notQ_def
  proof (induct rule: qReachable.induct)
    fix cfg2
    assume "qReachable cfg2 Q cfg1"
    moreover have "qReachable cfg1 (UNIV - Q) cfg1"
      using qReachable.simps by blast
    ultimately show 
      "\<exists>cfg'. qReachable cfg1 (UNIV - Q) cfg' 
        \<and> qReachable cfg2 Q cfg'"  
      by blast
  next
    fix cfg cfg2' cfg2 msg
    assume Ass1: " qReachable cfg Q cfg1" "qReachable cfg (UNIV - Q) cfg2' " 
    assume Ass2:  "cfg2' \<turnstile> msg \<mapsto> cfg2" "\<exists>p\<in>UNIV - Q. isReceiverOf p msg"
    assume "qReachable cfg Q cfg1 \<Longrightarrow> \<exists>cfg'. qReachable cfg1 (UNIV - Q) cfg' 
      \<and> qReachable cfg2' Q cfg'"
    with Ass1(1) have "\<exists>cfg'. qReachable cfg1 (UNIV - Q) cfg' 
      \<and> qReachable cfg2' Q cfg'" by blast
    then obtain cfg' where 
      Cfg'1: "qReachable cfg2' Q cfg'" and 
      Cfg':  "qReachable cfg1 (UNIV - Q) cfg'" by blast
    from Cfg'1 Ass2 have 
      "\<exists>cfg''.(cfg' \<turnstile> msg \<mapsto> cfg'') \<and> qReachable cfg2 Q cfg''" 
      using DiamondTwo by simp
    then obtain cfg'' where
      Cfg'': "cfg' \<turnstile> msg \<mapsto> cfg''" "qReachable cfg2 Q cfg''" by blast
    from Cfg' Cfg''(1) Ass2(2) have "qReachable cfg1 (UNIV - Q) cfg''"  
      using qReachable.simps[of cfg1 "UNIV-Q" cfg''] by auto
    with Cfg'' show 
      "\<exists>cfg'. qReachable cfg1 (UNIV - Q) cfg' 
        \<and> qReachable cfg2 Q cfg'" by blast
  qed
qed

subsection \<open>Invariant finite message count\<close>

lemma FiniteMessages:
fixes 
  cfg  :: "('p, 'v, 's) configuration"
assumes
  FiniteProcs: "finite Proc" and
  FiniteSends: "\<And> p s m. finite {v. v \<in># (sends p s m)}" and
  InitReachable: "initReachable cfg"
shows "finite {msg . msg \<in># msgs cfg}"
proof(-)
  have "\<exists> init . initial init \<and> reachable init cfg" using assms 
    unfolding initReachable_def by simp
  then obtain init where Init: "initial init" "reachable init cfg" 
    by blast
  have InitMsgs:"{msg . msg \<in># msgs init} 
    = { msg . (msg \<in># msgs init) \<and> (\<exists> p v. <p, v> = msg)} 
      \<union> { msg . (msg \<in># msgs init) \<and> (\<exists> v.  <\<bottom>, outM v> = msg)}
      \<union> { msg . (msg \<in># msgs init) \<and> (\<exists> p v.  <p, inM v> = msg)}" 
       by (auto,metis message.exhaust)
  have A:"{ msg . (msg \<in># msgs init) \<and> (\<exists> p v. <p, v> = msg)} = {}" 
  using initial_def[of init] Init(1)by (auto, metis less_not_refl3)
  have B:"{ msg . (msg \<in># msgs init) \<and> (\<exists> v.  <\<bottom>, outM v> = msg)} = {}" 
  using initial_def[of init] Init(1) by (auto, metis less_not_refl3)
  have "\<forall> p . finite {<p, inM True>, <p, inM False>}" by auto
  moreover have SubsetMsg:
    "\<forall> p. { msg . (msg \<in># msgs init) 
      \<and> (\<exists> v::bool .  <p, inM v> = msg)} 
      \<subseteq> {<p, inM True>, <p, inM False>}" by auto
  ultimately have AllFinite:
    "\<forall> p. finite { msg . (msg \<in># msgs init) 
      \<and> (\<exists> v::bool .  <p, inM v> = msg)}"
    using finite_subset by (clarify, auto)
  have " { msg . (msg \<in># msgs init) 
    \<and> (\<exists> p\<in>Proc . \<exists> v::bool.  <p, inM v> = msg)} 
      = (\<Union> p \<in> Proc . { msg . (msg \<in># msgs init) 
    \<and> (\<exists> v::bool .  <p, inM v> = msg)})" by auto
  hence "finite  { msg . (msg \<in># msgs init) 
    \<and> (\<exists> p\<in>Proc . \<exists> v::bool.  <p, inM v> = msg)}" 
    using AllFinite FiniteProcs by auto
  hence InitFinite:"finite {msg . msg \<in># msgs init}" 
    by (auto simp add: A B InitMsgs) 
  show ?thesis using Init(2) InitFinite
  proof(induct rule: reachable.induct, simp_all)
    fix cfg1 cfg2 msg cfg3
    assume assmsInduct:"reachable cfg1 cfg2" 
      "finite {msg. msg \<in># msgs cfg2}" "cfg2 \<turnstile> msg \<mapsto> cfg3" 
      "finite {msg. msg \<in># msgs cfg1}" "reachable init cfg" 
      "finite {msg. msg \<in># msgs init}"
    from assmsInduct(3) obtain p where "isReceiverOf p msg " 
      by (metis StepOutMsg isReceiverOf.simps(1) isReceiverOf.simps(2) 
       message.exhaust)
    hence "msgs cfg3 = ((msgs cfg2 -# msg) \<union># (sends p (states cfg2 p) 
      (unpackMessage msg) ))" 
      using assmsInduct(3) by (cases msg, auto simp add: add.commute)
    hence MsgSet: "{msg. msg \<in>#  msgs cfg3 } 
      = {m. m \<in># ((msgs cfg2 -# msg) \<union># (sends p (states cfg2 p) 
        (unpackMessage msg) )) } " by simp
    have "{v. v \<in># (msgs cfg2 -# msg)} \<subseteq> {msg. msg \<in># msgs cfg2}"
      by auto
    from finite_subset[OF this]
      have "finite {v. (v \<in># sends p (states cfg2 p) (unpackMessage msg))
        \<or> (v \<in># (msgs cfg2 -# msg))}"
      using FiniteSends assmsInduct(2) by auto
    thus "finite {msg. msg \<in># msgs cfg3}"
       unfolding MsgSet by auto
  qed
qed

end

end
