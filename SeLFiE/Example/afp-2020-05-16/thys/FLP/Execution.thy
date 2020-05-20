section \<open>Execution\<close>

text \<open>
  \file{Execution} introduces a locale for executions within asynchronous systems.
\<close>

theory Execution
imports AsynchronousSystem ListUtilities
begin

subsection \<open>Execution locale definition\<close>

text \<open>
  A (finite) execution within a system is a list of configurations \isb{exec}
  accompanied by a list of messages \isb{trace} such that the first configuration
  is initial and every next state can be reached processing the messages
  in \isb{trace}.
\<close>
locale execution =
  asynchronousSystem trans sends start    
for
  trans :: "'p \<Rightarrow> 's \<Rightarrow> 'v messageValue \<Rightarrow> 's" and
  sends :: "'p \<Rightarrow> 's \<Rightarrow> 'v messageValue \<Rightarrow> ('p, 'v) message multiset" and
  start :: "'p \<Rightarrow> 's"
+
fixes
  exec :: "('p, 'v, 's ) configuration list" and
  trace :: "('p, 'v) message list"
assumes 
  notEmpty: "length exec \<ge> 1" and 
  length: "length exec - 1 = length trace" and
  base: "initial (hd exec)" and
  step: "\<lbrakk> i < length exec - 1 ; cfg1 = exec ! i ; cfg2 = exec ! (i + 1) \<rbrakk>
      \<Longrightarrow> ((cfg1 \<turnstile> trace ! i \<mapsto> cfg2)) "
begin

abbreviation execMsg ::
  "nat \<Rightarrow> ('p,'v) message"
where
  "execMsg n \<equiv> (trace ! n)"

abbreviation execConf ::
  "nat \<Rightarrow> ('p, 'v, 's) configuration"
where
  "execConf n  \<equiv> (exec ! n)"

subsection \<open>Enabledness and occurrence in the execution\<close>

definition minimalEnabled ::
  "('p, 'v) message \<Rightarrow> bool"
where
  "minimalEnabled msg \<equiv> (\<exists> p . isReceiverOf p msg) 
    \<and> (enabled (last exec) msg)
    \<and> (\<exists> n . n < length exec \<and> enabled (execConf n) msg 
      \<and> (\<forall> n' \<ge> n . n' < length trace \<longrightarrow> msg \<noteq> (execMsg n'))
    \<and> (\<forall> n' msg' . ((\<exists> p . isReceiverOf p msg') 
      \<and> (enabled (last exec) msg') 
      \<and> n' < length trace 
      \<and> enabled (execConf n') msg' 
      \<and> (\<forall> n'' \<ge> n' . n'' < length trace \<longrightarrow> msg' \<noteq> 
                      (execMsg n''))) \<longrightarrow> n' \<ge> n))"

definition firstOccurrence ::
  "('p, 'v) message \<Rightarrow> nat \<Rightarrow> bool"
where                    
  "firstOccurrence msg n \<equiv> (\<exists> p . isReceiverOf p msg) 
    \<and> (enabled (last exec) msg) \<and> n < (length exec)
    \<and> enabled (execConf n) msg 
    \<and> (\<forall> n' \<ge> n . n' < length trace \<longrightarrow> msg \<noteq> (execMsg n'))
    \<and> ( n \<noteq> 0 \<longrightarrow> (\<not> enabled (execConf (n - 1)) msg 
      \<or> msg = execMsg (n - 1)))"

lemma FirstOccurrenceExists:
assumes
  "enabled (last exec) msg"
  "\<exists>p. isReceiverOf p msg"
shows
  "\<exists> n . firstOccurrence msg n"
proof-
  have "length exec - 1 < length exec 
    \<and> (\<forall> n' \<ge> (length exec - 1) . n' < length trace \<longrightarrow> trace ! n' \<noteq> msg)"
    using length
    by (metis diff_diff_cancel leD notEmpty zero_less_diff 
      zero_less_one)
  hence NNotInTrace: "\<exists> n < length exec . 
    (\<forall> n'\<ge>n . n' < length trace \<longrightarrow> trace ! n' \<noteq> msg)" by blast
  hence "\<exists> n0 < length exec . 
    (\<forall> n'\<ge>n0 . n' < length trace \<longrightarrow> trace ! n' \<noteq> msg) \<and>
    ((n0 = 0) 
      \<or> \<not> (\<forall> n' \<ge> (n0 - 1) . n' < length trace \<longrightarrow> trace ! n' \<noteq> msg))" 
    using MinPredicate2[of "\<lambda>x.(x < length exec 
      \<and> (\<forall>n'\<ge>x.(n'<length trace \<longrightarrow> trace ! n' \<noteq> msg)))"]
    by auto
  hence "\<exists> n0. n0 < length exec 
    \<and> (\<forall> n'\<ge>n0 . n' < length trace \<longrightarrow> trace ! n' \<noteq> msg) 
    \<and> ((n0 = 0) 
      \<or> \<not> (\<forall> n' \<ge> (n0 - 1) . n' < length trace \<longrightarrow> trace ! n' \<noteq> msg))" 
    by simp
  from this obtain n0 where N0a: "n0 < length exec 
    \<and> (\<forall> n'\<ge>n0 . n' < length trace \<longrightarrow> trace ! n' \<noteq> msg) 
    \<and> ((n0 = 0) 
      \<or> \<not> (\<forall> n' \<ge> (n0 - 1) . n' < length trace \<longrightarrow> trace ! n' \<noteq> msg))" 
    by metis
  hence N0: "n0 < length exec" 
    "(\<forall> n'\<ge>n0 . n' < length trace \<longrightarrow> trace ! n' \<noteq> msg)"
    "((n0 = 0) 
      \<or> \<not> (\<forall> n' \<ge> (n0 - 1) . n' < length trace \<longrightarrow> trace ! n' \<noteq> msg))" 
    using N0a by auto
  have N0': "n0 = 0 \<or> trace ! (n0 - 1) = msg"
  proof(cases "n0 = 0", auto)
    assume N0NotZero: "n0 > 0"
    hence "\<not> (\<forall> n' \<ge> (n0 - 1) . n' < length trace \<longrightarrow> trace ! n' \<noteq> msg)" 
      using N0(3) by blast
    moreover have "n0 - 1 < length trace"
      using N0(1) length N0NotZero 
      by (metis calculation le_less_trans)
    ultimately show "execMsg (n0 - Suc 0) = msg" using N0(2) 
      by (metis One_nat_def Suc_diff_Suc diff_Suc_eq_diff_pred 
         diff_diff_cancel diff_is_0_eq leI nat_le_linear)
  qed
  have "\<exists> n1 < length exec . 
    (\<forall> n'\<ge>n1 . n' < length trace \<longrightarrow> trace ! n' \<noteq> msg) 
    \<and> enabled (exec ! n1) msg 
    \<and> (n1 = 0 \<or> \<not> enabled (exec ! (n1 - 1)) msg \<or> trace ! (n1 - 1) = msg)"
  proof(cases "enabled (exec ! n0) msg")
    assume "enabled (execConf n0) msg"
    hence "n0 < length exec" 
      "(\<forall> n'\<ge>n0 . n' < length trace \<longrightarrow> trace ! n' \<noteq> msg)" 
      "enabled (exec ! n0) msg \<and>
      (n0 = 0 \<or> \<not> enabled (exec ! (n0 - 1)) msg \<or> trace ! (n0 - 1) = msg)"
    using N0 N0' by auto
    thus "\<exists>n1<length exec.
       (\<forall>n'\<ge>n1. n' < length trace \<longrightarrow> execMsg n' \<noteq> msg) 
       \<and> enabled (execConf n1) msg 
       \<and> (n1 = 0 \<or> \<not> enabled (execConf (n1 - 1)) msg 
         \<or> execMsg (n1 - 1) = msg)"
      by metis
  next
    assume NotEnabled: "\<not> enabled (execConf n0) msg"
    have "last exec = exec ! (length exec - 1)" using last_conv_nth notEmpty 
      by (metis NNotInTrace length_0_conv less_nat_zero_code)
    hence EnabledInLast: "enabled (exec ! (length exec - 1)) msg" 
      using assms(1) by simp
    hence "n0 \<noteq> length exec - 1" using NotEnabled by auto
    hence N0Small: "n0 < length exec - 1" using N0(1) by simp
    hence "\<exists> k < length exec - 1 - n0  . \<not> enabled (execConf (n0 + k)) msg 
      \<and> enabled (execConf (n0 + k + 1)) msg"
      using NatPredicateTippingPoint[of "length exec - 1 - n0" 
        "\<lambda>x.\<not>(enabled (exec ! (n0 + x)) msg)"]
        assms(1) NotEnabled EnabledInLast by simp
    then obtain k where K: " k < length exec - 1 - n0" 
      "\<not> enabled (execConf (n0 + k)) msg" 
      "enabled (execConf (n0 + k + 1)) msg" by blast
    define n1 where "n1 = k + n0 + 1"
    hence N1: "n1 \<ge> n0" "\<not> enabled (execConf (n1 - 1)) msg" 
      "enabled (execConf n1) msg" "n1 < length exec"
      unfolding n1_def using K
      by (auto simp add: add.commute)
    have "\<forall>n'\<ge>n1. n' < length trace \<longrightarrow> execMsg n' \<noteq> msg" 
      using N1(1) N0(2) by (metis order_trans)
    thus "\<exists>n1<length exec.
        (\<forall>n'\<ge>n1. n' < length trace \<longrightarrow> execMsg n' \<noteq> msg) 
        \<and> enabled (execConf n1) msg 
        \<and> (n1 = 0 \<or> \<not> enabled (execConf (n1 - 1)) msg 
          \<or> execMsg (n1 - 1) = msg)" 
    using N1 by auto
  qed
  then obtain n1 where N1: "n1 < length exec" 
    "\<forall> n'\<ge>n1 . n' < length trace \<longrightarrow> trace ! n' \<noteq> msg"
    "enabled (exec ! n1) msg"
    "n1 = 0 \<or> \<not> enabled (exec ! (n1 - 1)) msg \<or> trace ! (n1 - 1) = msg" 
    by metis
  hence "firstOccurrence msg n1" using assms unfolding firstOccurrence_def 
    by auto
  thus "\<exists>n. firstOccurrence msg n" by blast
qed

lemma ReachableInExecution:
assumes
  "i < length exec"
  "j \<le> i"
shows
  "reachable (execConf j) (execConf i)"
using assms proof(induct i, auto)
  show "reachable (execConf 0) (execConf 0)" 
    using reachable.simps by blast
next
  fix ia
  assume 
    IH: "(j \<le> ia \<Longrightarrow> reachable (execConf j) (execConf ia))" 
    "Suc ia < length exec" 
    "j \<le> Suc ia"  
    "i < length exec" 
    "j \<le> i"
  show "reachable (execConf j) (execConf (Suc ia))" 
  proof(cases "j = Suc ia", auto)
    show "reachable (execConf (Suc ia)) (execConf (Suc ia))" 
      using reachable.simps by metis
  next
    assume "j \<noteq> Suc ia"
    hence "j \<le> ia" using IH(3) by simp
    hence "reachable (execConf j) (execConf ia)" using IH(1) by simp
    moreover have "reachable (execConf ia) (execConf (Suc ia))" 
      using reachable.simps
      by (metis IH(2) Suc_eq_plus1 less_diff_conv local.step)
    ultimately show "reachable (execConf j) (execConf (Suc ia))" 
      using ReachableTrans by blast
  qed
qed

lemma LastPoint:
fixes
  msg::"('p, 'v) message"
assumes
  "enabled (last exec) msg"
obtains n where
  "n < length exec"
  "enabled (execConf n) msg"
  "\<forall> n' \<ge> n .
    n' < length trace \<longrightarrow> msg \<noteq> (execMsg n')"
  "\<forall> n0 . 
      n0 < length exec 
    \<and> enabled (execConf n0) msg 
    \<and> (\<forall> n' \<ge> n0 .
        n' < length trace \<longrightarrow> msg \<noteq> (execMsg n'))
    \<longrightarrow> n0 \<ge> n"
proof (cases ?thesis, simp)
  case False
  define len where "len = length exec - 1"
  have
    "len < length exec"
    "enabled (execConf len) msg" 
    "\<forall> n' \<ge> len . n' < length trace \<longrightarrow> msg \<noteq> (execMsg n')"
    using assms notEmpty length unfolding len_def
    by (auto, metis One_nat_def last_conv_nth list.size(3) not_one_le_zero)
  hence "\<exists> n . n < length exec \<and> enabled (execConf n) msg 
    \<and> (\<forall> n' \<ge> n . n' < length trace \<longrightarrow> msg \<noteq> (execMsg n'))"
    by blast
  from MinPredicate[OF this] 
    show ?thesis using that False by blast
qed

lemma ExistImpliesMinEnabled:
fixes 
  msg :: "('p, 'v) message" and
  p :: 'p
assumes 
  "isReceiverOf p msg" 
  "enabled (last exec) msg"
shows
  "\<exists> msg' . minimalEnabled msg'"
proof-
  have MsgHasMinTime:"\<forall> msg . (enabled (last exec) msg 
    \<and> (\<exists> p . isReceiverOf p msg))
    \<longrightarrow> (\<exists> n .  n < length exec \<and> enabled (execConf n) msg 
        \<and> (\<forall> n' \<ge> n . n' < length trace \<longrightarrow> msg \<noteq> (execMsg n'))
        \<and> (\<forall> n0 .  n0 < length exec \<and> enabled (execConf n0) msg 
        \<and> (\<forall> n' \<ge> n0 . n' < length trace \<longrightarrow> msg \<noteq> (execMsg n')) 
        \<longrightarrow> n0 \<ge> n))" by (clarify, rule LastPoint, auto)
  let ?enabledTimes = "{n::nat . \<exists> msg . (enabled (last exec) msg 
    \<and> (\<exists> p . isReceiverOf p msg))
    \<and>  n < length exec \<and> (enabled (execConf n) msg 
    \<and> (\<forall> n' \<ge> n . n' < length trace \<longrightarrow> msg \<noteq> (execMsg n')))}"
  have NotEmpty:"?enabledTimes \<noteq> {}" using assms MsgHasMinTime by blast
  hence "\<exists> n0 . n0 \<in> ?enabledTimes" by blast
  hence "\<exists> nMin \<in> ?enabledTimes . \<forall> x \<in> ?enabledTimes . x \<ge> nMin" 
    using MinPredicate[of "\<lambda>n.(n \<in> ?enabledTimes)"] by simp
  then obtain nMin where NMin: "nMin \<in> ?enabledTimes" 
    "\<forall> x \<in> ?enabledTimes . x \<ge> nMin" by blast
  hence "\<exists> msg . (enabled (last exec) msg \<and> (\<exists> p . isReceiverOf p msg))
    \<and>  nMin < length exec \<and> (enabled (execConf nMin) msg 
    \<and> (\<forall> n' \<ge> nMin . n' < length trace \<longrightarrow> msg \<noteq> (execMsg n'))
    \<and> (\<forall> n0 .  n0 < length exec \<and> enabled (execConf n0) msg 
      \<and> (\<forall> n' \<ge> n0 . n' < length trace \<longrightarrow> msg \<noteq> (execMsg n')) 
      \<longrightarrow> n0 \<ge> nMin))" by blast
  then obtain msg where "(enabled (last exec) msg 
    \<and> (\<exists> p . isReceiverOf p msg))
    \<and> nMin < length exec \<and>(enabled (execConf nMin) msg 
    \<and> (\<forall> n' \<ge> nMin . n' < length trace \<longrightarrow> msg \<noteq> (execMsg n'))
    \<and> (\<forall> n0 .  n0 < length exec \<and> enabled (execConf n0) msg 
      \<and> (\<forall> n' \<ge> n0 . n' < length trace \<longrightarrow> msg \<noteq> (execMsg n')) 
      \<longrightarrow> n0 \<ge> nMin))" by blast
  moreover have "(\<forall> n' msg' . ((\<exists> p . isReceiverOf p msg') 
    \<and> (enabled (last exec) msg') 
    \<and> n' < length trace \<and> enabled (execConf n') msg' 
    \<and> (\<forall> n'' \<ge> n' . n'' < length trace \<longrightarrow> msg' \<noteq> (execMsg n''))) 
      \<longrightarrow> n' \<ge> nMin)"
  proof(clarify)
    fix n' msg' p
    assume Assms:
      "isReceiverOf p msg'" 
      "enabled (last exec) msg'" 
      "n' < length trace" 
      "enabled (execConf n') msg'" 
      "\<forall>n'' \<ge> n'. (n'' < length trace) \<longrightarrow> (msg' \<noteq> execMsg n'')"
    from Assms(3) have "n' < length exec" using length by simp
    with Assms have "n' \<in> ?enabledTimes" by auto
    thus "nMin \<le> n'" using NMin(2) by simp
  qed
  ultimately have "minimalEnabled msg"
    using minimalEnabled_def by blast
  thus ?thesis by blast
qed

lemma StaysEnabledStep:
assumes
  En: "enabled cfg msg" and
  Cfg: "cfg = exec ! n" and
  N: "n < length exec" 
shows
  "enabled (exec ! (n + 1)) msg 
  \<or> n = (length exec - 1) 
  \<or> msg = trace ! n"
proof(cases "n = length exec - 1")
  case True
  thus ?thesis by simp
next
  case False
  with N have N: "n < length exec - 1" by simp
  with Cfg have Step:  "cfg \<turnstile> trace ! n \<mapsto> (exec ! (n + 1))" 
    using step by simp
  thus ?thesis proof(cases "enabled (exec ! (n + 1)) msg")
    case True
    thus ?thesis by simp
  next
    case False
    hence "\<not> enabled (exec ! (n + 1)) msg" by simp
    thus ?thesis using En enabled_def Step N OnlyOccurenceDisables by blast
  qed
qed                          

lemma StaysEnabledHelp:
assumes
  "enabled cfg msg" and
  "cfg = exec ! n" and
  "n < length exec"    
shows 
  "\<forall> i . i \<ge> n \<and> i < (length exec - 1) \<and> enabled (exec ! i) msg 
  \<longrightarrow> msg = (trace ! i) \<or> (enabled (exec ! (i+1)) msg)"
proof(clarify)
  fix i
  assume "n \<le> i" "i < length exec - 1"
    "enabled (execConf i) msg" "\<not> enabled (execConf (i + 1)) msg"
  thus "msg = (trace ! i)"
    using assms StaysEnabledStep
    by (metis add.right_neutral add_strict_mono le_add_diff_inverse2
        nat_neq_iff notEmpty  zero_less_one)
qed

lemma StaysEnabled:
assumes En: "enabled cfg msg" and
  "cfg = exec ! n" and
  "n < length exec"   
shows "enabled (last exec) msg \<or> (\<exists> i . i \<ge> n \<and> i < (length exec - 1) 
  \<and> msg = trace ! i )"
proof(cases "enabled (last exec) msg")
  case True
  thus ?thesis by simp
next
  case False 
  hence NotEnabled: "\<not> enabled (last exec) msg" by simp
  have "last exec = exec ! (length exec - 1)" 
    by (metis last_conv_nth list.size(3) notEmpty not_one_le_zero)
  hence "\<exists> l . l \<ge> n \<and> last exec = exec ! l \<and> l = length exec - 1" 
    using assms(3) by auto
  then obtain l where L: "l \<ge> n" "last exec = exec ! l" 
    "l = length exec - 1" by blast
  have "(\<exists> i . i \<ge> n \<and> i < (length exec - 1) \<and> msg = trace ! i )"  
  proof (rule ccontr)
    assume Ass: " \<not> (\<exists>i\<ge>n. i < length exec - 1 \<and> msg = execMsg i)" 
    hence Not: "\<forall> i. i < n \<or> i \<ge> length exec - 1 \<or> msg \<noteq> execMsg i" 
      by (metis leI)
    have "\<forall> i. i \<ge> n \<and> i \<le> length exec - 1 \<longrightarrow> enabled (exec ! i) msg" 
    proof(clarify)
      fix i 
      assume I: "n \<le> i" "i \<le> length exec - 1"  
      thus "enabled (execConf i) msg"
        using StaysEnabledHelp[OF assms] assms(1,2) Ass 
        by (induct i, auto, metis Suc_le_lessD le_Suc_eq)
    qed
    with NotEnabled L show False by simp
  qed
  thus ?thesis by simp
qed

end \<comment> \<open>end of locale Execution\<close>

subsection \<open>Expanding executions to longer executions\<close>

lemma (in asynchronousSystem) expandExecutionStep:
fixes 
  cfg :: "('p, 'v, 's ) configuration"
assumes
  CfgIsReachable: "(last exec') \<turnstile> msg \<mapsto> cMsg" and
  ExecIsExecution: "execution trans sends start exec' trace'" 
shows
  "\<exists> exec'' trace''. (execution trans sends start exec'' trace'') 
  \<and> (prefixList exec' exec'') 
  \<and> (prefixList trace' trace'') 
  \<and> (last exec'') = cMsg 
  \<and> (last trace'' = msg)"
proof -
  define execMsg where "execMsg = exec' @ [cMsg]"
  define traceMsg where "traceMsg = trace' @ [msg]"
  have ExecMsgEq: "\<forall> i < ((length execMsg) - 1) . execMsg ! i = exec'!i " 
    using execMsg_def by (auto simp add: nth_append)
  have TraceMsgEq: "\<forall> i < ((length traceMsg) - 1) . traceMsg!i = trace'!i" 
    using traceMsg_def 
    by (auto simp add: nth_append)
  have ExecLen: "(length execMsg) \<ge> 1" using execMsg_def by auto
  have lessLessExec: "\<forall> i . i < (length exec') \<longrightarrow> i < (length execMsg )" 
    unfolding execMsg_def by auto
  have ExecLenTraceLen: "length exec'- 1 = length trace'" 
    using ExecIsExecution execution.length by auto
  have lessLessTrace: "\<forall> i . i < (length exec' - 1) \<longrightarrow> i < (length trace')" 
    using ExecLenTraceLen by auto
  have Exec'Len: "length exec' \<ge> 1" 
    using ExecIsExecution execution.notEmpty by blast
  hence "hd exec' = hd execMsg " using execMsg_def
    by (metis One_nat_def hd_append2 length_0_conv not_one_le_zero)
  moreover have "initial (hd exec')" 
    using ExecIsExecution execution.base by blast 
  ultimately have ExecInit: "initial (hd execMsg)" using execMsg_def by auto
  have ExecMsgLen: "length execMsg - 1 = length traceMsg" 
    using ExecLenTraceLen unfolding execMsg_def traceMsg_def
    by (auto,metis Exec'Len Suc_pred length_greater_0_conv list.size(3) 
       not_one_le_zero) 
  have ExecSteps:"\<forall> i < length exec' - 1 .
    ((exec' ! i)  \<turnstile> trace' ! i \<mapsto> (exec' ! (i + 1)))" 
    using ExecIsExecution execution.step by blast
  have "\<forall> i < length execMsg - 1. 
    ((execMsg ! i) \<turnstile> traceMsg ! i \<mapsto> (execMsg ! (i + 1)))" 
    unfolding execMsg_def traceMsg_def
  proof auto
    fix i
    assume IlessLen:"i < (length exec')"
    show "((exec' @ [cMsg]) ! i) \<turnstile> ((trace' @ [msg]) ! i) 
      \<mapsto> ((exec' @ [cMsg]) ! (Suc i))" 
    proof (cases "(i < (length exec') - 1)")
    case True
      hence IlessLen1: "(i < (length exec') - 1)" by auto
      hence "((exec' ! i)  \<turnstile> trace' ! i \<mapsto> (exec' ! (i + 1)))" 
        using ExecSteps by auto
      with IlessLen1 ExecMsgEq lessLessExec execMsg_def 
      have "((exec' @ [cMsg]) ! i) \<turnstile> ((trace') ! i) 
        \<mapsto> ((exec' @ [cMsg]) ! (Suc i))" by auto
      thus "((exec' @ [cMsg]) ! i) \<turnstile> ((trace' @ [msg]) ! i) 
        \<mapsto> ((exec' @ [cMsg]) ! (Suc i))" 
        using IlessLen1 TraceMsgEq lessLessTrace traceMsg_def by auto
    next
    case False
      with IlessLen have IEqLen1: "(i = (length exec') - 1)" by auto
      thus "((exec' @ [cMsg]) ! i) \<turnstile> ((trace' @ [msg]) ! i) 
        \<mapsto> ((exec' @ [cMsg]) ! (Suc i))" 
        using  execMsg_def traceMsg_def  CfgIsReachable Exec'Len 
               ExecLenTraceLen ExecMsgEq ExecMsgLen IlessLen   
        by (metis One_nat_def Suc_eq_plus1 Suc_eq_plus1_left last_conv_nth 
           le_add_diff_inverse length_append less_nat_zero_code list.size(3) 
           list.size(4) nth_append_length)
    qed
  qed
  hence isExecution: "execution trans sends start execMsg traceMsg" 
    using ExecLen ExecMsgLen ExecInit  
    by (unfold_locales ,auto) 
  moreover have "prefixList exec' execMsg" unfolding execMsg_def 
    by (metis TailIsPrefixList not_Cons_self2)
  moreover have "prefixList trace' traceMsg" unfolding traceMsg_def 
    by (metis TailIsPrefixList not_Cons_self2)
  ultimately show ?thesis using execMsg_def traceMsg_def by (metis last_snoc)
qed

lemma (in asynchronousSystem) expandExecutionReachable:
fixes 
  cfg :: "('p, 'v, 's ) configuration" and
  cfgLast :: "('p, 'v, 's ) configuration"
assumes
  CfgIsReachable: "reachable (cfgLast) cfg" and
  ExecIsExecution: "execution trans sends start exec trace"  and
  ExecLast: "cfgLast = last exec" 
shows
  "\<exists> exec' trace'. (execution trans sends start exec' trace') 
  \<and> ((prefixList exec exec' 
    \<and> prefixList trace trace') 
    \<or> (exec = exec' \<and> trace = trace')) 
  \<and> (last exec') = cfg"
using CfgIsReachable  ExecIsExecution ExecLast 
proof (induct cfgLast cfg rule: reachable.induct, auto)
  fix msg cfg3 exec' trace'
  assume "(last exec') \<turnstile> msg \<mapsto> cfg3"
         "execution trans sends start exec' trace'"
  hence "\<exists> exec'' trace''. (execution trans sends start exec'' trace'') 
    \<and> (prefixList exec' exec'') 
    \<and> (prefixList trace' trace'') \<and> (last exec'') = cfg3 
    \<and> (last trace'') = msg" by (simp add: expandExecutionStep)
  then obtain  exec'' trace'' where 
    NewExec: "execution trans sends start exec'' trace''" 
             "prefixList exec' exec''" "prefixList trace' trace''" 
             "last exec'' = cfg3" by blast
  assume prefixLists: "prefixList exec exec'" 
                      "prefixList trace trace'" 
  from prefixLists(1) NewExec(2) have "prefixList exec exec''" 
    using PrefixListTransitive by auto
  moreover from prefixLists(2) NewExec(3) have 
    "prefixList trace trace''"  using PrefixListTransitive by auto
  ultimately show "\<exists> exec'' trace'' .
          execution trans sends start exec'' trace'' \<and>
          ((prefixList exec exec'' \<and> prefixList trace trace'') 
          \<or> (exec = exec'' \<and> trace = trace'')) \<and>
          last exec'' = cfg3" using NewExec(1) NewExec(4) by blast
next
  fix msg cfg3
  assume "(last exec) \<turnstile> msg \<mapsto> cfg3" "execution trans sends start exec trace"
  then show
    "\<exists>exec' trace'. execution trans sends start exec' trace' \<and>
       (prefixList exec exec' \<and> prefixList trace trace' 
        \<or> exec = exec' \<and> trace = trace') \<and> last exec' = cfg3" 
    using expandExecutionStep by blast
qed

lemma (in asynchronousSystem) expandExecution:
fixes 
  cfg :: "('p, 'v, 's ) configuration" and
  cfgLast :: "('p, 'v, 's ) configuration"
assumes
  CfgIsReachable: "stepReachable (last exec) msg cfg" and
  ExecIsExecution: "execution trans sends start exec trace"
shows
  "\<exists> exec' trace'. (execution trans sends start exec' trace') 
  \<and> (prefixList exec exec') 
  \<and> (prefixList trace trace') \<and> (last exec') = cfg 
  \<and> (msg \<in> set (drop (length trace) trace'))"  
proof -
  from CfgIsReachable obtain c' c'' where 
    Step: "reachable (last exec) c'" "c' \<turnstile> msg \<mapsto> c''" "reachable c'' cfg" 
    by (auto simp add: stepReachable_def)
  from Step(1) ExecIsExecution have "\<exists> exec' trace' .
    execution trans sends start exec' trace' \<and>
    ((prefixList exec exec' \<and> prefixList trace trace') 
    \<or> (exec = exec' \<and> trace = trace')) \<and>
    last exec' = c'" by (auto simp add: expandExecutionReachable)
  then obtain  exec' trace' where Exec': 
    "execution trans sends start exec' trace'"
    "(prefixList exec exec' \<and> prefixList trace trace') 
      \<or> (exec = exec' \<and> trace = trace')"
    "last exec' = c'" by blast
  from Exec'(1) Exec'(3) Step(2) have "\<exists> exec'' trace'' . 
    execution trans sends start exec'' trace'' \<and>
    prefixList exec' exec'' \<and> prefixList trace' trace'' 
    \<and> last exec'' = c'' \<and> last trace'' = msg" 
    by (auto simp add: expandExecutionStep)
  then obtain exec'' trace'' where Exec'': 
    "execution trans sends start exec'' trace''"
    "prefixList exec' exec''" "prefixList trace' trace''" 
    "last exec'' = c''" "last trace'' = msg" by blast
  have PrefixLists: "prefixList exec exec'' \<and> prefixList trace trace''"  
  proof(cases "exec = exec' \<and> trace = trace'")
  case True
    with Exec'' show "prefixList exec exec'' \<and> prefixList trace trace''" 
    by auto
  next
  case False
    with Exec'(2) have Prefix: "prefixList exec exec'" 
      "prefixList trace trace'" by auto
    from Prefix(1) Exec''(2) have "prefixList exec exec''" 
      using PrefixListTransitive by auto
    with Prefix(2) Exec''(3) show  "prefixList exec exec'' 
      \<and> prefixList trace trace''" 
      using PrefixListTransitive by auto
  qed
  with Exec''(5) have MsgInTrace'': "msg \<in> set (drop (length trace) trace'')" 
    by (metis PrefixListMonotonicity drop_eq_Nil last_drop 
      last_in_set not_le)
  from Step(3) Exec''(1) Exec''(4) have "\<exists> exec''' trace''' .
    execution trans sends start exec''' trace''' \<and>
    ((prefixList exec'' exec''' \<and> prefixList trace'' trace''') 
    \<or> (exec'' = exec''' \<and> trace'' = trace''')) \<and>
    last exec''' = cfg" 
    by (auto simp add: expandExecutionReachable)
  then obtain exec''' trace''' where Exec''': 
    "execution trans sends start exec''' trace'''"
    "(prefixList exec'' exec''' \<and> prefixList trace'' trace''') 
    \<or> (exec'' = exec''' \<and> trace'' = trace''')"
    "last exec''' = cfg" by blast
  have "prefixList exec exec''' \<and> prefixList trace trace''' 
    \<and> msg \<in> set (drop (length trace) trace''')"  
  proof(cases "exec'' = exec''' \<and> trace'' = trace'''")
  case True
    with PrefixLists MsgInTrace'' 
    show "prefixList exec exec''' \<and> prefixList trace trace''' 
    \<and> msg \<in> set (drop (length trace) trace''')" by auto
  next
  case False
    with Exec'''(2) have Prefix: "prefixList exec'' exec'''" 
      "prefixList trace'' trace'''" by auto
    from Prefix(1) PrefixLists have "prefixList exec exec'''" 
      using PrefixListTransitive by auto
    with Prefix(2) PrefixLists have "prefixList exec exec''' 
      \<and> prefixList trace trace'''"  
      using PrefixListTransitive by auto
    moreover have "msg \<in> set (drop (length trace) trace''')" 
      using Prefix(2) PrefixLists MsgInTrace'' 
      by (metis (hide_lams, no_types) PrefixListHasTail append_eq_conv_conj 
         drop_take rev_subsetD set_take_subset)
    ultimately show ?thesis by auto
  qed
  with Exec'''(1) Exec'''(3) show ?thesis by blast
qed

subsection \<open>Infinite and fair executions\<close>

text \<open>
  Völzer does not give much attention to the definition of the
  infinite executions. We derive them from finite executions by considering
  infinite executions to be infinite sequence of finite executions increasing
  monotonically w.r.t. the list prefix relation.
\<close>

definition (in asynchronousSystem) infiniteExecution ::
  "(nat \<Rightarrow> (('p, 'v, 's) configuration list)) 
  \<Rightarrow> (nat \<Rightarrow> (('p, 'v) message list)) \<Rightarrow> bool"
where
  "infiniteExecution fe ft \<equiv>
    \<forall> n . execution trans sends start (fe n) (ft n) \<and> 
      prefixList (fe n) (fe (n+1)) \<and>
      prefixList (ft n) (ft (n+1))"

definition (in asynchronousSystem) correctInfinite ::
  "(nat \<Rightarrow> (('p, 'v, 's) configuration list)) 
  \<Rightarrow> (nat \<Rightarrow> (('p, 'v) message list)) \<Rightarrow> 'p \<Rightarrow> bool"
where 
  "correctInfinite fe ft p \<equiv> 
    infiniteExecution fe ft
    \<and> (\<forall> n . \<forall> n0 < length (fe n). \<forall> msg .(enabled ((fe n) ! n0) msg) 
    \<and> isReceiverOf p msg 
    \<longrightarrow> (\<exists> msg' . \<exists> n' \<ge> n . \<exists> n0' \<ge> n0 .isReceiverOf p msg' 
    \<and> n0' < length (fe n') \<and> (msg' = ((ft n') ! n0'))))"

definition (in asynchronousSystem) fairInfiniteExecution ::
  "(nat \<Rightarrow> (('p, 'v, 's) configuration list)) 
  \<Rightarrow> (nat \<Rightarrow> (('p, 'v) message list)) \<Rightarrow> bool"
where
  "fairInfiniteExecution fe ft \<equiv>
    infiniteExecution fe ft
    \<and> (\<forall> n . \<forall> n0 < length (fe n). \<forall> p . \<forall> msg . 
      ((enabled ((fe n) ! n0) msg) 
        \<and> isReceiverOf p msg \<and> correctInfinite fe ft p ) 
      \<longrightarrow> (\<exists> n' \<ge> n . \<exists> n0' \<ge> n0 . n0' < length (ft n') 
        \<and> (msg = ((ft n') ! n0'))))"

end
