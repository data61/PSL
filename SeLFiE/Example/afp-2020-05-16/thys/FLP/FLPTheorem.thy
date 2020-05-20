section \<open>FLPTheorem\<close>

text \<open>
  \file{FLPTheorem} combines the results of \file{FLPSystem} with the concept
  of fair infinite executions and culminates in showing the impossibility
  of a consensus algorithm in the proposed setting.
\<close>

theory FLPTheorem
imports Execution FLPSystem
begin

locale flpPseudoConsensus =
  flpSystem trans sends start
for
  trans :: "'p \<Rightarrow> 's \<Rightarrow> 'v messageValue \<Rightarrow>'s" and
  sends :: "'p \<Rightarrow> 's \<Rightarrow> 'v messageValue \<Rightarrow> ('p, 'v) message multiset" and
  start :: "'p \<Rightarrow> 's" +
assumes
  Agreement: "\<And> i c . agreementInit i c" and
  PseudoTermination: "\<And>cc Q . terminationPseudo 1 cc Q"
begin

subsection \<open>Obtaining non-uniform executions\<close>

text \<open>
  Executions which end with a \isb{nonUniform} configuration can be expanded
  to a strictly longer execution consuming a particular message.

  This lemma connects the previous results to the world of executions,
  thereby paving the way to the final contradiction. It covers a big part of
  the original proof of the theorem, i.e.\ finding the expansion to a longer
  execution where the decision for both values is still possible.
  \voelzer{constructing executions using Lemma 2}
\<close>
lemma NonUniformExecutionsConstructable:
fixes
  exec :: "('p, 'v, 's ) configuration list " and
  trace :: "('p, 'v) message list" and 
  msg :: "('p, 'v) message" and
  p :: 'p  
assumes
  MsgEnabled: "enabled (last exec) msg" and
  PisReceiverOf: "isReceiverOf p msg" and
  ExecIsExecution: "execution trans sends start exec trace" and
  NonUniformLexec: "nonUniform (last exec)" and
  Agree: "\<And> cfg . reachable (last exec) cfg \<longrightarrow> agreement cfg"
shows
  "\<exists> exec' trace' . (execution trans sends start exec' trace') 
    \<and> nonUniform (last exec')
    \<and> prefixList exec exec' \<and> prefixList trace trace' 
    \<and> (\<forall> cfg . reachable (last exec') cfg \<longrightarrow> agreement cfg)
    \<and> stepReachable (last exec) msg (last exec') 
    \<and> (msg \<in> set (drop (length trace) trace'))"
proof -
  from NonUniformCanReachSilentBivalence[OF NonUniformLexec PseudoTermination Agree]
    obtain c' where C':
      "reachable (last exec) c'" 
      "val[p,c'] = {True, False}"
    by blast
  show ?thesis 
  proof (cases "stepReachable (last exec) msg c'")
    case True
    hence IsStepReachable: "stepReachable (last exec) msg c'" by simp
    hence "\<exists> exec' trace'. (execution trans sends start exec' trace') 
      \<and> prefixList exec exec' 
      \<and> prefixList trace trace' \<and> (last exec') = c' 
      \<and> msg \<in> set (drop (length trace) trace')" 
      using ExecIsExecution expandExecution
      by auto
    then obtain exec' trace' where NewExec: 
      "(execution trans sends start exec' trace')" 
      "prefixList exec exec'" "(last exec') = c'" "prefixList trace trace'" 
      "msg \<in> set (drop (length trace) trace')" by blast
    hence lastExecExec'Reachable: "reachable (last exec) (last exec')" 
      using C'(1) by simp
    hence InitReachLastExec':  "initReachable (last exec')" 
      using NonUniformLexec 
      by (metis ReachableTrans initReachable_def)
    hence nonUniformC': "nonUniform (last exec')" using C'(2) NewExec(3) 
      by (auto simp add: vUniform_def)
    hence isAgreementPreventing: 
      "(\<forall> cfg . reachable (last exec') cfg \<longrightarrow> agreement cfg)"
      using lastExecExec'Reachable Agree by (metis ReachableTrans)
    with NewExec nonUniformC' IsStepReachable show ?thesis by auto
  next
    case False
    hence NotStepReachable: "\<not> (stepReachable (last exec) msg c')" by simp
    from C'(1) obtain exec' trace' where NewExec: 
      "execution trans sends start exec' trace'"
      "(prefixList exec exec' \<and> prefixList trace trace') 
      \<or> (exec = exec' \<and> trace = trace')"
      "last exec' = c'"
      using ExecIsExecution expandExecutionReachable by blast
    have lastExecExec'Reachable: "reachable (last exec) (last exec')" 
      using C'(1) NewExec(3) by simp
    with NonUniformLexec have InitReachLastExec': 
      "initReachable (last exec')" 
      by (metis ReachableTrans initReachable_def)
    with C'(2) NewExec(3) have nonUniformC': "nonUniform (last exec')" 
      by (auto simp add: vUniform_def)
    show "\<exists> exec1 trace1 . (execution trans sends start exec1 trace1) 
      \<and> nonUniform (last exec1)
      \<and> prefixList exec exec1 \<and> prefixList trace trace1 
      \<and> (\<forall> cfg . reachable (last exec1) cfg \<longrightarrow> agreement cfg)
      \<and> stepReachable (last exec) msg (last exec1) 
      \<and> (msg \<in> set (drop (length trace) trace1))"
    proof (cases "enabled (last exec') msg") 
      case True
      hence EnabledMsg: "enabled (last exec') msg" by auto
      hence "\<exists> cMsg . ((last exec') \<turnstile> msg \<mapsto> cMsg )"  
      proof (cases msg)
        case (InMsg p' b)
        with PisReceiverOf have MsgIsInMsg: "(msg = <p, inM b>)" by auto
        define cfgInM where "cfgInM = \<lparr>states = \<lambda>proc. (
        if proc = p then
          trans p (states (last exec') p) (Bool b)
        else states (last exec') proc),
        msgs = (((sends p (states (last exec') p) (Bool b))
              \<union># (msgs (last exec')-# msg)))\<rparr> "
          with UniqueReceiverOf MsgIsInMsg EnabledMsg have 
          "((last exec') \<turnstile> msg \<mapsto> cfgInM)" by auto
        thus "\<exists> cMsg . ((last exec') \<turnstile> msg \<mapsto> cMsg )" by blast
      next 
        case (OutMsg b)
        thus "\<exists> cMsg . ((last exec') \<turnstile> msg \<mapsto> cMsg )" using PisReceiverOf 
          by auto
      next 
        case (Msg p' v')
        with PisReceiverOf have MsgIsVMsg: "(msg = <p, v'>)" by auto
        define cfgVMsg where "cfgVMsg =
          \<lparr>states = \<lambda>proc. (
              if proc = p then
               trans p (states (last exec') p) (Value v')
               else states (last exec') proc),
            msgs = (((sends p (states (last exec') p) (Value v'))
                \<union># (msgs (last exec') -# msg )))\<rparr> "
        with UniqueReceiverOf MsgIsVMsg EnabledMsg noInSends have 
          "((last exec') \<turnstile> msg \<mapsto> cfgVMsg)" by auto 
        thus "\<exists> cMsg . ((last exec') \<turnstile> msg \<mapsto> cMsg )" by blast
      qed  
      then obtain cMsg where  CMsg:"((last exec') \<turnstile> msg \<mapsto> cMsg )" by auto
      define execMsg where "execMsg = exec' @ [cMsg]"
      define traceMsg where "traceMsg = trace' @ [msg]"
      from NewExec(1) CMsg obtain execMsg traceMsg where isExecution: 
        "execution trans sends start execMsg traceMsg"
        and ExecMsg: "prefixList exec' execMsg" "prefixList trace' traceMsg"
        "last execMsg = cMsg" "last traceMsg = msg" 
        using expandExecutionStep by blast
      have isPrefixListExec: "prefixList exec execMsg" 
        using PrefixListTransitive NewExec(2) ExecMsg(1) by auto 
      have isPrefixListTrace: "prefixList trace traceMsg" 
        using PrefixListTransitive NewExec(2) ExecMsg(2) by auto
      have cMsgLastReachable: "reachable cMsg (last execMsg)" 
        by (auto simp add: ExecMsg reachable.init) 
      hence isStepReachable: "stepReachable (last exec) msg (last execMsg)" 
        using CMsg lastExecExec'Reachable   
        by (auto simp add: stepReachable_def) 
      have InitReachLastExecMsg: "initReachable (last execMsg)" 
        using CMsg InitReachLastExec' cMsgLastReachable 
        by (metis ReachableTrans initReachable_def step) 
      have "val[p, (last exec')] \<subseteq> val[p, cMsg]" 
        using CMsg PisReceiverOf InitReachLastExec'
          ActiveProcessSilentDecisionValuesIncrease[of p p "last exec'" msg cMsg]
        by auto
      with ExecMsg C'(2) NewExec(3) have 
        "val[p, (last execMsg)] = {True, False}" by auto
      with InitReachLastExecMsg have isNonUniform: 
        "nonUniform (last execMsg)" by (auto simp add: vUniform_def)
      have "reachable (last exec) (last execMsg)" 
        using lastExecExec'Reachable cMsgLastReachable CMsg 
        by (metis ReachableTrans step)
      hence isAgreementPreventing: 
        "(\<forall> cfg . reachable (last execMsg) cfg \<longrightarrow> agreement cfg)" 
        using Agree by (metis ReachableTrans)
      have "msg \<in> set (drop (length trace) traceMsg)" using ExecMsg(4) 
        isPrefixListTrace 
        by (metis (full_types) PrefixListMonotonicity last_drop last_in_set
          length_0_conv length_drop less_zeroE zero_less_diff)
      thus ?thesis using isExecution isNonUniform isPrefixListExec 
        isPrefixListTrace isAgreementPreventing isStepReachable by blast
    next
      case False
      hence notEnabled: "\<not> (enabled (last exec') msg)" by auto
      have isStepReachable: "stepReachable (last exec) msg (last exec')" 
        using MsgEnabled notEnabled lastExecExec'Reachable StepReachable 
          by auto
        with NotStepReachable NewExec(3) show ?thesis by simp
    qed 
  qed 
qed

lemma NonUniformExecutionBase:
fixes
  cfg
assumes
  Cfg: "initial cfg" "nonUniform cfg"
shows 
  "execution trans sends start [cfg] [] 
  \<and> nonUniform (last [cfg]) 
  \<and> (\<exists> cfgList' msgList'.  nonUniform (last cfgList') 
    \<and> prefixList [cfg] cfgList' 
    \<and> prefixList [] msgList'
    \<and> (execution trans sends start cfgList' msgList')
     \<and> (\<exists> msg'. execution.minimalEnabled [cfg] [] msg' 
         \<and> msg' \<in> set msgList'))"
proof -
  have NonUniListCfg: "nonUniform (last [cfg])" using Cfg(2) by auto
  have AgreeCfg': "\<forall> cfg' . 
    reachable (last [cfg]) cfg' \<longrightarrow> agreement cfg'" 
    using Agreement Cfg(1) 
    by (auto simp add: agreementInit_def reachable.init agreement_def)
  have StartExec: "execution trans sends start [cfg] []" 
    using Cfg(1) by (unfold_locales, auto)
  hence "\<exists> msg . execution.minimalEnabled [cfg] [] msg" 
    using Cfg execution.ExistImpliesMinEnabled
    by (metis enabled_def initial_def isReceiverOf.simps(1) 
       last.simps zero_less_one)
  then obtain msg where MinEnabledMsg: 
    "execution.minimalEnabled [cfg] [] msg" by blast
  hence "\<exists> pMin . isReceiverOf pMin msg" using StartExec 
    by (auto simp add: execution.minimalEnabled_def)
  then obtain pMin where PMin: "isReceiverOf pMin msg" by blast
  hence "enabled (last [cfg]) msg \<and> isReceiverOf pMin msg" 
    using MinEnabledMsg StartExec 
    by (auto simp add: execution.minimalEnabled_def)
  hence Enabled: "enabled (last [cfg]) msg" "isReceiverOf pMin msg" 
    by auto
  from Enabled StartExec NonUniListCfg PseudoTermination AgreeCfg' 
  have "\<exists> exec' trace' . (execution trans sends start exec' trace') 
    \<and> nonUniform (last exec')
    \<and> prefixList [cfg] exec' \<and> prefixList [] trace' 
    \<and> (\<forall> cfg' . reachable (last exec') cfg' \<longrightarrow> agreement cfg')
    \<and> stepReachable (last [cfg]) msg (last exec') 
    \<and> (msg \<in> set (drop (length []) trace'))" 
  using NonUniformExecutionsConstructable[of "[cfg]" "msg" "pMin"
          "[]::('p,'v) message list"] 
    by simp
  with StartExec NonUniListCfg MinEnabledMsg show ?thesis by auto
qed

lemma NonUniformExecutionStep:
fixes
 cfgList msgList
assumes
  Init: "initial (hd cfgList)" and
  NonUni: "nonUniform (last cfgList)" and
  Execution: "execution trans sends start cfgList msgList"
shows
  "(\<exists> cfgList' msgList' .
      nonUniform (last cfgList') 
      \<and> prefixList cfgList cfgList' 
      \<and> prefixList msgList msgList'
      \<and> (execution trans sends start cfgList' msgList') 
      \<and> (initial (hd cfgList'))
      \<and> (\<exists> msg'. execution.minimalEnabled cfgList msgList msg' 
        \<and> msg' \<in> (set (drop (length msgList ) msgList')) ))"
proof -
  have ReachImplAgree: "\<forall> cfg . reachable (last cfgList) cfg 
    \<longrightarrow> agreement cfg"
    using Agreement Init NonUni ReachableTrans
    unfolding agreementInit_def agreement_def initReachable_def
    by (metis (full_types))
  have "\<exists> msg p. enabled (last cfgList) msg \<and> isReceiverOf p msg" 
  proof -
    from PseudoTermination NonUni have 
      "\<exists>c'. qReachable (last cfgList) Proc c' \<and> decided c'" 
      using terminationPseudo_def by auto
      then obtain c' where C': "reachable (last cfgList) c'" 
        "decided c'" 
        using QReachImplReach by blast 
    have NoOut: 
      "0 = msgs (last cfgList) <\<bottom>, outM False>"  
      "0 = msgs (last cfgList) <\<bottom>, outM True>" 
      using NonUni ReachImplAgree PseudoTermination 
      by (metis NonUniformImpliesNotDecided neq0_conv)+
    with C'(2) have "(last cfgList) \<noteq> c'" 
      by (metis (full_types) less_zeroE)
    thus ?thesis using C'(1) ReachableStepFirst by blast
  qed
  then obtain msg p where Enabled: 
    "enabled (last cfgList) msg" "isReceiverOf p msg" by blast
  hence "\<exists> msg . execution.minimalEnabled cfgList msgList msg" 
    using Init execution.ExistImpliesMinEnabled[OF Execution] by auto        
  then obtain msg' where MinEnabledMsg: 
    "execution.minimalEnabled cfgList msgList msg'" by blast
  hence "\<exists> p' . isReceiverOf p' msg'"
    using Execution
    by (auto simp add: execution.minimalEnabled_def)
  then obtain p' where
    P': "isReceiverOf p' msg'" by blast
  hence Enabled':
    "enabled (last cfgList) msg'" "isReceiverOf p' msg'" 
    using MinEnabledMsg Execution
    by (auto simp add: execution.minimalEnabled_def)     
  have "\<exists> exec' trace' . (execution trans sends start exec' trace') 
    \<and> nonUniform (last exec')
    \<and> prefixList cfgList exec' \<and> prefixList msgList trace' 
    \<and> (\<forall> cfg . reachable (last exec') cfg \<longrightarrow> agreement cfg)
    \<and> stepReachable (last cfgList) msg' (last exec') 
    \<and> (msg' \<in> set (drop (length msgList) trace')) "
    using NonUniformExecutionsConstructable[OF Enabled' Execution
          NonUni] ReachImplAgree by auto
  thus ?thesis
    using MinEnabledMsg by (metis execution.base)
qed

subsection \<open>Non-uniformity even when demanding fairness\<close>

text \<open>
  Using \isb{NonUniformExecutionBase} and \isb{NonUniformExecutionStep} one can obtain
  non-uniform executions which are fair.

  Proving the fairness turned out quite cumbersome.
\<close>

text \<open>
  These two functions construct infinite series of configurations lists
  and message lists from two extension functions. 
\<close>
fun infiniteExecutionCfg ::
  "('p, 'v, 's) configuration \<Rightarrow>
   (('p, 'v, 's) configuration list \<Rightarrow> ('p, 'v) message list 
    \<Rightarrow> ('p, 'v, 's) configuration list) \<Rightarrow>
   (('p, 'v, 's) configuration list \<Rightarrow> ('p, 'v) message list 
    \<Rightarrow>('p, 'v) message list) 
  \<Rightarrow> nat
  \<Rightarrow> (('p, 'v, 's) configuration list)"
and  infiniteExecutionMsg ::
  "('p, 'v, 's) configuration \<Rightarrow>
   (('p, 'v, 's) configuration list \<Rightarrow> ('p, 'v) message list 
    \<Rightarrow> ('p, 'v, 's) configuration list) \<Rightarrow>
   (('p, 'v, 's) configuration list \<Rightarrow> ('p, 'v) message list 
    \<Rightarrow>('p, 'v) message list) 
  \<Rightarrow> nat
  \<Rightarrow> ('p, 'v) message list"
where
  "infiniteExecutionCfg cfg fStepCfg fStepMsg 0 = [cfg]"
| "infiniteExecutionCfg cfg fStepCfg fStepMsg (Suc n) =
    fStepCfg (infiniteExecutionCfg cfg fStepCfg fStepMsg n) 
             (infiniteExecutionMsg cfg fStepCfg fStepMsg n)"
| "infiniteExecutionMsg cfg fStepCfg fStepMsg 0 = []"
| "infiniteExecutionMsg cfg fStepCfg fStepMsg (Suc n) =
    fStepMsg (infiniteExecutionCfg cfg fStepCfg fStepMsg n) 
             (infiniteExecutionMsg cfg fStepCfg fStepMsg n)"

lemma FairNonUniformExecution:
fixes
  cfg
assumes
  Cfg: "initial cfg" "nonUniform cfg"
shows "\<exists> fe ft.
  (fe 0) = [cfg]
  \<and> fairInfiniteExecution fe ft
  \<and> (\<forall> n . nonUniform (last (fe n))
       \<and> prefixList (fe n) (fe (n+1)) 
       \<and> prefixList (ft n) (ft (n+1))
       \<and> (execution trans sends start (fe n) (ft n)))"
proof -
  have BC: 
    "execution trans sends start [cfg] [] 
    \<and> nonUniform (last [cfg]) 
    \<and> (\<exists> cfgList' msgList'.  nonUniform (last cfgList') 
    \<and> prefixList [cfg] cfgList' 
    \<and> prefixList [] msgList'
    \<and> (execution trans sends start cfgList' msgList')
    \<and> (\<exists> msg'. execution.minimalEnabled [cfg] [] msg' 
       \<and> msg' \<in> set msgList'))"
    using NonUniformExecutionBase[OF assms] .
  \<comment> \<open>fStep ... a step leading to a fair execution.\<close> 
  obtain fStepCfg fStepMsg where FStep: "\<forall> cfgList msgList . \<exists>cfgList' msgList' .
          fStepCfg cfgList msgList = cfgList' \<and>
          fStepMsg cfgList msgList = msgList' \<and>
          (initial (hd cfgList) \<and>
          nonUniform (last cfgList) \<and>
          execution trans sends start cfgList msgList \<longrightarrow> 
          (nonUniform (last (fStepCfg cfgList msgList)) 
          \<and> prefixList cfgList (fStepCfg cfgList msgList) 
          \<and> prefixList msgList (fStepMsg cfgList msgList) 
          \<and> execution trans sends start (fStepCfg cfgList msgList) 
              (fStepMsg cfgList msgList) 
          \<and> (initial (hd (fStepCfg cfgList msgList)))
          \<and> (\<exists> msg'. execution.minimalEnabled cfgList msgList msg' 
            \<and> msg' \<in> (set (drop (length msgList) 
                                (fStepMsg cfgList msgList))))))"
   using NonUniformExecutionStep
      PredicatePairFunctions2[of 
        "\<lambda> cfgList msgList cfgList' msgList'. 
          (initial (hd cfgList) 
          \<and> nonUniform (last cfgList) 
          \<and> execution trans sends start cfgList msgList 
            \<longrightarrow> (nonUniform (last cfgList') 
            \<and> prefixList cfgList cfgList' 
            \<and> prefixList msgList msgList' 
            \<and> execution trans sends start cfgList' msgList'
            \<and> (initial (hd cfgList'))
            \<and> (\<exists> msg'. execution.minimalEnabled cfgList msgList msg' 
              \<and> msg' \<in> (set (drop (length msgList ) msgList')))))" "False"] by auto
  define fe ft
    where "fe = infiniteExecutionCfg cfg fStepCfg fStepMsg"
      and "ft = infiniteExecutionMsg cfg fStepCfg fStepMsg"
  
  have BasicProperties: "(\<forall>n. nonUniform (last (fe n)) 
    \<and> prefixList (fe n) (fe (n + 1)) \<and> prefixList (ft n) (ft (n + 1)) 
    \<and> execution trans sends start (fe n) (ft n) 
    \<and> initial (hd (fe (n + 1))))"
  proof (clarify)
    fix n
    show "nonUniform (last (fe n)) \<and>
          prefixList (fe n) (fe (n + (1::nat))) 
          \<and> prefixList (ft n) (ft (n + (1::nat))) 
          \<and> execution trans sends start (fe n) (ft n) 
          \<and> initial (hd (fe (n + 1)))"
    proof(induct n)
      case 0
      hence "fe 0 = [cfg]" "ft 0 = []" "fe 1 = fStepCfg (fe 0) (ft 0)" 
        "ft 1 = fStepMsg (fe 0) (ft 0)"
        using fe_def ft_def
        by simp_all
      thus ?case
        using BC FStep
        by (simp, metis execution.base)
    next
      case (Suc n)
        thus ?case
        using fe_def ft_def
        by (auto, (metis FStep execution.base)+)
    qed
  qed
  have Fair: "fairInfiniteExecution fe ft" 
    using BasicProperties
    unfolding fairInfiniteExecution_def infiniteExecution_def 
      execution_def flpSystem_def
  proof(auto simp add: finiteProcs minimalProcs finiteSends noInSends) 
    fix n n0 p msg
    assume AssumptionFair: "\<forall>n. initReachable (last (fe n)) \<and>
       \<not> vUniform False (last (fe n)) \<and>
       \<not> vUniform True (last (fe n)) \<and>
       prefixList (fe n) (fe (Suc n)) \<and>
       prefixList (ft n) (ft (Suc n)) \<and>
       Suc 0 \<le> length (fe n) \<and>
       length (fe n) - Suc 0 = length (ft n) \<and>
       initial (hd (fe n)) \<and> 
       (\<forall>i<length (fe n) - Suc 0. ((fe n ! i) \<turnstile> (ft n ! i) 
       \<mapsto> (fe n ! Suc i))) \<and> initial (hd (fe (Suc n)))"
      "n0 < length (fe n)"
      "enabled (fe n ! n0) msg" 
      "isReceiverOf p msg" 
      "correctInfinite fe ft p"
    have MessageStaysOrConsumed: "\<And> n n1 n2 msg. 
      (n1 \<le> n2 \<and> n2 < length (fe n) \<and> (enabled (fe n ! n1) msg)) 
      \<longrightarrow> (enabled (fe n ! n2) msg) 
          \<or> (\<exists> n0' \<ge> n1. n0' < length (ft n) \<and> ft n ! n0' = msg)"
    proof(auto)
      fix n n1 n2 msg
      assume Ass: "n1 \<le> n2" "n2 < length (fe n)" "enabled (fe n ! n1) msg"
        "\<forall>index<length (ft n). n1 \<le> index \<longrightarrow> ft n ! index \<noteq> msg"
      have "\<forall> k \<le> n2 - n1 . 
        msgs (fe n ! n1) msg \<le> msgs (fe n ! (n1 + k)) msg" 
      proof(auto)
        fix k
        show "k \<le> n2 - n1 \<Longrightarrow> 
          msgs (fe n ! n1) msg \<le> msgs (fe n ! (n1 + k)) msg"
        proof(induct k, auto)
          fix k
          assume IV: "msgs (fe n ! n1) msg \<le> msgs (fe n ! (n1 + k)) msg" 
            "Suc k \<le> n2 - n1"
          from BasicProperties have Exec: 
            "execution trans sends start (fe n) (ft n)" by blast
          have "n2 \<le> length (ft n)"
            using Exec Ass(2)
            execution.length[of trans sends start "fe n" "ft n"]
            by simp
          hence RightIndex: "n1 + k \<ge> n1 \<and> n1 + k < length (ft n)"
            using IV(2) by simp
          have  Step: "(fe n ! (n1 + k)) \<turnstile> (ft n ! (n1 + k)) 
                      \<mapsto> (fe n ! Suc (n1 + k))" 
            using Exec execution.step[of trans sends start "fe n" "ft n" 
              "n1 + k" "fe n ! (n1 + k)" "fe n ! (n1 + k + 1)"] IV(2) 
              Ass(2) 
            by simp
          hence "msg \<noteq> (ft n ! (n1 + k))" 
            using Ass(4) Ass(2) IV(2) RightIndex Exec 
            execution.length[of trans sends start "fe n" "ft n"]
            by blast
          thus "msgs (fe n ! n1) msg \<le> msgs (fe n ! Suc (n1 + k)) msg" 
            using Step OtherMessagesOnlyGrowing[of "(fe n ! (n1 + k))" 
              "(ft n ! (n1 + k))" "(fe n ! Suc (n1 + k))" "msg"] IV(1)
            by simp
        qed
      qed
      hence "msgs (fe n ! n1) msg \<le> msgs (fe n ! n2) msg" 
        by (metis Ass(1) le_add_diff_inverse order_refl)
      thus "enabled (fe n ! n2) msg" using Ass(3) enabled_def 
        by (metis gr0I leD)
    qed
    have EnabledOrConsumed: "enabled (fe n ! (length (fe n) - 1)) msg 
      \<or> (\<exists>n0'\<ge>n0. n0' < length (ft n) \<and> ft n ! n0' = msg)" 
      using AssumptionFair(3) AssumptionFair(2) 
        MessageStaysOrConsumed[of "n0" "length (fe n) - 1" "n" "msg"] 
      by auto
    have EnabledOrConsumedAtLast: "enabled (last (fe n)) msg \<or> 
      (\<exists> n0' . n0' \<ge> n0 \<and> n0' < length (ft n) \<and> (ft n) ! n0' = msg )"
      using EnabledOrConsumed last_conv_nth AssumptionFair(2) 
      by (metis length_0_conv less_nat_zero_code)
    have Case2ImplThesis: "(\<exists> n0' . n0' \<ge> n0 \<and> n0' < length (ft n) 
      \<and> ft n ! n0' = msg) 
      \<Longrightarrow> (\<exists>n'\<ge>n. \<exists>n0'\<ge>n0. n0' < length (ft n') \<and> msg = ft n' ! n0')"
      by auto
    have Case1ImplThesis': "enabled (last (fe n)) msg 
      \<longrightarrow> (\<exists>n'\<ge>n. \<exists>n0'\<ge> (length (ft n)). n0' < length (ft n') 
          \<and> msg = ft n' ! n0')" 
    proof(clarify)
      assume AssumptionCase1ImplThesis': "enabled (last (fe n)) msg"
      show "\<exists>n'\<ge>n. \<exists>n0'\<ge>length (ft n). n0' < length (ft n') 
        \<and> msg = ft n' ! n0'" 
      proof(rule ccontr,simp)
        assume AssumptionFairContr: "\<forall>n'\<ge>n. \<forall>n0'<length (ft n'). 
          length (ft n) \<le> n0' \<longrightarrow> msg \<noteq> ft n' ! n0'"
        define firstOccSet where "firstOccSet n = { msg1 . \<exists> nMsg . 
          \<exists> n1 \<le> nMsg . 
          execution.firstOccurrence (fe n) (ft n) msg1 n1 
          \<and> execution.firstOccurrence (fe n) (ft n) msg nMsg }" for n
        have NotEmpty: "fe n \<noteq> []" using  AssumptionFair(2) 
          by (metis less_nat_zero_code list.size(3))
        have FirstToLast': 
          "\<forall> n . reachable ((fe n) ! 0) ((fe n) ! (length (fe n) - 1))"
          using execution.ReachableInExecution BasicProperties execution.notEmpty
          by (metis diff_less less_or_eq_imp_le not_gr0 not_one_le_zero)
        hence FirstToLast: "\<forall> n . reachable (hd (fe n)) (last (fe n))" 
          using NotEmpty hd_conv_nth last_conv_nth AssumptionFair(1) 
          by (metis (full_types) One_nat_def length_0_conv 
            not_one_le_zero)
        hence InitToLast: "\<forall> n . initReachable (last (fe n))" 
          using BasicProperties by auto
        have "\<And> msg n0 . \<forall> n . 
          (execution.firstOccurrence (fe n) (ft n) msg n0) 
          \<longrightarrow>  0 < msgs (last (fe n)) msg"
          using BasicProperties execution.firstOccurrence_def 
            enabled_def
          by metis
        hence "\<forall> n . \<forall> msg' \<in> (firstOccSet n) . 
          0 < msgs (last (fe n)) msg'" using firstOccSet_def by blast
        hence "\<forall> n . firstOccSet n \<subseteq> {msg. 0 < msgs (last (fe n)) msg}"
          by (metis (lifting, full_types) mem_Collect_eq subsetI)
        hence FiniteMsgs: "\<forall> n . finite (firstOccSet n)" 
          using FiniteMessages[OF finiteProcs finiteSends] InitToLast
          by (metis rev_finite_subset)
        have FirstOccSetDecrOrConsumed: "\<forall> index . 
          (enabled (last (fe index)) msg) 
          \<longrightarrow> (firstOccSet (Suc index) \<subset> firstOccSet index 
          \<and> (enabled (last (fe (Suc index))) msg)
            \<or> msg \<in> (set (drop (length (ft index)) (ft (Suc index)))))"
        proof(clarify)
          fix index
          assume AssumptionFirstOccSetDecrOrConsumed:
            "enabled (last (fe index)) msg" 
            "msg \<notin> set (drop (length (ft index)) (ft (Suc index)))"
          have NotEmpty: "fe (Suc index) \<noteq> []" "fe index \<noteq> []" 
            using BasicProperties 
            by (metis AssumptionFair(1) One_nat_def list.size(3) 
              not_one_le_zero)+
          have LengthStep: "length (ft (Suc index)) > length (ft index)"
            using AssumptionFair(1) 
            by (metis PrefixListMonotonicity)              
          have IPrefixList:
            "\<forall> i::nat . prefixList (ft i) (ft (Suc i))" 
            using AssumptionFair(1) by auto
          have IPrefixListEx:
            "\<forall> i::nat . prefixList (fe i) (fe (Suc i))" 
            using AssumptionFair(1) by auto
          have LastOfIndex:
            "(fe (Suc index) ! (length (fe index) - Suc 0)) 
            = (last (fe index))"
            using PrefixSameOnLow[of "fe index" "fe (Suc index)"]
              IPrefixListEx[rule_format, of index]
              NotEmpty LengthStep 
            by (auto simp add: last_conv_nth)
          have NotConsumedIntermediate: 
            "\<forall> i::nat < length (ft (Suc index)) . 
              (i \<ge> length (ft index)
              \<longrightarrow> ft (Suc index) ! i \<noteq> msg)" 
            using AssumptionFirstOccSetDecrOrConsumed(2) ListLenDrop 
            by auto
          hence 
            "\<not>(\<exists>i. i < length (ft (Suc index)) \<and> i \<ge> length (ft index)
            \<and> msg = (ft (Suc index)) ! i)" 
            using execution.length BasicProperties
            by auto
          hence "\<not>(\<exists>i. i < length (fe (Suc index)) - 1 
            \<and> i \<ge> length (fe index) - 1 
            \<and> msg = (ft (Suc index)) ! i)"
            using BasicProperties[rule_format, of "Suc index"]
              BasicProperties[rule_format, of "index"]
              execution.length[of trans sends start]
            by auto
          hence EnabledIntermediate: 
            "\<forall> i < length (fe (Suc index)) . (i \<ge> length (fe index) - 1
              \<longrightarrow> enabled (fe (Suc index) ! i) msg)" 
            using BasicProperties[rule_format, of "Suc index"]
              BasicProperties[rule_format, of "index"]
              execution.StaysEnabled[of trans sends start
              "fe (Suc index)" "ft (Suc index)" "last (fe index)" msg 
              "length (fe index) - 1 "]
              AssumptionFirstOccSetDecrOrConsumed(1)
            by (auto, metis AssumptionFair(1) LastOfIndex 
              MessageStaysOrConsumed)
          have "length (fe (Suc index)) - 1 \<ge> length (fe index) - 1"
            using PrefixListMonotonicity NotEmpty BasicProperties 
            by (metis AssumptionFair(1) diff_le_mono less_imp_le)
          hence "enabled (fe (Suc index) 
            ! (length (fe (Suc index)) - 1)) msg"
            using EnabledIntermediate NotEmpty(1) 
            by (metis diff_less length_greater_0_conv zero_less_one)
          hence EnabledInSuc: "enabled (last (fe (Suc index))) msg" 
            using NotEmpty last_conv_nth[of "fe (Suc index)"] by simp
          have IndexIsExec: 
            "execution trans sends start (fe index) (ft index)" 
            using BasicProperties by blast
          have SucIndexIsExec: 
            "execution trans sends start (fe (Suc index)) 
              (ft (Suc index))" 
            using BasicProperties by blast
          have SameCfgOnLow: "\<forall> i < length (fe index) . (fe index) ! i
            = (fe (Suc index)) ! i"
            using BasicProperties PrefixSameOnLow by auto
          have SameMsgOnLow: "\<forall> i < length (ft index) . (ft index) ! i
            = (ft (Suc index)) ! i"
            using BasicProperties PrefixSameOnLow by auto
          have SmallIndex: "\<And> nMsg . execution.firstOccurrence
            (fe (Suc index)) (ft (Suc index)) msg nMsg 
            \<Longrightarrow> nMsg < length (fe index)" 
          proof(-)
            fix nMsg
            assume "execution.firstOccurrence (fe (Suc index)) 
              (ft (Suc index)) msg nMsg"
            hence AssumptionSubset3: 
              "\<exists>p. isReceiverOf p msg"
                "enabled (last (fe (Suc index))) msg"
                "nMsg < length (fe (Suc index))"
                "enabled (fe (Suc index) ! nMsg) msg"
                "\<forall>n'\<ge>nMsg. n' < length (ft (Suc index)) 
                \<longrightarrow> msg \<noteq> ft (Suc index) ! n'"
                "nMsg \<noteq> 0 \<longrightarrow> \<not> enabled (fe (Suc index) ! (nMsg - 1)) 
                msg \<or> msg = ft (Suc index) ! (nMsg - 1)"
              using execution.firstOccurrence_def[of "trans" "sends" 
                "start" "fe (Suc index)" "ft (Suc index)" "msg" "nMsg"]
                SucIndexIsExec by auto
            show "nMsg < length (fe index)"
            proof(rule ccontr)
              assume AssumpSmallIndex: "\<not> nMsg < length (fe index)"
              have "fe index \<noteq> []" using BasicProperties 
                AssumptionFair(1)
                by (metis One_nat_def list.size(3) not_one_le_zero)
              hence "length (fe index) > 0" 
                by (metis length_greater_0_conv)
              hence nMsgNotZero: "nMsg \<noteq> 0" 
                using AssumpSmallIndex by metis
              hence SucCases: "\<not> enabled ((fe (Suc index)) ! (nMsg - 1))
                msg \<or> msg = (ft (Suc index)) ! (nMsg - 1)"
                using AssumptionSubset3(6) by blast
              have Cond1: "nMsg - 1 \<ge> length (fe index) - 1"
                using AssumpSmallIndex by (metis diff_le_mono leI)
              hence Enabled: "enabled (fe (Suc index) ! (nMsg - 1)) msg"
                using EnabledIntermediate AssumptionSubset3(3) 
                by (metis less_imp_diff_less)
              have Cond2: "nMsg - 1 \<ge> length (ft index) \<and> nMsg - 1
                < length (ft (Suc index))"
                using Cond1 execution.length[of "trans" "sends" "start"
                  "fe index" "ft index"]
                  IndexIsExec AssumptionSubset3(3) 
                  by (simp, metis AssumptionFair(1) One_nat_def Suc_diff_1 
                    Suc_eq_plus1 less_diff_conv nMsgNotZero neq0_conv)
              hence NotConsumed: "ft (Suc index) ! (nMsg - 1) \<noteq> msg" 
                using NotConsumedIntermediate by simp
              show False using SucCases Enabled NotConsumed
              by blast
            qed
          qed
          have Subset: "\<And> msgInSet . msgInSet \<in> firstOccSet (Suc index)
            \<Longrightarrow> msgInSet \<in> firstOccSet index" 
          unfolding firstOccSet_def
          proof(auto)
            fix msgInSet nMsg n1
            assume AssumptionSubset: "n1 \<le> nMsg"
              "execution.firstOccurrence (fe (Suc index)) 
                (ft (Suc index)) msgInSet n1"
              "execution.firstOccurrence (fe (Suc index)) 
                (ft (Suc index)) msg nMsg"
            have AssumptionSubset2: 
              "\<exists>p. isReceiverOf p msgInSet"
                "enabled (last (fe (Suc index))) msgInSet"
                "n1 < length (fe (Suc index))"
                "enabled (fe (Suc index) ! n1) msgInSet"
                "\<forall>n'\<ge>n1. n' < length (ft (Suc index)) 
                  \<longrightarrow> msgInSet \<noteq> ft (Suc index) ! n'"
                "n1 \<noteq> 0 \<longrightarrow> \<not> enabled (fe (Suc index) ! (n1 - 1)) 
                  msgInSet \<or> msgInSet = ft (Suc index) ! (n1 - 1)"
              using execution.firstOccurrence_def[of "trans" "sends" 
                "start" "fe (Suc index)" "ft (Suc index)" "msgInSet" 
                "n1"] AssumptionSubset(2) SucIndexIsExec by auto 
            have AssumptionSubset3: 
              "\<exists>p. isReceiverOf p msg"
                "enabled (last (fe (Suc index))) msg"
                "nMsg < length (fe (Suc index))"
                "enabled (fe (Suc index) ! nMsg) msg"
                "\<forall>n'\<ge>nMsg. n' < length (ft (Suc index)) 
                  \<longrightarrow> msg \<noteq> ft (Suc index) ! n'"
                "nMsg \<noteq> 0 \<longrightarrow> \<not> enabled (fe (Suc index) ! (nMsg - 1)) 
                  msg \<or> msg = ft (Suc index) ! (nMsg - 1)"
              using execution.firstOccurrence_def[of "trans" "sends" 
                "start" "fe (Suc index)" "ft (Suc index)" "msg" "nMsg"]
                AssumptionSubset(3) SucIndexIsExec by auto
            have ShorterTrace: "length (ft index) 
                                < length (ft (Suc index))" 
              using PrefixListMonotonicity BasicProperties by auto

            have FirstOccurrenceMsg: "execution.firstOccurrence 
              (fe index) (ft index) msg nMsg"
            proof-
              have Occ1: "\<exists> p . isReceiverOf p msg" 
                using AssumptionSubset3(1) by blast
              have Occ2: "enabled (last (fe index)) msg" 
                using AssumptionFirstOccSetDecrOrConsumed by blast

              have "(fe index) ! nMsg = (fe (Suc index)) ! nMsg"
                using SmallIndex AssumptionSubset(3) 
                  PrefixSameOnLow[of "fe index" "fe (Suc index)"] 
                  BasicProperties 
                by simp
              hence Occ4: "enabled ((fe index) ! nMsg) msg" 
                using AssumptionSubset3(4) by simp
              have OccSameMsg: "\<forall> n' \<ge> nMsg . n' < length (ft index) 
                \<longrightarrow> (ft index) ! n' = (ft (Suc index)) ! n'" 
                using PrefixSameOnLow BasicProperties by auto
              hence Occ5: "\<forall> n' \<ge> nMsg . n' < length (ft index) 
                \<longrightarrow> msg \<noteq> ((ft index) ! n')" 
                using AssumptionSubset3(5) ShorterTrace by simp

              have Occ6: "nMsg \<noteq> 0 \<longrightarrow> (\<not> enabled ((fe index) ! 
                (nMsg - 1)) msg \<or> msg = (ft index ) ! (nMsg - 1))" 
              proof(clarify)
                assume AssumpOcc6: "0 < nMsg" "msg \<noteq> ft index ! 
                  (nMsg - 1)" "enabled (fe index ! (nMsg - 1)) msg"
                have "nMsg - (Suc 0) < length (fe index) - (Suc 0)" 
                  using SmallIndex AssumptionSubset(3) AssumpOcc6(1) 
                  by (metis Suc_le_eq diff_less_mono)
                hence SmallIndexTrace: "nMsg - 1 < length (ft index)" 
                  using IndexIsExec execution.length 
                  by (metis One_nat_def)
                have "\<not> enabled (fe (Suc index) ! (nMsg - 1)) msg 
                  \<or> msg = ft (Suc index) ! (nMsg - 1)"
                  using AssumptionSubset3(6) AssumpOcc6(1) by blast
                moreover have "fe (Suc index) ! (nMsg - 1) 
                  = fe index ! (nMsg - 1)"
                  using SameCfgOnLow SmallIndex AssumptionSubset(3) 
                  by (metis less_imp_diff_less)
                moreover have "ft (Suc index) ! (nMsg - 1) 
                  = ft index ! (nMsg - 1)"
                  using SameMsgOnLow SmallIndexTrace by metis 
                ultimately have "\<not> enabled (fe index ! (nMsg - 1)) msg 
                  \<or> msg = ft index ! (nMsg - 1)"
                  by simp
                thus False using AssumpOcc6 by blast
              qed

              show ?thesis using IndexIsExec Occ1 Occ2 SmallIndex 
                AssumptionSubset(3) Occ4 Occ5 Occ6
                execution.firstOccurrence_def[of "trans" "sends" "start"
                  "fe index" "ft index"]
                by simp 
            qed

            have "execution.firstOccurrence (fe index) (ft index) 
              msgInSet n1" 
              using AssumptionSubset2 AssumptionSubset(1)
            proof-
              have Occ1': "\<exists>p. isReceiverOf p msgInSet" 
                using AssumptionSubset2(1) by blast                 
              have Occ3': "n1 < length (fe index)" 
                using SmallIndex AssumptionSubset(3) AssumptionSubset(1)
                by (metis le_less_trans)
              have "(fe index) ! n1 = (fe (Suc index)) ! n1"
                using Occ3' PrefixSameOnLow[of "fe index" 
                  "fe (Suc index)"] BasicProperties by simp
              hence Occ4': "enabled (fe index ! n1) msgInSet" 
                using AssumptionSubset2(4) by simp
              have OccSameMsg': "\<forall> n' \<ge> n1 . n' < length (ft index) 
                \<longrightarrow> (ft index) ! n' = (ft (Suc index)) ! n'" 
                using PrefixSameOnLow BasicProperties by auto
              hence Occ5': "\<forall>n' \<ge> n1. n' < length (ft index) 
                \<longrightarrow> msgInSet \<noteq> ft index ! n'" 
                using AssumptionSubset2(5) ShorterTrace by simp
              have "length (fe index) > 0" using NotEmpty(2) 
                by (metis length_greater_0_conv)
              hence "length (fe index) - 1 < length (fe index)" 
                by (metis One_nat_def diff_Suc_less)                  
              hence 
                "enabled (fe index ! (length (fe index) - 1)) msgInSet
                \<or> (\<exists>n0'\<ge>n1. n0' < length (ft index) \<and> ft index ! n0'
                  = msgInSet)"
                using Occ4' Occ3' MessageStaysOrConsumed[of "n1" 
                  "length (fe index) - 1" "index" "msgInSet"]
                by (metis Suc_pred' \<open>0 < length (fe index)\<close> 
                  not_le not_less_eq_eq)
              hence "enabled ((fe index) ! (length (fe index) - 1)) 
                msgInSet" 
                using Occ5' by auto
              hence Occ2': "enabled (last (fe index)) msgInSet" 
                using last_conv_nth[of "fe index"] NotEmpty(2) by simp

              have Occ6': "n1 \<noteq> 0 \<longrightarrow> \<not> enabled (fe index ! (n1 - 1)) 
                msgInSet \<or> msgInSet = ft index ! (n1 - 1)"
              proof(clarify)
                assume AssumpOcc6': "0 < n1" "msgInSet \<noteq> ft index ! 
                  (n1 - 1)" "enabled (fe index ! (n1 - 1)) msgInSet"
                have "n1 - (Suc 0) < length (fe index) - (Suc 0)" 
                  using Occ3' AssumpOcc6'(1) 
                  by (metis Suc_le_eq diff_less_mono)
                hence SmallIndexTrace': "n1 - 1 < length (ft index)" 
                  using IndexIsExec execution.length 
                  by (metis One_nat_def)
                have "\<not> enabled (fe (Suc index) ! (n1 - 1)) msgInSet 
                  \<or> msgInSet = ft (Suc index) ! (n1 - 1)"
                  using AssumptionSubset2(6) AssumpOcc6'(1) by blast
                moreover have "fe (Suc index) ! (n1 - 1) 
                  = fe index ! (n1 - 1)"
                  using SameCfgOnLow Occ3' by (metis less_imp_diff_less)
                moreover have "ft (Suc index) ! (n1 - 1) 
                  = ft index ! (n1 - 1)"
                  using SameMsgOnLow SmallIndexTrace' by metis 
                ultimately have "\<not> enabled (fe index ! 
                  (n1 - 1)) msgInSet \<or> msgInSet = ft index ! (n1 - 1)"
                  by simp
                thus False using AssumpOcc6' by blast
              qed

              show ?thesis using IndexIsExec Occ1' Occ2' Occ3' Occ4' 
                Occ5' Occ6'
                execution.firstOccurrence_def[of "trans" "sends" 
                  "start" "fe index" "ft index"]
                by simp  
            qed
            
            thus "\<exists>nMsg' n1'. n1' \<le> nMsg' 
              \<and> execution.firstOccurrence (fe index) (ft index) 
                msgInSet n1' 
              \<and> execution.firstOccurrence (fe index) (ft index) 
                msg nMsg'" 
              using FirstOccurrenceMsg AssumptionSubset(1) by blast
          qed

          have ProperSubset: "\<exists> msg' .msg' \<in> firstOccSet index 
            \<and> msg' \<notin> firstOccSet (Suc index)"
          proof-               
            have "initial (hd (fe index))" using AssumptionFair(1) 
              by blast
            hence "\<exists>msg'. execution.minimalEnabled (fe index) (ft index)
              msg' \<and>  msg' \<in> set (drop (length (ft index)) 
                (fStepMsg (fe index) (ft index)))" 
              using FStep fe_def ft_def
                BasicProperties by simp
            then obtain consumedMsg where ConsumedMsg: 
              "execution.minimalEnabled (fe index) (ft index) 
                consumedMsg"
              "consumedMsg \<in> set (drop (length (ft index)) 
                (fStepMsg (fe index) (ft index)))" by blast
            hence ConsumedIsInDrop:
              "consumedMsg \<in> set (drop (length (ft index)) (ft (Suc index)))"
              using fe_def ft_def FStep
                BasicProperties[rule_format, of index]
              by auto
            
            have MinImplAllBigger: "\<And> msg' . execution.minimalEnabled
            (fe index) (ft index) msg' 
             \<longrightarrow> (\<exists> OccM' . (execution.firstOccurrence (fe index) 
              (ft index) msg' OccM' )
                \<and> (\<forall> msg . \<forall> OccM . execution.firstOccurrence (fe index)
                  (ft index) msg OccM 
                \<longrightarrow> OccM' \<le> OccM))" 
            proof(auto)
              fix msg'
              assume AssumpMinImplAllBigger: "execution.minimalEnabled 
                (fe index) (ft index) msg'"
              have IsExecIndex: "execution trans sends start 
                (fe index) (ft index)" 
                using  BasicProperties[rule_format, of index] by simp
              have "(\<exists> p . isReceiverOf p msg') \<and> 
                (enabled (last (fe index)) msg')
                \<and> (\<exists> n .  n < length (fe index) 
                  \<and> enabled ( (fe index) ! n) msg' 
                  \<and> (\<forall> n' \<ge> n . n' < length (ft index) 
                  \<longrightarrow> msg' \<noteq> ((ft index)! n'))
                  \<and> (\<forall> n' msg' . ((\<exists> p . isReceiverOf p msg') 
                    \<and> (enabled (last (fe index)) msg') 
                    \<and> n' < length (ft index) 
                    \<and> enabled ((fe index)! n') msg' 
                    \<and> (\<forall> n'' \<ge> n' . n'' < length (ft index) 
                    \<longrightarrow> msg' \<noteq> ((ft index) ! n''))) \<longrightarrow> n' \<ge> n))" 
              using execution.minimalEnabled_def[of trans sends start 
                "(fe index)" "(ft index)" msg'] 
                AssumpMinImplAllBigger IsExecIndex by auto
              then obtain OccM' where OccM': 
                "(\<exists> p . isReceiverOf p msg')" 
                "(enabled (last (fe index)) msg')"
                "OccM' < length (fe index)" 
                "enabled ( (fe index) ! OccM') msg'"  
                "(\<forall> n' \<ge> OccM' . n' < length (ft index) 
                \<longrightarrow> msg' \<noteq> ((ft index)! n'))"
                "(\<forall> n' msg' . ((\<exists> p . isReceiverOf p msg') 
                  \<and> (enabled (last (fe index)) msg') 
                  \<and> n' < length (ft index) 
                  \<and> enabled ((fe index)! n') msg' 
                  \<and> (\<forall> n'' \<ge> n' . n'' < length (ft index) 
                  \<longrightarrow> msg' \<noteq> ((ft index) ! n''))) \<longrightarrow> n' \<ge> OccM')" 
                by blast                  
              have "0 < OccM' \<Longrightarrow> enabled (fe index ! (OccM' - Suc 0)) msg' 
                      \<Longrightarrow> msg' \<noteq> ft index ! (OccM' - Suc 0) \<Longrightarrow> False"
              proof(-)
                fix p
                assume AssumpContr: 
                  "0 < OccM'"
                  "enabled (fe index ! (OccM' - Suc 0)) msg'"
                  "msg' \<noteq> ft index ! (OccM' - Suc 0)"
                have LengthOccM': "(OccM' - 1) < length (ft index)" 
                using OccM'(3) IndexIsExec AssumpContr(1)   
                  AssumptionFair(1)
                  by (metis  One_nat_def Suc_diff_1 Suc_eq_plus1_left 
                    Suc_less_eq le_add_diff_inverse)
                have BiggerIndices: "(\<forall>n''\<ge>(OccM' - 1). 
                  n'' < length (ft index) \<longrightarrow> msg' \<noteq> ft index ! n'')"
                  using OccM'(5) by (metis AssumpContr(3) One_nat_def 
                      Suc_eq_plus1 diff_Suc_1 le_SucE le_diff_conv)
                have "(\<exists>p. isReceiverOf p msg') \<and> enabled (last 
                  (fe index)) msg' \<and> (OccM' - 1) < length (ft index)
                    \<and> enabled (fe index ! (OccM' - 1)) msg' 
                    \<and> (\<forall>n''\<ge>(OccM' - 1). n'' < length (ft index) 
                      \<longrightarrow> msg' \<noteq> ft index ! n'')" 
                  using OccM' LengthOccM' AssumpContr BiggerIndices 
                  by simp
                hence "OccM' \<le> OccM' - 1" using OccM'(6) by blast 
                thus False using AssumpContr(1) diff_less leD zero_less_one by blast
              qed
              hence FirstOccMsg': "execution.firstOccurrence (fe index)
                  (ft index) msg' OccM'"   
                unfolding execution_def
                  execution.firstOccurrence_def[OF IsExecIndex, of msg' OccM']
                by (auto simp add: OccM'(1,2,3,4,5))
              have "\<forall>msg OccM. execution.firstOccurrence (fe index) 
                (ft index) msg OccM \<longrightarrow> OccM' \<le> OccM" 
              proof clarify
                fix msg OccM
                assume  "execution.firstOccurrence (fe index) 
                  (ft index) msg OccM"
                hence AssumpOccMFirstOccurrence: 
                  "\<exists> p . isReceiverOf p msg" 
                  "enabled (last (fe index)) msg" 
                  "OccM < (length (fe index))"
                  "enabled ((fe index) ! OccM) msg" 
                  "(\<forall> n' \<ge> OccM . n' < length (ft index) 
                  \<longrightarrow> msg \<noteq> ((ft index) ! n'))"
                  "(OccM \<noteq> 0 \<longrightarrow> (\<not> enabled ((fe index) ! (OccM - 1)) 
                  msg \<or> msg = (ft index)!(OccM - 1)))"
                  by (auto simp add: execution.firstOccurrence_def[of 
                      trans sends start "(fe index)" "(ft index)" 
                      msg OccM] IsExecIndex)
                hence "(\<exists>p. isReceiverOf p msg) \<and>
                  enabled (last (fe index)) msg \<and>
                  enabled (fe index ! OccM) msg \<and> 
                  (\<forall>n''\<ge> OccM. n'' < length (ft index) 
                    \<longrightarrow> msg \<noteq> ft index ! n'')" 
                 by simp
                thus "OccM' \<le> OccM" using OccM' 
                proof(cases "OccM < length (ft index)",auto)
                  assume "\<not> OccM < length (ft index)"
                  hence "OccM \<ge> length (fe index) - 1" 
                    using AssumptionFair(1) by (metis One_nat_def leI)
                  hence "OccM = length (fe index) - 1"
                    using AssumpOccMFirstOccurrence(3) by simp
                  thus "OccM' \<le> OccM" using OccM'(3) by simp
                qed
              qed
              with FirstOccMsg' show "\<exists>OccM'. 
                execution.firstOccurrence (fe index) (ft index) 
                  msg' OccM' 
                \<and> (\<forall>msg OccM. execution.firstOccurrence (fe index) 
                  (ft index) msg OccM \<longrightarrow> OccM' \<le> OccM)" by blast
            qed

            have MinImplFirstOcc: "\<And> msg' . execution.minimalEnabled 
              (fe index) (ft index) msg' 
              \<Longrightarrow> msg' \<in> firstOccSet index"
            proof -
              fix msg'
              assume AssumpMinImplFirstOcc: 
                "execution.minimalEnabled (fe index) (ft index) msg'"
              then obtain OccM' where OccM': 
                "execution.firstOccurrence (fe index) (ft index) 
                  msg' OccM'"
                "\<forall> msg . \<forall> OccM . execution.firstOccurrence 
                (fe index) (ft index) msg OccM 
              \<longrightarrow> OccM' \<le> OccM" using MinImplAllBigger by blast
              thus "msg' \<in> firstOccSet index" using OccM' 
              proof (auto simp add: firstOccSet_def)
                have "enabled (last (fe index)) msg" 
                  using AssumptionFirstOccSetDecrOrConsumed(1) by blast
                hence "\<exists>nMsg .  execution.firstOccurrence (fe index) 
                  (ft index) msg nMsg"
                  using execution.FirstOccurrenceExists IndexIsExec 
                  AssumptionFair(4) by blast
                then obtain nMsg where NMsg: "execution.firstOccurrence
                  (fe index) (ft index) msg nMsg" by blast
                hence "OccM' \<le> nMsg" using OccM' by simp
                hence "\<exists>nMsg . OccM' \<le> nMsg \<and>
                  execution.firstOccurrence (fe index) (ft index) msg'
                    OccM' \<and>
                  execution.firstOccurrence (fe index) (ft index) msg 
                    nMsg" 
                  using OccM'(1) NMsg by blast 
                thus "\<exists>nMsg n1 . n1 \<le> nMsg \<and>
                  execution.firstOccurrence (fe index) (ft index) 
                    msg' n1 \<and>
                  execution.firstOccurrence (fe index) (ft index) 
                    msg nMsg" by blast
              qed
            qed
            hence ConsumedInSet: "consumedMsg \<in> firstOccSet index" 
              using ConsumedMsg by simp
            have GreaterOccurrence: "\<And> nMsg n1 . 
                execution.firstOccurrence (fe (Suc index)) 
                  (ft (Suc index)) consumedMsg n1 \<and> 
                execution.firstOccurrence (fe (Suc index)) 
                  (ft (Suc index)) msg nMsg 
                \<Longrightarrow> nMsg < n1" 
            proof(rule ccontr,auto)
              fix nMsg n1
              assume AssumpGreaterOccurrence: "\<not> nMsg < n1"
                "execution.firstOccurrence (fe (Suc index)) 
                  (ft (Suc index)) consumedMsg n1"
                "execution.firstOccurrence (fe (Suc index)) 
                  (ft (Suc index)) msg nMsg" 
              have "nMsg < length (fe index)" 
                using SmallIndex AssumpGreaterOccurrence(3) by simp
              hence "n1 < length (fe index)" 
                using AssumpGreaterOccurrence(1) 
                by (metis less_trans nat_neq_iff)
              hence N1Small: "n1 \<le> length (ft index)" 
                using IndexIsExec AssumptionFair(1) 
                by (metis  One_nat_def Suc_eq_plus1 le_diff_conv2 
                  not_le not_less_eq_eq)
              have NotConsumed: "\<forall> i \<ge> n1 . i < length (ft (Suc index))
                \<longrightarrow> consumedMsg \<noteq> (ft (Suc index)) ! i" 
                using execution.firstOccurrence_def[of "trans" "sends"
                  "start" "fe (Suc index)" "ft (Suc index)" 
                  "consumedMsg" "n1"]
                  AssumpGreaterOccurrence(2) SucIndexIsExec by auto
              have "\<exists> i \<ge> length (ft index) . 
                i < length (ft (Suc index)) 
                \<and> consumedMsg = (ft (Suc index)) ! i"
                using DropToIndex[of "consumedMsg" "length (ft index)"]
                ConsumedIsInDrop by simp
              then obtain i where IDef: "i \<ge> length (ft index)"
                "i < length (ft (Suc index))" 
                "consumedMsg = (ft (Suc index)) ! i" by blast
              thus False using NotConsumed N1Small by simp
            qed
            have "consumedMsg \<notin> firstOccSet (Suc index)" 
            proof(clarify)
              assume AssumpConsumedInSucSet: 
                "consumedMsg \<in> firstOccSet (Suc index)"
              hence "\<exists>nMsg n1. n1 \<le> nMsg \<and>
                  execution.firstOccurrence (fe (Suc index)) 
                    (ft (Suc index)) consumedMsg n1 \<and> 
                  execution.firstOccurrence (fe (Suc index)) 
                    (ft (Suc index)) msg nMsg" 
                using firstOccSet_def by blast
              thus False using GreaterOccurrence 
                by (metis less_le_trans less_not_refl3)
            qed
            thus ?thesis using ConsumedInSet by blast
          qed

          hence "firstOccSet (Suc index) \<subset> firstOccSet index" 
            using Subset by blast
          thus "firstOccSet (Suc index) \<subset> firstOccSet index 
            \<and> enabled (last (fe (Suc index))) msg"
            using EnabledInSuc by blast
        qed

        have NotConsumed: "\<forall> index \<ge> n . \<not> msg \<in> 
          (set (drop (length (ft index)) (ft (Suc index))))"
        proof(clarify)
          fix index
          assume AssumpMsgNotConsumed: "n \<le> index" 
            "msg \<in> set (drop (length (ft index)) (ft (Suc index)))"

          have "\<exists> n0' \<ge> length (ft index) . 
            n0' < length (ft (Suc index)) 
            \<and> msg = (ft (Suc index)) ! n0'" 
            using AssumpMsgNotConsumed(2) DropToIndex[of "msg" 
              "length (ft index)" "ft (Suc index)"] by auto
          then obtain n0' where MessageIndex: "n0' \<ge> length (ft index)" 
            "n0' < length (ft (Suc index))" 
            "msg = (ft (Suc index)) ! n0'" by blast
          have LengthIncreasing: "length (ft n) \<le> length (ft index)" 
            using AssumpMsgNotConsumed(1) 
          proof(induct index,auto)
            fix indexa
            assume AssumpLengthIncreasing: 
              "n \<le> indexa \<Longrightarrow> length (ft n) \<le> length (ft indexa)" 
              "n \<le> Suc indexa" "n \<le> index"
            show "length (ft n) \<le> length (ft (Suc indexa))"
            proof(cases "n = Suc indexa",auto)
              assume "n \<noteq> Suc indexa"
              hence "n \<le> indexa" using AssumpLengthIncreasing(2) 
                by (metis le_SucE)
              hence LengthNA: "length (ft n) \<le> length (ft indexa)" 
                using AssumpLengthIncreasing(1) by blast
              have PrefixIndexA: "prefixList (ft indexa) (ft (Suc indexa))"
                using BasicProperties by simp
              show "length (ft n) \<le> length (ft (Suc indexa))"
                using LengthNA PrefixListMonotonicity[OF PrefixIndexA]
                by (metis (hide_lams, no_types) antisym le_cases 
                  less_imp_le less_le_trans)
            qed
          qed
          thus False using AssumptionFairContr MessageIndex 
            AssumpMsgNotConsumed(1) 
            by (metis \<open>length (ft index) \<le> n0'\<close> le_SucI le_trans)
        qed

        hence FirstOccSetDecrImpl: 
          "\<forall> index \<ge> n . (enabled (last (fe index)) msg) 
          \<longrightarrow> firstOccSet (Suc index) \<subset> firstOccSet index 
            \<and> (enabled (last (fe (Suc index))) msg)"
          using FirstOccSetDecrOrConsumed by blast
        hence FirstOccSetDecrImpl: "\<forall> index \<ge> n . firstOccSet 
          (Suc index) \<subset> firstOccSet index"
          using KeepProperty[of "n" "\<lambda>x.(enabled (last (fe x)) msg)" 
            "\<lambda>x.(firstOccSet (Suc x) \<subset> firstOccSet x)"]
            AssumptionCase1ImplThesis' by blast
        hence FirstOccSetDecr': "\<forall> index \<ge> n . 
          card (firstOccSet (Suc index)) < card (firstOccSet index)"
          using FiniteMsgs psubset_card_mono by metis
        hence "card (firstOccSet (n + (card (firstOccSet n) + 1))) 
          \<le> card (firstOccSet n) - (card (firstOccSet n) + 1)"
          using SmallerMultipleStepsWithLimit[of "n" 
            "\<lambda>x. card (firstOccSet x)" "card (firstOccSet n) + 1"]
          by blast
        hence IsNegative:"card (firstOccSet (n + (card 
          (firstOccSet n) + 1))) < 0" 
          by (metis FirstOccSetDecr' diff_add_zero leD le_add1 
            less_nat_zero_code neq0_conv)
        thus False by (metis less_nat_zero_code)
      qed
    qed

    hence Case1ImplThesis: "enabled (last (fe n)) msg 
      \<Longrightarrow> (\<exists>n'\<ge>n. \<exists>n0'\<ge>n0. n0' < length (ft n') \<and> msg = ft n' ! n0')"
      using AssumptionFair(2) execution.length[of trans sends start 
        "fe n" "ft n"] BasicProperties 
      by (metis One_nat_def Suc_eq_plus1 Suc_lessI leI le_less_trans 
        less_asym less_diff_conv)

    show "\<exists>n'\<ge>n. \<exists>n0'\<ge>n0. n0' < length (ft n') \<and> msg = ft n' ! n0'"
    using disjE[OF EnabledOrConsumedAtLast Case1ImplThesis Case2ImplThesis] .
  qed
  show ?thesis proof (rule exI[of _ fe], rule exI[of _ ft])
    show "fe 0 = [cfg] \<and> fairInfiniteExecution fe ft 
      \<and> (\<forall>n. nonUniform (last (fe n)) \<and> prefixList (fe n) (fe (n + 1)) 
          \<and> prefixList (ft n) (ft (n + 1))
          \<and> execution trans sends start (fe n) (ft n))"
    using Fair fe_def FStep BasicProperties by auto
  qed
qed

subsection \<open>Contradiction\<close>

text \<open>
  An infinite execution is said to be a terminating FLP execution if each process
  at some point sends a decision message or if it stops, which is expressed
  by the process not processing any further messages.
\<close>
definition (in flpSystem) terminationFLP::
  "(nat \<Rightarrow> ('p, 'v, 's) configuration list) 
  \<Rightarrow> (nat \<Rightarrow> ('p, 'v) message list) \<Rightarrow> bool"
where
  "terminationFLP fe ft \<equiv> infiniteExecution fe ft \<longrightarrow> 
  (\<forall> p . \<exists> n .
     (\<exists> i0 < length (ft n). \<exists> b . 
      (<\<bottom>, outM b> \<in># sends p (states ((fe n) ! i0) p) (unpackMessage ((ft n) ! i0)))
      \<and> isReceiverOf p ((ft n) ! i0))
  \<or> (\<forall> n1 > n . \<forall> m \<in> set (drop (length (ft n)) (ft n1)) . \<not> isReceiverOf p m))"

theorem ConsensusFails:
assumes 
  Termination:
    "\<And> fe ft . (fairInfiniteExecution fe ft \<Longrightarrow> terminationFLP fe ft)" and
  Validity: "\<forall> i c . validity i c" and
  Agreement: "\<forall> i c . agreementInit i c"
shows
  "False"
proof -
  obtain cfg where Cfg: "initial cfg" "nonUniform cfg"
    using InitialNonUniformCfg[OF PseudoTermination Validity Agreement] 
        by blast
  obtain fe:: "nat \<Rightarrow> ('p, 'v, 's) configuration list" and
              ft:: "nat \<Rightarrow> ('p, 'v) message list"
    where FE: "(fe 0) = [cfg]" "fairInfiniteExecution fe ft"
        "(\<forall>(n::nat) . nonUniform (last (fe n)) 
          \<and> prefixList (fe n) (fe (n+1)) 
          \<and> prefixList (ft n) (ft (n+1))
          \<and> (execution trans sends start (fe n) (ft n)))" 
    using FairNonUniformExecution[OF Cfg] 
    by blast

  have AllArePrefixesExec: "\<forall> m . \<forall> n > m . prefixList (fe m) (fe n)"
  proof(clarify)
    fix m::nat and n::nat
    assume MLessN: "m < n"
    have "prefixList (fe m) (fe n)" using MLessN 
    proof(induct n, simp)
      fix n
      assume IA: "(m < n) \<Longrightarrow> (prefixList (fe m) (fe n))" "m < (Suc n)"
      have "m = n \<or> m < n" using IA(2) by (metis less_SucE)
      thus "prefixList (fe m) (fe (Suc n))"
      proof(cases "m = n", auto)
        show "prefixList (fe n) (fe (Suc n))" using FE by simp
      next
        assume "m < n"
        hence IA2: "prefixList (fe m) (fe n)" using IA(1) by simp
        have "prefixList (fe n) (fe (n+1))" using FE by simp
        thus "prefixList (fe m) (fe (Suc n))" using PrefixListTransitive 
          IA2 by simp
      qed
    qed
    thus "prefixList (fe m) (fe n)" by simp
  qed

  have AllArePrefixesTrace: "\<forall> m . \<forall> n > m . prefixList (ft m) (ft n)"
  proof(clarify)
    fix m::nat and n::nat
    assume MLessN: "m < n"
    have "prefixList (ft m) (ft n)" using MLessN
    proof(induct n, simp)
      fix n
      assume IA: "(m < n) \<Longrightarrow> (prefixList (ft m) (ft n))" "m < (Suc n)"
      have "m = n \<or> m < n" using IA(2) by (metis less_SucE)
      thus "prefixList (ft m) (ft (Suc n))"
      proof(cases "m = n", auto)
        show "prefixList (ft n) (ft (Suc n))" using FE by simp
      next
        assume "m < n"
        hence IA2: "prefixList (ft m) (ft n)" using IA(1) by simp
        have "prefixList (ft n) (ft (n+1))" using FE by simp
        thus "prefixList (ft m) (ft (Suc n))" using PrefixListTransitive 
          IA2 by simp
      qed
    qed
    thus "prefixList (ft m) (ft n)" by simp
  qed

  have Length: "\<forall> n . length (fe n) \<ge> n + 1" 
  proof(clarify)
    fix n
    show "length (fe n) \<ge> n + 1" 
    proof(induct n, simp add: FE(1))
      fix n
      assume IH: "(n + (1::nat)) \<le> (length (fe n))"
      have "length (fe (n+1)) \<ge> length (fe n) + 1" using FE(3) 
        PrefixListMonotonicity
        by (metis Suc_eq_plus1 Suc_le_eq)
      thus "(Suc n) + (1::nat) \<le> (length (fe (Suc n)))" using IH by auto
    qed
  qed

  have AllExecsFromInit: "\<forall> n . \<forall> n0 < length (fe n) . 
    reachable cfg ((fe n) ! n0)"
  proof(clarify)
    fix n::nat and n0::nat
    assume "n0 < length (fe n)"
    thus "reachable cfg ((fe n) ! n0)"
    proof(cases "0 = n", auto)
      assume N0Less: "n0 < length (fe 0)"
      have NoStep: "reachable cfg cfg" using reachable.simps by blast 
      have "length (fe 0) = 1" using FE(1) by simp
      hence N0Zero: "n0 = 0" using N0Less FE by simp
      hence "(fe 0) ! n0 = cfg" using FE(1) by simp
      thus "reachable cfg ((fe 0) ! n0)" using FE(1) NoStep N0Zero by simp
    next
      assume NNotZero: "0 < n" "n0 < (length (fe n))"
      have ZeroCfg: "(fe 0) = [cfg]" using FE by simp
      have "prefixList (fe 0) (fe n)" using AllArePrefixesExec NNotZero 
        by simp
      hence PrList: "prefixList [cfg] (fe n)" using ZeroCfg by simp
      have CfgFirst: "cfg = (fe n) ! 0"
        using prefixList.cases[OF PrList]
        by (metis (full_types) ZeroCfg list.distinct(1) nth_Cons_0)
      have "reachable ((fe n) ! 0) ((fe n) ! n0)"
        using execution.ReachableInExecution FE NNotZero(2) by (metis le0)
      thus "(reachable cfg ((fe n) ! n0))" using assms CfgFirst by simp
    qed
  qed

  have NoDecided: "(\<forall> n n0 v . (n0 < length (fe n)) 
                  \<longrightarrow> \<not> vDecided v ((fe n) ! n0))" 
  proof(clarify)
    fix n n0 v
    assume AssmNoDecided: "n0 < length (fe n)" 
      "initReachable ((fe n) ! n0)"
      "0 < (msgs ((fe n) ! n0) <\<bottom>, outM v>)"
    have LastNonUniform: "nonUniform (last (fe n))" using FE by simp
    have LastIsLastIndex: "\<And> l . l \<noteq> [] \<longrightarrow> last l = l ! ((length l) - 1)" 
      by (metis last_conv_nth)
    have Fou: "n0 \<le> length (fe n) - 1" using AssmNoDecided by simp
    have FeNNotEmpty:"fe n \<noteq> []" using FE(1) AllArePrefixesExec 
      by (metis AssmNoDecided(1) less_nat_zero_code list.size(3))
    hence Fou2: "length (fe n) - 1 < length (fe n)" by simp
    have "last (fe n) = (fe n) ! (length (fe n) - 1)" 
      using LastIsLastIndex FeNNotEmpty by auto
    have LastNonUniform: "nonUniform (last (fe n))" using FE by simp 
    have "reachable ((fe n) ! n0) ((fe n) ! (length (fe n) - 1))" 
      using FE execution.ReachableInExecution Fou Fou2 by metis
    hence N0ToLast: "reachable ((fe n) ! n0) (last (fe n))" 
      using LastIsLastIndex[of "fe n"] FeNNotEmpty by simp
    hence LastVDecided: "vDecided v (last (fe n))" 
      using NoOutMessageLoss[of "((fe n) ! n0)" "(last (fe n))"] 
        AssmNoDecided
      by (simp,
        metis LastNonUniform le_neq_implies_less less_nat_zero_code neq0_conv)

    have AllAgree: "\<forall> cfg' . reachable (last (fe n)) cfg' 
      \<longrightarrow> agreement cfg'" 
    proof(clarify)
      fix cfg'
      assume LastToNext: "reachable (last (fe n)) cfg'"
      hence "reachable cfg  ((fe n) ! (length (fe n) - 1))" 
        using AllExecsFromInit AssmNoDecided(1) by auto
      hence "reachable cfg (last (fe n))" using LastIsLastIndex[of "fe n"] 
        FeNNotEmpty by simp
      hence FirstToLast: "reachable cfg cfg'" using initReachable_def Cfg 
        LastToNext ReachableTrans by blast
      hence "agreementInit cfg cfg'" using Agreement by simp
      hence "\<forall>v1. (<\<bottom>, outM v1> \<in># msgs cfg') \<longrightarrow> (\<forall>v2. (<\<bottom>, outM v2> \<in># 
        msgs cfg') \<longleftrightarrow> v2 = v1)"
        using Cfg FirstToLast
        by (simp add: agreementInit_def)
      thus "agreement cfg'" by (simp add: agreement_def)
    qed
    thus "False" using NonUniformImpliesNotDecided LastNonUniform 
      PseudoTermination LastVDecided by simp
  qed

  have Termination: "terminationFLP fe ft" using assms(1)[OF FE(2)] .

  hence AllDecideOrCrash: 
    "\<forall>p. \<exists>n . 
       (\<exists> i0 < length (ft n) . \<exists>b. 
          (<\<bottom>, outM b> \<in># 
            sends p (states (fe n ! i0) p) (unpackMessage (ft n ! i0))) 
          \<and> isReceiverOf p (ft n ! i0)) 
      \<or> (\<forall> n1 > n . \<forall> m \<in> (set (drop (length (ft n)) (ft n1))) .
          \<not> isReceiverOf p m)"
    using FE(2)
    unfolding terminationFLP_def fairInfiniteExecution_def 
    by blast

  have "\<forall> p . \<exists> n . (\<forall> n1 > n . \<forall> m \<in> (set (drop (length (ft n)) (ft n1))) .
    \<not> isReceiverOf p m)"
  proof(clarify)
    fix p
    from AllDecideOrCrash have
    "\<exists> n . 
       (\<exists> i0 < length (ft n) . \<exists>b. 
        (<\<bottom>, outM b> \<in># sends p (states (fe n ! i0) p) (unpackMessage (ft n ! i0))) 
       \<and> isReceiverOf p (ft n ! i0)) 
      \<or> (\<forall> n1 > n . \<forall> m \<in> (set (drop (length (ft n)) (ft n1))). 
        \<not> isReceiverOf p m)" by simp
    hence "(\<exists> n . \<exists> i0 < length (ft n) . 
         (\<exists>b. (<\<bottom>, outM b> \<in># 
            sends p (states (fe n ! i0) p) (unpackMessage (ft n ! i0))) 
          \<and> isReceiverOf p (ft n ! i0)))
         \<or> (\<exists> n .\<forall> n1 > n . \<forall> m \<in> (set (drop (length (ft n)) (ft n1))) .
           \<not> isReceiverOf p m)" by blast
    thus "\<exists>n. (\<forall>n1>n. (\<forall> m \<in> (set (drop (length (ft n)) (ft n1))).
      (\<not> (isReceiverOf p m))))"
    proof(elim disjE, auto)
      fix n i0 b
      assume DecidingPoint:
        "i0 < length (ft n)"
        "isReceiverOf p (ft n ! i0)"
        "<\<bottom>, outM b> \<in># sends p (states (fe n ! i0) p) (unpackMessage (ft n ! i0))"
      have "i0 < length (fe n) - 1"
        using DecidingPoint(1)
        by (metis (no_types) FE(3) execution.length) 
      hence StepN0: "((fe n) ! i0) \<turnstile> ((ft n) ! i0) \<mapsto> ((fe n) ! (i0 + 1))" 
        using FE by (metis execution.step)
      hence "msgs ((fe n) ! (i0 + 1)) <\<bottom>, outM b> 
        = (msgs ((fe n) ! i0) <\<bottom>, outM b>) +
        (sends p (states ((fe n) ! i0) p) 
        (unpackMessage ((ft n) ! i0)) <\<bottom>, outM b>)" 
        using DecidingPoint(2) OutOnlyGrowing[of "(fe n) ! i0" "(ft n) ! i0"
          "(fe n) ! (i0 + 1)" "p"] 
        by auto
      hence "(sends p (states ((fe n) ! i0) p) 
        (unpackMessage ((ft n) ! i0)) <\<bottom>, outM b>) 
        \<le> msgs ((fe n) ! (i0 + 1)) <\<bottom>, outM b>" 
        using asynchronousSystem.steps_def by auto
      hence OutMsgEx: "0 < msgs ((fe n) ! (i0 + 1)) <\<bottom>, outM b>" 
        using asynchronousSystem.steps_def DecidingPoint(3) by auto
      have "(i0 + 1) < length (fe n)"
        using DecidingPoint(1) \<open>i0 < length (fe n) - 1\<close> by auto
      hence "initReachable ((fe n) ! (i0 + 1))" 
        using AllExecsFromInit Cfg(1) 
        by (metis asynchronousSystem.initReachable_def)
      hence Decided: "vDecided b ((fe n) ! (i0 + 1))" using OutMsgEx 
        by auto
      have "i0 + 1 < length (fe n)" using DecidingPoint(1) 
        by (metis \<open>(((i0::nat) + (1::nat)) < (length (
          (fe::(nat \<Rightarrow> ('p, 'v, 's) configuration list)) (n::nat))))\<close>)
      hence "\<not> vDecided b ((fe n) ! (i0 + 1))" using NoDecided by auto
      hence "False" using Decided by auto
      thus "\<exists>n. (\<forall>n1>n. (\<forall> m \<in> (set (drop (length (ft n)) (ft n1))). 
        (\<not> (isReceiverOf p m))))" by simp
    qed
  qed
  hence "\<exists> (crashPoint::'p \<Rightarrow> nat) . 
    \<forall> p . \<exists>  n . crashPoint p = n \<and> (\<forall> n1 > n . \<forall> m \<in> (set (drop 
    (length (ft n)) (ft n1))) . (\<not> isReceiverOf p m))" by metis  
  then obtain crashPoint where CrashPoint:
    "\<forall> p . (\<forall> n1 > (crashPoint p) . \<forall> m \<in> (set (drop (length 
    (ft (crashPoint p))) (ft n1))) . (\<not> isReceiverOf p m))"
    by blast
  define limitSet where "limitSet = {crashPoint p | p . p \<in> Proc}"
  have "finite {p. p \<in> Proc}" using finiteProcs by simp
  hence "finite limitSet" using limitSet_def finite_image_set[] by blast
  hence "\<exists> limit . \<forall> l \<in> limitSet . l < limit" using 
    finite_nat_set_iff_bounded by auto
  hence "\<exists> limit . \<forall> p . (crashPoint p) < limit" using limitSet_def by auto
  then obtain limit where Limit: "\<forall> p . (crashPoint p) < limit" by blast
  define lengthLimit where "lengthLimit = length (ft limit) - 1"
  define lateMessage where "lateMessage = last (ft limit)"
  hence "lateMessage = (ft limit) ! (length (ft limit) - 1)" 
    by (metis AllArePrefixesTrace Limit last_conv_nth less_nat_zero_code 
      list.size(3) PrefixListMonotonicity)
  hence LateIsLast: "lateMessage = (ft limit) ! lengthLimit" 
  using lateMessage_def lengthLimit_def by auto

  have "\<exists> p . isReceiverOf p lateMessage" 
  proof(rule ccontr)
    assume "\<not> (\<exists>(p::'p). (isReceiverOf p lateMessage))"
    hence IsOutMsg: "\<exists> v . lateMessage = <\<bottom>, outM v>"
      by (metis isReceiverOf.simps(1) isReceiverOf.simps(2) message.exhaust)
    have "execution trans sends start (fe limit) (ft limit)" using FE 
      by auto
    hence "length (fe limit) - 1 = length (ft limit)"
      using execution.length by simp
    hence "lengthLimit < length (fe limit) - 1" 
      using lengthLimit_def 
      by (metis (hide_lams, no_types) Length Limit One_nat_def Suc_eq_plus1
        Suc_le_eq diff_less 
        diffs0_imp_equal gr_implies_not0 less_Suc0 neq0_conv)
    hence "((fe limit) ! lengthLimit) \<turnstile> ((ft limit) ! lengthLimit) 
      \<mapsto> ((fe limit) ! (lengthLimit + 1))"
      using FE by (metis execution.step)
    hence "((fe limit) ! lengthLimit) \<turnstile> lateMessage \<mapsto> ((fe limit) ! 
      (lengthLimit + 1))"
      using LateIsLast by auto
    thus False using IsOutMsg steps_def by auto
  qed

  then obtain p where ReceiverOfLate: "isReceiverOf p lateMessage" by blast
  have "\<forall> n1 > (crashPoint p) . 
    \<forall> m \<in> (set (drop (length (ft (crashPoint p))) (ft n1))) . 
      (\<not> isReceiverOf p m)"
    using CrashPoint
    by simp
  hence NoMsgAfterLimit: "\<forall> m \<in> (set (drop (length (ft (crashPoint p))) 
    (ft limit))) . (\<not> isReceiverOf p m)"
    using Limit
    by auto
  have "lateMessage \<in> set (drop (length(ft (crashPoint p))) (ft limit))" 
  proof-
    have "crashPoint p < limit" using Limit by simp
    hence "prefixList (ft (crashPoint p)) (ft limit)" 
      using AllArePrefixesTrace by auto
    hence CrashShorterLimit: "length (ft (crashPoint p)) 
      < length (ft limit)" using PrefixListMonotonicity by auto
    hence "last (drop (length (ft (crashPoint p))) (ft limit)) 
      = last (ft limit)" by (metis last_drop)
    hence "lateMessage = last (drop (length (ft (crashPoint p))) 
      (ft limit))" using lateMessage_def by auto
    thus "lateMessage \<in> set (drop (length(ft (crashPoint p))) (ft limit))" 
      by (metis CrashShorterLimit drop_eq_Nil last_in_set not_le)
  qed
  
  hence "\<not> isReceiverOf p lateMessage" using NoMsgAfterLimit by auto
  thus "False" using ReceiverOfLate by simp
qed

end

end
