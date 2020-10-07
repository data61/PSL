section\<open>FLPSystem\<close>

text \<open>
  \file{FLPSystem} extends \file{AsynchronousSystem} with concepts of consensus
  and decisions. It develops a concept of non-uniformity regarding pending
  decision possibilities, where non-uniform configurations can always
  reach other non-uniform ones.
\<close>

theory FLPSystem
imports AsynchronousSystem ListUtilities
begin

subsection\<open>Locale for the FLP consensus setting\<close>

locale flpSystem =
  asynchronousSystem trans sends start    
    for trans :: "'p \<Rightarrow> 's \<Rightarrow> 'v messageValue \<Rightarrow>'s"
    and sends :: "'p \<Rightarrow> 's \<Rightarrow> 'v messageValue \<Rightarrow> ('p, 'v) message multiset"
    and start :: "'p \<Rightarrow> 's" +
assumes finiteProcs: "finite Proc"
    and minimalProcs: "card Proc \<ge> 2"
    and finiteSends: "finite {v. v \<in># (sends p s m)}"
    and noInSends: "sends p s m <p2, inM v> = 0"
begin

subsection\<open>Decidedness and uniformity of configurations\<close>

abbreviation vDecided ::
  "bool \<Rightarrow> ('p, 'v, 's) configuration \<Rightarrow> bool"
where
  "vDecided v cfg \<equiv> initReachable cfg \<and> (<\<bottom>, outM v> \<in># msgs cfg)"

abbreviation decided ::
  "('p, 'v, 's) configuration \<Rightarrow> bool"
where
  "decided cfg \<equiv> (\<exists>v . vDecided v cfg)"

definition pSilDecVal ::
  "bool \<Rightarrow> 'p \<Rightarrow> ('p, 'v, 's) configuration \<Rightarrow> bool"
where
  "pSilDecVal v p c \<equiv> initReachable c \<and> 
    (\<exists> c'::('p, 'v, 's) configuration . (withoutQReachable c {p} c') 
    \<and> vDecided v c')"

abbreviation pSilentDecisionValues ::
  "'p \<Rightarrow> ('p, 'v, 's) configuration \<Rightarrow> bool set" ("val[_,_]")
where 
  "val[p, c] \<equiv> {v. pSilDecVal v p c}"

definition vUniform ::
  "bool \<Rightarrow> ('p, 'v, 's) configuration \<Rightarrow> bool"
where 
  "vUniform v c \<equiv> initReachable c \<and> (\<forall>p. val[p,c] = {v})"

abbreviation nonUniform ::
  "('p, 'v, 's) configuration \<Rightarrow> bool"
where
  "nonUniform c \<equiv> initReachable c \<and>
    \<not>(vUniform False c) \<and> 
    \<not>(vUniform True c)"

subsection\<open>Agreement, validity, termination\<close>

text\<open>
  Völzer defines consensus in terms of the classical notions
  of agreement, validity, and termination. The proof then mostly applies a
  weakened notion of termination, which we refer to as ,,pseudo termination''.
\<close>

definition agreement ::
  "('p, 'v, 's) configuration \<Rightarrow> bool"
where 
  "agreement c \<equiv> 
    (\<forall>v1. (<\<bottom>, outM v1> \<in># msgs c) 
      \<longrightarrow> (\<forall>v2. (<\<bottom>, outM v2> \<in># msgs c) 
        \<longleftrightarrow> v2 = v1))"

definition agreementInit ::
  "('p, 'v, 's) configuration \<Rightarrow> ('p, 'v, 's) configuration \<Rightarrow> bool"
where 
  "agreementInit i c \<equiv> 
    initial i \<and> reachable i c \<longrightarrow> 
      (\<forall>v1. (<\<bottom>, outM v1> \<in># msgs c) 
        \<longrightarrow> (\<forall>v2. (<\<bottom>, outM v2> \<in># msgs c) 
          \<longleftrightarrow> v2 = v1))"

definition validity ::
  "('p, 'v, 's) configuration \<Rightarrow> ('p, 'v, 's) configuration \<Rightarrow> bool"
where
  "validity i c \<equiv>
    initial i \<and> reachable i c \<longrightarrow> 
      (\<forall>v. (<\<bottom>, outM v> \<in># msgs c) 
        \<longrightarrow> (\<exists>p. (<p, inM v> \<in># msgs i)))"

text\<open>
  The termination concept which is implied by the concept of "pseudo-consensus"
  in the paper.
\<close>
definition terminationPseudo ::
  "nat \<Rightarrow> ('p, 'v, 's) configuration \<Rightarrow> 'p set \<Rightarrow> bool"
where
  "terminationPseudo t c Q \<equiv> ((initReachable c \<and> card Q + t \<ge> card Proc) 
    \<longrightarrow> (\<exists>c'. qReachable c Q c' \<and> decided c'))"

subsection \<open>Propositions about decisions\<close>

text\<open>
  For every process \var{p} and every configuration that is reachable from an
  initial configuration (i.e. \isb{initReachable} \var{c}) we have
  $\var{val(p,c)} \neq \emptyset$.

  This follows directly from the definition of \var{val} and the definition of
  \isb{terminationPseudo}, which has to be assumed to ensure that there is a
  reachable configuration that is decided.
  
  \voelzer{Proposition 2(a)}
\<close>
lemma DecisionValuesExist:
fixes
  c :: "('p, 'v, 's) configuration" and
  p :: "'p" 
assumes
  Termination: "\<And>cc Q . terminationPseudo 1 cc Q" and
  Reachable: "initReachable c"      
shows
  "val[p,c] \<noteq> {}"  
proof -
  from Termination
    have "(initReachable c \<and> card Proc \<le> card (UNIV - {p}) + 1) 
      \<longrightarrow> (\<exists>c'. qReachable c (UNIV-{p}) c' \<and> initReachable c' 
      \<and> (\<exists>v. 0 < msgs c' <\<bottom>, outM v>))"
    unfolding terminationPseudo_def by simp
  with Reachable minimalProcs finiteProcs
    have "\<exists>c'. qReachable c (UNIV - {p}) c' \<and> initReachable c' 
    \<and> (\<exists>v. 0 < msgs c' <\<bottom>, outM v>)"
    unfolding terminationPseudo_def initReachable_def by simp
  thus ?thesis
    unfolding pSilDecVal_def 
    using Reachable by auto
qed

text\<open>
  The lemma \isb{DecidedImpliesUniform} proves that every \isb{vDecided}
  configuration \var{c} is also \isb{vUniform}. Völzer claims that this
  follows directly from the definitions of \isb{vDecided} and \isb{vUniform}.
  But this is not quite enough: One must also assume \isb{terminationPseudo}
  and \isb{agreement} for all reachable configurations.

  \voelzer{Proposition 2(b)}
\<close>
lemma DecidedImpliesUniform:
fixes
  c :: "('p, 'v, 's) configuration" and
  v :: "bool"
assumes
  AllAgree: "\<forall> cfg . reachable c cfg \<longrightarrow> agreement cfg" and
  Termination: "\<And>cc Q . terminationPseudo 1 cc Q" and
  VDec: "vDecided v c"
shows
  "vUniform v c"
  using AllAgree VDec unfolding agreement_def vUniform_def pSilDecVal_def 
proof simp 
  assume 
    Agree: "\<forall>cfg. reachable c cfg \<longrightarrow>
      (\<forall>v1. 0 < msgs cfg <\<bottom>, outM v1> 
      \<longrightarrow> (\<forall>v2. (0 < msgs cfg <\<bottom>, outM v2>) = (v2 = v1)))" and 
    vDec: "initReachable c \<and> 0 < msgs c <\<bottom>, outM v>"
  show 
    "(\<forall>p. {v. \<exists>c'. qReachable c (Proc - {p}) c' \<and> initReachable c' \<and> 
      0 < msgs c' <\<bottom>, outM v>} = {v})" 
  proof clarify
    fix p 
    have "val[p,c] \<noteq> {}" using Termination DecisionValuesExist vDec 
      by simp
    hence NotEmpty: "{v. \<exists>c'. qReachable c (UNIV - {p}) c' 
      \<and> initReachable c' \<and> 0 < msgs c' <\<bottom>, outM v>} \<noteq> {}" 
      using pSilDecVal_def by simp
    have U: "\<forall> u . u \<in> {v. \<exists>c'. qReachable c (UNIV - {p}) c' 
      \<and> initReachable c' \<and> 0 < msgs c' <\<bottom>, outM v>} \<longrightarrow> (u = v)" 
    proof clarify
      fix u c'
      assume "qReachable c (UNIV - {p}) c'" "initReachable c'"
      hence Reach: "reachable c c'" using QReachImplReach by simp
      from VDec have Msg: "0 < msgs c <\<bottom>, outM v>" by simp
      from Reach NoOutMessageLoss have 
        "msgs c <\<bottom>, outM v> \<le> msgs c' <\<bottom>, outM v>" by simp
      with Msg have VMsg: "0 < msgs c' <\<bottom>, outM v>" 
        using NoOutMessageLoss Reach by (metis less_le_trans)
      assume "0 < msgs c' <\<bottom>, outM u>"
      with Agree VMsg Reach show "u = v" by simp
    qed
    thus " {v. \<exists>c'. qReachable c (UNIV - {p}) c' \<and> initReachable c' \<and> 
      0 < msgs c' <\<bottom>, outM v>} = {v}" using NotEmpty U by auto  
  qed
qed

corollary NonUniformImpliesNotDecided:
fixes
  c :: "('p, 'v, 's) configuration" and
  v :: "bool"
assumes
  "\<forall> cfg . reachable c cfg \<longrightarrow> agreement cfg"
  "\<And>cc Q . terminationPseudo 1 cc Q"
  "nonUniform c"
  "vDecided v c"
shows
  "False"
using DecidedImpliesUniform[OF assms(1,2,4)] assms(3)
  by (cases v, simp_all)
      
text\<open>
  All three parts of Völzer's Proposition 3 consider a single step from an
  arbitrary \isb{initReachable} configuration \var{c} with a message
  $\var{msg}$ to a succeeding configuration \var{c'}.
\<close>

text\<open>
  The silent decision values of a process which is not active in a step only
  decrease or stay the same.
  
  This follows directly from the definitions and the transitivity of the
  reachability properties \isb{reachable} and \isb{qReachable}.

  \voelzer{Proposition 3(a)}
\<close>
lemma InactiveProcessSilentDecisionValuesDecrease:
fixes 
  p q :: 'p and
  c c' :: "('p, 'v, 's) configuration" and
  msg :: "('p, 'v) message"
assumes 
  "p \<noteq> q" and
  "c \<turnstile> msg \<mapsto> c'" and
  "isReceiverOf p msg" and
  "initReachable c"
shows 
  "val[q,c'] \<subseteq> val[q,c]"
proof(auto simp add: pSilDecVal_def assms(4))
  fix x cfg'
  assume 
    Msg: "0 < msgs cfg' <\<bottom>, outM x>" and 
    Cfg': "qReachable c' (Proc - {q}) cfg'"
  have "initReachable c'"
    using assms initReachable_def reachable.simps 
    by blast
  hence Init: "initReachable cfg'" 
    using Cfg' initReachable_def QReachImplReach[of c' "(Proc - {q})" cfg'] 
    ReachableTrans by blast
  have "p \<in> Proc - {q}"
    using assms by blast
  hence "qReachable c (Proc - {q}) c'"
    using assms qReachable.simps by metis
  hence "qReachable c (Proc - {q}) cfg'"
    using Cfg' QReachableTrans
    by blast
  with Msg Init show 
    "\<exists>c'a. qReachable c (Proc - {q}) c'a 
      \<and> initReachable c'a \<and> 
      0 < msgs c'a <\<bottom>, outM x>" by blast
qed

text\<open>
  ...while the silent decision values of the process which is active in
  a step may only increase or stay the same.
  
  This follows as stated in \cite{Voelzer} from the \emph{diamond property}
  for a reachable configuration and a single step, i.e. \isb{DiamondTwo},
  and in addition from the fact that output messages cannot get lost, i.e.
  \isb{NoOutMessageLoss}.

  \voelzer{Proposition 3(b)}
\<close>
lemma ActiveProcessSilentDecisionValuesIncrease :
fixes 
  p q :: 'p and
  c c' :: "('p, 'v, 's) configuration" and
  msg :: "('p, 'v) message"
assumes 
  "p = q" and
  "c \<turnstile> msg \<mapsto> c'" and
  "isReceiverOf p msg" and
  "initReachable c"
shows "val[q,c] \<subseteq> val[q,c']"
proof (auto simp add: pSilDecVal_def assms(4))
  from assms initReachable_def reachable.simps show "initReachable c'" 
    by meson
  fix x cv 
  assume Cv: "qReachable c (Proc - {q}) cv" "initReachable cv" 
    "0 < msgs cv <\<bottom>, outM x>" 
  have "\<exists>c'a. (cv \<turnstile> msg \<mapsto> c'a) \<and> qReachable c' (Proc - {q}) c'a" 
    using DiamondTwo Cv(1) assms 
    by blast
  then obtain c'' where C'': "(cv \<turnstile> msg \<mapsto> c'')" 
    "qReachable c' (Proc - {q}) c''" by auto
  with Cv(2) initReachable_def reachable.simps
    have Init: "initReachable c''" by blast
  have "reachable cv c''" using C''(1) reachable.intros by blast      
  hence "msgs cv <\<bottom>, outM x> \<le> msgs c'' <\<bottom>, outM x>" using NoOutMessageLoss 
    by simp
  hence "0 < msgs c'' <\<bottom>, outM x>" using Cv(3) by auto
  thus "\<exists>c'a. qReachable c' (Proc - {q}) c'a  
    \<and> initReachable c'a \<and> 0 < msgs c'a <\<bottom>, outM x>" 
    using C''(2) Init by blast
qed

text\<open>
  As a result from the previous two propositions, the silent decision values
  of a process cannot go from {0} to {1} or vice versa in a step.

  This is a slightly more generic version of Proposition 3 (c) from
  \cite{Voelzer} since it is proven for both values, while Völzer is only
  interested in the situation starting with $\var{val(q,c) = \{0\}}$.

  \voelzer{Proposition 3(c)}
\<close>
lemma SilentDecisionValueNotInverting:
fixes 
  p q :: 'p and
  c c' :: "('p, 'v, 's) configuration" and
  msg :: "('p, 'v) message" and
  v :: bool
assumes 
  Val: "val[q,c] = {v}" and
  Step:  "c \<turnstile> msg \<mapsto> c'" and
  Rec:  "isReceiverOf p msg" and
  Init: "initReachable c"
shows 
  "val[q,c'] \<noteq> {\<not> v}"
proof(cases "p = q")
  case False
    hence "val[q,c'] \<subseteq> val[q,c]"
      using Step Rec InactiveProcessSilentDecisionValuesDecrease Init by simp
    with Val show "val[q,c'] \<noteq> {\<not> v}" by auto
  next
  case True
    hence "val[q,c] \<subseteq> val[q,c']"
      using Step Rec ActiveProcessSilentDecisionValuesIncrease Init by simp
    with Val show "val[q,c'] \<noteq> {\<not> v}" by auto
qed

subsection\<open>Towards a proof of FLP\<close>

text\<open>
  There is an \isb{initial} configuration that is \isb{nonUniform} under
  the assumption of \isb{validity}, \isb{agreement} and \isb{terminationPseudo}.

  The lemma is used in the proof of the main theorem to construct the
  \isb{non\-Uni\-form} and \isb{initial} configuration that leads to the
  final contradiction.

  \voelzer{Lemma 1}
\<close>
lemma InitialNonUniformCfg:
assumes
  Termination: "\<And>cc Q . terminationPseudo 1 cc Q" and
  Validity: "\<forall> i c . validity i c" and
  Agreement: "\<forall> i c . agreementInit i c"
shows 
  "\<exists> cfg . initial cfg \<and> nonUniform cfg" 
proof-
  obtain n::nat where N: "n = card Proc" by blast
  hence "\<exists> procList::('p list). length procList = n \<and> set procList = Proc 
    \<and> distinct procList" 
    using finiteProcs 
    by (metis distinct_card finite_distinct_list)  
  then obtain procList where 
    ProcList: "length procList = n" "set procList = Proc" 
      "distinct procList" by blast
  have AllPInProclist: "\<forall>p. \<exists>i<n. procList ! i = p"
    using ProcList N 
  proof auto
    fix p
    assume Asm: "set procList = Proc" "length procList = card Proc"
    have "p \<in> set procList" using ProcList by auto
    with Asm in_set_conv_nth
      show "\<exists>i<card Proc. procList ! i = p" by metis
  qed
  have NGr0: "n > 0"
    using N finiteProcs minimalProcs by auto
  define initMsg :: "nat \<Rightarrow> ('p, 'v) message \<Rightarrow> nat"
    where "initMsg ind m = (if \<exists>p. m = <p, inM (\<exists>i<ind. procList!i = p)> then 1 else 0)" for ind m
  define initCfgList
    where "initCfgList = map (\<lambda>ind. \<lparr>states = start, msgs = initMsg ind\<rparr>) [0..<(n+1)]"
  have InitCfgLength: "length initCfgList = n + 1" 
    unfolding initCfgList_def by auto
  have InitCfgNonEmpty: "initCfgList \<noteq> []"  
    unfolding initCfgList_def by auto
  hence InitCfgStart: "(\<forall>c \<in> set initCfgList. states c = start)" 
    unfolding initCfgList_def by auto
  have InitCfgSet: "set initCfgList = 
    {x. \<exists>ind < n+1. x = \<lparr>states = start, msgs = initMsg ind\<rparr>}"
    unfolding initCfgList_def
  proof auto
    fix ind
    assume "ind < n"
    hence "\<exists>inda<Suc n. inda = ind \<and> initMsg ind = initMsg inda" by auto
    thus "\<exists>inda<Suc n. initMsg ind = initMsg inda" by blast
  next
    fix ind
    assume Asm:
      "\<lparr>states = start, msgs = initMsg ind\<rparr> \<notin> (\<lambda>ind::nat. \<lparr>states = start, msgs = initMsg ind\<rparr>) ` {0..<n}"
      "ind < Suc n"
    hence "ind \<ge> n" by auto
    with Asm have "ind = n" by auto
    thus "initMsg ind = initMsg n" by auto
  qed
  have InitInitial: "\<forall>c \<in> set initCfgList . initial c"
    unfolding initial_def initCfgList_def initMsg_def using InitCfgStart
    by auto
  with InitCfgSet have InitInitReachable: 
    "\<forall> c \<in> set initCfgList . initReachable c"
    using reachable.simps
    unfolding initReachable_def
    by blast

  define c0 where "c0 = initCfgList ! 0"
  hence "c0 = \<lparr> states = start, msgs = initMsg 0 \<rparr>"
    using InitCfgLength nth_map_upt[of 0 "n+1" 0]
    unfolding initCfgList_def by auto
  hence MsgC0: "msgs c0 = (\<lambda>m. if \<exists>p. m = <p, inM False> then 1 else 0)"
    unfolding initMsg_def by simp
      
  define cN where "cN = initCfgList ! n"
  hence "cN = \<lparr> states = start, msgs = initMsg n\<rparr>"
    using InitCfgLength nth_map_upt[of n "n+1" 0]
    unfolding initCfgList_def
    by auto
  hence MsgCN: "msgs cN = (\<lambda>m. if \<exists>p. m = <p, inM True> then 1 else 0)"
    unfolding initMsg_def
    using AllPInProclist
    by auto

  have C0NotCN: "c0 \<noteq> cN"
  proof
    assume "c0 = cN"
    hence StrangeEq: "(\<lambda>m::('p, 'v) message.
        if \<exists>p. m = <p, inM False> then 1 else 0 :: nat) =
      (\<lambda>m. if \<exists>p. m = <p, inM True> then 1 else 0)"
      using InitCfgLength N minimalProcs MsgC0 MsgCN 
      unfolding c0_def cN_def by auto
    thus "False"
      by (metis message.inject(1) zero_neq_one)
  qed

  have C0NAreUniform: "\<And> cX . (cX = c0) \<or> (cX = cN) 
                      \<Longrightarrow> vUniform (cX = cN) cX" 
  proof-
    fix cX
    assume xIs0OrN: "(cX = c0) \<or> (cX = cN)"
    have xInit: "initial cX"
      using InitCfgLength InitCfgSet set_conv_nth[of initCfgList] xIs0OrN
      unfolding c0_def cN_def
      by (auto simp add: InitInitial)
    from Validity
      have COnlyReachesOneDecision:
        "\<forall> c . reachable cX c \<and> decided c \<longrightarrow> (vDecided (cX = cN) c)"
      unfolding validity_def initReachable_def
    proof auto
      fix c cfg0 v
      assume
        Validity: "(\<forall>i c. ((initial i) \<and> (reachable i c)) \<longrightarrow>
          (\<forall>v. (0 < msgs c (<\<bottom>, outM v>)) 
          \<longrightarrow> (\<exists>p. (0 < msgs i (<p, inM v>)))))" and
        OutMsg: "0 < msgs c <\<bottom>, outM v>" and
        InitCXReachable: "reachable cX c"
      thus "0 < msgs c <\<bottom>, outM (cX = cN)>"
        using xIs0OrN 
      proof (cases "v = (cX = cN)", simp)
        assume "v \<noteq> (cX = cN)"
        hence vDef: "v = (cX \<noteq> cN)" by auto
        with Validity InitCXReachable OutMsg xInit
          have ExistMsg: "\<exists>p. (0 < msgs cX (<p, inM (cX \<noteq> cN)>))" by auto
        with initMsg_def have False
          using xIs0OrN
          by (auto simp add: MsgC0 MsgCN C0NotCN) 
        thus "0 < msgs c <\<bottom>, outM cX = cN>" by simp
      qed
    qed
    have InitRInitC: "initReachable cX" using xInit InitialIsInitReachable 
      by auto
    have NoWrongDecs: "\<And> v p cc::('p, 'v, 's) configuration.
      qReachable cX (Proc - {p}) cc \<and> initReachable cc 
      \<and> 0 < msgs cc <\<bottom>, outM v> 
        \<Longrightarrow> v = (cX = cN)"
    proof clarify
      fix v p cc
      assume Asm: "qReachable cX (Proc - {p}) cc" "initReachable cc" 
      "0 < msgs cc <\<bottom>, outM v>"
      hence "reachable cX cc" "decided cc" using QReachImplReach by auto
      hence "\<not>(vDecided (cX \<noteq> cN) cc)"
        using COnlyReachesOneDecision Agreement Asm C0NotCN xInit xIs0OrN
        unfolding agreementInit_def by metis
      with Asm C0NotCN xIs0OrN show "v = (cX = cN)" 
      by (auto, metis (full_types) neq0_conv)
    qed
    have ExRightDecs: "\<And>p. \<exists>cc. qReachable (cX) (Proc - {p}) cc
      \<and> initReachable cc \<and> 0 < msgs cc <\<bottom>, outM (cX = cN)>"
    proof-
      fix p
      show "\<exists>cc::('p, 'v, 's) configuration.
           qReachable cX (Proc - {p}) cc \<and> initReachable cc 
           \<and> (0::nat) < msgs cc <\<bottom>, outM cX = cN>"
        using Termination[of "cX" "Proc - {p}"] finiteProcs minimalProcs 
          InitRInitC
        unfolding terminationPseudo_def
      proof auto
        fix cc v
        assume 
          Asm: "initReachable cX" "qReachable (cX) (Proc - {p}) cc"
          "initReachable cc"  "0 < msgs cc <\<bottom>, outM v>"
        with COnlyReachesOneDecision[rule_format, of "cc"] QReachImplReach
          have "0 < msgs cc <\<bottom>, outM cX = cN>" by auto
        with Asm
          show "\<exists>cc::('p, 'v, 's) configuration. 
            qReachable cX (Proc - {p}) cc
            \<and> initReachable cc \<and> (0::nat) < msgs cc <\<bottom>, outM cX = cN>" 
            by blast
      qed
    qed
    have ZeroinPSilent: "\<forall> p v . v \<in> val[p, cX] \<longleftrightarrow> v = (cX = cN)"
    proof clarify
      fix p v
      show "v \<in> val[p, cX] \<longleftrightarrow> v = (cX = cN)"
        unfolding pSilDecVal_def
        using InitRInitC xIs0OrN C0NotCN NoWrongDecs ExRightDecs by auto
    qed
    thus "vUniform (cX = cN) cX" using InitRInitC 
      unfolding vUniform_def by auto
  qed
  hence
    C0Is0Uniform: "vUniform False c0" and
    CNNot0Uniform: "\<not> vUniform False cN"
    using C0NAreUniform unfolding vUniform_def using C0NotCN by auto
  hence "\<exists> j < n. vUniform False (initCfgList ! j) 
    \<and> \<not>(vUniform False (initCfgList ! Suc j))"
    unfolding c0_def cN_def
    using NatPredicateTippingPoint
      [of n "\<lambda>x. vUniform False (initCfgList ! x)"] NGr0 by auto
  then obtain j
    where J: "j < n"
      "vUniform False (initCfgList ! j)"
      "\<not>(vUniform False (initCfgList ! Suc j))" by blast
  define pJ where "pJ = procList ! j"
  define cJ where "cJ = initCfgList ! j"
  hence cJDef: "cJ = \<lparr> states = start, msgs = initMsg j\<rparr>"
    using J(1) InitCfgLength nth_map_upt[of 0 "j- 1" 1] 
      nth_map_upt[of "j" "n + 1" 0]
    unfolding initCfgList_def 
    by auto
  hence MsgCJ: "msgs cJ = (\<lambda>m::('p, 'v) message.
    if \<exists>p::'p. m = <p, inM \<exists>i<j. procList ! i = p> then 1::nat
    else (0::nat))"
    unfolding initMsg_def
    using AllPInProclist
    by auto
  define cJ1 where "cJ1 = initCfgList ! (Suc j)"
  hence cJ1Def: "cJ1 = \<lparr> states = start, msgs = initMsg (Suc j)\<rparr>"
    using J(1) InitCfgLength nth_map_upt[of 0 "j" 1] 
    nth_map_upt[of "j + 1" "n + 1" 0]
    unfolding initCfgList_def 
    by auto
  hence MsgCJ1: "msgs cJ1 = (\<lambda>m::('p, 'v) message.
    if \<exists>p::'p. m = <p, inM \<exists>i<(Suc j). procList ! i = p> then 1::nat
    else (0::nat))"
    unfolding initMsg_def
    using AllPInProclist
    by auto
  have CJ1Init: "initial cJ1"
    using InitInitial[rule_format, of cJ1]  J(1) InitCfgLength 
    unfolding cJ1_def by auto
  hence CJ1InitR: "initReachable cJ1"
    using InitialIsInitReachable by simp
  have ValPj0: "False \<in> val[pJ, cJ]"
    using J(2) unfolding cJ_def vUniform_def by auto
  hence "\<exists>cc. vDecided False cc \<and> withoutQReachable cJ {pJ} cc"
    unfolding pSilDecVal_def by auto
  then obtain cc
    where CC: "vDecided False cc" "withoutQReachable cJ {pJ} cc"
    by blast
    hence "\<exists>Q. qReachable cJ Q cc \<and> Q = Proc - {pJ}" by blast
    then obtain ccQ where CCQ: "qReachable cJ ccQ cc" "ccQ = Proc - {pJ}" 
      by blast
  have StatescJcJ1: "states cJ = states cJ1" 
    using  cJ_def cJ1_def initCfgList_def  
    by (metis InitCfgLength InitCfgStart J(1) Suc_eq_plus1 Suc_mono 
      less_SucI nth_mem) 
  have Distinct: "\<And> i . distinct procList \<Longrightarrow> i<j 
    \<Longrightarrow> procList ! i = procList ! j \<Longrightarrow> False"
    by (metis J(1) ProcList(1) distinct_conv_nth less_trans 
       not_less_iff_gr_or_eq)
  have A: "msgs cJ (<pJ ,inM False>) = 1" 
    using pJ_def ProcList J(1) MsgCJ using Distinct by auto
  have B: "msgs cJ1 (<pJ ,inM True>) = 1" 
    using pJ_def ProcList J(1) MsgCJ1 by auto
  have C: "msgs cJ (<pJ ,inM True>) = 0" 
    using pJ_def ProcList J(1) MsgCJ using Distinct by auto  
  have D: "msgs cJ1 (<pJ ,inM False>) = 0" 
    using pJ_def ProcList J(1) MsgCJ1 by auto
  define msgsCJ' where
    "msgsCJ' m = (if m = (<pJ ,inM False>) \<or> m = (<pJ ,inM True>) then 0 else (msgs cJ) m)" for m
  have MsgsCJ': "msgsCJ' = ((msgs cJ) -# (<pJ ,inM False>))"
    using A C msgsCJ'_def by auto
  have AllOther: "\<forall> m . msgsCJ' m = ((msgs cJ1) -# (<pJ ,inM True>)) m"
    using B D MsgCJ1 MsgCJ  J(1) N ProcList AllPInProclist 
    unfolding msgsCJ'_def pJ_def
  proof(clarify)
    fix m
    show "(if m = <procList ! j, inM False> \<or> 
        m = <procList ! j, inM True> then 0 else msgs cJ m) 
      = (msgs cJ1 -# <procList ! j, inM True>) m"
    proof(cases "m = <procList ! j, inM False> \<or> m 
      = <procList ! j, inM True>",auto)
      assume "0 < (msgs cJ1 <procList ! j, inM False>)"
      thus False using D pJ_def by (metis less_nat_zero_code)
    next
      show "msgs cJ1 <procList ! j, inM True> \<le> Suc 0" 
        by (metis B One_nat_def order_refl pJ_def)
    next
      assume AssumpMJ: "m \<noteq> <procList ! j, inM False>" 
                       "m \<noteq> <procList ! j, inM True>"
      hence "(if \<exists>p. m = <p, inM \<exists>i<j. procList ! i = p> then 1 else 0)
           = (if \<exists>p. m = <p, inM \<exists>i<Suc j. procList ! i = p> then 1 else 0)"
        by (induct m, auto simp add: less_Suc_eq)
      thus "msgs cJ m = msgs cJ1 m"
        using MsgCJ MsgCJ1 by auto
    qed
  qed \<comment> \<open>of AllOther\<close>

  with MsgsCJ' have InitMsgs: "((msgs cJ) -# (<pJ ,inM False>)) 
    = ((msgs cJ1) -# (<pJ, inM True>))"
    by simp 
  hence F: "(((msgs cJ) -# (<pJ ,inM False>)) \<union># ({#<pJ, inM True>})) =
    (((msgs cJ1) -# (<pJ, inM True>))  \<union># ({#<pJ, inM True>}))" 
    by (metis (full_types))
  from B have One: "(((msgs cJ1) -# (<pJ, inM True>)) 
    \<union># ({#<pJ, inM True>})) <pJ, inM True> = 1" by simp
  with B have "\<forall> m :: ('p, 'v) message . (msgs cJ1) m 
    = (((msgs cJ1) -# (<pJ, inM True>))  \<union># 
    ({#<pJ, inM True>})) m" by simp
  with B have "(((msgs cJ1) -# (<pJ, inM True>))  \<union># ({#<pJ, inM True>})) 
    = (msgs cJ1)" by simp
  with F have InitMsgs: "(((msgs cJ) -# (<pJ ,inM False>)) 
    \<union># ({#<pJ, inM True>})) = (msgs cJ1)" 
    by simp
  define cc' where "cc' = \<lparr>states = (states cc),
    msgs = (((msgs cc) -# (<pJ,inM False>)) \<union># {# (<pJ, inM True>)})\<rparr>"
  have "\<lbrakk>qReachable cJ ccQ cc; ccQ = Proc - {pJ}; 
    (((msgs cJ) -# (<pJ ,inM False>)) \<union># ({#<pJ, inM True>})) 
      = (msgs cJ1); states cJ = states cJ1\<rbrakk> 
      \<Longrightarrow> withoutQReachable cJ1 {pJ} \<lparr>states = (states cc), 
      msgs = (((msgs cc) -# (<pJ,inM False>)) \<union># {# (<pJ, inM True>)}) \<rparr>"
    proof (induct rule: qReachable.induct)
      fix cfg1::"('p, 'v, 's) configuration" 
      fix Q
      assume 
        Assm: "(((msgs cfg1) -#(<pJ, inM False>)) \<union># {# <pJ, inM True> })
        = msgs cJ1" 
        "states cfg1 = states cJ1"
      hence CJ1: "cJ1 = \<lparr>states = states cfg1, 
        msgs = ((msgs cfg1) -# <pJ, inM False>) \<union># {# <pJ, inM True> }\<rparr>" by auto
      have "qReachable cJ1  (Proc - {pJ}) cJ1" using qReachable.simps 
        by blast
      with Assm show "qReachable cJ1 (Proc - {pJ})
        \<lparr>states = states cfg1, msgs = ((msgs cfg1) -# <pJ, inM False>) 
        \<union># {# <pJ, inM True> }\<rparr>" using CJ1 by blast
      fix cfg1 cfg2 cfg3 :: "('p, 'v, 's) configuration"
      fix msg
      assume Q: "Q = (Proc - {pJ})"
      assume "(((msgs cfg1) -# <pJ, inM False>) \<union># {# <pJ, inM True> }) 
        = (msgs cJ1)"
        "(states cfg1) = (states cJ1)"
        "Q = (Proc - {pJ}) \<Longrightarrow>
          (((msgs cfg1) -# <pJ, inM False>) \<union># {# <pJ, inM True> }) 
            = (msgs cJ1) 
          \<Longrightarrow> (states cfg1) = (states cJ1) 
          \<Longrightarrow> qReachable cJ1 (Proc - {pJ})
          \<lparr>states = (states cfg2),
          msgs = (((msgs cfg2) -# <pJ, inM False>) \<union># {# <pJ, inM True> })\<rparr>"
      with Q have Cfg2: 
        "qReachable cJ1 (Proc - {pJ}) \<lparr>states = (states cfg2),
        msgs = (((msgs cfg2) -# <pJ, inM False>) \<union># {# <pJ, inM True> })\<rparr>" 
        by simp
      assume "qReachable cfg1 Q cfg2" 
        "cfg2 \<turnstile> msg \<mapsto> cfg3"
        "\<exists>(p::'p)\<in>Q. (isReceiverOf p msg)"
      with Q have Step: "qReachable cfg1 (Proc - {pJ}) cfg2" 
        "cfg2 \<turnstile> msg \<mapsto> cfg3"
        "\<exists>(p::'p)\<in>(Proc - {pJ}). (isReceiverOf p msg)" by auto
      then obtain p where P: "p\<in>(Proc - {pJ})" "isReceiverOf p msg" by blast
      hence NotEq: "pJ \<noteq> p" by blast
      with UniqueReceiverOf[of "p" "msg" "pJ"] P(2) 
        have notRec: "\<not> (isReceiverOf pJ msg)" by blast
      hence MsgNoIn:"msg \<noteq>  <pJ, inM False> \<and> msg \<noteq>  <pJ, inM True>" 
        by auto 
      from Step(2) have "enabled cfg2 msg" using steps.simps 
        by (auto, cases msg, auto)
      hence MsgEnabled: "enabled \<lparr>states = (states cfg2),
        msgs = (((msgs cfg2) -# <pJ, inM False>) 
        \<union># {# <pJ, inM True> })\<rparr> msg" 
        using MsgNoIn by (simp add: enabled_def)
      have  "\<lparr>states = (states cfg2),
              msgs = (((msgs cfg2) -# <pJ, inM False>) 
              \<union># {# <pJ, inM True> })\<rparr>
                \<turnstile> msg \<mapsto> \<lparr>states = (states cfg3),
                msgs = (((msgs cfg3) -# <pJ, inM False>) 
                \<union># {# <pJ, inM True> })\<rparr>" 
      proof (cases msg) 
        fix p' bool
        assume MsgIn :"(msg = <p', inM bool>)"
        with noInSends MsgIn MsgNoIn MsgEnabled 
          show "\<lparr>states = (states cfg2),
          msgs = (((msgs cfg2) -# <pJ, inM False>) \<union># {# <pJ, inM True> })\<rparr>
            \<turnstile> msg \<mapsto> \<lparr>states = (states cfg3),
              msgs = (((msgs cfg3) -# <pJ, inM False>) 
              \<union># {# <pJ, inM True> })\<rparr>"  
          using steps.simps(1) Step(2) select_convs(2) select_convs(1) 
          by auto
      next
        fix bool   
        assume "(msg = <\<bottom>, outM bool>)"
        thus "\<lparr>states = (states cfg2),
          msgs = (((msgs cfg2) -# <pJ, inM False>) \<union># {# <pJ, inM True> })\<rparr>
            \<turnstile> msg \<mapsto> \<lparr>states = (states cfg3),
              msgs = (((msgs cfg3) -# <pJ, inM False>) 
              \<union># {# <pJ, inM True> })\<rparr>" 
          using steps_def Step(2) by auto
      next
        fix p v
        assume "(msg = <p, v>)"
        with noInSends MsgNoIn MsgEnabled show "\<lparr>states = (states cfg2),
          msgs = (((msgs cfg2) -# <pJ, inM False>) \<union># {# <pJ, inM True> })\<rparr>
            \<turnstile> msg \<mapsto> \<lparr>states = (states cfg3),
              msgs = (((msgs cfg3) -# <pJ, inM False>) 
              \<union># {# <pJ, inM True> })\<rparr>" 
        using steps.simps(1) Step(2) select_convs(2) select_convs(1) by auto
      qed            
      with Cfg2 Step(3) show "qReachable cJ1 (Proc - {pJ})
        \<lparr>states = (states cfg3),
          msgs = (((msgs cfg3) -# <pJ, inM False>) \<union># {# <pJ, inM True> })\<rparr>" 
        using
          qReachable.simps[of "cJ1" "(Proc - {pJ})" 
          "\<lparr>states = (states cfg3),
          msgs = (((msgs cfg3) -# <pJ, inM False>) 
          \<union># {# <pJ, inM True> })\<rparr>"] by auto
    qed
  with CCQ(1) CCQ(2) InitMsgs StatescJcJ1 have CC':
    "withoutQReachable cJ1 {pJ} \<lparr>states = (states cc), 
      msgs = (((msgs cc) -# (<pJ,inM False>)) 
      \<union># {# (<pJ, inM True>)}) \<rparr>" by auto
  with QReachImplReach CJ1InitR initReachable_def reachable.simps 
    ReachableTrans
    have "initReachable \<lparr>states = (states cc), 
      msgs = (((msgs cc) -# (<pJ,inM False>)) 
      \<union># {# (<pJ, inM True>)}) \<rparr>" by meson
  with CC' have "False \<in> val[pJ, cJ1]"
    unfolding pSilDecVal_def
    using CJ1InitR CC(1) select_convs(2) by auto
  hence "\<not>(vUniform True (cJ1))"
    unfolding vUniform_def
    using CJ1InitR by blast
  hence "nonUniform cJ1"
    using J(3) CJ1InitR unfolding cJ1_def by auto
  thus ?thesis
    using CJ1Init by blast
qed

text\<open>
  Völzer's Lemma 2 proves that for every process $p$ in the consensus setting 
  \isb{nonUniform} configurations can reach a configuration where the silent
  decision values of $p$ are True and False. This is key to the construction of
  non-deciding executions.

  \voelzer{Lemma 2}
\<close>
lemma NonUniformCanReachSilentBivalence:
fixes 
  p:: 'p and
  c:: "('p, 'v, 's) configuration"
assumes 
  NonUni: "nonUniform c" and
  PseudoTermination: "\<And>cc Q . terminationPseudo 1 cc Q" and
  Agree: "\<And> cfg . reachable c cfg \<longrightarrow> agreement cfg"
shows 
   "\<exists> c' . reachable c c' \<and> val[p,c'] = {True, False}"
proof(cases "val[p,c] = {True, False}")
  case True 
  have "reachable c c" using reachable.simps by metis
  thus ?thesis
    using True by blast
next
  case False
  hence notEq: "val[p,c] \<noteq> {True, False}" by simp
  from NonUni PseudoTermination DecisionValuesExist 
  have notE: "\<forall>q. val[q,c] \<noteq> {}" by simp  
  hence notEP: "val[p,c] \<noteq> {}" by blast
  have valType: "\<forall>q. val[q,c] \<subseteq> {True, False}" using pSilDecVal_def 
    by (metis (full_types) insertCI subsetI)
  hence "val[p,c] \<subseteq> {True, False}" by blast
  with notEq notEP  have "\<exists>b:: bool. val[p,c] = {b}" by blast
  then obtain b where B: "val[p,c] = {b}" by auto
  from NonUni vUniform_def have 
    NonUni: "(\<exists>q. val[q,c] \<noteq> {True}) \<and> (\<exists>q. val[q,c] \<noteq> {False})" by simp
  have Bool: "b = True \<or> b = False" by simp
  with NonUni have "\<exists>q. val[q,c] \<noteq> {b}" by blast
  then obtain q where Q: "val[q,c] \<noteq> {b}" by auto
  from notE valType 
  have "val[q,c] = {True} \<or> val[q,c] = {False} \<or> val[q,c] = {True, False}" 
    by auto
  with Bool Q have "val[q,c] = {\<not>b} \<or> val[q,c] = {b, \<not>b}" by blast
  hence "(\<not>b) \<in> val[q,c]" by blast
  with pSilDecVal_def 
  have "\<exists> c'::('p, 'v, 's) configuration . (withoutQReachable c {q} c') \<and>
    vDecided (\<not>b) c'" by simp
  then obtain c' where C': "withoutQReachable c {q} c'" "vDecided (\<not>b) c'" 
    by auto
  hence Reach: "reachable c c'" using QReachImplReach by simp
  have "\<forall> cfg . reachable c' cfg \<longrightarrow> agreement cfg" 
  proof clarify
    fix cfg
    assume "reachable c' cfg"
    with Reach have "reachable c cfg" 
      using ReachableTrans[of c c'] by simp
    with Agree show "agreement cfg" by simp
  qed      
  with PseudoTermination C'(2) DecidedImpliesUniform have "vUniform (\<not>b) c'" 
    by simp
  hence notB: "val[p,c'] = {\<not>b}" using vUniform_def by simp
  with Reach B show "\<exists> cfg. reachable c cfg \<and> val[p,cfg] = {True, False}" 
  proof(induct rule: reachable.induct, simp)
    fix cfg1 cfg2 cfg3 msg
    assume
      IV: "val[p,cfg1] = {b} \<Longrightarrow>
        val[p,cfg2] = {\<not> b} \<Longrightarrow>
          \<exists>cfg::('p, 'v, 's) configuration. reachable cfg1 cfg 
          \<and> val[p,cfg] = {True, False}" and
      Reach:  "reachable cfg1 cfg2" and
      Step: "cfg2 \<turnstile> msg \<mapsto> cfg3" and
      ValCfg1: "val[p,cfg1] = {b}" and
      ValCfg3: "val[p,cfg3] = {\<not> b}"
    from ValCfg1 have InitCfg1: "initReachable cfg1" 
      using pSilDecVal_def by auto
    from Reach InitCfg1 initReachable_def reachable.simps ReachableTrans
      have InitCfg2: "initReachable cfg2" by blast
    with PseudoTermination DecisionValuesExist 
    have notE: "\<forall>q. val[q,cfg2] \<noteq> {}" by simp
    have valType: "\<forall>q. val[q,cfg2] \<subseteq> {True, False}" using pSilDecVal_def
      by (metis (full_types) insertCI subsetI)
    from notE valType 
      have "val[p,cfg2] = {True} \<or> val[p,cfg2] = {False} 
        \<or> val[p,cfg2] = {True, False}" 
      by auto
    with Bool have Val: "val[p,cfg2] = {b} \<or> val[p,cfg2] = {\<not>b} 
      \<or> val[p,cfg2] = {True, False}" 
      by blast
    show "\<exists>cfg::('p, 'v, 's) configuration. reachable cfg1 cfg 
      \<and> val[p,cfg] = {True, False}" 
    proof(cases "val[p,cfg2] = {b}")
      case True
      hence B: "val[p,cfg2] = {b}" by simp
      from Step have RecOrOut: "\<exists>q. isReceiverOf q msg" by(cases msg, auto)
      then obtain q where Rec: "isReceiverOf q msg" by auto
      with B Step InitCfg2 SilentDecisionValueNotInverting 
      have "val[p,cfg3] \<noteq> {\<not>b}" by simp
      with ValCfg3 have "False" by simp
      thus "\<exists>cfg::('p, 'v, 's) configuration. reachable cfg1 cfg \<and> 
        val[p,cfg] = {True, False}" by simp
    next 
      case False
      with Val have Val: "val[p,cfg2] = {\<not>b} \<or> val[p,cfg2] = {True, False}" 
        by simp
      show "\<exists>cfg::('p, 'v, 's) configuration. reachable cfg1 cfg \<and> 
            val[p,cfg] = {True, False}" 
      proof(cases "val[p,cfg2] = {\<not>b}")
        case True
        hence "val[p,cfg2] = {\<not>b}" by simp
        with ValCfg1 IV show 
          "\<exists>cfg::('p, 'v, 's) configuration. 
          reachable cfg1 cfg \<and> val[p,cfg] = {True, False}" 
          by simp
      next
        case False
        with Val have "val[p,cfg2] = {True, False}" by simp
        with Reach have "reachable cfg1 cfg2 \<and> val[p,cfg2] = {True, False}" 
          by blast
        from this show "\<exists>cfg::('p, 'v, 's) configuration. 
          reachable cfg1 cfg \<and> val[p,cfg] = {True, False}" by blast
      qed
    qed
  qed
qed

end
end
