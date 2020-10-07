theory OneThirdRuleProof
imports OneThirdRuleDefs "../Reduction" "../Majorities"
begin

text \<open>
  We prove that \emph{One-Third Rule} solves the Consensus problem
  under the communication predicate defined above. The proof is
  split into proofs of the Integrity, Agreement, and Termination
  properties.
\<close>

subsection \<open>Proof of Integrity\<close>

text \<open>
  Showing integrity of the algorithm is a simple, if slightly tedious
  exercise in invariant reasoning. The following inductive invariant
  asserts that the values of the \<open>x\<close> and \<open>decide\<close> fields
  of the process states are limited to the \<open>x\<close> values present
  in the initial states since the algorithm does not introduce any
  new values.
\<close>

definition VInv where
  "VInv rho n \<equiv>
   let xinit = (range (x \<circ> (rho 0)))
   in  range (x \<circ> (rho n)) \<subseteq> xinit
     \<and> range (decide \<circ> (rho n)) \<subseteq> {None} \<union> (Some ` xinit)"

lemma vinv_invariant:
  assumes run:"HORun OTR_M rho HOs"
  shows "VInv rho n"
proof (induct n)
  from run show "VInv rho 0"
    by (simp add: HORun_eq HOinitConfig_eq OTR_HOMachine_def initState_def
                  OTR_initState_def VInv_def image_def)
next
  fix m
  assume ih: "VInv rho m"
  let ?xinit = "range (x \<circ> (rho 0))"
  have "range (x \<circ> (rho (Suc m))) \<subseteq> ?xinit"
  proof (clarsimp cong del: image_cong_simp)
    fix p
    from run
    have nxt: "OTR_nextState m p (rho m p) 
                        (HOrcvdMsgs OTR_M m p (HOs m p) (rho m))
                        (rho (Suc m) p)"
          (is "OTR_nextState _ _ ?st ?msgs ?st'")
     by (simp add: HORun_eq HOnextConfig_eq OTR_HOMachine_def nextState_def)
    show "x ?st' \<in> ?xinit"
    proof (cases "(2*N) div 3 < card (HOs m p)")
      case True
      hence HO: "HOs m p \<noteq> {}" by auto
      let ?MFRs = "{v. MFR ?msgs v}"
      have "Min ?MFRs \<in> ?MFRs"
      proof (rule Min_in)
        from HO have "?MFRs \<subseteq> (the \<circ> ?msgs)`(HOs m p)"
          by (auto simp: image_def intro: MFR_in_msgs)
        thus "finite ?MFRs" by (auto elim: finite_subset)
      next
        from MFR_exists show "?MFRs \<noteq> {}" by auto
      qed
      with HO have "\<exists>q \<in> HOs m p. Min ?MFRs = the (?msgs q)"
        by (intro MFR_in_msgs) auto
      hence "\<exists>q \<in> HOs m p. Min ?MFRs = x (rho m q)"
        by (auto simp: HOrcvdMsgs_def OTR_HOMachine_def OTR_sendMsg_def)
     moreover
      from True nxt have "x ?st' = Min ?MFRs"
        by (simp add: OTR_nextState_def HOrcvdMsgs_def)
     ultimately
        show ?thesis using ih by (auto simp: VInv_def image_def)
    next
      case False
      with nxt ih show ?thesis
        by (auto simp: OTR_nextState_def VInv_def HOrcvdMsgs_def Let_def)
    qed
  qed
  moreover
  have "\<forall>p. decide ((rho (Suc m)) p) \<in> {None} \<union> (Some ` ?xinit)"
  proof
    fix p
    from run
    have nxt: "OTR_nextState m p (rho m p) 
                        (HOrcvdMsgs OTR_M m p (HOs m p) (rho m))
                        (rho (Suc m) p)"
          (is "OTR_nextState _ _ ?st ?msgs ?st'")
      by (simp add: HORun_eq HOnextConfig_eq OTR_HOMachine_def nextState_def)
    show "decide ?st' \<in> {None} \<union> (Some ` ?xinit)"
    proof (cases "(2*N) div 3 < card {q. ?msgs q \<noteq> None}")
      assume HO: "(2*N) div 3 < card {q. ?msgs q \<noteq> None}"
      show ?thesis
      proof (cases "\<exists>v. TwoThirds ?msgs v")
        case True
        let ?dec = "\<some>v. TwoThirds ?msgs v"
        from True have "TwoThirds ?msgs ?dec" by (rule someI_ex)
        hence "HOV ?msgs ?dec \<noteq> {}" by (auto simp add: TwoThirds_def)
        then obtain q where "x (rho m q) = ?dec"
          by (auto simp: HOV_def HOrcvdMsgs_def OTR_HOMachine_def
                         OTR_sendMsg_def)
        from sym[OF this] nxt ih show ?thesis
          by (auto simp: OTR_nextState_def VInv_def image_def)
      next
        case False
        with HO nxt ih show ?thesis
          by (auto simp: OTR_nextState_def VInv_def HOrcvdMsgs_def image_def)
      qed
    next
      case False
      with nxt ih show ?thesis
        by (auto simp: OTR_nextState_def VInv_def image_def)
    qed
  qed
  hence "range (decide \<circ> (rho (Suc m))) \<subseteq> {None} \<union> (Some ` ?xinit)" by auto
  ultimately
  show "VInv rho (Suc m)" by (auto simp: VInv_def image_def)
qed

text \<open>
  Integrity is an immediate consequence.
\<close>
theorem OTR_integrity:
  assumes run:"HORun OTR_M rho HOs" and dec: "decide (rho n p) = Some v"
  shows "\<exists>q. v = x (rho 0 q)"
proof -
  let ?xinit = "range (x \<circ> (rho 0))"
  from run have "VInv rho n" by (rule vinv_invariant)
  hence "range (decide \<circ> (rho n)) \<subseteq> {None} \<union> (Some ` ?xinit)"
    by (auto simp: VInv_def Let_def)
  hence "decide ((rho n) p) \<in> {None} \<union> (Some ` ?xinit)"
    by (auto simp: image_def)
  with dec show ?thesis by auto
qed


subsection \<open>Proof of Agreement\<close>

text \<open>
  The following lemma \<open>A1\<close> asserts that if process \<open>p\<close> 
  decides in a round on a value \<open>v\<close> then more than $2/3$ of 
  all processes have \<open>v\<close> as their \<open>x\<close> value in their 
  local state.

  We show a few simple lemmas in preparation.
\<close>

lemma nextState_change:
  assumes "HORun OTR_M rho HOs"
      and "\<not> ((2*N) div 3 
              < card {q. (HOrcvdMsgs OTR_M n p (HOs n p) (rho n)) q \<noteq> None})"
  shows "rho (Suc n) p = rho n p"
  using assms
  by (auto simp: HORun_eq HOnextConfig_eq OTR_HOMachine_def
                 nextState_def OTR_nextState_def)

lemma nextState_decide:
  assumes run:"HORun OTR_M rho HOs"
  and chg: "decide (rho (Suc n) p) \<noteq> decide (rho n p)"
  shows "TwoThirds (HOrcvdMsgs OTR_M n p (HOs n p) (rho n))
                   (the (decide (rho (Suc n) p)))"
proof -
  from run
  have "OTR_nextState n p (rho n p)
                    (HOrcvdMsgs OTR_M n p (HOs n p) (rho n)) (rho (Suc n) p)"
    by (simp add: HORun_eq HOnextConfig_eq OTR_HOMachine_def nextState_def)
  with chg show ?thesis by (auto simp: OTR_nextState_def elim: someI)
qed

lemma A1:
  assumes run:"HORun OTR_M rho HOs"
  and dec: "decide (rho (Suc n) p) = Some v"
  and chg: "decide (rho (Suc n) p) \<noteq> decide (rho n p)" (is "decide ?st' \<noteq> decide ?st")
  shows "(2*N) div 3 < card { q . x (rho n q) = v }"
proof -
  from run chg
  have "TwoThirds (HOrcvdMsgs OTR_M n p (HOs n p) (rho n)) 
                  (the (decide ?st'))"
    (is "TwoThirds ?msgs _")
    by (rule nextState_decide)
  with dec have "TwoThirds ?msgs v" by simp
  hence "(2*N) div 3 < card { q . ?msgs q = Some v }"
    by (simp add: TwoThirds_def HOV_def)
  moreover
  have "{ q . ?msgs q = Some v } \<subseteq> { q . x (rho n q) = v }"
    by (auto simp: OTR_HOMachine_def OTR_sendMsg_def HOrcvdMsgs_def)
  hence "card { q . ?msgs q = Some v } \<le> card { q . x (rho n q) = v }"
    by (simp add: card_mono)
  ultimately
  show ?thesis by simp
qed


text \<open>
  The following lemma \<open>A2\<close> contains the crucial correctness argument:
  if more than $2/3$ of all processes send \<open>v\<close> and process \<open>p\<close>
  hears from more than $2/3$ of all processes then the \<open>x\<close> field of
  \<open>p\<close> will be updated to \<open>v\<close>.
\<close>

lemma A2:
  assumes run: "HORun OTR_M rho HOs"
  and HO: "(2*N) div 3
             < card { q . HOrcvdMsgs OTR_M n p (HOs n p) (rho n) q \<noteq> None }"
  and maj: "(2*N) div 3 < card { q . x (rho n q) = v }"
  shows "x (rho (Suc n) p) = v"
proof -
  from run 
  have nxt: "OTR_nextState n p (rho n p) 
                      (HOrcvdMsgs OTR_M n p (HOs n p) (rho n)) 
                      (rho (Suc n) p)"
        (is "OTR_nextState _ _ ?st ?msgs ?st'")
    by (simp add: HORun_eq HOnextConfig_eq OTR_HOMachine_def nextState_def)
  let ?HOVothers = "\<Union> { HOV ?msgs w | w . w \<noteq> v}"
  \<comment> \<open>processes from which @{text p} received values different from @{text v}\<close>

  have w: "card ?HOVothers \<le> N div 3"
  proof -
    have "card ?HOVothers \<le> card (UNIV - { q . x (rho n q) = v })"
      by (auto simp: HOV_def HOrcvdMsgs_def OTR_HOMachine_def OTR_sendMsg_def 
               intro: card_mono)
    also have "\<dots> = N - card { q . x (rho n q) = v }"
      by (auto simp: card_Diff_subset)
    also from maj have "\<dots> \<le> N div 3" by auto
    finally show ?thesis .
  qed

  have hov: "HOV ?msgs v = { q . ?msgs q \<noteq> None } - ?HOVothers"
    by (auto simp: HOV_def) blast

  have othHO: "?HOVothers \<subseteq> { q . ?msgs q \<noteq> None }"
    by (auto simp: HOV_def)

  txt \<open>Show that \<open>v\<close> has been received from more than $N/3$ processes.\<close>
  from HO have "N div 3 < card { q . ?msgs q \<noteq> None } - (N div 3)" 
    by auto
  also from w HO have "\<dots> \<le> card { q . ?msgs q \<noteq> None } - card ?HOVothers" 
    by auto
  also from hov othHO have "\<dots> = card (HOV ?msgs v)" 
    by (auto simp: card_Diff_subset)
  finally have HOV: "N div 3 < card (HOV ?msgs v)" .

  txt \<open>All other values are received from at most $N/3$ processes.\<close>
  have "\<forall>w. w \<noteq> v \<longrightarrow> card (HOV ?msgs w) \<le> card ?HOVothers"
    by (force intro: card_mono)
  with w have cardw: "\<forall>w. w \<noteq> v \<longrightarrow> card (HOV ?msgs w) \<le> N div 3" by auto

  txt \<open>In particular, \<open>v\<close> is the single most frequently received value.\<close>
  with HOV have "MFR ?msgs v" by (auto simp: MFR_def)

  moreover
  have "\<forall>w. w \<noteq> v \<longrightarrow> \<not>(MFR ?msgs w)"
  proof (auto simp: MFR_def not_le)
    fix w
    assume "w \<noteq> v"
    with cardw HOV have "card (HOV ?msgs w) < card (HOV ?msgs v)" by auto
    thus "\<exists>v. card (HOV ?msgs w) < card (HOV ?msgs v)" ..
  qed

  ultimately
  have mfrv: "{ w . MFR ?msgs w } = {v}" by auto

  have "card { q . ?msgs q = Some v } \<le> card { q . ?msgs q \<noteq> None }"
    by (auto intro: card_mono)
  with HO mfrv nxt show ?thesis by (auto simp: OTR_nextState_def)
qed

text \<open>
  Therefore, once more than two thirds of the processes hold \<open>v\<close>
  in their \<open>x\<close> field, this will remain true forever.
\<close>

lemma A3:
  assumes run:"HORun OTR_M rho HOs"
      and n: "(2*N) div 3 < card { q . x (rho n q) = v }" (is "?twothird n")
  shows "?twothird (n+k)"
proof (induct k)
  from n show "?twothird (n+0)" by simp
next
  fix m
  assume m: "?twothird (n+m)"
  have "\<forall>q. x (rho (n+m) q) = v \<longrightarrow> x (rho (n + Suc m) q) = v"
  proof (rule+)
    fix q
    assume q: "x ((rho (n+m)) q) = v"
    let ?msgs = "HOrcvdMsgs OTR_M (n+m) q (HOs (n+m) q) (rho (n+m))"
    show "x (rho (n + Suc m) q) = v"
    proof (cases "(2*N) div 3 < card { q . ?msgs q \<noteq> None }")
      case True
      from m have "(2*N) div 3 < card { q . x (rho (n+m) q) = v }" by simp
      with True run show ?thesis by (auto elim: A2)
    next
      case False
      with run q show ?thesis by (auto dest: nextState_change)
    qed
  qed
  hence "card {q. x (rho (n+m) q) = v} \<le> card {q. x (rho (n + Suc m) q) = v}"
    by (auto intro: card_mono)
  with m show "?twothird (n + Suc m)" by simp
qed


text \<open>
  It now follows that once a process has decided on some value \<open>v\<close>, 
  more than two thirds of all processes continue to hold \<open>v\<close> in
  their \<open>x\<close> field.
\<close>

lemma A4:
  assumes run: "HORun OTR_M rho HOs" 
  and dec: "decide (rho n p) = Some v" (is "?dec n")
  shows "\<forall>k. (2*N) div 3 < card { q . x (rho (n+k) q) = v }"
        (is "\<forall>k. ?twothird (n+k)")
using dec proof (induct n)
  \<comment> \<open>The base case is trivial since no process has decided\<close>
  assume "?dec 0" with run show "\<forall>k. ?twothird (0+k)"
    by (simp add: HORun_eq HOinitConfig_eq OTR_HOMachine_def 
                  initState_def OTR_initState_def)
next
  \<comment> \<open>For the inductive step, we assume that process @{text p} has decided on @{text v}.\<close>
  fix m
  assume ih: "?dec m \<Longrightarrow> \<forall>k. ?twothird (m+k)" and m: "?dec (Suc m)"
  show "\<forall>k. ?twothird ((Suc m) + k)"
  proof
    fix k
    have "?twothird (m + Suc k)"
    txt \<open>
      There are two cases to consider: if \<open>p\<close> had already decided on \<open>v\<close>
      before, the assertion follows from the induction hypothesis. Otherwise, the
      assertion follows from lemmas \<open>A1\<close> and \<open>A3\<close>.
\<close>
    proof (cases "?dec m")
      case True with ih show ?thesis by blast
    next
      case False
      with run m have "?twothird m" by (auto elim: A1)
      with run show ?thesis by (blast dest: A3)
    qed
    thus "?twothird ((Suc m) + k)" by simp
  qed
qed

text \<open>
  The Agreement property follows easily from lemma \<open>A4\<close>: if processes
  \<open>p\<close> and \<open>q\<close> decide values \<open>v\<close> and \<open>w\<close>,
  respectively, then more than two thirds of the processes must propose
  \<open>v\<close> and more than two thirds must propose \<open>w\<close>.
  Because these two majorities must have an intersection, we must have
  \<open>v=w\<close>.

  We first prove an ``asymmetric'' version of the agreement property before
  deriving the general agreement theorem.
\<close>


lemma A5:
  assumes run:"HORun OTR_M rho HOs"
  and p: "decide (rho n p) = Some v"
  and p': "decide (rho (n+k) p') = Some w"
  shows "v = w"
proof -
  from run p 
  have "(2*N) div 3 < card {q. x (rho (n+k) q) = v}" (is "_ < card ?V")
    by (blast dest: A4)
  moreover
  from run p'
  have "(2*N) div 3 < card {q. x (rho ((n+k)+0) q) = w}" (is "_ < card ?W")
    by (blast dest: A4)
  ultimately
  have "N < card ?V + card ?W" by auto
  then obtain proc where "proc \<in> ?V \<inter> ?W" by (auto dest: majorities_intersect)
  thus ?thesis by auto
qed

theorem OTR_agreement:
  assumes run:"HORun OTR_M rho HOs"
  and p: "decide (rho n p) = Some v"
  and p': "decide (rho m p') = Some w"
  shows "v = w"
proof (cases "n \<le> m")
  case True
  then obtain k where "m = n+k" by (auto simp add: le_iff_add)
  with run p p' show ?thesis by (auto elim: A5)
next
  case False
  hence "m \<le> n" by auto
  then obtain k where "n = m+k"  by (auto simp add: le_iff_add)
  with run p p' have "w = v" by (auto elim: A5)
  thus ?thesis ..
qed


subsection \<open>Proof of  Termination\<close>

text \<open>
  We now show that every process must eventually decide.

  The idea of the proof is to observe that the communication predicate
  guarantees the existence of two uniform rounds where every process hears
  from the same two-thirds majority of processes. The first such round
  serves to ensure that all \<open>x\<close> fields hold the same value, the
  second round copies that value into all decision fields.

  Lemma \<open>A2\<close> is instrumental in this proof.
\<close>

theorem OTR_termination:
  assumes run: "HORun OTR_M rho HOs"
      and commG: "HOcommGlobal OTR_M HOs"
  shows "\<exists>r v. decide (rho r p) = Some v"
proof -
  from commG obtain r0 \<Pi> where 
    pi: "\<forall>q. HOs r0 q = \<Pi>" and pic: "card \<Pi> > (2*N) div 3"
    by (auto simp: OTR_HOMachine_def OTR_commGlobal_def)
  let "?msgs q r" = "HOrcvdMsgs OTR_M r q (HOs r q) (rho r)"

  from run pi have "\<forall>p q. ?msgs q r0 = ?msgs p r0"
    by (auto simp: HORun_eq OTR_HOMachine_def HOrcvdMsgs_def OTR_sendMsg_def)
  then obtain \<mu> where "\<forall>q. ?msgs q r0 = \<mu>" by auto
  moreover
  from pi pic have "\<forall>p. (2*N) div 3 < card {q. ?msgs p r0 q \<noteq> None}"
    by (auto simp: HORun_eq HOnextConfig_eq HOrcvdMsgs_def)
  with run have "\<forall>q. x (rho (Suc r0) q) = Min {v . MFR (?msgs q r0) v}"
    by (auto simp: HORun_eq HOnextConfig_eq OTR_HOMachine_def 
                   nextState_def OTR_nextState_def)
  ultimately
  have "\<forall>q. x (rho (Suc r0) q) = Min {v . MFR \<mu> v}" by auto
  then obtain v where v:"\<forall>q. x (rho (Suc r0) q) = v" by auto

  have P:"\<forall>k. \<forall>q. x (rho (Suc r0+k) q) = v"
  proof
    fix k
    show "\<forall>q. x (rho (Suc r0+k) q) = v"
    proof (induct k)
      from v show "\<forall>q. x (rho (Suc r0+0) q) = v" by simp
    next
      fix k
      assume ih:"\<forall>q. x (rho (Suc r0 + k) q) = v"
      show "\<forall>q. x (rho (Suc r0 + Suc k) q) = v"
      proof
        fix q
        show "x (rho (Suc r0 + Suc k) q) = v"
        proof (cases "(2*N) div 3 < card { p . ?msgs q (Suc r0 + k) p \<noteq> None }")
          case True
          have "N > 0" by (rule finite_UNIV_card_ge_0) simp
          with ih 
          have "(2*N) div 3 < card { p . x (rho (Suc r0 + k) p) = v }" by auto
          with True run show ?thesis by (auto elim: A2)
        next
          case False
          with run ih show ?thesis by (auto dest: nextState_change)
        qed
      qed
    qed
  qed

  from commG obtain r0' \<Pi>'
    where r0': "r0' \<ge> Suc r0"
      and pi': "\<forall>q. HOs r0' q = \<Pi>'"
      and pic': "card \<Pi>' > (2*N) div 3"
    by (force simp: OTR_HOMachine_def OTR_commGlobal_def)
  from r0' P have v':"\<forall>q. x (rho r0' q) = v" by (auto simp: le_iff_add)

  from run 
  have "OTR_nextState r0' p (rho r0' p) (?msgs p r0') (rho (Suc r0') p)"
    by (simp add: HORun_eq HOnextConfig_eq OTR_HOMachine_def nextState_def)
  moreover 
  from pi' pic' have "(2*N) div 3 < card {q. (?msgs p r0') q \<noteq> None}"
    by (auto simp: HOrcvdMsgs_def OTR_sendMsg_def)
  moreover
  from pi' pic' v' have "TwoThirds (?msgs p r0') v"
    by (simp add: TwoThirds_def HOrcvdMsgs_def OTR_HOMachine_def 
                  OTR_sendMsg_def HOV_def)
  ultimately
  have "decide (rho (Suc r0') p) = Some (\<some>v. TwoThirds (?msgs p r0') v)"
    by (auto simp: OTR_nextState_def)
  thus ?thesis by blast
qed


subsection \<open>\emph{One-Third Rule} Solves Consensus\<close>

text \<open>
  Summing up, all (coarse-grained) runs of \emph{One-Third Rule} for
  HO collections that satisfy the communication predicate satisfy
  the Consensus property.
\<close>

theorem OTR_consensus:
  assumes run: "HORun OTR_M rho HOs" and commG: "HOcommGlobal OTR_M HOs"
  shows "consensus (x \<circ> (rho 0)) decide rho"
  using OTR_integrity[OF run] OTR_agreement[OF run] OTR_termination[OF run commG]
  by (auto simp: consensus_def image_def)

text \<open>
  By the reduction theorem, the correctness of the algorithm also follows
  for fine-grained runs of the algorithm. It would be much more tedious
  to establish this theorem directly.
\<close>

theorem OTR_consensus_fg:
  assumes run: "fg_run OTR_M rho HOs HOs (\<lambda>r q. undefined)"
      and commG: "HOcommGlobal OTR_M HOs"
  shows "consensus (\<lambda>p. x (state (rho 0) p)) decide (state \<circ> rho)"
    (is "consensus ?inits _ _")
proof (rule local_property_reduction[OF run consensus_is_local])
  fix crun
  assume crun: "CSHORun OTR_M crun HOs HOs (\<lambda>r q. undefined)"
     and init: "crun 0 = state (rho 0)"
  from crun have "HORun OTR_M crun HOs" by (unfold HORun_def SHORun_def)
  from this commG have "consensus (x \<circ> (crun 0)) decide crun" by (rule OTR_consensus)
  with init show "consensus ?inits decide crun" by (simp add: o_def)
qed


end
