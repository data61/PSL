theory LastVotingProof
imports LastVotingDefs "../Majorities" "../Reduction"
begin


subsection \<open>Preliminary Lemmas\<close>

text \<open>
  We begin by proving some simple lemmas about the utility functions
  used in the model of \emph{LastVoting}. We also specialize the induction
  rules of the generic CHO model for this particular algorithm.
\<close>

lemma timeStampsRcvdFinite:
  "finite {ts . \<exists>q v. (msgs::Proc \<rightharpoonup> 'val msg) q = Some (ValStamp v ts)}"
  (is "finite ?ts")
proof -
  have "?ts = stamp ` the ` msgs ` (valStampsRcvd msgs)"
    by (force simp add: valStampsRcvd_def image_def)
  thus ?thesis by auto
qed

lemma highestStampRcvd_exists:
  assumes nempty: "valStampsRcvd msgs \<noteq> {}"
  obtains p v where "msgs p = Some (ValStamp v (highestStampRcvd msgs))"
proof -
  let ?ts = "{ts . \<exists>q v. msgs q = Some (ValStamp v ts)}"
  from nempty have "?ts \<noteq> {}" by (auto simp add: valStampsRcvd_def)
  with timeStampsRcvdFinite
  have "highestStampRcvd msgs \<in> ?ts"
    unfolding highestStampRcvd_def by (rule Max_in)
  then obtain p v where "msgs p = Some (ValStamp v (highestStampRcvd msgs))"
    by (auto simp add: highestStampRcvd_def)
  with that show thesis .
qed

lemma highestStampRcvd_max:
  assumes "msgs p = Some (ValStamp v ts)"
  shows "ts \<le> highestStampRcvd msgs"
  using assms unfolding highestStampRcvd_def
  by (blast intro: Max_ge timeStampsRcvdFinite)

lemma phase_Suc:
  "phase (Suc r) = (if step r = 3 then Suc (phase r)
                   else phase r)"
  unfolding step_def phase_def by presburger

text \<open>
  Many proofs are by induction on runs of the LastVoting algorithm, and
  we derive a specific induction rule to support these proofs.
\<close>

lemma LV_induct:
  assumes run: "CHORun LV_M rho HOs coords"
  and init: "\<forall>p. CinitState LV_M p (rho 0 p) (coords 0 p) \<Longrightarrow> P 0"
  and step0: "\<And>r.
                  \<lbrakk> step r = 0; P r; phase (Suc r) = phase r; step (Suc r) = 1;
                    \<forall>p. next0 r p (rho r p)
                              (HOrcvdMsgs LV_M r p (HOs r p) (rho r))
                              (coords (Suc r) p)
                              (rho (Suc r) p) \<rbrakk>
                  \<Longrightarrow> P (Suc r)"
  and step1: "\<And>r.
                  \<lbrakk> step r = 1; P r; phase (Suc r) = phase r; step (Suc r) = 2;
                    \<forall>p. next1 r p (rho r p)
                              (HOrcvdMsgs LV_M r p (HOs r p) (rho r))
                              (coords (Suc r) p)
                              (rho (Suc r) p) \<rbrakk>
                  \<Longrightarrow> P (Suc r)"
  and step2: "\<And>r.
                  \<lbrakk> step r = 2; P r; phase (Suc r) = phase r; step (Suc r) = 3;
                    \<forall>p. next2 r p (rho r p)
                              (HOrcvdMsgs LV_M r p (HOs r p) (rho r))
                              (coords (Suc r) p)
                              (rho (Suc r) p) \<rbrakk>
                  \<Longrightarrow> P (Suc r)"
  and step3: "\<And>r.
                  \<lbrakk> step r = 3; P r; phase (Suc r) = Suc (phase r); step (Suc r) = 0;
                    \<forall>p. next3 r p (rho r p)
                              (HOrcvdMsgs LV_M r p (HOs r p) (rho r))
                              (coords (Suc r) p)
                              (rho (Suc r) p) \<rbrakk>
                  \<Longrightarrow> P (Suc r)"
  shows "P n"
proof (rule CHORun_induct[OF run])
  assume "CHOinitConfig LV_M (rho 0) (coords 0)"
  thus "P 0" by (auto simp add: CHOinitConfig_def init)
next
  fix r
  assume ih: "P r" 
    and nxt: "CHOnextConfig LV_M r (rho r) (HOs r) 
                                 (coords (Suc r)) (rho (Suc r))"
  have "step r \<in> {0,1,2,3}" by (auto simp add: step_def)
  thus "P (Suc r)"
  proof auto
    assume stp: "step r = 0"
    hence "step (Suc r) = 1" 
      by (auto simp add: step_def mod_Suc)
    with ih nxt stp show ?thesis
      by (intro step0)
         (auto simp: LV_CHOMachine_def CHOnextConfig_eq 
                     LV_nextState_def LV_sendMsg_def phase_Suc)
  next
    assume stp: "step r = Suc 0"
    hence "step (Suc r) = 2" 
      by (auto simp add: step_def mod_Suc)
    with ih nxt stp show ?thesis
      by (intro step1)
         (auto simp: LV_CHOMachine_def CHOnextConfig_eq 
                     LV_nextState_def LV_sendMsg_def phase_Suc)
  next
    assume stp: "step r = 2"
    hence "step (Suc r) = 3"
      by (auto simp add: step_def mod_Suc)
    with ih nxt stp show ?thesis
      by (intro step2)
         (auto simp: LV_CHOMachine_def CHOnextConfig_eq 
                     LV_nextState_def LV_sendMsg_def phase_Suc)
  next
    assume stp: "step r = 3"
    hence "step (Suc r) = 0"
      by (auto simp add: step_def mod_Suc)
    with ih nxt stp show ?thesis
      by (intro step3)
         (auto simp: LV_CHOMachine_def CHOnextConfig_eq 
                     LV_nextState_def LV_sendMsg_def phase_Suc)
  qed
qed

text \<open>
  The following rule similarly establishes a property of two successive
  configurations of a run by case distinction on the step that was executed.
\<close>

lemma LV_Suc:
  assumes run: "CHORun LV_M rho HOs coords"
  and step0: "\<lbrakk> step r = 0; step (Suc r) = 1; phase (Suc r) = phase r;
                \<forall>p. next0 r p (rho r p)
                          (HOrcvdMsgs LV_M r p (HOs r p) (rho r))
                          (coords (Suc r) p) (rho (Suc r) p) \<rbrakk>
              \<Longrightarrow> P r"
  and step1: "\<lbrakk> step r = 1; step (Suc r) = 2; phase (Suc r) = phase r;
                \<forall>p. next1 r p (rho r p)
                          (HOrcvdMsgs LV_M r p (HOs r p) (rho r))
                          (coords (Suc r) p) (rho (Suc r) p) \<rbrakk>
              \<Longrightarrow> P r"
  and step2: "\<lbrakk> step r = 2; step (Suc r) = 3; phase (Suc r) = phase r;
                \<forall>p. next2 r p (rho r p)
                          (HOrcvdMsgs LV_M r p (HOs r p) (rho r))
                          (coords (Suc r) p) (rho (Suc r) p) \<rbrakk>
              \<Longrightarrow> P r"
  and step3: "\<lbrakk> step r = 3; step (Suc r) = 0; phase (Suc r) = Suc (phase r);
                \<forall>p. next3 r p (rho r p)
                          (HOrcvdMsgs LV_M r p (HOs r p) (rho r))
                          (coords (Suc r) p) (rho (Suc r) p) \<rbrakk>
              \<Longrightarrow> P r"
  shows "P r"
proof -
  from run 
  have nxt: "CHOnextConfig LV_M r (rho r) (HOs r) 
                                  (coords (Suc r)) (rho (Suc r))"
    by (auto simp add: CHORun_eq)
  have "step r \<in> {0,1,2,3}" by (auto simp add: step_def)
  thus "P r"
  proof (auto)
    assume stp: "step r = 0"
    hence "step (Suc r) = 1" 
      by (auto simp add: step_def mod_Suc)
    with nxt stp show ?thesis
      by (intro step0)
         (auto simp: LV_CHOMachine_def CHOnextConfig_eq 
                     LV_nextState_def LV_sendMsg_def phase_Suc)
  next
    assume stp: "step r = Suc 0"
    hence "step (Suc r) = 2" 
      by (auto simp add: step_def mod_Suc)
    with nxt stp show ?thesis
      by (intro step1)
         (auto simp: LV_CHOMachine_def CHOnextConfig_eq 
                     LV_nextState_def LV_sendMsg_def phase_Suc)
  next
    assume stp: "step r = 2"
    hence "step (Suc r) = 3"
      by (auto simp add: step_def mod_Suc)
    with nxt stp show ?thesis
      by (intro step2)
         (auto simp: LV_CHOMachine_def CHOnextConfig_eq 
                     LV_nextState_def LV_sendMsg_def phase_Suc)
  next
    assume stp: "step r = 3"
    hence "step (Suc r) = 0"
      by (auto simp add: step_def mod_Suc)
    with nxt stp show ?thesis
      by (intro step3)
         (auto simp: LV_CHOMachine_def CHOnextConfig_eq 
                     LV_nextState_def LV_sendMsg_def phase_Suc)
  qed
qed

text \<open>
  Sometimes the assertion to prove talks about a specific process and follows
  from the next-state relation of that particular process. We prove corresponding 
  variants of the induction and case-distinction rules. When these variants are
  applicable, they help automating the Isabelle proof.
\<close>

lemma LV_induct':
  assumes run: "CHORun LV_M rho HOs coords"
  and init: "CinitState LV_M p (rho 0 p) (coords 0 p) \<Longrightarrow> P p 0"
  and step0: "\<And>r. \<lbrakk> step r = 0; P p r; phase (Suc r) = phase r; step (Suc r) = 1;
                     next0 r p (rho r p)
                           (HOrcvdMsgs LV_M r p (HOs r p) (rho r))
                           (coords (Suc r) p) (rho (Suc r) p) \<rbrakk>
                  \<Longrightarrow> P p (Suc r)"
  and step1: "\<And>r. \<lbrakk> step r = 1; P p r; phase (Suc r) = phase r; step (Suc r) = 2;
                     next1 r p (rho r p)
                           (HOrcvdMsgs LV_M r p (HOs r p) (rho r))
                           (coords (Suc r) p) (rho (Suc r) p) \<rbrakk>
                  \<Longrightarrow> P p (Suc r)"
  and step2: "\<And>r. \<lbrakk> step r = 2; P p r; phase (Suc r) = phase r; step (Suc r) = 3;
                     next2 r p (rho r p)
                           (HOrcvdMsgs LV_M r p (HOs r p) (rho r))
                           (coords (Suc r) p) (rho (Suc r) p) \<rbrakk>
                  \<Longrightarrow> P p (Suc r)"
  and step3: "\<And>r. \<lbrakk> step r = 3; P p r; phase (Suc r) = Suc (phase r); step (Suc r) = 0;
                     next3 r p (rho r p)
                           (HOrcvdMsgs LV_M r p (HOs r p) (rho r))
                           (coords (Suc r) p) (rho (Suc r) p) \<rbrakk>
                  \<Longrightarrow> P p (Suc r)"
  shows "P p n"
  by (rule LV_induct[OF run])
     (auto intro: init step0 step1 step2 step3)

lemma LV_Suc':
  assumes run: "CHORun LV_M rho HOs coords"
  and step0: "\<lbrakk> step r = 0; step (Suc r) = 1; phase (Suc r) = phase r;
                next0 r p (rho r p)
                      (HOrcvdMsgs LV_M r p (HOs r p) (rho r))
                      (coords (Suc r) p) (rho (Suc r) p) \<rbrakk>
              \<Longrightarrow> P p r"
  and step1: "\<lbrakk> step r = 1; step (Suc r) = 2; phase (Suc r) = phase r;
                next1 r p (rho r p)
                      (HOrcvdMsgs LV_M r p (HOs r p) (rho r))
                      (coords (Suc r) p) (rho (Suc r) p) \<rbrakk>
              \<Longrightarrow> P p r"
  and step2: "\<lbrakk> step r = 2; step (Suc r) = 3; phase (Suc r) = phase r;
                next2 r p (rho r p)
                      (HOrcvdMsgs LV_M r p (HOs r p) (rho r))
                      (coords (Suc r) p) (rho (Suc r) p) \<rbrakk>
              \<Longrightarrow> P p r"
  and step3: "\<lbrakk> step r = 3; step (Suc r) = 0; phase (Suc r) = Suc (phase r);
                next3 r p (rho r p)
                      (HOrcvdMsgs LV_M r p (HOs r p) (rho r))
                      (coords (Suc r) p) (rho (Suc r) p) \<rbrakk>
              \<Longrightarrow> P p r"
  shows "P p r"
  by (rule LV_Suc[OF run])
     (auto intro: step0 step1 step2 step3)


subsection \<open>Boundedness and Monotonicity of Timestamps\<close>

text \<open>
  The timestamp of any process is bounded by the current phase.
\<close>

lemma LV_timestamp_bounded:
  assumes run: "CHORun LV_M rho HOs coords"
  shows "timestamp (rho n p) \<le> (if step n < 2 then phase n else Suc (phase n))"
        (is "?P p n")
  by (rule LV_induct' [OF run, where P="?P"])
     (auto simp: LV_CHOMachine_def LV_initState_def 
                 next0_def next1_def next2_def next3_def)

text \<open>
  Moreover, timestamps can only grow over time.
\<close>

lemma LV_timestamp_increasing:
  assumes run: "CHORun LV_M rho HOs coords"
  shows "timestamp (rho n p) \<le> timestamp (rho (Suc n) p)"
    (is "?P p n" is "?ts \<le> _")
proof (rule LV_Suc'[OF run, where P="?P"])
  txt \<open>The case of \<open>next1\<close> is the only interesting one because the
    timestamp may change: here we use the previously established fact that
    the timestamp is bounded by the phase number.\<close>
  assume stp: "step n = 1"
     and nxt: "next1 n p (rho n p)
                     (HOrcvdMsgs LV_M n p (HOs n p) (rho n))
                     (coords (Suc n) p) (rho (Suc n) p)"
  from stp have "?ts \<le> phase n"
    using LV_timestamp_bounded[OF run, where n=n, where p=p] by auto
  with nxt show ?thesis by (auto simp add: next1_def)
qed (auto simp add: next0_def next2_def next3_def)

lemma LV_timestamp_monotonic:
  assumes run: "CHORun LV_M rho HOs coords" and le: "m \<le> n"
  shows "timestamp (rho m p) \<le> timestamp (rho n p)"
    (is "?ts m \<le> _")
proof -
  from le obtain k where k: "n = m+k" 
    by (auto simp add: le_iff_add)
  have "?ts m \<le> ?ts (m+k)" (is "?P k")
  proof (induct k)
    case 0 show "?P 0" by simp
  next
    fix k
    assume ih: "?P k"
    from run have "?ts (m+k) \<le> ?ts (m + Suc k)"
      by (auto simp add: LV_timestamp_increasing)
    with ih show "?P (Suc k)" by simp
  qed
  with k show ?thesis by simp
qed

text \<open>
  The following definition collects the set of processes whose timestamp
  is beyond a given bound at a system state.
\<close>

definition procsBeyondTS where
  "procsBeyondTS ts cfg \<equiv> { p . ts \<le> timestamp (cfg p) }"

text \<open>
  Since timestamps grow monotonically, so does the set of processes
  that are beyond a certain bound.
\<close>

lemma procsBeyondTS_monotonic:
  assumes run: "CHORun LV_M rho HOs coords"
      and p: "p \<in> procsBeyondTS ts (rho m)" and le: "m \<le> n"
  shows "p \<in> procsBeyondTS ts (rho n)"
proof -
  from p have "ts \<le> timestamp (rho m p)" (is "_ \<le> ?ts m")
    by (simp add: procsBeyondTS_def)
  moreover
  from run le have "?ts m \<le> ?ts n" by (rule LV_timestamp_monotonic)
  ultimately show ?thesis
    by (simp add: procsBeyondTS_def)
qed


subsection \<open>Obvious Facts About the Algorithm\<close>

text \<open>
  The following lemmas state some very obvious facts that follow
  ``immediately'' from the definition of the algorithm. We could
  prove them in one fell swoop by defining a big invariant, but it
  appears more readable to prove them separately.
\<close>

text \<open>
  Coordinators change only at step 3.
\<close>

lemma notStep3EqualCoord:
  assumes run: "CHORun LV_M rho HOs coords" and stp:"step r \<noteq> 3"
  shows "coord\<Phi> (rho (Suc r) p) = coord\<Phi> (rho r p)" (is "?P p r")
  by (rule LV_Suc'[OF run, where P="?P"])
     (auto simp: stp next0_def next1_def next2_def)

lemma coordinators:
assumes run: "CHORun LV_M rho HOs coords"
shows "coord\<Phi> (rho r p) = coords (4*(phase r)) p"
proof -
  let ?r0 = "(4*(phase r) - 1)"
  let ?r1 = "(4*(phase r))"
  have "coord\<Phi> (rho ?r1 p) = coords ?r1 p"
  proof (cases "phase r > 0")
    case False
    hence "phase r = 0" by auto
    with run show ?thesis
      by (auto simp: LV_CHOMachine_def CHORun_eq CHOinitConfig_def
                     LV_initState_def)
  next
    case True
    hence "step (Suc ?r0) = 0" by (auto simp: step_def)
    hence "step ?r0 = 3" by (auto simp: mod_Suc step_def)
    moreover
    from run 
    have "LV_nextState ?r0 p (rho ?r0 p)
                  (HOrcvdMsgs LV_M ?r0 p (HOs ?r0 p) (rho ?r0))
                  (coords (Suc ?r0) p) (rho (Suc ?r0) p)"
      by (auto simp: LV_CHOMachine_def CHORun_eq CHOnextConfig_eq)
    ultimately
    have nxt: "next3 ?r0 p (rho ?r0 p)
                      (HOrcvdMsgs LV_M ?r0 p (HOs ?r0 p) (rho ?r0))
                      (coords (Suc ?r0) p) (rho (Suc ?r0) p)"
      by (auto simp: LV_nextState_def)
    hence "coord\<Phi> (rho (Suc ?r0) p) = coords (Suc ?r0) p" 
      by (auto simp: next3_def)
    with True show ?thesis by auto
  qed
  moreover
  from run
  have "coord\<Phi> (rho (Suc (Suc (Suc ?r1))) p) = coord\<Phi> (rho ?r1 p)
        \<and> coord\<Phi> (rho (Suc (Suc ?r1)) p) = coord\<Phi> (rho ?r1 p)
        \<and> coord\<Phi> (rho (Suc ?r1) p) = coord\<Phi> (rho ?r1 p)"
    by (auto simp: notStep3EqualCoord step_def phase_def mod_Suc)
  moreover
  have "r \<in> {?r1, Suc ?r1, Suc (Suc ?r1), Suc (Suc (Suc ?r1))}"
    by (auto simp: step_def phase_def mod_Suc)
  ultimately
  show ?thesis by auto
qed

text \<open>
  Votes only change at step 0.
\<close>

lemma notStep0EqualVote [rule_format]:
  assumes run: "CHORun LV_M rho HOs coords"
  shows "step r \<noteq> 0 \<longrightarrow> vote (rho (Suc r) p) = vote (rho r p)" (is "?P p r")
  by (rule LV_Suc'[OF run, where P="?P"])
     (auto simp: next0_def next1_def next2_def next3_def)

text \<open>
  Commit status only changes at steps 0 and 3.
\<close>

lemma notStep03EqualCommit [rule_format]:
  assumes run: "CHORun LV_M rho HOs coords"
  shows "step r \<noteq> 0 \<and> step r \<noteq> 3 \<longrightarrow> commt (rho (Suc r) p) = commt (rho r p)"
        (is "?P p r")
  by (rule LV_Suc'[OF run, where P="?P"])
     (auto simp: next0_def next1_def next2_def next3_def)

text \<open>
  Timestamps only change at step 1.
\<close>

lemma notStep1EqualTimestamp [rule_format]:
  assumes run: "CHORun LV_M rho HOs coords"
  shows "step r \<noteq> 1 \<longrightarrow> timestamp (rho (Suc r) p) = timestamp (rho r p)"
        (is "?P p r")
  by (rule LV_Suc'[OF run, where P="?P"])
     (auto simp: next0_def next1_def next2_def next3_def)

text \<open>
  The \<open>x\<close> field only changes at step 1.
\<close>

lemma notStep1EqualX [rule_format]:
  assumes run: "CHORun LV_M rho HOs coords"
  shows "step r \<noteq> 1 \<longrightarrow> x (rho (Suc r) p) = x (rho r p)" (is "?P p r")
  by (rule LV_Suc'[OF run, where P="?P"])
     (auto simp: next0_def next1_def next2_def next3_def)

text \<open>
  A process $p$ has its \<open>commt\<close> flag set only if the following conditions hold:
  \begin{itemize}
  \item the step number is at least $1$,
  \item $p$ considers itself to be the coordinator,
  \item $p$ has a non-null \<open>vote\<close>,
  \item a majority of processes consider $p$ as their coordinator.
  \end{itemize}
\<close>

lemma commitE:
  assumes run: "CHORun LV_M rho HOs coords" and cmt: "commt (rho r p)"
  and conds: "\<lbrakk> 1 \<le> step r; coord\<Phi> (rho r p) = p; vote (rho r p) \<noteq> None;
                card {q . coord\<Phi> (rho r q) = p} > N div 2
              \<rbrakk> \<Longrightarrow> A"
  shows "A"
proof -
  have "commt (rho r p) \<longrightarrow> 
          1 \<le> step r
        \<and> coord\<Phi> (rho r p) = p
        \<and> vote (rho r p) \<noteq> None
        \<and> card {q . coord\<Phi> (rho r q) = p} > N div 2"
    (is "?P p r" is "_ \<longrightarrow> ?R r")
  proof (rule LV_induct'[OF run, where P="?P"])
    \<comment> \<open>the only interesting step is step 0\<close>
    fix n
    assume nxt: "next0 n p (rho n p) (HOrcvdMsgs LV_M n p (HOs n p) (rho n))
                           (coords (Suc n) p) (rho (Suc n) p)"
       and ph: "phase (Suc n) = phase n" 
       and stp: "step n = 0" and stp': "step (Suc n) = 1"
       and ih: "?P p n"
    show "?P p (Suc n)"
    proof
      assume cm': "commt (rho (Suc n) p)"
      from stp ih have cm: "\<not> commt (rho n p)" by simp
      with nxt cm'
      have "coord\<Phi> (rho n p) = p
            \<and> vote (rho (Suc n) p) \<noteq> None 
            \<and> card (valStampsRcvd (HOrcvdMsgs LV_M n p (HOs n p) (rho n)))
                 > N div 2"
        by (auto simp add: next0_def)
      moreover
      from stp 
      have "valStampsRcvd (HOrcvdMsgs LV_M n p (HOs n p) (rho n))
             \<subseteq> {q . coord\<Phi> (rho n q) = p}"
        by (auto simp: valStampsRcvd_def LV_CHOMachine_def
                       HOrcvdMsgs_def  LV_sendMsg_def send0_def)
      hence "card (valStampsRcvd (HOrcvdMsgs LV_M n p (HOs n p)  (rho n)))
              \<le> card {q . coord\<Phi> (rho n q) = p}"
        by (auto intro: card_mono)
      moreover
      note stp stp' run
      ultimately
      show "?R (Suc n)" by (auto simp: notStep3EqualCoord)
    qed
  \<comment> \<open>the remaining cases are all solved by expanding the definitions\<close>
  qed (auto simp: LV_CHOMachine_def LV_initState_def next1_def next2_def
                  next3_def notStep3EqualCoord[OF run])
  with cmt show ?thesis by (intro conds, auto)
qed

text \<open>
  A process has a current timestamp only if:
  \begin{itemize}
  \item it is at step 2 or beyond,
  \item its coordinator has committed,
  \item its \<open>x\<close> value is the \<open>vote\<close> of its coordinator.
  \end{itemize}
\<close>

lemma currentTimestampE:
  assumes run: "CHORun LV_M rho HOs coords"
  and ts: "timestamp (rho r p) = Suc (phase r)"
  and conds: "\<lbrakk> 2 \<le> step r;
                commt (rho r (coord\<Phi> (rho r p)));
                x (rho r p) = the (vote (rho r (coord\<Phi> (rho r p))))
              \<rbrakk> \<Longrightarrow> A"
  shows "A"
proof -
  let "?ts n" = "timestamp (rho n p)"
  let "?crd n" = "coord\<Phi> (rho n p)"
  have "?ts r = Suc (phase r) \<longrightarrow> 
           2 \<le> step r 
         \<and> commt (rho r (?crd r))
         \<and> x (rho r p) = the (vote (rho r (?crd r)))"
    (is "?Q p r" is "_ \<longrightarrow> ?R r")
  proof (rule LV_induct'[OF run, where P="?Q"])
    \<comment> \<open>The assertion is trivially true initially because the timestamp is 0.\<close>
    assume "CinitState LV_M p (rho 0 p) (coords 0 p)" thus "?Q p 0"
      by (auto simp: LV_CHOMachine_def LV_initState_def)
  next
    txt \<open>The assertion is trivially preserved by step 0 because the timestamp in the
          post-state cannot be current (cf. lemma \<open>LV_timestamp_bounded\<close>).\<close>
    fix n
    assume stp': "step (Suc n) = 1"
    with run LV_timestamp_bounded[where n="Suc n"] 
    have "?ts (Suc n) \<le> phase (Suc n)" by auto
    thus "?Q p (Suc n)" by simp
  next
    txt \<open>Step 1 establishes the assertion by definition of the transition relation.\<close>
    fix n
    assume stp: "step n = 1" and stp':"step (Suc n) = 2"
       and ph: "phase (Suc n) = phase n"
       and nxt: "next1 n p (rho n p) (HOrcvdMsgs LV_M n p (HOs n p) (rho n)) 
                           (coords (Suc n) p) (rho (Suc n) p)"
    show "?Q p (Suc n)"
    proof
      assume ts: "?ts (Suc n) = Suc (phase (Suc n))"
      from run stp LV_timestamp_bounded[where n=n] 
      have "?ts n \<le> phase n" by auto
      moreover
      from run stp
      have "vote (rho (Suc n) (?crd (Suc n))) = vote (rho n (?crd n))"
        by (auto simp: notStep3EqualCoord notStep0EqualVote)
      moreover
      from run stp
      have "commt (rho (Suc n) (?crd (Suc n))) = commt (rho n (?crd n))"
        by (auto simp: notStep3EqualCoord notStep03EqualCommit)
      moreover
      note ts nxt stp stp' ph
      ultimately
      show "?R (Suc n)"
        by (auto simp: LV_CHOMachine_def HOrcvdMsgs_def LV_sendMsg_def
                       next1_def send1_def isVote_def)
    qed
  next
    txt \<open>For step 2, the assertion follows from the induction hypothesis,
          observing that none of the relevant state components change.\<close>
    fix n
    assume stp: "step n = 2" and stp': "step (Suc n) = 3"
       and ph: "phase (Suc n) = phase n"
       and ih: "?Q p n"
       and nxt: "next2 n p (rho n p) (HOrcvdMsgs LV_M n p (HOs n p) (rho n))
                           (coords (Suc n) p) (rho (Suc n) p)"
    show "?Q p (Suc n)"
    proof
      assume ts: "?ts (Suc n) = Suc (phase (Suc n))"
      from run stp
      have vt: "vote (rho (Suc n) (?crd (Suc n))) = vote (rho n (?crd n))"
        by (auto simp add: notStep3EqualCoord notStep0EqualVote)
      from run stp
      have cmt: "commt (rho (Suc n) (?crd (Suc n))) = commt (rho n (?crd n))"
        by (auto simp add: notStep3EqualCoord notStep03EqualCommit)
      with vt ts ph stp stp' ih nxt
      show "?R (Suc n)"
        by (auto simp add: next2_def)
    qed
  next
    txt \<open>The assertion is trivially preserved by step 3 because the timestamp in the
          post-state cannot be current (cf. lemma \<open>LV_timestamp_bounded\<close>).\<close>
    fix n
    assume stp': "step (Suc n) = 0"
    with run LV_timestamp_bounded[where n="Suc n"] 
    have "?ts (Suc n) \<le> phase (Suc n)" by auto
    thus "?Q p (Suc n)" by simp
  qed
  with ts show ?thesis by (intro conds) auto
qed

text \<open>
  If a process \<open>p\<close> has its \<open>ready\<close> bit set then:
  \begin{itemize}
  \item it is at step 3,
  \item it considers itself to be the coordinator of that phase and
  \item a majority of processes considers \<open>p\<close> to be the coordinator
    and has a current timestamp.
  \end{itemize}
\<close>

lemma readyE:
  assumes run: "CHORun LV_M rho HOs coords" and rdy: "ready (rho r p)"
  and conds: "\<lbrakk> step r = 3; coord\<Phi> (rho r p) = p;
                card { q . coord\<Phi> (rho r q) = p 
                         \<and> timestamp (rho r q) = Suc (phase r) } > N div 2
              \<rbrakk> \<Longrightarrow> P"
  shows P
proof -
  let "?qs n" = "{ q . coord\<Phi> (rho n q) = p 
                     \<and> timestamp (rho n q) = Suc (phase n) }"
  have "ready (rho r p) \<longrightarrow> 
          step r = 3
        \<and> coord\<Phi> (rho r p) = p
        \<and> card (?qs r) > N div 2"
    (is "?Q p r"  is "_ \<longrightarrow> ?R p r")
  proof (rule LV_induct'[OF run, where P="?Q"])
    \<comment> \<open>the interesting case is step 2\<close>
    fix n
    assume stp: "step n = 2" and stp': "step (Suc n) = 3"
       and ih: "?Q p n" and ph: "phase (Suc n) = phase n"
       and nxt: "next2 n p (rho n p) (HOrcvdMsgs LV_M n p (HOs n p) (rho n))
                           (coords (Suc n) p) (rho (Suc n) p)"
    show "?Q p (Suc n)"
    proof
      assume rdy: "ready (rho (Suc n) p)"
      from stp ih have nrdy: "\<not> ready (rho n p)" by simp
      with rdy nxt have "coord\<Phi> (rho n p) = p"
        by (auto simp: next2_def)
      with run stp have coord: "coord\<Phi> (rho (Suc n) p) = p"
        by (simp add: notStep3EqualCoord)
      let ?acks = "acksRcvd (HOrcvdMsgs LV_M n p (HOs n p) (rho n))"
      from nrdy rdy nxt have aRcvd: "card ?acks > N div 2"
        by (auto simp: next2_def)
      have "?acks \<subseteq> ?qs (Suc n)"
      proof (clarify)
        fix q
        assume q: "q \<in> ?acks"
        with stp 
        have n: "coord\<Phi> (rho n q) = p \<and> timestamp (rho n q) = Suc (phase n)"
          by (auto simp: LV_CHOMachine_def HOrcvdMsgs_def LV_sendMsg_def 
                         acksRcvd_def send2_def isAck_def)
        with run stp ph
        show "coord\<Phi> (rho (Suc n) q) = p
              \<and> timestamp (rho (Suc n) q) = Suc (phase (Suc n))"
          by (simp add: notStep3EqualCoord notStep1EqualTimestamp)
      qed
      hence "card ?acks \<le> card (?qs (Suc n))"
        by (intro card_mono) auto
      with stp' coord aRcvd show "?R p (Suc n)"
        by auto
    qed
    \<comment> \<open>the remaining steps are all solved trivially\<close>
  qed (auto simp: LV_CHOMachine_def LV_initState_def
                  next0_def next1_def next3_def)
  with rdy show ?thesis by (blast intro: conds)
qed


text \<open>
  A process decides only if the following conditions hold:
  \begin{itemize}
  \item it is at step 3,
  \item its coordinator votes for the value the process decides on,
  \item the coordinator has its \<open>ready\<close> and \<open>commt\<close> bits set.
  \end{itemize}
\<close>

lemma decisionE:
  assumes run: "CHORun LV_M rho HOs coords"
  and dec: "decide (rho (Suc r) p) \<noteq> decide (rho r p)"
  and conds: "\<lbrakk> 
        step r = 3; 
        decide (rho (Suc r) p) = Some (the (vote (rho r (coord\<Phi> (rho r p)))));
        ready (rho r (coord\<Phi> (rho r p))); commt (rho r (coord\<Phi> (rho r p)))
      \<rbrakk> \<Longrightarrow> P"
  shows P
proof -
  let ?cfg = "rho r"
  let ?cfg' = "rho (Suc r)"
  let "?crd p" = "coord\<Phi> (?cfg p)"
  let ?dec' = "decide (?cfg' p)"
  txt \<open>Except for the assertion about the \<open>commt\<close> field, the assertion can be
         proved directly from the next-state relation.\<close>
  have 1: "step r = 3
           \<and> ?dec' = Some (the (vote (?cfg (?crd p))))
           \<and> ready (?cfg (?crd p))"
    (is "?Q p r")
    proof (rule LV_Suc'[OF run, where P="?Q"])
    \<comment> \<open>for step 3, we prove the thesis by expanding the relevant definitions\<close>
    assume "next3 r p (?cfg p) (HOrcvdMsgs LV_M r p (HOs r p) ?cfg) 
                      (coords (Suc r) p) (?cfg' p)"
       and "step r = 3"
    with dec show ?thesis
      by (auto simp: next3_def send3_def isVote_def LV_CHOMachine_def 
                     HOrcvdMsgs_def LV_sendMsg_def)
  next
    \<comment> \<open>the other steps don't change the decision\<close>
    assume "next0 r p (?cfg p) (HOrcvdMsgs LV_M r p (HOs r p) ?cfg)
                      (coords (Suc r) p) (?cfg' p)"
    with dec show ?thesis by (auto simp: next0_def)
  next
    assume "next1 r p (?cfg p) (HOrcvdMsgs LV_M r p (HOs r p) ?cfg)
                      (coords (Suc r) p) (?cfg' p)"
    with dec show ?thesis by (auto simp: next1_def)
  next
    assume "next2 r p (?cfg p) (HOrcvdMsgs LV_M r p (HOs r p) ?cfg)
                      (coords (Suc r) p) (?cfg' p)"
    with dec show ?thesis by (auto simp: next2_def)
  qed
  hence "ready (?cfg (?crd p))" by blast
  txt \<open>Because the coordinator is ready, there is a majority of processes that
         consider it to be the coordinator and that have a current timestamp.\<close>
  with run
  have "card {q . ?crd q = ?crd p \<and> timestamp (?cfg q) = Suc (phase r)} 
          > N div 2" by (rule readyE)
  \<comment> \<open>Hence there is at least one such process \ldots\<close>
  hence "card {q . ?crd q = ?crd p \<and> timestamp (?cfg q) = Suc (phase r)} \<noteq> 0"
    by arith  (** auto simplifies too much **)
  then obtain q where "?crd q = ?crd p" and "timestamp (?cfg q) = Suc (phase r)"
    by auto
  \<comment> \<open>\ldots\ and by a previous lemma the coordinator must have committed.\<close>
  with run have "commt (?cfg (?crd p))"
    by (auto elim: currentTimestampE)
  with 1 show ?thesis by (blast intro: conds)
qed


subsection \<open>Proof of Integrity\<close>

text \<open>
  Integrity is proved using a standard invariance argument that asserts
  that only values present in the initial state appear in the relevant
  fields.
\<close>

(*
  The proof mainly relies on lemmas @{text notStep1EqualX},
  @{text notStep0EqualVote}, @{text commitE} and @{text decisionE}.
*)

lemma lv_integrityInvariant:
  assumes run: "CHORun LV_M rho HOs coords"
  and inv: "\<lbrakk> range (x \<circ> (rho n)) \<subseteq> range (x \<circ> (rho 0));
              range (vote \<circ> (rho n)) \<subseteq> {None} \<union> Some ` range (x \<circ> (rho 0));
              range (decide \<circ> (rho n)) \<subseteq> {None} \<union> Some ` range (x \<circ> (rho 0))
       \<rbrakk> \<Longrightarrow> A"
  shows "A"
proof -
  let ?x0 = "range (x \<circ> rho 0)"
  let ?x0opt = "{None} \<union> Some ` ?x0"
  have "range (x \<circ> rho n) \<subseteq> ?x0
        \<and> range (vote \<circ> rho n) \<subseteq> ?x0opt
        \<and> range (decide \<circ> rho n) \<subseteq> ?x0opt"
    (is "?Inv n" is "?X n \<and> ?Vote n \<and> ?Decide n")
  proof (induct n)
    from run show "?Inv 0" 
      by (auto simp: CHORun_eq CHOinitConfig_def LV_CHOMachine_def
                     LV_initState_def)
  next
    fix n
    assume ih: "?Inv n" thus "?Inv (Suc n)"
    proof (clarify)
      assume x: "?X n" and vt: "?Vote n" and dec: "?Decide n"

      txt \<open>Proof of first conjunct\<close>
      have x': "?X (Suc n)"
      proof (clarsimp)
        fix p
        from run
        show "x (rho (Suc n) p) \<in> range (\<lambda>q. x (rho 0 q))" (is "?P p n")
        proof (rule LV_Suc'[where P="?P"])
          \<comment> \<open>only @{text step1} is of interest\<close>
          assume stp: "step n = 1"
             and nxt: "next1 n p (rho n p)
                             (HOrcvdMsgs LV_M n p (HOs n p) (rho n))
                             (coords (Suc n) p) (rho (Suc n) p)"
          show ?thesis
          proof (cases "rho (Suc n) p = rho n p")
            case True
            with x show ?thesis by auto
          next
            case False
            with stp nxt have cmt: "commt (rho n (coord\<Phi> (rho n p)))"
              and xp: "x (rho (Suc n) p) = the (vote (rho n (coord\<Phi> (rho n p))))"
            by (auto simp: next1_def LV_CHOMachine_def HOrcvdMsgs_def 
                           LV_sendMsg_def send1_def isVote_def)
            from run cmt have "vote (rho n (coord\<Phi> (rho n p))) \<noteq> None"
              by (rule commitE)
            moreover
            from vt have "vote (rho n (coord\<Phi> (rho n p))) \<in> ?x0opt"
              by (auto simp add: image_def)
            moreover
            note xp
            ultimately
            show ?thesis by (force simp add: image_def)
          qed
          \<comment> \<open>the other steps don't change @{text x}\<close>
        next
          assume "step n = 0"
          with run have "x (rho (Suc n) p) = x (rho n p)"
            by (simp add: notStep1EqualX)
          with x show ?thesis by auto
        next
          assume "step n = 2"
          with run have "x (rho (Suc n) p) = x (rho n p)"
            by (simp add: notStep1EqualX)
          with x show ?thesis by auto
        next
          assume "step n = 3"
          with run have "x (rho (Suc n) p) = x (rho n p)" 
            by (simp add: notStep1EqualX)
          with x show ?thesis by auto
        qed
      qed

      txt \<open>Proof of second conjunct\<close>
      have vt': "?Vote (Suc n)"
      proof (clarsimp simp: image_def)
        fix p v
        assume v: "vote (rho (Suc n) p) = Some v"
        from run
        have "vote (rho (Suc n) p) = Some v \<longrightarrow> v \<in> ?x0" (is "?P p n")
        proof (rule LV_Suc'[where P="?P"])
          \<comment> \<open>here only @{text step0} is of interest\<close>
          assume stp: "step n = 0"
             and nxt: "next0 n p (rho n p)
                             (HOrcvdMsgs LV_M n p (HOs n p) (rho n))
                             (coords (Suc n) p) (rho (Suc n) p)"
          show ?thesis
          proof  (cases "rho (Suc n) p = rho n p")
            case True
            from vt have "vote (rho n p) \<in> ?x0opt" 
              by (auto simp: image_def)
            with True show ?thesis by auto
          next
            case False
            from nxt stp False v obtain q where "v = x (rho n q)"
              by (auto simp: next0_def send0_def LV_CHOMachine_def 
                             HOrcvdMsgs_def LV_sendMsg_def)
            with x show ?thesis by (auto simp: image_def)
          qed
          \<comment> \<open>the other cases don't change the vote\<close>
        next
          assume "step n = 1"
          with run have "vote (rho (Suc n) p) = vote (rho n p)"
            by (simp add: notStep0EqualVote)
          moreover
          from vt have "vote (rho n p) \<in> ?x0opt"
            by (auto simp: image_def)
          ultimately
          show ?thesis by auto
        next
          assume "step n = 2"
          with run have "vote (rho (Suc n) p) = vote (rho n p)"
            by (simp add: notStep0EqualVote)
          moreover
          from vt have "vote (rho n p) \<in> ?x0opt"
            by (auto simp: image_def)
          ultimately
          show ?thesis by auto
        next
          assume "step n = 3"
          with run have "vote (rho (Suc n) p) = vote (rho n p)"
            by (simp add: notStep0EqualVote)
          moreover
          from vt have "vote (rho n p) \<in> ?x0opt"
            by (auto simp: image_def)
          ultimately
          show ?thesis by auto
        qed
        with v show "\<exists>q. v = x (rho 0 q)" by auto
      qed

      txt \<open>Proof of third conjunct\<close>
      have dec': "?Decide (Suc n)"
      proof (clarsimp simp: image_def)
        fix p v
        assume v: "decide (rho (Suc n) p) = Some v"
        show "\<exists>q. v = x (rho 0 q)"
        proof (cases "decide (rho (Suc n) p) = decide (rho n p)")
          case True
          with dec True v show ?thesis by (auto simp: image_def)
        next
          case False
          let ?crd = "coord\<Phi> (rho n p)"
          from False run 
          have d': "decide (rho (Suc n) p) = Some (the (vote (rho n ?crd)))" 
            and cmt: "commt (rho n ?crd)"
            by (auto elim: decisionE)
          from vt have vtc: "vote (rho n ?crd) \<in> ?x0opt"
            by (auto simp: image_def)
          from run cmt have "vote (rho n ?crd) \<noteq> None" 
            by (rule commitE)
          with d' v vtc show ?thesis by auto
        qed
      qed
      from x' vt' dec' show ?thesis by simp
    qed
  qed
  with inv show ?thesis by simp
qed

text \<open>
  Integrity now follows immediately.
\<close>

theorem lv_integrity:
  assumes run: "CHORun LV_M rho HOs coords"
      and dec: "decide (rho n p) = Some v"
  shows "\<exists>q. v = x (rho 0 q)"
proof -
  from run have "decide (rho n p) \<in> {None} \<union> Some ` (range (x \<circ> (rho 0)))"
    by (rule lv_integrityInvariant) (auto simp: image_def)
  with dec show ?thesis by (auto simp: image_def)
qed


subsection \<open>Proof of Agreement and Irrevocability\<close>

text \<open>
  The following lemmas closely follow a hand proof provided by
  Bernadette Charron-Bost.

  If a process decides, then a majority of processes have a current
  timestamp.
\<close>
(*
  The proof mainly relies on lemmas @{text decisionE}, @{text readyE}
  and @{text LV_timestamp_bounded}. 
*)

lemma decisionThenMajorityBeyondTS:
  assumes run: "CHORun LV_M rho HOs coords"
  and dec: "decide (rho (Suc r) p) \<noteq> decide (rho r p)"
  shows "card (procsBeyondTS (Suc (phase r)) (rho r)) > N div 2"
  using run dec proof (rule decisionE)
  txt \<open>Lemma \<open>decisionE\<close> tells us that we are at step 3 and
    that the coordinator is ready.\<close>
  let ?crd = "coord\<Phi> (rho r p)"
  let ?qs = "{ q . coord\<Phi> (rho r q) = ?crd
                 \<and> timestamp (rho r q) = Suc (phase r) }"
  assume stp: "step r = 3" and rdy: "ready (rho r ?crd)"
  txt \<open>Now, lemma \<open>readyE\<close> implies that a majority of processes
    have a recent timestamp.\<close>
  from run rdy have "card ?qs > N div 2" by (rule readyE)
  moreover
  from stp LV_timestamp_bounded[OF run, where n=r]
  have "\<forall>q. timestamp (rho r q) \<le> Suc (phase r)" by auto
  hence "?qs \<subseteq> procsBeyondTS (Suc (phase r)) (rho r)"
    by (auto simp: procsBeyondTS_def)
  hence "card ?qs \<le> card (procsBeyondTS (Suc (phase r)) (rho r))"
    by (intro card_mono) auto
  ultimately show ?thesis by simp
qed

text \<open>
  No two different processes have their \emph{commit} flag set at any state.
\<close>

lemma committedProcsEqual:
  assumes run: "CHORun LV_M rho HOs coords"
  and cmt: "commt (rho r p)" and cmt': "commt (rho r p')"
  shows "p = p'"
proof -
  from run cmt have "card {q . coord\<Phi> (rho r q) = p} > N div 2"
    by (blast elim: commitE)
  moreover
  from run cmt' have "card {q . coord\<Phi> (rho r q) = p'} > N div 2" 
    by (blast elim: commitE)
  ultimately
  obtain q where "coord\<Phi> (rho r q) = p" and "p' = coord\<Phi> (rho r q)" 
    by (auto elim: majoritiesE')
  thus ?thesis by simp
qed

text \<open>
  No two different processes have their \emph{ready} flag set at any state.
\<close>

lemma readyProcsEqual:
  assumes run: "CHORun LV_M rho HOs coords"
  and rdy: "ready (rho r p)" and rdy': "ready (rho r p')"
  shows "p = p'"
proof -
  let "?C p" = "{q . coord\<Phi> (rho r q) = p \<and> timestamp (rho r q) = Suc (phase r)}"
  from run rdy have "card (?C p) > N div 2"
    by (blast elim: readyE)
  moreover
  from run rdy' have "card (?C p') > N div 2" 
    by (blast elim: readyE)
  ultimately
  obtain q where "coord\<Phi> (rho r q) = p" and "p' = coord\<Phi> (rho r q)" 
    by (auto elim: majoritiesE')
  thus ?thesis by simp
qed

text \<open>
  The following lemma asserts that whenever a process \<open>p\<close> commits
  at a state where a majority of processes have a timestamp beyond \<open>ts\<close>,
  then \<open>p\<close> votes for a value held by some process whose timestamp is
  beyond \<open>ts\<close>.
\<close>
(*
  The proof mainly relies on lemmas @{text commitE}, @{text highestStampRcvd_max},
  @{text notStep1EqualTimestamp}, @{text notStep1EqualX} and then on
  lemmas @{text notStep03EqualCommit}, @{text notStep0EqualVote}, @{text commitE},
  @{text committedProcsEqual} and @{text LV_timestamp_monotonic}.
*)

lemma commitThenVoteRecent:
  assumes run: "CHORun LV_M rho HOs coords"
  and maj: "card (procsBeyondTS ts (rho r)) > N div 2"
  and cmt: "commt (rho r p)"
  shows "\<exists>q \<in> procsBeyondTS ts (rho r). vote (rho r p) = Some (x (rho r q))"
        (is "?Q r")
proof -
  let "?bynd n" = "procsBeyondTS ts (rho n)"
  have "card (?bynd r) > N div 2 \<and> commt (rho r p) \<longrightarrow> ?Q r" (is "?P p r")
  proof (rule LV_induct[OF run])
    txt \<open>\<open>next0\<close> establishes the property\<close>
    fix n
    assume stp: "step n = 0"
       and nxt: "\<forall>q. next0 n q (rho n q) 
                             (HOrcvdMsgs LV_M n q (HOs n q) (rho n)) 
                             (coords (Suc n) q) 
                             (rho (Suc n) q)"
              (is "\<forall>q. ?nxt q")
    from nxt have nxp: "?nxt p" ..
    show "?P p (Suc n)"
    proof (clarify)
      assume mj: "card (?bynd (Suc n)) > N div 2"
         and ct: "commt (rho (Suc n) p)"
      show "?Q (Suc n)"
      proof -
        let ?msgs = "HOrcvdMsgs LV_M n p (HOs n p) (rho n)"
        from stp run have "\<not> commt (rho n p)" by (auto elim: commitE)
        with nxp ct obtain q v where
          v: "?msgs q = Some (ValStamp v (highestStampRcvd ?msgs))" and
          vote: "vote (rho (Suc n) p) = Some v" and
          rcvd: "card (valStampsRcvd ?msgs) > N div 2"
          by (auto simp: next0_def)
        from mj rcvd obtain q' where 
          q1': "q' \<in> ?bynd (Suc n)" and q2': "q' \<in> valStampsRcvd ?msgs"
          by (rule majoritiesE')
        have "timestamp (rho n q') \<le> timestamp (rho n q)"
        proof -
          from q2' obtain v' ts'
            where ts': "?msgs q' = Some (ValStamp v' ts')"
            by (auto simp: valStampsRcvd_def)
          hence "ts' \<le> highestStampRcvd ?msgs"
            by (rule highestStampRcvd_max)
          moreover
          from ts' stp have "timestamp (rho n q') = ts'"
            by (auto simp: LV_CHOMachine_def HOrcvdMsgs_def 
                           LV_sendMsg_def send0_def)
          moreover
          from v stp have "timestamp (rho n q) = highestStampRcvd ?msgs"
            by (auto simp: LV_CHOMachine_def HOrcvdMsgs_def
                           LV_sendMsg_def send0_def)
          ultimately
          show ?thesis by simp
        qed
        moreover
        from run stp 
        have "timestamp (rho (Suc n) q') = timestamp (rho n q')"
          by (simp add: notStep1EqualTimestamp)
        moreover
        from run stp
        have "timestamp (rho (Suc n) q) = timestamp (rho n q)"
          by (simp add: notStep1EqualTimestamp)
        moreover
        note q1'
        ultimately
        have "q \<in> ?bynd (Suc n)"
          by (simp add: procsBeyondTS_def)
        moreover
        from v vote stp
        have "vote (rho (Suc n) p) = Some (x (rho n q))"
          by (auto simp: LV_CHOMachine_def HOrcvdMsgs_def
                         LV_sendMsg_def send0_def)
        moreover
        from run stp have "x (rho (Suc n) q) = x (rho n q)"
          by (simp add: notStep1EqualX)
        ultimately
        show ?thesis by force
      qed
    qed

  next
    txt \<open>We now prove that \<open>next1\<close> preserves the property.
      Observe that \<open>next1\<close> may establish a majority of processes
      with current timestamps, so we cannot just refer to the induction
      hypothesis. However, if that happens, there is at least one process
      with a fresh timestamp that copies the vote of the (only) committed
      coordinator, thus establishing the property.\<close>
    fix n
    assume stp: "step n = 1"
       and nxt: "\<forall>q. next1 n q (rho n q) 
                               (HOrcvdMsgs LV_M n q (HOs n q) (rho n)) 
                               (coords (Suc n) q)
                               (rho (Suc n) q)" 
               (is "\<forall>q. ?nxt q")
       and ih: "?P p n"
    from nxt have nxp: "?nxt p" ..
    show "?P p (Suc n)"
    proof (clarify)
      assume mj': "card (?bynd (Suc n)) > N div 2"
         and ct': "commt (rho (Suc n) p)"
      from run stp ct' have ct: "commt (rho n p)"
        by (simp add: notStep03EqualCommit)
      from run stp have vote': "vote (rho (Suc n) p) = vote (rho n p)"
        by (simp add: notStep0EqualVote)
      show "?Q (Suc n)"
      proof (cases "\<exists>q \<in> ?bynd (Suc n). rho (Suc n) q \<noteq> rho n q")
        case True
        txt \<open>in this case the property holds because \<open>q\<close> updates
          its \<open>x\<close> field to the vote\<close>
        then obtain q where
          q1: "q \<in> ?bynd (Suc n)" and q2: "rho (Suc n) q \<noteq> rho n q" ..
        from nxt have "?nxt q" ..
        with q2 stp
        have  x': "x (rho (Suc n) q) = the (vote (rho n (coord\<Phi> (rho n q))))"
          and coord: "commt (rho n (coord\<Phi> (rho n q)))"
          by (auto simp: next1_def send1_def LV_CHOMachine_def HOrcvdMsgs_def
                         LV_sendMsg_def isVote_def)
        from run ct have vote: "vote (rho n p) \<noteq> None" 
          by (rule commitE)
        from run coord ct have "coord\<Phi> (rho n q) = p" 
          by (rule committedProcsEqual)
        with q1 x' vote vote' show ?thesis by auto
      next
        case False
        txt \<open>if no relevant process moves then \<open>procsBeyondTS\<close> doesn't 
          change and we invoke the induction hypothesis\<close>
        hence bynd: "?bynd (Suc n) = ?bynd n"
        proof (auto simp: procsBeyondTS_def)
          fix r
          assume ts: "ts \<le> timestamp (rho n r)"
          from run have "timestamp (rho n r) \<le> timestamp (rho (Suc n) r)"
            by (simp add: LV_timestamp_monotonic)
          with ts show "ts \<le> timestamp (rho (Suc n) r)" by simp
        qed
        with mj' have mj: "card (?bynd n) > N div 2" by simp
        with ct ih obtain q where
          "q \<in> ?bynd n" and "vote (rho n p) = Some (x (rho n q))"
          by blast
        with vote' bynd False show ?thesis by auto
      qed
    qed

  next
    txt \<open>\<open>step2\<close> preserves the property, via the induction hypothesis.\<close>
    fix n
    assume stp: "step n = 2"
       and nxt: "\<forall>q. next2 n q (rho n q) 
                               (HOrcvdMsgs LV_M n q (HOs n q) (rho n)) 
                               (coords (Suc n) q) 
                               (rho (Suc n) q)"
               (is "\<forall>q. ?nxt q")
       and ih: "?P p n"
    from nxt have nxp: "?nxt p" ..
    show "?P p (Suc n)"
    proof (clarify)
      assume mj': "card (?bynd (Suc n)) > N div 2"
         and ct': "commt (rho (Suc n) p)"
      from run stp ct' have ct: "commt (rho n p)"
        by (simp add: notStep03EqualCommit)
      from run stp have vote': "vote (rho (Suc n) p) = vote (rho n p)"
        by (simp add: notStep0EqualVote)
      from run stp have "\<forall>q. timestamp (rho (Suc n) q) = timestamp (rho n q)"
        by (simp add: notStep1EqualTimestamp)
      hence bynd': "?bynd (Suc n) = ?bynd n"
        by (auto simp add: procsBeyondTS_def)
      from run stp have "\<forall>q. x (rho (Suc n) q) = x (rho n q)"
        by (simp add: notStep1EqualX)
      with bynd' vote' ct mj' ih show "?Q (Suc n)"
        by auto
    qed

  txt \<open>the initial state and the \<open>step3\<close> transition are trivial 
    because the \<open>commt\<close> flag cannot be set.\<close>
  qed (auto elim: commitE[OF run])
  with maj cmt show ?thesis by simp
qed

text \<open>
  The following lemma gives the crucial argument for agreement:
  after some process \<open>p\<close> has decided, all processes whose
  timestamp is beyond the timestamp at the point of decision contain
  the decision value in their \<open>x\<close> field.
\<close>
(*
  The proof mainly relies on lemmas @{text LV_timestamp_bounded},
  @{text currentTimestampE}, @{text committedProcsEqual},
  @{text decisionThenMajorityBeyondTS}, @{text procsBeyondTS_monotonic}
  @{text commitThenVoteRecent}, @{text  notStep1EqualX}
  and @{text notStep1EqualTimestamp}.
*)

lemma XOfTimestampBeyondDecision:
  assumes run: "CHORun LV_M rho HOs coords"
      and dec: "decide (rho (Suc r) p) \<noteq> decide (rho r p)"
  shows "\<forall>q \<in> procsBeyondTS (Suc (phase r)) (rho (r+k)).
              x (rho (r+k) q) = the (decide (rho (Suc r) p))"
  (is "\<forall>q \<in> ?bynd k. _ = ?v" is "?P p k")
proof (induct k)
  \<comment> \<open>base step\<close>
  show "?P p 0"
  proof (clarify)
    fix q
    assume q: "q \<in> ?bynd 0"
    txt \<open>use preceding lemmas about the decision value and the 
      \<open>x\<close> field of processes with fresh timestamps\<close>
    from run dec
    have  stp: "step r = 3"
      and v: "decide (rho (Suc r) p) = Some (the (vote (rho r (coord\<Phi> (rho r p)))))"
      and cmt: "commt (rho r (coord\<Phi> (rho r p)))"
      by (auto elim: decisionE)
    from stp LV_timestamp_bounded[OF run, where n=r]
    have "timestamp (rho r q) \<le> Suc (phase r)" by simp
    with q have "timestamp (rho r q) = Suc (phase r)"
      by (simp add: procsBeyondTS_def)
    with run
    have  x: "x (rho r q) = the (vote (rho r (coord\<Phi> (rho r q))))"
      and cmt': "commt (rho r (coord\<Phi> (rho r q)))"
      by (auto elim: currentTimestampE)
    from run cmt cmt' have "coord\<Phi> (rho r p) = coord\<Phi> (rho r q)" 
      by (rule committedProcsEqual)
    with x v show "x (rho (r+0) q) = ?v" by simp
  qed
  next
  \<comment> \<open>induction step\<close>
  fix k
  assume ih: "?P p k"
  show "?P p (Suc k)"
  proof (clarify)
    fix q
    assume q: "q \<in> ?bynd (Suc k)"
    \<comment> \<open>distinguish the kind of transition---only @{text step1} is interesting\<close>
    have "x (rho (Suc (r + k)) q) = ?v" (is "?X q (r+k)")
    proof (rule LV_Suc'[OF run, where P="?X"])
      assume stp: "step (r + k) = 1"
      and nxt: "next1 (r+k) q (rho (r+k) q)
                      (HOrcvdMsgs LV_M (r+k) q (HOs (r+k) q) (rho (r+k)))
                      (coords (Suc (r+k)) q)
                      (rho (Suc (r+k)) q)"
      show ?thesis
      proof (cases "rho (Suc (r+k)) q = rho (r+k) q")
        case True
        with q ih show ?thesis by (auto simp: procsBeyondTS_def)
      next
        case False
        from run dec have "card (?bynd 0) > N div 2"
          by (simp add: decisionThenMajorityBeyondTS)
        moreover
        have "?bynd 0 \<subseteq> ?bynd k"
          by (auto elim: procsBeyondTS_monotonic[OF run])
        hence "card (?bynd 0) \<le> card (?bynd k)"
          by (auto intro: card_mono)
        ultimately
        have maj: "card (?bynd k) > N div 2" by simp
        let ?crd = "coord\<Phi> (rho (r+k) q)"
        from False stp nxt have 
          cmt: "commt (rho (r+k) ?crd)" and
          x: "x (rho (Suc (r+k)) q) = the (vote (rho (r+k) ?crd))"
          by (auto simp: next1_def LV_CHOMachine_def HOrcvdMsgs_def
                         LV_sendMsg_def send1_def isVote_def)
        from run maj cmt stp obtain q'
          where q1': "q' \<in> ?bynd k"
            and q2': "vote (rho (r+k) ?crd) = Some (x (rho (r+k) q'))"
          by (blast dest: commitThenVoteRecent)
        with x ih show ?thesis by auto
      qed
    next
      \<comment> \<open>all other steps hold by induction hypothesis\<close>
      assume "step (r+k) = 0"
      with run have x: "x (rho (Suc (r+k)) q) = x (rho (r+k) q)"
        and ts: "timestamp (rho (Suc (r+k)) q) = timestamp (rho (r+k) q)"
        by (auto simp: notStep1EqualX notStep1EqualTimestamp)
      from ts q have "q \<in> ?bynd k"
        by (auto simp: procsBeyondTS_def)
      with x ih show ?thesis by auto
    next
      assume "step (r+k) = 2"
      with run have x: "x (rho (Suc (r+k)) q) = x (rho (r+k) q)"
        and ts: "timestamp (rho (Suc (r+k)) q) = timestamp (rho (r+k) q)"
        by (auto simp: notStep1EqualX notStep1EqualTimestamp)
      from ts q have "q \<in> ?bynd k"
        by (auto simp: procsBeyondTS_def)
      with x ih show ?thesis by auto
    next
      assume "step (r+k) = 3"
      with run have x: "x (rho (Suc (r+k)) q) = x (rho (r+k) q)"
        and ts: "timestamp (rho (Suc (r+k)) q) = timestamp (rho (r+k) q)"
        by (auto simp: notStep1EqualX notStep1EqualTimestamp)
      from ts q have "q \<in> ?bynd k"
        by (auto simp: procsBeyondTS_def)
      with x ih show ?thesis by auto
    qed
    thus "x (rho (r + Suc k) q) = ?v" by simp
  qed
qed

text \<open>
  We are now in position to prove Agreement: if some process decides
  at step \<open>r\<close> and another (or possibly the same) process decides
  at step \<open>r+k\<close> then they decide the same value.
\<close>

(*
  The proof mainly relies on lemmas @{text decisionE},
  @{text decisionThenMajorityBeyondTS}, @{text procsBeyondTS_monotonic}
  @{text commitThenVoteRecent} and @{text XOfTimestampBeyondDecision}.
*)

lemma laterProcessDecidesSameValue:
  assumes run: "CHORun LV_M rho HOs coords"
  and p: "decide (rho (Suc r) p) \<noteq> decide (rho r p)"
  and q: "decide (rho (Suc (r+k)) q) \<noteq> decide (rho (r+k) q)"
  shows "decide (rho (Suc (r+k)) q) = decide (rho (Suc r) p)"
proof -
  let "?bynd k" = "procsBeyondTS (Suc (phase r)) (rho (r+k))"
  let ?qcrd = "coord\<Phi> (rho (r+k) q)"
  from run p have notNone: "decide (rho (Suc r) p) \<noteq> None"
    by (auto elim: decisionE)
  \<comment> \<open>process @{text q} decides on the vote of its coordinator\<close>
  from run q
  have dec: "decide (rho (Suc (r+k)) q) = Some (the (vote (rho (r+k) ?qcrd)))"
   and cmt: "commt (rho (r+k) ?qcrd)"
    by (auto elim: decisionE)
  \<comment> \<open>that vote is the @{text x} field of some process @{text "q'"} with a recent timestamp\<close>
  from run p have "card (?bynd 0) > N div 2"
    by (simp add: decisionThenMajorityBeyondTS)
  moreover
  from run have "?bynd 0 \<subseteq> ?bynd k" 
    by (auto elim: procsBeyondTS_monotonic)
  hence "card (?bynd 0) \<le> card (?bynd k)" 
    by (auto intro: card_mono)
  ultimately
  have maj: "card (?bynd k) > N div 2" by simp
  from run maj cmt obtain q' 
    where q'1: "q' \<in> ?bynd k"
      and q'2: "vote (rho (r+k) ?qcrd) = Some (x (rho (r+k) q'))"
    by (auto dest: commitThenVoteRecent)
  \<comment> \<open>the @{text x} field of process @{text "q'"} is the value @{text p} decided on\<close>
  from run p q'1
  have "x (rho (r+k) q') = the (decide (rho (Suc r) p))"
    by (auto dest: XOfTimestampBeyondDecision)
  \<comment> \<open>which proves the assertion\<close>
  with dec q'2 notNone show ?thesis by auto
qed

text \<open>
  A process that holds some decision \<open>v\<close> has decided \<open>v\<close>
  sometime in the past.
\<close>

lemma decisionNonNullThenDecided:
  assumes run: "CHORun LV_M rho HOs coords"
      and dec: "decide (rho n p) = Some v"
  shows "\<exists>m<n. decide (rho (Suc m) p) \<noteq> decide (rho m p) 
             \<and> decide (rho (Suc m) p) = Some v"
proof -
  let "?dec k" = "decide (rho k p)"
  have "(\<forall>m<n. ?dec (Suc m) \<noteq> ?dec m \<longrightarrow> ?dec (Suc m) \<noteq> Some v)
         \<longrightarrow> ?dec n \<noteq> Some v"
    (is "?P n" is "?A n \<longrightarrow> _")
  proof (induct n)
    from run show "?P 0"
      by (auto simp: CHORun_eq LV_CHOMachine_def
                     CHOinitConfig_def LV_initState_def)
  next
    fix n
    assume ih: "?P n"
    show "?P (Suc n)"
    proof (clarify)
      assume p: "?A (Suc n)" and v: "?dec (Suc n) = Some v"
      from p have "?A n" by simp
      with ih have "?dec n \<noteq> Some v" by simp
      moreover
      from p
      have "?dec (Suc n) \<noteq> ?dec n \<longrightarrow> ?dec (Suc n) \<noteq> Some v" by simp
      ultimately
      have "?dec (Suc n) \<noteq> Some v" by auto
      with v show "False" by simp
    qed
  qed
  with dec show ?thesis by auto
qed

text \<open>
  Irrevocability and Agreement are straightforward consequences
  of the two preceding lemmas.
\<close>
(*
  The proof mainly relies on lemmas @{text decisionNonNullThenDecided}
  and @{text laterProcessDecidesSameValue}. 
*)

theorem lv_irrevocability:
  assumes run: "CHORun LV_M rho HOs coords"
      and p: "decide (rho m p) = Some v"
  shows "decide (rho (m+k) p) = Some v"
proof -
  from run p obtain n where
    n1: "n < m" and
    n2: "decide (rho (Suc n) p) \<noteq> decide (rho n p)" and
    n3: "decide (rho (Suc n) p) = Some v"
    by (auto dest: decisionNonNullThenDecided)
  have "\<forall>i. decide (rho (Suc (n+i)) p) = Some v" (is "\<forall>i. ?dec i")
  proof
    fix i
    show "?dec i"
    proof (induct i)
      from n3 show "?dec 0" by simp
    next
      fix j
      assume ih: "?dec j"
      show "?dec (Suc j)"
      proof (rule ccontr)
        assume ctr: "\<not> (?dec (Suc j))"
        with ih 
        have "decide (rho (Suc (n + Suc j)) p) \<noteq> decide (rho (n + Suc j) p)"
          by simp
        with run n2
        have "decide (rho (Suc (n + Suc j)) p) = decide (rho (Suc n) p)"
          by (rule laterProcessDecidesSameValue)
        with ctr n3 show "False" by simp
      qed
    qed
  qed
  moreover
  from n1 obtain j where "m+k = Suc(n+j)"
    by (auto dest: less_imp_Suc_add)
  ultimately
  show ?thesis by auto
qed

theorem lv_agreement:
  assumes run: "CHORun LV_M rho HOs coords"
      and p: "decide (rho m p) = Some v"
      and q: "decide (rho n q) = Some w"
  shows "v = w"
proof -
  from run p obtain k 
    where k1: "decide (rho (Suc k) p) \<noteq> decide (rho k p)"
      and k2: "decide (rho (Suc k) p) = Some v"
    by (auto dest: decisionNonNullThenDecided)
  from run q obtain l 
    where l1: "decide (rho (Suc l) q) \<noteq> decide (rho l q)"
      and l2: "decide (rho (Suc l) q) = Some w"
    by (auto dest: decisionNonNullThenDecided)
  show ?thesis
  proof (cases "k \<le> l")
    case True
    then obtain m where m: "l = k+m" by (auto simp: le_iff_add)
    from run k1 l1 m
    have "decide (rho (Suc l) q) = decide (rho (Suc k) p)"
      by (auto elim: laterProcessDecidesSameValue)
    with k2 l2 show ?thesis by simp
  next
    case False
    hence "l \<le> k" by simp
    then obtain m where m: "k = l+m" by (auto simp: le_iff_add)
    from run l1 k1 m
    have "decide (rho (Suc k) p) = decide (rho (Suc l) q)"
      by (auto elim: laterProcessDecidesSameValue)
    with l2 k2 show ?thesis by simp
  qed
qed


subsection \<open>Proof of Termination\<close>

text\<open>
  The proof of termination relies on the communication predicate,
  which stipulates the existence of some phase
  during which there is a single coordinator that (a) receives a majority
  of messages and (b) is heard by everybody. Therefore, all processes
  successfully execute the protocol, deciding at step $3$ of that phase.
\<close>
(*
  The proof mainly relies on lemmas @{text notStep3EqualCoord},
  @{text commitE} and @{text readyE}.
*)

theorem lv_termination:
  assumes run: "CHORun LV_M rho HOs coords"
      and commG:"CHOcommGlobal LV_M HOs coords" 
  shows "\<exists>r. \<forall>p. decide (rho r p) \<noteq> None"
proof -
  txt \<open>The communication predicate implies the existence of a ``successful'' phase
    \<open>ph\<close>, coordinated by some process \<open>c\<close> for all processes.\<close>
  from commG obtain ph c
    where c: "\<forall>p. coords (4*ph) p = c"
    and maj0: "card (HOs (4*ph) c) > N div 2"
    and maj2: "card (HOs (4*ph+2) c) > N div 2"
    and rcv1: "\<forall>p. c \<in> HOs (4*ph+1) p"
    and rcv3: "\<forall>p. c \<in> HOs (4*ph+3) p"
    by (auto simp: LV_CHOMachine_def LV_commGlobal_def)
  let ?r0 = "4*ph"
  let ?r1 = "Suc ?r0"
  let ?r2 = "Suc ?r1"
  let ?r3 = "Suc ?r2"
  let ?r4 = "Suc ?r3"

  txt \<open>Process \<open>c\<close> is the coordinator of all steps of phase \<open>ph\<close>.\<close>
  from run c have c':"\<forall>p. coord\<Phi> (rho ?r p) = c"
    by (auto simp add: phase_def coordinators)
  with run have c1: "\<forall>p. coord\<Phi> (rho ?r1 p) = c"
    by (auto simp add: step_def mod_Suc notStep3EqualCoord)
  with run have c2: "\<forall>p. coord\<Phi> (rho ?r2 p) = c"
    by (auto simp add: step_def mod_Suc notStep3EqualCoord)
  with run have c3: "\<forall>p. coord\<Phi> (rho ?r3 p) = c"
    by (auto simp add: step_def mod_Suc notStep3EqualCoord)

  txt \<open>The coordinator receives \<open>ValStamp\<close> messages from a majority of
    processes at step $0$ of phase \<open>ph\<close> and therefore commits during the
    transition at the end of step $0$.\<close>
  have 1: "commt (rho ?r1 c)" (is "?P c (4*ph)")
  proof (rule LV_Suc'[OF run, where P="?P"], auto simp: step_def)
    assume "next0 ?r c (rho ?r c) (HOrcvdMsgs LV_M ?r c (HOs ?r c) (rho ?r))
                  (coords (Suc ?r) c) (rho (Suc ?r) c)"
    with c' maj0 show "commt (rho (Suc ?r) c)"
      by (auto simp: step_def next0_def send0_def valStampsRcvd_def 
                     LV_CHOMachine_def HOrcvdMsgs_def LV_sendMsg_def)
  qed

  txt \<open>All processes receive the vote of \<open>c\<close> at step 1 and therefore
    update their time stamps during the transition at the end of step $1$.\<close>
  have 2: "\<forall>p. timestamp (rho ?r2 p) = Suc ph"
  proof
    fix p
    let ?msgs = "HOrcvdMsgs LV_M ?r1 p (HOs ?r1 p) (rho ?r1)"
    let ?crd = "coord\<Phi> (rho ?r1 p)"
    from run 1 c1 rcv1
    have cnd: "?msgs ?crd \<noteq> None \<and> isVote (the (?msgs ?crd))"
      by (auto elim: commitE
               simp: step_def LV_CHOMachine_def HOrcvdMsgs_def
                     LV_sendMsg_def send1_def isVote_def)
    show "timestamp (rho ?r2 p) = Suc ph" (is "?P p (Suc (4*ph))")
    proof (rule LV_Suc'[OF run, where P="?P"], auto simp: step_def mod_Suc)
      assume "next1 ?r1 p (rho ?r1 p) ?msgs (coords (Suc ?r1) p) (rho ?r2 p)"
      with cnd show ?thesis by (auto simp: next1_def phase_def)
    qed
  qed

  txt \<open>The coordinator receives acknowledgements from a majority of processes
    at step $2$ and sets its \<open>ready\<close> flag during the transition at the
    end of step $2$.\<close>
  have 3: "ready (rho ?r3 c)" (is "?P c (Suc (Suc (4*ph)))")
  proof (rule LV_Suc'[OF run, where P="?P"], auto simp: step_def mod_Suc)
    assume "next2 ?r2 c (rho ?r2 c) 
                      (HOrcvdMsgs LV_M ?r2 c (HOs ?r2 c) (rho ?r2))
                      (coords (Suc ?r2) c) (rho ?r3 c)"
    with 2 c2 maj2 show ?thesis
      by (auto simp: mod_Suc step_def LV_CHOMachine_def HOrcvdMsgs_def
                     LV_sendMsg_def next2_def send2_def acksRcvd_def
                     isAck_def phase_def)
  qed

  txt \<open>All processes receive the vote of the coordinator during step $3$
    and decide during the transition at the end of that step.\<close>
  have 4: "\<forall>p. decide (rho ?r4 p) \<noteq> None"
  proof
    fix p
    let ?msgs = "HOrcvdMsgs LV_M ?r3 p (HOs ?r3 p) (rho ?r3)"
    let ?crd = "coord\<Phi> (rho ?r3 p)"
    from run 3 c3 rcv3
    have cnd: "?msgs ?crd \<noteq> None \<and> isVote (the (?msgs ?crd))"
      by (auto elim: readyE
               simp: step_def mod_Suc LV_CHOMachine_def HOrcvdMsgs_def
                     LV_sendMsg_def send3_def isVote_def numeral_3_eq_3)
    show "decide (rho ?r4 p) \<noteq> None" (is "?P p (Suc (Suc (Suc (4*ph))))")
    proof (rule LV_Suc'[OF run, where P="?P"], auto simp: step_def mod_Suc)
      assume "next3 ?r3 p (rho ?r3 p) ?msgs (coords (Suc ?r3) p) (rho ?r4 p)"
      with cnd show "\<exists>v. decide (rho ?r4 p) = Some v"
        by (auto simp: next3_def)
    qed
  qed

  txt \<open>This immediately proves the assertion.\<close>
  from 4 show ?thesis ..
qed


subsection \<open>\emph{LastVoting} Solves Consensus\<close>

text \<open>
  Summing up, all (coarse-grained) runs of \emph{LastVoting} for
  HO collections that satisfy the communication predicate satisfy
  the Consensus property.
\<close>

theorem lv_consensus:
  assumes run: "CHORun LV_M rho HOs coords" 
      and commG: "CHOcommGlobal LV_M HOs coords"
  shows "consensus (x \<circ> (rho 0)) decide rho"
proof -
  \<comment> \<open>the above statement of termination is stronger than what we need\<close>
  from lv_termination[OF assms]
  obtain r where "\<forall>p. decide (rho r p) \<noteq> None" ..
  hence "\<forall>p. \<exists>r. decide (rho r p) \<noteq> None" by blast
  with lv_integrity[OF run] lv_agreement[OF run]
  show ?thesis by (auto simp: consensus_def image_def)
qed

text \<open>
  By the reduction theorem, the correctness of the algorithm carries over
  to the fine-grained model of runs.
\<close>

theorem lv_consensus_fg:
  assumes run: "fg_run LV_M rho HOs HOs coords"
      and commG: "CHOcommGlobal LV_M HOs coords"
  shows "consensus (\<lambda>p. x (state (rho 0) p)) decide (state \<circ> rho)"
    (is "consensus ?inits _ _")
proof (rule local_property_reduction[OF run consensus_is_local])
  fix crun
  assume crun: "CSHORun LV_M crun HOs HOs coords"
     and init: "crun 0 = state (rho 0)"
  from crun have "CHORun LV_M crun HOs coords" 
    by (unfold CHORun_def SHORun_def)
  from this commG have "consensus (x \<circ> (crun 0)) decide crun" 
    by (rule lv_consensus)
  with init show "consensus ?inits decide crun" 
    by (simp add: o_def)
qed

end
