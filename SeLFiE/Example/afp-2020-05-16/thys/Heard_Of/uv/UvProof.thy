theory UvProof
imports UvDefs "../Reduction"
begin

subsection \<open>Preliminary Lemmas\<close>

text \<open>
  At any round, given two processes \<open>p\<close> and \<open>q\<close>, there is always
  some process which is heard by both of them, and from which \<open>p\<close> and
  \<open>q\<close> have received the same message.
\<close>
lemma some_common_msg:
  assumes "HOcommPerRd UV_M (HOs r)"
  shows "\<exists>pq. pq \<in> msgRcvd (HOrcvdMsgs UV_M r p (HOs r p) (rho r))
            \<and> pq \<in> msgRcvd (HOrcvdMsgs UV_M r q (HOs r q) (rho r))
            \<and> (HOrcvdMsgs UV_M r p (HOs r p) (rho r)) pq 
              = (HOrcvdMsgs UV_M r q (HOs r q) (rho r)) pq"
  using assms
  by (auto simp: UV_HOMachine_def UV_commPerRd_def HOrcvdMsgs_def
                 UV_sendMsg_def send0_def send1_def msgRcvd_def)

text \<open>
  When executing step 0, the minimum received value is always well defined.
\<close>

lemma minval_step0:
  assumes com: "HOcommPerRd UV_M (HOs r)" and s0: "step r = 0"
  shows "smallestValRcvd (HOrcvdMsgs UV_M r q (HOs r q) (rho r))
         \<in> {v. \<exists>p. (HOrcvdMsgs UV_M r q (HOs r q) (rho r)) p = Some (Val v)}"
         (is "smallestValRcvd ?msgs \<in> ?vals")
unfolding smallestValRcvd_def proof (rule Min_in)
  have "?vals \<subseteq> getval ` ((the \<circ> ?msgs) ` (HOs r q))"
    by (auto simp: HOrcvdMsgs_def image_def)
  thus "finite ?vals" by (auto simp: finite_subset)
next
  from some_common_msg[of HOs, OF com]
  obtain p where "p \<in> msgRcvd ?msgs" by blast
  with s0 show "?vals \<noteq> {}"
    by (auto simp: msgRcvd_def HOrcvdMsgs_def UV_HOMachine_def 
                   UV_sendMsg_def send0_def)
qed

text \<open>
  When executing step 1 and no vote has been received, the minimum among values received
  in messages carrying no vote is well defined.
\<close>

lemma minval_step1:
  assumes  com: "HOcommPerRd UV_M (HOs r)" and s1: "step r \<noteq> 0"
  and nov: "someVoteRcvd (HOrcvdMsgs UV_M r q (HOs r q) (rho r)) = {}"
  shows "smallestValNoVoteRcvd (HOrcvdMsgs UV_M r q (HOs r q) (rho r))
          \<in> {v . \<exists>p. (HOrcvdMsgs UV_M r q (HOs r q) (rho r)) p
                     = Some (ValVote v None)}"
        (is "smallestValNoVoteRcvd ?msgs \<in> ?vals")
unfolding smallestValNoVoteRcvd_def proof (rule Min_in)
  have "?vals \<subseteq> getval ` ((the \<circ> ?msgs) ` (HOs r q))"
    by (auto simp: HOrcvdMsgs_def image_def)
  thus "finite ?vals" by (auto simp: finite_subset)
next
  from some_common_msg[of HOs, OF com]
  obtain p where "p \<in> msgRcvd ?msgs" by blast
  with s1 nov show "?vals \<noteq> {}"
    by (auto simp: msgRcvd_def HOrcvdMsgs_def someVoteRcvd_def isValVote_def
                   UV_HOMachine_def UV_sendMsg_def send1_def)
qed

text \<open>
  The \<open>vote\<close> field is reset every time a new phase begins. 
\<close>

lemma reset_vote:
  assumes run: "HORun UV_M rho HOs" and s0: "step r' = 0"
  shows "vote (rho r' p) = None"
proof (cases r')
  assume "r' = 0"
  with run show ?thesis
    by (auto simp: UV_HOMachine_def HORun_eq HOinitConfig_eq
                   initState_def UV_initState_def)
next
  fix r
  assume sucr: "r' = Suc r"
  from run
  have nxt: "nextState UV_M r p (rho r p)
                                (HOrcvdMsgs UV_M r p (HOs r p) (rho r)) 
                                (rho (Suc r) p)"
    by (auto simp: UV_HOMachine_def HORun_eq HOnextConfig_eq nextState_def)
  from s0 sucr have "step r = 1" by (auto simp: step_def mod_Suc)
  with nxt sucr show ?thesis
    by (auto simp: UV_HOMachine_def nextState_def UV_nextState_def next1_def)
qed

text \<open>
  Processes only vote for the value they hold in their \<open>x\<close> field.
\<close>
(* The proof relies on previous lemmas @{text reset_vote} and @{text some_common_msg}. *)

lemma x_vote_eq:
  assumes run: "HORun UV_M rho HOs"
      and com: "\<forall>r. HOcommPerRd UV_M (HOs r)"
      and vote: "vote (rho r p) = Some v"
  shows "v = x (rho r p)"
proof (cases r)
  case 0
  with run vote show ?thesis  \<comment> \<open>no vote in initial state\<close>
    by (auto simp: UV_HOMachine_def HORun_eq HOinitConfig_eq 
                   initState_def UV_initState_def)
next
  fix r'
  assume r: "r = Suc r'"
  let ?msgs = "HOrcvdMsgs UV_M r' p (HOs r' p) (rho r')"
  from run have "nextState UV_M r' p (rho r' p) ?msgs (rho (Suc r') p)"
    by (auto simp: HORun_eq HOnextConfig_eq nextState_def)
  with vote r
  have nxt0: "next0 r' p (rho r' p) ?msgs (rho r p)" and s0: "step r' = 0"
    by (auto simp:  nextState_def UV_HOMachine_def UV_nextState_def next1_def)
  from run s0 have "vote (rho r' p) = None" by (rule reset_vote)
  with vote nxt0
  have idv: "\<forall>q \<in> msgRcvd ?msgs. ?msgs q = Some (Val v)"
    and x: "x (rho r p) = smallestValRcvd ?msgs"
    by (auto simp: next0_def)
  moreover
  from com obtain q where "q \<in> msgRcvd ?msgs"
    by (force dest: some_common_msg)
  with idv have "{x . \<exists>qq. ?msgs qq = Some (Val x)} = {v}"
    by (auto simp: msgRcvd_def)
  hence "smallestValRcvd ?msgs = v"
    by (auto simp: smallestValRcvd_def)
  ultimately
  show ?thesis by simp
qed


subsection \<open>Proof of Irrevocability, Agreement and Integrity\<close>


text \<open>A decision can only be taken in the second round of a phase.\<close>

lemma decide_step:
  assumes run: "HORun UV_M rho HOs"
      and decide: "decide (rho (Suc r) p) \<noteq> decide (rho r p)" 
  shows "step r = 1"
proof -
  let ?msgs = "HOrcvdMsgs UV_M r p (HOs r p) (rho r)"
  from run have "nextState UV_M r p (rho r p) ?msgs (rho (Suc r) p)"
    by (auto simp: HORun_eq HOnextConfig_eq nextState_def)
  with decide show ?thesis
    by (auto simp: nextState_def UV_HOMachine_def UV_nextState_def
                   next0_def step_def)
qed

text \<open>No process ever decides \<open>None\<close>.\<close>
lemma decide_nonnull:
  assumes run: "HORun UV_M rho HOs"
      and decide: "decide (rho (Suc r) p) \<noteq> decide (rho r p)" 
  shows "decide (rho (Suc r) p) \<noteq> None"
proof -
  let ?msgs = "HOrcvdMsgs UV_M r p (HOs r p) (rho r)"
  from assms have s1: "step r = 1" by (rule decide_step)
  with run have "next1 r p (rho r p) ?msgs (rho (Suc r) p)"
    by (auto simp: UV_HOMachine_def HORun_eq HOnextConfig_eq
                   nextState_def UV_nextState_def)
  with decide show ?thesis
    by (auto simp: next1_def dec_update_def)
qed

text \<open>
  If some process \<open>p\<close> votes for \<open>v\<close> at some round \<open>r\<close>, then any message
  that \<open>p\<close> received in \<open>r\<close> was holding \<open>v\<close> as a value.
\<close>

lemma msgs_unanimity:
  assumes run: "HORun UV_M rho HOs"
      and vote: "vote (rho (Suc r) p) = Some v"
      and q: "q \<in> msgRcvd (HOrcvdMsgs UV_M r p (HOs r p) (rho r))"
             (is "_ \<in> msgRcvd ?msgs")
  shows "getval (the (?msgs q)) = v"
proof -
  have s0: "step r = 0"
  proof (rule ccontr)
    assume "step r \<noteq> 0"
    hence "step (Suc r) = 0" by (simp add: step_def mod_Suc)
    with run vote show False by (auto simp: reset_vote)
  qed
  with run have novote: "vote (rho r p) = None" by (auto simp: reset_vote)
  from run have "nextState UV_M r p (rho r p) ?msgs (rho (Suc r) p)"
    by (auto simp: HORun_eq HOnextConfig_eq nextState_def)
  with s0 have nxt: "next0 r p (rho r p) ?msgs (rho (Suc r) p)"
    by (auto simp: UV_HOMachine_def nextState_def UV_nextState_def)
  with novote vote q show ?thesis by (auto simp: next0_def)
qed

text \<open>
  Any two processes can only vote for the same value.
\<close>
(* The proof relies on previous lemmas @{text some_common_msg} and @{text msgs_unanimity}. *)

lemma vote_agreement:
  assumes run: "HORun UV_M rho HOs"
      and com: "\<forall>r. HOcommPerRd UV_M (HOs r)"
      and p: "vote (rho r p) = Some v"
      and q: "vote (rho r q) = Some w"
  shows "v = w"
proof (cases r)
  case 0
  with run p show ?thesis  \<comment> \<open>no votes in initial state\<close>
    by (auto simp: UV_HOMachine_def HORun_eq HOinitConfig_eq
                   initState_def UV_initState_def)
next
  fix r'
  assume r: "r = Suc r'"
  let "?msgs p" = "HOrcvdMsgs UV_M r' p (HOs r' p) (rho r')"
  from com obtain pq
    where "?msgs p pq = ?msgs q pq"
      and smp: "pq \<in> msgRcvd (?msgs p)" and smq: "pq \<in> msgRcvd (?msgs q)"
    by (force dest: some_common_msg)
  moreover
  from run p smp r have "getval (the (?msgs p pq)) = v"
    by (simp add: msgs_unanimity)
  moreover
  from run q smq r have "getval (the (?msgs q pq)) = w"
    by (simp add: msgs_unanimity)
  ultimately
  show ?thesis by simp
qed

text \<open>
  If a process decides value \<open>v\<close> then all processes must have \<open>v\<close>
  in their \<open>x\<close> fields.
\<close>
(* The proof relies on previous lemmas @{text decide_step}, @{text some_common_msg},
   @{text vote_agreement}. *)

lemma decide_equals_x:
  assumes run: "HORun UV_M rho HOs"
      and com: "\<forall>r. HOcommPerRd UV_M (HOs r)"
      and decide: "decide (rho (Suc r) p) \<noteq> decide (rho r p)"
      and decval: "decide (rho (Suc r) p) = Some v"
  shows "x (rho (Suc r) q) = v"
proof -
  let "?msgs p'" = "HOrcvdMsgs UV_M r p' (HOs r p') (rho r)"
  from run decide have s1: "step r = 1" by (rule decide_step)
  from run have "nextState UV_M r p (rho r p) (?msgs p) (rho (Suc r) p)"
    by (auto simp: HORun_eq HOnextConfig_eq nextState_def)
  with s1 have nxtp: "next1 r p (rho r p) (?msgs p) (rho (Suc r) p)"
    by (auto simp: UV_HOMachine_def nextState_def UV_nextState_def)
  from run have "nextState UV_M r q (rho r q) (?msgs q) (rho (Suc r) q)"
    by (auto simp: HORun_eq HOnextConfig_eq nextState_def)
  with s1 have nxtq: "next1 r q (rho r q) (?msgs q) (rho (Suc r) q)"
    by (auto simp: UV_HOMachine_def nextState_def UV_nextState_def)

  from com obtain pq where
    pq: "pq \<in> msgRcvd (?msgs p)" "pq \<in> msgRcvd (?msgs q)" 
        "(?msgs p) pq = (?msgs q) pq"
    by (force dest: some_common_msg)
  with decide decval nxtp
  have vote: "isValVote (the (?msgs p pq))"
             "getvote (the (?msgs p pq)) = Some v"
    by (auto simp: next1_def dec_update_def identicalVoteRcvd_def)
  with nxtq pq obtain q' where
    q': "q' \<in> someVoteRcvd (?msgs q)"
        "x (rho (Suc r) q) = the (getvote (the (?msgs q q')))"
    by (auto simp: next1_def x_update_def someVoteRcvd_def)
  with s1 pq vote show ?thesis
    by (auto simp: HOrcvdMsgs_def UV_HOMachine_def UV_sendMsg_def send1_def
                   someVoteRcvd_def msgRcvd_def vote_agreement[OF run com])
qed

text \<open>
  If at some point all processes hold value \<open>v\<close> in their \<open>x\<close>
  fields, then this will still be the case at the next step.
\<close>
(* The proof relies on the previous lemma @{text x_vote_eq}. *)

lemma same_x_stable:
  assumes run: "HORun UV_M rho HOs"
      and comm: "\<forall>r. HOcommPerRd UV_M (HOs r)"
      and x: "\<forall>p. x (rho r p) = v"
  shows "x (rho (Suc r) q) = v"
proof -
  let ?msgs = "HOrcvdMsgs UV_M r q (HOs r q) (rho r)"
  from comm obtain p where p: "p \<in> msgRcvd ?msgs"
    by (force dest: some_common_msg)
  from run have "nextState UV_M r q (rho r q) ?msgs (rho (Suc r) q)"
    by (auto simp: HORun_eq HOnextConfig_eq nextState_def)
  hence "next0 r q (rho r q) ?msgs (rho (Suc r) q) \<and> step r = 0
         \<or> next1 r q (rho r q) ?msgs (rho (Suc r) q) \<and> step r \<noteq> 0"
    (is "?nxt0 \<or> ?nxt1")
    by (auto simp: UV_HOMachine_def nextState_def UV_nextState_def)
  thus ?thesis
  proof
    assume nxt0: "?nxt0"
    hence "x (rho (Suc r) q) = smallestValRcvd ?msgs"
      by (auto simp: next0_def)
    moreover
    from nxt0 x have "\<forall>p \<in> msgRcvd ?msgs. ?msgs p = Some (Val v)"
      by (auto simp: UV_HOMachine_def HOrcvdMsgs_def UV_sendMsg_def
                     msgRcvd_def send0_def)
    from this p have "{x . \<exists>p. ?msgs p = Some (Val x)} = {v}"
      by (auto simp: msgRcvd_def)
    hence "smallestValRcvd ?msgs = v"
      by (auto simp: smallestValRcvd_def)
    ultimately
    show ?thesis by simp
  next
    assume nxt1: "?nxt1"
    show ?thesis
    proof (cases "someVoteRcvd ?msgs = {}")
      case True
      with nxt1 have "x (rho (Suc r) q) = smallestValNoVoteRcvd ?msgs"
        by (auto simp: next1_def x_update_def)
      moreover
      from nxt1 x True 
      have "\<forall>p \<in> msgRcvd ?msgs. ?msgs p = Some (ValVote v None)"
        by (auto simp: UV_HOMachine_def HOrcvdMsgs_def UV_sendMsg_def
                       msgRcvd_def send1_def someVoteRcvd_def isValVote_def)
      from this p have "{x . \<exists>p. ?msgs p = Some (ValVote x None)} = {v}"
        by (auto simp: msgRcvd_def)
      hence "smallestValNoVoteRcvd ?msgs = v"
        by (auto simp: smallestValNoVoteRcvd_def)
      ultimately show ?thesis by simp
    next
      case False
      with nxt1 obtain p' v' where
        p': "p' \<in> msgRcvd ?msgs" "isValVote (the (?msgs p'))"
            "getvote (the (?msgs p')) = Some v'""x (rho (Suc r) q) = v'"
        by (auto simp: someVoteRcvd_def next1_def x_update_def)
      with nxt1 have "x (rho (Suc r) q) = x (rho r p')"
        by (auto simp: UV_HOMachine_def HOrcvdMsgs_def UV_sendMsg_def
                       msgRcvd_def send1_def isValVote_def
                       x_vote_eq[OF run comm])
      with x show ?thesis by auto
    qed
  qed
qed

text \<open>
  Combining the last two lemmas, it follows that as soon as some process
  decides value \<open>v\<close>, all processes hold \<open>v\<close> in their \<open>x\<close> fields.
\<close>

lemma safety_argument:
  assumes run: "HORun UV_M rho HOs"
      and com: "\<forall>r. HOcommPerRd UV_M (HOs r)"
      and decide: "decide (rho (Suc r) p) \<noteq> decide (rho r p)"
      and decval: "decide (rho (Suc r) p) = Some v"
  shows "x (rho (Suc r+k) q) = v"
proof (induct k arbitrary: q)
  fix q
  from decide_equals_x[OF assms] show "x (rho (Suc r + 0) q) = v" by simp
next
  fix k q
  assume "\<And>q. x (rho (Suc r+k) q) = v"
  with run com show "x (rho (Suc r + Suc k) q) = v"
    by (auto dest: same_x_stable)
qed

text \<open>
  Any process that holds a non-null decision value has made a decision
  sometime in the past.
\<close>

lemma decided_then_past_decision:
  assumes run: "HORun UV_M rho HOs"
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
      by (auto simp: HORun_eq UV_HOMachine_def HOinitConfig_eq
                     initState_def UV_initState_def)
  next
    fix n
    assume ih: "?P n" thus "?P (Suc n)" by force
  qed
  with dec show ?thesis by auto
qed

text \<open>
  We can now prove the safety properties of the algorithm, and start with
  proving Integrity.
\<close>

lemma x_values_initial:
  assumes run:"HORun UV_M rho HOs"
      and com:"\<forall>r. HOcommPerRd UV_M (HOs r)"
  shows "\<exists>q. x (rho r p) = x (rho 0 q)"
proof (induct r arbitrary: p)
  fix p
  show "\<exists>q. x (rho 0 p) = x (rho 0 q)" by auto
next
  fix r p
  assume ih: "\<And>p'. \<exists>q. x (rho r p') = x (rho 0 q)"
  let ?msgs = "HOrcvdMsgs UV_M r p (HOs r p) (rho r)"
  from run have "nextState UV_M r p (rho r p) ?msgs (rho (Suc r) p)"
    by (auto simp: HORun_eq HOnextConfig_eq nextState_def)
  hence "next0 r p (rho r p) ?msgs (rho (Suc r) p) \<and> step r = 0
         \<or> next1 r p (rho r p) ?msgs (rho (Suc r) p) \<and> step r \<noteq> 0"
    (is "?nxt0 \<or> ?nxt1")
    by (auto simp: UV_HOMachine_def nextState_def UV_nextState_def)
  thus "\<exists>q. x (rho (Suc r) p) = x (rho 0 q)"
  proof
    assume nxt0: "?nxt0"
    hence "x (rho (Suc r) p) = smallestValRcvd ?msgs"
      by (auto simp: next0_def)
    also with com nxt0 have "\<dots> \<in> {v . \<exists>q. ?msgs q = Some (Val v)}"
      by (intro minval_step0) auto
    also with nxt0 have "\<dots> = { x (rho r q) | q . q \<in> msgRcvd ?msgs }"
      by (auto simp: UV_HOMachine_def HOrcvdMsgs_def UV_sendMsg_def 
                     msgRcvd_def send0_def)
    finally obtain q where "x (rho (Suc r) p) = x (rho r q)" by auto
    with ih show ?thesis by auto
  next
    assume nxt1: "?nxt1"
    show ?thesis
    proof (cases "someVoteRcvd ?msgs = {}")
      case True
      with nxt1 have "x (rho (Suc r) p) = smallestValNoVoteRcvd ?msgs"
        by (auto simp: next1_def x_update_def)
      also with com nxt1 True
      have "\<dots> \<in> {v . \<exists>q. ?msgs q = Some (ValVote v None)}"
        by (intro minval_step1) auto
      also with nxt1 True
      have "\<dots> = { x (rho r q) | q . q \<in> msgRcvd ?msgs }"
        by (auto simp: UV_HOMachine_def HOrcvdMsgs_def UV_sendMsg_def 
                       someVoteRcvd_def isValVote_def msgRcvd_def send1_def)
      finally obtain q where "x (rho (Suc r) p) = x (rho r q)" by auto
      with ih show ?thesis by auto
    next
      case False
      with nxt1 obtain q where
        "q \<in> someVoteRcvd ?msgs" 
        "x (rho (Suc r) p) = the (getvote (the (?msgs q)))"
        by (auto simp: next1_def x_update_def)
      with nxt1 have "vote (rho r q) = Some (x (rho (Suc r) p))"
        by (auto simp: UV_HOMachine_def HOrcvdMsgs_def UV_sendMsg_def 
                       someVoteRcvd_def isValVote_def msgRcvd_def send1_def)
      with run com have "x (rho (Suc r) p) = x (rho r q)"
        by (rule x_vote_eq)
      with ih show ?thesis by auto
    qed
  qed
qed

theorem uv_integrity:
  assumes run: "HORun UV_M rho HOs"
      and com: "\<forall>r. HOcommPerRd UV_M (HOs r)"
      and dec: "decide (rho r p) = Some v"
  shows "\<exists>q. v = x (rho 0 q)"
proof -
  from run dec obtain k where
    "decide (rho (Suc k) p) \<noteq> decide (rho k p)"
    "decide (rho (Suc k) p) = Some v"
    by (auto dest: decided_then_past_decision)
  with run com have "x (rho (Suc k) p) = v"
    by (rule decide_equals_x)
  with run com show ?thesis 
    by (auto dest: x_values_initial)
qed

text \<open>
  We now turn to Agreement.
\<close>

lemma two_decisions_agree:
  assumes run: "HORun UV_M rho HOs"
      and com: "\<forall>r. HOcommPerRd UV_M (HOs r)"
      and decidep: "decide (rho (Suc r) p) \<noteq> decide (rho r p)"
      and decvalp: "decide (rho (Suc r) p) = Some v"
      and decideq: "decide (rho (Suc (r+k)) q) \<noteq> decide (rho (r+k) q)"
      and decvalq: "decide (rho (Suc (r+k)) q) = Some w"
  shows "v = w"
proof -
  from run com decidep decvalp have "x (rho (Suc r+k) q) = v"
    by (rule safety_argument)
  moreover
  from run com decideq decvalq have "x (rho (Suc (r+k)) q) = w"
    by (rule decide_equals_x)
  ultimately
  show ?thesis by simp
qed

theorem uv_agreement:
  assumes run: "HORun UV_M rho HOs"
      and com: "\<forall>r. HOcommPerRd UV_M (HOs r)"
      and p: "decide (rho m p) = Some v"
      and q: "decide (rho n q) = Some w"
  shows "v = w"
proof -
  from run p obtain k where
    k: "decide (rho (Suc k) p) \<noteq> decide (rho k p)"
       "decide (rho (Suc k) p) = Some v"
    by (auto dest: decided_then_past_decision)
  from run q obtain l where
    l: "decide (rho (Suc l) q) \<noteq> decide (rho l q)"
       "decide (rho (Suc l) q) = Some w"
    by (auto dest: decided_then_past_decision)
  show ?thesis
  proof (cases "k \<le> l")
    case True
    then obtain m where m: "l = k+m" by (auto simp: le_iff_add)
    from run com k l m show ?thesis by (blast dest: two_decisions_agree)
  next
    case False
    hence "l \<le> k" by simp
    then obtain m where m: "k = l+m" by (auto simp: le_iff_add)
    from run com k l m show ?thesis by (blast dest: two_decisions_agree)
  qed
qed

text \<open>
  Irrevocability is a consequence of Agreement and the fact that no process
  can decide \<open>None\<close>.
\<close>

theorem uv_irrevocability:
  assumes run: "HORun UV_M rho HOs"
      and com: "\<forall>r. HOcommPerRd UV_M (HOs r)"
      and p: "decide (rho m p) = Some v"
  shows "decide (rho (m+n) p) = Some v"
proof (induct n)
  from p show "decide (rho (m+0) p) = Some v" by simp
next
  fix n
  assume ih: "decide (rho (m+n) p) = Some v"
  show "decide (rho (m + Suc n) p) = Some v"
  proof (rule classical)
    assume "\<not> ?thesis"
    with run ih obtain w where w: "decide (rho (m + Suc n) p) = Some w"
      by (auto dest!: decide_nonnull)
    with p have "w = v" by (auto simp: uv_agreement[OF run com])
    with w show ?thesis by simp
  qed
qed


subsection \<open>Proof of Termination\<close>

text \<open>
  Two processes having the same \emph{Heard-Of} set at some round will
  hold the same value in their \<open>x\<close> variable at the next round.
\<close>
(* The proof relies on the previous lemma @{text vote_agreement}. *)

lemma hoeq_xeq:
  assumes run: "HORun UV_M rho HOs"
      and com: "\<forall>r. HOcommPerRd UV_M (HOs r)"
      and hoeq: "HOs r p = HOs r q"
  shows "x (rho (Suc r) p) = x (rho (Suc r) q)"
proof -
  let "?msgs p" = "HOrcvdMsgs UV_M r p (HOs r p) (rho r)"
  from hoeq have msgeq: "?msgs p = ?msgs q"
    by (auto simp: UV_HOMachine_def HOrcvdMsgs_def UV_sendMsg_def 
                   send0_def send1_def)
 
  show ?thesis
  proof (cases "step r = 0")
    case True
    with run
    have "\<forall>p. next0 r p (rho r p) (?msgs p) (rho (Suc r) p)" (is "\<forall>p. ?nxt0 p")
      by (force simp: UV_HOMachine_def HORun_eq HOnextConfig_eq
                      nextState_def UV_nextState_def)
    hence "?nxt0 p" "?nxt0 q" by auto
    with msgeq show ?thesis by (auto simp: next0_def)
  next
    assume stp: "step r \<noteq> 0"
    with run
    have "\<forall>p. next1 r p (rho r p) (?msgs p) (rho (Suc r) p)" (is "\<forall>p. ?nxt1 p")
      by (force simp: UV_HOMachine_def HORun_eq HOnextConfig_eq
                      nextState_def UV_nextState_def)
    hence "x_update (rho r p) (?msgs p) (rho (Suc r) p)"
          "x_update (rho r q) (?msgs q) (rho (Suc r) q)"
      by (auto simp: next1_def)
    with msgeq have
      x': "x_update (rho r p) (?msgs p) (rho (Suc r) p)"
          "x_update (rho r q) (?msgs p) (rho (Suc r) q)"
      by auto
    show ?thesis
    proof (cases "someVoteRcvd (?msgs p) = {}")
      case True
      with x' show ?thesis
        by (auto simp: x_update_def)
    next
      case False
      with x' stp obtain qp qq where
        "vote (rho r qp) = Some (x (rho (Suc r) p))" and
        "vote (rho r qq) = Some (x (rho (Suc r) q))"
        by (force simp: UV_HOMachine_def HOrcvdMsgs_def UV_sendMsg_def 
                        x_update_def someVoteRcvd_def isValVote_def 
                        msgRcvd_def send1_def)
      with run com show ?thesis by (rule vote_agreement)
    qed
  qed
qed

text \<open>
  We now prove that \emph{UniformVoting} terminates.
\<close>

theorem uv_termination:
  assumes run: "HORun UV_M rho HOs"
      and commR: "\<forall>r. HOcommPerRd UV_M (HOs r)"
      and commG: "HOcommGlobal UV_M HOs"
  shows "\<exists>r v. decide (rho r p) = Some v"
proof -
  txt \<open>First obtain a round where all \<open>x\<close> values agree.\<close>
  from commG obtain r0 where r0: "\<forall>q. HOs r0 q = HOs r0 p"
    by (force simp: UV_HOMachine_def UV_commGlobal_def)
  let ?v = "x (rho (Suc r0) p)"
  from run commR r0 have xs: "\<forall>q. x (rho (Suc r0) q) = ?v"
    by (auto dest: hoeq_xeq)

  txt \<open>Now obtain a round where all votes agree.\<close>
  define r' where "r' = (if step (Suc r0) = 0 then Suc r0 else Suc (Suc r0))"
  have stp': "step r' = 0"
    by (simp add: r'_def step_def mod_Suc)
  have x': "\<forall>q. x (rho r' q) = ?v"
  proof (auto simp: r'_def)
    fix q
    from xs show "x (rho (Suc r0) q) = ?v" ..
  next
    fix q
    from run commR xs show "x (rho (Suc (Suc r0)) q) = ?v"
      by (rule same_x_stable)
  qed
  have vote': "\<forall>q. vote (rho (Suc r') q) = Some ?v"
  proof
    fix q
    let ?msgs = "HOrcvdMsgs UV_M r' q (HOs r' q) (rho r')"
    from run stp' have "next0 r' q (rho r' q) ?msgs (rho (Suc r') q)"
      by (force simp: UV_HOMachine_def HORun_eq HOnextConfig_eq
                      nextState_def UV_nextState_def)
    moreover
    from stp' x' have "\<forall>q' \<in> msgRcvd ?msgs. ?msgs q' = Some (Val ?v)"
      by (auto simp: UV_HOMachine_def HOrcvdMsgs_def UV_sendMsg_def 
                     send0_def msgRcvd_def)
    moreover
    from commR have "msgRcvd ?msgs \<noteq> {}"
      by (force dest: some_common_msg)
    ultimately
    show "vote (rho (Suc r') q) = Some ?v"
      by (auto simp: next0_def)
  qed

  txt \<open>At the subsequent round, process \<open>p\<close> will decide.\<close>
  let ?r'' = "Suc r'"
  let ?msgs' = "HOrcvdMsgs UV_M ?r'' p (HOs ?r'' p) (rho ?r'')"
  from stp' have stp'': "step ?r'' = 1"
    by (simp add: step_def mod_Suc)
  with run have "next1 ?r'' p (rho ?r'' p) ?msgs' (rho (Suc ?r'') p)"
    by (auto simp: UV_HOMachine_def HORun_eq HOnextConfig_eq
                   nextState_def UV_nextState_def)
  moreover
  from stp'' vote' have "identicalVoteRcvd ?msgs' ?v"
    by (auto simp: UV_HOMachine_def HOrcvdMsgs_def UV_sendMsg_def
                   send1_def identicalVoteRcvd_def isValVote_def msgRcvd_def)
  moreover
  from commR have "msgRcvd ?msgs' \<noteq> {}"
    by (force dest: some_common_msg)
  ultimately
  have "decide (rho (Suc ?r'') p) = Some ?v"
    by (force simp: next1_def dec_update_def identicalVoteRcvd_def
                    msgRcvd_def isValVote_def)
  (* subtle point: there can't be two different identical votes received,
     proving this requires "force" and takes a while *)

  thus ?thesis by blast
qed


subsection \<open>\emph{UniformVoting} Solves Consensus\<close>

text \<open>
  Summing up, all (coarse-grained) runs of \emph{UniformVoting} for
  HO collections that satisfy the communication predicate satisfy
  the Consensus property.
\<close>

theorem uv_consensus:
  assumes run: "HORun UV_M rho HOs" 
      and commR: "\<forall>r. HOcommPerRd UV_M (HOs r)"
      and commG: "HOcommGlobal UV_M HOs"
  shows "consensus (x \<circ> (rho 0)) decide rho"
  using assms unfolding consensus_def image_def
  by (auto elim: uv_integrity uv_agreement uv_termination)

text \<open>
  By the reduction theorem, the correctness of the algorithm carries over
  to the fine-grained model of runs.
\<close>

theorem uv_consensus_fg:
  assumes run: "fg_run UV_M rho HOs HOs (\<lambda>r q. undefined)"
      and commR: "\<forall>r. HOcommPerRd UV_M (HOs r)"
      and commG: "HOcommGlobal UV_M HOs"
  shows "consensus (\<lambda>p. x (state (rho 0) p)) decide (state \<circ> rho)"
    (is "consensus ?inits _ _")
proof (rule local_property_reduction[OF run consensus_is_local])
  fix crun
  assume crun: "CSHORun UV_M crun HOs HOs (\<lambda>r q. undefined)"
     and init: "crun 0 = state (rho 0)"
  from crun have "HORun UV_M crun HOs" 
    by (unfold HORun_def SHORun_def)
  from this commR commG have "consensus (x \<circ> (crun 0)) decide crun"
    by (rule uv_consensus)
  with init show "consensus ?inits decide crun" 
    by (simp add: o_def)
qed


end
