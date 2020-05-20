theory UteProof
imports UteDefs "../Majorities" "../Reduction"
begin

context ute_parameters
begin

subsection \<open>Preliminary Lemmas\<close>

text \<open>Processes can make a vote only at first round of each phase.\<close>

lemma vote_step:
  assumes  nxt: "nextState Ute_M r p (rho r p) \<mu> (rho (Suc r) p)"
  and "vote (rho (Suc r) p) \<noteq> None"
  shows "step r = 0"
proof (rule ccontr)
  assume "step r \<noteq> 0"
  with assms have "vote (rho (Suc r) p) = None"
    by (auto simp:Ute_SHOMachine_def nextState_def Ute_nextState_def next1_def)
  with assms show False by auto
qed

text \<open>Processes can make a new decision only at second round of each phase.\<close>

lemma decide_step:
  assumes run: "SHORun Ute_M rho HOs SHOs"
  and d1: "decide (rho r p) \<noteq> Some v"
  and d2: "decide (rho (Suc r) p) = Some v"
  shows "step r \<noteq> 0"
proof
  assume sr:"step r = 0"
  from run obtain \<mu> where "Ute_nextState r p (rho r p) \<mu> (rho (Suc r) p)"
    unfolding Ute_SHOMachine_def nextState_def SHORun_eq SHOnextConfig_eq 
    by force
  with sr have "next0 r p (rho r p) \<mu> (rho (Suc r) p)"
    unfolding Ute_nextState_def by auto
  hence "decide (rho r p) = decide (rho (Suc r) p)" 
    by (auto simp:next0_def)
  with d1 d2 show False by auto
qed

lemma unique_majority_E:
  assumes majv: "card {qq::Proc. F qq = Some m} > E"
  and majw: "card {qq::Proc. F qq = Some m'} > E"
  shows "m = m'"
proof -
  from majv majw majE 
  have "card {qq::Proc. F qq = Some m} > N div 2"
    and "card {qq::Proc. F qq = Some m'} > N div 2"
    by auto
  then obtain qq
    where "qq \<in> {qq::Proc. F qq = Some m}"
      and "qq \<in> {qq::Proc. F qq = Some m'}"
    by (rule majoritiesE')
  thus ?thesis by auto
qed

lemma unique_majority_E_\<alpha>:
  assumes majv: "card {qq::Proc. F qq = m} > E - \<alpha>"
  and majw: "card {qq::Proc. F qq = m'} > E - \<alpha>"
  shows "m = m'"
proof -
  from majE alpha_lt_N majv majw
  have "card {qq::Proc. F qq = m} > N div 2"
    and "card {qq::Proc. F qq = m'} > N div 2"
    by auto
  then obtain qq
    where "qq \<in> {qq::Proc. F qq = m}"
      and "qq \<in> {qq::Proc. F qq = m'}"
    by (rule majoritiesE')
  thus ?thesis by auto
qed

lemma unique_majority_T:
  assumes majv: "card {qq::Proc. F qq = Some m} > T"
  and majw: "card {qq::Proc. F qq = Some m'} > T"
  shows "m = m'"
proof -
  from majT majv majw
  have "card {qq::Proc. F qq = Some m} > N div 2"
    and "card {qq::Proc. F qq = Some m'} > N div 2"
    by auto
  then obtain qq
    where "qq \<in> {qq::Proc. F qq = Some m}"
      and "qq \<in> {qq::Proc. F qq = Some m'}"
    by (rule majoritiesE')
  thus ?thesis by auto
qed

text \<open>No two processes may vote for different values in the same round.\<close>

lemma common_vote:
  assumes usafe: "SHOcommPerRd Ute_M HO SHO"
  and nxtp: "nextState Ute_M r p (rho r p)  \<mu>p (rho (Suc r) p)"
  and mup: "\<mu>p \<in> SHOmsgVectors Ute_M r p (rho r) (HO p) (SHO p)"
  and nxtq: "nextState Ute_M r q (rho r q)  \<mu>q (rho (Suc r) q)"
  and muq: "\<mu>q \<in> SHOmsgVectors Ute_M r q (rho r) (HO q) (SHO q)"
  and vp: "vote (rho (Suc r) p) = Some vp"
  and vq: "vote (rho (Suc r) q) = Some vq"
  shows "vp = vq"
using assms proof -
  have gtn: "card {qq. sendMsg Ute_M r qq p (rho r qq) = Val vp}
           + card {qq. sendMsg Ute_M r qq q (rho r qq) = Val vq} > N"
  proof -
    have "card {qq. sendMsg Ute_M r qq p (rho r qq) = Val vp} > T - \<alpha>
        \<and> card {qq. sendMsg Ute_M r qq q (rho r qq) = Val vq} > T - \<alpha>"
      (is "card ?vsentp > _ \<and> card ?vsentq > _")
    proof -
      from nxtp vp have stp:"step r = 0" by (auto simp: vote_step)
      from mup
      have "{qq. \<mu>p qq = Some (Val vp)} - (HO p - SHO p) 
             \<subseteq> {qq. sendMsg Ute_M r qq p (rho r qq) = Val vp}"
             (is "?vrcvdp - ?ahop \<subseteq> ?vsentp") 
         by (auto simp: SHOmsgVectors_def)
      hence "card (?vrcvdp - ?ahop) \<le> card ?vsentp"
        and "card (?vrcvdp - ?ahop) \<ge> card ?vrcvdp - card ?ahop"
        by (auto simp: card_mono diff_card_le_card_Diff)
      hence "card ?vsentp \<ge> card ?vrcvdp - card ?ahop" by auto
      moreover
      from nxtp stp have "next0 r p (rho r p) \<mu>p (rho (Suc r) p)"
        by (auto simp: Ute_SHOMachine_def nextState_def Ute_nextState_def)
      with vp have "card ?vrcvdp > T"
        unfolding next0_def by auto
      moreover
      from muq
      have "{qq. \<mu>q qq = Some (Val vq)} - (HO q - SHO q)
             \<subseteq> {qq. sendMsg Ute_M r qq q (rho r qq) = Val vq}"
             (is "?vrcvdq - ?ahoq \<subseteq> ?vsentq") 
        by (auto simp: SHOmsgVectors_def)
      hence "card (?vrcvdq - ?ahoq) \<le> card ?vsentq"
        and "card (?vrcvdq - ?ahoq) \<ge> card ?vrcvdq - card ?ahoq"
        by (auto simp: card_mono diff_card_le_card_Diff)
      hence "card ?vsentq \<ge> card ?vrcvdq - card ?ahoq" by auto
      moreover
      from nxtq stp have "next0 r q (rho r q) \<mu>q (rho (Suc r) q)"
        by (auto simp: Ute_SHOMachine_def nextState_def Ute_nextState_def)
      with vq have "card {qq. \<mu>q qq = Some (Val vq)} > T" 
        by (unfold next0_def, auto)
      moreover
      from usafe have "card ?ahop \<le> \<alpha>" and "card ?ahoq \<le> \<alpha>"
        by (auto simp: Ute_SHOMachine_def Ute_commPerRd_def)
      ultimately
      show ?thesis using alpha_lt_T by auto
    qed
    thus ?thesis using majT by auto
  qed

  show ?thesis
  proof (rule ccontr)
    assume vpq:"vp \<noteq> vq"
    have "\<forall>qq. sendMsg Ute_M r qq p (rho r qq)
               = sendMsg Ute_M r qq q (rho r qq)"
      by (auto simp: Ute_SHOMachine_def Ute_sendMsg_def 
                     step_def send0_def send1_def)
    with vpq 
    have "{qq. sendMsg Ute_M r qq p (rho r qq) = Val vp} 
           \<inter> {qq. sendMsg Ute_M r qq q (rho r qq) = Val vq} = {}" 
      by auto
    with gtn
    have "card ({qq. sendMsg Ute_M r qq p (rho r qq) = Val vp} 
                  \<union> {qq. sendMsg Ute_M r qq q (rho r qq) = Val vq}) > N"
      by (auto simp: card_Un_Int)
    moreover
    have "card ({qq. sendMsg Ute_M r qq p (rho r qq) = Val vp} 
                  \<union> {qq. sendMsg Ute_M r qq q (rho r qq) = Val vq}) \<le> N"
      by (auto simp: card_mono)
    ultimately
    show "False" by auto
  qed
qed

text \<open>
  No decision may be taken by a process unless it received enough messages
  holding the same value.
\<close>
(*
  The proof mainly relies on lemma @{text decide_step}
  and the @{text Ute_commPerRound} predicate. 
*)

lemma decide_with_threshold_E:
  assumes run: "SHORun Ute_M rho HOs SHOs" 
  and usafe: "SHOcommPerRd Ute_M (HOs r) (SHOs r)"
  and d1: "decide (rho r p) \<noteq> Some v"
  and d2: "decide (rho (Suc r) p) = Some v"
  shows "card {q. sendMsg Ute_M r q p (rho r q) = Vote (Some v)}
           > E - \<alpha>"
proof -
  from run obtain \<mu>p
    where nxt:"nextState Ute_M r p (rho r p) \<mu>p (rho (Suc r) p)"
      and "\<forall>qq. qq \<in> HOs r p \<longleftrightarrow> \<mu>p qq \<noteq> None"
      and "\<forall>qq. qq \<in> SHOs r p \<inter> HOs r p 
                \<longrightarrow> \<mu>p qq = Some (sendMsg Ute_M r qq p (rho r qq))"
    unfolding Ute_SHOMachine_def SHORun_eq SHOnextConfig_eq SHOmsgVectors_def
    by blast
  hence "{qq. \<mu>p qq = Some (Vote (Some v))} - (HOs r p - SHOs r p)
          \<subseteq> {qq. sendMsg Ute_M r qq p (rho r qq) = Vote (Some v)}"
         (is "?vrcvdp - ?ahop \<subseteq> ?vsentp") by auto
  hence "card (?vrcvdp - ?ahop) \<le> card ?vsentp"
    and "card (?vrcvdp - ?ahop) \<ge> card ?vrcvdp - card ?ahop"
    by (auto simp: card_mono diff_card_le_card_Diff)
  hence "card ?vsentp \<ge> card ?vrcvdp - card ?ahop" by auto
  moreover
  from usafe have "card (HOs r p - SHOs r p) \<le> \<alpha>"
    by (auto simp: Ute_SHOMachine_def Ute_commPerRd_def)
  moreover
  from run d1 d2 have "step r \<noteq> 0" by (rule decide_step)
  with nxt have "next1 r p (rho r p) \<mu>p (rho (Suc r) p)"
    by (auto simp: Ute_SHOMachine_def nextState_def Ute_nextState_def)
  with run d1 d2 have "card {qq. \<mu>p qq = Some (Vote (Some v))} > E"
    unfolding next1_def by auto
  ultimately
  show ?thesis using alpha_lt_E by auto
qed

subsection \<open>Proof of Agreement and Validity\<close>

text \<open>
  If more than \<open>E - \<alpha>\<close> messages holding \<open>v\<close> are sent to
  some process \<open>p\<close> at round \<open>r\<close>, then every process \<open>pp\<close>
  correctly receives more than \<open>\<alpha>\<close> such messages.
\<close>
(*
  The proof mainly relies on the @{text Ute_commPerRound} predicate. 
*)

lemma common_x_argument_1:
  assumes usafe:"SHOcommPerRd Ute_M (HOs (Suc r)) (SHOs (Suc r))"
  and threshold: "card {q. sendMsg Ute_M (Suc r) q p (rho (Suc r) q) 
                            = Vote (Some v)} > E - \<alpha>"
                 (is "card (?msgs p v) > _")
  shows "card (?msgs pp v \<inter> (SHOs (Suc r) pp \<inter> HOs (Suc r) pp)) > \<alpha>"
proof -
  have "card (?msgs pp v) + card (SHOs (Suc r) pp \<inter> HOs (Suc r) pp) > N + \<alpha>"
  proof -
    have "\<forall>q. sendMsg Ute_M (Suc r) q p (rho (Suc r) q) 
                = sendMsg Ute_M (Suc r) q pp (rho (Suc r) q)"
      by (auto simp: Ute_SHOMachine_def Ute_sendMsg_def 
                     step_def send0_def send1_def)
    moreover
    from usafe
    have "card (SHOs (Suc r) pp \<inter> HOs (Suc r) pp) > N + 2*\<alpha> - E - 1"
      by (auto simp: Ute_SHOMachine_def step_def Ute_commPerRd_def)
    ultimately
    show ?thesis using threshold by auto
  qed
  moreover
  have "card (?msgs pp v) + card (SHOs (Suc r) pp \<inter> HOs (Suc r) pp)
        = card (?msgs pp v \<union> (SHOs (Suc r) pp \<inter> HOs (Suc r) pp))
          + card (?msgs pp v \<inter> (SHOs (Suc r) pp \<inter> HOs (Suc r) pp))"
    by (auto intro: card_Un_Int)
  moreover
  have "card (?msgs pp v \<union> (SHOs (Suc r) pp \<inter> HOs (Suc r) pp)) \<le> N"
    by (auto simp: card_mono)
  ultimately
  show ?thesis by auto
qed

text \<open>
  If more than \<open>E - \<alpha>\<close> messages holding \<open>v\<close> are sent to \<open>p\<close>
  at some round \<open>r\<close>, then any process \<open>pp\<close> will set its \<open>x\<close> to
  value \<open>v\<close> in \<open>r\<close>.
\<close>
(*
  The proof relies on previous lemmas @{text common_x_argument_1}
  and @{text common_vote} and the @{text Ute_commPerRound} predicate. 
*)

lemma common_x_argument_2:
  assumes run: "SHORun Ute_M rho HOs SHOs" 
  and usafe: "\<forall>r. SHOcommPerRd Ute_M (HOs r) (SHOs r)"
  and nxtpp: "nextState Ute_M (Suc r) pp (rho (Suc r) pp) 
                        \<mu>pp (rho (Suc (Suc r)) pp)"
  and mupp: "\<mu>pp \<in> SHOmsgVectors Ute_M (Suc r) pp (rho (Suc r)) 
                                 (HOs (Suc r) pp) (SHOs (Suc r) pp)"
  and threshold: "card {q. sendMsg Ute_M (Suc r) q p (rho (Suc r) q) 
                             = Vote (Some v)} > E - \<alpha>"
                 (is "card (?sent p v) > _")
  shows "x (rho (Suc (Suc r)) pp) = v"
proof -
  have stp:"step (Suc r) \<noteq> 0"
  proof
    assume sr: "step (Suc r) = 0"
    hence "\<forall>q. sendMsg Ute_M (Suc r) q p (rho (Suc r) q) 
                 = Val (x (rho (Suc r) q))"
      by (auto simp: Ute_SHOMachine_def Ute_sendMsg_def send0_def)
    moreover
    from threshold obtain qq where
      "sendMsg Ute_M (Suc r) qq p (rho (Suc r) qq) = Vote (Some v)"
      by force
    ultimately
    show False by simp
  qed

  have va: "card {qq. \<mu>pp qq = Some (Vote (Some v))} > \<alpha>"
       (is "card (?msgs v) > \<alpha>")
  proof -
    from mupp
    have "SHOs (Suc r) pp \<inter> HOs (Suc r) pp 
          \<subseteq> {qq. \<mu>pp qq = Some (sendMsg Ute_M (Suc r) qq pp (rho (Suc r) qq))}"
      unfolding SHOmsgVectors_def by auto
    moreover
    hence "(?msgs v) \<supseteq> (?sent pp v) \<inter> (SHOs (Suc r) pp \<inter> HOs (Suc r) pp)" 
      by auto
    hence "card (?msgs v) 
             \<ge> card ((?sent pp v) \<inter> (SHOs (Suc r) pp \<inter> HOs (Suc r) pp))"
      by (auto intro: card_mono)
    moreover
    from usafe threshold 
    have alph:"card ((?sent pp v) \<inter> (SHOs (Suc r) pp \<inter> HOs (Suc r) pp)) > \<alpha>"
      by (blast dest: common_x_argument_1)
    ultimately
    show ?thesis by auto
  qed
  moreover
  from nxtpp stp
  have "next1 (Suc r) pp (rho (Suc r) pp)  \<mu>pp (rho (Suc (Suc r)) pp)"
    by (auto simp: Ute_SHOMachine_def nextState_def Ute_nextState_def)
  ultimately
  obtain w where wa:"card (?msgs w) > \<alpha>" and xw:"x (rho (Suc (Suc r)) pp) = w"
    unfolding next1_def by auto

  have "v = w"
  proof -
    note usafe
    moreover
    obtain qv where "qv \<in> SHOs (Suc r) pp" and "\<mu>pp qv = Some (Vote (Some v))"
    proof -
      have "\<not> (?msgs v \<subseteq> HOs (Suc r) pp - SHOs (Suc r) pp)"
      proof
        assume "?msgs v \<subseteq> HOs (Suc r) pp - SHOs (Suc r) pp"
        hence "card (?msgs v) \<le> card ((HOs (Suc r) pp) - (SHOs (Suc r) pp))"
          by (auto simp: card_mono)
        moreover
        from usafe
        have "card (HOs (Suc r) pp - SHOs (Suc r) pp) \<le> \<alpha>"
          by (auto simp: Ute_SHOMachine_def Ute_commPerRd_def)
        moreover
        note va
        ultimately
        show False by auto
      qed
      then obtain qv
        where "qv \<notin> HOs (Suc r) pp - SHOs (Suc r) pp"
          and qsv:"\<mu>pp qv = Some (Vote (Some v))" 
        by auto
      with mupp have "qv \<in> SHOs (Suc r) pp"
        unfolding SHOmsgVectors_def by auto
      with qsv that show ?thesis by auto
    qed
    with stp mupp have "vote (rho (Suc r) qv) = Some v"
      by (auto simp: Ute_SHOMachine_def SHOmsgVectors_def 
                     Ute_sendMsg_def send1_def)
    moreover
    obtain qw where
      "qw \<in> SHOs (Suc r) pp" and "\<mu>pp qw = Some (Vote (Some w))"
    proof -
      have "\<not> (?msgs w \<subseteq> HOs (Suc r) pp - SHOs (Suc r) pp)"
      proof
        assume "?msgs w \<subseteq> HOs (Suc r) pp - SHOs (Suc r) pp"
        hence "card (?msgs w) \<le> card ((HOs (Suc r) pp) - (SHOs (Suc r) pp))"
          by (auto simp: card_mono)
        moreover
        from usafe
        have "card (HOs (Suc r) pp - SHOs (Suc r) pp) \<le> \<alpha>"
          by (auto simp: Ute_SHOMachine_def Ute_commPerRd_def)
        moreover
        note wa
        ultimately
        show False by auto
      qed
      then obtain qw
        where "qw \<notin> HOs (Suc r) pp - SHOs (Suc r) pp"
          and qsw: "\<mu>pp qw = Some (Vote (Some w))" 
        by auto
      with mupp have "qw \<in> SHOs (Suc r) pp" 
        unfolding SHOmsgVectors_def by auto
      with qsw that show ?thesis by auto
    qed
    with stp mupp have "vote (rho (Suc r) qw) = Some w"
      by (auto simp: Ute_SHOMachine_def SHOmsgVectors_def
                     Ute_sendMsg_def send1_def)
    moreover
    from run obtain \<mu>qv \<mu>qw
      where "nextState Ute_M r qv ((rho r) qv)  \<mu>qv (rho (Suc r) qv)"
        and "\<mu>qv \<in> SHOmsgVectors Ute_M r qv (rho r) (HOs r qv) (SHOs r qv)"
        and "nextState Ute_M r qw ((rho r) qw)  \<mu>qw (rho (Suc r) qw)"
        and "\<mu>qw \<in> SHOmsgVectors Ute_M r qw (rho r) (HOs r qw) (SHOs r qw)"
      by (auto simp: Ute_SHOMachine_def SHORun_eq SHOnextConfig_eq) blast
    ultimately
    show ?thesis using usafe by (auto dest: common_vote)
  qed
  with xw show "x (rho (Suc (Suc r)) pp) = v" by auto
qed

text \<open>
  Inductive argument for the agreement and validity theorems.
\<close>
(*
  The proof relies on previous lemmas @{text common_x_argument_2}
  and @{text unique_majority_T} and the @{text Ute_commPerRound} predicate.
*)

lemma safety_inductive_argument:
  assumes run: "SHORun Ute_M rho HOs SHOs"
  and comm: "\<forall>r. SHOcommPerRd Ute_M (HOs r) (SHOs r)"
  and ih: "E - \<alpha> < card {q. sendMsg Ute_M r' q p (rho r' q) = Vote (Some v)}"
  and stp1: "step r' = Suc 0"
  shows "E - \<alpha> <
         card {q. sendMsg Ute_M (Suc (Suc r')) q p (rho (Suc (Suc r')) q)
                     = Vote (Some v)}"
proof -
  from stp1 have "r' > 0" by (auto simp: step_def)
  with stp1 obtain r where rr':"r' = Suc r" and stpr:"step (Suc r) = Suc 0"
    by (auto dest: gr0_implies_Suc)

  have "\<forall>pp. x (rho (Suc (Suc r)) pp) = v"
  proof 
    fix pp
    from run obtain \<mu>pp
      where "\<mu>pp \<in> SHOmsgVectors Ute_M r' pp (rho r') (HOs r' pp) (SHOs r' pp)"
        and "nextState Ute_M r' pp (rho r' pp)  \<mu>pp (rho (Suc r') pp)"
      by (auto simp: Ute_SHOMachine_def SHORun_eq SHOnextConfig_eq)
    with run comm ih rr' show "x (rho (Suc (Suc r)) pp) = v" 
      by (auto dest: common_x_argument_2)
  qed
  with run stpr
  have "\<forall>pp p. sendMsg Ute_M (Suc (Suc r)) pp p (rho (Suc (Suc r)) pp) = Val v"
    by (auto simp: Ute_SHOMachine_def SHORun_eq SHOnextConfig_eq
                   Ute_sendMsg_def send0_def mod_Suc step_def)
  with rr'
  have "\<And>p \<mu>p'. \<mu>p' \<in> SHOmsgVectors Ute_M (Suc r') p (rho (Suc r')) 
                                     (HOs (Suc r') p) (SHOs (Suc r') p)
             \<Longrightarrow> SHOs (Suc r') p \<inter> HOs (Suc r') p
                   \<subseteq> {q. \<mu>p' q = Some (Val v)}"
    by (auto simp: SHOmsgVectors_def)
  hence "\<And>p \<mu>p'. \<mu>p' \<in> SHOmsgVectors Ute_M (Suc r') p (rho (Suc r')) 
                                       (HOs (Suc r') p) (SHOs (Suc r') p)
             \<Longrightarrow> card (SHOs (Suc r') p \<inter> HOs (Suc r') p)
                   \<le> card {q. \<mu>p' q = Some (Val v)}" 
    by (auto simp: card_mono)
  moreover
  from comm have "\<And>p. T < card (SHOs (Suc r') p \<inter> HOs (Suc r') p)"
    by (auto simp: Ute_SHOMachine_def Ute_commPerRd_def)
  ultimately 
  have vT:"\<And>p \<mu>p'. \<mu>p' \<in> SHOmsgVectors Ute_M (Suc r') p (rho (Suc r')) 
                                         (HOs (Suc r') p) (SHOs (Suc r') p)
                \<Longrightarrow> T < card {q. \<mu>p' q = Some (Val v)}"
    by (auto dest: less_le_trans)

  show ?thesis
  proof -
    have "\<forall>pp. vote ((rho (Suc (Suc r'))) pp) = Some v"
    proof
      fix pp
      from run obtain \<mu>pp
        where nxtpp: "nextState Ute_M (Suc r') pp (rho (Suc r') pp) \<mu>pp 
                                      (rho (Suc (Suc r')) pp)"
          and mupp: "\<mu>pp \<in> SHOmsgVectors Ute_M (Suc r') pp (rho (Suc r'))
                                     (HOs (Suc r') pp) (SHOs (Suc r') pp)"
        by (auto simp: Ute_SHOMachine_def SHORun_eq SHOnextConfig_eq)
      with vT have vT':"card {q. \<mu>pp q = Some (Val v)} > T" 
        by auto
      moreover
      from stpr rr' have "step (Suc r') = 0"
        by (auto simp: mod_Suc step_def)
      with nxtpp
      have "next0 (Suc r') pp (rho (Suc r') pp) \<mu>pp (rho (Suc (Suc r')) pp)"
        by (auto simp: Ute_SHOMachine_def nextState_def Ute_nextState_def)
      ultimately
      obtain w
        where wT:"card {q. \<mu>pp q = Some (Val w)} > T"
          and votew:"vote (rho (Suc (Suc r')) pp) = Some w" 
        by (auto simp: next0_def)
      from vT' wT have "v = w"
        by (auto dest: unique_majority_T)
      with votew show "vote (rho (Suc (Suc r')) pp) = Some v" by simp
    qed
    with run stpr rr'
    have "\<forall>p. N = card {q. sendMsg Ute_M (Suc (Suc (Suc r))) q p 
                                  ((rho (Suc (Suc (Suc r)))) q) = Vote (Some v)}"
      by (auto simp: Ute_SHOMachine_def SHORun_eq SHOnextConfig_eq 
                     Ute_sendMsg_def send1_def step_def mod_Suc)
    with rr' majE EltN show ?thesis by auto
  qed
qed

text \<open>
  A process that holds some decision \<open>v\<close> has decided \<open>v\<close>
  sometime in the past.
\<close>

lemma decisionNonNullThenDecided:
  assumes run:"SHORun Ute_M rho HOs SHOs" and dec: "decide (rho n p) = Some v"
  shows "\<exists>m<n. decide (rho (Suc m) p) \<noteq> decide (rho m p) 
             \<and> decide (rho (Suc m) p) = Some v"
proof -
  let "?dec k" = "decide ((rho k) p)"
  have "(\<forall>m<n. ?dec (Suc m) \<noteq> ?dec m \<longrightarrow> ?dec (Suc m) \<noteq> Some v)
        \<longrightarrow> ?dec n \<noteq> Some v"
    (is "?P n" is "?A n \<longrightarrow> _")
  proof (induct n)
    from run show "?P 0"
      by (auto simp: Ute_SHOMachine_def SHORun_eq HOinitConfig_eq
                     initState_def Ute_initState_def)
  next
    fix n
    assume ih: "?P n" thus "?P (Suc n)" by force
  qed
  with dec show ?thesis by auto
qed


text \<open>
  If process \<open>p1\<close> has decided value \<open>v1\<close> and process
  \<open>p2\<close> later decides, then \<open>p2\<close> must decide \<open>v1\<close>.
\<close>
(*
  The proof relies on previous lemmas @{text decide_step},
  @{text decide_with_threshold_E}, @{text unique_majority_E_\<alpha>},
  @{text decisionNonNullThenDecided} and @{text safety_inductive_argument}.
*)

lemma laterProcessDecidesSameValue:
  assumes run:"SHORun Ute_M rho HOs SHOs"
  and comm:"\<forall>r. SHOcommPerRd Ute_M (HOs r) (SHOs r)"
  and dv1:"decide (rho (Suc r) p1) = Some v1"
  and dn2:"decide (rho (r + k) p2) \<noteq> Some v2"
  and dv2:"decide (rho (Suc (r + k)) p2) = Some v2"
  shows "v2 = v1"
proof -
  from run dv1 obtain r1
    where r1r:"r1 < Suc r"
      and dn1:"decide (rho r1 p1) \<noteq> Some v1"
      and dv1':"decide (rho (Suc r1) p1) = Some v1"
    by (auto dest: decisionNonNullThenDecided)

  from r1r obtain s where rr1:"Suc r = Suc (r1 + s)"
    by (auto dest: less_imp_Suc_add)
  then obtain k' where kk':"r + k = r1 + k'" 
    by auto
  with dn2 dv2 
  have dn2': "decide (rho (r1 + k') p2) \<noteq> Some v2"
    and dv2': "decide (rho (Suc (r1 + k')) p2) = Some v2"
    by auto

  from run dn1 dv1' dn2' dv2' 
  have rs0:"step r1 = Suc 0" and  rks0:"step (r1 + k') = Suc 0"
    by (auto simp: mod_Suc step_def dest: decide_step)

  have "step (r1 + k') = step (step r1 + k')"
    unfolding step_def by (simp add: mod_add_left_eq)
  with rs0 rks0 have "step k' = 0" by (auto simp: step_def mod_Suc)
  then obtain k'' where "k' = k''*nSteps" by (auto simp: step_def)
  with dn2' dv2' 
  have dn2'':"decide (rho (r1 + k''*nSteps) p2) \<noteq> Some v2"
    and dv2'':"decide (rho (Suc (r1 + k''*nSteps)) p2) = Some v2" 
    by auto

  from rs0 have stp:"step (r1 + k''*nSteps) = Suc 0" 
    unfolding step_def by auto

  have inv:"card {q. sendMsg Ute_M (r1 + k''*nSteps) q p1 (rho (r1 + k''*nSteps) q)
                         = Vote (Some v1)} > E - \<alpha>"
  proof (induct k'')
    from stp have "step (r1 + 0*nSteps) = Suc 0" 
      by (auto simp: step_def)
    from run comm dn1 dv1'
    show "card {q. sendMsg Ute_M (r1 + 0*nSteps) q p1 (rho (r1 + 0*nSteps) q)
                      = Vote (Some v1)} > E - \<alpha>"
      by (intro decide_with_threshold_E) auto
  next
    fix k''
    assume ih: "E - \<alpha> <
          card {q. sendMsg Ute_M (r1 + k''*nSteps) q p1 (rho (r1 + k''*nSteps) q)
                       = Vote (Some v1)}"
    from rs0 have stps: "step (r1 + k''*nSteps) = Suc 0" 
      by (auto simp: step_def)
    with run comm ih
    have "E - \<alpha>  <
       card {q. sendMsg Ute_M (Suc (Suc (r1 + k''*nSteps))) q p1 
                              (rho (Suc (Suc (r1 + k''*nSteps))) q) 
                   = Vote (Some v1)}"
      by (rule safety_inductive_argument)
    thus "E - \<alpha> <
       card {q. sendMsg Ute_M (r1 + Suc k'' * nSteps) q p1
                              (rho (r1 + Suc k'' * nSteps) q)
                     = Vote (Some v1)}"
      by auto
  qed
  moreover
  from run
  have "\<forall>q. sendMsg Ute_M (r1 + k''*nSteps) q p1 (rho (r1 + k''*nSteps) q)
          = sendMsg Ute_M (r1 + k''*nSteps) q p2 (rho (r1 + k''*nSteps) q)"
    by (auto simp: Ute_SHOMachine_def Ute_sendMsg_def 
                   step_def send0_def send1_def)
  moreover
  from run comm dn2'' dv2''
  have "E - \<alpha> <
      card {q. sendMsg Ute_M (r1 + k''*nSteps) q p2 (rho (r1 + k''*nSteps) q)
                  = Vote (Some v2)}"
    by (auto dest: decide_with_threshold_E)
  ultimately
  show "v2 = v1" by (auto dest: unique_majority_E_\<alpha>)
qed

text \<open>
  The Agreement property is an immediate consequence of the two
  preceding lemmas.
\<close>

theorem ute_agreement:
  assumes run: "SHORun Ute_M rho HOs SHOs" 
  and comm: "\<forall>r. SHOcommPerRd Ute_M (HOs r) (SHOs r)"
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
    then obtain m where m: "l = k+m" by (auto simp add: le_iff_add)
    from run comm k2 l1 l2 m have "w = v"
      by (auto elim!: laterProcessDecidesSameValue)
    thus ?thesis by simp
  next
    case False
    hence "l \<le> k" by simp
    then obtain m where m: "k = l+m" by (auto simp add: le_iff_add)
    from run comm l2 k1 k2 m show ?thesis
      by (auto elim!: laterProcessDecidesSameValue)
  qed
qed

text \<open>
  Main lemma for the proof of the Validity property.
\<close>
(*
  The proof relies on previous lemmas @{text safety_inductive_argument},
  @{text unique_majority_T} and the @{text Ute_commPerRound} predicate.
*)

lemma validity_argument:
  assumes run: "SHORun Ute_M rho HOs SHOs"
  and comm: "\<forall>r. SHOcommPerRd Ute_M (HOs r) (SHOs r)"
  and init: "\<forall>p. x ((rho 0) p) = v"
  and dw: "decide (rho r p) = Some w"
  and stp: "step r' = Suc 0"
  shows "card {q. sendMsg Ute_M r' q p (rho r' q) = Vote (Some v)} > E - \<alpha>"
proof -
  define k where "k = r' div nSteps"
  with stp have stp: "r' = Suc 0 + k * nSteps"
    using div_mult_mod_eq [of r' nSteps]
    by (simp add: step_def)
  moreover
  have "E - \<alpha> <
        card {q. sendMsg Ute_M (Suc 0 + k*nSteps) q p ((rho (Suc 0 + k*nSteps)) q)
                   = Vote (Some v)}"
  proof (induct k)
    have "\<forall>pp. vote ((rho (Suc 0)) pp) = Some v"
    proof
      fix pp
      from run obtain \<mu>pp
        where nxtpp:"nextState Ute_M 0 pp (rho 0 pp) \<mu>pp (rho (Suc 0) pp)"
          and mupp:"\<mu>pp \<in> SHOmsgVectors Ute_M 0 pp (rho 0) (HOs 0 pp) (SHOs 0 pp)"
        by (auto simp: Ute_SHOMachine_def SHORun_eq SHOnextConfig_eq)
      have majv:"card {q. \<mu>pp q = Some (Val v)} > T"
      proof -
        from run init have "\<forall>q. sendMsg Ute_M 0 q pp (rho 0 q) = Val v"
          by (auto simp: Ute_SHOMachine_def SHORun_eq SHOnextConfig_eq 
                         Ute_sendMsg_def send0_def step_def)
        moreover
        from comm have shoT:"card (SHOs 0 pp \<inter> HOs 0 pp) > T"
          by (auto simp: Ute_SHOMachine_def Ute_commPerRd_def)
        moreover
        from mupp
        have "SHOs 0 pp \<inter> HOs 0 pp 
               \<subseteq> {q. \<mu>pp q = Some (sendMsg Ute_M 0 q pp (rho 0 q))}"
          by (auto simp: SHOmsgVectors_def)
        hence "card (SHOs 0 pp \<inter> HOs 0 pp)
                 \<le> card {q. \<mu>pp q = Some (sendMsg Ute_M 0 q pp (rho 0 q))}"
          by (auto simp: card_mono)
        ultimately
        show ?thesis by (auto simp: less_le_trans)
      qed
      moreover
      from nxtpp have "next0 0 pp ((rho 0) pp) \<mu>pp (rho (Suc 0) pp)"
        by (auto simp: Ute_SHOMachine_def nextState_def Ute_nextState_def step_def)
      ultimately
      obtain w where majw:"card {q. \<mu>pp q = Some (Val w)} > T"
                 and votew:"vote (rho (Suc 0) pp) = Some w"
        by (auto simp: next0_def)

      from majv majw have "v = w" by (auto dest: unique_majority_T)
      with votew show "vote ((rho (Suc 0)) pp) = Some v" by simp
    qed
    with run
    have "card {q. sendMsg Ute_M (Suc 0) q p (rho (Suc 0) q) = Vote (Some v)} = N"
      by (auto simp: Ute_SHOMachine_def SHORun_eq SHOnextConfig_eq
                     Ute_nextState_def step_def Ute_sendMsg_def send1_def)
    thus "E - \<alpha> <
      card {q. sendMsg Ute_M (Suc 0 + 0 * nSteps) q p (rho (Suc 0 + 0 * nSteps) q)
                   = Vote (Some v)}"
      using majE EltN by auto
  next
    fix k
    assume ih:"E - \<alpha> <
        card {q. sendMsg Ute_M (Suc 0 + k * nSteps) q p (rho (Suc 0 + k * nSteps) q)
                     = Vote (Some v)}"
    have "step (Suc 0 + k * nSteps) = Suc 0"
      by (auto simp: mod_Suc step_def)
    from run comm ih this
    have "E - \<alpha> <
      card {q. sendMsg Ute_M (Suc (Suc (Suc 0 + k * nSteps))) q p
                             (rho (Suc (Suc (Suc 0 + k * nSteps))) q)
                  = Vote (Some v)}"
      by (rule safety_inductive_argument)
    thus "E - \<alpha> <
       card {q. sendMsg Ute_M (Suc 0 + Suc k * nSteps) q p 
                              (rho (Suc 0 + Suc k * nSteps) q)
                 = Vote (Some v)}" by simp
  qed
  ultimately
  show ?thesis by simp
qed

text \<open>
  The following theorem shows the Validity property of algorithm \ute{}.
\<close>
(*
 The proof relies on previous lemmas @{text decisionNonNullThenDecided},
 @{text decide_step}, @{text decide_with_threshold_E},  @{text unique_majority_E_\<alpha>},
 and the @{text Validity_argument}. 
*)

theorem ute_validity:
  assumes run: "SHORun Ute_M rho HOs SHOs"
  and comm: "\<forall>r. SHOcommPerRd Ute_M (HOs r) (SHOs r)"
  and init: "\<forall>p. x (rho 0 p) = v"
  and dw: "decide (rho r p) = Some w"
  shows "v = w"
proof -
  from run dw obtain r1
    where dnr1:"decide ((rho r1) p) \<noteq> Some w"
      and dwr1:"decide ((rho (Suc r1)) p) = Some w"
    by (force dest: decisionNonNullThenDecided)
  with run have "step r1 \<noteq> 0" by (rule decide_step)
  hence "step r1 = Suc 0" by (simp add: step_def mod_Suc)
  with assms
  have "E - \<alpha> <
        card {q. sendMsg Ute_M r1 q p (rho r1 q) = Vote (Some v)}"
    by (rule validity_argument)
  moreover
  from run comm dnr1 dwr1
  have "card {q. sendMsg Ute_M r1 q p (rho r1 q) = Vote (Some w)} > E - \<alpha>"
    by (auto dest: decide_with_threshold_E)
  ultimately
  show "v = w" by (auto dest: unique_majority_E_\<alpha>)
qed


subsection \<open>Proof of Termination\<close>

text \<open>
  At the second round of a phase that satisfies the conditions expressed in
  the global communication predicate, processes update their \<open>x\<close> variable 
  with the value \<open>v\<close> they receive in more than \<open>\<alpha>\<close> messages.
\<close>
(* The proof relies on @{text common_vote}. *)

lemma set_x_from_vote:
  assumes run: "SHORun Ute_M rho HOs SHOs" 
  and comm: "SHOcommPerRd Ute_M (HOs r) (SHOs r)"
  and stp: "step (Suc r) = Suc 0"
  and \<pi>: "\<forall>p. HOs (Suc r) p = SHOs (Suc r) p"
  and nxt: "nextState Ute_M (Suc r) p (rho (Suc r) p) \<mu> (rho (Suc (Suc r)) p)"
  and mu: "\<mu> \<in> SHOmsgVectors Ute_M (Suc r) p (rho (Suc r))
                                   (HOs (Suc r) p) (SHOs (Suc r) p)"
  and vp: "\<alpha> < card {qq. \<mu> qq = Some (Vote (Some v))}"
  shows "x ((rho (Suc (Suc r))) p) = v"
proof -
  from nxt stp vp obtain wp
    where xwp:"\<alpha> < card {qq. \<mu> qq = Some (Vote (Some wp))}"
      and xp:"x (rho (Suc (Suc r)) p) = wp"
    by (auto simp: Ute_SHOMachine_def nextState_def Ute_nextState_def next1_def)

  have "wp = v"
  proof -
    from xwp obtain pp where smw:"\<mu> pp = Some (Vote (Some wp))"
      by force
    have "vote (rho (Suc r) pp) = Some wp"
    proof -
      from smw mu \<pi> 
      have "\<mu> pp = Some (sendMsg Ute_M (Suc r) pp p (rho (Suc r) pp))"
        unfolding SHOmsgVectors_def by force
      with stp have "\<mu> pp = Some (Vote (vote (rho (Suc r) pp)))"
        by (auto simp: Ute_SHOMachine_def Ute_sendMsg_def send1_def)
      with smw show ?thesis by auto
    qed
    moreover
    from vp obtain qq where smv:"\<mu> qq = Some (Vote (Some v))" 
      by force
    have "vote (rho (Suc r) qq) = Some v"
    proof -
      from smv mu \<pi>
      have "\<mu> qq = Some (sendMsg Ute_M (Suc r) qq p (rho (Suc r) qq))"
        unfolding SHOmsgVectors_def by force
      with stp have "\<mu> qq = Some (Vote (vote (rho (Suc r) qq)))"
        by (auto simp: Ute_SHOMachine_def Ute_sendMsg_def send1_def)
      with smv show ?thesis by auto
    qed
    moreover
    from run obtain \<mu>pp \<mu>qq
      where "nextState Ute_M r pp (rho r pp) \<mu>pp (rho (Suc r) pp)"
        and "\<mu>pp \<in> SHOmsgVectors Ute_M r pp (rho r) (HOs r pp) (SHOs r pp)"
        and "nextState Ute_M r qq ((rho r) qq)  \<mu>qq (rho (Suc r) qq)"
        and "\<mu>qq \<in> SHOmsgVectors Ute_M r qq (rho r) (HOs r qq) (SHOs r qq)"
      unfolding Ute_SHOMachine_def SHORun_eq SHOnextConfig_eq by blast
    ultimately
    show ?thesis using comm by (auto dest: common_vote)
  qed
  with xp show ?thesis by simp
qed

text \<open>
  Assume that HO and SHO sets are uniform at the second step of some
  phase. Then at the subsequent round there exists some value \<open>v\<close>
  such that any received message which is not corrupted holds \<open>v\<close>.
\<close>
(* The proof relies on lemma @{text set_x_from_vote}. *)

lemma termination_argument_1:
  assumes run: "SHORun Ute_M rho HOs SHOs" 
  and comm: "SHOcommPerRd Ute_M (HOs r) (SHOs r)"
  and stp: "step (Suc r) = Suc 0"
  and \<pi>: "\<forall>p. \<pi>0 = HOs (Suc r) p \<and> \<pi>0 = SHOs (Suc r) p"
  obtains v where 
    "\<And>p \<mu>p' q. 
       \<lbrakk> q \<in> SHOs (Suc (Suc r)) p \<inter> HOs (Suc (Suc r)) p; 
         \<mu>p' \<in> SHOmsgVectors Ute_M (Suc (Suc r)) p (rho (Suc (Suc r)))
                             (HOs (Suc (Suc r)) p) (SHOs (Suc (Suc r)) p)
       \<rbrakk> \<Longrightarrow> \<mu>p' q = (Some (Val v))"
proof -
  from \<pi> have hosho:"\<forall>p. SHOs (Suc r) p = SHOs (Suc r) p \<inter> HOs (Suc r) p"
    by simp

  have "\<And>p q. x (rho (Suc (Suc r)) p) = x (rho (Suc (Suc r)) q)"
  proof -
    fix p q
    from run obtain \<mu>p
      where nxt: "nextState Ute_M (Suc r) p (rho (Suc r) p)  
                                  \<mu>p (rho (Suc (Suc r)) p)"
        and mu: "\<mu>p \<in> SHOmsgVectors Ute_M (Suc r) p (rho (Suc r)) 
                                          (HOs (Suc r) p) (SHOs (Suc r) p)"
      by (auto simp: Ute_SHOMachine_def SHORun_eq SHOnextConfig_eq)

    from run obtain \<mu>q
      where nxtq: "nextState Ute_M (Suc r) q (rho (Suc r) q)
                                   \<mu>q (rho (Suc (Suc r)) q)"
       and muq: "\<mu>q \<in> SHOmsgVectors Ute_M (Suc r) q (rho (Suc r))
                                          (HOs (Suc r) q) (SHOs (Suc r) q)"
      by (auto simp: Ute_SHOMachine_def SHORun_eq SHOnextConfig_eq)
       
    have "\<forall>qq. \<mu>p qq = \<mu>q qq"
    proof
      fix qq
      show "\<mu>p qq = \<mu>q qq"
      proof (cases "\<mu>p qq = None")
        case False
        with mu \<pi> have 1:"qq \<in> SHOs (Suc r) p" and 2:"qq \<in> SHOs (Suc r) q"
          unfolding SHOmsgVectors_def by auto
        from mu \<pi> 1
        have "\<mu>p qq = Some (sendMsg Ute_M (Suc r) qq p (rho (Suc r) qq))"
          unfolding SHOmsgVectors_def by auto
        moreover
        from muq \<pi> 2 
        have "\<mu>q qq = Some (sendMsg Ute_M (Suc r) qq q (rho (Suc r) qq))"
          unfolding SHOmsgVectors_def by auto
        ultimately
        show ?thesis
          by (auto simp: Ute_SHOMachine_def Ute_sendMsg_def step_def 
                         send0_def send1_def)
      next
        case True
        with mu have "qq \<notin> HOs (Suc r) p" unfolding SHOmsgVectors_def by auto
        with \<pi> muq have "\<mu>q qq = None" unfolding SHOmsgVectors_def by auto
        with True show ?thesis by simp
      qed
    qed
    hence vsets:"\<And>v. {qq. \<mu>p qq = Some (Vote (Some v))} 
                    = {qq. \<mu>q qq = Some (Vote (Some v))}"
      by auto
    (* NB: due to the Global predicate (HO = SHO), we do not need \<alpha> + 1 msgs
       holding a true vote, only 1. We might also prefer to invoke only the
       @{text Ute_commPerRound} predicate to obtain qq :
       since "card (HOs (Suc r) p - SHOs (Suc r) p) < \<alpha>", there should be one
       "correct" message holding a vote and this vote should be common according
       to previous (Suc r)esults. *)

    show "x (rho (Suc (Suc r)) p) = x (rho (Suc (Suc r)) q)"
    proof (cases "\<exists>v. \<alpha> < card {qq. \<mu>p qq = Some (Vote (Some v))}", clarify)
      fix v
      assume vp: "\<alpha> < card {qq. \<mu>p qq = Some (Vote (Some v))}"
      with run comm stp \<pi> nxt mu have "x (rho (Suc (Suc r)) p) = v" 
        by (auto dest: set_x_from_vote)
      moreover
      from vsets vp
      have "\<alpha> < card {qq. \<mu>q qq = Some (Vote (Some v))}" by auto
      with run comm stp \<pi> nxtq muq have "x (rho (Suc (Suc r)) q) = v" 
        by (auto dest: set_x_from_vote)
      ultimately
      show "x (rho (Suc (Suc r)) p) = x (rho (Suc (Suc r)) q)" 
        by auto
    next
      assume nov: "\<not> (\<exists>v. \<alpha> < card {qq. \<mu>p qq = Some (Vote (Some v))})"
      with nxt stp have "x (rho (Suc (Suc r)) p) = undefined"
        by (auto simp: Ute_SHOMachine_def nextState_def 
                       Ute_nextState_def next1_def)
      moreover
      from vsets nov
      have "\<not> (\<exists>v. \<alpha> < card {qq. \<mu>q qq = Some (Vote (Some v))})" by auto
      with nxtq stp have "x (rho (Suc (Suc r)) q) = undefined" 
        by (auto simp: Ute_SHOMachine_def nextState_def 
                       Ute_nextState_def next1_def)
      ultimately
      show ?thesis by simp
    qed
  qed
  then obtain v where "\<And>q. x (rho (Suc (Suc r)) q) = v" by blast
  moreover
  from stp have "step (Suc (Suc r)) = 0" 
    by (auto simp: step_def mod_Suc)
  hence "\<And>p \<mu>p' q. 
    \<lbrakk> q \<in> SHOs (Suc (Suc r)) p \<inter> HOs (Suc (Suc r)) p;
      \<mu>p' \<in> SHOmsgVectors Ute_M (Suc (Suc r)) p (rho (Suc (Suc r)))
                          (HOs (Suc (Suc r)) p) (SHOs (Suc (Suc r)) p)
    \<rbrakk> \<Longrightarrow> \<mu>p' q = Some (Val (x (rho (Suc (Suc r)) q)))"
    by (auto simp: Ute_SHOMachine_def SHOmsgVectors_def Ute_sendMsg_def send0_def)
  ultimately
  have "\<And>p \<mu>p' q. 
    \<lbrakk> q \<in> SHOs (Suc (Suc r)) p  \<inter> HOs (Suc (Suc r)) p; 
      \<mu>p' \<in> SHOmsgVectors Ute_M (Suc (Suc r)) p (rho (Suc (Suc r)))
                                (HOs (Suc (Suc r)) p) (SHOs (Suc (Suc r)) p)
    \<rbrakk> \<Longrightarrow> \<mu>p' q = (Some (Val v))" 
    by auto
  with that show thesis by blast
qed

text \<open>
  If a process \<open>p\<close> votes \<open>v\<close> at some round \<open>r\<close>,
  then all messages received by \<open>p\<close> in \<open>r\<close> that are not
  corrupted hold \<open>v\<close>.
\<close>
(* immediate from lemma @{text vote_step} and the algorithm definition. *)

lemma termination_argument_2:
  assumes mup: "\<mu>p \<in> SHOmsgVectors Ute_M (Suc r) p (rho (Suc r)) 
                                     (HOs (Suc r) p) (SHOs (Suc r) p)"
  and nxtq: "nextState Ute_M r q (rho r q)  \<mu>q (rho (Suc r) q)"
  and vq: "vote (rho (Suc r) q) = Some v"
  and qsho: "q \<in> SHOs (Suc r) p \<inter> HOs (Suc r) p"
  shows "\<mu>p q = Some (Vote (Some v))"
proof -
  from nxtq vq have "step r = 0" by (auto simp: vote_step)
  with mup qsho have "\<mu>p q = Some (Vote (vote (rho (Suc r) q)))"
    by (auto simp: Ute_SHOMachine_def SHOmsgVectors_def Ute_sendMsg_def
                   step_def send1_def mod_Suc)
  with vq show "\<mu>p q = Some (Vote (Some v))" by auto
qed

text\<open>
  We now prove the Termination property.
\<close>
(*
  The proof relies on previous lemmas @{text termination_argument_1},
  @{text termination_argument_2}, @{text common_vote}, @{text unique_majority_E},
  and the @{text Ute_commGlobal} predicate.
*)

theorem ute_termination:
  assumes run: "SHORun Ute_M rho HOs SHOs"
  and commR: "\<forall>r. SHOcommPerRd Ute_M (HOs r) (SHOs r)"
  and commG: "SHOcommGlobal Ute_M HOs SHOs"
  shows "\<exists>r v. decide (rho r p) = Some v"
proof -
  from commG
  obtain \<Phi> \<pi> r0
    where rr: "r0 = Suc (nSteps * \<Phi>)"
      and \<pi>: "\<forall>p. \<pi> = HOs r0 p \<and> \<pi> = SHOs r0 p"
      and t: "\<forall>p. card (SHOs (Suc r0) p \<inter> HOs (Suc r0) p) > T"
      and e: "\<forall>p. card (SHOs (Suc (Suc r0)) p \<inter> HOs (Suc (Suc r0)) p) > E"
    by (auto simp: Ute_SHOMachine_def Ute_commGlobal_def Let_def)
  from rr have stp:"step r0 = Suc 0" by (auto simp: step_def)

  obtain w where votew:"\<forall>p. (vote (rho (Suc (Suc r0)) p)) = Some w"
  proof -    
    have abc:"\<forall>p. \<exists>w. vote (rho (Suc (Suc r0)) p) = Some w"
    proof
      fix p
      from run stp obtain \<mu>p
        where nxt:"nextState Ute_M (Suc r0) p (rho (Suc r0) p) \<mu>p 
                                   (rho (Suc (Suc r0)) p)"
          and mup:"\<mu>p \<in> SHOmsgVectors Ute_M (Suc r0) p (rho (Suc r0)) 
                                      (HOs (Suc r0) p) (SHOs (Suc r0) p)"
        by (auto simp: Ute_SHOMachine_def SHORun_eq SHOnextConfig_eq)

      have "\<exists>v. T < card {qq. \<mu>p qq = Some (Val v)}"
      proof -
        from t have "card (SHOs (Suc r0) p \<inter> HOs (Suc r0) p) > T" .. 
        moreover
        from run commR stp \<pi> rr
        obtain v where
          "\<And>p \<mu>p' q. 
              \<lbrakk> q \<in> SHOs (Suc r0) p \<inter> HOs (Suc r0) p;
                \<mu>p' \<in> SHOmsgVectors Ute_M (Suc r0) p (rho (Suc r0)) 
                                          (HOs (Suc r0) p) (SHOs (Suc r0) p)
              \<rbrakk> \<Longrightarrow> \<mu>p' q = Some (Val v)" 
          using termination_argument_1 by blast

        with mup obtain v where
          "\<And>qq. qq \<in> SHOs (Suc r0) p \<inter> HOs (Suc r0) p \<Longrightarrow> \<mu>p qq = Some (Val v)" 
          by auto
        hence "SHOs (Suc r0) p \<inter> HOs (Suc r0) p \<subseteq> {qq. \<mu>p qq = Some (Val v)}" 
          by auto
        hence "card (SHOs (Suc r0) p \<inter> HOs (Suc r0) p)
                 \<le> card {qq. \<mu>p qq = Some (Val v)}"
          by (auto intro: card_mono)
        ultimately
        have "T < card {qq. \<mu>p qq = Some (Val v)}" by auto
        thus ?thesis by auto
      qed
      with stp nxt show "\<exists>w. vote ((rho (Suc (Suc r0))) p) = Some w"
        by (auto simp: Ute_SHOMachine_def nextState_def Ute_nextState_def 
                       step_def mod_Suc next0_def)
    qed
    then obtain qq w where qqw:"vote (rho (Suc (Suc r0)) qq) = Some w" 
      by blast
    have "\<forall>pp. vote (rho (Suc (Suc r0)) pp) = Some w"
    proof
      fix pp
      from abc obtain wp where pwp:"vote ((rho (Suc (Suc r0))) pp) = Some wp" 
        by blast
      from run obtain \<mu>pp \<mu>qq
        where nxtp: "nextState Ute_M (Suc r0) pp (rho (Suc r0) pp)
                                     \<mu>pp (rho (Suc (Suc r0)) pp)"
          and mup: "\<mu>pp \<in> SHOmsgVectors Ute_M (Suc r0) pp (rho (Suc r0))
                                          (HOs (Suc r0) pp) (SHOs (Suc r0) pp)"
          and nxtq: "nextState Ute_M (Suc r0) qq (rho (Suc r0) qq)
                                     \<mu>qq (rho (Suc (Suc r0)) qq)"
          and muq: "\<mu>qq \<in> SHOmsgVectors Ute_M (Suc r0) qq (rho (Suc r0))
                                          (HOs (Suc r0) qq) (SHOs (Suc r0) qq)"
        unfolding Ute_SHOMachine_def SHORun_eq SHOnextConfig_eq by blast
      from commR this pwp qqw have "wp = w"
        by (auto dest: common_vote)
      with pwp show "vote ((rho (Suc (Suc r0))) pp) = Some w" 
        by auto
    qed
    with that show ?thesis by auto
  qed

  from run obtain \<mu>p'
    where nxtp: "nextState Ute_M (Suc (Suc r0)) p (rho (Suc (Suc r0)) p)
                                 \<mu>p' (rho (Suc (Suc (Suc r0))) p)"
      and mup': "\<mu>p' \<in> SHOmsgVectors Ute_M (Suc (Suc r0)) p (rho (Suc (Suc r0)))
                                     (HOs (Suc (Suc r0)) p) (SHOs (Suc (Suc r0)) p)"
    by (auto simp: Ute_SHOMachine_def SHORun_eq SHOnextConfig_eq)
  have "\<And>qq. qq \<in> SHOs (Suc (Suc r0)) p \<inter> HOs (Suc (Suc r0)) p 
              \<Longrightarrow> \<mu>p' qq = Some (Vote (Some w))"
  proof -
    fix qq
    assume qqsho:"qq \<in> SHOs (Suc (Suc r0)) p \<inter> HOs (Suc (Suc r0)) p"
    from run obtain \<mu>qq where
      nxtqq:"nextState Ute_M (Suc r0) qq (rho (Suc r0) qq)
                             \<mu>qq (rho (Suc (Suc r0)) qq)"
      by (auto simp: Ute_SHOMachine_def SHORun_eq SHOnextConfig_eq)
    from commR mup' nxtqq votew qqsho show "\<mu>p' qq = Some (Vote (Some w))"
      by (auto dest: termination_argument_2)
  qed
  hence "SHOs (Suc (Suc r0)) p  \<inter> HOs (Suc (Suc r0)) p
           \<subseteq> {qq. \<mu>p' qq = Some (Vote (Some w))}" 
    by auto
  hence wsho: "card (SHOs (Suc (Suc r0)) p  \<inter> HOs (Suc (Suc r0)) p)
                 \<le> card {qq. \<mu>p' qq = Some (Vote (Some w))}"
    by (auto simp: card_mono)
   
  from stp have "step (Suc (Suc r0)) = Suc 0" 
    unfolding step_def by auto
  with nxtp have "next1 (Suc (Suc r0)) p (rho (Suc (Suc r0)) p) \<mu>p'
                        (rho (Suc (Suc (Suc r0))) p)"
    by (auto simp: Ute_SHOMachine_def nextState_def Ute_nextState_def)
  moreover
  from e have "E < card (SHOs (Suc (Suc r0)) p \<inter> HOs (Suc (Suc r0)) p)" 
    by auto
  with wsho have majv:"card {qq. \<mu>p' qq = Some (Vote (Some w))} > E" 
    by auto
  ultimately
  show ?thesis by (auto simp: next1_def)
qed


subsection \<open>\ute{} Solves Weak Consensus\<close>

text \<open>
  Summing up, all (coarse-grained) runs of \ute{} for
  HO and SHO collections that satisfy the communication predicate 
  satisfy the Weak Consensus property.
\<close>

theorem ute_weak_consensus:
  assumes run: "SHORun Ute_M rho HOs SHOs"
      and commR: "\<forall>r. SHOcommPerRd Ute_M (HOs r) (SHOs r)"
      and commG: "SHOcommGlobal Ute_M HOs SHOs"
  shows "weak_consensus (x \<circ> (rho 0)) decide rho"
  unfolding weak_consensus_def
  using ute_validity[OF run commR]
        ute_agreement[OF run commR]
        ute_termination[OF run commR commG]
  by auto

text \<open>
  By the reduction theorem, the correctness of the algorithm carries over
  to the fine-grained model of runs.
\<close>

theorem ute_weak_consensus_fg:
  assumes run: "fg_run Ute_M rho HOs SHOs (\<lambda>r q. undefined)"
      and commR: "\<forall>r. SHOcommPerRd Ute_M (HOs r) (SHOs r)"
      and commG: "SHOcommGlobal Ute_M HOs SHOs"
  shows "weak_consensus (\<lambda>p. x (state (rho 0) p)) decide (state \<circ> rho)"
    (is "weak_consensus ?inits _ _")
proof (rule local_property_reduction[OF run weak_consensus_is_local])
  fix crun
  assume crun: "CSHORun Ute_M crun HOs SHOs (\<lambda>r q. undefined)"
     and init: "crun 0 = state (rho 0)"
  from crun have "SHORun Ute_M crun HOs SHOs" by (unfold SHORun_def)
  from this commR commG 
  have "weak_consensus (x \<circ> (crun 0)) decide crun" 
    by (rule ute_weak_consensus)
  with init show "weak_consensus ?inits decide crun"
    by (simp add: o_def)
qed

end    \<comment> \<open>context @{text "ute_parameters"}\<close>

end    (* theory UteProof *)
