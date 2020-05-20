theory AteProof
imports AteDefs "../Reduction"
begin

context ate_parameters
begin

subsection \<open>Preliminary Lemmas\<close>

text \<open>
  If a process newly decides value \<open>v\<close> at some round,
  then it received more than \<open>E - \<alpha>\<close> messages holding \<open>v\<close>
  at this round.
\<close>

lemma decide_sent_msgs_threshold:
  assumes run: "SHORun Ate_M rho HOs SHOs"
  and comm: "SHOcommPerRd Ate_M (HOs r) (SHOs r)"
  and nvp: "decide (rho r p) \<noteq> Some v"
  and vp: "decide (rho (Suc r) p) = Some v"
  shows "card {qq. sendMsg Ate_M r qq p (rho r qq) = v} > E - \<alpha>"
proof -
  from run obtain \<mu>p
    where mu: "\<mu>p \<in> SHOmsgVectors Ate_M r p (rho r) (HOs r p) (SHOs r p)"
      and nxt: "nextState Ate_M r p (rho r p) \<mu>p (rho (Suc r) p)"
    by (auto simp: SHORun_eq SHOnextConfig_eq)
  from mu
  have "{qq. \<mu>p qq = Some v} - (HOs r p - SHOs r p)
          \<subseteq> {qq. sendMsg Ate_M r qq p (rho r qq) = v}"
       (is "?vrcvdp - ?ahop \<subseteq> ?vsentp") 
    by (auto simp: SHOmsgVectors_def)
  hence "card (?vrcvdp - ?ahop) \<le> card ?vsentp"
    and "card (?vrcvdp - ?ahop) \<ge> card ?vrcvdp - card ?ahop"
    by (auto simp: card_mono diff_card_le_card_Diff)
  hence "card ?vsentp \<ge> card ?vrcvdp - card ?ahop" by auto
  moreover
  from nxt nvp vp have "card ?vrcvdp > E"
    by (auto simp: Ate_SHOMachine_def nextState_def Ate_nextState_def)
  moreover
  from comm have "card (HOs r p - SHOs r p) \<le> \<alpha>"
    by (auto simp: Ate_SHOMachine_def Ate_commPerRd_def)
  ultimately
  show ?thesis using Egta by auto
qed

text \<open>
  If more than \<open>E - \<alpha>\<close> processes send a value \<open>v\<close> to some
  process \<open>q\<close> at some round, then \<open>q\<close> will receive at least
  \<open>N + 2*\<alpha> - E\<close> messages holding \<open>v\<close> at this round. 
\<close>

lemma other_values_received:
  assumes comm: "SHOcommPerRd Ate_M (HOs r) (SHOs r)"
  and nxt: "nextState Ate_M r q (rho r q) \<mu>q ((rho (Suc r)) q)"
  and muq: "\<mu>q \<in> SHOmsgVectors Ate_M r q (rho r) (HOs r q) (SHOs r q)"
  and vsent: "card {qq. sendMsg Ate_M r qq q (rho r qq) = v} > E - \<alpha>"
             (is "card ?vsent > _")
  shows "card ({qq. \<mu>q qq \<noteq> Some v} \<inter> HOs r q) \<le> N + 2*\<alpha> - E"
proof -
  from nxt muq
  have "({qq. \<mu>q qq \<noteq> Some v} \<inter> HOs r q) - (HOs r q - SHOs r q)
        \<subseteq>  {qq. sendMsg Ate_M r qq q (rho r qq) \<noteq> v}"
    (is "?notvrcvd - ?aho \<subseteq> ?notvsent") 
    unfolding SHOmsgVectors_def by auto
  hence "card ?notvsent \<ge> card (?notvrcvd - ?aho)"
    and "card (?notvrcvd - ?aho) \<ge> card ?notvrcvd - card ?aho"
    by (auto simp: card_mono diff_card_le_card_Diff)
  moreover
  from comm have "card ?aho \<le> \<alpha>"
    by (auto simp: Ate_SHOMachine_def Ate_commPerRd_def)
  moreover
  have 1: "card ?notvsent + card ?vsent = card (?notvsent \<union> ?vsent)"
    by (subst card_Un_Int) auto
  have "?notvsent \<union> ?vsent = (UNIV::Proc set)" by auto
  hence "card (?notvsent \<union> ?vsent) = N" by simp
  with 1 vsent have "card ?notvsent \<le>  N - (E + 1 - \<alpha>)" by auto
  ultimately
  show ?thesis using EltN Egta by auto
qed

text \<open>
  If more than \<open>E - \<alpha>\<close> processes send a value \<open>v\<close> to some
  process \<open>q\<close> at some round \<open>r\<close>, and if \<open>q\<close> receives more than
  \<open>T\<close> messages in \<open>r\<close>, then \<open>v\<close> is the most frequently
  received value by \<open>q\<close> in \<open>r\<close>.
\<close>

lemma mostOftenRcvd_v:
  assumes comm: "SHOcommPerRd Ate_M (HOs r) (SHOs r)"
  and nxt: "nextState Ate_M r q (rho r q) \<mu>q ((rho (Suc r)) q)"
  and muq: "\<mu>q \<in> SHOmsgVectors Ate_M r q (rho r) (HOs r q) (SHOs r q)"
  and threshold_T: "card {qq. \<mu>q qq \<noteq> None} > T"
  and threshold_E: "card {qq. sendMsg Ate_M r qq q (rho r qq) = v} > E - \<alpha>"
  shows "mostOftenRcvd \<mu>q = {v}"
proof -
  from muq have hodef:"HOs r q = {qq. \<mu>q qq \<noteq> None}"
    unfolding SHOmsgVectors_def by auto

  from comm nxt muq threshold_E
  have "card ({qq. \<mu>q qq \<noteq> Some v} \<inter> HOs r q) \<le> N + 2*\<alpha> - E"
    (is "card ?heardnotv \<le> _")
    by (rule other_values_received)
  moreover
  have "card ?heardnotv \<ge> T + 1 - card {qq. \<mu>q qq = Some v}"
  proof -
    from muq
    have "?heardnotv = (HOs r q) - {qq. \<mu>q qq = Some v}"
      and "{qq. \<mu>q qq = Some v} \<subseteq> HOs r q"
      unfolding SHOmsgVectors_def by auto
    hence "card ?heardnotv = card (HOs r q) - card {qq. \<mu>q qq = Some v}"
      by (auto simp: card_Diff_subset)
    with hodef threshold_T show ?thesis by auto
  qed
  ultimately
  have "card {qq. \<mu>q qq = Some v} > card ?heardnotv"
    using TNaE by auto
  moreover
  {
    fix w
    assume w: "w \<noteq> v"
    with hodef have "{qq. \<mu>q qq = Some w} \<subseteq> ?heardnotv" by auto
    hence "card {qq. \<mu>q qq = Some w} \<le> card ?heardnotv" by (auto simp: card_mono)
  }
  ultimately
  have "{w. card {qq. \<mu>q qq = Some w} \<ge> card {qq. \<mu>q qq = Some v}} = {v}"
    by force
  thus ?thesis unfolding mostOftenRcvd_def by auto
qed

text \<open>
  If at some round more than \<open>E - \<alpha>\<close> processes have their \<open>x\<close>
  variable set to \<open>v\<close>, then this is also true at next round.
\<close>

lemma common_x_induct:
  assumes run: "SHORun Ate_M rho HOs SHOs" 
  and comm: "SHOcommPerRd Ate_M (HOs (r+k)) (SHOs (r+k))"
  and ih: "card {qq. x (rho (r + k) qq) = v} > E - \<alpha>"
  shows "card {qq. x (rho (r + Suc k) qq) = v} > E - \<alpha>"
proof -
  from ih 
  have thrE:"\<forall>pp. card {qq. sendMsg Ate_M (r + k) qq pp (rho (r + k) qq) = v}
                      > E - \<alpha>"
    by (auto simp: Ate_SHOMachine_def Ate_sendMsg_def)

  {
    fix qq
    assume kv:"x (rho (r + k) qq) = v"
    from run obtain \<mu>qq
      where nxt: "nextState Ate_M (r + k) qq (rho (r + k) qq) \<mu>qq ((rho (Suc (r + k))) qq)"
        and muq: "\<mu>qq \<in> SHOmsgVectors Ate_M (r + k) qq (rho (r + k)) 
                                         (HOs (r + k) qq) (SHOs (r + k) qq)"
      by (auto simp: SHORun_eq SHOnextConfig_eq)
        
    have "x (rho (r + Suc k) qq) = v"
    proof (cases "card {pp. \<mu>qq pp \<noteq> None} > T")
      case True
      with comm nxt muq thrE have "mostOftenRcvd \<mu>qq = {v}"
        by (auto dest: mostOftenRcvd_v)
      with nxt True show "x (rho (r + Suc k) qq) = v"
        by (auto simp: Ate_SHOMachine_def nextState_def Ate_nextState_def)
    next
      case False
      with nxt have "x (rho (r + Suc k) qq) = x (rho (r + k) qq)"
        by (auto simp: Ate_SHOMachine_def nextState_def Ate_nextState_def)
      with kv show "x (rho (r + Suc k) qq) = v" by simp
    qed
  }
  hence "{qq. x (rho (r + k) qq) = v} \<subseteq> {qq. x (rho (r + Suc k) qq) = v}"
    by auto
  hence "card {qq. x (rho (r + k) qq) = v} \<le> card {qq. x (rho (r + Suc k) qq) = v}"
    by (auto simp: card_mono)
  with ih show ?thesis by auto
qed

text \<open>
  Whenever some process newly decides value \<open>v\<close>, then any
  process that updates its \<open>x\<close> variable will set it to \<open>v\<close>.
\<close>
(* The proof mainly relies on lemmas @{text decide_sent_msgs_threshold},
   @{text mostOftenRcvd_v} and @{text common_x_induct}. *)

lemma common_x:
  assumes run: "SHORun Ate_M rho HOs SHOs"
  and comm: "\<forall>r. SHOcommPerRd (Ate_M::(Proc, 'val::linorder pstate, 'val) SHOMachine)
                              (HOs r) (SHOs r)"
  and d1: "decide (rho r p) \<noteq> Some v"
  and d2: "decide (rho (Suc r) p) = Some v"
  and qupdatex: "x (rho (r + Suc k) q) \<noteq> x (rho (r + k) q)"
  shows "x (rho (r + Suc k) q) = v"
proof -
  from comm 
  have "SHOcommPerRd (Ate_M::(Proc, 'val::linorder pstate, 'val) SHOMachine) 
                     (HOs (r+k)) (SHOs (r+k))" ..
  moreover
  from run obtain \<mu>q
    where nxt: "nextState Ate_M (r+k) q (rho (r+k) q) \<mu>q (rho (r + Suc k) q)"
      and muq: "\<mu>q \<in> SHOmsgVectors Ate_M (r+k) q (rho (r+k))
                                   (HOs (r+k) q) (SHOs (r+k) q)"
    by (auto simp: SHORun_eq SHOnextConfig_eq)
  moreover
  from nxt qupdatex 
  have threshold_T: "card {qq. \<mu>q qq \<noteq> None} > T"
    and xsmall: "x (rho (r + Suc k) q) = Min (mostOftenRcvd \<mu>q)"
    by (auto simp: Ate_SHOMachine_def nextState_def Ate_nextState_def)
  moreover
  have "E - \<alpha> < card {qq. x (rho (r + k) qq) = v}"
  proof (induct k)
    from run comm d1 d2
    have "E - \<alpha> < card {qq. sendMsg Ate_M r qq p (rho r qq) = v}"
      by (auto dest: decide_sent_msgs_threshold)
    thus "E - \<alpha> < card {qq. x (rho (r + 0) qq) = v}"
      by (auto simp: Ate_SHOMachine_def Ate_sendMsg_def)
  next
    fix k
    assume "E - \<alpha> < card {qq. x (rho (r + k) qq) = v}"
    with run comm show "E - \<alpha> < card {qq. x (rho (r + Suc k) qq) = v}"
      by (auto dest: common_x_induct)
  qed
  with run
  have "E - \<alpha> < card {qq. sendMsg Ate_M (r+k) qq q (rho (r+k) qq) = v}"
    by (auto simp: Ate_SHOMachine_def Ate_sendMsg_def SHORun_eq SHOnextConfig_eq)
  ultimately
  have "mostOftenRcvd \<mu>q = {v}" by (auto dest:mostOftenRcvd_v)
  with xsmall show ?thesis by auto
qed

text \<open>
  A process that holds some decision \<open>v\<close> has decided \<open>v\<close>
  sometime in the past.
\<close>
lemma decisionNonNullThenDecided:
  assumes run: "SHORun Ate_M rho HOs SHOs"
      and dec: "decide (rho n p) = Some v"
  obtains m where "m < n"
              and "decide (rho m p) \<noteq> Some v"
              and "decide (rho (Suc m) p) = Some v"
proof -
  let "?dec k" = "decide (rho k p)"
  have "(\<forall>m<n. ?dec (Suc m) \<noteq> ?dec m \<longrightarrow> ?dec (Suc m) \<noteq> Some v) \<longrightarrow> ?dec n \<noteq> Some v"
    (is "?P n" is "?A n \<longrightarrow> _")
  proof (induct n)
    from run show "?P 0"
      by (auto simp: Ate_SHOMachine_def SHORun_eq HOinitConfig_eq
                     initState_def Ate_initState_def)
  next
    fix n
    assume ih: "?P n" thus "?P (Suc n)" by force
  qed
  with dec that show ?thesis by auto
qed


subsection \<open>Proof of Validity\<close>

text \<open>
  Validity asserts that if all processes were initialized with the same value,
  then no other value may ever be decided.
\<close>

theorem ate_validity:
  assumes run: "SHORun Ate_M rho HOs SHOs"
  and comm: "\<forall>r. SHOcommPerRd Ate_M (HOs r) (SHOs r)"
  and initv: "\<forall>q. x (rho 0 q) = v"
  and dp: "decide (rho r p) = Some w"
  shows "w = v"
proof -
  {
    fix r
    have "\<forall>qq. sendMsg Ate_M r qq p (rho r qq) = v"
    proof (induct r)
      from run initv show "\<forall>qq. sendMsg Ate_M 0 qq p (rho 0 qq) = v"
        by (auto simp: SHORun_eq SHOnextConfig_eq Ate_SHOMachine_def Ate_sendMsg_def)
    next
      fix r
      assume ih:"\<forall>qq. sendMsg Ate_M r qq p (rho r qq) = v"

      have "\<forall>qq. x (rho (Suc r) qq) = v"
      proof
        fix qq
        from run obtain \<mu>qq
          where nxt: "nextState Ate_M r qq (rho r qq) \<mu>qq (rho (Suc r) qq)"
            and mu: "\<mu>qq \<in> SHOmsgVectors Ate_M r qq (rho r) (HOs r qq) (SHOs r qq)"
          by (auto simp: SHORun_eq SHOnextConfig_eq)
        from nxt
        have "(card {pp. \<mu>qq pp \<noteq> None} > T \<and> x (rho (Suc r) qq) = Min (mostOftenRcvd \<mu>qq))
            \<or> (card {pp. \<mu>qq pp \<noteq> None} \<le> T \<and> x (rho (Suc r) qq) = x (rho r qq))"
          by (auto simp: Ate_SHOMachine_def nextState_def Ate_nextState_def)
        thus "x (rho (Suc r) qq) = v"
        proof safe
          assume "x (rho (Suc r) qq) = x (rho r qq)"
          with ih show "?thesis"
            by (auto simp: Ate_SHOMachine_def Ate_sendMsg_def)
        next
          assume threshold_T:"T < card {pp. \<mu>qq pp \<noteq> None}"
             and xsmall:"x (rho (Suc r) qq) = Min (mostOftenRcvd \<mu>qq)"
                   
          have "card {pp. \<exists>w. w \<noteq> v \<and> \<mu>qq pp = Some w} \<le> T div 2"
          proof -
            from comm have 1:"card (HOs r qq - SHOs r qq) \<le> \<alpha>"
              by (auto simp: Ate_SHOMachine_def Ate_commPerRd_def)
            moreover
            from mu ih
            have "SHOs r qq \<inter> HOs r qq \<subseteq> {pp. \<mu>qq pp = Some v}"
              and "HOs r qq = {pp. \<mu>qq pp \<noteq> None}"
              by (auto simp: SHOmsgVectors_def Ate_SHOMachine_def Ate_sendMsg_def)
            hence "{pp. \<mu>qq pp \<noteq> None} - {pp. \<mu>qq pp = Some v} 
                   \<subseteq> HOs r qq - SHOs r qq"
              by auto
            hence "card ({pp. \<mu>qq pp \<noteq> None} - {pp. \<mu>qq pp = Some v})
                      \<le> card (HOs r qq - SHOs r qq)"
              by (auto simp:card_mono)
            ultimately
            have "card ({pp. \<mu>qq pp \<noteq> None} - {pp. \<mu>qq pp = Some v}) \<le> T div 2"
              using Tge2a by auto
            moreover
            have "{pp. \<mu>qq pp \<noteq> None} - {pp. \<mu>qq pp = Some v}
                  = {pp. \<exists>w. w \<noteq> v \<and> \<mu>qq pp = Some w}" by auto
            ultimately
            show ?thesis by simp
          qed
          moreover
          have "{pp. \<mu>qq pp \<noteq> None}
                = {pp. \<mu>qq pp = Some v} \<union> {pp. \<exists>w. w \<noteq> v \<and> \<mu>qq pp = Some w}"
            and "{pp. \<mu>qq pp = Some v} \<inter> {pp. \<exists>w. w \<noteq> v \<and> \<mu>qq pp = Some w} = {}" 
            by auto
          hence "card {pp. \<mu>qq pp \<noteq> None}
                 = card {pp. \<mu>qq pp = Some v} + card {pp. \<exists>w. w \<noteq> v \<and> \<mu>qq pp = Some w}"
            by (auto simp: card_Un_Int)
          moreover
          note threshold_T
          ultimately
          have "card {pp. \<mu>qq pp = Some v} > card {pp. \<exists>w. w \<noteq> v \<and> \<mu>qq pp = Some w}"
            by auto
          moreover
          {
            fix w
            assume "w \<noteq> v"
            hence "{pp. \<mu>qq pp = Some w} \<subseteq> {pp. \<exists>w. w \<noteq> v \<and> \<mu>qq pp = Some w}" 
              by auto
            hence "card {pp. \<mu>qq pp = Some w} \<le> card {pp. \<exists>w. w \<noteq> v \<and> \<mu>qq pp = Some w}"
              by (auto simp: card_mono)
          }
          ultimately
          have zz:"\<And>w. w \<noteq> v \<Longrightarrow> 
                       card {pp. \<mu>qq pp = Some w} < card {pp. \<mu>qq pp = Some v}"
            by force
          hence "\<And>w. card {pp. \<mu>qq pp = Some v} \<le> card {pp. \<mu>qq pp = Some w}
                      \<Longrightarrow> w = v" 
            by force
          with zz have "mostOftenRcvd \<mu>qq = {v}"
            by (force simp: mostOftenRcvd_def)
          with xsmall show "x (rho (Suc r) qq) = v" by auto
        qed
      qed
      thus "\<forall>qq. sendMsg Ate_M (Suc r) qq p (rho (Suc r) qq) = v"
        by (auto simp: Ate_SHOMachine_def Ate_sendMsg_def)
    qed
  }
  note P = this

  from run dp obtain rp
    where rp: "rp < r" "decide (rho rp p) \<noteq> Some w" 
              "decide (rho (Suc rp) p) = Some w"
    by (rule decisionNonNullThenDecided)

  from run obtain \<mu>p
    where nxt: "nextState Ate_M rp p (rho rp p) \<mu>p (rho (Suc rp) p)"
      and mu: "\<mu>p \<in> SHOmsgVectors Ate_M rp p (rho rp) (HOs rp p) (SHOs rp p)"
    by (auto simp: SHORun_eq SHOnextConfig_eq)

  {
    fix w
    assume w: "w \<noteq> v"
    from comm have "card (HOs rp p - SHOs rp p) \<le> \<alpha>"
      by (auto simp: Ate_SHOMachine_def Ate_commPerRd_def)
    moreover
    from mu P
    have "SHOs rp p \<inter> HOs rp p \<subseteq> {pp. \<mu>p pp = Some v}"
      and "HOs rp p = {pp. \<mu>p pp \<noteq> None}"
      by (auto simp: SHOmsgVectors_def)
    hence "{pp. \<mu>p pp \<noteq> None} - {pp. \<mu>p pp = Some v}
           \<subseteq> HOs rp p - SHOs rp p"
      by auto
    hence "card ({pp. \<mu>p pp \<noteq> None} - {pp. \<mu>p pp = Some v})
            \<le> card (HOs rp p - SHOs rp p)"
      by (auto simp: card_mono)
    ultimately
    have "card ({pp. \<mu>p pp \<noteq> None} - {pp. \<mu>p pp = Some v}) < E"
      using Egta by auto
    moreover
    from w have "{pp. \<mu>p pp = Some w} 
                 \<subseteq> {pp. \<mu>p pp \<noteq> None} - {pp. \<mu>p pp = Some v}"
      by auto
    hence "card {pp. \<mu>p pp = Some w} 
             \<le> card ({pp. \<mu>p pp \<noteq> None} - {pp. \<mu>p pp = Some v})"
      by (auto simp: card_mono)
    ultimately
    have "card {pp. \<mu>p pp = Some w} < E" by simp
  }
  hence PP: "\<And>w. card {pp. \<mu>p pp = Some w} \<ge> E \<Longrightarrow> w = v" by force

  from rp nxt mu have "card {q. \<mu>p q = Some w} > E"
    by (auto simp: SHOmsgVectors_def Ate_SHOMachine_def 
                   nextState_def Ate_nextState_def)
  with PP show ?thesis by auto
qed


subsection \<open>Proof of Agreement\<close>

text \<open>
  If two processes decide at the some round, they decide the same value.
\<close>
(* The proof mainly relies on lemma @{text decide_sent_msgs_threshold}. *)

lemma common_decision:
  assumes run: "SHORun Ate_M rho HOs SHOs"
  and comm: "SHOcommPerRd Ate_M (HOs r) (SHOs r)"
  and nvp: "decide (rho r p) \<noteq> Some v"
  and vp: "decide (rho (Suc r) p) = Some v"
  and nwq: "decide (rho r q) \<noteq> Some w"
  and wq: "decide (rho (Suc r) q) = Some w"
  shows "w = v"
proof -
  have gtn: "card {qq. sendMsg Ate_M r qq p (rho r qq) = v}
             + card {qq. sendMsg Ate_M r qq q (rho r qq) = w} > N"
  proof -
    from run comm nvp vp
    have "card {qq. sendMsg Ate_M r qq p (rho r qq) = v} > E - \<alpha>"
      by (rule decide_sent_msgs_threshold)
    moreover
    from run comm nwq wq
    have "card {qq. sendMsg Ate_M r qq q (rho r qq) = w} > E - \<alpha>"
      by (rule decide_sent_msgs_threshold)
    ultimately
    show ?thesis using majE by auto
  qed

  show ?thesis
  proof (rule ccontr)
    assume vw:"w \<noteq> v"
    have "\<forall>qq. sendMsg Ate_M r qq p (rho r qq) = sendMsg Ate_M r qq q (rho r qq)"
      by (auto simp: Ate_SHOMachine_def Ate_sendMsg_def)
    with vw
    have "{qq. sendMsg Ate_M r qq p (rho r qq) = v}
          \<inter> {qq. sendMsg Ate_M r qq q (rho r qq) = w} = {}"
      by auto
    with gtn
    have "card ({qq. sendMsg Ate_M r qq p (rho r qq) = v} 
                 \<union> {qq. sendMsg Ate_M r qq q (rho r qq) = w}) > N"
      by (auto simp: card_Un_Int)
    moreover
    have "card ({qq. sendMsg Ate_M r qq p (rho r qq) = v} 
                 \<union> {qq. sendMsg Ate_M r qq q (rho r qq) = w}) \<le> N"
      by (auto simp: card_mono)
    ultimately
    show "False" by auto
  qed
qed

text \<open>
  If process \<open>p\<close> decides at step \<open>r\<close> and process \<open>q\<close> decides
  at some later step \<open>r+k\<close> then \<open>p\<close> and \<open>q\<close> decide the
  same value.
\<close>
(*
  The proof mainly relies on lemmas @{text common_decision}, @{text common_x},
  @{text decide_with_threshold_E}, @{text unique_majority_E_\<alpha>} 
  and @{text  decide_sent_msgs_threshold}.
*)

lemma laterProcessDecidesSameValue :
  assumes run: "SHORun Ate_M rho HOs SHOs"
  and comm: "\<forall>r. SHOcommPerRd Ate_M (HOs r) (SHOs r)"
  and nd1: "decide (rho r p) \<noteq> Some v"
  and d1: "decide (rho (Suc r) p) = Some v"
  and nd2: "decide (rho (r+k) q) \<noteq> Some w"
  and d2: "decide (rho (Suc (r+k)) q) = Some w"
  shows "w = v"
proof (rule ccontr)
  assume vdifw:"w \<noteq> v"
  have kgt0: "k > 0"
  proof (rule ccontr)
    assume "\<not> k > 0"
    hence "k = 0" by auto
    with run comm nd1 d1 nd2 d2 have "w = v"
      by (auto dest: common_decision)
    with vdifw show False ..
  qed

  have 1: "{qq. sendMsg Ate_M r qq p (rho r qq) = v}
           \<inter> {qq. sendMsg Ate_M (r+k) qq q (rho (r+k) qq) = w} = {}"
    (is "?sentv \<inter> ?sentw = {}")
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain qq
      where xrv: "x (rho r qq) = v" and rkw: "x (rho (r+k) qq) = w"
      by (auto simp: Ate_SHOMachine_def Ate_sendMsg_def)
    have "\<exists>k' < k. x (rho (r + k') qq) \<noteq> w \<and> x (rho (r + Suc k') qq) = w"
    proof (rule ccontr)
      assume f: "\<not> ?thesis"
      {
        fix k'
        assume kk':"k' < k" hence "x (rho (r + k') qq) \<noteq> w"
        proof (induct k')
          from xrv vdifw
          show "x (rho (r + 0) qq) \<noteq> w" by simp
        next
          fix k'
          assume ih:"k' < k \<Longrightarrow> x (rho (r + k') qq) \<noteq> w"
             and ksk':"Suc k' < k"
          from ksk' have "k' < k" by simp
          with ih f  show "x (rho (r + Suc k') qq) \<noteq> w" by auto
        qed
      }
      with f have "\<forall>k' < k. x (rho (r + Suc k') qq) \<noteq> w" by auto
      moreover
      from kgt0 have "k - 1 < k" and kk:"Suc (k - 1) = k" by auto
      ultimately
      have "x (rho (r + Suc (k - 1)) qq) \<noteq> w" by blast
      with rkw kk show "False" by simp
    qed
    then obtain k'
      where "k' < k" 
        and w: "x (rho (r + Suc k') qq) = w"
        and qqupdatex: "x (rho (r + Suc k') qq) \<noteq> x (rho (r + k') qq)" 
      by auto
    from run comm nd1 d1 qqupdatex
    have "x (rho (r + Suc k') qq) = v" by (rule common_x)
    with w vdifw show False by simp
  qed
  from run comm nd1 d1 have sentv: "card ?sentv > E - \<alpha>"
    by (auto dest: decide_sent_msgs_threshold)
  from run comm nd2 d2 have "card ?sentw > E - \<alpha>"
    by (auto dest: decide_sent_msgs_threshold)
  with sentv majE have "(card ?sentv) + (card ?sentw) > N"
    by simp
  with 1 vdifw  have 2: "card (?sentv \<union> ?sentw) > N"
    by (auto simp: card_Un_Int)
  have "card (?sentv \<union> ?sentw) \<le> N"
    by (auto simp: card_mono)
  with 2 show "False" by simp
qed

text \<open>
  The Agreement property is now an immediate consequence.
\<close>
(*
  The proof mainly relies on lemmas @{text decisionNonNullThenDecided}
  and @{text laterProcessDecidesSameValue}.
*)

theorem ate_agreement:
  assumes run: "SHORun Ate_M rho HOs SHOs"
  and comm: "\<forall>r. SHOcommPerRd Ate_M (HOs r) (SHOs r)"
  and p: "decide (rho m p) = Some v"
  and q: "decide (rho n q) = Some w"
  shows "w = v"
proof -
  from run p obtain k where
    k: "k < m" "decide (rho k p) \<noteq> Some v" "decide (rho (Suc k) p) = Some v"
    by (rule decisionNonNullThenDecided)
  from run q obtain l where
    l: "l < n" "decide (rho l q) \<noteq> Some w" "decide (rho (Suc l) q) = Some w"
    by (rule decisionNonNullThenDecided)
  show ?thesis
  proof (cases "k \<le> l")
    case True
    then obtain i where "l = k+i" by (auto simp add: le_iff_add)
    with run comm k l show ?thesis
      by (auto dest: laterProcessDecidesSameValue)
  next
    case False
    hence "l \<le> k" by simp
    then obtain i where m: "k = l+i" by (auto simp add: le_iff_add)
    with run comm k l show ?thesis
      by (auto dest: laterProcessDecidesSameValue)
  qed
qed


subsection \<open>Proof of Termination\<close>

text \<open>
  We now prove that every process must eventually decide, given the
  global and round-by-round communication predicates.
\<close>
(* The proof relies on previous lemmas @{text common_x_induct} and @{text mostOftenRcvd_v}. *)

theorem ate_termination:
  assumes run: "SHORun Ate_M rho HOs SHOs"
  and commR: "\<forall>r. (SHOcommPerRd::((Proc, 'val::linorder pstate, 'val) SHOMachine)
                                     \<Rightarrow> (Proc HO) \<Rightarrow> (Proc HO) \<Rightarrow> bool) 
                  Ate_M (HOs r) (SHOs r)"
  and commG: "SHOcommGlobal Ate_M HOs SHOs"
  shows "\<exists>r v. decide (rho r p) = Some v"
proof -
  from commG obtain r' \<pi>1 \<pi>2
    where \<pi>ea: "card \<pi>1 > E - \<alpha>"
      and \<pi>t: "card \<pi>2 > T"
      and  hosho: "\<forall>p \<in> \<pi>1. (HOs r' p = \<pi>2 \<and> SHOs r' p \<inter> HOs r' p = \<pi>2)"
    by (auto simp: Ate_SHOMachine_def Ate_commGlobal_def)

  obtain v where
    P1: "\<forall>pp. card {qq. sendMsg Ate_M (Suc r') qq pp (rho (Suc r') qq) = v} > E - \<alpha>"
  proof -
    have "\<forall>p \<in> \<pi>1. \<forall>q \<in> \<pi>1. x (rho (Suc r') p) = x (rho (Suc r') q)"
    proof (clarify)
      fix p q
      assume p: "p \<in> \<pi>1" and q: "q \<in> \<pi>1"

      from run obtain \<mu>p
        where nxtp: "nextState Ate_M r' p (rho r' p) \<mu>p (rho (Suc r') p)"
          and mup: "\<mu>p \<in> SHOmsgVectors Ate_M r' p (rho r') (HOs r' p) (SHOs r' p)"
        by (auto simp: SHORun_eq SHOnextConfig_eq)

      from run obtain \<mu>q
        where nxtq: "nextState Ate_M r' q (rho r' q) \<mu>q (rho (Suc r') q)"
          and muq: "\<mu>q \<in> SHOmsgVectors Ate_M r' q (rho r') (HOs r' q) (SHOs r' q)"
        by (auto simp: SHORun_eq SHOnextConfig_eq)

      from mup muq p q
      have "{qq. \<mu>q qq \<noteq> None}  = HOs r' q"
        and 2:"{qq. \<mu>q qq = Some (sendMsg Ate_M r' qq q (rho r' qq))}
               \<supseteq> SHOs r' q \<inter> HOs r' q"
        and "{qq. \<mu>p qq \<noteq> None}  = HOs r' p"
        and 4:"{qq. \<mu>p qq = Some (sendMsg Ate_M r' qq p (rho r' qq))}
               \<supseteq> SHOs r' p \<inter> HOs r' p"
        by (auto simp: SHOmsgVectors_def)
      with p q hosho 
      have aa:"\<pi>2 = {qq. \<mu>q qq \<noteq> None}"
        and cc:"\<pi>2 = {qq. \<mu>p qq \<noteq> None}" by auto
      from p q hosho 2
      have bb:"{qq. \<mu>q qq = Some (sendMsg Ate_M r' qq q (rho r' qq))} \<supseteq> \<pi>2"
        by auto
      from p q hosho 4
      have dd:"{qq. \<mu>p qq = Some (sendMsg Ate_M r' qq p (rho r' qq))} \<supseteq> \<pi>2" 
        by auto
      have "Min (mostOftenRcvd \<mu>p) = Min (mostOftenRcvd \<mu>q)"
      proof -
        have "\<forall>qq. sendMsg Ate_M r' qq p (rho r' qq)
                   = sendMsg Ate_M r' qq q (rho r' qq)"
          by (auto simp: Ate_SHOMachine_def Ate_sendMsg_def)
        with aa bb cc dd have "\<forall>qq. \<mu>p qq \<noteq> None \<longrightarrow> \<mu>p qq = \<mu>q qq"
          by force
        moreover
        from aa bb cc dd
        have "{qq. \<mu>p qq \<noteq> None} = {qq. \<mu>q qq \<noteq> None}" by auto
        hence "\<forall>qq. \<mu>p qq = None \<longleftrightarrow> \<mu>q qq = None" by blast
        hence "\<forall>qq. \<mu>p qq = None \<longrightarrow> \<mu>p qq = \<mu>q qq" by auto
        ultimately
        have "\<forall>qq. \<mu>p qq = \<mu>q qq" by blast
        thus ?thesis by (auto simp: mostOftenRcvd_def)
      qed
      with \<pi>t aa nxtq \<pi>t cc nxtp
      show "x (rho (Suc r') p) = x (rho (Suc r') q)"
        by (auto simp: Ate_SHOMachine_def nextState_def Ate_nextState_def)
    qed
    then obtain v where Pv:"\<forall>p \<in> \<pi>1. x (rho (Suc r') p) = v" by blast
    {
      fix pp
      from Pv have "\<forall>p \<in> \<pi>1. sendMsg Ate_M (Suc r') p pp (rho (Suc r') p) = v"
        by (auto simp: Ate_SHOMachine_def Ate_sendMsg_def)
      hence "card \<pi>1 \<le> card {qq. sendMsg Ate_M (Suc r') qq pp (rho (Suc r') qq) = v}"
        by (auto intro: card_mono)
      with \<pi>ea
      have "E - \<alpha> < card {qq. sendMsg Ate_M (Suc r') qq pp (rho (Suc r') qq) = v}"
        by simp
    }
    with that show ?thesis by blast
  qed

  {
    fix k pp
    have "E - \<alpha> < card {qq. sendMsg Ate_M (Suc r' + k) qq pp (rho (Suc r' + k) qq) = v}"
      (is "?P k")
    proof (induct k)
      from P1 show "?P 0" by simp
    next
      fix k
      assume ih: "?P k"
      from commR
      have "(SHOcommPerRd::((Proc, 'val::linorder pstate, 'val) SHOMachine) 
                               \<Rightarrow> (Proc HO) \<Rightarrow> (Proc HO) \<Rightarrow> bool) 
                Ate_M (HOs (Suc r' + k)) (SHOs (Suc r' + k))" ..
      moreover
      from ih have "E - \<alpha> < card {qq. x (rho (Suc r' + k) qq) = v}"
        by (auto simp: Ate_SHOMachine_def Ate_sendMsg_def)
      ultimately
      have "E - \<alpha> < card {qq. x (rho (Suc r' + Suc k) qq) = v}"
        by (rule common_x_induct[OF run])
      thus "?P (Suc k)"
        by (auto simp: Ate_SHOMachine_def Ate_sendMsg_def)
    qed
  }
  note P2 = this

  {
    fix k pp
    assume ppupdatex: "x (rho (Suc r' + Suc k) pp) \<noteq> x (rho (Suc r' + k) pp)"

    from commR 
    have "(SHOcommPerRd::((Proc, 'val::linorder pstate, 'val) SHOMachine)
                            \<Rightarrow> (Proc HO) \<Rightarrow> (Proc HO) \<Rightarrow> bool)
              Ate_M (HOs (Suc r' + k)) (SHOs (Suc r' + k))" ..
    moreover
    from run obtain \<mu>pp
      where nxt:"nextState Ate_M (Suc r' + k) pp (rho (Suc r' + k) pp) \<mu>pp 
                           (rho (Suc r' + Suc k) pp)"
        and mu: "\<mu>pp \<in> SHOmsgVectors Ate_M (Suc r' + k) pp (rho (Suc r' + k))
                           (HOs (Suc r' + k) pp) (SHOs (Suc r' + k) pp)"
      by (auto simp: SHORun_eq SHOnextConfig_eq)
    moreover
    from nxt ppupdatex
    have threshold_T: "card {qq. \<mu>pp qq \<noteq> None} > T"
      and xsmall: "x (rho (Suc r' + Suc k) pp) = Min (mostOftenRcvd \<mu>pp)"
      by (auto simp: Ate_SHOMachine_def nextState_def Ate_nextState_def)
    moreover
    from P2
    have "E - \<alpha> < card {qq. sendMsg Ate_M (Suc r' + k) qq pp (rho (Suc r' + k) qq) = v}" .
    ultimately
    have "mostOftenRcvd \<mu>pp = {v}" by (auto dest!: mostOftenRcvd_v)
    with xsmall 
    have "x (rho (Suc r' + Suc k) pp) = v" by simp
  }
  note P3 = this

  have P4:"\<forall>pp. \<exists>k. x (rho (Suc r' + Suc k) pp) = v"
  proof
    fix pp
    from commG have "\<exists>r'' > r'. card (HOs r'' pp) > T"
      by (auto simp: Ate_SHOMachine_def Ate_commGlobal_def)
    then obtain k where "Suc r' + k > r'" and t:"card (HOs (Suc r' + k) pp) > T"
      by (auto dest: less_imp_Suc_add)
    moreover
    from run obtain \<mu>pp
      where nxt: "nextState Ate_M (Suc r' + k) pp (rho (Suc r' + k) pp) \<mu>pp
                                  (rho (Suc r' + Suc k) pp)"
        and mu: "\<mu>pp \<in> SHOmsgVectors Ate_M (Suc r' + k) pp (rho (Suc r' + k))
                                  (HOs (Suc r' + k) pp) (SHOs (Suc r' + k) pp)"
      by (auto simp: SHORun_eq SHOnextConfig_eq)
    moreover
    have "x (rho (Suc r' + Suc k) pp) = v"
    proof -
      from commR
      have "(SHOcommPerRd::((Proc, 'val::linorder pstate, 'val::linorder) SHOMachine)
                                \<Rightarrow> (Proc HO) \<Rightarrow> (Proc HO) \<Rightarrow> bool) 
                Ate_M (HOs (Suc r' + k)) (SHOs (Suc r' + k))" ..
      moreover
      from mu have "HOs (Suc r' + k) pp = {q. \<mu>pp q \<noteq> None}"
        by (auto simp: SHOmsgVectors_def)
      with nxt t
      have threshold_T: "card {q. \<mu>pp q \<noteq> None} > T"
        and xsmall: "x (rho (Suc r' + Suc k) pp) = Min (mostOftenRcvd \<mu>pp)"
        by (auto simp: Ate_SHOMachine_def nextState_def Ate_nextState_def)
      moreover
      from P2
      have "E - \<alpha> < card {qq. sendMsg Ate_M (Suc r' + k) qq pp (rho (Suc r' + k) qq) = v}" .
      ultimately
      have "mostOftenRcvd \<mu>pp = {v}"  
        using nxt mu by (auto dest!: mostOftenRcvd_v)
      with xsmall show ?thesis by auto
    qed
    thus "\<exists>k. x (rho (Suc r' + Suc k) pp) = v" ..
  qed

  have P5a: "\<forall>pp. \<exists>rr. \<forall>k. x (rho (rr + k) pp) = v"
  proof
    fix pp
    from P4 obtain rk where
      xrrv: "x (rho (Suc r' + Suc rk) pp) = v" (is "x (rho ?rr pp) = v")
      by blast
    have "\<forall>k. x (rho (?rr + k) pp) = v"
    proof
      fix k
      show "x (rho (?rr + k) pp) = v" 
      proof (induct k)
        from xrrv show "x (rho (?rr + 0) pp) = v" by simp
      next
        fix k
        assume ih: "x (rho (?rr + k) pp) = v"
        obtain k' where rrk: "Suc r' + k' = ?rr + k" by auto
        show "x (rho (?rr + Suc k) pp) = v"
        proof (rule ccontr)
          assume nv: "x (rho (?rr + Suc k) pp) \<noteq> v"
          with rrk ih
          have "x (rho (Suc r' + Suc k') pp) \<noteq> x (rho (Suc r' + k') pp)"
            by (simp add: ac_simps)
          hence "x (rho (Suc r' + Suc k') pp) = v" by (rule P3)
          with rrk nv show False by (simp add: ac_simps)
        qed
      qed
    qed
    thus "\<exists>rr. \<forall>k. x (rho (rr + k) pp) = v" by blast
  qed

  from P5a have "\<exists>F. \<forall>pp k. x (rho (F pp + k) pp) = v" by (rule choice)
  then obtain R::"(Proc \<Rightarrow> nat)"
    where imgR: "R ` (UNIV::Proc set) \<noteq> {}"
      and R: "\<forall>pp k. x (rho (R pp + k) pp) = v" 
    by blast
  define rr where "rr = Max (R ` UNIV)"

  have P5: "\<forall>r' > rr. \<forall>pp. x (rho r' pp) = v"
  proof (clarify)
    fix r' pp
    assume r': "r' > rr"
    hence "r' > R pp" by (auto simp: rr_def)
    then obtain i where "r' = R pp + i"
      by (auto dest: less_imp_Suc_add)
    with R show "x (rho r' pp) = v" by auto
  qed

  from commG have "\<exists>r' > rr. card (SHOs r' p \<inter> HOs r' p) > E"
    by (auto simp: Ate_SHOMachine_def Ate_commGlobal_def)
  with P5 obtain r'
    where "r' > rr"
      and "card (SHOs r' p \<inter> HOs r' p) > E"
      and "\<forall>pp. sendMsg Ate_M r' pp p (rho r' pp) = v"
    by (auto simp: Ate_SHOMachine_def Ate_sendMsg_def)
  moreover
  from run obtain \<mu>p
    where nxt: "nextState Ate_M r' p (rho r' p) \<mu>p (rho (Suc r') p)"
      and mu: "\<mu>p \<in> SHOmsgVectors Ate_M r' p (rho r') (HOs r' p) (SHOs r' p)"
    by (auto simp: SHORun_eq SHOnextConfig_eq)
  from mu 
  have "card (SHOs r' p \<inter> HOs r' p)
        \<le> card {q. \<mu>p q = Some (sendMsg Ate_M r' q p (rho r' q))}"
    by (auto simp: SHOmsgVectors_def intro: card_mono)
  ultimately
  have threshold_E: "card {q. \<mu>p q = Some v} > E" by auto
  with nxt show ?thesis
    by (auto simp: Ate_SHOMachine_def nextState_def Ate_nextState_def)
qed


subsection \<open>\ate{} Solves Weak Consensus\<close>

text \<open>
  Summing up, all (coarse-grained) runs of \ate{} for
  HO and SHO collections that satisfy the communication predicate 
  satisfy the Weak Consensus property.
\<close>

theorem ate_weak_consensus:
  assumes run: "SHORun Ate_M rho HOs SHOs"
      and commR: "\<forall>r. SHOcommPerRd Ate_M (HOs r) (SHOs r)"
      and commG: "SHOcommGlobal Ate_M HOs SHOs"
  shows "weak_consensus (x \<circ> (rho 0)) decide rho"
  unfolding weak_consensus_def using assms
  by (auto elim: ate_validity ate_agreement ate_termination)

text \<open>
  By the reduction theorem, the correctness of the algorithm carries over
  to the fine-grained model of runs.
\<close>

theorem ate_weak_consensus_fg:
  assumes run: "fg_run Ate_M rho HOs SHOs (\<lambda>r q. undefined)"
      and commR: "\<forall>r. SHOcommPerRd Ate_M (HOs r) (SHOs r)"
      and commG: "SHOcommGlobal Ate_M HOs SHOs"
  shows "weak_consensus (\<lambda>p. x (state (rho 0) p)) decide (state \<circ> rho)"
    (is "weak_consensus ?inits _ _")
proof (rule local_property_reduction[OF run weak_consensus_is_local])
  fix crun
  assume crun: "CSHORun Ate_M crun HOs SHOs (\<lambda>r q. undefined)"
     and init: "crun 0 = state (rho 0)"
  from crun have "SHORun Ate_M crun HOs SHOs" by (unfold SHORun_def)
  from this commR commG 
  have "weak_consensus (x \<circ> (crun 0)) decide crun"
    by (rule ate_weak_consensus)
  with init show "weak_consensus ?inits decide crun"
    by (simp add: o_def)
qed

end   \<comment> \<open>context @{text "ate_parameters"}\<close>

end   (* theory AteProof *)
