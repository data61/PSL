section \<open>Security of message authentication\<close>

theory Message_Authentication_Code imports
  System_Construction
begin

definition rnd :: "security \<Rightarrow> bool list set" where
  "rnd \<eta> \<equiv> nlists UNIV \<eta>"

definition mac :: "security \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool list spmf" where
  "mac \<eta> r m \<equiv> return_spmf r"

definition vld :: "security \<Rightarrow> bool list set" where
  "vld \<eta> \<equiv> nlists UNIV \<eta>"

fun valid_mac_query :: "security \<Rightarrow> (bool list \<times> bool list) insec_query \<Rightarrow> bool" where
  "valid_mac_query \<eta> (ForwardOrEdit (Some (a, m))) \<longleftrightarrow> a \<in> vld \<eta> \<and> m \<in> vld \<eta>"
| "valid_mac_query \<eta> _ = True"

fun sim :: "('b list \<times> 'b list) option + unit \<Rightarrow> ('b list \<times> 'b list) insec_query 
  \<Rightarrow> (('b list \<times> 'b list) option \<times> (('b list \<times> 'b list) option + unit), auth_query , 'b list option) gpv" where
  "sim (Inr ())             _                = Done (None, Inr())"
| "sim (Inl None)           (Edit  (a', m')) = do { _ \<leftarrow> Pause Drop Done; Done (None, Inr ())}"
| "sim (Inl (Some (a, m)))  (Edit  (a', m')) = (if a = a' \<and> m = m' 
    then do { _ \<leftarrow> Pause Forward Done; Done (None, Inl (Some (a, m)))}
    else do { _ \<leftarrow> Pause Drop Done; Done (None, Inr ())})"
| "sim (Inl None)           Forward          = do { 
    Pause Forward Done;
    Done (None, Inl None) }"
| "sim (Inl (Some _))       Forward          = do { 
    Pause Forward Done;
    Done (None, Inr ()) }"
| "sim (Inl None)           Drop             = do { 
    Pause Drop Done;
    Done (None, Inl None) }"
| "sim (Inl (Some _))       Drop             = do { 
    Pause Drop Done;
    Done (None, Inr ()) }"
| "sim (Inl (Some (a, m)))  Look             = do {
    lo \<leftarrow> Pause Look Done; 
    (case lo of
      Some m \<Rightarrow> Done (Some (a, m), Inl (Some (a, m)))
    | None   \<Rightarrow> Done (None, Inl (Some (a, m))))}"
| "sim (Inl None)           Look             = do {
    lo \<leftarrow> Pause Look Done;
    (case lo of 
      Some m \<Rightarrow> do {
        a \<leftarrow> lift_spmf (spmf_of_set (nlists UNIV (length m)));
        Done (Some (a, m), Inl (Some (a, m)))}
    | None   \<Rightarrow> Done (None, Inl None))}"


context
  fixes \<eta> :: "security"
begin

private definition rorc_channel_send :: "((bool \<times> unit) \<times> (bool list \<Rightarrow> bool list option) \<times> (bool list \<times> bool list) cstate, bool list, unit) oracle'" where
  "rorc_channel_send s m \<equiv> (if fst (fst s) 
    then return_spmf ((), (True, ()), snd s)
    else do {
      (r, s) \<leftarrow> (rorc.rnd_oracle (rnd \<eta>))\<dagger> (snd s) m;
      a \<leftarrow> mac \<eta> r m;
      (_, s) \<leftarrow> \<dagger>channel.send_oracle s (a, m);
      return_spmf ((), (True, ()), s)
    })"

private definition rorc_channel_recv :: "((bool \<times> unit) \<times> (bool list \<Rightarrow> bool list option) \<times> (bool list \<times> bool list) cstate, unit, bool list option) oracle'" where
  "rorc_channel_recv s q \<equiv> do {
    (m, s) \<leftarrow> \<dagger>\<dagger>channel.recv_oracle s ();
    (case m of 
      None \<Rightarrow> return_spmf (None, s)
    | Some (a, m) \<Rightarrow> do {
        (r, s) \<leftarrow> \<dagger>(rorc.rnd_oracle (rnd \<eta>))\<dagger> s m;
        a' \<leftarrow> mac \<eta> r m;
        return_spmf (if a' = a then Some m else None, s)})
  }"

private definition rorc_channel_recv_f :: "((bool list \<Rightarrow> bool list option) \<times> (bool list \<times> bool list) cstate, unit, bool list option) oracle'" where
  "rorc_channel_recv_f s q \<equiv> do {
    (am, (as, ams)) \<leftarrow>  \<dagger>channel.recv_oracle s ();
    (case am of 
      None \<Rightarrow> return_spmf (None, (as, ams))
    | Some (a, m) \<Rightarrow> (case as m of
        None \<Rightarrow> do {
          a'' :: bool list \<leftarrow> spmf_of_set (nlists UNIV \<eta> - {a});
          a'  \<leftarrow> spmf_of_set (nlists UNIV \<eta>);
          (if a' = a 
            then return_spmf (None, as(m := Some a''), ams)
            else return_spmf (None, as(m := Some a'), ams)) }
      | Some a' \<Rightarrow> return_spmf (if a' = a then Some m else None, as, ams)))}"

private fun lazy_channel_send :: "(bool list cstate \<times> (bool list \<times> bool list) option \<times> (bool list \<Rightarrow> bool list option), bool list, unit) oracle'" where
  "lazy_channel_send (Void, es) m = return_spmf ((), (Store m, es))"
| "lazy_channel_send s          m = return_spmf ((), s)"

private fun lazy_channel_recv :: "(bool list cstate \<times> (bool list \<times> bool list) option \<times> (bool list \<Rightarrow> bool list option), unit, bool list option) oracle'" where
  "lazy_channel_recv (Collect m, None, as)   () = return_spmf (Some m, (Fail, None, as))"
| "lazy_channel_recv (ms, Some (a', m'), as) () = (case as m' of
    None \<Rightarrow> do {
      a \<leftarrow> spmf_of_set (rnd \<eta>);
      return_spmf (if a = a' then Some m' else None, cstate.Fail, None, as (m' := Some a))}
  | Some a \<Rightarrow> return_spmf (if a = a' then Some m' else None, Fail, None, as))"
| "lazy_channel_recv s                                 () = return_spmf (None, s)"

private fun lazy_channel_insec :: "(bool list cstate \<times> (bool list \<times> bool list) option \<times> (bool list \<Rightarrow> bool list option),
   (bool list \<times> bool list) insec_query, (bool list \<times> bool list) option) oracle'" where
  "lazy_channel_insec (Void, _, as)       (Edit (a', m')) = return_spmf (None, (Collect m', Some (a', m'), as))"
| "lazy_channel_insec (Store m, _, as)    (Edit (a', m')) = return_spmf (None, (Collect m', Some (a', m'), as))"
| "lazy_channel_insec (Store m, es)       Forward         = return_spmf (None, (Collect m, es))"
| "lazy_channel_insec (Store m, es)       Drop            = return_spmf (None, (Fail, es))"
| "lazy_channel_insec (Store m, None, as) Look            = (case as m of
    None \<Rightarrow> do {
      a \<leftarrow> spmf_of_set (rnd \<eta>);
      return_spmf (Some (a, m), Store m, None, as (m := Some a))}
  | Some a \<Rightarrow> return_spmf (Some (a, m), Store m, None, as))"
| "lazy_channel_insec s                   _               = return_spmf (None, s)"

private fun lazy_channel_recv_f :: "(bool list  cstate \<times> (bool list \<times> bool list) option \<times> (bool list \<Rightarrow> bool list option), unit, bool list option) oracle'" where
  "lazy_channel_recv_f (Collect m, None, as)   () = return_spmf (Some m, (Fail, None, as))"
| "lazy_channel_recv_f (ms, Some (a', m'), as) () = (case as m' of
    None \<Rightarrow> do {
      a \<leftarrow> spmf_of_set (rnd \<eta>);
      return_spmf (None, Fail, None, as (m' := Some a))}
  | Some a \<Rightarrow> return_spmf (if a = a' then Some m' else None, Fail, None, as))"
| "lazy_channel_recv_f s                       () = return_spmf (None, s)"

private abbreviation callee_auth_channel where
  "callee_auth_channel callee \<equiv> lift_state_oracle extend_state_oracle (attach_callee callee auth_channel.auth_oracle)"

private abbreviation 
  "valid_insecQ \<equiv> {(x :: (bool list \<times> bool list) insec_query). case x of 
    ForwardOrEdit (Some (a, m)) \<Rightarrow> length a = id' \<eta> \<and> length m = id' \<eta> 
  | _ \<Rightarrow> True}"

private inductive S :: "(bool list cstate \<times> (bool list \<times> bool list) option \<times> (bool list \<Rightarrow> bool list option)) spmf
  \<Rightarrow> ((bool \<times> unit) \<times> (bool list \<Rightarrow> bool list option) \<times> (bool list \<times> bool list)  cstate) spmf \<Rightarrow> bool" where
  "S (return_spmf (Void, None, Map.empty)) 
     (return_spmf ((False, ()), Map.empty, Void))"
| "S (return_spmf (Store m, None, Map.empty))
     (map_spmf (\<lambda>a. ((True, ()), [m \<mapsto> a], Store (a, m))) (spmf_of_set (nlists UNIV \<eta>)))"
if "length m = id' \<eta>"
| "S (return_spmf (Collect m, None, Map.empty))
     (map_spmf (\<lambda>a. ((True, ()), [m \<mapsto> a], Collect (a, m))) (spmf_of_set (nlists UNIV \<eta>)))"
if "length m = id' \<eta>"
| "S (return_spmf (Store m, None, [m \<mapsto> a])) 
     (return_spmf ((True, ()), [m \<mapsto> a], Store (a, m)))"
if "length m = id' \<eta>" and "length a = id' \<eta>"
| "S (return_spmf (Collect m, None, [m \<mapsto> a]))
     (return_spmf ((True, ()), [m \<mapsto> a], Collect (a, m)))"
if "length m = id' \<eta>" and "length a = id' \<eta>"
| "S (return_spmf (Fail, None, Map.empty)) 
     (map_spmf (\<lambda>a. ((True, ()), [m \<mapsto> a], Fail)) (spmf_of_set (nlists UNIV \<eta>)))"
if "length m = id' \<eta>"
| "S (return_spmf (Fail, None, [m \<mapsto> a])) 
     (return_spmf ((True, ()), [m \<mapsto> a], Fail))"
if "length m = id' \<eta>" and "length a = id' \<eta>"
| "S (return_spmf (Collect m', Some (a', m'), Map.empty)) 
     (return_spmf ((False, ()), Map.empty, Collect (a', m')))"
if "length m' = id' \<eta>" and "length a' = id' \<eta>"
| "S (return_spmf (Collect m', Some (a', m'), [m \<mapsto> a])) 
     (return_spmf ((True, ()), [m \<mapsto> a], Collect (a', m')))"
if "length m = id' \<eta>" and "length a = id' \<eta>" and "length m' = id' \<eta>" and "length a' = id' \<eta>"
| "S (return_spmf (Collect m', Some (a', m'), Map.empty))
     (map_spmf (\<lambda>x. ((True, ()), [m \<mapsto> x], Collect (a', m'))) (spmf_of_set (nlists UNIV \<eta>)))"
if "length m = id' \<eta>" and "length m' = id' \<eta>" and "length a' = id' \<eta>"
| "S (map_spmf (\<lambda>x. (Fail, None, as(m' \<mapsto> x))) spmf_s)
     (map_spmf (\<lambda>x. ((False, ()), as(m' \<mapsto> x), Fail)) spmf_s)"
if "length m' = id' \<eta>" and "lossless_spmf spmf_s"  
| "S (map_spmf (\<lambda>x. (Fail, None, as(m' \<mapsto> x))) spmf_s)
     (map_spmf (\<lambda>x. ((True, ()), as(m' \<mapsto> x), Fail)) spmf_s)"
if "length m' = id' \<eta>"  and "lossless_spmf spmf_s" 
| "S (return_spmf (Fail, None, [m' \<mapsto> a']))
     (map_spmf (\<lambda>x. ((True, ()), [m \<mapsto> x, m' \<mapsto> a'], Fail)) (spmf_of_set (nlists UNIV \<eta>)))"
if "length m = id' \<eta>" and "length m'= id' \<eta>" and "length a' = id' \<eta>"
| "S (map_spmf (\<lambda>x. (Fail, None, [m' \<mapsto> x])) (spmf_of_set (nlists UNIV \<eta> \<inter> {x. x \<noteq> a'})))
     (map_spmf (\<lambda>x. ((True, ()), [m \<mapsto> fst x, m' \<mapsto> snd x], Fail)) (spmf_of_set (nlists UNIV \<eta> \<times> nlists UNIV \<eta> \<inter> {x. snd x \<noteq> a'})))"
if "length m = id' \<eta>" and "length m'= id' \<eta>"
| "S (map_spmf (\<lambda>x. (Fail, None, as(m' \<mapsto> x))) spmf_s)
     (map_spmf (\<lambda>p. ((True, ()), as(m' \<mapsto> fst p, m \<mapsto> snd p), Fail)) (mk_lossless (pair_spmf spmf_s (spmf_of_set (nlists UNIV \<eta>)))))"
if "length m = id' \<eta>" and "length m'= id' \<eta>" and "lossless_spmf spmf_s"


private lemma trace_eq_lazy:
  assumes "\<eta> > 0"
  shows "(valid_insecQ <+> nlists UNIV (id' \<eta>) <+> UNIV) \<turnstile>\<^sub>R 
    RES (lazy_channel_insec \<oplus>\<^sub>O lazy_channel_send \<oplus>\<^sub>O lazy_channel_recv) (Void, None, Map.empty) 
    \<approx> 
    RES (\<dagger>\<dagger>insec_channel.insec_oracle \<oplus>\<^sub>O rorc_channel_send \<oplus>\<^sub>O rorc_channel_recv) ((False, ()), Map.empty, Void)"
    (is "?A \<turnstile>\<^sub>R RES (?L1 \<oplus>\<^sub>O ?L2 \<oplus>\<^sub>O ?L3) ?SL \<approx> RES (?R1 \<oplus>\<^sub>O ?R2 \<oplus>\<^sub>O ?R3) ?SR")
proof -
  note [simp] = 
    spmf.map_comp o_def map_bind_spmf bind_map_spmf bind_spmf_const exec_gpv_bind
    insec_channel.insec_oracle.simps channel.send_oracle.simps channel.recv_oracle.simps
    rorc_channel_send_def rorc_channel_recv_def rorc.rnd_oracle.simps mac_def rnd_def

  have aux1: "nlists (UNIV::bool set) \<eta> \<times> nlists (UNIV::bool set) \<eta> \<inter> {x. snd x \<noteq> a'} \<noteq> {}" (is ?aux1)
    and aux2: "nlists (UNIV::bool set) \<eta> \<inter> {x. x \<noteq> a'} \<noteq> {}" (is ?aux2) for a'
  proof -
    have "\<exists>a. a \<in> nlists (UNIV::bool set) \<eta> \<and> a \<noteq> a'" for a'
    proof (cases "a' \<in> nlists (UNIV::bool set) \<eta>")
      case True
      show ?thesis 
      proof (rule ccontr)
        have "2 ^ \<eta> = card (nlists (UNIV :: bool set) \<eta>)" by (simp add: card_nlists)
        also assume "\<nexists>a. a \<in> nlists UNIV \<eta> \<and> a \<noteq> a'"
        then have "nlists UNIV \<eta> = {a'}" using True by blast
        then have fct:"card (nlists (UNIV :: bool set) \<eta>) = card {a'}" by simp
        also have " card {a'} = 1" by simp
        finally have "\<eta> = 0" by simp
        then show "False" using assms by blast
      qed
    next
      case False
      obtain a where obt:"a \<in> nlists (UNIV::bool set) \<eta>" using assms by auto
      then have "a \<noteq> a'" using False by blast
      then show ?thesis using obt by auto
    qed
    then obtain a where o1: "a \<in> nlists (UNIV::bool set) \<eta>" and o2: "a \<noteq> a'" by blast

    obtain m where "m \<in> nlists (UNIV::bool set) \<eta>" by blast
    with o1 o2 have "(m, a) \<in> {x. snd x \<noteq> a'}" and "(m, a) \<in> nlists UNIV \<eta> \<times> nlists UNIV \<eta>" by auto
    then show ?aux1 by blast

    from o1 o2 have "a \<in> {x. x \<noteq> a'}" and "a \<in> nlists UNIV \<eta>" by auto
    then show ?aux2 by blast
  qed

  have *: "?A \<turnstile>\<^sub>C ?L1 \<oplus>\<^sub>O ?L2 \<oplus>\<^sub>O ?L3(?SL) \<approx> ?R1 \<oplus>\<^sub>O ?R2 \<oplus>\<^sub>O ?R3(?SR)"
  proof(rule trace'_eqI_sim[where S=S], goal_cases Init_OK Output_OK State_OK)
    case Init_OK
    then show ?case by (simp add: S.simps)
  next
    case (Output_OK p q query)
    show ?case
    proof (cases query)
      case (Inl adv_query)
      with Output_OK show ?thesis
      proof cases
        case (14 m m' a')
        then show ?thesis using Output_OK(2) Inl
          by(cases adv_query)(simp; subst (1 2) weight_spmf_of_set_finite; auto simp add: assms aux1 aux2)+
      qed (auto simp add: weight_mk_lossless lossless_spmf_def split: aquery.splits option.splits)
    next
      case Snd_Rcv: (Inr query')
      show ?thesis
      proof (cases query')
        case (Inl snd_query)
        with Output_OK Snd_Rcv show ?thesis
        proof cases
          case (11 m' _ as)
          with Output_OK(2) Snd_Rcv Inl show ?thesis
            by(cases "snd_query = m'"; cases "as snd_query")(simp_all)
        next
          case (14 m m' a')
          with Output_OK(2) Snd_Rcv Inl show ?thesis
            by(simp; subst (1 2) weight_spmf_of_set_finite; auto simp add: assms aux1 aux2)
        qed (auto simp add: weight_mk_lossless lossless_spmf_def)
      next
        case (Inr rcv_query)
        with Output_OK Snd_Rcv show ?thesis 
        proof cases
          case (10 m m' a')
          with Output_OK(2) Snd_Rcv Inr show ?thesis by(cases "m = m'")(simp_all)
        next
          case (14 m m' a')
          with Output_OK(2) Snd_Rcv Inr show ?thesis
            by(simp; subst (1 2) weight_spmf_of_set_finite; auto simp add: assms aux1 aux2)
        qed (auto simp add: weight_mk_lossless lossless_spmf_def split:option.splits)
      qed
    qed
  next
    case (State_OK p q query state answer state')
    show ?case
    proof (cases query)
      case (Inl adv_query)
      show ?thesis
      proof (cases adv_query)
        case Look
        with State_OK Inl show ?thesis 
        proof cases
          case Store_State_Channel: (2 m)
          have[simp]: " a \<in> nlists UNIV \<eta> \<Longrightarrow> 
          S (cond_spmf_fst (map_spmf (\<lambda>x. (Inl (Some (x, m)), Store m, None, [m \<mapsto> x]))
              (spmf_of_set (nlists UNIV \<eta>))) (Inl (Some (a, m))))
            (cond_spmf_fst (map_spmf (\<lambda>x. (Inl (Some (x, m)), (True, ()), [m \<mapsto> x], Store (x, m)))
              (spmf_of_set (nlists UNIV \<eta>))) (Inl (Some (a, m))))" for a 
          proof(subst (1 2) cond_spmf_fst_map_Pair1, goal_cases)
            case 4
            then show ?case 
              by(subst (1 2 3) inv_into_f_f, simp_all add: inj_on_def)
                (rule S.intros, simp_all add: Store_State_Channel in_nlists_UNIV id'_def)
          qed (simp_all add: id'_def inj_on_def)

          from Store_State_Channel show ?thesis using State_OK Inl Look
            by(clarsimp simp add: map_spmf_conv_bind_spmf[symmetric]) 

        qed (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro: S.intros)
      next
        case (ForwardOrEdit foe)
        with State_OK Inl show ?thesis 
        proof (cases foe)
          case (Some am')
          obtain a' m' where "am' = (a', m')" by (cases am') simp
          with State_OK Inl ForwardOrEdit Some show ?thesis 
            by cases (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro: S.intros elim:S.cases)
        qed (erule S.cases, auto simp add: map_spmf_conv_bind_spmf[symmetric] intro: S.intros)
      next
        case Drop
        with State_OK Inl show ?thesis 
          by cases (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro: S.intros)
      qed
    next
      case Snd_Rcv: (Inr query')
      show ?thesis
      proof (cases query')
        case (Inl snd_query)
        with State_OK Snd_Rcv show ?thesis 
        proof cases
          case 1
          with State_OK Snd_Rcv Inl show ?thesis 
            by(clarsimp simp add: map_spmf_conv_bind_spmf[symmetric]) 
              (rule S.intros, simp add: in_nlists_UNIV)
        next
          case (8 m' a')
          with State_OK Snd_Rcv Inl show ?thesis
            by(clarsimp simp add: map_spmf_conv_bind_spmf[symmetric]) 
              (rule S.intros, simp add: in_nlists_UNIV)
        next
          case (11 m' spmf_s as)
          with State_OK Snd_Rcv Inl show ?thesis
            by(auto simp add: bind_bind_conv_pair_spmf split_def split: if_splits option.splits  intro!: S.intros)
              ((auto simp add: map_spmf_conv_bind_spmf[symmetric] intro!: S.intros), simp only: id'_def in_nlists_UNIV)
        qed (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro: S.intros)
      next
        case (Inr rcv_query)
        with State_OK Snd_Rcv show ?thesis 
        proof(cases)
          case (8 m' a')
          then show ?thesis using State_OK(2-) Snd_Rcv Inr
            by (auto simp add: map_spmf_conv_bind_spmf[symmetric] image_def 
                cond_spmf_fst_def vimage_def aux1 aux2 assms intro:S.intros)
        next
          case (9 m a m' a')
          then show ?thesis using State_OK(2-) Snd_Rcv Inr
            by (cases "m = m'") (auto simp add: map_spmf_conv_bind_spmf[symmetric] cond_spmf_fst_def 
                vimage_def aux1 aux2 assms intro:S.intros split!: if_splits)
        next
          case (10 m m' a')
          show ?thesis
          proof (cases "m = m'")
            case True
            with 10 show ?thesis using State_OK(2-) Snd_Rcv Inr
              by (auto simp add: map_spmf_conv_bind_spmf[symmetric] cond_spmf_fst_def 
                  vimage_def aux1 aux2 assms split!: if_split intro:S.intros)
          next
            case False
            have[simp]: "a' \<in> nlists UNIV \<eta> \<Longrightarrow> nlists (UNIV :: bool set) \<eta> \<times> nlists UNIV \<eta> \<inter> {x. snd x = a'} = nlists UNIV \<eta> \<times> {a'}"
              by auto

            from 10 False show ?thesis using State_OK(2-) Snd_Rcv Inr
              by(simp add: bind_bind_conv_pair_spmf)
                ((auto simp add: bind_bind_conv_pair_spmf split_def image_def map_spmf_conv_bind_spmf[symmetric]
                    cond_spmf_fst_def vimage_def cond_spmf_spmf_of_set pair_spmf_of_set )
                  , (auto simp add: pair_spmf_of_set[symmetric] spmf_of_set_singleton pair_spmf_return_spmf2 
                    map_spmf_of_set_inj_on[symmetric] simp del: map_spmf_of_set_inj_on intro: S.intros))
          qed
        qed (auto simp add: map_spmf_conv_bind_spmf[symmetric] intro: S.intros)
      qed
    qed 
  qed

  from * show ?thesis by simp
qed


private lemma game_difference:
  defines "\<I> \<equiv> \<I>_uniform (Set.Collect (valid_mac_query \<eta>)) (insert None (Some ` (nlists UNIV \<eta> \<times> nlists UNIV \<eta>))) \<oplus>\<^sub>\<I>
     (\<I>_uniform (vld \<eta>) UNIV \<oplus>\<^sub>\<I> \<I>_uniform UNIV (insert None (Some ` vld \<eta>)))"
  assumes bound: "interaction_bounded_by' (\<lambda>_. True) \<A> q"
    and lossless: "plossless_gpv \<I> \<A>"
    and WT: "\<I> \<turnstile>g \<A> \<surd>"
  shows
    "\<bar>spmf (connect \<A> (RES (lazy_channel_insec \<oplus>\<^sub>O lazy_channel_send \<oplus>\<^sub>O lazy_channel_recv_f) (Void, None, Map.empty))) True - 
    spmf (connect \<A> (RES (lazy_channel_insec \<oplus>\<^sub>O lazy_channel_send \<oplus>\<^sub>O lazy_channel_recv) (Void, None, Map.empty))) True\<bar> 
    \<le> q / real (2 ^ \<eta>)" (is "?LHS \<le> _")
proof -

  define lazy_channel_insec' where
    "lazy_channel_insec' = (\<dagger>lazy_channel_insec :: (bool \<times> bool list cstate \<times> (bool list \<times> bool list) option \<times> (bool list \<Rightarrow> bool list option),
   (bool list \<times> bool list) insec_query, (bool list \<times> bool list) option) oracle')"

  define lazy_channel_send' where
    "lazy_channel_send' = (\<dagger>lazy_channel_send :: (bool \<times> bool list cstate \<times> (bool list \<times> bool list) option \<times> (bool list \<Rightarrow> bool list option),
    bool list, unit) oracle')"

  define lazy_channel_recv' where 
    "lazy_channel_recv' = (\<lambda> (s :: bool \<times> bool list cstate \<times> (bool list \<times> bool list) option \<times> (bool list \<Rightarrow> bool list option)) (q :: unit). 
    (case s of
      (flg, Collect m, None, as) \<Rightarrow> return_spmf (Some m, (flg, Fail, None, as))
    | (flg, ms, Some (a', m'), as) \<Rightarrow> (case as m' of
        None \<Rightarrow> do {
          a \<leftarrow> spmf_of_set (rnd \<eta>);
          return_spmf (if a = a' then Some m' else None, flg \<or> a = a', Fail, None, as (m' := Some a))}
      | Some a \<Rightarrow> return_spmf (if a = a' then Some m' else None, flg, Fail, None, as))
    | _ \<Rightarrow> return_spmf (None, s)))"

  define lazy_channel_recv_f' where 
    "lazy_channel_recv_f' = (\<lambda> (s :: bool \<times> bool list cstate \<times> (bool list \<times> bool list) option \<times> (bool list \<Rightarrow> bool list option)) (q :: unit). 
    (case s of
      (flg, Collect m, None, as) \<Rightarrow> return_spmf (Some m, (flg, Fail, None, as))
    | (flg, ms, Some (a', m'), as) \<Rightarrow> (case as m' of
        None \<Rightarrow> do {
          a \<leftarrow> spmf_of_set (rnd \<eta>);
          return_spmf (None, flg \<or> a = a', Fail, None, as (m' := Some a))}
      | Some a \<Rightarrow> return_spmf (if a = a' then Some m' else None, flg, Fail, None, as))
    | _ \<Rightarrow> return_spmf (None, s)))"

  define game where 
    "game = (\<lambda>(\<A> :: ((bool list \<times> bool list) insec_query + bool list + unit, (bool list \<times> bool list) option + unit + bool list option) distinguisher) recv_oracle. do {
    (b :: bool, (flg, ams, es, as))\<leftarrow> (exec_gpv (lazy_channel_insec' \<oplus>\<^sub>O lazy_channel_send' \<oplus>\<^sub>O recv_oracle) \<A> (False, Void, None, Map.empty));
    return_spmf (b, flg) })"

  have fact1: "spmf (connect \<A> (RES (lazy_channel_insec \<oplus>\<^sub>O lazy_channel_send \<oplus>\<^sub>O lazy_channel_recv_f) (Void, None, Map.empty))) True  
    = spmf (connect \<A> (RES (lazy_channel_insec' \<oplus>\<^sub>O lazy_channel_send' \<oplus>\<^sub>O lazy_channel_recv_f') (False, Void, None, Map.empty))) True"
  proof -
    let ?orc_lft = "lazy_channel_insec \<oplus>\<^sub>O lazy_channel_send \<oplus>\<^sub>O lazy_channel_recv_f"
    let ?orc_rgt = "lazy_channel_insec' \<oplus>\<^sub>O lazy_channel_send' \<oplus>\<^sub>O lazy_channel_recv_f'"

    have[simp]: "rel_spmf (rel_prod (=) (\<lambda>x y. x = snd y)) 
      (lazy_channel_insec s q) (lazy_channel_insec' (flg, s) q) " for s flg q
      by (cases s) (simp add: lazy_channel_insec'_def spmf_rel_map rel_prod_sel split_def option.rel_refl pmf.rel_refl split:option.split)

    have[simp]: "rel_spmf (rel_prod (=) (\<lambda>x y. x = snd y)) 
      (lazy_channel_send s q) (lazy_channel_send' (flg, s) q)" for s flg q
    proof -
      obtain ams es as where "s = (ams, es, as)" by (cases s)
      then show ?thesis by (cases ams) (auto simp add: spmf_rel_map map_spmf_conv_bind_spmf split_def lazy_channel_send'_def)
    qed 

    have[simp]: "rel_spmf (rel_prod (=) (\<lambda>x y. x = snd y))  
      (lazy_channel_recv_f s q) (lazy_channel_recv_f' (flg, s) q)" for s flg q
    proof -
      obtain ams es as where *: "s = (ams, es, as)" by (cases s)
      show ?thesis 
      proof (cases es)
        case None
        with * show ?thesis by (cases ams) (simp_all add:lazy_channel_recv_f'_def)
      next
        case (Some am)
        obtain a m where "am = (a, m)" by (cases am)
        with * show ?thesis by (cases ams) (simp_all add: lazy_channel_recv_f'_def rel_spmf_bind_reflI split:option.split)
      qed
    qed

    have[simp]: "rel_spmf (rel_prod (=) (\<lambda>x y. x = snd y))
     ((lazy_channel_insec \<oplus>\<^sub>O lazy_channel_send \<oplus>\<^sub>O lazy_channel_recv_f) (ams, es, as) query)
     ((lazy_channel_insec' \<oplus>\<^sub>O lazy_channel_send' \<oplus>\<^sub>O lazy_channel_recv_f') (flg, ams, es, as) query)" for flg ams es as query
    proof (cases query)
      case (Inl adv_query)
      then show ?thesis 
        by(clarsimp simp add: spmf_rel_map map_spmf_conv_bind_spmf[symmetric] apfst_def map_prod_def split_beta)
          ((rule rel_spmf_mono[where A="rel_prod (=) (\<lambda>x y. x = snd y)"]), auto)
    next
      case (Inr query')
      note Snd_Rcv = this
      then show ?thesis
        by (cases query', auto simp add: spmf_rel_map map_spmf_conv_bind_spmf[symmetric] split_beta)
          ((rule rel_spmf_mono[where A="rel_prod (=) (\<lambda>x y. x = snd y)"]); auto)+
    qed

    have[simp]: "rel_spmf (\<lambda>x y. fst x = fst y)
     (exec_gpv ?orc_lft \<A> (Void, None, Map.empty)) (exec_gpv ?orc_rgt \<A> (False, Void, None, Map.empty))" 
      by(rule rel_spmf_mono[where A="rel_prod (=) (\<lambda>x y. x = snd y)"])
        (auto simp add: gpv.rel_eq split_def intro!: rel_funI 
          exec_gpv_parametric[where CALL="(=)", THEN rel_funD, THEN rel_funD, THEN rel_funD])

    show ?thesis 
      unfolding map_spmf_conv_bind_spmf exec_gpv_resource_of_oracle connect_def spmf_conv_measure_spmf
      by(rule measure_spmf_parametric[where A="(=)", THEN rel_funD, THEN rel_funD])
        (auto simp add: rel_pred_def spmf_rel_map map_spmf_conv_bind_spmf[symmetric] gpv.rel_eq split_def intro!: rel_funI)
  qed

  have fact2: "\<bar>spmf (connect \<A> (RES (lazy_channel_insec' \<oplus>\<^sub>O lazy_channel_send' \<oplus>\<^sub>O lazy_channel_recv_f') (False, Void, None, Map.empty))) True - 
    spmf (connect \<A> (RES (lazy_channel_insec' \<oplus>\<^sub>O lazy_channel_send' \<oplus>\<^sub>O lazy_channel_recv') (False, Void, None, Map.empty))) True\<bar> 
    \<le> Sigma_Algebra.measure (measure_spmf (game \<A> lazy_channel_recv_f')) {x. snd x}" (is "\<bar>spmf ?L _ - spmf ?R _ \<bar> \<le> _ ")
  proof -
    let ?orc_lft = "lazy_channel_insec' \<oplus>\<^sub>O lazy_channel_send' \<oplus>\<^sub>O lazy_channel_recv_f'" 
    let ?orc_rgt = "lazy_channel_insec' \<oplus>\<^sub>O lazy_channel_send' \<oplus>\<^sub>O lazy_channel_recv'"

    have[simp]: "callee_invariant_on lazy_channel_insec' fst (\<I>_uniform (Set.Collect (valid_mac_query \<eta>)) UNIV)"
    proof (unfold_locales, goal_cases)
      case (1 state query answer state')
      then show ?case
        by(cases state; cases "fst (snd state)")(auto simp add: spmf_rel_map map_spmf_conv_bind_spmf split_def lazy_channel_insec'_def)
    qed (auto intro: WT_calleeI)

    have[simp]: "callee_invariant_on lazy_channel_send' fst (\<I>_uniform (vld \<eta>) UNIV)"
    proof (unfold_locales, goal_cases)
      case (1 state query answer state')
      then show ?case
        by(cases state; cases "fst (snd state)")(auto simp add: spmf_rel_map map_spmf_conv_bind_spmf split_def lazy_channel_send'_def)
    qed (auto intro: WT_calleeI)

    have[simp]: "callee_invariant lazy_channel_recv' fst"
    proof (unfold_locales, goal_cases)
      case (1 state query answer state')
      then show ?case
        by(cases state; cases "fst (snd state)")(auto simp add: lazy_channel_recv'_def split:option.splits)
    qed (auto split:option.splits)

    have[simp]: "callee_invariant lazy_channel_recv_f' fst"
    proof (unfold_locales, goal_cases)
      case (1 state query answer state')
      then show ?case
        by(cases state; cases "fst (snd state)")(auto simp add: lazy_channel_recv_f'_def split:option.splits)
    qed (auto split:option.splits)

    have[simp]: "lossless_spmf (lazy_channel_insec s q)" for s q
      by(cases "(s, q)" rule: lazy_channel_insec.cases)(auto simp add: rnd_def split!: option.split)

    have[simp]: "lossless_spmf (lazy_channel_send' s q)" for s q
      by(cases s; cases "fst (snd s)")(simp_all add: lazy_channel_send'_def)

    have[simp]: "lossless_spmf (lazy_channel_recv' s ())" for s
      by(auto simp add: lazy_channel_recv'_def rnd_def split: prod.split cstate.split option.split)

    have[simp]: "lossless_spmf (lazy_channel_recv_f' s ())" for s
      by(auto simp add: lazy_channel_recv_f'_def rnd_def split: prod.split cstate.split option.split)

    have[simp]: "rel_spmf (\<lambda>(a, s1') (b, s2'). (fst s2' \<longrightarrow> fst s1') \<and> (\<not> fst s2' \<longrightarrow> \<not> fst s1' \<and> a = b \<and> s1' = s2'))
     (?orc_lft (flg, ams, es, as) query) (?orc_rgt (flg, ams, es, as) query)" for flg ams es as query
    proof (cases query)
      case (Inl adv_query)
      then show ?thesis by (auto simp add: spmf_rel_map map_spmf_conv_bind_spmf intro: rel_spmf_bind_reflI)
    next
      case (Inr query')
      note Snd_Rcv = this  
      show ?thesis
      proof (cases query')
        case (Inl snd_query)
        with Snd_Rcv show ?thesis
          by (auto simp add: spmf_rel_map map_spmf_conv_bind_spmf intro: rel_spmf_bind_reflI)
      next
        case (Inr rcv_query)
        with Snd_Rcv show ?thesis 
        proof (cases es)
          case (Some am')
          obtain a' m' where "am' = (a', m')" by (cases am')
          with Snd_Rcv Some Inr show ?thesis 
            by (cases ams) (auto simp add: spmf_rel_map map_spmf_conv_bind_spmf 
                lazy_channel_recv'_def lazy_channel_recv_f'_def rel_spmf_bind_reflI split:option.splits)
        qed (cases ams; auto simp add: lazy_channel_recv'_def lazy_channel_recv_f'_def split:option.splits)
      qed
    qed
    let ?\<I> = "\<I>_uniform (Set.Collect (valid_mac_query \<eta>)) UNIV \<oplus>\<^sub>\<I> (\<I>_uniform (vld \<eta>) UNIV \<oplus>\<^sub>\<I> \<I>_full)"
    let ?\<A> = "mk_lossless_gpv (responses_\<I> \<I>) True \<A>"

    have "plossless_gpv ?\<I> ?\<A>" using lossless WT
      by(rule plossless_gpv_mk_lossless_gpv)(simp add: \<I>_def)
    moreover have "?\<I> \<turnstile>g ?\<A> \<surd>" using WT by(rule WT_gpv_mk_lossless_gpv)(simp add: \<I>_def)
    ultimately have "rel_spmf (\<lambda>x y. fst (snd x) = fst (snd y) \<and> (\<not> fst (snd y) \<longrightarrow> (fst x \<longleftrightarrow> fst y)))
      (exec_gpv ?orc_lft ?\<A> (False, Void, None, Map.empty)) (exec_gpv ?orc_rgt ?\<A> (False, Void, None, Map.empty))"
      by(auto simp add: \<I>_def intro!: exec_gpv_oracle_bisim_bad_plossless[where X="(=)" and
            X_bad="\<lambda> _ _. True" and ?bad1.0="fst" and ?bad2.0="fst" and \<I> = "?\<I>", THEN rel_spmf_mono])
        (auto simp add: lazy_channel_insec'_def intro: WT_calleeI)
    also let ?I = "(\<lambda>(_, s1, s2, s3). pred_cstate (\<lambda>x. length x = \<eta>) s1 \<and> pred_option (\<lambda>(x, y). length x = \<eta> \<and> length y = \<eta>) s2 \<and> ran s3 \<subseteq> nlists UNIV \<eta>)"
    have "callee_invariant_on (lazy_channel_insec' \<oplus>\<^sub>O lazy_channel_send' \<oplus>\<^sub>O lazy_channel_recv_f') ?I \<I>"
      apply(unfold_locales)
      subgoal for s x y s'
        apply(clarsimp simp add: \<I>_def; elim PlusE; clarsimp simp add: lazy_channel_insec'_def lazy_channel_send'_def lazy_channel_recv_f'_def)
        subgoal for _ _ _ _ x'
          by(cases "(snd s, x')" rule: lazy_channel_insec.cases)
            (auto simp add: vld_def in_nlists_UNIV rnd_def split: option.split_asm)
        subgoal by(cases "(snd s, projl (projr x))" rule: lazy_channel_send.cases)(auto simp add: vld_def in_nlists_UNIV)
        subgoal by(cases "(snd s, ())" rule: lazy_channel_recv_f.cases)(auto 4 3 split: option.split_asm if_split_asm cstate.split_asm simp add: in_nlists_UNIV vld_def ran_def rnd_def option.pred_set )
        done
      subgoal for s
        apply(clarsimp simp add: \<I>_def; intro conjI WT_calleeI; clarsimp simp add: lazy_channel_insec'_def lazy_channel_send'_def lazy_channel_recv_f'_def)
        subgoal for _ _ _ _ x
          by(cases "(snd s, x)" rule: lazy_channel_insec.cases)
            (auto simp add: vld_def in_nlists_UNIV rnd_def ran_def split: option.split_asm)
        subgoal by(cases "(snd s, ())" rule: lazy_channel_recv_f.cases)(auto 4 3 split: option.split_asm if_split_asm cstate.split_asm simp add: in_nlists_UNIV vld_def ran_def rnd_def)
        done
      done
    then have "exec_gpv ?orc_lft ?\<A> (False, Void, None, Map.empty) = exec_gpv ?orc_lft \<A> (False, Void, None, Map.empty)"
      using WT by(rule callee_invariant_on.exec_gpv_mk_lossless_gpv) simp
    also have "callee_invariant_on (lazy_channel_insec' \<oplus>\<^sub>O lazy_channel_send' \<oplus>\<^sub>O lazy_channel_recv') ?I \<I>"
      apply(unfold_locales)
      subgoal for s x y s'
        apply(clarsimp simp add: \<I>_def; elim PlusE; clarsimp simp add: lazy_channel_insec'_def lazy_channel_send'_def lazy_channel_recv'_def)
        subgoal for _ _ _ _ x'
          by(cases "(snd s, x')" rule: lazy_channel_insec.cases)
            (auto simp add: vld_def in_nlists_UNIV rnd_def split: option.split_asm)
        subgoal by(cases "(snd s, projl (projr x))" rule: lazy_channel_send.cases)(auto simp add: vld_def in_nlists_UNIV)
        subgoal by(cases "(snd s, ())" rule: lazy_channel_recv.cases)(auto 4 3 split: option.split_asm if_split_asm cstate.split_asm simp add: in_nlists_UNIV vld_def ran_def rnd_def option.pred_set )
        done
      subgoal for s
        apply(clarsimp simp add: \<I>_def; intro conjI WT_calleeI; clarsimp simp add: lazy_channel_insec'_def lazy_channel_send'_def lazy_channel_recv'_def)
        subgoal for _ _ _ _ x
          by(cases "(snd s, x)" rule: lazy_channel_insec.cases)
            (auto simp add: vld_def in_nlists_UNIV rnd_def ran_def split: option.split_asm)
        subgoal by(cases "(snd s, ())" rule: lazy_channel_recv.cases)(auto 4 3 split: option.split_asm if_split_asm cstate.split_asm simp add: in_nlists_UNIV vld_def ran_def rnd_def)
        done
      done
    then have "exec_gpv ?orc_rgt ?\<A> (False, Void, None, Map.empty) = exec_gpv ?orc_rgt \<A> (False, Void, None, Map.empty)"
      using WT by(rule callee_invariant_on.exec_gpv_mk_lossless_gpv) simp
    finally have "\<bar>Sigma_Algebra.measure (measure_spmf (game \<A> lazy_channel_recv_f')) {x. fst x} 
          - Sigma_Algebra.measure (measure_spmf (game \<A> lazy_channel_recv')) {x. fst x}\<bar>
        \<le> Sigma_Algebra.measure (measure_spmf (game \<A> lazy_channel_recv_f')) {x. snd x}"
      unfolding game_def
      by - (rule fundamental_lemma[where ?bad2.0="snd"]; auto simp add: spmf_rel_map map_spmf_conv_bind_spmf[symmetric] split_def)

    moreover have "Sigma_Algebra.measure (measure_spmf (game \<A> lazy_channel_recv_f')) {x. fst x} = spmf ?L True"
      unfolding game_def
      by(auto simp add: map_spmf_conv_bind_spmf exec_gpv_resource_of_oracle connect_def spmf_conv_measure_spmf)
        (auto simp add: rel_pred_def intro!: rel_spmf_bind_reflI measure_spmf_parametric[where A="\<lambda>l r. fst l \<longleftrightarrow> r", THEN rel_funD, THEN rel_funD])

    moreover have "spmf ?R True = Sigma_Algebra.measure (measure_spmf (game \<A> lazy_channel_recv')) {x. fst x}"
      unfolding game_def
      by(auto simp add: map_spmf_conv_bind_spmf exec_gpv_resource_of_oracle connect_def spmf_conv_measure_spmf)
        (auto simp add: rel_pred_def intro!: rel_spmf_bind_reflI measure_spmf_parametric[where A="\<lambda>l r. l \<longleftrightarrow> fst r", THEN rel_funD, THEN rel_funD])

    ultimately show ?thesis by simp
  qed

  have fact3: "spmf (connect \<A> (RES (lazy_channel_insec' \<oplus>\<^sub>O lazy_channel_send' \<oplus>\<^sub>O lazy_channel_recv') (False, Void, None, Map.empty))) True  
    = spmf (connect \<A> (RES (lazy_channel_insec \<oplus>\<^sub>O lazy_channel_send \<oplus>\<^sub>O lazy_channel_recv) (Void, None, Map.empty))) True"
  proof -
    let ?orc_lft = "lazy_channel_insec' \<oplus>\<^sub>O lazy_channel_send' \<oplus>\<^sub>O lazy_channel_recv'"
    let ?orc_rgt = "lazy_channel_insec \<oplus>\<^sub>O lazy_channel_send \<oplus>\<^sub>O lazy_channel_recv"

    have[simp]: "rel_spmf (rel_prod (=) (\<lambda>x y. y = snd x)) 
      (lazy_channel_insec' (flg, s) q) (lazy_channel_insec s q)" for s flg q
      by (cases s) (simp add: lazy_channel_insec'_def spmf_rel_map rel_prod_sel split_def option.rel_refl pmf.rel_refl split:option.split)

    have[simp]: "rel_spmf (rel_prod (=) (\<lambda>x y. y = snd x)) 
      (lazy_channel_send' (flg, s) q) (lazy_channel_send s q)" for s flg q
      by(cases "(s, q)" rule: lazy_channel_send.cases)(auto simp add: spmf_rel_map map_spmf_conv_bind_spmf split_def lazy_channel_send'_def)

    have[simp]: "rel_spmf (rel_prod (=) (\<lambda>x y. y = snd x))  
       (lazy_channel_recv' (flg, s) q) (lazy_channel_recv s q)" for s flg q
      by(cases "(s, q)" rule: lazy_channel_recv.cases)(auto simp add: lazy_channel_recv'_def rel_spmf_bind_reflI split:option.split cstate.split)

    have[simp]: "rel_spmf (rel_prod (=) (\<lambda>x y. y = snd x))
     ((lazy_channel_insec' \<oplus>\<^sub>O lazy_channel_send' \<oplus>\<^sub>O lazy_channel_recv') (flg, ams, es, as) query)
     ((lazy_channel_insec \<oplus>\<^sub>O lazy_channel_send \<oplus>\<^sub>O lazy_channel_recv) (ams, es, as)  query)" for flg ams es as query
    proof (cases query)
      case (Inl adv_query)
      then show ?thesis 
        by(auto simp add: spmf_rel_map map_spmf_conv_bind_spmf[symmetric] apfst_def map_prod_def split_beta intro: rel_spmf_mono[where A="rel_prod (=) (\<lambda>x y. y = snd x)"])
    next
      case (Inr query')
      note Snd_Rcv = this
      then show ?thesis
        by (cases query', auto simp add: spmf_rel_map map_spmf_conv_bind_spmf[symmetric] split_beta)
          ((rule rel_spmf_mono[where A="rel_prod (=) (\<lambda>x y. y = snd x)"]); auto)+
    qed

    have[simp]: "rel_spmf (\<lambda>x y. fst x = fst y)
     (exec_gpv ?orc_lft \<A> (False, Void, None, Map.empty)) (exec_gpv ?orc_rgt \<A> (Void, None, Map.empty))" 
      by(rule rel_spmf_mono[where A="rel_prod (=) (\<lambda>x y. y = snd x)"])
        (auto simp add: gpv.rel_eq split_def intro!: rel_funI 
          exec_gpv_parametric[where CALL="(=)", THEN rel_funD, THEN rel_funD, THEN rel_funD])

    show ?thesis 
      unfolding map_spmf_conv_bind_spmf exec_gpv_resource_of_oracle connect_def spmf_conv_measure_spmf
      by(rule measure_spmf_parametric[where A="(=)", THEN rel_funD, THEN rel_funD])
        (auto simp add: rel_pred_def spmf_rel_map map_spmf_conv_bind_spmf[symmetric] gpv.rel_eq split_def intro!: rel_funI)
  qed

  have fact4: "Sigma_Algebra.measure (measure_spmf (game \<A> lazy_channel_recv_f')) {x. snd x} \<le> q / real (2 ^ \<eta>)"
  proof -
    let ?orc_sum = "lazy_channel_insec' \<oplus>\<^sub>O lazy_channel_send' \<oplus>\<^sub>O lazy_channel_recv_f'"

    have "Sigma_Algebra.measure (measure_spmf (game \<A> lazy_channel_recv_f')) {x. snd x} 
          = spmf (map_spmf (fst \<circ> snd) (exec_gpv ?orc_sum \<A> (False, Void, None, Map.empty))) True"
      unfolding game_def
      by (simp add: split_def map_spmf_conv_bind_spmf[symmetric] measure_map_spmf)
        (simp add: spmf_conv_measure_spmf measure_map_spmf vimage_def)
    also have "\<dots> \<le>  (1 / real (card (nlists (UNIV :: bool set) \<eta>))) * real q"
    proof -
      have *: "spmf (map_spmf (fst \<circ> snd) (?orc_sum (False, ams, es, as) query)) True 
                      \<le> 1 / real (card (nlists (UNIV :: bool set) \<eta>))" for ams es as query
      proof (cases query)
        case (Inl adv_query)
        then show ?thesis 
          by(cases "((ams, es, as), adv_query)" rule: lazy_channel_insec.cases)
            (auto simp add: lazy_channel_insec'_def rnd_def map_spmf_conv_bind_spmf bind_spmf_const split: option.split)
      next
        case (Inr query')
        note Snd_Rcv = this
        then show ?thesis
        proof (cases query')
          case (Inr rcv_query)
          with Snd_Rcv show ?thesis
            by (cases ams, auto simp add: lazy_channel_recv_f'_def map_spmf_conv_bind_spmf split_def split:option.split)
              (auto simp add: spmf_of_set map_spmf_conv_bind_spmf[symmetric] rnd_def spmf_map vimage_def spmf_conv_measure_spmf[symmetric] split: split_indicator)
        qed (cases ams, simp_all add: lazy_channel_send'_def)
      qed

      show ?thesis by (rule oi_True.interaction_bounded_by_exec_gpv_bad[where bad="fst"]) (auto simp add: * assms)
    qed

    also have "...  = 1 / real (2 ^ \<eta>) * real q" by (simp add: card_nlists)
    finally show ?thesis by simp
  qed

  have "?LHS \<le> Sigma_Algebra.measure (measure_spmf (game \<A> lazy_channel_recv_f')) {x. snd x}"
    using fact1 fact2 fact3 by arith
  also note fact4
  finally  show ?thesis .
qed


private inductive S' :: "(((bool list \<times> bool list) option + unit) \<times> unit \<times> bool list cstate) spmf \<Rightarrow>
  (bool list cstate \<times> (bool list \<times> bool list) option \<times> (bool list \<Rightarrow> bool list option)) spmf \<Rightarrow> bool" where
  "S' (return_spmf (Inl None, (), Void)) 
      (return_spmf (Void, None, Map.empty))"
| "S' (return_spmf (Inl None, (), Store m)) 
      (return_spmf (Store m, None, Map.empty))"
if "length m = id' \<eta>"
| "S' (return_spmf (Inr (), (), Collect m)) 
      (return_spmf (Collect m, None, Map.empty))"
if "length m = id' \<eta>"
| "S' (return_spmf (Inl (Some (a, m)), (), Store m))
      (return_spmf (Store m, None, [m \<mapsto> a]))"
if "length m = id' \<eta>"
| "S' (return_spmf (Inr (), (), Collect m)) 
      (return_spmf (Collect m, None, [m \<mapsto> a]))"
if "length m = id' \<eta>"
| "S' (return_spmf (Inr (), (), Fail)) 
      (return_spmf (Fail, None, Map.empty))"
| "S' (return_spmf (Inr (), (), Fail)) 
      (return_spmf (Fail, None, [m \<mapsto> x]))"
if "length m = id' \<eta>"
| "S' (return_spmf (Inr (), (), Void))
      (return_spmf (Collect m', Some (a', m'), Map.empty))"
if "length m' = id' \<eta>" and "length a' = id' \<eta>"
| "S' (return_spmf (Inr (), (), Fail))
      (return_spmf (Collect m', Some (a', m'), Map.empty))"
if "length m' = id' \<eta>" and "length a' = id' \<eta>"
| "S' (return_spmf (Inr (), (), Store m))
      (return_spmf (Collect m', Some (a', m'), Map.empty))"
if "length m = id' \<eta>" and "length m' = id' \<eta>" and "length a' = id' \<eta>"
| "S' (return_spmf (Inl (Some (a', m')), (), Collect m')) 
      (return_spmf (Collect m', Some (a', m'), [m' \<mapsto> a']))"
if "length m' = id' \<eta>" and "length a' = id' \<eta>"

| "S' (return_spmf (Inl None, (), cstate.Collect m))
      (return_spmf (cstate.Collect m, None, Map.empty))"
if "length m = id' \<eta>"
| "S' (return_spmf (Inl None, (), cstate.Fail))
      (return_spmf (cstate.Fail, None, Map.empty))"

| "S' (return_spmf (Inr (), (), Fail))
      (return_spmf (Collect m', Some (a', m'), [m \<mapsto> a]))"
if "length m = id' \<eta>" and "length m' = id' \<eta>" and "length a' = id' \<eta>" and "m \<noteq> m'"
| "S' (return_spmf (Inr (), (), Fail)) 
      (return_spmf (Collect m', Some (a', m'), [m \<mapsto> a]))"
if "length m = id' \<eta>" and "length m' = id' \<eta>" and "length a' = id' \<eta>"  and "a \<noteq> a'"
| "S' (return_spmf (Inl None, (), Collect m'))
      (return_spmf (Collect m', Some (a', m'), [m' \<mapsto> a']))"
if "length m' = id' \<eta>" and "length a' = id' \<eta>"
| "S' (return_spmf (Inr (), (), Collect m')) 
      (return_spmf (Collect m', Some (a', m'), [m' \<mapsto> a']))"
if "length m' = id' \<eta>" and "length a' = id' \<eta>"
| "S' (return_spmf (Inr (), (), Void))
      (map_spmf (\<lambda>a'. (Fail, None, [m' \<mapsto> a']))  (spmf_of_set (nlists UNIV \<eta>)))"
if "length m' = id' \<eta>"
| "S' (return_spmf (Inr (), (), Fail))
      (map_spmf (\<lambda>a'. (Fail, None, [m' \<mapsto> a'])) (spmf_of_set (nlists UNIV \<eta>)))"
if "length m' = id' \<eta>"
| "S' (return_spmf (Inr (), (), Store m))
      (map_spmf (\<lambda>a'. (Fail, None, [m' \<mapsto> a'])) (spmf_of_set (nlists UNIV \<eta>)))"
if "length m = id' \<eta>" and "length m' = id' \<eta>"
| "S' (return_spmf (Inr (), (), Fail)) 
      (map_spmf (\<lambda>a'. (Fail, None, [m \<mapsto> a, m' \<mapsto> a'])) (spmf_of_set (nlists UNIV \<eta>)))"
if "length m = id' \<eta>" and "length m' = id' \<eta>" and "m \<noteq> m'"
| "S' (return_spmf (Inl (Some (a', m')), (), Fail)) 
      (return_spmf (Fail, None, [m' \<mapsto> a']))"
if "length m' = id' \<eta>" and "length a' = id' \<eta>"
| "S' (return_spmf (Inl None, (), Fail)) 
      (return_spmf (Fail, None, [m' \<mapsto> a']))"
if "length m' = id' \<eta>" and "length a' = id' \<eta>"


private lemma trace_eq_sim: 
  shows "(valid_insecQ <+> nlists UNIV (id' \<eta>) <+> UNIV) \<turnstile>\<^sub>R 
    RES (callee_auth_channel sim \<oplus>\<^sub>O  \<dagger>\<dagger>channel.send_oracle \<oplus>\<^sub>O \<dagger>\<dagger>channel.recv_oracle) (Inl None, (), Void) 
    \<approx> 
    RES (lazy_channel_insec \<oplus>\<^sub>O lazy_channel_send \<oplus>\<^sub>O lazy_channel_recv_f) (Void, None, Map.empty)"
    (is "?A \<turnstile>\<^sub>R RES (?L1 \<oplus>\<^sub>O ?L2 \<oplus>\<^sub>O ?L3) ?SL \<approx> RES (?R1 \<oplus>\<^sub>O ?R2 \<oplus>\<^sub>O ?R3) ?SR")
proof -
  note [simp] =
    spmf.map_comp o_def map_bind_spmf bind_map_spmf bind_spmf_const exec_gpv_bind
    auth_channel.auth_oracle.simps channel.send_oracle.simps channel.recv_oracle.simps
    rorc_channel_send_def rorc_channel_recv_def rnd_def

  have *: "?A \<turnstile>\<^sub>C ?L1 \<oplus>\<^sub>O ?L2 \<oplus>\<^sub>O ?L3(?SL) \<approx> ?R1 \<oplus>\<^sub>O ?R2 \<oplus>\<^sub>O ?R3(?SR)"
  proof(rule trace'_eqI_sim[where S=S'], goal_cases Init_OK Output_OK State_OK)
    case Init_OK
    then show ?case by (rule S'.intros)
  next
    case (Output_OK p q query)
    show ?case
    proof (cases query)
      case (Inl adv_query)
      with Output_OK show ?thesis
      proof (cases adv_query)
        case (ForwardOrEdit foe)
        with Output_OK Inl show ?thesis 
        proof (cases foe)
          case (Some am')
          obtain a' m' where "am' = (a', m')" by (cases am') simp
          with Output_OK Inl ForwardOrEdit Some show ?thesis 
            by cases (simp_all add: id'_def)
        qed (erule S'.cases, simp_all add: id'_def)
      qed (erule S'.cases, simp_all add: id'_def)+
    next
      case (Inr query')
      with Output_OK show ?thesis by (cases; cases query') (simp_all)
    qed
  next
    case (State_OK p q query state answer state')
    show ?case
    proof (cases query)
      case (Inl adv_query)
      show ?thesis
      proof (cases adv_query)
        case Look
        with State_OK Inl show ?thesis 
        proof cases
          case (2 m)
          have "S' (return_spmf (Inl (Some (x, m)), (), Store m)) (return_spmf (Store m, None, [m \<mapsto> x]))" for x
            by (rule S'.intros) (simp only: 2)
          with 2 show ?thesis using State_OK(2-) Inl Look
            by clarsimp (simp add: cond_spmf_spmf_of_set spmf_of_set_singleton map_spmf_conv_bind_spmf[symmetric]
                split_beta cond_spmf_fst_def image_def vimage_def id'_def)
        qed (auto simp add: map_spmf_const[symmetric] map_spmf_conv_bind_spmf[symmetric] image_def intro: S'.intros; simp add: id'_def)+
      next
        case (ForwardOrEdit foe)
        show ?thesis 
        proof (cases foe)
          case None
          with State_OK Inl ForwardOrEdit show ?thesis
            by cases(auto simp add: map_spmf_const[symmetric] map_spmf_conv_bind_spmf[symmetric] image_def S'.intros)
        next
          case (Some am')
          obtain a' m' where [simp]: "am' = (a', m')" by (cases am')
          from State_OK Inl ForwardOrEdit Some show ?thesis 
          proof cases
            case (4 m a)
            then show ?thesis using State_OK(2-) Inl ForwardOrEdit Some
              by (auto simp add: if_distrib_exec_gpv if_distrib_map_spmf split_def image_def if_distrib[symmetric] intro: S'.intros cong: if_cong)
          qed (auto simp add: map_spmf_const[symmetric] map_spmf_conv_bind_spmf[symmetric] image_def intro:S'.intros)
        qed
      next
        case Drop
        with State_OK Inl show ?thesis 
          by cases (auto simp add: map_spmf_const[symmetric] map_spmf_conv_bind_spmf[symmetric] image_def intro:S'.intros; simp add: id'_def)+
      qed
    next
      case Snd_Rcv: (Inr query')
      with State_OK show ?thesis
        by(cases; cases query')
          (auto simp add: map_spmf_const[symmetric] map_spmf_conv_bind_spmf[symmetric] image_def;
            (rule S'.intros; simp add: in_nlists_UNIV id'_def))+
    qed
  qed

  from * show ?thesis by simp
qed

private lemma real_resource_wiring: "macode.res (rnd \<eta>) (mac \<eta>) = 
  RES (\<dagger>\<dagger>insec_channel.insec_oracle \<oplus>\<^sub>O rorc_channel_send \<oplus>\<^sub>O rorc_channel_recv) ((False, ()), Map.empty, Void)"
  (is "?L = ?R") including lifting_syntax
proof -
  have *: "(\<lambda>x y. map_spmf (map_prod id lprodr) ((A \<oplus>\<^sub>O B) (rprodl x) y))
          = (\<lambda>x yl. map_spmf (\<lambda>p. ((), lprodr (snd p))) (A (rprodl x) yl)) \<oplus>\<^sub>O    
            (\<lambda>x yr. map_spmf (\<lambda>p. (fst p, lprodr (snd p))) (B (rprodl x) yr)) " for A B C    
  proof -
    have aux: "map_prod id g \<circ> apfst h = apfst h \<circ> map_prod id g" for f g h  by auto
    show ?thesis
      by (auto simp add: aux plus_oracle_def spmf.map_comp[where f="apfst _", symmetric] 
          spmf.map_comp[where f="map_prod id lprodr"] sum.case_distrib[where h="map_spmf _"] cong:sum.case_cong split!:sum.splits)
        (subst plus_oracle_def[symmetric], simp add: map_prod_def split_def)
  qed

  have "?L = RES (\<dagger>\<dagger>insec_channel.insec_oracle \<oplus>\<^sub>O (rprodl ---> id ---> map_spmf (map_prod id lprodr))
         (lift_state_oracle extend_state_oracle (attach_callee
           (\<lambda>s m. if s 
             then Done ((), True)
             else do { 
               r \<leftarrow> Pause (Inl m) Done;
               a \<leftarrow> lift_spmf (mac \<eta> (projl r) m);
               _ \<leftarrow> Pause (Inr (a, m)) Done; 
               ( Done ((), True))}) ((rorc.rnd_oracle (rnd \<eta>))\<dagger> \<oplus>\<^sub>O \<dagger>channel.send_oracle)) \<oplus>\<^sub>O
           \<dagger>\<dagger>(\<lambda>s q. do {
             (amo, s') \<leftarrow> \<dagger>channel.recv_oracle s ();
             case amo of 
               None \<Rightarrow> return_spmf (None, s')
             | Some (a, m) \<Rightarrow> do {
                 (r, s'') \<leftarrow> (rorc.rnd_oracle (rnd \<eta>))\<dagger> s' m;
                 a'\<leftarrow> mac \<eta> r m;
                 return_spmf (if a' = a then Some m else None, s'')}}))) ((False, ()), Map.empty, Void)"
  proof -
    note[simp] = attach_CNV_RES attach_callee_parallel_intercept attach_stateless_callee
      resource_of_oracle_rprodl Rel_def prod.rel_eq[symmetric] extend_state_oracle_plus_oracle[symmetric]
      conv_callee_parallel[symmetric] conv_callee_parallel_id_left[where s="()", symmetric]
      o_def  bind_map_spmf exec_gpv_bind split_def option.case_distrib[where h="\<lambda>gpv. exec_gpv _ gpv _"]

    show ?thesis
      unfolding channel.res_def rorc.res_def macode.res_def macode.routing_def
        macode.\<pi>E_def macode.enm_def macode.dem_def interface_wiring
      by (subst lift_state_oracle_extend_state_oracle | auto cong del: option.case_cong_weak intro: extend_state_oracle_parametric)+
  qed

  also have "... = ?R"
    unfolding rorc_channel_send_def rorc_channel_recv_def extend_state_oracle_def
    by(simp add: * split_def o_def map_fun_def spmf.map_comp extend_state_oracle_def lift_state_oracle_def 
        exec_gpv_bind if_distrib[where f="\<lambda>gpv. exec_gpv _ gpv _"]  cong: if_cong)
      (simp add: split_def o_def rprodl_def Pair_fst_Unity  bind_map_spmf map_spmf_bind_spmf 
        if_distrib[where f="map_spmf _"]  option.case_distrib[where h="map_spmf _"] cong: if_cong option.case_cong)

  finally show ?thesis .
qed

private lemma ideal_resource_wiring: "(CNV callee s) |\<^sub>= 1\<^sub>C \<rhd> channel.res auth_channel.auth_oracle = 
  RES (callee_auth_channel callee \<oplus>\<^sub>O \<dagger>\<dagger>channel.send_oracle \<oplus>\<^sub>O \<dagger>\<dagger>channel.recv_oracle ) (s, (), Void)"   (is "?L1 \<rhd> _ = ?R")
proof -
  have[simp]: "\<I>_full, \<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<turnstile>\<^sub>C ?L1 \<sim> ?L1" (is "_, ?I \<turnstile>\<^sub>C _ \<sim> _")
    by(rule eq_\<I>_converter_mono)
      (rule parallel_converter2_eq_\<I>_cong eq_\<I>_converter_reflI WT_converter_\<I>_full \<I>_full_le_plus_\<I> order_refl plus_\<I>_mono)+ 

  have[simp]: "?I \<turnstile>c (auth_channel.auth_oracle \<oplus>\<^sub>O channel.send_oracle \<oplus>\<^sub>O channel.recv_oracle) s \<surd>" for s 
    by(rule WT_plus_oracleI WT_parallel_oracle WT_callee_full; (unfold split_paired_all)?)+

  have[simp]: "?L1 \<rhd> RES (auth_channel.auth_oracle \<oplus>\<^sub>O channel.send_oracle \<oplus>\<^sub>O channel.recv_oracle) Void = ?R"     
    by(simp add: conv_callee_parallel_id_right[where s'="()", symmetric] attach_CNV_RES 
        attach_callee_parallel_intercept resource_of_oracle_rprodl extend_state_oracle_plus_oracle)

  show ?thesis unfolding channel.res_def
    by (subst eq_\<I>_attach[OF WT_resource_of_oracle, where \<I>' = "?I" and conv="?L1" and conv'="?L1"]) simp_all
qed

lemma all_together:
  defines "\<I> \<equiv> \<I>_uniform (Set.Collect (valid_mac_query \<eta>)) (insert None (Some ` (nlists UNIV \<eta> \<times> nlists UNIV \<eta>))) \<oplus>\<^sub>\<I>
     (\<I>_uniform (vld \<eta>) UNIV \<oplus>\<^sub>\<I> \<I>_uniform UNIV (insert None (Some ` vld \<eta>)))"
  assumes "\<eta> > 0"
    and "interaction_bounded_by' (\<lambda>_. True) (\<A> \<eta>) q"
    and lossless: "plossless_gpv \<I> (\<A> \<eta>)"
    and WT: "\<I> \<turnstile>g \<A> \<eta> \<surd>"
  shows 
    "\<bar>spmf (connect (\<A> \<eta>) (CNV sim (Inl None) |\<^sub>= 1\<^sub>C \<rhd> channel.res auth_channel.auth_oracle)) True -
          spmf (connect (\<A> \<eta>) (macode.res (rnd \<eta>) (mac \<eta>))) True\<bar> \<le> q / real (2 ^ \<eta>)"
proof -
  have *: "\<forall>a b. ma = Edit (a, b) \<longrightarrow> length a = \<eta> \<and> length b = \<eta> \<Longrightarrow> valid_mac_query \<eta> ma" for ma a b
    by(cases "(\<eta>, ma)" rule: valid_mac_query.cases)(auto simp add: vld_def in_nlists_UNIV)

  have assm4_alt: "outs_gpv \<I> (\<A> \<eta>) \<subseteq> valid_insecQ <+> nlists UNIV (id' \<eta>) <+> UNIV"
    using assms(5)[THEN WT_gpv_outs_gpv] unfolding id'_def
    by(rule ord_le_eq_trans) (auto simp add: * split: aquery.split option.split simp add: in_nlists_UNIV vld_def \<I>_def)

  have "callee_invariant_on (callee_auth_channel sim \<oplus>\<^sub>O \<dagger>\<dagger>channel.send_oracle \<oplus>\<^sub>O \<dagger>\<dagger>channel.recv_oracle) 
    (\<lambda>(s1, _, s3). (\<forall>x y. s1 = Inl (Some (x, y)) \<longrightarrow> length x = \<eta> \<and> length y = \<eta>) \<and> pred_cstate (\<lambda>x. length x = \<eta>) s3) \<I>"
    apply unfold_locales
    subgoal for s x y s'
      by(cases "(fst s, projl x)" rule: sim.cases; cases "snd (snd s)")
        (auto split: if_split_asm simp add: exec_gpv_bind auth_channel.auth_oracle.simps channel.send_oracle.simps channel.recv_oracle.simps vld_def in_nlists_UNIV \<I>_def)
    subgoal for s
      apply(rule WT_calleeI)
      subgoal for x
        by(cases "(fst s, projl x)" rule: sim.cases; cases "snd (snd s)")
          (auto split: if_split_asm simp add: exec_gpv_bind auth_channel.auth_oracle.simps channel.send_oracle.simps channel.recv_oracle.simps vld_def in_nlists_UNIV \<I>_def)
      done
    done
  then have WT1: "\<I> \<turnstile>res RES (callee_auth_channel sim \<oplus>\<^sub>O \<dagger>\<dagger>channel.send_oracle \<oplus>\<^sub>O \<dagger>\<dagger>channel.recv_oracle) (Inl None, (), Void) \<surd>"
    by(rule callee_invariant_on.WT_resource_of_oracle) simp

  have "callee_invariant_on (lazy_channel_insec \<oplus>\<^sub>O lazy_channel_send \<oplus>\<^sub>O lazy_channel_recv_f)
     (\<lambda>(s1, s2, s3). pred_cstate (\<lambda>x. length x = \<eta>) s1 \<and> pred_option (\<lambda>(x, y). length x = \<eta> \<and> length y = \<eta>) s2 \<and> ran s3 \<subseteq> nlists UNIV \<eta>)
     \<I>"
    apply unfold_locales
    subgoal for s x y s'
      apply(clarsimp simp add: \<I>_def; elim PlusE; clarsimp)
      subgoal for _ _ _ x'
        by(cases "(s, x')" rule: lazy_channel_insec.cases)
          (auto simp add: vld_def in_nlists_UNIV rnd_def split: option.split_asm)
      subgoal by(cases "(s, projl (projr x))" rule: lazy_channel_send.cases)(auto simp add: vld_def in_nlists_UNIV)
      subgoal by(cases "(s, ())" rule: lazy_channel_recv_f.cases)(auto 4 3 split: option.split_asm if_split_asm simp add: in_nlists_UNIV vld_def ran_def rnd_def)
      done
    subgoal for s
      apply(clarsimp simp add: \<I>_def; intro conjI WT_calleeI; clarsimp)
      subgoal for _ _ _ x
        by(cases "(s, x)" rule: lazy_channel_insec.cases)
          (auto simp add: vld_def in_nlists_UNIV rnd_def ran_def split: option.split_asm)
      subgoal by(cases "(s, ())" rule: lazy_channel_recv_f.cases)(auto 4 3 split: option.split_asm if_split_asm simp add: in_nlists_UNIV vld_def ran_def rnd_def)
      done
    done
  then have WT2: "\<I> \<turnstile>res RES (lazy_channel_insec \<oplus>\<^sub>O lazy_channel_send \<oplus>\<^sub>O lazy_channel_recv_f) (Void, None, Map.empty) \<surd>"
    by(rule callee_invariant_on.WT_resource_of_oracle) simp

  have "callee_invariant_on (lazy_channel_insec \<oplus>\<^sub>O lazy_channel_send \<oplus>\<^sub>O lazy_channel_recv)
     (\<lambda>(s1, s2, s3). pred_cstate (\<lambda>x. length x = \<eta>) s1 \<and> pred_option (\<lambda>(x, y). length x = \<eta> \<and> length y = \<eta>) s2 \<and> ran s3 \<subseteq> nlists UNIV \<eta>)
     \<I>"
    apply unfold_locales
    subgoal for s x y s'
      apply(clarsimp simp add: \<I>_def; elim PlusE; clarsimp)
      subgoal for _ _ _ x'
        by(cases "(s, x')" rule: lazy_channel_insec.cases)
          (auto simp add: vld_def in_nlists_UNIV rnd_def split: option.split_asm)
      subgoal by(cases "(s, projl (projr x))" rule: lazy_channel_send.cases)(auto simp add: vld_def in_nlists_UNIV)
      subgoal by(cases "(s, ())" rule: lazy_channel_recv.cases)(auto 4 3 split: option.split_asm if_split_asm simp add: in_nlists_UNIV vld_def ran_def rnd_def option.pred_set)
      done
    subgoal for s
      apply(clarsimp simp add: \<I>_def; intro conjI WT_calleeI; clarsimp)
      subgoal for _ _ _ x
        by(cases "(s, x)" rule: lazy_channel_insec.cases)
          (auto simp add: vld_def in_nlists_UNIV rnd_def ran_def split: option.split_asm)
      subgoal by(cases "(s, ())" rule: lazy_channel_recv_f.cases)(auto 4 3 split: option.split_asm if_split_asm simp add: in_nlists_UNIV vld_def ran_def rnd_def)
      done
    done
  then have WT3: "\<I> \<turnstile>res RES (lazy_channel_insec \<oplus>\<^sub>O lazy_channel_send \<oplus>\<^sub>O lazy_channel_recv) (Void, None, Map.empty) \<surd>"
    by(rule callee_invariant_on.WT_resource_of_oracle) simp

  have "callee_invariant_on (\<dagger>\<dagger>insec_channel.insec_oracle \<oplus>\<^sub>O rorc_channel_send \<oplus>\<^sub>O rorc_channel_recv)
    (\<lambda>(_, m, s). ran m \<subseteq> nlists UNIV \<eta> \<and> pred_cstate (\<lambda>(x, y). length x = \<eta> \<and> length y = \<eta>) s) \<I>"
    apply(unfold_locales)
    subgoal for s x y s'
      apply(clarsimp simp add: \<I>_def; elim PlusE; clarsimp)
      subgoal for _ _ _ x'
        by(cases "(snd (snd s), x')" rule: insec_channel.insec_oracle.cases)
          (auto simp add: vld_def in_nlists_UNIV rnd_def insec_channel.insec_oracle.simps split: option.split_asm)
      subgoal
        by(cases "snd (snd s)")
          (auto 4 3 simp add: channel.send_oracle.simps rorc_channel_send_def rorc.rnd_oracle.simps in_nlists_UNIV rnd_def vld_def mac_def ran_def split: option.split_asm if_split_asm)
      subgoal
        by(cases "snd (snd s)")
          (auto 4 4 simp add: rorc_channel_recv_def channel.recv_oracle.simps rorc.rnd_oracle.simps rnd_def mac_def ran_def iff: in_nlists_UNIV split: option.split_asm if_split_asm)
      done
    subgoal for s
      apply(clarsimp simp add: \<I>_def; intro conjI WT_calleeI; clarsimp)
      subgoal for _ _ _ x'
        by(cases "(snd (snd s), x')" rule: insec_channel.insec_oracle.cases)
          (auto simp add: vld_def in_nlists_UNIV rnd_def insec_channel.insec_oracle.simps split: option.split_asm)
      subgoal
        by(cases "snd (snd s)")
          (auto simp add: rorc_channel_recv_def channel.recv_oracle.simps rorc.rnd_oracle.simps rnd_def mac_def vld_def ran_def iff: in_nlists_UNIV split: option.split_asm if_split_asm)
      done
    done
  then have WT4: "\<I> \<turnstile>res RES (\<dagger>\<dagger>insec_channel.insec_oracle \<oplus>\<^sub>O rorc_channel_send \<oplus>\<^sub>O rorc_channel_recv) ((False, ()), Map.empty, Void) \<surd>"
    by(rule callee_invariant_on.WT_resource_of_oracle) simp

  note game_difference[OF assms(3), folded \<I>_def, OF assms(4,5)]
  also note connect_cong_trace[OF trace_eq_sim WT assm4_alt WT1 WT2, symmetric]
  also note connect_cong_trace[OF trace_eq_lazy, OF assms(2), OF WT assm4_alt WT3 WT4]
  also note ideal_resource_wiring[of sim, of "Inl None", symmetric]
  also note real_resource_wiring[symmetric]
  finally show ?thesis by simp
qed

end

context begin
interpretation MAC: macode "rnd \<eta>" "mac \<eta>" for \<eta> . 
interpretation A_CHAN: auth_channel . 

lemma WT_enm: 
  "X \<noteq> {} \<Longrightarrow> \<I>_uniform (vld \<eta>) UNIV, \<I>_uniform (vld \<eta>) X \<oplus>\<^sub>\<I> \<I>_uniform (X \<times> vld \<eta>) UNIV \<turnstile>\<^sub>C MAC.enm \<eta> \<surd>"
  unfolding MAC.enm_def
  by(rule WT_converter_of_callee) (auto simp add: mac_def)

lemma WT_dem: "\<I>_uniform UNIV (insert None (Some ` vld \<eta>)), \<I>_full \<oplus>\<^sub>\<I> \<I>_uniform UNIV (insert None (Some ` (nlists UNIV \<eta> \<times> nlists UNIV \<eta>))) \<turnstile>\<^sub>C MAC.dem \<eta> \<surd>"
  unfolding MAC.dem_def
  by (rule WT_converter_of_callee) (auto simp add: vld_def stateless_callee_def mac_def split: option.split_asm)

lemma valid_insec_query_of [simp]: "valid_mac_query \<eta> (insec_query_of x)"
  by(cases x) simp_all

lemma secure_mac:
  defines "\<I>_real \<equiv> \<lambda>\<eta>. \<I>_uniform {x. valid_mac_query \<eta> x} (insert None (Some ` (nlists UNIV \<eta> \<times> nlists UNIV \<eta>)))"
    and "\<I>_ideal \<equiv> \<lambda>\<eta>. \<I>_uniform UNIV (insert None (Some ` nlists UNIV \<eta>))"
    and "\<I>_common \<equiv> \<lambda>\<eta>. \<I>_uniform (vld \<eta>) UNIV \<oplus>\<^sub>\<I> \<I>_uniform UNIV (insert None (Some ` vld \<eta>))"
  shows
    "constructive_security MAC.res (\<lambda>_. A_CHAN.res) (\<lambda>_. CNV sim (Inl None))
     \<I>_real \<I>_ideal \<I>_common (\<lambda>_. enat q) True (\<lambda>_. insec_auth_wiring)"
proof
  show WT_res [WT_intro]: "\<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>res MAC.res \<eta> \<surd>" for \<eta>
  proof -
    let ?I = "pred_cstate (\<lambda>(x, y). length x = \<eta> \<and> length y = \<eta>)"

    have *: "callee_invariant_on (MAC.RO.rnd_oracle \<eta> \<oplus>\<^sub>O MAC.RO.rnd_oracle \<eta>) (\<lambda>m. ran m \<subseteq> vld \<eta>) (\<I>_uniform (vld \<eta>) (vld \<eta>) \<oplus>\<^sub>\<I> \<I>_full)" for \<eta>
      apply unfold_locales
      subgoal for s x y s' by(cases x; clarsimp split: option.split_asm; auto simp add: rnd_def vld_def)
      subgoal by(clarsimp intro!: WT_calleeI split: option.split_asm; auto simp add: rnd_def in_nlists_UNIV vld_def ran_def)
      done
    have [WT_intro]: "\<I>_uniform (vld \<eta>) (vld \<eta>) \<oplus>\<^sub>\<I> \<I>_full \<turnstile>res MAC.RO.res \<eta> \<surd>" for \<eta>
      unfolding MAC.RO.res_def by(rule callee_invariant_on.WT_resource_of_oracle[OF *]) simp
    have [simp]: "\<I>_real \<eta> \<turnstile>c MAC.INSEC.insec_oracle s \<surd>" if "?I s" for s
      apply(rule WT_calleeI)
      subgoal for x using that by(cases "(s, x)" rule: MAC.INSEC.insec_oracle.cases)(auto simp add: \<I>_real_def in_nlists_UNIV)
      done
    have [simp]: " \<I>_uniform UNIV (insert None (Some ` (nlists UNIV \<eta> \<times> nlists UNIV \<eta>))) \<turnstile>c A_CHAN.recv_oracle s \<surd>"
      if "?I s" for s :: "(bool list \<times> bool list) cstate" using that
      by(cases s)(auto intro!: WT_calleeI simp add: in_nlists_UNIV)
    have *: "callee_invariant_on (MAC.INSEC.insec_oracle \<oplus>\<^sub>O A_CHAN.send_oracle \<oplus>\<^sub>O A_CHAN.recv_oracle) ?I
      (\<I>_real \<eta> \<oplus>\<^sub>\<I> (\<I>_uniform (vld \<eta> \<times> vld \<eta>) UNIV \<oplus>\<^sub>\<I> \<I>_uniform UNIV (insert None (Some ` (nlists UNIV \<eta> \<times> nlists UNIV \<eta>)))))"
      apply unfold_locales
      subgoal for s x y s'
        by(cases s; cases "(s, projl x)" rule: MAC.INSEC.insec_oracle.cases)(auto simp add: \<I>_real_def vld_def in_nlists_UNIV)
      subgoal by(auto intro: WT_calleeI)
      done
    have [WT_intro]: "\<I>_real \<eta> \<oplus>\<^sub>\<I> (\<I>_uniform (vld \<eta> \<times> vld \<eta>) UNIV \<oplus>\<^sub>\<I> \<I>_uniform UNIV (insert None (Some ` (nlists UNIV \<eta> \<times> nlists UNIV \<eta>)))) \<turnstile>res MAC.INSEC.res \<surd>"  
      unfolding MAC.INSEC.res_def
      by(rule callee_invariant_on.WT_resource_of_oracle[OF *]) simp
    show ?thesis
      unfolding \<I>_common_def MAC.res_def
      by(rule WT_intro WT_enm[where X="vld \<eta>"] WT_dem | (simp add: vld_def; fail))+
  qed
  let ?I = "\<lambda>\<eta>. pred_cstate (\<lambda>x. length x = \<eta>)"
  have WT_auth: "\<I>_uniform UNIV (insert None (Some ` nlists UNIV \<eta>)) \<turnstile>c A_CHAN.auth_oracle s \<surd>"
    if "?I \<eta> s" for \<eta> s
    apply(rule WT_calleeI)
    subgoal for x using that by(cases "(s, x)" rule: A_CHAN.auth_oracle.cases; auto simp add: in_nlists_UNIV)
    done
  have WT_recv: "\<I>_uniform UNIV (insert None (Some ` vld \<eta>)) \<turnstile>c A_CHAN.recv_oracle s \<surd>"
    if "?I \<eta> s" for \<eta> s using that
    by(cases s)(auto intro!: WT_calleeI simp add: vld_def in_nlists_UNIV)
  have *: "callee_invariant_on (A_CHAN.auth_oracle \<oplus>\<^sub>O A_CHAN.send_oracle \<oplus>\<^sub>O A_CHAN.recv_oracle)
     (?I \<eta>) (\<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>)" for \<eta>
    apply(unfold_locales)
    subgoal for s x y s'
      by(cases "(s, projl x)" rule: A_CHAN.auth_oracle.cases; cases "projr x")(auto simp add: \<I>_common_def vld_def in_nlists_UNIV)
    subgoal for s using WT_auth WT_recv by(auto simp add: \<I>_common_def \<I>_ideal_def intro: WT_calleeI)
    done
  show WT_auth: "\<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>res A_CHAN.res \<surd>" for \<eta>
    unfolding A_CHAN.res_def by(rule callee_invariant_on.WT_resource_of_oracle[OF *]) simp

  let ?I_sim = "\<lambda>\<eta> (s :: (bool list \<times> bool list) option + unit). \<forall>x y. s = Inl (Some (x, y)) \<longrightarrow> length x = \<eta> \<and> length y = \<eta>"

  have "\<I>_real \<eta>, \<I>_ideal \<eta> \<turnstile>\<^sub>C CNV sim s \<surd>" if "?I_sim \<eta> s" for \<eta> s using that
    apply(coinduction arbitrary: s)
    subgoal for q r conv' s by(cases "(s, q)" rule: sim.cases)(auto simp add: \<I>_real_def \<I>_ideal_def vld_def in_nlists_UNIV)
    done
  then show [WT_intro]: "\<I>_real \<eta>, \<I>_ideal \<eta> \<turnstile>\<^sub>C CNV sim (Inl None) \<surd>" for \<eta> by simp

  { fix \<A> :: "security  \<Rightarrow> ((bool list \<times> bool list) insec_query + bool list + unit, (bool list \<times> bool list) option + unit + bool list option) distinguisher"
    assume WT: "\<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>g \<A> \<eta> \<surd>" for \<eta>
    assume bounded[simplified]: "interaction_bounded_by' (\<lambda>_. True) (\<A> \<eta>) q" for \<eta>
    assume lossless[simplified]: "True \<Longrightarrow> plossless_gpv (\<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) (\<A> \<eta>)" for \<eta>
    show "negligible (\<lambda>\<eta>. advantage (\<A> \<eta>) (CNV sim (Inl None) |\<^sub>= 1\<^sub>C \<rhd> A_CHAN.res) (MAC.res \<eta>))"
    proof -
      have f1: "negligible (\<lambda>\<eta>. q * (1 / real (2 ^ \<eta>)))" (is "negligible ?ov")
        by(rule negligible_poly_times[where n=0]) (simp add: negligible_inverse_powerI)+
  
      have f2: "(\<lambda>\<eta>. spmf (connect (\<A> \<eta>) (CNV sim (Inl None) |\<^sub>= 1\<^sub>C \<rhd> A_CHAN.res)) True -
           spmf (connect (\<A> \<eta>) (MAC.res \<eta>)) True) \<in> O(?ov)" (is "?L \<in> _")
        by (auto simp add: bigo_def intro!: all_together[simplified] bounded eventually_at_top_linorderI[where c=1] 
            exI[where x=1] lossless[unfolded \<I>_real_def \<I>_common_def] WT[unfolded \<I>_real_def \<I>_common_def])
      have "negligible ?L"  using f1 f2 by (rule negligible_mono[of "?ov"]) 
      then show ?thesis by (simp add: advantage_def)
    qed
  next
    let ?cnv = "map_converter id id insec_query_of auth_response_of 1\<^sub>C"
    show "\<exists>cnv. \<forall>\<D>. (\<forall>\<eta>. \<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>g \<D> \<eta> \<surd>) \<longrightarrow>
               (\<forall>\<eta>. interaction_bounded_by' (\<lambda>_. True) (\<D> \<eta>) q) \<longrightarrow>
               (\<forall>\<eta>. True \<longrightarrow> plossless_gpv (\<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) (\<D> \<eta>)) \<longrightarrow>
               (\<forall>\<eta>. wiring (\<I>_ideal \<eta>) (\<I>_real \<eta>) (cnv \<eta>) (insec_query_of, map_option snd)) \<and>
               negligible (\<lambda>\<eta>. advantage (\<D> \<eta>) A_CHAN.res (cnv \<eta> |\<^sub>= 1\<^sub>C \<rhd> MAC.res \<eta>))"
    proof(intro exI[where x="\<lambda>_. ?cnv"] strip conjI)
      fix \<D> :: "security \<Rightarrow> (auth_query + bool list + unit, bool list option + unit + bool list option) distinguisher"
      assume WT_D [rule_format, WT_intro]: "\<forall>\<eta>. \<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>g \<D> \<eta> \<surd>"

      let ?A = "\<lambda>\<eta>. UNIV <+> nlists UNIV \<eta> <+> UNIV"
      have WT1: "\<I>_ideal \<eta>, map_\<I> insec_query_of (map_option snd) (\<I>_real \<eta>) \<turnstile>\<^sub>C 1\<^sub>C \<surd>" for \<eta> 
        using WT_converter_id order_refl by(rule WT_converter_mono)(auto simp add: le_\<I>_def \<I>_ideal_def \<I>_real_def)
      have WT0: "\<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>  \<turnstile>res map_converter id id insec_query_of (map_option snd) 1\<^sub>C |\<^sub>= 1\<^sub>C \<rhd> MAC.res \<eta> \<surd>" for \<eta>
        by(rule WT1 WT_intro | simp)+

      have WT2: "\<I>_ideal \<eta>, map_\<I> insec_query_of (map_option snd) (\<I>_real \<eta>) \<turnstile>\<^sub>C 1\<^sub>C \<surd>" for \<eta>
        using WT_converter_id order_refl
        by(rule WT_converter_mono)(auto simp add: le_\<I>_def \<I>_ideal_def \<I>_real_def)
      have WT_cnv: "\<I>_ideal \<eta>, \<I>_real \<eta> \<turnstile>\<^sub>C ?cnv \<surd>" for \<eta>
        by(rule WT_converter_map_converter)(simp_all add: WT2)

      from eq_\<I>_converter_reflI[OF this] this
      show "wiring (\<I>_ideal \<eta>) (\<I>_real \<eta>) ?cnv insec_auth_wiring" for \<eta> ..

      define res' :: "security \<Rightarrow> _ \<Rightarrow> auth_query + (bool list + bool list \<times> bool list) + bool list + unit \<Rightarrow> _"
        where "res' \<eta> = 
         map_fun id (map_fun insec_query_of (map_spmf (map_prod (map_option snd) id))) \<dagger>MAC.INSEC.insec_oracle \<oplus>\<^sub>O
         ((MAC.RO.rnd_oracle \<eta>)\<dagger> \<oplus>\<^sub>O \<dagger>A_CHAN.send_oracle) \<oplus>\<^sub>O (MAC.RO.rnd_oracle \<eta>)\<dagger> \<oplus>\<^sub>O \<dagger>A_CHAN.recv_oracle"
        for \<eta>
      
      have push: "map_resource (map_sum f id) (map_sum g id) ((1\<^sub>C |\<^sub>= conv) \<rhd> res) =
         (1\<^sub>C |\<^sub>= conv) \<rhd> map_resource (map_sum f id) (map_sum g id) res"
        for f g conv res
      proof -
        have "map_resource (map_sum f id) (map_sum g id) ((1\<^sub>C |\<^sub>= conv) \<rhd> res) = map_converter f g id id 1\<^sub>C |\<^sub>= conv \<rhd> res"
          by(simp add: attach_map_converter parallel_converter2_map1_out sum.map_id0)
        also have "\<dots> = (1\<^sub>C |\<^sub>= conv) \<rhd> map_resource (map_sum f id) (map_sum g id) res"
          by(subst map_converter_id_move_right)(simp add: parallel_converter2_map1_out sum.map_id0 attach_map_converter)
        finally show ?thesis .
      qed
      have res': "map_resource (map_sum insec_query_of id) (map_sum (map_option snd) id) (MAC.res \<eta>) = 
        1\<^sub>C |\<^sub>= MAC.enm \<eta> |\<^sub>= MAC.dem \<eta> \<rhd> RES (res' \<eta>) (Map.empty, Void)"  for \<eta>
        unfolding MAC.res_def MAC.RO.res_def MAC.INSEC.res_def interface_wiring push
        by(simp add: parallel_converter2_map1_out sum.map_id0 attach_map_converter map_resource_resource_of_oracle map_sum_plus_oracle prod.map_id0 option.map_id0 map_fun_id res'_def)

      define res'' :: "security \<Rightarrow> (unit \<times> bool \<times> unit)  \<times> (bool list \<Rightarrow> bool list option) \<times> _ cstate \<Rightarrow> auth_query + bool list + unit \<Rightarrow> _"
        where "res'' \<eta> = map_fun rprodl (map_fun id (map_spmf (map_prod id lprodr)))
          (lift_state_oracle extend_state_oracle \<dagger>(map_fun id (map_fun insec_query_of (map_spmf (map_prod (map_option snd) id))) \<dagger>MAC.INSEC.insec_oracle) \<oplus>\<^sub>O
           \<dagger>(map_fun rprodl (map_fun id (map_spmf (map_prod id lprodr)))
              (lift_state_oracle extend_state_oracle
                (attach_callee
                  (\<lambda>bs m. if bs then Done ((), True) else Pause (Inl m) Done \<bind> (\<lambda>r. lift_spmf (mac \<eta> (projl r) m) \<bind> (\<lambda>a. Pause (Inr (a, m)) Done \<bind> (\<lambda>_. Done ((), True)))))
                  ((MAC.RO.rnd_oracle \<eta>)\<dagger> \<oplus>\<^sub>O \<dagger>A_CHAN.send_oracle)) \<oplus>\<^sub>O
               \<dagger>\<dagger>(\<lambda>s q. \<dagger>A_CHAN.recv_oracle s () \<bind>
                         (\<lambda>x. case x of (None, s') \<Rightarrow> return_spmf (None, s')
                               | (Some (x1, x2a), s') \<Rightarrow> (MAC.RO.rnd_oracle \<eta>)\<dagger> s' x2a \<bind> (\<lambda>(x, s'). mac \<eta> x x2a \<bind> (\<lambda>y. return_spmf (if y = x1 then Some x2a else None, s'))))))))"
        for \<eta>
      have "?cnv |\<^sub>= 1\<^sub>C \<rhd> MAC.res \<eta> = 1\<^sub>C |\<^sub>= MAC.enm \<eta> |\<^sub>= MAC.dem \<eta> \<rhd> RES (res' \<eta>) (Map.empty, Void)" for \<eta>
        by(simp add: parallel_converter2_map1_out attach_map_converter sum.map_id0 res' attach_compose[symmetric] comp_converter_parallel2 comp_converter_id_left)
      also have "\<dots> \<eta> = RES (res'' \<eta>) (((), False, ()), Map.empty, Void)" for \<eta>
        unfolding MAC.enm_def MAC.dem_def conv_callee_parallel[symmetric] conv_callee_parallel_id_left[where s="()", symmetric] attach_CNV_RES
        unfolding res'_def res''_def attach_callee_parallel_intercept attach_stateless_callee attach_callee_id_oracle prod.rel_eq[symmetric]
        by(simp add: extend_state_oracle_plus_oracle[symmetric] rprodl_extend_state_oracle sum.case_distrib[where h="\<lambda>x. exec_gpv _ x _"] 
             option.case_distrib[where h="\<lambda>x. exec_gpv _ x _"] prod.case_distrib[where h="\<lambda>x. exec_gpv _ x _"] exec_gpv_bind bind_map_spmf o_def
           cong: sum.case_cong option.case_cong)
      also
      define S :: "security \<Rightarrow> bool list cstate \<Rightarrow> (unit \<times> bool \<times> unit) \<times> (bool list \<Rightarrow> bool list option) \<times> (bool list \<times> bool list) cstate \<Rightarrow> bool"
        where "S \<eta> l r = (case (l, r) of
          (Void, ((_, False, _), m, Void)) \<Rightarrow> m = Map.empty
        | (Store x, ((_, True, _), m, Store (y, z))) \<Rightarrow> length x = \<eta> \<and> length y = \<eta> \<and> length z = \<eta> \<and> m = [z \<mapsto> y] \<and> x = z
        | (Collect x, ((_, True, _), m, Collect (y, z))) \<Rightarrow> length x = \<eta> \<and> length y = \<eta> \<and> length z = \<eta> \<and> m = [z \<mapsto> y] \<and> x = z
        | (Fail, ((_, True, _), m, Fail)) \<Rightarrow> True
        | _ \<Rightarrow> False)" for \<eta> l r

      note [simp] = spmf_rel_map bind_map_spmf exec_gpv_bind
      have "connect (\<D> \<eta>) (?cnv |\<^sub>= 1\<^sub>C \<rhd> MAC.res \<eta>) = connect (\<D> \<eta>) A_CHAN.res" for \<eta>
        unfolding calculation using WT_D _ WT_auth
        apply(rule connect_eq_resource_cong[symmetric])
        unfolding A_CHAN.res_def
        apply(rule eq_resource_on_resource_of_oracleI[where S="S \<eta>"])
         apply(rule rel_funI)+
        subgoal for s s' q q'
          by(cases q; cases "projl q"; cases "projr q"; clarsimp simp add: eq_on_def S_def res''_def split: cstate.split_asm bool.split_asm; clarsimp simp add: rel_spmf_return_spmf1 rnd_def mac_def bind_UNION \<I>_common_def vld_def in_nlists_UNIV S_def)+
        subgoal by(simp add: S_def)
        done
      then show adv: "negligible (\<lambda>\<eta>. advantage (\<D> \<eta>) A_CHAN.res (?cnv |\<^sub>= 1\<^sub>C \<rhd> MAC.res \<eta>))"
        by(simp add: advantage_def)
    qed
  }
qed

end

end
