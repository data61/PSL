section \<open>Security of one-time-pad encryption\<close>

theory One_Time_Pad imports
  System_Construction
begin

definition key :: "security \<Rightarrow> bool list spmf" where
  "key \<eta> \<equiv> spmf_of_set (nlists UNIV \<eta>)"

definition enc :: "security \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool list spmf" where
  "enc \<eta> k m \<equiv> return_spmf (k [\<oplus>] m)"

definition dec :: "security \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool list option" where
  "dec \<eta> k c \<equiv> Some (k [\<oplus>] c)"

definition sim :: "'b list option \<Rightarrow> 'a \<Rightarrow> ('b list option \<times> 'b list option, 'a, nat option) gpv" where
  "sim c q \<equiv> (do {
    lo \<leftarrow> Pause q Done;
    (case lo of 
      Some n \<Rightarrow> if c = None 
        then do { 
          x \<leftarrow> lift_spmf (spmf_of_set (nlists UNIV n));
          Done (Some x, Some x)} 
        else Done (c, c)
    | None   \<Rightarrow> Done (None, c))})"

context
  fixes \<eta> :: "security"
begin

private definition key_channel_send :: "bool list option \<times> bool list  cstate
  \<Rightarrow> bool list \<Rightarrow> (unit \<times> bool list option \<times> bool list cstate) spmf" where
  "key_channel_send s m \<equiv> do {
    (k, s) \<leftarrow> (key.key_oracle (key \<eta>))\<dagger> s ();
    c \<leftarrow> enc \<eta> k m;
    (_, s) \<leftarrow> \<dagger>channel.send_oracle s c;
    return_spmf ((), s)}"

private definition key_channel_recv :: "bool list option \<times> bool list cstate
  \<Rightarrow> 'a \<Rightarrow> (bool list option \<times> bool list option \<times> bool list cstate) spmf" where 
  "key_channel_recv s m \<equiv>do {
    (c, s) \<leftarrow> \<dagger>channel.recv_oracle s ();
    (case c of None \<Rightarrow> return_spmf (None, s)
    | Some c' \<Rightarrow> do {
      (k, s) \<leftarrow> (key.key_oracle (key \<eta>))\<dagger> s ();
      return_spmf (dec \<eta> k c', s)})}"

private abbreviation callee_sec_channel where
  "callee_sec_channel callee \<equiv> lift_state_oracle extend_state_oracle (attach_callee callee sec_channel.sec_oracle)"

private inductive S :: "(bool list option \<times> unit \<times> bool list cstate) spmf \<Rightarrow> 
  (bool list option \<times> bool list cstate) spmf \<Rightarrow> bool" where
  "S (return_spmf (None, (), Void)) 
     (return_spmf (None, Void))"
| "S (return_spmf (None, (), Store plain)) 
     (map_spmf (\<lambda>key. (Some key, Store (key [\<oplus>] plain))) (spmf_of_set (nlists UNIV \<eta>)))"
if "length plain = id' \<eta>"
| "S (return_spmf (None, (), Collect plain)) 
     (map_spmf (\<lambda>key. (Some key, Collect (key [\<oplus>] plain))) (spmf_of_set (nlists UNIV \<eta>)))"
if "length plain = id' \<eta>"
| "S (return_spmf (Some (key [\<oplus>] plain), (), Store plain)) 
     (return_spmf (Some key, Store (key [\<oplus>] plain)))"
if "length plain = id' \<eta>" "length key = id' \<eta>" for key
| "S (return_spmf (Some (key [\<oplus>] plain), (), Collect plain)) 
     (return_spmf (Some key, Collect (key [\<oplus>] plain)))"
if "length plain = id' \<eta>" "length key = id' \<eta>" for key
| "S (return_spmf (None, (), Fail)) 
     (map_spmf (\<lambda>x. (Some x, Fail)) (spmf_of_set (nlists UNIV \<eta>)))"
| "S (return_spmf (Some (key [\<oplus>] plain), (), Fail)) 
     (return_spmf (Some key, Fail))"
if "length plain = id' \<eta>" "length key = id' \<eta>" for key plain


lemma resources_indistinguishable: 
  shows "(UNIV <+> nlists UNIV (id' \<eta>) <+> UNIV) \<turnstile>\<^sub>R 
    RES (callee_sec_channel sim \<oplus>\<^sub>O \<dagger>\<dagger>channel.send_oracle \<oplus>\<^sub>O \<dagger>\<dagger>channel.recv_oracle) (None :: bool list option, (), Void) 
    \<approx> 
    RES (\<dagger>auth_channel.auth_oracle \<oplus>\<^sub>O key_channel_send \<oplus>\<^sub>O key_channel_recv) (None :: bool list option, Void)" 
    (is "?A \<turnstile>\<^sub>R RES (?L1 \<oplus>\<^sub>O ?L2 \<oplus>\<^sub>O ?L3) ?SL \<approx> RES (?R1 \<oplus>\<^sub>O ?R2 \<oplus>\<^sub>O ?R3) ?SR")
proof -
  note [simp] = 
    exec_gpv_bind spmf.map_comp o_def map_bind_spmf bind_map_spmf bind_spmf_const
    sec_channel.sec_oracle.simps auth_channel.auth_oracle.simps
    channel.send_oracle.simps key_channel_send_def
    channel.recv_oracle.simps key_channel_recv_def
    key.key_oracle.simps dec_def key_def enc_def

  have *: "?A \<turnstile>\<^sub>C ?L1 \<oplus>\<^sub>O ?L2 \<oplus>\<^sub>O ?L3(?SL) \<approx> ?R1 \<oplus>\<^sub>O ?R2 \<oplus>\<^sub>O ?R3(?SR)"
  proof(rule trace'_eqI_sim[where S=S], goal_cases Init_OK Output_OK State_OK)
    case Init_OK
    show ?case by (simp add: S.simps)
  next
    case (Output_OK p q query)
    show ?case 
    proof (cases query)
      case (Inl adv_query)
      with Output_OK show ?thesis
      proof (cases adv_query)
        case Look
        with Output_OK Inl show ?thesis 
        proof cases
          case Store_State_Channel: (2 plain)

          have*: "length plain = id' \<eta> \<Longrightarrow> 
            map_spmf (\<lambda>x. Inl (Some x)) (spmf_of_set (nlists UNIV (id' \<eta>))) =
            map_spmf (\<lambda>x. Inl (Some x)) (map_spmf (\<lambda>x. x [\<oplus>] plain) (spmf_of_set (nlists UNIV \<eta>)))" for \<eta> 
            unfolding id'_def by (subst xor_list_commute, subst one_time_pad[where xs=plain, symmetric]) simp_all

          from Store_State_Channel show ?thesis using Output_OK(2-) Inl Look
            by(simp add: sim_def, simp add: map_spmf_conv_bind_spmf[symmetric])
              (subst (2) spmf.map_comp[where f="\<lambda>x. Inl (Some x)", symmetric, unfolded o_def], simp only: *)
        qed (auto simp add: sim_def)
      qed (auto simp add: sim_def id'_def elim: S.cases)
    next
      case Snd_Rcv: (Inr query')
      with Output_OK show ?thesis
      proof (cases query')
        case (Inr rcv_query)
        with Output_OK Snd_Rcv show ?thesis 
        proof cases
          case Collect_State_Channel: (3 plain)
          then show ?thesis using Output_OK(2-) Snd_Rcv Inr
            by (simp cong: bind_spmf_cong_simp add: in_nlists_UNIV id'_def)  
        qed simp_all
      qed (auto elim: S.cases)
    qed
  next
    case (State_OK p q query state answer state')
    then show ?case 
    proof (cases query)
      case (Inl adv_query)
      with State_OK show ?thesis
      proof (cases adv_query)
        case Look
        with State_OK Inl show ?thesis
        proof cases
          case Store_State_Channel: (2 plain)
          have *: "length plain = id' \<eta> \<Longrightarrow> key \<in> nlists UNIV \<eta>  \<Longrightarrow> 
            S (cond_spmf_fst (map_spmf (\<lambda>x. (Inl (Some x), Some x, (), Store plain))
               (spmf_of_set (nlists UNIV (id' \<eta>)))) (Inl (Some (key [\<oplus>] plain))))
            (cond_spmf_fst  (map_spmf (\<lambda>x. (Inl (Some (x [\<oplus>] plain)), Some x, Store (x [\<oplus>] plain)))
               (spmf_of_set (nlists UNIV \<eta>))) (Inl (Some (key [\<oplus>] plain))))" for key 
          proof(subst (1 2) cond_spmf_fst_map_Pair1, goal_cases)
            case 2
            note inj_onD[OF inj_on_xor_list_nlists, rotated, simplified xor_list_commute]
            with 2 show ?case 
              unfolding inj_on_def by (auto simp add: id'_def)    
          next
            case 5
            note inj_onD[OF inj_on_xor_list_nlists, rotated, simplified xor_list_commute]
            with 5 show ?case 
              by (subst (1 2 3) inv_into_f_f)
                ((clarsimp simp add: inj_on_def), (auto simp add: S.simps id'_def inj_on_def in_nlists_UNIV ))
          qed (simp_all add: id'_def in_nlists_UNIV min_def inj_on_def)
          from Store_State_Channel show ?thesis using State_OK(2-) Inl Look
            by (clarsimp simp add: sim_def) (simp add: map_spmf_conv_bind_spmf[symmetric] * )
        qed (auto simp add: sim_def map_spmf_conv_bind_spmf[symmetric] S.simps)
      qed (erule S.cases; (simp add: sim_def, auto simp add: map_spmf_conv_bind_spmf[symmetric] S.simps))+
    next
      case Snd_Rcv: (Inr query')
      with State_OK show ?thesis
      proof (cases query')
        case (Inr rcv_query)
        with State_OK Snd_Rcv show ?thesis
        proof cases
          case Collect_State_Channel: (3 plain)
          then show ?thesis using State_OK(2-) Snd_Rcv Inr
            by clarsimp (simp add: S.simps in_nlists_UNIV id'_def map_spmf_conv_bind_spmf[symmetric] cong: bind_spmf_cong_simp)
        qed (simp add: sim_def, auto simp add: map_spmf_conv_bind_spmf[symmetric] S.simps)
      qed (erule S.cases, 
          (simp add: sim_def, auto simp add: map_spmf_conv_bind_spmf[symmetric] S.simps  in_nlists_UNIV))
    qed
  qed

  from * show ?thesis by simp
qed

lemma real_resource_wiring: 
  shows "cipher.res (key \<eta>) (enc \<eta>) (dec \<eta>) 
    = RES (\<dagger>auth_channel.auth_oracle \<oplus>\<^sub>O key_channel_send \<oplus>\<^sub>O key_channel_recv) (None, Void)"
  including lifting_syntax
proof -
  note[simp]= Rel_def prod.rel_eq[symmetric] split_def split_beta o_def exec_gpv_bind bind_map_spmf 
    resource_of_oracle_rprodl rprodl_extend_state_oracle
    conv_callee_parallel[symmetric] extend_state_oracle_plus_oracle[symmetric]  
    attach_CNV_RES attach_callee_parallel_intercept attach_stateless_callee 

  show ?thesis
    unfolding channel.res_def cipher.res_def  cipher.routing_def cipher.enc_def cipher.dec_def 
      interface_wiring cipher.\<pi>E_def key.res_def key_channel_send_def key_channel_recv_def
    by (simp add: conv_callee_parallel_id_left[where s="()", symmetric])
      ((auto cong: option.case_cong simp add: option.case_distrib[where h="\<lambda>gpv. exec_gpv _ gpv _"] 
          intro!: extend_state_oracle_parametric ) | subst lift_state_oracle_extend_state_oracle)+
qed

lemma ideal_resource_wiring: 
  shows "(CNV callee s) |\<^sub>= 1\<^sub>C \<rhd> channel.res sec_channel.sec_oracle 
    = RES (callee_sec_channel callee \<oplus>\<^sub>O \<dagger>\<dagger>channel.send_oracle \<oplus>\<^sub>O \<dagger>\<dagger>channel.recv_oracle ) (s, (), Void)"  (is "?L1 \<rhd> _ = ?R")
proof -
  have[simp]: "\<I>_full, \<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_full) \<turnstile>\<^sub>C ?L1 \<sim> ?L1" (is "_, ?I \<turnstile>\<^sub>C _ \<sim> _")
    by(rule eq_\<I>_converter_mono)
      (rule parallel_converter2_eq_\<I>_cong eq_\<I>_converter_reflI WT_converter_\<I>_full \<I>_full_le_plus_\<I> order_refl plus_\<I>_mono)+ 

  have[simp]: "?I \<turnstile>c (sec_channel.sec_oracle \<oplus>\<^sub>O channel.send_oracle \<oplus>\<^sub>O channel.recv_oracle) s \<surd>" for s 
    by(rule WT_plus_oracleI WT_parallel_oracle WT_callee_full; (unfold split_paired_all)?)+

  have[simp]: "?L1 \<rhd> RES (sec_channel.sec_oracle \<oplus>\<^sub>O channel.send_oracle \<oplus>\<^sub>O channel.recv_oracle) Void = ?R"     
    by(simp add: conv_callee_parallel_id_right[where s'="()", symmetric] attach_CNV_RES 
        attach_callee_parallel_intercept resource_of_oracle_rprodl extend_state_oracle_plus_oracle)

  show ?thesis unfolding channel.res_def
    by (subst eq_\<I>_attach[OF WT_resource_of_oracle, where ?\<I>' = "?I" and ?conv="?L1" and ?conv'="?L1"]) simp_all
qed

end

lemma eq_\<I>_gpv_Done1:
  "eq_\<I>_gpv A \<I> (Done x) gpv \<longleftrightarrow> lossless_spmf (the_gpv gpv) \<and> (\<forall>a\<in>set_spmf (the_gpv gpv). eq_\<I>_generat A \<I> (eq_\<I>_gpv A \<I>) (Pure x) a)"
  by(auto intro: eq_\<I>_gpv.intros simp add: rel_spmf_return_spmf1 elim: eq_\<I>_gpv.cases)

lemma eq_\<I>_gpv_Done2:
  "eq_\<I>_gpv A \<I> gpv (Done x) \<longleftrightarrow> lossless_spmf (the_gpv gpv) \<and> (\<forall>a\<in>set_spmf (the_gpv gpv). eq_\<I>_generat A \<I> (eq_\<I>_gpv A \<I>) a (Pure x))"
  by(auto intro: eq_\<I>_gpv.intros simp add: rel_spmf_return_spmf2 elim: eq_\<I>_gpv.cases)

context begin
interpretation CIPHER: cipher "key \<eta>" "enc \<eta>" "dec \<eta>" for \<eta> . 
interpretation S_CHAN: sec_channel .

lemma one_time_pad:
  defines "\<I>_real \<equiv> \<lambda>\<eta>. \<I>_uniform UNIV (insert None (Some ` nlists UNIV \<eta>))"
    and "\<I>_ideal \<equiv> \<lambda>\<eta>. \<I>_uniform UNIV {None, Some \<eta>}"
    and "\<I>_common \<equiv> \<lambda>\<eta>. \<I>_uniform (nlists UNIV \<eta>) UNIV \<oplus>\<^sub>\<I> \<I>_uniform UNIV (insert None (Some ` nlists UNIV \<eta>))"
  shows
    "constructive_security2 CIPHER.res (\<lambda>_. S_CHAN.res) (\<lambda>_. CNV sim None)
     \<I>_real \<I>_ideal \<I>_common (\<lambda>_. \<infinity>) False (\<lambda>_. auth_sec_wiring)"
proof
  let ?\<I>_key = "\<lambda>\<eta>. \<I>_uniform UNIV (nlists UNIV \<eta>)"
  let ?\<I>_enc = "\<lambda>\<eta>. \<I>_uniform (nlists UNIV \<eta>) UNIV"
  let ?\<I>_dec = "\<lambda>\<eta>. \<I>_uniform UNIV (insert None (Some ` nlists UNIV \<eta>))"
  have i1 [WT_intro]: "\<I>_uniform (nlists UNIV \<eta>) UNIV, ?\<I>_key \<eta> \<oplus>\<^sub>\<I> ?\<I>_enc \<eta> \<turnstile>\<^sub>C CIPHER.enc \<eta> \<surd>" for \<eta> 
    unfolding CIPHER.enc_def by(rule WT_converter_of_callee)(auto simp add: stateless_callee_def enc_def in_nlists_UNIV)
  have i2 [WT_intro]: "?\<I>_dec \<eta>, ?\<I>_key \<eta> \<oplus>\<^sub>\<I> ?\<I>_dec \<eta> \<turnstile>\<^sub>C CIPHER.dec \<eta> \<surd>" for \<eta>
    unfolding CIPHER.dec_def by(rule WT_converter_of_callee)(auto simp add: stateless_callee_def dec_def in_nlists_UNIV)
  have [WT_intro]: "\<I>_common \<eta>, (?\<I>_key \<eta> \<oplus>\<^sub>\<I> ?\<I>_enc \<eta>) \<oplus>\<^sub>\<I> (?\<I>_key \<eta> \<oplus>\<^sub>\<I> ?\<I>_dec \<eta>) \<turnstile>\<^sub>C CIPHER.enc \<eta> |\<^sub>= CIPHER.dec \<eta> \<surd>" for \<eta>
    unfolding \<I>_common_def by(rule WT_intro)+
  have key: "callee_invariant_on (CIPHER.KEY.key_oracle \<eta> \<oplus>\<^sub>O CIPHER.KEY.key_oracle \<eta>) (pred_option (\<lambda>x. length x = \<eta>))
     (?\<I>_key \<eta> \<oplus>\<^sub>\<I> ?\<I>_key \<eta>)" for \<eta>
    apply unfold_locales
    subgoal for s x y s' by(cases s; cases x)(auto simp add: option.pred_set, simp_all add: key_def in_nlists_UNIV)
    subgoal for s by(cases s)(auto intro!: WT_calleeI, simp_all add: key_def in_nlists_UNIV)
    done
  have i3: "?\<I>_key \<eta> \<oplus>\<^sub>\<I> ?\<I>_key \<eta> \<turnstile>res CIPHER.KEY.res \<eta> \<surd>" for \<eta> 
    unfolding CIPHER.KEY.res_def by(rule callee_invariant_on.WT_resource_of_oracle[OF key]) simp 
  let ?I = "\<lambda>\<eta>. pred_cstate (\<lambda>x. length x = \<eta>)"
  have WT_auth: "\<I>_real \<eta> \<turnstile>c CIPHER.AUTH.auth_oracle s \<surd>" if "?I \<eta> s" for \<eta> s
    apply(rule WT_calleeI)
    subgoal for x y s' using that
      by(cases "(s, x)" rule: CIPHER.AUTH.auth_oracle.cases)(auto simp add: \<I>_real_def in_nlists_UNIV intro!: imageI)
    done
  have WT_recv: "?\<I>_dec \<eta> \<turnstile>c S_CHAN.recv_oracle s \<surd>" if "pred_cstate (\<lambda>x. length x = \<eta>) s" for \<eta> s
    using that by(cases s)(auto intro!: WT_calleeI simp add: in_nlists_UNIV)
  have WT_send: "?\<I>_enc \<eta> \<turnstile>c S_CHAN.send_oracle s \<surd>" for \<eta> s
    by(rule WT_calleeI)(auto)
  have *: "callee_invariant_on (CIPHER.AUTH.auth_oracle \<oplus>\<^sub>O S_CHAN.send_oracle \<oplus>\<^sub>O S_CHAN.recv_oracle) (?I \<eta>)
     (\<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>)" for \<eta>
    apply unfold_locales
    subgoal for s x y s'
      by(cases x; cases "(s, projl x)" rule: CIPHER.AUTH.auth_oracle.cases; cases "projr x")(auto simp add: \<I>_common_def in_nlists_UNIV)
    subgoal by(auto simp add: \<I>_common_def WT_auth WT_recv intro: WT_calleeI)
    done
  have i4 [unfolded \<I>_common_def, WT_intro]: "\<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>res CIPHER.AUTH.res \<surd>" for \<eta> 
    unfolding CIPHER.AUTH.res_def by(rule callee_invariant_on.WT_resource_of_oracle[OF *]) simp
  show cipher: "\<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>res CIPHER.res \<eta> \<surd>" for \<eta>
    unfolding CIPHER.res_def by(rule WT_intro i3)+

  show secure: "\<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>res S_CHAN.res \<surd>" for \<eta>
  proof -
    have[simp]:"\<I>_ideal \<eta> \<turnstile>c S_CHAN.sec_oracle s \<surd>" if "?I \<eta> s" for s 
    proof (cases rule: WT_calleeI, goal_cases)
      case (1 call ret s')
      then show ?case using that by (cases "(s, call)" rule: S_CHAN.sec_oracle.cases) (simp_all add: \<I>_ideal_def)
    qed
    have[simp]: "\<I>_common \<eta> \<turnstile>c (S_CHAN.send_oracle \<oplus>\<^sub>O S_CHAN.recv_oracle) s \<surd>" 
      if "pred_cstate (\<lambda>x. length x = \<eta>) s" for s 
      unfolding \<I>_common_def by(rule WT_plus_oracleI WT_send WT_recv that)+

    have *: "callee_invariant_on (S_CHAN.sec_oracle \<oplus>\<^sub>O S_CHAN.send_oracle \<oplus>\<^sub>O S_CHAN.recv_oracle) (?I \<eta>) (\<I>_ideal \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>)"
      apply(unfold_locales)
      subgoal for s x y s'
        by(cases "(s, projl x)" rule: S_CHAN.sec_oracle.cases; cases "projr x")(auto simp add: \<I>_common_def in_nlists_UNIV)
      subgoal by simp
      done

    show ?thesis unfolding S_CHAN.res_def
      by(rule callee_invariant_on.WT_resource_of_oracle[OF *]) simp
  qed

  have sim [WT_intro]: "\<I>_real \<eta>, \<I>_ideal \<eta> \<turnstile>\<^sub>C CNV sim s \<surd>" if "s \<noteq> None \<longrightarrow> length (the s) = \<eta>" for s \<eta>
    using that by(coinduction arbitrary: s)(auto simp add: sim_def \<I>_ideal_def \<I>_real_def in_nlists_UNIV)
  show "\<I>_real \<eta>, \<I>_ideal \<eta> \<turnstile>\<^sub>C CNV sim None \<surd>" for \<eta> by(rule sim) simp

  { fix \<A> :: "security \<Rightarrow> (auth_query + bool list + unit, bool list option + unit + bool list option) distinguisher"
    assume WT: "\<And>\<eta>. \<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>g \<A> \<eta> \<surd>"
      and bound: "\<And>\<eta>. interaction_bounded_by (\<lambda>_. True) (\<A> \<eta>) \<infinity>"
    have "connect (\<A> \<eta>) (CNV sim None |\<^sub>= 1\<^sub>C \<rhd> S_CHAN.res) = connect (\<A> \<eta>) (CIPHER.res \<eta>)" for \<eta> 
      using _ WT
    proof(rule connect_cong_trace)
      show "(UNIV <+> nlists UNIV (id' \<eta>) <+> UNIV) \<turnstile>\<^sub>R CNV sim None |\<^sub>= 1\<^sub>C \<rhd> S_CHAN.res \<approx> CIPHER.res \<eta>"
        unfolding ideal_resource_wiring real_resource_wiring
        by(rule resources_indistinguishable)
      show "outs_gpv (\<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta>) (\<A> \<eta>) \<subseteq> UNIV <+> nlists UNIV (id' \<eta>) <+> UNIV"
        using WT[of \<eta>, THEN WT_gpv_outs_gpv]
        by(auto simp add: \<I>_real_def \<I>_common_def id'_def)
      show "\<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>res CIPHER.res \<eta> \<surd>" by(rule cipher)
      show "\<I>_real \<eta> \<oplus>\<^sub>\<I> \<I>_common \<eta> \<turnstile>res CNV sim None |\<^sub>= 1\<^sub>C \<rhd> S_CHAN.res \<surd>"
        by(rule WT_intro secure | simp)+
    qed
    then show "negligible (\<lambda>\<eta>. advantage (\<A> \<eta>) (CNV sim None |\<^sub>= 1\<^sub>C \<rhd> S_CHAN.res) (CIPHER.res \<eta>))"
      by(simp add: advantage_def)
  next
    let ?cnv = "map_converter id id auth_query_of sec_response_of 1\<^sub>C 
      :: (auth_query, nat option, auth_query, bool list option) converter"
    have [simp]: "\<I>_full, map_\<I> id (map_option length) \<I>_full \<turnstile>\<^sub>C 1\<^sub>C \<surd>"
      using WT_converter_id order_refl
      by(rule WT_converter_mono)(simp add: le_\<I>_def)
    have WT [WT_intro]: "\<I>_ideal \<eta>, \<I>_real \<eta> \<turnstile>\<^sub>C ?cnv \<surd>" for \<eta>
      by(rule WT_converter_map_converter)(auto simp add: \<I>_ideal_def \<I>_real_def intro!: WT_converter_mono[OF WT_converter_id order_refl] simp add: le_\<I>_def in_nlists_UNIV)
    with eq_\<I>_converter_reflI[OF this]
    have "wiring (\<I>_ideal \<eta>) (\<I>_real \<eta>) ?cnv auth_sec_wiring" for \<eta> ..
    moreover
    have eq: "\<I>_ideal \<eta>, \<I>_ideal \<eta> \<turnstile>\<^sub>C map_converter id (map_option length) id id (CNV sim s) \<sim> 1\<^sub>C"
      if "s \<noteq> None \<longrightarrow> length (the s) = \<eta>" for \<eta> and s :: "bool list option"
      unfolding map_converter_of_callee map_gpv_conv_map_gpv'[symmetric] using that
      by(coinduction arbitrary: s)
        (fastforce intro!: eq_\<I>_gpv_Pause simp add: \<I>_ideal_def in_nlists_UNIV eq_\<I>_gpv_Done2 gpv.map_sel eq_onp_same_args sim_def map_gpv_conv_bind[symmetric] id_def[symmetric] split!: option.split if_split_asm)
    have "\<I>_ideal \<eta>, \<I>_ideal \<eta> \<turnstile>\<^sub>C ?cnv \<odot> CNV sim None \<surd>" for \<eta> by(rule WT WT_intro)+ simp
    with _ have "wiring (\<I>_ideal \<eta>) (\<I>_ideal \<eta>) (?cnv \<odot> CNV sim None) (id, id)" for \<eta>
      by(rule wiring.intros)(auto  simp add: comp_converter_map_converter1 comp_converter_id_left eq)
    ultimately show "\<exists>cnv. \<forall>\<eta>. wiring (\<I>_ideal \<eta>) (\<I>_real \<eta>) (cnv \<eta>) auth_sec_wiring \<and>
              wiring (\<I>_ideal \<eta>) (\<I>_ideal \<eta>) (cnv \<eta> \<odot> CNV sim None) (id, id)"
      by meson
  }
qed

end

end
