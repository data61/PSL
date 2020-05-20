(*  Title:      JinjaThreads/MM/JMM_DRF.thy
    Author:     Andreas Lochbihler
*)

section \<open>The data race free guarantee of the JMM\<close>

theory JMM_DRF
imports
  JMM_Spec
begin

context drf begin

lemma drf_lemma:
  assumes wf: "P \<turnstile> (E, ws) \<surd>"
  and E: "E \<in> \<E>"
  and sync: "correctly_synchronized P \<E>"
  and read_before: "\<And>r. r \<in> read_actions E \<Longrightarrow> P,E \<turnstile> ws r \<le>hb r"
  shows "sequentially_consistent P (E, ws)"
proof(rule ccontr)
  let ?Q = "{r. r \<in> read_actions E \<and> \<not> P,E \<turnstile> r \<leadsto>mrw ws r}"

  assume "\<not> ?thesis"
  then obtain r where "r \<in> read_actions E" "\<not> P,E \<turnstile> r \<leadsto>mrw ws r"
    by(auto simp add: sequentially_consistent_def)
  hence "r \<in> ?Q" by simp
  with wf_action_order[of E] obtain r' 
    where "r' \<in> ?Q"  
    and "(action_order E)\<^sup>\<noteq>\<^sup>\<noteq>^** r' r"
    and r'_min: "\<And>a. (action_order E)\<^sup>\<noteq>\<^sup>\<noteq> a r' \<Longrightarrow> a \<notin> ?Q"
    by(rule wfP_minimalE) blast
  from \<open>r' \<in> ?Q\<close> have r': "r' \<in> read_actions E"
    and not_mrw: "\<not> P,E \<turnstile> r' \<leadsto>mrw ws r'" by blast+

  from r' obtain ad al v where obs_r': "action_obs E r' = NormalAction (ReadMem ad al v)"
    by(cases) auto
  from wf have ws: "is_write_seen P E ws" 
    and tsa_ok: "thread_start_actions_ok E" 
    by(rule wf_exec_is_write_seenD wf_exec_thread_start_actions_okD)+
  from is_write_seenD[OF ws r' obs_r']
  have ws_r: "ws r' \<in> write_actions E"
    and adal: "(ad, al) \<in> action_loc P E (ws r')"
    and v: "v = value_written P E (ws r') (ad, al)"
    and not_hb: "\<not> P,E \<turnstile> r' \<le>hb ws r'" by auto
  from r' have "P,E \<turnstile> ws r' \<le>hb r'" by(rule read_before)
  hence "E \<turnstile> ws r' \<le>a r'" by(rule happens_before_into_action_order)
  from not_mrw
  have "\<exists>w'. w' \<in> write_actions E \<and> (ad, al) \<in> action_loc P E w' \<and> 
      \<not> P,E \<turnstile> w' \<le>hb ws r' \<and> \<not> P,E \<turnstile> w' \<le>so ws r' \<and> 
      \<not> P,E \<turnstile> r' \<le>hb w' \<and> \<not> P,E \<turnstile> r' \<le>so w' \<and> E \<turnstile> w' \<le>a r'"
  proof(rule contrapos_np)
    assume inbetween: "\<not> ?thesis"
    note r'
    moreover from obs_r' have "(ad, al) \<in> action_loc P E r'" by simp
    moreover note \<open>E \<turnstile> ws r' \<le>a r'\<close> ws_r adal
    moreover
    { fix w'
      assume "w' \<in> write_actions E" "(ad, al) \<in> action_loc P E w'"
      with inbetween have "P,E \<turnstile> w' \<le>hb ws r' \<or> P,E \<turnstile> w' \<le>so ws r' \<or> P,E \<turnstile> r' \<le>hb w' \<or> P,E \<turnstile> r' \<le>so w' \<or> \<not> E \<turnstile> w' \<le>a r'" by simp
      moreover from total_onPD[OF total_action_order, of w' E r'] \<open>w' \<in> write_actions E\<close> r'
      have "E \<turnstile> w' \<le>a r' \<or> E \<turnstile> r' \<le>a w'" by(auto dest: read_actions_not_write_actions)
      ultimately have "E \<turnstile> w' \<le>a ws r' \<or> E \<turnstile> r' \<le>a w'" unfolding sync_order_def
        by(blast intro: happens_before_into_action_order) }
    ultimately show "P,E \<turnstile> r' \<leadsto>mrw ws r'" by(rule most_recent_write_for.intros)
  qed
  then obtain w' where w': "w' \<in> write_actions E"
    and adal_w': "(ad, al) \<in> action_loc P E w'"
    and "\<not> P,E \<turnstile> w' \<le>hb ws r'" "\<not> P,E \<turnstile> r' \<le>hb w'" "E \<turnstile> w' \<le>a r'" 
    and so: "\<not> P,E \<turnstile> w' \<le>so ws r'" "\<not> P,E \<turnstile> r' \<le>so w'" by blast

  have "ws r' \<noteq> w'" using \<open>\<not> P,E \<turnstile> w' \<le>hb ws r'\<close> ws_r
    by(auto intro: happens_before_refl)

  have vol: "\<not> is_volatile P al"
  proof
    assume vol_al: "is_volatile P al"
    with r' obs_r' have "r' \<in> sactions P E" by cases(rule sactionsI, simp_all)
    moreover from w' vol_al adal_w' have "w' \<in> sactions P E" 
      by(cases)(auto intro: sactionsI elim!: is_write_action.cases)
    ultimately have "P,E \<turnstile> w' \<le>so r' \<or> w' = r' \<or> P,E \<turnstile> r' \<le>so w'"
      using total_sync_order[of P E] by(blast dest: total_onPD)
    moreover have "w' \<noteq> r'" using w' r' by(auto dest: read_actions_not_write_actions)
    ultimately have "P,E \<turnstile> w' \<le>so r'" using \<open>\<not> P,E \<turnstile> r' \<le>so w'\<close> by simp
    moreover from ws_r vol_al adal have "ws r' \<in> sactions P E" 
      by(cases)(auto intro: sactionsI elim!: is_write_action.cases)
    with total_sync_order[of P E] \<open>w' \<in> sactions P E\<close> \<open>\<not> P,E \<turnstile> w' \<le>so ws r'\<close> \<open>ws r' \<noteq> w'\<close>
    have "P,E \<turnstile> ws r' \<le>so w'" by(blast dest: total_onPD)
    ultimately show False
      using is_write_seenD[OF ws r' obs_r'] w' adal_w' vol_al \<open>ws r' \<noteq> w'\<close> by auto
  qed

  { fix a
    assume "a < r'" and "a \<in> read_actions E"
    hence "(action_order E)\<^sup>\<noteq>\<^sup>\<noteq> a r'" using r' obs_r' by(auto intro: action_orderI)
    from r'_min[OF this] \<open>a \<in> read_actions E\<close>
    have "P,E \<turnstile> a \<leadsto>mrw ws a" by simp }

  from \<E>_sequential_completion[OF E wf this, of r'] r'
  obtain E' ws' where "E' \<in> \<E>" "P \<turnstile> (E', ws') \<surd>"
    and eq: "ltake (enat r') E = ltake (enat r') E'"
    and sc': "sequentially_consistent P (E', ws')" 
    and r'': "action_tid E r' = action_tid E' r'" "action_obs E r' \<approx> action_obs E' r'"
    and "r' \<in> actions E'"
    by auto

  from \<open>P \<turnstile> (E', ws') \<surd>\<close> have tsa_ok': "thread_start_actions_ok E'"
    by(rule wf_exec_thread_start_actions_okD)

  from \<open>r' \<in> read_actions E\<close> have "enat r' < llength E" by(auto elim: read_actions.cases actionsE)
  moreover from \<open>r' \<in> actions E'\<close> have "enat r' < llength E'" by(auto elim: actionsE)
  ultimately have eq': "ltake (enat (Suc r')) E [\<approx>] ltake (enat (Suc r')) E'"
    using eq[THEN eq_into_sim_actions] r''
    by(auto simp add: ltake_Suc_conv_snoc_lnth sim_actions_def split_beta action_tid_def action_obs_def intro!: llist_all2_lappendI)
  from r' have r'': "r' \<in> read_actions E'"
    by(rule read_actions_change_prefix[OF _eq']) simp
  from obs_r' have "(ad, al) \<in> action_loc P E r'" by simp
  hence adal_r'': "(ad, al) \<in> action_loc P E' r'"
    by(subst (asm) action_loc_change_prefix[OF eq']) simp

  from \<open>\<not> P,E \<turnstile> w' \<le>hb ws r'\<close>
  have "\<not> is_new_action (action_obs E w')"
  proof(rule contrapos_nn)
    assume new_w': "is_new_action (action_obs E w')"
    show "P,E \<turnstile> w' \<le>hb ws r'"
    proof(cases "is_new_action (action_obs E (ws r'))")
      case True
      with adal new_w' adal_w' w' ws_r
      have "ws r' \<in> new_actions_for P E (ad, al)" "w' \<in> new_actions_for P E (ad, al)"
        by(auto simp add: new_actions_for_def)
      with \<open>E \<in> \<E>\<close> have "ws r' = w'" by(rule \<E>_new_actions_for_fun)
      thus ?thesis using w' by(auto intro: happens_before_refl)
    next
      case False
      with tsa_ok w' ws_r new_w'
      show ?thesis by(auto intro: happens_before_new_not_new)
    qed
  qed
  with \<open>E \<turnstile> w' \<le>a r'\<close> have "w' \<le> r'" by(auto elim!: action_orderE)
  moreover from w' r' have "w' \<noteq> r'" by(auto intro: read_actions_not_write_actions)
  ultimately have "w' < r'" by simp
  with w' have "w' \<in> write_actions E'"
    by(auto intro: write_actions_change_prefix[OF _ eq'])
  hence "w' \<in> actions E'" by simp

  from adal_w' \<open>w' < r'\<close>
  have "(ad, al) \<in> action_loc P E' w'"
    by(subst action_loc_change_prefix[symmetric, OF eq']) simp_all
  
  from vol \<open>r' \<in> read_actions E'\<close> \<open>w' \<in> write_actions E'\<close> \<open>(ad, al) \<in> action_loc P E' w'\<close> adal_r''
  have "P,E' \<turnstile> r' \<dagger> w'" unfolding non_volatile_conflict_def by auto
  with sync \<open>E' \<in> \<E>\<close> \<open>P \<turnstile> (E', ws') \<surd>\<close> sc' \<open>r' \<in> actions E'\<close> \<open>w' \<in> actions E'\<close>
  have hb'_r'_w': "P,E' \<turnstile> r' \<le>hb w' \<or> P,E' \<turnstile> w' \<le>hb r'"
    by(rule correctly_synchronizedD[rule_format])
  hence "P,E \<turnstile> r' \<le>hb w' \<or> P,E \<turnstile> w' \<le>hb r'" using \<open>w' < r'\<close>
    by(auto intro: happens_before_change_prefix[OF _ tsa_ok eq'[symmetric]])
  with \<open>\<not> P,E \<turnstile> r' \<le>hb w'\<close> have "P,E \<turnstile> w' \<le>hb r'" by simp
  
  have "P,E \<turnstile> ws r' \<le>hb w'"
  proof(cases "is_new_action (action_obs E (ws r'))")
    case False
    with \<open>E \<turnstile> ws r' \<le>a r'\<close> have "ws r' \<le> r'" by(auto elim!: action_orderE)
    moreover from ws_r r' have "ws r' \<noteq> r'" by(auto dest: read_actions_not_write_actions)
    ultimately have "ws r' < r'" by simp
    with ws_r have "ws r' \<in> write_actions E'"
      by(auto intro: write_actions_change_prefix[OF _ eq'])
    hence "ws r' \<in> actions E'" by simp
    
    from adal \<open>ws r' < r'\<close>
    have "(ad, al) \<in> action_loc P E' (ws r')"
      by(subst action_loc_change_prefix[symmetric, OF eq']) simp_all
    hence "P,E' \<turnstile> ws r' \<dagger> w'"
      using \<open>ws r' \<in> write_actions E'\<close> \<open>w' \<in> write_actions E'\<close> \<open>(ad, al) \<in> action_loc P E' w'\<close> vol
      unfolding non_volatile_conflict_def by auto
    with sync \<open>E' \<in> \<E>\<close> \<open>P \<turnstile> (E', ws') \<surd>\<close> sc' \<open>ws r' \<in> actions E'\<close> \<open>w' \<in> actions E'\<close>
    have "P,E' \<turnstile> ws r' \<le>hb w' \<or> P,E' \<turnstile> w' \<le>hb ws r'"
      by(rule correctly_synchronizedD[rule_format])
    thus "P,E \<turnstile> ws r' \<le>hb w'" using \<open>w' < r'\<close> \<open>ws r' < r'\<close> \<open>\<not> P,E \<turnstile> w' \<le>hb ws r'\<close>
      by(auto dest: happens_before_change_prefix[OF _ tsa_ok eq'[symmetric]])
  next
    case True 
    with tsa_ok ws_r w' \<open>\<not> is_new_action (action_obs E w')\<close>
    show "P,E \<turnstile> ws r' \<le>hb w'" by(auto intro: happens_before_new_not_new)
  qed
  moreover
  from wf have "is_write_seen P E ws" by(rule wf_exec_is_write_seenD)
  ultimately have "w' = ws r'"
    using is_write_seenD[OF \<open>is_write_seen P E ws\<close> \<open>r' \<in> read_actions E\<close> obs_r']
      \<open>w' \<in> write_actions E\<close> \<open>(ad, al) \<in> action_loc P E w'\<close> \<open>P,E \<turnstile> w' \<le>hb r'\<close>
    by auto
  with porder_happens_before[of E P] \<open>\<not> P,E \<turnstile> w' \<le>hb ws r'\<close> ws_r show False
    by(auto dest: refl_onPD[where a="ws r'"] elim!: porder_onE)
qed

lemma justified_action_committedD:
  assumes justified: "P \<turnstile> (E, ws) weakly_justified_by J"
  and a: "a \<in> actions E"
  obtains n a' where "a = action_translation (J n) a'" "a' \<in> committed (J n)"
proof(atomize_elim)
  from justified have "actions E = (\<Union>n. action_translation (J n) ` committed (J n))"
    by(simp add: is_commit_sequence_def)
  with a show "\<exists>n a'. a = action_translation (J n) a' \<and> a' \<in> committed (J n)" by auto
qed

theorem drf_weak:
  assumes sync: "correctly_synchronized P \<E>"
  and legal: "weakly_legal_execution P \<E> (E, ws)"
  shows "sequentially_consistent P (E, ws)"
using legal_wf_execD[OF legal] legal_\<E>D[OF legal] sync
proof(rule drf_lemma)
  fix r
  assume "r \<in> read_actions E"

  from legal obtain J where E: "E \<in> \<E>"
    and wf_exec: "P \<turnstile> (E, ws) \<surd>"
    and J: "P \<turnstile> (E, ws) weakly_justified_by J"
    and range_J: "range (justifying_exec \<circ> J) \<subseteq> \<E>"
    by(rule legal_executionE)

  let ?E = "\<lambda>n. justifying_exec (J n)"
    and ?ws = "\<lambda>n. justifying_ws (J n)"
    and ?C = "\<lambda>n. committed (J n)"
    and ?\<phi> = "\<lambda>n. action_translation (J n)"
  
  from \<open>r \<in> read_actions E\<close> have "r \<in> actions E" by simp
  with J obtain n r' where r: "r = action_translation (J n) r'"
    and r': "r' \<in> ?C n" by(rule justified_action_committedD)

  note \<open>r \<in> read_actions E\<close>
  moreover from J have wfan: "wf_action_translation_on (?E n) E (?C n) (?\<phi> n)"
    by(simp add: wf_action_translations_def)
  hence "action_obs (?E n) r' \<approx> action_obs E r" using r' unfolding r
    by(blast dest: wf_action_translation_on_actionD)
  moreover from J r' have "r' \<in> actions (?E n)"
    by(auto simp add: committed_subset_actions_def)
  ultimately have "r' \<in> read_actions (?E n)" unfolding r 
    by cases(auto intro: read_actions.intros)
  hence "P,E \<turnstile> ws (?\<phi> n r') \<le>hb ?\<phi> n r'" using \<open>r' \<in> ?C n\<close>
  proof(induct n arbitrary: r')
    case 0
    from J have "?C 0 = {}" by(simp add: is_commit_sequence_def)
    with 0 have False by simp
    thus ?case ..
  next
    case (Suc n r)
    note r = \<open>r \<in> read_actions (?E (Suc n))\<close>
    from J have wfan: "wf_action_translation_on (?E n) E (?C n) (?\<phi> n)"
      and wfaSn: "wf_action_translation_on (?E (Suc n)) E (?C (Suc n)) (?\<phi> (Suc n))"
      by(simp_all add: wf_action_translations_def)

    from wfaSn have injSn: "inj_on (?\<phi> (Suc n)) (actions (?E (Suc n)))"
      by(rule wf_action_translation_on_inj_onD)
    from J have C_sub_A: "?C (Suc n) \<subseteq> actions (?E (Suc n))"
      by(simp add: committed_subset_actions_def)

    from J have wf: "P \<turnstile> (?E (Suc n), ?ws (Suc n)) \<surd>" by(simp add: justification_well_formed_def)
    moreover from range_J have "?E (Suc n) \<in> \<E>" by auto
    ultimately have sc: "sequentially_consistent P (?E (Suc n), ?ws (Suc n))" using sync
    proof(rule drf_lemma)
      fix r'
      assume r': "r' \<in> read_actions (?E (Suc n))"
      hence "r' \<in> actions (?E (Suc n))" by simp
      
      show "P,?E (Suc n) \<turnstile> ?ws (Suc n) r' \<le>hb r'"
      proof(cases "?\<phi> (Suc n) r' \<in> ?\<phi> n ` ?C n")
        case True
        then obtain r'' where r'': "r'' \<in> ?C n"
          and r'_r'': "?\<phi> (Suc n) r' = ?\<phi> n r''" by(auto)
        from r'' wfan have "action_tid (?E n) r'' = action_tid E (?\<phi> n r'')"
          and "action_obs (?E n) r'' \<approx> action_obs E (?\<phi> n r'')"
          by(blast dest: wf_action_translation_on_actionD)+
        moreover from J have "?\<phi> n ` ?C n \<subseteq> ?\<phi> (Suc n) ` ?C (Suc n)"
          by(simp add: is_commit_sequence_def)
        with r'' have "?\<phi> (Suc n) r' \<in> ?\<phi> (Suc n) ` ?C (Suc n)" 
          unfolding r'_r'' by auto
        hence "r' \<in> ?C (Suc n)"
          unfolding inj_on_image_mem_iff[OF injSn C_sub_A \<open>r' \<in> actions (?E (Suc n))\<close>] .
        with wfaSn have "action_tid (?E (Suc n)) r' = action_tid E (?\<phi> (Suc n) r')"
          and "action_obs (?E (Suc n)) r' \<approx> action_obs E (?\<phi> (Suc n) r')"
          by(blast dest: wf_action_translation_on_actionD)+
        ultimately have tid: "action_tid (?E n) r'' = action_tid (?E (Suc n)) r'"
          and obs: "action_obs (?E n) r'' \<approx> action_obs (?E (Suc n)) r'"
          unfolding r'_r'' by(auto intro: sim_action_trans sim_action_sym)
        
        from J have "?C n \<subseteq> actions (?E n)" by(simp add: committed_subset_actions_def)
        with r'' have "r'' \<in> actions (?E n)" by blast
        with r' obs have "r'' \<in> read_actions (?E n)"
          by cases(auto intro: read_actions.intros)
        hence hb'': "P,E \<turnstile> ws (?\<phi> n r'') \<le>hb ?\<phi> n r''"
          using \<open>r'' \<in> ?C n\<close> by(rule Suc)

        have r_conv_inv: "r' = inv_into (actions (?E (Suc n))) (?\<phi> (Suc n)) (?\<phi> n r'')"
          using \<open>r' \<in> actions (?E (Suc n))\<close> unfolding r'_r''[symmetric]
          by(simp add: inv_into_f_f[OF injSn])
        with \<open>r'' \<in> ?C n\<close> r' J \<open>r'' \<in> read_actions (?E n)\<close>
        have ws_eq[symmetric]: "?\<phi> (Suc n) (?ws (Suc n) r') = ws (?\<phi> n r'')"
          by(simp add: write_seen_committed_def Let_def)
        with r'_r''[symmetric] hb'' have "P,E \<turnstile> ?\<phi> (Suc n) (?ws (Suc n) r') \<le>hb ?\<phi> (Suc n) r'" by simp
        
        moreover

        from J r' \<open>r' \<in> committed (J (Suc n))\<close>
        have "ws (?\<phi> (Suc n) r') \<in> ?\<phi> (Suc n) ` ?C (Suc n)"
          by(rule weakly_justified_write_seen_hb_read_committed)
        then obtain w' where w': "ws (?\<phi> (Suc n) r') = ?\<phi> (Suc n) w'"
          and committed_w': "w' \<in> ?C (Suc n)" by blast
        with C_sub_A have w'_action: "w' \<in> actions (?E (Suc n))" by auto

        hence w'_def: "w' = inv_into (actions (?E (Suc n))) (?\<phi> (Suc n)) (ws (?\<phi> (Suc n) r'))"
          using injSn unfolding w' by simp

        from J r'  \<open>r' \<in> committed (J (Suc n))\<close> 
        have hb_eq: "P,E \<turnstile> ws (?\<phi> (Suc n) r') \<le>hb ?\<phi> (Suc n) r' \<longleftrightarrow> P,?E (Suc n) \<turnstile> w' \<le>hb r'"
          unfolding w'_def by(simp add: happens_before_committed_weak_def)

        from r' obtain ad al v where "action_obs (?E (Suc n)) r' = NormalAction (ReadMem ad al v)" by(cases)
        from is_write_seenD[OF wf_exec_is_write_seenD[OF wf] r' this]
        have "?ws (Suc n) r' \<in> actions (?E (Suc n))" by(auto)
        with injSn have "w' = ?ws (Suc n) r'"
          unfolding w'_def ws_eq[folded r'_r''] by(rule inv_into_f_f)
        thus ?thesis using hb'' hb_eq w'_action r'_r''[symmetric] w' injSn by simp
      next
        case False
        with J r' show ?thesis by(auto simp add: uncommitted_reads_see_hb_def)
      qed
    qed

    from r have "r \<in> actions (?E (Suc n))" by simp
    let ?w = "inv_into (actions (?E (Suc n))) (?\<phi> (Suc n)) (ws (?\<phi> (Suc n) r))"
    from J r \<open>r \<in> ?C (Suc n)\<close> have ws_rE_comm: "ws (?\<phi> (Suc n) r) \<in> ?\<phi> (Suc n) ` ?C (Suc n)"
      by(rule weakly_justified_write_seen_hb_read_committed)
    hence "?w \<in> ?C (Suc n)" using C_sub_A by(auto simp add: inv_into_f_f[OF injSn])
    with C_sub_A have w: "?w \<in> actions (?E (Suc n))" by blast

    from ws_rE_comm C_sub_A have w_eq: "?\<phi> (Suc n) ?w = ws (?\<phi> (Suc n) r)"
      by(auto simp: f_inv_into_f[where f="?\<phi> (Suc n)"])
    from r obtain ad al v
      where obsr: "action_obs (?E (Suc n)) r = NormalAction (ReadMem ad al v)" by cases
    hence adal_r: "(ad, al) \<in> action_loc P (?E (Suc n)) r" by simp
    from J wfaSn \<open>r \<in> ?C (Suc n)\<close>
    have obs_sim: "action_obs (?E (Suc n)) r \<approx> action_obs E (?\<phi> (Suc n) r)" "?\<phi> (Suc n) r \<in> actions E"
      by(auto dest: wf_action_translation_on_actionD simp add: committed_subset_actions_def is_commit_sequence_def)
    with obsr have rE: "?\<phi> (Suc n) r \<in> read_actions E" by(fastforce intro: read_actions.intros)
    from obs_sim obsr obtain v' 
      where obsrE: "action_obs E (?\<phi> (Suc n) r) = NormalAction (ReadMem ad al v')" by auto
    from wf_exec have "is_write_seen P E ws" by(rule wf_exec_is_write_seenD)
    from is_write_seenD[OF this rE obsrE]
    have "ws (?\<phi> (Suc n) r) \<in> write_actions E" 
      and "(ad, al) \<in> action_loc P E (ws (?\<phi> (Suc n) r))"
      and nhb: "\<not> P,E \<turnstile> ?\<phi> (Suc n) r \<le>hb ws (?\<phi> (Suc n) r)" 
      and vol: "is_volatile P al \<Longrightarrow> \<not> P,E \<turnstile> ?\<phi> (Suc n) r \<le>so ws (?\<phi> (Suc n) r)" by simp_all

    show ?case
    proof(cases "is_volatile P al")
      case False

      from wf_action_translation_on_actionD[OF wfaSn \<open>?w \<in> ?C (Suc n)\<close>]
      have "action_obs (?E (Suc n)) ?w \<approx> action_obs E (?\<phi> (Suc n) ?w)" by simp
      with w_eq have obs_sim_w: "action_obs (?E (Suc n)) ?w \<approx> action_obs E (ws (?\<phi> (Suc n) r))" by simp
      with \<open>ws (?\<phi> (Suc n) r) \<in> write_actions E\<close> \<open>?w \<in> actions (?E (Suc n))\<close>
      have "?w \<in> write_actions (?E (Suc n))"
        by cases(fastforce intro: write_actions.intros is_write_action.intros elim!: is_write_action.cases)
      from \<open>(ad, al) \<in> action_loc P E (ws (?\<phi> (Suc n) r))\<close> obs_sim_w 
      have "(ad, al) \<in> action_loc P (?E (Suc n)) ?w" by cases(auto intro: action_loc_aux_intros)
      with r adal_r \<open>?w \<in> write_actions (?E (Suc n))\<close> False
      have "P,?E (Suc n) \<turnstile> r \<dagger> ?w" by(auto simp add: non_volatile_conflict_def)
      with sc \<open>r \<in> actions (?E (Suc n))\<close> w
      have "P,?E (Suc n) \<turnstile> r \<le>hb ?w \<or> P,?E (Suc n) \<turnstile> ?w \<le>hb r"
        by(rule correctly_synchronizedD[rule_format, OF sync \<open>?E (Suc n) \<in> \<E>\<close> wf])
      moreover from J r \<open>r \<in> ?C (Suc n)\<close> 
      have "P,?E (Suc n) \<turnstile> ?w \<le>hb r \<longleftrightarrow> P,E \<turnstile> ws (?\<phi> (Suc n) r) \<le>hb ?\<phi> (Suc n) r"
        and "\<not> P,?E (Suc n) \<turnstile> r \<le>hb ?w"
        by(simp_all add: happens_before_committed_weak_def)
      ultimately show ?thesis by auto
    next
      case True
      with rE obsrE have "?\<phi> (Suc n) r \<in> sactions P E" by cases (auto intro: sactionsI)
      moreover from \<open>ws (?\<phi> (Suc n) r) \<in> write_actions E\<close> \<open>(ad, al) \<in> action_loc P E (ws (?\<phi> (Suc n) r))\<close> True 
      have "ws (?\<phi> (Suc n) r) \<in> sactions P E" by cases(auto intro!: sactionsI elim: is_write_action.cases)
      moreover have "?\<phi> (Suc n) r \<noteq> ws (?\<phi> (Suc n) r)"
        using \<open>ws (?\<phi> (Suc n) r) \<in> write_actions E\<close> rE by(auto dest: read_actions_not_write_actions)
      ultimately have "P,E \<turnstile> ws (?\<phi> (Suc n) r) \<le>so ?\<phi> (Suc n) r"
        using total_sync_order[of P E] vol[OF True] by(auto dest: total_onPD)
      moreover from \<open>ws (?\<phi> (Suc n) r) \<in> write_actions E\<close> \<open>(ad, al) \<in> action_loc P E (ws (?\<phi> (Suc n) r))\<close> True
      have "P \<turnstile> (action_tid E (ws (?\<phi> (Suc n) r)), action_obs E (ws (?\<phi> (Suc n) r))) \<leadsto>sw
        (action_tid E (?\<phi> (Suc n) r), action_obs E (?\<phi> (Suc n) r))"
        by cases(fastforce elim!: is_write_action.cases intro: synchronizes_with.intros addr_locsI simp add: obsrE)
      ultimately have "P,E \<turnstile> ws (?\<phi> (Suc n) r) \<le>sw ?\<phi> (Suc n) r" by(rule sync_withI)
      thus ?thesis unfolding po_sw_def by blast
    qed
  qed
  thus "P,E \<turnstile> ws r \<le>hb r" unfolding r .
qed

corollary drf:
  "\<lbrakk> correctly_synchronized P \<E>; legal_execution P \<E> (E, ws) \<rbrakk>
  \<Longrightarrow> sequentially_consistent P (E, ws)"
by(erule drf_weak)(rule legal_imp_weakly_legal_execution)

end

end
