(*  Title:      JinjaThreads/MM/HB_Completion.thy
    Author:     Andreas Lochbihler
*)

section \<open>Happens-before consistent completion of executions in the JMM\<close>

theory HB_Completion imports
  Non_Speculative
begin

coinductive ta_hb_consistent :: "'m prog \<Rightarrow> ('thread_id \<times> ('addr, 'thread_id) obs_event action) list \<Rightarrow> ('thread_id \<times> ('addr, 'thread_id) obs_event action) llist \<Rightarrow> bool"
for P :: "'m prog"
where
  LNil: "ta_hb_consistent P obs LNil" 
| LCons:
  "\<lbrakk> ta_hb_consistent P (obs @ [ob]) obs';
     case ob of (t, NormalAction (ReadMem ad al v))
        \<Rightarrow> (\<exists>w. w \<in> write_actions (llist_of (obs @ [ob])) \<and> (ad, al) \<in> action_loc P (llist_of (obs @ [ob])) w \<and>
               value_written P (llist_of (obs @ [ob])) w (ad, al) = v \<and>
             P,llist_of (obs @ [ob]) \<turnstile> w \<le>hb length obs \<and>
             (\<forall>w'\<in>write_actions (llist_of (obs @ [ob])). (ad, al) \<in> action_loc P (llist_of (obs @ [ob])) w' \<longrightarrow> 
                (P,llist_of (obs @ [ob]) \<turnstile> w \<le>hb w' \<and> P,llist_of (obs @ [ob]) \<turnstile> w' \<le>hb length obs \<or> 
                   is_volatile P al \<and> P,llist_of (obs @ [ob]) \<turnstile> w \<le>so w' \<and> P,llist_of (obs @ [ob]) \<turnstile> w' \<le>so length obs) \<longrightarrow> 
                w' = w))
     | _ \<Rightarrow> True \<rbrakk> 
  \<Longrightarrow> ta_hb_consistent P obs (LCons ob obs')"

inductive_simps ta_hb_consistent_LNil [simp]:
  "ta_hb_consistent P obs LNil"

inductive_simps ta_hb_consistent_LCons:
  "ta_hb_consistent P obs (LCons ob obs')"

lemma ta_hb_consistent_into_non_speculative:
  "ta_hb_consistent P obs0 obs
  \<Longrightarrow> non_speculative P (w_values P (\<lambda>_. {}) (map snd obs0)) (lmap snd obs)"
proof(coinduction arbitrary: obs0 obs)
  case (non_speculative obs0 obs)
  let ?vs = "w_values P (\<lambda>_. {}) (map snd obs0)"
  let ?CH = "\<lambda>vs obs'. \<exists>obs0 obs. vs = w_values P (\<lambda>_. {}) (map snd obs0) \<and> obs' = lmap snd obs \<and> ta_hb_consistent P obs0 obs"
  from non_speculative show ?case
  proof(cases)
    case LNil hence ?LNil by simp
    thus ?thesis ..
  next
    case (LCons tob obs'')
    note obs = \<open>obs = LCons tob obs''\<close>
    obtain t ob where tob: "tob = (t, ob)" by(cases tob)
    from \<open>ta_hb_consistent P (obs0 @ [tob]) obs''\<close> tob obs
    have "?CH (w_value P ?vs ob) (lmap snd obs'')" by(auto intro!: exI)
    moreover {
      fix ad al v
      assume ob: "ob = NormalAction (ReadMem ad al v)"
      with LCons tob obtain w where w: "w \<in> write_actions (llist_of (obs0 @ [tob]))"
        and adal: "(ad, al) \<in> action_loc P (llist_of (obs0 @ [tob])) w"
        and v: "value_written P (llist_of (obs0 @ [tob])) w (ad, al) = v" by auto
      from w obtain "is_write_action (action_obs (llist_of (obs0 @ [tob])) w)" 
        and w_actions: "w \<in> actions (llist_of (obs0 @ [tob]))" by cases
      hence "v \<in> ?vs (ad, al)"
      proof(cases)
        case (WriteMem ad' al' v')
        hence "NormalAction (WriteMem ad al v) \<in> set (map snd obs0)"
          using adal ob tob v w_actions unfolding in_set_conv_nth
          by(auto simp add: action_obs_def nth_append value_written.simps actions_def cong: conj_cong split: if_split_asm)
        thus ?thesis by(rule w_values_WriteMemD)
      next
        case (NewHeapElem ad' hT)
        hence "NormalAction (NewHeapElem ad hT) \<in> set (map snd obs0)"
          using adal ob tob v w_actions unfolding in_set_conv_nth
          by(auto simp add: action_obs_def nth_append value_written.simps actions_def cong: conj_cong split: if_split_asm)
        thus ?thesis using NewHeapElem adal unfolding v[symmetric]
          by(fastforce simp add: value_written.simps intro!: w_values_new_actionD intro: rev_image_eqI)
      qed }
    hence "case ob of NormalAction (ReadMem ad al v) \<Rightarrow> v \<in> ?vs (ad, al) | _ \<Rightarrow> True"
      by(simp split: action.split obs_event.split)
    ultimately have ?LCons using obs tob by simp
    thus ?thesis ..
  qed
qed

lemma ta_hb_consistent_lappendI:
  assumes hb1: "ta_hb_consistent P E E'"
  and hb2: "ta_hb_consistent P (E @ list_of E') E''"
  and fin: "lfinite E'"
  shows "ta_hb_consistent P E (lappend E' E'')"
using fin hb1 hb2
proof(induction arbitrary: E)
  case lfinite_LNil thus ?case by simp
next
  case (lfinite_LConsI E' tob)
  from \<open>ta_hb_consistent P E (LCons tob E')\<close>
  have "ta_hb_consistent P (E @ [tob]) E'" by cases
  moreover from \<open>ta_hb_consistent P (E @ list_of (LCons tob E')) E''\<close> \<open>lfinite E'\<close>
  have "ta_hb_consistent P ((E @ [tob]) @ list_of E') E''" by simp
  ultimately have "ta_hb_consistent P (E @ [tob]) (lappend E' E'')" by(rule lfinite_LConsI.IH)
  thus ?case unfolding lappend_code apply(rule ta_hb_consistent.LCons)
    using \<open>ta_hb_consistent P E (LCons tob E')\<close>
    by cases (simp split: prod.split_asm action.split_asm obs_event.split_asm)
qed

lemma ta_hb_consistent_coinduct_append
  [consumes 1, case_names ta_hb_consistent, case_conclusion ta_hb_consistent LNil lappend]:
  assumes major: "X E tobs"
  and step: "\<And>E tobs. X E tobs 
    \<Longrightarrow> tobs = LNil \<or>
       (\<exists>tobs' tobs''. tobs = lappend tobs' tobs'' \<and> tobs' \<noteq> LNil \<and> ta_hb_consistent P E tobs' \<and>
                    (lfinite tobs' \<longrightarrow> (X (E @ list_of tobs') tobs''\<or> 
                                       ta_hb_consistent P (E @ list_of tobs') tobs'')))"
    (is "\<And>E tobs. _ \<Longrightarrow> _ \<or> ?step E tobs")
  shows "ta_hb_consistent P E tobs"
proof -
  from major
  have "\<exists>tobs' tobs''. tobs = lappend (llist_of tobs') tobs'' \<and> ta_hb_consistent P E (llist_of tobs') \<and> 
                     X (E @ tobs') tobs''"
    by(auto intro: exI[where x="[]"])
  thus ?thesis
  proof(coinduct)
    case (ta_hb_consistent E tobs)
    then obtain tobs' tobs'' 
      where tobs: "tobs = lappend (llist_of tobs') tobs''"
      and hb_tobs': "ta_hb_consistent P E (llist_of tobs')"
      and X: "X (E @ tobs') tobs''" by blast

    show ?case
    proof(cases tobs')
      case Nil
      with X have "X E tobs''" by simp
      from step[OF this] show ?thesis
      proof
        assume "tobs'' = LNil" 
        with Nil tobs show ?thesis by simp
      next
        assume "?step E tobs''"
        then obtain tobs''' tobs'''' 
          where tobs'': "tobs'' = lappend tobs''' tobs''''" and "tobs''' \<noteq> LNil"
          and sc_obs''': "ta_hb_consistent P E tobs'''" 
          and fin: "lfinite tobs''' \<Longrightarrow> X (E @ list_of tobs''') tobs'''' \<or>
                                      ta_hb_consistent P (E @ list_of tobs''') tobs''''"
          by blast
        from \<open>tobs''' \<noteq> LNil\<close> obtain t ob tobs''''' where tobs''': "tobs''' = LCons (t, ob) tobs'''''"
          unfolding neq_LNil_conv by auto
        with Nil tobs'' tobs have concl1: "tobs = LCons (t, ob) (lappend tobs''''' tobs'''')" by simp
        
        have ?LCons
        proof(cases "lfinite tobs'''")
          case False
          hence "lappend tobs''''' tobs'''' = tobs'''''" using tobs''' by(simp add: lappend_inf)
          hence "ta_hb_consistent P (E @ [(t, ob)]) (lappend tobs''''' tobs'''')" 
            using sc_obs''' tobs''' by(simp add: ta_hb_consistent_LCons)
          with concl1 show ?LCons apply(simp)
            using sc_obs'''[unfolded tobs'''] by cases simp
        next
          case True
          with tobs''' obtain tobs'''''' where tobs''''': "tobs''''' = llist_of tobs''''''"
            by simp(auto simp add: lfinite_eq_range_llist_of)
          from fin[OF True] 
          have "ta_hb_consistent P (E @ [(t, ob)]) (llist_of tobs'''''') \<and> X (E @ (t, ob) # tobs'''''') tobs'''' \<or> 
                ta_hb_consistent P (E @ [(t, ob)]) (lappend (llist_of tobs'''''') tobs'''')"
          proof
            assume X: "X (E @ list_of tobs''') tobs''''"
            hence "X (E @ (t, ob) # tobs'''''') tobs''''" using tobs''''' tobs''' by simp
            moreover have "ta_hb_consistent P (E @ [(t, ob)]) (llist_of tobs'''''')"
              using sc_obs''' tobs''' tobs''''' by(simp add: ta_hb_consistent_LCons)
            ultimately show ?thesis by simp
          next
            assume "ta_hb_consistent P (E @ list_of tobs''') tobs''''"
            with sc_obs''' tobs''''' tobs'''
            have "ta_hb_consistent P (E @ [(t, ob)]) (lappend (llist_of tobs'''''') tobs'''')"
              by(simp add: ta_hb_consistent_LCons ta_hb_consistent_lappendI)
            thus ?thesis ..
          qed
          hence "((\<exists>tobs' tobs''. lappend (llist_of tobs'''''') tobs'''' = lappend (llist_of tobs') tobs'' \<and>
                                  ta_hb_consistent P (E @ [(t, ob)]) (llist_of tobs') \<and> X (E @ (t, ob) # tobs') tobs'') \<or>
                 ta_hb_consistent P (E @ [(t, ob)]) (lappend (llist_of tobs'''''') tobs''''))"
            by auto
          thus "?LCons" using concl1 tobs''''' apply(simp)
            using sc_obs'''[unfolded tobs'''] by cases simp
        qed
        thus ?thesis ..
      qed
    next
      case (Cons tob tobs''')
      with X tobs hb_tobs' show ?thesis by(auto simp add: ta_hb_consistent_LCons)
    qed
  qed
qed

lemma ta_hb_consistent_coinduct_append_wf
  [consumes 2, case_names ta_hb_consistent, case_conclusion ta_hb_consistent LNil lappend]:
  assumes major: "X E obs a"
  and wf: "wf R"
  and step: "\<And>E obs a. X E obs a
    \<Longrightarrow> obs = LNil \<or>
       (\<exists>obs' obs'' a'. obs = lappend obs' obs'' \<and> ta_hb_consistent P E obs' \<and> (obs' = LNil \<longrightarrow> (a', a) \<in> R) \<and>
                        (lfinite obs' \<longrightarrow> X (E @ list_of obs') obs'' a' \<or>
                                          ta_hb_consistent P (E @ list_of obs') obs''))"
    (is "\<And>E obs a. _ \<Longrightarrow> _ \<or> ?step E obs a")
  shows "ta_hb_consistent P E obs"
proof -
  { fix E obs a
    assume "X E obs a"
    with wf
    have "obs = LNil \<or> (\<exists>obs' obs''. obs = lappend obs' obs'' \<and> obs' \<noteq> LNil \<and> ta_hb_consistent P E obs' \<and>
          (lfinite obs' \<longrightarrow> (\<exists>a. X (E @ list_of obs') obs'' a) \<or> 
                            ta_hb_consistent P (E @ list_of obs') obs''))"
      (is "_ \<or> ?step_concl E obs")
    proof(induction a arbitrary: E obs rule: wf_induct[consumes 1, case_names wf])
      case (wf a)
      note IH = wf.IH[rule_format]
      from step[OF \<open>X E obs a\<close>]
      show ?case
      proof
        assume "obs = LNil" thus ?thesis ..
      next
        assume "?step E obs a"
        then obtain obs' obs'' a'
          where obs: "obs = lappend obs' obs''"
          and sc_obs': "ta_hb_consistent P E obs'"
          and decr: "obs' = LNil \<Longrightarrow> (a', a) \<in> R"
          and fin: "lfinite obs' \<Longrightarrow> 
                    X (E @ list_of obs') obs'' a' \<or>
                    ta_hb_consistent P (E @ list_of obs') obs''"
          by blast
        show ?case
        proof(cases "obs' = LNil")
          case True
          hence "lfinite obs'" by simp
          from fin[OF this] show ?thesis
          proof
            assume X: "X (E @ list_of obs') obs'' a'"
            from True have "(a', a) \<in> R" by(rule decr)
            from IH[OF this X] show ?thesis
            proof
              assume "obs'' = LNil"
              with True obs have "obs = LNil" by simp
              thus ?thesis ..
            next
              assume "?step_concl (E @ list_of obs') obs''"
              hence "?step_concl E obs" using True obs by simp
              thus ?thesis ..
            qed
          next
            assume "ta_hb_consistent P (E @ list_of obs') obs''"
            thus ?thesis using obs True
              by cases (auto 4 3 cong: action.case_cong obs_event.case_cong intro: exI[where x="LCons x LNil" for x] simp add: ta_hb_consistent_LCons)
          qed
        next
          case False
          with obs sc_obs' fin show ?thesis by auto
        qed
      qed
    qed }
  note step' = this

  from major show ?thesis
  proof(coinduction arbitrary: E obs a rule: ta_hb_consistent_coinduct_append)
    case (ta_hb_consistent E obs)
    thus ?case by simp(rule step')
  qed
qed

lemma ta_hb_consistent_lappendD2:
  assumes hb: "ta_hb_consistent P E (lappend E' E'')"
  and fin: "lfinite E'"
  shows "ta_hb_consistent P (E @ list_of E') E''"
using fin hb
by(induct arbitrary: E)(fastforce simp add: ta_hb_consistent_LCons)+

lemma ta_hb_consistent_Read_hb:
  fixes E E' defines "E'' \<equiv> lappend (llist_of E') E"
  assumes hb: "ta_hb_consistent P E' E"
  and tsa: "thread_start_actions_ok E''"
  and E'': "is_write_seen P (llist_of E') ws'"
  and new_actions_for_fun: 
  "\<And>w w' adal. \<lbrakk> w \<in> new_actions_for P E'' adal; 
                 w' \<in> new_actions_for P E'' adal \<rbrakk> \<Longrightarrow> w = w'"
  shows "\<exists>ws. P \<turnstile> (E'', ws) \<surd> \<and> (\<forall>n. n \<in> read_actions E'' \<longrightarrow> length E' \<le> n \<longrightarrow> P,E'' \<turnstile> ws n \<le>hb n) \<and> 
              (\<forall>n. n < length E' \<longrightarrow> ws n = ws' n)"
proof(intro exI conjI strip)
  let ?P = 
    "\<lambda>n w. case lnth E'' n of
        (t, NormalAction (ReadMem ad al v)) \<Rightarrow> 
          (w \<in> write_actions E'' \<and> (ad, al) \<in> action_loc P E'' w \<and> value_written P E'' w (ad, al) = v \<and>
          P,E'' \<turnstile> w \<le>hb n \<and> 
          (\<forall>w'\<in>write_actions E''. (ad, al) \<in> action_loc P E'' w' \<longrightarrow> 
              (P,E'' \<turnstile> w \<le>hb w' \<and> P,E'' \<turnstile> w' \<le>hb n \<or> 
               is_volatile P al \<and> P,E'' \<turnstile> w \<le>so w' \<and> P,E'' \<turnstile> w' \<le>so n) \<longrightarrow> 
              w' = w))"
  let ?ws = "\<lambda>n. if n < length E' then ws' n else Eps (?P n)"
  
  have "\<And>n. n < length E' \<Longrightarrow> ?ws n = ws' n" by simp
  moreover
  have "P \<turnstile> (E'', ?ws) \<surd> \<and> 
        (\<forall>n ad al v. n \<in> read_actions E'' \<longrightarrow> length E' \<le> n \<longrightarrow> action_obs E'' n = NormalAction (ReadMem ad al v) \<longrightarrow> P,E'' \<turnstile> ?ws n \<le>hb n)"
  proof(intro conjI wf_execI strip is_write_seenI)
    fix a' ad al v
    assume read: "a' \<in> read_actions E''" 
      and aobs: "action_obs E'' a' = NormalAction (ReadMem ad al v)"
    then obtain t where a': "enat a' < llength E''"
      and lnth'': "lnth E'' a' = (t, NormalAction (ReadMem ad al v))"
      by(cases)(cases "lnth E'' a'", clarsimp simp add: actions_def action_obs_def)

    have "?ws a' \<in> write_actions E'' \<and> 
      (ad, al) \<in> action_loc P E'' (?ws a') \<and> 
      value_written P E'' (?ws a') (ad, al) = v \<and>
      (length E' \<le> a' \<longrightarrow> P,E'' \<turnstile> ?ws a' \<le>hb a') \<and>
      \<not> P,E'' \<turnstile> a' \<le>hb ?ws a' \<and>
      (is_volatile P al \<longrightarrow> \<not> P,E'' \<turnstile> a' \<le>so ?ws a') \<and>
      (\<forall>a''. a'' \<in> write_actions E'' \<longrightarrow> (ad, al) \<in> action_loc P E'' a'' \<longrightarrow>
             (P,E'' \<turnstile> ?ws a' \<le>hb a'' \<and> P,E'' \<turnstile> a'' \<le>hb a' \<or> is_volatile P al \<and> P,E'' \<turnstile> ?ws a' \<le>so a'' \<and> P,E'' \<turnstile> a'' \<le>so a')
             \<longrightarrow> a'' = ?ws a')"
    proof(cases "a' < length E'", safe del: notI disjE conjE)
      assume a'_E': "a' < length E'"
      with read aobs have a': "a' \<in> read_actions (llist_of E')" 
        and aobs': "action_obs (llist_of E') a' = NormalAction (ReadMem ad al v)"
        by(auto simp add: E''_def action_obs_def lnth_lappend1 actions_def elim: read_actions.cases intro: read_actions.intros)
      have sim: "ltake (enat (length E')) (llist_of E') [\<approx>] ltake (enat (length E')) (lappend (llist_of E') E)"
        by(rule eq_into_sim_actions)(simp add: ltake_all ltake_lappend1)
      from tsa have tsa': "thread_start_actions_ok (llist_of E')"
        by(rule thread_start_actions_ok_prefix)(simp add: E''_def lprefix_lappend)

      from is_write_seenD[OF E'' a' aobs'] a'_E'
      show "?ws a' \<in> write_actions E''"
        and "(ad, al) \<in> action_loc P E'' (?ws a')"
        and "value_written P E'' (?ws a') (ad, al) = v"
        and "\<not> P,E'' \<turnstile> a' \<le>hb ?ws a'"
        and "is_volatile P al \<Longrightarrow> \<not> P,E'' \<turnstile> a' \<le>so ?ws a'"
        by(auto elim!: write_actions.cases intro!: write_actions.intros simp add: E''_def lnth_lappend1 actions_def action_obs_def value_written_def enat_less_enat_plusI dest: happens_before_change_prefix[OF _ tsa' sim[symmetric]] sync_order_change_prefix[OF _ sim[symmetric]])

      { assume "length E' \<le> a'"
        thus "P,E'' \<turnstile> ?ws a' \<le>hb a'" using a'_E' by simp }

      { fix w
        assume w: "w \<in> write_actions E''" "(ad, al) \<in> action_loc P E'' w" 
          and hbso: "P,E'' \<turnstile> ?ws a' \<le>hb w \<and> P,E'' \<turnstile> w \<le>hb a' \<or> is_volatile P al \<and> P,E'' \<turnstile> ?ws a' \<le>so w \<and> P,E'' \<turnstile> w \<le>so a'"
        show "w = ?ws a'"
        proof(cases "w < length E'")
          case True
          with is_write_seenD[OF E'' a' aobs'] a'_E' w hbso show ?thesis
            by(auto 4 3 elim!: write_actions.cases intro!: write_actions.intros simp add: E''_def lnth_lappend1 actions_def action_obs_def value_written_def enat_less_enat_plusI dest: happens_before_change_prefix[OF _ tsa[unfolded E''_def] sim] happens_before_change_prefix[OF _ tsa' sim[symmetric]] sync_order_change_prefix[OF _ sim, simplified] sync_order_change_prefix[OF _ sim[symmetric], simplified] bspec[where x=w])
        next
          case False
          from hbso have "E'' \<turnstile> w \<le>a a'" by(auto intro: happens_before_into_action_order elim: sync_orderE)
          moreover from w(1) read have "w \<noteq> a'" by(auto dest: read_actions_not_write_actions)
          ultimately have new_w: "is_new_action (action_obs E'' w)" using False aobs a'_E'
            by(cases rule: action_orderE) auto
          moreover from hbso a'_E' have "E'' \<turnstile> ws' a' \<le>a w"
            by(auto intro: happens_before_into_action_order elim: sync_orderE)
          hence new_a': "is_new_action (action_obs E'' (?ws a'))" using new_w a'_E'
            by(cases rule: action_orderE) auto
          ultimately have "w \<in> new_actions_for P E'' (ad, al)" "?ws a' \<in> new_actions_for P E'' (ad, al)"
            using w is_write_seenD[OF E'' a' aobs'] a'_E'
            by(auto simp add: new_actions_for_def actions_def action_obs_def lnth_lappend1 E''_def enat_less_enat_plusI elim!: write_actions.cases)
          thus ?thesis by(rule new_actions_for_fun)
        qed }
    next
      assume "\<not> a' < length E'"
      hence a'_E': "length E' \<le> a'" by simp
      define a where "a = a' - length E'"
      with a' a'_E' have a: "enat a < llength E"
        by(simp add: E''_def) (metis enat_add_mono le_add_diff_inverse plus_enat_simps(1))
      
      from a_def aobs lnth'' a'_E'
      have aobs: "action_obs E a = NormalAction (ReadMem ad al v)"
        and lnth: "lnth E a = (t, NormalAction (ReadMem ad al v))"
        by(simp_all add: E''_def lnth_lappend2 action_obs_def)
      
      define E''' where "E''' = lappend (llist_of E') (ltake (enat a) E)"
      let ?E'' = "lappend E''' (LCons (t, NormalAction (ReadMem ad al v)) LNil)"
    
      note hb also
      have E_unfold1: "E = lappend (ltake (enat a) E) (ldropn a E)" by simp
      also have E_unfold2: "ldropn a E = LCons (t, NormalAction (ReadMem ad al v)) (ldropn (Suc a) E)"
        using a lnth by (metis ldropn_Suc_conv_ldropn)
      finally
      have "ta_hb_consistent P (E' @ list_of (ltake (enat a) E))
              (LCons (t, NormalAction (ReadMem ad al v)) (ldropn (Suc a) E))"
        by(rule ta_hb_consistent_lappendD2) simp
      with a a'_E' a_def obtain w where w: "w \<in> write_actions ?E''"
        and adal_w: "(ad, al) \<in> action_loc P ?E'' w"
        and written: "value_written P ?E'' w (ad, al) = v"
        and hb: "P,?E'' \<turnstile> w \<le>hb a'"
        and in_between_so:
        "\<And>w'. \<lbrakk> w' \<in> write_actions ?E''; (ad, al) \<in> action_loc P ?E'' w'; 
                is_volatile P al; P,?E'' \<turnstile> w \<le>so w'; P,?E'' \<turnstile> w' \<le>so a' \<rbrakk>
        \<Longrightarrow> w' = w"        
        and in_between_hb: 
        "\<And>w'. \<lbrakk> w' \<in> write_actions ?E''; (ad, al) \<in> action_loc P ?E'' w'; 
                P,?E'' \<turnstile> w \<le>hb w'; P,?E'' \<turnstile> w' \<le>hb a' \<rbrakk>
        \<Longrightarrow> w' = w"
        by(auto simp add: ta_hb_consistent_LCons length_list_of_conv_the_enat min_def lnth_ltake lappend_llist_of_llist_of[symmetric] E'''_def lappend_assoc simp del: lappend_llist_of_llist_of nth_list_of split: if_splits)

      from a' a'_E' a
      have eq: "ltake (enat (Suc a')) ?E'' = ltake (enat (Suc a')) E''" (is "?lhs = ?rhs")
        unfolding E''_def E'''_def lappend_assoc
        apply(subst (2) E_unfold1)
        apply(subst E_unfold2)
        apply(subst (1 2) ltake_lappend2)
         apply(simp)
        apply(rule arg_cong) back
        apply(subst (1 2) ltake_lappend2)
         apply(simp add: min_def)
         apply (metis Suc_diff_le a_def le_Suc_eq order_le_less)
        apply(rule arg_cong) back
        apply(auto simp add: min_def a_def)
        apply(auto simp add: eSuc_enat[symmetric] zero_enat_def[symmetric])
        done
      hence sim: "?lhs [\<approx>] ?rhs" by(rule eq_into_sim_actions)
      from tsa have tsa': "thread_start_actions_ok ?E''" unfolding E''_def E'''_def lappend_assoc
        by(rule thread_start_actions_ok_prefix)(subst (2) E_unfold1, simp add: E_unfold2)

      from w a a' a_def a'_E' have w_a': "w < Suc a'"
        by cases(simp add: actions_def E'''_def min_def zero_enat_def eSuc_enat split: if_split_asm)

      from w sim have "w \<in> write_actions E''" by(rule write_actions_change_prefix)(simp add: w_a')
      moreover
      from adal_w action_loc_change_prefix[OF sim, of w P] w_a'
      have "(ad, al) \<in> action_loc P E'' w" by simp
      moreover
      from written value_written_change_prefix[OF eq, of w P] w_a'
      have "value_written P E'' w (ad, al) = v" by simp
      moreover
      from hb tsa sim have "P,E'' \<turnstile> w \<le>hb a'" by(rule happens_before_change_prefix)(simp_all add: w_a')
      moreover {
        fix w'
        assume w': "w' \<in> write_actions E''"
          and adal: "(ad, al) \<in> action_loc P E'' w'"
          and hbso: "P,E'' \<turnstile> w \<le>hb w' \<and> P,E'' \<turnstile> w' \<le>hb a' \<or> is_volatile P al \<and> P,E'' \<turnstile> w \<le>so w' \<and> P,E'' \<turnstile> w' \<le>so a'"
          (is "?hbso E''")
        from hbso have ao: "E'' \<turnstile> w \<le>a w'" "E'' \<turnstile> w' \<le>a a'"
          by(auto dest: happens_before_into_action_order elim: sync_orderE)
        have "w' = w"
        proof(cases "is_new_action (action_obs E'' w')")
          case True
          hence "w' \<in> new_actions_for P E'' (ad, al)" using w' adal by(simp add: new_actions_for_def)
          moreover from ao True have "is_new_action (action_obs E'' w)" by(cases rule: action_orderE) simp_all
          with \<open>w \<in> write_actions E''\<close> \<open>(ad, al) \<in> action_loc P E'' w\<close>
          have "w \<in> new_actions_for P E'' (ad, al)" by(simp add: new_actions_for_def)
          ultimately show "w' = w" by(rule new_actions_for_fun)
        next
          case False
          with ao have "w' \<le> a'" by(auto elim: action_orderE)
          hence w'_a: "enat w' < enat (Suc a')" by simp
          with hbso w_a' have "?hbso ?E''"
            by(auto 4 3 elim: happens_before_change_prefix[OF _ tsa' sim[symmetric]] sync_order_change_prefix[OF _ sim[symmetric]] del: disjCI intro: disjI1 disjI2)
          moreover from w' \<open>w' \<le> a'\<close> a' a lnth a'_E' have "w' \<in> write_actions ?E''"
            by(cases)(cases "w' < a'", auto intro!: write_actions.intros simp add: E'''_def actions_def action_obs_def lnth_lappend min_def zero_enat_def eSuc_enat lnth_ltake a_def E''_def not_le not_less)
          moreover from adal \<open>w' \<le> a'\<close> a a' lnth w' a'_E' have "(ad, al) \<in> action_loc P ?E'' w'"
            by(cases "w' < a'")(cases "w' < length E'", auto simp add: E'''_def action_obs_def lnth_lappend lappend_assoc[symmetric] min_def lnth_ltake less_trans[where y="enat a"] a_def E''_def lnth_ltake elim: write_actions.cases)
          ultimately show "w' = w" by(blast dest: in_between_so in_between_hb)
        qed }
      ultimately have "?P a' w" using a'_E' lnth unfolding E''_def a_def by(simp add: lnth_lappend)
      hence P: "?P a' (Eps (?P a'))" by(rule someI[where P="?P a'"])
      
      from P lnth'' a'_E'
      show "?ws a' \<in> write_actions E''" 
        and "(ad, al) \<in> action_loc P E'' (?ws a')" 
        and "value_written P E'' (?ws a') (ad, al) = v" 
        and "P,E'' \<turnstile> ?ws a' \<le>hb a'" by simp_all

      show "\<not> P,E'' \<turnstile> a' \<le>hb ?ws a'"
      proof
        assume "P,E'' \<turnstile> a' \<le>hb ?ws a'"
        with \<open>P,E'' \<turnstile> ?ws a' \<le>hb a'\<close> have "a' = ?ws a'"
          by(blast dest: antisymPD[OF antisym_action_order] happens_before_into_action_order)
        with read \<open>?ws a' \<in> write_actions E''\<close> show False
          by(auto dest: read_actions_not_write_actions)
      qed

      show "\<not> P,E'' \<turnstile> a' \<le>so ?ws a'"
      proof
        assume "P,E'' \<turnstile> a' \<le>so ?ws a'"
        hence "E'' \<turnstile> a' \<le>a ?ws a'" by(blast elim: sync_orderE)
        with \<open>P,E'' \<turnstile> ?ws a' \<le>hb a'\<close> have "a' = ?ws a'"
          by(blast dest: antisymPD[OF antisym_action_order] happens_before_into_action_order)
        with read \<open>?ws a' \<in> write_actions E''\<close> show False
          by(auto dest: read_actions_not_write_actions)
      qed
      
      fix a''
      assume "a'' \<in> write_actions E''" "(ad, al) \<in> action_loc P E'' a''"
        and "P,E'' \<turnstile> ?ws a' \<le>hb a'' \<and> P,E'' \<turnstile> a'' \<le>hb a' \<or>
             is_volatile P al \<and> P,E'' \<turnstile> ?ws a' \<le>so a'' \<and> P,E'' \<turnstile> a'' \<le>so a'"
      thus "a'' = ?ws a'" using lnth'' P a'_E' by -(erule disjE, clarsimp+)
    qed
    thus "?ws a' \<in> write_actions E''"
      and "(ad, al) \<in> action_loc P E'' (?ws a')"
      and "value_written P E'' (?ws a') (ad, al) = v"
      and "length E' \<le> a' \<Longrightarrow> P,E'' \<turnstile> ?ws a' \<le>hb a'"
      and "\<not> P,E'' \<turnstile> a' \<le>hb ?ws a'"
      and "is_volatile P al \<Longrightarrow> \<not> P,E'' \<turnstile> a' \<le>so ?ws a'"
      and "\<And>a''. \<lbrakk> a'' \<in> write_actions E''; (ad, al) \<in> action_loc P E'' a''; P,E'' \<turnstile> ?ws a' \<le>hb a''; P,E'' \<turnstile> a'' \<le>hb a' \<rbrakk> \<Longrightarrow> a'' = ?ws a'"
      and "\<And>a''. \<lbrakk> a'' \<in> write_actions E''; (ad, al) \<in> action_loc P E'' a''; is_volatile P al; P,E'' \<turnstile> ?ws a' \<le>so a''; P,E'' \<turnstile> a'' \<le>so a' \<rbrakk> \<Longrightarrow> a'' = ?ws a'"
      by blast+
  qed(assumption|rule tsa)+
  thus "P \<turnstile> (E'', ?ws) \<surd>"
    and "\<And>n. \<lbrakk> n \<in> read_actions E''; length E' \<le> n \<rbrakk> \<Longrightarrow> P,E'' \<turnstile> ?ws n \<le>hb n"
    by(blast elim: read_actions.cases intro: read_actions.intros)+
  
  fix n
  assume "n < length E'"
  thus "?ws n = ws' n" by simp
qed

lemma ta_hb_consistent_not_ReadI:
  "(\<And>t ad al v. (t, NormalAction (ReadMem ad al v)) \<notin> lset E) \<Longrightarrow> ta_hb_consistent P E' E"
proof(coinduction arbitrary: E' E)
  case (ta_hb_consistent E' E)
  thus ?case by(cases E)(auto split: action.split obs_event.split, blast)
qed

context jmm_multithreaded begin

definition complete_hb :: "('l,'thread_id,'x,'m,'w) state \<Rightarrow> ('thread_id \<times> ('addr, 'thread_id) obs_event action) list
  \<Rightarrow> ('thread_id \<times> ('l, 'thread_id, 'x, 'm, 'w, ('addr, 'thread_id) obs_event action) thread_action) llist"
where
  "complete_hb s E = unfold_llist
     (\<lambda>(s, E). \<forall>t ta s'. \<not> s -t\<triangleright>ta\<rightarrow> s')
     (\<lambda>(s, E). fst (SOME ((t, ta), s'). s -t\<triangleright>ta\<rightarrow> s' \<and> ta_hb_consistent P E (llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))))
     (\<lambda>(s, E). let ((t, ta), s') = SOME ((t, ta), s'). s -t\<triangleright>ta\<rightarrow> s' \<and> ta_hb_consistent P E (llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))
         in (s', E @ map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))
     (s, E)"

definition hb_completion ::
  "('l, 'thread_id, 'x, 'm, 'w) state \<Rightarrow> ('thread_id \<times> ('addr, 'thread_id) obs_event action) list \<Rightarrow> bool"
where
  "hb_completion s E \<longleftrightarrow>
   (\<forall>ttas s' t x ta x' m' i.
       s -\<triangleright>ttas\<rightarrow>* s' \<longrightarrow> 
       non_speculative P (w_values P (\<lambda>_. {}) (map snd E)) (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) \<longrightarrow>
       thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor> \<longrightarrow> t \<turnstile> (x, shr s') -ta\<rightarrow> (x', m') \<longrightarrow> actions_ok s' t ta \<longrightarrow>
       non_speculative P (w_values P (w_values P (\<lambda>_. {}) (map snd E)) (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (llist_of (take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) \<longrightarrow>
       (\<exists>ta' x'' m''. t \<turnstile> (x, shr s') -ta'\<rightarrow> (x'', m'') \<and> actions_ok s' t ta' \<and> 
                      take i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> = take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<and>
                      ta_hb_consistent P
                        (E @ concat (map (\<lambda>(t, ta). map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas) @ map (Pair t) (take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))
                        (llist_of (map (Pair t) (drop i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>))) \<and>
                      (i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<longrightarrow> i < length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) \<and>
                      (if \<exists>ad al v. \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NormalAction (ReadMem ad al v) then sim_action else (=)) (\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i) (\<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! i)))"

lemma hb_completionD:
  "\<lbrakk> hb_completion s E; s -\<triangleright>ttas\<rightarrow>* s';
     non_speculative P (w_values P (\<lambda>_. {}) (map snd E)) (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))); 
     thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor>; t \<turnstile> (x, shr s') -ta\<rightarrow> (x', m'); actions_ok s' t ta;
     non_speculative P (w_values P (w_values P (\<lambda>_. {}) (map snd E)) (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (llist_of (take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) \<rbrakk>
  \<Longrightarrow> \<exists>ta' x'' m''. t \<turnstile> (x, shr s') -ta'\<rightarrow> (x'', m'') \<and> actions_ok s' t ta' \<and>
                   take i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> = take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<and>
                   ta_hb_consistent P (E @ concat (map (\<lambda>(t, ta). map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas) @ map (Pair t) (take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))
                                      (llist_of (map (Pair t) (drop i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>))) \<and>
                   (i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<longrightarrow> i < length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) \<and>
                   (if \<exists>ad al v. \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NormalAction (ReadMem ad al v) then sim_action else (=)) (\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i) (\<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! i)"
unfolding hb_completion_def by blast

lemma hb_completionI [intro?]:
  "(\<And>ttas s' t x ta x' m' i. 
     \<lbrakk> s -\<triangleright>ttas\<rightarrow>* s'; non_speculative P (w_values P (\<lambda>_. {}) (map snd E)) (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)));
       thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor>; t \<turnstile> (x, shr s') -ta\<rightarrow> (x', m'); actions_ok s' t ta;
       non_speculative P (w_values P (w_values P (\<lambda>_. {}) (map snd E)) (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (llist_of (take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) \<rbrakk>
     \<Longrightarrow> \<exists>ta' x'' m''. t \<turnstile> (x, shr s') -ta'\<rightarrow> (x'', m'') \<and> actions_ok s' t ta' \<and> take i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> = take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<and>
                   ta_hb_consistent P (E @ concat (map (\<lambda>(t, ta). map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas) @ map (Pair t) (take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of (map (Pair t) (drop i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>))) \<and>
                   (i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<longrightarrow> i < length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) \<and>
                   (if \<exists>ad al v. \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NormalAction (ReadMem ad al v) then sim_action else (=)) (\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i) (\<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! i))
  \<Longrightarrow> hb_completion s E"
unfolding hb_completion_def by blast

lemma hb_completion_shift:
  assumes hb_c: "hb_completion s E"
  and \<tau>Red: "s -\<triangleright>ttas\<rightarrow>* s'"
  and sc: "non_speculative P (w_values P (\<lambda>_. {}) (map snd E)) (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
      (is "non_speculative _ ?vs _")
  shows "hb_completion s' (E @ (concat (map (\<lambda>(t, ta). map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
  (is "hb_completion _ ?E")
proof(rule hb_completionI)
  fix ttas' s'' t x ta x' m' i
  assume \<tau>Red': "s' -\<triangleright>ttas'\<rightarrow>* s''"
    and sc': "non_speculative P (w_values P (\<lambda>_. {}) (map snd ?E)) (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas')))"
    and red: "thr s'' t = \<lfloor>(x, no_wait_locks)\<rfloor>" "t \<turnstile> \<langle>x, shr s''\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>" "actions_ok s'' t ta" 
    and ns: "non_speculative P (w_values P (w_values P (\<lambda>_. {}) (map snd ?E)) (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas'))) (llist_of (take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))"
  from \<tau>Red \<tau>Red' have "s -\<triangleright>ttas @ ttas'\<rightarrow>* s''" unfolding RedT_def by(rule rtrancl3p_trans)
  moreover from sc sc' have "non_speculative P ?vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (ttas @ ttas'))))"
    unfolding map_append concat_append lappend_llist_of_llist_of[symmetric] map_concat
    by(simp add: non_speculative_lappend o_def split_def del: lappend_llist_of_llist_of)
  ultimately
  show "\<exists>ta' x'' m''. t \<turnstile> \<langle>x, shr s''\<rangle> -ta'\<rightarrow> \<langle>x'', m''\<rangle> \<and> actions_ok s'' t ta' \<and> take i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> = take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<and>
         ta_hb_consistent P (?E @ concat (map (\<lambda>(t, ta). map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas') @ map (Pair t) (take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))
                            (llist_of (map (Pair t) (drop i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>))) \<and>
         (i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<longrightarrow> i < length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) \<and>
         (if \<exists>ad al v. \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NormalAction (ReadMem ad al v) then sim_action else (=)) (\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i) (\<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! i)"
    using red ns unfolding append_assoc
    apply(subst (2) append_assoc[symmetric])
    unfolding concat_append[symmetric] map_append[symmetric] foldr_append[symmetric]
    by(rule hb_completionD[OF hb_c])(simp_all add: map_concat o_def split_def)
qed

lemma hb_completion_shift1:
  assumes hb_c: "hb_completion s E"
  and Red: "s -t\<triangleright>ta\<rightarrow> s'"
  and sc: "non_speculative P (w_values P (\<lambda>_. {}) (map snd E)) (llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
  shows "hb_completion s' (E @ map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
using hb_completion_shift[OF hb_c, of "[(t, ta)]" s'] Red sc
by(simp add: RedT_def rtrancl3p_Cons rtrancl3p_Nil del: split_paired_Ex)

lemma complete_hb_in_Runs:
  assumes hb_c: "hb_completion s E"
  and ta_hb_consistent_convert_RA: "\<And>t E ln. ta_hb_consistent P E (llist_of (map (Pair t) (convert_RA ln)))"
  shows "mthr.Runs s (complete_hb s E)"
using hb_c
proof(coinduction arbitrary: s E)
  case (Runs s E)
  let ?P = "\<lambda>((t, ta), s'). s -t\<triangleright>ta\<rightarrow> s' \<and> ta_hb_consistent P E (llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))"
  show ?case
  proof(cases "\<exists>t ta s'. s -t\<triangleright>ta\<rightarrow> s'")
    case False
    then have ?Stuck by(simp add: complete_hb_def)
    thus ?thesis ..
  next
    case True
    let ?t = "fst (fst (Eps ?P))" and ?ta = "snd (fst (Eps ?P))" and ?s' = "snd (Eps ?P)"
    from True obtain t ta s' where red: "s -t\<triangleright>ta\<rightarrow> s'" by blast
    hence "\<exists>x. ?P x"
    proof(cases)
      case (redT_normal x x' m')
      from hb_completionD[OF Runs _ _ \<open>thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>\<close> \<open>t \<turnstile> \<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>\<close> \<open>actions_ok s t ta\<close>, of "[]" 0]
      obtain ta' x'' m'' where "t \<turnstile> \<langle>x, shr s\<rangle> -ta'\<rightarrow> \<langle>x'', m''\<rangle>"
        and "actions_ok s t ta'" "ta_hb_consistent P E (llist_of (map (Pair t) \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>))" 
        by fastforce
      moreover obtain ws' where "redT_updWs t (wset s) \<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> ws'" by (metis redT_updWs_total)
      ultimately show ?thesis using \<open>thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>\<close>
        by(cases ta')(auto intro!: exI redT.redT_normal)
    next
      case (redT_acquire x n ln)
      thus ?thesis using ta_hb_consistent_convert_RA[of E t ln] 
        by(auto intro!: exI redT.redT_acquire)
    qed
    hence "?P (Eps ?P)" by(rule someI_ex)
    hence red: "s -?t\<triangleright>?ta\<rightarrow> ?s'"
      and hb: "ta_hb_consistent P E (llist_of (map (Pair ?t) \<lbrace>?ta\<rbrace>\<^bsub>o\<^esub>))"
      by(simp_all add: split_beta)
    moreover
    from ta_hb_consistent_into_non_speculative[OF hb]
    have "non_speculative P (w_values P (\<lambda>_. {}) (map snd E)) (llist_of \<lbrace>?ta\<rbrace>\<^bsub>o\<^esub>)" by(simp add: o_def)
    with Runs red have "hb_completion ?s' (E @ map (Pair ?t) \<lbrace>?ta\<rbrace>\<^bsub>o\<^esub>)" by(rule hb_completion_shift1)
    ultimately have ?Step using True
      unfolding complete_hb_def by(fastforce simp del: split_paired_Ex simp add: split_def)
    thus ?thesis ..
  qed
qed

lemma complete_hb_ta_hb_consistent:
  assumes "hb_completion s E"
  and ta_hb_consistent_convert_RA: "\<And>E t ln. ta_hb_consistent P E (llist_of (map (Pair t) (convert_RA ln)))"
  shows "ta_hb_consistent P E (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (complete_hb s E)))"
  (is "ta_hb_consistent _ _ (?obs (complete_hb s E))")
proof -
  define obs a where "obs = ?obs (complete_hb s E)" and "a = complete_hb s E"
  with \<open>hb_completion s E\<close> have "\<exists>s. hb_completion s E \<and> obs = ?obs (complete_hb s E) \<and> a = complete_hb s E" by blast
  moreover have "wf (inv_image {(m, n). m < n} (llength \<circ> ltakeWhile (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = [])))"
    (is "wf ?R") by(rule wf_inv_image)(rule wellorder_class.wf)
  ultimately show "ta_hb_consistent P E obs"
  proof(coinduct E obs a rule: ta_hb_consistent_coinduct_append_wf)
    case (ta_hb_consistent E obs a)
    then obtain s where hb_c: "hb_completion s E"
      and obs: "obs = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (complete_hb s E))"
      and a: "a = complete_hb s E"
      by blast
    let ?P = "\<lambda>((t, ta), s'). s -t\<triangleright>ta\<rightarrow> s' \<and> ta_hb_consistent P E (llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))"
    show ?case
    proof(cases "\<exists>t ta s'. s -t\<triangleright>ta\<rightarrow> s'")
      case False
      with obs have ?LNil by(simp add: complete_hb_def)
      thus ?thesis ..
    next
      case True
      let ?t = "fst (fst (Eps ?P))" and ?ta = "snd (fst (Eps ?P))" and ?s' = "snd (Eps ?P)"
      from True obtain t ta s' where red: "s -t\<triangleright>ta\<rightarrow> s'" by blast
      hence "\<exists>x. ?P x"
      proof(cases)
        case (redT_normal x x' m')
        from hb_completionD[OF hb_c _ _ \<open>thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>\<close> \<open>t \<turnstile> \<langle>x, shr s\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>\<close> \<open>actions_ok s t ta\<close>, of "[]" 0]
        obtain ta' x'' m'' where "t \<turnstile> \<langle>x, shr s\<rangle> -ta'\<rightarrow> \<langle>x'', m''\<rangle>"
          and "actions_ok s t ta'" "ta_hb_consistent P E (llist_of (map (Pair t) \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>))"
          by fastforce
        moreover obtain ws' where "redT_updWs t (wset s) \<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> ws'" by (metis redT_updWs_total)
        ultimately show ?thesis using \<open>thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>\<close>
          by(cases ta')(auto intro!: exI redT.redT_normal)
      next
        case (redT_acquire x n ln)
        thus ?thesis using ta_hb_consistent_convert_RA[of E t ln]
          by(auto intro!: exI redT.redT_acquire)
      qed
      hence "?P (Eps ?P)" by(rule someI_ex)
      hence red': "s -?t\<triangleright>?ta\<rightarrow> ?s'" 
        and hb: "ta_hb_consistent P E (llist_of (map (Pair ?t) \<lbrace>?ta\<rbrace>\<^bsub>o\<^esub>))"
        by(simp_all add: split_beta)
      moreover
      from ta_hb_consistent_into_non_speculative[OF hb]
      have "non_speculative P (w_values P (\<lambda>_. {}) (map snd E)) (llist_of \<lbrace>?ta\<rbrace>\<^bsub>o\<^esub>)" by(simp add: o_def)
      with hb_c red' have hb_c': "hb_completion ?s' (E @ map (Pair ?t) \<lbrace>?ta\<rbrace>\<^bsub>o\<^esub>)"
        by(rule hb_completion_shift1)
      show ?thesis
      proof(cases "lnull obs")
        case True thus ?thesis unfolding lnull_def by simp
      next
        case False
        have eq: "(\<forall>t ta s'. \<not> s -t\<triangleright>ta\<rightarrow> s') = False" using True by auto
        { assume "\<lbrace>?ta\<rbrace>\<^bsub>o\<^esub> = []"
          moreover from obs False
          have "lfinite (ltakeWhile (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = []) (complete_hb s E))"
            unfolding lfinite_ltakeWhile by(fastforce simp add: split_def lconcat_eq_LNil)
          ultimately have "(complete_hb ?s' (E @ map (Pair ?t) \<lbrace>?ta\<rbrace>\<^bsub>o\<^esub>), a) \<in> ?R"
            using red unfolding a complete_hb_def
            apply(subst (2) unfold_llist.code)
            apply(subst (asm) unfold_llist.code)
            apply(auto simp add: split_beta simp del: split_paired_Ex split_paired_All split: if_split_asm)
            apply(auto simp add: lfinite_eq_range_llist_of)
            done }
        hence ?lappend using red hb hb_c' unfolding obs complete_hb_def
          apply(subst unfold_llist.code)
          apply(simp add: split_beta eq del: split_paired_Ex split_paired_All split del: if_split)
          apply(intro exI conjI impI refl disjI1|rule refl|assumption|simp_all add: llist_of_eq_LNil_conv)+
          done
        thus ?thesis ..
      qed
    qed
  qed
qed

lemma hb_completion_Runs:
  assumes "hb_completion s E"
  and "\<And>E t ln. ta_hb_consistent P E (llist_of (map (Pair t) (convert_RA ln)))"
  shows "\<exists>ttas. mthr.Runs s ttas \<and> ta_hb_consistent P E (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ttas))"
using complete_hb_in_Runs[OF assms] complete_hb_ta_hb_consistent[OF assms]
by blast

end

end


