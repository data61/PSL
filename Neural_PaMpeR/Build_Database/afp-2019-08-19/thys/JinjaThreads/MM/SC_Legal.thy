(*  Title:      JinjaThreads/MM/SC_Legal.thy
    Author:     Andreas Lochbihler
*)

section \<open>Sequentially consistent executions are legal\<close>

theory SC_Legal imports
  JMM_Spec
begin

context executions_base begin

primrec commit_for_sc :: "'m prog \<Rightarrow> ('addr, 'thread_id) execution \<times> write_seen \<Rightarrow> ('addr, 'thread_id) justification"
where
  "commit_for_sc P (E, ws) n =
   (if enat n \<le> llength E then 
      let (E', ws') = SOME (E', ws'). E' \<in> \<E> \<and> P \<turnstile> (E', ws') \<surd> \<and> enat n \<le> llength E' \<and>
                                      ltake (enat (n - 1)) E = ltake (enat (n - 1)) E' \<and> 
                                      (n > 0 \<longrightarrow> action_tid E' (n - 1) = action_tid E (n - 1) \<and> 
                                                (if n - 1 \<in> read_actions E then sim_action else (=))
                                                   (action_obs E' (n - 1)) (action_obs E (n - 1)) \<and>
                                                (\<forall>i < n - 1. i \<in> read_actions E  \<longrightarrow> ws' i = ws i)) \<and>
                                      (\<forall>r \<in> read_actions E'. n - 1 \<le> r \<longrightarrow> P,E' \<turnstile> ws' r \<le>hb r)
      in \<lparr>committed = {..<n}, justifying_exec = E', justifying_ws = ws', action_translation = id\<rparr>
    else \<lparr>committed = actions E, justifying_exec = E, justifying_ws = ws, action_translation = id\<rparr>)"

end

context sc_legal begin

lemma commit_for_sc_correct:
  assumes E: "E \<in> \<E>" 
  and wf: "P \<turnstile> (E, ws) \<surd>"
  and sc: "sequentially_consistent P (E, ws)"
  shows wf_action_translation_commit_for_sc: 
    "\<And>n. wf_action_translation E (commit_for_sc P (E, ws) n)" (is "\<And>n. ?thesis1 n")
  and commit_for_sc_in_\<E>:
    "\<And>n. justifying_exec (commit_for_sc P (E, ws) n) \<in> \<E>" (is "\<And>n. ?thesis2 n")
  and commit_for_sc_wf: 
    "\<And>n. P \<turnstile> (justifying_exec (commit_for_sc P (E, ws) n), justifying_ws (commit_for_sc P (E, ws) n)) \<surd>"
    (is "\<And>n. ?thesis3 n")
  and commit_for_sc_justification:
    "P \<turnstile> (E, ws) justified_by commit_for_sc P (E, ws)" (is ?thesis4)
proof -
  let ?\<phi> = "commit_for_sc P (E, ws)"

  note [simp] = split_beta
  from wf have tsok: "thread_start_actions_ok E" by simp

  let ?P = "\<lambda>n (E', ws'). E' \<in> \<E> \<and> P \<turnstile> (E', ws') \<surd> \<and> (enat n \<le> llength E \<longrightarrow> enat n \<le> llength E') \<and>
                         ltake (enat (n - 1)) E = ltake (enat (n - 1)) E' \<and> 
                         (n > 0 \<longrightarrow> action_tid E' (n - 1) = action_tid E (n - 1) \<and> 
                                   (if n - 1 \<in> read_actions E then sim_action else (=)) 
                                      (action_obs E' (n - 1)) (action_obs E (n - 1)) \<and>
                                   (\<forall>i < n - 1. i \<in> read_actions E  \<longrightarrow> ws' i = ws i)) \<and> 
                         (\<forall>r \<in> read_actions E'. n - 1 \<le> r \<longrightarrow> P,E' \<turnstile> ws' r \<le>hb r)"
  define E' ws' where "E' n = fst (Eps (?P n))" and "ws' n = snd (Eps (?P n))" for n
  hence [simp]: 
    "\<And>n. commit_for_sc P (E, ws) n = 
    (if enat n \<le> llength E
     then \<lparr>committed = {..<n}, justifying_exec = E' n, justifying_ws = ws' n, action_translation = id\<rparr>
     else \<lparr>committed = actions E, justifying_exec = E, justifying_ws = ws, action_translation = id\<rparr>)"
    by simp
  note [simp del] = commit_for_sc.simps

  have "(\<forall>n. ?thesis1 n) \<and> (\<forall>n. ?thesis2 n) \<and> (\<forall>n. ?thesis3 n) \<and> ?thesis4"
    unfolding is_justified_by.simps is_commit_sequence_def justification_well_formed_def committed_subset_actions_def
      happens_before_committed_def sync_order_committed_def value_written_committed_def uncommitted_reads_see_hb_def
      committed_reads_see_committed_writes_def external_actions_committed_def wf_action_translations_def
      write_seen_committed_def
  proof(intro conjI strip LetI)

    show "committed (?\<phi> 0) = {}"
      by(auto simp add: actions_def zero_enat_def[symmetric])
    show actions_E: "actions E = (\<Union>n. action_translation (?\<phi> n) ` committed (?\<phi> n))"
      by(auto simp add: actions_def less_le_trans[where y="enat n" for n] split: if_split_asm)
    hence committed_subset_E: "\<And>n. action_translation (?\<phi> n) ` committed (?\<phi> n) \<subseteq> actions E" by fastforce

    { fix n
      have "?P n (Eps (?P n))"
      proof(cases n)
        case 0
        from \<E>_hb_completion[OF E wf, of 0] have "\<exists>Ews. ?P 0 Ews"
          by(fastforce simp add: zero_enat_def[symmetric])
        thus ?thesis unfolding 0 by(rule someI_ex)
      next
        case (Suc n')
        moreover
        from sc have sc': "\<And>a. \<lbrakk> a < n'; a \<in> read_actions E \<rbrakk> \<Longrightarrow> P,E \<turnstile> a \<leadsto>mrw ws a"
          by(simp add: sequentially_consistent_def)
        from \<E>_hb_completion[OF E wf this, of n']
        obtain E' ws' where "E' \<in> \<E>" and "P \<turnstile> (E', ws') \<surd>"
          and eq: "ltake (enat n') E = ltake (enat n') E'"
          and hb: "\<forall>a\<in>read_actions E'. if a < n' then ws' a = ws a else P,E' \<turnstile> ws' a \<le>hb a"
          and n_sim: "action_tid E' n' = action_tid E n'"
            "(if n' \<in> read_actions E then sim_action else (=)) (action_obs E' n') (action_obs E n')"
          and n: "n' \<in> actions E \<Longrightarrow> n' \<in> actions E'" by blast
        moreover {
          assume "enat n \<le> llength E"
          with n Suc have "enat n \<le> llength E'"
            by(simp add: actions_def Suc_ile_eq) }
        moreover { 
          fix i
          assume "i \<in> read_actions E"
          moreover from eq have "ltake (enat n') E [\<approx>] ltake (enat n') E'"
            by(rule eq_into_sim_actions)
          moreover assume "i < n'"
          hence "enat i < enat n'" by simp
          ultimately have "i \<in> read_actions E'" by(rule read_actions_change_prefix)
          with hb[rule_format, OF this] \<open>i < n'\<close>
          have "ws' i = ws i" by simp }
        ultimately have "?P n (E', ws')" by simp
        thus ?thesis by(rule someI)
      qed }
    hence P [simplified]: "\<And>n. ?P n (E' n, ws' n)" by(simp add: E'_def ws'_def)
    {  fix n
      assume n_E: "enat n \<le> llength E"
      have "ltake (enat n) (E' n) [\<approx>] ltake (enat n) E" unfolding sim_actions_def
      proof(rule llist_all2_all_lnthI)
        show "llength (ltake (enat n) (E' n)) = llength (ltake (enat n) E)" 
          using n_E P[of n] by(clarsimp simp add: min_def)
      next
        fix n'
        assume n': "enat n' < llength (ltake (enat n) (E' n))"
        show "(\<lambda>(t, a) (t', a'). t = t' \<and> a \<approx> a') (lnth (ltake (enat n) (E' n)) n') (lnth (ltake (enat n) E) n')"
        proof(cases "n = Suc n'")
          case True
          with P[of n] show ?thesis
            by(simp add: action_tid_def action_obs_def lnth_ltake split: if_split_asm)
        next
          case False
          with n' have "n' < n - 1" by auto
          moreover from P[of n] have "lnth (ltake (enat (n - 1)) (E' n)) n' = lnth (ltake (enat (n - 1)) E) n'" by simp
          ultimately show ?thesis by(simp add: lnth_ltake)
        qed
      qed }
    note sim = this
    note len_eq = llist_all2_llengthD[OF this[unfolded sim_actions_def]]

    { fix n
      show "wf_action_translation E (?\<phi> n)"
      proof(cases "enat n \<le> llength E")
        case False thus ?thesis by(simp add: wf_action_translation_on_def)
      next
        case True
        hence "{..<n} \<subseteq> actions E"
          by(auto simp add: actions_def min_def less_le_trans[where y="enat n"] split: if_split_asm)
        moreover
        from True len_eq[OF True] have "{..<n} \<subseteq> actions (E' n)"
          by(auto simp add: actions_def min_def less_le_trans[where y="enat n"] split: if_split_asm)
        moreover {
          fix a assume "a < n"
          moreover from sim[OF True]
          have "action_tid (ltake (enat n) (E' n)) a = action_tid (ltake (enat n) E) a"
            "action_obs (ltake (enat n) (E' n)) a \<approx> action_obs (ltake (enat n) E) a"
            by(rule sim_actions_action_tidD sim_actions_action_obsD)+
          ultimately have "action_tid (E' n) a = action_tid E a" "action_obs (E' n) a \<approx> action_obs E a"
            by(simp_all add: action_tid_def action_obs_def lnth_ltake) }
        ultimately show ?thesis by(auto simp add: wf_action_translation_on_def del: subsetI)
      qed
      thus "wf_action_translation E (?\<phi> n)" . }
    note wfa = this
    
    { fix n from P E show "justifying_exec (?\<phi> n) \<in> \<E>"
        by(cases "enat n \<le> llength E") simp_all }
    note En = this

    { fix n from P wf show "P \<turnstile> (justifying_exec (?\<phi> n), justifying_ws (?\<phi> n)) \<surd>"
        by(cases "enat n \<le> llength E") simp_all
      thus "P \<turnstile> (justifying_exec (?\<phi> n), justifying_ws (?\<phi> n)) \<surd>" . }
    note wfn = this

    { fix n show "action_translation (?\<phi> n) ` committed (?\<phi> n) \<subseteq> action_translation (?\<phi> (Suc n)) ` committed (?\<phi> (Suc n))"
        by(auto simp add: actions_def less_le_trans[where y="enat n"]) (metis Suc_ile_eq order_less_imp_le) }
    note committed_subset = this

    { fix n
      from len_eq[of n] have "enat n \<le> llength E \<Longrightarrow> {..<n} \<subseteq> actions (E' n)"
        by(auto simp add: E'_def actions_def min_def less_le_trans[where y="enat n"] split: if_split_asm)
      thus "committed (?\<phi> n) \<subseteq> actions (justifying_exec (?\<phi> n))"
        by(simp add: actions_def E'_def) }
    note committed_actions = this

    fix n
    show "happens_before P (justifying_exec (?\<phi> n)) |` committed (?\<phi> n) =
          inv_imageP (happens_before P E) (action_translation (?\<phi> n)) |` committed (?\<phi> n)"
    proof(cases "enat n \<le> llength E")
      case False thus ?thesis by simp
    next
      case True thus ?thesis
      proof(safe intro!: ext)
        fix a b
        assume hb: "P,justifying_exec (?\<phi> n) \<turnstile> a \<le>hb b"
          and a: "a \<in> committed (?\<phi> n)"
          and b: "b \<in> committed (?\<phi> n)"
        from hb True have "P,E' n \<turnstile> a \<le>hb b" by(simp add: E'_def)
        moreover note tsok sim[OF True]
        moreover from a b True
        have "enat a < enat n" "enat b < enat n" by simp_all
        ultimately have "P,E \<turnstile> a \<le>hb b" by(rule happens_before_change_prefix)
        thus "P,E \<turnstile> action_translation (?\<phi> n) a \<le>hb action_translation (?\<phi> n) b" by simp
      next
        fix a b
        assume a: "a \<in> committed (?\<phi> n)"
          and b: "b \<in> committed (?\<phi> n)"
          and hb: "P,E \<turnstile> action_translation (?\<phi> n) a \<le>hb action_translation (?\<phi> n) b"
        from hb True have "P,E \<turnstile> a \<le>hb b" by simp
        moreover from wfn[of n] True have "thread_start_actions_ok (E' n)" by(simp)
        moreover from sim[OF True] have "ltake (enat n) E [\<approx>] ltake (enat n) (E' n)"
          by(rule sim_actions_sym)
        moreover from a b True have "enat a < enat n" "enat b < enat n" by simp_all
        ultimately have "P,E' n \<turnstile> a \<le>hb b" by(rule happens_before_change_prefix)
        thus "P,justifying_exec (?\<phi> n) \<turnstile> a \<le>hb b" using True by(simp add: E'_def)
      qed
    qed
  
    show "sync_order P (justifying_exec (?\<phi> n)) |` committed (?\<phi> n) =
      inv_imageP (sync_order P E) (action_translation (?\<phi> n)) |` committed (?\<phi> n)"
    proof(cases "enat n \<le> llength E")
      case False thus ?thesis by simp
    next
      case True thus ?thesis
      proof(safe intro!: ext)
        fix a b
        assume hb: "P,justifying_exec (?\<phi> n) \<turnstile> a \<le>so b"
          and a: "a \<in> committed (?\<phi> n)"
          and b: "b \<in> committed (?\<phi> n)"
        from hb True have "P,E' n \<turnstile> a \<le>so b" by(simp add: E'_def)
        moreover note sim[OF True]
        moreover from a b True
        have "enat a < enat n" "enat b < enat n" by simp_all
        ultimately have "P,E \<turnstile> a \<le>so b" by(rule sync_order_change_prefix)
        thus "P,E \<turnstile> action_translation (?\<phi> n) a \<le>so action_translation (?\<phi> n) b" by simp
      next
        fix a b
        assume a: "a \<in> committed (?\<phi> n)"
          and b: "b \<in> committed (?\<phi> n)"
          and hb: "P,E \<turnstile> action_translation (?\<phi> n) a \<le>so action_translation (?\<phi> n) b"
        from hb True have "P,E \<turnstile> a \<le>so b" by simp
        moreover from sim[OF True] have "ltake (enat n) E [\<approx>] ltake (enat n) (E' n)"
          by(rule sim_actions_sym)
        moreover from a b True have "enat a < enat n" "enat b < enat n" by simp_all
        ultimately have "P,E' n \<turnstile> a \<le>so b" by(rule sync_order_change_prefix)
        thus "P,justifying_exec (?\<phi> n) \<turnstile> a \<le>so b" using True by(simp add: E'_def)
      qed
    qed
    
    { fix w w' adal
      assume w: "w \<in> write_actions (justifying_exec (?\<phi> n)) \<inter> committed (?\<phi> n)"
        and w': "w' = action_translation (?\<phi> n) w"
        and adal: "adal \<in> action_loc P E w'"
      show "value_written P (justifying_exec (?\<phi> n)) w adal = value_written P E w' adal"
      proof(cases "enat n \<le> llength E")
        case False thus ?thesis using w' by simp
      next
        case True
        note n_E = this
        have "action_obs E w = action_obs (E' n) w"
        proof(cases "w < n - 1")
          case True
          with P[of n] w' n_E show ?thesis
            by(clarsimp simp add: action_obs_change_prefix_eq)
        next
          case False
          with w True have "w = n - 1" "n > 0" by auto
          moreover
          with True have "w \<in> actions E"
            by(simp add: actions_def)(metis Suc_ile_eq Suc_pred)
          with True w wf_action_translation_on_actionD[OF wfa, of w n] w'
          have "w' \<in> write_actions E" 
            by(auto intro!: write_actions.intros elim!: write_actions.cases is_write_action.cases)
          hence "w' \<notin> read_actions E" by(blast dest: read_actions_not_write_actions)
          ultimately show ?thesis using P[of n] w' True by clarsimp
        qed
        with True w' show ?thesis by(cases adal)(simp add: value_written.simps)
      qed }

    { fix r' r r''
      assume r': "r' \<in> read_actions (justifying_exec (commit_for_sc P (E, ws) n)) \<inter> committed (?\<phi> n)"
        and r: "r = action_translation (?\<phi> n) r'"
        and r'': "r'' = inv_into (actions (justifying_exec (?\<phi> (Suc n)))) (action_translation (?\<phi> (Suc n))) r"
      from r' r committed_subset[of n] have "r \<in> actions E"
        by(auto split: if_split_asm elim!: read_actions.cases simp add: actions_def Suc_ile_eq less_trans[where y="enat n"])
      with r' r have r_actions: "r \<in> read_actions E"
        by(fastforce dest: wf_action_translation_on_actionD[OF wfa] split: if_split_asm elim!: read_actions.cases intro: read_actions.intros)
      moreover from r' committed_subset[of n] committed_actions[of "Suc n"]
      have "r' \<in> actions (justifying_exec (?\<phi> (Suc n)))" by(auto split: if_split_asm elim: read_actions.cases)
      ultimately have "r'' = r'" using r' r r'' by(cases "enat (Suc n) \<le> llength E") simp_all
      moreover from r' have "r' < n"
        by(simp add: actions_def split: if_split_asm)(metis enat_ord_code(2) linorder_linear order_less_le_trans)
      ultimately show "action_translation (?\<phi> (Suc n)) (justifying_ws (?\<phi> (Suc n)) r'') = ws r"
        using P[of "Suc n"] r' r r_actions by(clarsimp split: if_split_asm) }

    { fix r'
      assume r': "r' \<in> read_actions (justifying_exec (?\<phi> (Suc n)))"
      show "action_translation (?\<phi> (Suc n)) r' \<in> action_translation (?\<phi> n) ` committed (?\<phi> n) \<or>
            P,justifying_exec (?\<phi> (Suc n)) \<turnstile> justifying_ws (?\<phi> (Suc n)) r' \<le>hb r'" (is "?committed \<or> ?hb")
      proof(cases "r' < n")
        case True
        hence "?committed" using r'
          by(auto elim!: actionsE split: if_split_asm dest!: read_actions_actions)(metis Suc_ile_eq linorder_not_le not_less_iff_gr_or_eq)
        thus ?thesis ..
      next
        case False
        hence "r' \<ge> n" by simp
        hence "enat (Suc n) \<le> llength E" using False r'
          by(auto split: if_split_asm dest!: read_actions_actions elim!: actionsE) (metis Suc_ile_eq enat_ord_code(2) not_le_imp_less order_less_le_trans)
        hence ?hb using P[of "Suc n"] r' \<open>r' \<ge> n\<close> by simp
        thus ?thesis ..
      qed }

    { fix r' r C_n
      assume r': "r' \<in> read_actions (justifying_exec (?\<phi> (Suc n))) \<inter> committed (?\<phi> (Suc n))"
        and r: "r = action_translation (?\<phi> (Suc n)) r'"
        and C_n: "C_n = action_translation (?\<phi> n) ` committed (?\<phi> n)"
      show "r \<in> C_n \<or> action_translation (?\<phi> (Suc n)) (justifying_ws (?\<phi> (Suc n)) r') \<in> C_n \<and> ws r \<in> C_n"
        (is "_ \<or> (?C_ws_n \<and> ?C_ws)")
      proof(cases "r \<in> C_n")
        case True thus ?thesis ..
      next
        case False
        with r' r C_n have [simp]: "r' = n" 
          apply(auto split: if_split_asm dest!: read_actions_actions elim!: actionsE)
          apply(metis enat_ord_code(1) less_SucI less_eq_Suc_le not_less_eq_eq order_trans)
          by (metis Suc_ile_eq enat_ord_code(1) leD leI linorder_cases)
        from r' have len_E: "enat (Suc n) \<le> llength E"
          by(clarsimp simp add: actions_def Suc_ile_eq split: if_split_asm)
        with r' P[of "Suc n"] have "P,justifying_exec (?\<phi> (Suc n)) \<turnstile> ws' (Suc n) r' \<le>hb r'" by(simp)
        hence "justifying_exec (?\<phi> (Suc n)) \<turnstile> ws' (Suc n) r' \<le>a r'" by(rule happens_before_into_action_order)
        moreover from r' have "r' \<in> read_actions (justifying_exec (?\<phi> (Suc n)))" by simp
        moreover then obtain ad al v where "action_obs (justifying_exec (?\<phi> (Suc n))) r' = NormalAction (ReadMem ad al v)"
          by cases auto
        with wfn[of "Suc n"] \<open>r' \<in> read_actions _\<close> len_E obtain adal 
          where "ws' (Suc n) r' \<in> write_actions (justifying_exec (?\<phi> (Suc n)))"
          and "adal \<in> action_loc P (justifying_exec (?\<phi> (Suc n))) r'"
          and "adal \<in> action_loc P (justifying_exec (?\<phi> (Suc n))) (ws' (Suc n) r')"
          by(clarsimp)(auto dest: is_write_seenD)
        moreover {
          from En[of "Suc n"] len_E have "E' (Suc n) \<in> \<E>" by simp
          moreover
          fix a assume "a \<in> read_actions (justifying_exec (?\<phi> (Suc n)))" and "a < r'"
          hence "a \<in> read_actions (E' (Suc n))" "enat a < enat (Suc n)" using len_E by simp_all
          with sim[OF len_E] have a: "a \<in> read_actions E" by -(rule read_actions_change_prefix)
          with \<open>a < r'\<close> have mrw: "P,E \<turnstile> a \<leadsto>mrw ws a" using sc by(simp add: sequentially_consistent_def)
          from P[of "Suc n"] \<open>a < r'\<close> a len_E have "ws a = ws' (Suc n) a" by simp
          with mrw have mrw': "P,E \<turnstile> a \<leadsto>mrw ws' (Suc n) a" by simp
          moreover from wfn[of "Suc n"] wf len_E have "thread_start_actions_ok (E' (Suc n))" by(simp)
          moreover note sim[OF len_E, symmetric]
          moreover from E wf mrw' have "ws' (Suc n) a < a" 
            by(rule mrw_before)(erule sequentially_consistentE[OF sc])
          with \<open>a < r'\<close> have "ws' (Suc n) a < r'" by simp
          ultimately have "P,E' (Suc n) \<turnstile> a \<leadsto>mrw ws' (Suc n) a" using \<open>a < r'\<close>
            by -(rule mrw_change_prefix, simp+)
          hence "P,justifying_exec (?\<phi> (Suc n)) \<turnstile> a \<leadsto>mrw justifying_ws (?\<phi> (Suc n)) a" using len_E by simp
        }
        ultimately have "ws' (Suc n) r' < r'" by(rule action_order_read_before_write[OF En wfn])
        with len_E C_n have "?C_ws_n" by clarsimp (metis Suc_ile_eq linorder_le_cases order_less_irrefl order_trans)
        moreover
        from r' have "r' \<in> committed (?\<phi> (Suc n))" by blast
        with r' r len_E wf_action_translation_on_actionD[OF wfa this] committed_subset_E[of "Suc n"]
        have "r \<in> read_actions E" by(fastforce elim!: read_actions.cases intro: read_actions.intros split: if_split_asm)
        with sc obtain "P,E \<turnstile> r \<leadsto>mrw ws r" by(rule sequentially_consistentE)
        with E wf have "ws r < r" by(rule mrw_before)(rule sequentially_consistentE[OF sc])
        with C_n len_E r have ?C_ws by(auto simp add: Suc_ile_eq)
        ultimately show ?thesis by simp
      qed }

    { fix a a'
      assume a: "a \<in> external_actions (justifying_exec (?\<phi> n))"
        and a': "a' \<in> committed (?\<phi> n)"
        and hb: "P,justifying_exec (?\<phi> n) \<turnstile> a \<le>hb a'"
      from hb have "justifying_exec (?\<phi> n) \<turnstile> a \<le>a a'"
        by(rule happens_before_into_action_order)
      with a have "a \<le> a'" by(auto elim!: action_orderE dest: external_actions_not_new)
      with a' a show "a \<in> committed (?\<phi> n)" by(auto elim: external_actions.cases) }
  qed
  thus "\<And>n. ?thesis1 n" "\<And>n. ?thesis2 n" "\<And>n. ?thesis3 n" "?thesis4"
    by blast+
qed

theorem SC_is_legal:
  assumes E: "E \<in> \<E>" 
  and wf: "P \<turnstile> (E, ws) \<surd>"
  and sc: "sequentially_consistent P (E, ws)"
  shows "legal_execution P \<E> (E, ws)"
using E wf
apply(rule legal_executionI)
 apply(rule commit_for_sc_correct[OF assms])
apply clarify
apply(unfold o_apply)
apply(rule commit_for_sc_in_\<E>[OF assms])
done

end

context jmm_consistent begin

theorem consistent:
  assumes "E \<in> \<E>" "P \<turnstile> (E, ws) \<surd>"
  shows "\<exists>E \<in> \<E>. \<exists>ws. legal_execution P \<E> (E, ws)"
proof -
  from \<E>_sequential_completion[OF assms, of 0]
  obtain E' ws' where "E'\<in>\<E>" "P \<turnstile> (E', ws') \<surd>" "sequentially_consistent P (E', ws')" by auto
  moreover hence "legal_execution P \<E> (E', ws')" by(rule SC_is_legal)
  ultimately show ?thesis by blast
qed

end

end
