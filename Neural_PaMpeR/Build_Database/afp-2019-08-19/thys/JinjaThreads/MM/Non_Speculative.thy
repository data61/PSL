(*  Title:      JinjaThreads/MM/Non_Speculative.thy
    Author:     Andreas Lochbihler
*)

section \<open>Non-speculative prefixes of executions\<close>

theory Non_Speculative imports
  JMM_Spec
  "../Framework/FWLTS"
begin

declare addr_locsI [simp]

subsection \<open>Previously written values\<close>

fun w_value :: 
  "'m prog \<Rightarrow> (('addr \<times> addr_loc) \<Rightarrow> 'addr val set) \<Rightarrow> ('addr, 'thread_id) obs_event action
  \<Rightarrow> (('addr \<times> addr_loc) \<Rightarrow> 'addr val set)"
where
  "w_value P vs (NormalAction (WriteMem ad al v)) = vs((ad, al) := insert v (vs (ad, al)))"
| "w_value P vs (NormalAction (NewHeapElem ad hT)) =
   (\<lambda>(ad', al). if ad = ad' \<and> al \<in> addr_locs P hT
                then insert (addr_loc_default P hT al) (vs (ad, al))
                else vs (ad', al))"
| "w_value P vs _ = vs"

lemma w_value_cases:
  obtains ad al v where "x = NormalAction (WriteMem ad al v)"
  | ad hT where "x = NormalAction (NewHeapElem ad hT)"
  | ad M vs v where "x = NormalAction (ExternalCall ad M vs v)"
  | ad al v where "x = NormalAction (ReadMem ad al v)"
  | t where "x = NormalAction (ThreadStart t)"
  | t where "x = NormalAction (ThreadJoin t)"
  | ad where "x = NormalAction (SyncLock ad)"
  | ad where "x = NormalAction (SyncUnlock ad)"
  | t where "x = NormalAction (ObsInterrupt t)"
  | t where "x = NormalAction (ObsInterrupted t)"
  | "x = InitialThreadAction"
  | "x = ThreadFinishAction"
by pat_completeness

abbreviation w_values ::
  "'m prog \<Rightarrow> (('addr \<times> addr_loc) \<Rightarrow> 'addr val set) \<Rightarrow> ('addr, 'thread_id) obs_event action list
  \<Rightarrow> (('addr \<times> addr_loc) \<Rightarrow> 'addr val set)"
where "w_values P \<equiv> foldl (w_value P)"

lemma in_w_valuesD:
  assumes w: "v \<in> w_values P vs0 obs (ad, al)"
  and v: "v \<notin> vs0 (ad, al)"
  shows "\<exists>obs' wa obs''. obs = obs' @ wa # obs'' \<and> is_write_action wa \<and> (ad, al) \<in> action_loc_aux P wa \<and>
            value_written_aux P wa al = v"
  (is "?concl obs")
using w
proof(induction obs rule: rev_induct)
  case Nil thus ?case using v by simp
next
  case (snoc ob obs)
  from snoc.IH show ?case
  proof(cases "v \<in> w_values P vs0 obs (ad, al)")
    case False thus ?thesis using \<open>v \<in> w_values P vs0 (obs @ [ob]) (ad, al)\<close>
      by(cases ob rule: w_value_cases)(auto 4 4 intro: action_loc_aux_intros split: if_split_asm simp add: addr_locs_def split: htype.split_asm)
  qed fastforce
qed

lemma w_values_WriteMemD:
  assumes "NormalAction (WriteMem ad al v) \<in> set obs"
  shows "v \<in> w_values P vs0 obs (ad, al)"
using assms
apply(induct obs rule: rev_induct)
 apply simp
apply clarsimp
apply(erule disjE)
 apply clarsimp
apply clarsimp
apply(case_tac x rule: w_value_cases)
apply auto
done


lemma w_values_new_actionD:
  assumes "NormalAction (NewHeapElem ad hT) \<in> set obs" "(ad, al) \<in> action_loc_aux P (NormalAction (NewHeapElem ad hT))"
  shows "addr_loc_default P hT al \<in> w_values P vs0 obs (ad, al)"
using assms
apply(induct obs rule: rev_induct)
 apply simp
apply clarsimp
apply(rename_tac w' obs)
apply(case_tac w' rule: w_value_cases)
apply(auto simp add: split_beta)
done

lemma w_value_mono: "vs0 adal \<subseteq> w_value P vs0 ob adal"
by(cases ob rule: w_value_cases)(auto split: if_split_asm simp add: split_beta)

lemma w_values_mono: "vs0 adal \<subseteq> w_values P vs0 obs adal"
by(induct obs rule: rev_induct)(auto del: subsetI intro: w_value_mono subset_trans)

lemma w_value_greater: "vs0 \<le> w_value P vs0 ob"
by(rule le_funI)(rule w_value_mono)

lemma w_values_greater: "vs0 \<le> w_values P vs0 obs"
by(rule le_funI)(rule w_values_mono)

lemma w_values_eq_emptyD:
  assumes "w_values P vs0 obs adal = {}"
  and "w \<in> set obs" and "is_write_action w" and "adal \<in> action_loc_aux P w"
  shows False
using assms(4) assms(1-3)
apply(cases rule: action_loc_aux_cases)
apply(auto dest!: w_values_new_actionD[where ?vs0.0=vs0 and P=P] w_values_WriteMemD[where ?vs0.0=vs0 and P=P])
apply blast
done

subsection \<open>Coinductive version of non-speculative prefixes\<close>

coinductive non_speculative :: 
  "'m prog \<Rightarrow> ('addr \<times> addr_loc \<Rightarrow> 'addr val set) \<Rightarrow> ('addr, 'thread_id) obs_event action llist \<Rightarrow> bool"
for P :: "'m prog" 
where
  LNil: "non_speculative P vs LNil"
| LCons:
  "\<lbrakk> case ob of NormalAction (ReadMem ad al v) \<Rightarrow> v \<in> vs (ad, al) | _ \<Rightarrow> True;
     non_speculative P (w_value P vs ob) obs \<rbrakk> 
  \<Longrightarrow> non_speculative P vs (LCons ob obs)"

inductive_simps non_speculative_simps [simp]:
  "non_speculative P vs LNil"
  "non_speculative P vs (LCons ob obs)"

lemma non_speculative_lappend:
  assumes "lfinite obs"
  shows "non_speculative P vs (lappend obs obs') \<longleftrightarrow>
         non_speculative P vs obs \<and> non_speculative P (w_values P vs (list_of obs)) obs'"
  (is "?concl vs obs")
using assms
proof(induct arbitrary: vs)
  case lfinite_LNil thus ?case by simp
next
  case (lfinite_LConsI obs ob)
  have "?concl (w_value P vs ob) obs" by fact
  thus ?case using \<open>lfinite obs\<close> by simp
qed

lemma
  assumes "non_speculative P vs obs"
  shows non_speculative_ltake: "non_speculative P vs (ltake n obs)" (is ?thesis1)
  and non_speculative_ldrop: "non_speculative P (w_values P vs (list_of (ltake n obs))) (ldrop n obs)" (is ?thesis2)
proof -
  note assms
  also have "obs = lappend (ltake n obs) (ldrop n obs)" by(simp add: lappend_ltake_ldrop)
  finally have "?thesis1 \<and> ?thesis2"
    by(cases n)(simp_all add: non_speculative_lappend del: lappend_ltake_enat_ldropn)
  thus ?thesis1 ?thesis2 by blast+
qed

lemma non_speculative_coinduct_append [consumes 1, case_names non_speculative, case_conclusion non_speculative LNil lappend]:
  assumes major: "X vs obs"
  and step: "\<And>vs obs. X vs obs 
    \<Longrightarrow> obs = LNil \<or>
       (\<exists>obs' obs''. obs = lappend obs' obs'' \<and> obs' \<noteq> LNil \<and> non_speculative P vs obs' \<and>
                    (lfinite obs' \<longrightarrow> (X (w_values P vs (list_of obs')) obs'' \<or> 
                                       non_speculative P (w_values P vs (list_of obs')) obs'')))"
    (is "\<And>vs obs. _ \<Longrightarrow> _ \<or> ?step vs obs")
  shows "non_speculative P vs obs"
proof -
  from major
  have "\<exists>obs' obs''. obs = lappend (llist_of obs') obs'' \<and> non_speculative P vs (llist_of obs') \<and> 
                     X (w_values P vs obs') obs''"
    by(auto intro: exI[where x="[]"])
  thus ?thesis
  proof(coinduct)
    case (non_speculative vs obs)
    then obtain obs' obs'' 
      where obs: "obs = lappend (llist_of obs') obs''"
      and sc_obs': "non_speculative P vs (llist_of obs')"
      and X: "X (w_values P vs obs') obs''" by blast

    show ?case
    proof(cases obs')
      case Nil
      with X have "X vs obs''" by simp
      from step[OF this] show ?thesis
      proof
        assume "obs'' = LNil" 
        with Nil obs show ?thesis by simp
      next
        assume "?step vs obs''"
        then obtain obs''' obs'''' 
          where obs'': "obs'' = lappend obs''' obs''''" and "obs''' \<noteq> LNil"
          and sc_obs''': "non_speculative P vs obs'''" 
          and fin: "lfinite obs''' \<Longrightarrow> X (w_values P vs (list_of obs''')) obs'''' \<or>
                                      non_speculative P (w_values P vs (list_of obs''')) obs''''"
          by blast
        from \<open>obs''' \<noteq> LNil\<close> obtain ob obs''''' where obs''': "obs''' = LCons ob obs'''''"
          unfolding neq_LNil_conv by blast
        with Nil obs'' obs have concl1: "obs = LCons ob (lappend obs''''' obs'''')" by simp
        have concl2: "case ob of NormalAction (ReadMem ad al v) \<Rightarrow> v \<in> vs (ad, al) | _ \<Rightarrow> True"
          using sc_obs''' obs''' by simp

        show ?thesis
        proof(cases "lfinite obs'''")
          case False
          hence "lappend obs''''' obs'''' = obs'''''" using obs''' by(simp add: lappend_inf)
          hence "non_speculative P (w_value P vs ob) (lappend obs''''' obs'''')" 
            using sc_obs''' obs''' by simp
          with concl1 concl2 have ?LCons by blast
          thus ?thesis by simp
        next
          case True
          with obs''' obtain obs'''''' where obs''''': "obs''''' = llist_of obs''''''"
            by simp(auto simp add: lfinite_eq_range_llist_of)
          from fin[OF True] have "?LCons"
          proof
            assume X: "X (w_values P vs (list_of obs''')) obs''''"
            hence "X (w_values P (w_value P vs ob) obs'''''') obs''''"
              using obs''''' obs''' by simp
            moreover from obs'''''
            have "lappend obs''''' obs'''' = lappend (llist_of obs'''''') obs''''" by simp
            moreover have "non_speculative P (w_value P vs ob) (llist_of obs'''''')" 
              using sc_obs''' obs''' obs''''' by simp
            ultimately show ?thesis using concl1 concl2 by blast
          next
            assume "non_speculative P (w_values P vs (list_of obs''')) obs''''"
            with sc_obs''' obs''''' obs'''
            have "non_speculative P (w_value P vs ob) (lappend obs''''' obs'''')"
              by(simp add: non_speculative_lappend)
            with concl1 concl2 show ?thesis by blast
          qed
          thus ?thesis by simp
        qed
      qed
    next
      case (Cons ob obs''')
      hence "obs = LCons ob (lappend (llist_of obs''') obs'')"
        using obs by simp
      moreover from sc_obs' Cons 
      have "case ob of NormalAction (ReadMem ad al v) \<Rightarrow> v \<in> vs (ad, al) | _ \<Rightarrow> True"
        and "non_speculative P (w_value P vs ob) (llist_of obs''')" by simp_all
      moreover from X Cons have "X (w_values P (w_value P vs ob) obs''') obs''" by simp
      ultimately show ?thesis by blast
    qed
  qed
qed

lemma non_speculative_coinduct_append_wf
  [consumes 2, case_names non_speculative, case_conclusion non_speculative LNil lappend]:
  assumes major: "X vs obs a"
  and wf: "wf R"
  and step: "\<And>vs obs a. X vs obs a
    \<Longrightarrow> obs = LNil \<or>
       (\<exists>obs' obs'' a'. obs = lappend obs' obs'' \<and> non_speculative P vs obs' \<and> (obs' = LNil \<longrightarrow> (a', a) \<in> R) \<and>
                        (lfinite obs' \<longrightarrow> X (w_values P vs (list_of obs')) obs'' a' \<or>
                                          non_speculative P (w_values P vs (list_of obs')) obs''))"
    (is "\<And>vs obs a. _ \<Longrightarrow> _ \<or> ?step vs obs a")
  shows "non_speculative P vs obs"
proof -
  { fix vs obs a
    assume "X vs obs a"
    with wf
    have "obs = LNil \<or> (\<exists>obs' obs''. obs = lappend obs' obs'' \<and> obs' \<noteq> LNil \<and> non_speculative P vs obs' \<and>
          (lfinite obs' \<longrightarrow> (\<exists>a. X (w_values P vs (list_of obs')) obs'' a) \<or> 
                            non_speculative P (w_values P vs (list_of obs')) obs''))"
      (is "_ \<or> ?step_concl vs obs")
    proof(induct a arbitrary: vs obs rule: wf_induct[consumes 1, case_names wf])
      case (wf a)
      note IH = wf.hyps[rule_format]
      from step[OF \<open>X vs obs a\<close>]
      show ?case
      proof
        assume "obs = LNil" thus ?thesis ..
      next
        assume "?step vs obs a"
        then obtain obs' obs'' a'
          where obs: "obs = lappend obs' obs''"
          and sc_obs': "non_speculative P vs obs'"
          and decr: "obs' = LNil \<Longrightarrow> (a', a) \<in> R"
          and fin: "lfinite obs' \<Longrightarrow> 
                    X (w_values P vs (list_of obs')) obs'' a' \<or>
                    non_speculative P (w_values P vs (list_of obs')) obs''"
          by blast
        show ?case
        proof(cases "obs' = LNil")
          case True
          hence "lfinite obs'" by simp
          from fin[OF this] show ?thesis
          proof
            assume X: "X (w_values P vs (list_of obs')) obs'' a'"
            from True have "(a', a) \<in> R" by(rule decr)
            from IH[OF this X] show ?thesis
            proof
              assume "obs'' = LNil"
              with True obs have "obs = LNil" by simp
              thus ?thesis ..
            next
              assume "?step_concl (w_values P vs (list_of obs')) obs''"
              hence "?step_concl vs obs" using True obs by simp
              thus ?thesis ..
            qed
          next
            assume "non_speculative P (w_values P vs (list_of obs')) obs''"
            thus ?thesis using obs True
              by cases(auto cong: action.case_cong obs_event.case_cong intro: exI[where x="LCons x LNil" for x])
          qed
        next
          case False
          with obs sc_obs' fin show ?thesis by auto
        qed
      qed
    qed }
  note step' = this

  from major show ?thesis
  proof(coinduction arbitrary: vs obs a rule: non_speculative_coinduct_append)
    case (non_speculative vs obs)
    thus ?case by simp(rule step')
  qed
qed

lemma non_speculative_nthI:
  "(\<And>i ad al v. 
    \<lbrakk> enat i < llength obs; lnth obs i = NormalAction (ReadMem ad al v);
      non_speculative P vs (ltake (enat i) obs) \<rbrakk> 
    \<Longrightarrow> v \<in> w_values P vs (list_of (ltake (enat i) obs)) (ad, al))
  \<Longrightarrow> non_speculative P vs obs"
proof(coinduction arbitrary: vs obs rule: non_speculative.coinduct)
  case (non_speculative vs obs)
  hence nth:
    "\<And>i ad al v. \<lbrakk> enat i < llength obs; lnth obs i = NormalAction (ReadMem ad al v); 
                   non_speculative P vs (ltake (enat i) obs) \<rbrakk> 
    \<Longrightarrow> v \<in> w_values P vs (list_of (ltake (enat i) obs)) (ad, al)" by blast
  show ?case
  proof(cases obs)
    case LNil thus ?thesis by simp
  next
    case (LCons ob obs')
    { fix ad al v
      assume "ob = NormalAction (ReadMem ad al v)"
      with nth[of 0 ad al v] LCons
      have "v \<in> vs (ad, al)" by(simp add: zero_enat_def[symmetric]) }
    note base = this
    moreover { 
      fix i ad al v
      assume "enat i < llength obs'" "lnth obs' i = NormalAction (ReadMem ad al v)"
        and "non_speculative P (w_value P vs ob) (ltake (enat i) obs')"
      with LCons nth[of "Suc i" ad al v] base
      have "v \<in> w_values P (w_value P vs ob) (list_of (ltake (enat i) obs')) (ad, al)"
        by(clarsimp simp add: eSuc_enat[symmetric] split: obs_event.split action.split) }
    ultimately have ?LCons using LCons by(simp split: action.split obs_event.split)
    thus ?thesis ..
  qed
qed

locale executions_sc_hb =
  executions_base \<E> P
  for \<E> :: "('addr, 'thread_id) execution set"
  and P :: "'m prog" +
  assumes \<E>_new_actions_for_fun:
  "\<lbrakk> E \<in> \<E>; a \<in> new_actions_for P E adal; a' \<in> new_actions_for P E adal \<rbrakk> \<Longrightarrow> a = a'"
  and \<E>_ex_new_action:
  "\<lbrakk> E \<in> \<E>; ra \<in> read_actions E; adal \<in> action_loc P E ra; non_speculative P (\<lambda>_. {}) (ltake (enat ra) (lmap snd E)) \<rbrakk>
  \<Longrightarrow> \<exists>wa. wa \<in> new_actions_for P E adal \<and> wa < ra"
begin

lemma \<E>_new_same_addr_singleton:
  assumes E: "E \<in> \<E>"
  shows "\<exists>a. new_actions_for P E adal \<subseteq> {a}"
by(blast dest: \<E>_new_actions_for_fun[OF E])

lemma new_action_before_read:
  assumes E: "E \<in> \<E>"
  and ra: "ra \<in> read_actions E"
  and adal: "adal \<in> action_loc P E ra"
  and new: "wa \<in> new_actions_for P E adal"
  and sc: "non_speculative P (\<lambda>_. {}) (ltake (enat ra) (lmap snd E))"
  shows "wa < ra"
using \<E>_new_same_addr_singleton[OF E, of adal] \<E>_ex_new_action[OF E ra adal sc] new
by auto

lemma most_recent_write_exists:
  assumes E: "E \<in> \<E>"
  and ra: "ra \<in> read_actions E"
  and sc: "non_speculative P (\<lambda>_. {}) (ltake (enat ra) (lmap snd E))"
  shows "\<exists>wa. P,E \<turnstile> ra \<leadsto>mrw wa"
proof -
  from ra obtain ad al where
    adal: "(ad, al) \<in> action_loc P E ra"
    by(rule read_action_action_locE)

  define Q where "Q = {a. a \<in> write_actions E \<and> (ad, al) \<in> action_loc P E a \<and> E \<turnstile> a \<le>a ra}"
  let ?A = "new_actions_for P E (ad, al)"
  let ?B = "{a. a \<in> actions E \<and> (\<exists>v'. action_obs E a = NormalAction (WriteMem ad al v')) \<and> a \<le> ra}"

  have "Q \<subseteq> ?A \<union> ?B" unfolding Q_def
    by(auto elim!: write_actions.cases action_loc_aux_cases simp add: new_actions_for_def elim: action_orderE)
  moreover from \<E>_new_same_addr_singleton[OF E, of "(ad, al)"]
  have "finite ?A" by(blast intro: finite_subset)
  moreover have "finite ?B" by auto
  ultimately have finQ: "finite Q" 
    by(blast intro: finite_subset)

  from \<E>_ex_new_action[OF E ra adal sc] ra obtain wa 
    where wa: "wa \<in> Q" unfolding Q_def
    by(fastforce elim!: new_actionsE is_new_action.cases read_actions.cases intro: write_actionsI action_orderI)
   
  define wa' where "wa' = Max_torder (action_order E) Q"

  from wa have "Q \<noteq> {}" "Q \<subseteq> actions E" by(auto simp add: Q_def)
  with finQ have "wa' \<in> Q" unfolding wa'_def
    by(rule Max_torder_in_set[OF torder_action_order])
  hence "E \<turnstile> wa' \<le>a ra" "wa' \<in> write_actions E"
    and "(ad, al) \<in> action_loc P E wa'" by(simp_all add: Q_def)
  with ra adal have "P,E \<turnstile> ra \<leadsto>mrw wa'"
  proof
    fix wa''
    assume wa'': "wa'' \<in> write_actions E" "(ad, al) \<in> action_loc P E wa''"
    from \<open>wa'' \<in> write_actions E\<close> ra
    have "ra \<noteq> wa''" by(auto dest: read_actions_not_write_actions)
    show "E \<turnstile> wa'' \<le>a wa' \<or> E \<turnstile> ra \<le>a wa''"
    proof(rule disjCI)
      assume "\<not> E \<turnstile> ra \<le>a wa''"
      with total_onPD[OF total_action_order, of ra E wa''] 
        \<open>ra \<noteq> wa''\<close> \<open>ra \<in> read_actions E\<close> \<open>wa'' \<in> write_actions E\<close>
      have "E \<turnstile> wa'' \<le>a ra" by simp
      with wa'' have "wa'' \<in> Q" by(simp add: Q_def)
      with finQ show "E \<turnstile> wa'' \<le>a wa'"
        using \<open>Q \<subseteq> actions E\<close> unfolding wa'_def
        by(rule Max_torder_above[OF torder_action_order])
    qed
  qed
  thus ?thesis ..
qed

lemma mrw_before:
  assumes E: "E \<in> \<E>"
  and mrw: "P,E \<turnstile> r \<leadsto>mrw w"
  and sc: "non_speculative P (\<lambda>_. {}) (ltake (enat r) (lmap snd E))"
  shows "w < r"
using mrw read_actions_not_write_actions[of r E]
apply cases
apply(erule action_orderE)
 apply(erule (1) new_action_before_read[OF E])
  apply(simp add: new_actions_for_def)
 apply(rule sc)
apply(cases "w = r")
apply auto
done

lemma sequentially_consistent_most_recent_write_for:
  assumes E: "E \<in> \<E>"
  and sc: "non_speculative P (\<lambda>_. {}) (lmap snd E)"
  shows "sequentially_consistent P (E, \<lambda>r. THE w. P,E \<turnstile> r \<leadsto>mrw w)"
proof(rule sequentially_consistentI)
  fix r
  assume r: "r \<in> read_actions E"
  from sc have sc': "non_speculative P (\<lambda>_. {}) (ltake (enat r) (lmap snd E))"
    by(rule non_speculative_ltake)
  from most_recent_write_exists[OF E r this]
  obtain w where "P,E \<turnstile> r \<leadsto>mrw w" ..
  thus "P,E \<turnstile> r \<leadsto>mrw THE w. P,E \<turnstile> r \<leadsto>mrw w"
    by(simp add: THE_most_recent_writeI)
qed

end

locale jmm_multithreaded = multithreaded_base +
  constrains final :: "'x \<Rightarrow> bool" 
  and r :: "('l, 'thread_id, 'x, 'm, 'w, ('addr, 'thread_id) obs_event action) semantics" 
  and convert_RA :: "'l released_locks \<Rightarrow> ('addr, 'thread_id) obs_event action list" 
  fixes P :: "'md prog"

end
