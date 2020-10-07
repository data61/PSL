(*  Title:      JinjaThreads/MM/SC_Completion.thy
    Author:     Andreas Lochbihler
*)

section \<open>Sequentially consistent completion of executions in the JMM\<close>

theory SC_Completion 
imports
  Non_Speculative
begin

subsection \<open>Most recently written values\<close>

fun mrw_value :: 
  "'m prog \<Rightarrow> (('addr \<times> addr_loc) \<rightharpoonup> ('addr val \<times> bool)) \<Rightarrow> ('addr, 'thread_id) obs_event action
  \<Rightarrow> (('addr \<times> addr_loc) \<rightharpoonup> ('addr val \<times> bool))"
where
  "mrw_value P vs (NormalAction (WriteMem ad al v)) = vs((ad, al) \<mapsto> (v, True))"
| "mrw_value P vs (NormalAction (NewHeapElem ad hT)) =
   (\<lambda>(ad', al). if ad = ad' \<and> al \<in> addr_locs P hT \<and> (case vs (ad, al) of None \<Rightarrow> True | Some (v, b) \<Rightarrow> \<not> b)
                then Some (addr_loc_default P hT al, False)
                else vs (ad', al))"
| "mrw_value P vs _ = vs"

lemma mrw_value_cases:
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

abbreviation mrw_values ::
  "'m prog \<Rightarrow> (('addr \<times> addr_loc) \<rightharpoonup> ('addr val \<times> bool)) \<Rightarrow> ('addr, 'thread_id) obs_event action list
  \<Rightarrow> (('addr \<times> addr_loc) \<rightharpoonup> ('addr val \<times> bool))"
where "mrw_values P \<equiv> foldl (mrw_value P)"

lemma mrw_values_eq_SomeD:
  assumes mrw: "mrw_values P vs0 obs (ad, al) = \<lfloor>(v, b)\<rfloor>"
  and "vs0 (ad, al) = \<lfloor>(v, b)\<rfloor> \<Longrightarrow> \<exists>wa. wa \<in> set obs \<and> is_write_action wa \<and> (ad, al) \<in> action_loc_aux P wa \<and> (b \<longrightarrow> \<not> is_new_action wa)"
  shows "\<exists>obs' wa obs''. obs = obs' @ wa # obs'' \<and> is_write_action wa \<and> (ad, al) \<in> action_loc_aux P wa \<and>
            value_written_aux P wa al = v \<and> (is_new_action wa \<longleftrightarrow> \<not> b) \<and>
            (\<forall>ob\<in>set obs''. is_write_action ob \<longrightarrow> (ad, al) \<in> action_loc_aux P ob \<longrightarrow> is_new_action ob \<and> b)"
  (is "?concl obs")
using assms
proof(induct obs rule: rev_induct)
  case Nil thus ?case by simp
next
  case (snoc ob obs)
  note mrw = \<open>mrw_values P vs0 (obs @ [ob]) (ad, al) = \<lfloor>(v, b)\<rfloor>\<close>
  show ?case
  proof(cases "is_write_action ob \<and> (ad, al) \<in> action_loc_aux P ob \<and> (is_new_action ob \<longrightarrow> \<not> b)")
    case True thus ?thesis using mrw
      by(fastforce elim!: is_write_action.cases intro: action_loc_aux_intros split: if_split_asm)
  next
    case False
    with mrw have "mrw_values P vs0 obs (ad, al) = \<lfloor>(v, b)\<rfloor>"
      by(cases "ob" rule: mrw_value_cases)(auto split: if_split_asm simp add: addr_locs_def split: htype.split_asm)
    moreover
    { assume "vs0 (ad, al) = \<lfloor>(v, b)\<rfloor>"
      hence "\<exists>wa. wa \<in> set (obs @ [ob]) \<and> is_write_action wa \<and> (ad, al) \<in> action_loc_aux P wa \<and> (b \<longrightarrow> \<not> is_new_action wa)"
        by(rule snoc)
      with False have "\<exists>wa. wa \<in> set obs \<and> is_write_action wa \<and> (ad, al) \<in> action_loc_aux P wa \<and> (b \<longrightarrow> \<not> is_new_action wa)"
        by auto }
    ultimately have "?concl obs" by(rule snoc)
    thus ?thesis using False mrw by fastforce
  qed
qed

lemma mrw_values_WriteMemD:
  assumes "NormalAction (WriteMem ad al v') \<in> set obs"
  shows "\<exists>v. mrw_values P vs0 obs (ad, al) = Some (v, True)"
using assms
apply(induct obs rule: rev_induct)
 apply simp
apply clarsimp
apply(erule disjE)
 apply clarsimp
apply clarsimp
apply(case_tac x rule: mrw_value_cases)
apply simp_all
done

lemma mrw_values_new_actionD:
  assumes "w \<in> set obs" "is_new_action w" "adal \<in> action_loc_aux P w"
  shows "\<exists>v b. mrw_values P vs0 obs adal = Some (v, b)"
using assms
apply(induct obs rule: rev_induct)
 apply simp
apply clarsimp
apply(erule disjE)
 apply(fastforce simp add: split_beta elim!: action_loc_aux_cases is_new_action.cases)
apply clarsimp
apply(rename_tac w' obs' v b)
apply(case_tac w' rule: mrw_value_cases)
apply(auto simp add: split_beta)
done

lemma mrw_value_dom_mono:
  "dom vs \<subseteq> dom (mrw_value P vs ob)"
by(cases ob rule: mrw_value_cases) auto

lemma mrw_values_dom_mono:
  "dom vs \<subseteq> dom (mrw_values P vs obs)"
by(induct obs arbitrary: vs)(auto intro: subset_trans[OF mrw_value_dom_mono] del: subsetI)

lemma mrw_values_eq_NoneD:
  assumes "mrw_values P vs0 obs adal = None"
  and "w \<in> set obs" and "is_write_action w" and "adal \<in> action_loc_aux P w"
  shows False
using assms
apply -
apply(erule is_write_action.cases)
apply(fastforce dest: mrw_values_WriteMemD[where ?vs0.0=vs0 and P=P] mrw_values_new_actionD[where ?vs0.0=vs0] elim: action_loc_aux_cases)+
done

lemma mrw_values_mrw:
  assumes mrw: "mrw_values P vs0 (map snd obs) (ad, al) = \<lfloor>(v, b)\<rfloor>"
  and initial: "vs0 (ad, al) = \<lfloor>(v, b)\<rfloor> \<Longrightarrow> \<exists>wa. wa \<in> set (map snd obs) \<and> is_write_action wa \<and> (ad, al) \<in> action_loc_aux P wa \<and> (b \<longrightarrow> \<not> is_new_action wa)"
  shows "\<exists>i. i < length obs \<and> P,llist_of (obs @ [(t, NormalAction (ReadMem ad al v))]) \<turnstile> length obs \<leadsto>mrw i \<and> value_written P (llist_of obs) i (ad, al) = v"
proof -
  from mrw_values_eq_SomeD[OF mrw initial]
  obtain obs' wa obs'' where obs: "map snd obs = obs' @ wa # obs''"
    and wa: "is_write_action wa"
    and adal: "(ad, al) \<in> action_loc_aux P wa"
    and written: "value_written_aux P wa al = v"
    and new: "is_new_action wa \<longleftrightarrow> \<not> b"
    and last: "\<And>ob. \<lbrakk> ob \<in> set obs''; is_write_action ob; (ad, al) \<in> action_loc_aux P ob \<rbrakk> \<Longrightarrow> is_new_action ob \<and> b"
    by blast
  let ?i = "length obs'"
  let ?E = "llist_of (obs @ [(t, NormalAction (ReadMem ad al v))])"

  from obs have len: "length (map snd obs) = Suc (length obs') + length obs''" by simp
  hence "?i < length obs" by simp
  moreover
  hence obs_i: "action_obs ?E ?i = wa" using len obs
    by(auto simp add: action_obs_def map_eq_append_conv)

  have "P,?E \<turnstile> length obs \<leadsto>mrw ?i"
  proof(rule most_recent_write_for.intros)
    show "length obs \<in> read_actions ?E"
      by(auto intro: read_actions.intros simp add: actions_def action_obs_def)
    show "(ad, al) \<in> action_loc P ?E (length obs)"
      by(simp add: action_obs_def lnth_llist_of)
    show "?E \<turnstile> length obs' \<le>a length obs" using len
      by-(rule action_orderI, auto simp add: actions_def action_obs_def nth_append)
    show "?i \<in> write_actions ?E" using len obs wa
      by-(rule write_actions.intros, auto simp add: actions_def action_obs_def nth_append map_eq_append_conv)
    show "(ad, al) \<in> action_loc P ?E ?i" using obs_i adal by simp

    fix wa'
    assume wa': "wa' \<in> write_actions ?E"
      and adal': "(ad, al) \<in> action_loc P ?E wa'"
    from wa' \<open>?i \<in> write_actions ?E\<close>
    have "wa' \<in> actions ?E" "?i \<in> actions ?E" by simp_all
    hence "?E \<turnstile> wa' \<le>a ?i"
    proof(rule action_orderI)
      assume new_wa': "is_new_action (action_obs ?E wa')"
        and new_i: "is_new_action (action_obs ?E ?i)"
      from new_i obs_i new have b: "\<not> b" by simp

      show "wa' \<le> ?i"
      proof(rule ccontr)
        assume "\<not> ?thesis"
        hence "?i < wa'" by simp
        hence "snd (obs ! wa') \<in> set obs''" using obs wa' unfolding in_set_conv_nth
          by -(rule exI[where x="wa' - Suc (length obs')"], auto elim!: write_actions.cases actionsE simp add: action_obs_def lnth_llist_of actions_def nth_append map_eq_append_conv nth_Cons' split: if_split_asm)
        moreover from wa' have "is_write_action (snd (obs ! wa'))"
          by cases(auto simp add: action_obs_def nth_append actions_def split: if_split_asm)
        moreover from adal' wa' have "(ad, al) \<in> action_loc_aux P (snd (obs ! wa'))"
          by(auto simp add: action_obs_def nth_append nth_Cons' actions_def split: if_split_asm elim!: write_actions.cases)
        ultimately show False using last[of "snd (obs ! wa')"] b by simp
      qed
    next
      assume new_wa': "\<not> is_new_action (action_obs ?E wa')"
      with wa' adal' obtain v' where "NormalAction (WriteMem ad al v') \<in> set (map snd obs)"
        unfolding in_set_conv_nth
        by (fastforce elim!: write_actions.cases is_write_action.cases simp add: action_obs_def actions_def nth_append split: if_split_asm intro!: exI[where x=wa'])
      from mrw_values_WriteMemD[OF this, of P vs0] mrw have b by simp
      with new obs_i have "\<not> is_new_action (action_obs ?E ?i)" by simp
      moreover
      have "wa' \<le> ?i"
      proof(rule ccontr)
        assume "\<not> ?thesis"
        hence "?i < wa'" by simp
        hence "snd (obs ! wa') \<in> set obs''" using obs wa' unfolding in_set_conv_nth
          by -(rule exI[where x="wa' - Suc (length obs')"], auto elim!: write_actions.cases actionsE simp add: action_obs_def lnth_llist_of actions_def nth_append map_eq_append_conv nth_Cons' split: if_split_asm)
        moreover from wa' have "is_write_action (snd (obs ! wa'))"
          by cases(auto simp add: action_obs_def nth_append actions_def split: if_split_asm)
        moreover from adal' wa' have "(ad, al) \<in> action_loc_aux P (snd (obs ! wa'))"
          by(auto simp add: action_obs_def nth_append nth_Cons' actions_def split: if_split_asm elim!: write_actions.cases)
        ultimately have "is_new_action (snd (obs ! wa'))" using last[of "snd (obs ! wa')"] by simp
        moreover from new_wa' wa' have "\<not> is_new_action (snd (obs ! wa'))"
          by(auto elim!: write_actions.cases simp add: action_obs_def nth_append actions_def split: if_split_asm)
        ultimately show False by contradiction
      qed
      ultimately
      show "\<not> is_new_action (action_obs ?E ?i) \<and> wa' \<le> ?i" by blast
    qed
    thus "?E \<turnstile> wa' \<le>a ?i \<or> ?E \<turnstile> length obs \<le>a wa'" ..
  qed
  moreover from written \<open>?i < length obs\<close> obs_i
  have "value_written P (llist_of obs) ?i (ad, al) = v"
    by(simp add: value_written_def action_obs_def nth_append)
  ultimately show ?thesis by blast
qed

lemma mrw_values_no_write_unchanged:
  assumes no_write: "\<And>w. \<lbrakk> w \<in> set obs; is_write_action w; adal \<in> action_loc_aux P w \<rbrakk>
  \<Longrightarrow> case vs adal of None \<Rightarrow> False | Some (v, b) \<Rightarrow> b \<and> is_new_action w"
  shows "mrw_values P vs obs adal = vs adal"
using assms
proof(induct obs arbitrary: vs)
  case Nil show ?case by simp
next
  case (Cons ob obs)
  from Cons.prems[of ob]
  have "mrw_value P vs ob adal = vs adal"
    apply(cases adal)
    apply(cases ob rule: mrw_value_cases, fastforce+)
    apply(auto simp add: addr_locs_def split: htype.split_asm)
    apply blast+
    done
  moreover
  have "mrw_values P (mrw_value P vs ob) obs adal = mrw_value P vs ob adal"
  proof(rule Cons.hyps)
    fix w
    assume "w \<in> set obs" "is_write_action w" "adal \<in> action_loc_aux P w"
    with Cons.prems[of w] \<open>mrw_value P vs ob adal = vs adal\<close>
    show "case mrw_value P vs ob adal of None \<Rightarrow> False | \<lfloor>(v, b)\<rfloor> \<Rightarrow> b \<and> is_new_action w" by simp
  qed
  ultimately show ?case by simp
qed

subsection \<open>Coinductive version of sequentially consistent prefixes\<close>

coinductive ta_seq_consist :: 
  "'m prog \<Rightarrow> ('addr \<times> addr_loc \<rightharpoonup> 'addr val \<times> bool) \<Rightarrow> ('addr, 'thread_id) obs_event action llist \<Rightarrow> bool"
for P :: "'m prog" 
where
  LNil: "ta_seq_consist P vs LNil"
| LCons:
  "\<lbrakk> case ob of NormalAction (ReadMem ad al v) \<Rightarrow> \<exists>b. vs (ad, al) = \<lfloor>(v, b)\<rfloor> | _ \<Rightarrow> True;
     ta_seq_consist P (mrw_value P vs ob) obs \<rbrakk> 
  \<Longrightarrow> ta_seq_consist P vs (LCons ob obs)"

inductive_simps ta_seq_consist_simps [simp]:
  "ta_seq_consist P vs LNil"
  "ta_seq_consist P vs (LCons ob obs)"

lemma ta_seq_consist_lappend:
  assumes "lfinite obs"
  shows "ta_seq_consist P vs (lappend obs obs') \<longleftrightarrow>
         ta_seq_consist P vs obs \<and> ta_seq_consist P (mrw_values P vs (list_of obs)) obs'"
  (is "?concl vs obs")
using assms
proof(induct arbitrary: vs)
  case lfinite_LNil thus ?case by simp
next
  case (lfinite_LConsI obs ob)
  have "?concl (mrw_value P vs ob) obs" by fact
  thus ?case using \<open>lfinite obs\<close> by(simp split: action.split add: list_of_LCons)
qed

lemma
  assumes "ta_seq_consist P vs obs"
  shows ta_seq_consist_ltake: "ta_seq_consist P vs (ltake n obs)" (is ?thesis1)
  and ta_seq_consist_ldrop: "ta_seq_consist P (mrw_values P vs (list_of (ltake n obs))) (ldrop n obs)" (is ?thesis2)
proof -
  note assms
  also have "obs = lappend (ltake n obs) (ldrop n obs)" by(simp add: lappend_ltake_ldrop)
  finally have "?thesis1 \<and> ?thesis2"
    by(cases n)(simp_all add: ta_seq_consist_lappend del: lappend_ltake_enat_ldropn)
  thus ?thesis1 ?thesis2 by blast+
qed

lemma ta_seq_consist_coinduct_append [consumes 1, case_names ta_seq_consist, case_conclusion ta_seq_consist LNil lappend]:
  assumes major: "X vs obs"
  and step: "\<And>vs obs. X vs obs 
    \<Longrightarrow> obs = LNil \<or>
       (\<exists>obs' obs''. obs = lappend obs' obs'' \<and> obs' \<noteq> LNil \<and> ta_seq_consist P vs obs' \<and>
                    (lfinite obs' \<longrightarrow> (X (mrw_values P vs (list_of obs')) obs'' \<or> 
                                       ta_seq_consist P (mrw_values P vs (list_of obs')) obs'')))"
    (is "\<And>vs obs. _ \<Longrightarrow> _ \<or> ?step vs obs")
  shows "ta_seq_consist P vs obs"
proof -
  from major
  have "\<exists>obs' obs''. obs = lappend (llist_of obs') obs'' \<and> ta_seq_consist P vs (llist_of obs') \<and> 
                     X (mrw_values P vs obs') obs''"
    by(auto intro: exI[where x="[]"])
  thus ?thesis
  proof(coinduct)
    case (ta_seq_consist vs obs)
    then obtain obs' obs'' 
      where obs: "obs = lappend (llist_of obs') obs''"
      and sc_obs': "ta_seq_consist P vs (llist_of obs')"
      and X: "X (mrw_values P vs obs') obs''" by blast

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
          and sc_obs''': "ta_seq_consist P vs obs'''" 
          and fin: "lfinite obs''' \<Longrightarrow> X (mrw_values P vs (list_of obs''')) obs'''' \<or>
                                      ta_seq_consist P (mrw_values P vs (list_of obs''')) obs''''"
          by blast
        from \<open>obs''' \<noteq> LNil\<close> obtain ob obs''''' where obs''': "obs''' = LCons ob obs'''''"
          unfolding neq_LNil_conv by blast
        with Nil obs'' obs have concl1: "obs = LCons ob (lappend obs''''' obs'''')" by simp
        have concl2: "case ob of NormalAction (ReadMem ad al v) \<Rightarrow> \<exists>b. vs (ad, al) = \<lfloor>(v, b)\<rfloor> | _ \<Rightarrow> True"
          using sc_obs''' obs''' by simp

        show ?thesis
        proof(cases "lfinite obs'''")
          case False
          hence "lappend obs''''' obs'''' = obs'''''" using obs''' by(simp add: lappend_inf)
          hence "ta_seq_consist P (mrw_value P vs ob) (lappend obs''''' obs'''')" 
            using sc_obs''' obs''' by simp
          with concl1 concl2 have ?LCons by blast
          thus ?thesis by simp
        next
          case True
          with obs''' obtain obs'''''' where obs''''': "obs''''' = llist_of obs''''''"
            by simp(auto simp add: lfinite_eq_range_llist_of)
          from fin[OF True] have "?LCons"
          proof
            assume X: "X (mrw_values P vs (list_of obs''')) obs''''"
            hence "X (mrw_values P (mrw_value P vs ob) obs'''''') obs''''"
              using obs''''' obs''' by simp
            moreover from obs'''''
            have "lappend obs''''' obs'''' = lappend (llist_of obs'''''') obs''''" by simp
            moreover have "ta_seq_consist P (mrw_value P vs ob) (llist_of obs'''''')" 
              using sc_obs''' obs''' obs''''' by simp
            ultimately show ?thesis using concl1 concl2 by blast
          next
            assume "ta_seq_consist P (mrw_values P vs (list_of obs''')) obs''''"
            with sc_obs''' obs''''' obs'''
            have "ta_seq_consist P (mrw_value P vs ob) (lappend obs''''' obs'''')"
              by(simp add: ta_seq_consist_lappend)
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
      have "case ob of NormalAction (ReadMem ad al v) \<Rightarrow> \<exists>b. vs (ad, al) = \<lfloor>(v, b)\<rfloor> | _ \<Rightarrow> True"
        and "ta_seq_consist P (mrw_value P vs ob) (llist_of obs''')" by simp_all
      moreover from X Cons have "X (mrw_values P (mrw_value P vs ob) obs''') obs''" by simp
      ultimately show ?thesis by blast
    qed
  qed
qed

lemma ta_seq_consist_coinduct_append_wf
  [consumes 2, case_names ta_seq_consist, case_conclusion ta_seq_consist LNil lappend]:
  assumes major: "X vs obs a"
  and wf: "wf R"
  and step: "\<And>vs obs a. X vs obs a
    \<Longrightarrow> obs = LNil \<or>
       (\<exists>obs' obs'' a'. obs = lappend obs' obs'' \<and> ta_seq_consist P vs obs' \<and> (obs' = LNil \<longrightarrow> (a', a) \<in> R) \<and>
                        (lfinite obs' \<longrightarrow> X (mrw_values P vs (list_of obs')) obs'' a' \<or>
                                          ta_seq_consist P (mrw_values P vs (list_of obs')) obs''))"
    (is "\<And>vs obs a. _ \<Longrightarrow> _ \<or> ?step vs obs a")
  shows "ta_seq_consist P vs obs"
proof -
  { fix vs obs a
    assume "X vs obs a"
    with wf
    have "obs = LNil \<or> (\<exists>obs' obs''. obs = lappend obs' obs'' \<and> obs' \<noteq> LNil \<and> ta_seq_consist P vs obs' \<and>
          (lfinite obs' \<longrightarrow> (\<exists>a. X (mrw_values P vs (list_of obs')) obs'' a) \<or> 
                            ta_seq_consist P (mrw_values P vs (list_of obs')) obs''))"
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
          and sc_obs': "ta_seq_consist P vs obs'"
          and decr: "obs' = LNil \<Longrightarrow> (a', a) \<in> R"
          and fin: "lfinite obs' \<Longrightarrow> 
                    X (mrw_values P vs (list_of obs')) obs'' a' \<or>
                    ta_seq_consist P (mrw_values P vs (list_of obs')) obs''"
          by blast
        show ?case
        proof(cases "obs' = LNil")
          case True
          hence "lfinite obs'" by simp
          from fin[OF this] show ?thesis
          proof
            assume X: "X (mrw_values P vs (list_of obs')) obs'' a'"
            from True have "(a', a) \<in> R" by(rule decr)
            from IH[OF this X] show ?thesis
            proof
              assume "obs'' = LNil"
              with True obs have "obs = LNil" by simp
              thus ?thesis ..
            next
              assume "?step_concl (mrw_values P vs (list_of obs')) obs''"
              hence "?step_concl vs obs" using True obs by simp
              thus ?thesis ..
            qed
          next
            assume "ta_seq_consist P (mrw_values P vs (list_of obs')) obs''"
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
  proof(coinduction arbitrary: vs obs a rule: ta_seq_consist_coinduct_append)
    case (ta_seq_consist vs obs a)
    thus ?case by simp(rule step')
  qed
qed

lemma ta_seq_consist_nthI:
  "(\<And>i ad al v. \<lbrakk> enat i < llength obs; lnth obs i = NormalAction (ReadMem ad al v);
      ta_seq_consist P vs (ltake (enat i) obs) \<rbrakk> 
    \<Longrightarrow> \<exists>b. mrw_values P vs (list_of (ltake (enat i) obs)) (ad, al) = \<lfloor>(v, b)\<rfloor>)
  \<Longrightarrow> ta_seq_consist P vs obs"
proof(coinduction arbitrary: vs obs)
  case (ta_seq_consist vs obs)
  hence nth:
    "\<And>i ad al v. \<lbrakk> enat i < llength obs; lnth obs i = NormalAction (ReadMem ad al v); 
                   ta_seq_consist P vs (ltake (enat i) obs) \<rbrakk> 
    \<Longrightarrow> \<exists>b. mrw_values P vs (list_of (ltake (enat i) obs)) (ad, al) = \<lfloor>(v, b)\<rfloor>" by blast
  show ?case
  proof(cases obs)
    case LNil thus ?thesis by simp
  next
    case (LCons ob obs')
    { fix ad al v
      assume "ob = NormalAction (ReadMem ad al v)"
      with nth[of 0 ad al v] LCons
      have "\<exists>b. vs (ad, al) = \<lfloor>(v, b)\<rfloor>"
        by(simp add: zero_enat_def[symmetric]) }
    note base = this
    moreover { 
      fix i ad al v
      assume "enat i < llength obs'" "lnth obs' i = NormalAction (ReadMem ad al v)"
        and "ta_seq_consist P (mrw_value P vs ob) (ltake (enat i) obs')"
      with LCons nth[of "Suc i" ad al v] base
      have "\<exists>b. mrw_values P (mrw_value P vs ob) (list_of (ltake (enat i) obs')) (ad, al) = \<lfloor>(v, b)\<rfloor>"
        by(clarsimp simp add: eSuc_enat[symmetric] split: obs_event.split action.split) }
    ultimately have ?LCons using LCons by(simp split: action.split obs_event.split)
    thus ?thesis ..
  qed
qed

lemma ta_seq_consist_into_non_speculative:
  "\<lbrakk> ta_seq_consist P vs obs; \<forall>adal. set_option (vs adal) \<subseteq> vs' adal \<times> UNIV \<rbrakk>
  \<Longrightarrow> non_speculative P vs' obs"
proof(coinduction arbitrary: vs' obs vs)
  case (non_speculative vs' obs vs)
  thus ?case
    apply cases
    apply(auto split: action.split_asm obs_event.split_asm)
    apply(rule exI, erule conjI, auto)+
    done
qed

lemma llist_of_list_of_append:
  "lfinite xs \<Longrightarrow> llist_of (list_of xs @ ys) = lappend xs (llist_of ys)"
unfolding lfinite_eq_range_llist_of by(clarsimp simp add: lappend_llist_of_llist_of)

lemma ta_seq_consist_most_recent_write_for:
  assumes sc: "ta_seq_consist P Map.empty (lmap snd E)"
  and read: "r \<in> read_actions E"
  and new_actions_for_fun: "\<And>adal a a'. \<lbrakk> a \<in> new_actions_for P E adal; a' \<in> new_actions_for P E adal \<rbrakk> \<Longrightarrow> a = a'"
  shows "\<exists>i. P,E \<turnstile> r \<leadsto>mrw i \<and> i < r"
proof -
  from read obtain t v ad al 
    where nth_r: "lnth E r = (t, NormalAction (ReadMem ad al v))"
    and r: "enat r < llength E"
    by(cases)(cases "lnth E r", auto simp add: action_obs_def actions_def)
  from nth_r r
  have E_unfold: "E = lappend (ltake (enat r) E) (LCons (t, NormalAction (ReadMem ad al v)) (ldropn (Suc r) E))"
    by (metis lappend_ltake_enat_ldropn ldropn_Suc_conv_ldropn)
  from sc obtain b where sc': "ta_seq_consist P Map.empty (ltake (enat r) (lmap snd E))"
    and mrw': "mrw_values P Map.empty (map snd (list_of (ltake (enat r) E))) (ad, al) = \<lfloor>(v, b)\<rfloor>"
    by(subst (asm) (3) E_unfold)(auto simp add: ta_seq_consist_lappend lmap_lappend_distrib)
  
  from mrw_values_mrw[OF mrw', of t] r
  obtain E' w' 
    where E': "E' = llist_of (list_of (ltake (enat r) E) @ [(t, NormalAction (ReadMem ad al v))])"
    and v: "v = value_written P (ltake (enat r) E) w' (ad, al)"
    and mrw'': "P,E' \<turnstile> r \<leadsto>mrw w'"
    and w': "w' < r" by(fastforce simp add: length_list_of_conv_the_enat min_def split: if_split_asm)

  from E' r have sim: "ltake (enat (Suc r)) E' [\<approx>] ltake (enat (Suc r)) E"
    by(subst E_unfold)(simp add: ltake_lappend llist_of_list_of_append min_def, auto simp add: eSuc_enat[symmetric] zero_enat_def[symmetric] eq_into_sim_actions)
  from nth_r have adal_r: "(ad, al) \<in> action_loc P E r" by(simp add: action_obs_def)
  from E' r have nth_r': "lnth E' r = (t, NormalAction (ReadMem ad al v))"
    by(auto simp add: nth_append length_list_of_conv_the_enat min_def)
  with mrw'' w' r adal_r obtain "E \<turnstile> w' \<le>a r" "w' \<in> write_actions E" "(ad, al) \<in> action_loc P E w'"
    by cases(fastforce simp add: action_obs_def action_loc_change_prefix[OF sim[symmetric], simplified action_obs_def] intro: action_order_change_prefix[OF _ sim] write_actions_change_prefix[OF _ sim])
  
  with read adal_r have "P,E \<turnstile> r \<leadsto>mrw w'"
  proof(rule most_recent_write_for.intros)
    fix wa'
    assume write': "wa' \<in> write_actions E"
      and adal_wa': "(ad, al) \<in> action_loc P E wa'"
    show "E \<turnstile> wa' \<le>a w' \<or> E \<turnstile> r \<le>a wa'"
    proof(cases "r \<le> wa'")
      assume "r \<le> wa'"
      show ?thesis
      proof(cases "is_new_action (action_obs E wa')")
        case False
        with \<open>r \<le> wa'\<close> have "E \<turnstile> r \<le>a wa'" using read write'
          by(auto simp add: action_order_def elim!: read_actions.cases)
        thus ?thesis ..
      next
        case True
        with write' adal_wa' have "wa' \<in> new_actions_for P E (ad, al)"
          by(simp add: new_actions_for_def)
        hence "w' \<notin> new_actions_for P E (ad, al)" using r w' \<open>r \<le> wa'\<close>
          by(auto dest: new_actions_for_fun)
        with \<open>w' \<in> write_actions E\<close> \<open>(ad, al) \<in> action_loc P E w'\<close>
        have "\<not> is_new_action (action_obs E w')" by(simp add: new_actions_for_def)
        with write' True \<open>w' \<in> write_actions E\<close> have "E \<turnstile> wa' \<le>a w'" by(simp add: action_order_def)
        thus ?thesis ..
      qed
    next
      assume "\<not> r \<le> wa'"
      hence "wa' < r" by simp
      with write' adal_wa'
      have "wa' \<in> write_actions E'" "(ad, al) \<in> action_loc P E' wa'"
        by(auto intro: write_actions_change_prefix[OF _ sim[symmetric]] simp add: action_loc_change_prefix[OF sim])
      from most_recent_write_recent[OF mrw'' _ this] nth_r'
      have "E' \<turnstile> wa' \<le>a w' \<or> E' \<turnstile> r \<le>a wa'" by(simp add: action_obs_def)
      thus ?thesis using \<open>wa' < r\<close> w'
        by(auto 4 3 del: disjCI intro: disjI1 disjI2 action_order_change_prefix[OF _ sim])
    qed
  qed
  with w' show ?thesis by blast
qed

lemma ta_seq_consist_mrw_before:
  assumes sc: "ta_seq_consist P Map.empty (lmap snd E)"
  and new_actions_for_fun: "\<And>adal a a'. \<lbrakk> a \<in> new_actions_for P E adal; a' \<in> new_actions_for P E adal \<rbrakk> \<Longrightarrow> a = a'"
  and mrw: "P,E \<turnstile> r \<leadsto>mrw w"
  shows "w < r"
proof -
  from mrw have "r \<in> read_actions E" by cases
  with sc new_actions_for_fun obtain w' where "P,E \<turnstile> r \<leadsto>mrw w'" "w' < r"
    by(auto dest: ta_seq_consist_most_recent_write_for)
  with mrw show ?thesis by(auto dest: most_recent_write_for_fun)
qed

lemma ta_seq_consist_imp_sequentially_consistent:
  assumes tsa_ok: "thread_start_actions_ok E"
  and new_actions_for_fun: "\<And>adal a a'. \<lbrakk> a \<in> new_actions_for P E adal; a' \<in> new_actions_for P E adal \<rbrakk> \<Longrightarrow> a = a'"
  and seq: "ta_seq_consist P Map.empty (lmap snd E)"
  shows "\<exists>ws. sequentially_consistent P (E, ws) \<and> P \<turnstile> (E, ws) \<surd>"
proof(intro exI conjI)
  define ws where "ws i = (THE w. P,E \<turnstile> i \<leadsto>mrw w)" for i
  from seq have ns: "non_speculative P (\<lambda>_. {}) (lmap snd E)"
    by(rule ta_seq_consist_into_non_speculative) simp
  show "sequentially_consistent P (E, ws)" unfolding ws_def
  proof(rule sequentially_consistentI)
    fix r
    assume "r \<in> read_actions E"
    with seq new_actions_for_fun
    obtain w where "P,E \<turnstile> r \<leadsto>mrw w" by(auto dest: ta_seq_consist_most_recent_write_for)
    thus "P,E \<turnstile> r \<leadsto>mrw THE w. P,E \<turnstile> r \<leadsto>mrw w" by(simp add: THE_most_recent_writeI)
  qed

  show "P \<turnstile> (E, ws) \<surd>"
  proof(rule wf_execI)
    show "is_write_seen P E ws"
    proof(rule is_write_seenI)
      fix a ad al v
      assume a: "a \<in> read_actions E"
        and adal: "action_obs E a = NormalAction (ReadMem ad al v)"
      from ns have seq': "non_speculative P (\<lambda>_. {}) (ltake (enat a) (lmap snd E))" by(rule non_speculative_ltake)
      from seq a seq new_actions_for_fun
      obtain w where mrw: "P,E \<turnstile> a \<leadsto>mrw w" 
        and "w < a" by(auto dest: ta_seq_consist_most_recent_write_for)
      hence w: "ws a = w" by(simp add: ws_def THE_most_recent_writeI)
      with mrw adal

      show "ws a \<in> write_actions E"
        and "(ad, al) \<in> action_loc P E (ws a)"
        and "\<not> P,E \<turnstile> a \<le>hb ws a"
        by(fastforce elim!: most_recent_write_for.cases dest: happens_before_into_action_order antisymPD[OF antisym_action_order] read_actions_not_write_actions)+

      let ?between = "ltake (enat (a - Suc w)) (ldropn (Suc w) E)"
      let ?prefix = "ltake (enat w) E"
      let ?vs_prefix = "mrw_values P Map.empty (map snd (list_of ?prefix))"

      { fix v'
        assume new: "is_new_action (action_obs E w)"
          and vs': "?vs_prefix (ad, al) = \<lfloor>(v', True)\<rfloor>"
        from mrw_values_eq_SomeD[OF vs']
        obtain obs' wa obs'' where split: "map snd (list_of ?prefix) = obs' @ wa # obs''"
          and wa: "is_write_action wa"
          and adal': "(ad, al) \<in> action_loc_aux P wa"
          and new_wa: "\<not> is_new_action wa" by blast
        from split have "length (map snd (list_of ?prefix)) = Suc (length obs' + length obs'')" by simp
        hence len_prefix: "llength ?prefix = enat \<dots>" by(simp add: length_list_of_conv_the_enat min_enat1_conv_enat)
        with split have "nth (map snd (list_of ?prefix)) (length obs') = wa"
          and "enat (length obs') < llength ?prefix" by simp_all
        hence "snd (lnth ?prefix (length obs')) = wa" by(simp add: list_of_lmap[symmetric] del: list_of_lmap)
        hence wa': "action_obs E (length obs') = wa" and "enat (length obs') < llength E"
          using \<open>enat (length obs') < llength ?prefix\<close> by(auto simp add: action_obs_def lnth_ltake)
        with wa have "length obs' \<in> write_actions E" by(auto intro: write_actions.intros simp add: actions_def)
        from most_recent_write_recent[OF mrw _ this, of "(ad, al)"] adal adal' wa'
        have "E \<turnstile> length obs' \<le>a w \<or> E \<turnstile> a \<le>a length obs'" by simp
        hence False using new_wa new wa' adal len_prefix \<open>w < a\<close>
          by(auto elim!: action_orderE simp add: min_enat1_conv_enat split: enat.split_asm) 
      }
      hence mrw_value_w: "mrw_value P ?vs_prefix (snd (lnth E w)) (ad, al) =
                          \<lfloor>(value_written P E w (ad, al), \<not> is_new_action (action_obs E w))\<rfloor>"
        using \<open>ws a \<in> write_actions E\<close> \<open>(ad, al) \<in> action_loc P E (ws a)\<close> w
        by(cases "snd (lnth E w)" rule: mrw_value_cases)(fastforce elim: write_actions.cases simp add: value_written_def action_obs_def)+
      have "mrw_values P (mrw_value P ?vs_prefix (snd (lnth E w))) (list_of (lmap snd ?between)) (ad, al) = \<lfloor>(value_written P E w (ad, al), \<not> is_new_action (action_obs E w))\<rfloor>"
      proof(subst mrw_values_no_write_unchanged)
        fix wa
        assume "wa \<in> set (list_of (lmap snd ?between))"
          and write_wa: "is_write_action wa"
          and adal_wa: "(ad, al) \<in> action_loc_aux P wa"
        hence wa: "wa \<in> lset (lmap snd ?between)" by simp
        from wa obtain i_wa where "wa = lnth (lmap snd ?between) i_wa"
          and i_wa: "enat i_wa < llength (lmap snd ?between)"
          unfolding lset_conv_lnth by blast
        moreover hence i_wa_len: "enat (Suc (w + i_wa)) < llength E" by(cases "llength E") auto
        ultimately have wa': "wa = action_obs E (Suc (w + i_wa))"
          by(simp_all add: lnth_ltake action_obs_def ac_simps)
        with write_wa i_wa_len have "Suc (w + i_wa) \<in> write_actions E"
          by(auto intro: write_actions.intros simp add: actions_def)
        from most_recent_write_recent[OF mrw _ this, of "(ad, al)"] adal adal_wa wa'
        have "E \<turnstile> Suc (w + i_wa) \<le>a w \<or> E \<turnstile> a \<le>a Suc (w + i_wa)" by(simp)
        hence "is_new_action wa \<and> \<not> is_new_action (action_obs E w)"
          using adal i_wa wa' by(auto elim: action_orderE)
        thus "case (mrw_value P ?vs_prefix (snd (lnth E w)) (ad, al)) of None \<Rightarrow> False | Some (v, b) \<Rightarrow> b \<and> is_new_action wa"
          unfolding mrw_value_w by simp
      qed(simp add: mrw_value_w)

      moreover

      from a have "a \<in> actions E" by simp
      hence "enat a < llength E" by(rule actionsE)
      with \<open>w < a\<close> have "enat (a - Suc w) < llength E - enat (Suc w)"
        by(cases "llength E") simp_all
      hence "E = lappend (lappend ?prefix (LCons (lnth E w) ?between)) (LCons (lnth (ldropn (Suc w) E) (a - Suc w)) (ldropn (Suc (a - Suc w)) (ldropn (Suc w) E)))"
        using \<open>w < a\<close> \<open>enat a < llength E\<close> unfolding lappend_assoc lappend_code
        apply(subst ldropn_Suc_conv_ldropn, simp)
        apply(subst lappend_ltake_enat_ldropn)
        apply(subst ldropn_Suc_conv_ldropn, simp add: less_trans[where y="enat a"])
        by simp
      hence E': "E = lappend (lappend ?prefix (LCons (lnth E w) ?between)) (LCons (lnth E a) (ldropn (Suc a) E))"
        using \<open>w < a\<close> \<open>enat a < llength E\<close> by simp
      
      from seq have "ta_seq_consist P (mrw_values P Map.empty (list_of (lappend (lmap snd ?prefix) (LCons (snd (lnth E w)) (lmap snd ?between))))) (lmap snd (LCons (lnth E a) (ldropn (Suc a) E)))"
        by(subst (asm) E')(simp add: lmap_lappend_distrib ta_seq_consist_lappend)
      ultimately show "value_written P E (ws a) (ad, al) = v" using adal w
        by(clarsimp simp add: action_obs_def list_of_lappend list_of_LCons)

      (* assume "is_volatile P al" *)
      show "\<not> P,E \<turnstile> a \<le>so ws a" using \<open>w < a\<close> w adal by(auto elim!: action_orderE sync_orderE)

      fix a'
      assume a': "a' \<in> write_actions E" "(ad, al) \<in> action_loc P E a'"

      {
        presume "E \<turnstile> ws a \<le>a a'" "E \<turnstile> a' \<le>a a"
        with mrw adal a' have "a' = ws a" unfolding w
          by cases(fastforce dest: antisymPD[OF antisym_action_order] read_actions_not_write_actions elim!: meta_allE[where x=a'])
        thus "a' = ws a" "a' = ws a" by -
      next
        assume "P,E \<turnstile> ws a \<le>hb a'" "P,E \<turnstile> a' \<le>hb a"
        thus "E \<turnstile> ws a \<le>a a'" "E \<turnstile> a' \<le>a a" using a' by(blast intro: happens_before_into_action_order)+
      next
        assume "is_volatile P al" "P,E \<turnstile> ws a \<le>so a'" "P,E \<turnstile> a' \<le>so a"
        thus "E \<turnstile> ws a \<le>a a'" "E \<turnstile> a' \<le>a a" by(auto elim: sync_orderE)
      }
    qed
  qed(rule tsa_ok)
qed

subsection \<open>Cut-and-update and sequentially consistent completion\<close>

inductive foldl_list_all2 ::
  "('b \<Rightarrow> 'c \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> 'a \<Rightarrow> bool"
for f and P and Q
where
  "foldl_list_all2 f P Q [] [] s"
| "\<lbrakk> Q x y s; P x y s \<Longrightarrow> foldl_list_all2 f P Q xs ys (f x y s) \<rbrakk> \<Longrightarrow> foldl_list_all2 f P Q (x # xs) (y # ys) s"

inductive_simps foldl_list_all2_simps [simp]:
  "foldl_list_all2 f P Q [] ys s"
  "foldl_list_all2 f P Q xs [] s"
  "foldl_list_all2 f P Q (x # xs) (y # ys) s"

inductive_simps foldl_list_all2_Cons1:
  "foldl_list_all2 f P Q (x # xs) ys s"

inductive_simps foldl_list_all2_Cons2:
  "foldl_list_all2 f P Q xs (y # ys) s"

definition eq_upto_seq_inconsist ::
  "'m prog \<Rightarrow> ('addr, 'thread_id) obs_event action list \<Rightarrow> ('addr, 'thread_id) obs_event action list
  \<Rightarrow> ('addr \<times> addr_loc \<rightharpoonup> 'addr val \<times> bool) \<Rightarrow> bool"
where
  "eq_upto_seq_inconsist P =
   foldl_list_all2 (\<lambda>ob ob' vs. mrw_value P vs ob) 
                   (\<lambda>ob ob' vs. case ob of NormalAction (ReadMem ad al v) \<Rightarrow> \<exists>b. vs (ad, al) = Some (v, b) | _ \<Rightarrow> True)
                   (\<lambda>ob ob' vs. if (case ob of NormalAction (ReadMem ad al v) \<Rightarrow> \<exists>b. vs (ad, al) = Some (v, b) | _ \<Rightarrow> True) then ob = ob' else ob \<approx> ob')"

lemma eq_upto_seq_inconsist_simps:
  "eq_upto_seq_inconsist P [] obs' vs \<longleftrightarrow> obs' = []"
  "eq_upto_seq_inconsist P obs [] vs \<longleftrightarrow> obs = []"
  "eq_upto_seq_inconsist P (ob # obs) (ob' # obs') vs \<longleftrightarrow> 
   (case ob of NormalAction (ReadMem ad al v) \<Rightarrow> 
      if (\<exists>b. vs (ad, al) = \<lfloor>(v, b)\<rfloor>) 
      then ob = ob' \<and> eq_upto_seq_inconsist P obs obs' (mrw_value P vs ob) 
      else ob \<approx> ob'
    | _ \<Rightarrow> ob = ob' \<and> eq_upto_seq_inconsist P obs obs' (mrw_value P vs ob))"
by(auto simp add: eq_upto_seq_inconsist_def split: action.split obs_event.split)

lemma eq_upto_seq_inconsist_Cons1:
  "eq_upto_seq_inconsist P (ob # obs) obs' vs \<longleftrightarrow>
   (\<exists>ob' obs''. obs' = ob' # obs'' \<and> 
      (case ob of NormalAction (ReadMem ad al v) \<Rightarrow> 
         if (\<exists>b. vs (ad, al) = \<lfloor>(v, b)\<rfloor>) 
         then ob' = ob \<and> eq_upto_seq_inconsist P obs obs'' (mrw_value P vs ob)
         else ob \<approx> ob'
       | _ \<Rightarrow> ob' = ob \<and> eq_upto_seq_inconsist P obs obs'' (mrw_value P vs ob)))"
unfolding eq_upto_seq_inconsist_def
by(auto split: obs_event.split action.split simp add: foldl_list_all2_Cons1)

lemma eq_upto_seq_inconsist_appendD:
  assumes "eq_upto_seq_inconsist P (obs @ obs') obs'' vs"
  and "ta_seq_consist P vs (llist_of obs)"
  shows "length obs \<le> length obs''" (is ?thesis1)
  and "take (length obs) obs'' = obs" (is ?thesis2)
  and "eq_upto_seq_inconsist P obs' (drop (length obs) obs'') (mrw_values P vs obs)" (is ?thesis3)
using assms
by(induct obs arbitrary: obs'' vs)(auto split: action.split_asm obs_event.split_asm simp add: eq_upto_seq_inconsist_Cons1)

lemma ta_seq_consist_imp_eq_upto_seq_inconsist_refl:
  "ta_seq_consist P vs (llist_of obs) \<Longrightarrow> eq_upto_seq_inconsist P obs obs vs"
apply(induct obs arbitrary: vs)
apply(auto simp add: eq_upto_seq_inconsist_simps split: action.split obs_event.split)
done

context notes split_paired_Ex [simp del] eq_upto_seq_inconsist_simps [simp] begin

lemma eq_upto_seq_inconsist_appendI:
  "\<lbrakk> eq_upto_seq_inconsist P obs OBS vs;
     \<lbrakk> ta_seq_consist P vs (llist_of obs) \<rbrakk> \<Longrightarrow> eq_upto_seq_inconsist P obs' OBS' (mrw_values P vs OBS) \<rbrakk>
  \<Longrightarrow> eq_upto_seq_inconsist P (obs @ obs') (OBS @ OBS') vs"
apply(induct obs arbitrary: vs OBS)
 apply simp
apply(auto simp add: eq_upto_seq_inconsist_Cons1)
apply(simp split: action.split obs_event.split)
apply auto
done

lemma eq_upto_seq_inconsist_trans:
  "\<lbrakk> eq_upto_seq_inconsist P obs obs' vs; eq_upto_seq_inconsist P obs' obs'' vs \<rbrakk>
  \<Longrightarrow> eq_upto_seq_inconsist P obs obs'' vs"
  apply(induction obs arbitrary: obs' obs'' vs)
  apply(clarsimp simp add: eq_upto_seq_inconsist_Cons1)+
  apply(auto split!: action.split obs_event.split if_split_asm)
  done

lemma eq_upto_seq_inconsist_append2:
  "\<lbrakk> eq_upto_seq_inconsist P obs obs' vs; \<not> ta_seq_consist P vs (llist_of obs) \<rbrakk>
  \<Longrightarrow> eq_upto_seq_inconsist P obs (obs' @ obs'') vs"
  apply(induction obs arbitrary: obs' vs)
  apply(clarsimp simp add: eq_upto_seq_inconsist_Cons1)+
  apply(auto split!: action.split obs_event.split if_split_asm)
  done

end


context executions_sc_hb begin

lemma ta_seq_consist_mrwI:
  assumes E: "E \<in> \<E>"
  and wf: "P \<turnstile> (E, ws) \<surd>"
  and mrw: "\<And>a. \<lbrakk> enat a < r; a \<in> read_actions E \<rbrakk> \<Longrightarrow> P,E \<turnstile> a \<leadsto>mrw ws a"
  shows "ta_seq_consist P Map.empty (lmap snd (ltake r E))"
proof(rule ta_seq_consist_nthI)
  fix i ad al v
  assume i_len: "enat i < llength (lmap snd (ltake r E))"
    and E_i: "lnth (lmap snd (ltake r E)) i = NormalAction (ReadMem ad al v)"
    and sc: "ta_seq_consist P Map.empty (ltake (enat i) (lmap snd (ltake r E)))"
  from i_len have "enat i < r" by simp
  with sc have "ta_seq_consist P Map.empty (ltake (enat i) (lmap snd E))"
    by(simp add: min_def split: if_split_asm)
  hence ns: "non_speculative P (\<lambda>_. {}) (ltake (enat i) (lmap snd E))"
    by(rule ta_seq_consist_into_non_speculative) simp
  from i_len have "i \<in> actions E" by(simp add: actions_def)
  moreover from E_i i_len have obs_i: "action_obs E i = NormalAction (ReadMem ad al v)"
    by(simp add: action_obs_def lnth_ltake)
  ultimately have read: "i \<in> read_actions E" ..
  with i_len have mrw_i: "P,E \<turnstile> i \<leadsto>mrw ws i" by(auto intro: mrw)
  with E have "ws i < i" using ns by(rule mrw_before)

  from mrw_i obs_i obtain adal_w: "(ad, al) \<in> action_loc P E (ws i)"
    and adal_r: "(ad, al) \<in> action_loc P E i"
    and "write": "ws i \<in> write_actions E" by cases auto
  
  from wf have "is_write_seen P E ws" by(rule wf_exec_is_write_seenD)
  from is_write_seenD[OF this read obs_i]
  have vw_v: "value_written P E (ws i) (ad, al) = v" by simp

  let ?vs = "mrw_values P Map.empty (map snd (list_of (ltake (enat (ws i)) E)))"

  from \<open>ws i < i\<close> i_len have "enat (ws i) < llength (ltake (enat i) E)"
    by(simp add: less_trans[where y="enat i"])
  hence "ltake (enat i) E = lappend (ltake (enat (ws i)) (ltake (enat i) E)) (LCons (lnth (ltake (enat i) E) (ws i)) (ldropn (Suc (ws i)) (ltake (enat i) E)))"
    by(simp only: ldropn_Suc_conv_ldropn lappend_ltake_enat_ldropn)
  also have "\<dots> = lappend (ltake (enat (ws i)) E) (LCons (lnth E (ws i)) (ldropn (Suc (ws i)) (ltake (enat i) E)))"
    using \<open>ws i < i\<close> i_len \<open>enat (ws i) < llength (ltake (enat i) E)\<close> 
    by(simp add: lnth_ltake)(simp add: min_def)
  finally have r_E: "ltake (enat i) E = \<dots>" .

  have "mrw_values P Map.empty (list_of (ltake (enat i) (lmap snd (ltake r E)))) (ad, al)
    = mrw_values P Map.empty (map snd (list_of (ltake (enat i) E))) (ad, al)"
    using \<open>enat i < r\<close> by(auto simp add: min_def)
  also have "\<dots> = mrw_values P (mrw_value P ?vs (snd (lnth E (ws i)))) (map snd (list_of (ldropn (Suc (ws i)) (ltake (enat i) E)))) (ad, al)"
    by(subst r_E)(simp add: list_of_lappend)
  also have "\<dots> = mrw_value P ?vs (snd (lnth E (ws i))) (ad, al)"
  proof(rule mrw_values_no_write_unchanged)
    fix wa
    assume wa: "wa \<in> set (map snd (list_of (ldropn (Suc (ws i)) (ltake (enat i) E))))"
      and "is_write_action wa" "(ad, al) \<in> action_loc_aux P wa"

    from wa obtain w where "w < length (map snd (list_of (ldropn (Suc (ws i)) (ltake (enat i) E))))"
      and "map snd (list_of (ldropn (Suc (ws i)) (ltake (enat i) E))) ! w = wa"
      unfolding in_set_conv_nth by blast
    moreover hence "Suc (ws i + w) < i" (is "?w < _") using i_len 
      by(cases "llength E")(simp_all add: length_list_of_conv_the_enat)
    ultimately have obs_w': "action_obs E ?w = wa" using i_len
      by(simp add: action_obs_def lnth_ltake less_trans[where y="enat i"] ac_simps)
    from \<open>?w < i\<close> i_len have "?w \<in> actions E"
      by(simp add: actions_def less_trans[where y="enat i"])
    with \<open>is_write_action wa\<close> obs_w' \<open>(ad, al) \<in> action_loc_aux P wa\<close>
    have write': "?w \<in> write_actions E" 
      and adal': "(ad, al) \<in> action_loc P E ?w"
      by(auto intro: write_actions.intros)
      
    from \<open>?w < i\<close> \<open>i \<in> read_actions E\<close> \<open>?w \<in> actions E\<close>
    have "E \<turnstile> ?w \<le>a i" by(auto simp add: action_order_def elim: read_actions.cases)

    from mrw_i adal_r write' adal'
    have "E \<turnstile> ?w \<le>a ws i \<or> E \<turnstile> i \<le>a ?w" by(rule most_recent_write_recent)
    hence "E \<turnstile> ?w \<le>a ws i"
    proof
      assume "E \<turnstile> i \<le>a ?w"
      with \<open>E \<turnstile> ?w \<le>a i\<close> have "?w = i" by(rule antisymPD[OF antisym_action_order])
      with write' read have False by(auto dest: read_actions_not_write_actions)
      thus ?thesis ..
    qed

    from adal_w "write" have "mrw_value P ?vs (snd (lnth E (ws i))) (ad, al) \<noteq> None"
      by(cases "snd (lnth E (ws i))" rule: mrw_value_cases)
        (auto simp add: action_obs_def split: if_split_asm elim: write_actions.cases)
    then obtain b v where vb: "mrw_value P ?vs (snd (lnth E (ws i))) (ad, al) = Some (v, b)" by auto
    moreover
    from \<open>E \<turnstile> ?w \<le>a ws i\<close> obs_w'
    have "is_new_action wa" "\<not> is_new_action (action_obs E (ws i))" by(auto elim!: action_orderE)
    from \<open>\<not> is_new_action (action_obs E (ws i))\<close> "write" adal_w
    obtain v' where "action_obs E (ws i) = NormalAction (WriteMem ad al v')"
      by(auto elim!: write_actions.cases is_write_action.cases)
    with vb have b by(simp add: action_obs_def)
    with \<open>is_new_action wa\<close> vb 
    show "case mrw_value P ?vs (snd (lnth E (ws i))) (ad, al) of None \<Rightarrow> False | \<lfloor>(v, b)\<rfloor> \<Rightarrow> b \<and> is_new_action wa" by simp
  qed
  also {
    fix v
    assume "?vs (ad, al) = Some (v, True)"
      and "is_new_action (action_obs E (ws i))"
    
    from mrw_values_eq_SomeD[OF this(1)]
    obtain wa where "wa \<in> set (map snd (list_of (ltake (enat (ws i)) E)))"
      and "is_write_action wa"
      and "(ad, al) \<in> action_loc_aux P wa"
      and "\<not> is_new_action wa" by(fastforce simp del: set_map)
    moreover then obtain w where w: "w < ws i"  and wa: "wa = snd (lnth E w)"
      unfolding in_set_conv_nth by(cases "llength E")(auto simp add: lnth_ltake length_list_of_conv_the_enat)
    ultimately have "w \<in> write_actions E" "action_obs E w = wa" "(ad, al) \<in> action_loc P E w"
      using \<open>ws i \<in> write_actions E\<close>
      by(auto intro!: write_actions.intros simp add: actions_def less_trans[where y="enat (ws i)"] action_obs_def elim!: write_actions.cases)
    with mrw_i adal_r have "E \<turnstile> w \<le>a ws i \<or> E \<turnstile> i \<le>a w" by -(rule most_recent_write_recent)
    hence False
    proof
      assume "E \<turnstile> w \<le>a ws i"
      moreover from \<open>\<not> is_new_action wa\<close> \<open>is_new_action (action_obs E (ws i))\<close> "write" w wa \<open>w \<in> write_actions E\<close>
      have "E \<turnstile> ws i \<le>a w" by(auto simp add: action_order_def action_obs_def)
      ultimately have "w = ws i" by(rule antisymPD[OF antisym_action_order])
      with \<open>w < ws i\<close> show False by simp
    next
      assume "E \<turnstile> i \<le>a w"
      moreover from \<open>w \<in> write_actions E\<close> \<open>w < ws i\<close> \<open>ws i < i\<close> read
      have "E \<turnstile> w \<le>a i" by(auto simp add: action_order_def elim: read_actions.cases)
      ultimately have "i = w" by(rule antisymPD[OF antisym_action_order])
      with \<open>w < ws i\<close> \<open>ws i < i\<close> show False by simp
    qed }
  then obtain b where "\<dots> = Some (v, b)" using vw_v "write" adal_w
    apply(atomize_elim)
    apply(auto simp add: action_obs_def value_written_def write_actions_iff)
    apply(erule is_write_action.cases)
    apply auto
    apply blast+
    done
  finally show "\<exists>b. mrw_values P Map.empty (list_of (ltake (enat i) (lmap snd (ltake r E)))) (ad, al) = \<lfloor>(v, b)\<rfloor>"
    by blast
qed

end

context jmm_multithreaded begin

definition complete_sc :: "('l,'thread_id,'x,'m,'w) state \<Rightarrow> ('addr \<times> addr_loc \<rightharpoonup> 'addr val \<times> bool) \<Rightarrow> 
  ('thread_id \<times> ('l, 'thread_id, 'x, 'm, 'w, ('addr, 'thread_id) obs_event action) thread_action) llist"
where
  "complete_sc s vs = unfold_llist
     (\<lambda>(s, vs). \<forall>t ta s'. \<not> s -t\<triangleright>ta\<rightarrow> s')
     (\<lambda>(s, vs). fst (SOME ((t, ta), s'). s -t\<triangleright>ta\<rightarrow> s' \<and> ta_seq_consist P vs (llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)))
     (\<lambda>(s, vs). let ((t, ta), s') = SOME ((t, ta), s'). s -t\<triangleright>ta\<rightarrow> s' \<and> ta_seq_consist P vs (llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)
         in (s', mrw_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))
     (s, vs)"

definition sc_completion :: "('l, 'thread_id, 'x, 'm, 'w) state \<Rightarrow> ('addr \<times> addr_loc \<rightharpoonup> 'addr val \<times> bool) \<Rightarrow> bool"
where
  "sc_completion s vs \<longleftrightarrow>
   (\<forall>ttas s' t x ta x' m'.
       s -\<triangleright>ttas\<rightarrow>* s' \<longrightarrow> ta_seq_consist P vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) \<longrightarrow>
       thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor> \<longrightarrow> t \<turnstile> (x, shr s') -ta\<rightarrow> (x', m') \<longrightarrow> actions_ok s' t ta \<longrightarrow>
       (\<exists>ta' x'' m''. t \<turnstile> (x, shr s') -ta'\<rightarrow> (x'', m'') \<and> actions_ok s' t ta' \<and>
                      ta_seq_consist P (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (llist_of \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)))"

lemma sc_completionD:
  "\<lbrakk> sc_completion s vs; s -\<triangleright>ttas\<rightarrow>* s'; ta_seq_consist P vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))); 
     thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor>; t \<turnstile> (x, shr s') -ta\<rightarrow> (x', m'); actions_ok s' t ta \<rbrakk>
  \<Longrightarrow> \<exists>ta' x'' m''. t \<turnstile> (x, shr s') -ta'\<rightarrow> (x'', m'') \<and> actions_ok s' t ta' \<and>
                   ta_seq_consist P (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (llist_of \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)"
unfolding sc_completion_def by blast

lemma sc_completionI:
  "(\<And>ttas s' t x ta x' m'. 
     \<lbrakk> s -\<triangleright>ttas\<rightarrow>* s'; ta_seq_consist P vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))); 
       thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor>; t \<turnstile> (x, shr s') -ta\<rightarrow> (x', m'); actions_ok s' t ta \<rbrakk>
     \<Longrightarrow> \<exists>ta' x'' m''. t \<turnstile> (x, shr s') -ta'\<rightarrow> (x'', m'') \<and> actions_ok s' t ta' \<and>
                   ta_seq_consist P (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (llist_of \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>))
  \<Longrightarrow> sc_completion s vs"
unfolding sc_completion_def by blast

lemma sc_completion_shift:
  assumes sc_c: "sc_completion s vs"
  and \<tau>Red: "s -\<triangleright>ttas\<rightarrow>* s'"
  and sc: "ta_seq_consist P vs (lconcat (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (llist_of ttas)))"
  shows "sc_completion s' (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
proof(rule sc_completionI)
  fix ttas' s'' t x ta x' m'
  assume \<tau>Red': "s' -\<triangleright>ttas'\<rightarrow>* s''"
    and sc': "ta_seq_consist P (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas')))"
    and red: "thr s'' t = \<lfloor>(x, no_wait_locks)\<rfloor>" "t \<turnstile> \<langle>x, shr s''\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>" "actions_ok s'' t ta" 
  from \<tau>Red \<tau>Red' have "s -\<triangleright>ttas @ ttas'\<rightarrow>* s''" unfolding RedT_def by(rule rtrancl3p_trans)
  moreover from sc sc' have "ta_seq_consist P vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (ttas @ ttas'))))"
    apply(simp add: lappend_llist_of_llist_of[symmetric] ta_seq_consist_lappend del: lappend_llist_of_llist_of)
    apply(simp add: lconcat_llist_of[symmetric] lmap_llist_of[symmetric] llist.map_comp o_def split_def del: lmap_llist_of)
    done
  ultimately
  show "\<exists>ta' x'' m''. t \<turnstile> \<langle>x, shr s''\<rangle> -ta'\<rightarrow> \<langle>x'', m''\<rangle> \<and> actions_ok s'' t ta' \<and>
         ta_seq_consist P (mrw_values P (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas'))) (llist_of \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)"
    using red unfolding foldl_append[symmetric] concat_append[symmetric] map_append[symmetric]
    by(rule sc_completionD[OF sc_c])
qed

lemma complete_sc_in_Runs:
  assumes cau: "sc_completion s vs"
  and ta_seq_consist_convert_RA: "\<And>vs ln. ta_seq_consist P vs (llist_of (convert_RA ln))"
  shows "mthr.Runs s (complete_sc s vs)"
proof -
  let ?ttas' = "\<lambda>ttas' :: ('thread_id \<times> ('l,'thread_id,'x,'m,'w, ('addr, 'thread_id) obs_event action) thread_action) list.
               concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas')"
  let "?vs ttas'" = "mrw_values P vs (?ttas' ttas')"

  define s' vs'
    and ttas :: "('thread_id \<times> ('l,'thread_id,'x,'m,'w, ('addr, 'thread_id) obs_event action) thread_action) list"
    where "s' = s" and "vs' = vs" and "ttas = []"
  hence "s -\<triangleright>ttas\<rightarrow>* s'" "ta_seq_consist P vs (llist_of (?ttas' ttas))" by auto
  hence "mthr.Runs s' (complete_sc s' (?vs ttas))"
  proof(coinduction arbitrary: s' ttas rule: mthr.Runs.coinduct)
    case (Runs s' ttas')
    note Red = \<open>s -\<triangleright>ttas'\<rightarrow>* s'\<close>
      and sc = \<open>ta_seq_consist P vs (llist_of (?ttas' ttas'))\<close>
    show ?case
    proof(cases "\<exists>t' ta' s''. s' -t'\<triangleright>ta'\<rightarrow> s''")
      case False
      hence ?Stuck by(simp add: complete_sc_def)
      thus ?thesis ..
    next
      case True
      let ?proceed = "\<lambda>((t', ta'), s''). s' -t'\<triangleright>ta'\<rightarrow> s'' \<and> ta_seq_consist P (?vs ttas') (llist_of \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)"
      from True obtain t' ta' s'' where red: "s' -t'\<triangleright>ta'\<rightarrow> s''" by(auto)
      then obtain ta'' s''' where "s' -t'\<triangleright>ta''\<rightarrow> s'''"
        and "ta_seq_consist P (?vs ttas') (llist_of \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>)"
      proof(cases)
        case (redT_normal x x' m')
        note red = \<open>t' \<turnstile> \<langle>x, shr s'\<rangle> -ta'\<rightarrow> \<langle>x', m'\<rangle>\<close>
          and ts''t' = \<open>thr s' t' = \<lfloor>(x, no_wait_locks)\<rfloor>\<close>
          and aok = \<open>actions_ok s' t' ta'\<close>
          and s'' = \<open>redT_upd s' t' ta' x' m' s''\<close>
        from sc_completionD[OF cau Red sc ts''t' red aok]
        obtain ta'' x'' m'' where red': "t' \<turnstile> \<langle>x, shr s'\<rangle> -ta''\<rightarrow> \<langle>x'', m''\<rangle>"
          and aok': "actions_ok s' t' ta''"
          and sc': "ta_seq_consist P (?vs ttas') (llist_of \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>)" by blast
        from redT_updWs_total obtain ws' where "redT_updWs t' (wset s') \<lbrace>ta''\<rbrace>\<^bsub>w\<^esub> ws'" ..
        then obtain s''' where "redT_upd s' t' ta'' x'' m'' s'''" by fastforce
        with red' ts''t' aok' have "s' -t'\<triangleright>ta''\<rightarrow> s'''" ..
        thus thesis using sc' by(rule that)
      next
        case redT_acquire
        thus thesis by(simp add: that[OF red] ta_seq_consist_convert_RA)
      qed
      hence "?proceed ((t', ta''), s''')" using Red by(auto)
      hence *: "?proceed (Eps ?proceed)" by(rule someI)
      moreover from Red * have "s -\<triangleright>ttas' @ [fst (Eps ?proceed)]\<rightarrow>* snd (Eps ?proceed)"
        by(auto simp add: split_beta RedT_def intro: rtrancl3p_step)
      moreover from True
      have "complete_sc s' (?vs ttas') = LCons (fst (Eps ?proceed)) (complete_sc (snd (Eps ?proceed)) (?vs (ttas' @ [fst (Eps ?proceed)])))"
        unfolding complete_sc_def by(simp add: split_def)
      moreover from sc \<open>?proceed (Eps ?proceed)\<close>
      have "ta_seq_consist P vs (llist_of (?ttas' (ttas' @ [fst (Eps ?proceed)])))"
        unfolding map_append concat_append lappend_llist_of_llist_of[symmetric] 
        by(subst ta_seq_consist_lappend)(auto simp add: split_def)
      ultimately have ?Step
        by(fastforce intro: exI[where x="ttas' @ [fst (Eps ?proceed)]"] simp del: split_paired_Ex)
      thus ?thesis by simp
    qed
  qed
  thus ?thesis by(simp add: s'_def ttas_def)
qed

lemma complete_sc_ta_seq_consist:
  assumes cau: "sc_completion s vs"
  and ta_seq_consist_convert_RA: "\<And>vs ln. ta_seq_consist P vs (llist_of (convert_RA ln))"
  shows "ta_seq_consist P vs (lconcat (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (complete_sc s vs)))"
proof -
  define vs' where "vs' = vs"
  let ?obs = "\<lambda>ttas. lconcat (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)"
  define obs where "obs = ?obs (complete_sc s vs)"
  define a where "a = complete_sc s vs'"
  let ?ttas' = "\<lambda>ttas' :: ('thread_id \<times> ('l,'thread_id,'x,'m,'w,('addr, 'thread_id) obs_event action) thread_action) list.
               concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas')"
  let ?vs = "\<lambda>ttas'. mrw_values P vs (?ttas' ttas')"
  from vs'_def obs_def
  have "s -\<triangleright>[]\<rightarrow>* s" "ta_seq_consist P vs (llist_of (?ttas' []))" "vs' = ?vs []" by(auto)
  hence "\<exists>s' ttas'. obs = ?obs (complete_sc s' vs') \<and> s -\<triangleright>ttas'\<rightarrow>* s' \<and> 
                    ta_seq_consist P vs (llist_of (?ttas' ttas')) \<and> vs' = ?vs ttas' \<and> 
                    a = complete_sc s' vs'"
    unfolding obs_def vs'_def a_def by metis
  moreover have "wf (inv_image {(m, n). m < n} (llength \<circ> ltakeWhile (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = [])))"
    (is "wf ?R") by(rule wf_inv_image)(rule wellorder_class.wf)
  ultimately show "ta_seq_consist P vs' obs"
  proof(coinduct vs' obs a rule: ta_seq_consist_coinduct_append_wf)
    case (ta_seq_consist vs' obs a)
    then obtain s' ttas' where obs_def: "obs = ?obs (complete_sc s' (?vs ttas'))"
      and Red: "s -\<triangleright>ttas'\<rightarrow>* s'"
      and sc: "ta_seq_consist P vs (llist_of (?ttas' ttas'))"
      and vs'_def: "vs' = ?vs ttas'" 
      and a_def: "a = complete_sc s' vs'" by blast

    show ?case
    proof(cases "\<exists>t' ta' s''. s' -t'\<triangleright>ta'\<rightarrow> s''")
      case False
      hence "obs = LNil" unfolding obs_def complete_sc_def by simp
      hence ?LNil unfolding obs_def by auto
      thus ?thesis ..
    next
      case True
      let ?proceed = "\<lambda>((t', ta'), s''). s' -t'\<triangleright>ta'\<rightarrow> s'' \<and> ta_seq_consist P (?vs ttas') (llist_of \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)"
      let ?tta = "fst (Eps ?proceed)"
      let ?s' = "snd (Eps ?proceed)"

      from True obtain t' ta' s'' where red: "s' -t'\<triangleright>ta'\<rightarrow> s''" by blast
      then obtain ta'' s''' where "s' -t'\<triangleright>ta''\<rightarrow> s'''"
        and "ta_seq_consist P (?vs ttas') (llist_of \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>)"
      proof(cases)
        case (redT_normal x x' m')
        note red = \<open>t' \<turnstile> \<langle>x, shr s'\<rangle> -ta'\<rightarrow> \<langle>x', m'\<rangle>\<close>
          and ts''t' = \<open>thr s' t' = \<lfloor>(x, no_wait_locks)\<rfloor>\<close>
          and aok = \<open>actions_ok s' t' ta'\<close>
          and s''' = \<open>redT_upd s' t' ta' x' m' s''\<close>
        from sc_completionD[OF cau Red sc ts''t' red aok]
        obtain ta'' x'' m'' where red': "t' \<turnstile> \<langle>x, shr s'\<rangle> -ta''\<rightarrow> \<langle>x'', m''\<rangle>"
          and aok': "actions_ok s' t' ta''"
          and sc': "ta_seq_consist P (?vs ttas') (llist_of \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>)" by blast
        from redT_updWs_total obtain ws' where "redT_updWs t' (wset s') \<lbrace>ta''\<rbrace>\<^bsub>w\<^esub> ws'" ..
        then obtain s''' where "redT_upd s' t' ta'' x'' m'' s'''" by fastforce
        with red' ts''t' aok' have "s' -t'\<triangleright>ta''\<rightarrow> s'''" ..
        thus thesis using sc' by(rule that)
      next
        case redT_acquire
        thus thesis by(simp add: that[OF red] ta_seq_consist_convert_RA)
      qed
      hence "?proceed ((t', ta''), s''')" by auto
      hence "?proceed (Eps ?proceed)" by(rule someI)
      show ?thesis
      proof(cases "obs = LNil")
        case True thus ?thesis ..
      next
        case False
        from True
        have csc_unfold: "complete_sc s' (?vs ttas') = LCons ?tta (complete_sc ?s' (?vs (ttas' @ [?tta])))"
          unfolding complete_sc_def by(simp add: split_def)
        hence "obs = lappend (llist_of \<lbrace>snd ?tta\<rbrace>\<^bsub>o\<^esub>) (?obs (complete_sc ?s' (?vs (ttas' @ [?tta]))))"
          using obs_def by(simp add: split_beta)
        moreover have "ta_seq_consist P vs' (llist_of \<lbrace>snd ?tta\<rbrace>\<^bsub>o\<^esub>)"
          using \<open>?proceed (Eps ?proceed)\<close> vs'_def by(clarsimp simp add: split_beta)
        moreover {
          assume "llist_of \<lbrace>snd ?tta\<rbrace>\<^bsub>o\<^esub> = LNil"
          moreover from obs_def \<open>obs \<noteq> LNil\<close>
          have "lfinite (ltakeWhile (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = []) (complete_sc s' (?vs ttas')))"
            unfolding lfinite_ltakeWhile by(fastforce simp add: split_def lconcat_eq_LNil)
          ultimately have "(complete_sc ?s' (?vs (ttas' @ [?tta])), a) \<in> ?R"
            unfolding a_def vs'_def csc_unfold
            by(clarsimp simp add: split_def llist_of_eq_LNil_conv)(auto simp add: lfinite_eq_range_llist_of) }
        moreover have "?obs (complete_sc ?s' (?vs (ttas' @ [?tta]))) = ?obs (complete_sc ?s' (mrw_values P vs' (list_of (llist_of \<lbrace>snd ?tta\<rbrace>\<^bsub>o\<^esub>))))"
          unfolding vs'_def by(simp add: split_def)
        moreover from \<open>?proceed (Eps ?proceed)\<close> Red
        have "s -\<triangleright>ttas' @ [?tta]\<rightarrow>* ?s'" by(auto simp add: RedT_def split_def intro: rtrancl3p_step)
        moreover from sc \<open>?proceed (Eps ?proceed)\<close>
        have "ta_seq_consist P vs (llist_of (?ttas' (ttas' @ [?tta])))"
          by(clarsimp simp add: split_def ta_seq_consist_lappend lappend_llist_of_llist_of[symmetric] simp del: lappend_llist_of_llist_of)
        moreover have "mrw_values P vs' (list_of (llist_of \<lbrace>snd ?tta\<rbrace>\<^bsub>o\<^esub>)) = ?vs (ttas' @ [?tta])" 
          unfolding vs'_def by(simp add: split_def)
        moreover have "complete_sc ?s' (?vs (ttas' @ [?tta])) = complete_sc ?s' (mrw_values P vs' (list_of (llist_of \<lbrace>snd ?tta\<rbrace>\<^bsub>o\<^esub>)))"
          unfolding vs'_def by(simp add: split_def)
        ultimately have "?lappend" by blast
        thus ?thesis ..
      qed
    qed
  qed
qed

lemma sequential_completion_Runs:
  assumes "sc_completion s vs"
  and "\<And>vs ln. ta_seq_consist P vs (llist_of (convert_RA ln))"
  shows "\<exists>ttas. mthr.Runs s ttas \<and> ta_seq_consist P vs (lconcat (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))"
using complete_sc_ta_seq_consist[OF assms] complete_sc_in_Runs[OF assms]
by blast


definition cut_and_update :: "('l, 'thread_id, 'x, 'm, 'w) state \<Rightarrow> ('addr \<times> addr_loc \<rightharpoonup> 'addr val \<times> bool) \<Rightarrow> bool"
where
  "cut_and_update s vs \<longleftrightarrow>
   (\<forall>ttas s' t x ta x' m'.
      s -\<triangleright>ttas\<rightarrow>* s' \<longrightarrow> ta_seq_consist P vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) \<longrightarrow>
      thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor> \<longrightarrow> t \<turnstile> (x, shr s') -ta\<rightarrow> (x', m') \<longrightarrow> actions_ok s' t ta \<longrightarrow> 
   (\<exists>ta' x'' m''. t \<turnstile> (x, shr s') -ta'\<rightarrow> (x'', m'') \<and> actions_ok s' t ta' \<and>
                   ta_seq_consist P (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (llist_of \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) \<and>
                   eq_upto_seq_inconsist P \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))))"

lemma cut_and_updateI[intro?]:
  "(\<And>ttas s' t x ta x' m'. 
     \<lbrakk> s -\<triangleright>ttas\<rightarrow>* s'; ta_seq_consist P vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)));
       thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor>; t \<turnstile> (x, shr s') -ta\<rightarrow> (x', m'); actions_ok s' t ta \<rbrakk>
      \<Longrightarrow> \<exists>ta' x'' m''. t \<turnstile> (x, shr s') -ta'\<rightarrow> (x'', m'') \<and> actions_ok s' t ta' \<and> 
                       ta_seq_consist P (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (llist_of \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) \<and>
                       eq_upto_seq_inconsist P \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))))
    \<Longrightarrow> cut_and_update s vs"
unfolding cut_and_update_def by blast

lemma cut_and_updateD:
  "\<lbrakk> cut_and_update s vs; s -\<triangleright>ttas\<rightarrow>* s'; ta_seq_consist P vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)));
     thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor>; t \<turnstile> (x, shr s') -ta\<rightarrow> (x', m'); actions_ok s' t ta \<rbrakk>
  \<Longrightarrow> \<exists>ta' x'' m''. t \<turnstile> (x, shr s') -ta'\<rightarrow> (x'', m'') \<and> actions_ok s' t ta' \<and> 
                   ta_seq_consist P (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (llist_of \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) \<and>
                   eq_upto_seq_inconsist P \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
unfolding cut_and_update_def by blast

lemma cut_and_update_imp_sc_completion:
  "cut_and_update s vs \<Longrightarrow> sc_completion s vs"
apply(rule sc_completionI)
apply(drule (5) cut_and_updateD)
apply blast
done

lemma sequential_completion:
  assumes cut_and_update: "cut_and_update s vs"
  and ta_seq_consist_convert_RA: "\<And>vs ln. ta_seq_consist P vs (llist_of (convert_RA ln))"
  and Red: "s -\<triangleright>ttas\<rightarrow>* s'"
  and sc: "ta_seq_consist P vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
  and red: "s' -t\<triangleright>ta\<rightarrow> s''"
  shows
  "\<exists>ta' ttas'. mthr.Runs s' (LCons (t, ta') ttas') \<and> 
     ta_seq_consist P vs (lconcat (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (lappend (llist_of ttas) (LCons (t, ta') ttas')))) \<and> 
     eq_upto_seq_inconsist P \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
proof -
  from red obtain ta' s''' 
    where red': "redT s' (t, ta') s'''"
    and sc': "ta_seq_consist P vs (lconcat (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (lappend (llist_of ttas) (LCons (t, ta') LNil))))"
    and eq: "eq_upto_seq_inconsist P \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
  proof cases
    case (redT_normal x x' m')
    note ts't = \<open>thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor>\<close>
      and red = \<open>t \<turnstile> \<langle>x, shr s'\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>\<close>
      and aok = \<open>actions_ok s' t ta\<close>
      and s'' = \<open>redT_upd s' t ta x' m' s''\<close>
    from cut_and_updateD[OF cut_and_update, OF Red sc ts't red aok]
    obtain ta' x'' m'' where red: "t \<turnstile> \<langle>x, shr s'\<rangle> -ta'\<rightarrow> \<langle>x'', m''\<rangle>"
      and sc': "ta_seq_consist P (mrw_values P vs (concat (map (\<lambda>(t, y). \<lbrace>y\<rbrace>\<^bsub>o\<^esub>) ttas))) (llist_of \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)"
      and eq: "eq_upto_seq_inconsist P \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
      and aok: "actions_ok s' t ta'" by blast
    obtain ws''' where "redT_updWs t (wset s') \<lbrace>ta'\<rbrace>\<^bsub>w\<^esub> ws'''"
      using redT_updWs_total ..
    then obtain s''' where s''': "redT_upd s' t ta' x'' m'' s'''" by fastforce
    with red \<open>thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor>\<close> aok have "s' -t\<triangleright>ta'\<rightarrow> s'''" by(rule redT.redT_normal)
    moreover from sc sc'
    have "ta_seq_consist P vs (lconcat (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (lappend (llist_of ttas) (LCons (t, ta') LNil))))"
      by(auto simp add: lmap_lappend_distrib ta_seq_consist_lappend split_def lconcat_llist_of[symmetric] o_def list_of_lconcat)
    ultimately show thesis using eq by(rule that)
  next
    case (redT_acquire x ln n)
    hence "ta_seq_consist P vs (lconcat (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (lappend (llist_of ttas) (LCons (t, ta) LNil))))"
      and "eq_upto_seq_inconsist P \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
      using sc
      by(simp_all add: lmap_lappend_distrib ta_seq_consist_lappend split_def lconcat_llist_of[symmetric] o_def list_of_lconcat ta_seq_consist_convert_RA ta_seq_consist_imp_eq_upto_seq_inconsist_refl)
    with red show thesis by(rule that)
  qed

  txt \<open>Now, find a sequentially consistent completion from @{term "s'''"} onwards.\<close>
  from Red red' have Red': "s -\<triangleright>ttas @ [(t, ta')]\<rightarrow>* s'''"
    unfolding RedT_def by(auto intro: rtrancl3p_step)

  from sc sc'
  have "ta_seq_consist P vs (lconcat (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (llist_of (ttas @ [(t, ta')]))))"
    by(simp add: o_def split_def lappend_llist_of_llist_of[symmetric])
  with cut_and_update_imp_sc_completion[OF cut_and_update] Red'
  have "sc_completion s''' (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (ttas @ [(t, ta')]))))"
    by(rule sc_completion_shift)
  from sequential_completion_Runs[OF this ta_seq_consist_convert_RA]
  obtain ttas' where \<tau>Runs: "mthr.Runs s''' ttas'"
    and sc'': "ta_seq_consist P (mrw_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (ttas @ [(t, ta')])))) 
                                (lconcat (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas'))"
    by blast
  from red' \<tau>Runs have "mthr.Runs s' (LCons (t, ta') ttas')" ..
  moreover from sc sc' sc''
  have "ta_seq_consist P vs (lconcat (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (lappend (llist_of ttas) (LCons (t, ta') ttas'))))"
    unfolding lmap_lappend_distrib lconcat_lappend by(simp add: o_def ta_seq_consist_lappend split_def list_of_lconcat)
  ultimately show ?thesis using eq by blast
qed

end

end
