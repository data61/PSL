(*  Title:      JinjaThreads/MM/JMM_Framework.thy
    Author:     Andreas Lochbihler
*)

section \<open>Combination of locales for heap operations and interleaving\<close>

theory JMM_Framework
imports
  JMM_Heap
  "../Framework/FWInitFinLift"
  "../Common/WellForm"
begin

lemma enat_plus_eq_enat_conv: \<comment> \<open>Move to Extended\_Nat\<close>
  "enat m + n = enat k \<longleftrightarrow> k \<ge> m \<and> n = enat (k - m)"
by(cases n) auto

declare convert_new_thread_action_id [simp]

context heap begin

lemma init_fin_lift_state_start_state:
  "init_fin_lift_state s (start_state f P C M vs) = start_state (\<lambda>C M Ts T meth vs. (s, f C M Ts T meth vs)) P C M vs"
by(simp add: start_state_def init_fin_lift_state_def split_beta fun_eq_iff)

lemma non_speculative_start_heap_obs:
  "non_speculative P vs  (llist_of (map snd (lift_start_obs start_tid start_heap_obs)))"
apply(rule non_speculative_nthI)
using start_heap_obs_not_Read
by(clarsimp simp add: lift_start_obs_def lnth_LCons o_def eSuc_enat[symmetric] in_set_conv_nth split: nat.split_asm)

lemma ta_seq_consist_start_heap_obs:
  "ta_seq_consist P Map.empty (llist_of (map snd (lift_start_obs start_tid start_heap_obs)))"
using start_heap_obs_not_Read
by(auto intro: ta_seq_consist_nthI simp add: lift_start_obs_def o_def lnth_LCons in_set_conv_nth split: nat.split_asm)

end

context allocated_heap begin

lemma w_addrs_lift_start_heap_obs:
  "w_addrs (w_values P vs (map snd (lift_start_obs start_tid start_heap_obs))) \<subseteq> w_addrs vs"
by(simp add: lift_start_obs_def o_def w_addrs_start_heap_obs)

end

context heap begin

lemma w_values_start_heap_obs_typeable:
  assumes wf: "wf_syscls P"
  and mrws: "v \<in> w_values P (\<lambda>_. {}) (map snd (lift_start_obs start_tid start_heap_obs)) (ad, al)"
  shows "\<exists>T. P,start_heap \<turnstile> ad@al : T \<and> P,start_heap \<turnstile> v :\<le> T"
proof -
  from in_w_valuesD[OF mrws]
  obtain obs' wa obs'' 
    where eq: "map snd (lift_start_obs start_tid start_heap_obs) = obs' @ wa # obs''"
    and "is_write_action wa"
    and adal: "(ad, al) \<in> action_loc_aux P wa"
    and vwa: "value_written_aux P wa al = v"
    by blast
  from \<open>is_write_action wa\<close> show ?thesis
  proof cases
    case (WriteMem ad' al' v')
    with vwa adal eq have "WriteMem ad al v \<in> set start_heap_obs"
      by(auto simp add: map_eq_append_conv Cons_eq_append_conv lift_start_obs_def)
    thus ?thesis by(rule start_heap_write_typeable)
  next
    case (NewHeapElem ad' hT)
    with vwa adal eq have "NewHeapElem ad hT \<in> set start_heap_obs"
      by(auto simp add: map_eq_append_conv Cons_eq_append_conv lift_start_obs_def)
    hence "typeof_addr start_heap ad = \<lfloor>hT\<rfloor>"
      by(rule NewHeapElem_start_heap_obsD[OF wf])
    thus ?thesis using adal vwa NewHeapElem
      apply(cases hT)
      apply(auto intro!: addr_loc_type.intros dest: has_field_decl_above)
      apply(frule has_field_decl_above)
      apply(auto intro!: addr_loc_type.intros dest: has_field_decl_above)
      done
  qed
qed

lemma start_state_vs_conf:
  "wf_syscls P \<Longrightarrow> vs_conf P start_heap (w_values P (\<lambda>_. {}) (map snd (lift_start_obs start_tid start_heap_obs)))"
by(rule vs_confI)(rule w_values_start_heap_obs_typeable)

end


subsection \<open>JMM traces for Jinja semantics\<close>

context multithreaded_base begin

inductive_set \<E> :: "('l,'t,'x,'m,'w) state \<Rightarrow> ('t \<times> 'o) llist set"
  for \<sigma> :: "('l,'t,'x,'m,'w) state"
where
  "mthr.Runs \<sigma> E'
  \<Longrightarrow> lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E') \<in> \<E> \<sigma>"

lemma actions_\<E>E_aux:
  fixes \<sigma> E'
  defines "E == lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E')"
  assumes mthr: "mthr.Runs \<sigma> E'"
  and a: "enat a < llength E"
  obtains m n t ta
  where "lnth E a = (t, \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n)"
  and "n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" and "enat m < llength E'"
  and "a = (\<Sum>i<m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) + n"
  and "lnth E' m = (t, ta)"
proof -
  from lnth_lconcat_conv[OF a[unfolded E_def], folded E_def]
  obtain m n
    where "lnth E a = lnth (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E') m) n"
    and "enat n < llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E') m)"
    and "enat m < llength (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E')"
    and "enat a = (\<Sum>i<m. llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E') i)) + enat n"
    by blast
  moreover
  obtain t ta where "lnth E' m = (t, ta)" by(cases "lnth E' m")
  ultimately have E_a: "lnth E a = (t, \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n)"
    and n: "n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
    and m: "enat m < llength E'"
    and a: "enat a = (\<Sum>i<m. llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E') i)) + enat n"
    by(simp_all add: lnth_llist_of)
  note a
  also have "(\<Sum>i<m. llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E') i)) = 
            sum (enat \<circ> (\<lambda>i. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>)) {..<m}"
    using m by(simp add: less_trans[where y="enat m"] split_beta)
  also have "\<dots> = enat (\<Sum>i<m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
    by(subst sum_hom)(simp_all add: zero_enat_def)
  finally have a: "a = (\<Sum>i<m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) + n" by simp
  with E_a n m show thesis using \<open>lnth E' m = (t, ta)\<close> by(rule that)
qed

lemma actions_\<E>E:
  assumes E: "E \<in> \<E> \<sigma>"
  and a: "enat a < llength E"
  obtains E' m n t ta
  where "E = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E')"
  and "mthr.Runs \<sigma> E'"
  and "lnth E a = (t, \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n)"
  and "n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" and "enat m < llength E'"
  and "a = (\<Sum>i<m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) + n"
  and "lnth E' m = (t, ta)"
proof -
  from E obtain E' ws
    where E: "E = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E')"
    and "mthr.Runs \<sigma> E'" by(rule \<E>.cases) blast
  from \<open>mthr.Runs \<sigma> E'\<close> a[unfolded E]
  show ?thesis
    by(rule actions_\<E>E_aux)(fold E, rule that[OF E \<open>mthr.Runs \<sigma> E'\<close>])
qed

end

context \<tau>multithreaded_wf begin

text \<open>Alternative characterisation for @{term "\<E>"}\<close>
lemma \<E>_conv_Runs:
  "\<E> \<sigma> = lconcat ` lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ` llist_of_tllist ` {E. mthr.\<tau>Runs \<sigma> E}"
  (is "?lhs = ?rhs")
proof(intro equalityI subsetI)
  fix E
  assume "E \<in> ?rhs"
  then obtain E' where E: "E = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E'))"
    and \<tau>Runs: "mthr.\<tau>Runs \<sigma> E'" by(blast)
  obtain E'' where E': "E' = tmap (\<lambda>(tls, s', tl, s''). tl) (case_sum (\<lambda>(tls, s'). \<lfloor>s'\<rfloor>) Map.empty) E''"
    and \<tau>Runs': "mthr.\<tau>Runs_table2 \<sigma> E''"
    using \<tau>Runs by(rule mthr.\<tau>Runs_into_\<tau>Runs_table2)
  have "mthr.Runs \<sigma> (lconcat (lappend (lmap (\<lambda>(tls, s, tl, s'). llist_of (tls @ [tl])) (llist_of_tllist E'')) 
                                      (LCons (case terminal E'' of Inl (tls, s') \<Rightarrow> llist_of tls | Inr tls \<Rightarrow> tls) LNil)))"
    (is "mthr.Runs _ ?E'''")
    using \<tau>Runs' by(rule mthr.\<tau>Runs_table2_into_Runs)
  moreover 
  let ?tail = "\<lambda>E''. case terminal E'' of Inl (tls, s') \<Rightarrow> llist_of tls | Inr tls \<Rightarrow> tls"
  {
    have "E = lconcat (lfilter (\<lambda>xs. \<not> lnull xs) (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of_tllist E')))"
      unfolding E by(simp add: lconcat_lfilter_neq_LNil)
    also have "\<dots> = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (lmap (\<lambda>(tls, s', tta, s''). tta) (lfilter (\<lambda>(tls, s', (t, ta), s''). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<noteq> []) (llist_of_tllist E''))))"
      by(simp add: E' lfilter_lmap llist.map_comp o_def split_def)
    also
    from \<open>mthr.\<tau>Runs_table2 \<sigma> E''\<close>
    have "lmap (\<lambda>(tls, s', tta, s''). tta) (lfilter (\<lambda>(tls, s', (t, ta), s''). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<noteq> []) (llist_of_tllist E'')) = 
          lfilter (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<noteq> []) (lconcat (lappend (lmap (\<lambda>(tls, s, tl, s'). llist_of (tls @ [tl])) (llist_of_tllist E'')) (LCons (?tail E'') LNil)))"
      (is "?lhs \<sigma> E'' = ?rhs \<sigma> E''")
    proof(coinduction arbitrary: \<sigma> E'' rule: llist.coinduct_strong)
      case (Eq_llist \<sigma> E'')
      have ?lnull
        by(cases "lfinite (llist_of_tllist E'')")(fastforce split: sum.split_asm simp add: split_beta lset_lconcat_lfinite lappend_inf mthr.silent_move2_def dest: mthr.\<tau>Runs_table2_silentsD[OF Eq_llist] mthr.\<tau>Runs_table2_terminal_silentsD[OF Eq_llist] mthr.\<tau>Runs_table2_terminal_inf_stepD[OF Eq_llist] m\<tau>move_silentD inf_step_silentD silent_moves2_silentD split: sum.split_asm)+
      moreover
      have ?LCons
      proof(intro impI conjI)
        assume lhs': "\<not> lnull (lmap (\<lambda>(tls, s', tta, s''). tta) (lfilter (\<lambda>(tls, s', (t, ta), s''). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<noteq> []) (llist_of_tllist E'')))"
          (is "\<not> lnull ?lhs'")
          and "\<not> lnull (lfilter (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<noteq> []) (lconcat (lappend (lmap (\<lambda>(tls, s, tl, s'). llist_of (tls @ [tl])) (llist_of_tllist E'')) (LCons (case terminal E'' of Inl (tls, s') \<Rightarrow> llist_of tls | Inr tls \<Rightarrow> tls) LNil))))"
          (is "\<not> lnull ?rhs'")

        note \<tau>Runs' = \<open>mthr.\<tau>Runs_table2 \<sigma> E''\<close>
        from lhs' obtain tl tls' where "?lhs \<sigma> E'' = LCons tl tls'"
          by(auto simp only: not_lnull_conv)
        then obtain tls s' s'' tlsstlss'
          where tls': "tls' = lmap (\<lambda>(tls, s', tta, s''). tta) tlsstlss'"
          and filter: "lfilter (\<lambda>(tls, s', (t, ta), s''). obs_a ta \<noteq> []) (llist_of_tllist E'') = LCons (tls, s', tl, s'') tlsstlss'"
          using lhs' by(fastforce simp add: lmap_eq_LCons_conv)
        from lfilter_eq_LConsD[OF filter]
        obtain us vs where eq: "llist_of_tllist E'' = lappend us (LCons (tls, s', tl, s'') vs)"
          and fin: "lfinite us"
          and empty: "\<forall>(tls, s', (t, ta), s'')\<in>lset us. obs_a ta = []"
          and neq_empty: "obs_a (snd tl) \<noteq> []"
          and tlsstlss': "tlsstlss' = lfilter (\<lambda>(tls, s', (t, ta), s''). obs_a ta \<noteq> []) vs"
          by(auto simp add: split_beta)
        from eq obtain E''' where E'': "E'' = lappendt us E'''" 
          and eq': "llist_of_tllist E''' = LCons (tls, s', tl, s'') vs"
          and terminal: "terminal E''' = terminal E''"
          unfolding llist_of_tllist_eq_lappend_conv by auto
        from \<tau>Runs' fin E'' obtain \<sigma>' where \<tau>Runs'': "mthr.\<tau>Runs_table2 \<sigma>' E'''"
          by(auto dest: mthr.\<tau>Runs_table2_lappendtD)
        then obtain \<sigma>'' E'''' where "mthr.\<tau>Runs_table2 \<sigma>'' E''''" "E''' = TCons (tls, s', tl, s'') E''''"
          using eq' by cases auto
        moreover from \<tau>Runs' E'' fin
        have "\<forall>(tls, s, tl, s')\<in>lset us. \<forall>(t, ta)\<in>set tls. ta = \<epsilon>"
          by(fastforce dest: mthr.\<tau>Runs_table2_silentsD m\<tau>move_silentD simp add: mthr.silent_move2_def)
        hence "lfilter (\<lambda>(t, ta). obs_a ta \<noteq> []) (lconcat (lmap (\<lambda>(tls, s, tl, s'). llist_of (tls @ [tl])) us)) = LNil"
          using empty by(auto simp add: lfilter_empty_conv lset_lconcat_lfinite split_beta)
        moreover from \<tau>Runs'' eq' have "snd ` set tls \<subseteq> {\<epsilon>}"
          by(cases)(fastforce dest: silent_moves2_silentD)+
        hence "[(t, ta)\<leftarrow>tls . obs_a ta \<noteq> []] = []"
          by(auto simp add: filter_empty_conv split_beta)
        ultimately 
        show "lhd ?lhs' = lhd ?rhs'"
          and "(\<exists>\<sigma> E''. ltl ?lhs' = lmap (\<lambda>(tls, s', tta, s''). tta) (lfilter (\<lambda>(tls, s', (t, ta), s''). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<noteq> []) (llist_of_tllist E'')) \<and>
           ltl ?rhs' = lfilter (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<noteq> []) (lconcat (lappend (lmap (\<lambda>(tls, s, tl, s'). llist_of (tls @ [tl])) (llist_of_tllist E'')) (LCons (case terminal E'' of Inl (tls, s') \<Rightarrow> llist_of tls | Inr tls \<Rightarrow> tls) LNil))) \<and>
           \<tau>trsys.\<tau>Runs_table2 redT m\<tau>move \<sigma> E'') \<or>
          ltl ?lhs' = ltl ?rhs'"
          using lhs' E'' fin tls' tlsstlss' filter eq' neq_empty
          by(auto simp add: lmap_lappend_distrib lappend_assoc split_beta filter_empty_conv simp del: split_paired_Ex)
      qed
      ultimately show ?case ..
    qed
    also have "lmap (\<lambda>(t, ta). llist_of (map (Pair t) (obs_a ta))) \<dots> = lfilter (\<lambda>obs. \<not> lnull obs) (lmap (\<lambda>(t, ta). llist_of (map (Pair t) (obs_a ta))) (lconcat (lappend (lmap (\<lambda>(tls, s, tl, s'). llist_of (tls @ [tl])) (llist_of_tllist E'')) (LCons (?tail E'') LNil))))"
      unfolding lfilter_lmap by(simp add: o_def split_def llist_of_eq_LNil_conv)
    finally have "E = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ?E''')"
      by(simp add: lconcat_lfilter_neq_LNil) }
  ultimately show "E \<in> ?lhs" by(blast intro: \<E>.intros)
next
  fix E
  assume "E \<in> ?lhs"
  then obtain E' where E: "E = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) (obs_a ta))) E')"
    and Runs: "mthr.Runs \<sigma> E'" by(blast elim: \<E>.cases)
  from Runs obtain E'' where E': "E' = lmap (\<lambda>(s, tl, s'). tl) E''"
    and Runs': "mthr.Runs_table \<sigma> E''" by(rule mthr.Runs_into_Runs_table)
  have "mthr.\<tau>Runs \<sigma> (tmap (\<lambda>(s, tl, s'). tl) id (tfilter None (\<lambda>(s, tl, s'). \<not> m\<tau>move s tl s') (tllist_of_llist (Some (llast (LCons \<sigma> (lmap (\<lambda>(s, tl, s'). s') E'')))) E'')))"
    (is "mthr.\<tau>Runs _ ?E'''")
    using Runs' by(rule mthr.Runs_table_into_\<tau>Runs)
  moreover
  have "(\<lambda>(s, (t, ta), s'). obs_a ta \<noteq> []) = (\<lambda>(s, (t, ta), s'). obs_a ta \<noteq> [] \<and> \<not> m\<tau>move s (t, ta) s')"
    by(rule ext)(auto dest: m\<tau>move_silentD)
  hence "E = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) (obs_a ta))) (llist_of_tllist ?E'''))"
    unfolding E E'
    by(subst (1 2) lconcat_lfilter_neq_LNil[symmetric])(simp add: lfilter_lmap lfilter_lfilter o_def split_def)
  ultimately show "E \<in> ?rhs" by(blast)
qed

end

text \<open>Running threads have been started before\<close>

definition Status_no_wait_locks :: "('l,'t,status \<times> 'x) thread_info \<Rightarrow> bool"
where
  "Status_no_wait_locks ts \<longleftrightarrow> 
  (\<forall>t status x ln. ts t = \<lfloor>((status, x), ln)\<rfloor> \<longrightarrow> status \<noteq> Running \<longrightarrow> ln = no_wait_locks)"

lemma Status_no_wait_locks_PreStartD:
  "\<And>ln. \<lbrakk> Status_no_wait_locks ts; ts t = \<lfloor>((PreStart, x), ln)\<rfloor> \<rbrakk> \<Longrightarrow> ln = no_wait_locks"
unfolding Status_no_wait_locks_def by blast

lemma Status_no_wait_locks_FinishedD:
  "\<And>ln. \<lbrakk> Status_no_wait_locks ts; ts t = \<lfloor>((Finished, x), ln)\<rfloor> \<rbrakk> \<Longrightarrow> ln = no_wait_locks"
unfolding Status_no_wait_locks_def by blast

lemma Status_no_wait_locksI:
  "(\<And>t status x ln. \<lbrakk> ts t = \<lfloor>((status, x), ln)\<rfloor>; status = PreStart \<or> status = Finished \<rbrakk> \<Longrightarrow> ln = no_wait_locks)
  \<Longrightarrow> Status_no_wait_locks ts"
unfolding Status_no_wait_locks_def 
apply clarify
apply(case_tac status)
apply auto
done

context heap_base begin

lemma Status_no_wait_locks_start_state:
  "Status_no_wait_locks (thr (init_fin_lift_state status (start_state f P C M vs)))"
by(clarsimp simp add: Status_no_wait_locks_def init_fin_lift_state_def start_state_def split_beta)

end

context multithreaded_base begin

lemma init_fin_preserve_Status_no_wait_locks:
  assumes ok: "Status_no_wait_locks (thr s)"
  and redT: "multithreaded_base.redT init_fin_final init_fin (map NormalAction \<circ> convert_RA) s tta s'"
  shows "Status_no_wait_locks (thr s')"
using redT
proof(cases rule: multithreaded_base.redT.cases[consumes 1, case_names redT_normal redT_acquire])
  case redT_acquire
  with ok show ?thesis
    by(auto intro!: Status_no_wait_locksI dest: Status_no_wait_locks_PreStartD Status_no_wait_locks_FinishedD split: if_split_asm)
next
  case redT_normal
  show ?thesis
  proof(rule Status_no_wait_locksI)
    fix t' status' x' ln'
    assume tst': "thr s' t' = \<lfloor>((status', x'), ln')\<rfloor>"
      and status: "status' = PreStart \<or> status' = Finished"
    show "ln' = no_wait_locks"
    proof(cases "thr s t'")
      case None
      with redT_normal tst' show ?thesis
        by(fastforce elim!: init_fin.cases dest: redT_updTs_new_thread simp add: final_thread.actions_ok_iff split: if_split_asm)
    next
      case (Some sxln)
      obtain status'' x'' ln'' 
        where [simp]: "sxln = ((status'', x''), ln'')" by(cases sxln) auto
      show ?thesis
      proof(cases "fst tta = t'")
        case True
        with redT_normal tst' status show ?thesis by(auto simp add: expand_finfun_eq fun_eq_iff)
      next
        case False
        with tst' redT_normal Some status have "status'' = status'" "ln'' = ln'" 
          by(force dest: redT_updTs_Some simp add: final_thread.actions_ok_iff)+
        with ok Some status show ?thesis
          by(auto dest: Status_no_wait_locks_PreStartD Status_no_wait_locks_FinishedD)
      qed
    qed
  qed
qed

lemma init_fin_Running_InitialThreadAction:
  assumes redT: "multithreaded_base.redT init_fin_final init_fin (map NormalAction \<circ> convert_RA) s tta s'"
  and not_running: "\<And>x ln. thr s t \<noteq> \<lfloor>((Running, x), ln)\<rfloor>"
  and running: "thr s' t = \<lfloor>((Running, x'), ln')\<rfloor>"
  shows "tta = (t, \<lbrace>InitialThreadAction\<rbrace>)"
using redT
proof(cases rule: multithreaded_base.redT.cases[consumes 1, case_names redT_normal redT_acquire])
  case redT_acquire
  with running not_running show ?thesis by(auto split: if_split_asm)
next
  case redT_normal
  show ?thesis
  proof(cases "thr s t")
    case None
    with redT_normal running not_running show ?thesis
      by(fastforce simp add: final_thread.actions_ok_iff elim: init_fin.cases dest: redT_updTs_new_thread split: if_split_asm)
  next
    case (Some a)
    with redT_normal running not_running show ?thesis
      apply(cases a)
      apply(auto simp add: final_thread.actions_ok_iff split: if_split_asm elim: init_fin.cases)
      apply((drule (1) redT_updTs_Some)?, fastforce)+
      done
  qed
qed

end

context if_multithreaded begin

lemma init_fin_Trsys_preserve_Status_no_wait_locks:
  assumes ok: "Status_no_wait_locks (thr s)"
  and Trsys: "if.mthr.Trsys s ttas s'"
  shows "Status_no_wait_locks (thr s')"
using Trsys ok
by(induct)(blast dest: init_fin_preserve_Status_no_wait_locks)+

lemma init_fin_Trsys_Running_InitialThreadAction:
  assumes redT: "if.mthr.Trsys s ttas s'"
  and not_running: "\<And>x ln. thr s t \<noteq> \<lfloor>((Running, x), ln)\<rfloor>"
  and running: "thr s' t = \<lfloor>((Running, x'), ln')\<rfloor>"
  shows "(t, \<lbrace>InitialThreadAction\<rbrace>) \<in> set ttas"
using redT not_running running
proof(induct arbitrary: x' ln')
  case rtrancl3p_refl thus ?case by(fastforce)
next
  case (rtrancl3p_step s ttas s' tta s'') thus ?case
    by(cases "\<exists>x ln. thr s' t = \<lfloor>((Running, x), ln)\<rfloor>")(fastforce dest: init_fin_Running_InitialThreadAction)+
qed

end

locale heap_multithreaded_base =
  heap_base
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write 
  +
  mthr: multithreaded_base final r convert_RA
  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and spurious_wakeups :: bool
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool" 
  and final :: "'x \<Rightarrow> bool"
  and r :: "('addr, 'thread_id, 'x, 'heap, 'addr, ('addr, 'thread_id) obs_event) semantics" ("_ \<turnstile> _ -_\<rightarrow> _" [50,0,0,50] 80) 
  and convert_RA :: "'addr released_locks \<Rightarrow> ('addr, 'thread_id) obs_event list"

sublocale heap_multithreaded_base < mthr: if_multithreaded_base final r convert_RA
.

context heap_multithreaded_base begin

abbreviation \<E>_start ::
  "(cname \<Rightarrow> mname \<Rightarrow> ty list \<Rightarrow> ty \<Rightarrow> 'md \<Rightarrow> 'addr val list \<Rightarrow> 'x) 
  \<Rightarrow> 'md prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> 'addr val list \<Rightarrow> status 
  \<Rightarrow> ('thread_id \<times> ('addr, 'thread_id) obs_event action) llist set"
where
  "\<E>_start f P C M vs status \<equiv> 
  lappend (llist_of (lift_start_obs start_tid start_heap_obs)) ` 
  mthr.if.\<E> (init_fin_lift_state status (start_state f P C M vs))"

end

locale heap_multithreaded =
  heap_multithreaded_base 
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write
    final r convert_RA
  +
  heap
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write 
    P 
  + 
  mthr: multithreaded final r convert_RA

  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and spurious_wakeups :: bool
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool" 
  and final :: "'x \<Rightarrow> bool"
  and r :: "('addr, 'thread_id, 'x, 'heap, 'addr, ('addr, 'thread_id) obs_event) semantics" ("_ \<turnstile> _ -_\<rightarrow> _" [50,0,0,50] 80) 
  and convert_RA :: "'addr released_locks \<Rightarrow> ('addr, 'thread_id) obs_event list" 
  and P :: "'md prog"

sublocale heap_multithreaded < mthr: if_multithreaded final r convert_RA
by(unfold_locales)

sublocale heap_multithreaded < "if": jmm_multithreaded
  mthr.init_fin_final mthr.init_fin "map NormalAction \<circ> convert_RA" P
.

context heap_multithreaded begin

lemma thread_start_actions_ok_init_fin_RedT:
  assumes Red: "mthr.if.RedT (init_fin_lift_state status (start_state f P C M vs)) ttas s'"
           (is "mthr.if.RedT ?start_state _ _")
  shows "thread_start_actions_ok (llist_of (lift_start_obs start_tid start_heap_obs @ concat (map (\<lambda>(t, ta). map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
   (is "thread_start_actions_ok (llist_of (?obs_prefix @ ?E'))")
proof(rule thread_start_actions_okI)
  let ?E = "llist_of (?obs_prefix @ ?E')"
  fix a
  assume a: "a \<in> actions ?E"
    and new: "\<not> is_new_action (action_obs ?E a)"
  show "\<exists>i \<le> a. action_obs ?E i = InitialThreadAction \<and> action_tid ?E i = action_tid ?E a"
  proof(cases "action_tid ?E a = start_tid")
    case True thus ?thesis
      by(auto simp add: lift_start_obs_def action_tid_def action_obs_def)
  next
    case False
    let ?a = "a - length ?obs_prefix"

    from False have a_len: "a \<ge> length ?obs_prefix"
      by(rule contrapos_np)(auto simp add: lift_start_obs_def action_tid_def lnth_LCons nth_append split: nat.split)
    hence [simp]: "action_tid ?E a = action_tid (llist_of ?E') ?a" "action_obs ?E a = action_obs (llist_of ?E') ?a"
      by(simp_all add: action_tid_def nth_append action_obs_def)

    from False have not_running: "\<And>x ln. thr ?start_state (action_tid (llist_of ?E') ?a) \<noteq> \<lfloor>((Running, x), ln)\<rfloor>"
      by(auto simp add: start_state_def split_beta init_fin_lift_state_def split: if_split_asm)
    
    from a a_len have "?a < length ?E'" by(simp add: actions_def)
    from nth_concat_conv[OF this]
    obtain m n where E'_a: "?E' ! ?a = (\<lambda>(t, ta). (t, \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n)) (ttas ! m)"
      and n: "n < length \<lbrace>snd (ttas ! m)\<rbrace>\<^bsub>o\<^esub>"
      and m: "m < length ttas"
      and a_conv: "?a = (\<Sum>i<m. length (map (\<lambda>(t, ta). map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas ! i)) + n"
      by(clarsimp simp add: split_def)

    from Red obtain s'' s''' where Red1: "mthr.if.RedT ?start_state (take m ttas) s''"
      and red: "mthr.if.redT s'' (ttas ! m) s'''"
      and Red2: "mthr.if.RedT s''' (drop (Suc m) ttas) s'"
      unfolding mthr.if.RedT_def
      by(subst (asm) (4) id_take_nth_drop[OF m])(blast elim: rtrancl3p_appendE rtrancl3p_converseE)

    from E'_a m n have [simp]: "action_tid (llist_of ?E') ?a = fst (ttas ! m)"
      by(simp add: action_tid_def split_def)
    
    from red obtain status x ln where tst: "thr s'' (fst (ttas ! m)) = \<lfloor>((status, x), ln)\<rfloor>" by cases auto
    show ?thesis
    proof(cases "status = PreStart \<or> status = Finished")
      case True
      from Red1 have "Status_no_wait_locks (thr s'')"
        unfolding mthr.if.RedT_def
        by(rule mthr.init_fin_Trsys_preserve_Status_no_wait_locks[OF Status_no_wait_locks_start_state])
      with True tst have "ln = no_wait_locks"
        by(auto dest: Status_no_wait_locks_PreStartD Status_no_wait_locks_FinishedD)
      with red tst True have "\<lbrace>snd (ttas ! m)\<rbrace>\<^bsub>o\<^esub> = [InitialThreadAction]" by(cases) auto
      hence "action_obs ?E a = InitialThreadAction" using a_conv n a_len E'_a
        by(simp add: action_obs_def nth_append split_beta)
      thus ?thesis by(auto)
    next
      case False
      hence "status = Running" by(cases status) auto
      with tst mthr.init_fin_Trsys_Running_InitialThreadAction[OF Red1[unfolded mthr.if.RedT_def] not_running]
      have "(fst (ttas ! m), \<lbrace>InitialThreadAction\<rbrace>) \<in> set (take m ttas)"
        using E'_a by(auto simp add: action_tid_def split_beta)
      then obtain i where i: "i < m" 
        and nth_i: "ttas ! i = (fst (ttas ! m), \<lbrace>InitialThreadAction\<rbrace>)"
        unfolding in_set_conv_nth by auto

      let ?i' = "length (concat (map (\<lambda>(t, ta). map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (take i ttas)))"
      let ?i = "length ?obs_prefix + ?i'"

      from i m nth_i
      have "?i' < length (concat (map (\<lambda>(t, ta). map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (take m ttas)))"
        apply(simp add: length_concat o_def split_beta)
        apply(subst (6) id_take_nth_drop[where i=i])
        apply(simp_all add: take_map[symmetric] min_def)
        done
      also from m have "\<dots> \<le> ?a" unfolding a_conv
        by(simp add: length_concat sum_list_sum_nth min_def split_def atLeast0LessThan)
      finally have "?i < a" using a_len by simp
      moreover
      from i m nth_i have "?i' < length ?E'"
        apply(simp add: length_concat o_def split_def)
        apply(subst (7) id_take_nth_drop[where i=i])
        apply(simp_all add: take_map[symmetric])
        done
      from nth_i i E'_a a_conv m
      have "lnth ?E ?i = (fst (ttas ! m), InitialThreadAction)"
        by(simp add: lift_start_obs_def nth_append length_concat o_def split_def)(rule nth_concat_eqI[where k=0 and i=i], simp_all add: take_map o_def split_def)
      ultimately show ?thesis using E'_a
        by(cases "ttas ! m")(auto simp add: action_obs_def action_tid_def nth_append intro!: exI[where x="?i"])
    qed
  qed
qed

(* TODO: use previous lemma for proof *)

lemma thread_start_actions_ok_init_fin:
  assumes E: "E \<in> mthr.if.\<E> (init_fin_lift_state status (start_state f P C M vs))"
  shows "thread_start_actions_ok (lappend (llist_of (lift_start_obs start_tid start_heap_obs)) E)"
  (is "thread_start_actions_ok ?E")
proof(rule thread_start_actions_okI)
  let ?start_heap_obs = "lift_start_obs start_tid start_heap_obs"
  let ?start_state = "init_fin_lift_state status (start_state f P C M vs)"
  fix a
  assume a: "a \<in> actions ?E"
    and a_new: "\<not> is_new_action (action_obs ?E a)"
  show "\<exists>i. i \<le> a \<and> action_obs ?E i = InitialThreadAction \<and> action_tid ?E i = action_tid ?E a"
  proof(cases "action_tid ?E a = start_tid")
    case True thus ?thesis
      by(auto simp add: lift_start_obs_def action_tid_def action_obs_def)
  next
    case False

    let ?a = "a - length ?start_heap_obs"

    from False have "a \<ge> length ?start_heap_obs"
      by(rule contrapos_np)(auto simp add: lift_start_obs_def action_tid_def lnth_LCons lnth_lappend1 split: nat.split)
    hence [simp]: "action_tid ?E a = action_tid E ?a" "action_obs ?E a = action_obs E ?a"
      by(simp_all add: action_tid_def lnth_lappend2 action_obs_def)

    from False have not_running: "\<And>x ln. thr ?start_state (action_tid E ?a) \<noteq> \<lfloor>((Running, x), ln)\<rfloor>"
      by(auto simp add: start_state_def split_beta init_fin_lift_state_def split: if_split_asm)
    
    from E obtain E' where E': "E = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E')"
      and \<tau>Runs: "mthr.if.mthr.Runs ?start_state E'" by(rule mthr.if.\<E>.cases)
    from a E' \<open>a \<ge> length ?start_heap_obs\<close>
    have enat_a: "enat ?a < llength (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E'))"
      by(cases "llength (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E'))")(auto simp add: actions_def)
    with \<tau>Runs obtain m n t ta
    where a_obs: "lnth (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E')) (a - length ?start_heap_obs) = (t, \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n)"
      and n: "n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" 
      and m: "enat m < llength E'"
      and a_conv: "?a = (\<Sum>i<m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) + n"
      and E'_m: "lnth E' m = (t, ta)"
      by(rule mthr.if.actions_\<E>E_aux)
    from a_obs have [simp]: "action_tid E ?a = t" "action_obs E ?a = \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n"
      by(simp_all add: E' action_tid_def action_obs_def)

    let ?E' = "ldropn (Suc m) E'"
    let ?m_E' = "ltake (enat m) E'"
    have E'_unfold: "E' = lappend (ltake (enat m) E') (LCons (lnth E' m) ?E')"
      unfolding ldropn_Suc_conv_ldropn[OF m] by simp
    hence "mthr.if.mthr.Runs ?start_state (lappend ?m_E' (LCons (lnth E' m) ?E'))"
      using \<tau>Runs by simp
    then obtain \<sigma>' where \<sigma>_\<sigma>': "mthr.if.mthr.Trsys ?start_state (list_of ?m_E') \<sigma>'"
      and \<tau>Runs': "mthr.if.mthr.Runs \<sigma>' (LCons (lnth E' m) ?E')"
      by(rule mthr.if.mthr.Runs_lappendE) simp
    from \<tau>Runs' obtain \<sigma>''' where red_a: "mthr.if.redT \<sigma>' (t, ta) \<sigma>'''"
      and \<tau>Runs'': "mthr.if.mthr.Runs \<sigma>''' ?E'"
      unfolding E'_m by cases
    from red_a obtain status x ln where tst: "thr \<sigma>' t = \<lfloor>((status, x), ln)\<rfloor>" by cases auto
    show ?thesis
    proof(cases "status = PreStart \<or> status = Finished")
      case True
      have "Status_no_wait_locks (thr \<sigma>')"
        by(rule mthr.init_fin_Trsys_preserve_Status_no_wait_locks[OF _ \<sigma>_\<sigma>'])(rule Status_no_wait_locks_start_state)
      with True tst have "ln = no_wait_locks"
        by(auto dest: Status_no_wait_locks_PreStartD Status_no_wait_locks_FinishedD)
      with red_a tst True have "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = [InitialThreadAction]" by(cases) auto
      hence "action_obs E ?a = InitialThreadAction" using a_obs n unfolding E'
        by(simp add: action_obs_def)
      thus ?thesis by(auto)
    next
      case False
      hence "status = Running" by(cases status) auto
      with tst mthr.init_fin_Trsys_Running_InitialThreadAction[OF \<sigma>_\<sigma>' not_running]
      have "(action_tid E ?a, \<lbrace>InitialThreadAction\<rbrace>) \<in> set (list_of (ltake (enat m) E'))"
        using a_obs E' by(auto simp add: action_tid_def)
      then obtain i where "i < m" "enat i < llength E'" 
        and nth_i: "lnth E' i = (action_tid E ?a, \<lbrace>InitialThreadAction\<rbrace>)"
        unfolding in_set_conv_nth 
        by(cases "llength E'")(auto simp add: length_list_of_conv_the_enat lnth_ltake)

      let ?i' = "\<Sum>i<i. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>"
      let ?i = "length ?start_heap_obs + ?i'"

      from \<open>i < m\<close> have "(\<Sum>i<m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) = ?i' + (\<Sum>i=i..<m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
        unfolding atLeast0LessThan[symmetric] by(subst sum.atLeastLessThan_concat) simp_all
      hence "?i' \<le> ?a" unfolding a_conv by simp
      hence "?i \<le> a" using \<open>a \<ge> length ?start_heap_obs\<close> by arith


      from \<open>?i' \<le> ?a\<close> have "enat ?i' < llength E" using enat_a E'
        by(simp add: le_less_trans[where y="enat ?a"])
      from lnth_lconcat_conv[OF this[unfolded E'], folded E']
      obtain k l 
        where nth_i': "lnth E ?i' = lnth (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E') k) l"
        and l: "l < length \<lbrace>snd (lnth E' k)\<rbrace>\<^bsub>o\<^esub>"
        and k: "enat k < llength E'"
        and i_conv: "enat ?i' = (\<Sum>i<k. llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E') i)) + enat l"
        by(fastforce simp add: split_beta)

      have "(\<Sum>i<k. llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E') i)) =
            (\<Sum>i<k. (enat \<circ> (\<lambda>i. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>)) i)"
        by(rule sum.cong)(simp_all add: less_trans[where y="enat k"] split_beta k)
      also have "\<dots> = enat (\<Sum>i<k. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
        by(rule sum_hom)(simp_all add: zero_enat_def)
      finally have i_conv: "?i' = (\<Sum>i<k. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) + l" using i_conv by simp

      have [simp]: "i = k"
      proof(rule ccontr)
        assume "i \<noteq> k"
        thus False unfolding neq_iff
        proof
          assume "i < k"
          hence "(\<Sum>i<k. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) = 
                 (\<Sum>i<i. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) + (\<Sum>i=i..<k. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
            unfolding atLeast0LessThan[symmetric] by(subst sum.atLeastLessThan_concat) simp_all
          with i_conv have "(\<Sum>i=i..<k. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) = l" "l = 0" by simp_all
          moreover have "(\<Sum>i=i..<k. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) \<ge> length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>"
            by(subst sum.atLeast_Suc_lessThan[OF \<open>i < k\<close>]) simp
          ultimately show False using nth_i by simp
        next
          assume "k < i"
          hence "?i' = (\<Sum>i<k. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) + (\<Sum>i=k..<i. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
            unfolding atLeast0LessThan[symmetric] by(subst sum.atLeastLessThan_concat) simp_all
          with i_conv have "(\<Sum>i=k..<i. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) = l" by simp
          moreover have "(\<Sum>i=k..<i. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) \<ge> length \<lbrace>snd (lnth E' k)\<rbrace>\<^bsub>o\<^esub>"
            by(subst sum.atLeast_Suc_lessThan[OF \<open>k < i\<close>]) simp
          ultimately show False using l by simp
        qed
      qed
      with l nth_i have [simp]: "l = 0" by simp
      
      hence "lnth E ?i' = (action_tid E ?a, InitialThreadAction)"
        using nth_i nth_i' k by simp
      with \<open>?i \<le> a\<close> show ?thesis
        by(auto simp add: action_tid_def action_obs_def lnth_lappend2)
    qed
  qed
qed



end

text \<open>In the subsequent locales, \<open>convert_RA\<close> refers to @{term "convert_RA"} and is no longer a parameter!\<close>

lemma convert_RA_not_write:
  "\<And>ln. ob \<in> set (convert_RA ln) \<Longrightarrow> \<not> is_write_action (NormalAction ob)"
by(auto simp add: convert_RA_def)

lemma ta_seq_consist_convert_RA:
  fixes ln shows
  "ta_seq_consist P vs (llist_of ((map NormalAction \<circ> convert_RA) ln))"
proof(rule ta_seq_consist_nthI)
  fix i ad al v
  assume "enat i < llength (llist_of ((map NormalAction \<circ> convert_RA) ln :: ('b, 'c) obs_event action list))"
    and "lnth (llist_of ((map NormalAction \<circ> convert_RA) ln :: ('b, 'c) obs_event action list)) i = NormalAction (ReadMem ad al v)"
  hence "ReadMem ad al v \<in> set (convert_RA ln :: ('b, 'c) obs_event list)"
    by(auto simp add: in_set_conv_nth)
  hence False by(auto simp add: convert_RA_def)
  thus "\<exists>b. mrw_values P vs (list_of (ltake (enat i) (llist_of ((map NormalAction \<circ> convert_RA) ln)))) (ad, al) = \<lfloor>(v, b)\<rfloor>" ..
qed

lemma ta_hb_consistent_convert_RA:
  "\<And>ln. ta_hb_consistent P E (llist_of (map (Pair t) ((map NormalAction \<circ> convert_RA) ln)))"
by(rule ta_hb_consistent_not_ReadI)(auto simp add: convert_RA_def)

locale allocated_multithreaded =
  allocated_heap
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write 
    allocated
    P 
  + 
  mthr: multithreaded final r convert_RA

  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and spurious_wakeups :: bool
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool" 
  and allocated :: "'heap \<Rightarrow> 'addr set"
  and final :: "'x \<Rightarrow> bool"
  and r :: "('addr, 'thread_id, 'x, 'heap, 'addr, ('addr, 'thread_id) obs_event) semantics" ("_ \<turnstile> _ -_\<rightarrow> _" [50,0,0,50] 80) 
  and P :: "'md prog"
  +
  assumes red_allocated_mono: "t \<turnstile> (x, m) -ta\<rightarrow> (x', m') \<Longrightarrow> allocated m \<subseteq> allocated m'"
  and red_New_allocatedD:
  "\<lbrakk> t \<turnstile> (x, m) -ta\<rightarrow> (x', m'); NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> ad \<in> allocated m' \<and> ad \<notin> allocated m"
  and red_allocated_NewD:
  "\<lbrakk> t \<turnstile> (x, m) -ta\<rightarrow> (x', m'); ad \<in> allocated m'; ad \<notin> allocated m \<rbrakk>
  \<Longrightarrow> \<exists>CTn. NewHeapElem ad CTn \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  and red_New_same_addr_same:
  "\<lbrakk> t \<turnstile> (x, m) -ta\<rightarrow> (x', m'); 
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NewHeapElem a CTn; i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>;
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NewHeapElem a CTn'; j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> i = j"


sublocale allocated_multithreaded < heap_multithreaded
  addr2thread_id thread_id2addr
  spurious_wakeups
  empty_heap allocate typeof_addr heap_read heap_write
  final r convert_RA P
by(unfold_locales)

context allocated_multithreaded begin

lemma redT_allocated_mono:
  assumes "mthr.redT \<sigma> (t, ta) \<sigma>'"
  shows "allocated (shr \<sigma>) \<subseteq> allocated (shr \<sigma>')"
using assms
by cases(auto dest: red_allocated_mono del: subsetI)

lemma RedT_allocated_mono:
  assumes "mthr.RedT \<sigma> ttas \<sigma>'"
  shows "allocated (shr \<sigma>) \<subseteq> allocated (shr \<sigma>')"
using assms unfolding mthr.RedT_def
by induct(auto dest!: redT_allocated_mono intro: subset_trans del: subsetI)

lemma init_fin_allocated_mono:
  "t \<turnstile> (x, m) -ta\<rightarrow>i (x', m') \<Longrightarrow> allocated m \<subseteq> allocated m'"
by(cases rule: mthr.init_fin.cases)(auto dest: red_allocated_mono)

lemma init_fin_redT_allocated_mono:
  assumes "mthr.if.redT \<sigma> (t, ta) \<sigma>'"
  shows "allocated (shr \<sigma>) \<subseteq> allocated (shr \<sigma>')"
using assms
by cases(auto dest: init_fin_allocated_mono del: subsetI)

lemma init_fin_RedT_allocated_mono:
  assumes "mthr.if.RedT \<sigma> ttas \<sigma>'"
  shows "allocated (shr \<sigma>) \<subseteq> allocated (shr \<sigma>')"
using assms unfolding mthr.if.RedT_def
by induct(auto dest!: init_fin_redT_allocated_mono intro: subset_trans del: subsetI)

lemma init_fin_red_New_allocatedD:
  assumes "t \<turnstile> (x, m) -ta\<rightarrow>i (x', m')" "NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  shows "ad \<in> allocated m' \<and> ad \<notin> allocated m"
using assms
by cases(auto dest: red_New_allocatedD)

lemma init_fin_red_allocated_NewD:
  assumes "t \<turnstile> (x, m) -ta\<rightarrow>i (x', m')" "ad \<in> allocated m'" "ad \<notin> allocated m"
  shows "\<exists>CTn. NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
using assms
by(cases)(auto dest!: red_allocated_NewD)

lemma init_fin_red_New_same_addr_same:
  assumes "t \<turnstile> (x, m) -ta\<rightarrow>i (x', m')"
  and "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NormalAction (NewHeapElem a CTn)" "i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  and "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! j = NormalAction (NewHeapElem a CTn')" "j < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  shows "i = j"
using assms
by cases(auto dest: red_New_same_addr_same)

lemma init_fin_redT_allocated_NewHeapElemD:
  assumes  "mthr.if.redT s (t, ta) s'"
  and "ad \<in> allocated (shr s')"
  and "ad \<notin> allocated (shr s)"
  shows "\<exists>CTn. NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
using assms
by(cases)(auto dest: init_fin_red_allocated_NewD)

lemma init_fin_RedT_allocated_NewHeapElemD:
  assumes "mthr.if.RedT s ttas s'"
  and "ad \<in> allocated (shr s')"
  and "ad \<notin> allocated (shr s)"
  shows "\<exists>t ta CTn. (t, ta) \<in> set ttas \<and> NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
using assms
proof(induct rule: mthr.if.RedT_induct')
  case refl thus ?case by simp
next
  case (step ttas s' t ta s'') thus ?case
    by(cases "ad \<in> allocated (shr s')")(fastforce simp del: split_paired_Ex dest: init_fin_redT_allocated_NewHeapElemD)+
qed

lemma \<E>_new_actions_for_unique:
  assumes E: "E \<in> \<E>_start f P C M vs status"
  and a: "a \<in> new_actions_for P E adal"
  and a': "a' \<in> new_actions_for P E adal"
  shows "a = a'"
using a a'
proof(induct a a' rule: wlog_linorder_le)
  case symmetry thus ?case by simp
next
  case (le a a')
  note a = \<open>a \<in> new_actions_for P E adal\<close>
    and a' = \<open>a' \<in> new_actions_for P E adal\<close>
    and a_a' = \<open>a \<le> a'\<close>
  obtain ad al where adal: "adal = (ad, al)" by(cases adal)
  
  let ?init_obs = "lift_start_obs start_tid start_heap_obs"
  let ?start_state = "init_fin_lift_state status (start_state f P C M vs)"

  have distinct: "distinct (filter (\<lambda>obs. \<exists>a CTn. obs = NormalAction (NewHeapElem a CTn)) (map snd ?init_obs))"
    unfolding start_heap_obs_def
    by(fastforce intro: inj_onI intro!: distinct_filter simp add: distinct_map distinct_zipI1 distinct_initialization_list)

  from start_addrs_allocated
  have dom_start_state: "{a. \<exists>CTn. NormalAction (NewHeapElem a CTn) \<in> snd ` set ?init_obs} \<subseteq> allocated (shr ?start_state)"
    by(fastforce simp add: init_fin_lift_state_conv_simps shr_start_state dest: NewHeapElem_start_heap_obs_start_addrsD subsetD)
  
  show ?case
  proof(cases "a' < length ?init_obs")
    case True
    with a' adal E obtain t_a' CTn_a'
      where CTn_a': "?init_obs ! a' = (t_a', NormalAction (NewHeapElem ad CTn_a'))"
      by(cases "?init_obs ! a'")(fastforce elim!: is_new_action.cases action_loc_aux_cases simp add: action_obs_def lnth_lappend1 new_actions_for_def )+
    from True a_a' have len_a: "a < length ?init_obs" by simp
    with a adal E obtain t_a CTn_a
      where CTn_a: "?init_obs ! a = (t_a, NormalAction (NewHeapElem ad CTn_a))"
      by(cases "?init_obs ! a")(fastforce elim!: is_new_action.cases action_loc_aux_cases simp add: action_obs_def lnth_lappend1 new_actions_for_def )+
    from CTn_a CTn_a' True len_a
    have "NormalAction (NewHeapElem ad CTn_a') \<in> snd ` set ?init_obs"
      and "NormalAction (NewHeapElem ad CTn_a) \<in> snd ` set ?init_obs" unfolding set_conv_nth
      by(fastforce intro: rev_image_eqI)+
    hence [simp]: "CTn_a' = CTn_a" using distinct_start_addrs'
      by(auto simp add: in_set_conv_nth distinct_conv_nth start_heap_obs_def start_addrs_def) blast
    from distinct_filterD[OF distinct, of a' a "NormalAction (NewHeapElem ad CTn_a)"] len_a True CTn_a CTn_a'
    show "a = a'" by simp
  next
    case False
    obtain n where n: "length ?init_obs = n" by blast
    with False have "n \<le> a'" by simp
    
    from E obtain E'' where E: "E = lappend (llist_of ?init_obs) E''"
      and E'': "E'' \<in> mthr.if.\<E> ?start_state" by auto
    from E'' obtain E' where E': "E'' = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E')"
      and \<tau>Runs: "mthr.if.mthr.Runs ?start_state E'" by(rule mthr.if.\<E>.cases)
    
    from E E'' a' n \<open>n \<le> a'\<close> adal have a': "a' - n \<in> new_actions_for P E'' adal"
      by(auto simp add: new_actions_for_def lnth_lappend2 action_obs_def actions_lappend elim: actionsE)
    
    from a' have "a' - n \<in> actions E''" by(auto elim: new_actionsE)
    hence "enat (a' - n) < llength E''" by(rule actionsE)
    with \<tau>Runs obtain a'_m a'_n t_a' ta_a'
      where E_a': "lnth E'' (a' - n) = (t_a', \<lbrace>ta_a'\<rbrace>\<^bsub>o\<^esub> ! a'_n)"
      and a'_n: "a'_n < length \<lbrace>ta_a'\<rbrace>\<^bsub>o\<^esub>" and a'_m: "enat a'_m < llength E'"
      and a'_conv: "a' - n = (\<Sum>i<a'_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) + a'_n"
      and E'_a'_m: "lnth E' a'_m = (t_a', ta_a')"
      unfolding E' by(rule mthr.if.actions_\<E>E_aux)
    
    from a' have "is_new_action (action_obs E'' (a' - n))"
      and "(ad, al) \<in> action_loc P E'' (a' - n)"
      unfolding adal by(auto elim: new_actionsE)
    then obtain CTn'
      where "action_obs E'' (a' - n) = NormalAction (NewHeapElem ad CTn')"
      by cases(fastforce)+
    hence New_ta_a': "\<lbrace>ta_a'\<rbrace>\<^bsub>o\<^esub> ! a'_n = NormalAction (NewHeapElem ad CTn')"
      using E_a' a'_n unfolding action_obs_def by simp

    show ?thesis
    proof(cases "a < n")
      case True
      with a adal E n obtain t_a CTn_a where "?init_obs ! a = (t_a, NormalAction (NewHeapElem ad CTn_a))"
        by(cases "?init_obs ! a")(fastforce elim!: is_new_action.cases simp add: action_obs_def lnth_lappend1 new_actions_for_def)+

      with subsetD[OF dom_start_state, of ad] n True
      have a_shr_\<sigma>: "ad \<in> allocated (shr ?start_state)"
        by(fastforce simp add: set_conv_nth intro: rev_image_eqI)
      
      have E'_unfold': "E' = lappend (ltake (enat a'_m) E') (LCons (lnth E' a'_m) (ldropn (Suc a'_m) E'))"
        unfolding ldropn_Suc_conv_ldropn[OF a'_m] by simp
      hence "mthr.if.mthr.Runs ?start_state (lappend (ltake (enat a'_m) E') (LCons (lnth E' a'_m) (ldropn (Suc a'_m) E')))"
        using \<tau>Runs by simp

      then obtain \<sigma>'
        where \<sigma>_\<sigma>': "mthr.if.mthr.Trsys ?start_state (list_of (ltake (enat a'_m) E')) \<sigma>'"
        and \<tau>Runs': "mthr.if.mthr.Runs \<sigma>' (LCons (lnth E' a'_m) (ldropn (Suc a'_m) E'))"
        by(rule mthr.if.mthr.Runs_lappendE) simp
      from \<tau>Runs' obtain \<sigma>''
        where red_a': "mthr.if.redT \<sigma>' (t_a', ta_a') \<sigma>''"
        and \<tau>Runs'': "mthr.if.mthr.Runs \<sigma>'' (ldropn (Suc a'_m) E')"
        unfolding E'_a'_m by cases
      from New_ta_a' a'_n have "NormalAction (NewHeapElem ad CTn') \<in> set \<lbrace>ta_a'\<rbrace>\<^bsub>o\<^esub>"
        unfolding in_set_conv_nth by blast
      with red_a' obtain x_a' x'_a' m'_a' 
        where red'_a': "mthr.init_fin t_a' (x_a', shr \<sigma>') ta_a' (x'_a', m'_a')"
        and \<sigma>''': "redT_upd \<sigma>' t_a' ta_a' x'_a' m'_a' \<sigma>''"
        and ts_t_a': "thr \<sigma>' t_a' = \<lfloor>(x_a', no_wait_locks)\<rfloor>"
        by cases auto
      from red'_a' \<open>NormalAction (NewHeapElem ad CTn') \<in> set \<lbrace>ta_a'\<rbrace>\<^bsub>o\<^esub>\<close>
      obtain ta'_a' X_a' X'_a'
        where x_a': "x_a' = (Running, X_a')"
        and x'_a': "x'_a' = (Running, X'_a')"
        and ta_a': "ta_a' = convert_TA_initial (convert_obs_initial ta'_a')"
        and red''_a': "t_a' \<turnstile> \<langle>X_a', shr \<sigma>'\<rangle> -ta'_a'\<rightarrow> \<langle>X'_a', m'_a'\<rangle>"
        by cases fastforce+
      
      from ta_a' New_ta_a' a'_n have New_ta'_a': "\<lbrace>ta'_a'\<rbrace>\<^bsub>o\<^esub> ! a'_n = NewHeapElem ad CTn'"
        and a'_n': "a'_n < length \<lbrace>ta'_a'\<rbrace>\<^bsub>o\<^esub>" by auto
      hence "NewHeapElem ad CTn' \<in> set \<lbrace>ta'_a'\<rbrace>\<^bsub>o\<^esub>" unfolding in_set_conv_nth by blast
      with red''_a' have allocated_ad': "ad \<notin> allocated (shr \<sigma>')"
        by(auto dest: red_New_allocatedD)
      
      have "allocated (shr ?start_state) \<subseteq> allocated (shr \<sigma>')"
        using \<sigma>_\<sigma>' unfolding mthr.if.RedT_def[symmetric] by(rule init_fin_RedT_allocated_mono)
      hence False using allocated_ad' a_shr_\<sigma> by blast
      thus ?thesis ..
    next
      case False
      hence "n \<le> a" by simp

      from E E'' a n \<open>n \<le> a\<close> adal have a: "a - n \<in> new_actions_for P E'' adal"
        by(auto simp add: new_actions_for_def lnth_lappend2 action_obs_def actions_lappend elim: actionsE)

      from a have "a - n \<in> actions E''" by(auto elim: new_actionsE)
      hence "enat (a - n) < llength E''" by(rule actionsE)

      with \<tau>Runs obtain a_m a_n t_a ta_a 
        where E_a: "lnth E'' (a - n) = (t_a, \<lbrace>ta_a\<rbrace>\<^bsub>o\<^esub> ! a_n)"
        and a_n: "a_n < length \<lbrace>ta_a\<rbrace>\<^bsub>o\<^esub>" and a_m: "enat a_m < llength E'"
        and a_conv: "a - n = (\<Sum>i<a_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) + a_n"
        and E'_a_m: "lnth E' a_m = (t_a, ta_a)"
        unfolding E' by(rule mthr.if.actions_\<E>E_aux)
  
      from a have "is_new_action (action_obs E'' (a - n))" 
        and "(ad, al) \<in> action_loc P E'' (a - n)" 
        unfolding adal by(auto elim: new_actionsE)
      then obtain CTn where "action_obs E'' (a - n) = NormalAction (NewHeapElem ad CTn)"
        by cases(fastforce)+
      hence New_ta_a: " \<lbrace>ta_a\<rbrace>\<^bsub>o\<^esub> ! a_n = NormalAction (NewHeapElem ad CTn)"
        using E_a a_n unfolding action_obs_def by simp
      
      let ?E' = "ldropn (Suc a_m) E'"
  
      have E'_unfold: "E' = lappend (ltake (enat a_m) E') (LCons (lnth E' a_m) ?E')"
        unfolding ldropn_Suc_conv_ldropn[OF a_m] by simp
      hence "mthr.if.mthr.Runs ?start_state (lappend (ltake (enat a_m) E') (LCons (lnth E' a_m) ?E'))"
        using \<tau>Runs by simp
      then obtain \<sigma>' where \<sigma>_\<sigma>': "mthr.if.mthr.Trsys ?start_state (list_of (ltake (enat a_m) E')) \<sigma>'"
        and \<tau>Runs': "mthr.if.mthr.Runs \<sigma>' (LCons (lnth E' a_m) ?E')"
        by(rule mthr.if.mthr.Runs_lappendE) simp
      from \<tau>Runs' obtain \<sigma>''
        where red_a: "mthr.if.redT \<sigma>' (t_a, ta_a) \<sigma>''"
        and \<tau>Runs'': "mthr.if.mthr.Runs \<sigma>'' ?E'"
        unfolding E'_a_m by cases
      from New_ta_a a_n have "NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta_a\<rbrace>\<^bsub>o\<^esub>"
        unfolding in_set_conv_nth by blast
      with red_a obtain x_a x'_a m'_a 
        where red'_a: "mthr.init_fin t_a (x_a, shr \<sigma>') ta_a (x'_a, m'_a)"
        and \<sigma>''': "redT_upd \<sigma>' t_a ta_a x'_a m'_a \<sigma>''"
        and ts_t_a: "thr \<sigma>' t_a = \<lfloor>(x_a, no_wait_locks)\<rfloor>"
        by cases auto
      from red'_a \<open>NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta_a\<rbrace>\<^bsub>o\<^esub>\<close>
      obtain ta'_a X_a X'_a
        where x_a: "x_a = (Running, X_a)"
        and x'_a: "x'_a = (Running, X'_a)"
        and ta_a: "ta_a = convert_TA_initial (convert_obs_initial ta'_a)"
        and red''_a: "t_a \<turnstile> (X_a, shr \<sigma>') -ta'_a\<rightarrow> (X'_a, m'_a)"
        by cases fastforce+
      from ta_a New_ta_a a_n have New_ta'_a: "\<lbrace>ta'_a\<rbrace>\<^bsub>o\<^esub> ! a_n = NewHeapElem ad CTn"
        and a_n': "a_n < length \<lbrace>ta'_a\<rbrace>\<^bsub>o\<^esub>" by auto
      hence "NewHeapElem ad CTn \<in> set \<lbrace>ta'_a\<rbrace>\<^bsub>o\<^esub>" unfolding in_set_conv_nth by blast
      with red''_a have allocated_m'_a_ad: "ad \<in> allocated m'_a"
        by(auto dest: red_New_allocatedD)
      
      have "a_m \<le> a'_m"
      proof(rule ccontr)
        assume "\<not> ?thesis"
        hence "a'_m < a_m" by simp
        hence "(\<Sum>i<a_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) = (\<Sum>i<a'_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) + (\<Sum>i = a'_m..<a_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
          by(simp add: sum_upto_add_nat)
        hence "a' - n < a - n" using \<open>a'_m < a_m\<close> a'_n E'_a'_m unfolding a_conv a'_conv
          by(subst (asm) sum.atLeast_Suc_lessThan) simp_all
        with a_a' show False by simp
      qed
  
      have a'_less: "a' - n < (a - n) - a_n + length \<lbrace>ta_a\<rbrace>\<^bsub>o\<^esub>"
      proof(rule ccontr)
        assume "\<not> ?thesis"
        hence a'_greater: "(a - n) - a_n + length \<lbrace>ta_a\<rbrace>\<^bsub>o\<^esub> \<le> a' - n" by simp
        
        have "a_m < a'_m"
        proof(rule ccontr)
          assume "\<not> ?thesis"
          with \<open>a_m \<le> a'_m\<close> have "a_m = a'_m" by simp
          with a'_greater a_n a'_n E'_a'_m E'_a_m show False
            unfolding a_conv a'_conv by simp
        qed
        hence a'_m_a_m: "enat (a'_m - Suc a_m) < llength ?E'" using a'_m
          by(cases "llength E'") simp_all
        from \<open>a_m < a'_m\<close> a'_m E'_a'_m
        have E'_a'_m': "lnth ?E' (a'_m - Suc a_m) = (t_a', ta_a')" by simp
    
        have E'_unfold': "?E' = lappend (ltake (enat (a'_m - Suc a_m)) ?E') (LCons (lnth ?E' (a'_m - Suc a_m)) (ldropn (Suc (a'_m - Suc a_m)) ?E'))"
          unfolding ldropn_Suc_conv_ldropn[OF a'_m_a_m] lappend_ltake_enat_ldropn ..
        hence "mthr.if.mthr.Runs \<sigma>'' (lappend (ltake (enat (a'_m - Suc a_m)) ?E') (LCons (lnth ?E' (a'_m - Suc a_m)) (ldropn (Suc (a'_m - Suc a_m)) ?E')))"
          using \<tau>Runs'' by simp
        then obtain \<sigma>'''
          where \<sigma>''_\<sigma>''': "mthr.if.mthr.Trsys \<sigma>'' (list_of (ltake (enat (a'_m - Suc a_m)) ?E')) \<sigma>'''"
          and \<tau>Runs''': "mthr.if.mthr.Runs \<sigma>''' (LCons (lnth ?E' (a'_m - Suc a_m)) (ldropn (Suc (a'_m - Suc a_m)) ?E'))"
          by(rule mthr.if.mthr.Runs_lappendE) simp
        from \<tau>Runs''' obtain \<sigma>''''
          where red_a': "mthr.if.redT \<sigma>''' (t_a', ta_a') \<sigma>''''"
          and \<tau>Runs'''': "mthr.if.mthr.Runs \<sigma>'''' (ldropn (Suc (a'_m - Suc a_m)) ?E')"
          unfolding E'_a'_m' by cases
        from New_ta_a' a'_n have "NormalAction (NewHeapElem ad CTn') \<in> set \<lbrace>ta_a'\<rbrace>\<^bsub>o\<^esub>"
          unfolding in_set_conv_nth by blast
        with red_a' obtain x_a' x'_a' m'_a' 
          where red'_a': "mthr.init_fin t_a' (x_a', shr \<sigma>''') ta_a' (x'_a', m'_a')"
          and \<sigma>'''''': "redT_upd \<sigma>''' t_a' ta_a' x'_a' m'_a' \<sigma>''''"
          and ts_t_a': "thr \<sigma>''' t_a' = \<lfloor>(x_a', no_wait_locks)\<rfloor>"
          by cases auto
        from red'_a' \<open>NormalAction (NewHeapElem ad CTn') \<in> set \<lbrace>ta_a'\<rbrace>\<^bsub>o\<^esub>\<close>
        obtain ta'_a' X_a' X'_a' 
          where x_a': "x_a' = (Running, X_a')"
          and x'_a': "x'_a' = (Running, X'_a')"
          and ta_a': "ta_a' = convert_TA_initial (convert_obs_initial ta'_a')"
          and red''_a': "t_a' \<turnstile> (X_a', shr \<sigma>''') -ta'_a'\<rightarrow> (X'_a', m'_a')"
          by cases fastforce+
        from ta_a' New_ta_a' a'_n have New_ta'_a': "\<lbrace>ta'_a'\<rbrace>\<^bsub>o\<^esub> ! a'_n = NewHeapElem ad CTn'"
          and a'_n': "a'_n < length \<lbrace>ta'_a'\<rbrace>\<^bsub>o\<^esub>" by auto
        hence "NewHeapElem ad CTn' \<in> set \<lbrace>ta'_a'\<rbrace>\<^bsub>o\<^esub>" unfolding in_set_conv_nth by blast
        with red''_a' have allocated_ad': "ad \<notin> allocated (shr \<sigma>''')"
          by(auto dest: red_New_allocatedD)
    
        have "allocated m'_a = allocated (shr \<sigma>'')" using \<sigma>''' by auto
        also have "\<dots> \<subseteq> allocated (shr \<sigma>''')"
          using \<sigma>''_\<sigma>''' unfolding mthr.if.RedT_def[symmetric] by(rule init_fin_RedT_allocated_mono)
        finally have "ad \<in> allocated (shr \<sigma>''')" using allocated_m'_a_ad by blast
        with allocated_ad' show False by contradiction
      qed
      
      from \<open>a_m \<le> a'_m\<close> have [simp]: "a_m = a'_m"
      proof(rule le_antisym)
        show "a'_m \<le> a_m"
        proof(rule ccontr)
          assume "\<not> ?thesis"
          hence "a_m < a'_m" by simp
          hence "(\<Sum>i<a'_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) = (\<Sum>i<a_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) + (\<Sum>i = a_m..<a'_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
            by(simp add: sum_upto_add_nat)
          with a'_less \<open>a_m < a'_m\<close> E'_a_m a_n a'_n show False
            unfolding a'_conv a_conv by(subst (asm) sum.atLeast_Suc_lessThan) simp_all
        qed
      qed
      with E'_a_m E'_a'_m have [simp]: "t_a' = t_a" "ta_a' = ta_a" by simp_all
      from New_ta_a' a'_n ta_a have a'_n': "a'_n < length \<lbrace>ta'_a\<rbrace>\<^bsub>o\<^esub>"
        and New_ta'_a': "\<lbrace>ta'_a\<rbrace>\<^bsub>o\<^esub> ! a'_n = NewHeapElem ad CTn'" by auto
      with red''_a New_ta'_a a_n' have "a'_n = a_n"
        by(auto dest: red_New_same_addr_same)
      with \<open>a_m = a'_m\<close> have "a - n = a' - n" unfolding a_conv a'_conv by simp
      thus ?thesis using \<open>n \<le> a\<close> \<open>n \<le> a'\<close> by simp
    qed
  qed
qed

end


text \<open>Knowledge of addresses of a multithreaded state\<close>

fun ka_Val :: "'addr val \<Rightarrow> 'addr set"
where
  "ka_Val (Addr a) = {a}"
| "ka_Val _ = {}"

fun new_obs_addr :: "('addr, 'thread_id) obs_event \<Rightarrow> 'addr set"
where
  "new_obs_addr (ReadMem ad al (Addr ad')) = {ad'}"
| "new_obs_addr (NewHeapElem ad hT) = {ad}"
| "new_obs_addr _ = {}"

lemma new_obs_addr_cases[consumes 1, case_names ReadMem NewHeapElem, cases set]:
  assumes "ad \<in> new_obs_addr ob"
  obtains ad' al where "ob = ReadMem ad' al (Addr ad)"
  | CTn where "ob = NewHeapElem ad CTn"
using assms
by(cases ob rule: new_obs_addr.cases) auto

definition new_obs_addrs :: "('addr, 'thread_id) obs_event list \<Rightarrow> 'addr set"
where
  "new_obs_addrs obs = \<Union>(new_obs_addr ` set obs)"

fun new_obs_addr_if :: "('addr, 'thread_id) obs_event action \<Rightarrow> 'addr set"
where
  "new_obs_addr_if (NormalAction a) = new_obs_addr a"
| "new_obs_addr_if _ = {}"

definition new_obs_addrs_if :: "('addr, 'thread_id) obs_event action list \<Rightarrow> 'addr set"
where 
  "new_obs_addrs_if obs = \<Union>(new_obs_addr_if ` set obs)"

lemma ka_Val_subset_new_obs_Addr_ReadMem:
  "ka_Val v \<subseteq> new_obs_addr (ReadMem ad al v)"
by(cases v) simp_all

lemma typeof_ka: "typeof v \<noteq> None \<Longrightarrow> ka_Val v = {}"
by(cases v) simp_all

lemma ka_Val_undefined_value [simp]:
  "ka_Val undefined_value = {}"
apply(cases "undefined_value :: 'a val")
apply(bestsimp simp add: undefined_value_not_Addr dest: subst)+
done

locale known_addrs_base =
  fixes known_addrs :: "'t \<Rightarrow> 'x \<Rightarrow> 'addr set"
begin

definition known_addrs_thr :: "('l, 't, 'x) thread_info \<Rightarrow> 'addr set"
where "known_addrs_thr ts = (\<Union>t \<in> dom ts. known_addrs t (fst (the (ts t))))"

definition known_addrs_state :: "('l,'t,'x,'m,'w) state \<Rightarrow> 'addr set"
where "known_addrs_state s = known_addrs_thr (thr s)"

lemma known_addrs_state_simps [simp]:
  "known_addrs_state (ls, (ts, m), ws) = known_addrs_thr ts"
by(simp add: known_addrs_state_def)

lemma known_addrs_thr_cases[consumes 1, case_names known_addrs, cases set: known_addrs_thr]:
  assumes "ad \<in> known_addrs_thr ts"
  and "\<And>t x ln. \<lbrakk> ts t = \<lfloor>(x, ln)\<rfloor>; ad \<in> known_addrs t x \<rbrakk> \<Longrightarrow> thesis"
  shows thesis
using assms
by(auto simp add: known_addrs_thr_def ran_def)

lemma known_addrs_stateI:
  "\<And>ln. \<lbrakk> ad \<in> known_addrs t x; thr s t = \<lfloor>(x, ln)\<rfloor> \<rbrakk> \<Longrightarrow> ad \<in> known_addrs_state s"
by(fastforce simp add: known_addrs_state_def known_addrs_thr_def intro: rev_bexI)

fun known_addrs_if :: "'t \<Rightarrow> status \<times> 'x \<Rightarrow> 'addr set"
where "known_addrs_if t (s, x) = known_addrs t x"

end

locale if_known_addrs_base = 
  known_addrs_base known_addrs 
  +
  multithreaded_base final r convert_RA
  for known_addrs :: "'t \<Rightarrow> 'x \<Rightarrow> 'addr set"
  and final :: "'x \<Rightarrow> bool"
  and r :: "('addr, 't, 'x, 'heap, 'addr, 'obs) semantics" ("_ \<turnstile> _ -_\<rightarrow> _" [50,0,0,50] 80)
  and convert_RA :: "'addr released_locks \<Rightarrow> 'obs list"

sublocale if_known_addrs_base < "if": known_addrs_base known_addrs_if .

locale known_addrs =
  allocated_multithreaded (* Check why all the heap operations are necessary in this locale! *)
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write
    allocated
    final r
    P 
  +
  if_known_addrs_base known_addrs final r convert_RA

  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and spurious_wakeups :: bool
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool" 
  and allocated :: "'heap \<Rightarrow> 'addr set"
  and known_addrs :: "'thread_id \<Rightarrow> 'x \<Rightarrow> 'addr set"
  and final :: "'x \<Rightarrow> bool"
  and r :: "('addr, 'thread_id, 'x, 'heap, 'addr, ('addr, 'thread_id) obs_event) semantics" ("_ \<turnstile> _ -_\<rightarrow> _" [50,0,0,50] 80) 
  and P :: "'md prog"
  +
  assumes red_known_addrs_new:
  "t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>
  \<Longrightarrow> known_addrs t x' \<subseteq> known_addrs t x \<union> new_obs_addrs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  and red_known_addrs_new_thread:
  "\<lbrakk> t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>; NewThread t' x'' m'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> known_addrs t' x'' \<subseteq> known_addrs t x"
  and red_read_knows_addr:
  "\<lbrakk> t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>; ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> ad \<in> known_addrs t x"
  and red_write_knows_addr:
  "\<lbrakk> t \<turnstile> \<langle>x, m\<rangle> -ta\<rightarrow> \<langle>x', m'\<rangle>; \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n = WriteMem ad al (Addr ad'); n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> ad' \<in> known_addrs t x \<or> ad' \<in> new_obs_addrs (take n \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
  \<comment> \<open>second possibility necessary for @{term heap_clone}\<close>
begin

notation mthr.redT_syntax1 ("_ -_\<triangleright>_\<rightarrow> _" [50,0,0,50] 80)

lemma if_red_known_addrs_new: 
  assumes "t \<turnstile> (x, m) -ta\<rightarrow>i (x', m')"
  shows "known_addrs_if t x' \<subseteq> known_addrs_if t x \<union> new_obs_addrs_if \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
using assms
by cases(auto dest!: red_known_addrs_new simp add: new_obs_addrs_if_def new_obs_addrs_def)

lemma if_red_known_addrs_new_thread:
  assumes "t \<turnstile> (x, m) -ta\<rightarrow>i (x', m')" "NewThread t' x'' m'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
  shows "known_addrs_if t' x'' \<subseteq> known_addrs_if t x"
using assms
by cases(fastforce dest: red_known_addrs_new_thread)+

lemma if_red_read_knows_addr:
  assumes "t \<turnstile> (x, m) -ta\<rightarrow>i (x', m')" "NormalAction (ReadMem ad al v) \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  shows "ad \<in> known_addrs_if t x"
using assms
by cases(fastforce dest: red_read_knows_addr)+

lemma if_red_write_knows_addr:
  assumes "t \<turnstile> (x, m) -ta\<rightarrow>i (x', m')"
  and "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! n = NormalAction (WriteMem ad al (Addr ad'))" "n < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  shows "ad' \<in> known_addrs_if t x \<or> ad' \<in> new_obs_addrs_if (take n \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
using assms
by cases(auto dest: red_write_knows_addr simp add: new_obs_addrs_if_def new_obs_addrs_def take_map)

lemma if_redT_known_addrs_new:
  assumes redT: "mthr.if.redT s (t, ta) s'"
  shows "if.known_addrs_state s' \<subseteq> if.known_addrs_state s \<union> new_obs_addrs_if \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
using redT
proof(cases)
  case redT_acquire thus ?thesis
    by(cases s)(fastforce simp add: if.known_addrs_thr_def split: if_split_asm intro: rev_bexI)
next
  case (redT_normal x x' m)
  note red = \<open>t \<turnstile> (x, shr s) -ta\<rightarrow>i (x', m)\<close>
  show ?thesis
  proof
    fix ad
    assume "ad \<in> if.known_addrs_state s'"
    hence "ad \<in> if.known_addrs_thr (thr s')" by(simp add: if.known_addrs_state_def)
    then obtain t' x'' ln'' where ts't': "thr s' t' = \<lfloor>(x'', ln'')\<rfloor>" 
      and ad: "ad \<in> known_addrs_if t' x''"
      by(rule if.known_addrs_thr_cases)
    show "ad \<in> if.known_addrs_state s \<union> new_obs_addrs_if \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
    proof(cases "thr s t'")
      case None
      with redT_normal \<open>thr s' t' = \<lfloor>(x'', ln'')\<rfloor>\<close>
      obtain m'' where "NewThread t' x'' m'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"
        by(fastforce dest: redT_updTs_new_thread split: if_split_asm)
      with red have "known_addrs_if t' x'' \<subseteq> known_addrs_if t x" by(rule if_red_known_addrs_new_thread)
      also have "\<dots> \<subseteq> known_addrs_if t x \<union> new_obs_addrs_if \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" by simp
      finally have "ad \<in> known_addrs_if t x \<union> new_obs_addrs_if \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" using ad by blast
      thus ?thesis using \<open>thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>\<close> by(blast intro: if.known_addrs_stateI)
    next
      case (Some xln)
      show ?thesis
      proof(cases "t = t'")
        case True
        with redT_normal ts't' if_red_known_addrs_new[OF red] ad
        have "ad \<in> known_addrs_if t x \<union> new_obs_addrs_if \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" by auto
        thus ?thesis using \<open>thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>\<close> by(blast intro: if.known_addrs_stateI)
      next
        case False
        with ts't' redT_normal ad Some show ?thesis
          by(fastforce dest: redT_updTs_Some[where ts="thr s" and t=t'] intro: if.known_addrs_stateI)
      qed
    qed
  qed
qed

lemma if_redT_read_knows_addr:
  assumes redT: "mthr.if.redT s (t, ta) s'"
  and read: "NormalAction (ReadMem ad al v) \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  shows "ad \<in> if.known_addrs_state s"
using redT
proof(cases)
  case redT_acquire thus ?thesis using read by auto
next
  case (redT_normal x x' m')
  with if_red_read_knows_addr[OF \<open>t \<turnstile> (x, shr s) -ta\<rightarrow>i (x', m')\<close> read]
  show ?thesis
    by(auto simp add: if.known_addrs_state_def if.known_addrs_thr_def intro: bexI[where x=t])
qed

lemma init_fin_redT_known_addrs_subset:
  assumes "mthr.if.redT s (t, ta) s'"
  shows "if.known_addrs_state s' \<subseteq> if.known_addrs_state s \<union> known_addrs_if t (fst (the (thr s' t)))"
using assms
apply(cases)
 apply(rule subsetI)
 apply(clarsimp simp add: if.known_addrs_thr_def split: if_split_asm)
 apply(rename_tac status x status' x' m' a ws' t'' status'' x'' ln'')
 apply(case_tac "thr s t''")
  apply(drule (2) redT_updTs_new_thread)
  apply clarsimp
  apply(drule (1) if_red_known_addrs_new_thread)
  apply simp
  apply(drule (1) subsetD)
  apply(rule_tac x="(status, x)" in if.known_addrs_stateI)
   apply(simp)
  apply simp
 apply(frule_tac t="t''" in redT_updTs_Some, assumption)
 apply clarsimp
 apply(rule_tac x="(status'', x'')" in if.known_addrs_stateI)
  apply simp
 apply simp
apply(auto simp add: if.known_addrs_state_def if.known_addrs_thr_def split: if_split_asm)
done

lemma w_values_no_write_unchanged:
  assumes no_write: "\<And>w. \<lbrakk> w \<in> set obs; is_write_action w; adal \<in> action_loc_aux P w \<rbrakk> \<Longrightarrow> False"
  shows "w_values P vs obs adal = vs adal"
using assms
proof(induct obs arbitrary: vs)
  case Nil show ?case by simp
next
  case (Cons ob obs)
  from Cons.prems[of ob]
  have "w_value P vs ob adal = vs adal"
    by(cases adal)(cases ob rule: w_value_cases, auto simp add: addr_locs_def split: htype.split_asm, blast+)
  moreover
  have "w_values P (w_value P vs ob) obs adal = w_value P vs ob adal"
  proof(rule Cons.hyps)
    fix w
    assume "w \<in> set obs" "is_write_action w" "adal \<in> action_loc_aux P w"
    with Cons.prems[of w] \<open>w_value P vs ob adal = vs adal\<close>
    show "False" by simp
  qed
  ultimately show ?case by simp
qed

lemma redT_non_speculative_known_addrs_allocated:
  assumes red: "mthr.if.redT s (t, ta) s'"
  and tasc: "non_speculative P vs (llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
  and ka: "if.known_addrs_state s \<subseteq> allocated (shr s)"
  and vs: "w_addrs vs \<subseteq> allocated (shr s)"
  shows "if.known_addrs_state s' \<subseteq> allocated (shr s')" (is "?thesis1")
  and "w_addrs (w_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) \<subseteq> allocated (shr s')" (is "?thesis2")
proof -
  have "?thesis1 \<and> ?thesis2" using red
  proof(cases)
    case (redT_acquire x ln n)
    hence "if.known_addrs_state s' = if.known_addrs_state s"
      by(auto 4 4 simp add: if.known_addrs_state_def if.known_addrs_thr_def split: if_split_asm dest: bspec)
    also note ka 
    also from redT_acquire have "shr s = shr s'" by simp
    finally have "if.known_addrs_state s' \<subseteq> allocated (shr s')" .
    moreover have "w_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = vs" using redT_acquire
      by(fastforce intro!: w_values_no_write_unchanged del: equalityI dest: convert_RA_not_write)
    ultimately show ?thesis using vs by(simp add: \<open>shr s = shr s'\<close>)
  next
    case (redT_normal x x' m')
    note red = \<open>t \<turnstile> (x, shr s) -ta\<rightarrow>i (x', m')\<close>
      and tst = \<open>thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>\<close>
    have allocated_subset: "allocated (shr s) \<subseteq> allocated (shr s')"
      using \<open>mthr.if.redT s (t, ta) s'\<close> by(rule init_fin_redT_allocated_mono)
    with vs have vs': "w_addrs vs \<subseteq> allocated (shr s')" by blast
    { fix obs obs'
      assume "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = obs @ obs'"
      moreover with tasc have "non_speculative P vs (llist_of obs)"
        by(simp add: lappend_llist_of_llist_of[symmetric] non_speculative_lappend del: lappend_llist_of_llist_of)
      ultimately have "w_addrs (w_values P vs obs) \<union> new_obs_addrs_if obs \<subseteq> allocated (shr s')" 
        (is "?concl obs")
      proof(induct obs arbitrary: obs' rule: rev_induct)
        case Nil thus ?case using vs' by(simp add: new_obs_addrs_if_def)
      next
        case (snoc ob obs)
        note ta = \<open>\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = (obs @ [ob]) @ obs'\<close>
        note tasc = \<open>non_speculative P vs (llist_of (obs @ [ob]))\<close>
        from snoc have IH: "?concl obs"
          by(simp add: lappend_llist_of_llist_of[symmetric] non_speculative_lappend del: lappend_llist_of_llist_of)
        hence "?concl (obs @ [ob])"
        proof(cases "ob" rule: mrw_value_cases)
          case (1 ad' al v)
          note ob = \<open>ob = NormalAction (WriteMem ad' al v)\<close>
          with ta have Write: "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! length obs = NormalAction (WriteMem ad' al v)" by simp
          show ?thesis
          proof
            fix ad''
            assume "ad'' \<in> w_addrs (w_values P vs (obs @ [ob])) \<union> new_obs_addrs_if (obs @ [ob])"
            hence "ad'' \<in> w_addrs (w_values P vs obs) \<union> new_obs_addrs_if obs \<or> v = Addr ad''"
              by(auto simp add: ob w_addrs_def ran_def new_obs_addrs_if_def split: if_split_asm)
            thus "ad'' \<in> allocated (shr s')"
            proof
              assume "ad'' \<in> w_addrs (w_values P vs obs) \<union> new_obs_addrs_if obs"
              also note IH finally show ?thesis .
            next
              assume v: "v = Addr ad''"
              with Write have "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! length obs = NormalAction (WriteMem ad' al (Addr ad''))" by simp
              with red have "ad'' \<in> known_addrs_if t x \<or> ad'' \<in> new_obs_addrs_if (take (length obs) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
                by(rule if_red_write_knows_addr)(simp add: ta)
              thus ?thesis
              proof
                assume "ad'' \<in> known_addrs_if t x"
                hence "ad'' \<in> if.known_addrs_state s" using tst by(rule if.known_addrs_stateI)
                with ka allocated_subset show ?thesis by blast
              next
                assume "ad'' \<in> new_obs_addrs_if (take (length obs) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
                with ta have "ad'' \<in> new_obs_addrs_if obs" by simp
                with IH show ?thesis by blast
              qed
            qed
          qed
        next
          case (2 ad hT)

          hence ob: "ob = NormalAction (NewHeapElem ad hT)" by simp
          hence "w_addrs (w_values P vs (obs @ [ob])) \<subseteq> w_addrs (w_values P vs obs)"
            by(cases hT)(auto simp add: w_addrs_def default_val_not_Addr Addr_not_default_val)
          moreover from ob ta have "NormalAction (NewHeapElem ad hT) \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" by simp
          from init_fin_red_New_allocatedD[OF red this] have "ad \<in> allocated m'" ..
          with redT_normal have "ad \<in> allocated (shr s')" by auto
          ultimately show ?thesis using IH ob by(auto simp add: new_obs_addrs_if_def)
        next
          case (4 ad al v)
          note ob = \<open>ob = NormalAction (ReadMem ad al v)\<close>
          { fix ad'
            assume v: "v = Addr ad'"
            with tasc ob have mrw: "Addr ad' \<in> w_values P vs obs (ad, al)"
              by(auto simp add: lappend_llist_of_llist_of[symmetric] non_speculative_lappend simp del: lappend_llist_of_llist_of)
            hence "ad' \<in> w_addrs (w_values P vs obs)"
              by(auto simp add: w_addrs_def)
            with IH have "ad' \<in> allocated (shr s')" by blast }
          with ob IH show ?thesis by(cases v)(simp_all add: new_obs_addrs_if_def)
        qed(simp_all add: new_obs_addrs_if_def)
        thus ?case by simp
      qed }
    note this[of "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub>" "[]"]
    moreover have "if.known_addrs_state s' \<subseteq> if.known_addrs_state s \<union> new_obs_addrs_if \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
      using \<open>mthr.if.redT s (t, ta) s'\<close> by(rule if_redT_known_addrs_new)
    ultimately show ?thesis using ka allocated_subset by blast
  qed
  thus ?thesis1 ?thesis2 by simp_all
qed


lemma RedT_non_speculative_known_addrs_allocated:
  assumes red: "mthr.if.RedT s ttas s'"
  and tasc: "non_speculative P vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
  and ka: "if.known_addrs_state s \<subseteq> allocated (shr s)"
  and vs: "w_addrs vs \<subseteq> allocated (shr s)"
  shows "if.known_addrs_state s' \<subseteq> allocated (shr s')" (is "?thesis1 s'")
  and "w_addrs (w_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) \<subseteq> allocated (shr s')" (is "?thesis2 s' ttas")
proof -
  from red tasc have "?thesis1 s' \<and> ?thesis2 s' ttas"
  proof(induct rule: mthr.if.RedT_induct')
    case refl thus ?case using ka vs by simp
  next
    case (step ttas s' t ta s'')
    hence "non_speculative P (w_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
      and "?thesis1 s'" "?thesis2 s' ttas"
      by(simp_all add: lappend_llist_of_llist_of[symmetric] non_speculative_lappend del: lappend_llist_of_llist_of)
    from redT_non_speculative_known_addrs_allocated[OF \<open>mthr.if.redT s' (t, ta) s''\<close> this]
    show ?case by simp
  qed
  thus "?thesis1 s'" "?thesis2 s' ttas" by simp_all
qed

lemma read_ex_NewHeapElem [consumes 5, case_names start Red]:
  assumes RedT: "mthr.if.RedT (init_fin_lift_state status (start_state f P C M vs)) ttas s"
  and red: "mthr.if.redT s (t, ta) s'"
  and read: "NormalAction (ReadMem ad al v) \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  and sc: "non_speculative P (\<lambda>_. {}) (llist_of (map snd (lift_start_obs start_tid start_heap_obs) @ concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
  and known: "known_addrs start_tid (f (fst (method P C M)) M (fst (snd (method P C M))) (fst (snd (snd (method P C M)))) (the (snd (snd (snd (method P C M))))) vs) \<subseteq> allocated start_heap"
  obtains (start) CTn where "NewHeapElem ad CTn \<in> set start_heap_obs"
  | (Red) ttas' s'' t' ta' s''' ttas'' CTn
  where "mthr.if.RedT (init_fin_lift_state status (start_state f P C M vs)) ttas' s''"
  and "mthr.if.redT s'' (t', ta') s'''"
  and "mthr.if.RedT s''' ttas'' s"
  and "ttas = ttas' @ (t', ta') # ttas''"
  and "NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>"
proof -
  let ?start_state = "init_fin_lift_state status (start_state f P C M vs)"
  let ?obs_prefix = "lift_start_obs start_tid start_heap_obs"
  let ?vs_start = "w_values P (\<lambda>_. {}) (map snd ?obs_prefix)"

  from sc have "non_speculative P (w_values P (\<lambda>_. {}) (map snd (lift_start_obs start_tid start_heap_obs))) (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
    by(simp add: non_speculative_lappend lappend_llist_of_llist_of[symmetric] del: lappend_llist_of_llist_of)
  with RedT have "if.known_addrs_state s \<subseteq> allocated (shr s)"
  proof(rule RedT_non_speculative_known_addrs_allocated)
    show "if.known_addrs_state ?start_state \<subseteq> allocated (shr ?start_state)"
      using known
      by(auto simp add: if.known_addrs_state_def if.known_addrs_thr_def start_state_def init_fin_lift_state_def split_beta split: if_split_asm)
    
    have "w_addrs ?vs_start \<subseteq> w_addrs (\<lambda>_. {})" by(rule w_addrs_lift_start_heap_obs)
    thus "w_addrs ?vs_start \<subseteq> allocated (shr ?start_state)" by simp
  qed
  also from red read obtain x_ra x'_ra m'_ra 
    where red'_ra: "t \<turnstile> (x_ra, shr s) -ta\<rightarrow>i (x'_ra, m'_ra)"
    and s': "redT_upd s t ta x'_ra m'_ra s'"
    and ts_t: "thr s t = \<lfloor>(x_ra, no_wait_locks)\<rfloor>"
    by cases auto
  from red'_ra read
  have "ad \<in> known_addrs_if t x_ra" by(rule if_red_read_knows_addr)
  hence "ad \<in> if.known_addrs_state s" using ts_t by(rule if.known_addrs_stateI)
  finally have "ad \<in> allocated (shr s)" .

  show ?thesis
  proof(cases "ad \<in> allocated start_heap")
    case True
    then obtain CTn where "NewHeapElem ad CTn \<in> set start_heap_obs"
      unfolding start_addrs_allocated by(blast dest: start_addrs_NewHeapElem_start_heap_obsD)
    thus ?thesis by(rule start)
  next
    case False
    hence "ad \<notin> allocated (shr ?start_state)" by(simp add: start_state_def split_beta shr_init_fin_lift_state)
    with RedT \<open>ad \<in> allocated (shr s)\<close> obtain t' ta' CTn
      where tta: "(t', ta') \<in> set ttas"
      and new: "NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>"
      by(blast dest: init_fin_RedT_allocated_NewHeapElemD)
    from tta obtain ttas' ttas'' where ttas: "ttas = ttas' @ (t', ta') # ttas''" by(auto dest: split_list)
    with RedT obtain s'' s''' 
      where "mthr.if.RedT ?start_state ttas' s''"
      and "mthr.if.redT s'' (t', ta') s'''"
      and "mthr.if.RedT s''' ttas'' s"
      unfolding mthr.if.RedT_def by(auto elim!: rtrancl3p_appendE dest!: converse_rtrancl3p_step)
    thus thesis using ttas new by(rule Red)
  qed
qed

end

locale known_addrs_typing =
  known_addrs
    addr2thread_id thread_id2addr
    spurious_wakeups
    empty_heap allocate typeof_addr heap_read heap_write
    allocated known_addrs
    final r P
  for addr2thread_id :: "('addr :: addr) \<Rightarrow> 'thread_id"
  and thread_id2addr :: "'thread_id \<Rightarrow> 'addr"
  and spurious_wakeups :: bool
  and empty_heap :: "'heap"
  and allocate :: "'heap \<Rightarrow> htype \<Rightarrow> ('heap \<times> 'addr) set"
  and typeof_addr :: "'heap \<Rightarrow> 'addr \<rightharpoonup> htype"
  and heap_read :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> bool"
  and heap_write :: "'heap \<Rightarrow> 'addr \<Rightarrow> addr_loc \<Rightarrow> 'addr val \<Rightarrow> 'heap \<Rightarrow> bool" 
  and allocated :: "'heap \<Rightarrow> 'addr set"
  and known_addrs :: "'thread_id \<Rightarrow> 'x \<Rightarrow> 'addr set"
  and final :: "'x \<Rightarrow> bool"
  and r :: "('addr, 'thread_id, 'x, 'heap, 'addr, ('addr, 'thread_id) obs_event) semantics" ("_ \<turnstile> _ -_\<rightarrow> _" [50,0,0,50] 80) 
  and wfx :: "'thread_id \<Rightarrow> 'x \<Rightarrow> 'heap \<Rightarrow> bool"
  and P :: "'md prog"
  +
  assumes wfs_non_speculative_invar:
  "\<lbrakk> t \<turnstile> (x, m) -ta\<rightarrow> (x', m'); wfx t x m;
     vs_conf P m vs; non_speculative P vs (llist_of (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) \<rbrakk>
  \<Longrightarrow> wfx t x' m'"
  and wfs_non_speculative_spawn:
  "\<lbrakk> t \<turnstile> (x, m) -ta\<rightarrow> (x', m'); wfx t x m;
     vs_conf P m vs; non_speculative P vs (llist_of (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>));
     NewThread t'' x'' m'' \<in> set \<lbrace>ta\<rbrace>\<^bsub>t\<^esub> \<rbrakk>
  \<Longrightarrow> wfx t'' x'' m''"
  and wfs_non_speculative_other:
  "\<lbrakk> t \<turnstile> (x, m) -ta\<rightarrow> (x', m'); wfx t x m;
     vs_conf P m vs; non_speculative P vs (llist_of (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>));
     wfx t'' x'' m \<rbrakk>
  \<Longrightarrow> wfx t'' x'' m'"
  and wfs_non_speculative_vs_conf:
  "\<lbrakk> t \<turnstile> (x, m) -ta\<rightarrow> (x', m'); wfx t x m;
     vs_conf P m vs; non_speculative P vs (llist_of (take n (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))) \<rbrakk>
  \<Longrightarrow> vs_conf P m' (w_values P vs (take n (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)))"
  and red_read_typeable:
  "\<lbrakk> t \<turnstile> (x, m) -ta\<rightarrow> (x', m'); wfx t x m; ReadMem ad al v \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk> 
  \<Longrightarrow> \<exists>T. P,m \<turnstile> ad@al : T"
  and red_NewHeapElemD:
  "\<lbrakk> t \<turnstile> (x, m) -ta\<rightarrow> (x', m'); wfx t x m; NewHeapElem ad hT \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<rbrakk>
  \<Longrightarrow> typeof_addr m' ad = \<lfloor>hT\<rfloor>"
  and red_hext_incr: 
  "\<lbrakk> t \<turnstile> (x, m) -ta\<rightarrow> (x', m'); wfx t x m; 
     vs_conf P m vs; non_speculative P vs (llist_of (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) \<rbrakk>
  \<Longrightarrow> m \<unlhd> m'"
begin

lemma redT_wfs_non_speculative_invar:
  assumes redT: "mthr.redT s (t, ta) s'"
  and wfx: "ts_ok wfx (thr s) (shr s)"
  and vs: "vs_conf P (shr s) vs"
  and ns: "non_speculative P vs (llist_of (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))"
  shows "ts_ok wfx (thr s') (shr s')"
using redT
proof(cases)
  case (redT_normal x x' m')
  with vs wfx ns show ?thesis
    apply(clarsimp intro!: ts_okI split: if_split_asm)
     apply(erule wfs_non_speculative_invar, auto dest: ts_okD)
    apply(rename_tac t' x' ln ws')
    apply(case_tac "thr s t'")
    apply(frule (2) redT_updTs_new_thread, clarify)
    apply(frule (1) mthr.new_thread_memory)
    apply(auto intro: wfs_non_speculative_other wfs_non_speculative_spawn dest: ts_okD simp add: redT_updTs_Some)
    done
next
  case (redT_acquire x ln n)
  thus ?thesis using wfx by(auto intro!: ts_okI dest: ts_okD split: if_split_asm)
qed

lemma redT_wfs_non_speculative_vs_conf:
  assumes redT: "mthr.redT s (t, ta) s'"
  and wfx: "ts_ok wfx (thr s) (shr s)"
  and conf: "vs_conf P (shr s) vs"
  and ns: "non_speculative P vs (llist_of (take n (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)))"
  shows "vs_conf P (shr s') (w_values P vs (take n (map NormalAction \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)))"
using redT
proof(cases)
  case (redT_normal x x' m')
  thus ?thesis using ns conf wfx by(auto dest: wfs_non_speculative_vs_conf ts_okD)
next
  case (redT_acquire x l ln)
  have "w_values P vs (take n (map NormalAction (convert_RA ln :: ('addr, 'thread_id) obs_event list))) = vs"
    by(fastforce dest: in_set_takeD simp add: convert_RA_not_write intro!: w_values_no_write_unchanged del: equalityI)
  thus ?thesis using conf redT_acquire by(auto)
qed

lemma if_redT_non_speculative_invar:
  assumes red: "mthr.if.redT s (t, ta) s'"
  and ts_ok: "ts_ok (init_fin_lift wfx) (thr s) (shr s)"
  and sc: "non_speculative P vs (llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)" 
  and vs: "vs_conf P (shr s) vs"
  shows "ts_ok (init_fin_lift wfx) (thr s') (shr s')"
proof -
  let ?s = "\<lambda>s. (locks s, (\<lambda>t. map_option (\<lambda>((status, x), ln). (x, ln)) (thr s t), shr s), wset s, interrupts s)"
  
  from ts_ok have ts_ok': "ts_ok wfx (thr (?s s)) (shr (?s s))" by(auto intro!: ts_okI dest: ts_okD)
  from vs have vs': "vs_conf P (shr (?s s)) vs" by simp

  from red show ?thesis
  proof(cases)
    case (redT_normal x x' m)
    note tst = \<open>thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>\<close>
    from \<open>t \<turnstile> (x, shr s) -ta\<rightarrow>i (x', m)\<close>
    show ?thesis 
    proof(cases)
      case (NormalAction X TA X')
      from \<open>ta = convert_TA_initial (convert_obs_initial TA)\<close> \<open>mthr.if.actions_ok s t ta\<close>
      have "mthr.actions_ok (?s s) t TA"
        by(auto elim: rev_iffD1[OF _ thread_oks_ts_change] cond_action_oks_final_change)

      with tst NormalAction \<open>redT_upd s t ta x' m s'\<close> have "mthr.redT (?s s) (t, TA) (?s s')"
        using map_redT_updTs[of snd "thr s" "\<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"]
        by(auto intro!: mthr.redT.intros simp add: split_def map_prod_def o_def fun_eq_iff)
      moreover note ts_ok' vs'
      moreover from \<open>ta = convert_TA_initial (convert_obs_initial TA)\<close> have "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = map NormalAction \<lbrace>TA\<rbrace>\<^bsub>o\<^esub>" by(auto)
      with sc have "non_speculative P vs (llist_of (map NormalAction \<lbrace>TA\<rbrace>\<^bsub>o\<^esub>))" by simp
      ultimately have "ts_ok wfx (thr (?s s')) (shr (?s s'))"
        by(auto dest: redT_wfs_non_speculative_invar)
      thus ?thesis using \<open>\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = map NormalAction \<lbrace>TA\<rbrace>\<^bsub>o\<^esub>\<close> by(auto intro!: ts_okI dest: ts_okD)
    next
      case InitialThreadAction
      with redT_normal ts_ok' vs show ?thesis
        by(auto 4 3 intro!: ts_okI dest: ts_okD split: if_split_asm)
    next
      case ThreadFinishAction
      with redT_normal ts_ok' vs show ?thesis
        by(auto 4 3 intro!: ts_okI dest: ts_okD split: if_split_asm)
    qed
  next
    case (redT_acquire x ln l)
    thus ?thesis using vs ts_ok by(auto 4 3 intro!: ts_okI dest: ts_okD split: if_split_asm)
  qed
qed

lemma if_redT_non_speculative_vs_conf:
  assumes red: "mthr.if.redT s (t, ta) s'"
  and ts_ok: "ts_ok (init_fin_lift wfx) (thr s) (shr s)"
  and sc: "non_speculative P vs (llist_of (take n \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))"
  and vs: "vs_conf P (shr s) vs"
  shows "vs_conf P (shr s') (w_values P vs (take n \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))"
proof -
  let ?s = "\<lambda>s. (locks s, (\<lambda>t. map_option (\<lambda>((status, x), ln). (x, ln)) (thr s t), shr s), wset s, interrupts s)"
  
  from ts_ok have ts_ok': "ts_ok wfx (thr (?s s)) (shr (?s s))" by(auto intro!: ts_okI dest: ts_okD)
  from vs have vs': "vs_conf P (shr (?s s)) vs" by simp

  from red show ?thesis
  proof(cases)
    case (redT_normal x x' m)
    note tst = \<open>thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>\<close>
    from \<open>t \<turnstile> (x, shr s) -ta\<rightarrow>i (x', m)\<close>
    show ?thesis 
    proof(cases)
      case (NormalAction X TA X')
      from \<open>ta = convert_TA_initial (convert_obs_initial TA)\<close> \<open>mthr.if.actions_ok s t ta\<close>
      have "mthr.actions_ok (?s s) t TA"
        by(auto elim: rev_iffD1[OF _ thread_oks_ts_change] cond_action_oks_final_change)

      with tst NormalAction \<open>redT_upd s t ta x' m s'\<close> have "mthr.redT (?s s) (t, TA) (?s s')"
        using map_redT_updTs[of snd "thr s" "\<lbrace>ta\<rbrace>\<^bsub>t\<^esub>"]
        by(auto intro!: mthr.redT.intros simp add: split_def map_prod_def o_def fun_eq_iff)
      moreover note ts_ok' vs'
      moreover from \<open>ta = convert_TA_initial (convert_obs_initial TA)\<close> have "\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = map NormalAction \<lbrace>TA\<rbrace>\<^bsub>o\<^esub>" by(auto)
      with sc have "non_speculative P vs (llist_of (take n (map NormalAction \<lbrace>TA\<rbrace>\<^bsub>o\<^esub>)))" by simp
      ultimately have "vs_conf P (shr (?s s')) (w_values P vs (take n (map NormalAction \<lbrace>TA\<rbrace>\<^bsub>o\<^esub>)))"
        by(auto dest: redT_wfs_non_speculative_vs_conf)
      thus ?thesis using \<open>\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> = map NormalAction \<lbrace>TA\<rbrace>\<^bsub>o\<^esub>\<close> by(auto)
    next
      case InitialThreadAction
      with redT_normal vs show ?thesis by(auto simp add: take_Cons')
    next
      case ThreadFinishAction
      with redT_normal vs show ?thesis by(auto simp add: take_Cons')
    qed
  next
    case (redT_acquire x l ln)
    have "w_values P vs (take n (map NormalAction (convert_RA ln :: ('addr, 'thread_id) obs_event list))) = vs"
      by(fastforce simp add: convert_RA_not_write take_Cons' dest: in_set_takeD intro!: w_values_no_write_unchanged del: equalityI)
    thus ?thesis using vs redT_acquire by auto 
  qed
qed

lemma if_RedT_non_speculative_invar:
  assumes red: "mthr.if.RedT s ttas s'"
  and tsok: "ts_ok (init_fin_lift wfx) (thr s) (shr s)"
  and sc: "non_speculative P vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
  and vs: "vs_conf P (shr s) vs"
  shows "ts_ok (init_fin_lift wfx) (thr s') (shr s')" (is ?thesis1)
  and "vs_conf P (shr s') (w_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))" (is ?thesis2)
using red tsok sc vs unfolding mthr.if.RedT_def
proof(induct arbitrary: vs rule: rtrancl3p_converse_induct')
  case refl
  case 1 thus ?case by -
  case 2 thus ?case by simp
next
  case (step s tta s' ttas)
  obtain t ta where tta: "tta = (t, ta)" by(cases tta)

  case 1
  hence sc1: "non_speculative P vs (llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
    and sc2: "non_speculative P (w_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
    unfolding lconcat_llist_of[symmetric] lmap_llist_of[symmetric] llist.map_comp o_def llist_of.simps llist.map(2) lconcat_LCons tta
    by(simp_all add: non_speculative_lappend list_of_lconcat o_def)
  from if_redT_non_speculative_invar[OF step(2)[unfolded tta] _ sc1] if_redT_non_speculative_vs_conf[OF step(2)[unfolded tta], where vs = vs and n="length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"] 1 step.hyps(3)[of "w_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"] sc2 sc1
  show ?case by simp

  case 2
  hence sc1: "non_speculative P vs (llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
    and sc2: "non_speculative P (w_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
    unfolding lconcat_llist_of[symmetric] lmap_llist_of[symmetric] llist.map_comp o_def llist_of.simps llist.map(2) lconcat_LCons tta
    by(simp_all add: non_speculative_lappend list_of_lconcat o_def)
  from if_redT_non_speculative_invar[OF step(2)[unfolded tta] _ sc1] if_redT_non_speculative_vs_conf[OF step(2)[unfolded tta], where vs = vs and n="length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"] 2 step.hyps(4)[of "w_values P vs \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"] sc2 sc1
  show ?case by(simp add: tta o_def)
qed

lemma init_fin_hext_incr:
  assumes "t \<turnstile> (x, m) -ta\<rightarrow>i (x', m')"
  and "init_fin_lift wfx t x m"
  and "non_speculative P vs (llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
  and "vs_conf P m vs"
  shows "m \<unlhd> m'"
using assms
by(cases)(auto intro: red_hext_incr)

lemma init_fin_redT_hext_incr:
  assumes "mthr.if.redT s (t, ta) s'"
  and "ts_ok (init_fin_lift wfx) (thr s) (shr s)"
  and "non_speculative P vs (llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
  and "vs_conf P (shr s) vs"
  shows "shr s \<unlhd> shr s'"
using assms
by(cases)(auto dest: init_fin_hext_incr ts_okD)

lemma init_fin_RedT_hext_incr:
  assumes "mthr.if.RedT s ttas s'"
  and "ts_ok (init_fin_lift wfx) (thr s) (shr s)"
  and sc: "non_speculative P vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
  and vs: "vs_conf P (shr s) vs"
  shows "shr s \<unlhd> shr s'"
using assms
proof(induction rule: mthr.if.RedT_induct')
  case refl thus ?case by simp
next
  case (step ttas s' t ta s'')
  note ts_ok = \<open>ts_ok (init_fin_lift wfx) (thr s) (shr s)\<close>
  from \<open>non_speculative P vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (ttas @ [(t, ta)]))))\<close>
  have ns: "non_speculative P vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
    and ns': "non_speculative P (w_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
    by(simp_all add: lappend_llist_of_llist_of[symmetric] non_speculative_lappend del: lappend_llist_of_llist_of)
  from ts_ok ns have "shr s \<unlhd> shr s'" 
    using \<open>vs_conf P (shr s) vs\<close> by(rule step.IH)
  also have "ts_ok (init_fin_lift wfx) (thr s') (shr s')"
    using \<open>mthr.if.RedT s ttas s'\<close> ts_ok ns \<open>vs_conf P (shr s) vs\<close>
    by(rule if_RedT_non_speculative_invar)
  with \<open>mthr.if.redT s' (t, ta) s''\<close> 
  have "\<dots> \<unlhd> shr s''" using ns'
  proof(rule init_fin_redT_hext_incr)
    from \<open>mthr.if.RedT s ttas s'\<close> ts_ok ns \<open>vs_conf P (shr s) vs\<close>
    show "vs_conf P (shr s') (w_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
      by(rule if_RedT_non_speculative_invar)
  qed
  finally show ?case .
qed

lemma init_fin_red_read_typeable:
  assumes "t \<turnstile> (x, m) -ta\<rightarrow>i (x', m')"
  and "init_fin_lift wfx t x m" "NormalAction (ReadMem ad al v) \<in> set \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
  shows "\<exists>T. P,m \<turnstile> ad@al : T"
using assms
by cases(auto dest: red_read_typeable)

lemma Ex_new_action_for:
  assumes wf: "wf_syscls P"
  and wfx_start: "ts_ok wfx (thr (start_state f P C M vs)) start_heap"
  and ka: "known_addrs start_tid (f (fst (method P C M)) M (fst (snd (method P C M))) (fst (snd (snd (method P C M)))) (the (snd (snd (snd (method P C M))))) vs) \<subseteq> allocated start_heap"
  and E: "E \<in> \<E>_start f P C M vs status"
  and read: "ra \<in> read_actions E"
  and aloc: "adal \<in> action_loc P E ra"
  and sc: "non_speculative P (\<lambda>_. {}) (ltake (enat ra) (lmap snd E))"
  shows "\<exists>wa. wa \<in> new_actions_for P E adal \<and> wa < ra"
proof -
  let ?obs_prefix = "lift_start_obs start_tid start_heap_obs"
  let ?start_state = "init_fin_lift_state status (start_state f P C M vs)"

  from start_state_vs_conf[OF wf]
  have vs_conf_start: "vs_conf P start_heap (w_values P (\<lambda>_. {}) (map NormalAction start_heap_obs))" 
    by(simp add: lift_start_obs_def o_def)

  obtain ad al where adal: "adal = (ad, al)" by(cases adal)
  with read aloc obtain v where ra: "action_obs E ra = NormalAction (ReadMem ad al v)"
    and ra_len: "enat ra < llength E"
    by(cases "lnth E ra")(auto elim!: read_actions.cases actionsE)

  from E obtain E'' where E: "E = lappend (llist_of ?obs_prefix) E''"
    and E'': "E'' \<in> mthr.if.\<E> ?start_state" by(auto)
  from E'' obtain E' where E': "E'' = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E')"
    and \<tau>Runs: "mthr.if.mthr.Runs ?start_state E'" by(rule mthr.if.\<E>.cases)

  have ra_len': "length ?obs_prefix \<le> ra"
  proof(rule ccontr)
    assume "\<not> ?thesis"
    hence "ra < length ?obs_prefix" by simp
    moreover with ra ra_len E obtain ra' ad al v 
      where "start_heap_obs ! ra' = ReadMem ad al v" "ra' < length start_heap_obs"
      by(cases ra)(auto simp add: lnth_LCons lnth_lappend1 action_obs_def lift_start_obs_def)
    ultimately have "ReadMem ad al v \<in> set start_heap_obs" unfolding in_set_conv_nth by blast
    thus False by(simp add: start_heap_obs_not_Read)
  qed
  let ?n = "length ?obs_prefix"
  from ra ra_len ra_len' E have "enat (ra - ?n) < llength E''"
    and ra_obs: "action_obs E'' (ra - ?n) = NormalAction (ReadMem ad al v)"
    by(cases "llength E''", auto simp add: action_obs_def lnth_lappend2)
  
  from \<tau>Runs \<open>enat (ra - ?n) < llength E''\<close> obtain ra_m ra_n t_ra ta_ra 
    where E_ra: "lnth E'' (ra - ?n) = (t_ra, \<lbrace>ta_ra\<rbrace>\<^bsub>o\<^esub> ! ra_n)"
    and ra_n: "ra_n < length \<lbrace>ta_ra\<rbrace>\<^bsub>o\<^esub>" and ra_m: "enat ra_m < llength E'"
    and ra_conv: "ra - ?n = (\<Sum>i<ra_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) + ra_n"
    and E'_ra_m: "lnth E' ra_m = (t_ra, ta_ra)"
    unfolding E' by(rule mthr.if.actions_\<E>E_aux)
    
  let ?E' = "ldropn (Suc ra_m) E'"
    
  have E'_unfold: "E' = lappend (ltake (enat ra_m) E') (LCons (lnth E' ra_m) ?E')"
    unfolding ldropn_Suc_conv_ldropn[OF ra_m] by simp
  hence "mthr.if.mthr.Runs ?start_state (lappend (ltake (enat ra_m) E') (LCons (lnth E' ra_m) ?E'))"
    using \<tau>Runs by simp
  then obtain \<sigma>' where \<sigma>_\<sigma>': "mthr.if.mthr.Trsys ?start_state (list_of (ltake (enat ra_m) E')) \<sigma>'"
    and \<tau>Runs': "mthr.if.mthr.Runs \<sigma>' (LCons (lnth E' ra_m) ?E')"
    by(rule mthr.if.mthr.Runs_lappendE) simp
  from \<tau>Runs' obtain \<sigma>'' where red_ra: "mthr.if.redT \<sigma>' (t_ra, ta_ra) \<sigma>''"
    and \<tau>Runs'': "mthr.if.mthr.Runs \<sigma>'' ?E'"
    unfolding E'_ra_m by cases

  from E_ra ra_n ra_obs have "NormalAction (ReadMem ad al v) \<in> set \<lbrace>ta_ra\<rbrace>\<^bsub>o\<^esub>"
    by(auto simp add: action_obs_def in_set_conv_nth)
  with red_ra obtain x_ra x'_ra m'_ra 
    where red'_ra: "mthr.init_fin t_ra (x_ra, shr \<sigma>') ta_ra (x'_ra, m'_ra)"
    and \<sigma>'': "redT_upd \<sigma>' t_ra ta_ra x'_ra m'_ra \<sigma>''"
    and ts_t_a: "thr \<sigma>' t_ra = \<lfloor>(x_ra, no_wait_locks)\<rfloor>"
    by cases auto
  from red'_ra \<open>NormalAction (ReadMem ad al v) \<in> set \<lbrace>ta_ra\<rbrace>\<^bsub>o\<^esub>\<close>
  obtain ta'_ra X_ra X'_ra
    where x_ra: "x_ra = (Running, X_ra)"
    and x'_ra: "x'_ra = (Running, X'_ra)"
    and ta_ra: "ta_ra = convert_TA_initial (convert_obs_initial ta'_ra)"
    and red''_ra: "t_ra \<turnstile> (X_ra, shr \<sigma>') -ta'_ra\<rightarrow> (X'_ra, m'_ra)"
    by cases fastforce+

  from \<open>NormalAction (ReadMem ad al v) \<in> set \<lbrace>ta_ra\<rbrace>\<^bsub>o\<^esub>\<close> ta_ra 
  have "ReadMem ad al v \<in> set \<lbrace>ta'_ra\<rbrace>\<^bsub>o\<^esub>" by auto

  from wfx_start have wfx_start: "ts_ok (init_fin_lift wfx) (thr ?start_state) (shr ?start_state)"
    by(simp add: start_state_def split_beta)

  from sc ra_len'
  have "non_speculative P (w_values P (\<lambda>_. {}) (map snd ?obs_prefix))
    (lmap snd (ltake (enat (ra - ?n)) (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E'))))"
    unfolding E E' by(simp add: ltake_lappend2 lmap_lappend_distrib non_speculative_lappend)
  also note ra_conv also note plus_enat_simps(1)[symmetric]
  also have "enat (\<Sum>i<ra_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) = (\<Sum>i<ra_m. enat (length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>))"
    by(subst sum_hom[symmetric])(simp_all add: zero_enat_def)
  also have "\<dots> = (\<Sum>i<ra_m. llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E') i))"
    using ra_m by-(rule sum.cong[OF refl], simp add: le_less_trans[where y="enat ra_m"] split_beta)
  also note ltake_plus_conv_lappend also note lconcat_ltake[symmetric]
  also note lmap_lappend_distrib
  also note non_speculative_lappend
  finally have "non_speculative P (w_values P (\<lambda>_. {}) (map snd ?obs_prefix)) (lmap snd (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (llist_of (list_of (ltake (enat ra_m) E'))))))"
    by(simp add: split_def)
  hence sc': "non_speculative P (w_values P (\<lambda>_. {}) (map snd ?obs_prefix)) (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of (ltake (enat ra_m) E')))))"
    unfolding lmap_lconcat llist.map_comp o_def lconcat_llist_of[symmetric] lmap_llist_of[symmetric]
    by(simp add: split_beta o_def)

  from vs_conf_start have vs_conf_start: "vs_conf P (shr ?start_state) (w_values P (\<lambda>_. {}) (map snd ?obs_prefix))"
    by(simp add:init_fin_lift_state_conv_simps start_state_def split_beta lift_start_obs_def o_def)
  with \<sigma>_\<sigma>' wfx_start sc' have "ts_ok (init_fin_lift wfx) (thr \<sigma>') (shr \<sigma>')"
    unfolding mthr.if.RedT_def[symmetric] by(rule if_RedT_non_speculative_invar)
  with ts_t_a have "wfx t_ra X_ra (shr \<sigma>')" unfolding x_ra by(auto dest: ts_okD)

  with red''_ra \<open>ReadMem ad al v \<in> set \<lbrace>ta'_ra\<rbrace>\<^bsub>o\<^esub>\<close>
  obtain T' where type_adal: "P,shr \<sigma>' \<turnstile> ad@al : T'" by(auto dest: red_read_typeable)

  from sc ra_len' have "non_speculative P (\<lambda>_. {}) (llist_of (map snd ?obs_prefix))"
    unfolding E by(simp add: ltake_lappend2 lmap_lappend_distrib non_speculative_lappend)
  with sc' have sc'': "non_speculative P (\<lambda>_. {}) (llist_of (map snd (lift_start_obs start_tid start_heap_obs) @ concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of (ltake (enat ra_m) E')))))"
    by(simp add: lappend_llist_of_llist_of[symmetric] non_speculative_lappend del: lappend_llist_of_llist_of)

  from \<sigma>_\<sigma>' red_ra \<open>NormalAction (ReadMem ad al v) \<in> set \<lbrace>ta_ra\<rbrace>\<^bsub>o\<^esub>\<close> sc'' ka
  show "\<exists>wa. wa \<in> new_actions_for P E adal \<and> wa < ra"
    unfolding mthr.if.RedT_def[symmetric]
  proof(cases rule: read_ex_NewHeapElem)
    case (start CTn)
    then obtain n where n: "start_heap_obs ! n = NewHeapElem ad CTn" 
      and len: "n < length start_heap_obs"
      unfolding in_set_conv_nth by blast
    from len have "Suc n \<in> actions E" unfolding E by(simp add: actions_def enat_less_enat_plusI)
    moreover
    from \<sigma>_\<sigma>' have hext: "start_heap \<unlhd> shr \<sigma>'" unfolding mthr.if.RedT_def[symmetric]
      using wfx_start sc' vs_conf_start
      by(auto dest!: init_fin_RedT_hext_incr simp add: start_state_def split_beta init_fin_lift_state_conv_simps)
    
    from start have "typeof_addr start_heap ad = \<lfloor>CTn\<rfloor>"
      by(auto dest: NewHeapElem_start_heap_obsD[OF wf])
    with hext have "typeof_addr (shr \<sigma>') ad = \<lfloor>CTn\<rfloor>" by(rule typeof_addr_hext_mono)
    with type_adal have "adal \<in> action_loc P E (Suc n)" using n len unfolding E adal
      by cases(auto simp add: action_obs_def lnth_lappend1 lift_start_obs_def)
    moreover have "is_new_action (action_obs E (Suc n))" using n len unfolding E
      by(simp add: action_obs_def lnth_lappend1 lift_start_obs_def)
    ultimately have "Suc n \<in> new_actions_for P E adal" by(rule new_actionsI)
    moreover have "Suc n < ra" using ra_len' len by(simp)
    ultimately show ?thesis by blast
  next
    case (Red ttas' s'' t' ta' s''' ttas'' CTn)
    
    from \<open>NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>\<close>
    obtain obs obs' where obs: "\<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> = obs @ NormalAction (NewHeapElem ad CTn) # obs'"
      by(auto dest: split_list)
    
    let ?wa = "?n + length (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas')) + length obs"
    have "enat (length (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas')) + length obs) < enat (length (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (ttas' @ [(t', ta')]))))"
      using obs by simp
    also have "\<dots> = llength (lconcat (lmap llist_of (lmap (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (llist_of (ttas' @ [(t', ta')])))))"
      by(simp del: map_map map_append add: lconcat_llist_of)
    also have "\<dots> \<le> llength (lconcat (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (llist_of (ttas' @ (t', ta') # ttas''))))"
      by(auto simp add: o_def split_def intro: lprefix_llist_ofI intro!: lprefix_lconcatI lprefix_llength_le)
    also note len_less = calculation
    have "\<dots> \<le> (\<Sum>i<ra_m. llength (lnth (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) E') i))"
      unfolding \<open>list_of (ltake (enat ra_m) E') = ttas' @ (t', ta') # ttas''\<close>[symmetric]
      by(simp add: ltake_lmap[symmetric] lconcat_ltake del: ltake_lmap)
    also have "\<dots> = enat (\<Sum>i<ra_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>)" using ra_m
      by(subst sum_hom[symmetric, where f="enat"])(auto intro: sum.cong simp add: zero_enat_def less_trans[where y="enat ra_m"] split_beta)
    also have "\<dots> \<le> enat (ra - ?n)" unfolding ra_conv by simp
    finally have enat_length: "enat (length (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas')) + length obs) < enat (ra - length (lift_start_obs start_tid start_heap_obs))" .
    then have wa_ra: "?wa < ra" by simp
    with ra_len have "?wa \<in> actions E" by(cases "llength E")(simp_all add: actions_def)
    moreover
    from \<open>mthr.if.redT s'' (t', ta') s'''\<close> \<open>NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>\<close>
    obtain x_wa x_wa' where ts''t': "thr s'' t' = \<lfloor>(x_wa, no_wait_locks)\<rfloor>"
      and red_wa: "mthr.init_fin t' (x_wa, shr s'') ta' (x_wa', shr s''')"
      by(cases) fastforce+

    from sc'
    have ns: "non_speculative P (w_values P (\<lambda>_. {}) (map snd ?obs_prefix)) (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas')))"
      and ns': "non_speculative P (w_values P (w_values P (\<lambda>_. {}) (map snd ?obs_prefix)) (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas'))) (llist_of \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)"
      and ns'': "non_speculative P (w_values P (w_values P (w_values P (\<lambda>_. {}) (map snd ?obs_prefix)) (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas'))) \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas'')))"
      unfolding \<open>list_of (ltake (enat ra_m) E') = ttas' @ (t', ta') # ttas''\<close>
      by(simp_all add: lappend_llist_of_llist_of[symmetric] lmap_lappend_distrib non_speculative_lappend del: lappend_llist_of_llist_of)
    from \<open>mthr.if.RedT ?start_state ttas' s''\<close> wfx_start ns
    have ts_ok'': "ts_ok (init_fin_lift wfx) (thr s'') (shr s'')"
      using vs_conf_start by(rule if_RedT_non_speculative_invar)
    with ts''t' have wfxt': "wfx t' (snd x_wa) (shr s'')" by(cases x_wa)(auto dest: ts_okD)

    {
      have "action_obs E ?wa = 
        snd (lnth (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E')) (length (concat (map (\<lambda>(t, y). \<lbrace>y\<rbrace>\<^bsub>o\<^esub>) ttas')) + length obs))"
        unfolding E E' by(simp add: action_obs_def lnth_lappend2)
      also from enat_length \<open>enat (ra - ?n) < llength E''\<close>
      have "\<dots> = lnth (lconcat (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) E')) (length (concat (map (\<lambda>(t, y). \<lbrace>y\<rbrace>\<^bsub>o\<^esub>) ttas')) + length obs)"
        unfolding E'
        by(subst lnth_lmap[symmetric, where f=snd])(erule (1) less_trans, simp add: lmap_lconcat llist.map_comp split_def o_def)
      also from len_less
      have "enat (length (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas')) + length obs) < llength (lconcat (ltake (enat ra_m) (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) E')))"
        unfolding \<open>list_of (ltake (enat ra_m) E') = ttas' @ (t', ta') # ttas''\<close>[symmetric]
        by(simp add: ltake_lmap[symmetric] del: ltake_lmap)
      note lnth_lconcat_ltake[OF this, symmetric]
      also note ltake_lmap
      also have "ltake (enat ra_m) E' = llist_of (list_of (ltake (enat ra_m) E'))" by(simp)
      also note \<open>list_of (ltake (enat ra_m) E') = ttas' @ (t', ta') # ttas''\<close>
      also note lmap_llist_of also have "(\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) = llist_of \<circ> (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
        by(simp add: o_def split_def)
      also note map_map[symmetric] also note lconcat_llist_of
      also note lnth_llist_of 
      also have "concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (ttas' @ (t', ta') # ttas'')) ! (length (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas')) + length obs) = NormalAction (NewHeapElem ad CTn)"
        by(simp add: nth_append obs)
      finally have "action_obs E ?wa = NormalAction (NewHeapElem ad CTn)" .
    }
    note wa_obs = this
    
    from \<open>mthr.if.RedT ?start_state ttas' s''\<close> wfx_start ns vs_conf_start
    have vs'': "vs_conf P (shr s'') (w_values P (w_values P (\<lambda>_. {}) (map snd ?obs_prefix)) (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas')))"
      by(rule if_RedT_non_speculative_invar)
    from if_redT_non_speculative_vs_conf[OF \<open>mthr.if.redT s'' (t', ta') s'''\<close> ts_ok'' _ vs'', of "length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>"] ns'
    have vs''': "vs_conf P (shr s''') (w_values P (w_values P (w_values P (\<lambda>_. {}) (map snd ?obs_prefix)) (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas'))) \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)"
      by simp
    
    from \<open>mthr.if.redT s'' (t', ta') s'''\<close> ts_ok'' ns' vs''
    have "ts_ok (init_fin_lift wfx) (thr s''') (shr s''')"
      by(rule if_redT_non_speculative_invar)
    with \<open>mthr.if.RedT s''' ttas'' \<sigma>'\<close>
    have hext: "shr s''' \<unlhd> shr \<sigma>'" using ns'' vs'''
      by(rule init_fin_RedT_hext_incr)

    from red_wa have "typeof_addr (shr s''') ad = \<lfloor>CTn\<rfloor>"
      using wfxt' \<open>NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>\<close> by cases(auto dest: red_NewHeapElemD)
    with hext have "typeof_addr (shr \<sigma>') ad = \<lfloor>CTn\<rfloor>" by(rule typeof_addr_hext_mono)
    with type_adal have "adal \<in> action_loc P E ?wa" using wa_obs unfolding E adal
      by cases (auto simp add: action_obs_def lnth_lappend1 lift_start_obs_def)
    moreover have "is_new_action (action_obs E ?wa)" using wa_obs by simp
    ultimately have "?wa \<in> new_actions_for P E adal" by(rule new_actionsI)
    thus ?thesis using wa_ra by blast
  qed
qed

lemma executions_sc_hb:
  assumes "wf_syscls P"
  and "ts_ok wfx (thr (start_state f P C M vs)) start_heap"
  and "known_addrs start_tid (f (fst (method P C M)) M (fst (snd (method P C M))) (fst (snd (snd (method P C M)))) (the (snd (snd (snd (method P C M))))) vs) \<subseteq> allocated start_heap"
  shows
  "executions_sc_hb (\<E>_start f P C M vs status) P"
  (is "executions_sc_hb ?E P")
proof
  fix E a adal a'
  assume "E \<in> ?E" "a \<in> new_actions_for P E adal" "a' \<in> new_actions_for P E adal"
  thus "a = a'" by(rule \<E>_new_actions_for_unique)
next
  fix E ra adal
  assume "E \<in> ?E" "ra \<in> read_actions E" "adal \<in> action_loc P E ra" 
    and "non_speculative P (\<lambda>_. {}) (ltake (enat ra) (lmap snd E))"
  with assms show "\<exists>wa. wa \<in> new_actions_for P E adal \<and> wa < ra"
    by(rule Ex_new_action_for)
qed

lemma executions_aux:
  assumes wf: "wf_syscls P"
  and wfx_start: "ts_ok wfx (thr (start_state f P C M vs)) start_heap" (is "ts_ok wfx (thr ?start_state) _")
  and ka: "known_addrs start_tid (f (fst (method P C M)) M (fst (snd (method P C M))) (fst (snd (snd (method P C M)))) (the (snd (snd (snd (method P C M))))) vs) \<subseteq> allocated start_heap"
  shows "executions_aux (\<E>_start f P C M vs status) P"
  (is "executions_aux ?\<E> P")
proof
  fix E a adal a'
  assume "E \<in> ?\<E>" "a \<in> new_actions_for P E adal" "a' \<in> new_actions_for P E adal"
  thus "a = a'" by(rule \<E>_new_actions_for_unique)
next
  fix E ws r adal
  assume E: "E \<in> ?\<E>"
    and wf_exec: "P \<turnstile> (E, ws) \<surd>" 
    and read: "r \<in> read_actions E" "adal \<in> action_loc P E r"
    and sc: "\<And>a. \<lbrakk>a < r; a \<in> read_actions E\<rbrakk> \<Longrightarrow> P,E \<turnstile> a \<leadsto>mrw ws a"

  interpret jmm: executions_sc_hb ?\<E> P
    using wf wfx_start ka by(rule executions_sc_hb)

  from E wf_exec sc
  have "ta_seq_consist P Map.empty (ltake (enat r) (lmap snd E))"
    unfolding ltake_lmap by(rule jmm.ta_seq_consist_mrwI) simp
  hence "non_speculative P (\<lambda>_. {}) (ltake (enat r) (lmap snd E))"
    by(rule ta_seq_consist_into_non_speculative) simp
  with wf wfx_start ka E read
  have "\<exists>i. i \<in> new_actions_for P E adal \<and> i < r"
    by(rule Ex_new_action_for)
  thus "\<exists>i<r. i \<in> new_actions_for P E adal" by blast
qed

lemma drf:
  assumes cut_and_update:
    "if.cut_and_update
       (init_fin_lift_state status (start_state f P C M vs))
       (mrw_values P Map.empty (map snd (lift_start_obs start_tid start_heap_obs)))"
    (is "if.cut_and_update ?start_state (mrw_values _ _ (map _ ?start_heap_obs))")
  and wf: "wf_syscls P"
  and wfx_start: "ts_ok wfx (thr (start_state f P C M vs)) start_heap"
  and ka: "known_addrs start_tid (f (fst (method P C M)) M (fst (snd (method P C M))) (fst (snd (snd (method P C M)))) (the (snd (snd (snd (method P C M))))) vs) \<subseteq> allocated start_heap"
  shows "drf (\<E>_start f P C M vs status) P" (is "drf ?\<E> _")
proof -
  interpret jmm: executions_sc_hb "?\<E>" P
    using wf wfx_start ka by(rule executions_sc_hb)

  let ?n = "length ?start_heap_obs"
  let ?\<E>' = "lappend (llist_of ?start_heap_obs) ` mthr.if.\<E> ?start_state"

  show ?thesis 
  proof
    fix E ws r
    assume E: "E \<in> ?\<E>'"
      and wf: "P \<turnstile> (E, ws) \<surd>"
      and mrw: "\<And>a. \<lbrakk> a < r; a \<in> read_actions E \<rbrakk> \<Longrightarrow> P,E \<turnstile> a \<leadsto>mrw ws a"
    show "\<exists>E'\<in>?\<E>'. \<exists>ws'. P \<turnstile> (E', ws') \<surd> \<and> ltake (enat r) E = ltake (enat r) E' \<and>
                           sequentially_consistent P (E', ws') \<and>
                           action_tid E r = action_tid E' r \<and> action_obs E r \<approx> action_obs E' r \<and>
                           (r \<in> actions E \<longrightarrow> r \<in> actions E')"
    proof(cases "\<exists>r'. r' \<in> read_actions E \<and> r \<le> r'")
      case False
      have "sequentially_consistent P (E, ws)"
      proof(rule sequentially_consistentI)
        fix a
        assume "a \<in> read_actions E"
        with False have "a < r" by auto
        thus "P,E \<turnstile> a \<leadsto>mrw ws a" using \<open>a \<in> read_actions E\<close> by(rule mrw)
      qed
      moreover have "action_obs E r \<approx> action_obs E r" by(rule sim_action_refl)
      ultimately show ?thesis using wf E by blast
    next
      case True
      let ?P = "\<lambda>r'. r' \<in> read_actions E \<and> r \<le> r'"
      let ?r = "Least ?P"
      from True obtain r' where r': "?P r'" by blast
      hence r: "?P ?r" by(rule LeastI)
      {
        fix a
        assume "a < ?r" "a \<in> read_actions E"
        have "P,E \<turnstile> a \<leadsto>mrw ws a"
        proof(cases "a < r")
          case True
          thus ?thesis using \<open>a \<in> read_actions E\<close> by(rule mrw)
        next
          case False
          with \<open>a \<in> read_actions E\<close> have "?P a" by simp
          hence "?r \<le> a" by(rule Least_le)
          with \<open>a < ?r\<close> have False by simp
          thus ?thesis ..
        qed }
      note mrw' = this

      from E obtain E'' where E: "E = lappend (llist_of ?start_heap_obs) E''"
        and E'': "E'' \<in> mthr.if.\<E> ?start_state" by auto

      from E'' obtain E' where E': "E'' = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E')"
        and \<tau>Runs: "mthr.if.mthr.Runs ?start_state E'"
        by(rule mthr.if.\<E>.cases)

      have r_len: "length ?start_heap_obs \<le> ?r"
      proof(rule ccontr)
        assume "\<not> ?thesis"
        hence "?r < length ?start_heap_obs" by simp
        moreover with r E obtain t ad al v where "?start_heap_obs ! ?r = (t, NormalAction (ReadMem ad al v))"
          by(cases "?start_heap_obs ! ?r")(fastforce elim!: read_actions.cases simp add: actions_def action_obs_def lnth_lappend1)
        ultimately have "(t, NormalAction (ReadMem ad al v)) \<in> set ?start_heap_obs" unfolding in_set_conv_nth by blast
        thus False by(auto simp add: start_heap_obs_not_Read)
      qed
      let ?n = "length ?start_heap_obs"
      from r r_len E have r: "?r - ?n \<in> read_actions E''"
        by(fastforce elim!: read_actions.cases simp add: actions_lappend action_obs_def lnth_lappend2 elim: actionsE intro: read_actions.intros)
      
      from r have "?r - ?n \<in> actions E''" by(auto)
      hence "enat (?r - ?n) < llength E''" by(rule actionsE)
      with \<tau>Runs obtain r_m r_n t_r ta_r 
        where E_r: "lnth E'' (?r - ?n) = (t_r, \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> ! r_n)"
        and r_n: "r_n < length \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>" and r_m: "enat r_m < llength E'"
        and r_conv: "?r - ?n = (\<Sum>i<r_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) + r_n"
        and E'_r_m: "lnth E' r_m = (t_r, ta_r)"
        unfolding E' by(rule mthr.if.actions_\<E>E_aux)

      let ?E' = "ldropn (Suc r_m) E'"
      let ?r_m_E' = "ltake (enat r_m) E'"
      have E'_unfold: "E' = lappend (ltake (enat r_m) E') (LCons (lnth E' r_m) ?E')"
        unfolding ldropn_Suc_conv_ldropn[OF r_m] by simp
      hence "mthr.if.mthr.Runs ?start_state (lappend ?r_m_E' (LCons (lnth E' r_m) ?E'))"
        using \<tau>Runs by simp
      then obtain \<sigma>' where \<sigma>_\<sigma>': "mthr.if.mthr.Trsys ?start_state (list_of ?r_m_E') \<sigma>'"
        and \<tau>Runs': "mthr.if.mthr.Runs \<sigma>' (LCons (lnth E' r_m) ?E')"
        by(rule mthr.if.mthr.Runs_lappendE) simp
      from \<tau>Runs' obtain \<sigma>''' where red_ra: "mthr.if.redT \<sigma>' (t_r, ta_r) \<sigma>'''"
        and \<tau>Runs'': "mthr.if.mthr.Runs \<sigma>''' ?E'"
        unfolding E'_r_m by cases

      let ?vs = "mrw_values P Map.empty (map snd ?start_heap_obs)"
      { fix a
        assume "enat a < enat ?r"
          and "a \<in> read_actions E"
        have "a < r"
        proof(rule ccontr)
          assume "\<not> a < r"
          with \<open>a \<in> read_actions E\<close> have "?P a" by simp
          hence "?r \<le> a" by(rule Least_le)
          with \<open>enat a < enat ?r\<close> show False by simp
        qed
        hence "P,E \<turnstile> a \<leadsto>mrw ws a" using \<open>a \<in> read_actions E\<close> by(rule mrw) }
      with \<open>E \<in> ?\<E>'\<close> wf have "ta_seq_consist P Map.empty (lmap snd (ltake (enat ?r) E))"
        by(rule jmm.ta_seq_consist_mrwI)

      hence start_sc: "ta_seq_consist P Map.empty (llist_of (map snd ?start_heap_obs))"
        and "ta_seq_consist P ?vs (lmap snd (ltake (enat (?r - ?n)) E''))"
        using \<open>?n \<le> ?r\<close> unfolding E ltake_lappend lmap_lappend_distrib
        by(simp_all add: ta_seq_consist_lappend o_def)

      note this(2) also from r_m
      have r_m_sum_len_eq: "(\<Sum>i<r_m. llength (lnth (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E') i)) = enat (\<Sum>i<r_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>)"
        by(subst sum_hom[symmetric, where f=enat])(auto simp add: zero_enat_def split_def less_trans[where y="enat r_m"] intro: sum.cong)
      hence "ltake (enat (?r - ?n)) E'' = 
            lappend (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ?r_m_E')) 
                    (ltake (enat r_n) (ldrop (enat (\<Sum>i<r_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>)) E''))"
        unfolding ltake_lmap[symmetric] lconcat_ltake r_conv plus_enat_simps(1)[symmetric] ltake_plus_conv_lappend
        unfolding E' by simp
      finally have "ta_seq_consist P ?vs (lmap snd (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ?r_m_E')))"
        and sc_ta_r: "ta_seq_consist P (mrw_values P ?vs (map snd (list_of (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ?r_m_E'))))) (lmap snd (ltake (enat r_n) (ldropn (\<Sum>i<r_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) E'')))"
        unfolding lmap_lappend_distrib by(simp_all add: ta_seq_consist_lappend split_def ldrop_enat)
      note this(1) also
      have "lmap snd (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (ltake (enat r_m) E')))
            = llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of ?r_m_E')))"
        unfolding lmap_lconcat llist.map_comp o_def split_def lconcat_llist_of[symmetric] map_map lmap_llist_of[symmetric]
        by simp
      finally have "ta_seq_consist P ?vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of ?r_m_E'))))" .
      from if.sequential_completion[OF cut_and_update ta_seq_consist_convert_RA \<sigma>_\<sigma>'[folded mthr.if.RedT_def] this red_ra]
      obtain ta' ttas' 
        where "mthr.if.mthr.Runs \<sigma>' (LCons (t_r, ta') ttas')"
        and sc: "ta_seq_consist P (mrw_values P Map.empty (map snd ?start_heap_obs)) 
                   (lconcat (lmap (\<lambda>(t, ta). llist_of \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (lappend (llist_of (list_of ?r_m_E')) (LCons (t_r, ta') ttas'))))"
          and eq_ta: "eq_upto_seq_inconsist P \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> (mrw_values P ?vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of ?r_m_E'))))"
          by blast

      let ?E_sc' = "lappend (llist_of (list_of ?r_m_E')) (LCons (t_r, ta') ttas')"
      let ?E_sc'' = "lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ?E_sc')"
      let ?E_sc = "lappend (llist_of ?start_heap_obs) ?E_sc''"

      from \<sigma>_\<sigma>' \<open>mthr.if.mthr.Runs \<sigma>' (LCons (t_r, ta') ttas')\<close>
      have "mthr.if.mthr.Runs ?start_state ?E_sc'" by(rule mthr.if.mthr.Trsys_into_Runs)
      hence "?E_sc'' \<in> mthr.if.\<E> ?start_state" by(rule mthr.if.\<E>.intros)
      hence "?E_sc \<in> ?\<E>" by(rule imageI)
      moreover from \<open>?E_sc'' \<in> mthr.if.\<E> ?start_state\<close>
      have tsa_ok: "thread_start_actions_ok ?E_sc" by(rule thread_start_actions_ok_init_fin) 
        
      from sc have "ta_seq_consist P Map.empty (lmap snd ?E_sc)"
        by(simp add: lmap_lappend_distrib o_def lmap_lconcat llist.map_comp split_def ta_seq_consist_lappend start_sc)
      from ta_seq_consist_imp_sequentially_consistent[OF tsa_ok jmm.\<E>_new_actions_for_fun[OF \<open>?E_sc \<in> ?\<E>\<close>] this]
      obtain ws_sc where "sequentially_consistent P (?E_sc, ws_sc)"
        and "P \<turnstile> (?E_sc, ws_sc) \<surd>" unfolding start_heap_obs_def[symmetric] by iprover
      moreover {
        have enat_sum_r_m_eq: "enat (\<Sum>i<r_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) = llength (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ?r_m_E'))"
          by(auto intro: sum.cong simp add: less_trans[OF _ r_m] lnth_ltake llength_lconcat_lfinite_conv_sum sum_hom[symmetric, where f=enat] zero_enat_def[symmetric] split_beta)
        also have "\<dots> \<le> llength E''" unfolding E'
          by(blast intro: lprefix_llength_le lprefix_lconcatI lmap_lprefix)
        finally have r_m_E: "ltake (enat (?n + (\<Sum>i<r_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>))) E = ltake (enat (?n + (\<Sum>i<r_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>))) ?E_sc"
          by(simp add: ltake_lappend lappend_eq_lappend_conv lmap_lappend_distrib r_m_sum_len_eq ltake_lmap[symmetric] min_def zero_enat_def[symmetric] E E' lconcat_ltake ltake_all del: ltake_lmap)

        have drop_r_m_E: "ldropn (?n + (\<Sum>i<r_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>)) E = lappend (llist_of (map (Pair t_r) \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>)) (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (ldropn (Suc r_m) E')))"
          (is "_ = ?drop_r_m_E") using E'_r_m unfolding E E'
          by(subst (2) E'_unfold)(simp add: ldropn_lappend2 lmap_lappend_distrib enat_sum_r_m_eq[symmetric])

        have drop_r_m_E_sc: "ldropn (?n + (\<Sum>i<r_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>)) ?E_sc =
          lappend (llist_of (map (Pair t_r) \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)) (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ttas'))"
          by(simp add: ldropn_lappend2 lmap_lappend_distrib enat_sum_r_m_eq[symmetric])

        let ?vs_r_m = "mrw_values P ?vs (map snd (list_of (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ?r_m_E'))))"
        note sc_ta_r also
        from drop_r_m_E have "ldropn (\<Sum>i<r_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) E'' = ?drop_r_m_E"
          unfolding E by(simp add: ldropn_lappend2)
        also have "lmap snd (ltake (enat r_n) \<dots>) = llist_of (take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>)" using r_n
          by(simp add: ltake_lappend lmap_lappend_distrib ltake_lmap[symmetric] take_map o_def zero_enat_def[symmetric] del: ltake_lmap)
        finally have sc_ta_r: "ta_seq_consist P ?vs_r_m (llist_of (take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>))" .
        note eq_ta
        also have "\<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> = take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> @ drop r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>" by simp
        finally have "eq_upto_seq_inconsist P (take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> @ drop r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>) \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ?vs_r_m"
          by(simp add: list_of_lconcat split_def o_def map_concat)
        from eq_upto_seq_inconsist_appendD[OF this sc_ta_r]
        have r_n': "r_n \<le> length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>"
          and take_r_n_eq: "take r_n \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> = take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>"
          and eq_r_n: "eq_upto_seq_inconsist P (drop r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>) (drop r_n \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) (mrw_values P ?vs_r_m (take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>))"
          using r_n by(simp_all add: min_def)
        from r_conv \<open>?n \<le> ?r\<close> have r_conv': "?r = (?n + (\<Sum>i<r_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>)) + r_n" by simp
        from r_n' r_n take_r_n_eq r_m_E drop_r_m_E drop_r_m_E_sc
        have take_r'_eq: "ltake (enat ?r) E = ltake (enat ?r) ?E_sc" unfolding r_conv'
          apply(subst (1 2) plus_enat_simps(1)[symmetric])
          apply(subst (1 2) ltake_plus_conv_lappend)
          apply(simp add: lappend_eq_lappend_conv ltake_lappend1 ldrop_enat take_map)
          done
        hence take_r_eq: "ltake (enat r) E = ltake (enat r) ?E_sc"
          by(rule ltake_eq_ltake_antimono)(simp add: \<open>?P ?r\<close>)
        
        from eq_r_n Cons_nth_drop_Suc[OF r_n, symmetric]
        have "drop r_n \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> \<noteq> []" by(auto simp add: eq_upto_seq_inconsist_simps)
        hence r_n': "r_n < length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>" by simp
        hence eq_r_n: "\<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> ! r_n \<approx> \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! r_n"
          using eq_r_n Cons_nth_drop_Suc[OF r_n, symmetric] Cons_nth_drop_Suc[OF r_n', symmetric]
          by(simp add: eq_upto_seq_inconsist_simps split: action.split_asm obs_event.split_asm if_split_asm)
        obtain tid_eq: "action_tid E r = action_tid ?E_sc r" 
          and obs_eq: "action_obs E r \<approx> action_obs ?E_sc r"
        proof(cases "r < ?r")
          case True
          { from True have "action_tid E r = action_tid (ltake (enat ?r) E) r"
              by(simp add: action_tid_def lnth_ltake)
            also note take_r'_eq
            also have "action_tid (ltake (enat ?r) ?E_sc) r = action_tid ?E_sc r"
              using True by(simp add: action_tid_def lnth_ltake)
            finally have "action_tid E r = action_tid ?E_sc r" . }
          moreover
          { from True have "action_obs E r = action_obs (ltake (enat ?r) E) r"
              by(simp add: action_obs_def lnth_ltake)
            also note take_r'_eq
            also have "action_obs (ltake (enat ?r) ?E_sc) r = action_obs ?E_sc r"
              using True by(simp add: action_obs_def lnth_ltake)
            finally have "action_obs E r \<approx> action_obs ?E_sc r" by simp }
          ultimately show thesis by(rule that)
        next
          case False
          with \<open>?P ?r\<close> have r_eq: "r = ?r" by simp
          hence "lnth E r = (t_r, \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> ! r_n)" using E_r r_conv' E by(simp add: lnth_lappend2)
          moreover have "lnth ?E_sc r = (t_r, \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! r_n)" using \<open>?n \<le> ?r\<close> r_n'
            by(subst r_eq)(simp add: r_conv lnth_lappend2 lmap_lappend_distrib enat_sum_r_m_eq[symmetric] lnth_lappend1 del: length_lift_start_obs)
          ultimately have "action_tid E r = action_tid ?E_sc r" "action_obs E r \<approx> action_obs ?E_sc r"
            using eq_r_n by(simp_all add: action_tid_def action_obs_def)
          thus thesis by(rule that)
        qed
        
        have "enat r < enat ?n + llength (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (lappend ?r_m_E' (LCons (t_r, ta') LNil))))"
          using \<open>?P ?r\<close> r_n' unfolding lmap_lappend_distrib
          by(simp add: enat_sum_r_m_eq[symmetric] r_conv')
        also have "llength (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (lappend ?r_m_E' (LCons (t_r, ta') LNil)))) \<le> llength ?E_sc''"
          by(rule lprefix_llength_le[OF lprefix_lconcatI])(simp add: lmap_lprefix)
        finally have "r \<in> actions ?E_sc" by(simp add: actions_def add_left_mono)
        note this tid_eq obs_eq take_r_eq }
      ultimately show ?thesis by blast
    qed
  qed(rule \<E>_new_actions_for_unique)
qed

lemma sc_legal:
  assumes hb_completion:
    "if.hb_completion (init_fin_lift_state status (start_state f P C M vs)) (lift_start_obs start_tid start_heap_obs)"
    (is "if.hb_completion ?start_state ?start_heap_obs")
  and wf: "wf_syscls P"
  and wfx_start: "ts_ok wfx (thr (start_state f P C M vs)) start_heap"
  and ka: "known_addrs start_tid (f (fst (method P C M)) M (fst (snd (method P C M))) (fst (snd (snd (method P C M)))) (the (snd (snd (snd (method P C M))))) vs) \<subseteq> allocated start_heap"
  shows "sc_legal (\<E>_start f P C M vs status) P"
  (is "sc_legal ?\<E> P")
proof -
  interpret jmm: executions_sc_hb ?\<E> P
    using wf wfx_start ka by(rule executions_sc_hb)

  interpret jmm: executions_aux ?\<E> P
    using wf wfx_start ka by(rule executions_aux)

  show ?thesis
  proof
    fix E ws r
    assume E: "E \<in> ?\<E>" and wf_exec: "P \<turnstile> (E, ws) \<surd>"
      and mrw: "\<And>a. \<lbrakk>a < r; a \<in> read_actions E\<rbrakk> \<Longrightarrow> P,E \<turnstile> a \<leadsto>mrw ws a"


    from E obtain E'' where E: "E = lappend (llist_of ?start_heap_obs) E''"
      and E'': "E'' \<in> mthr.if.\<E> ?start_state" by auto
    
    from E'' obtain E' where E': "E'' = lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) E')"
      and \<tau>Runs: "mthr.if.mthr.Runs ?start_state E'"
      by(rule mthr.if.\<E>.cases)
    
    show "\<exists>E'\<in>?\<E>. \<exists>ws'. P \<turnstile> (E', ws') \<surd> \<and> ltake (enat r) E = ltake (enat r) E' \<and>
                         (\<forall>a\<in>read_actions E'. if a < r then ws' a = ws a else P,E' \<turnstile> ws' a \<le>hb a) \<and>
                         action_tid E' r = action_tid E r \<and>
                         (if r \<in> read_actions E then sim_action else (=)) (action_obs E' r) (action_obs E r) \<and>
                         (r \<in> actions E \<longrightarrow> r \<in> actions E')"
      (is "\<exists>E'\<in>?\<E>. \<exists>ws'. _ \<and> ?same E' \<and> ?read E' ws' \<and> ?tid E' \<and> ?obs E' \<and> ?actions E'")
    proof(cases "r < length ?start_heap_obs")
      case True

      from if.hb_completion_Runs[OF hb_completion ta_hb_consistent_convert_RA]
      obtain ttas where Runs: "mthr.if.mthr.Runs ?start_state ttas"
        and hb: "ta_hb_consistent P ?start_heap_obs (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ttas))"
        by blast

      from Runs have \<E>: "lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ttas) \<in> mthr.if.\<E> ?start_state"
        by(rule mthr.if.\<E>.intros)
        
      let ?E = "lappend (llist_of ?start_heap_obs) (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ttas))"
      from \<E> have E': "?E \<in> ?\<E>" by blast

      from \<E> have tsa: "thread_start_actions_ok ?E" by(rule thread_start_actions_ok_init_fin)

      from start_heap_obs_not_Read
      have ws: "is_write_seen P (llist_of (lift_start_obs start_tid start_heap_obs)) ws"
        by(unfold in_set_conv_nth)(rule is_write_seenI, auto simp add: action_obs_def actions_def lift_start_obs_def lnth_LCons elim!: read_actions.cases split: nat.split_asm)

      with hb tsa
      have "\<exists>ws'. P \<turnstile> (?E, ws') \<surd> \<and>
                  (\<forall>n. n \<in> read_actions ?E \<longrightarrow> length ?start_heap_obs \<le> n \<longrightarrow> P,?E \<turnstile> ws' n \<le>hb n) \<and>
                  (\<forall>n<length ?start_heap_obs. ws' n = ws n)"
        by(rule ta_hb_consistent_Read_hb)(rule jmm.\<E>_new_actions_for_fun[OF E'])
      then obtain ws' where wf_exec': "P \<turnstile> (?E, ws') \<surd>" 
        and read_hb: "\<And>n. \<lbrakk> n \<in> read_actions ?E; length ?start_heap_obs \<le> n \<rbrakk> \<Longrightarrow> P,?E \<turnstile> ws' n \<le>hb n"
        and same: "\<And>n. n<length ?start_heap_obs \<Longrightarrow> ws' n = ws n" by blast

      from True have "?same ?E" unfolding E by(simp add: ltake_lappend1)
      moreover {
        fix a
        assume a: "a \<in> read_actions ?E"
        have "if a < r then ws' a = ws a else P,?E \<turnstile> ws' a \<le>hb a"
        proof(cases "a < length ?start_heap_obs")
          case True
          with a have False using start_heap_obs_not_Read
            by cases(auto simp add: action_obs_def actions_def lnth_lappend1 lift_start_obs_def lnth_LCons in_set_conv_nth split: nat.split_asm)
          thus ?thesis ..
        next
          case False
          with read_hb[of a] True a show ?thesis by auto
        qed }
      hence "?read ?E ws'" by blast
      moreover from True E have "?tid ?E" by(simp add: action_tid_def lnth_lappend1)
      moreover from True E have "?obs ?E" by(simp add: action_obs_def lnth_lappend1)
      moreover from True have "?actions ?E" by(simp add: actions_def enat_less_enat_plusI)
      ultimately show ?thesis using E' wf_exec' by blast
    next
      case False
      hence r: "length ?start_heap_obs \<le> r" by simp

      show ?thesis
      proof(cases "enat r < llength E")
        case False
        then obtain "?same E" "?read E ws" "?tid E" "?obs E" "?actions E"
          by(cases "llength E")(fastforce elim!: read_actions.cases simp add: actions_def split: if_split_asm)+
        with wf_exec \<open>E \<in> ?\<E>\<close> show ?thesis by blast
      next
        case True
        note r' = this

        let ?r = "r - length ?start_heap_obs"
        from E r r' have "enat ?r < llength E''" by(cases "llength E''")(auto)
        with \<tau>Runs obtain r_m r_n t_r ta_r 
          where E_r: "lnth E'' ?r = (t_r, \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> ! r_n)"
          and r_n: "r_n < length \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>" and r_m: "enat r_m < llength E'"
          and r_conv: "?r = (\<Sum>i<r_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) + r_n"
          and E'_r_m: "lnth E' r_m = (t_r, ta_r)"
          unfolding E' by(rule mthr.if.actions_\<E>E_aux)

        let ?E' = "ldropn (Suc r_m) E'"
        let ?r_m_E' = "ltake (enat r_m) E'"
        have E'_unfold: "E' = lappend (ltake (enat r_m) E') (LCons (lnth E' r_m) ?E')"
          unfolding ldropn_Suc_conv_ldropn[OF r_m] by simp
        hence "mthr.if.mthr.Runs ?start_state (lappend ?r_m_E' (LCons (lnth E' r_m) ?E'))"
          using \<tau>Runs by simp
        then obtain \<sigma>' where \<sigma>_\<sigma>': "mthr.if.mthr.Trsys ?start_state (list_of ?r_m_E') \<sigma>'"
          and \<tau>Runs': "mthr.if.mthr.Runs \<sigma>' (LCons (lnth E' r_m) ?E')"
          by(rule mthr.if.mthr.Runs_lappendE) simp
        from \<tau>Runs' obtain \<sigma>''' where red_ra: "mthr.if.redT \<sigma>' (t_r, ta_r) \<sigma>'''"
          and \<tau>Runs'': "mthr.if.mthr.Runs \<sigma>''' ?E'"
          unfolding E'_r_m by cases

        let ?vs = "mrw_values P Map.empty (map snd ?start_heap_obs)"
        from \<open>E \<in> ?\<E>\<close> wf_exec have "ta_seq_consist P Map.empty (lmap snd (ltake (enat r) E))"
          by(rule jmm.ta_seq_consist_mrwI)(simp add: mrw)
        hence ns: "non_speculative P (\<lambda>_. {}) (lmap snd (ltake (enat r) E))"
          by(rule ta_seq_consist_into_non_speculative) simp
        also note E also note ltake_lappend2 also note E'
        also note E'_unfold also note lmap_lappend_distrib also note lmap_lappend_distrib 
        also note lconcat_lappend also note llist.map(2) also note E'_r_m also note prod.simps(2)
        also note ltake_lappend2 also note lconcat_LCons also note ltake_lappend1
        also note non_speculative_lappend also note lmap_lappend_distrib also note non_speculative_lappend
        also have "lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (ltake (enat r_m) E')) = 
                  llist_of (concat (map (\<lambda>(t, ta). map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of (ltake (enat r_m) E'))))"
          by(simp add: lconcat_llist_of[symmetric] lmap_llist_of[symmetric] llist.map_comp o_def split_def del: lmap_llist_of)
        ultimately
        have "non_speculative P (\<lambda>_. {}) (lmap snd (llist_of ?start_heap_obs))"
          and "non_speculative P (w_values P (\<lambda>_. {}) (map snd ?start_heap_obs)) 
                 (lmap snd (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (ltake (enat r_m) E'))))"
          and ns': "non_speculative P (w_values P (w_values P (\<lambda>_. {}) (map snd ?start_heap_obs)) (map snd (concat (map (\<lambda>(t, ta). map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of (ltake (enat r_m) E'))))))
               (lmap snd (ltake (enat r_n) (llist_of (map (Pair t_r) \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>))))"
          using r r_conv r_m r_n
          by(simp_all add: length_concat o_def split_def sum_list_sum_nth length_list_of_conv_the_enat less_min_eq1 atLeast0LessThan lnth_ltake split: if_split_asm cong: sum.cong_simp)
        hence ns: "non_speculative P (w_values P (\<lambda>_. {}) (map snd ?start_heap_obs)) 
                     (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of (ltake (enat r_m) E')))))"
          unfolding lconcat_llist_of[symmetric] lmap_lconcat lmap_llist_of[symmetric] llist.map_comp o_def split_def
          by(simp)

        from ns'
        have ns': "non_speculative P (w_values P (w_values P (\<lambda>_. {}) (map snd ?start_heap_obs))  (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of (ltake (enat r_m) E'))))) (llist_of (take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>))"
          unfolding map_concat map_map by(simp add: take_map[symmetric] o_def split_def)

        let ?hb = "\<lambda>ta'_r  :: ('addr, 'thread_id, status \<times> 'x, 'heap, 'addr, ('addr, 'thread_id) obs_event action) thread_action. 
             ta_hb_consistent P (?start_heap_obs @ concat (map (\<lambda>(t, ta). map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of (ltake (enat r_m) E'))) @ map (Pair t_r) (take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>)) (llist_of (map (Pair t_r) (drop r_n \<lbrace>ta'_r\<rbrace>\<^bsub>o\<^esub>)))"
        let ?sim = "\<lambda>ta'_r. (if \<exists>ad al v. \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> ! r_n = NormalAction (ReadMem ad al v) then sim_action else (=)) (\<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> ! r_n) (\<lbrace>ta'_r\<rbrace>\<^bsub>o\<^esub> ! r_n)"

        from red_ra obtain ta'_r \<sigma>''''
          where red_ra': "mthr.if.redT \<sigma>' (t_r, ta'_r) \<sigma>''''"
          and eq: "take r_n \<lbrace>ta'_r\<rbrace>\<^bsub>o\<^esub> = take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>"
          and hb: "?hb ta'_r"
          and r_n': "r_n < length \<lbrace>ta'_r\<rbrace>\<^bsub>o\<^esub>"
          and sim: "?sim ta'_r"
        proof(cases)
          case (redT_normal x x' m')
          note tst = \<open>thr \<sigma>' t_r = \<lfloor>(x, no_wait_locks)\<rfloor>\<close>
            and red = \<open>t_r \<turnstile> (x, shr \<sigma>') -ta_r\<rightarrow>i (x', m')\<close>
            and aok = \<open>mthr.if.actions_ok \<sigma>' t_r ta_r\<close>
            and \<sigma>''' = \<open>redT_upd \<sigma>' t_r ta_r x' m' \<sigma>'''\<close>
          from if.hb_completionD[OF hb_completion \<sigma>_\<sigma>'[folded mthr.if.RedT_def] ns tst red aok ns'] r_n
          obtain ta'_r x'' m''
            where red': "t_r \<turnstile> (x, shr \<sigma>') -ta'_r\<rightarrow>i (x'', m'')"
            and aok': "mthr.if.actions_ok \<sigma>' t_r ta'_r"
            and eq': "take r_n \<lbrace>ta'_r\<rbrace>\<^bsub>o\<^esub> = take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>"
            and hb: "?hb ta'_r" 
            and r_n': "r_n < length \<lbrace>ta'_r\<rbrace>\<^bsub>o\<^esub>"
            and sim: "?sim ta'_r" by blast
          from redT_updWs_total[of t_r "wset \<sigma>'" "\<lbrace>ta'_r\<rbrace>\<^bsub>w\<^esub>"]
          obtain \<sigma>'''' where "redT_upd \<sigma>' t_r ta'_r x'' m'' \<sigma>''''" by fastforce
          with red' tst aok' have "mthr.if.redT \<sigma>' (t_r, ta'_r) \<sigma>''''" ..
          thus thesis using eq' hb r_n' sim by(rule that)
        next
          case (redT_acquire x n ln)
          hence "?hb ta_r" using set_convert_RA_not_Read[where ln=ln]
            by -(rule ta_hb_consistent_not_ReadI, fastforce simp del: set_convert_RA_not_Read dest!: in_set_dropD)
          with red_ra r_n show ?thesis by(auto intro: that)
        qed
        from hb
        have "non_speculative P (w_values P (\<lambda>_. {}) (map snd (?start_heap_obs @ concat (map (\<lambda>(t, ta). map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of (ltake (enat r_m) E'))) @ map (Pair t_r) (take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>)))) (lmap snd (llist_of (map (Pair t_r) (drop r_n \<lbrace>ta'_r\<rbrace>\<^bsub>o\<^esub>))))"
          by(rule ta_hb_consistent_into_non_speculative)
        with ns' eq[symmetric] have "non_speculative P (w_values P (\<lambda>_. {}) (map snd (?start_heap_obs @ concat (map (\<lambda>(t, ta). map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of (ltake (enat r_m) E')))))) (llist_of (map snd (map (Pair t_r) \<lbrace>ta'_r\<rbrace>\<^bsub>o\<^esub>)))"
          by(subst append_take_drop_id[where xs="\<lbrace>ta'_r\<rbrace>\<^bsub>o\<^esub>" and n=r_n, symmetric])(simp add: o_def map_concat split_def lappend_llist_of_llist_of[symmetric] non_speculative_lappend del: append_take_drop_id lappend_llist_of_llist_of)
        with ns have ns'': "non_speculative P (w_values P (\<lambda>_. {}) (map snd ?start_heap_obs)) (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of (ltake (enat r_m) E') @ [(t_r, ta'_r)]))))"
          unfolding lconcat_llist_of[symmetric] map_append lappend_llist_of_llist_of[symmetric] lmap_llist_of[symmetric] llist.map_comp
          by(simp add: o_def split_def non_speculative_lappend list_of_lconcat map_concat)
        from \<sigma>_\<sigma>' red_ra' have "mthr.if.RedT ?start_state (list_of ?r_m_E' @ [(t_r, ta'_r)]) \<sigma>''''"
          unfolding mthr.if.RedT_def ..
        with hb_completion
        have hb_completion': "if.hb_completion \<sigma>'''' (?start_heap_obs @ concat (map (\<lambda>(t, ta). map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of (ltake (enat r_m) E') @ [(t_r, ta'_r)])))"
          using ns'' by(rule if.hb_completion_shift)
        from if.hb_completion_Runs[OF hb_completion' ta_hb_consistent_convert_RA]
        obtain ttas' where Runs': "mthr.if.mthr.Runs \<sigma>'''' ttas'"
          and hb': "ta_hb_consistent P (?start_heap_obs @ concat (map (\<lambda>(t, ta). map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of (ltake (enat r_m) E') @ [(t_r, ta'_r)]))) (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ttas'))"
          by blast

        let ?E = "lappend (llist_of ?start_heap_obs) (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (lappend (ltake (enat r_m) E') (LCons (t_r, ta'_r) ttas'))))"

        have \<E>: "lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) (lappend (ltake (enat r_m) E') (LCons (t_r, ta'_r) ttas'))) \<in> mthr.if.\<E> ?start_state"
          by(subst (4) llist_of_list_of[symmetric])(simp, blast intro: mthr.if.\<E>.intros mthr.if.mthr.Trsys_into_Runs \<sigma>_\<sigma>' mthr.if.mthr.Runs.Step red_ra' Runs')
        hence \<E>': "?E \<in> ?\<E>" by blast

        from \<E> have tsa: "thread_start_actions_ok ?E" by(rule thread_start_actions_ok_init_fin)
        also let ?E' = "lappend (llist_of (lift_start_obs start_tid start_heap_obs @ concat (map (\<lambda>(t, ta). map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of (ltake (enat r_m) E'))) @ map (Pair t_r) (take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>))) (lappend (llist_of (map (Pair t_r) (drop r_n \<lbrace>ta'_r\<rbrace>\<^bsub>o\<^esub>))) (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ttas')))"
        have "?E = ?E'"
          using eq[symmetric]
          by(simp add: lmap_lappend_distrib lappend_assoc lappend_llist_of_llist_of[symmetric] lconcat_llist_of[symmetric] lmap_llist_of[symmetric] llist.map_comp o_def split_def del: lmap_llist_of)(simp add: lappend_assoc[symmetric] lmap_lappend_distrib[symmetric] map_append[symmetric] lappend_llist_of_llist_of del: map_append)
        finally have tsa': "thread_start_actions_ok ?E'" .

        from hb hb' eq[symmetric]
        have HB: "ta_hb_consistent P (?start_heap_obs @ concat (map (\<lambda>(t, ta). map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of (ltake (enat r_m) E'))) @ map (Pair t_r) (take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>)) (lappend (llist_of (map (Pair t_r) (drop r_n \<lbrace>ta'_r\<rbrace>\<^bsub>o\<^esub>))) (lconcat (lmap (\<lambda>(t, ta). llist_of (map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) ttas')))"
          by -(rule ta_hb_consistent_lappendI, simp_all add: take_map[symmetric] drop_map[symmetric])
        
        define EE where "EE = llist_of (?start_heap_obs @ concat (map (\<lambda>(t, ta). map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of (ltake (enat r_m) E'))) @ map (Pair t_r) (take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>))"

        from r r_conv have r_conv': "r = (\<Sum>i<r_m. length \<lbrace>snd (lnth E' i)\<rbrace>\<^bsub>o\<^esub>) + r_n + length ?start_heap_obs" by auto
        hence len_EE: "llength EE = enat r" using r_m r_n
          by(auto simp add: EE_def length_concat sum_list_sum_nth atLeast0LessThan lnth_ltake less_min_eq1 split_def min_def length_list_of_conv_the_enat cong: sum.cong_simp)
        
        from r_conv r_m
        have r_conv3: "llength (lconcat (lmap (\<lambda>x. llist_of (map (Pair (fst x)) \<lbrace>snd x\<rbrace>\<^bsub>o\<^esub>)) (ltake (enat r_m) E'))) = enat (r - Suc (length start_heap_obs) - r_n)" 
          apply(simp add: llength_lconcat_lfinite_conv_sum lnth_ltake cong: sum.cong_simp conj_cong)
          apply(auto simp add: sum_hom[where f=enat, symmetric] zero_enat_def less_trans[where y="enat r_m"] intro: sum.cong)
          done            

        have is_ws: "is_write_seen P EE ws"
        proof(rule is_write_seenI)
          fix a ad al v
          assume a: "a \<in> read_actions EE"
            and a_obs: "action_obs EE a = NormalAction (ReadMem ad al v)"
          from a have a_r: "a < r" by cases(simp add: len_EE actions_def)

          from r E'_r_m r_m r_n r_conv3
          have eq: "ltake (enat r) EE = ltake (enat r) E"
            unfolding E E' EE_def
            apply(subst (2) E'_unfold)
            apply(simp add: ltake_lappend2 lappend_llist_of_llist_of[symmetric] lappend_eq_lappend_conv lmap_lappend_distrib lconcat_llist_of[symmetric] o_def split_def lmap_llist_of[symmetric] del: lappend_llist_of_llist_of lmap_llist_of)
            apply(subst ltake_lappend1)
            defer
            apply(simp add: ltake_lmap[symmetric] take_map[symmetric] ltake_llist_of[symmetric] del: ltake_lmap ltake_llist_of)
            apply(auto simp add: min_def)
            done
          hence sim: "ltake (enat r) EE [\<approx>] ltake (enat r) E" by(rule eq_into_sim_actions)
          
          from a sim have a': "a \<in> read_actions E"
            by(rule read_actions_change_prefix)(simp add: a_r)
          from action_obs_change_prefix_eq[OF eq, of a] a_r a_obs
          have a_obs': "action_obs E a = NormalAction (ReadMem ad al v)" by simp
          
          have a_mrw: "P,E \<turnstile> a \<leadsto>mrw ws a" using a_r a' by(rule mrw)
          with \<open>E \<in> ?\<E>\<close> wf_exec have ws_a_a: "ws a < a"
            by(rule jmm.mrw_before)(auto intro: a_r less_trans mrw)
          hence [simp]: "ws a < r" using a_r by simp

          from wf_exec have ws: "is_write_seen P E ws" by(rule wf_exec_is_write_seenD)
          from is_write_seenD[OF this a' a_obs']
          have "ws a \<in> write_actions E"
            and "(ad, al) \<in> action_loc P E (ws a)"
            and "value_written P E (ws a) (ad, al) = v"
            and "\<not> P,E \<turnstile> a \<le>hb ws a"
            and "is_volatile P al \<Longrightarrow> \<not> P,E \<turnstile> a \<le>so ws a"
            and between: "\<And>a'. \<lbrakk> a' \<in> write_actions E; (ad, al) \<in> action_loc P E a'; 
                        P,E \<turnstile> ws a \<le>hb a' \<and> P,E \<turnstile> a' \<le>hb a \<or> is_volatile P al \<and> P,E \<turnstile> ws a \<le>so a' \<and> P,E \<turnstile> a' \<le>so a \<rbrakk>
                      \<Longrightarrow> a' = ws a" by simp_all

          from \<open>ws a \<in> write_actions E\<close> sim[symmetric]
          show "ws a \<in> write_actions EE" by(rule write_actions_change_prefix) simp
          
          from action_loc_change_prefix[OF sim, of "ws a" P] \<open>(ad, al) \<in> action_loc P E (ws a)\<close>
          show "(ad, al) \<in> action_loc P EE (ws a)" by(simp)

          from value_written_change_prefix[OF eq, of "ws a" P] \<open>value_written P E (ws a) (ad, al) = v\<close>
          show "value_written P EE (ws a) (ad, al) = v" by simp
          
           from wf_exec have tsa_E: "thread_start_actions_ok E"
              by(rule wf_exec_thread_start_actions_okD)

          from \<open>\<not> P,E \<turnstile> a \<le>hb ws a\<close> show "\<not> P,EE \<turnstile> a \<le>hb ws a"
          proof(rule contrapos_nn)
            assume "P,EE \<turnstile> a \<le>hb ws a"
            thus "P,E \<turnstile> a \<le>hb ws a" using tsa_E sim
              by(rule happens_before_change_prefix)(simp_all add: a_r)
          qed

          { assume "is_volatile P al"
            hence "\<not> P,E \<turnstile> a \<le>so ws a" by fact
            thus "\<not> P,EE \<turnstile> a \<le>so ws a"
              by(rule contrapos_nn)(rule sync_order_change_prefix[OF _ sim], simp_all add: a_r) }
          
          fix a'
          assume "a' \<in> write_actions EE" "(ad, al) \<in> action_loc P EE a'"
          moreover
          hence [simp]: "a' < r" by cases(simp add: actions_def len_EE)
          ultimately have a': "a' \<in> write_actions E" "(ad, al) \<in> action_loc P E a'"
            using sim action_loc_change_prefix[OF sim, of a' P]
            by(auto intro: write_actions_change_prefix)
          { assume "P,EE \<turnstile> ws a \<le>hb a'" "P,EE \<turnstile> a' \<le>hb a"
            hence "P,E \<turnstile> ws a \<le>hb a'" "P,E \<turnstile> a' \<le>hb a"
              using tsa_E sim a_r by(auto elim!: happens_before_change_prefix)
            with between[OF a'] show "a' = ws a" by simp }
          { assume "is_volatile P al " "P,EE \<turnstile> ws a \<le>so a'" "P,EE \<turnstile> a' \<le>so a"
            with sim a_r between[OF a'] show "a' = ws a"
              by(fastforce elim: sync_order_change_prefix intro!: disjI2 del: disjCI) }
        qed

        with HB tsa'
        have "\<exists>ws'. P \<turnstile> (?E', ws') \<surd> \<and>
                    (\<forall>n. n \<in> read_actions ?E' \<longrightarrow> length (?start_heap_obs @ concat (map (\<lambda>(t, ta). map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of (ltake (enat r_m) E'))) @ map (Pair t_r) (take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>)) \<le> n \<longrightarrow> P,?E' \<turnstile> ws' n \<le>hb n) \<and>
                    (\<forall>n<length (lift_start_obs start_tid start_heap_obs @ concat (map (\<lambda>(t, ta). map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of (ltake (enat r_m) E'))) @ map (Pair t_r) (take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>)). ws' n = ws n)"
          unfolding EE_def
          by(rule ta_hb_consistent_Read_hb)(rule jmm.\<E>_new_actions_for_fun[OF \<E>'[unfolded \<open>?E = ?E'\<close>]])
        also have r_conv'': "length (?start_heap_obs @ concat (map (\<lambda>(t, ta). map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (list_of (ltake (enat r_m) E'))) @ map (Pair t_r) (take r_n \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>)) = r"
          using r_n r_m unfolding r_conv'
          by(auto simp add: length_concat sum_list_sum_nth atLeast0LessThan lnth_ltake split_def o_def less_min_eq1 min_def length_list_of_conv_the_enat cong: sum.cong_simp)
        finally obtain ws' where wf_exec': "P \<turnstile> (?E', ws') \<surd>" 
          and read_hb: "\<And>n. \<lbrakk> n \<in> read_actions ?E'; r \<le> n \<rbrakk> \<Longrightarrow> P,?E' \<turnstile> ws' n \<le>hb n"
          and read_same: "\<And>n. n < r \<Longrightarrow> ws' n = ws n" by blast

        have "?same ?E'"
          apply(subst ltake_lappend1, simp add: r_conv''[symmetric] length_list_of_conv_the_enat)
          unfolding E E' lappend_llist_of_llist_of[symmetric]
          apply(subst (1 2) ltake_lappend2, simp add: r[simplified])
          apply(subst lappend_eq_lappend_conv, simp)
          apply safe
          apply(subst E'_unfold)
          unfolding lmap_lappend_distrib 
          apply(subst lconcat_lappend, simp)
          apply(subst lconcat_llist_of[symmetric])
          apply(subst (3) lmap_llist_of[symmetric])
          apply(subst (3) lmap_llist_of[symmetric])
          apply(subst llist.map_comp)
          apply(simp only: split_def o_def)
          apply(subst llist_of_list_of, simp)
          apply(subst (1 2) ltake_lappend2, simp add: r_conv3)
          apply(subst lappend_eq_lappend_conv, simp)
          apply safe
          unfolding llist.map(2) lconcat_LCons E'_r_m snd_conv fst_conv take_map
          apply(subst ltake_lappend1)
           defer
           apply(subst append_take_drop_id[where xs="\<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub>" and n=r_n, symmetric])
           unfolding map_append lappend_llist_of_llist_of[symmetric]
           apply(subst ltake_lappend1)
            using r_n
            apply(simp add: min_def r_conv3)
           apply(rule refl)
          apply(simp add: r_conv3)
          using r_n by arith

        moreover {
          fix a
          assume "a \<in> read_actions ?E'"
          with read_hb[of a] read_same[of a]
          have "if a < r then ws' a = ws a else P,?E' \<turnstile> ws' a \<le>hb a" by simp }
        hence "?read ?E' ws'" by blast
        moreover from r_m r_n r_n'
        have E'_r: "lnth ?E' r = (t_r, \<lbrace>ta'_r\<rbrace>\<^bsub>o\<^esub> ! r_n)" unfolding r_conv'
          by(auto simp add: lnth_lappend nth_append length_concat sum_list_sum_nth atLeast0LessThan split_beta lnth_ltake less_min_eq1 length_list_of_conv_the_enat cong: sum.cong_simp)
        from E_r r have E_r: "lnth E r = (t_r, \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> ! r_n)"
          unfolding E by(simp add: lnth_lappend)
        have "r \<in> read_actions E \<longleftrightarrow> (\<exists>ad al v. \<lbrace>ta_r\<rbrace>\<^bsub>o\<^esub> ! r_n = NormalAction (ReadMem ad al v))" using True
          by(auto elim!: read_actions.cases simp add: action_obs_def E_r actions_def intro!: read_actions.intros)
        with sim E'_r E_r have "?tid ?E'" "?obs ?E'"
          by(auto simp add: action_tid_def action_obs_def)
        moreover have "?actions ?E'" using r_n r_m r_n' unfolding r_conv'
          by(cases "llength ?E'")(auto simp add: actions_def less_min_eq2 length_concat sum_list_sum_nth atLeast0LessThan split_beta lnth_ltake less_min_eq1 length_list_of_conv_the_enat enat_plus_eq_enat_conv cong: sum.cong_simp)
        ultimately show ?thesis using wf_exec' \<E>'
          unfolding \<open>?E = ?E'\<close> by blast
      qed
    qed
  qed
qed

end

lemma w_value_mrw_value_conf:
  assumes "set_option (vs' adal) \<subseteq> vs adal \<times> UNIV"
  shows "set_option (mrw_value P vs' ob adal) \<subseteq> w_value P vs ob adal \<times> UNIV"
using assms by(cases adal)(cases ob rule: w_value_cases, auto)

lemma w_values_mrw_values_conf:
  assumes "set_option (vs' adal) \<subseteq> vs adal \<times> UNIV"
  shows "set_option (mrw_values P vs' obs adal) \<subseteq> w_values P vs obs adal \<times> UNIV"
using assms
by(induct obs arbitrary: vs' vs)(auto del: subsetI intro: w_value_mrw_value_conf)

lemma w_value_mrw_value_dom_eq_preserve:
  assumes "dom vs' = {adal. vs adal \<noteq> {}}"
  shows "dom (mrw_value P vs' ob) = {adal. w_value P vs ob adal \<noteq> {}}"
using assms
apply(cases ob rule: w_value_cases)
apply(simp_all add: dom_def split_beta del: not_None_eq)
apply(blast elim: equalityE dest: subsetD)+
done

lemma w_values_mrw_values_dom_eq_preserve:
  assumes "dom vs' = {adal. vs adal \<noteq> {}}"
  shows "dom (mrw_values P vs' obs) = {adal. w_values P vs obs adal \<noteq> {}}"
using assms
by(induct obs arbitrary: vs vs')(auto del: equalityI intro: w_value_mrw_value_dom_eq_preserve)

context jmm_multithreaded begin

definition non_speculative_read :: 
  "nat \<Rightarrow> ('l, 'thread_id, 'x, 'm, 'w) state \<Rightarrow> ('addr \<times> addr_loc \<Rightarrow> 'addr val set) \<Rightarrow> bool"
where
  "non_speculative_read n s vs \<longleftrightarrow>
   (\<forall>ttas s' t x ta x' m' i ad al v v'.
       s -\<triangleright>ttas\<rightarrow>* s' \<longrightarrow> non_speculative P vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) \<longrightarrow>
       thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor> \<longrightarrow> t \<turnstile> (x, shr s') -ta\<rightarrow> (x', m') \<longrightarrow> actions_ok s' t ta \<longrightarrow> 
       i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<longrightarrow> 
       non_speculative P (w_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (llist_of (take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) \<longrightarrow>
       \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NormalAction (ReadMem ad al v) \<longrightarrow> 
       v' \<in> w_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas) @ take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (ad, al) \<longrightarrow>
       (\<exists>ta' x'' m''. t \<turnstile> (x, shr s') -ta'\<rightarrow> (x'', m'') \<and> actions_ok s' t ta' \<and>
                      i < length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> \<and> take i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> = take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<and> \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! i = NormalAction (ReadMem ad al v') \<and>
                      length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> \<le> max n (length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)))" 

lemma non_speculative_readI [intro?]:
  "(\<And>ttas s' t x ta x' m' i ad al v v'. 
    \<lbrakk> s -\<triangleright>ttas\<rightarrow>* s'; non_speculative P vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)));
     thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor>; t \<turnstile> (x, shr s') -ta\<rightarrow> (x', m'); actions_ok s' t ta;
     i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>; non_speculative P (w_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (llist_of (take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>));
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NormalAction (ReadMem ad al v);
     v' \<in> w_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas) @ take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (ad, al) \<rbrakk>
    \<Longrightarrow> \<exists>ta' x'' m''. t \<turnstile> (x, shr s') -ta'\<rightarrow> (x'', m'') \<and> actions_ok s' t ta' \<and>
                      i < length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> \<and> take i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> = take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<and> \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! i = NormalAction (ReadMem ad al v') \<and>
                      length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> \<le> max n (length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))
  \<Longrightarrow> non_speculative_read n s vs"
unfolding non_speculative_read_def by blast

lemma non_speculative_readD:
  "\<lbrakk> non_speculative_read n s vs; s -\<triangleright>ttas\<rightarrow>* s'; non_speculative P vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)));
     thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor>; t \<turnstile> (x, shr s') -ta\<rightarrow> (x', m'); actions_ok s' t ta;
     i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>; non_speculative P (w_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (llist_of (take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)); 
     \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NormalAction (ReadMem ad al v);
     v' \<in> w_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas) @ take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (ad, al) \<rbrakk>
  \<Longrightarrow> \<exists>ta' x'' m''. t \<turnstile> (x, shr s') -ta'\<rightarrow> (x'', m'') \<and> actions_ok s' t ta' \<and>
                      i < length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> \<and> take i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> = take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<and> \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! i = NormalAction (ReadMem ad al v') \<and>
                      length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> \<le> max n (length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
unfolding non_speculative_read_def by blast

end

subsection \<open>@{term "non_speculative"} generalises @{term "cut_and_update"} and @{term "ta_hb_consistent"}\<close>

context known_addrs_typing begin

lemma read_non_speculative_new_actions_for:
  fixes status f C M params E
  defines "E \<equiv> lift_start_obs start_tid start_heap_obs"
  and "vs \<equiv> w_values P (\<lambda>_. {}) (map snd E)"
  and "s \<equiv> init_fin_lift_state status (start_state f P C M params)"
  assumes wf: "wf_syscls P"
  and RedT: "mthr.if.RedT s ttas s'"
  and redT: "mthr.if.redT s' (t, ta') s''"
  and read: "NormalAction (ReadMem ad al v) \<in> set \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>"
  and ns: "non_speculative P (\<lambda>_. {}) (llist_of (map snd E @ concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
  and ka: "known_addrs start_tid (f (fst (method P C M)) M (fst (snd (method P C M))) (fst (snd (snd (method P C M)))) (the (snd (snd (snd (method P C M))))) params) \<subseteq> allocated start_heap"
  and wt: "ts_ok (init_fin_lift wfx) (thr s) (shr s)"
  and type_adal: "P,shr s' \<turnstile> ad@al : T"
  shows "\<exists>w. w \<in> new_actions_for P (llist_of (E @ concat (map (\<lambda>(t, ta). map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (ad, al)"
  (is "\<exists>w. ?new_w w")
using RedT redT read ns[unfolded E_def] ka unfolding s_def
proof(cases rule: read_ex_NewHeapElem)
  case (start CTn)
  then obtain n where n: "start_heap_obs ! n = NewHeapElem ad CTn"
    and len: "n < length start_heap_obs"
    unfolding in_set_conv_nth by blast
  from ns have "non_speculative P (w_values P (\<lambda>_. {}) (map snd E)) (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
    unfolding lappend_llist_of_llist_of[symmetric]
    by(simp add: non_speculative_lappend del: lappend_llist_of_llist_of)
  with RedT wt have hext: "start_heap \<unlhd> shr s'"
    unfolding s_def E_def using start_state_vs_conf[OF wf]
    by(auto dest!: init_fin_RedT_hext_incr simp add: start_state_def split_beta init_fin_lift_state_conv_simps)
  
  from start have "typeof_addr start_heap ad = \<lfloor>CTn\<rfloor>"
    by(auto dest: NewHeapElem_start_heap_obsD[OF wf])
  with hext have "typeof_addr (shr s') ad = \<lfloor>CTn\<rfloor>" by(rule typeof_addr_hext_mono)
  with type_adal have "(ad, al) \<in> action_loc_aux P (NormalAction (NewHeapElem ad CTn))" using n len 
    by cases (auto simp add: action_obs_def lnth_lappend1 lift_start_obs_def)
  with n len have "?new_w (Suc n)"
    by(simp add: new_actions_for_def actions_def E_def action_obs_def lift_start_obs_def nth_append)
  thus ?thesis ..
next
  case (Red ttas' s'' t' ta' s''' ttas'' CTn)
  note ttas = \<open>ttas = ttas' @ (t', ta') # ttas''\<close>
  
  from \<open>NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>\<close>
  obtain obs obs' where obs: "\<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> = obs @ NormalAction (NewHeapElem ad CTn) # obs'"
    by(auto dest: split_list)
  
  let ?n = "length (lift_start_obs start_tid start_heap_obs)"
  let ?wa = "?n + length (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas')) + length obs"
  
  have "?wa = ?n + length (concat (map (\<lambda>(t, ta). map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas')) + length obs"
    by(simp add: length_concat o_def split_def)
  also have "\<dots> < length (E @ concat (map (\<lambda>(t, ta). map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))"
    using obs ttas by(simp add: E_def)
  also
  from ttas obs
  have "(E @ concat (map (\<lambda>(t, ta). map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)) ! ?wa = (t', NormalAction (NewHeapElem ad CTn))"
    by(auto simp add: E_def lift_start_obs_def nth_append o_def split_def length_concat)
  moreover
  from \<open>mthr.if.redT s'' (t', ta') s'''\<close> \<open>NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>\<close>
  obtain x_wa x_wa' where ts''t': "thr s'' t' = \<lfloor>(x_wa, no_wait_locks)\<rfloor>"
    and red_wa: "mthr.init_fin t' (x_wa, shr s'') ta' (x_wa', shr s''')"
    by(cases) fastforce+

  from start_state_vs_conf[OF wf]
  have vs: "vs_conf P (shr s) vs" unfolding vs_def E_def s_def
    by(simp add: init_fin_lift_state_conv_simps start_state_def split_def)
  
  from ns
  have ns: "non_speculative P vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas')))"
    and ns': "non_speculative P (w_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas'))) (llist_of \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)"
    and ns'': "non_speculative P (w_values P (w_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas'))) \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas'')))"
    unfolding ttas vs_def
    by(simp_all add: lappend_llist_of_llist_of[symmetric] non_speculative_lappend del: lappend_llist_of_llist_of)
  from \<open>mthr.if.RedT (init_fin_lift_state status (start_state f P C M params)) ttas' s''\<close> wt ns
  have ts_ok'': "ts_ok (init_fin_lift wfx) (thr s'') (shr s'')" using vs unfolding vs_def s_def
    by(rule if_RedT_non_speculative_invar)
  with ts''t' have wfxt': "wfx t' (snd x_wa) (shr s'')" by(cases x_wa)(auto dest: ts_okD)

  from \<open>mthr.if.RedT (init_fin_lift_state status (start_state f P C M params)) ttas' s''\<close> wt ns
  have vs'': "vs_conf P (shr s'') (w_values P (w_values P (\<lambda>_. {}) (map snd E)) (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas')))"
    unfolding s_def E_def vs_def
    by(rule if_RedT_non_speculative_invar)(simp add: start_state_def split_beta init_fin_lift_state_conv_simps start_state_vs_conf[OF wf])
  from if_redT_non_speculative_vs_conf[OF \<open>mthr.if.redT s'' (t', ta') s'''\<close> ts_ok'' _ vs'', of "length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>"] ns'
  have vs''': "vs_conf P (shr s''') (w_values P (w_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas'))) \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)"
    by(simp add: vs_def)

  from \<open>mthr.if.redT s'' (t', ta') s'''\<close> ts_ok'' ns' vs''
  have "ts_ok (init_fin_lift wfx) (thr s''') (shr s''')" 
    unfolding vs_def by(rule if_redT_non_speculative_invar)
  with \<open>mthr.if.RedT s''' ttas'' s'\<close>
  have hext: "shr s''' \<unlhd> shr s'" using ns'' vs'''
    by(rule init_fin_RedT_hext_incr)
  
  from red_wa have "typeof_addr (shr s''') ad = \<lfloor>CTn\<rfloor>"
    using wfxt' \<open>NormalAction (NewHeapElem ad CTn) \<in> set \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>\<close> by cases(auto dest: red_NewHeapElemD)
  with hext have "typeof_addr (shr s') ad = \<lfloor>CTn\<rfloor>" by(rule typeof_addr_hext_mono)
  with type_adal have "(ad, al) \<in> action_loc_aux P (NormalAction (NewHeapElem ad CTn))" by cases auto
  ultimately have "?new_w ?wa"
    by(simp add: new_actions_for_def actions_def action_obs_def)
  thus ?thesis ..
qed

lemma non_speculative_read_into_cut_and_update:
  fixes status f C M params E
  defines "E \<equiv> lift_start_obs start_tid start_heap_obs"
  and "vs \<equiv> w_values P (\<lambda>_. {}) (map snd E)"
  and "s \<equiv> init_fin_lift_state status (start_state f P C M params)"
  and "vs' \<equiv> mrw_values P Map.empty (map snd E)"
  assumes wf: "wf_syscls P"
  and nsr: "if.non_speculative_read n s vs"
  and wt: "ts_ok (init_fin_lift wfx) (thr s) (shr s)"
  and ka: "known_addrs start_tid (f (fst (method P C M)) M (fst (snd (method P C M))) (fst (snd (snd (method P C M)))) (the (snd (snd (snd (method P C M))))) params) \<subseteq> allocated start_heap"
  shows "if.cut_and_update s vs'"
proof(rule if.cut_and_updateI)
  fix ttas s' t x ta x' m'
  assume Red: "mthr.if.RedT s ttas s'"
    and sc: "ta_seq_consist P vs' (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
    and tst: "thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor>"
    and red: "t \<turnstile> (x, shr s') -ta\<rightarrow>i (x', m')"
    and aok: "mthr.if.actions_ok s' t ta"
  let ?vs = "w_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))"
  let ?vs' = "mrw_values P vs' (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))"

  from start_state_vs_conf[OF wf]
  have vs: "vs_conf P (shr s) vs" unfolding vs_def E_def s_def
    by(simp add: init_fin_lift_state_conv_simps start_state_def split_def)

  from sc have ns: "non_speculative P vs (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
    by(rule ta_seq_consist_into_non_speculative)(auto simp add: vs'_def vs_def del: subsetI intro: w_values_mrw_values_conf)

  from ns have ns': "non_speculative P (\<lambda>_. {}) (llist_of (map snd (lift_start_obs start_tid start_heap_obs) @ concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
    unfolding lappend_llist_of_llist_of[symmetric] vs_def
    by(simp add: non_speculative_lappend E_def non_speculative_start_heap_obs del: lappend_llist_of_llist_of)

  have vs_vs'': "\<And>adal. set_option (?vs' adal) \<subseteq> ?vs adal \<times> UNIV"
    by(rule w_values_mrw_values_conf)(auto simp add: vs'_def vs_def del: subsetI intro: w_values_mrw_values_conf)
  from Red wt ns vs
  have wt': "ts_ok (init_fin_lift wfx) (thr s') (shr s')"
    by(rule if_RedT_non_speculative_invar)
  hence wtt: "init_fin_lift wfx t x (shr s')" using tst by(rule ts_okD)

  { fix i
    have "\<exists>ta' x'' m''. t \<turnstile> (x, shr s') -ta'\<rightarrow>i (x'', m'') \<and> mthr.if.actions_ok s' t ta' \<and>
                        length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> \<le> max n (length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) \<and>
                        ta_seq_consist P ?vs' (llist_of (take i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)) \<and>
                        eq_upto_seq_inconsist P (take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (take i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) ?vs' \<and>
                        (ta_seq_consist P ?vs' (llist_of (take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) \<longrightarrow> ta' = ta)"
    proof(induct i)
      case 0 
      show ?case using red aok
        by(auto simp del: split_paired_Ex simp add: eq_upto_seq_inconsist_simps)
    next
      case (Suc i)
      then obtain ta' x'' m''
        where red': "t \<turnstile> (x, shr s') -ta'\<rightarrow>i (x'', m'')"
        and aok': "mthr.if.actions_ok s' t ta'"
        and len: "length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> \<le> max n (length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
        and sc': "ta_seq_consist P ?vs' (llist_of (take i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>))"
        and eusi: "eq_upto_seq_inconsist P (take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (take i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) ?vs'" 
        and ta'_ta: "ta_seq_consist P ?vs' (llist_of (take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) \<Longrightarrow> ta' = ta"
        by blast
      let ?vs'' = "mrw_values P ?vs' (take i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)"
      show ?case
      proof(cases "i < length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> \<and> \<not> ta_seq_consist P ?vs' (llist_of (take (Suc i) \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)) \<and> \<not> ta_seq_consist P ?vs' (llist_of (take (Suc i) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))")
        case True
        hence i: "i < length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>" and "\<not> ta_seq_consist P ?vs'' (LCons (\<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! i) LNil)" using sc'
          by(auto simp add: take_Suc_conv_app_nth lappend_llist_of_llist_of[symmetric] ta_seq_consist_lappend simp del: lappend_llist_of_llist_of)
        then obtain ad al v where ta'_i: "\<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! i = NormalAction (ReadMem ad al v)"
          by(auto split: action.split_asm obs_event.split_asm)
        from ta'_i True have read: "NormalAction (ReadMem ad al v) \<in> set \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>" by(auto simp add: in_set_conv_nth)
        with red' have "ad \<in> known_addrs_if t x" by(rule if_red_read_knows_addr)
        hence "ad \<in> if.known_addrs_state s'" using tst by(rule if.known_addrs_stateI)
        moreover from init_fin_red_read_typeable[OF red' wtt read]
        obtain T where type_adal: "P,shr s' \<turnstile> ad@al : T" ..

        from redT_updWs_total[of t "wset s'" "\<lbrace>ta'\<rbrace>\<^bsub>w\<^esub>"] red' tst aok'
        obtain s'' where redT': "mthr.if.redT s' (t, ta') s''" by(auto dest!: mthr.if.redT.redT_normal)
        with wf Red
        have "\<exists>w. w \<in> new_actions_for P (llist_of (E @ concat (map (\<lambda>(t, ta). map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (ad, al)"
          (is "\<exists>w. ?new_w w")
          using read ns' ka wt type_adal unfolding s_def E_def by(rule read_non_speculative_new_actions_for)
        then obtain w where w: "?new_w w" ..
        have "(ad, al) \<in> dom ?vs'"
        proof(cases "w < length E")
          case True
          with w have "(ad, al) \<in> dom vs'" unfolding vs'_def new_actions_for_def
            by(clarsimp)(erule mrw_values_new_actionD[rotated 1], auto simp del: split_paired_Ex simp add: set_conv_nth action_obs_def nth_append intro!: exI[where x=w])
          also have "dom vs' \<subseteq> dom ?vs'" by(rule mrw_values_dom_mono)
          finally show ?thesis .
        next
          case False
          with w show ?thesis unfolding new_actions_for_def
            apply(clarsimp)
            apply(erule mrw_values_new_actionD[rotated 1])
            apply(simp_all add: set_conv_nth action_obs_def nth_append actions_def)
            apply(rule exI[where x="w - length E"])
            apply(subst nth_map[where f=snd, symmetric])
            apply(simp_all add: length_concat o_def split_def map_concat)
            done
        qed
        hence "(ad, al) \<in> dom (mrw_values P ?vs' (take i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>))"
          by(rule subsetD[OF mrw_values_dom_mono])
        then obtain v' b where v': "mrw_values P ?vs' (take i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) (ad, al) = \<lfloor>(v', b)\<rfloor>" by auto
        moreover from vs_vs''[of "(ad, al)"]
        have "set_option (mrw_values P ?vs' (take i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) (ad, al)) \<subseteq> w_values P ?vs (take i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) (ad, al) \<times> UNIV"
          by(rule w_values_mrw_values_conf)
        ultimately have "v' \<in> w_values P ?vs (take i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) (ad, al)" by simp
        moreover from sc'
        have "non_speculative P (w_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (llist_of (take i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>))"
          by(blast intro: ta_seq_consist_into_non_speculative vs_vs'' del: subsetI)
        ultimately obtain ta'' x'' m''
          where red'': "t \<turnstile> (x, shr s') -ta''\<rightarrow>i (x'', m'')"
          and aok'': "mthr.if.actions_ok s' t ta''"
          and i': "i < length \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>"
          and eq: "take i \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub> = take i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>"
          and ta''_i: "\<lbrace>ta''\<rbrace>\<^bsub>o\<^esub> ! i = NormalAction (ReadMem ad al v')"
          and len': "length \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub> \<le> max n (length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)"
          using if.non_speculative_readD[OF nsr Red ns tst red' aok' i _ ta'_i, of v'] by auto
        from len' len have "length \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub> \<le> max n (length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)" by simp
        moreover have "ta_seq_consist P ?vs' (llist_of (take (Suc i) \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>))"
          using eq sc' i' ta''_i v'
          by(simp add: take_Suc_conv_app_nth lappend_llist_of_llist_of[symmetric] ta_seq_consist_lappend del: lappend_llist_of_llist_of)
        moreover
        have eusi': "eq_upto_seq_inconsist P (take (Suc i) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (take (Suc i) \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>) ?vs'"
        proof(cases "i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>")
          case True
          with i' i len eq eusi ta'_i ta''_i v' show ?thesis
            by(auto simp add: take_Suc_conv_app_nth ta'_ta eq_upto_seq_inconsist_simps intro: eq_upto_seq_inconsist_appendI)
        next
          case False
          with i ta'_ta have "\<not> ta_seq_consist P ?vs' (llist_of (take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))" by auto
          then show ?thesis using False i' eq eusi
            by(simp add: take_Suc_conv_app_nth eq_upto_seq_inconsist_append2)
        qed
        moreover {
          assume "ta_seq_consist P ?vs' (llist_of (take (Suc i) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))"
          with True have "ta'' = ta" by simp }
        ultimately show ?thesis using red'' aok'' True by blast
      next
        case False
        hence "ta_seq_consist P ?vs' (llist_of (take (Suc i) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)) \<or> 
               length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> \<le> i \<or> 
               ta_seq_consist P ?vs' (llist_of (take (Suc i) \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>))" 
          (is "?case1 \<or> ?case2 \<or> ?case3") by auto
        thus ?thesis
        proof(elim disjCE)
          assume "?case1"
          moreover
          hence "eq_upto_seq_inconsist P (take (Suc i) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (take (Suc i) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ?vs'"
            by(rule ta_seq_consist_imp_eq_upto_seq_inconsist_refl)
          ultimately show ?thesis using red aok by fastforce
        next
          assume "?case2" and "\<not> ?case1"
          have "eq_upto_seq_inconsist P (take (Suc i) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (take (Suc i) \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) ?vs'"
          proof(cases "i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>")
            case True
            from \<open>?case2\<close> \<open>\<not> ?case1\<close> have "\<not> ta_seq_consist P ?vs' (llist_of (take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))" by(auto simp add: ta'_ta)
            hence "eq_upto_seq_inconsist P (take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> @ [\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i]) (take i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> @ []) ?vs'"
              by(blast intro: eq_upto_seq_inconsist_appendI[OF eusi])
            thus ?thesis using True \<open>?case2\<close> by(simp add: take_Suc_conv_app_nth)
          next
            case False with eusi \<open>?case2\<close> show ?thesis by simp
          qed
          with red' aok' len sc' eusi \<open>?case2\<close> \<open>\<not> ?case1\<close>show ?thesis
            by (fastforce simp add: take_all simp del: split_paired_Ex)
        next
          assume "?case3" and "\<not> ?case1" and "\<not> ?case2"
          with len eusi ta'_ta
          have "eq_upto_seq_inconsist P (take (Suc i) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (take (Suc i) \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) ?vs'"
            by(cases "i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>")(auto simp add: take_Suc_conv_app_nth lappend_llist_of_llist_of[symmetric] ta_seq_consist_lappend intro: eq_upto_seq_inconsist_appendI eq_upto_seq_inconsist_append2 cong: action.case_cong obs_event.case_cong)
          with red' aok' \<open>?case3\<close> len \<open>\<not> ?case1\<close> show ?thesis by blast
        qed
      qed
    qed }
  from this[of "max n (length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"]
  show "\<exists>ta' x'' m''. t \<turnstile> (x, shr s') -ta'\<rightarrow>i (x'', m'') \<and> mthr.if.actions_ok s' t ta' \<and> ta_seq_consist P ?vs' (llist_of \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) \<and> eq_upto_seq_inconsist P \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ?vs'"
    by(auto simp del: split_paired_Ex cong: conj_cong)
qed

lemma non_speculative_read_into_hb_completion:
  fixes status f C M params E
  defines "E \<equiv> lift_start_obs start_tid start_heap_obs"
  and "vs \<equiv> w_values P (\<lambda>_. {}) (map snd E)"
  and "s \<equiv> init_fin_lift_state status (start_state f P C M params)"
  assumes wf: "wf_syscls P"
  and nsr: "if.non_speculative_read n s vs"
  and wt: "ts_ok (init_fin_lift wfx) (thr s) (shr s)"
  and ka: "known_addrs start_tid (f (fst (method P C M)) M (fst (snd (method P C M))) (fst (snd (snd (method P C M)))) (the (snd (snd (snd (method P C M))))) params) \<subseteq> allocated start_heap"
  shows "if.hb_completion s E"
proof
  fix ttas s' t x ta x' m' i
  assume Red: "mthr.if.RedT s ttas s'"
    and ns: "non_speculative P (w_values P (\<lambda>_. {}) (map snd E)) (llist_of (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
    and tst: "thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor>"
    and red: "t \<turnstile> (x, shr s') -ta\<rightarrow>i (x', m')"
    and aok: "mthr.if.actions_ok s' t ta"
    and nsi: "non_speculative P (w_values P (w_values P (\<lambda>_. {}) (map snd E)) (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (llist_of (take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>))"

  let ?E = "E @ concat (map (\<lambda>(t, ta). map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas) @ map (Pair t) (take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
  let ?vs = "w_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))"

  from ns have ns': "non_speculative P (\<lambda>_. {}) (llist_of (map snd (lift_start_obs start_tid start_heap_obs) @ concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas)))"
    unfolding lappend_llist_of_llist_of[symmetric]
    by(simp add: non_speculative_lappend E_def non_speculative_start_heap_obs del: lappend_llist_of_llist_of)

  from start_state_vs_conf[OF wf]
  have vs: "vs_conf P (shr s) vs" unfolding vs_def E_def s_def
    by(simp add: init_fin_lift_state_conv_simps start_state_def split_def)

  from Red wt ns vs
  have wt': "ts_ok (init_fin_lift wfx) (thr s') (shr s')"
    unfolding vs_def by(rule if_RedT_non_speculative_invar)
  hence wtt: "init_fin_lift wfx t x (shr s')" using tst by(rule ts_okD)

  { fix j
    have "\<exists>ta' x'' m''. t \<turnstile> (x, shr s') -ta'\<rightarrow>i (x'', m'') \<and> mthr.if.actions_ok s' t ta' \<and> length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> \<le> max n (length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) \<and>
                        take i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> = take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<and> 
                        ta_hb_consistent P ?E (llist_of (map (Pair t) (take j (drop i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)))) \<and>
                        (i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<longrightarrow> i < length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) \<and>
                        (if \<exists>ad al v. \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NormalAction (ReadMem ad al v) then sim_action else (=)) (\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i) (\<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! i)"
    proof(induct j)
      case 0 from red aok show ?case by(fastforce simp del: split_paired_Ex)
    next
      case (Suc j)
      then obtain ta' x'' m''
        where red': "t \<turnstile> (x, shr s') -ta'\<rightarrow>i (x'', m'')"
        and aok': "mthr.if.actions_ok s' t ta'"
        and len: "length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> \<le> max n (length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"
        and eq: "take i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> = take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
        and hb: "ta_hb_consistent P ?E (llist_of (map (Pair t) (take j (drop i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>))))"
        and len_i: "i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<longrightarrow> i < length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>"
        and sim_i: "(if \<exists>ad al v. \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NormalAction (ReadMem ad al v) then sim_action else (=)) (\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i) (\<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! i)"
        by blast
      show ?case
      proof(cases "i + j < length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>")
        case False
        with red' aok' len eq hb len_i sim_i show ?thesis by(fastforce simp del: split_paired_Ex)
      next
        case True
        note j = this
        show ?thesis
        proof(cases "\<exists>ad al v. \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! (i + j) = NormalAction (ReadMem ad al v)")
          case True
          then obtain ad al v where ta'_j: "\<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! (i + j) = NormalAction (ReadMem ad al v)" by blast
          hence read: "NormalAction (ReadMem ad al v) \<in> set \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>" using j by(auto simp add: in_set_conv_nth)
          with red' have "ad \<in> known_addrs_if t x" by(rule if_red_read_knows_addr)
          hence "ad \<in> if.known_addrs_state s'" using tst by(rule if.known_addrs_stateI)
          from init_fin_red_read_typeable[OF red' wtt read] obtain T 
            where type_adal: "P,shr s' \<turnstile> ad@al : T" ..

          from redT_updWs_total[of t "wset s'" "\<lbrace>ta'\<rbrace>\<^bsub>w\<^esub>"] red' tst aok'
          obtain s'' where redT': "mthr.if.redT s' (t, ta') s''" by(auto dest!: mthr.if.redT.redT_normal)
          with wf Red
          have "\<exists>w. w \<in> new_actions_for P (llist_of (E @ concat (map (\<lambda>(t, ta). map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (ad, al)"
            (is "\<exists>w. ?new_w w")
            using read ns' ka wt type_adal unfolding s_def E_def
            by(rule read_non_speculative_new_actions_for)
          then obtain w where w: "?new_w w" ..

          define E'' where "E'' = ?E @ map (Pair t) (take (Suc j) (drop i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>))"

          from Red redT' have "mthr.if.RedT s (ttas @ [(t, ta')]) s''" unfolding mthr.if.RedT_def ..
          hence tsa: "thread_start_actions_ok (llist_of (lift_start_obs start_tid start_heap_obs @ concat (map (\<lambda>(t, ta). map (Pair t) \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) (ttas @ [(t, ta')]))))"
            unfolding s_def by(rule thread_start_actions_ok_init_fin_RedT)
          hence "thread_start_actions_ok (llist_of E'')" unfolding E_def[symmetric] E''_def
            by(rule thread_start_actions_ok_prefix)(rule lprefix_llist_ofI, simp, metis append_take_drop_id eq map_append)
          moreover from w have "w \<in> actions (llist_of E'')"
            unfolding E''_def by(auto simp add: new_actions_for_def actions_def)
          moreover have "length ?E + j \<in> actions (llist_of E'')" using j by(auto simp add: E''_def actions_def)
          moreover from w have "is_new_action (action_obs (llist_of E'') w)"
            by(auto simp add: new_actions_for_def action_obs_def actions_def nth_append E''_def)
          moreover have "\<not> is_new_action (action_obs (llist_of E'') (length ?E + j))"
            using j ta'_j by(auto simp add: action_obs_def nth_append min_def E''_def)(subst (asm) nth_map, simp_all)
          ultimately have hb_w: "P,llist_of E'' \<turnstile> w \<le>hb length ?E + j"
            by(rule happens_before_new_not_new)
          
          define writes where
            "writes = {w. P,llist_of E'' \<turnstile> w \<le>hb length ?E + j \<and> w \<in> write_actions (llist_of E'') \<and> 
                 (ad, al) \<in> action_loc P (llist_of E'') w}"

          define w' where "w' = Max_torder (action_order (llist_of E'')) writes"

          have writes_actions: "writes \<subseteq> actions (llist_of E'')" unfolding writes_def actions_def
            by(auto dest!: happens_before_into_action_order elim!: action_orderE simp add: actions_def)
          also have "finite \<dots>" by(simp add: actions_def)
          finally (finite_subset) have "finite writes" .
          moreover from hb_w w have w_writes: "w \<in> writes"
            by(auto 4 3 simp add: writes_def new_actions_for_def action_obs_def actions_def nth_append E''_def intro!: write_actions.intros elim!: is_new_action.cases)
          hence "writes \<noteq> {}" by auto

          with torder_action_order \<open>finite writes\<close> 
          have w'_writes: "w' \<in> writes" using writes_actions unfolding w'_def by(rule Max_torder_in_set)
          moreover
          { fix w''
            assume "w'' \<in> writes"
            with torder_action_order \<open>finite writes\<close>
            have "llist_of E'' \<turnstile> w'' \<le>a w'" using writes_actions unfolding w'_def by(rule Max_torder_above) }
          note w'_maximal = this

          define v' where "v' = value_written P (llist_of E'') w' (ad, al)"

          from nsi ta_hb_consistent_into_non_speculative[OF hb]
          have nsi': "non_speculative P (w_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas))) (llist_of (take (i + j) \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>))"
            unfolding take_add lappend_llist_of_llist_of[symmetric] non_speculative_lappend vs_def eq
            by(simp add: non_speculative_lappend o_def map_concat split_def del: lappend_llist_of_llist_of)
            
          from w'_writes have adal_w': "(ad, al) \<in> action_loc P (llist_of E'') w'" by(simp add: writes_def)
          from w'_writes have "w' \<in> write_actions (llist_of E'')"
            unfolding writes_def by blast
          then obtain "is_write_action (action_obs (llist_of E'') w')" 
            and w'_actions: "w' \<in> actions (llist_of E'')" by cases
          hence "v' \<in> w_values P (\<lambda>_. {}) (map snd E'') (ad, al)"
          proof cases
            case (NewHeapElem ad' CTn)
            hence "NormalAction (NewHeapElem ad' CTn) \<in> set (map snd E'')"
              using w'_actions unfolding in_set_conv_nth
              by(auto simp add: actions_def action_obs_def cong: conj_cong)
            moreover have "ad' = ad" 
              and "(ad, al) \<in> action_loc_aux P (NormalAction (NewHeapElem ad CTn))"
              using adal_w' NewHeapElem by auto
            ultimately show ?thesis using NewHeapElem unfolding v'_def
              by(simp add: value_written.simps w_values_new_actionD)
          next
            case (WriteMem ad' al' v'')
            hence "NormalAction (WriteMem ad' al' v'') \<in> set (map snd E'')"
              using w'_actions unfolding in_set_conv_nth
              by(auto simp add: actions_def action_obs_def cong: conj_cong)
            moreover have "ad' = ad" "al' = al" using adal_w' WriteMem by auto
            ultimately show ?thesis using WriteMem unfolding v'_def
              by(simp add: value_written.simps w_values_WriteMemD)
          qed
          hence "v' \<in> w_values P vs (concat (map (\<lambda>(t, ta). \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>) ttas) @ take (i + j) \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) (ad, al)"
            using j ta'_j eq unfolding E''_def vs_def
            by(simp add: o_def split_def map_concat take_add take_Suc_conv_app_nth)
          from if.non_speculative_readD[OF nsr Red ns[folded vs_def] tst red' aok' j nsi' ta'_j this]
          obtain ta'' x'' m'' 
            where red'': "t \<turnstile> (x, shr s') -ta''\<rightarrow>i (x'', m'')"
            and aok'': "mthr.if.actions_ok s' t ta''"
            and j': "i + j < length \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>"
            and eq': "take (i + j) \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub> = take (i + j) \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>"
            and ta''_j: "\<lbrace>ta''\<rbrace>\<^bsub>o\<^esub> ! (i + j) = NormalAction (ReadMem ad al v')"
            and len': "length \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub> \<le> max n (length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)" by blast

          define EE where "EE = ?E @ map (Pair t) (take j (drop i \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>))"
          define E' where "E' = ?E @ map (Pair t) (take j (drop i \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>)) @ [(t, NormalAction (ReadMem ad al v'))]"

          from len' len have "length \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub> \<le> max n (length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)" by simp
          moreover from eq' eq j j' have "take i \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub> = take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>"
            by(auto simp add: take_add min_def)
          moreover {
            note hb
            also have eq'': "take j (drop i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) = take j (drop i \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>)"
              using eq' j j' by(simp add: take_add min_def)
            also have "ta_hb_consistent P (?E @ list_of (llist_of (map (Pair t) (take j (drop i \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>))))) (llist_of [(t, \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub> ! (i + j))])"
              unfolding llist_of.simps ta_hb_consistent_LCons ta_hb_consistent_LNil ta''_j prod.simps action.simps obs_event.simps list_of_llist_of append_assoc E'_def[symmetric, unfolded append_assoc]
              unfolding EE_def[symmetric, unfolded append_assoc]
            proof(intro conjI TrueI exI[where x=w'] strip)
              have "llist_of E'' [\<approx>] llist_of E'" using j len eq'' ta'_j unfolding E''_def E'_def
                by(auto simp add: sim_actions_def list_all2_append List.list_all2_refl split_beta take_Suc_conv_app_nth take_map[symmetric])
              moreover have "length E'' = length E'" using j j' by(simp add: E''_def E'_def)
              ultimately have sim: "ltake (enat (length E')) (llist_of E'') [\<approx>] ltake (enat (length E')) (llist_of E')" by simp

              from w'_actions \<open>length E'' = length E'\<close>
              have w'_len: "w' < length E'" by(simp add: actions_def)

              from \<open>w' \<in> write_actions (llist_of E'')\<close> sim
              show "w' \<in> write_actions (llist_of E')" by(rule write_actions_change_prefix)(simp add: w'_len)
              from adal_w' action_loc_change_prefix[OF sim, of w' P]
              show "(ad, al) \<in> action_loc P (llist_of E') w'" by(simp add: w'_len)

              from ta'_j j have "length ?E + j \<in> read_actions (llist_of E'')"
                by(auto intro!: read_actions.intros simp add: action_obs_def actions_def E''_def min_def nth_append)(auto)
              hence "w' \<noteq> length ?E + j" using \<open>w' \<in> write_actions (llist_of E'')\<close>
                by(auto dest: read_actions_not_write_actions)
              with w'_len have "w' < length ?E + j" by(simp add: E'_def)
              from j j' len' eq''
              have "ltake (enat (length ?E + j)) (llist_of E'') = ltake (enat (length ?E + j)) (llist_of E')"
                by(auto simp add: E''_def E'_def min_def take_Suc_conv_app_nth)
              from value_written_change_prefix[OF this, of w' P] \<open>w' < length ?E + j\<close>
              show "value_written P (llist_of E') w' (ad, al) = v'" unfolding v'_def by simp

              from \<open>thread_start_actions_ok (llist_of E'')\<close> \<open>llist_of E'' [\<approx>] llist_of E'\<close>
              have tsa'': "thread_start_actions_ok (llist_of E')"
                by(rule thread_start_actions_ok_change)
                
              from w'_writes j j' len len' have "P,llist_of E'' \<turnstile> w' \<le>hb length EE"
                by(auto simp add: EE_def writes_def min_def ac_simps)
              thus "P,llist_of E' \<turnstile> w' \<le>hb length EE" using tsa'' sim
                by(rule happens_before_change_prefix)(simp add: w'_len, simp add: EE_def E'_def)
              
              fix w''
              assume w'': "w'' \<in> write_actions (llist_of E')"
                and adal_w'': "(ad, al) \<in> action_loc P (llist_of E') w''"

              from w'' have w''_len: "w'' < length E'" by(cases)(simp add: actions_def)
              
              from w'' sim[symmetric] have w'': "w'' \<in> write_actions (llist_of E'')"
                by(rule write_actions_change_prefix)(simp add: w''_len)
              from adal_w'' action_loc_change_prefix[OF sim[symmetric], of w'' P] w''_len
              have adal_w'': "(ad, al) \<in> action_loc P (llist_of E'') w''" by simp
              {
                presume w'_w'': "llist_of E' \<turnstile> w' \<le>a w''"
                  and w''_hb: "P,llist_of E' \<turnstile> w'' \<le>hb length EE"
                from w''_hb \<open>thread_start_actions_ok (llist_of E'')\<close> sim[symmetric]
                have "P,llist_of E'' \<turnstile> w'' \<le>hb length EE"
                  by(rule happens_before_change_prefix)(simp add: w''_len, simp add: E'_def EE_def)
                with w'' adal_w'' j j' len len' have "w'' \<in> writes"
                  by(auto simp add: writes_def EE_def min_def ac_simps split: if_split_asm)
                hence "llist_of E'' \<turnstile> w'' \<le>a w'" by(rule w'_maximal)
                hence "llist_of E' \<turnstile> w'' \<le>a w'" using sim
                  by(rule action_order_change_prefix)(simp_all add: w'_len w''_len)
                thus "w'' = w'" "w'' = w'" using w'_w'' by(rule antisymPD[OF antisym_action_order])+ 
              }

              { assume "P,llist_of E' \<turnstile> w' \<le>hb w'' \<and> P,llist_of E' \<turnstile> w'' \<le>hb length EE"
                thus "llist_of E' \<turnstile> w' \<le>a w''" "P,llist_of E' \<turnstile> w'' \<le>hb length EE"
                  by(blast dest: happens_before_into_action_order)+ }
              { assume "is_volatile P al \<and> P,llist_of E' \<turnstile> w' \<le>so w'' \<and> P,llist_of E' \<turnstile> w'' \<le>so length EE"
                then obtain vol: "is_volatile P al"
                  and so: "P,llist_of E' \<turnstile> w' \<le>so w''" 
                  and so': "P,llist_of E' \<turnstile> w'' \<le>so length EE" by blast
                from so show "llist_of E' \<turnstile> w' \<le>a w''" by(blast elim: sync_orderE)

                show "P,llist_of E' \<turnstile> w'' \<le>hb length EE"
                proof(cases "is_new_action (action_obs (llist_of E') w'')")
                  case True
                  with \<open>w'' \<in> write_actions (llist_of E')\<close> ta''_j show ?thesis
                    by cases(rule happens_before_new_not_new[OF tsa''], auto simp add: actions_def EE_def E'_def action_obs_def min_def nth_append)
                next
                  case False
                  with \<open>w'' \<in> write_actions (llist_of E')\<close> \<open>(ad, al) \<in> action_loc P (llist_of E') w''\<close>
                  obtain v'' where "action_obs (llist_of E') w'' = NormalAction (WriteMem ad al v'')"
                    by cases(auto elim: is_write_action.cases)
                  with ta''_j w'' j j' len len'
                  have "P \<turnstile> (action_tid (llist_of E') w'', action_obs (llist_of E') w'') \<leadsto>sw (action_tid (llist_of E') (length EE), action_obs (llist_of E') (length EE))"
                    by(auto simp add: E'_def EE_def action_obs_def min_def nth_append Volatile)
                  with so' have "P,llist_of E' \<turnstile> w'' \<le>sw length EE" by(rule sync_withI)
                  thus ?thesis unfolding po_sw_def [abs_def] by(blast intro: tranclp.r_into_trancl)
                qed }
            qed
            ultimately have "ta_hb_consistent P ?E (lappend (llist_of (map (Pair t) (take j (drop i \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>)))) (llist_of ([(t, \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub> ! (i + j))])))"
              by(rule ta_hb_consistent_lappendI) simp
            hence "ta_hb_consistent P ?E (llist_of (map (Pair t) (take (Suc j) (drop i \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>))))"
              using j' unfolding lappend_llist_of_llist_of by(simp add: take_Suc_conv_app_nth) }
          moreover from len_i have "i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<longrightarrow> i < length \<lbrace>ta''\<rbrace>\<^bsub>o\<^esub>" using eq' j' by auto
          moreover from sim_i eq' ta''_j ta'_j
          have "(if \<exists>ad al v. \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NormalAction (ReadMem ad al v) then sim_action else (=)) (\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i) (\<lbrace>ta''\<rbrace>\<^bsub>o\<^esub> ! i)"
            by(cases "j = 0")(auto split: if_split_asm, (metis add_strict_left_mono add_0_right nth_take)+)
          ultimately show ?thesis using red'' aok'' by blast
        next
          case False
          hence "ta_hb_consistent P (?E @ list_of (llist_of (map (Pair t) (take j (drop i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>))))) (llist_of [(t, \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! (i + j))])"
            by(simp add: ta_hb_consistent_LCons split: action.split obs_event.split)
          with hb
          have "ta_hb_consistent P ?E (lappend (llist_of (map (Pair t) (take j (drop i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>)))) (llist_of ([(t, \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! (i + j))])))"
            by(rule ta_hb_consistent_lappendI) simp
          hence "ta_hb_consistent P ?E (llist_of (map (Pair t) (take (Suc j) (drop i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>))))"
            using j unfolding lappend_llist_of_llist_of by(simp add: take_Suc_conv_app_nth)
          with red' aok' len eq len_i sim_i show ?thesis by blast
        qed
      qed
    qed }
  from this[of "max n (length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub>)"]
  show "\<exists>ta' x'' m''. t \<turnstile> (x, shr s') -ta'\<rightarrow>i (x'', m'') \<and> mthr.if.actions_ok s' t ta' \<and> 
                      take i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> = take i \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<and> 
                      ta_hb_consistent P ?E (llist_of (map (Pair t) (drop i \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>))) \<and> 
                      (i < length \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> \<longrightarrow> i < length \<lbrace>ta'\<rbrace>\<^bsub>o\<^esub>) \<and>
                      (if \<exists>ad al v. \<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i = NormalAction (ReadMem ad al v) then sim_action else (=)) (\<lbrace>ta\<rbrace>\<^bsub>o\<^esub> ! i) (\<lbrace>ta'\<rbrace>\<^bsub>o\<^esub> ! i)"
    by(simp del: split_paired_Ex cong: conj_cong split del: if_split) blast
qed

end

end
