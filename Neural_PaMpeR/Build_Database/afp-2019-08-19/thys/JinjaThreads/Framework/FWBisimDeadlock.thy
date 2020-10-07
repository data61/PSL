(*  Title:      JinjaThreads/Framework/FWBisimDeadlock.thy
    Author:     Andreas Lochbihler
*)

section \<open>Preservation of deadlock across bisimulations\<close>

theory FWBisimDeadlock
imports
  FWBisimulation
  FWDeadlock
begin

context FWdelay_bisimulation_obs begin

lemma actions_ok1_ex_actions_ok2:
  assumes "r1.actions_ok s1 t ta1"
  and "ta1 \<sim>m ta2"
  obtains s2 where "r2.actions_ok s2 t ta2"
proof -
  let ?s2 = "(locks s1, (\<lambda>t. map_option (\<lambda>(x1, ln). (SOME x2. if final1 x1 then final2 x2 else \<not> final2 x2, ln)) (thr s1 t), undefined), wset s1, interrupts s1)"
  from \<open>ta1 \<sim>m ta2\<close> have "\<lbrace>ta1\<rbrace>\<^bsub>c\<^esub> = \<lbrace>ta2\<rbrace>\<^bsub>c\<^esub>" by(simp add: ta_bisim_def)
  with \<open>r1.actions_ok s1 t ta1\<close> have cao1: "r1.cond_action_oks s1 t \<lbrace>ta2\<rbrace>\<^bsub>c\<^esub>" by auto
  have "r2.cond_action_oks ?s2 t \<lbrace>ta2\<rbrace>\<^bsub>c\<^esub>" unfolding r2.cond_action_oks_conv_set
  proof
    fix ct
    assume "ct \<in> set \<lbrace>ta2\<rbrace>\<^bsub>c\<^esub>"
    with cao1 have "r1.cond_action_ok s1 t ct"
      unfolding r1.cond_action_oks_conv_set by auto
    thus "r2.cond_action_ok ?s2 t ct" using ex_final1_conv_ex_final2
      by(cases ct)(fastforce intro: someI_ex[where P=final2])+
  qed
  hence "r2.actions_ok ?s2 t ta2"
    using assms by(auto simp add: ta_bisim_def split del: if_split elim: rev_iffD1[OF _ thread_oks_bisim_inv])
  thus thesis by(rule that)
qed

lemma actions_ok2_ex_actions_ok1:
  assumes "r2.actions_ok s2 t ta2"
  and "ta1 \<sim>m ta2"
  obtains s1 where "r1.actions_ok s1 t ta1"
using FWdelay_bisimulation_obs.actions_ok1_ex_actions_ok2[OF FWdelay_bisimulation_obs_flip] assms
unfolding flip_simps .

lemma ex_actions_ok1_conv_ex_actions_ok2:
  "ta1 \<sim>m ta2 \<Longrightarrow> (\<exists>s1. r1.actions_ok s1 t ta1) \<longleftrightarrow> (\<exists>s2. r2.actions_ok s2 t ta2)"
by(metis actions_ok1_ex_actions_ok2 actions_ok2_ex_actions_ok1)

end

context FWdelay_bisimulation_diverge begin

lemma no_\<tau>Move1_\<tau>s_to_no_\<tau>Move2:
  fixes no_\<tau>moves1 no_\<tau>moves2
  defines "no_\<tau>moves1 \<equiv> \<lambda>s1 t. wset s1 t = None \<and> (\<exists>x. thr s1 t = \<lfloor>(x, no_wait_locks)\<rfloor> \<and> (\<forall>x' m'. \<not> r1.silent_move t (x, shr s1) (x', m')))"
  defines "no_\<tau>moves2 \<equiv> \<lambda>s2 t. wset s2 t = None \<and> (\<exists>x. thr s2 t = \<lfloor>(x, no_wait_locks)\<rfloor> \<and> (\<forall>x' m'. \<not> r2.silent_move t (x, shr s2) (x', m')))"
  assumes mbisim: "s1 \<approx>m (ls2, (ts2, m2), ws2, is2)"
  
  shows "\<exists>ts2'. r2.mthr.silent_moves (ls2, (ts2, m2), ws2, is2) (ls2, (ts2', m2), ws2, is2) \<and> 
                (\<forall>t. no_\<tau>moves1 s1 t \<longrightarrow> no_\<tau>moves2 (ls2, (ts2', m2), ws2, is2) t) \<and> s1 \<approx>m (ls2, (ts2', m2), ws2, is2)"
proof -
  from mbisim have "finite (dom (thr s1))" by(simp add: mbisim_def)
  hence "finite {t. no_\<tau>moves1 s1 t}" unfolding no_\<tau>moves1_def
    by-(rule finite_subset, auto)
  thus ?thesis using \<open>s1 \<approx>m (ls2, (ts2, m2), ws2, is2)\<close>
  proof(induct A\<equiv>"{t. no_\<tau>moves1 s1 t}" arbitrary: s1 ts2 rule: finite_induct)
    case empty
    from \<open>{} = {t. no_\<tau>moves1 s1 t}\<close>[symmetric] have "no_\<tau>moves1 s1 = (\<lambda>t. False)"
      by(auto intro: ext)
    thus ?case using \<open>s1 \<approx>m (ls2, (ts2, m2), ws2, is2)\<close> by auto
  next
    case (insert t A)
    note mbisim = \<open>s1 \<approx>m (ls2, (ts2, m2), ws2, is2)\<close>
    from \<open>insert t A = {t. no_\<tau>moves1 s1 t}\<close>
    have "no_\<tau>moves1 s1 t" by auto
    then obtain x1 where ts1t: "thr s1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>"
      and ws1t: "wset s1 t = None"
      and \<tau>1: "\<And>x1m1'. \<not> r1.silent_move t (x1, shr s1) x1m1'"
      by(auto simp add: no_\<tau>moves1_def)

    from ts1t mbisim obtain x2 where ts2t: "ts2 t = \<lfloor>(x2, no_wait_locks)\<rfloor>"
      and "t \<turnstile> (x1, shr s1) \<approx> (x2, m2)" by(auto dest: mbisim_thrD1)
    from mbisim ws1t have "ws2 t = None" by(simp add: mbisim_def)

    let ?s1 = "(locks s1, ((thr s1)(t := None), shr s1), wset s1, interrupts s1)"
    let ?s2 = "(ls2, (ts2(t := None), m2), ws2, is2)"
    from \<open>insert t A = {t. no_\<tau>moves1 s1 t}\<close> \<open>t \<notin> A\<close>
    have A: "A = {t. no_\<tau>moves1 ?s1 t}" by(auto simp add: no_\<tau>moves1_def)
    have "?s1 \<approx>m ?s2"
    proof(rule mbisimI)
      from mbisim
      show "finite (dom (thr ?s1))" "locks ?s1 = locks ?s2" "wset ?s1 = wset ?s2" "interrupts ?s1 = interrupts ?s2"
        by(simp_all add: mbisim_def)
    next
      from mbisim_wset_thread_ok1[OF mbisim] ws1t show "wset_thread_ok (wset ?s1) (thr ?s1)"
        by(auto intro!: wset_thread_okI dest: wset_thread_okD split: if_split_asm)
    next
      fix t'
      assume "thr ?s1 t' = None"
      with mbisim_thrNone_eq[OF mbisim, of t']
      show "thr ?s2 t' = None" by auto
    next
      fix t' x1 ln
      assume "thr ?s1 t' = \<lfloor>(x1, ln)\<rfloor>"
      hence "thr s1 t' = \<lfloor>(x1, ln)\<rfloor>" "t' \<noteq> t" by(auto split: if_split_asm)
      with mbisim_thrD1[OF mbisim \<open>thr s1 t' = \<lfloor>(x1, ln)\<rfloor>\<close>] mbisim
      show "\<exists>x2. thr ?s2 t' = \<lfloor>(x2, ln)\<rfloor> \<and> t' \<turnstile> (x1, shr ?s1) \<approx> (x2, shr ?s2) \<and> (wset ?s2 t' = None \<or> x1 \<approx>w x2)"
        by(auto simp add: mbisim_def)
    qed
    with A have "\<exists>ts2'. r2.mthr.silent_moves ?s2 (ls2, (ts2', m2), ws2, is2) \<and> (\<forall>t. no_\<tau>moves1 ?s1 t \<longrightarrow> no_\<tau>moves2 (ls2, (ts2', m2), ws2, is2) t) \<and> ?s1 \<approx>m (ls2, (ts2', m2), ws2, is2)" by(rule insert)
    then obtain ts2' where "r2.mthr.silent_moves ?s2 (ls2, (ts2', m2), ws2, is2)"
      and no_\<tau>: "\<And>t. no_\<tau>moves1 ?s1 t \<Longrightarrow> no_\<tau>moves2 (ls2, (ts2', m2), ws2, is2) t"
      and "?s1 \<approx>m (ls2, (ts2', m2), ws2, is2)" by auto
    let ?s2' = "(ls2, (ts2'(t \<mapsto> (x2, no_wait_locks)), m2), ws2, is2)"
    from ts2t have "ts2(t \<mapsto> (x2, no_wait_locks)) = ts2" by(auto intro: ext)
    with r2.\<tau>mRedT_add_thread_inv[OF \<open>r2.mthr.silent_moves ?s2 (ls2, (ts2', m2), ws2, is2)\<close>, of t "(x2, no_wait_locks)"]
    have "r2.mthr.silent_moves (ls2, (ts2, m2), ws2, is2) ?s2'" by simp
    from no_\<tau>move1_\<tau>s_to_no_\<tau>move2[OF \<open>t \<turnstile> (x1, shr s1) \<approx> (x2, m2)\<close> \<tau>1]
    obtain x2' m2' where "r2.silent_moves t (x2, m2) (x2', m2')" 
      and "\<And>x2'' m2''. \<not> r2.silent_move t (x2', m2') (x2'', m2'')" 
      and "t \<turnstile> (x1, shr s1) \<approx> (x2', m2')" by auto
    let ?s2'' = "(ls2, (ts2'(t \<mapsto> (x2', no_wait_locks)), m2'), ws2, is2)"
    from red2_rtrancl_\<tau>_heapD[OF \<open>r2.silent_moves t (x2, m2) (x2', m2')\<close> \<open>t \<turnstile> (x1, shr s1) \<approx> (x2, m2)\<close>]
    have "m2' = m2" by simp
    with \<open>r2.silent_moves t (x2, m2) (x2', m2')\<close> have "r2.silent_moves t (x2, shr ?s2') (x2', m2)" by simp
    hence "r2.mthr.silent_moves ?s2' (redT_upd_\<epsilon> ?s2' t x2' m2)"
      by(rule red2_rtrancl_\<tau>_into_RedT_\<tau>)(auto simp add: \<open>ws2 t = None\<close> intro: \<open>t \<turnstile> (x1, shr s1) \<approx> (x2, m2)\<close>)
    also have "redT_upd_\<epsilon> ?s2' t x2' m2 = ?s2''" using \<open>m2' = m2\<close>
      by(auto simp add: fun_eq_iff redT_updLns_def finfun_Diag_const2 o_def)
    finally (back_subst) have "r2.mthr.silent_moves (ls2, (ts2, m2), ws2, is2) ?s2''" 
      using \<open>r2.mthr.silent_moves (ls2, (ts2, m2), ws2, is2) ?s2'\<close> by-(rule rtranclp_trans)
    moreover {
      fix t'
      assume no_\<tau>1: "no_\<tau>moves1 s1 t'"
      have "no_\<tau>moves2 ?s2'' t'"
      proof(cases "t' = t")
        case True thus ?thesis
          using \<open>ws2 t = None\<close> \<open>\<And>x2'' m2''. \<not> r2.silent_move t (x2', m2') (x2'', m2'')\<close> by(simp add: no_\<tau>moves2_def)
      next
        case False
        with no_\<tau>1 have "no_\<tau>moves1 ?s1 t'" by(simp add: no_\<tau>moves1_def)
        hence "no_\<tau>moves2 (ls2, (ts2', m2), ws2, is2) t'"
          by(rule \<open>no_\<tau>moves1 ?s1 t' \<Longrightarrow> no_\<tau>moves2 (ls2, (ts2', m2), ws2, is2) t'\<close>)
        with False \<open>m2' = m2\<close> show ?thesis by(simp add: no_\<tau>moves2_def)
      qed }
    moreover have "s1 \<approx>m ?s2''"
    proof(rule mbisimI)
      from mbisim
      show "finite (dom (thr s1))" "locks s1 = locks ?s2''" "wset s1 = wset ?s2''" "interrupts s1 = interrupts ?s2''"
        by(simp_all add: mbisim_def)
    next
      from mbisim show "wset_thread_ok (wset s1) (thr s1)" by(rule mbisim_wset_thread_ok1)
    next
      fix t'
      assume "thr s1 t' = None"
      hence "thr ?s1 t' = None" "t' \<noteq> t" using ts1t by auto
      with mbisim_thrNone_eq[OF \<open>?s1 \<approx>m (ls2, (ts2', m2), ws2, is2)\<close>, of t']
      show "thr ?s2'' t' = None" by simp
    next
      fix t' x1' ln'
      assume "thr s1 t' = \<lfloor>(x1', ln')\<rfloor>"
      show "\<exists>x2. thr ?s2'' t' = \<lfloor>(x2, ln')\<rfloor> \<and> t' \<turnstile> (x1', shr s1) \<approx> (x2, shr ?s2'') \<and> (wset ?s2'' t' = None \<or> x1' \<approx>w x2)"
      proof(cases "t = t'")
        case True
        with \<open>thr s1 t' = \<lfloor>(x1', ln')\<rfloor>\<close> ts1t \<open>t \<turnstile> (x1, shr s1) \<approx> (x2', m2')\<close> \<open>m2' = m2\<close> \<open>ws2 t = None\<close>
        show ?thesis by auto
      next
        case False
        with mbisim_thrD1[OF \<open>?s1 \<approx>m (ls2, (ts2', m2), ws2, is2)\<close>, of t' x1' ln'] \<open>thr s1 t' = \<lfloor>(x1', ln')\<rfloor>\<close> \<open>m2' = m2\<close> mbisim
        show ?thesis by(auto simp add: mbisim_def)
      qed
    qed
    ultimately show ?case unfolding \<open>m2' = m2\<close> by blast
  qed
qed

lemma no_\<tau>Move2_\<tau>s_to_no_\<tau>Move1:
  fixes no_\<tau>moves1 no_\<tau>moves2
  defines "no_\<tau>moves1 \<equiv> \<lambda>s1 t. wset s1 t = None \<and> (\<exists>x. thr s1 t = \<lfloor>(x, no_wait_locks)\<rfloor> \<and> (\<forall>x' m'. \<not> r1.silent_move t (x, shr s1) (x', m')))"
  defines "no_\<tau>moves2 \<equiv> \<lambda>s2 t. wset s2 t = None \<and> (\<exists>x. thr s2 t = \<lfloor>(x, no_wait_locks)\<rfloor> \<and> (\<forall>x' m'. \<not> r2.silent_move t (x, shr s2) (x', m')))"
  assumes "(ls1, (ts1, m1), ws1, is1) \<approx>m s2"
  
  shows "\<exists>ts1'. r1.mthr.silent_moves (ls1, (ts1, m1), ws1, is1) (ls1, (ts1', m1), ws1, is1) \<and>
                (\<forall>t. no_\<tau>moves2 s2 t \<longrightarrow> no_\<tau>moves1 (ls1, (ts1', m1), ws1, is1) t) \<and> (ls1, (ts1', m1), ws1, is1) \<approx>m s2"
using assms FWdelay_bisimulation_diverge.no_\<tau>Move1_\<tau>s_to_no_\<tau>Move2[OF FWdelay_bisimulation_diverge_flip]
unfolding flip_simps by blast

lemma deadlock_mbisim_not_final_thread_pres:
  assumes dead: "t \<in> r1.deadlocked s1 \<or> r1.deadlock s1"
  and nfin: "r1.not_final_thread s1 t"
  and fin: "r1.final_thread s1 t \<Longrightarrow> r2.final_thread s2 t"
  and mbisim: "s1 \<approx>m s2"
  shows "r2.not_final_thread s2 t"
proof -
  from nfin obtain x1 ln where "thr s1 t = \<lfloor>(x1, ln)\<rfloor>" by cases auto
  with mbisim obtain x2 where "thr s2 t = \<lfloor>(x2, ln)\<rfloor>" "t \<turnstile> (x1, shr s1) \<approx> (x2, shr s2)" "wset s1 t = None \<or> x1 \<approx>w x2" 
    by(auto dest: mbisim_thrD1)
  show "r2.not_final_thread s2 t"
  proof(cases "wset s1 t = None \<and> ln = no_wait_locks")
    case False
    with \<open>r1.not_final_thread s1 t\<close> \<open>thr s1 t = \<lfloor>(x1, ln)\<rfloor>\<close> \<open>thr s2 t = \<lfloor>(x2, ln)\<rfloor>\<close> mbisim 
    show ?thesis by cases(auto simp add: mbisim_def r2.not_final_thread_iff)
  next
    case True
    with \<open>r1.not_final_thread s1 t\<close> \<open>thr s1 t = \<lfloor>(x1, ln)\<rfloor>\<close> have "\<not> final1 x1" by(cases) auto
    have "\<not> final2 x2"
    proof
      assume "final2 x2"
      with final2_simulation[OF \<open>t \<turnstile> (x1, shr s1) \<approx> (x2, shr s2)\<close>]
      obtain x1' m1' where "r1.silent_moves t (x1, shr s1) (x1', m1')" "t \<turnstile> (x1', m1') \<approx> (x2, shr s2)" "final1 x1'" by auto
      from \<open>r1.silent_moves t (x1, shr s1) (x1', m1')\<close> have "x1' = x1"
      proof(cases rule: converse_rtranclpE2[consumes 1, case_names refl step])
        case (step x1'' m1'')
        from \<open>r1.silent_move t (x1, shr s1) (x1'', m1'')\<close>
        have "t \<turnstile> (x1, shr s1) -1-\<epsilon>\<rightarrow> (x1'', m1'')" by(auto dest: r1.silent_tl)
        hence "r1.redT s1 (t, \<epsilon>) (redT_upd_\<epsilon> s1 t x1'' m1'')"
          using \<open>thr s1 t = \<lfloor>(x1, ln)\<rfloor>\<close> True
          by -(erule r1.redT_normal, auto simp add: redT_updLns_def finfun_Diag_const2 o_def redT_updWs_def)
        hence False using dead by(auto intro: r1.deadlock_no_red r1.red_no_deadlock)
        thus ?thesis ..
      qed simp
      with \<open>\<not> final1 x1\<close> \<open>final1 x1'\<close> show False by simp
    qed
    thus ?thesis using \<open>thr s2 t = \<lfloor>(x2, ln)\<rfloor>\<close> by(auto simp add: r2.not_final_thread_iff)
  qed
qed

lemma deadlocked1_imp_\<tau>s_deadlocked2:
  assumes mbisim: "s1 \<approx>m s2"
  and dead: "t \<in> r1.deadlocked s1"
  shows "\<exists>s2'. r2.mthr.silent_moves s2 s2' \<and> t \<in> r2.deadlocked s2' \<and> s1 \<approx>m s2'"
proof -
  from mfinal1_inv_simulation[OF mbisim]
  obtain ls2 ts2 m2 ws2 is2 where red1: "r2.mthr.silent_moves s2 (ls2, (ts2, m2), ws2, is2)"
    and "s1 \<approx>m (ls2, (ts2, m2), ws2, is2)" and "m2 = shr s2" 
    and fin: "\<And>t. r1.final_thread s1 t \<Longrightarrow> r2.final_thread (ls2, (ts2, m2), ws2, is2) t" by fastforce
  from no_\<tau>Move1_\<tau>s_to_no_\<tau>Move2[OF \<open>s1 \<approx>m (ls2, (ts2, m2), ws2, is2)\<close>]
  obtain ts2' where red2: "r2.mthr.silent_moves (ls2, (ts2, m2), ws2, is2) (ls2, (ts2', m2), ws2, is2)"
    and no_\<tau>: "\<And>t x1 x2 x2' m2'. \<lbrakk> wset s1 t = None; thr s1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>; ts2' t = \<lfloor>(x2, no_wait_locks)\<rfloor>;
                           \<And>x' m'. r1.silent_move t (x1, shr s1) (x', m') \<Longrightarrow> False \<rbrakk>
              \<Longrightarrow>  \<not> r2.silent_move t (x2, m2) (x2', m2')"
    and mbisim: "s1 \<approx>m (ls2, (ts2', m2), ws2, is2)" by fastforce
  from mbisim have mbisim_eqs: "ls2 = locks s1" "ws2 = wset s1" "is2 = interrupts s1"
    by(simp_all add: mbisim_def)
  let ?s2 = "(ls2, (ts2', m2), ws2, is2)"
  from red2 have fin': "\<And>t. r1.final_thread s1 t \<Longrightarrow> r2.final_thread ?s2 t"
    by(rule r2.\<tau>mRedT_preserves_final_thread)(rule fin)
  from dead
  have "t \<in> r2.deadlocked ?s2"
  proof(coinduct)
    case (deadlocked t)
    thus ?case
    proof(cases rule: r1.deadlocked_elims)
      case (lock x1)
      hence csmw: "\<And>LT. r1.can_sync t x1 (shr s1) LT \<Longrightarrow>
                   \<exists>lt\<in>LT. r1.must_wait s1 t lt (r1.deadlocked s1 \<union> r1.final_threads s1)"
        by blast
      from \<open>thr s1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>\<close> mbisim obtain x2
        where "ts2' t = \<lfloor>(x2, no_wait_locks)\<rfloor>" and bisim: "t \<turnstile> (x1, shr s1) \<approx> (x2, m2)"
        by(auto dest: mbisim_thrD1)
      note \<open>ts2' t = \<lfloor>(x2, no_wait_locks)\<rfloor>\<close> moreover
      { from \<open>r1.must_sync t x1 (shr s1)\<close> obtain ta1 x1' m1'
          where r1: "t \<turnstile> (x1, shr s1) -1-ta1\<rightarrow> (x1', m1')"
          and s1': "\<exists>s1'. r1.actions_ok s1' t ta1" by(fastforce elim: r1.must_syncE)
        have "\<not> \<tau>move1 (x1, shr s1) ta1 (x1', m1')" (is "\<not> ?\<tau>")
        proof
          assume "?\<tau>"
          hence "ta1 = \<epsilon>" by(rule r1.silent_tl)
          with r1 have "r1.can_sync t x1 (shr s1) {}"
            by(auto intro!: r1.can_syncI simp add: collect_locks_def collect_interrupts_def)
          from csmw[OF this] show False by blast
        qed
        from simulation1[OF bisim r1 this]
        obtain x2' m2' x2'' m2'' ta2 where r2: "r2.silent_moves t (x2, m2) (x2', m2')"
          and r2': "t \<turnstile> (x2', m2') -2-ta2\<rightarrow>  (x2'', m2'')"
          and \<tau>2: "\<not> \<tau>move2 (x2', m2') ta2 (x2'', m2'')"
          and bisim': "t \<turnstile> (x1', m1') \<approx> (x2'', m2'')" and tasim: "ta1 \<sim>m ta2" by auto
        from r2
        have "\<exists>ta2 x2' m2' s2'. t \<turnstile> (x2, m2) -2-ta2\<rightarrow> (x2', m2') \<and> r2.actions_ok s2' t ta2"
        proof(cases rule: converse_rtranclpE2[consumes 1, case_names base step])
          case base
          from r2'[folded base] s1'[unfolded ex_actions_ok1_conv_ex_actions_ok2[OF tasim]]
          show ?thesis by blast
        next
          case (step x2''' m2''')
          hence "t \<turnstile> (x2, m2) -2-\<epsilon>\<rightarrow> (x2''', m2''')" by(auto dest: r2.silent_tl)
          moreover have "r2.actions_ok (undefined, (undefined, undefined), Map.empty, undefined) t \<epsilon>" by auto
          ultimately show ?thesis by-(rule exI conjI|assumption)+
        qed
        hence "r2.must_sync t x2 m2" unfolding r2.must_sync_def2 . }
      moreover
      { fix LT
        assume "r2.can_sync t x2 m2 LT"
        then obtain ta2 x2' m2' where r2: "t \<turnstile> (x2, m2) -2-ta2\<rightarrow> (x2', m2')"
          and LT: "LT = collect_locks \<lbrace>ta2\<rbrace>\<^bsub>l\<^esub> <+> collect_cond_actions \<lbrace>ta2\<rbrace>\<^bsub>c\<^esub> <+> collect_interrupts \<lbrace>ta2\<rbrace>\<^bsub>i\<^esub>"
          by(auto elim: r2.can_syncE)
        from \<open>wset s1 t = None\<close> \<open>thr s1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>\<close> \<open>ts2' t = \<lfloor>(x2, no_wait_locks)\<rfloor>\<close>
        have "\<not> r2.silent_move t (x2, m2) (x2', m2')"
        proof(rule no_\<tau>)
          fix x1' m1'
          assume "r1.silent_move t (x1, shr s1) (x1', m1')"
          hence "t \<turnstile> (x1, shr s1) -1-\<epsilon>\<rightarrow> (x1', m1')" by(auto dest: r1.silent_tl)
          hence "r1.can_sync t x1 (shr s1) {}"
            by(auto intro: r1.can_syncI simp add: collect_locks_def collect_interrupts_def)
          with csmw[OF this] show False by blast
        qed
        with r2 have "\<not> \<tau>move2 (x2, m2) ta2 (x2', m2')" by auto
        from simulation2[OF bisim r2 this] obtain x1' m1' x1'' m1'' ta1
          where \<tau>r1: "r1.silent_moves t (x1, shr s1) (x1', m1')"
          and r1: "t \<turnstile> (x1', m1') -1-ta1\<rightarrow> (x1'', m1'')"
          and n\<tau>1: "\<not> \<tau>move1 (x1', m1') ta1 (x1'', m1'')"
          and bisim': "t \<turnstile> (x1'', m1'') \<approx> (x2', m2')"
          and tlsim: "ta1 \<sim>m ta2" by auto
        from \<tau>r1 obtain [simp]: "x1' = x1" "m1' = shr s1"
        proof(cases rule: converse_rtranclpE2[consumes 1, case_names refl step])
          case (step X M)
          from \<open>r1.silent_move t (x1, shr s1) (X, M)\<close>
          have "t \<turnstile> (x1, shr s1) -1-\<epsilon>\<rightarrow> (X, M)" by(auto dest: r1.silent_tl)
          hence "r1.can_sync t x1 (shr s1) {}"
            by(auto intro: r1.can_syncI simp add: collect_locks_def collect_interrupts_def)
          with csmw[OF this] have False by blast
          thus ?thesis ..
        qed blast
        from tlsim LT have "LT = collect_locks \<lbrace>ta1\<rbrace>\<^bsub>l\<^esub> <+> collect_cond_actions \<lbrace>ta1\<rbrace>\<^bsub>c\<^esub> <+> collect_interrupts \<lbrace>ta1\<rbrace>\<^bsub>i\<^esub>"
          by(auto simp add: ta_bisim_def)
        with r1 have "r1.can_sync t x1 (shr s1) LT" by(auto intro: r1.can_syncI)
        from csmw[OF this] obtain lt 
          where lt: "lt \<in> LT" and mw: "r1.must_wait s1 t lt (r1.deadlocked s1 \<union> r1.final_threads s1)" by blast
        have subset: "r1.deadlocked s1 \<union> r1.final_threads s1 \<subseteq> r1.deadlocked s1 \<union> r2.deadlocked s2 \<union> r2.final_threads ?s2"
          by(auto dest: fin')
        from mw have "r2.must_wait ?s2 t lt (r1.deadlocked s1 \<union> r2.deadlocked ?s2 \<union> r2.final_threads ?s2)"
        proof(cases rule: r1.must_wait_elims)
          case lock thus ?thesis by(auto simp add: mbisim_eqs dest!: fin')
        next
          case (join t')
          from \<open>r1.not_final_thread s1 t'\<close> obtain x1 ln
            where "thr s1 t' = \<lfloor>(x1, ln)\<rfloor>" by cases auto
          with mbisim obtain x2 where "ts2' t' = \<lfloor>(x2, ln)\<rfloor>" "t' \<turnstile> (x1, shr s1) \<approx> (x2, m2)" by(auto dest: mbisim_thrD1)
          show ?thesis
          proof(cases "wset s1 t' = None \<and> ln = no_wait_locks")
            case False
            with \<open>r1.not_final_thread s1 t'\<close> \<open>thr s1 t' = \<lfloor>(x1, ln)\<rfloor>\<close> \<open>ts2' t' = \<lfloor>(x2, ln)\<rfloor>\<close> \<open>lt = Inr (Inl t')\<close> join
            show ?thesis by(auto simp add: mbisim_eqs r2.not_final_thread_iff r1.final_thread_def)
          next
            case True
            with \<open>r1.not_final_thread s1 t'\<close> \<open>thr s1 t' = \<lfloor>(x1, ln)\<rfloor>\<close> have "\<not> final1 x1" by(cases) auto
            with join \<open>thr s1 t' = \<lfloor>(x1, ln)\<rfloor>\<close> have "t' \<in> r1.deadlocked s1" by(auto simp add: r1.final_thread_def)
            have "\<not> final2 x2"
            proof
              assume "final2 x2"
              with final2_simulation[OF \<open>t' \<turnstile> (x1, shr s1) \<approx> (x2, m2)\<close>]
              obtain x1' m1' where "r1.silent_moves t' (x1, shr s1) (x1', m1')"
                and "t' \<turnstile> (x1', m1') \<approx> (x2, m2)" "final1 x1'" by auto
              from \<open>r1.silent_moves t' (x1, shr s1) (x1', m1')\<close> have "x1' = x1"
              proof(cases rule: converse_rtranclpE2[consumes 1, case_names refl step])
                case (step x1'' m1'')
                from \<open>r1.silent_move t' (x1, shr s1) (x1'', m1'')\<close>
                have "t' \<turnstile> (x1, shr s1) -1-\<epsilon>\<rightarrow> (x1'', m1'')" by(auto dest: r1.silent_tl)
                hence "r1.redT s1 (t', \<epsilon>) (redT_upd_\<epsilon> s1 t' x1'' m1'')"
                  using \<open>thr s1 t' = \<lfloor>(x1, ln)\<rfloor>\<close> True
                  by -(erule r1.redT_normal, auto simp add: redT_updLns_def redT_updWs_def finfun_Diag_const2 o_def)
                hence False using \<open>t' \<in> r1.deadlocked s1\<close> by(rule r1.red_no_deadlock)
                thus ?thesis ..
              qed simp
              with \<open>\<not> final1 x1\<close> \<open>final1 x1'\<close> show False by simp
            qed
            thus ?thesis using \<open>ts2' t' = \<lfloor>(x2, ln)\<rfloor>\<close> join
              by(auto simp add: r2.not_final_thread_iff r1.final_thread_def)
          qed
        next
          case (interrupt t')
          have "r2.all_final_except ?s2 (r1.deadlocked s1 \<union> r2.deadlocked ?s2 \<union> r2.final_threads ?s2)"
          proof(rule r2.all_final_exceptI)
            fix t''
            assume "r2.not_final_thread ?s2 t''"
            then obtain x2 ln where "thr ?s2 t'' = \<lfloor>(x2, ln)\<rfloor>"
              and fin: "\<not> final2 x2 \<or> ln \<noteq> no_wait_locks \<or> wset ?s2 t'' \<noteq> None"
              by(auto simp add: r2.not_final_thread_iff)
            from \<open>thr ?s2 t'' = \<lfloor>(x2, ln)\<rfloor>\<close> mbisim
            obtain x1 where ts1t'': "thr s1 t'' = \<lfloor>(x1, ln)\<rfloor>" 
              and bisim'': "t'' \<turnstile> (x1, shr s1) \<approx> (x2, shr ?s2)"
              by(auto dest: mbisim_thrD2)
            have "r1.not_final_thread s1 t''"
            proof(cases "wset ?s2 t'' = None \<and> ln = no_wait_locks")
              case True
              with fin have "\<not> final2 x2" by simp
              hence "\<not> final1 x1"
              proof(rule contrapos_nn)
                assume "final1 x1"
                with final1_simulation[OF bisim'']
                obtain x2' m2' where \<tau>s2: "r2.silent_moves t'' (x2, shr ?s2) (x2', m2')"
                  and bisim''': "t'' \<turnstile> (x1, shr s1) \<approx> (x2', m2')"
                  and "final2 x2'" by auto
                from \<tau>s2 have "x2' = x2"
                proof(cases rule: converse_rtranclpE2[consumes 1, case_names refl step])
                  case refl thus ?thesis by simp
                next
                  case (step x2'' m2'')
                  from True have "wset s1 t'' = None" "thr s1 t'' = \<lfloor>(x1, no_wait_locks)\<rfloor>" "ts2' t'' = \<lfloor>(x2, no_wait_locks)\<rfloor>"
                    using ts1t'' \<open>thr ?s2 t'' = \<lfloor>(x2, ln)\<rfloor>\<close> mbisim by(simp_all add: mbisim_def)
                  hence no_\<tau>2: "\<not> r2.silent_move t'' (x2, m2) (x2'', m2'')"
                  proof(rule no_\<tau>)
                    fix x1' m1'
                    assume "r1.silent_move t'' (x1, shr s1) (x1', m1')"
                    with \<open>final1 x1\<close> show False by(auto dest: r1.final_no_red)
                  qed
                  with \<open>r2.silent_move t'' (x2, shr ?s2) (x2'', m2'')\<close> have False by simp
                  thus ?thesis ..
                qed
                with \<open>final2 x2'\<close> show "final2 x2" by simp
              qed
              with ts1t'' show ?thesis ..
            next
              case False
              with ts1t'' mbisim show ?thesis by(auto simp add: r1.not_final_thread_iff mbisim_def)
            qed
            with \<open>r1.all_final_except s1 (r1.deadlocked s1 \<union> r1.final_threads s1)\<close>
            have "t'' \<in> r1.deadlocked s1 \<union> r1.final_threads s1" by(rule r1.all_final_exceptD)
            thus "t'' \<in> r1.deadlocked s1 \<union> r2.deadlocked ?s2 \<union> r2.final_threads ?s2"
              by(auto dest: fin' simp add: mbisim_eqs)
          qed
          thus ?thesis using interrupt mbisim by(auto simp add: mbisim_def)
        qed
        hence "\<exists>lt\<in>LT. r2.must_wait ?s2 t lt (r1.deadlocked s1 \<union> r2.deadlocked ?s2 \<union> r2.final_threads ?s2)"
          using \<open>lt \<in> LT\<close> by blast }
      moreover from mbisim \<open>wset s1 t = None\<close> have "wset ?s2 t = None" by(simp add: mbisim_def)
      ultimately have ?Lock by simp
      thus ?thesis ..
    next
      case (wait x1 ln)
      from mbisim \<open>thr s1 t = \<lfloor>(x1, ln)\<rfloor>\<close>
      obtain x2 where "ts2' t = \<lfloor>(x2, ln)\<rfloor>" by(auto dest: mbisim_thrD1)
      moreover
      have "r2.all_final_except ?s2 (r1.deadlocked s1)"
      proof(rule r2.all_final_exceptI)
        fix t
        assume "r2.not_final_thread ?s2 t"
        then obtain x2 ln where "ts2' t = \<lfloor>(x2, ln)\<rfloor>" by(auto simp add: r2.not_final_thread_iff)
        with mbisim obtain x1 where "thr s1 t = \<lfloor>(x1, ln)\<rfloor>" "t \<turnstile> (x1, shr s1) \<approx> (x2, m2)" by(auto dest: mbisim_thrD2)
        hence "r1.not_final_thread s1 t" using \<open>r2.not_final_thread ?s2 t\<close> \<open>ts2' t = \<lfloor>(x2, ln)\<rfloor>\<close> mbisim fin'[of t]
          by(cases "wset s1 t")(auto simp add: r1.not_final_thread_iff r2.not_final_thread_iff mbisim_def r1.final_thread_def r2.final_thread_def)
        with \<open>r1.all_final_except s1 (r1.deadlocked s1)\<close>
        show "t \<in> r1.deadlocked s1" by(rule r1.all_final_exceptD)
      qed
      hence "r2.all_final_except ?s2 (r1.deadlocked s1 \<union> r2.deadlocked ?s2)"
        by(rule r2.all_final_except_mono') blast
      moreover
      from \<open>waiting (wset s1 t)\<close> mbisim
      have "waiting (wset ?s2 t)" by(simp add: mbisim_def)
      ultimately have ?Wait by simp
      thus ?thesis by blast
    next
      case (acquire x1 ln l t')
      from mbisim \<open>thr s1 t = \<lfloor>(x1, ln)\<rfloor>\<close>
      obtain x2 where "ts2' t = \<lfloor>(x2, ln)\<rfloor>" by(auto dest: mbisim_thrD1)
      moreover
      from \<open>t' \<in> r1.deadlocked s1 \<or> r1.final_thread s1 t'\<close>
      have "(t' \<in> r1.deadlocked s1 \<or> t' \<in> r2.deadlocked ?s2) \<or> r2.final_thread ?s2 t'" by(blast dest: fin')
      moreover
      from mbisim \<open>has_lock (locks s1 $ l) t'\<close>
      have "has_lock (locks ?s2 $ l) t'" by(simp add: mbisim_def)
      ultimately have ?Acquire
        using \<open>0 < ln $ l\<close> \<open>t \<noteq> t'\<close> \<open>\<not> waiting (wset s1 t)\<close> mbisim
        by(auto simp add: mbisim_def)
      thus ?thesis by blast
    qed
  qed
  with red1 red2 mbisim show ?thesis by(blast intro: rtranclp_trans)
qed

lemma deadlocked2_imp_\<tau>s_deadlocked1:
  "\<lbrakk> s1 \<approx>m s2; t \<in> r2.deadlocked s2 \<rbrakk>
  \<Longrightarrow> \<exists>s1'. r1.mthr.silent_moves s1 s1' \<and> t \<in> r1.deadlocked s1' \<and> s1' \<approx>m s2"
using FWdelay_bisimulation_diverge.deadlocked1_imp_\<tau>s_deadlocked2[OF FWdelay_bisimulation_diverge_flip]
unfolding flip_simps .

lemma deadlock1_imp_\<tau>s_deadlock2:
  assumes mbisim: "s1 \<approx>m s2"
  and dead: "r1.deadlock s1"
  shows "\<exists>s2'. r2.mthr.silent_moves s2 s2' \<and> r2.deadlock s2' \<and> s1 \<approx>m s2'"
proof(cases "\<exists>t. r1.not_final_thread s1 t")
  case True
  then obtain t where nfin: "r1.not_final_thread s1 t" ..
  from mfinal1_inv_simulation[OF mbisim]
  obtain ls2 ts2 m2 ws2 is2 where red1: "r2.mthr.silent_moves s2 (ls2, (ts2, m2), ws2, is2)"
    and "s1 \<approx>m (ls2, (ts2, m2), ws2, is2)" and "m2 = shr s2" 
    and fin: "\<And>t. r1.final_thread s1 t \<Longrightarrow> r2.final_thread (ls2, (ts2, m2), ws2, is2) t" by fastforce
  from no_\<tau>Move1_\<tau>s_to_no_\<tau>Move2[OF \<open>s1 \<approx>m (ls2, (ts2, m2), ws2, is2)\<close>]
  obtain ts2' where red2: "r2.mthr.silent_moves (ls2, (ts2, m2), ws2, is2) (ls2, (ts2', m2), ws2, is2)"
    and no_\<tau>: "\<And>t x1 x2 x2' m2'. \<lbrakk> wset s1 t = None; thr s1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>; ts2' t = \<lfloor>(x2, no_wait_locks)\<rfloor>;
                           \<And>x' m'. r1.silent_move t (x1, shr s1) (x', m') \<Longrightarrow> False \<rbrakk>
              \<Longrightarrow>  \<not> r2.silent_move t (x2, m2) (x2', m2')"
    and mbisim: "s1 \<approx>m (ls2, (ts2', m2), ws2, is2)" by fastforce
  from mbisim have mbisim_eqs: "ls2 = locks s1" "ws2 = wset s1" "is2 = interrupts s1"
    by(simp_all add: mbisim_def)
  let ?s2 = "(ls2, (ts2', m2), ws2, is2)"
  from red2 have fin': "\<And>t. r1.final_thread s1 t \<Longrightarrow> r2.final_thread ?s2 t"
    by(rule r2.\<tau>mRedT_preserves_final_thread)(rule fin)
  have "r2.deadlock ?s2"
  proof(rule r2.deadlockI, goal_cases)
    case (1 t x2)
    note ts2t = \<open>thr ?s2 t = \<lfloor>(x2, no_wait_locks)\<rfloor>\<close>
    with mbisim obtain x1 where ts1t: "thr s1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>"
      and bisim: "t \<turnstile> (x1, shr s1) \<approx> (x2, m2)" by(auto dest: mbisim_thrD2)
    from \<open>wset ?s2 t = None\<close> mbisim have ws1t: "wset s1 t = None" by(simp add: mbisim_def)
    have "\<not> final1 x1"
    proof
      assume "final1 x1"
      with ts1t ws1t have "r1.final_thread s1 t" by(simp add: r1.final_thread_def)
      hence "r2.final_thread ?s2 t" by(rule fin')
      with \<open>\<not> final2 x2\<close> ts2t \<open>wset ?s2 t = None\<close> show False by(simp add: r2.final_thread_def)
    qed
    from r1.deadlockD1[OF dead ts1t this \<open>wset s1 t = None\<close>]
    have ms: "r1.must_sync t x1 (shr s1)"
      and csmw: "\<And>LT. r1.can_sync t x1 (shr s1) LT \<Longrightarrow> \<exists>lt\<in>LT. r1.must_wait s1 t lt (dom (thr s1))"
      by blast+
    {
      from \<open>r1.must_sync t x1 (shr s1)\<close> obtain ta1 x1' m1'
        where r1: "t \<turnstile> (x1, shr s1) -1-ta1\<rightarrow> (x1', m1')"
        and s1': "\<exists>s1'. r1.actions_ok s1' t ta1" by(fastforce elim: r1.must_syncE)
      have "\<not> \<tau>move1 (x1, shr s1) ta1 (x1', m1')" (is "\<not> ?\<tau>")
      proof
        assume "?\<tau>"
        hence "ta1 = \<epsilon>" by(rule r1.silent_tl)
        with r1 have "r1.can_sync t x1 (shr s1) {}"
          by(auto intro!: r1.can_syncI simp add: collect_locks_def collect_interrupts_def)
        from csmw[OF this] show False by blast
      qed
      from simulation1[OF bisim r1 this]
      obtain x2' m2' x2'' m2'' ta2 where r2: "r2.silent_moves t (x2, m2) (x2', m2')"
        and r2': "t \<turnstile> (x2', m2') -2-ta2\<rightarrow>  (x2'', m2'')"
        and bisim': "t \<turnstile> (x1', m1') \<approx> (x2'', m2'')" and tasim: "ta1 \<sim>m ta2" by auto
      from r2
      have "\<exists>ta2 x2' m2' s2'. t \<turnstile> (x2, m2) -2-ta2\<rightarrow> (x2', m2') \<and> r2.actions_ok s2' t ta2"
      proof(cases rule: converse_rtranclpE2[consumes 1, case_names base step])
        case base
        from r2'[folded base] s1'[unfolded ex_actions_ok1_conv_ex_actions_ok2[OF tasim]]
        show ?thesis by blast
      next
        case (step x2''' m2''')
        hence "t \<turnstile> (x2, m2) -2-\<epsilon>\<rightarrow> (x2''', m2''')" by(auto dest: r2.silent_tl)
        moreover have "r2.actions_ok (undefined, (undefined, undefined), Map.empty, undefined) t \<epsilon>" by auto
        ultimately show ?thesis by-(rule exI conjI|assumption)+
      qed
      hence "r2.must_sync t x2 m2" unfolding r2.must_sync_def2 . }
    moreover
    { fix LT
      assume "r2.can_sync t x2 m2 LT"
      then obtain ta2 x2' m2' where r2: "t \<turnstile> (x2, m2) -2-ta2\<rightarrow> (x2', m2')"
        and LT: "LT = collect_locks \<lbrace>ta2\<rbrace>\<^bsub>l\<^esub> <+> collect_cond_actions \<lbrace>ta2\<rbrace>\<^bsub>c\<^esub> <+> collect_interrupts \<lbrace>ta2\<rbrace>\<^bsub>i\<^esub>"
        by(auto elim: r2.can_syncE)
      from ts2t have "ts2' t = \<lfloor>(x2, no_wait_locks)\<rfloor>" by simp
      with ws1t ts1t have "\<not> r2.silent_move t (x2, m2) (x2', m2')"
      proof(rule no_\<tau>)
        fix x1' m1'
        assume "r1.silent_move t (x1, shr s1) (x1', m1')"
        hence "t \<turnstile> (x1, shr s1) -1-\<epsilon>\<rightarrow> (x1', m1')" by(auto dest: r1.silent_tl)
        hence "r1.can_sync t x1 (shr s1) {}"
          by(auto intro: r1.can_syncI simp add: collect_locks_def collect_interrupts_def)
        with csmw[OF this] show False by blast
      qed
      with r2 have "\<not> \<tau>move2 (x2, m2) ta2 (x2', m2')" by auto
      from simulation2[OF bisim r2 this] obtain x1' m1' x1'' m1'' ta1
        where \<tau>r1: "r1.silent_moves t (x1, shr s1) (x1', m1')"
        and r1: "t \<turnstile> (x1', m1') -1-ta1\<rightarrow> (x1'', m1'')"
        and n\<tau>1: "\<not> \<tau>move1 (x1', m1') ta1 (x1'', m1'')"
        and bisim': "t \<turnstile> (x1'', m1'') \<approx> (x2', m2')"
        and tlsim: "ta1 \<sim>m ta2" by auto
      from \<tau>r1 obtain [simp]: "x1' = x1" "m1' = shr s1"
      proof(cases rule: converse_rtranclpE2[consumes 1, case_names refl step])
        case (step X M)
        from \<open>r1.silent_move t (x1, shr s1) (X, M)\<close>
        have "t \<turnstile> (x1, shr s1) -1-\<epsilon>\<rightarrow> (X, M)" by(auto dest: r1.silent_tl)
        hence "r1.can_sync t x1 (shr s1) {}"
          by(auto intro: r1.can_syncI simp add: collect_locks_def collect_interrupts_def)
        with csmw[OF this] have False by blast
        thus ?thesis ..
      qed blast
      from tlsim LT have "LT = collect_locks \<lbrace>ta1\<rbrace>\<^bsub>l\<^esub> <+> collect_cond_actions \<lbrace>ta1\<rbrace>\<^bsub>c\<^esub> <+> collect_interrupts \<lbrace>ta1\<rbrace>\<^bsub>i\<^esub>"
        by(auto simp add: ta_bisim_def)
      with r1 have "r1.can_sync t x1 (shr s1) LT" by(auto intro: r1.can_syncI)
      from csmw[OF this] obtain lt 
        where lt: "lt \<in> LT" "r1.must_wait s1 t lt (dom (thr s1))" by blast
      from \<open>r1.must_wait s1 t lt (dom (thr s1))\<close> have "r2.must_wait ?s2 t lt (dom (thr ?s2))"
      proof(cases rule: r1.must_wait_elims)
        case (lock l)
        with mbisim_dom_eq[OF mbisim] show ?thesis by(auto simp add: mbisim_eqs)
      next
        case (join t')
        from dead deadlock_mbisim_not_final_thread_pres[OF _ \<open>r1.not_final_thread s1 t'\<close> fin' mbisim]
        have "r2.not_final_thread ?s2 t'" by auto
        thus ?thesis using join mbisim_dom_eq[OF mbisim] by auto
      next
        case (interrupt t')
        have "r2.all_final_except ?s2 (dom (thr ?s2))" by(auto intro!: r2.all_final_exceptI)
        with interrupt show ?thesis by(auto simp add: mbisim_eqs)
      qed
      with lt have "\<exists>lt\<in>LT. r2.must_wait ?s2 t lt (dom (thr ?s2))" by blast }
    ultimately show ?case by fastforce
  next
    case (2 t x2 ln l)
    note dead moreover
    from mbisim \<open>thr ?s2 t = \<lfloor>(x2, ln)\<rfloor>\<close>
    obtain x1 where "thr s1 t = \<lfloor>(x1, ln)\<rfloor>" by(auto dest: mbisim_thrD2)
    moreover note \<open>0 < ln $ l\<close>
    moreover from \<open>\<not> waiting (wset ?s2 t)\<close> mbisim
    have "\<not> waiting (wset s1 t)" by(simp add: mbisim_def)
    ultimately obtain l' t' where "0 < ln $ l'" "t \<noteq> t'" "thr s1 t' \<noteq> None" "has_lock (locks s1 $ l') t'"
      by(rule r1.deadlockD2)
    thus ?case using mbisim_thrNone_eq[OF mbisim, of t'] mbisim by(auto simp add: mbisim_def)
  next
    case (3 t x2 w)
    from mbisim_thrD2[OF mbisim this]
    obtain x1 where "thr s1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>" by auto
    with dead have "wset s1 t \<noteq> \<lfloor>PostWS w\<rfloor>" by(rule r1.deadlockD3[rule_format])
    with mbisim show ?case by(simp add: mbisim_def)
  qed
  with red1 red2 mbisim show ?thesis by(blast intro: rtranclp_trans)
next
  case False
  hence "r1.mfinal s1" by(auto intro: r1.mfinalI simp add: r1.not_final_thread_iff)
  from mfinal1_simulation[OF mbisim this]
  obtain s2' where "\<tau>mRed2 s2 s2'" "s1 \<approx>m s2'" "r2.mfinal s2'" "shr s2' = shr s2" by blast
  thus ?thesis by(blast intro: r2.mfinal_deadlock)
qed

lemma deadlock2_imp_\<tau>s_deadlock1:
  "\<lbrakk> s1 \<approx>m s2; r2.deadlock s2 \<rbrakk>
  \<Longrightarrow> \<exists>s1'. r1.mthr.silent_moves s1 s1' \<and> r1.deadlock s1' \<and> s1' \<approx>m s2"
using FWdelay_bisimulation_diverge.deadlock1_imp_\<tau>s_deadlock2[OF FWdelay_bisimulation_diverge_flip]
unfolding flip_simps .

lemma deadlocked'1_imp_\<tau>s_deadlocked'2:
  "\<lbrakk> s1 \<approx>m s2; r1.deadlocked' s1 \<rbrakk>
  \<Longrightarrow> \<exists>s2'. r2.mthr.silent_moves s2 s2' \<and> r2.deadlocked' s2' \<and> s1 \<approx>m s2'"
unfolding r1.deadlock_eq_deadlocked'[symmetric] r2.deadlock_eq_deadlocked'[symmetric]
by(rule deadlock1_imp_\<tau>s_deadlock2)

lemma deadlocked'2_imp_\<tau>s_deadlocked'1:
  "\<lbrakk> s1 \<approx>m s2; r2.deadlocked' s2 \<rbrakk> \<Longrightarrow> \<exists>s1'. r1.mthr.silent_moves s1 s1' \<and> r1.deadlocked' s1' \<and> s1' \<approx>m s2"
unfolding r1.deadlock_eq_deadlocked'[symmetric] r2.deadlock_eq_deadlocked'[symmetric]
by(rule deadlock2_imp_\<tau>s_deadlock1)

end

context FWbisimulation begin

lemma mbisim_final_thread_preserve1:
  assumes mbisim: "s1 \<approx>m s2" and fin: "r1.final_thread s1 t"
  shows "r2.final_thread s2 t"
proof -
  from fin obtain x1 where ts1t: "thr s1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>"
    and fin1: "final1 x1" and ws1t: "wset s1 t = None"
    by(auto elim: r1.final_threadE)
  from mbisim ts1t obtain x2 
    where ts2t: "thr s2 t = \<lfloor>(x2, no_wait_locks)\<rfloor>"
    and bisim: "t \<turnstile> (x1, shr s1) \<approx> (x2, shr s2)" by(auto dest: mbisim_thrD1)
  note ts2t moreover from fin1 bisim have "final2 x2" by(auto dest: bisim_final)
  moreover from mbisim ws1t have "wset s2 t = None" by(simp add: mbisim_def)
  ultimately show ?thesis by(rule r2.final_threadI)
qed

lemma mbisim_final_thread_preserve2:
  "\<lbrakk> s1 \<approx>m s2; r2.final_thread s2 t \<rbrakk> \<Longrightarrow> r1.final_thread s1 t"
using FWbisimulation.mbisim_final_thread_preserve1[OF FWbisimulation_flip]
unfolding flip_simps .

lemma mbisim_final_thread_inv:
  "s1 \<approx>m s2 \<Longrightarrow> r1.final_thread s1 t \<longleftrightarrow> r2.final_thread s2 t"
by(blast intro: mbisim_final_thread_preserve1 mbisim_final_thread_preserve2)

lemma mbisim_not_final_thread_inv:
  assumes bisim: "mbisim s1 s2"
  shows "r1.not_final_thread s1 = r2.not_final_thread s2"
proof(rule ext)
  fix t
  show "r1.not_final_thread s1 t = r2.not_final_thread s2 t"
  proof(cases "thr s1 t")
    case None
    with mbisim_thrNone_eq[OF bisim, of t] have "thr s2 t = None" by simp
    with None show ?thesis
      by(auto elim!: r2.not_final_thread.cases r1.not_final_thread.cases
             intro: r2.not_final_thread.intros r1.not_final_thread.intros)
  next
    case (Some a)
    then obtain x1 ln where tst1: "thr s1 t = \<lfloor>(x1, ln)\<rfloor>" by(cases a) auto
    from mbisim_thrD1[OF bisim tst1] obtain x2
      where tst2: "thr s2 t = \<lfloor>(x2, ln)\<rfloor>" and bisimt: "t \<turnstile> (x1, shr s1) \<approx> (x2, shr s2)" by blast
    from bisim have "wset s2 = wset s1" by(simp add: mbisim_def)
    with tst2 tst1 bisim_final[OF bisimt] show ?thesis
      by(simp add: r1.not_final_thread_conv r2.not_final_thread_conv)(rule mbisim_final_thread_inv[OF bisim])
  qed
qed

lemma mbisim_deadlocked_preserve1:
  assumes mbisim: "s1 \<approx>m s2" and dead: "t \<in> r1.deadlocked s1"
  shows "t \<in> r2.deadlocked s2"
proof -
  from deadlocked1_imp_\<tau>s_deadlocked2[OF mbisim dead]
  obtain s2' where "r2.mthr.silent_moves s2 s2'"
    and "t \<in> r2.deadlocked s2'" by blast
  from \<open>r2.mthr.silent_moves s2 s2'\<close> have "s2' = s2"
    by(rule converse_rtranclpE)(auto elim: r2.m\<tau>move.cases)
  with \<open>t \<in> r2.deadlocked s2'\<close> show ?thesis by simp
qed

lemma mbisim_deadlocked_preserve2:
  "\<lbrakk> s1 \<approx>m s2; t \<in> r2.deadlocked s2 \<rbrakk> \<Longrightarrow> t \<in> r1.deadlocked s1"
using FWbisimulation.mbisim_deadlocked_preserve1[OF FWbisimulation_flip]
unfolding flip_simps .

lemma mbisim_deadlocked_inv:
  "s1 \<approx>m s2 \<Longrightarrow> r1.deadlocked s1 = r2.deadlocked s2"
by(blast intro!: mbisim_deadlocked_preserve1 mbisim_deadlocked_preserve2)

lemma mbisim_deadlocked'_inv:
  "s1 \<approx>m s2 \<Longrightarrow> r1.deadlocked' s1 \<longleftrightarrow> r2.deadlocked' s2"
unfolding r1.deadlocked'_def r2.deadlocked'_def
by(simp add: mbisim_not_final_thread_inv mbisim_deadlocked_inv)

lemma mbisim_deadlock_inv:
  "s1 \<approx>m s2 \<Longrightarrow> r1.deadlock s1 = r2.deadlock s2"
unfolding r1.deadlock_eq_deadlocked' r2.deadlock_eq_deadlocked'
by(rule mbisim_deadlocked'_inv)

end

(* Nice to have, but not needed any more *)

context FWbisimulation begin

lemma bisim_can_sync_preserve1:
  assumes bisim: "t \<turnstile> (x1, m1) \<approx> (x2, m2)" and cs: "t \<turnstile> \<langle>x1, m1\<rangle> LT \<wrong>1"
  shows "t \<turnstile> \<langle>x2, m2\<rangle> LT \<wrong>2"
proof -
  from cs obtain ta1 x1' m1' where red1: "t \<turnstile> (x1, m1) -1-ta1\<rightarrow> (x1', m1')"
    and LT: "LT = collect_locks \<lbrace>ta1\<rbrace>\<^bsub>l\<^esub> <+> collect_cond_actions \<lbrace>ta1\<rbrace>\<^bsub>c\<^esub> <+> collect_interrupts \<lbrace>ta1\<rbrace>\<^bsub>i\<^esub>" by(rule r1.can_syncE)
  from bisimulation.simulation1[OF bisimulation_axioms, OF bisim red1] obtain x2' ta2 m2'
    where red2: "t \<turnstile> (x2, m2) -2-ta2\<rightarrow> (x2', m2')" 
    and tasim: "ta1 \<sim>m ta2" by fastforce
  from tasim LT have "LT = collect_locks \<lbrace>ta2\<rbrace>\<^bsub>l\<^esub> <+> collect_cond_actions \<lbrace>ta2\<rbrace>\<^bsub>c\<^esub> <+> collect_interrupts \<lbrace>ta2\<rbrace>\<^bsub>i\<^esub>"
    by(auto simp add: ta_bisim_def)
  with red2 show ?thesis by(rule r2.can_syncI)
qed

lemma bisim_can_sync_preserve2:
  "\<lbrakk> t \<turnstile> (x1, m1) \<approx> (x2, m2); t \<turnstile> \<langle>x2, m2\<rangle> LT \<wrong>2 \<rbrakk> \<Longrightarrow> t \<turnstile> \<langle>x1, m1\<rangle> LT \<wrong>1"
using FWbisimulation.bisim_can_sync_preserve1[OF FWbisimulation_flip]
unfolding flip_simps .

lemma bisim_can_sync_inv:
  "t \<turnstile> (x1, m1) \<approx> (x2, m2) \<Longrightarrow> t \<turnstile> \<langle>x1, m1\<rangle> LT \<wrong>1 \<longleftrightarrow> t \<turnstile> \<langle>x2, m2\<rangle> LT \<wrong>2"
by(blast intro: bisim_can_sync_preserve1 bisim_can_sync_preserve2)

lemma bisim_must_sync_preserve1:
  assumes bisim: "t \<turnstile> (x1, m1) \<approx> (x2, m2)" and ms: "t \<turnstile> \<langle>x1, m1\<rangle> \<wrong>1"
  shows "t \<turnstile> \<langle>x2, m2\<rangle> \<wrong>2"
proof -
  from ms obtain ta1 x1' m1' where red1: "t \<turnstile> (x1, m1) -1-ta1\<rightarrow> (x1', m1')"
    and s1': "\<exists>s1'. r1.actions_ok s1' t ta1" by(fastforce elim: r1.must_syncE)
  from bisimulation.simulation1[OF bisimulation_axioms, OF bisim red1] obtain x2' ta2 m2'
    where red2: "t \<turnstile> (x2, m2) -2-ta2\<rightarrow> (x2', m2')" 
    and tasim: "ta1 \<sim>m ta2" by fastforce
  from ex_actions_ok1_conv_ex_actions_ok2[OF tasim, of t] s1' red2
  show ?thesis unfolding r2.must_sync_def2 by blast
qed

lemma bisim_must_sync_preserve2:
  "\<lbrakk> t \<turnstile> (x1, m1) \<approx> (x2, m2); t \<turnstile> \<langle>x2, m2\<rangle> \<wrong>2 \<rbrakk> \<Longrightarrow> t \<turnstile> \<langle>x1, m1\<rangle> \<wrong>1"
using FWbisimulation.bisim_must_sync_preserve1[OF FWbisimulation_flip]
unfolding flip_simps .

lemma bisim_must_sync_inv:
  "t \<turnstile> (x1, m1) \<approx> (x2, m2) \<Longrightarrow> t \<turnstile> \<langle>x1, m1\<rangle> \<wrong>1 \<longleftrightarrow> t \<turnstile> \<langle>x2, m2\<rangle> \<wrong>2"
by(blast intro: bisim_must_sync_preserve1 bisim_must_sync_preserve2)

end

end
