theory FWBisimLift imports
  FWInitFinLift
  FWBisimulation
begin

context FWbisimulation_base begin

inductive init_fin_bisim :: "'t \<Rightarrow> ((status \<times> 'x1) \<times> 'm1, (status \<times> 'x2) \<times> 'm2) bisim"
  ("_ \<turnstile> _ \<approx>i _"[50,50,50] 60)
for t :: 't
where
  PreStart: "t \<turnstile> (x1, m1) \<approx> (x2, m2) \<Longrightarrow> t \<turnstile> ((PreStart, x1), m1) \<approx>i ((PreStart, x2), m2)"
| Running: "t \<turnstile> (x1, m1) \<approx> (x2, m2) \<Longrightarrow> t \<turnstile> ((Running, x1), m1) \<approx>i ((Running, x2), m2)"
| Finished: 
    "\<lbrakk> t \<turnstile> (x1, m1) \<approx> (x2, m2); final1 x1; final2 x2 \<rbrakk>
    \<Longrightarrow> t \<turnstile> ((Finished, x1), m1) \<approx>i ((Finished, x2), m2)"

definition init_fin_bisim_wait :: "(status \<times> 'x1, status \<times> 'x2) bisim" ("_ \<approx>iw _" [50,50] 60)
where 
  "init_fin_bisim_wait = (\<lambda>(status1, x1) (status2, x2). status1 = Running \<and> status2 = Running \<and> x1 \<approx>w x2)"

inductive_simps init_fin_bisim_simps [simp]:
  "t \<turnstile> ((PreStart, x1), m1) \<approx>i ((s2, x2), m2)"
  "t \<turnstile> ((Running, x1), m1) \<approx>i ((s2, x2), m2)"
  "t \<turnstile> ((Finished, x1), m1) \<approx>i ((s2, x2), m2)"
  "t \<turnstile> ((s1, x1), m1) \<approx>i ((PreStart, x2), m2)"
  "t \<turnstile> ((s1, x1), m1) \<approx>i ((Running, x2), m2)"
  "t \<turnstile> ((s1, x1), m1) \<approx>i ((Finished, x2), m2)"

lemma init_fin_bisim_iff:
  "t \<turnstile> ((s1, x1), m1) \<approx>i ((s2, x2), m2) \<longleftrightarrow> 
   s1 = s2 \<and> t \<turnstile> (x1, m1) \<approx> (x2, m2) \<and> (s2 = Finished \<longrightarrow> final1 x1 \<and> final2 x2)"
by(cases s1) auto

lemma nta_bisim_init_fin_bisim [simp]:
  "nta_bisim init_fin_bisim (convert_new_thread_action (Pair PreStart) nt1)
      (convert_new_thread_action (Pair PreStart) nt2) =
   nta_bisim bisim nt1 nt2"
by(cases nt1) simp_all

lemma ta_bisim_init_fin_bisim_convert [simp]:
  "ta_bisim init_fin_bisim (convert_TA_initial (convert_obs_initial ta1)) (convert_TA_initial (convert_obs_initial ta2)) \<longleftrightarrow> ta1 \<sim>m ta2"
by(auto simp add: ta_bisim_def list_all2_map1 list_all2_map2)

lemma ta_bisim_init_fin_bisim_InitialThreadAction [simp]:
  "ta_bisim init_fin_bisim \<lbrace>InitialThreadAction\<rbrace> \<lbrace>InitialThreadAction\<rbrace>"
by(simp add: ta_bisim_def)

lemma ta_bisim_init_fin_bisim_ThreadFinishAction [simp]:
  "ta_bisim init_fin_bisim \<lbrace>ThreadFinishAction\<rbrace> \<lbrace>ThreadFinishAction\<rbrace>"
by(simp add: ta_bisim_def)

lemma init_fin_bisim_wait_simps [simp]:
  "(status1, x1) \<approx>iw (status2, x2) \<longleftrightarrow> status1 = Running \<and> status2 = Running \<and> x1 \<approx>w x2"
by(simp add: init_fin_bisim_wait_def)

lemma init_fin_lift_state_mbisimI:
  "s \<approx>m s' \<Longrightarrow>
  FWbisimulation_base.mbisim init_fin_bisim init_fin_bisim_wait (init_fin_lift_state Running s) (init_fin_lift_state Running s')"
apply(rule FWbisimulation_base.mbisimI)
      apply(simp add: thr_init_fin_list_state' o_def dom_map_option mbisim_finite1)
     apply(simp add: locks_init_fin_lift_state mbisim_def)
    apply(simp add: wset_init_fin_lift_state mbisim_def)
   apply(simp add: interrupts_init_fin_lift_stae mbisim_def)
  apply(clarsimp simp add: wset_init_fin_lift_state mbisim_def thr_init_fin_list_state' o_def wset_thread_ok_conv_dom dom_map_option del: subsetI)
 apply(drule_tac t=t in mbisim_thrNone_eq)
 apply(simp add: thr_init_fin_list_state)
apply(clarsimp simp add: thr_init_fin_list_state shr_init_fin_lift_state wset_init_fin_lift_state init_fin_bisim_iff)
apply(frule (1) mbisim_thrD1)
apply(simp add: mbisim_def)
done

end

context FWdelay_bisimulation_base begin

lemma init_fin_delay_bisimulation_final_base:
  "delay_bisimulation_final_base (r1.init_fin t) (r2.init_fin t) (init_fin_bisim t) 
     r1.init_fin_\<tau>move r2.init_fin_\<tau>move (\<lambda>(x1, m). r1.init_fin_final x1) (\<lambda>(x2, m). r2.init_fin_final x2)"
by(unfold_locales)(auto 4 3)

end

lemma init_fin_bisim_flip [flip_simps]:
  "FWbisimulation_base.init_fin_bisim final2 final1 (\<lambda>t. flip (bisim t)) =
   (\<lambda>t. flip (FWbisimulation_base.init_fin_bisim final1 final2 bisim t))"
by(auto simp only: FWbisimulation_base.init_fin_bisim_iff flip_simps fun_eq_iff split_paired_Ex)

lemma init_fin_bisim_wait_flip [flip_simps]:
  "FWbisimulation_base.init_fin_bisim_wait (flip bisim_wait) =
   flip (FWbisimulation_base.init_fin_bisim_wait bisim_wait)"
by(auto simp add: fun_eq_iff FWbisimulation_base.init_fin_bisim_wait_simps flip_simps)

context FWdelay_bisimulation_lift_aux begin

lemma init_fin_FWdelay_bisimulation_lift_aux:
  "FWdelay_bisimulation_lift_aux r1.init_fin_final r1.init_fin r2.init_fin_final r2.init_fin r1.init_fin_\<tau>move r2.init_fin_\<tau>move"
by(intro FWdelay_bisimulation_lift_aux.intro r1.\<tau>multithreaded_wf_init_fin r2.\<tau>multithreaded_wf_init_fin)

lemma init_fin_FWdelay_bisimulation_final_base:
  "FWdelay_bisimulation_final_base 
     r1.init_fin_final r1.init_fin r2.init_fin_final r2.init_fin 
     init_fin_bisim r1.init_fin_\<tau>move r2.init_fin_\<tau>move"
by(intro FWdelay_bisimulation_final_base.intro init_fin_FWdelay_bisimulation_lift_aux FWdelay_bisimulation_final_base_axioms.intro init_fin_delay_bisimulation_final_base)

end

context FWdelay_bisimulation_obs begin

lemma init_fin_simulation1:
  assumes bisim: "t \<turnstile> s1 \<approx>i s2"
    and red1: "r1.init_fin t s1 tl1 s1'"
    and \<tau>1: "\<not> r1.init_fin_\<tau>move s1 tl1 s1'"
  shows "\<exists>s2' s2'' tl2. (\<tau>trsys.silent_move (r2.init_fin t) r2.init_fin_\<tau>move)\<^sup>*\<^sup>* s2 s2' \<and>
             r2.init_fin t s2' tl2 s2'' \<and> \<not> r2.init_fin_\<tau>move s2' tl2 s2'' \<and>
             t \<turnstile> s1' \<approx>i s2'' \<and> ta_bisim init_fin_bisim tl1 tl2"
proof -
  from bisim obtain status x1 m1 x2 m2 
    where s1: "s1 = ((status, x1), m1)"
    and s2: "s2 = ((status, x2), m2)"
    and bisim: "t \<turnstile> (x1, m1) \<approx> (x2, m2)"
    and finished: "status = Finished \<Longrightarrow> final1 x1 \<and> final2 x2"
    by(cases s1)(cases s2, fastforce simp add: init_fin_bisim_iff)
  from red1 show ?thesis unfolding s1
  proof(cases)
    case (NormalAction ta1 x1' m1')
    with \<tau>1 s1 have "\<not> \<tau>move1 (x1, m1) ta1 (x1', m1')" by(simp)
    from simulation1[OF bisim \<open>t \<turnstile> (x1, m1) -1-ta1\<rightarrow> (x1', m1')\<close> this]
    obtain x2' m2' x2'' m2'' ta2
      where red2: "r2.silent_moves t (x2, m2) (x2', m2')"
      and red2': "t \<turnstile> (x2', m2') -2-ta2\<rightarrow> (x2'', m2'')"
      and \<tau>2: "\<not> \<tau>move2 (x2', m2') ta2 (x2'', m2'')"
      and bisim': "t \<turnstile> (x1', m1') \<approx> (x2'', m2'')"
      and tasim: "ta1 \<sim>m ta2" by auto
    let ?s2' = "((Running, x2'), m2')"
    let ?s2'' = "((Running, x2''), m2'')"
    let ?ta2 = "(convert_TA_initial (convert_obs_initial ta2))"
    from red2 have "\<tau>trsys.silent_moves (r2.init_fin t) r2.init_fin_\<tau>move s2 ?s2'"
      unfolding s2 \<open>status = Running\<close> by(rule r2.init_fin_silent_moves_RunningI)
    moreover from red2' have "r2.init_fin t ?s2' ?ta2 ?s2''" by(rule r2.init_fin.NormalAction)
    moreover from \<tau>2 have "\<not> r2.init_fin_\<tau>move ?s2' ?ta2 ?s2''" by simp
    moreover from bisim' have "t \<turnstile> s1' \<approx>i ?s2''"using \<open>s1' = ((Running, x1'), m1')\<close> by simp
    moreover from tasim \<open>tl1 = convert_TA_initial (convert_obs_initial ta1)\<close>
    have "ta_bisim init_fin_bisim tl1 ?ta2" by simp
    ultimately show ?thesis by blast
  next
    case InitialThreadAction
    with s1 s2 bisim show ?thesis by(auto simp del: split_paired_Ex)
  next
    case ThreadFinishAction
    from final1_simulation[OF bisim] \<open>final1 x1\<close>
    obtain x2' m2' where red2: "r2.silent_moves t (x2, m2) (x2', m2')"
      and bisim': "t \<turnstile> (x1, m1) \<approx> (x2', m2')"
      and fin2: "final2 x2'" by auto
    let ?s2' = "((Running, x2'), m2')"
    let ?s2'' = "((Finished, x2'), m2')"
    from red2 have "\<tau>trsys.silent_moves (r2.init_fin t) r2.init_fin_\<tau>move s2 ?s2'"
      unfolding s2 \<open>status = Running\<close> by(rule r2.init_fin_silent_moves_RunningI)
    moreover from fin2 have "r2.init_fin t ?s2' \<lbrace>ThreadFinishAction\<rbrace> ?s2''" ..
    moreover have "\<not> r2.init_fin_\<tau>move ?s2' \<lbrace>ThreadFinishAction\<rbrace> ?s2''" by simp
    moreover have "t \<turnstile> s1' \<approx>i ?s2''"
      using \<open>s1' = ((Finished, x1), m1)\<close> fin2 \<open>final1 x1\<close> bisim' by simp
    ultimately show ?thesis unfolding \<open>tl1 = \<lbrace>ThreadFinishAction\<rbrace>\<close>
      by(blast intro: ta_bisim_init_fin_bisim_ThreadFinishAction)
  qed
qed

lemma init_fin_simulation2:
  "\<lbrakk> t \<turnstile> s1 \<approx>i s2; r2.init_fin t s2 tl2 s2'; \<not> r2.init_fin_\<tau>move s2 tl2 s2' \<rbrakk>
  \<Longrightarrow> \<exists>s1' s1'' tl1. (\<tau>trsys.silent_move (r1.init_fin t) r1.init_fin_\<tau>move)\<^sup>*\<^sup>* s1 s1' \<and>
             r1.init_fin t s1' tl1 s1'' \<and> \<not> r1.init_fin_\<tau>move s1' tl1 s1'' \<and>
             t \<turnstile> s1'' \<approx>i s2' \<and> ta_bisim init_fin_bisim tl1 tl2"
using FWdelay_bisimulation_obs.init_fin_simulation1[OF FWdelay_bisimulation_obs_flip]
unfolding flip_simps .

lemma init_fin_simulation_Wakeup1:
  assumes bisim: "t \<turnstile> (sx1, m1) \<approx>i (sx2, m2)"
  and wait: "sx1 \<approx>iw sx2"
  and red1: "r1.init_fin t (sx1, m1) ta1 (sx1', m1')"
  and wakeup: "Notified \<in> set \<lbrace>ta1\<rbrace>\<^bsub>w\<^esub> \<or> WokenUp \<in> set \<lbrace>ta1\<rbrace>\<^bsub>w\<^esub>"
  shows "\<exists>ta2 sx2' m2'. r2.init_fin t (sx2, m2) ta2 (sx2', m2') \<and> t \<turnstile> (sx1', m1') \<approx>i (sx2', m2') \<and> 
                        ta_bisim init_fin_bisim ta1 ta2"
proof -
  from bisim wait obtain status x1 x2 
    where sx1: "sx1 = (status, x1)"
    and sx2: "sx2 = (status, x2)"
    and Bisim: "t \<turnstile> (x1, m1) \<approx> (x2, m2)"
    and Wait: "x1 \<approx>w x2" by cases auto
  from red1 wakeup sx1 obtain x1' ta1' 
    where sx1': "sx1' = (Running, x1')"
    and status: "status = Running"
    and Red1: "t \<turnstile> (x1, m1) -1-ta1'\<rightarrow> (x1', m1')"
    and ta1: "ta1 = convert_TA_initial (convert_obs_initial ta1')"
    and Wakeup: "Notified \<in> set \<lbrace>ta1'\<rbrace>\<^bsub>w\<^esub> \<or> WokenUp \<in> set \<lbrace>ta1'\<rbrace>\<^bsub>w\<^esub>"
    by cases auto
  from simulation_Wakeup1[OF Bisim Wait Red1 Wakeup] obtain ta2' x2' m2'
    where red2: "t \<turnstile> (x2, m2) -2-ta2'\<rightarrow> (x2', m2')"
    and bisim': "t \<turnstile> (x1', m1') \<approx> (x2', m2')" 
    and tasim: "ta1' \<sim>m ta2'" by blast
  let ?sx2' = "(Running, x2')"
  let ?ta2 = "convert_TA_initial (convert_obs_initial ta2')"
  from red2 have "r2.init_fin t (sx2, m2) ?ta2 (?sx2', m2')" unfolding sx2 status ..
  moreover from bisim' sx1' have "t \<turnstile> (sx1', m1') \<approx>i (?sx2', m2')" by simp
  moreover from tasim ta1 have "ta_bisim init_fin_bisim ta1 ?ta2" by simp
  ultimately show ?thesis by blast
qed

lemma init_fin_simulation_Wakeup2:
  "\<lbrakk> t \<turnstile> (sx1, m1) \<approx>i (sx2, m2); sx1 \<approx>iw sx2; r2.init_fin t (sx2, m2) ta2 (sx2', m2');
    Notified \<in> set \<lbrace>ta2\<rbrace>\<^bsub>w\<^esub> \<or> WokenUp \<in> set \<lbrace>ta2\<rbrace>\<^bsub>w\<^esub> \<rbrakk>
  \<Longrightarrow> \<exists>ta1 sx1' m1'. r1.init_fin t (sx1, m1) ta1 (sx1', m1') \<and> t \<turnstile> (sx1', m1') \<approx>i (sx2', m2') \<and> 
                     ta_bisim init_fin_bisim ta1 ta2"
using FWdelay_bisimulation_obs.init_fin_simulation_Wakeup1[OF FWdelay_bisimulation_obs_flip]
unfolding flip_simps .

lemma init_fin_delay_bisimulation_obs:
  "delay_bisimulation_obs (r1.init_fin t) (r2.init_fin t) (init_fin_bisim t) (ta_bisim init_fin_bisim)
         r1.init_fin_\<tau>move r2.init_fin_\<tau>move"
by(unfold_locales)(erule (2) init_fin_simulation1 init_fin_simulation2)+

lemma init_fin_FWdelay_bisimulation_obs:
  "FWdelay_bisimulation_obs r1.init_fin_final r1.init_fin r2.init_fin_final r2.init_fin init_fin_bisim init_fin_bisim_wait r1.init_fin_\<tau>move r2.init_fin_\<tau>move"
proof(intro FWdelay_bisimulation_obs.intro init_fin_FWdelay_bisimulation_final_base FWdelay_bisimulation_obs_axioms.intro init_fin_delay_bisimulation_obs)
  fix t' sx m1 sxx m2 t sx1 sx2 sx1' ta1 sx1'' m1' sx2' ta2 sx2'' m2'
  assume bisim: "t' \<turnstile> (sx, m1) \<approx>i (sxx, m2)" 
    and bisim1: "t \<turnstile> (sx1, m1) \<approx>i (sx2, m2)"
    and red1: "\<tau>trsys.silent_moves (r1.init_fin t) r1.init_fin_\<tau>move (sx1, m1) (sx1', m1)"
    and red1': "r1.init_fin t (sx1', m1) ta1 (sx1'', m1')"
    and \<tau>1: "\<not> r1.init_fin_\<tau>move (sx1', m1) ta1 (sx1'', m1')"
    and red2: "\<tau>trsys.silent_moves (r2.init_fin t) r2.init_fin_\<tau>move (sx2, m2) (sx2', m2)"
    and red2':"r2.init_fin t (sx2', m2) ta2 (sx2'', m2')"
    and \<tau>2: "\<not> r2.init_fin_\<tau>move (sx2', m2) ta2 (sx2'', m2')"
    and bisim1': "t \<turnstile> (sx1'', m1') \<approx>i (sx2'', m2')"
    and tasim: "ta_bisim init_fin_bisim ta1 ta2"
  from bisim obtain status x xx 
    where sx:"sx = (status, x)"
    and sxx: "sxx = (status, xx)"
    and Bisim: "t' \<turnstile> (x, m1) \<approx> (xx, m2)"
    and Finish: "status = Finished \<Longrightarrow> final1 x \<and> final2 xx"
    by(cases sx)(cases sxx, auto simp add: init_fin_bisim_iff)
  from bisim1 obtain status1 x1 x2
    where sx1: "sx1 = (status1, x1)"
    and sx2: "sx2 = (status1, x2)"
    and Bisim1: "t \<turnstile> (x1, m1) \<approx> (x2, m2)"
    by(cases sx1)(cases sx2, auto simp add: init_fin_bisim_iff)
  from bisim1' obtain status1' x1'' x2''
    where sx1'': "sx1'' = (status1', x1'')"
    and sx2'': "sx2'' = (status1', x2'')"
    and Bisim1': "t \<turnstile> (x1'', m1') \<approx> (x2'', m2')"
     by(cases sx1'')(cases sx2'', auto simp add: init_fin_bisim_iff)
  from red1 sx1 obtain x1' where sx1': "sx1' = (status1, x1')"
    and Red1: "r1.silent_moves t (x1, m1) (x1', m1)"
    by(cases sx1')(auto dest: r1.init_fin_silent_movesD)
  from red2 sx2 obtain x2' where sx2': "sx2' = (status1, x2')"
    and Red2: "r2.silent_moves t (x2, m2) (x2', m2)"
    by(cases sx2')(auto dest: r2.init_fin_silent_movesD)
  show "t' \<turnstile> (sx, m1') \<approx>i (sxx, m2')"
  proof(cases "status1 = Running \<and> status1' = Running")
    case True
    with red1' sx1' sx1'' obtain ta1'
      where Red1': "t \<turnstile> (x1', m1) -1-ta1'\<rightarrow> (x1'', m1')"
      and ta1: "ta1 = convert_TA_initial (convert_obs_initial ta1')"
      by cases auto
    from red2' sx2' sx2'' True obtain ta2'
      where Red2': "t \<turnstile> (x2', m2) -2-ta2'\<rightarrow> (x2'', m2')"
      and ta2: "ta2 = convert_TA_initial (convert_obs_initial ta2')"
      by cases auto
    from \<tau>1 sx1' sx1'' ta1 True have \<tau>1':"\<not> \<tau>move1 (x1', m1) ta1' (x1'', m1')" by simp
    from \<tau>2 sx2' sx2'' ta2 True have \<tau>2':"\<not> \<tau>move2 (x2', m2) ta2' (x2'', m2')" by simp
    from tasim ta1 ta2 have "ta1' \<sim>m ta2'" by simp
    with Bisim Bisim1 Red1 Red1' \<tau>1' Red2 Red2' \<tau>2' Bisim1'
    have "t' \<turnstile> (x, m1') \<approx> (xx, m2')" by(rule bisim_inv_red_other)
    with True Finish show ?thesis unfolding sx sxx by(simp add: init_fin_bisim_iff)
  next
    case False
    with red1' sx1' sx1'' have "m1' = m1" by cases auto
    moreover from red2' sx2' sx2'' False have "m2' = m2" by cases auto
    ultimately show ?thesis using bisim by simp
  qed
next
  fix t sx1 m1 sx2 m2 sx1' ta1 sx1'' m1' sx2' ta2 sx2'' m2' w
  assume bisim: "t \<turnstile> (sx1, m1) \<approx>i (sx2, m2)"
    and red1: "\<tau>trsys.silent_moves (r1.init_fin t) r1.init_fin_\<tau>move (sx1, m1) (sx1', m1)"
    and red1': "r1.init_fin t (sx1', m1) ta1 (sx1'', m1')"
    and \<tau>1: "\<not> r1.init_fin_\<tau>move (sx1', m1) ta1 (sx1'', m1')"
    and red2: "\<tau>trsys.silent_moves (r2.init_fin t) r2.init_fin_\<tau>move (sx2, m2) (sx2', m2)"
    and red2': "r2.init_fin t (sx2', m2) ta2 (sx2'', m2')"
    and \<tau>2: "\<not> r2.init_fin_\<tau>move (sx2', m2) ta2 (sx2'', m2')"
    and bisim': "t \<turnstile> (sx1'', m1') \<approx>i (sx2'', m2')"
    and tasim: "ta_bisim init_fin_bisim ta1 ta2"
    and suspend1: "Suspend w \<in> set \<lbrace>ta1\<rbrace>\<^bsub>w\<^esub>"
    and suspend2: "Suspend w \<in> set \<lbrace>ta2\<rbrace>\<^bsub>w\<^esub>"
  from bisim obtain status x1 x2
    where sx1: "sx1 = (status, x1)"
    and sx2: "sx2 = (status, x2)"
    and Bisim: "t \<turnstile> (x1, m1) \<approx> (x2, m2)"
    by(cases sx1)(cases sx2, auto simp add: init_fin_bisim_iff)
  from bisim' obtain status' x1'' x2''
    where sx1'': "sx1'' = (status', x1'')"
    and sx2'': "sx2'' = (status', x2'')"
    and Bisim': "t \<turnstile> (x1'', m1') \<approx> (x2'', m2')"
     by(cases sx1'')(cases sx2'', auto simp add: init_fin_bisim_iff)
  from red1 sx1 obtain x1' where sx1': "sx1' = (status, x1')"
    and Red1: "r1.silent_moves t (x1, m1) (x1', m1)"
    by(cases sx1')(auto dest: r1.init_fin_silent_movesD)
  from red2 sx2 obtain x2' where sx2': "sx2' = (status, x2')"
    and Red2: "r2.silent_moves t (x2, m2) (x2', m2)"
    by(cases sx2')(auto dest: r2.init_fin_silent_movesD)
  from red1' sx1' sx1'' suspend1 obtain ta1'
    where Red1': "t \<turnstile> (x1', m1) -1-ta1'\<rightarrow> (x1'', m1')"
    and ta1: "ta1 = convert_TA_initial (convert_obs_initial ta1')"
    and Suspend1: "Suspend w \<in> set \<lbrace>ta1'\<rbrace>\<^bsub>w\<^esub>"
    and status: "status = Running" "status' = Running" by cases auto
  from red2' sx2' sx2'' suspend2 obtain ta2'
    where Red2': "t \<turnstile> (x2', m2) -2-ta2'\<rightarrow> (x2'', m2')"
    and ta2: "ta2 = convert_TA_initial (convert_obs_initial ta2')"
    and Suspend2: "Suspend w \<in> set \<lbrace>ta2'\<rbrace>\<^bsub>w\<^esub>" by cases auto
  from \<tau>1 sx1' sx1'' ta1 status have \<tau>1':"\<not> \<tau>move1 (x1', m1) ta1' (x1'', m1')" by simp
  from \<tau>2 sx2' sx2'' ta2 status have \<tau>2':"\<not> \<tau>move2 (x2', m2) ta2' (x2'', m2')" by simp
  from tasim ta1 ta2 have "ta1' \<sim>m ta2'" by simp
  with Bisim Red1 Red1' \<tau>1' Red2 Red2' \<tau>2' Bisim' have "x1'' \<approx>w x2''" 
    using Suspend1 Suspend2 by(rule bisim_waitI)
  thus "sx1'' \<approx>iw sx2''" using sx1'' sx2'' status by simp
next
  fix t sx1 m1 sx2 m2 ta1 sx1' m1'
  assume "t \<turnstile> (sx1, m1) \<approx>i (sx2, m2)" and "sx1 \<approx>iw sx2"
    and "r1.init_fin t (sx1, m1) ta1 (sx1', m1')"
    and "Notified \<in> set \<lbrace>ta1\<rbrace>\<^bsub>w\<^esub> \<or> WokenUp \<in> set \<lbrace>ta1\<rbrace>\<^bsub>w\<^esub>"
  thus "\<exists>ta2 sx2' m2'. r2.init_fin t (sx2, m2) ta2 (sx2', m2') \<and> t \<turnstile> (sx1', m1') \<approx>i (sx2', m2') \<and> 
                       ta_bisim init_fin_bisim ta1 ta2"
    by(rule init_fin_simulation_Wakeup1)
next
  fix t sx1 m1 sx2 m2 ta2 sx2' m2'
  assume "t \<turnstile> (sx1, m1) \<approx>i (sx2, m2)" and "sx1 \<approx>iw sx2"
    and "r2.init_fin t (sx2, m2) ta2 (sx2', m2')"
    and "Notified \<in> set \<lbrace>ta2\<rbrace>\<^bsub>w\<^esub> \<or> WokenUp \<in> set \<lbrace>ta2\<rbrace>\<^bsub>w\<^esub>"
  thus "\<exists>ta1 sx1' m1'. r1.init_fin t (sx1, m1) ta1 (sx1', m1') \<and> t \<turnstile> (sx1', m1') \<approx>i (sx2', m2') \<and> 
                       ta_bisim init_fin_bisim ta1 ta2"
    by(rule init_fin_simulation_Wakeup2)
next
  show "(\<exists>sx1. r1.init_fin_final sx1) = (\<exists>sx2. r2.init_fin_final sx2)"
    using ex_final1_conv_ex_final2 by(auto)
qed

end

context FWdelay_bisimulation_diverge begin

lemma init_fin_simulation_silent1:
  "\<lbrakk> t \<turnstile> sxm1 \<approx>i sxm2; \<tau>trsys.silent_move (r1.init_fin t) r1.init_fin_\<tau>move sxm1 sxm1' \<rbrakk>
  \<Longrightarrow> \<exists>sxm2'. \<tau>trsys.silent_moves (r2.init_fin t) r2.init_fin_\<tau>move sxm2 sxm2' \<and> t \<turnstile> sxm1' \<approx>i sxm2'"
by(cases sxm1')(auto 4 4 elim!: init_fin_bisim.cases dest!: r1.init_fin_silent_moveD dest: simulation_silent1 intro!: r2.init_fin_silent_moves_RunningI)

lemma init_fin_simulation_silent2:
  "\<lbrakk> t \<turnstile> sxm1 \<approx>i sxm2; \<tau>trsys.silent_move (r2.init_fin t) r2.init_fin_\<tau>move sxm2 sxm2' \<rbrakk>
  \<Longrightarrow> \<exists>sxm1'. \<tau>trsys.silent_moves (r1.init_fin t) r1.init_fin_\<tau>move sxm1 sxm1' \<and> t \<turnstile> sxm1' \<approx>i sxm2'"
using FWdelay_bisimulation_diverge.init_fin_simulation_silent1[OF FWdelay_bisimulation_diverge_flip]
unfolding flip_simps .

lemma init_fin_\<tau>diverge_bisim_inv:
  "t \<turnstile> sxm1 \<approx>i sxm2 
  \<Longrightarrow> \<tau>trsys.\<tau>diverge (r1.init_fin t) r1.init_fin_\<tau>move sxm1 =
      \<tau>trsys.\<tau>diverge (r2.init_fin t) r2.init_fin_\<tau>move sxm2"
by(cases sxm1)(cases sxm2, auto simp add: r1.init_fin_\<tau>diverge_conv r2.init_fin_\<tau>diverge_conv init_fin_bisim_iff \<tau>diverge_bisim_inv)

lemma init_fin_delay_bisimulation_diverge:
  "delay_bisimulation_diverge (r1.init_fin t) (r2.init_fin t) (init_fin_bisim t) (ta_bisim init_fin_bisim)
         r1.init_fin_\<tau>move r2.init_fin_\<tau>move"
by(blast intro: delay_bisimulation_diverge.intro init_fin_delay_bisimulation_obs delay_bisimulation_diverge_axioms.intro init_fin_simulation_silent1 init_fin_simulation_silent2 init_fin_\<tau>diverge_bisim_inv del: iffI)+

lemma init_fin_FWdelay_bisimulation_diverge:
  "FWdelay_bisimulation_diverge r1.init_fin_final r1.init_fin r2.init_fin_final r2.init_fin init_fin_bisim init_fin_bisim_wait r1.init_fin_\<tau>move r2.init_fin_\<tau>move"
by(intro FWdelay_bisimulation_diverge.intro init_fin_FWdelay_bisimulation_obs FWdelay_bisimulation_diverge_axioms.intro init_fin_delay_bisimulation_diverge)

end

context FWbisimulation begin

lemma init_fin_simulation1:
  assumes "t \<turnstile> s1 \<approx>i s2" and "r1.init_fin t s1 tl1 s1'"
  shows "\<exists>s2' tl2. r2.init_fin t s2 tl2 s2' \<and> t \<turnstile> s1' \<approx>i s2' \<and> ta_bisim init_fin_bisim tl1 tl2"
using init_fin_simulation1[OF assms] by(auto simp add: \<tau>moves_False init_fin_\<tau>moves_False)

lemma init_fin_simulation2:
  "\<lbrakk> t \<turnstile> s1 \<approx>i s2; r2.init_fin t s2 tl2 s2' \<rbrakk>
  \<Longrightarrow> \<exists>s1' tl1. r1.init_fin t s1 tl1 s1' \<and> t \<turnstile> s1' \<approx>i s2' \<and> ta_bisim init_fin_bisim tl1 tl2"
using FWbisimulation.init_fin_simulation1[OF FWbisimulation_flip]
unfolding flip_simps .

lemma init_fin_bisimulation: 
  "bisimulation (r1.init_fin t) (r2.init_fin t)  (init_fin_bisim t) (ta_bisim init_fin_bisim)"
by(unfold_locales)(erule (1) init_fin_simulation1 init_fin_simulation2)+

lemma init_fin_FWbisimulation:
  "FWbisimulation r1.init_fin_final r1.init_fin r2.init_fin_final r2.init_fin init_fin_bisim"
proof(intro FWbisimulation.intro r1.multithreaded_init_fin r2.multithreaded_init_fin FWbisimulation_axioms.intro init_fin_bisimulation)
  fix t sx1 m1 sx2 m2
  assume "t \<turnstile> (sx1, m1) \<approx>i (sx2, m2)"
  thus "r1.init_fin_final sx1 = r2.init_fin_final sx2"
    by cases simp_all
next
  fix t' sx m1 sxx m2 t sx1 sx2 ta1 sx1' m1' ta2 sx2' m2'
  assume "t' \<turnstile> (sx, m1) \<approx>i (sxx, m2)" "t \<turnstile> (sx1, m1) \<approx>i (sx2, m2)"
    and "r1.init_fin t (sx1, m1) ta1 (sx1', m1')"
    and "r2.init_fin t (sx2, m2) ta2 (sx2', m2')"
    and "t \<turnstile> (sx1', m1') \<approx>i (sx2', m2')"
    and "ta_bisim init_fin_bisim ta1 ta2"
  from FWdelay_bisimulation_obs.bisim_inv_red_other
  [OF init_fin_FWdelay_bisimulation_obs, OF this(1-2) _ this(3) _ _ this(4) _ this(5-6)]
  show "t' \<turnstile> (sx, m1') \<approx>i (sxx, m2')" by(simp add: init_fin_\<tau>moves_False)
next
  show "(\<exists>sx1. r1.init_fin_final sx1) = (\<exists>sx2. r2.init_fin_final sx2)"
    using ex_final1_conv_ex_final2 by(auto)
qed

end

end
