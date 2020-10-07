(*  Title:      JinjaThreads/Framework/FWLTS.thy
    Author:     Andreas Lochbihler
*)

section \<open>The multithreaded semantics as a labelled transition system\<close>

theory FWLTS
imports
  FWProgressAux
  FWLifting
  LTS
begin

sublocale multithreaded_base < trsys "r t" for t .
sublocale multithreaded_base < mthr: trsys redT .

\<comment> \<open>Move to FWSemantics?\<close>
definition redT_upd_\<epsilon> :: "('l,'t,'x,'m,'w) state \<Rightarrow> 't \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> ('l,'t,'x,'m,'w) state"
where [simp]: "redT_upd_\<epsilon> s t x' m' = (locks s, ((thr s)(t \<mapsto> (x', snd (the (thr s t)))), m'), wset s, interrupts s)"

lemma redT_upd_\<epsilon>_redT_upd:
  "redT_upd s t \<epsilon> x' m' (redT_upd_\<epsilon> s t x' m')"
by(auto simp add: redT_updLns_def redT_updWs_def)

context multithreaded begin
  
sublocale trsys "r t" for t .
    
sublocale mthr: trsys redT .
    
end
  
subsection \<open>The multithreaded semantics with internal actions\<close>

type_synonym
  ('l,'t,'x,'m,'w,'o) \<tau>moves =
    "'x \<times> 'm \<Rightarrow> ('l,'t,'x,'m,'w,'o) thread_action \<Rightarrow> 'x \<times> 'm \<Rightarrow> bool"

text \<open>pretty printing for \<open>\<tau>moves\<close>\<close>
print_translation \<open>
  let
    fun tr' [(Const (@{type_syntax "prod"}, _) $ x1 $ m1),
             (Const (@{type_syntax "fun"}, _) $
               (Const (@{type_syntax "prod"}, _) $ 
                 (Const (@{type_syntax "finfun"}, _) $ l $ 
                   (Const (@{type_syntax "list"}, _) $ Const (@{type_syntax "lock_action"}, _))) $
                 (Const (@{type_syntax "prod"},_) $ 
                   (Const (@{type_syntax "list"}, _) $ (Const (@{type_syntax "new_thread_action"}, _) $ t1 $ x2 $ m2)) $
                   (Const (@{type_syntax "prod"}, _) $ 
                     (Const (@{type_syntax "list"}, _) $ (Const (@{type_syntax "conditional_action"}, _) $ t2)) $
                     (Const (@{type_syntax "prod"}, _) $ 
                       (Const (@{type_syntax "list"}, _) $ (Const (@{type_syntax "wait_set_action"}, _) $ t3 $ w)) $
                       (Const (@{type_syntax prod}, _) $ 
                         (Const (@{type_syntax list}, _) $ (Const (@{type_syntax "interrupt_action"}, _) $ t4)) $
                         (Const (@{type_syntax "list"}, _) $ o1)))))) $
               (Const (@{type_syntax "fun"}, _) $ 
                 (Const (@{type_syntax "prod"}, _) $ x3 $ m3) $
                 (Const (@{type_syntax "bool"}, _))))] =
      if x1 = x2 andalso x1 = x3 andalso m1 = m2 andalso m1 = m3 andalso t1 = t2 andalso t2 = t3 andalso t3 = t4
      then Syntax.const (@{type_syntax "\<tau>moves"}) $ l $ t1 $ x1 $ m1 $ w $ o1
      else raise Match;
  in [(@{type_syntax "fun"}, K tr')]
  end
\<close>
typ "('l,'t,'x,'m,'w,'o) \<tau>moves"

locale \<tau>multithreaded = multithreaded_base +
  constrains final :: "'x \<Rightarrow> bool"
  and r :: "('l,'t,'x,'m,'w,'o) semantics"
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  fixes \<tau>move :: "('l,'t,'x,'m,'w,'o) \<tau>moves"

sublocale \<tau>multithreaded < \<tau>trsys "r t" \<tau>move for t .

context \<tau>multithreaded begin

inductive m\<tau>move :: "(('l,'t,'x,'m,'w) state, 't \<times> ('l,'t,'x,'m,'w,'o) thread_action) trsys"
where
  "\<lbrakk> thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>; thr s' t = \<lfloor>(x', ln')\<rfloor>; \<tau>move (x, shr s) ta (x', shr s') \<rbrakk>
  \<Longrightarrow> m\<tau>move s (t, ta) s'"

end

sublocale \<tau>multithreaded < mthr: \<tau>trsys redT m\<tau>move .

context \<tau>multithreaded begin

abbreviation \<tau>mredT :: "('l,'t,'x,'m,'w) state \<Rightarrow> ('l,'t,'x,'m,'w) state \<Rightarrow> bool"
where "\<tau>mredT == mthr.silent_move"

end

lemma (in multithreaded_base) \<tau>rtrancl3p_redT_thread_not_disappear:
  assumes "\<tau>trsys.\<tau>rtrancl3p redT \<tau>move s ttas s'" "thr s t \<noteq> None"
  shows "thr s' t \<noteq> None"
proof -
  interpret T: \<tau>trsys redT \<tau>move .
  show ?thesis
  proof
    assume "thr s' t = None"
    with \<open>\<tau>trsys.\<tau>rtrancl3p redT \<tau>move s ttas s'\<close> have "thr s t = None"
      by(induct rule: T.\<tau>rtrancl3p.induct)(auto simp add: split_paired_all dest: redT_thread_not_disappear)
    with \<open>thr s t \<noteq> None\<close> show False by contradiction
  qed
qed

lemma m\<tau>move_False: "\<tau>multithreaded.m\<tau>move (\<lambda>s ta s'. False) = (\<lambda>s ta s'. False)"
by(auto intro!: ext elim: \<tau>multithreaded.m\<tau>move.cases)

declare split_paired_Ex [simp del]

locale \<tau>multithreaded_wf =
  \<tau>multithreaded _ _ _ \<tau>move +
  multithreaded final r convert_RA
  for \<tau>move :: "('l,'t,'x,'m,'w,'o) \<tau>moves" +
  assumes \<tau>move_heap: "\<lbrakk> t \<turnstile> (x, m) -ta\<rightarrow> (x', m'); \<tau>move (x, m) ta (x', m') \<rbrakk> \<Longrightarrow> m = m'"
  assumes silent_tl: "\<tau>move s ta s' \<Longrightarrow> ta = \<epsilon>"
begin

lemma m\<tau>move_silentD: "m\<tau>move s (t, ta) s' \<Longrightarrow> ta = (K$ [], [], [], [], [], [])"
by(auto elim!: m\<tau>move.cases dest: silent_tl)

lemma m\<tau>move_heap: 
  assumes redT: "redT s (t, ta) s'"
  and m\<tau>move: "m\<tau>move s (t, ta) s'"
  shows "shr s' = shr s"
using m\<tau>move redT
by cases(auto dest: \<tau>move_heap elim!: redT.cases)

lemma \<tau>mredT_thread_preserved:
  "\<tau>mredT s s' \<Longrightarrow> thr s t = None \<longleftrightarrow> thr s' t = None"
by(auto simp add: mthr.silent_move_iff elim!: redT.cases dest!: m\<tau>move_silentD split: if_split_asm)

lemma \<tau>mRedT_thread_preserved:
  "\<tau>mredT^** s s' \<Longrightarrow> thr s t = None \<longleftrightarrow> thr s' t = None"
by(induct rule: rtranclp.induct)(auto dest: \<tau>mredT_thread_preserved[where t=t])

lemma \<tau>mtRedT_thread_preserved:
  "\<tau>mredT^++ s s' \<Longrightarrow> thr s t = None \<longleftrightarrow> thr s' t = None"
by(induct rule: tranclp.induct)(auto dest: \<tau>mredT_thread_preserved[where t=t])

lemma \<tau>mredT_add_thread_inv:
  assumes \<tau>red: "\<tau>mredT s s'" and tst: "thr s t = None"
  shows "\<tau>mredT (locks s, ((thr s)(t \<mapsto> xln), shr s), wset s, interrupts s) (locks s', ((thr s')(t \<mapsto> xln), shr s'), wset s', interrupts s')"
proof -
  obtain ls ts m ws "is" where s: "s = (ls, (ts, m), ws, is)" by(cases s) fastforce
  obtain ls' ts' m' ws' is' where s': "s' = (ls', (ts', m'), ws', is')" by(cases s') fastforce
  from \<tau>red s s' obtain t' where red: "(ls, (ts, m), ws, is) -t'\<triangleright>\<epsilon>\<rightarrow> (ls', (ts', m'), ws', is')"
    and \<tau>: "m\<tau>move (ls, (ts, m), ws, is) (t', \<epsilon>) (ls', (ts', m'), ws', is')"
    by(auto simp add: mthr.silent_move_iff dest: m\<tau>move_silentD)
  from red have "(ls, (ts(t \<mapsto> xln), m), ws, is) -t'\<triangleright>\<epsilon>\<rightarrow> (ls', (ts'(t \<mapsto> xln), m'), ws', is')"
  proof(cases rule: redT_elims)
    case (normal x x' m') with tst s show ?thesis
      by-(rule redT_normal, auto simp add: fun_upd_twist elim!: rtrancl3p_cases)
  next
    case (acquire x ln n)
    with tst s show ?thesis
      unfolding \<open>\<epsilon> = (K$ [], [], [], [], [], convert_RA ln)\<close>
      by -(rule redT_acquire, auto intro: fun_upd_twist)
  qed
  moreover from red tst s have tt': "t \<noteq> t'" by(cases) auto
  have "(\<lambda>t''. (ts(t \<mapsto> xln)) t'' \<noteq> None \<and> (ts(t \<mapsto> xln)) t'' \<noteq> (ts'(t \<mapsto> xln)) t'') =
        (\<lambda>t''. ts t'' \<noteq> None \<and> ts t'' \<noteq> ts' t'')" using tst s by(auto simp add: fun_eq_iff)
  with \<tau> tst tt' have "m\<tau>move (ls, (ts(t \<mapsto> xln), m), ws, is) (t', \<epsilon>) (ls', (ts'(t \<mapsto> xln), m'), ws', is')"
    by cases(rule m\<tau>move.intros, auto)
  ultimately show ?thesis unfolding s s' by auto
qed

lemma \<tau>mRedT_add_thread_inv:
  "\<lbrakk> \<tau>mredT^** s s'; thr s t = None \<rbrakk>
  \<Longrightarrow> \<tau>mredT^** (locks s, ((thr s)(t \<mapsto> xln), shr s), wset s, interrupts s) (locks s', ((thr s')(t \<mapsto> xln), shr s'), wset s', interrupts s')"
apply(induct rule: rtranclp_induct)
apply(blast dest: \<tau>mRedT_thread_preserved[where t=t] \<tau>mredT_add_thread_inv[where xln=xln] intro: rtranclp.rtrancl_into_rtrancl)+
done

lemma \<tau>mtRed_add_thread_inv:
  "\<lbrakk> \<tau>mredT^++ s s'; thr s t = None \<rbrakk>
  \<Longrightarrow> \<tau>mredT^++ (locks s, ((thr s)(t \<mapsto> xln), shr s), wset s, interrupts s) (locks s', ((thr s')(t \<mapsto> xln), shr s'), wset s', interrupts s')"
apply(induct rule: tranclp_induct)
apply(blast dest: \<tau>mtRedT_thread_preserved[where t=t] \<tau>mredT_add_thread_inv[where xln=xln] intro: tranclp.trancl_into_trancl)+
done

lemma silent_move_into_RedT_\<tau>_inv:
  assumes move: "silent_move t (x, shr s) (x', m')"
  and state: "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>" "wset s t = None"
  shows "\<tau>mredT s (redT_upd_\<epsilon> s t x' m')"
proof -
  from move obtain red: "t \<turnstile> (x, shr s) -\<epsilon>\<rightarrow> (x', m')" and \<tau>: "\<tau>move (x, shr s) \<epsilon> (x', m')"
    by(auto simp add: silent_move_iff dest: silent_tl)
  from red state have "s -t\<triangleright>\<epsilon>\<rightarrow> redT_upd_\<epsilon> s t x' m'"
    by -(rule redT_normal, auto simp add: redT_updLns_def o_def finfun_Diag_const2 redT_updWs_def)
  moreover from \<tau> red state have "m\<tau>move s (t, \<epsilon>) (redT_upd_\<epsilon> s t x' m')"
    by -(rule m\<tau>move.intros, auto dest: \<tau>move_heap simp add: redT_updLns_def)
  ultimately show ?thesis by auto
qed

lemma silent_moves_into_RedT_\<tau>_inv:
  assumes major: "silent_moves t (x, shr s) (x', m')"
  and state: "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>" "wset s t = None"
  shows "\<tau>mredT^** s (redT_upd_\<epsilon> s t x' m')"
using major
proof(induct rule: rtranclp_induct2)
  case refl with state show ?case by(cases s)(auto simp add: fun_upd_idem)
next
  case (step x' m' x'' m'')
  from \<open>silent_move t (x', m') (x'', m'')\<close> state
  have "\<tau>mredT (redT_upd_\<epsilon> s t x' m') (redT_upd_\<epsilon> (redT_upd_\<epsilon> s t x' m') t x'' m'')"
    by -(rule silent_move_into_RedT_\<tau>_inv, auto)
  hence "\<tau>mredT (redT_upd_\<epsilon> s t x' m') (redT_upd_\<epsilon> s t x'' m'')" by(simp)
  with \<open>\<tau>mredT^** s (redT_upd_\<epsilon> s t x' m')\<close> show ?case ..
qed

lemma red_rtrancl_\<tau>_heapD_inv:
  "\<lbrakk> silent_moves t s s'; wfs t s \<rbrakk> \<Longrightarrow> snd s' = snd s"
proof(induct rule: rtranclp_induct)
  case base show ?case ..
next
  case (step s' s'')
  thus ?case by(cases s, cases s', cases s'')(auto dest: \<tau>move_heap)
qed

lemma red_trancl_\<tau>_heapD_inv:
  "\<lbrakk> silent_movet t s s'; wfs t s \<rbrakk> \<Longrightarrow> snd s' = snd s"
proof(induct rule: tranclp_induct)
  case (base s') thus ?case by(cases s')(cases s, auto simp add: silent_move_iff dest: \<tau>move_heap)
next
  case (step s' s'')
  thus ?case by(cases s, cases s', cases s'')(auto simp add: silent_move_iff dest: \<tau>move_heap)
qed

lemma red_trancl_\<tau>_into_RedT_\<tau>_inv:
  assumes major: "silent_movet t (x, shr s) (x', m')"
  and state: "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>" "wset s t = None"
  shows "\<tau>mredT^++ s (redT_upd_\<epsilon> s t x' m')"
using major
proof(induct rule: tranclp_induct2)
  case (base x' m')
  thus ?case using state
    by -(rule tranclp.r_into_trancl, rule silent_move_into_RedT_\<tau>_inv, auto)
next
  case (step x' m' x'' m'')
  hence "\<tau>mredT^++ s (redT_upd_\<epsilon> s t x' m')" by blast
  moreover from \<open>silent_move t (x', m') (x'', m'')\<close> state
  have "\<tau>mredT (redT_upd_\<epsilon> s t x' m') (redT_upd_\<epsilon> (redT_upd_\<epsilon> s t x' m') t x'' m'')"
    by -(rule silent_move_into_RedT_\<tau>_inv, auto simp add: redT_updLns_def)
  hence "\<tau>mredT (redT_upd_\<epsilon> s t x' m') (redT_upd_\<epsilon> s t x'' m'')"
    by(simp add: redT_updLns_def)
  ultimately show ?case ..
qed

lemma \<tau>diverge_into_\<tau>mredT:
  assumes "\<tau>diverge t (x, shr s)"
  and "thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>" "wset s t = None"
  shows "mthr.\<tau>diverge s"
using assms
proof(coinduction arbitrary: s x)
  case (\<tau>diverge s x)
  note tst = \<open>thr s t = \<lfloor>(x, no_wait_locks)\<rfloor>\<close>
  from \<open>\<tau>diverge t (x, shr s)\<close> obtain x' m' where "silent_move t (x, shr s) (x', m')" 
    and "\<tau>diverge t (x', m')" by cases auto
  from \<open>silent_move t (x, shr s) (x', m')\<close> tst \<open>wset s t = None\<close>
  have "\<tau>mredT s (redT_upd_\<epsilon> s t x' m')" by(rule silent_move_into_RedT_\<tau>_inv)
  moreover have "thr (redT_upd_\<epsilon> s t x' m') t = \<lfloor>(x', no_wait_locks)\<rfloor>"
    using tst by(auto simp add: redT_updLns_def)
  moreover have "wset (redT_upd_\<epsilon> s t x' m') t = None" using \<open>wset s t = None\<close> by simp
  moreover from \<open>\<tau>diverge t (x', m')\<close> have "\<tau>diverge t (x', shr (redT_upd_\<epsilon> s t x' m'))" by simp
  ultimately show ?case using \<open>\<tau>diverge t (x', m')\<close> by blast
qed

lemma \<tau>diverge_\<tau>mredTD:
  assumes div: "mthr.\<tau>diverge s"
  and fin: "finite (dom (thr s))"
  shows "\<exists>t x. thr s t = \<lfloor>(x, no_wait_locks)\<rfloor> \<and> wset s t = None \<and> \<tau>diverge t (x, shr s)"
using fin div
proof(induct A\<equiv>"dom (thr s)" arbitrary: s rule: finite_induct)
  case empty
  from \<open>mthr.\<tau>diverge s\<close> obtain s' where "\<tau>mredT s s'" by cases auto
  with \<open>{} = dom (thr s)\<close>[symmetric] have False by(auto elim!: mthr.silent_move.cases redT.cases)
  thus ?case ..
next
  case (insert t A)
  note IH = \<open>\<And>s. \<lbrakk> A = dom (thr s); mthr.\<tau>diverge s \<rbrakk>
             \<Longrightarrow> \<exists>t x. thr s t = \<lfloor>(x, no_wait_locks)\<rfloor> \<and> wset s t = None \<and> \<tau>diverge t (x, shr s)\<close>
  from \<open>insert t A = dom (thr s)\<close>
  obtain x ln where tst: "thr s t = \<lfloor>(x, ln)\<rfloor>" by(fastforce simp add: dom_def)
  define s' where "s' = (locks s, ((thr s)(t := None), shr s), wset s, interrupts s)"
  show ?case
  proof(cases "ln = no_wait_locks \<and> \<tau>diverge t (x, shr s) \<and> wset s t = None")
    case True
    with tst show ?thesis by blast
  next
    case False
    define xm where "xm = (x, shr s)"
    define xm' where "xm' = (x, shr s)"
    have "A = dom (thr s')" using \<open>t \<notin> A\<close> \<open>insert t A = dom (thr s)\<close>
      unfolding s'_def by auto
    moreover { 
      from xm'_def tst \<open>mthr.\<tau>diverge s\<close> False
      have "\<exists>s x. thr s t = \<lfloor>(x, ln)\<rfloor> \<and> (ln \<noteq> no_wait_locks \<or> wset s t \<noteq> None \<or> \<not> \<tau>diverge t xm') \<and>
                  s' = (locks s, ((thr s)(t := None), shr s), wset s, interrupts s) \<and> xm = (x, shr s) \<and> 
                  mthr.\<tau>diverge s \<and> silent_moves t xm' xm"
        unfolding s'_def xm_def by blast
      moreover
      from False have "wfP (if \<tau>diverge t xm' then (\<lambda>s s'. False) else flip (silent_move_from t xm'))"
        using \<tau>diverge_neq_wfP_silent_move_from[of t "(x, shr s)"] unfolding xm'_def by(auto)
      ultimately have "mthr.\<tau>diverge s'"
      proof(coinduct s' xm rule: mthr.\<tau>diverge_trancl_measure_coinduct)
        case (\<tau>diverge s' xm)
        then obtain s x where tst: "thr s t = \<lfloor>(x, ln)\<rfloor>"
          and blocked: "ln \<noteq> no_wait_locks \<or> wset s t \<noteq> None \<or> \<not> \<tau>diverge t xm'"
          and s'_def: "s' = (locks s, ((thr s)(t := None), shr s), wset s, interrupts s)"
          and xm_def: "xm = (x, shr s)"
          and xmxm': "silent_moves t xm' (x, shr s)"
          and "mthr.\<tau>diverge s" by blast
        from \<open>mthr.\<tau>diverge s\<close> obtain s'' where "\<tau>mredT s s''" "mthr.\<tau>diverge s''" by cases auto
        from \<open>\<tau>mredT s s''\<close> obtain t' ta where "s -t'\<triangleright>ta\<rightarrow> s''" and "m\<tau>move s (t', ta) s''" by auto
        then obtain x' x'' m'' where red: "t' \<turnstile> \<langle>x', shr s\<rangle> -ta\<rightarrow> \<langle>x'', m''\<rangle>"
          and tst': "thr s t' = \<lfloor>(x', no_wait_locks)\<rfloor>" 
          and aoe: "actions_ok s t' ta"
          and s'': "redT_upd s t' ta x'' m'' s''"
          by cases(fastforce elim: m\<tau>move.cases)+
        from \<open>m\<tau>move s (t', ta) s''\<close> have [simp]: "ta = \<epsilon>"
          by(auto elim!: m\<tau>move.cases dest!: silent_tl)
        hence wst': "wset s t' = None" using aoe by auto
        from \<open>m\<tau>move s (t', ta) s''\<close> tst' s''
        have "\<tau>move (x', shr s) \<epsilon> (x'', m'')" by(auto elim: m\<tau>move.cases)
        show ?case
        proof(cases "t' = t")
          case False
          with tst' wst' have "thr s' t' = \<lfloor>(x', no_wait_locks)\<rfloor>"
            "wset s' t' = None" "shr s' = shr s" unfolding s'_def by auto
          with red have "s' -t'\<triangleright>\<epsilon>\<rightarrow> redT_upd_\<epsilon> s' t' x'' m''"
            by -(rule redT_normal, auto simp add: redT_updLns_def o_def finfun_Diag_const2 redT_updWs_def)
          moreover from \<open>\<tau>move (x', shr s) \<epsilon> (x'', m'')\<close> \<open>thr s' t' = \<lfloor>(x', no_wait_locks)\<rfloor>\<close> \<open>shr s' = shr s\<close>
          have "m\<tau>move s' (t', ta) (redT_upd_\<epsilon> s' t' x'' m'')"
            by -(rule m\<tau>move.intros, auto)
          ultimately have "\<tau>mredT s' (redT_upd_\<epsilon> s' t' x'' m'')"
            unfolding \<open>ta = \<epsilon>\<close> by(rule mthr.silent_move.intros)
          hence "\<tau>mredT^++ s' (redT_upd_\<epsilon> s' t' x'' m'')" ..
          moreover have "thr s'' t = \<lfloor>(x, ln)\<rfloor>"
            using tst \<open>t' \<noteq> t\<close> s'' by auto
          moreover from \<open>\<tau>move (x', shr s) \<epsilon> (x'', m'')\<close> red
          have [simp]: "m'' = shr s" by(auto dest: \<tau>move_heap)
          hence "shr s = shr s''" using s'' by(auto)
          have "ln \<noteq> no_wait_locks \<or> wset s'' t \<noteq> None \<or> \<not> \<tau>diverge t xm'"
            using blocked s'' by(auto simp add: redT_updWs_def elim!: rtrancl3p_cases)
          moreover have "redT_upd_\<epsilon> s' t' x'' m'' = (locks s'', ((thr s'')(t := None), shr s''), wset s'', interrupts s'')"
            unfolding s'_def using tst s'' \<open>t' \<noteq> t\<close>
            by(auto intro: ext elim!: rtrancl3p_cases simp add: redT_updLns_def redT_updWs_def)
          ultimately show ?thesis using \<open>mthr.\<tau>diverge s''\<close> xmxm'
            unfolding \<open>shr s = shr s''\<close> by blast
        next
          case True
          with tst tst' wst' blocked have "\<not> \<tau>diverge t xm'"
            and [simp]: "x' = x" by auto
          moreover from red \<open>\<tau>move (x', shr s) \<epsilon> (x'', m'')\<close> True
          have "silent_move t (x, shr s) (x'', m'')" by auto
          with xmxm' have "silent_move_from t xm' (x, shr s) (x'', m'')"
            by(rule silent_move_fromI)
          ultimately have "(if \<tau>diverge t xm' then \<lambda>s s'. False else flip (silent_move_from t xm')) (x'', m'') xm"
            by(auto simp add: flip_conv xm_def)
          moreover have "thr s'' t = \<lfloor>(x'', ln)\<rfloor>" using tst True s''
            by(auto simp add: redT_updLns_def)
          moreover from \<open>\<tau>move (x', shr s) \<epsilon> (x'', m'')\<close> red
          have [simp]: "m'' = shr s" by(auto dest: \<tau>move_heap)
          hence "shr s = shr s''" using s'' by auto
          have "s' = (locks s'', ((thr s'')(t := None), shr s''), wset s'', interrupts s'')"
            using True s'' unfolding s'_def 
            by(auto intro: ext elim!: rtrancl3p_cases simp add: redT_updLns_def redT_updWs_def)
          moreover have "(x'', m'') = (x'', shr s'')" using s'' by auto
          moreover from xmxm' \<open>silent_move t (x, shr s) (x'', m'')\<close>
          have "silent_moves t xm' (x'', shr s'')"
            unfolding \<open>m'' = shr s\<close> \<open>shr s = shr s''\<close> by auto
          ultimately show ?thesis using \<open>\<not> \<tau>diverge t xm'\<close> \<open>mthr.\<tau>diverge s''\<close> by blast
        qed
      qed }
    ultimately have "\<exists>t x. thr s' t = \<lfloor>(x, no_wait_locks)\<rfloor> \<and> wset s' t = None \<and> \<tau>diverge t (x, shr s')" by(rule IH)
    then obtain t' x' where "thr s' t' = \<lfloor>(x', no_wait_locks)\<rfloor>"
      and "wset s' t' = None" and "\<tau>diverge t' (x', shr s')" by blast
    moreover with False have "t' \<noteq> t" by(auto simp add: s'_def)
    ultimately have "thr s t' = \<lfloor>(x', no_wait_locks)\<rfloor>" "wset s t' = None" "\<tau>diverge t' (x', shr s)"
      unfolding s'_def by auto
    thus ?thesis by blast
  qed
qed

lemma \<tau>mredT_preserves_final_thread:
  "\<lbrakk> \<tau>mredT s s'; final_thread s t \<rbrakk> \<Longrightarrow> final_thread s' t"
by(auto elim: mthr.silent_move.cases intro: redT_preserves_final_thread)

lemma \<tau>mRedT_preserves_final_thread:
  "\<lbrakk> \<tau>mredT^** s s'; final_thread s t \<rbrakk> \<Longrightarrow> final_thread s' t"
by(induct rule: rtranclp.induct)(blast intro: \<tau>mredT_preserves_final_thread)+

lemma silent_moves2_silentD:
  assumes "rtrancl3p mthr.silent_move2 s ttas s'"
  and "(t, ta) \<in> set ttas"
  shows "ta = \<epsilon>"
using assms
by(induct)(auto simp add: mthr.silent_move2_def dest: m\<tau>move_silentD)

lemma inf_step_silentD:
  assumes step: "trsys.inf_step mthr.silent_move2 s ttas"
  and lset: "(t, ta) \<in> lset ttas"
  shows "ta = \<epsilon>"
using lset step
by(induct arbitrary: s rule: lset_induct)(fastforce elim: trsys.inf_step.cases simp add: mthr.silent_move2_def dest: m\<tau>move_silentD)+

end

subsection \<open>The multithreaded semantics with a well-founded relation on states\<close>

locale multithreaded_base_measure = multithreaded_base +
  constrains final :: "'x \<Rightarrow> bool"
  and r :: "('l,'t,'x,'m,'w,'o) semantics"
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  fixes \<mu> :: "('x \<times> 'm) \<Rightarrow> ('x \<times> 'm) \<Rightarrow> bool"
begin

inductive m\<mu>t :: "'m \<Rightarrow> ('l,'t,'x) thread_info \<Rightarrow> ('l,'t,'x) thread_info \<Rightarrow> bool"
for m and ts and ts'
where
  m\<mu>tI:
  "\<And>ln. \<lbrakk> finite (dom ts); ts t = \<lfloor>(x, ln)\<rfloor>; ts' t = \<lfloor>(x', ln')\<rfloor>; \<mu> (x, m) (x', m); \<And>t'. t' \<noteq> t \<Longrightarrow> ts t' = ts' t' \<rbrakk>
  \<Longrightarrow> m\<mu>t m ts ts'"

definition m\<mu> :: "('l,'t,'x,'m,'w) state \<Rightarrow> ('l,'t,'x,'m,'w) state \<Rightarrow> bool"
where "m\<mu> s s' \<longleftrightarrow> shr s = shr s' \<and> m\<mu>t (shr s) (thr s) (thr s')"

lemma m\<mu>t_thr_dom_eq: "m\<mu>t m ts ts' \<Longrightarrow> dom ts = dom ts'"
apply(erule m\<mu>t.cases)
apply(rule equalityI)
 apply(rule subsetI)
 apply(case_tac "xa = t")
  apply(auto)[2]
apply(rule subsetI)
apply(case_tac "xa = t")
apply auto
done

lemma m\<mu>_finite_thrD:
  assumes "m\<mu>t m ts ts'"
  shows "finite (dom ts)" "finite (dom ts')"
using assms
by(simp_all add: m\<mu>t_thr_dom_eq[symmetric])(auto elim: m\<mu>t.cases)

end

locale multithreaded_base_measure_wf = multithreaded_base_measure +
  constrains final :: "'x \<Rightarrow> bool"
  and r :: "('l,'t,'x,'m,'w,'o) semantics"
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and \<mu> :: "('x \<times> 'm) \<Rightarrow> ('x \<times> 'm) \<Rightarrow> bool"
  assumes wf_\<mu>: "wfP \<mu>"
begin

lemma wf_m\<mu>t: "wfP (m\<mu>t m)"
unfolding wfP_eq_minimal
proof(intro strip)
  fix Q :: "('l,'t,'x) thread_info set" and ts
  assume "ts \<in> Q"
  show "\<exists>z\<in>Q. \<forall>y. m\<mu>t m y z \<longrightarrow> y \<notin> Q"
  proof(cases "finite (dom ts)")
    case False
    hence "\<forall>y. m\<mu>t m y ts \<longrightarrow> y \<notin> Q" by(auto dest: m\<mu>_finite_thrD)
    thus ?thesis using \<open>ts \<in> Q\<close> by blast
  next
    case True
    thus ?thesis using \<open>ts \<in> Q\<close>
    proof(induct A\<equiv>"dom ts" arbitrary: ts Q rule: finite_induct)
      case empty
      hence "dom ts = {}" by simp
      with \<open>ts \<in> Q\<close> show ?case by(auto elim: m\<mu>t.cases)
    next
      case (insert t A)
      note IH = \<open>\<And>ts Q. \<lbrakk>A = dom ts; ts \<in> Q\<rbrakk> \<Longrightarrow> \<exists>z\<in>Q. \<forall>y. m\<mu>t m y z \<longrightarrow> y \<notin> Q\<close>
      define Q' where "Q' = {ts. ts t = None \<and> (\<exists>xln. ts(t \<mapsto> xln) \<in> Q)}"
      let ?ts' = "ts(t := None)"
      from \<open>insert t A = dom ts\<close> \<open>t \<notin> A\<close> have "A = dom ?ts'" by auto
      moreover from \<open>insert t A = dom ts\<close> obtain xln where "ts t = \<lfloor>xln\<rfloor>" by(cases "ts t") auto
      hence "ts(t \<mapsto> xln) = ts" by(auto simp add: fun_eq_iff)
      with \<open>ts \<in> Q\<close> have "ts(t \<mapsto> xln) \<in> Q" by(auto)
      hence "?ts' \<in> Q'" unfolding Q'_def by(auto simp del: split_paired_Ex)
      ultimately have "\<exists>z\<in>Q'. \<forall>y. m\<mu>t m y z \<longrightarrow> y \<notin> Q'" by(rule IH)
      then obtain ts' where "ts' \<in> Q'" 
        and min: "\<And>ts''. m\<mu>t m ts'' ts' \<Longrightarrow> ts'' \<notin> Q'" by blast
      from \<open>ts' \<in> Q'\<close> obtain x' ln' where "ts' t = None" "ts'(t \<mapsto> (x', ln')) \<in> Q"
        unfolding Q'_def by auto
      define Q'' where "Q'' = {(x, m)|x. \<exists>ln. ts'(t \<mapsto> (x, ln)) \<in> Q}"
      from \<open>ts'(t \<mapsto> (x', ln')) \<in> Q\<close> have "(x', m) \<in> Q''" unfolding Q''_def by blast
      hence "\<exists>xm''\<in>Q''. \<forall>xm'''. \<mu> xm''' xm'' \<longrightarrow> xm''' \<notin> Q''" by(rule wf_\<mu>[unfolded wfP_eq_minimal, rule_format])
      then obtain xm'' where "xm'' \<in> Q''" and min': "\<And>xm'''. \<mu> xm''' xm'' \<Longrightarrow> xm''' \<notin> Q''" by blast
      from \<open>xm'' \<in> Q''\<close> obtain x'' ln'' where "xm'' = (x'', m)" "ts'(t \<mapsto> (x'', ln'')) \<in> Q" unfolding Q''_def by blast
      moreover {
        fix ts''
        assume "m\<mu>t m ts'' (ts'(t \<mapsto> (x'', ln'')))"
        then obtain T X'' LN'' X' LN'
          where "finite (dom ts'')" "ts'' T = \<lfloor>(X'', LN'')\<rfloor>" 
          and "(ts'(t \<mapsto> (x'', ln''))) T = \<lfloor>(X', LN')\<rfloor>" "\<mu> (X'', m) (X', m)"
          and eq: "\<And>t'. t' \<noteq> T \<Longrightarrow> ts'' t' = (ts'(t \<mapsto> (x'', ln''))) t'" by(cases) blast
        have "ts'' \<notin> Q"
        proof(cases "T = t")
          case True
          from True \<open>(ts'(t \<mapsto> (x'', ln''))) T = \<lfloor>(X', LN')\<rfloor>\<close> have "X' = x''" by simp
          with \<open>\<mu> (X'', m) (X', m)\<close> have "(X'', m) \<notin> Q''" by(auto dest: min'[unfolded \<open>xm'' = (x'', m)\<close>])
          hence "\<forall>ln. ts'(t \<mapsto> (X'', ln)) \<notin> Q" by(simp add: Q''_def)
          moreover from \<open>ts' t = None\<close> eq True
          have "ts''(t := None) = ts'" by(auto simp add: fun_eq_iff)
          with \<open>ts'' T = \<lfloor>(X'', LN'')\<rfloor>\<close> True
          have ts'': "ts'' = ts'(t \<mapsto> (X'', LN''))" by(auto intro!: ext)
          ultimately show ?thesis by blast
        next
          case False
          from \<open>finite (dom ts'')\<close> have "finite (dom (ts''(t := None)))" by simp
          moreover from \<open>ts'' T = \<lfloor>(X'', LN'')\<rfloor>\<close> False
          have "(ts''(t := None)) T = \<lfloor>(X'', LN'')\<rfloor>" by simp
          moreover from \<open>(ts'(t \<mapsto> (x'', ln''))) T = \<lfloor>(X', LN')\<rfloor>\<close> False
          have "ts' T = \<lfloor>(X', LN')\<rfloor>" by simp
          ultimately have "m\<mu>t m (ts''(t := None)) ts'" using \<open>\<mu> (X'', m) (X', m)\<close>
          proof(rule m\<mu>tI)
            fix t'
            assume "t' \<noteq> T"
            with eq[OF False[symmetric]] eq[OF this] \<open>ts' t = None\<close>
            show "(ts''(t := None)) t' = ts' t'" by auto
          qed
          hence "ts''(t := None) \<notin> Q'" by(rule min)
          thus ?thesis
          proof(rule contrapos_nn)
            assume "ts'' \<in> Q"
            from eq[OF False[symmetric]] have "ts'' t = \<lfloor>(x'', ln'')\<rfloor>" by simp
            hence ts'': "ts''(t \<mapsto> (x'', ln'')) = ts''" by(auto simp add: fun_eq_iff)
            from \<open>ts'' \<in> Q\<close> have "ts''(t \<mapsto> (x'', ln'')) \<in> Q" unfolding ts'' .
            thus "ts''(t := None) \<in> Q'" unfolding Q'_def by auto
          qed
        qed
      }
      ultimately show ?case by blast
    qed
  qed
qed

lemma wf_m\<mu>: "wfP m\<mu>"
proof -
  have "wf (inv_image (same_fst (\<lambda>m. True) (\<lambda>m. {(ts, ts'). m\<mu>t m ts ts'})) (\<lambda>s. (shr s, thr s)))"
    by(rule wf_inv_image)(rule wf_same_fst, rule wf_m\<mu>t[unfolded wfP_def])
  also have "inv_image (same_fst (\<lambda>m. True) (\<lambda>m. {(ts, ts'). m\<mu>t m ts ts'})) (\<lambda>s. (shr s, thr s)) = {(s, s'). m\<mu> s s'}"
    by(auto simp add: m\<mu>_def same_fst_def)
  finally show ?thesis by(simp add: wfP_def)
qed

end

end
