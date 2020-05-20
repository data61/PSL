(*  Title:      JinjaThreads/Framework/FWBisimulation.thy
    Author:     Andreas Lochbihler
*)

section \<open>Bisimulation relations for the multithreaded semantics\<close>

theory FWBisimulation
imports
  FWLTS
  Bisimulation
begin

subsection \<open>Definitions for lifting bisimulation relations\<close>

primrec nta_bisim :: "('t \<Rightarrow> ('x1 \<times> 'm1, 'x2 \<times> 'm2) bisim) \<Rightarrow> (('t,'x1,'m1) new_thread_action, ('t,'x2,'m2) new_thread_action) bisim"
  where
  [code del]: "nta_bisim bisim (NewThread t x m) ta = (\<exists>x' m'. ta = NewThread t x' m' \<and> bisim t (x, m) (x', m'))"
| "nta_bisim bisim (ThreadExists t b) ta = (ta = ThreadExists t b)"

lemma nta_bisim_1_code [code]:
  "nta_bisim bisim (NewThread t x m) ta = (case ta of NewThread t' x' m' \<Rightarrow> t = t' \<and> bisim t (x, m) (x', m') | _ \<Rightarrow> False)"
by(auto split: new_thread_action.split)
  
lemma nta_bisim_simps_sym [simp]:
  "nta_bisim bisim ta (NewThread t x m) = (\<exists>x' m'. ta = NewThread t x' m' \<and> bisim t (x', m') (x, m))"
  "nta_bisim bisim ta (ThreadExists t b) = (ta = ThreadExists t b)"
by(cases ta, auto)+

definition ta_bisim :: "('t \<Rightarrow> ('x1 \<times> 'm1, 'x2 \<times> 'm2) bisim) \<Rightarrow> (('l,'t,'x1,'m1,'w,'o) thread_action, ('l,'t,'x2,'m2,'w,'o) thread_action) bisim"
where
  "ta_bisim bisim ta1 ta2 \<equiv>
  \<lbrace> ta1 \<rbrace>\<^bsub>l\<^esub> = \<lbrace> ta2 \<rbrace>\<^bsub>l\<^esub> \<and> \<lbrace> ta1 \<rbrace>\<^bsub>w\<^esub> = \<lbrace> ta2 \<rbrace>\<^bsub>w\<^esub> \<and> \<lbrace> ta1 \<rbrace>\<^bsub>c\<^esub> = \<lbrace> ta2 \<rbrace>\<^bsub>c\<^esub> \<and> \<lbrace> ta1 \<rbrace>\<^bsub>o\<^esub> = \<lbrace> ta2 \<rbrace>\<^bsub>o\<^esub> \<and> \<lbrace> ta1 \<rbrace>\<^bsub>i\<^esub> = \<lbrace> ta2 \<rbrace>\<^bsub>i\<^esub> \<and>
  list_all2 (nta_bisim bisim) \<lbrace> ta1 \<rbrace>\<^bsub>t\<^esub> \<lbrace> ta2 \<rbrace>\<^bsub>t\<^esub>"

lemma ta_bisim_empty [iff]: "ta_bisim bisim \<epsilon> \<epsilon>"
by(auto simp add: ta_bisim_def)

lemma ta_bisim_\<epsilon> [simp]:
  "ta_bisim b \<epsilon> ta' \<longleftrightarrow> ta' = \<epsilon>" "ta_bisim b ta \<epsilon> \<longleftrightarrow> ta = \<epsilon>"
apply(cases ta', fastforce simp add: ta_bisim_def)
apply(cases ta, fastforce simp add: ta_bisim_def)
done

lemma nta_bisim_mono:
  assumes major: "nta_bisim bisim ta ta'"
  and mono: "\<And>t s1 s2. bisim t s1 s2 \<Longrightarrow> bisim' t s1 s2"
  shows "nta_bisim bisim' ta ta'"
using major by(cases ta)(auto intro: mono)

lemma ta_bisim_mono:
  assumes major: "ta_bisim bisim ta1 ta2"
  and mono: "\<And>t s1 s2. bisim t s1 s2 \<Longrightarrow> bisim' t s1 s2"
  shows "ta_bisim bisim' ta1 ta2"
using major
by(auto simp add: ta_bisim_def elim!: List.list_all2_mono nta_bisim_mono intro: mono)

lemma nta_bisim_flip [flip_simps]:
  "nta_bisim (\<lambda>t. flip (bisim t)) = flip (nta_bisim bisim)"
by(rule ext)(case_tac x, auto simp add: flip_simps)

lemma ta_bisim_flip [flip_simps]:
  "ta_bisim (\<lambda>t. flip (bisim t)) = flip (ta_bisim bisim)"
by(auto simp add: fun_eq_iff flip_simps ta_bisim_def)

locale FWbisimulation_base =
  r1: multithreaded_base final1 r1 convert_RA +
  r2: multithreaded_base final2 r2 convert_RA 
  for final1 :: "'x1 \<Rightarrow> bool"
  and r1 :: "('l,'t,'x1,'m1,'w,'o) semantics" ("_ \<turnstile> _ -1-_\<rightarrow> _" [50, 0, 0, 50] 80)
  and final2 :: "'x2 \<Rightarrow> bool"
  and r2 :: "('l,'t,'x2,'m2,'w,'o) semantics" ("_ \<turnstile> _ -2-_\<rightarrow> _" [50, 0, 0, 50] 80) 
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  +
  fixes bisim :: "'t \<Rightarrow> ('x1 \<times> 'm1, 'x2 \<times> 'm2) bisim" ("_ \<turnstile> _/ \<approx> _" [50, 50, 50] 60)
  and bisim_wait :: "('x1, 'x2) bisim" ("_/ \<approx>w _" [50, 50] 60)
begin

notation r1.redT_syntax1 ("_ -1-_\<triangleright>_\<rightarrow> _" [50,0,0,50] 80)
notation r2.redT_syntax1 ("_ -2-_\<triangleright>_\<rightarrow> _" [50,0,0,50] 80)

notation r1.RedT ("_ -1-\<triangleright>_\<rightarrow>* _" [50,0,50] 80)
notation r2.RedT ("_ -2-\<triangleright>_\<rightarrow>* _" [50,0,50] 80)

notation r1.must_sync ("_ \<turnstile> \<langle>_,/ _\<rangle>/ \<wrong>1" [50,0,0] 81)
notation r2.must_sync ("_ \<turnstile> \<langle>_,/ _\<rangle>/ \<wrong>2" [50,0,0] 81)

notation r1.can_sync  ("_ \<turnstile> \<langle>_,/ _\<rangle>/ _/ \<wrong>1" [50,0,0,0] 81)
notation r2.can_sync  ("_ \<turnstile> \<langle>_,/ _\<rangle>/ _/ \<wrong>2" [50,0,0,0] 81)

abbreviation ta_bisim_bisim_syntax ("_/ \<sim>m _" [50, 50] 60)
where "ta1 \<sim>m ta2 \<equiv> ta_bisim bisim ta1 ta2"

definition tbisim :: "bool \<Rightarrow> 't \<Rightarrow> ('x1 \<times> 'l released_locks) option \<Rightarrow> 'm1 \<Rightarrow> ('x2 \<times> 'l released_locks) option \<Rightarrow> 'm2 \<Rightarrow> bool" where
  "\<And>ln. tbisim nw t ts1 m1 ts2 m2 \<longleftrightarrow>
  (case ts1 of None \<Rightarrow> ts2 = None
       | \<lfloor>(x1, ln)\<rfloor> \<Rightarrow> (\<exists>x2. ts2 = \<lfloor>(x2, ln)\<rfloor> \<and> t \<turnstile> (x1, m1) \<approx> (x2, m2) \<and> (nw \<or> x1 \<approx>w x2)))"

lemma tbisim_NoneI: "tbisim w t None m None m'"
by(simp add: tbisim_def)

lemma tbisim_SomeI:
  "\<And>ln. \<lbrakk> t \<turnstile> (x, m) \<approx> (x', m'); nw \<or> x \<approx>w x' \<rbrakk> \<Longrightarrow> tbisim nw t (Some (x, ln)) m (Some (x', ln)) m'"
by(simp add: tbisim_def)

lemma tbisim_cases[consumes 1, case_names None Some]:
  assumes major: "tbisim nw t ts1 m1 ts2 m2"
  and "\<lbrakk> ts1 = None; ts2 = None \<rbrakk> \<Longrightarrow> thesis"
  and "\<And>x ln x'. \<lbrakk> ts1 = \<lfloor>(x, ln)\<rfloor>; ts2 = \<lfloor>(x', ln)\<rfloor>; t \<turnstile> (x, m1) \<approx> (x', m2); nw \<or> x \<approx>w x' \<rbrakk> \<Longrightarrow> thesis"
  shows thesis
using assms
by(auto simp add: tbisim_def)

definition mbisim :: "(('l,'t,'x1,'m1,'w) state, ('l,'t,'x2,'m2,'w) state) bisim" ("_ \<approx>m _" [50, 50] 60)
where
  "s1 \<approx>m s2 \<equiv> 
  finite (dom (thr s1)) \<and> locks s1 = locks s2 \<and> wset s1 = wset s2 \<and> wset_thread_ok (wset s1) (thr s1) \<and>
  interrupts s1 = interrupts s2 \<and>
  (\<forall>t. tbisim (wset s2 t = None) t (thr s1 t) (shr s1) (thr s2 t) (shr s2))"

lemma mbisim_thrNone_eq: "s1 \<approx>m s2 \<Longrightarrow> thr s1 t = None \<longleftrightarrow> thr s2 t = None"
unfolding mbisim_def tbisim_def
apply(clarify)
apply(erule allE[where x=t])
apply(clarsimp)
done

lemma mbisim_thrD1:
  "\<And>ln. \<lbrakk> s1 \<approx>m s2; thr s1 t = \<lfloor>(x, ln)\<rfloor> \<rbrakk>
  \<Longrightarrow> \<exists>x'. thr s2 t = \<lfloor>(x', ln)\<rfloor> \<and> t \<turnstile> (x, shr s1) \<approx> (x', shr s2) \<and> (wset s1 t = None \<or> x \<approx>w x')"
by(fastforce simp add: mbisim_def tbisim_def)

lemma mbisim_thrD2:
  "\<And>ln. \<lbrakk> s1 \<approx>m s2; thr s2 t = \<lfloor>(x, ln)\<rfloor> \<rbrakk>
  \<Longrightarrow> \<exists>x'. thr s1 t = \<lfloor>(x', ln)\<rfloor> \<and> t \<turnstile> (x', shr s1) \<approx> (x, shr s2) \<and> (wset s2 t = None \<or> x' \<approx>w x)"
by(frule mbisim_thrNone_eq[where t=t])(cases "thr s1 t",(fastforce simp add: mbisim_def tbisim_def)+)

lemma mbisim_dom_eq: "s1 \<approx>m s2 \<Longrightarrow> dom (thr s1) = dom (thr s2)"
apply(clarsimp simp add: dom_def fun_eq_iff simp del: not_None_eq)
apply(rule Collect_cong)
apply(drule mbisim_thrNone_eq)
apply(simp del: not_None_eq)
done

lemma mbisim_wset_thread_ok1:
  "s1 \<approx>m s2 \<Longrightarrow> wset_thread_ok (wset s1) (thr s1)"
by(clarsimp simp add: mbisim_def)

lemma mbisim_wset_thread_ok2:
  assumes "s1 \<approx>m s2"
  shows "wset_thread_ok (wset s2) (thr s2)"
using assms
apply(clarsimp simp add: mbisim_def)
apply(auto intro!: wset_thread_okI simp add: mbisim_thrNone_eq[OF assms, THEN sym] dest: wset_thread_okD)
done

lemma mbisimI:
  "\<lbrakk> finite (dom (thr s1)); locks s1 = locks s2; wset s1 = wset s2; interrupts s1 = interrupts s2; 
     wset_thread_ok (wset s1) (thr s1);
     \<And>t. thr s1 t = None \<Longrightarrow> thr s2 t = None;
     \<And>t x1 ln. thr s1 t = \<lfloor>(x1, ln)\<rfloor> \<Longrightarrow> \<exists>x2. thr s2 t = \<lfloor>(x2, ln)\<rfloor> \<and> t \<turnstile> (x1, shr s1) \<approx> (x2, shr s2) \<and> (wset s2 t = None \<or> x1 \<approx>w x2) \<rbrakk>
  \<Longrightarrow> s1 \<approx>m s2"
by(fastforce simp add: mbisim_def tbisim_def)

lemma mbisimI2:
  "\<lbrakk> finite (dom (thr s2)); locks s1 = locks s2; wset s1 = wset s2; interrupts s1 = interrupts s2;
     wset_thread_ok (wset s2) (thr s2);
     \<And>t. thr s2 t = None \<Longrightarrow> thr s1 t = None;
     \<And>t x2 ln. thr s2 t = \<lfloor>(x2, ln)\<rfloor> \<Longrightarrow> \<exists>x1. thr s1 t = \<lfloor>(x1, ln)\<rfloor> \<and> t \<turnstile> (x1, shr s1) \<approx> (x2, shr s2) \<and> (wset s2 t = None \<or> x1 \<approx>w x2) \<rbrakk>
  \<Longrightarrow> s1 \<approx>m s2"
apply(auto simp add: mbisim_def tbisim_def)
   prefer 2
   apply(rule wset_thread_okI)
   apply(case_tac "thr s2 t")
    apply(auto dest!: wset_thread_okD)[1]
   apply fastforce
  apply(erule back_subst[where P=finite])
  apply(clarsimp simp add: dom_def fun_eq_iff simp del: not_None_eq)
  defer
  apply(rename_tac t)
  apply(case_tac [!] "thr s2 t")
by fastforce+

lemma mbisim_finite1:
  "s1 \<approx>m s2 \<Longrightarrow> finite (dom (thr s1))"
by(simp add: mbisim_def)

lemma mbisim_finite2:
  "s1 \<approx>m s2 \<Longrightarrow> finite (dom (thr s2))"
by(frule mbisim_finite1)(simp add: mbisim_dom_eq)

definition mta_bisim :: "('t \<times> ('l,'t,'x1,'m1,'w,'o) thread_action,
                       't \<times> ('l,'t,'x2,'m2,'w,'o) thread_action) bisim"
  ("_/ \<sim>T _" [50, 50] 60)
where "tta1 \<sim>T tta2 \<equiv> fst tta1 = fst tta2 \<and> snd tta1 \<sim>m snd tta2"

lemma mta_bisim_conv [simp]: "(t, ta1) \<sim>T (t', ta2) \<longleftrightarrow> t = t' \<and> ta1 \<sim>m ta2"
by(simp add: mta_bisim_def)

definition bisim_inv :: "bool" where
  "bisim_inv \<equiv> (\<forall>s1 ta1 s1' s2 t. t \<turnstile> s1 \<approx> s2 \<longrightarrow> t \<turnstile> s1 -1-ta1\<rightarrow> s1' \<longrightarrow> (\<exists>s2'. t \<turnstile> s1' \<approx> s2')) \<and>
               (\<forall>s2 ta2 s2' s1 t. t \<turnstile> s1 \<approx> s2 \<longrightarrow> t \<turnstile> s2 -2-ta2\<rightarrow> s2' \<longrightarrow> (\<exists>s1'. t \<turnstile> s1' \<approx> s2'))"

lemma bisim_invI:
  "\<lbrakk> \<And>s1 ta1 s1' s2 t. \<lbrakk> t \<turnstile> s1 \<approx> s2; t \<turnstile> s1 -1-ta1\<rightarrow> s1' \<rbrakk> \<Longrightarrow> \<exists>s2'. t \<turnstile> s1' \<approx> s2';
     \<And>s2 ta2 s2' s1 t. \<lbrakk> t \<turnstile> s1 \<approx> s2; t \<turnstile> s2 -2-ta2\<rightarrow> s2' \<rbrakk> \<Longrightarrow> \<exists>s1'. t \<turnstile> s1' \<approx> s2' \<rbrakk>
  \<Longrightarrow> bisim_inv"
by(auto simp add: bisim_inv_def)

lemma bisim_invD1:
  "\<lbrakk> bisim_inv; t \<turnstile> s1 \<approx> s2; t \<turnstile> s1 -1-ta1\<rightarrow> s1' \<rbrakk> \<Longrightarrow> \<exists>s2'. t \<turnstile> s1' \<approx> s2'"
unfolding bisim_inv_def by blast

lemma bisim_invD2:
  "\<lbrakk> bisim_inv; t \<turnstile> s1 \<approx> s2; t \<turnstile> s2 -2-ta2\<rightarrow> s2' \<rbrakk> \<Longrightarrow> \<exists>s1'. t \<turnstile> s1' \<approx> s2'"
unfolding bisim_inv_def by blast

lemma thread_oks_bisim_inv:
  "\<lbrakk> \<forall>t. ts1 t = None \<longleftrightarrow> ts2 t = None; list_all2 (nta_bisim bisim) tas1 tas2 \<rbrakk>
  \<Longrightarrow> thread_oks ts1 tas1 \<longleftrightarrow> thread_oks ts2 tas2"
proof(induct tas2 arbitrary: tas1 ts1 ts2)
  case Nil thus ?case by(simp)
next
  case (Cons ta2 TAS2 tas1 TS1 TS2)
  note IH = \<open>\<And>ts1 tas1 ts2. \<lbrakk> \<forall>t. ts1 t = None \<longleftrightarrow> ts2 t = None; list_all2 (nta_bisim bisim) tas1 TAS2 \<rbrakk>
             \<Longrightarrow> thread_oks ts1 tas1 \<longleftrightarrow> thread_oks ts2 TAS2\<close>
  note eqNone = \<open>\<forall>t. TS1 t = None \<longleftrightarrow> TS2 t = None\<close>[rule_format]
  hence fti: "free_thread_id TS1 = free_thread_id TS2" by(auto simp add: free_thread_id_def)
  from \<open>list_all2 (nta_bisim bisim) tas1 (ta2 # TAS2)\<close>
  obtain ta1 TAS1 where "tas1 = ta1 # TAS1" "nta_bisim bisim ta1 ta2" "list_all2 (nta_bisim bisim) TAS1 TAS2"
    by(auto simp add: list_all2_Cons2)
  moreover
  { fix t
    from \<open>nta_bisim bisim ta1 ta2\<close> have "redT_updT' TS1 ta1 t = None \<longleftrightarrow> redT_updT' TS2 ta2 t = None"
      by(cases ta1, auto split: if_split_asm simp add: eqNone) }
  ultimately have "thread_oks (redT_updT' TS1 ta1) TAS1 \<longleftrightarrow> thread_oks (redT_updT' TS2 ta2) TAS2"
    by -(rule IH, auto)
  moreover from \<open>nta_bisim bisim ta1 ta2\<close> fti have "thread_ok TS1 ta1 = thread_ok TS2 ta2" by(cases ta1, auto)
  ultimately show ?case using \<open>tas1 = ta1 # TAS1\<close> by auto
qed

lemma redT_updT_nta_bisim_inv:
  "\<lbrakk> nta_bisim bisim ta1 ta2; ts1 T = None \<longleftrightarrow> ts2 T = None \<rbrakk> \<Longrightarrow> redT_updT ts1 ta1 T = None \<longleftrightarrow> redT_updT ts2 ta2 T = None"
by(cases ta1, auto)

lemma redT_updTs_nta_bisim_inv:
  "\<lbrakk> list_all2 (nta_bisim bisim) tas1 tas2; ts1 T = None \<longleftrightarrow> ts2 T = None \<rbrakk>
  \<Longrightarrow> redT_updTs ts1 tas1 T = None \<longleftrightarrow> redT_updTs ts2 tas2 T = None"
proof(induct tas1 arbitrary: tas2 ts1 ts2)
  case Nil thus ?case by(simp)
next
  case (Cons TA1 TAS1 tas2 TS1 TS2)
  note IH = \<open>\<And>tas2 ts1 ts2. \<lbrakk>list_all2 (nta_bisim bisim) TAS1 tas2; (ts1 T = None) = (ts2 T = None)\<rbrakk>
            \<Longrightarrow> (redT_updTs ts1 TAS1 T = None) = (redT_updTs ts2 tas2 T = None)\<close>
  from \<open>list_all2 (nta_bisim bisim) (TA1 # TAS1) tas2\<close>
  obtain TA2 TAS2 where "tas2 = TA2 # TAS2" "nta_bisim bisim TA1 TA2" "list_all2 (nta_bisim bisim) TAS1 TAS2"
    by(auto simp add: list_all2_Cons1)
  from \<open>nta_bisim bisim TA1 TA2\<close> \<open>(TS1 T = None) = (TS2 T = None)\<close>
  have "redT_updT TS1 TA1 T = None \<longleftrightarrow> redT_updT TS2 TA2 T = None"
    by(rule redT_updT_nta_bisim_inv)
  with IH[OF \<open>list_all2 (nta_bisim bisim) TAS1 TAS2\<close>, of "redT_updT TS1 TA1" "redT_updT TS2 TA2"] \<open>tas2 = TA2 # TAS2\<close>
  show ?case by simp
qed

end

lemma tbisim_flip [flip_simps]:
  "FWbisimulation_base.tbisim (\<lambda>t. flip (bisim t)) (flip bisim_wait) w t ts2 m2 ts1 m1 =
   FWbisimulation_base.tbisim bisim bisim_wait w t ts1 m1 ts2 m2"
unfolding FWbisimulation_base.tbisim_def flip_simps by auto

lemma mbisim_flip [flip_simps]:
  "FWbisimulation_base.mbisim (\<lambda>t. flip (bisim t)) (flip bisim_wait) s2 s1 =
   FWbisimulation_base.mbisim bisim bisim_wait s1 s2"
apply(rule iffI)
 apply(frule FWbisimulation_base.mbisim_dom_eq)
 apply(frule FWbisimulation_base.mbisim_wset_thread_ok2)
 apply(fastforce simp add: FWbisimulation_base.mbisim_def flip_simps)
apply(frule FWbisimulation_base.mbisim_dom_eq)
apply(frule FWbisimulation_base.mbisim_wset_thread_ok2)
apply(fastforce simp add: FWbisimulation_base.mbisim_def flip_simps)
done

lemma mta_bisim_flip [flip_simps]:
  "FWbisimulation_base.mta_bisim (\<lambda>t. flip (bisim t)) = flip (FWbisimulation_base.mta_bisim bisim)"
by(auto simp add: fun_eq_iff flip_simps FWbisimulation_base.mta_bisim_def)

lemma flip_const [simp]: "flip (\<lambda>a b. c) = (\<lambda>a b. c)"
by(rule flip_def)

lemma mbisim_K_flip [flip_simps]:
  "FWbisimulation_base.mbisim (\<lambda>t. flip (bisim t)) (\<lambda>x1 x2. c) s1 s2 = 
   FWbisimulation_base.mbisim bisim (\<lambda>x1 x2. c) s2 s1"
using mbisim_flip[of bisim "\<lambda>x1 x2. c" s1 s2]
unfolding flip_const . 

context FWbisimulation_base begin

lemma mbisim_actions_ok_bisim_no_join_12:
  assumes mbisim: "mbisim s1 s2"
  and "collect_cond_actions \<lbrace>ta1\<rbrace>\<^bsub>c\<^esub> = {}"
  and "ta_bisim bisim ta1 ta2"
  and "r1.actions_ok s1 t ta1"
  shows "r2.actions_ok s2 t ta2"
using assms mbisim_thrNone_eq[OF mbisim]
by(auto simp add: ta_bisim_def mbisim_def intro: thread_oks_bisim_inv[THEN iffD1] r2.may_join_cond_action_oks)

lemma mbisim_actions_ok_bisim_no_join_21:
  "\<lbrakk> mbisim s1 s2; collect_cond_actions \<lbrace>ta2\<rbrace>\<^bsub>c\<^esub> = {}; ta_bisim bisim ta1 ta2; r2.actions_ok s2 t ta2 \<rbrakk>
  \<Longrightarrow> r1.actions_ok s1 t ta1"
using FWbisimulation_base.mbisim_actions_ok_bisim_no_join_12[where bisim="\<lambda>t. flip (bisim t)" and bisim_wait="flip bisim_wait"]
unfolding flip_simps .

lemma mbisim_actions_ok_bisim_no_join:
  "\<lbrakk> mbisim s1 s2; collect_cond_actions \<lbrace>ta1\<rbrace>\<^bsub>c\<^esub> = {}; ta_bisim bisim ta1 ta2 \<rbrakk> 
  \<Longrightarrow> r1.actions_ok s1 t ta1 = r2.actions_ok s2 t ta2"
apply(rule iffI)
 apply(erule (3) mbisim_actions_ok_bisim_no_join_12)
apply(erule mbisim_actions_ok_bisim_no_join_21[where ?ta2.0 = ta2])
  apply(simp add: ta_bisim_def)
apply assumption+
done

end

locale FWbisimulation_base_aux = FWbisimulation_base +
  r1: multithreaded final1 r1 convert_RA +
  r2: multithreaded final2 r2 convert_RA +
  constrains final1 :: "'x1 \<Rightarrow> bool"
  and r1 :: "('l,'t,'x1,'m1,'w, 'o) semantics"
  and final2 :: "'x2 \<Rightarrow> bool"
  and r2 :: "('l,'t,'x2,'m2,'w, 'o) semantics"
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and bisim :: "'t \<Rightarrow> ('x1 \<times> 'm1, 'x2 \<times> 'm2) bisim"
  and bisim_wait :: "('x1, 'x2) bisim"
begin

lemma FWbisimulation_base_aux_flip:
  "FWbisimulation_base_aux final2 r2 final1 r1"
by(unfold_locales)

end

lemma FWbisimulation_base_aux_flip_simps [flip_simps]:
  "FWbisimulation_base_aux final2 r2 final1 r1 = FWbisimulation_base_aux final1 r1 final2 r2"
by(blast intro: FWbisimulation_base_aux.FWbisimulation_base_aux_flip)

sublocale FWbisimulation_base_aux < mthr:
  bisimulation_final_base 
    r1.redT
    r2.redT
    mbisim
    mta_bisim
    r1.mfinal
    r2.mfinal
.

declare split_paired_Ex [simp del]

subsection \<open>Lifting for delay bisimulations\<close>

locale FWdelay_bisimulation_base =
  FWbisimulation_base _ _ _ r2 convert_RA bisim bisim_wait +
  r1: \<tau>multithreaded final1 r1 convert_RA \<tau>move1 +
  r2: \<tau>multithreaded final2 r2 convert_RA \<tau>move2 
  for r2 :: "('l,'t,'x2,'m2,'w,'o) semantics" ("_ \<turnstile> _ -2-_\<rightarrow> _" [50,0,0,50] 80)
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and bisim :: "'t \<Rightarrow> ('x1 \<times> 'm1, 'x2 \<times> 'm2) bisim" ("_ \<turnstile> _/ \<approx> _" [50, 50, 50] 60)
  and bisim_wait :: "('x1, 'x2) bisim" ("_/ \<approx>w _" [50, 50] 60)
  and \<tau>move1 :: "('l,'t,'x1,'m1,'w,'o) \<tau>moves"
  and \<tau>move2 :: "('l,'t,'x2,'m2,'w,'o) \<tau>moves"
begin

abbreviation \<tau>mred1 :: "('l,'t,'x1,'m1,'w) state \<Rightarrow> ('l,'t,'x1,'m1,'w) state \<Rightarrow> bool"
where "\<tau>mred1 \<equiv> r1.\<tau>mredT"

abbreviation \<tau>mred2 :: "('l,'t,'x2,'m2,'w) state \<Rightarrow> ('l,'t,'x2,'m2,'w) state \<Rightarrow> bool"
where "\<tau>mred2 \<equiv> r2.\<tau>mredT"

abbreviation m\<tau>move1 :: "(('l,'t,'x1,'m1,'w) state, 't \<times> ('l,'t,'x1,'m1,'w,'o) thread_action) trsys"
where "m\<tau>move1 \<equiv> r1.m\<tau>move"

abbreviation m\<tau>move2 :: "(('l,'t,'x2,'m2,'w) state, 't \<times> ('l,'t,'x2,'m2,'w,'o) thread_action) trsys"
where "m\<tau>move2 \<equiv> r2.m\<tau>move"

abbreviation \<tau>mRed1 :: "('l,'t,'x1,'m1,'w) state \<Rightarrow> ('l,'t,'x1,'m1,'w) state \<Rightarrow> bool"
where "\<tau>mRed1 \<equiv> \<tau>mred1^**"

abbreviation \<tau>mRed2 :: "('l,'t,'x2,'m2,'w) state \<Rightarrow> ('l,'t,'x2,'m2,'w) state \<Rightarrow> bool"
where "\<tau>mRed2 \<equiv> \<tau>mred2^**"

abbreviation \<tau>mtRed1 :: "('l,'t,'x1,'m1,'w) state \<Rightarrow> ('l,'t,'x1,'m1,'w) state \<Rightarrow> bool"
where "\<tau>mtRed1 \<equiv> \<tau>mred1^++"

abbreviation \<tau>mtRed2 :: "('l,'t,'x2,'m2,'w) state \<Rightarrow> ('l,'t,'x2,'m2,'w) state \<Rightarrow> bool"
where "\<tau>mtRed2 \<equiv> \<tau>mred2^++"

lemma bisim_inv_\<tau>s1_inv:
  assumes inv: "bisim_inv"
  and bisim: "t \<turnstile> s1 \<approx> s2"
  and red: "r1.silent_moves t s1 s1'"
  obtains s2' where "t \<turnstile> s1' \<approx> s2'"
proof(atomize_elim)
  from red bisim show "\<exists>s2'. t \<turnstile> s1' \<approx> s2'"
    by(induct rule: rtranclp_induct)(fastforce elim: bisim_invD1[OF inv])+
qed

lemma bisim_inv_\<tau>s2_inv:
  assumes inv: "bisim_inv"
  and bisim: "t \<turnstile> s1 \<approx> s2"
  and red: "r2.silent_moves t s2 s2'"
  obtains s1' where "t \<turnstile> s1' \<approx> s2'"
proof(atomize_elim)
  from red bisim show "\<exists>s1'. t \<turnstile> s1' \<approx> s2'"
    by(induct rule: rtranclp_induct)(fastforce elim: bisim_invD2[OF inv])+
qed

primrec activate_cond_action1 :: "('l,'t,'x1,'m1,'w) state \<Rightarrow> ('l,'t,'x2,'m2,'w) state \<Rightarrow> 
                                 't conditional_action \<Rightarrow> ('l,'t,'x1,'m1,'w) state"
where
  "activate_cond_action1 s1 s2 (Join t) =
   (case thr s1 t of None \<Rightarrow> s1
            | \<lfloor>(x1, ln1)\<rfloor> \<Rightarrow> (case thr s2 t of None \<Rightarrow> s1
                                     | \<lfloor>(x2, ln2)\<rfloor> \<Rightarrow> 
  if final2 x2 \<and> ln2 = no_wait_locks
  then redT_upd_\<epsilon> s1 t
                  (SOME x1'. r1.silent_moves t (x1, shr s1) (x1', shr s1) \<and> final1 x1' \<and> 
                             t \<turnstile> (x1', shr s1) \<approx> (x2, shr s2))
                  (shr s1)
  else s1))"
| "activate_cond_action1 s1 s2 Yield = s1"

primrec activate_cond_actions1 :: "('l,'t,'x1,'m1,'w) state \<Rightarrow> ('l,'t,'x2,'m2,'w) state
                                  \<Rightarrow> ('t conditional_action) list \<Rightarrow> ('l,'t,'x1,'m1,'w) state"
where
  "activate_cond_actions1 s1 s2 [] = s1"
| "activate_cond_actions1 s1 s2 (ct # cts) = activate_cond_actions1 (activate_cond_action1 s1 s2 ct) s2 cts"

primrec activate_cond_action2 :: "('l,'t,'x1,'m1,'w) state \<Rightarrow> ('l,'t,'x2,'m2,'w) state \<Rightarrow> 
                                 't conditional_action \<Rightarrow> ('l,'t,'x2,'m2,'w) state"
where
 "activate_cond_action2 s1 s2 (Join t) =
   (case thr s2 t of None \<Rightarrow> s2
            | \<lfloor>(x2, ln2)\<rfloor> \<Rightarrow> (case thr s1 t of None \<Rightarrow> s2
                                     | \<lfloor>(x1, ln1)\<rfloor> \<Rightarrow> 
  if final1 x1 \<and> ln1 = no_wait_locks
  then redT_upd_\<epsilon> s2 t
                  (SOME x2'. r2.silent_moves t (x2, shr s2) (x2', shr s2) \<and> final2 x2' \<and>
                             t \<turnstile> (x1, shr s1) \<approx> (x2', shr s2))
                  (shr s2)
  else s2))"
| "activate_cond_action2 s1 s2 Yield = s2"

primrec activate_cond_actions2 :: "('l,'t,'x1,'m1,'w) state \<Rightarrow> ('l,'t,'x2,'m2,'w) state \<Rightarrow>
                                  ('t conditional_action) list \<Rightarrow> ('l,'t,'x2,'m2,'w) state"
where
  "activate_cond_actions2 s1 s2 [] = s2"
| "activate_cond_actions2 s1 s2 (ct # cts) = activate_cond_actions2 s1 (activate_cond_action2 s1 s2 ct) cts"

end

lemma activate_cond_action1_flip [flip_simps]:
  "FWdelay_bisimulation_base.activate_cond_action1 final2 r2 final1 (\<lambda>t. flip (bisim t)) \<tau>move2 s2 s1 =
   FWdelay_bisimulation_base.activate_cond_action2 final1 final2 r2 bisim \<tau>move2 s1 s2"
apply(rule ext)
apply(case_tac x)
apply(simp_all only: FWdelay_bisimulation_base.activate_cond_action1.simps 
                     FWdelay_bisimulation_base.activate_cond_action2.simps flip_simps)
done

lemma activate_cond_actions1_flip [flip_simps]:
  "FWdelay_bisimulation_base.activate_cond_actions1 final2 r2 final1 (\<lambda>t. flip (bisim t)) \<tau>move2 s2 s1 =
   FWdelay_bisimulation_base.activate_cond_actions2 final1 final2 r2 bisim \<tau>move2 s1 s2"
  (is "?lhs = ?rhs")
proof(rule ext)
  fix xs
  show "?lhs xs = ?rhs xs"
    by(induct xs arbitrary: s2)
      (simp_all only: FWdelay_bisimulation_base.activate_cond_actions1.simps
                      FWdelay_bisimulation_base.activate_cond_actions2.simps flip_simps)
qed

lemma activate_cond_action2_flip [flip_simps]:
  "FWdelay_bisimulation_base.activate_cond_action2 final2 final1 r1 (\<lambda>t. flip (bisim t)) \<tau>move1 s2 s1 =
   FWdelay_bisimulation_base.activate_cond_action1 final1 r1 final2 bisim \<tau>move1 s1 s2"
apply(rule ext)
apply(case_tac x)
apply(simp_all only: FWdelay_bisimulation_base.activate_cond_action1.simps 
                     FWdelay_bisimulation_base.activate_cond_action2.simps flip_simps)
done

lemma activate_cond_actions2_flip [flip_simps]:
  "FWdelay_bisimulation_base.activate_cond_actions2 final2 final1 r1 (\<lambda>t. flip (bisim t)) \<tau>move1 s2 s1 =
   FWdelay_bisimulation_base.activate_cond_actions1 final1 r1 final2 bisim \<tau>move1 s1 s2"
  (is "?lhs = ?rhs")
proof(rule ext)
  fix xs
  show "?lhs xs = ?rhs xs"
    by(induct xs arbitrary: s1)
      (simp_all only: FWdelay_bisimulation_base.activate_cond_actions1.simps 
                      FWdelay_bisimulation_base.activate_cond_actions2.simps flip_simps)
qed
  
context FWdelay_bisimulation_base begin

lemma shr_activate_cond_action1 [simp]: "shr (activate_cond_action1 s1 s2 ct) = shr s1"
by(cases ct) simp_all

lemma shr_activate_cond_actions1 [simp]: "shr (activate_cond_actions1 s1 s2 cts) = shr s1"
by(induct cts arbitrary: s1) auto

lemma shr_activate_cond_action2 [simp]: "shr (activate_cond_action2 s1 s2 ct) = shr s2"
by(cases ct) simp_all

lemma shr_activate_cond_actions2 [simp]: "shr (activate_cond_actions2 s1 s2 cts) = shr s2"
by(induct cts arbitrary: s2) auto

lemma locks_activate_cond_action1 [simp]: "locks (activate_cond_action1 s1 s2 ct) = locks s1"
by(cases ct) simp_all

lemma locks_activate_cond_actions1 [simp]: "locks (activate_cond_actions1 s1 s2 cts) = locks s1"
by(induct cts arbitrary: s1) auto

lemma locks_activate_cond_action2 [simp]: "locks (activate_cond_action2 s1 s2 ct) = locks s2"
by(cases ct) simp_all

lemma locks_activate_cond_actions2 [simp]: "locks (activate_cond_actions2 s1 s2 cts) = locks s2"
by(induct cts arbitrary: s2) auto

lemma wset_activate_cond_action1 [simp]: "wset (activate_cond_action1 s1 s2 ct) = wset s1"
by(cases ct) simp_all

lemma wset_activate_cond_actions1 [simp]: "wset (activate_cond_actions1 s1 s2 cts) = wset s1"
by(induct cts arbitrary: s1) auto

lemma wset_activate_cond_action2 [simp]: "wset (activate_cond_action2 s1 s2 ct) = wset s2"
by(cases ct) simp_all

lemma wset_activate_cond_actions2 [simp]: "wset (activate_cond_actions2 s1 s2 cts) = wset s2"
by(induct cts arbitrary: s2) auto

lemma interrupts_activate_cond_action1 [simp]: "interrupts (activate_cond_action1 s1 s2 ct) = interrupts s1"
by(cases ct) simp_all

lemma interrupts_activate_cond_actions1 [simp]: "interrupts (activate_cond_actions1 s1 s2 cts) = interrupts s1"
by(induct cts arbitrary: s1) auto

lemma interrupts_activate_cond_action2 [simp]: "interrupts (activate_cond_action2 s1 s2 ct) = interrupts s2"
by(cases ct) simp_all

lemma interrupts_activate_cond_actions2 [simp]: "interrupts (activate_cond_actions2 s1 s2 cts) = interrupts s2"
by(induct cts arbitrary: s2) auto

end

locale FWdelay_bisimulation_lift_aux =
  FWdelay_bisimulation_base _ _ _ _ _ _ _ \<tau>move1 \<tau>move2 +
  r1: \<tau>multithreaded_wf final1 r1 convert_RA \<tau>move1 +
  r2: \<tau>multithreaded_wf final2 r2 convert_RA \<tau>move2 
  for \<tau>move1 :: "('l,'t,'x1,'m1,'w,'o) \<tau>moves"
  and \<tau>move2 :: "('l,'t,'x2,'m2,'w,'o) \<tau>moves"
begin

lemma FWdelay_bisimulation_lift_aux_flip:
  "FWdelay_bisimulation_lift_aux final2 r2 final1 r1 \<tau>move2 \<tau>move1"
by unfold_locales

end

lemma FWdelay_bisimulation_lift_aux_flip_simps [flip_simps]:
  "FWdelay_bisimulation_lift_aux final2 r2 final1 r1 \<tau>move2 \<tau>move1 =
   FWdelay_bisimulation_lift_aux final1 r1 final2 r2 \<tau>move1 \<tau>move2"
by(auto dest: FWdelay_bisimulation_lift_aux.FWdelay_bisimulation_lift_aux_flip simp only: flip_flip)

context FWdelay_bisimulation_lift_aux begin

lemma cond_actions_ok_\<tau>mred1_inv:
  assumes red: "\<tau>mred1 s1 s1'"
  and ct: "r1.cond_action_ok s1 t ct"
  shows "r1.cond_action_ok s1' t ct"
using ct
proof(cases ct)
  case (Join t')
  show ?thesis using red ct
  proof(cases "thr s1 t'")
    case None with red ct Join show ?thesis
      by(fastforce elim!: r1.mthr.silent_move.cases r1.redT.cases r1.m\<tau>move.cases rtrancl3p_cases 
                  dest: r1.silent_tl split: if_split_asm)
  next
    case (Some a) with red ct Join show ?thesis
      by(fastforce elim!: r1.mthr.silent_move.cases r1.redT.cases r1.m\<tau>move.cases rtrancl3p_cases
                  dest: r1.silent_tl r1.final_no_red split: if_split_asm simp add: redT_updWs_def)
  qed
next
  case Yield thus ?thesis by simp
qed

lemma cond_actions_ok_\<tau>mred2_inv:
  "\<lbrakk> \<tau>mred2 s2 s2'; r2.cond_action_ok s2 t ct \<rbrakk> \<Longrightarrow> r2.cond_action_ok s2' t ct"
using FWdelay_bisimulation_lift_aux.cond_actions_ok_\<tau>mred1_inv[OF FWdelay_bisimulation_lift_aux_flip] .

lemma cond_actions_ok_\<tau>mRed1_inv:
  "\<lbrakk> \<tau>mRed1 s1 s1'; r1.cond_action_ok s1 t ct \<rbrakk> \<Longrightarrow> r1.cond_action_ok s1' t ct"
by(induct rule: rtranclp_induct)(blast intro: cond_actions_ok_\<tau>mred1_inv)+

lemma cond_actions_ok_\<tau>mRed2_inv:
  "\<lbrakk> \<tau>mRed2 s2 s2'; r2.cond_action_ok s2 t ct \<rbrakk> \<Longrightarrow> r2.cond_action_ok s2' t ct"
by(rule FWdelay_bisimulation_lift_aux.cond_actions_ok_\<tau>mRed1_inv[OF FWdelay_bisimulation_lift_aux_flip])

end

locale FWdelay_bisimulation_lift =
  FWdelay_bisimulation_lift_aux +
  constrains final1 :: "'x1 \<Rightarrow> bool"
  and r1 :: "('l, 't, 'x1, 'm1, 'w, 'o) semantics"
  and final2 :: "'x2 \<Rightarrow> bool"
  and r2 :: "('l, 't, 'x2, 'm2, 'w, 'o) semantics"
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and bisim :: "'t \<Rightarrow> ('x1 \<times> 'm1, 'x2 \<times> 'm2) bisim"
  and bisim_wait :: "('x1, 'x2) bisim"
  and \<tau>move1 :: "('l, 't, 'x1, 'm1, 'w, 'o) \<tau>moves" 
  and \<tau>move2 :: "('l, 't, 'x2, 'm2, 'w, 'o) \<tau>moves"
  assumes \<tau>inv_locale: "\<tau>inv (r1 t) (r2 t) (bisim t) (ta_bisim bisim) \<tau>move1 \<tau>move2"

sublocale FWdelay_bisimulation_lift < \<tau>inv "r1 t" "r2 t" "bisim t" "ta_bisim bisim" \<tau>move1 \<tau>move2 for t
by(rule \<tau>inv_locale)

context FWdelay_bisimulation_lift begin

lemma FWdelay_bisimulation_lift_flip:
  "FWdelay_bisimulation_lift final2 r2 final1 r1 (\<lambda>t. flip (bisim t)) \<tau>move2 \<tau>move1"
apply(rule FWdelay_bisimulation_lift.intro)
 apply(rule FWdelay_bisimulation_lift_aux_flip)
apply(rule FWdelay_bisimulation_lift_axioms.intro)
apply(unfold flip_simps)
apply(unfold_locales)
done

end

lemma FWdelay_bisimulation_lift_flip_simps [flip_simps]:
  "FWdelay_bisimulation_lift final2 r2 final1 r1 (\<lambda>t. flip (bisim t)) \<tau>move2 \<tau>move1 =
   FWdelay_bisimulation_lift final1 r1 final2 r2 bisim \<tau>move1 \<tau>move2"
by(auto dest: FWdelay_bisimulation_lift.FWdelay_bisimulation_lift_flip simp only: flip_flip)

context FWdelay_bisimulation_lift begin

lemma \<tau>inv_lift: "\<tau>inv r1.redT r2.redT mbisim mta_bisim m\<tau>move1 m\<tau>move2"
proof
  fix s1 s2 tl1 s1' tl2 s2'
  assume "s1 \<approx>m s2" "s1' \<approx>m s2'" "tl1 \<sim>T tl2" "r1.redT s1 tl1 s1'" "r2.redT s2 tl2 s2'"
  moreover obtain t ta1 where tl1: "tl1 = (t, ta1)" by(cases tl1)
  moreover obtain t' ta2 where tl2: "tl2 = (t', ta2)" by(cases tl2)
  moreover obtain ls1 ts1 ws1 m1 is1 where s1: "s1 = (ls1, (ts1, m1), ws1, is1)" by(cases s1) fastforce
  moreover obtain ls2 ts2 ws2 m2 is2 where s2: "s2 = (ls2, (ts2, m2), ws2, is2)" by(cases s2) fastforce
  moreover obtain ls1' ts1' ws1' m1' is1' where s1': "s1' = (ls1', (ts1', m1'), ws1', is1')" by(cases s1') fastforce
  moreover obtain ls2' ts2' ws2' m2' is2' where s2': "s2' = (ls2', (ts2', m2'), ws2', is2')" by(cases s2') fastforce
  ultimately have mbisim: "(ls1, (ts1, m1), ws1, is1) \<approx>m (ls2, (ts2, m2), ws2, is2)"
    and mbisim': "(ls1', (ts1', m1'), ws1', is1') \<approx>m (ls2', (ts2', m2'), ws2', is2')"
    and mred1: "(ls1, (ts1, m1), ws1, is1) -1-t\<triangleright>ta1\<rightarrow> (ls1', (ts1', m1'), ws1', is1')"
    and mred2: "(ls2, (ts2, m2), ws2, is2) -2-t\<triangleright>ta2\<rightarrow> (ls2', (ts2', m2'), ws2', is2')"
    and tasim: "ta1 \<sim>m ta2" and tt': "t' = t" by simp_all
  from mbisim have ls: "ls1 = ls2" and ws: "ws1 = ws2" and "is": "is1 = is2"
    and tbisim: "\<And>t. tbisim (ws2 t = None) t (ts1 t) m1 (ts2 t) m2" by(simp_all add: mbisim_def)
  from mbisim' have ls': "ls1' = ls2'" and ws': "ws1' = ws2'" and is': "is1' = is2'"
    and tbisim': "\<And>t. tbisim (ws2' t = None) t (ts1' t) m1' (ts2' t) m2'" by(simp_all add: mbisim_def)
  from mred1 r1.redT_thread_not_disappear[OF mred1]
  obtain x1 ln1 x1' ln1' where tst1: "ts1 t = \<lfloor>(x1, ln1)\<rfloor>"
    and tst1': "ts1' t = \<lfloor>(x1', ln1')\<rfloor>"
    by(fastforce elim!: r1.redT.cases)
  from mred2 r2.redT_thread_not_disappear[OF mred2]
  obtain x2 ln2 x2' ln2' where tst2: "ts2 t = \<lfloor>(x2, ln2)\<rfloor>"
    and tst2': "ts2' t = \<lfloor>(x2', ln2')\<rfloor>" by(fastforce elim!: r2.redT.cases)
  from tbisim[of t] tst1 tst2 ws have bisim: "t \<turnstile> (x1, m1) \<approx> (x2, m2)"
    and ln: "ln1 = ln2" by(auto simp add: tbisim_def)
  from tbisim'[of t] tst1' tst2' have bisim': "t \<turnstile> (x1', m1') \<approx> (x2', m2')"
    and ln': "ln1' = ln2'" by(auto simp add: tbisim_def)
  show "m\<tau>move1 s1 tl1 s1' = m\<tau>move2 s2 tl2 s2'" unfolding s1 s2 s1' s2' tt' tl1 tl2
  proof -
    show "m\<tau>move1 (ls1, (ts1, m1), ws1, is1) (t, ta1) (ls1', (ts1', m1'), ws1', is1') =
          m\<tau>move2 (ls2, (ts2, m2), ws2, is2) (t, ta2) (ls2', (ts2', m2'), ws2', is2')"
      (is "?lhs = ?rhs")
    proof
      assume m\<tau>: ?lhs
      with tst1 tst1' obtain \<tau>1: "\<tau>move1 (x1, m1) ta1 (x1', m1')" 
        and ln1: "ln1 = no_wait_locks" by(fastforce elim!: r1.m\<tau>move.cases)
      from \<tau>1 have "ta1 = \<epsilon>" by(rule r1.silent_tl)
      with mred1 \<tau>1 tst1 tst1' ln1 have red1: "t \<turnstile> (x1, m1) -1-ta1\<rightarrow> (x1', m1')"
        by(auto elim!: r1.redT.cases rtrancl3p_cases)
      from tasim \<open>ta1 = \<epsilon>\<close> have [simp]: "ta2 = \<epsilon>" by(simp)
      with mred2 ln1 ln tst2 tst2' have red2: "t \<turnstile> (x2, m2) -2-\<epsilon>\<rightarrow> (x2', m2')"
        by(fastforce elim!: r2.redT.cases rtrancl3p_cases)
      from \<tau>1 \<tau>inv[OF bisim red1 red2] bisim' tasim
      have \<tau>2: "\<tau>move2 (x2, m2) \<epsilon> (x2', m2')" by simp
      with tst2 tst2' ln ln1 show ?rhs by -(rule r2.m\<tau>move.intros, auto)
    next
      assume m\<tau>: ?rhs
      with tst2 tst2' obtain \<tau>2: "\<tau>move2 (x2, m2) ta2 (x2', m2')" 
        and ln2: "ln2 = no_wait_locks" by(fastforce elim!: r2.m\<tau>move.cases)
      from \<tau>2 have "ta2 = \<epsilon>" by(rule r2.silent_tl)
      with mred2 \<tau>2 tst2 tst2' ln2 have red2: "t \<turnstile> (x2, m2) -2-ta2\<rightarrow> (x2', m2')"
        by(auto elim!: r2.redT.cases rtrancl3p_cases)
      from tasim \<open>ta2 = \<epsilon>\<close> have [simp]: "ta1 = \<epsilon>" by simp
      with mred1 ln2 ln tst1 tst1' have red1: "t \<turnstile> (x1, m1) -1-\<epsilon>\<rightarrow> (x1', m1')"
        by(fastforce elim!: r1.redT.cases rtrancl3p_cases)
      from \<tau>2 \<tau>inv[OF bisim red1 red2] bisim' tasim
      have \<tau>1: "\<tau>move1 (x1, m1) \<epsilon> (x1', m1')" by auto
      with tst1 tst1' ln ln2 show ?lhs unfolding \<open>ta1 = \<epsilon>\<close>
        by-(rule r1.m\<tau>move.intros, auto)
    qed
  qed
qed

end

sublocale FWdelay_bisimulation_lift < mthr: \<tau>inv r1.redT r2.redT mbisim mta_bisim m\<tau>move1 m\<tau>move2
by(rule \<tau>inv_lift)

locale FWdelay_bisimulation_final_base =
  FWdelay_bisimulation_lift_aux +
  constrains final1 :: "'x1 \<Rightarrow> bool"
  and r1 :: "('l,'t,'x1,'m1,'w, 'o) semantics"
  and final2 :: "'x2 \<Rightarrow> bool"
  and r2 :: "('l,'t,'x2,'m2,'w, 'o) semantics"
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and bisim :: "'t \<Rightarrow> ('x1 \<times> 'm1, 'x2 \<times> 'm2) bisim"
  and bisim_wait :: "('x1, 'x2) bisim"
  and \<tau>move1 :: "('l,'t,'x1,'m1,'w, 'o) \<tau>moves"
  and \<tau>move2 :: "('l,'t,'x2,'m2,'w, 'o) \<tau>moves"
  assumes delay_bisim_locale:
  "delay_bisimulation_final_base (r1 t) (r2 t) (bisim t) \<tau>move1 \<tau>move2 (\<lambda>(x1, m). final1 x1) (\<lambda>(x2, m). final2 x2)"

sublocale FWdelay_bisimulation_final_base <
  delay_bisimulation_final_base "r1 t" "r2 t" "bisim t" "ta_bisim bisim" \<tau>move1 \<tau>move2
                                "\<lambda>(x1, m). final1 x1" "\<lambda>(x2, m). final2 x2" 
  for t
by(rule delay_bisim_locale)

context FWdelay_bisimulation_final_base begin

lemma FWdelay_bisimulation_final_base_flip:
  "FWdelay_bisimulation_final_base final2 r2 final1 r1 (\<lambda>t. flip (bisim t)) \<tau>move2 \<tau>move1"
apply(rule FWdelay_bisimulation_final_base.intro)
 apply(rule FWdelay_bisimulation_lift_aux_flip)
apply(rule FWdelay_bisimulation_final_base_axioms.intro)
apply(rule delay_bisimulation_final_base_flip)
done

end

lemma FWdelay_bisimulation_final_base_flip_simps [flip_simps]:
  "FWdelay_bisimulation_final_base final2 r2 final1 r1 (\<lambda>t. flip (bisim t)) \<tau>move2 \<tau>move1 =
   FWdelay_bisimulation_final_base final1 r1 final2 r2 bisim \<tau>move1 \<tau>move2"
by(auto dest: FWdelay_bisimulation_final_base.FWdelay_bisimulation_final_base_flip simp only: flip_flip)

context FWdelay_bisimulation_final_base begin

lemma cond_actions_ok_bisim_ex_\<tau>1_inv:
  fixes ls ts1 m1 ws "is" ts2 m2 ct
  defines "s1' \<equiv> activate_cond_action1 (ls, (ts1, m1), ws, is) (ls, (ts2, m2), ws, is) ct"
  assumes mbisim: "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws t' = None) t' (ts1 t') m1 (ts2 t') m2"
  and ts1t: "ts1 t = Some xln"
  and ts2t: "ts2 t = Some xln'"
  and ct: "r2.cond_action_ok (ls, (ts2, m2), ws, is) t ct"
  shows "\<tau>mRed1 (ls, (ts1, m1), ws, is) s1'"
  and "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws t' = None) t' (thr s1' t') m1 (ts2 t') m2"
  and "r1.cond_action_ok s1' t ct"
  and "thr s1' t = Some xln"
proof -
  have "\<tau>mRed1 (ls, (ts1, m1), ws, is) s1' \<and>
        (\<forall>t'. t' \<noteq> t \<longrightarrow> tbisim (ws t' = None) t' (thr s1' t') m1 (ts2 t') m2) \<and>
        r1.cond_action_ok s1' t ct \<and> thr s1' t = \<lfloor>xln\<rfloor>"
    using ct
  proof(cases ct)
    case (Join t')
    show ?thesis 
    proof(cases "ts1 t'")
      case None
      with mbisim ts1t have "t \<noteq> t'" by auto
      moreover from None Join have "s1' = (ls, (ts1, m1), ws, is)" by(simp add: s1'_def)
      ultimately show ?thesis using mbisim Join ct None ts1t by(simp add: tbisim_def)
    next
      case (Some xln)
      moreover obtain x1 ln where "xln = (x1, ln)" by(cases xln)
      ultimately have ts1t': "ts1 t' = \<lfloor>(x1, ln)\<rfloor>" by simp
      from Join ct Some ts2t have tt': "t' \<noteq> t" by auto
      from mbisim[OF tt'] ts1t' obtain x2 where ts2t': "ts2 t' = \<lfloor>(x2, ln)\<rfloor>" 
        and bisim: "t' \<turnstile> (x1, m1) \<approx> (x2, m2)" by(auto simp add: tbisim_def)
      from ct Join ts2t' have final2: "final2 x2" and ln: "ln = no_wait_locks"
      and wst': "ws t' = None" by simp_all
      let ?x1' = "SOME x. r1.silent_moves t' (x1, m1) (x, m1) \<and> final1 x \<and> t' \<turnstile> (x, m1) \<approx> (x2, m2)"
      { from final2_simulation[OF bisim] final2 obtain x1' m1' 
          where "r1.silent_moves t' (x1, m1) (x1', m1')" and "t' \<turnstile> (x1', m1') \<approx> (x2, m2)"
          and "final1 x1'" by auto
        moreover hence "m1' = m1" using bisim by(auto dest: r1.red_rtrancl_\<tau>_heapD_inv)
        ultimately have "\<exists>x. r1.silent_moves t' (x1, m1) (x, m1) \<and> final1 x \<and> t' \<turnstile> (x, m1) \<approx> (x2, m2)"
          by blast }
      from someI_ex[OF this] have red1: "r1.silent_moves t' (x1, m1) (?x1', m1)"
        and final1: "final1 ?x1'" and bisim': "t' \<turnstile> (?x1', m1) \<approx> (x2, m2)" by blast+
      let ?S1' = "redT_upd_\<epsilon> (ls, (ts1, m1), ws, is) t' ?x1' m1"
      from r1.silent_moves_into_RedT_\<tau>_inv[where ?s="(ls, (ts1, m1), ws, is)" and t=t', simplified, OF red1]
        bisim ts1t' ln wst'
      have Red1: "\<tau>mRed1 (ls, (ts1, m1), ws, is) ?S1'" by auto
      moreover from Join ln ts1t' final1 wst' tt'
      have ct': "r1.cond_action_ok ?S1' t ct" by(auto intro: finfun_ext)
      { fix t''
        assume "t \<noteq> t''"
        with Join mbisim[OF this[symmetric]] bisim' ts1t' ts2t' wst' s1'_def
        have "tbisim (ws t'' = None) t'' (thr s1' t'') m1 (ts2 t'') m2"
          by(auto simp add: tbisim_def redT_updLns_def o_def finfun_Diag_const2) }
      moreover from Join ts1t' ts2t' final2 ln have "s1' = ?S1'" by(simp add: s1'_def)
      ultimately show ?thesis using Red1 ct' ts1t' tt' ts1t by(auto)
    qed
  next
    case Yield thus ?thesis using mbisim ts1t by(simp add: s1'_def)
  qed
  thus "\<tau>mRed1 (ls, (ts1, m1), ws, is) s1'"
    and "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws t' = None) t' (thr s1' t') m1 (ts2 t') m2"
    and "r1.cond_action_ok s1' t ct"
    and "thr s1' t = \<lfloor>xln\<rfloor>" by blast+
qed

lemma cond_actions_oks_bisim_ex_\<tau>1_inv:
  fixes ls ts1 m1 ws "is" ts2 m2 cts
  defines "s1' \<equiv> activate_cond_actions1 (ls, (ts1, m1), ws, is) (ls, (ts2, m2), ws, is) cts"
  assumes tbisim: "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws t' = None) t' (ts1 t') m1 (ts2 t') m2"
  and ts1t: "ts1 t = Some xln"
  and ts2t: "ts2 t = Some xln'"
  and ct: "r2.cond_action_oks (ls, (ts2, m2), ws, is) t cts"
  shows "\<tau>mRed1 (ls, (ts1, m1), ws, is) s1'" 
  and "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws t' = None) t' (thr s1' t') m1 (ts2 t') m2"
  and "r1.cond_action_oks s1' t cts"
  and "thr s1' t = Some xln"
using tbisim ts1t ct unfolding s1'_def
proof(induct cts arbitrary: ts1)
  case (Cons ct cts)
  note IH1 = \<open>\<And>ts1. \<lbrakk>\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws t' = None) t' (ts1 t') m1 (ts2 t') m2; ts1 t = \<lfloor>xln\<rfloor>;
                    r2.cond_action_oks (ls, (ts2, m2), ws, is) t cts\<rbrakk>
              \<Longrightarrow> \<tau>mred1\<^sup>*\<^sup>* (ls, (ts1, m1), ws, is) (activate_cond_actions1 (ls, (ts1, m1), ws, is) (ls, (ts2, m2), ws, is) cts)\<close>
  note IH2 = \<open>\<And>t' ts1. \<lbrakk>t' \<noteq> t; \<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws t' = None) t' (ts1 t') m1 (ts2 t') m2; ts1 t = \<lfloor>xln\<rfloor>;
                        r2.cond_action_oks (ls, (ts2, m2), ws, is) t cts\<rbrakk>
           \<Longrightarrow> tbisim (ws t' = None) t' (thr (activate_cond_actions1 (ls, (ts1, m1), ws, is) (ls, (ts2, m2), ws, is) cts) t') m1 (ts2 t') m2\<close>
  note IH3 = \<open>\<And>ts1. \<lbrakk>\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws t' = None) t' (ts1 t') m1 (ts2 t') m2; ts1 t = \<lfloor>xln\<rfloor>;
                     r2.cond_action_oks (ls, (ts2, m2), ws, is) t cts\<rbrakk>
              \<Longrightarrow> r1.cond_action_oks (activate_cond_actions1 (ls, (ts1, m1), ws, is) (ls, (ts2, m2), ws, is) cts) t cts\<close>
  note IH4 = \<open>\<And>ts1. \<lbrakk>\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws t' = None) t' (ts1 t') m1 (ts2 t') m2; ts1 t = \<lfloor>xln\<rfloor>;
                     r2.cond_action_oks (ls, (ts2, m2), ws, is) t cts\<rbrakk>
              \<Longrightarrow> thr (activate_cond_actions1 (ls, (ts1, m1), ws, is) (ls, (ts2, m2), ws, is) cts) t = \<lfloor>xln\<rfloor>\<close>
  { fix ts1
    assume tbisim: "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws t' = None) t' (ts1 t') m1 (ts2 t') m2"
      and ts1t: "ts1 t = \<lfloor>xln\<rfloor>"
      and ct: "r2.cond_action_oks (ls, (ts2, m2), ws, is) t (ct # cts)"
    from ct have 1: "r2.cond_action_ok (ls, (ts2, m2), ws, is) t ct"
      and 2: "r2.cond_action_oks (ls, (ts2, m2), ws, is) t cts" by auto
    let ?s1' = "activate_cond_action1 (ls, (ts1, m1), ws, is) (ls, (ts2, m2), ws, is) ct"
    from cond_actions_ok_bisim_ex_\<tau>1_inv[OF tbisim, OF _ ts1t ts2t 1]
    have tbisim': "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws t' = None) t' (thr ?s1' t') m1 (ts2 t') m2"
      and red: "\<tau>mRed1 (ls, (ts1, m1), ws, is) ?s1'" and ct': "r1.cond_action_ok ?s1' t ct" 
      and ts1't: "thr ?s1' t = \<lfloor>xln\<rfloor>" by blast+
    let ?s1'' = "activate_cond_actions1 ?s1' (ls, (ts2, m2), ws, is) cts"
    have "locks ?s1' = ls" "shr ?s1' = m1" "wset ?s1' = ws" "interrupts ?s1' = is" by simp_all
    hence s1': "(ls, (thr ?s1', m1), ws, is) = ?s1'" by(cases "?s1'") auto
    from IH1[OF tbisim', OF _ ts1't 2] s1' have red': "\<tau>mRed1 ?s1' ?s1''" by simp
    with red show "\<tau>mRed1 (ls, (ts1, m1), ws, is) (activate_cond_actions1 (ls, (ts1, m1), ws, is) (ls, (ts2, m2), ws, is) (ct # cts))"
      by auto
    { fix t'
      assume t't: "t' \<noteq> t"
      from IH2[OF t't tbisim', OF _ ts1't 2] s1'
      show "tbisim (ws t' = None) t' (thr (activate_cond_actions1 (ls, (ts1, m1), ws, is) (ls, (ts2, m2), ws, is) (ct # cts)) t') m1 (ts2 t') m2"
        by auto }
    from red' ct' have "r1.cond_action_ok ?s1'' t ct" by(rule cond_actions_ok_\<tau>mRed1_inv)
    with IH3[OF tbisim', OF _ ts1't 2] s1'
    show "r1.cond_action_oks (activate_cond_actions1 (ls, (ts1, m1), ws, is) (ls, (ts2, m2), ws, is) (ct # cts)) t (ct # cts)"
      by auto
    from ts1't IH4[OF tbisim', OF _ ts1't 2] s1'
    show "thr (activate_cond_actions1 (ls, (ts1, m1), ws, is) (ls, (ts2, m2), ws, is) (ct # cts)) t = \<lfloor>xln\<rfloor>" by auto }
qed(auto)

lemma cond_actions_ok_bisim_ex_\<tau>2_inv:
  fixes ls ts1 m1 "is" ws ts2 m2 ct
  defines "s2' \<equiv> activate_cond_action2 (ls, (ts1, m1), ws, is) (ls, (ts2, m2), ws, is) ct"
  assumes mbisim: "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws t' = None) t' (ts1 t') m1 (ts2 t') m2"
  and ts1t: "ts1 t = Some xln"
  and ts2t: "ts2 t = Some xln'"
  and ct: "r1.cond_action_ok (ls, (ts1, m1), ws, is) t ct"
  shows "\<tau>mRed2 (ls, (ts2, m2), ws, is) s2'"
  and "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws t' = None) t' (ts1 t') m1 (thr s2' t') m2"
  and "r2.cond_action_ok s2' t ct"
  and "thr s2' t = Some xln'"
unfolding s2'_def
by(blast intro: FWdelay_bisimulation_final_base.cond_actions_ok_bisim_ex_\<tau>1_inv[OF FWdelay_bisimulation_final_base_flip, where bisim_wait = "flip bisim_wait", unfolded flip_simps, OF mbisim _ _ ct, OF _ ts2t ts1t])+

lemma cond_actions_oks_bisim_ex_\<tau>2_inv:
  fixes ls ts1 m1 ws "is" ts2 m2 cts
  defines "s2' \<equiv> activate_cond_actions2 (ls, (ts1, m1), ws, is) (ls, (ts2, m2), ws, is) cts"
  assumes tbisim: "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws t' = None) t' (ts1 t') m1 (ts2 t') m2"
  and ts1t: "ts1 t = Some xln"
  and ts2t: "ts2 t = Some xln'"
  and ct: "r1.cond_action_oks (ls, (ts1, m1), ws, is) t cts"
  shows "\<tau>mRed2 (ls, (ts2, m2), ws, is) s2'"
  and "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws t' = None) t' (ts1 t') m1 (thr s2' t') m2"
  and "r2.cond_action_oks s2' t cts"
  and "thr s2' t = Some xln'"
unfolding s2'_def
by(blast intro: FWdelay_bisimulation_final_base.cond_actions_oks_bisim_ex_\<tau>1_inv[OF FWdelay_bisimulation_final_base_flip, where bisim_wait = "flip bisim_wait", unfolded flip_simps, OF tbisim _ _ ct, OF _ ts2t ts1t])+

lemma mfinal1_inv_simulation:
  assumes "s1 \<approx>m s2" 
  shows "\<exists>s2'. r2.mthr.silent_moves s2 s2' \<and> s1 \<approx>m s2' \<and> r1.final_threads s1 \<subseteq> r2.final_threads s2' \<and> shr s2' = shr s2"
proof -
  from \<open>s1 \<approx>m s2\<close> have "finite (dom (thr s1))" by(auto dest: mbisim_finite1)
  moreover have "r1.final_threads s1 \<subseteq> dom (thr s1)" by(auto simp add: r1.final_thread_def)
  ultimately have "finite (r1.final_threads s1)" by(blast intro: finite_subset)
  thus ?thesis using \<open>s1 \<approx>m s2\<close>
  proof(induct A\<equiv>"r1.final_threads s1" arbitrary: s1 s2 rule: finite_induct)
    case empty
    from \<open>{} = r1.final_threads s1\<close>[symmetric] have "\<forall>t. \<not> r1.final_thread s1 t" by(auto)
    with \<open>s1 \<approx>m s2\<close> show ?case by blast
  next
    case (insert t A)
    define s1' where "s1' = (locks s1, ((thr s1)(t := None), shr s1), wset s1, interrupts s1)"
    define s2' where "s2' = (locks s2, ((thr s2)(t := None), shr s2), wset s2, interrupts s2)"
    from \<open>t \<notin> A\<close> \<open>insert t A = r1.final_threads s1\<close> have "A = r1.final_threads s1'"
      unfolding s1'_def by(auto simp add: r1.final_thread_def r1.final_threads_def)
    moreover from \<open>insert t A = r1.final_threads s1\<close> have "r1.final_thread s1 t" by auto
    hence "wset s1 t = None" by(auto simp add: r1.final_thread_def)
    with \<open>s1 \<approx>m s2\<close> have "s1' \<approx>m s2'" unfolding s1'_def s2'_def
      by(auto simp add: mbisim_def intro: tbisim_NoneI intro!: wset_thread_okI dest: wset_thread_okD split: if_split_asm)
    ultimately have "\<exists>s2''. r2.mthr.silent_moves s2' s2'' \<and> s1' \<approx>m s2'' \<and> r1.final_threads s1' \<subseteq> r2.final_threads s2'' \<and> shr s2'' = shr s2'" by(rule insert)
    then obtain s2'' where reds: "r2.mthr.silent_moves s2' s2''" 
      and "s1' \<approx>m s2''" and fin: "\<And>t. r1.final_thread s1' t \<Longrightarrow> r2.final_thread s2'' t" and "shr s2'' = shr s2'" by blast
    have "thr s2' t = None" unfolding s2'_def by simp
    with \<open>r2.mthr.silent_moves s2' s2''\<close>
    have "r2.mthr.silent_moves (locks s2', (thr s2'(t \<mapsto> the (thr s2 t)), shr s2'), wset s2', interrupts s2')
      (locks s2'', (thr s2''(t \<mapsto> the (thr s2 t)), shr s2''), wset s2'', interrupts s2'')"
      by(rule r2.\<tau>mRedT_add_thread_inv)
    also let ?s2'' = "(locks s2, (thr s2''(t \<mapsto> the (thr s2 t)), shr s2), wset s2, interrupts s2)"
    from \<open>shr s2'' = shr s2'\<close> \<open>s1' \<approx>m s2''\<close> \<open>s1 \<approx>m s2\<close>
    have "(locks s2'', (thr s2''(t \<mapsto> the (thr s2 t)), shr s2''), wset s2'', interrupts s2'') = ?s2''"
      unfolding s2'_def s1'_def by(simp add: mbisim_def)
    also (back_subst) from \<open>s1 \<approx>m s2\<close> have "dom (thr s1) = dom (thr s2)" by(rule mbisim_dom_eq)
    with \<open>r1.final_thread s1 t\<close> have "t \<in> dom (thr s2)" by(auto simp add: r1.final_thread_def)
    then obtain x2 ln where tst2: "thr s2 t = \<lfloor>(x2, ln)\<rfloor>" by auto
    hence "(locks s2', (thr s2'(t \<mapsto> the (thr s2 t)), shr s2'), wset s2', interrupts s2') = s2"
      unfolding s2'_def by(cases s2)(auto intro!: ext)
    also from \<open>s1 \<approx>m s2\<close> tst2 obtain x1
      where tst1: "thr s1 t = \<lfloor>(x1, ln)\<rfloor>"
      and bisim: "t \<turnstile> (x1, shr s1) \<approx> (x2, shr s2)" by(auto dest: mbisim_thrD2)
    from \<open>shr s2'' = shr s2'\<close> have "shr ?s2'' = shr s2" by(simp add: s2'_def)
    from \<open>r1.final_thread s1 t\<close> tst1
    have final: "final1 x1" "ln = no_wait_locks" "wset s1 t = None" by(auto simp add: r1.final_thread_def)
    with final1_simulation[OF bisim] \<open>shr ?s2'' = shr s2\<close> obtain x2' m2'
      where red: "r2.silent_moves t (x2, shr ?s2'') (x2', m2')"
      and bisim': "t \<turnstile> (x1, shr s1) \<approx> (x2', m2')" and "final2 x2'" by auto
    from \<open>wset s1 t = None\<close> \<open>s1 \<approx>m s2\<close> have "wset s2 t = None" by(simp add: mbisim_def) 
    with bisim r2.silent_moves_into_RedT_\<tau>_inv[OF red] tst2 \<open>ln = no_wait_locks\<close>
    have "r2.mthr.silent_moves ?s2'' (redT_upd_\<epsilon> ?s2'' t x2' m2')" unfolding s2'_def by auto
    also (rtranclp_trans)
    from bisim r2.red_rtrancl_\<tau>_heapD_inv[OF red] have "m2' = shr s2" by auto
    hence "s1 \<approx>m (redT_upd_\<epsilon> ?s2'' t x2' m2')"
      using \<open>s1' \<approx>m s2''\<close> \<open>s1 \<approx>m s2\<close> tst1 tst2 \<open>shr ?s2'' = shr s2\<close> bisim' \<open>shr s2'' = shr s2'\<close> \<open>wset s2 t = None\<close>
      unfolding s1'_def s2'_def by(auto simp add: mbisim_def redT_updLns_def split: if_split_asm intro: tbisim_SomeI)
    moreover { 
      fix t'
      assume "r1.final_thread s1 t'"
      with fin[of t'] \<open>final2 x2'\<close> tst2 \<open>ln = no_wait_locks\<close> \<open>wset s2 t = None\<close> \<open>s1' \<approx>m s2''\<close> \<open>s1 \<approx>m s2\<close>
      have "r2.final_thread (redT_upd_\<epsilon> ?s2'' t x2' m2') t'" unfolding s1'_def
        by(fastforce split: if_split_asm simp add: r2.final_thread_def r1.final_thread_def redT_updLns_def finfun_Diag_const2 o_def mbisim_def)
    }
    moreover have "shr (redT_upd_\<epsilon> ?s2'' t x2' m2') = shr s2" using \<open>m2' = shr s2\<close> by simp
    ultimately show ?case by blast
  qed
qed

lemma mfinal2_inv_simulation:
  "s1 \<approx>m s2 \<Longrightarrow> \<exists>s1'. r1.mthr.silent_moves s1 s1' \<and> s1' \<approx>m s2 \<and> r2.final_threads s2 \<subseteq> r1.final_threads s1' \<and> shr s1' = shr s1"
using FWdelay_bisimulation_final_base.mfinal1_inv_simulation[OF FWdelay_bisimulation_final_base_flip, where bisim_wait="flip bisim_wait"]
by(unfold flip_simps)

lemma mfinal1_simulation:
  assumes "s1 \<approx>m s2" and "r1.mfinal s1"
  shows "\<exists>s2'. r2.mthr.silent_moves s2 s2' \<and> s1 \<approx>m s2' \<and> r2.mfinal s2' \<and> shr s2' = shr s2"
proof -
  from mfinal1_inv_simulation[OF \<open>s1 \<approx>m s2\<close>]
  obtain s2' where 1: "r2.mthr.silent_moves s2 s2'" "s1 \<approx>m s2'" "shr s2' = shr s2"
    and fin: "\<And>t. r1.final_thread s1 t \<Longrightarrow> r2.final_thread s2' t" by blast
  have "r2.mfinal s2'"
  proof(rule r2.mfinalI)
    fix t x2 ln
    assume "thr s2' t = \<lfloor>(x2, ln)\<rfloor>"
    with \<open>s1 \<approx>m s2'\<close> obtain x1 where "thr s1 t = \<lfloor>(x1, ln)\<rfloor>" "t \<turnstile> (x1, shr s1) \<approx> (x2, shr s2')"
      by(auto dest: mbisim_thrD2)
    from \<open>thr s1 t = \<lfloor>(x1, ln)\<rfloor>\<close> \<open>r1.mfinal s1\<close> have "r1.final_thread s1 t"
      by(auto elim!: r1.mfinalE simp add: r1.final_thread_def)
    hence "r2.final_thread s2' t" by(rule fin)
    thus "final2 x2 \<and> ln = no_wait_locks \<and> wset s2' t = None"
      using \<open>thr s2' t = \<lfloor>(x2, ln)\<rfloor>\<close> by(auto simp add: r2.final_thread_def)
  qed
  with 1 show ?thesis by blast
qed
    
lemma mfinal2_simulation:
  "\<lbrakk> s1 \<approx>m s2; r2.mfinal s2 \<rbrakk>
  \<Longrightarrow> \<exists>s1'. r1.mthr.silent_moves s1 s1' \<and> s1' \<approx>m s2 \<and> r1.mfinal s1' \<and> shr s1' = shr s1"
using FWdelay_bisimulation_final_base.mfinal1_simulation[OF FWdelay_bisimulation_final_base_flip, where bisim_wait = "flip bisim_wait"]
by(unfold flip_simps)

end

locale FWdelay_bisimulation_obs =
  FWdelay_bisimulation_final_base _ _ _ _ _ _ _ \<tau>move1 \<tau>move2
  for \<tau>move1 :: "('l,'t,'x1,'m1,'w, 'o) \<tau>moves"
  and \<tau>move2 :: "('l,'t,'x2,'m2,'w, 'o) \<tau>moves" +
  assumes delay_bisimulation_obs_locale: "delay_bisimulation_obs (r1 t) (r2 t) (bisim t) (ta_bisim bisim) \<tau>move1 \<tau>move2"
  and bisim_inv_red_other:
   "\<lbrakk> t' \<turnstile> (x, m1) \<approx> (xx, m2); t \<turnstile> (x1, m1) \<approx> (x2, m2); 
      r1.silent_moves t (x1, m1) (x1', m1);
      t \<turnstile> (x1', m1) -1-ta1\<rightarrow> (x1'', m1'); \<not> \<tau>move1 (x1', m1) ta1 (x1'', m1');
      r2.silent_moves t (x2, m2) (x2', m2);
      t \<turnstile> (x2', m2) -2-ta2\<rightarrow> (x2'', m2'); \<not> \<tau>move2 (x2', m2) ta2 (x2'', m2');
      t \<turnstile> (x1'', m1') \<approx> (x2'', m2'); ta_bisim bisim ta1 ta2 \<rbrakk>
   \<Longrightarrow> t' \<turnstile> (x, m1') \<approx> (xx, m2')"
  and bisim_waitI:
   "\<lbrakk> t \<turnstile> (x1, m1) \<approx> (x2, m2); r1.silent_moves t (x1, m1) (x1', m1);
      t \<turnstile> (x1', m1) -1-ta1\<rightarrow> (x1'', m1'); \<not> \<tau>move1 (x1', m1) ta1 (x1'', m1');
      r2.silent_moves t (x2, m2) (x2', m2);
      t \<turnstile> (x2', m2) -2-ta2\<rightarrow> (x2'', m2'); \<not> \<tau>move2 (x2', m2) ta2 (x2'', m2');
      t \<turnstile> (x1'', m1') \<approx> (x2'', m2'); ta_bisim bisim ta1 ta2;
      Suspend w \<in> set \<lbrace>ta1\<rbrace>\<^bsub>w\<^esub>; Suspend w \<in> set \<lbrace>ta2\<rbrace>\<^bsub>w\<^esub> \<rbrakk>
   \<Longrightarrow> x1'' \<approx>w x2''"
  and simulation_Wakeup1:
    "\<lbrakk> t \<turnstile> (x1, m1) \<approx> (x2, m2); x1 \<approx>w x2; t \<turnstile> (x1, m1) -1-ta1\<rightarrow> (x1', m1'); Notified \<in> set \<lbrace>ta1\<rbrace>\<^bsub>w\<^esub> \<or> WokenUp \<in> set \<lbrace>ta1\<rbrace>\<^bsub>w\<^esub> \<rbrakk>
    \<Longrightarrow> \<exists>ta2 x2' m2'. t \<turnstile> (x2, m2) -2-ta2\<rightarrow> (x2', m2') \<and> t \<turnstile> (x1', m1') \<approx> (x2', m2') \<and> ta_bisim bisim ta1 ta2"
  and simulation_Wakeup2:
    "\<lbrakk> t \<turnstile> (x1, m1) \<approx> (x2, m2); x1 \<approx>w x2; t \<turnstile> (x2, m2) -2-ta2\<rightarrow> (x2', m2'); Notified \<in> set \<lbrace>ta2\<rbrace>\<^bsub>w\<^esub> \<or> WokenUp \<in> set \<lbrace>ta2\<rbrace>\<^bsub>w\<^esub> \<rbrakk>
    \<Longrightarrow> \<exists>ta1 x1' m1'. t \<turnstile> (x1, m1) -1-ta1\<rightarrow> (x1', m1') \<and> t \<turnstile> (x1', m1') \<approx> (x2', m2') \<and> ta_bisim bisim ta1 ta2"
  and ex_final1_conv_ex_final2:
    "(\<exists>x1. final1 x1) \<longleftrightarrow> (\<exists>x2. final2 x2)"

sublocale FWdelay_bisimulation_obs <
  delay_bisimulation_obs "r1 t" "r2 t" "bisim t" "ta_bisim bisim" \<tau>move1 \<tau>move2 for t
by(rule delay_bisimulation_obs_locale)

context FWdelay_bisimulation_obs begin

lemma FWdelay_bisimulation_obs_flip:
  "FWdelay_bisimulation_obs final2 r2 final1 r1 (\<lambda>t. flip (bisim t)) (flip bisim_wait) \<tau>move2 \<tau>move1"
apply(rule FWdelay_bisimulation_obs.intro)
 apply(rule FWdelay_bisimulation_final_base_flip)
apply(rule FWdelay_bisimulation_obs_axioms.intro)
     apply(unfold flip_simps)
     apply(rule delay_bisimulation_obs_axioms)
    apply(erule (9) bisim_inv_red_other)
   apply(erule (10) bisim_waitI)
  apply(erule (3) simulation_Wakeup2)
 apply(erule (3) simulation_Wakeup1)
apply(rule ex_final1_conv_ex_final2[symmetric])
done

end

lemma FWdelay_bisimulation_obs_flip_simps [flip_simps]:
  "FWdelay_bisimulation_obs final2 r2 final1 r1 (\<lambda>t. flip (bisim t)) (flip bisim_wait) \<tau>move2 \<tau>move1 = 
   FWdelay_bisimulation_obs final1 r1 final2 r2 bisim bisim_wait \<tau>move1 \<tau>move2"
by(auto dest: FWdelay_bisimulation_obs.FWdelay_bisimulation_obs_flip simp only: flip_flip)

context FWdelay_bisimulation_obs begin

lemma mbisim_redT_upd:
  fixes s1 t ta1 x1' m1' s2 ta2 x2' m2' ln
  assumes s1': "redT_upd s1 t ta1 x1' m1' s1'"
  and s2': "redT_upd s2 t ta2 x2' m2' s2'"
  and [simp]: "wset s1 = wset s2" "locks s1 = locks s2" 
  and wset: "wset s1' = wset s2'"
  and interrupts: "interrupts s1' = interrupts s2'"
  and fin1: "finite (dom (thr s1))"
  and wsts: "wset_thread_ok (wset s1) (thr s1)"
  and tst: "thr s1 t = \<lfloor>(x1, ln)\<rfloor>"
  and tst': "thr s2 t = \<lfloor>(x2, ln)\<rfloor>"
  and aoe1: "r1.actions_ok s1 t ta1"
  and aoe2: "r2.actions_ok s2 t ta2"
  and tasim: "ta_bisim bisim ta1 ta2"
  and bisim': "t \<turnstile> (x1', m1') \<approx> (x2', m2')"
  and bisimw: "wset s1' t = None \<or> x1' \<approx>w x2'"
  and \<tau>red1: "r1.silent_moves t (x1'', shr s1) (x1, shr s1)"
  and red1: "t \<turnstile> (x1, shr s1) -1-ta1\<rightarrow> (x1', m1')"
  and \<tau>red2: "r2.silent_moves t (x2'', shr s2) (x2, shr s2)"
  and red2: "t \<turnstile> (x2, shr s2) -2-ta2\<rightarrow> (x2', m2')"
  and bisim: "t \<turnstile> (x1'', shr s1) \<approx> (x2'', shr s2)"
  and \<tau>1: "\<not> \<tau>move1 (x1, shr s1) ta1 (x1', m1')"
  and \<tau>2: "\<not> \<tau>move2 (x2, shr s2) ta2 (x2', m2')"
  and tbisim: "\<And>t'. t \<noteq> t' \<Longrightarrow> tbisim (wset s1 t' = None) t' (thr s1 t') (shr s1) (thr s2 t') (shr s2)"
  shows "s1' \<approx>m s2'"
proof(rule mbisimI)
  from fin1 s1' show "finite (dom (thr s1'))"
    by(auto simp add: redT_updTs_finite_dom_inv)
next
  from tasim s1' s2' show "locks s1' = locks s2'"
    by(auto simp add: redT_updLs_def o_def ta_bisim_def)
next
  from wset show "wset s1' = wset s2'" .
next
  from interrupts show "interrupts s1' = interrupts s2'" .
next
  from wsts s1' s2' wset show "wset_thread_ok (wset s1') (thr s1')"
    by(fastforce intro!: wset_thread_okI split: if_split_asm dest: redT_updTs_None wset_thread_okD redT_updWs_None_implies_None)
next
  fix T
  assume "thr s1' T = None"
  moreover with tst s1' have [simp]: "t \<noteq> T" by auto
  from tbisim[OF this] have "(thr s1 T = None) = (thr s2 T = None)"
    by(auto simp add: tbisim_def)
  hence "(redT_updTs (thr s1) \<lbrace>ta1\<rbrace>\<^bsub>t\<^esub> T = None) = (redT_updTs (thr s2) \<lbrace>ta2\<rbrace>\<^bsub>t\<^esub> T = None)"
    using tasim by -(rule redT_updTs_nta_bisim_inv, simp_all add: ta_bisim_def)
  ultimately show "thr s2' T = None" using s2' s1' by(auto split: if_split_asm)
next
  fix T X1 LN
  assume tsT: "thr s1' T = \<lfloor>(X1, LN)\<rfloor>"
  show "\<exists>x2. thr s2' T = \<lfloor>(x2, LN)\<rfloor> \<and> T \<turnstile> (X1, shr s1') \<approx> (x2, shr s2') \<and> (wset s2' T = None \<or> X1 \<approx>w x2)"
  proof(cases "thr s1 T")
    case None
    with tst have "t \<noteq> T" by auto
    with tbisim[OF this] None have tsT': "thr s2 T = None" by(simp add: tbisim_def)
    from None \<open>t \<noteq> T\<close> tsT aoe1 s1' obtain M1
      where ntset: "NewThread T X1 M1 \<in> set \<lbrace>ta1\<rbrace>\<^bsub>t\<^esub>" and [simp]: "LN = no_wait_locks"
      by(auto dest!: redT_updTs_new_thread)
    from ntset obtain tas1 tas1' where "\<lbrace>ta1\<rbrace>\<^bsub>t\<^esub> = tas1 @ NewThread T X1 M1 # tas1'"
      by(auto simp add: in_set_conv_decomp)
    with tasim obtain tas2 X2 M2 tas2' where "\<lbrace>ta2\<rbrace>\<^bsub>t\<^esub> = tas2 @ NewThread T X2 M2 # tas2'"
      "length tas2 = length tas2" "length tas1' = length tas2'" and Bisim: "T \<turnstile> (X1, M1) \<approx> (X2, M2)"
      by(auto simp add: list_all2_append1 list_all2_Cons1 ta_bisim_def)
    hence ntset': "NewThread T X2 M2 \<in> set \<lbrace>ta2\<rbrace>\<^bsub>t\<^esub>" by auto
    with tsT' \<open>t \<noteq> T\<close> aoe2 s2' have "thr s2' T = \<lfloor>(X2, no_wait_locks)\<rfloor>"
      by(auto intro: redT_updTs_new_thread_ts)
    moreover from ntset' red2 have "m2' = M2" by(auto dest: r2.new_thread_memory)
    moreover from ntset red1 have "m1' = M1"
      by(auto dest: r1.new_thread_memory)
    moreover from wsts None have "wset s1 T = None" by(rule wset_thread_okD)
    ultimately show ?thesis using Bisim \<open>t \<noteq> T\<close> s1' s2'
      by(auto simp add: redT_updWs_None_implies_None)
  next
    case (Some a)
    show ?thesis
    proof(cases "t = T")
      case True
      with tst tsT s1' have [simp]: "X1 = x1'" "LN = redT_updLns (locks s1) t ln \<lbrace>ta1\<rbrace>\<^bsub>l\<^esub>" by(auto)
      show ?thesis using True bisim' bisimw tasim tst tst' s1' s2' wset
        by(auto simp add: redT_updLns_def ta_bisim_def)
    next
      case False
      with Some aoe1 tsT s1' have "thr s1 T = \<lfloor>(X1, LN)\<rfloor>" by(auto dest: redT_updTs_Some)
      with tbisim[OF False] obtain X2 
        where tsT': "thr s2 T = \<lfloor>(X2, LN)\<rfloor>" and Bisim: "T \<turnstile> (X1, shr s1) \<approx> (X2, shr s2)"
        and bisimw: "wset s1 T = None \<or> X1 \<approx>w X2" by(auto simp add: tbisim_def)
      with aoe2 False s2' have tsT': "thr s2' T = \<lfloor>(X2, LN)\<rfloor>" by(auto simp add: redT_updTs_Some)
      moreover from Bisim bisim \<tau>red1 red1 \<tau>1 \<tau>red2 red2 \<tau>2 bisim' tasim
      have "T \<turnstile> (X1, m1') \<approx> (X2, m2')" by(rule bisim_inv_red_other)
      ultimately show ?thesis using False bisimw s1' s2'
        by(auto simp add: redT_updWs_None_implies_None)
    qed
  qed
qed

theorem mbisim_simulation1:
  assumes mbisim: "mbisim s1 s2" and "\<not> m\<tau>move1 s1 tl1 s1'" "r1.redT s1 tl1 s1'"
  shows "\<exists>s2' s2'' tl2. r2.mthr.silent_moves s2 s2' \<and> r2.redT s2' tl2 s2'' \<and>
                        \<not> m\<tau>move2 s2' tl2 s2'' \<and> mbisim s1' s2'' \<and> mta_bisim tl1 tl2"
proof -
  from assms obtain t ta1 where tl1 [simp]: "tl1 = (t, ta1)" and redT: "s1 -1-t\<triangleright>ta1\<rightarrow> s1'"
    and m\<tau>: "\<not> m\<tau>move1 s1 (t, ta1) s1'" by(cases tl1) fastforce
  obtain ls1 ts1 m1 ws1 is1 where [simp]: "s1 = (ls1, (ts1, m1), ws1, is1)" by(cases s1) fastforce
  obtain ls1' ts1' m1' ws1' is1' where [simp]: "s1' = (ls1', (ts1', m1'), ws1', is1')" by(cases s1') fastforce
  obtain ls2 ts2 m2 ws2 is2 where [simp]: "s2 = (ls2, (ts2, m2), ws2, is2)" by(cases s2) fastforce
  from mbisim have [simp]: "ls2 = ls1" "ws2 = ws1" "is2 = is1" "finite (dom ts1)" by(auto simp add: mbisim_def)
  from redT show ?thesis
  proof cases
    case (redT_normal x1 x1' M1')
    hence red: "t \<turnstile> (x1, m1) -1-ta1\<rightarrow> (x1', M1')" 
      and tst: "ts1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>"
      and aoe: "r1.actions_ok s1 t ta1"
      and s1': "redT_upd s1 t ta1 x1' M1' s1'" by auto
    from mbisim tst obtain x2 where tst': "ts2 t = \<lfloor>(x2, no_wait_locks)\<rfloor>"
      and bisim: "t \<turnstile> (x1, m1) \<approx> (x2, m2)" by(auto dest: mbisim_thrD1)
    from m\<tau> have \<tau>: "\<not> \<tau>move1 (x1, m1) ta1 (x1', M1')"
    proof(rule contrapos_nn)
      assume \<tau>: "\<tau>move1 (x1, m1) ta1 (x1', M1')"
      moreover hence [simp]: "ta1 = \<epsilon>" by(rule r1.silent_tl)
      moreover have [simp]: "M1' = m1" by(rule r1.\<tau>move_heap[OF red \<tau>, symmetric])
      ultimately show "m\<tau>move1 s1 (t, ta1) s1'" using s1' tst s1'
        by(auto simp add: redT_updLs_def o_def intro: r1.m\<tau>move.intros elim: rtrancl3p_cases)
    qed
    show ?thesis
    proof(cases "ws1 t")
      case None
      note wst = this
      from simulation1[OF bisim red \<tau>] obtain x2' M2' x2'' M2'' ta2
        where red21: "r2.silent_moves t (x2, m2) (x2', M2')"
        and red22: "t \<turnstile> (x2', M2') -2-ta2\<rightarrow> (x2'', M2'')" and \<tau>2: "\<not> \<tau>move2 (x2', M2') ta2 (x2'', M2'')"
        and bisim': "t \<turnstile> (x1', M1') \<approx> (x2'', M2'')"
        and tasim: "ta_bisim bisim ta1 ta2" by auto
      let ?s2' = "redT_upd_\<epsilon> s2 t x2' M2'"
      let ?S2' = "activate_cond_actions2 s1 ?s2' \<lbrace>ta2\<rbrace>\<^bsub>c\<^esub>"
      let ?s2'' = "(redT_updLs (locks ?S2') t \<lbrace>ta2\<rbrace>\<^bsub>l\<^esub>, ((redT_updTs (thr ?S2') \<lbrace>ta2\<rbrace>\<^bsub>t\<^esub>)(t \<mapsto> (x2'', redT_updLns (locks ?S2') t (snd (the (thr ?S2' t))) \<lbrace>ta2\<rbrace>\<^bsub>l\<^esub>)), M2''), wset s1', interrupts s1')"
      from red21 tst' wst bisim have "\<tau>mRed2 s2 ?s2'"
        by -(rule r2.silent_moves_into_RedT_\<tau>_inv, auto)
      moreover from red21 bisim have [simp]: "M2' = m2" by(auto dest: r2.red_rtrancl_\<tau>_heapD_inv)
      from tasim have [simp]: "\<lbrace> ta1 \<rbrace>\<^bsub>l\<^esub> = \<lbrace> ta2 \<rbrace>\<^bsub>l\<^esub>" "\<lbrace> ta1 \<rbrace>\<^bsub>w\<^esub> = \<lbrace> ta2 \<rbrace>\<^bsub>w\<^esub>" "\<lbrace> ta1 \<rbrace>\<^bsub>c\<^esub> = \<lbrace> ta2 \<rbrace>\<^bsub>c\<^esub>" "\<lbrace> ta1 \<rbrace>\<^bsub>i\<^esub> = \<lbrace> ta2 \<rbrace>\<^bsub>i\<^esub>"
        and nta: "list_all2 (nta_bisim bisim) \<lbrace> ta1 \<rbrace>\<^bsub>t\<^esub> \<lbrace> ta2 \<rbrace>\<^bsub>t\<^esub>" by(auto simp add: ta_bisim_def)
      from mbisim have tbisim: "\<And>t. tbisim (ws1 t = None) t (ts1 t) m1 (ts2 t) m2" by(simp add: mbisim_def)
      hence tbisim': "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws1 t' = None) t' (ts1 t') m1 (thr ?s2' t') m2" by(auto)
      from aoe have cao1: "r1.cond_action_oks (ls1, (ts1, m1), ws1, is1) t \<lbrace>ta2\<rbrace>\<^bsub>c\<^esub>" by auto
      from tst' have "thr ?s2' t = \<lfloor>(x2', no_wait_locks)\<rfloor>" by(auto simp add: redT_updLns_def o_def finfun_Diag_const2)
      from cond_actions_oks_bisim_ex_\<tau>2_inv[OF tbisim', OF _ tst this cao1]
      have red21': "\<tau>mRed2 ?s2' ?S2'" and tbisim'': "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws1 t' = None) t' (ts1 t') m1 (thr ?S2' t') m2"
        and cao2: "r2.cond_action_oks ?S2' t \<lbrace>ta2\<rbrace>\<^bsub>c\<^esub>" and tst'': "thr ?S2' t = \<lfloor>(x2', no_wait_locks)\<rfloor>"
        by(auto simp del: fun_upd_apply)
      note red21' also (rtranclp_trans)
      from tbisim'' tst'' tst have "\<forall>t'. ts1 t' = None \<longleftrightarrow> thr ?S2' t' = None" by(force simp add: tbisim_def)
      from aoe thread_oks_bisim_inv[OF this nta] have "thread_oks (thr ?S2') \<lbrace>ta2\<rbrace>\<^bsub>t\<^esub>" by simp
      with cao2 aoe have aoe': "r2.actions_ok ?S2' t ta2" by auto
      with red22 tst'' s1' have "?S2' -2-t\<triangleright>ta2\<rightarrow> ?s2''"
        by -(rule r2.redT.redT_normal, auto)
      moreover
      from \<tau>2 have "\<not> m\<tau>move2 ?S2' (t, ta2) ?s2''"
      proof(rule contrapos_nn)
        assume m\<tau>: "m\<tau>move2 ?S2' (t, ta2) ?s2''"
        thus "\<tau>move2 (x2', M2') ta2 (x2'', M2'')" using tst'' tst'
          by cases auto
      qed
      moreover
      { 
        note s1'
        moreover have "redT_upd ?S2' t ta2 x2'' M2'' ?s2''" using s1' by auto
        moreover have "wset s1 = wset ?S2'" "locks s1 = locks ?S2'" by simp_all
        moreover have "wset s1' = wset ?s2''" by simp
        moreover have "interrupts s1' = interrupts ?s2''" by simp
        moreover have "finite (dom (thr s1))" by simp
        moreover from mbisim have "wset_thread_ok (wset s1) (thr s1)" by(simp add: mbisim_def) 
        moreover from tst have "thr s1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>" by simp
        moreover note tst'' aoe aoe' tasim bisim'
        moreover have "wset s1' t = None \<or> x1' \<approx>w x2''"
        proof(cases "wset s1' t")
          case None thus ?thesis ..
        next
          case (Some w)
          with wst s1' obtain w' where Suspend1: "Suspend w' \<in> set \<lbrace>ta1\<rbrace>\<^bsub>w\<^esub>"
            by(auto dest: redT_updWs_None_SomeD)
          with tasim have Suspend2: "Suspend w' \<in> set \<lbrace>ta2\<rbrace>\<^bsub>w\<^esub>" by(simp add: ta_bisim_def)
          from bisim_waitI[OF bisim rtranclp.rtrancl_refl red \<tau> _ _ _ bisim' tasim Suspend1 this, of x2'] red21 red22 \<tau>2
          have "x1' \<approx>w x2''" by auto
          thus ?thesis ..
        qed
        moreover note rtranclp.rtrancl_refl
        moreover from red have "t \<turnstile> (x1, shr s1) -1-ta1\<rightarrow> (x1', M1')" by simp
        moreover from red21 have "r2.silent_moves t (x2, shr ?S2') (x2', shr ?S2')" by simp
        moreover from red22 have "t \<turnstile> (x2', shr ?S2') -2-ta2\<rightarrow> (x2'', M2'')" by simp
        moreover from bisim have "t \<turnstile> (x1, shr s1) \<approx> (x2, shr ?S2')" by simp
        moreover from \<tau> have "\<not> \<tau>move1 (x1, shr s1) ta1 (x1', M1')" by simp
        moreover from \<tau>2 have "\<not> \<tau>move2 (x2', shr ?S2') ta2 (x2'', M2'')" by simp
        moreover from tbisim'' 
        have "\<And>t'. t \<noteq> t' \<Longrightarrow> tbisim (wset s1 t' = None) t' (thr s1 t') (shr s1) (thr ?S2' t') (shr ?S2')" 
          by simp
        ultimately have "mbisim s1' ?s2''" by(rule mbisim_redT_upd)
        }
      ultimately show ?thesis using tasim unfolding tl1 s1' by fastforce
    next
      case (Some w)
      with mbisim tst tst' have "x1 \<approx>w x2"
        by(auto dest: mbisim_thrD1)
      from aoe Some have wakeup: "Notified \<in> set \<lbrace>ta1\<rbrace>\<^bsub>w\<^esub> \<or> WokenUp \<in> set \<lbrace>ta1\<rbrace>\<^bsub>w\<^esub>"
        by(auto simp add: wset_actions_ok_def split: if_split_asm)
      from simulation_Wakeup1[OF bisim \<open>x1 \<approx>w x2\<close> red this]
      obtain ta2 x2' m2' where red2: "t \<turnstile> (x2, m2) -2-ta2\<rightarrow> (x2', m2')"
        and bisim': "t \<turnstile> (x1', M1') \<approx> (x2', m2')"
        and tasim: "ta1 \<sim>m ta2" by auto

      let ?S2' = "activate_cond_actions2 s1 s2 \<lbrace>ta2\<rbrace>\<^bsub>c\<^esub>"

      let ?s2' = "(redT_updLs (locks ?S2') t \<lbrace>ta2\<rbrace>\<^bsub>l\<^esub>, ((redT_updTs (thr ?S2') \<lbrace>ta2\<rbrace>\<^bsub>t\<^esub>)(t \<mapsto> (x2', redT_updLns (locks ?S2') t (snd (the (thr ?S2' t))) \<lbrace>ta2\<rbrace>\<^bsub>l\<^esub>)), m2'), wset s1', interrupts s1')"

      from tasim have [simp]: "\<lbrace> ta1 \<rbrace>\<^bsub>l\<^esub> = \<lbrace> ta2 \<rbrace>\<^bsub>l\<^esub>" "\<lbrace> ta1 \<rbrace>\<^bsub>w\<^esub> = \<lbrace> ta2 \<rbrace>\<^bsub>w\<^esub>" "\<lbrace> ta1 \<rbrace>\<^bsub>c\<^esub> = \<lbrace> ta2 \<rbrace>\<^bsub>c\<^esub>" "\<lbrace> ta1 \<rbrace>\<^bsub>i\<^esub> = \<lbrace> ta2 \<rbrace>\<^bsub>i\<^esub>"
        and nta: "list_all2 (nta_bisim bisim) \<lbrace> ta1 \<rbrace>\<^bsub>t\<^esub> \<lbrace> ta2 \<rbrace>\<^bsub>t\<^esub>" by(auto simp add: ta_bisim_def)
      from mbisim have tbisim: "\<And>t. tbisim (ws1 t = None) t (ts1 t) m1 (ts2 t) m2" by(simp add: mbisim_def)
      hence tbisim': "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws1 t' = None) t' (ts1 t') m1 (thr s2 t') m2" by(auto)
      from aoe have cao1: "r1.cond_action_oks (ls1, (ts1, m1), ws1, is1) t \<lbrace>ta2\<rbrace>\<^bsub>c\<^esub>" by auto
      from tst' have "thr s2 t = \<lfloor>(x2, no_wait_locks)\<rfloor>"
        by(auto simp add: redT_updLns_def o_def finfun_Diag_const2)
      from cond_actions_oks_bisim_ex_\<tau>2_inv[OF tbisim', OF _ tst this cao1]
      have red21': "\<tau>mRed2 s2 ?S2'" and tbisim'': "\<And>t'. t' \<noteq> t \<Longrightarrow> tbisim (ws1 t' = None) t' (ts1 t') m1 (thr ?S2' t') m2"
        and cao2: "r2.cond_action_oks ?S2' t \<lbrace>ta2\<rbrace>\<^bsub>c\<^esub>" and tst'': "thr ?S2' t = \<lfloor>(x2, no_wait_locks)\<rfloor>"
        by(auto simp del: fun_upd_apply)
      note red21' moreover
      from tbisim'' tst'' tst have "\<forall>t'. ts1 t' = None \<longleftrightarrow> thr ?S2' t' = None" by(force simp add: tbisim_def)
      from aoe thread_oks_bisim_inv[OF this nta] have "thread_oks (thr ?S2') \<lbrace>ta2\<rbrace>\<^bsub>t\<^esub>" by simp
      with cao2 aoe have aoe': "r2.actions_ok ?S2' t ta2" by auto
      with red2 tst'' s1' tasim have "?S2' -2-t\<triangleright>ta2\<rightarrow> ?s2'"
        by -(rule r2.redT_normal, auto simp add: ta_bisim_def)
      moreover from wakeup tasim
      have \<tau>2: "\<not> \<tau>move2 (x2, m2) ta2 (x2', m2')" by(auto dest: r2.silent_tl)
      hence "\<not> m\<tau>move2 ?S2' (t, ta2) ?s2'"
      proof(rule contrapos_nn)
        assume m\<tau>: "m\<tau>move2 ?S2' (t, ta2) ?s2'"
        thus "\<tau>move2 (x2, m2) ta2 (x2', m2')" using tst'' tst'
          by cases auto
      qed
      moreover {
        note s1'
        moreover have "redT_upd ?S2' t ta2 x2' m2' ?s2'" using s1' tasim by(auto simp add: ta_bisim_def)
        moreover have "wset s1 = wset ?S2'" "locks s1 = locks ?S2'" by simp_all
        moreover have "wset s1' = wset ?s2'" by simp
        moreover have "interrupts s1' = interrupts ?s2'" by simp
        moreover have "finite (dom (thr s1))" by simp
        moreover from mbisim have "wset_thread_ok (wset s1) (thr s1)" by(rule mbisim_wset_thread_ok1)
        moreover from tst have "thr s1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>" by simp
        moreover from tst'' have "thr ?S2' t = \<lfloor>(x2, no_wait_locks)\<rfloor>" by simp
        moreover note aoe aoe' tasim bisim'
        moreover have "wset s1' t = None \<or> x1' \<approx>w x2'"
        proof(cases "wset s1' t")
          case None thus ?thesis ..
        next
          case (Some w')
          with redT_updWs_WokenUp_SuspendD[OF _ wakeup, of t "wset s1" "wset s1'" w'] s1'
          obtain w' where Suspend1: "Suspend w' \<in> set \<lbrace>ta1\<rbrace>\<^bsub>w\<^esub>" by(auto)
          with tasim have Suspend2: "Suspend w' \<in> set \<lbrace>ta2\<rbrace>\<^bsub>w\<^esub>" by(simp add: ta_bisim_def)
          with bisim rtranclp.rtrancl_refl red \<tau> rtranclp.rtrancl_refl red2 \<tau>2 bisim' tasim Suspend1
          have "x1' \<approx>w x2'" by(rule bisim_waitI)
          thus ?thesis ..
        qed
        moreover note rtranclp.rtrancl_refl
        moreover from red have "t \<turnstile> (x1, shr s1) -1-ta1\<rightarrow> (x1', M1')" by simp
        moreover note rtranclp.rtrancl_refl
        moreover from red2 have "t \<turnstile> (x2, shr ?S2') -2-ta2\<rightarrow> (x2', m2')" by simp
        moreover from bisim have "t \<turnstile> (x1, shr s1) \<approx> (x2, shr ?S2')" by simp
        moreover from \<tau> have "\<not> \<tau>move1 (x1, shr s1) ta1 (x1', M1')" by simp
        moreover from \<tau>2 have "\<not> \<tau>move2 (x2, shr ?S2') ta2 (x2', m2')" by simp
        moreover from tbisim'' have "\<And>t'. t \<noteq> t' \<Longrightarrow> tbisim (wset s1 t' = None) t' (thr s1 t') (shr s1) (thr ?S2' t') (shr ?S2')" by simp
        ultimately have "s1' \<approx>m ?s2'" by(rule mbisim_redT_upd) }
      moreover from tasim have "tl1 \<sim>T (t, ta2)" by simp
      ultimately show ?thesis unfolding s1' by blast
    qed
  next
    case (redT_acquire x1 n ln)
    hence [simp]: "ta1 = (K$ [], [], [], [], [], convert_RA ln)"
      and tst: "thr s1 t = \<lfloor>(x1, ln)\<rfloor>" and wst: "\<not> waiting (wset s1 t)"
      and maa: "may_acquire_all (locks s1) t ln" and ln: "0 < ln $ n"
      and s1': "s1' = (acquire_all ls1 t ln, (ts1(t \<mapsto> (x1, no_wait_locks)), m1), ws1, is1)" by auto
    from tst mbisim obtain x2 where tst': "ts2 t = \<lfloor>(x2, ln)\<rfloor>" 
      and bisim: "t \<turnstile> (x1, m1) \<approx> (x2, m2)" by(auto dest: mbisim_thrD1)
    let ?s2' = "(acquire_all ls1 t ln, (ts2(t \<mapsto> (x2, no_wait_locks)), m2), ws1, is1)"
    from tst' wst maa ln have "s2 -2-t\<triangleright>(K$ [], [], [], [], [], convert_RA ln)\<rightarrow> ?s2'"
      by-(rule r2.redT.redT_acquire, auto)
    moreover from tst' ln have "\<not> m\<tau>move2 s2 (t, (K$ [], [], [], [], [], convert_RA ln)) ?s2'"
      by(auto simp add: acquire_all_def fun_eq_iff elim!: r2.m\<tau>move.cases)
    moreover have "mbisim s1' ?s2'"
    proof(rule mbisimI)
      from s1' show "locks s1' = locks ?s2'" by auto
    next
      from s1' show "wset s1' = wset ?s2'" by auto
    next
      from s1' show "interrupts s1' = interrupts ?s2'" by auto
    next
      fix t' assume "thr s1' t' = None"
      with s1' have "thr s1 t' = None" by(auto split: if_split_asm)
      with mbisim_thrNone_eq[OF mbisim] have "ts2 t' = None" by simp
      with tst' show "thr ?s2' t' = None" by auto
    next
      fix t' X1 LN
      assume ts't: "thr s1' t' = \<lfloor>(X1, LN)\<rfloor>"
      show "\<exists>x2. thr ?s2' t' = \<lfloor>(x2, LN)\<rfloor> \<and> t' \<turnstile> (X1, shr s1') \<approx> (x2, shr ?s2') \<and> (wset ?s2' t' = None \<or> X1 \<approx>w x2)"
      proof(cases "t' = t")
        case True
        with s1' tst ts't have [simp]: "X1 = x1" "LN = no_wait_locks" by simp_all
        with mbisim_thrD1[OF mbisim tst] bisim tst tst' True s1' wst show ?thesis by(auto)
      next
        case False
        with ts't s1' have "ts1 t' = \<lfloor>(X1, LN)\<rfloor>" by auto
        with mbisim obtain X2 where "ts2 t' = \<lfloor>(X2, LN)\<rfloor>" "t' \<turnstile> (X1, m1) \<approx> (X2, m2)" "wset ?s2' t' = None \<or> X1 \<approx>w X2"
          by(auto dest: mbisim_thrD1)
        with False s1' show ?thesis by auto
      qed
    next
      from s1' show "finite (dom (thr s1'))" by auto
    next
      from mbisim_wset_thread_ok1[OF mbisim]
      show "wset_thread_ok (wset s1') (thr s1')" using s1' by(auto intro: wset_thread_ok_upd)
    qed
    moreover have "(t, K$ [], [], [], [], [], convert_RA ln) \<sim>T (t, K$ [], [], [], [], [], convert_RA ln)"
      by(simp add: ta_bisim_def)
    ultimately show ?thesis by fastforce
  qed
qed

theorem mbisim_simulation2:
  "\<lbrakk> mbisim s1 s2; r2.redT s2 tl2 s2'; \<not> m\<tau>move2 s2 tl2 s2' \<rbrakk>
  \<Longrightarrow> \<exists>s1' s1'' tl1. r1.mthr.silent_moves s1 s1' \<and> r1.redT s1' tl1 s1'' \<and> \<not> m\<tau>move1 s1' tl1 s1'' \<and>
                    mbisim s1'' s2' \<and> mta_bisim tl1 tl2"
using FWdelay_bisimulation_obs.mbisim_simulation1[OF FWdelay_bisimulation_obs_flip]
unfolding flip_simps .

end

locale FWdelay_bisimulation_diverge =
  FWdelay_bisimulation_obs _ _ _ _ _ _ _ \<tau>move1 \<tau>move2
  for \<tau>move1 :: "('l,'t,'x1,'m1,'w,'o) \<tau>moves"
  and \<tau>move2 :: "('l,'t,'x2,'m2,'w,'o) \<tau>moves" +
  assumes delay_bisimulation_diverge_locale: "delay_bisimulation_diverge (r1 t) (r2 t) (bisim t) (ta_bisim bisim) \<tau>move1 \<tau>move2"

sublocale FWdelay_bisimulation_diverge <
  delay_bisimulation_diverge "r1 t" "r2 t" "bisim t" "ta_bisim bisim" \<tau>move1 \<tau>move2 for t
by(rule delay_bisimulation_diverge_locale)

context FWdelay_bisimulation_diverge begin

lemma FWdelay_bisimulation_diverge_flip:
  "FWdelay_bisimulation_diverge final2 r2 final1 r1 (\<lambda>t. flip (bisim t)) (flip bisim_wait) \<tau>move2 \<tau>move1"
apply(rule FWdelay_bisimulation_diverge.intro)
 apply(rule FWdelay_bisimulation_obs_flip)
apply(rule FWdelay_bisimulation_diverge_axioms.intro)
apply(unfold flip_simps)
apply(rule delay_bisimulation_diverge_axioms)
done

end

lemma FWdelay_bisimulation_diverge_flip_simps [flip_simps]:
  "FWdelay_bisimulation_diverge final2 r2 final1 r1 (\<lambda>t. flip (bisim t)) (flip bisim_wait) \<tau>move2 \<tau>move1 = 
   FWdelay_bisimulation_diverge final1 r1 final2 r2 bisim bisim_wait \<tau>move1 \<tau>move2"
by(auto dest: FWdelay_bisimulation_diverge.FWdelay_bisimulation_diverge_flip simp only: flip_flip)

context FWdelay_bisimulation_diverge begin

lemma bisim_inv1:
  assumes bisim: "t \<turnstile> s1 \<approx> s2"
  and red: "t \<turnstile> s1 -1-ta1\<rightarrow> s1'"
  obtains s2' where "t \<turnstile> s1' \<approx> s2'"
proof(atomize_elim)
  show "\<exists>s2'. t \<turnstile> s1' \<approx> s2'"
  proof(cases "\<tau>move1 s1 ta1 s1'")
    case True
    with red have "r1.silent_move t s1 s1'" by auto
    from simulation_silent1[OF bisim this]
    show ?thesis by auto
  next
    case False
    from simulation1[OF bisim red False] show ?thesis by auto
  qed
qed

lemma bisim_inv2:
  assumes "t \<turnstile> s1 \<approx> s2" "t \<turnstile> s2 -2-ta2\<rightarrow> s2'"
  obtains s1' where "t \<turnstile> s1' \<approx> s2'"
using assms FWdelay_bisimulation_diverge.bisim_inv1[OF FWdelay_bisimulation_diverge_flip]
unfolding flip_simps by blast

lemma bisim_inv: "bisim_inv"
by(blast intro!: bisim_invI elim: bisim_inv1 bisim_inv2)

lemma bisim_inv_\<tau>s1:
  assumes "t \<turnstile> s1 \<approx> s2" and "r1.silent_moves t s1 s1'"
  obtains s2' where "t \<turnstile> s1' \<approx> s2'"
using assms by(rule bisim_inv_\<tau>s1_inv[OF bisim_inv])

lemma bisim_inv_\<tau>s2:
  assumes "t \<turnstile> s1 \<approx> s2" and "r2.silent_moves t s2 s2'"
  obtains s1' where "t \<turnstile> s1' \<approx> s2'"
using assms by(rule bisim_inv_\<tau>s2_inv[OF bisim_inv])

lemma red1_rtrancl_\<tau>_into_RedT_\<tau>:
  assumes "r1.silent_moves t (x1, shr s1) (x1', m1')" "t \<turnstile> (x1, shr s1) \<approx> (x2, m2)"
  and "thr s1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>" "wset s1 t = None"
  shows "\<tau>mRed1 s1 (redT_upd_\<epsilon> s1 t x1' m1')"
using assms by(blast intro: r1.silent_moves_into_RedT_\<tau>_inv)

lemma red2_rtrancl_\<tau>_into_RedT_\<tau>:
  assumes "r2.silent_moves t (x2, shr s2) (x2', m2')"
  and "t \<turnstile> (x1, m1) \<approx> (x2, shr s2)" "thr s2 t = \<lfloor>(x2, no_wait_locks)\<rfloor>" "wset s2 t = None"
  shows "\<tau>mRed2 s2 (redT_upd_\<epsilon> s2 t x2' m2')"
using assms by(blast intro: r2.silent_moves_into_RedT_\<tau>_inv)

lemma red1_rtrancl_\<tau>_heapD:
  "\<lbrakk> r1.silent_moves t s1 s1'; t \<turnstile> s1 \<approx> s2 \<rbrakk> \<Longrightarrow> snd s1' = snd s1"
by(blast intro: r1.red_rtrancl_\<tau>_heapD_inv)

lemma red2_rtrancl_\<tau>_heapD:
  "\<lbrakk> r2.silent_moves t s2 s2'; t \<turnstile> s1 \<approx> s2 \<rbrakk> \<Longrightarrow> snd s2' = snd s2"
by(blast intro: r2.red_rtrancl_\<tau>_heapD_inv)

lemma mbisim_simulation_silent1:
  assumes m\<tau>': "r1.mthr.silent_move s1 s1'" and mbisim: "s1 \<approx>m s2"
  shows "\<exists>s2'. r2.mthr.silent_moves s2 s2' \<and> s1' \<approx>m s2'"
proof -
  from m\<tau>' obtain tl1 where m\<tau>: "m\<tau>move1 s1 tl1 s1'" "r1.redT s1 tl1 s1'" by auto
  obtain ls1 ts1 m1 ws1 is1 where [simp]: "s1 = (ls1, (ts1, m1), ws1, is1)" by(cases s1) fastforce
  obtain ls1' ts1' m1' ws1' is1' where [simp]: "s1' = (ls1', (ts1', m1'), ws1', is1')" by(cases s1') fastforce
  obtain ls2 ts2 m2 ws2 is2 where [simp]: "s2 = (ls2, (ts2, m2), ws2, is2)" by(cases s2) fastforce
  from m\<tau> obtain t where "tl1 = (t, \<epsilon>)" by(auto elim!: r1.m\<tau>move.cases dest: r1.silent_tl)
  with m\<tau> have m\<tau>: "m\<tau>move1 s1 (t, \<epsilon>) s1'" and redT1: "s1 -1-t\<triangleright>\<epsilon>\<rightarrow> s1'" by simp_all
  from m\<tau> obtain x x' ln' where tst: "ts1 t = \<lfloor>(x, no_wait_locks)\<rfloor>"
    and ts't: "ts1' t = \<lfloor>(x', ln')\<rfloor>" and \<tau>: "\<tau>move1 (x, m1) \<epsilon> (x', m1')"
    by(fastforce elim: r1.m\<tau>move.cases)
  from mbisim have [simp]: "ls2 = ls1" "ws2 = ws1" "is2 = is1" "finite (dom ts1)" by(auto simp add: mbisim_def)
  from redT1 show ?thesis
  proof cases
    case (redT_normal x1 x1' M')
    with tst ts't have [simp]: "x = x1" "x' = x1'"
      and red: "t \<turnstile> (x1, m1) -1-\<epsilon>\<rightarrow> (x1', M')"
      and tst: "thr s1 t = \<lfloor>(x1, no_wait_locks)\<rfloor>"
      and wst: "wset s1 t = None"
      and s1': "redT_upd s1 t \<epsilon> x1' M' s1'" by(auto)
    from s1' tst have [simp]: "ls1' = ls1" "ws1' = ws1" "is1' = is1" "M' = m1'" "ts1' = ts1(t \<mapsto> (x1', no_wait_locks))"
      by(auto simp add: redT_updLs_def redT_updLns_def o_def redT_updWs_def elim!: rtrancl3p_cases)
    from mbisim tst obtain x2 where tst': "ts2 t = \<lfloor>(x2, no_wait_locks)\<rfloor>"
      and bisim: "t \<turnstile> (x1, m1) \<approx> (x2, m2)" by(auto dest: mbisim_thrD1)
    from r1.\<tau>move_heap[OF red] \<tau> have [simp]: "m1 = M'" by simp
    from red \<tau> have "r1.silent_move t (x1, m1) (x1', M')" by auto
    from simulation_silent1[OF bisim this]
    obtain x2' m2' where red: "r2.silent_moves t (x2, m2) (x2', m2')"
      and bisim': "t \<turnstile> (x1', m1) \<approx> (x2', m2')" by auto
    from red bisim have [simp]: "m2' = m2" 
      by(auto dest: red2_rtrancl_\<tau>_heapD)
    let ?s2' = "redT_upd_\<epsilon> s2 t x2' m2'"
    from red tst' wst bisim have "\<tau>mRed2 s2 ?s2'"
      by -(rule red2_rtrancl_\<tau>_into_RedT_\<tau>, auto)
    moreover have "mbisim s1' ?s2'"
    proof(rule mbisimI)
      show "locks s1' = locks ?s2'" "wset s1' = wset ?s2'" "interrupts s1' = interrupts ?s2'" by auto
    next
      fix t'
      assume "thr s1' t' = None"
      hence "ts1 t' = None" by(auto split: if_split_asm)
      with mbisim_thrNone_eq[OF mbisim] have "ts2 t' = None" by simp
      with tst' show "thr ?s2' t' = None" by auto
    next
      fix t' X1 LN
      assume ts't': "thr s1' t' = \<lfloor>(X1, LN)\<rfloor>"
      show "\<exists>x2. thr ?s2' t' = \<lfloor>(x2, LN)\<rfloor> \<and> t' \<turnstile> (X1, shr s1') \<approx> (x2, shr ?s2') \<and> (wset ?s2' t' = None \<or> X1 \<approx>w x2)"
      proof(cases "t' = t")
        case True
        note this[simp]
        with s1' tst ts't' have [simp]: "X1 = x1'" "LN = no_wait_locks"
          by(simp_all)(auto simp add: redT_updLns_def o_def finfun_Diag_const2)
        with bisim' tst' wst show ?thesis by(auto simp add: redT_updLns_def o_def finfun_Diag_const2)
      next
        case False
        with ts't' have "ts1 t' = \<lfloor>(X1, LN)\<rfloor>" by auto
        with mbisim obtain X2 where "ts2 t' = \<lfloor>(X2, LN)\<rfloor>" "t' \<turnstile> (X1, m1) \<approx> (X2, m2)" "ws1 t' = None \<or> X1 \<approx>w X2"
          by(auto dest: mbisim_thrD1)
        with False show ?thesis by auto
      qed
    next
      show "finite (dom (thr s1'))" by simp
    next
      from mbisim_wset_thread_ok1[OF mbisim]
      show "wset_thread_ok (wset s1') (thr s1')" by(auto intro: wset_thread_ok_upd)
    qed
    ultimately show ?thesis by(auto)
  next
    case redT_acquire
    with tst have False by auto
    thus ?thesis ..
  qed
qed

lemma mbisim_simulation_silent2:
  "\<lbrakk> mbisim s1 s2; r2.mthr.silent_move s2 s2' \<rbrakk>
  \<Longrightarrow> \<exists>s1'. r1.mthr.silent_moves s1 s1' \<and> mbisim s1' s2'"
using FWdelay_bisimulation_diverge.mbisim_simulation_silent1[OF FWdelay_bisimulation_diverge_flip]
unfolding flip_simps .

lemma mbisim_simulation1':
  assumes mbisim: "mbisim s1 s2" and "\<not> m\<tau>move1 s1 tl1 s1'" "r1.redT s1 tl1 s1'"
  shows "\<exists>s2' s2'' tl2. r2.mthr.silent_moves s2 s2' \<and> r2.redT s2' tl2 s2'' \<and>
                        \<not> m\<tau>move2 s2' tl2 s2'' \<and> mbisim s1' s2'' \<and> mta_bisim tl1 tl2"
using mbisim_simulation1 assms .

lemma mbisim_simulation2':
  "\<lbrakk> mbisim s1 s2; r2.redT s2 tl2 s2'; \<not> m\<tau>move2 s2 tl2 s2' \<rbrakk>
  \<Longrightarrow> \<exists>s1' s1'' tl1. r1.mthr.silent_moves s1 s1' \<and> r1.redT s1' tl1 s1'' \<and> \<not> m\<tau>move1 s1' tl1 s1'' \<and>
                    mbisim s1'' s2' \<and> mta_bisim tl1 tl2"
using FWdelay_bisimulation_diverge.mbisim_simulation1'[OF FWdelay_bisimulation_diverge_flip]
unfolding flip_simps .

lemma m\<tau>diverge_simulation1:
  assumes "s1 \<approx>m s2"
  and "r1.mthr.\<tau>diverge s1"
  shows "r2.mthr.\<tau>diverge s2"
proof -
  from \<open>s1 \<approx>m s2\<close> have "finite (dom (thr s1))"
    by(rule mbisim_finite1)+
  from r1.\<tau>diverge_\<tau>mredTD[OF \<open>r1.mthr.\<tau>diverge s1\<close> this]
  obtain t x where "thr s1 t = \<lfloor>(x, no_wait_locks)\<rfloor>" "wset s1 t = None" "r1.\<tau>diverge t (x, shr s1)" by blast
  from \<open>s1 \<approx>m s2\<close> \<open>thr s1 t = \<lfloor>(x, no_wait_locks)\<rfloor>\<close> obtain x'
    where "thr s2 t = \<lfloor>(x', no_wait_locks)\<rfloor>" "t \<turnstile> (x, shr s1) \<approx> (x', shr s2)"
    by(auto dest: mbisim_thrD1)
  from \<open>s1 \<approx>m s2\<close> \<open>wset s1 t = None\<close> have "wset s2 t = None" by(simp add: mbisim_def)
  from \<open>t \<turnstile> (x, shr s1) \<approx> (x', shr s2)\<close> \<open>r1.\<tau>diverge t (x, shr s1)\<close>
  have "r2.\<tau>diverge t (x', shr s2)" by(simp add: \<tau>diverge_bisim_inv)
  thus ?thesis using \<open>thr s2 t = \<lfloor>(x', no_wait_locks)\<rfloor>\<close> \<open>wset s2 t = None\<close>
    by(rule r2.\<tau>diverge_into_\<tau>mredT)
qed

lemma \<tau>diverge_mbisim_inv:
  "s1 \<approx>m s2 \<Longrightarrow> r1.mthr.\<tau>diverge s1 \<longleftrightarrow> r2.mthr.\<tau>diverge s2"
apply(rule iffI)
 apply(erule (1) m\<tau>diverge_simulation1)
by(rule FWdelay_bisimulation_diverge.m\<tau>diverge_simulation1[OF FWdelay_bisimulation_diverge_flip, unfolded flip_simps])

lemma mbisim_delay_bisimulation:
  "delay_bisimulation_diverge r1.redT r2.redT mbisim mta_bisim m\<tau>move1 m\<tau>move2"
apply(unfold_locales)
apply(rule mbisim_simulation1 mbisim_simulation2 mbisim_simulation_silent1 mbisim_simulation_silent2 \<tau>diverge_mbisim_inv|assumption)+
done

theorem mdelay_bisimulation_final_base:
  "delay_bisimulation_final_base r1.redT r2.redT mbisim m\<tau>move1 m\<tau>move2 r1.mfinal r2.mfinal"
apply(unfold_locales)
apply(blast dest: mfinal1_simulation mfinal2_simulation)+
done

end

sublocale FWdelay_bisimulation_diverge < mthr: delay_bisimulation_diverge r1.redT r2.redT mbisim mta_bisim m\<tau>move1 m\<tau>move2
by(rule mbisim_delay_bisimulation)

sublocale FWdelay_bisimulation_diverge <
  mthr: delay_bisimulation_final_base r1.redT r2.redT mbisim mta_bisim m\<tau>move1 m\<tau>move2 r1.mfinal r2.mfinal
by(rule mdelay_bisimulation_final_base)

context FWdelay_bisimulation_diverge begin

lemma mthr_delay_bisimulation_diverge_final:
  "delay_bisimulation_diverge_final r1.redT r2.redT mbisim mta_bisim m\<tau>move1 m\<tau>move2 r1.mfinal r2.mfinal"
by(unfold_locales)

end

sublocale FWdelay_bisimulation_diverge <
  mthr: delay_bisimulation_diverge_final r1.redT r2.redT mbisim mta_bisim m\<tau>move1 m\<tau>move2 r1.mfinal r2.mfinal
by(rule mthr_delay_bisimulation_diverge_final)

subsection \<open>Strong bisimulation as corollary\<close>

locale FWbisimulation = FWbisimulation_base _ _ _ r2 convert_RA bisim "\<lambda>x1 x2. True" +
  r1: multithreaded final1 r1 convert_RA +
  r2: multithreaded final2 r2 convert_RA
  for r2 :: "('l,'t,'x2,'m2,'w,'o) semantics" ("_ \<turnstile> _ -2-_\<rightarrow> _" [50,0,0,50] 80)
  and convert_RA :: "'l released_locks \<Rightarrow> 'o list"
  and bisim :: "'t \<Rightarrow> ('x1 \<times> 'm1, 'x2 \<times> 'm2) bisim" ("_ \<turnstile> _/ \<approx> _" [50, 50, 50] 60) +
  assumes bisimulation_locale: "bisimulation (r1 t) (r2 t) (bisim t) (ta_bisim bisim)"
  and bisim_final: "t \<turnstile> (x1, m1) \<approx> (x2, m2) \<Longrightarrow> final1 x1 \<longleftrightarrow> final2 x2"
  and bisim_inv_red_other:
   "\<lbrakk> t' \<turnstile> (x, m1) \<approx> (xx, m2); t \<turnstile> (x1, m1) \<approx> (x2, m2); 
      t \<turnstile> (x1, m1) -1-ta1\<rightarrow> (x1', m1'); t \<turnstile> (x2, m2) -2-ta2\<rightarrow> (x2', m2'); 
      t \<turnstile> (x1', m1') \<approx> (x2', m2'); ta_bisim bisim ta1 ta2 \<rbrakk>
   \<Longrightarrow> t' \<turnstile> (x, m1') \<approx> (xx, m2')"
  and ex_final1_conv_ex_final2:
   "(\<exists>x1. final1 x1) \<longleftrightarrow> (\<exists>x2. final2 x2)"

sublocale FWbisimulation < bisim?: bisimulation "r1 t" "r2 t" "bisim t" "ta_bisim bisim" for t
by(rule bisimulation_locale)

sublocale FWbisimulation < bisim_diverge?:
  FWdelay_bisimulation_diverge final1 r1 final2 r2 convert_RA bisim "\<lambda>x1 x2. True" "\<lambda>s ta s'. False" "\<lambda>s ta s'. False"
proof -
  interpret biw: bisimulation_into_delay "r1 t" "r2 t" "bisim t" "ta_bisim bisim" "\<lambda>s ta s'. False" "\<lambda>s ta s'. False"
    for t
    by(unfold_locales) simp
  show "FWdelay_bisimulation_diverge final1 r1 final2 r2 bisim (\<lambda>x1 x2. True) (\<lambda>s ta s'. False) (\<lambda>s ta s'. False)"
  proof(unfold_locales)
    fix t' x m1 xx m2 x1 x2 t x1' ta1 x1'' m1' x2' ta2 x2'' m2'
    assume bisim: "t' \<turnstile> (x, m1) \<approx> (xx, m2)" and bisim12: "t \<turnstile> (x1, m1) \<approx> (x2, m2)"
      and \<tau>1: "\<tau>trsys.silent_moves (r1 t) (\<lambda>s ta s'. False) (x1, m1) (x1', m1)" 
      and red1: "t \<turnstile> (x1', m1) -1-ta1\<rightarrow> (x1'', m1')"
      and \<tau>2: "\<tau>trsys.silent_moves (r2 t) (\<lambda>s ta s'. False) (x2, m2) (x2', m2)"
      and red2: "t \<turnstile> (x2', m2) -2-ta2\<rightarrow> (x2'', m2')"
      and bisim12': "t \<turnstile> (x1'', m1') \<approx> (x2'', m2')" and tasim: "ta1 \<sim>m ta2"
    from \<tau>1 \<tau>2 have [simp]: "x1' = x1" "x2' = x2" by(simp_all add: rtranclp_False \<tau>moves_False)
    from bisim12 bisim_inv_red_other[OF bisim _ red1 red2 bisim12' tasim]
    show "t' \<turnstile> (x, m1') \<approx> (xx, m2')" by simp
  next
    fix t x1 m1 x2 m2 ta1 x1' m1'
    assume "t \<turnstile> (x1, m1) \<approx> (x2, m2)" "t \<turnstile> (x1, m1) -1-ta1\<rightarrow> (x1', m1')"
    from simulation1[OF this]
    show "\<exists>ta2 x2' m2'. t \<turnstile> (x2, m2) -2-ta2\<rightarrow> (x2', m2') \<and> t \<turnstile> (x1', m1') \<approx> (x2', m2') \<and> ta1 \<sim>m ta2"
      by auto
  next
    fix t x1 m1 x2 m2 ta2 x2' m2'
    assume "t \<turnstile> (x1, m1) \<approx> (x2, m2)" "t \<turnstile> (x2, m2) -2-ta2\<rightarrow> (x2', m2')"
    from simulation2[OF this]
    show "\<exists>ta1 x1' m1'. t \<turnstile> (x1, m1) -1-ta1\<rightarrow> (x1', m1') \<and> t \<turnstile> (x1', m1') \<approx> (x2', m2') \<and> ta1 \<sim>m ta2"
      by auto
  next
    show "(\<exists>x1. final1 x1) \<longleftrightarrow> (\<exists>x2. final2 x2)" by(rule ex_final1_conv_ex_final2)
  qed(fastforce simp add: bisim_final)+
qed

context FWbisimulation begin

lemma FWbisimulation_flip: "FWbisimulation final2 r2 final1 r1 (\<lambda>t. flip (bisim t))"
apply(rule FWbisimulation.intro)
  apply(rule r2.multithreaded_axioms)
 apply(rule r1.multithreaded_axioms)
apply(rule FWbisimulation_axioms.intro)
   apply(unfold flip_simps)
   apply(rule bisimulation_axioms)
  apply(erule bisim_final[symmetric])
 apply(erule (5) bisim_inv_red_other)
apply(rule ex_final1_conv_ex_final2[symmetric])
done

end

lemma FWbisimulation_flip_simps [flip_simps]:
  "FWbisimulation final2 r2 final1 r1 (\<lambda>t. flip (bisim t)) = FWbisimulation final1 r1 final2 r2 bisim"
by(auto dest: FWbisimulation.FWbisimulation_flip simp only: flip_flip)

context FWbisimulation begin

text \<open>
  The notation for mbisim is lost because @{term "bisim_wait"} is instantiated to @{term "\<lambda>x1 x2. True"}.
  This reintroduces the syntax, but it does not work for output mode. This would require a new abbreviation.
\<close>
notation mbisim ("_ \<approx>m _" [50, 50] 60)

theorem mbisim_bisimulation:
  "bisimulation r1.redT r2.redT mbisim mta_bisim"
proof
  fix s1 s2 tta1 s1'
  assume mbisim: "s1 \<approx>m s2" and "r1.redT s1 tta1 s1'"
  from mthr.simulation1[OF this]
  show "\<exists>s2' tta2. r2.redT s2 tta2 s2' \<and> s1' \<approx>m s2' \<and> tta1 \<sim>T tta2"
    by(auto simp add: \<tau>moves_False m\<tau>move_False)
next
  fix s2 s1 tta2 s2'
  assume "s1 \<approx>m s2" and "r2.redT s2 tta2 s2'"
  from mthr.simulation2[OF this]
  show "\<exists>s1' tta1. r1.redT s1 tta1 s1' \<and> s1' \<approx>m s2' \<and> tta1 \<sim>T tta2"
    by(auto simp add: \<tau>moves_False m\<tau>move_False)
qed

lemma mbisim_wset_eq:
  "s1 \<approx>m s2 \<Longrightarrow> wset s1 = wset s2"
by(simp add: mbisim_def)

lemma mbisim_mfinal:
  "s1 \<approx>m s2 \<Longrightarrow> r1.mfinal s1 \<longleftrightarrow> r2.mfinal s2"
apply(auto intro!: r2.mfinalI r1.mfinalI dest: mbisim_thrD2 mbisim_thrD1 bisim_final elim: r1.mfinalE r2.mfinalE)
apply(frule (1) mbisim_thrD2, drule mbisim_wset_eq, auto elim: r1.mfinalE)
apply(frule (1) mbisim_thrD1, drule mbisim_wset_eq, auto elim: r2.mfinalE)
done

end

sublocale FWbisimulation < mthr: bisimulation r1.redT r2.redT mbisim mta_bisim
by(rule mbisim_bisimulation)

sublocale FWbisimulation < mthr: bisimulation_final r1.redT r2.redT mbisim mta_bisim r1.mfinal r2.mfinal
by(unfold_locales)(rule mbisim_mfinal)

end
