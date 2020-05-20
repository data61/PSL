(*  Title:      JinjaThreads/Framework/FWWait.thy
    Author:     Andreas Lochbihler
*)

section \<open>Semantics of the thread actions for wait, notify and interrupt\<close>

theory FWWait
imports
  FWState
begin

text \<open>Update functions for the wait sets in the multithreaded state\<close>

inductive redT_updW :: "'t \<Rightarrow> ('w, 't) wait_sets \<Rightarrow> ('t,'w) wait_set_action \<Rightarrow> ('w,'t) wait_sets \<Rightarrow> bool"
for t :: 't and ws :: "('w, 't) wait_sets"
where
  "ws t' = \<lfloor>InWS w\<rfloor> \<Longrightarrow> redT_updW t ws (Notify w) (ws(t' \<mapsto> PostWS WSNotified))"
| "(\<And>t'. ws t' \<noteq> \<lfloor>InWS w\<rfloor>) \<Longrightarrow> redT_updW t ws (Notify w) ws"
| "redT_updW t ws (NotifyAll w) (\<lambda>t. if ws t = \<lfloor>InWS w\<rfloor> then \<lfloor>PostWS WSNotified\<rfloor> else ws t)"
| "redT_updW t ws (Suspend w) (ws(t \<mapsto> InWS w))"
| "ws t' = \<lfloor>InWS w\<rfloor> \<Longrightarrow> redT_updW t ws (WakeUp t') (ws(t' \<mapsto> PostWS WSInterrupted))"
| "(\<And>w. ws t' \<noteq> \<lfloor>InWS w\<rfloor>) \<Longrightarrow> redT_updW t ws (WakeUp t') ws"
| "redT_updW t ws Notified (ws(t := None))"
| "redT_updW t ws WokenUp (ws(t := None))"

definition redT_updWs :: "'t \<Rightarrow> ('w,'t) wait_sets \<Rightarrow> ('t,'w) wait_set_action list \<Rightarrow> ('w,'t) wait_sets \<Rightarrow> bool"
where "redT_updWs t = rtrancl3p (redT_updW t)"

inductive_simps redT_updW_simps [simp]:
  "redT_updW t ws (Notify w) ws'"
  "redT_updW t ws (NotifyAll w) ws'"
  "redT_updW t ws (Suspend w) ws'"
  "redT_updW t ws (WakeUp t') ws'"
  "redT_updW t ws WokenUp ws'"
  "redT_updW t ws Notified ws'"

lemma redT_updW_total: "\<exists>ws'. redT_updW t ws wa ws'"
by(cases wa)(auto simp add: redT_updW.simps)

lemma redT_updWs_total: "\<exists>ws'. redT_updWs t ws was ws'"
proof(induct was rule: rev_induct)
  case Nil thus ?case by(auto simp add: redT_updWs_def)
next
  case (snoc wa was)
  then obtain ws' where "redT_updWs t ws was ws'" ..
  also from redT_updW_total[of t ws' wa]
  obtain ws'' where "redT_updW t ws' wa ws''" ..
  ultimately show ?case unfolding redT_updWs_def by(auto intro: rtrancl3p_step)
qed

lemma redT_updWs_trans: "\<lbrakk> redT_updWs t ws was ws'; redT_updWs t ws' was' ws'' \<rbrakk> \<Longrightarrow> redT_updWs t ws (was @ was') ws''"
unfolding redT_updWs_def by(rule rtrancl3p_trans)

lemma redT_updW_None_implies_None:
  "\<lbrakk> redT_updW t' ws wa ws'; ws t = None; t \<noteq> t' \<rbrakk> \<Longrightarrow> ws' t = None"
by(auto simp add: redT_updW.simps)

lemma redT_updWs_None_implies_None:
  assumes "redT_updWs t' ws was ws'"
  and "t \<noteq> t'" and "ws t = None"
  shows "ws' t = None"
using \<open>redT_updWs t' ws was ws'\<close> \<open>ws t = None\<close> unfolding redT_updWs_def
by induct(auto intro: redT_updW_None_implies_None[OF _ _ \<open>t \<noteq> t'\<close>])

lemma redT_updW_PostWS_imp_PostWS:
  "\<lbrakk> redT_updW t ws wa ws'; ws t'' = \<lfloor>PostWS w\<rfloor>; t'' \<noteq> t \<rbrakk> \<Longrightarrow>  ws' t'' = \<lfloor>PostWS w\<rfloor>"
by(auto simp add: redT_updW.simps)

lemma redT_updWs_PostWS_imp_PostWS:
  "\<lbrakk> redT_updWs t ws was ws'; t'' \<noteq> t; ws t'' = \<lfloor>PostWS w\<rfloor> \<rbrakk> \<Longrightarrow> ws' t'' = \<lfloor>PostWS w\<rfloor>"
unfolding redT_updWs_def 
by(induct rule: rtrancl3p.induct)(auto dest: redT_updW_PostWS_imp_PostWS)

lemma redT_updW_Some_otherD:
  "\<lbrakk> redT_updW t' ws wa ws'; ws' t = \<lfloor>w\<rfloor>; t \<noteq> t' \<rbrakk> 
  \<Longrightarrow> (case w of InWS w' \<Rightarrow> ws t = \<lfloor>InWS w'\<rfloor> | _ \<Rightarrow> ws t = \<lfloor>w\<rfloor> \<or> (\<exists>w'. ws t = \<lfloor>InWS w'\<rfloor>))"
by(auto simp add: redT_updW.simps split: if_split_asm wait_set_status.split)

lemma redT_updWs_Some_otherD:
  "\<lbrakk> redT_updWs t' ws was ws'; ws' t = \<lfloor>w\<rfloor>; t \<noteq> t' \<rbrakk> 
  \<Longrightarrow> (case w of InWS w' \<Rightarrow> ws t = \<lfloor>InWS w'\<rfloor> | _ \<Rightarrow> ws t = \<lfloor>w\<rfloor> \<or> (\<exists>w'. ws t = \<lfloor>InWS w'\<rfloor>))"
unfolding redT_updWs_def
apply(induct arbitrary: w rule: rtrancl3p.induct)
apply(fastforce split: wait_set_status.splits dest: redT_updW_Some_otherD)+
done

lemma redT_updW_None_SomeD:
  "\<lbrakk> redT_updW t ws wa ws'; ws' t' = \<lfloor>w\<rfloor>; ws t' = None \<rbrakk> \<Longrightarrow> t = t' \<and> (\<exists>w'. w = InWS w' \<and> wa = Suspend w')"
by(auto simp add: redT_updW.simps split: if_split_asm)

lemma redT_updWs_None_SomeD:
  "\<lbrakk> redT_updWs t ws was ws'; ws' t' = \<lfloor>w\<rfloor>; ws t' = None \<rbrakk> \<Longrightarrow> t = t' \<and> (\<exists>w'. Suspend w' \<in> set was)"
unfolding redT_updWs_def
proof(induct arbitrary: w rule: rtrancl3p.induct)
  case (rtrancl3p_refl ws) thus ?case by simp
next
  case (rtrancl3p_step ws was ws' wa ws'')
  show ?case
  proof(cases "ws' t'")
    case None
    from redT_updW_None_SomeD[OF \<open>redT_updW t ws' wa ws''\<close>, OF \<open>ws'' t' = \<lfloor>w\<rfloor>\<close> this]
    show ?thesis by auto
  next
    case (Some w')
    with \<open>ws t' = None\<close> rtrancl3p_step.hyps(2) show ?thesis by auto
  qed
qed

lemma redT_updW_neq_Some_SomeD:
  "\<lbrakk> redT_updW t' ws wa ws'; ws' t = \<lfloor>InWS w\<rfloor>; ws t \<noteq> \<lfloor>InWS w\<rfloor> \<rbrakk> \<Longrightarrow> t = t' \<and> wa = Suspend w"
by(auto simp add: redT_updW.simps split: if_split_asm)

lemma redT_updWs_neq_Some_SomeD:
  "\<lbrakk> redT_updWs t ws was ws'; ws' t' = \<lfloor>InWS w\<rfloor>; ws t' \<noteq> \<lfloor>InWS w\<rfloor> \<rbrakk> \<Longrightarrow> t = t' \<and> Suspend w \<in> set was"
unfolding redT_updWs_def
proof(induct rule: rtrancl3p.induct)
  case rtrancl3p_refl thus ?case by simp
next
  case (rtrancl3p_step ws was ws' wa ws'')
  show ?case
  proof(cases "ws' t' = \<lfloor>InWS w\<rfloor>")
    case True
    with \<open>ws t' \<noteq> \<lfloor>InWS w\<rfloor>\<close> \<open>\<lbrakk>ws' t' = \<lfloor>InWS w\<rfloor>; ws t' \<noteq> \<lfloor>InWS w\<rfloor>\<rbrakk> \<Longrightarrow> t = t' \<and> Suspend w \<in> set was\<close>
    show ?thesis by simp
  next
    case False
    with \<open>redT_updW t ws' wa ws''\<close> \<open>ws'' t' = \<lfloor>InWS w\<rfloor>\<close>
    have "t' = t \<and> wa = Suspend w" by(rule redT_updW_neq_Some_SomeD)
    thus ?thesis by auto
  qed
qed

lemma redT_updW_not_Suspend_Some:
  "\<lbrakk> redT_updW t ws wa ws'; ws' t = \<lfloor>w'\<rfloor>; ws t = \<lfloor>w\<rfloor>; \<And>w. wa \<noteq> Suspend w \<rbrakk>
  \<Longrightarrow> w' = w \<or> (\<exists>w'' w'''. w = InWS w'' \<and> w' = PostWS w''')"
by(auto simp add: redT_updW.simps split: if_split_asm)

lemma redT_updWs_not_Suspend_Some:
  "\<lbrakk> redT_updWs t ws was ws'; ws' t = \<lfloor>w'\<rfloor>; ws t = \<lfloor>w\<rfloor>; \<And>w. Suspend w \<notin> set was \<rbrakk>
  \<Longrightarrow> w' = w \<or> (\<exists>w'' w'''. w = InWS w'' \<and> w' = PostWS w''')"
unfolding redT_updWs_def
proof(induct arbitrary: w rule: rtrancl3p_converse_induct)
  case refl thus ?case by simp
next
  case (step ws wa ws' was ws'')
  note \<open>ws'' t = \<lfloor>w'\<rfloor>\<close>
  moreover  
  have "ws' t \<noteq> None"
  proof
    assume "ws' t = None"
    with \<open>rtrancl3p (redT_updW t) ws' was ws''\<close> \<open>ws'' t = \<lfloor>w'\<rfloor>\<close>
    obtain w' where "Suspend w' \<in> set was" unfolding redT_updWs_def[symmetric]
      by(auto dest: redT_updWs_None_SomeD)
    with \<open>Suspend w' \<notin> set (wa # was)\<close> show False by simp
  qed
  then obtain w'' where "ws' t = \<lfloor>w''\<rfloor>" by auto
  moreover {
    fix w
    from \<open>Suspend w \<notin> set (wa # was)\<close> have "Suspend w \<notin> set was" by simp }
  ultimately have "w' = w'' \<or> (\<exists>w''' w''''. w'' = InWS w''' \<and> w' = PostWS w'''')" by(rule step.hyps)
  moreover { fix w
    from \<open>Suspend w \<notin> set (wa # was)\<close> have "wa \<noteq> Suspend w" by auto }
  note redT_updW_not_Suspend_Some[OF \<open>redT_updW t ws wa ws'\<close>, OF \<open>ws' t = \<lfloor>w''\<rfloor>\<close> \<open>ws t = \<lfloor>w\<rfloor>\<close> this]
  ultimately show ?case by auto
qed

lemma redT_updWs_WokenUp_SuspendD:
  "\<lbrakk> redT_updWs t ws was ws'; Notified \<in> set was \<or> WokenUp \<in> set was; ws' t = \<lfloor>w\<rfloor> \<rbrakk> \<Longrightarrow> \<exists>w. Suspend w \<in> set was"
unfolding redT_updWs_def
by(induct rule: rtrancl3p_converse_induct)(auto dest: redT_updWs_None_SomeD[unfolded redT_updWs_def])

lemma redT_updW_Woken_Up_same_no_Notified_Interrupted:
  "\<lbrakk> redT_updW t ws wa ws'; ws' t = \<lfloor>PostWS w\<rfloor>; ws t = \<lfloor>PostWS w\<rfloor>; \<And>w. wa \<noteq> Suspend w \<rbrakk>
  \<Longrightarrow> wa \<noteq> Notified \<and> wa \<noteq> WokenUp"
by(fastforce)

lemma redT_updWs_Woken_Up_same_no_Notified_Interrupted:
  "\<lbrakk> redT_updWs t ws was ws'; ws' t = \<lfloor>PostWS w\<rfloor>; ws t = \<lfloor>PostWS w\<rfloor>; \<And>w. Suspend w \<notin> set was \<rbrakk>
  \<Longrightarrow> Notified \<notin> set was \<and> WokenUp \<notin> set was"
unfolding redT_updWs_def
proof(induct rule: rtrancl3p_converse_induct)
  case refl thus ?case by simp
next
  case (step ws wa ws' was ws'')
  note Suspend = \<open>\<And>w. Suspend w \<notin> set (wa # was)\<close>
  note \<open>ws'' t = \<lfloor>PostWS w\<rfloor>\<close>
  moreover have "ws' t = \<lfloor>PostWS w\<rfloor>"
  proof(cases "ws' t")
    case None
    with \<open>rtrancl3p (redT_updW t) ws' was ws''\<close> \<open>ws'' t = \<lfloor>PostWS w\<rfloor>\<close>
    obtain w where "Suspend w \<in> set was" unfolding redT_updWs_def[symmetric]
      by(auto dest: redT_updWs_None_SomeD)
    with Suspend[of w] have False by simp
    thus ?thesis ..
  next
    case (Some w')
    thus ?thesis using \<open>ws t = \<lfloor>PostWS w\<rfloor>\<close> Suspend \<open>redT_updW t ws wa ws'\<close>
      by(auto simp add: redT_updW.simps split: if_split_asm)
  qed
  moreover
  { fix w from Suspend[of w] have "Suspend w \<notin> set was" by simp }
  ultimately have "Notified \<notin> set was \<and> WokenUp \<notin> set was" by(rule step.hyps)
  moreover 
  { fix w from Suspend[of w] have "wa \<noteq> Suspend w" by auto }
  with \<open>redT_updW t ws wa ws'\<close> \<open>ws' t = \<lfloor>PostWS w\<rfloor>\<close> \<open>ws t = \<lfloor>PostWS w\<rfloor>\<close>
  have "wa \<noteq> Notified \<and> wa \<noteq> WokenUp" by(rule redT_updW_Woken_Up_same_no_Notified_Interrupted)
  ultimately show ?case by auto
qed

text \<open>Preconditions for wait set actions\<close>

definition wset_actions_ok :: "('w,'t) wait_sets \<Rightarrow> 't \<Rightarrow> ('t,'w) wait_set_action list \<Rightarrow> bool"
where
  "wset_actions_ok ws t was \<longleftrightarrow>
  (if Notified \<in> set was then ws t = \<lfloor>PostWS WSNotified\<rfloor>
   else if WokenUp \<in> set was then ws t = \<lfloor>PostWS WSWokenUp\<rfloor>
   else ws t = None)"

lemma wset_actions_ok_Nil [simp]:
  "wset_actions_ok ws t [] \<longleftrightarrow> ws t = None"
by(simp add: wset_actions_ok_def)

definition waiting :: "'w wait_set_status option \<Rightarrow> bool"
where "waiting w \<longleftrightarrow> (\<exists>w'. w = \<lfloor>InWS w'\<rfloor>)"

lemma not_waiting_iff:
  "\<not> waiting w \<longleftrightarrow> w = None \<or> (\<exists>w'. w = \<lfloor>PostWS w'\<rfloor>)"
apply(cases "w")
apply(case_tac [2] a)
apply(auto simp add: waiting_def)
done

lemma waiting_code [code]:
  "waiting None = False"
  "\<And>w. waiting \<lfloor>PostWS w\<rfloor> = False"
  "\<And>w. waiting \<lfloor>InWS w\<rfloor> = True"
by(simp_all add: waiting_def)

end
