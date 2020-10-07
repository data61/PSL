theory StateEventSystems
imports EventSystems
begin

(* structural representation of state event systems *)
record ('s, 'e) SES_rec = 
  S_SES ::  "'s set"
  s0_SES :: "'s"
  E_SES ::  "'e set"
  I_SES ::  "'e set"
  O_SES ::  "'e set"
  T_SES ::  "'s \<Rightarrow> 'e \<rightharpoonup> 's"

(* syntax abbreviations for SES_rec *)
abbreviation SESrecSSES :: "('s, 'e) SES_rec \<Rightarrow> 's set"
("S\<^bsub>_\<^esub>" [1000] 1000)
where
"S\<^bsub>SES\<^esub> \<equiv> (S_SES SES)"

abbreviation SESrecs0SES :: "('s, 'e) SES_rec \<Rightarrow> 's"
("s0\<^bsub>_\<^esub>" [1000] 1000)
where
"s0\<^bsub>SES\<^esub> \<equiv> (s0_SES SES)"

abbreviation SESrecESES :: "('s, 'e) SES_rec \<Rightarrow> 'e set"
("E\<^bsub>_\<^esub>" [1000] 1000)
where
"E\<^bsub>SES\<^esub> \<equiv> (E_SES SES)"

abbreviation SESrecISES :: "('s, 'e) SES_rec \<Rightarrow> 'e set"
("I\<^bsub>_\<^esub>" [1000] 1000)
where
"I\<^bsub>SES\<^esub> \<equiv> (I_SES SES)"

abbreviation SESrecOSES :: "('s, 'e) SES_rec \<Rightarrow> 'e set"
("O\<^bsub>_\<^esub>" [1000] 1000)
where
"O\<^bsub>SES\<^esub> \<equiv> (O_SES SES)"

abbreviation SESrecTSES :: "('s, 'e) SES_rec \<Rightarrow> ('s \<Rightarrow> 'e \<rightharpoonup> 's)"
("T\<^bsub>_\<^esub>" [1000] 1000)
where
"T\<^bsub>SES\<^esub> \<equiv> (T_SES SES)"

abbreviation TSESpred :: "'s \<Rightarrow> 'e \<Rightarrow> ('s, 'e) SES_rec \<Rightarrow> 's \<Rightarrow> bool"
("_ _\<longrightarrow>\<^bsub>_\<^esub> _" [100,100,100,100] 100)
where
"s e\<longrightarrow>\<^bsub>SES\<^esub> s' \<equiv> (T\<^bsub>SES\<^esub> s e = Some s')"

(* side conditions for state event systems *)
definition s0_is_state :: "('s, 'e) SES_rec \<Rightarrow> bool"
where
"s0_is_state SES \<equiv> s0\<^bsub>SES\<^esub> \<in> S\<^bsub>SES\<^esub>"

definition ses_inputs_are_events :: "('s, 'e) SES_rec \<Rightarrow> bool"
where
"ses_inputs_are_events SES \<equiv> I\<^bsub>SES\<^esub> \<subseteq> E\<^bsub>SES\<^esub>"

definition ses_outputs_are_events :: "('s, 'e) SES_rec \<Rightarrow> bool"
where
"ses_outputs_are_events SES \<equiv> O\<^bsub>SES\<^esub> \<subseteq> E\<^bsub>SES\<^esub>"

definition ses_inputs_outputs_disjoint :: "('s, 'e) SES_rec \<Rightarrow> bool"
where
"ses_inputs_outputs_disjoint SES \<equiv> I\<^bsub>SES\<^esub> \<inter> O\<^bsub>SES\<^esub> = {}"

definition correct_transition_relation :: "('s, 'e) SES_rec \<Rightarrow> bool"
where
"correct_transition_relation SES \<equiv>
 \<forall>x y z. x y\<longrightarrow>\<^bsub>SES\<^esub> z \<longrightarrow> ((x \<in> S\<^bsub>SES\<^esub>) \<and> (y \<in> E\<^bsub>SES\<^esub>) \<and> (z \<in> S\<^bsub>SES\<^esub>))"

(* State event systems are instances of SES_rec that satisfy SES_valid. *)
definition SES_valid :: "('s, 'e) SES_rec \<Rightarrow> bool"
where
"SES_valid SES \<equiv> 
  s0_is_state SES \<and> ses_inputs_are_events SES 
  \<and> ses_outputs_are_events SES \<and> ses_inputs_outputs_disjoint SES \<and>
  correct_transition_relation SES"

(* auxiliary definitions for state event systems *)

(* Paths in state event systems *)
primrec path :: "('s, 'e) SES_rec \<Rightarrow> 's \<Rightarrow> 'e list \<rightharpoonup> 's" 
where
path_empt: "path SES s1 [] = (Some s1)" |
path_nonempt: "path SES s1 (e # t) = 
  (if (\<exists>s2. s1 e\<longrightarrow>\<^bsub>SES\<^esub> s2) 
  then (path SES (the (T\<^bsub>SES\<^esub> s1 e)) t) 
  else None)" 

abbreviation pathpred :: "'s \<Rightarrow> 'e list \<Rightarrow> ('s, 'e) SES_rec \<Rightarrow> 's \<Rightarrow> bool"
("_ _\<Longrightarrow>\<^bsub>_\<^esub> _" [100, 100, 100, 100] 100)
where
"s t\<Longrightarrow>\<^bsub>SES\<^esub> s' \<equiv> path SES s t = Some s'"

(* A state s is reachable in a state event system if there is a path from the initial state
of the state event system to state s. *)
definition reachable :: "('s, 'e) SES_rec \<Rightarrow> 's \<Rightarrow> bool" 
where
"reachable SES s \<equiv> (\<exists>t. s0\<^bsub>SES\<^esub> t\<Longrightarrow>\<^bsub>SES\<^esub> s)"

(* A trace t is enabled in a state s if there is a path t from s to some other state.*)
definition enabled :: "('s, 'e) SES_rec \<Rightarrow> 's \<Rightarrow> 'e list \<Rightarrow> bool"
where
"enabled SES s t \<equiv> (\<exists>s'. s t\<Longrightarrow>\<^bsub>SES\<^esub> s')"

(* The set of possible traces in a state event system SES is the set of traces that are enabled in
the initial state of SES. *)
definition possible_traces :: "('s, 'e) SES_rec \<Rightarrow> ('e list) set"
where
"possible_traces SES \<equiv> {t. (enabled SES s0\<^bsub>SES\<^esub> t)}"

(* structural representation of the event system induced by a state event system *) 
definition induceES :: "('s, 'e) SES_rec \<Rightarrow> 'e ES_rec"
where
"induceES SES \<equiv> 
 \<lparr> 
  E_ES = E\<^bsub>SES\<^esub>, 
  I_ES = I\<^bsub>SES\<^esub>, 
  O_ES  = O\<^bsub>SES\<^esub>, 
  Tr_ES = possible_traces SES 
 \<rparr>"
(* auxiliary lemmas for state event systems *)

(* If some event sequence is not enabled in a state,
  then it will not become possible by appending events. *)
lemma none_remains_none : "\<And> s e. (path SES s t) = None 
  \<Longrightarrow> (path SES s (t @ [e])) = None"
  by (induct t, auto)

(* If some event sequence t is enabled in a state s in which
 some event e is not enabled, then the event sequence
 obtained by appending e to t is not enabled in s. *)
lemma path_trans_single_neg: "\<And> s1. \<lbrakk>s1 t\<Longrightarrow>\<^bsub>SES\<^esub> s2; \<not> (s2 e\<longrightarrow>\<^bsub>SES\<^esub> sn)\<rbrakk> 
     \<Longrightarrow> \<not> (s1 (t @ [e])\<Longrightarrow>\<^bsub>SES\<^esub> sn)"
    by (induct t, auto)

(* If the event sequence t:e is enabled in some state, then 
  the event sequence t is also enabled and results in some state t' *)
lemma path_split_single: "s1 (t@[e])\<Longrightarrow>\<^bsub>SES\<^esub> sn 
  \<Longrightarrow> \<exists>s'. s1 t\<Longrightarrow>\<^bsub>SES\<^esub> s'  \<and> s' e\<longrightarrow>\<^bsub>SES\<^esub> sn"
  by (cases "path SES s1 t", simp add: none_remains_none,
    simp, rule ccontr, auto simp add: path_trans_single_neg)


(* If an event sequence results in a state s', from which the event e results in sn,
  then the combined event sequence also results in sn *)
lemma path_trans_single: "\<And>s. \<lbrakk> s t\<Longrightarrow>\<^bsub>SES\<^esub> s'; s' e\<longrightarrow>\<^bsub>SES\<^esub> sn \<rbrakk> 
  \<Longrightarrow> s (t @ [e])\<Longrightarrow>\<^bsub>SES\<^esub> sn"
proof (induct t)
  case Nil thus ?case by auto
next
  case (Cons a t) thus ?case
  proof -
    from Cons obtain s1' where trans_s_a_s1': "s a\<longrightarrow>\<^bsub>SES\<^esub> s1'" 
      by (simp, split if_split_asm, auto)
    with Cons have "s1' (t @ [e])\<Longrightarrow>\<^bsub>SES\<^esub> sn" 
      by auto
    with trans_s_a_s1' show ?thesis 
      by auto
  qed
qed

(* We can split a path from s1 to sn via the event sequence t1:t2
 into two paths from s1 to s2 via t1 and from s2 to sn via t2  *)
lemma path_split: "\<And> sn. \<lbrakk> s1 (t1 @ t2)\<Longrightarrow>\<^bsub>SES\<^esub> sn \<rbrakk> 
  \<Longrightarrow> (\<exists>s2. (s1 t1\<Longrightarrow>\<^bsub>SES\<^esub> s2 \<and> s2 t2\<Longrightarrow>\<^bsub>SES\<^esub> sn))"
proof (induct t2 rule: rev_induct)
  case Nil thus ?case by auto
next
  case (snoc a t) thus ?case
  proof -
    from snoc have "s1 (t1 @ t @ [a])\<Longrightarrow>\<^bsub>SES\<^esub> sn" 
      by auto
    hence "\<exists>sn'. s1 (t1 @ t)\<Longrightarrow>\<^bsub>SES\<^esub> sn' \<and> sn' a\<longrightarrow>\<^bsub>SES\<^esub> sn" 
      by (simp add: path_split_single)
    then obtain sn' where path_t1_t_trans_a: 
      "s1 (t1 @ t)\<Longrightarrow>\<^bsub>SES\<^esub> sn' \<and> sn' a\<longrightarrow>\<^bsub>SES\<^esub> sn" 
      by auto
    with snoc obtain s2 where path_t1_t: 
      "s1 t1\<Longrightarrow>\<^bsub>SES\<^esub> s2 \<and> s2 t\<Longrightarrow>\<^bsub>SES\<^esub> sn'" 
      by auto
    with path_t1_t_trans_a have "s2 (t @ [a])\<Longrightarrow>\<^bsub>SES\<^esub> sn" 
      by (simp add: path_trans_single)
    with path_t1_t show ?thesis by auto
  qed
qed

(* Two paths can be concatenated. *)
lemma path_trans: 
"\<And>sn. \<lbrakk> s1 l1\<Longrightarrow>\<^bsub>SES\<^esub> s2; s2 l2\<Longrightarrow>\<^bsub>SES\<^esub> sn \<rbrakk> \<Longrightarrow> s1 (l1 @ l2)\<Longrightarrow>\<^bsub>SES\<^esub> sn"
proof (induct l2 rule: rev_induct)
  case Nil thus ?case by auto
next
  case (snoc a l) thus ?case
  proof -
    assume path_l1: "s1 l1\<Longrightarrow>\<^bsub>SES\<^esub> s2"
    assume "s2 (l@[a])\<Longrightarrow>\<^bsub>SES\<^esub> sn"
    hence "\<exists>sn'. s2 l\<Longrightarrow>\<^bsub>SES\<^esub> sn' \<and> sn' [a]\<Longrightarrow>\<^bsub>SES\<^esub> sn" 
      by (simp add: path_split del: path_nonempt)
    then obtain sn' where path_l_a: "s2 l\<Longrightarrow>\<^bsub>SES\<^esub> sn' \<and> sn' [a]\<Longrightarrow>\<^bsub>SES\<^esub> sn" 
      by auto
    with snoc path_l1 have path_l1_l: "s1 (l1@l)\<Longrightarrow>\<^bsub>SES\<^esub> sn'" 
      by auto
    with path_l_a have "sn' a\<longrightarrow>\<^bsub>SES\<^esub> sn" 
      by (simp, split if_split_asm, auto)
    with path_l1_l show "s1 (l1 @ l @ [a])\<Longrightarrow>\<^bsub>SES\<^esub> sn" 
      by (subst append_assoc[symmetric], rule_tac s'="sn'" in path_trans_single, auto)
  qed
qed	


(* The prefix of an enabled trace is also enabled. (This lemma cuts of the last element.) *)
lemma enabledPrefixSingle : "\<lbrakk> enabled SES s (t@[e]) \<rbrakk> \<Longrightarrow> enabled SES s t"
unfolding enabled_def
proof -
  assume ass: "\<exists>s'. s (t @ [e])\<Longrightarrow>\<^bsub>SES\<^esub> s'"
  from ass obtain s' where "s (t @ [e])\<Longrightarrow>\<^bsub>SES\<^esub> s'" ..
  hence "\<exists>t'. (s t\<Longrightarrow>\<^bsub>SES\<^esub> t') \<and> (t' e\<longrightarrow>\<^bsub>SES\<^esub> s')" 
    by (rule path_split_single)
  then obtain t' where "s t\<Longrightarrow>\<^bsub>SES\<^esub> t'" 
    by (auto)
  thus "\<exists>s'. s t\<Longrightarrow>\<^bsub>SES\<^esub> s'" ..
qed


(* The prefix of an enabled trace is also enabled.
    (This lemma cuts of a suffix trace.) *)
lemma enabledPrefix : "\<lbrakk> enabled SES s (t1 @ t2) \<rbrakk> \<Longrightarrow> enabled SES s t1"
  unfolding enabled_def
proof - 
  assume ass: "\<exists>s'. s (t1 @ t2)\<Longrightarrow>\<^bsub>SES\<^esub> s'"
  from ass obtain s' where "s (t1 @ t2)\<Longrightarrow>\<^bsub>SES\<^esub> s'" ..
  hence "\<exists>t. (s t1\<Longrightarrow>\<^bsub>SES\<^esub> t \<and> t t2\<Longrightarrow>\<^bsub>SES\<^esub> s')" 
    by (rule path_split)
  then obtain t where "s t1\<Longrightarrow>\<^bsub>SES\<^esub> t" 
    by (auto)
  then show "\<exists>s'. s t1\<Longrightarrow>\<^bsub>SES\<^esub> s'" ..
qed


(* The last element of an enabled trace makes a transition between two states. *)
lemma enabledPrefixSingleFinalStep : "\<lbrakk> enabled SES s (t@[e]) \<rbrakk> \<Longrightarrow> \<exists> t' t''. t' e\<longrightarrow>\<^bsub>SES\<^esub> t''"
  unfolding enabled_def
proof -
  assume ass: "\<exists>s'. s (t @ [e])\<Longrightarrow>\<^bsub>SES\<^esub> s'" 
  from ass obtain s' where "s (t @ [e])\<Longrightarrow>\<^bsub>SES\<^esub> s'" .. 
  hence "\<exists>t'. (s t\<Longrightarrow>\<^bsub>SES\<^esub> t')  \<and> (t' e\<longrightarrow>\<^bsub>SES\<^esub> s')" 
    by (rule path_split_single)
  then obtain t' where "t' e\<longrightarrow>\<^bsub>SES\<^esub> s'" 
    by (auto)
  thus "\<exists>t' t''. t' e\<longrightarrow>\<^bsub>SES\<^esub> t''" 
    by (auto)
qed


(* applying induceES on a state event system yields an event system *)
lemma induceES_yields_ES: 
  "SES_valid SES \<Longrightarrow> ES_valid (induceES SES)"
proof (simp add: SES_valid_def ES_valid_def, auto)
  assume SES_inputs_are_events: "ses_inputs_are_events SES"
  thus "es_inputs_are_events (induceES SES)"
    by (simp add: induceES_def ses_inputs_are_events_def es_inputs_are_events_def)
next
  assume SES_outputs_are_events: "ses_outputs_are_events SES"
  thus "es_outputs_are_events (induceES SES)"
    by (simp add: induceES_def ses_outputs_are_events_def es_outputs_are_events_def)
next
  assume SES_inputs_outputs_disjoint: "ses_inputs_outputs_disjoint SES"
  thus "es_inputs_outputs_disjoint (induceES SES)"
    by (simp add: induceES_def ses_inputs_outputs_disjoint_def es_inputs_outputs_disjoint_def)
next
  assume SES_correct_transition_relation: "correct_transition_relation SES"
  thus "traces_contain_events (induceES SES)"
      unfolding induceES_def traces_contain_events_def possible_traces_def
    proof (auto)
    fix l e
    assume enabled_l: "enabled SES s0\<^bsub>SES\<^esub> l"
    assume e_in_l: "e \<in> set l"
    from enabled_l e_in_l show "e \<in> E\<^bsub>SES\<^esub>"
    proof (induct l rule: rev_induct)
      case Nil 
        assume e_in_empty_list: "e \<in> set []" 
        hence f: "False"
          by (auto) 
        thus ?case 
          by auto
      next
      case (snoc a l)
      from snoc.prems have l_enabled: "enabled SES s0\<^bsub>SES\<^esub> l"
        by (simp add: enabledPrefixSingle)
        show ?case
          proof  (cases "e \<in> (set l)")
            from snoc.hyps l_enabled show "e \<in> set l \<Longrightarrow> e \<in> E\<^bsub>SES\<^esub>"
              by auto
            show "e \<notin> set l \<Longrightarrow> e \<in> E\<^bsub>SES\<^esub>"
              proof -
                assume "e \<notin> set l"
                with snoc.prems have e_eq_a : "e=a"
                  by auto
                from snoc.prems have "\<exists> t t'. t a\<longrightarrow>\<^bsub>SES\<^esub> t'" 
                  by (auto simp add: enabledPrefixSingleFinalStep)
                then obtain t t' where "t a\<longrightarrow>\<^bsub>SES\<^esub> t'"
                  by auto
                with e_eq_a SES_correct_transition_relation show "e \<in> E\<^bsub>SES\<^esub>" 
                  by (simp add: correct_transition_relation_def)
             qed
         qed
      qed
   qed
next
  show "traces_prefixclosed (induceES SES)"
    unfolding traces_prefixclosed_def prefixclosed_def induceES_def possible_traces_def prefix_def
    by (clarsimp simp add: enabledPrefix)
qed

end
