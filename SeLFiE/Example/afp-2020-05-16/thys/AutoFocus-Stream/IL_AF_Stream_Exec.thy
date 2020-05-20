(*  Title:      IL_AF_Exec_Stream.thy
    Date:       Nov 2007
    Author:     David Trachtenherz
*)

section \<open>\textsc{AutoFocus} message stream processing and temporal logic on intervals\<close>

theory IL_AF_Stream_Exec
imports Main IL_AF_Stream AF_Stream_Exec
begin

subsection \<open>Correlation between Pre/Post-Conditions for \<open>f_Exec_Comp_Stream\<close> and \<open>f_Exec_Comp_Stream_Init\<close>\<close>

lemma i_Exec_Stream_Pre_Post1_iAll: "
  \<lbrakk> result = i_Exec_Comp_Stream trans_fun input c;
    \<forall>x_n c_n. P1 x_n \<and> P2 c_n \<longrightarrow> Q (trans_fun x_n c_n) \<rbrakk> \<Longrightarrow>
  \<box> t I. (P1 (input t) \<and> P2 (result\<^bsup>\<leftarrow> c\<^esup> t) \<longrightarrow> Q (result t))"
by (simp add: i_Exec_Stream_Pre_Post1)

text \<open>Direct relation between input and result after transition\<close>
lemma i_Exec_Stream_Pre_Post2_iAll: "
  \<lbrakk> result = i_Exec_Comp_Stream trans_fun input c;
    \<forall>x_n c_n. P c_n \<longrightarrow> Q x_n (trans_fun x_n c_n) \<rbrakk> \<Longrightarrow>
  \<box> t I. P (result\<^bsup>\<leftarrow> c\<^esup> t) \<longrightarrow> Q (input t) (result t)"
by (simp add: i_Exec_Stream_Pre_Post2)

lemma i_Exec_Stream_Pre_Post3_iAll_iNext: "
  \<lbrakk> result = i_Exec_Comp_Stream trans_fun input c;
    \<forall>x_n c_n. P c_n \<longrightarrow> Q x_n (trans_fun x_n c_n);
    \<forall>t\<in>I. inext t I' = Suc t \<rbrakk> \<Longrightarrow>
  \<box> t I. P (result t) \<longrightarrow> (\<circle> t1 t I'. Q (input t1) (result t1))"
by (rule iallI, simp add: iNext_def i_Exec_Stream_Pre_Post2_Suc)

lemma i_Exec_Stream_Init_Pre_Post1_iAll_iNext: "
  \<lbrakk> result = i_Exec_Comp_Stream_Init trans_fun input c;
    \<forall>x_n c_n. P1 x_n \<and> P2 c_n \<longrightarrow> Q (trans_fun x_n c_n);
    \<forall>t\<in>I. inext t I' = Suc t \<rbrakk> \<Longrightarrow>
  \<box> t I. (P1 (input t) \<and> P2 (result t) \<longrightarrow> (\<circle> t1 t I'. Q (result t1)))"
by (rule iallI, simp add: iNext_def i_Exec_Stream_Init_Pre_Post1)

text \<open>Direct relation between input and state before transition\<close>
lemma i_Exec_Stream_Init_Pre_Post2_iAll_iNext: "
  \<lbrakk> result = i_Exec_Comp_Stream_Init trans_fun input c;
    \<forall>x_n c_n. P x_n c_n \<longrightarrow> Q (trans_fun x_n c_n);
    \<forall>t\<in>I. inext t I' = Suc t \<rbrakk> \<Longrightarrow>
  \<box> t I. (P (input t) (result t) \<longrightarrow> (\<circle> t1 t I'. Q (result t1)))"
by (rule iallI, simp add: iNext_def i_Exec_Stream_Init_Pre_Post2)

text \<open>Relation between input and output\<close>
lemma i_Exec_Stream_Init_Pre_Post3_iAll_iNext: "
  \<lbrakk> result = i_Exec_Comp_Stream_Init trans_fun input c;
    \<forall>x_n c_n. P c_n \<longrightarrow> Q x_n (trans_fun x_n c_n);
    \<forall>t\<in>I. inext t I' = Suc t \<rbrakk> \<Longrightarrow>
  \<box> t I. (P (result t) \<longrightarrow> (\<circle> t1 t I'. Q (input\<^bsup>\<leftarrow> \<NoMsg>\<^esup> t1) (result t1)))"
apply (rule iallI, unfold iNext_def)
apply (simp add: ilist_Previous_Suc i_Exec_Stream_Init_nth_Suc_eq_i_Exec_Stream_nth i_Exec_Stream_Previous_i_Exec_Stream_Init)
apply (blast dest: i_Exec_Stream_Pre_Post2_iAll[OF refl])
done


subsection \<open>\<open>i_Exec_Comp_Stream_Acc_Output\<close> and temporal operators with bounded intervals.\<close>

text \<open>Temporal relation between uncompressed and compressed output of accelerated components.\<close>

lemma i_Exec_Comp_Stream_Acc_Output__eq_NoMsg_iAll_conv: "
  0 < k \<Longrightarrow>
  ((i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c) t = \<NoMsg>) =
  (\<box> t1 [t * k\<dots>,k - Suc 0]. (output_fun \<circ> i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c) t1 = \<NoMsg>)"
by (simp add: i_Exec_Comp_Stream_Acc_Output_def i_shrink_eq_NoMsg_iAll_conv)

lemma i_Exec_Comp_Stream_Acc_Output__eq_NoMsg_iAll_conv2: "
  0 < k \<Longrightarrow>
  ((i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c) t = \<NoMsg>) =
  (\<box> t1 [\<dots>k - Suc 0] \<oplus> (t * k). (output_fun \<circ> i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c) t1 = \<NoMsg>)"
by (simp add: iT_add i_Exec_Comp_Stream_Acc_Output__eq_NoMsg_iAll_conv)

lemma i_Exec_Comp_Stream_Acc_Output__Init__eq_NoMsg_iAll_conv: "
  0 < k \<Longrightarrow>
  ((i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c) t = \<NoMsg>) =
  (\<box> t1 [Suc (t * k)\<dots>,k - Suc 0]. (output_fun \<circ> i_Exec_Comp_Stream_Init trans_fun (input \<odot>\<^sub>i k) c) t1 = \<NoMsg>)"
apply (unfold i_Exec_Comp_Stream_Acc_Output_def)
apply (simp add: i_shrink_eq_NoMsg_iAll_conv i_Exec_Stream_Init_eq_i_Exec_Stream_Cons)
apply (rule_tac t="[Suc (t * k)\<dots>,k - Suc 0]" and s="[t * k\<dots>,k - Suc 0] \<oplus> 1" in subst)
 apply (simp add: iIN_add)
apply (simp add: iT_Plus_iAll_conv)
done

lemma i_Exec_Comp_Stream_Acc_Output__eq_Msg_iEx_iAll_cut_greater_conv: "
  \<lbrakk> 0 < k; m \<noteq> \<NoMsg>; s = (output_fun \<circ> i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c) \<rbrakk> \<Longrightarrow>
  ((i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c) t = m) =
  (\<diamond> t1 [t * k\<dots>,k - Suc 0]. (s t1 = m \<and>
    (\<box> t2 [t * k\<dots>,k - Suc 0] \<down>> t1 . s t2 = \<NoMsg>)))"
by (simp add: i_Exec_Comp_Stream_Acc_Output_def i_shrink_eq_Msg_iEx_iAll_cut_greater_conv)

lemma i_Exec_Comp_Stream_Acc_Output__eq_Msg_iEx_iAll_cut_greater_conv2: "
  \<lbrakk> 0 < k; m \<noteq> \<NoMsg>; s = (output_fun \<circ> i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c) \<rbrakk> \<Longrightarrow>
  ((i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c) t = m) =
  (\<diamond> t1 [\<dots>k - Suc 0] \<oplus> (t * k). (s t1 = m \<and>
    (\<box> t2 ([\<dots>k - Suc 0] \<oplus> (t * k)) \<down>> t1 . s t2 = \<NoMsg>)))"
by (simp add: i_Exec_Comp_Stream_Acc_Output_def i_shrink_eq_Msg_iEx_iAll_cut_greater_conv2)


lemma i_Exec_Comp_Stream_Acc_Output__eq_Msg_iSince_conv: "
  \<lbrakk> 0 < k; m \<noteq> \<NoMsg>; s = (output_fun \<circ> i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c) \<rbrakk> \<Longrightarrow>
  ((i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c) t = m) =
  (s t2 = \<NoMsg>. t2 \<S> t1 [t * k\<dots>,k - Suc 0]. s t1 = m)"
by (simp add: i_Exec_Comp_Stream_Acc_Output_def i_shrink_eq_Msg_iSince_conv)
lemma i_Exec_Comp_Stream_Acc_Output__eq_Msg_iSince_conv2: "
  \<lbrakk> 0 < k; m \<noteq> \<NoMsg>; s = (output_fun \<circ> i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c) \<rbrakk> \<Longrightarrow>
  ((i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c) t = m) =
  (s t2 = \<NoMsg>. t2 \<S> t1 [\<dots>k - Suc 0] \<oplus> (t * k). s t1 = m)"
by (simp add: i_Exec_Comp_Stream_Acc_Output__eq_Msg_iSince_conv iT_add)

lemma i_Exec_Comp_Stream_Acc_Output__Init__eq_Msg_iSince_conv: "
  \<lbrakk> 0 < k; m \<noteq> \<NoMsg>; s = (output_fun \<circ> i_Exec_Comp_Stream_Init trans_fun (input \<odot>\<^sub>i k) c) \<rbrakk> \<Longrightarrow>
  ((i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c) t = m) =
  (s t2 = \<NoMsg>. t2 \<S> t1 [Suc (t * k)\<dots>,k - Suc 0]. s t1 = m)"
apply (unfold i_Exec_Comp_Stream_Acc_Output_def)
apply (simp add: i_shrink_eq_Msg_iSince_conv i_Exec_Stream_Init_eq_i_Exec_Stream_Cons)
apply (rule_tac t="[Suc (t * k)\<dots>,k - Suc 0]" and s="[t * k\<dots>,k - Suc 0] \<oplus> 1" in subst)
 apply (simp add: iIN_add)
apply (simp add: iT_Plus_iSince_conv)
done

lemma i_Exec_Comp_Stream_Acc_Output__eq_iAll_iSince_conv: "
  \<lbrakk> 0 < k; s = (output_fun \<circ> i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c) \<rbrakk> \<Longrightarrow>
  ((i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c) t = m) =
  ((m = \<NoMsg> \<longrightarrow> (\<box> t1 [t * k\<dots>,k - Suc 0]. s t1 = \<NoMsg>)) \<and>
  ((m \<noteq> \<NoMsg> \<longrightarrow> (s t2 = \<NoMsg>. t2 \<S> t1 [t * k\<dots>,k - Suc 0]. s t1 = m))))"
apply (case_tac "m = \<NoMsg>")
apply (simp add: i_Exec_Comp_Stream_Acc_Output__eq_NoMsg_iAll_conv)
apply (simp add: i_Exec_Comp_Stream_Acc_Output__eq_Msg_iSince_conv)
done

lemma i_Exec_Comp_Stream_Acc_Output__eq_iAll_iSince_conv2: "
  \<lbrakk> 0 < k; s = (output_fun \<circ> i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c) \<rbrakk> \<Longrightarrow>
  ((i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c) t = m) =
  ((m = \<NoMsg> \<longrightarrow> (\<box> t1 [\<dots>k - Suc 0] \<oplus> (t * k). s t1 = \<NoMsg>)) \<and>
  ((m \<noteq> \<NoMsg> \<longrightarrow> (s t2 = \<NoMsg>. t2 \<S> t1 [\<dots>k - Suc 0] \<oplus> (t * k). s t1 = m))))"
by (simp add: i_Exec_Comp_Stream_Acc_Output__eq_iAll_iSince_conv iT_add)


subsection \<open>\<open>i_Exec_Comp_Stream_Acc_Output\<close> and temporal operators with unbounded intervals and start/finish events.\<close>

lemma i_Exec_Comp_Stream_Acc_Output__eq_NoMsg_iAll_start_event_conv: "
  \<lbrakk> 0 < k; \<And> t. event t = (t mod k = 0); t0 = t * k;
    s = (output_fun \<circ> i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c) \<rbrakk>\<Longrightarrow>
  ((i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c) t = \<NoMsg>) =
  (s t0 = \<NoMsg> \<and> (\<circle> t' t0 [0\<dots>]. (s t1 = \<NoMsg>. t1 \<U> t2 [0\<dots>] \<oplus> t'. event t2)))"
by (simp add: i_Exec_Comp_Stream_Acc_Output_def i_shrink_eq_NoMsg_iAll_start_event_conv)

lemma i_Exec_Comp_Stream_Acc_Output__Init__eq_NoMsg_iAll_start_event_conv: "
  \<lbrakk> 0 < k; \<And> t. event t = ((t + k - Suc 0) mod k = 0); t0 = Suc (t * k);
    s = (output_fun \<circ> i_Exec_Comp_Stream_Init trans_fun (input \<odot>\<^sub>i k) c) \<rbrakk>\<Longrightarrow>
  ((i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c) t = \<NoMsg>) =
  (s t0 = \<NoMsg> \<and> (\<circle> t' t0 [0\<dots>]. (s t1 = \<NoMsg>. t1 \<U> t2 [0\<dots>] \<oplus> t'. event t2)))"
apply (simp add: i_Exec_Comp_Stream_Acc_Output_def i_shrink_eq_NoMsg_iAll_start_event_conv)
apply (simp add: iT_add iNext_def iFROM_inext iT_iff)
apply (simp add: i_Exec_Stream_Init_eq_i_Exec_Stream_Cons)
apply (rule_tac t="[Suc (Suc (t*k))\<dots>]" and s="[Suc (t*k)\<dots>] \<oplus> Suc 0" in subst)
 apply (simp add: iFROM_add)
apply (simp add: iT_Plus_iUntil_conv)
done

lemma i_Exec_Comp_Stream_Acc_Output__Init__eq_NoMsg_iAll_start_event2_conv: "
  \<lbrakk> Suc 0 < k; \<And> t. event t = (t mod k = Suc 0); t0 = Suc (t * k);
    s = (output_fun \<circ> i_Exec_Comp_Stream_Init trans_fun (input \<odot>\<^sub>i k) c) \<rbrakk>\<Longrightarrow>
  ((i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c) t = \<NoMsg>) =
  (s t0 = \<NoMsg> \<and> (\<circle> t' t0 [0\<dots>]. (s t1 = \<NoMsg>. t1 \<U> t2 [0\<dots>] \<oplus> t'. event t2)))"
by (simp add: i_Exec_Comp_Stream_Acc_Output__Init__eq_NoMsg_iAll_start_event_conv mod_eq_Suc_0_conv)

lemma i_Exec_Comp_Stream_Acc_Output__eq_Msg_iUntil_start_event_conv: "
  \<lbrakk> 0 < k; m \<noteq> \<NoMsg>; \<And>t. event t = (t mod k = 0); t0 = t * k;
    s = (output_fun \<circ> i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c) \<rbrakk> \<Longrightarrow>
  ((i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c) t = m) = (
  (s t0 = m \<and> (\<circle> t' t0 [0\<dots>]. (s t1 = \<NoMsg>. t1 \<U> t2 ([0\<dots>] \<oplus> t'). event t2))) \<or>
  (\<circle> t' t0 [0\<dots>]. (\<not> event t1. t1 \<U> t2 ([0\<dots>] \<oplus> t'). (
    s t2 = m \<and> \<not> event t2 \<and> (\<circle> t'' t2 [0\<dots>].
      (s t3 = \<NoMsg>. t3 \<U> t4 ([0\<dots>] \<oplus> t''). event t4))))))"
by (simp add: i_Exec_Comp_Stream_Acc_Output_def i_shrink_eq_Msg_iUntil_start_event_conv)

lemma i_Exec_Comp_Stream_Acc_Output__Init__eq_Msg_iUntil_start_event_conv: "
  \<lbrakk> 0 < k; m \<noteq> \<NoMsg>; \<And>t. event t = ((t + k - Suc 0) mod k = 0); t0 = Suc (t * k);
    s = (output_fun \<circ> i_Exec_Comp_Stream_Init trans_fun (input \<odot>\<^sub>i k) c) \<rbrakk> \<Longrightarrow>
  ((i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c) t = m) = (
  (s t0 = m \<and> (\<circle> t' t0 [0\<dots>]. (s t1 = \<NoMsg>. t1 \<U> t2 ([0\<dots>] \<oplus> t'). event t2))) \<or>
  (\<circle> t' t0 [0\<dots>]. (\<not> event t1. t1 \<U> t2 ([0\<dots>] \<oplus> t'). (
    s t2 = m \<and> \<not> event t2 \<and> (\<circle> t'' t2 [0\<dots>].
      (s t3 = \<NoMsg>. t3 \<U> t4 ([0\<dots>] \<oplus> t''). event t4))))))"
apply (simp add: i_Exec_Comp_Stream_Acc_Output_def i_shrink_eq_Msg_iUntil_start_event_conv)
apply (simp add: iNext_def iFROM_inext iFROM_iff iT_add)
apply (simp add: i_Exec_Stream_Init_eq_i_Exec_Stream_Cons)
apply (simp only: Suc_eq_plus1 iFROM_add[symmetric])
apply (simp add: iT_Plus_iUntil_conv)
apply (simp only: Suc_eq_plus1 iFROM_add[symmetric])
apply (simp add: iT_Plus_iUntil_conv)
done

lemma i_Exec_Comp_Stream_Acc_Output__Init__eq_Msg_iUntil_start_event2_conv: "
  \<lbrakk> Suc 0 < k; m \<noteq> \<NoMsg>; \<And>t. event t = (t mod k = Suc 0); t0 = Suc (t * k);
    s = (output_fun \<circ> i_Exec_Comp_Stream_Init trans_fun (input \<odot>\<^sub>i k) c) \<rbrakk> \<Longrightarrow>
  ((i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c) t = m) = (
  (s t0 = m \<and> (\<circle> t' t0 [0\<dots>]. (s t1 = \<NoMsg>. t1 \<U> t2 ([0\<dots>] \<oplus> t'). event t2))) \<or>
  (\<circle> t' t0 [0\<dots>]. (\<not> event t1. t1 \<U> t2 ([0\<dots>] \<oplus> t'). (
    s t2 = m \<and> \<not> event t2 \<and> (\<circle> t'' t2 [0\<dots>].
      (s t3 = \<NoMsg>. t3 \<U> t4 ([0\<dots>] \<oplus> t''). event t4))))))"
by (simp add: i_Exec_Comp_Stream_Acc_Output__Init__eq_Msg_iUntil_start_event_conv mod_eq_Suc_0_conv)

lemma i_Exec_Comp_Stream_Acc_Output__eq_NoMsg_iAll_finish_event_conv: "
  \<lbrakk> Suc 0 < k; \<And> t. event t = (t mod k = k - Suc 0); t0 = t * k;
    s = (output_fun \<circ> i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c) \<rbrakk>\<Longrightarrow>
  ((i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c) t = \<NoMsg>) =
  (s t0 = \<NoMsg> \<and> (\<circle> t' t0 [0\<dots>]. (s t1 = \<NoMsg>. t1 \<U> t2 [0\<dots>] \<oplus> t'. event t2 \<and> s t2 = \<NoMsg>)))"
by (simp add: i_Exec_Comp_Stream_Acc_Output_def i_shrink_eq_NoMsg_iAll_finish_event_conv)

lemma i_Exec_Comp_Stream_Acc_Output__Init__eq_NoMsg_iAll_finish_event_conv: "
  \<lbrakk> Suc 0 < k; \<And> t. event t = (t mod k = 0); t0 = Suc (t * k);
    s = (output_fun \<circ> i_Exec_Comp_Stream_Init trans_fun (input \<odot>\<^sub>i k) c) \<rbrakk>\<Longrightarrow>
  ((i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c) t = \<NoMsg>) =
  (s t0 = \<NoMsg> \<and> (\<circle> t' t0 [0\<dots>]. (s t1 = \<NoMsg>. t1 \<U> t2 [0\<dots>] \<oplus> t'. event t2 \<and> s t2 = \<NoMsg>)))"
apply (simp add: i_Exec_Comp_Stream_Acc_Output__eq_NoMsg_iAll_finish_event_conv)
apply (simp add: iNext_def iFROM_inext iFROM_iff iT_add)
apply (simp add: i_Exec_Stream_Init_eq_i_Exec_Stream_Cons)
apply (rule_tac t="[Suc (Suc (t * k))\<dots>]" and s="[Suc (t * k)\<dots>] \<oplus> 1" in subst)
 apply (simp add: iFROM_add)
apply (simp add: iT_Plus_iUntil_conv)
apply (simp add: mod_eq_divisor_minus_Suc_0_conv)
done

lemma i_Exec_Comp_Stream_Acc_Output__eq_Msg_iUntil_finish_event_conv: "
  \<lbrakk> 0 < k; m \<noteq> \<NoMsg>; \<And> t. event t = (t mod k = k - Suc 0); t0 = t * k;
    s = (output_fun \<circ> i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c) \<rbrakk>\<Longrightarrow>
  ((i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c) t = m) =
  ((\<not> event t1. t1 \<U> t2 ([0\<dots>] \<oplus> t0). event t2 \<and> s t2 = m) \<or>
  (\<not> event t1. t1 \<U> t2 ([0\<dots>] \<oplus> t0). (\<not> event t2 \<and> s t2 = m \<and> (
    \<circle> t' t2 [0\<dots>]. (s t3 = \<NoMsg>. t3 \<U> t4 ([0\<dots>] \<oplus> t'). event t4 \<and> s t4 = \<NoMsg>)))))"
apply (case_tac "k = Suc 0")
 apply (simp add: iT_add iT_not_empty iFROM_Min)
apply (drule neq_le_trans[OF not_sym], simp)
apply (simp add: i_Exec_Comp_Stream_Acc_Output_def i_shrink_eq_Msg_iUntil_finish_event_conv)
done

lemma i_Exec_Comp_Stream_Acc_Output__Init__eq_Msg_iUntil_finish_event_conv: "
  \<lbrakk> Suc 0 < k; m \<noteq> \<NoMsg>; \<And> t. event t = (t mod k = 0); t0 = Suc (t * k);
    s = (output_fun \<circ> i_Exec_Comp_Stream_Init trans_fun (input \<odot>\<^sub>i k) c) \<rbrakk>\<Longrightarrow>
  ((i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c) t = m) =
  ((\<not> event t1. t1 \<U> t2 ([0\<dots>] \<oplus> t0). event t2 \<and> s t2 = m) \<or>
  (\<not> event t1. t1 \<U> t2 ([0\<dots>] \<oplus> t0). (\<not> event t2 \<and> s t2 = m \<and> (
    \<circle> t' t2 [0\<dots>]. (s t3 = \<NoMsg>. t3 \<U> t4 ([0\<dots>] \<oplus> t'). event t4 \<and> s t4 = \<NoMsg>)))))"
apply (simp add: i_Exec_Comp_Stream_Acc_Output__eq_Msg_iUntil_finish_event_conv)
apply (simp add: iNext_def iFROM_inext iT_iff)
apply (simp add: i_Exec_Stream_Init_eq_i_Exec_Stream_Cons)
apply (simp add: iT_Plus_iUntil_conv)
apply (simp add: mod_eq_divisor_minus_Suc_0_conv add_Suc[symmetric] del: add_Suc)
done


subsection \<open>\<open>i_Exec_Comp_Stream_Acc_Output\<close> and temporal operators with idle states.\<close>

lemma i_Exec_Comp_Stream_Acc_Output__eq_NoMsg_State_Idle_conv: "
  \<lbrakk> 0 < k;
    State_Idle localState output_fun trans_fun (
      i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun input c t);
    t0 = t * k;
    s = i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c \<rbrakk> \<Longrightarrow>
  (i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c t = \<NoMsg>) =
  (output_fun (s t1) = \<NoMsg>. t1 \<U> t2 ([0\<dots>] \<oplus> t0). (
   output_fun (s t2) = \<NoMsg> \<and> State_Idle localState output_fun trans_fun (localState (s t2))))"
apply (case_tac "k = Suc 0")
 apply (simp add: iUntil_def)
 apply (rule iffI)
  apply (rule_tac t=t in iexI)
   apply (simp add: iT_add iT_cut_less)
  apply (simp add: iT_add iT_iff)
 apply (clarify, rename_tac t1)
 apply (simp add: iT_add iT_iff iT_cut_less)
 apply (drule order_le_less[THEN iffD1])
 apply (erule disjE)
  apply (drule_tac t=t in ispec)
  apply (simp add: iT_iff)+
apply (drule order_neq_le_trans[OF not_sym Suc_leI], assumption)
apply (simp add: i_Exec_Comp_Stream_Acc_Output__eq_NoMsg_iAll_conv)
apply (simp add: iT_add i_Exec_Stream_nth i_Exec_Stream_Acc_LocalState_nth)
apply (simp add: i_take_Suc_conv_app_nth[of t])
apply (simp add: i_expand_i_take_mult[symmetric] f_Exec_append)
apply (subgoal_tac "\<forall>t1 \<in> [t * k\<dots>,k - Suc 0]. input \<odot>\<^sub>i k \<Down> Suc t1 \<up> (t * k) = input t # \<NoMsg>\<^bsup>t1 - t * k\<^esup>")
 prefer 2
 apply (simp add: i_expand_nth_interval_eq_nth_append_replicate_NoMsg iIN_iff)
apply (case_tac "output_fun (f_Exec_Comp trans_fun (input \<odot>\<^sub>i k \<Down> Suc (t * k)) c) \<noteq> \<NoMsg>")
 apply (subgoal_tac "
   \<not> (\<box> t1 [t * k\<dots>,k - Suc 0]. output_fun (f_Exec_Comp trans_fun (input \<odot>\<^sub>i k \<Down> Suc t1) c) = \<NoMsg>)")
  prefer 2
  apply simp
  apply (rule_tac t="t * k" in iexI, assumption)
  apply (simp add: iIN_iff)
 apply (simp add: not_iUntil del: not_iAll)
 apply (clarsimp simp: iT_iff, rename_tac t1 t2)
 apply (case_tac "t1 = t * k", simp)
 apply (drule order_le_neq_trans[OF _ not_sym], assumption)
 apply (rule_tac t="t * k" in iexI, simp)
 apply (simp add: iFROM_cut_less1 iIN_iff)
apply (case_tac "
  State_Idle localState output_fun trans_fun
    (localState ((trans_fun (input t) (f_Exec_Comp trans_fun (input \<odot>\<^sub>i k \<Down> (t * k)) c))))")
 apply (subgoal_tac "
   (\<box> t1 [t * k\<dots>,k - Suc 0]. output_fun (f_Exec_Comp trans_fun (input \<odot>\<^sub>i k \<Down> Suc t1) c) = NoMsg)")
  prefer 2
  apply (clarsimp simp: iIN_iff, rename_tac t1)
  apply (rule_tac m="t * k" and n="Suc t1" in subst[OF i_take_drop_append, rule_format], simp)
  apply (drule_tac x=t1 in bspec, simp add: iT_iff)
  apply (simp add: f_Exec_append del: i_take_drop_append)
  apply (simp add: i_take_Suc_conv_app_nth f_Exec_append i_expand_nth_mult)
  apply (rule f_Exec_State_Idle_replicate_NoMsg_output, assumption+)
 apply (simp add: iUntil_def)
 apply (rule_tac t="t * k" in iexI)
  apply (simp add: i_take_Suc_conv_app_nth f_Exec_append i_expand_nth_mult iFROM_cut_less)
 apply (simp add: iFROM_iff)
apply (subgoal_tac "\<forall>i < k. input \<odot>\<^sub>i k \<Up> Suc (t * k) \<Down> i = NoMsg\<^bsup>i\<^esup>")
 prefer 2
 apply (simp add: list_eq_iff i_expand_nth_if)
apply (rule iffI)
 apply (frule State_Idle_imp_exists_state_change2, assumption)
 apply (elim exE conjE, rename_tac i)
 apply (frule Suc_less_pred_conv[THEN iffD2])
 apply (simp only: iUntil_def)
 apply (rule_tac t="Suc (t * k + i)" in iexI)
  apply (rule conjI)
   apply (drule_tac t="Suc (t * k + i)" in ispec)
    apply (simp add: iIN_iff)
   apply (rule conjI, simp)
   apply (rule_tac t="Suc (Suc (t * k + i))" and s="Suc (t * k) + Suc i" in subst, simp)
   apply (subst i_take_add)
   apply (drule_tac x="Suc i" in spec)+
   apply (simp add: i_take_Suc_conv_app_nth f_Exec_append i_expand_nth_mult)
  apply (rule iallI, rename_tac t1)
  apply (drule_tac t=t1 in ispec)
   apply (drule_tac m="Suc i" in less_imp_le_pred)
   apply (clarsimp simp: iIN_iff iFROM_cut_less1)
   apply (rule order_trans, assumption)
   apply simp
  apply assumption
 apply (simp add: iFROM_iff)
apply (rule iallI)
apply (unfold iUntil_def, elim iexE conjE, rename_tac t2)
apply (case_tac "t1 < t2")
 apply (drule_tac t=t1 in ispec)
  apply (simp add: cut_less_mem_iff iT_iff)
 apply simp
apply (simp add: linorder_not_less)
apply (case_tac "t1 = t2", simp)
apply (drule le_neq_trans[OF _ not_sym], assumption)
apply (drule_tac i=t2 in less_imp_add_positive, elim exE conjE, rename_tac i)
apply (drule_tac t=t1 in sym)
apply (simp del: add_Suc add: add_Suc[symmetric] i_take_add f_Exec_append iFROM_iff)
apply (rule_tac t="input \<odot>\<^sub>i k \<Up> Suc t2 \<Down> i" and s="\<NoMsg>\<^bsup>i\<^esup>" in subst)
 apply (rule list_eq_iff[THEN iffD2])
 apply simp
 apply (intro allI impI, rename_tac i1)
 apply (simp add: i_expand_nth_if)
 apply (subst imp_conv_disj, rule disjI1)
 apply simp
 apply (subgoal_tac "t * k < Suc (t2 + i1) \<and> Suc (t2 + i1) < t * k + k", elim conjE)
  prefer 2
  apply (simp add: iIN_iff)
 apply (simp only: mult.commute[of _ k])
 apply (rule between_imp_mod_gr0, assumption+)
apply (rule f_Exec_State_Idle_replicate_NoMsg_gr0_output, assumption+)
done

lemma i_Exec_Comp_Stream_Acc_Output__eq_Msg_with_State_Idle_imp: "
  \<lbrakk> 0 < k;
    s = i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c;
    t0 = t * k;
    t1 \<in> [0\<dots>, k - Suc 0] \<oplus> t0;
    State_Idle localState output_fun trans_fun (localState (s t1));
    output_fun (s t1) \<noteq> \<NoMsg> \<rbrakk> \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c t = output_fun (s t1)"
apply (case_tac "k = Suc 0")
 apply (simp add: iIN_0 iT_Plus_singleton)
apply (drule order_neq_le_trans[OF not_sym], rule Suc_leI, assumption)
apply (simp add: iT_add iT_iff, erule conjE)
apply (simp only: i_Exec_Stream_Acc_Output_nth i_Exec_Stream_nth)
apply (rule_tac t="Suc t1" and s="t * k + (Suc t1 - t * k)" in subst, simp)
apply (simp only: i_take_add f_Exec_append i_expand_i_take_mult)
apply (subgoal_tac "input \<odot>\<^sub>i k \<Up> (t * k) \<Down> (Suc t1 - t * k) = input t # \<NoMsg>\<^bsup>t1 - t * k\<^esup>")
 prefer 2
 apply (simp add: i_take_i_drop)
 apply (subst i_expand_nth_interval_eq_nth_append_replicate_NoMsg)
 apply (simp del: f_Exec_Comp_Stream.simps)+
apply (subgoal_tac "\<exists>i. k - Suc 0 = t1 - t * k + i")
 prefer 2
 apply (rule le_iff_add[THEN iffD1])
 apply (simp add: le_diff_conv)
apply (erule exE)
apply (simp only: replicate_add)
apply (subst append_Cons[symmetric])
apply (subst State_Idle_append_replicate_NoMsg_output_last_message)
 apply (simp only: f_Exec_append[symmetric])
 apply (rule_tac t="input \<Down> t \<odot>\<^sub>f k @ input t # NoMsg\<^bsup>t1 - t * k\<^esup>" and s="input \<odot>\<^sub>i k \<Down> Suc t1" in subst)
  apply (subst i_expand_i_take_mult[symmetric])
  apply (drule_tac t="input t # NoMsg\<^bsup>t1 - t * k\<^esup>" in sym)
  apply (simp add: i_take_add[symmetric])
 apply assumption
apply (subgoal_tac "
  f_Exec_Comp_Stream trans_fun (input t # NoMsg\<^bsup>t1 - t * k\<^esup>)
   (f_Exec_Comp trans_fun (input \<Down> t \<odot>\<^sub>f k) c) \<noteq> []")
 prefer 2
 apply (simp add: f_Exec_Stream_not_empty_conv)
apply (rule ssubst[OF last_message_Msg_eq_last])
  apply simp
 apply (subst map_last, simp)
 apply (subst f_Exec_eq_f_Exec_Stream_last2[symmetric], simp)
 apply (subst f_Exec_append[symmetric])
 apply (rule_tac t="input \<Down> t \<odot>\<^sub>f k @ input t # NoMsg\<^bsup>t1 - t * k\<^esup>" and s="input \<odot>\<^sub>i k \<Down> Suc t1" in subst)
  apply (subst i_expand_i_take_mult[symmetric])
  apply (rule_tac t="Suc t1" and s="t * k + (Suc t1 - t * k)" in subst, simp)
  apply (subst i_take_add, simp)
 apply assumption
apply (subst map_last, simp)
apply (subst f_Exec_eq_f_Exec_Stream_last2[symmetric], simp+)
done

lemma i_Exec_Comp_Stream_Acc_Output__eq_Msg_with_State_Idle_conv2: "
  \<lbrakk> 0 < k;
    State_Idle localState output_fun trans_fun (
      i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun input c t);
    m \<noteq> \<NoMsg>;
    t0 = t * k;
    s = i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c;
    t1 \<in> [0\<dots>, k - Suc 0] \<oplus> t0;
    State_Idle localState output_fun trans_fun (localState (s t1));
    output_fun (s t1) \<noteq> \<NoMsg> \<rbrakk> \<Longrightarrow>
  (i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c t = m) =
  (\<diamond> t1 [0\<dots>, k - Suc 0] \<oplus> t0. (
      (output_fun (s t1) = m \<and> State_Idle localState output_fun trans_fun (localState (s t1)))))"
apply (case_tac "k = Suc 0")
 apply (simp add: iIN_0 iT_Plus_singleton)
apply (drule order_neq_le_trans[OF not_sym], rule Suc_leI, assumption)
apply simp
apply (simp add: i_Exec_Comp_Stream_Acc_Output__eq_Msg_with_State_Idle_imp)
apply (rule iffI)
 apply blast
apply (clarify, rename_tac t1')
apply (subgoal_tac "t1' = t1")
 prefer 2
 apply (rule ccontr)
 apply (simp add: i_Exec_Stream_nth)
 apply (subgoal_tac "
   \<And> n1 n2.
   \<lbrakk> n1 < n2; n1 \<in> [0\<dots>,k - Suc 0] \<oplus> t * k; n2 \<in> [0\<dots>,k - Suc 0] \<oplus> t * k;
     State_Idle localState output_fun trans_fun (localState (f_Exec_Comp trans_fun (input \<odot>\<^sub>i k \<Down> Suc n1) c));
     output_fun (f_Exec_Comp trans_fun (input \<odot>\<^sub>i k \<Down> Suc n2) c) \<noteq> NoMsg \<rbrakk> \<Longrightarrow>
   False")
  prefer 2
  apply (drule_tac i=n1 in less_imp_add_positive, elim exE conjE, rename_tac i)
  apply (drule_tac t=n2 in sym, simp)
  apply (simp only: add_Suc[symmetric] i_take_add f_Exec_append)
  apply (subgoal_tac "input \<odot>\<^sub>i k \<Up> Suc n1 \<Down> i = \<NoMsg>\<^bsup>i\<^esup>")
   prefer 2
   apply (subst i_take_i_drop)
   apply (rule_tac t="\<NoMsg>\<^bsup>i\<^esup>" and s="\<NoMsg>\<^bsup>i + Suc n1 - Suc n1\<^esup>" in subst, simp)
   apply (rule_tac t=t in i_expand_nth_interval_eq_replicate_NoMsg)
   apply (simp add: iT_add iT_iff)+
  apply (frule_tac c="f_Exec_Comp trans_fun (input \<odot>\<^sub>i k \<Down> Suc n1) c" and n=i
     in f_Exec_State_Idle_replicate_NoMsg_gr0_output)
  apply (fastforce dest: linorder_neq_iff[THEN iffD1])+
done

text \<open>Here the property to be checked uses only unbounded intervals suitable for LTL.\<close>
lemma i_Exec_Comp_Stream_Acc_Output__eq_Msg_with_State_Idle_conv: "
  \<lbrakk> 0 < k;
    State_Idle localState output_fun trans_fun (
      i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun input c t);
    m \<noteq> \<NoMsg>;
    t0 = t * k;
    s = i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c;
    t1 \<in> [0\<dots>, k - Suc 0] \<oplus> t0;
    State_Idle localState output_fun trans_fun (localState (s t1));
    output_fun (s t1) \<noteq> \<NoMsg> \<rbrakk> \<Longrightarrow>
  (i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c t = m) =
  ((\<not> State_Idle localState output_fun trans_fun (localState (s t2))). t2 \<U> t1 [0\<dots>] \<oplus> t0. (
      (output_fun (s t1) = m \<and> State_Idle localState output_fun trans_fun (localState (s t1)))))"
apply (subst i_Exec_Comp_Stream_Acc_Output__eq_Msg_with_State_Idle_conv2, assumption+)
apply (unfold iUntil_def)
apply (rule iffI)
 apply (elim iexE conjE, rename_tac t2)
 apply (rule_tac t=t2 in iexI)
  prefer 2
  apply (simp add: iT_add iT_iff)
 apply simp
 apply (rule iallI, rename_tac t2')
 apply (rule ccontr)
 apply (simp add: cut_less_mem_iff iT_iff iT_add, elim conjE)
 apply (frule_tac n=t2' in le_imp_less_Suc)
 apply (frule_tac i=t2' in less_imp_add_positive, elim exE conjE, rename_tac i)
 apply (drule_tac t=t2 in sym)
 apply (simp only: i_Exec_Stream_nth add_Suc[symmetric] i_take_add f_Exec_append)
 apply (simp only: i_take_i_drop)
 apply (subgoal_tac "input \<odot>\<^sub>i k \<Down> (i + Suc t2') \<up> Suc t2' = \<NoMsg>\<^bsup>i\<^esup>")
  prefer 2
  apply (rule_tac t="\<NoMsg>\<^bsup>i\<^esup>" and s="\<NoMsg>\<^bsup>i + Suc t2' - Suc t2'\<^esup>" in subst, simp)
  apply (rule_tac t=t in i_expand_nth_interval_eq_replicate_NoMsg)
  apply simp+
 apply (drule_tac c="(f_Exec_Comp trans_fun (input \<odot>\<^sub>i k \<Down> Suc t2') c)" and n=i
   in f_Exec_State_Idle_replicate_NoMsg_gr0_output, assumption)
 apply simp
apply (fastforce simp: iT_add iT_iff i_Exec_Stream_Acc_LocalState_nth i_Exec_Stream_nth)
done

lemma i_Exec_Comp_Stream_Acc_Output__eq_Msg_before_State_Idle_imp2: "
  \<lbrakk> Suc 0 < k;
    State_Idle localState output_fun trans_fun (
      i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun input c t);
    m \<noteq> \<NoMsg>;
    t0 = t * k;
    s = i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c;
    t1 \<in> [0\<dots>, k - Suc 0] \<oplus> t0;
    output_fun (s t1) = m;
    \<circle> t2 t1 [0\<dots>].
     ((output_fun (s t3) = \<NoMsg>. t3 \<U> t4 ([0\<dots>] \<oplus> t2).
      (output_fun (s t4) = \<NoMsg> \<and> State_Idle localState output_fun trans_fun (localState (s t4))))) \<rbrakk> \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c t = m"
apply (clarsimp simp: iUntil_def iNext_def iT_inext iT_iff, rename_tac t2)
apply (simp only: i_Exec_Stream_Acc_Output_nth i_Exec_Stream_Acc_LocalState_nth i_Exec_Stream_nth)
apply (rule last_message_conv[THEN iffD2], assumption)
apply (clarsimp simp: iT_add iT_iff simp del: f_Exec_Comp_Stream.simps)
apply (subgoal_tac "t1 - t * k < k")
 prefer 2
 apply simp
apply (rule_tac x="t1 - t * k" in exI)
apply (rule conjI, simp)
apply (rule conjI)
 apply (simp add: f_Exec_Stream_nth min_eqL del: f_Exec_Comp.simps f_Exec_Comp_Stream.simps)
 apply (simp only: f_Exec_append[symmetric])
 apply (subst i_expand_i_take_mult_Suc[symmetric], assumption)
 apply simp
apply (intro allI impI)
apply (simp only: f_Exec_Stream_length length_Cons length_replicate Suc_pred
  nth_map f_Exec_Stream_nth take_Suc_Cons take_replicate min_eqL[OF less_imp_le_pred])
apply (subst f_Exec_append[symmetric])
apply (subst i_expand_i_take_mult_Suc[symmetric], assumption)
apply (case_tac "t2 \<le> t * k + j")
 prefer 2
 apply fastforce
apply (drule_tac x=t2 in order_le_less[THEN iffD1, rule_format])
apply (erule disjE)
 prefer 2
 apply simp
apply (subgoal_tac "
  State_Idle localState output_fun trans_fun
    (localState (f_Exec_Comp trans_fun (input \<odot>\<^sub>i k \<Down> (t * k + Suc j)) c))")
 prefer 2
 apply (rule_tac t="t * k + Suc j" and s="Suc t2 + (t * k + j - t2)" in subst, simp)
 apply (simp only: i_take_add f_Exec_append)
 apply (simp only: i_take_i_drop)
 apply simp
 apply (rule_tac t=t in ssubst[OF i_expand_nth_interval_eq_replicate_NoMsg, rule_format], simp+)
 apply (simp add: f_Exec_State_Idle_replicate_NoMsg_state)
apply (subgoal_tac "t1 div k = t \<and> t2 div k = t", elim conjE)
 prefer 2
 apply (simp add: le_less_imp_div)
apply (simp only: i_expand_i_take_Suc i_expand_i_take_mult_Suc f_Exec_append)
apply (simp add: f_Exec_append)
apply (rule_tac m="t2 mod k" in f_Exec_State_Idle_replicate_NoMsg_gr_output, assumption)
apply (simp add: minus_div_mult_eq_mod [symmetric])
done

lemma i_Exec_Comp_Stream_Acc_Output__eq_Msg_before_State_Idle_conv2: "
  \<lbrakk> Suc 0 < k;
    State_Idle localState output_fun trans_fun (
      i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun input c t);
    m \<noteq> \<NoMsg>;
    t0 = t * k;
    s = i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c;
    \<box> t1 [0\<dots>, k - Suc 0] \<oplus> t0. \<not> (
      State_Idle localState output_fun trans_fun (localState (s t1)) \<and>
      output_fun (s t1) \<noteq> \<NoMsg>) \<rbrakk> \<Longrightarrow>
  (i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c t = m) =
  (\<diamond> t1 [0\<dots>, k - Suc 0] \<oplus> t0. (
     (output_fun (s t1) = m) \<and>
     (\<circle> t2 t1 [0\<dots>].
      ((output_fun (s t3) = \<NoMsg>. t3 \<U> t4 ([0\<dots>] \<oplus> t2).
      (output_fun (s t4) = \<NoMsg> \<and> State_Idle localState output_fun trans_fun (localState (s t4))))))))"
apply (rule iffI)
 apply (simp only: i_Exec_Stream_Acc_Output_nth i_Exec_Stream_nth)
 apply (simp only: iNext_def iFROM_iff iFROM_inext)
 apply (frule last_message_conv[THEN iffD1], assumption)
 apply (elim exE conjE, rename_tac i)
 apply (simp add: f_Exec_Stream_nth min_eqL del: f_Exec_Comp.simps f_Exec_Comp_Stream.simps de_Morgan_conj)
 apply (subgoal_tac "
   \<box> t' ([0\<dots>] \<oplus> (Suc (t * k + i))) \<down>< (t * k + k).
   output_fun (f_Exec_Comp trans_fun (input \<odot>\<^sub>i k \<Down> Suc t') c) = \<NoMsg>")
  prefer 2
  apply (rule iallI, rename_tac t')
  apply (simp only: iT_add iT_iff cut_less_mem_iff, erule conjE)
  apply (drule_tac x="t' - t * k" in spec)
  apply (subgoal_tac "t' - t * k < k")
   prefer 2
   apply simp
  apply (simp add: f_Exec_Stream_nth min_eqL del: f_Exec_Comp_Stream.simps de_Morgan_conj)
  apply (subgoal_tac "t * k \<le> t'")
   prefer 2
   apply simp
  apply (rule_tac t="Suc t'" and s="t * k + (Suc t' - t * k)" in subst, simp)
  apply (simp only: i_take_add f_Exec_append i_expand_i_take_mult)
  apply (simp add: i_take_i_drop)
  apply (rule ssubst[OF i_expand_nth_interval_eq_nth_append_replicate_NoMsg])
  apply (simp del: f_Exec_Comp_Stream.simps de_Morgan_conj)+
 apply (rule_tac t="t * k + i" in iexI)
  prefer 2
  apply (simp add: iT_add iT_iff)
 apply (rule conjI)
  apply (simp add: add_Suc_right[symmetric] i_expand_i_take_mult_Suc f_Exec_append del: add_Suc_right)
 apply (simp only: i_Exec_Stream_Acc_LocalState_nth i_expand_i_take_mult[symmetric] mult_Suc add.commute[of k])
 apply (subgoal_tac "
   \<not> State_Idle localState output_fun trans_fun
       (localState (f_Exec_Comp trans_fun (input \<odot>\<^sub>i k \<Down> (t * k + Suc i)) c))")
  prefer 2
  apply (drule_tac t="t * k + i" in ispec)
   apply (simp add: iT_add iT_iff)
  apply (simp add: add_Suc_right[symmetric] i_expand_i_take_mult_Suc f_Exec_append i_expand_i_take_mult del: add_Suc_right)
 apply (thin_tac "last_message x = m" for x)
 apply (drule_tac
   a="t * k + k" and b="t * k + Suc (k - Suc 0)" and
   P="\<lambda>x. State_Idle localState output_fun trans_fun
          (localState (f_Exec_Comp trans_fun (input \<odot>\<^sub>i k \<Down> x) c))" in back_subst, simp)
  apply (simp only: i_expand_i_take_mult_Suc f_Exec_append)
 apply (frule_tac n="k - Suc 0 - i" in State_Idle_imp_exists_state_change)
  apply (simp add: f_Exec_append[symmetric] replicate_add[symmetric])
 apply (elim exE conjE, rename_tac i1)
 apply (frule_tac i=i1 in less_diff_conv[THEN iffD1, rule_format])
 apply (drule_tac a=i1 and P="\<lambda>x. (x < k - Suc 0)" in subst[OF add.commute, rule_format])
 apply (frule Suc_less_pred_conv[THEN iffD2])
 apply (simp only: iUntil_def)
 apply (rule_tac t="t * k + Suc (i + i1)" in iexI)
  prefer 2
  apply (simp add: iT_add iT_iff)
 apply (rule conjI)
  apply (drule_tac t="t * k + Suc (i + i1)" in ispec)
   apply (simp add: iT_add iT_iff cut_less_mem_iff)
  apply (subgoal_tac "Suc (t * k + Suc (i + i1)) = t * k + Suc (Suc (i + i1))")
   prefer 2
   apply simp
  apply (simp only: i_expand_i_take_mult_Suc f_Exec_append)
  apply (simp add: add_Suc_right[symmetric] replicate_add f_Exec_append del: add_Suc_right replicate.simps)
 apply (clarsimp simp: cut_less_mem_iff iT_add iT_iff simp del: f_Exec_Comp_Stream.simps, rename_tac t')
 apply (subgoal_tac "\<exists>i'>i. t' = t * k + i'")
  prefer 2
  apply (rule_tac x="t' - t * k" in exI)
  apply simp
 apply (thin_tac "iAll I P" for I P)+
 apply (elim exE conjE)
 apply (subgoal_tac "i' < k")
  prefer 2
  apply simp
 apply (simp add: add_Suc_right[symmetric] i_expand_i_take_mult_Suc f_Exec_append f_Exec_Stream_nth min_eqL i_expand_i_take_mult del: add_Suc_right f_Exec_Comp_Stream.simps)
apply (elim iexE conjE, rename_tac t1)
apply (rule i_Exec_Comp_Stream_Acc_Output__eq_Msg_before_State_Idle_imp2, assumption+)
done

text \<open>Here the property to be checked uses only unbounded intervals suitable for LTL.\<close>
lemma i_Exec_Comp_Stream_Acc_Output__eq_Msg_before_State_Idle_imp: "
  \<lbrakk> Suc 0 < k;
    State_Idle localState output_fun trans_fun (
      i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun input c t);
    m \<noteq> \<NoMsg>;
    t0 = t * k;
    s = i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c;
    (\<not> State_Idle localState output_fun trans_fun (localState (s t1))). t1 \<U> t2 [0\<dots>] \<oplus> t0. (
    (output_fun (s t2) = m) \<and>
    (\<circle> t3 t2 [0\<dots>].
      ((output_fun (s t4) = \<NoMsg>. t4 \<U> t5 ([0\<dots>] \<oplus> t3).
       (output_fun (s t5) = \<NoMsg> \<and> State_Idle localState output_fun trans_fun (localState (s t5))))))) \<rbrakk> \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c t = m"
apply (case_tac "
  \<diamond> t1 [0\<dots>, k - Suc 0] \<oplus> t0. (
      State_Idle localState output_fun trans_fun (localState (s t1)) \<and>
      output_fun (s t1) \<noteq> \<NoMsg>)")
 apply (clarsimp, rename_tac t1)
 apply (frule i_Exec_Comp_Stream_Acc_Output__eq_Msg_with_State_Idle_imp[OF Suc_lessD refl refl], assumption+)
 apply (simp only: iNext_def iT_inext iT_iff iUntil_def)
 apply (elim iexE conjE, rename_tac t2 t3)
 apply (subgoal_tac "t2 \<le> t1")
  prefer 2
  apply (rule ccontr)
  apply (drule_tac t=t1 in ispec)
   apply (simp add: cut_less_mem_iff iT_add iT_iff)
  apply simp
 apply (thin_tac "iAll I P" for I P)
 apply (subgoal_tac "t1 \<le> t2")
  prefer 2
  apply (rule ccontr)
  apply (subgoal_tac "t3 < t1 \<longrightarrow> output_fun (i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c t1) = \<NoMsg>")
   prefer 2
   apply (rule impI)
   apply (subgoal_tac "t * k \<le> t3")
    prefer 2
    apply (simp add: iT_add iT_iff)
   apply (subgoal_tac "t1 div k = t \<and> t3 div k = t", elim conjE)
    prefer 2
    apply (simp add: iT_add iT_iff le_less_imp_div)
   apply (simp (no_asm_simp) add: i_Exec_Stream_nth i_expand_i_take_Suc f_Exec_append)
   apply (rule_tac m="t3 mod k" in f_Exec_State_Idle_replicate_NoMsg_gr_output[of localState output_fun trans_fun])
    apply (simp add: i_Exec_Stream_nth i_expand_i_take_Suc f_Exec_append)
   apply (simp add: minus_div_mult_eq_mod [symmetric])
  apply (case_tac "t1 < t3")
   apply (drule_tac t=t1 in ispec)
    apply (simp add: cut_less_mem_iff iT_add iT_iff)
   apply simp+
apply (rule ssubst[OF i_Exec_Comp_Stream_Acc_Output__eq_Msg_before_State_Idle_conv2], simp+)
apply (simp only: iNext_def iT_inext iT_iff iUntil_def)
apply (elim iexE conjE, rename_tac t1 t2)
apply (subgoal_tac "t1 \<le> t * k + (k - Suc 0)")
 prefer 2
 apply (rule ccontr)
 apply (simp add: i_Exec_Stream_Acc_LocalState_nth i_expand_i_take_mult[symmetric] add.commute[of k])
 apply (thin_tac "iAll I P" for I P)
 apply (drule_tac t="t * k + (k - Suc 0)" in ispec)
  apply (simp add: cut_less_mem_iff iT_add iT_iff)
 apply (simp add: i_Exec_Stream_nth)
apply (rule_tac t=t1 in iexI)
 prefer 2
 apply (simp add: iT_add iT_iff)
apply simp
apply (rule_tac t=t2 in iexI)
apply simp+
done
lemma i_Exec_Comp_Stream_Acc_Output__eq_Msg_before_State_Idle_conv: "
  \<lbrakk> Suc 0 < k;
    State_Idle localState output_fun trans_fun (
      i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun input c t);
    m \<noteq> \<NoMsg>;
    t0 = t * k;
    s = i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c;
    \<box> t1 [0\<dots>, k - Suc 0] \<oplus> t0. \<not> (
      State_Idle localState output_fun trans_fun (localState (s t1)) \<and>
      output_fun (s t1) \<noteq> \<NoMsg>) \<rbrakk> \<Longrightarrow>
  (i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c t = m) =
  ((\<not> State_Idle localState output_fun trans_fun (localState (s t1))). t1 \<U> t2 [0\<dots>] \<oplus> t0. (
     (output_fun (s t2) = m) \<and>
     (\<circle> t3 t2 [0\<dots>].
       ((output_fun (s t4) = \<NoMsg>. t4 \<U> t5 ([0\<dots>] \<oplus> t3).
        (output_fun (s t5) = \<NoMsg> \<and> State_Idle localState output_fun trans_fun (localState (s t5))))))))"
apply (rule iffI)
 apply (frule subst[OF i_Exec_Comp_Stream_Acc_Output__eq_Msg_before_State_Idle_conv2, where P="\<lambda>x. x"], assumption+)
 apply (simp only: iNext_def iT_inext iT_iff iUntil_def)
 apply (elim iexE conjE, rename_tac t1 t2)
 apply (rule_tac t=t1 in iexI)
  prefer 2
  apply (simp add: iT_add iT_iff)
 apply (intro conjI)
   apply simp
  apply (rule_tac t=t2 in iexI)
   prefer 2
   apply (simp add: iT_add iT_iff)
  apply simp
 apply (rule iallI, rename_tac t')
 apply (rule ccontr)
 apply (clarsimp simp: cut_less_mem_iff)
 apply (drule_tac i=t' in less_imp_add_positive)
 apply (elim exE conjE, rename_tac i)
 apply (drule_tac t=t1 in sym)
 apply (simp only: i_Exec_Stream_nth)
 apply (simp only: add_Suc[symmetric] i_take_add f_Exec_append)
 apply (simp only: i_take_i_drop)
 apply (subgoal_tac "i + Suc t' \<le> t * k + k")
  prefer 2
  apply (simp add: iT_add iT_iff)
 apply (simp only: iT_add iT_iff)
 apply (simp only: i_expand_nth_interval_eq_replicate_NoMsg[of k t, OF _ le_imp_less_Suc le_add2])
 apply (drule_tac c="f_Exec_Comp trans_fun (input \<odot>\<^sub>i k \<Down> Suc t') c" and n=i in f_Exec_State_Idle_replicate_NoMsg_gr0_output)
 apply simp+
apply (rule i_Exec_Comp_Stream_Acc_Output__eq_Msg_before_State_Idle_imp, simp+)
done

lemma i_Exec_Comp_Stream_Acc_Output__eq_Msg_State_Idle_conv2: "
  \<lbrakk> Suc 0 < k;
    State_Idle localState output_fun trans_fun (
      i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun input c t);
    m \<noteq> \<NoMsg>;
    t0 = t * k;
    s = i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c \<rbrakk> \<Longrightarrow>
  (i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c t = m) =
  (\<diamond> t1 [0\<dots>, k - Suc 0] \<oplus> t0. (
    output_fun (s t1) = m \<and>
    (State_Idle localState output_fun trans_fun (localState (s t1)) \<or>
    (\<circle> t2 t1 [0\<dots>].
      ((output_fun (s t3) = \<NoMsg>. t3 \<U> t4 ([0\<dots>] \<oplus> t2).
       (output_fun (s t4) = \<NoMsg> \<and> State_Idle localState output_fun trans_fun (localState (s t4)))))))))"
apply (subst conj_disj_distribL)
apply (case_tac "
  \<diamond> t1 [0\<dots>,k - Suc 0] \<oplus> t0.
    (State_Idle localState output_fun trans_fun (localState (s t1)) \<and> output_fun (s t1) \<noteq> \<NoMsg>)")
 apply (elim iexE conjE, rename_tac t1)
 apply (rule iffI)
  apply (frule i_Exec_Comp_Stream_Acc_Output__eq_Msg_with_State_Idle_conv2[THEN iffD1, OF Suc_lessD], assumption+)
  apply fastforce
 apply (elim iexE conjI, rename_tac t2)
 apply (erule disjE)
  apply (rule i_Exec_Comp_Stream_Acc_Output__eq_Msg_with_State_Idle_conv2[THEN iffD2], simp+)
  apply (rule_tac t=t2 in iexI, simp+)
 apply (rule_tac ?t1.0=t2 in i_Exec_Comp_Stream_Acc_Output__eq_Msg_before_State_Idle_imp2, simp+)
apply (rule ssubst[OF i_Exec_Comp_Stream_Acc_Output__eq_Msg_before_State_Idle_conv2[OF _ _ _ refl refl]], simp+)
apply fastforce
done

lemma i_Exec_Comp_Stream_Acc_Output__eq_Msg_State_Idle_conv2': "
  \<lbrakk> Suc 0 < k;
    State_Idle localState output_fun trans_fun (
      i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun input c t);
    m \<noteq> \<NoMsg>;
    t0 = t * k;
    s = i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c \<rbrakk> \<Longrightarrow>
  (i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c t = m) =
  ((\<diamond> t1 [0\<dots>, k - Suc 0] \<oplus> t0. (
      output_fun (s t1) = m \<and> State_Idle localState output_fun trans_fun (localState (s t1)))) \<or>
  (\<diamond> t1 [0\<dots>, k - Suc 0] \<oplus> t0. (
      ((output_fun (s t1) = m) \<and>
        (\<circle> t2 t1 [0\<dots>].
          ((output_fun (s t3) = \<NoMsg>. t3 \<U> t4 ([0\<dots>] \<oplus> t2).
           (output_fun (s t4) = \<NoMsg> \<and> State_Idle localState output_fun trans_fun (localState (s t4))))))))))"
apply (subst i_Exec_Comp_Stream_Acc_Output__eq_Msg_State_Idle_conv2, assumption+)
apply blast
done

lemma i_Exec_Comp_Stream_Acc_Output__eq_iAll_iUntil_State_Idle_conv2: "
  \<lbrakk> Suc 0 < k;
    State_Idle localState output_fun trans_fun (
      i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun input c t);
    t0 = t * k;
    s = i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c \<rbrakk> \<Longrightarrow>
  (i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c t = m) = (
  (m = \<NoMsg> \<longrightarrow>
    (output_fun (s t1) = \<NoMsg>. t1 \<U> t2 ([0\<dots>] \<oplus> t0). (
     output_fun (s t2) = \<NoMsg> \<and> State_Idle localState output_fun trans_fun (localState (s t2))))) \<and>
  (m \<noteq> \<NoMsg> \<longrightarrow>
    (\<diamond> t1 [0\<dots>, k - Suc 0] \<oplus> t0. (
      output_fun (s t1) = m \<and>
      (State_Idle localState output_fun trans_fun (localState (s t1)) \<or>
      (\<circle> t2 t1 [0\<dots>].
        ((output_fun (s t3) = \<NoMsg>. t3 \<U> t4 ([0\<dots>] \<oplus> t2).
         (output_fun (s t4) = \<NoMsg> \<and> State_Idle localState output_fun trans_fun (localState (s t4)))))))))))"
apply (case_tac "m = \<NoMsg>")
 apply (simp add: i_Exec_Comp_Stream_Acc_Output__eq_NoMsg_State_Idle_conv)
apply (simp add: i_Exec_Comp_Stream_Acc_Output__eq_Msg_State_Idle_conv2)
done

lemma i_Exec_Comp_Stream_Acc_Output__eq_Msg_State_Idle_conv': "
  \<lbrakk> Suc 0 < k;
    State_Idle localState output_fun trans_fun (
      i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun input c t);
    m \<noteq> \<NoMsg>;
    t0 = t * k;
    s = i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c \<rbrakk> \<Longrightarrow>
  (i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c t = m) =
  (((\<not> State_Idle localState output_fun trans_fun (localState (s t2))). t2 \<U> t1 [0\<dots>] \<oplus> t0.
    (output_fun (s t1) = m \<and> State_Idle localState output_fun trans_fun (localState (s t1)))) \<or>
  ((\<not> State_Idle localState output_fun trans_fun (localState (s t2))). t2 \<U> t1 [0\<dots>] \<oplus> t0.
   (output_fun (s t1) = m \<and>
   (\<circle> t3 t1 [0\<dots>].
     ((output_fun (s t4) = \<NoMsg>. t4 \<U> t5 ([0\<dots>] \<oplus> t3).
      (output_fun (s t5) = \<NoMsg> \<and> State_Idle localState output_fun trans_fun (localState (s t5)))))))))"
apply (case_tac "
  \<diamond> t1 [0\<dots>,k - Suc 0] \<oplus> t0.
    (State_Idle localState output_fun trans_fun (localState (s t1)) \<and> output_fun (s t1) \<noteq> \<NoMsg>)")
 apply (elim iexE conjE, rename_tac t1)
 apply (rule iffI)
  apply (frule i_Exec_Comp_Stream_Acc_Output__eq_Msg_with_State_Idle_conv[THEN iffD1, OF Suc_lessD], simp+)
 apply (erule disjE)
  apply (rule i_Exec_Comp_Stream_Acc_Output__eq_Msg_with_State_Idle_conv[THEN iffD2], simp+)
 apply (rule_tac i_Exec_Comp_Stream_Acc_Output__eq_Msg_before_State_Idle_imp, simp+)
apply (subst i_Exec_Comp_Stream_Acc_Output__eq_Msg_before_State_Idle_conv[OF _ _ _ refl refl], simp+)
apply (rule iffI)
 apply simp
apply (unfold iUntil_def, erule disjE)
 apply (elim iexE conjE, rename_tac t1)
 apply (case_tac "t1 \<le> t * k + (k - Suc 0)")
  prefer 2
  apply (simp add: i_Exec_Stream_Acc_LocalState_nth i_Exec_Stream_nth i_expand_i_take_mult[symmetric])
  apply (thin_tac "iAll I P" for I P)
  apply (drule_tac t="t * k + (k - Suc 0)" in ispec)
   apply (simp add: cut_less_mem_iff iT_add iT_iff)
  apply (simp add: add.commute[of k])
 apply (fastforce simp: iT_add iT_iff)+
done

lemma i_Exec_Comp_Stream_Acc_Output__eq_Msg_State_Idle_conv: "
  \<lbrakk> Suc 0 < k;
    State_Idle localState output_fun trans_fun (
      i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun input c t);
    m \<noteq> \<NoMsg>;
    t0 = t * k;
    s = i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c \<rbrakk> \<Longrightarrow>
  (i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c t = m) =
  (((\<not> State_Idle localState output_fun trans_fun (localState (s t2))). t2 \<U> t1 [0\<dots>] \<oplus> t0.
    (output_fun (s t1) = m \<and>
      (State_Idle localState output_fun trans_fun (localState (s t1)) \<or>
      (\<circle> t3 t1 [0\<dots>].
          ((output_fun (s t4) = \<NoMsg>. t4 \<U> t5 ([0\<dots>] \<oplus> t3).
           (output_fun (s t5) = \<NoMsg> \<and> State_Idle localState output_fun trans_fun (localState (s t5))))))))))"
apply (subst i_Exec_Comp_Stream_Acc_Output__eq_Msg_State_Idle_conv', assumption+)
apply (subst iUntil_disj_distrib[symmetric])
apply (rule iUntil_cong2)
apply blast
done

lemma i_Exec_Comp_Stream_Acc_Output__eq_iUntil_State_Idle_conv: "
  \<lbrakk> Suc 0 < k;
    State_Idle localState output_fun trans_fun (
      i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun input c t);
    t0 = t * k;
    s = i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c \<rbrakk> \<Longrightarrow>
  (i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c t = m) = (
  (m = \<NoMsg> \<longrightarrow>
    (output_fun (s t1) = \<NoMsg>. t1 \<U> t2 ([0\<dots>] \<oplus> t0). (
     output_fun (s t2) = \<NoMsg> \<and> State_Idle localState output_fun trans_fun (localState (s t2))))) \<and>
  (m \<noteq> \<NoMsg> \<longrightarrow>
    (((\<not> State_Idle localState output_fun trans_fun (localState (s t2))). t2 \<U> t1 [0\<dots>] \<oplus> t0.
      (output_fun (s t1) = m \<and>
        (State_Idle localState output_fun trans_fun (localState (s t1)) \<or>
        (\<circle> t3 t1 [0\<dots>].
            ((output_fun (s t4) = \<NoMsg>. t4 \<U> t5 ([0\<dots>] \<oplus> t3).
             (output_fun (s t5) = \<NoMsg> \<and> State_Idle localState output_fun trans_fun (localState (s t5))))))))))))"
apply (case_tac "m = \<NoMsg>")
 apply (simp add: i_Exec_Comp_Stream_Acc_Output__eq_NoMsg_State_Idle_conv)
apply (simp add: i_Exec_Comp_Stream_Acc_Output__eq_Msg_State_Idle_conv)
done


text \<open>Sufficient conditions for output messages.\<close>

corollary i_Exec_Comp_Stream_Acc_Output__eq_Msg_State_Idle_iEx_imp1: "
  \<lbrakk> Suc 0 < k;
    State_Idle localState output_fun trans_fun (
      i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun input c t);
    m \<noteq> \<NoMsg>;
    t0 = t * k;
    s = i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c;
    (\<diamond> t1 [0\<dots>, k - Suc 0] \<oplus> t0. (
       output_fun (s t1) = m \<and> State_Idle localState output_fun trans_fun (localState (s t1)))) \<rbrakk> \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c t = m"
by (blast intro: i_Exec_Comp_Stream_Acc_Output__eq_Msg_State_Idle_conv2'[THEN iffD2])

corollary i_Exec_Comp_Stream_Acc_Output__eq_Msg_State_Idle_iEx_imp2: "
  \<lbrakk> Suc 0 < k;
    State_Idle localState output_fun trans_fun (
      i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun input c t);
    m \<noteq> \<NoMsg>;
    t0 = t * k;
    s = i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c;
    \<diamond> t1 [0\<dots>, k - Suc 0] \<oplus> t0. (
          ((output_fun (s t1) = m) \<and>
            (\<circle> t2 t1 [0\<dots>].
              ((output_fun (s t3) = \<NoMsg>. t3 \<U> t4 ([0\<dots>] \<oplus> t2).
               (output_fun (s t4) = \<NoMsg> \<and> State_Idle localState output_fun trans_fun (localState (s t4)))))))) \<rbrakk> \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c t = m"
by (blast intro: i_Exec_Comp_Stream_Acc_Output__eq_Msg_State_Idle_conv2'[THEN iffD2])

lemma i_Exec_Comp_Stream_Acc_Output__eq_Msg_State_Idle_iUntil_imp1: "
  \<lbrakk> Suc 0 < k;
    State_Idle localState output_fun trans_fun (
      i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun input c t);
    m \<noteq> \<NoMsg>;
    t0 = t * k;
    s = i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c;
    (\<not> State_Idle localState output_fun trans_fun (localState (s t2))). t2 \<U> t1 [0\<dots>] \<oplus> t0.
    (output_fun (s t1) = m \<and> State_Idle localState output_fun trans_fun (localState (s t1))) \<rbrakk> \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c t = m"
by (blast intro: i_Exec_Comp_Stream_Acc_Output__eq_Msg_State_Idle_conv'[THEN iffD2])
lemma i_Exec_Comp_Stream_Acc_Output__eq_Msg_State_Idle_iUntil_imp2: "
  \<lbrakk> Suc 0 < k;
    State_Idle localState output_fun trans_fun (
      i_Exec_Comp_Stream_Acc_LocalState k localState trans_fun input c t);
    m \<noteq> \<NoMsg>;
    t0 = t * k;
    s = i_Exec_Comp_Stream trans_fun (input \<odot>\<^sub>i k) c;
    (\<not> State_Idle localState output_fun trans_fun (localState (s t2))). t2 \<U> t1 [0\<dots>] \<oplus> t0.
    (output_fun (s t1) = m \<and>
    (\<circle> t3 t1 [0\<dots>].
      ((output_fun (s t4) = \<NoMsg>. t4 \<U> t5 ([0\<dots>] \<oplus> t3).
       (output_fun (s t5) = \<NoMsg> \<and> State_Idle localState output_fun trans_fun (localState (s t5))))))) \<rbrakk> \<Longrightarrow>
  i_Exec_Comp_Stream_Acc_Output k output_fun trans_fun input c t = m"
by (blast intro: i_Exec_Comp_Stream_Acc_Output__eq_Msg_State_Idle_conv'[THEN iffD2])


text \<open>List of selected lemmas about output of accelerated components.\<close>

thm i_Exec_Comp_Stream_Acc_Output__eq_NoMsg_iAll_conv
thm i_Exec_Comp_Stream_Acc_Output__eq_Msg_iEx_iAll_cut_greater_conv
thm i_Exec_Comp_Stream_Acc_Output__eq_Msg_iSince_conv
thm i_Exec_Comp_Stream_Acc_Output__eq_iAll_iSince_conv

thm i_Exec_Comp_Stream_Acc_Output__eq_NoMsg_State_Idle_conv
thm i_Exec_Comp_Stream_Acc_Output__eq_Msg_State_Idle_conv2
thm i_Exec_Comp_Stream_Acc_Output__eq_Msg_State_Idle_conv
thm i_Exec_Comp_Stream_Acc_Output__eq_Msg_State_Idle_conv2'
thm i_Exec_Comp_Stream_Acc_Output__eq_Msg_State_Idle_conv'

thm i_Exec_Comp_Stream_Acc_Output__eq_iAll_iUntil_State_Idle_conv2
thm i_Exec_Comp_Stream_Acc_Output__eq_iUntil_State_Idle_conv

thm i_Exec_Comp_Stream_Acc_Output__eq_Msg_State_Idle_iEx_imp1
thm i_Exec_Comp_Stream_Acc_Output__eq_Msg_State_Idle_iEx_imp2
thm i_Exec_Comp_Stream_Acc_Output__eq_Msg_State_Idle_iUntil_imp1
thm i_Exec_Comp_Stream_Acc_Output__eq_Msg_State_Idle_iUntil_imp2

end
