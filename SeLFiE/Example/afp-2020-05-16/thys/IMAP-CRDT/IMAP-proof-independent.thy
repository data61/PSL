section \<open>Independence of IMAP Commands\<close>

text\<open>In this section we show that two concurrent operations that reference to the same tag must be 
identical.\<close>

theory
  "IMAP-proof-independent"
  imports
    "IMAP-def"
    "IMAP-proof-helpers"  
begin

lemma (in imap) Broadcast_Expunge_Deliver_prefix_closed:
  assumes "xs @ [Broadcast (i, Expunge e mo i)] prefix of j"
  shows "Deliver (mo, Append mo e) \<in> set xs \<or> 
    (\<exists> mo2 . Deliver (mo, Store e mo2 mo) \<in> set xs)"
proof -  
  obtain y where "apply_operations xs = Some y"
    using assms broadcast_only_valid_msgs by blast
  moreover hence "mo \<in> snd (y e)"
    using broadcast_only_valid_msgs[of xs "(i, Expunge e mo i)" j] 
      valid_behaviours_def[of y "(i, Expunge e mo i)"] assms by auto
  ultimately show ?thesis
    using assms Deliver_added_files apply_operations_added_files by blast
qed

lemma (in imap) Broadcast_Store_Deliver_prefix_closed:
  assumes "xs @ [Broadcast (i, Store e mo i)] prefix of j"
  shows "Deliver (mo, Append mo e) \<in> set xs \<or> 
    (\<exists> mo2 . Deliver (mo, Store e mo2 mo) \<in> set xs)"
proof -  
  obtain y where "apply_operations xs = Some y"
    using assms broadcast_only_valid_msgs by blast
  moreover hence "mo \<in> snd (y e)"
    using broadcast_only_valid_msgs[of xs "(i, Store e mo i)" j] 
      valid_behaviours_def[of y "(i, Store e mo i)"] assms by auto
  ultimately show ?thesis
    using assms Deliver_added_files apply_operations_added_files by blast
qed

lemma (in imap) Deliver_added_ids:
  assumes "xs prefix of j"
    and "i \<in> set (added_ids xs e)"
  shows "Deliver (i, Create i e) \<in> set xs \<or> 
    (\<exists> mo . Deliver (i, Expunge e mo i) \<in> set xs)"
  using assms proof (induct xs rule: rev_induct, clarsimp)
  case (snoc x xs) thus ?case
  proof (cases x, force)
    case X: (Deliver e')
    moreover obtain a b where "e' = (a, b)" by force
    ultimately show ?thesis
      using snoc apply (case_tac b; clarify)
          apply (simp, metis added_ids_Deliver_Create_diff_collapse 
          added_ids_Deliver_Create_same_collapse empty_iff list.set(1) set_ConsD create_id_valid 
          in_set_conv_decomp prefix_of_appendD, force)
      using append_id_valid apply (simp, metis (no_types, lifting)  prefix_of_appendD, simp, metis 
          Un_iff added_ids_Deliver_Expunge_diff_collapse added_ids_Deliver_Expunge_same_collapse 
          empty_iff expunge_id_valid list.set(1) list.set_intros(1) prefix_of_appendD set_ConsD 
          set_append)
      by (simp, blast)
  qed
qed

lemma (in imap) Broadcast_Deliver_prefix_closed:
  assumes "xs @ [Broadcast (r, Delete ix e)] prefix of j"
    and "i \<in> ix"
  shows "Deliver (i, Create i e) \<in> set xs \<or> 
    Deliver (i, Append i e) \<in> set xs \<or> 
    (\<exists> mo . Deliver (i, Expunge e mo i) \<in> set xs) \<or> 
    (\<exists> mo . Deliver (i, Store e mo i) \<in> set xs)"
proof -  
  obtain y where "apply_operations xs = Some y"
    using assms broadcast_only_valid_msgs by blast
  moreover hence "ix = fst (y e) \<union> snd (y e)"
    by (metis (mono_tags, lifting) assms(1) broadcast_only_valid_msgs operation.case(2)
        option.simps(1) valid_behaviours_def case_prodD)
  ultimately show ?thesis
    using assms Deliver_added_ids apply_operations_added_ids
    by (metis Deliver_added_files Un_iff apply_operations_added_files le_iff_sup prefix_of_appendD)
qed

lemma (in imap) concurrent_create_delete_independent_technical:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "(i, Create i e) \<in> set (node_deliver_messages xs)" 
    and "(ir, Delete is e) \<in> set (node_deliver_messages xs)"
  shows "hb (i, Create i e) (ir, Delete is e)"
proof -
  have f1: "Deliver (i, Create i e) \<in> set (history j)"
    using assms prefix_msg_in_history by blast
  obtain pre k where P: "pre@[Broadcast (ir, Delete is e)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  hence f2: "Deliver (i, Create i e) \<in> set pre \<or> 
                  Deliver (i, Append i e) \<in> set pre \<or> 
                  (\<exists> mo . Deliver (i, Expunge e mo i) \<in> set pre) \<or> 
                  (\<exists> mo . Deliver (i, Store e mo i) \<in> set pre)"
    using Broadcast_Deliver_prefix_closed assms by auto
  have f3: "Deliver (i, Append i e) \<notin> set pre" using f1 P 
    by (metis (full_types) Pair_inject fst_conv network.delivery_has_a_cause network.msg_id_unique 
        network_axioms operation.simps(9) prefix_elem_to_carriers prefix_of_appendD)
  have f4: "\<forall> mo . Deliver (i, Expunge e mo i) \<notin> set pre" using f1 P
    by (metis delivery_has_a_cause fst_conv msg_id_unique old.prod.inject operation.simps(11)
        prefix_elem_to_carriers prefix_of_appendD)
  have "\<forall> mo . Deliver (i, Store e mo i) \<notin> set pre" using f1 P
    by (metis delivery_has_a_cause fst_conv msg_id_unique old.prod.inject operation.simps(13)
        prefix_elem_to_carriers prefix_of_appendD) 
  thus ?thesis using f2 f3 f4  P events_in_local_order hb_deliver by blast
qed

lemma (in imap) concurrent_store_expunge_independent_technical:
  assumes "xs prefix of j"
    and "(i, Store e mo i) \<in> set (node_deliver_messages xs)" 
    and "(r, Expunge e i r) \<in> set (node_deliver_messages xs)"
  shows "hb (i, Store e mo i) (r, Expunge e i r)"
proof -
  obtain pre k where P: "pre@[Broadcast (r, Expunge e i r)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  moreover hence f1: "Deliver (i, Append i e) \<in> set pre \<or> 
  (\<exists> mo2 . Deliver (i, Store e mo2 i) \<in> set pre)"
    using Broadcast_Expunge_Deliver_prefix_closed assms(1) by auto
  hence f2: "Deliver (i, Append i e) \<notin> set (history k)"
    by (metis Pair_inject assms(1) assms(2) fst_conv msg_id_unique network.delivery_has_a_cause 
        network_axioms operation.distinct(17) prefix_msg_in_history)
  from f1 obtain mo2 :: 'a where
    "Deliver (i, Store e mo2 i) \<in> set (history k)" using f2
    using P prefix_elem_to_carriers by blast  
  hence "Deliver (i, Store e mo i) \<in> set (history k)" using assms f1 f2 P 
    by (metis fst_conv msg_id_unique network.delivery_has_a_cause network_axioms 
        prefix_msg_in_history)    
  then show ?thesis
    using hb.intros(2) events_in_local_order f1 f2 P
    by (metis delivery_has_a_cause fst_conv msg_id_unique node_histories.prefix_of_appendD 
        node_histories_axioms prefix_elem_to_carriers)
qed

lemma (in imap) concurrent_store_expunge_independent_technical2:
  assumes "xs prefix of j"
    and "(i, Store e1 mo2 i) \<in> set (node_deliver_messages xs)" 
    and "(r, Expunge e mo r) \<in> set (node_deliver_messages xs)"
  shows "mo2 \<noteq> r"
proof -
  obtain oid :: "'a \<times> ('a, 'b) operation \<Rightarrow> nat" where
    oid: "\<forall>p n. Deliver p \<notin> set (history n) \<or> Broadcast p \<in> set (history (oid p))"
    by (metis (no_types) delivery_has_a_cause)
  hence f1: "Broadcast (r, Expunge e mo r) \<in> set (history (oid (r, Expunge e mo r)))"
    using assms(1) assms(3) prefix_msg_in_history by blast
  obtain k :: "'a \<Rightarrow> 'b \<Rightarrow> ('a \<times> ('a, 'b) operation) event list \<Rightarrow> 'a" where k: 
    "\<forall>i e pre. (\<exists>mo. Deliver (i, Store e mo i) \<in> set pre) = 
    (Deliver (i, Store e (k i e pre) i) \<in> set pre)"
    by moura
  obtain pre :: "nat \<Rightarrow> ('a \<times> ('a, 'b) operation) event \<Rightarrow> ('a \<times> ('a, 'b) operation) event list" 
    where pre: "\<forall>k op1. (\<exists>op2. op2 @ [op1] prefix of k) = (pre k op1 @ [op1] prefix of k)"
    by moura
  hence f2: "\<forall>e n. e \<notin> set (history n) \<or> pre n e @ [e] prefix of n"
    using events_before_exist by simp
  hence f3: "pre (oid (i, Store e1 mo2 i)) (Broadcast (i, Store e1 mo2 i))
  prefix of oid (i, Store e1 mo2 i)"
    using oid  assms(1) assms(2) prefix_msg_in_history by blast
  have f4: "Deliver (r, Append r e1) \<notin> set (history (oid (i, Store e1 mo2 i)))"
    by (metis (no_types) oid f1 fst_conv msg_id_unique old.prod.inject operation.distinct(15))
  have "Deliver (r, Store e1 (k r e1 (pre (oid (i, Store e1 mo2 i)) 
  (Broadcast (i, Store e1 mo2 i)))) r) \<notin> set (history (oid (i, Store e1 mo2 i)))"
    by (metis (no_types) oid f1 fst_conv msg_id_unique old.prod.inject operation.distinct(19))
  thus ?thesis using oid k f2 f3 f4 assms
    by (metis (no_types, lifting) Broadcast_Store_Deliver_prefix_closed 
        network.prefix_msg_in_history network_axioms prefix_elem_to_carriers)
qed

lemma (in imap) concurrent_store_delete_independent_technical:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "(i, Store e mo i) \<in> set (node_deliver_messages xs)" 
    and "(ir, Delete is e) \<in> set (node_deliver_messages xs)"
  shows "hb (i, Store e mo i) (ir, Delete is e)"
proof -
  have f1: "Deliver (i, Store e mo i) \<in> set (history j)" using assms prefix_msg_in_history by auto
  obtain pre k where P: "pre@[Broadcast (ir, Delete is e)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  hence f2: "Deliver (i, Create i e) \<in> set pre \<or> 
  Deliver (i, Append i e) \<in> set pre \<or>
  (\<exists> mo . Deliver (i, Expunge e mo i) \<in> set pre) \<or> 
  (\<exists> mo . Deliver (i, Store e mo i) \<in> set pre)"  
    using Broadcast_Deliver_prefix_closed assms(1) by auto    
  have f3: "Deliver (i, Create i e) \<notin> set pre" using f1 P 
    by (metis Pair_inject delivery_has_a_cause fst_conv msg_id_unique operation.distinct(7) 
        prefix_elem_to_carriers prefix_of_appendD)
  have f4: "Deliver (i, Append i e) \<notin> set pre" using f1 P
    by (metis delivery_has_a_cause fst_conv msg_id_unique operation.distinct(17) 
        prefix_elem_to_carriers prefix_of_appendD prod.inject)
  have "\<forall> mo . Deliver (i, Expunge e mo i) \<notin> set pre" using f1 P
    by (metis Pair_inject delivery_has_a_cause fst_conv msg_id_unique operation.simps(25) 
        prefix_elem_to_carriers prefix_of_appendD)
  hence "Deliver (i, Store e mo i) \<in> set pre" using f1 f2 f3 f4 P
    by (metis delivery_has_a_cause fst_conv msg_id_unique node_histories.prefix_of_appendD 
        node_histories_axioms prefix_elem_to_carriers)     
  thus ?thesis using P events_in_local_order hb_deliver by blast
qed

lemma (in imap) concurrent_append_delete_independent_technical:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "(i, Append i e) \<in> set (node_deliver_messages xs)" 
    and "(ir, Delete is e) \<in> set (node_deliver_messages xs)"
  shows "hb (i, Append i e) (ir, Delete is e)"
proof -
  obtain pre k where P: "pre@[Broadcast (ir, Delete is e)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  hence f1: "Deliver (i, Create i e) \<in> set pre \<or> 
  Deliver (i, Append i e) \<in> set pre \<or> 
  (\<exists> mo . Deliver (i, Expunge e mo i) \<in> set pre) \<or> 
  (\<exists> mo . Deliver (i, Store e mo i) \<in> set pre)"
    using Broadcast_Deliver_prefix_closed assms(1) by auto
  hence "Deliver (i, Append i e) \<in> set pre" using assms P f1
    by (metis (no_types, hide_lams) delivery_has_a_cause events_in_local_order fst_conv 
        hb_broadcast_exists1 hb_deliver msg_id_unique prefix_msg_in_history)
  thus ?thesis using P events_in_local_order hb_deliver by blast
qed

lemma (in imap) concurrent_append_expunge_independent_technical:
  assumes "i = mo"
    and "xs prefix of j"
    and "(i, Append i e) \<in> set (node_deliver_messages xs)" 
    and "(r, Expunge e mo r) \<in> set (node_deliver_messages xs)"
  shows "hb (i, Append i e) (r, Expunge e mo r)"
proof -
  obtain pre k where P: "pre@[Broadcast (r, Expunge e mo r)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  hence f1: "Deliver (mo, Append mo e) \<in> set pre \<or> 
  (\<exists> mo2 . Deliver (mo, Store e mo2 mo) \<in> set pre)"
    using Broadcast_Expunge_Deliver_prefix_closed assms(1) by auto
  hence "(\<forall> mo2 . Deliver (mo, Store e mo2 mo) \<notin> set pre)" using P assms 
  proof -
    have "Deliver (mo, Append mo e) \<in> set (history j)"
      using assms(1) assms(2) assms(3) prefix_msg_in_history by blast
    thus ?thesis
      by (metis (no_types) P Pair_inject delivery_has_a_cause fst_conv msg_id_unique 
          operation.simps(23) prefix_elem_to_carriers prefix_of_appendD)
  qed
  thus ?thesis
    using hb.intros(2) events_in_local_order assms(1) P f1 by blast
qed

lemma (in imap) concurrent_append_store_independent_technical:
  assumes "i = mo"
    and "xs prefix of j"
    and "(i, Append i e) \<in> set (node_deliver_messages xs)" 
    and "(r, Store e mo r) \<in> set (node_deliver_messages xs)"
  shows "hb (i, Append i e) (r, Store e mo r)"
proof -
  obtain pre k where pre: "pre@[Broadcast (r, Store e mo r)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  moreover hence f1: "Deliver (mo, Append mo e) \<in> set pre \<or> 
  (\<exists> mo2 . Deliver (mo, Store e mo2 mo) \<in> set pre)"
    using Broadcast_Store_Deliver_prefix_closed assms(1) by auto
  have f2: "Deliver (i, Append i e) \<in> set (history j)"
    by (meson assms network.prefix_msg_in_history network_axioms)
  then show ?thesis using assms f1 
    by (metis  pre delivery_has_a_cause events_in_local_order fst_conv hb_deliver 
        msg_id_unique node_histories.prefix_of_appendD node_histories_axioms 
        prefix_elem_to_carriers)
qed

lemma (in imap) concurrent_expunge_delete_independent_technical:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "(i, Expunge e mo i) \<in> set (node_deliver_messages xs)" 
    and "(ir, Delete is e) \<in> set (node_deliver_messages xs)"
  shows "hb (i, Expunge e mo i) (ir, Delete is e)"
proof -
  obtain pre k where pre: "pre@[Broadcast (ir, Delete is e)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  moreover hence A: "Deliver (i, Create i e) \<in> set pre \<or> 
  Deliver (i, Append i e) \<in> set pre \<or> 
  (\<exists> mo . Deliver (i, Expunge e mo i) \<in> set pre) \<or> 
  (\<exists> mo . Deliver (i, Store e mo i) \<in> set pre)"
    using Broadcast_Deliver_prefix_closed assms(1) by auto      
  hence "Deliver (i, Expunge e mo i) \<in> set pre" using assms
  proof -
    have f1: "\<And>e. e \<notin> set pre \<or> e \<in> set (history k)"
      using pre prefix_elem_to_carriers by blast
    have f2: "Deliver (i, Expunge e mo i) \<in> set (history j)"
      by (meson assms network.prefix_msg_in_history network_axioms)
    then show ?thesis using f1 A 
      by (metis (no_types, lifting) fst_conv msg_id_unique network.delivery_has_a_cause 
          network_axioms)
  qed     
  ultimately show ?thesis
    using hb.intros(2) events_in_local_order by blast
qed

lemma (in imap) concurrent_store_store_independent_technical:
  assumes "xs prefix of j"
    and "(i, Store e mo i) \<in> set (node_deliver_messages xs)" 
    and "(r, Store e i r) \<in> set (node_deliver_messages xs)"
  shows "hb (i, Store e mo i) (r, Store e i r)"
proof -
  obtain pre k where P: "pre@[Broadcast (r, Store e i r)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  hence f1: "\<forall>e. e \<notin> set pre \<or> e \<in> set (history k)"
    using prefix_elem_to_carriers by blast
  have f2: "Deliver (i, Append i e) \<in> set pre \<or> (\<exists> mo2 . Deliver (i, Store e mo2 i) \<in> set pre)"
    using Broadcast_Store_Deliver_prefix_closed assms(1) P by auto     
  hence "Deliver (i, Store e mo i) \<in> set pre" using assms f1 
    by (metis delivery_has_a_cause fst_conv msg_id_unique prefix_msg_in_history)
  then show ?thesis
    using hb.intros(2) events_in_local_order P by blast
qed

lemma (in imap) expunge_delete_tag_causality:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "(i, Expunge e1 mo i) \<in> set (node_deliver_messages xs)" 
    and "(ir, Delete is e2) \<in> set (node_deliver_messages xs)" 
    and "pre@[Broadcast (ir, Delete is e2)] prefix of k"
  shows "Deliver (i, Expunge e2 mo i) \<in> set (history k)"
proof- 
  have f1: "Deliver (i, Append i e2) \<notin> set (history k)" using assms
    by (metis fst_conv msg_id_unique network.delivery_has_a_cause network_axioms old.prod.inject 
        operation.distinct(15) prefix_msg_in_history)
  have f2: "Deliver (i, Create i e2) \<notin> set (history k)" using assms
    by (metis fst_conv msg_id_unique network.delivery_has_a_cause network_axioms old.prod.inject 
        operation.distinct(5) prefix_msg_in_history)
  have f3: "\<forall> mo. Deliver (i, Store e2 mo i) \<notin> set (history k)" using assms
    by (metis Pair_inject fst_conv msg_id_unique network.delivery_has_a_cause network_axioms 
        operation.simps(25) prefix_msg_in_history)
  hence "\<exists> mo1. Deliver (i, Expunge e2 mo1 i) \<in> set (history k)" using assms f1 f2 
    by (meson imap.Broadcast_Deliver_prefix_closed imap_axioms node_histories.prefix_of_appendD 
        node_histories_axioms prefix_elem_to_carriers)
  then obtain mo1 :: 'a where
    "Deliver (i, Expunge e2 mo1 i) \<in> set (history k)" by blast
  then show ?thesis  using assms f1 f2 f3
    by (metis fst_conv msg_id_unique network.delivery_has_a_cause network_axioms old.prod.inject 
        operation.inject(4) prefix_msg_in_history)
qed

lemma (in imap) expunge_delete_ids_imply_messages_same:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "(i, Expunge e1 mo i) \<in> set (node_deliver_messages xs)" 
    and "(ir, Delete is e2) \<in> set (node_deliver_messages xs)"
  shows "e1 = e2"
proof -
  obtain pre k where P: "pre@[Broadcast (ir, Delete is e2)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast  
  hence "Deliver (i, Expunge e2 mo i) \<in> set (history k)" using assms expunge_delete_tag_causality
    by blast
  then show ?thesis using assms
    by (metis delivery_has_a_cause fst_conv network.msg_id_unique network_axioms 
        operation.inject(4) prefix_msg_in_history prod.inject)
qed

lemma (in imap) store_delete_ids_imply_messages_same:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "(i, Store e1 mo i) \<in> set (node_deliver_messages xs)" 
    and "(ir, Delete is e2) \<in> set (node_deliver_messages xs)"
  shows "e1 = e2"
proof -
  obtain pre k where P: "pre@[Broadcast (ir, Delete is e2)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast 
  have f1: "Deliver (i, Append i e2) \<notin> set (history k)" using assms
    by (metis fst_conv msg_id_unique network.delivery_has_a_cause network_axioms old.prod.inject 
        operation.distinct(17) prefix_msg_in_history)
  have f2: "\<forall> mo. Deliver (i, Expunge e2 mo i) \<notin> set (history k)" using assms
    by (metis Pair_inject fst_conv msg_id_unique network.delivery_has_a_cause network_axioms 
        operation.distinct(19) prefix_msg_in_history)
  have f3: "Deliver (i, Create i e2) \<notin> set (history k)" using assms
    by (metis fst_conv msg_id_unique network.delivery_has_a_cause network_axioms old.prod.inject 
        operation.distinct(8) prefix_msg_in_history)
  hence "(\<exists> mo1. Deliver (i, Store e2 mo1 i) \<in> set pre)" using assms P f1 f2 imap_axioms 
    by (meson imap.Broadcast_Deliver_prefix_closed prefix_elem_to_carriers prefix_of_appendD)
  then obtain mo1 :: 'a where
    f3: "Deliver (i, Store e2 mo1 i) \<in> set pre" by blast
  then have f4: "Deliver (i, Store e2 mo1 i) \<in> set (history k)"
    using P prefix_elem_to_carriers by blast 
  hence "Deliver (i, Store e2 mo i) \<in> set pre" using f2 f3 assms 
    by (metis fst_conv msg_id_unique network.delivery_has_a_cause network_axioms old.prod.inject 
        operation.inject(5) prefix_msg_in_history)
  moreover have "Deliver(i, Store e1 mo i) \<in> set (history j)"
    using assms(2) assms(3) prefix_msg_in_history by blast 
  ultimately show ?thesis using f4
    by (metis delivery_has_a_cause fst_conv msg_id_unique old.prod.inject operation.inject(5))
qed

lemma (in imap) create_delete_ids_imply_messages_same:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "(i, Create i e1) \<in> set (node_deliver_messages xs)" 
    and "(ir, Delete is e2) \<in> set (node_deliver_messages xs)"
  shows "e1 = e2"
proof -
  obtain pre k where P: "pre@[Broadcast (ir, Delete is e2)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast
  have f1: "Deliver (i, Append i e2) \<notin> set (history k)"
    by (metis assms(2) assms(3) delivery_has_a_cause fst_conv network.msg_id_unique 
        network.prefix_msg_in_history network_axioms operation.distinct(3) prod.inject)
  have f2: "\<forall> mo. Deliver (i, Expunge e2 mo i) \<notin> set (history k)"
    by (metis assms(2) assms(3) fst_conv msg_id_unique network.delivery_has_a_cause network_axioms 
        old.prod.inject operation.distinct(5) prefix_msg_in_history)
  have f3: "\<forall> mo. Deliver (i, Store e2 mo i) \<notin> set (history k)"
    by (metis Pair_inject assms(2) assms(3) delivery_has_a_cause fst_conv msg_id_unique 
        operation.distinct(7) prefix_msg_in_history)
  hence "Deliver (i, Create i e2) \<in> set pre" using assms P f2 f1 imap_axioms
    by (meson imap.Broadcast_Deliver_prefix_closed  prefix_elem_to_carriers prefix_of_appendD)
  then show ?thesis using f1 f2 f3
    by (metis (no_types, lifting) P assms(2) assms(3) delivery_has_a_cause fst_conv msg_id_unique 
        node_histories.prefix_of_appendD node_histories_axioms old.prod.inject operation.inject(1) 
        prefix_elem_to_carriers prefix_msg_in_history)
qed

lemma (in imap) append_delete_ids_imply_messages_same:
  assumes "i \<in> is"
    and "xs prefix of j"
    and "(i, Append i e1) \<in> set (node_deliver_messages xs)" 
    and "(ir, Delete is e2) \<in> set (node_deliver_messages xs)"
  shows "e1 = e2"
proof -
  obtain pre k where P: "pre@[Broadcast (ir, Delete is e2)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast  
  hence f1: "\<And>e. e \<in> set pre \<Longrightarrow> e \<in> set (history k)" using prefix_elem_to_carriers by blast
  have f2: "Deliver (i, Create i e2) \<notin> set pre" using P f1
    by (metis assms(2) assms(3) fst_conv msg_id_unique network.delivery_has_a_cause network_axioms 
        old.prod.inject operation.distinct(3) prefix_msg_in_history)
  moreover have D1: "\<forall> mo. Deliver (i, Expunge e2 mo i) \<notin> set pre" using P f1
    by (metis Pair_inject assms(2) assms(3) fst_conv msg_id_unique network.delivery_has_a_cause 
        network_axioms operation.distinct(15) prefix_msg_in_history)
  moreover have D2: "\<forall> mo. Deliver (i, Store e2 mo i) \<notin> set pre" using P f1
    by (metis Pair_inject assms(2) assms(3) fst_conv msg_id_unique network.delivery_has_a_cause 
        network_axioms operation.simps(23) prefix_msg_in_history)
  moreover hence "Deliver (i, Append i e2) \<in> set pre" 
    using P D1 D2 f2 assms(1) Broadcast_Deliver_prefix_closed by blast
  moreover have "Deliver (i, Append i e1) \<in> set (history j)"
    using assms(2) assms(3) prefix_msg_in_history by blast
  ultimately show ?thesis using assms 
    by (metis f1 msg_id_unique network.delivery_has_a_cause network_axioms old.prod.inject 
        operation.inject(3) prod.sel(1))
qed

lemma (in imap) append_expunge_ids_imply_messages_same:
  assumes "i = mo"
    and "xs prefix of j"
    and "(i, Append i e1) \<in> set (node_deliver_messages xs)" 
    and "(r, Expunge e2 mo r) \<in> set (node_deliver_messages xs)"
  shows "e1 = e2"
proof -
  obtain pre k where pre: "pre@[Broadcast (r, Expunge e2 mo r)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast  
  moreover hence "Deliver (mo, Append mo e2) \<in> set pre \<or> 
  (\<exists> mo2 . Deliver (mo, Store e2 mo2 mo) \<in> set pre)"
    using Broadcast_Expunge_Deliver_prefix_closed assms(1)
    by (meson imap.Broadcast_Deliver_prefix_closed imap_axioms)      
  hence "Deliver (i, Append i e2) \<in> set pre" using assms
    by (metis (no_types, lifting) pre delivery_has_a_cause fst_conv hb_broadcast_exists1 
        msg_id_unique network.hb_deliver network.prefix_msg_in_history network_axioms 
        node_histories.events_in_local_order node_histories_axioms operation.distinct(17) 
        prod.inject)     
  moreover have "Deliver (i, Append i e1) \<in> set (history j)"
    using assms(2) assms(3) prefix_msg_in_history by blast
  ultimately show ?thesis
    by (metis (no_types, lifting) fst_conv network.delivery_has_a_cause network.msg_id_unique 
        network_axioms operation.inject(3) prefix_elem_to_carriers prefix_of_appendD prod.inject)
qed

lemma (in imap) append_store_ids_imply_messages_same:
  assumes "i = mo"
    and "xs prefix of j"
    and "(i, Append i e1) \<in> set (node_deliver_messages xs)" 
    and "(r, Store e2 mo r) \<in> set (node_deliver_messages xs)"
  shows "e1 = e2"
proof -
  obtain pre k where P: "pre@[Broadcast (r, Store e2 mo r)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast  
  moreover hence A: "Deliver (mo, Append mo e2) \<in> set pre \<or> 
  (\<exists> mo2 . Deliver (mo, Store e2 mo2 mo) \<in> set pre)"
    using Broadcast_Store_Deliver_prefix_closed assms(1)
    by (meson imap.Broadcast_Deliver_prefix_closed imap_axioms)
  have f1: "Deliver (i, Append i e1) \<in> set (history j)"
    using assms(2) assms(3) prefix_msg_in_history by blast
  hence "Deliver (i, Append i e2) \<in> set pre" using assms P A
    by (metis Pair_inject assms(1) P delivery_has_a_cause fst_conv msg_id_unique 
        operation.simps(23) prefix_elem_to_carriers prefix_of_appendD)
  then show ?thesis using f1
    by (metis P delivery_has_a_cause fst_conv msg_id_unique 
        node_histories.prefix_of_appendD node_histories_axioms operation.inject(3) 
        prefix_elem_to_carriers prod.inject)
qed

lemma (in imap) expunge_store_ids_imply_messages_same:
  assumes "xs prefix of j"
    and "(i, Store e1 mo i) \<in> set (node_deliver_messages xs)" 
    and "(r, Expunge e2 i r) \<in> set (node_deliver_messages xs)"
  shows "e1 = e2"
proof -
  obtain pre k where P: "pre@[Broadcast (r, Expunge e2 i r)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast 
  hence pprefix: "pre prefix of k"
    using P by blast
  have A: "Deliver (i, Append i e2) \<in> set pre \<or> 
  (\<exists> mo2 . Deliver (i, Store e2 mo2 i) \<in> set pre)"
    using Broadcast_Expunge_Deliver_prefix_closed assms(1) P by blast      
  have "Deliver (i, Store e2 mo i) \<in> set pre" using assms A P
  proof -
    obtain op1 :: "'a \<times> ('a, 'b) operation \<Rightarrow> nat" where
      f1: "Broadcast (i, Store e1 mo i) \<in> set (history (op1 (i, Store e1 mo i)))"
      by (meson assms(1) assms(2) delivery_has_a_cause prefix_msg_in_history)
    then show ?thesis 
      using f1 A pprefix delivery_has_a_cause network.msg_id_unique network_axioms 
        node_histories.prefix_to_carriers node_histories_axioms 
      by fastforce
  qed
  moreover have "Deliver (i, Store e1 mo i) \<in> set (history j)"
    using assms(1) assms(2) prefix_msg_in_history by auto
  ultimately show ?thesis using assms P
    by (metis delivery_has_a_cause fst_conv msg_id_unique operation.inject(5) 
        prefix_elem_to_carriers prefix_of_appendD prod.inject) 
qed

lemma (in imap) store_store_ids_imply_messages_same:
  assumes "xs prefix of j"
    and "(i, Store e1 mo i) \<in> set (node_deliver_messages xs)" 
    and "(r, Store e2 i r) \<in> set (node_deliver_messages xs)"
  shows "e1 = e2"
proof -
  obtain pre k where P: "pre@[Broadcast (r, Store e2 i r)] prefix of k"
    using assms delivery_has_a_cause events_before_exist prefix_msg_in_history by blast  
  moreover hence A: "Deliver (i, Append i e2) \<in> set pre \<or>
    (\<exists> mo2 . Deliver (i, Store e2 mo2 i) \<in> set pre)"
    using Broadcast_Store_Deliver_prefix_closed assms(1) by blast
  have "\<forall>e. e \<notin> set pre \<or> e \<in> set (history k)"
    using P prefix_elem_to_carriers by auto
  hence "Deliver (i, Store e2 mo i) \<in> set pre" 
    by (metis A assms(1) assms(2) delivery_has_a_cause fst_conv msg_id_unique 
        operation.distinct(17) operation.inject(5) prefix_msg_in_history prod.inject)
  moreover have "Deliver (i, Store e1 mo i) \<in> set (history j)"
    using assms(1) assms(2) prefix_msg_in_history by auto
  ultimately show ?thesis using assms
    by (metis Pair_inject delivery_has_a_cause msg_id_unique operation.simps(5) 
        prefix_elem_to_carriers prefix_of_appendD prod.sel(1))
qed 

end
