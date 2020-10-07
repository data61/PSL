section \<open>Convergence of the IMAP-CRDT\<close>

text\<open>In this final section show that concurrent updates commute and thus Strong Eventual 
Convergence is achieved.\<close>

theory
  "IMAP-proof"
  imports
    "IMAP-def"
    "IMAP-proof-commute"
    "IMAP-proof-helpers"
    "IMAP-proof-independent"
begin

corollary (in imap) concurrent_create_delete_independent:
  assumes "\<not> hb (i, Create i e1) (ir, Delete is e2)" 
    and "\<not> hb (ir, Delete is e2) (i, Create i e1)"
    and "xs prefix of j"
    and "(i, Create i e1) \<in> set (node_deliver_messages xs)" 
    and "(ir, Delete is e2) \<in> set (node_deliver_messages xs)"
  shows "i \<notin> is"
  using assms create_delete_ids_imply_messages_same concurrent_create_delete_independent_technical 
  by fastforce

corollary (in imap) concurrent_append_delete_independent:
  assumes "\<not> hb (i, Append i e1) (ir, Delete is e2)" 
    and "\<not> hb (ir, Delete is e2) (i, Append i e1)"
    and "xs prefix of j"
    and "(i, Append i e1) \<in> set (node_deliver_messages xs)" 
    and "(ir, Delete is e2) \<in> set (node_deliver_messages xs)"
  shows "i \<notin> is"
  using assms append_delete_ids_imply_messages_same concurrent_append_delete_independent_technical 
  by fastforce

corollary (in imap) concurrent_append_expunge_independent:
  assumes "\<not> hb (i, Append i e1) (r, Expunge e2 mo r)" 
    and "\<not> hb (r, Expunge e2 mo r) (i, Append i e1)"
    and "xs prefix of j"
    and "(i, Append i e1) \<in> set (node_deliver_messages xs)" 
    and "(r, Expunge e2 mo r) \<in> set (node_deliver_messages xs)"
  shows "i \<noteq> mo"
  using assms append_expunge_ids_imply_messages_same concurrent_append_expunge_independent_technical 
  by fastforce

corollary (in imap) concurrent_append_store_independent:
  assumes "\<not> hb (i, Append i e1) (r, Store e2 mo r)" 
    and "\<not> hb (r, Store e2 mo r) (i, Append i e1)"
    and "xs prefix of j"
    and "(i, Append i e1) \<in> set (node_deliver_messages xs)" 
    and "(r, Store e2 mo r) \<in> set (node_deliver_messages xs)"
  shows "i \<noteq> mo"
  using assms append_store_ids_imply_messages_same concurrent_append_store_independent_technical 
  by fastforce

corollary (in imap) concurrent_expunge_delete_independent:
  assumes "\<not> hb (i, Expunge e1 mo i) (ir, Delete is e2)" 
    and "\<not> hb (ir, Delete is e2) (i, Expunge e1 mo i)"
    and "xs prefix of j"
    and "(i, Expunge e1 mo i) \<in> set (node_deliver_messages xs)" 
    and "(ir, Delete is e2) \<in> set (node_deliver_messages xs)"
  shows "i \<notin> is"
  using assms expunge_delete_ids_imply_messages_same concurrent_expunge_delete_independent_technical 
  by fastforce

corollary (in imap) concurrent_store_delete_independent:
  assumes "\<not> hb (i, Store e1 mo i) (ir, Delete is e2)" 
    and "\<not> hb (ir, Delete is e2) (i, Store e1 mo i)"
    and "xs prefix of j"
    and "(i, Store e1 mo i) \<in> set (node_deliver_messages xs)" 
    and "(ir, Delete is e2) \<in> set (node_deliver_messages xs)"
  shows "i \<notin> is"
  using assms store_delete_ids_imply_messages_same concurrent_store_delete_independent_technical 
  by fastforce

corollary (in imap) concurrent_store_expunge_independent:
  assumes "\<not> hb (i, Store e1 mo i) (r, Expunge e2 mo2 r)" 
    and "\<not> hb (r, Expunge e2 mo2 r) (i, Store e1 mo i)"
    and "xs prefix of j"
    and "(i, Store e1 mo i) \<in> set (node_deliver_messages xs)" 
    and "(r, Expunge e2 mo2 r) \<in> set (node_deliver_messages xs)"
  shows "i \<noteq> mo2 \<and> r \<noteq> mo"
  using assms expunge_store_ids_imply_messages_same concurrent_store_expunge_independent_technical2 
    concurrent_store_expunge_independent_technical by metis


corollary (in imap) concurrent_store_store_independent:
  assumes "\<not> hb (i, Store e1 mo i) (r, Store e2 mo2 r)" 
    and "\<not> hb (r, Store e2 mo2 r) (i, Store e1 mo i)"
    and "xs prefix of j"
    and "(i, Store e1 mo i) \<in> set (node_deliver_messages xs)" 
    and "(r, Store e2 mo2 r) \<in> set (node_deliver_messages xs)"
  shows "i \<noteq> mo2 \<and> r \<noteq> mo"
  using assms store_store_ids_imply_messages_same concurrent_store_store_independent_technical 
  by metis

lemma (in imap) concurrent_operations_commute:
  assumes "xs prefix of i"
  shows "hb.concurrent_ops_commute (node_deliver_messages xs)"                     
proof -
  { fix a b x y
    assume "(a, b) \<in> set (node_deliver_messages xs)"
      "(x, y) \<in> set (node_deliver_messages xs)"
      "hb.concurrent (a, b) (x, y)"
    hence "interp_msg (a, b) \<rhd> interp_msg (x, y) = interp_msg (x, y) \<rhd> interp_msg (a, b)" 
      apply(unfold interp_msg_def, case_tac "b"; case_tac "y"; 
          simp add: create_create_commute delete_delete_commute append_append_commute 
          create_append_commute create_expunge_commute create_store_commute 
          expunge_expunge_commute hb.concurrent_def)
      using assms prefix_contains_msg apply (metis (full_types) 
          create_id_valid create_delete_commute concurrent_create_delete_independent)
      using assms prefix_contains_msg apply (metis (full_types) 
          create_id_valid create_delete_commute concurrent_create_delete_independent)
      using assms prefix_contains_msg apply (metis 
          append_id_valid append_delete_ids_imply_messages_same 
          concurrent_append_delete_independent_technical delete_append_commute)
      using assms prefix_contains_msg apply (metis 
          concurrent_expunge_delete_independent expunge_id_valid imap.delete_expunge_commute 
          imap_axioms)
      using assms prefix_contains_msg apply (metis 
          concurrent_store_delete_independent delete_store_commute store_id_valid)
      using assms prefix_contains_msg apply (metis 
          append_id_valid append_delete_ids_imply_messages_same 
          concurrent_append_delete_independent_technical delete_append_commute)
      using assms prefix_contains_msg apply (metis 
          append_id_valid expunge_id_valid append_expunge_ids_imply_messages_same 
          concurrent_append_expunge_independent_technical append_expunge_commute)
      using assms prefix_contains_msg apply (metis 
          append_id_valid append_store_commute concurrent_append_store_independent store_id_valid)
      using assms prefix_contains_msg apply (metis 
          concurrent_expunge_delete_independent expunge_id_valid delete_expunge_commute)
      using assms prefix_contains_msg apply (metis 
          append_expunge_commute append_id_valid concurrent_append_expunge_independent 
          expunge_id_valid)
      using assms prefix_contains_msg apply (metis 
          expunge_id_valid expunge_store_commute imap.concurrent_store_expunge_independent 
          imap_axioms store_id_valid)
      using assms prefix_contains_msg apply (metis 
          concurrent_store_delete_independent delete_store_commute store_id_valid)
      using assms prefix_contains_msg apply (metis 
          append_id_valid append_store_commute imap.concurrent_append_store_independent imap_axioms 
          store_id_valid)
      using assms prefix_contains_msg apply (metis 
          expunge_id_valid expunge_store_commute imap.concurrent_store_expunge_independent 
          imap_axioms store_id_valid)
      using assms prefix_contains_msg by (metis concurrent_store_store_independent store_id_valid 
          store_store_commute)   
  } thus ?thesis
    by(fastforce simp: hb.concurrent_ops_commute_def)
qed

theorem (in imap) convergence:
  assumes "set (node_deliver_messages xs) = set (node_deliver_messages ys)"
    and "xs prefix of i" 
    and "ys prefix of j"
  shows "apply_operations xs = apply_operations ys"
  using assms by(auto simp add: apply_operations_def intro: hb.convergence_ext 
      concurrent_operations_commute node_deliver_messages_distinct hb_consistent_prefix)

context imap begin

sublocale sec: strong_eventual_consistency weak_hb hb interp_msg
  "\<lambda>ops.\<exists>xs i. xs prefix of i \<and> node_deliver_messages xs = ops" "\<lambda>x.({},{})"
  apply(standard; clarsimp simp add: hb_consistent_prefix node_deliver_messages_distinct
      concurrent_operations_commute)
  apply(metis (no_types, lifting) apply_operations_def bind.bind_lunit not_None_eq
      hb.apply_operations_Snoc kleisli_def apply_operations_never_fails interp_msg_def)
  using drop_last_message apply blast
  done

end
end

