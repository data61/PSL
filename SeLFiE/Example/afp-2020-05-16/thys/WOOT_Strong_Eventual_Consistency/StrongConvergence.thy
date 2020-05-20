subsection \<open>Strong Convergence\<close>

theory StrongConvergence
  imports IntegrateInsertCommute CreateConsistent HOL.Finite_Set DistributedExecution
begin

lemma  (in dist_execution) happened_before_same:
  assumes "i < j"
  assumes "j < length (events k)"
  shows "(happened_immediately_before)\<^sup>+\<^sup>+ (k,i) (k,j)" 
proof -
  obtain v where v_def: "j = Suc i + v" using assms(1) less_iff_Suc_add by auto
  have "is_valid_event_id (k, Suc i + v) \<longrightarrow> (happened_immediately_before)\<^sup>+\<^sup>+ (k,i) (k, Suc i + v)"
    apply (induction v, simp add: tranclp.r_into_trancl)
    by (metis Suc_lessD add_Suc_right fst_conv happened_immediately_before.elims(3) 
        is_valid_event_id.simps snd_conv tranclp.simps)
  then show ?thesis
    using is_valid_event_id.simps v_def assms by blast
qed

definition make_set where "make_set (k :: nat) p = {x. \<exists>j. p j x \<and> j < k}"

lemma make_set_nil [simp]: "make_set 0 p = {}" by (simp add:make_set_def)

lemma make_set_suc [simp]: "make_set (Suc k) p = make_set k p \<union> {x. p k x}"
  using less_Suc_eq by (simp add:make_set_def, blast)

lemma (in dist_execution) received_messages_eff:
  assumes "is_valid_state_id (i,j)"
  shows "set (received_messages (i,j)) = make_set j (\<lambda>k x. (\<exists>s. event_at (i, k) (Receive s x)))" 
  using assms by (induction j, simp add:make_set_def, simp add: take_Suc_conv_app_nth)

lemma (in dist_execution) finite_valid_event_ids:
  "finite {i. is_valid_event_id i}"
proof -
  define X where "X = {p. events p = events p}"
  have "finite X \<Longrightarrow> \<exists>m. (\<forall>p \<in> X. (length (events p)) < m)" 
    apply (induction rule:finite_induct, simp)
    by (metis gt_ex insert_iff le_less_trans less_imp_not_less not_le_imp_less)
  then obtain m where m_def: "\<And>p. length (events p) < m" using X_def fin_peers by auto
  have "{(i,j). is_valid_event_id (i,j)} \<subseteq> {(i,j). j < m}" 
    using m_def by (simp add: Collect_mono_iff less_trans)
  also have "... \<subseteq> X \<times> {j. j < m}" using X_def by blast
  finally have "{i. is_valid_event_id i} \<subseteq> X \<times> {j. j < m}" 
    by (simp add: subset_iff)
  thus ?thesis
    using fin_peers finite_Collect_less_nat finite_cartesian_product
        infinite_super subset_eq
    by (metis UNIV_I)
qed

lemma (in dist_execution) send_insert_id_1:
  "state i \<bind> (\<lambda>s. create_insert s n \<sigma> i) = Inr (Insert m) \<Longrightarrow> I m = i"
  by fastforce

lemma (in dist_execution) send_insert_id_2:
  "state i \<bind> (\<lambda>s. create_delete s n) = Inr (Insert m) \<Longrightarrow> False"
  by fastforce

lemma (in dist_execution) send_insert_id:
  "event_at i (Send (Insert m)) \<Longrightarrow> I m = i" 
  using send_correct send_insert_id_1 send_insert_id_2 by metis

lemma (in dist_execution) recv_insert_once:
  "event_at (i,j) (Receive s (Insert m)) \<Longrightarrow> event_at (i,k) (Receive t (Insert m)) \<Longrightarrow> j = k"
  using no_data_corruption send_insert_id at_most_once
  by (simp, metis (mono_tags) Pair_inject event_pred.simps fst_conv is_valid_event_id.simps)

proposition integrate_insert_commute':
  fixes M m s
  assumes "consistent M"
  assumes "is_delete m \<or> m \<notin> T"
  assumes "m \<in> M"
  assumes "T \<subseteq> M"
  assumes "deps m \<subseteq> I ` insert_messages T" 
  assumes "is_certified_associated_string T s"
  shows "is_certified_associated_string (T \<union> {m}) (s \<bind> (\<lambda>t. integrate t m))" 
proof (cases s)
  case (Inl a)
  then show ?thesis using assms by simp
next
  case (Inr b)
  have "T \<union> {m} \<subseteq> M" using assms(3) assms(4) by simp 
  moreover have "\<Union> (deps ` (T \<union> {m})) \<subseteq> I ` insert_messages (T \<union> {m})" 
    using assms(5) assms(6) Inr apply (simp add:is_associated_string_def consistent_def)
    by (meson dual_order.trans subset_insertI subset_mono)
  ultimately have "consistent (T \<union> {m})"
    using assms consistent_subset by force 
  then show ?thesis using integrate_insert_commute assms(2) assms(6) Inr by auto
qed

lemma foldM_rev: "foldM f s (li@[ll]) = foldM f s li \<bind> (\<lambda>t. f t ll)"
  by (induction li arbitrary:s, simp+)

lemma  (in dist_execution) state_is_associated_string':
  fixes i M
  assumes "j \<le> length (events i)"
  assumes "consistent M"
  assumes "make_set j (\<lambda>k m. \<exists>s. event_at (i,k) (Receive s m)) \<subseteq> M"
  shows "is_certified_associated_string (make_set j (\<lambda>k m. \<exists>s. event_at (i,k) (Receive s m))) (state (i,j))"
  using assms
proof (induction j)
  case 0
  then show ?case by (simp add: empty_associated)
next
  case (Suc j)
  have b:"j < length (events i)" using Suc by auto
  show ?case
  proof (cases "events i ! j")
    case (Send m)
    then show ?thesis using Suc by (simp add: take_Suc_conv_app_nth) 
  next
    case (Receive s m)
    moreover have "is_delete m \<or> m \<notin> (make_set j (\<lambda>k m. \<exists>s. event_at (i,k) (Receive s m)))"
      apply (cases m) using recv_insert_once Receive b apply (simp add: make_set_def) 
      apply (metis nat_neq_iff)
      by (simp)
    moreover have "deps m \<subseteq> I ` insert_messages (make_set j (\<lambda>k m. \<exists>s. event_at (i,k) (Receive s m)))"
      apply (rule subsetI)
      using semantic_causal_delivery Receive b apply (simp add:insert_messages_def image_iff make_set_def) by metis
    ultimately show ?thesis 
      using Suc apply (cases s, simp add:take_Suc_conv_app_nth foldM_rev)
      using integrate_insert_commute' by fastforce
  qed  
qed

lemma  (in dist_execution) sent_before_recv:
  assumes "event_at (i,k) (Receive s m)"
  assumes "j < length (events i)"
  assumes "k < j" 
  shows "event_at s (Send m) \<and> happened_immediately_before\<^sup>+\<^sup>+ s (i,j)"
proof -
  have a:"event_at s (Send m)"
    using assms no_data_corruption by blast
  hence "happened_immediately_before s (i,k)" 
    using assms by (cases s, simp, metis (mono_tags, lifting) event.simps(6))
  hence "(happened_immediately_before)\<^sup>+\<^sup>+ s (i,j)" using happened_before_same 
    by (meson assms(2) assms(3) tranclp_into_tranclp2)
  thus ?thesis using a by blast
qed

lemma (in dist_execution) irrefl_p: "irreflp (happened_immediately_before\<^sup>+\<^sup>+)" 
  by (meson acyclic_def dist_execution.acyclic_happened_before
      dist_execution_axioms irreflpI tranclp_unfold)

lemma (in dist_execution) new_messages_keep_consistency:
  assumes "consistent M"
  assumes "event_at i (Send m)"
  assumes "set (received_messages i) \<subseteq> M"
  assumes "i \<notin> I ` insert_messages M"
  shows "consistent (insert m M)"
proof -
  have a:"is_valid_state_id i" using assms(2) by (cases i, simp)
  consider 
    (1) "(\<exists>n \<sigma>. Inr m = (state i) \<bind> (\<lambda>s. create_insert s n \<sigma> i))" |
    (2) "(\<exists>n.   Inr m = (state i) \<bind> (\<lambda>s. create_delete s n))" 
    by (metis (full_types) send_correct assms(2))
  then show ?thesis 
    proof (cases)
    case 1
    then obtain s n' \<sigma> where s_def:
      "Inr s = state i" "Inr m = create_insert s n' \<sigma> i" 
      by (cases "state i", simp, simp add:bind_def, blast)
    moreover have "is_associated_string (set (received_messages i)) s"
      using a assms(1) assms(3) apply (cases i, simp only:received_messages_eff)
      using s_def(1) state_is_associated_string'
      by (simp, metis (mono_tags, lifting) is_certified_associated_string.simps(1))
    ultimately show ?thesis using create_insert_consistent s_def assms 
      by (metis Un_insert_right sup_bot.right_neutral)
  next
    case 2
    then obtain s n' where s_def:
      "Inr s = state i" "Inr m = create_delete s n'" 
      by (cases "state i", simp, simp add:bind_def, blast)
    moreover have "is_associated_string (set (received_messages i)) s"
      using a assms(1) assms(3) apply (cases i, simp only:received_messages_eff)
      using s_def(1) state_is_associated_string'
      by (simp, metis (mono_tags, lifting) is_certified_associated_string.simps(1))
    ultimately show ?thesis using create_delete_consistent s_def assms 
      by (metis Un_insert_right sup_bot.right_neutral)
  qed
qed

lemma (in dist_execution) sent_messages_consistent:
  "consistent {m. (\<exists>i. event_at i (Send m))}"
proof -
  obtain ids where ids_def: "set ids = {i. is_valid_event_id i} \<and> 
    sorted_wrt (to_ord (happened_immediately_before)) ids \<and> distinct ids"
    using top_sort finite_valid_event_ids  by (metis acyclic_happened_before)
  have "\<And>x y. happened_immediately_before\<^sup>+\<^sup>+ x y \<Longrightarrow> x \<in> set ids \<and> y \<in> set ids"
    using converse_tranclpE ids_def tranclp.cases by fastforce
  hence a:"\<And>x y. happened_immediately_before\<^sup>+\<^sup>+ x y \<Longrightarrow>
    (\<exists>i j. i < j \<and> j < length ids \<and> ids ! i = x \<and> ids ! j = y)"
    by (metis top_sort_eff ids_def  distinct_Ex1 irrefl_p)
  define n where "n = length ids"
  have "n \<le> length ids \<Longrightarrow> consistent (make_set n (\<lambda>k x. event_at (ids ! k) (Send x)))"
  proof (induction n)
    case 0
    then show ?case using empty_consistent by simp
  next
    case (Suc n)
    moreover obtain i j where ij_def: 
      "ids ! n = (i,j)" "n < length ids"
      "is_valid_event_id (i,j)" "is_valid_state_id (i,j)"
      by (metis Suc.prems Suc_le_lessD ids_def is_valid_event_id.elims(2) is_valid_state_id.simps
          le_eq_less_or_eq mem_Collect_eq nth_mem)
    moreover have "set (received_messages (i,j)) \<subseteq> make_set n (\<lambda>k x. event_at (ids ! k) (Send x))"
      using ij_def apply (simp add:received_messages_eff del:received_messages.simps, rule_tac subsetI)
      using sent_before_recv a apply (simp add:make_set_def) 
      by (metis (no_types, hide_lams) distinct_Ex1 ids_def in_set_conv_nth)
    moreover have "(i,j) \<notin> I ` insert_messages (make_set n (\<lambda>k x. event_at (ids ! k) (Send x)))"
        apply (simp add:insert_messages_def image_iff make_set_def del:event_at.simps)  
        using ids_def le_eq_less_or_eq nth_eq_iff_index_eq send_insert_id  
        by (metis dual_order.strict_trans1 ij_def(1) ij_def(2) less_not_refl)
    ultimately show ?case using Suc
      apply (cases "events i ! j")
      using new_messages_keep_consistency [where i = "(i,j)"] by simp+
  qed
  moreover have "make_set n (\<lambda>k x. event_at (ids ! k) (Send x)) = {x. (\<exists>i. event_at i (Send x))}" 
    apply (simp add:make_set_def n_def, rule set_eqI, subst surjective_pairing, simp only:event_pred.simps)
    using ids_def apply simp 
    by (metis fst_conv in_set_conv_nth is_valid_event_id.simps mem_Collect_eq prod.exhaust_sel snd_conv) 
  ultimately show ?thesis using ids_def n_def by simp
qed

lemma (in dist_execution) received_messages_were_sent:
  assumes "is_valid_state_id (i,j)"
  shows "make_set j (\<lambda>k m. (\<exists>s. event_at (i, k) (Receive s m))) \<subseteq> {m. \<exists>i. event_at i (Send m)}"
  using no_data_corruption by (simp add:make_set_def, rule_tac subsetI, fastforce)

lemma (in dist_execution) state_is_associated_string:
  assumes "is_valid_state_id i"
  shows "is_certified_associated_string (set (received_messages i)) (state i)"
  using state_is_associated_string' received_messages_eff
    sent_messages_consistent received_messages_were_sent assms by (cases i, simp)

end
