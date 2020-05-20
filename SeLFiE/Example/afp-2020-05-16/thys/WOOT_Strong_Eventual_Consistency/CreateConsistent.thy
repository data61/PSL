subsection \<open>Create Consistent\label{sec:create_consistent}\<close>

theory CreateConsistent
  imports CreateAlgorithms Consistency
begin

lemma nth_visible_inc':
  assumes "sorted_wrt (<) (map a (ext_ids s))"
  assumes "nth_visible s n = Inr i"
  assumes "nth_visible s (Suc n) = Inr j"
  shows "a i < a j" 
proof -
  have "subseq (ext_ids (filter is_visible s)) (ext_ids s)" 
    by (simp add: ext_ids_def subseq_map)
  hence "sorted_wrt (<) (map a (ext_ids (filter is_visible s)))"
    using assms(1) subseq_imp_sorted sorted_wrt_map by blast
  moreover have a:"Suc n < length (ext_ids (filter is_visible s))" 
    apply (rule classical) using assms(3) by simp
  ultimately show ?thesis using assms(2) assms(3) apply (simp) 
    using sorted_wrt_nth_less by fastforce
qed

lemma nth_visible_eff:
  assumes "nth_visible s n = Inr i"
  shows "extended_to_set i \<subseteq> I ` set s"
proof -
  have "i \<in> set (ext_ids (filter is_visible s))"
    apply (cases "n < length (ext_ids (filter is_visible s))")
    using assms by auto
  thus ?thesis  
    apply (simp add: ext_ids_def) 
    using extended.inject by auto
qed

lemma subset_mono:
  assumes "N \<subseteq> M"
  shows "I ` insert_messages N \<subseteq> I ` insert_messages M"
proof -
  have "insert_messages N \<subseteq> insert_messages M" using assms
    by (metis (no_types, lifting) Collect_mono_iff insert_messages_def subsetCE)
  thus ?thesis by (simp add: image_mono)
qed

lemma deps_insert:
  assumes "\<Union> (deps ` M) \<subseteq> (I ` insert_messages M)"
  assumes "deps m \<subseteq> I ` insert_messages M"
  shows "\<Union> (deps ` (M \<union> {m})) \<subseteq> (I ` insert_messages (M \<union> {m}))"
proof -
  have "deps m \<subseteq> I ` insert_messages (M \<union> {m})" using assms(2) subset_mono
    by (metis Un_upper1 order_trans)
  thus ?thesis using assms(1) apply (simp) 
    by (meson rev_subsetD subsetI subset_insertI subset_mono)
qed

lemma wf_add:
  fixes m :: "('a,'b) insert_message"
  assumes "wfP (depends_on M)"
  assumes "\<And>n. n \<in> (M \<union> {m}) \<Longrightarrow> I m \<notin> deps (Insert n)"
  assumes "m \<notin> M"
  shows "wfP (depends_on (M \<union> {m}))" 
proof -
  have "\<And>Q. Q \<noteq> {} \<Longrightarrow> (\<exists>z\<in>Q. \<forall>y. (y \<in> M \<union> {m}) \<and> (z \<in> M \<union> {m}) \<and>
           I y \<in> deps (Insert z) \<longrightarrow> y \<notin> Q)"
  proof -
    fix Q :: "('a, 'b) insert_message set"
    assume b:"Q \<noteq> {}"
    show "\<exists>z\<in>Q. \<forall>y. (y \<in> M \<union> {m}) \<and> (z \<in> M \<union> {m}) \<and> I y \<in> deps (Insert z)
           \<longrightarrow> y \<notin> Q"
    proof (cases "\<exists>x. x \<in> Q - {m}")
      case True
      hence "\<exists>z\<in> Q - {m}. \<forall>y. (y \<in> M) \<and> (z \<in> M) \<and> I y \<in> deps (Insert z)
             \<longrightarrow> y \<notin> Q - {m}"
        by (metis depends_on.simps assms(1) wfP_eq_minimal)
      then show ?thesis using assms(2) DiffD2 by auto
    next
      case False
      hence "Q = {m}" using b by blast
      thus ?thesis using assms(2) by blast
    qed
  qed
  thus ?thesis by (simp add:wfP_eq_minimal, blast)
qed

lemma create_insert_p_s_ordered:
  assumes "is_associated_string N s"
  assumes "a_conditions (insert_messages N) a"
  assumes "Inr (Insert m) = create_insert s n \<sigma> new_id"
  shows "a (P m) < a (S m)"
proof -
  obtain p q where pq_def: 
    "create_insert s n \<sigma> new_id = Inr (Insert (InsertMessage p new_id q \<sigma>))" 
    by (metis (no_types, lifting) One_nat_def add.right_neutral add_Suc_right 
        create_insert.elims sum.case_eq_if sum.simps(4) assms(3) bind_def)
  have "Inr p = nth_visible s n" using pq_def Error_Monad.bindE by fastforce
  moreover have "Inr q = nth_visible s (Suc n)" 
    using pq_def Error_Monad.bindE by fastforce  
  ultimately have "a p < a q"
    using assms by (metis is_associated_string_def nth_visible_inc')
  moreover have "m = InsertMessage p new_id q \<sigma>"
    using assms(3) pq_def by auto
  ultimately show ?thesis by (simp add: pq_def)
qed

lemma create_insert_consistent:
  assumes "consistent M"
  assumes "is_associated_string N s"
  assumes "N \<subseteq> M"
  assumes "Inr m = create_insert s n \<sigma> new_id"
  assumes "new_id \<notin> I ` insert_messages M"
  shows "consistent (M \<union> {m})"
proof -
  obtain p q where pq_def:
    "create_insert s n \<sigma> new_id = Inr (Insert (InsertMessage p new_id q \<sigma>))"
    by (metis (no_types, lifting) One_nat_def add.right_neutral add_Suc_right 
        create_insert.elims assms(4) sum.case_eq_if sum.simps(4) bind_def)
  define m' where "m' = InsertMessage p new_id q \<sigma>" 
  hence a:"m = Insert m'" using pq_def assms(4) by auto
  hence d: "create_insert s n \<sigma> new_id = Inr (Insert m')"
    using pq_def assms by simp
  have b:"I m' = new_id" using m'_def by (simp add:I_def)
  hence "inj_on I (insert_messages M \<union> {m'})" using assms(5) assms(1)
    using consistent_def by fastforce
  hence "inj_on I (insert_messages (M \<union> {m}))" using assms(4) pq_def m'_def
    by (metis Inr_inject insert_insert_message)
  moreover 
  have p:"extended_to_set p \<subseteq> I ` set s" using pq_def nth_visible_eff by fastforce 
  have q: "extended_to_set q \<subseteq> I ` set s"
    using pq_def apply (simp add:bind_def del:nth_visible.simps)
    apply (cases "nth_visible s n", simp)
    by (cases "nth_visible s (Suc n)", simp, simp add: nth_visible_eff)  
  have "extended_to_set p \<union> extended_to_set q \<subseteq> I ` set s" using p q by simp
  hence "extended_to_set p \<union> extended_to_set q \<subseteq> I ` insert_messages N"
    by (metis assms(2) is_associated_string_def to_woot_character_keeps_i_lifted)
  hence "extended_to_set p \<union> extended_to_set q \<subseteq> I ` insert_messages M" 
    using assms(3) subset_mono by blast
  hence c:"deps m \<subseteq> I ` insert_messages M" using pq_def assms(4) by auto
  hence "\<Union> (deps ` (M \<union> {m})) \<subseteq> (I ` insert_messages (M \<union> {m}))"
    by (metis consistent_def assms(1) deps_insert)
  moreover have w: 
    "\<forall>n \<in> insert_messages M \<union> {m'}. deps (Insert n) \<subseteq> I ` insert_messages M" 
    by (metis a c consistent_def assms(1) Sup_le_iff imageI insert_iff 
        insert_is_Un insert_messages_def mem_Collect_eq sup.commute)
  hence "\<forall>n \<in> insert_messages M \<union> {m'}. I m' \<notin> deps (Insert n)"
    using b assms(5) by blast 
  hence "wfP (depends_on (insert_messages M \<union> {m'}))" 
    by (metis Un_insert_right insert_absorb wf_add assms(1)
        consistent_def sup_bot.right_neutral)
  moreover obtain a where a_def: "a_conditions (insert_messages M) a"
    using consistent_def  assms(1) by blast
  define a' where 
    "a' = (\<lambda>i. if i = \<lbrakk> new_id \<rbrakk> then \<lbrakk>\<Psi> (a (P m'), a(S m')) new_id\<rbrakk> else a i)"   
  hence "a_conditions (insert_messages (M \<union> {m})) a'"
  proof -
    have "a' \<turnstile> < a' \<stileturn>" using a'_def a_conditions_def a_def by auto
    moreover have 
      "\<And>m''. m'' \<in> (insert_messages M \<union> {m'}) \<longrightarrow> 
          a'(P m'') < a'(S m'')  \<and>
          a' \<lbrakk>I m''\<rbrakk> = \<lbrakk>\<Psi> (a'(P m''), a'(S m'')) (I m'')\<rbrakk>" 
    proof 
      fix m''
      assume e:" m'' \<in> (insert_messages M \<union> {m'})"
      show "a'(P m'') < a'(S m'') \<and> a' \<lbrakk> I m''\<rbrakk> = 
            \<lbrakk>\<Psi> (a'(P m''), a'(S m'')) (I m'')\<rbrakk>" 
      proof (cases "m'' \<in> insert_messages M")
        case True
        moreover have "deps (Insert m'') \<subseteq> I ` insert_messages M" 
          using e w by blast
        hence "P m'' \<noteq> \<lbrakk> new_id \<rbrakk> \<and> S m'' \<noteq> \<lbrakk> new_id \<rbrakk>"
          by (meson assms(5) contra_subsetD pred_is_dep succ_is_dep)
        moreover have "I m'' \<noteq> new_id" 
          using assms(5) True by blast
        ultimately show ?thesis using a_def True 
          by (simp add: a_conditions_def a'_def)
      next
        case False
        moreover have "I m'' = new_id" using False b e by blast
        moreover have "deps (Insert m'') \<subseteq> I ` insert_messages M"
          using False a c e by blast
        hence "P m'' \<noteq> \<lbrakk> new_id \<rbrakk> \<and> S m'' \<noteq> \<lbrakk> new_id \<rbrakk>" 
          by (meson assms(5) contra_subsetD pred_is_dep succ_is_dep)
        moreover have "a_conditions (insert_messages N) a" 
          using a_def a_subset assms is_associated_string_def by blast
        hence "a (P m') < a (S m')"
          by (metis assms(2) d create_insert_p_s_ordered)
        hence "a' (P m'') < a' (S m'')" using calculation a'_def False e by auto
        ultimately show ?thesis using e a'_def by auto
      qed
    qed
    ultimately show "?thesis" using a_conditions_def 
      by (metis a insert_insert_message)
  qed
  ultimately show "?thesis" using consistent_def a by (metis insert_insert_message)
qed

lemma bind_simp: "(x \<bind> (\<lambda>l. y l) = Inr r) \<Longrightarrow> (y (projr x) = Inr r)"
  using isOK_I by force

lemma create_delete_consistent:
  assumes "consistent M"
  assumes "is_associated_string N s"
  assumes "N \<subseteq> M"
  assumes "Inr m = create_delete s n"
  shows "consistent (M \<union> {m})"
proof -
  obtain i where pq_def: "create_delete s n = Inr (Delete (DeleteMessage i))"
    by (metis (no_types, lifting) Error_Monad.bindE create_delete.simps assms(4)) 
  hence a: "m = Delete (DeleteMessage i)" using assms(4) by auto
  hence b: "insert_messages (M \<union> {m}) = insert_messages M" 
    by (simp add:insert_messages_def)
  have "n \<noteq> 0" apply (rule classical) using pq_def by (simp add:bind_def ext_ids_def) 
  then obtain u where "n = Suc u" using not0_implies_Suc by blast
  then have "i \<in> I ` set s" using pq_def 
    apply (cases "u < length (filter is_visible s)")
    apply (simp add:bind_simp ext_ids_def nth_append) 
    apply (meson filter_is_subset imageI in_set_conv_nth subset_code(1))
    apply (cases "u = length (filter is_visible s)")
    by (simp add:bind_def ext_ids_def nth_append)+
  hence "i \<in> I ` insert_messages N" using assms
    by (metis is_associated_string_def to_woot_character_keeps_i_lifted)
  hence c:"deps m \<subseteq> I ` insert_messages M" using a 
    by (metis assms(3) deps.simps(2) singletonD subsetCE subsetI subset_mono)
  then show "?thesis" using assms(1) b by (simp add:consistent_def)
qed

end