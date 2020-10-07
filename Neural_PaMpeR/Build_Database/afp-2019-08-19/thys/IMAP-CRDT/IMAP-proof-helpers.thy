section \<open>Proof Helpers\<close>

text\<open>In this section we define and prove lemmas that help to show that all identified critical 
conditions hold for concurrent operations. Many of the following parts are derivations from the 
definitions and lemmas of Gomes et al.\<close>

theory
  "IMAP-proof-helpers"
  imports
    "IMAP-def"  

begin

lemma (in imap) apply_operations_never_fails:
  assumes "xs prefix of i"
  shows "apply_operations xs \<noteq> None"
  using assms proof(induction xs rule: rev_induct, clarsimp)
  case (snoc x xs) thus ?case
  proof (cases x)
    case (Broadcast e) thus ?thesis
      using snoc by force
  next
    case (Deliver e) thus ?thesis
      using snoc apply clarsimp unfolding interp_msg_def apply_operations_def
      by (metis (no_types, lifting) bind.bind_lunit interpret_op_def prefix_of_appendD)
  qed
qed

lemma (in imap) create_id_valid:
  assumes "xs prefix of j"
    and "Deliver (i1, Create i2 e) \<in> set xs"
  shows "i1 = i2"
proof -
  have "\<exists>s. valid_behaviours s (i1, Create i2 e)"
    using assms deliver_in_prefix_is_valid by blast
  thus ?thesis
    by(simp add: valid_behaviours_def)
qed

lemma (in imap) append_id_valid:
  assumes "xs prefix of j"
    and "Deliver (i1, Append i2 e) \<in> set xs"
  shows "i1 = i2"
proof -
  have "\<exists>s. valid_behaviours s (i1, Append i2 e)"
    using assms deliver_in_prefix_is_valid by blast
  thus ?thesis
    by(simp add: valid_behaviours_def)
qed

lemma (in imap) expunge_id_valid:
  assumes "xs prefix of j"
    and "Deliver (i1, Expunge e mo i2) \<in> set xs"
  shows "i1 = i2"
proof -
  have "\<exists>s. valid_behaviours s (i1, Expunge e mo i2)"
    using assms deliver_in_prefix_is_valid by blast
  thus ?thesis
    by(simp add: valid_behaviours_def)
qed

lemma (in imap) store_id_valid:
  assumes "xs prefix of j"
    and "Deliver (i1, Store e mo i2) \<in> set xs"
  shows "i1 = i2"
proof -
  have "\<exists>s. valid_behaviours s (i1, Store e mo i2)"
    using assms deliver_in_prefix_is_valid by blast
  thus ?thesis
    by(simp add: valid_behaviours_def)
qed

definition (in imap) added_ids :: "('id \<times> ('id, 'b) operation) event list \<Rightarrow> 'b \<Rightarrow> 'id list" where
  "added_ids es p \<equiv> List.map_filter (\<lambda>x. case x of 
    Deliver (i, Create j e) \<Rightarrow> if e = p then Some j else None | 
    Deliver (i, Expunge e mo j) \<Rightarrow> if e = p then Some j else None |
    _ \<Rightarrow> None) es"

definition (in imap) added_files :: "('id \<times> ('id, 'b) operation) event list \<Rightarrow> 'b \<Rightarrow> 'id list" where
  "added_files es p \<equiv> List.map_filter (\<lambda>x. case x of 
    Deliver (i, Append j e) \<Rightarrow> if e = p then Some j else None |
    Deliver (i, Store e mo j) \<Rightarrow> if e = p then Some j else None |
    _ \<Rightarrow> None) es"

\<comment> \<open>added files simplifier\<close>

lemma (in imap) [simp]:
  shows "added_files [] e = []"
  by (auto simp: added_files_def map_filter_def)

lemma (in imap) [simp]:
  shows "added_files (xs @ ys) e = added_files xs e @ added_files ys e"
  by (auto simp: added_files_def map_filter_append)

lemma (in imap) added_files_Broadcast_collapse [simp]:
  shows "added_files ([Broadcast e]) e' = []"
  by (auto simp: added_files_def map_filter_append map_filter_def)

lemma (in imap) added_files_Deliver_Delete_collapse [simp]:
  shows "added_files ([Deliver (i, Delete is e)]) e' = []"
  by (auto simp: added_files_def map_filter_append map_filter_def)

lemma (in imap) added_files_Deliver_Create_collapse [simp]:
  shows "added_files ([Deliver (i, Create j e)]) e' = []"
  by (auto simp: added_files_def map_filter_append map_filter_def)

lemma (in imap) added_files_Deliver_Expunge_collapse [simp]:
  shows "added_files ([Deliver (i, Expunge e mo j)]) e' = []"
  by (auto simp: added_files_def map_filter_append map_filter_def)

lemma (in imap) added_files_Deliver_Append_diff_collapse [simp]:
  shows "e \<noteq> e' \<Longrightarrow> added_files ([Deliver (i, Append j e)]) e' = []"
  by (auto simp: added_files_def map_filter_append map_filter_def)

lemma (in imap) added_files_Deliver_Append_same_collapse [simp]:
  shows "added_files ([Deliver (i, Append j e)]) e = [j]"
  by (auto simp: added_files_def map_filter_append map_filter_def)

lemma (in imap) added_files_Deliver_Store_diff_collapse [simp]:
  shows "e \<noteq> e' \<Longrightarrow> added_files ([Deliver (i, Store e mo j)]) e' = []"
  by (auto simp: added_files_def map_filter_append map_filter_def)

lemma (in imap) added_files_Deliver_Store_same_collapse [simp]:
  shows "added_files ([Deliver (i, Store e mo j)]) e = [j]"
  by (auto simp: added_files_def map_filter_append map_filter_def)


\<comment> \<open>added ids simplifier\<close>

lemma (in imap) [simp]:
  shows "added_ids [] e = []"
  by (auto simp: added_ids_def map_filter_def)

lemma (in imap) split_ids [simp]:
  shows "added_ids (xs @ ys) e = added_ids xs e @ added_ids ys e"
  by (auto simp: added_ids_def map_filter_append)

lemma (in imap) added_ids_Broadcast_collapse [simp]:
  shows "added_ids ([Broadcast e]) e' = []"
  by (auto simp: added_ids_def map_filter_append map_filter_def)

lemma (in imap) added_ids_Deliver_Delete_collapse [simp]:
  shows "added_ids ([Deliver (i, Delete is e)]) e' = []"
  by (auto simp: added_ids_def map_filter_append map_filter_def)

lemma (in imap) added_ids_Deliver_Append_collapse [simp]:
  shows "added_ids ([Deliver (i, Append j e)]) e' = []"
  by (auto simp: added_ids_def map_filter_append map_filter_def)

lemma (in imap) added_ids_Deliver_Store_collapse [simp]:
  shows "added_ids ([Deliver (i, Store e mo j)]) e' = []"
  by (auto simp: added_ids_def map_filter_append map_filter_def)

lemma (in imap) added_ids_Deliver_Create_diff_collapse [simp]:
  shows "e \<noteq> e' \<Longrightarrow> added_ids ([Deliver (i, Create j e)]) e' = []"
  by (auto simp: added_ids_def map_filter_append map_filter_def)

lemma (in imap) added_ids_Deliver_Expunge_diff_collapse [simp]:
  shows "e \<noteq> e' \<Longrightarrow> added_ids ([Deliver (i, Expunge e mo j)]) e' = []"
  by (auto simp: added_ids_def map_filter_append map_filter_def)

lemma (in imap) added_ids_Deliver_Create_same_collapse [simp]:
  shows "added_ids ([Deliver (i, Create j e)]) e = [j]"
  by (auto simp: added_ids_def map_filter_append map_filter_def)

lemma (in imap) added_ids_Deliver_Expunge_same_collapse [simp]:
  shows "added_ids ([Deliver (i, Expunge e mo j)]) e = [j]"
  by (auto simp: added_ids_def map_filter_append map_filter_def)

lemma (in imap) expunge_id_not_in_set:
  assumes "i1 \<notin> set (added_ids [Deliver (i, Expunge e mo i2)] e)"
  shows "i1 \<noteq> i2"
  using assms by simp

lemma (in imap) apply_operations_added_ids:
  assumes "es prefix of j"
    and "apply_operations es = Some f"
  shows "fst (f x) \<subseteq> set (added_ids es x)"
  using assms proof (induct es arbitrary: f rule: rev_induct, force)
  case (snoc x xs) thus ?case
  proof (cases x, force)
    case (Deliver e)
    moreover obtain a b where "e = (a, b)" by force
    ultimately show ?thesis
      using snoc by(case_tac b; clarsimp simp: interp_msg_def split: bind_splits,
          force split: if_split_asm simp add: op_elem_def interpret_op_def)
  qed
qed

lemma (in imap) apply_operations_added_files:
  assumes "es prefix of j"
    and "apply_operations es = Some f"
  shows "snd (f x) \<subseteq> set (added_files es x)"
  using assms proof (induct es arbitrary: f rule: rev_induct, force)
  case (snoc x xs) thus ?case
  proof (cases x, force)
    case (Deliver e)
    moreover obtain a b where "e = (a, b)" by force
    ultimately show ?thesis
      using snoc by(case_tac b; clarsimp simp: interp_msg_def split: bind_splits,
          force split: if_split_asm simp add: op_elem_def interpret_op_def)
  qed
qed

lemma (in imap) Deliver_added_files:
  assumes "xs prefix of j"
    and "i \<in> set (added_files xs e)"
  shows "Deliver (i, Append i e) \<in> set xs \<or> (\<exists> mo . Deliver (i, Store e mo i) \<in> set xs)"
  using assms proof (induct xs rule: rev_induct, clarsimp)
  case (snoc x xs) thus ?case
  proof (cases x, force)
    case X: (Deliver e')
    moreover obtain a b where E: "e' = (a, b)" by force
    ultimately show ?thesis using snoc 
      apply (case_tac b; clarify) apply (simp,metis prefix_of_appendD,force)
      using append_id_valid apply simp 
      using E apply (metis 
          added_files_Deliver_Append_diff_collapse added_files_Deliver_Append_same_collapse 
          empty_iff in_set_conv_decomp list.set(1) prefix_of_appendD set_ConsD, simp)
      using E apply_operations_added_files apply (blast,simp) 
      using E apply_operations_added_files 
      by (metis Un_iff 
          added_files_Deliver_Store_diff_collapse added_files_Deliver_Store_same_collapse empty_iff 
          empty_set list.set_intros(1) prefix_of_appendD set_ConsD set_append store_id_valid)
  qed
qed

end
