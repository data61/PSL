subsection \<open>Consistency of sets of WOOT Messages \label{sec:consistency}\<close>

theory Consistency
  imports SortKeys Psi Sorting DistributedExecution
begin

definition insert_messages :: "('\<I>, '\<Sigma>) message set \<Rightarrow> ('\<I>, '\<Sigma>) insert_message set"
  where "insert_messages M = {x. Insert x \<in> M}"

lemma insert_insert_message: 
  "insert_messages (M \<union> {Insert m}) = insert_messages M \<union> {m}"
  by (simp add:insert_messages_def, simp add:set_eq_iff)

definition delete_messages :: "('a, 's) message set \<Rightarrow> 'a delete_message set"
  where "delete_messages M = {x. Delete x \<in> M}"

fun depends_on where "depends_on M x y = (x \<in> M \<and> y \<in> M \<and> I x \<in> deps (Insert y))"

definition a_conditions ::
  "(('a :: linorder), 's) insert_message set \<Rightarrow> ('a extended \<Rightarrow> 'a position) \<Rightarrow> bool"
  where "a_conditions M a = (
    a \<turnstile> < a \<stileturn> \<and>
    (\<forall>m. m \<in> M \<longrightarrow> a (P m) < a (S m) \<and>
                   a \<lbrakk>I m\<rbrakk> = \<lbrakk>\<Psi> (a (P m), a (S m)) (I m)\<rbrakk>))"

definition consistent :: "('a :: linorder, 's) message set \<Rightarrow> bool"
  where "consistent M \<equiv>
    inj_on I (insert_messages M) \<and>
    (\<Union> (deps ` M) \<subseteq> (I ` insert_messages M)) \<and>
    wfP (depends_on (insert_messages M)) \<and>
    (\<exists>a. a_conditions (insert_messages M) a)"

lemma consistent_subset:
  assumes "consistent N"
  assumes "M \<subseteq> N"
  assumes "\<Union> (deps ` M) \<subseteq> (I ` insert_messages M)"
  shows "consistent M"
proof -
  have a:"insert_messages M \<subseteq> insert_messages N"
    using assms(2) insert_messages_def by blast
  hence b:"inj_on I (insert_messages M)"
    using assms(1) consistent_def inj_on_subset by blast
  have "wfP (depends_on (insert_messages N))"
    using assms(1) consistent_def by blast
  moreover have 
    "depends_on (insert_messages M) \<le> depends_on (insert_messages N)" 
    using a by auto
  ultimately have c:"wfP (depends_on (insert_messages M))"
    using a wf_subset [to_pred] by blast
  obtain a where "a_conditions (insert_messages N) a"
    using assms(1) consistent_def by blast
  hence "a_conditions (insert_messages M) a"
    by (meson a a_conditions_def subset_iff)
  thus ?thesis using b c assms(3) consistent_def by blast
qed

lemma pred_is_dep: "P m = \<lbrakk> i \<rbrakk> \<longrightarrow> i \<in> deps (Insert m)"
  by (metis Un_iff deps.simps(1) extended.set_intros extended.simps(27)
      extended_to_set.simps(1) insert_message.exhaust_sel)

lemma succ_is_dep: "S m = \<lbrakk> i \<rbrakk> \<longrightarrow> i \<in> deps (Insert m)"
  by (metis Un_insert_right deps.simps(1) extended_to_set.simps(1) insertI1
      insert_message.exhaust_sel)

lemma a_subset:
  fixes M N a
  assumes "M \<subseteq> N"
  assumes "a_conditions (insert_messages N) a"
  shows "a_conditions (insert_messages M) a"
  using assms by (simp add:a_conditions_def insert_messages_def, blast)

definition delete_maybe :: "'\<I>  \<Rightarrow> ('\<I>, '\<Sigma>) message set \<Rightarrow> '\<Sigma>  \<Rightarrow> '\<Sigma> option" where 
  "delete_maybe i D s = (if Delete (DeleteMessage i) \<in> D then None else Some s)"

definition to_woot_character ::
  "('\<I>, '\<Sigma>) message set \<Rightarrow> ('\<I>, '\<Sigma>) insert_message \<Rightarrow> ('\<I>, '\<Sigma>) woot_character"
  where
    "to_woot_character D m = (
       case m of
         (InsertMessage l i u s) \<Rightarrow> InsertMessage l i u (delete_maybe i D s))"

lemma to_woot_character_keeps_i [simp]: "I (to_woot_character M m) = I m"
  by (cases m, simp add:to_woot_character_def)

lemma to_woot_character_keeps_i_lifted [simp]: 
  "I ` to_woot_character M ` X = I ` X"
  by (metis (no_types, lifting) image_cong image_image to_woot_character_keeps_i)

lemma to_woot_character_keeps_P [simp]: "P (to_woot_character M m) = P m"
  by (cases m, simp add:to_woot_character_def)

lemma to_woot_character_keeps_S [simp]: "S (to_woot_character M m) = S m"
  by (cases m, simp add:to_woot_character_def)

lemma to_woot_character_insert_no_eff:
  "to_woot_character (insert (Insert m) M) = to_woot_character M"
  by (rule HOL.ext, simp add:delete_maybe_def to_woot_character_def insert_message.case_eq_if)

definition is_associated_string ::
  "('a, 's) message set \<Rightarrow> ('a :: linorder, 's) woot_character list \<Rightarrow> bool"
  where "is_associated_string M s \<equiv> (
    consistent M \<and>
    set s = to_woot_character M ` (insert_messages M) \<and>
    (\<forall>a. a_conditions (insert_messages M) a \<longrightarrow> 
         sorted_wrt (<) (map a (ext_ids s))))"

fun is_certified_associated_string where
  "is_certified_associated_string M (Inr v) = is_associated_string M v" |
  "is_certified_associated_string M (Inl _) = False"

lemma associated_string_unique:
  assumes "is_associated_string M s"
  assumes "is_associated_string M t"
  shows "s = t"
  using assms
  apply (simp add:ext_ids_def is_associated_string_def consistent_def
         sorted_wrt_append)
  by (metis sort_set_unique)

lemma is_certified_associated_string_unique:
  assumes "is_certified_associated_string M s"
  assumes "is_certified_associated_string M t"
  shows "s = t"
  using assms by (case_tac s, case_tac [!] t, (simp add:associated_string_unique)+)

lemma empty_consistent: "consistent {}"
proof -
  have "a_conditions {} (\<lambda>x. (case x of \<turnstile> \<Rightarrow> \<turnstile> | \<stileturn> \<Rightarrow> \<stileturn>))"
    by (simp add: a_conditions_def)
  hence "\<exists>f. a_conditions {} f" by blast
  moreover have "wfP (depends_on {})" by (simp add: wfP_eq_minimal)
  ultimately show ?thesis by (simp add:consistent_def insert_messages_def)
qed

lemma empty_associated: "is_associated_string {} []"
  by (simp add:is_associated_string_def insert_messages_def empty_consistent 
      ext_ids_def a_conditions_def)

text \<open>The empty set of messages is consistent and the associated string is the empty string.\<close>

end
