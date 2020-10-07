theory Indexed_FSet
imports
  "HOL-Library.FSet"
begin

text \<open>It is convenient to address the members of a finite set by a natural number, and
also to convert a finite set to a list.\<close>

context includes fset.lifting
begin
lift_definition fset_from_list :: "'a list => 'a fset" is set by (rule finite_set)
lemma mem_fset_from_list[simp]: "x |\<in>| fset_from_list l  \<longleftrightarrow> x \<in> set l" by transfer rule
lemma fimage_fset_from_list[simp]: "f |`| fset_from_list l = fset_from_list (map f l)"  by transfer auto
lemma fset_fset_from_list[simp]: "fset (fset_from_list l) = set l"  by transfer auto
lemmas fset_simps[simp] = set_simps[Transfer.transferred]
lemma size_fset_from_list[simp]: "distinct l \<Longrightarrow> size (fset_from_list l) = length l"
  by (induction l) auto

definition list_of_fset :: "'a fset \<Rightarrow> 'a list" where
  "list_of_fset s = (SOME l. fset_from_list l = s \<and> distinct l)"

lemma fset_from_list_of_fset[simp]: "fset_from_list (list_of_fset s) = s"
  and distinct_list_of_fset[simp]: "distinct (list_of_fset s)"
  unfolding atomize_conj list_of_fset_def 
  by (transfer, rule someI_ex, rule finite_distinct_list)

lemma length_list_of_fset[simp]: "length (list_of_fset s) = size s"
  by (metis distinct_list_of_fset fset_from_list_of_fset size_fset_from_list)

lemma nth_list_of_fset_mem[simp]: "i < size s \<Longrightarrow> list_of_fset s ! i |\<in>| s"
  by (metis fset_from_list_of_fset length_list_of_fset mem_fset_from_list nth_mem)

inductive indexed_fmember :: "'a \<Rightarrow> nat \<Rightarrow> 'a fset \<Rightarrow> bool" ("_ |\<in>|\<^bsub>_\<^esub> _" [50,50,50] 50 ) where
  "i < size s \<Longrightarrow> list_of_fset s ! i |\<in>|\<^bsub>i\<^esub> s"

lemma indexed_fmember_is_fmember: "x |\<in>|\<^bsub>i\<^esub> s \<Longrightarrow> x |\<in>| s"
proof (induction rule: indexed_fmember.induct)
case (1 i s)
   hence "i < length (list_of_fset s)" by (metis length_list_of_fset)
   hence "list_of_fset s ! i \<in> set (list_of_fset s)" by (rule nth_mem)
   thus "list_of_fset s ! i |\<in>| s" by (metis mem_fset_from_list fset_from_list_of_fset)
qed 

lemma fmember_is_indexed_fmember:
  assumes "x |\<in>| s"
  shows "\<exists>i. x |\<in>|\<^bsub>i\<^esub> s"
proof-
  from assms
  have "x \<in> set (list_of_fset s)" using mem_fset_from_list by fastforce
  then obtain i where "i < length (list_of_fset s)" and "x = list_of_fset s ! i" by (metis in_set_conv_nth)
  hence "x |\<in>|\<^bsub>i\<^esub> s"  by (simp add: indexed_fmember.simps)
  thus ?thesis..
qed


lemma indexed_fmember_unique: "x |\<in>|\<^bsub>i\<^esub> s \<Longrightarrow> y |\<in>|\<^bsub>j\<^esub> s \<Longrightarrow> x = y \<longleftrightarrow> i = j"
  by (metis distinct_list_of_fset indexed_fmember.cases length_list_of_fset nth_eq_iff_index_eq)

definition indexed_members :: "'a fset \<Rightarrow> (nat \<times> 'a) list" where
  "indexed_members s = zip [0..<size s] (list_of_fset s)"

lemma mem_set_indexed_members:
  "(i,x) \<in> set (indexed_members s) \<longleftrightarrow> x |\<in>|\<^bsub>i\<^esub> s"
  unfolding indexed_members_def indexed_fmember.simps
  by (force simp add: set_zip)

lemma mem_set_indexed_members'[simp]:
  "t \<in> set (indexed_members s) \<longleftrightarrow> snd t |\<in>|\<^bsub>fst t\<^esub> s"
  by (cases t, simp add: mem_set_indexed_members)

definition fnth (infixl "|!|" 100)  where
  "s |!| n = list_of_fset s ! n"
lemma fnth_indexed_fmember: "i < size s \<Longrightarrow> s |!| i |\<in>|\<^bsub>i\<^esub> s"
  unfolding fnth_def by (rule indexed_fmember.intros)
lemma indexed_fmember_fnth: "x |\<in>|\<^bsub>i\<^esub> s \<longleftrightarrow> (s |!| i = x \<and> i < size s)"
 unfolding fnth_def by (metis indexed_fmember.simps)
end

definition fidx :: "'a fset \<Rightarrow> 'a \<Rightarrow> nat" where
  "fidx s x = (SOME i. x |\<in>|\<^bsub>i\<^esub> s)"

lemma fidx_eq[simp]: "x |\<in>|\<^bsub>i\<^esub> s \<Longrightarrow> fidx s x = i"
  unfolding fidx_def
  by (rule someI2)(auto simp add: indexed_fmember_fnth fnth_def nth_eq_iff_index_eq)

lemma fidx_inj[simp]: "x |\<in>| s \<Longrightarrow> y |\<in>| s \<Longrightarrow> fidx s x = fidx s y \<longleftrightarrow> x = y"
  by (auto dest!: fmember_is_indexed_fmember simp add: indexed_fmember_unique)

lemma inj_on_fidx: "inj_on (fidx vertices) (fset vertices)"
  by (rule inj_onI) (auto simp: fmember.rep_eq [symmetric])

end
