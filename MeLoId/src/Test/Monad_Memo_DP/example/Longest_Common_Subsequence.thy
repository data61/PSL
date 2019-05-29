subsection \<open>Longest Common Subsequence\<close>

theory Longest_Common_Subsequence
  imports
    "HOL-Library.Sublist"
    "HOL-Library.IArray"
    "HOL-Library.Code_Target_Numeral"
    "HOL-Library.Product_Lexorder"
    "../state_monad/State_Main"
begin

subsubsection \<open>Misc\<close>

(* TODO: Move *)
lemma finite_subseq:
  "finite {xs. subseq xs ys}" (is "finite ?S")
proof -
  have "?S \<subseteq> {xs. set xs \<subseteq> set ys \<and> length xs \<le> length ys}"
    by (auto elim: list_emb_set intro: list_emb_length)
  moreover have "finite \<dots>"
    by (intro finite_lists_length_le finite_set)
  ultimately show ?thesis
    by (rule finite_subset)
qed

lemma subseq_singleton_right:
  "subseq xs [x] = (xs = [x] \<or> xs = [])"
  by (cases xs; simp add: subseq_append_le_same_iff[of _ "[]", simplified])

lemma subseq_append_single_right:
  "subseq xs (ys @ [x]) = ((\<exists> xs'. subseq xs' ys \<and> xs = xs' @ [x]) \<or> subseq xs ys)"
  by (auto simp: subseq_append_iff subseq_singleton_right)

(* TODO: Move, generalize *)
lemma Max_nat_plus:
  "Max ((op + n) ` S) = (n :: nat) + Max S" if "finite S" "S \<noteq> {}"
  using that by (auto intro!: Max_ge Max_in Max_eqI)


subsubsection \<open>Definitions\<close>

context
  fixes A B :: "'a list"
begin

fun lcs :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "lcs 0 _ = 0" |
  "lcs _ 0 = 0" |
  "lcs (Suc i) (Suc j) = (if A!i = B!j then 1 + lcs i j else max (lcs i (j + 1)) (lcs (i + 1) j))"

definition "OPT i j = Max {length xs | xs. subseq xs (take i A) \<and> subseq xs (take j B)}"

lemma finite_OPT:
  "finite {xs. subseq xs (take i A) \<and> subseq xs (take j B)}" (is "finite ?S")
proof -
  have "?S \<subseteq> {xs. subseq xs (take i A)}"
    by auto
  moreover have "finite \<dots>"
    by (rule finite_subseq)
  ultimately show ?thesis
    by (rule finite_subset)
qed

subsubsection \<open>Correctness Proof\<close>
lemma non_empty_OPT:
  "{xs. subseq xs (take i A) \<and> subseq xs (take j B)} \<noteq> {}"
  by auto

lemma OPT_0_left:
  "OPT 0 j = 0"
  unfolding OPT_def by (simp add: subseq_append_le_same_iff[of _ "[]", simplified])

lemma OPT_0_right:
  "OPT i 0 = 0"
  unfolding OPT_def by (simp add: subseq_append_le_same_iff[of _ "[]", simplified])

lemma OPT_rec1:
  "OPT (i + 1) (j + 1) = 1 + OPT i j" (is "?l = ?r")
  if "A!i = B!j" "i < length A" "j < length B"
proof -
  let ?S = "{length xs |xs. subseq xs (take (i + 1) A) \<and> subseq xs (take (j + 1) B)}"
  let ?R = "{length xs + 1 |xs. subseq xs (take i A) \<and> subseq xs (take j B)}"
  have "?S = {length xs | xs. subseq xs (take i A) \<and> subseq xs (take j B)}
    \<union> {length xs | xs. \<exists> ys. subseq ys (take i A) \<and> subseq ys (take j B) \<and> xs = ys @ [B!i]}
    "
    using that
    apply (simp add: take_Suc_conv_app_nth)
    apply (simp add: subseq_append_single_right)
    apply auto
    apply (metis length_append_singleton list_emb_prefix subseq_append)+
    done
  moreover have "\<dots> = {length xs | xs. subseq xs (take i A) \<and> subseq xs (take j B)}
    \<union> {length xs + 1 | xs. subseq xs (take i A) \<and> subseq xs (take j B)}"
    by force
  moreover have "Max \<dots> = Max ?R"
    using finite_OPT by - (rule Max_eq_if, auto)
  ultimately show "?l = ?r"
    unfolding OPT_def
    using finite_OPT non_empty_OPT
    by (subst Max_nat_plus[symmetric]) (auto simp: image_def intro: arg_cong[where f = Max])
qed

lemma OPT_rec2:
  "OPT (i + 1) (j + 1) = max (OPT i (j + 1)) (OPT (i + 1) j)" (is "?l = ?r")
  if "A!i \<noteq> B!j" "i < length A" "j < length B"
proof -
  have "{length xs |xs. subseq xs (take (i + 1) A) \<and> subseq xs (take (j + 1) B)}
    = {length xs |xs. subseq xs (take i A) \<and> subseq xs (take (j + 1) B)}
    \<union> {length xs |xs. subseq xs (take (i + 1) A) \<and> subseq xs (take j B)}"
    using that by (auto simp: subseq_append_single_right take_Suc_conv_app_nth)
  with finite_OPT non_empty_OPT show "?l = ?r"
    unfolding OPT_def by (simp) (rule Max_Un, auto)
qed

lemma lcs_correct':
  "OPT i j = lcs i j" if "i \<le> length A" "j \<le> length B"
  using that OPT_rec1 OPT_rec2 by (induction i j rule: lcs.induct; simp add: OPT_0_left OPT_0_right)

theorem lcs_correct:
  "Max {length xs | xs. subseq xs A \<and> subseq xs B} = lcs (length A) (length B)"
  by (simp add: OPT_def lcs_correct'[symmetric])

end (* Fixed Lists *)


subsubsection \<open>Functional Memoization\<close>

context
  fixes A B :: "'a iarray"
begin

fun lcs_ia :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "lcs_ia 0 _ = 0" |
  "lcs_ia _ 0 = 0" |
  "lcs_ia (Suc i) (Suc j) =
    (if A!!i = B!!j then 1 + lcs_ia i j else max (lcs_ia i (j + 1)) (lcs_ia (i + 1) j))"

lemma lcs_lcs_ia:
  "lcs xs ys i j = lcs_ia i j" if "A = IArray xs" "B = IArray ys"
  by (induction i j rule: lcs_ia.induct; simp; simp add: that)

memoize_fun lcs\<^sub>m: lcs_ia with_memory dp_consistency_rbt monadifies (state) lcs_ia.simps

memoize_correct
  by memoize_prover

lemmas [code] = lcs\<^sub>m.memoized_correct

end

subsubsection \<open>Test Case\<close>

definition lcs\<^sub>a where
  "lcs\<^sub>a xs ys = (let A = IArray xs; B = IArray ys in lcs_ia A B (length xs) (length ys))"

lemma lcs\<^sub>a_correct:
  "lcs xs ys (length xs) (length ys) = lcs\<^sub>a xs ys"
  unfolding lcs\<^sub>a_def by (simp add: lcs_lcs_ia)

value "lcs\<^sub>a ''ABCDGH'' ''AEDFHR''"

value "lcs\<^sub>a ''AGGTAB'' ''GXTXAYB''"

end (* Theory *)