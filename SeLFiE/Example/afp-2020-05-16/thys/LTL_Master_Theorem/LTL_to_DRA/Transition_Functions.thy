(*
    Author:   Benedikt Seidl
    License:  BSD
*)

section \<open>Transition Functions for Deterministic Automata\<close>

theory Transition_Functions
imports
  "../Logical_Characterization/After"
  "../Logical_Characterization/Advice"
begin

text \<open>
  This theory defines three functions based on the ``after''-function
  which we use as transition functions for deterministic automata.
\<close>

locale transition_functions =
  af_congruent + GF_advice_congruent
begin

subsection \<open>After Functions with Resets for @{term "GF(\<mu>LTL)"} and @{term "FG(\<nu>LTL)"}\<close>

definition af_letter\<^sub>F :: "'a ltln \<Rightarrow> 'a ltln \<Rightarrow> 'a set \<Rightarrow> 'a ltln"
where
  "af_letter\<^sub>F \<phi> \<psi> \<nu> = (if \<psi> \<sim> true\<^sub>n then F\<^sub>n \<phi> else af_letter \<psi> \<nu>)"

definition af_letter\<^sub>G :: "'a ltln \<Rightarrow> 'a ltln \<Rightarrow> 'a set \<Rightarrow> 'a ltln"
where
  "af_letter\<^sub>G \<phi> \<psi> \<nu> = (if \<psi> \<sim> false\<^sub>n then G\<^sub>n \<phi> else af_letter \<psi> \<nu>)"

abbreviation af\<^sub>F :: "'a ltln \<Rightarrow> 'a ltln \<Rightarrow> 'a set list \<Rightarrow> 'a ltln"
where
  "af\<^sub>F \<phi> \<psi> w \<equiv> foldl (af_letter\<^sub>F \<phi>) \<psi> w"

abbreviation af\<^sub>G :: "'a ltln \<Rightarrow> 'a ltln \<Rightarrow> 'a set list \<Rightarrow> 'a ltln"
where
  "af\<^sub>G \<phi> \<psi> w \<equiv> foldl (af_letter\<^sub>G \<phi>) \<psi> w"


lemma af\<^sub>F_step:
  "af\<^sub>F \<phi> \<psi> w \<sim> true\<^sub>n \<Longrightarrow> af\<^sub>F \<phi> \<psi> (w @ [\<nu>]) = F\<^sub>n \<phi>"
  by (induction w rule: rev_induct) (auto simp: af_letter\<^sub>F_def)

lemma af\<^sub>G_step:
  "af\<^sub>G \<phi> \<psi> w \<sim> false\<^sub>n \<Longrightarrow> af\<^sub>G \<phi> \<psi> (w @ [\<nu>]) = G\<^sub>n \<phi>"
  by (induction w rule: rev_induct) (auto simp: af_letter\<^sub>G_def)

lemma af\<^sub>F_segments:
  "af\<^sub>F \<phi> \<psi> w = F\<^sub>n \<phi> \<Longrightarrow> af\<^sub>F \<phi> \<psi> (w @ w') = af\<^sub>F \<phi> (F\<^sub>n \<phi>) w'"
  by simp

lemma af\<^sub>G_segments:
  "af\<^sub>G \<phi> \<psi> w = G\<^sub>n \<phi> \<Longrightarrow> af\<^sub>G \<phi> \<psi> (w @ w') = af\<^sub>G \<phi> (G\<^sub>n \<phi>) w'"
  by simp


lemma af_not_true_implies_af_equals_af\<^sub>F:
  "(\<And>xs ys. w = xs @ ys \<Longrightarrow> \<not> af \<psi> xs \<sim> true\<^sub>n) \<Longrightarrow> af\<^sub>F \<phi> \<psi> w = af \<psi> w"
proof (induction w rule: rev_induct)
  case (snoc x xs)

  then have "af\<^sub>F \<phi> \<psi> xs = af \<psi> xs"
    by simp

  moreover

  have "\<not> af \<psi> xs \<sim> true\<^sub>n"
    using snoc.prems by blast

  ultimately show ?case
    by (metis af_letter\<^sub>F_def foldl_Cons foldl_Nil foldl_append)
qed simp

lemma af_not_false_implies_af_equals_af\<^sub>G:
  "(\<And>xs ys. w = xs @ ys \<Longrightarrow> \<not> af \<psi> xs \<sim> false\<^sub>n) \<Longrightarrow> af\<^sub>G \<phi> \<psi> w = af \<psi> w"
proof (induction w rule: rev_induct)
  case (snoc x xs)

  then have "af\<^sub>G \<phi> \<psi> xs = af \<psi> xs"
    by simp

  moreover

  have "\<not> af \<psi> xs \<sim> false\<^sub>n"
    using snoc.prems by blast

  ultimately show ?case
    by (metis af_letter\<^sub>G_def foldl_Cons foldl_Nil foldl_append)
qed simp


lemma af\<^sub>F_not_true_implies_af_equals_af\<^sub>F:
  "(\<And>xs ys. w = xs @ ys \<Longrightarrow> \<not> af\<^sub>F \<phi> \<psi> xs \<sim> true\<^sub>n) \<Longrightarrow> af\<^sub>F \<phi> \<psi> w = af \<psi> w"
proof (induction w rule: rev_induct)
  case (snoc x xs)

  then have "af\<^sub>F \<phi> \<psi> xs = af \<psi> xs"
    by simp

  moreover

  have "\<not> af\<^sub>F \<phi> \<psi> xs \<sim> true\<^sub>n"
    using snoc.prems by blast

  ultimately show ?case
    by (metis af_letter\<^sub>F_def foldl_Cons foldl_Nil foldl_append)
qed simp

lemma af\<^sub>G_not_false_implies_af_equals_af\<^sub>G:
  "(\<And>xs ys. w = xs @ ys \<Longrightarrow> \<not> af\<^sub>G \<phi> \<psi> xs \<sim> false\<^sub>n) \<Longrightarrow> af\<^sub>G \<phi> \<psi> w = af \<psi> w"
proof (induction w rule: rev_induct)
  case (snoc x xs)

  then have "af\<^sub>G \<phi> \<psi> xs = af \<psi> xs"
    by simp

  moreover

  have "\<not> af\<^sub>G \<phi> \<psi> xs \<sim> false\<^sub>n"
    using snoc.prems by blast

  ultimately show ?case
    by (metis af_letter\<^sub>G_def foldl_Cons foldl_Nil foldl_append)
qed simp


lemma af\<^sub>F_true_implies_af_true:
  "af\<^sub>F \<phi> \<psi> w \<sim> true\<^sub>n \<Longrightarrow> af \<psi> w \<sim> true\<^sub>n"
  by (metis af_append_true af_not_true_implies_af_equals_af\<^sub>F)

lemma af\<^sub>G_false_implies_af_false:
  "af\<^sub>G \<phi> \<psi> w \<sim> false\<^sub>n \<Longrightarrow> af \<psi> w \<sim> false\<^sub>n"
  by (metis af_append_false af_not_false_implies_af_equals_af\<^sub>G)


lemma af_equiv_true_af\<^sub>F_prefix_true:
  "af \<psi> w \<sim> true\<^sub>n \<Longrightarrow> \<exists>xs ys. w = xs @ ys \<and> af\<^sub>F \<phi> \<psi> xs \<sim> true\<^sub>n"
proof (induction w rule: rev_induct)
  case (snoc a w)
  then show ?case
  proof (cases "af \<psi> w \<sim> true\<^sub>n")
    case False

    then have "\<And>xs ys. w = xs @ ys \<Longrightarrow> \<not> af \<psi> xs \<sim> true\<^sub>n"
      using af_append_true by blast

    then have "af\<^sub>F \<phi> \<psi> w = af \<psi> w"
      using af_not_true_implies_af_equals_af\<^sub>F by auto

    then have "af\<^sub>F \<phi> \<psi> (w @ [a]) = af \<psi> (w @ [a])"
      by (simp add: False af_letter\<^sub>F_def)

    then show ?thesis
      by (metis append_Nil2 snoc.prems)
  qed (insert snoc, force)
qed (simp add: const_implies_eq)

lemma af_equiv_false_af\<^sub>G_prefix_false:
  "af \<psi> w \<sim> false\<^sub>n \<Longrightarrow> \<exists>xs ys. w = xs @ ys \<and> af\<^sub>G \<phi> \<psi> xs \<sim> false\<^sub>n"
proof (induction w rule: rev_induct)
  case (snoc a w)
  then show ?case
  proof (cases "af \<psi> w \<sim> false\<^sub>n")
    case False

    then have "\<And>xs ys. w = xs @ ys \<Longrightarrow> \<not> af \<psi> xs \<sim> false\<^sub>n"
      using af_append_false by blast

    then have "af\<^sub>G \<phi> \<psi> w = af \<psi> w"
      using af_not_false_implies_af_equals_af\<^sub>G by auto

    then have "af\<^sub>G \<phi> \<psi> (w @ [a]) = af \<psi> (w @ [a])"
      by (simp add: False af_letter\<^sub>G_def)

    then show ?thesis
      by (metis append_Nil2 snoc.prems)
  qed (insert snoc, force)
qed (simp add: const_implies_eq)


lemma append_take_drop:
  "w = xs @ ys \<longleftrightarrow> xs = take (length xs) w \<and> ys = drop (length xs) w"
  by (metis append_eq_conv_conj)

lemma subsequence_split:
  "(w [i \<rightarrow> j]) = xs @ ys \<Longrightarrow> xs = (w [i \<rightarrow> i + length xs])"
  by (simp add: append_take_drop) (metis add_diff_cancel_left' subsequence_length subsequence_prefix_suffix)

lemma subsequence_append_general:
  "i \<le> k \<Longrightarrow> k \<le> j \<Longrightarrow> (w [i \<rightarrow> j]) = (w [i \<rightarrow> k]) @ (w [k \<rightarrow> j])"
  by (metis le_Suc_ex map_append subsequence_def upt_add_eq_append)


lemma af\<^sub>F_semantics_rtl:
  assumes
    "\<forall>i. \<exists>j>i. af\<^sub>F \<phi> (F\<^sub>n \<phi>) (w [0 \<rightarrow> j]) \<sim> true\<^sub>n"
  shows
    "\<forall>i. \<exists>j. af (F\<^sub>n \<phi>) (w [i \<rightarrow> j]) \<sim>\<^sub>L true\<^sub>n"
proof
  fix i
  from assms obtain j where "j > i" and "af\<^sub>F \<phi> (F\<^sub>n \<phi>) (w [0 \<rightarrow> j]) \<sim> true\<^sub>n"
    by blast
  then have X: "af\<^sub>F \<phi> (F\<^sub>n \<phi>) (w [0 \<rightarrow> Suc j]) = F\<^sub>n \<phi>"
    using af\<^sub>F_step by auto

  obtain k where "k > j" and "af\<^sub>F \<phi> (F\<^sub>n \<phi>) (w [0 \<rightarrow> k]) \<sim> true\<^sub>n"
    using assms using Suc_le_eq by blast
  then have "af\<^sub>F \<phi> (F\<^sub>n \<phi>) (w [Suc j \<rightarrow> k]) \<sim> true\<^sub>n"
    using af\<^sub>F_segments[OF X] by (metis le_Suc_ex le_simps(3) subsequence_append)
  then have "af (F\<^sub>n \<phi>) (w [Suc j \<rightarrow> k]) \<sim> true\<^sub>n"
    using af\<^sub>F_true_implies_af_true by blast
  then show "\<exists>k. af (F\<^sub>n \<phi>) (w [i \<rightarrow> k]) \<sim>\<^sub>L true\<^sub>n"
    by (metis (full_types) af_F_prefix_lang_equiv_true eq_implies_lang subsequence_append_general Suc_le_eq \<open>i < j\<close> \<open>j < k\<close> less_SucI order.order_iff_strict)
qed

lemma af\<^sub>F_semantics_ltr:
  assumes
    "\<forall>i. \<exists>j. af (F\<^sub>n \<phi>) (w [i \<rightarrow> j]) \<sim> true\<^sub>n"
  shows
    "\<forall>i. \<exists>j>i. af\<^sub>F \<phi> (F\<^sub>n \<phi>) (w [0 \<rightarrow> j]) \<sim> true\<^sub>n"
proof (rule ccontr)
  define resets where "resets = {i. af\<^sub>F \<phi> (F\<^sub>n \<phi>) (w [0 \<rightarrow> i]) \<sim> true\<^sub>n}"
  define m where "m = (if resets = {} then 0 else Suc (Max resets))"

  assume "\<not> (\<forall>i. \<exists>j>i. af\<^sub>F \<phi> (F\<^sub>n \<phi>) (w [0 \<rightarrow> j]) \<sim> true\<^sub>n)"

  then have "finite resets"
    using infinite_nat_iff_unbounded resets_def by force
  then have "resets \<noteq> {} \<Longrightarrow> af\<^sub>F \<phi> (F\<^sub>n \<phi>) (w [0 \<rightarrow> Max resets]) \<sim> true\<^sub>n"
    unfolding resets_def using Max_in by blast
  then have m_reset: "af\<^sub>F \<phi> (F\<^sub>n \<phi>) (w [0 \<rightarrow> m]) = F\<^sub>n \<phi>"
    unfolding m_def using af\<^sub>F_step by auto

  {
    fix i
    assume "i \<ge> m"

    with m_reset have "\<not> af\<^sub>F \<phi> (F\<^sub>n \<phi>) (w [0 \<rightarrow> i]) \<sim> true\<^sub>n"
      by (metis (mono_tags, lifting) Max_ge_iff Suc_n_not_le_n \<open>finite resets\<close> empty_Collect_eq m_def mem_Collect_eq resets_def)
    with m_reset have "\<not> af\<^sub>F \<phi>  (F\<^sub>n \<phi>)(w [m \<rightarrow> i]) \<sim> true\<^sub>n"
      by (metis (mono_tags, hide_lams) \<open>m \<le> i\<close> af\<^sub>F_segments bot_nat_def le0 subsequence_append_general)
  }

  then have "\<nexists>j. af\<^sub>F \<phi> (F\<^sub>n \<phi>) (w [m \<rightarrow> j]) \<sim> true\<^sub>n"
    by (metis le_cases subseq_to_smaller)
  then have "\<nexists>j. af (F\<^sub>n \<phi>) (w [m \<rightarrow> j]) \<sim> true\<^sub>n"
    by (metis af_equiv_true_af\<^sub>F_prefix_true subsequence_split)
  then show False
    using assms by blast
qed


lemma af\<^sub>G_semantics_rtl:
  assumes
    "\<exists>i. \<forall>j>i. \<not> af\<^sub>G \<phi> (G\<^sub>n \<phi>) (w [0 \<rightarrow> j]) \<sim> false\<^sub>n"
  shows
    "\<exists>i. \<forall>j. \<not> af (G\<^sub>n \<phi>) (w [i \<rightarrow> j]) \<sim> false\<^sub>n"
proof
  define resets where "resets = {i. af\<^sub>G \<phi> (G\<^sub>n \<phi>) (w [0 \<rightarrow> i]) \<sim> false\<^sub>n}"
  define m where "m = (if resets = {} then 0 else Suc (Max resets))"

  from assms have "finite resets"
    by (metis (mono_tags, lifting) infinite_nat_iff_unbounded mem_Collect_eq resets_def)
  then have "resets \<noteq> {} \<Longrightarrow> af\<^sub>G \<phi> (G\<^sub>n \<phi>) (w [0 \<rightarrow> Max resets]) \<sim> false\<^sub>n"
    unfolding resets_def using Max_in by blast
  then have m_reset: "af\<^sub>G \<phi> (G\<^sub>n \<phi>) (w [0 \<rightarrow> m]) = G\<^sub>n \<phi>"
    unfolding m_def using af\<^sub>G_step by auto

  {
    fix i
    assume "i \<ge> m"

    with m_reset have "\<not> af\<^sub>G \<phi> (G\<^sub>n \<phi>) (w [0 \<rightarrow> i]) \<sim> false\<^sub>n"
      by (metis (mono_tags, lifting) Max_ge_iff Suc_n_not_le_n \<open>finite resets\<close> empty_Collect_eq m_def mem_Collect_eq resets_def)
    with m_reset have "\<not> af\<^sub>G \<phi> (G\<^sub>n \<phi>) (w [m \<rightarrow> i]) \<sim> false\<^sub>n"
      by (metis (mono_tags, hide_lams) \<open>m \<le> i\<close> af\<^sub>G_segments bot_nat_def le0 subsequence_append_general)
  }

  then have "\<forall>j. \<not> af\<^sub>G \<phi> (G\<^sub>n \<phi>) (w [m \<rightarrow> j]) \<sim> false\<^sub>n"
    by (metis le_cases subseq_to_smaller)
  then show "\<forall>j. \<not> af (G\<^sub>n \<phi>) (w [m \<rightarrow> j]) \<sim> false\<^sub>n"
    by (metis af_equiv_false_af\<^sub>G_prefix_false subsequence_split)
qed

lemma af\<^sub>G_semantics_ltr:
  assumes
    "\<exists>i. \<forall>j. \<not> af (G\<^sub>n \<phi>) (w [i \<rightarrow> j]) \<sim>\<^sub>L false\<^sub>n"
  shows
    "\<exists>i. \<forall>j>i. \<not> af\<^sub>G \<phi> (G\<^sub>n \<phi>) (w [0 \<rightarrow> j]) \<sim> false\<^sub>n"
proof (rule ccontr, auto)
  assume 1: "\<forall>i. \<exists>j>i. af\<^sub>G \<phi> (G\<^sub>n \<phi>) (w [0 \<rightarrow> j]) \<sim> false\<^sub>n"

  {
    fix i
    obtain j where "j > i" and "af\<^sub>G \<phi> (G\<^sub>n \<phi>) (w [0 \<rightarrow> j]) \<sim> false\<^sub>n"
      using 1 by blast
    then have X: "af\<^sub>G \<phi> (G\<^sub>n \<phi>) (w [0 \<rightarrow> Suc j]) = G\<^sub>n \<phi>"
      using af\<^sub>G_step by auto

    obtain k where "k > j" and "af\<^sub>G \<phi> (G\<^sub>n \<phi>) (w [0 \<rightarrow> k]) \<sim> false\<^sub>n"
      using 1 using Suc_le_eq by blast
    then have "af\<^sub>G \<phi> (G\<^sub>n \<phi>) (w [Suc j \<rightarrow> k]) \<sim> false\<^sub>n"
      using af\<^sub>G_segments[OF X] by (metis le_Suc_ex le_simps(3) subsequence_append)
    then have "af (G\<^sub>n \<phi>) (w [Suc j \<rightarrow> k]) \<sim> false\<^sub>n"
      using af\<^sub>G_false_implies_af_false by fastforce
    then have "af (G\<^sub>n \<phi>) (w [Suc j \<rightarrow> k]) \<sim>\<^sub>L false\<^sub>n"
      using eq_implies_lang by fastforce
    then have "af (G\<^sub>n \<phi>) (w [i \<rightarrow> k]) \<sim>\<^sub>L false\<^sub>n"
      by (metis (full_types) af_G_prefix_lang_equiv_false subsequence_append_general Suc_le_eq \<open>i < j\<close> \<open>j < k\<close> less_SucI order.order_iff_strict)
    then have "\<exists>j. af (G\<^sub>n \<phi>) (w [i \<rightarrow> j]) \<sim>\<^sub>L false\<^sub>n"
      by fast
  }

  then show False
    using assms by blast
qed



subsection \<open>After Function using GF-advice\<close>

definition af_letter\<^sub>\<nu> :: "'a ltln set \<Rightarrow> 'a ltln \<times> 'a ltln \<Rightarrow> 'a set \<Rightarrow> 'a ltln \<times> 'a ltln"
where
  "af_letter\<^sub>\<nu> X p \<nu> = (if snd p \<sim> false\<^sub>n
    then (af_letter (fst p) \<nu>, (normalise (af_letter (fst p) \<nu>))[X]\<^sub>\<nu>)
    else (af_letter (fst p) \<nu>, af_letter (snd p) \<nu>))"

abbreviation af\<^sub>\<nu> :: "'a ltln set \<Rightarrow> 'a ltln \<times> 'a ltln \<Rightarrow> 'a set list \<Rightarrow> 'a ltln \<times> 'a ltln"
where
  "af\<^sub>\<nu> X p w \<equiv> foldl (af_letter\<^sub>\<nu> X) p w"

lemma af_letter\<^sub>\<nu>_fst[simp]:
  "fst (af_letter\<^sub>\<nu> X p \<nu>) = af_letter (fst p) \<nu>"
  by (simp add: af_letter\<^sub>\<nu>_def)

lemma af_letter\<^sub>\<nu>_snd[simp]:
  "snd p \<sim> false\<^sub>n \<Longrightarrow> snd (af_letter\<^sub>\<nu> X p \<nu>) = (normalise (af_letter (fst p) \<nu>))[X]\<^sub>\<nu>"
  "\<not> (snd p) \<sim> false\<^sub>n \<Longrightarrow> snd (af_letter\<^sub>\<nu> X p \<nu>) = af_letter (snd p) \<nu>"
  by (simp_all add: af_letter\<^sub>\<nu>_def)

lemma af\<^sub>\<nu>_fst:
  "fst (af\<^sub>\<nu> X p w) = af (fst p) w"
  by (induction w rule: rev_induct) simp+

lemma af\<^sub>\<nu>_snd:
  "\<not> af (snd p) w \<sim> false\<^sub>n \<Longrightarrow> snd (af\<^sub>\<nu> X p w) = af (snd p) w"
  by (induction w rule: rev_induct) (simp_all, metis af_letter\<^sub>\<nu>_snd(2) af_letter.simps(2) af_letter_congruent)

lemma af\<^sub>\<nu>_snd':
  "\<forall>i. \<not> snd (af\<^sub>\<nu> X p (take i w)) \<sim> false\<^sub>n \<Longrightarrow> snd (af\<^sub>\<nu> X p w) = af (snd p) w"
  by (induction w rule: rev_induct) (simp_all, metis af_letter\<^sub>\<nu>_snd(2) diff_is_0_eq foldl_Nil le_cases take_all take_eq_Nil)

lemma af\<^sub>\<nu>_step:
  "snd (af\<^sub>\<nu> X (\<xi>, \<zeta>) w) \<sim> false\<^sub>n \<Longrightarrow> snd (af\<^sub>\<nu> X (\<xi>, \<zeta>) (w @ [\<nu>])) = (normalise (af \<xi> (w @ [\<nu>])))[X]\<^sub>\<nu>"
  by (simp add: af\<^sub>\<nu>_fst)

lemma af\<^sub>\<nu>_segments:
  "af\<^sub>\<nu> X (\<xi>, \<zeta>) w = (af \<xi> w, (af \<xi> w)[X]\<^sub>\<nu>) \<Longrightarrow> af\<^sub>\<nu> X (\<xi>, \<zeta>) (w @ w') = af\<^sub>\<nu> X (af \<xi> w, (af \<xi> w)[X]\<^sub>\<nu>) w'"
  by (induction w' rule: rev_induct) fastforce+


lemma af\<^sub>\<nu>_semantics_ltr:
  assumes
    "\<exists>i. suffix i w \<Turnstile>\<^sub>n (af \<phi> (prefix i w))[X]\<^sub>\<nu>"
  shows
    "\<exists>m. \<forall>k\<ge>m. \<not> snd (af\<^sub>\<nu> X (\<phi>, (normalise \<phi>)[X]\<^sub>\<nu>) (prefix (Suc k) w)) \<sim> false\<^sub>n"
proof
  define resets where "resets = {i. snd (af\<^sub>\<nu> X (\<phi>, (normalise \<phi>)[X]\<^sub>\<nu>) (prefix i w)) \<sim> false\<^sub>n}"
  define m where "m = (if resets = {} then 0 else Suc (Max resets))"

  from assms obtain i where 1: "suffix i w \<Turnstile>\<^sub>n (af \<phi> (prefix i w))[X]\<^sub>\<nu>"
    by blast

  {
    fix j
    assume "i \<le> j" and "j \<in> resets"

    let ?\<phi> = "af \<phi> (prefix (Suc j) w)"

    from 1 have "\<forall>n. suffix n (suffix i w) \<Turnstile>\<^sub>n (normalise (af \<phi> (prefix i w @ prefix n (suffix i w))))[X]\<^sub>\<nu>"
      using normalise_monotonic by (simp add: GF_advice_af)

    then have "suffix (Suc j) w \<Turnstile>\<^sub>n (normalise (af \<phi> (prefix (Suc j) w)))[X]\<^sub>\<nu>"
      by (metis (no_types) \<open>i \<le> j\<close> add.right_neutral le_SucI le_Suc_ex subsequence_append subsequence_shift suffix_suffix)

    then have "\<forall>k>j. \<not> af ((normalise (af \<phi> (prefix (Suc j) w)))[X]\<^sub>\<nu>) (w [Suc j \<rightarrow> k]) \<sim> false\<^sub>n"
      by (metis ltl_implies_satisfiable_prefix subsequence_prefix_suffix)

    then have "\<forall>k>j. \<not> snd (af\<^sub>\<nu> X (?\<phi>, (normalise ?\<phi>)[X]\<^sub>\<nu>) (w [Suc j \<rightarrow> k])) \<sim> false\<^sub>n"
      by (metis af\<^sub>\<nu>_snd snd_eqD)

    moreover

    {
      have "fst (af\<^sub>\<nu> X (\<phi>, (normalise \<phi>)[X]\<^sub>\<nu>) (prefix (Suc j) w)) = ?\<phi>"
        by (simp add: af\<^sub>\<nu>_fst)

      moreover

      have "snd (af\<^sub>\<nu> X (\<phi>, (normalise \<phi>)[X]\<^sub>\<nu>) (prefix j w)) \<sim> false\<^sub>n"
        using \<open>j \<in> resets\<close> resets_def by blast

      ultimately have "af\<^sub>\<nu> X (\<phi>, (normalise \<phi>)[X]\<^sub>\<nu>) (prefix (Suc j) w) = (?\<phi>, (normalise ?\<phi>)[X]\<^sub>\<nu>)"
        by (metis (no_types) af\<^sub>\<nu>_step prod.collapse subseq_to_Suc zero_le)
    }

    ultimately have "\<forall>k>j. \<not> snd (af\<^sub>\<nu> X (\<phi>, (normalise \<phi>)[X]\<^sub>\<nu>) ((w [0 \<rightarrow> Suc j]) @ (w [Suc j \<rightarrow> k]))) \<sim> false\<^sub>n"
      by (simp add: af\<^sub>\<nu>_segments)

    then have "\<forall>k>j. \<not> snd (af\<^sub>\<nu> X (\<phi>, (normalise \<phi>)[X]\<^sub>\<nu>) (prefix k w)) \<sim> false\<^sub>n"
      by (metis Suc_leI le0 subsequence_append_general)

    then have "\<forall>k \<in> resets. k \<le> j"
      using \<open>j \<in> resets\<close> resets_def le_less_linear by blast
  }

  then have "finite resets"
    by (meson finite_nat_set_iff_bounded_le infinite_nat_iff_unbounded_le)

  then have "resets \<noteq> {} \<Longrightarrow> snd (af\<^sub>\<nu> X (\<phi>, (normalise \<phi>)[X]\<^sub>\<nu>) (prefix (Max resets) w)) \<sim> false\<^sub>n"
    using Max_in resets_def by blast

  then have "\<forall>k\<ge>m. \<not> snd (af\<^sub>\<nu> X (\<phi>, (normalise \<phi>)[X]\<^sub>\<nu>) (prefix k w)) \<sim> false\<^sub>n"
    by (metis (mono_tags, lifting) Max_ge Suc_n_not_le_n \<open>finite resets\<close> empty_Collect_eq m_def mem_Collect_eq order.trans resets_def)

  then show "\<forall>k\<ge>m. \<not> snd (af\<^sub>\<nu> X (\<phi>, (normalise \<phi>)[X]\<^sub>\<nu>) (prefix (Suc k) w)) \<sim> false\<^sub>n"
    using le_SucI by blast
qed

lemma af\<^sub>\<nu>_semantics_rtl:
  assumes
    "\<exists>n. \<forall>k\<ge>n. \<not> snd (af\<^sub>\<nu> X (\<phi>, (normalise \<phi>)[X]\<^sub>\<nu>) (prefix (Suc k) w)) \<sim> false\<^sub>n"
  shows
    "\<exists>i. suffix i w \<Turnstile>\<^sub>n af \<phi> (prefix i w)[X]\<^sub>\<nu>"
proof -
  define resets where "resets = {i. snd (af\<^sub>\<nu> X (\<phi>, (normalise \<phi>)[X]\<^sub>\<nu>) (prefix i w)) \<sim> false\<^sub>n}"
  define m where "m = (if resets = {} then 0 else Suc (Max resets))"

  from assms obtain n where "\<forall>k\<ge>n. \<not> snd (af\<^sub>\<nu> X (\<phi>, (normalise \<phi>)[X]\<^sub>\<nu>) (prefix (Suc k) w)) \<sim> false\<^sub>n"
    by blast

  then have "\<forall>k>n. \<not> snd (af\<^sub>\<nu> X (\<phi>, (normalise \<phi>)[X]\<^sub>\<nu>) (prefix k w)) \<sim> false\<^sub>n"
    by (metis le_SucE lessE less_imp_le_nat)

  then have "finite resets"
    by (metis (mono_tags, lifting) infinite_nat_iff_unbounded mem_Collect_eq resets_def)

  then have "\<forall>i\<ge>m. \<not> snd (af\<^sub>\<nu> X (\<phi>, (normalise \<phi>)[X]\<^sub>\<nu>) (prefix i w)) \<sim> false\<^sub>n"
    unfolding resets_def m_def using Max_ge not_less_eq_eq by auto

  then have "\<forall>i. \<not> snd (af\<^sub>\<nu> X (\<phi>, (normalise \<phi>)[X]\<^sub>\<nu>) ((w [0 \<rightarrow> m]) @ (w [m \<rightarrow> i]))) \<sim> false\<^sub>n"
    by (metis le0 nat_le_linear subseq_to_smaller subsequence_append_general)

  moreover

  let ?\<phi> = "af \<phi> (prefix m w)"

  have "resets \<noteq> {} \<Longrightarrow> snd (af\<^sub>\<nu> X (\<phi>, (normalise \<phi>)[X]\<^sub>\<nu>) (prefix (Max resets) w)) \<sim> false\<^sub>n"
    using Max_in \<open>finite resets\<close> resets_def by blast

  then have prefix_\<phi>': "snd (af\<^sub>\<nu> X (\<phi>, (normalise \<phi>)[X]\<^sub>\<nu>) (prefix m w)) = (normalise ?\<phi>)[X]\<^sub>\<nu>"
    by (auto simp: GF_advice_congruent m_def af\<^sub>\<nu>_fst)

  ultimately have "\<forall>i. \<not> snd (af\<^sub>\<nu> X (?\<phi>, (normalise ?\<phi>)[X]\<^sub>\<nu>) (w [m \<rightarrow> i])) \<sim> false\<^sub>n"
    by (metis af\<^sub>\<nu>_fst foldl_append fst_conv prod.collapse)

  then have "\<forall>i. \<not> af ((normalise ?\<phi>)[X]\<^sub>\<nu>) (w [m \<rightarrow> i]) \<sim> false\<^sub>n"
    by (metis prefix_\<phi>' af\<^sub>\<nu>_fst af\<^sub>\<nu>_snd' fst_conv prod.collapse subsequence_take)

  then have "suffix m w \<Turnstile>\<^sub>n (normalise (af \<phi> (prefix m w)))[X]\<^sub>\<nu>"
    by (metis GF_advice_\<nu>LTL(1) satisfiable_prefix_implies_\<nu>LTL add.right_neutral subsequence_shift)

  from this[THEN normalise_eventually_equivalent]
    show "\<exists>i. suffix i w \<Turnstile>\<^sub>n af \<phi> (prefix i w)[X]\<^sub>\<nu>"
    by (metis add.commute af_subsequence_append le_add1 le_add_same_cancel1 prefix_suffix_subsequence suffix_suffix)
qed

end


subsection \<open>Reachability Bounds\<close>

text \<open>
  We show that the reach of each after-function is bounded by the atomic
  propositions of the input formula.
\<close>

locale transition_functions_size = transition_functions +
  assumes
    normalise_nested_propos: "nested_prop_atoms \<phi> \<supseteq> nested_prop_atoms (normalise \<phi>)"
begin

lemma af_letter\<^sub>F_nested_prop_atoms:
  "nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms (F\<^sub>n \<phi>) \<Longrightarrow> nested_prop_atoms (af_letter\<^sub>F \<phi> \<psi> \<nu>) \<subseteq> nested_prop_atoms (F\<^sub>n \<phi>)"
  by (induction \<psi>) (auto simp: af_letter\<^sub>F_def, insert af_letter_nested_prop_atoms, blast+)

lemma af\<^sub>F_nested_prop_atoms:
  "nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms (F\<^sub>n \<phi>) \<Longrightarrow> nested_prop_atoms (af\<^sub>F \<phi> \<psi> w) \<subseteq> nested_prop_atoms (F\<^sub>n \<phi>)"
  by (induction w rule: rev_induct) (insert af_letter\<^sub>F_nested_prop_atoms, auto)

lemma af_letter\<^sub>F_range:
  "nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms (F\<^sub>n \<phi>) \<Longrightarrow> range (af_letter\<^sub>F \<phi> \<psi>) \<subseteq> {\<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms (F\<^sub>n \<phi>)}"
  using af_letter\<^sub>F_nested_prop_atoms by blast

lemma af\<^sub>F_range:
  "nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms (F\<^sub>n \<phi>) \<Longrightarrow> range (af\<^sub>F \<phi> \<psi>) \<subseteq> {\<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms (F\<^sub>n \<phi>)}"
  using af\<^sub>F_nested_prop_atoms by blast

lemma af_letter\<^sub>G_nested_prop_atoms:
  "nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms (G\<^sub>n \<phi>) \<Longrightarrow> nested_prop_atoms (af_letter\<^sub>G \<phi> \<psi> \<nu>) \<subseteq> nested_prop_atoms (G\<^sub>n \<phi>)"
  by (induction \<psi>) (auto simp: af_letter\<^sub>G_def, insert af_letter_nested_prop_atoms, blast+)

lemma af\<^sub>G_nested_prop_atoms:
  "nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms (G\<^sub>n \<phi>) \<Longrightarrow> nested_prop_atoms (af\<^sub>G \<phi> \<psi> w) \<subseteq> nested_prop_atoms (G\<^sub>n \<phi>)"
  by (induction w rule: rev_induct) (insert af_letter\<^sub>G_nested_prop_atoms, auto)

lemma af_letter\<^sub>G_range:
  "nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms (G\<^sub>n \<phi>) \<Longrightarrow> range (af_letter\<^sub>G \<phi> \<psi>) \<subseteq> {\<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms (G\<^sub>n \<phi>)}"
  using af_letter\<^sub>G_nested_prop_atoms by blast

lemma af\<^sub>G_range:
  "nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms (G\<^sub>n \<phi>) \<Longrightarrow> range (af\<^sub>G \<phi> \<psi>) \<subseteq> {\<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms (G\<^sub>n \<phi>)}"
  using af\<^sub>G_nested_prop_atoms by blast

lemma af_letter\<^sub>\<nu>_snd_nested_prop_atoms_helper:
  "snd p \<sim> false\<^sub>n \<Longrightarrow> nested_prop_atoms (snd (af_letter\<^sub>\<nu> X p \<nu>)) \<subseteq> nested_prop_atoms\<^sub>\<nu> (fst p) X"
  "\<not> snd p \<sim> false\<^sub>n \<Longrightarrow> nested_prop_atoms (snd (af_letter\<^sub>\<nu> X p \<nu>)) \<subseteq> nested_prop_atoms (snd p)"
  by (simp_all add: af_letter_nested_prop_atoms nested_prop_atoms\<^sub>\<nu>_def)
     (metis GF_advice_nested_prop_atoms\<^sub>\<nu> af_letter_nested_prop_atoms nested_prop_atoms\<^sub>\<nu>_subset dual_order.trans nested_prop_atoms\<^sub>\<nu>_def normalise_nested_propos)

lemma af_letter\<^sub>\<nu>_fst_nested_prop_atoms:
  "nested_prop_atoms (fst (af_letter\<^sub>\<nu> X p \<nu>)) \<subseteq> nested_prop_atoms (fst p)"
  by (simp add: af_letter_nested_prop_atoms)

lemma af_letter\<^sub>\<nu>_snd_nested_prop_atoms:
  "nested_prop_atoms (snd (af_letter\<^sub>\<nu> X p \<nu>)) \<subseteq> (nested_prop_atoms\<^sub>\<nu> (fst p) X) \<union> (nested_prop_atoms (snd p))"
  using af_letter\<^sub>\<nu>_snd_nested_prop_atoms_helper by blast

lemma af_letter\<^sub>\<nu>_fst_range:
  "range (fst \<circ> af_letter\<^sub>\<nu> X p) \<subseteq> {\<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms (fst p)}"
  using af_letter\<^sub>\<nu>_fst_nested_prop_atoms by force

lemma af_letter\<^sub>\<nu>_snd_range:
  "range (snd \<circ> af_letter\<^sub>\<nu> X p) \<subseteq> {\<psi>. nested_prop_atoms \<psi> \<subseteq> (nested_prop_atoms\<^sub>\<nu> (fst p) X) \<union> nested_prop_atoms (snd p)}"
  using af_letter\<^sub>\<nu>_snd_nested_prop_atoms by force

lemma af_letter\<^sub>\<nu>_range:
  "range (af_letter\<^sub>\<nu> X p) \<subseteq> {\<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms (fst p)} \<times> {\<psi>. nested_prop_atoms \<psi> \<subseteq> (nested_prop_atoms\<^sub>\<nu> (fst p) X) \<union> nested_prop_atoms (snd p)}"
proof -
  have "range (af_letter\<^sub>\<nu> X p) \<subseteq> range (fst \<circ> af_letter\<^sub>\<nu> X p) \<times> range (snd \<circ> af_letter\<^sub>\<nu> X p)"
    by (simp add: image_subset_iff mem_Times_iff)

  also have "\<dots> \<subseteq> {\<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms (fst p)} \<times> {\<psi>. nested_prop_atoms \<psi> \<subseteq> (nested_prop_atoms\<^sub>\<nu> (fst p) X) \<union> nested_prop_atoms (snd p)}"
    using af_letter\<^sub>\<nu>_fst_range af_letter\<^sub>\<nu>_snd_range by blast

  finally show ?thesis .
qed

lemma af\<^sub>\<nu>_fst_nested_prop_atoms:
  "nested_prop_atoms (fst (af\<^sub>\<nu> X p w)) \<subseteq> nested_prop_atoms (fst p)"
  by (induction w rule: rev_induct) (auto, insert af_letter_nested_prop_atoms, blast)

lemma af_letter_nested_prop_atoms\<^sub>\<nu>:
  "nested_prop_atoms\<^sub>\<nu> (af_letter \<phi> \<nu>) X \<subseteq> nested_prop_atoms\<^sub>\<nu> \<phi> X"
  by (induction \<phi>) (simp_all add: nested_prop_atoms\<^sub>\<nu>_def, blast+)

lemma af\<^sub>\<nu>_fst_nested_prop_atoms\<^sub>\<nu>:
  "nested_prop_atoms\<^sub>\<nu> (fst (af\<^sub>\<nu> X p w)) X \<subseteq> nested_prop_atoms\<^sub>\<nu> (fst p) X"
  by (induction w rule: rev_induct) (auto, insert af_letter_nested_prop_atoms\<^sub>\<nu>, blast)

lemma af\<^sub>\<nu>_fst_range:
  "range (fst \<circ> af\<^sub>\<nu> X p) \<subseteq> {\<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms (fst p)}"
  using af\<^sub>\<nu>_fst_nested_prop_atoms by fastforce

lemma af\<^sub>\<nu>_snd_nested_prop_atoms:
  "nested_prop_atoms (snd (af\<^sub>\<nu> X p w)) \<subseteq> (nested_prop_atoms\<^sub>\<nu> (fst p) X) \<union> (nested_prop_atoms (snd p))"
proof (induction w arbitrary: p rule: rev_induct)
  case (snoc x xs)

  let ?p = "af\<^sub>\<nu> X p xs"

  have "nested_prop_atoms (snd (af\<^sub>\<nu> X p (xs @ [x]))) \<subseteq> (nested_prop_atoms\<^sub>\<nu> (fst ?p) X) \<union> (nested_prop_atoms (snd ?p))"
    by (simp add: af_letter\<^sub>\<nu>_snd_nested_prop_atoms)

  then show ?case
    using snoc af\<^sub>\<nu>_fst_nested_prop_atoms\<^sub>\<nu> by blast
qed (simp add: nested_prop_atoms\<^sub>\<nu>_def)

lemma af\<^sub>\<nu>_snd_range:
  "range (snd \<circ> af\<^sub>\<nu> X p) \<subseteq> {\<psi>. nested_prop_atoms \<psi> \<subseteq> (nested_prop_atoms\<^sub>\<nu> (fst p) X) \<union> nested_prop_atoms (snd p)}"
  using af\<^sub>\<nu>_snd_nested_prop_atoms by fastforce

lemma af\<^sub>\<nu>_range:
  "range (af\<^sub>\<nu> X p) \<subseteq> {\<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms (fst p)} \<times> {\<psi>. nested_prop_atoms \<psi> \<subseteq> (nested_prop_atoms\<^sub>\<nu> (fst p) X) \<union> nested_prop_atoms (snd p)}"
proof -
  have "range (af\<^sub>\<nu> X p) \<subseteq> range (fst \<circ> af\<^sub>\<nu> X p) \<times> range (snd \<circ> af\<^sub>\<nu> X p)"
    by (simp add: image_subset_iff mem_Times_iff)

  also have "\<dots> \<subseteq> {\<psi>. nested_prop_atoms \<psi> \<subseteq> nested_prop_atoms (fst p)} \<times> {\<psi>. nested_prop_atoms \<psi> \<subseteq> (nested_prop_atoms\<^sub>\<nu> (fst p) X) \<union> nested_prop_atoms (snd p)}"
    using af\<^sub>\<nu>_fst_range af\<^sub>\<nu>_snd_range by blast

  finally show ?thesis .
qed

end

end
