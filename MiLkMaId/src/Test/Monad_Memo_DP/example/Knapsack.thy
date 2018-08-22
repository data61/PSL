subsection \<open>The Knapsack Problem\<close>

theory Knapsack
  imports
    "HOL-Library.Code_Target_Numeral"
    "../state_monad/State_Main" 
    "../heap_monad/Heap_Default"
    Example_Misc
begin

subsubsection \<open>Definitions\<close>

context (* Subset Sum *)
  fixes w :: "nat \<Rightarrow> nat"
begin

context (* Knapsack *)
  fixes v :: "nat \<Rightarrow> nat"
begin

fun knapsack :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "knapsack 0 W = 0" |
  "knapsack (Suc i) W = (if W < w (Suc i)
    then knapsack i W
    else max (knapsack i W) (v (Suc i) + knapsack i (W - w (Suc i))))"

no_notation fun_app_lifted (infixl "." 999)

text \<open>
  The correctness proof closely follows Kleinberg \<open>&\<close> Tardos: "Algorithm Design",
  chapter "Dynamic Programming" @{cite "Kleinberg-Tardos"}
\<close>

definition
  "OPT n W = Max {\<Sum> i \<in> S. v i | S. S \<subseteq> {1..n} \<and> (\<Sum> i \<in> S. w i) \<le> W}"

lemma OPT_0:
  "OPT 0 W = 0"
  unfolding OPT_def by simp

subsubsection \<open>Functional Correctness\<close>

lemma Max_add_left:
  "(x :: nat) + Max S = Max ((op + x) ` S)" (is "?A = ?B") if "finite S" "S \<noteq> {}"
proof -
  have "?A \<le> ?B"
    using that by (force intro: Min.boundedI)
  moreover have "?B \<le> ?A"
    using that by (force intro: Min.boundedI)
  ultimately show ?thesis
    by simp
qed

lemma OPT_Suc:
  "OPT (Suc i) W = (
    if W < w (Suc i)
    then OPT i W
    else max(v (Suc i) + OPT i (W - w (Suc i))) (OPT i W)
  )" (is "?lhs = ?rhs")
proof -
  have OPT_in: "OPT n W \<in> {\<Sum> i \<in> S. v i | S. S \<subseteq> {1..n} \<and> (\<Sum> i \<in> S. w i) \<le> W}" for n W
    unfolding OPT_def by - (rule Max_in; force)
  from OPT_in[of "Suc i" W] obtain S where S:
    "S \<subseteq> {1..Suc i}" "sum w S \<le> W" and [simp]: "OPT (Suc i) W = sum v S"
    by auto

  have "OPT i W \<le> OPT (Suc i) W"
    unfolding OPT_def by (force intro: Max_mono)
  moreover have "v (Suc i) + OPT i (W - w (Suc i)) \<le> OPT (Suc i) W" if "w (Suc i) \<le> W"
  proof -
    have *: "
      v (Suc i) + sum v S = sum v (S \<union> {Suc i}) \<and> (S \<union> {Suc i}) \<subseteq> {1..Suc i}
      \<and> sum w (S \<union> {Suc i}) \<le> W" if "S \<subseteq> {1..i}" "sum w S \<le> W - w (Suc i)" for S
      using that \<open>w (Suc i) \<le> W\<close>
      by (subst sum.insert_if | auto intro: finite_subset[OF _ finite_atLeastAtMost])+
    show ?thesis
      unfolding OPT_def
      by (subst Max_add_left;
          fastforce intro: Max_mono finite_subset[OF _ finite_atLeastAtMost] dest: *
         )
  qed
  ultimately have "?lhs \<ge> ?rhs"
    by auto

  from S have *: "sum v S \<le> OPT i W" if "Suc i \<notin> S"
    using that unfolding OPT_def by (auto simp: atLeastAtMostSuc_conv intro!: Max_ge)

  have "sum v S \<le> OPT i W" if "W < w (Suc i)"
  proof (rule *, rule ccontr, simp)
    assume "Suc i \<in> S"
    then have "sum w S \<ge> w (Suc i)"
      using S(1) by (subst sum.remove) (auto intro: finite_subset[OF _ finite_atLeastAtMost])
    with \<open>W < _\<close> \<open>_ \<le> W\<close> show False
      by simp
  qed
  moreover have
    "OPT (Suc i) W \<le> max(v (Suc i) + OPT i (W - w (Suc i))) (OPT i W)" if "w (Suc i) \<le> W"
  proof (cases "Suc i \<in> S")
    case True
    then have [simp]:
      "sum v S = v (Suc i) + sum v (S - {Suc i})" "sum w S = w (Suc i) + sum w (S - {Suc i})"
      using S(1) by (auto intro: finite_subset[OF _ finite_atLeastAtMost] sum.remove)
    have "OPT i (W - w (Suc i)) \<ge> sum v (S - {Suc i})"
      unfolding OPT_def using S by (fastforce intro!: Max_ge)
    then show ?thesis
      by simp
  next
    case False
    then show ?thesis
      by (auto dest: *)
  qed
  ultimately have "?lhs \<le> ?rhs"
    by auto
  with \<open>?lhs \<ge> ?rhs\<close> show ?thesis
    by simp
qed

theorem knapsack_correct:
  "OPT n W = knapsack n W"
  by (induction n arbitrary: W; auto simp: OPT_0 OPT_Suc)


subsubsection \<open>Functional Memoization\<close>

memoize_fun knapsack\<^sub>m: knapsack with_memory dp_consistency_rbt monadifies (state) knapsack.simps

text \<open>Generated Definitions\<close>
context includes state_monad_syntax begin
thm knapsack\<^sub>m'.simps knapsack\<^sub>m_def
end

text \<open>Correspondence Proof\<close>
memoize_correct
  by memoize_prover
print_theorems
lemmas [code] = knapsack\<^sub>m.memoized_correct


subsubsection \<open>Imperative Memoization\<close>

context fixes
  mem :: "nat option array"
  and n W :: nat
begin

memoize_fun knapsack\<^sub>T: knapsack
  with_memory dp_consistency_heap_default where bound = "Bound (0, 0) (n, W)" and mem="mem"
  monadifies (heap) knapsack.simps

context includes heap_monad_syntax begin
thm knapsack\<^sub>T'.simps knapsack\<^sub>T_def
end

memoize_correct
  by memoize_prover

lemmas memoized_empty = knapsack\<^sub>T.memoized_empty

end (* Fixed array *)

text \<open>Adding Memory Initialization\<close>
context
  includes heap_monad_syntax
  notes [simp del] = knapsack\<^sub>T'.simps
begin

definition
  "knapsack\<^sub>h \<equiv> \<lambda> i j. Heap_Monad.bind (mem_empty (i * j)) (\<lambda> mem. knapsack\<^sub>T' mem i j i j)"

lemmas memoized_empty' = memoized_empty[
      of mem n W "\<lambda> m. \<lambda>(i,j). knapsack\<^sub>T' m n W i j",
      OF knapsack\<^sub>T.crel[of mem n W], of "(n, W)" for mem n W
    ]

lemma knapsack_heap:
  "knapsack n W = result_of (knapsack\<^sub>h n W) Heap.empty"
  unfolding knapsack\<^sub>h_def using memoized_empty'[of _ n W] by (simp add: index_size_defs)

end

end (* Knapsack *)

fun su :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "su 0 W = 0" |
  "su (Suc i) W = (if W < w (Suc i)
    then su i W
    else max (su i W) (w (Suc i) + su i (W - w (Suc i))))"

lemma su_knapsack:
  "su n W = knapsack w n W"
  by (induction n arbitrary: W; simp)

lemma su_correct:
  "Max {\<Sum> i \<in> S. w i | S. S \<subseteq> {1..n} \<and> (\<Sum> i \<in> S. w i) \<le> W} = su n W"
  unfolding su_knapsack knapsack_correct[symmetric] OPT_def ..

subsubsection \<open>Memoization\<close>

memoize_fun su\<^sub>m: su with_memory dp_consistency_rbt monadifies (state) su.simps

text \<open>Generated Definitions\<close>
context includes state_monad_syntax begin
thm su\<^sub>m'.simps su\<^sub>m_def
end

text \<open>Correspondence Proof\<close>
memoize_correct
  by memoize_prover
print_theorems
lemmas [code] = su\<^sub>m.memoized_correct

end (* Subset Sum *)


subsubsection \<open>Regression Test\<close>

definition
  "knapsack_test = (knapsack\<^sub>h (\<lambda> i. [2,3,4] ! (i - 1)) (\<lambda> i. [2,3,4] ! (i - 1)) 3 8)"

code_reflect Test functions knapsack_test

ML \<open>Test.knapsack_test ()\<close>

end (* Theory *)