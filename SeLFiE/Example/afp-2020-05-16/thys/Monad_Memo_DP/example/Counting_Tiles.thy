theory Counting_Tiles
  imports
    "HOL-Library.Code_Target_Numeral"
    "HOL-Library.Product_Lexorder"
    "HOL-Library.RBT_Mapping"
    "../state_monad/State_Main" 
    Example_Misc
begin

subsection \<open>A Counting Problem\<close>

text \<open>
  This formalization contains verified solutions for Project Euler problems
    \<^item> \<open>#\<close>114 (\<^url>\<open>https://projecteuler.net/problem=114\<close>) and
    \<^item> \<open>#\<close>115 (\<^url>\<open>https://projecteuler.net/problem=115\<close>).

  This is the problem description for \<open>#\<close>115:
  \begin{quote}
  A row measuring n units in length has red blocks with a minimum length of m units placed on it,
  such that any two red blocks (which are allowed to be different lengths) are separated
  by at least one black square.
  Let the fill-count function, F(m, n), represent the number of ways that a row can be filled.

  For example, F(3, 29) = 673135 and F(3, 30) = 1089155.

  That is, for m = 3, it can be seen that n = 30 is the smallest value for which the fill-count
  function first exceeds one million.
  In the same way, for m = 10, it can be verified that F(10, 56) = 880711 and F(10, 57) = 1148904,
  so n = 57 is the least value for which the fill-count function first exceeds one million.

  For m = 50, find the least value of n for which the fill-count function first exceeds one million.
  \end{quote}
\<close>

subsubsection \<open>Misc\<close>

(* Duplicate from Refine_Misc with slightly nicer proof *)
lemma lists_of_len_fin1:
  "finite (lists A \<inter> {l. length l = n})" if "finite A"
  using that
proof (induction n)
  case 0 thus ?case
    by auto
next
  case (Suc n)
  have "lists A \<inter> { l. length l = Suc n } = (\<lambda>(a,l). a#l) ` (A \<times> (lists A \<inter> {l. length l = n}))"
    by (auto simp: length_Suc_conv)
  moreover from Suc have "finite \<dots>"
    by auto
  ultimately show ?case
    by simp
qed

(* Duplicate from Refine_Misc *)
lemma disjE1:
  "A \<or> B \<Longrightarrow> (A \<Longrightarrow> P) \<Longrightarrow> (\<not> A \<Longrightarrow> B \<Longrightarrow> P) \<Longrightarrow> P"
  by metis


subsubsection \<open>Problem Specification\<close>

text \<open>Colors\<close>

datatype color = R | B

text \<open>Direct natural definition of a valid line\<close>

context
  fixes m :: nat
begin

inductive valid where
  "valid []" |
  "valid xs \<Longrightarrow> valid (B # xs)" |
  "valid xs \<Longrightarrow> n \<ge> m \<Longrightarrow> valid (replicate n R @ xs)"

text \<open>Definition of the fill-count function\<close>

definition "F n = card {l. length l = n \<and> valid l}"


subsubsection \<open>Combinatorial Identities\<close>

text \<open>This alternative variant helps us to prove the split lemma below.\<close>
inductive valid' where
  "valid' []" |
  "n \<ge> m \<Longrightarrow> valid' (replicate n R)" |
  "valid' xs \<Longrightarrow> valid' (B # xs)" |
  "valid' xs \<Longrightarrow> n \<ge> m \<Longrightarrow> valid' (replicate n R @ B # xs)"

lemma valid_valid':
  "valid l \<Longrightarrow> valid' l"
  by (induction rule: valid.induct)
     (auto 4 4 intro: valid'.intros elim: valid'.cases
       simp: replicate_add[symmetric] append_assoc[symmetric]
     )

lemmas valid_red = valid.intros(3)[OF valid.intros(1), simplified]

lemma valid'_valid:
  "valid' l \<Longrightarrow> valid l"
  by (induction rule: valid'.induct) (auto intro: valid.intros valid_red)

lemma valid_eq_valid':
  "valid' l = valid l"
  using valid_valid' valid'_valid by metis


text \<open>Additional Facts on Replicate\<close>

lemma replicate_iff:
  "(\<forall>i<length l. l ! i = R) \<longleftrightarrow> (\<exists> n. l = replicate n R)"
  by auto (metis (full_types) in_set_conv_nth replicate_eqI)

lemma replicate_iff2:
  "(\<forall>i<n. l ! i = R) \<longleftrightarrow> (\<exists> l'. l = replicate n R @ l')" if "n < length l"
  using that by (auto simp: list_eq_iff_nth_eq nth_append intro: exI[where x = "drop n l"])

lemma replicate_Cons_eq:
  "replicate n x = y # ys \<longleftrightarrow> (\<exists> n'. n = Suc n' \<and> x = y \<and> replicate n' x = ys)"
  by (cases n) auto


text \<open>Main Case Analysis on \<open>@term valid\<close>\<close>

lemma valid_split:
  "valid l \<longleftrightarrow>
    l = [] \<or>
    (l!0 = B \<and> valid (tl l)) \<or>
    length l \<ge> m \<and> (\<forall> i < length l. l ! i = R) \<or>
    (\<exists> j < length l. j \<ge> m \<and> (\<forall> i < j. l ! i = R) \<and> l ! j = B \<and> valid (drop (j + 1) l))"
  unfolding valid_eq_valid'[symmetric]
  apply standard
  subgoal
    by (erule valid'.cases) (auto simp: nth_append nth_Cons split: nat.splits)
  subgoal
    apply (auto intro: valid'.intros simp: replicate_iff elim!: disjE1)
      apply (fastforce intro: valid'.intros simp: neq_Nil_conv)
     apply (subst (asm) replicate_iff2; fastforce intro: valid'.intros simp: neq_Nil_conv nth_append)+
    done
  done


text \<open>Base cases\<close>

lemma valid_line_just_B:
  "valid (replicate n B)"
  by (induction n) (auto intro: valid.intros)

lemma F_base_0_aux:
  "{l. l = [] \<and> valid l} = {[]}"
  by (auto intro: valid.intros)

lemma F_base_0: "F 0 = 1"
  by (auto simp: F_base_0_aux F_def)

lemma F_base_aux: "{l. length l=n \<and> valid l} = {replicate n B}" if "n > 0" "n < m"
  using that
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  show ?case
  proof (cases "n = 0")
    case True
    with Suc.prems show ?thesis
      by (auto intro: valid.intros elim: valid.cases)
  next
    case False
    with Suc.prems show ?thesis
      apply safe
      using Suc.IH
        apply -
        apply (erule valid.cases)
          apply (auto intro: valid.intros elim: valid.cases)
      done
  qed
qed

lemma F_base_1:
  "F n = 1" if "n > 0" "n < m"
  using that unfolding F_def by (simp add: F_base_aux)

lemma valid_m_Rs [simp]:
  "valid (replicate m R)"
  using valid_red[of m, simplified] by simp

lemma F_base_aux_2: "{l. length l=m \<and> valid l} = {replicate m R, replicate m B}"
  apply (auto simp: valid_line_just_B)
  apply (erule Counting_Tiles.valid.cases)
    apply auto
  subgoal for xs
    using F_base_aux[of "length xs"] by (cases "xs = []") auto
  done

lemma F_base_2:
  "F m = 2" if "0 < m"
  using that unfolding F_def by (simp add: F_base_aux_2)


text \<open>The recursion case\<close>

lemma finite_valid_length:
  "finite {l. length l = n \<and> valid l}" (is "finite ?S")
proof -
  have "?S \<subseteq> lists {R, B} \<inter> {l. length l = n}"
    by (auto intro: color.exhaust)
  moreover have "finite \<dots>"
    by (auto intro: lists_of_len_fin1)
  ultimately show ?thesis
    by (rule finite_subset)
qed

lemma valid_line_aux:
  "{l. length l = n \<and> valid l} \<noteq> {}" (is "?S \<noteq> {}")
  using valid_line_just_B[of n] by force

lemma replicate_unequal_aux:
  "replicate x R @ B # l \<noteq> replicate y R @ B # l'" (is "?l \<noteq> ?r") if \<open>x < y\<close> for l l'
proof -
  have "?l ! x = B" "?r ! x = R"
    using that by (auto simp: nth_append)
  then show ?thesis
    by auto
qed

lemma valid_prepend_B_iff:
  "valid (B # xs) \<longleftrightarrow> valid xs" if "m > 0"
  using that
  by (auto 4 3 intro: valid.intros elim: valid.cases simp: Cons_replicate_eq Cons_eq_append_conv)

lemma F_rec: "F n = F (n-1) + 1 + (\<Sum>i=m..<n. F (n-i-1))" if \<open>n>m\<close> "m > 0"
proof -
  have "{l. length l = n \<and> valid l}
          = {l. length l = n \<and> valid (tl l) \<and> l!0=B}
          \<union> {l. length l = n \<and>
              (\<exists> i. i < n \<and> i \<ge> m \<and> (\<forall> k < i. l!k = R) \<and> l!i = B \<and> valid (drop (i + 1) l))}
          \<union> {l. length l = n \<and> (\<forall>i<n. l!i=R)}
          " (is "?A = ?B \<union> ?D \<union> ?C")
    using \<open>n > m\<close> by (subst valid_split) auto

  let ?B1 = "((#) B) ` {l. length l = n - Suc 0 \<and> valid l}"
  from \<open>n > m\<close> have "?B = ?B1"
    apply safe
    subgoal for l
      by (cases l) (auto simp: valid_prepend_B_iff)
    by auto
  have 1: "card ?B1 = F (n-1)"
    unfolding F_def by (auto intro: card_image)

  have "?C = {replicate n R}"
    by (auto simp: nth_equalityI)
  have 2: "card {replicate n R} = 1"
    by auto

  let ?D1="(\<Union> i \<in> {m..<n}. (\<lambda> l. replicate i R @ B # l)` {l. length l = n - i - 1 \<and> valid l})"
  have "?D =
        (\<Union>i \<in> {m..<n}. {l. length l = n \<and> (\<forall> k < i. l!k = R) \<and> l!i = B \<and> valid (drop (i + 1) l)})"
    by auto
  have "{l. length l = n \<and> (\<forall> k < i. l!k = R) \<and> l!i = B \<and> valid (drop (i + 1) l)}
              = (\<lambda> l. replicate i R @ B # l)` {l. length l = n - i - 1 \<and> valid l}"
    if "i < n" for i
    apply safe
    subgoal for l
      apply (rule image_eqI[where x = "drop (i + 1) l"])
       apply (rule nth_equalityI)
      using that
        apply (simp_all split: nat.split add: nth_Cons nth_append)
      using add_diff_inverse_nat apply fastforce
      done
    using that by (simp add: nth_append; fail)+

  then have D_eq: "?D = ?D1"
    unfolding \<open>?D = _\<close> by auto

  have inj: "inj_on (\<lambda>l. replicate x R @ B # l) {l. length l = n - Suc x \<and> valid l}" for x
    unfolding inj_on_def by auto

  have *:
    "(\<lambda>l. replicate x R @ B # l) ` {l. length l = n - Suc x \<and> valid l} \<inter>
         (\<lambda>l. replicate y R @ B # l) ` {l. length l = n - Suc y \<and> valid l} = {}"
    if "m \<le> x" "x < y" "y < n" for x y
    using that replicate_unequal_aux[OF \<open>x < y\<close>] by auto

  have 3: "card ?D1 = (\<Sum>i=m..<n. F (n-i-1))"
  proof (subst card_Union_disjoint, goal_cases)
    case 1
    show ?case
      unfolding pairwise_def disjnt_def
    proof (clarsimp, goal_cases)
      case prems: (1 x y)
      from prems show ?case
        apply -
        apply (rule linorder_cases[of x y])
          apply (rule *; assumption)
         apply (simp; fail)
        apply (subst Int_commute; rule *; assumption)
        done
    qed
  next
    case 3
    show ?case
    proof (subst sum.reindex, unfold inj_on_def, clarsimp, goal_cases)
      case prems: (1 x y)
      with *[of y x] *[of x y] valid_line_aux[of "n - Suc x"] show ?case
        by - (rule linorder_cases[of x y], auto)
    next
      case 2
      then show ?case
        by (simp add: F_def card_image[OF inj])
    qed
  qed (auto intro: finite_subset[OF _ finite_valid_length])

  show ?thesis
    apply (subst F_def)
    unfolding \<open>?A = _\<close> \<open>?B = _\<close> \<open>?C = _\<close> D_eq
    apply (subst card_Un_disjoint)
      (* Finiteness *)
       apply (blast intro: finite_subset[OF _ finite_valid_length])+
      (* Disjointness *)
    subgoal
      using Cons_replicate_eq[of B _ n R] replicate_unequal_aux by fastforce
    apply (subst card_Un_disjoint)
      (* Finiteness *)
       apply (blast intro: finite_subset[OF _ finite_valid_length])+
      (* Disjointness & final rewriting *)
    unfolding 1 2 3 using \<open>m > 0\<close> by (auto simp: Cons_replicate_eq Cons_eq_append_conv)
qed


subsubsection \<open>Computing the Fill-Count Function\<close>

fun lcount :: "nat \<Rightarrow> nat" where
  "lcount n = (
    if n < m then 1
    else if n = m then 2
    else lcount (n - 1) + 1 + (\<Sum>i \<leftarrow> [m..<n]. lcount (n - i - 1))
  )"

lemmas [simp del] = lcount.simps

lemma lcount_correct:
  "lcount n = F n" if "m > 0"
proof (induction n rule: less_induct)
  case (less n)
  from \<open>m > 0\<close> show ?case
    apply (cases "n = 0")
    subgoal
      by (simp add: lcount.simps F_base_0)
    by (subst lcount.simps)
      (simp add: less.IH F_base_1 F_base_2 F_rec interv_sum_list_conv_sum_set_nat)
qed


subsubsection \<open>Memoization\<close>

memoize_fun lcount\<^sub>m: lcount with_memory dp_consistency_mapping monadifies (state) lcount.simps

memoize_correct
  by memoize_prover

lemmas [code] = lcount\<^sub>m.memoized_correct

end (* Fixed block size *)


subsubsection \<open>Problem solutions\<close>

text \<open>Example and solution for problem \<open>#\<close>114\<close>
value "lcount 3 7"
value "lcount 3 50"

text \<open>Examples for problem \<open>#\<close>115\<close>
value "lcount 3 29"
value "lcount 3 30"
value "lcount 10 56"
value "lcount 10 57"

text \<open>Binary search for the solution of problem \<open>#\<close>115\<close>
value "lcount 50 100"
value "lcount 50 150"
value "lcount 50 163"
value "lcount 50 166"
value "lcount 50 167"
value "lcount 50 168" \<comment> \<open>The solution\<close>
value "lcount 50 169"
value "lcount 50 175"
value "lcount 50 200"
value "lcount 50 300"
value "lcount 50 500"
value "lcount 50 1000"

text \<open>We prove that 168 is the solution for problem \<open>#\<close>115\<close>
theorem
  "(LEAST n. F 50 n > 1000000) = 168"
proof -
  have "lcount 50 168 > 1000000"
    by eval
  moreover have "\<forall> n \<in> {0..<168}. lcount 50 n < 1000000"
    by eval
  ultimately show ?thesis
    by - (rule Least_equality; rule ccontr; force simp: not_le lcount_correct)
qed

end
