(*<*)
theory Misc
imports Complex_Main
begin

chapter \<open>Basic lemmas which do not belong to the particular domain of Timed Automata\<close>

section \<open>Reals\<close>

subsection \<open>Properties of fractions\<close>

lemma frac_add_le_preservation:
  fixes a d :: real and b :: nat
  assumes "a < b" "d < 1 - frac a"
  shows "a + d < b"
proof -
  from assms have "a + d < a + 1 - frac a" by auto
  also have "\<dots> = (a - frac a) + 1" by auto
  also have "\<dots> = floor a + 1" unfolding frac_def by auto
  also have "\<dots> \<le> b" using \<open>a < b\<close>
  by (metis floor_less_iff int_less_real_le of_int_1 of_int_add of_int_of_nat_eq) 
  finally show "a + d < b" .
qed

lemma lt_lt_1_ccontr:
  "(a :: int) < b \<Longrightarrow> b < a + 1 \<Longrightarrow> False" by auto

lemma int_intv_frac_gt0:
  "(a :: int) < b \<Longrightarrow> b < a + 1 \<Longrightarrow> frac b > 0" by auto

lemma floor_frac_add_preservation:
  fixes a d :: real
  assumes "0 < d" "d < 1 - frac a"
  shows "floor a = floor (a + d)"
proof -
  have "frac a \<ge> 0" by auto
  with assms(2) have "d < 1" by linarith
  from assms have "a + d < a + 1 - frac a" by auto
  also have "\<dots> = (a - frac a) + 1" by auto
  also have "\<dots> = (floor a) + 1" unfolding frac_def by auto
  finally have *: "a + d < floor a + 1" .
  have "floor (a + d) \<ge> floor a" using \<open>d > 0\<close> by linarith
  moreover from * have "floor (a + d) < floor a + 1" by linarith
  ultimately show "floor a = floor (a + d)" by auto
qed

lemma frac_distr:
  fixes a d :: real
  assumes "0 < d" "d < 1 - frac a"
  shows "frac (a + d) > 0" "frac a + d = frac (a + d)"
proof -
  have "frac a \<ge> 0" by auto
  with assms(2) have "d < 1" by linarith
  from assms have "a + d < a + 1 - frac a" by auto
  also have "\<dots> = (a - frac a) + 1" by auto
  also have "\<dots> = (floor a) + 1" unfolding frac_def by auto
  finally have *: "a + d < floor a + 1" .
  have **: "floor a < a + d" using assms(1) by linarith
  have "frac (a + d) \<noteq> 0"
  proof (rule ccontr, auto, goal_cases)
    case 1
    then obtain b :: int where "b = a + d" by (metis Ints_cases)
    with * ** have "b < floor a + 1" "floor a < b" by auto
    with lt_lt_1_ccontr show ?case by blast
  qed
  then show "frac (a + d) > 0" by auto
  from floor_frac_add_preservation assms have "floor a = floor (a + d)" by auto
  then show "frac a + d = frac (a + d)" unfolding frac_def by force
qed

lemma frac_add_leD:
  fixes a d :: real
  assumes "0 < d" "d < 1 - frac a" "d < 1 - frac b" "frac (a + d) \<le> frac (b + d)"
  shows "frac a \<le> frac b"
proof -
  from floor_frac_add_preservation assms have
    "floor a = floor (a + d)" "floor b = floor (b + d)"
  by auto
  with assms(4) show "frac a \<le> frac b" unfolding frac_def by auto
qed

lemma floor_frac_add_preservation':
  fixes a d :: real
  assumes "0 \<le> d" "d < 1 - frac a"
  shows "floor a = floor (a + d)"
using assms floor_frac_add_preservation by (cases "d = 0") auto

lemma frac_add_leIFF:
  fixes a d :: real
  assumes "0 \<le> d" "d < 1 - frac a" "d < 1 - frac b"
  shows "frac a \<le> frac b \<longleftrightarrow> frac (a + d) \<le> frac (b + d)"
proof -
  from floor_frac_add_preservation' assms have
    "floor a = floor (a + d)" "floor b = floor (b + d)"
  by auto
  then show ?thesis unfolding frac_def by auto
qed

lemma nat_intv_frac_gt0:
  fixes c :: nat fixes x :: real
  assumes "c < x" "x < real (c + 1)"
  shows "frac x > 0"
proof (rule ccontr, auto, goal_cases)
  case 1
  then obtain d :: int where d: "x = d" by (metis Ints_cases)
  with assms have "c < d" "d < int c + 1" by auto
  with int_intv_frac_gt0[OF this] 1 d show False by auto
qed

lemma nat_intv_frac_decomp:
  fixes c :: nat and d :: real
  assumes "c < d" "d < c + 1"
  shows "d = c + frac d"
proof -
  from assms have "int c = \<lfloor>d\<rfloor>" by linarith
  thus ?thesis by (simp add: frac_def)
qed

lemma nat_intv_not_int:
  fixes c :: nat
  assumes "real c < d" "d < c + 1"
  shows "d \<notin> \<int>"
proof (standard, goal_cases)
  case 1
  then obtain k :: int where "d = k" using Ints_cases by auto
  then have "frac d = 0" by auto
  moreover from nat_intv_frac_decomp[OF assms] have *: "d = c + frac d" by auto
  ultimately have "d = c" by linarith
  with assms show ?case by auto
qed

lemma frac_idempotent: "frac (frac x) = frac x" by (simp add: frac_eq frac_lt_1)

lemma frac_nat_add_id: "frac ((n :: nat) + (r :: real)) = frac r" \<comment> \<open>Found by sledgehammer\<close>
proof -
  have "\<And>r. frac (r::real) < 1"
    by (meson frac_lt_1)
  then show ?thesis
    by (simp add: floor_add frac_def)
qed

lemma floor_nat_add_id: "0 \<le> (r :: real) \<Longrightarrow> r < 1 \<Longrightarrow> floor (real (n::nat) + r) = n" by linarith

lemma int_intv_frac_gt_0':
  "(a :: real) \<in> \<int> \<Longrightarrow> (b :: real) \<in> \<int> \<Longrightarrow> a \<le> b \<Longrightarrow> a \<noteq> b \<Longrightarrow> a \<le> b - 1"
proof (goal_cases)
  case 1
  then have "a < b" by auto
  from 1(1,2) obtain k l :: int where "a = real_of_int k" "b = real_of_int l" by (metis Ints_cases)
  with \<open>a < b\<close> show ?case by auto
qed

lemma int_lt_Suc_le:
  "(a :: real) \<in> \<int> \<Longrightarrow> (b :: real) \<in> \<int> \<Longrightarrow> a < b + 1 \<Longrightarrow> a \<le> b"
proof (goal_cases)
  case 1
  from 1(1,2) obtain k l :: int where "a = real_of_int k" "b = real_of_int l" by (metis Ints_cases)
  with \<open>a < b + 1\<close> show ?case by auto
qed

lemma int_lt_neq_Suc_lt:
  "(a :: real) \<in> \<int> \<Longrightarrow> (b :: real) \<in> \<int> \<Longrightarrow> a < b \<Longrightarrow> a + 1 \<noteq> b \<Longrightarrow> a + 1 < b"
proof (goal_cases)
  case 1
  from 1(1,2) obtain k l :: int where "a = real_of_int k" "b = real_of_int l" by (metis Ints_cases)
  with 1 show ?case by auto
qed

lemma int_lt_neq_prev_lt:
  "(a :: real) \<in> \<int> \<Longrightarrow> (b :: real) \<in> \<int> \<Longrightarrow> a - 1 < b \<Longrightarrow> a \<noteq> b \<Longrightarrow> a < b"
proof (goal_cases)
  case 1
  from 1(1,2) obtain k l :: int where "a = real_of_int k" "b = real_of_int l" by (metis Ints_cases)
  with 1 show ?case by auto
qed

lemma ints_le_add_frac1:
  fixes a b x :: real
  assumes "0 < x" "x < 1" "a \<in> \<int>" "b \<in> \<int>" "a + x \<le> b"
  shows "a \<le> b"
using assms by auto

lemma ints_le_add_frac2:
  fixes a b x :: real
  assumes "0 \<le> x" "x < 1" "a \<in> \<int>" "b \<in> \<int>" "b \<le> a + x"
  shows "b \<le> a"
using assms
by (metis add.commute add_le_cancel_left add_mono_thms_linordered_semiring(1) int_lt_Suc_le leD le_less_linear)

section \<open>Ordering Fractions\<close>

lemma distinct_twice_contradiction:
  "xs ! i = x \<Longrightarrow> xs ! j = x \<Longrightarrow> i < j \<Longrightarrow> j < length xs \<Longrightarrow> \<not> distinct xs"
proof (rule ccontr, simp, induction xs arbitrary: i j)
  case Nil thus ?case by auto
next
  case (Cons y xs)
  show ?case
  proof (cases "i = 0")
    case True
    with Cons have "y = x" by auto
    moreover from True Cons have "x \<in> set xs" by auto
    ultimately show False using Cons(6) by auto
  next
    case False
    with Cons have
      "xs ! (i - 1) = x" "xs ! (j - 1) = x" "i - 1 < j - 1" "j - 1 < length xs" "distinct xs"
    by auto
    from Cons.IH[OF this] show False .
  qed
qed

lemma distinct_nth_unique:
  "xs ! i = xs ! j \<Longrightarrow> i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> distinct xs \<Longrightarrow> i = j"
  apply (rule ccontr)
  apply (cases "i < j")
  apply auto
  apply (auto dest: distinct_twice_contradiction)
using distinct_twice_contradiction by fastforce

lemma (in linorder) linorder_order_fun:
  fixes S :: "'a set"
  assumes "finite S"
  obtains f :: "'a \<Rightarrow> nat"
  where "(\<forall> x \<in> S. \<forall> y \<in> S. f x \<le> f y \<longleftrightarrow> x \<le> y)" and "range f \<subseteq> {0..card S - 1}"
proof -
  obtain l where l_def: "l = sorted_list_of_set S" by auto
  with assms have l: "set l = S" "sorted l" "distinct l" by auto
  from l(1,3) \<open>finite S\<close> have len: "length l = card S" using distinct_card by force 
  let ?f = "\<lambda> x. if x \<notin> S then 0 else THE i. i < length l \<and> l ! i = x"
  { fix x y assume A: "x \<in> S" "y \<in> S" "x < y"
    with l(1) obtain i j where *: "l ! i = x" "l ! j = y" "i < length l" "j < length l"
    by (meson in_set_conv_nth)
    have "i < j"
    proof (rule ccontr, goal_cases)
      case 1
      with sorted_nth_mono[OF l(2)] \<open>i < length l\<close> have "l ! j \<le> l ! i" by auto
      with * A(3) show False by auto
    qed
    moreover have "?f x = i" using * l(3) A(1) by (auto) (rule, auto intro: distinct_nth_unique)
    moreover have "?f y = j" using * l(3) A(2) by (auto) (rule, auto intro: distinct_nth_unique)
    ultimately have "?f x < ?f y" by auto
  } moreover
  { fix x y assume A: "x \<in> S" "y \<in> S" "?f x < ?f y"
    with l(1) obtain i j where *: "l ! i = x" "l ! j = y" "i < length l" "j < length l"
    by (meson in_set_conv_nth)
    moreover have "?f x = i" using * l(3) A(1) by (auto) (rule, auto intro: distinct_nth_unique)
    moreover have "?f y = j" using * l(3) A(2) by (auto) (rule, auto intro: distinct_nth_unique)
    ultimately have **: "l ! ?f x = x" "l ! ?f y = y" "i < j" using A(3) by auto
    have "x < y"
    proof (rule ccontr, goal_cases)
      case 1
      then have "y \<le> x" by simp
      moreover from sorted_nth_mono[OF l(2), of i j] **(3) * have "x \<le> y" by auto
      ultimately show False using distinct_nth_unique[OF _ *(3,4) l(3)] *(1,2) **(3) by fastforce
    qed
  }
  ultimately have "\<forall> x \<in> S. \<forall> y \<in> S. ?f x \<le> ?f y \<longleftrightarrow> x \<le> y" by force
  moreover have "range ?f \<subseteq> {0..card S - 1}"
  proof (auto, goal_cases)
    case (1 x)
    with l(1) obtain i where *: "l ! i = x" "i < length l" by (meson in_set_conv_nth)
    then have "?f x = i" using l(3) 1 by (auto) (rule, auto intro: distinct_nth_unique)
    with len show ?case using *(2) 1 by auto
  qed
  ultimately show ?thesis ..
qed

locale enumerateable =
  fixes T :: "'a set"
  fixes less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<prec>" 50)
  assumes finite: "finite T"
  assumes total:  "\<forall> x \<in> T. \<forall> y \<in> T. x \<noteq> y \<longrightarrow> (x \<prec> y) \<or> (y \<prec> x)"
  assumes trans:  "\<forall>x \<in> T. \<forall> y \<in> T. \<forall> z \<in> T. (x :: 'a) \<prec> y \<longrightarrow> y \<prec> z \<longrightarrow> x \<prec> z"
  assumes asymmetric: "\<forall> x \<in> T. \<forall> y \<in> T. x \<prec> y \<longrightarrow> \<not> (y \<prec> x)"
begin

lemma non_empty_set_has_least':
  "S \<subseteq> T \<Longrightarrow> S \<noteq> {} \<Longrightarrow> \<exists> x \<in> S. \<forall> y \<in> S. x \<noteq> y \<longrightarrow> \<not> y \<prec> x"
proof (rule ccontr, induction "card S" arbitrary: S)
  case 0 then show ?case using finite by (auto simp: finite_subset)
next
  case (Suc n)
  then obtain x where x: "x \<in> S" by blast
  from finite Suc.prems(1) have finite: "finite S" by (auto simp: finite_subset)
  let ?S = "S - {x}"
  show ?case
  proof (cases "S = {x}")
    case True
    with Suc.prems(3) show False by auto
  next
    case False
    then have S: "?S \<noteq> {}" using x by blast
    show False
    proof (cases "\<exists>x \<in> ?S. \<forall>y\<in>?S. x \<noteq> y \<longrightarrow> \<not> y \<prec> x")
      case False
      have "n = card ?S" using Suc.hyps finite by (simp add: x)
      from Suc.hyps(1)[OF this _ S False] Suc.prems(1) show False by auto
    next
      case True
      then obtain x' where x': "\<forall>y\<in>?S. x' \<noteq> y \<longrightarrow> \<not> y \<prec> x'" "x' \<in> ?S" "x \<noteq> x'" by auto
      from total Suc.prems(1) x'(2) have "\<And> y. y \<in> S \<Longrightarrow> x' \<noteq> y \<Longrightarrow> \<not> y \<prec> x' \<Longrightarrow> x' \<prec> y" by auto
      from total Suc.prems(1) x'(1,2) have *: "\<forall> y \<in> ?S. x' \<noteq> y \<longrightarrow> x' \<prec> y" by auto
      from Suc.prems(3) x'(1,2) have **: "x \<prec> x'" by auto
      have "\<forall> y \<in> ?S. x \<prec> y"
      proof
        fix y assume y: "y \<in> S - {x}"
        show "x \<prec> y"
        proof (cases "y = x'")
          case True then show ?thesis using ** by simp
        next
          case False
          with * y have "x' \<prec> y" by auto
          with trans Suc.prems(1) ** y x'(2) x ** show ?thesis by auto
        qed
      qed
      with x Suc.prems(1,3) show False using asymmetric by blast
    qed
  qed
qed

lemma non_empty_set_has_least'':
  "S \<subseteq> T \<Longrightarrow> S \<noteq> {} \<Longrightarrow> \<exists>! x \<in> S. \<forall> y \<in> S. x \<noteq> y \<longrightarrow> \<not> y \<prec> x"
proof (intro ex_ex1I, goal_cases)
  case 1
  with non_empty_set_has_least'[OF this] show ?case by auto
next
  case (2 x y)
  show ?case
  proof (rule ccontr)
    assume "x \<noteq> y"
    with 2 total have "x \<prec> y \<or> y \<prec> x" by blast
    with 2(2-) \<open>x \<noteq> y\<close> show False by auto
  qed
qed

abbreviation "least S \<equiv> THE t :: 'a. t \<in> S \<and> (\<forall> y \<in> S. t \<noteq> y \<longrightarrow> \<not> y \<prec> t)"

lemma non_empty_set_has_least:
  "S \<subseteq> T \<Longrightarrow> S \<noteq> {} \<Longrightarrow> least S \<in> S \<and> (\<forall> y \<in> S. least S \<noteq> y \<longrightarrow> \<not> y \<prec> least S)"
proof goal_cases
  case 1
  note A = this
  show ?thesis
  proof (rule theI', goal_cases)
    case 1
    from non_empty_set_has_least''[OF A] show ?case .
  qed
qed

fun f :: "'a set \<Rightarrow> nat \<Rightarrow> 'a list"
where
  "f S 0 = []" |
  "f S (Suc n) = least S # f (S - {least S}) n"

inductive sorted :: "'a list \<Rightarrow> bool" where
  Nil [iff]: "sorted []"
| Cons: "\<forall>y\<in>set xs. x \<prec> y \<Longrightarrow> sorted xs \<Longrightarrow> sorted (x # xs)"

lemma f_set:
  "S \<subseteq> T \<Longrightarrow> n = card S \<Longrightarrow> set (f S n) = S"
proof (induction n arbitrary: S)
  case 0 then show ?case using finite by (auto simp: finite_subset)
next
  case (Suc n)
  then have fin: "finite S" using finite by (auto simp: finite_subset)
  with Suc.prems have "S \<noteq> {}" by auto
  from non_empty_set_has_least[OF Suc.prems(1) this] have least: "least S \<in> S" by blast
  let ?S = "S - {least S}"
  from fin least Suc.prems have "?S \<subseteq> T" "n = card ?S" by auto
  from Suc.IH[OF this] have "set (f ?S n) = ?S" .
  with least show ?case by auto
qed

lemma f_distinct:
  "S \<subseteq> T \<Longrightarrow> n = card S \<Longrightarrow> distinct (f S n)"
proof (induction n arbitrary: S)
  case 0 then show ?case using finite by (auto simp: finite_subset)
next
  case (Suc n)
  then have fin: "finite S" using finite by (auto simp: finite_subset)
  with Suc.prems have "S \<noteq> {}" by auto
  from non_empty_set_has_least[OF Suc.prems(1) this] have least: "least S \<in> S" by blast
  let ?S = "S - {least S}"
  from fin least Suc.prems have "?S \<subseteq> T" "n = card ?S" by auto
  from Suc.IH[OF this] f_set[OF this] have "distinct (f ?S n)" "set (f ?S n) = ?S" .
  then show ?case by simp
qed

lemma f_sorted:
  "S \<subseteq> T \<Longrightarrow> n = card S \<Longrightarrow> sorted (f S n)"
proof (induction n arbitrary: S)
  case 0 then show ?case by auto
next
  case (Suc n)
  then have fin: "finite S" using finite by (auto simp: finite_subset)
  with Suc.prems have "S \<noteq> {}" by auto
  from non_empty_set_has_least[OF Suc.prems(1) this] have least:
    "least S \<in> S" "(\<forall> y \<in> S. least S \<noteq> y \<longrightarrow> \<not> y \<prec> least S)"
  by blast+
  let ?S = "S - {least S}"
  { fix x assume x: "x \<in> ?S"
    with least have "\<not> x \<prec> least S" by auto
    with total x Suc.prems(1) least(1) have "least S \<prec> x" by blast
  } note le = this
  from fin least Suc.prems have "?S \<subseteq> T" "n = card ?S" by auto
  from f_set[OF this] Suc.IH[OF this] have *: "set (f ?S n) = ?S" "sorted (f ?S n)" .
  with le have "\<forall> x \<in> set (f ?S n). least S \<prec> x" by auto
  with *(2) show ?case by (auto intro: Cons)
qed

lemma sorted_nth_mono:
  "sorted xs \<Longrightarrow> i < j \<Longrightarrow> j < length xs \<Longrightarrow> xs!i \<prec> xs!j"
proof (induction xs arbitrary: i j)
  case Nil thus ?case by auto
next
  case (Cons x xs)
  show ?case
  proof (cases "i = 0")
    case True
    with Cons.prems show ?thesis by (auto elim: sorted.cases)
  next
    case False
    from Cons.prems have "sorted xs" by (auto elim: sorted.cases)
    from Cons.IH[OF this] Cons.prems False show ?thesis by auto
  qed
qed

lemma order_fun:
  fixes S :: "'a set"
  assumes "S \<subseteq> T"
  obtains f :: "'a \<Rightarrow> nat" where "\<forall> x \<in> S. \<forall> y \<in> S. f x < f y \<longleftrightarrow> x \<prec> y" and "range f \<subseteq> {0..card S - 1}"
proof -
  obtain l where l_def: "l = f S (card S)" by auto
  with f_set f_distinct f_sorted assms have l: "set l = S" "sorted l" "distinct l" by auto
  then have len: "length l = card S" using distinct_card by force
  let ?f = "\<lambda> x. if x \<notin> S then 0 else THE i. i < length l \<and> l ! i = x"
  { fix x y :: 'a assume A: "x \<in> S" "y \<in> S" "x \<prec> y"
    with l(1) obtain i j where *: "l ! i = x" "l ! j = y" "i < length l" "j < length l"
    by (meson in_set_conv_nth)
    have "i \<noteq> j"
    proof (rule ccontr, goal_cases)
      case 1
      with A * have "x \<prec> x" by auto
      with asymmetric A assms show False by auto
    qed
    have "i < j"
    proof (rule ccontr, goal_cases)
      case 1
      with \<open>i \<noteq> j\<close> sorted_nth_mono[OF l(2)] \<open>i < length l\<close> have "l ! j \<prec> l ! i" by auto
      with * A(3) A assms asymmetric show False by auto
    qed
    moreover have "?f x = i" using * l(3) A(1) by (auto) (rule, auto intro: distinct_nth_unique)
    moreover have "?f y = j" using * l(3) A(2) by (auto) (rule, auto intro: distinct_nth_unique)
    ultimately have "?f x < ?f y" by auto
  } moreover
  { fix x y assume A: "x \<in> S" "y \<in> S" "?f x < ?f y"
    with l(1) obtain i j where *: "l ! i = x" "l ! j = y" "i < length l" "j < length l"
    by (meson in_set_conv_nth)
    moreover have "?f x = i" using * l(3) A(1) by (auto) (rule, auto intro: distinct_nth_unique)
    moreover have "?f y = j" using * l(3) A(2) by (auto) (rule, auto intro: distinct_nth_unique)
    ultimately have **: "l ! ?f x = x" "l ! ?f y = y" "i < j" using A(3) by auto
    from sorted_nth_mono[OF l(2), of i j] **(3) * have "x \<prec> y" by auto
  }
  ultimately have "\<forall> x \<in> S. \<forall> y \<in> S. ?f x < ?f y \<longleftrightarrow> x \<prec> y" by force
  moreover have "range ?f \<subseteq> {0..card S - 1}"
  proof (auto, goal_cases)
    case (1 x)
    with l(1) obtain i where *: "l ! i = x" "i < length l" by (meson in_set_conv_nth)
    then have "?f x = i" using l(3) 1 by (auto) (rule, auto intro: distinct_nth_unique)
    with len show ?case using *(2) 1 by auto
  qed
  ultimately show ?thesis ..
qed

end

lemma finite_total_preorder_enumeration:
  fixes X :: "'a set"
  fixes r :: "'a rel"
  assumes fin:   "finite X"
  assumes tot:   "total_on X r"
  assumes refl:  "refl_on X r"
  assumes trans: "trans r"
  obtains f :: "'a \<Rightarrow> nat" where "\<forall> x \<in> X. \<forall> y \<in> X. f x \<le> f y \<longleftrightarrow> (x, y) \<in> r"
proof -
  let ?A = "\<lambda> x. {y \<in> X . (y, x) \<in> r \<and> (x, y) \<in> r}"
  have ex: "\<forall> x \<in> X. x \<in> ?A x" using refl unfolding refl_on_def by auto
  let ?R = "\<lambda> S. SOME y. y \<in> S"
  let ?T = "{?A x | x.  x \<in> X}"
  { fix A assume A: "A \<in> ?T"
    then obtain x where x: "x \<in> X" "?A x = A" by auto
    then have "x \<in> A" using refl unfolding refl_on_def by auto
    then have "?R A \<in> A" by (auto intro: someI)
    with x(2) have "(?R A, x) \<in> r" "(x, ?R A) \<in> r" by auto
    with trans have "(?R A, ?R A) \<in> r" unfolding trans_def by blast
  } note refl_lifted = this
  { fix A assume A: "A \<in> ?T"
    then obtain x where x: "x \<in> X" "?A x = A" by auto
    then have "x \<in> A" using refl unfolding refl_on_def by auto
    then have "?R A \<in> A" by (auto intro: someI)
  } note R_in = this
  { fix A y z assume A: "A \<in> ?T" and y: "y \<in> A" and z: "z \<in> A"
    from A obtain x where x: "x \<in> X" "?A x = A" by auto
    then have "x \<in> A" using refl unfolding refl_on_def by auto
    with x y have "(x, y) \<in> r" "(y, x) \<in> r" by auto
    moreover from x z have "(x,z) \<in> r" "(z,x) \<in> r" by auto
    ultimately have "(y, z) \<in> r" "(z, y) \<in> r" using trans unfolding trans_def by blast+
  } note A_dest' = this
  { fix A y assume "A \<in> ?T" and "y \<in> A"
    with A_dest'[OF _ _ R_in] have "(?R A, y) \<in> r" "(y, ?R A) \<in> r" by blast+
  } note A_dest = this
  { fix A y z assume A: "A \<in> ?T" and y: "y \<in> A" and z: "z \<in> X" and r: "(y, z) \<in> r" "(z, y) \<in> r"
    from A obtain x where x: "x \<in> X" "?A x = A" by auto
    then have "x \<in> A" using refl unfolding refl_on_def by auto
    with x y have "(x,y) \<in> r" "(y, x) \<in> r" by auto
    with r have "(x,z) \<in> r" "(z,x) \<in> r" using trans unfolding trans_def by blast+
    with x z have "z \<in> A" by auto
  } note A_intro' = this
  { fix A y assume A: "A \<in> ?T" and y: "y \<in> X" and r: "(?R A, y) \<in> r" "(y, ?R A) \<in> r"
    with A_intro' R_in have "y \<in> A" by blast
  } note A_intro = this
  { fix A B C
    assume r1: "(?R A, ?R B) \<in> r" and r2: "(?R B, ?R C) \<in> r"
    with trans have "(?R A, ?R C) \<in> r" unfolding trans_def by blast
  } note trans_lifted[intro] = this
  { fix A B a b
    assume A: "A \<in> ?T" and B: "B \<in> ?T"
    and a: "a \<in> A" and b: "b \<in> B"
    and r: "(a, b) \<in> r" "(b, a) \<in> r"
    with R_in have "?R A \<in> A" "?R B \<in> B" by blast+
    have "A = B"
    proof auto
      fix x assume x: "x \<in> A"
      with A have "x \<in> X" by auto
      from A_intro'[OF B b this] A_dest'[OF A x a] r trans[unfolded trans_def] show "x \<in> B" by blast
    next
      fix x assume x: "x \<in> B"
      with B have "x \<in> X" by auto
      from A_intro'[OF A a this] A_dest'[OF B x b] r trans[unfolded trans_def] show "x \<in> A" by blast
    qed
  } note eq_lifted'' = this
  { fix A B C
    assume A: "A \<in> ?T" and B: "B \<in> ?T" and r: "(?R A, ?R B) \<in> r" "(?R B, ?R A) \<in> r"
    with eq_lifted'' R_in have "A = B" by blast
  } note eq_lifted' = this
  { fix A B C
    assume A: "A \<in> ?T" and B: "B \<in> ?T" and eq: "?R A = ?R B"
    from R_in[OF A] A have "?R A \<in> X" by auto
    with refl have "(?R A, ?R A) \<in> r" unfolding refl_on_def by auto
    with eq_lifted'[OF A B] eq have "A = B" by auto
  } note eq_lifted = this
  { fix A B
    assume A: "A \<in> ?T" and B: "B \<in> ?T" and neq: "A \<noteq> B"
    from neq eq_lifted[OF A B] have "?R A \<noteq> ?R B" by metis
    moreover from A B R_in have "?R A \<in> X" "?R B \<in> X" by auto
    ultimately have "(?R A, ?R B) \<in> r \<or> (?R B, ?R A) \<in> r" using tot unfolding total_on_def by auto
  } note total_lifted = this
  { fix x y assume x: "x \<in> X" and y: "y \<in> X"
    from x y have "?A x \<in> ?T" "?A y \<in> ?T" by auto
    from R_in[OF this(1)] R_in[OF this(2)] have "?R (?A x) \<in> ?A x" "?R (?A y) \<in> ?A y" by auto
    then have "(x, ?R (?A x)) \<in> r" "(?R (?A y), y) \<in> r" "(?R (?A x), x) \<in> r" "(y, ?R (?A y)) \<in> r" by auto
    with trans[unfolded trans_def] have "(x, y) \<in> r \<longleftrightarrow> (?R (?A x), ?R (?A y)) \<in> r" by meson
  } note repr = this
  interpret interp: enumerateable "{?A x | x.  x \<in> X}" "\<lambda> A B. A \<noteq> B \<and> (?R A, ?R B) \<in> r"
  proof (standard, goal_cases)
    case 1
    from fin show ?case by auto
  next
    case 2
    with total_lifted show ?case by auto
  next
    case 3
    then show ?case unfolding transp_def
    proof (standard, standard, standard, standard, standard, goal_cases)
      case (1 A B C)
      note A = this
      with trans_lifted have "(?R A,?R C) \<in> r" by blast
      moreover have "A \<noteq> C"
      proof (rule ccontr, goal_cases)
        case 1
        with A have "(?R A,?R B) \<in> r" "(?R B,?R A) \<in> r" by auto
        with eq_lifted'[OF A(1,2)] A show False by auto
      qed
      ultimately show ?case by auto
    qed
  next
    case 4
    { fix A B assume A: "A \<in> ?T" and B: "B \<in> ?T" and neq: "A \<noteq> B" "(?R A, ?R B) \<in> r"
      with eq_lifted'[OF A B] neq have "\<not> (?R B, ?R A) \<in> r" by auto
    }
    then show ?case by auto
  qed
  from interp.order_fun[OF subset_refl] obtain f :: "'a set \<Rightarrow> nat" where
    f: "\<forall> x \<in> ?T. \<forall> y \<in> ?T. f x < f y \<longleftrightarrow> x \<noteq> y \<and> (?R x, ?R y) \<in> r" "range f \<subseteq> {0..card ?T - 1}"
  by auto
  let ?f = "\<lambda> x. if x \<in> X then f (?A x) else 0"
  { fix x y assume x: "x \<in> X" and y: "y \<in> X"
    have "?f x \<le> ?f y \<longleftrightarrow> (x, y) \<in> r"
    proof (cases "x = y")
      case True
      with refl x show ?thesis unfolding refl_on_def by auto
    next
      case False
      note F = this
      from ex x y have *: "?A x \<in> ?T" "?A y \<in> ?T" "x \<in> ?A x" "y \<in> ?A y" by auto
      show ?thesis
      proof (cases "(x, y) \<in> r \<and> (y, x) \<in> r")
        case True
        from eq_lifted''[OF *] True x y have "?f x = ?f y" by auto
        with True show ?thesis by auto
      next
        case False
        with A_dest'[OF *(1,3), of y] *(4) have **: "?A x \<noteq> ?A y" by auto
        from total_lifted[OF *(1,2) this] have "(?R (?A x), ?R (?A y)) \<in> r \<or> (?R (?A y), ?R (?A x)) \<in> r" .
        then have neq: "?f x \<noteq> ?f y"
        proof (standard, goal_cases)
          case 1
          with f *(1,2) ** have "f (?A x) < f (?A y)" by auto
          with * show ?case by auto
        next
          case 2
          with f *(1,2) ** have "f (?A y) < f (?A x)" by auto
          with * show ?case by auto
        qed
        then have "?thesis = (?f x < ?f y \<longleftrightarrow> (x, y) \<in> r)" by linarith
        moreover from f ** * have "(?f x < ?f y \<longleftrightarrow> (?R (?A x), ?R (?A y)) \<in> r)" by auto
        moreover from repr * have "\<dots> \<longleftrightarrow> (x, y) \<in> r" by auto
        ultimately show ?thesis by auto
      qed
    qed
  }
  then have "\<forall> x \<in> X. \<forall> y \<in> X. ?f x \<le> ?f y \<longleftrightarrow> (x, y) \<in> r" by blast
  then show ?thesis ..
qed

section \<open>Finiteness\<close>

lemma pairwise_finiteI:
  assumes "finite {b. \<exists>a. P a b}" (is "finite ?B")
  assumes "finite {a. \<exists>b. P a b}"
  shows "finite {(a,b). P a b}" (is "finite ?C")
proof -
  from assms(1) have "finite ?B" .
  let ?f = "\<lambda> b. {(a,b) | a. P a b}"
  { fix b
    have "?f b \<subseteq> {(a,b) | a. \<exists>b. P a b}" by blast
    moreover have "finite \<dots>" using assms(2) by auto 
    ultimately have "finite (?f b)" by (blast intro: finite_subset)
  }
  with assms(1) have "finite (\<Union> (?f ` ?B))" by auto
  moreover have "?C \<subseteq> \<Union> (?f ` ?B)" by auto
  ultimately show ?thesis by (blast intro: finite_subset)
qed

lemma finite_ex_and1:
  assumes "finite {b. \<exists>a. P a b}" (is "finite ?A")
  shows "finite {b. \<exists>a. P a b \<and> Q a b}" (is "finite ?B")
proof -
  have "?B \<subseteq> ?A" by auto
  with assms show ?thesis by (blast intro: finite_subset)
qed

lemma finite_ex_and2:
  assumes "finite {b. \<exists>a. Q a b}" (is "finite ?A")
  shows "finite {b. \<exists>a. P a b \<and> Q a b}" (is "finite ?B")
proof -
  have "?B \<subseteq> ?A" by auto
  with assms show ?thesis by (blast intro: finite_subset)
qed

lemma finite_set_of_finite_funs2:
  fixes A :: "'a set" 
    and B :: "'b set"
    and C :: "'c set"
    and d :: "'c" 
  assumes "finite A"
    and "finite B"
    and "finite C"
  shows "finite {f. \<forall>x. \<forall>y. (x \<in> A \<and> y \<in> B \<longrightarrow> f x y \<in> C) \<and> (x \<notin> A \<longrightarrow> f x y = d) \<and> (y \<notin> B \<longrightarrow> f x y = d)}"
proof -
  let ?S = "{f. \<forall>x. \<forall>y. (x \<in> A \<and> y \<in> B \<longrightarrow> f x y \<in> C) \<and> (x \<notin> A \<longrightarrow> f x y = d) \<and> (y \<notin> B \<longrightarrow> f x y = d)}"
  let ?R = "{g. \<forall>x. (x \<in> B \<longrightarrow> g x \<in> C) \<and> (x \<notin> B \<longrightarrow> g x = d)}"
  let ?Q = "{f. \<forall>x. (x \<in> A \<longrightarrow> f x \<in> ?R) \<and> (x \<notin> A \<longrightarrow> f x = (\<lambda>y. d))}"
  from finite_set_of_finite_funs[OF assms(2,3)] have "finite ?R" .
  from finite_set_of_finite_funs[OF assms(1) this, of "\<lambda> y. d"] have "finite ?Q" .
  moreover have "?S = ?Q" by auto (case_tac "xa \<in> A", auto)
  ultimately show ?thesis by simp
qed

section \<open>Numbering the elements of finite sets\<close>

lemma upt_last_append: "a \<le> b \<Longrightarrow> [a..<b] @ [b] = [a ..< Suc b]" by (induction b) auto

lemma map_of_zip_dom_to_range:
  "a \<in> set A \<Longrightarrow> length B = length A \<Longrightarrow> the (map_of (zip A B) a) \<in> set B"
by (metis map_of_SomeD map_of_zip_is_None option.collapse set_zip_rightD)

lemma zip_range_id:
  "length A = length B \<Longrightarrow> snd ` set (zip A B) = set B"
by (metis map_snd_zip set_map)

lemma map_of_zip_in_range:
  "distinct A \<Longrightarrow> length B = length A \<Longrightarrow> b \<in> set B \<Longrightarrow> \<exists> a \<in> set A. the (map_of (zip A B) a) = b"
proof goal_cases
  case 1
  from ran_distinct[of "zip A B"] 1(1,2) have
    "ran (map_of (zip A B)) = set B"
  by (auto simp: zip_range_id)
  with 1(3) obtain a where "map_of (zip A B) a = Some b" unfolding ran_def by auto
  with map_of_zip_is_Some[OF 1(2)[symmetric]] have "the (map_of (zip A B) a) = b" "a \<in> set A" by auto
  then show ?case by blast
qed

lemma distinct_zip_inj:
  "distinct ys \<Longrightarrow> (a, b) \<in> set (zip xs ys) \<Longrightarrow> (c, b) \<in> set (zip xs ys) \<Longrightarrow> a = c"
proof (induction ys arbitrary: xs)
  case Nil then show ?case by auto
next
  case (Cons y ys)
  from this(3) have "xs \<noteq> []" by auto
  then obtain z zs where xs: "xs = z # zs" by (cases xs) auto
  show ?case
  proof (cases "(a, b) \<in> set (zip zs ys)")
    case True
    note T = this
    then have b: "b \<in> set ys" by (meson in_set_zipE) 
    show ?thesis
    proof (cases "(c, b) \<in> set (zip zs ys)")
      case True
      with T Cons show ?thesis by auto
    next
      case False
      with Cons.prems xs b show ?thesis by auto
    qed
  next
    case False
    with Cons.prems xs have b: "a = z" "b = y" by auto
    show ?thesis
    proof (cases "(c, b) \<in> set (zip zs ys)")
      case True
      then have "b \<in> set ys" by (meson in_set_zipE)
      with b \<open>distinct (y#ys)\<close> show ?thesis by auto
    next
      case False
      with Cons.prems xs b show ?thesis by auto
    qed
  qed
qed

lemma map_of_zip_distinct_inj:
  "distinct B \<Longrightarrow> length A = length B \<Longrightarrow> inj_on (the o map_of (zip A B)) (set A)"
unfolding inj_on_def proof (clarify, goal_cases)
  case (1 x y)
  with map_of_zip_is_Some[OF 1(2)] obtain a where
    "map_of (zip A B) x = Some a" "map_of (zip A B) y = Some a"
  by auto
  then have "(x, a) \<in> set (zip A B)" "(y, a) \<in> set (zip A B)" using map_of_SomeD by metis+
  from distinct_zip_inj[OF _ this] 1 show ?case by auto
qed

lemma nat_not_ge_1D: "\<not> Suc 0 \<le> x \<Longrightarrow> x = 0" by auto

lemma standard_numbering:
  assumes "finite A"
  obtains v :: "'a \<Rightarrow> nat" and n where "bij_betw v A {1..n}"
  and "\<forall> c \<in> A. v c > 0"
  and "\<forall> c. c \<notin> A \<longrightarrow> v c > n"
proof -
  from assms obtain L where L: "distinct L" "set L = A" by (meson finite_distinct_list)
  let ?N = "length L + 1"
  let ?P = "zip L [1..<?N]"
  let ?v = "\<lambda> x. let v = map_of ?P x in if v = None then ?N else the v"
  from length_upt have len: "length [1..<?N] = length L" by auto (cases L, auto)
  then have lsimp: "length [Suc 0 ..<Suc (length L)] = length L" by simp
  note * = map_of_zip_dom_to_range[OF _ len]
  have "bij_betw ?v A {1..length L}" unfolding bij_betw_def
  proof
    show "?v ` A = {1..length L}" apply auto
      apply (auto simp: L)[] 
      apply (auto simp only: upt_last_append)[] using * apply force
      using * apply (simp only: upt_last_append) apply force
      apply (simp only: upt_last_append) using L(2) apply (auto dest: nat_not_ge_1D)
      apply (subgoal_tac "x \<in> set [1..< length L +1]")
      apply (force dest!: map_of_zip_in_range[OF L(1) len])
      apply auto
    done
  next
    from L map_of_zip_distinct_inj[OF distinct_upt, of L 1 "length L + 1"] len
    have "inj_on (the o map_of ?P) A" by auto
    moreover have "inj_on (the o map_of ?P) A = inj_on ?v A"
    using len L(2) by - (rule inj_on_cong, auto)
    ultimately show "inj_on ?v A" by blast
  qed
  moreover have "\<forall> c \<in> A. ?v c > 0"
  proof
    fix c
    show "?v c > 0"
    proof (cases "c \<in> set L")
      case False
      then show ?thesis by auto
    next
      case True
      with dom_map_of_zip[OF len[symmetric]] obtain x where
        "Some x = map_of ?P c" "x \<in> set [1..<length L + 1]"
      by (metis * domIff option.collapse)
      then have "?v c \<in> set [1..<length L + 1]" using * True len by auto
      then show ?thesis by auto
    qed
  qed
  moreover have "\<forall> c. c \<notin> A \<longrightarrow> ?v c > length L" using L by auto
  ultimately show ?thesis ..
qed

end
(*>*)
