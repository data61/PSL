(*
  File:    IMO2019_Q5.thy
  Author:  Manuel Eberl, TU München
*)
section \<open>Q5\<close>
theory IMO2019_Q5
  imports Complex_Main
begin

text \<open>
  Given a sequence $(c_1,\ldots, c_n)$ of coins, each of which can be heads (\<open>H\<close>) or tails (\<open>T\<close>),
  Harry performs the following process: Let \<open>k\<close> be the number of coins that show \<open>H\<close>. If \<open>k > 0\<close>,
  flip the \<open>k\<close>-th coin and repeat the process. Otherwise, stop.

  What is the average number of steps that this process takes, averaged over all $2^n$ 
  coin sequences of length \<open>n\<close>?
\<close>

subsection \<open>Definition\<close>

text \<open>
  We represent coins as Booleans, where @{term True} indicates \<open>H\<close> and @{term False} indicates \<open>T\<close>.
  Coin sequences are then simply lists of Booleans.

  The following function flips the \<open>i\<close>-th coin in the sequence (in Isabelle, the convention is that
  the first list element is indexed with 0).
\<close>
definition flip :: "bool list \<Rightarrow> nat \<Rightarrow> bool list" where
  "flip xs i = xs[i := \<not>xs ! i]"

lemma flip_Cons_pos [simp]: "n > 0 \<Longrightarrow> flip (x # xs) n = x # flip xs (n - 1)"
  by (cases n) (auto simp: flip_def)

lemma flip_Cons_0 [simp]: "flip (x # xs) 0 = (\<not>x) # xs"
  by (simp add: flip_def)

lemma flip_append1 [simp]: "n < length xs \<Longrightarrow> flip (xs @ ys) n = flip xs n @ ys"
  and flip_append2 [simp]: "n \<ge> length xs \<Longrightarrow> n < length xs + length ys \<Longrightarrow>
                               flip (xs @ ys) n = xs @ flip ys (n - length xs)"
  by (auto simp: flip_def list_update_append nth_append)

lemma length_flip [simp]: "length (flip xs i) = length xs"
  by (simp add: flip_def)



text \<open>
  The following function computes the number of \<open>H\<close> in a coin sequence.
\<close>
definition heads :: "bool list \<Rightarrow> nat" where "heads xs = length (filter id xs)"

lemma heads_True [simp]: "heads (True # xs) = 1 + heads xs"
  and heads_False [simp]: "heads (False # xs) = heads xs"
  and heads_append [simp]: "heads (xs @ ys) = heads xs + heads ys"
  and heads_Nil [simp]: "heads [] = 0"
  by (auto simp: heads_def)

lemma heads_Cons: "heads (x # xs) = (if x then heads xs + 1 else heads xs)"
  by (auto simp: heads_def)

lemma heads_pos: "True \<in> set xs \<Longrightarrow> heads xs > 0"
  by (induction xs) (auto simp: heads_Cons)

lemma heads_eq_0 [simp]: "True \<notin> set xs \<Longrightarrow> heads xs = 0"
  by (induction xs) (auto simp: heads_Cons)

lemma heads_eq_0_iff [simp]: "heads xs = 0 \<longleftrightarrow> True \<notin> set xs"
  by (induction xs) (auto simp: heads_Cons)

lemma heads_pos_iff [simp]: "heads xs > 0 \<longleftrightarrow> True \<in> set xs"
  by (induction xs) (auto simp: heads_Cons)

lemma heads_le_length: "heads xs \<le> length xs"
  by (auto simp: heads_def)


text \<open>
  The following function performs a single step of Harry's process.
\<close>
definition harry_step :: "bool list \<Rightarrow> bool list" where
  "harry_step xs = flip xs (heads xs - 1)"

lemma length_harry_step [simp]: "length (harry_step xs) = length xs"
  by (simp add: harry_step_def)


text \<open>
  The following is the measure function for Harry's process, i.e. how many steps the process takes
  to terminate starting from the given sequence. We define it like this now and prove the
  correctness later.
\<close>
function harry_meas where
  "harry_meas xs =
     (if xs = [] then 0
      else if hd xs then 1 + harry_meas (tl xs)
      else if \<not>last xs then harry_meas (butlast xs)
      else let n = length xs in harry_meas (take (n - 2) (tl xs)) + 2 * n - 1)"
  by auto
termination by (relation "Wellfounded.measure length") (auto simp: min_def)

lemmas [simp del] = harry_meas.simps


text \<open>
  We now prove some simple properties of @{const harry_meas} and @{const harry_step}.
\<close>

text \<open>
  We prove a more convenient case distinction rule for lists that allows us to
  distinguish between lists starting with @{term True}, ending with @{term False}, and
  starting with @{term False} and ending with @{term True}.
\<close>
lemma head_last_cases [case_names Nil True False False_True]:
  assumes "xs = [] \<Longrightarrow> P"
  assumes "\<And>ys. xs = True # ys \<Longrightarrow> P" "\<And>ys. xs = ys @ [False] \<Longrightarrow> P"
          "\<And>ys. xs = False # ys @ [True] \<Longrightarrow> P"
  shows   "P"
proof -
  consider "length xs = 0" | "length xs = 1" | "length xs \<ge> 2" by linarith
  thus ?thesis
  proof cases
    assume "length xs = 1"
    hence "xs = [hd xs]" by (cases xs) auto
    thus P using assms(2)[of "[]"] assms(3)[of "[]"] by (cases "hd xs") auto
  next
    assume len: "length xs \<ge> 2"
    from len obtain x xs' where *: "xs = x # xs'"
      by (cases xs) auto
    have **: "xs' = butlast xs' @ [last xs']"
      using len by (subst append_butlast_last_id) (auto simp: *)
    have [simp]: "xs = x # butlast xs' @ [last xs']"
      by (subst *, subst **) auto
    show P
      using assms(2)[of xs'] assms(3)[of "x # butlast xs'"] assms(4)[of "butlast xs'"] **
      by (cases x; cases "last xs'") auto
  qed (use assms in auto)
qed

lemma harry_meas_Nil [simp]: "harry_meas [] = 0"
  by (simp add: harry_meas.simps)

lemma harry_meas_True_start [simp]: "harry_meas (True # xs) = 1 + harry_meas xs"
  by (subst harry_meas.simps) auto

lemma harry_meas_False_end [simp]: "harry_meas (xs @ [False]) = harry_meas xs"
proof (induction xs)
  case (Cons x xs)
  thus ?case by (cases x) (auto simp: harry_meas.simps)
qed (auto simp: harry_meas.simps)

lemma harry_meas_False_True: "harry_meas (False # xs @ [True]) = harry_meas xs + 2 * length xs + 3"
  by (subst harry_meas.simps) auto

lemma harry_meas_eq_0 [simp]:
  assumes "True \<notin> set xs"
  shows   "harry_meas xs = 0"
  using assms by (induction xs rule: rev_induct) auto

text \<open>
  If the sequence starts with \<open>H\<close>, the process runs on the remaining sequence until it
  terminates and then flips this \<open>H\<close> in another single step.
\<close>
lemma harry_step_True_start [simp]:
  "harry_step (True # xs) = (if True \<in> set xs then True # harry_step xs else False # xs)"
  by (auto simp: harry_step_def)

text \<open>
  If the sequence ends in \<open>T\<close>, the process simply runs on the remaining sequence as if it
  were not present.
\<close>
lemma harry_step_False_end [simp]:
  assumes "True \<in> set xs"
  shows   "harry_step (xs @ [False]) = harry_step xs @ [False]"
proof -
  have "harry_step (xs @ [False]) = flip (xs @ [False]) (heads xs - 1)"
    using heads_le_length[of xs] by (auto simp: harry_step_def)
  also have "\<dots> = harry_step xs @ [False]"
    using Suc_less_eq assms heads_le_length[of xs]
    by (subst flip_append1; fastforce simp: harry_step_def)
  finally show ?thesis .
qed

text \<open>
  If the sequence starts with \<open>T\<close> and ends with \<open>H\<close>, the process runs on the remaining
  sequence inbetween as if these two were not present, eventually leaving a sequence that
  consists entirely if \<open>T\<close> except for a single final \<open>H\<close>.
\<close>
lemma harry_step_False_True:
  assumes "True \<in> set xs"
  shows "harry_step (False # xs @ [True]) = False # harry_step xs @ [True]"
proof -
  have "harry_step (False # xs @ [True]) = False # flip (xs @ [True]) (heads xs - 1)"
    using assms heads_le_length[of xs] by (auto simp: harry_step_def heads_le_length)
  also have "\<dots> = False # harry_step xs @ [True]"
    using assms by (subst flip_append1)
                   (auto simp: harry_step_def Suc_less_SucD heads_le_length less_Suc_eq_le)
  finally show ?thesis .
qed

text \<open>
  That sequence consisting only of \<open>T\<close> except for a single final \<open>H\<close> is then turned into
  an all-\<open>T\<close> sequence in \<open>2n+1\<close> steps.
\<close>
lemma harry_meas_Falses_True [simp]: "harry_meas (replicate n False @ [True]) = 2 * n + 1"
proof (cases "n = 0")
  case False
  hence "replicate n False @ [True] = False # replicate (n - 1) False @ [True]"
    by (cases n) auto
  also have "harry_meas \<dots> = 2 * n + 1"
    using False by (simp add: harry_meas_False_True algebra_simps)
  finally show ?thesis .
qed auto

lemma harry_step_Falses_True [simp]:
  "n > 0 \<Longrightarrow> harry_step (replicate n False @ [True]) = True # replicate (n - 1) False @ [True]"
  by (cases n) (simp_all add: harry_step_def)


subsection \<open>Correctness of the measure\<close>

text \<open>
  We will now show that @{const harry_meas} indeed counts the length of the process.
  As a first step, we will show that if there is a \<open>H\<close> in a sequence, applying a single step
  decreases the measure by one.
\<close>
lemma harry_meas_step_aux:
  assumes "True \<in> set xs"
  shows   "harry_meas xs = Suc (harry_meas (harry_step xs))"
  using assms
proof (induction xs rule: length_induct)
  case (1 xs)
  hence IH: "harry_meas ys = Suc (harry_meas (harry_step ys))"
    if "length ys < length xs" "True \<in> set ys" for ys
    using that by blast

  show ?case
  proof (cases xs rule: head_last_cases)
    case (True ys)
    thus ?thesis by (auto simp: IH)
  next
    case (False ys)
    thus ?thesis using "1.prems" by (auto simp: IH)
  next
    case (False_True ys)
    thus ?thesis
    proof (cases "True \<in> set ys")
      case False
      define n where "n = length ys + 1"
      have "n > 0" by (simp add: n_def)
      from False have "ys = replicate (n - 1) False"
        unfolding n_def by (induction ys) auto
      with False_True \<open>n > 0\<close> have [simp]: "xs = replicate n False @ [True]"
        by (cases n) auto
      show ?thesis using \<open>n > 0\<close> by auto
    qed (auto simp: IH False_True harry_step_False_True harry_meas_False_True)
  qed (use 1 in auto)
qed

lemma harry_meas_step: "True \<in> set xs \<Longrightarrow> harry_meas (harry_step xs) = harry_meas xs - 1"
  using harry_meas_step_aux[of xs] by simp

text \<open>
  Next, we show that the measure is zero if and only if there is no \<open>H\<close> left in the sequence.
\<close>
lemma harry_meas_eq_0_iff [simp]: "harry_meas xs = 0 \<longleftrightarrow> True \<notin> set xs"
proof (induction xs rule: length_induct)
  case (1 xs)
  show ?case
    by (cases xs rule: head_last_cases) (auto simp: 1 harry_meas_False_True 1)
qed

text \<open>
  It follows by induction that if the measure of a sequence is \<open>n\<close>, then iterating the step
  less than \<open>n\<close> times yields a sequence with at least one \<open>H\<close> in it, but iterating it exactly
  \<open>n\<close> times yields a sequence that contains no more \<open>H\<close>.
\<close>
lemma True_in_funpow_harry_step:
  assumes "n < harry_meas xs"
  shows   "True \<in> set ((harry_step ^^ n) xs)"
  using assms
proof (induction n arbitrary: xs)
  case 0
  show ?case by (rule ccontr) (use 0 in auto)
next
  case (Suc n)
  have "True \<in> set xs" by (rule ccontr) (use Suc in auto)
  have "(harry_step ^^ Suc n) xs = (harry_step ^^ n) (harry_step xs)"
    by (simp only: funpow_Suc_right o_def)
  also have "True \<in> set \<dots>"
    using Suc \<open>True \<in> set xs\<close> by (intro Suc) (auto simp: harry_meas_step)
  finally show ?case .
qed

lemma True_notin_funpow_harry_step: "True \<notin> set ((harry_step ^^ harry_meas xs) xs)"
proof (induction "harry_meas xs" arbitrary: xs)
  case (Suc n)
  have "True \<in> set xs" by (rule ccontr) (use Suc in auto)
  have "(harry_step ^^ harry_meas xs) xs = (harry_step ^^ Suc n) xs"
    by (simp only: Suc)
  also have "\<dots> = (harry_step ^^ n) (harry_step xs)"
    by (simp only: funpow_Suc_right o_def)
  also have "\<dots> = (harry_step ^^ (harry_meas xs - 1)) (harry_step xs)"
    by (simp flip: Suc(2))
  also have "harry_meas xs - 1 = harry_meas (harry_step xs)"
     using \<open>True \<in> set xs\<close> by (subst harry_meas_step) auto
  also have "True \<notin> set ((harry_step ^^ \<dots>) (harry_step xs))"
    using Suc \<open>True \<in> set xs\<close> by (intro Suc) (auto simp: harry_meas_step)
  finally show ?case .
qed auto

text \<open>
  This shows that the measure is indeed the correct one: It is the smallest number such that
  iterating Harry's step that often yields a sequence with no heads in it.
\<close>
theorem "harry_meas xs = (LEAST n. True \<notin> set ((harry_step ^^ n) xs))"
proof (rule sym, rule Least_equality, goal_cases)
  show "True \<notin> set ((harry_step ^^ harry_meas xs) xs)"
    by (rule True_notin_funpow_harry_step)
next
  case (2 y)
  show ?case
    by (rule ccontr) (use 2 True_in_funpow_harry_step[of y] in auto)
qed


subsection \<open>Average-case analysis\<close>

text \<open>
  The set of all coin sequences of a given length.
\<close>
definition seqs where "seqs n = {xs :: bool list . length xs = n}"

lemma length_seqs [dest]: "xs \<in> seqs n \<Longrightarrow> length xs = n"
  by (simp add: seqs_def)

lemma seqs_0 [simp]: "seqs 0 = {[]}"
  by (auto simp: seqs_def)

text \<open>
  The coin sequences of length \<open>n + 1\<close> are simply what is obtained by appending either \<open>H\<close>
  or \<open>T\<close> to each coin sequence of length \<open>n\<close>.
\<close>
lemma seqs_Suc: "seqs (Suc n) = (\<lambda>xs. True # xs) ` seqs n \<union> (\<lambda>xs. False # xs) ` seqs n"
  by (auto simp: seqs_def length_Suc_conv)

text \<open>
  The set of coin sequences of length \<open>n\<close> is invariant under reversal.
\<close>
lemma seqs_rev [simp]: "rev ` seqs n = seqs n"
proof
  show "rev ` seqs n \<subseteq> seqs n"
    by (auto simp: seqs_def)
  hence "rev ` rev ` seqs n \<subseteq> rev ` seqs n"
    by blast
  thus "seqs n \<subseteq> rev ` seqs n" by (simp add: image_image)
qed

text \<open>
  Hence we get a similar decomposition theorem that appends at the end.
\<close>
lemma seqs_Suc': "seqs (Suc n) = (\<lambda>xs. xs @ [True]) ` seqs n \<union> (\<lambda>xs. xs @ [False]) ` seqs n"
proof -
  have "rev ` rev ` ((\<lambda>xs. xs @ [True]) ` seqs n \<union> (\<lambda>xs. xs @ [False]) ` seqs n) =
          rev ` ((\<lambda>xs. True # xs) ` rev ` seqs n \<union> (\<lambda>xs. False # xs) ` rev ` seqs n)"
    unfolding image_Un image_image by simp
  also have "(\<lambda>xs. True # xs) ` rev ` seqs n \<union> (\<lambda>xs. False # xs) ` rev ` seqs n = seqs (Suc n)"
    by (simp add: seqs_Suc)
  finally show ?thesis by (simp add: image_image)
qed

lemma finite_seqs [intro]: "finite (seqs n)"
  by (induction n) (auto simp: seqs_Suc)

lemma card_seqs [simp]: "card (seqs n) = 2 ^ n"
proof (induction n)
  case (Suc n)
  have "card (seqs (Suc n)) = card ((#) True ` seqs n \<union> (#) False ` seqs n)"
    by (auto simp: seqs_Suc)
  also from Suc.IH have "\<dots> = 2 ^ Suc n"
    by (subst card_Un_disjoint) (auto simp: card_image)
  finally show ?case .
qed auto

lemmas seqs_code [code] = seqs_0 seqs_Suc


text \<open>
  The sum of the measures over all possible coin sequences of a given length (defined
  as a recurrence relation; correctness proven later).
\<close>
fun harry_sum :: "nat \<Rightarrow> nat" where
  "harry_sum 0 = 0"
| "harry_sum (Suc 0) = 1"
| "harry_sum (Suc (Suc n)) = 2 * harry_sum (Suc n) + (2 * n + 4) * 2 ^ n"

lemma Suc_Suc_induct: "P 0 \<Longrightarrow> P (Suc 0) \<Longrightarrow> (\<And>n. P n \<Longrightarrow> P (Suc n) \<Longrightarrow> P (Suc (Suc n))) \<Longrightarrow> P n"
  by induction_schema (pat_completeness, rule wf_measure[of id], auto)

text \<open>
  The recurrence relation really does describe the sum over all measures:
\<close>
lemma harry_sum_correct: "harry_sum n = sum harry_meas (seqs n)"
proof (induction n rule: Suc_Suc_induct)
  case (3 n)
  have "seqs (Suc (Suc n)) =
          (\<lambda>xs. xs @ [False]) ` seqs (Suc n) \<union>
          (\<lambda>xs. True # xs @ [True]) ` seqs n \<union> 
          (\<lambda>xs. False # xs @ [True]) ` seqs n"
    by (subst (1) seqs_Suc, subst (1 2) seqs_Suc') (simp add: image_Un image_image Un_ac seqs_Suc)
  also have "int (sum harry_meas \<dots>) =
               int (harry_sum (Suc n)) +
               int (\<Sum>xs\<in>seqs n. 1 + harry_meas (xs @ [True])) +
               int (\<Sum>xs\<in>seqs n. harry_meas (False # xs @ [True]))"
    by (subst sum.union_disjoint sum.reindex, auto simp: inj_on_def 3)+
  also have "int (\<Sum>xs\<in>seqs n. 1 + harry_meas (xs @ [True])) =
                2 ^ n + int (\<Sum>xs\<in>seqs n. harry_meas (xs @ [True]))"
    by (subst sum.distrib) auto
  also have "(\<Sum>xs\<in>seqs n. harry_meas (False # xs @ [True])) = harry_sum n + (2 * n + 3) * 2 ^ n"
    by (auto simp: 3 harry_meas_False_True sum.distrib algebra_simps length_seqs)
  also have "harry_sum (Suc n) = (\<Sum>xs\<in>seqs n. harry_meas (xs @ [True])) + harry_sum n"
    unfolding seqs_Suc' 3 by (subst sum.union_disjoint sum.reindex, auto simp: inj_on_def)+
  hence "int (\<Sum>xs\<in>seqs n. harry_meas (xs @ [True])) = int (harry_sum (Suc n)) - int (harry_sum n)"
    by simp
  finally have "int (\<Sum>x\<in>seqs (Suc (Suc n)). harry_meas x) =
                  int (2 * harry_sum (Suc n) + (2 * n + 4) * 2 ^ n)"
    unfolding of_nat_add by (simp add: algebra_simps)
  hence "(\<Sum>x\<in>seqs (Suc (Suc n)). (harry_meas x)) =
            (2 * harry_sum (Suc n) + (2 * n + 4) * 2 ^ n)" by linarith
  thus ?case by simp
qed (auto simp: seqs_Suc)

lemma harry_sum_closed_form_aux: "4 * harry_sum n = n * (n + 1) * 2 ^ n"
  by (induction n rule: harry_sum.induct) (auto simp: algebra_simps)

text \<open>
  Solving the recurrence gives us the following solution:
\<close>
theorem harry_sum_closed_form: "harry_sum n = n * (n + 1) * 2 ^ n div 4"
  using harry_sum_closed_form_aux[of n] by simp


text \<open>
  The average is now a simple consequence:
\<close>
definition harry_avg where "harry_avg n = harry_sum n / card (seqs n)"

corollary "harry_avg n = n * (n + 1) / 4"
proof -
  have "real (4 * harry_sum n) = n * (n + 1) * 2 ^ n"
    by (subst harry_sum_closed_form_aux) auto
  hence "real (harry_sum n) = n * (n + 1) * 2 ^ n / 4"
    by (simp add: field_simps)
  thus ?thesis
    by (simp add: harry_avg_def field_simps)
qed

end