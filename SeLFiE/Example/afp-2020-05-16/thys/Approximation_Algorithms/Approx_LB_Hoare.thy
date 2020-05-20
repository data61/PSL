section \<open>Load Balancing\<close>

theory Approx_LB_Hoare
  imports Complex_Main "HOL-Hoare.Hoare_Logic"
begin

text \<open>This is formalization of the load balancing algorithms and proofs
in the book by Kleinberg and Tardos \cite{KleinbergT06}.\<close>

hide_const (open) sorted

(* TODO: mv *)

lemma sum_le_card_Max: "\<lbrakk> finite A; A \<noteq> {} \<rbrakk> \<Longrightarrow> sum f A \<le> card A * Max (f ` A)"
proof(induction A rule: finite_ne_induct)
  case (singleton x)
  then show ?case by simp
next
  case (insert x F)
  then show ?case by (auto simp: max_def order.trans[of "sum f F" "card F * Max (f ` F)"])
qed

lemma Max_const[simp]: "\<lbrakk> finite A; A \<noteq> {} \<rbrakk> \<Longrightarrow> Max ((\<lambda>_. c) ` A) = c"
using Max_in image_is_empty by blast

abbreviation Max\<^sub>0 :: "nat set \<Rightarrow> nat" where
"Max\<^sub>0 N \<equiv> (if N={} then 0 else Max N)"

fun f_Max\<^sub>0 :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "f_Max\<^sub>0 f 0 = 0"
| "f_Max\<^sub>0 f (Suc x) = max (f (Suc x)) (f_Max\<^sub>0 f x)"

lemma f_Max\<^sub>0_equiv: "f_Max\<^sub>0 f n = Max\<^sub>0 (f ` {1..n})"
  by (induction n) (auto simp: not_le atLeastAtMostSuc_conv)

lemma f_Max\<^sub>0_correct:
  "\<forall>x \<in> {1..m}. T x \<le> f_Max\<^sub>0 T m"
  "m > 0 \<Longrightarrow> \<exists>x \<in> {1..m}. T x = f_Max\<^sub>0 T m"
   apply (induction m)
     apply simp_all
   apply (metis atLeastAtMost_iff le_Suc_eq max.cobounded1 max.coboundedI2)
  subgoal for m by (cases \<open>m = 0\<close>) (auto simp: max_def)
  done

lemma f_Max\<^sub>0_mono:
  "y \<le> T x \<Longrightarrow> f_Max\<^sub>0 (T (x := y)) m \<le> f_Max\<^sub>0 T m"
  "T x \<le> y \<Longrightarrow> f_Max\<^sub>0 T m \<le> f_Max\<^sub>0 (T (x := y)) m"
  by (induction m) auto

lemma f_Max\<^sub>0_out_of_range [simp]:
  "x \<notin> {1..k} \<Longrightarrow> f_Max\<^sub>0 (T (x := y)) k = f_Max\<^sub>0 T k"
  by (induction k) auto

lemma fun_upd_f_Max\<^sub>0:
  assumes "x \<in> {1..m}" "T x \<le> y"
  shows "f_Max\<^sub>0 (T (x := y)) m = max y (f_Max\<^sub>0 T m)"
  using assms by (induction m) auto

locale LoadBalancing = (* Load Balancing *)
  fixes t :: "nat \<Rightarrow> nat"
    and m :: nat
    and n :: nat
  assumes m_gt_0: "m > 0"
begin

subsection \<open>Formalization of a Correct Load Balancing\<close>

subsubsection \<open>Definition\<close>

definition lb :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat set) \<Rightarrow> nat \<Rightarrow> bool" where
  "lb T A j = ((\<forall>x \<in> {1..m}. \<forall>y \<in> {1..m}. x \<noteq> y \<longrightarrow> A x \<inter> A y = {}) \<comment> \<open>No job is assigned to more than one machine\<close>
             \<and> (\<Union>x \<in> {1..m}. A x) = {1..j} \<comment> \<open>Every job is assigned\<close>
             \<and> (\<forall>x \<in> {1..m}. (\<Sum>j \<in> A x. t j) = T x) \<comment> \<open>The processing times sum up to the correct load\<close>)"

abbreviation makespan :: "(nat \<Rightarrow> nat) \<Rightarrow> nat" where
  "makespan T \<equiv> f_Max\<^sub>0 T m"

lemma makespan_def': "makespan T = Max (T ` {1..m})"
  using m_gt_0 by (simp add: f_Max\<^sub>0_equiv)
(*
lemma makespan_correct:
  "\<forall>x \<in> {1..m}. T x \<le> makespan T m"
  "m > 0 \<Longrightarrow> \<exists>x \<in> {1..m}. T x = makespan T m"
   apply (induction m)
     apply simp_all
   apply (metis atLeastAtMost_iff le_Suc_eq max.cobounded1 max.coboundedI2)
  subgoal for m by (cases \<open>m = 0\<close>) (auto simp: max_def)
  done

lemma no_machines_lb_iff_no_jobs: "lb T A j 0 \<longleftrightarrow> j = 0"
  unfolding lb_def by auto

lemma machines_if_jobs: "\<lbrakk> lb T A j m; j > 0 \<rbrakk> \<Longrightarrow> m > 0"
  using no_machines_lb_iff_no_jobs by (cases m) auto
*)

lemma makespan_correct:
  "\<forall>x \<in> {1..m}. T x \<le> makespan T"
  "\<exists>x \<in> {1..m}. T x = makespan T"
  using f_Max\<^sub>0_correct m_gt_0 by auto

lemma lbE:
  assumes "lb T A j"
  shows "\<forall>x \<in> {1..m}. \<forall>y \<in> {1..m}. x \<noteq> y \<longrightarrow> A x \<inter> A y = {}"
        "(\<Union>x \<in> {1..m}. A x) = {1..j}"
        "\<forall>x \<in> {1..m}. (\<Sum>y \<in> A x. t y) = T x"
  using assms unfolding lb_def by blast+

lemma lbI:
  assumes "\<forall>x \<in> {1..m}. \<forall>y \<in> {1..m}. x \<noteq> y \<longrightarrow> A x \<inter> A y = {}"
          "(\<Union>x \<in> {1..m}. A x) = {1..j}"
          "\<forall>x \<in> {1..m}. (\<Sum>y \<in> A x. t y) = T x"
  shows "lb T A j" using assms unfolding lb_def by blast

lemma A_lb_finite [simp]:
  assumes "lb T A j" "x \<in> {1..m}"
  shows "finite (A x)"
  by (metis lbE(2) assms finite_UN finite_atLeastAtMost)

text \<open>If \<open>A x\<close> is pairwise disjoint for all \<open>x \<in> {1..m}\<close>, then the the sum over the sums of the
      individual \<open>A x\<close> is equal to the sum over the union of all \<open>A x\<close>.\<close>
lemma sum_sum_eq_sum_Un:
  fixes A :: "nat \<Rightarrow> nat set"
  assumes "\<forall>x \<in> {1..m}. \<forall>y \<in> {1..m}. x \<noteq> y \<longrightarrow> A x \<inter> A y = {}"
      and "\<forall>x \<in> {1..m}. finite (A x)"
  shows "(\<Sum>x \<in> {1..m}. (\<Sum>y \<in> A x. t y)) = (\<Sum>x \<in> (\<Union>y \<in> {1..m}. A y). t x)"
  using assms
proof (induction m)
  case (Suc m)
  have FINITE: "finite (\<Union>x \<in> {1..m}. A x)" "finite (A (Suc m))"
    using Suc.prems(2) by auto
  have "\<forall>x \<in> {1..m}. A x \<inter> A (Suc m) = {}"
    using Suc.prems(1) by simp
  then have DISJNT: "(\<Union>x \<in> {1..m}. A x) \<inter> (A (Suc m)) = {}" using Union_disjoint by blast
  have "(\<Sum>x \<in> (\<Union>y \<in> {1..m}. A y). t x) + (\<Sum>x \<in> A (Suc m). t x)
      = (\<Sum>x \<in> ((\<Union>y \<in> {1..m}. A y) \<union> A (Suc m)). t x)"
    using sum.union_disjoint[OF FINITE DISJNT, symmetric] .
  also have "... = (\<Sum>x \<in> (\<Union>y \<in> {1..Suc m}. A y). t x)"
    by (metis UN_insert image_Suc_lessThan image_insert inf_sup_aci(5) lessThan_Suc)
  finally show ?case using Suc by auto
qed simp

text \<open>If \<open>T\<close> and \<open>A\<close> are a correct load balancing for \<open>j\<close> jobs and \<open>m\<close> machines, 
      then the sum of the loads has to be equal to the sum of the processing times of the jobs\<close>
lemma lb_impl_job_sum:
  assumes "lb T A j"
  shows "(\<Sum>x \<in> {1..m}. T x) = (\<Sum>x \<in> {1..j}. t x)"
proof -
  note lbrules = lbE[OF assms]
  from assms have FINITE: "\<forall>x \<in> {1..m}. finite (A x)" by simp
  have "(\<Sum>x \<in> {1..m}. T x) = (\<Sum>x \<in> {1..m}. (\<Sum>y \<in> A x. t y))"
    using lbrules(3) by simp
  also have "... = (\<Sum>x \<in> {1..j}. t x)"
    using sum_sum_eq_sum_Un[OF lbrules(1) FINITE]
    unfolding lbrules(2) .
  finally show ?thesis .
qed

subsubsection \<open>Lower Bounds for the Makespan\<close>

text \<open>If \<open>T\<close> and \<open>A\<close> are a correct load balancing for \<open>j\<close> jobs and \<open>m\<close> machines, then the processing time
      of any job \<open>x \<in> {1..j}\<close> is a lower bound for the load of some machine \<open>y \<in> {1..m}\<close>\<close>
lemma job_lower_bound_machine:
  assumes "lb T A j" "x \<in> {1..j}"
  shows "\<exists>y \<in> {1..m}. t x \<le> T y"
proof -
  note lbrules = lbE[OF assms(1)]
  have "\<exists>y \<in> {1..m}. x \<in> A y" using lbrules(2) assms(2) by blast
  then obtain y where y_def: "y \<in> {1..m}" "x \<in> A y" ..
  moreover have "finite (A y)" using assms(1) y_def(1) by simp
  ultimately have "t x \<le> (\<Sum>x \<in> A y. t x)" using lbrules(1) member_le_sum by fast
  also have "... = T y" using lbrules(3) y_def(1) by blast
  finally show ?thesis using y_def(1) by blast
qed

text \<open>As the load of any machine is a lower bound for the makespan, the processing time 
      of any job \<open>x \<in> {1..j}\<close> has to also be a lower bound for the makespan.
      Follows from @{thm [source] job_lower_bound_machine} and @{thm [source] makespan_correct}.\<close>
lemma job_lower_bound_makespan:
  assumes "lb T A j" "x \<in> {1..j}"
  shows "t x \<le> makespan T"
  by (meson job_lower_bound_machine[OF assms] makespan_correct(1) le_trans)

text \<open>The makespan over \<open>j\<close> jobs is a lower bound for the makespan of any correct load balancing for \<open>j\<close> jobs.\<close>
lemma max_job_lower_bound_makespan:
  assumes "lb T A j"
  shows "Max\<^sub>0 (t ` {1..j}) \<le> makespan T"
  using job_lower_bound_makespan[OF assms] by fastforce

lemma job_dist_lower_bound_makespan:
  assumes "lb T A j"
  shows "(\<Sum>x \<in> {1..j}. t x) / m \<le> makespan T"
proof -
  have "(\<Sum>x \<in> {1..j}. t x) \<le> m * makespan T"
    using assms lb_impl_job_sum[symmetric]
      and sum_le_card_Max[of "{1..m}"] m_gt_0 by (simp add: makespan_def')
  then have "real (\<Sum>x \<in> {1..j}. t x) \<le> real m * real (makespan T)"
    using of_nat_mono by fastforce
  then show ?thesis by (simp add: field_simps m_gt_0)
qed

subsection \<open>The Greedy Approximation Algorithm\<close>

text \<open>This function will perform a linear scan from \<open>k \<in> {1..m}\<close> and return the index of the machine with minimum load assuming \<open>m > 0\<close>\<close>
fun min\<^sub>k :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "min\<^sub>k T 0 = 1"
| "min\<^sub>k T (Suc x) =
   (let k = min\<^sub>k T x
    in if T (Suc x) < T k then (Suc x) else k)"

lemma min_correct:
  "\<forall>x \<in> {1..m}. T (min\<^sub>k T m) \<le> T x"
  by (induction m) (auto simp: Let_def le_Suc_eq, force)

lemma min_in_range:
  "k > 0 \<Longrightarrow> (min\<^sub>k T k) \<in> {1..k}"
  by (induction k) (auto simp: Let_def, force+)

lemma add_job:
  assumes "lb T A j" "x \<in> {1..m}"
  shows "lb (T (x := T x + t (Suc j))) (A (x := A x \<union> {Suc j})) (Suc j)"
    (is \<open>lb ?T ?A _\<close>)
proof -
  note lbrules = lbE[OF assms(1)]

  \<comment> \<open>Rule 1: @{term ?A} pairwise disjoint\<close>
  have NOTIN: "\<forall>i \<in> {1..m}. Suc j \<notin> A i" using lbrules(2) assms(2) by force
  with lbrules(1) have "\<forall>i \<in> {1..m}. i \<noteq> x \<longrightarrow> A i \<inter> (A x \<union> {Suc j}) = {}"
    using assms(2) by blast
  then have 1: "\<forall>x \<in> {1..m}. \<forall>y \<in> {1..m}. x \<noteq> y \<longrightarrow> ?A x \<inter> ?A y = {}"
    using lbrules(1) by simp

  \<comment> \<open>Rule 2: @{term ?A} contains all jobs\<close>
  have "(\<Union>y \<in> {1..m}. ?A y) = (\<Union>y \<in> {1..m}. A y) \<union> {Suc j}"
    using UNION_fun_upd assms(2) by auto
  also have "... = {1..Suc j}" unfolding lbrules(2) by auto
  finally have 2: "(\<Union>y \<in> {1..m}. ?A y) = {1..Suc j}" .

  \<comment> \<open>Rule 3: @{term ?A} sums to @{term ?T}\<close>
  have "(\<Sum>i \<in> ?A x. t i) = (\<Sum>i \<in> A x \<union> {Suc j}. t i)" by simp
  moreover have "A x \<inter> {Suc j} = {}" using NOTIN assms(2) by blast
  moreover have "finite (A x)" "finite {Suc j}" using assms by simp+
  ultimately have "(\<Sum>i \<in> ?A x. t i) = (\<Sum>i \<in> A x. t i) + (\<Sum>i \<in> {Suc j}. t i)"
    using sum.union_disjoint by simp
  also have "... = T x + t (Suc j)" using lbrules(3) assms(2) by simp
  finally have "(\<Sum>i \<in> ?A x. t i) = ?T x" by simp
  then have 3: "\<forall>i \<in> {1..m}. (\<Sum>j \<in> ?A i. t j) = ?T i"
    using lbrules(3) assms(2) by simp

  from lbI[OF 1 2 3] show ?thesis .
qed

lemma makespan_mono:
  "y \<le> T x \<Longrightarrow> makespan (T (x := y)) \<le> makespan T"
  "T x \<le> y \<Longrightarrow> makespan T \<le> makespan (T (x := y))"
  using f_Max\<^sub>0_mono by auto

lemma smaller_optimum:
  assumes "lb T A (Suc j)"
  shows "\<exists>T' A'. lb T' A' j \<and> makespan T' \<le> makespan T"
proof -
  note lbrules = lbE[OF assms]
  have "\<exists>x \<in> {1..m}. Suc j \<in> A x" using lbrules(2) by auto
  then obtain x where x_def: "x \<in> {1..m}" "Suc j \<in> A x" ..
  let ?T = "T (x := T x - t (Suc j))"
  let ?A = "A (x := A x - {Suc j})"

  \<comment> \<open>Rule 1: @{term ?A} pairwise disjoint\<close>
  from lbrules(1) have "\<forall>i \<in> {1..m}. i \<noteq> x \<longrightarrow> A i \<inter> (A x - {Suc j}) = {}"
    using x_def(1) by blast
  then have 1: "\<forall>x \<in> {1..m}. \<forall>y \<in> {1..m}. x \<noteq> y \<longrightarrow> ?A x \<inter> ?A y = {}"
    using lbrules(1) by auto

  \<comment> \<open>Rule 2: @{term ?A} contains all jobs\<close>
  have NOTIN: "\<forall>i \<in> {1..m}. i \<noteq> x \<longrightarrow> Suc j \<notin> A i" using lbrules(1) x_def by blast
  then have "(\<Union>y \<in> {1..m}. ?A y) = (\<Union>y \<in> {1..m}. A y) - {Suc j}"
    using UNION_fun_upd x_def by auto
  also have "... = {1..j}" unfolding lbrules(2) by auto
  finally have 2: "(\<Union>y \<in> {1..m}. ?A y) = {1..j}" .

  \<comment> \<open>Rule 3: @{term ?A} sums to @{term ?T}\<close>
  have "(\<Sum>i \<in> A x - {Suc j}. t i) = (\<Sum>i \<in> A x. t i) - t (Suc j)"
    by (simp add: sum_diff1_nat x_def(2))
  also have "... = T x - t (Suc j)" using lbrules(3) x_def(1) by simp
  finally have "(\<Sum>i \<in> ?A x. t i) = ?T x" by simp
  then have 3: "\<forall>i \<in> {1..m}. (\<Sum>j \<in> ?A i. t j) = ?T i"
    using lbrules(3) x_def(1) by simp

  \<comment> \<open>@{term makespan} is not larger\<close>
  have "lb ?T ?A j \<and> makespan ?T \<le> makespan T"
    using lbI[OF 1 2 3] makespan_mono(1) by force
  then show ?thesis by blast
qed

text \<open>If the processing time \<open>y\<close> does not contribute to the makespan, we can ignore it.\<close>
lemma remove_small_job:
  assumes "makespan (T (x := T x + y)) \<noteq> T x + y"
  shows   "makespan (T (x := T x + y)) = makespan T"
proof -
  let ?T = "T (x := T x + y)"
  have NOT_X: "makespan ?T \<noteq> ?T x" using assms(1) by simp
  then have "\<exists>i \<in> {1..m}. makespan ?T = ?T i \<and> i \<noteq> x"
    using makespan_correct(2) by metis
  then obtain i where i_def: "i \<in> {1..m}" "makespan ?T = ?T i" "i \<noteq> x" by blast
  then have "?T i = T i" using NOT_X by simp
  moreover from this have "makespan T = T i"
    by (metis i_def(1,2) antisym_conv le_add1 makespan_mono(2) makespan_correct(1))
  ultimately show ?thesis using i_def(2) by simp
qed

lemma greedy_makespan_no_jobs [simp]:
  "makespan (\<lambda>_. 0) = 0"
  using m_gt_0 by (simp add: makespan_def')

lemma min_avg: "m * T (min\<^sub>k T m) \<le> (\<Sum>i \<in> {1..m}. T i)"
           (is \<open>_ * ?T \<le> ?S\<close>)
proof -
  have "(\<Sum>_ \<in> {1..m}. ?T) \<le> ?S"
    using sum_mono[of \<open>{1..m}\<close> \<open>\<lambda>_. ?T\<close> T]
      and min_correct by blast
  then show ?thesis by simp
qed

definition inv\<^sub>1 :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat set) \<Rightarrow> nat \<Rightarrow> bool" where
  "inv\<^sub>1 T A j = (lb T A j \<and> j \<le> n \<and> (\<forall>T' A'. lb T' A' j \<longrightarrow> makespan T \<le> 2 * makespan T'))"

lemma inv\<^sub>1E:
  assumes "inv\<^sub>1 T A j"
  shows "lb T A j" "j \<le> n"
        "lb T' A' j \<Longrightarrow> makespan T \<le> 2 * makespan T'"
  using assms unfolding inv\<^sub>1_def by blast+

lemma inv\<^sub>1I:
  assumes "lb T A j" "j \<le> n" "\<forall>T' A'. lb T' A' j \<longrightarrow> makespan T \<le> 2 * makespan T'"
  shows "inv\<^sub>1 T A j" using assms unfolding inv\<^sub>1_def by blast

lemma inv\<^sub>1_step:
  assumes "inv\<^sub>1 T A j" "j < n"
  shows "inv\<^sub>1 (T ((min\<^sub>k T m) := T (min\<^sub>k T m) + t (Suc j)))
              (A ((min\<^sub>k T m) := A (min\<^sub>k T m) \<union> {Suc j})) (Suc j)"
    (is \<open>inv\<^sub>1 ?T ?A _\<close>)
proof -
  note invrules = inv\<^sub>1E[OF assms(1)]
  \<comment> \<open>Greedy is correct\<close>
  have LB: "lb ?T ?A (Suc j)"
    using add_job[OF invrules(1) min_in_range[OF m_gt_0]] by blast
  \<comment> \<open>Greedy maintains approximation factor\<close>
  have MK: "\<forall>T' A'. lb T' A' (Suc j) \<longrightarrow> makespan ?T \<le> 2 * makespan T'"
  proof rule+
    fix T\<^sub>1 A\<^sub>1 assume "lb T\<^sub>1 A\<^sub>1 (Suc j)"
    from smaller_optimum[OF this]
    obtain T\<^sub>0 A\<^sub>0 where "lb T\<^sub>0 A\<^sub>0 j" "makespan T\<^sub>0 \<le> makespan T\<^sub>1" by blast
    then have IH: "makespan T \<le> 2 * makespan T\<^sub>1"
      using invrules(3) by force
    show "makespan ?T \<le> 2 * makespan T\<^sub>1"
    proof (cases \<open>makespan ?T = T (min\<^sub>k T m) + t (Suc j)\<close>)
      case True
      have "m * T (min\<^sub>k T m) \<le> (\<Sum>i \<in> {1..m}. T i)" by (rule min_avg)
      also have "... = (\<Sum>i \<in> {1..j}. t i)" by (rule lb_impl_job_sum[OF invrules(1)])
      finally have "real m * T (min\<^sub>k T m) \<le> (\<Sum>i \<in> {1..j}. t i)"
        by (auto dest: of_nat_mono)
      with m_gt_0 have "T (min\<^sub>k T m) \<le> (\<Sum>i \<in> {1..j}. t i) / m"
        by (simp add: field_simps)
      then have "T (min\<^sub>k T m) \<le> makespan T\<^sub>1"
        using job_dist_lower_bound_makespan[OF \<open>lb T\<^sub>0 A\<^sub>0 j\<close>] 
          and \<open>makespan T\<^sub>0 \<le> makespan T\<^sub>1\<close> by linarith
      moreover have "t (Suc j) \<le> makespan T\<^sub>1"
        using job_lower_bound_makespan[OF \<open>lb T\<^sub>1 A\<^sub>1 (Suc j)\<close>] by simp
      ultimately show ?thesis unfolding True by simp
    next
      case False show ?thesis using remove_small_job[OF False] IH by simp
    qed
  qed
  from inv\<^sub>1I[OF LB _ MK] show ?thesis using assms(2) by simp
qed

lemma simple_greedy_approximation:
"VARS T A i j
{True}
T := (\<lambda>_. 0);
A := (\<lambda>_. {});
j := 0;
WHILE j < n INV {inv\<^sub>1 T A j} DO
  i := min\<^sub>k T m;
  j := (Suc j);
  A := A (i := A(i) \<union> {j});
  T := T (i := T(i) + t j)
OD
{lb T A n \<and> (\<forall>T' A'. lb T' A' n \<longrightarrow> makespan T \<le> 2 * makespan T')}"
proof (vcg, goal_cases)
  case (1 T A i j)
  then show ?case by (simp add: lb_def inv\<^sub>1_def)
next
  case (2 T A i j)
  then show ?case using inv\<^sub>1_step by simp
next
  case (3 T A i j)
  then show ?case unfolding inv\<^sub>1_def by force
qed

definition sorted :: "nat \<Rightarrow> bool" where
  "sorted j = (\<forall>x \<in> {1..j}. \<forall>y \<in> {1..x}. t x \<le> t y)"

lemma sorted_smaller [simp]: "\<lbrakk> sorted j; j \<ge> j' \<rbrakk> \<Longrightarrow> sorted j'"
  unfolding sorted_def by simp

lemma j_gt_m_pigeonhole:
  assumes "lb T A j" "j > m"
  shows "\<exists>x \<in> {1..j}. \<exists>y \<in> {1..j}. \<exists>z \<in> {1..m}. x \<noteq> y \<and> x \<in> A z \<and> y \<in> A z"
proof -
  have "\<forall>x \<in> {1..j}. \<exists>y \<in> {1..m}. x \<in> A y"
    using lbE(2)[OF assms(1)] by blast
  then have "\<exists>f. \<forall>x \<in> {1..j}. x \<in> A (f x) \<and> f x \<in> {1..m}" by metis
  then obtain f where f_def: "\<forall>x \<in> {1..j}. x \<in> A (f x) \<and> f x \<in> {1..m}" ..
  then have "card (f ` {1..j}) \<le> card {1..m}"
    by (meson card_mono finite_atLeastAtMost image_subset_iff)
  also have "... < card {1..j}" using assms(2) by simp
  finally have "card (f ` {1..j}) < card {1..j}" .
  then have "\<not> inj_on f {1..j}" using pigeonhole by blast
  then have "\<exists>x \<in> {1..j}. \<exists>y \<in> {1..j}. x \<noteq> y \<and> f x = f y"
    unfolding inj_on_def by blast
  then show ?thesis using f_def by metis
qed

text \<open>If \<open>T\<close> and \<open>A\<close> are a correct load balancing for \<open>j\<close> jobs and \<open>m\<close> machines with \<open>j > m\<close>,
      and the jobs are sorted in descending order, then there exists a machine \<open>x \<in> {1..m}\<close>
      whose load is at least twice as large as the processing time of job \<open>j\<close>.\<close>
lemma sorted_job_lower_bound_machine:
  assumes "lb T A j" "j > m" "sorted j"
  shows "\<exists>x \<in> {1..m}. 2 * t j \<le> T x"
proof -
  \<comment> \<open>Step 1: Obtaining the jobs\<close>
  note lbrules = lbE[OF assms(1)]
  obtain j\<^sub>1 j\<^sub>2 x where *:
    "j\<^sub>1 \<in> {1..j}" "j\<^sub>2 \<in> {1..j}" "x \<in> {1..m}" "j\<^sub>1 \<noteq> j\<^sub>2" "j\<^sub>1 \<in> A x" "j\<^sub>2 \<in> A x"
    using j_gt_m_pigeonhole[OF assms(1,2)] by blast

  \<comment> \<open>Step 2: Jobs contained in sum\<close>
  have "finite (A x)" using assms(1) *(3) by simp
  then have SUM: "(\<Sum>i \<in> A x. t i) = t j\<^sub>1 + t j\<^sub>2 + (\<Sum>i \<in> A x - {j\<^sub>1} - {j\<^sub>2}. t i)"
    using *(4-6) by (simp add: sum.remove)

  \<comment> \<open>Step 3: Proof of lower bound\<close>
  have "t j \<le> t j\<^sub>1" "t j \<le> t j\<^sub>2"
    using assms(3) *(1-2) unfolding sorted_def by auto
  then have "2 * t j \<le> t j\<^sub>1 + t j\<^sub>2" by simp
  also have "... \<le> (\<Sum>i \<in> A x. t i)" unfolding SUM by simp
  finally have "2 * t j \<le> T x" using lbrules(3) *(3) by simp
  then show ?thesis using *(3) by blast
qed

text \<open>Reasoning analogous to @{thm [source] job_lower_bound_makespan}.\<close>
lemma sorted_job_lower_bound_makespan:
  assumes "lb T A j" "j > m" "sorted j"
  shows "2 * t j \<le> makespan T"
proof -
  obtain x where x_def: "x \<in> {1..m}" "2 * t j \<le> T x"
    using sorted_job_lower_bound_machine[OF assms] ..
  with makespan_correct(1) have "T x \<le> makespan T" by blast
  with x_def(2) show ?thesis by simp
qed

lemma min_zero:
  assumes "x \<in> {1..k}" "T x = 0"
  shows "T (min\<^sub>k T k) = 0"
  using assms(1)
proof (induction k)
  case (Suc k)
  show ?case proof (cases \<open>x = Suc k\<close>)
    case True
    then show ?thesis using assms(2) by (simp add: Let_def)
  next
    case False
    with Suc have "T (min\<^sub>k T k) = 0" by simp
    then show ?thesis by simp
  qed
qed simp

lemma min_zero_index:
  assumes "x \<in> {1..k}" "T x = 0"
  shows "min\<^sub>k T k \<le> x"
  using assms(1)
proof (induction k)
  case (Suc k)
  show ?case proof (cases \<open>x = Suc k\<close>)
    case True
    then show ?thesis using min_in_range[of "Suc k"] by simp
  next
    case False
    with Suc.prems have "x \<in> {1..k}" by simp
    from min_zero[OF this, of T] assms(2) Suc.IH[OF this]
    show ?thesis by simp
  qed
qed simp

definition inv\<^sub>2 :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat set) \<Rightarrow> nat \<Rightarrow> bool" where
  "inv\<^sub>2 T A j = (lb T A j \<and> j \<le> n
                \<and> (\<forall>T' A'. lb T' A' j \<longrightarrow> makespan T \<le> 3 / 2 * makespan T') 
                \<and> (\<forall>x > j. T x = 0)
                \<and> (j \<le> m \<longrightarrow> makespan T = Max\<^sub>0 (t ` {1..j})))"

lemma inv\<^sub>2E:
  assumes "inv\<^sub>2 T A j"
  shows "lb T A j" "j \<le> n"
        "lb T' A' j \<Longrightarrow> makespan T \<le> 3 / 2 * makespan T'"
        "\<forall>x > j. T x = 0" "j \<le> m \<Longrightarrow> makespan T = Max\<^sub>0 (t ` {1..j})"
  using assms unfolding inv\<^sub>2_def by blast+

lemma inv\<^sub>2I:
  assumes "lb T A j" "j \<le> n"
          "\<forall>T' A'. lb T' A' j \<longrightarrow> makespan T \<le> 3 / 2 * makespan T'"
          "\<forall>x > j. T x = 0"
          "j \<le> m \<Longrightarrow> makespan T = Max\<^sub>0 (t ` {1..j})"
  shows "inv\<^sub>2 T A j"
  unfolding inv\<^sub>2_def using assms by blast

lemma inv\<^sub>2_step:
  assumes "sorted n" "inv\<^sub>2 T A j" "j < n"
  shows "inv\<^sub>2 (T (min\<^sub>k T m := T(min\<^sub>k T m) + t(Suc j)))
              (A (min\<^sub>k T m := A(min\<^sub>k T m) \<union> {Suc j})) (Suc j)"
    (is \<open>inv\<^sub>2 ?T ?A _\<close>)
proof (cases \<open>Suc j > m\<close>)
  case True note invrules = inv\<^sub>2E[OF assms(2)]
  \<comment> \<open>Greedy is correct\<close>
  have LB: "lb ?T ?A (Suc j)"
    using add_job[OF invrules(1) min_in_range[OF m_gt_0]] by blast
  \<comment> \<open>Greedy maintains approximation factor\<close>
  have MK: "\<forall>T' A'. lb T' A' (Suc j) \<longrightarrow> makespan ?T \<le> 3 / 2 * makespan T'"
  proof rule+
    fix T\<^sub>1 A\<^sub>1 assume "lb T\<^sub>1 A\<^sub>1 (Suc j)"
    from smaller_optimum[OF this]
    obtain T\<^sub>0 A\<^sub>0 where "lb T\<^sub>0 A\<^sub>0 j" "makespan T\<^sub>0 \<le> makespan T\<^sub>1" by blast
    then have IH: "makespan T \<le> 3 / 2 * makespan T\<^sub>1"
      using invrules(3) by force
    show "makespan ?T \<le> 3 / 2 * makespan T\<^sub>1"
    proof (cases \<open>makespan ?T = T (min\<^sub>k T m) + t (Suc j)\<close>)
      case True
      have "m * T (min\<^sub>k T m) \<le> (\<Sum>i \<in> {1..m}. T i)" by (rule min_avg)
      also have "... = (\<Sum>i \<in> {1..j}. t i)" by (rule lb_impl_job_sum[OF invrules(1)])
      finally have "real m * T (min\<^sub>k T m) \<le> (\<Sum>i \<in> {1..j}. t i)"
        by (auto dest: of_nat_mono)
      with m_gt_0 have "T (min\<^sub>k T m) \<le> (\<Sum>i \<in> {1..j}. t i) / m"
        by (simp add: field_simps)
      then have "T (min\<^sub>k T m) \<le> makespan T\<^sub>1"
        using job_dist_lower_bound_makespan[OF \<open>lb T\<^sub>0 A\<^sub>0 j\<close>] 
          and \<open>makespan T\<^sub>0 \<le> makespan T\<^sub>1\<close> by linarith
      moreover have "2 * t (Suc j) \<le> makespan T\<^sub>1"
        using sorted_job_lower_bound_makespan[OF \<open>lb T\<^sub>1 A\<^sub>1 (Suc j)\<close> \<open>Suc j > m\<close>]
          and assms(1,3) by simp
      ultimately show ?thesis unfolding True by simp
    next
      case False show ?thesis using remove_small_job[OF False] IH by simp
    qed
  qed
  have "\<forall>x > Suc j. ?T x = 0"
    using invrules(4) min_in_range[OF m_gt_0, of T] True by simp
  with inv\<^sub>2I[OF LB _ MK] show ?thesis using assms(3) True by simp
next
  case False
  then have IN_RANGE: "Suc j \<in> {1..m}" by simp
  note invrules = inv\<^sub>2E[OF assms(2)]
  then have "T (Suc j) = 0" by blast

  \<comment> \<open>Greedy is correct\<close>
  have LB: "lb ?T ?A (Suc j)"
    using add_job[OF invrules(1) min_in_range[OF m_gt_0]] by blast

  \<comment> \<open>Greedy is trivially optimal\<close>
  from IN_RANGE \<open>T (Suc j) = 0\<close> have "min\<^sub>k T m \<le> Suc j"
    using min_zero_index by blast
  with invrules(4) have EMPTY: "\<forall>x > Suc j. ?T x = 0" by simp
  from IN_RANGE \<open>T (Suc j) = 0\<close> have "T (min\<^sub>k T m) = 0"
    using min_zero by blast
  with fun_upd_f_Max\<^sub>0[OF min_in_range[OF m_gt_0]] invrules(5) False
  have TRIV: "makespan ?T = Max\<^sub>0 (t ` {1..Suc j})" unfolding f_Max\<^sub>0_equiv[symmetric] by simp
  have MK: "\<forall>T' A'. lb T' A' (Suc j) \<longrightarrow> makespan ?T \<le> 3 / 2 * makespan T'"
    by (auto simp: TRIV[folded f_Max\<^sub>0_equiv]
            dest!: max_job_lower_bound_makespan[folded f_Max\<^sub>0_equiv])

  from inv\<^sub>2I[OF LB _ MK EMPTY TRIV] show ?thesis using assms(3) by simp
qed

lemma sorted_greedy_approximation:
"sorted n \<Longrightarrow> VARS T A i j
{True}
T := (\<lambda>_. 0);
A := (\<lambda>_. {});
j := 0;
WHILE j < n INV {inv\<^sub>2 T A j} DO
  i := min\<^sub>k T m;
  j := (Suc j);
  A := A (i := A(i) \<union> {j});
  T := T (i := T(i) + t j)
OD
{lb T A n \<and> (\<forall>T' A'. lb T' A' n \<longrightarrow> makespan T \<le> 3 / 2 * makespan T')}"
proof (vcg, goal_cases)
  case (1 T A i j)
  then show ?case by (simp add: lb_def inv\<^sub>2_def)
next
  case (2 T A i j)
  then show ?case using inv\<^sub>2_step by simp
next
  case (3 T A i j)
  then show ?case unfolding inv\<^sub>2_def by force
qed

end (* LoadBalancing *)

end (* Theory *)