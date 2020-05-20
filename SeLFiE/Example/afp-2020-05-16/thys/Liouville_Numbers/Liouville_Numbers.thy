(* 
  File:    Liouville_Numbers.thy
  Author:  Manuel Eberl <eberlm@in.tum.de>

  The definition of Liouville numbers and their standard construction, plus the proof
  that any Liouville number is transcendental.
*)

theory Liouville_Numbers
imports 
  Complex_Main
  "HOL-Computational_Algebra.Polynomial"
  Liouville_Numbers_Misc
begin

(* 
  TODO: Move definition of algebraic numbers out of Algebraic_Numbers to reduce unnecessary
  dependencies.
*)

text \<open>
A Liouville number is a real number that can be approximated well -- but not perfectly -- 
by a sequence of rational numbers. ``Well``, in this context, means that the error of the
 $n$-th rational in the sequence is bounded by the $n$-th power of its denominator.

Our approach will be the following:
\begin{itemize}
\item Liouville numbers cannot be rational.
\item Any irrational algebraic number cannot be approximated in the Liouville sense
\item Therefore, all Liouville numbers are transcendental.
\item The standard construction fulfils all the properties of Liouville numbers.
\end{itemize}
\<close>

subsection \<open>Definition of Liouville numbers\<close>

text \<open>
  The following definitions and proofs are largely adapted from those in the Wikipedia
  article on Liouville numbers.~\cite{wikipedia}
\<close>

text \<open>
  A Liouville number is a real number that can be approximated well -- but not perfectly --
  by a sequence of rational numbers. The error of the $n$-th term $\frac{p_n}{q_n}$ is at most
  $q_n^{-n}$, where $p_n\in\isasymint$ and $q_n \in\isasymint_{\geq 2}$.

  We will say that such a number can be approximated in the Liouville sense.
\<close>
locale liouville =
  fixes x :: real and p q :: "nat \<Rightarrow> int"
  assumes approx_int_pos: "abs (x - p n / q n) > 0" 
      and denom_gt_1:     "q n > 1"
      and approx_int:     "abs (x - p n / q n) < 1 / of_int (q n) ^ n"

text \<open>
  First, we show that any Liouville number is irrational.
\<close>
lemma (in liouville) irrational: "x \<notin> \<rat>"
proof
  assume "x \<in> \<rat>"
  then obtain c d :: int where d: "x = of_int c / of_int d" "d > 0" 
    by (elim Rats_cases') simp
  define n where "n = Suc (nat \<lceil>log 2 d\<rceil>)"
  note q_gt_1 = denom_gt_1[of n]

  have neq: "c * q n \<noteq> d * p n"
  proof
    assume "c * q n = d * p n"
    hence "of_int (c * q n) = of_int (d * p n)" by (simp only: )
    with approx_int_pos[of n] d q_gt_1 show False by (auto simp: field_simps)
  qed
  hence abs_pos: "0 < abs (c * q n - d * p n)" by simp

  from q_gt_1 d have "of_int d = 2 powr log 2 d" by (subst powr_log_cancel) simp_all
  also from d have "log 2 (of_int d) \<ge> log 2 1" by (subst log_le_cancel_iff) simp_all
  hence "2 powr log 2 d \<le> 2 powr of_nat (nat \<lceil>log 2 d\<rceil>)" 
    by (intro powr_mono) simp_all
  also have "\<dots> = of_int (2 ^ nat \<lceil>log 2 d\<rceil>)"
    by (subst powr_realpow) simp_all
  finally have "d \<le> 2 ^ nat \<lceil>log 2 (of_int d)\<rceil>" 
    by (subst (asm) of_int_le_iff)
  also have "\<dots> * q n \<le> q n ^ Suc (nat \<lceil>log 2 (of_int d)\<rceil>)" 
    by (subst power_Suc, subst mult.commute, intro mult_left_mono power_mono, 
        insert q_gt_1) simp_all
  also from q_gt_1 have "\<dots> = q n ^ n" by (simp add: n_def)
  finally have "1 / of_int (q n ^ n) \<le> 1 / real_of_int (d * q n)" using q_gt_1 d
    by (intro divide_left_mono Rings.mult_pos_pos of_int_pos, subst of_int_le_iff) simp_all
  also have "\<dots> \<le> of_int (abs (c * q n - d * p n)) / real_of_int (d * q n)" using q_gt_1 d abs_pos
    by (intro divide_right_mono) (linarith, simp)
  also have "\<dots> = abs (x - of_int (p n) / of_int (q n))" using q_gt_1 d(2) 
    by (simp_all add: divide_simps d(1) mult_ac)
  finally show False using approx_int[of n] by simp
qed


text \<open>
  Next, any irrational algebraic number cannot be approximated with rational 
  numbers in the Liouville sense.
\<close>
lemma liouville_irrational_algebraic:
  fixes x :: real
  assumes irrationsl: "x \<notin> \<rat>" and "algebraic x"
  obtains c :: real and n :: nat
    where "c > 0" and "\<And>(p::int) (q::int). q > 0 \<Longrightarrow> abs (x - p / q) > c / of_int q ^ n"
proof -
  from \<open>algebraic x\<close> guess p by (elim algebraicE) note p = this
  define n where "n = degree p"

  \<comment> \<open>The derivative of @{term p} is bounded within @{term "{x-1..x+1}"}.\<close>
  let ?f = "\<lambda>t. \<bar>poly (pderiv p) t\<bar>"
  define M where "M = (SUP t\<in>{x-1..x+1}. ?f t)"
  define roots where "roots = {x. poly p x = 0} - {x}"

  define A_set where "A_set = {1, 1/M} \<union> {abs (x' - x) |x'. x' \<in> roots}"
  define A' where "A' = Min A_set"
  define A  where "A = A' / 2"
  \<comment> \<open>We define @{term A} to be a positive real number that is less than @{term 1}, 
      @{term "1/M"} and any distance from @{term x} to another root of @{term p}.\<close>

  \<comment> \<open>Properties of @{term M}, our upper bound for the derivative of @{term p}:\<close>
  have "\<exists>s\<in>{x-1..x+1}. \<forall>y\<in>{x-1..x+1}. ?f s \<ge> ?f y"
    by (intro continuous_attains_sup) (auto intro!: continuous_intros)
  hence bdd: "bdd_above (?f ` {x-1..x+1})" by auto
  
  have M_pos: "M > 0"
  proof -
    from p have "pderiv p \<noteq> 0" by (auto dest!: pderiv_iszero)
    hence "finite {x. poly (pderiv p) x = 0}" using poly_roots_finite by blast
    moreover have "\<not>finite {x-1..x+1}" by (simp add: infinite_Icc)
    ultimately have "\<not>finite ({x-1..x+1} - {x. poly (pderiv p) x = 0})" by simp
    hence "{x-1..x+1} - {x. poly (pderiv p) x = 0} \<noteq> {}" by (intro notI) simp
    then obtain t where t: "t \<in> {x-1..x+1}" and "poly (pderiv p) t \<noteq> 0" by blast
    hence "0 < ?f t" by simp
    also from t and bdd have "\<dots> \<le> M" unfolding M_def by (rule cSUP_upper)
    finally show "M > 0" .
  qed

  have M_sup: "?f t \<le> M" if "t \<in> {x-1..x+1}" for t
  proof -
    from that and bdd show "?f t \<le> M"
      unfolding M_def by (rule cSUP_upper)
  qed


  \<comment> \<open>Properties of @{term A}:\<close>
  from p poly_roots_finite[of p] have "finite A_set" 
    unfolding A_set_def roots_def by simp
  have "x \<notin> roots" unfolding roots_def by auto
  hence "A' > 0" using Min_gr_iff[OF \<open>finite A_set\<close>, folded A'_def, of 0]
    by (auto simp: A_set_def M_pos)
  hence A_pos: "A > 0" by (simp add: A_def)
  
  from \<open>A' > 0\<close> have "A < A'" by (simp add: A_def)
  moreover from Min_le[OF \<open>finite A_set\<close>, folded A'_def] 
    have "A' \<le> 1" "A' \<le> 1/M" "\<And>x'. x' \<noteq> x \<Longrightarrow> poly p x' = 0 \<Longrightarrow> A' \<le> abs (x' - x)"
    unfolding A_set_def roots_def by auto
  ultimately have A_less: "A < 1" "A < 1/M" "\<And>x'. x' \<noteq> x \<Longrightarrow> poly p x' = 0 \<Longrightarrow> A < abs (x' - x)"
    by fastforce+


  \<comment> \<open>Finally: no rational number can approximate @{term x} ``well enough''.\<close>
  have "\<forall>(a::int) (b :: int). b > 0 \<longrightarrow> \<bar>x - of_int a / of_int b\<bar> > A / of_int b ^ n"
  proof (intro allI impI, rule ccontr)
    fix a b :: int
    assume b: "b > 0" and "\<not>(A / of_int b ^ n < \<bar>x - of_int a / of_int b\<bar>)"
    hence ab: "abs (x - of_int a / of_int b) \<le> A / of_int b ^ n" by simp
    also from A_pos b have "A / of_int b ^ n \<le> A / 1"
      by (intro divide_left_mono) simp_all
    finally have ab': "abs (x - a / b) \<le> A" by simp
    also have "\<dots> \<le> 1" using A_less by simp
    finally have ab'': "a / b \<in> {x-1..x+1}" by auto
    
    have no_root: "poly p (a / b) \<noteq> 0" 
    proof
      assume "poly p (a / b) = 0"
      moreover from \<open>x \<notin> \<rat>\<close> have "x \<noteq> a / b" by auto
      ultimately have "A < abs (a / b - x)" using A_less(3) by simp
      with ab' show False by simp
    qed

    have "\<exists>x0\<in>{x-1..x+1}. poly p (a / b) - poly p x = (a / b - x) * poly (pderiv p) x0"
      using ab'' by (intro poly_MVT') (auto simp: min_def max_def)
    with p obtain x0 :: real where x0:
        "x0 \<in> {x-1..x+1}" "poly p (a / b) = (a / b - x) * poly (pderiv p) x0" by auto

    from x0(2) no_root have deriv_pos: "poly (pderiv p) x0 \<noteq> 0" by auto

    from b p no_root have p_ab: "abs (poly p (a / b)) \<ge> 1 / of_int b ^ n"
      unfolding n_def by (intro int_poly_rat_no_root_ge)

    note ab
    also from A_less b have "A / of_int b ^ n < (1/M) / of_int b ^ n"
      by (intro divide_strict_right_mono) simp_all
    also have "\<dots> = (1 / b ^ n) / M" by simp
    also from M_pos ab p_ab have "\<dots> \<le> abs (poly p (a / b)) / M"
      by (intro divide_right_mono) simp_all
    also from deriv_pos M_pos x0(1)
      have "\<dots> \<le> abs (poly p (a / b)) / abs (poly (pderiv p) x0)"
      by (intro divide_left_mono M_sup) simp_all
    also have "\<bar>poly p (a / b)\<bar> = \<bar>a / b - x\<bar> * \<bar>poly (pderiv p) x0\<bar>"
      by (subst x0(2)) (simp add: abs_mult)
    with deriv_pos have "\<bar>poly p (a / b)\<bar> / \<bar>poly (pderiv p) x0\<bar> = \<bar>x - a / b\<bar>" 
      by (subst nonzero_divide_eq_eq) simp_all
    finally show False by simp 
  qed
  with A_pos show ?thesis using that[of A n] by blast
qed


text \<open>
  Since Liouville numbers are irrational, but can be approximated well by rational 
  numbers in the Liouville sense, they must be transcendental.
\<close>
lemma (in liouville) transcendental: "\<not>algebraic x"
proof
  assume "algebraic x"
  from liouville_irrational_algebraic[OF irrational this] guess c n . note cn = this
  
  define r where "r = nat \<lceil>log 2 (1 / c)\<rceil>"
  define m where "m = n + r"
  from cn(1) have "(1/c) = 2 powr log 2 (1/c)" by (subst powr_log_cancel) simp_all
  also have "log 2 (1/c) \<le> of_nat (nat \<lceil>log 2 (1/c)\<rceil>)" by linarith
  hence "2 powr log 2 (1/c) \<le> 2 powr \<dots>" by (intro powr_mono) simp_all
  also have "\<dots> = 2 ^ r" unfolding r_def by (simp add: powr_realpow)
  finally have "1 / (2^r) \<le> c" using cn(1) by (simp add: field_simps)

  have "abs (x - p m / q m) < 1 / of_int (q m) ^ m" by (rule approx_int)
  also have "\<dots> = (1 / of_int (q m) ^ r) * (1 / real_of_int (q m) ^ n)"
    by (simp add: m_def power_add)
  also from denom_gt_1[of m] have "1 / real_of_int (q m) ^ r \<le> 1 / 2 ^ r"
    by (intro divide_left_mono power_mono) simp_all
  also have "\<dots> \<le> c" by fact
  finally have "abs (x - p m / q m) < c / of_int (q m) ^ n"
    using denom_gt_1[of m] by - (simp_all add: divide_right_mono)
  with cn(2)[of "q m" "p m"] denom_gt_1[of m] show False by simp
qed


subsection \<open>Standard construction for Liouville numbers\<close>

text \<open>
  We now define the standard construction for Liouville numbers.
\<close>
definition standard_liouville :: "(nat \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> real" where
  "standard_liouville p q = (\<Sum>k. p k / of_int q ^ fact (Suc k))"

lemma standard_liouville_summable:
  fixes p :: "nat \<Rightarrow> int" and q :: int
  assumes "q > 1" "range p \<subseteq> {0..<q}"
  shows   "summable (\<lambda>k. p k / of_int q ^ fact (Suc k))"
proof (rule summable_comparison_test')
  from assms(1) show "summable (\<lambda>n. (1 / q) ^ n)"
    by (intro summable_geometric) simp_all
next
  fix n :: nat
  from assms have "p n \<in> {0..<q}" by blast
  with assms(1) have "norm (p n / of_int q ^ fact (Suc n)) \<le> 
                        q / of_int q ^ (fact (Suc n))" by (auto simp: field_simps)
  also from assms(1) have "\<dots> = 1 / of_int q ^ (fact (Suc n) - 1)" 
    by (subst power_diff) (auto simp del: fact_Suc)
  also have "Suc n \<le> fact (Suc n)" by (rule fact_ge_self)
  with assms(1) have "1 / real_of_int q ^ (fact (Suc n) - 1) \<le> 1 / of_int q ^ n"
    by (intro divide_left_mono power_increasing)
       (auto simp del: fact_Suc simp add: algebra_simps)
  finally show "norm (p n / of_int q ^ fact (Suc n)) \<le> (1 / q) ^ n"
    by (simp add: power_divide)
qed

lemma standard_liouville_sums:
  assumes "q > 1" "range p \<subseteq> {0..<q}"
  shows   "(\<lambda>k. p k / of_int q ^ fact (Suc k)) sums standard_liouville p q"
  using standard_liouville_summable[OF assms] unfolding standard_liouville_def 
  by (simp add: summable_sums)


text \<open>
  Now we prove that the standard construction indeed yields Liouville numbers.
\<close>
lemma standard_liouville_is_liouville:
  assumes "q > 1" "range p \<subseteq> {0..<q}" "frequently (\<lambda>n. p n \<noteq> 0) sequentially"
  defines "b \<equiv> \<lambda>n. q ^ fact (Suc n)"
  defines "a \<equiv> \<lambda>n. (\<Sum>k\<le>n. p k * q ^ (fact (Suc n) - fact (Suc k)))"
  shows   "liouville (standard_liouville p q) a b"
proof
  fix n :: nat
  from assms(1) have "1 < q ^ 1" by simp
  also from assms(1) have "\<dots> \<le> b n" unfolding b_def 
    by (intro power_increasing) (simp_all del: fact_Suc)
  finally show "b n > 1" .

  note summable = standard_liouville_summable[OF assms(1,2)]
  let ?S = "\<Sum>k. p (k + n + 1) / of_int q ^ (fact (Suc (k + n + 1)))"
  let ?C = "(q - 1) / of_int q ^ (fact (n+2))"

  have "a n / b n = (\<Sum>k\<le>n. p k * (of_int q ^ (fact (n+1) - fact (k+1)) / of_int q ^ (fact (n+1))))"
    by (simp add: a_def b_def sum_divide_distrib of_int_sum)
  also have "\<dots> = (\<Sum>k\<le>n. p k / of_int q ^ (fact (Suc k)))"
    by (intro sum.cong refl, subst inverse_divide [symmetric], subst power_diff [symmetric])
       (insert assms(1), simp_all add: divide_simps fact_mono_nat del: fact_Suc)
  also have "standard_liouville p q - \<dots> = ?S" unfolding standard_liouville_def
    by (subst diff_eq_eq) (intro suminf_split_initial_segment' summable)
  finally have "abs (standard_liouville p q - a n / b n) = abs ?S" by (simp only: )
  moreover from assms have "?S \<ge> 0" 
    by (intro suminf_nonneg allI divide_nonneg_pos summable_ignore_initial_segment summable) force+
  ultimately have eq: "abs (standard_liouville p q - a n / b n) = ?S" by simp

  also have "?S \<le> (\<Sum>k. ?C * (1 / q) ^ k)"
  proof (intro suminf_le allI summable_ignore_initial_segment summable)
    from assms show "summable (\<lambda>k. ?C * (1 / q) ^ k)"
      by (intro summable_mult summable_geometric) simp_all
  next
    fix k :: nat
    from assms have "p (k + n + 1) \<le> q - 1" by force
    with \<open>q > 1\<close> have "p (k + n + 1) / of_int q ^ fact (Suc (k + n + 1)) \<le> 
                         (q - 1) / of_int q ^ (fact (Suc (k + n + 1)))"
      by (intro divide_right_mono) (simp_all del: fact_Suc)
    also from \<open>q > 1\<close> have "\<dots> \<le> (q - 1) / of_int q ^ (fact (n+2) + k)"
      using fact_ineq[of "n+2" k]
      by (intro divide_left_mono power_increasing) (simp_all add: add_ac)
    also have "\<dots> = ?C * (1 / q) ^ k" 
      by (simp add: field_simps power_add del: fact_Suc)
    finally show "p (k + n + 1) / of_int q ^ fact (Suc (k + n + 1)) \<le> \<dots>" .
  qed
  also from assms have "\<dots> = ?C * (\<Sum>k. (1 / q) ^ k)"
    by (intro suminf_mult summable_geometric) simp_all
  also from assms have "(\<Sum>k. (1 / q) ^ k) = 1 / (1 - 1 / q)"
    by (intro suminf_geometric) simp_all
  also from assms(1) have "?C * \<dots> = of_int q ^ 1 / of_int q ^ fact (n + 2)" 
    by (simp add: field_simps)
  also from assms(1) have "\<dots> \<le> of_int q ^ fact (n + 1) / of_int q ^ fact (n + 2)"
    by (intro divide_right_mono power_increasing) (simp_all add: field_simps del: fact_Suc)
  also from assms(1) have "\<dots> = 1 / (of_int q ^ (fact (n + 2) - fact (n + 1)))" 
    by (subst power_diff) simp_all
  also have "fact (n + 2) - fact (n + 1) = (n + 1) * fact (n + 1)" by (simp add: algebra_simps)
  also from assms(1) have "1 / (of_int q ^ \<dots>) < 1 / (real_of_int q ^ (fact (n + 1) * n))"
    by (intro divide_strict_left_mono power_increasing mult_right_mono) simp_all
  also have "\<dots> = 1 / of_int (b n) ^ n" 
    by (simp add: power_mult b_def power_divide del: fact_Suc)
  finally show "\<bar>standard_liouville p q - a n / b n\<bar> < 1 / of_int (b n) ^ n" .

  from assms(3) obtain k where k: "k \<ge> n + 1" "p k \<noteq> 0" 
    by (auto simp: frequently_def eventually_at_top_linorder)
  define k' where "k' = k - n - 1"
  from assms k have "p k \<ge> 0" by force
  with k assms have k': "p (k' + n + 1) > 0" unfolding k'_def by force
  with assms(1,2) have "?S > 0"
    by (intro suminf_pos2[of _ k'] summable_ignore_initial_segment summable) 
       (force intro!: divide_pos_pos divide_nonneg_pos)+
  with eq show "\<bar>standard_liouville p q - a n / b n\<bar> > 0" by (simp only: )
qed


text \<open>
  We can now show our main result: any standard Liouville number is transcendental.
\<close>
theorem transcendental_standard_liouville:
  assumes "q > 1" "range p \<subseteq> {0..<q}" "frequently (\<lambda>k. p k \<noteq> 0) sequentially"
  shows   "\<not>algebraic (standard_liouville p q)"
proof -
  from assms interpret 
    liouville "standard_liouville p q" 
              "\<lambda>n. (\<Sum>k\<le>n. p k * q ^ (fact (Suc n) - fact (Suc k)))" 
              "\<lambda>n. q ^ fact (Suc n)" 
    by (rule standard_liouville_is_liouville)
  from transcendental show ?thesis .
qed

text \<open>
  In particular: The the standard construction for constant sequences, such as the
  ``classic'' Liouville constant $\sum_{n=1}^\infty 10^{-n!} = 0.11000100\ldots$,
  are transcendental. 

  This shows that Liouville numbers exists and therefore gives a concrete and 
  elementary proof that transcendental numbers exist.
\<close>
corollary transcendental_standard_standard_liouville:
  "a \<in> {0<..<b} \<Longrightarrow> \<not>algebraic (standard_liouville (\<lambda>_. int a) (int b))"
  by (intro transcendental_standard_liouville) auto

corollary transcendental_liouville_constant:
  "\<not>algebraic (standard_liouville (\<lambda>_. 1) 10)"
  by (intro transcendental_standard_liouville) auto

end
