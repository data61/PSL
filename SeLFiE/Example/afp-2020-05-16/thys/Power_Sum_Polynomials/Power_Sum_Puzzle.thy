(*
  File:     Power_Sum_Puzzle.thy
  Author:   Manuel Eberl, TU München
*)
section \<open>Power sum puzzles\<close>
theory Power_Sum_Puzzle
imports
  Power_Sum_Polynomials
  "Polynomial_Factorization.Rational_Root_Test"
begin

subsection \<open>General setting and results\<close>

text \<open>
  We now consider the following situation: Given unknown complex numbers $x_1,\ldots,x_n$,
  define $p_k = x_1^k + \ldots + x_n^k$. Also, define $e_k := e_k(x_1,\ldots,x_n)$ where
  $e_k(X_1,\ldots,X_n)$ is the $k$-th elementary symmetric polynomial.

  What is the relationship between the sequences $e_k$ and $p_k$; in particular,
  how can we determine one from the other?
\<close>
locale power_sum_puzzle =
  fixes x :: "nat \<Rightarrow> complex"
  fixes n :: nat
begin

text \<open>
  We first introduce the notation $p_k := x_1 ^ k + \ldots + x_n ^ k$:
\<close>
definition p where "p k = (\<Sum>i<n. x i ^ k)"

lemma p_0 [simp]: "p 0 = of_nat n"
  by (simp add: p_def)

lemma p_altdef: "p k = insertion x (powsum_mpoly {..<n} k)"
  by (simp add: p_def)

text \<open>
  Similarly, we introduce the notation $e_k = e_k(x_1,\ldots, x_n)$ where
  $e_k(X_1,\ldots,X_n)$ is the $k$-th elementary symmetric polynomial (i.\,e. the sum of
  all monomials that can be formed by taking the product of exactly $k$ distinct variables).
\<close>
definition e where "e k = (\<Sum>Y | Y \<subseteq> {..<n} \<and> card Y = k. prod x Y)"

lemma e_altdef: "e k = insertion x (sym_mpoly {..<n} k)"
  by (simp add: e_def insertion_sym_mpoly)

text \<open>
  It is clear that $e_k$ vanishes for $k > n$.
\<close>
lemma e_eq_0 [simp]: "k > n \<Longrightarrow> e k = 0"
  by (simp add: e_altdef)

lemma e_0 [simp]: "e 0 = 1"
  by (simp add: e_altdef)


text \<open>
  The recurrences we got from the Girard--Newton Theorem earlier now directly give us
  analogous recurrences for $e_k$ and $p_k$:
\<close>
lemma e_recurrence:
  assumes k: "k > 0"
  shows   "e k = -(\<Sum>i=1..k. (- 1) ^ i * e (k - i) * p i) / of_nat k"
  using assms unfolding e_altdef p_altdef
  by (subst sym_mpoly_recurrence)
     (auto simp: insertion_sum insertion_add insertion_mult insertion_power insertion_sym_mpoly)

lemma p_recurrence:
  assumes k: "k > 0"
  shows   "p k = -of_nat k * (-1) ^ k * e k - (\<Sum>i=1..<k. (-1) ^ i * e i * p (k - i))"
  using assms unfolding e_altdef p_altdef
  by (subst powsum_mpoly_recurrence)
     (auto simp: insertion_sum insertion_add insertion_mult insertion_diff 
                 insertion_power insertion_sym_mpoly)

lemma p_recurrence'':
  assumes k: "k > n"
  shows   "p k = -(\<Sum>i=1..n. (-1) ^ i * e i * p (k - i))"
  using assms unfolding e_altdef p_altdef
  by (subst powsum_mpoly_recurrence')
     (auto simp: insertion_sum insertion_add insertion_mult insertion_diff 
                 insertion_power insertion_sym_mpoly)


text \<open>
  It is clear from this recurrence that if $p_1$ to $p_n$ are rational, then so are the $e_k$:
\<close>
lemma e_in_Rats:
  assumes "\<And>k. k \<in> {1..n} \<Longrightarrow> p k \<in> \<rat>"
  shows   "e k \<in> \<rat>"
proof (cases "k \<le> n")
  case True
  thus ?thesis
  proof (induction k rule: less_induct)
    case (less k)
    show ?case
    proof (cases "k = 0")
      case False
      thus ?thesis using assms less
        by (subst e_recurrence) (auto intro!: Rats_divide)
    qed auto
  qed
qed auto

text \<open>
  Analogously, if $p_1$ to $p_n$ are rational, then so are all the other $p_k$:
\<close>
lemma p_in_Rats:
  assumes "\<And>k. k \<in> {1..n} \<Longrightarrow> p k \<in> \<rat>"
  shows   "p k \<in> \<rat>"
proof (induction k rule: less_induct)
  case (less k)
  consider "k = 0" | "k \<in> {1..n}" | "k > n"
    by force
  thus ?case
  proof cases
    assume "k > n"
    thus ?thesis
      using less assms by (subst p_recurrence'') (auto intro!: sum_in_Rats Rats_mult e_in_Rats)
  qed (use assms in auto)
qed


text \<open>
  Next, we define the unique monic polynomial that has $x_1, \ldots, x_n$ as its roots
  (respecting multiplicity):
\<close>
definition Q :: "complex poly" where "Q = (\<Prod>i<n. [:-x i, 1:])"

lemma degree_Q [simp]: "Polynomial.degree Q = n"
  by (simp add: Q_def degree_prod_eq_sum_degree)

lemma lead_coeff_Q [simp]: "Polynomial.coeff Q n = 1"
  using monic_prod[of "{..<n}" "\<lambda>i. [:-x i, 1:]"]
  by (simp add: Q_def degree_prod_eq_sum_degree)

text \<open>
  By Vieta's Theorem, we then have:
  \[Q(X) = \sum_{k=0}^n (-1)^{n-k} e_{n-k} X^k\]
  In other words: The above allows us to determine the $x_1, \ldots, x_n$ explicitly.
  They are, in fact, precisely the roots of the above polynomial (respecting multiplicity).
  Since this polynomial depends only on the $e_k$, which are in turn determined by
  $p_1, \ldots, p_n$, this means that these are the \<^emph>\<open>only\<close> solutions of this puzzle
  (up to permutation of the $x_i$).
\<close>
lemma coeff_Q: "Polynomial.coeff Q k = (if k > n then 0 else (-1) ^ (n - k) * e (n - k))"
proof (cases "k \<le> n")
  case True
  thus ?thesis
    using coeff_poly_from_roots[of "{..<n}" k x] by (auto simp: Q_def e_def)
qed (auto simp: Polynomial.coeff_eq_0)

lemma Q_altdef: "Q = (\<Sum>k\<le>n. Polynomial.monom ((-1) ^ (n - k) * e (n - k)) k)"
  by (subst poly_as_sum_of_monoms [symmetric]) (simp add: coeff_Q)

text \<open>
  The following theorem again shows that $x_1, \ldots, x_n$ are precisely the roots
  of \<^term>\<open>Q\<close>, respecting multiplicity.
\<close>
theorem mset_x_eq_poly_roots_Q: "{#x i. i \<in># mset_set {..<n}#} = poly_roots Q"
proof -
  have "poly_roots Q = (\<Sum>i<n. {#x i#})"
    by (simp add: Q_def poly_roots_prod)
  also have "\<dots> = {#x i. i \<in># mset_set {..<n}#}"
    by (induction n) (auto simp: lessThan_Suc)
  finally show ?thesis ..
qed

end


subsection \<open>Existence of solutions\<close>

text \<open>
  So far, we have assumed a solution to the puzzle and then shown the properties that this
  solution must fulfil. However, we have not yet shown that there \<^emph>\<open>is\<close> a solution.
  We will do that now.

  Let $n$ be a natural number and $f_k$ some sequence of complex numbers. We will show that 
  there are $x_1, \ldots, x_n$ so that $x_1 ^ k + \ldots + x_n ^ k = f_k$ for any $1\leq k\leq n$.
\<close>
locale power_sum_puzzle_existence =
  fixes f :: "nat \<Rightarrow> complex" and n :: nat
begin

text \<open>
  First, we define a sequence of numbers \<open>e'\<close> analogously to the sequence \<open>e\<close> before,
  except that we replace all occurrences of the power sum $p_k$ with $f_k$ (recall that in the end
  we want $p_k = f_k$).
\<close>
fun e' :: "nat \<Rightarrow> complex"
  where "e' k = (if k = 0 then 1 else if k > n then 0
                 else -(\<Sum>i=1..k. (-1) ^ i * e' (k - i) * f i) / of_nat k)"

lemmas [simp del] = e'.simps

lemma e'_0 [simp]: "e' 0 = 1"
  by (simp add: e'.simps)

lemma e'_eq_0 [simp]: "k > n \<Longrightarrow> e' k = 0"
  by (auto simp: e'.simps)

text \<open>
  Just as before, we can show the following recurrence for \<open>f\<close> in terms of \<open>e'\<close>:
\<close>
lemma f_recurrence:
  assumes k: "k > 0" "k \<le> n"
  shows   "f k = -of_nat k * (-1) ^ k * e' k - (\<Sum>i=1..<k. (- 1) ^ i * e' i * f (k - i))"
proof -
  have "-of_nat k * e' k = (\<Sum>i=1..k. (- 1) ^ i * e' (k - i) * f i)"
    using assms by (subst e'.simps) (simp add: field_simps)
  hence "(-1)^k * (-of_nat k * e' k) = (-1)^k * (\<Sum>i=1..k. (- 1) ^ i * e' (k - i) * f i)"
    by simp
  also have "\<dots> = f k + (-1) ^ k * (\<Sum>i=1..<k. (- 1) ^ i * e' (k - i) * f i)"
    using assms by (subst sum.last_plus) (auto simp: minus_one_power_iff)
  also have "(-1) ^ k * (\<Sum>i=1..<k. (- 1) ^ i * e' (k - i) * f i) =
             (\<Sum>i=1..<k. (- 1) ^ (k - i) * e' (k - i) * f i)"
    unfolding sum_distrib_left by (intro sum.cong) (auto simp: minus_one_power_iff)
  also have "\<dots> = (\<Sum>i=1..<k. (- 1) ^ i * e' i * f (k - i))"
    by (intro sum.reindex_bij_witness[of _ "\<lambda>i. k - i" "\<lambda>i. k - i"]) auto
  finally show ?thesis
    by (simp add: algebra_simps)
qed

text \<open>
  We now define a polynomial whose roots will be precisely the solution $x_1, \ldots, x_n$ to our
  problem.
\<close>
lift_definition Q' :: "complex poly" is "\<lambda>k. if k > n then 0 else (-1) ^ (n - k) * e' (n - k)"
  using eventually_gt_at_top[of n] unfolding cofinite_eq_sequentially
  by eventually_elim auto

lemma coeff_Q': "Polynomial.coeff Q' k = (if k > n then 0 else (-1) ^ (n - k) * e' (n - k))"
  by transfer auto

lemma lead_coeff_Q': "Polynomial.coeff Q' n = 1"
  by (simp add: coeff_Q')

lemma degree_Q' [simp]: "Polynomial.degree Q' = n"
proof (rule antisym)
  show "Polynomial.degree Q' \<ge> n"
    by (rule le_degree) (auto simp: coeff_Q')
  show "Polynomial.degree Q' \<le> n"
    by (rule degree_le) (auto simp: coeff_Q')
qed

text \<open>
  Since the complex numbers are algebraically closed, this polynomial splits into
  linear factors:
\<close>
definition Root :: "nat \<Rightarrow> complex"
  where "Root = (SOME Root. Q' = (\<Prod>i<n. [:-Root i, 1:]))"

lemma Root: "Q' = (\<Prod>i<n. [:-Root i, 1:])"
proof -
  obtain rs where rs: "(\<Prod>r\<leftarrow>rs. [:-r, 1:]) = Q'" "length rs = n"
    using fundamental_theorem_algebra_factorized[of Q'] lead_coeff_Q' by auto
  have "Q' = (\<Prod>r\<leftarrow>rs. [:-r, 1:])"
    by (simp add: rs)
  also have "\<dots> = (\<Prod>r=0..<n. [:-rs ! r, 1:])"
    by (subst prod_list_prod_nth) (auto simp: rs)
  also have "{0..<n} = {..<n}"
    by auto
  finally have "\<exists>Root. Q' = (\<Prod>i<n. [:-Root i, 1:])"
    by blast
  thus ?thesis
    unfolding Root_def by (rule someI_ex)
qed

text \<open>
  We can therefore now use the results from before for these $x_1, \ldots, x_n$.
\<close>
sublocale power_sum_puzzle Root n .

text \<open>
  Vieta's theorem gives us an expression for the coefficients of \<open>Q'\<close> in terms of
  $e_k(x_1,\ldots,x_n)$. This shows that our \<open>e'\<close> is indeed exactly the same as \<open>e\<close>.
\<close>
lemma e'_eq_e: "e' k = e k"
proof (cases "k \<le> n")
  case True
  from True have "e' k = (-1) ^ k * poly.coeff Q' (n - k)"
    by (simp add: coeff_Q')
  also have "Q' = (\<Prod>x<n. [:-Root x, 1:])"
    using Root by simp
  also have "(-1) ^ k * poly.coeff \<dots> (n - k) = e k"
    using True coeff_poly_from_roots[of "{..<n}" "n - k" Root]
    by (simp add: insertion_sym_mpoly e_altdef)
  finally show "e' k = e k" .
qed auto

text \<open>
  It then follows by a simple induction that $p_k = f_k$ for $1\leq k\leq n$, as intended:
\<close>
lemma p_eq_f:
  assumes "k > 0" "k \<le> n"
  shows   "p k = f k"
  using assms
proof (induction k rule: less_induct)
  case (less k)
  thus "p k = f k"
    using p_recurrence[of k] f_recurrence[of k] less by (simp add: e'_eq_e)
qed

end

text \<open>
  Here is a more condensed form of the above existence theorem:
\<close>
theorem power_sum_puzzle_has_solution:
  fixes f :: "nat \<Rightarrow> complex"
  shows "\<exists>Root. \<forall>k\<in>{1..n}. (\<Sum>i<n. Root i ^ k) = f k"
proof -
  interpret power_sum_puzzle_existence f .
  from p_eq_f have "\<forall>k\<in>{1..n}. (\<Sum>i<n. Root i ^ k) = f k"
    by (auto simp: p_def)
  thus ?thesis by blast
qed


subsection \<open>A specific puzzle\<close>

text \<open>
  We now look at one particular instance of this puzzle, which was given as an exercise in
  \<^emph>\<open>Abstract Algebra\<close> by Dummit and Foote (Exercise 23 in Section 14.6)~\cite{dummit}.

 Suppose we know that
  $x + y + z = 1$, $x^2 + y^2 + z^2 = 2$, and $x^3 + y^3 + z^3 = 3$. Then what is
  $x^5+y^5+z^5$? What about any arbitrary $x^n+y^n+z^n$?
\<close>
locale power_sum_puzzle_example =
  fixes x y z :: complex
  assumes xyz: "x   + y   + z   = 1"
               "x^2 + y^2 + z^2 = 2"
               "x^3 + y^3 + z^3 = 3"
begin

text \<open>
  We reuse the results we have shown in the general case before.
\<close>
definition f where "f n = [x,y,z] ! n"

sublocale power_sum_puzzle f 3 .

text \<open>
  We can simplify \<^term>\<open>p\<close> a bit more now.
\<close>
lemma p_altdef': "p k = x ^ k + y ^ k + z ^ k"
  unfolding p_def f_def by (simp add: eval_nat_numeral)

lemma p_base [simp]: "p (Suc 0) = 1" "p 2 = 2" "p 3 = 3"
  using xyz by (simp_all add: p_altdef')

text \<open>
  We can easily compute all the non-zero values of \<^term>\<open>e\<close> recursively:
\<close>
lemma e_Suc_0 [simp]: "e (Suc 0) = 1"
  by (subst e_recurrence; simp)

lemma e_2 [simp]: "e 2 = -1/2"
  by (subst e_recurrence; simp add: atLeastAtMost_nat_numeral)

lemma e_3 [simp]: "e 3 = 1/6"
  by (subst e_recurrence; simp add: atLeastAtMost_nat_numeral)

text \<open>
  Plugging in all the values, the recurrence relation for \<^term>\<open>p\<close> now looks like this:
\<close>
lemma p_recurrence''': "k > 3 \<Longrightarrow> p k = p (k-3) / 6 + p (k-2) / 2 + p (k-1)"
  using p_recurrence''[of k] by (simp add: atLeastAtMost_nat_numeral)

text \<open>
  Also note again that all $p_k$ are rational:
\<close>
lemma p_in_Rats': "p k \<in> \<rat>"
proof -
  have *: "{1..3} = {1, 2, (3::nat)}"
    by auto
  also have "\<forall>k\<in>\<dots>. p k \<in> \<rat>"
    by auto
  finally show ?thesis
    using p_in_Rats[of k] by simp
qed  

text \<open>
  The above recurrence has the characteristic polynomial $X^3 - X^2 - \frac{1}{2} X - \frac{1}{6}$
  (which is exactly our \<^term>\<open>Q\<close>), so we know that can now specify $x$, $y$, and $z$
  more precisely: They are the roots of that polynomial (in unspecified order).
\<close>

lemma xyz_eq: "{#x, y, z#} = poly_roots [:-1/6, -1/2, -1, 1:]"
proof -
  have "image_mset f (mset_set {..<3}) = poly_roots Q"
    using mset_x_eq_poly_roots_Q .
  also have "image_mset f (mset_set {..<3}) = {#x, y, z#}"
    by (simp add: numeral_3_eq_3 lessThan_Suc f_def Multiset.union_ac)
  also have "Q = [:-1/6, -1/2, -1, 1:]"
    by (simp add: Q_altdef atMost_nat_numeral Polynomial.monom_altdef
                  power3_eq_cube power2_eq_square)
  finally show ?thesis .
qed

text \<open>
  Using the rational root test, we can easily show that $x$, $y$, and $z$ are irrational.
\<close>
lemma xyz_irrational: "set_mset (poly_roots [:-1/6, -1/2, -1, 1::complex:]) \<inter> \<rat> = {}"
proof -
  define p :: "rat poly" where "p = [:-1/6, -1/2, -1, 1:]"
  have "rational_root_test p = None"
    unfolding p_def by code_simp
  hence "\<not>(\<exists>x::rat. poly p x = 0)"
    by (rule rational_root_test)
  hence "\<not>(\<exists>x\<in>\<rat>. poly (map_poly of_rat p) x = (0 :: complex))"
    by (auto simp: Rats_def)
  also have "map_poly of_rat p = [:-1/6, -1/2, -1, 1 :: complex:]"
    by (simp add: p_def of_rat_minus of_rat_divide)
  finally show ?thesis
    by auto
qed   
    

text \<open>
  This polynomial is \<^emph>\<open>squarefree\<close>, so these three roots are, in fact, unique (so that there are
  indeed $3! = 6$ possible permutations).
\<close>
lemma rsquarefree: "rsquarefree [:-1/6, -1/2, -1, 1 :: complex:]"
  by (rule coprime_pderiv_imp_rsquarefree)
     (auto simp: pderiv_pCons coprime_iff_gcd_eq_1 gcd_poly_code gcd_poly_code_def content_def
                 primitive_part_def gcd_poly_code_aux_reduce pseudo_mod_def pseudo_divmod_def
                 Let_def Polynomial.monom_altdef normalize_poly_def)

lemma distinct_xyz: "distinct [x, y, z]"
  by (rule rsquarefree_imp_distinct_roots[OF rsquarefree]) (simp_all add: xyz_eq)


text \<open>
  While these roots \<^emph>\<open>can\<close> be written more explicitly in radical form, they are not very pleasant
  to look at. We therefore only compute a few values of \<open>p\<close> just for fun:
\<close>
lemma "p 4 = 25 / 6" and "p 5 = 6" and "p 10 = 15539 / 432"
  by (simp_all add: p_recurrence''')

text \<open>
  Lastly, let us (informally) examine the asymptotics of this problem.

  Two of the roots have a norm of roughly $\beta \approx 0.341$, while the remaining root 
  \<open>\<alpha>\<close> is roughly 1.431. Consequently, $x^n + y^n + z^n$ is asymptotically equivalent to $\alpha^n$,
  with the error being bounded by $2\cdot \beta^n$ and therefore goes to 0 very quickly.

  For $p(10) = \frac{15539}{432} \approx 35.97$, for instance, this approximation is correct
  up to 6 decimals (a relative error of about 0.0001\,\%).
\<close>

end


text \<open>
  To really emphasise that the above puzzle has a solution and the locale is not `vacuous',
  here is an interpretation of the locale using the existence theorem from before:
\<close>
notepad
begin
  define f :: "nat \<Rightarrow> complex" where "f = (\<lambda>k. [1,2,3] ! (k - 1))"
  obtain Root :: "nat \<Rightarrow> complex" where Root: "\<And>k. k \<in> {1..3} \<Longrightarrow> (\<Sum>i<3. Root i ^ k) = f k"
    using power_sum_puzzle_has_solution[of 3 f] by metis
  define x y z where "x = Root 0" "y = Root 1" "z = Root 2"
  have "x + y + z = 1" and "x^2 + y^2 + z^2 = 2" and "x^3 + y^3 + z^3 = 3"
    using Root[of 1] Root[of 2] Root[of 3] by (simp_all add: eval_nat_numeral x_y_z_def f_def)
  then interpret power_sum_puzzle_example x y z
    by unfold_locales
  have "p 5 = 6"
    by (simp add: p_recurrence''')
end

end