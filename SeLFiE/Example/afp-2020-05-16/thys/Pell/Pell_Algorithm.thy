(*
  File:    Pell_Algorithm.thy
  Author:  Manuel Eberl, TU München

  Some executable but not too efficient algorithms for computing solutions to Pell's equation.
*)
subsection \<open>Executable code\<close>
theory Pell_Algorithm
imports
  Pell
  Efficient_Discrete_Sqrt
  "HOL-Library.Discrete"
  "HOL-Library.While_Combinator"
  "HOL-Library.Stream"
begin

subsubsection \<open>Efficient computation of powers by squaring\<close>

text \<open>
  The following is a tail-recursive implementation of exponentiation by squaring.
  It works for any binary operation \<open>f\<close> that fulfils \<open>f x (f x z) = f (f x x) z\<close>, i.\,e.\ 
  some weak form of associativity.
\<close>

context
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
begin

function efficient_power :: "'a \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "efficient_power y x 0 = y"
| "efficient_power y x (Suc 0) = f x y"
| "n \<noteq> 0 \<Longrightarrow> even n \<Longrightarrow> efficient_power y x n = efficient_power y (f x x) (n div 2)"
| "n \<noteq> 1 \<Longrightarrow> odd n \<Longrightarrow> efficient_power y x n = efficient_power (f x y) (f x x) (n div 2)"
  by force+
termination by (relation "measure (snd \<circ> snd)") (auto elim: oddE)

lemma efficient_power_code [code]:
  "efficient_power y x n =
     (if n = 0 then y
      else if n = 1 then f x y
      else if even n then efficient_power y (f x x) (n div 2)
      else efficient_power (f x y) (f x x) (n div 2))"
  by (induction y x n rule: efficient_power.induct) auto

lemma efficient_power_correct:
  assumes "\<And>x z. f x (f x z) = f (f x x) z"
  shows   "efficient_power y x n = (f x ^^ n) y"
proof -
  have [simp]: "f ^^ 2 = (\<lambda>x. f (f x))" for f :: "'a \<Rightarrow> 'a"
    by (simp add: eval_nat_numeral o_def)
  show ?thesis
    by (induction y x n rule: efficient_power.induct)
       (auto elim!: evenE oddE simp: funpow_mult [symmetric] funpow_Suc_right assms
             simp del: funpow.simps(2))
qed

end


subsubsection \<open>Multiplication and powers of solutions\<close>

text \<open>
  We define versions of Pell solution multiplication and exponentiation specialised
  to natural numbers, both for efficiency reasons and to circumvent the problem of
  generating code for definitions made inside locales.
\<close>
fun pell_mul_nat :: "nat \<Rightarrow> nat \<times> nat \<Rightarrow> _" where
  "pell_mul_nat D (a, b) (x, y) = (a * x + D * b * y, a * y + b * x)"

lemma (in pell) pell_mul_nat_correct [simp]: "pell_mul_nat D = pell.pell_mul D"
  by (auto simp add: pell_mul_def fun_eq_iff)

definition efficient_pell_power :: "nat \<Rightarrow> nat \<times> nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  "efficient_pell_power D z n = efficient_power (pell_mul_nat D) (1, 0) z n"

lemma efficient_pell_power_correct [simp]:
  "efficient_pell_power D z n = (pell_mul_nat D z ^^ n) (1, 0)"
  unfolding efficient_pell_power_def
  by (intro efficient_power_correct) (auto simp: algebra_simps)


subsubsection \<open>Finding the fundamental solution\<close>

text \<open>
  In the following, we set up a very simple algorithm for computing the fundamental
  solution \<open>(x, y)\<close>. We try inreasing values for \<open>y\<close> until $1 + Dy^2$ is a perfect 
  square, which we check using an efficient square-detection algorithm. This is efficient
  enough to work on some interesting small examples.

  Much better algorithms (typically based on the continued fraction expansion of $\sqrt{D}$) 
  are available, but they are also considerably more complicated.
\<close>

lemma Discrete_sqrt_square_is_square:
  assumes "is_square n"
  shows   "Discrete.sqrt n ^ 2 = n"
  using assms unfolding is_nth_power_def by force

definition find_fund_sol_step :: "nat \<Rightarrow> nat \<times> nat + nat \<times> nat \<Rightarrow> _" where
  "find_fund_sol_step D = (\<lambda>Inl (y, y') \<Rightarrow>
     (case get_nat_sqrt y' of 
        Some x \<Rightarrow> Inr (x, y)
      | None \<Rightarrow> Inl (y + 1, y' + D * (2 * y + 1))))"

definition find_fund_sol where
  "find_fund_sol D =
     (if square_test D then
        (0, 0)
      else
        sum.projr (while sum.isl (find_fund_sol_step D) (Inl (1, 1 + D))))"

lemma fund_sol_code:
  assumes "\<not>is_square (D :: nat)"
  shows   "pell.fund_sol D = sum.projr (while isl (find_fund_sol_step D) (Inl (Suc 0, Suc D)))"
proof -
  from assms interpret pell D by unfold_locales
  note [simp] = find_fund_sol_step_def
  define f where "f = find_fund_sol_step D"
  define P :: "nat \<Rightarrow> bool" where "P = (\<lambda>y. y > 0 \<and> is_square (y^2 * D + 1))" 
  define Q :: "nat \<times> nat \<Rightarrow> bool" where
    "Q = (\<lambda>(x,y). P y \<and> (\<forall>y'\<in>{0<..<y}. \<not>P y') \<and> x = Discrete.sqrt (y^2 * D + 1))"
  define R :: "nat \<times> nat + nat \<times> nat \<Rightarrow> bool" 
    where "R = (\<lambda>s. case s of
                      Inl (m, m') \<Rightarrow> m > 0 \<and> (m' = m^2 * D + 1) \<and> (\<forall>y\<in>{0<..<m}. \<not>is_square (y^2 * D + 1))
                    | Inr x \<Rightarrow> Q x)"
  define rel :: "((nat \<times> nat + nat \<times> nat) \<times> (nat \<times> nat + nat \<times> nat)) set"
    where "rel = {(A,B). (case (A, B) of
                           (Inl (m, _), Inl (m', _)) \<Rightarrow> m' > 0 \<and> m > m' \<and> m \<le> snd fund_sol
                         | (Inr _, Inl (m', _)) \<Rightarrow> m' \<le> snd fund_sol
                         | _ \<Rightarrow> False) \<and> A = f B}"
  obtain x y where xy: "sum.projr (while isl f (Inl (Suc 0, Suc D))) = (x, y)"
    by (cases "sum.projr (while isl f (Inl (Suc 0, Suc D)))")

  have neq_fund_solI: "y \<noteq> snd fund_sol" if "\<not> is_square (Suc (y\<^sup>2 * D))" for y
  proof
    assume "y = snd fund_sol"
    with fund_sol_is_nontriv_solution have "Suc (y\<^sup>2 * D) = fst fund_sol ^ 2"
      by (simp add: nontriv_solution_def case_prod_unfold)
    hence "is_square (Suc (y\<^sup>2 * D))" by simp
    with that show False by contradiction
  qed

  have "case_sum (\<lambda>_. False) Q (while sum.isl f (Inl (m, m^2 * D + 1)))"
    if "\<forall>y\<in>{0<..<m}. \<not>is_square (y^2 * D + 1)" "m > 0" for m
  proof (rule while_rule[where b = sum.isl])
    show "R (Inl (m, m\<^sup>2 * D + 1))"
      using that by (auto simp: R_def)
  next
    fix s assume "R s" "isl s"
    thus "R (f s)"
      by (auto simp: not_less_less_Suc_eq Q_def P_def R_def f_def get_nat_sqrt_def
                     power2_eq_square algebra_simps split: sum.splits prod.splits)
  next
    fix s assume "R s" "\<not>isl s"
    thus "case s of Inl _ \<Rightarrow> False | Inr x \<Rightarrow> Q x"
      by (auto simp: R_def split: sum.splits)
  next
    fix s assume s: "R s" "isl s"
    show "(f s, s) \<in> rel"
    proof (cases s)
      case [simp]: (Inl s')
      obtain a b where [simp]: "s' = (a, b)" by (cases s')
      from s have *: "a > 0" "b = Suc (a\<^sup>2 * D)" "\<And>y. y \<in> {0<..<a} \<Longrightarrow> \<not> is_square (Suc (y\<^sup>2 * D))"
        by (auto simp: R_def)
     
      have "a < snd fund_sol" if **: "\<not> is_square (Suc (a\<^sup>2 * D))"
      proof -
        from neq_fund_solI have "y' \<noteq> snd fund_sol" if "y' \<in> {0<..<Suc a}" for y'
          using * ** that by (cases "y' = a") auto
        moreover have "snd fund_sol \<noteq> 0" using fund_sol_is_nontriv_solution
          by (intro notI, cases fund_sol) (auto simp: nontriv_solution_altdef)
        ultimately have "\<forall>y'\<le>a. y' \<noteq> snd fund_sol" by (auto simp: less_Suc_eq_le)
        thus "snd fund_sol > a" by (cases "a < snd fund_sol") (auto simp: not_less)
      qed
      moreover have "a \<le> snd fund_sol"
      proof -
        have "\<forall>y'\<in>{0<..<a}. y' \<noteq> snd fund_sol" using neq_fund_solI *
          by (auto simp: less_Suc_eq_le)
        moreover have "snd fund_sol \<noteq> 0" using fund_sol_is_nontriv_solution
          by (intro notI, cases fund_sol) (auto simp: nontriv_solution_altdef)
        ultimately have "\<forall>y'<a. y' \<noteq> snd fund_sol" by (auto simp: less_Suc_eq_le)
        thus "snd fund_sol \<ge> a" by (cases "a \<le> snd fund_sol") (auto simp: not_less)
      qed
      ultimately show ?thesis using *
        by (auto simp: f_def get_nat_sqrt_def rel_def)
    qed (insert s, auto)
  next
    define rel'
      where "rel' = {(y, x). (case x of Inl (m, _) \<Rightarrow> m \<le> snd fund_sol | Inr _ \<Rightarrow> False) \<and> y = f x}"
    have "wf rel'" unfolding rel'_def
      by (rule wf_if_measure[where f = "\<lambda>z. case z of Inl (m, _) \<Rightarrow> Suc (snd fund_sol) - m | _ \<Rightarrow> 0"])
         (auto split: prod.splits sum.splits simp: f_def get_nat_sqrt_def)
    moreover have "rel \<subseteq> rel'"
    proof safe
      fix w z assume "(w, z) \<in> rel"
      thus "(w, z) \<in> rel'" by (cases w; cases z) (auto simp: rel_def rel'_def)
    qed
    ultimately show "wf rel" by (rule wf_subset)
  qed
  from this[of 1] and xy have *: "Q (x, y)"
    by (auto split: sum.splits)

  from * have "is_square (Suc (y\<^sup>2 * D))" by (simp add: Q_def P_def)
  with * have "x\<^sup>2 = Suc (y\<^sup>2 * D)" "y > 0"
    by (auto simp: Q_def P_def Discrete_sqrt_square_is_square)
  hence "nontriv_solution (x, y)"
    by (auto simp: nontriv_solution_def)
  from this have "snd fund_sol \<le> snd (x, y)"
    by (rule fund_sol_minimal'')
  moreover have "snd fund_sol \<ge> y"
  proof -
    from * have "(\<forall>y'\<in>{0<..<y}. \<not> is_square (Suc (y'\<^sup>2 * D)))"
      by (simp add: Q_def P_def)
    with neq_fund_solI have "(\<forall>y'\<in>{0<..<y}. y' \<noteq> snd fund_sol)"
      by auto
    moreover have "snd fund_sol \<noteq> 0"
      using fund_sol_is_nontriv_solution
      by (cases fund_sol) (auto intro!: Nat.gr0I simp: nontriv_solution_altdef)
    ultimately have "(\<forall>y'<y. y' \<noteq> snd fund_sol)" by auto
    thus "snd fund_sol \<ge> y" by (cases "snd fund_sol \<ge> y") (auto simp: not_less)
  qed
  ultimately have "snd fund_sol = y" by simp
  with solutions_linorder_strict[of x y "fst fund_sol" "snd fund_sol"]
       fund_sol_is_nontriv_solution \<open>nontriv_solution (x, y)\<close>
    have "fst fund_sol = x" by (cases fund_sol) (auto simp: nontriv_solution_altdef)
  with \<open>snd fund_sol = y\<close> have "fund_sol = (x, y)"
    by (cases fund_sol) simp
  with xy show ?thesis by (simp add: f_def)
qed

lemma find_fund_sol_correct: "find_fund_sol D = (if is_square D then (0, 0) else pell.fund_sol D)"
  by (simp add: find_fund_sol_def fund_sol_code square_test_correct)


subsubsection \<open>The infinite list of all solutions\<close>

definition pell_solutions :: "nat \<Rightarrow> (nat \<times> nat) stream" where
  "pell_solutions D = (let z = find_fund_sol D in siterate (pell_mul_nat D z) (1, 0))"

lemma (in pell) "snth (pell_solutions D) n = nth_solution n"
  by (simp add: pell_solutions_def Let_def find_fund_sol_correct nonsquare_D nth_solution_def
                pell_power_def pell_mul_commutes[of _ fund_sol])


subsubsection \<open>Computing the $n$-th solution\<close>

definition find_nth_solution :: "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  "find_nth_solution D n =
     (if is_square D then (0, 0) else
        let z = sum.projr (while isl (find_fund_sol_step D) (Inl (Suc 0, Suc D)))
        in  efficient_pell_power D z n)"

lemma (in pell) find_nth_solution_correct: "find_nth_solution D n = nth_solution n"
  by (simp add: find_nth_solution_def nonsquare_D nth_solution_def fund_sol_code 
                pell_power_def pell_mul_commutes[of _ "projr _"])

end