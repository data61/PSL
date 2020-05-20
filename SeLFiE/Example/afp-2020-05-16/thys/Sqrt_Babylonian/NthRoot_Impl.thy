(*  Title:       Computing Square Roots using the Babylonian Method
    Author:      René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  René Thiemann
    License:     LGPL
*)

(*
Copyright 2009-2014 René Thiemann

This file is part of IsaFoR/CeTA.

IsaFoR/CeTA is free software: you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

IsaFoR/CeTA is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along
with IsaFoR/CeTA. If not, see <http://www.gnu.org/licenses/>.
*)
section \<open>Executable algorithms for $p$-th roots\<close>

theory NthRoot_Impl
imports
  Log_Impl
  Cauchy.CauchysMeanTheorem
begin

text \<open>
We implemented algorithms to decide $\sqrt[p]{n} \in \rats$ and to compute $\lfloor \sqrt[p]{n} \rfloor$.
To this end, we use a variant of Newton iteration which works with integer division instead of floating
point or rational division. To get suitable starting values for the Newton iteration, we also implemented
a function to approximate logarithms.
\<close>

subsection \<open>Logarithm\<close>

text \<open>For computing the $p$-th root of a number $n$, we must choose a starting value
  in the iteration. Here, we use @{term "2 ^ (nat \<lceil>of_int \<lceil>log 2 n\<rceil> / p\<rceil>)"}.
\<close>

text \<open>We use a partial efficient algorithm, which does not terminate on
  corner-cases, like $b = 0$ or $p = 1$, and invoke it properly afterwards.
  Then there is a second algorithm which terminates on these corner-cases by additional
  guards and on which we can perform induction.
\<close>

subsection \<open>Computing the $p$-th root of an integer number\<close>

text \<open>Using the logarithm, we can define an executable version of the
  intended  starting value. Its main property is the inequality
  @{term "(start_value x p) ^ p \<ge> x"}, i.e., the start value is larger
  than the p-th root. This property is essential, since our algorithm will abort
  as soon as we fall below the p-th root.\<close>

definition start_value :: "int \<Rightarrow> nat \<Rightarrow> int" where
  "start_value n p = 2 ^ (nat \<lceil>of_nat (log_ceiling 2 n) / rat_of_nat p\<rceil>)"

lemma start_value_main: assumes x: "x \<ge> 0" and p: "p > 0"
  shows "x \<le> (start_value x p)^p \<and> start_value x p \<ge> 0"
proof (cases "x = 0")
  case True
  with p show ?thesis unfolding start_value_def True by simp
next
  case False
  with x have x: "x > 0" by auto
  define l2x where "l2x = \<lceil>log 2 x\<rceil>"
  define pow where "pow = nat \<lceil>rat_of_int l2x / of_nat p\<rceil>"
  have "root p x = x powr (1 / p)" by (rule root_powr_inverse, insert x p, auto)
  also have "\<dots> = (2 powr (log 2 x)) powr (1 / p)" using powr_log_cancel[of 2 x] x by auto
  also have "\<dots> = 2 powr (log 2 x * (1 / p))" by (rule powr_powr)
  also have "log 2 x * (1 / p) = log 2 x / p" using p by auto
  finally have r: "root p x = 2 powr (log 2 x / p)" .
  have lp: "log 2 x \<ge> 0" using x by auto
  hence l2pos: "l2x \<ge> 0" by (auto simp: l2x_def)
  have "log 2 x / p \<le> l2x / p" using x p unfolding l2x_def
    by (metis divide_right_mono le_of_int_ceiling of_nat_0_le_iff)
  also have "\<dots> \<le> \<lceil>l2x / (p :: real)\<rceil>" by (simp add: ceiling_correct)
  also have "l2x / real p = l2x / real_of_rat (of_nat p)"
    by (metis of_rat_of_nat_eq)
  also have "of_int l2x = real_of_rat (of_int l2x)"
    by (metis of_rat_of_int_eq)
  also have "real_of_rat (of_int l2x) / real_of_rat (of_nat p) = real_of_rat (rat_of_int l2x / of_nat p)"
    by (metis of_rat_divide)
  also have "\<lceil>real_of_rat (rat_of_int l2x / rat_of_nat p)\<rceil> = \<lceil>rat_of_int l2x / of_nat p\<rceil>"
    by simp
  also have "\<lceil>rat_of_int l2x / of_nat p\<rceil> \<le> real pow" unfolding pow_def by auto
  finally have le: "log 2 x / p \<le> pow" .
  from powr_mono[OF le, of 2, folded r]
  have "root p x \<le> 2 powr pow" by auto
  also have "\<dots> = 2 ^ pow" by (rule powr_realpow, auto)
  also have "\<dots> = of_int ((2 :: int) ^ pow)" by simp
  also have "pow = (nat \<lceil>of_int (log_ceiling 2 x) / rat_of_nat p\<rceil>)"
    unfolding pow_def l2x_def using x by simp
  also have "real_of_int ((2 :: int) ^ \<dots> ) = start_value x p" unfolding start_value_def  by simp
  finally have less: "root p x \<le> start_value x p" .
  have "0 \<le> root p x" using p x by auto
  also have "\<dots> \<le> start_value x p" by (rule less)
  finally have start: "0 \<le> start_value x p" by simp
  from power_mono[OF less, of p] have "root p (of_int x) ^ p \<le> of_int (start_value x p) ^ p" using p x by auto
  also have "\<dots> = start_value x p ^ p" by simp
  also have "root p (of_int x) ^ p = x" using p x by force
  finally have "x \<le> (start_value x p) ^ p" by presburger
  with start show ?thesis by auto
qed

lemma start_value: assumes x: "x \<ge> 0" and p: "p > 0" shows "x \<le> (start_value x p) ^ p" "start_value x p \<ge> 0"
  using start_value_main[OF x p] by auto

text \<open>We now define the Newton iteration to compute the $p$-th root. We are working on the integers,
  where every @{term "(/)"} is replaced by @{term "(div)"}. We are proving several things within
  a locale which ensures that $p > 0$, and where $pm = p - 1$.
\<close>

locale fixed_root =
  fixes p pm :: nat
  assumes p: "p = Suc pm"
begin

function root_newton_int_main :: "int \<Rightarrow> int \<Rightarrow> int \<times> bool" where
  "root_newton_int_main x n = (if (x < 0 \<or> n < 0) then (0,False) else (if x ^ p \<le> n then (x, x ^ p = n)
    else root_newton_int_main ((n div (x ^ pm) + x * int pm) div (int p)) n))"
    by pat_completeness auto
end

text \<open>For the executable algorithm we omit the guard and use a let-construction\<close>

partial_function (tailrec) root_int_main' :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<times> bool" where
  [code]: "root_int_main' pm ipm ip x n = (let xpm = x^pm; xp = xpm * x in if xp \<le> n then (x, xp = n)
    else root_int_main' pm ipm ip ((n div xpm + x * ipm) div ip) n)"

text \<open>In the following algorithm, we
  start the iteration.
  It will compute @{term "\<lfloor>root p n\<rfloor>"} and a boolean to indicate whether the root is exact.\<close>

definition root_int_main :: "nat \<Rightarrow> int \<Rightarrow> int \<times> bool" where
  "root_int_main p n \<equiv> if p = 0 then (1,n = 1) else
     let pm = p - 1
       in root_int_main' pm (int pm) (int p) (start_value n p) n"

text \<open>Once we have proven soundness of @{const fixed_root.root_newton_int_main} and equivalence
  to @{const root_int_main}, it
  is easy to assemble the following algorithm which computes all roots for arbitrary integers.\<close>

definition root_int :: "nat \<Rightarrow> int \<Rightarrow> int list" where
  "root_int p x \<equiv> if p = 0 then [] else
    if x = 0 then [0] else
      let e = even p; s = sgn x; x' = abs x
      in if x < 0 \<and> e then [] else case root_int_main p x' of (y,True) \<Rightarrow> if e then [y,-y] else [s * y] | _ \<Rightarrow> []"

text \<open>We start with proving termination of @{const fixed_root.root_newton_int_main}.\<close>

context fixed_root
begin
lemma iteration_mono_eq: assumes xn: "x ^ p = (n :: int)"
  shows "(n div x ^ pm + x * int pm) div int p = x"
proof -
  have [simp]: "\<And> n. (x + x * n) = x * (1 + n)" by (auto simp: field_simps)
  show ?thesis unfolding xn[symmetric] p by simp
qed

lemma p0: "p \<noteq> 0" unfolding p by auto

text \<open>The following property is the essential property for
  proving termination of @{const "root_newton_int_main"}.
\<close>
lemma iteration_mono_less: assumes x: "x \<ge> 0"
  and n: "n \<ge> 0"
  and xn: "x ^ p > (n :: int)"
  shows "(n div x ^ pm + x * int pm) div int p < x"
proof -
  let ?sx = "(n div x ^ pm + x * int pm) div int p"
  from xn have xn_le: "x ^ p \<ge> n" by auto
  from xn x n have x0: "x > 0"
    using not_le p by fastforce
  from p have xp: "x ^ p = x * x ^ pm" by auto
  from x n have "n div x ^ pm * x ^ pm \<le> n"
    by (auto simp add: minus_mod_eq_div_mult [symmetric] mod_int_pos_iff not_less power_le_zero_eq)
  also have "\<dots> \<le> x ^ p" using xn by auto
  finally have le: "n div x ^ pm \<le> x" using x x0 unfolding xp by simp
  have "?sx \<le> (x^p div x ^ pm + x * int pm) div int p"
    by (rule zdiv_mono1, insert le p0, unfold xp, auto)
  also have "x^p div x ^ pm = x" unfolding xp by auto
  also have "x + x * int pm = x * int p" unfolding p by (auto simp: field_simps)
  also have "x * int p div int p = x" using p by force
  finally have le: "?sx \<le> x" .
  {
    assume "?sx = x"
    from arg_cong[OF this, of "\<lambda> x. x * int p"]
    have "x * int p \<le> (n div x ^ pm + x * int pm) div (int p) * int p" using p0 by simp
    also have "\<dots> \<le> n div x ^ pm + x * int pm"
      unfolding mod_div_equality_int using p by auto
    finally have "n div x^pm \<ge> x" by (auto simp: p field_simps)
    from mult_right_mono[OF this, of "x ^ pm"]
    have ge: "n div x^pm * x^pm \<ge> x^p" unfolding xp using x by auto
    from div_mult_mod_eq[of n "x^pm"] have "n div x^pm * x^pm = n - n mod x^pm" by arith
    from ge[unfolded this]
    have le: "x^p \<le> n - n mod x^pm" .
    from x n have ge: "n mod x ^ pm \<ge> 0"
      by (auto simp add: mod_int_pos_iff not_less power_le_zero_eq)
    from le ge
    have "n \<ge> x^p" by auto
    with xn have False by auto
  }
  with le show ?thesis unfolding p by fastforce
qed

lemma iteration_mono_lesseq: assumes x: "x \<ge> 0" and n: "n \<ge> 0" and xn: "x ^ p \<ge> (n :: int)"
  shows "(n div x ^ pm + x * int pm) div int p \<le> x"
proof (cases "x ^ p = n")
  case True
  from iteration_mono_eq[OF this] show ?thesis by simp
next
  case False
  with assms have "x ^ p > n" by auto
  from iteration_mono_less[OF x n this]
  show ?thesis by simp
qed

termination (* of root_newton_int_main *)
proof -
  let ?mm = "\<lambda> x  n :: int. nat x"
  let ?m1 = "\<lambda> (x,n). ?mm x n"
  let ?m = "measures [?m1]"
  show ?thesis
  proof (relation ?m)
    fix x n :: int
    assume "\<not> x ^ p \<le> n"
    hence x: "x ^ p > n" by auto
    assume "\<not> (x < 0 \<or> n < 0)"
    hence x_n: "x \<ge> 0" "n \<ge> 0" by auto
    from x x_n have x0: "x > 0" using p by (cases "x = 0", auto)
    from iteration_mono_less[OF x_n x] x0
    show "(((n div x ^ pm + x * int pm) div int p, n), x, n) \<in> ?m" by auto
  qed auto
qed

text \<open>We next prove that @{const root_int_main'} is a correct implementation of @{const root_newton_int_main}.
We additionally prove that the result is always positive, a lower bound, and that the returned boolean indicates
whether the result has a root or not. We prove all these results in one go, so that we can share the
inductive proof.
\<close>

abbreviation root_main' where "root_main' \<equiv> root_int_main' pm (int pm) (int p)"

lemmas root_main'_simps = root_int_main'.simps[of pm "int pm" "int p"]

lemma root_main'_newton_pos: "x \<ge> 0 \<Longrightarrow> n \<ge> 0 \<Longrightarrow>
  root_main' x n = root_newton_int_main x n \<and> (root_main' x n = (y,b) \<longrightarrow> y \<ge> 0 \<and> y^p \<le> n \<and> b = (y^p = n))"
proof (induct x n rule: root_newton_int_main.induct)
  case (1 x n)
  have pm_x[simp]: "x ^ pm * x = x ^ p" unfolding p by simp
  from 1 have id: "(x < 0 \<or> n < 0) = False" by auto
  note d = root_main'_simps[of x n] root_newton_int_main.simps[of x n] id if_False Let_def
  show ?case
  proof (cases "x ^ p \<le> n")
    case True
    thus ?thesis unfolding d using 1(2) by auto
  next
    case False
    hence id: "(x ^ p \<le> n) = False" by simp
    from 1(3) 1(2) have not: "\<not> (x < 0 \<or> n < 0)" by auto
    then have x: "x > 0 \<or> x = 0"
      by auto
    with \<open>0 \<le> n\<close> have "0 \<le> (n div x ^ pm + x * int pm) div int p"
      by (auto simp add: p algebra_simps pos_imp_zdiv_nonneg_iff power_0_left)
    then show ?thesis unfolding d id pm_x
      by (rule 1(1)[OF not False _ 1(3)])
  qed
qed

lemma root_main': "x \<ge> 0 \<Longrightarrow> n \<ge> 0 \<Longrightarrow> root_main' x n = root_newton_int_main x n"
  using root_main'_newton_pos by blast

lemma root_main'_pos: "x \<ge> 0 \<Longrightarrow> n \<ge> 0 \<Longrightarrow> root_main' x n = (y,b) \<Longrightarrow> y \<ge> 0"
  using root_main'_newton_pos by blast

lemma root_main'_sound: "x \<ge> 0 \<Longrightarrow> n \<ge> 0 \<Longrightarrow> root_main' x n = (y,b) \<Longrightarrow> b = (y ^ p = n)"
  using root_main'_newton_pos by blast

text \<open>In order to prove completeness of the algorithms, we provide sharp upper and lower bounds
  for @{const root_main'}. For the upper bounds, we use Cauchy's mean theorem where we added
  the non-strict variant to Porter's formalization of this theorem.\<close>

lemma root_main'_lower: "x \<ge> 0 \<Longrightarrow> n \<ge> 0 \<Longrightarrow> root_main' x n = (y,b) \<Longrightarrow> y ^ p \<le> n"
  using root_main'_newton_pos by blast

lemma root_newton_int_main_upper:
  shows "y ^ p \<ge> n \<Longrightarrow> y \<ge> 0 \<Longrightarrow> n \<ge> 0 \<Longrightarrow> root_newton_int_main y n = (x,b) \<Longrightarrow> n < (x + 1) ^ p"
proof (induct y n rule: root_newton_int_main.induct)
  case (1 y n)
  from 1(3) have y0: "y \<ge> 0" .
  then have "y > 0 \<or> y = 0"
    by auto
  from 1(4) have n0: "n \<ge> 0" .
  define y' where "y' = (n div (y ^ pm) + y * int pm) div (int p)"
  from \<open>y > 0 \<or> y = 0\<close> \<open>n \<ge> 0\<close> have y'0: "y' \<ge> 0"
    by (auto simp add: y'_def p algebra_simps pos_imp_zdiv_nonneg_iff power_0_left)
  let ?rt = "root_newton_int_main"
  from 1(5) have rt: "?rt y n = (x,b)" by auto
  from y0 n0 have not: "\<not> (y < 0 \<or> n < 0)" "(y < 0 \<or> n < 0) = False" by auto
  note rt = rt[unfolded root_newton_int_main.simps[of y n] not(2) if_False, folded y'_def]
  note IH = 1(1)[folded y'_def, OF not(1) _ _ y'0 n0]
  show ?case
  proof (cases "y ^ p \<le> n")
    case False note yyn = this
    with rt have rt: "?rt y' n = (x,b)" by simp
    show ?thesis
    proof (cases "n \<le> y' ^ p")
      case True
      show ?thesis
        by (rule IH[OF False True rt])
    next
      case False
      with rt have x: "x = y'" unfolding root_newton_int_main.simps[of y' n]
        using n0 y'0 by simp
      from yyn have yyn: "y^p > n" by simp
      from False have yyn': "n > y' ^ p" by auto
      {
        assume pm: "pm = 0"
        have y': "y' = n" unfolding y'_def p pm by simp
        with yyn' have False unfolding p pm by auto
      }
      hence pm0: "pm > 0" by auto
      show ?thesis
      proof (cases "n = 0")
        case True
        thus ?thesis unfolding p
          by (metis False y'0 zero_le_power)
      next
        case False note n00 = this
        let ?y = "of_int y :: real"
        let ?n = "of_int n :: real"
        from yyn n0 have y00: "y \<noteq> 0" unfolding p by auto
        from y00 y0 have y0: "?y > 0" by auto
        from n0 False have n0: "?n > 0" by auto
        define Y where "Y = ?y * of_int pm"
        define NY where "NY = ?n / ?y ^ pm"
        note pos_intro = divide_nonneg_pos add_nonneg_nonneg mult_nonneg_nonneg
        have NY0: "NY > 0" unfolding NY_def using y0 n0
          by (metis NY_def zero_less_divide_iff zero_less_power)
        let ?ls = "NY # replicate pm ?y"
        have prod: "\<Prod>:replicate pm ?y = ?y ^ pm "
          by (induct pm, auto)
        have sum: "\<Sum>:replicate pm ?y = Y" unfolding Y_def
          by (induct pm, auto simp: field_simps)
        have pos: "pos ?ls" unfolding pos_def using NY0 y0 by auto
        have "root p ?n = gmean ?ls" unfolding gmean_def using y0
          by (auto simp: p NY_def prod)
        also have "\<dots> < mean ?ls"
        proof (rule CauchysMeanTheorem_Less[OF pos het_gt_0I])
          show "NY \<in> set ?ls" by simp
          from pm0 show "?y \<in> set ?ls" by simp
          have "NY < ?y"
          proof -
            from yyn have less: "?n < ?y ^ Suc pm" unfolding p
              by (metis of_int_less_iff of_int_power)
            have "NY < ?y ^ Suc pm / ?y ^ pm" unfolding NY_def
              by (rule divide_strict_right_mono[OF less], insert y0, auto)
            thus ?thesis using y0 by auto
          qed
          thus "NY \<noteq> ?y" by blast
        qed
        also have "\<dots> = (NY + Y) / real p"
          by (simp add: mean_def sum p)
        finally have *: "root p ?n < (NY + Y) / real p" .
        have "?n = (root p ?n)^p" using n0
          by (metis neq0_conv p0 real_root_pow_pos)
        also have "\<dots> < ((NY + Y) / real p)^p"
          by (rule power_strict_mono[OF *], insert n0 p, auto)
        finally have ineq1: "?n < ((NY + Y) / real p)^p" by auto
        {
          define s where "s = n div y ^ pm + y * int pm"
          define S where "S = NY + Y"
          have Y0: "Y \<ge> 0" using y0 unfolding Y_def
            by (metis "1.prems"(2) mult_nonneg_nonneg of_int_0_le_iff of_nat_0_le_iff)
          have S0: "S > 0" using NY0 Y0 unfolding S_def by auto
          from p have p0: "p > 0" by auto
          have "?n / ?y ^ pm  < of_int (floor (?n / ?y^pm)) + 1"
            by (rule divide_less_floor1)
          also have "floor (?n / ?y ^ pm) = n div y^pm"
            unfolding div_is_floor_divide_real by (metis of_int_power)
          finally have "NY < of_int (n div y ^ pm) + 1" unfolding NY_def by simp
          hence less: "S < of_int s + 1" unfolding Y_def s_def S_def by simp
          { (* by sledgehammer *)
            have f1: "\<forall>x\<^sub>0. rat_of_int \<lfloor>rat_of_nat x\<^sub>0\<rfloor> = rat_of_nat x\<^sub>0"
              using of_int_of_nat_eq by simp
            have f2: "\<forall>x\<^sub>0. real_of_int \<lfloor>rat_of_nat x\<^sub>0\<rfloor> = real x\<^sub>0"
              using of_int_of_nat_eq by auto
            have f3: "\<forall>x\<^sub>0 x\<^sub>1. \<lfloor>rat_of_int x\<^sub>0 / rat_of_int x\<^sub>1\<rfloor> = \<lfloor>real_of_int x\<^sub>0 / real_of_int x\<^sub>1\<rfloor>"
              using div_is_floor_divide_rat div_is_floor_divide_real by simp
            have f4: "0 < \<lfloor>rat_of_nat p\<rfloor>"
              using p by simp
            have "\<lfloor>S\<rfloor> \<le> s" using less floor_le_iff by auto
            hence "\<lfloor>rat_of_int \<lfloor>S\<rfloor> / rat_of_nat p\<rfloor> \<le> \<lfloor>rat_of_int s / rat_of_nat p\<rfloor>"
              using f1 f3 f4 by (metis div_is_floor_divide_real zdiv_mono1)
            hence "\<lfloor>S / real p\<rfloor> \<le> \<lfloor>rat_of_int s / rat_of_nat p\<rfloor>"
              using f1 f2 f3 f4 by (metis div_is_floor_divide_real floor_div_pos_int)
            hence "S / real p \<le> real_of_int (s div int p) + 1"
              using f1 f3 by (metis div_is_floor_divide_real floor_le_iff floor_of_nat less_eq_real_def)
          }
          hence "S / real p \<le> of_int(s div p) + 1" .
          note this[unfolded S_def s_def]
        }
        hence ge: "of_int y' + 1 \<ge> (NY + Y) / p" unfolding y'_def
          by simp
        have pos1: "(NY + Y) / p \<ge> 0" unfolding Y_def NY_def
          by (intro divide_nonneg_pos add_nonneg_nonneg mult_nonneg_nonneg,
          insert y0 n0 p0, auto)
        have pos2: "of_int y' + (1 :: rat) \<ge> 0" using y'0 by auto
        have ineq2: "(of_int y' + 1) ^ p \<ge> ((NY + Y) / p) ^ p"
          by (rule power_mono[OF ge pos1])
        from order.strict_trans2[OF ineq1 ineq2]
        have "?n < of_int ((x + 1) ^ p)" unfolding x
          by (metis of_int_1 of_int_add of_int_power)
        thus "n < (x + 1) ^ p" using of_int_less_iff by blast
      qed
    qed
  next
    case True
    with rt have x: "x = y" by simp
    with 1(2) True have n: "n = y ^ p" by auto
    show ?thesis unfolding n x using y0 unfolding p
      by (metis add_le_less_mono add_less_cancel_left lessI less_add_one add.right_neutral le_iff_add power_strict_mono)
  qed
qed

lemma root_main'_upper:
  "x ^ p \<ge> n \<Longrightarrow> x \<ge> 0 \<Longrightarrow> n \<ge> 0 \<Longrightarrow> root_main' x n = (y,b) \<Longrightarrow> n < (y + 1) ^ p"
  using root_newton_int_main_upper[of n x y b] root_main'[of x n] by auto
end

text \<open>Now we can prove all the nice properties of @{const root_int_main}.\<close>

lemma root_int_main_all: assumes n: "n \<ge> 0"
  and rm: "root_int_main p n = (y,b)"
  shows "y \<ge> 0 \<and> b = (y ^ p = n) \<and> (p > 0 \<longrightarrow> y ^ p \<le> n \<and> n < (y + 1)^p)
    \<and> (p > 0 \<longrightarrow> x \<ge> 0 \<longrightarrow> x ^ p = n \<longrightarrow> y = x \<and> b)"
proof (cases "p = 0")
  case True
  with rm[unfolded root_int_main_def]
  have y: "y = 1" and b: "b = (n = 1)" by auto
  show ?thesis unfolding True y b using n by auto
next
  case False
  from False have p_0: "p > 0" by auto
  from False have "(p = 0) = False" by simp
  from rm[unfolded root_int_main_def this Let_def]
  have rm: "root_int_main' (p - 1) (int (p - 1)) (int p) (start_value n p) n = (y,b)" by simp
  from start_value[OF n p_0] have start: "n \<le> (start_value n p)^p" "0 \<le> start_value n p" by auto
  interpret fixed_root p "p - 1"
    by (unfold_locales, insert False, auto)
  from root_main'_pos[OF start(2) n rm] have y: "y \<ge> 0" .
  from root_main'_sound[OF start(2) n rm] have b: "b = (y ^ p = n)" .
  from root_main'_lower[OF start(2) n rm] have low: "y ^ p \<le> n" .
  from root_main'_upper[OF start n rm] have up: "n < (y + 1) ^ p" .
  {
    assume n: "x ^ p = n" and x: "x \<ge> 0"
    with low up have low: "y ^ p \<le> x ^ p" and up: "x ^ p < (y+1) ^ p" by auto
    from power_strict_mono[of x y, OF _ x p_0] low have x: "x \<ge> y" by arith
    from power_mono[of "(y + 1)" x p] y up have y: "y \<ge> x" by arith
    from x y have "x = y" by auto
    with b n
    have "y = x \<and> b" by auto
  }
  thus ?thesis using b low up y by auto
qed

lemma root_int_main: assumes n: "n \<ge> 0"
  and rm: "root_int_main p n = (y,b)"
  shows "y \<ge> 0" "b = (y ^ p = n)" "p > 0 \<Longrightarrow> y ^ p \<le> n" "p > 0 \<Longrightarrow> n < (y + 1)^p"
    "p > 0 \<Longrightarrow> x \<ge> 0 \<Longrightarrow> x ^ p = n \<Longrightarrow> y = x \<and> b"
  using root_int_main_all[OF n rm, of x] by blast+

lemma root_int[simp]: assumes p: "p \<noteq> 0 \<or> x \<noteq> 1"
  shows "set (root_int p x) = {y . y ^ p = x}"
proof (cases "p = 0")
  case True
  with p have "x \<noteq> 1" by auto
  thus ?thesis unfolding root_int_def True by auto
next
  case False
  hence p: "(p = 0) = False" and p0: "p > 0" by auto
  note d = root_int_def p if_False Let_def
  show ?thesis
  proof (cases "x = 0")
    case True
    thus ?thesis unfolding d using p0 by auto
  next
    case False
    hence x: "(x = 0) = False" by auto
    show ?thesis
    proof (cases "x < 0 \<and> even p")
      case True
      hence left: "set (root_int p x) = {}" unfolding d by auto
      {
        fix y
        assume x: "y ^ p = x"
        with True have "y ^ p < 0 \<and> even p" by auto
        hence False by presburger
      }
      with left show ?thesis by auto
    next
      case False
      with x p have cond: "(x = 0) = False" "(x < 0 \<and> even p) = False" by auto
      obtain y b where rt: "root_int_main p \<bar>x\<bar> = (y,b)" by force
      have "abs x \<ge> 0" by auto
      note rm = root_int_main[OF this rt]
      have "?thesis =
        (set (case root_int_main p \<bar>x\<bar> of (y, True) \<Rightarrow> if even p then [y, - y] else [sgn x * y] | (y, False) \<Rightarrow> []) =
        {y. y ^ p = x})" unfolding d cond by blast
      also have "(case root_int_main p \<bar>x\<bar> of (y, True) \<Rightarrow> if even p then [y, - y] else [sgn x * y] | (y, False) \<Rightarrow> [])
        = (if b then if even p then [y, - y] else [sgn x * y] else [])" (is "_ = ?lhs")
        unfolding rt by auto
      also have "set ?lhs = {y. y ^ p = x}" (is "_ = ?rhs")
      proof -
        {
          fix z
          assume idx: "z ^ p = x"
          hence eq: "(abs z) ^ p = abs x" by (metis power_abs)
          from idx x p0 have z: "z \<noteq> 0" unfolding p by auto
          have "(y, b) = (\<bar>z\<bar>, True)"
            using rm(5)[OF p0 _ eq] by auto
          hence id: "y = abs z" "b = True" by auto
          have "z \<in> set ?lhs" unfolding id using z by (auto simp: idx[symmetric], cases "z < 0", auto)
        }
        moreover
        {
          fix z
          assume z: "z \<in> set ?lhs"
          hence b: "b = True" by (cases b, auto)
          note z = z[unfolded b if_True]
          from rm(2) b have yx: "y ^ p = \<bar>x\<bar>" by auto
          from rm(1) have y: "y \<ge> 0" .
          from False have "odd p \<or> even p \<and> x \<ge> 0" by auto
          hence "z \<in> ?rhs"
          proof
            assume odd: "odd p"
            with z have "z = sgn x * y" by auto
            hence "z ^ p = (sgn x * y) ^ p" by auto
            also have "\<dots> = sgn x ^ p * y ^ p" unfolding power_mult_distrib by auto
            also have "\<dots> = sgn x ^ p * abs x" unfolding yx by simp
            also have "sgn x ^ p = sgn x" using x odd by auto
            also have "sgn x * abs x = x" by (rule mult_sgn_abs)
            finally show "z \<in> ?rhs" by auto
          next
            assume even: "even p \<and> x \<ge> 0"
            from z even have "z = y \<or> z = -y" by auto
            hence id: "abs z = y" using y by auto
            with yx x even have z: "z \<noteq> 0" using p0 by (cases "y = 0", auto)
            have "z ^ p = (sgn z * abs z) ^ p" by (simp add: mult_sgn_abs)
            also have "\<dots> = (sgn z * y) ^ p" using id by auto
            also have "\<dots> = (sgn z)^p * y ^ p" unfolding power_mult_distrib  by simp
            also have "\<dots> = sgn z ^ p * x" unfolding yx using even by auto
            also have "sgn z ^ p = 1" using even z by (auto)
            finally show "z \<in> ?rhs" by auto
          qed
        }
        ultimately show ?thesis by blast
      qed
      finally show ?thesis by auto
    qed
  qed
qed

lemma root_int_pos: assumes x: "x \<ge> 0" and ri: "root_int p x = y # ys"
  shows "y \<ge> 0"
proof -
  from x have abs: "abs x = x" by auto
  note ri = ri[unfolded root_int_def Let_def abs]
  from ri have p: "(p = 0) = False" by (cases p, auto)
  note ri = ri[unfolded p if_False]
  show ?thesis
  proof (cases "x = 0")
    case True
    with ri show ?thesis by auto
  next
    case False
    hence "(x = 0) = False" "(x < 0 \<and> even p) = False" using x by auto
    note ri = ri[unfolded this if_False]
    obtain y' b' where r: "root_int_main p x = (y',b')" by force
    note ri = ri[unfolded this]
    hence y: "y = (if even p then y' else sgn x * y')" by (cases b', auto)
    from root_int_main(1)[OF x r] have y': "0 \<le> y'" .
    thus ?thesis unfolding y using x False by auto
  qed
qed

subsection \<open>Floor and ceiling of roots\<close>

text \<open>Using the bounds for @{const root_int_main} we can easily design
  algorithms which compute @{term "floor (root p x)"} and @{term "ceiling (root p x)"}.
  To this end, we first develop algorithms for non-negative @{term x}, and later on
  these are used for the general case.\<close>

definition "root_int_floor_pos p x = (if p = 0 then 0 else fst (root_int_main p x))"
definition "root_int_ceiling_pos p x = (if p = 0 then 0 else (case root_int_main p x of (y,b) \<Rightarrow> if b then y else y + 1))"

lemma root_int_floor_pos_lower: assumes p0: "p \<noteq> 0" and x: "x \<ge> 0"
  shows "root_int_floor_pos p x ^ p \<le> x"
  using root_int_main(3)[OF x, of p] p0 unfolding root_int_floor_pos_def
  by (cases "root_int_main p x", auto)

lemma root_int_floor_pos_pos: assumes x: "x \<ge> 0"
  shows "root_int_floor_pos p x \<ge> 0"
  using root_int_main(1)[OF x, of p]
  unfolding root_int_floor_pos_def
  by (cases "root_int_main p x", auto)

lemma root_int_floor_pos_upper: assumes p0: "p \<noteq> 0" and x: "x \<ge> 0"
  shows "(root_int_floor_pos p x + 1) ^ p > x"
  using root_int_main(4)[OF x, of p] p0 unfolding root_int_floor_pos_def
  by (cases "root_int_main p x", auto)

lemma root_int_floor_pos: assumes x: "x \<ge> 0"
  shows "root_int_floor_pos p x = floor (root p (of_int x))"
proof (cases "p = 0")
  case True
  thus ?thesis by (simp add: root_int_floor_pos_def)
next
  case False
  hence p: "p > 0" by auto
  let ?s1 = "real_of_int (root_int_floor_pos p x)"
  let ?s2 = "root p (of_int x)"
  from x have s1: "?s1 \<ge> 0"
    by (metis of_int_0_le_iff root_int_floor_pos_pos)
  from x have s2: "?s2 \<ge> 0"
    by (metis of_int_0_le_iff real_root_pos_pos_le)
  from s1 have s11: "?s1 + 1 \<ge> 0" by auto
  have id: "?s2 ^ p = of_int x" using x
    by (metis p of_int_0_le_iff real_root_pow_pos2)
  show ?thesis
  proof (rule floor_unique[symmetric])
    show "?s1 \<le> ?s2"
      unfolding compare_pow_le_iff[OF p s1 s2, symmetric]
      unfolding id
      using root_int_floor_pos_lower[OF False x]
      by (metis of_int_le_iff of_int_power)
    show "?s2 < ?s1 + 1"
      unfolding compare_pow_less_iff[OF p s2 s11, symmetric]
      unfolding id
      using root_int_floor_pos_upper[OF False x]
      by (metis of_int_add of_int_less_iff of_int_power of_int_1)
  qed
qed

lemma root_int_ceiling_pos: assumes x: "x \<ge> 0"
  shows "root_int_ceiling_pos p x = ceiling (root p (of_int x))"
proof (cases "p = 0")
  case True
  thus ?thesis by (simp add: root_int_ceiling_pos_def)
next
  case False
  hence p: "p > 0" by auto
  obtain y b where s: "root_int_main p x = (y,b)" by force
  note rm = root_int_main[OF x s]
  note rm = rm(1-2) rm(3-5)[OF p]
  from rm(1) have y: "y \<ge> 0" by simp
  let ?s = "root_int_ceiling_pos p x"
  let ?sx = "root p (of_int x)"
  note d = root_int_ceiling_pos_def
  show ?thesis
  proof (cases b)
    case True
    hence id: "?s = y" unfolding s d using p by auto
    from rm(2) True have xy: "x = y ^ p" by auto
    show ?thesis unfolding id unfolding xy using y
      by (simp add: p real_root_power_cancel)
  next
    case False
    hence id: "?s = root_int_floor_pos p x + 1" unfolding d root_int_floor_pos_def
      using s p by simp
    from False have x0: "x \<noteq> 0" using rm(5)[of 0] using s unfolding root_int_main_def Let_def using p
      by (cases "x = 0", auto)
    show ?thesis unfolding id root_int_floor_pos[OF x]
    proof (rule ceiling_unique[symmetric])
      show "?sx \<le> real_of_int (\<lfloor>root p (of_int x)\<rfloor> + 1)"
        by (metis of_int_add real_of_int_floor_add_one_ge of_int_1)
      let ?l = "real_of_int (\<lfloor>root p (of_int x)\<rfloor> + 1) - 1"
      let ?m = "real_of_int \<lfloor>root p (of_int x)\<rfloor>"
      have "?l = ?m" by simp
      also have "\<dots> < ?sx"
      proof -
        have le: "?m \<le> ?sx" by (rule of_int_floor_le)
        have neq: "?m \<noteq> ?sx"
        proof
          assume "?m = ?sx"
          hence "?m ^ p = ?sx ^ p" by auto
          also have "\<dots> = of_int x" using x False
            by (metis p real_root_ge_0_iff real_root_pow_pos2 root_int_floor_pos root_int_floor_pos_pos zero_le_floor zero_less_Suc)
          finally have xs: "x = \<lfloor>root p (of_int x)\<rfloor> ^ p"
            by (metis floor_power floor_of_int)
          hence "\<lfloor>root p (of_int x)\<rfloor> \<in> set (root_int p x)" using p by simp
          hence "root_int p x \<noteq> []" by force
          with s False \<open>p \<noteq> 0\<close> x x0 show False unfolding root_int_def
            by (cases p, auto)
        qed
        from le neq show ?thesis by arith
      qed
      finally show "?l < ?sx" .
    qed
  qed
qed


definition "root_int_floor p x = (if x \<ge> 0 then root_int_floor_pos p x else - root_int_ceiling_pos p (- x))"
definition "root_int_ceiling p x = (if x \<ge> 0 then root_int_ceiling_pos p x else - root_int_floor_pos p (- x))"

lemma root_int_floor[simp]: "root_int_floor p x = floor (root p (of_int x))"
proof -
  note d = root_int_floor_def
  show ?thesis
  proof (cases "x \<ge> 0")
    case True
    with root_int_floor_pos[OF True, of p] show ?thesis unfolding d by simp
  next
    case False
    hence "- x \<ge> 0" by auto
    from False root_int_ceiling_pos[OF this] show ?thesis unfolding d
      by (simp add: real_root_minus ceiling_minus)
  qed
qed

lemma root_int_ceiling[simp]: "root_int_ceiling p x = ceiling (root p (of_int x))"
proof -
  note d = root_int_ceiling_def
  show ?thesis
  proof (cases "x \<ge> 0")
    case True
    with root_int_ceiling_pos[OF True] show ?thesis unfolding d by simp
  next
    case False
    hence "- x \<ge> 0" by auto
    from False root_int_floor_pos[OF this, of p] show ?thesis unfolding d
      by (simp add: real_root_minus floor_minus)
  qed
qed

subsection \<open>Downgrading algorithms to the naturals\<close>

definition root_nat_floor :: "nat \<Rightarrow> nat \<Rightarrow> int" where
  "root_nat_floor p x = root_int_floor_pos p (int x)"

definition root_nat_ceiling :: "nat \<Rightarrow> nat \<Rightarrow> int" where
  "root_nat_ceiling p x = root_int_ceiling_pos p (int x)"

definition root_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "root_nat p x = map nat (take 1 (root_int p x))"

lemma root_nat_floor [simp]: "root_nat_floor p x = floor (root p (real x))"
  unfolding root_nat_floor_def using root_int_floor_pos[of "int x" p]
  by auto

lemma root_nat_floor_lower: assumes p0: "p \<noteq> 0"
  shows "root_nat_floor p x ^ p \<le> x"
  using root_int_floor_pos_lower[OF p0, of x] unfolding root_nat_floor_def by auto

lemma root_nat_floor_upper: assumes p0: "p \<noteq> 0"
  shows "(root_nat_floor p x + 1) ^ p > x"
  using root_int_floor_pos_upper[OF p0, of x] unfolding root_nat_floor_def by auto

lemma root_nat_ceiling [simp]: "root_nat_ceiling p x = ceiling (root p x)"
  unfolding root_nat_ceiling_def using root_int_ceiling_pos[of x p]
  by auto

lemma root_nat: assumes p0: "p \<noteq> 0 \<or> x \<noteq> 1"
  shows "set (root_nat p x) = { y. y ^ p = x}"
proof -
  {
    fix y
    assume "y \<in> set (root_nat p x)"
    note y = this[unfolded root_nat_def]
    then obtain yi ys where ri: "root_int p x = yi # ys" by (cases "root_int p x", auto)
    with y have y: "y = nat yi" by auto
    from root_int_pos[OF _ ri] have yi: "0 \<le> yi" by auto
    from root_int[of p "int x"] p0 ri have "yi ^ p = x" by auto
    from arg_cong[OF this, of nat] yi have "nat yi ^ p = x"
      by (metis nat_int nat_power_eq)
    hence "y \<in> {y. y ^ p = x}" using y by auto
  }
  moreover
  {
    fix y
    assume yx: "y ^ p = x"
    hence y: "int y ^ p = int x"
      by (metis of_nat_power)
    hence "set (root_int p (int x)) \<noteq> {}" using root_int[of p "int x"] p0
      by (metis (mono_tags) One_nat_def \<open>y ^ p = x\<close> empty_Collect_eq nat_power_eq_Suc_0_iff)
    then obtain yi ys where ri: "root_int p (int x) = yi # ys"
      by (cases "root_int p (int x)", auto)
    from root_int_pos[OF _ this] have yip: "yi \<ge> 0" by auto
    from root_int[of p "int x", unfolded ri] p0 have yi: "yi ^ p = int x" by auto
    with y have "int y ^ p = yi ^ p" by auto
    from arg_cong[OF this, of nat] have id: "y ^ p = nat yi ^ p"
      by (metis \<open>y ^ p = x\<close> nat_int nat_power_eq yi yip)
    {
      assume p: "p \<noteq> 0"
      hence p0: "p > 0" by auto
      obtain yy b where rm: "root_int_main p (int x) = (yy,b)" by force
      from root_int_main(5)[OF _ rm p0 _ y] have "yy = int y" and "b = True" by auto
      note rm = rm[unfolded this]
      hence "y \<in> set (root_nat p x)"
        unfolding root_nat_def p root_int_def using p0 p yx
        by auto
    }
    moreover
    {
      assume p: "p = 0"
      with p0 have "x \<noteq> 1" by auto
      with y p have False by auto
    }
    ultimately have "y \<in> set (root_nat p x)" by auto
  }
  ultimately show ?thesis by blast
qed

subsection \<open>Upgrading algorithms to the rationals\<close>

text \<open>The main observation to lift everything from the integers to the rationals is the fact, that one
  can reformulate $\frac{a}{b}^{1/p}$ as $\frac{(ab^{p-1})^{1/p}}b$.\<close>

definition root_rat_floor :: "nat \<Rightarrow> rat \<Rightarrow> int" where
  "root_rat_floor p x \<equiv> case quotient_of x of (a,b) \<Rightarrow> root_int_floor p (a * b^(p - 1)) div b"

definition root_rat_ceiling :: "nat \<Rightarrow> rat \<Rightarrow> int" where
  "root_rat_ceiling p x \<equiv> - (root_rat_floor p (-x))"

definition root_rat :: "nat \<Rightarrow> rat \<Rightarrow> rat list" where
  "root_rat p x \<equiv> case quotient_of x of (a,b) \<Rightarrow> concat
  (map (\<lambda> rb. map (\<lambda> ra. of_int ra / rat_of_int rb) (root_int p a)) (take 1 (root_int p b)))"


lemma root_rat_reform: assumes q: "quotient_of x = (a,b)"
  shows "root p (real_of_rat x) = root p (of_int (a * b ^ (p - 1))) / of_int b"
proof (cases "p = 0")
  case False
  from quotient_of_denom_pos[OF q] have b: "0 < b" by auto
  hence b: "0 < real_of_int b" by auto
  from quotient_of_div[OF q] have x: "root p (real_of_rat x) = root p (a / b)"
    by (metis of_rat_divide of_rat_of_int_eq)
  also have "a / b = a * real_of_int b ^ (p - 1) / of_int b ^ p" using b False
    by (cases p, auto simp: field_simps)
  also have "root p \<dots> = root p (a * real_of_int b ^ (p - 1)) / root p (of_int b ^ p)" by (rule real_root_divide)
  also have "root p (of_int b ^ p) = of_int b" using False b
    by (metis neq0_conv real_root_pow_pos real_root_power)
  also have "a * real_of_int b ^ (p - 1) = of_int (a * b ^ (p - 1))"
    by (metis of_int_mult of_int_power)
  finally show ?thesis .
qed auto

lemma root_rat_floor [simp]: "root_rat_floor p x = floor (root p (of_rat x))"
proof -
  obtain a b where q: "quotient_of x = (a,b)" by force
  from quotient_of_denom_pos[OF q] have b: "b > 0" .
  show ?thesis
    unfolding root_rat_floor_def q split root_int_floor
    unfolding root_rat_reform[OF q] floor_div_pos_int[OF b] ..
qed

lemma root_rat_ceiling [simp]: "root_rat_ceiling p x = ceiling (root p (of_rat x))"
  unfolding
    root_rat_ceiling_def
    ceiling_def
    real_root_minus
    root_rat_floor
    of_rat_minus
    ..

lemma root_rat[simp]: assumes p: "p \<noteq> 0 \<or> x \<noteq> 1"
  shows "set (root_rat p x) = { y. y ^ p = x}"
proof (cases "p = 0")
  case False
  note p = this
  obtain a b where q: "quotient_of x = (a,b)" by force
  note x = quotient_of_div[OF q]
  have b: "b > 0" by (rule quotient_of_denom_pos[OF q])
  note d = root_rat_def q split set_concat set_map
  {
    fix q
    assume "q \<in> set (root_rat p x)"
    note mem = this[unfolded d]
    from mem obtain rb xs where rb: "root_int p b = Cons rb xs" by (cases "root_int p b", auto)
    note mem = mem[unfolded this]
    from mem obtain ra where ra: "ra \<in> set (root_int p a)" and q: "q = of_int ra / of_int rb"
      by (cases "root_int p a", auto)
    from rb have "rb \<in> set (root_int p b)" by auto
    with ra p have rb: "b = rb ^ p" and ra: "a = ra ^ p" by auto
    have "q \<in> {y. y ^ p = x}" unfolding q x ra rb
      by (auto simp: power_divide)
  }
  moreover
  {
    fix q
    assume "q \<in> {y. y ^ p = x}"
    hence "q ^ p = of_int a / of_int b" unfolding x by auto
    hence eq: "of_int b * q ^ p = of_int a" using b by auto
    obtain z n where quo: "quotient_of q = (z,n)" by force
    note qzn = quotient_of_div[OF quo]
    have n: "n > 0" using quotient_of_denom_pos[OF quo] .
    from eq[unfolded qzn] have "rat_of_int b * of_int z^p / of_int n^p = of_int a"
      unfolding power_divide by simp
    from arg_cong[OF this, of "\<lambda> x. x * of_int n^p"] n have "rat_of_int b * of_int z^p = of_int a * of_int n ^ p"
      by auto
    also have "rat_of_int b * of_int z^p = rat_of_int (b * z^p)" unfolding of_int_mult of_int_power ..
    also have "of_int a * rat_of_int n ^ p = of_int (a * n ^ p)" unfolding of_int_mult of_int_power ..
    finally have id: "a * n ^ p = b * z ^ p" by linarith
    from quotient_of_coprime[OF quo] have cop: "coprime (z ^ p) (n ^ p)"
      by simp
    from coprime_crossproduct_int[OF quotient_of_coprime[OF q] this] arg_cong[OF id, of abs]
    have "\<bar>n ^ p\<bar> = \<bar>b\<bar>"
      by (simp add: field_simps abs_mult)
    with n b have bnp: "b = n ^ p" by auto
    hence rn: "n \<in> set (root_int p b)" using p by auto
    then obtain rb rs where rb: "root_int p b = Cons rb rs" by (cases "root_int p b", auto)
    from id[folded bnp] b have "a = z ^ p" by auto
    hence a: "z \<in> set (root_int p a)" using p by auto
    from root_int_pos[OF _ rb] b have rb0: "rb \<ge> 0" by auto
    from root_int[OF disjI1[OF p], of b] rb have "rb ^ p = b" by auto
    with bnp have id: "rb ^ p = n ^ p" by auto
    have "rb = n" by (rule power_eq_imp_eq_base[OF id], insert n rb0 p, auto)
    with rb have b: "n \<in> set (take 1 (root_int p b))" by auto
    have "q \<in> set (root_rat p x)" unfolding d qzn using b a by auto
  }
  ultimately show ?thesis by blast
next
  case True
  with p have x: "x \<noteq> 1" by auto
  obtain a b where q: "quotient_of x = (a,b)" by force
  show ?thesis unfolding True root_rat_def q split root_int_def using x
    by auto
qed

end
