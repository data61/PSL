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

theory Sqrt_Babylonian
imports 
  Sqrt_Babylonian_Auxiliary
  NthRoot_Impl
begin

section \<open>Executable algorithms for square roots\<close>

text \<open>
  This theory provides executable algorithms for computing square-roots of numbers which
  are all based on the Babylonian method (which is also known as Heron's method or Newton's method).
  
  For integers / naturals / rationals precise algorithms are given, i.e., here $sqrt\ x$ delivers
  a list of all integers / naturals / rationals $y$ where $y^2 = x$. 
  To this end, the Babylonian method has been adapted by using integer-divisions.

  In addition to the precise algorithms, we also provide approximation algorithms. One works for 
  arbitrary linear ordered fields, where some number $y$ is computed such that
  @{term "abs(y^2 - x) < \<epsilon>"}. Moreover, for the naturals, integers, and rationals we provide algorithms to compute
  @{term "floor (sqrt x)"} and @{term "ceiling (sqrt x)"} which are all based
  on the underlying algorithm that is used to compute the precise square-roots on integers, if these 
  exist.

  The major motivation for developing the precise algorithms was given by \ceta{} \cite{CeTA},
  a tool for certifiying termination proofs. Here, non-linear equations of the form
  $(a_1x_1 + \dots a_nx_n)^2 = p$ had to be solved over the integers, where $p$ is a concrete polynomial.
  For example, for the equation $(ax + by)^2 = 4x^2 - 12xy + 9y^2$ one easily figures out that
  $a^2 = 4, b^2 = 9$, and $ab = -6$, which results in a possible solution $a = \sqrt 4 = 2, b = - \sqrt 9 = -3$.
\<close>

subsection \<open>The Babylonian method\<close>

text \<open>
The Babylonian method for computing $\sqrt n$ iteratively computes 
\[
x_{i+1} = \frac{\frac n{x_i} + x_i}2
\]
until $x_i^2 \approx n$. Note that if $x_0^2 \geq n$, then for all $i$ we have both
$x_i^2 \geq n$ and $x_i \geq x_{i+1}$. 
\<close>

subsection \<open>The Babylonian method using integer division\<close>
text \<open>
  First, the algorithm is developed for the non-negative integers.
  Here, the division operation $\frac xy$ is replaced by @{term "x div y = \<lfloor>of_int x / of_int y\<rfloor>"}.
  Note that replacing @{term "\<lfloor>of_int x / of_int y\<rfloor>"} by @{term "\<lceil>of_int x / of_int y\<rceil>"} would lead to non-termination
  in the following algorithm.

  We explicititly develop the algorithm on the integers and not on the naturals, as the calculations
  on the integers have been much easier. For example, $y - x + x = y$ on the integers, which would require
  the side-condition $y \geq x$ for the naturals. These conditions will make the reasoning much more tedious---as
  we have experienced in an earlier state of this development where everything was based on naturals.

  Since the elements
  $x_0, x_1, x_2,\dots$ are monotone decreasing, in the main algorithm we abort as soon as $x_i^2 \leq n$.\<close>


text \<open>\textbf{Since in the meantime, all of these algorithms have been generalized to arbitrary
  $p$-th roots in @{theory Sqrt_Babylonian.NthRoot_Impl}, we just instantiate the general algorithms by $p = 2$ and then provide 
  specialized code equations which are more efficient than the general purpose algorithms.}\<close>

definition sqrt_int_main' :: "int \<Rightarrow> int \<Rightarrow> int \<times> bool" where
  [simp]: "sqrt_int_main' x n = root_int_main' 1 1 2 x n"

lemma sqrt_int_main'_code[code]: "sqrt_int_main' x n = (let x2 = x * x in if x2 \<le> n then (x, x2 = n)
    else sqrt_int_main' ((n div x + x) div 2) n)"
  using root_int_main'.simps[of 1 1 2 x n]
  unfolding Let_def by auto

definition sqrt_int_main :: "int \<Rightarrow> int \<times> bool" where
  [simp]: "sqrt_int_main x = root_int_main 2 x"

lemma sqrt_int_main_code[code]: "sqrt_int_main x = sqrt_int_main' (start_value x 2) x"
  by (simp add: root_int_main_def Let_def)

definition sqrt_int :: "int \<Rightarrow> int list" where
  "sqrt_int x = root_int 2 x"

lemma sqrt_int_code[code]: "sqrt_int x = (if x < 0 then [] else case sqrt_int_main x of (y,True) \<Rightarrow> if y = 0 then [0] else [y,-y] | _ \<Rightarrow> [])"
proof -
  interpret fixed_root 2 1 by (unfold_locales, auto)
  obtain b y where res: "root_int_main 2 x = (b,y)" by force
  show ?thesis
    unfolding sqrt_int_def root_int_def Let_def
    using root_int_main[OF _ res]
    using res
    by simp
qed

lemma sqrt_int[simp]: "set (sqrt_int x) = {y. y * y = x}"
  unfolding sqrt_int_def by (simp add: power2_eq_square)


lemma sqrt_int_pos: assumes res: "sqrt_int x = Cons s ms"
  shows "s \<ge> 0"
proof -
  note res = res[unfolded sqrt_int_code Let_def, simplified]
  from res have x0: "x \<ge> 0" by (cases ?thesis, auto)
  obtain ss b where call: "sqrt_int_main x = (ss,b)" by force
  from res[unfolded call] x0 have "ss = s" 
    by (cases b, cases "ss = 0", auto)
  from root_int_main(1)[OF x0 call[unfolded this sqrt_int_main_def]]
  show ?thesis .
qed

definition [simp]: "sqrt_int_floor_pos x = root_int_floor_pos 2 x"

lemma sqrt_int_floor_pos_code[code]: "sqrt_int_floor_pos x = fst (sqrt_int_main x)"
  by (simp add: root_int_floor_pos_def)

lemma sqrt_int_floor_pos: assumes x: "x \<ge> 0" 
  shows "sqrt_int_floor_pos x = \<lfloor> sqrt (of_int x) \<rfloor>"
  using root_int_floor_pos[OF x, of 2] by (simp add: sqrt_def)

definition [simp]: "sqrt_int_ceiling_pos x = root_int_ceiling_pos 2 x"

lemma sqrt_int_ceiling_pos_code[code]: "sqrt_int_ceiling_pos x = (case sqrt_int_main x of (y,b) \<Rightarrow> if b then y else y + 1)"
  by (simp add: root_int_ceiling_pos_def)

lemma sqrt_int_ceiling_pos: assumes x: "x \<ge> 0" 
  shows "sqrt_int_ceiling_pos x = \<lceil> sqrt (of_int x) \<rceil>"
  using root_int_ceiling_pos[OF x, of 2] by (simp add: sqrt_def)

definition "sqrt_int_floor x = root_int_floor 2 x"

lemma sqrt_int_floor_code[code]: "sqrt_int_floor x = (if x \<ge> 0 then sqrt_int_floor_pos x else - sqrt_int_ceiling_pos (- x))"
  unfolding sqrt_int_floor_def root_int_floor_def by simp

lemma sqrt_int_floor[simp]: "sqrt_int_floor x = \<lfloor> sqrt (of_int x) \<rfloor>"
  by (simp add: sqrt_int_floor_def sqrt_def)

definition "sqrt_int_ceiling x = root_int_ceiling 2 x"

lemma sqrt_int_ceiling_code[code]: "sqrt_int_ceiling x = (if x \<ge> 0 then sqrt_int_ceiling_pos x else - sqrt_int_floor_pos (- x))"
  unfolding sqrt_int_ceiling_def root_int_ceiling_def by simp

lemma sqrt_int_ceiling[simp]: "sqrt_int_ceiling x = \<lceil> sqrt (of_int x) \<rceil>"
  by (simp add: sqrt_int_ceiling_def sqrt_def)

lemma sqrt_int_ceiling_bound: "0 \<le> x \<Longrightarrow> x \<le> (sqrt_int_ceiling x)^2"
  unfolding sqrt_int_ceiling using le_of_int_ceiling sqrt_le_D
  by (metis of_int_power_le_of_int_cancel_iff)


subsection \<open>Square roots for the naturals\<close>


definition sqrt_nat :: "nat \<Rightarrow> nat list"
  where "sqrt_nat x = root_nat 2 x"
 
lemma sqrt_nat_code[code]: "sqrt_nat x \<equiv> map nat (take 1 (sqrt_int (int x)))"
  unfolding sqrt_nat_def root_nat_def sqrt_int_def by simp

lemma sqrt_nat[simp]: "set (sqrt_nat x) = { y. y * y = x}" 
  unfolding sqrt_nat_def using root_nat[of 2 x] by (simp add: power2_eq_square)

definition sqrt_nat_floor :: "nat \<Rightarrow> int" where
  "sqrt_nat_floor x = root_nat_floor 2 x"

lemma sqrt_nat_floor_code[code]: "sqrt_nat_floor x = sqrt_int_floor_pos (int x)"
  unfolding sqrt_nat_floor_def root_nat_floor_def by simp

lemma sqrt_nat_floor[simp]: "sqrt_nat_floor x = \<lfloor> sqrt (real x) \<rfloor>"
  unfolding sqrt_nat_floor_def by (simp add: sqrt_def)

definition sqrt_nat_ceiling :: "nat \<Rightarrow> int" where
  "sqrt_nat_ceiling x = root_nat_ceiling 2 x"

lemma sqrt_nat_ceiling_code[code]: "sqrt_nat_ceiling x = sqrt_int_ceiling_pos (int x)"
  unfolding sqrt_nat_ceiling_def root_nat_ceiling_def by simp

lemma sqrt_nat_ceiling[simp]: "sqrt_nat_ceiling x = \<lceil> sqrt (real x) \<rceil>"
  unfolding sqrt_nat_ceiling_def by (simp add: sqrt_def)

subsection \<open>Square roots for the rationals\<close>

definition sqrt_rat :: "rat \<Rightarrow> rat list" where
  "sqrt_rat x = root_rat 2 x"

lemma sqrt_rat_code[code]: "sqrt_rat x = (case quotient_of x of (z,n) \<Rightarrow> (case sqrt_int n of 
    [] \<Rightarrow> [] 
  | sn # xs \<Rightarrow> map (\<lambda> sz. of_int sz / of_int sn) (sqrt_int z)))"
proof -
  obtain z n where q: "quotient_of x = (z,n)" by force
  show ?thesis
  unfolding sqrt_rat_def root_rat_def q split sqrt_int_def
  by (cases "root_int 2 n", auto)
qed

lemma sqrt_rat[simp]: "set (sqrt_rat x) = { y. y * y = x}"
  unfolding sqrt_rat_def using root_rat[of 2 x]
  by (simp add: power2_eq_square)

lemma sqrt_rat_pos: assumes sqrt: "sqrt_rat x = Cons s ms" 
  shows "s \<ge> 0"
proof -
  obtain z n where q: "quotient_of x = (z,n)" by force
  note sqrt = sqrt[unfolded sqrt_rat_code q, simplified]
  let ?sz = "sqrt_int z"
  let ?sn = "sqrt_int n"
  from q have n: "n > 0" by (rule quotient_of_denom_pos)
  from sqrt obtain sz mz where sz: "?sz = sz # mz" by (cases ?sn, auto)
  from sqrt obtain sn mn where sn: "?sn = sn # mn" by (cases ?sn, auto)
  from sqrt_int_pos[OF sz] sqrt_int_pos[OF sn] have pos: "0 \<le> sz" "0 \<le> sn" by auto
  from sqrt sz sn have s: "s = of_int sz / of_int sn" by auto
  show ?thesis unfolding s using pos
    by (metis of_int_0_le_iff zero_le_divide_iff)
qed

definition sqrt_rat_floor :: "rat \<Rightarrow> int" where
  "sqrt_rat_floor x = root_rat_floor 2 x"

lemma sqrt_rat_floor_code[code]: "sqrt_rat_floor x = (case quotient_of x of (a,b) \<Rightarrow> sqrt_int_floor (a * b) div b)"
  unfolding sqrt_rat_floor_def root_rat_floor_def by (simp add: sqrt_def)

lemma sqrt_rat_floor[simp]: "sqrt_rat_floor x = \<lfloor> sqrt (of_rat x) \<rfloor>"
  unfolding sqrt_rat_floor_def by (simp add: sqrt_def)

definition sqrt_rat_ceiling :: "rat \<Rightarrow> int" where
  "sqrt_rat_ceiling x = root_rat_ceiling 2 x"

lemma sqrt_rat_ceiling_code[code]: "sqrt_rat_ceiling x = - (sqrt_rat_floor (-x))"
  unfolding sqrt_rat_ceiling_def sqrt_rat_floor_def root_rat_ceiling_def by simp

lemma sqrt_rat_ceiling: "sqrt_rat_ceiling x = \<lceil> sqrt (of_rat x) \<rceil>"
  unfolding sqrt_rat_ceiling_def by (simp add: sqrt_def)

lemma sqr_rat_of_int: assumes x: "x * x = rat_of_int i"
  shows "\<exists> j :: int. j * j = i"
proof -
  from x have mem: "x \<in> set (sqrt_rat (rat_of_int i))" by simp
  from x have "rat_of_int i \<ge> 0" by (metis zero_le_square)
  hence *: "quotient_of (rat_of_int i) = (i,1)" by (metis quotient_of_int)
  have 1: "sqrt_int 1 = [1,-1]" by code_simp
  from mem sqrt_rat_code * split 1 
  have x: "x \<in> rat_of_int ` {y. y * y = i}" by auto
  thus ?thesis by auto
qed

subsection \<open>Approximating square roots\<close>

text \<open>
  The difference to the previous algorithms is that now we abort, once the distance is below
  $\epsilon$.  
  Moreover, here we use standard division and not integer division.
  This part is not yet generalized by @{theory Sqrt_Babylonian.NthRoot_Impl}.

  We first provide the executable version without guard @{term "x > 0"} as partial function,
  and afterwards prove termination and soundness for a similar algorithm that is defined within the upcoming
locale.
\<close>

partial_function (tailrec) sqrt_approx_main_impl :: "'a :: linordered_field \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where 
  [code]: "sqrt_approx_main_impl \<epsilon> n x = (if x * x - n < \<epsilon> then x else sqrt_approx_main_impl \<epsilon> n 
    ((n / x + x) / 2))"

text \<open>We setup a locale where we ensure that we have standard assumptions: positive $\epsilon$ and
  positive $n$. We require sort @{term floor_ceiling}, since @{term "\<lfloor> x \<rfloor>"} is used for the termination
  argument.\<close>
locale sqrt_approximation = 
  fixes \<epsilon> :: "'a :: {linordered_field,floor_ceiling}"
  and n :: 'a
  assumes \<epsilon> : "\<epsilon> > 0"
  and n: "n > 0"
begin

function sqrt_approx_main :: "'a \<Rightarrow> 'a" where 
  "sqrt_approx_main x = (if x > 0 then (if x * x - n < \<epsilon> then x else sqrt_approx_main 
    ((n / x + x) / 2)) else 0)"
    by pat_completeness auto

text \<open>Termination essentially is a proof of convergence. Here, one complication is the fact
  that the limit is not always defined. E.g., if @{typ "'a"} is @{typ rat} then there is no
  square root of 2. Therefore, the error-rate $\frac x{\sqrt n} - 1$ is not expressible. 
  Instead we use the expression $\frac{x^2}n - 1$ as error-rate which
  does not require any square-root operation.\<close>
termination
proof -
  define er where "er x = (x * x / n - 1)" for x
  define c where "c = 2 * n / \<epsilon>"
  define m where "m x = nat \<lfloor> c * er x \<rfloor>" for x
  have c: "c > 0" unfolding c_def using n \<epsilon> by auto
  show ?thesis
  proof
    show "wf (measures [m])" by simp
  next
    fix x 
    assume x: "0 < x" and xe: "\<not> x * x - n < \<epsilon>"
    define y where "y = (n / x + x) / 2"    
    show "((n / x + x) / 2,x) \<in> measures [m]" unfolding y_def[symmetric]
    proof (rule measures_less)
      from n have inv_n: "1 / n > 0" by auto
      from xe have "x * x - n \<ge> \<epsilon>" by simp
      from this[unfolded mult_le_cancel_left_pos[OF inv_n, of \<epsilon>, symmetric]]
      have erxen: "er x \<ge> \<epsilon> / n" unfolding er_def using n by (simp add: field_simps)
      have en: "\<epsilon> / n > 0" and ne: "n / \<epsilon> > 0" using \<epsilon> n by auto
      from en erxen have erx: "er x > 0" by linarith
      have pos: "er x * 4 + er x * (er x * 4) > 0" using erx
        by (auto intro: add_pos_nonneg)
      have "er y = 1 / 4 * (n / (x * x) - 2  + x * x / n)" unfolding er_def y_def using x n
        by (simp add: field_simps)
      also have "\<dots> = 1 / 4 * er x * er x / (1 + er x)" unfolding er_def using x n
        by (simp add: field_simps)
      finally have "er y = 1 / 4 * er x * er x / (1 + er x)" .
      also have "\<dots> < 1 / 4 * (1 + er x) * er x / (1 + er x)" using erx erx pos
        by (auto simp: field_simps)
      also have "\<dots> = er x / 4" using erx by (simp add: field_simps)
      finally have er_y_x: "er y \<le> er x / 4" by linarith
      from erxen have "c * er x \<ge> 2" unfolding c_def mult_le_cancel_left_pos[OF ne, of _ "er x", symmetric]
        using n \<epsilon> by (auto simp: field_simps)
      hence pos: "\<lfloor>c * er x\<rfloor> > 0" "\<lfloor>c * er x\<rfloor> \<ge> 2" by auto
      show "m y < m x" unfolding m_def nat_mono_iff[OF pos(1)]
      proof -      
        have "\<lfloor>c * er y\<rfloor> \<le> \<lfloor>c * (er x / 4)\<rfloor>"
          by (rule floor_mono, unfold mult_le_cancel_left_pos[OF c], rule er_y_x)
        also have "\<dots> < \<lfloor>c * er x / 4 + 1\<rfloor>" by auto
        also have "\<dots> \<le> \<lfloor>c * er x\<rfloor>"
          by (rule floor_mono, insert pos(2), simp add: field_simps)
        finally show "\<lfloor>c * er y\<rfloor> < \<lfloor>c * er x\<rfloor>" .
      qed
    qed
  qed
qed

text \<open>Once termination is proven, it is easy to show equivalence of 
  @{const sqrt_approx_main_impl} and @{const sqrt_approx_main}.\<close>
lemma sqrt_approx_main_impl: "x > 0 \<Longrightarrow> sqrt_approx_main_impl \<epsilon> n x = sqrt_approx_main x"
proof (induct x rule: sqrt_approx_main.induct)
  case (1 x)
  hence x: "x > 0" by auto
  hence nx: "0 < (n / x + x) / 2" using n by (auto intro: pos_add_strict)
  note simps = sqrt_approx_main_impl.simps[of _ _ x] sqrt_approx_main.simps[of x]
  show ?case 
  proof (cases "x * x - n < \<epsilon>")
    case True
    thus ?thesis unfolding simps using x by auto
  next
    case False
    show ?thesis using 1(1)[OF x False nx] unfolding simps using x False by auto
  qed
qed

text \<open>Also soundness is not complicated.\<close>

lemma sqrt_approx_main_sound: assumes x: "x > 0" and xx: "x * x > n"
  shows "sqrt_approx_main x * sqrt_approx_main x > n \<and> sqrt_approx_main x * sqrt_approx_main x - n < \<epsilon>"
  using assms
proof (induct x rule: sqrt_approx_main.induct)
  case (1 x)
  from 1 have x:  "x > 0" "(x > 0) = True" by auto
  note simp = sqrt_approx_main.simps[of x, unfolded x if_True]
  show ?case
  proof (cases "x * x - n < \<epsilon>")
    case True
    with 1 show ?thesis unfolding simp by simp
  next
    case False
    let ?y = "(n / x + x) / 2"
    from False simp have simp: "sqrt_approx_main x = sqrt_approx_main ?y" by simp
    from n x have y: "?y > 0" by (auto intro: pos_add_strict)
    note IH = 1(1)[OF x(1) False y]
    from x have x4: "4 * x * x > 0" by (auto intro: mult_sign_intros)
    show ?thesis unfolding simp
    proof (rule IH)
      show "n < ?y * ?y"
        unfolding mult_less_cancel_left_pos[OF x4, of n, symmetric]
      proof -
        have id: "4 * x * x * (?y * ?y) = 4 * x * x * n + (n - x * x) * (n - x * x)" using x(1)
          by (simp add: field_simps)
        from 1(3) have "x * x - n > 0" by auto
        from mult_pos_pos[OF this this]
        show "4 * x * x * n < 4 * x * x * (?y * ?y)" unfolding id 
          by (simp add: field_simps)
      qed
    qed
  qed
qed   

end

text \<open>It remains to assemble everything into one algorithm.\<close>

definition sqrt_approx :: "'a :: {linordered_field,floor_ceiling} \<Rightarrow> 'a \<Rightarrow> 'a" where
  "sqrt_approx \<epsilon> x \<equiv> if \<epsilon> > 0 then (if x = 0 then 0 else let xpos = abs x in sqrt_approx_main_impl \<epsilon> xpos (xpos + 1)) else 0"


lemma sqrt_approx: assumes \<epsilon>: "\<epsilon> > 0"
  shows "\<bar>sqrt_approx \<epsilon> x * sqrt_approx \<epsilon> x - \<bar>x\<bar>\<bar> < \<epsilon>"
proof (cases "x = 0")
  case True
  with \<epsilon> show ?thesis unfolding sqrt_approx_def by auto
next
  case False
  let ?x = "\<bar>x\<bar>" 
  let ?sqrti = "sqrt_approx_main_impl \<epsilon> ?x (?x + 1)"
  let ?sqrt = "sqrt_approximation.sqrt_approx_main \<epsilon> ?x (?x + 1)"
  define sqrt where "sqrt = ?sqrt"
  from False have x: "?x > 0" "?x + 1 > 0" by auto
  interpret sqrt_approximation \<epsilon> ?x
    by (unfold_locales, insert x \<epsilon>, auto)
  from False \<epsilon> have "sqrt_approx \<epsilon> x = ?sqrti" unfolding sqrt_approx_def by (simp add: Let_def)
  also have "?sqrti = ?sqrt"
    by (rule sqrt_approx_main_impl, auto)
  finally have id: "sqrt_approx \<epsilon> x = sqrt" unfolding sqrt_def .
  have sqrt: "sqrt * sqrt > ?x \<and> sqrt * sqrt - ?x < \<epsilon>" unfolding sqrt_def
    by (rule sqrt_approx_main_sound[OF x(2)], insert x mult_pos_pos[OF x(1) x(1)], auto simp: field_simps)
  show ?thesis unfolding id using sqrt by auto
qed

subsection \<open>Some tests\<close>

text \<open>Testing executabity and show that sqrt 2 is irrational\<close>
lemma "\<not> (\<exists> i :: rat. i * i = 2)"
proof -
  have "set (sqrt_rat 2) = {}" by eval
  thus ?thesis by simp
qed

text \<open>Testing speed\<close>
lemma "\<not> (\<exists> i :: int. i * i = 1234567890123456789012345678901234567890)"
proof -
  have "set (sqrt_int 1234567890123456789012345678901234567890) = {}" by eval
  thus ?thesis by simp
qed

text \<open>The following test\<close>

value "let \<epsilon> = 1 / 100000000 :: rat; s = sqrt_approx \<epsilon> 2 in (s, s * s - 2, \<bar>s * s - 2\<bar> < \<epsilon>)"

text \<open>results in (1.4142135623731116, 4.738200762148612e-14, True).\<close>
 
end
