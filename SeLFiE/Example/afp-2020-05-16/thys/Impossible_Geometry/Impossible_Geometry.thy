(* Title:       Proving the impossibility of trisecting an angle and doubling the cube
   Authors:     Ralph Romanos <ralph.romanos at student.ecp.fr> (2012),
                Lawrence Paulson <lp15 at cam.ac.uk> (2012)
   Maintainer:  Ralph Romanos <ralph.romanos at student.ecp.fr>
*)

section \<open>Proving the impossibility of trisecting an angle and doubling the cube\<close>

theory Impossible_Geometry
imports Complex_Main
begin

section \<open>Formal Proof\<close>

subsection \<open>Definition of the set of Points\<close>

datatype point = Point real real

definition points_def:
  "points = {M. \<exists> x \<in> \<real>. \<exists> y \<in> \<real>. (M = Point x y)}"

primrec abscissa :: "point => real"
  where abscissa: "abscissa (Point x y) = x"

primrec ordinate :: "point => real"
  where ordinate: "ordinate (Point x y) = y"

lemma point_surj [simp]:
  "Point (abscissa M) (ordinate M) = M"
  by (induct M) simp

lemma point_eqI [intro?]:
  "\<lbrakk>abscissa M = abscissa N; ordinate M = ordinate N\<rbrakk> \<Longrightarrow> M = N"
  by (induct M, induct N) simp

lemma point_eq_iff:
  "M = N \<longleftrightarrow> abscissa M = abscissa N \<and> ordinate M = ordinate N"
  by (induct M, induct N) simp

subsection \<open>Subtraction\<close>

text \<open>Datatype point has a structure of abelian group\<close>

instantiation point :: ab_group_add
begin

definition point_zero_def:
  "0 = Point 0 0"

definition point_one_def:
  "point_one = Point 1 0"

definition point_add_def:
  "A + B = Point (abscissa A + abscissa B) (ordinate A + ordinate B)"

definition point_minus_def:
  "- A = Point (- abscissa A) (- ordinate A)"

definition point_diff_def:
  "A - (B::point) = A + - B"

lemma Point_eq_0 [simp]:
  "Point xA yA = 0 \<longleftrightarrow> (xA = 0 \<and> yA = 0)"
  by (simp add: point_zero_def)

lemma point_abscissa_zero [simp]:
  "abscissa 0 = 0"
  by (simp add: point_zero_def)

lemma point_ordinate_zero [simp]:
  "ordinate 0 = 0"
  by (simp add: point_zero_def)

lemma point_add [simp]:
  "Point xA yA + Point xB yB = Point (xA + xB) (yA + yB)"
  by (simp add: point_add_def)

lemma point_abscissa_add [simp]:
  "abscissa (A + B) = abscissa A + abscissa B"
  by (simp add: point_add_def)

lemma point_ordinate_add [simp]:
  "ordinate (A + B) = ordinate A + ordinate B"
  by (simp add: point_add_def)

lemma point_minus [simp]:
  "- (Point xA yA) = Point (- xA) (- yA)"
  by (simp add: point_minus_def)

lemma point_abscissa_minus [simp]:
  "abscissa (- A) = - abscissa (A)"
  by (simp add: point_minus_def)

lemma point_ordinate_minus [simp]:
  "ordinate (- A) = - ordinate (A)"
  by (simp add: point_minus_def)

lemma point_diff [simp]:
  "Point xA yA - Point xB yB = Point (xA - xB) (yA - yB)"
  by (simp add: point_diff_def)

lemma point_abscissa_diff [simp]:
  "abscissa (A - B) = abscissa (A) - abscissa (B)"
  by (simp add: point_diff_def)

lemma point_ordinate_diff [simp]:
  "ordinate (A - B) = ordinate (A) - ordinate (B)"
  by (simp add: point_diff_def)

instance
  by intro_classes (simp_all add: point_add_def point_diff_def)

end

subsection \<open>Metric Space\<close>

text \<open>We can also define a distance, hence point is also a metric space\<close>

instantiation point :: metric_space
begin

definition point_dist_def:
  "dist A B =  sqrt ((abscissa (A - B))^2 + (ordinate (A - B))^2)"

definition
  "(uniformity :: (point \<times> point) filter) = (INF e\<in>{0 <..}. principal {(x, y). dist x y < e})"

definition
  "open (S :: point set) = (\<forall>x\<in>S. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> S)"

lemma point_dist [simp]:
  "dist (Point xA yA) (Point xB yB) =  sqrt ((xA - xB)^2 + (yA - yB)^2)"
  unfolding point_dist_def
  by simp

lemma real_sqrt_diff_squares_triangle_ineq:
  fixes a b c d :: real
  shows "sqrt ((a - c)^2 + (b - d)^2) \<le> sqrt (a^2 + b^2) + sqrt (c^2 + d^2)"
proof -
  have "sqrt ((a - c)^2 + (b - d)^2) \<le> sqrt (a^2 + b^2) + sqrt ((-c)^2 + (-d)^2)"
    by (metis diff_conv_add_uminus real_sqrt_sum_squares_triangle_ineq)
  also have "... = sqrt (a^2 + b^2) + sqrt (c^2 + d^2)"
    by simp
  finally show ?thesis .
qed

instance
proof
  fix A B C :: point and S :: "point set"
  show "(dist A B = 0) = (A = B)"
    by (induct A, induct B) (simp add: point_dist_def)
  show "(dist A B) \<le> (dist A C) + (dist B C)"
  proof -
    have "sqrt ((abscissa (A - B))^2 + (ordinate (A - B))^2) \<le>
          sqrt ((abscissa (A - C))^2 + (ordinate (A - C))^2) +
          sqrt ((abscissa (B - C))^2 + (ordinate (B - C))^2)"
      using real_sqrt_diff_squares_triangle_ineq
             [of "abscissa (A) - abscissa (C)" "abscissa (B) - abscissa (C)"
                 "ordinate (A) - ordinate (C)" "ordinate (B) - ordinate (C)"]
      by (simp only: point_diff_def) (simp add: algebra_simps)
    thus ?thesis
      by (simp add: point_dist_def)
  qed
qed (rule uniformity_point_def open_point_def)+
end

subsection \<open>Geometric Definitions\<close>

text \<open>These geometric definitions will later be used to define
constructible points\<close>

text \<open>The distance between two points is defined with the distance
of the metric space point\<close>
definition distance_def:
  "distance A B = dist A B"

text \<open>@{term "parallel A B C D"} is true if the lines @{term "(AB)"}
and @{term "(CD)"} are parallel. If not it is false.\<close>

definition parallel_def:
  "parallel A B C D = ((abscissa A - abscissa B) * (ordinate C - ordinate D) = (ordinate A - ordinate B) * (abscissa C - abscissa D))"

text \<open>Three points @{term "A B C"} are collinear if and only if the
lines @{term "(AB)"} and @{term "(AC)"} are parallel\<close>

definition collinear_def:
  "collinear A B C = parallel A B A C"

text \<open>The point @{term M} is the intersection of two lines @{term
"(AB)"} and @{term "(CD)"} if and only if the points @{term A}, @{term
M} and @{term B} are collinear and the points @{term C}, @{term M} and
@{term D} are also collinear\<close>

definition is_intersection_def:
  "is_intersection M A B C D = (collinear A M B \<and> collinear C M D)"


subsection \<open>Reals definable with square roots\<close>

text \<open>The inductive set @{term "radical_sqrt"} defines the reals
that can be defined with square roots. If @{term x} is in the
following set, then it depends only upon rational expressions and
square roots. For example, suppose @{term x} is of the form : $x =
(\sqrt{a + \sqrt{b}} + \sqrt{c + \sqrt{d*e +f}}) / (\sqrt{a} +
\sqrt{b}) + (a + \sqrt{b}) / \sqrt{g}$, where @{term a}, @{term b},
@{term c}, @{term d}, @{term e}, @{term f} and @{term g} are
rationals. Then @{term x} is in @{term "radical_sqrt"} because it is
only defined with rationals and square roots of radicals.\<close>

inductive_set radical_sqrt :: "real set"
  where
  "x \<in> \<rat> \<Longrightarrow> x \<in> radical_sqrt"|
  "x \<in> radical_sqrt \<Longrightarrow> -x \<in> radical_sqrt"|
  "x \<in> radical_sqrt \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> 1/x \<in> radical_sqrt"|
  "x \<in> radical_sqrt \<Longrightarrow> y \<in> radical_sqrt \<Longrightarrow> x+y \<in> radical_sqrt"|
  "x \<in> radical_sqrt \<Longrightarrow> y \<in> radical_sqrt \<Longrightarrow> x*y \<in> radical_sqrt"|
  "x \<in> radical_sqrt \<Longrightarrow> x \<ge> 0 \<Longrightarrow> sqrt x \<in> radical_sqrt"

text \<open>Here, we list some rules that will be used to prove that a
given real is in @{term "radical_sqrt"}.\<close>

text \<open>Given two reals in @{term "radical_sqrt"} @{term x} and @{term
y}, the subtraction $x - y$ is also in @{term "radical_sqrt"}.\<close>

lemma radical_sqrt_rule_subtraction:
  "x \<in> radical_sqrt \<Longrightarrow> y \<in> radical_sqrt \<Longrightarrow> x-y \<in> radical_sqrt"
by (metis diff_conv_add_uminus radical_sqrt.intros(2) radical_sqrt.intros(4))


text \<open>Given two reals in @{term "radical_sqrt"} @{term x} and @{term
y}, and $y \neq 0$, the division $x / y$ is also in @{term
"radical_sqrt"}.\<close>

lemma radical_sqrt_rule_division:
  "x \<in> radical_sqrt \<Longrightarrow> y \<in> radical_sqrt \<Longrightarrow> y \<noteq> 0 \<Longrightarrow> x/y \<in> radical_sqrt"
  by (metis divide_real_def radical_sqrt.intros(3) radical_sqrt.intros(5) real_scaleR_def real_vector.scale_one)


text \<open>Given a positive real @{term x} in @{term "radical_sqrt"}, its
square $x^2$ is also in @{term "radical_sqrt"}.\<close>

lemma radical_sqrt_rule_power2:
  "x \<in> radical_sqrt \<Longrightarrow> x \<ge> 0 \<Longrightarrow> x^2 \<in> radical_sqrt"
by (metis power2_eq_square radical_sqrt.intros(5))


text \<open>Given a positive real @{term x} in @{term "radical_sqrt"}, its
cube $x^3$ is also in @{term "radical_sqrt"}.\<close>

lemma radical_sqrt_rule_power3:
  "x \<in> radical_sqrt \<Longrightarrow> x \<ge> 0 \<Longrightarrow> x^3 \<in> radical_sqrt"
  by (metis power3_eq_cube radical_sqrt.intros(5))

subsection \<open>Introduction of the datatype expr which represents radical expressions\<close>

text \<open>An expression expr is either a rational constant: Const or the
negation of an expression or the inverse of an expression or the
addition of two expressions or the multiplication of two expressions
or the square root of an expression.\<close>

datatype expr = Const rat | Negation expr | Inverse expr | Addition expr expr | Multiplication expr expr | Sqrt expr

text \<open>The function @{term "translation"} translates a given
expression into its equivalent real.\<close>

fun translation :: "expr => real" ("(2\<lbrace>_\<rbrace>)")
  where
  "translation (Const x) = of_rat x"|
  "translation (Negation e) = - translation e"|
  "translation (Inverse e) = (1::real) / translation e"|
  "translation (Addition e1 e2) = translation e1 + translation e2"|
  "translation (Multiplication e1 e2) = translation e1 * translation e2"|
  "translation (Sqrt e) = (if translation e < 0 then 0 else sqrt (translation e))"

text \<open>Define the set of all the radicals of a given expression. For
example, suppose @{term "expr"} is of the form : expr = Addition (Sqrt
(Addition (Const @{term a}) Sqrt (Const @{term b}))) (Sqrt (Addition
(Const @{term c}) (Sqrt (Sqrt (Const @{term d}))))), where @{term a},
@{term b}, @{term c} and @{term d} are rationals. This can be
translated as follows: \<open>\<lbrace>expr\<rbrace> =\<close>~$\sqrt{a + \sqrt{b}} +
\sqrt{c + \sqrt{\sqrt{d}}}$. Moreover, the set @{term "radicals"} of
this expression is : \<open>\<lbrace>\<close>Addition (Const @{term a}) (Sqrt
(Const @{term b})), Const @{term b}, Addition (Const @{term c}) (Sqrt
(Sqrt (Const @{term d}))), Sqrt (Const @{term d}), Const @{term
d}\<open>\<rbrace>\<close>.\<close>

fun radicals :: "expr => expr set"
  where
  "radicals (Const x) = {}"|
  "radicals (Negation e) = (radicals e)"|
  "radicals (Inverse e) = (radicals e)"|
  "radicals (Addition e1 e2) = ((radicals e1) \<union> (radicals e2))"|
  "radicals (Multiplication e1 e2) = ((radicals e1) \<union> (radicals e2))"|
  "radicals (Sqrt e) = (if \<lbrace>e\<rbrace> < 0 then radicals e else {e} \<union> (radicals e))"


text \<open>If @{term r} is in @{term "radicals"} of @{term e} then the
set @{term "radical_sqrt"} of @{term r} is a subset (strictly
speaking) of the set @{term "radicals"} of @{term e}.\<close>

lemma radicals_expr_subset: "r \<in> radicals e \<Longrightarrow> radicals r \<subset> radicals e"
  by (induct e, auto simp add: if_split_asm)

text \<open>If @{term x} is in @{term "radical_sqrt"} then there exists a
radical expression @{term e} which translation is @{term x} (it is
important to notice that this expression is not necessarily
unique).\<close>

lemma radical_sqrt_correct_expr:
  "x \<in> radical_sqrt \<Longrightarrow> (\<exists> e. \<lbrace>e\<rbrace> = x)"
  apply (rule radical_sqrt.induct)
  apply auto
  apply (erule Rats_induct)
  apply (metis translation.simps(1))
  apply (metis translation.simps(2))
  apply (metis translation.simps(3))
  apply (metis translation.simps(4))
  apply (metis translation.simps(5))
  apply (metis linorder_not_less translation.simps(6))
  done

text \<open>The order of an expression is the maximum number of radicals
one over another occurring in a given expression. Using the example
above, suppose @{term "expr"} is of the form : expr = Addition (Sqrt
(Addition (Const @{term a}) Sqrt (Const @{term b}))) (Sqrt (Addition
(Const @{term c}) (Sqrt (Sqrt (Const @{term d}))))), where @{term a},
@{term b}, @{term c} and @{term d} are rationals and which can be
translated as follows: \<open>\<lbrace>expr\<rbrace> =\<close>~$\sqrt{a + \sqrt{b} +
\sqrt{c + \sqrt{\sqrt{d}}}}$. The order of @{term expr} is $max (2,3)
= 3$.\<close>

fun order :: "expr => nat"
  where
  "order (Const x) = 0"|
  "order (Negation e) = order e"|
  "order (Inverse e) = order e"|
  "order (Addition e1 e2) = max (order e1) (order e2)"|
  "order (Multiplication e1 e2) = max (order e1) (order e2)"|
  "order (Sqrt e) = 1 + order e"

text \<open>If an expression @{term s} is one of the radicals (or in
@{term "radicals"}) of the expression @{term r}, then its order is
smaller (strictly speaking) then the order of @{term r}.\<close>

lemma in_radicals_smaller_order:
  "s \<in> radicals r \<Longrightarrow> (order s) < (order r)"
  apply (induct r, auto)
  apply (metis insert_iff insert_is_Un less_Suc_eq)
  done

text \<open>The following theorem is the converse of the previous lemma.\<close>

lemma in_radicals_smaller_order_contrap:
  "(order s) \<ge> (order r) \<Longrightarrow> \<not> (s \<in> radicals r)"
  by (metis in_radicals_smaller_order leD)

text \<open>An expression @{term r} cannot be one of its own radicals.\<close>

lemma not_in_own_radicals:
  "\<not> (r \<in> radicals r)"
  by (metis in_radicals_smaller_order order_less_irrefl)


text \<open>If an expression @{term e} is a radical expression and it has
no radicals then its translation is a rational.\<close>

lemma radicals_empty_rational: "radicals e = {} \<Longrightarrow> \<lbrace>e\<rbrace> \<in> \<rat>"
  by (induct e, auto)

text \<open>A finite non-empty set of natural numbers has necessarily a
maximum.\<close>

lemma finite_set_has_max:
  "finite (s:: nat set) \<Longrightarrow> s \<noteq> {} \<Longrightarrow> \<exists>k \<in> s. \<forall> p \<in> s. p \<le> k"
  by (metis Max_ge Max_in)

text \<open>There is a finite number of radicals in an expression.\<close>

lemma finite_radicals: "finite (radicals e)"
  by (induct e, auto)

text \<open>We define here a new set corresponding to the orders of each
element in the set @{term "radicals"} of an expression @{term
expr}. Using the example above, suppose @{term expr} is of the form :
expr = Addition (Sqrt (Addition (Const @{term a}) Sqrt (Const @{term
b}))) (Sqrt (Addition (Const @{term c}) (Sqrt (Sqrt (Const @{term
d}))))), where @{term a}, @{term b}, @{term c} and @{term d} are
rationals and which can be translated as follows: \<open>\<lbrace>expr\<rbrace>
=\<close>~$\sqrt{a + \sqrt{b}} + \sqrt{c + \sqrt{\sqrt{d}}}$. The set @{term
"radicals"} of @{term expr} is $\{$Addition (Const @{term a}) Sqrt
(Const @{term b}), Const @{term b}, Addition (Const @{term c}) (Sqrt
(Sqrt (Const @{term d}))), Sqrt (Const @{term d}), Const @{term
d}$\}$; therefore, the set @{term "order_radicals"} of this set is
$\{1,0,2,1,0\}$.\<close>

fun order_radicals:: "expr set => nat set"
  where "order_radicals s = {y. \<exists> x \<in> s. y = order x}"

text \<open>If the set of radicals of an expression @{term e} is not empty
and is finite then the set @{term "order_radicals"} of the set of
radicals of @{term e} is not empty and is also finite.\<close>

lemma finite_order_radicals:
  "radicals e \<noteq> {} \<Longrightarrow> finite (radicals e) \<Longrightarrow>
   order_radicals (radicals e) \<noteq> {} \<and> finite (order_radicals (radicals e))"
  by simp (metis equals0I)

text \<open>The following lemma states that given an expression @{term e},
if the set @{term "order_radicals"} of the set @{term "radicals e"} is
not empty and is finite, then there exists a radical @{term r} of
@{term e} which is of highest order among the radicals of @{term e}.
\<close>

lemma finite_order_radicals_has_max:
  "order_radicals (radicals e) \<noteq> {} \<Longrightarrow>
   finite (order_radicals (radicals e)) \<Longrightarrow>
   \<exists> r. (r \<in> radicals e) \<and> (\<forall> s \<in> (radicals e). (order r \<ge> order s))"
  using finite_set_has_max [of "order_radicals (radicals e)"]
    by auto


text \<open>This important lemma states that in an expression that has at
least one radical, we can find an upmost radical @{term r} which is
not radical of any other term of the expression @{term e}. It is also
important to notice that this upmost radical is not necessarily unique
and is not the term of highest order of the expression @{term
e}. Using the example above, suppose @{term e} is of the form : @{term
e} = Addition (Sqrt (Addition (Const @{term a}) Sqrt (Const @{term
b}))) (Sqrt (Addition (Const @{term c}) (Sqrt (Sqrt (Const @{term
d}))))), where @{term a}, @{term b}, @{term c} and @{term d} are
rationals and which can be translated as follows: \<open>\<lbrace>e\<rbrace>
=\<close>~$\sqrt{a + \sqrt{b}} + \sqrt{c + \sqrt{\sqrt{d}}}$. The possible
upmost radicals in this expression are Addition (Const @{term a})
(Sqrt (Const @{term b})) or Addition (Const @{term c}) (Sqrt (Sqrt
(Const @{term d}))).\<close>


lemma upmost_radical_sqrt2:
  "radicals e \<noteq> {} \<Longrightarrow>
   \<exists> r \<in> radicals e. \<forall> s \<in> radicals e. r \<notin> radicals s"
  using in_radicals_smaller_order_contrap [of r s]  finite_radicals [of e]
  by (metis finite_order_radicals finite_order_radicals_has_max in_radicals_smaller_order_contrap)


text \<open>The following 7 lemmas are used to prove the main lemma @{term
"radical_sqrt_normal_form"} which states that if an expression @{term
e} has at least one radical then it can be written in a normal
form. This means that there exist three radical expressions @{term a},
@{term b} and @{term r} such that \<open>\<lbrace>e\<rbrace> = \<lbrace>a\<rbrace> + \<lbrace>b\<rbrace> *
\<sqrt>\<lbrace>r\<rbrace>\<close> and the radicals of @{term a} are radicals of @{term e}
but are not @{term r}, and the same goes for the radicals of @{term b}
and @{term r}. It is important to notice that @{term a}, @{term b} and
@{term r} are not unique and @{term "Sqrt r"} is not necessarily the
term of highest order.\<close>

lemma radical_sqrt_normal_form_sublemma:
  "((a::real) - b) * (a + b) = a * a - b * b"
  by (simp add: field_simps)

lemma eq_sqrt_squared:
  "(x::real) \<ge> 0 \<Longrightarrow> (sqrt x) * (sqrt x) = x"
  by (metis abs_of_nonneg real_sqrt_abs2 real_sqrt_mult)

lemma radical_sqrt_normal_form_lemma4:
  assumes "z \<ge> 0" "x \<noteq> y * sqrt z"
  shows
   "1 / (x + y * sqrt z) =
    x / (x * x - y * y * z) - (y * sqrt z) / (x * x - y * y * z)"
proof -
  have "1 / (x + y * sqrt z) = ((x - y * sqrt z) / (x + y * sqrt z)) / (x - y * sqrt z)"
    by (auto simp add: eq_divide_imp assms)
  also have "... = x / (x * x - y * y * z) - (y * sqrt z) / (x * x - y * y * z)"
    by (auto simp add: algebra_simps eq_sqrt_squared diff_divide_distrib assms)
  finally show ?thesis .
qed

lemma radical_sqrt_normal_form_lemma:
  fixes e::expr
  assumes "radicals e \<noteq> {}"
  and "\<forall>s \<in> radicals e. r \<notin> radicals s"
  and "r : radicals e"
  shows "\<exists>a b. 0 \<le> \<lbrace>r\<rbrace> & \<lbrace>e\<rbrace> = \<lbrace>a\<rbrace> + \<lbrace>b\<rbrace> * sqrt \<lbrace>r\<rbrace> &
          radicals a \<union> radicals b \<union> radicals r \<subseteq> radicals e &
          r \<notin> radicals a \<union> radicals b"
       (is "\<exists>a b. ?concl e a b")
  using assms
proof (induct e)
  case (Const rat) thus ?case
    by auto
next
  case (Negation e)
  obtain a b
    where a2: "?concl e a b"
    by (metis Negation radicals.simps(2))
  hence "\<lbrace>Negation e\<rbrace> = \<lbrace>Negation a\<rbrace> + \<lbrace>Negation b\<rbrace> * sqrt \<lbrace>r\<rbrace>"
    by simp
  thus ?case using a2
    by (metis radicals.simps(2))
next
  case (Inverse e)
  obtain a b
    where "?concl e a b"
    by (metis Inverse radicals.simps(3))
  thus ?case
    apply (case_tac "\<lbrace>b\<rbrace> * sqrt \<lbrace>r\<rbrace> = \<lbrace>a\<rbrace>")
    apply simp
    apply (case_tac "\<lbrace>a\<rbrace> = 0")
    apply (metis add_0_right div_by_0 mult_zero_right)
    apply (rule_tac x = "Multiplication (Const 1) (Inverse (Multiplication (Const 2) a))"in exI)
    apply (rule_tac x = "Const 0" in exI, simp)
    apply (rule_tac x = "Multiplication a (Inverse (Addition (Multiplication a a) (Negation (Multiplication (Multiplication b b) r))))" in exI)
    apply (rule_tac x = "Negation (Multiplication b (Inverse (Addition (Multiplication a a) (Negation (Multiplication (Multiplication b b) r)))))" in exI)
    apply (simp add: algebra_simps not_in_own_radicals eq_diff_eq' radical_sqrt_normal_form_lemma4)
    done
next
  case (Addition e1 e2)
  hence d1: "\<forall>s \<in> radicals e1 \<union> radicals e2. r \<notin> radicals s"
    by (metis radicals.simps(4))
  show ?case
  proof (cases "r: radicals e1 & r : radicals e2")
    case True
    obtain a1 b1 a2 b2
      where ab: "?concl e1 a1 b1"
        and bb: "?concl e2 a2 b2"
      using Addition.hyps
      by (simp add: d1) (metis True empty_iff)
    thus ?thesis
      apply simp
      apply (rule_tac x = "Addition a1 a2" in exI)
      apply (rule_tac x = "Addition b1 b2" in exI)
      apply (auto simp add: comm_semiring_class.distrib)
      done
  next
    case False
    thus ?thesis
    proof (cases "r: radicals e1")
      case True
      obtain a1 b1
      where "0 \<le> \<lbrace>r\<rbrace>" "?concl e1 a1 b1"
        using Addition.hyps
        by (auto simp: d1) (metis True empty_iff)
      thus ?thesis
        apply (rule_tac x = "Addition a1 e2" in exI)
        apply (rule_tac x = "b1" in exI)    using False True
        apply auto
        done
    next
      case False
      obtain a2 b2
        where "0 \<le> \<lbrace>r\<rbrace>" "?concl e2 a2 b2"
        using Addition d1
        by (metis False Un_iff empty_iff radicals.simps(4))
      thus ?thesis
        apply (rule_tac x = "Addition a2 e1" in exI)
        apply (rule_tac x = "b2" in exI)    using False
        apply auto
        done
    qed
  qed
next
  case (Multiplication e1 e2)
  show ?case
  proof (cases "r: radicals e1 & r : radicals e2")
    case True
    then obtain a1 b1 a2 b2
      where "?concl e1 a1 b1" "?concl e2 a2 b2"
      using Multiplication
      by simp (metis True empty_iff)
    thus ?thesis
      apply (rule_tac x = "Addition (Multiplication a1 a2) (Multiplication r (Multiplication b1 b2))" in exI)
      apply (rule_tac x = "Addition (Multiplication a1 b2) (Multiplication a2 b1)" in exI)
      apply (auto simp add: not_in_own_radicals algebra_simps eq_sqrt_squared)
      done
  next
    case False
    thus ?thesis
    proof (cases "r: radicals e1")
      case True
      then obtain a1 b1
      where "?concl e1 a1 b1"
        using Multiplication.hyps Multiplication(4)
        by auto (metis True empty_iff)
      thus ?thesis
        apply (rule_tac x = "Multiplication a1 e2" in exI)
        apply (rule_tac x = "Multiplication b1 e2" in exI)
        apply (simp add: algebra_simps)
        by (metis False True le_supI1 radicals.simps(5))
    next
      case False
      then obtain a2 b2
        where "?concl e2 a2 b2"
        using Multiplication.hyps Multiplication(4) Multiplication(5)
        by auto blast
      thus ?thesis
        apply (rule_tac x = "Multiplication a2 e1" in exI)
        apply (rule_tac x = "Multiplication b2 e1" in exI)
        apply (simp add: algebra_simps)
        by (metis False le_supI2)
    qed
  qed
next
  case (Sqrt e)
  show ?case
  proof (cases "\<lbrace>e\<rbrace> < 0")
    case True thus ?thesis
      using Sqrt
      apply (rule_tac x = "Const 0" in exI)
      apply (rule_tac x = "Const 0" in exI)
      apply auto
      done
  next
    case False thus ?thesis
      apply (rule_tac x = "Const 0" in exI)
      apply (rule_tac x = "Const 1" in exI)   using Sqrt
      apply (auto simp add: linorder_not_less)
      done
  qed
qed

text \<open>This main lemma is essential for the remaining part of the proof.\<close>

theorem radical_sqrt_normal_form:
  "radicals e \<noteq> {} \<Longrightarrow>
   \<exists> r \<in> radicals e.
        \<exists> a b. \<lbrace>e\<rbrace> = \<lbrace>Addition a (Multiplication b (Sqrt r))\<rbrace> \<and> \<lbrace>r\<rbrace> \<ge> 0 \<and>
               radicals a \<union> radicals b \<union> radicals r \<subseteq> radicals e &
               r \<notin> radicals a \<union> radicals b \<union> radicals r"
  using upmost_radical_sqrt2 [of e] radical_sqrt_normal_form_lemma
  by auto (metis all_not_in_conv leD)


subsection \<open>Important properties of the roots of a cubic equation\<close>

text \<open>The following 7 lemmas are used to prove a main result about
the properties of the roots of a cubic equation (@{term
"cubic_root_radical_sqrt_rational"}) which states that assuming that
@{term a} @{term b} and @{term c} are rationals and that @{term x} is
a radical satisfying $x^3 + a x^2 + b x + c = 0$ then there exists a
rational root. This lemma will be used in the proof of the
impossibility of trisection an angle and of duplicating a cube.\<close>


lemma cubic_root_radical_sqrt_steplemma:
  fixes P :: "real set"
  assumes Nats [THEN subsetD, intro]: "Nats \<subseteq> P"
  and Neg:  "\<forall>x \<in> P. -x \<in> P"
  and Inv:  "\<forall>x \<in> P. x \<noteq> 0 \<longrightarrow> 1/x \<in> P"
  and Add:  "\<forall>x \<in> P. \<forall>y \<in> P. x+y \<in> P"
  and Mult: "\<forall>x \<in> P. \<forall>y \<in> P. x*y \<in> P"
  and a: "(a \<in> P)" and b: "(b \<in> P)" and c: "(c \<in> P)"
  and eq0: "z^3 + a * z^2 + b * z + c = 0"
  and u: "(u \<in> P)"
  and v: "(v \<in> P)"
  and s: "((s * s) \<in> P)"
  and z: "(z = u + v * s)"
  shows "\<exists>w \<in> P. w^3 + a * w^2 + b * w + c = 0"
proof (cases "v * s = 0")
  case True
  thus ?thesis
    by (metis eq0 u z add_0_iff)
next
  case False
  hence sl0: "v \<noteq> 0"
    by (metis mult_eq_0_iff)
  from Add Neg have Minus: "\<forall>x \<in> P. \<forall>y \<in> P. x - y \<in> P" by (simp only: diff_conv_add_uminus) blast
  have l2: "(u^3 + 3 * u * v^2 * s^2 + a * u^2 + a * v^2 * s^2 + b * u + c) + (3 * u^2 * v + v^3 * s^2 + 2 * a * u * v + b * v) * s = 0"
    using eq0 z
    by algebra
  show ?thesis
  proof (cases "3 * u^2 * v + v^3 * s^2 + 2 * a * u * v + b * v \<noteq> 0")
    case True
    hence  "s * ((3 * u^2 * v + v^3 * s^2 + 2 * a * u * v + b * v) * (1/ (3 * u^2 * v + v^3 * s^2 + 2 * a * u * v + b * v)))= - (u^3 + 3 * u * v^2 * s^2 + a * u^2 + a * v^2 * s^2 + b * u + c)* (1/ (3 * u^2 * v + v^3 * s^2 + 2 * a * u * v + b * v))"
      using l2
      by algebra
    hence "s * ((3 * u^2 * v + v^3 * s^2 + 2 * a * u * v + b * v) /
                (3 * u^2 * v + v^3 * s^2 + 2 * a * u * v + b * v))
           = - (u^3 + 3 * u * v^2 * s^2 + a * u^2 + a * v^2 * s^2 + b * u + c) *
               (1 / (3 * u^2 * v + v^3 * s^2 + 2 * a * u * v + b * v))"
      by auto
    hence "s = - (u^3 + 3 * u * v^2 * s^2 + a * u^2 + a * v^2 * s^2 + b * u + c) *
               (1 /(3 * u^2 * v + v^3 * s^2 + 2 * a * u * v + b * v))"
      by (metis mult_1_right True divide_self_if)
    hence l10: "s = - (u *u *u  + 3 * u * v *v * (s*s) + a * u *u + a * v*v * (s *s) + b * u + c) *
                (1 / (3 * u *u * v + v *v*v * (s *s) + 2 * a * u * v + b * v))"
      by (simp add: algebra_simps power2_eq_square power3_eq_cube)
    have "(3*u*u * v + v*v*v * (s *s) + 2 * a * u * v + b * v) \<in> P"
      using a b u v s Nats Mult Add
      by auto
    hence l103: "1 / (3 * u *u * v + v *v*v * (s *s) + 2 * a * u * v + b * v) \<in> P"
      using Inv True
      by auto
    have "-(u*u*u + 3 * u * v *v * (s*s) + a * u *u + a * v*v * (s *s) + b * u + c) \<in> P"
      using a b c u v s Mult Add Neg Minus Nats
      by simp
    hence "- (u *u *u  + 3 * u * v *v * (s*s) + a * u *u + a * v*v * (s *s) + b * u + c) * (1 /(3 * u *u * v + v *v*v * (s *s) + 2 * a * u * v + b * v)) \<in> P"
      using l103 Mult
      by metis
    hence "s \<in> P"
      using l10
      by auto
    hence "z \<in> P"
      using z u v Mult Add
      by auto
    thus ?thesis
      using eq0
      by auto
  next
    case False
    have "(- a - 2 * u)^3 + a * (- a - 2 * u)^2 + b * ( - a - 2 * u) + c =
          (- a - 2 * u)^3 + a * (- a - 2 * u)^2 + (- (3 * u^2 + v^2 * s^2 + 2 * a * u)) *
          ( - a - 2 * u) + (- (u^3) - 3 * u * v^2 * s^2 - a * u^2 - a * v^2 * s^2 + 3 * u^3 + v^2 * s^2 * u + 2 * a * u^2)"
      using l2 False sl0
      by algebra
    also have "... = 0"
      by (simp add: algebra_simps power_def)
    finally show ?thesis
      by (metis a u Add Neg diff_conv_add_uminus mult_2)
  qed
qed

lemma cubic_root_radical_sqrt_steplemma_sqrt:
  assumes Nats [THEN subsetD, intro]: "Nats \<subseteq> P"
  and Neg:  "\<forall>x \<in> P. -x \<in> P"
  and Inv:  "\<forall>x \<in> P. x \<noteq> 0 \<longrightarrow> 1/x \<in> P"
  and Add:  "\<forall>x \<in> P. \<forall>y \<in> P. x+y \<in> P"
  and Mult: "\<forall>x \<in> P. \<forall>y \<in> P. x*y \<in> P"
  and a: "(a \<in> P)" and b: "(b \<in> P)" and c: "(c \<in> P)"
  and eq0: "z^3 + a * z^2 + b * z + c = 0"
  and u: "(u \<in> P)"
  and v: "(v \<in> P)"
  and s: "(s \<in> P)"
  and sPositive: "s \<ge> 0"
  and z: "z = u + v * sqrt s"
  shows "\<exists>w \<in> P. w^3 + a * w^2 + b * w + c = 0"
proof-
  have "(sqrt s) * (sqrt s) \<in> P"
    by (metis eq_sqrt_squared s sPositive)
  thus ?thesis
    using cubic_root_radical_sqrt_steplemma [of P a b c z u v "sqrt s"]
          Neg Add Mult Inv a b c u v s eq0 z
    by auto
qed

lemma cubic_root_radical_sqrt_lemma:
  fixes e::expr
  assumes a: "a \<in> \<rat>" and b: "b \<in> \<rat>" and c: "c \<in> \<rat>"
  and notEmpty: "radicals e \<noteq> {}"
  and eq0: "\<lbrace>e\<rbrace>^ 3 + a * \<lbrace>e\<rbrace>^2 + b * \<lbrace>e\<rbrace> + c = 0"
  shows "\<exists> e1. radicals e1 \<subset> radicals e & (\<lbrace>e1\<rbrace>^3 + a * \<lbrace>e1\<rbrace>^2 + b * \<lbrace>e1\<rbrace> + c = 0)"
proof -
  obtain r u v
    where hypsruv: "\<lbrace>r\<rbrace> \<ge> 0" "r \<in> radicals e"
                   "\<lbrace>e\<rbrace> = \<lbrace>Addition u (Multiplication v (Sqrt r))\<rbrace>"
                    "radicals u \<union> radicals v \<union> radicals r \<subseteq> radicals e"
                    "r \<notin> radicals u \<union> radicals v" "r \<notin> radicals r"
    using notEmpty radical_sqrt_normal_form [of e]
    by blast
  let ?E = "{x. \<exists> ex. (\<lbrace>ex\<rbrace> = x) & ((radicals ex) \<subseteq> (radicals e)) & (r \<notin> (radicals ex))}"
  have NatsE: "Nats \<subseteq> ?E"
    by (force elim: Nats_cases intro: exI[of _ "Const (rat_of_nat n)" for n])
  have negE: "\<forall>x \<in> ?E. -x \<in> ?E"
    using hypsruv by (force intro: exI[of _ "Negation ex" for ex])
  have invE: "\<forall>x \<in> ?E. x \<noteq> 0 --> 1/x \<in> ?E"
    using hypsruv by (force intro: exI[of _ "Inverse ex" for ex])
  have addE: "\<forall>x \<in> ?E. \<forall>y \<in> ?E. x+y \<in> ?E"
    using hypsruv by (force intro: exI[of _ "Addition ex1 ex2" for ex1 ex2])
  have multE: "\<forall>x \<in> ?E. \<forall>y \<in> ?E. x*y \<in> ?E"
    using hypsruv by (force intro: exI[of _ "Multiplication ex1 ex2" for ex1 ex2])
  obtain ra rb rc
    where hypsra: "a = of_rat ra"
      and hypsrb: "b = of_rat rb"
      and hypsrc: "c = of_rat rc"
    unfolding Rats_def
    by (metis Rats_cases a b c)
  have "a \<in> ?E & b \<in> ?E & c \<in> ?E & \<lbrace>u\<rbrace> \<in> ?E & \<lbrace>v\<rbrace> \<in> ?E & \<lbrace>r\<rbrace> \<in> ?E & \<lbrace>r\<rbrace> \<ge> 0 & \<lbrace>e\<rbrace> = \<lbrace>u\<rbrace> + \<lbrace>v\<rbrace> * sqrt \<lbrace>r\<rbrace>"
    using a b c notEmpty hypsruv hypsra hypsrb hypsrc
    by (auto intro: exI[of _ "Const x" for x])
  with eq0 hypsruv NatsE negE invE addE multE
      cubic_root_radical_sqrt_steplemma_sqrt [of "?E" a b c"\<lbrace>e\<rbrace>" "\<lbrace>u\<rbrace>" "\<lbrace>v\<rbrace>" "\<lbrace>r\<rbrace>"]
   obtain w where "w \<in> ?E & (w^3 + a * w^2 + b * w + c = 0)"
     by auto
   then obtain e2
     where "\<lbrace>e2\<rbrace> = w" "radicals e2 \<subseteq> radicals e" "r \<notin> radicals e2"
           "\<lbrace>e2\<rbrace>^3 + a * \<lbrace>e2\<rbrace>^2 + b * \<lbrace>e2\<rbrace> + c = 0"
     by auto
   with hypsruv show ?thesis
     by (metis subset_iff_psubset_eq)
qed

lemma cubic_root_radical_sqrt:
  assumes abc: "a \<in> \<rat>" "b \<in> \<rat>" "c \<in> \<rat>"
  shows "card (radicals e) = n \<Longrightarrow> \<lbrace>e\<rbrace>^3 + a * \<lbrace>e\<rbrace>^2 + b * \<lbrace>e\<rbrace> + c = 0 \<Longrightarrow>
         \<exists>x \<in> \<rat>. x^3 + a * x^2 + b * x + c = 0"
proof (induct n arbitrary: e rule: less_induct)
  case (less n)
  thus ?case
  proof cases
    assume n: "n = 0"
    thus ?thesis
      using less.prems radicals_empty_rational [of e] finite_radicals [of e]
      by (auto simp add: card_eq_0_iff n)
  next
    assume "n \<noteq> 0"
    hence "card (radicals e) \<noteq> 0"
      using less.prems by auto
    hence "radicals e \<noteq> {}"
      by (metis card.empty)
    hence "\<exists> e1. radicals e1 \<subset> radicals e & (\<lbrace>e1\<rbrace>^3 + a * \<lbrace>e1\<rbrace>^2 + b * \<lbrace>e1\<rbrace> + c = 0)"
      using abc less.prems cubic_root_radical_sqrt_lemma [of "a" "b" "c" "e"]
      by auto
    then obtain e1
      where hypse1: "radicals e1 \<subset> radicals e & (\<lbrace>e1\<rbrace>^3 + a * \<lbrace>e1\<rbrace>^2 + b * \<lbrace>e1\<rbrace> + c = 0)"
      by auto
    hence "card (radicals e1) < card (radicals e)"
      by (metis finite_radicals psubset_card_mono)
    hence "card (radicals e1) < n & a : Rats & b : Rats & c : Rats & \<lbrace>e1\<rbrace>^3 + a * \<lbrace>e1\<rbrace>^2 + b * \<lbrace>e1\<rbrace> + c = 0"
      using hypse1 less.prems abc
      by auto
    thus ?thesis using less.hyps [of _ e1]
      by auto
  qed
qed

text \<open>Now we can prove the final result about the properties of the
roots of a cubic equation.\<close>

theorem cubic_root_radical_sqrt_rational:
  assumes a: "a \<in> \<rat>" and b: "b \<in> \<rat>" and c: "c \<in> \<rat>"
  and x: "x \<in> radical_sqrt"
  and x_eqn: "x^3 + a * x^2 + b * x + c = 0"
  shows c: "\<exists>x \<in> \<rat>. x^3 + a * x^2 + b * x + c = 0"
proof-
   obtain e n
    where "\<lbrace>e\<rbrace> = x & (\<lbrace>e\<rbrace>^ 3 + a * \<lbrace>e\<rbrace>^2 + b * \<lbrace>e\<rbrace> + c = 0)" "n = card (radicals e)"
    using x x_eqn radical_sqrt_correct_expr [of x]
    by auto
  thus ?thesis
    using cubic_root_radical_sqrt [OF a b c]
    by auto
qed

subsection \<open>Important properties of radicals\<close>

lemma sqrt_roots:
  "y^2=x \<Longrightarrow> x\<ge>0 & (sqrt (x) = y | sqrt (x) = -y)"
  apply (simp add: power_def)
  by (metis abs_of_nonneg abs_of_nonpos real_sqrt_abs2 zero_le_mult_iff zero_le_square)

lemma radical_sqrt_linear_equation:
  assumes a: "a \<in> radical_sqrt"
  and b: "b \<in> radical_sqrt"
  and abNotNull: "\<not> (a = 0 & b = 0)"
  and eq0: "a * x + b = 0"
  shows "x \<in> radical_sqrt"
proof (cases "a=0")
  case True
  thus ?thesis
    using abNotNull eq0
    by auto
next
  case False
  hence l0: "a \<noteq> 0"
    by simp
  hence "x = - b /a"
    using eq0 by (simp add: field_simps)
  also have "... \<in> radical_sqrt"
    using a b radical_sqrt.simps l0
    by (metis radical_sqrt.intros(2) radical_sqrt_rule_division)
  finally show ?thesis .
qed


lemma radical_sqrt_simultaneous_linear_equation:
  assumes a: "a \<in> radical_sqrt"
  and b: "b \<in> radical_sqrt"
  and c: "c \<in> radical_sqrt"
  and d: "d \<in> radical_sqrt"
  and e: "e \<in> radical_sqrt"
  and f: "f \<in> radical_sqrt"
  and NotNull: "\<not> (a*e - b*d =0 & a*f - c*d = 0 & e*c = b*f)"
  and eq0: "a*x + b*y = c"
  and eq1: "d*x + e*y = f"
  shows "x \<in> radical_sqrt & y \<in> radical_sqrt"
proof (cases "a*e - b*d =0")
  case False
  hence "(a*e-b*d) * x = (e*c-b*f)" using eq0 eq1
    by algebra
  hence x: "x = (e*c-b*f) / (a*e-b*d)"
    using False by (simp add: field_simps)
  hence "(a*e-b*d) * y = (a*f - d*c)" using eq0 eq1
    by algebra
  hence y: "y = (a*f-d*c)/(a*e-b*d)"
    using False by (simp add: field_simps)
  have ae_rad: "(a*e -b*d) \<in> radical_sqrt"
    using a e b d radical_sqrt.simps
    by (metis radical_sqrt.intros(5) radical_sqrt_rule_subtraction)
  hence "((e*c-b*f) / (a*e-b*d)) \<in> radical_sqrt"  "((a*f-d*c) / (a*e-b*d)) \<in> radical_sqrt"
    using False a b c d e f by (auto intro!: radical_sqrt.intros(5) radical_sqrt_rule_division radical_sqrt_rule_subtraction)
  thus ?thesis
    by (simp add: x y)
next
  case True
  hence "(a*e-b*d) * x = (e*c-b*f)" "(a*e-b*d) * y = (a*f - d*c)" using eq0 eq1
    by algebra+
  thus ?thesis using NotNull True
    by simp
qed


lemma radical_sqrt_quadratic_equation:
  assumes a: "a \<in> radical_sqrt"
      and b: "b \<in> radical_sqrt"
      and c: "c \<in> radical_sqrt"
      and eq0: "a*x^2+b*x+c =0"
      and NotNull: "\<not> (a = 0 & b = 0 & c = 0)"
  shows "x \<in> radical_sqrt"
proof (cases "a=0")
  case True
  have "\<not> (b = 0 & c = 0)"
    by (metis True NotNull)
  thus ?thesis
    using b c radical_sqrt_linear_equation [of "b" "c" "x"]
    by (metis True add_0 eq0 mult_zero_left)
next
  case False
  hence "(2*a*x+b)^2 = 4*a*(- c)+b^2" using eq0
    by algebra
  hence "(b^2 - 4*a*c)\<ge>0 & (sqrt ((b^2 - 4*a*c)) = (2*a*x+b) | sqrt ((b^2 - 4*a*c)) = -(2*a*x+b))"
    using sqrt_roots [of "2*a*x+b" "b^2 - 4*a*c"]
    by auto
  hence l12: "b^2 - 4*a*c \<ge> 0 & ((-b + sqrt (b^2 - 4*a*c)) / (2*a) = x |
                                 (-b - sqrt (b^2 - 4*a*c)) / (2*a) = x)"
    using False
    by auto
  have "4*a*c \<in> radical_sqrt"
    using a c radical_sqrt.simps
    by (metis Rats_number_of radical_sqrt.intros(1) radical_sqrt.intros(5))
  hence "b^2 - 4*a*c \<in> radical_sqrt" using a b c
    by (metis power2_eq_square radical_sqrt.intros(5) radical_sqrt_rule_subtraction)
  hence l22: "sqrt (b^2 - 4*a*c) \<in> radical_sqrt"
    using l12
    by (metis radical_sqrt.intros(6))
  hence l23: "(-b + sqrt (b^2 - 4*a*c)) / (2*a) \<in> radical_sqrt"
    using b a False
    apply (simp add: algebra_simps)
    apply (metis radical_sqrt_rule_division radical_sqrt_rule_subtraction double_zero_sym mult_2_right mult_2_right radical_sqrt.intros(4))
    done
  have "(-b - sqrt (b^2 - 4*a*c)) / (2*a) \<in> radical_sqrt"
    using a b False l22
    by (metis div_by_0 mult_2 radical_sqrt.intros(2) radical_sqrt.intros(4) radical_sqrt_rule_division radical_sqrt_rule_subtraction)
  thus ?thesis
    by (metis l12 l23)
qed


lemma radical_sqrt_simultaneous_linear_quadratic:
  assumes a: "a \<in> radical_sqrt"
      and b: "b \<in> radical_sqrt"
      and c: "c \<in> radical_sqrt"
      and d: "d \<in> radical_sqrt"
      and e: "e \<in> radical_sqrt"
      and f: "f \<in> radical_sqrt"
      and NotNull: "\<not>(d=0 & e=0 & f=0)"
      and eq0: "(x-a)^2 + (y-b)^2 = c"
      and eq1: "d*x+e*y = f"
  shows "x \<in> radical_sqrt & y \<in> radical_sqrt"
proof (cases "d=0 & e=0")
  case True
  thus ?thesis
    by (metis add_0 eq1 mult_zero_left NotNull)
next
  case False
  hence l10: "(e^2 + d^2) * x^2 + (2*e*b*d - 2*a*e^2 - 2*d*f)*x + (a^2 * e^2 + f^2 - 2* e *b* f + b^2 * e^2 - e^2 *c) = 0"
     using eq0 eq1
    by algebra
  have l12: "\<not> (e^2 +d^2 = 0 & 2*e*b*d - 2*a*e^2 - 2*d*f = 0 & a^2 * e^2 + f^2 - 2* e *b* f + b^2 * e^2 - e^2 *c = 0)"
    using False power_def
    by auto
  have l13: "(e^2 +d^2) \<in> radical_sqrt"
    using e d
    by (metis power2_eq_square radical_sqrt.intros(4) radical_sqrt.intros(5))
  have 2: "2 \<in> radical_sqrt"
    by (auto intro: radical_sqrt.intros)
  have sl1: "(2*e*b*d) \<in> radical_sqrt"
    using e b d
    by (metis (lifting) mult_2 radical_sqrt.intros(4) radical_sqrt.intros(5))
  hence sl2: "(- 2*a*e^2) \<in> radical_sqrt" using radical_sqrt.intros
    by (simp add: field_simps) (metis mult_2 power2_eq_square a e)
  have "(- 2*d*f) \<in> radical_sqrt" using radical_sqrt.intros
    using d f by (auto intro: radical_sqrt.intros simp add: power2_eq_square)
  hence sl4: "((2*e*b*d) + (- 2*a*e^2) + (- 2*d*f)) \<in> radical_sqrt"
    using sl1 sl2
    by (metis radical_sqrt.intros(4))
  have sl5: "2*e*b*d - 2*a*e^2 - 2*d*f = (2*e*b*d) + (- 2*a*e^2) + (- 2*d*f)"
    by auto
  hence l14: "(2*e*b*d - 2*a*e^2 - 2*d*f) \<in> radical_sqrt"
    using sl4
    by metis
  have sl6: "(a^2 * e^2) \<in> radical_sqrt"
    using a e by (auto intro: radical_sqrt.intros simp add: power2_eq_square)
  have sl7: "(f^2) \<in> radical_sqrt"
    using f by (auto intro: radical_sqrt.intros simp add: power2_eq_square)
  have sl8: "(- 2 * e *b* f) \<in> radical_sqrt"
    using e b f 2 by (auto intro: radical_sqrt.intros simp add: power2_eq_square)
  have sl9: "(b^2 * e^2) \<in> radical_sqrt"
    using b e by (auto intro: radical_sqrt.intros simp add: power2_eq_square)
  have sl10: "(- c* e^2) \<in> radical_sqrt"
    using c e by (auto intro: radical_sqrt.intros simp add: power2_eq_square)
  have sl6: "(a^2 * e^2 + f^2 + (- 2 * e *b* f) + b^2 * e^2 + (- c* e^2)) \<in> radical_sqrt"
    using a e f b c sl6 sl7 sl8 sl9 sl10
    by (metis (hide_lams, no_types) power2_eq_square radical_sqrt.intros(4))
  have "a^2 * e^2 + f^2 - 2* e *b* f + b^2 * e^2 - e^2 *c = a^2 * e^2 + f^2 + (- 2 * e *b* f) + b^2 * e^2 + (- c* e^2)"
    by auto
  hence "(a^2 * e^2 + f^2 - 2* e *b* f + b^2 * e^2 - e^2 *c) \<in> radical_sqrt"
    using sl6
    by metis
  hence x: "x \<in> radical_sqrt"
    using radical_sqrt_quadratic_equation [of "e^2 +d^2" "2*e*b*d - 2*a*e^2 - 2*d*f" "a^2 * e^2 + f^2 - 2* e *b* f + b^2 * e^2 - e^2 *c" "x"] l13 l14 l12 l10
    by auto
  have l18: "e*y + (d*x - f) = 0"
    using eq1
    by auto
  hence y: "y \<in> radical_sqrt"
    using e d f x False
  proof (cases "e = 0")
    case True
    hence l22: "1 * y^2 + (- 2* b) * y + (b^2 + (x - a)^2 - c) =0"
      using eq0
      by algebra
    have l24: "1 \<in> radical_sqrt"
      by (metis Rats_1 radical_sqrt.intros(1))
    have l25: "(- 2* b) \<in> radical_sqrt"
      using b
      by (metis minus_mult_commute mult_2 radical_sqrt.intros(2) radical_sqrt.intros(4))
    have l26: "(b^2 + (x - a)^2 - c) \<in> radical_sqrt"
      using a b c x
      by (auto intro: radical_sqrt.intros radical_sqrt_rule_subtraction simp add: power2_eq_square)
    thus ?thesis
      using radical_sqrt_quadratic_equation [of "1::real" "- 2* b" "b^2 + (x - a)^2 - c" "y"] l22 l24 l25 l26
      by auto
  next
    case False
    hence l29: "\<not> (e=0 & d*x-f = 0)"
      by simp
    have "(d*x - f) \<in> radical_sqrt"
      using d f x
      by (metis radical_sqrt.intros(5) radical_sqrt_rule_subtraction)
    thus ?thesis
      using radical_sqrt_linear_equation [of "e" "d*x - f" y] e d f l18 l29
      by auto
  qed
  show ?thesis
    by (metis x y)
qed

lemma radical_sqrt_simultaneous_quadratic_quadratic:
  assumes a: "a \<in> radical_sqrt"
      and b: "b \<in> radical_sqrt"
      and c: "c \<in> radical_sqrt"
      and d: "d \<in> radical_sqrt"
      and e: "e \<in> radical_sqrt"
      and f: "f \<in> radical_sqrt"
      and NotEqual: "\<not> (a = d & b = e & c = f)"
      and eq0: "(x - a)^2 + (y - b)^2 = c"
      and eq1: "(x - d)^2 + (y - e)^2 = f"
  shows "x \<in> radical_sqrt & y \<in> radical_sqrt"
proof -
  have "(x^2 - 2*a*x + a^2 + y^2 - 2*y*b + b^2) - (x^2 - 2*d*x + d^2 + y^2 - 2*y*e + e^2) = (c - f)"
    using eq0 eq1
    by (simp add: algebra_simps power_def)
  hence l4: "(2*d - 2*a)*x + (2*e - 2*b)*y +(b^2 - e^2 + a^2 - d^2 + f - c) = 0"
    by algebra
  hence l6: "\<not> ((2*d - 2*a) = 0 & (2*e - 2*b) = 0 & (b^2 - e^2) + (a^2 - d^2) + (f - c) = 0)"
    using NotEqual
    by algebra
  have l7: "(2*d - 2*a) \<in> radical_sqrt"
    by (metis a d mult_2 radical_sqrt.intros(4) radical_sqrt_rule_subtraction)
  have l8: "(2*e - 2*b) \<in> radical_sqrt"
    by (metis b e mult_2 radical_sqrt.intros(4) radical_sqrt_rule_subtraction)
  have be_rad: "(b^2 - e^2) \<in> radical_sqrt"
    by (metis b e power2_eq_square radical_sqrt.intros(5) radical_sqrt_rule_subtraction)
  have ad_rad: "(a^2 - d^2) \<in> radical_sqrt"
    by (metis a d power2_eq_square radical_sqrt.intros(5) radical_sqrt_rule_subtraction)
  have "(f - c) \<in> radical_sqrt"
    using f c
    by (metis radical_sqrt_rule_subtraction)
  hence "-((b^2 - e^2) + (a^2 - d^2) + (f - c)) \<in> radical_sqrt"
    using radical_sqrt.intros
    by (metis be_rad ad_rad)
  thus ?thesis
    using radical_sqrt_simultaneous_linear_quadratic [of "a" "b" "c" "(2*d - 2*a)" "(2*e - 2*b)" "- ((b^2 - e^2) + (a^2 - d^2) + (f - c))" "x" "y"] l7 l8 l6 l4 a b c d e f NotEqual eq0 eq1
    by simp
qed


subsection \<open>Important properties of geometrical points which coordinates are radicals\<close>

lemma radical_sqrt_line_line_intersection:
  assumes absA: "(abscissa (A)) \<in> radical_sqrt"
      and ordA: "(ordinate A) \<in> radical_sqrt"
      and absB: "(abscissa B) \<in> radical_sqrt"
      and ordB: "(ordinate B) \<in> radical_sqrt"
      and absC: "(abscissa C) \<in> radical_sqrt"
      and ordC: "(ordinate C) \<in> radical_sqrt"
      and absD: "(abscissa D) \<in> radical_sqrt"
      and ordD: "(ordinate D) \<in> radical_sqrt"
      and notParallel: "\<not> (parallel A B C D)"
      and isIntersec: "is_intersection X A B C D"
  shows "(abscissa X) \<in> radical_sqrt & (ordinate X) \<in> radical_sqrt"
proof-
  have l2: "(abscissa A - abscissa X) * (ordinate A - ordinate B) = (ordinate A - ordinate X) * (abscissa A - abscissa B) & (abscissa C - abscissa X) * (ordinate C - ordinate D) = (ordinate C - ordinate X) * (abscissa C - abscissa D)"
    using isIntersec is_intersection_def collinear_def parallel_def
    by auto
  hence l4: "(- (ordinate A - ordinate B)) * abscissa X + (abscissa A - abscissa B) * ordinate X = (- abscissa A * (ordinate A - ordinate B) + ordinate A * (abscissa A - abscissa B))"
    by (simp add: algebra_simps)
  have l6: "(- (ordinate C - ordinate D)) * abscissa X + (abscissa C - abscissa D) * ordinate X = (- abscissa C * (ordinate C - ordinate D) + ordinate C * (abscissa C - abscissa D))"
    using l2
    by (simp add: algebra_simps)
  have sl1: "(- (ordinate A - ordinate B)) \<in> radical_sqrt"
    by (metis ordA ordB minus_diff_eq radical_sqrt_rule_subtraction)
  have sl2: "(abscissa A - abscissa B) \<in> radical_sqrt"
    by (metis absA absB radical_sqrt_rule_subtraction)
  have sl3: "(- abscissa A * (ordinate A - ordinate B) + ordinate A * (abscissa A - abscissa B)) \<in> radical_sqrt"
    using absA ordA ordB absB
    by (metis diff_conv_add_uminus radical_sqrt.intros(2) radical_sqrt.intros(4) radical_sqrt.intros(5))
  have sl4: "(- (ordinate C - ordinate D)) \<in> radical_sqrt"
    by (metis ordC ordD minus_diff_eq radical_sqrt_rule_subtraction)
  have sl5: "(abscissa C - abscissa D) \<in> radical_sqrt"
    by (metis absC absD radical_sqrt_rule_subtraction)
  have sl6: "(- abscissa C * (ordinate C - ordinate D) + ordinate C * (abscissa C - abscissa D)) \<in> radical_sqrt"
    using absC ordC absD ordD
    by (metis diff_conv_add_uminus radical_sqrt.intros(2) radical_sqrt.intros(4) radical_sqrt.intros(5))
  have "(- (ordinate A - ordinate B)) * (abscissa C - abscissa D) \<noteq> (abscissa A - abscissa B) * (- (ordinate C - ordinate D))"
    using notParallel parallel_def
    by (simp add: algebra_simps)
  thus ?thesis
    using radical_sqrt_simultaneous_linear_equation [of "- (ordinate A - ordinate B)" "(abscissa A - abscissa B)" "- abscissa A * (ordinate A - ordinate B) + ordinate A * (abscissa A - abscissa B)" "- (ordinate C - ordinate D)" "abscissa C - abscissa D" "- abscissa C * (ordinate C - ordinate D) + ordinate C * (abscissa C - abscissa D)" "abscissa X" "ordinate X"] absA ordA absB ordB absC ordC absD ordD l4 sl1 sl2 sl3 sl4 sl5 sl6 l6
    by simp
qed


lemma radical_sqrt_line_circle_intersection:
  assumes absA: "(abscissa A) \<in> radical_sqrt" and ordA: "(ordinate A) \<in> radical_sqrt"
      and absB: "(abscissa B) \<in> radical_sqrt" and ordB: "(ordinate B) \<in> radical_sqrt"
      and absC: "(abscissa C) \<in> radical_sqrt" and ordC: "(ordinate C) \<in> radical_sqrt"
      and absD: "(abscissa D) \<in> radical_sqrt" and ordD: "(ordinate D) \<in> radical_sqrt"
      and absE: "(abscissa E) \<in> radical_sqrt" and ordE: "(ordinate E) \<in> radical_sqrt"
      and notEqual: "A \<noteq> B"
      and colin: "collinear A X B"
      and eqDist: "(distance C X = distance D E)"
shows "(abscissa X) \<in> radical_sqrt & (ordinate X) \<in> radical_sqrt"
proof-
  have l3: "(- (ordinate A - ordinate B)) * abscissa X + (abscissa A - abscissa B) * ordinate X = (- abscissa A * (ordinate A - ordinate B) + ordinate A * (abscissa A - abscissa B))"
    using colin  unfolding collinear_def parallel_def
    by algebra
  have "sqrt ((abscissa X - abscissa C)^2 + (ordinate X - ordinate C) ^2) = sqrt ((abscissa D - abscissa E)^2 + (ordinate D - ordinate E) ^2)"
    using eqDist distance_def
    by (metis (no_types) minus_diff_eq point_abscissa_diff point_dist_def point_ordinate_diff power2_minus)
  hence l6: "(abscissa X - abscissa C)^2 + (ordinate X - ordinate C) ^2 = (abscissa D - abscissa E)^2 + (ordinate D - ordinate E)^2"
    by auto
  have l8: "\<not> (- (ordinate A - ordinate B) = 0 & (abscissa A - abscissa B) = 0 & (- abscissa A * (ordinate A - ordinate B) + ordinate A * (abscissa A - abscissa B)) = 0)"
    using notEqual  unfolding point_eq_iff
    by auto
  have sl1: "(- (ordinate A - ordinate B)) \<in> radical_sqrt"
    by (metis ordA ordB minus_diff_eq radical_sqrt_rule_subtraction)
  have sl2: "(abscissa A - abscissa B) \<in> radical_sqrt"
    by (metis absA absB radical_sqrt_rule_subtraction)
  have sl3: "(- abscissa A * (ordinate A - ordinate B) + ordinate A * (abscissa A - abscissa B)) \<in> radical_sqrt"
    by (metis absA ordA absB ordB diff_conv_add_uminus radical_sqrt.intros(2) radical_sqrt.intros(4) radical_sqrt.intros(5))
  have "(abscissa D - abscissa E)^2 + (ordinate D - ordinate E)^2 \<in> radical_sqrt"
    by (metis power2_eq_square
             absD absE ordD ordE radical_sqrt_rule_subtraction radical_sqrt.intros(5) radical_sqrt.intros(4) )
  thus ?thesis
    using radical_sqrt_simultaneous_linear_quadratic
            [of "abscissa C" "ordinate C"
                "(abscissa D - abscissa E)^2 + (ordinate D - ordinate E)^2"
                "- (ordinate A - ordinate B)" "abscissa A - abscissa B"
                "- abscissa A * (ordinate A - ordinate B) + ordinate A * (abscissa A - abscissa B)"
                "abscissa X" "ordinate X"]
       l3 absC ordC sl1 sl2 sl3 l6 l8
    by simp
qed


lemma radical_sqrt_circle_circle_intersection:
  assumes absA: "(abscissa A) \<in> radical_sqrt" and ordA: "(ordinate A)  \<in> radical_sqrt"
      and absB: "(abscissa B) \<in> radical_sqrt" and ordB: "(ordinate B) \<in> radical_sqrt"
      and absC: "(abscissa C) \<in> radical_sqrt" and ordC: "(ordinate C) \<in> radical_sqrt"
      and absD: "(abscissa D) \<in> radical_sqrt" and ordD: "(ordinate D) \<in> radical_sqrt"
      and absE: "(abscissa E) \<in> radical_sqrt" and ordE: "(ordinate E) \<in> radical_sqrt"
      and absF: "(abscissa F) \<in> radical_sqrt" and ordF: "(ordinate F) \<in> radical_sqrt"
      and eqDist0: "distance A X = distance B C"
      and eqDist1: "distance D X = distance E F"
      and notEqual: "\<not> (A = D & distance B C = distance E F)"
  shows "(abscissa X) \<in> radical_sqrt & (ordinate X) \<in> radical_sqrt"
proof-
  have "sqrt ((abscissa X - abscissa A)^2 + (ordinate X - ordinate A) ^2) = sqrt ((abscissa B - abscissa C)^2 + (ordinate B - ordinate C) ^2)"
    by (metis (no_types) eqDist0 distance_def minus_diff_eq point_abscissa_diff point_dist_def point_ordinate_diff power2_minus)
  hence "(sqrt ((abscissa X - abscissa A)^2 + (ordinate X - ordinate A) ^2))^2 = (sqrt ((abscissa B - abscissa C)^2 + (ordinate B - ordinate C)^2)) ^2"
    by (auto simp add: power_def)
  hence l3: "(abscissa X - abscissa A)^2 + (ordinate X - ordinate A) ^2 = (abscissa B - abscissa C)^2 + (ordinate B - ordinate C)^2"
    by auto
  have "sqrt ((abscissa X - abscissa D)^2 + (ordinate X - ordinate D) ^2) = sqrt ((abscissa E - abscissa F)^2 + (ordinate E - ordinate F) ^2)"
    by (metis (no_types) eqDist1 distance_def minus_diff_eq point_abscissa_diff point_dist_def point_ordinate_diff power2_minus)
  hence l3bis: "(abscissa X - abscissa D)^2 + (ordinate X - ordinate D) ^2 = (abscissa E - abscissa F)^2 + (ordinate E - ordinate F)^2"
    by auto
  have l4: "\<not> (abscissa A = abscissa D & ordinate A = ordinate D)"
    by (metis point_eq_iff notEqual eqDist0 eqDist1)
  have "(abscissa B - abscissa C) \<in> radical_sqrt"
    by (metis absB absC radical_sqrt_rule_subtraction)
  hence sl1: "((abscissa B - abscissa C)^2) \<in> radical_sqrt"
    by (auto intro: radical_sqrt.intros simp add: power2_eq_square)
  have "(ordinate B - ordinate C) \<in> radical_sqrt"
    by (metis ordB ordC radical_sqrt_rule_subtraction)
  hence "(ordinate B - ordinate C)^2 \<in> radical_sqrt"
    by (auto intro: radical_sqrt.intros simp add: power2_eq_square)
  hence sl3: "((abscissa B - abscissa C)^2 + (ordinate B - ordinate C)^2) \<in> radical_sqrt"
    by (metis radical_sqrt.intros(4) sl1)
  have "(abscissa E - abscissa F) \<in> radical_sqrt"
    by (metis absE absF radical_sqrt_rule_subtraction)
  hence sl4: "((abscissa E - abscissa F)^2) \<in> radical_sqrt"
    by (auto intro: radical_sqrt.intros simp add: power2_eq_square)
  have "(ordinate E - ordinate F) \<in> radical_sqrt"
    by (metis ordE ordF radical_sqrt_rule_subtraction)
  hence "(ordinate E - ordinate F)^2 \<in> radical_sqrt"
    by (auto intro: radical_sqrt.intros simp add: power2_eq_square)
  hence "((abscissa E - abscissa F)^2 + (ordinate E - ordinate F)^2) \<in> radical_sqrt"
    by (metis radical_sqrt.intros(4) sl4)
  thus ?thesis
    using radical_sqrt_simultaneous_quadratic_quadratic
            [of "abscissa A" "ordinate A" "(abscissa B - abscissa C)^2 + (ordinate B - ordinate C)^2"
                "abscissa D" "ordinate D" "(abscissa E - abscissa F)^2 + (ordinate E - ordinate F)^2"
                "abscissa X" "ordinate X"]
          absA ordA absD ordD l3 l3bis l4 sl3
    by auto
qed

subsection \<open>Definition of the set of contructible points\<close>

inductive_set constructible :: "point set"
  where
  "(M \<in> points \<and> (abscissa M) \<in> \<rat> \<and> (ordinate M) \<in> \<rat>) \<Longrightarrow> M \<in> constructible"|
  "(A \<in> constructible \<and> B \<in> constructible \<and> C \<in> constructible \<and> D \<in> constructible \<and> \<not> parallel A B C D \<and> is_intersection M A B C D) \<Longrightarrow> M \<in> constructible"|
  "(A \<in> constructible \<and> B \<in> constructible \<and> C \<in> constructible \<and> D \<in> constructible \<and> E \<in> constructible \<and> \<not> A = B \<and> collinear A M B \<and> distance C M = distance D E) \<Longrightarrow> M \<in> constructible"|
  "(A \<in> constructible \<and> B \<in> constructible \<and> C \<in> constructible \<and> D \<in> constructible \<and> E \<in> constructible \<and> F \<in> constructible \<and> \<not> (A = D \<and> distance B C = distance E F) \<and> distance A M = distance B C \<and> distance D M = distance E F) \<Longrightarrow> M \<in> constructible"

subsection \<open>An important property about constructible points: their
coordinates are radicals\<close>

lemma constructible_radical_sqrt:
  assumes h: "M \<in> constructible"
  shows "(abscissa M) \<in> radical_sqrt & (ordinate M) \<in> radical_sqrt"
  apply (rule constructible.induct)
  apply (metis assms)
  apply (metis radical_sqrt.intros(1))
  apply (metis radical_sqrt_line_line_intersection)
  apply (metis radical_sqrt_line_circle_intersection)
  apply (metis radical_sqrt_circle_circle_intersection)
  done

subsection \<open>Proving the impossibility of duplicating the cube\<close>

lemma impossibility_of_doubling_the_cube_lemma:
  assumes x: "x \<in> radical_sqrt"
  and x_eqn: "x^3 = 2"
  shows False
proof-
  have  "\<exists>x \<in> Rats. x^3 + 0 * x^2 + 0 * x + (- 2) = (0::real)"
    using x x_eqn cubic_root_radical_sqrt_rational [of "0" "0" "- 2"]
    by auto
  then obtain y::real where hypsy: "y: Rats & y^3 = 2"
    by (simp only: left_minus mult_zero_left add_0_right real_add_minus_iff) auto
  then obtain r where hypsr: "y = of_rat r"
    unfolding Rats_def
    by (metis Rats_cases hypsy)
  hence "\<exists>! p. r = Fract (fst p) (snd p) & snd p > 0 & coprime (fst p) (snd p)"
    by (metis quotient_of_unique)
  then obtain p q where hypsp: "r = Fract p q" "q > 0" "coprime p q"
    by auto
  have l6: "r^3 = 2"
    by (metis (lifting) hypsy hypsr of_rat_eq_iff of_rat_numeral_eq of_rat_power)
  have l7: "r^3  = Fract (p^3) (q^3)"
    using hypsp by (simp add: power3_eq_cube)
  have l8: "q ^ 3 > 0 & coprime (p ^ 3) (q ^ 3)"
    using hypsp by simp
  have "Fract (p ^ 3) (q ^ 3) = 2"
    using l6 l7
    by auto
  hence "Fract (p ^ 3) (q ^ 3) = Fract 2 1"
    by (metis rat_number_expand(3))
  hence l12: "p ^ 3 = q ^ 3 * 2" using hypsp
    by (simp add: eq_rat)
  hence "even (p ^ 3)"
    by (auto intro: dvdI)
  then have "even p"
    by auto
  then have "8 dvd p ^ 3"
    by (auto simp add: dvd_def power_def)
  then have "8 dvd q ^ 3 * 2"
    using l12 by auto
  then have "even (q ^ 3)"
    by (auto simp add: dvd_def)
  then have "even q"
    by auto
  with \<open>even p\<close> have "2 dvd gcd p q"
    by (rule gcd_greatest)
  with \<open>coprime p q\<close> show False by simp
qed


theorem impossibility_of_doubling_the_cube:
  "x^3 = 2 \<Longrightarrow> (Point x 0) \<notin> constructible"
  by (metis abscissa.simps constructible_radical_sqrt impossibility_of_doubling_the_cube_lemma)


subsection \<open>Proving the impossibility of trisecting an angle\<close>

lemma impossibility_of_trisecting_pi_over_3_lemma:
  assumes x: "x \<in> radical_sqrt"
  and x_eqn: "x^3 - 3 * x - 1 = 0"
  shows False
proof-
  have "\<exists>x \<in> Rats. x^3 + (- 3) * x = (1::real)"
    using x_eqn cubic_root_radical_sqrt_rational [of 0 "- 3" "- 1"] x
    by force
  then obtain y :: real where hypsy: "y \<in> Rats \<and> y ^ 3 - 3 * y = 1" by auto
  then obtain r where hypsr: "y = of_rat r"
    by (metis Rats_cases)
  then obtain p where hypsp: "r = Fract (fst p) (snd p) & snd p > 0 & coprime (fst p) (snd p)"
      using quotient_of_unique hypsy
      by blast
  have r3eq: "r^3 - 3 * r = 1"
    using hypsy hypsr [[hypsubst_thin = true]]
    by auto (metis (hide_lams, no_types) of_rat_1 of_rat_diff of_rat_eq_iff of_rat_mult of_rat_numeral_eq of_rat_power)
  have l7: "(snd p) ^3 > 0 & coprime ((fst p)^3) ((snd p)^3)"
    using hypsp by simp
  have "r^3  = Fract ((fst p)^3) ((snd p)^3)"
    by (metis (no_types) mult_rat power3_eq_cube hypsp)
  then have "Fract ((fst p)^3) ((snd p)^3) - (Fract (3 * (fst p)) (snd p)) = 1"
    using r3eq hypsp
    by (simp add: Fract_of_int_quotient)
  then have l10: "Fract ((fst p)^3) ((snd p)^3) - Fract (3 * (fst p) * (snd p)^2 ) ((snd p)^3) = 1"
    using hypsp
    by (simp add: power_def algebra_simps Fract_of_int_quotient)
  have "Fract ((fst p)^3 - (3 * (fst p) * (snd p)^2)) ((snd p)^3) =
        Fract (((fst p)^3 - (3 * (fst p) * (snd p)^2))*(snd p)^3) (((snd p)^3) * (snd p)^3)"
    using l7
        mult_rat_cancel [of "(snd p)^3" "((fst p)^3 - (3 * (fst p) * (snd p)^2))" "(snd p)^3"]
    by (auto simp add: algebra_simps)
  also have "... = Fract 1 1"
    by (metis l7 l10 one_rat diff_rat mult_neg_pos not_square_less_zero int_distrib(3))
  finally have "(fst p)^3 - 3 * (fst p) * (snd p)^2 = (snd p)^3" using hypsp
    by (simp add: eq_rat)
  hence "(fst p) * ((fst p)^2 - 3 * (snd p) ^2) = (snd p)^3"
        "(snd p) * ((snd p)^2 + 3 * (fst p) * (snd p)) = (fst p) ^3"
    by (auto simp add: power_def algebra_simps)
  hence "(fst p) dvd ((snd p)^3)"  "(snd p) dvd ((fst p)^3)"
    apply (auto simp add: dvd_def)
    apply (rule_tac x = "(fst p)^2 - 3 * (snd p) ^2" in exI)
    apply (rule_tac [2] x = "(snd p)^2 + 3 * (fst p) * (snd p)" in exI)
    apply auto
    done
  moreover have "coprime (fst p) (snd p ^ 3)" "coprime (fst p ^ 3) (snd p)"
    using hypsp by auto
  ultimately have "is_unit (fst p)" "is_unit (snd p)"
    using coprime_common_divisor [of "fst p" "snd p ^ 3" "fst p"]
      coprime_common_divisor [of "fst p ^ 3" "snd p" "snd p"]
    by auto
  with hypsp have "fst p = 1 \<or> fst p = - 1" "snd p = 1"
    by auto
  with hypsp have "r = 1 | r = - 1"
    by (auto simp add: rat_number_collapse)
  with r3eq show False
    by (auto simp add: power_def algebra_simps)
qed


theorem impossibility_of_trisecting_angle_pi_over_3:
  "Point (cos (pi / 9)) 0 \<notin> constructible"
proof-
  have "cos (3 *(pi/9)) = 4 * (cos (pi/9))^3 - 3 * cos (pi/9)"
    using cos_treble_cos [of "pi / 9"]
    by auto
  hence "1/2 = 4 * (cos (pi/9))^3 - 3 * cos (pi/9)"
    by (simp add: cos_60)
  hence "8 * (cos (pi/9))^3 - 6 * cos (pi/9) - 1 = 0"
    by (simp add: algebra_simps)
  hence "(2 * cos (pi / 9)) ^3 - 3 * (2 * cos (pi / 9)) - 1 = 0"
    by (simp add: algebra_simps power_def)
  hence "\<not> (2 * cos (pi / 9)) \<in> radical_sqrt"
    by (metis impossibility_of_trisecting_pi_over_3_lemma)
  hence "\<not> (cos (pi / 9)) \<in> radical_sqrt"
    by (metis divide_self_if mult_zero_right one_add_one radical_sqrt.intros(4) radical_sqrt.intros(5) radical_sqrt_rule_division)
  thus ?thesis
    by (metis abscissa.simps constructible_radical_sqrt)
qed

end
