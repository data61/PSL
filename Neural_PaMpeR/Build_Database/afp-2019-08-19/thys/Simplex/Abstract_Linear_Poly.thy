(* Authors: F. Maric, M. Spasic, R. Thiemann *)
section \<open>Linear Polynomials and Constraints\<close>

theory Abstract_Linear_Poly  
  imports
    Simplex_Algebra 
begin

type_synonym var = nat

text\<open>(Infinite) linear polynomials as functions from vars to coeffs\<close>

definition fun_zero :: "var \<Rightarrow> 'a::zero" where
  [simp]: "fun_zero == \<lambda> v. 0"
definition fun_plus :: "(var \<Rightarrow> 'a) \<Rightarrow> (var \<Rightarrow> 'a) \<Rightarrow> var \<Rightarrow> 'a::plus" where
  [simp]: "fun_plus f1 f2 == \<lambda> v. f1 v + f2 v"
definition fun_scale :: "'a \<Rightarrow> (var \<Rightarrow> 'a) \<Rightarrow> (var \<Rightarrow> 'a::ring)" where
  [simp]: "fun_scale c f == \<lambda> v. c*(f v)"
definition fun_coeff :: "(var \<Rightarrow> 'a) \<Rightarrow> var \<Rightarrow> 'a" where
  [simp]: "fun_coeff f var = f var"
definition fun_vars :: "(var \<Rightarrow> 'a::zero) \<Rightarrow> var set" where
  [simp]: "fun_vars f = {v. f v \<noteq> 0}"
definition fun_vars_list :: "(var \<Rightarrow> 'a::zero) \<Rightarrow> var list" where
  [simp]: "fun_vars_list f = sorted_list_of_set {v. f v \<noteq> 0}"
definition fun_var :: "var \<Rightarrow> (var \<Rightarrow> 'a::{zero,one})" where
  [simp]: "fun_var x = (\<lambda> x'. if x' = x then 1 else 0)"
type_synonym 'a valuation = "var \<Rightarrow> 'a"
definition fun_valuate :: "(var \<Rightarrow> rat) \<Rightarrow> 'a valuation \<Rightarrow> ('a::rational_vector)" where
  [simp]: "fun_valuate lp val = (\<Sum>x\<in>{v. lp v \<noteq> 0}. lp x *R val x)"

text\<open>Invariant -- only finitely many variables\<close>
definition inv where
  [simp]: "inv c == finite {v. c v \<noteq> 0}"

lemma inv_fun_zero [simp]: 
  "inv fun_zero" by simp

lemma inv_fun_plus [simp]: 
  "\<lbrakk>inv (f1 :: nat \<Rightarrow> 'a::monoid_add); inv f2\<rbrakk> \<Longrightarrow> inv (fun_plus f1 f2)"
proof-
  have *: "{v. f1 v + f2 v \<noteq> (0 :: 'a)} \<subseteq> {v. f1 v \<noteq> (0 :: 'a)} \<union> {v. f2 v \<noteq> (0 :: 'a)}"
    by auto
  assume "inv f1" "inv f2"
  then show ?thesis
    using *
    by (auto simp add: finite_subset)
qed

lemma inv_fun_scale [simp]: 
  "inv (f :: nat \<Rightarrow> 'a::ring) \<Longrightarrow> inv (fun_scale r f)"
proof-
  have *: "{v. r * (f v) \<noteq> 0} \<subseteq> {v. f v \<noteq> 0}" 
    by auto
  assume "inv f"
  then show ?thesis
    using *
    by (auto simp add: finite_subset)
qed

text\<open>linear-poly type -- rat coeffs\<close>
  (* TODO: change rat to arbitrary ring *)

typedef  linear_poly = "{c :: var \<Rightarrow> rat. inv c}"
  by (rule_tac x="\<lambda> v. 0" in exI) auto


text\<open>Linear polynomials are of the form $a_1 \cdot x_1 + ... + a_n
\cdot x_n$. Their formalization follows the data-refinement approach
of Isabelle/HOL \cite{florian-refinement}. Abstract representation of
polynomials are functions mapping variables to their coefficients,
where only finitely many variables have non-zero
coefficients. Operations on polynomials are defined as operations on
functions. For example, the sum of @{term "p\<^sub>1"} and \<open>p\<^sub>2\<close> is
defined by @{term "\<lambda> v. p\<^sub>1 v + p\<^sub>2 v"} and the value of a polynomial
@{term "p"} for a valuation @{term "v"} (denoted by \<open>p\<lbrace>v\<rbrace>\<close>),
is defined by @{term "\<Sum>x\<in>{x. p x \<noteq> 0}. p x * v x"}. Executable
representation of polynomials uses RBT mappings instead of functions.
\<close>

setup_lifting type_definition_linear_poly 

text\<open>Vector space operations on polynomials\<close>
instantiation linear_poly :: rational_vector
begin

lift_definition zero_linear_poly :: "linear_poly" is fun_zero by (rule inv_fun_zero)

lift_definition plus_linear_poly :: "linear_poly \<Rightarrow> linear_poly \<Rightarrow> linear_poly" is fun_plus
  by (rule inv_fun_plus)

lift_definition scaleRat_linear_poly :: "rat \<Rightarrow> linear_poly \<Rightarrow> linear_poly" is fun_scale
  by (rule inv_fun_scale)

definition uminus_linear_poly :: "linear_poly \<Rightarrow> linear_poly" where 
  "uminus_linear_poly lp = -1 *R lp"

definition minus_linear_poly :: "linear_poly \<Rightarrow> linear_poly \<Rightarrow> linear_poly" where
  "minus_linear_poly lp1 lp2 = lp1 + (- lp2)"

instance
proof
  fix a b c::linear_poly
  show "a + b + c = a + (b + c)" by (transfer, auto)
  show "a + b = b + a" by (transfer, auto)
  show "0 + a = a" by (transfer, auto)
  show "-a + a = 0" unfolding uminus_linear_poly_def by (transfer, auto)
  show "a - b = a + (- b)" unfolding minus_linear_poly_def ..
next
  fix a :: rat and x y :: linear_poly
  show "a *R (x + y) = a *R x + a *R y" by (transfer, auto simp: field_simps)
next
  fix a b::rat and x::linear_poly
  show "(a + b) *R x = a *R x + b *R x" by (transfer, auto simp: field_simps)
  show "a *R b *R x = (a * b) *R x" by (transfer, auto simp: field_simps)
next
  fix x::linear_poly
  show "1 *R x = x" by (transfer, auto)
qed

end

text\<open>Coefficient\<close>
lift_definition coeff :: "linear_poly \<Rightarrow> var \<Rightarrow> rat" is fun_coeff .

lemma coeff_plus [simp] : "coeff (lp1 + lp2) var = coeff lp1 var + coeff lp2 var"
  by transfer auto

lemma coeff_scaleRat [simp]: "coeff (k *R lp1) var = k * coeff lp1 var"
  by transfer auto

lemma coeff_uminus [simp]: "coeff (-lp) var = - coeff lp var"
  unfolding uminus_linear_poly_def 
  by transfer auto

lemma coeff_minus [simp]: "coeff (lp1 - lp2) var = coeff lp1 var - coeff lp2 var"
  unfolding minus_linear_poly_def uminus_linear_poly_def
  by transfer auto

text\<open>Set of variables\<close>

lift_definition vars :: "linear_poly \<Rightarrow> var set" is fun_vars .

lemma coeff_zero: "coeff p x \<noteq> 0 \<longleftrightarrow> x \<in> vars p" 
  by transfer auto


lemma finite_vars: "finite (vars p)" 
  by transfer auto


text\<open>List of variables\<close>
lift_definition vars_list :: "linear_poly \<Rightarrow> var list" is fun_vars_list .

lemma set_vars_list: "set (vars_list lp) = vars lp"
  by transfer auto

text\<open>Construct single variable polynomial\<close>
lift_definition Var :: "var \<Rightarrow> linear_poly" is fun_var by auto

text\<open>Value of a polynomial in a given valuation\<close>
lift_definition valuate :: "linear_poly \<Rightarrow> 'a valuation \<Rightarrow> ('a::rational_vector)" is fun_valuate .

syntax
  "_valuate" :: "linear_poly \<Rightarrow> 'a valuation \<Rightarrow> 'a"    ("_ \<lbrace> _ \<rbrace>")
translations
  "p\<lbrace>v\<rbrace> " == "CONST valuate p v"

lemma valuate_zero: "(0 \<lbrace>v\<rbrace>) = 0" 
  by transfer auto

lemma 
  valuate_diff: "(p \<lbrace>v1\<rbrace>) - (p \<lbrace>v2\<rbrace>) = (p \<lbrace> \<lambda> x. v1 x - v2 x \<rbrace>)"
  by (transfer, simp add: sum_subtractf[THEN sym], auto simp: rational_vector.scale_right_diff_distrib)


lemma valuate_opposite_val: 
  shows "p \<lbrace> \<lambda> x. - v x \<rbrace> = - (p \<lbrace> v \<rbrace>)"
  using valuate_diff[of p "\<lambda> x. 0" v]
  by (auto simp add: valuate_def)

lemma valuate_nonneg:
  fixes v :: "'a::linordered_rational_vector valuation"
  assumes "\<forall> x \<in> vars p. (coeff p x > 0 \<longrightarrow> v x \<ge> 0) \<and> (coeff p x < 0 \<longrightarrow> v x \<le> 0)"
  shows "p \<lbrace> v \<rbrace> \<ge> 0" 
  using assms
proof (transfer, unfold fun_valuate_def, goal_cases)
  case (1 p v)
  from 1 have fin: "finite {v. p v \<noteq> 0}" by auto
  then show "0 \<le> (\<Sum>x\<in>{v. p v \<noteq> 0}. p x *R v x)" 
  proof (induct rule: finite_induct)
    case empty show ?case by auto
  next
    case (insert x F)
    show ?case unfolding sum.insert[OF insert(1-2)]
    proof (rule order.trans[OF _ add_mono[OF _ insert(3)]])
      show "0 \<le> p x *R v x" using scaleRat_leq1[of 0 "v x" "p x"]
        using scaleRat_leq2[of "v x" 0 "p x"] 1(2)
        by (cases "p x > 0"; cases "p x < 0"; auto)
    qed auto
  qed
qed

lemma valuate_nonpos:
  fixes v :: "'a::linordered_rational_vector valuation"
  assumes "\<forall> x \<in> vars p. (coeff p x > 0 \<longrightarrow> v x \<le> 0) \<and> (coeff p x < 0 \<longrightarrow> v x \<ge> 0)"
  shows "p \<lbrace> v \<rbrace> \<le> 0"
  using assms
  using valuate_opposite_val[of p v]
  using valuate_nonneg[of p "\<lambda> x. - v x"]
  using scaleRat_leq2[of "0::'a" _ "-1"]
  using scaleRat_leq2[of _ "0::'a" "-1"]
  by force

lemma valuate_uminus: "(-p) \<lbrace>v\<rbrace> = - (p \<lbrace>v\<rbrace>)"
  unfolding uminus_linear_poly_def 
  by (transfer, auto simp: sum_negf)

lemma valuate_add_lemma:
  fixes v :: "'a \<Rightarrow> 'b::rational_vector"
  assumes "finite {v. f1 v \<noteq> 0}" "finite {v. f2 v \<noteq> 0}"
  shows
    "(\<Sum>x\<in>{v. f1 v + f2 v \<noteq> 0}. (f1 x + f2 x) *R v x) =
   (\<Sum>x\<in>{v. f1 v \<noteq> 0}. f1 x *R v x) +  (\<Sum>x\<in>{v. f2 v \<noteq> 0}. f2 x *R v x)"
proof-
  let ?A = "{v. f1 v + f2 v \<noteq> 0} \<union> {v. f1 v + f2 v = 0 \<and> (f1 v \<noteq> 0 \<or> f2 v \<noteq> 0)}"
  have "?A = {v. f1 v \<noteq> 0 \<or> f2 v \<noteq> 0}"
    by auto
  then have
    "finite ?A"
    using assms
    by (subgoal_tac "{v. f1 v \<noteq> 0 \<or> f2 v \<noteq> 0} = {v. f1 v \<noteq> 0} \<union> {v. f2 v \<noteq> 0}") auto

  then have "(\<Sum>x\<in>{v. f1 v + f2 v \<noteq> 0}. (f1 x + f2 x) *R v x) = 
    (\<Sum>x\<in>{v. f1 v + f2 v \<noteq> 0} \<union> {v. f1 v + f2 v = 0 \<and> (f1 v \<noteq> 0 \<or> f2 v \<noteq> 0)}. (f1 x + f2 x) *R v x)"
    by (rule sum.mono_neutral_left) auto
  also have "... = (\<Sum>x \<in> {v. f1 v \<noteq> 0 \<or> f2 v \<noteq> 0}. (f1 x + f2 x) *R v x)"
    by (rule sum.cong) auto
  also have "... = (\<Sum>x \<in> {v. f1 v \<noteq> 0 \<or> f2 v \<noteq> 0}. f1 x *R v x) + 
                   (\<Sum>x \<in> {v. f1 v \<noteq> 0 \<or> f2 v \<noteq> 0}. f2 x *R v x)"
    by (simp add: scaleRat_left_distrib sum.distrib)
  also have "... = (\<Sum>x\<in>{v. f1 v \<noteq> 0}. f1 x *R v x) +  (\<Sum>x\<in>{v. f2 v \<noteq> 0}. f2 x *R v x)"
  proof-
    {
      fix f1 f2::"'a \<Rightarrow> rat"
      assume "finite {v. f1 v \<noteq> 0}" "finite {v. f2 v \<noteq> 0}"
      then have "finite {v. f1 v \<noteq> 0 \<or> f2 v \<noteq> 0 \<and> f1 v = 0}"
        by (subgoal_tac "{v. f1 v \<noteq> 0 \<or> f2 v \<noteq> 0} = {v. f1 v \<noteq> 0} \<union> {v. f2 v \<noteq> 0}") auto
      have "(\<Sum>x\<in>{v. f1 v \<noteq> 0 \<or> f2 v \<noteq> 0}. f1 x *R v x) = 
        (\<Sum>x\<in>{v. f1 v \<noteq> 0 \<or> (f2 v \<noteq> 0 \<and> f1 v = 0)}. f1 x *R v x)"
        by auto
      also have "... = (\<Sum>x\<in>{v. f1 v \<noteq> 0}. f1 x *R v x)"
        using \<open>finite {v. f1 v \<noteq> 0 \<or> f2 v \<noteq> 0 \<and> f1 v = 0}\<close>
        by (rule sum.mono_neutral_left[THEN sym]) auto
      ultimately have "(\<Sum>x\<in>{v. f1 v \<noteq> 0 \<or> f2 v \<noteq> 0}. f1 x *R v x) = 
        (\<Sum>x\<in>{v. f1 v \<noteq> 0}. f1 x *R v x)"
        by simp
    }
    note * = this
    show ?thesis
      using assms
      using *[of f1 f2]
      using *[of f2 f1]
      by (subgoal_tac "{v. f2 v \<noteq> 0 \<or> f1 v \<noteq> 0} = {v. f1 v \<noteq> 0 \<or> f2 v \<noteq> 0}") auto
  qed
  ultimately
  show ?thesis by simp
qed

lemma valuate_add:  "(p1 + p2) \<lbrace>v\<rbrace> = (p1 \<lbrace>v\<rbrace>) + (p2 \<lbrace>v\<rbrace>)"
  by (transfer, simp add: valuate_add_lemma)

lemma valuate_minus: "(p1 - p2) \<lbrace>v\<rbrace> = (p1 \<lbrace>v\<rbrace>) - (p2 \<lbrace>v\<rbrace>)"
  unfolding minus_linear_poly_def valuate_add 
  by (simp add: valuate_uminus)


lemma valuate_scaleRat:
  "(c *R lp) \<lbrace> v \<rbrace> = c *R ( lp\<lbrace>v\<rbrace> )"
proof (cases "c=0")
  case True
  then show ?thesis
    by (auto simp add: valuate_def zero_linear_poly_def Abs_linear_poly_inverse)
next
  case False
  then have "\<And> v. Rep_linear_poly (c *R lp) v = c * (Rep_linear_poly lp v)"
    unfolding scaleRat_linear_poly_def
    using Abs_linear_poly_inverse[of "\<lambda>v. c * Rep_linear_poly lp v"]
    using Rep_linear_poly
    by auto
  then show ?thesis
    unfolding valuate_def
    using \<open>c \<noteq> 0\<close>
    by auto (subst rational_vector.scale_sum_right, auto)
qed

lemma valuate_Var: "(Var x) \<lbrace>v\<rbrace> = v x"
  by transfer auto

lemma valuate_sum: "((\<Sum>x\<in>A. f x) \<lbrace> v \<rbrace>) = (\<Sum>x\<in>A. ((f x) \<lbrace> v \<rbrace>))" 
  by (induct A rule: infinite_finite_induct, auto simp: valuate_zero valuate_add)

lemma distinct_vars_list: 
  "distinct (vars_list p)"
  by transfer (use distinct_sorted_list_of_set in auto)


lemma zero_coeff_zero: "p = 0 \<longleftrightarrow> (\<forall> v. coeff p v = 0)"
  by transfer auto

lemma all_val: 
  assumes "\<forall> (v::var \<Rightarrow> 'a::lrv). \<exists> v'. (\<forall> x \<in> vars p. v' x = v x) \<and> (p \<lbrace>v'\<rbrace> = 0)"
  shows "p = 0"
proof (subst zero_coeff_zero, rule allI)
  fix x
  show "coeff p x = 0"
  proof (cases "x \<in> vars p")
    case False
    then show ?thesis
      using coeff_zero[of p x]
      by simp
  next
    case True
    have "(0::'a::lrv) \<noteq> (1::'a)"
      using zero_neq_one
      by auto

    let ?v = "\<lambda> x'. if x = x' then 1 else 0::'a"
    obtain v' where "\<forall> x \<in> vars p. v' x = ?v x" "p \<lbrace>v'\<rbrace> = 0"
      using assms
      by (erule_tac x="?v" in allE) auto
    then have "\<forall> x' \<in> vars p. v' x' = (if x = x' then 1 else 0)" "p \<lbrace>v'\<rbrace> = 0"
      by auto

    let ?fp = "Rep_linear_poly p"
    have "{x. ?fp x \<noteq> 0 \<and> v' x \<noteq> (0 :: 'a)} = {x}"
      using \<open>x \<in> vars p\<close> unfolding vars_def
    proof (safe, simp_all)
      fix x'
      assume "v' x' \<noteq> 0" "Rep_linear_poly p x' \<noteq> 0"
      then show "x' = x"
        using \<open>\<forall> x' \<in> vars p. v' x' = (if x = x' then 1 else 0)\<close>
        unfolding vars_def
        by (erule_tac x="x'" in ballE) (simp_all split: if_splits)
    next
      assume "v' x = 0" "Rep_linear_poly p x \<noteq> 0"
      then show False
        using \<open>\<forall> x' \<in> vars p. v' x' = (if x = x' then 1 else 0)\<close>
        using \<open>0 \<noteq> 1\<close>
        unfolding vars_def
        by simp
    qed

    have "p \<lbrace>v'\<rbrace> = (\<Sum>x\<in>{v. ?fp v \<noteq> 0}. ?fp x *R v' x)"
      unfolding valuate_def
      by auto
    also have "... = (\<Sum>x\<in>{v. ?fp v \<noteq> 0 \<and> v' v \<noteq> 0}. ?fp x *R v' x)"
      apply (rule sum.mono_neutral_left[THEN sym])
      using Rep_linear_poly[of p]
      by auto
    also have "... = ?fp x *R v' x"
      using \<open>{x. ?fp x \<noteq> 0 \<and> v' x \<noteq> (0 :: 'a)} = {x}\<close>
      by simp
    also have "... = ?fp x *R 1"
      using \<open>x \<in> vars p\<close>
      using \<open>\<forall> x' \<in> vars p. v' x' = (if x = x' then 1 else 0)\<close>
      by simp
    ultimately
    have "p \<lbrace>v'\<rbrace> = ?fp x *R 1"
      by simp
    then have "coeff p x *R (1::'a)= 0"
      using \<open>p \<lbrace>v'\<rbrace> = 0\<close>
      unfolding coeff_def
      by simp
    then show ?thesis
      using rational_vector.scale_eq_0_iff
      using \<open>0 \<noteq> 1\<close>
      by simp
  qed
qed

lift_definition lp_monom :: "rat \<Rightarrow> var \<Rightarrow> linear_poly" is
  "\<lambda> c x y. if x = y then c else 0" by auto

lemma valuate_lp_monom: "((lp_monom c x) \<lbrace>v\<rbrace>) = c * (v x)" 
proof (transfer, simp, goal_cases) 
  case (1 c x v)
  have id: "{v. x = v \<and> (x = v \<longrightarrow> c \<noteq> 0)} = (if c = 0 then {} else {x})" by auto
  show ?case unfolding id
    by (cases "c = 0", auto)
qed

lemma valuate_lp_monom_1[simp]: "((lp_monom 1 x) \<lbrace>v\<rbrace>) = v x"
  by transfer simp 

lemma coeff_lp_monom [simp]:
  shows "coeff (lp_monom c v) v' = (if v = v' then c else 0)"
  by (transfer, auto)

lemma vars_uminus [simp]: "vars (-p) = vars p"
  unfolding uminus_linear_poly_def
  by transfer auto

lemma vars_plus [simp]: "vars (p1 + p2) \<subseteq> vars p1 \<union> vars p2"
  by transfer auto

lemma vars_minus [simp]: "vars (p1 - p2) \<subseteq> vars p1 \<union> vars p2"
  unfolding minus_linear_poly_def
  using vars_plus[of p1 "-p2"] vars_uminus[of p2]
  by simp

lemma vars_lp_monom: "vars (lp_monom r x) = (if r = 0 then {} else {x})" 
  by (transfer, auto)

lemma vars_scaleRat1: "vars (c *R p) \<subseteq> vars p"
  by transfer auto

lemma vars_scaleRat: "c \<noteq> 0 \<Longrightarrow> vars(c *R p) = vars p"
  by transfer auto

lemma vars_Var [simp]: "vars (Var x) = {x}"
  by transfer auto

lemma coeff_Var1 [simp]: "coeff (Var x) x = 1"
  by transfer auto

lemma coeff_Var2: "x \<noteq> y \<Longrightarrow> coeff (Var x) y = 0"
  by transfer auto

lemma valuate_depend:
  assumes "\<forall> x \<in> vars p. v x = v' x"
  shows "(p \<lbrace>v\<rbrace>) = (p \<lbrace>v'\<rbrace>)"
  using assms
  by transfer auto

lemma valuate_update_x_lemma:
  fixes v1 v2 :: "'a::rational_vector valuation"
  assumes
    "\<forall>y. f y \<noteq> 0 \<longrightarrow> y \<noteq> x \<longrightarrow> v1 y = v2 y"
    "finite {v. f v \<noteq> 0}"
  shows
    "(\<Sum>x\<in>{v. f v \<noteq> 0}. f x *R v1 x) + f x *R (v2 x - v1 x) = (\<Sum>x\<in>{v. f v \<noteq> 0}. f x *R v2 x)"
proof (cases "f x = 0")
  case True
  then have "\<forall>y. f y \<noteq> 0 \<longrightarrow> v1 y = v2 y"
    using assms(1) by auto
  then show ?thesis using \<open>f x = 0\<close> by auto
next
  case False
  let ?A = "{v. f v \<noteq> 0}" and ?Ax = "{v. v \<noteq> x \<and> f v \<noteq> 0}"
  have "?A = ?Ax \<union> {x}"
    using \<open>f x \<noteq> 0\<close> by auto
  then have "(\<Sum>x\<in>?A. f x *R v1 x) = f x *R v1 x + (\<Sum>x\<in>?Ax. f x *R v1 x)"
    "(\<Sum>x\<in>?A. f x *R v2 x) = f x *R v2 x + (\<Sum>x\<in>?Ax. f x *R v2 x)"
    using assms(2) by auto
  moreover
  have "\<forall> y \<in> ?Ax. v1 y = v2 y"
    using assms by auto
  moreover
  have "f x *R v1 x + f x *R (v2 x - v1 x) = f x *R v2 x"
    by (subst rational_vector.scale_right_diff_distrib) auto
  ultimately
  show ?thesis by simp
qed

lemma valuate_update_x:
  fixes v1 v2 :: "'a::rational_vector valuation"
  assumes "\<forall>y \<in> vars lp. y\<noteq>x \<longrightarrow> v1 y = v2 y"
  shows "lp \<lbrace>v1\<rbrace>  + coeff lp x *R (v2 x - v1 x) = (lp \<lbrace>v2\<rbrace>)"
  using assms 
  unfolding valuate_def vars_def coeff_def
  using valuate_update_x_lemma[of "Rep_linear_poly lp" x v1 v2] Rep_linear_poly
  by auto

lemma vars_zero: "vars 0 = {}"
  using zero_coeff_zero coeff_zero by auto

lemma vars_empty_zero: "vars lp = {} \<longleftrightarrow> lp = 0"
  using zero_coeff_zero coeff_zero by auto

definition max_var:: "linear_poly \<Rightarrow> var" where
  "max_var lp \<equiv> if lp = 0 then 0 else Max (vars lp)"

lemma max_var_max:
  assumes "a \<in> vars lp"
  shows "max_var lp \<ge> a"
  using assms
  by (auto simp add: finite_vars max_var_def vars_zero)

lemma max_var_code[code]: 
  "max_var lp = (let vl = vars_list lp 
                in if vl = [] then 0 else foldl max (hd vl) (tl vl))"
proof (cases "lp = (0::linear_poly)")
  case True
  then show ?thesis
    using set_vars_list[of lp]
    by (auto simp add: max_var_def vars_zero)
next
  case False
  then show ?thesis
    using set_vars_list[of lp, THEN sym]
    using vars_empty_zero[of lp]
    unfolding max_var_def Let_def 
    using Max.set_eq_fold[of "hd (vars_list lp)" "tl (vars_list lp)"]
    by (cases "vars_list lp", auto simp: foldl_conv_fold intro!: fold_cong)
qed

definition monom_var:: "linear_poly \<Rightarrow> var" where
  "monom_var l = max_var l"

definition monom_coeff:: "linear_poly \<Rightarrow> rat" where
  "monom_coeff l = coeff l (monom_var l)"

definition is_monom :: "linear_poly \<Rightarrow> bool" where
  "is_monom l \<longleftrightarrow> length (vars_list l) = 1"

lemma is_monom_vars_not_empty:
  "is_monom l \<Longrightarrow> vars l \<noteq> {}"
  by (auto simp add: is_monom_def vars_list_def) (auto simp add: vars_def)

lemma monom_var_in_vars:
  "is_monom l \<Longrightarrow> monom_var l \<in> vars l"
  using vars_zero
  by (auto simp add: monom_var_def max_var_def is_monom_vars_not_empty finite_vars is_monom_def)

lemma zero_is_no_monom[simp]: "\<not> is_monom 0"
  using is_monom_vars_not_empty vars_zero by blast

lemma is_monom_monom_coeff_not_zero:
  "is_monom l \<Longrightarrow> monom_coeff l \<noteq> 0"
  by (simp add: coeff_zero monom_var_in_vars monom_coeff_def)

lemma list_two_elements:
  "\<lbrakk>y \<in> set l; x \<in> set l; length l = Suc 0; y \<noteq> x\<rbrakk> \<Longrightarrow> False"
  by (induct l) auto

lemma is_monom_vars_monom_var:
  assumes "is_monom l"
  shows "vars l = {monom_var l}"
proof-
  have "\<And>x. \<lbrakk>is_monom l; x \<in> vars l\<rbrakk> \<Longrightarrow> monom_var l = x"
  proof-
    fix x
    assume "is_monom l" "x \<in> vars l"
    then have "x \<in> set (vars_list l)"
      using finite_vars
      by (auto simp add: vars_list_def vars_def)
    show "monom_var l = x"
    proof(rule ccontr)
      assume "monom_var l \<noteq> x"
      then have "\<exists>y. monom_var l = y \<and> y \<noteq> x"
        by simp
      then obtain y where "monom_var l = y" "y \<noteq> x"
        by auto
      then have "Rep_linear_poly l y \<noteq> 0"
        using monom_var_in_vars \<open>is_monom l\<close>
        by (auto simp add: vars_def)
      then have "y \<in> set (vars_list l)"
        using finite_vars
        by (auto simp add: vars_def vars_list_def)
      then show False
        using \<open>x \<in> set (vars_list l)\<close> \<open>is_monom l\<close> \<open>y \<noteq> x\<close>
        using list_two_elements
        by (simp add: is_monom_def)
    qed
  qed
  then show "vars l = {monom_var l}"
    using assms
    by (auto simp add: monom_var_in_vars)
qed

lemma monom_valuate:
  assumes "is_monom m"
  shows "m\<lbrace>v\<rbrace> = (monom_coeff m) *R v (monom_var m)"
  using assms
  using is_monom_vars_monom_var
  by (simp add: vars_def coeff_def monom_coeff_def valuate_def)

lemma coeff_zero_simp [simp]:
  "coeff 0 v = 0"
  using zero_coeff_zero by blast

lemma poly_eq_iff: "p = q \<longleftrightarrow> (\<forall> v. coeff p v = coeff q v)"
  by transfer auto

lemma poly_eqI:
  assumes "\<And>v. coeff p v = coeff q v"
  shows "p = q"
  using assms poly_eq_iff by simp

lemma coeff_sum_list:
  assumes "distinct xs"
  shows "coeff (\<Sum>x\<leftarrow>xs. f x *R lp_monom 1 x) v = (if v \<in> set xs then f v else 0)"
  using assms by (induction xs) auto

lemma linear_poly_sum:
  "p \<lbrace> v \<rbrace> = (\<Sum>x\<in>vars p. coeff p x *R v x)"
  by transfer simp

lemma all_valuate_zero: assumes "\<And>(v::'a::lrv valuation). p \<lbrace>v\<rbrace> = 0"
  shows "p = 0"
  using all_val assms by blast

lemma linear_poly_eqI: assumes "\<And>(v::'a::lrv valuation). (p \<lbrace>v\<rbrace>) = (q \<lbrace>v\<rbrace>)"
  shows "p = q"
  using assms 
proof -
  have "(p - q) \<lbrace> v \<rbrace> = 0" for v::"'a::lrv valuation"
    using assms by (subst valuate_minus) auto
  then have "p - q = 0"
    by (intro all_valuate_zero) auto
  then show ?thesis
    by simp
qed

lemma monom_poly_assemble:
  assumes "is_monom p"
  shows "monom_coeff p *R lp_monom 1 (monom_var p) = p"
  by (simp add: assms linear_poly_eqI monom_valuate valuate_scaleRat)

lemma coeff_sum: "coeff (sum (f :: _ \<Rightarrow> linear_poly) is) x = sum (\<lambda> i. coeff (f i) x) is" 
  by (induct "is" rule: infinite_finite_induct, auto)

end
