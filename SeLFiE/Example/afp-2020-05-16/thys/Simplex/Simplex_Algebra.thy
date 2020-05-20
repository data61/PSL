(* Authors: F. Maric, M. Spasic *)
section \<open>Linearly Ordered Rational Vectors\<close>
theory Simplex_Algebra
  imports 
    HOL.Rat 
    HOL.Real_Vector_Spaces
begin

class scaleRat =
  fixes scaleRat :: "rat \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "*R" 75)
begin

abbreviation
  divideRat :: "'a \<Rightarrow> rat \<Rightarrow> 'a" (infixl "'/R" 70)
  where
    "x /R r == scaleRat (inverse r) x"
end

class rational_vector = scaleRat + ab_group_add + 
  assumes scaleRat_right_distrib: "scaleRat a (x + y) = scaleRat a x + scaleRat a y"
    and scaleRat_left_distrib: "scaleRat (a + b) x = scaleRat a x + scaleRat b x"
    and scaleRat_scaleRat: "scaleRat a (scaleRat b x) = scaleRat (a * b) x"
    and scaleRat_one: "scaleRat 1 x = x" 

interpretation rational_vector:
  vector_space "scaleRat :: rat \<Rightarrow> 'a \<Rightarrow> 'a::rational_vector"
  by (unfold_locales) (simp_all add: scaleRat_right_distrib  scaleRat_left_distrib scaleRat_scaleRat scaleRat_one)

class ordered_rational_vector = rational_vector + order

class linordered_rational_vector = ordered_rational_vector + linorder +
  assumes plus_less: "(a::'a) < b \<Longrightarrow> a + c < b + c" and
    scaleRat_less1: "\<lbrakk>(a::'a) < b; k > 0\<rbrakk> \<Longrightarrow> (k *R a) < (k *R b)" and 
    scaleRat_less2: "\<lbrakk>(a::'a) < b; k < 0\<rbrakk> \<Longrightarrow> (k *R a) > (k *R b)"
begin 

lemma scaleRat_leq1: "\<lbrakk> a \<le> b; k > 0\<rbrakk> \<Longrightarrow> k *R a \<le> k *R b"
  unfolding le_less
  using scaleRat_less1[of a b k]
  by auto

lemma scaleRat_leq2: "\<lbrakk> a \<le> b; k < 0\<rbrakk> \<Longrightarrow> k *R a \<ge> k *R b"
  unfolding le_less
  using scaleRat_less2[of a b k]
  by auto

lemma zero_scaleRat
  [simp]: "0 *R v = zero"
  using scaleRat_left_distrib[of 0 0 v]
  by auto

lemma scaleRat_zero
  [simp]: "a *R (0::'a) = 0"
  using scaleRat_right_distrib[of a 0 0]
  by auto

lemma scaleRat_uminus [simp]:
  "-1 *R x = - (x :: 'a)"
proof-
  have "0  = -1 *R x + x"
    using scaleRat_left_distrib[of "-1" 1 x]
    by (simp add: scaleRat_one)
  have "-x = 0 - x"
    by simp
  then have "-x = -1 *R x + x - x"
    using \<open>0  = -1 *R x + x\<close>
    by simp
  then show ?thesis
    by (simp add: add_assoc)
qed

lemma minus_lt: "(a::'a) < b \<longleftrightarrow> a - b < 0"
  using plus_less[of a b "-b"]
  using plus_less[of "a - b" 0 b]
  by (auto simp add: add_assoc)

lemma minus_gt: "(a::'a) < b \<longleftrightarrow> 0 < b - a"
  using plus_less[of a b "-a"]
  using plus_less[of 0 "b-a" a]
  by (auto simp add: add_assoc)

lemma minus_leq:
  "(a::'a) \<le> b \<longleftrightarrow> a - b \<le> 0"
proof-
  have *: "a \<le> b \<Longrightarrow> a - b \<le> (0 :: 'a)"
    using minus_gt[of a b]
    using scaleRat_less2[of 0 "b-a" "-1"]
    by (auto simp add: not_less_iff_gr_or_eq)
  have **: "a - b \<le> 0 \<Longrightarrow> a \<le> b"
  proof-
    assume "a - b \<le> 0"
    show ?thesis
    proof(cases "a - b < 0")
      case True
      then show ?thesis
        using plus_less[of "a - b" 0 b]
        by (simp add: add_assoc )
    next
      case False
      then show ?thesis
        using \<open>a - b \<le> 0\<close>
        by (simp add:antisym_conv1)
    qed
  qed
  show ?thesis
    using * **
    by auto
qed

lemma minus_geq: "(a::'a) \<le> b \<longleftrightarrow> 0 \<le> b - a"
proof-
  have *: "a \<le> b \<Longrightarrow> 0 \<le> b - a"
    using minus_gt[of a b]
    by (auto simp add: not_less_iff_gr_or_eq)
  have **: "0 \<le> b - a \<Longrightarrow> a \<le> b"
  proof-
    assume "0 \<le> b - a"
    show ?thesis
    proof(cases "0 < b - a")
      case True
      then show ?thesis
        using plus_less[of 0 "b - a" a]
        by (simp add: add_assoc)
    next
      case False
      then show ?thesis
        using \<open>0 \<le> b - a\<close>
        using eq_iff[of "b - a" 0]
        by auto
    qed
  qed
  show ?thesis
    using * **
    by auto
qed

lemma divide_lt:
  "\<lbrakk>c *R (a::'a) < b; (c::rat) > 0 \<rbrakk> \<Longrightarrow> a < (1/c) *R b"
  using scaleRat_less1[of "c *R a" b "1/c"]
  by (simp add: scaleRat_one scaleRat_scaleRat)

lemma divide_gt:
  "\<lbrakk>c *R (a::'a) > b;(c::rat) > 0\<rbrakk> \<Longrightarrow> a > (1/c) *R b"
  using scaleRat_less1[of b "c *R a" "1/c"]
  by (simp add: scaleRat_one scaleRat_scaleRat)

lemma divide_leq:
  "\<lbrakk>c *R (a::'a) \<le>  b; (c::rat) > 0\<rbrakk> \<Longrightarrow> a \<le> (1/c) *R b"
proof(cases "c *R a < b")
  assume "c > 0"
  case True
  then show ?thesis
    using divide_lt[of c a b]
    using \<open>c > 0\<close>
    by simp
next
  assume "c *R a \<le>  b" "c > 0"
  case False
  then have *: "c *R a = b"
    using \<open>c *R a \<le> b\<close>
    by simp
  then show ?thesis
    using \<open>c > 0\<close>
    by (auto simp add: scaleRat_one scaleRat_scaleRat)
qed

lemma divide_geq:
  "\<lbrakk>c *R (a::'a) \<ge> b; (c::rat) > 0\<rbrakk> \<Longrightarrow> a \<ge> (1/c) *R b"
proof(cases "c *R a > b")
  assume "c > 0"
  case True
  then show ?thesis
    using divide_gt[of b c a]
    using \<open>c > 0\<close>
    by simp
next
  assume "c *R a \<ge> b" "c > 0"
  case False
  then have *: "c *R a = b"
    using \<open>c *R a \<ge> b\<close>
    by simp
  then show ?thesis
    using \<open>c > 0\<close>
    by (auto simp add: scaleRat_one scaleRat_scaleRat)
qed

lemma divide_lt1:
  "\<lbrakk>c *R (a::'a) < b; (c::rat) < 0\<rbrakk> \<Longrightarrow> a > (1/c) *R b"
  using scaleRat_less2[of "c *R a" b "1/c"]
  by (simp add: scaleRat_scaleRat scaleRat_one)

lemma divide_gt1:
  "\<lbrakk>c *R (a::'a) > b; (c::rat) < 0 \<rbrakk> \<Longrightarrow>  a < (1/c) *R b"
  using scaleRat_less2[of b "c *R a" "1/c"]
  by (simp add: scaleRat_scaleRat scaleRat_one)

lemma divide_leq1:
  "\<lbrakk>c *R (a::'a) \<le>  b; (c::rat) < 0\<rbrakk> \<Longrightarrow> a \<ge> (1/c) *R b"
proof(cases "c *R a < b")
  assume "c < 0"
  case True
  then show ?thesis
    using divide_lt1[of c a b]
    using \<open>c < 0\<close>
    by simp
next
  assume "c *R a \<le>  b" "c < 0"
  case False
  then have *: "c *R a = b"
    using \<open>c *R a \<le> b\<close>
    by simp
  then show ?thesis
    using \<open>c < 0\<close>
    by (auto simp add: scaleRat_one scaleRat_scaleRat)
qed

lemma divide_geq1:
  "\<lbrakk>c *R (a::'a) \<ge> b; (c::rat) < 0\<rbrakk> \<Longrightarrow> a \<le> (1/c) *R b"
proof(cases "c *R a > b")
  assume "c < 0"
  case True
  then show ?thesis
    using divide_gt1[of b c a]
    using \<open>c < 0\<close>
    by simp
next
  assume "c *R a \<ge> b" "c < 0"
  case False
  then have *: "c *R a = b"
    using \<open>c *R a \<ge> b\<close>
    by simp
  then show ?thesis
    using \<open>c < 0\<close>
    by (auto simp add: scaleRat_one scaleRat_scaleRat)
qed

end

class lrv = linordered_rational_vector + one +
  assumes zero_neq_one: "0 \<noteq> 1"

subclass (in linordered_rational_vector) ordered_ab_semigroup_add
proof
  fix a b c
  assume "a \<le> b"
  then show "c + a \<le> c + b"
    using plus_less[of a b c]
    by (auto simp add: add_ac le_less)
qed

instantiation rat :: rational_vector
begin
definition scaleRat_rat :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
  [simp]: "x *R y = x * y"
instance by standard (auto simp add: field_simps)
end

instantiation rat :: ordered_rational_vector
begin
instance ..
end

instantiation rat :: linordered_rational_vector
begin
instance by standard (auto simp add: field_simps)
end

instantiation rat :: lrv
begin
instance by standard (auto simp add: field_simps)
end

lemma uminus_less_lrv[simp]: fixes a b :: "'a :: lrv"
  shows "- a < - b \<longleftrightarrow> b < a" 
proof -
  have "(- a < - b) = (-1 *R a < -1 *R b)" by simp
  also have "\<dots> \<longleftrightarrow> (b < a)" 
    using scaleRat_less2[of _ _ "-1"] scaleRat_less2[of "-1 *R a" "-1 *R b" "-1"] by auto 
  finally show ?thesis .
qed

end
