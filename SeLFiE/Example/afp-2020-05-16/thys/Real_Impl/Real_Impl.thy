(*  Title:       Implementing field extensions of the form Q[sqrt(b)]
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
section \<open>A representation of real numbers via triples\<close>

theory Real_Impl
imports
  Sqrt_Babylonian.Sqrt_Babylonian
begin

text \<open>We represent real numbers of the form $p + q \cdot \sqrt{b}$ for $p,q \in \rats$, $n \in \nats$
by triples $(p,q,b)$. However, we require the invariant that $\sqrt{b}$ is irrational.
Most binary operations are implemented via partial functions where the common the restriction is that
the numbers $b$ in both triples have to be identical. So, we support addition of $\sqrt{2} + \sqrt{2}$,
but not $\sqrt{2} + \sqrt{3}$.\<close>

text \<open>The set of natural numbers whose sqrt is irrational\<close>

definition "sqrt_irrat = { q :: nat. \<not> (\<exists> p. p * p = rat_of_nat q)}"

lemma sqrt_irrat: assumes choice: "q = 0 \<or> b \<in> sqrt_irrat"
   and eq: "real_of_rat p + real_of_rat q * sqrt (of_nat b) = 0"
   shows "q = 0"
  using choice
proof (cases "q = 0")
  case False
  with choice have sqrt_irrat: "b \<in> sqrt_irrat" by blast
  from eq have "real_of_rat q * sqrt (of_nat b) = real_of_rat (- p)"
    by (auto simp: of_rat_minus)
  then obtain p where "real_of_rat q * sqrt (of_nat b) = real_of_rat p" by blast
  from arg_cong[OF this, of "\<lambda> x. x * x"] have "real_of_rat (q * q) * (sqrt (of_nat b) * sqrt (of_nat b)) =
    real_of_rat (p * p)" by (auto simp: field_simps of_rat_mult)
  also have "sqrt (of_nat b) * sqrt (of_nat b) = of_nat b" by simp
  finally have "real_of_rat (q * q * rat_of_nat b) = real_of_rat (p * p)" by (auto simp: of_rat_mult)
  hence "q * q * (rat_of_nat b) = p * p" by auto
  from arg_cong[OF this, of "\<lambda> x. x / (q * q)"]
  have "(p / q) * (p / q) = rat_of_nat b" using False by (auto simp: field_simps)
  with sqrt_irrat show ?thesis unfolding sqrt_irrat_def by blast
qed

text \<open>To represent  numbers of the form $p + q \cdot \sqrt{b}$, use mini algebraic numbers, i.e.,
  triples $(p,q,b)$ with irrational $\sqrt{b}$.\<close>
typedef mini_alg =
  "{(p,q,b) | (p :: rat) (q :: rat) (b :: nat).
  q = 0 \<or> b \<in> sqrt_irrat}"
  by auto

setup_lifting type_definition_mini_alg

lift_definition real_of :: "mini_alg \<Rightarrow> real" is
  "\<lambda> (p,q,b). of_rat p + of_rat q * sqrt (of_nat b)" .

lift_definition ma_of_rat :: "rat \<Rightarrow> mini_alg" is "\<lambda> x. (x,0,0)" by auto

lift_definition ma_rat :: "mini_alg \<Rightarrow> rat" is fst .
lift_definition ma_base :: "mini_alg \<Rightarrow> nat" is "snd o snd" .
lift_definition ma_coeff :: "mini_alg \<Rightarrow> rat" is "fst o snd" .

lift_definition ma_uminus :: "mini_alg \<Rightarrow> mini_alg" is
  "\<lambda> (p1,q1,b1). (- p1, - q1, b1)" by auto

lift_definition ma_compatible :: "mini_alg \<Rightarrow> mini_alg \<Rightarrow> bool" is
  "\<lambda> (p1,q1,b1) (p2,q2,b2). q1 = 0 \<or> q2 = 0 \<or> b1 = b2" .

definition ma_normalize :: "rat \<times> rat \<times> nat \<Rightarrow> rat \<times> rat \<times> nat" where
  "ma_normalize x \<equiv> case x of (a,b,c) \<Rightarrow> if b = 0 then (a,0,0) else (a,b,c)"

lemma ma_normalize_case[simp]: "(case ma_normalize r of (a,b,c) \<Rightarrow> real_of_rat a + real_of_rat b * sqrt (of_nat c))
  = (case r of (a,b,c) \<Rightarrow> real_of_rat a + real_of_rat b * sqrt (of_nat c))"
  by (cases r, auto simp: ma_normalize_def)

lift_definition ma_plus :: "mini_alg \<Rightarrow> mini_alg \<Rightarrow> mini_alg" is
  "\<lambda> (p1,q1,b1) (p2,q2,b2). if q1 = 0 then
    (p1 + p2, q2, b2) else ma_normalize (p1 + p2, q1 + q2, b1)" by (auto simp: ma_normalize_def)

lift_definition ma_times :: "mini_alg \<Rightarrow> mini_alg \<Rightarrow> mini_alg" is
  "\<lambda> (p1,q1,b1) (p2,q2,b2). if q1 = 0 then
    ma_normalize (p1*p2, p1*q2, b2) else
    ma_normalize (p1*p2 + of_nat b2*q1*q2, p1*q2 + q1*p2, b1)" by (auto simp: ma_normalize_def)

lift_definition ma_inverse :: "mini_alg \<Rightarrow> mini_alg" is
   "\<lambda> (p,q,b). let d = inverse (p * p - of_nat b * q * q) in
   ma_normalize (p * d, - q * d, b)" by (auto simp: Let_def ma_normalize_def)

lift_definition ma_floor :: "mini_alg \<Rightarrow> int" is
  "\<lambda> (p,q,b). case (quotient_of p,quotient_of q) of ((z1,n1),(z2,n2)) \<Rightarrow>
    let z2n1 = z2 * n1; z1n2 = z1 * n2; n12 = n1 * n2; prod = z2n1 * z2n1 * int b in
    (z1n2 + (if z2n1 \<ge> 0 then sqrt_int_floor_pos prod else - sqrt_int_ceiling_pos prod)) div n12" .

lift_definition ma_sqrt :: "mini_alg \<Rightarrow> mini_alg" is
   "\<lambda> (p,q,b). let (a,b) = quotient_of p; aa = abs (a * b) in
   case sqrt_int aa of [] \<Rightarrow> (0,inverse (of_int b),nat aa) | (Cons s _) \<Rightarrow> (of_int s / of_int b,0,0)"
proof (unfold Let_def)
   fix prod :: "rat \<times> rat \<times> nat"
   obtain p q b where prod: "prod = (p,q,b)" by (cases prod, auto)
   obtain a b where p: "quotient_of p = (a,b)" by force
   show "\<exists>p q b. (case prod of
                     (p, q, b) \<Rightarrow>
                       case quotient_of p of
                       (a, b) \<Rightarrow>
                         (case sqrt_int \<bar>a * b\<bar> of [] \<Rightarrow> (0, inverse (of_int b), nat \<bar>a * b\<bar>)
                         | s # x \<Rightarrow> (of_int s / of_int b, 0, 0))) =
                    (p, q, b) \<and>
                    (q = 0 \<or> b \<in> sqrt_irrat)"
   proof (cases "sqrt_int (abs (a * b))")
     case Nil
     from sqrt_int[of "abs (a * b)"] Nil have irrat: "\<not> (\<exists> y. y * y = \<bar>a * b\<bar>)" by auto
     have "nat \<bar>a * b\<bar> \<in> sqrt_irrat"
     proof (rule ccontr)
       assume "nat \<bar>a * b\<bar> \<notin> sqrt_irrat"
       then obtain x :: rat
       where "x * x = rat_of_nat (nat \<bar>a * b\<bar>)" unfolding sqrt_irrat_def by auto
       hence "x * x = rat_of_int \<bar>a * b\<bar>" by auto
       from sqr_rat_of_int[OF this] irrat show False by blast
     qed
     thus ?thesis using Nil by (auto simp: prod p)
   qed (auto simp: prod p Cons)
qed

lift_definition ma_equal :: "mini_alg \<Rightarrow> mini_alg \<Rightarrow> bool" is
   "\<lambda> (p1,q1,b1) (p2,q2,b2).
   p1 = p2 \<and> q1 = q2 \<and> (q1 = 0 \<or> b1 = b2)" .

lift_definition ma_ge_0 :: "mini_alg \<Rightarrow> bool" is
  "\<lambda> (p,q,b). let bqq = of_nat b * q * q; pp = p * p in
  0 \<le> p \<and> bqq \<le> pp \<or> 0 \<le> q \<and> pp \<le> bqq" .

lift_definition ma_is_rat :: "mini_alg \<Rightarrow> bool" is
  "\<lambda> (p,q,b). q = 0" .

definition ge_0 :: "real \<Rightarrow> bool" where [code del]: "ge_0 x = (x \<ge> 0)"

lemma ma_ge_0: "ge_0 (real_of x) = ma_ge_0 x"
proof (transfer, unfold Let_def, clarsimp)
  fix p' q' :: rat and b' :: nat
  assume b': "q' = 0 \<or> b' \<in> sqrt_irrat"
  define b where "b = real_of_nat b'"
  define p where "p = real_of_rat p'"
  define q where "q = real_of_rat q'"
  from b' have b: "0 \<le> b" "q = 0 \<or> b' \<in> sqrt_irrat" unfolding b_def q_def by auto
  define qb where "qb = q * sqrt b"
  from b have sqrt: "sqrt b \<ge> 0" by auto
  from b(2) have disj: "q = 0 \<or> b \<noteq> 0" unfolding sqrt_irrat_def b_def by auto
  have bdef: "b = real_of_rat (of_nat b')" unfolding b_def by auto
  have "(0 \<le> p + q * sqrt b) = (0 \<le> p + qb)" unfolding qb_def by simp
  also have "\<dots> \<longleftrightarrow> (0 \<le> p \<and> abs qb \<le> abs p \<or> 0 \<le> qb \<and> abs p \<le> abs qb)" by arith
  also have "\<dots> \<longleftrightarrow> (0 \<le> p \<and> qb * qb \<le> p * p \<or> 0 \<le> qb \<and> p * p \<le> qb * qb)"
    unfolding abs_lesseq_square ..
  also have "qb * qb = b * q * q" unfolding qb_def
    using b by auto
  also have "0 \<le> qb \<longleftrightarrow> 0 \<le> q" unfolding qb_def using sqrt disj
    by (metis le_cases mult_eq_0_iff mult_nonneg_nonneg mult_nonpos_nonneg order_class.order.antisym  qb_def real_sqrt_eq_zero_cancel_iff)
  also have "(0 \<le> p \<and> b * q * q \<le> p * p \<or> 0 \<le> q \<and> p * p \<le> b * q * q)
    \<longleftrightarrow> (0 \<le> p' \<and> of_nat b' * q' * q' \<le> p' * p' \<or> 0 \<le> q' \<and> p' * p' \<le> of_nat b' * q' * q')" unfolding qb_def
    by (unfold bdef p_def q_def of_rat_mult[symmetric] of_rat_less_eq, simp)
  finally
  show "ge_0 (real_of_rat p' + real_of_rat q' * sqrt (of_nat b')) =
       (0 \<le> p' \<and> of_nat b' * q' * q' \<le> p' * p' \<or> 0 \<le> q' \<and> p' * p' \<le> of_nat b' * q' * q')"
    unfolding ge_0_def p_def b_def q_def
    by (auto simp: of_rat_add of_rat_mult)
qed

lemma ma_0: "0 = real_of (ma_of_rat 0)" by (transfer, auto)

lemma ma_1: "1 = real_of (ma_of_rat 1)" by (transfer, auto)

lemma ma_uminus:
  "- (real_of x) = real_of (ma_uminus x)"
  by (transfer, auto simp: of_rat_minus)

lemma ma_inverse: "inverse (real_of r) = real_of (ma_inverse r)"
proof (transfer, unfold Let_def, clarsimp)
  fix p' q' :: rat and b' :: nat
  assume b': "q' = 0 \<or> b' \<in> sqrt_irrat"
  define b where "b = real_of_nat b'"
  define p where "p = real_of_rat p'"
  define q where "q = real_of_rat q'"
  from b' have b: "b \<ge> 0" "q = 0 \<or> b' \<in> sqrt_irrat" unfolding b_def q_def by auto
  have "inverse (p + q * sqrt b) = (p - q * sqrt b) * inverse (p * p - b * (q * q))"
  proof (cases "q = 0")
    case True thus ?thesis by (cases "p = 0", auto simp: field_simps)
  next
    case False
    from sqrt_irrat[OF b', of p'] b_def p_def q_def False have nnull: "p + q * sqrt b \<noteq> 0" by auto
    have "?thesis \<longleftrightarrow> (p + q * sqrt b) * inverse (p + q * sqrt b) =
      (p + q * sqrt b) * ((p - q * sqrt b) * inverse (p * p - b * (q * q)))"
      unfolding mult_left_cancel[OF nnull] by auto
    also have "(p + q * sqrt b) * inverse (p + q * sqrt b) = 1" using nnull by auto
    also have "(p + q * sqrt b) * ((p - q * sqrt b) * inverse (p * p - b * (q * q)))
      = (p * p - b * (q * q)) * inverse (p * p - b * (q * q))"
      using b by (auto simp: field_simps)
    also have "... = 1"
    proof (rule right_inverse, rule)
      assume eq: "p * p - b * (q * q) = 0"
      have "real_of_rat (p' * p' / (q' * q')) = p * p / (q * q)"
        unfolding p_def b_def q_def by (auto simp: of_rat_mult of_rat_divide)
      also have "\<dots> = b" using eq False by (auto simp: field_simps)
      also have "\<dots> = real_of_rat (of_nat b')" unfolding b_def by auto
      finally have "(p' / q') * (p' / q') = of_nat b'"
        unfolding of_rat_eq_iff by simp
      with b False show False unfolding sqrt_irrat_def by blast
    qed
    finally
    show ?thesis by simp
  qed
  thus "inverse (real_of_rat p' + real_of_rat q' * sqrt (of_nat b')) =
       real_of_rat (p' * inverse (p' * p' - of_nat b' * q' * q')) +
       real_of_rat (- (q' * inverse (p' * p' - of_nat b' * q' * q'))) * sqrt (of_nat b')"
    by (simp add: divide_simps of_rat_mult of_rat_divide of_rat_diff of_rat_minus b_def p_def q_def
             split: if_splits)
qed

lemma ma_sqrt_main: "ma_rat r \<ge> 0 \<Longrightarrow> ma_coeff r = 0 \<Longrightarrow> sqrt (real_of r) = real_of (ma_sqrt r)"
proof (transfer, unfold Let_def, clarsimp)
  fix p :: rat
  assume p: "0 \<le> p"
  hence abs: "abs p = p" by auto
  obtain a b where ab: "quotient_of p = (a,b)" by force
  hence pab: "p = of_int a / of_int b" by (rule quotient_of_div)
  from ab have b: "b > 0" by (rule quotient_of_denom_pos)
  with p pab have abpos: "a * b \<ge> 0"
    by (metis of_int_0_le_iff of_int_le_0_iff zero_le_divide_iff zero_le_mult_iff)
  have rab: "of_nat (nat (a * b)) = real_of_int a * real_of_int b" using abpos
    by simp
  let ?lhs = "sqrt (of_int a / of_int b)"
  let ?rhs = "(case case quotient_of p of
               (a, b) \<Rightarrow> (case sqrt_int \<bar>a * b\<bar> of [] \<Rightarrow> (0, inverse (of_int b), nat \<bar>a * b\<bar>)
                 | s # x \<Rightarrow> (of_int s / of_int b, 0, 0)) of
          (p, q, b) \<Rightarrow> of_rat p + of_rat q * sqrt (of_nat b))"
  have "sqrt (real_of_rat p) = ?lhs" unfolding pab
    by (metis of_rat_divide of_rat_of_int_eq)
  also have "\<dots> = ?rhs"
  proof (cases "sqrt_int \<bar>a * b\<bar>")
    case Nil
    define sb where "sb = sqrt (of_int b)"
    define sa where "sa = sqrt (of_int a)"
    from b sb_def have sb: "sb > 0" "real_of_int b > 0" by auto
    have sbb: "sb * sb = real_of_int b" unfolding sb_def
      by (rule sqrt_sqrt, insert b, auto)
    from Nil have "?thesis = (sa / sb =
      inverse (of_int b) * (sa * sb))" unfolding ab sa_def sb_def using abpos
      by (simp add: rab of_rat_divide real_sqrt_mult real_sqrt_divide of_rat_inverse)
    also have "\<dots> = (sa = inverse (of_int b) * sa * (sb * sb))" using sb
      by (metis b divide_real_def eq_divide_imp inverse_divide inverse_inverse_eq inverse_mult_distrib less_int_code(1) of_int_eq_0_iff real_sqrt_eq_zero_cancel_iff sb_def sbb times_divide_eq_right)
    also have "\<dots> = True" using sb(2) unfolding sbb by auto
    finally show "?thesis" by simp
  next
    case (Cons s x)
    from b have b: "real_of_int b > 0" by auto
    from Cons sqrt_int[of "abs (a * b)"] have "s * s = abs (a * b)" by auto
    with sqrt_int_pos[OF Cons] have "sqrt (real_of_int (abs (a * b))) = of_int s"
      by (metis abs_of_nonneg of_int_mult of_int_abs real_sqrt_abs2)
    with abpos have "of_int s = sqrt (real_of_int (a * b))" by auto
    thus ?thesis unfolding ab split using Cons b
      by (auto simp: of_rat_divide field_simps real_sqrt_divide real_sqrt_mult)
  qed
  finally show "sqrt (real_of_rat p) = ?rhs" .
qed

lemma ma_sqrt: "sqrt (real_of r) = (if ma_coeff r = 0 then
  (if ma_rat r \<ge> 0 then real_of (ma_sqrt r) else - real_of (ma_sqrt (ma_uminus r)))
  else Code.abort (STR ''cannot represent sqrt of irrational number'') (\<lambda> _. sqrt (real_of r)))"
proof (cases "ma_coeff r = 0")
  case True note 0 = this
  hence 00: "ma_coeff (ma_uminus r) = 0" by (transfer, auto)
  show ?thesis
  proof (cases "ma_rat r \<ge> 0")
    case True
    from ma_sqrt_main[OF this 0] 0 True show ?thesis by auto
  next
    case False
    hence "ma_rat (ma_uminus r) \<ge> 0" by (transfer, auto)
    from ma_sqrt_main[OF this 00, folded ma_uminus, symmetric] False 0
    show ?thesis by (auto simp: real_sqrt_minus)
  qed
qed auto

lemma ma_plus:
  "(real_of r1 + real_of r2) = (if ma_compatible r1 r2
    then real_of (ma_plus r1 r2) else
    Code.abort (STR ''different base'') (\<lambda> _. real_of r1 + real_of r2))"
  by transfer (auto split: prod.split simp: field_simps of_rat_add)

lemma ma_times:
  "(real_of r1 * real_of r2) = (if ma_compatible r1 r2
    then real_of (ma_times r1 r2) else
    Code.abort (STR ''different base'') (\<lambda> _. real_of r1 * real_of r2))"
  by transfer (auto split: prod.split simp: field_simps of_rat_mult of_rat_add)

lemma ma_equal:
  "HOL.equal (real_of r1) (real_of r2) = (if ma_compatible r1 r2
    then ma_equal r1 r2 else
    Code.abort (STR ''different base'') (\<lambda> _. HOL.equal (real_of r1) (real_of r2)))"
proof (transfer, unfold equal_real_def, clarsimp)
  fix p1 q1 p2 q2 :: rat and b1 b2 :: nat
  assume b1: "q1 = 0 \<or> b1 \<in> sqrt_irrat"
  assume b2: "q2 = 0 \<or> b2 \<in> sqrt_irrat"
  assume base: "q1 = 0 \<or> q2 = 0 \<or> b1 = b2"
  let ?l = "real_of_rat p1 + real_of_rat q1 * sqrt (of_nat b1) =
      real_of_rat p2 + real_of_rat q2 * sqrt (of_nat b2)"
  let ?m = "real_of_rat q1 * sqrt (of_nat b1) = real_of_rat (p2 - p1) + real_of_rat q2 * sqrt (of_nat b2)"
  let ?r = "p1 = p2 \<and> q1 = q2 \<and> (q1 = 0 \<or> b1 = b2)"
  have "?l \<longleftrightarrow> real_of_rat q1 * sqrt (of_nat b1) = real_of_rat (p2 - p1) + real_of_rat q2 * sqrt (of_nat b2)"
    by (auto simp: of_rat_add of_rat_diff of_rat_minus)
  also have "\<dots> \<longleftrightarrow> p1 = p2 \<and> q1 = q2 \<and> (q1 = 0 \<or> b1 = b2)"
  proof
    assume ?m
    from base have "q1 = 0 \<or> q1 \<noteq> 0 \<and> q2 = 0 \<or> q1 \<noteq> 0 \<and> q2 \<noteq> 0 \<and> b1 = b2" by auto
    thus "p1 = p2 \<and> q1 = q2 \<and> (q1 = 0 \<or> b1 = b2)"
    proof
      assume q1: "q1 = 0"
      with \<open>?m\<close> have "real_of_rat (p2 - p1) + real_of_rat q2 * sqrt (of_nat b2) = 0" by auto
      with sqrt_irrat b2 have q2: "q2 = 0" by auto
      with q1 \<open>?m\<close> show ?thesis by auto
    next
      assume "q1 \<noteq> 0 \<and> q2 = 0 \<or> q1 \<noteq> 0 \<and> q2 \<noteq> 0 \<and> b1 = b2"
      thus ?thesis
      proof
        assume ass: "q1 \<noteq> 0 \<and> q2 = 0"
        with \<open>?m\<close> have "real_of_rat (p1 - p2) + real_of_rat q1 * sqrt (of_nat b1) = 0"
          by (auto simp: of_rat_diff)
        with b1 have "q1 = 0" using sqrt_irrat by auto
        with ass show ?thesis by auto
      next
        assume ass: "q1 \<noteq> 0 \<and> q2 \<noteq> 0 \<and> b1 = b2"
        with \<open>?m\<close> have *: "real_of_rat (p2 - p1) + real_of_rat (q2 - q1) * sqrt (of_nat b2) = 0"
          by (auto simp: field_simps of_rat_diff)
        have "q2 - q1 = 0"
          by (rule sqrt_irrat[OF _ *], insert ass b2, auto)
        with * ass show ?thesis by auto
      qed
    qed
  qed auto
  finally show "?l = ?r" by simp
qed

lemma ma_floor: "floor (real_of r) = ma_floor r"
proof (transfer, unfold Let_def, clarsimp)
  fix p q :: rat and b :: nat
  obtain z1 n1 where qp: "quotient_of p = (z1,n1)" by force
  obtain z2 n2 where qq: "quotient_of q = (z2,n2)" by force
  from quotient_of_denom_pos[OF qp] have n1: "0 < n1" .
  from quotient_of_denom_pos[OF qq] have n2: "0 < n2" .
  from quotient_of_div[OF qp] have p: "p = of_int z1 / of_int n1" .
  from quotient_of_div[OF qq] have q: "q = of_int z2 / of_int n2" .
  have p: "p = of_int (z1 * n2) / of_int (n1 * n2)" unfolding p using n2 by auto
  have q: "q = of_int (z2 * n1) / of_int (n1 * n2)" unfolding q using n1 by auto
  define z1n2 where "z1n2 = z1 * n2"
  define z2n1 where "z2n1 = z2 * n1"
  define n12 where "n12 = n1 * n2"
  define r_add where "r_add = of_int (z2n1) * sqrt (real_of_int (int b))"
  from n1 n2 have n120: "n12 > 0" unfolding n12_def by simp
  have "floor (of_rat p + of_rat q * sqrt (real_of_nat b)) = floor ((of_int z1n2 + r_add) / of_int n12)"
    unfolding r_add_def n12_def z1n2_def z2n1_def
    unfolding p q add_divide_distrib of_rat_divide of_rat_of_int_eq of_int_of_nat_eq by simp
  also have "\<dots> = floor (of_int z1n2 + r_add) div n12"
    by (rule floor_div_pos_int[OF n120])
  also have "of_int z1n2 + r_add = r_add + of_int z1n2" by simp
  also have "floor (\<dots>) = floor r_add + z1n2" by simp
  also have "\<dots> = z1n2 + floor r_add" by simp
  finally have id: "\<lfloor>of_rat p + of_rat q * sqrt (of_nat b)\<rfloor> = (z1n2 + \<lfloor>r_add\<rfloor>) div n12" .
  show "\<lfloor>of_rat p + of_rat q * sqrt (of_nat b)\<rfloor> =
              (case quotient_of p of
               (z1, n1) \<Rightarrow>
                 case quotient_of q of
                 (z2, n2) \<Rightarrow>
                 (z1 * n2 + (if 0 \<le> z2 * n1 then sqrt_int_floor_pos (z2 * n1 * (z2 * n1) * int b) else
                    - sqrt_int_ceiling_pos (z2 * n1 * (z2 * n1) * int b))) div (n1 * n2))"
    unfolding qp qq split id n12_def z1n2_def
  proof (rule arg_cong[of _ _ "\<lambda> x. ((z1 * n2) + x) div (n1 * n2)"])
    have ge_int: "z2 * n1 * (z2 * n1) * int b \<ge> 0"
      by (metis mult_nonneg_nonneg zero_le_square of_nat_0_le_iff)
    show "\<lfloor>r_add\<rfloor> = (if 0 \<le> z2 * n1 then sqrt_int_floor_pos (z2 * n1 * (z2 * n1) * int b) else - sqrt_int_ceiling_pos (z2 * n1 * (z2 * n1) * int b))"
    proof (cases "z2 * n1 \<ge> 0")
      case True
      hence ge: "real_of_int (z2 * n1) \<ge> 0" by (metis of_int_0_le_iff)
      have radd: "r_add = sqrt (of_int (z2 * n1 * (z2 * n1) * int b))"
        unfolding r_add_def z2n1_def using sqrt_sqrt[OF ge]
        by (simp add: ac_simps real_sqrt_mult)
      show ?thesis unfolding radd sqrt_int_floor_pos[OF ge_int] using True by simp
    next
      case False
      hence ge: "real_of_int (- (z2 * n1)) \<ge> 0"
        by (metis mult_zero_left neg_0_le_iff_le of_int_0_le_iff order_refl zero_le_mult_iff)
      have "r_add = - sqrt (of_int (z2 * n1 * (z2 * n1) * int b))"
        unfolding r_add_def z2n1_def using sqrt_sqrt[OF ge]
        by (metis minus_minus minus_mult_commute minus_mult_right of_int_minus of_int_mult real_sqrt_minus real_sqrt_mult z2n1_def)
      hence radd: "floor r_add = - ceiling (sqrt (of_int (z2 * n1 * (z2 * n1) * int b)))"
        by (metis ceiling_def minus_minus)
      show ?thesis unfolding radd sqrt_int_ceiling_pos[OF ge_int] using False by simp
    qed
  qed
qed

lemma comparison_impl:
  "(x :: real) \<le> (y :: real) = ge_0 (y - x)"
  "(x :: real) < (y :: real) = (x \<noteq> y \<and> ge_0 (y - x))"
  by (simp_all add: ge_0_def, linarith+)

lemma ma_of_rat: "real_of_rat r = real_of (ma_of_rat r)"
  by (transfer, auto)

definition is_rat :: "real \<Rightarrow> bool" where
  [code_abbrev]: "is_rat x \<longleftrightarrow> x \<in> \<rat>"

lemma ma_is_rat: "is_rat (real_of x) = ma_is_rat x"
proof (transfer, unfold is_rat_def, clarsimp)
  fix p q :: rat and b :: nat
  let ?p = "real_of_rat p"
  let ?q = "real_of_rat q"
  let ?b = "real_of_nat b"
  let ?b' = "real_of_rat (of_nat b)"
  assume b: "q = 0 \<or> b \<in> sqrt_irrat"
  show "(?p + ?q * sqrt ?b \<in> \<rat>) = (q = 0)"
  proof (cases "q = 0")
    case False
    from False b have b: "b \<in> sqrt_irrat" by auto
    {
      assume "?p + ?q * sqrt ?b \<in> \<rat>"
      from this[unfolded Rats_def] obtain r where r: "?p + ?q * sqrt ?b = real_of_rat r" by auto
      let ?r = "real_of_rat r"
      from r have "real_of_rat (p - r) + ?q * sqrt ?b = 0" by (simp add: of_rat_diff)
      from sqrt_irrat[OF disjI2[OF b] this] False have False by auto
    }
    thus ?thesis by auto
  qed auto
qed

(* compute all numbers y for which y * y = x, if x \<in> \<rat>, otherwise return empty list.
   of course, one could have returned [-sqrt x, sqrt x], but this might result in runtime errors,
   e.g., if sqrt_real (sqrt 2) would be invoked. The current formulation is guaranteed to not crash. *)
definition "sqrt_real x = (if x \<in> \<rat> \<and> x \<ge> 0 then (if x = 0 then [0] else (let sx = sqrt x in [sx,-sx])) else [])"

lemma sqrt_real[simp]: assumes x: "x \<in> \<rat>"
  shows "set (sqrt_real x) = {y . y * y = x}"
proof (cases "x \<ge> 0")
  case False
  hence "\<And> y. y * y \<noteq> x" by auto
  with False show ?thesis unfolding sqrt_real_def by auto
next
  case True
  thus ?thesis using x
    by (cases "x = 0", auto simp: Let_def sqrt_real_def)
qed

code_datatype real_of

declare [[code drop:
  "plus :: real \<Rightarrow> real \<Rightarrow> real"
  "uminus :: real \<Rightarrow> real"
  "times :: real \<Rightarrow> real \<Rightarrow> real"
  "inverse :: real \<Rightarrow> real"
  "floor :: real \<Rightarrow> int"
  sqrt
  "HOL.equal :: real \<Rightarrow> real \<Rightarrow> bool"
]]

lemma [code]:
  "Ratreal = real_of \<circ> ma_of_rat"
  by (simp add: fun_eq_iff) (transfer, simp)

lemmas ma_code_eqns [code equation] = ma_ge_0 ma_floor ma_0 ma_1 ma_uminus ma_inverse ma_sqrt ma_plus ma_times ma_equal ma_is_rat
  comparison_impl

lemma [code equation]:
  "(x :: real) / (y :: real) = x * inverse y"
  "(x :: real) - (y :: real) = x + (- y)"
  by (simp_all add: divide_inverse)

text \<open>Some tests with small numbers. To work on larger number, one should
  additionally import the theories for efficient calculation on numbers\<close>

value "\<lfloor>101.1 * (3 * sqrt 2 + 6 * sqrt 0.5)\<rfloor>"
value "\<lfloor>606.2 * sqrt 2 + 0.001\<rfloor>"
value "101.1 * (3 * sqrt 2 + 6 * sqrt 0.5) = 606.2 * sqrt 2 + 0.001"
value "101.1 * (3 * sqrt 2 + 6 * sqrt 0.5) > 606.2 * sqrt 2 + 0.001"
value "(sqrt 0.1 \<in> \<rat>, sqrt (- 0.09) \<in> \<rat>)"

end
