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
section \<open>A unique representation of real numbers via triples\<close>
theory Real_Unique_Impl
imports
  Prime_Product
  Real_Impl
  Show.Show_Instances
  Show.Show_Real
begin

text \<open>We implement the real numbers again using triples, but now we require an additional
 invariant on the triples, namely that the base has to be a prime product. This has the consequence
 that the mapping of triples into $\reals$ is injective. Hence, equality on reals is now equality
 on triples, which can even be executed in case of different bases. Similarly, we now also allow
 different basis in comparisons. Ultimately, injectivity allows us to define a show-function for
 real numbers, which pretty prints real numbers into strings.\<close>

typedef mini_alg_unique =
  "{ r :: mini_alg . ma_coeff r = 0 \<and> ma_base r = 0 \<or> ma_coeff r \<noteq> 0 \<and> prime_product (ma_base r)}"
  by (transfer, auto)

setup_lifting type_definition_mini_alg_unique

lift_definition real_of_u :: "mini_alg_unique \<Rightarrow> real" is real_of .
lift_definition mau_floor :: "mini_alg_unique \<Rightarrow> int" is ma_floor .
lift_definition mau_of_rat :: "rat \<Rightarrow> mini_alg_unique" is ma_of_rat by (transfer, auto)
lift_definition mau_rat :: "mini_alg_unique \<Rightarrow> rat" is ma_rat .
lift_definition mau_base :: "mini_alg_unique \<Rightarrow> nat" is ma_base .
lift_definition mau_coeff :: "mini_alg_unique \<Rightarrow> rat" is ma_coeff .
lift_definition mau_uminus :: "mini_alg_unique \<Rightarrow> mini_alg_unique" is ma_uminus by (transfer, auto)
lift_definition mau_compatible :: "mini_alg_unique \<Rightarrow> mini_alg_unique \<Rightarrow> bool" is ma_compatible .
lift_definition mau_ge_0 :: "mini_alg_unique \<Rightarrow> bool" is ma_ge_0 .
lift_definition mau_inverse :: "mini_alg_unique \<Rightarrow> mini_alg_unique" is ma_inverse
  by (transfer, auto simp: ma_normalize_def Let_def split: if_splits)
lift_definition mau_plus :: "mini_alg_unique \<Rightarrow> mini_alg_unique \<Rightarrow> mini_alg_unique" is ma_plus
  by (transfer, auto simp: ma_normalize_def split: if_splits)
lift_definition mau_times :: "mini_alg_unique \<Rightarrow> mini_alg_unique \<Rightarrow> mini_alg_unique" is ma_times
  by (transfer, auto simp: ma_normalize_def split: if_splits)
lift_definition ma_identity :: "mini_alg \<Rightarrow> mini_alg \<Rightarrow> bool" is "(=)" .
lift_definition mau_equal :: "mini_alg_unique \<Rightarrow> mini_alg_unique \<Rightarrow> bool" is ma_identity .
lift_definition mau_is_rat :: "mini_alg_unique \<Rightarrow> bool" is ma_is_rat .

lemma Ratreal_code[code]:
  "Ratreal = real_of_u \<circ> mau_of_rat"
  by (simp add: fun_eq_iff) (transfer, transfer, simp)

lemma mau_floor: "floor (real_of_u r) = mau_floor r"
  using ma_floor by (transfer, auto)
lemma mau_inverse: "inverse (real_of_u r) = real_of_u (mau_inverse r)"
  using ma_inverse by (transfer, auto)
lemma mau_uminus: "- (real_of_u r) = real_of_u (mau_uminus r)"
  using ma_uminus by (transfer, auto)
lemma mau_times:
  "(real_of_u r1 * real_of_u r2) = (if mau_compatible r1 r2
    then real_of_u (mau_times r1 r2) else
    Code.abort (STR ''different base'') (\<lambda> _. real_of_u r1 * real_of_u r2))"
  using ma_times by (transfer, auto)
lemma mau_plus:
  "(real_of_u r1 + real_of_u r2) = (if mau_compatible r1 r2
    then real_of_u (mau_plus r1 r2) else
    Code.abort (STR ''different base'') (\<lambda> _. real_of_u r1 + real_of_u r2))"
  using ma_plus by (transfer, auto)

lemma real_of_u_inj[simp]: "real_of_u x = real_of_u y \<longleftrightarrow> x = y"
proof
  note field_simps[simp] of_rat_diff[simp]
  assume "real_of_u x = real_of_u y"
  thus "x = y"
  proof (transfer)
    fix x y
    assume "ma_coeff x = 0 \<and> ma_base x = 0 \<or> ma_coeff x \<noteq> 0 \<and> prime_product (ma_base x)"
      and  "ma_coeff y = 0 \<and> ma_base y = 0 \<or> ma_coeff y \<noteq> 0 \<and> prime_product (ma_base y)"
      and  "real_of x = real_of y"
    thus "x = y"
    proof (transfer, clarsimp)
      fix p1 q1 p2 q2 :: rat and b1 b2
      let ?p1 = "real_of_rat p1"
      let ?p2 = "real_of_rat p2"
      let ?q1 = "real_of_rat q1"
      let ?q2 = "real_of_rat q2"
      let ?b1 = "real_of_nat b1"
      let ?b2 = "real_of_nat b2"
      assume q1: "q1 = 0 \<and> b1 = 0 \<or> q1 \<noteq> 0 \<and> prime_product b1"
      and q2: "q2 = 0 \<and> b2 = 0 \<or> q2 \<noteq> 0 \<and> prime_product b2"
      and i1: "q1 = 0 \<or> b1 \<in> sqrt_irrat"
      and i2: "q2 = 0 \<or> b2 \<in> sqrt_irrat"
      and eq: "?p1 + ?q1 * sqrt ?b1 = ?p2 + ?q2 * sqrt ?b2"
      show "p1 = p2 \<and> q1 = q2 \<and> b1 = b2"
      proof (cases "q1 = 0")
        case True
        have "q2 = 0"
          by (rule sqrt_irrat[OF i2, of "p2 - p1"], insert eq True q1, auto)
        with True q1 q2 eq show ?thesis by auto
      next
        case False
        hence 1: "q1 \<noteq> 0" "prime_product b1" using q1 by auto
        {
          assume *: "q2 = 0"
          have "q1 = 0"
            by (rule sqrt_irrat[OF i1, of "p1 - p2"], insert eq * q2, auto)
          with False have False by auto
        }
        hence 2: "q2 \<noteq> 0" "prime_product b2" using q2 by auto
        from 1 i1 have b1: "b1 \<noteq> 0" unfolding sqrt_irrat_def by (cases b1, auto)
        from 2 i2 have b2: "b2 \<noteq> 0" unfolding sqrt_irrat_def by (cases b2, auto)
        let ?sq = "\<lambda> x. x * x"
        define q3 where "q3 = p2 - p1"
        let ?q3 = "real_of_rat q3"
        let ?e = "of_rat (q2 * q2 * of_nat b2 + ?sq q3  - ?sq q1 * of_nat b1) + of_rat (2 * q2 * q3) * sqrt ?b2"
        from eq have *: "?q1 * sqrt ?b1 = ?q2 * sqrt ?b2 + ?q3"
          by (simp add: q3_def)
        from arg_cong[OF this, of ?sq] have "0 = (real_of_rat 2 * ?q2 * ?q3) * sqrt ?b2 +
          (?sq ?q2 * ?b2 +  ?sq ?q3 - ?sq ?q1 * ?b1)"
          by auto
        also have "\<dots> = ?e"
          by (simp add: of_rat_mult of_rat_add of_rat_minus)
        finally have eq: "?e = 0" by simp
        from sqrt_irrat[OF _ this] 2 i2 have q3: "q3 = 0" by auto
        hence p: "p1 = p2" unfolding q3_def by simp
        let ?b1 = "rat_of_nat b1"
        let ?b2 = "rat_of_nat b2"
        from eq[unfolded q3] have eq: "?sq q2 * ?b2 = ?sq q1 * ?b1" by auto
        obtain z1 n1 where d1: "quotient_of q1 = (z1,n1)" by force
        obtain z2 n2 where d2: "quotient_of q2 = (z2,n2)" by force
        note id = quotient_of_div[OF d1] quotient_of_div[OF d2]
        note pos = quotient_of_denom_pos[OF d1] quotient_of_denom_pos[OF d2]
        from id(1) 1(1) pos(1) have z1: "z1 \<noteq> 0" by auto
        from id(2) 2(1) pos(2) have z2: "z2 \<noteq> 0" by auto
        let ?n1 = "rat_of_int n1"
        let ?n2 = "rat_of_int n2"
        let ?z1 = "rat_of_int z1"
        let ?z2 = "rat_of_int z2"
        from arg_cong[OF eq[simplified id], of "\<lambda> x. x * ?sq ?n1 * ?sq ?n2",
          simplified field_simps]
        have "?sq (?n1 * ?z2) * ?b2 = ?sq (?n2 * ?z1) * ?b1"
          using pos by auto
        moreover have "?n1 * ?z2 \<noteq> 0" "?n2 * ?z1 \<noteq> 0" using z1 z2 pos by auto
        ultimately obtain i1 i2 where 0: "rat_of_int i1 \<noteq> 0" "rat_of_int i2 \<noteq> 0"
          and eq: "?sq (rat_of_int i2) * ?b2 = ?sq (rat_of_int i1) * ?b1"
          unfolding of_int_mult[symmetric] by blast+
        let ?b1 = "int b1"
        let ?b2 = "int b2"
        from eq have eq: "?sq i1 * ?b1 = ?sq i2 * ?b2"
          by (metis (hide_lams, no_types) of_int_eq_iff of_int_mult of_int_of_nat_eq)
        from 0 have 0: "i1 \<noteq> 0" "i2 \<noteq> 0" by auto
        from arg_cong[OF eq, of nat] have "?sq (nat (abs i1)) * b1 = ?sq (nat (abs i2)) * b2"
          by (metis abs_of_nat eq nat_abs_mult_distrib nat_int)
        moreover have "nat (abs i1) > 0" "nat (abs i2) > 0" using 0 by auto
        ultimately obtain n1 n2 where 0: "n1 > 0" "n2 > 0" and eq: "?sq n1 * b1 = ?sq n2 * b2" by blast
        from b1 0 have b1: "b1 > 0" "n1 > 0" "n1 * n1 > 0" by auto
        from b2 0 have b2: "b2 > 0" "n2 > 0" "n2 * n2 > 0" by auto
        {
          fix p :: nat assume p: "prime p"
          have "multiplicity p (?sq n1 * b1) = multiplicity p b1 + 2 * multiplicity p n1"
            using b1 p by (auto simp: prime_elem_multiplicity_mult_distrib)
          also have "\<dots> mod 2 = multiplicity p b1 mod 2" by presburger
          finally have id1: "multiplicity p (?sq n1 * b1) mod 2 = multiplicity p b1 mod 2" .
          have "multiplicity p (?sq n2 * b2) = multiplicity p b2 + 2 * multiplicity p n2"
            using b2 p by (auto simp: prime_elem_multiplicity_mult_distrib)
          also have "\<dots> mod 2 = multiplicity p b2 mod 2" by presburger
          finally have id2: "multiplicity p (?sq n2 * b2) mod 2 = multiplicity p b2 mod 2" .
          from id1 id2 eq have eq: "multiplicity p b1 mod 2 = multiplicity p b2 mod 2" by simp
          from 1(2) 2(2) p have "multiplicity p b1 \<le> 1" "multiplicity p b2 \<le> 1"
            unfolding prime_product_def by auto
          with eq have "multiplicity p b1 = multiplicity p b2" by simp
        }
        with b1(1) b2(1) have b: "b1 = b2" by (rule multiplicity_eq_nat)
        from *[unfolded b q3] b1(1) b2(1) have q: "q1 = q2" by simp
        from p q b show ?thesis by blast
      qed
    qed
  qed
qed simp

lift_definition mau_sqrt :: "mini_alg_unique \<Rightarrow> mini_alg_unique" is
   "\<lambda> ma. let (a,b) = quotient_of (ma_rat ma); (sq,fact) = prime_product_factor (nat (abs a * b));
      ma' = ma_of_rat (of_int (sgn(a)) * of_nat sq / of_int b)
      in ma_times ma' (ma_sqrt (ma_of_rat (of_nat fact)))"
proof -
  fix ma :: mini_alg
  let ?num =
    "let (a, b) = quotient_of (ma_rat ma); (sq, fact) = prime_product_factor (nat (\<bar>a\<bar> * b));
       ma' = ma_of_rat (rat_of_int (sgn a) * rat_of_nat sq / of_int b)
     in ma_times ma' (ma_sqrt (ma_of_rat (rat_of_nat fact)))"
  obtain a b where q: "quotient_of (ma_rat ma) = (a,b)" by force
  obtain sq fact where ppf: "prime_product_factor (nat (abs a * b)) = (sq,fact)" by force
  define asq where "asq = rat_of_int (sgn a) * of_nat sq / of_int b"
  define ma' where "ma' = ma_of_rat asq"
  define sqrt where "sqrt = ma_sqrt (ma_of_rat (rat_of_nat fact))"
  have num: "?num = ma_times ma' sqrt" unfolding q ppf asq_def Let_def split ma'_def sqrt_def ..
  let ?inv = "\<lambda> ma. ma_coeff ma = 0 \<and> ma_base ma = 0 \<or> ma_coeff ma \<noteq> 0 \<and> prime_product (ma_base ma)"
  have ma': "?inv ma'" unfolding ma'_def
    by (transfer, auto)
  have id: "\<And> i. int i * 1 = i" "\<And> i :: rat. i / 1 = i" "rat_of_int 1 = 1" "inverse (1 :: rat) = 1"
    "\<And> n. nat \<bar>int n\<bar> = n" by auto
  from prime_product_factor[OF ppf] have "prime_product fact" by auto
  hence sqrt: "?inv sqrt" unfolding sqrt_def
    by (transfer, unfold split quotient_of_nat Let_def id, case_tac "sqrt_int \<bar>int facta\<bar>", auto)
  show "?inv ?num" unfolding num using ma' sqrt
    by (transfer, auto simp: ma_normalize_def split: if_splits)  (* slow *)
qed

lemma sqrt_sgn[simp]: "sqrt (of_int (sgn a)) = of_int (sgn a)"
  by (cases "a \<ge> 0", cases "a = 0", auto simp: real_sqrt_minus)

lemma mau_sqrt_main: "mau_coeff r = 0 \<Longrightarrow> sqrt (real_of_u r) = real_of_u (mau_sqrt r)"
proof (transfer)
  fix r
  assume "ma_coeff r = 0"
  hence rr: "real_of r = of_rat (ma_rat r)" by (transfer, auto)
  obtain a b where q: "quotient_of (ma_rat r) = (a,b)" by force
  from quotient_of_div[OF q] have r: "ma_rat r = of_int a / of_int b" by auto
  from quotient_of_denom_pos[OF q] have b: "b > 0" by auto
  obtain sq fact where ppf: "prime_product_factor (nat (\<bar>a\<bar> * b)) = (sq, fact)" by force
  from prime_product_factor[OF ppf] have ab: "nat (\<bar>a\<bar> * b) = sq * sq * fact" ..
  have "sqrt (real_of r) = sqrt(of_int a / of_int b)" unfolding rr r
    by (metis of_rat_divide of_rat_of_int_eq)
  also have "real_of_int a / of_int b = of_int a * of_int b / (of_int b * of_int b)" using b by auto
  also have "sqrt (\<dots>) = sqrt (of_int a * of_int b) / of_int b" using sqrt_sqrt[of "real_of_int b"] b
    by (metis less_eq_real_def of_int_0_less_iff real_sqrt_divide real_sqrt_mult)
  also have "real_of_int a * of_int b = real_of_int (a * b)" by auto
  also have "a * b = sgn a * (abs a * b)" by (simp, metis mult_sgn_abs)
  also have "real_of_int (\<dots>) = of_int (sgn a) * real_of_int (\<bar>a\<bar> * b)"
    unfolding of_int_mult[of "sgn a"] ..
  also have "real_of_int (\<bar>a\<bar> * b) = of_nat (nat (abs a * b))" using b
    by (metis abs_sgn mult_pos_pos mult_zero_left nat_int of_int_of_nat_eq of_nat_0 zero_less_abs_iff zero_less_imp_eq_int)
  also have "\<dots> = of_nat fact * (of_nat sq * of_nat sq)" unfolding ab of_nat_mult by simp
  also have "sqrt (of_int (sgn a) * (of_nat fact * (of_nat sq * of_nat sq))) =
    of_int (sgn a) * sqrt (of_nat fact) * of_nat sq"
    unfolding real_sqrt_mult by simp
  finally have r: "sqrt (real_of r) = real_of_int (sgn a) * real_of_nat sq / real_of_int b * sqrt (real_of_nat fact)" by simp
  let ?asqb = "ma_of_rat (rat_of_int (sgn a) * rat_of_nat sq / rat_of_int b)"
  let ?f = "ma_of_rat (rat_of_nat fact)"
  let ?sq = "ma_sqrt ?f"
  have sq: "0 \<le> ma_rat ?f" "ma_coeff ?f = 0" by ((transfer, simp)+)
  have compat: "\<And> m. (ma_compatible ?asqb m) = True"
    by (transfer, auto)
  show "sqrt (real_of r) =
         real_of
          (let (a, b) = quotient_of (ma_rat r); (sq, fact) = prime_product_factor (nat (\<bar>a\<bar> * b));
               ma' = ma_of_rat (rat_of_int (sgn a) * rat_of_nat sq / rat_of_int b)
           in ma_times ma' (ma_sqrt (ma_of_rat (rat_of_nat fact))))"
    unfolding q ppf Let_def split
    unfolding r
    unfolding ma_times[symmetric, of ?asqb, unfolded compat if_True]
    unfolding ma_sqrt_main[OF sq, symmetric]
    unfolding ma_of_rat[symmetric]
    by (simp add: of_rat_divide of_rat_mult)
qed

lemma mau_sqrt: "sqrt (real_of_u r) = (if mau_coeff r = 0 then
  real_of_u (mau_sqrt r)
  else Code.abort (STR ''cannot represent sqrt of irrational number'') (\<lambda> _. sqrt (real_of_u r)))"
  using mau_sqrt_main[of r] by (cases "mau_coeff r = 0", auto)

lemma mau_0: "0 = real_of_u (mau_of_rat 0)" using ma_0 by (transfer, auto)

lemma mau_1: "1 = real_of_u (mau_of_rat 1)" using ma_1 by (transfer, auto)

lemma mau_equal:
  "HOL.equal (real_of_u r1) (real_of_u r2) = mau_equal r1 r2" unfolding equal_real_def
  using real_of_u_inj[of r1 r2]
  by (transfer, transfer, auto)

lemma mau_ge_0: "ge_0 (real_of_u x) = mau_ge_0 x" using ma_ge_0
  by (transfer, auto)

definition real_lt :: "real \<Rightarrow> real \<Rightarrow> bool" where "real_lt = (<)"

text\<open>The following code equation terminates if it is started on two
  different inputs.\<close>
lemma real_lt [code equation]: "real_lt x y = (let fx = floor x; fy = floor y in
  (if fx < fy then True else if fx > fy then False else real_lt (x * 1024) (y * 1024)))"
proof (cases "floor x < floor y")
  case True
  thus ?thesis by (auto simp: real_lt_def floor_less_cancel)
next
  case False note nless = this
  show ?thesis
  proof (cases "floor x > floor y")
    case True
    from floor_less_cancel[OF this] True nless show ?thesis
      by (simp add: real_lt_def)
  next
    case False
    with nless show ?thesis unfolding real_lt_def by auto
  qed
qed

text \<open>For comparisons we first check for equality. Then, if the bases are
  compatible we can just compare the differences with 0. Otherwise, we start
  the recursive algorithm @{const real_lt} which works on arbitrary bases.
  In this way, we have an implementation of comparisons which can compare
  all representable numbers.

  Note that in @{theory Real_Impl.Real_Impl} we did not use @{const real_lt} as there
  the code-equations for equality already require identical bases.
\<close>
lemma comparison_impl:
  "real_of_u x \<le> real_of_u y \<longleftrightarrow> real_of_u x = real_of_u y \<or>
    (if mau_compatible x y then ge_0 (real_of_u y - real_of_u x) else real_lt (real_of_u x) (real_of_u y))"
  "real_of_u x < real_of_u y \<longleftrightarrow> real_of_u x \<noteq> real_of_u y \<and>
    (if mau_compatible x y then ge_0 (real_of_u y - real_of_u x) else real_lt (real_of_u x) (real_of_u y))"
  unfolding ge_0_def real_lt_def by (auto simp del: real_of_u_inj)

lemma mau_is_rat: "is_rat (real_of_u x) = mau_is_rat x" using ma_is_rat
  by (transfer, auto)

lift_definition ma_show_real :: "mini_alg \<Rightarrow> string" is
  "\<lambda> (p,q,b). let sb = shows ''sqrt('' \<circ> shows b \<circ> shows '')'';
      qb = (if q = 1 then sb else if q = -1 then shows ''-'' \<circ> sb else shows q \<circ> shows ''*'' \<circ> sb) in
      if q = 0 then shows p [] else
      if p = 0 then qb [] else
      if q < 0 then ((shows p \<circ> qb) [])
      else ((shows p \<circ> shows ''+'' \<circ> qb) [])" .

lift_definition mau_show_real :: "mini_alg_unique \<Rightarrow> string" is ma_show_real .

overloading show_real \<equiv> show_real
begin
  definition show_real
    where "show_real x \<equiv>
      (if (\<exists> y. x = real_of_u y) then mau_show_real (THE y. x = real_of_u y) else [])"
end

lemma mau_show_real: "show_real (real_of_u x) = mau_show_real x"
  unfolding show_real_def by simp

code_datatype real_of_u

declare [[code drop:
  "plus :: real \<Rightarrow> real \<Rightarrow> real"
  "uminus :: real \<Rightarrow> real"
  "times :: real \<Rightarrow> real \<Rightarrow> real"
  "inverse :: real \<Rightarrow> real"
  "floor :: real \<Rightarrow> int"
  sqrt
  "HOL.equal :: real \<Rightarrow> real \<Rightarrow> bool"
  ge_0
  is_rat
  "less :: real \<Rightarrow> real \<Rightarrow> bool" 
  "less_eq :: real \<Rightarrow> real \<Rightarrow> bool" 
]]

lemmas mau_code_eqns [code] = mau_floor mau_0 mau_1 mau_uminus mau_inverse mau_sqrt mau_plus mau_times mau_equal mau_ge_0 mau_is_rat
  mau_show_real comparison_impl

text \<open>Some tests with small numbers. To work on larger number, one should
  additionally import the theories for efficient calculation on numbers\<close>

value "\<lfloor>101.1 * (sqrt 18 + 6 * sqrt 0.5)\<rfloor>"
value "\<lfloor>324 * sqrt 7 + 0.001\<rfloor>"
value "101.1 * (sqrt 18 + 6 * sqrt 0.5) = 324 * sqrt 7 + 0.001"
value "101.1 * (sqrt 18 + 6 * sqrt 0.5) > 324 * sqrt 7 + 0.001"
value "show (101.1 * (sqrt 18 + 6 * sqrt 0.5))"
value "(sqrt 0.1 \<in> \<rat>, sqrt (- 0.09) \<in> \<rat>)"

end
