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
section \<open>Prime products\<close>

theory Prime_Product
imports 
  Real_Impl_Auxiliary
  Sqrt_Babylonian.Sqrt_Babylonian
begin

text \<open>
  Prime products are natural numbers where no prime factor occurs more than once.
\<close>
definition prime_product 
  where "prime_product (n :: nat) = (\<forall> p. prime p \<longrightarrow> multiplicity p n \<le> 1)"

text \<open>
  The main property is that whenever $b_1$ and $b_2$ are different prime products,
  then $p_1 + q_1 \sqrt{b_1} = p_2 + q_2 \sqrt{b_2}$ implies $(p_1,q_1,b_1) = (p_2,q_2,b_2)$
  for all rational numbers $p_1,q_1,p_2,q_2$. This is the key property to uniquely
  represent numbers in $\ratsb$ by triples. In the following we develop an algorithm
  to decompose any natural number $n$ into $n = s^2 \cdot p$ for some $s$ and prime product $p$.
\<close>


(* factor a number into square * a prime product *)
function prime_product_factor_main :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  "prime_product_factor_main factor_sq factor_pr limit n i = 
    (if i \<le> limit \<and> i \<ge> 2 then
       (if i dvd n 
           then (let n' = n div i in 
             (if i dvd n' then
                let n'' = n' div i in 
                  prime_product_factor_main (factor_sq * i) factor_pr (nat (root_nat_floor 3 n'')) n'' i
                else
                  (case sqrt_nat n' of 
                    Cons sn _ \<Rightarrow> (factor_sq * sn, factor_pr * i)
                  | [] \<Rightarrow> prime_product_factor_main factor_sq (factor_pr * i) (nat (root_nat_floor 3 n')) n' (Suc i)
                  )
             )              
           )
         else 
           prime_product_factor_main factor_sq factor_pr limit n (Suc i))
       else
         (factor_sq, factor_pr * n))" by pat_completeness auto

termination
proof -
  let ?m1 = "\<lambda> (factor_sq :: nat,factor_pr :: nat,limit :: nat,n :: nat,i :: nat). n"
  let ?m2 = "\<lambda> (factor_sq,factor_pr,limit,n,i). (Suc limit - i)"
  {
    fix i
    have "2 \<le> i \<Longrightarrow> Suc 0 < i * i" using one_less_mult[of i i] by auto
  } note * = this
  show ?thesis
    using wf_measures [of "[?m1, ?m2]"]
    by rule (auto simp add: * elim!: dvdE split: if_splits)
qed
  
lemma prime_product_factor_main: assumes "\<not> (\<exists> s. s * s = n)"
  and "limit = nat (root_nat_floor 3 n)"
  and "m = factor_sq * factor_sq * factor_pr * n"
  and "prime_product_factor_main factor_sq factor_pr limit n i = (sq, p)"
  and "i \<ge> 2"
  and "\<And> j. j \<ge> 2 \<Longrightarrow> j < i \<Longrightarrow> \<not> j dvd n"
  and "\<And> j. prime j \<Longrightarrow> j < i \<Longrightarrow> multiplicity j factor_pr \<le> 1"
  and "\<And> j. prime j \<Longrightarrow> j \<ge> i \<Longrightarrow> multiplicity j factor_pr = 0"
  and "factor_pr > 0"
  shows "m = sq * sq * p \<and> prime_product p"
  using assms
proof (induct factor_sq factor_pr limit n i rule: prime_product_factor_main.induct)
  case (1 factor_sq factor_pr limit n i)
  note IH = 1(1-3)
  note prems = 1(4-)
  note simp = prems(4)[unfolded prime_product_factor_main.simps[of factor_sq factor_pr limit n i]]
  show ?case
  proof (cases "i \<le> limit")
    case True note i = this
    with prems(5) have cond: "i \<le> limit \<and> i \<ge> 2" and *: "(i \<le> limit \<and> i \<ge> 2) = True" by blast+
    note IH = IH[OF cond]
    note simp = simp[unfolded * if_True]
    show ?thesis
    proof (cases "i dvd n")
      case False
      hence *: "(i dvd n) = False" by simp
      note simp = simp[unfolded * if_False]      
      note IH = IH(3)[OF False prems(1-3) simp]
      show ?thesis
      proof (rule IH)
        fix j
        assume 2: "2 \<le> j" and j: "j < Suc i"
        from prems(6)[OF 2] j False
        show "\<not> j dvd n" by (cases "j = i", auto)
      next
        fix j :: nat
        assume j: "j < Suc i" "prime j"
        with prems(7-8)[of j] 
        show "multiplicity j factor_pr \<le> 1" by (cases "j = i", auto)
      qed (insert prems(8-9) cond, auto)
    next
      case True note mod = this
      hence "(i dvd n) = True" by simp
      note simp = simp[unfolded this if_True Let_def]
      note IH = IH(1,2)[OF True refl]
      show ?thesis
      proof (cases "i dvd n div i")
        case True
        hence *: "(i dvd n div i) = True" by auto
        define n' where "n' = n div i div i"
        from mod True have n: "n = n' * i * i" by (auto simp: n'_def dvd_eq_mod_eq_0)
        note simp = simp[unfolded * if_True split]
        note IH = IH(1)[OF True refl _ refl _ simp prems(5) _ prems(7-9)]
        show ?thesis
        proof (rule IH)
          show "m = factor_sq * i * (factor_sq * i) * factor_pr * (n div i div i)"
            unfolding prems(3) n'_def[symmetric]
            unfolding n by (auto simp: field_simps)
        next
          fix j
          assume "2 \<le> j" "j < i"
          from prems(6)[OF this] have "\<not> j dvd n" by auto
          thus "\<not> j dvd n div i div i" 
            by (metis dvd_mult n n'_def mult.commute)
        next
          show "\<not> (\<exists> s. s * s = n div i div i)"
          proof
            assume "\<exists> s. s * s = n div i div i"
            then obtain s where "s * s = n div i div i" by auto
            hence "(s * i) * (s * i) = n" unfolding n by auto
            with prems(1) show False by blast
          qed
        qed
      next
        case False        
        define n' where "n' = n div i"
        from mod True have n: "n = n' * i" by (auto simp: n'_def dvd_eq_mod_eq_0)
        have prime: "prime i" 
          unfolding prime_nat_iff
        proof (intro conjI allI impI)
          fix m
          assume m: "m dvd i"
          hence "m dvd n" unfolding n by auto
          with prems(6)[of m] have choice: "m \<le> 1 \<or> m \<ge> i" by arith
          from m prems(5) have "m > 0"
            by (metis dvd_0_left_iff le0 le_antisym neq0_conv zero_neq_numeral)
          with choice have choice: "m = 1 \<or> m \<ge> i" by arith
          from m prems(5) have "m \<le> i" 
            by (metis False div_by_0 dvd_refl dvd_imp_le gr0I)
          with choice
          show "m = 1 \<or> m = i" by auto        
        qed (insert prems(5), auto)
        from False have "(i dvd n div i) = False" by auto
        note simp = simp[unfolded this if_False]
        note IH = IH(2)[OF False _ _ refl]
        from prime have "i > 0" by (simp add: prime_gt_0_nat)

        show ?thesis
        proof (cases "sqrt_nat (n div i)")
          case (Cons s)
          note simp = simp[unfolded Cons list.simps]
          hence sq: "sq = factor_sq * s" and p: "p = factor_pr * i" by auto          
          from arg_cong[OF Cons, of set] have s: "s * s = n div i" by auto
          have pp: "prime_product (factor_pr * i)" 
            unfolding prime_product_def
          proof safe
            fix m :: nat assume m: "prime m"
            consider "i < m" | "i > m" | "i = m" by force
            thus "multiplicity m (factor_pr * i) \<le> 1"
              by cases (insert prems(7)[of m] prems(8)[of m] prems(9) \<open>i > 0\<close> prime m,
                          simp_all add: multiplicity_prime prime_elem_multiplicity_mult_distrib)
          qed
          show ?thesis unfolding sq p prems(3) n unfolding n'_def s[symmetric]
            using pp by auto
        next
          case Nil
          note simp = simp[unfolded Nil list.simps]
          from arg_cong[OF Nil, of set] have "\<not> (\<exists> x. x * x = n div i)" by simp
          note IH = IH[OF Nil this  _ simp] 
          show ?thesis
          proof (rule IH)
            show "m = factor_sq * factor_sq * (factor_pr * i) * (n div i)" 
              unfolding prems(3) n by auto
          next
            fix j
            assume *: "2 \<le> j" "j < Suc i"
            show "\<not> j dvd n div i"
            proof
              assume j: "j dvd n div i"
              with False have "j \<noteq> i" by auto
              with * have "2 \<le> j" "j < i" by auto
              from prems(6)[OF this] j
              show False unfolding n
                by (metis dvd_mult n n'_def mult.commute)
            qed
          next
            fix j :: nat 
            assume "Suc i \<le> j" and j_prime: "prime j"
            hence ij: "i \<le> j" and j: "j \<noteq> i" by auto
            have 0: "multiplicity j i = 0" using prime j by (rule multiplicity_prime)
            show "multiplicity j (factor_pr * i) = 0" 
              unfolding prems(8)[OF j_prime ij] 0 
              using prime j_prime j \<open> 0 < factor_pr\<close> \<open>multiplicity j factor_pr = 0\<close>
              by (subst prime_elem_multiplicity_mult_distrib) (auto simp: multiplicity_prime)
          next
            fix j 
            assume "j < Suc i" and j_prime: "prime j"
            hence "j < i \<or> j = i" by auto
            thus "multiplicity j (factor_pr * i) \<le> 1"
            proof 
              assume "j = i"
              with prems(8)[of i] prime j_prime \<open>0 < factor_pr\<close> show ?thesis
                by (subst prime_elem_multiplicity_mult_distrib) auto
            next
              assume ji: "j < i"
              hence "j \<noteq> i" by auto
              from prems(7)[OF j_prime ji] multiplicity_prime[OF prime this]
                   prime j_prime \<open>0 < factor_pr\<close>
              show ?thesis by (subst prime_elem_multiplicity_mult_distrib) auto
            qed
          qed (insert prems(5,9), auto)
        qed
      qed
    qed
  next
    case False
    hence "(i \<le> limit \<and> i \<ge> 2) = False" by auto
    note simp = simp[unfolded this if_False]
    hence sq: "sq = factor_sq" and p: "p = factor_pr * n" by auto
    show ?thesis
    proof
      show "m = sq * sq * p" unfolding sq p prems(3) by simp
      show "prime_product p" unfolding prime_product_def
      proof safe
        fix m :: nat assume m: "prime m"
        from prems(1) have n1: "n > 1" by (cases n, auto, case_tac nat, auto)
        hence n0: "n > 0" by auto
        have "i > limit" using False by auto
        from this[unfolded prems(2)] have less: "int i \<ge> root_nat_floor 3 n + 1" by auto
        have "int n < (root_nat_floor 3 n + 1) ^ 3" by (rule root_nat_floor_upper, auto)
        also have "\<dots> \<le> int i ^ 3" by (rule power_mono[OF less, of 3], auto)
        finally have n_i3: "n < i ^ 3"
          by (metis of_nat_less_iff of_nat_power [symmetric])
        {
          fix m
          assume m: "prime m" "multiplicity m n > 0"
          hence mp: "m \<in> prime_factors n"
            by (auto simp: prime_factors_multiplicity)
          hence md: "m dvd n" 
            by auto
          then obtain k where n: "n = m * k" ..
          from mp have pm: "prime m" by auto
          hence m2: "m \<ge> 2" and m0: "m > 0" by (auto simp: prime_nat_iff)
          from prems(6)[OF m2] md have mi: "m \<ge> i" by force
          {
            assume "multiplicity m n \<noteq> 1"
            with m have "\<exists> k. multiplicity m n = 2 + k" by presburger
            then obtain j where mult: "multiplicity m n = 2 + j" ..
            from n0 n have k: "k > 0" by auto
            from mult m0 k n m have "multiplicity m k > 0"
              by (auto simp: prime_elem_multiplicity_mult_distrib)
            with m have mp: "m \<in> prime_factors k"
              by (auto simp: prime_factors_multiplicity)
            hence md: "m dvd k" by (auto simp: k)
            then obtain l where kml: "k = m * l" ..
            note n = n[unfolded kml]
            from n have "l dvd n" by auto
            with prems(6)[of l] have "l \<le> 1 \<or> l \<ge> i" by arith
            with n n0 have l: "l = 1 \<or> l \<ge> i" by auto
            from n prems(1) have "l \<noteq> 1" by auto
            with l have l: "l \<ge> i" by auto
            from mult_le_mono[OF mult_le_mono[OF mi mi] l]
            have "n \<ge> i^3" unfolding n by (auto simp: power3_eq_cube)
            with n_i3 have False by auto
          }
          with mi m
          have "multiplicity m n = 1 \<and> m \<ge> i" by auto
        } note n = this
        have "multiplicity m p = multiplicity m factor_pr + multiplicity m n"
          unfolding p using prems(1,9) m \<open>n > 0\<close>
          by (auto simp: prime_elem_multiplicity_mult_distrib)
        also have "\<dots> \<le> 1"
        proof (cases "m < i")
          case True
          from prems(7)[of m] n[of m] True m show ?thesis by force
        next
          case False
          hence "m \<ge> i" by auto
          from prems(8)[OF m(1) this] n[of m] m show ?thesis by force
        qed
        finally show "multiplicity m p \<le> 1" .
      qed
    qed
  qed
qed


definition prime_product_factor :: "nat \<Rightarrow> nat \<times> nat" where
  "prime_product_factor n = (case sqrt_nat n of 
     (Cons s _) \<Rightarrow> (s,1)
   | [] \<Rightarrow> prime_product_factor_main 1 1 (nat (root_nat_floor 3 n)) n 2)"

lemma prime_product_one[simp, intro]: "prime_product 1"
  unfolding prime_product_def multiplicity_one_nat by auto

lemma prime_product_factor: assumes pf: "prime_product_factor n = (sq,p)"
  shows "n = sq * sq * p \<and> prime_product p"
proof (cases "sqrt_nat n")
  case (Cons s) 
  from pf[unfolded prime_product_factor_def Cons] arg_cong[OF Cons, of set]
    prime_product_one
  show ?thesis by auto
next
  case Nil
  from arg_cong[OF Nil, of set] have nsq: "\<not> (\<exists>s. s * s = n)" by auto
  show ?thesis
    by (rule prime_product_factor_main[OF nsq refl, of _ 1 1 2], unfold multiplicity_one,
    insert pf[unfolded prime_product_factor_def Nil], auto)
qed

end
