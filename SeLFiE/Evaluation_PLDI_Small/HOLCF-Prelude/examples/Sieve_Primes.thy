theory Sieve_Primes
  imports
    "HOL-Computational_Algebra.Primes"
    "../Num_Class"
    "../HOLCF_Prelude"
(*FIXME: import order matters, if HOLCF_Prelude is not imported last,
constants like "filter" etc. refer to List.thy; I'm afraid however
that the current order only works by accident*)
begin

section \<open>The Sieve of Eratosthenes\<close>

declare [[coercion int]]
declare [[coercion_enabled]]

text \<open>
  This example proves that the well-known Haskell two-liner that lazily
  calculates the list of all primes does indeed do so. This proof is using
  coinduction.
\<close>

text \<open>
  We need to hide some constants again since we imported something from HOL
  not via @{theory "HOLCF-Prelude.HOLCF_Main"}.
\<close>

no_notation
  Rings.divide (infixl "div" 70) and
  Rings.modulo (infixl "mod" 70)

no_notation
  Set.member  ("(:)") and
  Set.member  ("(_/ : _)" [51, 51] 50)

text \<open>This is the implementation. We also need a modulus operator.\<close>
fixrec sieve :: "[Integer] \<rightarrow> [Integer]" where
  "sieve\<cdot>(p : xs) = p : (sieve\<cdot>(filter\<cdot>(\<Lambda> x. neg\<cdot>(eq\<cdot>(mod\<cdot>x\<cdot>p)\<cdot>0))\<cdot>xs))"

fixrec primes :: "[Integer]" where
  "primes = sieve\<cdot>[2..]"

text \<open>Simplification rules for modI:\<close>

definition MkI' :: "int \<Rightarrow> Integer" where
  "MkI' x = MkI\<cdot>x"

lemma MkI'_simps [simp]:
  shows "MkI' 0 = 0" and "MkI' 1 = 1" and "MkI' (numeral k) = numeral k"
  unfolding MkI'_def zero_Integer_def one_Integer_def numeral_Integer_eq
  by rule+

lemma modI_numeral_numeral [simp]:
  "mod\<cdot>(numeral i)\<cdot>(numeral j) = MkI' (Rings.modulo (numeral i) (numeral j))"
  unfolding numeral_Integer_eq mod_Integer_def MkI'_def by simp

text \<open>Some lemmas demonstrating evaluation of our list:\<close>

lemma "primes !! 0 = 2"
  unfolding primes.simps
  apply (simp only: enumFrom_intsFrom_conv)
  apply (subst intsFrom.simps)
  apply simp
  done

lemma "primes !! 1 = 3"
  unfolding primes.simps
  apply (simp only: enumFrom_intsFrom_conv)
  apply (subst intsFrom.simps)
  apply (subst intsFrom.simps)
  apply simp
  done

lemma "primes !! 2 = 5"
  unfolding primes.simps
  apply (simp only: enumFrom_intsFrom_conv)
  apply (subst intsFrom.simps)
  apply (subst intsFrom.simps)
  apply (subst intsFrom.simps)
  apply (subst intsFrom.simps)
  apply simp
  done

lemma "primes !! 3 = 7"
  unfolding primes.simps
  apply (simp only: enumFrom_intsFrom_conv)
  apply (subst intsFrom.simps)
  apply (subst intsFrom.simps)
  apply (subst intsFrom.simps)
  apply (subst intsFrom.simps)
  apply (subst intsFrom.simps)
  apply (subst intsFrom.simps)
  apply (simp del: filter_FF filter_TT)
  (* FIXME: remove these two from the default simpset *)
  done

text \<open>Auxiliary lemmas about prime numbers\<close>

lemma find_next_prime_nat:
  fixes n :: nat
  assumes "prime n"
  shows "\<exists> n'. n' > n \<and> prime n' \<and> (\<forall>k. n < k \<longrightarrow> k < n' \<longrightarrow> \<not> prime k)"
  using ex_least_nat_le[of "\<lambda> k . k > n \<and> prime k"]
  by (metis bigger_prime not_prime_0)


text \<open>Simplification for andalso:\<close>

lemma andAlso_Def[simp]: "((Def x) andalso (Def y)) = Def (x \<and> y)"
  by (metis Def_bool2 Def_bool4 andalso_thms(1) andalso_thms(2))

text \<open>This defines the bisimulation and proves it to be a list bisimulation.\<close>

definition prim_bisim:
  "prim_bisim x1 x2 = (\<exists> n . prime n  \<and>
    x1 = sieve\<cdot>(filter\<cdot>(\<Lambda> (MkI\<cdot>i). Def ((\<forall>d. d > 1 \<longrightarrow> d < n \<longrightarrow> \<not> (d dvd i))))\<cdot>[MkI\<cdot>n..]) \<and>
    x2 = filter\<cdot>(\<Lambda> (MkI\<cdot>i). Def (prime (nat \<bar>i\<bar>)))\<cdot>[MkI\<cdot>n..])"

lemma prim_bisim_is_bisim: "list_bisim prim_bisim"
proof -
  {
    fix xs ys
    assume "prim_bisim xs ys"
    then obtain n :: nat where
      "prime n" and
      "n > 1" and
      "xs = sieve\<cdot>(filter\<cdot>(\<Lambda> (MkI\<cdot>i). Def ((\<forall>d::int. d > 1 \<longrightarrow> d < n \<longrightarrow> \<not> (d dvd i))))\<cdot>[MkI\<cdot>n..])" (is "_ = sieve\<cdot>?xs") and
      "ys = filter\<cdot>(\<Lambda> (MkI\<cdot>i). Def (prime (nat \<bar>i\<bar>)))\<cdot>[MkI\<cdot>n..]"
      (* sledgehammer *)
    proof -
      assume a1: "\<And>n. \<lbrakk>prime n; 1 < n; xs = sieve\<cdot> (Data_List.filter\<cdot> (\<Lambda> (MkI\<cdot>i). Def (\<forall>d>1. d < int n \<longrightarrow> \<not> d dvd i))\<cdot> [MkI\<cdot>(int n)..]); ys = Data_List.filter\<cdot> (\<Lambda> (MkI\<cdot>i). Def (prime (nat \<bar>i\<bar>)))\<cdot> [MkI\<cdot>(int n)..]\<rbrakk> \<Longrightarrow> thesis"
      obtain ii  where
        f2: "\<forall>is isa. (\<not> prim_bisim is isa \<or> prime (ii is isa) \<and> is = sieve\<cdot> (Data_List.filter\<cdot> (\<Lambda> (MkI\<cdot>i). Def (\<forall>ia>1. ia < ii is isa \<longrightarrow> \<not> ia dvd i))\<cdot> [MkI\<cdot>(ii is isa)..]) \<and> isa = Data_List.filter\<cdot> (\<Lambda> (MkI\<cdot>i). Def (prime (nat \<bar>i\<bar>)))\<cdot> [MkI\<cdot>(ii is isa)..]) \<and> ((\<forall>i. \<not> prime i \<or> is \<noteq> sieve\<cdot> (Data_List.filter\<cdot> (\<Lambda> (MkI\<cdot>ia). Def (\<forall>ib>1. ib < i \<longrightarrow> \<not> ib dvd ia))\<cdot> [MkI\<cdot>i..]) \<or> isa \<noteq> Data_List.filter\<cdot> (\<Lambda> (MkI\<cdot>i). Def (prime (nat \<bar>i\<bar>)))\<cdot> [MkI\<cdot>i..]) \<or> prim_bisim is isa)"
        using prim_bisim by moura
      then have f3: "prime (ii xs ys)"
        using \<open>prim_bisim xs ys\<close> by blast
      then obtain nn :: "int \<Rightarrow> nat" where
        f4: "int (nn (ii xs ys)) = ii xs ys"
        by (metis (no_types) prime_gt_0_int zero_less_imp_eq_int)
      then have "prime (nn (ii xs ys))"
        using f3 by (metis (no_types) prime_nat_int_transfer)
      then show ?thesis
        using f4 f2 a1 \<open>prim_bisim xs ys\<close> prime_gt_1_nat by presburger
    qed

    obtain n' where "n' > n" and "prime n'" and not_prime: "\<forall>k. n < k \<longrightarrow> k < n' \<longrightarrow> \<not> prime k"
      using find_next_prime_nat[OF \<open>prime n\<close>] by auto

    {
      fix k :: int
      assume "n < k" and "k < n'"

      have  "k > 1" using \<open>n < k\<close> \<open>n > 1\<close> by auto
      then obtain k' :: nat where "k = int k'" by (cases k) auto
      then obtain p where "prime p" and "p dvd k"
        using \<open>k > 1\<close> \<open>k = int k'\<close>
        by (metis (full_types) less_numeral_extra(4) of_nat_1 of_nat_dvd_iff prime_factor_nat prime_nat_int_transfer)  
      then have "p < n'" using \<open>k < n'\<close>  \<open>k > 1\<close>
        using zdvd_imp_le [of p k] by simp
      then have "p \<le> n" using \<open>prime p\<close> not_prime
        using not_le prime_gt_0_int zero_less_imp_eq_int
        by (metis of_nat_less_iff prime_nat_int_transfer) 
      then have "\<exists>d::int>1. d \<le> n \<and> d dvd k" using \<open>p dvd k\<close> \<open>prime p\<close> of_nat_le_iff prime_gt_1_nat
          prime_gt_1_int by auto
    }
    then have between_have_divisors: "\<And>k::int. n < k \<Longrightarrow> k < n' \<Longrightarrow> \<exists>d::int>1. d \<le> n \<and> d dvd k".

    {
      fix i
      {
        assume small: "\<forall>d::int>1. d \<le> n \<longrightarrow> \<not> d dvd i"
        fix d
        assume "1 < d" and "d dvd i" and "d < n'"
        with small have "d > n" by auto

        obtain d'::int where "d' > 1" and "d' \<le> n" and "d' dvd d" using between_have_divisors[OF \<open>n < d\<close> \<open>d < n'\<close>] by auto
        with \<open>d dvd i\<close> small have False by (metis (full_types) dvd_trans)
      }
      then have "(\<forall>d::int. d > 1 \<longrightarrow> d \<le> n \<longrightarrow> \<not> (d dvd i)) = (\<forall>d::int. d > 1 \<longrightarrow> d < n' \<longrightarrow> \<not> (d dvd i))"
        using \<open>n' > n\<close> by auto
    }
    then have between_not_relvant:  "\<And> i. (\<forall>d::int. d > 1 \<longrightarrow> d \<le> n \<longrightarrow> \<not> (d dvd i)) = (\<forall>d::int. d > 1 \<longrightarrow> d < n' \<longrightarrow> \<not> (d dvd i))" .

    from \<open>prime n\<close>
    have "\<forall>d::int >1. d < n \<longrightarrow> \<not> d dvd n"
      unfolding prime_int_altdef using int_one_le_iff_zero_less le_less
      by (simp add: prime_int_not_dvd)
    then
    obtain xs' where "?xs = (MkI\<cdot>n) : xs'" and "xs' = filter\<cdot>(\<Lambda> (MkI\<cdot>i). Def ((\<forall>d::int. d > 1 \<longrightarrow> d < n \<longrightarrow> \<not> (d dvd i))))\<cdot>[MkI\<cdot>(n+1)..]"
      by (subst (asm) intsFrom.simps[unfolded enumFrom_intsFrom_conv[symmetric]], simp add: one_Integer_def TT_def[symmetric] add.commute)

    {
      have "filter\<cdot>(\<Lambda> x. neg\<cdot>(eq\<cdot>(mod\<cdot>x\<cdot>(MkI\<cdot>n))\<cdot>0))\<cdot>(filter\<cdot>(\<Lambda> (MkI\<cdot>i). Def ((\<forall>d::int. d > 1 \<longrightarrow> d < n \<longrightarrow> \<not> (d dvd i))))\<cdot>[MkI\<cdot>(n+1)..])
            = filter\<cdot>(\<Lambda> (MkI\<cdot>x). Def (\<not> n dvd x))\<cdot>(filter\<cdot>(\<Lambda> (MkI\<cdot>i). Def ((\<forall>d::int. d > 1 \<longrightarrow> d < n \<longrightarrow> \<not> (d dvd i))))\<cdot>[MkI\<cdot>(n+1)..])"
        apply (rule filter_cong[rule_format])
        apply (rename_tac x, case_tac x)
         apply (simp)
        apply (auto simp add: zero_Integer_def)
         apply (rule FF_def)
        apply (simp add: TT_def)
        by (metis dvd_eq_mod_eq_0)
      also have "... = filter\<cdot>(\<Lambda> (MkI\<cdot>i). Def ((\<not> n dvd i) \<and> (\<forall>d::int. d > 1 \<longrightarrow> d < n \<longrightarrow> \<not> (d dvd i))))\<cdot>[MkI\<cdot>(n+1)..]"
        by (auto intro!: filter_cong[rule_format])
      also have "... = filter\<cdot>(\<Lambda> (MkI\<cdot>i). Def ((\<forall>d::int. d > 1 \<longrightarrow> d \<le> n \<longrightarrow> \<not> (d dvd i))))\<cdot>[MkI\<cdot>(n+1)..]"
        apply (rule filter_cong[rule_format])
        apply (rename_tac x, case_tac x)
        using \<open>n > 1\<close>
         apply auto
        done
      also have "... = filter\<cdot>(\<Lambda> (MkI\<cdot>i). Def ((\<forall>d::int. d > 1 \<longrightarrow> d \<le> n \<longrightarrow> \<not> (d dvd i))))\<cdot>[MkI\<cdot>(int n+1)..]"
        by (metis (no_types, lifting) of_nat_1 of_nat_add)
      also have "... = filter\<cdot>(\<Lambda> (MkI\<cdot>i). Def ((\<forall>d::int. d > 1 \<longrightarrow> d \<le> n \<longrightarrow> \<not> (d dvd i))))\<cdot>[MkI\<cdot>n'..]"
        apply (rule filter_fast_forward[of n n'])  using \<open>n' > n\<close>
         apply (auto simp add: between_have_divisors)
        done
      also have "... = filter\<cdot>(\<Lambda> (MkI\<cdot>i). Def ((\<forall>d::int. d > 1 \<longrightarrow> d < n' \<longrightarrow> \<not> (d dvd i))))\<cdot>[MkI\<cdot>n'..]"
        by (auto intro: filter_cong[rule_format] simp add: between_not_relvant)
      also note calculation
    }
    note tmp = this

    {
      have "xs = sieve\<cdot>?xs" by fact
      also have "... = sieve\<cdot>((MkI\<cdot>n) : xs')" using \<open>?xs = _\<close> by simp
      also have "... = sieve\<cdot>((MkI\<cdot>n) : filter\<cdot>(\<Lambda> (MkI\<cdot>i). Def ((\<forall>d::int. d > 1 \<longrightarrow> d < n \<longrightarrow> \<not> (d dvd i))))\<cdot>[MkI\<cdot>(n+1)..])" using \<open>xs' = _\<close> by simp
      also have "... = (MkI\<cdot>n) : sieve\<cdot>(filter\<cdot>(\<Lambda> (MkI\<cdot>i). Def ((\<forall>d::int. d > 1 \<longrightarrow> d < n' \<longrightarrow> \<not> (d dvd i))))\<cdot>[MkI\<cdot>n'..])"  using tmp by simp
      also note calculation
    }
    moreover
    {
      have "ys = filter\<cdot>(\<Lambda> (MkI\<cdot>i). Def (prime (nat \<bar>i\<bar>)))\<cdot>[MkI\<cdot>n..]" by fact
      also have "... = (MkI\<cdot>n) : filter\<cdot>(\<Lambda> (MkI\<cdot>i). Def (prime (nat \<bar>i\<bar>)))\<cdot>[MkI\<cdot>(int n+1)..]"
        using \<open>prime n\<close>
        by (subst intsFrom.simps[unfolded enumFrom_intsFrom_conv[symmetric]])(simp add: one_Integer_def TT_def[symmetric] add.commute)
      also have "... = (MkI\<cdot>n) : filter\<cdot>(\<Lambda> (MkI\<cdot>i). Def (prime (nat \<bar>i\<bar>)))\<cdot>[MkI\<cdot>n'..]"
        apply (subst filter_fast_forward[of n n']) using \<open>n' > n\<close> and not_prime
          apply auto
        apply (metis (full_types) \<open>\<And>k. \<lbrakk>int n < k; k < int n'\<rbrakk> \<Longrightarrow> \<exists>d>1. d \<le> int n \<and> d dvd k\<close> le_less not_le prime_gt_0_int prime_int_not_dvd zdvd_imp_le) 
        done
      also note calculation
    }
    moreover
    note \<open>prime n'\<close>
    ultimately
    have "\<exists> p xs' ys'. xs = p : xs' \<and> ys = p : ys' \<and> prim_bisim xs' ys'" unfolding prim_bisim
      using prime_nat_int_transfer by blast
  }
  then show ?thesis unfolding list.bisim_def by metis
qed

text \<open>Now we apply coinduction:\<close>

lemma sieve_produces_primes:
  fixes n :: nat
  assumes "prime n"
  shows "sieve\<cdot>(filter\<cdot>(\<Lambda> (MkI\<cdot>i). Def ((\<forall>d::int. d > 1 \<longrightarrow> d < n \<longrightarrow> \<not> (d dvd i))))\<cdot>[MkI\<cdot>n..])
    = filter\<cdot>(\<Lambda> (MkI\<cdot>i). Def (prime (nat \<bar>i\<bar>)))\<cdot>[MkI\<cdot>n..]"
  using assms
  apply -
  apply (rule list.coinduct[OF prim_bisim_is_bisim], auto simp add: prim_bisim)
  using prime_nat_int_transfer by blast

text \<open>And finally show the correctness of primes.\<close>

theorem primes:
  shows "primes = filter\<cdot>(\<Lambda> (MkI\<cdot>i). Def (prime (nat \<bar>i\<bar>)))\<cdot>[MkI\<cdot>2..]"
proof -
  have "primes = sieve\<cdot>[2 ..]" by (rule primes.simps)
  also have "... = sieve\<cdot>(filter\<cdot>(\<Lambda> (MkI\<cdot>i). Def ((\<forall>d::int. d > 1 \<longrightarrow> d < (int 2) \<longrightarrow> \<not> (d dvd i))))\<cdot>[MkI\<cdot>(int 2)..])"
    unfolding numeral_Integer_eq
    by (subst filter_TT, auto)
  also have "... = filter\<cdot>(\<Lambda> (MkI\<cdot>i). Def (prime (nat \<bar>i\<bar>)))\<cdot>[MkI\<cdot>(int 2)..]"
    by (rule sieve_produces_primes[OF two_is_prime_nat])
  also have "... = filter\<cdot>(\<Lambda> (MkI\<cdot>i). Def (prime (nat \<bar>i\<bar>)))\<cdot>[MkI\<cdot>2..]"
    by simp
  finally show ?thesis .
qed

end
