section \<open>Efficient code for testing Mersenne primes\<close>
theory Lucas_Lehmer_Code
imports
  Lucas_Lehmer
  "HOL-Library.Code_Target_Numeral"
  "Native_Word.Code_Target_Bits_Int"
begin

subsection \<open>Efficient computation of remainders modulo a Mersenne number\<close>

text \<open>
  We have $k = k\ \text{mod}\ 2^n + k\ \text{div}\ 2^n\ \ (\text{mod}\ (2^n - 1))$,
  and $k\ \text{mod}\ 2^n = k\, \&\, (2^n - 1)$ and $k\ \text{div}\ 2^n = k \gg n$.
  Therefore, we can reduce $k$ modulo $2^n - 1$ using only bitwise operations, addition, and
  bit shifts. 
\<close>
lemma cong_mersenne_number_int:
  fixes k :: int
  shows "[k mod 2 ^ n + k div 2 ^ n = k] (mod (2 ^ n - 1))"
proof -
  have "k = (2 ^ n - 1 + 1) * (k div 2 ^ n) + (k mod 2 ^ n)"
    by simp
  also have "[\<dots> = (0 + 1) * (k div 2 ^ n) + (k mod 2 ^ n)] (mod (2 ^ n - 1))"
    by (intro cong_add cong_mult cong_refl) (auto simp: cong_def)
  finally show ?thesis by (simp add: cong_sym add_ac)
qed

text \<open>
  We encapsulate a single reduction step in the following operation. Note, however,
  that the result is not, in general, the same as $k\ \text{mod}\ (2^n - 1)$. Multiple 
  reductions might be required in order to reduce it below $2^n$, and a multiple of $2 ^ n - 1$
  can be reduced to $2 ^ n - 1$, which is invariant to further reduction steps.
\<close>
definition mersenne_mod :: "int \<Rightarrow> nat \<Rightarrow> int" where
  "mersenne_mod k n = k mod 2 ^ n + k div 2 ^ n"

lemma mersenne_mod_code [code]:
  "mersenne_mod k n = (k AND ((1 << n) - 1)) + (k >> n)"
  by (simp add: mersenne_mod_def shiftr_int_def shiftl_int_def AND_mod)

lemma cong_mersenne_mod: "[mersenne_mod k n = k] (mod (2 ^ n - 1))"
  unfolding mersenne_mod_def by (rule cong_mersenne_number_int)

lemma mersenne_mod_nonneg [simp]: "k \<ge> 0 \<Longrightarrow> mersenne_mod k n \<ge> 0"
  unfolding mersenne_mod_def by (intro add_nonneg_nonneg) (simp_all add: pos_imp_zdiv_nonneg_iff)

lemma mersenne_mod_less:
  assumes "k \<le> 2 ^ m" "m \<ge> n"
  shows   "mersenne_mod k n < 2 ^ n + 2 ^ (m - n)"
proof -
  have "mersenne_mod k n = k mod 2 ^ n + k div 2 ^ n"
    by (simp add: mersenne_mod_def)
  also have "k mod 2 ^ n < 2 ^ n"
    by simp
  also {
    have "k div 2 ^ n * 2 ^ n + 0 \<le> k div 2 ^ n * 2 ^ n + k mod (2 ^ n)"
      by (intro add_mono) auto
    also have "\<dots> = k"
      by (subst mult.commute) auto
    also have "\<dots> \<le> 2 ^ m"
      using assms by simp
    also have "\<dots> = 2 ^ (m - n) * 2 ^ n"
      using assms by (simp flip: power_add)
    finally have "k div 2 ^ n \<le> 2 ^ (m - n)"
      by simp
  }
  finally show ?thesis by simp
qed

lemma mersenne_mod_less':
  assumes "k \<le> 5 * 2 ^ n"
  shows   "mersenne_mod k n < 2 ^ n + 5"
proof -
  have "mersenne_mod k n = k mod 2 ^ n + k div 2 ^ n"
    by (simp add: mersenne_mod_def)
  also have "k mod 2 ^ n < 2 ^ n"
    by simp
  also {
    have "k div 2 ^ n * 2 ^ n + 0 \<le> k div 2 ^ n * 2 ^ n + k mod (2 ^ n)"
      by (intro add_mono) auto
    also have "\<dots> = k"
      by (subst mult.commute) auto
    also have "\<dots> \<le> 5 * 2 ^ n"
      using assms by simp
    finally have "k div 2 ^ n \<le> 5"
      by simp
  }
  finally show ?thesis by simp
qed

text \<open>
  It turns out that for our use case, a single reduction is not enough to reduce
  the number in question enough (or at least I was unable to prove that it is). We
  therefore perform two reduction steps, which is enough to guarantee that our numbers
  are below $2^n + 4$ before and after every step in the Lucas--Lehmer sequence.

  Whether one or two reductions are performed is not very important anyway, since the
  dominant step is the squaring anyway.
\<close>
definition mersenne_mod2 :: "int \<Rightarrow> nat \<Rightarrow> int" where
  "mersenne_mod2 k n = mersenne_mod (mersenne_mod k n) n"

lemma cong_mersenne_mod2: "[mersenne_mod2 k n = k] (mod (2 ^ n - 1))"
  unfolding mersenne_mod2_def by (rule cong_trans) (rule cong_mersenne_mod)+

lemma mersenne_mod2_nonneg [simp]: "k \<ge> 0 \<Longrightarrow> mersenne_mod2 k n \<ge> 0"
  unfolding mersenne_mod2_def by simp

lemma mersenne_mod2_less:
  assumes "n > 2" and "k \<le> 2 ^ (2 * n + 2)"
  shows   "mersenne_mod2 k n < 2 ^ n + 5"
proof -
  from assms have "2 ^ 3 \<le> (2 ^ n :: int)"
    by (intro power_increasing) auto
  hence "2 ^ n \<ge> (8 :: int)" by simp
  have "mersenne_mod k n < 2 ^ n + 2 ^ (2 * n + 2 - n)"
    by (rule mersenne_mod_less) (use assms in auto)
  also have "\<dots> \<le> 5 * 2 ^ n"
    by (simp add: power_add)
  finally have "mersenne_mod (mersenne_mod k n) n < 2 ^ n + 5"
    by (intro mersenne_mod_less') auto
  thus ?thesis by (simp add: mersenne_mod2_def)
qed

text \<open>
  Since we subtract 2 at one point, the intermediate results can become negative. This
  is not a problem since our reduction modulo $2 ^ p - 1$ happens to make them positive again
  immediately.
\<close>
lemma mersenne_mod_nonneg_strong:
  assumes "a > -(2 ^ p) + 1"
  shows   "mersenne_mod a p \<ge> 0"
proof (cases "a < 0")
  case True
  have "eucl_rel_int a (2 ^ p) (- 1, a + 2 ^ p)"
    using assms True by (auto simp: eucl_rel_int_iff)
  hence "a div 2 ^ p = -1" and "a mod 2 ^ p = a + 2 ^ p"
    by (simp_all add: div_int_unique mod_int_unique) 
  hence "mersenne_mod a p = a + 2 ^ p - 1"
    by (simp add: mersenne_mod_def)
  also have "\<dots> > 0" using assms by simp
  finally show ?thesis by simp
qed auto

lemma mersenne_mod2_nonneg_strong:
  assumes "a > -(2 ^ p) + 1"
  shows   "mersenne_mod2 a p \<ge> 0"
  unfolding mersenne_mod2_def 
  by (rule mersenne_mod_nonneg, rule mersenne_mod_nonneg_strong) (use assms in auto)


subsection \<open>Efficient code for the Lucas--Lehmer sequence\<close>

primrec gen_lucas_lehmer_sequence'' :: "nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int" where
  "gen_lucas_lehmer_sequence'' p a 0 = a"
| "gen_lucas_lehmer_sequence'' p a (Suc n) =
     gen_lucas_lehmer_sequence'' p (mersenne_mod2 (a ^ 2 - 2) p) n"

lemma gen_lucas_lehmer_sequence''_correct:
  assumes "[a = a'] (mod (2 ^ p - 1))"
  shows   "[gen_lucas_lehmer_sequence'' p a n = gen_lucas_lehmer_sequence a' n] (mod (2 ^ p - 1))"
  using assms
proof (induction n arbitrary: a a')
  case (Suc n)
  have "[mersenne_mod2 (a ^ 2 - 2) p = a ^ 2 - 2] (mod (2 ^ p - 1))"
    by (rule cong_mersenne_mod2)
  also have "[a ^ 2 - 2 = a' ^ 2 - 2] (mod (2 ^ p - 1))"
    by (intro cong_pow cong_diff Suc.prems cong_refl)
  finally have "[gen_lucas_lehmer_sequence'' p (mersenne_mod2 (a\<^sup>2 - 2) p) n =
                 gen_lucas_lehmer_sequence (a'\<^sup>2 - 2) n] (mod 2 ^ p - 1)"
    by (rule Suc.IH)
  thus ?case
    by (auto simp del: gen_lucas_lehmer_sequence.simps simp: gen_lucas_lehmer_sequence_Suc')
qed auto

lemma gen_lucas_lehmer_sequence''_bounds:
  assumes "a \<ge> 0" "a < 2 ^ p + 5" "p > 2"
  shows   "gen_lucas_lehmer_sequence'' p a n \<in> {0..<2 ^ p + 5}"
  using assms 
proof (induction n arbitrary: a)
  case (Suc n)
  from Suc.prems have "a ^ 2 < (2 ^ p + 5) ^ 2"
    by (intro power_strict_mono Suc.prems) auto
  also have "\<dots> \<le> (2 ^ (p + 1)) ^ 2"
    using power_increasing[of 3 p "2 :: int"] \<open>p > 2\<close> by (intro power_mono) auto
  finally have "a ^ 2 - 2 < 2 ^ (2 * p + 2)"
    by (simp flip: power_mult mult_ac)
  moreover {
    from \<open>p > 2\<close> have "(2 ^ p) \<ge> (2 ^ 3 :: int)"
      by (intro power_increasing) auto
    hence "-(2 ^ p) + 1 < (-2 :: int)"
      by simp
    also have "-2 \<le> a ^ 2 - 2"
      by simp
    finally have "mersenne_mod2 (a ^ 2 - 2) p \<ge> 0"
      by (rule mersenne_mod2_nonneg_strong)
  }
  ultimately have "gen_lucas_lehmer_sequence'' p (mersenne_mod2 (a\<^sup>2 - 2) p) n \<in> {0..<2 ^ p + 5}"
    using \<open>p > 2\<close> by (intro Suc.IH mersenne_mod2_less) auto
  thus ?case by simp
qed auto


subsection \<open>Code for the Lucas--Lehmer test\<close>

lemmas [code del] = lucas_lehmer_test_code_arithmetic

lemma lucas_lehmer_test_code [code]:
  "lucas_lehmer_test p =
     (2 < p \<and> (let x = gen_lucas_lehmer_sequence'' p 4 (p - 2) in x = 0 \<or> x = (1 << p) - 1))"
  unfolding lucas_lehmer_test_def
proof (rule conj_cong)
  assume "p > 2"
  define x where "x = gen_lucas_lehmer_sequence'' p 4 (p - 2)"
  from \<open>p > 2\<close> have "2 ^ 3 \<le> (2 ^ p :: int)" by (intro power_increasing) auto
  hence "2 ^ p \<ge> (8 :: int)" by simp
  hence bounds: "x \<in> {0..<2 ^ p + 5}"
    unfolding x_def using \<open>p > 2\<close> by (intro gen_lucas_lehmer_sequence''_bounds) auto
  have "2 ^ p - 1 dvd gen_lucas_lehmer_sequence 4 (p - 2) \<longleftrightarrow> 2 ^ p - 1 dvd x"
    unfolding x_def by (intro cong_dvd_iff cong_sym[OF gen_lucas_lehmer_sequence''_correct]) auto
  also have "\<dots> \<longleftrightarrow> x \<in> {0, 2 ^ p - 1}"
  proof
    assume "2 ^ p - 1 dvd x"
    then obtain k where k: "x = (2 ^ p - 1) * k" by auto
    have "k \<ge> 0" using bounds \<open>2 ^ p \<ge> 8\<close>
      by (auto simp: k zero_le_mult_iff)
    moreover {
      have "x < 2 ^ p + 5" using bounds by simp
      also have "\<dots> \<le> (2 ^ p - 1) * 2"
        using \<open>2 ^ p \<ge> 8\<close> by simp
      finally have "(2 ^ p - 1) * k < (2 ^ p - 1) * 2"
        unfolding k .
      hence "k < 2"
        by (subst (asm) mult_less_cancel_left) auto
    }
    ultimately have "k = 0 \<or> k = 1" by auto
    thus "x \<in> {0, 2 ^ p - 1}"
      using k by auto
  qed auto
  finally show "(2 ^ p - 1 dvd gen_lucas_lehmer_sequence 4 (p - 2)) =
                ((let x = x in x = 0 \<or> x = (1 << p) - 1))"
    by (simp add: shiftl_int_def Let_def)
qed auto


subsection \<open>Examples\<close>

text \<open>
  Note that for some reason, the clever bit-arithmetic version of the Lucas--Lehmer test is 
  actually much slower than the one using integer arithmetic when using PolyML, and even more so 
  when using the built-in evaluator in Isabelle (which also uses PolyML with a slightly different 
  setup).

  I do not quite know why this is the case, but it is likely because of inefficient implementations
  of bit arithmetic operations in PolyML and/or the code generator setup for it.

  When running with GHC, the bit-arithmetic version is \<^emph>\<open>much\<close> faster.
\<close>

value "filter mersenne_prime [0..<100]"

lemma "prime (2 ^ 521 - 1 :: nat)"
  by (subst lucas_lehmer_correct') eval

lemma "prime (2 ^ 4253 - 1 :: nat)"
  by (subst lucas_lehmer_correct') eval

end