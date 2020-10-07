section\<open>Sum of divisors function\<close>

theory Sigma
imports PerfectBasics "HOL-Library.Infinite_Set"
begin

definition divisors :: "nat => nat set" where
    "divisors (m::nat) == {n . n dvd m}"

definition sigma :: "nat => nat" where
    "sigma m == \<Sum> n | n dvd m . n"

lemma sigma_divisors: "sigma(n) = \<Sum> (divisors(n))"
by (auto simp: sigma_def divisors_def)

lemma divisors_eq_dvd[iff]: "(a:divisors(n)) = (a dvd n)"
by(simp add: divisors_def)

lemma mult_divisors: "(a::nat)*b=c==>a: divisors c"
by (unfold divisors_def dvd_def,blast)
lemma mult_divisors2: "(a::nat)*b=c==>b: divisors c"
by (unfold divisors_def dvd_def,auto)

lemma divisorsfinite[simp]:
   assumes "n>0"
   shows "finite (divisors n)"
proof -
  from assms have  "divisors n = {m . m dvd n & m <= n}"
    by (auto simp only:divisors_def dvd_imp_le)
  hence "divisors n <= {m . m<=n}" by auto
  thus "finite (divisors n)"
    by (metis finite_Collect_le_nat finite_subset) 
qed

lemma divs_of_zero_UNIV[simp]: "divisors(0) = UNIV"
by(auto simp add: divisors_def)

lemma sigma0[simp]: "sigma(0) = 0"
by (simp add: sigma_def)
lemma sigma1[simp]: "sigma(1) = 1"
by (simp add: sigma_def)

lemma prime_divisors: "prime (p::nat) \<longleftrightarrow> divisors p = {1,p} & p>1"
  by (auto simp add: divisors_def prime_nat_iff)

lemma prime_imp_sigma: "prime (p::nat) ==> sigma(p) = p+1"
proof -
  assume "prime (p::nat)"
  hence "p>1 \<and> divisors(p) = {1,p}" by (simp add: prime_divisors)
  hence "p>1 \<and> sigma(p) = \<Sum> {1,p}" by (auto simp only: sigma_divisors divisors_def)
  thus "sigma(p) = p+1" by simp
qed

lemma sigma_third_divisor:
  assumes  "1 < a" "a < n" "a : divisors n"
  shows "1+a+n <= sigma(n)"
proof -
  from assms have "finite {1,a,n} & finite (divisors n) & {1,a,n} <= divisors n" by auto
  hence "\<Sum> {1,a,n} <= \<Sum> (divisors n)" by (simp only: sum_mono2)
  hence "\<Sum> {1,a,n} <= sigma n" by (simp add: sigma_divisors)
  with assms show "?thesis" by auto
qed

lemma sigma_imp_divisors: "sigma(n)=n+1 ==> n>1 & divisors n = {n,1}"
proof
  assume ass:"sigma(n)=n+1"
  hence "n\<noteq>0 & n\<noteq>1"
    by (metis Suc_eq_plus1 n_not_Suc_n sigma0 sigma1)
  thus conc1: "n>1" by simp

  show "divisors n = {n,1}" (*TODO: use sigma_third_divisor *)
  proof (rule ccontr)
    assume "divisors n \<noteq> {n,1}"
    with conc1 have "divisors n \<noteq> {n,1} & 1<n" by auto
    moreover
    from ass conc1 have "1 : divisors(n) & n : divisors n & ~0 : divisors n"
      by (simp add: dvd_def divisors_def)
    ultimately
    have  "(\<exists>a. a\<noteq>n & a\<noteq>1 & 1<n & a : divisors n) & 0 ~: divisors n" by auto
    hence "(\<exists>a. a\<noteq>n & a\<noteq>1 & 1<n & a\<noteq>0 & a : divisors n)" by metis
    hence "\<exists>a . a\<noteq>n & a\<noteq>1 & 1\<noteq>n & a\<noteq>0 & finite {1,a,n} & finite (divisors n) & {1,a,n} <= divisors n" by auto
    hence "\<exists>a. a\<noteq>n & a\<noteq>1 & 1\<noteq>n & a\<noteq>0 & \<Sum> {1,a,n} <= sigma n"
      by (metis sum_mono2_nat sigma_divisors)
    hence "\<exists>a. a\<noteq>0 & (1+a+n) <= sigma n" by auto
    hence "1+n<sigma n" by auto (*TODO: this step can be deleted, should i?*)
    with ass show "False" by auto
  qed
qed


lemma sigma_imp_prime: "sigma(n)=n+1 ==> prime n"
proof -
  assume ass: "sigma(n)=n+1"
  hence "n>1 & divisors(n)={1,n}" by (metis insert_commute sigma_imp_divisors)
  thus "prime n" by (simp add: prime_divisors)
qed

lemma pr_pow_div_eq_sm_pr_pow: 
  fixes p::nat
  assumes prime: "prime p"
  shows "{d . d dvd p^n} = {p^f| f . f<=n}"
proof
  show "{p^f | f . f<=n} <= { d .  d dvd p^n}"
  proof
    fix x
    assume "x: {p ^ f | f . f <= n}"
    hence "\<exists>i . x = p^i & i<= n"   by auto
    with prime have  "x dvd p^n"
      by (metis le_imp_power_dvd) 
    thus "x : { d . d dvd p^n}" by auto
  qed
  next
  show "{d. d dvd p ^ n} <= {p ^ f | f . f <= n}"
  proof
    fix x
    assume "x : {d . d dvd p^n}"
    hence "x dvd p^n" by auto
    with prime obtain "i" where  "i <= n & x = p^i" using prime_dvd_power_nat_iff prime_dvd_power_nat
      by (auto simp only: divides_primepow_nat)
    hence "x = p^i & i <=n" by auto
    thus "x : { p^f | f . f<=n }" by auto
  qed
qed

lemma rewrite_sum_of_powers:
assumes p: "(p::nat)>1"
shows "(\<Sum> {p^m | m . m<=(n::nat)}) = (\<Sum> i = 0 .. n . p^i)" (is "?l = ?r")
proof -
  have "?l = sum (%x. x) {((^) p) m |m . m<= n}" by auto
  also have "... = sum (%x. x) (((^) p)`{m . m<= n})"
    by (simp add: setcompr_eq_image)
  moreover with p have "inj_on ((^) p) {m . m<=n}"
    by (simp add: inj_on_def)
  ultimately have "?l = sum ((^) p) {m . m<=n}"
    by (simp add: sum.reindex)
  moreover have "{m::nat . m<=n} = {0..n}" by auto
  ultimately show "?l = (\<Sum> i = 0 .. n . p^i)" by auto
qed

theorem sigma_primepower:
  "prime p ==> (p - 1)*sigma(p^(e::nat)) = (p^(e+1) - 1)"
proof -
  assume "prime p"
  hence "sigma(p^(e::nat)) = (\<Sum>i=0 .. e . p^i)"
    by (simp add: pr_pow_div_eq_sm_pr_pow sigma_def rewrite_sum_of_powers prime_nat_iff)
  thus "(p - 1)*sigma(p^e)=p^(e+1) - 1" by (simp only: simplify_sum_of_powers)
qed

lemma sigma_prime_power_two: "sigma(2^(n::nat)) = 2^(n+1) - 1"
proof -
  have "(2 - 1)*sigma(2^(n::nat))=2^(n+1) - 1"
    by (auto simp only: sigma_primepower two_is_prime_nat)
  thus ?thesis by simp
qed

lemma prodsums_eq_sumprods:
  fixes p :: nat and m :: nat
  assumes "coprime p m"
  shows "\<Sum>{p ^ f |f. f \<le> n} * \<Sum>{b. b dvd m} = \<Sum>{p ^ f * b |f b. f \<le> n \<and> b dvd m}" (is "?lhs = ?rhs")
proof -
  have "coprime p x" if "x dvd m" for x
    using assms by (rule coprime_imp_coprime) (auto intro: dvd_trans that)
  then have "coprime (p ^ f) x" if "x dvd m" for x f
    using that by simp
  then have "?lhs = \<Sum>{a * b |a b. (\<exists>f. a = p ^ f \<and> f \<le> n) \<and> b dvd m}"
    by (subst sum_mult_sum_if_inj [OF mult_inj_if_coprime_nat]) auto
  also have "... = ?rhs"
    by (blast intro: sum.cong)
  finally show ?thesis .
qed

declare [[simproc add: finite_Collect]]

lemma rewrite_for_sigma_semimultiplicative:
fixes p::nat
assumes "prime p"
shows "{p^f*b |f b. f<=n & b dvd m} = {a*b |a b. a dvd (p^n) & b dvd m}"
proof
  show "{p^f * b |f b. f <= n & b dvd m} <= {a*b |a b. a dvd p ^ n & b dvd m}"
  proof
    fix x
    assume "x : {p ^ f * b | f b. f <= n & b dvd m}"
    then obtain b f where "x = p^f*b & f <= n & b dvd m" by auto
    with \<open>prime p\<close> show "x : {a * b |a b. a dvd p ^ n & b dvd m}"
      by (auto simp add: divides_primepow_nat)
  qed
next
  show "{a*b |a b. a dvd p ^ n & b dvd m} <= {p^f * b |f b. f <= n & b dvd m}"
    using \<open>prime p\<close> by auto (metis assms divides_primepow_nat)
qed


lemma div_decomp_comp:
  fixes a::nat
  shows "coprime m n \<Longrightarrow> a dvd m*n \<longleftrightarrow> (\<exists>b c. a = b * c & b dvd m & c dvd n)"
by (auto simp only: division_decomp mult_dvd_mono)

theorem sigma_semimultiplicative:
  assumes p: "prime p" and cop: "coprime p m"
  shows "sigma (p^n) * sigma m = sigma (p^n * m)" (is "?l = ?r")
proof -
  from cop have cop2: "coprime (p^n) m"
    by simp
  have "?l = (\<Sum> {a . a dvd p^n})*(\<Sum> {b . b dvd m})" by (simp add: sigma_def)
  also from p have "... = (\<Sum> {p^f| f . f<=n})*(\<Sum> {b . b dvd m})"
    by (simp add: pr_pow_div_eq_sm_pr_pow)
  also from cop  have "... = (\<Sum> {p^f*b| f b . f<=n & b dvd m})"
    by (auto simp add: prodsums_eq_sumprods prime_nat_iff)
  also have "... = (\<Sum> {a*b| a b . a dvd (p^n) & b dvd m})"
    by (simp add: p rewrite_for_sigma_semimultiplicative)
  finally have "?l = \<Sum>{c. c dvd (p^n*m)}" by (subst div_decomp_comp[OF cop2])
  thus "?l = sigma (p^n*m)" by (auto simp add: sigma_def)
qed

end
