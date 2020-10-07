(*  Title:      Fermat4.thy
    Author:     Roelof Oosterhuis
                2007  Rijksuniversiteit Groningen
*)

section \<open>Pythagorean triples and Fermat's last theorem, case $n=4$\<close>

theory Fermat4
imports "HOL-Computational_Algebra.Primes"
begin

context
begin

(* TODO: this lemma is also used in Fermat3 with a slightly different generalization to ints.
Maybe it should be generalized to factorial rings and moved to another theory. *)
private lemma nat_relprime_power_divisors: 
  assumes n0: "0 < n" and abc: "(a::nat)*b = c^n" and relprime: "coprime a b"
  shows "\<exists> k. a = k^n"
using assms proof (induct c arbitrary: a b rule: nat_less_induct)
case (1 c)
  show ?case
  proof (cases "a > 1")
  case False
    hence "a = 0 \<or> a = 1" by linarith
    thus ?thesis using n0 power_one zero_power by (simp only: eq_sym_conv) blast
  next
  case True
    then obtain p where p: "prime p" "p dvd a" using prime_factor_nat[of a] by blast
    hence h1: "p dvd (c^n)" using 1(3) dvd_mult2[of p a b] by presburger
    hence "(p^n) dvd (c^n)"
      using p(1) prime_dvd_power_nat[of p c n] dvd_power_same[of p c n] by blast
    moreover have h2: "\<not> p dvd b"
      using p \<open>coprime a b\<close> coprime_common_divisor_nat [of a b p] by auto
    hence "\<not> (p^n) dvd b" using n0 p(1)
      by (auto intro: dvd_trans dvd_power[of n p])
    ultimately have "(p^n) dvd a"
      using "1.prems" p(1) prime_elem_divprod_pow [of p a b n] by simp
    then obtain a' c' where ac: "a = p^n * a'" "c = p * c'"
      using h1 dvdE[of "p^n" a] dvdE[of p c] prime_dvd_power_nat[of p c n] p(1) by meson
    hence "p^n * (a' * b) = p^n * c'^n" using 1(3)
      by (simp add: power_mult_distrib semiring_normalization_rules(18))
    hence "a' * b = c'^n" using p(1) by auto
    moreover have "coprime a' b" using 1(4) ac(1)
      by (simp add: ac_simps)
    moreover have "0 < b" "0 < a" using h2 dvd_0_right gr0I True by fastforce+
    then have "0 < c" "1 < p"
      using p \<open>a * b = c ^ n\<close> n0 nat_0_less_mult_iff [of a b] n0
      by (auto simp add: prime_gt_Suc_0_nat)
    hence "c' < c" using ac(2) by simp
    ultimately obtain k where "a' = k^n" using 1(1) n0 by presburger
    hence "a = (p*k)^n" using ac(1) by (simp add: power_mult_distrib)
    thus ?thesis by blast
  qed
qed

private lemma int_relprime_power_divisors:
  assumes "0 < n" and "0 \<le> a" and "0 \<le> b" and "(a::int) * b = c ^ n" and "coprime a b"
  shows "\<exists>k. a = k^n"
proof (cases "a = 0")
  case False
  from \<open>0 \<le> a\<close> \<open>0 \<le> b\<close> \<open>a * b = c ^ n\<close>[symmetric] have "0 \<le> c ^ n"
    by simp
  hence "c^n = \<bar>c\<bar>^n" using power_even_abs[of n c] zero_le_power_eq[of c n] by linarith
  hence "a * b = \<bar>c\<bar>^n" using assms(4) by presburger
  hence "nat a * nat b = (nat \<bar>c\<bar>)^n" using nat_mult_distrib[of "a" "b"] assms(2)
    by (simp add: nat_power_eq)
  moreover have "0 \<le> b" using assms mult_less_0_iff[of a b] False by auto
  with \<open>0 \<le> a\<close> \<open>coprime a b\<close> have "coprime (nat a) (nat b)"
    using coprime_nat_abs_left_iff [of a "nat b"] by simp
  ultimately have "\<exists> k. nat a = k^n"
    using nat_relprime_power_divisors[of n "nat a" "nat b" "nat \<bar>c\<bar>"] assms(1) by blast
  thus ?thesis using assms(2) int_nat_eq[of "a"] by fastforce
qed (simp add: zero_power[of n] assms(1))

text \<open>Proof of Fermat's last theorem for the case $n=4$: $$\forall x,y,z:~x^4 + y^4 = z^4 \Longrightarrow xyz=0.$$\<close>

(* 
NB: this lemma is quite slow, maybe use more steps *)
private lemma nat_power2_diff: "a \<ge> (b::nat) \<Longrightarrow> (a-b)^2 = a^2 + b^2 - 2*a*b"
proof -
  assume a_ge_b: "a \<ge> b"
  hence a2_ge_b2: "a^2 \<ge> b^2" by (simp only: power_mono)
  from a_ge_b have ab_ge_b2: "a*b \<ge> b^2" by (simp add: power2_eq_square)
  have "b*(a-b) + (a-b)^2 = a*(a-b)" by (simp add: power2_eq_square diff_mult_distrib)
  also have "\<dots> = a*b + a^2 + (b^2 - b^2) - 2*a*b" 
    by (simp add: diff_mult_distrib2 power2_eq_square)
  also with a2_ge_b2 have "\<dots> = a*b + (a^2 - b^2) + b^2 - 2*a*b" by simp
  also with ab_ge_b2 have "\<dots> = (a*b - b^2) + a^2 + b^2 - 2*a*b" by auto
  also have "\<dots> = b*(a-b) + a^2 + b^2 - 2*a*b" 
    by (simp only: diff_mult_distrib2 power2_eq_square mult.commute)
  finally show ?thesis by arith
qed

private lemma nat_power_le_imp_le_base: "\<lbrakk> n \<noteq> 0; a^n \<le> b^n \<rbrakk> \<Longrightarrow> (a::nat) \<le> b"
proof -
  assume "n \<noteq> 0" and ab: "a^n \<le> b^n"
  then obtain m where "n = Suc m" by (frule_tac n="n" in not0_implies_Suc, auto)
  with ab have "a \<ge> 0" and "a^Suc m \<le> b^Suc m" and "b \<ge> 0" by auto
  thus ?thesis by (rule_tac n="m" in power_le_imp_le_base)
qed
  
private lemma nat_power_inject_base: "\<lbrakk> n \<noteq> 0; a^n = b^n \<rbrakk> \<Longrightarrow> (a::nat) = b"
proof -
  assume "n \<noteq> 0" and ab: "a^n = b^n"
  then obtain m where "n = Suc m" by (frule_tac n="n" in not0_implies_Suc, auto)
  with ab have "a^Suc m = b^Suc m" and "a \<ge> 0" and "b \<ge> 0" by auto
  thus ?thesis by (rule power_inject_base)
qed
  
subsection \<open>Parametrisation of Pythagorean triples (over $\mathbb{N}$ and $\mathbb{Z}$)\<close>

private theorem nat_euclid_pyth_triples:
  assumes abc: "(a::nat)^2 + b^2 = c^2" and ab_relprime: "coprime a b" and aodd: "odd a"
  shows "\<exists> p q. a = p^2 - q^2 \<and> b = 2*p*q \<and> c = p^2 + q^2 \<and> coprime p q"
proof -
  have two0: "(2::nat) \<noteq> 0" by simp
  from abc have a2cb: "a^2 = c^2 - b^2" by arith
  \<comment> \<open>factor $a^2$ in coprime factors $(c-b)$ and $(c+b)$; hence both are squares\<close>
  have a2factor: "a^2 = (c-b)*(c+b)"
  proof -
    have "c*b - c*b = 0" by simp
    with a2cb have "a^2 = c*c + c*b - c*b - b*b" by (simp add: power2_eq_square)
    also have "\<dots> = c*(c+b) - b*(c+b)" 
      by (simp add: add_mult_distrib2 add_mult_distrib mult.commute)
    finally show ?thesis by (simp only: diff_mult_distrib)
  qed
  have a_nonzero: "a \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> a \<noteq> 0" hence "a = 0" by simp
    with aodd have "odd (0::nat)" by simp
    thus False by simp
  qed
  have b_less_c: "b < c"
  proof -
    from abc have "b^2 \<le> c^2" by auto
    with two0 have "b \<le> c" by (rule_tac n="2" in nat_power_le_imp_le_base)
    moreover have"b \<noteq> c"
    proof
      assume "b=c" with a2cb have "a^2 = 0" by simp
      with a_nonzero show False by (simp add: power2_eq_square)
    qed
    ultimately show ?thesis by auto
  qed
  hence b2_le_c2: "b^2 \<le> c^2" by (simp add: power_mono)
  have bc_relprime: "coprime b c"
  proof -
    from b2_le_c2 have cancelb2: "c^2-b^2+b^2 = c^2" by auto
    let ?g = "gcd b c"
    have "?g^2 = gcd (b^2) (c^2)" by simp
    with cancelb2 have "?g^2 = gcd (b^2) (c^2-b^2+b^2)" by simp
    hence "?g^2 = gcd (b^2) (c^2-b^2)" using gcd_add2[of "b^2" "c^2 - b^2"] 
      by (simp add: algebra_simps del: gcd_add1)
    with a2cb have "?g^2 dvd a^2" by (simp only: gcd_dvd2)
    hence "?g dvd a \<and> ?g dvd b" by simp
    hence "?g dvd gcd a b" by (simp only: gcd_greatest)
    with ab_relprime show ?thesis
      by (simp add: ac_simps gcd_eq_1_imp_coprime)
  qed
  have p2: "prime (2::nat)" by simp
  have factors_odd: "odd (c-b) \<and> odd (c+b)"
  proof (auto simp only: ccontr)
    assume "even (c-b)" 
    with a2factor have "2 dvd a^2" by (simp only: dvd_mult2)
    with p2 have "2 dvd a" by auto
    with aodd show False by simp
  next
    assume "even (c+b)"
    with a2factor have "2 dvd a^2" by (simp only: dvd_mult)
    with p2 have "2 dvd a" by auto
    with aodd show False by simp
  qed
  have cb1: "c-b + (c+b) = 2*c" 
  proof -
    have "c-b + (c+b) = ((c-b)+b)+c" by simp
    also with b_less_c have "\<dots> = (c+b-b)+c" by (simp only: diff_add_assoc2)
    also have "\<dots> = c+c" by simp
    finally show ?thesis by simp
  qed
  have cb2: "2*b + (c-b) = c+b"
  proof -
    have "2*b + (c-b) = b+b + (c - b)" by auto
    also have "\<dots> = b + ((c-b)+b)" by simp
    also with b_less_c have " \<dots> = b + (c+b-b)" by (simp only: diff_add_assoc2)
    finally show ?thesis by simp
  qed
  have factors_relprime: "coprime (c-b) (c+b)"
  proof -
    let ?g = "gcd (c-b) (c+b)"
    have cb1: "c-b + (c+b) = 2*c"
    proof -
      have "c-b + (c+b) = ((c-b)+b)+c" by simp
      also with b_less_c have "\<dots> = (c+b-b)+c" by (simp only: diff_add_assoc2)
      also have "\<dots> = c+c" by simp
      finally show ?thesis by simp
    qed
    have "?g = gcd (c-b + (c+b)) (c+b)" by simp
    with cb1 have "?g = gcd (2*c) (c+b)" by (rule_tac a="c-b + (c+b)" in back_subst)
    hence g2c: "?g dvd 2*c" by (simp only: gcd_dvd1)
    have "gcd (c-b) (2*b + (c-b)) = gcd (c-b) (2*b)"
      using gcd_add2[of "c - b" "2*b + (c - b)"] by (simp add: algebra_simps)
    with cb2 have "?g = gcd (c-b) (2*b)" by (rule_tac a="2*b + (c-b)" in back_subst)
    hence g2b: "?g dvd 2*b" by (simp only: gcd_dvd2)
    with g2c have "?g dvd 2 * gcd b c" by (simp only: gcd_greatest gcd_mult_distrib_nat)
    with bc_relprime have "?g dvd 2" by simp
    moreover have "?g \<noteq> 0"
      using b_less_c by auto
    ultimately have "1 \<le> ?g" "?g \<le> 2"
      by (simp_all add: dvd_imp_le)
    then have g1or2: "?g = 2 \<or> ?g = 1"
      by arith
    moreover have "?g \<noteq> 2"
    proof
      assume "?g = 2"
      moreover have "?g dvd c - b"
        by simp
      ultimately show False
        using factors_odd by simp
    qed 
    ultimately show ?thesis
      by (auto intro: gcd_eq_1_imp_coprime)
  qed
  from a2factor have "(c-b)*(c+b) = a^2" and "(2::nat) >1"  by auto
  with factors_relprime have "\<exists> k. c-b = k^2"
    by (simp only: nat_relprime_power_divisors)
  then obtain r where r: "c-b = r^2" by auto
  from a2factor have "(c+b)*(c-b) = a^2" and "(2::nat) >1"  by auto
  with factors_relprime have "\<exists> k. c+b = k^2"
    by (simp only: nat_relprime_power_divisors ac_simps)
  then obtain s where s: "c+b = s^2" by auto
  \<comment> \<open>now $p := (s+r)/2$ and $q := (s-r)/2$ is our solution\<close>
  have rs_odd: "odd r \<and> odd s"
  proof (auto dest: ccontr)
    assume "even r" hence "2 dvd r"by presburger
    with r have  "2 dvd (c-b)" by (simp only: power2_eq_square dvd_mult)
    with factors_odd show False by auto
  next
    assume "even s" hence "2 dvd s" by presburger
    with s have "2 dvd (c+b)" by (simp only: power2_eq_square dvd_mult)
    with factors_odd show False by auto
  qed
  obtain m where m: "m = s-r" by simp
  from r s have "r^2 \<le> s^2" by arith
  with two0 have "r \<le> s" by (rule_tac n="2" in nat_power_le_imp_le_base)
  with m have m2: "s = r + m" by simp
  have "even m" 
  proof (rule ccontr)
    assume "odd m" with rs_odd and m2 show False by presburger 
  qed
  then obtain q where "m = 2*q" ..
  with m2 have q: "s = r + 2*q" by simp
  obtain p where p: "p = r+q" by simp
  have c: "c = p^2 + q^2"
  proof -
    from cb1 and r and s have "2*c = r^2 + s^2" by simp
    also with q have "\<dots> = 2*r^2+(2*q)^2+2*r*(2*q)" by algebra
    also have "\<dots> = 2*r^2+2^2*q^2+2*2*q*r" by (simp add: power_mult_distrib)
    also have "\<dots> = 2*(r^2+2*q*r+q^2)+2*q^2" by (simp add: power2_eq_square)
    also with p have "\<dots> = 2*p^2+2*q^2" by algebra
    finally show ?thesis by auto
  qed
  moreover have b: "b = 2*p*q"
  proof -
    from cb2 and r and s have "2*b = s^2 - r^2" by arith
    also with q have "\<dots> = (2*q)^2 + 2*r*(2*q)" by (simp add: power2_sum)
    also with p have "\<dots> = 4*q*p" by (simp add: power2_eq_square add_mult_distrib2)
    finally show ?thesis by auto
  qed
  moreover have a: "a = p^2 - q^2"
  proof -
    from p have "p\<ge>q" by simp
    hence p2_ge_q2: "p^2 \<ge> q^2" by (simp only: power_mono)
    from a2cb and b and c have "a^2 = (p^2 + q^2)^2 - (2*p*q)^2" by simp
    also have "\<dots> = (p^2)^2 + (q^2)^2 - 2*(p^2)*(q^2)" 
      by (auto simp add: power2_sum power_mult_distrib ac_simps)
    also with p2_ge_q2 have "\<dots> = (p^2 - q^2)^2" by (simp only: nat_power2_diff)
    finally have "a^2 = (p^2 - q^2)^2" by simp
    with two0 show ?thesis by (rule_tac n="2" in nat_power_inject_base)
  qed
  moreover have "coprime p q"
  proof -
    let ?k = "gcd p q"
    have "?k dvd p \<and> ?k dvd q" by simp
    with b and a have "?k dvd a \<and> ?k dvd b" 
      by (simp add: power2_eq_square)
    hence "?k dvd gcd a b" by (simp only: gcd_greatest)
    with ab_relprime show ?thesis
      by (auto intro: gcd_eq_1_imp_coprime)
  qed
  ultimately show ?thesis by auto
qed

text \<open>Now for the case of integers. Based on \textit{nat-euclid-pyth-triples}.\<close>
  
private corollary int_euclid_pyth_triples: "\<lbrakk> coprime (a::int) b; odd a; a^2 + b^2 = c^2 \<rbrakk>
  \<Longrightarrow> \<exists> p q. a = p^2 - q^2 \<and> b = 2*p*q \<and> \<bar>c\<bar> = p^2 + q^2 \<and> coprime p q"
proof -
  assume ab_rel: "coprime a b" and aodd: "odd a" and abc: "a^2 + b^2 = c^2"
  let ?a = "nat\<bar>a\<bar>"
  let ?b = "nat\<bar>b\<bar>"
  let ?c = "nat\<bar>c\<bar>"
  have ab2_pos: "a^2 \<ge> 0 \<and> b^2 \<ge> 0" by simp
  hence "nat(a^2) + nat(b^2) = nat(a^2 + b^2)" by (simp only: nat_add_distrib)
  with abc have "nat(a^2) + nat(b^2) = nat(c^2)" by presburger
  hence "nat(\<bar>a\<bar>^2) + nat(\<bar>b\<bar>^2) = nat(\<bar>c\<bar>^2)" by simp
  hence new_abc: "?a^2 + ?b^2 = ?c^2"
    by (simp only: nat_mult_distrib power2_eq_square nat_add_distrib)
  moreover from ab_rel have new_ab_rel: "coprime ?a ?b"
    by (simp add: gcd_int_def)
  moreover have new_a_odd: "odd ?a" using aodd
    by simp
  ultimately have 
    "\<exists> p q. ?a = p^2-q^2 \<and> ?b = 2*p*q \<and> ?c = p^2 + q^2 \<and> coprime p q" 
    by (rule_tac a="?a" and b = "?b" and c="?c" in nat_euclid_pyth_triples)
  then obtain m and n where mn: 
    "?a = m^2-n^2 \<and> ?b = 2*m*n \<and> ?c = m^2 + n^2 \<and> coprime m n" by auto
  have "n^2 \<le> m^2"
  proof (rule ccontr)
    assume "\<not> n^2 \<le> m^2" hence "n^2 > m^2" by simp 
    with mn have "?a = 0" by simp
    with new_a_odd show False by simp
  qed
  moreover from mn have "int ?a = int(m^2 - n^2)" and "int ?b = int(2*m*n)" 
    and "int ?c = int(m^2 + n^2)" by auto
  ultimately have "\<bar>a\<bar> = int(m^2) - int(n^2)" and "\<bar>b\<bar> = int(2*m*n)"
    and "\<bar>c\<bar> = int(m^2) + int(n^2)" by (simp add: of_nat_diff)+
  hence absabc: "\<bar>a\<bar> = (int m)^2 - (int n)^2 \<and> \<bar>b\<bar> = 2*(int m)*int n
    \<and> \<bar>c\<bar> = (int m)^2 + (int n)^2" by (simp add: power2_eq_square)
  from mn have mn_rel: "coprime (int m) (int n)"
    by (simp add: gcd_int_def)
  show "\<exists> p q. a = p^2 - q^2 \<and> b = 2*p*q \<and> \<bar>c\<bar> = p^2 + q^2 \<and> coprime p q" 
    (is "\<exists> p q. ?Q p q")
  proof (cases)
    assume apos: "a \<ge> 0" then obtain p where p: "p = int m" by simp
    hence "\<exists> q. ?Q p q"
    proof (cases)
      assume bpos: "b \<ge> 0" then obtain q where "q = int n" by simp
      with p apos bpos absabc mn_rel have "?Q p q" by simp
      thus ?thesis by (rule exI)
    next
      assume "\<not> b\<ge>0" hence bneg: "b<0" by simp 
      then obtain q where "q = - int n" by simp
      with p apos bneg absabc mn_rel have "?Q p q" by simp
      thus ?thesis by (rule exI)
    qed
    thus ?thesis by (simp only: exI)
  next
    assume "\<not> a\<ge>0" hence aneg: "a<0" by simp 
    then obtain p where p: "p = int n" by simp
    hence "\<exists> q. ?Q p q"
    proof (cases)
      assume bpos: "b \<ge> 0" then obtain q where "q = int m" by simp
      with p aneg bpos absabc mn_rel have "?Q p q"
        by (simp add: ac_simps)
      thus ?thesis by (rule exI)
    next
      assume "\<not> b\<ge>0" hence bneg: "b<0" by simp 
      then obtain q where "q = - int m" by simp
      with p aneg bneg absabc mn_rel have "?Q p q" 
        by (simp add: ac_simps)
      thus ?thesis by (rule exI)
    qed
    thus ?thesis by (simp only: exI)
  qed
qed

subsection \<open>Fermat's last theorem, case $n=4$\<close>

text \<open>Core of the proof. Constructs a smaller solution over $\mathbb{Z}$ of $$a^4+b^4=c^2\,\land\,coprime\,a\,b\,\land\,abc\ne 0\,\land\,a~{\rm odd}.$$\<close>

private lemma smaller_fermat4:
  assumes abc: "(a::int)^4+b^4=c^2" and abc0: "a*b*c \<noteq> 0" and aodd: "odd a" 
    and ab_relprime: "coprime a b"
  shows 
  "\<exists> p q r. (p^4+q^4=r^2 \<and> p*q*r \<noteq> 0 \<and> odd p \<and> coprime p q \<and> r^2 < c^2)"
proof - 
  \<comment> \<open>put equation in shape of a pythagorean triple and obtain $u$ and $v$\<close>
  from ab_relprime have a2b2relprime: "coprime (a^2) (b^2)"
    by simp
  moreover from aodd have "odd (a^2)" by presburger
  moreover from abc have "(a^2)^2 + (b^2)^2 = c^2" by simp
  ultimately obtain u and v where uvabc: 
    "a^2 = u^2-v^2 \<and> b^2 = 2*u*v \<and> \<bar>c\<bar> = u^2 + v^2 \<and> coprime u v" 
    by (frule_tac a="a^2" in int_euclid_pyth_triples, auto)
  with abc0 have uv0: "u\<noteq>0 \<and> v\<noteq>0" by auto
  have av_relprime: "coprime a v" 
  proof -
    have "gcd a v dvd gcd (a^2) v" by (simp add: power2_eq_square)
    moreover from uvabc have "gcd v (a^2) dvd gcd (b^2) (a^2)"
      by simp
    with a2b2relprime have "gcd (a^2) v dvd (1::int)"
      by (simp add: ac_simps)
    ultimately have "gcd a v dvd 1"
      by (rule dvd_trans)
    then show ?thesis
      by (simp add: gcd_eq_1_imp_coprime)
  qed
  \<comment> \<open>make again a pythagorean triple and obtain $k$ and $l$\<close>
  from uvabc have "a^2 + v^2 = u^2" by simp
  with av_relprime and aodd obtain k l where 
    klavu: "a = k^2-l^2 \<and> v = 2*k*l \<and> \<bar>u\<bar> = k^2+l^2" and kl_rel: "coprime k l" 
    by (frule_tac a="a" in int_euclid_pyth_triples, auto)
  \<comment> \<open>prove $b=2m$ and $kl(k^2 + l^2) = m^2$, for coprime $k$, $l$ and $k^2+l^2$\<close>
  from uvabc have "even (b^2)" by simp
  hence "even b" by simp
  then obtain m where bm: "b = 2*m" using evenE by blast
  have "\<bar>k\<bar>*\<bar>l\<bar>*\<bar>k^2+l^2\<bar> = m^2"
  proof -  
    from bm have "4*m^2 = b^2" by (simp only: power2_eq_square ac_simps)
    also have "\<dots> = \<bar>b^2\<bar>" by simp
    also with uvabc have "\<dots> = 2*\<bar>v\<bar>*\<bar>\<bar>u\<bar>\<bar>" by (simp add: abs_mult)
    also with klavu have "\<dots> = 2*\<bar>2*k*l\<bar>*\<bar>k^2+l^2\<bar>" by simp
    also have "\<dots> = 4*\<bar>k\<bar>*\<bar>l\<bar>*\<bar>k^2+l^2\<bar>" by (auto simp add: abs_mult)
    finally show ?thesis by simp
  qed
  moreover have "(2::nat) > 1" by auto
  moreover from kl_rel have "coprime \<bar>k\<bar> \<bar>l\<bar>" by simp
  moreover have "coprime \<bar>l\<bar> (\<bar>k^2+l^2\<bar>)"
  proof -
    from kl_rel have "coprime (k*k) l"
      by simp
    hence "coprime (k*k+l*l) l" using gcd_add_mult [of l l "k*k"]
      by (simp add: ac_simps gcd_eq_1_imp_coprime)
    hence "coprime l (k^2+l^2)"
      by (simp add: power2_eq_square ac_simps)
    thus ?thesis by simp
  qed
  moreover have "coprime \<bar>k^2+l^2\<bar> \<bar>k\<bar>"
  proof -
    from kl_rel have "coprime l k"
      by (simp add: ac_simps)
    hence "coprime (l*l) k"
      by simp
    hence "coprime (l*l+k*k) k" using gcd_add_mult[of k k "l*l"]
      by (simp add: ac_simps gcd_eq_1_imp_coprime)
    hence "coprime (k^2+l^2) k"
      by (simp add: power2_eq_square ac_simps)
    thus ?thesis by simp
  qed
  ultimately have "\<exists> x y z. \<bar>k\<bar> = x^2 \<and> \<bar>l\<bar> = y^2 \<and> \<bar>k^2+l^2\<bar> = z^2"
    using int_relprime_power_divisors[of 2 "\<bar>k\<bar>" "\<bar>l\<bar> * \<bar>k\<^sup>2 + l\<^sup>2\<bar>" m]
      int_relprime_power_divisors[of 2 "\<bar>l\<bar>" "\<bar>k\<bar> * \<bar>k\<^sup>2 + l\<^sup>2\<bar>" m]
      int_relprime_power_divisors[of 2 "\<bar>k\<^sup>2 + l\<^sup>2\<bar>" "\<bar>k\<bar>*\<bar>l\<bar>" m]
    by (simp_all add: ac_simps)
  then obtain \<alpha> \<beta> \<gamma> where albega: 
    "\<bar>k\<bar> = \<alpha>^2 \<and> \<bar>l\<bar> = \<beta>^2 \<and> \<bar>k^2+l^2\<bar> = \<gamma>^2" 
    by auto
  \<comment> \<open>show this is a new solution\<close>
  have "k^2 = \<alpha>^4"
  proof -
    from albega have "\<bar>k\<bar>^2 = (\<alpha>^2)^2" by simp
    thus ?thesis by simp
  qed
  moreover have "l^2 = \<beta>^4"
  proof -
    from albega have "\<bar>l\<bar>^2 = (\<beta>^2)^2" by simp
    thus ?thesis by simp
  qed
  moreover have gamma2: "k^2 + l^2 = \<gamma>^2"
  proof -
    have "k^2 \<ge> 0 \<and> l^2 \<ge> 0" by simp
    with albega show ?thesis by auto
  qed
  ultimately have newabc: "\<alpha>^4 + \<beta>^4 = \<gamma>^2" by auto 
  from uv0 klavu albega have albega0: "\<alpha> * \<beta> * \<gamma>  \<noteq> 0" by auto
  \<comment> \<open>show the coprimality\<close>
  have alphabeta_relprime: "coprime \<alpha> \<beta>"
  proof (rule classical)
    let ?g = "gcd \<alpha> \<beta>"
    assume "\<not> coprime \<alpha> \<beta>"
    then have gnot1: "?g \<noteq> 1"
      by (auto intro: gcd_eq_1_imp_coprime)
    have "?g > 1"
    proof -
      have "?g \<noteq> 0"
      proof
        assume "?g=0"
        hence "nat \<bar>\<alpha>\<bar>=0" by simp
        hence "\<alpha>=0" by arith
        with albega0 show False by simp
      qed
      hence "?g>0" by auto
      with gnot1 show ?thesis by linarith
    qed
    moreover have "?g dvd gcd k l"
    proof -
      have "?g dvd \<alpha> \<and> ?g dvd \<beta>" by auto
      with albega have "?g dvd \<bar>k\<bar> \<and> ?g dvd \<bar>l\<bar>" 
        by (simp add: power2_eq_square mult.commute)
      hence "?g dvd k \<and> ?g dvd l" by simp
      thus ?thesis by simp
    qed
    ultimately have "gcd k l \<noteq> 1" by fastforce
    with kl_rel show ?thesis by auto
  qed
  \<comment> \<open>choose $p$ and $q$ in the right way\<close>
  have "\<exists> p q. p^4 + q^4 = \<gamma>^2 \<and> p*q*\<gamma> \<noteq> 0 \<and> odd p \<and> coprime p q"
  proof -
    have "odd \<alpha> \<or> odd \<beta>"      
    proof (rule ccontr)
      assume "\<not> (odd \<alpha> \<or> odd \<beta>)" 
      hence "even \<alpha> \<and> even \<beta>" by simp
      then have "2 dvd \<alpha> \<and> 2 dvd \<beta>" by simp
      then have "2 dvd gcd \<alpha> \<beta>" by simp
      with alphabeta_relprime show False by auto
    qed
    moreover
    { assume "odd \<alpha>"
      with newabc albega0 alphabeta_relprime obtain p q where 
        "p=\<alpha> \<and> q=\<beta> \<and> p^4 + q^4 = \<gamma>^2 \<and> p*q*\<gamma>  \<noteq> 0 \<and> odd p \<and> coprime p q" 
        by auto
      hence ?thesis by auto }
    moreover
    { assume "odd \<beta>"
      with newabc albega0 alphabeta_relprime obtain p q where 
        "q=\<alpha> \<and> p=\<beta> \<and> p^4 + q^4 = \<gamma>^2 \<and> p*q*\<gamma>  \<noteq> 0 \<and> odd p \<and> coprime p q" 
        by (auto simp add: ac_simps)
      hence ?thesis by auto }
    ultimately show ?thesis by auto
  qed
  \<comment> \<open>show the solution is smaller\<close>
  moreover have "\<gamma>^2 < c^2"
  proof -
    from gamma2 klavu have "\<gamma>^2 \<le> \<bar>u\<bar>" by simp
    also have h1: "\<dots> \<le> \<bar>u\<bar>^2" using self_le_power[of "\<bar>u\<bar>" 2] uv0 by auto
    also have h2: "\<dots> \<le> u^2" by simp
    also have h3: "\<dots> < u^2 + v^2" 
    proof -
      from uv0 have v2non0: "0 \<noteq> v^2" 
        by simp
      have "0 \<le> v^2" by (rule zero_le_power2)
      with v2non0 have "0 < v^2" by (auto simp add: less_le)
      thus ?thesis by auto
    qed
    also with uvabc have "\<dots> \<le> \<bar>c\<bar>" by auto
    also have "\<dots> \<le> \<bar>c\<bar>^2" using self_le_power[of "\<bar>c\<bar>" 2] h1 h2 h3 uvabc by linarith
    also have "\<dots> \<le> c^2" by simp
    finally show ?thesis by simp
  qed
  ultimately show ?thesis by auto
qed

text \<open>Show that no solution exists, by infinite descent of $c^2$.\<close>

private lemma no_rewritten_fermat4:
  "\<not> (\<exists> (a::int) b. (a^4 + b^4 = c^2 \<and> a*b*c \<noteq> 0 \<and> odd a \<and> coprime a b))"
proof (induct c rule: infinite_descent0_measure[where V="\<lambda>c. nat(c^2)"])
  case (0 x)
  have "x^2 \<ge> 0" by (rule zero_le_power2)
  with 0 have "int(nat(x^2)) = 0" by auto
  hence "x = 0" by auto
  thus ?case by auto
next
  case (smaller x)
  then obtain a b where "a^4 + b^4 = x^2" and "a*b*x \<noteq> 0" 
    and "odd a" and "coprime a b" by auto
  hence "\<exists> p q r. (p^4+q^4=r^2 \<and> p*q*r \<noteq> 0 \<and> odd p
    \<and> coprime p q \<and> r^2 < x^2)" by (rule smaller_fermat4)
  then obtain p q r where pqr: "p^4 + q^4 = r^2 \<and> p*q*r \<noteq> 0 \<and> odd p
    \<and> coprime p q \<and> r^2 < x^2" by auto
  have "r^2 \<ge> 0" and "x^2 \<ge> 0" by (auto simp only: zero_le_power2)
  hence "int(nat(r^2)) = r^2 \<and> int(nat(x^2)) = x^2" by auto
  with pqr have "int(nat(r^2)) < int(nat(x^2))" by auto
  hence "nat(r^2) < nat(x^2)" by presburger
  with pqr show ?case by auto
qed

text \<open>The theorem. Puts equation in requested shape.\<close>

theorem fermat_4:
  assumes ass: "(x::int)^4 + y^4 = z^4"
  shows "x*y*z=0"
proof (rule ccontr)
  let ?g = "gcd x y"
  let ?c = "(z div ?g)^2"
  assume xyz0: "x*y*z \<noteq> 0"
  \<comment> \<open>divide out the g.c.d.\<close>
  hence "x \<noteq> 0 \<or> y \<noteq> 0" by simp
  then obtain a b where ab: "x = ?g*a \<and> y = ?g*b \<and> coprime a b"
     using gcd_coprime_exists[of x y] by (auto simp: mult.commute)
  moreover have abc: "a^4 + b^4 = ?c^2 \<and> a*b*?c \<noteq> 0"
  proof -
    have zgab: "z^4 = ?g^4 * (a^4+b^4)"
    proof -
      from ab ass have "z^4 = (?g*a)^4+(?g*b)^4" by simp
      thus ?thesis by (simp only: power_mult_distrib distrib_left)
    qed
    have cgz: "z^2 = ?c * ?g^2" 
    proof -
      from zgab have "?g^4 dvd z^4" by simp
      hence "?g dvd z" by simp
      hence "(z div ?g)*?g = z" by (simp only: ac_simps dvd_mult_div_cancel)
      with ab show ?thesis by (auto simp only: power2_eq_square ac_simps)
    qed
    with xyz0 have c0: "?c\<noteq>0" by (auto simp add: power2_eq_square)
    from xyz0 have g0: "?g\<noteq>0" by simp
    have "a^4 + b^4 = ?c^2"
    proof -
      have "?c^2 * ?g^4 = (a^4+b^4)*?g^4"
      proof -
        have "?c^2 * ?g^4 = (?c*?g^2)^2" by algebra
        also with cgz have "\<dots> = (z^2)^2" by simp
        also have "\<dots> = z^4" by algebra
        also with zgab have "\<dots> = ?g^4*(a^4+b^4)" by simp
        finally show ?thesis by simp
      qed
      with g0 show ?thesis by auto
    qed
    moreover from ab xyz0 c0 have "a*b*?c\<noteq>0" by auto
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>choose the parity right\<close>
  have "\<exists> p q. p^4 + q^4 = ?c^2 \<and> p*q*?c\<noteq>0 \<and> odd p \<and> coprime p q"
  proof -
    have "odd a \<or> odd b"
    proof (rule ccontr)
      assume "\<not>(odd a \<or> odd b)"
      hence "2 dvd a \<and> 2 dvd b" by simp
      hence "2 dvd gcd a b" by simp
      with ab show False by auto
    qed
    moreover
    { assume "odd a"
      then obtain p q where "p = a" and "q = b" and "odd p" by simp
      with ab abc have ?thesis by auto }
    moreover 
    { assume "odd b"
      then obtain p q where "p = b" and "q = a" and "odd p" by simp    
      with ab abc have 
        "p^4 + q^4 = ?c^2 \<and> p*q*?c\<noteq>0 \<and> odd p \<and> coprime p q"
        by (simp add: ac_simps)
      hence ?thesis by auto }
    ultimately show ?thesis by auto
  qed
  \<comment> \<open>show contradiction using the earlier result\<close>
  thus False by (auto simp only: no_rewritten_fermat4)
qed

corollary fermat_mult4:
  assumes xyz: "(x::int)^n + y^n = z^n" and n: "4 dvd n"
  shows "x*y*z=0"
proof -
  from n obtain m where "n = m*4" by (auto simp only: ac_simps dvd_def)
  with xyz have "(x^m)^4 + (y^m)^4 = (z^m)^4" by (simp only: power_mult)
  hence "(x^m)*(y^m)*(z^m) = 0" by (rule fermat_4)
  thus ?thesis by auto
qed

end

end
