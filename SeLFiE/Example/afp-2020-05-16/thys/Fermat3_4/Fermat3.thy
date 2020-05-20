(*  Title:      Fermat3.thy
    Author:     Roelof Oosterhuis, 2007  Rijksuniversiteit Groningen
*)

section \<open>Fermat's last theorem, case $n=3$\<close>

theory Fermat3
imports Quad_Form
begin

context
begin

text \<open>Proof of Fermat's last theorem for the case $n=3$: $$\forall x,y,z:~x^3 + y^3 = z^3 \Longrightarrow xyz=0.$$\<close>

(* TODO: this lemma is also used in Fermat4 with a slightly different generalization to ints.
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
    thus ?thesis using n0 power_one zero_power  by (simp only: eq_sym_conv) blast
  next
  case True
    then obtain p where p: "prime p" "p dvd a" using prime_factor_nat[of a] by blast
    hence h1: "p dvd (c^n)" using 1(3) dvd_mult2[of p a b] by presburger
    hence "(p^n) dvd (c^n)"
      using p(1) prime_dvd_power_nat[of p c n] dvd_power_same[of p c n] by blast
    moreover have h2: "\<not> p dvd b"
      using p \<open>coprime a b\<close> coprime_common_divisor_nat [of a b p] by auto
    hence "\<not> (p^n) dvd b" using n0 p(1)  dvd_power[of n p] gcd_nat.trans by blast
    ultimately have "(p^n) dvd a"
      using "1.prems" p(1) prime_elem_divprod_pow [of p a b n] by simp
    then obtain a' c' where ac: "a = p^n * a'" "c = p * c'"
      using h1 dvdE[of "p^n" a] dvdE[of p c] prime_dvd_power_nat[of p c n] p(1) by meson
    hence "p^n * (a' * b) = p^n * c'^n" using 1(3)
      by (simp add: power_mult_distrib semiring_normalization_rules(18))
    hence "a' * b = c'^n" using p(1) by auto
    moreover have "coprime a' b" using 1(4) ac(1)
      by simp
    moreover have "0 < b" "0 < a" using h2 dvd_0_right gr0I True by fastforce+
    then have "0 < c" "1 < p" using p(1) 1(3) nat_0_less_mult_iff [of a b] n0 prime_gt_Suc_0_nat
      by simp_all
    hence "c' < c" using ac(2) by simp
    ultimately obtain k where "a' = k^n" using 1(1) n0 by presburger
    hence "a = (p*k)^n" using ac(1) by (simp add: power_mult_distrib)
    thus ?thesis by blast
  qed
qed

private lemma int_relprime_odd_power_divisors:
  assumes "odd n" and "(a::int) * b = c ^ n" and "coprime a b"
  shows "\<exists>k. a = k^n" 
proof -
  from assms have "\<bar>a\<bar> * \<bar>b\<bar> = \<bar>c\<bar> ^ n"
    by (simp add: abs_mult [symmetric] power_abs)
  then have "nat \<bar>a\<bar> * nat \<bar>b\<bar> = nat \<bar>c\<bar> ^ n"
    by (simp add: nat_mult_distrib [of "\<bar>a\<bar>" "\<bar>b\<bar>", symmetric] nat_power_eq)
  moreover have "coprime (nat \<bar>a\<bar>) (nat \<bar>b\<bar>)" using assms(3) gcd_int_def by fastforce
  ultimately have "\<exists> k. nat \<bar>a\<bar> = k^n"
    using nat_relprime_power_divisors[of n "nat \<bar>a\<bar>" "nat \<bar>b\<bar>" "nat \<bar>c\<bar>"] assms(1) by blast
  then obtain k' where k': "nat \<bar>a\<bar> = k'^n" by blast
  moreover define k where "k = int k'"
  ultimately have k: "\<bar>a\<bar> = k^n" using int_nat_eq[of "\<bar>a\<bar>"] of_nat_power[of k' n] by force
  { assume "a \<noteq> k^n"
    with k have "a = -(k^n)" by arith
    hence "a = (-k)^n" using assms(1) power_minus_odd by simp }
  thus ?thesis by blast
qed

private lemma factor_sum_cubes: "(x::int)^3 + y^3 = (x+y)*(x^2 - x*y + y^2)"
  by (simp add: eval_nat_numeral field_simps)

private lemma two_not_abs_cube: "\<bar>x^3\<bar> = (2::int) \<Longrightarrow> False"
proof -
  assume "\<bar>x^3\<bar> = 2"
  hence x32: "\<bar>x\<bar>^3 = 2" by (simp add: power_abs)
  have "\<bar>x\<bar> \<ge> 0" by simp
  moreover 
  { assume "\<bar>x\<bar> = 0 \<or> \<bar>x\<bar> = 1 \<or> \<bar>x\<bar> = 2"
    with x32 have False by (auto simp add: power_0_left) }
  moreover
  { assume "\<bar>x\<bar> > 2"
    moreover have "(0::int) \<le> 2" and "(0::nat) < 3" by auto
    ultimately have "\<bar>x\<bar>^3 > 2^3" by (simp only: power_strict_mono) 
    with x32 have False by simp }
  ultimately show False by arith
qed

text \<open>Shows there exists no solution $v^3+w^3 = x^3$ with $vwx\ne 0$ and $coprime v w$ and $x$ even, by constructing a solution with a smaller $|x^3|$.\<close>

private lemma no_rewritten_fermat3: 
  "\<not> (\<exists> v w. v^3+w^3 = x^3 \<and> v*w*x \<noteq> 0 \<and> even (x::int) \<and> coprime v w)"
proof (induct x rule: infinite_descent0_measure[where V="\<lambda>x. nat\<bar>x^3\<bar>"])
  case (0 x) hence "x^3 = 0" by arith
  hence "x=0" by auto
  thus ?case by auto
next
  case (smaller x)
  then obtain v w where vwx: 
    "v^3+w^3=x^3 \<and> v*w*x \<noteq> 0 \<and> even x \<and> coprime v w" (is "?P v w x")
    by auto
  then have "coprime v w"
    by simp
  have "\<exists> \<alpha> \<beta> \<gamma>. ?P \<alpha> \<beta> \<gamma> \<and> nat\<bar>\<gamma>^3\<bar> < nat\<bar>x^3\<bar>"
  proof -
    \<comment> \<open>obtain coprime $p$ and $q$ such that $v = p+q$ and $w = p-q$\<close>
    have vwOdd: "odd v \<and> odd w"
    proof (rule ccontr, case_tac "odd v", simp_all)
      assume ve: "even v"
      hence "even (v^3)" by simp
      moreover from vwx have "even (x^3)" by simp
      ultimately have "even (x^3-v^3)" by simp
      moreover from vwx have "x^3-v^3 = w^3" by simp
      ultimately have "even (w^3)" by simp
      hence "even w" by simp
      with ve have "2 dvd v \<and> 2 dvd w" by auto
      hence "2 dvd gcd v w" by simp
      with vwx show False by simp
    next
      assume "odd v" and "even w"
      hence "odd (v^3)" and "even (w^3)" 
        by auto
      hence "odd (w^3 + v^3)" by simp
      with vwx have "odd (x^3)" by (simp add: add.commute)
      hence "odd x" by simp
      with vwx show False by auto
    qed
    hence "even (v+w) \<and> even (v-w)" by simp
    then obtain p q where pq: "v+w = 2*p \<and> v-w = 2*q"
      using evenE[of "v+w"] evenE[of "v-w"] by meson
    hence vw: "v = p+q \<and> w = p-q" by auto
    \<comment> \<open>show that $x^3 = (2p)(p^2 + 3q^2)$ and that these factors are\<close>
    \<comment> \<open>either coprime (first case), or have $3$ as g.c.d. (second case)\<close>
    have vwpq: "v^3 + w^3 = (2*p)*(p^2 + 3*q^2)"
    proof -
      have "2*(v^3 + w^3) = 2*(v+w)*(v^2 - v*w + w^2)" 
        by (simp only: factor_sum_cubes)
      also from pq have "\<dots> = 4*p*(v^2 - v*w + w^2)" by auto
      also have "\<dots> = p*((v+w)^2 + 3*(v-w)^2)" 
        by (simp add: eval_nat_numeral field_simps)
      also with pq have "\<dots> = p*((2*p)^2 + 3*(2*q)^2)" by simp
      also have "\<dots> = 2*(2*p)*(p^2+3*q^2)" by (simp add: power_mult_distrib)
      finally show ?thesis by simp
    qed
    let ?g = "gcd (2 * p) (p\<^sup>2 + 3 * q\<^sup>2)"
    have g1: "?g \<ge> 1" 
    proof (rule ccontr)
      assume "\<not> ?g \<ge> 1"
      then have "?g < 0 \<or> ?g = 0" unfolding not_le by arith
      moreover have "?g \<ge> 0" by simp
      ultimately have "?g = 0" by arith
      hence "p = 0" by simp
      with vwpq vwx \<open>0 < nat\<bar>x^3\<bar>\<close> show False by auto
    qed
    have gOdd: "odd ?g"
    proof (rule ccontr)
      assume "\<not> odd ?g"
      hence"2 dvd p^2+3*q^2" by simp
      then obtain k where k: "p^2 + 3*q^2 = 2*k" by (auto simp add: dvd_def)
      hence "2*(k - 2*q^2) = p^2-q^2" by auto
      also have "\<dots> = (p+q)*(p-q)" by (simp add: power2_eq_square algebra_simps)
      finally have "v*w = 2*(k - 2*q^2)" using vw by presburger
      hence "even (v*w)" by auto
      hence "even (v) \<or> even (w)" by simp
      with vwOdd show False by simp
    qed
    then have even_odd_p_q: "even p \<and> odd q \<or> odd p \<and> even q"
      by auto
    \<comment> \<open>first case: $p$ is not a multiple of $3$; hence $2p$ and $p^2+3q^2$\<close>
    \<comment> \<open>are coprime; hence both are cubes\<close>
    { assume p3: "\<not> 3 dvd p"
      have g3: "\<not> 3 dvd ?g"
      proof (rule ccontr)
        assume "\<not> \<not> 3 dvd ?g" hence "3 dvd 2*p" by simp
        hence "(3::int) dvd 2 \<or> 3 dvd p"
          using prime_dvd_multD[of 3] by (fastforce simp add: prime_dvd_mult_iff)
        with p3 show False by arith
      qed
      from \<open>coprime v w\<close> have pq_relprime: "coprime p q"
      proof (rule coprime_imp_coprime)
        fix c
        assume "c dvd p" and "c dvd q"
        then have "c dvd p + q" and "c dvd p - q"
          by simp_all
        with vw show "c dvd v" and "c dvd w"
          by simp_all
      qed
      from \<open>coprime p q\<close> have "coprime p (q\<^sup>2)"
        by simp
      then have factors_relprime: "coprime (2 * p) (p\<^sup>2 + 3 * q\<^sup>2)" 
      proof (rule coprime_imp_coprime)
        fix c
        assume g2p: "c dvd 2 * p" and gpq: "c dvd p\<^sup>2 + 3 * q\<^sup>2"
        have "coprime 2 c"
          using g2p gpq even_odd_p_q dvd_trans [of 2 c "p\<^sup>2 + 3 * q\<^sup>2"]
          by auto
        with g2p show "c dvd p"
          by (simp add: coprime_dvd_mult_left_iff ac_simps)
        then have "c dvd p\<^sup>2"
          by (simp add: power2_eq_square)
        with gpq have "c dvd 3 * q\<^sup>2"
          by (simp add: dvd_add_right_iff)
        moreover have "coprime 3 c"
          using \<open>c dvd p\<close> p3 dvd_trans [of 3 c p]
          by (auto intro: prime_imp_coprime)
        ultimately show "c dvd q\<^sup>2"
          by (simp add: coprime_dvd_mult_right_iff ac_simps)
      qed
      moreover from vwx vwpq have pqx: "(2*p)*(p^2 + 3*q^2) = x^3" by auto
      ultimately have "\<exists> c. 2*p = c^3" by (simp add: int_relprime_odd_power_divisors)
      then obtain c where c: "c^3 = 2*p" by auto
      from pqx factors_relprime have "coprime (p^2 + 3*q^2) (2*p)"
        and "(p^2 + 3*q^2)*(2*p) = x^3" by (auto simp add: ac_simps)
      hence "\<exists> d. p^2 + 3*q^2 = d^3" by (simp add: int_relprime_odd_power_divisors)
      then obtain d where d: "p^2 + 3*q^2 = d^3" by auto
      have "odd d"
      proof (rule ccontr)
        assume "\<not> odd d"
        hence "even (d^3)" by simp
        hence "2 dvd d^3" by simp
        moreover have "2 dvd 2*p" by (rule dvd_triv_left)
        ultimately have "2 dvd gcd (2*p) (d^3)" by simp
        with d factors_relprime show False by simp
      qed
      with d pq_relprime have "coprime p q \<and> p^2 + 3*q^2 = d^3 \<and> odd d"
        by simp
      hence "is_cube_form p q" by (rule qf3_cube_impl_cube_form)
      then obtain a b where "p = a^3 - 9*a*b^2 \<and> q = 3*a^2*b - 3*b^3"
        by (unfold is_cube_form_def, auto)
      hence ab: "p = a*(a+3*b)*(a- 3*b) \<and> q = b*(a+b)*(a-b)*3"
        by (simp add: eval_nat_numeral field_simps)
      with c have abc: "(2*a)*(a+3*b)*(a- 3*b) = c^3" by auto
      from pq_relprime ab have ab_relprime: "coprime a b"
        by (auto intro: coprime_imp_coprime)
      then have ab1: "coprime (2 * a) (a + 3 * b)"
      proof (rule coprime_imp_coprime)
        fix h
        assume h2a: "h dvd 2 * a" and hab: "h dvd a + 3 * b"
        have "coprime 2 h"
          using ab even_odd_p_q hab dvd_trans [of 2 h "a + 3 * b"]
          by auto
        with h2a show "h dvd a"
          by (simp add: coprime_dvd_mult_left_iff ac_simps)
        with hab have "h dvd 3 * b" and "\<not> 3 dvd h"
          using dvd_trans [of 3 h a] ab \<open>\<not> 3 dvd p\<close>
          by (auto simp add: dvd_add_right_iff)
        moreover have "coprime 3 h"
          using \<open>\<not> 3 dvd h\<close> by (auto intro: prime_imp_coprime)
        ultimately show "h dvd b"
          by (simp add: coprime_dvd_mult_left_iff ac_simps)
      qed
      then have [simp]: "even b \<longleftrightarrow> odd a"
        and ab3: "coprime a (a + 3 * b)"
        by simp_all
      from \<open>coprime a b\<close> have ab4: "coprime a (a - 3 * b)"
      proof (rule coprime_imp_coprime)
        fix h
        assume h2a: "h dvd a" and hab: "h dvd a - 3 * b"
        then show "h dvd a"
          by simp
        with hab have "h dvd 3 * b" and "\<not> 3 dvd h"
          using dvd_trans [of 3 h a] ab \<open>\<not> 3 dvd p\<close> dvd_add_right_iff [of h a "- 3 * b"]
          by auto
        moreover have "coprime 3 h"
          using \<open>\<not> 3 dvd h\<close> by (auto intro: prime_imp_coprime)
        ultimately show "h dvd b"
          by (simp add: coprime_dvd_mult_left_iff ac_simps)
      qed
      from ab1 have ab2: "coprime (a + 3 * b) (a - 3 * b)"
        by (rule coprime_imp_coprime)
          (use dvd_add [of _ "a + 3 * b" "a - 3 * b"] in simp_all)
      have "\<exists>k l m. 2 * a = k ^ 3 \<and> a + 3 * b = l ^ 3 \<and> a - 3 * b = m ^ 3"
        using ab2 ab3 ab4 abc
          int_relprime_odd_power_divisors [of 3 "2 * a" "(a + 3 * b) * (a - 3 * b)" c]
          int_relprime_odd_power_divisors [of 3 "(a + 3 * b)" "2 * a * (a - 3 * b)" c]
          int_relprime_odd_power_divisors [of 3 "(a - 3 * b)" "2 * a * (a + 3 * b)" c]
        by auto (auto simp add: ac_simps)
      then obtain \<alpha> \<beta> \<gamma> where albega: 
        "2*a = \<gamma>^3 \<and> a - 3*b = \<alpha>^3 \<and> a+3*b = \<beta>^3" by auto 
      \<comment> \<open>show this is a (smaller) solution\<close>
      hence "\<alpha>^3 + \<beta>^3 = \<gamma>^3" by auto
      moreover have "\<alpha>*\<beta>*\<gamma> \<noteq> 0"
      proof (rule ccontr, safe)
        assume "\<alpha> * \<beta> * \<gamma> = 0"
        with albega ab have "p=0" by (auto simp add: power_0_left)
        with vwpq vwx show False by auto
      qed
      moreover have "even \<gamma>"
      proof -
        have "even (2*a)" by simp
        with albega have "even (\<gamma>^3)" by simp
        thus ?thesis by simp
      qed
      moreover have "coprime \<alpha> \<beta>"
      using ab2 proof (rule coprime_imp_coprime)
        fix h
        assume ha: "h dvd \<alpha>" and hb: "h dvd \<beta>"
        then have "h dvd \<alpha> * \<alpha>^2 \<and> h dvd \<beta> * \<beta>^2" by simp
        then have "h dvd \<alpha>^Suc 2 \<and> h dvd \<beta>^Suc 2" by (auto simp only: power_Suc)
        with albega show "h dvd a - 3 * b" "h dvd a + 3 * b" by auto 
      qed
      moreover have "nat\<bar>\<gamma>^3\<bar> < nat\<bar>x^3\<bar>"
      proof -
        let ?A = "p^2 + 3*q^2"
        from vwx vwpq have "x^3 = 2*p*?A" by auto
        also with ab have "\<dots> = 2*a*((a+3*b)*(a- 3*b)*?A)" by auto
        also with albega have "\<dots> = \<gamma>^3 *((a+3*b)*(a- 3*b)*?A)" by auto
        finally have eq: "\<bar>x^3\<bar> = \<bar>\<gamma>^3\<bar> * \<bar>(a+3*b)*(a- 3*b)*?A\<bar>"
          by (auto simp add: abs_mult)
        with \<open>0 < nat\<bar>x^3\<bar>\<close> have "\<bar>(a+3*b)*(a- 3*b)*?A\<bar> > 0" by auto
        hence eqpos: "\<bar>(a+3*b)*(a- 3*b)\<bar> > 0" by auto
        moreover have Ag1: "\<bar>?A\<bar> > 1"
        proof -
          have Aqf3: "is_qfN ?A 3" by (auto simp add: is_qfN_def)
          moreover have triv3b: "(3::int) \<ge> 1" by simp
          ultimately have "?A \<ge> 0" by (simp only: qfN_pos)
          hence "?A > 1 \<or> ?A = 0 \<or> ?A =1" by arith
          moreover
          { assume "?A = 0" with triv3b have "p = 0 \<and> q = 0" by (rule qfN_zero)
            with vwpq vwx have False by auto }
          moreover 
          { assume A1: "?A = 1" 
            have "q=0"
            proof (rule ccontr)
              assume "q \<noteq> 0"
              hence "q^2 > 0"  by simp
              hence "3*q^2 > 1" by arith
              moreover have "p^2 \<ge> 0" by (rule zero_le_power2)
              ultimately have "?A > 1" by arith
              with A1 show False by simp
            qed
            with pq_relprime have "\<bar>p\<bar> = 1" by simp
            with vwpq vwx A1 have "\<bar>x^3\<bar> = 2" by auto
            hence False by (rule two_not_abs_cube) }
          ultimately show ?thesis by auto
        qed
        ultimately have 
          "\<bar>(a+3*b)*(a- 3*b)\<bar>*1 < \<bar>(a+3*b)*(a- 3*b)\<bar>*\<bar>?A\<bar>"
          by (simp only: zmult_zless_mono2)
        with eqpos have "\<bar>(a+3*b)*(a- 3*b)\<bar>*\<bar>?A\<bar> > 1" by arith
        hence "\<bar>(a+3*b)*(a- 3*b)*?A\<bar> > 1" by (auto simp add: abs_mult)
        moreover have "\<bar>\<gamma>^3\<bar> > 0"
        proof - 
          from eq have "\<bar>\<gamma>^3\<bar> = 0 \<Longrightarrow> \<bar>x^3\<bar>=0" by auto
          with \<open>0 < nat\<bar>x^3\<bar>\<close> show ?thesis by auto
        qed
        ultimately have "\<bar>\<gamma>^3\<bar> * 1 < \<bar>\<gamma>^3\<bar> * \<bar>(a+3*b)*(a- 3*b)*?A\<bar>"
          by (rule zmult_zless_mono2)
        with eq have "\<bar>x^3\<bar> > \<bar>\<gamma>^3\<bar>" by auto
        thus ?thesis by arith
      qed
      ultimately have ?thesis by auto }
    moreover
    \<comment> \<open>second case: $p = 3r$ and hence $x^3 = (18r)(q^2+3r^2)$ and these\<close>
    \<comment> \<open>factors are coprime; hence both are cubes\<close> 
    { assume p3: "3 dvd p"
      then obtain r where r: "p = 3*r" by (auto simp add: dvd_def)
      moreover have "3 dvd 3*(3*r^2 + q^2)" by (rule dvd_triv_left)
      ultimately have pq3: "3 dvd p^2+3*q^2" by (simp add: power_mult_distrib)
      moreover from p3 have "3 dvd 2*p" by (rule dvd_mult)
      ultimately have g3: "3 dvd ?g" by simp
      from \<open>coprime v w\<close> have qr_relprime: "coprime q r" 
      proof (rule coprime_imp_coprime)
        fix h
        assume hq: "h dvd q" "h dvd r"
        with r have "h dvd p" by simp
        with hq have "h dvd p + q" "h dvd p - q"
          by simp_all
        with vw show "h dvd v" "h dvd w"
          by simp_all
      qed
      have factors_relprime: "coprime (18*r) (q^2 + 3*r^2)"
      proof -
        from g3 obtain k where k: "?g = 3*k" by (auto simp add: dvd_def)
        have "k = 1"
        proof (rule ccontr)
          assume "k \<noteq> 1"
          with g1 k have "k > 1" by auto
          then obtain h where h: "prime h \<and> h dvd k"
            using prime_divisor_exists[of k] by auto
          with k have hg: "3*h dvd ?g" by (auto simp add: mult_dvd_mono)
          hence "3*h dvd p^2 + 3*q^2" and hp: "3*h dvd 2*p" by auto
          then obtain s where s: "p^2 + 3*q^2 = (3*h)*s" 
            by (auto simp add: dvd_def)
          with r have rqh: "3*r^2+q^2 = h*s" by (simp add: power_mult_distrib)
          from hp r have "3*h dvd 3*(2*r)" by simp
          moreover have "(3::int) \<noteq> 0" by simp
          ultimately have "h dvd 2*r" by (rule zdvd_mult_cancel)
          with h have "h dvd 2 \<or> h dvd r" 
            by (auto dest: prime_dvd_multD)
          moreover have "\<not> h dvd 2" 
          proof (rule ccontr, simp)
            assume "h dvd 2" 
            with h have "h=2" using zdvd_not_zless[of 2 h] by (auto simp: prime_int_iff)
            with hg have "2*3 dvd ?g" by auto
            hence "2 dvd ?g" by (rule dvd_mult_left)
            with gOdd show False by simp
          qed
          ultimately have hr: "h dvd r" by simp
          then obtain t where "r = h*t" by (auto simp add: dvd_def)
          hence t: "r^2 = h*(h*t^2)" by (auto simp add: power2_eq_square)
          with rqh have "h*s = h*(3*h*t^2) + q^2" by simp
          hence "q^2 = h*(s - 3*h*t^2)" by (simp add: right_diff_distrib)
          hence "h dvd q^2" by simp
          with h have "h dvd q" using prime_dvd_multD[of h q q]
            by (simp add: power2_eq_square)
          with hr have "h dvd gcd q r" by simp
          with h qr_relprime show False by (unfold prime_def, auto)
        qed
        with k r have "3 = gcd (2*(3*r)) ((3*r)^2 + 3*q^2)" by auto
        also have "\<dots> = gcd (3*(2*r)) (3*(3*r^2 + q^2))" 
          by (simp add: power_mult_distrib)
        also have "\<dots> = 3 * gcd (2*r) (3*r^2 + q^2)" using gcd_mult_distrib_int[of 3] by auto
        finally have "coprime (2*r) (3*r^2 + q^2)"
          by (auto dest: gcd_eq_1_imp_coprime)
        moreover have "coprime 9 (3*r^2 + q^2)"
        using \<open>coprime v w\<close> proof (rule coprime_imp_coprime)
          fix h :: int
          assume "\<not> is_unit h"
          assume h9: "h dvd 9" and hrq: "h dvd 3 * r\<^sup>2 + q\<^sup>2"
          have "prime (3::int)"
            by simp
          moreover from \<open>h dvd 9\<close> have "h dvd 3\<^sup>2"
            by simp
          ultimately obtain k where "normalize h = 3 ^ k"
            by (rule divides_primepow)
          with \<open>\<not> is_unit h\<close> have "0 < k"
            by simp
          with \<open>normalize h = 3 ^ k\<close> have "\<bar>h\<bar> = 3 * 3 ^ (k - 1)"
            by (cases k) simp_all
          then have "3 dvd \<bar>h\<bar>" ..
          then have "3 dvd h"
            by simp
          then have "3 dvd 3 * r\<^sup>2 + q\<^sup>2"
            using hrq by (rule dvd_trans)
          then have "3 dvd q\<^sup>2"
            by presburger
          then have "3 dvd q"
            using prime_dvd_power_int [of 3 q 2] by auto
          with p3 have "3 dvd p + q" and "3 dvd p - q"
            by simp_all
          with vw have "3 dvd v" and "3 dvd w"
            by simp_all
          with \<open>coprime v w\<close> have "is_unit (3::int)"
            by (rule coprime_common_divisor)
          then show "h dvd v" and "h dvd w"
            by simp_all
        qed
        ultimately have "coprime (2 * r * 9) (3 * r\<^sup>2 + q\<^sup>2)"
          by (simp only: coprime_mult_left_iff)
        then show ?thesis
          by (simp add: ac_simps)
      qed
      moreover have rqx: "(18*r)*(q^2 + 3*r^2) = x^3"
      proof -
        from vwx vwpq have "x^3 = 2*p*(p^2 + 3*q^2)" by auto
        also with r have "\<dots> = 2*(3*r)*(9*r^2 + 3*q^2)" 
          by (auto simp add: power2_eq_square)
        finally show ?thesis by auto
      qed
      ultimately have "\<exists> c. 18*r = c^3" 
        by (simp add: int_relprime_odd_power_divisors)
      then obtain c1 where c1: "c1^3 = 3*(6*r)" by auto
      hence "3 dvd c1^3" and "prime (3::int)" by auto
      hence "3 dvd c1" using prime_dvd_power[of 3] by fastforce
      with c1 obtain c where c: "3*c^3 = 2*r" 
        by (auto simp add: power_mult_distrib dvd_def)
      from rqx factors_relprime have "coprime (q^2 + 3*r^2) (18*r)"
        and "(q^2 + 3*r^2)*(18*r) = x^3" by (auto simp add: ac_simps)
      hence "\<exists> d. q^2 + 3*r^2 = d^3" 
        by (simp add: int_relprime_odd_power_divisors)
      then obtain d where d: "q^2 + 3*r^2 = d^3" by auto
      have "odd d"
      proof (rule ccontr)
        assume "\<not> odd d"
        hence "2 dvd d^3" by simp
        moreover have "2 dvd 2*(9*r)" by (rule dvd_triv_left)
        ultimately have "2 dvd gcd (2*(9*r)) (d^3)" by simp
        with d factors_relprime show False by auto
      qed
      with d qr_relprime have "coprime q r \<and> q^2 + 3*r^2 = d^3 \<and> odd d" 
        by simp
      hence "is_cube_form q r" by (rule qf3_cube_impl_cube_form)
      then obtain a b where "q = a^3 - 9*a*b^2 \<and> r = 3*a^2*b - 3*b^3" 
        by (unfold is_cube_form_def, auto)
      hence ab: "q = a*(a+3*b)*(a- 3*b) \<and> r = b*(a+b)*(a-b)*3"
        by (simp add: eval_nat_numeral field_simps)
      with c have abc: "(2*b)*(a+b)*(a-b) = c^3" by auto
      from qr_relprime ab have ab_relprime: "coprime a b"
        by (auto intro: coprime_imp_coprime)
      then have ab1: "coprime (2*b) (a+b)"
      proof (rule coprime_imp_coprime)
        fix h
        assume h2b: "h dvd 2*b" and hab: "h dvd a+b"
        have "odd h"
        proof
          assume "even h"
          then have "even (a + b)"
            using hab by (rule dvd_trans)
          then have "even (a+3*b)"
            by simp
          with ab have "even q" "even r"
            by auto
          then show False
            using coprime_common_divisor_int qr_relprime by fastforce
        qed
        with h2b show "h dvd b" 
          using coprime_dvd_mult_right_iff [of h 2 b] by simp
        with hab show "h dvd a"
          using dvd_diff [of h "a + b" b] by simp
      qed
      from ab1 have ab2: "coprime (a+b) (a-b)"
      proof (rule coprime_imp_coprime)
        fix h
        assume hab1: "h dvd a+b" and hab2: "h dvd a-b"
        then show "h dvd 2*b" using dvd_diff[of h "a+b" "a-b"] by fastforce
      qed
      from ab1 have ab3: "coprime (a-b) (2*b)"
      proof (rule coprime_imp_coprime)
        fix h
        assume hab: "h dvd a-b" and h2b: "h dvd 2*b"
        have "a-b+2*b = a+b" by simp
        then show "h dvd a+b" using hab h2b dvd_add [of h "a-b" "2*b"] by presburger
      qed
      then have [simp]: "even b \<longleftrightarrow> odd a"
        by simp
      have "\<exists> k l m. 2*b = k^3 \<and> a+b = l^3 \<and> a-b = m^3"
        using abc ab1 ab2 ab3
          int_relprime_odd_power_divisors [of 3 "2 * b" "(a + b) * (a - b)" c]
          int_relprime_odd_power_divisors [of 3 "a + b" "(2 * b) * (a - b)" c]
          int_relprime_odd_power_divisors [of 3 "a - b" "(2 * b) * (a + b)" c]
        by simp (simp add: ac_simps, simp add: algebra_simps)
      then obtain \<alpha>1 \<beta> \<gamma> where a1: "2*b = \<gamma>^3 \<and> a-b = \<alpha>1^3 \<and> a+b = \<beta>^3"
        by auto 
      then obtain \<alpha> where "\<alpha> = -\<alpha>1" by auto
      \<comment> \<open>show this is a (smaller) solution\<close>
      with a1 have a2: "\<alpha>^3 = b-a" by auto
      with a1 have "\<alpha>^3 + \<beta>^3 = \<gamma>^3" by auto
      moreover have "\<alpha>*\<beta>*\<gamma> \<noteq> 0"
      proof (rule ccontr, safe)
        assume "\<alpha> * \<beta> * \<gamma> = 0"
        with a1 a2 ab have "r=0" by (auto simp add: power_0_left)
        with r vwpq vwx show False by auto
      qed
      moreover have "even \<gamma>"
      proof -
        have "even (2*b)" by simp
        with a1 have "even (\<gamma>^3)" by simp
        thus ?thesis by simp
      qed
      moreover have "coprime \<alpha> \<beta>"
      using ab2 proof (rule coprime_imp_coprime)
        fix h
        assume ha: "h dvd \<alpha>" and hb: "h dvd \<beta>"
        then have "h dvd \<alpha> * \<alpha>^2" and "h dvd \<beta> * \<beta>^2" by simp_all
        then have "h dvd \<alpha>^Suc 2" and "h dvd \<beta>^Suc 2" by (auto simp only: power_Suc)
        with a1 a2 have "h dvd b - a" and "h dvd a + b" by auto 
        then show "h dvd a + b" and "h dvd a - b"
          by (simp_all add: dvd_diff_commute)
      qed
      moreover have "nat\<bar>\<gamma>^3\<bar> < nat\<bar>x^3\<bar>"
      proof -
        let ?A = "p^2 + 3*q^2"
        from vwx vwpq have "x^3 = 2*p*?A" by auto
        also with r have "\<dots> = 6*r*?A" by auto
        also with ab have "\<dots> = 2*b*(9*(a+b)*(a-b)*?A)" by auto
        also with a1 have "\<dots> = \<gamma>^3 *(9*(a+b)*(a-b)*?A)" by auto
        finally have eq: "\<bar>x^3\<bar> = \<bar>\<gamma>^3\<bar> * \<bar>9*(a+b)*(a-b)*?A\<bar>" 
          by (auto simp add: abs_mult)
        with \<open>0 < nat\<bar>x^3\<bar>\<close> have "\<bar>9*(a+b)*(a-b)*?A\<bar> > 0" by auto
        hence "\<bar>(a+b)*(a-b)*?A\<bar> \<ge> 1" by arith
        hence "\<bar>9*(a+b)*(a-b)*?A\<bar> > 1" by arith
        moreover have "\<bar>\<gamma>^3\<bar> > 0"
        proof - 
          from eq have "\<bar>\<gamma>^3\<bar> = 0 \<Longrightarrow> \<bar>x^3\<bar>=0" by auto
          with \<open>0 < nat\<bar>x^3\<bar>\<close> show ?thesis by auto
        qed
        ultimately have "\<bar>\<gamma>^3\<bar> * 1 < \<bar>\<gamma>^3\<bar> * \<bar>9*(a+b)*(a-b)*?A\<bar>"
          by (rule zmult_zless_mono2)
        with eq have "\<bar>x^3\<bar> > \<bar>\<gamma>^3\<bar>" by auto
        thus ?thesis by arith
      qed
      ultimately have ?thesis by auto }
    ultimately show ?thesis by auto
  qed
  thus ?case by auto
qed

text \<open>The theorem. Puts equation in requested shape.\<close>  

theorem fermat_3:
  assumes ass: "(x::int)^3 + y^3 = z^3"
  shows "x*y*z=0"
proof (rule ccontr)
  let ?g = "gcd x y"
  let ?c = "z div ?g"
  assume xyz0: "x*y*z\<noteq>0"
  \<comment> \<open>divide out the g.c.d.\<close>
  hence "x \<noteq> 0 \<or> y \<noteq> 0" by simp
  then obtain a b where ab: "x = ?g*a \<and> y = ?g*b \<and> coprime a b"
    using gcd_coprime_exists[of x y] by (auto simp: mult.commute)
  moreover have abc: "?c*?g = z \<and> a^3 + b^3 = ?c^3 \<and> a*b*?c \<noteq> 0"
  proof -
    from xyz0 have g0: "?g\<noteq>0" by simp
    have zgab: "z^3 = ?g^3 * (a^3+b^3)"
    proof -
      from ab and ass have "z^3 = (?g*a)^3+(?g*b)^3" by simp
      thus ?thesis by (simp only: power_mult_distrib distrib_left)
    qed
    have cgz: "?c * ?g = z"
    proof - 
      from zgab have "?g^3 dvd z^3" by simp
      hence "?g dvd z" by simp
      thus ?thesis by (simp only: ac_simps dvd_mult_div_cancel)
    qed
    moreover have "a^3 + b^3 = ?c^3"
    proof -
      have "?c^3 * ?g^3 = (a^3+b^3)*?g^3"
      proof -
        have "?c^3 * ?g^3 = (?c*?g)^3" by (simp only: power_mult_distrib)
        also with cgz have "\<dots> = z^3" by simp
        also with zgab have "\<dots> = ?g^3*(a^3+b^3)" by simp
        finally show ?thesis by simp
      qed
      with g0 show ?thesis by auto
    qed
    moreover from ab and xyz0 and cgz have "a*b*?c\<noteq>0" by auto
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>make both sides even\<close>
  from ab have "coprime (a ^ 3) (b ^ 3)"
    by simp
  have "\<exists> u v w. u^3 + v^3 = w^3 \<and> u*v*w\<noteq>(0::int) \<and> even w \<and> coprime u v"
  proof -
    let "?Q u v w" = "u^3 + v^3 = w^3 \<and> u*v*w\<noteq>(0::int) \<and> even w \<and> coprime u v"
    have "even a \<or> even b \<or> even ?c"
    proof (rule ccontr)
      assume "\<not>(even a \<or> even b \<or> even ?c)"
      hence aodd: "odd a" and "odd b \<and> odd ?c" by auto
      hence "even (?c^3 - b^3)" by simp
      moreover from abc have "?c^3-b^3 = a^3" by simp
      ultimately have "even (a^3)" by auto
      hence "even (a)" by simp
      with aodd show False by simp
    qed
    moreover
    { assume "even (a)"
      then obtain u v w where uvwabc: "u = -b \<and> v = ?c \<and> w = a \<and> even w" 
        by auto
      moreover with abc have "u*v*w\<noteq>0" by auto
      moreover have uvw: "u^3+v^3=w^3" 
      proof -
        from uvwabc have "u^3 + v^3 = (-1*b)^3 + ?c^3" by simp
        also have "\<dots> = (-1)^3*b^3 + ?c^3" by (simp only: power_mult_distrib)
        also have "\<dots> = - (b^3) + ?c^3" by auto
        also with abc and uvwabc have "\<dots> = w^3" by auto
        finally show ?thesis by simp
      qed
      moreover have "coprime u v"
      using \<open>coprime (a ^ 3) (b ^ 3)\<close> proof (rule coprime_imp_coprime)
        fix h
        assume hu: "h dvd u" and "h dvd v"
        with uvwabc have "h dvd ?c*?c^2" by (simp only: dvd_mult2)
        with abc have "h dvd a^3+b^3" using power_Suc[of ?c 2] by simp
        moreover from hu uvwabc have hb3: "h dvd b*b^2" by simp
        ultimately have "h dvd a^3+b^3-b^3"
          using power_Suc [of b 2] dvd_diff [of h "a ^ 3 + b ^ 3" "b ^ 3"] by simp
        with hb3 show "h dvd a^3" "h dvd b^3" using power_Suc[of b 2] by auto
      qed
      ultimately have "?Q u v w" using \<open>even a\<close> by simp
      hence ?thesis by auto }
    moreover 
    { assume "even b"
      then obtain u v w where uvwabc: "u = -a \<and> v = ?c \<and> w = b \<and> even w" 
        by auto
      moreover with abc have "u*v*w\<noteq>0" by auto
      moreover have uvw: "u^3+v^3=w^3" 
      proof -
        from uvwabc have "u^3 + v^3 = (-1*a)^3 + ?c^3" by simp
        also have "\<dots> = (-1)^3*a^3 + ?c^3" by (simp only: power_mult_distrib)
        also have "\<dots> = - (a^3) + ?c^3" by auto
        also with abc and uvwabc have "\<dots> = w^3" by auto
        finally show ?thesis by simp
      qed
      moreover have "coprime u v"
      using \<open>coprime (a ^ 3) (b ^ 3)\<close> proof (rule coprime_imp_coprime)
        fix h
        assume hu: "h dvd u" and "h dvd v"
        with uvwabc have "h dvd ?c*?c^2" by (simp only: dvd_mult2)
        with abc have "h dvd a^3+b^3" using power_Suc[of ?c 2] by simp
        moreover from hu uvwabc have hb3: "h dvd a*a^2" by simp
        ultimately have "h dvd a^3+b^3-a^3"
          using power_Suc [of a 2] dvd_diff [of h "a ^ 3 + b ^ 3" "a ^ 3"] by simp
        with hb3 show "h dvd a^3" and "h dvd b^3" using power_Suc[of a 2] by auto
      qed
      ultimately have "?Q u v w" using \<open>even b\<close> by simp
      hence ?thesis by auto }
    moreover 
    { assume "even ?c"
      then obtain u v w where uvwabc: "u = a \<and> v = b \<and> w = ?c \<and> even w"
        by auto
      with abc ab have ?thesis by auto }
    ultimately show ?thesis by auto
  qed
  hence "\<exists> w. \<exists> u v. u^3 + v^3 = w^3 \<and> u*v*w \<noteq> (0::int) \<and> even w \<and> coprime u v"
    by auto
  \<comment> \<open>show contradiction using the earlier result\<close>
  thus False by (auto simp only: no_rewritten_fermat3)
qed

corollary fermat_mult3:
  assumes xyz: "(x::int)^n + y^n = z^n" and n: "3 dvd n"
  shows "x*y*z=0"
proof -
  from n obtain m where "n = m*3" by (auto simp only: ac_simps dvd_def)
  with xyz have "(x^m)^3 + (y^m)^3 = (z^m)^3" by (simp only: power_mult)
  hence "(x^m)*(y^m)*(z^m) = 0" by (rule fermat_3)
  thus ?thesis by auto
qed

end

end
