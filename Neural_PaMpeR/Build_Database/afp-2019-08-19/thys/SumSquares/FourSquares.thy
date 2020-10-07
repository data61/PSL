(*  Title:      FourSquares.thy
    Author:     Roelof Oosterhuis, 2007  Rijksuniversiteit Groningen
*)

section \<open>Lagrange's four-square theorem\<close>

theory FourSquares
  imports "HOL-Number_Theory.Number_Theory"
begin

context

  fixes sum4sq_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  defines "sum4sq_nat a b c d \<equiv> a^2+b^2+c^2+d^2"
  
  fixes is_sum4sq_nat :: "nat \<Rightarrow> bool"
  defines "is_sum4sq_nat n \<equiv> (\<exists> a b c d. n = sum4sq_nat a b c d)"
  
begin

(* TODO: move this lemma to the distribution (?). (It is used also in QuadForm and TwoSquares) *)
private lemma best_division_abs: "(n::int) > 0 \<Longrightarrow> \<exists> k. 2 * \<bar>a - k*n\<bar> \<le> n"
proof -
  assume a: "n > 0"
  define k where "k = a div n"
  have h: "a - k * n = a mod n" by (simp add: div_mult_mod_eq algebra_simps k_def)
  thus ?thesis
  proof (cases "2 * (a mod n) \<le> n")
    case True
    hence "2 * \<bar>a - k*n\<bar> \<le> n" using h pos_mod_sign a by auto
    thus ?thesis by blast
  next
    case False
    hence "2 * (n - a mod n) \<le> n" by auto
    have "a - (k+1)*n = a mod n - n" using h by (simp add: algebra_simps)
    hence "2 * \<bar>a - (k+1)*n\<bar> \<le> n" using h pos_mod_bound[of n a] a False by fastforce
    thus ?thesis by blast
  qed
qed

text \<open>Shows that all nonnegative integers can be written as the sum of four squares. The proof consists of the following steps:
\begin{itemize}\item For every prime $p=2n+1$ the two sets of residue classes $$\{x^2 \bmod p\mid 0\le x\le n\} ~{\rm and}~ \{-1-y^2 \bmod p \mid 0 \le y \le n\}$$ both contain $n+1$ different elements and therefore they must have at least one element in common.
\item Hence there exist $x,y$ such that $x^2+y^2+1^2+0^2$ is a multiple of $p$.
\item The next step is to show, by an infinite descent, that $p$ itself can be written as the sum of four squares.
\item Finally, using the multiplicity of this form, the same holds for all positive numbers.
\end{itemize}\<close>

private definition
  sum4sq_int :: "int \<times> int \<times> int \<times> int \<Rightarrow> int" where
  "sum4sq_int = (\<lambda>(a,b,c,d). a^2+b^2+c^2+d^2)"

private definition
  is_sum4sq_int :: "int \<Rightarrow> bool" where
  "is_sum4sq_int n \<longleftrightarrow> (\<exists> a b c d. n = sum4sq_int(a,b,c,d))"

private lemma mult_sum4sq_int: "sum4sq_int(a,b,c,d) * sum4sq_int(p,q,r,s) =
  sum4sq_int(a*p+b*q+c*r+d*s, a*q-b*p-c*s+d*r,
         a*r+b*s-c*p-d*q, a*s-b*r+c*q-d*p)"
  by (unfold sum4sq_int_def, simp add: eval_nat_numeral field_simps)

private lemma sum4sq_int_nat_eq: "sum4sq_nat a b c d = sum4sq_int (a, b, c, d)"
  unfolding sum4sq_nat_def sum4sq_int_def by simp

private lemma is_sum4sq_int_nat_eq: "is_sum4sq_nat n = is_sum4sq_int (int n)"
  unfolding is_sum4sq_nat_def is_sum4sq_int_def
proof
  assume "\<exists>a b c d. n = sum4sq_nat a b c d"
  thus "\<exists>a b c d. int n = sum4sq_int (a, b, c, d)" using sum4sq_int_nat_eq by force
next
  assume "\<exists>a b c d. int n = sum4sq_int (a, b, c, d)"
  then obtain a b c d where "int n = sum4sq_int (a, b, c, d)" by blast
  hence "int n = sum4sq_int (int (nat \<bar>a\<bar>), int (nat \<bar>b\<bar>), int (nat \<bar>c\<bar>), int (nat \<bar>d\<bar>))"
    unfolding sum4sq_int_def by simp
  hence "int n = int (sum4sq_nat (nat \<bar>a\<bar>) (nat \<bar>b\<bar>) (nat \<bar>c\<bar>) (nat \<bar>d\<bar>))"
    using sum4sq_int_nat_eq by presburger
  thus "\<exists>a b c d. n = sum4sq_nat a b c d" by auto
qed

private lemma is_mult_sum4sq_int: "is_sum4sq_int x \<Longrightarrow> is_sum4sq_int y \<Longrightarrow> is_sum4sq_int (x*y)"
  by (unfold is_sum4sq_int_def, auto simp only: mult_sum4sq_int, blast)

private lemma is_mult_sum4sq_nat: "is_sum4sq_nat x \<Longrightarrow> is_sum4sq_nat y \<Longrightarrow> is_sum4sq_nat (x*y)"
  using is_mult_sum4sq_int is_sum4sq_int_nat_eq by simp

private lemma mult_oddprime_is_sum4sq: "\<lbrakk> prime (nat p); odd p \<rbrakk> \<Longrightarrow>
  \<exists> t. 0<t \<and> t<p \<and> is_sum4sq_int (p*t)"
proof -
  assume p1: "prime (nat p)"
  then have p0: "p > 1" and "prime p"
    by (simp_all add: prime_int_nat_transfer prime_nat_iff)
  assume p2: "odd p"
  then obtain n where n: "p = 2*n+1" using oddE by blast
  with p1 have n0: "n > 0" by (auto simp add: prime_nat_iff)
  let ?C = "{0 ..< p}"
  let ?D = "{0 .. n}"
  let ?f = "%x. x^2 mod p"
  let ?g = "%x. (-1-x^2) mod p"
  let ?A = "?f ` ?D"
  let ?B = "?g ` ?D"
  have finC: "finite ?C" by simp
  have finD: "finite ?D" by simp
  from p0 have AsubC: "?A \<subseteq> ?C" and BsubC: "?B \<subseteq> ?C"
    by (auto simp add: pos_mod_conj)
  with finC have finA: "finite ?A" and finB: "finite ?B"
    by (auto simp add: finite_subset)
  from AsubC BsubC have AunBsubC: "?A \<union> ?B \<subseteq> ?C" by (rule Un_least)
  from p0 have cardC: "card ?C = nat p" using card_atLeastZeroLessThan_int by blast
  from n0 have cardD: "card ?D = 1+ nat n" by simp
  have cardA: "card ?A = card ?D"
  proof -
    have "inj_on ?f ?D"
    proof (unfold inj_on_def, auto)
      fix x fix y
      assume x0: "0 \<le> x" and xn: "x \<le> n" and y0: "0 \<le> y" and yn: " y \<le> n"
        and xyp: "x^2 mod p = y^2 mod p"
      with p0 have "[x^2 = y^2] (mod p)" using cong_def by blast
      hence "p dvd x^2-y^2" using cong_iff_dvd_diff by blast
      hence "p dvd (x+y)*(x-y)" by (simp add: power2_eq_square algebra_simps)
      hence "p dvd x+y \<or> p dvd x-y" using \<open>prime p\<close> p0 
        by (auto dest: prime_dvd_multD)
      moreover
      { assume "p dvd x+y"
        moreover from xn yn n have "x+y < p" by auto
        ultimately have "\<not> x+y > 0" by (auto simp add: zdvd_not_zless)
        with x0 y0 have "x = y" by auto } \<comment> \<open>both are zero\<close>
      moreover
      { assume ass: "p dvd x-y"
        have "x = y"
        proof (rule ccontr, case_tac "x-y \<ge> 0")
          assume "x-y \<ge> 0" and "x \<noteq> y" hence "x-y > 0" by auto
          with ass have "\<not> x-y < p" by (auto simp add: zdvd_not_zless)
          with xn y0 n p0 show "False" by auto
        next
          assume "\<not> 0 \<le> x-y" hence "y-x > 0" by auto
          moreover from x0 yn n p0 have "y-x < p" by auto
          ultimately have "\<not> p dvd y-x" by (auto simp add: zdvd_not_zless)
          moreover from ass have "p dvd -(x-y)" by (simp only: dvd_minus_iff)
          ultimately show "False" by auto
        qed }
      ultimately show "x=y" by auto
    qed
    with finD show ?thesis by (simp only: inj_on_iff_eq_card)
  qed
  have cardB: "card ?B = card ?D"
  proof -
    have "inj_on ?g ?D"
    proof (unfold inj_on_def, auto)
      fix x fix y
      assume x0: "0 \<le> x" and xn: "x \<le> n" and y0: "0 \<le> y" and yn: " y \<le> n"
        and xyp: "(-1-x^2) mod p = (-1-y^2) mod p"
      with p0 have "[-1-y^2 = -1-x^2] (mod p)" by (simp only: cong_def)
      hence "p dvd (-1-y^2) - (-1-x^2)" by (simp only: cong_iff_dvd_diff)
      moreover have "-1-y^2 - (-1-x^2) = x^2 - y^2" by arith
      ultimately have "p dvd x^2-y^2" by simp
      hence "p dvd (x+y)*(x-y)" by (simp add: power2_eq_square algebra_simps)
      with p1 have "p dvd x+y \<or> p dvd x-y" using \<open>prime p\<close> p0 
        by (auto dest: prime_dvd_multD)
      moreover
      { assume "p dvd x+y"
        moreover from xn yn n have "x+y < p" by auto
        ultimately have "\<not> x+y > 0" by (auto simp add: zdvd_not_zless)
        with x0 y0 have "x = y" by auto } \<comment> \<open>both are zero\<close>
      moreover
      { assume ass: "p dvd x-y"
        have "x = y"
        proof (rule ccontr, case_tac "x-y \<ge> 0")
          assume "x-y \<ge> 0" and "x \<noteq> y" hence "x-y > 0" by auto
          with ass have "\<not> x-y < p" by (auto simp add: zdvd_not_zless)
          with xn y0 n p0 show "False" by auto
        next
          assume "\<not> 0 \<le> x-y" hence "y-x > 0" by auto
          moreover from x0 yn n p0 have "y-x < p" by auto
          ultimately have "\<not> p dvd y-x" by (auto simp add: zdvd_not_zless)
          moreover from ass have "p dvd -(x-y)" by (simp only: dvd_minus_iff)
          ultimately show "False" by auto
        qed }
      ultimately show "x=y" by auto
    qed
    with finD show ?thesis by (simp only: inj_on_iff_eq_card)
  qed
  have "?A \<inter> ?B \<noteq> {}"
  proof (rule ccontr, auto)
    assume ABdisj: "?A \<inter> ?B = {}"
    from cardA cardB cardD have "2 + 2*(nat n) = card ?A + card ?B" by auto
    also with finA finB ABdisj have "\<dots> = card (?A \<union> ?B)"
      by (simp only: card_Un_disjoint)
    also with finC AunBsubC have "\<dots> \<le> card ?C" by (simp only: card_mono)
    also with cardC have "\<dots> = nat p" by simp
    finally have "2 + 2*(nat n) \<le> nat p" by simp
    with n show "False" by arith
  qed
  then obtain z where "z \<in> ?A \<and> z \<in> ?B" by auto
  then obtain x y where xy: "x \<in> ?D \<and> y \<in> ?D \<and> z = x^2 mod p \<and> z = (-1-y^2) mod p" by blast
  with p0 have "[x^2=-1-y^2](mod p)" by (simp add: cong_def)
  hence "p dvd x^2-(-1-y^2)" by (simp only: cong_iff_dvd_diff)
  moreover have "x^2-(-1-y^2)=x^2+y^2+1" by arith
  ultimately have "p dvd sum4sq_int(x,y,1,0)" by (auto simp add: sum4sq_int_def)
  then obtain t where t: "p * t = sum4sq_int(x,y,1,0)" by (auto simp only: dvd_def eq_refl)
  hence "is_sum4sq_int (p*t)" by (unfold is_sum4sq_int_def, auto)
  moreover have "t > 0 \<and> t < p"
  proof
    have "x^2 \<ge> 0 \<and> y^2 \<ge> 0" by simp
    hence "x^2+y^2+1 > 0" by arith
    with t have "p*t > 0" by (unfold sum4sq_int_def, auto)
    moreover
    { assume "t < 0" with p0 have "p*t < p*0" by (simp only: zmult_zless_mono2)
      hence "p*t < 0" by simp }
    moreover
    { assume "t = 0" hence "p*t = 0" by simp }
    ultimately have "\<not> t < 0 \<and> t \<noteq> 0" by auto
    thus "t > 0" by simp
    from xy have "x^2 \<le> n^2 \<and> y^2 \<le> n^2" by (auto simp add: power_mono)
    hence "x^2+y^2+1 \<le> 2*n^2 + 1" by auto
    with t have contr: "p*t \<le> 2*n^2+1" by (simp add: sum4sq_int_def)
    moreover
    { assume "t > n+1"
      with p0 have "p*(n+1) < p*t" by (simp only: zmult_zless_mono2)
      with n have "p*t > (2*n+1)*n + (2*n+1)*1" by (simp only: distrib_left)
      hence "p*t > 2*n*n + n + 2*n + 1" by (simp only: distrib_right mult_1_left)
      with n0 have "p*t > 2*n^2 + 1" by (simp add: power2_eq_square) }
    ultimately have "\<not> t > n+1" by auto
    with n0 n show "t < p" by auto
  qed
  ultimately show ?thesis by blast
qed

private lemma zprime_is_sum4sq: "prime (nat p) \<Longrightarrow> is_sum4sq_int p"
proof (cases)
  assume p2: "p=2"
  hence "p = sum4sq_int(1,1,0,0)" by (auto simp add: sum4sq_int_def)
  thus ?thesis by (auto simp add: is_sum4sq_int_def)
next
  assume "\<not> p =2" and prp: "prime (nat p)"
  hence "\<not> nat p = 2" by simp
  with prp have "2 < nat p" using prime_nat_iff by force
  moreover with prp have "odd (nat p)" using prime_odd_nat[of "nat p"] by blast
  ultimately have "odd p" by (simp add: even_nat_iff)
  with prp have "\<exists> t. 0<t \<and> t<p \<and> is_sum4sq_int (p*t)" by (rule mult_oddprime_is_sum4sq)
  then obtain a b c d t where pt_sol: "0<t \<and> t<p \<and> p*t = sum4sq_int(a,b,c,d)"
    by (unfold is_sum4sq_int_def, blast)
  hence Qt: "0<t \<and> t<p \<and> (\<exists> a1 a2 a3 a4. p*t = sum4sq_int(a1,a2,a3,a4))"
    (is "?Q t") by blast
  have "?Q 1"
  proof (rule ccontr)
    assume nQ1: "\<not> ?Q 1"
    have "\<not> ?Q t"
    proof (induct t rule: infinite_descent0_measure[where V="\<lambda>x. (nat x)- 1"], clarify)
      fix x a b c d
      assume "nat x - 1 = 0" and "x > 0" and s: "p*x=sum4sq_int(a,b,c,d)" and "x < p"
      moreover hence "x = 1" by arith
      ultimately have "?Q 1" by auto
      with nQ1 show False by auto
    next
      fix x
      assume "0 < nat x - 1" and "\<not> \<not> ?Q x"
      then obtain a1 a2 a3 a4 where ass: "1<x \<and> x<p \<and> p*x = sum4sq_int(a1,a2,a3,a4)"
        by auto
      have "\<exists> y. nat y - 1 < nat x - 1 \<and> ?Q y"
      proof (cases)
        assume evx: "even x"
        hence "even (x*p)" by simp
        with ass have ev1234: "even (a1^2+a2^2 + a3^2+a4^2)"
          by (auto simp add: sum4sq_int_def ac_simps)
        have "\<exists> b1 b2 b3 b4. p*x=sum4sq_int(b1,b2,b3,b4) \<and> even (b1+b2) \<and> even (b3+b4)"
        proof (cases)
          assume ev12: "even (a1^2+a2^2)"
          with ev1234 ass show ?thesis by auto
        next
          assume "\<not> even (a1^2+a2^2)"
          hence odd12: "odd (a1^2+a2^2)" by simp
          with ev1234 have odd34: "odd (a3^2+a4^2)" by auto
          show ?thesis
          proof (cases)
            assume ev1: "even (a1^2)"
            with odd12 have odd2: "odd (a2^2)" by simp
            show ?thesis
            proof (cases)
              assume "even (a3^2)"
              moreover from ass have "p*x = sum4sq_int(a1,a3,a2,a4)" by (auto simp add: sum4sq_int_def)
              ultimately show ?thesis using odd2 odd34 ev1 by auto
            next
              assume "\<not> even (a3^2)"
              moreover from ass have "p*x = sum4sq_int(a1,a4,a2,a3)" by (auto simp add: sum4sq_int_def)
              ultimately show ?thesis using odd34 odd2 ev1 by auto
            qed
          next
            assume odd1: "\<not> even (a1^2)"
            with odd12 have ev2: "even (a2^2)" by simp
            show ?thesis
            proof (cases)
              assume "even (a3^2)"
              moreover from ass have "sum4sq_int(a1,a4,a2,a3)=p*x" by (auto simp add: sum4sq_int_def)
              ultimately show ?thesis using odd34 odd1 ev2 by force
            next
              assume "\<not> even (a3^2)"
              moreover from ass have "sum4sq_int(a1,a3,a2,a4)=p*x" by (auto simp add: sum4sq_int_def)
              ultimately show ?thesis using odd34 odd1 ev2 by force
            qed
          qed
        qed
        then obtain b1 b2 b3 b4
          where b: "p*x = sum4sq_int(b1,b2,b3,b4) \<and> even (b1+b2) \<and> even (b3+b4)" by auto
        then obtain c1 c3 where c13: "b1+b2 = 2*c1 \<and> b3+b4 = 2*c3"
          using evenE[of "b1+b2"] evenE[of "b3+b4"] by meson
        from b have "even (b1-b2) \<and> even (b3-b4)" by simp
        then obtain c2 c4 where c24: "b1-b2 = 2*c2 \<and> b3-b4 = 2*c4"
          using evenE[of "b1-b2"] evenE[of "b3-b4"] by meson
        from evx obtain y where y: "x = 2*y" using evenE by blast
        hence "4*(p*y) = 2*(p*x)" by (simp add: ac_simps)
        also from b have "\<dots> = 2*b1^2 + 2*b2^2 + 2*b3^2 + 2*b4^2"
          by (auto simp: sum4sq_int_def)
        also have "\<dots> = (b1 + b2)^2 + (b1 - b2)^2 + (b3 + b4)^2 + (b3 - b4)^2"
          by (auto simp add: power2_eq_square algebra_simps)
        also with c13 c24 have "\<dots> = 4*(c1^2 + c2^2 + c3^2 + c4^2)"
          by (auto simp add: power_mult_distrib)
        finally have "p * y = sum4sq_int(c1,c2,c3,c4)" by (auto simp add: sum4sq_int_def)
        moreover from y ass have "0 < y \<and> y < p \<and> (nat y) - 1 < (nat x) - 1" by arith
        ultimately show ?thesis by blast
      next
        assume xodd: "\<not> even x"
        with ass have "\<exists> c1 c2 c3 c4. 2*\<bar>a1-c1*x\<bar>\<le>x \<and> 2*\<bar>a2-c2*x\<bar>\<le>x \<and> 2*\<bar>a3-c3*x\<bar>\<le>x \<and> 2*\<bar>a4-c4*x\<bar>\<le>x"
          by (simp add: best_division_abs)
        then obtain b1 c1 b2 c2 b3 c3 b4 c4 where
          bc_def: "b1 = a1-c1*x \<and> b2 = a2-c2*x \<and> b3 = a3-c3*x \<and> b4 = a4-c4*x"
          and "2*\<bar>b1\<bar>\<le>x \<and> 2*\<bar>b2\<bar>\<le>x \<and> 2*\<bar>b3\<bar>\<le>x \<and> 2*\<bar>b4\<bar>\<le>x"
          by blast
        moreover have "2*\<bar>b1\<bar>\<noteq>x \<and> 2*\<bar>b2\<bar>\<noteq>x \<and> 2*\<bar>b3\<bar>\<noteq>x \<and> 2*\<bar>b4\<bar>\<noteq>x" using xodd by fastforce
        ultimately have bc_abs: "2*\<bar>b1\<bar><x \<and> 2*\<bar>b2\<bar><x \<and> 2*\<bar>b3\<bar><x \<and> 2*\<bar>b4\<bar><x" by auto
        let ?B = "b1^2 + b2^2 + b3^2 + b4^2"
        let ?C = "c1^2 + c2^2 + c3^2 + c4^2"
        have "x dvd ?B"
        proof
          from bc_def ass have
            "?B = p*x - 2*(a1*c1+a2*c2+a3*c3+a4*c4)*x + ?C*x^2"
            unfolding sum4sq_int_def by (auto simp add: power2_eq_square algebra_simps)
          thus "?B = x*(p - 2*(a1*c1+a2*c2+a3*c3+a4*c4) + ?C*x)"
            by (auto simp add: ac_simps power2_eq_square
              distrib_left right_diff_distrib)
        qed
        then obtain y where y: "?B = x * y" by (auto simp add: dvd_def)
        let ?A1 = "a1*b1 + a2*b2 + a3*b3 + a4*b4"
        let ?A2 = "a1*b2 - a2*b1 - a3*b4 + a4*b3"
        let ?A3 = "a1*b3 + a2*b4 - a3*b1 - a4*b2"
        let ?A4 = "a1*b4 - a2*b3 + a3*b2 - a4*b1"
        let ?A = "sum4sq_int(?A1,?A2,?A3,?A4)"
        have "x dvd ?A1 \<and> x dvd ?A2 \<and> x dvd ?A3 \<and> x dvd ?A4"
        proof (safe)
          from bc_def have
            "?A1 = (b1+c1*x)*b1 + (b2+c2*x)*b2 + (b3+c3*x)*b3 + (b4+c4*x)*b4"
            by simp
          also with y have "\<dots> = x*(y + c1*b1 + c2*b2 + c3*b3 + c4*b4)"
            by (auto simp add: distrib_left power2_eq_square ac_simps)
          finally show "x dvd ?A1" by auto
          from bc_def have
            "?A2 = (b1+c1*x)*b2 - (b2+c2*x)*b1 - (b3+c3*x)*b4 + (b4+c4*x)*b3"
            by simp
          also have "\<dots> = x*(c1*b2 - c2*b1 - c3*b4 + c4*b3)"
            by (auto simp add: distrib_left right_diff_distrib ac_simps)
          finally show "x dvd ?A2" by auto
          from bc_def have
            "?A3 = (b1+c1*x)*b3 + (b2+c2*x)*b4 - (b3+c3*x)*b1 - (b4+c4*x)*b2"
            by simp
          also have "\<dots> = x*(c1*b3 + c2*b4 - c3*b1 - c4*b2)"
            by (auto simp add: distrib_left right_diff_distrib ac_simps)
          finally show "x dvd ?A3" by auto
          from bc_def have
            "?A4 = (b1+c1*x)*b4 - (b2+c2*x)*b3 + (b3+c3*x)*b2 - (b4+c4*x)*b1"
            by simp
          also have "\<dots> = x*(c1*b4 - c2*b3 + c3*b2 - c4*b1)"
            by (auto simp add: distrib_left right_diff_distrib ac_simps)
          finally show "x dvd ?A4" by auto
        qed
        then obtain d1 d2 d3 d4 where d:
          "?A1=x*d1 \<and> ?A2=x*d2 \<and> ?A3=x*d3 \<and> ?A4=x*d4"
          by (auto simp add: dvd_def)
        let ?D = "sum4sq_int(d1,d2,d3,d4)"
        from d have "x^2*?D = ?A"
          by (auto simp only: sum4sq_int_def power_mult_distrib distrib_left)
        also have "\<dots> = sum4sq_int(a1,a2,a3,a4)*sum4sq_int(b1,b2,b3,b4)"
          by (simp only: mult_sum4sq_int)
        also with y ass have "\<dots> = (p*x)*(x*y)" by (auto simp add: sum4sq_int_def)
        also have "\<dots> = x^2*(p*y)" by (simp only: power2_eq_square ac_simps)
        finally have "x^2*(?D - p*y) = 0" by (auto simp add: right_diff_distrib)
        with ass have "p*y = ?D" by auto
        moreover have y_l_x: "y < x"
        proof -
          have "4*b1^2 = (2*\<bar>b1\<bar>)^2 \<and> 4*b2^2 = (2*\<bar>b2\<bar>)^2 \<and>
            4*b3^2 = (2*\<bar>b3\<bar>)^2 \<and> 4*b4^2 = (2*\<bar>b4\<bar>)^2" by simp
          with bc_abs have "4*b1^2<x^2 \<and> 4*b2^2<x^2 \<and> 4*b3^2<x^2 \<and> 4*b4^2<x^2"
            using power_strict_mono [of "2*\<bar>b\<bar>" x 2 for b]
            by auto
          hence "?B < x^2" by auto
          with y have "x*(x-y) > 0"
            by (auto simp add: power2_eq_square right_diff_distrib)
          moreover from ass have "x > 0" by simp
          ultimately show ?thesis using zero_less_mult_pos by fastforce
        qed
        moreover have "y > 0"
        proof -
          have b2pos: "b1^2 \<ge> 0 \<and> b2^2 \<ge> 0 \<and> b3^2 \<ge> 0 \<and> b4^2 \<ge> 0" by simp
          hence "?B = 0 \<or> ?B > 0" by arith
          moreover
          { assume "?B = 0"
            moreover from b2pos have
              "?B-b1^2 \<ge> 0 \<and> ?B-b2^2 \<ge> 0 \<and> ?B-b3^2 \<ge> 0 \<and> ?B-b4^2 \<ge> 0" by arith
            ultimately have "b1^2 \<le> 0 \<and> b2^2 \<le> 0 \<and> b3^2 \<le> 0 \<and> b4^2 \<le> 0" by auto
            with b2pos have  "b1^2 = 0 \<and> b2^2 = 0 \<and> b3^2 = 0 \<and> b4^2 = 0" by arith
            hence "b1 = 0 \<and> b2 = 0 \<and> b3 = 0 \<and> b4 = 0" by auto
            with bc_def have "x dvd a1 \<and> x dvd a2 \<and> x dvd a3 \<and> x dvd a4"
              by auto
            hence "x^2 dvd a1^2 \<and> x^2 dvd a2^2 \<and> x^2 dvd a3^2 \<and> x^2 dvd a4^2" by simp
            hence "x^2 dvd a1^2+a2^2+a3^2+a4^2" by (simp only: dvd_add)
            with ass have "x^2 dvd p*x" by (auto simp only: sum4sq_int_def)
            hence "x*x dvd x*p" by (simp only: power2_eq_square ac_simps)
            with ass have "nat x dvd nat p"
              by (simp add: nat_dvd_iff)
            moreover from ass prp have "x \<ge> 0 \<and> x \<noteq> 1 \<and> x \<noteq> p \<and> prime (nat p)" by simp
            ultimately have "False" unfolding prime_nat_iff by auto }
          moreover
          { assume "?B > 0"
            with y have "x*y > 0" by simp
            moreover from ass have "x > 0" by simp
            ultimately have ?thesis using zero_less_mult_pos by blast }
          ultimately show ?thesis by auto
        qed
        moreover with y_l_x have "(nat y) - 1 < (nat x) - 1" by arith
        moreover from y_l_x ass have "y < p" by auto
        ultimately show ?thesis by blast
      qed
      thus "\<exists> y. nat y - 1 < nat x - 1 \<and> \<not> \<not> ?Q y" by blast
    qed
    with Qt show "False" by simp
  qed
  thus "is_sum4sq_int p" by (auto simp add: is_sum4sq_int_def)
qed

private lemma prime_is_sum4sq: "prime p \<Longrightarrow> is_sum4sq_nat p"
  using zprime_is_sum4sq is_sum4sq_int_nat_eq by simp

theorem sum_of_four_squares: "is_sum4sq_nat n"
proof (induction n rule: nat_less_induct)
case (1 n)
  show ?case
  proof (cases "n>1")
  case False
    hence "n = 0 \<or> n = 1" by auto
    moreover have "0 = sum4sq_nat 0 0 0 0" "1 = sum4sq_nat 1 0 0 0" unfolding sum4sq_nat_def by auto
    ultimately show ?thesis unfolding is_sum4sq_nat_def by blast
  next
  case True
    then obtain p m where dec: "prime p \<and> n = p * m" using prime_factor_nat[of n] 
      by (auto elim: dvdE)
    moreover hence "m<n" using n_less_m_mult_n[of m p] prime_gt_Suc_0_nat[of p] True by linarith
    ultimately have "is_sum4sq_nat m" "is_sum4sq_nat p" using 1 prime_is_sum4sq by blast+
    thus ?thesis using dec is_mult_sum4sq_nat by blast
  qed
qed

end

end
