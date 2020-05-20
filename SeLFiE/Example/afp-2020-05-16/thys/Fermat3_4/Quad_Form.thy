(*  Title:      QuadForm.thy
    Author:     Roelof Oosterhuis
                2007  Rijksuniversiteit Groningen
*)

section \<open>The quadratic form $x^2 + Ny^2$\<close>

theory Quad_Form
imports
  "HOL-Number_Theory.Number_Theory"
begin

context
begin

text \<open>Shows some properties of the quadratic form $x^2+Ny^2$, such as how to multiply and divide them. The second part focuses on the case $N=3$ and is used in the proof of the case $n=3$ of Fermat's last theorem. The last part -- not used for FLT3 -- shows which primes can be written as $x^2 + 3y^2$.\<close>

subsection \<open>Definitions and auxiliary results\<close>

(* TODO: move this lemma to the distribution (?). (It is used also in TwoSquares and FourSquares) *)
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

lemma prime_power_dvd_cancel_right:
  "p ^ n dvd a" if "prime (p::'a::semiring_gcd)" "\<not> p dvd b" "p ^ n dvd a * b"
proof -
  from that have "coprime p b"
    by (auto intro: prime_imp_coprime)
  with that show ?thesis
    by (simp add: coprime_dvd_mult_left_iff)
qed

definition
  is_qfN :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "is_qfN A N \<longleftrightarrow> (\<exists> x y. A = x^2 + N*y^2)"

definition
  is_cube_form :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "is_cube_form a b \<longleftrightarrow> (\<exists> p q. a = p^3 - 9*p*q^2 \<and> b = 3*p^2*q - 3*q^3)"

private lemma abs_eq_impl_unitfactor: "\<bar>a::int\<bar> = \<bar>b\<bar> \<Longrightarrow> \<exists> u. a = u*b \<and> \<bar>u\<bar>=1"
proof -
  assume "\<bar>a\<bar> = \<bar>b\<bar>"
  hence "a = 1*b \<or> a = (-1)*b" by arith
  then obtain u where "a = u*b \<and> (u=1 \<or> u=-1)" by blast
  thus ?thesis by auto
qed

private lemma prime_3_nat: "prime (3::nat)" by auto

subsection \<open>Basic facts if $N \ge 1$\<close>

lemma qfN_pos: "\<lbrakk> N \<ge> 1; is_qfN A N \<rbrakk> \<Longrightarrow> A \<ge> 0"
proof -
  assume N: "N \<ge> 1" and "is_qfN A N"
  then obtain a b where ab: "A = a^2 + N*b^2" by (auto simp add: is_qfN_def)
  have "N*b^2 \<ge> 0"
  proof (cases)
    assume "b = 0" thus ?thesis by auto
  next
    assume "\<not> b = 0" hence " b^2 > 0" by simp
    moreover from N have "N>0" by simp
    ultimately have "N*b^2 > N*0" by (auto simp only: zmult_zless_mono2)
    thus ?thesis by auto
  qed
  with ab have "A \<ge> a^2" by auto
  moreover have "a^2 \<ge> 0" by (rule zero_le_power2)
  ultimately show ?thesis by arith
qed

lemma qfN_zero: "\<lbrakk> (N::int) \<ge> 1; a^2 + N*b^2 = 0 \<rbrakk> \<Longrightarrow> (a = 0 \<and> b = 0)"
proof -
  assume N: "N \<ge> 1" and abN: "a^2 + N*b^2 = 0"
  show ?thesis
  proof (rule ccontr, auto)
    assume "a \<noteq> 0" hence "a^2 > 0" by simp
    moreover have "N*b^2 \<ge> 0"
    proof (cases)
      assume "b = 0" thus ?thesis by auto
    next
      assume "\<not> b = 0" hence " b^2 > 0" by simp
      moreover from N have "N>0" by simp
      ultimately have "N*b^2 > N*0" by (auto simp only: zmult_zless_mono2)
      thus ?thesis by auto
    qed
    ultimately have "a^2 + N*b^2 > 0" by arith
    with abN show False by auto
  next
    assume "b \<noteq> 0" hence "b^2>0" by simp
    moreover from N have "N>0" by simp
    ultimately have "N*b^2>N*0" by (auto simp only: zmult_zless_mono2)
    hence "N*b^2 > 0" by simp
    moreover have "a^2 \<ge> 0" by (rule zero_le_power2)
    ultimately have "a^2 + N*b^2 > 0" by arith
    with abN show False by auto
  qed
qed

subsection \<open>Multiplication and division\<close>

lemma qfN_mult1: "((a::int)^2 + N*b^2)*(c^2 + N*d^2)
  = (a*c+N*b*d)^2 + N*(a*d-b*c)^2"
  by (simp add: eval_nat_numeral field_simps)

lemma qfN_mult2: "((a::int)^2 + N*b^2)*(c^2 + N*d^2)
  = (a*c-N*b*d)^2 + N*(a*d+b*c)^2"
  by (simp add: eval_nat_numeral field_simps)

corollary is_qfN_mult: "is_qfN A N \<Longrightarrow> is_qfN B N \<Longrightarrow> is_qfN (A*B) N"
  by (unfold is_qfN_def, auto, auto simp only: qfN_mult1)

corollary is_qfN_power: "(n::nat) > 0 \<Longrightarrow> is_qfN A N \<Longrightarrow> is_qfN (A^n) N"
  by (induct n, auto, case_tac "n=0", auto simp add: is_qfN_mult)

lemma qfN_div_prime:
  fixes p :: int
  assumes ass: "prime (p^2+N*q^2) \<and> (p^2+N*q^2) dvd (a^2+N*b^2)"
  shows "\<exists> u v. a^2+N*b^2 = (u^2+N*v^2)*(p^2+N*q^2)
                \<and> (\<exists> e. a = p*u+e*N*q*v \<and> b = p*v - e*q*u \<and> \<bar>e\<bar>=1)"
proof -
  let ?P = "p^2+N*q^2"
  let ?A = "a^2+N*b^2"
  from ass obtain U where U: "?A = ?P*U" by (auto simp only: dvd_def)
  have "\<exists> e. ?P dvd b*p + e*a*q \<and> \<bar>e\<bar> = 1"
  proof -
    have "?P dvd (b*p + a*q)*(b*p - a*q)"
    proof -
      have "(b*p + a*q)*(b*p - a*q)= b^2*?P - q^2*?A"
        by (simp add: eval_nat_numeral field_simps)
      also from U have "\<dots> = (b^2 - q^2*U)*?P" by (simp add: field_simps)
      finally show ?thesis by simp
    qed
    with ass have "?P dvd (b*p + a*q) \<or> ?P dvd (b*p - a*q)"
      by (simp add: nat_abs_mult_distrib prime_int_iff prime_dvd_mult_iff)
    moreover
    { assume "?P dvd b*p + a*q"
      hence "?P dvd b*p + 1*a*q \<and> \<bar>1\<bar> = (1::int)" by simp }
    moreover
    { assume "?P dvd b*p - a*q"
      hence "?P dvd b*p + (-1)*a*q \<and> \<bar>-1\<bar> = (1::int)" by simp }
    ultimately show ?thesis by blast
  qed
  then obtain v e where v: "b*p + e*a*q = ?P*v" and e: "\<bar>e\<bar> = 1"
    by (auto simp only: dvd_def)
  have "?P dvd a*p - e*N*b*q"
  proof (cases)
    assume e1: "e = 1"
    from U have "U * ?P^2 = ?A * ?P" by (simp add: power2_eq_square)
    also with e1 have "\<dots> = (a*p-e*N*b*q)^2 + N*(b*p+e*a*q)^2"
      by (simp only: qfN_mult2 add.commute mult_1_left)
    also with v have "\<dots> = (a*p-e*N*b*q)^2 + N*v^2*?P^2"
      by (simp only: power_mult_distrib ac_simps)
    finally have "(a*p-e*N*b*q)^2 = ?P^2*(U-N*v^2)"
      by (simp add: ac_simps left_diff_distrib)
    hence "?P^2 dvd (a*p - e*N*b*q)^2" by (rule dvdI)
    thus ?thesis by simp
  next
    assume "\<not> e=1" with e have e1: "e=-1" by auto
    from U have "U * ?P^2 = ?A * ?P" by (simp add: power2_eq_square)
    also with e1 have "\<dots> = (a*p-e*N*b*q)^2 + N*( -(b*p+e*a*q))^2"
      by (simp add: qfN_mult1)
    also have "\<dots> = (a*p-e*N*b*q)^2 + N*(b*p+e*a*q)^2"
      by (simp only: power2_minus)
    also with v have "\<dots> = (a*p-e*N*b*q)^2 + N*v^2*?P^2"
      by (simp only: power_mult_distrib ac_simps)
    finally have "(a*p-e*N*b*q)^2 = ?P^2*(U-N*v^2)"
      by (simp add: ac_simps left_diff_distrib)
    hence "?P^2 dvd (a*p-e*N*b*q)^2" by (rule dvdI)
    thus ?thesis by simp
  qed
  then obtain u where u: "a*p - e*N*b*q = ?P*u" by (auto simp only: dvd_def)
  from e have e2_1: "e * e = 1"
    using abs_mult_self_eq [of e] by simp
  have a: "a = p*u + e*N*q*v"
  proof -
    have "(p*u + e*N*q*v)*?P = p*(?P*u) + (e*N*q)*(?P*v)"
      by (simp only: distrib_right ac_simps)
    also with v u have "\<dots> = p*(a*p - e*N*b*q) + (e*N*q)*(b*p + e*a*q)"
      by simp
    also have "\<dots> = a*(p^2 + e*e*N*q^2)"
      by (simp add: power2_eq_square distrib_left ac_simps right_diff_distrib)
    also with e2_1 have "\<dots> = a*?P" by simp
    finally have "(a-(p*u+e*N*q*v))*?P = 0" by auto
    moreover from ass have "?P \<noteq> 0" by auto
    ultimately show ?thesis by simp
  qed
  moreover have b: "b = p*v-e*q*u"
  proof -
    have "(p*v-e*q*u)*?P = p*(?P*v) - (e*q)*(?P*u)"
      by (simp only: left_diff_distrib ac_simps)
    also with v u have "\<dots> = p*(b*p+e*a*q) - e*q*(a*p-e*N*b*q)" by simp
    also have "\<dots> = b*(p^2 + e*e*N*q^2)"
      by (simp add: power2_eq_square distrib_left ac_simps right_diff_distrib)
    also with e2_1 have "\<dots> = b * ?P" by simp
    finally have "(b-(p*v-e*q*u))*?P = 0" by auto
    moreover from ass have "?P \<noteq> 0" by auto
    ultimately show ?thesis by simp
  qed
  moreover have "?A = (u^2 + N*v^2)*?P"
  proof (cases)
    assume "e=1"
    with a and b show ?thesis by (simp add: qfN_mult1 ac_simps)
  next
    assume "\<not> e=1" with e have "e=-1" by simp
    with a and b show ?thesis by (simp add: qfN_mult2 ac_simps)
  qed
  moreover from e have "\<bar>e\<bar> = 1" .
  ultimately show ?thesis by blast
qed

corollary qfN_div_prime_weak:
  "\<lbrakk> prime (p^2+N*q^2::int); (p^2+N*q^2) dvd (a^2+N*b^2) \<rbrakk>
  \<Longrightarrow> \<exists> u v. a^2+N*b^2 = (u^2+N*v^2)*(p^2+N*q^2)"
  apply (subgoal_tac "\<exists> u v. a^2+N*b^2 = (u^2+N*v^2)*(p^2+N*q^2)
    \<and> (\<exists> e. a = p*u+e*N*q*v \<and> b = p*v - e*q*u \<and> \<bar>e\<bar>=1)", blast)
  apply (rule qfN_div_prime, auto)
done

corollary qfN_div_prime_general: "\<lbrakk> prime P; P dvd A; is_qfN A N; is_qfN P N \<rbrakk>
  \<Longrightarrow> \<exists> Q. A = Q*P \<and> is_qfN Q N"
  apply (subgoal_tac "\<exists> u v. A = (u^2+N*v^2)*P")
  apply (unfold is_qfN_def, auto)
  apply (simp only: qfN_div_prime_weak)
done

lemma qfN_power_div_prime:
  fixes P :: int
  assumes ass: "prime P \<and> odd P \<and> P dvd A \<and> P^n = p^2+N*q^2
  \<and> A^n = a^2+N*b^2 \<and> coprime a b \<and> coprime p (N*q) \<and> n>0"
  shows "\<exists> u v. a^2+N*b^2 = (u^2 + N*v^2)*(p^2+N*q^2) \<and> coprime u v
                \<and> (\<exists> e. a = p*u+e*N*q*v \<and> b = p*v-e*q*u \<and> \<bar>e\<bar> = 1)"
proof -
  from ass have "P dvd A \<and> n>0" by simp
  hence "P^n dvd A^n" by simp
  then obtain U where U: "A^n = U*P^n" by (auto simp only: dvd_def ac_simps)
  from ass have "coprime a b"
    by blast
  have "\<exists> e. P^n dvd b*p + e*a*q \<and> \<bar>e\<bar> = 1"
  proof -
    have Pn_dvd_prod: "P^n dvd (b*p + a*q)*(b*p - a*q)"
    proof -
      have "(b*p + a*q)*(b*p - a*q) = (b*p)^2 - (a*q)^2" 
        by (simp add: power2_eq_square algebra_simps)
      also have "\<dots> = b^2 * p^2 + b^2*N*q^2 - b^2*N*q^2 - a^2*q^2"
        by (simp add: power_mult_distrib)
      also with ass have "\<dots> = b^2*P^n - q^2*A^n"
        by (simp only: ac_simps distrib_right distrib_left)
      also with U have "\<dots> = (b^2-q^2*U)*P^n" by (simp only: left_diff_distrib)
      finally show ?thesis by (simp add: ac_simps)
    qed
    have "P^n dvd (b*p + a*q) \<or> P^n dvd (b*p - a*q)"
    proof -
      have PdvdPn: "P dvd P^n"
      proof -
        from ass have "\<exists> m. n = Suc m" by (simp add: not0_implies_Suc)
        then obtain m where "n = Suc m" by auto
        hence "P^n = P*(P^m)" by auto
        thus ?thesis by auto
      qed
      have "\<not> P dvd b*p+a*q \<or>  \<not> P dvd b*p-a*q"
      proof (rule ccontr, simp)
        assume "P dvd b*p+a*q \<and> P dvd b*p-a*q"
        hence "P dvd (b*p+a*q)+(b*p-a*q) \<and> P dvd (b*p+a*q)-(b*p-a*q)"
          by (simp only: dvd_add, simp only: dvd_diff)
        hence "P dvd 2*(b*p) \<and> P dvd 2*(a*q)" by (simp only: mult_2, auto)
        with ass have "(P dvd 2 \<or> P dvd b*p) \<and> (P dvd 2 \<or> P dvd a*q)"
          using prime_dvd_multD by blast
        hence "P dvd 2 \<or> (P dvd b*p \<and> P dvd a*q)" by auto
        moreover have "\<not> P dvd 2"
        proof (rule ccontr, simp)
          assume pdvd2: "P dvd 2"
          have "P \<le> 2"
          proof (rule ccontr)
            assume "\<not> P \<le> 2" hence Pl2: "P > 2" by simp
            with pdvd2 show False by (simp add: zdvd_not_zless)
          qed
          moreover from ass have "P > 1" by (simp add: prime_int_iff)
          ultimately have "P=2" by auto
          with ass have "odd 2" by simp
          thus False by simp
        qed
        ultimately have "P dvd b*p \<and> P dvd a*q" by auto
        with ass have "(P dvd b \<or> P dvd p) \<and> (P dvd a \<or> P dvd q)"
          using prime_dvd_multD by blast
        moreover have "\<not> P dvd p \<and> \<not> P dvd q"
        proof (auto dest: ccontr)
          assume Pdvdp: "P dvd p"
          hence "P dvd p^2" by (simp only: dvd_mult power2_eq_square)
          with PdvdPn have "P dvd P^n-p^2" by (simp only: dvd_diff)
          with ass have "P dvd N*(q*q)" by (simp add: power2_eq_square)
          with ass have h1: "P dvd N \<or> P dvd (q*q)" using prime_dvd_multD by blast
          moreover
          {
            assume "P dvd (q*q)"
            hence "P dvd q" using prime_dvd_multD ass by blast
          }
          ultimately have "P dvd N*q" by fastforce
          with Pdvdp have "P dvd gcd p (N*q)" by simp
          with ass show False by (simp add: prime_int_iff)
        next
          assume "P dvd q"
          hence PdvdNq: "P dvd N*q" by simp
          hence "P dvd N*q*q" by simp
          hence "P dvd N*q^2" by (simp add: power2_eq_square ac_simps)
          with PdvdPn have "P dvd P^n-N*q^2" by (simp only: dvd_diff)
          with ass have "P dvd p*p" by (simp add: power2_eq_square)
          with ass have "P dvd p" by (auto dest: prime_dvd_multD)
          with PdvdNq have "P dvd gcd p (N*q)" by auto
          with ass show False by (auto simp add: prime_int_iff)
        qed
        ultimately have "P dvd a \<and> P dvd b" by auto
        hence "P dvd gcd a b" by simp
        with ass show False by (auto simp add: prime_int_iff)
      qed
      moreover
      { assume "\<not> P dvd b*p+a*q"
        with Pn_dvd_prod and ass have "P^n dvd b*p-a*q"
          by (rule_tac b="b*p+a*q" in prime_power_dvd_cancel_right, auto simp add: mult.commute) }
      moreover
      { assume "\<not> P dvd b*p-a*q"
        with Pn_dvd_prod and ass have "P^n dvd b*p+a*q"
          by (rule_tac a="b*p+a*q" in prime_power_dvd_cancel_right, simp) }
      ultimately show ?thesis by auto
    qed
    moreover
    { assume "P^n dvd b*p + a*q"
      hence "P^n dvd b*p + 1*a*q \<and> \<bar>1\<bar> = (1::int)" by simp }
    moreover
    { assume "P^n dvd b*p - a*q"
      hence "P^n dvd b*p + (-1)*a*q \<and> \<bar>-1\<bar> = (1::int)" by simp }
    ultimately show ?thesis by blast
  qed
  then obtain v e where v: "b*p + e*a*q = P^n*v" and e: "\<bar>e\<bar> = 1"
    by (auto simp only: dvd_def)
  have "P^n dvd a*p - e*N*b*q"
  proof (cases)
    assume e1: "e = 1"
    from U have "(P^n)^2*U = A^n*P^n" by (simp add: power2_eq_square ac_simps)
    also with e1 ass have "\<dots> = (a*p-e*N*b*q)^2 + N*(b*p+e*a*q)^2"
      by (simp only: qfN_mult2 add.commute mult_1_left)
    also with v have "\<dots> = (a*p-e*N*b*q)^2 + (P^n)^2*(N*v^2)"
      by (simp only: power_mult_distrib ac_simps)
    finally have "(a*p-e*N*b*q)^2 = (P^n)^2*U - (P^n)^2*N*v^2" by simp
    also have "\<dots> = (P^n)^2 * (U - N*v^2)" by (simp only: right_diff_distrib)
    finally have "(P^n)^2 dvd (a*p - e*N*b*q)^2" by (rule dvdI)
    thus ?thesis by simp
  next
    assume "\<not> e=1" with e have e1: "e=-1" by auto
    from U have "(P^n)^2 * U = A^n * P^n" by (simp add: power2_eq_square)
    also with e1 ass have "\<dots> = (a*p-e*N*b*q)^2 + N*( -(b*p+e*a*q))^2"
      by (simp add: qfN_mult1)
    also have "\<dots> = (a*p-e*N*b*q)^2 + N*(b*p+e*a*q)^2"
      by (simp only: power2_minus)
    also with v and ass have "\<dots> = (a*p-e*N*b*q)^2 + N*v^2*(P^n)^2"
      by (simp only: power_mult_distrib ac_simps)
    finally have "(a*p-e*N*b*q)^2 = (P^n)^2*U-(P^n)^2*N*v^2" by simp
    also have "\<dots> = (P^n)^2 * (U - N*v^2)" by (simp only: right_diff_distrib)
    finally have "(P^n)^2 dvd (a*p-e*N*b*q)^2" by (rule dvdI)
    thus ?thesis by simp
  qed
  then obtain u where u: "a*p - e*N*b*q = P^n*u" by (auto simp only: dvd_def)
  from e have e2_1: "e * e = 1"
    using abs_mult_self_eq [of e] by simp
  have a: "a = p*u + e*N*q*v"
  proof -
    from ass have "(p*u + e*N*q*v)*P^n = p*(P^n*u) + (e*N*q)*(P^n*v)"
      by (simp only: distrib_right ac_simps)
    also with v and u have "\<dots> = p*(a*p - e*N*b*q) + (e*N*q)*(b*p + e*a*q)"
      by simp
    also have "\<dots> = a*(p^2 + e*e*N*q^2)"
      by (simp add: power2_eq_square distrib_left ac_simps right_diff_distrib)
    also with e2_1 and ass have "\<dots> = a*P^n" by simp
    finally have "(a-(p*u+e*N*q*v))*P^n = 0" by auto
    moreover from ass have "P^n \<noteq> 0"
      by (unfold prime_int_iff, auto)
    ultimately show ?thesis by auto
  qed
  moreover have b: "b = p*v-e*q*u"
  proof -
    from ass have "(p*v-e*q*u)*P^n = p*(P^n*v) - (e*q)*(P^n*u)"
      by (simp only: left_diff_distrib ac_simps)
    also with v u have "\<dots> = p*(b*p+e*a*q) - e*q*(a*p-e*N*b*q)" by simp
    also have "\<dots> = b*(p^2 + e*e*N*q^2)"
      by (simp add: power2_eq_square distrib_left ac_simps right_diff_distrib)
    also with e2_1 and ass have "\<dots> = b * P^n" by simp
    finally have "(b-(p*v-e*q*u))*P^n = 0" by auto
    moreover from ass have "P^n \<noteq> 0"
      by (unfold prime_int_iff, auto)
    ultimately show ?thesis by auto
  qed
  moreover have "A^n = (u^2 + N*v^2)*P^n"
  proof (cases)
    assume "e=1"
    with a and b and ass show ?thesis by (simp add: qfN_mult1 ac_simps)
  next
    assume "\<not> e=1" with e have "e=-1" by simp
    with a and b and ass show ?thesis by (simp add: qfN_mult2 ac_simps)
  qed
  moreover have "coprime u v"
    using \<open>coprime a b\<close>
  proof (rule coprime_imp_coprime)
    fix w
    assume "w dvd u" "w dvd v"
    then have "w dvd u*p + v*(e*N*q) \<and> w dvd v*p - u*(e*q)"
      by simp
    with a b show "w dvd a" "w dvd b"
      by (auto simp only: ac_simps)
  qed
  moreover from e and ass have
    "\<bar>e\<bar> = 1 \<and> A^n = a^2+N*b^2 \<and> P^n = p^2+N*q^2" by simp
  ultimately show ?thesis by auto
qed

lemma qfN_primedivisor_not:
  assumes ass: "prime P \<and> Q > 0 \<and> is_qfN (P*Q) N \<and> \<not> is_qfN P N"
  shows "\<exists> R. (prime R \<and> R dvd Q \<and> \<not> is_qfN R N)"
proof (rule ccontr, auto)
  assume ass2: "\<forall> R. R dvd Q \<longrightarrow> prime R \<longrightarrow> is_qfN R N"
  define ps where "ps = prime_factorization (nat Q)"
  from ass have ps: "(\<forall>p\<in>set_mset ps. prime p) \<and> Q = int (\<Prod>i\<in>#ps. i)"
    by (auto simp: ps_def prod_mset_prime_factorization_int)
  have ps_lemma: "((\<forall>p\<in>set_mset ps. prime p) \<and> is_qfN (P*int(\<Prod>i\<in>#ps. i)) N
    \<and> (\<forall>R. (prime R \<and> R dvd int(\<Prod>i\<in>#ps. i)) \<longrightarrow> is_qfN R N)) \<Longrightarrow> False"
    (is "?B ps \<Longrightarrow> False")
  proof (induct ps)
    case empty hence "is_qfN P N" by simp
    with ass show False by simp
  next
    case (add p ps)
    hence ass3: "?B ps \<Longrightarrow> False"
      and IH: "?B (ps + {#p#})" by simp_all
    hence p: "prime (int p)" and "int p dvd int(\<Prod>i\<in>#ps + {#p#}. i)" by auto
    moreover with IH have pqfN: "is_qfN (int p) N"
      and "int p dvd P*int(\<Prod>i\<in>#ps + {#p#}. i)" and "is_qfN (P*int(\<Prod>i\<in>#ps + {#p#}. i)) N"
      by auto
    ultimately obtain S where S: "P*int(\<Prod>i\<in>#ps + {#p#}. i) = S*(int p) \<and> is_qfN S N"
      using qfN_div_prime_general by blast
    hence "(int p)*(P* int(\<Prod>i\<in>#ps. i) - S) = 0" by auto
    with p S have "is_qfN (P*int(\<Prod>i\<in>#ps. i)) N" by (auto simp add: prime_int_iff)
    moreover from IH have "(\<forall>p\<in>set_mset ps. prime p)" by simp
    moreover from IH have "\<forall> R. prime R \<and> R dvd int(\<Prod>i\<in>#ps. i) \<longrightarrow> is_qfN R N" by auto
    ultimately have "?B ps" by simp
    with ass3 show False by simp
  qed
  with ps ass2 ass show False by auto
qed

lemma prime_factor_int:
  fixes k :: int
  assumes "\<bar>k\<bar> \<noteq> 1"
  obtains p where "prime p" "p dvd k"
proof (cases "k = 0")
  case True
  then have "prime (2::int)" and "2 dvd k"
    by simp_all
  with that show thesis
    by blast
next
  case False
  with assms prime_divisor_exists [of k] obtain p where "prime p" "p dvd k"
    by auto
  with that show thesis
    by blast
qed

lemma qfN_oddprime_cube:
  "\<lbrakk> prime (p^2+N*q^2::int); odd (p^2+N*q^2); p \<noteq> 0; N \<ge> 1 \<rbrakk>
  \<Longrightarrow> \<exists> a b. (p^2+N*q^2)^3 = a^2 + N*b^2 \<and> coprime a (N*b)"
proof -
  let ?P = "p^2+N*q^2"
  assume P: "prime ?P" and Podd: "odd ?P" and p0: "p \<noteq> 0" and N1: "N \<ge> 1"
  have suc23: "3 = Suc 2" by simp
  let ?a = "p*(p^2 - 3*N*q^2)"
  let ?b = "q*(3*p^2 - N*q^2)"
  have abP: "?P^3 = ?a^2 + N*?b^2" by (simp add: eval_nat_numeral field_simps)
  have "?P dvd p" if h1: "gcd ?b ?a \<noteq> 1"
  proof -
    let ?h = "gcd ?b ?a"
    have h2: "?h \<ge> 0" by simp
    hence "?h = 0 \<or> ?h = 1 \<or> ?h > 1" by arith
    with h1 have "?h =0 \<or> ?h >1" by auto
    moreover
    { assume "?h = 0"
      hence "?a = 0 \<and> ?b = 0"
        by auto
      with abP have "?P^3 = 0"
        by auto
      with P have False
        by (unfold prime_int_iff, auto)
      hence ?thesis by simp }
    moreover
    { assume "?h > 1"
      then have "\<exists>g. prime g \<and> g dvd ?h"
        using prime_factor_int [of ?h] by auto
      then obtain g where g: "prime g" "g dvd ?h"
        by blast
      then have "g dvd ?b \<and> g dvd ?a" by simp
      with g have g1: "g dvd q \<or> g dvd 3*p^2-N*q^2"
        and g2: "g dvd p \<or> g dvd p^2 - 3*N*q^2"
        by (auto dest: prime_dvd_multD)
      from g have gpos: "g \<ge> 0" by (auto simp only: prime_int_iff)
      have "g dvd ?P"
      proof (cases)
        assume "g dvd q"
        hence gNq: "g dvd N*q^2" by (auto simp add: dvd_def power2_eq_square)
        show ?thesis
        proof (cases)
          assume gp: "g dvd p"
          hence "g dvd p^2" by (auto simp add: dvd_def power2_eq_square)
          with gNq show ?thesis by auto
        next
          assume "\<not> g dvd p" with g2 have "g dvd p^2 - 3*N*q^2" by auto
          moreover from gNq have "g dvd 4*(N*q^2)" by (rule dvd_mult)
          ultimately have "g dvd p^2 - 3*(N*q^2) + 4*(N*q^2)"
            by (simp only: ac_simps dvd_add)
          moreover have "p^2 - 3*(N*q^2)+4*(N*q^2) = p^2 + N*q^2" by arith
          ultimately show ?thesis by simp
        qed
      next
        assume "\<not> g dvd q" with g1 have gpq: "g dvd 3*p^2-N*q^2" by simp
        show ?thesis
        proof (cases)
          assume "g dvd p"
          hence "g dvd 4*p^2" by (auto simp add: dvd_def power2_eq_square)
          with gpq have " g dvd 4*p^2 - (3*p^2 - N*q^2)" by (simp only: dvd_diff)
          moreover have "4*p^2 - (3*p^2 - N*q^2) = p^2 + N*q^2" by arith
          ultimately show ?thesis by simp
        next
          assume "\<not> g dvd p" with g2 have "g dvd p^2 - 3*N*q^2" by auto
          with gpq have "g dvd 3*p^2-N*q^2 - (p^2 - 3*N*q^2)"
            by (simp only: dvd_diff)
          moreover have "3*p^2-N*q^2 - (p^2 - 3*N*q^2) = 2*?P" by auto
          ultimately have "g dvd 2*?P" by simp
          with g have "g dvd 2 \<or> g dvd ?P" by (simp only: prime_dvd_multD)
          moreover have "\<not> g dvd 2"
          proof (rule ccontr, simp)
            assume gdvd2: "g dvd 2"
            have "g \<le> 2"
            proof (rule ccontr)
              assume "\<not> g \<le> 2" hence "g > 2" by simp
              moreover have "(0::int) < 2" by auto
              ultimately have "\<not> g dvd 2" by (auto simp only: zdvd_not_zless)
              with gdvd2 show False by simp
            qed
            moreover from g have "g \<ge> 2" by (simp add: prime_int_iff)
            ultimately have "g = 2" by auto
            with g have "2 dvd ?a \<and> 2 dvd ?b" by auto
            hence "2 dvd ?a^2 \<and> 2 dvd N*?b^2"
              by (simp add: power2_eq_square)
            with abP have "2 dvd ?P^3" by (simp only: dvd_add)
            hence "even (?P^3)" by auto
            moreover have "odd (?P^3)" using Podd by simp
            ultimately show False by auto
          qed
          ultimately show ?thesis by simp
        qed
      qed
      with P gpos have "g = 1 \<or> g = ?P"
        by (simp add: prime_int_iff)
      with g have "g = ?P" by (simp add: prime_int_iff)
      with g have Pab: "?P dvd ?a \<and> ?P dvd ?b" by auto
      have ?thesis
      proof -
        from Pab P have "?P dvd p \<or> ?P dvd p^2- 3*N*q^2"
          by (auto dest: prime_dvd_multD)
        moreover
        { assume "?P dvd p^2 - 3*N*q^2"
          moreover have "?P dvd 3*(p^2 + N*q^2)"
            by (auto simp only: dvd_refl dvd_mult)
          ultimately have "?P dvd p^2- 3*N*q^2 + 3*(p^2+N*q^2)"
            by (simp only: dvd_add)
          hence "?P dvd 4*p^2" by auto
          with P have "?P dvd 4 \<or> ?P dvd p^2"
            by (simp only: prime_dvd_multD)
          moreover have "\<not> ?P dvd 4"
          proof (rule ccontr, simp)
            assume Pdvd4: "?P dvd 4"
            have "?P \<le> 4"
            proof (rule ccontr)
              assume "\<not> ?P \<le> 4" hence "?P > 4" by simp
              moreover have "(0::int) < 4" by auto
              ultimately have "\<not> ?P dvd 4" by (auto simp only: zdvd_not_zless)
              with Pdvd4 show False by simp
            qed
            moreover from P have "?P \<ge> 2" by (auto simp add: prime_int_iff)
            moreover have "?P \<noteq> 2 \<and> ?P \<noteq> 4"
            proof (rule ccontr, simp)
              assume "?P = 2 \<or> ?P = 4" hence "even ?P" by fastforce
              with Podd show False by blast
            qed
            ultimately have "?P = 3" by auto
            with Pdvd4 have "(3::int) dvd 4" by simp
            thus False by arith
          qed
          ultimately have "?P dvd p*p" by (simp add: power2_eq_square)
          with P have ?thesis by (auto dest: prime_dvd_multD) }
        ultimately show ?thesis by auto
      qed }
    ultimately show ?thesis by blast
  qed
  moreover have "?P dvd p" if h1: "gcd N ?a \<noteq> 1"
  proof -
    let ?h = "gcd N ?a"
    have h2: "?h \<ge> 0" by simp
    hence "?h = 0 \<or> ?h = 1 \<or> ?h > 1" by arith
    with h1 have "?h =0 \<or> ?h >1" by auto
    moreover
    { assume "?h = 0" hence "N = 0 \<and> ?a = 0"
        by auto
      hence "N = 0" by arith
      with N1 have False by auto
      hence ?thesis by simp }
    moreover
    { assume "?h > 1"
      then have "\<exists>g. prime g \<and> g dvd ?h"
        using prime_factor_int [of ?h] by auto
      then obtain g where g: "prime g" "g dvd ?h"
        by blast
      hence gN: "g dvd N" and "g dvd ?a" by auto
      hence "g dvd p*p^2 - N*(3*p*q^2)"
        by (auto simp only: right_diff_distrib ac_simps)
      with gN have "g dvd p*p^2 - N*(3*p*q^2) + N*(3*p*q^2)"
        by (simp only: dvd_add dvd_mult2)
      hence "g dvd p*p^2" by simp
      with g have "g dvd p \<or> g dvd p*p"
        by (simp add: prime_dvd_multD power2_eq_square)
      with g have gp: "g dvd p" by (auto dest: prime_dvd_multD)
      hence "g dvd p^2" by (simp add: power2_eq_square)
      with gN have gP: "g dvd ?P" by auto
      from g have "g \<ge> 0" by (simp add: prime_int_iff)
      with gP P g have "g = 1 \<or> g = ?P"
        by (auto dest: primes_dvd_imp_eq)
      with g have "g = ?P" by (auto simp only: prime_int_iff)
      with gp have ?thesis by simp }
    ultimately show ?thesis by auto
  qed
  moreover have "\<not> ?P dvd p"
  proof (rule ccontr, clarsimp)
    assume Pdvdp: "?P dvd p"
    have "p^2 \<ge> ?P^2"
    proof (rule ccontr)
      assume "\<not> p^2 \<ge> ?P^2" hence pP: "p^2 < ?P^2" by simp
      moreover with p0 have "p^2 > 0" by simp
      ultimately have "\<not> ?P^2 dvd p^2" by (simp add: zdvd_not_zless)
      with Pdvdp show False by simp
    qed
    moreover with P have "?P*1 < ?P*?P"
      unfolding prime_int_iff by (auto simp only: zmult_zless_mono2)
    ultimately have "p^2 > ?P" by (auto simp add: power2_eq_square)
    hence neg: "N*q^2 < 0" by auto
    show False
    proof -
      have "is_qfN (0^2 + N*q^2) N" by (auto simp only: is_qfN_def)
      with N1 have "0^2 +N*q^2 \<ge> 0" by (rule qfN_pos)
      with neg show False by simp
    qed
  qed
  ultimately have "gcd ?a ?b = 1" "gcd ?a N = 1"
    by (auto simp add: ac_simps)
  then have "coprime ?a ?b" "coprime ?a N "
    by (auto simp only: gcd_eq_1_imp_coprime)
  then have "coprime ?a (N * ?b)"
    by simp
  with abP show ?thesis
    by blast
qed

subsection \<open>Uniqueness ($N>1$)\<close>

lemma qfN_prime_unique:
  "\<lbrakk> prime (a^2+N*b^2::int); N > 1; a^2+N*b^2 = c^2+N*d^2 \<rbrakk>
  \<Longrightarrow> (\<bar>a\<bar> = \<bar>c\<bar> \<and> \<bar>b\<bar> = \<bar>d\<bar>)"
proof -
  let ?P = "a^2+N*b^2"
  assume P: "prime ?P" and N: "N > 1" and abcdN: "?P = c^2 + N*d^2"
  have mult: "(a*d+b*c)*(a*d-b*c) = ?P*(d^2-b^2)"
  proof -
    have "(a*d+b*c)*(a*d-b*c) = (a^2 + N*b^2)*d^2 - b^2*(c^2 + N*d^2)"
      by (simp add: eval_nat_numeral field_simps)
    with abcdN show ?thesis by (simp add: field_simps)
  qed
  have "?P dvd a*d+b*c \<or> ?P dvd a*d-b*c"
  proof -
    from mult have "?P dvd (a*d+b*c)*(a*d-b*c)" by simp
    with P show ?thesis by (auto dest: prime_dvd_multD)
  qed
  moreover
  { assume "?P dvd a*d+b*c"
    then obtain Q where Q: "a*d+b*c = ?P*Q" by (auto simp add: dvd_def)
    from abcdN have "?P^2 = (a^2 + N*b^2) * (c^2 + N*d^2)"
      by (simp add: power2_eq_square)
    also have "\<dots> = (a*c-N*b*d)^2 + N*(a*d+b*c)^2" by (rule qfN_mult2)
    also with Q have "\<dots> = (a*c-N*b*d)^2 + N*Q^2*?P^2"
      by (simp add: ac_simps power_mult_distrib)
    also have "\<dots> \<ge> N*Q^2*?P^2" by simp
    finally have pos: "?P^2 \<ge> ?P^2*(Q^2*N)" by (simp add: ac_simps)
    have "b^2 = d^2"
    proof (rule ccontr)
      assume "b^2 \<noteq> d^2"
      with P mult Q have "Q \<noteq> 0" by (unfold prime_int_iff, auto)
      hence "Q^2 > 0" by simp
      moreover with N have "Q^2*N > Q^2*1" by (simp only: zmult_zless_mono2)
      ultimately have "Q^2*N > 1" by arith
      moreover with P have "?P^2 > 0" by (simp add: prime_int_iff)
      ultimately have "?P^2*1 < ?P^2*(Q^2*N)" by (simp only: zmult_zless_mono2)
      with pos show False by simp
    qed }
  moreover
  { assume "?P dvd a*d-b*c"
    then obtain Q where Q: "a*d-b*c = ?P*Q" by (auto simp add: dvd_def)
    from abcdN have "?P^2 = (a^2 + N*b^2) * (c^2 + N*d^2)"
      by (simp add: power2_eq_square)
    also have "\<dots> = (a*c+N*b*d)^2 + N*(a*d-b*c)^2" by (rule qfN_mult1)
    also with Q have "\<dots> = (a*c+N*b*d)^2 + N*Q^2*?P^2"
      by (simp add: ac_simps power_mult_distrib)
    also have "\<dots> \<ge> N*Q^2*?P^2" by simp
    finally have pos: "?P^2 \<ge> ?P^2*(Q^2*N)" by (simp add: ac_simps)
    have "b^2 = d^2"
    proof (rule ccontr)
      assume "b^2 \<noteq> d^2"
      with P mult Q have "Q \<noteq> 0" by (unfold prime_int_iff, auto)
      hence "Q^2 > 0" by simp
      moreover with N have "Q^2*N > Q^2*1" by (simp only: zmult_zless_mono2)
      ultimately have "Q^2*N > 1" by arith
      moreover with P have "?P^2 > 0" by (simp add: prime_int_iff)
      ultimately have "?P^2*1 < ?P^2 * (Q^2*N)" by (simp only: zmult_zless_mono2)
      with pos show False by simp
    qed }
  ultimately have bd: "b^2 = d^2" by blast
  moreover with abcdN have "a^2 = c^2" by auto
  ultimately show ?thesis by (auto simp only: power2_eq_iff)
qed

lemma qfN_square_prime:
  assumes ass:
  "prime (p^2+N*q^2::int) \<and> N>1 \<and> (p^2+N*q^2)^2 = r^2+N*s^2 \<and> coprime r s"
  shows "\<bar>r\<bar> = \<bar>p^2-N*q^2\<bar> \<and> \<bar>s\<bar> = \<bar>2*p*q\<bar>"
proof -
  let ?P = "p^2 + N*q^2"
  let ?A = "r^2 + N*s^2"
  from ass have P1: "?P > 1" by (simp add: prime_int_iff)
  from ass have APP: "?A = ?P*?P" by (simp only: power2_eq_square)
  with ass have "prime ?P \<and> ?P dvd ?A" by (simp add: dvdI)
  then obtain u v e where uve:
    "?A = (u^2+N*v^2)*?P \<and> r = p*u+e*N*q*v \<and> s = p*v - e*q*u \<and> \<bar>e\<bar>=1"
    by (frule_tac p="p" in qfN_div_prime, auto)
  with APP P1 ass have "prime (u^2+N*v^2) \<and> N>1 \<and> u^2 + N*v^2 = ?P"
    by auto
  hence "\<bar>u\<bar> = \<bar>p\<bar> \<and> \<bar>v\<bar> = \<bar>q\<bar>" by (auto dest: qfN_prime_unique)
  then obtain f g where f: "u = f*p \<and> \<bar>f\<bar> = 1" and g: "v = g*q \<and> \<bar>g\<bar> = 1"
    by (blast dest: abs_eq_impl_unitfactor)
  with uve have "r = f*p*p + (e*g)*N*q*q \<and> s = g*p*q - (e*f)*p*q" by simp
  hence rs: "r = f*p^2 + (e*g)*N*q^2 \<and> s = (g - e*f)*p*q"
    by (auto simp only: power2_eq_square left_diff_distrib)
  moreover have "s \<noteq> 0"
  proof (rule ccontr, simp)
    assume s0: "s=0"
    hence "gcd r s = \<bar>r\<bar>" by simp
    with ass have "\<bar>r\<bar> = 1" by simp
    hence "r^2 = 1" by (auto simp add: power2_eq_1_iff)
    with s0 have "?A = 1" by simp
    moreover have "?P^2 > 1"
    proof -
      from P1 have "1 < ?P \<and> (0::int) \<le>  1 \<and> (0::nat) < 2" by auto
      hence "?P^2 > 1^2" by (simp only: power_strict_mono)
      thus ?thesis by auto
    qed
    moreover from ass have "?A = ?P^2" by simp
    ultimately show False by auto
  qed
  ultimately have "g \<noteq> e*f" by auto
  moreover from f g uve have "\<bar>g\<bar> = \<bar>e*f\<bar>" unfolding abs_mult by presburger
  ultimately have gef: "g = -(e*f)" by arith
  from uve have "e * - (e * f) = - f" 
    using abs_mult_self_eq [of e] by simp
  hence "r = f*(p^2 - N*q^2) \<and> s = (-e*f)*2*p*q" using rs gef unfolding right_diff_distrib by auto
  hence "\<bar>r\<bar> = \<bar>f\<bar> * \<bar>p^2-N*q^2\<bar>
    \<and> \<bar>s\<bar> = \<bar>e\<bar>*\<bar>f\<bar>*\<bar>2*p*q\<bar>"
    by (auto simp add: abs_mult)
  with uve f g show ?thesis by (auto simp only: mult_1_left)
qed

lemma qfN_cube_prime:
  assumes ass: "prime (p^2 + N*q^2::int) \<and> N > 1
  \<and> (p^2 + N*q^2)^3 = a^2 + N*b^2 \<and> coprime a b"
  shows "\<bar>a\<bar> = \<bar>p^3- 3*N*p*q^2\<bar> \<and> \<bar>b\<bar> = \<bar>3*p^2*q-N*q^3\<bar>"
proof -
  let ?P = "p^2 + N*q^2"
  let ?A = "a^2 + N*b^2"
  from ass have "coprime a b" by blast
  from ass have P1: "?P > 1" by (simp add: prime_int_iff)
  with ass have APP: "?A = ?P*?P^2" by (simp add: power2_eq_square power3_eq_cube)
  with ass have "prime ?P \<and> ?P dvd ?A" by (simp add: dvdI)
  then obtain u v e where uve:
    "?A = (u^2+N*v^2)*?P \<and> a = p*u+e*N*q*v \<and> b = p*v-e*q*u \<and> \<bar>e\<bar>=1"
    by (frule_tac p="p" in qfN_div_prime, auto)
  have "coprime u v"
  proof (rule coprimeI)
    fix c
    assume "c dvd u" "c dvd v"
    with uve have "c dvd a" "c dvd b"
      by simp_all
    with \<open>coprime a b\<close> show "is_unit c"
      by (rule coprime_common_divisor)
  qed
  with P1 uve APP ass have "prime ?P \<and> N > 1 \<and> ?P^2 = u^2+N*v^2
    \<and> coprime u v" by (auto simp add: ac_simps)
  hence "\<bar>u\<bar> = \<bar>p^2-N*q^2\<bar> \<and> \<bar>v\<bar> = \<bar>2*p*q\<bar>" by (rule qfN_square_prime)
  then obtain f g where f: "u = f*(p^2-N*q^2) \<and> \<bar>f\<bar> = 1"
    and g: "v = g*(2*p*q) \<and> \<bar>g\<bar> = 1" by (blast dest: abs_eq_impl_unitfactor)
  with uve have "a = p*f*(p^2-N*q^2) + e*N*q*g*2*p*q
    \<and> b = p*g*2*p*q -e*q*f*(p^2-N*q^2)" by auto
  hence ab: "a = f*p*p^2 + -f*N*p*q^2 + 2*e*g*N*p*q^2
    \<and> b = 2*g*p^2*q - e*f*p^2*q + e*f*N*q*q^2"
    by (auto simp add: ac_simps right_diff_distrib power2_eq_square)
  from f have f2: "f\<^sup>2 = 1"
    using abs_mult_self_eq [of f] by (simp add: power2_eq_square) 
  from g have g2: "g\<^sup>2 = 1"
    using abs_mult_self_eq [of g] by (simp add: power2_eq_square)
  have "e \<noteq> f*g"
  proof (rule ccontr, simp)
    assume efg: "e = f*g"
    with ab g2 have "a = f*p*p^2+f*N*p*q^2" by (auto simp add: power2_eq_square)
    hence "a = (f*p)*?P" by (auto simp add: distrib_left ac_simps)
    hence Pa: "?P dvd a" by auto
    have "e * f = g" using f2 power2_eq_square[of f] efg by simp
    with ab have "b = g*p^2*q+g*N*q*q^2" by auto
    hence "b = (g*q)*?P" by (auto simp add: distrib_left ac_simps)
    hence "?P dvd b" by auto
    with Pa have "?P dvd gcd a b" by simp
    with ass have "?P dvd 1" by auto
    with P1 show False by auto
  qed
  moreover from f g uve have "\<bar>e\<bar> = \<bar>f*g\<bar>" unfolding abs_mult by auto
  ultimately have "e = -(f*g)" by arith
  hence "e * g = -f" "e * f = -g" using f2 g2 unfolding power2_eq_square by auto
  with ab have "a = f*p*p^2 - 3*f*N*p*q^2 \<and> b = 3*g*p^2*q - g*N*q*q^2" by (simp add: mult.assoc)
  hence "a = f*(p^3 - 3*N*p*q^2) \<and> b = g*( 3*p^2*q - N*q^3 )"
    by (auto simp only: right_diff_distrib ac_simps power2_eq_square power3_eq_cube)
  with f g show ?thesis by (auto simp add: abs_mult)
qed

subsection \<open>The case $N=3$\<close>

lemma qf3_even: "even (a^2+3*b^2) \<Longrightarrow> \<exists> B. a^2+3*b^2 = 4*B \<and> is_qfN B 3"
proof -
  let ?A = "a^2+3*b^2"
  assume even: "even ?A"
  have "(odd a \<and> odd b) \<or> (even a \<and> even b)"
  proof (rule ccontr, auto)
    assume "even a" and "odd b"
    hence "even (a^2) \<and> odd (b^2)"
      by (auto simp add: power2_eq_square)
    moreover have "odd 3" by simp
    ultimately have "odd ?A" by simp
    with even show False by simp
  next
    assume "odd a" and "even b"
    hence "odd (a^2) \<and> even (b^2)"
      by (auto simp add: power2_eq_square)
    moreover hence "even (b^2*3)" by simp
    ultimately have "odd (b^2*3+a^2)" by simp
    hence "odd ?A" by (simp add: ac_simps)
    with even show False by simp
  qed
  moreover
  { assume "even a \<and> even b"
    then obtain c d where abcd: "a = 2*c \<and> b = 2*d" using evenE[of a] evenE[of b] by meson
    hence "?A = 4*(c^2 + 3*d^2)" by (simp add: power_mult_distrib)
    moreover have "is_qfN (c^2+3*d^2) 3" by (unfold is_qfN_def, auto)
    ultimately have ?thesis by blast }
  moreover
  { assume "odd a \<and> odd b"
    then obtain c d where abcd: "a = 2*c+1 \<and> b = 2*d+1" using oddE[of a] oddE[of b] by meson
    have "odd (c-d) \<or> even (c-d)" by blast
    moreover
    { assume "even (c-d)"
      then obtain e where "c-d = 2*e" using evenE by blast
      with abcd have e1: "a-b = 4*e" by arith
      hence e2: "a+3*b = 4*(e+b)" by auto
      have "4*?A = (a+3*b)^2 + 3*(a-b)^2"
        by (simp add: eval_nat_numeral field_simps)
      also with e1 e2 have "\<dots> = (4*(e+b))^2+3*(4*e)^2" by (simp(no_asm_simp))
      finally have "?A = 4*((e+b)^2 + 3*e^2)" by (simp add: eval_nat_numeral field_simps)
      moreover have "is_qfN ((e+b)^2 + 3*e^2) 3" by (unfold is_qfN_def, auto)
      ultimately have ?thesis by blast }
    moreover
    { assume "odd (c-d)"
      then obtain e where "c-d = 2*e+1" using oddE by blast
      with abcd have e1: "a+b = 4*(e+d+1)" by auto
      hence e2: "a- 3*b = 4*(e+d-b+1)" by auto
      have "4*?A = (a- 3*b)^2 + 3*(a+b)^2"
        by (simp add: eval_nat_numeral field_simps)
      also with e1 e2 have "\<dots> = (4*(e+d-b+1))^2 +3*(4*(e+d+1))^2"
        by (simp (no_asm_simp))
      finally have "?A = 4*((e+d-b+1)^2+3*(e+d+1)^2)"
        by (simp add: eval_nat_numeral field_simps)
      moreover have "is_qfN ((e+d-b+1)^2 + 3*(e+d+1)^2) 3"
        by (unfold is_qfN_def, auto)
      ultimately have ?thesis by blast }
    ultimately have ?thesis by auto }
  ultimately show ?thesis by auto
qed

lemma qf3_even_general: "\<lbrakk> is_qfN A 3; even A \<rbrakk>
  \<Longrightarrow> \<exists> B. A = 4*B \<and> is_qfN B 3"
proof -
  assume "even A" and "is_qfN A 3"
  then obtain a b where "A = a^2 + 3*b^2"
    and "even (a^2 + 3*b^2)" by (unfold is_qfN_def, auto)
  thus ?thesis by (auto simp add: qf3_even)
qed

lemma qf3_oddprimedivisor_not:
  assumes ass: "prime P \<and> odd P \<and> Q>0 \<and> is_qfN (P*Q) 3 \<and> \<not> is_qfN P 3"
  shows "\<exists> R. prime R \<and> odd R \<and> R dvd Q \<and> \<not> is_qfN R 3"
proof (rule ccontr, simp)
  assume ass2: "\<forall> R. R dvd Q \<longrightarrow> prime R \<longrightarrow> even R \<or> is_qfN R 3"
  (is "?A Q")
  obtain n::nat where "n = nat Q" by auto
  with ass have n: "Q = int n" by auto
  have "(n > 0 \<and> is_qfN (P*int n) 3 \<and> ?A(int n)) \<Longrightarrow> False" (is "?B n \<Longrightarrow> False")
  proof (induct n rule: less_induct)
    case (less n)
    hence IH: "!!m. m<n \<and> ?B m \<Longrightarrow> False"
      and Bn: "?B n" by auto
    show False
    proof (cases)
      assume odd: "odd (int n)"
      from Bn ass have "prime P \<and> int n > 0 \<and> is_qfN (P*int n) 3 \<and> \<not> is_qfN P 3"
        by simp
      hence "\<exists> R. prime R \<and> R dvd int n \<and> \<not> is_qfN R 3"
        by (rule qfN_primedivisor_not)
      then obtain R where R: "prime R \<and> R dvd int n \<and> \<not> is_qfN R 3" by auto
      moreover with odd have "odd R"
      proof -
        from R obtain U where "int n = R*U" by (auto simp add: dvd_def)
        with odd show ?thesis by auto
      qed
      moreover from Bn have "?A (int n)" by simp
      ultimately show False by auto
    next
      assume even: "\<not> odd (int n)"
      hence "even ((int n)*P)" by simp
      with Bn have  "even (P*int n) \<and> is_qfN (P*int n) 3" by (simp add: ac_simps)
      hence "\<exists> B. P*(int n) = 4*B \<and> is_qfN B 3" by (simp only: qf3_even_general)
      then obtain B where B: "P*(int n) = 4*B \<and> is_qfN B 3" by auto
      hence "2^2 dvd (int n)*P" by (simp add: ac_simps)
      moreover have "\<not> 2 dvd P"
      proof (rule ccontr, simp)
        assume "2 dvd P"
        with ass have "odd P \<and> even P" by simp
        thus False by simp
      qed
      moreover have "prime (2::int)" by simp
      ultimately have "2^2 dvd int n"
        by (rule_tac p="2" in prime_power_dvd_cancel_right)
      then obtain im::int where "int n = 4*im" by (auto simp add: dvd_def)
      moreover obtain m::nat where "m = nat im" by auto
      ultimately have m: "n = 4*m" by arith
      with B have "is_qfN (P*int m) 3" by auto
      moreover from m Bn have "m > 0" by auto
      moreover from m Bn have "?A (int m)" by auto
      ultimately have Bm: "?B m" by simp
      from Bn m have "m < n" by arith
      with IH Bm show False by auto
    qed
  qed
  with ass ass2 n show False by auto
qed

lemma qf3_oddprimedivisor:
  "\<lbrakk> prime (P::int); odd P; coprime a b; P dvd (a^2+3*b^2) \<rbrakk>
  \<Longrightarrow> is_qfN P 3"
proof(induct P arbitrary:a b rule:infinite_descent0_measure[where V="\<lambda>P. nat\<bar>P\<bar>"])
  case (0 x)
  moreover hence "x = 0" by arith
  ultimately show ?case by (simp add: prime_int_iff)
next
  case (smaller x)
  then obtain a b where abx: "prime x \<and> odd x \<and> coprime a b
    \<and> x dvd (a^2+3*b^2) \<and> \<not> is_qfN x 3" by auto
  then obtain M where M: "a^2+3*b^2 = x*M" by (auto simp add: dvd_def)
  let ?A = "a^2 + 3*b^2"
  from abx have x0: "x > 0" by (simp add: prime_int_iff)
  then obtain m where "2*\<bar>a-m*x\<bar>\<le>x" by (auto dest: best_division_abs)
  with abx have "2*\<bar>a-m*x\<bar><x" using odd_two_times_div_two_succ[of x] by presburger
  then obtain c where cm: "c = a-m*x \<and> 2*\<bar>c\<bar> < x" by auto
  from x0 obtain n where "2*\<bar>b-n*x\<bar>\<le>x" by (auto dest: best_division_abs)
  with abx have "2*\<bar>b-n*x\<bar><x" using odd_two_times_div_two_succ[of x] by presburger
  then obtain d where dn: "d = b-n*x \<and> 2*\<bar>d\<bar> < x" by auto
  let ?C = "c^2+3*d^2"
  have C3: "is_qfN ?C 3" by (unfold is_qfN_def, auto)
  have C0: "?C > 0"
  proof -
    have hlp: "(3::int) \<ge> 1" by simp
    have "?C \<ge> 0" by simp
    hence "?C = 0 \<or> ?C > 0" by arith
    moreover
    { assume "?C = 0"
      with hlp have "c=0 \<and> d=0" by (rule qfN_zero)
      with cm dn have "a = m*x \<and> b = n*x" by simp
      hence "x dvd a \<and> x dvd b" by simp
      hence "x dvd gcd a b" by simp
      with abx have False by (auto simp add: prime_int_iff) }
    ultimately show ?thesis by blast
  qed
  have "x dvd ?C"
  proof
    have "?C = \<bar>c\<bar>^2 + 3*\<bar>d\<bar>^2" by (simp only: power2_abs)
    also with cm dn have "\<dots> = (a-m*x)^2 + 3*(b-n*x)^2" by simp
    also have "\<dots> =
      a^2 - 2*a*(m*x) + (m*x)^2 + 3*(b^2 - 2*b*(n*x) + (n*x)^2)"
      by (simp add: algebra_simps power2_eq_square)
    also with abx M have "\<dots> =
      x*M - x*(2*a*m + 3*2*b*n) + x^2*(m^2 + 3*n^2)"
      by (simp only: power_mult_distrib distrib_left ac_simps, auto)
    finally show "?C = x*(M - (2*a*m + 3*2*b*n) + x*(m^2 + 3*n^2))"
      by (simp add: power2_eq_square distrib_left right_diff_distrib)
  qed
  then obtain y where y: "?C = x*y" by (auto simp add: dvd_def)
  have yx: "y < x"
  proof (rule ccontr)
    assume "\<not> y < x" hence xy: "x-y \<le> 0" by simp
    have hlp: "2*\<bar>c\<bar> \<ge> 0 \<and> 2*\<bar>d\<bar> \<ge> 0 \<and> (3::nat) > 0" by simp
    from y have "4*x*y = 2^2*c^2 + 3*2^2*d^2" by simp
    hence "4*x*y = (2*\<bar>c\<bar>)^2 + 3*(2*\<bar>d\<bar>)^2"
      by (auto simp add: power_mult_distrib)
    with cm dn hlp have "4*x*y < x^2 + 3*(2*\<bar>d\<bar>)^2"
      and "(3::int) > 0 \<and> (2*\<bar>d\<bar>)^2 < x^2"
            using power_strict_mono [of "2*\<bar>b\<bar>" x 2 for b]
      by auto
    hence "x*4*y < x^2 + 3*x^2" by (auto)
    also have "\<dots> = x*4*x" by (simp add: power2_eq_square)
    finally have contr: "(x-y)*(4*x) > 0" by (auto simp add: right_diff_distrib)
    show False
    proof (cases)
      assume "x-y = 0" with contr show False by auto
    next
      assume "\<not> x-y =0" with xy have "x-y < 0" by simp
      moreover from x0 have "4*x > 0" by simp
      ultimately have "4*x*(x-y) < 4*x*0" by (simp only: zmult_zless_mono2)
      with contr show False by auto
    qed
  qed
  have y0: "y > 0"
  proof (rule ccontr)
    assume "\<not> y > 0"
    hence "y \<le> 0" by simp
    moreover have "y \<noteq> 0"
    proof (rule ccontr)
      assume "\<not> y\<noteq>0" hence "y=0" by simp
      with y and C0 show False by auto
    qed
    ultimately have "y < 0" by simp
    with x0 have "x*y < x*0" by (simp only: zmult_zless_mono2)
    with C0 y show False by simp
  qed
  let ?g = "gcd c d"
  have "c \<noteq> 0 \<or> d \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> (c\<noteq>0 \<or> d\<noteq>0)" hence "c=0 \<and> d=0" by simp
    with C0 show False by simp
  qed
  then obtain e f where ef: "c = ?g*e \<and> d = ?g * f \<and> coprime e f"
    using gcd_coprime_exists[of c d] gcd_pos_int[of c d] by (auto simp: mult.commute)
  have g2nonzero: "?g^2 \<noteq> 0"
  proof (rule ccontr, simp)
    assume "c = 0 \<and> d = 0"
    with C0 show False by simp
  qed
  let ?E = "e^2 + 3*f^2"
  have E3: "is_qfN ?E 3" by (unfold is_qfN_def, auto)
  have CgE: "?C = ?g^2 * ?E"
  proof -
    have "?g^2 * ?E = (?g*e)^2 + 3*(?g*f)^2"
      by (simp add: distrib_left power_mult_distrib)
    with ef show ?thesis by simp
  qed
  hence "?g^2 dvd ?C" by (simp add: dvd_def)
  with y have g2dvdxy: "?g^2 dvd y*x" by (simp add: ac_simps)
  moreover have "coprime x (?g^2)"
  proof -
    let ?h = "gcd ?g x"
    have "?h dvd ?g" and "?g dvd c" by blast+
    hence "?h dvd c" by (rule dvd_trans)
    have "?h dvd ?g" and "?g dvd d" by blast+
    hence "?h dvd d" by (rule dvd_trans)
    have "?h dvd x" by simp
    hence "?h dvd m*x" by (rule dvd_mult)
    with \<open>?h dvd c\<close> have "?h dvd c+m*x" by (rule dvd_add)
    with cm have "?h dvd a" by simp
    from \<open>?h dvd x\<close> have "?h dvd n*x" by (rule dvd_mult)
    with \<open>?h dvd d\<close> have "?h dvd d+n*x" by (rule dvd_add)
    with dn have "?h dvd b" by simp
    with \<open>?h dvd a\<close> have "?h dvd gcd a b" by simp
    with abx have "?h dvd 1" by simp
    hence "?h = 1" by simp
    hence "coprime (?g^2) x" by (auto intro: gcd_eq_1_imp_coprime)
    thus ?thesis by (simp only: ac_simps)
  qed
  ultimately have "?g^2 dvd y"
    by (auto simp add: ac_simps coprime_dvd_mult_right_iff)
  then obtain w where w: "y = ?g^2 * w" by (auto simp add: dvd_def)
  with CgE y g2nonzero have Ewx: "?E = x*w" by auto
  have "w>0"
  proof (rule ccontr)
    assume "\<not> w>0" hence "w \<le> 0" by auto
    hence "w=0 \<or> w<0" by auto
    moreover
    { assume "w=0" with w y0 have False by auto }
    moreover
    { assume wneg: "w<0"
      have "?g^2 \<ge> 0" by (rule zero_le_power2)
      with g2nonzero have "?g^2 > 0" by arith
      with wneg have "?g^2*w < ?g^2*0" by (simp only: zmult_zless_mono2)
      with w y0 have False by auto }
    ultimately show False by blast
  qed
  have w_le_y: "w \<le> y"
  proof (rule ccontr)
    assume "\<not> w \<le> y"
    hence wy: "w > y" by simp
    have "?g^2 = 1 \<or> ?g^2 > 1"
    proof -
      have "?g^2 \<ge> 0" by (rule zero_le_power2)
      hence "?g^2 =0 \<or> ?g^2 > 0" by auto
      with g2nonzero show ?thesis by arith
    qed
    moreover
    { assume "?g^2 =1" with w wy have False by simp }
    moreover
    { assume g1: "?g^2 >1"
      with \<open>w>0\<close> have "w*1 < w*?g^2" by (auto dest: zmult_zless_mono2)
      with w have "w < y" by (simp add: ac_simps)
      with wy have False by auto }
    ultimately show False by blast
  qed
  from Ewx E3 abx \<open>w>0\<close> have
    "prime x \<and> odd x \<and> w > 0 \<and> is_qfN (x*w) 3 \<and> \<not> is_qfN x 3" by simp
  then obtain z where z: "prime z \<and> odd z \<and> z dvd w \<and> \<not> is_qfN z 3"
    by (frule_tac P="x" in qf3_oddprimedivisor_not, auto)
  from Ewx have "w dvd ?E" by simp
  with z have "z dvd ?E" by (auto dest: dvd_trans)
  with z ef have "prime z \<and> odd z \<and> coprime e f \<and> z dvd ?E \<and> \<not> is_qfN z 3"
    by auto
  moreover have "nat\<bar>z\<bar> < nat\<bar>x\<bar>"
  proof -
    have "z \<le> w"
    proof (rule ccontr)
      assume "\<not> z \<le> w" hence "w < z" by auto
      with \<open>w>0\<close> have "\<not> z dvd w" by (rule zdvd_not_zless)
      with z show False by simp
    qed
    with w_le_y yx have "z < x" by simp
    with z have "\<bar>z\<bar> < \<bar>x\<bar>" by (simp add: prime_int_iff)
    thus ?thesis by auto
  qed
  ultimately show ?case by auto
qed

lemma qf3_cube_prime_impl_cube_form:
  assumes ab_relprime: "coprime a b" and abP: "P^3 = a^2 + 3*b^2"
  and P: "prime P \<and> odd P"
  shows "is_cube_form a b"
proof -
  from abP have qfP3: "is_qfN (P^3) 3" by (auto simp only: is_qfN_def)
  have PvdP3: "P dvd P^3" by (simp add: eval_nat_numeral)
  with abP ab_relprime P have qfP: "is_qfN P 3" by (simp add: qf3_oddprimedivisor)
  then obtain p q where pq: "P = p^2 + 3*q^2" by (auto simp only: is_qfN_def)
  with P abP ab_relprime have "prime (p^2 + 3*q^2) \<and> (3::int) > 1
    \<and> (p^2+3*q^2)^3 = a^2+3*b^2 \<and> coprime a b" by auto
  hence ab: "\<bar>a\<bar> = \<bar>p^3 - 3*3*p*q^2\<bar> \<and> \<bar>b\<bar> = \<bar>3*p^2*q - 3*q^3\<bar>"
    by (rule qfN_cube_prime)
  hence a: "a = p^3 - 9*p*q^2 \<or> a = -(p^3) + 9*p*q^2" by arith
  from ab have b: "b = 3*p^2*q - 3*q^3 \<or> b = -(3*p^2*q) + 3*q^3" by arith
  obtain r s where r: "r = -p" and s: "s = -q"  by simp
  show ?thesis
  proof (cases)
    assume a1: "a = p^3- 9*p*q^2"
    show ?thesis
    proof (cases)
      assume b1: "b = 3*p^2*q - 3*q^3"
      with a1 show ?thesis by (unfold is_cube_form_def, auto)
    next
      assume "\<not> b = 3*p^2*q - 3*q^3"
      with b have "b = - 3*p^2*q + 3*q^3" by simp
      with s have "b = 3*p^2*s - 3*s^3" by simp
      moreover from a1 s have "a = p^3 - 9*p*s^2" by simp
      ultimately show ?thesis by (unfold is_cube_form_def, auto)
    qed
  next
    assume "\<not> a = p^3 - 9*p*q^2"
    with a have "a = -(p^3) + 9*p*q^2" by simp
    with r have ar: "a = r^3 - 9*r*q^2" by simp
    show ?thesis
    proof (cases)
      assume b1: "b = 3*p^2*q - 3*q^3"
      with r have "b = 3*r^2*q - 3*q^3" by simp
      with ar show ?thesis by (unfold is_cube_form_def, auto)
    next
      assume "\<not> b = 3*p^2*q - 3*q^3"
      with b have "b = - 3*p^2*q + 3*q^3" by simp
      with r s have "b = 3*r^2*s - 3*s^3" by simp
      moreover from ar s have "a = r^3 - 9*r*s^2" by simp
      ultimately show ?thesis by (unfold is_cube_form_def, auto)
    qed
  qed
qed

lemma cube_form_mult: "\<lbrakk> is_cube_form a b; is_cube_form c d; \<bar>e\<bar> = 1 \<rbrakk>
  \<Longrightarrow> is_cube_form (a*c+e*3*b*d) (a*d-e*b*c)"
proof -
  assume ab: "is_cube_form a b" and c_d: "is_cube_form c d" and e: "\<bar>e\<bar> = 1"
  from ab obtain p q where pq: "a = p^3 - 9*p*q^2 \<and> b = 3*p^2*q - 3*q^3"
    by (auto simp only: is_cube_form_def)
  from c_d obtain r s where rs: "c = r^3 - 9*r*s^2 \<and> d = 3*r^2*s - 3*s^3"
    by (auto simp only: is_cube_form_def)
  let ?t = "p*r + e*3*q*s"
  let ?u = "p*s - e*r*q"
  have e2: "e^2=1"
  proof -
    from e have "e=1 \<or> e=-1" by linarith
    moreover
    { assume "e=1" hence ?thesis by auto }
    moreover
    { assume "e=-1" hence ?thesis by simp }
    ultimately show ?thesis by blast
  qed
  hence "e*e^2 = e" by simp
  hence e3: "e*1 = e^3" by (simp only: power2_eq_square power3_eq_cube)
  have "a*c+e*3*b*d = ?t^3 - 9*?t*?u^2"
  proof -
    have "?t^3 - 9*?t*?u^2 = p^3*r^3 + e*9*p^2*q*r^2*s + e^2*27*p*q^2*r*s^2
      + e^3*27*q^3*s^3 - 9*p*p^2*r*s^2 + e*18*p^2*q*r^2*s - e^2*9*p*q^2*(r*r^2)
      - e*27*p^2*q*(s*s^2) + e^2*54*p*q^2*r*s^2 - e*e^2*27*(q*q^2)*r^2*s"
      by (simp add: eval_nat_numeral field_simps)
    also with e2 e3 have "\<dots> =
      p^3*r^3 + e*27*p^2*q*r^2*s + 81*p*q^2*r*s^2 + e*27*q^3*s^3
      - 9*p^3*r*s^2 - 9*p*q^2*r^3 - e*27*p^2*q*s^3 - e*27*q^3*r^2*s"
      by (simp add: power2_eq_square power3_eq_cube)
    also with pq rs have "\<dots> = a*c + e*3*b*d"
      by (simp only: left_diff_distrib right_diff_distrib ac_simps)
    finally show ?thesis by auto
  qed
  moreover have "a*d-e*b*c = 3*?t^2*?u - 3*?u^3"
  proof -
    have "3*?t^2*?u - 3*?u^3 =
      3*(p*p^2)*r^2*s - e*3*p^2*q*(r*r^2) + e*18*p^2*q*r*s^2
      - e^2*18*p*q^2*r^2*s + e^2*27*p*q^2*(s*s^2) - e*e^2*27*(q*q^2)*r*s^2
      - 3*p^3*s^3 + e*9*p^2*q*r*s^2 - e^2*9*p*q^2*r^2*s + e^3*3*r^3*q^3"
      by (simp add: eval_nat_numeral field_simps)
    also with e2 e3 have "\<dots> = 3*p^3*r^2*s - e*3*p^2*q*r^3 + e*18*p^2*q*r*s^2
      - 18*p*q^2*r^2*s + 27*p*q^2*s^3 - e*27*q^3*r*s^2 - 3*p^3*s^3
      + e*9*p^2*q*r*s^2 - 9*p*q^2*r^2*s + e*3*r^3*q^3"
      by (simp add: power2_eq_square power3_eq_cube)
    also with pq rs have "\<dots> = a*d-e*b*c"
      by (simp only: left_diff_distrib right_diff_distrib ac_simps)
    finally show ?thesis by auto
  qed
  ultimately show ?thesis by (auto simp only: is_cube_form_def)
qed

lemma qf3_cube_primelist_impl_cube_form: "\<lbrakk> (\<forall>p\<in>set_mset ps. prime p); odd (int (\<Prod>i\<in>#ps. i)) \<rbrakk> \<Longrightarrow>
  (!! a b. coprime a b \<Longrightarrow> a^2 + 3*b^2 = (int(\<Prod>i\<in>#ps. i))^3 \<Longrightarrow> is_cube_form a b)"
proof (induct ps)
  case empty hence ab1: "a^2 + 3*b^2 = 1" by simp
  have b0: "b=0"
  proof (rule ccontr)
    assume "b\<noteq>0"
    hence "b^2>0" by simp
    hence "3*b^2 > 1" by arith
    with ab1 have "a^2 < 0" by arith
    moreover have "a^2 \<ge> 0" by (rule zero_le_power2)
    ultimately show False by auto
  qed
  with ab1 have a1: "(a=1 \<or> a=-1)" by (auto simp add: power2_eq_square zmult_eq_1_iff)
  then obtain p and q where "p=a" and "q=(0::int)" by simp
  with a1 and b0 have "a = p^3 - 9*p*q^2 \<and> b = 3*p^2*q - 3*q^3" by auto
  thus "is_cube_form a b" by (auto simp only: is_cube_form_def)
next
  case (add p ps) hence ass: "coprime a b \<and> odd (int(\<Prod>i\<in>#ps + {#p#}. i))
    \<and> a^2+3*b^2 = int(\<Prod>i\<in>#ps + {#p#}. i)^3 \<and>  (\<forall>a\<in>set_mset ps. prime a) \<and> prime (int p)"
    and IH: "!! u v. coprime u v \<and> u^2+3*v^2 = int(\<Prod>i\<in>#ps. i)^3
    \<and> odd (int(\<Prod>i\<in>#ps. i)) \<Longrightarrow> is_cube_form u v"
    by auto
  then have "coprime a b"
    by simp
  let ?w = "int (\<Prod>i\<in>#ps + {#p#}. i)"
  let ?X = "int (\<Prod>i\<in>#ps. i)"
  let ?p = "int p"
  have ge3_1: "(3::int) \<ge> 1" by auto
  have pw: "?w = ?p * ?X \<and> odd ?p \<and> odd ?X"
  proof (safe)
    have "(\<Prod>i\<in>#ps + {#p#}. i) = p * (\<Prod>i\<in>#ps. i)" by simp
    thus wpx: "?w = ?p * ?X" by (auto simp only: of_nat_mult [symmetric])
    with ass show "even ?p \<Longrightarrow> False" by auto
    from wpx have "?w = ?X*?p" by simp
    with ass show "even ?X \<Longrightarrow> False" by simp
  qed
  have "is_qfN ?p 3"
  proof -
    from ass have "a^2+3*b^2 = (?p*?X)^3" by (simp add: mult.commute)
    hence "?p dvd a^2+3*b^2" by (simp add: eval_nat_numeral field_simps)
    moreover from ass have "prime ?p" and "coprime a b" by simp_all
    moreover from pw have "odd ?p" by simp
    ultimately show ?thesis by (simp add: qf3_oddprimedivisor)
  qed
  then obtain \<alpha> \<beta> where alphabeta: "?p = \<alpha>^2 + 3*\<beta>^2"
    by (auto simp add: is_qfN_def)
  have "\<alpha> \<noteq> 0"
  proof (rule ccontr, simp)
    assume "\<alpha> = 0" with alphabeta have "3 dvd ?p" by auto
    with pw have w3: "3 dvd ?w" by (simp only: dvd_mult2)
    then obtain v where "?w = 3*v" by (auto simp add: dvd_def)
    with ass have vab: "27*v^3 = a^2 + 3*b^2" by simp
    hence "a^2 = 3*(9*v^3 - b^2)" by auto
    hence "3 dvd a^2" by (unfold dvd_def, blast)
    moreover have "prime (3::int)" by simp
    ultimately have a3: "3 dvd a" using prime_dvd_power_int[of "3::int" a 2] by fastforce
    then obtain c where c: "a = 3*c" by (auto simp add: dvd_def)
    with vab have "27*v^3 = 9*c^2 + 3*b^2" by (simp add: power_mult_distrib)
    hence "b^2 = 3*(3*v^3 - c^2)" by auto
    hence "3 dvd b^2" by (unfold dvd_def, blast)
    moreover have "prime (3::int)" by simp
    ultimately have "3 dvd b" using prime_dvd_power_int[of "3::int" b 2] by fastforce
    with a3 have "3 dvd gcd a b" by simp
    with ass show False by simp
  qed
  moreover from alphabeta pw ass have
    "prime (\<alpha>^2 + 3*\<beta>^2) \<and> odd (\<alpha>^2+3*\<beta>^2) \<and> (3::int) \<ge> 1" by auto
  ultimately obtain c d where cdp:
    "(\<alpha>^2+3*\<beta>^2)^3 = c^2+3*d^2 \<and> coprime c (3*d)"
    by (blast dest: qfN_oddprime_cube)
  with ass pw alphabeta have "\<exists> u v. a^2+3*b^2 = (u^2 + 3*v^2)*(c^2+3*d^2)
    \<and> coprime u v \<and> (\<exists> e. a = c*u+e*3*d*v \<and> b = c*v-e*d*u \<and> \<bar>e\<bar> = 1)"
    by (rule_tac A="?w" and n="3" in qfN_power_div_prime, auto)
  then obtain u v e where uve: "a^2+3*b^2 = (u^2+3*v^2)*(c^2+3*d^2)
    \<and> coprime u v \<and> a = c*u+e*3*d*v \<and> b = c*v-e*d*u \<and> \<bar>e\<bar> = 1" by blast
  moreover have "is_cube_form u v"
  proof -
    have uvX: "u^2+3*v^2 = ?X^3"
    proof -
      from ass have p0: "?p \<noteq> 0" by (simp add: prime_int_iff)
      from pw have "?p^3*?X^3 = ?w^3" by (simp add: power_mult_distrib)
      also with ass have "\<dots> = a^2+3*b^2" by simp
      also with uve have "\<dots> = (u^2+3*v^2)*(c^2+3*d^2)" by auto
      also with cdp alphabeta have "\<dots> = ?p^3 * (u^2+3*v^2)" by (simp only: ac_simps)
      finally have "?p^3*(u^2+3*v^2-?X^3) = 0" by auto
      with p0 show ?thesis by auto
    qed
    with pw IH uve show ?thesis by simp
  qed
  moreover have "is_cube_form c d"
  proof -
    have "coprime c d"
    proof (rule coprimeI)
      fix f
      assume "f dvd c" and "f dvd d"
      then have "f dvd c*u + d*(e*3*v) \<and> f dvd c*v-d*(e*u)"
        by simp
      with uve have "f dvd a" and "f dvd b"
        by (auto simp only: ac_simps)
      with \<open>coprime a b\<close> show "is_unit f"
        by (rule coprime_common_divisor)
    qed
    with pw cdp ass alphabeta show ?thesis
      by (rule_tac P="?p" in qf3_cube_prime_impl_cube_form, auto)
  qed
  ultimately show "is_cube_form a b" by (simp only: cube_form_mult)
qed

lemma qf3_cube_impl_cube_form:
  assumes ass: "coprime a b \<and> a^2 + 3*b^2 = w^3 \<and> odd w"
  shows "is_cube_form a b"
proof -
  have "0 \<le> w^3" using ass not_sum_power2_lt_zero[of a b] zero_le_power2[of b] by linarith
  hence "0 < w" using ass by auto arith
  define M where "M = prime_factorization (nat w)"
  from \<open>w > 0\<close> have "(\<forall>p\<in>set_mset M. prime p) \<and> w = int (\<Prod>i\<in>#M. i)"
    by (auto simp: M_def prod_mset_prime_factorization_int)
  with ass show ?thesis by (auto dest: qf3_cube_primelist_impl_cube_form)
qed

subsection \<open>Existence ($N=3$)\<close>

text \<open>This part contains the proof that all prime numbers $\equiv 1 \bmod 6$ can be written as $x^2 + 3y^2$.\<close>

text \<open>First show $(\frac{a}{p})(\frac{b}{p}) = (\frac{ab}{p})$, where $p$ is an odd prime.\<close>
lemma Legendre_zmult: "\<lbrakk> p > 2; prime p \<rbrakk>
  \<Longrightarrow> (Legendre (a*b) p) = (Legendre a p)*(Legendre b p)"
proof -
  assume p2: "p > 2" and prp: "prime p"
  from prp have prp': "prime (nat p)"
    by simp
  let ?p12 = "nat(((p) - 1) div 2)"
  let ?Labp = "Legendre (a*b) p"
  let ?Lap = "Legendre a p"
  let ?Lbp = "Legendre b p"
  have h1: "((nat p - 1) div 2) = nat ((p - 1) div 2)" using p2 by auto
  hence "[?Labp = (a*b)^?p12] (mod p)" using prp p2 euler_criterion[of "nat p" "a*b"] 
    by auto
  hence "[a^?p12 * b^?p12 = ?Labp] (mod p)"
    by (simp only: power_mult_distrib cong_sym)
  moreover have "[?Lap * ?Lbp = a^?p12*b^?p12] (mod p)"
    using euler_criterion[of "nat p"] p2 prp' h1 by (simp add: cong_mult)
  ultimately have "[?Lap * ?Lbp = ?Labp] (mod p)"
    using cong_trans by blast
  then obtain k where k: "?Labp = (?Lap*?Lbp) + p * k"
    by (auto simp add: cong_iff_lin)
  have "k=0"
  proof (rule ccontr)
    assume "k \<noteq> 0" hence "\<bar>k\<bar> = 1 \<or> \<bar>k\<bar> > 1" by arith
    moreover
    { assume "\<bar>k\<bar>= 1"
      with p2 have "\<bar>k\<bar>*p > 2" by auto }
    moreover
    { assume k1: "\<bar>k\<bar> > 1"
      with p2 have "\<bar>k\<bar>*2 < \<bar>k\<bar>*p"
        by (simp only: zmult_zless_mono2)
      with k1 have "\<bar>k\<bar>*p > 2" by arith }
   ultimately have "\<bar>k\<bar>*p > 2" by auto
   moreover from p2 have "\<bar>p\<bar> = p" by auto
   ultimately have "\<bar>k*p\<bar> > 2" by (auto simp only: abs_mult)
   moreover from k have "?Labp - ?Lap*?Lbp = k*p" by auto
   ultimately have "\<bar>?Labp - ?Lap*?Lbp\<bar> > 2" by auto
   moreover have "?Labp = 1 \<or> ?Labp = 0 \<or> ?Labp = -1"
     by (simp add: Legendre_def)
   moreover have "?Lap*?Lbp = 1 \<or> ?Lap*?Lbp = 0 \<or> ?Lap*?Lbp = -1"
     by (auto simp add: Legendre_def)
   ultimately show False by auto
 qed
 with k show ?thesis by auto
qed

text \<open>Now show $(\frac{-3}{p}) = +1$ for primes $p \equiv 1 \bmod 6$.\<close>

lemma Legendre_1mod6: "prime (6*m+1) \<Longrightarrow> Legendre (-3) (6*m+1) = 1"
proof -
  let ?p = "6*m+1"
  let ?L = "Legendre (-3) ?p"
  let ?L1 = "Legendre (-1) ?p"
  let ?L3 = "Legendre 3 ?p"
  assume p: "prime ?p"
  from p have p': "prime (nat ?p)" by simp
  have neg1cube: "(-1::int)^3 = -1" by simp
  have m1: "m \<ge> 1"
  proof (rule ccontr)
    assume "\<not> m \<ge> 1" hence "m \<le> 0" by simp
    with p show False by (auto simp add: prime_int_iff)
  qed
  hence pn3: "?p \<noteq> 3" and p2: "?p > 2" by auto
  with p have "?L = (Legendre (-1) ?p) * (Legendre 3 ?p)"
    by (frule_tac a="-1" and b="3" in Legendre_zmult, auto)
  moreover have "[Legendre (-1) ?p = (-1)^nat m] (mod ?p)"
  proof -
    have "nat((?p - 1) div 2) = (nat ?p - 1) div 2" by auto
    hence "[?L1 = (-1)^(nat(((?p) - 1) div 2))] (mod ?p)"
      using euler_criterion[of "nat ?p" "-1"] p' p2 by fastforce
    moreover have "nat ((?p - 1) div 2) = 3* nat m"
    proof -
      have "(?p - 1) div 2 = 3*m" by auto
      hence "nat((?p - 1) div 2) = nat (3*m)" by simp
      moreover have "(3::int) \<ge> 0" by simp
      ultimately show ?thesis by (simp add: nat_mult_distrib)
    qed
    moreover with neg1cube have "(-1::int)^(3*nat m) = (-1)^nat m"
      by (simp only: power_mult)
    ultimately show ?thesis by auto
  qed
  moreover have "?L3 = (-1)^nat m"
  proof -
    have "?L3 * (Legendre ?p 3) = (-1)^nat m"
    proof -
      have "nat ((3 - 1) div 2 * ((6 * m + 1 - 1) div 2)) = 3*nat m" by auto
      hence "?L3 * (Legendre ?p 3) = (-1::int) ^ (3*nat m)"
        using Quadratic_Reciprocity_int[of "3" "?p"] p' pn3 p2 by fastforce
      with neg1cube show ?thesis by (simp add: power_mult)
    qed
    moreover have "Legendre ?p 3 = 1"
    proof -
      have "[1^2 = ?p] (mod 3)" by (unfold cong_iff_dvd_diff dvd_def, auto)
      hence "QuadRes 3 ?p" by (unfold QuadRes_def, blast)
      moreover have "\<not> [?p = 0] (mod 3)"
      proof (rule ccontr, simp)
        assume "[?p = 0] (mod 3)"
        hence "3 dvd ?p" by (simp add: cong_iff_dvd_diff)
        moreover have "3 dvd 6*m" by (auto simp add: dvd_def)
        ultimately have "3 dvd ?p- 6*m" by (simp only: dvd_diff)
        hence "(3::int) dvd 1" by simp
        thus False by auto
      qed
      ultimately show ?thesis by (unfold Legendre_def, auto)
    qed
    ultimately show ?thesis by auto
  qed
  ultimately have "[?L = (-1)^(nat m)*(-1)^(nat m)] (mod ?p)"
    by (metis cong_scalar_right)
  hence "[?L = (-1)^((nat m)+(nat m))] (mod ?p)" by (simp only: power_add)
  moreover have "(nat m)+(nat m) = 2*(nat m)" by auto
  ultimately have "[?L = (-1)^(2*(nat m))] (mod ?p)" by simp
  hence "[?L = ((-1)^2)^(nat m)] (mod ?p)" by (simp only: power_mult)
  hence "[1 = ?L] (mod ?p)" by (auto simp add: cong_sym)
  hence "?p dvd 1 - ?L" by (simp only: cong_iff_dvd_diff)
  moreover have "?L = -1 \<or> ?L = 0 \<or> ?L = 1" by (simp add: Legendre_def)
  ultimately have "?p dvd 2 \<or> ?p dvd 1 \<or> ?L = 1" by auto
  moreover
  { assume "?p dvd 2 \<or> ?p dvd 1"
    with p2 have False by (auto simp add: zdvd_not_zless) }
  ultimately show ?thesis by auto
qed

text \<open>Use this to prove that such primes can be written as $x^2 + 3y^2$.\<close>

lemma qf3_prime_exists: "prime (6*m+1::int) \<Longrightarrow> \<exists> x y. 6*m+1 = x^2 + 3*y^2"
proof -
  let ?p = "6*m+1"
  assume p: "prime ?p"
  hence "Legendre (-3) ?p = 1" by (rule Legendre_1mod6)
  moreover
  { assume "\<not> QuadRes ?p (-3)"
    hence "Legendre (-3) ?p \<noteq> 1" by (unfold Legendre_def, auto) }
  ultimately have "QuadRes ?p (-3)" by auto
  then obtain s where s: "[s^2 = -3] (mod ?p)" by (auto simp add: QuadRes_def)
  hence "?p dvd s^2 - (-3::int)" by (unfold cong_iff_dvd_diff, simp)
  moreover have "s^2 -(-3::int) = s^2 + 3" by arith
  ultimately have "?p dvd s^2 + 3*1^2" by auto
  moreover have "coprime s 1" by auto
  moreover have "odd ?p"
  proof -
    have "?p = 2*(3*m)+1" by simp
    thus ?thesis by simp
  qed
  moreover from p have "prime ?p" by simp
  ultimately have "is_qfN ?p 3" using qf3_oddprimedivisor by blast
  thus ?thesis by (unfold is_qfN_def, auto)
qed

end

end
