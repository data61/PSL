(*  Title:      TwoSquares.thy
    Authors:    Roelof Oosterhuis, 2007  Rijksuniversiteit Groningen
                Jaime Mendizabal Roche, 2016
*)

theory TwoSquares
imports
  "HOL-Number_Theory.Number_Theory"
begin

context
  
  fixes sum2sq_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  defines "sum2sq_nat a b \<equiv> a^2+b^2"
  
  fixes is_sum2sq_nat :: "nat \<Rightarrow> bool"
  defines "is_sum2sq_nat n \<equiv> (\<exists> a b. n = sum2sq_nat a b)"
  
begin

(* TODO: move this lemma to the distribution (?). (It is used also in QuadForm and FourSquares) *)
private lemma best_division_abs: "(n::int) > 0 \<Longrightarrow> \<exists> k. 2 * \<bar>a - k*n\<bar> \<le> n"
proof -
  assume a: "n > 0"
  define k where "k = a div n"
  hence h: "a - k * n = a mod n" by (simp add: mod_div_mult_eq algebra_simps)
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

private definition
  sum2sq_int :: "int \<times> int \<Rightarrow> int" where
  "sum2sq_int = (\<lambda>(a,b). a^2+b^2)"

private definition
  is_sum2sq_int :: "int \<Rightarrow> bool" where
  "is_sum2sq_int n \<longleftrightarrow> (\<exists> a b. n = sum2sq_int(a,b))"

private lemma sum2sq_int_nat_eq: "sum2sq_nat a b = sum2sq_int (a, b)"
  unfolding sum2sq_nat_def sum2sq_int_def by simp

private lemma is_sum2sq_int_nat_eq: "is_sum2sq_nat n = is_sum2sq_int (int n)"
  unfolding is_sum2sq_nat_def is_sum2sq_int_def
proof
  assume "\<exists>a b. n = sum2sq_nat a b"
  thus "\<exists>a b. int n = sum2sq_int (a, b)" using sum2sq_int_nat_eq by force
next
  assume "\<exists>a b. int n = sum2sq_int (a, b)"
  then obtain a b where "int n = sum2sq_int (a, b)" by blast
  hence "int n = sum2sq_int (int (nat \<bar>a\<bar>), int (nat \<bar>b\<bar>))" unfolding sum2sq_int_def by simp
  hence "int n = int (sum2sq_nat (nat \<bar>a\<bar>) (nat \<bar>b\<bar>))" using sum2sq_int_nat_eq by presburger
  thus "\<exists>a b. n = sum2sq_nat a b" by auto
qed

private lemma product_two_squares_aux: "sum2sq_int(a, b) * sum2sq_int(c, d) = sum2sq_int(a*c - b*d, a*d + b*c)"
  unfolding power2_eq_square sum2sq_int_def by (simp add: algebra_simps)

private lemma product_two_squares_int: "is_sum2sq_int m \<Longrightarrow> is_sum2sq_int n \<Longrightarrow> is_sum2sq_int (m*n)"
  by (unfold is_sum2sq_int_def, auto simp only: product_two_squares_aux, blast)

private lemma product_two_squares_nat: "is_sum2sq_nat m \<Longrightarrow> is_sum2sq_nat n \<Longrightarrow> is_sum2sq_nat (m*n)"
  using product_two_squares_int is_sum2sq_int_nat_eq by simp

private lemma sots1_aux:
  assumes "prime (4*k+3)"
  assumes "odd (multiplicity (4*k+3) n)"
  shows "\<not> is_sum2sq_nat n"
proof
  assume "is_sum2sq_nat n"
  then obtain a b where h1: "n = a^2 + b^2"  unfolding is_sum2sq_nat_def sum2sq_nat_def by blast
  have ab_nz: "a \<noteq> 0 \<or> b \<noteq> 0" by (rule ccontr) (insert assms, auto simp: h1) 
  let ?p = "4*k+3"
  let ?g = "gcd a b"
  have h2: "?g \<noteq> 0" using assms(2) h1 odd_pos by fastforce
  then obtain a' b' where h3: "a = a' * ?g" "b = b' * ?g" "coprime a' b'"
    using gcd_coprime_exists by blast
  have "?g^2 dvd n" using dvd_add h1 by auto
  then obtain m where h4: "m * ?g^2 = n" using dvd_div_mult_self by blast
  also have "\<dots> = (a' * ?g)^2 + (b' * ?g)^2" unfolding h1 using h3 by presburger
  also have "\<dots> = ?g^2 * a'^2 + ?g^2 * b'^2" unfolding power2_eq_square by simp
  finally have "?g^2 * m = ?g^2 * (a'^2 + b'^2)" by (simp add: distrib_left mult.commute)
  hence h5: "m = a'^2 + b'^2" using h2 by auto
  let ?mul = "multiplicity ?p ?g"
  have "multiplicity ?p (?g^2) = ?mul + ?mul"
    unfolding power2_eq_square using h2 assms 
    by (subst prime_elem_multiplicity_mult_distrib) simp_all
  hence "even (multiplicity ?p (?g^2))" by simp
  moreover have "m \<noteq> 0" using assms(2) h4 odd_pos by fastforce
  ultimately have "odd (multiplicity ?p m)"
    using assms ab_nz by (simp_all add: h4 [symmetric] prime_elem_multiplicity_mult_distrib)
  hence "?p dvd m" using not_dvd_imp_multiplicity_0 by force
  hence h6: "?p dvd a'^2+b'^2" using h5 by auto
  {
    assume "?p dvd a'^2"
    moreover hence "?p dvd b'^2" using h6 dvd_add_right_iff by blast
    ultimately have "?p dvd a'" "?p dvd b'" using assms(1) prime_dvd_power_nat by blast+
    hence "False"
      using assms(1) h3(3) coprime_common_divisor_nat[of a' b' ?p] not_prime_1 by linarith
  }
  hence "\<not> (?p dvd a'^2)" ..
  hence h7: "\<not> (?p dvd a')" using assms(1)
    by (simp add: power2_eq_square prime_dvd_mult_iff)
  hence "coprime ?p a'"
    using assms(1) by (simp add: prime_imp_coprime)
  thm prime_imp_coprime_nat
  moreover have "a' \<noteq> 0" using h7 dvd_0_right[of ?p] by meson
  ultimately obtain ainv aux where "a' * ainv = ?p * aux + 1"
    using bezout_nat[of "a'" ?p]
    by (auto simp: ac_simps)
  hence "[a' * ainv = 1] (mod ?p)" using cong_to_1'_nat by auto
  from cong_mult [OF this this] have h11: "[1 = ainv^2 * a'^2] (mod ?p)"
    unfolding power2_eq_square by (simp add: algebra_simps cong_sym)
  let ?bdiva = "ainv * b'"
  have "[ainv^2 * (a'^2 + b'^2) = 0] (mod ?p)"
    using h6 cong_dvd_modulus_nat cong_mult_self_right by blast 
  from cong_add [OF h11 this] have "[1 + ainv^2 * b'^2 = 0] (mod ?p)"
    unfolding add_mult_distrib2 using cong_add_lcancel_nat[of "ainv^2 * a'^2"]
    by fastforce
  hence h8: "[?bdiva^2 + 1 = 0] (mod ?p)" by (simp add: power_mult_distrib)
  {
    assume "?p dvd ?bdiva"
    hence "?p dvd (?bdiva^2)" by (simp add: assms(1) prime_dvd_power_nat_iff)
    hence "[?bdiva^2 = 0] (mod ?p)" using cong_altdef_nat by auto
    hence "[?bdiva^2 +1 = 1] (mod ?p)" using cong_add_rcancel_0_nat by blast
    from this h8 have "[0 = 1] (mod ?p)" using cong_sym cong_trans by blast
    hence "?p dvd 1" using cong_0_1_nat by auto
    hence "False" using assms(1) by simp
  }
  hence "\<not> (?p dvd ?bdiva)" ..
  hence h9: "[?bdiva^(?p-1) = 1] (mod ?p)"
    using assms(1) fermat_theorem [of ?p ?bdiva] by simp
  have h10: "?p\<ge>3" by simp
  have h11: "[?bdiva^(4*k+2) = 1] (mod ?p)" using h9 by auto
  have "[(?bdiva^2 + 1)^2 = 0] (mod ?p)" using h8 cong_pow [of "?bdiva^2 + 1" 0 ?p 2] by auto
  moreover have "?bdiva ^ 4 = (?bdiva ^ 2) ^ 2" by auto
  hence "(?bdiva^2 + 1)^2 = ?bdiva^4 + ?bdiva^2 + ?bdiva^2 + 1"
    by (auto simp: algebra_simps power2_eq_square)
  ultimately have "[?bdiva^4 + ?bdiva^2 + ?bdiva^2 + 1 = 0] (mod ?p)" by simp
  moreover have "[?bdiva^4 + ?bdiva^2 + (?bdiva^2 + 1) = ?bdiva^4 + ?bdiva^2 + 0] (mod ?p)"
    using h8 cong_add_lcancel_nat by blast
  ultimately have "[?bdiva^4 + ?bdiva^2 = 0] (mod ?p)" by (simp add: cong_def)
  hence "[?bdiva^4 + ?bdiva^2 + 1 = 0 + 1] (mod ?p)" using cong_add_rcancel_nat by blast
  moreover have "[?bdiva^4 + (?bdiva^2 + 1) = ?bdiva^4 + 0] (mod ?p)"
    using h8 cong_add_lcancel_nat by blast
  ultimately have "[?bdiva^4 = 1] (mod ?p)" by (simp add: cong_def)
  hence "[(?bdiva^4)^k = 1^k] (mod ?p)" using cong_pow by blast
  hence h12: "[?bdiva^(4*k) = 1] (mod ?p)" by (simp add: power_mult)
  hence h13: "[?bdiva^(4*k)*(?bdiva^2 + 1) = 1*(?bdiva^2 + 1)] (mod ?p)"
    using cong_scalar_right by blast
  have "?bdiva^(4*k)*(?bdiva^2 + 1) = ?bdiva^(4*k+2)+?bdiva^(4*k)"
    unfolding add_mult_distrib2 power_add by simp
  hence "[?bdiva^(4*k+2)+?bdiva^(4*k) = ?bdiva^2 + 1] (mod ?p)"
    using h13 unfolding nat_mult_1 by presburger
  moreover have "[?bdiva^(4*k+2) + ?bdiva^(4*k) = 1 + 1] (mod ?p)"
    using h11 h12 cong_add by blast
  ultimately have "[?bdiva^2 + 1 = 2] (mod ?p)"
    by (auto simp add: cong_def)
  hence "[0 = 2] (mod ?p)" using h8 by (simp add: cong_def)
  then have "?p dvd 2" by (auto dest: cong_dvd_iff)
  then show False
    by (auto dest: dvd_imp_le)
qed

private lemma sots1: assumes "is_sum2sq_nat n"
  shows "\<And> k. prime (4*k+3) \<longrightarrow> even (multiplicity (4*k+3) n)"
using sots1_aux assms by blast

private lemma aux_lemma: assumes "[(a::nat) = b] (mod c)" "b < c"
  shows "\<exists> k. a = c*k + b"
proof -
  have "a mod c = b" using assms by (simp add: cong_def mod_if)
  hence "b \<le> a" using assms by auto
  thus ?thesis using cong_le_nat assms(1) by auto
qed

private lemma Legendre_1mod4: "prime (4*k+1::nat) \<Longrightarrow> (Legendre (-1) (4*k+1)) = 1"
proof -
  let ?p = "4*k+1"
  let ?L = "Legendre (-1) ?p"
  assume p: "prime ?p"
  from p have "k \<noteq> 0" by (intro notI) simp_all 
  hence p2: "?p > 2" by simp
  with p have "[?L = (-1)^((?p - 1) div 2)] (mod ?p)"
    by (rule euler_criterion)
  hence "[?L = (-1)^(2 * nat k)] (mod ?p)" by auto
  hence "[?L = 1] (mod ?p)" unfolding power_mult by simp
  hence "?p dvd 1-?L" 
    using cong_iff_dvd_diff dvd_minus_iff[of ?p "?L-1"] by auto
  moreover have "?L=1 \<or> ?L=0 \<or> ?L=-1" by (simp add: Legendre_def)
  ultimately have "?L = 1 \<or> ?p dvd 1 \<or> ?p dvd (2::int)" by auto
  moreover
  { assume "?p dvd 1 \<or> ?p dvd (2::int)"
    with p2 have False by (auto simp add: zdvd_not_zless) }
  ultimately show ?thesis by auto
qed

private lemma qf1_prime_exists: "prime (4*k+1) \<Longrightarrow> is_sum2sq_nat (4*k+1)"
proof -
  let ?p = "4*k+1"
  assume p: "prime ?p"
  hence "Legendre (-1) ?p = 1" by (rule Legendre_1mod4)
  moreover
  { assume "\<not> QuadRes ?p (-1)"
    hence "Legendre (-1) ?p \<noteq> 1" by (unfold Legendre_def, auto) }
  ultimately have "QuadRes ?p (-1)" by auto
  then obtain s1 where s1: "[s1^2 = -1] (mod ?p)" by (auto simp add: QuadRes_def)
  hence s1': "[s1^2 + 1 = 0] (mod ?p)" by (simp add: cong_iff_dvd_diff)
  define s2 where "s2 = nat \<bar>s1\<bar>"
  hence "int (s2^2 + 1) = s1^2 + 1" by auto
  with s1' have "[int (s2^2 + 1) = 0] (mod ?p)" by presburger
  hence s2: "[s2^2 + 1 = 0] (mod ?p)"
    using cong_int_iff by fastforce
  from p have p0: "?p > 0" by simp
  then obtain s where s0p: "0 \<le> s \<and> s < ?p \<and> [s2 = s] (mod ?p)"
    using cong_less_unique_nat[of ?p] by fastforce
  then have "[s^2 = s2^2] (mod ?p)"
    by (simp add: cong_sym cong_pow)
  with s2 have s: "[s^2 + 1 = 0] (mod ?p)"
    using cong_trans cong_add_rcancel_nat by blast
  hence "?p dvd s^2 + 1" using cong_altdef_nat by auto
  then obtain t where t: "s^2 + 1 = ?p*t" by (auto simp add: dvd_def)
  hence "?p*t = sum2sq_nat s 1" by (simp add: sum2sq_nat_def)
  hence qf1pt: "is_sum2sq_nat (?p*t)" by (auto simp add: is_sum2sq_nat_def)
  have t_l_p: "t < ?p"
  proof (rule ccontr)
    assume "\<not> t < ?p"
    hence "t > ?p - 1" by simp
    with p0 have "?p*(?p - 1) < ?p*t" by (simp only: mult_less_mono2)
    also with t have "\<dots> = s^2 + 1" by simp
    also have "\<dots> \<le> ?p*(?p - 1) - ?p + 2"
    proof -
      from s0p have "s \<le> ?p - 1" by (auto simp add: less_le)
      with s0p have "s^2 \<le> (?p - 1)^2" by (simp only: power_mono)
      also have "\<dots> = ?p*(?p - 1) - 1*(?p - 1)" by (simp only: power2_eq_square diff_mult_distrib)
      finally show ?thesis by auto
    qed
    finally have "?p < 2" by simp
    with p show False by (unfold prime_def, auto)
  qed
  have tpos: "t \<ge> 1"
  proof (rule ccontr)
    assume "\<not> t \<ge> 1"
    hence "t < 1" by auto
    moreover
    { assume "t = 0" with t have "s^2 + 1 = 0" by simp }
     moreover
    { assume "t < 0"
      with p0 have "?p*t < ?p*0" by (simp only: zmult_zless_mono2)
      with t have "s^2 + 1 < 0" by auto }
    moreover have "s^2 \<ge> 0" by (simp only: zero_le_power2)
    ultimately show False by (auto simp add: less_le)
  qed
  moreover
  { assume t1: "t > 0"
    then obtain tn where tn: "tn = t - 1" by auto
    have "is_sum2sq_nat (?p*(1+ 0))" (is "?Q 0")
      \<comment> \<open>So, $Q~n =$ there exist $x,y$ such that $x^2+y^2 =(p*(1+ int(n)))$\<close>
    proof (rule ccontr)
      assume nQ1: "\<not> ?Q 0"
      have "(1 + tn) < ?p \<Longrightarrow> \<not> ?Q tn"
      proof (induct tn rule: infinite_descent0)
        case 0
        from nQ1 show "1+ 0 < ?p \<Longrightarrow> \<not> ?Q 0" by simp
      next
        case (smaller n)
        hence n0: "n > 0" and IH: "1+ n < ?p \<and> ?Q n" by auto
        then obtain x y where "x^2 + y^2 = int (?p*(1+ n))"
          using is_sum2sq_int_nat_eq by (unfold is_sum2sq_int_def sum2sq_int_def, auto)
        hence xy: "x^2 + y^2 = (int ?p)*(int (1+ n))" unfolding of_nat_mult by presburger
        let ?n1 = "int (1 + n)"
        from n0 have n1pos: "?n1 > 0" by simp
        then obtain r v where rv: "v = x-r*?n1 \<and> 2*\<bar>v\<bar> \<le> ?n1"
          by (frule_tac n="?n1" in best_division_abs, auto)
        from n1pos obtain s w where sw: "w = y-s*?n1 \<and> 2*\<bar>w\<bar> \<le> ?n1"
          by (frule_tac n="?n1" in best_division_abs, auto)
        let ?C = "v^2 + w^2"
        have "?n1 dvd ?C"
        proof
          from rv sw have "?C = (x-r*?n1)^2 + (y-s*?n1)^2" by simp
          also have "\<dots> = x^2 + y^2 - 2*x*(r*?n1) - 2*y*(s*?n1) + (r*?n1)^2 + (s*?n1)^2"
            unfolding power2_eq_square by (simp add: algebra_simps)
          also with xy have "\<dots> = ?n1*?p - ?n1*(2*x*r) - ?n1*(2*y*s) + ?n1^2*r^2 + ?n1^2*s^2"
            by (simp only: ac_simps power_mult_distrib)
          finally show "?C = ?n1*(?p - 2*x*r - 2*y*s + ?n1*(r^2 + s^2))"
            by (simp only: power_mult_distrib distrib_left ac_simps
              left_diff_distrib right_diff_distrib power2_eq_square)
        qed
        then obtain m1 where m1: "?C = ?n1*m1" by (auto simp add: dvd_def)
        have mn: "m1 < ?n1"
        proof (rule ccontr)
          assume "\<not> m1 < ?n1" hence "?n1-m1 \<le> 0" by simp
          hence "4*?n1 - 4*m1 \<le> 0" by simp
          with n1pos have "2*?n1 - 4*m1 < 0" by simp
          with n1pos have "?n1*(2*?n1 - 4*m1) < ?n1*0" by (simp only: zmult_zless_mono2)
          hence contr: "?n1*(2*?n1- 4*m1) < 0" by simp
          have hlp: "2*\<bar>v\<bar> \<ge> 0 \<and> 2*\<bar>w\<bar> \<ge> 0" by simp
          from m1 have "4*?n1*m1 = 4*v^2 + 4*w^2" by arith
          also have "\<dots> = (2*\<bar>v\<bar>)^2 + (2*\<bar>w\<bar>)^2"
            by (auto simp add: power_mult_distrib)
          also from rv hlp have "\<dots> \<le> ?n1^2 + (2*\<bar>w\<bar>)^2"
            using power_mono [of "2*\<bar>b\<bar>" "1 + int n" 2 for b] by auto
          also from sw hlp have "\<dots> \<le> ?n1^2 + ?n1^2"
            using power_mono [of "2*\<bar>b\<bar>" "1 + int n" 2 for b] by auto
          finally have "?n1*m1*4 \<le> ?n1*?n1*2" by (simp add: power2_eq_square ac_simps)
          hence "?n1*(2*?n1- 4*m1) \<ge> 0" by (simp only: right_diff_distrib ac_simps)
          with contr show False by auto
        qed
        have "?p*m1 = (r*v + s*w + m1)^2 + (r*w - s*v)^2"
        proof -
          from m1 xy have "(?p*?n1)*?C = (x^2+y^2)*(v^2+w^2)" by simp
          also have "\<dots> = (x*v + y*w)^2 + (x*w - y*v)^2"
            by (simp add: eval_nat_numeral field_simps)
          also with rv sw have "\<dots> = ((r*?n1+v)*v + (s*?n1+w)*w)^2 + ((r*?n1+v)*w - (s*?n1+w)*v)^2"
            by simp
          also have "\<dots> = (?n1*(r*v) + ?n1*(s*w) + (v^2+w^2))^2 + (?n1*(r*w) - ?n1*(s*v))^2"
            by (simp add: eval_nat_numeral field_simps)
          also from m1 have "\<dots> = (?n1*(r*v) + ?n1*(s*w) + ?n1*m1)^2 + (?n1*(r*w) - ?n1*(s*v))^2"
            by simp
          finally have "(?p*?n1)*?C = ?n1^2*(r*v + s*w + m1)^2 + ?n1^2*(r*w - s*v)^2"
            by (simp add: eval_nat_numeral field_simps)
          with m1 have "?n1^2*(?p*m1) = ?n1^2*((r*v + s*w + m1)^2 + (r*w - s*v)^2)"
            by (simp only: ac_simps power2_eq_square, simp add: distrib_left)
          hence "?n1^2*(?p*m1 - (r*v+s*w+m1)^2 - (r*w-s*v)^2) = 0"
            by (auto simp add: distrib_left right_diff_distrib)
          moreover from n1pos have "?n1^2 \<noteq> 0" by (simp add: power2_eq_square)
          ultimately show ?thesis by simp
        qed
        hence qf1pm1: "is_sum2sq_int ((int ?p)*m1)"
          by (unfold is_sum2sq_int_def sum2sq_int_def, auto)
        have m1pos: "m1 > 0"
        proof -
          { assume "v^2 + w^2 = 0"
            hence "v = 0 \<and> w = 0" using sum_power2_eq_zero_iff by blast
            with rv sw have "?n1 dvd x \<and> ?n1 dvd y" by (unfold dvd_def, auto)
            hence "?n1^2 dvd x^2 \<and> ?n1^2 dvd y^2" by simp
            hence "?n1^2 dvd x^2 + y^2" by (simp only: dvd_add)
            with xy have "?n1*?n1 dvd ?n1*?p" by (simp only: power2_eq_square ac_simps)
            moreover from n1pos have "?n1 \<noteq> 0" by simp
            ultimately have "?n1 dvd ?p" by (rule zdvd_mult_cancel)
            with n1pos have "?n1 \<ge> 0 \<and> ?n1 dvd ?p" by simp
            with p have "?n1 = 1 \<or> ?n1 = ?p" unfolding prime_nat_iff by presburger
            with IH have "?Q 0" by auto
            with nQ1 have False by simp }
          moreover
          { assume "v^2 + 1*w^2 \<noteq> 0"
            moreover have "v^2 + w^2 \<ge> 0" by simp
            ultimately have vwpos: "v^2 + w^2 > 0" by arith
            with m1 have "m1 \<noteq> 0" by auto
            moreover have "m1 \<ge> 0"
            proof (rule ccontr)
              assume "\<not> m1 \<ge> 0"
              hence "m1 < 0" by simp
              with n1pos have "?n1*m1 < ?n1*0" by (simp only: zmult_zless_mono2)
              with m1 vwpos show False by simp
            qed
            ultimately have ?thesis by auto }
          ultimately show ?thesis by auto
        qed
        hence "1 + int((nat m1) - 1) = m1" by arith
        with qf1pm1 have Qm1: "?Q ((nat m1) - 1)"
          using is_sum2sq_int_nat_eq by (simp add: algebra_simps)
        then obtain mm where tmp: "mm = (nat m1) - 1 \<and> ?Q mm" by auto
        moreover have "mm<n" using tmp mn m1pos by arith
        moreover with IH have "1 + int mm < ?p" by auto
        ultimately show ?case by auto
      qed
      hence "\<not> is_sum2sq_nat (?p*t)" using tn tpos t_l_p by auto
      with qf1pt show False by simp
    qed
    hence ?thesis by auto }
  ultimately show ?thesis by (auto simp add: less_le)
qed

private lemma fermat_two_squares: assumes "prime p" "(\<not> [p = 3] (mod 4))"
  shows "is_sum2sq_nat p"
proof (cases "p=2")
case True
  have "(2::nat)=1^2+1^2" using power2_eq_square by simp
  thus ?thesis unfolding is_sum2sq_nat_def sum2sq_nat_def using True by fast
next
case False
  hence "p > 2" using assms(1) unfolding prime_nat_iff by auto
  hence h1: "odd p" using assms(1) prime_odd_nat by simp
  hence h2: "\<not> [p = 0] (mod 4)" unfolding cong_def by fastforce
  have h3: "\<not> [p = 2] (mod 4)" using h1 cong_dvd_iff [of p 2 2] cong_dvd_modulus_nat by auto
  obtain x where h4: "[p = x] (mod 4) \<and> x<4" by (meson cong_less_unique_nat zero_less_numeral)
  from h1 h2 h3 h4 assms have "x\<noteq>0 \<and> x\<noteq>2 \<and> x\<noteq>3 \<and> x<4" by meson
  hence "x=1" by linarith
  from this h4 have "[p = 1] (mod 4)" by simp
  then obtain k where "p = 4*k+1" using aux_lemma by fastforce
  thus ?thesis using qf1_prime_exists assms by blast
qed

private lemma sots2: assumes "\<And> k. prime (4*k+3) \<longrightarrow> even (multiplicity (4*k+3) n)"
  shows "is_sum2sq_nat n" using assms
proof (induction n rule: nat_less_induct)
case (1 n)
  thus ?case
  proof (cases "n>1")
  case f: False
    thus ?thesis
    proof (cases "n=1")
    case True
      have "(1::nat)=0^2+1^2" by (simp add: power2_eq_square)
      thus ?thesis using True unfolding is_sum2sq_nat_def sum2sq_nat_def by blast
    next
    case False
      hence "n=0" using f by simp
      moreover have "(0::nat)=0^2+0^2" by (simp add: power2_eq_square)
      ultimately show ?thesis unfolding is_sum2sq_nat_def sum2sq_nat_def by blast
    qed
  next
  case True
  then obtain p m where h1: "prime p \<and> n = p * m" using prime_divisor_exists[of n]
    by (auto elim: dvdE)
  with True have m_nz: "m \<noteq> 0" by (intro notI) auto
  from h1 have h2: "m<n" using n_less_m_mult_n[of m p] prime_gt_Suc_0_nat[of p] True by linarith
    {
      assume a1: "[p = 3] (mod 4)"
      then obtain kp where "p = 4*kp+3" using aux_lemma by fastforce
      hence "even (multiplicity p n)" using "1.prems" h1 by auto
      moreover have "multiplicity p n \<noteq> 0" using h1 True m_nz 
        by (subst multiplicity_eq_zero_iff) (auto simp: prime_gt_0_nat)
      ultimately have h3: "multiplicity p n \<ge> 2" by presburger
      have "p dvd m"
      proof (rule ccontr)
        assume a2: "\<not> p dvd m"
        hence "multiplicity p m = 0" by (rule not_dvd_imp_multiplicity_0)
        moreover from h1 have "multiplicity p p = 1" by (intro multiplicity_prime) auto
        moreover have "m > 0" using h1 True by (cases "m = 0") simp_all
        ultimately have "multiplicity p n = 1" using h1
          using prime_elem_multiplicity_mult_distrib [of p p m] m_nz prime_gt_0_nat
          by auto
        thus "False" using h3 by simp
      qed
      then obtain m' where h4: "m = p * m'" using dvdE by blast
      with h1 have h5: "n = p^2 * m'" by (simp add: power2_eq_square)
      have h6: "m'<n"
        using dual_order.strict_trans h1 h2 h4 nat_mult_less_cancel1 prime_gt_0_nat[of p] by blast
      have "\<And> kq. prime (4*kq + 3) \<Longrightarrow> even (multiplicity (4*kq + 3) m')"
      proof -
        fix kq::nat
        let ?q = "4*kq + 3"
        assume a2: "prime ?q"
        {
          assume p: "p=?q"
          hence h7: "multiplicity ?q (p^2) = 2" using h1 
            by (auto intro!: multiplicity_prime_power)
          have "even (multiplicity ?q n)" using 1(2)[of kq] a2 by blast
          also note h5
          also from p h1 h4 m_nz 
            have "multiplicity (4 * kq + 3) (p^2 * m') =
                    Suc (Suc (multiplicity (4 * kq + 3) m'))"
            by (subst prime_elem_multiplicity_mult_distrib) auto
          finally have "even (multiplicity ?q m')" by simp
        }
        moreover {
          assume "p\<noteq>?q"
          from a2 h4 m_nz have "multiplicity ?q n = 
                                  multiplicity (4 * kq + 3) (p\<^sup>2) + multiplicity (4 * kq + 3) m'" 
            unfolding h5 by (subst prime_elem_multiplicity_mult_distrib) simp_all
          also from \<open>p \<noteq> ?q\<close> a2 h1 have "multiplicity ?q (p^2) = 0"
            by (intro multiplicity_distinct_prime_power) simp_all
          finally have "multiplicity ?q n = multiplicity ?q m'" by simp
          moreover have "even (multiplicity ?q n)" using 1(2)[of kq] a2 by blast
          ultimately have "even (multiplicity ?q m')" by simp
        }
        ultimately show "even (multiplicity ?q m')" by blast
      qed
      hence "is_sum2sq_nat m'" by (simp add: 1 h6)
      moreover have "p^2 = p^2 + 0^2" by simp
      hence "is_sum2sq_nat (p^2)" unfolding is_sum2sq_nat_def sum2sq_nat_def by blast
      ultimately have ?thesis using product_two_squares_nat h5 by blast
    } moreover
    {
      assume a1: "\<not> [p = 3] (mod 4)"
      have "\<And> kq. prime (4*kq+3) \<Longrightarrow> even (multiplicity (4*kq+3) m)"
      proof -
        fix kq
        let ?q = "4*(kq::nat) + 3"
        assume a2: "prime ?q"
        { assume "p = ?q"
          then have False using a1 cong_add_rcancel_0_nat [of "4 * kq" 3 4]
            by (auto simp add: cong_def)
        }
        hence "p\<noteq>?q" ..
        
        have "n = p * m" using h1 by simp
        also from h1 a2 m_nz have "multiplicity ?q \<dots> = 
                                  multiplicity (4 * kq + 3) p + multiplicity (4 * kq + 3) m" 
          by (subst prime_elem_multiplicity_mult_distrib) (simp_all add: prime_gt_0_nat)
        also from \<open>p \<noteq> ?q\<close> a2 h1 have "multiplicity ?q p = 0"
          by (intro prime_multiplicity_other) simp_all
        finally have "multiplicity ?q n = multiplicity ?q m" by simp
        moreover have "even (multiplicity ?q n)" using 1(2)[of kq] a2 by blast
        ultimately show "even (multiplicity ?q m)" by simp
      qed
      hence "is_sum2sq_nat m" by (simp add: 1 h2)
      moreover have "is_sum2sq_nat p" using fermat_two_squares a1 h1 by blast
      ultimately have ?thesis using product_two_squares_nat h1 by blast
    } ultimately
    show ?thesis by blast
  qed
qed

theorem sum_of_two_squares:
    "is_sum2sq_nat n \<longleftrightarrow> (\<forall> k. prime (4*k+3) \<longrightarrow> even (multiplicity (4*k+3) n))"
  using sots1[of n] sots2[of n] by blast

private lemma k_mod_eq: "(\<forall>p::nat. prime p \<and> [p = 3] (mod 4) \<longrightarrow> P p) = (\<forall>k. prime (4*k+3) \<longrightarrow> P (4*k+3))"
proof
  assume a1: "\<forall>p. prime p \<and> [p = 3] (mod 4) \<longrightarrow> P p"
  {
    fix k :: nat
    assume "prime (4 * k + 3)"
    moreover hence "[4*k+3 = 3] (mod 4)"
      by (simp add: cong_add_rcancel_0_nat cong_mult_self_left)
    ultimately have "P (4 * k + 3)" using a1 by blast
  }
  thus "\<forall>k. prime (4 * k + 3) \<longrightarrow> P (4 * k + 3)" by blast
next
  assume a1: "\<forall>k. prime (4 * k + 3) \<longrightarrow> P (4 * k + 3)"
  {
    fix p :: nat
    assume "prime p" "[p = 3] (mod 4)"
    moreover with aux_lemma obtain k where "p = 4*k+3" by fastforce
    ultimately have "P p" using a1 by blast
  }
  thus "\<forall>p. prime p \<and> [p = 3] (mod 4) \<longrightarrow> P p" by blast
qed

theorem sum_of_two_squares':
    "is_sum2sq_nat n \<longleftrightarrow> (\<forall> p. prime p \<and> [p = 3] (mod 4) \<longrightarrow> even (multiplicity p n))"
  using sum_of_two_squares k_mod_eq by presburger

theorem sum_of_two_squares_prime: assumes "prime p"
  shows "is_sum2sq_nat p = [p\<noteq>3] (mod 4)"
proof (cases "[p=3] (mod 4)")
case True
  have "odd (multiplicity p p)" using assms by simp
  hence "\<not> (is_sum2sq_nat p)" using assms True sum_of_two_squares' by blast
  with True show ?thesis by simp
qed (simp add: fermat_two_squares assms)

end

end
