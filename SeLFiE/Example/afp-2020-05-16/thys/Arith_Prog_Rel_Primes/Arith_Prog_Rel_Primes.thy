(*
  File:   Arith_Prog_Rel_Primes.thy
  Author: Jose Manuel Rodriguez Caballero, University of Tartu
*)
section \<open>Problem ARITHMETIC PROGRESSIONS (Putnam exam problems 2002)\<close>
theory Arith_Prog_Rel_Primes
  imports
    Complex_Main 
    "HOL-Number_Theory.Number_Theory"
begin

text \<open>
 Statement of the problem (from ~\cite{putnam}): For which integers $n>1$ does the set of positive 
 integers less than and relatively prime to $n$ constitute an arithmetic progression?
 
 The solution of the above problem is theorem @{text arith_prog_rel_primes_solution}.

 First, we will require some auxiliary material before we get started with the actual
 solution.
\<close>

subsection \<open>Auxiliary results\<close>

lemma even_and_odd_parts:
  fixes n::nat
  assumes \<open>n \<noteq> 0\<close>
  shows \<open>\<exists> k q::nat. n = (2::nat)^k*q \<and> odd q\<close>
proof-
  have \<open>prime (2::nat)\<close>
    by simp    
  thus ?thesis
    using prime_power_canonical[where p = "2" and m = "n"]
      assms semiring_normalization_rules(7) by auto    
qed

lemma only_one_odd_div_power2:
  fixes n::nat
  assumes \<open>n \<noteq> 0\<close> and  \<open>\<And> x. x dvd n \<Longrightarrow> odd x \<Longrightarrow> x = 1\<close>
  shows \<open>\<exists> k. n = (2::nat)^k\<close>
  by (metis even_and_odd_parts assms(1) assms(2) dvd_triv_left semiring_normalization_rules(11)
      semiring_normalization_rules(7))

lemma coprime_power2:
  fixes n::nat
  assumes \<open>n \<noteq> 0\<close> and \<open>\<And> x. x < n \<Longrightarrow> (coprime x n \<longleftrightarrow> odd x)\<close>
  shows \<open>\<exists> k. n = (2::nat)^k\<close>
proof-
  have \<open>x dvd n \<Longrightarrow> odd x \<Longrightarrow> x = 1\<close>
    for x
    by (metis neq0_conv One_nat_def Suc_1 Suc_lessI assms(1) assms(2) coprime_left_2_iff_odd
        dvd_refl linorder_neqE_nat nat_dvd_1_iff_1 nat_dvd_not_less not_coprimeI)
  thus ?thesis
    using assms(1) only_one_odd_div_power2 
    by auto 
qed

subsection \<open>Main result\<close>

text \<open>
  The solution to the problem  ARITHMETIC PROGRESSIONS (Putnam exam problems 2002)
\<close>

theorem arith_prog_rel_primes_solution:
  fixes n :: nat
  assumes \<open>n > 1\<close>
  shows \<open>(prime n \<or> (\<exists> k. n = 2^k) \<or> n = 6) \<longleftrightarrow>  
(\<exists> a b m. m \<noteq> 0 \<and> {x | x. x < n \<and> coprime x n} = {a+j*b| j::nat. j < m})\<close>
proof-
  have \<open> (prime n \<or> (\<exists> k. n = 2^k) \<or>  n = 6) \<longleftrightarrow>
 (\<exists> b m. m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*b| j::nat. j < m})\<close>
  proof
    show "\<exists>b m. m \<noteq> 0 \<and> {x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}"
      if "prime n \<or> (\<exists>k. n = 2 ^ k) \<or> n = 6"
    proof-
      have "\<exists>b m. m \<noteq> 0 \<and> {x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}"
        if "prime n"
      proof-
        have \<open>\<exists>m.   m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j| j::nat. j < m}\<close>
        proof-
          have \<open>{x | x :: nat. x < n \<and> coprime x n} =  {x | x :: nat. x \<noteq> 0 \<and> x < n}\<close> 
          proof
            show "{x |x. x < n \<and> coprime x n} \<subseteq> {x |x. x \<noteq> 0 \<and> x < n}"
              by (smt Collect_mono not_le ord_0_nat ord_eq_0 order_refl prime_gt_1_nat that zero_neq_one)
            show "{x |x. x \<noteq> 0 \<and> x < n} \<subseteq> {x |x. x < n \<and> coprime x n}"
              using coprime_commute prime_nat_iff'' that 
              by fastforce              
          qed
          obtain m where \<open>m+1 = n\<close>
            using add.commute assms less_imp_add_positive by blast
          have \<open>{1+j| j::nat. j < (m::nat)} =  {x | x :: nat. x \<noteq> 0 \<and> x < m+1}\<close> 
            by (metis Suc_eq_plus1   \<open>m + 1 = n\<close> gr0_implies_Suc le_simps(3)   less_nat_zero_code   linorder_not_less nat.simps(3) nat_neq_iff  plus_1_eq_Suc )
          hence  \<open>{x | x :: nat. x < n \<and> coprime x n} = {1+j| j::nat. j < (m::nat)}\<close>
            using \<open>{x | x :: nat. x < n \<and> coprime x n} =  {x | x :: nat. x \<noteq> 0 \<and> x < n}\<close>  \<open>m+1 = n\<close> 
            by auto
          from \<open>n > 1\<close> have \<open>m \<noteq> 0\<close> 
            using \<open>m + 1 = n\<close> by linarith
          have \<open>{x | x :: nat. x < n \<and> coprime x n} = {1+j| j::nat. j < m}\<close> 
            using Suc_eq_plus1 \<open>1 < n\<close> \<open>{x |x. x < n \<and> coprime x n} = {1 + j |j. j < m}\<close> 
            by auto
          hence \<open>(\<exists> m.  m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j| j::nat. j < m})\<close>
            using \<open>m \<noteq> 0\<close> 
            by blast
          thus ?thesis by blast
        qed
        hence \<open>\<exists>m.  m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*1| j::nat. j < m}\<close>
          by auto
        thus ?thesis
          by blast 
      qed
      moreover have "\<exists>b m. m \<noteq> 0 \<and> {x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}"
        if "\<exists>k. n = 2 ^ k"
      proof-
        obtain k where \<open>n = 2 ^ k\<close>
          using \<open>\<exists>k. n = 2 ^ k\<close> by auto
        have \<open>k \<noteq> 0\<close> 
          by (metis \<open>1 < n\<close> \<open>n = 2 ^ k\<close> nat_less_le power.simps(1))
        obtain t where \<open>Suc t = k\<close> 
          by (metis \<open>k \<noteq> 0\<close> fib.cases)
        have \<open>n = 2^(Suc t)\<close> 
          by (simp add: \<open>Suc t = k\<close> \<open>n = 2 ^ k\<close>)
        have \<open>{x | x :: nat. x < n \<and> coprime x n} = {1+j*2| j::nat. j < 2^t}\<close>
        proof
          show "{x |x. x < n \<and> coprime x n} \<subseteq> {1 + j * 2 |j. j < 2^t}"
          proof
            fix x
            assume \<open>x \<in> {x |x. x < n \<and> coprime x n}\<close>
            hence \<open>x < n\<close>
              by blast
            have \<open>coprime x n\<close>
              using \<open>x \<in> {x |x. x < n \<and> coprime x n}\<close>
              by blast
            hence \<open>coprime x (2^(Suc k))\<close>
              by (simp add: \<open>k \<noteq> 0\<close> \<open>n = 2 ^ k\<close>)              
            have \<open>odd x\<close>
              using \<open>coprime x n\<close> \<open>k \<noteq> 0\<close> \<open>n = 2 ^ k\<close> 
              by auto 
            then obtain j where \<open>x = 1+j*2\<close>
              by (metis add.commute add.left_commute left_add_twice mult_2_right oddE)
            have \<open>x < 2^k\<close>
              using \<open>n = 2 ^ k\<close> \<open>x < n\<close> \<open>x = 1+j*2\<close> 
              by linarith
            hence \<open>1+j*2 < 2^k\<close>
              using \<open>x = 1+j*2\<close>
              by blast
            hence \<open>j < 2^t\<close>
              using \<open>Suc t = k\<close> by auto              
            thus \<open>x \<in> {1 + j * 2 |j. j < 2^t}\<close>
              using \<open>x = 1+j*2\<close>
              by blast
          qed
          show "{1 + j * 2 |j. j < 2 ^ t} \<subseteq> {x |x. x < n \<and> coprime x n}"
          proof
            fix x::nat
            assume \<open>x \<in> {1 + j * 2 |j. j < 2 ^ t}\<close>
            then obtain j where \<open>x = 1 + j * 2\<close> and \<open>j < 2 ^ t\<close>
              by blast
            have \<open>x < 2*(2^t)\<close>
              using  \<open>x = 1 + j * 2\<close>  \<open>j < 2 ^ t\<close>
              by linarith              
            hence \<open>x < n\<close>
              by (simp add: \<open>n = 2 ^ Suc t\<close>)
            moreover have \<open>coprime x n\<close>
              by (metis (no_types) \<open>\<And>thesis. (\<And>j. \<lbrakk>x = 1 + j * 2; j < 2 ^ t\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>n = 2 ^ k\<close> coprime_Suc_left_nat coprime_mult_right_iff coprime_power_right_iff plus_1_eq_Suc)              
            ultimately show \<open>x \<in> {x |x. x < n \<and> coprime x n}\<close>
              by blast
          qed
        qed
        have \<open>(2::nat)^(t::nat) \<noteq> 0\<close> 
          by simp
        obtain m where \<open>m = (2::nat)^t\<close> by blast
        have \<open>m \<noteq> 0\<close> 
          using \<open>m = 2 ^ t\<close> 
          by auto
        have \<open>{x | x :: nat. x < n \<and> coprime x n} = {1+j*2| j::nat. j < m}\<close>
          using \<open>m = 2 ^ t\<close> \<open>{x |x. x < n \<and> coprime x n} = {1 + j * 2 |j. j < 2 ^ t}\<close> 
          by auto
        from  \<open>m \<noteq> 0\<close>  \<open>{x | x :: nat. x < n \<and> coprime x n} = {1+j*2| j::nat. j < m}\<close>
        show ?thesis by blast
      qed
      moreover have "\<exists>b m. m \<noteq> 0 \<and> {x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}"
        if "n = 6"
      proof-
        have  \<open>{x | x. x < 6 \<and> coprime x 6} = {1+j*4| j::nat. j < 2}\<close>
        proof-
          have \<open>{x | x::nat. x < 6 \<and> coprime x 6} = {1, 5}\<close>
          proof
            show "{u. \<exists>x. u = (x::nat) \<and> x < 6 \<and> coprime x 6} \<subseteq> {1, 5}"
            proof
              fix u::nat
              assume \<open>u \<in> {u. \<exists>x. u = x \<and> x < 6 \<and> coprime x 6}\<close>
              hence \<open>coprime u 6\<close>
                by blast
              have \<open>u < 6\<close>
                using \<open>u \<in> {u. \<exists>x. u = x \<and> x < 6 \<and> coprime x 6}\<close>
                by blast
              moreover have \<open>u \<noteq> 0\<close>
                using \<open>coprime u 6\<close> ord_eq_0 
                by fastforce
              moreover have \<open>u \<noteq> 2\<close>
                using \<open>coprime u 6\<close>
                by auto
              moreover have \<open>u \<noteq> 3\<close>
              proof-
                have \<open>gcd (3::nat) 6 = 3\<close>
                  by auto
                thus ?thesis 
                  by (metis (no_types) \<open>coprime u 6\<close> \<open>gcd 3 6 = 3\<close> coprime_iff_gcd_eq_1 
                      numeral_eq_one_iff semiring_norm(86))
              qed
              moreover have \<open>u \<noteq> 4\<close>
              proof-
                have \<open>gcd (4::nat) 6 = 2\<close>
                  by (metis (no_types, lifting) add_numeral_left gcd_add1 gcd_add2 gcd_nat.idem
                      numeral_Bit0 numeral_One one_plus_numeral semiring_norm(4) semiring_norm(5))
                thus ?thesis
                  using \<open>coprime u 6\<close> coprime_iff_gcd_eq_1 
                  by auto 
              qed
              ultimately have \<open>u = 1 \<or> u = 5\<close>
                by auto
              thus \<open>u \<in> {1, 5}\<close>
                by blast
            qed
            show "{1::nat, 5} \<subseteq> {x |x. x < 6 \<and> coprime x 6}"
            proof-
              have \<open>(1::nat) \<in> {x |x. x < 6 \<and> coprime x 6}\<close>
                by simp                
              moreover have \<open>(5::nat) \<in> {x |x. x < 6 \<and> coprime x 6}\<close>
                by (metis Suc_numeral coprime_Suc_right_nat less_add_one mem_Collect_eq
                    numeral_plus_one semiring_norm(5) semiring_norm(8))                
              ultimately show ?thesis 
                by blast
            qed
          qed
          moreover have \<open>{1+j*4| j::nat. j < 2} = {1, 5}\<close>
            by auto
          ultimately show ?thesis by auto
        qed
        moreover have \<open>(2::nat) \<noteq> 0\<close>
          by simp          
        ultimately have \<open>\<exists> m.  m \<noteq> 0 \<and> {x | x :: nat. x < 6 \<and> coprime x 6} = {1+j*4| j::nat. j < m}\<close>
          by blast
        thus ?thesis
          using that 
          by auto 
      qed
      ultimately show ?thesis
        using that 
        by blast 
    qed
    show "prime n \<or> (\<exists>k. n = 2 ^ k) \<or> n = 6"
      if "\<exists>b m. m \<noteq> 0 \<and> {x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}"
    proof-
      obtain b m where \<open>m \<noteq> 0\<close> and \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close>
        using \<open>\<exists>b m. m \<noteq> 0 \<and> {x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> 
        by auto
      show ?thesis
      proof(cases \<open>n = 2\<close>)
        case True
        thus ?thesis
          by auto 
      next
        case False
        have \<open>b \<le> 4\<close>
        proof(cases \<open>odd b\<close>)
          case True
          show ?thesis
          proof(rule classical)
            assume \<open>\<not>(b \<le> 4)\<close>
            hence \<open>b > 4\<close> 
              using le_less_linear 
              by blast
            obtain m where \<open>m \<noteq> 0\<close> 
              and \<open>{x | x :: nat. x < n \<and> coprime x n} = {1+j*b| j::nat. j < m}\<close>
              using \<open>m \<noteq> 0\<close> \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> 
              by blast
            have \<open>b \<noteq> 0\<close> 
              using \<open>4 < b\<close> 
              by linarith
            have \<open>n = 2 + (m-1)*b\<close> 
            proof-
              have \<open>n-1 \<in> {x | x :: nat. x < n \<and> coprime x n}\<close> 
                using \<open>1 < n\<close> coprime_diff_one_left_nat 
                by auto
              have \<open>n-1 \<in> {1+j*b| j::nat. j < m}\<close> 
                using \<open>n - 1 \<in> {x |x. x < n \<and> coprime x n}\<close> 
                  \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> 
                by blast
              then obtain i::nat where \<open>n-1 = 1+i*b\<close> and \<open>i < m\<close> 
                by blast
              have \<open>i \<le> m-1\<close> 
                using \<open>i < m\<close> 
                by linarith
              have \<open>1 + (m-1)*b \<in> {1+j*b| j::nat. j < m}\<close> 
                using \<open>m \<noteq> 0\<close> 
                by auto
              hence \<open>1 + (m-1)*b \<in> {x | x::nat. x < n \<and> coprime x n}\<close> 
                using \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> 
                by blast
              hence \<open>1 + (m-1)*b < n\<close> 
                by blast
              hence \<open>1 + (m-1)*b \<le> n-1\<close> 
                by linarith
              hence \<open>1 + (m-1)*b \<le> 1+i*b\<close> 
                using \<open>n - 1 = 1 + i * b\<close> 
                by linarith
              hence \<open>(m-1)*b \<le> i*b\<close> 
                by linarith
              hence \<open>m-1 \<le> i\<close> 
                using \<open>b \<noteq> 0\<close> 
                by auto
              hence \<open>m-1 = i\<close> 
                using \<open>i \<le> m - 1\<close> le_antisym 
                by blast
              thus ?thesis 
                using \<open>m \<noteq> 0\<close> \<open>n - 1 = 1 + i * b\<close> 
                by auto
            qed
            have \<open>m \<ge> 2\<close> 
              using \<open>n = 2 + (m - 1)*b\<close> \<open>n \<noteq> 2\<close> 
              by auto
            hence \<open>1+b \<in> {1+j*b| j. j < m}\<close> 
              by fastforce
            hence  \<open>1+b \<in> {x | x::nat. x < n \<and> coprime x n}\<close>
              using \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> 
              by blast
            hence \<open>coprime (1+b) n\<close> 
              by blast
            have \<open>(2::nat) dvd (1+b)\<close> 
              using \<open>odd b\<close> 
              by simp
            hence \<open>coprime (2::nat) n\<close> 
              using \<open>coprime (1 + b) n\<close> coprime_common_divisor coprime_left_2_iff_odd odd_one 
              by blast
            have \<open>(2::nat) < n\<close> 
              using \<open>1 < n\<close> \<open>n \<noteq> 2\<close> 
              by linarith
            have \<open>2 \<in> {x | x :: nat. x < n \<and> coprime x n}\<close> 
              using \<open>2 < n\<close> \<open>coprime 2 n\<close> 
              by blast 
            hence  \<open>2 \<in> {1+j*b| j::nat. j < m}\<close> 
              using \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> 
              by blast
            then obtain j::nat where \<open>2 = 1+j*b\<close> 
              by blast 
            have  \<open>1 = j*b\<close> 
              using \<open>2 = 1+j*b\<close>
              by linarith
            thus ?thesis 
              by simp
          qed
        next
          case False
          hence \<open>even b\<close>
            by simp
          show ?thesis
          proof(rule classical)
            assume \<open>\<not>(b \<le> 4)\<close>
            hence \<open>b > 4\<close> 
              using le_less_linear 
              by blast
            obtain m where  \<open> m \<noteq> 0\<close>
              and \<open>{x | x::nat. x < n \<and> coprime x n} = {1+j*b| j::nat. j < m}\<close>
              using \<open>m \<noteq> 0\<close> \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> 
              by blast
            have \<open>b \<noteq> 0\<close> 
              using \<open>4 < b\<close> 
              by linarith
            have \<open>n = 2 + (m-1)*b\<close> 
            proof-
              have \<open>n-1 \<in> {x | x::nat. x < n \<and> coprime x n}\<close> 
                using \<open>1 < n\<close> coprime_diff_one_left_nat 
                by auto
              have \<open>n-1 \<in> {1+j*b| j::nat. j < m}\<close> 
                using \<open>n - 1 \<in> {x |x. x < n \<and> coprime x n}\<close> 
                  \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> 
                by blast
              then obtain i::nat where \<open>n-1 = 1+i*b\<close> and \<open>i < m\<close> 
                by blast
              have \<open>i \<le> m-1\<close> 
                using \<open>i < m\<close> 
                by linarith
              have \<open>1 + (m-1)*b \<in> {1+j*b| j::nat. j < m}\<close> 
                using \<open>m \<noteq> 0\<close> 
                by auto
              hence \<open>1 + (m-1)*b \<in> {x | x :: nat. x < n \<and> coprime x n}\<close> 
                using \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> 
                by blast
              hence \<open>1 + (m-1)*b < n\<close> 
                by blast
              hence \<open>1 + (m-1)*b \<le> n-1\<close> 
                by linarith
              hence \<open>1 + (m-1)*b \<le> 1+i*b\<close> 
                using \<open>n - 1 = 1 + i * b\<close> 
                by linarith
              hence \<open>(m-1)*b \<le> i*b\<close> 
                by linarith
              hence \<open>m-1 \<le> i\<close> 
                using \<open>b \<noteq> 0\<close> 
                by auto
              hence \<open>m-1 = i\<close> 
                using \<open>i \<le> m - 1\<close> le_antisym 
                by blast
              thus ?thesis 
                using \<open>m \<noteq> 0\<close> \<open>n - 1 = 1 + i * b\<close> 
                by auto
            qed
            obtain k :: nat where \<open>b = 2*k\<close> 
              using \<open>even b\<close>
              by blast
            have \<open>n = 2*(1 + (m-1)*k)\<close>
              using  \<open>n = 2 + (m-1)*b\<close>  \<open>b = 2*k\<close> 
              by simp
            show ?thesis
            proof (cases \<open>odd m\<close>)
              case True
              hence \<open>odd m\<close> by blast
              then obtain t::nat where \<open>m-1 = 2*t\<close> 
                by (metis odd_two_times_div_two_nat)
              have  \<open>n = 2*(1 + b*t)\<close> 
                using \<open>m - 1 = 2 * t\<close> \<open>n = 2 + (m - 1) * b\<close> 
                by auto
              have \<open>t < m\<close> 
                using \<open>m - 1 = 2 * t\<close> \<open>m \<noteq> 0\<close> 
                by linarith
              have \<open>1 + b*t \<in> {1+j*b| j::nat. j < m}\<close> 
                using \<open>t < m\<close> 
                by auto 
              hence \<open>1 + b*t \<in> {x | x::nat. x < n \<and> coprime x n}\<close> 
                using \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> 
                by blast 
              hence \<open>coprime (1 + b*t) n\<close> 
                by auto
              thus ?thesis 
                by (metis (no_types, lifting) \<open>b = 2 * k\<close> \<open>n = 2 * (1 + (m - 1) * k)\<close> \<open>n = 2 * (1 + b * t)\<close> \<open>n = 2 + (m - 1) * b\<close> \<open>n \<noteq> 2\<close> add_cancel_right_right coprime_mult_right_iff coprime_self mult_cancel_left mult_is_0 nat_dvd_1_iff_1)
            next
              case False
              thus ?thesis
              proof(cases \<open>odd k\<close>)
                case True
                hence \<open>odd k\<close>
                  by blast
                have \<open>even (1 + (m - 1) * k)\<close> 
                  by (simp add: False True \<open>m \<noteq> 0\<close>)
                have \<open>coprime (2 + (m - 1) * k) (1 + (m - 1) * k)\<close> 
                  by simp
                have \<open>coprime (2 + (m - 1) * k) n\<close> 
                  using \<open>coprime (2 + (m - 1) * k) (1 + (m - 1) * k)\<close> \<open>even (1 + (m - 1) * k)\<close> 
                    \<open>n = 2 * (1 + (m - 1) * k)\<close> coprime_common_divisor coprime_mult_right_iff
                    coprime_right_2_iff_odd odd_one 
                  by blast
                have \<open>2 + (m - 1) * k < n\<close> 
                  by (metis (no_types, lifting) \<open>even (1 + (m - 1) * k)\<close> \<open>n = 2 * (1 + (m - 1) * k)\<close>
                      add_gr_0 add_mono_thms_linordered_semiring(1) dvd_add_left_iff dvd_add_triv_left_iff dvd_imp_le le_add2 le_neq_implies_less less_numeral_extra(1) mult_2 odd_one)
                have \<open>2 + (m - 1) * k  \<in> {x | x :: nat. x < n \<and> coprime x n}\<close> 
                  using \<open>2 + (m - 1) * k < n\<close> \<open>coprime (2 + (m - 1) * k) n\<close> 
                  by blast
                hence \<open>2 + (m - 1) * k  \<in> {1 + j * b |j. j < m}\<close> 
                  using \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> 
                  by blast
                then obtain j::nat where  \<open>2 + (m - 1) * k  = 1 + j * b\<close> and \<open>j < m\<close>
                  by blast
                have  \<open>1 + (m - 1) * k  = j * b\<close>
                  using \<open>2 + (m - 1) * k  = 1 + j * b\<close>
                  by simp
                hence  \<open>1 + (m - 1) * k  = j * (2*k)\<close> 
                  using \<open>b = 2 * k\<close> by blast
                thus ?thesis 
                  by (metis \<open>b = 2 * k\<close> \<open>even b\<close> \<open>n = 2 * (1 + (m - 1) * k)\<close> \<open>n = 2 + (m - 1) * b\<close> dvd_add_times_triv_right_iff dvd_antisym dvd_imp_le dvd_triv_right even_numeral mult_2 zero_less_numeral)
              next
                case False
                hence \<open>even k\<close> by auto
                have \<open>odd (1 + (m - 1) * k)\<close> 
                  by (simp add: \<open>even k\<close> )
                hence \<open>coprime (3 + (m - 1) * k) (1 + (m - 1) * k)\<close> 
                  by (smt add_numeral_left coprime_common_divisor coprime_right_2_iff_odd dvd_add_left_iff not_coprimeE numeral_Bit1 numeral_One numeral_plus_one one_add_one)
                hence \<open>coprime (3 + (m - 1) * k) n\<close> 
                  by (metis \<open>even k\<close> \<open>n = 2 * (1 + (m - 1) * k)\<close> coprime_mult_right_iff coprime_right_2_iff_odd even_add even_mult_iff odd_numeral)
                have \<open>3 + (m - 1) * k < n\<close> 
                  by (smt Groups.add_ac(2) \<open>even k\<close> \<open>n = 2 * (1 + (m - 1) * k)\<close> \<open>n = 2 + (m - 1) * b\<close> \<open>n \<noteq> 2\<close> add_Suc_right add_cancel_right_right add_mono_thms_linordered_semiring(1) dvd_imp_le even_add even_mult_iff le_add2 le_neq_implies_less left_add_twice mult_2 neq0_conv numeral_Bit1 numeral_One odd_numeral one_add_one plus_1_eq_Suc)
                have \<open>3 + (m - 1) * k \<in> {x |x. x < n \<and> coprime x n}\<close> 
                  using \<open>3 + (m - 1) * k < n\<close> \<open>coprime (3 + (m - 1) * k) n\<close> 
                  by blast
                hence \<open>3 + (m - 1) * k \<in> {1 + j * b |j. j < m}\<close> 
                  using \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> 
                  by blast 
                then obtain j::nat where \<open>3 + (m - 1) * k = 1 + j * b\<close> 
                  by blast  
                have \<open>2 + (m - 1) * k = j * b\<close> 
                  using \<open>3 + (m - 1) * k = 1 + j * b\<close> 
                  by simp
                hence  \<open>2 + (m - 1) * k = j * 2*k\<close> 
                  by (simp add: \<open>b = 2 * k\<close>)
                thus ?thesis 
                  by (metis \<open>4 < b\<close> \<open>b = 2 * k\<close> \<open>even k\<close> dvd_add_times_triv_right_iff dvd_antisym 
                      dvd_triv_right mult_2 nat_neq_iff numeral_Bit0)
              qed
            qed
          qed
        qed
        moreover have \<open>b \<noteq> 3\<close>
        proof (rule classical)
          assume \<open>\<not> (b \<noteq> 3)\<close>
          hence \<open>b = 3\<close> 
            by blast
          obtain m where  \<open>m \<noteq> 0\<close> and 
            \<open>{x | x::nat. x < n \<and> coprime x n} = {1+j*b| j::nat. j < m}\<close>
            using \<open>m \<noteq> 0\<close> \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> 
            by blast
          have \<open>b \<noteq> 0\<close> 
            by (simp add: \<open>b = 3\<close>)
          have \<open>n = 2 + (m-1)*b\<close> 
          proof-
            have \<open>n-1 \<in> {x | x::nat. x < n \<and> coprime x n}\<close> 
              using \<open>1 < n\<close> coprime_diff_one_left_nat 
              by auto
            have \<open>n-1 \<in> {1+j*b| j::nat. j < m}\<close> 
              using \<open>n - 1 \<in> {x |x. x < n \<and> coprime x n}\<close> 
                \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> 
              by blast
            then obtain i::nat where \<open>n-1 = 1+i*b\<close> and \<open>i < m\<close> 
              by blast
            have \<open>i \<le> m-1\<close> 
              using \<open>i < m\<close> 
              by linarith
            have \<open>1 + (m-1)*b \<in> {1+j*b| j::nat. j < m}\<close> 
              using \<open>m \<noteq> 0\<close> 
              by auto
            hence \<open>1 + (m-1)*b \<in> {x | x :: nat. x < n \<and> coprime x n}\<close> 
              using \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> 
              by blast
            hence \<open>1 + (m-1)*b < n\<close> 
              by blast
            hence \<open>1 + (m-1)*b \<le> n-1\<close> 
              by linarith
            hence \<open>1 + (m-1)*b \<le> 1+i*b\<close> 
              using \<open>n - 1 = 1 + i * b\<close> 
              by linarith
            hence \<open>(m-1)*b \<le> i*b\<close> 
              by linarith
            hence \<open>m-1 \<le> i\<close> 
              using \<open>b \<noteq> 0\<close> 
              by auto
            hence \<open>m-1 = i\<close> 
              using \<open>i \<le> m - 1\<close> le_antisym 
              by blast
            thus ?thesis 
              using \<open>m \<noteq> 0\<close> \<open>n - 1 = 1 + i * b\<close> 
              by auto
          qed
          have \<open>n > 2\<close> 
            using \<open>1 < n\<close> \<open>n \<noteq> 2\<close> 
            by linarith
          hence \<open> m \<ge> 2 \<close> using  \<open>n = 2 + (m-1)*b\<close> \<open>b = 3\<close> 
            by simp
          have \<open>4 \<in> {1+j*(b::nat)| j::nat. j < m}\<close> 
            using \<open>2 \<le> m\<close> \<open>b = 3\<close> 
            by force
          hence \<open>(4::nat) \<in>  {x | x :: nat. x < n \<and> coprime x n}\<close> 
            using \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close>
            by auto
          hence \<open>coprime (4::nat) n\<close> 
            by blast
          have \<open>(2::nat) dvd 4\<close> 
            by auto
          hence \<open>coprime (2::nat) n\<close> 
            using \<open>coprime (4::nat) n\<close> coprime_divisors dvd_refl 
            by blast
          have \<open>4 < n\<close> 
            using \<open>4 \<in> {x |x. x < n \<and> coprime x n}\<close> 
            by blast
          have \<open>2 < (4::nat)\<close> 
            by auto
          have  \<open>2 < n\<close> 
            by (simp add: \<open>2 < n\<close>)
          hence \<open>2 \<in> {x | x :: nat. x < n \<and> coprime x n}\<close> 
            using  \<open>coprime (2::nat) n\<close> 
            by blast
          hence  \<open>2 \<in> {1+j*(b::nat)| j::nat. j < m}\<close> 
            using \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> 
            by blast
          then obtain j::nat where \<open>2 = 1+j*3\<close> 
            using \<open>b = 3\<close> 
            by blast
          from  \<open>2 = 1+j*3\<close>
          have  \<open>1 = j*3\<close> 
            by auto
          hence \<open>3 dvd 1\<close> 
            by auto
          thus ?thesis
            using nat_dvd_1_iff_1 numeral_eq_one_iff 
            by blast
        qed
        ultimately have \<open>b = 0 \<or> b = 1 \<or> b = 2 \<or> b = 4\<close>
          by auto
        moreover have \<open>b = 0 \<Longrightarrow> \<exists>k. n = 2^k\<close>
        proof-
          assume \<open>b = 0\<close>
          have \<open>{1 + j * b |j. j < m} = {1}\<close>
            using \<open>b = 0\<close> \<open>m \<noteq> 0\<close> 
            by auto
          hence \<open>{x |x. x < n \<and> coprime x n} = {1}\<close>
            using \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close>
            by blast
          hence \<open>n = 2\<close>
          proof-
            have \<open>n-1 \<in>  {x | x :: nat. x < n \<and> coprime x n}\<close> 
              using \<open>1 < n\<close> coprime_diff_one_left_nat 
              by auto
            have \<open>n-1 \<in> {1}\<close> 
              using \<open>n - 1 \<in> {x |x. x < n \<and> coprime x n}\<close> \<open>{x |x. x < n \<and> coprime x n} = {1}\<close> 
              by blast
            hence \<open>n-1 = 1\<close> 
              by blast
            hence \<open>n = 2\<close> 
              by simp
            thus ?thesis 
              by blast
          qed
          hence \<open>n = 2^1\<close>
            by auto
          thus ?thesis
            by blast 
        qed
        moreover have \<open>b = 1 \<Longrightarrow> prime n\<close>
        proof-
          assume \<open>b = 1\<close>
          have \<open>x < n \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> coprime x n\<close>
            for x
          proof-
            assume \<open>x < n\<close> and \<open>x \<noteq> 0\<close>
            have \<open>{1+j| j::nat. j < m} = {x | x::nat. x < m+1 \<and> x \<noteq> 0}\<close> 
              by (metis (full_types) Suc_eq_plus1  add_mono1 less_Suc_eq_0_disj  nat.simps(3) plus_1_eq_Suc )
            hence \<open>{x | x :: nat. x < n \<and> coprime x n} = {x | x :: nat. x < m+1 \<and> x \<noteq> 0}\<close>
              using \<open>b = 1\<close> \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> 
              by auto
            have \<open>coprime (n-1) n\<close> 
              using \<open>1 < n\<close> coprime_diff_one_left_nat 
              by auto
            have \<open>n-1 < n\<close> 
              using \<open>1 < n\<close> 
              by auto
            have \<open>n-1 \<in> {x |x. x < n \<and> coprime x n}\<close> 
              using \<open>coprime (n - 1) n\<close> \<open>n - 1 < n\<close> 
              by blast
            have \<open>n-1 \<le> m\<close> 
              by (metis (no_types, lifting) CollectD Suc_eq_plus1 Suc_less_eq2 \<open>n - 1 \<in> {x |x. x < n \<and> coprime x n}\<close> \<open>{x |x. x < n \<and> coprime x n} = {x |x. x < m + 1 \<and> x \<noteq> 0}\<close>   leD  le_less_linear not_less_eq_eq )
            have \<open>m \<in>  {x | x :: nat. x < m+1 \<and> x \<noteq> 0}\<close> 
              using \<open>m \<noteq> 0\<close> 
              by auto
            have \<open>m \<in> {x |x. x < n \<and> coprime x n} \<close> 
              using \<open>m \<in> {x |x. x < m + 1 \<and> x \<noteq> 0}\<close> 
                \<open>{x |x. x < n \<and> coprime x n} = {x |x. x < m + 1 \<and> x \<noteq> 0}\<close> 
              by blast
            have \<open>m < n\<close> 
              using \<open>m \<in> {x |x. x < n \<and> coprime x n}\<close> 
              by blast
            have \<open>m+1 = n\<close> 
              using \<open>m < n\<close> \<open>n - 1 \<le> m\<close> 
              by linarith
            have \<open>x \<in>  {x | x :: nat. x < m+1 \<and> x \<noteq> 0}\<close> 
              using \<open>m + 1 = n\<close> \<open>x < n\<close> \<open>x \<noteq> 0\<close> 
              by blast
            hence \<open>x \<in> {x |x. x < n \<and> coprime x n}\<close> 
              using \<open>{x |x. x < n \<and> coprime x n} = {x |x. x < m + 1 \<and> x \<noteq> 0}\<close> 
              by blast
            thus ?thesis 
              by blast
          qed
          thus ?thesis
            using assms coprime_commute nat_neq_iff prime_nat_iff'' by auto 
        qed
        moreover have \<open>b = 2 \<Longrightarrow> \<exists> k. n = 2^k\<close>
        proof-
          assume \<open>b = 2\<close>
          have \<open>{x | x :: nat. x < n \<and> coprime x n} = {1+j*2| j::nat. j < m}\<close>
            using \<open>b = 2\<close> \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> 
            by auto
          have \<open>x < n \<Longrightarrow> coprime x n \<longleftrightarrow> odd x\<close>
            for x::nat
          proof-
            assume \<open>x < n\<close>
            have \<open>coprime x n \<Longrightarrow> odd x\<close>
            proof-
              assume \<open>coprime x n\<close>
              have \<open>x \<in> {x | x :: nat. x < n \<and> coprime x n}\<close> 
                by (simp add: \<open>coprime x n\<close> \<open>x < n\<close>)
              hence \<open>x \<in> {1+j*2| j::nat. j < m}\<close> 
                using \<open>{x |x. x < n \<and> coprime x n} = {1 + j * 2 |j. j < m}\<close> 
                by blast
              then obtain j where \<open>x = 1+j*2\<close> 
                by blast
              thus ?thesis
                by simp
            qed
            moreover have \<open>odd x \<Longrightarrow> coprime x n\<close>
            proof-
              assume \<open>odd x\<close>
              obtain j::nat where \<open>x = 1+j*2\<close> 
                by (metis \<open>odd x\<close> add.commute mult_2_right odd_two_times_div_two_succ one_add_one semiring_normalization_rules(16)) 
              have \<open>j < (n-1)/2\<close> 
                using \<open>x < n\<close> \<open>x = 1 + j * 2\<close> 
                by linarith
              have \<open>n = 2*m\<close>
              proof-
                have  \<open>(2::nat) \<noteq> 0\<close> 
                  by auto
                have \<open>n = 2+(m-1)*2\<close> 
                proof-
                  have \<open>n-1 \<in> {x | x :: nat. x < n \<and> coprime x n}\<close> 
                    using \<open>1 < n\<close> coprime_diff_one_left_nat 
                    by auto
                  have \<open>n-1 \<in> {1+j*b| j::nat. j < m}\<close> 
                    using \<open>n - 1 \<in> {x |x. x < n \<and> coprime x n}\<close> 
                      \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> 
                    by blast
                  then obtain i::nat where \<open>n-1 = 1+i*b\<close> and \<open>i < m\<close> 
                    by blast
                  have \<open>i \<le> m-1\<close> 
                    using \<open>i < m\<close> 
                    by linarith
                  have \<open>1 + (m-1)*b \<in> {1+j*b| j::nat. j < m}\<close> 
                    using \<open>m \<noteq> 0\<close> by auto
                  hence \<open>1 + (m-1)*b \<in> {x | x :: nat. x < n \<and> coprime x n}\<close> 
                    using \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> 
                    by blast
                  hence \<open>1 + (m-1)*b < n\<close> 
                    by blast
                  hence \<open>1 + (m-1)*b \<le> n-1\<close> 
                    by linarith
                  hence \<open>1 + (m-1)*b \<le> 1+i*b\<close> 
                    using \<open>n - 1 = 1 + i * b\<close> 
                    by linarith
                  hence \<open>(m-1)*b \<le> i*b\<close> 
                    by linarith
                  hence \<open>m-1 \<le> i\<close> 
                  proof-
                    have \<open>b \<noteq> 0\<close>
                      using \<open>b = 2\<close>
                      by simp
                    thus ?thesis
                      using \<open>(m - 1) * b \<le> i * b\<close> mult_le_cancel2 
                      by blast 
                  qed
                  hence \<open>m-1 = i\<close> 
                    using \<open>i \<le> m - 1\<close> le_antisym 
                    by blast
                  thus ?thesis 
                    using \<open>m \<noteq> 0\<close> \<open>n - 1 = 1 + i * b\<close>
                    by (simp add: \<open>b = 2\<close>)
                qed
                thus  ?thesis 
                  by (simp add: \<open>m \<noteq> 0\<close> \<open>n = 2 + (m - 1) * 2\<close> mult.commute mult_eq_if)
              qed
              hence \<open>j < m\<close> 
                using \<open>x < n\<close> \<open>x = 1 + j * 2\<close> 
                by linarith
              hence \<open>x \<in> {1+j*2| j::nat. j < m}\<close> 
                using \<open>x = 1 + j * 2\<close> 
                by blast
              hence \<open>x \<in> {x | x :: nat. x < n \<and> coprime x n}\<close> 
                using \<open>{x |x. x < n \<and> coprime x n} = {1 + j * 2 |j. j < m}\<close> 
                by blast
              thus ?thesis 
                by blast
            qed
            ultimately show ?thesis 
              by blast
          qed
          thus ?thesis 
            using coprime_power2 assms 
            by auto
        qed
        moreover have \<open>b = 4 \<Longrightarrow> n = 6\<close>
        proof-
          assume \<open>b = 4\<close>
          have \<open>n = 2 \<or> n = 6\<close>
          proof(rule classical)
            assume \<open>\<not> (n = 2 \<or> n = 6)\<close>
            have  \<open>(4::nat) \<noteq> 0\<close> 
              by auto
            have \<open>n =  2+(m-1)*4\<close> 
            proof-
              have \<open>n-1 \<in> {x | x :: nat. x < n \<and> coprime x n}\<close> 
                using \<open>1 < n\<close> coprime_diff_one_left_nat 
                by auto
              have \<open>n-1 \<in> {1+j*b| j::nat. j < m}\<close> 
                using \<open>n - 1 \<in> {x |x. x < n \<and> coprime x n}\<close> 
                  \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> 
                by blast
              then obtain i::nat where \<open>n-1 = 1+i*b\<close> and \<open>i < m\<close> 
                by blast
              have \<open>i \<le> m-1\<close> 
                using \<open>i < m\<close> 
                by linarith
              have \<open>1 + (m-1)*b \<in> {1+j*b| j::nat. j < m}\<close> 
                using \<open>m \<noteq> 0\<close> 
                by auto
              hence \<open>1 + (m-1)*b \<in> {x | x :: nat. x < n \<and> coprime x n}\<close> 
                using \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> 
                by blast
              hence \<open>1 + (m-1)*b < n\<close> 
                by blast
              hence \<open>1 + (m-1)*b \<le> n-1\<close> 
                by linarith
              hence \<open>1 + (m-1)*b \<le> 1+i*b\<close> 
                using \<open>n - 1 = 1 + i * b\<close> 
                by linarith
              hence \<open>(m-1)*b \<le> i*b\<close> 
                by linarith
              hence \<open>m-1 \<le> i\<close> 
              proof-
                have \<open>b \<noteq> 0\<close>
                  using \<open>b = 4\<close> by auto
                thus ?thesis
                  using \<open>(m - 1) * b \<le> i * b\<close> mult_le_cancel2 
                  by blast 
              qed
              hence \<open>m-1 = i\<close> 
                using \<open>i \<le> m - 1\<close> le_antisym 
                by blast
              thus ?thesis 
                using \<open>m \<noteq> 0\<close> \<open>n - 1 = 1 + i * b\<close>
                by (simp add: \<open>b = 4\<close>) 
            qed
            hence \<open>n = 4*m - 2\<close> 
              by (simp add: \<open>m \<noteq> 0\<close> mult.commute mult_eq_if)
            have \<open>m \<ge> 3\<close> 
              using \<open>\<not> (n = 2 \<or> n = 6)\<close> \<open>n = 2 + (m - 1) * 4\<close> 
              by auto
            hence \<open> {1+j*4| j::nat. j < 3} \<subseteq> {1+j*4| j::nat. j < m}\<close>
              by force
            hence \<open>9 \<in> {1+j*4| j::nat. j < 3}\<close> 
              by force
            hence \<open>9 \<in> {1+j*4| j::nat. j < m}\<close> 
              using  \<open> {1+j*4| j::nat. j < 3} \<subseteq> {1+j*4| j::nat. j < m}\<close> 
              by blast
            hence \<open>9 \<in> {x | x :: nat. x < n \<and> coprime x n}\<close>
              using \<open>b = 4\<close> \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> 
              by auto
            hence \<open>coprime (9::nat) n\<close> 
              by blast
            have \<open>(3::nat) dvd 9\<close> 
              by auto
            have  \<open>coprime (3::nat) n\<close> using  \<open>coprime (9::nat) n\<close> \<open>(3::nat) dvd 9\<close>
              by (metis coprime_commute coprime_mult_right_iff dvd_def)
            have \<open>(3::nat) < n\<close> 
              by (metis One_nat_def Suc_lessI \<open>1 < n\<close> \<open>\<not> (n = 2 \<or> n = 6)\<close> \<open>coprime 3 n\<close>
                  coprime_self numeral_2_eq_2 numeral_3_eq_3 less_numeral_extra(1) nat_dvd_not_less)
            have \<open>3 \<in>  {x | x :: nat. x < n \<and> coprime x n}\<close> 
              using \<open>3 < n\<close> \<open>coprime 3 n\<close> 
              by blast
            hence  \<open>(3::nat) \<in> {1+j*4| j::nat. j < m}\<close>
              using \<open>b = 4\<close> \<open>{x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}\<close> 
              by blast
            then obtain j::nat where \<open>(3::nat) = 1 + j*4\<close> 
              by blast  
            have \<open>2 = j*4\<close> 
              using numeral_3_eq_3 \<open>(3::nat) = 1 + j*4\<close>
              by linarith
            hence \<open>1 = j*2\<close> 
              by linarith
            hence \<open>even 1\<close> 
              by simp
            thus ?thesis 
              using odd_one 
              by blast
          qed
          thus ?thesis
            by (simp add: False)            
        qed
        ultimately show ?thesis 
          by blast
      qed
    qed
  qed
  moreover have \<open>(\<exists> b m. m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {1+j*b| j::nat. j < m})
  \<longleftrightarrow> (\<exists> a b m. m \<noteq> 0 \<and> {x | x :: nat. x < n \<and> coprime x n} = {a+j*b| j::nat. j < m})\<close>
  proof
    show "\<exists>a b m. m \<noteq> 0 \<and> {x |x. x < n \<and> coprime x n} = {a + j * b |j. j < m}"
      if "\<exists>b m. m \<noteq> 0 \<and> {x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}"
      using that
      by blast 
    show "\<exists>b m. m \<noteq> 0 \<and> {x |x. x < n \<and> coprime x n} = {1 + j * b |j. j < m}"
      if "\<exists>a b m. m \<noteq> 0 \<and> {x |x. x < n \<and> coprime x n} = {a + j * b |j. j < m}"
    proof-
      obtain a b m::nat where \<open>m \<noteq> 0\<close>
        and \<open>{x | x :: nat. x < n \<and> coprime x n} = {a+j*b| j::nat. j < m}\<close>
        using \<open>\<exists>a b m. m \<noteq> 0 \<and> {x |x. x < n \<and> coprime x n} = {a + j * b |j. j < m}\<close> 
        by auto        
      have \<open>a = 1\<close> 
      proof-
        have \<open>{x | x :: nat. x < n \<and> coprime x n} = {(a::nat)+j*(b::nat)| j::nat. j < m} \<Longrightarrow> a = 1\<close>
        proof-
          have \<open>Min {x | x :: nat. x < n \<and> coprime x n} = Min {a+j*b| j::nat. j < m}\<close>
            using \<open>{x |x. x < n \<and> coprime x n} = {a + j * b |j. j < m}\<close> 
            by auto            
          have  \<open>Min {x | x :: nat. x < n \<and> coprime x n} = 1\<close>
          proof-
            have \<open>finite {x | x :: nat. x < n \<and> coprime x n}\<close>
              by auto
            have \<open>{x | x :: nat. x < n \<and> coprime x n} \<noteq> {}\<close> 
              using \<open>1 < n\<close> by auto
            have \<open>1 \<in> {x | x :: nat. x < n \<and> coprime x n}\<close> 
              using \<open>1 < n\<close> 
              by auto
            have \<open>\<forall> x. coprime x n \<longrightarrow> x \<ge> 1\<close> 
              using \<open>1 < n\<close> le_less_linear 
              by fastforce
            hence \<open>\<forall> x.  x < n \<and> coprime x n \<longrightarrow> x \<ge> 1\<close> 
              by blast
            hence \<open>\<forall> x \<in> {x | x :: nat. x < n \<and> coprime x n}. x \<ge> 1\<close> 
              by blast
            hence \<open>Min {x | x :: nat. x < n \<and> coprime x n} \<ge> 1\<close> 
              using \<open>finite {x | x :: nat. x < n \<and> coprime x n}\<close> \<open>{x |x. x < n \<and> coprime x n} \<noteq> {}\<close>
              by auto
            thus ?thesis 
              using Min_le \<open>1 \<in> {x |x. x < n \<and> coprime x n}\<close> \<open>finite {x |x. x < n \<and> coprime x n}\<close>
                antisym by blast
          qed
          have \<open>Min  {a+j*b| j::nat. j < m} = a\<close>
          proof -
            have f1: "\<exists>n. a = a + n * b \<and> n < m"
              using \<open>m \<noteq> 0\<close> 
              by auto
            have f2: "\<exists>n. 1 = a + n * b \<and> n < m"
              using \<open>{x |x. x < n \<and> coprime x n} = {a + j * b |j. j < m}\<close> assms coprime_1_left 
              by blast
            have f3: "\<exists>na. a = na \<and> na < n \<and> coprime na n"
              using f1 \<open>{x |x. x < n \<and> coprime x n} = {a + j * b |j. j < m}\<close> by blast
            have "n \<noteq> 1"
              by (metis (lifting) assms less_irrefl_nat)
            then have "\<not> coprime 0 n"
              by simp
            then show ?thesis
              using f3 f2 by (metis \<open>Min {x |x. x < n \<and> coprime x n} = 1\<close> \<open>{x |x. x < n \<and> coprime x n} = {a + j * b |j. j < m}\<close> less_one linorder_neqE_nat not_add_less1)
          qed
          hence \<open>Min  {a+j*b| j::nat. j < m} = a\<close> by blast
          thus ?thesis 
            using \<open>Min {x | x :: nat. x < n \<and> coprime x n} = 1\<close> \<open>Min {x | x :: nat. x < n \<and> coprime x n} = Min {a+j*b| j::nat. j < m}\<close>
            by linarith
        qed
        thus ?thesis
          using \<open>{x |x. x < n \<and> coprime x n} = {a + j * b |j. j < m}\<close> 
          by blast 
      qed
      thus ?thesis using  \<open>m \<noteq> 0\<close> \<open>{x | x. x < n \<and> coprime x n} = {a+j*b| j::nat. j < m}\<close> 
        by auto
    qed
  qed 
  ultimately show ?thesis
    by simp 
qed

end