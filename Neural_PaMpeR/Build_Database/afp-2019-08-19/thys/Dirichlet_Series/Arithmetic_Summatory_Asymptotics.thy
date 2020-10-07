(*
    File:      Arithmetic_Summatory_Asymptotics.thy
    Author:    Manuel Eberl, TU München
*)
section \<open>Asymptotics of summatory arithmetic functions\<close>
theory Arithmetic_Summatory_Asymptotics
  imports 
    Euler_MacLaurin.Euler_MacLaurin_Landau
    Arithmetic_Summatory 
    Dirichlet_Series_Analysis
    Landau_Symbols.Landau_More
begin

subsection \<open>Auxiliary bounds\<close>

lemma sum_inverse_squares_tail_bound:
  assumes "d > 0"
  shows   "summable (\<lambda>n. 1 / (real (Suc n) + d) ^ 2)"
          "(\<Sum>n. 1 / (real (Suc n) + d) ^ 2) \<le> 1 / d"
proof -
  show *: "summable (\<lambda>n. 1 / (real (Suc n) + d) ^ 2)"
  proof (rule summable_comparison_test, intro allI exI impI)
    fix n :: nat
    from assms show "norm (1 / (real (Suc n) + d) ^ 2) \<le> 1 / real (Suc n) ^ 2"
      unfolding norm_divide norm_one norm_power
      by (intro divide_left_mono power_mono) simp_all
  qed (insert inverse_squares_sums, simp add: sums_iff)
  show "(\<Sum>n. 1 / (real (Suc n) + d) ^ 2) \<le> 1 / d"
  proof (rule sums_le[OF allI])
    fix n have "1 / (real (Suc n) + d) ^ 2 \<le> 1 / ((real n + d) * (real (Suc n) + d))"
      unfolding power2_eq_square using assms
      by (intro divide_left_mono mult_mono mult_pos_pos add_nonneg_pos) simp_all
    also have "\<dots> = 1 / (real n + d) - 1 / (real (Suc n) + d)"
      using assms by (simp add: divide_simps)
    finally show "1 / (real (Suc n) + d)\<^sup>2 \<le> 1 / (real n + d) - 1 / (real (Suc n) + d)" .
  next
    show "(\<lambda>n. 1 / (real (Suc n) + d)\<^sup>2) sums (\<Sum>n. 1 / (real (Suc n) + d)\<^sup>2)"
      using * by (simp add: sums_iff)
  next
    have "(\<lambda>n. 1 / (real n + d) - 1 / (real (Suc n) + d)) sums (1 / (real 0 + d) - 0)"
      by (intro telescope_sums' real_tendsto_divide_at_top[OF tendsto_const],
          subst add.commute, rule filterlim_tendsto_add_at_top[OF tendsto_const 
            filterlim_real_sequentially])
    thus "(\<lambda>n. 1 / (real n + d) - 1 / (real (Suc n) + d)) sums (1 / d)" by simp
  qed
qed

lemma moebius_sum_tail_bound:
  assumes "d > 0"
  shows   "abs (\<Sum>n. moebius_mu (Suc n + d) / real (Suc n + d)^2) \<le> 1 / d" (is "abs ?S \<le> _")
proof -
  have *: "summable (\<lambda>n. 1 / (real (Suc n + d))\<^sup>2)"
    by (insert sum_inverse_squares_tail_bound(1)[of "real d"] assms, simp_all add: add_ac)
  have **: "summable (\<lambda>n. abs (moebius_mu (Suc n + d) / real (Suc n + d)^2))"
  proof (rule summable_comparison_test, intro exI allI impI)
    fix n :: nat
    show "norm (\<bar>moebius_mu (Suc n + d) / (real (Suc n + d))^2\<bar>) \<le>
            1 / (real (Suc n + d))^2" 
      unfolding real_norm_def abs_abs abs_divide power_abs abs_of_nat
      by (intro divide_right_mono abs_moebius_mu_le) simp_all
  qed (insert *)   
  from ** have "abs ?S \<le> (\<Sum>n. abs (moebius_mu (Suc n + d) / real (Suc n + d)^2))"
    by (rule summable_rabs)
  also have "\<dots> \<le> (\<Sum>n. 1 / (real (Suc n) + d) ^ 2)"
  proof (intro suminf_le allI)
    fix n :: nat
    show "abs (moebius_mu (Suc n + d) / (real (Suc n + d))^2) \<le> 1 / (real (Suc n) + real d)^2"
      unfolding abs_divide abs_of_nat power_abs of_nat_add [symmetric]
      by (intro divide_right_mono abs_moebius_mu_le) simp_all
  qed (insert * **, simp_all add: add_ac)
  also from assms have "\<dots> \<le> 1 / d" by (intro sum_inverse_squares_tail_bound) simp_all
  finally show ?thesis .
qed

lemma sum_upto_inverse_bound:
  "sum_upto (\<lambda>i. 1 / real i) x \<ge> 0"
  "eventually (\<lambda>x. sum_upto (\<lambda>i. 1 / real i) x \<le> ln x + 13 / 22) at_top"
proof -
  show "sum_upto (\<lambda>i. 1 / real i) x \<ge> 0"
    by (simp add: sum_upto_def sum_nonneg)
  from order_tendstoD(2)[OF euler_mascheroni_LIMSEQ euler_mascheroni_less_13_over_22]
  obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> harm n - ln (real n) < 13 / 22"
    unfolding eventually_at_top_linorder by blast
  show "eventually (\<lambda>x. sum_upto (\<lambda>i. 1 / real i) x \<le> ln x + 13 / 22) at_top"
    using eventually_ge_at_top[of "max (real N) 1"]
  proof eventually_elim
    case (elim x)
    have "sum_upto (\<lambda>i. 1 / real i) x = (\<Sum>i\<in>{0<..nat \<lfloor>x\<rfloor>}. 1 / real i)"
      by (simp add: sum_upto_altdef)
    also have "\<dots> = harm (nat \<lfloor>x\<rfloor>)"
      unfolding harm_def by (intro sum.cong refl) (auto simp: field_simps)
    also have "\<dots> \<le> ln (real (nat \<lfloor>x\<rfloor>)) + 13 / 22"
      using N[of "nat \<lfloor>x\<rfloor>"] elim by (auto simp: le_nat_iff le_floor_iff)
    also have "ln (real (nat \<lfloor>x\<rfloor>)) \<le> ln x" using elim by (subst ln_le_cancel_iff) auto
    finally show ?case by - simp
  qed
qed

lemma sum_upto_inverse_bigo: "sum_upto (\<lambda>i. 1 / real i) \<in> O(\<lambda>x. ln x)"
proof -
  have "eventually (\<lambda>x. norm (sum_upto (\<lambda>i. 1 / real i) x) \<le> 1 * norm (ln x + 13/22)) at_top"
    using eventually_ge_at_top[of "1::real"] sum_upto_inverse_bound(2)
    by eventually_elim (insert sum_upto_inverse_bound(1), simp_all)
  hence "sum_upto (\<lambda>i. 1 / real i) \<in> O(\<lambda>x. ln x + 13/22)"
    by (rule bigoI)
  also have "(\<lambda>x::real. ln x + 13/22) \<in> O(\<lambda>x. ln x)" by simp
  finally show ?thesis .
qed

lemma
  defines "G \<equiv> (\<lambda>x::real. (\<Sum>n. moebius_mu (n + Suc (nat \<lfloor>x\<rfloor>)) / (n + Suc (nat \<lfloor>x\<rfloor>))^2) :: real)"
  shows   moebius_sum_tail_bound': "\<And>t. t \<ge> 2 \<Longrightarrow> \<bar>G t\<bar> \<le> 1 / (t - 1)"
    and   moebius_sum_tail_bigo:   "G \<in> O(\<lambda>t. 1 / t)"
proof -
  show "\<bar>G t\<bar> \<le> 1 / (t - 1)" if t: "t \<ge> 2" for t
  proof -
    from t have "\<bar>G t\<bar> \<le> 1 / real (nat \<lfloor>t\<rfloor>)"
      unfolding G_def using moebius_sum_tail_bound[of "nat \<lfloor>t\<rfloor>"] by simp
    also have "t \<le> 1 + real_of_int \<lfloor>t\<rfloor>" by linarith
    hence "1 / real (nat \<lfloor>t\<rfloor>) \<le> 1 / (t - 1)" using t by (simp add: field_simps)
    finally show ?thesis .
  qed
  hence "G \<in> O(\<lambda>t. 1 / (t - 1))" 
    by (intro bigoI[of _ 1] eventually_mono[OF eventually_ge_at_top[of "2::real"]]) auto
  also have "(\<lambda>t::real. 1 / (t - 1)) \<in> \<Theta>(\<lambda>t. 1 / t)" by simp
  finally show "G \<in> O(\<lambda>t. 1 / t)" .
qed


subsection \<open>Summatory totient function\<close>

theorem summatory_totient_asymptotics:
  "(\<lambda>x. sum_upto (\<lambda>n. real (totient n)) x - 3 / pi\<^sup>2 * x\<^sup>2) \<in> O(\<lambda>x. x * ln x)"
proof -
  define H where "H = (\<lambda>x. of_int (floor x) * (of_int (floor x) + 1) / 2 - x ^ 2 / 2 :: real)"
  define H' where "H' = (\<lambda>x. sum_upto (\<lambda>n. moebius_mu n * H (x / real n)) x)"
  have H: "sum_upto real x = x^2/2 + H x" if "x \<ge> 0" for x
    using that by (simp add: sum_upto_real H_def)
  define G where "G = (\<lambda>x::real. (\<Sum>n. moebius_mu (n + Suc (nat \<lfloor>x\<rfloor>)) / (n + Suc (nat \<lfloor>x\<rfloor>))^2))"
  
  have H_bound: "\<bar>H t\<bar> \<le> t / 2" if "t \<ge> 0" for t
  proof -
    have "H t - t / 2 = (-(t - of_int (floor t))) * (floor t + t + 1) / 2"
      by (simp add: H_def field_simps power2_eq_square)
    also have "\<dots> \<le> 0" using that by (intro mult_nonpos_nonneg divide_nonpos_nonneg) simp_all
    finally have "H t \<le> t / 2" by simp
    have "-H t - t / 2 = (t - of_int (floor t) - 1) * (of_int (floor t) + t) / 2"
      by (simp add: H_def field_simps power2_eq_square)
    also have "\<dots> \<le> 0" using that
      by (intro divide_nonpos_nonneg mult_nonpos_nonneg) ((simp; fail) | linarith)+
    finally have "-H t \<le> t / 2" by simp
    with \<open>H t \<le> t / 2\<close> show "\<bar>H t\<bar> \<le> t / 2" by simp
  qed
  
  have H'_bound: "\<bar>H' t\<bar> \<le> t / 2 * sum_upto (\<lambda>i. 1 / real i) t" if "t \<ge> 0" for t
  proof -
    have "\<bar>H' t\<bar> \<le> (\<Sum>i | 0 < i \<and> real i \<le> t. \<bar>moebius_mu i * H (t / real i)\<bar>)"
      unfolding H'_def sum_upto_def by (rule sum_abs)
    also have "\<dots> \<le> (\<Sum>i | 0 < i \<and> real i \<le> t. 1 * ((t / real i) / 2))"
      unfolding abs_mult using that
      by (intro sum_mono mult_mono abs_moebius_mu_le H_bound) simp_all
    also have "\<dots> = t / 2 * sum_upto (\<lambda>i. 1 / real i) t"
      by (simp add: sum_upto_def sum_distrib_left sum_distrib_right mult_ac)
    finally show ?thesis .
  qed
  hence "H' \<in> O(\<lambda>t. t * sum_upto (\<lambda>i. 1 / real i) t)"
    using sum_upto_inverse_bound(1)
    by (intro bigoI[of _ "1/2"] eventually_mono[OF eventually_ge_at_top[of "0::real"]]) 
       (auto elim!: eventually_mono simp: abs_mult)
  also have "(\<lambda>t. t * sum_upto (\<lambda>i. 1 / real i) t) \<in> O(\<lambda>t. t * ln t)"
    by (intro landau_o.big.mult sum_upto_inverse_bigo) simp_all
  finally have H'_bigo: "H' \<in> O(\<lambda>x. x * ln x)" .
  
  {
    fix x :: real assume x: "x \<ge> 0"
    have "sum_upto (\<lambda>n. real (totient n)) x = sum_upto (\<lambda>n. of_int (int (totient n))) x"
      by simp
    also have "\<dots> = sum_upto (\<lambda>n. moebius_mu n * sum_upto real (x / real n)) x"
      by (subst totient_conv_moebius_mu) (simp add: sum_upto_dirichlet_prod of_int_dirichlet_prod)
    also have "\<dots> = sum_upto (\<lambda>n. moebius_mu n * ((x / real n) ^ 2 / 2 + H (x / real n))) x" using x
      by (intro sum_upto_cong) (simp_all add: H)
    also have "\<dots> = x^2 / 2 * sum_upto (\<lambda>n. moebius_mu n / real n ^ 2) x + H' x"
      by (simp add: sum_upto_def H'_def sum.distrib ring_distribs
                    sum_distrib_left sum_distrib_right power_divide mult_ac)
    also have "sum_upto (\<lambda>n. moebius_mu n / real n ^ 2) x = 
                 (\<Sum>n\<in>{..<Suc (nat \<lfloor>x\<rfloor>)}. moebius_mu n / real n ^ 2)" 
      unfolding sum_upto_altdef by (intro sum.mono_neutral_cong_left refl) auto
    also have "\<dots> = 6 / pi ^ 2 - G x"
      using sums_split_initial_segment[OF moebius_over_square_sums, of "Suc (nat \<lfloor>x\<rfloor>)"]
      by (auto simp: sums_iff algebra_simps G_def)
    finally have "sum_upto (\<lambda>n. real (totient n)) x = 3 / pi\<^sup>2 * x\<^sup>2 - x\<^sup>2 / 2 * G x + H' x"
      by (simp add: algebra_simps)
  }
  hence "(\<lambda>x. sum_upto (\<lambda>n. real (totient n)) x - 3 / pi^2 * x^2) \<in> 
            \<Theta>(\<lambda>x. (-(x^2) / 2) * G x + H' x)"
    by (intro bigthetaI_cong eventually_mono[OF eventually_ge_at_top[of "0::real"]]) 
       (auto elim!: eventually_mono)
  also have "(\<lambda>x. (-(x^2) / 2) * G x + H' x) \<in> O(\<lambda>x. x * ln x)"
  proof (intro sum_in_bigo H'_bigo)
    have "(\<lambda>x. (- (x^2) / 2) * G x) \<in> O(\<lambda>x. x^2 * (1 / x))"
      using moebius_sum_tail_bigo [folded G_def] by (intro landau_o.big.mult) simp_all
    also have "(\<lambda>x::real. x^2 * (1 / x)) \<in> O(\<lambda>x. x * ln x)" by simp
    finally show "(\<lambda>x. (- (x^2) / 2) * G x) \<in> O(\<lambda>x. x * ln x)" .
  qed
  finally show ?thesis .
qed

theorem summatory_totient_asymptotics':
  "(\<lambda>x. sum_upto (\<lambda>n. real (totient n)) x) =o (\<lambda>x. 3 / pi\<^sup>2 * x\<^sup>2) +o O(\<lambda>x. x * ln x)"
  using summatory_totient_asymptotics
  by (subst set_minus_plus [symmetric]) (simp_all add: fun_diff_def)

theorem summatory_totient_asymptotics'':
  "sum_upto (\<lambda>n. real (totient n)) \<sim>[at_top] (\<lambda>x. 3 / pi\<^sup>2 * x\<^sup>2)"
proof -
  have "(\<lambda>x. sum_upto (\<lambda>n. real (totient n)) x - 3 / pi\<^sup>2 * x\<^sup>2) \<in> O(\<lambda>x. x * ln x)"
    by (rule summatory_totient_asymptotics)
  also have "(\<lambda>x. x * ln x) \<in> o(\<lambda>x. 3 / pi ^ 2 * x ^ 2)" by simp
  finally show ?thesis by (simp add: asymp_equiv_altdef)
qed


subsection \<open>Asymptotic distribution of squarefree numbers\<close>

lemma le_sqrt_iff: "x \<ge> 0 \<Longrightarrow> x \<le> sqrt y \<longleftrightarrow> x^2 \<le> y"
  using real_sqrt_le_iff[of "x^2" y] by (simp del: real_sqrt_le_iff)

theorem squarefree_asymptotics: "(\<lambda>x. card {n. real n \<le> x \<and> squarefree n} - 6 / pi\<^sup>2 * x) \<in> O(sqrt)"
proof -
  define f :: "nat \<Rightarrow> real" where "f = (\<lambda>n. if n = 0 then 0 else 1)"
  define g :: "nat \<Rightarrow> real" where "g = dirichlet_prod (ind squarefree) moebius_mu"
  
  interpret g: multiplicative_function g unfolding g_def
    by (intro multiplicative_dirichlet_prod squarefree.multiplicative_function_axioms 
              moebius_mu.multiplicative_function_axioms)
  interpret g: multiplicative_function' g "\<lambda>p k. if k = 2 then -1 else 0" "\<lambda>_. 0"
  proof
    interpret g': multiplicative_dirichlet_prod' "ind squarefree" moebius_mu
     "\<lambda>p k. if 1 < k then 0 else 1" "\<lambda>p k. if k = 1 then - 1 else 0" "\<lambda>_. 1" "\<lambda>_. - 1"
    by (intro multiplicative_dirichlet_prod'.intro squarefree.multiplicative_function'_axioms 
              moebius_mu.multiplicative_function'_axioms)
    fix p k :: nat assume "prime p" "k > 0"
    hence "g (p ^ k) = (\<Sum>i\<in>{0<..<k}. (if Suc 0 < i then 0 else 1) *
                           (if k - i = Suc 0 then - 1 else 0))"
      by (auto simp: g'.prime_power g_def)
    also have "\<dots> = (\<Sum>i\<in>{0<..<k}. (if k = 2 then -1 else 0))" 
      by (intro sum.cong refl) auto
    also from \<open>k > 0\<close> have "\<dots> = (if k = 2 then -1 else 0)" by simp
    finally show "g (p ^ k) = \<dots>" .
  qed simp_all
  have mult_g_square: "multiplicative_function (\<lambda>n. g (n ^ 2))"
    by standard (simp_all add: power_mult_distrib g.mult_coprime)
    
  have g_square: "g (m ^ 2) = moebius_mu m" for m
    using mult_g_square moebius_mu.multiplicative_function_axioms
  proof (rule multiplicative_function_eqI)
    fix p k :: nat assume *: "prime p" "k > 0"
    have "g ((p ^ k) ^ 2) = g (p ^ (2 * k))" by (simp add: power_mult [symmetric] mult_ac)
    also from * have "\<dots> = (if k = 1 then -1 else 0)" by (simp add: g.prime_power)
    also from * have "\<dots> = moebius_mu (p ^ k)" by (simp add: moebius_mu.prime_power)
    finally show "g ((p ^ k) ^ 2) = moebius_mu (p ^ k)" .
  qed

  have g_nonsquare: "g m = 0" if "\<not>is_square m" for m
  proof (cases "m = 0")
    case False
    from that False obtain p where p: "prime p" "odd (multiplicity p m)"
      using is_nth_power_conv_multiplicity_nat[of 2 m] by auto
    from p have "multiplicity p m \<noteq> 2" by auto
    moreover from p have "p \<in> prime_factors m" 
      by (auto simp: prime_factors_multiplicity intro!: Nat.gr0I)
    ultimately have "(\<Prod>p\<in>prime_factors m. if multiplicity p m = 2 then - 1 else 0 :: real) = 0"
      (is "?P = _") by auto
    also have "?P = g m" using False by (subst g.prod_prime_factors') auto
    finally show ?thesis .
  qed auto
    
  have abs_g_le: "abs (g m) \<le> 1" for m
    by (cases "is_square m")
       (auto simp: g_square g_nonsquare abs_moebius_mu_le elim!: is_nth_powerE)
    
  have fds_g: "fds g = fds_ind squarefree * fds moebius_mu"
    by (rule fds_eqI) (simp add: g_def fds_nth_mult)
  have "fds g * fds_zeta = fds_ind squarefree * (fds_zeta * fds moebius_mu)"
    by (simp add: fds_g mult_ac)
  also have "fds_zeta * fds moebius_mu = (1 :: real fds)"
    by (rule fds_zeta_times_moebius_mu)
  finally have *: "fds_ind squarefree = fds g * fds_zeta" by simp
  have ind_squarefree: "ind squarefree = dirichlet_prod g f"
  proof
    fix n :: nat
    from * show "ind squarefree n = dirichlet_prod g f n"
      by (cases "n = 0") (simp_all add: fds_eq_iff fds_nth_mult f_def)
  qed
    
  define H :: "real \<Rightarrow> real" 
    where "H = (\<lambda>x. sum_upto (\<lambda>m. g (m^2) * (real_of_int \<lfloor>x / real (m\<^sup>2)\<rfloor> - x / real (m^2))) (sqrt x))"
  define J where "J = (\<lambda>x::real. (\<Sum>n. moebius_mu (n + Suc (nat \<lfloor>x\<rfloor>)) / (n + Suc (nat \<lfloor>x\<rfloor>))^2))"
      
  have "eventually (\<lambda>x. norm (H x) \<le> 1 * norm (sqrt x)) at_top" 
    using eventually_ge_at_top[of "0::real"]
  proof eventually_elim
    case (elim x)
    have "abs (H x) \<le> sum_upto (\<lambda>m. abs (g (m^2) * (real_of_int \<lfloor>x / real (m\<^sup>2)\<rfloor> - 
                         x / real (m^2)))) (sqrt x)" (is "_ \<le> ?S") unfolding H_def sum_upto_def
      by (rule sum_abs)
    also have "x / (real m)\<^sup>2 - real_of_int \<lfloor>x / (real m)\<^sup>2\<rfloor> \<le> 1" for m by linarith
    hence "?S \<le> sum_upto (\<lambda>m. 1 * 1) (sqrt x)" unfolding abs_mult sum_upto_def
      by (intro sum_mono mult_mono abs_g_le) simp_all
    also have "\<dots> = of_int \<lfloor>sqrt x\<rfloor>" using elim by (simp add: sum_upto_altdef)
    also have "\<dots> \<le> sqrt x" by linarith
    finally show ?case using elim by simp
  qed
  hence H_bigo: "H \<in> O(\<lambda>x. sqrt x)" by (rule bigoI)
  
  let ?A = "\<lambda>x. card {n. real n \<le> x \<and> squarefree n}"
  have "eventually (\<lambda>x. ?A x - 6 / pi\<^sup>2 * x = (-x) * J (sqrt x) + H x) at_top"
    using eventually_ge_at_top[of "0::real"]
  proof eventually_elim
    fix x :: real assume x: "x \<ge> 0"
    have "{n. real n \<le> x \<and> squarefree n} = {n. n > 0 \<and> real n \<le> x \<and> squarefree n}" 
      by (auto intro!: Nat.gr0I)
    also have "card \<dots> = sum_upto (ind squarefree :: nat \<Rightarrow> real) x"
      by (rule sum_upto_ind [symmetric])
    also have "\<dots> = sum_upto (\<lambda>d. g d * sum_upto f (x / real d)) x" (is "_ = ?S")
      unfolding ind_squarefree by (rule sum_upto_dirichlet_prod)
    also have "sum f {0<..nat \<lfloor>x / real i\<rfloor>} = of_int \<lfloor>x / real i\<rfloor>" if "i > 0" for i
      using x by (simp add: f_def)
    hence "?S = sum_upto (\<lambda>d. g d * of_int \<lfloor>x / real d\<rfloor>) x"
      unfolding sum_upto_altdef by (intro sum.cong refl) simp_all
    also have "\<dots> = sum_upto (\<lambda>m. g (m ^ 2) * of_int \<lfloor>x / real (m ^ 2)\<rfloor>) (sqrt x)"
      unfolding sum_upto_def 
    proof (intro sum.reindex_bij_betw_not_neutral [symmetric])
      show "bij_betw power2 ({i. 0 < i \<and> real i \<le> sqrt x} - {}) 
              ({i. 0 < i \<and> real i \<le> x} - {i\<in>{0<..nat \<lfloor>x\<rfloor>}. \<not>is_square i})"
        by (auto simp: bij_betw_def inj_on_def power_eq_iff_eq_base le_sqrt_iff 
                       is_nth_power_def le_nat_iff le_floor_iff)
    qed (auto simp: g_nonsquare)
    also have "\<dots> = x * sum_upto (\<lambda>m. g (m ^ 2) / real m ^ 2) (sqrt x) + H x"
      by (simp add: H_def sum_upto_def sum.distrib ring_distribs sum_subtractf 
                    sum_distrib_left sum_distrib_right mult_ac)
    also have "sum_upto (\<lambda>m. g (m ^ 2) / real m ^ 2) (sqrt x) = 
                 sum_upto (\<lambda>m. moebius_mu m / real m ^ 2) (sqrt x)"
      unfolding sum_upto_altdef by (intro sum.cong refl) (simp_all add: g_square)
    also have "sum_upto (\<lambda>m. moebius_mu m / (real m)\<^sup>2) (sqrt x) =
                 (\<Sum>m<Suc (nat \<lfloor>sqrt x\<rfloor>). moebius_mu m / (real m) ^ 2)"
      unfolding sum_upto_altdef by (intro sum.mono_neutral_cong_left) auto
    also have "\<dots> = (6 / pi^2 - J (sqrt x))"
      using sums_split_initial_segment[OF moebius_over_square_sums, of "Suc (nat \<lfloor>sqrt x\<rfloor>)"]
      by (auto simp: sums_iff algebra_simps J_def sum_upto_altdef)
    finally show "?A x - 6 / pi\<^sup>2 * x = (-x) * J (sqrt x) + H x"
      by (simp add: algebra_simps)
  qed
  hence "(\<lambda>x. ?A x - 6 / pi\<^sup>2 * x) \<in> \<Theta>(\<lambda>x. (-x) * J (sqrt x) + H x)"
    by (rule bigthetaI_cong)
  also have "(\<lambda>x. (-x) * J (sqrt x) + H x) \<in> O(\<lambda>x. sqrt x)"
  proof (intro sum_in_bigo H_bigo)
    have "(\<lambda>x. J (sqrt x)) \<in> O(\<lambda>x. 1 / sqrt x)" unfolding J_def
        using moebius_sum_tail_bigo sqrt_at_top by (rule landau_o.big.compose)
    hence "(\<lambda>x. (-x) * J (sqrt x)) \<in> O(\<lambda>x. x * (1 / sqrt x))"
      by (intro landau_o.big.mult) simp_all
    also have "(\<lambda>x::real. x * (1 / sqrt x)) \<in> \<Theta>(\<lambda>x. sqrt x)"
      by (intro bigthetaI_cong eventually_mono[OF eventually_gt_at_top[of "0::real"]]) 
         (auto simp: field_simps)
    finally show "(\<lambda>x. (-x) * J (sqrt x)) \<in> O(\<lambda>x. sqrt x)" .
  qed
  finally show ?thesis .
qed

theorem squarefree_asymptotics':
  "(\<lambda>x. card {n. real n \<le> x \<and> squarefree n}) =o (\<lambda>x. 6 / pi\<^sup>2 * x) +o O(\<lambda>x. sqrt x)"
  using squarefree_asymptotics
  by (subst set_minus_plus [symmetric]) (simp_all add: fun_diff_def)

theorem squarefree_asymptotics'':
  "(\<lambda>x. card {n. real n \<le> x \<and> squarefree n}) \<sim>[at_top] (\<lambda>x. 6 / pi\<^sup>2 * x)"
proof -
  have "(\<lambda>x. card {n. real n \<le> x \<and> squarefree n} - 6 / pi\<^sup>2 * x) \<in> O(\<lambda>x. sqrt x)"
    by (rule squarefree_asymptotics)
  also have "(sqrt :: real \<Rightarrow> real) \<in> \<Theta>(\<lambda>x. x powr (1/2))" 
    by (intro bigthetaI_cong eventually_mono[OF eventually_ge_at_top[of "0::real"]]) 
       (auto simp: powr_half_sqrt)
  also have "(\<lambda>x::real. x powr (1/2)) \<in> o(\<lambda>x. 6 / pi ^ 2 * x)" by simp
  finally show ?thesis by (simp add: asymp_equiv_altdef)
qed


subsection \<open>The hyperbola method\<close>

lemma hyperbola_method_bigo:
  fixes f g :: "nat \<Rightarrow> 'a :: real_normed_field"
  assumes "(\<lambda>x. sum_upto (\<lambda>n. f n * sum_upto g (x / real n)) (sqrt x) - R x) \<in> O(b)"
  assumes "(\<lambda>x. sum_upto (\<lambda>n. sum_upto f (x / real n) * g n) (sqrt x) - S x) \<in> O(b)"
  assumes "(\<lambda>x. sum_upto f (sqrt x) * sum_upto g (sqrt x) - T x) \<in> O(b)"
  shows   "(\<lambda>x. sum_upto (dirichlet_prod f g) x - (R x + S x - T x)) \<in> O(b)"
proof -
  let ?A = "\<lambda>x. (sum_upto (\<lambda>n. f n * sum_upto g (x / real n)) (sqrt x) - R x) +
                (sum_upto (\<lambda>n. sum_upto f (x / real n) * g n) (sqrt x) - S x) +
                (-(sum_upto f (sqrt x) * sum_upto g (sqrt x) - T x))"
  have "(\<lambda>x. sum_upto (dirichlet_prod f g) x - (R x + S x - T x)) \<in> \<Theta>(?A)"
    by (intro bigthetaI_cong eventually_mono[OF eventually_ge_at_top[of "0::real"]])
       (auto simp: hyperbola_method_sqrt)
  also from assms have "?A \<in> O(b)"
    by (intro sum_in_bigo(1)) (simp_all only: landau_o.big.uminus_in_iff)
  finally show ?thesis .
qed

lemma frac_le_1: "frac x \<le> 1"
  unfolding frac_def by linarith

lemma ln_minus_ln_floor_bound:
  assumes "x \<ge> 2"
  shows   "ln x - ln (floor x) \<in> {0..<1 / (x - 1)}"
proof -
  from assms have "ln (floor x) \<ge> ln (x - 1)" by (subst ln_le_cancel_iff) simp_all
  hence "ln x - ln (floor x) \<le> ln ((x - 1) + 1) - ln (x - 1)" by simp
  also from assms have "\<dots> < 1 / (x - 1)" by (intro ln_diff_le_inverse) simp_all
  finally have "ln x - ln (floor x) < 1 / (x - 1)" by simp
  moreover from assms have "ln x \<ge> ln (of_int \<lfloor>x\<rfloor>)" by (subst ln_le_cancel_iff) simp_all
  ultimately show ?thesis by simp
qed
  
lemma ln_minus_ln_floor_bigo:
  "(\<lambda>x::real. ln x - ln (floor x)) \<in> O(\<lambda>x. 1 / x)"
proof -
  have "eventually (\<lambda>x. norm (ln x - ln (floor x)) \<le> 1 * norm (1 / (x - 1))) at_top"
    using eventually_ge_at_top[of "2::real"]
  proof eventually_elim
    case (elim x)
    with ln_minus_ln_floor_bound[OF this] show ?case by auto
  qed
  hence "(\<lambda>x::real. ln x - ln (floor x)) \<in> O(\<lambda>x. 1 / (x - 1))" by (rule bigoI) 
  also have "(\<lambda>x::real. 1 / (x - 1)) \<in> O(\<lambda>x. 1 / x)" by simp
  finally show ?thesis .
qed

lemma divisor_count_asymptotics_aux:
  "(\<lambda>x. sum_upto (\<lambda>n. sum_upto (\<lambda>_. 1) (x / real n)) (sqrt x) -
                    (x * ln x / 2 + euler_mascheroni * x)) \<in> O(sqrt)"
proof -
  define R where "R = (\<lambda>x. \<Sum>i\<in>{0<..nat \<lfloor>sqrt x\<rfloor>}. frac (x / real i))"
  define S where "S = (\<lambda>x. ln (real (nat \<lfloor>sqrt x\<rfloor>)) - ln x / 2)"
  have R_bound: "R x \<in> {0..sqrt x}" if x: "x \<ge> 0" for x
  proof -
    have "R x \<le> (\<Sum>i\<in>{0<..nat \<lfloor>sqrt x\<rfloor>}. 1)" unfolding R_def by (intro sum_mono frac_le_1)
    also from x have "\<dots> = of_int \<lfloor>sqrt x\<rfloor>" by simp
    also have "\<dots> \<le> sqrt x" by simp
    finally have "R x \<le> sqrt x" .
    moreover have "R x \<ge> 0" unfolding R_def by (intro sum_nonneg) simp_all
    ultimately show ?thesis by simp
  qed
  have R_bound': "norm (R x) \<le> 1 * norm (sqrt x)" if "x \<ge> 0" for x 
    using R_bound[OF that] that by simp
  have R_bigo: "R \<in> O(sqrt)" using eventually_ge_at_top[of "0::real"]
    by (intro bigoI[of _ 1], elim eventually_mono) (rule R_bound')
  
  have "eventually (\<lambda>x. sum_upto (\<lambda>n. sum_upto (\<lambda>_. 1 :: real) (x / real n)) (sqrt x) =
                          x * harm (nat \<lfloor>sqrt x\<rfloor>) - R x) at_top"
    using eventually_ge_at_top[of "0 :: real"]
  proof eventually_elim
    case (elim x)
    have "sum_upto (\<lambda>n. sum_upto (\<lambda>_. 1 :: real) (x / real n)) (sqrt x) = 
            (\<Sum>i\<in>{0<..nat \<lfloor>sqrt x\<rfloor>}. of_int \<lfloor>x / real i\<rfloor>)" using elim
      by (simp add: sum_upto_altdef)
    also have "\<dots> = x * (\<Sum>i\<in>{0<..nat \<lfloor>sqrt x\<rfloor>}. 1 / real i) - R x"
      by (simp add: sum_subtractf frac_def R_def sum_distrib_left)
    also have "{0<..nat \<lfloor>sqrt x\<rfloor>} = {1..nat \<lfloor>sqrt x\<rfloor>}" by auto
    also have "(\<Sum>i\<in>\<dots>. 1 / real i) = harm (nat \<lfloor>sqrt x\<rfloor>)" by (simp add: harm_def divide_simps)
    finally show ?case .
  qed
  hence "(\<lambda>x. sum_upto (\<lambda>n. sum_upto (\<lambda>_. 1 :: real) (x / real n)) (sqrt x) -
                (x * ln x / 2 + euler_mascheroni * x)) \<in> 
         \<Theta>(\<lambda>x. x * (harm (nat \<lfloor>sqrt x\<rfloor>) - (ln (nat \<lfloor>sqrt x\<rfloor>) + euler_mascheroni)) - R x + x * S x)" 
   (is "_ \<in> \<Theta>(?A)")
   by (intro bigthetaI_cong) (elim eventually_mono, simp_all add: algebra_simps S_def)
  also have "?A \<in> O(sqrt)"
  proof (intro sum_in_bigo)
    have "(\<lambda>x. - S x) \<in> \<Theta>(\<lambda>x. ln (sqrt x) - ln (of_int \<lfloor>sqrt x\<rfloor>))"
      by (intro bigthetaI_cong eventually_mono [OF eventually_ge_at_top[of "1::real"]]) 
         (auto simp: S_def ln_sqrt)
    also have "(\<lambda>x. ln (sqrt x) - ln (of_int \<lfloor>sqrt x\<rfloor>)) \<in> O(\<lambda>x. 1 / sqrt x)"
      by (rule landau_o.big.compose[OF ln_minus_ln_floor_bigo sqrt_at_top])
    finally have "(\<lambda>x. x * S x) \<in> O(\<lambda>x. x * (1 / sqrt x))" by (intro landau_o.big.mult) simp_all
    also have "(\<lambda>x::real. x * (1 / sqrt x)) \<in> \<Theta>(\<lambda>x. sqrt x)"
      by (intro bigthetaI_cong eventually_mono [OF eventually_gt_at_top[of "0::real"]]) 
         (auto simp: field_simps)
    finally show "(\<lambda>x. x * S x) \<in> O(sqrt)" .
  next
    let ?f = "\<lambda>x::real. harm (nat \<lfloor>sqrt x\<rfloor>) - (ln (real (nat \<lfloor>sqrt x\<rfloor>)) + euler_mascheroni)"
    have "?f \<in> O(\<lambda>x. 1 / real (nat \<lfloor>sqrt x\<rfloor>))"
    proof (rule landau_o.big.compose[of _ _ _ "\<lambda>x. nat \<lfloor>sqrt x\<rfloor>"])
      show "filterlim (\<lambda>x::real. nat \<lfloor>sqrt x\<rfloor>) at_top at_top"
        by (intro filterlim_compose[OF filterlim_nat_sequentially]
                  filterlim_compose[OF filterlim_floor_sequentially] sqrt_at_top)
    next
      show "(\<lambda>a. harm a - (ln (real a) + euler_mascheroni)) \<in> O(\<lambda>a. 1 / real a)"
        by (rule harm_expansion_bigo_simple2)
    qed
    also have "(\<lambda>x. 1 / real (nat \<lfloor>sqrt x\<rfloor>)) \<in> O(\<lambda>x. 1 / (sqrt x - 1))"
    proof (rule bigoI[of _ 1], use eventually_ge_at_top[of 2] in eventually_elim)
      case (elim x)
      have "sqrt x \<le> 1 + real_of_int \<lfloor>sqrt x\<rfloor>" by linarith
      with elim show ?case by (simp add: field_simps)
    qed
    also have "(\<lambda>x::real. 1 / (sqrt x - 1)) \<in> O(\<lambda>x. 1 / sqrt x)"
      by (rule landau_o.big.compose[OF _ sqrt_at_top]) simp_all
    finally have "(\<lambda>x. x * ?f x) \<in> O(\<lambda>x. x * (1 / sqrt x))" 
      by (intro landau_o.big.mult landau_o.big_refl)
    also have "(\<lambda>x::real. x * (1 / sqrt x)) \<in> \<Theta>(\<lambda>x. sqrt x)"
      by (intro bigthetaI_cong eventually_mono[OF eventually_gt_at_top[of "0::real"]]) 
         (auto elim!: eventually_mono simp: field_simps)
    finally show "(\<lambda>x. x * ?f x) \<in> O(sqrt)" .
  qed fact+
  finally show ?thesis .
qed

lemma sum_upto_sqrt_bound:
  assumes x: "x \<ge> (0 :: real)"
  shows   "norm ((sum_upto (\<lambda>_. 1) (sqrt x))\<^sup>2 - x) \<le> 2 * norm (sqrt x)"
proof -
  from x have "0 \<le> 2 * sqrt x * (1 - frac (sqrt x)) + frac (sqrt x) ^ 2"
    by (intro add_nonneg_nonneg mult_nonneg_nonneg) (simp_all add: frac_le_1)
  also from x have "\<dots> = (sqrt x - frac (sqrt x)) ^ 2 - x + 2 * sqrt x"
    by (simp add: algebra_simps power2_eq_square)
  also have "sqrt x - frac (sqrt x) = of_int \<lfloor>sqrt x\<rfloor>" by (simp add: frac_def)
  finally have "(of_int \<lfloor>sqrt x\<rfloor>) ^ 2 - x \<ge> -2 * sqrt x" by (simp add: algebra_simps)
  moreover from x have "of_int (\<lfloor>sqrt x\<rfloor>) ^ 2 \<le> sqrt x ^ 2"
    by (intro power_mono) simp_all
  with x have "of_int (\<lfloor>sqrt x\<rfloor>) ^ 2 - x \<le> 0" by simp
  ultimately have "sum_upto (\<lambda>_. 1) (sqrt x) ^ 2 - x \<in> {-2 * sqrt x..0}"
    using x by (simp add: sum_upto_altdef)
  with x show ?thesis by simp
qed

lemma summatory_divisor_count_asymptotics:
  "(\<lambda>x. sum_upto (\<lambda>n. real (divisor_count n)) x -
          (x * ln x + (2 * euler_mascheroni - 1) * x)) \<in> O(sqrt)"
proof -
  let ?f = "\<lambda>x. x * ln x / 2 + euler_mascheroni * x"
  have "(\<lambda>x. sum_upto (dirichlet_prod (\<lambda>_. 1 :: real) (\<lambda>_. 1)) x - (?f x + ?f x - x)) \<in> O(sqrt)"
    (is "?g \<in> _")
  proof (rule hyperbola_method_bigo)
    have "eventually (\<lambda>x::real. norm (sum_upto (\<lambda>_. 1) (sqrt x) ^ 2 - x) \<le> 
             2 * norm (sqrt x)) at_top"
      using eventually_ge_at_top[of "0::real"] by eventually_elim (rule sum_upto_sqrt_bound)
    thus "(\<lambda>x::real. sum_upto (\<lambda>_. 1) (sqrt x) * sum_upto (\<lambda>_. 1) (sqrt x) - x) \<in> O(sqrt)"
      by (intro bigoI[of _ 2]) (simp_all add: power2_eq_square)
  next
    show "(\<lambda>x. sum_upto (\<lambda>n. 1 * sum_upto (\<lambda>_. 1) (x / real n)) (sqrt x) -
                 (x * ln x / 2 + euler_mascheroni * x)) \<in> O(sqrt)"
      using divisor_count_asymptotics_aux by simp
  next
    show "(\<lambda>x. sum_upto (\<lambda>n. sum_upto (\<lambda>_. 1) (x / real n) * 1) (sqrt x) -
                 (x * ln x / 2 + euler_mascheroni * x)) \<in> O(sqrt)"
      using divisor_count_asymptotics_aux by simp
  qed
  also have "divisor_count n = dirichlet_prod (\<lambda>_. 1) (\<lambda>_. 1) n" for n
    using fds_divisor_count
    by (cases "n = 0") (simp_all add: fds_eq_iff power2_eq_square fds_nth_mult)
  hence "?g = (\<lambda>x. sum_upto (\<lambda>n. real (divisor_count n)) x - 
               (x * ln x + (2 * euler_mascheroni - 1) * x))"
    by (intro ext) (simp_all add: algebra_simps dirichlet_prod_def)
  finally show ?thesis .
qed

theorem summatory_divisor_count_asymptotics':
  "(\<lambda>x. sum_upto (\<lambda>n. real (divisor_count n)) x) =o 
     (\<lambda>x. x * ln x + (2 * euler_mascheroni - 1) * x) +o O(\<lambda>x. sqrt x)"
  using summatory_divisor_count_asymptotics
  by (subst set_minus_plus [symmetric]) (simp_all add: fun_diff_def)

theorem summatory_divisor_count_asymptotics'':
  "sum_upto (\<lambda>n. real (divisor_count n)) \<sim>[at_top] (\<lambda>x. x * ln x)"
proof -
  have "(\<lambda>x. sum_upto (\<lambda>n. real (divisor_count n)) x - 
           (x * ln x + (2 * euler_mascheroni - 1) * x)) \<in> O(sqrt)"
    by (rule summatory_divisor_count_asymptotics)
  also have "sqrt \<in> \<Theta>(\<lambda>x. x powr (1/2))"
    by (intro bigthetaI_cong eventually_mono [OF eventually_ge_at_top[of "0::real"]]) 
       (auto elim!: eventually_mono simp: powr_half_sqrt)
  also have "(\<lambda>x::real. x powr (1/2)) \<in> o(\<lambda>x. x * ln x + (2 * euler_mascheroni - 1) * x)" by simp
  finally have "sum_upto (\<lambda>n. real (divisor_count n)) \<sim>[at_top]
                  (\<lambda>x. x * ln x + (2 * euler_mascheroni - 1) * x)"
    by (simp add: asymp_equiv_altdef)
  also have "\<dots> \<sim>[at_top] (\<lambda>x. x * ln x)" by (subst asymp_equiv_add_right) simp_all
  finally show ?thesis .
qed

lemma summatory_divisor_eq:
  "sum_upto (\<lambda>n. real (divisor_count n)) (real m) = card {(n,d). n \<in> {0<..m} \<and> d dvd n}"
proof -
  have "sum_upto (\<lambda>n. real (divisor_count n)) m = card (SIGMA n:{0<..m}. {d. d dvd n})"
    unfolding sum_upto_altdef divisor_count_def by (subst card_SigmaI) simp_all
  also have "(SIGMA n:{0<..m}. {d. d dvd n}) = {(n,d). n \<in> {0<..m} \<and> d dvd n}" by auto
  finally show ?thesis .
qed

context
  fixes M :: "nat \<Rightarrow> real"
  defines "M \<equiv> \<lambda>m. card {(n,d). n \<in> {0<..m} \<and> d dvd n} / card {0<..m}"
begin

lemma mean_divisor_count_asymptotics:
  "(\<lambda>m. M m - (ln m + 2 * euler_mascheroni - 1)) \<in> O(\<lambda>m. 1 / sqrt m)"
proof -
  have "(\<lambda>m. M m - (ln m + 2 * euler_mascheroni - 1)) 
          \<in> \<Theta>(\<lambda>m. (sum_upto (\<lambda>n. real (divisor_count n)) (real m) -
                 (m * ln m + (2 * euler_mascheroni - 1) * m)) / m)" (is "_ \<in> \<Theta>(?f)")
    unfolding M_def 
    by (intro bigthetaI_cong eventually_mono [OF eventually_gt_at_top[of "0::nat"]]) 
       (auto simp: summatory_divisor_eq field_simps)
  also have "?f \<in> O(\<lambda>m. sqrt m / m)"
    by (intro landau_o.big.compose[OF _ filterlim_real_sequentially] landau_o.big.divide_right
          summatory_divisor_count_asymptotics eventually_at_top_not_equal)
  also have "(\<lambda>m::nat. sqrt m / m) \<in> \<Theta>(\<lambda>m. 1 / sqrt m)"
    by (intro bigthetaI_cong eventually_mono [OF eventually_gt_at_top[of "0::nat"]]) 
       (auto simp: field_simps)
  finally show ?thesis .
qed

theorem mean_divisor_count_asymptotics':
  "M =o (\<lambda>x. ln x + 2 * euler_mascheroni - 1) +o O(\<lambda>x. 1 / sqrt x)"
  using mean_divisor_count_asymptotics
  by (subst set_minus_plus [symmetric]) (simp_all add: fun_diff_def)

theorem mean_divisor_count_asymptotics'': "M \<sim>[at_top] ln"
proof -
  have "(\<lambda>x. M x - (ln x + 2 * euler_mascheroni - 1)) \<in> O(\<lambda>x. 1 / sqrt x)"
    by (rule mean_divisor_count_asymptotics)
  also have "(\<lambda>x. 1 / sqrt (real x)) \<in> \<Theta>(\<lambda>x. x powr (-1/2))"
    using eventually_gt_at_top[of "0::nat"] 
    by (intro bigthetaI_cong) 
       (auto elim!: eventually_mono simp: powr_half_sqrt field_simps powr_minus)
  also have "(\<lambda>x::nat. x powr (-1/2)) \<in> o(\<lambda>x. ln x + 2 * euler_mascheroni - 1)"
    by (intro smallo_real_nat_transfer) simp_all
  finally have "M \<sim>[at_top] (\<lambda>x. ln x + 2 * euler_mascheroni - 1)"
    by (simp add: asymp_equiv_altdef)
  also have "\<dots> = (\<lambda>x::nat. ln x + (2 * euler_mascheroni - 1))" by (simp add: algebra_simps)
  also have "\<dots> \<sim>[at_top] (\<lambda>x::nat. ln x)" by (subst asymp_equiv_add_right) auto
  finally show ?thesis .
qed

end


subsection \<open>The asymptotic ditribution of coprime pairs\<close>

context
  fixes A :: "nat \<Rightarrow> (nat \<times> nat) set"
  defines "A \<equiv> (\<lambda>N. {(m,n) \<in> {1..N} \<times> {1..N}. coprime m n})"  
begin

lemma coprime_pairs_asymptotics:
  "(\<lambda>N. real (card (A N)) - 6 / pi\<^sup>2 * (real N)\<^sup>2) \<in> O(\<lambda>N. real N * ln (real N))"
proof -
  define C :: "nat \<Rightarrow> (nat \<times> nat) set"
    where "C = (\<lambda>N. (\<Union>m\<in>{1..N}. (\<lambda>n. (m,n)) ` totatives m))"
  define D :: "nat \<Rightarrow> (nat \<times> nat) set"
    where "D = (\<lambda>N. (\<Union>n\<in>{1..N}. (\<lambda>m. (m,n)) ` totatives n))"
  have fin: "finite (C N)" "finite (D N)" for N unfolding C_def D_def
    by (intro finite_UN_I finite_imageI; simp)+    
  
  have *: "card (A N) = 2 * (\<Sum>m\<in>{0<..N}. totient m) - 1" if N: "N > 0" for N
  proof -
    have "A N = C N \<union> D N"
      by (auto simp add: A_def C_def D_def totatives_def image_iff ac_simps)
    also have "card \<dots> = card (C N) + card (D N) - card (C N \<inter> D N)"
      using card_Un_Int[OF fin[of N]] by arith
    also have "C N \<inter> D N = {(1, 1)}" using N by (auto simp: image_iff totatives_def C_def D_def)
    also have "D N = (\<lambda>(x,y). (y,x)) ` C N" by (simp add: image_UN image_image C_def D_def)
    also have "card \<dots> = card (C N)" by (rule card_image) (simp add: inj_on_def C_def)
    also have "card (C N) = (\<Sum>m\<in>{1..N}. card ((\<lambda>n. (m,n)) ` totatives m))"
      unfolding C_def by (intro card_UN_disjoint) auto
    also have "\<dots> = (\<Sum>m\<in>{1..N}. totient m)" unfolding totient_def
      by (subst card_image) (auto simp: inj_on_def)
    also have "\<dots> = (\<Sum>m\<in>{0<..N}. totient m)" by (intro sum.cong refl) auto
    finally show "card (A N) = 2 * \<dots> - 1" by simp
  qed
  have **: "(\<Sum>m\<in>{0<..N}. totient m) \<ge> 1" if "N \<ge> 1" for N
  proof -
    have "1 \<le> N" by fact
    also have "N = (\<Sum>m\<in>{0<..N}. 1)" by simp
    also have "(\<Sum>m\<in>{0<..N}. 1) \<le> (\<Sum>m\<in>{0<..N}. totient m)" 
      by (intro sum_mono) (simp_all add: Suc_le_eq)
    finally show ?thesis .
  qed
  
  have "(\<lambda>N. real (card (A N)) - 6 / pi\<^sup>2 * (real N)\<^sup>2) \<in>
          \<Theta>(\<lambda>N. 2 * (sum_upto (\<lambda>m. real (totient m)) (real N) - (3 / pi\<^sup>2 * (real N)\<^sup>2)) - 1)"
    (is "_ \<in> \<Theta>(?f)") using * **
    by (intro bigthetaI_cong eventually_mono [OF eventually_gt_at_top[of "0::nat"]]) 
       (auto simp: of_nat_diff sum_upto_altdef)
  also have "?f \<in> O(\<lambda>N. real N * ln (real N))"
  proof (rule landau_o.big.compose[OF _ filterlim_real_sequentially], rule sum_in_bigo)
    show " (\<lambda>x. 2 * (sum_upto (\<lambda>m. real (totient m)) x - 3 / pi\<^sup>2 * x\<^sup>2)) \<in> O(\<lambda>x. x * ln x)"
      by (subst landau_o.big.cmult_in_iff, simp, rule summatory_totient_asymptotics)
  qed simp_all
  finally show ?thesis .
qed

theorem coprime_pairs_asymptotics':
  "(\<lambda>N. real (card (A N))) =o (\<lambda>N. 6 / pi\<^sup>2 * (real N)\<^sup>2) +o O(\<lambda>N. real N * ln (real N))"
  using coprime_pairs_asymptotics
  by (subst set_minus_plus [symmetric]) (simp_all add: fun_diff_def)

theorem coprime_pairs_asymptotics'':
  "(\<lambda>N. real (card (A N))) \<sim>[at_top] (\<lambda>N. 6 / pi\<^sup>2 * (real N)\<^sup>2)"
proof -
  have "(\<lambda>N. real (card (A N)) - 6 / pi\<^sup>2 * (real N) ^ 2) \<in> O(\<lambda>N. real N * ln (real N))"
    by (rule coprime_pairs_asymptotics)
  also have "(\<lambda>N. real N * ln (real N)) \<in> o(\<lambda>N. 6 / pi ^ 2 * real N ^ 2)"
    by (rule landau_o.small.compose[OF _ filterlim_real_sequentially]) simp
  finally show ?thesis by (simp add: asymp_equiv_altdef)
qed

theorem coprime_probability_tendsto:
  "(\<lambda>N. card (A N) / card ({1..N} \<times> {1..N})) \<longlonglongrightarrow> 6 / pi\<^sup>2"
proof -
  have "(\<lambda>N. 6 / pi ^ 2) \<sim>[at_top] (\<lambda>N. 6 / pi ^ 2 * real N ^ 2 / real N ^ 2)" 
    using eventually_gt_at_top[of "0::nat"]
    by (intro asymp_equiv_refl_ev) (auto elim!: eventually_mono)
  also have "\<dots> \<sim>[at_top] (\<lambda>N. real (card (A N)) / real N ^ 2)"
    by (intro asymp_equiv_intros asymp_equiv_symI[OF coprime_pairs_asymptotics''])
  also have "\<dots> \<sim>[at_top] (\<lambda>N. real (card (A N)) / real (card ({1..N} \<times> {1..N})))"
    by (simp add: power2_eq_square)
  finally have "\<dots> \<sim>[at_top] (\<lambda>_. 6 / pi ^ 2)" by (simp add: asymp_equiv_sym)
  thus ?thesis by (rule asymp_equivD_const)
qed

end


subsection \<open>The asymptotics of the number of Farey fractions\<close>

definition farey_fractions :: "nat \<Rightarrow> rat set" where
  "farey_fractions N = {q :: rat \<in> {0<..1}. snd (quotient_of q) \<le> int N}  "

lemma Fract_eq_coprime: 
  assumes "Rat.Fract a b = Rat.Fract c d" "b > 0" "d > 0" "coprime a b" "coprime c d"
  shows   "a = c" "b = d"
proof -
  from assms have "a * d = c * b" by (auto simp: eq_rat)
  hence "abs (a * d) = abs (c * b)" by (simp only:)
  hence "abs a * abs d = abs c * abs b" by (simp only: abs_mult)
  also have "?this \<longleftrightarrow> abs a = abs c \<and> d = b" 
    using assms by (subst coprime_crossproduct_int) simp_all
  finally show "b = d" by simp
  with \<open>a * d = c * b\<close> and \<open>b > 0\<close> show "a = c" by simp
qed
  
lemma quotient_of_split: 
  "P (quotient_of q) = (\<forall>a b. b > 0 \<longrightarrow> coprime a b \<longrightarrow> q = Rat.Fract a b \<longrightarrow> P (a, b))"
  by (cases q) (auto simp: quotient_of_Fract dest: Fract_eq_coprime)

lemma quotient_of_split_asm: 
  "P (Rat.quotient_of q) = (\<not>(\<exists>a b. b > 0 \<and> coprime a b \<and> q = Rat.Fract a b \<and> \<not>P (a, b)))"
  using quotient_of_split[of P q] by blast

lemma farey_fractions_bij:
  "bij_betw (\<lambda>(a,b). Rat.Fract (int a) (int b)) 
     {(a,b)|a b. 0 < a \<and> a \<le> b \<and> b \<le> N \<and> coprime a b} (farey_fractions N)"
proof (rule bij_betwI[of _ _ _ "\<lambda>q. case quotient_of q of (a, b) \<Rightarrow> (nat a, nat b)"], goal_cases)
  case 1
  show ?case
    by (auto simp: farey_fractions_def Rat.zero_less_Fract_iff Rat.Fract_le_one_iff 
                   Rat.quotient_of_Fract Rat.normalize_def gcd_int_def Let_def)
next
  case 2
  show ?case
    by (auto simp add: farey_fractions_def Rat.Fract_le_one_iff Rat.zero_less_Fract_iff split: prod.splits quotient_of_split_asm)
      (simp add: coprime_int_iff [symmetric])
next
  case (3 x)
  thus ?case by (auto simp: Rat.quotient_of_Fract Rat.normalize_def Let_def gcd_int_def)
next
  case (4 x)
  thus ?case unfolding farey_fractions_def
    by (split quotient_of_split) (auto simp: Rat.zero_less_Fract_iff)
qed

lemma card_farey_fractions: "card (farey_fractions N) = sum totient {0<..N}"
proof -
  have "card (farey_fractions N) = card {(a,b)|a b. 0 < a \<and> a \<le> b \<and> b \<le> N \<and> coprime a b}"
    using farey_fractions_bij by (rule bij_betw_same_card [symmetric])
  also have "{(a,b)|a b. 0 < a \<and> a \<le> b \<and> b \<le> N \<and> coprime a b} =
               (\<Union>b\<in>{0<..N}. (\<lambda>a. (a, b)) ` totatives b)"
    by (auto simp: totatives_def image_iff)
  also have "card \<dots> = (\<Sum>b\<in>{0<..N}. card ((\<lambda>a. (a, b)) ` totatives b))"
    by (intro card_UN_disjoint) auto
  also have "\<dots> = (\<Sum>b\<in>{0<..N}. totient b)"
    unfolding totient_def by (intro sum.cong refl card_image) (auto simp: inj_on_def)
  finally show ?thesis .
qed

lemma card_farey_fractions_asymptotics:
  "(\<lambda>N. real (card (farey_fractions N)) - 3 / pi\<^sup>2 * (real N)\<^sup>2) \<in> O(\<lambda>N. real N * ln (real N))"
proof -
  have "(\<lambda>N. sum_upto (\<lambda>n. real (totient n)) (real N) - 3 / pi\<^sup>2 * (real N)\<^sup>2) 
            \<in> O(\<lambda>N. real N * ln (real N))" (is "?f \<in> _")
    using summatory_totient_asymptotics filterlim_real_sequentially 
    by (rule landau_o.big.compose)
  also have "?f = (\<lambda>N. real (card (farey_fractions N)) - 3 / pi\<^sup>2 * (real N)\<^sup>2)"
    by (intro ext) (simp add: sum_upto_altdef card_farey_fractions)
  finally show ?thesis .
qed

theorem card_farey_fractions_asymptotics':
  "(\<lambda>N. card (farey_fractions N)) =o (\<lambda>N. 3 / pi\<^sup>2 * N^2) +o O(\<lambda>N. N * ln N)"
  using card_farey_fractions_asymptotics
  by (subst set_minus_plus [symmetric]) (simp_all add: fun_diff_def)

theorem card_farey_fractions_asymptotics'':
  "(\<lambda>N. real (card (farey_fractions N))) \<sim>[at_top] (\<lambda>N. 3 / pi\<^sup>2 * (real N)\<^sup>2)"
proof -
  have "(\<lambda>N. real (card (farey_fractions N)) - 3 / pi\<^sup>2 * (real N) ^ 2) \<in> O(\<lambda>N. real N * ln (real N))"
    by (rule card_farey_fractions_asymptotics)
  also have "(\<lambda>N. real N * ln (real N)) \<in> o(\<lambda>N. 3 / pi ^ 2 * real N ^ 2)"
    by (rule landau_o.small.compose[OF _ filterlim_real_sequentially]) simp
  finally show ?thesis by (simp add: asymp_equiv_altdef)
qed

end
