(*
  File:    Rational_FPS_Asymptotics.thy
  Author:  Manuel Eberl, TU München
*)
theory Rational_FPS_Asymptotics
imports
  "HOL-Library.Landau_Symbols"
  "HOL-Analysis.Analysis"
  "Polynomial_Factorization.Square_Free_Factorization"
  "HOL-Real_Asymp.Real_Asymp"
  "Count_Complex_Roots.Count_Complex_Roots"
  Linear_Homogenous_Recurrences
  Linear_Inhomogenous_Recurrences
  RatFPS
  Rational_FPS_Solver
  "HOL-Library.Code_Target_Numeral"
begin

lemma poly_asymp_equiv:
  assumes "p \<noteq> 0" and "F \<le> at_infinity"
  shows   "poly p \<sim>[F] (\<lambda>x. lead_coeff p * x ^ degree p)"
proof -
  have poly_pCons': "poly (pCons a q) = (\<lambda>x. a + x * poly q x)" for a :: 'a and q
    by (simp add: fun_eq_iff)
  show ?thesis using assms(1)
  proof (induction p)
    case (pCons a p)
    define n where "n = Suc (degree p)"
    show ?case
    proof (cases "p = 0")
      case [simp]: False
      hence *: "poly p \<sim>[F] (\<lambda>x. lead_coeff p * x ^ degree p)"
        by (intro pCons.IH)
      have "poly (pCons a p) = (\<lambda>x. a + x * poly p x)"
        by (simp add: poly_pCons')
      moreover have "\<dots> \<sim>[F] (\<lambda>x. lead_coeff p * x ^ n)"
      proof (subst asymp_equiv_add_left)
        have "(\<lambda>x. x * poly p x) \<sim>[F] (\<lambda>x. x * (lead_coeff p * x ^ degree p))"
          by (intro asymp_equiv_intros *)
        also have "\<dots> = (\<lambda>x. lead_coeff p * x ^ n)" by (simp add: n_def mult_ac)
        finally show "(\<lambda>x. x * poly p x) \<sim>[F] \<dots>" .
      next
        have "filterlim (\<lambda>x. x) at_infinity F"
          by (simp add: filterlim_def assms)
        hence "(\<lambda>x. x ^ n) \<in> \<omega>[F](\<lambda>_. 1 :: 'a)" unfolding smallomega_1_conv_filterlim
          by (intro Limits.filterlim_power_at_infinity filterlim_ident) (auto simp: n_def)
        hence "(\<lambda>x. a) \<in> o[F](\<lambda>x. x ^ n)" unfolding smallomega_iff_smallo[symmetric]
          by (cases "a = 0") auto
        thus "(\<lambda>x. a) \<in> o[F](\<lambda>x. lead_coeff p * x ^ n)"
          by simp
      qed
      ultimately show ?thesis by (simp add: n_def)
    qed auto
  qed auto
qed

lemma poly_bigtheta:
  assumes "p \<noteq> 0" and "F \<le> at_infinity"
  shows   "poly p \<in> \<Theta>[F](\<lambda>x. x ^ degree p)"
proof -
  have "poly p \<sim>[F] (\<lambda>x. lead_coeff p * x ^ degree p)"
    by (intro poly_asymp_equiv assms)
  thus ?thesis using assms by (auto dest!: asymp_equiv_imp_bigtheta)
qed

lemma poly_bigo:
  assumes "F \<le> at_infinity" and "degree p \<le> k"
  shows   "poly p \<in> O[F](\<lambda>x. x ^ k)"
proof (cases "p = 0")
  case True
  hence "poly p = (\<lambda>_. 0)" by (auto simp: fun_eq_iff)
  thus ?thesis by simp
next
  case False
  have *: "(\<lambda>x. x ^ (k - degree p)) \<in> \<Omega>[F](\<lambda>x. 1)"
  proof (cases "k = degree p")
    case False
    hence "(\<lambda>x. x ^ (k - degree p)) \<in> \<omega>[F](\<lambda>_. 1)"
      unfolding smallomega_1_conv_filterlim using assms False
      by (intro Limits.filterlim_power_at_infinity filterlim_ident)
         (auto simp: filterlim_def)
    thus ?thesis by (rule landau_omega.small_imp_big)
  qed auto

  have "poly p \<in> \<Theta>[F](\<lambda>x. x ^ degree p * 1)"
    using poly_bigtheta[OF False assms(1)] by simp
  also have "(\<lambda>x. x ^ degree p * 1) \<in> O[F](\<lambda>x. x ^ degree p * x ^ (k - degree p))" using *
    by (intro landau_o.big.mult landau_o.big_refl) (auto simp: bigomega_iff_bigo)
  also have "(\<lambda>x::'a. x ^ degree p * x ^ (k - degree p)) = (\<lambda>x. x ^ k)"
    using assms by (simp add: power_add [symmetric])
  finally show ?thesis .
qed

lemma reflect_poly_dvdI:
  fixes p q :: "'a::{comm_semiring_1,semiring_no_zero_divisors} poly"
  assumes "p dvd q"
  shows   "reflect_poly p dvd reflect_poly q"
  using assms by (auto simp: reflect_poly_mult)

lemma smult_altdef: "smult c p = [:c:] * p"
  by (induction p) (auto simp: mult_ac)

lemma smult_power: "smult (c ^ n) (p ^ n) = (smult c p) ^ n"
proof -
  have "smult (c ^ n) (p ^ n) = [:c ^ n:] * p ^ n"
    by simp
  also have "[:c:] ^ n = [:c ^ n:]"
    by (induction n) (auto simp: mult_ac)
  hence "[:c ^ n:] = [:c:] ^ n" ..
  also have "\<dots> * p ^ n = ([:c:] * p) ^ n"
    by (rule power_mult_distrib [symmetric])
  also have "\<dots> = (smult c p) ^ n" by simp
  finally show ?thesis .
qed

lemma order_reflect_poly_ge:
  fixes c :: "'a :: field"
  assumes "c \<noteq> 0" and "p \<noteq> 0"
  shows   "order c (reflect_poly p) \<ge> order (1 / c) p"
proof -
  have "reflect_poly ([:-(1 / c), 1:] ^ order (1 / c) p) dvd reflect_poly p"
    by (intro reflect_poly_dvdI, subst order_divides) auto
  also have "reflect_poly ([:-(1 / c), 1:] ^ order (1 / c) p) =
               smult ((-1 / c) ^ order (1 / c) p) ([:-c, 1:] ^ order (1 / c) p)"
    using assms by (simp add: reflect_poly_power reflect_poly_pCons smult_power)
  finally have "([:-c, 1:] ^ order (1 / c) p) dvd reflect_poly p"
    by (rule smult_dvd_cancel)
  with \<open>p \<noteq> 0\<close> show ?thesis by (subst (asm) order_divides) auto
qed

lemma order_reflect_poly:
  fixes c :: "'a :: field"
  assumes "c \<noteq> 0" and "coeff p 0 \<noteq> 0"
  shows   "order c (reflect_poly p) = order (1 / c) p"
proof (rule antisym)
  from assms show "order c (reflect_poly p) \<ge> order (1 / c) p"
    by (intro order_reflect_poly_ge) auto
next
  from assms have "order (1 / (1 / c)) (reflect_poly p) \<le>
                     order (1 / c) (reflect_poly (reflect_poly p))"
    by (intro order_reflect_poly_ge) auto
  with assms show "order c (reflect_poly p) \<le> order (1 / c) p"
    by simp
qed

lemma poly_reflect_eq_0_iff:
  "poly (reflect_poly p) (x :: 'a :: field) = 0 \<longleftrightarrow> p = 0 \<or> x \<noteq> 0 \<and> poly p (1 / x) = 0"
  by (cases "x = 0") (auto simp: poly_reflect_poly_nz inverse_eq_divide)
  

theorem ratfps_nth_bigo:
  fixes q :: "complex poly"
  assumes "R > 0" 
  assumes roots1: "\<And>z. z \<in> ball 0 (1 / R) \<Longrightarrow> poly q z \<noteq> 0"
  assumes roots2: "\<And>z. z \<in> sphere 0 (1 / R) \<Longrightarrow> poly q z = 0 \<Longrightarrow> order z q \<le> Suc k"
  shows   "fps_nth (fps_of_poly p / fps_of_poly q) \<in> O(\<lambda>n. of_nat n ^ k * of_real R ^ n)"
proof -
  define q' where "q' = reflect_poly q"
  from roots1[of 0] and \<open>R > 0\<close> have [simp]: "coeff q 0 \<noteq> 0" "q \<noteq> 0"
    by (auto simp: poly_0_coeff_0)
  from ratfps_closed_form_exists[OF this(1), of p] guess r rs . note closed_form = this

  have "fps_nth (fps_of_poly p / fps_of_poly q) =
          (\<lambda>n. coeff r n + (\<Sum>c | poly q' c = 0. poly (rs c) (of_nat n) * c ^ n))"
    by (intro ext, subst closed_form) (simp_all add: q'_def)
  also have "\<dots> \<in> O(\<lambda>n. of_nat n ^ k * of_real R ^ n)"
  proof (intro sum_in_bigo big_sum_in_bigo)
    have "eventually (\<lambda>n. coeff r n = 0) at_top"
      using MOST_nat coeff_eq_0 cofinite_eq_sequentially by force
    hence "coeff r \<in> \<Theta>(\<lambda>_. 0)" by (rule bigthetaI_cong)
    also have "(\<lambda>_. 0 :: complex) \<in> O(\<lambda>n. of_nat n ^ k * of_real R ^ n)"
      by simp
    finally show "coeff r \<in> O(\<lambda>n. of_nat n ^ k * of_real R ^ n)" .
  next
    fix c assume c: "c \<in> {c. poly q' c = 0}"
    hence [simp]: "c \<noteq> 0" by (auto simp: q'_def)

    show "(\<lambda>n. poly (rs c) n * c ^ n) \<in> O(\<lambda>n. of_nat n ^ k * of_real R ^ n)"
    proof (cases "norm c = R")
      case True \<comment>\<open>The case of a root at the border of the disc\<close>
      show ?thesis
      proof (intro landau_o.big.mult landau_o.big.compose[OF poly_bigo tendsto_of_nat])
        have "degree (rs c) \<le> order c (reflect_poly q) - 1"
          using c by (intro closed_form(2)) (auto simp: q'_def)
        also have "order c (reflect_poly q) = order (1 / c) q"
          using c by (intro order_reflect_poly) (auto simp: q'_def)
        also {
          have "order (1 / c) q \<le> Suc k" using \<open>R > 0\<close> and True and c
            by (intro roots2) (auto simp: q'_def norm_divide poly_reflect_eq_0_iff)
          moreover have "order (1 / c) q \<noteq> 0"
            using order_root[of q "1 / c"] c by (auto simp: q'_def poly_reflect_eq_0_iff)
          ultimately have "order (1 / c) q - 1 \<le> k" by simp
        }
        finally show "degree (rs c) \<le> k" .
      next
        have "(\<lambda>n. norm (c ^ n)) \<in> O(\<lambda>n. norm (complex_of_real R ^ n))"
          using True and \<open>R > 0\<close> by (simp add: norm_power)
        thus "(\<lambda>n. c ^ n) \<in> O(\<lambda>n. complex_of_real R ^ n)"
          by (subst (asm) landau_o.big.norm_iff)
      qed auto
    next
      case False  \<comment>\<open>The case of a root in the interior of the disc\<close>
      hence "norm c < R" using c and roots1[of "1/c"] and \<open>R > 0\<close>
        by (cases "norm c" R rule: linorder_cases)
           (auto simp: q'_def poly_reflect_eq_0_iff norm_divide field_simps)
      define l where "l = degree (rs c)"

      have "(\<lambda>n. poly (rs c) (of_nat n) * c ^ n) \<in> O(\<lambda>n. of_nat n ^ l * c ^ n)"
        by (intro landau_o.big.mult landau_o.big.compose[OF poly_bigo tendsto_of_nat])
           (auto simp: l_def)
      also have "(\<lambda>n. of_nat n ^ l * c ^ n) \<in> O(\<lambda>n. of_nat n ^ k * of_real R ^ n)"
      proof (subst landau_o.big.norm_iff [symmetric])
        have "(\<lambda>n. real n ^ l) \<in> O(\<lambda>n. real n ^ k * (R / norm c) ^ n)"
          using \<open>norm c < R\<close> and \<open>R > 0\<close> by real_asymp
        hence "(\<lambda>n. real n ^ l * norm c ^ n) \<in> O(\<lambda>n. real n ^ k * R ^ n)"
          by (simp add: power_divide landau_o.big.divide_eq1)
        thus "(\<lambda>x. norm (of_nat x ^ l * c ^ x)) \<in> 
                O(\<lambda>x. norm (of_nat x ^ k * complex_of_real R ^ x))"
          unfolding norm_power norm_mult using \<open>R > 0\<close> by simp
      qed
      finally show ?thesis .
    qed
  qed
  finally show ?thesis .
qed

lemma order_power: "p \<noteq> 0 \<Longrightarrow> order c (p ^ n) = n * order c p"
  by (induction n) (auto simp: order_mult)

lemma same_root_imp_not_coprime:
  assumes "poly p x = 0" and "poly q (x :: 'a :: {factorial_ring_gcd}) = 0"
  shows   "\<not>coprime p q"
proof
  assume "coprime p q"
  from assms have "[:-x, 1:] dvd p" and "[:-x, 1:] dvd q"
    by (simp_all add: poly_eq_0_iff_dvd)
  hence "[:-x, 1:] dvd gcd p q" by (simp add: poly_eq_0_iff_dvd)
  also from \<open>coprime p q\<close> have "gcd p q = 1"
    by (rule coprime_imp_gcd_eq_1)
  finally show False by (elim is_unit_polyE) auto
qed



lemma ratfps_nth_bigo_square_free_factorization:
  fixes p :: "complex poly"
  assumes "square_free_factorization q (b, cs)"
  assumes "q \<noteq> 0" and "R > 0"
  assumes roots1: "\<And>c l. (c, l) \<in> set cs \<Longrightarrow> \<forall>x\<in>ball 0 (1 / R). poly c x \<noteq> 0"
  assumes roots2: "\<And>c l. (c, l) \<in> set cs \<Longrightarrow> l > k \<Longrightarrow> \<forall>x\<in>sphere 0 (1 / R). poly c x \<noteq> 0"
  shows   "fps_nth (fps_of_poly p / fps_of_poly q) \<in> O(\<lambda>n. of_nat n ^ k * of_real R ^ n)"
proof -
  from assms(1) have q: "q = smult b (\<Prod>(c, l)\<in>set cs. c ^ Suc l)"
    unfolding square_free_factorization_def prod.case by blast 
  with \<open>q \<noteq> 0\<close> have [simp]: "b \<noteq> 0" by auto

  from assms(1) have [simp]: "(0, x) \<notin> set cs" for x
    by (auto simp: square_free_factorization_def)
  from assms(1) have coprime: "c1 = c2" "m = n"
    if "\<not>coprime c1 c2" "(c1, m) \<in> set cs" "(c2, n) \<in> set cs" for c1 c2 m n
    using that by (auto simp: square_free_factorization_def case_prod_unfold)

  show ?thesis
  proof (rule ratfps_nth_bigo)
    fix z :: complex assume z: "z \<in> ball 0 (1 / R)"
    show "poly q z \<noteq> 0"
    proof
      assume "poly q z = 0"
      then obtain c l where cl: "(c, l) \<in> set cs" and "poly c z = 0"
        by (auto simp: q poly_prod image_iff)
      with roots1[of c l] and z show False by auto
    qed
  next
    fix z :: complex assume z: "z \<in> sphere 0 (1 / R)"

    have order: "order z q = order z (\<Prod>(c, l)\<in>set cs. c ^ Suc l)"
      by (simp add: order_smult q)
    also have "\<dots> = (\<Sum>x\<in>set cs. order z (case x of (c, l) \<Rightarrow> c ^ Suc l))"
      by (subst order_prod) (auto dest: coprime)
    also have "\<dots> = (\<Sum>(c, l)\<in>set cs. Suc l * order z c)"
      unfolding case_prod_unfold by (intro sum.cong refl, subst order_power) auto
    finally have "order z q = \<dots>" .

    show "order z q \<le> Suc k"
    proof (cases "\<exists>c0 l0. (c0, l0) \<in> set cs \<and> poly c0 z = 0")
      case False
      have "order z q = (\<Sum>(c, l)\<in>set cs. Suc l * order z c)" by fact
      also have "order z c = 0" if "(c, l) \<in> set cs" for c l
        using False that by (auto simp: order_root)
      hence "(\<Sum>(c, l)\<in>set cs. Suc l * order z c) = 0"
        by (intro sum.neutral) auto
      finally show "order z q \<le> Suc k" by simp
    next
      case True \<comment>\<open>The order of a root is determined by the unique polynomial in the
                   square-free factorisation that contains it.\<close>
      then obtain c0 l0 where cl0: "(c0, l0) \<in> set cs" "poly c0 z = 0"
        by blast
      have "order z q = (\<Sum>(c, l)\<in>set cs. Suc l * order z c)" by fact
      also have "\<dots> = Suc l0 * order z c0 + (\<Sum>(c, l) \<in> set cs - {(c0, l0)}. Suc l * order z c)"
        using cl0 by (subst sum.remove[of _ "(c0, l0)"]) auto
      also have "(\<Sum>(c, l) \<in> set cs - {(c0, l0)}. Suc l * order z c) = 0"
      proof (intro sum.neutral ballI, goal_cases)
        case (1 cl)
        then obtain c l where [simp]: "cl = (c, l)" and cl: "(c, l) \<in> set cs" "(c0, l0) \<noteq> (c, l)"
          by (cases cl) auto
        from cl and cl0 and coprime[of c c0 l l0] have "coprime c c0"
          by auto
        with same_root_imp_not_coprime[of c z c0] and cl0 have "poly c z \<noteq> 0" by auto
        thus ?case by (auto simp: order_root)
      qed
      also have "square_free c0" using cl0 assms(1)
        by (auto simp: square_free_factorization_def)
      hence "rsquarefree c0" by (rule square_free_rsquarefree)
      with cl0 have "order z c0 = 1"
        by (auto simp: rsquarefree_def' order_root intro: antisym)
      finally have "order z q = Suc l0" by simp

      also from roots2[of c0 l0] cl0 z have "l0 \<le> k"
        by (cases l0 k rule: linorder_cases) auto
      finally show "order z q \<le> Suc k" by simp
    qed
  qed fact+
qed

find_consts name:"Count_Complex"
term proots_ball_card
term proots_sphere_card

lemma proots_within_card_zero_iff:
  assumes "p \<noteq> (0 :: 'a :: idom poly)"
  shows   "card (proots_within p A) = 0 \<longleftrightarrow> (\<forall>x\<in>A. poly p x \<noteq> 0)"
  using assms by (subst card_0_eq) (auto intro: finite_proots)


lemma ratfps_nth_bigo_square_free_factorization':
  fixes p :: "complex poly"
  assumes "square_free_factorization q (b, cs)"
  assumes "q \<noteq> 0" and "R > 0"
  assumes roots1: "list_all (\<lambda>cl. proots_ball_card (fst cl) 0 (1 / R) = 0) cs"
  assumes roots2: "list_all (\<lambda>cl. proots_sphere_card (fst cl) 0 (1 / R) = 0)
                     (filter (\<lambda>cl. snd cl > k) cs)"
  shows   "fps_nth (fps_of_poly p / fps_of_poly q) \<in> O(\<lambda>n. of_nat n ^ k * of_real R ^ n)"
proof (rule ratfps_nth_bigo_square_free_factorization[OF assms(1)])
  from assms(1) have q: "q = smult b (\<Prod>(c, l)\<in>set cs. c ^ Suc l)"
    unfolding square_free_factorization_def prod.case by blast 
  with \<open>q \<noteq> 0\<close> have [simp]: "b \<noteq> 0" by auto
  from assms(1) have [simp]: "(0, x) \<notin> set cs" for x
    by (auto simp: square_free_factorization_def)

  show "\<forall>x\<in>ball 0 (1 / R). poly c x \<noteq> 0" if "(c, l) \<in> set cs" for c l
  proof -
    from roots1 that have "card (proots_within c (ball 0 (1 / R))) = 0"
      by (auto simp: proots_ball_card_def list_all_def)
    with that show ?thesis by (subst (asm) proots_within_card_zero_iff) auto
  qed

  show "\<forall>x\<in>sphere 0 (1 / R). poly c x \<noteq> 0" if "(c, l) \<in> set cs" "l > k" for c l
  proof -
    from roots2 that have "card (proots_within c (sphere 0 (1 / R))) = 0"
      by (auto simp: proots_sphere_card_def list_all_def)
    with that show ?thesis by (subst (asm) proots_within_card_zero_iff) auto
  qed
qed fact+

definition ratfps_has_asymptotics where
  "ratfps_has_asymptotics q k R \<longleftrightarrow> q \<noteq> 0 \<and> R > 0 \<and>
     (let cs = snd (yun_factorization gcd q)
      in  list_all (\<lambda>cl. proots_ball_card (fst cl) 0 (1 / R) = 0) cs \<and>
          list_all (\<lambda>cl. proots_sphere_card (fst cl) 0 (1 / R) = 0) (filter (\<lambda>cl. snd cl > k) cs))"

lemma ratfps_has_asymptotics_correct:
  assumes "ratfps_has_asymptotics q k R"
  shows   "fps_nth (fps_of_poly p / fps_of_poly q) \<in> O(\<lambda>n. of_nat n ^ k * of_real R ^ n)"
proof (rule ratfps_nth_bigo_square_free_factorization')
  show "square_free_factorization q (fst (yun_factorization gcd q), snd (yun_factorization gcd q))"
    by (rule yun_factorization) simp
qed (insert assms, auto simp: ratfps_has_asymptotics_def Let_def list_all_def)


value "map (fps_nth (fps_of_poly [:0, 1:] / fps_of_poly [:1, -1, -1 :: real:])) [0..<5]"




method ratfps_bigo = (rule ratfps_has_asymptotics_correct; eval)

lemma "fps_nth (fps_of_poly [:0, 1:] / fps_of_poly [:1, -1, -1 :: complex:]) \<in>
         O(\<lambda>n. of_nat n ^ 0 * complex_of_real 1.618034 ^ n)"
  by ratfps_bigo

lemma "fps_nth (fps_of_poly 1 / fps_of_poly [:1, -3, 3, -1 :: complex:]) \<in>
         O(\<lambda>n. of_nat n ^ 2 * complex_of_real 1 ^ n)"
  by ratfps_bigo

lemma "fps_nth (fps_of_poly f / fps_of_poly [:5, 4, 3, 2, 1 :: complex:]) \<in>
         O(\<lambda>n. of_nat n ^ 0 * complex_of_real 0.69202 ^ n)"
  by ratfps_bigo

end
