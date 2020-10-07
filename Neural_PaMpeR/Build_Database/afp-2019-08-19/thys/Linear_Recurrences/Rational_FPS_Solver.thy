(*
  File:    Rational_FPS_Solver.thy
  Author:  Manuel Eberl, TU München
*)
section \<open>Solver for rational formal power series\<close>

theory Rational_FPS_Solver
imports
  Complex_Main
  Pochhammer_Polynomials
  Partial_Fraction_Decomposition
  Factorizations
  "HOL-Computational_Algebra.Field_as_Ring"
begin

text \<open>
  We can determine the $k$-th coefficient of an FPS of the form $d/(1-cX)^n$, which is
  an important step in solving linear recurrences. The $k$-th coefficient of such an FPS is always
  of the form $p(k) c^k$ where $p$ is the following polynomial:
\<close>

definition inverse_irred_power_poly :: "'a :: field_char_0 \<Rightarrow> nat \<Rightarrow> 'a poly" where
  "inverse_irred_power_poly d n =
       Poly [(d * of_nat (stirling n (k+1))) / (fact (n - 1)). k \<leftarrow> [0..<n]]"

lemma one_minus_const_fps_X_neg_power'':
  fixes c :: "'a :: field_char_0"
  assumes n: "n > 0"
  shows "fps_const d / ((1 - fps_const (c :: 'a :: field_char_0) * fps_X) ^ n) =
           Abs_fps (\<lambda>k. poly (inverse_irred_power_poly d n) (of_nat k) * c^k)" (is "?lhs = ?rhs")
proof (rule fps_ext)
  include fps_notation
  fix k :: nat
  let ?p = "smult (d / (fact (n - 1))) (pcompose (pochhammer_poly (n - 1)) [:1,1:])"
  from n have "?lhs = fps_const d * inverse ((1 - fps_const c * fps_X) ^ n)"
    by (subst fps_divide_unit) auto
  also have "inverse ((1 - fps_const c * fps_X) ^ n) =
                 Abs_fps (\<lambda>k. of_nat ((n + k - 1) choose k) * c^k)"
    by (intro one_minus_const_fps_X_neg_power' n)
  also have "(fps_const d * \<dots>) $ k  = d * of_nat ((n + k - 1) choose k) * c^k" by simp
  also from n have "(n + k - 1 choose k) = (n + k - 1 choose (n - 1))"
    by (subst binomial_symmetric) simp_all
  also from n have "of_nat \<dots> = (pochhammer (of_nat k + 1) (n - 1) / fact (n - 1) :: 'a)"
    by (simp_all add: binomial_gbinomial gbinomial_pochhammer' of_nat_diff)
  also have "d * \<dots> = poly ?p (of_nat k)"
    by (simp add: divide_inverse eval_pochhammer_poly poly_pcompose add_ac)
  also {
    from assms have "pCons 0 (pcompose (pochhammer_poly (n-1)) [:1,1::'a:]) = pochhammer_poly n"
      by (subst pochhammer_poly_Suc' [symmetric]) simp
    also from assms have "\<dots> = pCons 0 (Poly [of_nat (stirling n (k+1)). k \<leftarrow> [0..<Suc n]])"
      unfolding pochhammer_poly_def
      by (auto simp add: poly_eq_iff nth_default_def coeff_pCons
               split: nat.split simp del: upt_Suc )
    finally have "pcompose (pochhammer_poly (n-1)) [:1,1::'a:] =
                      Poly [of_nat (stirling n (k+1)). k \<leftarrow> [0..<Suc n]]" by simp
  }
  also have "smult (d / fact (n - 1)) (Poly [of_nat (stirling n (k+1)). k \<leftarrow> [0..<Suc n]]) =
               inverse_irred_power_poly d n"
    by (auto simp: poly_eq_iff inverse_irred_power_poly_def nth_default_def)
  also have "poly \<dots> (of_nat k) * c ^ k = ?rhs $ k" by simp
  finally show "?lhs $ k = ?rhs $ k" .
qed

lemma inverse_irred_power_poly_code [code abstract]:
  "coeffs (inverse_irred_power_poly d n) =
    (if n = 0 \<or> d = 0 then [] else
     let e = d / (fact (n - 1))
     in  [e * of_nat x. x \<leftarrow> tl (stirling_row n)])"
proof (cases "n = 0 \<or> d = 0")
  case False
  define e where "e = d / (fact (n - 1))"
  from False have "coeffs (inverse_irred_power_poly d n) =
                     [e * of_nat (stirling n (k+1)). k \<leftarrow> [0..<n]]"
    by (auto simp: inverse_irred_power_poly_def Let_def divide_inverse mult_ac last_map
                   stirling_row_def map_tl [symmetric] tl_upt e_def no_trailing_unfold)
  also have "\<dots> = [e * of_nat x. x \<leftarrow> tl (stirling_row n)]"
    by (simp add: stirling_row_def map_tl [symmetric] o_def tl_upt
                  map_Suc_upt [symmetric] del: upt_Suc)
  finally show ?thesis using False by (simp add: Let_def e_def)
qed (auto simp: inverse_irred_power_poly_def)

lemma solve_rat_fps_aux:
  fixes p :: "'a :: {field_char_0,factorial_ring_gcd,normalization_euclidean_semiring} poly" and cs :: "('a \<times> nat) list"
  assumes distinct: "distinct (map fst cs)"
  assumes azs: "(a, zs) = poly_pfd_simple p cs"
  assumes nz: "0 \<notin> fst ` set cs"
  shows "fps_of_poly p / fps_of_poly (\<Prod>(c,n)\<leftarrow>cs. [:1,-c:]^Suc n) =
           Abs_fps (\<lambda>k. coeff a k + (\<Sum>i<length cs. poly (\<Sum>j\<le>snd (cs ! i).
                   (inverse_irred_power_poly (zs ! i ! j) (snd (cs ! i)+1 - j)))
               (of_nat k) * (fst (cs ! i)) ^ k))" (is "_ = ?rhs")
proof -
  interpret pfd_homomorphism "fps_of_poly :: 'a poly \<Rightarrow> 'a fps"
    by standard (auto simp: fps_of_poly_add fps_of_poly_mult)
  from distinct have distinct': "(a, b1) \<in> set cs \<Longrightarrow>
    (a, b2) \<in> set cs \<Longrightarrow> b1 = b2" for a b1 b2
    by (metis (no_types, hide_lams) Some_eq_map_of_iff image_set in_set_zipE insert_iff list.simps(15) map_of_Cons_code(2) map_of_SomeD nz snd_conv)
  from nz have nz': "(0, b) \<notin> set cs" for b
    by (auto simp add: image_iff)
  define n where "n = length cs"
  let ?g = "\<lambda>(c, n). [:1, - c:] ^ Suc n"
  have "inj_on ?g (set cs)"
  proof
    fix x y
    assume "x \<in> set cs" "y \<in> set cs" "?g x = ?g y"
    moreover obtain c1 n1 c2 n2 where [simp]: "x = (c1, n1)" "y = (c2, n2)"
      by (cases x, cases y)
    ultimately have in_cs: "(c1, n1) \<in> set cs"
      "(c2, n2) \<in> set cs"
      and eq: "[:1, - c1:] ^ Suc n1 = [:1, - c2:] ^ Suc n2"
      by simp_all
    with nz have [simp]: "c1 \<noteq> 0" "c2 \<noteq> 0"
      by (auto simp add: image_iff)
    have "Suc n1 = degree ([:1, - c1:] ^ Suc n1)"
      by (simp add: degree_power_eq del: power_Suc)
    also have "\<dots> = degree ([:1, - c2:] ^ Suc n2)"
      using eq by simp
    also have "\<dots> = Suc n2"
      by (simp add: degree_power_eq del: power_Suc)
    finally have "n1 = n2" by simp
    then have "0 = poly ([:1, - c1:] ^ Suc n1) (1 / c1)"
      by simp
    also have "\<dots> = poly ([:1, - c2:] ^ Suc n2) (1 / c1)"
      using eq by simp
    finally show "x = y" using \<open>n1 = n2\<close>
      by (auto simp: field_simps)
  qed
  with distinct have distinct': "distinct (map ?g cs)"
    by (simp add: distinct_map del: power_Suc)
  from nz' distinct have coprime: "pairwise coprime (?g ` set cs)"
    by (auto intro!: pairwise_imageI coprime_linear_poly' simp add: eq_key_imp_eq_value
      simp del: power_Suc)
  have [simp]: "length zs = n"
    using assms by (simp add: poly_pfd_simple_def n_def split: if_split_asm)
  have [simp]: "i < length cs \<Longrightarrow> length (zs!i) = snd (cs!i)+1" for i
   using assms by (simp add: poly_pfd_simple_def Let_def case_prod_unfold split: if_split_asm)

  let ?f = "\<lambda>(c, n). ([:1,-c:], n)"
  let ?cs' = "map ?f cs"
  have "fps_of_poly (fst (poly_pfd_simple p cs)) +
          (\<Sum>i<length ?cs'. \<Sum>j\<le>snd (?cs' ! i).
               from_decomp (map (map (\<lambda>c. [:c:])) (snd (poly_pfd_simple p cs)) ! i ! j)
                           (fst (?cs' ! i)) (snd (?cs' ! i)+1 - j)) =
          fps_of_poly p / fps_of_poly (\<Prod>(x, n)\<leftarrow>?cs'. x ^ Suc n)"
          (is "?A = ?B") using nz distinct' coprime
    by (intro partial_fraction_decomposition poly_pfd_simple)
       (force simp: o_def case_prod_unfold simp del: power_Suc)+
  note this [symmetric]
  also from azs [symmetric]
    have "?A = fps_of_poly a + (\<Sum>i<n. \<Sum>j\<le>snd (cs ! i). from_decomp
                  (map (map (\<lambda>c. [:c:])) zs ! i ! j) [:1,-fst (cs ! i):] (snd (cs ! i)+1 - j))"
      (is "_ = _ + ?S") by (simp add: case_prod_unfold Let_def n_def)
  also have "?S = (\<Sum>i<length cs. \<Sum>j\<le>snd (cs ! i). fps_const (zs ! i ! j) /
                      ((1 - fps_const (fst (cs!i))*fps_X) ^ (snd (cs!i)+1 - j)))"
    by (intro sum.cong refl)
       (auto simp: from_decomp_def map_nth n_def fps_of_poly_linear' fps_of_poly_simps
                    fps_const_neg [symmetric] mult_ac simp del: fps_const_neg)
  also have "\<dots> = (\<Sum>i<length cs. \<Sum>j\<le>snd (cs ! i) .
                      Abs_fps (\<lambda>k. poly (inverse_irred_power_poly (zs ! i ! j)
                          (snd (cs ! i)+1 - j)) (of_nat k) * (fst (cs ! i)) ^ k))"
    using nz by (intro sum.cong refl one_minus_const_fps_X_neg_power'') auto
  also have "fps_of_poly a + \<dots> = ?rhs"
    by (intro fps_ext) (simp_all add: sum_distrib_right fps_sum_nth poly_sum)
  finally show ?thesis by (simp add: o_def case_prod_unfold)
qed



definition solve_factored_ratfps ::
    "('a :: {field_char_0,factorial_ring_gcd,normalization_euclidean_semiring}) poly \<Rightarrow> ('a \<times> nat) list \<Rightarrow> 'a poly \<times> ('a poly \<times> 'a) list" where
  "solve_factored_ratfps p cs = (let n = length cs in case poly_pfd_simple p cs of (a, zs) \<Rightarrow>
      (a, zip_with (\<lambda>zs (c,n). ((\<Sum>(z,j) \<leftarrow> zip zs [0..<Suc n].
              inverse_irred_power_poly z (n + 1 - j)), c)) zs cs))"

lemma length_snd_poly_pfd_simple [simp]: "length (snd (poly_pfd_simple p cs)) = length cs"
  by (simp add: poly_pfd_simple_def)

lemma length_nth_snd_poly_pfd_simple [simp]:
  "i < length cs \<Longrightarrow> length (snd (poly_pfd_simple p cs) ! i) = snd (cs!i) + 1"
  by (auto simp: poly_pfd_simple_def case_prod_unfold Let_def)

lemma solve_factored_ratfps_roots:
  "map snd (snd (solve_factored_ratfps p cs)) = map fst cs"
  by (rule nth_equalityI)
     (simp_all add: solve_factored_ratfps_def poly_pfd_simple case_prod_unfold Let_def
                    zip_with_altdef o_def)


definition interp_ratfps_solution where
  "interp_ratfps_solution = (\<lambda>(p,cs) n. coeff p n + (\<Sum>(q,c)\<leftarrow>cs. poly q (of_nat n) * c ^ n))"

lemma solve_factored_ratfps:
  fixes p :: "'a :: {field_char_0,factorial_ring_gcd,normalization_euclidean_semiring} poly" and cs :: "('a \<times> nat) list"
  assumes distinct: "distinct (map fst cs)"
  assumes nz: "0 \<notin> fst ` set cs"
  shows "fps_of_poly p / fps_of_poly (\<Prod>(c,n)\<leftarrow>cs. [:1,-c:]^Suc n) =
           Abs_fps (interp_ratfps_solution (solve_factored_ratfps p cs))" (is "?lhs = ?rhs")
proof -
  obtain a zs where azs: "(a, zs) = solve_factored_ratfps p cs"
    using prod.exhaust by metis
  from azs have a: "a = fst (poly_pfd_simple p cs)"
    by (simp add: solve_factored_ratfps_def Let_def case_prod_unfold)
  define zs' where "zs' = snd (poly_pfd_simple p cs)"
  with a have azs': "(a, zs') = poly_pfd_simple p cs" by simp
  from azs have zs: "zs = snd (solve_factored_ratfps p cs)"
    by (auto simp add: snd_def split: prod.split)

  have "?lhs = Abs_fps (\<lambda>k. coeff a k + (\<Sum>i<length cs. poly (\<Sum>j\<le>snd (cs ! i).
                 inverse_irred_power_poly (zs' ! i ! j) (snd (cs ! i)+1 - j))
                 (of_nat k) * (fst (cs ! i)) ^ k))"
    by (rule solve_rat_fps_aux[OF distinct azs' nz])
  also from azs have "\<dots> = ?rhs" unfolding interp_ratfps_solution_def
    by (auto simp: a zs solve_factored_ratfps_def Let_def case_prod_unfold zip_altdef
                   zip_with_altdef' sum_list_sum_nth atLeast0LessThan zs'_def lessThan_Suc_atMost
             intro!: fps_ext sum.cong simp del: upt_Suc)
  finally show ?thesis .
qed


definition solve_factored_ratfps' where
  "solve_factored_ratfps' = (\<lambda>p (a,cs). solve_factored_ratfps (smult (inverse a) p) cs)"

lemma solve_factored_ratfps':
  assumes "is_alt_factorization_of fctrs q" "q \<noteq> 0"
  shows   "Abs_fps (interp_ratfps_solution (solve_factored_ratfps' p fctrs)) =
             fps_of_poly p / fps_of_poly q"
proof -
  from assms have q: "q = interp_alt_factorization fctrs"
    by (simp add: is_alt_factorization_of_def)
  from assms(2) have nz: "fst fctrs \<noteq> 0"
    by (subst (asm) q) (auto simp: interp_alt_factorization_def case_prod_unfold)
  note q
  also from nz have "coeff (interp_alt_factorization fctrs) 0 \<noteq> 0"
    by (auto simp: interp_alt_factorization_def case_prod_unfold coeff_0_prod_list
                   o_def coeff_0_power prod_list_zero_iff)
  finally have "coeff q 0 \<noteq> 0" .

  obtain a cs where fctrs: "fctrs = (a, cs)" by (cases fctrs) simp_all
  obtain b zs where sol: "solve_factored_ratfps' p fctrs = (b, zs)" using prod.exhaust by metis
  from assms have [simp]: "a \<noteq> 0"
    by (auto simp: is_alt_factorization_of_def interp_alt_factorization_def fctrs)

  have "fps_of_poly p / fps_of_poly (smult a (\<Prod>(c, n)\<leftarrow>cs. [:1, - c:] ^ Suc n)) =
          fps_of_poly p / (fps_const a * fps_of_poly (\<Prod>(c, n)\<leftarrow>cs. [:1, - c:] ^ Suc n))"
    by (simp_all add: fps_of_poly_smult case_prod_unfold del: power_Suc)
  also have "\<dots> = fps_of_poly p / fps_const a / fps_of_poly (\<Prod>(c, n)\<leftarrow>cs. [:1, - c:] ^ Suc n)"
    by (subst is_unit_div_mult2_eq)
       (auto simp: coeff_0_power coeff_0_prod_list prod_list_zero_iff)
  also have "fps_of_poly p / fps_const a = fps_of_poly (smult (inverse a) p)"
    by (simp add: fps_const_inverse fps_divide_unit)
  also from assms have "smult a (\<Prod>(c, n)\<leftarrow>cs. [:1, - c:] ^ Suc n) = q"
    by (simp add: is_alt_factorization_of_def interp_alt_factorization_def fctrs del: power_Suc)
  also have "fps_of_poly (smult (inverse a) p) /
                   fps_of_poly (\<Prod>(c, n)\<leftarrow>cs. [:1, - c:] ^ Suc n) =
               Abs_fps (interp_ratfps_solution (solve_factored_ratfps (smult (inverse a) p) cs))"
    (is "?lhs = _") using assms
    by (intro solve_factored_ratfps)
       (simp_all add: is_alt_factorization_of_def fctrs solve_factored_ratfps'_def)
  also have "\<dots> = Abs_fps (interp_ratfps_solution (solve_factored_ratfps' p fctrs))"
    by (simp add: solve_factored_ratfps'_def fctrs)
  finally show ?thesis ..
qed

lemma degree_Poly_eq:
  assumes "xs = [] \<or> last xs \<noteq> 0"
  shows   "degree (Poly xs) = length xs - 1"
proof -
  from assms consider "xs = []" | "xs \<noteq> []" "last xs \<noteq> 0" by blast
  thus ?thesis
  proof cases
    assume "last xs \<noteq> 0" "xs \<noteq> []"
    hence "no_trailing ((=) 0) xs" by (auto simp: no_trailing_unfold)
    thus ?thesis by (simp add: degree_eq_length_coeffs)
  qed auto
qed

lemma degree_Poly': "degree (Poly xs) \<le> length xs - 1"
  using length_strip_while_le[of "(=) 0" xs] by (simp add: degree_eq_length_coeffs)

lemma degree_inverse_irred_power_poly_le:
  "degree (inverse_irred_power_poly c n) \<le> n - 1"
  by (auto simp: inverse_irred_power_poly_def intro: order.trans[OF degree_Poly'])

lemma degree_inverse_irred_power_poly:
  assumes "c \<noteq> 0"
  shows   "degree (inverse_irred_power_poly c n) = n - 1"
  unfolding inverse_irred_power_poly_def using assms
  by (subst degree_Poly_eq) (auto simp: last_conv_nth)


lemma reflect_poly_0_iff [simp]: "reflect_poly p = 0 \<longleftrightarrow> p = 0"
  using coeff_0_reflect_poly_0_iff[of p] by fastforce

lemma degree_sum_list_le: "(\<And>p. p \<in> set ps \<Longrightarrow> degree p \<le> T) \<Longrightarrow> degree (sum_list ps) \<le> T"
  by (induction ps) (auto intro: degree_add_le)

theorem ratfps_closed_form_exists:
  fixes q :: "complex poly"
  assumes nz: "coeff q 0 \<noteq> 0"
  defines "q' \<equiv> reflect_poly q"
  obtains r rs
  where "\<And>n. fps_nth (fps_of_poly p / fps_of_poly q) n =
                coeff r n + (\<Sum>c | poly q' c = 0. poly (rs c) (of_nat n) * c ^ n)"
  and   "\<And>z. poly q' z = 0 \<Longrightarrow> degree (rs z) \<le> order z q' - 1"
proof -
  from assms have nz': "q \<noteq> 0" by auto
  from complex_alt_factorization_exists [OF nz]
  obtain fctrs where fctrs: "is_alt_factorization_of fctrs q" ..
  with nz have fctrs': "is_factorization_of fctrs q'" unfolding q'_def
    by (rule reflect_factorization')
  define r where "r = fst (solve_factored_ratfps' p fctrs)"
  define ts where "ts = snd (solve_factored_ratfps' p fctrs)"
  define rs where "rs = the \<circ> map_of (map (\<lambda>(x,y). (y,x)) ts)"

  from nz' have "q' \<noteq> 0" by (simp add: q'_def)
  hence roots: "{z. poly q' z = 0} = set (map fst (snd fctrs))"
    using is_factorization_of_roots [of "fst fctrs" "snd fctrs" q'] fctrs' by simp

  have rs: "rs c = r" if "(r, c) \<in> set ts" for c r
  proof -
    have "map_of (map (\<lambda>(x,y). (y, x)) (snd (solve_factored_ratfps' p fctrs))) c = Some r"
      using that fctrs
      by (intro map_of_is_SomeI)
         (force simp: o_def case_prod_unfold solve_factored_ratfps'_def ts_def
                      solve_factored_ratfps_roots is_alt_factorization_of_def)+
    thus ?thesis by (simp add: rs_def ts_def)
  qed

  have [simp]: "length ts = length (snd fctrs)"
    by (auto simp: ts_def solve_factored_ratfps'_def case_prod_unfold solve_factored_ratfps_def)

  {
    fix n :: nat
    have "fps_of_poly p / fps_of_poly q =
            Abs_fps (interp_ratfps_solution (solve_factored_ratfps' p fctrs))"
      using solve_factored_ratfps' [OF fctrs nz'] ..
    also have "fps_nth \<dots> n = interp_ratfps_solution (solve_factored_ratfps' p fctrs) n"
      by simp
    also have "\<dots> = coeff r n + (\<Sum>p\<leftarrow>snd (solve_factored_ratfps' p fctrs).
                                   poly (fst p) (of_nat n) * snd p ^ n)" (is "_ = _ + ?A")
      unfolding interp_ratfps_solution_def case_prod_unfold r_def by simp
    also have "?A = (\<Sum>p\<leftarrow>ts. poly (rs (snd p)) (of_nat n) * snd p ^ n)"
      by (intro arg_cong[OF map_cong] refl) (auto simp: rs ts_def)
    also have "\<dots> = (\<Sum>c\<leftarrow>map snd ts.
                       poly (rs c) (of_nat n) * c ^ n)" by (simp add: o_def)
    also have "map snd ts = map fst (snd fctrs)"
      unfolding solve_factored_ratfps'_def case_prod_unfold ts_def
      by (rule solve_factored_ratfps_roots)
    also have "(\<Sum>c\<leftarrow>\<dots>. poly (rs c) (of_nat n) * c ^ n) =
                 (\<Sum>c | poly q' c = 0. poly (rs c) (of_nat n) * c ^ n)" unfolding roots
      using fctrs by (intro sum_list_distinct_conv_sum_set) (auto simp: is_alt_factorization_of_def)
    finally have "fps_nth (fps_of_poly p / fps_of_poly q) n =
                    coeff r n + (\<Sum>c\<in>{z. poly q' z = 0}. poly (rs c) (of_nat n) * c ^ n)" .
  } moreover {
    fix z assume "poly q' z = 0"
    hence "z \<in> set (map fst (snd fctrs))" using roots by blast
    then obtain i where i: "i < length (snd fctrs)" and [simp]: "z = fst (snd fctrs ! i)"
      by (auto simp: set_conv_nth)
    from i have "(fst (ts ! i), snd (ts ! i)) \<in> set ts"
      by (auto simp: set_conv_nth)
    also from i have "snd (ts ! i) = z"
      by (simp add: ts_def solve_factored_ratfps'_def case_prod_unfold solve_factored_ratfps_def)
    finally have "rs z = fst (ts ! i)" by (intro rs) auto
    also have "\<dots> = (\<Sum>p\<leftarrow>zip (snd (poly_pfd_simple (smult (inverse (fst fctrs)) p) (snd fctrs)) ! i)
                       [0..<Suc (snd (snd fctrs ! i))].
                         inverse_irred_power_poly (fst p) (Suc (snd (snd fctrs ! i)) - snd p))"
      using i by (auto simp: ts_def solve_factored_ratfps'_def solve_factored_ratfps_def o_def
                     case_prod_unfold Let_def simp del: upt_Suc power_Suc)
    also have "degree \<dots> \<le> snd (snd fctrs ! i)"
      by (intro degree_sum_list_le)
         (auto intro!: order.trans [OF degree_inverse_irred_power_poly_le])
    also have "order z q' = Suc \<dots>"
      using nz' fctrs' i
      by (intro is_factorization_of_order[of q' "fst fctrs" "snd fctrs"]) (auto simp: q'_def)
    hence "snd (snd fctrs ! i) = order z q' - 1" by simp
    finally have "degree (rs z) \<le> \<dots>" .
  }
  ultimately show ?thesis
    using that[of r rs] by blast
qed

end
