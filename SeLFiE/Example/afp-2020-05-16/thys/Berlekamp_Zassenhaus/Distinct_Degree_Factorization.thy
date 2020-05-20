(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
section \<open>Distinct Degree Factorization\<close>
theory Distinct_Degree_Factorization
imports 
  Finite_Field
  Polynomial_Factorization.Square_Free_Factorization 
  Berlekamp_Type_Based
begin

definition factors_of_same_degree :: "nat \<Rightarrow> 'a :: field poly \<Rightarrow> bool" where
  "factors_of_same_degree i f = (i \<noteq> 0 \<and> degree f \<noteq> 0 \<and> monic f \<and> (\<forall> g. irreducible g \<longrightarrow> g dvd f \<longrightarrow> degree g = i))" 

lemma factors_of_same_degreeD: assumes "factors_of_same_degree i f"
  shows "i \<noteq> 0" "degree f \<noteq> 0" "monic f" "g dvd f \<Longrightarrow> irreducible g = (degree g = i)" 
proof -
  note * = assms[unfolded factors_of_same_degree_def]
  show i: "i \<noteq> 0" and f: "degree f \<noteq> 0" "monic f" using * by auto
  assume gf: "g dvd f" 
  with * have "irreducible g \<Longrightarrow> degree g = i" by auto
  moreover
  {
    assume **: "degree g = i" "\<not> irreducible g" 
    with irreducible\<^sub>d_factor[of g] i obtain h1 h2 where irr: "irreducible h1" and gh: "g = h1 * h2" 
      and deg_h2: "degree h2 < degree g" by auto
    from ** i have g0: "g \<noteq> 0" by auto
    from gf gh g0 have "h1 dvd f" using dvd_mult_left by blast
    from * f this irr have deg_h: "degree h1 = i" by auto
    from arg_cong[OF gh, of degree] g0 have "degree g = degree h1 + degree h2"
      by (simp add: degree_mult_eq gh)
    with **(1) deg_h have "degree h2 = 0" by auto
    from degree0_coeffs[OF this] obtain c where h2: "h2 = [:c:]" by auto
    with gh g0 have g: "g = smult c h1" "c \<noteq> 0" by auto
    with irr **(2) irreducible_smult_field[of c h1] have False by auto
  }
  ultimately show "irreducible g = (degree g = i)" by auto
qed

(* Exercise 16 in Knuth, pages 457 and 682 *)

hide_const order
hide_const up_ring.monom

(*This theorem is field.finite_field_mult_group_has_gen but adding the order of the element.*)
theorem (in field) finite_field_mult_group_has_gen2:
  assumes finite:"finite (carrier R)"
  shows "\<exists>a \<in> carrier (mult_of R). group.ord (mult_of R) a = order (mult_of R) 
  \<and> carrier (mult_of R) = {a[^]i | i::nat . i \<in> UNIV}"
proof -
  note mult_of_simps[simp]
  have finite': "finite (carrier (mult_of R))" using finite by (rule finite_mult_of)

  interpret G: group "mult_of R" rewrites
      "([^]\<^bsub>mult_of R\<^esub>) = (([^]) :: _ \<Rightarrow> nat \<Rightarrow> _)" and "\<one>\<^bsub>mult_of R\<^esub> = \<one>"
    by (rule field_mult_group) (simp_all add: fun_eq_iff nat_pow_def)

  let ?N = "\<lambda> x . card {a \<in> carrier (mult_of R). group.ord (mult_of R) a  = x}"
  have "0 < order R - 1" unfolding Coset.order_def using card_mono[OF finite, of "{\<zero>, \<one>}"] by simp
  then have *: "0 < order (mult_of R)" using assms by (simp add: order_mult_of)
  have fin: "finite {d. d dvd order (mult_of R) }" using dvd_nat_bounds[OF *] by force

  have "(\<Sum>d | d dvd order (mult_of R). ?N d)
      = card (UN d:{d . d dvd order (mult_of R) }. {a \<in> carrier (mult_of R). group.ord (mult_of R) a  = d})"
      (is "_ = card ?U")
    using fin finite by (subst card_UN_disjoint) auto
  also have "?U = carrier (mult_of R)"
  proof
    { fix x assume x:"x \<in> carrier (mult_of R)"
      hence x':"x\<in>carrier (mult_of R)" by simp
      then have "group.ord (mult_of R) x dvd order (mult_of R)"
          using finite' G.ord_dvd_group_order[OF x'] by (simp add: order_mult_of)
      hence "x \<in> ?U" using dvd_nat_bounds[of "order (mult_of R)" "group.ord (mult_of R) x"] x by blast
    } thus "carrier (mult_of R) \<subseteq> ?U" by blast
  qed auto
  also have "card ... = Coset.order (mult_of R)"
    using order_mult_of finite' by (simp add: Coset.order_def)
  finally have sum_Ns_eq: "(\<Sum>d | d dvd order (mult_of R). ?N d) = order (mult_of R)" .

  { fix d assume d:"d dvd order (mult_of R)"
    have "card {a \<in> carrier (mult_of R). group.ord (mult_of R) a = d} \<le> phi' d"
    proof cases
      assume "card {a \<in> carrier (mult_of R). group.ord (mult_of R) a = d} = 0" thus ?thesis by presburger
      next
      assume "card {a \<in> carrier (mult_of R). group.ord (mult_of R) a = d} \<noteq> 0"
      hence "\<exists>a \<in> carrier (mult_of R). group.ord (mult_of R) a = d" by (auto simp: card_eq_0_iff)
      thus ?thesis using num_elems_of_ord_eq_phi'[OF finite d] by auto
    qed
  }
  hence all_le:"\<And>i. i \<in> {d. d dvd order (mult_of R) }
        \<Longrightarrow> (\<lambda>i. card {a \<in> carrier (mult_of R). group.ord (mult_of R) a = i}) i \<le> (\<lambda>i. phi' i) i" by fast
  hence le:"(\<Sum>i | i dvd order (mult_of R). ?N i)
            \<le> (\<Sum>i | i dvd order (mult_of R). phi' i)"
            using sum_mono[of "{d .  d dvd order (mult_of R)}"
                  "\<lambda>i. card {a \<in> carrier (mult_of R). group.ord (mult_of R) a = i}"] by presburger
  have "order (mult_of R) = (\<Sum>d | d dvd order (mult_of R). phi' d)" using *
    by (simp add: sum_phi'_factors)
  hence eq:"(\<Sum>i | i dvd order (mult_of R). ?N i)
          = (\<Sum>i | i dvd order (mult_of R). phi' i)" using le sum_Ns_eq by presburger
  have "\<And>i. i \<in> {d. d dvd order (mult_of R) } \<Longrightarrow> ?N i = (\<lambda>i. phi' i) i"
  proof (rule ccontr)
    fix i
    assume i1:"i \<in> {d. d dvd order (mult_of R)}" and "?N i \<noteq> phi' i"
    hence "?N i = 0"
      using num_elems_of_ord_eq_phi'[OF finite, of i] by (auto simp: card_eq_0_iff)
    moreover  have "0 < i" using * i1 by (simp add: dvd_nat_bounds[of "order (mult_of R)" i])
    ultimately have "?N i < phi' i" using phi'_nonzero by presburger
    hence "(\<Sum>i | i dvd order (mult_of R). ?N i)
         < (\<Sum>i | i dvd order (mult_of R). phi' i)"
      using sum_strict_mono_ex1[OF fin, of "?N" "\<lambda> i . phi' i"]
            i1 all_le by auto
    thus False using eq by force
  qed
  hence "?N (order (mult_of R)) > 0" using * by (simp add: phi'_nonzero)
  then obtain a where a:"a \<in> carrier (mult_of R)" and a_ord:"group.ord (mult_of R) a = order (mult_of R)"
    by (auto simp add: card_gt_0_iff)
  hence set_eq:"{a[^]i | i::nat. i \<in> UNIV} = (\<lambda>x. a[^]x) ` {0 .. group.ord (mult_of R) a - 1}"
    using G.ord_elems[OF finite'] by auto
  have card_eq:"card ((\<lambda>x. a[^]x) ` {0 .. group.ord (mult_of R) a - 1}) = card {0 .. group.ord (mult_of R) a - 1}"
    by (intro card_image G.ord_inj finite' a)
  hence "card ((\<lambda> x . a[^]x) ` {0 .. group.ord (mult_of R) a - 1}) = card {0 ..order (mult_of R) - 1}"
    using assms by (simp add: card_eq a_ord)
  hence card_R_minus_1:"card {a[^]i | i::nat. i \<in> UNIV} =  order (mult_of R)"
    using * by (subst set_eq) auto
  have **:"{a[^]i | i::nat. i \<in> UNIV} \<subseteq> carrier (mult_of R)"
    using G.nat_pow_closed[OF a] by auto
  with _ have "carrier (mult_of R) = {a[^]i|i::nat. i \<in> UNIV}"
    by (rule card_seteq[symmetric]) (simp_all add: card_R_minus_1 finite Coset.order_def del: UNIV_I)
  thus ?thesis using a a_ord by blast
qed

(*This lemma is a generalization of the theorem add_power_poly_mod_ring 
  which appears in Belekamp_Type_Based.thy*)

lemma add_power_prime_poly_mod_ring[simp]:
fixes x :: "'a::{prime_card} mod_ring poly"
shows "(x + y) ^ CARD('a)^n = x ^ (CARD('a)^n) + y ^ CARD('a)^n"
proof (induct n arbitrary: x y)
  case 0
  then show ?case by auto
next
  case (Suc n)
  define p where p: "p = CARD('a)"
  have "(x + y) ^ p ^ Suc n =  (x + y) ^ (p * p^n)" by simp
  also have "... = ((x + y) ^ p) ^ (p^n)"
    by (simp add: power_mult)
  also have "... = (x^p + y^p)^ (p^n)" 
    by (simp add: add_power_poly_mod_ring p)
  also have "... = (x^p)^(p^n) + (y^p)^(p^n)" using Suc.hyps unfolding p by auto
  also have "... = x^(p^(n+1)) + y^(p^(n+1))" by (simp add: power_mult)
  finally show ?case by (simp add: p)  
qed

(*This lemma is a generalization of the theorem fermat_theorem_mod_ring 
  which appears in Berlekamp_Type_Based.thy*)
lemma fermat_theorem_mod_ring2[simp]:
fixes a::"'a::{prime_card} mod_ring"
shows "a ^ (CARD('a)^n) = a"
proof (induct n arbitrary: a)
  case (Suc n)
  define p where "p = CARD('a)"
  have "a ^ p ^ Suc n = a ^ (p * (p ^ n))" by simp
  also have "... = (a ^ p) ^(p ^ n)" by (simp add: power_mult)
  also have "... = a^(p ^ n)" using fermat_theorem_mod_ring[of "a^p"] unfolding p_def by auto
  also have "... = a" using Suc.hyps p_def by auto
  finally show ?case by (simp add: p_def)
qed auto

lemma fermat_theorem_power_poly[simp]:
  fixes a::"'a::prime_card mod_ring"
  shows "[:a:] ^ CARD('a::prime_card) ^ n = [:a:]" 
  by (auto simp add: Missing_Polynomial.poly_const_pow mod_poly_less)

(* Some previous facts *)
lemma degree_prod_monom: "degree (\<Prod>i = 0..<n. monom 1 1) = n"
  by (metis degree_monom_eq prod_pow x_pow_n zero_neq_one)

lemma degree_monom0[simp]: "degree (monom a 0) = 0" using degree_monom_le by auto
lemma degree_monom0'[simp]: "degree (monom 0 b) = 0" by auto

lemma sum_monom_mod:
  assumes "b < degree f"
  shows "(\<Sum>i\<le>b. monom (g i) i) mod f = (\<Sum>i\<le>b. monom (g i) i)"
  using assms 
proof (induct b)
  case 0
  then show ?case by (auto simp add: mod_poly_less)
next
  case (Suc b)
  have hyp: "(\<Sum>i\<le>b. monom (g i) i) mod f = (\<Sum>i\<le>b. monom (g i) i)" 
    using Suc.prems Suc.hyps by simp
  have rw_monom: "monom (g (Suc b)) (Suc b) mod f = monom (g (Suc b)) (Suc b)"
    by (metis Suc.prems degree_monom_eq mod_0 mod_poly_less monom_hom.hom_0_iff)
  have rw: "(\<Sum>i\<le>Suc b. monom (g i) i) = (monom (g (Suc b)) (Suc b) + (\<Sum>i\<le>b. monom (g i) i))"
    by auto  
  have "(\<Sum>i\<le>Suc b. monom (g i) i) mod f 
    = (monom (g (Suc b)) (Suc b) + (\<Sum>i\<le>b. monom (g i) i)) mod f" using rw by presburger
  also have "... =((monom (g (Suc b)) (Suc b)) mod f) + ((\<Sum>i\<le>b. monom (g i) i) mod f)" 
    using poly_mod_add_left by auto
  also have "... = monom (g (Suc b)) (Suc b) + (\<Sum>i\<le>b. monom (g i) i)" 
    using hyp rw_monom by presburger
  also have "... = (\<Sum>i\<le>Suc b. monom (g i) i)" using rw by auto
  finally show ?case .
qed

lemma x_power_aq_minus_1_rw:
  fixes x::nat
  assumes x: "x > 1" 
    and a: "a > 0" 
    and b: "b > 0"
  shows "x ^ (a * q) - 1 = ((x^a) - 1) * sum ((^) (x^a)) {..<q}"
proof (cases "q=0")
  case False
  note q0 = False     
  have xa: "(x ^ a) > 0" using x by auto
  have int_rw1: "int (x ^ a) - 1 = int ((x ^ a) - 1)"
    using xa by linarith
  have int_rw2: "sum ((^) (int (x ^ a))) {..<q} = int (sum ((^) ((x ^ a))) {..<q})" 
    unfolding int_sum by simp
  have "int (x ^ a) ^ q = int (Suc ((x ^ a) ^ q - 1))" using xa by auto
  hence "int ((x ^ a) ^ q - 1) = int (x ^ a) ^ q - 1" using xa by presburger    
  also have "... = (int (x ^ a) - 1) * sum ((^) (int (x ^ a))) {..<q}" 
    by (rule power_diff_1_eq[OF q0])
  also have "... = (int ((x ^ a) - 1)) * int (sum ((^) ( (x ^ a))) {..<q})" 
    unfolding int_rw1 int_rw2 by simp
  also have "... = int (((x ^ a) - 1) * (sum ((^) ( (x ^ a))) {..<q}))" by auto
  finally have aux: "int ((x ^ a) ^ q - 1) = int (((x ^ a) - 1) * sum ((^) (x ^ a)) {..<q})" .     
  have "x ^ (a * q) - 1 = (x^a)^q - 1"
    by (simp add: power_mult)
  also have "... = ((x^a) - 1) * sum ((^) (x^a)) {..<q}" 
    using aux unfolding int_int_eq .
  finally show ?thesis .
qed auto

lemma dvd_power_minus_1_conv1:
  fixes x::nat
  assumes x: "x > 1" 
    and a: "a > 0" 
    and xa_dvd: "x ^ a - 1 dvd x^b - 1" 
    and b0: "b > 0"
  shows "a dvd b"
proof -
  define r where r[simp]: "r = b mod a"
  define q where q[simp]: "q = b div a"  
  have b: "b = a * q + r" by auto
  have ra: "r < a" by (simp add: a)
  hence xr_less_xa: "x ^ r - 1 < x ^ a - 1"
    using x power_strict_increasing_iff diff_less_mono x by simp
  have dvd: "x ^ a - 1 dvd x ^ (a * q) - 1"
    using x_power_aq_minus_1_rw[OF x a b0] unfolding dvd_def by auto
  have "x^b - 1 = x^b - x^r + x^r - 1"
    using assms(1) assms(4) by auto  
  also have "... = x^r * (x^(a*q) - 1) + x^r - 1"
    by (metis (no_types, lifting) b diff_mult_distrib2 mult.commute nat_mult_1_right power_add)
  finally have "x^b - 1 = x^r * (x^(a*q) - 1) + x^r - 1" .
  hence "x ^ a - 1 dvd x ^ r * (x ^ (a * q) - 1) + x ^ r - 1" using xa_dvd by presburger
  hence "x^a - 1 dvd x^r - 1" 
    by (metis (no_types) diff_add_inverse diff_commute dvd dvd_diff_nat dvd_trans dvd_triv_right)  
  hence "r = 0" 
    using xr_less_xa
    by (meson nat_dvd_not_less neq0_conv one_less_power x zero_less_diff)
  thus ?thesis by auto
qed


lemma dvd_power_minus_1_conv2:
  fixes x::nat
  assumes x: "x > 1" 
    and a: "a > 0" 
    and a_dvd_b: "a dvd b" 
    and b0: "b > 0"
  shows "x ^ a - 1 dvd x^b - 1"
proof -
  define q where q[simp]: "q = b div a"  
  have b: "b = a * q" using a_dvd_b by auto
  have "x^b - 1 = ((x ^ a) - 1) * sum ((^) (x ^ a)) {..<q}" 
    unfolding b by (rule x_power_aq_minus_1_rw[OF x a b0])
  thus ?thesis unfolding dvd_def by auto
qed

corollary dvd_power_minus_1_conv:
  fixes x::nat
  assumes x: "x > 1" 
    and a: "a > 0" 
    and b0: "b > 0"
  shows "a dvd b = (x ^ a - 1 dvd x^b - 1)"
  using assms dvd_power_minus_1_conv1 dvd_power_minus_1_conv2 by blast



(* Proof of part a) of exercise 16: given f(x) an irreducible polynomial modulo a prime p 
  of degree n, the p^n polynomials of degree less than n form a field under arithmetic 
  modulo f(x) and p.
*)


locale poly_mod_type_irr = poly_mod_type m "TYPE('a::prime_card)" for m + 
  fixes f::"'a::{prime_card} mod_ring poly"
  assumes irr_f: "irreducible\<^sub>d f"
begin

definition plus_irr :: "'a mod_ring poly \<Rightarrow>'a mod_ring poly \<Rightarrow> 'a mod_ring poly"
  where "plus_irr a b = (a + b) mod f"

definition minus_irr :: "'a mod_ring poly \<Rightarrow>'a mod_ring poly \<Rightarrow> 'a mod_ring poly"
  where "minus_irr x y \<equiv> (x - y) mod f"

definition uminus_irr :: "'a mod_ring poly \<Rightarrow>'a mod_ring poly "
  where "uminus_irr x = -x"

definition mult_irr :: "'a mod_ring poly \<Rightarrow>'a mod_ring poly \<Rightarrow> 'a mod_ring poly"
  where "mult_irr x y = ((x*y) mod f)"

definition carrier_irr :: "'a mod_ring poly set"
  where "carrier_irr = {x. degree x < degree f}"

definition power_irr :: "'a mod_ring poly \<Rightarrow> nat \<Rightarrow> 'a mod_ring poly"
  where "power_irr p n = ((p^n) mod f)"

definition "R = \<lparr>carrier = carrier_irr, monoid.mult = mult_irr, one = 1, zero = 0, add = plus_irr\<rparr>"

lemma degree_f[simp]: "degree f > 0"
  using irr_f irreducible\<^sub>dD(1) by blast

lemma element_in_carrier: "(a \<in> carrier R) = (degree a < degree f)" 
  unfolding R_def carrier_irr_def by auto

lemma f_dvd_ab:
  "a = 0 \<or> b = 0" if "f dvd a * b" 
    and a: "degree a < degree f" 
    and b: "degree b < degree f" 
proof (rule ccontr)
  assume "\<not> (a = 0 \<or> b = 0)"
  then have "a \<noteq> 0" and "b \<noteq> 0"
    by simp_all
  with a b have "\<not> f dvd a" and "\<not> f dvd b"
    by (auto simp add: mod_poly_less dvd_eq_mod_eq_0)
  moreover from \<open>f dvd a * b\<close> irr_f have "f dvd a \<or> f dvd b"
    by auto
  ultimately show False
    by simp
qed

lemma ab_mod_f0:
  "a = 0 \<or> b = 0" if "a * b mod f = 0" 
    and a: "degree a < degree f" 
    and b: "degree b < degree f" 
  using that f_dvd_ab by auto

lemma irreducible\<^sub>dD2:
  fixes p q :: "'b::{comm_semiring_1,semiring_no_zero_divisors} poly"
  assumes "irreducible\<^sub>d p"
  and  "degree q < degree p" and "degree q \<noteq> 0"
  shows "\<not> q dvd p"
  using assms irreducible\<^sub>d_dvd_smult by force


lemma times_mod_f_1_imp_0:
  assumes x: "degree x < degree f" 
    and x2: "\<forall>xa. x * xa mod f = 1 \<longrightarrow> \<not> degree xa < degree f"    
  shows "x = 0" 
proof (rule ccontr)
  assume x3: "x \<noteq> 0"
  let ?u = "fst (bezout_coefficients f x)"
  let ?v = "snd (bezout_coefficients f x)"
  have "?u * f + ?v * x = gcd f x" using bezout_coefficients_fst_snd by auto
  also have "... = 1"
  proof (rule ccontr)
    assume g: "gcd f x \<noteq> 1"
    have "degree (gcd f x) < degree f"
        by (metis degree_0 dvd_eq_mod_eq_0 gcd_dvd1 gcd_dvd2 irr_f 
            irreducible\<^sub>dD(1) mod_poly_less nat_neq_iff x x3)
    have "\<not> gcd f x dvd f"
    proof (rule irreducible\<^sub>dD2[OF irr_f])
      show "degree (gcd f x) < degree f"
        by (metis degree_0 dvd_eq_mod_eq_0 gcd_dvd1 gcd_dvd2 irr_f 
            irreducible\<^sub>dD(1) mod_poly_less nat_neq_iff x x3)
      show "degree (gcd f x) \<noteq> 0"
        by (metis (no_types, hide_lams) g degree_mod_less' gcd.bottom_left_bottom gcd_eq_0_iff 
            gcd_left_idem gcd_mod_left gr_implies_not0 x)
    qed
    moreover have "gcd f x dvd f" by auto
    ultimately show False by contradiction
  qed
  finally have "?v*x mod f = 1"
    by (metis degree_1 degree_f mod_mult_self3 mod_poly_less)
  hence "(x*(?v mod f)) mod f = 1" 
    by (simp add: mod_mult_right_eq mult.commute)
  moreover have "degree (?v mod f) < degree f"
    by (metis degree_0 degree_f degree_mod_less' not_gr_zero)
  ultimately show False using x2 by auto
qed

sublocale field_R: field R 
proof -
  have *: "\<exists>y. degree y < degree f \<and> f dvd x + y" if "degree x < degree f"
    for x :: "'a mod_ring poly"  
  proof -
    from that have "degree (- x) < degree f"
      by simp
    moreover have "f dvd (x + - x)"
      by simp
    ultimately show ?thesis
      by blast
  qed
  have **: "degree (x * y mod f) < degree f"
    if "degree x < degree f" and "degree y < degree f"
    for x y :: "'a mod_ring poly"
    using that by (cases "x = 0 \<or> y = 0")
      (auto intro: degree_mod_less' dest: f_dvd_ab)
  show "field R"
    by standard (auto simp add: R_def carrier_irr_def plus_irr_def mult_irr_def Units_def algebra_simps degree_add_less mod_poly_less mod_add_eq mult_poly_add_left mod_mult_left_eq mod_mult_right_eq mod_eq_0_iff_dvd ab_mod_f0 * ** dest: times_mod_f_1_imp_0)
qed

lemma zero_in_carrier[simp]: "0 \<in> carrier_irr" unfolding carrier_irr_def by auto

lemma card_carrier_irr[simp]: "card carrier_irr = CARD('a)^(degree f)"
proof -
  let ?A = "(carrier_vec (degree f):: 'a mod_ring vec set)"
  have bij_A_carrier: "bij_betw (Poly \<circ> list_of_vec) ?A carrier_irr" 
  proof (unfold bij_betw_def, rule conjI)
    show "inj_on (Poly \<circ> list_of_vec) ?A" by (rule inj_Poly_list_of_vec)
    show "(Poly \<circ> list_of_vec) ` ?A = carrier_irr" 
    proof (unfold image_def o_def carrier_irr_def, auto)
      fix xa assume "xa \<in> ?A" thus "degree (Poly (list_of_vec xa)) < degree f"
        using degree_Poly_list_of_vec irr_f by blast
    next
      fix x::"'a mod_ring poly" 
      assume deg_x: "degree x < degree f"
      let ?xa = "vec_of_list (coeffs x @ replicate (degree f - length (coeffs x)) 0)"
      show "\<exists>xa\<in>carrier_vec (degree f). x = Poly (list_of_vec xa)"
        by (rule bexI[of _ "?xa"], unfold carrier_vec_def, insert deg_x) 
           (auto simp add: degree_eq_length_coeffs)        
    qed
  qed 
  have "CARD('a)^(degree f) = card ?A" 
    by (simp add: card_carrier_vec)
  also have "... = card carrier_irr" using bij_A_carrier bij_betw_same_card by blast
  finally show ?thesis ..
qed

lemma finite_carrier_irr[simp]: "finite (carrier_irr)"
proof -
  have "degree f > degree 0" using degree_0 by auto
  hence "carrier_irr \<noteq> {}" using degree_0 unfolding carrier_irr_def
    by blast
  moreover have "card carrier_irr \<noteq> 0" by auto
  ultimately show ?thesis using card_eq_0_iff by metis  
qed  

lemma finite_carrier_R[simp]: "finite (carrier R)" unfolding R_def by simp

lemma finite_carrier_mult_of[simp]: "finite (carrier (mult_of R))" 
  unfolding carrier_mult_of by auto

lemma constant_in_carrier[simp]: "[:a:] \<in> carrier R"
  unfolding R_def carrier_irr_def by auto

lemma mod_in_carrier[simp]: "a mod f \<in> carrier R" 
  unfolding R_def carrier_irr_def
  by (auto, metis degree_0 degree_f degree_mod_less' less_not_refl)

lemma order_irr: "Coset.order (mult_of R) = CARD('a)^degree f - 1"
  by (simp add: card_Diff_singleton Coset.order_def carrier_mult_of R_def)
 
lemma element_power_order_eq_1:
    assumes x: "x \<in> carrier (mult_of R)" 
    shows "x [^]\<^bsub>(mult_of R)\<^esub> Coset.order (mult_of R) = \<one>\<^bsub>(mult_of R)\<^esub>"
  by (meson field_R.field_mult_group finite_carrier_mult_of group.pow_order_eq_1 x)

corollary element_power_order_eq_1': 
assumes x: "x \<in> carrier (mult_of R)"
shows"x [^]\<^bsub>(mult_of R)\<^esub> CARD('a)^degree f = x"
proof -  
  have "x [^]\<^bsub>(mult_of R)\<^esub> CARD('a)^degree f 
  = x \<otimes>\<^bsub>(mult_of R)\<^esub> x [^]\<^bsub>(mult_of R)\<^esub> (CARD('a)^degree f - 1)" 
    by (metis Diff_iff One_nat_def Suc_pred field_R.m_comm field_R.nat_pow_Suc field_R.nat_pow_closed 
        mult_of_simps(1) mult_of_simps(2) nat_pow_mult_of neq0_conv power_eq_0_iff x zero_less_card_finite)  
  also have "x \<otimes>\<^bsub>(mult_of R)\<^esub> x [^]\<^bsub>(mult_of R)\<^esub> (CARD('a)^degree f - 1) = x"     
    by (metis carrier_mult_of element_power_order_eq_1 field_R.Units_closed field_R.field_Units 
        field_R.r_one monoid.simps(2) mult_mult_of mult_of_def order_irr x)
  finally show ?thesis .  
qed  

lemma pow_irr[simp]: "x [^]\<^bsub>(R)\<^esub> n= x^n mod f"
  by (induct n, auto simp add: mod_poly_less nat_pow_def R_def mult_of_def mult_irr_def 
      carrier_irr_def mod_mult_right_eq mult.commute)

lemma pow_irr_mult_of[simp]: "x [^]\<^bsub>(mult_of R)\<^esub> n= x^n mod f"
  by (induct n, auto simp add: mod_poly_less nat_pow_def R_def mult_of_def mult_irr_def 
      carrier_irr_def mod_mult_right_eq mult.commute)

lemma fermat_theorem_power_poly_R[simp]: "[:a:] [^]\<^bsub>R\<^esub> CARD('a) ^ n = [:a:]"
  by (auto simp add: Missing_Polynomial.poly_const_pow mod_poly_less)

lemma times_mod_expand:
  "(a \<otimes>\<^bsub>(R)\<^esub> b) = ((a mod f) \<otimes>\<^bsub>(R)\<^esub> (b mod f))"
  by (simp add: mod_mult_eq R_def mult_irr_def)

(*Elements that satisfy y^p^m = y in the field are closed under addition and multiplication.*)
lemma mult_closed_power:
assumes x: "x \<in> carrier R" and y: "y \<in> carrier R"
and "x [^]\<^bsub>(R)\<^esub> CARD('a) ^ m' = x"
and "y [^]\<^bsub>(R)\<^esub> CARD('a) ^ m' = y"
shows "(x \<otimes>\<^bsub>(R)\<^esub> y) [^]\<^bsub>(R)\<^esub> CARD('a) ^ m' = (x \<otimes>\<^bsub>(R)\<^esub> y)" 
  using assms assms field_R.nat_pow_distrib by auto

lemma add_closed_power:
assumes x1: "x [^]\<^bsub>(R)\<^esub> CARD('a) ^ m' = x"
and y1: "y [^]\<^bsub>(R)\<^esub> CARD('a) ^ m' = y"
shows "(x \<oplus>\<^bsub>(R)\<^esub> y) [^]\<^bsub>(R)\<^esub> CARD('a) ^ m' = (x \<oplus>\<^bsub>(R)\<^esub> y)"
proof -
  have "(x + y) ^ CARD('a) ^ m' = x^(CARD('a) ^ m') + y ^ (CARD('a) ^ m')" by auto  
  hence "(x + y) ^ CARD('a) ^ m' mod f = (x^(CARD('a) ^ m') + y ^ (CARD('a) ^ m')) mod f" by auto
  hence "(x \<oplus>\<^bsub>(R)\<^esub> y) [^]\<^bsub>(R)\<^esub> CARD('a) ^ m' 
  = (x [^]\<^bsub>(R)\<^esub> CARD('a)^m') \<oplus>\<^bsub>(R)\<^esub> (y [^]\<^bsub>(R)\<^esub> CARD('a)^m')"    
    by (auto, unfold R_def plus_irr_def, auto simp add: mod_add_eq power_mod)
  also have "... = x \<oplus>\<^bsub>(R)\<^esub> y" unfolding x1 y1 by simp
  finally show ?thesis .
qed

lemma x_power_pm_minus_1: 
  assumes x: "x \<in> carrier (mult_of R)"
  and "x [^]\<^bsub>(R)\<^esub> CARD('a) ^ m' = x"
  shows "x [^]\<^bsub>(R)\<^esub> (CARD('a) ^ m' - 1) = \<one>\<^bsub>(R)\<^esub>"
  by (metis (no_types, lifting) One_nat_def Suc_pred assms(2) carrier_mult_of field_R.Units_closed 
      field_R.Units_l_cancel field_R.field_Units field_R.l_one field_R.m_rcancel field_R.nat_pow_Suc 
      field_R.nat_pow_closed field_R.one_closed field_R.r_null field_R.r_one x zero_less_card_finite 
      zero_less_power)

context
begin

private lemma monom_a_1_P:
  assumes m: "monom 1 1 \<in> carrier R"
  and eq: "monom 1 1 [^]\<^bsub>(R)\<^esub> (CARD('a) ^ m') = monom 1 1"
  shows "monom a 1 [^]\<^bsub>(R)\<^esub> (CARD('a) ^ m') = monom a 1"
proof -
  have "monom a 1 = [:a:] * (monom 1 1)"
    by (metis One_nat_def monom_0 monom_Suc mult.commute pCons_0_as_mult)
  also have "... = [:a:] \<otimes>\<^bsub>(R)\<^esub> (monom 1 1)" 
    by (auto simp add: R_def mult_irr_def)
       (metis One_nat_def assms(2) mod_mod_trivial mod_smult_left pow_irr)
  finally have eq2: "monom a 1 = [:a:] \<otimes>\<^bsub>R\<^esub> monom 1 1" .
  show ?thesis unfolding eq2 
    by (rule mult_closed_power[OF _ m _ eq], insert fermat_theorem_power_poly_R, auto)
qed

private lemma prod_monom_1_1:
  defines "P == (\<lambda> x n. (x[^]\<^bsub>(R)\<^esub> (CARD('a) ^ n) = x))"
  assumes m: "monom 1 1 \<in> carrier R"
  and eq: "P (monom 1 1) n"
  shows "P ((\<Prod>i = 0..<b::nat. monom 1 1) mod f) n"
proof (induct b)
  case 0
  then show ?case unfolding P_def
    by (simp add: power_mod)
next
  case (Suc b)
  let ?N = "(\<Prod>i = 0..<b. monom 1 1)"
  have eq2: "(\<Prod>i = 0..<Suc b. monom 1 1) mod f = monom 1 1 \<otimes>\<^bsub>(R)\<^esub> (\<Prod>i = 0..<b. monom 1 1)"
    by (metis field_R.m_comm field_R.nat_pow_Suc mod_in_carrier mod_mod_trivial 
        pow_irr prod_pow times_mod_expand)
  also have "... = (monom 1 1 mod f) \<otimes>\<^bsub>(R)\<^esub> ((\<Prod>i = 0..<b. monom 1 1) mod f)" 
    by (rule times_mod_expand)
  finally have eq2: "(\<Prod>i = 0..<Suc b. monom 1 1) mod f 
    = (monom 1 1 mod f) \<otimes>\<^bsub>(R)\<^esub> ((\<Prod>i = 0..<b. monom 1 1) mod f)" .
  show ?case 
  unfolding eq2 P_def 
  proof (rule mult_closed_power)
    show "(monom 1 1 mod f) [^]\<^bsub>R\<^esub> CARD('a) ^ n = monom 1 1 mod f"
      using P_def element_in_carrier eq m mod_poly_less by force
    show "((\<Prod>i = 0..<b. monom 1 1) mod f) [^]\<^bsub>R\<^esub> CARD('a) ^ n = (\<Prod>i = 0..<b. monom 1 1) mod f"      
      using P_def Suc.hyps by blast
  qed (auto)
qed


private lemma monom_1_b:
  defines "P == (\<lambda> x n. (x[^]\<^bsub>(R)\<^esub> (CARD('a) ^ n) = x))"
  assumes m: "monom 1 1 \<in> carrier R"
  and monom_1_1: "P (monom 1 1) m'"
  and b: "b < degree f"
  shows "P (monom 1 b) m'"
proof -
  have "monom 1 b = (\<Prod>i = 0..<b. monom 1 1)"
    by (metis prod_pow x_pow_n)
  also have "... = (\<Prod>i = 0..<b. monom 1 1) mod f" 
    by (rule mod_poly_less[symmetric], auto)
       (metis One_nat_def b degree_linear_power x_as_monom)
  finally have eq2: "monom 1 b = (\<Prod>i = 0..<b. monom 1 1) mod f" .
  show ?thesis unfolding eq2 P_def 
    by (rule prod_monom_1_1[OF m monom_1_1[unfolded P_def]])  
qed



private lemma monom_a_b:
  defines "P == (\<lambda> x n. (x[^]\<^bsub>(R)\<^esub> (CARD('a) ^ n) = x))"
  assumes m: "monom 1 1 \<in> carrier R"
  and m1: "P (monom 1 1) m'"
  and b: "b < degree f"
  shows "P (monom a b) m'"
proof -
  have "monom a b = smult a (monom 1 b)"
    by (simp add: smult_monom)
  also have "... = [:a:] * (monom 1 b)" by auto
  also have "... = [:a:] \<otimes>\<^bsub>(R)\<^esub> (monom 1 b)" 
    unfolding R_def mult_irr_def
    by (simp add: b degree_monom_eq mod_poly_less)
  finally have eq: "monom a b = [:a:] \<otimes>\<^bsub>(R)\<^esub> (monom 1 b)" .
  show ?thesis unfolding eq P_def 
  proof (rule mult_closed_power)
    show "[:a:] [^]\<^bsub>R\<^esub> CARD('a) ^ m' = [:a:]" by (rule fermat_theorem_power_poly_R)
    show "monom 1 b [^]\<^bsub>R\<^esub> CARD('a) ^ m' = monom 1 b" 
      unfolding P_def by (rule monom_1_b[OF m m1[unfolded P_def] b])
    show "monom 1 b \<in> carrier R" unfolding element_in_carrier using b
      by (simp add: degree_monom_eq)
  qed (auto)
qed


private lemma sum_monoms_P:
  defines "P == (\<lambda> x n. (x[^]\<^bsub>(R)\<^esub> (CARD('a) ^ n) = x))"
  assumes m: "monom 1 1 \<in> carrier R"
  and monom_1_1: "P (monom 1 1) n"
  and b: "b < degree f"
shows "P ((\<Sum>i\<le>b. monom (g i) i)) n"
  using b
proof (induct b)
  case 0
  then show ?case unfolding P_def
    by (simp add: poly_const_pow mod_poly_less monom_0)
next
  case (Suc b)
  have b: "b < degree f" using Suc.prems by auto
  have rw: "(\<Sum>i\<le>b. monom (g i) i) mod f = (\<Sum>i\<le>b. monom (g i) i)" by (rule sum_monom_mod[OF b])
  have rw2: "(monom (g (Suc b)) (Suc b) mod f) = monom (g (Suc b)) (Suc b)"
    by (metis Suc.prems field_R.nat_pow_eone m monom_a_b pow_irr power_0 power_one_right)
  have hyp: "P (\<Sum>i\<le>b. monom (g i) i) n" using Suc.prems Suc.hyps by auto
  have "(\<Sum>i\<le>Suc b. monom (g i) i) = monom (g (Suc b)) (Suc b) + (\<Sum>i\<le>b. monom (g i) i)"    
    by simp
  also have "... = (monom (g (Suc b)) (Suc b) mod f) + ((\<Sum>i\<le>b. monom (g i) i) mod f)" 
    using rw rw2 by argo
  also have "... = monom (g (Suc b)) (Suc b) \<oplus>\<^bsub>R\<^esub> (\<Sum>i\<le>b. monom (g i) i)" 
    unfolding R_def plus_irr_def
    by (simp add: poly_mod_add_left)
  finally have eq: "(\<Sum>i\<le>Suc b. monom (g i) i) 
    = monom (g (Suc b)) (Suc b) \<oplus>\<^bsub>R\<^esub> (\<Sum>i\<le>b. monom (g i) i)" .  
  show ?case unfolding eq P_def 
  proof (rule add_closed_power)
    show "monom (g (Suc b)) (Suc b) [^]\<^bsub>R\<^esub> CARD('a) ^ n = monom (g (Suc b)) (Suc b)"
      by (rule monom_a_b[OF m monom_1_1[unfolded P_def] Suc.prems])
    show "(\<Sum>i\<le>b. monom (g i) i) [^]\<^bsub>R\<^esub> CARD('a) ^ n = (\<Sum>i\<le>b. monom (g i) i)" 
      using hyp unfolding P_def by simp
  qed
qed

lemma element_carrier_P:
  defines "P \<equiv> (\<lambda> x n. (x[^]\<^bsub>(R)\<^esub> (CARD('a) ^ n) = x))"
  assumes m: "monom 1 1 \<in> carrier R"
  and monom_1_1: "P (monom 1 1) m'"
  and a: "a \<in> carrier R"
shows "P a m'"
proof -
  have degree_a: "degree a < degree f" using a element_in_carrier by simp
  have "P (\<Sum>i\<le>degree a. monom (poly.coeff a i) i) m'"
    unfolding P_def
    by (rule sum_monoms_P[OF m monom_1_1[unfolded P_def] degree_a])
  thus ?thesis unfolding poly_as_sum_of_monoms by simp
qed
end

end

(* First part of the result that we need *)
lemma degree_divisor1: 
  assumes f: "irreducible (f :: 'a :: prime_card mod_ring poly)" 
  and d: "degree f = d" 
shows "f dvd (monom 1 1)^(CARD('a)^d) - monom 1 1"
proof -
  interpret poly_mod_type_irr "CARD('a)" f by (unfold_locales, auto simp add: f)
  show ?thesis
  proof (cases "d = 1")
    case True
    show ?thesis
    proof (cases "monom 1 1 mod f = 0")
      case True
      then show ?thesis
        by (metis Suc_pred dvd_diff dvd_mult2 mod_eq_0_iff_dvd power.simps(2) 
            zero_less_card_finite zero_less_power)
    next
      case False note mod_f_not0 = False    
      have "monom 1 (CARD('a)) mod f = monom 1 1 mod f"
      proof -
        let ?g1 = "(monom 1 (CARD('a))) mod f"
        let ?g2 = "(monom 1 1) mod f"
        have deg_g1: "degree ?g1 < degree f" and deg_g2: "degree ?g2 < degree f"
          by (metis True card_UNIV_unit d degree_0 degree_mod_less' zero_less_card_finite zero_neq_one)+   
        have g2: "?g2 [^]\<^bsub>(mult_of R)\<^esub> CARD('a)^degree f = ?g2 ^ (CARD('a)^degree f) mod f"
          by (rule pow_irr_mult_of)
        have "?g2 [^]\<^bsub>(mult_of R)\<^esub> CARD('a)^degree f = ?g2" 
          by (rule element_power_order_eq_1', insert mod_f_not0 deg_g2, 
              auto simp add: carrier_mult_of R_def carrier_irr_def )  
        hence "?g2 ^ CARD('a) mod f = ?g2 mod f" using True d by auto    
        hence "?g1 mod f = ?g2 mod f" by (metis mod_mod_trivial power_mod x_pow_n)
        thus ?thesis by simp
      qed
      thus ?thesis by (metis True mod_eq_dvd_iff_poly power_one_right x_pow_n) 
    qed
  next
    case False
    have deg_f1: "1 < degree f"
      using False d degree_f by linarith
    have "monom 1 1 [^]\<^bsub>(mult_of R)\<^esub> CARD('a)^degree f = monom 1 1"
      by (rule element_power_order_eq_1', insert deg_f1) 
          (auto simp add: carrier_mult_of R_def carrier_irr_def degree_monom_eq) 
    hence "monom 1 1^CARD('a)^degree f mod f = monom 1 1 mod f" 
      using deg_f1 by (auto, metis mod_mod_trivial)
    thus ?thesis using d mod_eq_dvd_iff_poly by blast
  qed
qed

(* Second part *)
lemma degree_divisor2: 
  assumes f: "irreducible (f :: 'a :: prime_card mod_ring poly)" 
  and d: "degree f = d" 
  and c_ge_1: "1 \<le> c" and cd: "c < d"
shows "\<not> f dvd monom 1 1 ^ CARD('a) ^ c - monom 1 1"
proof (rule ccontr)
  interpret poly_mod_type_irr "CARD('a)" f by (unfold_locales, auto simp add: f)
  have field_R: "field R"
    by (simp add: field_R.field_axioms)
  assume "\<not> \<not> f dvd monom 1 1 ^ CARD('a) ^ c - monom 1 1"
  hence f_dvd: "f dvd monom 1 1 ^ CARD('a) ^ c - monom 1 1" by simp 
  obtain a where a_R: "a \<in> carrier (mult_of R)" 
    and ord_a: "group.ord (mult_of R) a = order (mult_of R)" 
    and gen: "carrier (mult_of R) = {a [^]\<^bsub>R\<^esub> i |i. i \<in> (UNIV::nat set)}" 
    using field.finite_field_mult_group_has_gen2[OF field_R] by auto
  have d_not1: "d>1" using c_ge_1 cd by auto
  have monom_in_carrier: "monom 1 1 \<in> carrier (mult_of R)" 
    using d_not1 unfolding carrier_mult_of R_def carrier_irr_def
    by (simp add: d degree_monom_eq)
  then have "monom 1 1 \<notin> {\<zero>\<^bsub>R\<^esub>}"
    by auto
  then obtain k where "monom 1 1 = a ^ k mod f"
    using gen monom_in_carrier by auto
  then have k: "a [^]\<^bsub>R\<^esub> k = monom 1 1"
    by simp
  have a_m_1: "a [^]\<^bsub>R\<^esub> (CARD('a)^c - 1) = \<one>\<^bsub>R\<^esub>"
  proof (rule x_power_pm_minus_1[OF a_R])
    let ?x = "monom 1 1::'a mod_ring poly"
    show "a [^]\<^bsub>R\<^esub> CARD('a) ^ c = a" 
    proof (rule element_carrier_P)
      show "?x \<in> carrier R"
        by (metis k mod_in_carrier pow_irr)
      have "?x ^ CARD('a)^ c mod f = ?x mod f" using f_dvd
        using mod_eq_dvd_iff_poly by blast
      thus "?x [^]\<^bsub>R\<^esub> CARD('a)^ c = ?x"
        by (metis d d_not1 degree_monom_eq mod_poly_less one_neq_zero pow_irr)
      show "a \<in> carrier R" using a_R unfolding carrier_mult_of by auto
    qed  
  qed
  have "Group.group (mult_of R)"
    by (simp add: field_R.field_mult_group)
  moreover have "finite (carrier (mult_of R))" by auto
  moreover have "a \<in> carrier (mult_of R)" by (rule a_R )
  moreover have "a [^]\<^bsub>mult_of R\<^esub> (CARD('a) ^ c - 1) = \<one>\<^bsub>mult_of R\<^esub>" 
    using a_m_1 unfolding mult_of_def 
    by (auto, metis mult_of_def pow_irr_mult_of nat_pow_mult_of)
  ultimately have ord_dvd: "group.ord (mult_of R) a dvd (CARD('a)^c - 1)" 
    by (meson group.pow_eq_id)
  have "d dvd c" 
  proof (rule dvd_power_minus_1_conv1[OF nontriv])    
    show "0 < d" using cd by auto
    show "CARD('a) ^ d - 1 dvd CARD('a) ^ c - 1" 
      using ord_dvd by (simp add: d ord_a order_irr)
    show "0 < c" using c_ge_1 by auto
  qed
  thus False using c_ge_1 cd
    using nat_dvd_not_less by auto
qed

lemma degree_divisor: assumes "irreducible (f :: 'a :: prime_card mod_ring poly)" "degree f = d" 
  shows "f dvd (monom 1 1)^(CARD('a)^d) - monom 1 1" 
  and "1 \<le> c \<Longrightarrow> c < d \<Longrightarrow> \<not> f dvd (monom 1 1)^(CARD('a)^c) - monom 1 1"
    using assms degree_divisor1 degree_divisor2 by blast+

context 
  assumes "SORT_CONSTRAINT('a :: prime_card)" 
begin

function dist_degree_factorize_main :: 
  "'a mod_ring poly \<Rightarrow> 'a mod_ring poly \<Rightarrow> nat \<Rightarrow> (nat \<times> 'a mod_ring poly) list 
  \<Rightarrow> (nat \<times> 'a mod_ring poly) list" where
  "dist_degree_factorize_main v w d res = (if v = 1 then res else if d + d > degree v 
    then (degree v, v) # res else let
      w = w^(CARD('a)) mod v;
      d = Suc d;
      gd = gcd (w - monom 1 1) v
      in if gd = 1 then dist_degree_factorize_main v w d res else 
      let v' = v div gd in 
      dist_degree_factorize_main v' (w mod v') d ((d,gd) # res))" 
  by pat_completeness auto


termination 
proof (relation "measure (\<lambda> (v,w,d,res). Suc (degree v) - d)", goal_cases) 
  case (3 v w d res x xa xb xc) 
  have "xb dvd v" unfolding 3 by auto
  hence "xc dvd v" unfolding 3 by (metis dvd_def dvd_div_mult_self)
  from divides_degree[OF this] 3
  show ?case by auto
qed auto

declare dist_degree_factorize_main.simps[simp del]
  
lemma dist_degree_factorize_main: assumes 
  dist: "dist_degree_factorize_main v w d res = facts" and
  w: "w = (monom 1 1)^(CARD('a)^d) mod v" and
  sf: "square_free u" and  
  mon: "monic u" and
  prod: "u = v * prod_list (map snd res)" and
  deg: "\<And> f. irreducible f \<Longrightarrow> f dvd v \<Longrightarrow> degree f > d" and
  res: "\<And> i f. (i,f) \<in> set res \<Longrightarrow> i \<noteq> 0 \<and> degree f \<noteq> 0 \<and> monic f \<and> (\<forall> g. irreducible g \<longrightarrow> g dvd f \<longrightarrow> degree g = i)" 
shows "u = prod_list (map snd facts) \<and> (\<forall> i f. (i,f) \<in> set facts \<longrightarrow> factors_of_same_degree i f)" 
  using dist w prod res deg unfolding factors_of_same_degree_def
proof (induct v w d res rule: dist_degree_factorize_main.induct)
  case (1 v w d res)
  note IH = 1(1-2)
  note result = 1(3)
  note w = 1(4)
  note u = 1(5)
  note res = 1(6)
  note fact = 1(7)
  note [simp] = dist_degree_factorize_main.simps[of _ _ d] 
  let ?x = "monom 1 1 :: 'a mod_ring poly" 
  show ?case
  proof (cases "v = 1") 
    case True
    thus ?thesis using result u mon res by auto
  next
    case False note v = this
    note IH = IH[OF this]
    have mon_prod: "monic (prod_list (map snd res))" by (rule monic_prod_list, insert res, auto)
    with mon[unfolded u] have mon_v: "monic v" by (simp add: coeff_degree_mult)
    with False have deg_v: "degree v \<noteq> 0" by (simp add: monic_degree_0)
    show ?thesis
    proof (cases "degree v < d + d")
      case True
      with result False have facts: "facts = (degree v, v) # res" by simp
      show ?thesis 
      proof (intro allI conjI impI)
        fix i f g
        assume *: "(i,f) \<in> set facts" "irreducible g" "g dvd f"          
        show "degree g = i"
        proof (cases "(i,f) \<in> set res")
          case True
          from res[OF this] * show ?thesis by auto
        next
          case False
          with * facts have id: "i = degree v" "f = v" by auto
          note * = *(2-3)[unfolded id]
          from fact[OF *] have dg: "d < degree g" by auto
          from divides_degree[OF *(2)] mon_v have deg_gv: "degree g \<le> degree v" by auto
          from *(2) obtain h where vgh: "v = g * h" unfolding dvd_def by auto
          from arg_cong[OF this, of degree] mon_v have dvgh: "degree v = degree g + degree h" 
            by (metis deg_v degree_mult_eq degree_mult_eq_0) 
          with dg deg_gv dg True have deg_h: "degree h < d" by auto
          {
            assume "degree h = 0" 
            with dvgh have "degree g = degree v" by simp
          }
          moreover
          {
            assume deg_h0: "degree h \<noteq> 0" 
            hence "\<exists> k. irreducible\<^sub>d k \<and> k dvd h" 
              using dvd_triv_left irreducible\<^sub>d_factor by blast
            then obtain k where irr: "irreducible k" and "k dvd h" by auto
            from dvd_trans[OF this(2), of v] vgh have "k dvd v" by auto
            from fact[OF irr this] have dk: "d < degree k" .
            from divides_degree[OF \<open>k dvd h\<close>] deg_h0 have "degree k \<le> degree h" by auto
            with deg_h have "degree k < d" by auto
            with dk have False by auto
          }
          ultimately have "degree g = degree v" by auto
          thus ?thesis unfolding id by auto
        qed
      qed (insert v mon_v deg_v u facts res, force+)        
    next
      case False
      note IH = IH[OF this refl refl refl]
      let ?p = "CARD('a)" 
      let ?w = "w ^ ?p mod v"
      let ?g = "gcd (?w - ?x) v" 
      let ?v = "v div ?g" 
      let ?d = "Suc d" 
      from result[simplified] v False
      have result: "(if ?g = 1 then dist_degree_factorize_main v ?w ?d res
                  else dist_degree_factorize_main ?v (?w mod ?v) ?d ((?d, ?g) # res)) = facts" 
        by (auto simp: Let_def)
      from mon_v have mon_g: "monic ?g" by (metis deg_v degree_0 poly_gcd_monic)
      have ww: "?w = ?x ^ ?p ^ ?d mod v" unfolding w
        by simp (metis (mono_tags, hide_lams) One_nat_def mult.commute power_Suc power_mod power_mult x_pow_n)
      have gv: "?g dvd v" by auto
      hence gv': "v div ?g dvd v"
        by (metis dvd_def dvd_div_mult_self)
      {
        fix f
        assume irr: "irreducible f" and fv: "f dvd v" and "degree f = ?d" 
        from degree_divisor(1)[OF this(1,3)]
        have "f dvd ?x ^ ?p ^ ?d - ?x" by auto
        hence "f dvd (?x ^ ?p ^ ?d - ?x) mod v" using fv by (rule dvd_mod)
        also have "(?x ^ ?p ^ ?d - ?x) mod v = ?x ^ ?p ^ ?d mod v - ?x mod v" by (rule poly_mod_diff_left)
        also have "?x ^ ?p ^ ?d mod v = ?w mod v" unfolding ww by auto
        also have "\<dots> - ?x mod v = (w ^ ?p mod v - ?x) mod v" by (metis poly_mod_diff_left)
        finally have "f dvd (w^?p mod v - ?x)" using fv by (rule dvd_mod_imp_dvd)
        with fv have "f dvd ?g" by auto
      } note deg_d_dvd_g = this
      show ?thesis
      proof (cases "?g = 1")
        case True
        with result have dist: "dist_degree_factorize_main v ?w ?d res = facts" by auto
        show ?thesis 
        proof (rule IH(1)[OF True dist ww u res])
          fix f
          assume irr: "irreducible f" and fv: "f dvd v" 
          from fact[OF this] have "d < degree f" .
          moreover have "degree f \<noteq> ?d"
          proof
            assume "degree f = ?d" 
            from divides_degree[OF deg_d_dvd_g[OF irr fv this]] mon_v
            have "degree f \<le> degree ?g" by auto
            with irr have "degree ?g \<noteq> 0" unfolding irreducible\<^sub>d_def by auto
            with True show False by auto
          qed
          ultimately show "?d < degree f" by auto
        qed
      next
        case False
        with result 
        have result: "dist_degree_factorize_main ?v (?w mod ?v) ?d ((?d, ?g) # res) = facts" 
          by auto 
        from False mon_g have deg_g: "degree ?g \<noteq> 0" by (simp add: monic_degree_0)
        have www: "?w mod ?v = monom 1 1 ^ ?p ^ ?d mod ?v" using gv'
          by (simp add: mod_mod_cancel ww)
        from square_free_factor[OF _ sf, of v] u have sfv: "square_free v" by auto
        have u: "u = ?v * prod_list (map snd ((?d, ?g) # res))" 
          unfolding u by simp
        show ?thesis
        proof (rule IH(2)[OF False refl result www u], goal_cases)
          case (1 i f)
          show ?case
          proof (cases "(i,f) \<in> set res")
            case True
            from res[OF this] show ?thesis by auto
          next
            case False
            with 1 have id: "i = ?d" "f = ?g" by auto
            show ?thesis unfolding id 
            proof (intro conjI impI allI)
              fix g
              assume *: "irreducible g" "g dvd ?g"
              hence gv: "g dvd v" using dvd_trans[of g ?g v] by simp
              from fact[OF *(1) this] have dg: "d < degree g" .
              {
                assume "degree g > ?d"
                from degree_divisor(2)[OF *(1) refl _ this]
                have ndvd: "\<not> g dvd ?x ^ ?p ^ ?d - ?x" by auto 
                from *(2) have "g dvd ?w - ?x" by simp
                from this[unfolded ww]
                have "g dvd ?x ^ ?p ^ ?d mod v - ?x" .
                with gv have "g dvd (?x ^ ?p ^ ?d mod v - ?x) mod v" by (metis dvd_mod)
                also have "(?x ^ ?p ^ ?d mod v - ?x) mod v = (?x ^ ?p ^ ?d - ?x) mod v"
                  by (metis mod_diff_left_eq)
                finally have "g dvd ?x ^ ?p ^ ?d - ?x" using gv by (rule dvd_mod_imp_dvd)
                with ndvd have False by auto
              }
              with dg show "degree g = ?d" by presburger
            qed (insert mon_g deg_g, auto)
          qed
        next
          case (2 f)
          note irr = 2(1)
          from dvd_trans[OF 2(2) gv'] have fv: "f dvd v" .
          from fact[OF irr fv] have df: "d < degree f" "degree f \<noteq> 0" by auto
          {
            assume "degree f = ?d" 
            from deg_d_dvd_g[OF irr fv this] have fg: "f dvd ?g" .
            from gv have id: "v = (v div ?g) * ?g" by simp
            from sfv id have "square_free (v div ?g * ?g)" by simp
            from square_free_multD(1)[OF this 2(2) fg] have "degree f = 0" .
            with df have False by auto
          }
          with df show "?d < degree f" by presburger
        qed
      qed
    qed
  qed
qed

definition distinct_degree_factorization 
  :: "'a mod_ring poly \<Rightarrow> (nat \<times> 'a mod_ring poly) list" where
  "distinct_degree_factorization f = 
     (if degree f = 1 then [(1,f)] else dist_degree_factorize_main f (monom 1 1) 0 [])"
  
lemma distinct_degree_factorization: assumes 
  dist: "distinct_degree_factorization f = facts" and
  u: "square_free f" and  
  mon: "monic f" 
shows "f = prod_list (map snd facts) \<and> (\<forall> i f. (i,f) \<in> set facts \<longrightarrow> factors_of_same_degree i f)" 
proof -
  note dist = dist[unfolded distinct_degree_factorization_def]
  show ?thesis 
  proof (cases "degree f \<le> 1")
    case False
    hence "degree f > 1" and dist: "dist_degree_factorize_main f (monom 1 1) 0 [] = facts" 
      using dist by auto
    hence *: "monom 1 (Suc 0) = monom 1 (Suc 0) mod f"
      by (simp add: degree_monom_eq mod_poly_less)
    show ?thesis
      by (rule dist_degree_factorize_main[OF dist _ u mon], insert *, auto simp: irreducible\<^sub>d_def)
  next
    case True
    hence "degree f = 0 \<or> degree f = 1" by auto
    thus ?thesis
    proof 
      assume "degree f = 0" 
      with mon have f: "f = 1" using monic_degree_0 by blast
      hence "facts = []" using dist unfolding dist_degree_factorize_main.simps[of _ _ 0]
        by auto
      thus ?thesis using f by auto
    next
      assume deg: "degree f = 1" 
      hence facts: "facts = [(1,f)]" using dist by auto
      show ?thesis unfolding facts factors_of_same_degree_def
      proof (intro conjI allI impI; clarsimp)
        fix g
        assume "irreducible g" "g dvd f" 
        thus "degree g = Suc 0" using deg divides_degree[of g f] by (auto simp: irreducible\<^sub>d_def)
      qed (insert mon deg, auto)
    qed
  qed
qed
end

end
