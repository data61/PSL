(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
subsection \<open>The Mignotte Bound\<close>
theory Factor_Bound
imports 
  Mahler_Measure
  Polynomial_Factorization.Gauss_Lemma
  Subresultants.Coeff_Int 
begin

lemma binomial_mono_left: "n \<le> N \<Longrightarrow> n choose k \<le> N choose k" 
proof (induct n arbitrary: k N)
  case (0 k N)
  thus ?case by (cases k, auto)
next
  case (Suc n k N) note IH = this
  show ?case
  proof (cases k)
    case (Suc kk)
    from IH obtain NN where N: "N = Suc NN" and le: "n \<le> NN" by (cases N, auto)     
    show ?thesis unfolding N Suc using IH(1)[OF le] 
      by (simp add: add_le_mono)
  qed auto
qed

definition choose_int where "choose_int m n = (if n < 0 then 0 else m choose (nat n))"

lemma choose_int_suc[simp]:
  "choose_int (Suc n) i = choose_int n (i-1) + choose_int n i"
proof(cases "nat i")
  case 0 thus ?thesis by (simp add:choose_int_def) next
  case (Suc v) hence "nat (i - 1) = v" "i\<noteq>0" by simp_all
    thus ?thesis unfolding choose_int_def Suc by simp
qed

lemma sum_le_1_prod: assumes d: "1 \<le> d" and c: "1 \<le> c"
  shows "c + d \<le> 1 + c * (d :: real)"
proof -
  from d c have "(c - 1) * (d - 1) \<ge> 0" by auto
  thus ?thesis by (auto simp: field_simps)
qed

lemma mignotte_helper_coeff_int: "cmod (coeff_int (\<Prod>a\<leftarrow>lst. [:- a, 1:]) i)
    \<le> choose_int (length lst - 1) i * (\<Prod>a\<leftarrow>lst. (max 1 (cmod a))) 
    + choose_int (length lst - 1) (i - 1)"
proof(induct lst arbitrary:i)
  case Nil thus ?case by (auto simp:coeff_int_def choose_int_def)
  case (Cons v xs i)
  show ?case
  proof (cases "xs = []")
    case True
    show ?thesis unfolding True
      by (cases "nat i", cases "nat (i - 1)", auto simp: coeff_int_def choose_int_def)
  next
    case False
    hence id: "length (v # xs) - 1 = Suc (length xs - 1)" by auto
    have id': "choose_int (length xs) i = choose_int (Suc (length xs - 1)) i" for i
      using False by (cases xs, auto)
    let ?r = "(\<Prod>a\<leftarrow>xs. [:- a, 1:])"
    let ?mv = "(\<Prod>a\<leftarrow>xs. (max 1 (cmod a)))"
    let ?c1 = "real (choose_int (length xs - 1) (i - 1 - 1))" 
    let ?c2 = "real (choose_int (length (v # xs) - 1) i - choose_int (length xs - 1) i)" 
    let "?m xs n" = "choose_int (length xs - 1) n * (\<Prod>a\<leftarrow>xs. (max 1 (cmod a)))"
    have le1:"1 \<le> max 1 (cmod v)" by auto
    have le2:"cmod v \<le> max 1 (cmod v)" by auto
    have mv_ge_1:"1 \<le> ?mv" by (rule prod_list_ge1, auto)
    obtain a b c d where abcd : 
      "a = real (choose_int (length xs - 1) i)" 
      "b = real (choose_int (length xs - 1) (i - 1))" 
      "c = (\<Prod>a\<leftarrow>xs. max 1 (cmod a))" 
      "d = cmod v" by auto
    {
      have c1: "c \<ge> 1" unfolding abcd by (rule mv_ge_1)
      have b: "b = 0 \<or> b \<ge> 1" unfolding abcd by auto
      have a: "a = 0 \<or> a \<ge> 1" unfolding abcd by auto
      hence a0: "a \<ge> 0" by auto
      have acd: "a * (c * d) \<le> a * (c * max 1 d)" using a0 c1
        by (simp add: mult_left_mono)
      from b have "b * (c + d) \<le> b * (1  + (c * max 1 d))" 
      proof 
        assume "b \<ge> 1" 
        hence "?thesis = (c + d \<le> 1 + c * max 1 d)" by simp
        also have \<dots>
        proof (cases "d \<ge> 1")
          case False
          hence id: "max 1 d = 1" by simp
          show ?thesis using False unfolding id by simp
        next
          case True
          hence id: "max 1 d = d" by simp
          show ?thesis using True c1 unfolding id by (rule sum_le_1_prod)
        qed
        finally show ?thesis .
      qed auto
      with acd have "b * c + (b * d + a * (c * d)) \<le> b + (a * (c * max 1 d) + b * (c * max 1 d))" 
        by (auto simp: field_simps)
    } note abcd_main = this      
    have "cmod (coeff_int ([:- v, 1:] * ?r) i) \<le> cmod (coeff_int ?r (i - 1)) + cmod (coeff_int (smult v ?r) i)"
      using norm_triangle_ineq4 by auto
    also have "\<dots> \<le> ?m xs (i - 1) + (choose_int (length xs - 1) (i - 1 - 1)) + cmod (coeff_int (smult v ?r) i)" 
      using Cons[of "i-1"] by auto
    also have "choose_int (length xs - 1) (i - 1) = choose_int (length (v # xs) - 1) i - choose_int (length xs - 1) i" 
      unfolding id choose_int_suc by auto
    also have "?c2 * (\<Prod>a\<leftarrow>xs. max 1 (cmod a)) + ?c1 +
       cmod (coeff_int (smult v (\<Prod>a\<leftarrow>xs. [:- a, 1:])) i) \<le> 
       ?c2 * (\<Prod>a\<leftarrow>xs. max 1 (cmod a)) + ?c1 + cmod v * (
         real (choose_int (length xs - 1) i) * (\<Prod>a\<leftarrow>xs. max 1 (cmod a)) + 
         real (choose_int (length xs - 1) (i - 1)))"
      using mult_mono'[OF order_refl Cons, of "cmod v" i, simplified] by (auto simp: norm_mult)
    also have "\<dots> \<le> ?m (v # xs) i + (choose_int (length xs) (i - 1))" using abcd_main[unfolded abcd]
      by (simp add: field_simps id')
    finally show ?thesis by simp
  qed
qed

lemma mignotte_helper_coeff_int': "cmod (coeff_int (\<Prod>a\<leftarrow>lst. [:- a, 1:]) i)
    \<le> ((length lst - 1) choose i) * (\<Prod>a\<leftarrow>lst. (max 1 (cmod a))) 
    + min i 1 * ((length lst - 1) choose (nat (i - 1)))"
  by (rule order.trans[OF mignotte_helper_coeff_int], auto simp: choose_int_def min_def)

lemma mignotte_helper_coeff: 
  "cmod (coeff h i) \<le> (degree h - 1 choose i) * mahler_measure_poly h 
      + min i 1 * (degree h - 1 choose (i - 1)) * cmod (lead_coeff h)"
proof -
  let ?r = "complex_roots_complex h"
  have "cmod (coeff h i) = cmod (coeff (smult (lead_coeff h) (\<Prod>a\<leftarrow>?r. [:- a, 1:])) i)"
    unfolding complex_roots by auto
  also have "\<dots> = cmod (lead_coeff h) * cmod (coeff (\<Prod>a\<leftarrow>?r. [:- a, 1:]) i)" by(simp add:norm_mult)
  also have "\<dots> \<le> cmod (lead_coeff h) * ((degree h - 1 choose i) * mahler_measure_monic h + 
    (min i 1 * ((degree h - 1) choose nat (int i - 1))))"    
    unfolding mahler_measure_monic_def
    by (rule mult_left_mono, insert mignotte_helper_coeff_int'[of ?r i], auto)
  also have "\<dots> = (degree h - 1 choose i) * mahler_measure_poly h + cmod (lead_coeff h) * (
    min i 1 * ((degree h - 1) choose nat (int i - 1)))" 
    unfolding mahler_measure_poly_via_monic by (simp add: field_simps)
  also have "nat (int i - 1) = i - 1" by (cases i, auto)
  finally show ?thesis by (simp add: ac_simps split: if_splits)
qed

lemma mignotte_coeff_helper:
  "abs (coeff h i) \<le> 
   (degree h - 1 choose i) * mahler_measure h +
   (min i 1 * (degree h - 1 choose (i - 1)) * abs (lead_coeff h))"
  unfolding mahler_measure_def
  using mignotte_helper_coeff[of "of_int_poly h" i] 
  by auto

lemma cmod_through_lead_coeff[simp]:
  "cmod (lead_coeff (of_int_poly h)) = abs (lead_coeff h)"
  by simp

lemma choose_approx: "n \<le> N \<Longrightarrow> n choose k \<le> N choose (N div 2)" 
  by (rule order.trans[OF binomial_mono_left binomial_maximum])

text \<open>For Mignotte's factor bound, we currently do not support queries for individual coefficients,
  as we do not have a combined factor bound algorithm.\<close>

definition mignotte_bound :: "int poly \<Rightarrow> nat \<Rightarrow> int" where
  "mignotte_bound f d = (let d' = d - 1; d2 = d' div 2; binom = (d' choose d2) in
     (mahler_approximation 2 binom f + binom * abs (lead_coeff f)))" 

lemma mignotte_bound_main:  
  assumes "f \<noteq> 0" "g dvd f" "degree g \<le> n"
  shows "\<bar>coeff g k\<bar> \<le> \<lfloor>real (n - 1 choose k) * mahler_measure f\<rfloor> +
       int (min k 1 * (n - 1 choose (k - 1))) * \<bar>lead_coeff f\<bar>"   
proof-
  let ?bnd = 2
  let ?n = "(n - 1) choose k" 
  let ?n' = "min k 1 * ((n - 1) choose (k - 1))" 
  let ?approx = "mahler_approximation ?bnd ?n f" 
  obtain h where gh:"g * h = f" using assms by (metis dvdE)
  have nz:"g\<noteq>0" "h\<noteq>0" using gh assms(1) by auto
  have g1:"(1::real) \<le> mahler_measure h" using mahler_measure_poly_ge_1 gh assms(1) by auto
  note g0 = mahler_measure_ge_0
  have to_n: "(degree g - 1 choose k) \<le> real ?n"
    using binomial_mono_left[of "degree g - 1" "n - 1" k] assms(3) by auto
  have to_n': "min k 1 * (degree g - 1 choose (k - 1)) \<le> real ?n'"
    using binomial_mono_left[of "degree g - 1" "n - 1" "k - 1"] assms(3)
    by (simp add: min_def)
  have "\<bar>coeff g k\<bar> \<le> (degree g - 1 choose k) * mahler_measure g
    + (real (min k 1 * (degree g - 1 choose (k - 1))) * \<bar>lead_coeff g\<bar>)" 
    using mignotte_coeff_helper[of g k] by simp
  also have "\<dots> \<le> ?n * mahler_measure f + real ?n' * \<bar>lead_coeff f\<bar>"
  proof (rule add_mono[OF mult_mono[OF to_n] mult_mono[OF to_n']])
    have "mahler_measure g  \<le> mahler_measure g * mahler_measure h" using g1 g0[of g]
      using mahler_measure_poly_ge_1 nz(1) by force
    thus "mahler_measure g \<le> mahler_measure f"
      using measure_eq_prod[of "of_int_poly g" "of_int_poly h"]
      unfolding mahler_measure_def gh[symmetric] by (auto simp: hom_distribs)
    have *: "lead_coeff f = lead_coeff g * lead_coeff h" 
      unfolding arg_cong[OF gh, of lead_coeff, symmetric] by (rule lead_coeff_mult)
    have "\<bar>lead_coeff h\<bar> \<noteq> 0" using nz(2) by auto
    hence lh: "\<bar>lead_coeff h\<bar> \<ge> 1" by linarith
    have "\<bar>lead_coeff f\<bar> = \<bar>lead_coeff g\<bar> * \<bar>lead_coeff h\<bar>" unfolding * by (rule abs_mult)
    also have "\<dots> \<ge> \<bar>lead_coeff g\<bar> * 1" 
      by (rule mult_mono, insert lh, auto)
    finally have "\<bar>lead_coeff g\<bar> \<le> \<bar>lead_coeff f\<bar>" by simp
    thus "real_of_int \<bar>lead_coeff g\<bar> \<le> real_of_int \<bar>lead_coeff f\<bar>" by simp
  qed (auto simp: g0)
  finally have "\<bar>coeff g k\<bar> \<le> ?n * mahler_measure f + real_of_int (?n' * \<bar>lead_coeff f\<bar>)" by simp
  from floor_mono[OF this, folded floor_add_int]
  have "\<bar>coeff g k\<bar> \<le> floor (?n * mahler_measure f) + ?n' * \<bar>lead_coeff f\<bar>" by linarith
  thus ?thesis unfolding mignotte_bound_def Let_def using mahler_approximation[of ?n f ?bnd] by auto
qed

lemma Mignotte_bound: 
  shows "of_int \<bar>coeff g k\<bar> \<le> (degree g choose k) * mahler_measure g"
proof (cases "k \<le> degree g \<and> g \<noteq> 0")
  case False
  hence "coeff g k = 0" using le_degree by (cases "g = 0", auto)
  thus ?thesis using mahler_measure_ge_0[of g] by auto
next
  case kg: True
  hence g: "g \<noteq> 0" "g dvd g" by auto
  from mignotte_bound_main[OF g le_refl, of k]
  have "real_of_int \<bar>coeff g k\<bar>
    \<le> of_int \<lfloor>real (degree g - 1 choose k) * mahler_measure g\<rfloor> +
      of_int (int (min k 1 * (degree g - 1 choose (k - 1))) * \<bar>lead_coeff g\<bar>)" by linarith
  also have "\<dots> \<le> real (degree g - 1 choose k) * mahler_measure g 
     + real (min k 1 * (degree g - 1 choose (k - 1))) * (of_int \<bar>lead_coeff g\<bar> * 1)"
    by (rule add_mono, force, auto)
  also have "\<dots> \<le> real (degree g - 1 choose k) * mahler_measure g 
     + real (min k 1 * (degree g - 1 choose (k - 1))) * mahler_measure g"
    by (rule add_left_mono[OF mult_left_mono], 
    unfold mahler_measure_def mahler_measure_poly_def,
    rule mult_mono, auto intro!: prod_list_ge1)  
  also have "\<dots> = 
    (real ((degree g - 1 choose k) + (min k 1 * (degree g - 1 choose (k - 1))))) * mahler_measure g" 
    by (auto simp: field_simps)
  also have "(degree g - 1 choose k) + (min k 1 * (degree g - 1 choose (k - 1))) = degree g choose k"
  proof (cases "k = 0")
    case False
    then obtain kk where k: "k = Suc kk" by (cases k, auto)
    with kg obtain gg where g: "degree g = Suc gg" by (cases "degree g", auto)
    show ?thesis unfolding k g by auto
  qed auto
  finally show ?thesis .
qed

lemma mignotte_bound:  
  assumes "f \<noteq> 0" "g dvd f" "degree g \<le> n"
  shows "\<bar>coeff g k\<bar> \<le> mignotte_bound f n"  
proof -
  let ?bnd = 2
  let ?n = "(n - 1) choose ((n - 1) div 2)" 
  have to_n: "(n - 1 choose k) \<le> real ?n" for k
    using choose_approx[OF le_refl] by auto
  from mignotte_bound_main[OF assms, of k]
  have "\<bar>coeff g k\<bar> \<le> 
    \<lfloor>real (n - 1 choose k) * mahler_measure f\<rfloor> + 
    int (min k 1 * (n - 1 choose (k - 1))) * \<bar>lead_coeff f\<bar>" .
  also have "\<dots> \<le> \<lfloor>real (n - 1 choose k) * mahler_measure f\<rfloor> + 
    int ((n - 1 choose (k - 1))) * \<bar>lead_coeff f\<bar>"
    by (rule add_left_mono[OF mult_right_mono], cases k, auto)
  also have "\<dots> \<le> mignotte_bound f n" 
    unfolding mignotte_bound_def Let_def
    by (rule add_mono[OF order.trans[OF floor_mono[OF mult_right_mono] 
    mahler_approximation[of ?n f ?bnd]] mult_right_mono], insert to_n mahler_measure_ge_0, auto)
  finally show ?thesis .
qed

text \<open>As indicated before, at the moment the only available factor bound is Mignotte's one.
  As future work one might use a combined bound.\<close>

definition factor_bound :: "int poly \<Rightarrow> nat \<Rightarrow> int" where
  "factor_bound = mignotte_bound"

lemma factor_bound: assumes "f \<noteq> 0" "g dvd f" "degree g \<le> n"
  shows "\<bar>coeff g k\<bar> \<le> factor_bound f n"
  unfolding factor_bound_def by (rule mignotte_bound[OF assms])

text \<open>We further prove a result for factor bounds and scalar multiplication.\<close>

lemma factor_bound_ge_0: "f \<noteq> 0 \<Longrightarrow> factor_bound f n \<ge> 0" 
  using factor_bound[of f 1 n 0] by auto

lemma factor_bound_smult: assumes f: "f \<noteq> 0" and d: "d \<noteq> 0" 
  and dvd: "g dvd smult d f" and deg: "degree g \<le> n" 
  shows "\<bar>coeff g k\<bar> \<le> \<bar>d\<bar> * factor_bound f n" 
proof -
  let ?nf = "primitive_part f" let ?cf = "content f" 
  let ?ng = "primitive_part g" let ?cg = "content g" 
  from content_dvd_contentI[OF dvd] have "?cg dvd abs d * ?cf" 
    unfolding content_smult_int .  
  hence dvd_c: "?cg dvd d * ?cf" using d
    by (metis abs_content_int abs_mult dvd_abs_iff)
  from primitive_part_dvd_primitive_partI[OF dvd] have "?ng dvd smult (sgn d) ?nf" unfolding primitive_part_smult_int .
  hence dvd_n: "?ng dvd ?nf" using d 
    by (metis content_eq_zero_iff dvd dvd_smult_int f mult_eq_0_iff content_times_primitive_part smult_smult)
  define gc where "gc = gcd ?cf ?cg" 
  define cg where "cg = ?cg div gc"   
  from dvd d f have g: "g \<noteq> 0" by auto  
  from f have cf: "?cf \<noteq> 0" by auto
  from g have cg: "?cg \<noteq> 0" by auto
  hence gc: "gc \<noteq> 0" unfolding gc_def by auto
  have cg_dvd: "cg dvd ?cg" unfolding cg_def gc_def using g by (simp add: div_dvd_iff_mult)
  have cg_id: "?cg = cg * gc" unfolding gc_def cg_def using g cf by simp
  from dvd_smult_int[OF d dvd] have ngf: "?ng dvd f" .
  have gcf: "\<bar>gc\<bar> dvd content f" unfolding gc_def by auto
  have dvd_f: "smult gc ?ng dvd f" 
  proof (rule dvd_content_dvd, 
      unfold content_smult_int content_primitive_part[OF g] 
      primitive_part_smult_int primitive_part_idemp)
    show "\<bar>gc\<bar> * 1 dvd content f" using gcf by auto
    show "smult (sgn gc) (primitive_part g) dvd primitive_part f" 
      using dvd_n cf gc using zsgn_def by force
  qed    
  have "cg dvd d" using dvd_c unfolding gc_def cg_def using cf cg d
    by (simp add: div_dvd_iff_mult dvd_gcd_mult)
  then obtain h where dcg: "d = cg * h" unfolding dvd_def by auto
  with d have "h \<noteq> 0" by auto
  hence h1: "\<bar>h\<bar> \<ge> 1" by simp
  have "degree (smult gc (primitive_part g)) = degree g" 
    using gc by auto
  from factor_bound[OF f dvd_f, unfolded this, OF deg, of k, unfolded coeff_smult]
  have le: "\<bar>gc * coeff ?ng k\<bar> \<le> factor_bound f n" .
  note f0 = factor_bound_ge_0[OF f, of n]
  from mult_left_mono[OF le, of "abs cg"]
  have "\<bar>cg * gc * coeff ?ng k\<bar> \<le> \<bar>cg\<bar> * factor_bound f n" 
    unfolding abs_mult[symmetric] by simp
  also have "cg * gc * coeff ?ng k = coeff (smult ?cg ?ng) k" unfolding cg_id by simp
  also have "\<dots> = coeff g k" unfolding content_times_primitive_part by simp
  finally have "\<bar>coeff g k\<bar> \<le> 1 * (\<bar>cg\<bar> * factor_bound f n)" by simp
  also have "\<dots> \<le> \<bar>h\<bar> * (\<bar>cg\<bar> * factor_bound f n)" 
    by (rule mult_right_mono[OF h1], insert f0, auto)
  also have "\<dots> = (\<bar>cg * h\<bar>) * factor_bound f n" by (simp add: abs_mult)
  finally show ?thesis unfolding dcg .
qed

end 
