(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
subsection \<open>Chinese Remainder Theorem for Polynomials\<close>

text \<open>We prove the Chinese Remainder Theorem, and strengthen it by showing uniqueness\<close>

theory Chinese_Remainder_Poly
imports
  "HOL-Number_Theory.Residues"  
  Polynomial_Factorization.Polynomial_Divisibility
  Polynomial_Interpolation.Missing_Polynomial
begin

lemma cong_add_poly:
  "[(a::'b::{factorial_ring_gcd,field} poly) = b] (mod m) \<Longrightarrow> [c = d] (mod m) \<Longrightarrow> [a + c = b + d] (mod m)"
  by (fact cong_add)

lemma cong_mult_poly:
  "[(a::'b::{field, factorial_ring_gcd} poly) = b] (mod m) \<Longrightarrow> [c = d] (mod m) \<Longrightarrow> [a * c = b * d] (mod m)"
  by (fact cong_mult)

lemma cong_mult_self_poly: "[(a::'b::{factorial_ring_gcd,field} poly) * m = 0] (mod m)"
  by (fact cong_mult_self_right)

lemma cong_scalar2_poly: "[(a::'b::{field, factorial_ring_gcd} poly)= b] (mod m) \<Longrightarrow> [k * a = k * b] (mod m)"
  by (fact cong_scalar_left)

lemma cong_sum_poly:
    "(\<And>x. x \<in> A \<Longrightarrow> [((f x)::'b::{factorial_ring_gcd,field} poly) = g x] (mod m)) \<Longrightarrow>
      [(\<Sum>x\<in>A. f x) = (\<Sum>x\<in>A. g x)] (mod m)"
  by (rule cong_sum)

lemma cong_iff_lin_poly: "([(a::'b::{factorial_ring_gcd,field} poly) = b] (mod m)) = (\<exists>k. b = a + m * k)"
  using cong_diff_iff_cong_0 [of b a m] by (auto simp add: cong_0_iff dvd_def algebra_simps dest: cong_sym)

lemma cong_solve_poly: "(a::'b::{normalization_euclidean_semiring, factorial_ring_gcd,field} poly) \<noteq> 0 \<Longrightarrow> \<exists>x. [a * x = gcd a n] (mod n)"
proof (cases "n = 0")
  case True
  note n0=True
  show ?thesis
  proof (cases "monic a")
    case True
    have n: "normalize a = a" by (rule normalize_monic[OF True])
    show ?thesis
    by (rule exI[of _ 1], auto simp add: n0 n cong_def)
  next
    case False
    show ?thesis 
      by (auto simp add: True cong_def normalize_poly_old_def map_div_is_smult_inverse)
         (metis mult.right_neutral mult_smult_right) 
  qed
next
 case False
 note n_not_0 = False
 show ?thesis
   using bezout_coefficients_fst_snd [of a n, symmetric]
   by (auto simp add: cong_iff_lin_poly mult.commute [of a] mult.commute [of n])
qed


lemma cong_solve_coprime_poly: 
assumes coprime_an:"coprime (a::'b::{normalization_euclidean_semiring, factorial_ring_gcd,field} poly) n"
shows "\<exists>x. [a * x = 1] (mod n)"
proof (cases "a = 0")
  case True
  show ?thesis unfolding cong_def
    using True coprime_an by auto
next
  case False  
  show ?thesis
    using coprime_an cong_solve_poly[OF False, of n]
    unfolding cong_def
    by presburger  
qed
  
lemma cong_dvd_modulus_poly:
  "[x = y] (mod m) \<Longrightarrow> n dvd m \<Longrightarrow> [x = y] (mod n)" for x y :: "'b::{factorial_ring_gcd,field} poly"
  by (auto simp add: cong_iff_lin_poly elim!: dvdE)

lemma chinese_remainder_aux_poly:
  fixes A :: "'a set"
    and m :: "'a \<Rightarrow> 'b::{normalization_euclidean_semiring,factorial_ring_gcd,field} poly"
  assumes fin: "finite A"
    and cop: "\<forall>i \<in> A. (\<forall>j \<in> A. i \<noteq> j \<longrightarrow> coprime (m i) (m j))"
  shows "\<exists>b. (\<forall>i \<in> A. [b i = 1] (mod m i) \<and> [b i = 0] (mod (\<Prod>j \<in> A - {i}. m j)))"
proof (rule finite_set_choice, rule fin, rule ballI)
  fix i
  assume "i : A"
  with cop have "coprime (\<Prod>j \<in> A - {i}. m j) (m i)"
    by (auto intro: prod_coprime_left)
  then have "\<exists>x. [(\<Prod>j \<in> A - {i}. m j) * x = 1] (mod m i)"
    by (elim cong_solve_coprime_poly)
  then obtain x where "[(\<Prod>j \<in> A - {i}. m j) * x = 1] (mod m i)"
    by auto
  moreover have "[(\<Prod>j \<in> A - {i}. m j) * x = 0]
    (mod (\<Prod>j \<in> A - {i}. m j))"
    by (subst mult.commute, rule cong_mult_self_poly)
  ultimately show "\<exists>a. [a = 1] (mod m i) \<and> [a = 0]
      (mod prod m (A - {i}))"
    by blast
qed


(*The Chinese Remainder Theorem for polynomials: *)
lemma chinese_remainder_poly:
  fixes A :: "'a set"
    and m :: "'a \<Rightarrow> 'b::{normalization_euclidean_semiring,factorial_ring_gcd,field} poly"
    and u :: "'a \<Rightarrow> 'b poly"
  assumes fin: "finite A"
    and cop: "\<forall>i\<in>A. (\<forall>j\<in>A. i \<noteq> j \<longrightarrow> coprime (m i) (m j))"
  shows "\<exists>x. (\<forall>i\<in>A. [x = u i] (mod m i))"
proof -
  from chinese_remainder_aux_poly [OF fin cop] obtain b where
    bprop: "\<forall>i\<in>A. [b i = 1] (mod m i) \<and>
      [b i = 0] (mod (\<Prod>j \<in> A - {i}. m j))"
    by blast
  let ?x = "\<Sum>i\<in>A. (u i) * (b i)"
  show "?thesis"
  proof (rule exI, clarify)
    fix i
    assume a: "i : A"
    show "[?x = u i] (mod m i)"
    proof -
      from fin a have "?x = (\<Sum>j \<in> {i}. u j * b j) +
          (\<Sum>j \<in> A - {i}. u j * b j)"
        by (subst sum.union_disjoint [symmetric], auto intro: sum.cong)
      then have "[?x = u i * b i + (\<Sum>j \<in> A - {i}. u j * b j)] (mod m i)"
        unfolding cong_def
        by auto
      also have "[u i * b i + (\<Sum>j \<in> A - {i}. u j * b j) =
                  u i * 1 + (\<Sum>j \<in> A - {i}. u j * 0)] (mod m i)"
        apply (rule cong_add_poly)
        apply (rule cong_scalar2_poly)
        using bprop a apply blast
        apply (rule cong_sum)
        apply (rule cong_scalar2_poly)
        using bprop apply auto
        apply (rule cong_dvd_modulus_poly)
        apply (drule (1) bspec)
        apply (erule conjE)
        apply assumption
        apply rule
        using fin a apply auto
        done
       thus ?thesis
       by (metis (no_types, lifting) a add.right_neutral fin mult_cancel_left1 mult_cancel_right1 
         sum.not_neutral_contains_not_neutral sum.remove)
    qed
  qed
qed


(*********************** Now we try to prove the uniqueness **********************)

lemma cong_trans_poly:
    "[(a::'b::{factorial_ring_gcd,field} poly) = b] (mod m) \<Longrightarrow> [b = c] (mod m) \<Longrightarrow> [a = c] (mod m)"
  by (fact cong_trans)

lemma cong_mod_poly: "(n::'b::{factorial_ring_gcd,field} poly) ~= 0 \<Longrightarrow> [a mod n = a] (mod n)"
  by auto

lemma cong_sym_poly: "[(a::'b::{factorial_ring_gcd,field} poly) = b] (mod m) \<Longrightarrow> [b = a] (mod m)"
  by (fact cong_sym)

lemma cong_1_poly: "[(a::'b::{factorial_ring_gcd,field} poly) = b] (mod 1)"
  by (fact cong_1)

lemma coprime_cong_mult_poly:
  assumes "[(a::'b::{factorial_ring_gcd,field} poly) = b] (mod m)" and "[a = b] (mod n)" and "coprime m n"
  shows "[a = b] (mod m * n)"
  using divides_mult assms
  by (metis (no_types, hide_lams) cong_dvd_modulus_poly cong_iff_lin_poly dvd_mult2 dvd_refl minus_add_cancel mult.right_neutral) 

lemma coprime_cong_prod_poly:
    "(\<forall>i\<in>A. (\<forall>j\<in>A. i \<noteq> j \<longrightarrow> coprime (m i) (m j))) \<Longrightarrow>
      (\<forall>i\<in>A. [(x::'b::{factorial_ring_gcd,field} poly) = y] (mod m i)) \<Longrightarrow>
         [x = y] (mod (\<Prod>i\<in>A. m i))"
  apply (induct A rule: infinite_finite_induct)
    apply auto
  apply (metis coprime_cong_mult_poly prod_coprime_right)
  done

lemma cong_less_modulus_unique_poly:
    "[(x::'b::{factorial_ring_gcd,field} poly) = y] (mod m) \<Longrightarrow> degree x < degree m \<Longrightarrow> degree y < degree m \<Longrightarrow> x = y"
    by (simp add: cong_def mod_poly_less)


lemma chinese_remainder_unique_poly:
  fixes A :: "'a set"
    and m :: "'a \<Rightarrow> 'b::{normalization_euclidean_semiring,factorial_ring_gcd,field} poly"
    and u :: "'a \<Rightarrow> 'b poly"
  assumes nz: "\<forall>i\<in>A. (m i) \<noteq> 0"
    and cop: "\<forall>i\<in>A. (\<forall>j\<in>A. i \<noteq> j \<longrightarrow> coprime (m i) (m j))"
    (*The following assumption should not be necessary, but I need it since in Isabelle 
      degree 0 is 0 instead of -\<infinity>*)
    and not_constant: "0 < degree (prod m A)" 
  shows "\<exists>!x. degree x < (\<Sum>i\<in>A. degree (m i)) \<and> (\<forall>i\<in>A. [x = u i] (mod m i))"
proof -
  from not_constant have fin: "finite A"
    by (metis degree_1 gr_implies_not0 prod.infinite)
  from chinese_remainder_poly [OF fin cop]
  obtain y where one: "(\<forall>i\<in>A. [y = u i] (mod m i))"
    by blast
  let ?x = "y mod (\<Prod>i\<in>A. m i)"
  have degree_prod_sum: "degree (prod m A) = (\<Sum>i\<in>A. degree (m i))" 
    by (rule degree_prod_eq_sum_degree[OF nz])
  from fin nz have prodnz: "(\<Prod>i\<in>A. (m i)) \<noteq> 0"
     by auto
  (*This would hold without the premise not_constant if degree 0 = -\<infinity>*)
  have less: "degree ?x < (\<Sum>i\<in>A. degree (m i))" 
    unfolding degree_prod_sum[symmetric]
    using degree_mod_less[OF prodnz, of y]
    using not_constant
    by auto    
  have cong: "\<forall>i\<in>A. [?x = u i] (mod m i)"
    apply auto
    apply (rule cong_trans_poly)
    prefer 2
    using one apply auto
    apply (rule cong_dvd_modulus_poly)
    apply (rule cong_mod_poly)
    using prodnz apply auto
    apply rule
    apply (rule fin)
    apply assumption
    done    
  have unique: "\<forall>z. degree z < (\<Sum>i\<in>A. degree (m i)) \<and>
      (\<forall>i\<in>A. [z = u i] (mod m i)) \<longrightarrow> z = ?x"
  proof (clarify)
    fix z::"'b poly"
    assume zless: "degree z < (\<Sum>i\<in>A. degree (m i))"
    assume zcong: "(\<forall>i\<in>A. [z = u i] (mod m i))"   
    have deg1: "degree z < degree (prod m A)"
      using degree_prod_sum zless by simp
    have deg2: "degree ?x < degree (prod m A)"
      by (metis deg1 degree_0 degree_mod_less gr0I gr_implies_not0)
    have "\<forall>i\<in>A. [?x = z] (mod m i)"
      apply clarify
      apply (rule cong_trans_poly)
      using cong apply (erule bspec)
      apply (rule cong_sym_poly)
      using zcong by auto
    with fin cop have "[?x = z] (mod (\<Prod>i\<in>A. m i))"
      by (intro coprime_cong_prod_poly) auto
    with zless  show "z = ?x"
      apply (intro cong_less_modulus_unique_poly)
      apply (erule cong_sym_poly)
      apply (auto simp add:  deg1 deg2)
      done
  qed
  from less cong unique show ?thesis by blast
qed

end
